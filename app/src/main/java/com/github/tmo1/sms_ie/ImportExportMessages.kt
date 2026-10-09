/*
 * SMS Import / Export: a simple Android app for importing and exporting SMS and MMS messages,
 * call logs, and contacts, from and to JSON / NDJSON files.
 *
 * Copyright (c) 2021-2026 Thomas More
 *
 * This file is part of SMS Import / Export.
 *
 * SMS Import / Export is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMS Import / Export is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with SMS Import / Export.  If not, see <https://www.gnu.org/licenses/>
 *
 */

// This file contains the routines that import and export SMS and MMS messages.

package com.github.tmo1.sms_ie

import android.content.ContentProviderOperation
import android.content.ContentValues
import android.content.Context
import android.database.Cursor.FIELD_TYPE_BLOB
import android.net.Uri
import android.os.Build
import android.os.Build.VERSION.SDK_INT
import android.provider.Telephony
import android.util.Base64
import android.util.Log
import androidx.annotation.RequiresApi
import androidx.core.net.toUri
import androidx.preference.PreferenceManager
import kotlinx.coroutines.Dispatchers
import kotlinx.coroutines.coroutineScope
import kotlinx.coroutines.ensureActive
import kotlinx.coroutines.launch
import kotlinx.coroutines.withContext
import org.json.JSONArray
import org.json.JSONObject
import java.io.BufferedOutputStream
import java.io.BufferedReader
import java.io.InputStream
import java.io.InputStreamReader
import java.io.OutputStream
import java.util.Collections
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.atomic.AtomicInteger
import java.util.zip.CRC32
import java.util.zip.ZipEntry
import java.util.zip.ZipInputStream
import java.util.zip.ZipOutputStream
import kotlin.coroutines.coroutineContext

// PduHeaders are referenced here https://developer.android.com/reference/android/provider/Telephony.Mms.Addr#TYPE
// and defined here https://android.googlesource.com/platform/frameworks/opt/mms/+/4bfcd8501f09763c10255442c2b48fad0c796baa/src/java/com/google/android/mms/pdu/PduHeaders.java
// but are apparently unavailable in a public class
const val PDU_HEADERS_FROM = "137"
private const val INSERT_BATCH_SIZE = 200
private const val ADDR_PREFETCH_WORKERS = 8
private const val EXPORT_CURSOR_WORKERS = 4

data class MessageTotal(var sms: Int = 0, var mms: Int = 0)

data class MmsBinaryPart(val uri: Uri, val filename: String, val compressible: Boolean)

// MMS parts carrying already-compressed payloads (images, audio, video, ...)
// only waste CPU and battery when deflated again, so they are STORED
// uncompressed; text and SMIL parts still compress usefully.
private fun isCompressibleContentType(contentType: String): Boolean {
    return contentType.isEmpty() || contentType.startsWith("text/")
            || contentType == "application/smil"
}

// Reads the address rows of one MMS message and returns them as a JSONObject that
// may contain "__sender_address" and "__recipient_addresses". The provider only
// exposes addresses through a per-message URI, so callers issue one query per
// message; when many messages are exported, prefetching these with a few worker
// coroutines hides most of that round-trip latency.
private fun mmsAddrToJSON(
    appContext: Context, displayNames: MutableMap<String, String?>, msgId: String
): JSONObject {
    // the following is adapted from https://stackoverflow.com/questions/3012287/how-to-read-mms-data-in-android/6446831#6446831
    val mmsAddr = JSONObject()
    appContext.contentResolver.query(
        "content://mms/$msgId/addr".toUri(), null, null, null, null
    )?.use { address ->
        val addressTypeIndex =
            address.getColumnIndexOrThrow(Telephony.Mms.Addr.TYPE)
        val addressIndex =
            address.getColumnIndexOrThrow(Telephony.Mms.Addr.ADDRESS)
        // write sender address object
        if (address.moveToFirst()) {
            do {
                if (addressTypeIndex.let { x -> address.getString(x) } == PDU_HEADERS_FROM) {
                    val mmsSenderAddress = JSONObject()
                    address.columnNames.forEachIndexed { i, columnName ->
                        val value = address.getString(i)
                        if (value != null) mmsSenderAddress.put(columnName, value)
                    }
                    val displayName = lookupDisplayName(
                        appContext, displayNames, address.getString(addressIndex)
                    )
                    if (displayName != null) mmsSenderAddress.put(
                        "__display_name", displayName
                    )
                    mmsAddr.put("__sender_address", mmsSenderAddress)
                    break
                }
            } while (address.moveToNext())
        }
        // write array of recipient address objects
        if (address.moveToFirst()) {
            val mmsRecipientAddresses = JSONArray()
            do {
                if (addressTypeIndex.let { x -> address.getString(x) } != PDU_HEADERS_FROM) {
                    val mmsRecipientAddress = JSONObject()
                    address.columnNames.forEachIndexed { i, columnName ->
                        val value = address.getString(i)
                        if (value != null) mmsRecipientAddress.put(
                            columnName, value
                        )
                    }
                    val displayName = lookupDisplayName(
                        appContext, displayNames, address.getString(addressIndex)
                    )
                    if (displayName != null) mmsRecipientAddress.put(
                        "__display_name", displayName
                    )
                    mmsRecipientAddresses.put(mmsRecipientAddress)
                }
            } while (address.moveToNext())
            mmsAddr.put("__recipient_addresses", mmsRecipientAddresses)
        }
    }
    return mmsAddr
}

// Name of the marker entry written into incremental export archives.
const val EXPORT_METADATA_ENTRY = "export-metadata.json"

suspend fun exportMessages(
    appContext: Context, outputStream: OutputStream?, updateProgress: suspend (Progress) -> Unit,
    dateRangeMs: Pair<Long, Long>? = null
): MessageTotal {
    val prefs = PreferenceManager.getDefaultSharedPreferences(appContext)
    return withContext(Dispatchers.IO) {
        val totals = MessageTotal()
        // synchronizedMap because the MMS address prefetch workers share it; the
        // value type already permits nulls
        val displayNames = Collections.synchronizedMap(mutableMapOf<String, String?>())
        // https://www.reddit.com/r/Kotlin/comments/x5rrj5/any_other_way_to_write_nested_use_blocks/
        // https://bugs.openjdk.org/browse/JDK-8054565
        // https://stackoverflow.com/questions/25175882/java-8-filteroutputstream-exception
        // the BufferedOutputStream coalesces the small per-message JSON writes
        // into larger writes to the (often slow) SAF-provided file descriptor
        ZipOutputStream(BufferedOutputStream(outputStream)).use { zipOutputStream ->
            // Delta archives carry a marker so importers know their overlap
            // window deliberately re-exports already-covered messages and can
            // deduplicate them automatically. It is written first so a
            // streaming reader sees it before messages.ndjson.
            dateRangeMs?.let { (sinceMs, untilMs) ->
                zipOutputStream.putNextEntry(ZipEntry(EXPORT_METADATA_ENTRY))
                zipOutputStream.write(
                    JSONObject()
                        .put("incremental", true)
                        .put("since_ms", sinceMs)
                        .put("until_ms", untilMs)
                        .toString().toByteArray()
                )
                zipOutputStream.closeEntry()
            }
            val jsonZipEntry = ZipEntry("messages.ndjson")
            zipOutputStream.putNextEntry(jsonZipEntry)
            if (prefs.getBoolean("sms", true)) {
                totals.sms = smsToJSON(
                    appContext, zipOutputStream, displayNames, updateProgress, dateRangeMs
                )
            }
            // synchronizedList because the partitioned MMS cursor workers append to it
            val mmsPartList = Collections.synchronizedList(mutableListOf<MmsBinaryPart>())
            if (prefs.getBoolean("mms", true)) {
                totals.mms = mmsToJSON(
                    appContext,
                    zipOutputStream,
                    displayNames,
                    mmsPartList,
                    updateProgress,
                    dateRangeMs,
                )
            }
            zipOutputStream.closeEntry()
            if (prefs.getBoolean("mms", true)) {
                updateProgress(
                    Progress(
                        0, 0, appContext.getString(R.string.copying_mms_binary_data)
                    )
                )

                val buffer = ByteArray(1048576)
                val storeMediaUncompressed =
                    prefs.getBoolean("store_media_uncompressed", true)
                // snapshot: all cursor workers have finished, so the list is stable
                mmsPartList.toList().forEach {
                    ensureActive()

                    val partZipEntry = ZipEntry(it.filename)
                    try {
                        if (!it.compressible && storeMediaUncompressed) {
                            // STORED entries must declare their size and CRC-32
                            // before they are written, which costs one extra
                            // read pass over the provider stream; still far
                            // cheaper than deflating incompressible data.
                            appContext.contentResolver.openInputStream(it.uri)?.use { inputStream ->
                                var size = 0L
                                val crc = CRC32()
                                var n = inputStream.read(buffer)
                                while (n > -1) {
                                    crc.update(buffer, 0, n)
                                    size += n
                                    n = inputStream.read(buffer)
                                }
                                partZipEntry.method = ZipEntry.STORED
                                partZipEntry.size = size
                                partZipEntry.compressedSize = size
                                partZipEntry.crc = crc.value
                            }
                        }
                        zipOutputStream.putNextEntry(partZipEntry)
                        appContext.contentResolver.openInputStream(it.uri)?.use { inputStream ->
                            var n = inputStream.read(buffer)
                            while (n > -1) {
                                zipOutputStream.write(buffer, 0, n)
                                n = inputStream.read(buffer)
                            }
                        }
                    } catch (e: Exception) {
                        Log.e(
                            LOG_TAG,
                            "Error accessing binary data for MMS message part " + it.filename,
                            e
                        )
                    }
                    zipOutputStream.closeEntry()
                }
            }
        }
        totals
    }
}

// Splits a sorted ID list into at most `workers` contiguous ranges so that cursor
// iteration can be partitioned across coroutines.
private fun partitionIds(ids: List<Long>, workers: Int): List<Pair<Long, Long>> {
    if (ids.isEmpty()) return emptyList()
    val chunkSize = (ids.size + workers - 1) / workers
    return ids.chunked(chunkSize).map { it.first() to it.last() }
}

// Adds an _id range restriction to a messageSelection()-style selection string and
// returns it together with its selection arguments.
private fun rangeSelection(selection: String?, lo: Long, hi: Long): Pair<String, Array<String>> {
    return (if (selection == null) "_id BETWEEN ? AND ?"
    else "($selection) AND _id BETWEEN ? AND ?") to arrayOf(lo.toString(), hi.toString())
}

private suspend fun smsToJSON(
    appContext: Context,
    zipOutputStream: ZipOutputStream,
    displayNames: MutableMap<String, String?>,
    updateProgress: suspend (Progress) -> Unit,
    dateRangeMs: Pair<Long, Long>? = null,
): Int {
    val prefs = PreferenceManager.getDefaultSharedPreferences(appContext)
    val maxRecords = prefs.getString("max_records", "")?.toIntOrNull() ?: -1
    var progress = Progress(0, 0, null)
    val selection = messageSelection(appContext, SMS, dateRangeMs)
    // Collect the matching row IDs up front so that cursor iteration can be split
    // into contiguous _id ranges, one per worker.
    val messageIds = mutableListOf<Long>()
    appContext.contentResolver.query(
        Telephony.Sms.CONTENT_URI, arrayOf(Telephony.Sms._ID), selection, null, null
    )?.use {
        while (it.moveToNext()) messageIds.add(it.getLong(0))
    }
    messageIds.sort()
    // a max_records of 0 exported everything in the original per-message loop
    val exportIds = if (maxRecords > 0) messageIds.take(maxRecords) else messageIds
    progress = progress.copy(total = exportIds.size)
    updateProgress(progress)
    if (exportIds.isEmpty()) return 0
    val exported = AtomicInteger(0)
    val zipLock = Any()
    val ranges = partitionIds(exportIds, EXPORT_CURSOR_WORKERS)
    val nextRange = AtomicInteger(0)
    coroutineScope {
        repeat(minOf(ranges.size, EXPORT_CURSOR_WORKERS)) {
            launch(Dispatchers.IO) {
                while (true) {
                    val i = nextRange.getAndIncrement()
                    if (i >= ranges.size) break
                    val (rangeSelectionStr, rangeArgs) =
                        rangeSelection(selection, ranges[i].first, ranges[i].second)
                    appContext.contentResolver.query(
                        Telephony.Sms.CONTENT_URI, null, rangeSelectionStr, rangeArgs, null
                    )?.use { smsCursor ->
                        val addressIndex =
                            smsCursor.getColumnIndexOrThrow(Telephony.Sms.ADDRESS)
                        while (smsCursor.moveToNext()) {
                            coroutineContext.ensureActive()
                            val smsMessage = JSONObject()
                            smsCursor.columnNames.forEachIndexed { j, columnName ->
                                val value = smsCursor.getString(j)
                                if (value != null) smsMessage.put(columnName, value)
                            }
                            val displayName = lookupDisplayName(
                                appContext, displayNames, smsCursor.getString(addressIndex)
                            )
                            if (displayName != null) smsMessage.put(
                                "__display_name", displayName
                            )
                            synchronized(zipLock) {
                                zipOutputStream.write(
                                    (smsMessage.toString() + "\n").toByteArray()
                                )
                            }
                            val current = exported.incrementAndGet()
                            progress = progress.copy(
                                current = current,
                                message = appContext.getString(
                                    R.string.sms_export_progress, current, exportIds.size
                                ),
                            )
                            updateProgress(progress)
                        }
                    }
                }
            }
        }
    }
    return exported.get()
}

private suspend fun mmsToJSON(
    appContext: Context,
    zipOutputStream: ZipOutputStream,
    displayNames: MutableMap<String, String?>,
    mmsPartList: MutableList<MmsBinaryPart>,
    updateProgress: suspend (Progress) -> Unit,
    dateRangeMs: Pair<Long, Long>? = null,
): Int {
    val prefs = PreferenceManager.getDefaultSharedPreferences(appContext)
    val includeBlobs = prefs.getBoolean("include_blobs", true)
    val includeBinaryData = prefs.getBoolean("include_binary_data", true)
    val maxRecords = prefs.getString("max_records", "")?.toIntOrNull() ?: -1
    var progress = Progress(0, 0, null)
    val selection = messageSelection(appContext, MMS, dateRangeMs)
    // Fetch all MMS parts in a single query and group them by message ID, rather
    // than issuing one provider query per exported message.
    val partsByMessageId = ConcurrentHashMap<String, JSONArray>()
    appContext.contentResolver.query(
        "content://mms/part".toUri(), null, null, null, "mid ASC, seq ASC"
    )?.use { part ->
        if (part.moveToFirst()) {
            val midIndex = part.getColumnIndexOrThrow("mid")
            do {
                val mmsPart = JSONObject()
                part.columnNames.forEachIndexed { i, columnName ->
                    val value = part.getString(i)
                    if (value != null) mmsPart.put(columnName, value)
                }
                // The part table can contain rows whose mid does not reference an
                // exported message (orphans, or messages outside the export
                // selection); grouping is cheap, but binary entries are only
                // collected below, once a message is actually exported.
                partsByMessageId.getOrPut(part.getString(midIndex)) { JSONArray() }
                    .put(mmsPart)
            } while (part.moveToNext())
        }
    }
    // Collect the matching message IDs up front, both to prefetch address rows and
    // to split cursor iteration into contiguous _id ranges, one per worker.
    val mmsIds = mutableListOf<Long>()
    appContext.contentResolver.query(
        Telephony.Mms.CONTENT_URI, arrayOf("_id"), selection, null, null
    )?.use {
        while (it.moveToNext()) {
            mmsIds.add(it.getLong(0))
            // a max_records of 0 exported everything in the original per-message loop
            if (maxRecords > 0 && mmsIds.size == maxRecords) break
        }
    }
    mmsIds.sort()
    // The MMS address table can only be queried one message at a time, so fetch the
    // address JSON for every message up front with a few parallel workers; the
    // provider serializes SQLite access internally, but query setup and binder
    // round trips overlap across workers.
    val addressesByMessageId = ConcurrentHashMap<String, JSONObject>()
    val nextMessageIndex = AtomicInteger(0)
    coroutineScope {
        repeat(ADDR_PREFETCH_WORKERS) {
            launch(Dispatchers.IO) {
                while (true) {
                    val i = nextMessageIndex.getAndIncrement()
                    if (i >= mmsIds.size) break
                    try {
                        val msgId = mmsIds[i].toString()
                        addressesByMessageId[msgId] =
                            mmsAddrToJSON(appContext, displayNames, msgId)
                    } catch (e: Exception) {
                        // leave it to the cursor loop to fetch this message's
                        // addresses directly
                        Log.w(LOG_TAG, "MMS address prefetch failed: ${e.message}")
                    }
                }
            }
        }
    }
    progress = progress.copy(total = mmsIds.size)
    updateProgress(progress)
    val exported = AtomicInteger(0)
    val zipLock = Any()
    val ranges = partitionIds(mmsIds, EXPORT_CURSOR_WORKERS)
    val nextRange = AtomicInteger(0)
    coroutineScope {
        repeat(minOf(ranges.size, EXPORT_CURSOR_WORKERS)) {
            launch(Dispatchers.IO) {
                while (true) {
                    val i = nextRange.getAndIncrement()
                    if (i >= ranges.size) break
                    val (rangeSelectionStr, rangeArgs) =
                        rangeSelection(selection, ranges[i].first, ranges[i].second)
                    appContext.contentResolver.query(
                        Telephony.Mms.CONTENT_URI, null, rangeSelectionStr, rangeArgs, null
                    )?.use { mmsCursor ->
                        val msgIdIndex = mmsCursor.getColumnIndexOrThrow("_id")
                        // write MMS metadata
                        while (mmsCursor.moveToNext()) {
                            coroutineContext.ensureActive()
                            val mmsMessage = JSONObject()
                            mmsCursor.columnNames.forEachIndexed { j, columnName ->
                                if (mmsCursor.getType(j) != FIELD_TYPE_BLOB) {
                                    val value = mmsCursor.getString(j)
                                    if (value != null) mmsMessage.put(columnName, value)
                                } else if (includeBlobs) {
                                    val value = mmsCursor.getBlob(j)
                                    if (value != null) mmsMessage.put(
                                        "${columnName}__base64__", Base64.encodeToString(
                                            value, Base64.NO_WRAP
                                        )
                                    )
                                }
                            }
                            val msgId = mmsCursor.getString(msgIdIndex) ?: continue
                            val mmsAddr = addressesByMessageId.remove(msgId)
                                ?: mmsAddrToJSON(appContext, displayNames, msgId)
                            mmsAddr.optJSONObject("__sender_address")
                                ?.let { sender -> mmsMessage.put("__sender_address", sender) }
                            mmsAddr.optJSONArray("__recipient_addresses")
                                ?.let { recipients ->
                                    mmsMessage.put("__recipient_addresses", recipients)
                                }
                            partsByMessageId[msgId]?.let { mmsParts ->
                                if (includeBinaryData) {
                                    for (k in 0 until mmsParts.length()) {
                                        val mmsPart = mmsParts.getJSONObject(k)
                                        if (!mmsPart.has(Telephony.Mms.Part._DATA)) continue
                                        var filename = mmsPart.getString(Telephony.Mms.Part._DATA)
                                            .toUri().lastPathSegment
                                        // see https://android.googlesource.com/platform/packages/providers/TelephonyProvider/+/master/src/com/android/providers/telephony/MmsProvider.java#520
                                        if (filename == null) {
                                            filename =
                                                "MISSING_FILENAME" + System.currentTimeMillis() + mmsPart.getString(
                                                    Telephony.Mms.Part.CONTENT_LOCATION
                                                )
                                            mmsPart.put(Telephony.Mms.Part._DATA, filename)
                                        }
                                        mmsPartList.add(
                                            MmsBinaryPart(
                                                ("content://mms/part/" + mmsPart.getString(
                                                    Telephony.Mms.Part._ID
                                                )).toUri(),
                                                "data/$filename",
                                                isCompressibleContentType(
                                                    mmsPart.optString(Telephony.Mms.Part.CONTENT_TYPE)
                                                )
                                            )
                                        )
                                    }
                                }
                                mmsMessage.put("__parts", mmsParts)
                            }
                            synchronized(zipLock) {
                                zipOutputStream.write(
                                    (mmsMessage.toString() + "\n").toByteArray()
                                )
                            }
                            val current = exported.incrementAndGet()
                            progress = progress.copy(
                                current = current,
                                message = appContext.getString(
                                    R.string.mms_export_progress, current, mmsIds.size
                                ),
                            )
                            updateProgress(progress)
                        }
                    }
                }
            }
        }
    }
    return exported.get()
}

// bulkInsert() performs a single binder call per batch instead of one per row, which
// significantly reduces IPC and transaction overhead when importing many messages.
private fun bulkInsert(
    appContext: Context, uri: Uri, batch: MutableList<ContentValues>
): Int {
    if (batch.isEmpty()) return 0
    val inserted = appContext.contentResolver.bulkInsert(uri, batch.toTypedArray())
    if (inserted != batch.size) Log.w(
        LOG_TAG, "bulkInsert: expected ${batch.size} rows, got $inserted"
    ) else Log.d(LOG_TAG, "bulkInsert: $inserted rows inserted")
    return inserted
}

@RequiresApi(Build.VERSION_CODES.M)
suspend fun importMessages(
    appContext: Context, inputStream: InputStream?, updateProgress: suspend (Progress) -> Unit
): MessageTotal {
    val prefs = PreferenceManager.getDefaultSharedPreferences(appContext)
    var progress = Progress(0, 0, null)
    var deduplication = prefs.getBoolean("deduplication", false)
    val importSubIds = prefs.getBoolean("import_sub_ids", false)
    val importSms = prefs.getBoolean("sms", true)
    val importMms = prefs.getBoolean("mms", true)
    val includeBinaryData = prefs.getBoolean("include_binary_data", true)
    val maxRecords = prefs.getString("max_records", "")?.toIntOrNull() ?: -1
    return withContext(Dispatchers.IO) {
        val totals = MessageTotal()
        // get column names of local SMS, MMS, MMS address, and MMS part tables
        val smsColumns = mutableSetOf<String>()
        val smsCursor =
            appContext.contentResolver.query(Telephony.Sms.CONTENT_URI, null, null, null, null)
        smsCursor?.use {
            smsColumns.addAll(it.columnNames)
            smsColumns.removeAll(
                setOf(
                    "_id", "thread_id", "deleted", "sync_state", "need_download"
                )
            )
        }
        val mmsColumns = mutableSetOf<String>()
        val mmsCursor =
            appContext.contentResolver.query(Telephony.Mms.CONTENT_URI, null, null, null, null)
        mmsCursor?.use {
            mmsColumns.addAll(it.columnNames)
            mmsColumns.removeAll(
                setOf(
                    "_id", "thread_id", "deleted", "sync_state", "need_download"
                )
            )
        }
        val addressColumns = mutableSetOf<String>()
        // I don't know if there's a way to query the MMS address table without supplying a
        // dummy message ID, but this seems to work:
        val addressTableUri = "content://mms/0/addr".toUri()
        val addressCursor =
            appContext.contentResolver.query(addressTableUri, null, null, null, null)
        addressCursor?.use {
            addressColumns.addAll(it.columnNames)
            addressColumns.removeAll(
                setOf(
                    Telephony.Mms.Addr.MSG_ID, Telephony.Mms.Addr._ID, Telephony.Mms.Addr._COUNT
                )
            )
        }
        val partColumns = mutableSetOf<String>()
        // I can't find an officially documented way of getting the Part table URI for API < 29
        // the idea to use "content://mms/part" comes from here:
        // https://stackoverflow.com/a/6446831
        val partTableUri =
            if (SDK_INT >= 29) Telephony.Mms.Part.CONTENT_URI else "content://mms/part".toUri()
        val partCursor = appContext.contentResolver.query(partTableUri, null, null, null, null)
        partCursor?.use {
            partColumns.addAll(it.columnNames)
            partColumns.removeAll(
                setOf(
                    Telephony.Mms.Part.MSG_ID,
                    Telephony.Mms.Part._ID,
                    Telephony.Mms.Part._DATA,
                    Telephony.Mms.Part._COUNT
                )
            )
        }
        val threadIdMap = HashMap<String, String>()
        val excludedAddresses = (prefs.getString("excluded_addresses", "") ?: "").split(",")
        val insertExcludedAddresses = prefs.getBoolean("insert_excluded_addresses", true)
        // The following line assumes that no binary data file is ever referenced by more than one message part
        val mmsPartMap = mutableMapOf<String, Uri>()
        // SMS metadata is accumulated and written in batches via bulkInsert()
        val smsBatch = mutableListOf<ContentValues>()
        // MMS parts are batch-inserted, so their provider URIs are not immediately
        // available for writing their binary data. Instead, we record, per inserted
        // message ID and in insertion order, the filename of each part that carries
        // binary data (and null for each part that does not), and resolve the
        // corresponding part URIs with a single query once all messages are imported.
        val pendingPartFilenames = mutableMapOf<String, MutableList<String?>>()

        // Everything needed to insert one MMS later in a batch: the message's own
        // ContentValues plus its raw address and part JSON (their ContentValues can
        // only be built once the new message ID is known).
        class PendingMms(
            val metadata: ContentValues,
            val addresses: List<JSONObject>,
            val parts: JSONArray?
        )

        val pendingMms = ArrayList<PendingMms>()

        // Builds the ContentValues for one MMS part row (used in both the batched
        // and the fallback insert paths).
        fun buildPartValues(
            messageId: String, messagePart: JSONObject
        ): ContentValues {
            val part = ContentValues()
            part.put(Telephony.Mms.Part.MSG_ID, messageId)
            for (partKey in messagePart.keys()) {
                if (partKey in partColumns) part.put(
                    partKey, messagePart.getString(partKey)
                )
            }
            // sub_ids were added to the MMS address table here:
            // https://android.googlesource.com/platform/packages/providers/TelephonyProvider/+/a97076d34e2613d4a89c92d56c40daa1066c488a
            // Attempting to import sub_ids can cause a "FileNotFoundException: No entry for content"
            // when subsequently trying to write the part's binary data.
            // See: https://github.com/tmo1/sms-ie/issues/142
            if (!importSubIds && part.containsKey("sub_id")) part.put("sub_id", "-1")
            return part
        }

        // Builds the ContentValues for one MMS address row.
        fun buildAddressValues(messageId: String, address: JSONObject): ContentValues {
            val addressContentValues = ContentValues()
            for (addressKey in address.keys()) {
                if (addressKey in addressColumns) {
                    addressContentValues.put(addressKey, address.getString(addressKey))
                }
            }
            // "sub_id"s were added to the MMS address table here:
            // https://android.googlesource.com/platform/packages/providers/TelephonyProvider/+/a97076d34e2613d4a89c92d56c40daa1066c488a
            // Attempting to import "sub_id"s can cause address import to fail:
            // See: https://github.com/tmo1/sms-ie/issues/213
            if (!importSubIds && addressContentValues.containsKey("sub_id")) {
                addressContentValues.put("sub_id", "-1")
            }
            addressContentValues.put(Telephony.Mms.Addr.MSG_ID, messageId)
            return addressContentValues
        }

        // Inserts the address and part rows of one MMS whose message row already
        // exists under the given ID.
        fun insertMmsRowsDirect(messageId: String, pending: PendingMms) {
            val addressUri = "content://mms/$messageId/addr".toUri()
            val addressBatch = pending.addresses.map { buildAddressValues(messageId, it) }
            bulkInsert(appContext, addressUri, addressBatch.toMutableList())
            pending.parts?.let { messageParts ->
                val partUri = "content://mms/$messageId/part".toUri()
                val partBatch = mutableListOf<ContentValues>()
                val partFilenames = mutableListOf<String?>()
                for (i in 0 until messageParts.length()) {
                    val messagePart = messageParts.getJSONObject(i)
                    partBatch.add(buildPartValues(messageId, messagePart))
                    partFilenames.add(
                        if (includeBinaryData) messagePart.optString(
                            Telephony.Mms.Part._DATA
                        ).takeIf { name -> name != "" }
                        else null
                    )
                }
                bulkInsert(appContext, partUri, partBatch)
                pendingPartFilenames[messageId] = partFilenames
            }
        }

        // Inserts one prepared MMS the original way: individual insert() for the
        // message (to obtain its ID), then its address and part rows.
        fun insertMmsDirect(pending: PendingMms) {
            val insertUri = appContext.contentResolver.insert(
                Telephony.Mms.CONTENT_URI, pending.metadata
            )
            if (insertUri == null) {
                Log.e(LOG_TAG, "MMS insert failed!")
                return
            }
            insertUri.lastPathSegment?.let { insertMmsRowsDirect(it, pending) }
        }

        // Inserts the accumulated MMS batch with two applyBatch() calls: the first
        // inserts all message rows and returns each new message URI positionally;
        // the second inserts all address and part rows under those URIs. Compared
        // to per-message insert() calls this amortizes transaction setup and change
        // notification across the whole batch (SQLiteContentProvider batches run in
        // a single transaction). If either call fails, whatever was not committed
        // is replayed with individual inserts, which is slower but correct.
        suspend fun flushMmsBatch() {
            if (pendingMms.isEmpty()) return
            val messageIds = arrayOfNulls<String>(pendingMms.size)
            var pduBatchOk = false
            try {
                val messageOps = ArrayList<ContentProviderOperation>(pendingMms.size)
                pendingMms.forEach {
                    messageOps.add(
                        ContentProviderOperation.newInsert(Telephony.Mms.CONTENT_URI)
                            .withValues(it.metadata).build()
                    )
                }
                val results = appContext.contentResolver.applyBatch(
                    Telephony.Mms.CONTENT_URI.authority!!, messageOps
                )
                pendingMms.forEachIndexed { i, _ ->
                    messageIds[i] =
                        results.getOrNull(i)?.uri?.lastPathSegment
                }
                pduBatchOk = true
                val rowOps = ArrayList<ContentProviderOperation>()
                pendingMms.forEachIndexed { i, pending ->
                    val messageId = messageIds[i] ?: run {
                        Log.e(LOG_TAG, "MMS insert failed in batch!")
                        return@forEachIndexed
                    }
                    val addressUri = "content://mms/$messageId/addr".toUri()
                    pending.addresses.forEach { address ->
                        rowOps.add(
                            ContentProviderOperation.newInsert(addressUri)
                                .withValues(buildAddressValues(messageId, address)).build()
                        )
                    }
                    pending.parts?.let { messageParts ->
                        val partUri = "content://mms/$messageId/part".toUri()
                        val partFilenames = mutableListOf<String?>()
                        for (j in 0 until messageParts.length()) {
                            val messagePart = messageParts.getJSONObject(j)
                            rowOps.add(
                                ContentProviderOperation.newInsert(partUri)
                                    .withValues(buildPartValues(messageId, messagePart))
                                    .build()
                            )
                            partFilenames.add(
                                if (includeBinaryData) messagePart.optString(
                                    Telephony.Mms.Part._DATA
                                ).takeIf { name -> name != "" }
                                else null
                            )
                        }
                        pendingPartFilenames[messageId] = partFilenames
                    }
                }
                if (rowOps.isNotEmpty()) appContext.contentResolver.applyBatch(
                    Telephony.Mms.CONTENT_URI.authority!!, rowOps
                )
            } catch (e: Exception) {
                Log.w(LOG_TAG, "applyBatch import failed, replaying sequentially", e)
                if (pduBatchOk) {
                    // The message rows were committed; only their address and part
                    // rows are missing, so retry those against the known IDs.
                    // Entries staged above are overwritten by insertMmsRowsDirect.
                    pendingMms.forEachIndexed { i, pending ->
                        messageIds[i]?.let { insertMmsRowsDirect(it, pending) }
                    }
                } else {
                    // Nothing was committed; replay the whole batch individually.
                    pendingMms.forEach { insertMmsDirect(it) }
                }
            }
            totals.mms += pendingMms.size
            pendingMms.clear()
            progress = progress.copy(
                message = appContext.getString(
                    R.string.message_import_progress, totals.sms, totals.mms
                )
            )
            updateProgress(progress)
        }

        // Prepares one MMS line for batch insertion: dedup check, metadata,
        // thread_id resolution, address extraction.
        suspend fun prepareMms(messageJSON: JSONObject): PendingMms? {
            coroutineContext.ensureActive()
            val messageMetadata = ContentValues()
            val oldThreadId = messageJSON.optString("thread_id")
            threadIdMap[oldThreadId]?.let { messageMetadata.put("thread_id", it) }
            if (deduplication) {
                // flush the pending batch so the dedup query sees earlier imports
                flushMmsBatch()
                val messageID = messageJSON.optString(Telephony.Mms.MESSAGE_ID)
                val contentLocation =
                    messageJSON.optString(Telephony.Mms.CONTENT_LOCATION)
                var selection =
                    "${Telephony.Mms.DATE}=? AND ${Telephony.Mms.MESSAGE_BOX}=?"
                var selectionArgs = arrayOf(
                    messageJSON.optString(Telephony.Mms.DATE),
                    messageJSON.optString(Telephony.Mms.MESSAGE_BOX)
                )
                if (messageID != "") {
                    selection = "$selection AND ${Telephony.Mms.MESSAGE_ID}=?"
                    selectionArgs += messageJSON.optString(Telephony.Mms.MESSAGE_ID)
                } else if (contentLocation != "") {
                    selection = "$selection AND ${Telephony.Mms.CONTENT_LOCATION}=?"
                    selectionArgs += messageJSON.optString(Telephony.Mms.CONTENT_LOCATION)
                }
                appContext.contentResolver.query(
                    Telephony.Mms.CONTENT_URI,
                    arrayOf(Telephony.Mms._ID),
                    selection,
                    selectionArgs,
                    null
                )?.use {
                    if (it.moveToFirst()) {
                        Log.d(LOG_TAG, "Duplicate message - skipping")
                        return null
                    }
                }
            }
            messageJSON.keys().forEach { key ->
                if (key in mmsColumns) messageMetadata.put(
                    key, messageJSON.getString(key)
                )
            }
            val addresses = mutableListOf<JSONObject>()
            messageJSON.optJSONObject("__sender_address")?.let { addresses.add(it) }
            messageJSON.optJSONArray("__recipient_addresses")?.let {
                for (i in 0 until it.length()) {
                    addresses.add(it.getJSONObject(i))
                }
            }/*Log.d(LOG_TAG, "All addresses: ${addresses.map { x -> x.getString(Telephony.Mms.Addr.ADDRESS) }
                        .toList()}")*/
            val unexcludedAddresses = addresses.filter { address ->
                excludedAddresses.none { excludedAddress ->
                    comparePhoneNumbers(
                        excludedAddress, address.getString(Telephony.Mms.Addr.ADDRESS)
                    )
                }
            }/* If we don't yet have a thread_id (i.e., the message has a new
                    thread_id that we haven't yet encountered and so isn't yet in
                    threadIdMap), then we need to get a new thread_id and record the mapping
                    between the old and new ones in threadIdMap*//*Log.d(LOG_TAG, "Unexcluded Addresses: ${addresses.map { x -> x.getString(Telephony.Mms.Addr.ADDRESS) }
                        .toList()}")*/
            if (!messageMetadata.containsKey("thread_id")) {/* Calling getOrCreateThreadId with an empty set of addresses
                    will cause it to complain:
                    "getThreadId: NO receipients specified -- NOT creating thread" (sic)
                    and then throw an exception:
                    "java.lang.IllegalArgumentException: Unable to find or allocate a thread ID."
                    So if an MMS message has no associated recipient addresses, we add a dummy one here.
                    See: https://github.com/tmo1/sms-ie/issues/150
                    */
                if (addresses.isEmpty()) {
                    addresses.add(JSONObject())
                }
                val newThreadId = Telephony.Threads.getOrCreateThreadId(
                    appContext,
                    unexcludedAddresses.map { x -> x.getString(Telephony.Mms.Addr.ADDRESS) }
                        .toSet())
                messageMetadata.put("thread_id", newThreadId)
                if (oldThreadId != "") threadIdMap[oldThreadId] = newThreadId.toString()
            }
            return PendingMms(
                messageMetadata,
                if (insertExcludedAddresses) addresses else unexcludedAddresses,
                messageJSON.optJSONArray("__parts")
            )
        }

        ZipInputStream(inputStream).use { zipInputStream ->
            var zipEntry = zipInputStream.nextEntry
            while (zipEntry != null) {
                // Delta archives mark themselves so overlap re-exports cannot
                // duplicate rows on restore, regardless of the dedup pref.
                if (zipEntry.name == EXPORT_METADATA_ENTRY) {
                    try {
                        if (JSONObject(
                                zipInputStream.readBytes().decodeToString()
                            ).optBoolean("incremental")
                        ) deduplication = true
                    } catch (e: Exception) {
                        Log.w(LOG_TAG, "Ignoring malformed $EXPORT_METADATA_ENTRY", e)
                    }
                }
                if (zipEntry.name == "messages.ndjson") break
                zipEntry = zipInputStream.nextEntry
            }
            if (zipEntry == null) {
                throw UserFriendlyException(
                    appContext.getString(R.string.missing_messages_ndjson_error)
                )
            }
            progress = progress.copy(message = appContext.getString(R.string.importing_messages))
            updateProgress(progress)
            BufferedReader(InputStreamReader(zipInputStream)).lineSequence()
                .forEachIndexed JSONLine@{ lineNumber, line ->
                    coroutineContext.ensureActive()
                    Log.d(LOG_TAG, "Processing line #$lineNumber")
                    // Log.d(LOG_TAG, "Processing: $line")
                    val messageJSON = JSONObject(line)
                    val oldThreadId = messageJSON.optString("thread_id")
                    // See https://github.com/tmo1/sms-ie/issues/128
                    if (!importSubIds) {
                        messageJSON.put("sub_id", "-1")
                    }
                    if (!messageJSON.has("m_type")) { // it's SMS
                        val messageMetadata = ContentValues()
                        threadIdMap[oldThreadId]?.let {
                            messageMetadata.put("thread_id", it)
                        }
                        Log.d(LOG_TAG, "Message is SMS")
                        // It would obviously be more efficient to break rather than continue when hitting 'max_records', but this option is primarily for debugging and the inefficiency doesn't matter very much
                        if (!importSms || totals.sms == maxRecords) {
                            Log.d(LOG_TAG, "Skipping due to debug settings")
                            return@JSONLine
                        }
                        if (deduplication) {
                            // flush pending rows so the dedup query sees earlier imports
                            totals.sms += bulkInsert(
                                appContext, Telephony.Sms.CONTENT_URI, smsBatch
                            )
                            smsBatch.clear()
                            val smsDuplicatesCursor = appContext.contentResolver.query(
                                Telephony.Sms.CONTENT_URI,
                                arrayOf(Telephony.Sms._ID),
                                "${Telephony.Sms.ADDRESS}=? AND ${Telephony.Sms.TYPE}=? AND ${Telephony.Sms.DATE}=? AND ${Telephony.Sms.BODY}=?",
                                arrayOf(
                                    messageJSON.optString(Telephony.Sms.ADDRESS),
                                    messageJSON.optString(Telephony.Sms.TYPE),
                                    messageJSON.optString(Telephony.Sms.DATE),
                                    messageJSON.optString(Telephony.Sms.BODY)
                                ),
                                null
                            )
                            smsDuplicatesCursor?.use {
                                if (it.moveToFirst()) {
                                    Log.d(LOG_TAG, "Duplicate message - skipping")
                                    return@JSONLine
                                }
                            }
                        }
                        messageJSON.keys().forEach { key ->
                            if (key in smsColumns) messageMetadata.put(
                                key, messageJSON.getString(key)
                            )
                        }/* If we don't yet have a 'thread_id' (i.e., the message has a new
                                   'thread_id' that we haven't yet encountered and so isn't yet in
                                   'threadIdMap'), then we need to get a new 'thread_id' and record the mapping
                                   between the old and new ones in 'threadIdMap'
                                */
                        if (!messageMetadata.containsKey("thread_id")) {
                            val newThreadId = Telephony.Threads.getOrCreateThreadId(
                                appContext,
                                messageMetadata.getAsString(Telephony.TextBasedSmsColumns.ADDRESS)
                            )
                            messageMetadata.put("thread_id", newThreadId)
                            if (oldThreadId != "") threadIdMap[oldThreadId] = newThreadId.toString()
                        }
                        //Log.v(LOG_TAG, "Original thread_id: $oldThreadId\t New thread_id: ${messageMetadata.getAsString("thread_id")}")
                        smsBatch.add(messageMetadata)
                        // flush early at max_records so the cap stays exact
                        if (smsBatch.size == INSERT_BATCH_SIZE || totals.sms + smsBatch.size == maxRecords) {
                            totals.sms += bulkInsert(
                                appContext, Telephony.Sms.CONTENT_URI, smsBatch
                            )
                            smsBatch.clear()
                            progress = progress.copy(
                                message = appContext.getString(
                                    R.string.message_import_progress,
                                    totals.sms,
                                    totals.mms,
                                )
                            )
                            updateProgress(progress)
                        }
                    } else { // it's MMS
                        Log.d(LOG_TAG, "Message is MMS")
                        // flush early at max_records so the cap stays exact
                        if (totals.mms + pendingMms.size == maxRecords) flushMmsBatch()
                        if (!importMms || totals.mms == maxRecords) {
                            Log.d(LOG_TAG, "Skipping due to debug settings")
                            return@JSONLine
                        }
                        prepareMms(messageJSON)?.let {
                            pendingMms.add(it)
                            if (pendingMms.size >= INSERT_BATCH_SIZE) flushMmsBatch()
                        }
                    }
                }
            flushMmsBatch()
            totals.sms += bulkInsert(
                appContext, Telephony.Sms.CONTENT_URI, smsBatch
            )
            if (includeBinaryData && pendingPartFilenames.isNotEmpty()) {
                // Resolve the provider URIs of the batch-inserted MMS parts: within
                // each message, ascending _id order matches insertion order.
                val partIdsByMessage = mutableMapOf<String, ArrayDeque<String>>()
                appContext.contentResolver.query(
                    partTableUri, arrayOf(
                        Telephony.Mms.Part._ID, Telephony.Mms.Part.MSG_ID
                    ), null, null, Telephony.Mms.Part._ID + " ASC"
                )?.use {
                    val idIndex = it.getColumnIndexOrThrow(Telephony.Mms.Part._ID)
                    val midIndex = it.getColumnIndexOrThrow(Telephony.Mms.Part.MSG_ID)
                    while (it.moveToNext()) {
                        partIdsByMessage.getOrPut(it.getString(midIndex)) { ArrayDeque() }
                            .add(it.getString(idIndex))
                    }
                }
                pendingPartFilenames.forEach { (messageId, filenames) ->
                    val partIds = partIdsByMessage[messageId]
                    if (partIds == null || partIds.size != filenames.size) {
                        Log.e(
                            LOG_TAG,
                            "Could not match inserted parts to binary data for MMS message $messageId"
                        )
                    } else {
                        filenames.forEach { filename ->
                            val partId = partIds.removeFirst()
                            if (filename != null) {
                                mmsPartMap[filename.toUri().lastPathSegment.toString()] =
                                    "content://mms/part/$partId".toUri()
                            }
                        }
                    }
                }
            }
            if (includeBinaryData) {
                progress =
                    progress.copy(message = appContext.getString(R.string.copying_mms_binary_data))
                updateProgress(progress)
                val buffer = ByteArray(1048576)
                while (zipEntry != null) {
                    coroutineContext.ensureActive()
                    if (zipEntry.name.startsWith("data/")) {
                        val partUri = mmsPartMap[zipEntry.name.substring(5)]
                        partUri?.let {
                            Log.d(LOG_TAG, "Writing part: $zipEntry")
                            //Log.v(LOG_TAG, "Writing to: $partUri")
                            appContext.contentResolver.openOutputStream(partUri, "wt")
                                ?.use { outputStream ->
                                    var n = zipInputStream.read(buffer)
                                    while (n > -1) {
                                        //Log.v(LOG_TAG, "Read $n bytes")
                                        outputStream.write(buffer, 0, n)
                                        n = zipInputStream.read(buffer)
                                    }
                                } ?: Log.e(
                                LOG_TAG, "Error opening OutputStream to write MMS binary data"
                            )
                        }
                    }
                    zipEntry = zipInputStream.nextEntry
                }
            }
        }
        totals
    }
}
