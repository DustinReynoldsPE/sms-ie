/*
 * SMS Import / Export: a simple Android app for importing and exporting SMS and MMS messages,
 * call logs, contacts, and blocked numbers from and to JSON / NDJSON files.
 *
 * Copyright (c) 2021-2022,2024-2026 Thomas More
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
 * along with SMS Import / Export.  If not, see <https://www.gnu.org/licenses/>.
 */

/*
 * This file contains the post-export verification and manifest-writing code
 * used by automaticExport().
 */

package com.github.tmo1.sms_ie

import android.content.Context
import android.net.Uri
import android.system.Os
import androidx.documentfile.provider.DocumentFile
import org.json.JSONObject
import java.io.FileDescriptor
import java.io.FileInputStream
import java.io.IOException
import java.nio.ByteBuffer
import java.nio.ByteOrder
import java.util.Date
import java.util.Locale
import java.util.zip.ZipInputStream

// The result of verifying a single freshly written export file.
data class ExportVerification(
    val bytes: Long,
    // Entry count from the end-of-central-directory record, or null when the
    // archive uses ZIP64 (the EOCD field saturates at 0xFFFF).
    val zipEntries: Int? = null,
    // True if the NDJSON entry was fully read back and its CRC-32 checked.
    val ndjsonVerified: Boolean? = null
)

private const val EOCD_SIGNATURE = 0x06054B50
private const val EOCD_FIXED_LENGTH = 22
private const val ZIP64_SATURATED_COUNT = 0xFFFF

fun exportedFileSize(appContext: Context, uri: Uri): Long {
    appContext.contentResolver.openFileDescriptor(uri, "r")?.use { descriptor ->
        return Os.fstat(descriptor.fileDescriptor).st_size
    } ?: throw IOException("Could not open export file for verification")
}

// Count entries by locating and parsing the end-of-central-directory record,
// which lives at the tail of the file. The SAF descriptor is duplicated into a
// seekable FileChannel, so this reads at most 64 KB regardless of archive
// size. A truncated archive has no valid EOCD and fails here.
private fun countZipEntries(fd: FileDescriptor, fileSize: Long): Int? {
    FileInputStream(Os.dup(fd)).channel.use { channel ->
        val scanLength = minOf(fileSize, (EOCD_FIXED_LENGTH + 65536).toLong()).toInt()
        channel.position(fileSize - scanLength)
        val buffer = ByteBuffer.allocate(scanLength)
        while (buffer.hasRemaining()) {
            if (channel.read(buffer) < 0) break
        }
        buffer.flip()
        buffer.order(ByteOrder.LITTLE_ENDIAN)
        // Scan backwards for the EOCD signature. The comment-length field must
        // exactly account for the bytes after the fixed record, otherwise the
        // signature match is a false positive inside a comment.
        for (offset in scanLength - EOCD_FIXED_LENGTH downTo 0) {
            if (buffer.getInt(offset) == EOCD_SIGNATURE &&
                buffer.getShort(offset + 20).toInt() and 0xFFFF == scanLength - offset - EOCD_FIXED_LENGTH
            ) {
                val totalEntries = buffer.getShort(offset + 10).toInt() and 0xFFFF
                return if (totalEntries == ZIP64_SATURATED_COUNT) null else totalEntries
            }
        }
        throw IOException("Verification failed: no zip end-of-central-directory record")
    }
}

// Re-open a freshly written archive and verify it. The entry count comes from
// the EOCD record (cheap tail read; a truncated file fails). The NDJSON entry
// is then read back in full through ZipInputStream, which throws if its CRC-32
// does not match - and since messages.ndjson is always the first entry
// written, the read stops there instead of streaming gigabytes of binary
// parts, which receive structural verification only.
fun verifyExportZip(appContext: Context, uri: Uri): ExportVerification {
    appContext.contentResolver.openFileDescriptor(uri, "r")?.use { descriptor ->
        val bytes = Os.fstat(descriptor.fileDescriptor).st_size
        val entries = countZipEntries(descriptor.fileDescriptor, bytes)
        val input = appContext.contentResolver.openInputStream(uri)
            ?: throw IOException("Could not re-open export archive for verification")
        input.use { stream ->
            val zip = ZipInputStream(stream)
            val entry = zip.nextEntry
                ?: throw IOException("Verification failed: export archive has no entries")
            if (entry.name != "messages.ndjson") throw IOException("Verification failed: first export archive entry is ${entry.name}")
            val buffer = ByteArray(65536)
            while (zip.read(buffer) >= 0) {
                // Drain the entry; ZipInputStream validates the CRC-32 as the
                // entry data ends and throws ZipException on mismatch.
            }
        }
        return ExportVerification(bytes, entries, true)
    } ?: throw IOException("Could not open export file for verification")
}

fun ByteArray.toHexString(): String = joinToString("") { "%02x".format(it) }

// Write a manifest describing the verified exports of a single scheduled run.
// The manifest is deliberately small (< 1 KB) so that backup consumers can
// validate an export run - presence, size, SHA-256, record counts - without
// opening multi-GB archives. The SHA-256 covers the file bytes as stored,
// i.e. the ciphertext for encrypted exports.
fun writeExportManifest(
    appContext: Context,
    documentTree: DocumentFile,
    date: Date,
    exports: JSONObject
): DocumentFile {
    val manifest = JSONObject()
    manifest.put("format", 1)
    manifest.put("app", appContext.packageName)
    manifest.put("version", BuildConfig.VERSION_NAME)
    manifest.put("written_at", date.toString("yyyy-MM-dd'T'HH:mm:ssXXX", Locale.US))
    manifest.put("exports", exports)
    val file = createFile(
        documentTree, "application/json",
        "manifest-${date.toString("yyyy-MM-dd")}.json", false
    )
    appContext.contentResolver.openOutputStream(file.uri)?.use {
        it.write(manifest.toString(2).toByteArray())
    } ?: throw IOException("Failed to write export manifest")
    return file
}
