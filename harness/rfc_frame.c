// Law rfc_frame: A Zstandard frame built by hand from RFC 8878 (frames.h, new_frame: any data of any length the
// allocator provides, any Frame_Header form with a window up to ONE_CALL_WINDOW, any cut into Raw and RLE blocks, a
// Content_Checksum or not), given to ZSTD_decompress with any capacity at least the content's size, decodes to exactly
// its content (ZSTD_error_memory_allocation ends the run).
#include "frames.h"

int main(void) {
	// Choose the inputs: any data, any frame for it, any capacity that holds the data
	size_t n = upto(PTRDIFF_MAX), len;
	unsigned char *data = any_bytes(n);
	unsigned char *frame = data == NULL ? NULL : new_frame(data, n, n, ONE_CALL_WINDOW, 0, &len);
	size_t cap = n + upto(PTRDIFF_MAX - n);
	unsigned char *dst = malloc(cap);
	if (frame == NULL || dst == NULL)
		return 0;
	// Run zstd. RFC 8878 3.1.1.2: "Raw_Block - this is an uncompressed block"; "RLE_Block - this is a single byte,
	// repeated Block_Size times". zstd.h, ZSTD_decompress: "@return : the number of bytes decompressed into `dst`"
	size_t result = ZSTD_decompress(dst, cap, frame, len);
	if (out_of_memory(result))
		return 0;
	// Check
	gp_assert(result == n && bytes_eq(dst, data, n));
	return 0;
}
