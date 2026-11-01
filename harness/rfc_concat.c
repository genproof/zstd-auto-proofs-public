// Law rfc_concat: Any number of Zstandard frames built by hand (frames.h, new_frame: together any data of any length
// the allocator provides, cut into any pieces, one frame per piece, each in any header form with a window up to
// ONE_CALL_WINDOW and any blocks), one after the other, given to ZSTD_decompress with any capacity at least the total
// content, decode to exactly their contents one after the other (ZSTD_error_memory_allocation ends the run).
#include "frames.h"

int main(void) {
	// Choose the inputs: any data, cut into any number of pieces (empty ones too), one frame per piece
	size_t n = upto(PTRDIFF_MAX), done = 0, series_len = 0, len;
	unsigned char *data = any_bytes(n), *series = NULL;
	if (data == NULL)
		return 0;
	do {
		size_t piece = upto(n - done);
		unsigned char *frame = new_frame(data + done, piece, piece, ONE_CALL_WINDOW, 0, &len);
		series = frame == NULL ? NULL : join(series, series_len, frame, len);
		if (series == NULL)
			return 0;
		series_len += len;
		done += piece;
	} while (done < n || nondet_u8() != 0);
	size_t cap = n + upto(PTRDIFF_MAX - n);
	unsigned char *dst = malloc(cap);
	if (dst == NULL)
		return 0;
	// Run zstd. RFC 8878 3.1: "The decompressed content of multiple concatenated frames is the concatenation of
	// each frame decompressed content". zstd.h, ZSTD_decompress: "The result will be the concatenation of all
	// decompressed frames, back to back."
	size_t result = ZSTD_decompress(dst, cap, series, series_len);
	if (out_of_memory(result))
		return 0;
	// Check
	gp_assert(result == n && bytes_eq(dst, data, n));
	return 0;
}
