// Law rfc_skippable: Skippable frames (frames.h, new_skippable: any of the 16 magic numbers, any user data of any
// length up to 2^32 - 1 bytes), any number of them anywhere among Zstandard frames built by hand (as in rfc_concat),
// add nothing: ZSTD_decompress, with any capacity at least the total content, gives exactly the contents of the
// Zstandard frames one after the other (ZSTD_error_memory_allocation ends the run).
#include "frames.h"

int main(void) {
	// Choose the inputs: any data cut into any pieces, one Zstandard frame per piece; skippable frames anywhere
	size_t n = upto(PTRDIFF_MAX), done = 0, series_len = 0, len;
	unsigned char *data = any_bytes(n), *series = NULL;
	if (data == NULL)
		return 0;
	do {
		size_t piece = 0;
		unsigned char *frame;
		if (nondet_u8() & 1) {
			frame = new_skippable(&len);
		} else {
			piece = upto(n - done);
			frame = new_frame(data + done, piece, piece, ONE_CALL_WINDOW, 0, &len);
		}
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
	// Run zstd. RFC 8878 3.1.2: "From a compliant decoder perspective, skippable frames need just be skipped, and
	// their content ignored, resuming decoding after the skippable frame."
	size_t result = ZSTD_decompress(dst, cap, series, series_len);
	if (out_of_memory(result))
		return 0;
	// Check
	gp_assert(result == n && bytes_eq(dst, data, n));
	return 0;
}
