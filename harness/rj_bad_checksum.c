// Law rj_bad_checksum: A Zstandard frame built by hand with a Content_Checksum (frames.h, new_frame: any data of any
// length the allocator provides, any header form with a window up to STREAM_WINDOW, any blocks) whose checksum is
// replaced by any other value is refused: ZSTD_decompress, with any capacity that holds the content, returns
// ZSTD_error_checksum_wrong, and ZSTD_decompressStream, given it in any pieces with any output room (frames.h,
// stream_all), never reports the frame complete (ZSTD_error_memory_allocation ends the run).
#include "frames.h"

int main(void) {
	// Choose the inputs: any data, any frame for it with a checksum, any other checksum, any capacity for the data
	size_t n = upto(PTRDIFF_MAX), len, written, completed;
	unsigned char *data = any_bytes(n);
	unsigned char *frame = data == NULL ? NULL : new_frame(data, n, n, STREAM_WINDOW, 0, &len);
	uint32_t wrong = nondet_u32();
	size_t cap = n + upto(PTRDIFF_MAX - n);
	unsigned char *dst = malloc(cap);
	ZSTD_DStream *zds = ZSTD_createDStream();
	if (frame == NULL || dst == NULL || zds == NULL || !(frame[4] & 4) ||
	    wrong == (uint32_t) ZSTD_XXH64(data, n, 0))
		return 0;
	put_le(frame + len - 4, wrong, 4);
	// Run zstd. RFC 8878 3.1.1: "The content checksum is the result of xxh64() hash function digesting the original
	// (decoded) data". zstd.h, ZSTD_d_forceIgnoreChecksum: "skip checksum validation ... Default is 0"
	size_t result = ZSTD_decompress(dst, cap, frame, len);
	size_t last = stream_all(zds, frame, len, dst, cap, &written, &completed);
	if (out_of_memory(result) || out_of_memory(last))
		return 0;
	// Check
	gp_assert(ZSTD_getErrorCode(result) == ZSTD_error_checksum_wrong && completed == 0);
	return 0;
}
