// Law rj_content_size: A Zstandard frame built by hand (frames.h, new_frame: any data of any length the allocator
// provides, any header form with a window up to STREAM_WINDOW, any blocks, a checksum or not) whose Frame_Content_Size
// field declares any size other than its content's (ZSTD_CONTENTSIZE_UNKNOWN, 2^64 - 1, declares none) is refused:
// ZSTD_decompress, with any capacity that holds the content, returns an error, and ZSTD_decompressStream, given it in
// any pieces with any output room (frames.h, stream_all), never reports the frame complete
// (ZSTD_error_memory_allocation ends the run).
#include "frames.h"

int main(void) {
	// Choose the inputs: any data, any wrong declared size, any frame (with the field), any capacity for the data
	size_t n = upto(PTRDIFF_MAX), len, written, completed;
	uint64_t declared;
	pick(declared);
	unsigned char *data = any_bytes(n);
	unsigned char *frame = data == NULL ? NULL : new_frame(data, n, declared, STREAM_WINDOW, 0, &len);
	size_t cap = n + upto(PTRDIFF_MAX - n);
	unsigned char *dst = malloc(cap);
	ZSTD_DStream *zds = ZSTD_createDStream();
	if (frame == NULL || dst == NULL || zds == NULL || declared == n || declared == ZSTD_CONTENTSIZE_UNKNOWN)
		return 0;
	if ((frame[4] >> 6) == 0 && !(frame[4] & 0x20))   // Frame_Content_Size_flag 0, no Single_Segment_flag: no field
		return 0;
	// Run zstd. RFC 8878 3.1.1.1.4: Frame_Content_Size "is the original (uncompressed) size"
	size_t result = ZSTD_decompress(dst, cap, frame, len);
	size_t last = stream_all(zds, frame, len, dst, cap, &written, &completed);
	if (out_of_memory(result) || out_of_memory(last))
		return 0;
	// Check
	gp_assert(ZSTD_isError(result) && completed == 0);
	return 0;
}
