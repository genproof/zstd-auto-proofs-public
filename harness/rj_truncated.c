// Law rj_truncated: Any part of a Zstandard frame built by hand (frames.h, new_frame: any data of any length the
// allocator provides, any header form with a window up to STREAM_WINDOW, any blocks, a checksum or not) that stops
// before the frame's end (at least one byte of it) is never taken for a complete frame: ZSTD_decompress, with any
// capacity, returns an error, and ZSTD_decompressStream, given it in any pieces with any output room (frames.h,
// stream_all), never returns 0 (ZSTD_error_memory_allocation ends the run).
#include "frames.h"

int main(void) {
	// Choose the inputs: any data, any frame for it, any cut of the frame, any capacity
	size_t n = upto(PTRDIFF_MAX), len, written, completed;
	unsigned char *data = any_bytes(n);
	unsigned char *frame = data == NULL ? NULL : new_frame(data, n, n, STREAM_WINDOW, 0, &len);
	if (frame == NULL)
		return 0;
	size_t cut = 1 + upto(len - 2), cap = upto(PTRDIFF_MAX);   // a frame has at least 9 bytes
	unsigned char *part = copy_of(frame, cut), *dst = malloc(cap);
	ZSTD_DStream *zds = ZSTD_createDStream();
	if (part == NULL || dst == NULL || zds == NULL)
		return 0;
	// Run zstd. zstd.h, ZSTD_decompress: "`compressedSize` : must be the _exact_ size of some number of compressed
	// and/or skippable frames"; ZSTD_decompressStream: "@return : 0 when a frame is completely decoded"
	size_t result = ZSTD_decompress(dst, cap, part, cut);
	size_t last = stream_all(zds, part, cut, dst, cap, &written, &completed);
	if (out_of_memory(result) || out_of_memory(last))
		return 0;
	// Check
	gp_assert(ZSTD_isError(result) && completed == 0);
	return 0;
}
