// Law rj_reserved_bit: A Zstandard frame built by hand (frames.h, new_frame: any data of any length the allocator
// provides, any header form with a window up to STREAM_WINDOW, any blocks, a checksum or not) with the Reserved_bit of
// its Frame_Header_Descriptor set is refused: ZSTD_decompress, with any capacity, returns an error, and
// ZSTD_decompressStream, given it in any pieces with any output room (frames.h, stream_all), never reports the frame
// complete (ZSTD_error_memory_allocation ends the run).
#include "frames.h"

int main(void) {
	// Choose the inputs: any data, any frame for it with the Reserved_bit (bit 3) set, any capacity
	size_t n = upto(PTRDIFF_MAX), len, written, completed;
	unsigned char *data = any_bytes(n);
	unsigned char *frame = data == NULL ? NULL : new_frame(data, n, n, STREAM_WINDOW, 0, &len);
	size_t cap = upto(PTRDIFF_MAX);
	unsigned char *dst = malloc(cap);
	ZSTD_DStream *zds = ZSTD_createDStream();
	if (frame == NULL || dst == NULL || zds == NULL)
		return 0;
	frame[4] |= 8;
	// Run zstd. RFC 8878 3.1.1.1.1, Reserved_bit: "A decoder compliant with this specification version must ensure
	// it is not set."
	size_t result = ZSTD_decompress(dst, cap, frame, len);
	size_t last = stream_all(zds, frame, len, dst, cap, &written, &completed);
	if (out_of_memory(result) || out_of_memory(last))
		return 0;
	// Check
	gp_assert(ZSTD_isError(result) && completed == 0);
	return 0;
}
