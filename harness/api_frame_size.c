// Law api_frame_size: For a Zstandard frame built by hand (frames.h, new_frame: any data of any length the allocator
// provides, any header form with a window up to ONE_CALL_WINDOW, any blocks, a checksum or not) or a skippable frame
// (frames.h, new_skippable: any user data up to 2^32 - 1 bytes), followed by any bytes, ZSTD_findFrameCompressedSize
// returns exactly the frame's size.
#include "frames.h"

int main(void) {
	// Choose the inputs: a frame of any data, or a skippable frame; any bytes after it
	size_t n = upto(PTRDIFF_MAX), len, after = upto(PTRDIFF_MAX);
	unsigned char *data = any_bytes(n), *frame;
	if (data == NULL)
		return 0;
	if (nondet_u8() & 1)
		frame = new_skippable(&len);
	else
		frame = new_frame(data, n, n, ONE_CALL_WINDOW, 0, &len);
	unsigned char *src = frame == NULL ? NULL : join(frame, len, any_bytes(after), after);
	if (src == NULL)
		return 0;
	// Run zstd. zstd.h, ZSTD_findFrameCompressedSize: "@return : the compressed size of the first frame starting
	// at `src`"; for skippable frames "it returns the size of the complete skippable frame, which is always equal
	// to its content size + 8 bytes for headers"
	size_t size = ZSTD_findFrameCompressedSize(src, len + after);
	// Check
	gp_assert(size == len);
	return 0;
}
