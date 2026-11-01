// Law api_short_output: A Zstandard frame built by hand (frames.h, new_frame: any data of any length the allocator
// provides, at least one byte, any header form with a window up to ONE_CALL_WINDOW, any blocks, a checksum or not),
// given to ZSTD_decompress with any capacity smaller than its content, is refused with ZSTD_error_dstSize_tooSmall,
// never decoded in part (ZSTD_error_memory_allocation ends the run).
#include "frames.h"

int main(void) {
	// Choose the inputs: any data (at least one byte), any frame for it, any capacity below the data's size
	size_t n = upto(PTRDIFF_MAX), len;
	unsigned char *data = any_bytes(n);
	unsigned char *frame = data == NULL ? NULL : new_frame(data, n, n, ONE_CALL_WINDOW, 0, &len);
	size_t cap = n == 0 ? 0 : upto(n - 1);
	unsigned char *dst = malloc(cap);
	if (frame == NULL || n == 0 || (dst == NULL && cap != 0))
		return 0;
	// Run zstd. zstd.h, ZSTD_decompress: "`dstCapacity` is an upper bound of originalSize to regenerate";
	// "@return : the number of bytes decompressed into `dst` (<= `dstCapacity`), or an errorCode if it fails"
	size_t result = ZSTD_decompress(dst, cap, frame, len);
	if (out_of_memory(result))
		return 0;
	// Check
	gp_assert(ZSTD_getErrorCode(result) == ZSTD_error_dstSize_tooSmall);
	return 0;
}
