// Law api_ignore_checksum: With ZSTD_d_forceIgnoreChecksum set to ZSTD_d_ignoreChecksum, a Zstandard frame built by
// hand with a Content_Checksum of any value (frames.h, new_frame: any data of any length the allocator provides, any
// header form with a window up to ONE_CALL_WINDOW, any blocks; then any checksum) decodes with ZSTD_decompressDCtx,
// with any capacity that holds it, to exactly its content (ZSTD_error_memory_allocation ends the run).
#include "frames.h"

int main(void) {
	// Choose the inputs: any data, any frame for it, any checksum value, any capacity for the data
	size_t n = upto(PTRDIFF_MAX), len;
	unsigned char *data = any_bytes(n);
	unsigned char *frame = data == NULL ? NULL : new_frame(data, n, n, ONE_CALL_WINDOW, 0, &len);
	size_t cap = n + upto(PTRDIFF_MAX - n);
	unsigned char *dst = malloc(cap);
	ZSTD_DCtx *dctx = ZSTD_createDCtx();
	if (frame == NULL || dst == NULL || dctx == NULL || !(frame[4] & 4) ||
	    ZSTD_isError(ZSTD_DCtx_setParameter(dctx, ZSTD_d_forceIgnoreChecksum, ZSTD_d_ignoreChecksum)))
		return 0;
	put_le(frame + len - 4, nondet_u32(), 4);
	// Run zstd. zstd.h, ZSTD_d_forceIgnoreChecksum: "Tells the decompressor to skip checksum validation during
	// decompression, regardless of whether checksumming was specified during compression."
	size_t result = ZSTD_decompressDCtx(dctx, dst, cap, frame, len);
	if (out_of_memory(result))
		return 0;
	// Check
	gp_assert(result == n && bytes_eq(dst, data, n));
	return 0;
}
