// Law rj_any_input: For any input (any bytes, any length the allocator provides) and any output capacity (input and
// output each an object of exactly that size), ZSTD_decompress, and ZSTD_decompressDCtx called any number of times on
// one context (also after an error), return an error code or "the number of bytes decompressed into `dst` (<=
// `dstCapacity`)" (zstd.h, ZSTD_decompress). With the theorem's "no undefined behaviour", this is the protection
// against a malicious frame.
#include "laws_common.h"

int main(void) {
	ZSTD_DCtx *dctx = ZSTD_createDCtx();
	if (dctx == NULL)
		return 0;
	do {
		// Each call: any input, any capacity, one of the two functions
		size_t n = upto(PTRDIFF_MAX);
		unsigned char *src = any_bytes(n);
		size_t cap = upto(PTRDIFF_MAX);
		unsigned char *dst = malloc(cap);
		if (src == NULL || dst == NULL)
			return 0;
		size_t result = (nondet_u8() & 1) ? ZSTD_decompress(dst, cap, src, n)
		                                  : ZSTD_decompressDCtx(dctx, dst, cap, src, n);
		// Check. zstd.h, ZSTD_decompressDCtx: "Same as ZSTD_decompress()"
		gp_assert(ZSTD_isError(result) || result <= cap);
		free(src);
		free(dst);
	} while (nondet_u8() != 0);
	ZSTD_freeDCtx(dctx);
	return 0;
}
