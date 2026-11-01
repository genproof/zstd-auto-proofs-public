// Law rj_any_dict: For any dictionary and any input (any bytes, any lengths the allocator provides) and any output
// capacity, ZSTD_decompress_usingDict, called any number of times on one context, returns an error code or a size at
// most the capacity (RFC 8878 5: "If a dictionary is provided by an external source, it should be loaded with great
// care, its content considered untrusted"). The dictionary and the output are one object, with any gap between them:
// zstd compares the output's start with the dictionary's end, which CompCert's C defines only within one object.
#include "laws_common.h"

int main(void) {
	ZSTD_DCtx *dctx = ZSTD_createDCtx();
	if (dctx == NULL)
		return 0;
	do {
		// Each call: any input; any dictionary, gap and capacity, laid out as dictionary, gap, output
		size_t n = upto(PTRDIFF_MAX), dict_len = upto(PTRDIFF_MAX), gap = upto(PTRDIFF_MAX);
		size_t cap = upto(PTRDIFF_MAX);
		unsigned char *src = any_bytes(n), *both = NULL;
		if (dict_len <= PTRDIFF_MAX - gap && dict_len + gap <= PTRDIFF_MAX - cap)
			both = any_bytes(dict_len + gap + cap);
		if (src == NULL || both == NULL)
			return 0;
		size_t result = ZSTD_decompress_usingDict(dctx, both + dict_len + gap, cap, src, n, both, dict_len);
		// Check. zstd.h, ZSTD_decompress: "@return : the number of bytes decompressed into `dst` (<=
		// `dstCapacity`), or an errorCode if it fails"
		gp_assert(ZSTD_isError(result) || result <= cap);
		free(src);
		free(both);
	} while (nondet_u8() != 0);
	ZSTD_freeDCtx(dctx);
	return 0;
}
