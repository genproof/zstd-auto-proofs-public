// Law any_dict_copy (PROMISES.md: S1, S2, S3, S6): ANY dictionary bytes and ANY frame bytes through the dictionary APIs
// that copy the dictionary: 1 ZSTD_createDDict + ZSTD_decompress_usingDDict; 2 ZSTD_DCtx_loadDictionary, sticky: two
// decompressions; 3 ZSTD_createDDict + ZSTD_DCtx_refDDict.
//
// Claim (QuickProof.Contract.harness_safe of this program): no execution has undefined behaviour, and every gp_assert
// holds: every decompression returns an error or a size <= the capacity; ZSTD_freeDDict accepts NULL.
// zstd compares the output pointer with the end of its own copy of the dictionary, which CompCert's semantics
// cannot do; the patch's VST layer skips that comparison for a copied dictionary (patch/GENPROOF-PATCH.md, gpDictCopy).
// Draw order n, bytes, cap, then the dictionary's size and bytes (env.c).
#include <stdlib.h>
#include "quickproof.h"
#include "zstd.h"

#define SRC_MAX 4096
#define DST_MAX 65536
#define DICT_MAX 4096

int main(void)
{
	size_t n = nondet_size(), cap, dn, r;
	unsigned char *src, *dst, *dict;
	unsigned api = 1 + nondet_u32() % 3, k, rounds;
	ZSTD_DCtx *dctx;
	ZSTD_DDict *ddict = NULL;
	gp_assume(n <= SRC_MAX);
	src = malloc(n > 0 ? n : 1);
	if (src == NULL)
		return 0;                       /* harness out of memory: end the run */
	nondet_bytes(src, n);
	cap = nondet_size();
	gp_assume(cap <= DST_MAX);
	dn = nondet_size();
	gp_assume(dn <= DICT_MAX);
	dst = malloc(cap > 0 ? cap : 1);
	dict = malloc(dn > 0 ? dn : 1);
	dctx = ZSTD_createDCtx();
	rounds = (dst != NULL && dict != NULL && dctx != NULL) ? (api == 2 ? 2 : 1) : 0;
	if (rounds > 0) {
		nondet_bytes(dict, dn);
		if (api != 2) {
			ddict = ZSTD_createDDict(dict, dn);
			if (ddict == NULL)
				rounds = 0;
		}
	}
	for (k = 0; k < rounds; k++) {
		if (api == 1) {
			r = ZSTD_decompress_usingDDict(dctx, dst, cap, src, n, ddict);
		} else {
			r = 0;
			if (k == 0)
				r = api == 2 ? ZSTD_DCtx_loadDictionary(dctx, dict, dn) : ZSTD_DCtx_refDDict(dctx, ddict);
			if (!ZSTD_isError(r))
				r = ZSTD_decompressDCtx(dctx, dst, cap, src, n);
		}
		if (!ZSTD_isError(r))
			gp_assert(r <= cap);
	}
	ZSTD_freeDCtx(dctx);
	ZSTD_freeDDict(ddict);
	ZSTD_freeDDict(NULL);
	free(src);
	free(dst);
	free(dict);
	return 0;
}
