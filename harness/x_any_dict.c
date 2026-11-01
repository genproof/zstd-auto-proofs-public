// Law any_dict (PROMISES.md: S1, S2, S3, S6): dictionaries are untrusted input ("If a dictionary is provided by an
// external source, it should be loaded with great care, its content considered untrusted"): ANY dictionary bytes and
// ANY frame bytes, through the dictionary APIs that use the caller's dictionary by reference.
//
// Claim (QuickProof.Contract.harness_safe of this program): no execution has undefined behaviour, and every gp_assert
// holds: every decompression returns an error or a size <= the capacity; ZSTD_freeDDict accepts NULL.  The APIs:
// 0 ZSTD_decompress_usingDict; 1 ZSTD_createDDict_byReference + ZSTD_decompress_usingDDict; 2
// ZSTD_DCtx_loadDictionary_byReference, sticky: two decompressions; 3 ZSTD_createDDict_byReference +
// ZSTD_DCtx_refDDict; 4 ZSTD_DCtx_refPrefix.  The output and the dictionary are two regions of one allocation
// [dst | 1 byte | dict]: zstd compares the output pointer with the end of the dictionary (ZSTD_checkContinuity),
// which CompCert's C semantics (the theorems') defines only within one object; the APIs that copy the dictionary
// are in any_dict_copy.  Draw order n, bytes, cap, then the dictionary's size and bytes (env.c).
#include <stdlib.h>
#include "quickproof.h"
#define ZSTD_STATIC_LINKING_ONLY   /* the _byReference functions */
#include "zstd.h"

#define SRC_MAX 4096
#define DST_MAX 65536
#define DICT_MAX 4096

int main(void)
{
	size_t n = nondet_size(), cap, dn, r;
	unsigned char *src, *buf, *dst, *dict;
	unsigned api = nondet_u32() % 5, k, rounds;
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
	buf = malloc(cap + 1 + dn);
	dctx = ZSTD_createDCtx();
	rounds = (buf != NULL && dctx != NULL) ? (api == 2 ? 2 : 1) : 0;
	dst = buf;
	dict = NULL;
	if (buf != NULL)
		dict = buf + cap + 1;     /* not on NULL: NULL + n is undefined (C11 6.5.6p8) */
	if (rounds > 0) {
		nondet_bytes(dict, dn);
		(void) ZSTD_getDictID_fromDict(dict, dn);
		if (api == 1 || api == 3) {
			ddict = ZSTD_createDDict_byReference(dict, dn);
			if (ddict == NULL)
				rounds = 0;
			else
				(void) ZSTD_getDictID_fromDDict(ddict);
		}
	}
	for (k = 0; k < rounds; k++) {
		if (api == 0) {
			r = ZSTD_decompress_usingDict(dctx, dst, cap, src, n, dict, dn);
		} else if (api == 1) {
			r = ZSTD_decompress_usingDDict(dctx, dst, cap, src, n, ddict);
		} else {
			r = 0;
			if (k == 0)
				r = api == 2 ? ZSTD_DCtx_loadDictionary_byReference(dctx, dict, dn)
				    : api == 3 ? ZSTD_DCtx_refDDict(dctx, ddict) : ZSTD_DCtx_refPrefix(dctx, dict, dn);
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
	free(buf);
	return 0;
}
