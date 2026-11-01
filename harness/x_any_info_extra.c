// Law any_info_extra (PROMISES.md: S1, I7, I8): the inspection functions not in any_info, on ANY bytes:
//   ZSTD_getDecompressedSize (obsolete, stable API): "Both functions work the same way, but ZSTD_getDecompressedSize()
//     blends "empty", "unknown" and "error" results to the same return value (0), while ZSTD_getFrameContentSize()
//     gives them separate return values" (I7);
//   ZSTD_getFrameHeader_advanced (experimental): "same as ZSTD_getFrameHeader(), with added capability to select a
//     format (like ZSTD_f_zstd1_magicless)" (I8).
//
// Claim (QuickProof.Contract.harness_safe of this program): no execution has undefined behaviour, and every gp_assert
// holds: ZSTD_getDecompressedSize is ZSTD_getFrameContentSize with ZSTD_CONTENTSIZE_UNKNOWN and ZSTD_CONTENTSIZE_ERROR
// mapped to 0; ZSTD_getFrameHeader_advanced with ZSTD_f_zstd1 returns what ZSTD_getFrameHeader returns, and on 0 the
// same header fields; with ZSTD_f_zstd1_magicless it returns 0 (with headerSize <= srcSize), or "> 0 => srcSize is
// too small, @return value is the wanted srcSize amount" (> srcSize), or an error.  Draw order n, bytes (env.c).
#include <stdlib.h>
#include "quickproof.h"
#ifndef ZSTD_STATIC_LINKING_ONLY
#define ZSTD_STATIC_LINKING_ONLY   /* ZSTD_getFrameHeader_advanced */
#endif
#include "zstd.h"

#define SRC_MAX 4096

int main(void)
{
	size_t n = nondet_size(), r, r2;
	unsigned char *src;
	unsigned long long fcs, ds;
	ZSTD_FrameHeader h1, h2;
	gp_assume(n <= SRC_MAX);
	src = malloc(n > 0 ? n : 1);
	if (src == NULL)
		return 0;                       /* harness out of memory: end the run */
	nondet_bytes(src, n);
	fcs = ZSTD_getFrameContentSize(src, n);
	ds = ZSTD_getDecompressedSize(src, n);
	gp_assert(ds == ((fcs == ZSTD_CONTENTSIZE_UNKNOWN || fcs == ZSTD_CONTENTSIZE_ERROR) ? 0 : fcs));
	r = ZSTD_getFrameHeader(&h1, src, n);
	r2 = ZSTD_getFrameHeader_advanced(&h2, src, n, ZSTD_f_zstd1);
	gp_assert(r2 == r);
	if (r == 0) {
		gp_assert(h2.frameContentSize == h1.frameContentSize);
		gp_assert(h2.windowSize == h1.windowSize);
		gp_assert(h2.blockSizeMax == h1.blockSizeMax);
		gp_assert(h2.frameType == h1.frameType);
		gp_assert(h2.headerSize == h1.headerSize);
		gp_assert(h2.dictID == h1.dictID);
		gp_assert(h2.checksumFlag == h1.checksumFlag);
	}
	r = ZSTD_getFrameHeader_advanced(&h2, src, n, ZSTD_f_zstd1_magicless);
	if (r == 0)
		gp_assert(h2.headerSize <= n);
	else if (!ZSTD_isError(r))
		gp_assert(r > n);
	free(src);
	return 0;
}
