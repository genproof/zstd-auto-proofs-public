// Law any_info (PROMISES.md: S1, I1-I6): the frame-inspection functions on ANY bytes.
//
// Claim (QuickProof.Contract.harness_safe of this program): no execution has undefined behaviour, and every gp_assert
// holds, as zstd.h documents:
//   ZSTD_findFrameCompressedSize: an error, or the size of a frame within src (<= srcSize);
//   ZSTD_getFrameHeader: 0 (the header is complete: headerSize <= srcSize), or "> 0 => srcSize is too small, @return
//     value is the wanted srcSize amount" (> srcSize), or an error;
//   ZSTD_isFrame, ZSTD_isSkippableFrame: "If `size < 4`, @return will always be 0" (isFrame);
//   ZSTD_readSkippableFrame: an error or "number of bytes written" (<= dstCapacity);
//   ZSTD_getFrameContentSize, ZSTD_findDecompressedSize, ZSTD_decompressBound, ZSTD_frameHeaderSize,
//   ZSTD_getDictID_fromFrame: any value (only safety).
// Draw order n, bytes, cap (env.c).
#include <stdlib.h>
#include "quickproof.h"
#define ZSTD_STATIC_LINKING_ONLY   /* the experimental inspection functions */
#include "zstd.h"

#define SRC_MAX 4096
#define DST_MAX 65536

int main(void)
{
	size_t n = nondet_size(), cap, r;
	unsigned char *src, *dst;
	unsigned variant = 0;
	ZSTD_FrameHeader zfh;
	gp_assume(n <= SRC_MAX);
	src = malloc(n);
	if (src == NULL)
		return 0;                       /* harness out of memory: end the run */
	nondet_bytes(src, n);
	cap = nondet_size();
	gp_assume(cap <= DST_MAX);
	dst = malloc(cap);
	if (dst == NULL) {
		free(src);
		return 0;
	}
	r = ZSTD_findFrameCompressedSize(src, n);
	if (!ZSTD_isError(r))
		gp_assert(r <= n);
	r = ZSTD_getFrameHeader(&zfh, src, n);
	if (!ZSTD_isError(r)) {
		if (r == 0)
			gp_assert(zfh.headerSize <= n);
		else
			gp_assert(r > n);
	}
	if (n < 4) {
		gp_assert(ZSTD_isFrame(src, n) == 0);
		gp_assert(ZSTD_isSkippableFrame(src, n) == 0);
	} else {
		(void) ZSTD_isFrame(src, n);
		(void) ZSTD_isSkippableFrame(src, n);
	}
	r = ZSTD_readSkippableFrame(dst, cap, &variant, src, n);
	if (!ZSTD_isError(r))
		gp_assert(r <= cap);
	(void) ZSTD_getFrameContentSize(src, n);
	(void) ZSTD_findDecompressedSize(src, n);
	(void) ZSTD_decompressBound(src, n);
	(void) ZSTD_frameHeaderSize(src, n);
	(void) ZSTD_getDictID_fromFrame(src, n);
	free(src);
	free(dst);
	return 0;
}
