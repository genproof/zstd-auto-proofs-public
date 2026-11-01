// Law bound (PROMISES.md: C6): the compression bound of zstd.h.
//
// Claim (QuickProof.Contract.harness_safe of this program): every gp_assert holds: for ANY sizes A, B >= 128 KB with
// A + B < ZSTD_MAX_INPUT_SIZE, "bound(A) + bound(B) <= bound(A+B)" (ZSTD_COMPRESSBOUND: "this formula ensures that
// bound(A) + bound(B) <= bound(A+B) as long as A and B >= 128 KB").  (ZSTD_compressBound, the function, is the
// compressor's, which this project does not verify.)
#include "quickproof.h"
#include "zstd.h"

int main(void)
{
	size_t a = nondet_size(), b = nondet_size();
	if (a >= (128 << 10) && b >= (128 << 10) && a < ZSTD_MAX_INPUT_SIZE && b < ZSTD_MAX_INPUT_SIZE - a)
		gp_assert(ZSTD_COMPRESSBOUND(a) + ZSTD_COMPRESSBOUND(b) <= ZSTD_COMPRESSBOUND(a + b));
	return 0;
}
