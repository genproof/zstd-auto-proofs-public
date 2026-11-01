// Law stable_out (PROMISES.md: S7, V12; zstd's experimental API): ZSTD_d_stableOutBuffer, decoding into one output
// buffer the caller never changes ("the ZSTD_outBuffer will ALWAYS be the same between calls").
//
// Claim (QuickProof.Contract.harness_safe of this program): no execution has undefined behaviour, and every gp_assert
// holds: (a) on ANY bytes, over ANY input chunks, into a buffer of ANY size: "this flag is ALWAYS memory safe, and will
// never access out-of-bounds memory", and "0 <= pos <= size" (after an error the stream is reset); (b) on ANY series
// of compliant frames, into a buffer that holds its content ("MUST be large enough to fit the entire decompressed
// frame"): every byte written is the content, no call fails unless zlimits.h (window, memory, or the 16th call in a
// row without progress: stall_error), and a 0 return at the end of the series comes with the whole content.  Draw order for (a): n, bytes, cap (env.c).
#include <stdlib.h>
#include "quickproof.h"
#include "writer.h"
#include "zlimits.h"

#define SRC_MAX 4096
#define DST_MAX 65536
#define CALLS_MAX 4096

static wseries_t sr;

int main(void)
{
	int valid = choose(2);
	size_t n, cap, ipos = 0, calls, i, r, stalled = 0;   /* stalled: calls in a row that read and wrote nothing */
	unsigned char *src, *dst;
	ZSTD_DStream *ds;
	ZSTD_outBuffer out;
	if (valid) {
		w_series(&sr, 0);
		n = sr.n;
		src = exact_copy(sr.bytes, n);
		cap = choose_in(sr.content_n, sr.content_n + 16);
	} else {
		n = nondet_size();
		gp_assume(n <= SRC_MAX);
		src = malloc(n > 0 ? n : 1);
		if (src != NULL)
			nondet_bytes(src, n);
		cap = nondet_size();
		gp_assume(cap <= DST_MAX);
	}
	dst = malloc(cap > 0 ? cap : 1);
	ds = ZSTD_createDStream();
	if (src == NULL || dst == NULL || ds == NULL || ZSTD_isError(ZSTD_DCtx_setParameter(ds, ZSTD_d_stableOutBuffer, 1)))
		n = 0;                          /* out of memory: end the run */
	out.dst = dst;
	out.size = cap;
	out.pos = 0;
	for (calls = 0; n > 0 && calls < CALLS_MAX; calls++) {
		size_t ilen = choose_in(0, n - ipos), pos0 = out.pos;
		unsigned char *ib = exact_copy(src + ipos, ilen);
		ZSTD_inBuffer in;
		if (ib == NULL)
			break;
		in.src = ib;
		in.size = ilen;
		in.pos = 0;
		r = ZSTD_decompressStream(ds, &out, &in);
		gp_assert(in.pos <= in.size);
		gp_assert(out.pos <= out.size);
		ipos += in.pos;
		free(ib);
		if (valid) {
			for (i = pos0; i < out.pos; i++) {
				gp_assert(i < sr.content_n);
				gp_assert(dst[i] == sr.content[i]);
			}
			if (ZSTD_isError(r)) {
				gp_assert(!within_stream(&sr) || ZSTD_getErrorCode(r) == ZSTD_error_memory_allocation
				          || stall_error(ZSTD_getErrorCode(r), stalled, &in, &out, pos0));
				break;
			}
			stalled = in.pos == 0 && out.pos == pos0 ? stalled + 1 : 0;
			if (r == 0 && ipos == n) {
				gp_assert(out.pos == sr.content_n);
				break;
			}
		} else if (ZSTD_isError(r)) {
			ZSTD_DCtx_reset(ds, ZSTD_reset_session_only);
			out.pos = 0;
		} else if (ipos == n && (r == 0 || ilen == 0)) {
			break;
		}
	}
	ZSTD_freeDStream(ds);
	free(src);
	free(dst);
	return 0;
}
