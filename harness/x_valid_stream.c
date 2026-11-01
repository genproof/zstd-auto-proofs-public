// Law valid_stream (PROMISES.md: V1-V6, S4, S5): ANY series of compliant frames (harness/writer.h) decoded by
// ZSTD_decompressStream with ANY input and output chunks.
//
// Claim (QuickProof.Contract.harness_safe of this program): no execution has undefined behaviour, and every gp_assert
// holds: every byte delivered is the series' content at that position; a call returns 0 only at the end of a frame
// with all of the frame's content delivered ("0 when a frame is completely decoded and fully flushed"); a positive
// return asks for no more input than remains of the current frame ("will never request more than the remaining
// content of the compressed frame"; at least 1 when only flushing remains); "0 <= pos <= size"; a call with no new
// input delivers at most ZSTD_BLOCKSIZE_MAX bytes; no call fails unless a frame's window is beyond the streaming
// default, memory cannot be allocated, or it is the 16th call in a row without progress (zlimits.h, stall_error:
// zstd's deliberate busy-loop guard).  Each call gets fresh buffers of exactly its chunk sizes.
#include <stdlib.h>
#include "quickproof.h"
#include "writer.h"
#include "zlimits.h"

#define CALLS_MAX 4096

static wseries_t sr;

static size_t chunk(size_t max)
{
	unsigned c = choose(4);
	size_t lim = c == 0 ? 16 : c == 1 ? 512 : c == 2 ? 70000 : max;
	return choose_in(0, lim < max ? lim : max);
}

int main(void)
{
	size_t ipos = 0, got = 0, calls, stalled = 0;   /* stalled: calls in a row that read and wrote nothing */
	ZSTD_DStream *ds;
	w_series(&sr, 0);
	ds = ZSTD_createDStream();
	if (ds == NULL)
		return 0;                       /* out of memory: zstd.h allows it */
	for (calls = 0; calls < CALLS_MAX; calls++) {
		size_t ilen = chunk(sr.n - ipos), olen = 1 + chunk(W_CONTENT_MAX), j, r;
		unsigned char *ib = exact_copy(sr.bytes + ipos, ilen), *ob = malloc(olen);
		ZSTD_inBuffer in;
		ZSTD_outBuffer out;
		unsigned k;
		if (ib == NULL || ob == NULL) {
			free(ib);
			free(ob);
			break;                      /* harness out of memory: end the run */
		}
		in.src = ib;
		in.size = ilen;
		in.pos = 0;
		out.dst = ob;
		out.size = olen;
		out.pos = 0;
		r = ZSTD_decompressStream(ds, &out, &in);
		gp_assert(in.pos <= in.size);
		gp_assert(out.pos <= out.size);
		if (ilen == 0)
			gp_assert(out.pos <= ZSTD_BLOCKSIZE_MAX);
		for (j = 0; j < out.pos; j++) {
			gp_assert(got + j < sr.content_n);
			gp_assert(ob[j] == sr.content[got + j]);
		}
		got += out.pos;
		ipos += in.pos;
		free(ib);
		free(ob);
		if (ZSTD_isError(r)) {
			gp_assert(!within_stream(&sr) || ZSTD_getErrorCode(r) == ZSTD_error_memory_allocation
			          || stall_error(ZSTD_getErrorCode(r), stalled, &in, &out, 0));
			break;
		}
		stalled = in.pos == 0 && out.pos == 0 ? stalled + 1 : 0;
		if (r == 0) {
			int at_end = 0;
			for (k = 0; k < sr.nframes; k++)
				if (sr.f[k].start + sr.f[k].size == ipos && got == sr.f[k].cstart + sr.f[k].csize)
					at_end = 1;
			gp_assert(at_end);
			if (ipos == sr.n)
				break;
		} else {
			size_t end = sr.n;
			for (k = sr.nframes; k > 0; k--) {   /* the current frame: the first not yet decoded and delivered */
				size_t e = sr.f[k - 1].start + sr.f[k - 1].size;
				if (e > ipos || (e == ipos && got < sr.f[k - 1].cstart + sr.f[k - 1].csize))
					end = e;
			}
			gp_assert(r <= (end - ipos > 0 ? end - ipos : 1));
		}
	}
	ZSTD_freeDStream(ds);
	return 0;
}
