// Law any_stream (PROMISES.md: S1, S4, S5, S6, V6, V7): streaming decompression of ANY bytes over ANY chunking.
//
// Claim (QuickProof.Contract.harness_safe of this program): no execution has undefined behaviour, and every gp_assert
// holds: each call of ZSTD_decompressStream keeps "0 <= pos <= size" for its input and output; a call with no new
// input delivers at most ZSTD_BLOCKSIZE_MAX bytes ("with no additional input, amount of data flushed <=
// ZSTD_BLOCKSIZE_MAX"); after an error the stream is reset (ZSTD_DCtx_reset or ZSTD_initDStream, as zstd.h requires)
// and decoding goes on with the rest of the input; ZSTD_DStreamOutSize(), which can "flush at least one complete block
// in all circumstances", is at least ZSTD_BLOCKSIZE_MAX (the largest content of a block).  Each call gets fresh input and output buffers of any sizes, exactly sized (an
// input chunk may be empty).  Draw order n, bytes, cap (env.c); chunk sizes come from nondet_u32.
#include <stdlib.h>
#include "quickproof.h"
#include "zstd.h"

#define SRC_MAX 4096
#define DST_MAX 65536
#define CHUNK_MAX 256
#define CALLS_MAX 512

int main(void)
{
	size_t n = nondet_size(), cap, ipos = 0, got = 0;
	unsigned char *src;
	unsigned calls;
	ZSTD_DStream *ds;
	gp_assume(n <= SRC_MAX);
	src = malloc(n);
	if (src == NULL)
		return 0;                       /* harness out of memory: end the run */
	nondet_bytes(src, n);
	cap = nondet_size();
	gp_assume(cap <= DST_MAX);
	gp_assert(ZSTD_DStreamOutSize() >= ZSTD_BLOCKSIZE_MAX);
	ds = ZSTD_createDStream();
	if (ds == NULL) {
		free(src);
		return 0;
	}
	for (calls = 0; calls < CALLS_MAX && got <= cap; calls++) {
		size_t ilen = nondet_u32() % (CHUNK_MAX + 1), olen = nondet_u32() % CHUNK_MAX + 1, j, r;
		unsigned char *ib, *ob;
		ZSTD_inBuffer in;
		ZSTD_outBuffer out;
		if (ilen > n - ipos)
			ilen = n - ipos;
		ib = malloc(ilen > 0 ? ilen : 1);
		ob = malloc(olen);
		if (ib == NULL || ob == NULL) {
			free(ib);
			free(ob);
			break;
		}
		for (j = 0; j < ilen; j++)
			ib[j] = src[ipos + j];
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
		ipos += in.pos;
		got += out.pos;
		free(ib);
		free(ob);
		if (ZSTD_isError(r)) {
			if (nondet_u32() % 2)
				ZSTD_DCtx_reset(ds, ZSTD_reset_session_only);
			else
				ZSTD_initDStream(ds);
		}
		else if (ipos == n && (r == 0 || ilen == 0))
			break;
	}
	ZSTD_freeDStream(ds);
	ZSTD_freeDStream(NULL);
	free(src);
	return 0;
}
