// The limits under which zstd may refuse a compliant frame, as its documents state them (PROMISES.md V4): "a decoder
// is allowed to reject a compressed frame which requests a memory size beyond decoder's authorized range"
// (format), zstd's range being ZSTD_WINDOWLOG_MAX (31 on 64-bit: zstd.h) for any decoding and, for streaming,
// "By default, a decompression context accepts window sizes <= (1 << ZSTD_WINDOWLOG_LIMIT_DEFAULT)" (zstd.h);
// the memory allocation of its contexts; and, for streaming, zstd's deliberate busy-loop guard (stall_error).
#ifndef ZSTD_HARNESS_ZLIMITS_H
#define ZSTD_HARNESS_ZLIMITS_H
#include "writer.h"
#ifndef ZSTD_STATIC_LINKING_ONLY
#define ZSTD_STATIC_LINKING_ONLY   /* ZSTD_WINDOWLOG_MAX, ZSTD_WINDOWLOG_LIMIT_DEFAULT */
#endif
#include "zstd.h"
#include "zstd_errors.h"

/* every Zstandard frame of the series is within zstd's window range (single-segment: Window_Size = content size) */
static int within_oneshot(const wseries_t *sr)
{
	unsigned k;
	for (k = 0; k < sr->nframes; k++)
		if (!sr->f[k].skippable && !sr->f[k].single && sr->f[k].window_log > ZSTD_WINDOWLOG_MAX)
			return 0;
	return 1;
}

/* ... and within the streaming default */
static int within_stream(const wseries_t *sr)
{
	unsigned k;
	for (k = 0; k < sr->nframes; k++)
		if (!sr->f[k].skippable && sr->f[k].window > (1ULL << ZSTD_WINDOWLOG_LIMIT_DEFAULT))
			return 0;
	return within_oneshot(sr);
}

/* zstd's busy-loop guard, deliberate (commit 31769ce70 "error on no forward progress": a caller "may be caught in an
   infinite loop, calling the streaming decompression function again and again, without making any progress";
   db18a62f8 gave it its error codes): ZSTD_decompressStream fails on the ZSTD_NO_FORWARD_PROGRESS_MAX-th (16 by
   default) call in a row that reads no input and writes no output, with noForwardProgress_destFull if the output is
   full, else noForwardProgress_inputEmpty (the input is then empty).  zstd.h does not document it.  True iff error
   code e is that error, legitimately: this call (fresh input, output position opos0 before it) read and wrote
   nothing, and so did the `stalled` calls in a row before it. */
#define NO_PROGRESS_MAX 16
static int stall_error(ZSTD_ErrorCode e, size_t stalled, const ZSTD_inBuffer *in, const ZSTD_outBuffer *out,
                       size_t opos0)
{
	if (stalled + 1 < NO_PROGRESS_MAX || in->pos != 0 || out->pos != opos0)
		return 0;
	if (e == ZSTD_error_noForwardProgress_destFull)
		return out->pos == out->size;
	return e == ZSTD_error_noForwardProgress_inputEmpty && out->pos < out->size && in->pos == in->size;
}

/* a copy of b[0..n) in a buffer of exactly n bytes (NULL: out of memory) */
static unsigned char *exact_copy(const unsigned char *b, size_t n)
{
	unsigned char *p = malloc(n > 0 ? n : 1);
	size_t i;
	if (p != NULL)
		for (i = 0; i < n; i++)
			p[i] = b[i];
	return p;
}
#endif
