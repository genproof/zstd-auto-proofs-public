// Law api_reset: A decompression context used in any way (one-shot and streaming decoding of any inputs, dictionaries
// of any bytes, any ZSTD_d_windowLogMax), then reset with ZSTD_DCtx_reset(ZSTD_reset_session_and_parameters), behaves
// like a new one: given the same calls as a new context (one-shot, or any input in any pieces with any output room),
// each call fails in both, or returns the same result, moves the same positions and writes the same bytes in both
// (ZSTD_error_memory_allocation ends the run; which error is reported is not compared: zstd.h documents none).
#include "laws_common.h"

int main(void) {
	ZSTD_DCtx *used = ZSTD_createDCtx(), *fresh = ZSTD_createDCtx();
	ZSTD_inBuffer in, in2;
	ZSTD_outBuffer out, out2;
	size_t n, cap, result, expected;
	unsigned char *src, *dst, *other;
	if (used == NULL || fresh == NULL)
		return 0;
	do {   // Any use: any input, one-shot or in any pieces with any room; any dictionary, any windowLogMax
		n = upto(PTRDIFF_MAX);
		src = any_bytes(n);
		cap = upto(PTRDIFF_MAX);
		dst = malloc(cap);
		if (src == NULL || dst == NULL)
			return 0;
		in.src = src;
		in.size = in.pos = 0;
		out.dst = dst;
		out.pos = 0;
		if (nondet_u8() & 1)
			ZSTD_decompressDCtx(used, dst, cap, src, n);
		else
			do {   // the input so far and any more of it, any room after the output so far
				in.size += upto(n - in.size);
				out.size = out.pos + upto(cap - out.pos);
			} while (!ZSTD_isError(ZSTD_decompressStream(used, &out, &in)) && nondet_u8() != 0);
		ZSTD_DCtx_reset(used, ZSTD_reset_session_only);
		if (nondet_u8() & 1)
			ZSTD_DCtx_loadDictionary(used, src, n);
		ZSTD_DCtx_setParameter(used, ZSTD_d_windowLogMax, (int) nondet_u32());
		free(src);
		free(dst);
	} while (nondet_u8() != 0);
	if (ZSTD_isError(ZSTD_DCtx_reset(used, ZSTD_reset_session_and_parameters)))
		return 0;
	// The same calls on both: any input, any capacity, one-shot or in any pieces with any output room
	n = upto(PTRDIFF_MAX);
	src = any_bytes(n);
	cap = upto(PTRDIFF_MAX);
	dst = malloc(cap);
	other = malloc(cap);
	if (src == NULL || dst == NULL || other == NULL)
		return 0;
	if (nondet_u8() & 1) {
		result = ZSTD_decompressDCtx(used, dst, cap, src, n);
		expected = ZSTD_decompressDCtx(fresh, other, cap, src, n);
		if (out_of_memory(result) || out_of_memory(expected))
			return 0;
		gp_assert(ZSTD_isError(result) ? ZSTD_isError(expected)
		                               : result == expected && bytes_eq(dst, other, result));
		return 0;
	}
	in.src = in2.src = src;
	in.pos = in2.pos = 0;
	out.dst = dst;
	out2.dst = other;
	out.pos = out2.pos = 0;
	do {   // any number of calls, until an error
		in.size = in2.size = in.pos + upto(n - in.pos);         // each call: any more input, any more room
		out.size = out2.size = out.pos + upto(cap - out.pos);
		result = ZSTD_decompressStream(used, &out, &in);
		expected = ZSTD_decompressStream(fresh, &out2, &in2);
		if (out_of_memory(result) || out_of_memory(expected))
			return 0;
		// Check. zstd.h, ZSTD_DCtx_reset: "Return a DCtx to clean state."
		gp_assert(ZSTD_isError(result) ? ZSTD_isError(expected) : result == expected && in.pos == in2.pos &&
		          out.pos == out2.pos && bytes_eq(dst, other, out.pos));
	} while (!ZSTD_isError(result) && nondet_u8() != 0);
	return 0;
}
