// Law res_free: Counted through the allocator it is given (ZSTD_customMem), a decompression context gives back every
// byte it took: after any use (one-shot and streaming decoding of any inputs, dictionaries of any bytes loaded by
// copy, references to several dictionaries, any windowLogMax, resets) and ZSTD_freeDCtx, nothing is left allocated.
#include "laws_common.h"
ZSTD_DCtx *ZSTD_createDCtx_advancedP(const ZSTD_customMem *mem);   // ZSTD_createDCtx_advanced(*mem) (patch/lawhooks.py)

// An allocator that counts the bytes zstd holds. Each block carries its size just in front of it; freeing anything
// else than a block from count_alloc, or one twice, is undefined behaviour here.
static void *count_alloc(void *opaque, size_t size) {
	size_t *now = opaque, *block = size <= PTRDIFF_MAX - sizeof (size_t) ? malloc(sizeof (size_t) + size) : NULL;
	if (block == NULL)
		return NULL;
	block[0] = size;
	*now += size;
	return block + 1;
}
static void count_free(void *opaque, void *address) {
	size_t *now = opaque, *block = (size_t *) address - 1;
	if (address == NULL)
		return;
	*now -= block[0];
	free(block);
}

int main(void) {
	size_t now = 0;
	ZSTD_customMem mem;
	mem.customAlloc = count_alloc;
	mem.customFree = count_free;
	mem.opaque = &now;
	ZSTD_DCtx *dctx = ZSTD_createDCtx_advancedP(&mem);
	ZSTD_DDict *ddict = NULL;
	if (dctx == NULL)
		return 0;
	do {   // Any use: any input, one-shot or in any pieces with any room; dictionaries; parameters; resets
		size_t n = upto(PTRDIFF_MAX), cap = upto(PTRDIFF_MAX);
		unsigned char *src = any_bytes(n), *dst = malloc(cap);
		if (src == NULL || dst == NULL)
			return 0;
		ZSTD_inBuffer in;
		ZSTD_outBuffer out;
		in.src = src;
		in.size = in.pos = 0;
		out.dst = dst;
		out.pos = 0;
		if (nondet_u8() & 1)
			ZSTD_decompressDCtx(dctx, dst, cap, src, n);
		else {
			size_t r;
			do {
				in.size += upto(n - in.size);
				out.size = out.pos + upto(cap - out.pos);
			} while (!ZSTD_isError(r = ZSTD_decompressStream(dctx, &out, &in)) && nondet_u8() != 0);
			if (ZSTD_isError(r))   // zstd.h, after an error: "it must be first reset"
				ZSTD_DCtx_reset(dctx, ZSTD_reset_session_only);
		}
		ZSTD_DCtx_reset(dctx, (ZSTD_ResetDirective) (1 + nondet_u8() % 3));   // session, parameters, or both
		if (nondet_u8() & 1)
			ZSTD_DCtx_loadDictionary(dctx, src, n);
		unsigned char *kept = copy_of(src, n);      // a dictionary of the caller's (not counted; kept)
		if (kept == NULL && n != 0)
			return 0;
		if (ddict == NULL && (nondet_u8() & 1)) {
			ddict = ZSTD_createDDict(kept, n);
			ZSTD_DCtx_setParameter(dctx, ZSTD_d_refMultipleDDicts, nondet_u8() & 1);
			ZSTD_DCtx_refDDict(dctx, ddict);
		}
		ZSTD_DCtx_setParameter(dctx, ZSTD_d_windowLogMax, (int) nondet_u32());
		free(src);
		free(dst);
	} while (nondet_u8() != 0);
	// Run zstd. zstd.h, ZSTD_d_refMultipleDDicts: "ZSTD_freeDCtx() also frees this memory."
	ZSTD_freeDCtx(dctx);
	// Check
	gp_assert(now == 0);
	ZSTD_freeDDict(ddict);
	return 0;
}
