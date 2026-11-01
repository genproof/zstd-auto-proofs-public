// Law res_memory_oneshot: Counted through the allocator it is given (ZSTD_customMem), a decompression context never
// holds more than ZSTD_estimateDCtxSize() bytes while it decodes any inputs (any bytes, any lengths the allocator
// provides) into any capacities one-shot, any number of times: zstd.h, ZSTD_d_windowLogMax: "no internal buffer is
// allocated in single-pass mode"; ZSTD_estimate*(): "These functions make it possible to estimate memory usage of a
// future {D,C}Ctx, before its creation."
#include "laws_common.h"
ZSTD_DCtx *ZSTD_createDCtx_advancedP(const ZSTD_customMem *mem);   // ZSTD_createDCtx_advanced(*mem) (patch/lawhooks.py)

// An allocator that counts the bytes zstd holds now and at most. Each block carries its size just in front of it;
// freeing anything else than a block from count_alloc, or one twice, is undefined behaviour here.
struct count {
	size_t now, peak;
};
static void *count_alloc(void *opaque, size_t size) {
	struct count *count = opaque;
	size_t *block = size <= PTRDIFF_MAX - sizeof (size_t) ? malloc(sizeof (size_t) + size) : NULL;
	if (block == NULL)
		return NULL;
	block[0] = size;
	count->now += size;
	if (count->now > count->peak)
		count->peak = count->now;
	return block + 1;
}
static void count_free(void *opaque, void *address) {
	struct count *count = opaque;
	size_t *block = (size_t *) address - 1;
	if (address == NULL)
		return;
	count->now -= block[0];
	free(block);
}

int main(void) {
	struct count count;
	ZSTD_customMem mem;
	count.now = count.peak = 0;
	mem.customAlloc = count_alloc;
	mem.customFree = count_free;
	mem.opaque = &count;
	ZSTD_DCtx *dctx = ZSTD_createDCtx_advancedP(&mem);
	if (dctx == NULL)
		return 0;
	do {   // Each call: any input, any capacity
		size_t n = upto(PTRDIFF_MAX), cap = upto(PTRDIFF_MAX);
		unsigned char *src = any_bytes(n), *dst = malloc(cap);
		if (src == NULL || dst == NULL)
			return 0;
		ZSTD_decompressDCtx(dctx, dst, cap, src, n);
		free(src);
		free(dst);
	} while (nondet_u8() != 0);
	// Check
	gp_assert(count.peak <= ZSTD_estimateDCtxSize());
	ZSTD_freeDCtx(dctx);
	return 0;
}
