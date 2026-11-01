// Law res_memory_stream: Counted through the allocator it is given (ZSTD_customMem), a decompression context with
// ZSTD_d_windowLogMax set to any value zstd accepts (0: the default, 2^ZSTD_WINDOWLOG_LIMIT_DEFAULT bytes) never holds
// more than ZSTD_estimateDStreamSize(2^windowLogMax) bytes while it decodes any input (any bytes, any length the
// allocator provides) in any pieces with any output room, reset after errors: zstd.h, ZSTD_d_windowLogMax: "a size
// limit (in power of 2) beyond which the streaming API will refuse to allocate memory buffer"; ZSTD_estimate*(): "The
// ZSTD_DStream memory budget depends on frame's window Size. This information can be passed manually, using
// ZSTD_estimateDStreamSize".
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
	int window_log = (int) nondet_u32();
	ZSTD_DCtx *dctx = ZSTD_createDCtx_advancedP(&mem);
	if (dctx == NULL || ZSTD_isError(ZSTD_DCtx_setParameter(dctx, ZSTD_d_windowLogMax, window_log)))
		return 0;
	size_t n = upto(PTRDIFF_MAX), cap = upto(PTRDIFF_MAX);
	unsigned char *src = any_bytes(n), *dst = malloc(cap);
	if (src == NULL || dst == NULL)
		return 0;
	ZSTD_inBuffer in;
	ZSTD_outBuffer out;
	in.src = src;
	in.size = 0;
	in.pos = 0;
	out.dst = dst;
	out.pos = 0;
	do {   // Each call: the input so far and any more of it, any room after the output so far
		in.size += upto(n - in.size);
		out.size = out.pos + upto(cap - out.pos);
		if (ZSTD_isError(ZSTD_decompressStream(dctx, &out, &in)))   // zstd.h, after an error: "it must be first
			ZSTD_DCtx_reset(dctx, ZSTD_reset_session_only);     // reset"
	} while (nondet_u8() != 0);
	// Check
	size_t max_window = (size_t) 1 << (window_log == 0 ? ZSTD_WINDOWLOG_LIMIT_DEFAULT : window_log);
	gp_assert(count.peak <= ZSTD_estimateDStreamSize(max_window));
	ZSTD_freeDCtx(dctx);
	return 0;
}
