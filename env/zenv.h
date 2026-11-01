/* env/zenv.h: value distributions for native and interpreter runs of the zstd short laws (harness/laws_common.h).
 * Untrusted: it only steers testing; the theorems quantify over every value.  Each env/<law>.c includes it, after
 * defining ENV_CORPUS to 1 for a law that feeds any bytes to the decoder: then a nondet_size draw is often the length
 * of a real frame (env/corpus.h, or an edge case below), the next nondet_bytes of that length gives the frame (maybe
 * mutated), and the nondet_size after it a capacity around its content size (the order of the laws' draws: length,
 * bytes, capacity; sizes drawn between a frame's length and its bytes get any value).  Sizes stay below a few hundred KiB natively (ASan aborts on huge mallocs) and small under
 * CompCert's interpreter. */
#include <stddef.h>
#include <stdint.h>
#include "corpus.h"
extern uint64_t quickproof_rnd(void);
#define rnd quickproof_rnd
#ifndef ENV_CORPUS
#define ENV_CORPUS 0
#endif

#ifdef __COMPCERT__
static const size_t env_sizes[] = { 9, 40, 200, 600 };
#else
static const size_t env_sizes[] = { 17, 600, 70000, 300000 };
#endif

/* Edge cases besides the corpus (as in env.c): empty frames with a compressed block, a declared content
 * size the frame does not hold, a match beyond the window, a frame with a skippable frame. */
static const unsigned char edge0[] = { 0x28,0xB5,0x2F,0xFD, 0x00, 0x00, 0x15,0x00,0x00, 0x00, 0x00 };
static const unsigned char edge1[] = { 0x28,0xB5,0x2F,0xFD, 0x80, 0x00, 0x00,0x00,0x00,0x00, 0x15,0x00,0x00, 0x00, 0x00 };
static const unsigned char edge2[] = { 0x28,0xB5,0x2F,0xFD, 0x20, 0x00, 0x15,0x00,0x00, 0x00, 0x00 };
static const unsigned char edge3[] = { 0x28,0xB5,0x2F,0xFD, 0x20, 0xFD, 0x01,0x00,0x00 };
static const unsigned char edge4[] = { 0x28,0xb5,0x2f,0xfd,0x00,0x00,0x02,0x20,0x00,0x41,0x02,0x20,0x00,0x42,0x22,0x03,0x00,0x43,
	0x8d,0x00,0x00,0x50,'x','y','z','a','b','c','d','e','f','g',0x01,0x00,0x71,0x00,0x20,0x12 };
static const unsigned char edge5[] = { 0x52,0x2A,0x4D,0x18, 0x03,0x00,0x00,0x00, 1,2,3, 0x28,0xB5,0x2F,0xFD, 0x20, 0x02, 0x11,0x00,0x00, 'h','i' };
/* edge6: a frame whose match beyond the window reads the slack of a literal copy after the ring wraps, built
 * on first use; edge7: a declared Frame_Content_Size (100) smaller than the content (one Raw block of 200 bytes) */
static unsigned char edge6[3098];
static const unsigned char edge7[] = { 0x28,0xb5,0x2f,0xfd, 0x80, 0x00, 100,0,0,0, 0x41,0x06,0x00,
	'x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x',
	'x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x',
	'x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x',
	'x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x',
	'x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x',
	'x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x','x',
	'y','y','y','y','y','y','y','y','y','y','y','y','y','y','y','y','y','y','y','y' };
static const unsigned char *edge6_ptr(void)
{
	static const unsigned char hdr[] = { 0x28, 0xb5, 0x2f, 0xfd, 0x00, 0x00 };
	static const unsigned char last[] = { 0x45, 0x00, 0x00, 0x08, 0xbb, 0x01, 0x00, 0xed, 0x00, 0xa0, 0x10 };
	if (edge6[0] == 0) {
		size_t n = 0;
		for (size_t i = 0; i < sizeof hdr; i++) edge6[n++] = hdr[i];
		for (int b = 0; b < 3; b++) {
			edge6[n++] = 0x00; edge6[n++] = 0x20; edge6[n++] = 0x00;
			for (int i = 0; i < 1024; i++) edge6[n++] = (unsigned char) (0x11 + b);
		}
		for (size_t i = 0; i < sizeof last; i++) edge6[n++] = last[i];
	}
	return edge6;
}
/* edge8: one RLE block of 128 KiB (ZSTD_BLOCKSIZE_MAX), the largest block, window 128 KiB */
static const unsigned char edge8[] = { 0x28,0xb5,0x2f,0xfd, 0x00, 0x38, 0x03,0x00,0x10, 'q' };
static const unsigned char *const edge[] = { edge0, edge1, edge2, edge3, edge4, edge5, edge6, edge7, edge8 };
static const unsigned long edge_len[] = { sizeof edge0, sizeof edge1, sizeof edge2, sizeof edge3, sizeof edge4, sizeof edge5,
                                          sizeof edge6, sizeof edge7, sizeof edge8 };
static const unsigned long edge_content[] = { 0, 0, 0, 253, 2161, 2, 3076, 100, 131072 };
#define EDGE_N 9
#define FRAMES_N (CORPUS_N + EDGE_N)
static const unsigned char *frame_ptr(int i) { return i < CORPUS_N ? corpus[i] : i == CORPUS_N + 6 ? edge6_ptr() : edge[i - CORPUS_N]; }
static unsigned long frame_len(int i) { return i < CORPUS_N ? corpus_len[i] : edge_len[i - CORPUS_N]; }
static unsigned long frame_content(int i) { return i < CORPUS_N ? corpus_content[i] : edge_content[i - CORPUS_N]; }

static enum { IDLE, PICKED, EMITTED } env_state = IDLE;
static int env_frame;

static size_t generic_size(void)
{
	unsigned k = (unsigned) (rnd() % 20);
	if (k < 6) return rnd() % env_sizes[0];
	if (k < 12) return rnd() % env_sizes[1];
	if (k < 17) return rnd() % env_sizes[2];
	return rnd() % env_sizes[3];
}

size_t nondet_size(void)
{
	if (ENV_CORPUS && env_state == IDLE && rnd() % 4 != 0) {
		env_frame = (int) (rnd() % FRAMES_N);
		env_state = PICKED;
		return frame_len(env_frame);
	}
	if (env_state == PICKED)                         /* other sizes drawn before the frame's bytes: any */
		return generic_size();
	if (env_state == EMITTED) {
		size_t c = frame_content(env_frame);
		env_state = IDLE;
		switch (rnd() % 5) {
		case 0: case 1: return c;
		case 4: return 0;
		case 2: return c - (c ? rnd() % (c < 40 ? c + 1 : 40) : 0);
		default: return c + rnd() % 64;
		}
	}
	env_state = IDLE;
	return generic_size();
}

void nondet_bytes(uint8_t *buf, size_t n)
{
	if (env_state == PICKED && n == frame_len(env_frame)) {
		for (size_t i = 0; i < n; i++)
			buf[i] = frame_ptr(env_frame)[i];
		if (n > 0 && rnd() % 3 == 0) {
			switch (rnd() % 3) {
			case 0: buf[rnd() % n] ^= (uint8_t) (1u << (rnd() % 8)); break;
			case 1: for (int k = 0; k < 3; k++) buf[rnd() % n] = (uint8_t) rnd(); break;
			default: buf[4 + rnd() % (n > 12 ? 8 : (n > 4 ? n - 4 : 1))] ^= (uint8_t) rnd(); break;
			}
		}
		env_state = EMITTED;
		return;
	}
	env_state = IDLE;
	if (n == 8 && rnd() % 2) {                       /* pick() of a 64-bit value: often a small one */
		uint64_t v = rnd() % (rnd() % 2 ? 300 : 70000);
		for (size_t i = 0; i < 8; i++)
			buf[i] = (uint8_t) (v >> (8 * i));
		return;
	}
	const unsigned kind = (unsigned) (rnd() % 5);
	uint8_t c = (uint8_t) rnd();
	for (size_t i = 0; i < n; i++) {
		if (kind == 1 && rnd() % 50 == 0)
			c = (uint8_t) rnd();                     /* runs of one byte */
		buf[i] = kind == 0 ? (uint8_t) rnd() : kind == 1 ? c : kind == 2 ? (uint8_t) ('a' + rnd() % 4)
		       : kind == 3 ? (uint8_t) (i < 4 ? "\x28\xb5\x2f\xfd"[i] : rnd())   /* a frame's magic number */
		       : (uint8_t) (i < 4 ? "\x37\xa4\x30\xec"[i] : rnd());              /* a dictionary's */
	}
}

/* small values half of the time: flags stay uniform in their low bits, Window_Descriptors small (windows of a few KiB) */
#ifdef __COMPCERT__
/* the interpreter is slow: loops on nondet_u8() != 0 (more frames, more calls) end sooner */
uint8_t nondet_u8(void) { return (uint8_t) (rnd() % 4 == 0 ? 0 : rnd() % 2 ? rnd() % 16 : rnd()); }
#else
uint8_t nondet_u8(void) { return (uint8_t) (rnd() % 2 ? rnd() % 16 : rnd()); }
#endif

/* ENV_U32_WLOG: the law's u32 draws are windowLogMax values: 0 (the default), 10..31 (accepted), or anything */
uint32_t nondet_u32(void)
{
#ifdef ENV_U32_WLOG
	switch (rnd() % 4) {
	case 0: return 0;
	case 1: return (uint32_t) (10 + rnd() % 3);      /* small windows: the buffers the estimates bound */
	case 2: return (uint32_t) (10 + rnd() % 18);
	default: return (uint32_t) rnd();
	}
#else
	switch (rnd() % 4) {
	case 0: return (uint32_t) (rnd() % 8);
	case 1: return (uint32_t) (rnd() % 64);
	default: return (uint32_t) rnd();
	}
#endif
}
