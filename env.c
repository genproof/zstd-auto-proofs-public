// Value distributions for native and interpreter runs of the zstd harnesses.  They override the framework's
// generic nondet_* (quickproof/runtime/fuzz_driver.c, interp_driver.c).  Random bytes rarely get past a frame
// header, so most runs decode a real frame (harness/corpus.h), often mutated, into a capacity around its
// content size (or 0).  This relies on the harnesses' draw order n, bytes, cap:
//   nondet_size  (idle)    -> pick a frame, return its length
//   nondet_bytes (picked)  -> that frame, maybe mutated, when the length still matches
//   nondet_size  (emitted) -> a capacity: the frame's content size, a little less or more, or anything
// Other calls get generic values.  Chunk sizes and the like come from nondet_u32.
#include <stddef.h>
#include <stdint.h>
#include "harness/corpus.h"
extern uint64_t quickproof_rnd(void);
#define rnd quickproof_rnd

static enum { IDLE, PICKED, EMITTED } state = IDLE;
static int frame;

/* Edge cases besides the corpus: empty frames with a compressed block (output capacity 0: a counterexample found while proving),
 * a declared content size the frame does not hold, a match beyond the window. */
static const unsigned char edge0[] = { 0x28,0xB5,0x2F,0xFD, 0x00, 0x00, 0x15,0x00,0x00, 0x00, 0x00 };
static const unsigned char edge1[] = { 0x28,0xB5,0x2F,0xFD, 0x80, 0x00, 0x00,0x00,0x00,0x00, 0x15,0x00,0x00, 0x00, 0x00 };
static const unsigned char edge2[] = { 0x28,0xB5,0x2F,0xFD, 0x20, 0x00, 0x15,0x00,0x00, 0x00, 0x00 };
static const unsigned char edge3[] = { 0x28,0xB5,0x2F,0xFD, 0x20, 0xFD, 0x01,0x00,0x00 };
static const unsigned char edge4[] = { 0x28,0xb5,0x2f,0xfd,0x00,0x00,0x02,0x20,0x00,0x41,0x02,0x20,0x00,0x42,0x22,0x03,0x00,0x43,
	0x8d,0x00,0x00,0x50,'x','y','z','a','b','c','d','e','f','g',0x01,0x00,0x71,0x00,0x20,0x12 };
static const unsigned char *const edge[] = { edge0, edge1, edge2, edge3, edge4 };
static const unsigned long edge_len[] = { sizeof edge0, sizeof edge1, sizeof edge2, sizeof edge3, sizeof edge4 };
static const unsigned long edge_content[] = { 0, 0, 0, 253, 2161 };
#define EDGE_N 5
#define FRAMES_N (CORPUS_N + EDGE_N)
static const unsigned char *frame_ptr(int i) { return i < CORPUS_N ? corpus[i] : edge[i - CORPUS_N]; }
static unsigned long frame_len(int i) { return i < CORPUS_N ? corpus_len[i] : edge_len[i - CORPUS_N]; }
static unsigned long frame_content(int i) { return i < CORPUS_N ? corpus_content[i] : edge_content[i - CORPUS_N]; }

static size_t generic_size(void)
{
	switch (rnd() % 4) {
	case 0: return rnd() % 16;
	case 1: return rnd() % 512;
	case 2: return rnd() % 70000;
	default: return (size_t) rnd();
	}
}

size_t nondet_size(void)
{
	if (state == IDLE && rnd() % 4 != 0) {
		frame = (int) (rnd() % FRAMES_N);
		state = PICKED;
		return frame_len(frame);
	}
	if (state == EMITTED) {
		size_t c = frame_content(frame);
		state = IDLE;
		switch (rnd() % 5) {
		case 0: case 1: return c;
		case 4: return 0;
		case 2: return c - (c ? rnd() % (c < 40 ? c + 1 : 40) : 0);
		default: return c + rnd() % 64;
		}
	}
	state = IDLE;
	return generic_size();
}

void nondet_bytes(uint8_t *buf, size_t n)
{
	if (state == PICKED && n == frame_len(frame)) {
		for (size_t i = 0; i < n; i++)
			buf[i] = frame_ptr(frame)[i];
		if (n > 0 && rnd() % 3 == 0) {
			switch (rnd() % 3) {
			case 0: buf[rnd() % n] ^= (uint8_t) (1u << (rnd() % 8)); break;
			case 1: for (int k = 0; k < 3; k++) buf[rnd() % n] = (uint8_t) rnd(); break;
			default: buf[4 + rnd() % (n > 12 ? 8 : (n > 4 ? n - 4 : 1))] ^= (uint8_t) rnd(); break;
			}
		}
		state = EMITTED;
		return;
	}
	state = IDLE;
	const unsigned kind = rnd() % 3;
	for (size_t i = 0; i < n; i++)
		buf[i] = kind == 0 ? (uint8_t) rnd() : kind == 1 ? 0 : (uint8_t) (i < 4 ? "\x28\xb5\x2f\xfd"[i] : rnd());
}

uint8_t nondet_u8(void) { return (uint8_t) rnd(); }

uint32_t nondet_u32(void)
{
	switch (rnd() % 4) {
	case 0: return (uint32_t) (rnd() % 8);
	case 1: return (uint32_t) (rnd() % 64);
	default: return (uint32_t) rnd();
	}
}
