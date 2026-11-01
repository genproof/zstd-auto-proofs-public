// A writer of ANY compliant zstd data, written from the format specification (doc/zstd_compression_format.md,
// = RFC 8878; section names below) and independent of the library's code: series of Zstandard and skippable
// frames, and dictionaries.  Every choice comes from nondet (choose); a law that decodes what the writer wrote
// checks the decoder against the specification.  The writer covers every block type, every literals mode (raw,
// RLE, Huffman with a new tree described directly or with FSE-compressed weights, treeless; 1 or 4 streams),
// every sequence table mode (predefined, RLE, FSE-compressed, repeat), repeat offsets, every frame header form,
// dictionary IDs, checksums (its own XXH64), and raw-content or formatted dictionaries.
//
// gp_assume restricts choices to compliant data (a choice that cannot give a compliant frame is not a frame);
// gp_assert states the writer's own invariants (the proof shows them).  Two facts about FSE tables are assumed,
// not proved: from any state of the next symbol there is a state of the current one leading to it, and every
// symbol has a state that reads at least one bit (both hold of every table built from a distribution).
#ifndef ZSTD_HARNESS_WRITER_H
#define ZSTD_HARNESS_WRITER_H
#include <stddef.h>
#include <stdint.h>
#include "quickproof.h"

/* bounds of what the laws draw (the format allows more; the proof is symbolic in these) */
#define W_CONTENT_MAX (1u << 18)       /* the content of a series */
#define W_OUT_MAX     (1u << 19)       /* the bytes of a series */
#define W_FRAMES_MAX  4
#define W_BLOCKS_MAX  6
#define W_SEQ_MAX     (1u << 16)
#define W_DICT_MAX    (1u << 12)       /* dictionary content */
#define W_SKIP_MAX    64               /* skippable user data */

/* any value in [0, k), k >= 1 */
static unsigned choose(unsigned k)
{
	return nondet_u32() % k;
}

/* any value in [lo, hi] */
static size_t choose_in(size_t lo, size_t hi)
{
	gp_assert(lo <= hi);
	return lo + (size_t) (nondet_u32() % (unsigned) (hi - lo + 1));
}

/* floor(log2(x)), x >= 1 */
static unsigned highbit(unsigned long long x)
{
	unsigned r = 0;
	while (x > 1) {
		x >>= 1;
		r++;
	}
	return r;
}

/* ---------------------------------------------------------------------------------------------------------- */
/* bytes and bitstreams */

typedef struct {
	unsigned char *p;
	size_t n;
	size_t cap;
} out_t;

static void put8(out_t *o, unsigned v)
{
	gp_assume(o->n < o->cap);          /* data that does not fit the harness's buffers is not drawn */
	o->p[o->n] = (unsigned char) (v & 255);
	o->n++;
}

static void put_le(out_t *o, unsigned long long v, unsigned k)
{
	unsigned i;
	for (i = 0; i < k; i++)
		put8(o, (unsigned) ((v >> (8 * i)) & 255));
}

static void put_bytes(out_t *o, const unsigned char *b, size_t k)
{
	size_t i;
	for (i = 0; i < k; i++)
		put8(o, b[i]);
}

/* bit fields, least significant bit first.  A forward bitstream (FSE table descriptions) is read in the order
 * written and padded to a byte; a backward one (Huffman streams, sequences, Huffman weights) is read from its end,
 * so its fields are put in the reverse of the reading order, then the end mark (Huffman-coded Streams) */
typedef struct {
	out_t *o;
	unsigned long long acc;
	unsigned bits;
} bits_t;

static void bits_put(bits_t *b, unsigned long long v, unsigned nb)
{
	gp_assert(nb <= 32 && b->bits < 8);
	gp_assert(v < (1ULL << nb));
	b->acc |= v << b->bits;
	b->bits += nb;
	while (b->bits >= 8) {
		put8(b->o, (unsigned) (b->acc & 255));
		b->acc >>= 8;
		b->bits -= 8;
	}
}

static void bits_end_mark(bits_t *b)
{
	b->acc |= 1ULL << b->bits;
	put8(b->o, (unsigned) (b->acc & 255));
	b->acc = 0;
	b->bits = 0;
}

static void bits_pad(bits_t *b)
{
	if (b->bits > 0)
		put8(b->o, (unsigned) (b->acc & 255));
	b->acc = 0;
	b->bits = 0;
}

/* ---------------------------------------------------------------------------------------------------------- */
/* XXH64 (seed 0), for Content_Checksum: the xxHash specification, independent of the library's copy */

#define XP1 0x9E3779B185EBCA87ULL
#define XP2 0xC2B2AE3D27D4EB4FULL
#define XP3 0x165667B19E3779F9ULL
#define XP4 0x85EBCA77C2B2AE63ULL
#define XP5 0x27D4EB2F165667C5ULL

static unsigned long long xrotl(unsigned long long x, unsigned r)
{
	return (x << r) | (x >> (64 - r));
}

static unsigned long long xread(const unsigned char *p, unsigned k)
{
	unsigned long long v = 0;
	unsigned i;
	for (i = 0; i < k; i++)
		v |= (unsigned long long) p[i] << (8 * i);
	return v;
}

static unsigned long long xround(unsigned long long acc, unsigned long long in)
{
	acc += in * XP2;
	acc = xrotl(acc, 31);
	return acc * XP1;
}

static unsigned long long xmerge(unsigned long long h, unsigned long long v)
{
	h ^= xround(0, v);
	return h * XP1 + XP4;
}

static unsigned long long xxh64(const unsigned char *p, size_t len)
{
	size_t i = 0;
	unsigned long long h;
	if (len >= 32) {
		unsigned long long v1 = XP1 + XP2, v2 = XP2, v3 = 0, v4 = 0 - XP1;
		for (; i + 32 <= len; i += 32) {
			v1 = xround(v1, xread(p + i, 8));
			v2 = xround(v2, xread(p + i + 8, 8));
			v3 = xround(v3, xread(p + i + 16, 8));
			v4 = xround(v4, xread(p + i + 24, 8));
		}
		h = xrotl(v1, 1) + xrotl(v2, 7) + xrotl(v3, 12) + xrotl(v4, 18);
		h = xmerge(h, v1);
		h = xmerge(h, v2);
		h = xmerge(h, v3);
		h = xmerge(h, v4);
	} else {
		h = XP5;
	}
	h += (unsigned long long) len;
	for (; i + 8 <= len; i += 8) {
		h ^= xround(0, xread(p + i, 8));
		h = xrotl(h, 27) * XP1 + XP4;
	}
	if (i + 4 <= len) {
		h ^= xread(p + i, 4) * XP1;
		h = xrotl(h, 23) * XP2 + XP3;
		i += 4;
	}
	for (; i < len; i++) {
		h ^= (unsigned long long) p[i] * XP5;
		h = xrotl(h, 11) * XP1;
	}
	h ^= h >> 33;
	h *= XP2;
	h ^= h >> 29;
	h *= XP3;
	h ^= h >> 32;
	return h;
}

/* ---------------------------------------------------------------------------------------------------------- */
/* FSE (FSE Table Description; From normalized distribution to decoding tables) */

#define FSE_LOG_MAX 9
#define FSE_SYM_MAX 53

typedef struct {
	short norm[FSE_SYM_MAX];           /* probabilities of symbols 0..nsym-1; -1: "less than 1" */
	unsigned nsym;
	unsigned log;                      /* accuracy log; 0 for an RLE table */
	unsigned char sym[1 << FSE_LOG_MAX];
	unsigned char nb[1 << FSE_LOG_MAX];
	unsigned short base[1 << FSE_LOG_MAX];
} fse_t;

/* the decoding table of the distribution in t->norm */
static void fse_build(fse_t *t)
{
	unsigned size = 1U << t->log, high = size - 1, pos = 0, step = (size >> 1) + (size >> 3) + 3;
	unsigned next[FSE_SYM_MAX];
	unsigned s, i, state;
	for (s = 0; s < t->nsym; s++) {
		if (t->norm[s] == -1) {
			t->sym[high] = (unsigned char) s;
			high--;
			next[s] = 1;
		} else {
			next[s] = (unsigned) t->norm[s];
		}
	}
	for (s = 0; s < t->nsym; s++) {
		if (t->norm[s] > 0) {
			for (i = 0; i < (unsigned) t->norm[s]; i++) {
				t->sym[pos] = (unsigned char) s;
				pos = (pos + step) & (size - 1);
				while (pos > high)
					pos = (pos + step) & (size - 1);
			}
		}
	}
	for (state = 0; state < size; state++) {
		unsigned x = next[t->sym[state]];
		unsigned nb = t->log - highbit(x);
		next[t->sym[state]] = x + 1;
		t->nb[state] = (unsigned char) nb;
		t->base[state] = (unsigned short) ((x << nb) - size);
	}
}

/* the one-state table of RLE_Mode */
static void fse_rle(fse_t *t, unsigned symbol)
{
	t->nsym = symbol + 1;
	t->log = 0;
	t->sym[0] = (unsigned char) symbol;
	t->nb[0] = 0;
	t->base[0] = 0;
}

/* does the table give symbol s a state */
static int fse_has(const fse_t *t, unsigned s)
{
	if (t->log == 0)
		return t->sym[0] == s;
	return s < t->nsym && t->norm[s] != 0;
}

/* any distribution of accuracy log `log` over symbols 0..maxsym in which every symbol with need[s] has a non-zero
 * probability, and at least two symbols have one ("There must be two or more symbols with non-zero
 * probabilities"); the described symbols end with the one that completes the total 1 << log */
static void fse_pick(fse_t *t, unsigned log, unsigned maxsym, const unsigned char *need)
{
	int remaining = 1 << log;
	unsigned s, nonzero = 0, left = 0;
	gp_assert(log <= FSE_LOG_MAX && maxsym < FSE_SYM_MAX);
	for (s = 0; s <= maxsym; s++)
		left += need[s] ? 1 : 0;
	gp_assume(left + (left < 2 ? 2 - left : 0) <= (unsigned) remaining);   /* room for them at this accuracy */
	t->log = log;
	for (s = 0; remaining > 0; s++) {
		unsigned slots_after = maxsym - s, last = (s == maxsym);
		int reserve, options[3], nopt = 0, kind, p;
		gp_assert(s <= maxsym);
		if (need[s])
			left--;
		/* points to keep for later symbols if s gets a non-zero probability */
		reserve = (int) left;
		if (nonzero + 1 + left < 2)
			reserve += (int) (2 - (nonzero + 1 + left));
		if (!need[s] && !last && nonzero + slots_after >= 2
		    && remaining >= (int) left + (int) (nonzero + left < 2 ? 2 - (nonzero + left) : 0))
			options[nopt++] = 0;                           /* probability 0 */
		if (remaining - 1 >= reserve && (!last || remaining == 1))
			options[nopt++] = 1;                           /* probability -1 */
		if (remaining - reserve >= 1 && (!last || reserve == 0))
			options[nopt++] = 2;                           /* a positive probability */
		gp_assert(nopt > 0);
		kind = options[choose((unsigned) nopt)];
		if (kind == 0) {
			p = 0;
		} else if (kind == 1) {
			p = -1;
		} else {
			p = last ? remaining : (int) choose_in(1, (size_t) (remaining - reserve));
		}
		t->norm[s] = (short) p;
		remaining -= p < 0 ? 1 : p;
		if (p != 0)
			nonzero++;
	}
	t->nsym = s;
	gp_assert(nonzero >= 2);
	fse_build(t);
}

/* the table description (FSE Table Description): Accuracy_Log - 5 in 4 bits, then the probabilities as values
 * (probability + 1) in the variable-size fields, a probability 0 followed by 2-bit repeat flags for further zeros */
static void fse_put_description(out_t *o, const fse_t *t)
{
	bits_t b = { o, 0, 0 };
	int remaining = 1 << t->log;
	unsigned s = 0;
	bits_put(&b, t->log - 5, 4);
	while (s < t->nsym) {
		int p = t->norm[s];
		unsigned val = (unsigned) (p + 1);
		unsigned bits = highbit((unsigned long long) remaining + 1) + 1;
		unsigned lower_mask = (1U << (bits - 1)) - 1;
		unsigned threshold = (1U << bits) - 1 - (unsigned) (remaining + 1);
		if (val < threshold)
			bits_put(&b, val, bits - 1);
		else if (val <= lower_mask)
			bits_put(&b, val, bits);
		else
			bits_put(&b, val + threshold, bits);
		remaining -= p < 0 ? 1 : p;
		s++;
		if (p == 0) {
			unsigned z = 0;
			while (s + z < t->nsym && t->norm[s + z] == 0)
				z++;
			s += z;
			while (z >= 3) {
				bits_put(&b, 3, 2);
				z -= 3;
			}
			bits_put(&b, z, 2);
		}
	}
	gp_assert(remaining == 0);
	bits_pad(&b);
}

/* states for the symbols c[0..k) (k >= 1) read in this order by one FSE state: the last is any state of c[k-1];
 * going backwards, c[i]'s state is the one whose range [base, base + 2^nb) holds the next state */
static void fse_states(const fse_t *t, const unsigned char *c, size_t k, unsigned short *st)
{
	unsigned size = 1U << t->log, s, n = 0, pick;
	size_t i;
	for (s = 0; s < size; s++)
		if (t->sym[s] == c[k - 1])
			n++;
	gp_assert(n > 0);
	pick = choose(n);
	for (s = 0; s < size; s++) {
		if (t->sym[s] == c[k - 1]) {
			if (pick == 0)
				st[k - 1] = (unsigned short) s;
			pick--;
		}
	}
	i = k - 1;
	while (i > 0) {
		unsigned found = 0;
		i--;
		for (s = 0; s < size; s++) {
			if (t->sym[s] == c[i] && t->base[s] <= st[i + 1] && st[i + 1] - t->base[s] < (1U << t->nb[s])) {
				st[i] = (unsigned short) s;
				found = 1;
			}
		}
		gp_assume(found);   /* a property of FSE tables (header) */
	}
}

/* the predefined distributions (Default Distributions) */
static const short pre_LL[36] = { 4, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 2,
                                  1, 1, 1, 1, 1, -1, -1, -1, -1 };
static const short pre_ML[53] = { 1, 4, 3, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
                                  1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, -1, -1, -1, -1, -1, -1 };
static const short pre_OF[29] = { 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, -1,
                                  -1, -1, -1 };

static void fse_predefined(fse_t *t, unsigned type)
{
	const short *n = type == 0 ? pre_LL : type == 1 ? pre_OF : pre_ML;
	unsigned k = type == 0 ? 36 : type == 1 ? 29 : 53, s;
	for (s = 0; s < k; s++)
		t->norm[s] = n[s];
	t->nsym = k;
	t->log = type == 1 ? 5 : 6;
	fse_build(t);
}

/* ---------------------------------------------------------------------------------------------------------- */
/* Huffman (Huffman Tree Description; Conversion from weights to Huffman prefix codes) */

#define HUF_LOG_MAX 11

typedef struct {
	unsigned char w[256];              /* weight; 0: the symbol is absent */
	unsigned short code[256];
	unsigned char nb[256];
	unsigned last;                     /* the highest present symbol: its weight is not described */
	unsigned log;                      /* Max_Number_of_Bits */
	unsigned char used[256];
	unsigned nused;
} huf_t;

/* any prefix code of 2 to 256 symbols with codes of at most 11 bits: the leaf depths of a full binary tree (grown by
 * splitting leaves), in any order, given to any increasing symbols; then the codes of the specification: symbols by
 * increasing weight, then value, each taking 2^(weight-1) cells */
static void huf_pick(huf_t *h)
{
	unsigned char depth[256];
	unsigned leaves = 1, t, splits, i, s, w, cell;
	depth[0] = 0;
	splits = 1 + choose(255);
	for (t = 0; t < splits; t++) {
		unsigned j = choose(leaves);
		if (depth[j] < HUF_LOG_MAX && leaves < 256) {
			depth[j]++;
			depth[leaves] = depth[j];
			leaves++;
		}
	}
	for (i = leaves; i > 1; i--) {                   /* any order */
		unsigned j = choose(i);
		unsigned char d = depth[i - 1];
		depth[i - 1] = depth[j];
		depth[j] = d;
	}
	h->log = 0;
	for (i = 0; i < leaves; i++)
		if (depth[i] > h->log)
			h->log = depth[i];
	for (s = 0; s < 256; s++)
		h->w[s] = 0;
	s = choose(257 - leaves);                        /* any increasing symbols */
	for (i = 0; i < leaves; i++) {
		gp_assert(s <= 255);
		h->w[s] = (unsigned char) (h->log + 1 - depth[i]);
		h->used[i] = (unsigned char) s;
		h->last = s;
		if (i + 1 < leaves)
			s += 1 + choose(256 - s - (leaves - i - 1));
	}
	h->nused = leaves;
	cell = 0;
	for (w = 1; w <= h->log; w++) {
		for (s = 0; s <= h->last; s++) {
			if (h->w[s] == w) {
				h->nb[s] = (unsigned char) (h->log + 1 - w);
				h->code[s] = (unsigned short) (cell >> (w - 1));
				cell += 1U << (w - 1);
			}
		}
	}
	gp_assert(cell == 1U << h->log);
}

/* the weights of symbols 0..last-1 FSE-compressed (Finite State Entropy (FSE) compression of Huffman weights): a
 * table description, then one backward bitstream with two interleaved states, State1 for the even-indexed weights,
 * State2 for the odd ones.  Decoding stops at the first state update that needs more bits than remain, then gives the
 * other state's symbol: so the stream holds the two initial states and the updates after weights 0..N-3, and the
 * state of weight N-2 reads at least one bit */
static void huf_put_fse_weights(out_t *o, const huf_t *h)
{
	static fse_t t;
	static unsigned char need[FSE_SYM_MAX];
	static unsigned char wv[256];
	static unsigned short st[256 + 2];
	unsigned n = h->last, i, s, size, cnt, pick;
	bits_t b = { o, 0, 0 };
	gp_assert(n >= 2 && n <= 255);
	for (s = 0; s < FSE_SYM_MAX; s++)
		need[s] = 0;
	for (i = 0; i < n; i++) {
		wv[i] = h->w[i];
		need[h->w[i]] = 1;
	}
	fse_pick(&t, 5 + choose(2), HUF_LOG_MAX, need);
	fse_put_description(o, &t);
	size = 1U << t.log;
	/* the last state of each chain: weight n-1 any, weight n-2 one that reads at least one bit */
	cnt = 0;
	for (s = 0; s < size; s++)
		if (t.sym[s] == wv[n - 1])
			cnt++;
	pick = choose(cnt);
	for (s = 0; s < size; s++)
		if (t.sym[s] == wv[n - 1]) {
			if (pick == 0)
				st[n - 1] = (unsigned short) s;
			pick--;
		}
	cnt = 0;
	for (s = 0; s < size; s++)
		if (t.sym[s] == wv[n - 2] && t.nb[s] > 0)
			cnt++;
	gp_assume(cnt > 0);   /* a property of FSE tables (header) */
	pick = choose(cnt);
	for (s = 0; s < size; s++)
		if (t.sym[s] == wv[n - 2] && t.nb[s] > 0) {
			if (pick == 0)
				st[n - 2] = (unsigned short) s;
			pick--;
		}
	i = n - 2;
	while (i > 0) {                                  /* backwards along each chain: st[i] leads to st[i + 2] */
		unsigned found = 0;
		i--;
		for (s = 0; s < size; s++) {
			if (t.sym[s] == wv[i] && t.base[s] <= st[i + 2] && st[i + 2] - t.base[s] < (1U << t.nb[s])) {
				st[i] = (unsigned short) s;
				found = 1;
			}
		}
		gp_assume(found);   /* a property of FSE tables (header) */
	}
	/* reading order: State1 (st[0]), State2 (st[1]), then the update after weight i, from st[i] to st[i+2], for
	 * i = 0..n-3; written in reverse */
	i = n - 2;
	while (i > 0) {
		i--;
		bits_put(&b, st[i + 2] - t.base[st[i]], t.nb[st[i]]);
	}
	bits_put(&b, st[1], t.log);
	bits_put(&b, st[0], t.log);
	bits_end_mark(&b);
}

/* the tree description: a header byte, then the weights of symbols 0..last-1, directly (header 127 + count, two
 * weights per byte, the first in the high nibble; only when last <= 128) or FSE-compressed (header = its size,
 * < 128; at least 2 weights) */
static void huf_put_description(out_t *o, const huf_t *h)
{
	static unsigned char tmp[512];
	unsigned direct_ok = h->last <= 128, fse_ok = h->last >= 2, use_fse, j;
	gp_assert(direct_ok || fse_ok);
	use_fse = !direct_ok ? 1 : !fse_ok ? 0 : choose(2);
	if (use_fse) {
		out_t t = { tmp, 0, sizeof tmp };
		huf_put_fse_weights(&t, h);
		gp_assume(t.n <= 127);                       /* else this tree cannot be described with FSE */
		put8(o, (unsigned) t.n);
		put_bytes(o, tmp, t.n);
	} else {
		put8(o, 127 + h->last);
		for (j = 0; j < h->last; j += 2) {
			unsigned lo = (j + 1 < h->last) ? h->w[j + 1] : 0;
			put8(o, ((unsigned) h->w[j] << 4) | lo);
		}
	}
}

/* one Huffman-coded stream of lit[0..k): read from the end, lit[0] first */
static void huf_put_stream(out_t *o, const huf_t *h, const unsigned char *lit, size_t k)
{
	bits_t b = { o, 0, 0 };
	size_t i = k;
	while (i > 0) {
		i--;
		gp_assert(h->w[lit[i]] != 0);
		bits_put(&b, h->code[lit[i]], h->nb[lit[i]]);
	}
	bits_end_mark(&b);
}

/* ---------------------------------------------------------------------------------------------------------- */
/* literals sections (Literals Section) */

/* raw literals lit[0..k) (type 0), or lit[0] k times (type 1), any header form that holds k */
static void put_literals_raw_rle(out_t *o, unsigned type, const unsigned char *lit, size_t k)
{
	unsigned forms[3], nforms = 0, f;
	if (k <= 31)
		forms[nforms++] = 0;
	if (k <= 4095)
		forms[nforms++] = 1;
	if (k <= 1048575)
		forms[nforms++] = 2;
	gp_assert(nforms > 0);
	f = forms[choose(nforms)];
	if (f == 0)
		put8(o, type | (unsigned) (k << 3));                                              /* Size_Format x0 */
	else if (f == 1)
		put_le(o, type | (1U << 2) | ((unsigned long long) k << 4), 2);                  /* Size_Format 01 */
	else
		put_le(o, type | (3U << 2) | ((unsigned long long) k << 4), 3);                  /* Size_Format 11 */
	if (type == 0)
		put_bytes(o, lit, k);
	else
		put8(o, k > 0 ? lit[0] : choose(256));
}

/* Huffman literals lit[0..k): type 2 (with the tree description) or 3 (treeless: the previous tree), 1 stream or 4
 * (each stream (k+3)/4 literals, the last up to 3 fewer; "Regenerated_Size ... (6-1023)": k >= 6), any header form that
 * holds the sizes */
static void put_literals_huf(out_t *o, unsigned type, const huf_t *h, const unsigned char *lit, size_t k)
{
	static unsigned char tmp[W_OUT_MAX / 2];
	out_t body = { tmp, 0, sizeof tmp };
	unsigned can4 = (k >= 6), streams4, forms[3], nforms = 0, form, bitsz;   /* 4 streams: Regenerated_Size 6.. (Size_Format 01-11) */
	size_t c;
	streams4 = !can4 ? 0 : (k > 1023) ? 1 : choose(2);
	if (type == 2)
		huf_put_description(&body, h);
	if (!streams4) {
		huf_put_stream(&body, h, lit, k);
	} else {
		size_t seg = (k + 3) / 4, at, s1, s2, s3, j;
		at = body.n;
		for (j = 0; j < 6; j++)
			put8(&body, 0);                          /* the jump table, filled below */
		s1 = body.n;
		huf_put_stream(&body, h, lit, seg);
		s2 = body.n;
		huf_put_stream(&body, h, lit + seg, seg);
		s3 = body.n;
		huf_put_stream(&body, h, lit + 2 * seg, seg);
		c = body.n;
		huf_put_stream(&body, h, lit + 3 * seg, k - 3 * seg);
		gp_assume(s2 - s1 <= 65535 && s3 - s2 <= 65535 && c - s3 <= 65535);
		tmp[at + 0] = (unsigned char) ((s2 - s1) & 255);
		tmp[at + 1] = (unsigned char) ((s2 - s1) >> 8);
		tmp[at + 2] = (unsigned char) ((s3 - s2) & 255);
		tmp[at + 3] = (unsigned char) ((s3 - s2) >> 8);
		tmp[at + 4] = (unsigned char) ((c - s3) & 255);
		tmp[at + 5] = (unsigned char) ((c - s3) >> 8);
	}
	c = body.n;                                      /* Compressed_Size */
	if (!streams4) {
		gp_assume(k <= 1023 && c <= 1023);           /* the one-stream form */
		forms[nforms++] = 0;
	} else {
		if (k <= 1023 && c <= 1023)
			forms[nforms++] = 1;
		if (k <= 16383 && c <= 16383)
			forms[nforms++] = 2;
		if (k <= 262143 && c <= 262143)
			forms[nforms++] = 3;
		gp_assume(nforms > 0);
	}
	form = forms[choose(nforms)];
	bitsz = (form <= 1) ? 10 : (form == 2) ? 14 : 18;
	put_le(o, type | (form << 2) | ((unsigned long long) k << 4) | ((unsigned long long) c << (4 + bitsz)),
	       (form <= 1) ? 3 : (form == 2) ? 4 : 5);
	put_bytes(o, tmp, c);
}

/* ---------------------------------------------------------------------------------------------------------- */
/* sequences (Sequences Section; The codes for literals lengths, match lengths, and offsets; Repeat offsets) */

static const unsigned W_LL_base[36] = { 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22, 24, 28,
                                      32, 40, 48, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536 };
static const unsigned char W_LL_bits[36] = { 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 3, 3,
                                           4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16 };
static const unsigned W_ML_base[53] = { 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
                                      24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 37, 39, 41, 43, 47, 51, 59, 67,
                                      83, 99, 131, 259, 515, 1027, 2051, 4099, 8195, 16387, 32771, 65539 };
static const unsigned char W_ML_bits[53] = { 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                                           0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 3, 3, 4, 4, 5, 7, 8, 9, 10, 11,
                                           12, 13, 14, 15, 16 };

#define OF_CODE_MAX 31     /* the reference decoder supports offset codes up to 31 (Offset codes) */

static unsigned ll_code(size_t ll)
{
	unsigned c = 35;
	while (W_LL_base[c] > ll)
		c--;
	return c;
}

static unsigned ml_code(size_t ml)
{
	unsigned c = 52;
	while (W_ML_base[c] > ml)
		c--;
	return c;
}

/* the state of one frame's decoding that later blocks depend on */
typedef struct {
	unsigned rep[3];
	huf_t huf;                         /* the last Huffman tree (Treeless_Literals_Block) */
	int have_huf;
	fse_t tab[3];                      /* the last sequence tables (Repeat_Mode): LL, OF, ML */
	int have_tab;
} wstate_t;

/* copies element by element (VST has no struct assignment) */
static void fse_copy(fse_t *d, const fse_t *s)
{
	unsigned i;
	for (i = 0; i < FSE_SYM_MAX; i++)
		d->norm[i] = s->norm[i];
	d->nsym = s->nsym;
	d->log = s->log;
	for (i = 0; i < (1U << FSE_LOG_MAX); i++) {
		d->sym[i] = s->sym[i];
		d->nb[i] = s->nb[i];
		d->base[i] = s->base[i];
	}
}

static void huf_copy(huf_t *d, const huf_t *s)
{
	unsigned i;
	for (i = 0; i < 256; i++) {
		d->w[i] = s->w[i];
		d->code[i] = s->code[i];
		d->nb[i] = s->nb[i];
		d->used[i] = s->used[i];
	}
	d->last = s->last;
	d->log = s->log;
	d->nused = s->nused;
}

static void wstate_copy(wstate_t *d, const wstate_t *s)
{
	unsigned i;
	for (i = 0; i < 3; i++) {
		d->rep[i] = s->rep[i];
		fse_copy(&d->tab[i], &s->tab[i]);
	}
	huf_copy(&d->huf, &s->huf);
	d->have_huf = s->have_huf;
	d->have_tab = s->have_tab;
}

/* ---------------------------------------------------------------------------------------------------------- */
/* dictionaries (Dictionary Format) */

#define ZSTD_DICT_MAGIC 0xEC30A437U

typedef struct {
	unsigned char bytes[W_DICT_MAX + 2048];
	size_t n;
	int formatted;
	unsigned id;
	const unsigned char *content;
	size_t content_n;
	wstate_t st;                       /* formatted: its tables and repeat offsets */
} wdict_t;

/* any dictionary: raw content (at least 8 bytes, not starting with the dictionary magic number), or formatted:
 * magic, Dictionary_ID (not 0), the Huffman tree description, the FSE table descriptions for offsets, match lengths
 * and literals lengths (FSE_Compressed_Mode format: two or more symbols, accuracy logs <= 8, 9, 9), three repeat
 * offsets (1..content size), the content */
static void w_dict(wdict_t *d)
{
	static unsigned char need[FSE_SYM_MAX];
	out_t o = { d->bytes, 0, sizeof d->bytes };
	size_t k, i;
	unsigned s, t;
	d->formatted = choose(2);
	if (!d->formatted) {
		k = choose_in(8, W_DICT_MAX);
		for (i = 0; i < k; i++)
			put8(&o, choose(256));
		gp_assume(!(d->bytes[0] == 0x37 && d->bytes[1] == 0xA4 && d->bytes[2] == 0x30 && d->bytes[3] == 0xEC));
		d->id = 0;
		d->content = d->bytes;
		d->content_n = k;
		d->st.have_huf = 0;
		d->st.have_tab = 0;
		d->st.rep[0] = 1;
		d->st.rep[1] = 4;
		d->st.rep[2] = 8;
	} else {
		static const unsigned maxsym[3] = { 35, OF_CODE_MAX, 52 }, maxlog[3] = { 9, 8, 9 };
		static const unsigned order[3] = { 1, 2, 0 };   /* offsets, match lengths, literals lengths */
		put_le(&o, ZSTD_DICT_MAGIC, 4);
		d->id = 1 + choose(0xFFFFFFFFU);
		put_le(&o, d->id, 4);
		huf_pick(&d->st.huf);
		huf_put_description(&o, &d->st.huf);
		d->st.have_huf = 1;
		for (t = 0; t < 3; t++) {
			unsigned ty = order[t];
			for (s = 0; s < FSE_SYM_MAX; s++)
				need[s] = 0;
			fse_pick(&d->st.tab[ty], 5 + choose(maxlog[ty] - 4), maxsym[ty], need);
			fse_put_description(&o, &d->st.tab[ty]);
		}
		d->st.have_tab = 1;
		k = choose_in(1, W_DICT_MAX);
		for (t = 0; t < 3; t++) {
			d->st.rep[t] = (unsigned) choose_in(1, k);
			put_le(&o, d->st.rep[t], 4);
		}
		i = o.n;
		for (s = 0; s < k; s++)
			put8(&o, choose(256));
		d->content = d->bytes + i;
		d->content_n = k;
	}
	d->n = o.n;
}

/* ---------------------------------------------------------------------------------------------------------- */
/* frames and series (Frames; Zstandard frames; Skippable frames; Blocks) */

typedef struct {
	unsigned skippable, variant;       /* skippable: magic 0x184D2A50 + variant */
	size_t start, size;                /* in the series' bytes */
	size_t cstart, csize;              /* the content in the series' content (a skippable frame: none) */
	int fcs_present;
	unsigned long long fcs;
	unsigned did_size, did;            /* Dictionary_ID field size (0, 1, 2, 4) and value */
	int single;
	unsigned long long window;         /* Window_Size */
	unsigned window_log;               /* 10 + Exponent (0 for a single-segment frame) */
	unsigned checksum;
	unsigned blocks;
	size_t skip_n;                     /* a skippable frame's user data size */
	size_t hsize;                      /* the frame header's size (with the magic number; skippable: 8) */
	int uses_dict;
} winfo_t;

typedef struct {
	unsigned char bytes[W_OUT_MAX];
	size_t n;
	unsigned char content[W_CONTENT_MAX];
	size_t content_n;
	winfo_t f[W_FRAMES_MAX];
	unsigned nframes;
} wseries_t;

/* the content written so far into the current frame, behind the dictionary's content (Dictionary Format: Content) */
static unsigned char w_hist[W_DICT_MAX + W_CONTENT_MAX];

/* per compressed block: the sequences */
static unsigned char w_code[3][W_SEQ_MAX];
static unsigned w_extra[3][W_SEQ_MAX];
static unsigned short w_st[3][W_SEQ_MAX];
static unsigned char w_lit[1U << 17];

/* one compressed block of exactly t bytes of content, appended to w_hist[hn..), its tables and offsets carried in st.
 * dictn: the dictionary content in front of the frame; pos0: the frame's content before this block; window */
static void w_compressed_block(out_t *o, wstate_t *st, size_t dictn, size_t *hn, size_t t, unsigned long long window,
                               size_t bmax)
{
	static unsigned char blk_buf[(1U << 17) + 4096];
	static unsigned char need[FSE_SYM_MAX];
	static huf_t newhuf;
	static fse_t ntab[3];
	out_t blk = { blk_buf, 0, sizeof blk_buf };
	size_t nseq = 0, nlit = 0, rem = t, i;
	unsigned litmode, rleb = 0, ty, s;
	const huf_t *hp = 0;
	unsigned mode[3];
	/* the literals mode first: the literal bytes come from its alphabet */
	{
		unsigned opts[4], no = 0;
		opts[no++] = 0;
		opts[no++] = 1;
		opts[no++] = 2;
		if (st->have_huf)
			opts[no++] = 3;
		litmode = opts[choose(no)];
	}
	if (litmode == 1)
		rleb = choose(256);
	if (litmode == 2) {
		huf_pick(&newhuf);
		hp = &newhuf;
	}
	if (litmode == 3)
		hp = &st->huf;
	/* sequences: literals, then a match; trailing literals fill the block */
	while (rem >= 3 && nseq < W_SEQ_MAX - 1 && choose(4) != 0) {
		size_t ll = choose_in(0, rem - 3), ml, pos, maxoff, off, ov, j;
		size_t frame_pos = *hn - dictn;
		unsigned valid[3], nv = 0, r, kind;
		pos = frame_pos + ll;
		/* offsets into the frame's data: 1..pos, smaller than Window_Size; into the dictionary: while the frame's
		 * content stays within Window_Size */
		ml = choose_in(3, rem - ll);
		maxoff = pos < window - 1 ? pos : (size_t) (window - 1);
		if (dictn > 0 && pos + ml <= window)
			maxoff = pos + dictn;
		if (maxoff == 0)
			break;
		off = choose_in(1, maxoff);
		/* Offset_Value: a new offset (off + 3), or a repeat code that gives off */
		if (ll > 0) {
			for (r = 0; r < 3; r++)
				if (st->rep[r] == off)
					valid[nv++] = r + 1;
		} else {
			if (st->rep[1] == off)
				valid[nv++] = 1;
			if (st->rep[2] == off)
				valid[nv++] = 2;
			if (st->rep[0] > 1 && st->rep[0] - 1 == off)
				valid[nv++] = 3;
		}
		kind = choose(nv + 1);
		ov = kind < nv ? valid[kind] : off + 3;
		gp_assume(ov < (2ULL << OF_CODE_MAX));
		/* the repeat offsets after the sequence (Offset updates rules) */
		if (ov > 3 || (ov == 3 && ll == 0)) {
			st->rep[2] = st->rep[1];
			st->rep[1] = st->rep[0];
			st->rep[0] = (unsigned) off;
		} else {
			unsigned idx = (unsigned) ov - 1 + (ll == 0 ? 1 : 0);
			unsigned v = st->rep[idx];
			while (idx > 0) {
				st->rep[idx] = st->rep[idx - 1];
				idx--;
			}
			st->rep[0] = v;
		}
		/* the literals, then the match */
		for (j = 0; j < ll; j++) {
			unsigned char c = litmode == 0 ? (unsigned char) choose(256) : litmode == 1 ? (unsigned char) rleb
			                  : hp->used[choose(hp->nused)];
			w_lit[nlit++] = c;
			w_hist[(*hn)++] = c;
		}
		for (j = 0; j < ml; j++) {
			w_hist[*hn] = w_hist[*hn - off];
			(*hn)++;
		}
		w_code[0][nseq] = (unsigned char) ll_code(ll);
		w_extra[0][nseq] = (unsigned) (ll - W_LL_base[w_code[0][nseq]]);
		w_code[2][nseq] = (unsigned char) ml_code(ml);
		w_extra[2][nseq] = (unsigned) (ml - W_ML_base[w_code[2][nseq]]);
		w_code[1][nseq] = (unsigned char) highbit(ov);
		w_extra[1][nseq] = (unsigned) (ov - (1ULL << w_code[1][nseq]));
		nseq++;
		rem -= ll + ml;
	}
	for (i = 0; i < rem; i++) {                      /* the trailing literals */
		unsigned char c = litmode == 0 ? (unsigned char) choose(256) : litmode == 1 ? (unsigned char) rleb
		                  : hp->used[choose(hp->nused)];
		w_lit[nlit++] = c;
		w_hist[(*hn)++] = c;
	}
	/* the literals section */
	if (litmode <= 1)
		put_literals_raw_rle(&blk, litmode, w_lit, nlit);
	else
		put_literals_huf(&blk, litmode, hp, w_lit, nlit);
	if (litmode == 2) {
		huf_copy(&st->huf, &newhuf);
		st->have_huf = 1;
	}
	/* the sequences section header */
	if (nseq == 0) {
		if (choose(2))
			put8(&blk, 0);
		else
			put_le(&blk, 0x80, 2);                   /* the 2-byte form of 0 */
	} else {
		unsigned forms[3], nf = 0, f;
		if (nseq < 128)
			forms[nf++] = 0;
		if (nseq < 0x7F00)
			forms[nf++] = 1;
		if (nseq >= 0x7F00)
			forms[nf++] = 2;
		f = forms[choose(nf)];
		if (f == 0) {
			put8(&blk, (unsigned) nseq);
		} else if (f == 1) {
			put8(&blk, 0x80 + (unsigned) (nseq >> 8));
			put8(&blk, (unsigned) (nseq & 255));
		} else {
			put8(&blk, 255);
			put_le(&blk, nseq - 0x7F00, 2);
		}
		/* a mode per table that holds every code: 0 predefined, 1 RLE, 2 FSE-compressed, 3 repeat */
		for (ty = 0; ty < 3; ty++) {
			static const unsigned maxsym[3] = { 35, OF_CODE_MAX, 52 }, maxlog[3] = { 9, 8, 9 };
			unsigned opts[4], no = 0, same = 1, pre = 1;
			for (i = 0; i < nseq; i++) {
				if (w_code[ty][i] != w_code[ty][0])
					same = 0;
				if (ty == 1 && w_code[ty][i] > 28)
					pre = 0;
			}
			if (pre)
				opts[no++] = 0;
			if (same)
				opts[no++] = 1;
			opts[no++] = 2;
			if (st->have_tab) {
				unsigned covers = 1;
				for (i = 0; i < nseq; i++)
					if (!fse_has(&st->tab[ty], w_code[ty][i]))
						covers = 0;
				if (covers)
					opts[no++] = 3;
			}
			mode[ty] = opts[choose(no)];
			if (mode[ty] == 0) {
				fse_predefined(&ntab[ty], ty);
			} else if (mode[ty] == 1) {
				fse_rle(&ntab[ty], w_code[ty][0]);
			} else if (mode[ty] == 2) {
				for (s = 0; s < FSE_SYM_MAX; s++)
					need[s] = 0;
				for (i = 0; i < nseq; i++)
					need[w_code[ty][i]] = 1;
				fse_pick(&ntab[ty], 5 + choose(maxlog[ty] - 4), maxsym[ty], need);
			} else {
				fse_copy(&ntab[ty], &st->tab[ty]);
			}
		}
		put8(&blk, (mode[0] << 6) | (mode[1] << 4) | (mode[2] << 2));
		for (ty = 0; ty < 3; ty++) {                 /* literals lengths, offsets, match lengths */
			if (mode[ty] == 1)
				put8(&blk, w_code[ty][0]);
			else if (mode[ty] == 2)
				fse_put_description(&blk, &ntab[ty]);
		}
		/* the bitstream: initial states LL, OF, ML; per sequence the extra bits of OF, ML, LL, then (not after the
		 * last) the state updates LL, ML, OF; written in reverse */
		for (ty = 0; ty < 3; ty++)
			fse_states(&ntab[ty], w_code[ty], nseq, w_st[ty]);
		{
			bits_t b = { &blk, 0, 0 };
			static const unsigned upd[3] = { 2, 1, 0 };   /* reverse of LL, ML, OF */
			size_t q = nseq;
			while (q > 0) {
				q--;
				if (q + 1 < nseq) {
					for (s = 0; s < 3; s++) {
						unsigned u = upd[s];
						const fse_t *tb = &ntab[u == 2 ? 1 : u == 1 ? 2 : 0];
						unsigned short *sv = w_st[u == 2 ? 1 : u == 1 ? 2 : 0];
						bits_put(&b, sv[q + 1] - tb->base[sv[q]], tb->nb[sv[q]]);
					}
				}
				bits_put(&b, w_extra[0][q], W_LL_bits[w_code[0][q]]);
				bits_put(&b, w_extra[2][q], W_ML_bits[w_code[2][q]]);
				bits_put(&b, w_extra[1][q], w_code[1][q]);
			}
			bits_put(&b, w_st[2][0], ntab[2].log);
			bits_put(&b, w_st[1][0], ntab[1].log);
			bits_put(&b, w_st[0][0], ntab[0].log);
			bits_end_mark(&b);
		}
		for (ty = 0; ty < 3; ty++)
			fse_copy(&st->tab[ty], &ntab[ty]);
		st->have_tab = 1;
	}
	gp_assume(blk.n <= bmax);                        /* Block_Maximum_Size bounds the compressed size too */
	put_bytes(o, blk_buf, blk.n);                    /* the body; the caller writes the block header */
}

/* one Zstandard frame of n bytes of content (with the dictionary d, or none): header, blocks, checksum */
static void w_frame(wseries_t *sr, out_t *o, winfo_t *fi, size_t n, const wdict_t *d)
{
	static unsigned char hdr[32];
	wstate_t st;
	size_t dictn = (d && d->content_n > 0) ? d->content_n : 0, hn, left = n, i;
	unsigned long long window;
	size_t bmax;
	unsigned fcsflag, didflag, nblocks = 0, single, e = 0, m = 0;
	out_t h = { hdr, 0, sizeof hdr };
	/* the header: single segment (Window_Size = Frame_Content_Size) or a window descriptor; content size forms;
	 * Dictionary_ID: absent, or a field holding 0 or (with a dictionary) its ID; checksum or not */
	single = choose(2);
	fi->checksum = choose(2);
	if (single) {
		unsigned forms[4], nf = 0;
		if (n <= 255)
			forms[nf++] = 0;
		if (n >= 256 && n <= 65791)
			forms[nf++] = 1;
		forms[nf++] = 2;
		forms[nf++] = 3;
		fcsflag = forms[choose(nf)];
		window = n;
		fi->window_log = 0;
	} else {
		unsigned forms[4], nf = 0, emin = 0;
		forms[nf++] = 0;                             /* no content size */
		if (n >= 256 && n <= 65791)
			forms[nf++] = 1;
		forms[nf++] = 2;
		forms[nf++] = 3;
		fcsflag = forms[choose(nf)];
		while (emin < 7 && (size_t) W_BLOCKS_MAX << (10 + emin) < n)
			emin++;                                  /* smaller windows cannot hold n in W_BLOCKS_MAX blocks */
		e = emin + choose(32 - emin);
		m = choose(8);
		window = (1ULL << (10 + e)) + ((1ULL << (10 + e)) / 8) * m;
		fi->window_log = 10 + e;
	}
	fi->window = window;
	fi->single = (int) single;
	{
		unsigned opts[4], no = 0, id = d ? d->id : 0;
		opts[no++] = 0;
		if (id <= 255)
			opts[no++] = 1;
		if (id <= 65535)
			opts[no++] = 2;
		opts[no++] = 3;
		didflag = opts[choose(no)];
		fi->did = didflag == 0 ? 0 : (choose(2) ? id : 0);
	}
	fi->did_size = didflag == 0 ? 0 : didflag == 1 ? 1 : didflag == 2 ? 2 : 4;
	put_le(&h, 0xFD2FB528U, 4);
	put8(&h, (fcsflag << 6) | (single << 5) | (fi->checksum << 2) | didflag);
	if (!single)
		put8(&h, (e << 3) | m);
	put_le(&h, fi->did, fi->did_size);
	fi->fcs_present = single || fcsflag != 0;
	fi->fcs = n;
	if (fcsflag == 0 && single)
		put8(&h, (unsigned) n);
	else if (fcsflag == 1)
		put_le(&h, n - 256, 2);
	else if (fcsflag == 2) {
		gp_assume(n <= 0xFFFFFFFFULL);
		put_le(&h, n, 4);
	} else if (fcsflag == 3)
		put_le(&h, n, 8);
	put_bytes(o, hdr, h.n);
	fi->hsize = h.n;
	/* blocks: Block_Maximum_Size = min(Window_Size, 128 KB) bounds every block's content and size */
	bmax = window < (1ULL << 17) ? (size_t) window : (size_t) 1 << 17;
	if (d) {
		wstate_copy(&st, &d->st);
		for (i = 0; i < dictn; i++)
			w_hist[i] = d->content[i];
	} else {
		st.rep[0] = 1;
		st.rep[1] = 4;
		st.rep[2] = 8;
		st.have_huf = 0;
		st.have_tab = 0;
	}
	fi->uses_dict = d != 0;
	hn = dictn;
	do {
		size_t t = choose_in(0, left < bmax ? left : bmax), start = o->n;
		unsigned type = choose(3), last;
		gp_assume(nblocks < W_BLOCKS_MAX);
		last = (t == left) && (nblocks + 1 == W_BLOCKS_MAX || choose(4) != 0);
		put_le(o, 0, 3);                             /* the block header, filled below */
		if (type == 0) {                             /* Raw_Block */
			for (i = 0; i < t; i++) {
				unsigned char c = (unsigned char) choose(256);
				put8(o, c);
				w_hist[hn++] = c;
			}
		} else if (type == 1) {                      /* RLE_Block: one byte of content */
			unsigned char c = (unsigned char) choose(256);
			gp_assume(bmax >= 1);
			put8(o, c);
			for (i = 0; i < t; i++)
				w_hist[hn++] = c;
		} else {                                     /* Compressed_Block */
			w_compressed_block(o, &st, dictn, &hn, t, window, bmax);
		}
		{
			size_t bsize = type == 1 ? t : o->n - start - 3;
			unsigned long long hv = last | (type << 1) | ((unsigned long long) bsize << 3);
			gp_assert(bsize <= bmax);
			o->p[start] = (unsigned char) (hv & 255);
			o->p[start + 1] = (unsigned char) ((hv >> 8) & 255);
			o->p[start + 2] = (unsigned char) ((hv >> 16) & 255);
		}
		left -= t;
		nblocks++;
		if (last)
			break;
	} while (1);
	fi->blocks = nblocks;
	gp_assert(hn - dictn == n);
	/* the frame's content */
	for (i = 0; i < n; i++)
		sr->content[sr->content_n + i] = w_hist[dictn + i];
	if (fi->checksum)
		put_le(o, xxh64(w_hist + dictn, n) & 0xFFFFFFFFULL, 4);
}

/* any series of 1..W_FRAMES_MAX frames, Zstandard or skippable, every Zstandard frame with the dictionary d or
 * without one (d == 0); its content is the concatenation of the frames' contents */
static void w_series(wseries_t *sr, const wdict_t *d)
{
	out_t o = { sr->bytes, 0, sizeof sr->bytes };
	unsigned k = 1 + choose(W_FRAMES_MAX), f;
	sr->content_n = 0;
	for (f = 0; f < k; f++) {
		winfo_t *fi = &sr->f[f];
		fi->start = o.n;
		fi->cstart = sr->content_n;
		fi->skippable = choose(4) == 0;
		if (fi->skippable) {
			size_t m = choose_in(0, W_SKIP_MAX), i;
			fi->variant = choose(16);
			put_le(&o, 0x184D2A50U + fi->variant, 4);
			put_le(&o, m, 4);
			for (i = 0; i < m; i++)
				put8(&o, choose(256));
			fi->skip_n = m;
			fi->hsize = 8;
			fi->csize = 0;
		} else {
			size_t room = W_CONTENT_MAX - sr->content_n, scale = choose(4);
			size_t n = choose_in(0, scale == 0 ? (room < 16 ? room : 16) : scale == 1 ? (room < 300 ? room : 300)
			                         : scale == 2 ? (room < 5000 ? room : 5000) : room);
			w_frame(sr, &o, fi, n, d);
			fi->csize = n;
			sr->content_n += n;
		}
		fi->size = o.n - fi->start;
	}
	sr->nframes = k;
	sr->n = o.n;
}

#endif
