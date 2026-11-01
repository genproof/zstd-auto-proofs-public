// Differential test of the idiom patch (patch/diff.sh): the unmodified upstream decoder (orig_*) and the
// patched one decode the same bytes into equally sized, equally filled buffers; their results and their
// whole output buffers must be identical.  Inputs: frames of the upstream compressor (any level, with or
// without checksum and content size, several frames, a raw-content dictionary), valid or mutated (bit
// flips, overwritten bytes, truncation, spliced frames) or random bytes; any output capacity; one-shot,
// streaming with random chunk sizes, and decoding with a dictionary.
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

long long dt_oneshot(unsigned char *, size_t, const unsigned char *, size_t);
long long orig_dt_oneshot(unsigned char *, size_t, const unsigned char *, size_t);
long long dt_dict(unsigned char *, size_t, const unsigned char *, size_t, const unsigned char *, size_t);
long long orig_dt_dict(unsigned char *, size_t, const unsigned char *, size_t, const unsigned char *, size_t);
long long dt_ddict(unsigned char *, size_t, const unsigned char *, size_t, const unsigned char *, size_t);
long long orig_dt_ddict(unsigned char *, size_t, const unsigned char *, size_t, const unsigned char *, size_t);
long long dt_stream(unsigned char *, size_t, size_t *, const unsigned char *, size_t, const size_t *, size_t);
long long orig_dt_stream(unsigned char *, size_t, size_t *, const unsigned char *, size_t, const size_t *, size_t);
size_t dt_compress(unsigned char *, size_t, const unsigned char *, size_t, int, int, int, const unsigned char *, size_t);
size_t dt_bound(size_t);

static uint64_t s = 88172645463325252ULL;
static uint64_t rnd(void) { s ^= s << 13; s ^= s >> 7; s ^= s << 17; return s; }

static void fill(unsigned char *p, size_t n, const unsigned char *dict, size_t dn)
{
	const unsigned kind = rnd() % 6;
	for (size_t i = 0; i < n; i++) {
		switch (kind) {
		case 0: p[i] = (unsigned char) rnd(); break;                        /* incompressible */
		case 1: p[i] = 'a'; break;                                          /* one run */
		case 2: p[i] = (unsigned char) "zstd frame block "[i % 17]; break;  /* periodic */
		case 3: p[i] = (unsigned char) (rnd() % 4 + 'a'); break;            /* small alphabet */
		case 4: p[i] = (i > 40 && rnd() % 8) ? p[i - 1 - rnd() % 40] : (unsigned char) rnd(); break;  /* LZ-like */
		default: p[i] = dn && rnd() % 4 ? dict[rnd() % dn] : (unsigned char) rnd(); break;           /* dictionary-like */
		}
	}
}

static size_t pick_size(size_t max)
{
	switch (rnd() % 4) {
	case 0: return rnd() % 16;
	case 1: return rnd() % 512;
	default: return rnd() % (max + 1);
	}
}

static unsigned long long runs, decoded, mismatches;

static void report(const char *mode, long long a, long long b, size_t len)
{
	if (++mismatches <= 10)
		fprintf(stderr, "MISMATCH %s: orig %lld, patched %lld (input %zu bytes, seed state %llu)\n",
		        mode, a, b, len, (unsigned long long) s);
}

// Both decoders on a copy of src[0..n) in an exactly sized buffer, output capacity cap.
static void both(const unsigned char *in, size_t n, size_t cap, const unsigned char *dict, size_t dn)
{
	unsigned char *src = malloc(n ? n : 1), *a = malloc(cap ? cap : 1), *b = malloc(cap ? cap : 1);
	memcpy(src, in, n);
	unsigned char fillb = (unsigned char) rnd();
	runs++;
	memset(a, fillb, cap); memset(b, fillb, cap);
	long long ra = orig_dt_oneshot(a, cap, src, n), rb = dt_oneshot(b, cap, src, n);
	if (ra != rb || memcmp(a, b, cap)) report("oneshot", ra, rb, n);
	if (ra >= 0) decoded++;
	if (dict != NULL) {
		memset(a, fillb, cap); memset(b, fillb, cap);
		ra = orig_dt_dict(a, cap, src, n, dict, dn); rb = dt_dict(b, cap, src, n, dict, dn);
		if (ra != rb || memcmp(a, b, cap)) report("dict", ra, rb, n);
		if (ra >= 0) decoded++;
		memset(a, fillb, cap); memset(b, fillb, cap);
		ra = orig_dt_ddict(a, cap, src, n, dict, dn); rb = dt_ddict(b, cap, src, n, dict, dn);
		if (ra != rb || memcmp(a, b, cap)) report("ddict", ra, rb, n);
		if (ra >= 0) decoded++;
	}
	if (rnd() % 4 == 0) {
		size_t chunks[5], ga, gb;
		for (int i = 0; i < 5; i++) chunks[i] = 1 + rnd() % (rnd() % 2 ? 16 : 4096);
		memset(a, fillb, cap); memset(b, fillb, cap);
		ra = orig_dt_stream(a, cap, &ga, src, n, chunks, 5); rb = dt_stream(b, cap, &gb, src, n, chunks, 5);
		if (ra != rb || ga != gb || memcmp(a, b, cap)) report("stream", ra, rb, n);
		if (ra >= 0) decoded++;
	}
	free(src); free(a); free(b);
}

int main(int argc, char **argv)
{
	const unsigned long long cases = argc > 1 ? strtoull(argv[1], NULL, 10) : 20000;
	enum { NMAX = 1 << 17 };
	static unsigned char raw[NMAX], dict[4096], comp[2 * NMAX + 4096], mut[2 * NMAX + 4096];
	for (unsigned long long c = 0; c < cases; c++) {
		const size_t n = pick_size(rnd() % 8 ? 20000 : NMAX - 1);
		size_t dn = 0;
		const int use_dict = rnd() % 5 == 0;
		if (use_dict) { dn = 64 + rnd() % 4000; fill(dict, dn, NULL, 0); }
		fill(raw, n, dict, dn);
		const int level = rnd() % 10 ? 1 + (int) (rnd() % 9) : (int) (rnd() % 25) - 5;
		size_t m = dt_compress(comp, sizeof comp, raw, n, level, (int) (rnd() % 2), (int) (rnd() % 4 != 0),
		                       use_dict ? dict : NULL, dn);
		if (m == 0) continue;
		if (!use_dict && rnd() % 6 == 0 && n + 2000 <= NMAX) {   /* a second frame after the first (n2 <= 2000 fits raw) */
			size_t n2 = pick_size(2000);
			fill(raw + n, n2, NULL, 0);
			size_t m2 = dt_compress(comp + m, sizeof comp - m, raw + n, n2, 3, 1, 1, NULL, 0);
			if (m2) m += m2;
		}
		const size_t cap_exact = n + (rnd() % 2 ? 0 : 2000);
		/* the valid frame: exact, smaller and larger capacities */
		both(comp, m, cap_exact, use_dict ? dict : NULL, dn);
		both(comp, m, rnd() % (cap_exact + 1), use_dict ? dict : NULL, dn);
		/* mutants of it */
		for (int k = 0; k < 4; k++) {
			size_t len = m;
			memcpy(mut, comp, m);
			switch (rnd() % 5) {
			case 0: mut[rnd() % m] ^= (unsigned char) (1u << (rnd() % 8)); break;
			case 1: for (int j = 0; j < 4; j++) mut[rnd() % m] = (unsigned char) rnd(); break;
			case 2: len = rnd() % m; break;
			case 3: mut[4 + rnd() % (m > 12 ? 8 : m - 4)] = (unsigned char) rnd(); break;  /* frame/block header */
			default: { size_t at = rnd() % m, from = rnd() % m, k2 = rnd() % 64;            /* splice */
				for (size_t j = 0; j < k2 && at + j < m; j++) mut[at + j] = comp[(from + j) % m]; }
			}
			both(mut, len, rnd() % 3 ? cap_exact : rnd() % (cap_exact + 1), use_dict ? dict : NULL, dn);
		}
		/* random bytes, sometimes behind a valid magic number */
		size_t rn = pick_size(4096);
		for (size_t j = 0; j < rn; j++) mut[j] = (unsigned char) rnd();
		if (rn >= 4 && rnd() % 2) memcpy(mut, "\x28\xb5\x2f\xfd", 4);
		both(mut, rn, pick_size(1 << 16), NULL, 0);
	}
	printf("diff_decompress: %llu runs, %llu successful decodes, %llu mismatches\n", runs, decoded, mismatches);
	return mismatches != 0;
}
