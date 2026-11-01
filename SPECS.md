# The specs

Each spec is a small C program in `harness/`. QuickProof turns it into a Coq theorem: for every input the spec
allows, none of its checks (`gp_assert`) fails and nothing it runs has undefined behaviour. This page explains zstd
in a few lines, how to read a spec, and what each spec says: first the 25 short specs, then the 19 longer `x_`
specs. [README.md](README.md) gives the proof status and the limits that apply to every spec.

## zstd in two minutes

- **Frames.** Compressed data is a series of *frames* (RFC 8878 section 3.1). A *Zstandard frame* is a magic number,
  a header, one or more *blocks* and maybe a checksum; a *skippable frame* carries user data that a decoder skips.
- **The header** says which optional fields follow: the window size (how far back the data may refer), or "single
  segment" (the window is the whole content); the content size (`Frame_Content_Size`); a dictionary ID; and whether a
  checksum (the low 32 bits of XXH64 of the content) ends the frame.
- **Blocks** are *raw* (the bytes as they are), *RLE* (one byte, repeated), or *compressed* (Huffman-coded literals and
  LZ77 sequences). A block holds at most `min(Window_Size, 128 KiB)` bytes.
- **One-shot.** `ZSTD_decompress(dst, capacity, src, size)` decodes a whole series and returns the content's size or
  an error code (`ZSTD_isError`); `ZSTD_decompressDCtx` does the same with a context that can be reused.
- **Streaming.** `ZSTD_decompressStream(stream, &output, &input)` is called again and again; each call reads from
  `input.src` at `input.pos`, writes to `output.dst` at `output.pos`, and moves the two positions. It returns 0 when a
  frame is complete, an error code, or a hint (more to do).
- **Contexts and memory.** `ZSTD_DCtx_reset` returns a context to a clean state; `ZSTD_freeDCtx` frees it. A context
  can be given its own allocator (`ZSTD_customMem`); `ZSTD_d_windowLogMax` limits the window a stream accepts.

## How to read a spec

```c
size_t n = upto(PTRDIFF_MAX);          // any length (the allocator decides what it provides)
unsigned char *data = any_bytes(n);    // any n bytes
... call zstd ...
gp_assert(result == n && bytes_eq(dst, data, n));   // what must hold
```

- `nondet_*`, `upto(max)`, `any_bytes(n)` and `pick(x)` stand for *any* value: the theorem covers all of them at once.
- `gp_assume(c)` restricts the inputs the spec talks about. In the short specs the only one is in `frames.h`: the
  windows of the frames it writes are within the limit the spec names, and the first comment says so. The `x_`
  specs have more ([below](#the-x_-specs)).
- `gp_assert(c)` is the property. When zstd returns `ZSTD_error_memory_allocation`, or the spec cannot allocate, the
  run stops and the spec claims nothing about it.
- The first comment of each file is the claim; the tables below only summarize it. The first comments of the `x_`
  specs leave out their size bounds, which their `#define` and `gp_assume` lines, and for compliant data the
  `W_*_MAX` lines of `writer.h`, give. The comments call the specs "laws".
- Two shared headers, both without any model of zstd:
  - `laws_common.h` (33 lines): any bytes, a copy, a comparison, `out_of_memory`; every short spec includes it.
  - `frames.h` (115 lines): a writer of the simplest valid frames, field by field as RFC 8878 lays them out
    (`new_frame`: any header form, any cut of the data into Raw and RLE blocks, the checksum computed with zstd's own
    `ZSTD_XXH64`, which `ck_xxh64` checks against the xxHash specification; `new_skippable`; `join`), and `stream_all`
    (a series given to `ZSTD_decompressStream` in any pieces with any output room). The specs on valid frames include
    it; the specs on any bytes do not. zstd's compressor is not part of the verified code, so valid frames are
    written by hand, not compressed.
- Windows: `ONE_CALL_WINDOW` is `2^ZSTD_WINDOWLOG_MAX` (2 GiB), the largest window zstd decodes one-shot;
  `STREAM_WINDOW` is `2^ZSTD_WINDOWLOG_LIMIT_DEFAULT` (128 MiB), the largest a stream accepts by default (zstd.h).

The specs are about zstd's decoder with the edits that [README.md](README.md#the-code-under-test) lists. A spec
marked "Needs F5" holds only with that fix, and is false on the unmodified code
([below](#the-fixes-the-short-specs-need), [patch/GENPROOF-PATCH.md](patch/GENPROOF-PATCH.md)).

Before any proof, every spec was run natively under AddressSanitizer and UndefinedBehaviorSanitizer and in
CompCert's interpreter, and the short specs also against broken versions of the decoder that they must notice
([CHECK.md](CHECK.md)). In the interpreter, every run of nine `x_` specs reached the time limit, and `x_valid_dict`
started none.

## The short specs

`lines` counts the spec, then the spec with its headers.

### The standard on valid input (`rfc_`)

| spec | lines | what it says | source |
|---|---|---|---|
| `rfc_frame` | 24 / 172 | A frame of Raw and RLE blocks in any header form, with or without a checksum, decodes with `ZSTD_decompress`, given room for its content, to exactly its content. | RFC 8878 3.1.1, 3.1.1.2 |
| `rfc_concat` | 35 / 183 | Any number of such frames one after the other decode to their contents one after the other. | RFC 8878 3.1; zstd.h `ZSTD_decompress` |
| `rfc_skippable` | 40 / 188 | Skippable frames (any magic of the 16, any user data up to 2^32 - 1 bytes) anywhere among them add nothing. Needs F5. | RFC 8878 3.1.2 |

### Rejects (`rj_`): any input is safe, invalid input is refused

| spec | lines | what it says | source |
|---|---|---|---|
| `rj_any_input` | 29 / 62 | On any bytes, with any capacity, `ZSTD_decompress` and a reused context's `ZSTD_decompressDCtx` return an error or a size at most the capacity. With the theorem's "no undefined behaviour", no input makes these calls access memory outside their objects. | zstd.h `ZSTD_decompress` |
| `rj_any_stream` | 41 / 74 | On any bytes in any pieces, with any buffers and start positions, the stream reset after each error, `ZSTD_decompressStream` keeps both positions within their buffers and never moves them back. | zstd.h `ZSTD_inBuffer`, `ZSTD_outBuffer` |
| `rj_any_dict` | 30 / 63 | On any dictionary bytes and any input, `ZSTD_decompress_usingDict` returns an error or a size at most the capacity. The dictionary and the output are one object (the spec explains why). | RFC 8878 5 ("considered untrusted"); zstd.h |
| `rj_bad_checksum` | 30 / 178 | A frame whose checksum is changed to any other value is refused: `ZSTD_error_checksum_wrong` one-shot, never complete when streamed. | RFC 8878 3.1.1; zstd.h `ZSTD_d_forceIgnoreChecksum` |
| `rj_content_size` | 31 / 179 | A frame whose `Frame_Content_Size` declares any other size than its content's (2^64 - 1 means "unknown", see below) is refused, one-shot and streamed. Needs F6. | RFC 8878 3.1.1.1.4 |
| `rj_reserved_bit` | 28 / 176 | A frame with the header's `Reserved_bit` set is refused, one-shot and streamed. | RFC 8878 3.1.1.1.1 |
| `rj_reserved_block` | 35 / 183 | A frame where any one block's type is changed to 3 (Reserved) is refused, one-shot and streamed. | RFC 8878 3.1.1.2.2 |
| `rj_truncated` | 29 / 177 | Any part of a frame that stops before its end is never taken for a complete frame, one-shot or streamed. | zstd.h `ZSTD_decompress`, `ZSTD_decompressStream` |

### The interface (`api_`)

| spec | lines | what it says | source |
|---|---|---|---|
| `api_split_invariant` | 49 / 197 | For any accepted `ZSTD_d_windowLogMax`, a series of frames streamed in any pieces with any output room ends as one-shot decoding ends: when one-shot decoding fails, the stream never completes after reading everything; when it succeeds, the stream completes with exactly the same bytes. | zstd.h `ZSTD_decompressStream`, `ZSTD_d_windowLogMax` |
| `api_untouched_output` | 44 / 77 | On any input in any pieces, the stream reset after each error, a stream call never changes the output before the position it is given, and a call that returns no error writes nothing after the position it returns. Needs F7. | zstd.h `ZSTD_outBuffer` |
| `api_reset` | 77 / 110 | A context used for one-shot and streaming decoding of any inputs, with dictionaries loaded by copy and any `ZSTD_d_windowLogMax`, then reset with `ZSTD_reset_session_and_parameters`, behaves like a new one on any input (same results, positions and bytes; both fail or neither). Needs F8. | zstd.h `ZSTD_DCtx_reset` |
| `api_short_output` | 24 / 172 | A frame given less capacity than its content is refused with `ZSTD_error_dstSize_tooSmall`. The spec checks the error code only, not what is in `dst`. | zstd.h `ZSTD_decompress` |
| `api_flush_bound` | 34 / 67 | On any input, the stream reset after each error, a stream call given no input writes at most `ZSTD_BLOCKSIZE_MAX` (128 KiB). | zstd.h `ZSTD_decompressStream` |
| `api_content_size` | 32 / 180 | `ZSTD_getFrameContentSize` returns the declared size (any 64-bit value), `ZSTD_CONTENTSIZE_UNKNOWN` without the field, 0 for a skippable frame. | zstd.h; RFC 8878 3.1.1.1 |
| `api_frame_size` | 27 / 175 | `ZSTD_findFrameCompressedSize` returns exactly the size of the first frame, Zstandard or skippable, whatever follows. Needs F5. | zstd.h |
| `api_dict_id` | 26 / 174 | `ZSTD_getDictID_fromFrame` returns the frame's `Dictionary_ID` (any value, any field size), 0 for a skippable frame. Needs F1. | zstd.h; RFC 8878 3.1.1.1.3 |
| `api_ignore_checksum` | 27 / 175 | With `ZSTD_d_forceIgnoreChecksum`, a frame with any checksum decodes to exactly its content. | zstd.h (experimental) |
| `api_free_null` | 10 / 43 | `ZSTD_freeDCtx`, `ZSTD_freeDStream`, `ZSTD_freeDDict` accept NULL. | zstd.h |

### Memory (`res_`), counted through the context's allocator

| spec | lines | what it says | source |
|---|---|---|---|
| `res_free` | 78 / 111 | After any use (one-shot and streaming decoding, dictionaries loaded by copy, one referenced dictionary with or without `ZSTD_d_refMultipleDDicts`, any `ZSTD_d_windowLogMax`, resets), `ZSTD_freeDCtx` gives back every byte. | zstd.h `ZSTD_freeDCtx`, `ZSTD_d_refMultipleDDicts` |
| `res_memory_oneshot` | 57 / 90 | Decoding any inputs one-shot never holds more than `ZSTD_estimateDCtxSize()`. | zstd.h `ZSTD_d_windowLogMax` ("no internal buffer is allocated in single-pass mode") |
| `res_memory_stream` | 69 / 102 | With any accepted `ZSTD_d_windowLogMax`, streaming any input, the stream reset after each error, never holds more than `ZSTD_estimateDStreamSize(2^windowLogMax)`. | zstd.h `ZSTD_d_windowLogMax`, `ZSTD_estimateDStreamSize` |

### Checksum (`ck_`)

| spec | lines | what it says | source |
|---|---|---|---|
| `ck_xxh64` | 60 / 93 | `ZSTD_XXH64` equals XXH64 as the xxHash specification defines it, written out in the spec, for any bytes and seed. | xxHash spec, "XXH64 Algorithm Description" |

## The `x_` specs

These 19 specs encode the promises of zstd's documents that [PROMISES.md](PROMISES.md) lists
(`doc/zstd_compression_format.md`, `zstd.h` and the decoder's notes). Their harness comments and PROMISES.md use the
names without `x_`. The `x_valid_*` specs, `x_detect` and `x_stable_out` draw compliant data, compressed blocks and
dictionaries included, from the frame writer `harness/writer.h` (1231 lines); `harness/zlimits.h` holds the limits
under which zstd may refuse a frame. The `x_any_*` specs take any bytes; native runs feed them real frames from
`harness/corpus.h`.

Unlike the short specs, the `x_` specs are bounded. On any bytes: input up to 4096 bytes, output up to 65536,
dictionaries up to 4096 bytes (512 in `x_any_params` and `x_any_bufferless`), at most 512 calls (4096 in
`x_stable_out`), and in `x_any_stream` and `x_any_params` chunks of at most 256 bytes. On compliant data: series of 1
to 4 frames, each of at most 6 blocks, with at most 256 KiB of content in all, skippable frames of at most 64 bytes
of user data, and dictionaries of at most 4 KiB of content; the streaming specs stop after 4096 calls. `writer.h`
also assumes two facts about FSE tables (its first comment). "Any" in the table means any value within these bounds;
each spec's `#define` and `gp_assume` lines, and for compliant data the `W_*_MAX` lines of `writer.h`, give them
exactly.

| spec | what it says |
|---|---|
| `x_any_oneshot` | One-shot decompression of any bytes into any capacity: an error or at most the capacity; `ZSTD_freeDCtx` accepts NULL. |
| `x_any_stream` | Streaming any bytes over any chunking: `0 <= pos <= size` for input and output; at most `ZSTD_BLOCKSIZE_MAX` flushed without new input; resets after errors. |
| `x_any_dict` | Any dictionary bytes and any frame bytes through the by-reference dictionary APIs: an error or at most the capacity. |
| `x_any_dict_copy` | The same through the APIs that copy the dictionary. |
| `x_any_info` | The frame-inspection functions on any bytes return what `zstd.h` documents (sizes within the input, "wanted" sizes, magic tests). |
| `x_any_info_extra` | `ZSTD_getDecompressedSize` and `ZSTD_getFrameHeader_advanced` on any bytes, as documented. |
| `x_any_params` | Any values of the decoding parameters (window limit, format, checksum, several dictionaries, block size): one-shot and streaming stay safe and within their buffers. |
| `x_any_bufferless` | Buffer-less streaming (`ZSTD_decompressContinue`) on any bytes in any pieces, with or without a dictionary: an error or at most the capacity. |
| `x_bound` | `ZSTD_COMPRESSBOUND(A) + ZSTD_COMPRESSBOUND(B) <= ZSTD_COMPRESSBOUND(A + B)` for A, B of at least 128 KB with A + B < `ZSTD_MAX_INPUT_SIZE`. |
| `x_valid_oneshot` | Any series of compliant frames (every block, literal and table mode, header form, checksum, skippable frames) decodes one-shot to exactly its content; with room for it, it succeeds unless `zlimits.h` allows a refusal. |
| `x_valid_stream` | The same streamed in any pieces with any output room; the hint never asks for more than the frame holds. |
| `x_valid_dict` | Any dictionary (raw or formatted) and frames written with it, through the by-reference dictionary APIs: exactly the content. |
| `x_valid_dict_copy` | The same through the APIs that copy the dictionary. |
| `x_valid_dict_api` | Several dictionaries selected by their ID (`ZSTD_d_refMultipleDDicts`), the `_advanced` loaders, the deprecated stream initialisation: exactly the content. |
| `x_valid_info` | On compliant frames, the inspection functions report exactly the frames' sizes, content sizes and IDs. |
| `x_valid_params` | Compliant frames under any accepted decoding parameters decode to exactly their content. |
| `x_valid_bufferless` | Buffer-less streaming of compliant frames, each call given exactly what it asks for: exactly the content, 0 through skippable frames. |
| `x_detect` | A compliant series with one frame's checksum changed or reserved bit set is refused, one-shot and streamed. |
| `x_stable_out` | `ZSTD_d_stableOutBuffer`: memory safe on any bytes; on compliant frames, every byte written is the content. |

## The fixes the short specs need

The short specs are written from RFC 8878 and zstd.h. Five of them were false on the code with `patch/fixes.py`
only, for four reasons. `patch/fixes2.py` fixes them:

- F5 (`rfc_skippable`, `api_frame_size`): one-shot decoding and the frame-size functions refused skippable frames
  with 2^32 - 8 bytes of user data or more (a 32-bit sum in `readSkippableFrameSize`).
- F6 (`rj_content_size`): streaming did not compare the decoded size with `Frame_Content_Size` when a frame ends with
  an empty last block. The fix adds the check that a non-empty last block has.
- F7 (`api_untouched_output`): the single-pass shortcut of `ZSTD_decompressStream` decoded into all the output space,
  and its wildcopies wrote past the `output.pos` it returns. It now gets exactly the declared content size.
- F8 (`api_reset`): resetting the parameters kept the stream buffers and the literal buffer. With frames that break
  the format, a later frame then decodes differently, and can show bytes of the frame decoded before the reset. The
  reset now releases the buffers and clears the literal buffer.

## Harness corrections

Proof attempts found three places where a harness itself was wrong. Each harness was corrected, and each claim kept
what it meant to say:

- `rj_content_size`: the harness picks any declared size other than the content's, so it could pick 2^64 - 1. That
  value is `ZSTD_CONTENTSIZE_UNKNOWN` (zstd.h), and zstd reads an 8-byte `Frame_Content_Size` field holding it as
  "the size is not known". Such a frame declares no size, so there is nothing to compare, and zstd decodes it. The
  harness now also ends the run when `declared == ZSTD_CONTENTSIZE_UNKNOWN`, and its first comment says so. Every
  other wrong size is still refused, one-shot and streamed.
- `api_untouched_output`: with `room == 0`, the output space and its copy `before` may be NULL (`any_bytes(0)` and
  `copy_of(.., 0)` may return NULL), and the harness went on. Its own check then computed `out + output.pos` and
  `before + output.pos` on NULL. CompCert defines NULL + 0, but VST's rules accept `p + i` only for a pointer `p`,
  so the spec could not be proved as written, even though it was true. An empty output has no bytes before or after
  any position, so the harness now skips the comparison when `room == 0`. The call itself is still made, with the
  NULL output, so its safety is still part of the theorem (F9 is what makes that call safe).
- `res_free`: in its streaming branch the harness called `ZSTD_decompressStream` again on a context that had just
  returned an error, when the following parameters-only reset was refused inside a frame. zstd.h
  (`ZSTD_decompressStream`) calls that undefined: "It's UB to invoke ZSTD_decompressStream() on such a state ... it
  must be first reset". The harness now resets the session after an error, as `res_memory_stream` already does. The
  claim is unchanged: every byte comes back after any use that zstd.h allows. Checked natively (400 runs) and in
  CompCert's interpreter (4 runs, no stop).

## What the specs do not say

- Compressed blocks. The short specs state conformance for Raw and RLE blocks and skippable frames, the frames that
  can be written by hand in a few lines; compressed blocks (Huffman literals, FSE sequences) appear in them only as
  *any input* (`rj_any_*`, `api_untouched_output`, `api_reset`, `api_flush_bound`, `res_*`). The `x_valid_*` specs,
  with the frame writer `writer.h`, cover them, and dictionaries' content, within their bounds.
- Error codes, except where a spec names one (`checksum_wrong`, `dstSize_tooSmall`): zstd.h documents only "an
  error".
- Content sizes of 2^64 - 2 and 2^64 - 1 are what `ZSTD_getFrameContentSize` returns for "error" and "unknown":
  `api_content_size` holds, but a frame that declares one of them cannot be told from those cases.
- Sizes: in the short specs, any length the allocator provides, except the windows named above (zstd's documented
  limits); the `x_` specs are bounded ([above](#the-x_-specs)).
- Termination, other platforms, other configurations of zstd and the compressor: [README.md](README.md) states
  these limits.
