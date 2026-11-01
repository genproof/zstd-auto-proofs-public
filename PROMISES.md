# zstd: what it promises, and the specs that encode it

Sources, all at release v1.5.7 (line numbers refer to those files, not to this tree's later `lib/zstd.h`): **F** =
`doc/zstd_compression_format.md` (the format, = RFC 8878), **P** =
`doc/decompressor_permissive.md`, **E** = `doc/decompressor_errata.md`, **H** = `lib/zstd.h` (stable API up to line
1229; after it the experimental API, "not stable", static linking only, marked *exp*), **R** = `README.md`.
A spec may claim only what these say (or ISO C); a counterexample to a spec is then a bug by zstd's own
definition.

## The decoder's contract

> "While the reference decompressor *must* decode any compliant frame following the specification, its ability to
> detect erroneous data is on a best effort basis: the decoder may accept input data that would be formally invalid,
> when it causes no risk to the decoder" (P:7-11)

Three parts: (1) **every compliant frame decodes to its content**, including frames the reference compressor never
writes (the errata, E, call each rejected valid frame a decoder bug: 2-byte encoding of 0 sequences, a 128 KB
compressed block, 0 literals and 0 sequences, ...); (2) **any input is safe** (no risk to the decoder; ISO C: no
undefined behaviour); (3) **detecting invalid input is best effort**, except where a document says otherwise: the
reserved bit (F:216 "must ensure it is not set") and the checksum, which zstd validates by default (H:2538).

## Promises

### Decoder: any input is safe

| id | promise | source |
|---|---|---|
| S1 | invalid data is accepted only "when it causes no risk to the decoder": no undefined behaviour on any bytes, through every public decoding entry point | P:9-11; ISO C |
| S2 | untrusted dictionaries: "If a dictionary is provided by an external source, it should be loaded with great care, its content considered untrusted" | F:1533-1534 |
| S3 | `ZSTD_decompress` returns "the number of bytes decompressed into `dst` (<= `dstCapacity`)", or an error | H:171 |
| S4 | streaming: `pos` "Necessarily 0 <= pos <= size", for input and output | H:704, H:710 |
| S5 | streaming: "with no additional input, amount of data flushed <= ZSTD_BLOCKSIZE_MAX" | H:936 |
| S6 | `ZSTD_freeDCtx`/`ZSTD_freeDStream`/`ZSTD_freeDDict` "accept NULL pointer" | H:305, H:912, H:1027 |
| S7 | *exp* `ZSTD_d_stableOutBuffer`: "this flag is ALWAYS memory safe, and will never access out-of-bounds memory" | H:2523 |
| S8 | decoding parameters: "Providing a value beyond bound will either clamp it, or trigger an error": any values of `ZSTD_d_windowLogMax` and the experimental `ZSTD_d_format`, `ZSTD_d_forceIgnoreChecksum`, `ZSTD_d_refMultipleDDicts`, `ZSTD_d_maxBlockSize`, `ZSTD_DCtx_setMaxWindowSize` leave decoding safe (S1) | H:682 |
| S9 | *exp* buffer-less streaming on any bytes: `ZSTD_decompressContinue` "requires this _exact_ amount of bytes, or it will fail"; its result is "necessarily <= dstCapacity" | H:3098, H:3100 |

### Decoder: every compliant frame decodes to its content

| id | promise | source |
|---|---|---|
| V1 | "A compliant decompressor must be able to decompress at least one working set of parameters"; zstd: "*must* decode any compliant frame" | F:49, P:7 |
| V2 | "The decompressed content of multiple concatenated frames is the concatenation of each frame decompressed content"; `ZSTD_decompress`: "Multiple compressed frames can be decompressed at once ... The result will be the concatenation of all decompressed frames, back to back" | F:99, H:166-167 |
| V3 | "skippable frames need just be skipped, and their content ignored" | F:999-1000 |
| V4 | a parameter it does not support: "it must produce a non-ambiguous error code" (never wrong output); zstd's documented limits: `dstCapacity` too small, streaming window above `1 << ZSTD_WINDOWLOG_LIMIT_DEFAULT` (27) or `ZSTD_d_windowLogMax`, memory allocation | F:53-55, H:646, F:196 |
| V5 | streaming: "@return : 0 when a frame is completely decoded and fully flushed", else > 0 "a suggested next input size ... that will never request more than the remaining content of the compressed frame" | H:903-905, H:938-940 |
| V6 | `ZSTD_DStreamOutSize()`: "Guarantee to successfully flush at least one complete block in all circumstances" | H:951 |
| V7 | contexts: reusable; `ZSTD_decompressDCtx` is the "Same as ZSTD_decompress()"; after an error the state must be reset (`ZSTD_DCtx_reset`, `ZSTD_initDStream`, or a new one-shot job), then it works again | H:297-308, H:941-946 |
| V8 | dictionaries: `ZSTD_decompress_usingDict` with the dictionary used for compression; "When `dict == NULL || dictSize < 8` no dictionary is used"; raw-content dictionaries (>= 8 bytes) and formatted ones (magic, ID, entropy tables, 3 repeat offsets, content); the window rule for references into the dictionary | H:972-975, F:1474-1530 |
| V9 | dictionaries through a context: `ZSTD_DCtx_loadDictionary` is sticky ("remain valid when same context is reused"), `ZSTD_DCtx_refDDict`, `ZSTD_decompress_usingDDict`; `ZSTD_DCtx_refPrefix`: "only used once" | H:1079-1081, H:1161, H:1180, H:1186, H:1198 |
| V10 | the checksum is validated by default (`ZSTD_d_forceIgnoreChecksum`: "skip checksum validation ... Default is 0"): a frame whose checksum does not match its content is an error | H:2534-2540 |
| V11 | the reserved bit of the frame header: "A decoder compliant with this specification version must ensure it is not set" | F:216 |
| V12 | *exp* `ZSTD_d_stableOutBuffer`: decoding into the caller's buffer, which must hold the whole frame | H:2502-2530 |
| V13 | *exp* in-place decompression: input at the end of an output buffer of `ZSTD_decompressionMargin + Output_Size` bytes | H:1537-1559 |
| V14 | *exp* `ZSTD_d_forceIgnoreChecksum`: "skip checksum validation during decompression, regardless of whether checksumming was specified during compression": a frame decodes to its content whatever its checksum | H:2538-2539 |
| V15 | `ZSTD_d_windowLogMax`: "a size limit (in power of 2) beyond which the streaming API will refuse to allocate memory buffer", "only useful in streaming mode, since no internal buffer is allocated in single-pass mode", 0 = the default; *exp* `ZSTD_DCtx_setMaxWindowSize`: "Refuses allocating internal buffers for frames requiring a window size larger than provided limit": frames within the limit decode | H:642-647, H:2482-2484 |
| V16 | *exp* `ZSTD_d_maxBlockSize`: "Allowed values are between 1KB and ZSTD_BLOCKSIZE_MAX (128KB)", "setting to 0 will set to the default"; "reject blocks whose content size is larger than the configured maxBlockSize", "reject otherwise valid frames that have block sizes larger than the configured maxBlockSize"; read with the format's terms (a block's "Block_Content" is its compressed bytes, and Block_Maximum_Size "is applicable to both the decompressed size and the compressed size of any block", F:388-397): frames whose blocks' decompressed and compressed sizes fit the limit decode | H:2580-2591 |
| V17 | *exp* `ZSTD_d_format` = `ZSTD_f_zstd1_magicless` (or `ZSTD_DCtx_setFormat`, "REDUNDANT"): "Variant of zstd frame format, without initial 4-bytes magic number"; "Decoder cannot recognise automatically this format, requiring this instruction" | H:1386-1388, H:2596-2600 |
| V18 | *exp* `ZSTD_d_refMultipleDDicts`: "At decompression time, the appropriate dictID is selected from the set of DDicts based on the dictID in the frame" | H:2548-2556 |
| V19 | *exp* `ZSTD_DCtx_loadDictionary_advanced`, `ZSTD_DCtx_refPrefix_advanced`: `ZSTD_dlm_byCopy`/`ZSTD_dlm_byRef`; `ZSTD_dct_auto` ("full" when starting with `ZSTD_MAGIC_DICTIONARY`, "otherwise it is rawContent"), `ZSTD_dct_rawContent` ("ensures dictionary is always loaded as rawContent, even if it starts with ZSTD_MAGIC_DICTIONARY") | H:1374-1381, H:2468-2479 |
| V20 | *exp* `ZSTD_dct_fullDict`: "refuses to load a dictionary if it does not respect Zstandard's specification, starting with ZSTD_MAGIC_DICTIONARY" | H:1376 |
| V21 | *exp, deprecated* `ZSTD_initDStream_usingDict`, `ZSTD_initDStream_usingDDict`, `ZSTD_resetDStream`: "equivalent to" `ZSTD_DCtx_reset` + `ZSTD_DCtx_loadDictionary` / `ZSTD_DCtx_refDDict` / nothing; reset: "reuse decompression parameters from previous init; saves dictionary loading" | H:2770-2800 |
| V22 | *exp* buffer-less streaming: `ZSTD_decompressBegin` (`_usingDict`, `_usingDDict`), then "ZSTD_nextSrcSizeToDecompress() and ZSTD_decompressContinue() alternatively"; the result is "the number of bytes regenerated within 'dst'"; "A frame is fully decoded when ZSTD_nextSrcSizeToDecompress() returns zero"; skippable frames: "always returns 0"; each block "next to previous one" | H:3049-3120 |

### Frame inspection

| id | promise | source |
|---|---|---|
| I1 | `ZSTD_getFrameContentSize`: the content size if present, `ZSTD_CONTENTSIZE_UNKNOWN` if not, 0 for a skippable frame, `ZSTD_CONTENTSIZE_ERROR` on an invalid magic number or too few bytes | H:180-205 |
| I2 | `ZSTD_findFrameCompressedSize`: "the compressed size of the first frame"; for a skippable frame "its content size + 8 bytes" | H:215-227 |
| I3 | `ZSTD_getDictID_fromFrame`: the frame's `Dictionary_ID`, 0 if absent; `ZSTD_getDictID_fromDict`: the ID of a conformant dictionary, 0 otherwise | H:1045, H:1062-1071 |
| I4 | *exp* `ZSTD_findDecompressedSize`: the total content size of a series of frames, or UNKNOWN / ERROR | H:1466-1487 |
| I5 | *exp* `ZSTD_decompressBound`: an upper bound of the decompressed size, exact when every frame declares its size, else "# blocks * min(128 KB, Window_Size)" per frame | H:1489-1502 |
| I6 | *exp* `ZSTD_getFrameHeader`, `ZSTD_frameHeaderSize`, `ZSTD_isFrame`, `ZSTD_isSkippableFrame`, `ZSTD_readSkippableFrame`: the header's fields, its size, the magic checks, the skippable content and magic variant | H:1504-1530, H:1729-1747, H:2448-2453 |
| I7 | `ZSTD_getDecompressedSize` (obsolete): "Both functions work the same way, but ZSTD_getDecompressedSize() blends \"empty\", \"unknown\" and \"error\" results to the same return value (0)" | H:207-212 |
| I8 | *exp* `ZSTD_getFrameHeader_advanced`: "same as ZSTD_getFrameHeader(), with added capability to select a format (like ZSTD_f_zstd1_magicless)" | H:1531-1534 |

### Compressor

| id | promise | source |
|---|---|---|
| C1 | `ZSTD_compress`: "Providing `dstCapacity >= ZSTD_compressBound(srcSize)` guarantees that zstd will have enough space to successfully compress the data"; returns a size `<= dstCapacity` | H:154-160 |
| C2 | lossless: decompressing what it compressed gives the input back, at every level from `ZSTD_minCLevel()` to `ZSTD_maxCLevel()`; "a compliant compressor must produce data sets that conform to the specifications" | R:3, F:44-46, H:86-90 |
| C3 | "decompressed size is always present when compression is completed using single-pass functions" | H:194-195 |
| C4 | streaming compression: `ZSTD_e_end` "@return : 0 if frame fully completed and fully flushed"; `ZSTD_e_continue` "is guaranteed to make some forward progress"; the frames decode to the input | H:742, H:762-772 |
| C5 | dictionary compression: decompression "using a known Dictionary ... identical to the one used during compression"; `ZSTD_compress_usingCDict` writes "dictID=yes, contentSize=yes, checksum=no" | H:970-979, H:1011, H:1033 |
| C6 | `ZSTD_COMPRESSBOUND`: "bound(A) + bound(B) <= bound(A+B) as long as A and B >= 128 KB" | H:249 |

### Not promised (no spec)

- detecting invalid input, beyond V10 and V11 (P: "best effort");
- agreement between APIs on invalid input (one-shot and streaming decoding differ on some invalid inputs);
- that `Frame_Content_Size` is right (H:199 "could be wrong or intentionally modified");
- speed, memory use (`ZSTD_estimate*`, `ZSTD_sizeof_*`), threads.

## The specs

One C file each (one `main`, one theorem). The names here are those of the harness comments; the files carry the
prefix `x_` (`any_oneshot` is `harness/x_any_oneshot.c`). The valid-frame specs draw **any compliant data**, within
the bounds of SPECS.md, from one writer, `harness/writer.h`, written from F: every block type, every literals mode
(raw, RLE, Huffman with direct or FSE-compressed weights, 1 or 4 streams, treeless), every sequence-table mode
(predefined, RLE, FSE-compressed, repeat), repeat offsets, every header form, dictionary IDs, checksums (its own
XXH64), skippable frames, several frames, and dictionaries (raw content or formatted). The writer was checked against
two decoders: on 3,500 random series, zstd and zstd's educational decoder (`doc/educational_decoder`, written from the
specification) both decode the content exactly, except for frames with 4 literals in 4 streams, which the writer then
wrote and the format forbids (F:524-531, "(6-1023)"); the writer was corrected. `harness/zlimits.h` holds zstd's
documented limits (V4).

One limit is not in zstd's documents but deliberate in its code: the streaming specs allow
`ZSTD_error_noForwardProgress_inputEmpty`/`_destFull` on the 16th call in a row that reads and writes nothing
(`zlimits.h`, `stall_error`; commit 31769ce70 "error on no forward progress": a guard against callers "caught in an
infinite loop"). A proof attempt found that `valid_stream` and `stable_out` did not allow it (the native runs never
drew 16 empty chunks in a row). It is not a bug: it is intended, and only callers that busy-loop meet it.

| spec | promises | API |
|---|---|---|
| `any_oneshot` | S1, S3, S6, V7 | `ZSTD_decompress`, `ZSTD_decompressDCtx` on a reused context, any bytes, any capacity |
| `any_stream` | S1, S4, S5, S6, V6, V7 | `ZSTD_decompressStream`, any bytes, any chunking, reset after errors; `ZSTD_DStreamOutSize() >= ZSTD_BLOCKSIZE_MAX` |
| `any_dict` | S1, S2, S3, S6 | the by-reference dictionary APIs with any dictionary bytes and any frame bytes (output and dictionary in one allocation) |
| `any_dict_copy` | S1, S2, S3, S6 | the dictionary APIs that copy the dictionary (`ZSTD_createDDict`, `ZSTD_DCtx_loadDictionary`) |
| `any_info` | S1, I1-I6 | the frame-inspection functions on any bytes: no UB, results in their documented ranges |
| `valid_oneshot` | V1-V4, V7 | any series of compliant frames: exact concatenation when `dstCapacity` holds it, else an error |
| `valid_stream` | V1-V6, S4, S5 | the same frames streamed in any chunks: exact content, 0 only at frame ends, hints within the frame |
| `valid_dict` | V8, V9, V1-V4 | any dictionary and frames that use it, through the by-reference dictionary APIs: exact content |
| `valid_dict_copy` | V8, V9, V1-V4 | the same through the APIs that copy the dictionary |
| `valid_info` | I1-I6 | the inspection functions on written frames and dictionaries: exactly the written sizes and IDs |
| `detect` | V10, V11 | a compliant frame with a wrong checksum, or with the reserved bit set: an error |
| `stable_out` | S7, V12 | *exp* `ZSTD_d_stableOutBuffer`: safe on any bytes; exact content on compliant frames |
| `valid_params` | V14-V17, V1-V5, I8 | compliant series under one parameter: checksum ignored (checksums replaced), a window limit (`ZSTD_d_windowLogMax` or `ZSTD_DCtx_setMaxWindowSize`), `ZSTD_d_maxBlockSize`, or magicless (one frame without its magic, and its header through `ZSTD_getFrameHeader_advanced`); one-shot or streaming: exact content, failures only at the documented limits |
| `valid_dict_api` | V18-V21, V8 | several dictionaries selected by ID, one-shot and streaming; the `_advanced` loaders (`byCopy`/`byRef`, `auto`/`rawContent`, a formatted dictionary loaded as raw content); `fullDict` refusing a raw one; `refPrefix_advanced`; the deprecated stream init and reset: exact content |
| `valid_bufferless` | V22, V8 | compliant series decoded with the buffer-less API, no dictionary, `_usingDict` or `_usingDDict`: exact content, requests within the frame, 0 at frame ends and throughout skippable frames |
| `any_params` | S1, S3, S4, S6, S8 | any bytes, any parameter values and dictionaries, one-shot or streaming: safe, results in range |
| `any_bufferless` | S1, S2, S9 | the buffer-less API on any bytes, requested or any sizes, any dictionary: safe, `<= dstCapacity` |
| `any_info_extra` | S1, I7, I8 | `ZSTD_getDecompressedSize` and `ZSTD_getFrameHeader_advanced` on any bytes |
| `bound` | C6 | the `ZSTD_COMPRESSBOUND` inequality (a macro of zstd.h) |

The `_copy` specs use the dictionary APIs that copy the dictionary; zstd then compares the output pointer with the end of
its own copy (`ZSTD_checkContinuity`), which CompCert's semantics (VST's) cannot do, so the patch's VST layer skips that
comparison for a copied dictionary (`gpDictCopy`, patch/GENPROOF-PATCH.md). With a by-reference dictionary the harness
puts the output and the dictionary in one allocation, where the comparison is defined.

**Not encoded**, and why:
- C1-C5, the compressor's promises (lossless round trips, `ZSTD_compressBound`, streaming and dictionary
  compression): its 23,366 lines keep positions as pointers relative to a base outside the input (`window->base = ip -
  distanceFromBase`, about 140 sites, undefined in ISO C and rejected by CompCert's semantics) and pass parameter
  structs by value; making it VST-compatible would be a rewrite, not a patch.
- V13, in-place decompression: it needs zstd's original in-place test, which compares pointers into src and dst and
  so cannot be in the configuration of the other specs (a second configuration of the decoder would need a second
  proof).
- The static-allocation API (`ZSTD_initStaticDCtx`, `ZSTD_initStaticDStream`, `ZSTD_initStaticDDict`, H:1846):
  zstd checks the workspace's alignment with `(size_t)workspace & 7`, pointer bits CompCert does not define; a patch
  would change what is checked.
- The public functions that pass a struct by value (`ZSTD_createDCtx_advanced` and others with `ZSTD_customMem`,
  `ZSTD_dParam_getBounds`): left out of the configuration (`GP_NO_STRUCT_API`); VST has no struct parameters.
- Legacy formats (v0.5-v0.7 frames, `ZSTD_LEGACY_SUPPORT`): not in this configuration (`ZSTD_LEGACY_SUPPORT=0`):
  separate older decoders.
- The block-level API (deprecated: "This API is not as well tested as our normal API, so we recommend not using it.
  We will be removing it", H:3143) and `ZSTD_copyDCtx` (deprecated: "It is misleading and has very limited utility").
- V16's rejection side (a block larger than `ZSTD_d_maxBlockSize` is rejected) and round-buffer buffer-less decoding
  (`ZSTD_decodingBufferSize_min`): the writer does not record block sizes, and changing `writer.h` would change every
  spec that includes it.
- `ZSTD_d_disableHuffmanAssembly`: no effect in this configuration (no assembly).
- `ZSTD_DCtx_getParameter` (experimental: "Get the requested decompression parameter value"): its switch ends with an
  empty `default:;` that VST has no rule for, and the function promises no more than returning the value.
- Termination: the theorems are partial correctness (VST's `semax`): a run that never returns is not a
  counterexample (CONTRACT.md).

## Changes the specs need

On the unmodified decoder, two behaviours differ from what `zstd.h` says:

1. **`ZSTD_getDictID_fromFrame` on a skippable frame** returns the frame's magic variant (0-15), where H:1062-1069 says
   it provides "the dictID required to decompressed the frame" and 0 when "This is not a Zstandard frame".
   (`valid_info`.)
2. **The streaming hint on a skippable frame**: `ZSTD_decompressStream` can ask for up to 3 bytes more than remain of
   a skippable frame with fewer than 3 bytes of user data (or before its magic number is complete), where H:903-905
   says it "will never request more than the remaining content of the compressed frame". (`valid_stream`.)

F1 and F2 (`patch/fixes.py`) change these, F3 and F4 two more, and F5-F8 (`patch/fixes2.py`) four more
(`patch/GENPROOF-PATCH.md` describes each), so no spec fails on them in the code under test.

Two expressions are undefined in ISO C but have no effect and lie outside what the specs exercise: a
decoding with a DDict compares a pointer left by the previous, possibly freed, dictionary (the `ddictIsCold` edit of
`patch/GENPROOF-PATCH.md` removes that comparison in this configuration); `ZSTD_createDDict` with an empty dictionary
keeps the caller's buffer, which zstd.h says may be freed. The specs use one dictionary per context and keep their
buffers alive.
