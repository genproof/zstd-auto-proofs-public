# Fixes F9, F10, F11 and F12

Proving the 25 short specs exposed expressions that CompCert's C semantics leaves undefined, or that VST cannot
type (F9, F10, F12), reached by uses of the API that zstd.h allows, and needed a loop bound (F11). Wherever such an
expression can be reached, `harness_safe` is false. The specs stay as they are. `patch/fixes3.py` (F9, F10),
`patch/fixes4.py` (F11) and `patch/fixes5.py` (F12) run in that order after `fixes2.py`, before `lawhooks.py`, and
change the code so that the specs hold. Each replacement is asserted to match once, and every changed line carries
its F-number. F9, F11 and F12 change no result. F10 also changes a stream resumed after one-shot decoding on its
context. The sections below give each fix and its checks.

## F9: pointer differences on NULL (specs `rj_any_stream`, `api_untouched_output`, `api_short_output`)

**The expression.** zstd.h allows an empty buffer to be NULL (`src`/`dst` NULL with `size` 0). `ZSTD_decompressStream`
avoids `NULL + 0` for such a buffer (`input->size != 0 ? src + input->size : src`), but then computes differences of
its NULL pointers. Examples: `(size_t)(iend-ip)` in `zdss_loadHeader` (a new stream's first call with `{NULL, 0, 0}`),
`(size_t)(oend-op)` in the single-pass test, `ip - istart`, `oend - op` in the flush, and at the end
`ip - (const char*)(input->src)` and `op - (char*)(output->dst)`. One-shot decoding has the same defect.
`ZSTD_decompress(NULL, 0, ..)` and the other one-shot functions reach `ZSTD_decompressFrame`, whose
`ostart = op = oend = NULL` give `(size_t)(oend-op)` (the Raw and RLE block copies), `op - ostart`, and
`ZSTD_decompressMultiFrame`'s `(BYTE*)dst - (BYTE*)dststart`.

**Why undefined.** ISO C 6.5.6p9: both operands of a pointer subtraction point into (or one past) the same array
object. NULL points to no object. In CompCert (`Cop.sem_sub`, `sub_case_pp`) a pointer difference is defined only
for two `Vptr` of one block. On a 64-bit target NULL is `Vlong 0`, so `NULL - NULL` is stuck. VST's typechecker
refuses it too (`denote_tc_samebase`). In the theorems' world malloc may return NULL for 0 bytes (`malloc_spec'`, as
ISO C 7.22.3 allows), so the harnesses' `copy_of(.., 0)`, `malloc(0)` and `any_bytes(0)` give exactly such buffers
(`api_short_output`: `dst = malloc(cap)` with `cap = 0`).

**Run in CompCert's interpreter** (scenarios not published, on the code before and after F9; the interpreter's
`malloc(0)` is never NULL, so the scenarios pass NULL themselves):
- a new stream, `ZSTD_decompressStream(zds, &{out, 16, 0}, &{NULL, 0, 0})`: before F9, "Stuck state: in function
  ZSTD_decompressStream, expression remainingInput = (unsigned long long) (0LL - 0LL)"; after F9 it returns the hint 8;
- the empty frame `28 b5 2f fd 20 00 01 00 00` streamed into `{NULL, 0, 0}`: before F9, stuck on `(0LL - 0LL)` in the
  single-pass test; after F9 it returns 0, input consumed;
- `ZSTD_decompress(NULL, 0, ..)` on the 1-byte frame `28 b5 2f fd 20 01 09 00 00 'b'`: before F9, stuck on
  `ZSTD_copyRawBlock(0LL, (unsigned long long) (0LL - 0LL), ..)` in `ZSTD_decompressFrame`; after F9 it returns
  `dstSize_tooSmall`, and an empty skippable frame into `(NULL, 0)` returns 0.

**The edit.** An empty buffer passed as NULL gets a non-NULL base: `ZSTD_emptyBuffer`, a 1-byte static const object,
never read or written (every access through it has size 0). In `ZSTD_decompressStream` the base is used for both
buffers, and the positions are computed from it. In `ZSTD_decompressMultiFrame`, the one entry of every one-shot
function, `dst` takes the base, so `ZSTD_decompressFrame` and everything under it get a pointer. All pointers of a
call then point into one object. The caller's descriptor is unchanged: `ZSTD_checkOutBuffer`
and `expectedOutBuffer` still see the caller's NULL. An empty NULL buffer now behaves exactly like an empty
non-NULL buffer (a 0-byte object), which the code and its proof already handle. Upstream zstd uses the same idiom
in `BIT_reloadDStream` (`static const BitContainerType zeroFilled`).

```diff
diff --git a/lib/decompress/zstd_decompress.c b/lib/decompress/zstd_decompress.c
index c4657f5..fe698df 100644
--- a/lib/decompress/zstd_decompress.c
+++ b/lib/decompress/zstd_decompress.c
@@ -1071,6 +1071,9 @@ static size_t ZSTD_decompressFrame(ZSTD_DCtx* dctx,
     return (size_t)(op-ostart);
 }
 
+/* F9: the base of an empty buffer passed as NULL; never read or written (every access through it has size 0) */
+static const BYTE ZSTD_emptyBuffer[1] = { 0 };
+
 static
 ZSTD_ALLOW_POINTER_OVERFLOW_ATTR
 size_t ZSTD_decompressMultiFrame(ZSTD_DCtx* dctx,
@@ -1079,10 +1082,12 @@ size_t ZSTD_decompressMultiFrame(ZSTD_DCtx* dctx,
                                   const void* dict, size_t dictSize,
                                   const ZSTD_DDict* ddict)
 {
-    void* const dststart = dst;
+    void* const dststart = dst != NULL ? dst : (void*)ZSTD_emptyBuffer;   /* F9: was dst: no pointer difference on NULL */
     int moreThan1Frame = 0;
 
     DEBUGLOG(5, "ZSTD_decompressMultiFrame");
+    dctx->streamStage = zdss_init;   /* F10: one-shot decoding ends a streaming frame left unfinished (its state, previousDstEnd included, is overwritten) */
+    dst = dststart;   /* F9 */
     assert(dict==NULL || ddict==NULL);  /* either dict or ddict set, not both */
 
     if (ddict) {
@@ -2133,11 +2138,11 @@ static size_t ZSTD_decompressContinueStream(
 
 size_t ZSTD_decompressStream(ZSTD_DStream* zds, ZSTD_outBuffer* output, ZSTD_inBuffer* input)
 {
-    const char* const src = (const char*)input->src;
+    const char* const src = input->src != NULL ? (const char*)input->src : (const char*)ZSTD_emptyBuffer;   /* F9: was (const char*)input->src: no pointer difference on NULL */
     const char* const istart = input->pos != 0 ? src + input->pos : src;
     const char* const iend = input->size != 0 ? src + input->size : src;
     const char* ip = istart;
-    char* const dst = (char*)output->dst;
+    char* const dst = output->dst != NULL ? (char*)output->dst : (char*)ZSTD_emptyBuffer;   /* F9: was (char*)output->dst */
     char* const ostart = output->pos != 0 ? dst + output->pos : dst;
     char* const oend = output->size != 0 ? dst + output->size : dst;
     char* op = ostart;
@@ -2398,8 +2403,8 @@ size_t ZSTD_decompressStream(ZSTD_DStream* zds, ZSTD_outBuffer* output, ZSTD_inB
     }   }
 
     /* result */
-    input->pos = (size_t)(ip - (const char*)(input->src));
-    output->pos = (size_t)(op - (char*)(output->dst));
+    input->pos = (size_t)(ip - src);   /* F9: was (size_t)(ip - (const char*)(input->src)) */
+    output->pos = (size_t)(op - dst);   /* F9: was (size_t)(op - (char*)(output->dst)) */
 
     /* Update the expected output buffer for ZSTD_obm_stable. */
     ZSTD_outBuffer_copy(&zds->expectedOutBuffer, output);   /* genproof: was zds->expectedOutBuffer = *output */
```

**Behaviour unchanged.** A differential test (not published) ran 1,000 random inputs: one-shot
decoding of each into an empty output (`ZSTD_decompressDCtx`, `ZSTD_decompress`), then a stream of it (40,000 calls):
corpus frames, sometimes altered, in random pieces, with random output room and start positions, in buffered mode
and with `ZSTD_d_stableOutBuffer`, resetting after errors. Three configurations gave identical traces (every
result, both positions, a hash of the output): the new code with empty buffers passed as NULL, the new code with
empty buffers passed as 0-size objects, and the code before F9 with 0-size objects. AddressSanitizer and
UndefinedBehaviorSanitizer reported nothing.

**What remains for `api_untouched_output`.** After F9 the spec holds in CompCert's semantics. The harness itself,
with `out == NULL` (room 0), evaluates `out + output.pos` and `before + output.pos` in its check. CompCert defines
`NULL + 0` on a 64-bit target (`Cop.sem_add_ptr_long`, case `Vlong, Vlong`), but VST's typechecker requires a
pointer (`tc_isptr`). The spec is true, but VST cannot prove it as stated. A correction of the harness skips the
comparison when `room == 0` (an empty output has nothing to compare); see SPECS.md, "Harness corrections".

## F10: a dangling `previousDstEnd` after one-shot decoding (spec `res_free`)

**The expression.** Take a stream left inside a frame (`streamStage = zdss_read`). One-shot decoding on the same
context (`ZSTD_decompressDCtx`, `ZSTD_decompress_usingDict`, `ZSTD_decompress_usingDDict`, all through
`ZSTD_decompressMultiFrame`) sets `previousDstEnd` into the caller's `dst` and leaves `streamStage` as it was. The
caller frees `dst`. The next `ZSTD_decompressStream` resumes the old frame, and `ZSTD_checkContinuity` (through
`ZSTD_decompressContinue`) evaluates `dst != dctx->previousDstEnd` with a pointer into the freed block.

**Why undefined.** In CompCert (`Val.cmplu_bool`) comparing pointers into two different blocks is defined only when
both are valid pointers. A pointer into a freed block is not (VST: `denote_tc_comparable`). In ISO C the value of a
pointer to a freed object is indeterminate (6.2.4p2), so using it is undefined.

**Run in CompCert's interpreter.** A stream reads the 6-byte header of a frame without a content size. Then
`ZSTD_decompressDCtx` decodes the frame `28 b5 2f fd 20 03 19 00 00 'x' 'y' 'z'` into `dst2`, `dst2` is freed, and
the stream goes on with the rest of the first frame. Before F10: "Stuck state: in function ZSTD_checkContinuity,
expression (_Bool) (<ptr> != <ptr>)". After F10 the run ends without a stop: the stream starts a new frame and
reports an error for the bytes, which are not a frame.

**The edit.** One-shot decoding ends a streaming frame left unfinished: `ZSTD_decompressMultiFrame` sets
`streamStage = zdss_init`, as `ZSTD_DCtx_reset(.., ZSTD_reset_session_only)` does. The next `ZSTD_decompressStream`
starts a new frame, and its `ZSTD_decompressBegin` clears `previousDstEnd` before any comparison. Results change only
for a stream resumed after a one-shot decoding on its context. Its frame state (`stage`, `expected`, the frame
header, the entropy tables, `previousDstEnd`) was overwritten by that decoding, so resuming could not have decoded
the old frame anyway. The stream's own single-pass shortcut also goes through `ZSTD_decompressMultiFrame`. It sets
`zdss_init` itself after success; after an error the stage is now `zdss_init` instead of `zdss_loadHeader`, while
zstd.h requires a reset after an error.

(The diff of F10 is the `streamStage` line in the diff of F9 above, in `ZSTD_decompressMultiFrame`.)

## F11: a bound on `charnum` in `FSE_readNCount` (specs `rj_any_dict`, `api_reset`)

`patch/fixes4.py` (after `fixes3.py`) changes one loop condition in `FSE_readNCount_body`: the zero-repeat loop
`while (repeats >= 12)` is now `while (repeats >= 12 && charnum < maxSV1)`. With it `charnum` stays bounded, which
the specification of `FSE_readNCount` for headers of any length needs, and a header with too many symbols gets the
function's existing error. The result of `FSE_readNCount` is unchanged: a differential test of the function before
and after the edit on 200,000 headers (random bytes and runs of repeat flags, lengths 8 to 4096, maximum symbol
values 0 to 255) gave identical return values, maximum symbol values, table logs and counts.
All 44 specs natively on the code with F11 (`qp fuzz`, ASan/UBSan, 300 runs each): every spec passes.

## F12: `NULL + 0` with an empty dictionary (spec `res_free`)

`ZSTD_createDDict(NULL, 0)` is accepted on purpose (`zstd_ddict.c`: `dictContent = dict`, and `dictSize = 0` when
`dict` is NULL). Decoding with that DDict ran `ZSTD_copyDDictParameters`, which computed
`dctx->dictEnd = dictContent + dictSize`, that is `NULL + 0`: undefined in ISO C (6.5.6p8; UBSan reports "applying
zero offset to null pointer"). CompCert defines it, but VST's typechecker does not accept `+` on a null pointer, so the
path could not be proved. `patch/fixes5.py` (after `fixes4.py`) makes the end the start itself when the size is 0:
the same value in every execution, so no result of the decoder changes. Only `f_ZSTD_copyDDictParameters` changes in
the Clight. All 44 specs natively on the code with F12 (`qp fuzz`, 300 runs each): every spec passes.

## Checks

- CompCert's interpreter: the four scenarios above, stuck before, no stop after; `qp interp` (6 runs each) of
  `rj_any_stream`, `api_untouched_output`, `api_short_output`, `res_free`, `api_reset`, `api_flush_bound`,
  `res_memory_stream`: no stop.
- Native (`qp fuzz`, ASan/UBSan, 300 runs per spec, all 44 specs): every spec passes on this code.
- The F9 differential test above.
