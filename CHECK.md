# zstd: the check before the proof

Every spec was run before any proof, on the code under test of this repository (zstd 01b7154f1172 with items 1-20,
F1-F8 and H1 of `patch/GENPROOF-PATCH.md`), with QuickProof v0.1.0-beta.1 (`tools/qp`), on 2026-10-24. The table
below is the check before F9 to F12. The checks of F9 to F12 (interpreter scenarios, all specs again natively, the
streaming specs in the interpreter, differential tests) are in `docs/fixes-F9-F12.md`; that of the `res_free`
correction is in SPECS.md ("Harness corrections").

The corrections of `rj_content_size` and `api_untouched_output` (SPECS.md, "Harness corrections") were checked the
same way: natively, 400 runs each, both pass on this code, and on upstream they fail as before
(`api_untouched_output` 5/400, `rj_content_size` 38/400); in CompCert's interpreter, 6 runs each, no stop. With the
pick of the declared size forced to 2^64 - 1, the old `rj_content_size` harness fails 89/300 on this code and the
new one passes 300/300.

- Native runs (`qp fuzz`, AddressSanitizer and UndefinedBehaviorSanitizer, 400 runs per spec, the value
  distributions of `env.c` and `env/<name>.c`): every spec passes. On upstream zstd (no patch) the specs that the
  fixes are for fail: `x_valid_info` (F1), `x_valid_stream` (F2), `api_dict_id` (F1), `api_untouched_output` (F7),
  `rj_content_size` (F6); the `res_` specs need the hook H1, which upstream does not have. F5 (`rfc_skippable`,
  `api_frame_size`) needs a 4 GiB skippable frame and F8 (`api_reset`) crafted frames after a reset, which the
  distributions rarely produce; their counterexamples on upstream are proofs of concept (not published).
- MemorySanitizer with a memcpy and a memmove that check their source (1000 runs per spec): no copy of a
  never-written byte. QuickProof's memcpy and memmove are byte loops through `unsigned char`, stuck in CompCert's
  semantics on such a byte; without items 19 and 20 `x_any_stream` and `x_any_params` show it
  (`patch/GENPROOF-PATCH.md`, "The framework part").
- CompCert's interpreter (`qp interp`, the semantics of the theorems, with QuickProof's libc): no stop. Runs that
  hit the per-run time limit are counted as timed out (the frame writer of the `x_valid_*` specs is slow in the
  interpreter); they show nothing either way. Every run of nine `x_` specs timed out, and `x_valid_dict` started
  none.

The short specs were also checked on the code without items 19 and 20: more native runs, 37 mutants of the decoder
written for them (each spec notices at least one, some only rarely: `api_flush_bound` in 1 of 20,000 runs,
`api_reset` the partial revert of F8 in 1 of 300), 60 random mutants (11 noticed by some spec), and runs that reach
every `gp_assert`. The `x_` specs were checked earlier with 3,000 native runs per spec, allocation failures and
mutants (records not published).

| spec | native, this code (ASan/UBSan) | native, upstream | MemorySanitizer + checking memcpy/memmove | CompCert interpreter |
|---|---|---|---|---|
| `api_content_size` | ok (400 runs) | ok (400 runs) | 1000 runs: ok 1000, FAILED 0 | ok (6 runs, no stop) |
| `api_dict_id` | ok (400 runs) | FAILED 181/400, first: seed 2 (signal 6) | 1000 runs: ok 1000, FAILED 0 | ok (6 runs, no stop; 2 timed out) |
| `api_flush_bound` | ok (400 runs) | ok (400 runs) | 1000 runs: ok 1000, FAILED 0 | ok (6 runs, no stop; 1 timed out) |
| `api_frame_size` | ok (400 runs) | ok (400 runs) | 1000 runs: ok 1000, FAILED 0 | ok (6 runs, no stop; 1 timed out) |
| `api_free_null` | ok (400 runs) | ok (400 runs) | 1000 runs: ok 1000, FAILED 0 | ok (6 runs, no stop) |
| `api_ignore_checksum` | ok (400 runs) | ok (400 runs) | 1000 runs: ok 1000, FAILED 0 | ok (6 runs, no stop) |
| `api_reset` | ok (400 runs) | ok (400 runs) | 1000 runs: ok 1000, FAILED 0 | ok (6 runs, no stop) |
| `api_short_output` | ok (400 runs) | ok (400 runs) | 1000 runs: ok 1000, FAILED 0 | ok (6 runs, no stop) |
| `api_split_invariant` | ok (400 runs) | ok (400 runs) | 1000 runs: ok 1000, FAILED 0 | ok (6 runs, no stop; 3 timed out) |
| `api_untouched_output` | ok (400 runs) | FAILED 5/400, first: seed 28 (signal 6) | 1000 runs: ok 1000, FAILED 0 | ok (6 runs, no stop) |
| `ck_xxh64` | ok (400 runs) | ok (400 runs) | 1000 runs: ok 1000, FAILED 0 | ok (6 runs, no stop) |
| `res_free` | ok (400 runs) | build failed | 1000 runs: ok 1000, FAILED 0 | ok (6 runs, no stop; 1 timed out) |
| `res_memory_oneshot` | ok (400 runs) | build failed | 1000 runs: ok 1000, FAILED 0 | ok (6 runs, no stop; 1 timed out) |
| `res_memory_stream` | ok (400 runs) | build failed | 1000 runs: ok 1000, FAILED 0 | ok (6 runs, no stop) |
| `rfc_concat` | ok (400 runs) | ok (400 runs) | 1000 runs: ok 1000, FAILED 0 | ok (6 runs, no stop; 1 timed out) |
| `rfc_frame` | ok (400 runs) | ok (400 runs) | 1000 runs: ok 1000, FAILED 0 | ok (6 runs, no stop) |
| `rfc_skippable` | ok (400 runs) | ok (400 runs) | 1000 runs: ok 1000, FAILED 0 | ok (6 runs, no stop; 1 timed out) |
| `rj_any_dict` | ok (400 runs) | ok (400 runs) | 1000 runs: ok 1000, FAILED 0 | ok (6 runs, no stop) |
| `rj_any_input` | ok (400 runs) | ok (400 runs) | 1000 runs: ok 1000, FAILED 0 | ok (6 runs, no stop; 1 timed out) |
| `rj_any_stream` | ok (400 runs) | ok (400 runs) | 1000 runs: ok 1000, FAILED 0 | ok (6 runs, no stop) |
| `rj_bad_checksum` | ok (400 runs) | ok (400 runs) | 1000 runs: ok 1000, FAILED 0 | ok (6 runs, no stop) |
| `rj_content_size` | ok (400 runs) | FAILED 38/400, first: seed 1 (signal 6) | 1000 runs: ok 1000, FAILED 0 | ok (6 runs, no stop; 1 timed out) |
| `rj_reserved_bit` | ok (400 runs) | ok (400 runs) | 1000 runs: ok 1000, FAILED 0 | ok (6 runs, no stop) |
| `rj_reserved_block` | ok (400 runs) | ok (400 runs) | 1000 runs: ok 1000, FAILED 0 | ok (6 runs, no stop) |
| `rj_truncated` | ok (400 runs) | ok (400 runs) | 1000 runs: ok 1000, FAILED 0 | ok (6 runs, no stop) |
| `x_any_bufferless` | ok (400 runs) | ok (400 runs) | 1000 runs: ok 1000, FAILED 0 | ok (20 runs, no stop; 4 timed out) |
| `x_any_dict` | ok (400 runs) | ok (400 runs) | 1000 runs: ok 1000, FAILED 0 | ok (20 runs, no stop; 8 timed out) |
| `x_any_dict_copy` | ok (400 runs) | ok (400 runs) | 1000 runs: ok 1000, FAILED 0 | ok (20 runs, no stop; 8 timed out) |
| `x_any_info` | ok (400 runs) | ok (400 runs) | 1000 runs: ok 1000, FAILED 0 | ok (20 runs, no stop; 4 timed out) |
| `x_any_info_extra` | ok (400 runs) | ok (400 runs) | 1000 runs: ok 1000, FAILED 0 | ok (20 runs, no stop; 4 timed out) |
| `x_any_oneshot` | ok (400 runs) | ok (400 runs) | 1000 runs: ok 1000, FAILED 0 | ok (20 runs, no stop; 7 timed out) |
| `x_any_params` | ok (400 runs) | ok (400 runs) | 1000 runs: ok 1000, FAILED 0 | ok (20 runs, no stop; 4 timed out) |
| `x_any_stream` | ok (400 runs) | ok (400 runs) | 1000 runs: ok 1000, FAILED 0 | ok (20 runs, no stop; 4 timed out) |
| `x_bound` | ok (400 runs) | ok (400 runs) | 1000 runs: ok 1000, FAILED 0 | ok (20 runs, no stop) |
| `x_detect` | ok (400 runs) | ok (400 runs) | 1000 runs: ok 1000, FAILED 0 | ok (20 runs, no stop; 20 timed out) |
| `x_stable_out` | ok (400 runs) | ok (400 runs) | 1000 runs: ok 1000, FAILED 0 | ok (20 runs, no stop; 20 timed out) |
| `x_valid_bufferless` | ok (400 runs) | ok (400 runs) | 1000 runs: ok 1000, FAILED 0 | ok (20 runs, no stop; 20 timed out) |
| `x_valid_dict` | ok (400 runs) | ok (400 runs) | 1000 runs: ok 1000, FAILED 0 | timeout after 2400s (0 runs started) |
| `x_valid_dict_api` | ok (400 runs) | ok (400 runs) | 1000 runs: ok 1000, FAILED 0 | ok (20 runs, no stop; 20 timed out) |
| `x_valid_dict_copy` | ok (400 runs) | ok (400 runs) | 1000 runs: ok 1000, FAILED 0 | ok (20 runs, no stop; 20 timed out) |
| `x_valid_info` | ok (400 runs) | FAILED 64/400, first: seed 1 (signal 6) | 1000 runs: ok 1000, FAILED 0 | ok (20 runs, no stop; 20 timed out) |
| `x_valid_oneshot` | ok (400 runs) | ok (400 runs) | 1000 runs: ok 1000, FAILED 0 | ok (20 runs, no stop; 20 timed out) |
| `x_valid_params` | ok (400 runs) | ok (400 runs) | 1000 runs: ok 1000, FAILED 0 | ok (20 runs, no stop; 20 timed out) |
| `x_valid_stream` | ok (400 runs) | FAILED 6/400, first: seed 37 (signal 6) | 1000 runs: ok 1000, FAILED 0 | ok (20 runs, no stop; 20 timed out) |
