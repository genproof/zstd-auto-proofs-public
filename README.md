# zstd decoder: proved C specs

This repository proves 44 specs of zstd's decoder with QuickProof v0.1.0 (the `quickproof` submodule). Each spec is a
small C program, `harness/<name>.c`, that you can run. Its theorem says that for every value the spec draws, no run
has undefined behaviour (through VST's adequacy theorem, whose instance for QuickProof's environment is upcoming) and
every check in the spec holds. AI agents wrote the proofs, and Coq checks them, so nothing the agents wrote in the
proofs is trusted. AI agents drafted the specs too, and they have not had a human review yet.

**Status.** All 44 theorems are proved: the 25 short specs and the 19 `x_` specs, and `suite`, which states them
together. The proof has no admitted lemma, and `qp verify` checks it against the contract (tag `contract`).

## The specs

[SPECS.md](SPECS.md) shows how to read a spec and states each one in a sentence. The first comment of each spec
states its property in full; for the `x_` specs, the size bounds are in their code.

- 25 short specs (prefixes `rfc_`, `rj_`, `api_`, `res_`, `ck_`), 10 to 78 lines each, each quoting the text it
  comes from (RFC 8878, `zstd.h`, or the xxHash specification). They share `harness/laws_common.h` (33 lines); 14 of them also use
  `harness/frames.h` (115 lines), which writes frames of Raw and RLE blocks field by field. Together they are
  1,114 lines.
- 19 longer specs (prefix `x_`, 3,032 lines with their headers). Ten draw compliant frames, compressed blocks and
  dictionaries included, from the frame writer `harness/writer.h`; eight take any bytes; `x_bound` is about a
  macro. Their sizes are bounded (SPECS.md gives the bounds). [PROMISES.md](PROMISES.md) lists the promises of
  zstd's documents that they encode.
- One theorem per spec in `src/contracts/`, and `suite` (`src/contracts/suite.v`), which states all 44 at once.

## What a theorem says, and its limits

For each spec, `Theorem <name> : harness_safe whole_prog`, where `whole_prog` is the spec linked with the decoder.
By VST's adequacy theorem this means: for every value the spec draws, no run has undefined behaviour in CompCert's
semantics of C, and every check in the spec holds. An access outside an object or a use after `free` is undefined
behaviour, so memory safety is part of every theorem. [CONTRACT.md](CONTRACT.md) states this exactly.

- Partial correctness: a theorem is about every run that returns. Termination is not proved.
- The platform: the semantics is CompCert 3.15's for `x86_64-linux`, LP64, one thread. A binary built by another
  compiler, or for another platform, is outside the theorems. Running out of stack is not covered.
- Allocation may fail: any `malloc` may return `NULL`, and the theorems cover those runs too. When zstd returns
  `ZSTD_error_memory_allocation`, or the spec cannot allocate, the spec stops and claims nothing more about that
  run.
- The code is patched: the theorems are about zstd's decoder with the edits listed [below](#the-code-under-test),
  as `lib/` holds it. Nothing is proved about the unmodified code. The edits for the prover are tested against
  the original code, not proved equivalent.
- Inputs: in the short specs, data has any length the allocator provides, and only frame windows are limited, to
  zstd's documented limits. The `x_` specs bound their sizes, for example inputs of at most 4 KiB.
- The configuration: no assembly, no BMI2, software bit counting, memcpy-based memory access, no legacy formats,
  the plain Huffman loops (`quickproof.conf`).
  In-place decoding is left out (`GP_INPLACE` is 0), and so are the public functions that take a struct by value
  (`ZSTD_createDCtx_advanced`, `ZSTD_createDStream_advanced`, `ZSTD_createDDict_advanced`,
  `ZSTD_dParam_getBounds`). The compressor is not covered, and nothing is claimed about a function no spec calls.
- What you trust: the Coq 8.20.1 kernel; VST 2.15, with its malloc library's declarations and its adequacy theorem,
  which is not yet instantiated in Coq for QuickProof's environment (that instance is upcoming); CompCert 3.15's
  semantics of C; `clightgen` and QuickProof's translation scripts; QuickProof's model of the environment and `qp
  verify`; and the text of each spec. `quickproof/docs/GUARANTEES.md` has the full list.

## Checking the proof

Use your own QuickProof checkout at the tag `v0.1.0`:

```sh
git clone --recursive https://github.com/genproof/zstd-auto-proofs-public.git
<your quickproof>/tools/qp verify zstd-auto-proofs-public --base contract
```

`qp verify` compares this repository's framework files (the `quickproof` submodule, which pins QuickProof
v0.1.0, commit `80c8cd5`) with those of the `qp` you run. Run from your own checkout, it checks the
repository's copy; the submodule's own `qp` (`quickproof/tools/qp verify . --base contract`) would only compare
that copy with itself.

`qp verify` rebuilds every proof from a fresh clone. It checks that the specs, the code under test and the
statements are those of the tag `contract`, which holds the contract without any proof; that nothing
is admitted; and that each theorem rests only on Coq's standard axioms and the abstract predicates of VST's malloc
library. It needs 64-bit x86 Linux with the toolchain listed under "Installing" in QuickProof's README (Coq 8.20.1,
CompCert 3.15, VST 2.15); QuickProof's Docker image has the same toolchain.

## The code under test

zstd's decoder at commit
[`01b7154f1172432f8abe9b3bb9909e14a1176b7d`](https://github.com/facebook/zstd/commit/01b7154f1172432f8abe9b3bb9909e14a1176b7d)
on the dev branch (2026-09-18), after release v1.5.7. This is not a release. The decoder is `lib/common` and
`lib/decompress`, compiled as one unit (`patch/decoder.c`) with the flags of `quickproof.conf`. `lib/compress` is
here only for native tests. The scripts in `patch/` made these edits, and many changed lines carry a comment with
the original ([patch/GENPROOF-PATCH.md](patch/GENPROOF-PATCH.md) describes each one):

- idiom edits (items 1-20 in `zstdpatch.py`, and the VST layer in `vstpatch.py`): C that CompCert's semantics or
  VST cannot handle, rewritten without changing any result zstd documents; differential tests against the original
  check most of them (GENPROOF-PATCH.md gives each one's evidence). After a failed decode, the bytes left in `dst`
  and in the context may differ (items 18 and 20);
- changes F1-F8 (`fixes.py`, `fixes2.py`): each makes the code follow `zstd.h` or RFC 8878 in one case that a spec
  needs, and changes a result there; SPECS.md marks the short specs that need one;
- F9, F10 (`fixes3.py`, [docs/fixes-F9-F12.md](docs/fixes-F9-F12.md)): two expressions undefined in CompCert's C
  semantics, reached through uses that `zstd.h` allows. F9 removes pointer differences on empty buffers passed as
  `NULL`. F10 removes a comparison with a pointer into a freed buffer after one-shot decoding interrupts a stream.
  F10 also changes a stream resumed after one-shot decoding on the same context: it starts a new frame;
- F11 (`fixes4.py`): a bound on `charnum` in `FSE_readNCount`'s zero-repeat loop, results unchanged;
- F12 (`fixes5.py`): no `NULL + 0` for an empty dictionary given as `NULL`, results unchanged;
- H1 (`lawhooks.py`): one added function for the `res_` specs.

The scripts edit files in place, so do not run them on this tree. `patch/diff.sh` records how the differential test
was run; it does not run here unchanged.

## Layout

- `harness/`: the specs and their headers; `corpus.h` holds real frames for native runs.
- `lib/`: zstd's files, with the edits.
- `patch/`: the scripts that made the edits, the decoder unit `decoder.c`, the differential test, and
  `GENPROOF-PATCH.md`.
- `env.c`, `env/`: the value distributions of native and interpreter runs, part of no theorem.
- `src/contracts/`: the theorems (stated in `laws.v`, and `suite.v`); `src/zstd/`, `src/harness/`, `src/libc/`,
  `src/malloc/`: the Clight that `clightgen` generates from the C files; `src/proof/`: the proofs of the 44 specs.
- [SPECS.md](SPECS.md), [CONTRACT.md](CONTRACT.md), [CHECK.md](CHECK.md) (the checks run before any proof),
  [PROMISES.md](PROMISES.md); `docs/`: notes on fixes F9-F12 and the scripts that generate `laws.v`.

## Licence

Our files (the specs, the proofs, the scripts, the configuration and the documentation) are under the PolyForm
Noncommercial License 1.0.0 ([LICENSE.md](LICENSE.md), [NOTICE.md](NOTICE.md)), copyright 2026 GenProof. zstd's files
in `lib/` keep zstd's licence ([LICENSE](LICENSE), BSD), and [NOTICE.md](NOTICE.md) says which we altered; each
Clight file `src/**/code.v` has the licence of the C file `clightgen` generates it from.

We chose a noncommercial license to make QuickProof freely available for community use while reflecting CompCert’s
licensing restrictions. We remind users that commercial use of CompCert requires separate permission.

Maintained by Vladimir Kukharenko.
