# Contract: zstd's decoder

**The code under test.** zstd 01b7154f1172, the decoder (`lib/common` and `lib/decompress`, with `lib/zstd.h` and
`lib/zstd_errors.h`) as `patch/zstdpatch.py`, `patch/vstpatch.py`, `patch/fixes.py`, `patch/fixes2.py`,
`patch/fixes3.py`, `patch/fixes4.py`, `patch/fixes5.py` and `patch/lawhooks.py` leave it:
- idiom edits (items 1-20 and the VST layer), which change no result zstd documents;
- changes F1-F8, each of which changes one documented result;
- fixes F9, F10, F11 and F12 (`docs/fixes-F9-F12.md`). F9, F11 and F12 change no result. F10 also changes a stream
  resumed after one-shot decoding on the same context: it starts a new frame;
- the added function `ZSTD_createDCtx_advancedP` (H1).

`patch/GENPROOF-PATCH.md` describes each edit and why it is there; many changed lines carry a `genproof:` or
F-comment with the original. One unit, `patch/decoder.c`, includes the decoder's C files; the configuration (flags)
is in `quickproof.conf`. `lib/compress` is here only for the native tests; it is not code under test.

**The programs.** One per spec: `harness/<name>.c` linked with all units of `src/units.v` (`LINK=all`): the decoder
(`patch/decoder.c`), `quickproof/libc/libc.c` (memcpy, memmove, memset, memcmp, calloc: plain C, verified with the
code) and `quickproof/libc/malloc_unit.c`, translated by `quickproof/tools/clight.sh quickproof.conf` (clightgen
-normalize; malloc/free as the externals quickproof_malloc/quickproof_free; statics that clash between units renamed
per unit).

**The specs.** 44 C files in `harness/`: 25 short specs (prefixes `api_`, `ck_`, `res_`, `rfc_`, `rj_`, with the
shared headers `harness/laws_common.h` and `harness/frames.h`) and 19 longer specs (`x_`, with `harness/writer.h`,
`harness/zlimits.h`). `SPECS.md` introduces them. The native and interpreter runs use the value distributions of
`env.c` (the `x_` specs) and `env/<name>.c` (the short specs); they are not part of any theorem.

**The names.** The 19 longer specs carry the prefix `x_`: `harness/x_<name>.c`, `src/contracts/x_<name>.v`,
`Theorem x_<name>`. Their harness comments and `PROMISES.md` use the names without it.
The statics that `clight.sh` renames against a clash between units take the file's name (`x_<name>__name`).

**The claims.** `src/contracts/<name>.v` (in the proof commit, restated in `src/contracts/laws.v`): `Theorem <name> :
harness_safe whole_prog` (`quickproof/coq/QuickProof/Contract.v`): VST's `semax_prog` for `whole_prog`, with the
specifications of `QuickProof.Env` for the environment. By VST's adequacy theorem (its instance for QuickProof's
environment is upcoming), for every value the nondet_* functions return, no execution has undefined behaviour in
CompCert's Clight semantics; each spec has undefined behaviour exactly when one of its checks fails.
`src/contracts/suite.v` states all 44 specs in one theorem, `suite`. No spec is known to be false on this code.

What the claims do **not** cover:
- what each spec leaves out: its first comment states its property and its exclusions, and its code its bounds
  (SPECS.md gives the `x_` specs' bounds);
- termination (a run that never returns is not a counterexample);
- other configurations of zstd, the compressor, legacy formats, the fast Huffman loops; the patch is checked
  equivalent to the original by differential testing, not by proof.

**Frozen** after the contract (tag `contract`):
- `harness/**`, the code under test (`lib/**`, `patch/**`), `quickproof/**` (the framework), `quickproof.conf`;
- the generated `src/**/code.v` and `src/units.v`;
- in `src/contracts/*.v`: the module `Harness`, `whole_prog` and the statement (restated unchanged in
  `src/contracts/laws.v`; `qp verify` compares the elaborated statements).

**Proved** means, per theorem: **Qed**, built from a clean checkout, and **Print Assumptions <name>** lists only
standard axioms and the abstract predicates of VST's malloc library (mem_mgr, malloc_token and its facts,
create_mem_mgr). `quickproof/tools/qp verify` checks this, and that every statement is the one of the contract.

**Status.** The tag `contract` holds the contract alone: the 44 specs and their statements, without any proof. All 44
theorems and `suite` are proved; `qp verify` checks them against `contract`.
