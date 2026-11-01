(* The exact outcomes of zstd's decoder from a context in the configuration of a new one: no dictionary,
   default parameters, buffered streaming output, no DDict set.  Plain Coq, no VST.

   The decoder's specifications (zstd/Spec_api6.v: oneshot_exact, stream_exact) state that every call from
   that configuration returns what these functions say, up to a memory-allocation error.  Two contexts in
   the same abstract state, given the same calls, therefore behave alike (law api_reset).

   - os_res s cap: ZSTD_decompressDCtx on input s with capacity cap.  Some c: success, the content c
     (Zlength c <= cap); None: an error.  A function of cap as well as of s: a block whose content exceeds
     Block_Maximum_Size decodes or not depending on where zstd places the literal buffer.
   - zs_call h c: ZSTD_decompressStream's call c (the bytes it may read, ibs[ipos..isz), and the output room
     osz - opos) after the calls h since the last session reset.  None: an error; Some (r, k, dl, stall, a):
     the return value, the input consumed (in.pos moves by k), the bytes delivered (out.pos moves by
     Zlength dl), zstd's noForwardProgress after the call and the hostage byte held (0 or 1).  A function of
     the whole history: buffer sizes, oversizedDuration and the ring's wrap points depend on how earlier
     calls cut the input. *)
Require Import Coq.ZArith.ZArith Coq.Lists.List.
Import ListNotations.
Require Export Zstd.proof.model.ExCall.
Require Import Zstd.proof.model.ExHuf Zstd.proof.model.ExCSeq Zstd.proof.model.ExBlock Zstd.proof.model.ExFrame.
Require Import Zstd.proof.model.ExStream.
Local Open Scope Z_scope.

(* the decoding state of a context (entropy tables, repeat offsets, litExtraBuffer) and ZSTD_decompressBlock_internal
   on it, with the C-exact pieces the block model is built from *)
Definition xstate : Type := xst xhuf.
Definition xblock := x_block xhuf x_lits_huf ncount_c dseq_one c_offset.

Definition os_res (s: list Z) (cap: Z) : option (list Z) :=
  x_series xstate (xst_init xhuf) (xst_begin xhuf) xblock s cap.

Definition zs_call (h: list zcall) (c: zcall) : option (Z * Z * list Z * Z * Z) :=
  ExStream.zs_call xstate (xst_init xhuf) (xst_begin xhuf) xblock (x_frame xstate (xst_begin xhuf) xblock) h c.

(* sanity checks on a single-segment frame of one Raw block "abc" *)
Example os_res_raw_abc : os_res [40; 181; 47; 253; 32; 3; 25; 0; 0; 97; 98; 99] 3 = Some [97; 98; 99].
Proof. vm_compute. reflexivity. Qed.
Example os_res_raw_abc_small : os_res [40; 181; 47; 253; 32; 3; 25; 0; 0; 97; 98; 99] 2 = None.
Proof. vm_compute. reflexivity. Qed.
(* streamed in one call with room 3: the single-pass shortcut, all 12 bytes read, "abc" delivered, return 0 *)
Example zs_call_raw_abc :
  zs_call nil ([40; 181; 47; 253; 32; 3; 25; 0; 0; 97; 98; 99], 3) = Some (0, 12, [97; 98; 99], 0, 0).
Proof. vm_compute. reflexivity. Qed.
