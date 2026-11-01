(* Bounds on the exact stream model's reached states (model/Exact.v's instance of model/ExStream.v): what the proof of
   ZSTD_decompressStream needs to read the model's values back from zstd's fields, which hold them as U64 / U32
   (expected, rleSize, outStart, outEnd) or as an enumeration (stage, bType):
   - ZSTD_decompressContinue's stage is a ZSTD_dStage (0 .. DS_skipFrame), the block type one of the four;
   - expected is a constant, a block size (a 3-byte field), a skippable frame's size (a 4-byte field) or what is
     left of a raw block, so below 2^32; rleSize is a block size;
   - outStart <= outEnd <= outBuffSize at every stage (a decoding writes at most its capacity, outBuffSize -
     outStart).
   - the ring's cells are bytes and there are outBuffSize of them; the block decoder's litExtraBuffer holds bytes
     and its Huffman table's cells are in range (ExBlockBytes.xh_good), so that every block decoded into the ring
     leaves bytes (ExBlockBytes.xblock_bytes);
   - the input buffer is empty outside zdss_load (a load that completes decodes from it and empties it);
   - a compressed block about to be decoded with an extDict has room in the ring (an extDict exists only after the
     ring restarted, which happens only when a block of Block_Maximum_Size would not fit after outStart), and the
     ring offsets of previousDstEnd, prefixStart and the extDict are within the ring.
   zinv_x_bnd: every state satisfying the fuel invariant ExStreamFacts.zinv_x (every reached state, every state of
   the loop) satisfies them. *)
Require Import Coq.ZArith.ZArith.
Require Import Zstd.proof.model.Bytes Zstd.proof.model.ExStream Zstd.proof.model.ExStreamFacts.
Require Import Zstd.proof.model.ExHuf Zstd.proof.model.ExBlock Zstd.proof.model.ExBlockBytes.
Require Zstd.proof.model.Exact.
Local Open Scope Z_scope.

Definition zbnd_x (z: zstate_x) : Prop :=
  let d := zs_dc Exact.xstate z in
  0 <= d_stage Exact.xstate d <= DS_skipFrame /\ 0 <= d_btype Exact.xstate d <= 3 /\
  0 <= d_expected Exact.xstate d < 2 ^ 32 /\ 0 <= d_rle Exact.xstate d < 2 ^ 32 /\
  0 <= zs_ostart Exact.xstate z <= zs_oend Exact.xstate z /\ zs_oend Exact.xstate z <= zs_outbs Exact.xstate z /\
  bytes_ok (zs_mem Exact.xstate z) /\ Zlength (zs_mem Exact.xstate z) = zs_outbs Exact.xstate z /\
  bytes_ok (x_lxb xhuf (d_ent Exact.xstate d)) /\ xh_good (x_huf xhuf (d_ent Exact.xstate d)) /\
  (zs_stage Exact.xstate z <> ZDSS_load -> zs_ibuf Exact.xstate z = nil) /\
  (ZDSS_read <= zs_stage Exact.xstate z <= ZDSS_load ->
     (d_stage Exact.xstate d = DS_decompressBlock \/ d_stage Exact.xstate d = DS_decompressLastBlock) ->
     d_btype Exact.xstate d = 2 -> d_de Exact.xstate d <> None -> zs_ostart Exact.xstate z < zs_outbs Exact.xstate z) /\
  (forall x, d_prev Exact.xstate d = Some x \/ d_pfx Exact.xstate d = Some x \/ d_ds Exact.xstate d = Some x \/
             d_de Exact.xstate d = Some x -> 0 <= x <= zs_outbs Exact.xstate z).

(* ExStreamFacts.zinv carries these bounds (zi_dc, zi_ring, zi_buf, zi_ext), with xgood_x for the block decoder's
   state. *)
Lemma zinv_x_bnd (z: zstate_x) : zinv_x z -> zbnd_x z.
Proof.
  intros (Hd & Hr & Hb & He & _).
  destruct Hd as (Dst & Dbt & Dex & Drl & Din & [Dl Dh]).
  destruct Hr as (Ho1 & Ho2 & Hmb & Hml & Hoff).
  destruct Hb as (_ & Hn & _).
  unfold zbnd_x. cbv zeta.
  split; [exact Dst|]. split; [exact Dbt|]. split; [exact Dex|]. split; [exact Drl|].
  split; [exact Ho1|]. split; [exact Ho2|]. split; [exact Hmb|]. split; [exact Hml|].
  split; [exact Dl|]. split; [exact Dh|]. split; [intros Hs; exact (proj2 (Hn Hs))|].
  split; [|exact Hoff].
  intros Hs Hst _ Hde.
  assert (Hz: zin Exact.xstate (zs_dc Exact.xstate z)).
  { unfold zin, DS_decodeBlockHeader, DS_checkChecksum, DS_decompressBlock, DS_decompressLastBlock in *. lia. }
  destruct (He Hz) as (_ & _ & E3 & _).
  apply (proj2 (E3 ltac:(unfold ZDSS_read, ZDSS_load in *; lia))), Hde.
Qed.
