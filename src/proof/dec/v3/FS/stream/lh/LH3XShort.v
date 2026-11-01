(* ZSTD_decompressStream, case zdss_loadHeader with the exact claim: the model's single-pass shortcut (x_frame on one frame) against the one-shot model (Exact.os_res). *)
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3XDefs.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.ExFrame Zstd.proof.model.ExFrameFacts.
Require Import Zstd.proof.model.ExOneshot Zstd.proof.model.ExStreamFacts Zstd.proof.dec.FS.FramesHdr.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

(* ---------- a frame the model decodes takes exactly ZSTD_findFrameCompressedSize's bytes ---------- *)

(* ZSTD_decompressFrame's block loop and ZSTD_findFrameSizeInfo's block walk read the same block headers: a successful
   loop takes the bytes the walk counts *)
Lemma lhs_x_blocks_size (xst: Type) x_block (f: nat) (st st': xst) (t out o: list Z) (cap bsm k: Z) :
  x_blocks xst x_block f st t out cap bsm = Some (o, k, st') -> exists nb, blocks_size f t = Some (k, nb).
Proof.
  revert st t out k. induction f as [|f IH]; intros st t out k H; [discriminate|].
  cbn [x_blocks blocks_size] in *.
  destruct (cblock_size t) as [c|]; [|discriminate].
  destruct (Z.gtb_spec c (Zlength t - ZSTD_blockHeaderSize)); [discriminate|].
  destruct (Z.gtb_spec (ZSTD_blockHeaderSize + c) (Zlength t)); [lia|].
  match type of H with context [match ?r with Some _ => _ | None => None end] =>
    destruct r as [[st1 cn]|] end; [|discriminate].
  destruct (bp_last (block_props_of t) =? 1).
  - inversion H; subst. eauto.
  - destruct (x_blocks xst x_block f st1 _ _ cap bsm) as [[[o1 k1] st2]|] eqn:E; [|discriminate].
    inversion H; subst. destruct (IH _ _ _ _ E) as [nb ->]. eauto.
Qed.

(* a Zstandard frame header (not a skippable one) starts with zstd's magic number *)
Lemma lhs_gfh_magic (s: list Z) (h: frame_header) :
  get_frame_header s = FH_ok h -> is_skippable_magic (le_field s 0 4) = false ->
  ZSTD_FRAMEHEADERSIZE_PREFIX <= Zlength s /\ le_field s 0 4 = ZSTD_MAGICNUMBER.
Proof.
  intros H Hm. unfold get_frame_header in H.
  destruct (Z.ltb_spec (Zlength s) 5).
  { destruct (Zlength s >? 0); [destruct (negb _ && negb _)|]; discriminate. }
  destruct (Z.eqb_spec (le_field s 0 4) ZSTD_MAGICNUMBER) as [E|E].
  - unfold ZSTD_FRAMEHEADERSIZE_PREFIX. auto.
  - cbn [negb] in H. rewrite Hm in H. discriminate.
Qed.

(* the bytes a successful x_frame takes are the frame's compressed size *)
Lemma lhs_x_frame_fcs (xst: Type) xst_begin x_block (st st': xst) (x c: list Z) (cap k K: Z) :
  bytes_ok x -> frame_compressed_size x = Some K -> is_skippable_magic (le_field x 0 4) = false ->
  x_frame xst xst_begin x_block st x cap = Some (c, k, st') -> k = K.
Proof.
  intros Hb HK Hm H.
  destruct (Z.ltb_spec (Zlength x) (ZSTD_FRAMEHEADERSIZE_MIN + ZSTD_blockHeaderSize)) as [Hl|Hl].
  { rewrite x_frame_short in H by exact Hl. discriminate. }
  destruct (Z.ltb_spec (Zlength x) (fhd_header_size (byte_at x 4) + ZSTD_blockHeaderSize)) as [Hl2|Hl2].
  { rewrite x_frame_short_hs in H by exact Hl2. discriminate. }
  rewrite x_frame_eq in H by lia. cbv zeta in H.
  unfold frame_compressed_size in HK. rewrite Hm, andb_false_r in HK.
  destruct (get_frame_header x) as [| |h] eqn:Eh; try discriminate.
  destruct (lhs_gfh_magic x h Eh Hm) as [Hp Hmg].
  destruct (fh_gfh_ok x h Hb Hmg Eh) as (_ & Hhs & _).
  assert (Es: slice x 0 (fhd_header_size (byte_at x 4)) = firstn (Z.to_nat (fhd_header_size (byte_at x 4))) x)
    by reflexivity.
  rewrite Es, (get_frame_header_prefix x Hb Hp Hmg) in H by (unfold ZSTD_blockHeaderSize in *; lia).
  rewrite Eh in H. rewrite <- Hhs in H.
  destruct (negb (fh_dictID h =? 0)); [discriminate|].
  destruct (x_blocks _ _ _ _ _ _ _ _) as [[[out kb] st1]|] eqn:E; [|discriminate].
  destruct (lhs_x_blocks_size _ _ _ _ _ _ _ _ _ _ _ E) as [nb Ebs]. rewrite Ebs in HK.
  unfold x_fend in H.
  destruct (negb _ && negb _); [discriminate|].
  destruct (fh_checksumFlag h =? 1).
  - destruct (Zlength x - fh_headerSize h - kb <? 4); [discriminate|].
    destruct (negb _); [discriminate|]. inversion H; subst.
    destruct (Zlength x - (fh_headerSize h + kb) <? 4); inversion HK; lia.
  - inversion H; inversion HK; subst. lia.
Qed.

Local Open Scope logic.

Section CM_LH3XShort_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.

Lemma lh_short_model_ok : lh_short_model.
Proof.
  intros st x cap Hb HK Hm Hl.
  assert (Hp: ZSTD_FRAMEHEADERSIZE_PREFIX <= Zlength x).
  { unfold frame_compressed_size in HK. rewrite Hm, andb_false_r in HK.
    destruct (get_frame_header x) as [| |h] eqn:Eh; try discriminate.
    exact (proj1 (lhs_gfh_magic x h Eh Hm)). }
  rewrite os_res_rest, (xs_rest_frame st) by (unfold lxb_ok; assumption).
  rewrite Zlength_nil, Z.sub_0_r. unfold xframe1.
  destruct (x_frame _ _ _ st x cap) as [[[c k] st']|] eqn:E; [|reflexivity].
  rewrite (lhs_x_frame_fcs _ _ _ _ _ _ _ _ _ _ Hb HK Hm E), Z.eqb_refl.
  rewrite skipn_all2 by (rewrite Zlength_correct; lia).
  rewrite xs_rest_end by (rewrite Zlength_nil; unfold ZSTD_FRAMEHEADERSIZE_PREFIX; lia). reflexivity.
Qed.

End CM_LH3XShort_1.
