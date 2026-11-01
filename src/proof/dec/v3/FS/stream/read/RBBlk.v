(* FS3 streaming, zdss_read: block-level helpers for zunit_err_cap3, copied from
   modelw/MW3Unit1, MW3Unit2, MW3Hist under new stems. *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Block Zstd.proof.model.Xxh64 Zstd.proof.model.Info Zstd.proof.model.Series Zstd.proof.model.StreamModel Zstd.proof.model.Params Zstd.proof.model.ParamsH Zstd.proof.model.ParamsW.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Require Import Zstd.proof.dec.v3.FS.stream.S3ModelStmts Zstd.proof.dec.v3.FS.stream.read.RBBase Zstd.proof.dec.v3.FS.stream.read.RBFrame Zstd.proof.dec.v3.FS.stream.read.RBFrameM Zstd.proof.dec.v3.FS.stream.read.RBWalk.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

Lemma hdr_skip_false3 : forall mg hdr h r, get_frame_header_m mg hdr = FH_ok h -> fh_frameType h = 0 ->
  negb mg && is_skippable_magic (le_field (hdr ++ r) 0 4) = false.
Proof.
  intros. destruct mg; [reflexivity|].
  destruct (gfhm_info _ _ _ H) as [[_ [Ht _]]|[_ [H5 [Hm _]]]]; [congruence|].
  cbn [starting_len] in H5. unfold ZSTD_FRAMEHEADERSIZE_PREFIX in H5.
  rewrite le_field_app, Hm by lia. reflexivity.
Qed.

Lemma app_ne_nil_l : forall (a b: list Z), a <> nil -> a ++ b <> nil.
Proof. intros. destruct a; [congruence|discriminate]. Qed.

Lemma hdr_ne_nil3 : forall mg hdr h, get_frame_header_m mg hdr = FH_ok h -> hdr <> nil.
Proof.
  intros. apply gfhm_len in H. pose proof (starting_len_pos mg). intro E. subst.
  change (Zlength (@nil Z)) with 0 in H. lia.
Qed.

Definition blk_body (dw: bool) (st: dstate) (hist: list Z) (bp: block_props) (body out: list Z) (c bsm ws: Z)
    : option (dstate * list Z) :=
  if bp_type bp =? 0 then (if c >? bsm then None else Some (st, out ++ body))
  else if bp_type bp =? 1 then
    (if (bp_origSize bp >? bsm) || (c >? bsm) then None
     else Some (st, out ++ repeat (byte_at body 0) (Z.to_nat (bp_origSize bp))))
  else match dec_block dw st hist out body bsm ws with
       | Some (st', content) => Some (st', out ++ content)
       | None => None
       end.

Lemma br_eq : forall dw st hist s out bsm ws c, cblock_size s = Some c -> c <= Zlength s - 3 ->
  block_res dw st hist s out bsm ws =
  match blk_body dw st hist (block_props_of s) (slice s 3 c) out c bsm ws with
  | None => None
  | Some (st', out') => Some (st', out', 3 + c, bp_last (block_props_of s) =? 1)
  end.
Proof.
  intros. unfold block_res. rewrite H. unfold ZSTD_blockHeaderSize.
  replace (c >? Zlength s - 3) with false by (symmetry; apply Zgtb_le; lia). reflexivity.
Qed.

Lemma slice_hdr : forall bh t k, Zlength bh = 3 -> slice (bh ++ t) 3 k = firstn (Z.to_nat k) t.
Proof.
  intros. unfold slice. rewrite skipn_app. rewrite Zlength_correct in H.
  replace (Z.to_nat 3) with (length bh) by lia. rewrite skipn_all, Nat.sub_diag. auto.
Qed.

Lemma dec_block_lenient : forall dw st hist out b bsm ws x,
  dec_block dw st hist out b bsm ws = Some x -> decode_block st hist out b bsm ws = Some x.
Proof. intros [|] st hist out b bsm ws x H; [exact (pw_decode_block_w _ _ _ _ _ _ _ H)|exact H]. Qed.

Lemma origSize_nonneg : forall s, bytes_ok s -> 0 <= bp_origSize (block_props_of s).
Proof.
  intros. unfold block_props_of. cbn [bp_origSize]. rewrite Z.shiftr_div_pow2 by lia.
  pose proof (le_field_bound s 0 3 H ltac:(lia)). apply Z.div_pos; lia.
Qed.

Lemma Zlength_repeat : forall (x: Z) n, Zlength (repeat x n) = Z.of_nat n.
Proof. intros. rewrite Zlength_correct, repeat_length. auto. Qed.

Lemma lz_copy_grow : forall ml hist out offset, exists d, lz_copy hist out offset ml = out ++ d.
Proof.
  induction ml; intros; simpl; [exists nil; rewrite app_nil_r; auto|].
  destruct (IHml hist (out ++ [byte_at (hist ++ out) (Zlength hist + Zlength out - offset)]) offset) as [d ->].
  eexists. rewrite <- app_assoc. eauto.
Qed.

(* a copy from within the frame's output does not see the history *)
Lemma lz_copy_nil : forall ml hist out offset, offset <= Zlength out ->
  lz_copy hist out offset ml = lz_copy nil out offset ml.
Proof.
  induction ml; intros hist out offset Ho; simpl; auto.
  replace (Zlength hist + Zlength out - offset) with (Zlength hist + (Zlength out - offset)) by lia.
  rewrite byte_at_app_r by lia.
  apply IHml. rewrite Zlength_app. change (Zlength [byte_at out (Zlength out - offset)]) with 1. lia.
Qed.

Lemma exec_seqs_w_wrap : forall wsize hist seqs, Forall (fun sq => 0 <= sq_ml sq) seqs ->
  forall rep lits out, wsize < Zlength out ->
  exec_seqs_w wsize rep hist lits out seqs = exec_seqs_w wsize rep nil lits out seqs.
Proof.
  intros wsize hist seqs HF. induction HF as [|sq rest Hml Hrest IH]; intros rep lits out Hw; simpl; [reflexivity|].
  destruct (sq_ll sq >? Zlength lits); [reflexivity|].
  destruct (resolve_offset rep (sq_ll sq) (sq_ov sq)) as [[o r]|]; [|reflexivity].
  set (out' := out ++ firstn (Z.to_nat (sq_ll sq)) lits).
  assert (Hw': wsize < Zlength out') by (unfold out'; rewrite Zlength_app; pose proof (Zlength_nonneg (firstn (Z.to_nat (sq_ll sq)) lits)); lia).

  pose proof (Zlength_nonneg hist).
  destruct (Z.gtb_spec o (Zlength out')) as [Hgt|Hle].
  - destruct (o >? Zlength hist + Zlength out'); [reflexivity|].
    replace (o >? wsize) with true by (symmetry; apply Z.gtb_lt; lia).
    replace (Zlength out' + sq_ml sq <=? wsize) with false by (symmetry; apply Z.leb_gt; lia).
    rewrite Bool.andb_false_r. reflexivity.
  - replace (o >? Zlength hist + Zlength out') with false by (symmetry; apply Zgtb_le; lia).
    destruct (_ && _); [reflexivity|].
    rewrite (lz_copy_nil _ hist out' o) by lia. apply IH.
    destruct (lz_copy_grow (Z.to_nat (sq_ml sq)) nil out' o) as [d ->]. rewrite Zlength_app.
    pose proof (Zlength_nonneg d). lia.
Qed.

Lemma decode_block_w_wrap : forall st hist out b bsm wsize, wsize < Zlength out ->
  decode_block_w st hist out b bsm wsize = decode_block_w st nil out b bsm wsize.
Proof.
  intros st hist out b bsm wsize Hw. unfold decode_block_w.
  destruct (Zlength b >? bsm); [reflexivity|].
  destruct (decode_literals (st_huf st) b bsm) as [[[lits lused] huf]|]; [|reflexivity].
  destruct (decode_seq_header _ _) as [[[nbSeq tabs] hused]|]; [|reflexivity].
  match goal with |- match ?e with _ => _ end = _ => destruct e as [seqs|] eqn:ES end; [|reflexivity].
  assert (HF: Forall (fun sq => 0 <= sq_ml sq) seqs).
  { destruct (nbSeq =? 0); [inversion ES; constructor|].
    destruct tabs as [[[tLL tOF] tML]|]; [|discriminate]. eapply pw_decode_seq_stream_ml; exact ES. }
  rewrite (exec_seqs_w_wrap wsize hist seqs HF) by exact Hw. reflexivity.
Qed.

(* where the stream's decoder (behind the dictionary) decodes a block, B's lenient one behind H agrees *)
Lemma dec_hist : forall dw ts hist H out u bsm ws x,
  (H = hist \/ (H = nil /\ dw = true /\ ws < Zlength out)) ->
  dec_block dw ts hist out u bsm ws = Some x -> decode_block ts H out u bsm ws = Some x.
Proof.
  intros dw ts hist H out u bsm ws x [->|[-> [-> Hw]]] D; [eapply dec_block_lenient; eauto|].
  unfold dec_block in D. rewrite decode_block_w_wrap in D by exact Hw.
  rewrite pw_decode_block_nodict in D. exact D.
Qed.

Lemma zhist_dec : forall sm z H u x, zhist_ok sm z H ->
  dec_block (md_dwin (sm_md sm)) (zp_ts z) (zp_hist z) (zp_out z) u (zp_bsm z) (fh_windowSize (zp_h z)) = Some x ->
  decode_block (zp_ts z) H (zp_out z) u (zp_bsm z) (fh_windowSize (zp_h z)) = Some x.
Proof. intros sm z H u x Hz D. eapply dec_hist; [|exact D]. exact Hz. Qed.
