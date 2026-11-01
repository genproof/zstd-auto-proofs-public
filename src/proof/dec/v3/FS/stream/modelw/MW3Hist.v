(* FS3 streaming model facts, R1: the history H zstd's block decoder gets (zhist_ok: the frame's
   dictionary content, or nil once the frame's output exceeds the window) against the stream's own model
   (dec_block dw behind the dictionary): where the model decodes a block, B's lenient decode_block behind H
   gives the same.  Once the output exceeds the window the dictionary window rule forbids every reference to
   the dictionary, so the strict decoder behind the dictionary is the strict (= lenient) one behind nil. *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Block Zstd.proof.model.Xxh64 Zstd.proof.model.Info Zstd.proof.model.Series Zstd.proof.model.StreamModel Zstd.proof.model.Params Zstd.proof.model.ParamsH Zstd.proof.model.ParamsW.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Require Import Zstd.proof.dec.v3.FS.stream.S3ModelStmts Zstd.proof.dec.v3.FS.stream.modelw.MW3Base Zstd.proof.dec.v3.FS.stream.modelw.MW3Frame Zstd.proof.dec.v3.FS.stream.modelw.MW3Unit1 Zstd.proof.dec.v3.FS.stream.modelw.MW3Unit2.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

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

Lemma cnt_ok_w : forall sm z H u cnt ts', zhist_ok sm z H ->
  cnt_ok z H u cnt ts' -> cnt_okw (md_dwin (sm_md sm)) z u cnt ts'.
Proof.
  intros sm z H u cnt ts' Hz C. unfold cnt_ok, cnt_okw in *.
  destruct (zp_ph z); auto. cbv zeta in *.
  destruct (bp_type _ =? 0); auto. destruct (bp_type _ =? 1); auto.
  destruct C as [C1 [C2 C3]]. split; [exact C1|]. split; [exact C2|].
  destruct (dec_block _ _ _ _ _ _ _) as [[ts2 c2]|] eqn:D; [|exact I].
  rewrite (zhist_dec _ _ _ _ _ Hz D) in C3. exact C3.
Qed.

Lemma cont_err_w : forall sm hdr z H u cap, zhist_ok sm z H ->
  cont_err (FP_zstd hdr z) H u cap -> cont_errw (md_dwin (sm_md sm)) (FP_zstd hdr z) u cap.
Proof.
  intros sm hdr z H u cap Hz C. unfold cont_err, cont_errw in *. cbv zeta in *.
  destruct (zp_ph z); auto.
  destruct (bp_type _ =? 0); auto. destruct (bp_type _ =? 1); auto.
  destruct (dec_block _ _ _ _ _ _ _) as [[ts2 c2]|] eqn:D; [|exact I].
  rewrite (zhist_dec _ _ _ _ _ Hz D) in C. exact C.
Qed.
