(* FS3 streaming: the zero-return claim of ZSTD_decompressStream's epilogue (plain Coq; v2 template
   src/proof/dec/FS/StreamEpiZero.v). *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Block Zstd.proof.model.Series Zstd.proof.model.StreamModel Zstd.proof.model.Params.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Require Import Zstd.proof.dec.v3.FS.stream.S3ModelDefs Zstd.proof.model.Refuse.
Require Import Zstd.proof.dec.v3.FS.stream.S3ModelStmts Zstd.proof.dec.v3.FS.stream.epi.content.EC3Base Zstd.proof.dec.v3.FS.stream.epi.content.EC3Walk Zstd.proof.dec.v3.FS.stream.epi.zero.EZ3Series.
Import ListNotations.
Local Open Scope Z_scope.

Lemma ez3_walk_nil : forall md sel f cur w s off, walk_m f md sel cur w s off = (nil, TEnd) -> s = nil.
Proof.
  intros md sel [|f] cur w s off H; [discriminate|]. rewrite walk_S in H.
  destruct (wfirst md sel cur w s) as [[[[k c] sk] cur']|t] eqn:E.
  - destruct (walk_m f md sel cur' w _ _); discriminate.
  - inversion H; subst. eapply wfirst_end; eauto.
Qed.

Lemma ez3_walk_end : forall md sel f cur w s off l, walk_m f md sel cur w s off = (l, TEnd) -> bytes_ok s -> l <> nil ->
  fr_end (nth (length l - 1) l fr_dflt) = off + Zlength s.
Proof.
  intros md sel. induction f; intros cur w s off l H Hs Hl; [discriminate|].
  rewrite walk_S in H. destruct (wfirst md sel cur w s) as [[[[k c] sk] cur']|t] eqn:E.
  - destruct (walk_m f md sel cur' w (skipn (Z.to_nat k) s) (off + k)) as [l0 t0] eqn:E2.
    inversion H; subst; clear H.
    assert (Hk: Z.to_nat k <> 0%nat).
    { intro Hk. pose proof (walk_loop _ _ _ _ _ _ _ _ _ E Hk f (off + k)). rewrite Hk in E2. simpl in E2.
      rewrite E2 in H. discriminate. }
    destruct (wfirst_ext _ _ _ _ _ _ _ _ _ nil E Hs) as [Hkl _].
    destruct l0 as [|r l0].
    + apply ez3_walk_nil in E2. simpl. unfold fr_end, mkrec; simpl.
      pose proof (Zlength_skipn s k ltac:(lia)). rewrite E2 in H. simpl in H.
      rewrite Zlength_nil in H. lia.
    + specialize (IHf _ _ _ _ _ E2 (bytes_ok_skipn _ _ Hs) ltac:(discriminate)).
      rewrite Zlength_skipn in IHf by lia.
      replace (length (mkrec off k c sk :: r :: l0) - 1)%nat with (S (length (r :: l0) - 1)) by (simpl; lia).
      simpl nth. simpl in IHf |- *. rewrite Nat.sub_0_r in *. rewrite IHf. lia.
  - inversion H; subst. congruence.
Qed.

(* a stream that agrees with the model, at the end of a frame (or after finished frames only) with nothing
   pending: the bytes read are finished frames, at least one, whose content is the bytes delivered *)
Lemma ez3_read_frames : forall sm sin sout fp cd, bytes_ok sin ->
  m_rel_cd sm sin sout fp nil cd ->
  fp_complete fp = true \/ (fp = FP_none /\ sin <> nil) ->
  exists recs', series_frames_m (sm_md sm) (sm_sel sm) (sm_cur sm) no_wlim sin = (recs', TEnd) /\
    recs' <> nil /\ sout = flat_map fr_content recs'.
Proof.
  intros sm sin sout fp cd Hb Hm Hc.
  destruct Hm as [dsin [fb [recs [-> [Hser [Hcur [Hcr Hout]]]]]]].
  rewrite app_nil_r in Hout. apply bytes_ok_app in Hb. destruct Hb as [Hb1 Hb2].
  destruct Hc as [Hc|[-> Hne]].
  - destruct (m3_frames_done_app sm cd dsin recs fb fp Hb1 Hb2 Hser Hcur Hcr Hc) as [recs' [E1 [E2 [E3 _]]]].
    exists recs'. split; [exact E1|]. split; [intro; subst; discriminate|]. congruence.
  - simpl in Hcr. subst fb. rewrite app_nil_r in *. simpl in Hout. rewrite ?app_nil_r in Hout.
    exists recs. split; [auto|]. split; [|auto].
    intro; subst. apply Hne. eapply ez3_walk_nil. exact Hser.
Qed.

(* the frames of a series decoded to its end are the first frames of every extension *)
Lemma ez3_frames_app : forall md sel cur w dsin recs y, series_frames_m md sel cur w dsin = (recs, TEnd) ->
  bytes_ok dsin -> exists L, fst (series_frames_m md sel cur w (dsin ++ y)) = recs ++ L.
Proof.
  unfold series_frames_m. intros md sel cur w dsin recs y H Hb.
  pose proof (walk_len _ _ _ _ _ _ _ _ _ H ltac:(discriminate)) as HL.
  destruct (walk_app _ _ _ _ _ _ _ _ H Hb y (S (length (dsin ++ y)))) as [A1 _]; [rewrite length_app; lia|].
  rewrite A1. eexists; reflexivity.
Qed.

(* a stream that agrees with the model, at the end of a frame (or after finished frames only) with nothing
   pending: the bytes read end the n-th frame of every extension the model does not give up on, and the bytes
   delivered are the content of the first n frames (stream_claims_m's second clause) *)
Lemma epi3_zero : forall sm sin sout fp cd, bytes_ok sin ->
  m_rel_cd sm sin sout fp nil cd ->
  fp_complete fp = true \/ (fp = FP_none /\ sin <> nil) ->
  forall s, is_prefix sin s -> snd (series_frames_m (sm_md sm) (sm_sel sm) (sm_cur sm) no_wlim s) <> TUnk ->
  exists n, (1 <= n <= length (fst (series_frames_m (sm_md sm) (sm_sel sm) (sm_cur sm) no_wlim s)))%nat /\
    Zlength sin = fr_end (nth (n - 1) (fst (series_frames_m (sm_md sm) (sm_sel sm) (sm_cur sm) no_wlim s)) fr_dflt) /\
    sout = flat_map fr_content (firstn n (fst (series_frames_m (sm_md sm) (sm_sel sm) (sm_cur sm) no_wlim s))).
Proof.
  intros sm sin sout fp cd Hb Hm Hc s Hp Hs.
  destruct (ez3_read_frames _ _ _ _ _ Hb Hm Hc) as [recs' [Hser [Hne Hout]]].
  destruct (is_prefix_ex _ _ Hp) as [y ->].
  rewrite (proj1 (series_app _ _ _ _ _ _ _ Hser Hb)) in Hs.
  destruct (series_frames_m (sm_md sm) (sm_sel sm) (series_cur (sm_md sm) (sm_sel sm) (sm_cur sm) no_wlim sin) no_wlim y) as [l t] eqn:Ey.
  simpl in Hs.
  rewrite (series_app_full _ _ _ _ _ _ _ _ _ Hser Hb Ey Hs). simpl fst.
  exists (length recs'). destruct recs' as [|r0 rr]; [congruence|].
  split; [rewrite length_app; simpl; lia|]. split.
  - rewrite app_nth1 by (simpl; lia).
    unfold series_frames_m in Hser. rewrite (ez3_walk_end _ _ _ _ _ _ _ _ Hser Hb Hne). lia.
  - rewrite firstn_app, Nat.sub_diag, firstn_O, app_nil_r, firstn_all. auto.
Qed.

(* the zero-return claim on refused series (Refuse.stream_zero_ref): a stream that agrees with the model ends, at a
   return of 0, the frames it read, and these are the first frames of every extension (refused or not); a dead
   stream has no refused extension *)
Lemma epi3_zero_ref : forall sm sin sout fp pend r, bytes_ok sin ->
  dead sm sin \/ (exists cd, m_rel_cd sm sin sout fp pend cd) ->
  (r = 0 -> pend = nil /\ (fp_complete fp = true \/ (fp = FP_none /\ sin <> nil))) ->
  stream_zero_ref (sm_md sm) (sm_sel sm) (sm_cur sm) sin sout r.
Proof.
  intros sm sin sout fp pend r Hb Hst Hr s Hbs Hp Href Hr0.
  destruct Hst as [[_ Hn]|[cd Hm]]; [exfalso; exact (Hn s Hbs Hp Href)|].
  destruct (Hr Hr0) as [-> Hc]. cbv zeta.
  destruct (ez3_read_frames _ _ _ _ _ Hb Hm Hc) as [recs' [Hser [Hne Hout]]].
  destruct (is_prefix_ex _ _ Hp) as [y ->].
  destruct (ez3_frames_app _ _ _ _ _ _ y Hser Hb) as [L EL]. rewrite EL.
  exists (length recs'). destruct recs' as [|r0 rr]; [congruence|].
  split; [rewrite length_app; simpl; lia|]. split.
  - rewrite app_nth1 by (simpl; lia).
    unfold series_frames_m in Hser. rewrite (ez3_walk_end _ _ _ _ _ _ _ _ Hser Hb Hne). lia.
  - rewrite firstn_app, Nat.sub_diag, firstn_O, app_nil_r, firstn_all. auto.
Qed.
