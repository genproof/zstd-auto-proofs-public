(* FS3 streaming: the model facts behind the progress claim of ZSTD_decompressStream (Spec_api6.stream_progress,
   model/StreamProgress.v), plain Coq: a series the model decodes with a window limit is decoded the same way
   without it; a frame in progress whose remaining bytes are not read yet keeps the bytes read from being a
   complete series; at a frame boundary the bytes read are a complete series whose content was delivered; the
   output a stream holds back is a prefix of the content of every series it can still become. *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Block Zstd.proof.model.Series Zstd.proof.model.StreamModel Zstd.proof.model.Params.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Require Import Zstd.proof.dec.v3.FS.stream.S3ModelDefs Zstd.proof.dec.v3.FS.stream.epi.E3Rem.
Require Import Zstd.proof.dec.v3.FS.stream.epi.content.EC3Base Zstd.proof.dec.v3.FS.stream.epi.content.EC3Frame Zstd.proof.dec.v3.FS.stream.epi.content.EC3FrameM Zstd.proof.dec.v3.FS.stream.epi.content.EC3Walk.
Require Import Zstd.proof.dec.v3.FS.stream.epi.E3Content Zstd.proof.dec.v3.FS.stream.epi.E3Hint.
Require Import Zstd.proof.dec.v3.FS.stream.epi.zero.EZ3Series.
Require Import Zstd.proof.model.StreamProgress Zstd.proof.dec.v3.FS.stream.S3Main.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

Section CM_E3Prog_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* ---------- the window limit ---------- *)

(* the first frame the model decodes with a window limit w is decoded the same way without one (byte input:
   every Window_Size is at most no_wlim) *)
Lemma ep_wfirst_nowlim : forall md sel cur w s x, bytes_ok s ->
  wfirst md sel cur w s = inl x -> wfirst md sel cur no_wlim s = inl x.
Proof.
  intros md sel cur w s x Hb H. unfold wfirst in *.
  destruct (Zlength s <? starting_len (md_magicless md)); [discriminate|].
  destruct (negb (md_magicless md) && _); [exact H|].
  destruct (frame_dict _ _ _ _) as [d|]; [|discriminate].
  destruct (decode_frame_m md d w s) as [c k| | |] eqn:E; try discriminate.
  destruct (dfm_wshape md d w s c k E) as [h [G Hw]].
  rewrite (Hw no_wlim).
  replace (fh_windowSize h >? no_wlim) with false
    by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; exact (gfhm_ws _ _ _ G Hb)).
  exact H.
Qed.

Lemma ep_walk_nowlim : forall md sel f cur w s off l, bytes_ok s ->
  walk_m f md sel cur w s off = (l, TEnd) -> walk_m f md sel cur no_wlim s off = (l, TEnd).
Proof.
  intros md sel. induction f; intros cur w s off l Hb H; [discriminate|].
  rewrite walk_S in *.
  destruct (wfirst md sel cur w s) as [[[[k c] sk] cur']|t] eqn:E.
  - rewrite (ep_wfirst_nowlim md sel cur w s _ Hb E).
    destruct (walk_m f md sel cur' w (skipn (Z.to_nat k) s) (off + k)) as [l0 t0] eqn:E2.
    inversion H; subst.
    rewrite (IHf cur' w _ _ _ (bytes_ok_skipn _ _ Hb) E2). reflexivity.
  - inversion H; subst. apply wfirst_end in E. subst s.
    unfold wfirst.
    replace (Zlength (@nil Z) <? starting_len (md_magicless md)) with true
      by (symmetry; apply Z.ltb_lt; pose proof (starting_len_pos (md_magicless md));
          change (Zlength (@nil Z)) with 0; lia).
    reflexivity.
Qed.

Lemma ep_series_nowlim : forall md sel cur w s l, bytes_ok s ->
  series_frames_m md sel cur w s = (l, TEnd) -> series_frames_m md sel cur no_wlim s = (l, TEnd).
Proof. intros. unfold series_frames_m in *. eapply ep_walk_nowlim; eauto. Qed.

(* ---------- the end of the current frame ---------- *)

Lemma ep_cur_end_le : forall fl ipos got cacc dflt,
  (forall f, In f fl -> fr_end f <= dflt) -> ipos <= dflt -> cur_end_aux fl ipos got cacc dflt <= dflt.
Proof.
  induction fl as [|f fl IH]; intros ipos got cacc dflt Hf Hd; simpl; [lia|].
  destruct (_ || _)%bool.
  - apply Hf. left. reflexivity.
  - apply IH; auto. intros g Hg. apply Hf. right. exact Hg.
Qed.

(* a frame in progress with bytes still to come (fp_rem > 0): the bytes read are not a series the model decodes *)
Lemma ep_incomplete : forall sm sin sout fp pend cd, bytes_ok sin ->
  m_rel_cd sm sin sout fp pend cd -> 0 < fp_rem fp ->
  snd (series_frames_m (sm_md sm) (sm_sel sm) (sm_cur sm) no_wlim sin) <> TEnd.
Proof.
  intros sm sin sout fp pend cd Hb Hm Hr Ht.
  assert (Hp: is_prefix sin sin) by (pose proof (is_prefix_app sin nil) as P; rewrite app_nil_r in P; exact P).
  pose proof (epi3_hint sm sin sout fp pend cd Hb Hm sin Hp Hb (or_introl Ht)) as H.
  destruct (series_frames_m (sm_md sm) (sm_sel sm) (sm_cur sm) no_wlim sin) as [l t] eqn:E.
  cbn [fst snd] in *. subst t.
  assert (Hle: cur_end l (Zlength sin) (Zlength sout) (Zlength sin) <= Zlength sin).
  { unfold cur_end. apply ep_cur_end_le; [|lia].
    intros f Hf. unfold series_frames_m in E.
    pose proof (eh3_walk_ends _ _ _ _ _ _ _ _ _ E ltac:(discriminate) Hb f Hf). lia. }
  lia.
Qed.

(* ---------- the three situations of a call without progress ---------- *)

(* the stream's model relation, or no claim *)
Definition ep_alive (sm: smode) (sin sout: list Z) (fp: fprog) (pend: list Z) : Prop :=
  dead sm sin \/ exists cd, m_rel_cd sm sin sout fp pend cd.

Lemma ep_dead_end : forall sm sin s, dead sm sin -> is_prefix sin s -> bytes_ok s ->
  snd (series_frames_m (sm_md sm) (sm_sel sm) (sm_cur sm) (sm_wl sm) s) <> TEnd.
Proof.
  intros sm sin s Hd Hp Hb Ht.
  destruct (series_frames_m (sm_md sm) (sm_sel sm) (sm_cur sm) (sm_wl sm) s) as [l t] eqn:E.
  cbn [snd] in Ht. subst t.
  pose proof (proj1 Hd s Hp) as Hu. rewrite (ep_series_nowlim _ _ _ _ _ _ Hb E) in Hu. discriminate.
Qed.

(* a frame in progress with bytes still to come: the bytes read are not a series the model decodes *)
Lemma ep_incomplete_wl : forall sm sin sout fp pend, bytes_ok sin -> ep_alive sm sin sout fp pend ->
  0 < fp_rem fp -> snd (series_frames_m (sm_md sm) (sm_sel sm) (sm_cur sm) (sm_wl sm) sin) <> TEnd.
Proof.
  intros sm sin sout fp pend Hb [Hd|[cd Hm]] Hr Ht.
  - assert (Hp: is_prefix sin sin) by (pose proof (is_prefix_app sin nil) as P; rewrite app_nil_r in P; exact P).
    exact (ep_dead_end sm sin sin Hd Hp Hb Ht).
  - destruct (series_frames_m (sm_md sm) (sm_sel sm) (sm_cur sm) (sm_wl sm) sin) as [l t] eqn:E.
    cbn [snd] in Ht. subst t.
    apply (ep_incomplete sm sin sout fp pend cd Hb Hm Hr).
    rewrite (ep_series_nowlim _ _ _ _ _ _ Hb E). reflexivity.
Qed.

(* output held back (pend <> nil): every series the bytes read can still become has more content than was
   delivered *)
Lemma ep_pending_wl : forall sm sin sout fp pend, bytes_ok sin -> ep_alive sm sin sout fp pend ->
  pend <> nil -> forall s, bytes_ok s -> is_prefix sin s ->
  snd (series_frames_m (sm_md sm) (sm_sel sm) (sm_cur sm) (sm_wl sm) s) = TEnd ->
  Zlength sout < Zlength (flat_map fr_content (fst (series_frames_m (sm_md sm) (sm_sel sm) (sm_cur sm) (sm_wl sm) s))).
Proof.
  intros sm sin sout fp pend Hb [Hd|[cd Hm]] Hpn s Hbs Hp Ht.
  { exfalso. exact (ep_dead_end sm sin s Hd Hp Hbs Ht). }
  destruct (series_frames_m (sm_md sm) (sm_sel sm) (sm_cur sm) (sm_wl sm) s) as [l t] eqn:E.
  cbn [fst snd] in *. subst t.
  pose proof (ep_series_nowlim _ _ _ _ _ _ Hbs E) as E0.
  assert (Hm': m_rel_cd sm sin (sout ++ pend) fp nil cd).
  { destruct Hm as (dsin & fb & recs & H1 & H2 & H3 & H4 & H5).
    exists dsin, fb, recs. rewrite app_nil_r. auto. }
  pose proof (epi3_content sm sin (sout ++ pend) fp nil cd Hb Hm' s Hp) as Hc.
  cbv zeta in Hc. rewrite E0 in Hc. cbn [fst snd] in Hc.
  specialize (Hc (or_introl eq_refl)).
  apply is_prefix_ex in Hc. destruct Hc as [r Hr]. rewrite Hr, !Zlength_app.
  destruct pend as [|x pend]; [congruence|]. rewrite Zlength_cons.
  pose proof (Zlength_nonneg pend). pose proof (Zlength_nonneg r). lia.
Qed.

(* at a frame boundary (nothing held back), the bytes read are a series the model decodes, and its content was
   delivered *)
Lemma ep_boundary_wl : forall sm sin sout fp, bytes_ok sin -> ep_alive sm sin sout fp nil ->
  (fp_complete fp = true \/ fp = FP_none \/ fp = FP_hdr nil) ->
  snd (series_frames_m (sm_md sm) (sm_sel sm) (sm_cur sm) (sm_wl sm) sin) = TEnd ->
  Zlength (flat_map fr_content (fst (series_frames_m (sm_md sm) (sm_sel sm) (sm_cur sm) (sm_wl sm) sin))) <= Zlength sout.
Proof.
  intros sm sin sout fp Hb [Hd|[cd Hm]] Hfp Ht.
  { exfalso. assert (Hp: is_prefix sin sin) by (pose proof (is_prefix_app sin nil) as P; rewrite app_nil_r in P; exact P).
    exact (ep_dead_end sm sin sin Hd Hp Hb Ht). }
  destruct (series_frames_m (sm_md sm) (sm_sel sm) (sm_cur sm) (sm_wl sm) sin) as [l t] eqn:E.
  cbn [fst snd] in *. subst t.
  pose proof (ep_series_nowlim _ _ _ _ _ _ Hb E) as E0.
  assert (Hr: exists recs', series_frames_m (sm_md sm) (sm_sel sm) (sm_cur sm) no_wlim sin = (recs', TEnd) /\
                            sout = flat_map fr_content recs').
  { destruct Hm as (dsin & fb & recs & -> & Hser & Hcur & Hcr & Hout).
    rewrite app_nil_r in Hout. apply bytes_ok_app in Hb. destruct Hb as [Hb1 Hb2].
    destruct Hfp as [Hc|[->| ->]].
    - destruct (m3_frames_done_app sm cd dsin recs fb fp Hb1 Hb2 Hser Hcur Hcr Hc) as [recs' [E1 [E2 _]]].
      exists recs'. split; [exact E1|]. rewrite Hout, E2. reflexivity.
    - cbn [cur_rel] in Hcr. subst fb. rewrite app_nil_r. exists recs. split; [exact Hser|].
      rewrite Hout. cbn [fp_content]. rewrite app_nil_r. reflexivity.
    - cbn [cur_rel] in Hcr. destruct Hcr as [-> _]. rewrite app_nil_r. exists recs. split; [exact Hser|].
      rewrite Hout. cbn [fp_content]. rewrite app_nil_r. reflexivity. }
  destruct Hr as [recs' [E1 ->]]. rewrite E0 in E1. inversion E1. lia.
Qed.

(* a header still being loaded (zdss_loadHeader: more bytes needed) is not a frame the model decodes *)
Lemma ep_hdr_more_wfirst : forall md sel cd hb kk, bytes_ok hb ->
  get_frame_header_m (md_magicless md) hb = FH_more kk -> hb <> nil ->
  match wfirst md sel cd no_wlim hb with inl _ => False | inr t => t <> TEnd end.
Proof.
  intros md sel cd hb kk Hb G Hne. unfold wfirst.
  destruct (Zlength hb <? starting_len (md_magicless md)) eqn:E1.
  { destruct hb as [|x hb]; [congruence|]. rewrite Zlength_cons.
    replace (Z.succ (Zlength hb) =? 0) with false by (symmetry; apply Z.eqb_neq; pose proof (Zlength_nonneg hb); lia).
    discriminate. }
  destruct (negb (md_magicless md) && is_skippable_magic (le_field hb 0 4)) eqn:E2.
  - apply andb_prop in E2. destruct E2 as [Hmg Hsk]. apply Bool.negb_true_iff in Hmg.
    rewrite Hmg in G. cbn [get_frame_header_m negb] in G.
    unfold skippable_frame_size.
    destruct (Zlength hb <? ZSTD_SKIPPABLEHEADERSIZE) eqn:E3; [discriminate|].
    exfalso. unfold get_frame_header in G.
    apply Z.ltb_ge in E3. unfold ZSTD_SKIPPABLEHEADERSIZE in E3.
    replace (Zlength hb <? 5) with false in G by (symmetry; apply Z.ltb_ge; lia).
    rewrite (skip_not_magic _ Hsk), Hsk in G. cbn [negb] in G.
    replace (Zlength hb <? ZSTD_SKIPPABLEHEADERSIZE) with false in G
      by (symmetry; apply Z.ltb_ge; unfold ZSTD_SKIPPABLEHEADERSIZE; lia).
    discriminate.
  - destruct (frame_dict (md_magicless md) sel cd hb) as [d|]; [|discriminate].
    destruct (decode_frame_m md d no_wlim hb) as [c k| | |] eqn:E; try discriminate.
    exfalso. destruct (dfm_hdr_inv md d no_wlim hb) as [h [G' _]]; congruence.
Qed.

Lemma ep_hdr_incomplete_wl : forall sm sin sout hb pend kk, bytes_ok sin ->
  ep_alive sm sin sout (FP_hdr hb) pend ->
  get_frame_header_m (md_magicless (sm_md sm)) hb = FH_more kk -> hb <> nil ->
  snd (series_frames_m (sm_md sm) (sm_sel sm) (sm_cur sm) (sm_wl sm) sin) <> TEnd.
Proof.
  intros sm sin sout hb pend kk Hb [Hd|[cd Hm]] G Hne Ht.
  { assert (Hp: is_prefix sin sin) by (pose proof (is_prefix_app sin nil) as P; rewrite app_nil_r in P; exact P).
    exact (ep_dead_end sm sin sin Hd Hp Hb Ht). }
  destruct (series_frames_m (sm_md sm) (sm_sel sm) (sm_cur sm) (sm_wl sm) sin) as [l t] eqn:E.
  cbn [snd] in Ht. subst t.
  pose proof (ep_series_nowlim _ _ _ _ _ _ Hb E) as E0.
  destruct Hm as (dsin & fb & recs & -> & Hser & Hcur & Hcr & _).
  cbn [cur_rel] in Hcr. destruct Hcr as [-> _].
  apply bytes_ok_app in Hb. destruct Hb as [Hb1 Hb2].
  destruct (series_app _ _ _ _ _ _ hb Hser Hb1) as [Hs _].
  rewrite E0, Hcur in Hs. cbn [snd] in Hs.
  pose proof (ep_hdr_more_wfirst (sm_md sm) (sm_sel sm) cd hb kk Hb2 G Hne) as Hw.
  unfold series_frames_m in Hs. rewrite walk_S in Hs.
  destruct (wfirst (sm_md sm) (sm_sel sm) cd no_wlim hb) as [x|t]; [contradiction|].
  cbn [snd] in Hs. congruence.
Qed.

(* ---------- the claim on one call ---------- *)

(* model/StreamProgress.v's claim for the call a that returns r with in.pos' = ipos', out.pos' = opc, a' bytes read
   ahead and the stall count stall' (Spec_api6.stream_progress of the state after the call) *)
Definition ep_prog (a: dsa) (r ipos' opc a' stall': Z) : Prop :=
  let st := a_st a in let ss := dc_ss st in
  let sin' := ss_in ss ++ sublist (a_ipos a + ss_ahead ss) (ipos' + a') (a_ibs a) in
  stream_progress_m (sm_md (sm_of st)) (sm_sel (sm_of st)) (sm_cur (sm_of st)) (sm_wl (sm_of st))
    (ss_in ss) (ss_out ss) (sin' ++ sublist (ipos' + a') (a_isz a) (a_ibs a)) stall' r (a_ipos a) ipos' (a_isz a)
    (a_opos a) opc (a_osz a).

Lemma ep_prefix_eq : forall p s, is_prefix p s -> Zlength s <= Zlength p -> s = p.
Proof.
  intros p s H Hl. apply is_prefix_ex in H. destruct H as [r ->].
  rewrite Zlength_app in Hl. destruct r as [|x r]; [rewrite app_nil_r; reflexivity|].
  rewrite Zlength_cons in Hl. pose proof (Zlength_nonneg r). lia.
Qed.

Lemma ep_ahead_bytes : forall stable obuf sout k sv,
  c_core stable obuf sout k sv -> bytes_ok (sv_ahead sv).
Proof.
  intros stable obuf sout k sv (Hh & _).
  destruct Hh as [(_ & ->)|[(_ & ->)|(_ & _ & _ & _ & Hb & _)]]; auto; constructor.
Qed.

(* the claim from the situation of a call without progress: the output full with output held back; or all the
   input read, nothing of it beyond what the call read, and the current frame incomplete (bytes still to come,
   or a header still being loaded) or at its end with everything delivered *)
Lemma ep_prog_of : forall a k sv ipc opc oc dl r ipos' a' stall',
  let ss := dc_ss (a_st a) in
  let sin := a_sin a ++ sublist (a_ipos a) ipc (a_ibs a) ++ sv_ahead sv in
  dsa_ok a -> call_inv a k sv ipc opc oc dl ->
  ss_in ss ++ sublist (a_ipos a + ss_ahead ss) (ipos' + a') (a_ibs a) = sin ->
  (is_error_code r = false -> ipos' = a_ipos a -> opc = a_opos a ->
     (r = 0 -> a_ipos a = a_isz a \/ stall' = 0) /\
     (r <> 0 ->
        (opc = a_osz a /\ sv_pend sv <> nil) \/
        (a_ipos a = a_isz a /\ a_isz a <= ipos' + a' /\
         (0 < fp_rem (sv_fp sv) \/
          (exists hb kk, sv_fp sv = FP_hdr hb /\ hb <> nil /\
             get_frame_header_m (md_magicless (dmode_of (dc_par (a_st a)))) hb = FH_more kk) \/
          (sv_pend sv = nil /\ (fp_complete (sv_fp sv) = true \/ sv_fp sv = FP_none \/ sv_fp sv = FP_hdr nil) /\
           Zlength sin <= Zlength (ss_in ss)))))) ->
  ep_prog a r ipos' opc a' stall'.
Proof.
  intros a k sv ipc opc oc dl r ipos' a' stall' ss sin Ha CI Hsin H.
  pose proof CI as (Hip & Hop & Hloc & Hpre & Hdl & Hdlc & Hdlb & Hbc & Hbin & Hn1 & Hn2 & Hn3 &
    Hcore & Hdd & Hstout & Hahead & Hblk & Hmodel & _).
  pose proof Ha as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hopos & _ & _ & Hipos & _ & Hlibs & Hbibs & _).
  assert (Hbsin: bytes_ok sin).
  { unfold sin. apply Forall_app. split; [exact Hbin|]. apply Forall_app. split.
    - apply Forall_sublist. exact Hbibs.
    - eapply ep_ahead_bytes; eauto. }
  unfold ep_prog, stream_progress_m. fold ss. rewrite Hsin.
  intros Herr Hi Ho. destruct (H Herr Hi Ho) as [H0 H1].
  assert (Hdl0: dl = nil) by (destruct dl; [reflexivity|rewrite Zlength_cons in Hdl; pose proof (Zlength_nonneg dl); lia]).
  assert (Hal: ep_alive (sm_of (a_st a)) sin (ss_out ss) (sv_fp sv) (sv_pend sv)).
  { destruct Hmodel as [Hd|(cd & Hm & _)]; [left; exact Hd|right; exists cd].
    rewrite Hdl0, app_nil_r in Hm. exact Hm. }
  split; [exact H0|]. intros Hr. destruct (H1 Hr) as [(Hoo & Hpn)|(Hii & Hle & Hc)].
  - split; [right; lia|]. intros s Hbs Hps Ht. left. split; [lia|].
    exact (ep_pending_wl _ _ _ _ _ Hbsin Hal Hpn s Hbs (is_prefix_app_l _ _ _ Hps) Ht).
  - split; [left; lia|]. intros s Hbs Hps Ht. right. split; [lia|].
    rewrite (sublist_nil_gen (a_ibs a) (ipos' + a') (a_isz a)) in Hps |- * by lia.
    rewrite app_nil_r in Hps |- *.
    destruct (Z.lt_ge_cases (Zlength sin) (Zlength s)) as [Hlt|Hge]; [left; exact Hlt|right].
    pose proof (ep_prefix_eq _ _ Hps Hge) as ->.
    destruct Hc as [Hrem|[(hb & kk & Hfp & Hne & G)|(Hpn & Hfp & Hlen)]].
    + exfalso. exact (ep_incomplete_wl _ _ _ _ _ Hbsin Hal Hrem Ht).
    + exfalso. rewrite Hfp in Hal.
      exact (ep_hdr_incomplete_wl _ _ _ _ _ kk Hbsin Hal G Hne Ht).
    + split; [exact Hlen|]. rewrite Hpn in Hal.
      exact (ep_boundary_wl _ _ _ _ Hbsin Hal Hfp Ht).
Qed.

(* the claim on the state st' after the call (Spec_api6.stream_progress (a_st a) st' ...) *)
Definition ep_prog_st (a: dsa) (st': dctx_st) (r ipos' opc: Z) : Prop :=
  let st := a_st a in let ss := dc_ss st in let ss' := dc_ss st' in
  stream_progress_m (sm_md (sm_of st)) (sm_sel (sm_of st)) (sm_cur (sm_of st)) (sm_wl (sm_of st))
    (ss_in ss) (ss_out ss) (ss_in ss' ++ sublist (ipos' + ss_ahead ss') (a_isz a) (a_ibs a)) (ss_stall ss') r
    (a_ipos a) ipos' (a_isz a) (a_opos a) opc (a_osz a).

(* a call that read input *)
Lemma ep_prog_moved : forall a r ipos' opc a' stall', ipos' <> a_ipos a -> ep_prog a r ipos' opc a' stall'.
Proof. intros. unfold ep_prog, stream_progress_m. intros _ E. contradiction. Qed.

Lemma ep_walk_nil : forall md sel cur w, series_frames_m md sel cur w [] = ([], TEnd).
Proof.
  intros. unfold series_frames_m. cbn [length]. rewrite walk_S. unfold wfirst.
  replace (Zlength (@nil Z) <? starting_len (md_magicless md)) with true
    by (symmetry; apply Z.ltb_lt; pose proof (starting_len_pos (md_magicless md));
        change (Zlength (@nil Z)) with 0; lia).
  reflexivity.
Qed.

(* the bytes of a complete frame are not empty *)
Lemma ep_complete_nonnil : forall sm sin sout fp pend, ep_alive sm sin sout fp pend ->
  fp_complete fp = true -> sin <> nil.
Proof.
  intros sm sin sout fp pend [Hd|[cd Hm]] Hc ->.
  - pose proof (proj1 Hd nil (is_prefix_app nil nil)) as Hu. rewrite ep_walk_nil in Hu. discriminate.
  - destruct Hm as (dsin & fb & recs & E & _ & _ & Hcr & _).
    symmetry in E. apply app_eq_nil in E. destruct E as [_ ->].
    destruct fp as [|hb|hdr got|hdr z]; cbn [fp_complete] in Hc; try discriminate; cbn [cur_rel] in Hcr.
    + destruct Hcr as (_ & Hl & Hcr).
      repeat match goal with H: _ /\ _ |- _ => destruct H end.
      match goal with H: exists sk, _ |- _ => destruct H as [sk [E _]] end.
      symmetry in E. apply app_eq_nil in E. destruct E as [-> _].
      unfold ZSTD_SKIPPABLEHEADERSIZE in Hl. rewrite Zlength_nil in Hl. lia.
    + destruct Hcr as (G & _ & _ & _ & _ & _ & _ & outc & last & _ & E & _).
      symmetry in E. apply app_eq_nil in E. destruct E as [-> _].
      pose proof (gfhm_len _ _ _ G) as L. pose proof (starting_len_pos (md_magicless (sm_md sm))).
      rewrite Zlength_nil in L. lia.
Qed.

End CM_E3Prog_1.
