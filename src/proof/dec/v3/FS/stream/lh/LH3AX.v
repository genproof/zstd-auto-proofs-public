(* ZSTD_decompressStream, case zdss_loadHeader with the exact claim: piece A (getFrameHeader_advanced, the selection,
   the error and need-more branches: hint and error returns, or the header-load break), its returns with the model's
   outcome (LH3XDefs.lh_xok).  The relational proof (LH3A.lhA_ok) is reused case by case: its returns on an invalid
   or incomplete header are an error of the model's st_load_header too, or the hint; the case of a complete header
   never returns. *)
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3XDefs.
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3A2_tl Zstd.proof.dec.v3.FS.stream.lh.LH3A2_t1 Zstd.proof.dec.v3.FS.stream.lh.LH3A2_t2 Zstd.proof.dec.v3.FS.stream.lh.LH3A2_t3 Zstd.proof.dec.v3.FS.stream.lh.LH3A2_t4 Zstd.proof.dec.v3.FS.stream.lh.LH3A2_t5.
Require Zstd.proof.model.ParamsH.
Local Open Scope logic.

Section CM_LH3AX_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.

(* from the configuration of a new context the format is zstd1 (no magicless frames) *)
Lemma lhx_mg (a: dsa) (w: lw) (hb: list Z) : lh_entry a w hb -> fresh_cfg (a_st a) -> lh_mg (w_k w) = false.
Proof.
  intros He (_ & Hp & _). destruct He as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hbc & _).
  destruct Hbc as (_ & Hpar & _). unfold lh_mg. rewrite Hpar, Hp. reflexivity.
Qed.

Lemma lhx_slice (l: list Z) (i k: Z) : 0 <= i -> 0 <= k -> slice l i k = sublist i (i + k) l.
Proof. intros. unfold slice, sublist. rewrite firstn_skipn_comm, Z2Nat.inj_add by lia. reflexivity. Qed.

(* the input bytes of the call after the bytes consumed so far are the model's *)
Lemma lhx_rest (a: dsa) (w: lw) (hb: list Z) :
  dsa_ok a -> lh_entry a w hb ->
  slice (a_xin a) (w_ipc w - a_ipos a) (Zlength (a_xin a) - (w_ipc w - a_ipos a)) = sublist (w_ipc w) (a_isz a) (a_ibs a) /\
  Zlength (a_xin a) - (w_ipc w - a_ipos a) = a_isz a - w_ipc w.
Proof.
  intros Ha He.
  destruct Ha as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hipos & _ & Hibs & _).
  destruct He as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hipc & _).
  unfold a_xin. rewrite Zlength_sublist by lia.
  split; [| lia].
  rewrite lhx_slice by lia. rewrite sublist_sublist by (rewrite ?Zlength_sublist; lia).
  f_equal; lia.
Qed.

(* every return of piece A on a header that is not complete is an error of the model's call, or the hint *)
Lemma lhA_xok_nonok (a: dsa) (w: lw) (hb: list Z) (r ipos': Z) (w': lw) :
  dsa_ok a -> lh_entry a w hb -> lh_rc a w hb r ipos' w' ->
  (forall h, get_frame_header_m (lh_mg (w_k w)) hb <> FH_ok h) ->
  lh_xok a w hb r ipos' w'.
Proof.
  intros Ha He Hrc Hnok Hx. inversion Hrc; subst; try (exfalso; eapply Hnok; eassumption).
  - (* the header is invalid: st_load_header fails *)
    left. apply ex_err_of_loop. intro Hf.
    destruct (lhx_view a w hb He Hx Hf) as (z0 & zi & f & Hl & _ & _ & Hhb & Hit).
    exists z0, zi, f, (w_ipc w - a_ipos a), nil. split; [exact Hl |].
    pose proof (lhx_mg a w hb He Hf) as Hmg.
    match goal with Hg: get_frame_header_m _ hb = FH_err |- _ =>
      rewrite Hmg, ParamsH.get_frame_header_zstd1 in Hg; rename Hg into Eg end.
    rewrite Hit. unfold ExStream.st_load_header. rewrite Hhb, Eg. reflexivity.
  - (* the input ends inside the header and the bytes are invalid *)
    left. apply ex_err_of_loop. intro Hf.
    destruct (lhx_view a w hb He Hx Hf) as (z0 & zi & f & Hl & _ & _ & Hhb & Hit).
    exists z0, zi, f, (w_ipc w - a_ipos a), nil. split; [exact Hl |].
    destruct (lhx_rest a w hb Ha He) as (Es & El).
    pose proof (lhx_mg a w hb He Hf) as Hmg.
    match goal with Hg: get_frame_header_m _ hb = FH_more _ |- _ =>
      rewrite Hmg, ParamsH.get_frame_header_zstd1 in Hg; rename Hg into Eg end.
    match goal with Hg: get_frame_header_m _ (hb ++ _) = FH_err |- _ =>
      rewrite Hmg, ParamsH.get_frame_header_zstd1 in Hg; rename Hg into Eg2 end.
    rewrite Hit. unfold ExStream.st_load_header. rewrite Hhb, Eg.
    rewrite Es, El. rewrite (proj2 (Z.gtb_lt _ _)) by lia. rewrite Eg2. reflexivity.
  - (* the hint *)
    right. unfold lh_rc_hint. exists kk, v, tbl, d1, did1, r', v'.
    do 8 (split; [first [eassumption | reflexivity] |]). reflexivity.
Qed.

(* a statement with the relational post of piece A has the exact one when its returns are lh_xok *)
Lemma lhA_post_xw : forall (Espec: OracleKind) Delta DENT TABS (a: dsa) (w: lw) (hb: list Z) P c,
  (forall r ipos' w', lh_rc a w hb r ipos' w' -> lh_xok a w hb r ipos' w') ->
  semax Delta P c (lhA_post DENT TABS a w hb) -> semax Delta P c (lhA_post_x DENT TABS a w hb).
Proof.
  intros Espec Delta DENT TABS a w hb P c Hok H.
  eapply semax_post; [ | | | | exact H].
  - apply andp_left2. apply derives_refl.
  - apply andp_left2. apply derives_refl.
  - apply andp_left2. apply derives_refl.
  - intro vl. apply andp_left2. cbv beta iota delta [lhA_post lhA_post_x RA_return lh_ret lh_ret_x].
    Intros r ipos' w'. Exists r ipos' w'.
    unfold PROPx. apply andp_derives; [| apply derives_refl].
    apply prop_derives; simpl; intros (Hv & Hr & Hrc & _). pose proof (Hok _ _ _ Hrc). tauto.
Qed.

(* the case of a complete header (LH3A2_t1.lhA_t_ok with the exact post): the normal exit, never a return *)
Lemma lhA_t_ok_x : forall (Espec: OracleKind) DENT TABS BR (a: dsa) (w: lw) (hb: list Z) r v tbl d1 did1 h,
  DENT_OK DENT -> TABS_OK TABS -> dsa_ok a -> lh_entry a w hb ->
  lhA_sel (w_k w) hb r v tbl d1 did1 -> get_frame_header_m (lh_mg (w_k w)) hb = FH_ok h ->
  semax (ds_Delta DENT TABS BR) (lhA_mid DENT TABS a w r v tbl d1 did1) lhA_t (lhA_post_x DENT TABS a w hb).
Proof.
intros Espec DENT TABS BR a w hb r v tbl d1 did1 h HD HT Ha He Hsel Eg.
assert (Hsel' := Hsel). destruct Hsel' as (Hr & Hpost & _).
unfold fh_post_m in Hpost. rewrite Eg in Hpost. destruct Hpost as [-> ->].
a3_open.
forward_call 0.
rewrite (a3_small_noerr 0) by lia.
match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
  forward_if (PROPx P (LOCALx Q (SEPx R))) end.
{ a3_absurd. }
{ forward. apply ENTAIL_refl. }
forward_if.
{ a3_absurd. }
forward.
cbv beta iota delta [overridePost lhA_post_x lhA_post RA_normal].
Exists h tbl d1 did1.
unfold ds_LI_St, ds_LI_L. rewrite ctxA_split. a3_rw.
entailer!.
Qed.

(* piece A: the relational case split of LH3A.lhA_ok, the returns weakened to lh_ret_x *)
Lemma lhA_x_ok : lhA_x_stmt.
Proof.
intros Hlend Hfherr Espec DENT TABS BR a w hb HD HT Ha He Hsp Hx.
apply lhA_split with (Q := lhA_midx DENT TABS a w hb).
{ apply lhA_pre_ok; auto. }
unfold lhA_midx.
apply semax_extract_exists; intro r. apply semax_extract_exists; intro v.
apply semax_extract_exists; intro tbl. apply semax_extract_exists; intro d1.
apply semax_extract_exists; intro did1.
apply semax_extract_prop; intro Hsel.
assert (Hfpv: fp_ok v).
{ pose proof Hsel as (_ & Hp & _). pose proof He as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hbc & _).
  destruct Hbc as (_ & _ & _ & _ & _ & Hfp0 & _). exact (a3_fp_id _ _ _ _ _ Hfherr Hp Hfp0). }
destruct (get_frame_header_m (lh_mg (w_k w)) hb) as [|kk|h] eqn:Eg.
2: destruct (Z_lt_ge_dec (a_isz a - w_ipc w) (kk - Zlength hb)) as [Hlt|Hge].
1-3: apply lhA_post_xw; [intros r0 ip0 w0 Hrc; apply lhA_xok_nonok; auto; intros h' E; congruence |].
- eapply lhA_t_err; eauto.
- destruct (get_frame_header_m (lh_mg (w_k w)) (hb ++ sublist (w_ipc w) (a_isz a) (a_ibs a))) eqn:E2.
  + eapply lhA_t_more_err; eauto.
  + destruct (andb (negb (lh_mg (w_k w))) (orb (Zlength (hb ++ sublist (w_ipc w) (a_isz a) (a_ibs a)) <? 4)
      (is_skippable_frame (hb ++ sublist (w_ipc w) (a_isz a) (a_ibs a)) =? 1))) eqn:Eb.
    * eapply lhA_t_hint1; eauto; congruence.
    * eapply lhA_t_hint2; eauto; congruence.
  + destruct (andb (negb (lh_mg (w_k w))) (orb (Zlength (hb ++ sublist (w_ipc w) (a_isz a) (a_ibs a)) <? 4)
      (is_skippable_frame (hb ++ sublist (w_ipc w) (a_isz a) (a_ibs a)) =? 1))) eqn:Eb.
    * eapply lhA_t_hint1; eauto; congruence.
    * eapply lhA_t_hint2; eauto; congruence.
- eapply lhA_t_brk; eauto; lia.
- eapply lhA_t_ok_x; eauto.
Qed.

End CM_LH3AX_1.
