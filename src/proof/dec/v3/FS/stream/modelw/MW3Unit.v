(* FS3 streaming model facts (revision R1): one unit of the current frame (skip_more, zunit_partial,
   zunit_step, zunit_err); B's history H is brought to the stream's model by MW3Hist (cnt_ok_w, cont_err_w). *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Block Zstd.proof.model.Xxh64 Zstd.proof.model.Info Zstd.proof.model.Series Zstd.proof.model.StreamModel Zstd.proof.model.Params Zstd.proof.model.ParamsH Zstd.proof.model.Huffman.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Require Import Zstd.proof.dec.v3.FS.stream.S3ModelStmts Zstd.proof.dec.v3.FS.stream.modelw.MW3Base Zstd.proof.dec.v3.FS.stream.modelw.MW3Frame Zstd.proof.dec.v3.FS.stream.modelw.MW3FrameM Zstd.proof.dec.v3.FS.stream.modelw.MW3Walk.
Require Import Zstd.proof.dec.v3.FS.stream.modelw.MW3Unit1 Zstd.proof.dec.v3.FS.stream.modelw.MW3Unit2 Zstd.proof.dec.v3.FS.stream.modelw.MW3Hist.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

Lemma skip_more3 : P_skip_more.
Proof.
  intros md sel cd fb hdr got u H Hle. simpl in *.
  destruct H as [Hmg [H8 [Hm [Hg [sk [-> Hsk]]]]]].
  pose proof (Zlength_nonneg u).
  repeat split; auto; try lia.
  exists (sk ++ u). split; [rewrite app_assoc; auto|rewrite Zlength_app; lia].
Qed.

Lemma zunit_partial3 : P_zunit_partial.
Proof.
  intros md sel cd fb hdr z g H Hg Hph. unfold cur_rel in *.
  destruct H as [G [Hl [Ht [Hfd [Hd [Hbsm [Hign [outc [last [Hbp [Hfb Hp]]]]]]]]]]].
  unfold zp_set_got, zp_with, zp_hist in *.
  cbn [zp_h zp_dm zp_bsm zp_ign zp_bl zp_ts zp_out zp_ph zp_got] in *.
  repeat split; auto. exists outc, last. split; auto.
  rewrite Hg in Hfb, Hp. subst fb.
  destruct (zp_ph z) as [|bh| |]; try contradiction.
  - destruct Hp as [-> [-> _]]. rewrite app_nil_r, <- ?app_assoc. repeat split; auto.
  - destruct Hph as [Hty [c' [Hc' Hlt]]]. destruct Hp as [-> [H3 [c [Hc [Hcb [_ Ho]]]]]].
    rewrite app_nil_r. rewrite <- !app_assoc. split; auto. split; auto. split; auto.
    exists c. rewrite Hc in Hc'. inversion Hc'; subst c'. repeat split; auto; try lia.
    rewrite Ho. destruct (bp_type (block_props_of bh) =? 0) eqn:E; auto.
    apply Z.eqb_eq in E. contradiction.
  - destruct Hp as [-> [-> [Hf [Hck _]]]]. rewrite app_nil_r, <- ?app_assoc. repeat split; auto.
Qed.

Lemma dm_ok_st : forall dm, dm_ok dm -> bytes_ok (dm_content dm) /\ st_ok (dm_state dm).
Proof.
  intros dm [H1 H2]. split; auto. unfold st_ok, huf_ok.
  destruct (st_huf (dm_state dm)) eqn:E; auto.
Qed.

Lemma zunit_step3 : P_zunit_step.
Proof.
  intros sm cd fb hdr z HH u cnt ts' Hbf Hdm Hz _ H Hph Hun Hu Hsafe Hcnt Hck.
  apply (cnt_ok_w _ _ _ _ _ _ Hz) in Hcnt. clear Hz HH.
  unfold cur_rel in H. destruct H as [G [Hl [Ht [Hfd [Hd [Hbsm [Hign [outc [last [Hbp [Hfb Hp]]]]]]]]]]].
  unfold zp_hist in Hbp.
  subst fb. apply bytes_ok_app in Hbf. destruct Hbf as [Hbh Hbr].
  unfold unit_ok in Hun.
  destruct (zp_ph z) as [|bh| |] eqn:Eph.
  - destruct Hp as [-> [Eo _]]. destruct Hun as [Eg H3]. rewrite Eg, app_nil_r.
    unfold cont_checks in Hck. rewrite Eph, Eo in Hck.
    apply cms_lift; [unfold cnt_model_some; rewrite Eph; exact I|].
    rewrite <- app_assoc. eapply step_bhdr; eauto.
  - destruct Hp as [-> [H3 [c [Ec [Hc [Hg Eo]]]]]]. destruct Hun as [c' [Ec' Hn]].
    rewrite Ec in Ec'. inversion Ec'; subst c'.
    destruct (bp_type (block_props_of bh) =? 0) eqn:T.
    + rewrite <- !app_assoc. apply Z.eqb_eq in T.
      unfold cnt_okw in Hcnt. rewrite Eph in Hcnt. rewrite T in Hcnt. cbn [Z.eqb] in Hcnt.
      destruct Hcnt as [Hc1 Hc2].
      assert (Hm: Zlength (zp_got z) + Zlength u = c -> bp_last (block_props_of bh) = 1 ->
                  fcs_okm (zp_h z) (outc ++ zp_got z ++ u)).
      { intros Ecmp L. unfold cont_checks in Hck. rewrite Eph in Hck. unfold fcs_okm.
        rewrite app_assoc, <- Eo, <- Hc1. apply Hck; auto.
        unfold zstep. rewrite Eph, T. cbn [Z.eqb]. rewrite Ec, Zlength_app, Ecmp, Z.eqb_refl.
        unfold zp_with. cbn [zp_ph]. apply next_phase_not_body. }
      apply cms_lift; [unfold cnt_model_some; rewrite Eph; intro X; rewrite T in X; discriminate|].
      rewrite (app_assoc bh). eapply step_body_raw; eauto.
    + destruct Hph as [Hph|Hph]; [apply Z.eqb_neq in T; contradiction|].
      destruct Hn as [_ Hn]. rewrite Hph, app_nil_r. rewrite <- !app_assoc.
      apply bytes_ok_app in Hbr. destruct Hbr as [Hbl _].
      destruct (dm_ok_st _ Hdm) as [Hhb Hst0].
      destruct (bp_bytes _ _ _ _ _ _ _ _ _ Hbp Hhb Hst0 Hbl) as [Hbo Hst].
      assert (Hrle: bp_type (block_props_of bh) = 1 -> bp_origSize (block_props_of bh) <= zp_bsm z).
      { intros T1. unfold cnt_safe in Hsafe. rewrite Eph, T, T1 in Hsafe. cbn [Z.eqb Pos.eqb] in Hsafe. tauto. }
      eapply step_body_nraw; eauto.
  - destruct Hp as [-> [Eo [Hf [Hc1 _]]]]. destruct Hun as [Eg H4].
    rewrite Eg, app_nil_r, <- app_assoc.
    destruct (step_ck sm cd hdr z G Hl Ht Hfd Hd Hbsm Hign Hbh u cnt ts' outc Hbp Eph Eo Hf Hc1 H4 Hck) as [X|X].
    + left. split; [exact X|unfold cnt_model_some; rewrite Eph; exact I].
    + right. exact X.
  - contradiction.
Qed.

Lemma zunit_err3 : P_zunit_err.
Proof.
  intros sm cd fb hdr z HH u cap Hbf Hbsm0 Hz H Hph Hun Hu Herr Hroom.
  apply (cont_err_w _ _ _ _ _ _ Hz) in Herr. clear Hz HH.
  unfold cur_rel in H. destruct H as [G [Hl [Ht [Hfd [Hd [Hbsm [Hign [outc [last [Hbp [Hfb Hp]]]]]]]]]]].
  unfold zp_hist in Hbp.
  subst fb. apply bytes_ok_app in Hbf. destruct Hbf as [Hbh Hbr].
  unfold unit_ok in Hun.
  destruct (zp_ph z) as [|bh| |] eqn:Eph.
  - destruct Hp as [-> [Eo _]]. destruct Hun as [Eg H3]. rewrite Eg, app_nil_r, <- app_assoc.
    unfold cont_errw in Herr. rewrite Eph in Herr.
    eapply err_bhdr; eauto.
  - destruct Hp as [-> [H3 [c [Ec [Hc [Hg Eo]]]]]]. destruct Hun as [c' [Ec' Hn]].
    rewrite Ec in Ec'. inversion Ec'; subst c'.
    apply bytes_ok_app in Hbr. destruct Hbr as [_ Hbr]. apply bytes_ok_app in Hbr. destruct Hbr as [Hbb _].
    destruct (bp_type (block_props_of bh) =? 0) eqn:T.
    + replace ((hdr ++ zp_bl z ++ bh ++ zp_got z) ++ u) with (hdr ++ zp_bl z ++ (bh ++ zp_got z) ++ u)
        by (rewrite !app_assoc; auto).
      apply Z.eqb_eq in T.
      unfold cont_errw in Herr. rewrite Eph in Herr. cbv zeta in Herr. rewrite T in Herr. cbn [Z.eqb] in Herr.
      eapply err_body_raw; eauto.
    + destruct Hph as [Hph|Hph]; [apply Z.eqb_neq in T; contradiction|].
      destruct Hn as [_ Hn]. rewrite Hph, app_nil_r. rewrite <- !app_assoc.
      eapply err_body_nraw; eauto.
  - destruct Hp as [-> [Eo [Hf [Hc1 _]]]]. destruct Hun as [Eg H4].
    rewrite Eg, app_nil_r, <- app_assoc.
    unfold cont_errw in Herr. rewrite Eph, Eo in Herr. destruct Herr as [Hig Hx].
    eapply err_ck; eauto.
  - contradiction.
Qed.

Lemma M3_unit : P_skip_more /\ P_zunit_partial /\ P_zunit_step /\ P_zunit_err.
Proof.
  exact (conj skip_more3 (conj zunit_partial3 (conj zunit_step3 zunit_err3))).
Qed.
