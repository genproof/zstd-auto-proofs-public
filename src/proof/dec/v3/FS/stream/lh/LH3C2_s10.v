(* FS3 streaming, case zdss_loadHeader, piece C, segment s10 (LH3C_lib.v). The parts are in
   LH3C2_s10_lib/_g/_vA/_vT/_vC (states, views of the context), LH3C2_s10a (skippable test), LH3C2_s10t (skippable
   frame), LH3C2_s10c/m (ZSTD_decodeFrameHeader), LH3C2_s10e (its error test), LH3C2_s10r (expected, stage). *)
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3C_lib.
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3C2_s10_lib Zstd.proof.dec.v3.FS.stream.lh.LH3C2_s10a Zstd.proof.dec.v3.FS.stream.lh.LH3C2_s10t Zstd.proof.dec.v3.FS.stream.lh.LH3C2_s10m Zstd.proof.dec.v3.FS.stream.lh.LH3C2_s10e Zstd.proof.dec.v3.FS.stream.lh.LH3C2_s10r.
Local Open Scope logic.

Section CM_LH3C2_s10_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma lhC_seg10_ok : lhC_seg10_stmt.
Proof.
unfold lhC_seg10_stmt. intros Espec DENT TABS BR a w hb h tbl d1 did1 HP.
set (k1 := k_A (w_k w) (fh_val h) d1 did1).
unfold lhC_S2.
apply extract_exists_pre; intro dd. apply extract_exists_pre; intro cold.
apply extract_exists_pre; intro lxb.
apply semax_extract_PROP; intro Hlxb.
apply semax_pre with (c10_S2x DENT TABS a w k1 h tbl dd cold lxb); [apply andp_left2; apply derives_refl |].
rewrite c10_eq.
apply semax_seq with (c10_S2b DENT TABS a w k1 h tbl dd cold lxb); [apply (c10_La _ _ _ _ a w hb h tbl d1 did1); exact HP |].
unfold c10_S2b.
eapply semax_pre; [apply andp_left2; apply now_later |].
apply semax_ifthenelse_PQR' with (v := Vint (Int.repr (if fh_frameType h =? 1 then 1 else 0))).
- reflexivity.
- unfold c10_e, ds_LI_L. entailer!.
- unfold c10_e, ds_LI_L. entailer!.
- apply semax_extract_PROP. intro Ht.
  apply c10_Lt; auto.
  destruct (Z.eqb_spec (fh_frameType h) 1); [auto | cbv in Ht; discriminate].
- apply semax_extract_PROP. intro Ht.
  assert (Hft: fh_frameType h <> 1).
  { destruct (Z.eqb_spec (fh_frameType h) 1); [cbv in Ht; discriminate | auto]. }
  rewrite c10_f_eq.
  apply semax_seq with (c10_S2c DENT TABS a w k1 hb h tbl dd cold lxb).
  + apply c10_dowhile0_gen.
    apply c10_body_eq with (Q := c10_SM DENT TABS a w k1 hb h tbl dd cold lxb).
    * apply c10_Lc. exact HP.
    * eapply semax_post_flipped; [apply c10_Le; auto | ..]; cbv beta iota delta [loop1_ret_assert overridePost];
        simpl RA_normal; simpl RA_break; simpl RA_continue; simpl RA_return; intros;
        try (apply andp_left2; apply derives_refl); try (apply andp_left2; intro rho; apply FF_left).
  + apply c10_Lr; auto.
Qed.

End CM_LH3C2_s10_1.
