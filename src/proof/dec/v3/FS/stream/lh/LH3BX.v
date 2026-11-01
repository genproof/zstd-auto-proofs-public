(* ZSTD_decompressStream, case zdss_loadHeader with the exact claim: piece B, the single-pass shortcut, with its exact facts (LH3XDefs.lhB_none, lhB_x) and its returns' model outcome. *)
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3XDefs Zstd.proof.dec.v3.FS.stream.lh.LH3B.
Require Zstd.proof.dec.v3.FS.stream.lh.LH3RetG Zstd.proof.model.Refuse.
Require Import Zstd.proof.model.ParamsH Zstd.proof.model.ExCall Zstd.proof.model.ExStreamFacts.
Local Open Scope logic.

Section CM_LH3BX_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.

(* ---------- the model's shortcut fails when the C's does ---------- *)

(* a frame x = hb ++ t whose header hb declares its content size: what x_frame decodes of it has that size (the
   end-of-frame check of ZSTD_decompressFrame) *)
Lemma lhB_xframe_len (st e: XS) (hb t c: list Z) (cap k: Z) (h: frame_header) :
  bytes_ok hb -> get_frame_header hb = FH_ok h -> fh_frameType h = 0 ->
  fh_contentSize h <> ZSTD_CONTENTSIZE_UNKNOWN -> fh_headerSize h = Zlength hb ->
  xframe1 st (hb ++ t) cap = Some (c, k, e) -> Zlength c = fh_contentSize h.
Proof.
  intros Hb G Ht Hu Hs X.
  destruct (Refuse.rf_gfh hb h Hb G Ht) as (_ & Hhs & _).
  assert (H5: 5 <= Zlength hb) by (pose proof (Refuse.rf_fhd_hs (byte_at hb 4)); lia).
  assert (E4: byte_at (hb ++ t) 4 = byte_at hb 4).
  { unfold byte_at. apply app_nth1. rewrite Zlength_correct in H5. simpl. lia. }
  assert (Esl: slice (hb ++ t) 0 (fhd_header_size (byte_at hb 4)) = hb).
  { unfold slice. rewrite <- Hhs, Hs. simpl. rewrite Zlength_correct, Nat2Z.id.
    rewrite firstn_app, firstn_all, Nat.sub_diag. simpl. apply app_nil_r. }
  unfold xframe1, ExFrame.x_frame in X. rewrite E4, Esl, G in X.
  destruct (Zlength (hb ++ t) <? _); [discriminate|]. cbv zeta in X.
  destruct (Zlength (hb ++ t) <? _); [discriminate|].
  destruct (negb (fh_dictID h =? 0)); [discriminate|].
  destruct (ExFrame.x_blocks _ _ _ _ _ _ _ _) as [[[o kk] st']|] eqn:B; [|discriminate].
  destruct (negb (fh_contentSize h =? ZSTD_CONTENTSIZE_UNKNOWN) && negb (Zlength o =? fh_contentSize h))%bool eqn:C;
    [discriminate|].
  assert (o = c) by (repeat match type of X with context [if ?b then _ else _] => destruct b end; congruence).
  subst o. apply Bool.andb_false_iff in C. destruct C as [C|C].
  - apply Bool.negb_false_iff, Z.eqb_eq in C. contradiction.
  - apply Bool.negb_false_iff, Z.eqb_eq in C. exact C.
Qed.

(* the shortcut's error return: from the configuration of a new context the model takes the shortcut too (its
   conditions are the C's, the output room counted from output->pos), and the one-shot decoding fails as the C's
   did (os_match), so the model's x_frame on the frame fails or does not take all of it: st_header_done fails *)
Lemma lhB_ret_model (a: dsa) (w: lw) (hb: list Z) (h: frame_header) (cSize r: Z) (outv: list val) :
  lh_short_model -> dsa_ok a -> lh_entry a w hb -> lhx_entry a w -> lh_hb_in a w hb ->
  get_frame_header_m (lh_mg (w_k w)) hb = FH_ok h -> gfh3_facts (lh_mg (w_k w)) hb h ->
  fh_contentSize h <> ZSTD_CONTENTSIZE_UNKNOWN -> fh_frameType h <> 1 -> fh_contentSize h <= a_osz a - w_opc w ->
  w_ipc w - a_ipos a = Zlength hb ->
  frame_compressed_size_m (lh_mg (w_k w)) (sublist (a_ipos a) (a_isz a) (a_ibs a)) = Some cSize ->
  cSize <= a_isz a - a_ipos a ->
  Zlength (tabs_lxb (c3_tabs (w_k w))) = LITEXTRA_N ->
  is_error_code r = true ->
  (fresh_cfg (a_st a) -> os_match (sublist (a_ipos a) (a_ipos a + cSize) (a_ibs a)) (fh_contentSize h) r outv) ->
  ex_err a r.
Proof.
  intros Hsm Ha He Hx Hhbi Hg Hgf Hc1 Hc2 Hc3 Hc4 Hfc HcS Hlx Er Hom.
  apply ex_err_of_loop. intros Hf.
  destruct (lhx_view a w hb He Hx Hf) as (z0 & zi & f & Hl & Hz & Hst & Hhb & Hit).
  exists z0, zi, f, (w_ipc w - a_ipos a), nil. split; [exact Hl|]. rewrite Hit.
  assert (Hdsa: bytes_ok (a_ibs a) /\ 0 <= a_ipos a /\ Zlength (a_ibs a) = a_isz a /\ a_osz a <= 2 ^ 63 - 1 /\
                0 <= a_opos a)
    by (unfold dsa_ok in Ha; tauto).
  destruct Hdsa as (Hbibs & Hip0 & Hlibs & Hosz & Hop0).
  assert (Hent: bytes_ok hb /\ a_ipos a <= w_ipc w <= a_isz a /\ a_opos a <= w_opc w <= a_osz a /\
                base_call (a_st a) (w_k w) /\ hdr_lenok (lh_mg (w_k w)) hb)
    by (unfold lh_entry in He; tauto).
  destruct Hent as (Hbhb & Hipc & Hopc & Hbc & Hlenok).
  assert (Hmg: lh_mg (w_k w) = false).
  { destruct Hbc as (_ & Hp & _). destruct Hf as (_ & Hpd & _). unfold lh_mg. rewrite Hp, Hpd. reflexivity. }
  assert (Hsz: fh_headerSize h = Zlength hb) by (unfold hdr_lenok in Hlenok; rewrite Hg in Hlenok; exact Hlenok).
  pose proof (LH3RetG.RG.gap_of_hdr_m _ (a_ibs a) (a_ipos a) (w_ipc w) (a_isz a) hb h cSize Hbibs Hlibs Hip0
              (proj1 Hipc) (proj2 Hipc) (eq_sym (Hhbi Hc4)) Hg Hsz Hfc) as Hgap.
  rewrite Hmg in Hg, Hgf, Hfc. rewrite get_frame_header_zstd1 in Hg. rewrite frame_compressed_size_zstd1 in Hfc.
  assert (Ht0: fh_frameType h = 0) by (destruct Hgf as (_&_&_&_&_&_&Hft&_); lia).
  set (x := sublist (a_ipos a) (a_ipos a + cSize) (a_ibs a)) in *.
  assert (Hx_hb: x = hb ++ sublist (w_ipc w) (a_ipos a + cSize) (a_ibs a)).
  { subst x. rewrite (Hhbi Hc4), <- sublist_split; auto; lia. }
  assert (Hbx: bytes_ok x) by (subst x; unfold bytes_ok in *; apply Forall_sublist; auto).
  assert (Hlxx: Zlength x = cSize) by (subst x; rewrite Zlength_sublist; lia).
  assert (Hfirst: firstn (Z.to_nat cSize) (sublist (a_ipos a) (a_isz a) (a_ibs a)) = x).
  { subst x. rewrite <- sublist_firstn, sublist_sublist by lia. f_equal; lia. }
  assert (Hfxx: frame_compressed_size x = Some (Zlength x)).
  { assert (Hbs: bytes_ok (sublist (a_ipos a) (a_isz a) (a_ibs a)))
      by (unfold bytes_ok in *; apply Forall_sublist; auto).
    rewrite <- (frame_compressed_size_zstd1 (sublist _ _ _)) in Hfc.
    destruct (LH3RetG.RG.fcs_m_trunc _ _ _ Hbs Hfc) as [_ Ht'].
    rewrite Hfirst, frame_compressed_size_zstd1 in Ht'. rewrite Hlxx. exact Ht'. }
  (* the shortcut of the model's st_header_done *)
  unfold ExStream.st_load_header. rewrite Hhb, Hg.
  unfold ExStream.st_header_done. cbn [ExStream.zs_hbuf ExStream.z_fp ExStream.zs_dc].
  rewrite Hhb.
  assert (Eb: (negb (fh_contentSize h =? ZSTD_CONTENTSIZE_UNKNOWN) && negb (fh_frameType h =? 1) &&
               (a_xroom a - Zlength (@nil Z) >=? fh_contentSize h) && (Zlength hb =? w_ipc w - a_ipos a))%bool = true).
  { unfold a_xroom. rewrite Zlength_nil. rewrite !andb_true_iff, !negb_true_iff, !Z.eqb_neq, Z.geb_le, Z.eqb_eq.
    lia. }
  rewrite Eb. unfold a_xin. rewrite Hfc.
  rewrite (proj2 (Z.leb_le _ _)) by (rewrite Zlength_sublist; lia).
  rewrite Hfirst.
  (* the model's shortcut against the one-shot model *)
  assert (Hlxb: Zlength (ExBlock.x_lxb ExHuf.xhuf (ExStream.d_ent XS (ExStream.zs_dc XS zi))) =
                ExBlock.XLITEXTRA + ExBlock.XWILDCOPY).
  { destruct Hz as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Ht & _). unfold w_tabs in Ht. rewrite <- Ht, Hlx. reflexivity. }
  assert (Hgx: get_frame_header x = FH_ok h).
  { rewrite Hx_hb, <- get_frame_header_zstd1. apply LH3RetG.RG.gfh_m_ext; auto. }
  assert (Hskip: is_skippable_magic (le_field x 0 4) = false).
  { destruct (Refuse.rf_gfh x h Hbx Hgx Ht0) as (Hm & _). rewrite Hm. reflexivity. }
  pose proof (Hsm _ x (fh_contentSize h) Hbx Hfxx Hskip Hlxb) as Hos.
  specialize (Hom Hf). unfold os_match in Hom. rewrite Hos in Hom.
  destruct (xframe1 _ x _) as [[[c k] e]|] eqn:X; [|reflexivity].
  rewrite Hlxx in Hom. destruct (k =? cSize) eqn:Ek; [|reflexivity].
  exfalso. destruct Hom as [Hr _].
  rewrite Hx_hb in X. pose proof (lhB_xframe_len _ e hb _ c _ k h Hbhb Hg Ht0 Hc1 Hsz X) as Hcl.
  unfold is_error_code in Er. apply Z.ltb_lt in Er. lia.
Qed.

(* piece B: LH3B.lhB_gen at the context after piece A, the error return through lhB_ret_model *)
Lemma lhB_x_ok : lhB_x_stmt.
Proof.
unfold lhB_x_stmt.
intros MFh Hlend Hprobe Hsm Espec DENT TABS BR a w hb h tbl d1 did1 HD HT Ha He Hddb Hhbi Hx Hg Hf Hsel.
assert (Hdid: 0 <= fh_dictID h <= Int.max_unsigned) by (destruct Hf as (_&_&_&_&_&_&_&_&_&Hd&_); exact Hd).
apply (lhB_gen Espec DENT TABS BR a w hb h tbl _ MFh Hlend Hprobe HD HT Ha).
- intros Hh1. apply (lhB_entry_k1 a w hb h tbl d1 did1); auto.
- exact Hddb.
- exact Hhbi.
- exact Hg.
- exact Hf.
- reflexivity.
- intros cSize r out fs' d' lxb' Hfa Her Hdi Hfo.
  apply (RC_short a w hb h tbl d1 did1 cSize r out fs' d' lxb'); auto.
- reflexivity.
- intros cSize r out fs' d' lxb' Hfa Er Hom Hlxl _. left.
  destruct Hfa as (Hc2 & Hc1 & Hc3 & Hc4 & Hfc & HcS & _).
  exact (lhB_ret_model a w hb h cSize r (sublist 0 (fh_contentSize h) out) Hsm Ha He Hx Hhbi Hg Hf Hc1 Hc2 Hc3 Hc4
           Hfc HcS Hlxl Er Hom).
Qed.

End CM_LH3BX_1.
