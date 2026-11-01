(* ZSTD_decompressStream, case zdss_loadHeader with the exact claim: G2, the break after a successful shortcut: the loop invariant with ex_call (the model's LStop).
   The relational part is LH3G2's (the same witness, lw_sv0 of the context after the shortcut); the exact conjunct:
   at the entry the model is at a state zi of stage zdss_loadHeader holding the header bytes hb (lhx_view), whose
   iteration is st_load_header, hence st_header_done on the parsed header h; the C's conditions of the shortcut are
   the model's, the shortcut's one-shot decoding (os_match) is the model's x_frame on the frame's bytes
   (lh_short_model), so the model's iteration stops (LStop) in zdss_init after the frame, with the frame's content
   delivered; the context after the shortcut represents that state (zrel_end: expected 0, the tables' litExtraBuffer
   the frame's). *)
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3XDefs.
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3R2Lib Zstd.proof.dec.v3.FS.stream.lh.LH3G2.
Require Import Zstd.proof.model.ExCall Zstd.proof.model.ExStreamFacts.
Require Zstd.proof.model.ExFrame Zstd.proof.model.ExFrameFacts Zstd.proof.model.ExBlockBytes Zstd.proof.model.ExStreamBnd.

(* ---------- the content of a frame decoded on bytes is bytes ---------- *)

Lemma g2x_blocks_bytes (f: nat) (st st': XS) (t out o: list Z) (cap bsm k: Z) :
  bytes_ok (ExBlock.x_lxb ExHuf.xhuf st) -> ExBlockBytes.xh_good (ExBlock.x_huf ExHuf.xhuf st) ->
  bytes_ok t -> bytes_ok out ->
  ExFrame.x_blocks XS Exact.xblock f st t out cap bsm = Some (o, k, st') -> bytes_ok o.
Proof.
  revert st st' t out o k. induction f as [|f IH]; intros st st' t out o k Hl Hh Ht Ho H; [discriminate|].
  rewrite ExFrameFacts.x_blocks_S in H.
  destruct (ExFrameFacts.xb_one XS Exact.xblock st t out cap bsm) as [[[[st1 cn] n] l]|] eqn:E; [|discriminate].
  destruct (ExBlockBytes.xb_one_bytes _ _ _ _ _ _ _ _ _ Ht Ho Hl Hh E) as (Bc & Bl & Bh).
  destruct l.
  - injection H as <- _ _. apply zf_bytes_app; assumption.
  - destruct (ExFrame.x_blocks XS Exact.xblock f st1 (skipn (Z.to_nat n) t) (out ++ cn) cap bsm)
      as [[[o' k'] st'']|] eqn:E2; [|discriminate].
    injection H as <- _ _. eapply (IH st1); [exact Bl | exact Bh | apply zf_forall_skipn, Ht |
      apply zf_bytes_app; [exact Ho | exact Bc] | exact E2].
Qed.

Lemma g2x_frame_bytes (st e: XS) (s c: list Z) (cap k: Z) :
  bytes_ok (ExBlock.x_lxb ExHuf.xhuf st) -> ExBlockBytes.xh_good (ExBlock.x_huf ExHuf.xhuf st) -> bytes_ok s ->
  xframe1 st s cap = Some (c, k, e) -> bytes_ok c.
Proof.
  intros Hl Hh Hs. unfold xframe1, ExFrame.x_frame.
  destruct (_ <? _); [discriminate|]. destruct (_ <? _); [discriminate|].
  destruct (get_frame_header _) as [| |h]; try discriminate.
  destruct (negb _); [discriminate|].
  destruct (ExFrame.x_blocks _ _ _ _ _ _ _ _) as [[[out k1] st1]|] eqn:E; [|discriminate].
  assert (G: bytes_ok out).
  { refine (g2x_blocks_bytes _ _ _ _ _ _ _ _ _ _ _ (zf_forall_skipn _ _ _ Hs) (Forall_nil _) E); [exact Hl | exact I]. }
  destruct (_ && _)%bool; [discriminate|].
  destruct (_ =? 1); [destruct (_ <? 4); [discriminate|]; destruct (negb _); [discriminate|]|];
    intros H; injection H as <- _ _; exact G.
Qed.

Local Open Scope logic.

Section CM_LH3G2X_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.

(* the exact conjunct of the loop invariant after the shortcut *)
Lemma g2x_ex_call : lh_short_model ->
  forall (a: dsa) (w: lw) (hb: list Z) (h: frame_header) (d1: dfields) (did1: val)
         (cSize r: Z) (out: list val) (c: list Z) (fs': fstate) (d': dfields) (lxb': list Z),
    lh_ctx a w hb -> lhx_entry a w -> get_frame_header_m (lh_mg (w_k w)) hb = FH_ok h ->
    gfh3_facts (lh_mg (w_k w)) hb h ->
    let k1 := k_A (w_k w) (fh_val h) d1 did1 in
    lhB_facts a w k1 hb h cSize r out -> is_error_code r = false ->
    bytes_ok c -> Zlength c = r -> sublist 0 r out = zbytes c ->
    lhB_x a w k1 h cSize r out lxb' ->
    ex_call a (lw_sv0 (lhB_brk w k1 fs' d' lxb' (a_ipos a + cSize) r out c)).
Proof.
  intros HSM a w hb h d1 did1 cSize r out c fs' d' lxb' Hc Hx G Hgf k1 HB Hr Hcb Hcl Hco HBx.
  apply ex_call_stop_mk; [reflexivity|]. intros Hf.
  pose proof Hc as (Ha & _ & _ & _ & _ & He & _ & Hdl & _).
  destruct (lhx_view a w hb He Hx Hf) as (z0 & zi & f & Hl & Hz & Hst & Hhb & Hone).
  assert (Hib: bytes_ok (a_ibs a) /\ Zlength (a_ibs a) = a_isz a /\ 0 <= a_ipos a /\ a_isz a <= 2 ^ 63 - 1 /\
               0 <= a_opos a /\ a_osz a <= 2 ^ 63 - 1) by (unfold dsa_ok in Ha; tauto).
  destruct Hib as (Hibb & Hibl & Hip0 & Hisz & Hop0 & Hosz).
  pose proof He as (Hstg & Elh & Hl18 & Hbhb & Hsub & Ehost & Einp & Eos & Eoe & Hipc & Hopc & Hoc & Hsm & Hbase &
                    Hlenok).
  assert (Hmg: lh_mg (w_k w) = false).
  { destruct Hbase as (_ & Hpar & _). destruct Hf as (_ & Hp & _). unfold lh_mg. rewrite Hpar, Hp. reflexivity. }
  assert (Hmg1: lh_mg k1 = false) by exact Hmg.
  destruct HB as (Hft & Hcs & Hcap & Hipcl & Hfcs & HcS & Hr0 & Hlo & Hrcap & Herr & _).
  rewrite Hmg1 in Hfcs. rewrite Hmg in G, Hgf.
  (* hb is the input's first bytes *)
  pose proof Hc as (_ & _ & Hci & _ & _ & _ & Hfp & _ & Hah & Hpend & _).
  unfold call_inv in Hci. cbv zeta in Hci. rewrite Hdl, Hah, Hfp, Hpend in Hci.
  destruct Hci as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlhj & _).
  assert (Ehb: hb = sublist (a_ipos a) (w_ipc w) (a_ibs a)).
  { destruct (Hlhj Hstg hb eq_refl) as (pre & j & Hj & Ehb & Hjj). subst j.
    destruct pre as [ | p0 pre ]; [exact Ehb|].
    exfalso. rewrite Ehb, Zlength_app, Zlength_sublist, Zlength_cons in Hipcl by lia.
    pose proof (Zlength_nonneg pre). lia. }
  assert (Hhs: fh_headerSize h = Zlength hb) by (unfold hdr_lenok in Hlenok; rewrite Hmg, G in Hlenok; exact Hlenok).
  assert (Hhb5: 5 <= Zlength hb).
  { destruct Hgf as (Hsl & _). unfold starting_len, ZSTD_FRAMEHEADERSIZE_PREFIX in Hsl. lia. }
  assert (Hy: bytes_ok (a_xin a)) by (unfold a_xin, bytes_ok in *; apply Forall_sublist; auto).
  assert (Hgap: w_ipc w <= a_ipos a + cSize).
  { rewrite <- Hmg in G, Hfcs.
    apply (G3M.gap_of_hdr_m (lh_mg (w_k w)) (a_ibs a) (a_ipos a) (w_ipc w) (a_isz a) hb h cSize); auto; lia. }
  set (x := sublist (a_ipos a) (a_ipos a + cSize) (a_ibs a)) in *.
  assert (Hxl: Zlength x = cSize) by (unfold x; rewrite Zlength_sublist; lia).
  assert (Hxs: x = hb ++ sublist (w_ipc w) (a_ipos a + cSize) (a_ibs a)).
  { unfold x. rewrite Ehb. rewrite <- sublist_split; auto; lia. }
  assert (Hfirst: firstn (Z.to_nat cSize) (a_xin a) = x).
  { unfold a_xin, x. rewrite <- sublist_firstn, sublist_sublist by lia. f_equal; lia. }
  assert (Hfx: frame_compressed_size x = Some (Zlength x)).
  { destruct (G3M.fcs_m_trunc _ _ _ Hy Hfcs) as [_ Hxk]. rewrite Hfirst in Hxk. rewrite Hxl. exact Hxk. }
  assert (Hxb: bytes_ok x) by (rewrite <- Hfirst; apply zf_forall_firstn, Hy).
  assert (Hsk: is_skippable_magic (le_field x 0 4) = false).
  { destruct Hgf as (_ & _ & _ & _ & _ & _ & _ & Hft1 & _).
    assert (E4: le_field x 0 4 = le_field hb 0 4).
    { rewrite Hxs. unfold le_field, slice. cbn [Z.to_nat skipn]. rewrite firstn_app.
      replace (Pos.to_nat 4 - length hb)%nat with O by (rewrite Zlength_correct in Hhb5; lia).
      rewrite app_nil_r. reflexivity. }
    rewrite E4. destruct (is_skippable_magic (le_field hb 0 4)); [|reflexivity].
    exfalso. apply Hft. apply Hft1. auto. }
  (* the model's block decoder state at the entry: litExtraBuffer of the tables, full size, bytes *)
  set (st := ExStream.d_ent XS (ExStream.zs_dc XS zi)).
  pose proof Hl as (Hr0' & Hz0 & Hzi & _ & _).
  destruct (ExStreamBnd.zinv_x_bnd zi Hzi) as (_ & _ & _ & _ & _ & _ & _ & _ & Hstb & Hsth & _).
  assert (Hstx: ExBlock.x_lxb ExHuf.xhuf st = tabs_lxb (c3_tabs k1)).
  { destruct Hz as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Ht & _). symmetry. exact Ht. }
  destruct (HBx Hf) as (Hom & Hlxl & Hlx). fold x in Hom, Hlx.
  assert (Hstl: Zlength (ExBlock.x_lxb ExHuf.xhuf st) = ExBlock.XLITEXTRA + ExBlock.XWILDCOPY).
  { rewrite Hstx. exact Hlxl. }
  (* the shortcut's result is the model's frame *)
  unfold os_match in Hom. rewrite (HSM st x (fh_contentSize h) Hxb Hfx Hsk Hstl) in Hom.
  destruct (xframe1 st x (fh_contentSize h)) as [[[c' k] e]|] eqn:Efr; [|congruence].
  destruct (k =? Zlength x) eqn:Ek; [|congruence]. apply Z.eqb_eq in Ek. subst k.
  destruct Hom as (Erc & Eout).
  assert (Hc'b: bytes_ok c') by exact (g2x_frame_bytes st e x c' _ _ Hstb Hsth Hxb Efr).
  assert (Hrf: r <= fh_contentSize h).
  { assert (Lz: forall l, Zlength (zbytes l) = Zlength l)
      by (induction l as [|y l IH]; [reflexivity| cbn [zbytes]; rewrite !Zlength_cons; lia]).
    apply (f_equal (@Zlength val)) in Eout. rewrite Lz, Zlength_sublist2, Zlength_sublist2 in Eout.
    pose proof (Zlength_nonneg c'). destruct Hgf as (_ & Hfc0 & _). lia. }
  assert (Ec: c' = c).
  { apply lhx_zbytes_inj; auto. rewrite <- Eout, <- Hco. rewrite sublist_sublist00 by lia. reflexivity. }
  subst c'.
  assert (Elxb: lxb' = ExBlock.x_lxb ExHuf.xhuf e) by exact (Hlx Hr Hsk st e c Hstx Efr).
  (* the model's iteration: st_load_header on the complete header, the shortcut, LStop in zdss_init *)
  set (z1 := ExStream.z_stage XS (ExStream.z_dc XS (ExStream.z_fp XS zi h)
               (ExStream.d_after_shortcut XS (ExStream.zs_dc XS zi) e)) ExStream.ZDSS_init).
  assert (Hit: one_iter_x (a_xin a) (a_xroom a) zi (w_ipc w - a_ipos a) nil =
               ExStream.LStop XS z1 cSize (nil ++ c)).
  { rewrite Hone. unfold ExStream.st_load_header. rewrite Hhb. cbn [get_frame_header_m negb] in G. rewrite G.
    unfold ExStream.st_header_done. cbn [ExStream.zs_hbuf ExStream.zs_dc ExStream.z_fp].
    assert (B1: (fh_contentSize h =? ZSTD_CONTENTSIZE_UNKNOWN) = false) by (apply Z.eqb_neq; exact Hcs).
    assert (B2: (fh_frameType h =? 1) = false) by (apply Z.eqb_neq; exact Hft).
    assert (B3: (a_xroom a - Zlength (@nil Z) >=? fh_contentSize h) = true)
      by (unfold a_xroom; rewrite Zlength_nil; apply Z.geb_le; lia).
    assert (B4: (Zlength hb =? w_ipc w - a_ipos a) = true) by (apply Z.eqb_eq; lia).
    assert (Hfcs': frame_compressed_size (a_xin a) = Some cSize) by exact Hfcs.
    assert (B5: (cSize <=? Zlength (a_xin a)) = true)
      by (apply Z.leb_le; unfold a_xin; rewrite Zlength_sublist; lia).
    rewrite B1, B2, B3, Hhb, B4. cbn [negb andb]. rewrite Hfcs', B5, Hfirst. fold st. rewrite Efr, Hxl, Z.eqb_refl.
    reflexivity. }
  (* nothing was delivered before the shortcut: within the room *)
  assert (Hroom: Zlength (@nil Z) <= a_xroom a) by (unfold a_xroom; rewrite Zlength_nil; lia).
  destruct (ex_loop_stop a z0 zi f (w_ipc w - a_ipos a) nil z1 cSize (nil ++ c) Hy ltac:(unfold a_xin; rewrite Zlength_sublist; lia) Hroom Hl Hit)
    as (Hloop & Hz1).
  exists z0, z1. split; [exact Hr0'|]. split; [exact Hz0|]. split; [exact Hz1|].
  cbn [lw_sv0 lhB_brk w_ipc w_dl]. rewrite Hdl.
  replace (a_ipos a + cSize - a_ipos a) with cSize by lia. split; [exact Hloop|].
  (* the context after the shortcut represents z1: zdss_init, expected 0, the frame's litExtraBuffer, the buffers and
     the ring unchanged, no hostage byte *)
  unfold w_sx, w_fs, w_tabs in *. subst z1.
  cbn [lw_sv0 lhB_brk w_k c3_s c3_fs c3_tabs c3_with_s c3_with_fs c3_with_dict lhB_k fs_expected tabs_lxb].
  set (s0 := sf_strip (c3_s (w_k w))) in Hz. set (s1 := sf_strip (lhB_s k1 d')).
  assert (S1: sf_stage s1 = zdss_init /\ sf_inSize s1 = sf_inSize s0 /\ sf_outSize s1 = sf_outSize s0 /\
              sf_over s1 = sf_over s0 /\ sf_nfp s1 = sf_nfp s0 /\ sf_ring s1 = sf_ring s0 /\
              sf_inPos s1 = sf_inPos s0 /\ sf_outStart s1 = sf_outStart s0 /\ sf_outEnd s1 = sf_outEnd s0 /\
              sf_hostage s1 = sf_hostage s0) by (repeat split; reflexivity).
  clearbody s0 s1. destruct S1 as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10).
  unfold zrel_end, zrel.
  cbn [ExStream.zs_stage ExStream.zs_dc ExStream.z_stage ExStream.z_dc ExStream.z_fp ExStream.zs_inbs
       ExStream.zs_outbs ExStream.zs_over ExStream.zs_nfp ExStream.zs_mem ExStream.zs_inpos ExStream.zs_ostart
       ExStream.zs_oend ExStream.zs_host ExStream.d_after_shortcut ExStream.d_ent ExStream.d_expected
       ExStream.d_stage ExStream.zs_fp fs_expected fsu_expected tabs_lxb].
  destruct Hz as (Zs & Zst & Zin & Zout & Zov & Znfp & Zml & Zmb & Zring & Ztl & Zlh & Zrd).
  destruct (Zlh Hst) as (_ & _ & _ & _ & Zip & Zinp & Zos & Zoe & Zos' & Zoe' & Zh & Zh').
  rewrite Zinp, Zos', Zoe', Zh'. rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9, E10.
  unfold zdss_init, ExStream.ZDSS_init, ExStream.ZDSS_loadHeader, ExStream.ZDSS_read, ExStream.ZDSS_load.
  split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
  - split; [reflexivity|]. split; [lia|]. do 7 (split; [assumption|]). split; [exact Elxb|].
    split; intros Hxx; exfalso; lia.
  - intros _. split; [reflexivity | intros Hxx; exfalso; lia].
  - intros _ Hxx. exfalso; lia.
  - exact Zip.
  - exact Zos.
  - exact Zoe.
  - exact Zh.
  - left; reflexivity.
Qed.

(* the loop invariant's propositions with the exact conjunct: the relational ones and ex_call *)
Lemma g2x_props (a: dsa) (w: lw) :
  fold_right and True (ds_LI_P a w) -> ex_call a w -> fold_right and True (ds_LI_Px a w).
Proof.
  unfold ds_LI_P, ds_LI_Px. cbn [fold_right]. tauto.
Qed.

(* G2: the witness of the relational proof (LH3G2.lh_brkB_ok) with the exact conjunct *)
Lemma lh_brkB_x_ok : lh_brkB_x_stmt.
Proof.
  intros MFh HP Hdd0 HSM DENT TABS a w hb h tbl d1 did1 cSize r out c fs' d' lxb' Hc Hx Hgf0 Hgf HA k1 HB Hr Hcb Hcl
    Hco HD Hfp' HSF HD2 Hut HBx.
  pose proof (g2x_ex_call HSM a w hb h d1 did1 cSize r out c fs' d' lxb' Hc Hx Hgf0 Hgf HB Hr Hcb Hcl Hco HBx)
    as Hex.
  subst k1.
  set (wB := lhB_brk w (k_A (w_k w) (fh_val h) d1 did1) fs' d' lxb' (a_ipos a + cSize) r out c) in *.
  unfold lh_st, ds_inv_x. Exists (lw_sv0 wB).
  assert_PROP ((cold01 (c3_fs (w_k wB)) /\ (c3_set (w_k wB) <> nil -> c3_sp (w_k wB) <> nullval) /\
                (c3_set (w_k wB) = nil -> c3_sp (w_k wB) = nullval)) /\
     (forall od, dict_rel3_of od (c3_dict (w_k wB)) -> forall dr, od = Some dr -> dr_src dr = DSOwn ->
        bytes_ok (dr_bytes dr)) /\
     (forall dr q dd, dc_dict (a_st a) = Some dr -> dr_src dr = DSDDict q dd -> bytes_ok (dd_bytes dd)) /\
     Forall (fun e => cur_ddict (dc_dict (a_st a)) = Some (fst e) \/ bytes_ok (dd_bytes (snd e))) (dc_set (a_st a)) /\
     0 <= sf_held (c3_s (w_k wB)) - local_held (c3_dict (w_k wB)))
    as HF.
  { unfold ds_LI_S. go_lowerx.
    sep_apply (g2_ctx_facts DENT TABS (a_gv a) (a_d a) (w_k wB)). Intros.
    sep_apply (g2_own_bytes DENT TABS (a_gv a) (a_d a) (w_k wB)). Intros.
    sep_apply (g2_dictres_bytes DENT (a_gv a) Ews (dc_dict (a_st a))). Intros.
    sep_apply (g2_setres_bytes DENT (a_gv a) Ews (dc_set (a_st a)) (dc_dict (a_st a))). Intros.
    sep_apply (rl_ctx_held DENT TABS (a_gv a) (a_d a) (w_k wB)). Intros.
    apply prop_right. tauto. }
  destruct HF as ((Hcold & Hsp & Hsp0) & Hown & Hddb & Hsetb & Hheld).
  assert (Hsco: set_cur_ok (a_st a)).
  { destruct Hc as (_ & _ & _ & _ & _ & He & _). destruct He as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hb & _).
    destruct Hb as (_ & _ & _ & _ & ? & _). auto. }
  assert (Hdrb: dc_set (a_st a) = nil -> forall dr q dd, dc_dict (a_st a) = Some dr -> dr_src dr = DSDDict q dd ->
                bytes_ok (dr_bytes dr)).
  { intros Hnil dr q dd Ed Es. rewrite (Hdd0 a w hb Hc Hnil dr q dd Ed Es). eapply Hddb; eauto. }
  apply g2_frame; [reflexivity|reflexivity|].
  apply g2x_props; [|exact Hex].
  eapply brkB_pure; eauto.
  - intros q dd Hin. rewrite Forall_forall in Hsetb. destruct (Hsetb _ Hin) as [Ec|Hb]; [|exact Hb].
    cbn [fst] in Ec. unfold cur_ddict in Ec. destruct (dc_dict (a_st a)) as [dr|] eqn:Ed; [|discriminate].
    destruct (dr_src dr) as [| |q' dd'] eqn:Es; try discriminate. injection Ec as <-.
    rewrite (Hsco dr q' dd' dd Ed Es Hin). eapply Hddb; eauto.
Qed.

End CM_LH3G2X_1.
