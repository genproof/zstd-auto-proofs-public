(* FS3 streaming, case zdss_read: the precondition of ZSTD_decompressContinueStream at zdss_read
   (layout, history), stable and buffered (v2 StreamSeg_read.v read_pre_stable / read_pre_buf /
   read_cont_hist_*, with v3's dictionary prefix: HL_dict moves to the extDict ExtSep of the DDict content). *)
Require Export Zstd.proof.dec.v3.FS.stream.read.R3Borrow.
Local Open Scope logic.

Ltac zlia := unfold zdss_init, zdss_loadHeader, zdss_read, zdss_load, zdss_flush in *; lia.

Section CM_R3Pre_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* the dictionary content of a DDict's model is the end of its bytes *)
Lemma ddx_model_suffix : forall x dm, ddx_model x = Some dm -> exists pre, dx_bytes x = pre ++ dm_content dm.
Proof.
intros x dm H. unfold ddx_model in H. destruct (dx_raw x).
- inversion H; subst. exists nil. reflexivity.
- unfold dict_auto_c in H.
  destruct (Zlength (dx_bytes x) <? 8); [inversion H; subst; exists nil; reflexivity|].
  destruct (negb _); [inversion H; subst; exists nil; reflexivity|].
  destruct (dx_ld x) as [[st es]|]; [|discriminate]. inversion H; subst. cbn [dm_content].
  exists (firstn (Z.to_nat es) (dx_bytes x)). symmetry. apply firstn_skipn.
Qed.

Lemma Zlength_suffix : forall (pre h: list Z), Zlength h <= Zlength (pre ++ h).
Proof. intros. rewrite Zlength_app. pose proof (Zlength_nonneg pre). lia. Qed.

Lemma byte_at_suffix : forall (pre h: list Z) j, 0 <= j < Zlength h ->
  Znth (Zlength pre + j) (pre ++ h) = byte_at h j.
Proof.
intros pre h j Hj. rewrite Znth_app2 by (pose proof (Zlength_nonneg pre); lia).
replace (Zlength pre + j - Zlength pre) with j by lia.
unfold byte_at, Znth. destruct (Z_lt_dec j 0); [lia|reflexivity].
Qed.

(* the history right after the DDict content became the extDict (a frame's first segment) *)
Lemma hist_view_fresh_dict : forall oc d x eb dm ws, ddx_model x = Some dm ->
  hist_view oc d d (ext_of_dict eb (zbytes (dx_bytes x))) (dm_content dm) nil ws.
Proof.
intros oc d x eb dm ws Hm. destruct (ddx_model_suffix x dm Hm) as [pre Hb].
unfold hist_view, ext_of_dict. rewrite app_nil_r. intros k Hk.
assert (Hl: Zlength (dm_content dm) <= Zlength (dx_bytes x)) by (rewrite Hb; apply Zlength_suffix).
cbn [ext_len]. rewrite Zlength_map. split; [lia|].
unfold chist. rewrite (proj2 (Z.leb_gt k (d - d))) by lia.
erewrite Znth_map by (rewrite ?Zlength_map in *; lia).
rewrite Hb. rewrite Zlength_app.
replace (Zlength pre + Zlength (dm_content dm) - (k - (d - d))) with (Zlength pre + (Zlength (dm_content dm) - k)) by lia.
rewrite byte_at_suffix by lia. reflexivity.
Qed.

(* the facts of c_frame a Zstandard frame's continue call uses *)
Lemma c_frame_zstd_facts : forall fs tabs hdr z l dd, c_frame fs tabs (FP_zstd hdr z) l dd ->
  lay_fields fs l /\ lay_dd l dd /\ dd_model dd (zp_dm z) /\ 0 <= zp_bsm z <= fh_blockSizeMax (zp_h z) /\
  fh_blockSizeMax (zp_h z) = Z.min (fh_windowSize (zp_h z)) ZSTD_BLOCKSIZE_MAX /\ 0 <= fh_windowSize (zp_h z) /\
  bytes_ok (zp_out z).
Proof.
intros fs tabs hdr z l dd H. unfold c_frame in H.
destruct H as (_&_&_&Hlf&Hld&_&_&Hb&Hbe&Hw&_&_&_&Hdm&_&_&_&_&_&Hbo&_). auto 10.
Qed.

(* ---------- stable mode ---------- *)

Lemma read_pre_stable3 : forall a k sv ipc opc oc1 dl, dsa_ok a ->
  call_inv a k sv ipc opc oc1 dl -> sf_stage (c3_s k) = zdss_read -> dc_stable (a_st a) = true ->
  fp_complete (sv_fp sv) = false -> dd_facts (a_W a) (sv_dd sv) ->
  let o := oa_stable (a_shob a) (a_ob a) (a_osz a) (sv_fp sv) oc1 opc in
  lay_at (sv_lay sv) o /\ hist_pre (sv_fp sv) (sv_lay sv) o.
Proof.
intros a k sv ipc opc oc1 dl Ha Hi Hs Hst Hc Hdf o.
assert (Hop0: 0 <= a_opos a) by (destruct Ha as (_&_&_&_&_&_&_&_&_&Ho&_); lia).
destruct Hi as (H1&H2&H3&H4&H5&H6&H7&H8&H9&H10&H11&H12&Hcore&_&Hstout&_).
rewrite Hst in *. specialize (Hstout eq_refl).
set (sout := ss_out (dc_ss (a_st a)) ++ dl) in *.
assert (Hls: Zlength sout = opc).
{ apply (f_equal (@Zlength val)) in Hstout. rewrite Zlength_map, Zlength_sublist in Hstout by lia. lia. }
destruct Hcore as (_&_&_&Hcs). rewrite Hs in Hcs. simpl in Hcs.
destruct Hcs as (_&Hcf&Hring&_).
assert (Hlf: lay_fields (c3_fs k) (sv_lay sv)).
{ destruct (sv_fp sv); unfold c_frame in Hcf; try tauto; destruct Hcf as (_&_&_&Hlf&_); exact Hlf. }
destruct Hring as (_&_&_&os&oe&_&_&_&Hr). destruct Hr as (_&_&_&ob'&osz'&Hob&Hl).
inversion Hob; subst ob' osz'.
unfold o, oa_stable. clear o.
destruct (sv_lay sv) as [|eb ec gp|b pe od|b ps pe e] eqn:El.
- split; [exact I|].
  unfold hist_pre. destruct (sv_fp sv) as [| | |hdr z] eqn:Ef; auto. destruct (zp_ph z) eqn:Ep; auto.
  intros _ Hcap. simpl in Hcap |- *. unfold lmove. simpl.
  destruct (a_osz a - opc <=? 0) eqn:E0; [apply Z.leb_le in E0; lia|].
  destruct (c_frame_zstd_facts _ _ _ _ _ _ Hcf) as (_&Hld&Hdm&_). cbn [lay_dd] in Hld. apply (dd_nodict_model _ _ Hld) in Hdm. simpl in Hl.
  split; [auto|]. split; [auto|]. split; [unfold layout_ok_seg; simpl; lia|].
  split; [|simpl; auto].
  unfold hist_view. rewrite Hl. cbn [hist_for]. unfold zp_hist. rewrite Hdm. intros kk Hk. rewrite Zlength_nil in Hk. lia.
- split; [exact I|].
  unfold hist_pre. destruct (sv_fp sv) as [| | |hdr z] eqn:Ef; auto. destruct (zp_ph z) eqn:Ep; auto.
  intros _ Hcap. simpl in Hcap |- *. unfold lmove.
  destruct (a_osz a - opc <=? 0) eqn:E0; [apply Z.leb_le in E0; lia|].
  destruct (c_frame_zstd_facts _ _ _ _ _ _ Hcf) as (_&Hld&Hdm&_). cbn [lay_dd] in Hld.
  destruct Hld as (x & Edd & -> & _). rewrite Edd in Hdf, Hdm. cbn [dd_model] in Hdm.
  destruct Hdf as (_&Hlen&_). simpl in Hl.
  split; [auto|]. split; [auto|].
  split; [unfold layout_ok_seg, ext_of_dict; cbn [ext_len]; rewrite Zlength_map;
          repeat match goal with |- _ /\ _ => split end;
          first [apply writable_readable, writable_Ews | apply Zlength_nonneg | lia | reflexivity]|].
  split; [|exact I].
  rewrite Hl. apply hist_view_fresh_dict; auto.
- destruct Hl as (->&Hcn&Hpe&Hpe2). split.
  + unfold lay_at; simpl. split; [auto|]. split; [lia|]. destruct (is_skip (sv_fp sv)); lia.
  + unfold hist_pre. destruct (sv_fp sv) as [| | |hdr z] eqn:Ef; auto. destruct (zp_ph z) eqn:Ep; auto.
    intros _ Hcap. simpl in Hcap. lia.
- destruct Hl as (->&Hne&Hpe&Hps&Hsub).
  assert (Hps0: 0 <= ps <= pe) by (destruct Hlf as (_&_&Hlf&_); exact Hlf).
  split.
  + unfold lay_at; simpl. split; [auto|]. split; [lia|]. split; [lia|]. split; [lia|].
    destruct e; auto. contradiction.
  + unfold hist_pre. destruct (sv_fp sv) as [| | |hdr z] eqn:Ef; auto. destruct (zp_ph z) eqn:Ep; auto.
    intros _ Hcap. simpl in Hcap |- *. unfold lmove.
    destruct (a_osz a - opc <=? 0) eqn:E0; [apply Z.leb_le in E0; lia|].
    rewrite (proj2 (Z.eqb_eq pe opc)) by lia.
    destruct (c_frame_zstd_facts _ _ _ _ _ _ Hcf) as (_&Hld&Hdm&_). cbn [lay_dd] in Hld.
    simpl in Hsub, Hps.
    assert (Hlo: Zlength (zp_out z) = pe - ps) by (rewrite <- Hsub; rewrite Zlength_sublist; lia).
    (* the segment's part of the history: the delivered bytes *)
    assert (Hseg: forall kk, 1 <= kk <= Zlength (zp_out z) ->
              Znth (opc - kk) oc1 = Vint (Int.repr (byte_at (zp_out z) (Zlength (zp_out z) - kk)))).
    { intros kk Hk.
      replace (Znth (opc - kk) oc1) with (Znth (opc - kk) (sublist 0 opc oc1))
        by (rewrite Znth_sublist by lia; f_equal; lia).
      rewrite Hstout. rewrite Znth_map by lia. f_equal. f_equal.
      unfold byte_at. rewrite <- Hsub.
      rewrite Zlength_sublist by lia.
      replace (nth (Z.to_nat (pe - ps - kk)) (sublist ps pe sout) 0) with (Znth (pe - ps - kk) (sublist ps pe sout))
        by (unfold Znth; destruct (Z_lt_dec (pe - ps - kk) 0); [lia | reflexivity]).
      rewrite Znth_sublist by lia. f_equal; lia. }
    destruct e as [|e1 elen|sh eb en ec e1 elen].
    * cbn [lay_dd] in Hld. apply (dd_nodict_model _ _ Hld) in Hdm. cbn [hist_for]. unfold zp_hist. rewrite Hdm.
      cbn [dm_content no_dict dict_raw].
      split; [auto|]. split; [lia|]. split; [unfold layout_ok_seg; simpl; lia|].
      split; [|simpl; auto].
      unfold hist_view. simpl app. intros kk Hk. cbn [ext_len]. split; [lia|].
      unfold chist. rewrite (proj2 (Z.leb_le kk (opc - ps))) by lia. apply Hseg. lia.
    * contradiction.
    * destruct Hld as (-> & -> & -> & -> & gp & x & Edd & -> & _). rewrite Edd in Hdf, Hdm.
      cbn [dd_model] in Hdm. destruct Hdf as (_&Hlen&_). cbn [hist_for zp_hist].
      destruct (ddx_model_suffix x _ Hdm) as [pre Hb].
      assert (Hl: Zlength (dm_content (zp_dm z)) <= Zlength (dx_bytes x)) by (rewrite Hb; apply Zlength_suffix).
      split; [auto|]. split; [lia|].
      split; [unfold layout_ok_seg; cbn [ext_len]; rewrite Zlength_map;
              repeat match goal with |- _ /\ _ => split end;
              first [apply writable_readable, writable_Ews | apply Zlength_nonneg | lia | reflexivity]|].
      split; [|exact I].
      unfold hist_view. intros kk Hk. unfold zp_hist in *. rewrite Zlength_app in Hk. cbn [ext_len]. rewrite Zlength_map.
      split; [lia|].
      unfold chist. destruct (kk <=? opc - ps) eqn:Ek.
      -- apply Z.leb_le in Ek. rewrite Hseg by lia. f_equal. f_equal.
         unfold byte_at. rewrite Zlength_app.
         pose proof (Zlength_nonneg (dm_content (zp_dm z))).
         rewrite app_nth2 by (rewrite <- ZtoNat_Zlength; lia). f_equal. rewrite <- ZtoNat_Zlength.
         rewrite <- Z2Nat.inj_sub by lia. f_equal. lia.
      -- apply Z.leb_gt in Ek. erewrite Znth_map by (rewrite ?Zlength_map in *; lia).
         rewrite Hb, Zlength_app.
         replace (Zlength pre + Zlength (dm_content (zp_dm z)) - (kk - (opc - ps)))
           with (Zlength pre + (Zlength (dm_content (zp_dm z)) - (kk - (opc - ps)))) by lia.
         rewrite byte_at_suffix by lia. f_equal. f_equal.
         unfold byte_at. rewrite Zlength_app.
         rewrite app_nth1 by (rewrite <- ZtoNat_Zlength; lia). f_equal. lia.
Qed.

Lemma zbytes_byte : forall b j, bytes_ok b -> 0 <= j < Zlength b -> is_byte_val (Znth j (zbytes b)).
Proof.
intros b j Hb Hj. erewrite Znth_map by lia. exists (Znth j b). split; [|reflexivity].
unfold bytes_ok in Hb. rewrite Forall_Znth in Hb. specialize (Hb j Hj). unfold is_byte in Hb. lia.
Qed.

Lemma read_cont_hist_stable3 : forall a k sv ipc opc oc1 dl, dsa_ok a ->
  call_inv a k sv ipc opc oc1 dl -> sf_stage (c3_s k) = zdss_read -> dc_stable (a_st a) = true ->
  fp_complete (sv_fp sv) = false -> dd_facts (a_W a) (sv_dd sv) -> Forall (value_fits tuchar) oc1 ->
  cont_hist (sv_fp sv) (sv_lay sv) (oa_stable (a_shob a) (a_ob a) (a_osz a) (sv_fp sv) oc1 opc).
Proof.
intros a k sv ipc opc oc1 dl Ha Hi Hs Hst Hnc Hdf Hfits.
destruct (read_pre_stable3 a k sv ipc opc oc1 dl Ha Hi Hs Hst Hnc Hdf) as [Hlay _].
pose proof Hi as Hi'. destruct Hi' as (H1&H2&H3&H4&H5&H6&H7&_&_&_&_&_&Hcore&_&Hstout&_).
rewrite Hst in Hcore. specialize (Hstout Hst).
assert (Hop0: 0 <= a_opos a) by (destruct Ha as (_&_&_&_&_&_&_&_&_&Ho&_); lia).
assert (Hls: Zlength (ss_out (dc_ss (a_st a)) ++ dl) = opc).
{ apply (f_equal (@Zlength val)) in Hstout. rewrite Zlength_map, Zlength_sublist in Hstout by lia. lia. }
assert (Hbs: forall j, 0 <= j < opc -> is_byte_val (Znth j oc1)).
{ intros j Hj.
  assert (E: Znth j oc1 = Vint (Int.repr (Znth j (ss_out (dc_ss (a_st a)) ++ dl)))).
  { replace (Znth j oc1) with (Znth j (sublist 0 opc oc1)) by (rewrite Znth_sublist by lia; f_equal; lia).
    rewrite Hstout. erewrite Znth_map by lia. reflexivity. }
  assert (Hj': 0 <= j < Zlength oc1) by lia.
  rewrite E. apply fits_byte. rewrite <- E.
  rewrite Forall_Znth in Hfits. apply Hfits; exact Hj'. }
destruct Hcore as (_&_&_&Hcs). rewrite Hs in Hcs. simpl in Hcs. destruct Hcs as (_&Hcf&Hring&_).
unfold cont_hist. destruct (sv_fp sv) as [|hb|hdr got|hdr z] eqn:Ef; auto.
destruct (zp_ph z) eqn:Ep; auto. intros _ Hcap.
destruct (c_frame_zstd_facts _ _ _ _ _ _ Hcf) as (_&Hld&_).
cbn [oa_cap oa_base oa_d oa_c oa_stable is_skip] in *.
unfold lmove. rewrite (proj2 (Z.leb_gt _ 0) Hcap).
destruct (sv_lay sv) as [|eb ec gp|b pe od|b ps pe e] eqn:El.
- split; [intros kk Hk; simpl in Hk; lia | left; exact I].
- cbn [lay_dd] in Hld. destruct Hld as (x & Edd & -> & _ & Hbx & _).
  split; [|left; exact I].
  intros kk Hk. cbn [ext_of_dict ext_len] in Hk. rewrite Zlength_map in Hk.
  unfold chist, ext_of_dict. rewrite (proj2 (Z.leb_gt kk (opc - opc))) by lia.
  rewrite Zlength_map. apply zbytes_byte; auto; lia.
- exact I.
- destruct Hring as (_&_&_&os&oe&_&_&_&Hr). destruct Hr as (_&_&_&ob'&osz'&_&Hl).
  destruct Hl as (_&Hne&Hpe&_). rewrite Hpe, Hls, Z.eqb_refl.
  cbn [lay_at oa_stable oa_base oa_d oa_N] in Hlay. destruct Hlay as (_&Hps&_).
  split; [|left; destruct e; simpl; auto; simpl in Hne; contradiction].
  intros kk Hk. unfold chist. destruct (kk <=? opc - ps) eqn:Ek.
  + apply Z.leb_le in Ek. apply Hbs. lia.
  + apply Z.leb_gt in Ek. destruct e as [|e1 elen|sh eb en ec e1 elen]; cbn [ext_len] in Hk; try lia.
    * cbn [lay_dd] in Hld. destruct Hld as (-> & -> & -> & -> & gp & x & Edd & -> & _ & Hbx & _).
      rewrite Zlength_map in Hk |- *. apply zbytes_byte; auto; lia.
Qed.

End CM_R3Pre_1.
