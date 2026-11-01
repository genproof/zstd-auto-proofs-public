(* valid_dict_api main: modes 5 and 6, ZSTD_initDStream_usingDict / usingDDict, vd_stream,
   ZSTD_resetDStream, vd_stream (VDA3Defs.VDA_mode_ok). *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.harness.valid_dict_api.WTopSpecs_valid_dict_api.
Require Import Zstd.proof.harness.valid_dict_api.VDA3Defs.
Require Import Zstd.proof.zstd.ApiBridge Zstd.proof.model.ParamsDflt Zstd.proof.harness.HCsConv.
Require Import Zstd.proof.harness.ApiAfterKit.

Local Notation ZCS := Zstd.proof.zstd.Base.CompSpecs.
Local Notation HCS := Zstd.proof.harness.valid_dict_api.HOK_valid_dict_api.CompSpecs.

(* ---------- model facts ---------- *)

Lemma m56_tiles_le fs off coff n cn : tiles fs off coff n cn -> off <= n.
Proof.
  revert off coff. induction fs as [|f fs IH]; simpl; intros off coff H.
  - lia.
  - destruct H as (_ & _ & Hs & _ & _ & Ht). apply IH in Ht. lia.
Qed.

Lemma m56_n_pos dm ws : series_facts dm ws -> 0 < Zlength (ws_bytes ws).
Proof.
  intros (_ & _ & _ & _ & Hl & Ht & _).
  destruct (ws_frames ws) as [|f fs]; simpl in Hl, Ht; [lia|].
  destruct Ht as (_ & _ & Hs & _ & _ & Ht). apply m56_tiles_le in Ht. lia.
Qed.

Lemma m56_model_auto wd : dict_facts wd -> dict_auto (wd_bytes wd) = Some (wd_model wd).
Proof.
  intros (_ & _ & H & _). unfold wd_model. destruct (dict_auto (wd_bytes wd)); congruence.
Qed.

Lemma m56_vds_eq st st' dm s : dc_par st' = dc_par st -> dc_set st' = dc_set st -> dc_dict st' = dc_dict st ->
  vds_desc st dm s -> vds_desc st' dm s.
Proof.
  intros Hp Hs Hd. unfold vds_desc, st_sel. rewrite Hp, Hs, Hd. auto.
Qed.

Lemma m56_sdo_eq W st st' : dc_set st' = dc_set st -> dc_dict st' = dc_dict st -> dc_bl st' = dc_bl st ->
  stream_dict_ok W st -> stream_dict_ok W st'.
Proof.
  intros Hs Hd Hb. unfold stream_dict_ok. rewrite Hs, Hd, Hb. auto.
Qed.

(* a fresh context with the dictionary d (no set, default parameters) describes the series written for dm *)
Lemma m56_vds_fresh (d: dictref) dm ws : dictref_model (Some d) = Some dm -> series_dwin dm ws ->
  vds_desc (set_dict (set_ss dctx_init ss_init) (Some d)) dm (ws_bytes ws).
Proof.
  intros H Hw. split; [reflexivity|]. intros wl.
  rewrite st_sel_nil by reflexivity. cbn [fst snd dc_dict set_dict set_ss dctx_init dc_par].
  rewrite H, dmode_of_dflt. apply Hw.
Qed.

Lemma m56_starting_ok b : is_error_code (starting_len b) = false.
Proof. destruct b; reflexivity. Qed.

Lemma m56_starting_range b : 0 <= starting_len b <= Int64.max_unsigned.
Proof. destruct b; cbv; split; discriminate. Qed.

(* ---------- buffers ---------- *)

Lemma m56_wvp_at {cs: compspecs} sh k p i q : readable_share sh -> 0 <= i <= k -> 0 < k -> q = offset_val i p ->
  data_at_ sh (tarray tuchar k) p |-- weak_valid_pointer q.
Proof.
  intros Hsh Hi Hk ->. eapply derives_trans; [apply data_at__memory_block_cancel|].
  simpl sizeof. rewrite Z.mul_1_l, Z.max_r by lia.
  apply memory_block_weak_valid_pointer; try lia. apply readable_nonidentity; auto.
Qed.

(* a buffer of n > 0 bytes needs no witness *)
Lemma m56_buf_ok n p : 0 < n -> buf_ok [] Ews n p.
Proof.
  intros Hn. unfold buf_ok, pws_pred. simpl. rewrite emp_sepcon.
  destruct (isptr_dec p) as [Hp|Hp].
  - destruct p; try contradiction. apply andp_right.
    + eapply (m56_wvp_at _ n _ 0); [auto | lia | lia |]. simpl. rewrite Ptrofs.add_zero. reflexivity.
    + eapply (m56_wvp_at _ n _ n); [auto | lia | lia | reflexivity].
  - rewrite data_at__isptr. normalize.
Qed.

Lemma m56_split_bytes_ {cs: compspecs} sh m k p : 0 <= k <= m -> field_compatible (tarray tuchar m) [] p ->
  data_at_ sh (tarray tuchar m) p =
  (data_at_ sh (tarray tuchar k) p * data_at_ sh (tarray tuchar (m - k)) (offset_val k p))%logic.
Proof.
  intros Hk Hf. unfold tarray. rewrite (split2_data_at__Tarray_tuchar sh m k p Hk) by auto with field_compatible.
  rewrite field_address0_offset by auto with field_compatible. simpl. rewrite Z.mul_1_l, Z.add_0_l. reflexivity.
Qed.

(* src: a copy of the series' n > 0 bytes in a block of exactly n bytes *)
Lemma m56_src (cs: compspecs) src (bs: list Z) : 0 < Zlength bs ->
  @data_at HCS Ews (tarray tuchar (Z.max 1 (Zlength bs))) (zbytes bs ++ Zrepeat Vundef (Z.max 1 (Zlength bs) - Zlength bs)) src
  = @data_at cs Ews (tarray tuchar (Zlength bs)) (zbytes bs) src.
Proof.
  intros Hn. rewrite Z.max_r by lia. rewrite Z.sub_diag, Zrepeat_0, app_nil_r.
  apply data_at_bytes_cs.
Qed.

Lemma m56_src_back (cs: compspecs) src (bs: list Z) : 0 < Zlength bs ->
  @data_at cs Ews (tarray tuchar (Zlength bs)) (zbytes bs) src
  |-- @data_at_ HCS Ews (tarray tuchar (Z.max 1 (Zlength bs))) src.
Proof.
  intros Hn. rewrite Z.max_r by lia. rewrite (data_at_bytes_cs cs HCS).
  apply (@data_at_data_at_ HCS).
Qed.

(* buf = [dst (0 bytes) | gap | dict]: back to one block for free *)
Lemma m56_buf_back (cs: compspecs) buf (b: list Z) :
  @field_compatible HCS (tarray tuchar (0 + 1 + Zlength b)) [] buf ->
  @data_at_ HCS Ews (tarray tuchar (0 + 1)) buf *
  @data_at cs Ews (tarray tuchar (Zlength b)) (zbytes b) (offset_val (0 + 1) buf)
  |-- @data_at_ HCS Ews (tarray tuchar (0 + 1 + Zlength b)) buf.
Proof.
  intros Hf. pose proof (Zlength_nonneg b).
  rewrite (@m56_split_bytes_ HCS Ews (0 + 1 + Zlength b) (0 + 1) buf) by (auto; lia).
  replace (0 + 1 + Zlength b - (0 + 1)) with (Zlength b) by lia.
  rewrite (data_at_bytes_cs cs HCS). sep_apply (@data_at_data_at_ HCS Ews (tarray tuchar (Zlength b)) (zbytes b) (offset_val (0 + 1) buf)).
  cancel.
Qed.

Lemma m56_pws_intro (P: mpred) : P |-- P * pws_pred [].
Proof. unfold pws_pred. simpl. rewrite sepcon_emp. auto. Qed.

Lemma m56_pws_elim (P: mpred) : P * pws_pred [] |-- P.
Proof. unfold pws_pred. simpl. rewrite sepcon_emp. auto. Qed.

Lemma m56_res_own (DD: globals -> val -> ddict_st -> mpred) gv st (P: mpred) :
  (exists b, dc_dict st = Some {| dr_src := DSOwn; dr_raw := false; dr_once := false; dr_bytes := b |}) ->
  dc_set st = nil ->
  P |-- P * dict_res DD gv Ews (dc_dict st) * set_res DD gv Ews (dc_set st) (dc_dict st).
Proof.
  intros [b Hd] Hs. rewrite Hd, Hs. unfold dict_res, set_res. simpl. rewrite !sepcon_emp. auto.
Qed.

Lemma m56_dd_null (DD: globals -> val -> ddict_st -> mpred) gv : dd_res DD gv (Zrepeat nullval 3) = emp.
Proof. unfold dd_res. simpl. rewrite !sepcon_emp. reflexivity. Qed.

Lemma m56_dd_q (DD: globals -> val -> ddict_st -> mpred) gv q :
  dd_res DD gv [q; nullval; nullval] = (if eq_dec q nullval then emp else EX x: ddict_st, DD gv q x).
Proof. unfold dd_res. simpl. rewrite !sepcon_emp. reflexivity. Qed.

Lemma m56_and_l (P Q: mpred) : P && Q |-- P.
Proof. apply andp_left1. auto. Qed.

Lemma m56_res_dd (DD: globals -> val -> ddict_st -> mpred) gv st q dd :
  dc_dict st = Some (ddict_ref q dd) -> dd_ref dd = None -> dc_set st = nil ->
  DD gv q dd && valid_pointer q |-- dict_res DD gv Ews (dc_dict st) * set_res DD gv Ews (dc_set st) (dc_dict st).
Proof.
  intros Hd Hr Hs. rewrite Hd, Hs. destruct dd as [b r bf ld]; simpl in Hr; subst r.
  unfold dict_res, set_res, ddict_res. simpl. rewrite !sepcon_emp. auto.
Qed.

Lemma m56_res_dd_back (DD: globals -> val -> ddict_st -> mpred) gv st q dd :
  dc_dict st = Some (ddict_ref q dd) -> dd_ref dd = None -> dc_set st = nil ->
  dict_res DD gv Ews (dc_dict st) * set_res DD gv Ews (dc_set st) (dc_dict st) |-- DD gv q dd && valid_pointer q.
Proof.
  intros Hd Hr Hs. rewrite Hd, Hs. destruct dd as [b r bf ld]; simpl in Hr; subst r.
  unfold dict_res, set_res, ddict_res. simpl. rewrite !sepcon_emp. auto.
Qed.

Ltac m56_ifs := first [repeat apply -> seq_assoc; apply semax_if_seq | idtac]; forward_if.

Ltac m56_kill := solve [ discriminate | lia | contradiction
  | exfalso; match goal with H: Int.repr ?a = Int.zero |- _ =>
      apply (f_equal Int.unsigned) in H; rewrite Int.unsigned_repr in H by rep_lia; simpl in H; lia end
  | exfalso; match goal with H: _ <> _ |- _ => apply H; reflexivity end ].

Section M56.
Variable DC : globals -> val -> dctx_st -> mpred.
Variable DD : globals -> val -> ddict_st -> mpred.
Variable WG : globals -> mpred.
Variable WDS : wdict -> reptype t_wstate -> Prop.

Lemma vda_mode5 : VDA_mode_ok DC DD WG WDS 5.
Proof.
  intros Espec gv v_dd nd which wds wd ws cap src buf dctx.
  unfold VDA_A, VDA_Delta. simplify_func_tycontext.
  unfold VDA_setup_s, VDA_dec_s.
  Intros.
  match goal with H: vda_facts _ _ _ _ _ _ _ |- _ =>
    destruct H as (Hm & Hnd & Hnd2 & Hw & Hw0 & Hwd & Hdf & Hwf & H0' & H134 & H2 & Hsf & Hwsf & H0'' & H4 & H56 & Hcap & Hdwin) end.
  assert (cap = 0) by (apply H56; auto). subst cap.
  assert (Hdw: dict_facts wd) by (eapply Forall_forall; [exact Hdf | eapply nth_error_In; exact Hwd]).
  unfold vda_dm in Hsf; simpl in Hsf.
  assert (Hn: 0 < Zlength (ws_bytes ws)) by (eapply m56_n_pos; eauto).
  pose proof Hdw as (Hbo & Hdn & Hauto & _).
  rewrite (m56_src HCS src (ws_bytes ws) Hn).
  clear H0' H134 H2 H0'' H4 H56 Hm Hnd2 Hw0.
  m56_ifs; [m56_kill|].
  m56_ifs; [m56_kill|].
  forward.
  m56_ifs; [m56_kill|].
  m56_ifs; [m56_kill|].
  m56_ifs; [m56_kill|].
  m56_ifs; [|m56_kill].
  sep_apply (m56_pws_intro (mem_mgr gv)).
  rewrite (data_at_bytes_cs HCS ZCS Ews (Zlength (wd_bytes wd)) (zbytes (wd_bytes wd)) (offset_val (0 + 1) buf)).
  forward_call ([]: list ptr_witness, gv, dctx, dctx_init, Ews, offset_val (0 + 1) buf, wd_bytes wd).
  { cancel. }
  { apply m56_buf_ok; lia. }
  Intros vret. destruct vret as [r st1]; cbn [fst snd] in *.
  match goal with H: (_ /\ _) \/ _ |- _ => destruct H as [[Hr Hst]|[Her [Hst _]]] end.
  - (* success *)
    assert (Hd1: dc_dict st1 = Some {| dr_src := DSOwn; dr_raw := false; dr_once := false; dr_bytes := wd_bytes wd |})
      by (subst st1; reflexivity).
    assert (Hs1: dc_set st1 = nil) by (subst st1; reflexivity).
    assert (Hss1: dc_ss st1 = ss_init) by (subst st1; reflexivity).
    assert (Hst1: dc_stable st1 = false) by (subst st1; reflexivity).
    assert (Hbl1: dc_bl st1 = None) by (subst st1; reflexivity).
    assert (Hv1: vds_desc st1 (wd_model wd) (ws_bytes ws)).
    { subst st1. apply m56_vds_fresh; [cbn; apply m56_model_auto; auto | exact Hdwin]. }
    assert (Hsd1: stream_dict_ok [] st1).
    { unfold stream_dict_ok. rewrite Hd1, Hs1, Hbl1. cbn. auto. }
    clear Hst. subst r. cbn [dc_par dctx_init dparams_dflt dp_fmt Z.eqb] in *.
    forward_call (starting_len false).
    rewrite m56_starting_ok.
    forward.
    m56_ifs; [|m56_kill].
    m56_ifs; [|m56_kill].
    forward.
    m56_ifs; [|m56_kill].
    sep_apply (m56_res_own DD gv st1 (mem_mgr gv) (ex_intro _ _ Hd1) Hs1).
    flatten_sepcon_in_SEP.
    forward_call ([]: list ptr_witness, gv, dctx, st1, Ews, ws, wd_model wd, Ews, src).
    { cancel. }
    { apply m56_buf_ok; lia. }
    Intros st2.
    forward_call (gv, dctx, st2).
    set (st3 := set_ex (set_ss st2 ss_init) false).
    pose proof (m56_starting_range (dp_fmt (dc_par st2) =? 1)).
    forward_call (starting_len (dp_fmt (dc_par st2) =? 1)).
    rewrite m56_starting_ok.
    m56_ifs; [|m56_kill].
    { assert (Hd3: dc_dict st3 = dc_dict st1) by (unfold st3; simpl; congruence).
      assert (Hs3: dc_set st3 = dc_set st1) by (unfold st3; simpl; congruence).
      rewrite <- Hd3, <- Hs3.
      forward_call ([]: list ptr_witness, gv, dctx, st3, Ews, ws, wd_model wd, Ews, src).
      { assert (Hb3: buf_ok [] Ews (Zlength (ws_bytes ws)) src) by (apply m56_buf_ok; lia).
        assert (Hsd3: stream_dict_ok [] st3)
          by (eapply m56_sdo_eq; [exact Hs3 | exact Hd3 | unfold st3; simpl; rewrite H15, Hbl1; reflexivity | exact Hsd1]).
        assert (Hv3: vds_desc st3 (wd_model wd) (ws_bytes ws))
          by (eapply m56_vds_eq; [unfold st3; simpl; exact H13 | exact Hs3 | exact Hd3 | exact Hv1]).
        tauto. }
      Intros st4.
      Exists st4 (Zrepeat nullval 3). unfold VDA_E. rewrite m56_dd_null.
      sep_apply (m56_buf_back ZCS buf (wd_bytes wd) H0).
      sep_apply (m56_src_back HCS src (ws_bytes ws) Hn).
      entailer!; repeat constructor. }
  - (* the initialization failed *)
    forward_call r.
    rewrite Her.
    forward.
    m56_ifs; [m56_kill|].
    forward. Exists st1 (Zrepeat nullval 3). unfold VDA_E. rewrite m56_dd_null.
    sep_apply (m56_buf_back ZCS buf (wd_bytes wd) H0).
    sep_apply (m56_src_back HCS src (ws_bytes ws) Hn).
    entailer!; repeat constructor.
Qed.

Lemma vda_mode6 : VDA_mode_ok DC DD WG WDS 6.
Proof.
  intros Espec gv v_dd nd which wds wd ws cap src buf dctx.
  unfold VDA_A, VDA_Delta. simplify_func_tycontext.
  unfold VDA_setup_s, VDA_dec_s.
  Intros.
  match goal with H: vda_facts _ _ _ _ _ _ _ |- _ =>
    destruct H as (Hm & Hnd & Hnd2 & Hw & Hw0 & Hwd & Hdf & Hwf & H0' & H134 & H2 & Hsf & Hwsf & H0'' & H4 & H56 & Hcap & Hdwin) end.
  assert (cap = 0) by (apply H56; auto). subst cap.
  assert (Hdw: dict_facts wd) by (eapply Forall_forall; [exact Hdf | eapply nth_error_In; exact Hwd]).
  unfold vda_dm in Hsf; simpl in Hsf.
  assert (Hn: 0 < Zlength (ws_bytes ws)) by (eapply m56_n_pos; eauto).
  pose proof Hdw as (Hbo & Hdn & Hauto & _).
  rewrite (m56_src HCS src (ws_bytes ws) Hn).
  clear H0' H134 H2 H0'' H4 H56 Hm Hnd2 Hw0.
  m56_ifs; [m56_kill|].
  m56_ifs; [m56_kill|].
  forward.
  m56_ifs; [m56_kill|].
  m56_ifs; [m56_kill|].
  m56_ifs; [m56_kill|].
  m56_ifs; [m56_kill|].
  sep_apply (m56_pws_intro (mem_mgr gv)).
  rewrite (data_at_bytes_cs HCS ZCS Ews (Zlength (wd_bytes wd)) (zbytes (wd_bytes wd)) (offset_val (0 + 1) buf)).
  forward_call ([]: list ptr_witness, gv, Ews, offset_val (0 + 1) buf, wd_bytes wd).
  { rewrite bytes_at_ptr by (destruct buf; try contradiction; exact I). cancel. }
  { split; [intros Hz; destruct buf; try contradiction; discriminate Hz | intros _; apply m56_buf_ok; lia]. }
  Intros qd. destruct qd as [q dd]. cbn [fst snd] in *.
  rewrite bytes_at_ptr by (destruct buf; try contradiction; exact I).
  assert (Hddr: dd_ref dd = None).
  { match goal with H: dd_ref dd = _ |- _ => rewrite H end.
    rewrite if_false by (intros Hz; destruct buf; try contradiction; discriminate Hz).
    destruct (Z.eqb_spec (Zlength (wd_bytes wd)) 0); [lia | reflexivity]. }
  match goal with H: dd_bytes dd = _ |- _ => rename H into Hddb end.
  forward.
  forward.
  replace (upd_Znth 0 (Zrepeat nullval 3) q) with [q; nullval; nullval]
    by (unfold upd_Znth, Zrepeat; simpl; reflexivity).
  replace (Znth 0 [q; nullval; nullval]) with q by reflexivity.
  destruct (eq_dec q nullval) as [Hq|Hq].
  - (* no DDict *)
    subst q.
    m56_ifs; [|m56_kill].
    forward. forward.
    m56_ifs; [m56_kill|].
    forward. Exists dctx_init [nullval; nullval; nullval]. unfold VDA_E. rewrite m56_dd_q, if_true by auto.
    sep_apply (m56_buf_back ZCS buf (wd_bytes wd) H0).
    sep_apply (m56_src_back HCS src (ws_bytes ws) Hn).
    entailer!; repeat constructor.
  - (* the DDict q *)
    assert (Pq: isptr q) by (destruct q; try contradiction; simpl in *; auto; subst; contradiction).
    m56_ifs; [m56_kill|].
    forward.
    sep_apply (m56_and_l (DD gv q dd) (valid_pointer q)).
    forward_call (gv, dctx, dctx_init, q, dd, Ews).
    { unfold dict_res, set_res. simpl. cancel. }
    Intros vret. destruct vret as [[r st1] r0]. cbn [fst snd] in *.
    api_init; match goal with H: refddict_result _ _ _ _ _ |- _ => destruct H as [[Hr0 Hst]|[Hmu _]]; [|discriminate Hmu] end.
    subst r0.
    match goal with H: (if is_error_code 0 then _ else _) |- _ => cbn in H; subst r end.
    assert (Hd1: dc_dict st1 = Some (ddict_ref q dd)) by (subst st1; reflexivity).
    assert (Hs1: dc_set st1 = nil) by (subst st1; reflexivity).
    assert (Hbl1: dc_bl st1 = None) by (subst st1; reflexivity).
    assert (Hss1: dc_ss st1 = ss_init) by (subst st1; reflexivity).
    assert (Hst1: dc_stable st1 = false) by (subst st1; reflexivity).
    assert (Hv1: vds_desc st1 (wd_model wd) (ws_bytes ws)).
    { eapply m56_vds_eq; [| | | apply (m56_vds_fresh (ddict_ref q dd))]; [subst st1; reflexivity ..| |].
      - cbn. rewrite Hddb. apply m56_model_auto; auto.
      - exact Hdwin. }
    assert (Hsd1: stream_dict_ok [] st1).
    { unfold stream_dict_ok. rewrite Hd1, Hs1, Hbl1. cbn. unfold sddict_ok. rewrite Hddr. auto. }
    clear Hst.
    pose proof (m56_starting_range false).
    forward_call (starting_len false).
    rewrite m56_starting_ok.
    forward.
    forward.
    m56_ifs; [|m56_kill].
    m56_ifs; [m56_kill|].
    forward.
    m56_ifs; [|m56_kill].
    sep_apply (m56_res_dd DD gv st1 q dd Hd1 Hddr Hs1).
    flatten_sepcon_in_SEP.
    forward_call ([]: list ptr_witness, gv, dctx, st1, Ews, ws, wd_model wd, Ews, src).
    { cancel. }
    { assert (Hb1: buf_ok [] Ews (Zlength (ws_bytes ws)) src) by (apply m56_buf_ok; lia). tauto. }
    Intros st2.
    forward_call (gv, dctx, st2).
    set (st3 := set_ex (set_ss st2 ss_init) false).
    pose proof (m56_starting_range (dp_fmt (dc_par st2) =? 1)).
    forward_call (starting_len (dp_fmt (dc_par st2) =? 1)).
    rewrite m56_starting_ok.
    m56_ifs; [|m56_kill].
    assert (Hd3: dc_dict st3 = dc_dict st1) by (unfold st3; simpl; congruence).
    assert (Hs3: dc_set st3 = dc_set st1) by (unfold st3; simpl; congruence).
    rewrite <- Hd3, <- Hs3.
    forward_call ([]: list ptr_witness, gv, dctx, st3, Ews, ws, wd_model wd, Ews, src).
    { assert (Hb3: buf_ok [] Ews (Zlength (ws_bytes ws)) src) by (apply m56_buf_ok; lia).
      assert (Hsd3: stream_dict_ok [] st3)
        by (eapply m56_sdo_eq; [exact Hs3 | exact Hd3 | unfold st3; simpl; match goal with H: dc_bl st2 = None |- _ => rewrite H, Hbl1; reflexivity end | exact Hsd1]).
      assert (Hv3: vds_desc st3 (wd_model wd) (ws_bytes ws))
        by (eapply m56_vds_eq; [unfold st3; simpl; match goal with H: dc_par st2 = _ |- _ => exact H end | exact Hs3 | exact Hd3 | exact Hv1]).
      tauto. }
    Intros st4.
    rewrite Hd3, Hs3.
    sep_apply (m56_res_dd_back DD gv st1 q dd Hd1 Hddr Hs1).
    sep_apply (m56_and_l (DD gv q dd) (valid_pointer q)).
    Exists st4 [q; nullval; nullval]. unfold VDA_E. rewrite m56_dd_q, if_false by auto.
    sep_apply (m56_buf_back ZCS buf (wd_bytes wd) H0).
    sep_apply (m56_src_back HCS src (ws_bytes ws) Hn).
    Exists dd.
    entailer!; repeat constructor; auto.
Qed.

End M56.

Lemma vda_mode56_ok DC DD WG WDS : VDA_mode_ok DC DD WG WDS 5 /\ VDA_mode_ok DC DD WG WDS 6.
Proof. split; [apply vda_mode5 | apply vda_mode6]. Qed.
