(* valid_dict_api main: modes 1 and 2, ZSTD_DCtx_loadDictionary_advanced and one-shot decoding
   (VDA3Defs.VDA_mode_ok). *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.harness.valid_dict_api.WTopSpecs_valid_dict_api.
Require Import Zstd.proof.harness.valid_dict_api.VDA3Defs.
Require Import Zstd.proof.harness.valid_dict_api.VDA3M12Lemmas.
Require Import Zstd.proof.zstd.ApiBridge Zstd.proof.model.ParamsDflt.
Require Import Zstd.proof.zstd.NullBuf.

Local Notation ZCS := Zstd.proof.zstd.Base.CompSpecs.
Local Notation HCS := Zstd.proof.harness.valid_dict_api.HOK_valid_dict_api.CompSpecs.

Ltac m12_kill :=
  match goal with
  | H: false = true |- _ => discriminate H
  | H: true = false |- _ => discriminate H
  | H: ?x <> ?x |- _ => exfalso; exact (H eq_refl)
  | H: Int.repr ?x = Int.repr ?y |- _ =>
      exfalso; apply repr_inj_unsigned in H; [lia | rep_lia | rep_lia]
  | H: Int.repr ?x = Int.zero |- _ =>
      exfalso; change Int.zero with (Int.repr 0) in H; apply repr_inj_unsigned in H; [lia | rep_lia | rep_lia]
  | H: Int.one = Int.zero |- _ => exfalso; apply Int.one_not_zero; exact H
  | H: Int.repr 0 <> Int.zero |- _ => exfalso; apply H; reflexivity
  | H: typed_true _ _ |- _ => inv H
  | H: typed_false _ _ |- _ => inv H
  end.

Section M12.
Variable DC : globals -> val -> dctx_st -> mpred.
Variable DD : globals -> val -> ddict_st -> mpred.
Variable WG : globals -> mpred.
Variable WDS : wdict -> reptype t_wstate -> Prop.

(* VDA_A with the buffers at the decoder's compspecs and the witnesses folded *)
Definition M12_P (gv: globals) (v_dd: val) (m: Z) (wd: wdict) (ws: wseries) (cap: Z) (src buf dctx: val)
    : environ -> mpred :=
  PROP ()
  LOCAL (temp _mode (Vint (Int.repr m)); temp _cap (Vlong (Int64.repr cap)); temp _fail (Vint (Int.repr 0));
         temp _src src; temp _buf buf; temp _dst buf; temp _dict (offset_val (cap + 1) buf); temp _dctx dctx;
         temp _dn (Vlong (Int64.repr (Zlength (wd_bytes wd)))); lvar _dd t_ddp v_dd; gvars gv)
  SEP (mem_mgr gv; zstd_globals gv; DC gv dctx dctx_init;
       @data_at HCS Ews t_wseries (wseries_val ws) (gv _x_valid_dict_api__sr);
       @malloc_token HCS Ews (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws)))) src;
       @malloc_token HCS Ews (tarray tuchar (cap + 1 + Zlength (wd_bytes wd))) buf;
       pws_pred (VB_W src (Zlength (ws_bytes ws)) buf cap);
       @data_at ZCS Ews (tarray tuchar (Zlength (ws_bytes ws))) (zbytes (ws_bytes ws)) src;
       @data_at_ ZCS Ews (tarray tuchar cap) buf;
       @data_at ZCS Ews (tarray tuchar (Zlength (wd_bytes wd))) (zbytes (wd_bytes wd)) (offset_val (cap + 1) buf);
       @data_at HCS Tsh t_ddp (Zrepeat nullval 3) v_dd; TT).

(* after the setup: the load failed (fail = 1, no dictionary) or the context has the dictionary dr12 mm t *)
Definition M12_M (gv: globals) (v_dd: val) (m: Z) (wd: wdict) (ws: wseries) (cap: Z) (src buf dctx: val)
    (fail mm t: Z) (st: dctx_st) : environ -> mpred :=
  PROP (mm = 0 \/ mm = 1; t = 0 \/ t = 1; m = 2 -> t = 1;
        (fail = 0 /\ st = set_dict dctx_init (Some (dr12 mm t (offset_val (cap + 1) buf) (wd_bytes wd)))) \/
        (fail = 1 /\ st = set_dict dctx_init None))
  LOCAL (temp _mode (Vint (Int.repr m)); temp _cap (Vlong (Int64.repr cap)); temp _fail (Vint (Int.repr fail));
         temp _src src; temp _buf buf; temp _dst buf; temp _dctx dctx; lvar _dd t_ddp v_dd; gvars gv)
  SEP (mem_mgr gv; zstd_globals gv; DC gv dctx st;
       @data_at HCS Ews t_wseries (wseries_val ws) (gv _x_valid_dict_api__sr);
       @malloc_token HCS Ews (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws)))) src;
       @malloc_token HCS Ews (tarray tuchar (cap + 1 + Zlength (wd_bytes wd))) buf;
       pws_pred (VB_W src (Zlength (ws_bytes ws)) buf cap);
       @data_at ZCS Ews (tarray tuchar (Zlength (ws_bytes ws))) (zbytes (ws_bytes ws)) src;
       @data_at_ ZCS Ews (tarray tuchar cap) buf;
       @data_at ZCS Ews (tarray tuchar (Zlength (wd_bytes wd))) (zbytes (wd_bytes wd)) (offset_val (cap + 1) buf);
       @data_at HCS Tsh t_ddp (Zrepeat nullval 3) v_dd; TT).

(* after the decoding *)
Definition M12_F (gv: globals) (v_dd: val) (wd: wdict) (ws: wseries) (cap: Z) (src buf dctx: val)
    (st: dctx_st) (out: list val) : environ -> mpred :=
  PROP (Zlength out = cap)
  LOCAL (temp _dctx dctx; temp _src src; temp _buf buf; lvar _dd t_ddp v_dd; gvars gv)
  SEP (mem_mgr gv; zstd_globals gv; DC gv dctx st;
       @data_at HCS Ews t_wseries (wseries_val ws) (gv _x_valid_dict_api__sr);
       @malloc_token HCS Ews (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws)))) src;
       @malloc_token HCS Ews (tarray tuchar (cap + 1 + Zlength (wd_bytes wd))) buf;
       pws_pred (VB_W src (Zlength (ws_bytes ws)) buf cap);
       @data_at ZCS Ews (tarray tuchar (Zlength (ws_bytes ws))) (zbytes (ws_bytes ws)) src;
       @data_at ZCS Ews (tarray tuchar cap) out buf;
       @data_at ZCS Ews (tarray tuchar (Zlength (wd_bytes wd))) (zbytes (wd_bytes wd)) (offset_val (cap + 1) buf);
       @data_at HCS Tsh t_ddp (Zrepeat nullval 3) v_dd; TT).

Lemma M12_setup_ok (Espec: OracleKind) gv v_dd m wd ws cap src buf dctx :
  (m = 1 \/ m = 2) -> dict_facts wd -> isptr src -> isptr buf -> isptr dctx -> 0 <= cap ->
  field_compatible (tarray tuchar (cap + 1 + Zlength (wd_bytes wd))) [] buf ->
  @semax HCS Espec (VDA_Delta DC DD WG WDS) (M12_P gv v_dd m wd ws cap src buf dctx) VDA_setup_s
    (normal_ret_assert (EX fail: Z, EX mm: Z, EX t: Z, EX st: dctx_st,
       M12_M gv v_dd m wd ws cap src buf dctx fail mm t st)).
Proof.
  intros Hm Hdf Hs Hb Hd Hc Hfb.
  unfold M12_P, VDA_setup_s, VDA_Delta.
  simplify_func_tycontext. destruct src; try contradiction; destruct buf; try contradiction; destruct dctx; try contradiction.
  forward_if; [ exfalso; lia | ].
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _x_valid_dict_api__t'46 (Vint Int.one) :: L) (SEPx R))) end.
  { forward. entailer!. }
  { forward. entailer!. destruct Hm; subst m; [contradiction|reflexivity]. }
  forward_if; [ | exfalso; apply Int.one_not_zero; assumption ].
  forward_call 2.
  Intros c1.
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
    forward_if (EX mm: Z, PROPx ((mm = 0 \/ mm = 1) :: P)
                 (LOCALx (temp _x_valid_dict_api__t'24 (Vint (Int.repr mm)) :: L) (SEPx R))) end.
  { forward. Exists 1. entailer!. }
  { forward. Exists 0. entailer!. }
  Intros mm. forward.
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
    forward_if (EX t25: Z, PROPx ((t25 = 0 \/ t25 = 1) :: (m = 2 -> t25 = 1) :: P)
                 (LOCALx (temp _x_valid_dict_api__t'25 (Vint (Int.repr t25)) :: L) (SEPx R))) end.
  { forward. Exists 1. entailer!. }
  { forward_call 2. Intros c2. forward.
    Exists c2. entailer!.
    assert (c2 = 0 \/ c2 = 1) as [-> | ->] by lia; reflexivity. }
  Intros t25.
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
    forward_if (EX t: Z, PROPx ((t = 0 \/ t = 1) :: (m = 2 -> t = 1) :: P)
                 (LOCALx (temp _x_valid_dict_api__t'27 (Vint (Int.repr t)) :: L) (SEPx R))) end.
  { forward. Exists 1. entailer!. }
  { forward. Exists 0. entailer!.
    match goal with H: Int.repr ?x = Int.zero, Ht: ?x = 0 \/ ?x = 1 |- _ =>
      destruct Ht as [-> | ->]; [lia | change Int.zero with (Int.repr 0) in H; m12_kill] end. }
  Intros t. forward.
  pose proof Hdf as (Hdok & Hdl & _).
  forward_call (VB_W (Vptr b i) (Zlength (ws_bytes ws)) (Vptr b0 i0) cap, gv, Vptr b1 i1, dctx_init, Ews,
                offset_val (cap + 1) (Vptr b0 i0), wd_bytes wd, mm, t).
  { assert (buf_ok (VB_W (Vptr b i) (Zlength (ws_bytes ws)) (Vptr b0 i0) cap) Ews (Zlength (wd_bytes wd))
             (offset_val (cap + 1) (Vptr b0 i0))) by (apply VB_buf_ok_dict; [exact I | lia | apply Zlength_nonneg]).
    repeat match goal with |- _ /\ _ => split end; auto; try lia. }
  Intros vret. destruct vret as [r st']. cbn [fst snd] in *.
  forward_call r.
  forward.
  Exists (if is_error_code r then 1 else 0) mm t st'.
  unfold M12_M. entailer!.
  match goal with HL: load_result_adv _ _ _ _ _ |- _ =>
    destruct HL as [(-> & -> & _) | (He & -> & _)]; [left; split; reflexivity | rewrite He; right; split; reflexivity] end.
Qed.

(* the dictionary's memory: what dict_res holds of it (by reference), and what stays with main (by copy) *)
Definition M12_keep (mm: Z) (p: val) (b: list Z) : mpred :=
  if mm =? 1 then emp else @data_at ZCS Ews (tarray tuchar (Zlength b)) (zbytes b) p.

Lemma M12_res gv mm t p b :
  @data_at ZCS Ews (tarray tuchar (Zlength b)) (zbytes b) p =
  (dict_res DD gv Ews (Some (dr12 mm t p b)) * M12_keep mm p b)%logic.
Proof.
  unfold dict_res, dr12, M12_keep. cbn [dr_src dr_bytes].
  destruct (mm =? 1); [rewrite sepcon_emp | rewrite emp_sepcon]; reflexivity.
Qed.

Lemma M12_dec_ok (Espec: OracleKind) gv v_dd m wd ws cap src buf dctx fail mm t st :
  (m = 1 \/ m = 2) -> dict_facts wd -> series_facts (vda_dm m wd) ws -> wseries_wf ws ->
  (m = 1 -> wd_formatted wd = false) -> 0 <= cap <= Zlength (ws_content ws) + 16 ->
  isptr src -> isptr buf -> isptr dctx ->
  field_compatible (tarray tuchar (cap + 1 + Zlength (wd_bytes wd))) [] buf ->
  @semax HCS Espec (VDA_Delta DC DD WG WDS) (M12_M gv v_dd m wd ws cap src buf dctx fail mm t st) VDA_dec_s
    (normal_ret_assert (EX st': dctx_st, EX out: list val, M12_F gv v_dd wd ws cap src buf dctx st' out)).
Proof.
  intros Hm Hdf Hsf Hwf Hf1 Hc Hs Hb Hd Hfb.
  unfold M12_M, VDA_dec_s, VDA_Delta.
  simplify_func_tycontext. destruct src; try contradiction; destruct buf; try contradiction; destruct dctx; try contradiction.
  Intros.
  match goal with H: (fail = 0 /\ _) \/ _ |- _ => destruct H as [[-> ->] | [-> ->]] end.
  2: { forward_if; [ exfalso; m12_kill | ].
       forward. Exists (set_dict dctx_init None) (Zrepeat Vundef cap). unfold M12_F.
       rewrite (@VB_Zrepeat ZCS Ews cap (Vptr b0 i0)). entailer!. }
  forward_if; try solve [m12_kill].
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _x_valid_dict_api__t'56 (Vint Int.zero) :: L) (SEPx R))) end.
  { exfalso; destruct Hm; subst m; lia. }
  { forward. entailer!. destruct Hm; subst m; reflexivity. }
  forward_if; [ exfalso; m12_kill | ].
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _x_valid_dict_api__t'54 (Vint Int.zero) :: L) (SEPx R))) end.
  { exfalso; destruct Hm; subst m; lia. }
  { forward. entailer!. }
  forward_if; [ exfalso; m12_kill | ].
  pose proof Hsf as (Hbok & Hcok & Hnb & Hnc & Hnf & _).
  sep_apply (VB_ws_unfold ws (gv _x_valid_dict_api__sr) Hnb). Intros.
  unfold VB_Rn. forward.
  rewrite (M12_res gv mm t (offset_val (cap + 1) (Vptr b0 i0)) (wd_bytes wd)). Intros.
  forward_call (VB_W (Vptr b i) (Zlength (ws_bytes ws)) (Vptr b0 i0) cap, gv, Vptr b1 i1,
    set_dict dctx_init (Some (dr12 mm t (offset_val (cap + 1) (Vptr b0 i0)) (wd_bytes wd))),
    Ews, Ews, Vptr b0 i0, cap, Ews, Vptr b i, ws_bytes ws).
  { cbn [dc_set set_dict dctx_init]. rewrite set_res_nil. cancel. }
  { split; [apply VB_buf_ok_dst; [exact I | lia] |].
    split; [apply VB_buf_ok_src; [exact I | apply Zlength_nonneg] |].
    apply M12_dict_buf_ok; [exact I | lia | exact Hfb]. }
  Intros vret. destruct vret as [[r out] st']. cbn [fst snd] in *. rewrite mbuf_isptr by auto.
  cbn [dc_set dc_dict set_dict dctx_init] in *. rewrite set_res_nil.
  sep_apply (derives_refl' _ _ (eq_sym (M12_res gv mm t (offset_val (cap + 1) (Vptr b0 i0)) (wd_bytes wd)))).
  match goal with Ho: oneshot_dctx _ _ _ _ _ |- _ =>
    unfold oneshot_dctx in Ho; cbn [dc_set dc_dict dc_par set_dict dctx_init] in Ho;
    rewrite (M12_model m mm t (offset_val (cap + 1) (Vptr b0 i0)) wd Hm Hdf Hf1 H1) in Ho;
    destruct (M12_check (vda_dm m wd) ws cap r out Hsf Hwf Ho) as [Hsucc Herr];
    destruct Ho as [Hle _] end.
  forward.
  forward_call r.
  fold (VB_Rn ws (gv _x_valid_dict_api__sr)).
  forward_if.
  { (* success: the content *)
    assert (He: is_error_code r = false) by (destruct (is_error_code r); [m12_kill | reflexivity]).
    destruct (Hsucc He) as [Er Esub].
    unfold VB_Rcn. forward. fold (VB_Rcn ws (gv _x_valid_dict_api__sr)).
    forward_call (Int.one).
    { entailer!. rewrite Int64.eq_true. reflexivity. }
    try deadvars!.
    match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
      forward;
      forward_loop (EX j: Z, PROPx ((0 <= j <= r) :: P) (LOCALx (temp _j (Vlong (Int64.repr j)) :: L) (SEPx R)))
        break: (PROPx P (LOCALx L (SEPx R))) end.
    { Exists 0. entailer!. }
    { Intros j.
      forward_if.
      2: { forward. entailer!. }
      assert (Hi1: Znth j out = Vint (Int.repr (Znth j (ws_content ws)))) by (apply (VB_out_at (ws_content ws) r out j); auto; lia).
      assert (Hbyte: 0 <= Znth j (ws_content ws) <= Byte.max_unsigned).
      { pose proof (proj1 (Forall_Znth _ _) Hcok j ltac:(lia)) as Hz. unfold is_byte in Hz. rep_lia. }
      rewrite (VB_cs ZCS HCS Ews cap out (Vptr b0 i0)).
      specialize (Hle He).
      forward.
      1: { entailer!. replace (@Znth val Vundef j out) with (Vint (Int.repr (Znth j (ws_content ws)))) by (rewrite <- Hi1; reflexivity). simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
      assert_PROP (@field_compatible HCS t_wseries (DOT _content) (gv _x_valid_dict_api__sr)) as Hfcc
        by (unfold VB_Rc; entailer!).
      rewrite (VI_content_split ws (gv _x_valid_dict_api__sr) Hnc Hfcc). Intros.
      assert_PROP (force_val (sem_add_ptr_long tuchar (offset_val 524296 (gv _x_valid_dict_api__sr)) (Vlong (Int64.repr j))) =
        @field_address HCS (tarray tuchar (Zlength (ws_content ws))) (SUB j)
          (@field_address HCS t_wseries (DOT _content) (gv _x_valid_dict_api__sr))) as Ea.
      { entailer!. rewrite (field_address_offset t_wseries) by auto.
        rewrite arr_field_address by (auto; try lia; rewrite field_address_offset in *; auto).
        simpl; rewrite offset_offset_val; f_equal; lia. }
      forward.
      1: { entailer!. apply Hbyte. }
      sep_apply (derives_refl' _ _ (eq_sym (VI_content_split ws (gv _x_valid_dict_api__sr) Hnc Hfcc))).
      forward_call (Int.one).
      { entailer!.
        replace (@Znth val Vundef j out) with (Vint (Int.repr (Znth j (ws_content ws)))) by (rewrite <- Hi1; reflexivity).
        simpl. rewrite Int.eq_true. reflexivity. }
      forward.
      Exists (j + 1). rewrite (VB_cs HCS ZCS Ews cap out (Vptr b0 i0)).
      entailer!. }
    sep_apply (VB_ws_fold ws (gv _x_valid_dict_api__sr) Hnb).
    Exists st' out. unfold M12_F. entailer!. }
  (* an error: memory_allocation when the capacity holds the content and the frames are within range *)
  assert (He: is_error_code r = true) by (destruct (is_error_code r); [reflexivity | m12_kill]).
  unfold VB_Rcn. forward. fold (VB_Rcn ws (gv _x_valid_dict_api__sr)).
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _x_valid_dict_api__t'51
      (Vint (Int.repr (if andb (Zlength (ws_content ws) <=? cap) (within_oneshot_b (ws_frames ws)) then 1 else 0))) :: L)
      (SEPx R))) end.
  { sep_apply (VB_ws_fold ws (gv _x_valid_dict_api__sr) Hnb).
    forward_call (Ews, gv _x_valid_dict_api__sr, ws).
    forward.
    sep_apply (VB_ws_unfold ws (gv _x_valid_dict_api__sr) Hnb). Intros.
    entailer!.
    rewrite (proj2 (Z.leb_le _ _)) by lia. destruct (within_oneshot_b _); reflexivity. }
  { forward. entailer!. rewrite (proj2 (Z.leb_gt _ _)) by lia. reflexivity. }
  forward_if.
  { assert (Hw: Zlength (ws_content ws) <= cap /\ within_oneshot_b (ws_frames ws) = true).
    { match goal with H: Int.repr (if (?b1 && ?b2)%bool then 1 else 0) <> Int.zero |- _ =>
        destruct (b1 && b2)%bool eqn:Eb; [|contradiction H; reflexivity] end.
      apply andb_prop in Eb as [E1 E2]. apply Z.leb_le in E1. auto. }
    destruct Hw as [Hw1 Hw2].
    pose proof (Herr He Hw1 Hw2) as Er.
    forward_call r.
    forward_call (Int.one).
    { entailer!. }
    sep_apply (VB_ws_fold ws (gv _x_valid_dict_api__sr) Hnb).
    Exists st' out. unfold M12_F. entailer!. }
  { forward.
    sep_apply (VB_ws_fold ws (gv _x_valid_dict_api__sr) Hnb).
    Exists st' out. unfold M12_F. entailer!. }
Qed.

Lemma vda_m12 m : (m = 1 \/ m = 2) -> VDA_mode_ok DC DD WG WDS m.
Proof.
  intros Hm Espec gv v_dd nd which wds wd ws cap src buf dctx.
  unfold VDA_A. Intros.
  match goal with H: vda_facts _ _ _ _ _ _ _ |- _ =>
    destruct (M12_facts m nd which wds wd ws cap Hm H) as (Hdf & Hdw & Hsf & Hwf & Hf1 & Hc) end.
  match goal with Hf: field_compatible (tarray tuchar (Z.max 1 _)) [] src |- _ => rename Hf into Hfs end.
  match goal with Hf: field_compatible (tarray tuchar (cap + 1 + _)) [] buf |- _ => rename Hf into Hfb end.
  pose proof Hsf as (_ & _ & Hnb & _).
  pose proof (Zlength_nonneg (ws_bytes ws)). pose proof (Zlength_nonneg (wd_bytes wd)).
  eapply semax_pre with (P' := M12_P gv v_dd m wd ws cap src buf dctx).
  { unfold M12_P. entailer!.
    sep_apply (M12_bufs src buf ws wd cap ltac:(lia) Hfs Hfb). cancel. }
  eapply semax_seq'.
  { apply M12_setup_ok; auto; lia. }
  Intros fail mm t st.
  eapply semax_post_flipped'.
  { apply (M12_dec_ok Espec gv v_dd m wd ws cap src buf dctx fail mm t st); auto. }
  Intros st' out.
  Exists st' (Zrepeat nullval 3). unfold M12_F, VDA_E. rewrite M12_dd_res.
  entailer!.
  { unfold Zrepeat; simpl; repeat constructor. }
  sep_apply (VB_final_merge src (Zlength (ws_bytes ws)) buf (Zlength out) (Zlength (wd_bytes wd)) out
               (zbytes (wd_bytes wd)) (zbytes (ws_bytes ws)) ltac:(lia) ltac:(lia) ltac:(lia) Hfs Hfb).
  cancel.
Qed.

End M12.

Lemma vda_mode12_ok DC DD WG WDS : VDA_mode_ok DC DD WG WDS 1 /\ VDA_mode_ok DC DD WG WDS 2.
Proof. split; apply vda_m12; auto. Qed.
