(* valid_dict_api main, mode 0: the decoding after the setup (VDA3M0Defs.M0_M -> M0_F): streaming
   (vd_stream) or one-shot decoding (ZSTD_decompressDCtx), both with the DDict set. *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.harness.valid_dict_api.WTopSpecs_valid_dict_api.
Require Import Zstd.proof.harness.valid_dict_api.VDA3Defs.
Require Import Zstd.proof.harness.valid_dict_api.VDA3M0Lemmas.
Require Import Zstd.proof.harness.valid_dict_api.VDA3M0Defs.
Require Import Zstd.proof.zstd.NullBuf.

Local Notation ZCS := Zstd.proof.zstd.Base.CompSpecs.
Local Notation HCS := Zstd.proof.harness.valid_dict_api.HOK_valid_dict_api.CompSpecs.

Ltac m0d_kill :=
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

Lemma M0_ddv_facts (l: list (val * ddict_st)) : Forall (fun e => isptr (fst e)) l -> Zlength l <= 3 ->
  Zlength (map fst l ++ Zrepeat nullval (3 - Zlength l)) = 3 /\
  Forall is_pointer_or_null (map fst l ++ Zrepeat nullval (3 - Zlength l)).
Proof.
  intros Hp Hl. split; [rewrite Zlength_app, Zlength_map, Zlength_Zrepeat by (pose proof (Zlength_nonneg l); lia); lia|].
  apply Forall_app; split.
  - apply Forall_map. eapply Forall_impl; [|exact Hp]. intros e He. simpl in He. destruct (fst e); try contradiction; exact I.
  - unfold Zrepeat. apply Forall_repeat. reflexivity.
Qed.

Lemma M0_st_dict d l : dc_dict (M0_st d l) = d.
Proof. reflexivity. Qed.

Lemma M0_st_set' d l : dc_set (M0_st d l) = l.
Proof. reflexivity. Qed.

Lemma M0_cur_ddict l : 0 < Zlength l ->
  match M0_cur l with Some dr => match dr_src dr with DSDDict _ _ => True | _ => False end | None => False end.
Proof.
  intros H. unfold M0_cur. destruct (rev l) as [|e r] eqn:E.
  - apply (f_equal (@length _)) in E. rewrite length_rev in E. simpl in E.
    rewrite Zlength_correct, E in H. simpl in H. lia.
  - exact I.
Qed.

Lemma M0_cur_ne l : 0 < Zlength l -> M0_cur l <> None.
Proof.
  intros H. destruct l as [|e l0] using rev_ind; [rewrite Zlength_nil in H; lia|].
  rewrite M0_cur_snoc. discriminate.
Qed.

Lemma M0_stream_dict_ok W l wds : M0_ok l wds -> 0 < Zlength l ->
  stream_dict_ok W (M0_st (M0_cur l) l).
Proof.
  intros Hok H. pose proof (M0_ok_ref l wds Hok) as Hr.
  unfold stream_dict_ok. rewrite M0_st_dict, M0_st_set'.
  split; [| split; [| reflexivity]].
  - destruct l as [|e l0] using rev_ind; [rewrite Zlength_nil in H; lia|].
    rewrite M0_cur_snoc. cbn. split; [reflexivity|].
    apply Forall_app in Hr as [_ He]. inv He. unfold sddict_ok.
    match goal with H: dd_ref (snd e) = None |- _ => rewrite H end. exact I.
  - eapply Forall_impl; [| exact Hr]. intros e He. unfold sddict_ok. rewrite He. exact I.
Qed.

(* the one-shot preconditions on the dictionaries: copies, no comparison with dst *)
Lemma M0_dict_buf_ok W shk shd cap dst l wds : M0_ok l wds ->
  dict_buf_ok W shk (M0_cur l) shd cap dst /\
  match M0_cur l with Some dr => last_ok (M0_st (M0_cur l) l) dr | None => True end /\
  Forall (fun e => ddict_buf_ok W shk (snd e) shd cap dst) l.
Proof.
  intros Hok. pose proof (M0_ok_ref l wds Hok) as Hr. split; [| split].
  - destruct l as [|e l0] using rev_ind; [exact I|].
    rewrite M0_cur_snoc. cbn. apply Forall_app in Hr as [_ He]. inv He.
    match goal with H: dd_ref (snd e) = None |- _ => rewrite H end. exact I.
  - destruct (M0_cur l); [left; reflexivity | exact I].
  - eapply Forall_impl; [| exact Hr]. intros e He. unfold ddict_buf_ok. rewrite He. exact I.
Qed.

(* one-shot decoding with the set: the claims on the series *)
Lemma M0_check dm ws l cap r out :
  series_facts dm ws -> wseries_wf ws -> 0 < Zlength l ->
  decode_series_m (dmode_of (dc_par (M0_st (M0_cur l) l))) (fst (st_sel (M0_st (M0_cur l) l)))
    (snd (st_sel (M0_st (M0_cur l) l))) no_wlim (ws_bytes ws) = decode_series dm no_wlim (ws_bytes ws) ->
  oneshot_dctx (M0_st (M0_cur l) l) (ws_bytes ws) cap r out ->
  (is_error_code r = false -> r <= cap) /\
  (is_error_code r = false -> r = Zlength (ws_content ws) /\ sublist 0 r out = zbytes (ws_content ws)) /\
  (is_error_code r = true -> Zlength (ws_content ws) <= cap -> within_oneshot_b (ws_frames ws) = true ->
   r = err_code ZSTD_error_memory_allocation).
Proof.
  intros Hf Hw Hl Hd Ho. unfold oneshot_dctx in Ho. rewrite M0_st_set' in Ho.
  destruct l as [|e l0]; [rewrite Zlength_nil in Hl; lia|].
  destruct Ho as [Hle H]. rewrite Hd in H. rewrite (M0L_decode dm ws Hf Hw) in H.
  split; [exact Hle|].
  destruct (within_oneshot_b (ws_frames ws)) eqn:E.
  - destruct H as [H1 H2]. split; auto.
    intros He Hc _. destruct (H2 He) as [Hlt|Hm]; [lia | exact Hm].
  - split; intros He; [rewrite H in He; discriminate | intros _ Hx; discriminate].
Qed.

Section Dec.
Variable DC : globals -> val -> dctx_st -> mpred.
Variable DD : globals -> val -> ddict_st -> mpred.
Variable WG : globals -> mpred.
Variable WDS : wdict -> reptype t_wstate -> Prop.

(* after the decoding *)
Definition M0_F (gv: globals) (v_dd: val) (wds: list wdict) (wd: wdict) (ws: wseries) (cap: Z)
    (src buf dctx: val) (st: dctx_st) (ddv: list val) : environ -> mpred :=
  PROP (Zlength ddv = 3; Forall is_pointer_or_null ddv)
  LOCAL (temp _dctx dctx; temp _src src; temp _buf buf; lvar _dd t_ddp v_dd; gvars gv)
  SEP (mem_mgr gv; zstd_globals gv; DC gv dctx st;
       @data_at HCS Tsh t_ddp ddv v_dd; dd_res DD gv ddv;
       M0_bufs ws wd cap src buf; TT).

Lemma M0_dec_ok (Espec: OracleKind) gv v_dd wds wd ws cap src buf dctx fail l st :
  VDA_m0_model -> In wd wds -> Forall dict_facts wds -> Forall (fun w => wd_id w <> 0) wds ->
  NoDup (map wd_id wds) -> series_facts (wd_model wd) ws -> wseries_wf ws -> series_dwin (wd_model wd) ws ->
  Forall (fun f => wi_skippable f = true \/ (wi_did_size f <> 0 /\ wi_did f = wd_id wd)) (ws_frames ws) ->
  2 <= Zlength wds <= 3 -> 0 <= cap <= Zlength (ws_content ws) + 16 ->
  isptr src -> isptr buf -> isptr dctx ->
  field_compatible (tarray tuchar (cap + 1 + Zlength (wd_bytes wd))) [] buf ->
  @semax HCS Espec (VDA_Delta DC DD WG WDS)
    (M0_M DC DD WDS gv v_dd (Zlength wds) wds wd ws cap src buf dctx fail l st) VDA_dec_s
    (normal_ret_assert (EX st': dctx_st, EX ddv: list val, M0_F gv v_dd wds wd ws cap src buf dctx st' ddv)).
Proof.
  intros Hm Hin Hdf Hid0 Hid Hsf Hwf Hdw Hfr Hnd Hc Hs Hb Hd Hfb.
  unfold M0_M, VDA_dec_s, VDA_Delta.
  simplify_func_tycontext.
  Intros.
  match goal with H: M0_ok l wds |- _ => rename H into Hok end.
  pose proof (M0_ok_ptr l wds Hok) as Hptr.
  forward_if.
  2: { (* a setup step failed: nothing to decode *)
    forward. Exists st (map fst l ++ Zrepeat nullval (3 - Zlength l)). unfold M0_F. entailer!.
    { apply M0_ddv_facts; auto; lia. }
    sep_apply (M0_dd_res DD gv l (3 - Zlength l) Hptr). cancel. }
  assert (fail = 0) by (match goal with H: fail = 0 \/ fail = 1 |- _ => destruct H as [-> | ->]; [reflexivity | m0d_kill] end).
  subst fail.
  match goal with H: 0 = 0 -> _ |- _ => destruct (H eq_refl) as [Hql ->]; clear H end.
  (* the model facts of the set *)
  destruct (Hm wds wd ws (M0_st (M0_cur l) l) Hin Hdf Hid0 Hid Hsf Hwf Hdw Hfr eq_refl
              ltac:(rewrite M0_st_dict; apply M0_cur_ddict; lia)
              ltac:(rewrite M0_st_set'; apply M0_ok_all; auto)) as [Hvds Hone].
  destruct (M0_res DD gv l (M0_ok_ref l wds Hok)) as [F HF].
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _x_valid_dict_api__t'56 (Vint Int.zero) :: L) (SEPx R))) end.
  { exfalso; m0d_kill. }
  { forward. entailer!. }
  forward_if; [ exfalso; m0d_kill | ].
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
    forward_if (EX c: Z, PROPx ((c = 0 \/ c = 1) :: P)
                 (LOCALx (temp _x_valid_dict_api__t'54 (Vint (Int.repr c)) :: L) (SEPx R))) end.
  { forward_call 2. Intros c. forward.
    Exists c. entailer!. assert (c = 0 \/ c = 1) as [-> | ->] by lia; reflexivity. }
  { exfalso; m0d_kill. }
  Intros c.
  pose proof Hsf as (Hbok & Hcok & Hnb & Hnc & Hnf & _).
  forward_if.
  { (* streaming *)
    unfold M0_bufs.
    rewrite (VB_cs ZCS HCS Ews (Zlength (ws_bytes ws)) (zbytes (ws_bytes ws)) src).
    sep_apply (derives_refl' _ _ HF).
    forward_call (VB_W src (Zlength (ws_bytes ws)) buf cap, gv, dctx,
                  M0_st (M0_cur l) l, Ews, ws, wd_model wd, Ews, src).
    { rewrite M0_st_dict, M0_st_set'. cancel. }
    { pose proof (M0_stream_dict_ok (VB_W src (Zlength (ws_bytes ws)) buf cap) l wds Hok ltac:(lia)) as Hsd.
      pose proof (VB_buf_ok_src src (Zlength (ws_bytes ws)) buf cap Hs (Zlength_nonneg _)) as Hbs.
      split; [exact Hbs | exact Hsd]. }
    Intros st'.
    Exists st' (map fst l ++ Zrepeat nullval (3 - Zlength l)). unfold M0_F, M0_bufs.
    rewrite M0_st_dict, M0_st_set'.
    rewrite (VB_cs HCS ZCS Ews (Zlength (ws_bytes ws)) (zbytes (ws_bytes ws)) src).
    sep_apply (derives_refl' _ _ (eq_sym HF)).
    sep_apply (M0_dd_res DD gv l (3 - Zlength l) Hptr).
    entailer!.
    apply M0_ddv_facts; auto; lia. }
  { (* one-shot *)
    unfold M0_bufs. Intros.
    sep_apply (VB_ws_unfold ws (gv _x_valid_dict_api__sr) Hnb). Intros.
    unfold VB_Rn. forward.
    sep_apply (derives_refl' _ _ HF).
    destruct (M0_dict_buf_ok (VB_W src (Zlength (ws_bytes ws)) buf cap) Ews Ews cap buf l wds Hok) as (Hdb & Hlo & Hsb).
    forward_call (VB_W src (Zlength (ws_bytes ws)) buf cap, gv, dctx, M0_st (M0_cur l) l,
      Ews, Ews, buf, cap, Ews, src, ws_bytes ws).
    { rewrite M0_st_dict, M0_st_set'. sep_apply (data_at__mbuf Ews cap buf). cancel. }
    { rewrite ?M0_st_dict, ?M0_st_set'.
      repeat match goal with |- _ /\ _ => split end;
      first [apply VB_buf_ok_dst; [auto | lia] | apply VB_buf_ok_src; [auto | apply Zlength_nonneg]
            | exact Hdb | exact Hlo | exact Hsb | rep_lia | auto]. }
    Intros vret. destruct vret as [[r out] st']. cbn [fst snd] in *. rewrite mbuf_isptr by auto.
    rewrite M0_st_dict, M0_st_set'.
    sep_apply (derives_refl' _ _ (eq_sym HF)).
    match goal with Ho: oneshot_dctx _ _ _ _ _ |- _ =>
      destruct (M0_check (wd_model wd) ws l cap r out Hsf Hwf ltac:(lia) Hone Ho) as (Hle & Hsucc & Herr) end.
    forward.
    forward_call r.
    fold (VB_Rn ws (gv _x_valid_dict_api__sr)).
    forward_if.
    { (* success: the content *)
      assert (He: is_error_code r = false) by (destruct (is_error_code r); [m0d_kill | reflexivity]).
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
        rewrite (VB_cs ZCS HCS Ews cap out buf).
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
        Exists (j + 1). rewrite (VB_cs HCS ZCS Ews cap out buf).
        entailer!. }
      sep_apply (VB_ws_fold ws (gv _x_valid_dict_api__sr) Hnb).
      Exists st' (map fst l ++ Zrepeat nullval (3 - Zlength l)). unfold M0_F, M0_bufs.
      sep_apply (M0_dd_res DD gv l (3 - Zlength l) Hptr).
      sep_apply (@data_at_data_at_ ZCS Ews (tarray tuchar cap) out buf).
      entailer!. apply M0_ddv_facts; auto; lia. }
    (* an error: memory_allocation when the capacity holds the content and the frames are within range *)
    assert (He: is_error_code r = true) by (destruct (is_error_code r); [reflexivity | m0d_kill]).
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
      Exists st' (map fst l ++ Zrepeat nullval (3 - Zlength l)). unfold M0_F, M0_bufs.
      sep_apply (M0_dd_res DD gv l (3 - Zlength l) Hptr).
      sep_apply (@data_at_data_at_ ZCS Ews (tarray tuchar cap) out buf).
      entailer!. apply M0_ddv_facts; auto; lia. }
    { forward.
      sep_apply (VB_ws_fold ws (gv _x_valid_dict_api__sr) Hnb).
      Exists st' (map fst l ++ Zrepeat nullval (3 - Zlength l)). unfold M0_F, M0_bufs.
      sep_apply (M0_dd_res DD gv l (3 - Zlength l) Hptr).
      sep_apply (@data_at_data_at_ ZCS Ews (tarray tuchar cap) out buf).
      entailer!. apply M0_ddv_facts; auto; lia. } }
Qed.

End Dec.
