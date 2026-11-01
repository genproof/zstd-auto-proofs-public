(* valid_dict_api main, mode 0: the setup: ZSTD_d_refMultipleDDicts, then a DDict per dictionary of
   vd_wd, each referenced with ZSTD_DCtx_refDDict (VDA3M0Defs.M0_P -> M0_M). *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.harness.valid_dict_api.WTopSpecs_valid_dict_api.
Require Import Zstd.proof.harness.valid_dict_api.VDA3Defs.
Require Import Zstd.proof.harness.valid_dict_api.VDA3M0Lemmas.
Require Import Zstd.proof.harness.valid_dict_api.VDA3M0Defs.
Require Import Zstd.proof.harness.ApiAfterKit.

Local Notation ZCS := Zstd.proof.zstd.Base.CompSpecs.
Local Notation HCS := Zstd.proof.harness.valid_dict_api.HOK_valid_dict_api.CompSpecs.

Ltac m0_kill :=
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

(* &vd_wd[i] *)
Lemma M0_addr gv i : isptr (vda_wd_addr gv i) -> 0 <= i <= 3 ->
  force_val (sem_add_ptr_int t_wdict Unsigned (gv _vd_wd) (Vint (Int.repr i))) = vda_wd_addr gv i.
Proof.
  intros Hp Hi. unfold vda_wd_addr in *. destruct (gv _vd_wd); try contradiction. simpl.
  f_equal. unfold Ptrofs.of_intu, Ptrofs.of_int. rewrite Int.unsigned_repr by rep_lia.
  rewrite ptrofs_mul_repr. f_equal. f_equal. lia.
Qed.

(* a wdict_t: its first n bytes (for ZSTD_createDDict), and the rest *)
Definition M0_wd_rest (w: wdict) (p: val) (stv: reptype t_wstate) : mpred :=
  (@data_at HCS Ews (tarray tuchar (6144 - Zlength (wd_bytes w))) (Zrepeat (Vint Int.zero) (6144 - Zlength (wd_bytes w)))
     (@field_address0 HCS (tarray tuchar 6144) (SUB (Zlength (wd_bytes w))) (@field_address HCS t_wdict (DOT _bytes) p)) *
   @field_at HCS Ews t_wdict (DOT _n) (vl (Zlength (wd_bytes w))) p *
   @field_at HCS Ews t_wdict (DOT _formatted) (vb (wd_formatted w)) p *
   @field_at HCS Ews t_wdict (DOT _id) (vu (wd_id w)) p *
   @field_at HCS Ews t_wdict (DOT _content) (offset_val (Zlength (wd_bytes w) - Zlength (wd_content w)) p) p *
   @field_at HCS Ews t_wdict (DOT _content_n) (vl (Zlength (wd_content w))) p *
   @field_at HCS Ews t_wdict (DOT _x_valid_dict_api__st) stv p * spacer Ews 13980 13984 p)%logic.

Lemma M0_wd_split w p stv : Zlength (wd_bytes w) <= 6144 -> field_compatible t_wdict [] p ->
  @data_at HCS Ews t_wdict (wdict_val w p stv) p =
  (@data_at ZCS Ews (tarray tuchar (Zlength (wd_bytes w))) (zbytes (wd_bytes w)) p * M0_wd_rest w p stv)%logic.
Proof.
  intros Hn Hf. unfold M0_wd_rest.
  unfold_data_at (@data_at HCS _ _ _ p). cbn [fst snd wdict_val].
  rewrite (field_at_data_at Ews t_wdict (DOT _bytes)).
  change (@nested_field_type HCS t_wdict (DOT _bytes)) with (tarray tuchar 6144).
  rewrite (split2_data_at_Tarray_app (Zlength (wd_bytes w)) 6144 Ews tuchar).
  2: { rewrite Zlength_map. reflexivity. }
  2: { rewrite Zlength_Zrepeat; [reflexivity|]. pose proof (Zlength_nonneg (wd_bytes w)). lia. }
  rewrite (VB_cs HCS ZCS).
  replace (@field_address HCS t_wdict (DOT _bytes) p) with p at 1
    by (rewrite field_address_offset by auto with field_compatible; simpl; rewrite isptr_offset_val_zero; auto with field_compatible).
  apply pred_ext; cancel.
Qed.

Lemma M0_buf_ok_nil n p : isptr p -> 0 < n -> buf_ok [] Ews n p.
Proof.
  intros Hp Hn. destruct p; try contradiction. unfold buf_ok, pws_pred. simpl. rewrite emp_sepcon.
  apply andp_right; [VB_piece n 0 | VB_piece n n].
Qed.

Lemma M0_isptr q : is_pointer_or_null q -> q <> nullval -> isptr q.
Proof. intros H N. destruct q; simpl in *; auto; subst; contradiction. Qed.

Lemma M0_err0 : is_error_code 0 = false.
Proof. vm_compute. reflexivity. Qed.

Lemma M0_st_add d l d' l' : set_set (set_dict (M0_st d l) d') l' = M0_st d' l'.
Proof. reflexivity. Qed.

Lemma M0_st_set d l : dc_set (M0_st d l) = l.
Proof. reflexivity. Qed.

Lemma M0_st_multi d l : dp_multi (dc_par (M0_st d l)) = 1.
Proof. reflexivity. Qed.

Lemma M0_st_dict d l : dc_dict (M0_st d l) = d.
Proof. reflexivity. Qed.

Lemma M0_andp_drop (P Q: mpred) : P && Q |-- P.
Proof. apply andp_left1, derives_refl. Qed.

Section Setup.
Variable DC : globals -> val -> dctx_st -> mpred.
Variable DD : globals -> val -> ddict_st -> mpred.
Variable WG : globals -> mpred.
Variable WDS : wdict -> reptype t_wstate -> Prop.

Lemma M0_wds_fold gv wds i stv : 0 <= i < Zlength wds -> Zlength (wd_bytes (Znth i wds)) <= 6144 ->
  field_compatible t_wdict [] (vda_wd_addr gv i) -> WDS (Znth i wds) stv ->
  @data_at ZCS Ews (tarray tuchar (Zlength (wd_bytes (Znth i wds)))) (zbytes (wd_bytes (Znth i wds))) (vda_wd_addr gv i) *
  M0_wd_rest (Znth i wds) (vda_wd_addr gv i) stv *
  vda_wds_from WDS gv 0 (sublist 0 i wds) * vda_wds_from WDS gv (i + 1) (sublist (i + 1) (Zlength wds) wds)
  |-- vda_wds_from WDS gv 0 wds.
Proof.
  intros Hi Hn Hf Hw. rewrite (M0_wds_split WDS gv wds i Hi).
  rewrite <- (M0_wd_split (Znth i wds) (vda_wd_addr gv i) stv Hn Hf).
  unfold wdict_rep. Exists stv. entailer!.
Qed.

Lemma M0_dds_snoc gv l q dd :
  M0_dds DD gv (l ++ [(q, dd)]) = (M0_dds DD gv l * (DD gv q dd && valid_pointer q))%logic.
Proof. rewrite M0_dds_app, M0_dds_one. reflexivity. Qed.

Lemma M0_setup_ok (Espec: OracleKind) gv v_dd nd wds wd ws cap src buf dctx :
  2 <= nd <= 3 -> Zlength wds = nd -> Forall dict_facts wds -> NoDup (map wd_id wds) ->
  isptr src -> isptr buf -> isptr dctx -> 0 <= cap ->
  @semax HCS Espec (VDA_Delta DC DD WG WDS) (M0_P DC WDS gv v_dd nd wds wd ws cap src buf dctx) VDA_setup_s
    (normal_ret_assert (EX fail: Z, EX l: list (val * ddict_st), EX st: dctx_st,
       M0_M DC DD WDS gv v_dd nd wds wd ws cap src buf dctx fail l st)).
Proof.
  intros Hnd Hl Hdf Hid Hs Hb Hd Hc. subst nd.
  unfold M0_P, VDA_setup_s, VDA_Delta.
  simplify_func_tycontext.
  forward_if; [ | exfalso; m0_kill ].
  forward_call (gv, dctx, dctx_init, ZSTD_d_refMultipleDDicts, 1).
  { cbv; tauto. }
  Intros vret. destruct vret as [r st1]. cbn [fst snd] in *.
  match goal with H: after_stage _ _ _ _ |- _ => apply after_stage_init in H; [unfold setpar_res in H | reflexivity] end.
  match goal with H: if _ then _ else _ |- _ =>
    assert (Hr: r = 0 /\ st1 = set_par dctx_init M0_par) by exact H; clear H end.
  destruct Hr as [-> ->].
  forward_call 0.
  forward_call (Int.one).
  forward.
  forward_loop (EX i: Z, EX fail: Z, EX l: list (val * ddict_st), EX st: dctx_st,
    PROP (0 <= i <= (Zlength wds); fail = 0 \/ fail = 1; M0_ok l wds; Zlength l <= i;
          fail = 0 -> Zlength l = i /\ st = M0_st (M0_cur l) l)
    LOCAL (temp _i (Vint (Int.repr i)); temp _mode (Vint (Int.repr 0)); temp _nd (Vint (Int.repr (Zlength wds)));
           temp _cap (Vlong (Int64.repr cap)); temp _fail (Vint (Int.repr fail));
           temp _src src; temp _buf buf; temp _dst buf; temp _dctx dctx; lvar _dd t_ddp v_dd; gvars gv)
    SEP (mem_mgr gv; zstd_globals gv; DC gv dctx st;
         @data_at HCS Ews t_wseries (wseries_val ws) (gv _x_valid_dict_api__sr);
         vda_wds_from WDS gv 0 wds; M0_bufs ws wd cap src buf;
         @data_at HCS Tsh t_ddp (map fst l ++ Zrepeat nullval (3 - Zlength l)) v_dd;
         M0_dds DD gv l; TT))
    break: (EX fail: Z, EX l: list (val * ddict_st), EX st: dctx_st,
       M0_M DC DD WDS gv v_dd (Zlength wds) wds wd ws cap src buf dctx fail l st).
  { Exists 0 0 (@nil (val * ddict_st)) (M0_st None nil). entailer!.
    { apply M0_ok_nil. }
    unfold M0_dds. simpl. replace (M0_st None []) with (set_par dctx_init M0_par) by reflexivity. cancel. }
  Intros i fail l st.
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _x_valid_dict_api__t'18
      (Vint (Int.repr (if i <? (Zlength wds) then (if fail =? 0 then 1 else 0) else 0))) :: L) (SEPx R))) end.
  { forward. entailer!. rewrite (proj2 (Z.ltb_lt _ _)) by lia.
    match goal with H: fail = 0 \/ fail = 1 |- _ => destruct H as [-> | ->]; reflexivity end. }
  { forward. entailer!. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity. }
  forward_if.
  2: { (* break *)
    forward. Exists fail l st. unfold M0_M. entailer!.
    try intros ->.
    destruct (i <? Zlength wds) eqn:E; [exfalso; rewrite ?Z.eqb_refl in *; m0_kill |]. apply Z.ltb_ge in E.
    assert (i = Zlength wds) by lia. subst i.
    match goal with H: 0 = 0 -> _ |- _ => destruct (H eq_refl) as [Hq ->] end. split; [exact Hq | reflexivity]. }
  assert (Hi: i < (Zlength wds) /\ fail = 0).
  { destruct (i <? (Zlength wds)) eqn:E; [|exfalso; m0_kill]. apply Z.ltb_lt in E.
    destruct (fail =? 0) eqn:F; [|exfalso; m0_kill]. apply Z.eqb_eq in F. auto. }
  destruct Hi as [Hi ->].
  match goal with H: 0 = 0 -> _ |- _ => destruct (H eq_refl) as [Hqi ->]; clear H end.
  sep_apply (derives_refl' _ _ (M0_wds_split WDS gv wds i ltac:(lia))).
  unfold wdict_rep at 1. Intros stv.
  assert_PROP (isptr (vda_wd_addr gv i)) as Hwp by entailer!.
  assert_PROP (offset_val 6144 (force_val (sem_add_ptr_int t_wdict Unsigned (gv _vd_wd) (Vint (Int.repr i)))) =
               @field_address HCS t_wdict (DOT _n) (vda_wd_addr gv i)) as Ean.
  { entailer!. rewrite field_address_offset by auto with field_compatible.
    unfold vda_wd_addr. rewrite offset_offset_val. f_equal. simpl. lia. }
  forward.
  match goal with |- context [temp _x_valid_dict_api__t'67 ?v] =>
    replace v with (vl (Zlength (wd_bytes (Znth i wds)))) by reflexivity end.
  pose proof (proj1 (Forall_Znth _ _) Hdf i ltac:(lia)) as Hdfi.
  pose proof Hdfi as (Hbok & Hblen & _).
  assert (Hn6: Zlength (wd_bytes (Znth i wds)) <= 6144) by rep_lia.
  assert_PROP (field_compatible t_wdict [] (vda_wd_addr gv i)) as Hfw by entailer!.
  sep_apply (derives_refl' _ _ (M0_wd_split (Znth i wds) (vda_wd_addr gv i) stv Hn6 Hfw)).
  Intros.
  forward_call ([] : list ptr_witness, gv, Ews, vda_wd_addr gv i, wd_bytes (Znth i wds)).
  { entailer!. unfold vda_wd_addr. simpl. destruct (gv _vd_wd); try contradiction. simpl.
    rewrite Ptrofs.add_zero, Z.mul_comm. reflexivity. }
  { unfold pws_pred. simpl. rewrite bytes_at_ptr by exact Hwp. cancel. }
  { split; [intro E; rewrite E in Hwp; contradiction | intros _; apply M0_buf_ok_nil; [auto | lia]]. }
  Intros vret. destruct vret as [q dd]. cbn [fst snd] in *.
  rewrite bytes_at_ptr by exact Hwp.
  match goal with H: dd_ref dd = (if _ then _ else _) |- _ => rename H into Hddr end.
  rewrite if_false in Hddr by (intro E; rewrite E in Hwp; contradiction).
  rewrite (proj2 (Z.eqb_neq _ _)) in Hddr by lia.
  match goal with H: dd_bytes dd = _ |- _ => rename H into Hddb end.
  change (pws_pred []) with emp.
  sep_apply (M0_wds_fold gv wds i stv ltac:(lia) Hn6 Hfw H5).
  clear Ean.
  forward.
  forward.
  { entailer!. rewrite upd_Znth_same by list_solve. auto. }
  rewrite upd_Znth_same by list_solve.
  destruct (eq_dec q nullval) as [Eq | Nq].
  { (* ZSTD_createDDict failed *)
    subst q. try rewrite if_true by reflexivity.
    match goal with |- semax _ (PROPx ?P (LOCALx _ (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp _x_valid_dict_api__t'20 (Vint Int.one) :: [temp _i (Vint (Int.repr i)); temp _mode (Vint (Int.repr 0)); temp _nd (Vint (Int.repr (Zlength wds)));
           temp _cap (Vlong (Int64.repr cap)); temp _fail (Vint (Int.repr 0));
           temp _src src; temp _buf buf; temp _dst buf; temp _dctx dctx; lvar _dd t_ddp v_dd; gvars gv]) (SEPx R))) end.
    { forward. entailer!. }
    { exfalso; m0_kill. }
    match goal with |- semax _ (PROPx ?P (LOCALx _ (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx [temp _i (Vint (Int.repr i)); temp _mode (Vint (Int.repr 0)); temp _nd (Vint (Int.repr (Zlength wds)));
           temp _cap (Vlong (Int64.repr cap)); temp _fail (Vint (Int.repr 1));
           temp _src src; temp _buf buf; temp _dst buf; temp _dctx dctx; lvar _dd t_ddp v_dd; gvars gv] (SEPx R))) end.
    { forward. entailer!. }
    { exfalso; m0_kill. }
    forward.
    Exists (i + 1) 1 l (M0_st (M0_cur l) l).
    entailer!.
    replace (upd_Znth (Zlength l) (map fst l ++ Zrepeat nullval (3 - Zlength l)) nullval)
      with (map fst l ++ Zrepeat nullval (3 - Zlength l)) by list_solve.
    cancel. }
  apply semax_if_seq. forward_if.
  { contradiction. }
  forward.
  { entailer!. rewrite upd_Znth_same by list_solve. auto. }
  rewrite upd_Znth_same by list_solve.
  sep_apply (M0_andp_drop (DD gv q dd) (valid_pointer q)).
  match goal with Hk: M0_ok l wds |- _ => rename Hk into Hok end.
  destruct (M0_res DD gv l (M0_ok_ref l wds Hok)) as [F HF].
  sep_apply (derives_refl' _ _ HF).
  forward_call (gv, dctx, M0_st (M0_cur l) l, q, dd, Ews).
  { rewrite M0_st_dict, M0_st_set. destruct (eq_dec q nullval); [contradiction|]. cancel. }
  { rewrite M0_st_set; rep_lia. }
  Intros vret. destruct vret as [r st']. cbn [fst snd] in *.
  rewrite M0_st_dict, M0_st_set.
  api_init. destruct (eq_dec q nullval); [contradiction|].
  sep_apply (derives_refl' _ _ (eq_sym HF)).
  forward_call r.
  forward.
  assert (Hdd: (upd_Znth i (map fst l ++ Zrepeat nullval (3 - Zlength l)) q) =
               map fst (l ++ [(q, dd)]) ++ Zrepeat nullval (3 - Zlength (l ++ [(q, dd)]))) by list_solve.
  rewrite Hdd. clear Hdd.
  assert (Hok': M0_ok (l ++ [(q, dd)]) wds) by (apply M0_ok_snoc; auto; [apply M0_isptr; auto | lia | rewrite Hqi; exact Hddb]).
  api_init; match goal with H: refddict_result _ _ _ _ _ |- _ => destruct H as [[-> Hst] | (_ & Her & Hst)] end.
  { (* referenced and added to the set *)
    rewrite M0_err0.
    apply semax_if_seq. forward_if; [ exfalso; m0_kill | ].
    forward.
    Exists (Zlength l + 1) 0 (l ++ [(q, dd)]) st'.
    entailer!.
    { rewrite Zlength_app, Zlength_cons, Zlength_nil. split; [lia|]. intros _. split; [lia|].
      rewrite M0_cur_snoc, M0_st_multi, Z.eqb_refl, M0_st_set.
      rewrite (M0_set_add l wds q dd Hdf Hid Hok ltac:(lia)
                 ltac:(first [exact Hddb | rewrite Hqi; exact Hddb | rewrite <- Hqi; exact Hddb])).
      cbn [fst snd]. apply M0_st_add. }
    rewrite M0_dds_snoc. cancel. }
  { (* referenced, the set unchanged (memory) *)
    rewrite Her.
    apply semax_if_seq. forward_if; [ | exfalso; m0_kill ].
    forward. forward.
    Exists (Zlength l + 1) 1 (l ++ [(q, dd)]) st'.
    entailer!.
    { rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. }
    rewrite M0_dds_snoc. cancel. }
Qed.

End Setup.
