(* MainOK of the unit valid_dict_api: the main of the new harness valid_dict_api (added by a later revision of the
   contract) against API v3.  The segments are in VDA3*.v (VDA3Defs.v: their interface); here: the
   allocation check and the dictionary's copy (VDA_B -> VDA_A), the composition, and the lift from VDA_G1 to G0. *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.harness.valid_dict_api.WTopSpecs_valid_dict_api.
Require Import Zstd.proof.harness.valid_dict_api.VDA3Defs.
Require Import Zstd.proof.harness.valid_dict_api.VDA3Pro.
Require Import Zstd.proof.harness.valid_dict_api.VDA3Epi.
Require Import Zstd.proof.harness.valid_dict_api.VDA3M0.
Require Import Zstd.proof.harness.valid_dict_api.VDA3M0Model.
Require Import Zstd.proof.harness.valid_dict_api.VDA3M12.
Require Import Zstd.proof.harness.valid_dict_api.VDA3M34.
Require Import Zstd.proof.harness.valid_dict_api.VDA3M56.
Require Zstd.proof.top.MainPre6.

Local Notation ZCS := Zstd.proof.zstd.Base.CompSpecs.
Local Notation HCS := Zstd.proof.harness.valid_dict_api.HOK_valid_dict_api.CompSpecs.

Ltac kill :=
  match goal with
  | H: false = true |- _ => discriminate H
  | H: true = false |- _ => discriminate H
  | H: ?x <> ?x |- _ => exfalso; exact (H eq_refl)
  | H: Int.repr ?x = Int.repr ?y |- _ =>
      exfalso; apply repr_inj_unsigned in H; [lia | rep_lia | rep_lia]
  | H: Int.repr ?x = Int.zero |- _ =>
      exfalso; change Int.zero with (Int.repr 0) in H; apply repr_inj_unsigned in H; [lia | rep_lia | rep_lia]
  | H: typed_true _ _ |- _ => inv H
  | H: typed_false _ _ |- _ => inv H
  end.

Ltac vda_ptr x Hx PN :=
  match type of Hx with
  | x = nullval => subst x
  | x <> nullval => destruct x; simpl in PN; try contradiction; try (subst; exfalso; apply Hx; reflexivity)
  end.

Ltac vda_if := first [rewrite if_true by auto | rewrite if_false by discriminate].

Tactic Notation "vda_ent" tactic(t) := match goal with |- _ |-- _ => t | _ => idtac end.

Ltac ifs := repeat apply -> seq_assoc; apply semax_if_seq; forward_if; try solve [kill | exfalso; lia].

(* ---------- helpers for the copy of the dictionary (after valid_dict's v2 main) ---------- *)

Lemma VDA_split_bytes_ {cs: compspecs} sh m k p : 0 <= k <= m -> field_compatible (tarray tuchar m) [] p ->
  data_at_ sh (tarray tuchar m) p =
  (data_at_ sh (tarray tuchar k) p * data_at_ sh (tarray tuchar (m - k)) (offset_val k p))%logic.
Proof.
  intros Hk Hf. unfold tarray. rewrite (split2_data_at__Tarray_tuchar sh m k p Hk) by auto with field_compatible.
  rewrite field_address0_offset by auto with field_compatible. simpl. rewrite Z.mul_1_l, Z.add_0_l. reflexivity.
Qed.

Lemma VDA_Zrepeat {cs: compspecs} sh c p :
  data_at_ sh (tarray tuchar c) p = data_at sh (tarray tuchar c) (Zrepeat Vundef c) p.
Proof. unfold data_at_, field_at_, data_at. reflexivity. Qed.

Lemma VDA_content_at (c: list Z) k i : 0 <= i < Zlength c ->
  Znth i (zbytes c ++ Zrepeat (Vint Int.zero) k) = Vint (Int.repr (Znth i c)).
Proof.
  intros Hi. rewrite app_Znth1 by (rewrite Zlength_map; lia). rewrite Znth_map by lia. reflexivity.
Qed.

Lemma VDA_copy_step (b: list Z) i n : 0 <= i < n -> Zlength b = n ->
  upd_Znth i (zbytes (sublist 0 i b) ++ Zrepeat Vundef (n - i)) (Vint (Int.repr (Znth i b))) =
  zbytes (sublist 0 (i + 1) b) ++ Zrepeat Vundef (n - (i + 1)).
Proof.
  intros Hi Hn.
  rewrite upd_Znth_app2 by (rewrite Zlength_map, Zlength_sublist, Zlength_Zrepeat; lia).
  rewrite Zlength_map, Zlength_sublist by lia. replace (i - (i - 0)) with 0 by lia.
  replace (n - i) with (1 + (n - (i + 1))) by lia.
  rewrite <- Zrepeat_app by lia. rewrite upd_Znth_app1 by (rewrite Zlength_Zrepeat; lia).
  change (Zrepeat Vundef 1) with [Vundef]. rewrite upd_Znth0.
  rewrite (sublist_split 0 i (i + 1) b) by lia. rewrite map_app, <- app_assoc.
  rewrite sublist_len_1 by lia. reflexivity.
Qed.

(* vd_wd[k] out of the list of the dictionaries *)
Lemma VDA_wds_split WDS gv l : forall i k w, nth_error l k = Some w ->
  vda_wds_from WDS gv i l =
  (vda_wds_from WDS gv i (firstn k l) *
   (wdict_rep WDS Ews w (vda_wd_addr gv (i + Z.of_nat k)) * vda_wds_from WDS gv (i + Z.of_nat k + 1) (skipn (S k) l)))%logic.
Proof.
  induction l as [|x l IH]; intros i k w Hk; [destruct k; discriminate|].
  destruct k as [|k]; simpl in Hk |- *.
  - inv Hk. rewrite Z.add_0_r, emp_sepcon. reflexivity.
  - rewrite (IH (i + 1) k w Hk). rewrite sepcon_assoc.
    replace (i + 1 + Z.of_nat k) with (i + Z.pos (Pos.of_succ_nat k)) by lia. reflexivity.
Qed.

(* the bytes field of a wdict_t, and the rest *)
Definition VDA_wd_rest (wd: wdict) (p: val) (stv: reptype t_wstate) : mpred := (
  @field_at HCS Ews t_wdict (DOT _n) (vl (Zlength (wd_bytes wd))) p *
  @field_at HCS Ews t_wdict (DOT _formatted) (vb (wd_formatted wd)) p *
  @field_at HCS Ews t_wdict (DOT _id) (vu (wd_id wd)) p *
  @field_at HCS Ews t_wdict (DOT _content) (offset_val (Zlength (wd_bytes wd) - Zlength (wd_content wd)) p) p *
  @field_at HCS Ews t_wdict (DOT _content_n) (vl (Zlength (wd_content wd))) p *
  @field_at HCS Ews t_wdict (DOT _x_valid_dict_api__st) stv p * spacer Ews 13980 13984 p)%logic.

Lemma VDA_wd_fields wd p stv :
  @data_at HCS Ews t_wdict (wdict_val wd p stv) p =
  (@field_at HCS Ews t_wdict (DOT _bytes) (zbytes (wd_bytes wd) ++ Zrepeat (Vint Int.zero) (6144 - Zlength (wd_bytes wd))) p *
   VDA_wd_rest wd p stv)%logic.
Proof.
  unfold VDA_wd_rest. unfold_data_at (data_at _ _ _ p). cbn [fst snd wdict_val].
  apply pred_ext; cancel.
Qed.

(* ---------- the allocation check, the copy, the modes, the epilogue ---------- *)

Section Body.
Variable DC : globals -> val -> dctx_st -> mpred.
Variable DD : globals -> val -> ddict_st -> mpred.
Variable WG : globals -> mpred.
Variable WDS : wdict -> reptype t_wstate -> Prop.

Lemma VDA_cont (Espec: OracleKind) gv v_dd mode nd which wds wd ws cap src buf dctx :
  @semax HCS Espec (VDA_Delta DC DD WG WDS) (VDA_B DC WDS gv v_dd mode nd which wds wd ws cap src buf dctx)
    (Ssequence VDA_rest_s (Sreturn (Some (Econst_int (Int.repr 0) tint)))) VDA_R.
Proof.
  rewrite VDA_rest_eq. unfold VDA_B.
  apply semax_seq with (Q := FF); [| apply semax_ff].
  Intros.
  unfold VDA_Delta, VDA_R. abbreviate_semax.
  assert (Hvp: forall (P: mpred) q, (P && valid_pointer q) |-- P) by (intros; apply andp_left1, derives_refl).
  destruct (eq_dec src nullval) as [Hs|Hs]; destruct (eq_dec buf nullval) as [Hb|Hb];
    destruct (eq_dec dctx nullval) as [Hd|Hd].
  all: try (assert (Hfail: src = nullval \/ buf = nullval \/ dctx = nullval) by tauto).
  all: vda_ptr src Hs PNsrc; vda_ptr buf Hb PNbuf; vda_ptr dctx Hd PNdctx; Intros.
  1-7: repeat (first [ifs | forward]).
  1-7: (match goal with |- context [temp _src ?s] =>
          forward_call (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws))), s, gv) end).
  all: vda_ent (vda_if; cancel).
  1-7: (match goal with |- context [temp _buf ?b] =>
          forward_call (tarray tuchar (cap + 1 + Zlength (wd_bytes wd)), b, gv) end).
  all: vda_ent (vda_if; cancel).
  1-7: (match goal with |- context [temp _dctx ?d] =>
          forward_call (gv, d, if eq_dec d nullval then None else Some dctx_init) end).
  all: vda_ent (try (match goal with |- context [eq_dec ?d nullval] => destruct (eq_dec d nullval) end);
          first [contradiction | discriminate
                | (match goal with |- context [andp (DC ?g ?d dctx_init) (valid_pointer ?d)] =>
                     sep_apply (Hvp (DC g d dctx_init) d); cancel end)
                | (simpl; entailer!)]).
  1-7: forward.
  1-7: (sep_apply (data_at_data_at_ Tsh t_ddp (Zrepeat nullval 3) v_dd); cancel).
  (* every allocation succeeded *)
  rename b into bs, i into os, b0 into bb, i0 into ob, b1 into bd, i1 into od.
  repeat (first [ifs | forward]).
  sep_apply (Hvp (DC gv (Vptr bd od) dctx_init) (Vptr bd od)).
  pose proof H as Hfacts.
  destruct H as (Hm & Hnd & Hndr & Hwh & Hwh0 & Hnth & Hdf & Hwf & Hm0 & Hm134 & Hm2 & Hsf & Hww & Hm0f & Hm4 & Hm56 & Hcap & Hdwin).
  assert (Hdfw: dict_facts wd) by (eapply Forall_forall; [exact Hdf | eapply nth_error_In; exact Hnth]).
  pose proof Hdfw as (Hbok & Hdl & _).
  rewrite (VDA_wds_split WDS gv wds 0 (Z.to_nat which) wd Hnth).
  rewrite Z.add_0_l, Z2Nat.id by lia.
  unfold wdict_rep at 1. Intros stv.
  rewrite VDA_wd_fields.
  assert_PROP (field_compatible (tarray tuchar (cap + 1 + Zlength (wd_bytes wd))) [] (Vptr bb ob)) as Hfb.
  { entailer!. }
  rewrite (VDA_split_bytes_ Ews (cap + 1 + Zlength (wd_bytes wd)) (cap + 1) (Vptr bb ob)) by (auto; rep_lia).
  replace (cap + 1 + Zlength (wd_bytes wd) - (cap + 1)) with (Zlength (wd_bytes wd)) by lia.
  rewrite (VDA_Zrepeat Ews (Zlength (wd_bytes wd))).
  Intros.
  freeze [0;1;2;3;4;6;7;8;9;10;11;13;14] FR1.
  unfold VDA_copy_s. forward.
  match goal with |- semax _ (PROPx _ (LOCALx (_ :: ?L) (SEPx (?F :: ?B :: _ :: nil)))) _ _ =>
    forward_loop (EX i: Z, PROPx [0 <= i <= Zlength (wd_bytes wd)] (LOCALx (temp _j (Vlong (Int64.repr i)) :: L)
         (SEPx [F; B; data_at Ews (tarray tuchar (Zlength (wd_bytes wd))) (zbytes (sublist 0 i (wd_bytes wd)) ++ Zrepeat Vundef (Zlength (wd_bytes wd) - i)) (offset_val (cap + 1) (Vptr bb ob))])))
      continue: (EX i: Z, PROPx [0 <= i < Zlength (wd_bytes wd)] (LOCALx (temp _j (Vlong (Int64.repr i)) :: L)
         (SEPx [F; B; data_at Ews (tarray tuchar (Zlength (wd_bytes wd))) (zbytes (sublist 0 (i + 1) (wd_bytes wd)) ++ Zrepeat Vundef (Zlength (wd_bytes wd) - (i + 1))) (offset_val (cap + 1) (Vptr bb ob))])))
      break: (PROPx [] (LOCALx (temp _j (Vlong (Int64.repr (Zlength (wd_bytes wd)))) :: L)
         (SEPx [F; B; data_at Ews (tarray tuchar (Zlength (wd_bytes wd))) (zbytes (wd_bytes wd)) (offset_val (cap + 1) (Vptr bb ob))])))
  end.
  { Exists 0. entailer!. simpl app. cancel. }
  { Intros i. ifs.
    1: assert (Hbi: is_byte (Znth i (wd_bytes wd))) by (apply Forall_Znth; auto; lia).
    1: unfold is_byte in Hbi.
    1: forward.
    1: { entailer!. rewrite VDA_content_at by lia. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    1: rewrite VDA_content_at by lia.
    1: forward.
    1: Exists i. 1: entailer!.
    1: rewrite (VDA_copy_step (wd_bytes wd) i (Zlength (wd_bytes wd))) by (auto; lia). 1: cancel.
    assert (Hin: i = Zlength (wd_bytes wd)) by lia. subst i.
    forward. entailer!. rewrite sublist_same by lia. rewrite Z.sub_diag. simpl. rewrite app_nil_r. cancel. }
  { Intros i. forward. Exists (i + 1). entailer!. }
  thaw FR1.
  assert (Hmok: VDA_mode_ok DC DD WG WDS mode).
  { assert (mode = 0 \/ mode = 1 \/ mode = 2 \/ mode = 3 \/ mode = 4 \/ mode = 5 \/ mode = 6) as Hc by lia.
    destruct Hc as [->|[->|[->|[->|[->|[->| ->]]]]]].
    - apply vda_mode0_ok, vda_m0_model.
    - apply vda_mode12_ok. - apply vda_mode12_ok. - apply vda_mode34_ok. - apply vda_mode34_ok.
    - apply vda_mode56_ok. - apply vda_mode56_ok. }
  unfold MORE_COMMANDS, abbreviate.
  apply <- seq_assoc.
  eapply semax_seq'.
  { eapply semax_pre; [| apply (Hmok Espec gv v_dd nd which wds wd ws cap (Vptr bs os) (Vptr bb ob) (Vptr bd od))].
    unfold VDA_A.
    rewrite (VDA_wds_split WDS gv wds 0 (Z.to_nat which) wd Hnth).
    rewrite Z.add_0_l, Z2Nat.id by lia.
    unfold wdict_rep at 1. Exists stv. rewrite VDA_wd_fields.
    assert_PROP (field_compatible (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws)))) [] (Vptr bs os)) by entailer!.
    entailer!. }
  Intros st ddv.
  unfold POSTCONDITION, abbreviate.
  eapply semax_post; [| | | | apply (vda_epi_ok DC DD WG WDS Espec)].
  all: try (intros; simpl; normalize; fail).
  intros vl. unfold VDA_R. simpl RA_return. apply andp_left2, derives_refl.
Qed.

End Body.

Lemma VDA_body_main DC DD WG WDS (HWG: forall gv, InitGPred wvardefs gv |-- WG gv) :
  semax_body Vprog (VDA_G1 DC DD WG WDS) f_main main_spec.
Proof. apply (vda_pro_ok DC DD WG WDS HWG). intros. apply VDA_cont. Qed.

(* ---------- from VDA_G1 to G0 (Specs_api DC DD) (wtop_specs ..): every entry of VDA_G1 is found there unchanged ---------- *)

Lemma VDA_Externals : Externals = [nondet_u32_spec; gp_assert_spec; gp_assume_spec].
Proof.
  unfold Externals, present, env_harness, filter.
  repeat match goal with |- context [id_in_list ?i ?l] =>
    let b := eval lazy in (id_in_list i l) in change (id_in_list i l) with b end.
  reflexivity.
Qed.

Lemma VDA_make_tycontext_g_find (Vs: varspecs) (G: funspecs) i :
  Maps.PTree.get i (make_tycontext_g Vs G) =
  match initial_world.find_id i G with Some fs => Some (type_of_funspec fs) | None => Maps.PTree.get i (make_tycontext_g Vs nil) end.
Proof.
  induction G as [|[j fs] G IH]; simpl; auto.
  rewrite Maps.PTree.gsspec. unfold make_tycontext_g in IH |- *. simpl in IH.
  destruct (peq i j) as [->|Hne].
  - rewrite if_true by reflexivity. reflexivity.
  - rewrite if_false by exact Hne. exact IH.
Qed.

Lemma VDA_G1_in DC DD WG WDS i fs : initial_world.find_id i (VDA_G1 DC DD WG WDS) = Some fs ->
  initial_world.find_id i (G0 (Specs_api DC DD) (wtop_specs DC DD WG WDS)) = Some fs.
Proof.
  intros Hi.
  assert (Hin: In i [_quickproof_malloc; _quickproof_free; _ZSTD_isError; _ZSTD_getErrorCode; _ZSTD_decompressDCtx;
     _ZSTD_createDCtx; _ZSTD_freeDCtx; _ZSTD_DCtx_setParameter; _ZSTD_resetDStream;
     _ZSTD_createDDict; _ZSTD_freeDDict; _ZSTD_DCtx_refDDict;
     _ZSTD_DCtx_loadDictionary_advanced; _ZSTD_DCtx_refPrefix_advanced;
     _ZSTD_initDStream_usingDict; _ZSTD_initDStream_usingDDict; _gp_assert; _gp_assume;
     _choose; _choose_in; _exact_copy; _within_oneshot; _w_dict; _w_series; _vd_stream]).
  { apply initial_world.find_id_e in Hi. apply (in_map fst) in Hi. exact Hi. }
  unfold G0, Imports. rewrite VDA_Externals.
  repeat destruct Hin as [<-|Hin]; try contradiction; rewrite <- Hi; reflexivity.
Qed.

Lemma VDA_find_id_not_in {A} i (l: list (ident * A)) : ~ In i (map fst l) -> initial_world.find_id i l = None.
Proof.
  induction l as [|[j x] l IH]; simpl; intros H; auto.
  rewrite if_false by (intro; subst; tauto). apply IH; tauto.
Qed.

Lemma VDA_tyc_g_nil_in (V: varspecs) i t : Maps.PTree.get i (make_tycontext_g V nil) = Some t -> In i (map fst V).
Proof.
  unfold make_tycontext_g. simpl. induction V as [|[k u] V IH]; simpl.
  - rewrite Maps.PTree.gempty. discriminate.
  - rewrite Maps.PTree.gsspec. destruct (peq i k); auto.
Qed.

Definition VDA_fun_ids : list ident := ltac:(
  let l := eval lazy [G0 Imports Externals present env_harness filter map fst Specs_api wtop_specs id_in_list
                      orb negb andb Pos.eqb] in (map fst (G0 (Specs_api (fun _ _ _ => emp) (fun _ _ _ => emp))
                         (wtop_specs (fun _ _ _ => emp) (fun _ _ _ => emp) (fun _ => emp) (fun _ _ => True)))) in
  exact l).

Lemma VDA_G0_ids DC DD WG WDS : map fst (G0 (Specs_api DC DD) (wtop_specs DC DD WG WDS)) = VDA_fun_ids.
Proof. unfold G0, Imports. rewrite VDA_Externals. reflexivity. Qed.

Lemma VDA_vars_funs_b : forallb (fun i => negb (id_in_list i VDA_fun_ids)) (map fst Vprog) = true.
Proof. reflexivity. Qed.

Lemma VDA_var_not_fun DC DD WG WDS i t : Maps.PTree.get i (make_tycontext_g Vprog nil) = Some t ->
  initial_world.find_id i (G0 (Specs_api DC DD) (wtop_specs DC DD WG WDS)) = None.
Proof.
  intros H. apply VDA_tyc_g_nil_in in H. apply VDA_find_id_not_in. rewrite VDA_G0_ids.
  pose proof VDA_vars_funs_b as B. rewrite forallb_forall in B. specialize (B i H).
  intro Hin. apply Zstd.proof.top.MainPre6.MP_id_in_list_true_i in Hin. rewrite Hin in B. discriminate.
Qed.

Theorem main_ok3_valid_dict_api : MainOK.
Proof.
  intros DC DD WG WDS HWG.
  eapply semax_body_subsumption; [apply (VDA_body_main DC DD WG WDS HWG) |].
  apply tycontext_sub_i99. split; intro i.
  + rewrite (VDA_make_tycontext_g_find Vprog (VDA_G1 DC DD WG WDS) i).
    destruct (initial_world.find_id i (VDA_G1 DC DD WG WDS)) as [fs|] eqn:E.
    * rewrite (VDA_make_tycontext_g_find Vprog (G0 (Specs_api DC DD) (wtop_specs DC DD WG WDS)) i).
      rewrite (VDA_G1_in DC DD WG WDS i fs E). apply sub_option_refl.
    * (* G0 is abstracted first: otherwise the rewrite tries to unify it with the [] on the left by computing it *)
      remember (G0 (Specs_api DC DD) (wtop_specs DC DD WG WDS)) as P eqn:EP.
      rewrite (VDA_make_tycontext_g_find Vprog P i). subst P.
      destruct (Maps.PTree.get i (make_tycontext_g Vprog [])) as [t|] eqn:EV; [|exact Logic.I].
      rewrite (VDA_var_not_fun DC DD WG WDS i t EV). reflexivity.
  + rewrite !semax_prog.find_id_maketycontext_s.
    destruct (initial_world.find_id i (VDA_G1 DC DD WG WDS)) as [fs|] eqn:E; [|exact Logic.I].
    rewrite (VDA_G1_in DC DD WG WDS i fs E). exists fs. split; [reflexivity|]. apply funspec_sub_si_refl.
Qed.
