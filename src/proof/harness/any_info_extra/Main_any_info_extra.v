(* The harness obligation of harness/any_info_extra.c under the decoder's API v3.
   A law added by a later revision of the contract: templates in any_info (src/proof/harness/any_info/). *)
Require Import VST.floyd.proofauto.
Require Export Zstd.proof.zstd.Spec_api6.
Require Export Zstd.proof.harness.any_info_extra.HOK_any_info_extra.
Require Zstd.proof.top.MainPre6.
Require Import Zstd.proof.harness.any_info.InfoLemmas.
Require Import Zstd.proof.harness.any_info_extra.InfoExtraLemmas.

Local Ltac expand_main_pre ::= idtac.

Notation ZCS := Zstd.proof.zstd.Base.CompSpecs.
Notation HCS := Zstd.proof.harness.any_info_extra.HOK_any_info_extra.CompSpecs.

(* main calls malloc/free, the env functions and these decoder functions *)
Definition G0 : funspecs :=
  [(_quickproof_malloc, @malloc_spec' HCS); (_quickproof_free, @free_spec' HCS);
   ZSTD_isError_spec; ZSTD_getFrameContentSize_spec; ZSTD_getDecompressedSize_aspec;
   ZSTD_getFrameHeader_spec; ZSTD_getFrameHeader_advanced_aspec;
   nondet_size_spec; @nondet_bytes_nn_spec HCS; gp_assert_spec; gp_assume_spec].

(* from the decoder's compspecs (the API specs) to the harness's (main) *)

#[local] Instance CCE_any_info_extra : change_composite_env ZCS HCS.
Proof. make_cs_preserve ZCS HCS. Defined.

Lemma cs_bytes sh n (v: list val) p :
  @data_at ZCS sh (tarray tuchar n) v p = @data_at HCS sh (tarray tuchar n) v p.
Proof. erewrite (@data_at_change_composite ZCS HCS CCE_any_info_extra sh (tarray tuchar n) v v); [reflexivity | apply JMeq_refl | reflexivity]. Qed.

Lemma cs_bytes_d sh n (v: list val) p :
  @data_at HCS sh (tarray tuchar n) v p |-- @data_at Zstd.units.Zstd.CS sh (tarray tuchar n) v p.
Proof. rewrite <- cs_bytes. apply derives_refl. Qed.

Lemma cs_fh_pres : cs_preserve_type ZCS HCS (@coeq _ _ CCE_any_info_extra) t_fh = true.
Proof. vm_compute. reflexivity. Qed.

Lemma cs_fh_ sh p : @data_at_ ZCS sh t_fh p = @data_at_ HCS sh t_fh p.
Proof. erewrite (@data_at__change_composite ZCS HCS CCE_any_info_extra sh t_fh); [reflexivity | apply cs_fh_pres]. Qed.

Lemma cs_fh sh (v: @reptype ZCS t_fh) p : @data_at ZCS sh t_fh v p = @data_at HCS sh t_fh v p.
Proof. erewrite (@data_at_change_composite ZCS HCS CCE_any_info_extra sh t_fh v v); [reflexivity | apply JMeq_refl | apply cs_fh_pres]. Qed.

Lemma ltu_Z x y : 0 <= x <= Int64.max_unsigned -> 0 <= y <= Int64.max_unsigned ->
  Int64.ltu (Int64.repr x) (Int64.repr y) = (x <? y).
Proof.
  intros. unfold Int64.ltu. rewrite !Int64.unsigned_repr by lia.
  destruct (zlt x y); symmetry; [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Qed.

Lemma assume_le x m : 0 <= x <= Int64.max_unsigned -> 0 <= m <= Int64.max_unsigned ->
  Int.repr (if Int64.ltu (Int64.repr m) (Int64.repr x) then 0 else 1) <> Int.zero -> x <= m.
Proof.
  intros Hx Hm H. rewrite ltu_Z in H by lia.
  destruct (m <? x) eqn:E; [contradiction H; reflexivity | apply Z.ltb_ge in E; lia].
Qed.

Lemma iserr_false r : Int.repr (if is_error_code r then 1 else 0) = Int.zero -> is_error_code r = false.
Proof. destruct (is_error_code r); auto; intro H; inv H. Qed.

Lemma repr64_inj x y : 0 <= x <= Int64.max_unsigned -> 0 <= y <= Int64.max_unsigned ->
  Int64.repr x = Int64.repr y -> x = y.
Proof.
  intros Hx Hy H. apply (f_equal Int64.unsigned) in H.
  rewrite !Int64.unsigned_repr in H by lia. exact H.
Qed.

Lemma eq64_Z x y : 0 <= x <= Int64.max_unsigned -> 0 <= y <= Int64.max_unsigned ->
  Int64.eq (Int64.repr x) (Int64.repr y) = (x =? y).
Proof.
  intros Hx Hy. unfold Int64.eq. rewrite !Int64.unsigned_repr by lia.
  destruct (zeq x y); symmetry; [apply Z.eqb_eq | apply Z.eqb_neq]; auto.
Qed.

Lemma repr64_neg k : Int64.repr (- k) = Int64.repr (2 ^ 64 - k).
Proof. apply Int64.eqm_samerepr. exists (-1). rewrite Int64.modulus_power. change (two_p Int64.zwordsize) with (2 ^ 64). lia. Qed.

(* the source buffer: malloc'd with max 1 n bytes, of which nondet_bytes fills n *)
Lemma src_split (n m: Z) p : 0 <= n <= m -> field_compatible (tarray tuchar m) [] p ->
  @data_at_ HCS Ews (tarray tuchar m) p =
  (@data_at_ HCS Ews (tarray tuchar n) p *
   @data_at_ HCS Ews (tarray tuchar (m - n)) (field_address0 (tarray tuchar m) [ArraySubsc n] p))%logic.
Proof.
  intros Hn Hf. apply split2_data_at__Tarray_tuchar; auto.
Qed.

Lemma src_join (n m: Z) (v: list val) p : 0 <= n <= m -> field_compatible (tarray tuchar m) [] p ->
  (@data_at HCS Ews (tarray tuchar n) v p *
   @data_at_ HCS Ews (tarray tuchar (m - n)) (field_address0 (tarray tuchar m) [ArraySubsc n] p))%logic
  |-- @data_at_ HCS Ews (tarray tuchar m) p.
Proof.
  intros Hn Hf. rewrite (src_split n m p) by auto. cancel.
Qed.

(* the decoder's two readings of the header (getFrameHeader, getFrameHeader_advanced with ZSTD_f_zstd1) agree *)
Lemma fh_same s r r2 v0 v v2 :
  fh_post s r v0 v -> fh_post_m false s r2 v0 v2 -> r2 = r /\ (r = 0 -> v2 = v).
Proof.
  unfold fh_post, fh_post_m. change (get_frame_header_m false s) with (get_frame_header s). change (starting_len false) with 5.
  destruct (get_frame_header s) as [|k|h].
  - intros [[H1 _] [E1 _]] [_ [E2 _]]. split.
    + congruence.
    + intros ->. unfold is_error_code in H1. apply Z.ltb_lt in H1. lia.
  - intros [-> ->] [-> ->]. auto.
  - intros [-> ->] [-> ->]. auto.
Qed.

(* getFrameHeader returned 0: the struct holds a parsed header *)
Lemma fh_post_zero s v0 v : fh_post s 0 v0 v -> exists h, v = fh_val h.
Proof.
  unfold fh_post. destruct (get_frame_header s) as [|k|h] eqn:E.
  - intros [[H _] _]. discriminate H.
  - intros [Hk _]. subst k. apply IL_gfh_more in E. pose proof (IE_Zlength_nonneg s). lia.
  - intros [_ ->]. eauto.
Qed.

(* getFrameHeader_advanced(ZSTD_f_zstd1_magicless): 0 with headerSize <= srcSize, or > srcSize, or an error *)
Lemma fhm_zero s v0 v : fh_post_m true s 0 v0 v -> exists h, v = fh_val h /\ 1 <= fh_headerSize h <= Zlength s.
Proof.
  unfold fh_post_m. destruct (get_frame_header_m true s) as [|k|h] eqn:E.
  - intros [[H _] _]. discriminate H.
  - intros [Hk _]. subst k. apply IE_gfhm_more in E. pose proof (IE_Zlength_nonneg s). lia.
  - intros [_ ->]. apply IE_gfhm_ok in E. eauto.
Qed.

Lemma fhm_nonzero s r v0 v : fh_post_m true s r v0 v -> r <> 0 -> is_error_code r = false -> Zlength s < r.
Proof.
  unfold fh_post_m. destruct (get_frame_header_m true s) as [|k|h] eqn:E.
  - intros [[H _] _] _ H'. congruence.
  - intros [-> _] _ _. apply IE_gfhm_more in E. lia.
  - intros [-> _] H. contradiction.
Qed.

Lemma make_tycontext_g_isSome (V: varspecs) (G: funspecs) i :
  In i (map fst V) -> isSome (Maps.PTree.get i (make_tycontext_g V G)).
Proof.
  intros Hi. unfold make_tycontext_g.
  induction G as [|[j fs] G IH]; simpl.
  - induction V as [|[k t] V IHV]; simpl in *; [contradiction|].
    rewrite Maps.PTree.gsspec. destruct (peq i k); [exact Logic.I|]. apply IHV. destruct Hi; [congruence|auto].
  - rewrite Maps.PTree.gsspec. destruct (peq i j); [exact Logic.I|]. exact IH.
Qed.

Lemma vars_in_Vprog (G: funspecs) :
  Forall (fun ig : ident * globvar type => isSome (Maps.PTree.get (fst ig) (make_tycontext_g Vprog G)))
    (QPprog_vars Zstd.contracts.x_any_info_extra.whole_prog).
Proof.
  apply Forall_forall. intros [i v] Hin. apply make_tycontext_g_isSome.
  unfold Vprog, QPvarspecs. rewrite map_map.
  apply in_map_iff. exists (i, v). split; [reflexivity | exact Hin].
Qed.

(* main's precondition: the decoder's globals (MainPre6) *)
Lemma pre_globals gv : globals_ok gv ->
  InitGPred (Vardefs Zstd.contracts.x_any_info_extra.whole_prog) gv |-- zstd_globals gv * TT.
Proof.
  intros Hgv. eapply derives_trans.
  - apply (Zstd.proof.top.MainPre6.main_pre_fact6 Zstd.contracts.x_any_info_extra.whole_prog); [|exact Hgv].
    unfold Zstd.proof.top.MainPre6.all_progs. do 14 right. left. reflexivity.
  - apply sepcon_derives; [apply derives_refl | apply TT_right].
Qed.

Ltac eq_assert :=
  forward; forward; forward_call Int.one;
  [ entailer!; first [rewrite Int64.eq_true | rewrite Int.eq_true]; reflexivity | try deadvars! ].

Lemma body_main_G0 : semax_body Vprog G0 f_main main_spec.
Proof.
  change (semax_body Vprog G0 f_main (_main, WITH gv: globals PRE [] VST.floyd.VSU.main_pre
    Zstd.contracts.x_any_info_extra.whole_prog tt gv POST [tint] (fun _ : environ => TT))).
  replace (fun _ : environ => @TT mpred _) with (PROP () LOCAL () SEP (@TT mpred _))
    by (extensionality rho; unfold PROPx, LOCALx, SEPx; simpl; normalize).
  start_function1.
  eapply (main_pre_InitGpred (zstd_globals gv * TT)%logic).
  { apply pre_globals. }
  { reflexivity. }
  { apply vars_in_Vprog. }
  start_function3.
  sep_apply (create_mem_mgr gv).
  forward_call tt.
  Intros n.
  forward_call (Int.repr (if Int64.ltu (Int64.repr 4096) (Int64.repr n) then 0 else 1)).
  1: entailer!; simpl; destruct (Int64.ltu _ _); reflexivity.
  match goal with H: Int.repr _ <> Int.zero |- _ => apply assume_le in H; [|rep_lia|rep_lia] end.
  forward_if (PROP () LOCAL (temp _t'2 (Vlong (Int64.repr (Z.max 1 n))); temp _n (Vlong (Int64.repr n));
      lvar _h2 t_fh v_h2; lvar _h1 t_fh v_h1; gvars gv)
    SEP (mem_mgr gv; data_at_ Tsh t_fh v_h2; data_at_ Tsh t_fh v_h1; zstd_globals gv; TT; has_ext tt)).
  { forward. entailer!. rewrite !Int64.unsigned_repr in H1 by rep_lia. rewrite Z.max_r by lia. reflexivity. }
  { forward. entailer!. rewrite !Int64.unsigned_repr in H1 by rep_lia. rewrite Z.max_l by lia. reflexivity. }
  forward_call (tarray tuchar (Z.max 1 n), gv).
  { simpl. rep_lia. }
  Intros src.
  forward.
  forward_if (PROP (src <> nullval) LOCAL (temp _src src; temp _n (Vlong (Int64.repr n));
      lvar _h2 t_fh v_h2; lvar _h1 t_fh v_h1; gvars gv)
    SEP (mem_mgr gv; malloc_token Ews (tarray tuchar (Z.max 1 n)) src; data_at_ Ews (tarray tuchar (Z.max 1 n)) src;
      data_at_ Tsh t_fh v_h2; data_at_ Tsh t_fh v_h1; zstd_globals gv; TT; has_ext tt)).
  { if_tac; entailer!. }
  { forward. entailer!. }
  { forward. rewrite if_false by auto. entailer!. }
  Intros.
  assert_PROP (field_compatible (tarray tuchar (Z.max 1 n)) [] src) as Hfc by entailer!.
  rewrite (src_split n (Z.max 1 n) src) by (auto; lia). flatten_sepcon_in_SEP.
  forward_call (src, n, Ews).
  Intros bs.
  match goal with H: Zlength bs = n |- _ => subst n end.
  assert (Hbs: src_spec_pre Ews bs).
  { split; [auto|]. split; [rep_lia|]. eapply Forall_impl; [|eassumption]. intros b Hb; red; rep_lia. }
  rewrite <- cs_bytes.
  forward_call (gv, Ews, src, bs).
  forward_call (gv, Ews, src, bs).
  assert (Hbo: bytes_ok bs) by (destruct Hbs as [_ [_ ?]]; auto).
  pose proof (IE_fcs_range bs Hbo) as Hfr.
  rewrite (IE_ds bs Hbo).
  set (fcs := frame_content_size bs) in *.
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?S))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _t'6 (Vint (Int.repr
      (if orb (fcs =? ZSTD_CONTENTSIZE_UNKNOWN) (fcs =? ZSTD_CONTENTSIZE_ERROR) then 1 else 0))) :: L) (SEPx S))) end.
  { forward. entailer!.
    rewrite repr64_neg, eq64_Z in H2 by rep_lia. unfold ZSTD_CONTENTSIZE_UNKNOWN. rewrite H2. reflexivity. }
  { forward. entailer!.
    rewrite repr64_neg in H2. assert (fcs <> ZSTD_CONTENTSIZE_UNKNOWN) by (intro E; apply H2; rewrite E; reflexivity).
    unfold Int64.cmpu. rewrite repr64_neg, eq64_Z by rep_lia.
    unfold ZSTD_CONTENTSIZE_UNKNOWN, ZSTD_CONTENTSIZE_ERROR in *.
    destruct (Z.eqb_spec fcs (2 ^ 64 - 1)); [contradiction|].
    destruct (Z.eqb_spec fcs (2 ^ 64 - 2)); reflexivity. }
  match goal with |- semax _ (PROPx ?P (LOCALx (_ :: ?L) (SEPx ?S))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _t'7 (Vlong (Int64.repr
      (if orb (fcs =? ZSTD_CONTENTSIZE_UNKNOWN) (fcs =? ZSTD_CONTENTSIZE_ERROR) then 0 else fcs))) :: L) (SEPx S))) end.
  { forward. entailer!. destruct (orb _ _); [reflexivity | contradiction H2'; reflexivity]. }
  { forward. entailer!. destruct (orb _ _); [exfalso; apply Int.one_not_zero; exact H2 | reflexivity]. }
  forward_call Int.one.
  { entailer!. rewrite Int64.eq_true. reflexivity. }
  rewrite <- !cs_fh_.
  forward_call (gv, Tsh, v_h1, default_val t_fh, Ews, src, bs).
  { rewrite (@data_at__eq ZCS Tsh t_fh v_h1). cancel. }
  Intros vr. destruct vr as [r v1]. cbn [fst snd] in *.
  forward_call (gv, Tsh, v_h2, default_val t_fh, Ews, src, bs, 0).
  { rewrite (@data_at__eq ZCS Tsh t_fh v_h2). cancel. }
  Intros vr. destruct vr as [r2 v2]. cbn [fst snd] in *.
  change (0 =? 1) with false in *.
  match goal with H1: fh_post _ _ _ _, H2: fh_post_m _ _ _ _ _ |- _ =>
    destruct (fh_same _ _ _ _ _ _ H1 H2) as [-> Hv] end.
  forward_call Int.one.
  { entailer!. rewrite Int64.eq_true. reflexivity. }
  deadvars!.
  match goal with |- semax _ ?P _ _ => forward_if P end.
  { match goal with H: Int64.repr r = Int64.zero |- _ => apply (repr64_inj r 0) in H; [|rep_lia|rep_lia] end.
    subst r. specialize (Hv eq_refl). subst v2.
    destruct (fh_post_zero _ _ _ H4) as [h ->].
    rewrite !cs_fh.
    eq_assert. eq_assert. eq_assert. eq_assert. eq_assert. eq_assert. eq_assert.
    rewrite <- !cs_fh. entailer!. }
  { forward. entailer!. }
  forward_call (gv, Tsh, v_h2, v2, Ews, src, bs, 1).
  { rewrite <- (cs_bytes Ews (Zlength bs) (zbytes bs) src); cancel. }
  Intros vr. destruct vr as [r3 v3]. cbn [fst snd] in *.
  change (1 =? 1) with true in *.
  match goal with |- semax _ ?P _ _ => forward_if P end.
  { match goal with H: Int64.repr r3 = Int64.zero |- _ => apply (repr64_inj r3 0) in H; [|rep_lia|rep_lia] end.
    subst r3.
    match goal with H: fh_post_m true _ _ _ _ |- _ => destruct (fhm_zero _ _ _ H) as [h3 [-> Hh]] end.
    rewrite (cs_fh Tsh _ v_h2).
    forward.
    forward_call Int.one.
    { entailer!. rewrite ltu_Z by rep_lia.
      replace (Zlength bs <? fh_headerSize h3) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
    rewrite <- (cs_fh Tsh _ v_h2). entailer!. }
  { forward_call r3.
    destruct (is_error_code r3) eqn:Eerr.
    { forward_if; [exfalso; apply Int.one_not_zero; assumption | forward; entailer!]. }
    assert (Hgt: Zlength bs < r3).
    { eapply fhm_nonzero; [eassumption | | exact Eerr]. intro E; subst r3. apply H9; reflexivity. }
    forward_if.
    { forward_call Int.one.
      { entailer!. rewrite ltu_Z by rep_lia.
        replace (Zlength bs <? r3) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
      entailer!. }
    { match goal with H: Int.repr 0 <> Int.zero |- _ => contradiction H; reflexivity end. } }
  sep_apply (src_join (Zlength bs) (Z.max 1 (Zlength bs)) (zbytes bs) src ltac:(lia) Hfc).
  forward_call (tarray tuchar (Z.max 1 (Zlength bs)), src, gv).
  { rewrite if_false by auto. cancel. }
  rewrite !cs_fh.
  forward.
  unfold t_fh.
  sep_apply (@data_at_data_at_ HCS Tsh (Tstruct ___gp_ZSTD_FrameHeader noattr) v3 v_h2).
  sep_apply (@data_at_data_at_ HCS Tsh (Tstruct ___gp_ZSTD_FrameHeader noattr) v1 v_h1).
  cancel.
Qed.

(* From G0 to Gprog (Specs_api DC DD) []: every entry of G0 is found there unchanged *)
Definition G_env : funspecs := [nondet_size_spec; @nondet_bytes_nn_spec HCS; gp_assert_spec; gp_assume_spec].

Lemma Externals_eq : Externals = G_env.
Proof.
  unfold Externals, present, env_harness, filter.
  repeat match goal with |- context [id_in_list ?i ?l] =>
    let b := eval lazy in (id_in_list i l) in change (id_in_list i l) with b end.
  reflexivity.
Qed.

Lemma fid_false i (x: ident * funspec) l r :
  Pos.eqb (fst x) i = false -> initial_world.find_id i l = r -> initial_world.find_id i (x :: l) = r.
Proof.
  intros H1 H2. destruct x as [j f]. simpl in *. apply Pos.eqb_neq in H1.
  rewrite if_false by congruence. exact H2.
Qed.

Lemma fid_true i (x: ident * funspec) l :
  Pos.eqb (fst x) i = true -> initial_world.find_id i (x :: l) = Some (snd x).
Proof.
  intros H1. destruct x as [j f]. simpl in *. apply Pos.eqb_eq in H1. subst. rewrite if_true by auto. reflexivity.
Qed.

Lemma fid_inv i (x: ident * funspec) l fs :
  initial_world.find_id i (x :: l) = Some fs -> (fst x = i /\ fs = snd x) \/ initial_world.find_id i l = Some fs.
Proof.
  destruct x as [j f]. simpl. intros H.
  destruct (Memory.EqDec_ident i j) as [->|Hn]; [left; inv H; auto | right; exact H].
Qed.

Ltac fid_walk :=
  repeat first [ apply fid_false; [reflexivity |] | apply fid_true; reflexivity ].

Lemma G0_in_Gprog DC DD : forall i fs, initial_world.find_id i G0 = Some fs ->
  initial_world.find_id i (Gprog (Specs_api DC DD) []) = Some fs.
Proof.
  intros i fs E. unfold G0 in E.
  repeat (apply fid_inv in E; destruct E as [[<- ->]|E]);
    [.. | discriminate];
  unfold Gprog, Imports; rewrite Externals_eq; unfold Specs_api, G_env; cbn [app]; fid_walk.
Qed.

Lemma make_tycontext_g_find (Vs: varspecs) (G: funspecs) i :
  Maps.PTree.get i (make_tycontext_g Vs G) =
  match initial_world.find_id i G with Some fs => Some (type_of_funspec fs) | None => Maps.PTree.get i (make_tycontext_g Vs nil) end.
Proof.
  induction G as [|[j fs] G IH]; simpl; auto.
  rewrite Maps.PTree.gsspec. unfold make_tycontext_g in IH |- *. simpl in IH.
  destruct (peq i j) as [->|Hne].
  - rewrite if_true by reflexivity. reflexivity.
  - rewrite if_false by exact Hne. exact IH.
Qed.

Lemma mtg_none (V: varspecs) i : ~ In i (map fst V) -> Maps.PTree.get i (make_tycontext_g V []) = None.
Proof.
  unfold make_tycontext_g. induction V as [|[k t] V IH]; simpl; intros Hn.
  - apply Maps.PTree.gempty.
  - rewrite Maps.PTree.gsspec. destruct (peq i k); [subst; tauto |]. apply IH. tauto.
Qed.

(* no function name of Gprog is a global variable of the program *)
Lemma Gprog_not_var DC DD i : In i (map fst (Gprog (Specs_api DC DD) [])) -> ~ In i (map fst Vprog).
Proof.
  intros Hin Hv.
  assert (Hb: forallb (fun j => negb (id_in_list j (map fst Vprog))) (map fst (Gprog (Specs_api DC DD) [])) = true).
  { match goal with |- forallb ?f ?l = true => let L := eval lazy in l in change l with L end.
    vm_compute. reflexivity. }
  rewrite forallb_forall in Hb. specialize (Hb i Hin).
  rewrite (Zstd.proof.top.MainPre6.MP_id_in_list_true_i i _ Hv) in Hb. discriminate.
Qed.

Theorem any_info_extra_ok :
  forall (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred),
    exists Hs, HarnessOK (Specs_api DC DD) Hs.
Proof.
  intros DC DD. exists []. split.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    exists f_main. split; [reflexivity|]. split; [reflexivity|].
    eapply semax_body_subsumption; [apply body_main_G0 |].
    apply tycontext_sub_i99. split; intro i.
    + rewrite (make_tycontext_g_find Vprog G0 i).
      remember (Gprog (Specs_api DC DD) []) as GP eqn:HGP. (* abstract while rewriting: no comparison with [] by computation *)
      rewrite (make_tycontext_g_find Vprog GP i). subst GP.
      destruct (initial_world.find_id i G0) as [fs|] eqn:E.
      * rewrite (G0_in_Gprog DC DD i fs E). apply sub_option_refl.
      * destruct (initial_world.find_id i (Gprog (Specs_api DC DD) [])) as [fs'|] eqn:E'.
        -- rewrite mtg_none; [exact Logic.I |].
           apply (Gprog_not_var DC DD i).
           apply initial_world.find_id_e in E'. apply (in_map fst) in E'. exact E'.
        -- apply sub_option_refl.
    + rewrite !semax_prog.find_id_maketycontext_s.
      destruct (initial_world.find_id i G0) as [fs|] eqn:E; [|exact Logic.I].
      rewrite (G0_in_Gprog DC DD i fs E). exists fs. split; [reflexivity|]. apply funspec_sub_si_refl.
Qed.
