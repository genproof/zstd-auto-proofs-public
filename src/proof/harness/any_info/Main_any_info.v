(* The harness obligation of any_info (harness/any_info.c): for ANY predicates DC, DD of the decoder's API
   (Spec_api6), specifications of the harness's helpers such that every helper and main satisfy them. *)
Require Import VST.floyd.proofauto.
Require Export Zstd.proof.zstd.Spec_api6.
Require Export Zstd.proof.harness.any_info.HOK_any_info.

Require Import Zstd.proof.harness.any_info.InfoLemmas.
Require Zstd.proof.top.MainPre6.

Local Ltac expand_main_pre ::= idtac.

Notation ZCS := Zstd.proof.zstd.Base.CompSpecs.
Notation HCS := Zstd.proof.harness.any_info.HOK_any_info.CompSpecs.

(* main calls malloc/free, the env functions and these decoder functions *)
Definition G0 : funspecs :=
  [(_quickproof_malloc, @malloc_spec' HCS); (_quickproof_free, @free_spec' HCS);
   ZSTD_isError_spec; ZSTD_findFrameCompressedSize_spec; ZSTD_getFrameContentSize_spec;
   ZSTD_findDecompressedSize_spec; ZSTD_decompressBound_spec; ZSTD_frameHeaderSize_spec;
   ZSTD_getDictID_fromFrame_spec; ZSTD_isFrame_spec; ZSTD_isSkippableFrame_spec;
   ZSTD_getFrameHeader_spec; ZSTD_readSkippableFrame_spec;
   nondet_size_spec; @nondet_bytes_nn_spec HCS; gp_assert_spec; gp_assume_spec].

(* from the decoder's compspecs (the API specs) to the harness's (main) *)

#[local] Instance CCE_any_info : change_composite_env ZCS HCS.
Proof. make_cs_preserve ZCS HCS. Defined.

Lemma cs_bytes sh n (v: list val) p :
  @data_at ZCS sh (tarray tuchar n) v p = @data_at HCS sh (tarray tuchar n) v p.
Proof. erewrite (@data_at_change_composite ZCS HCS CCE_any_info sh (tarray tuchar n) v v); [reflexivity | apply JMeq_refl | reflexivity]. Qed.

Lemma cs_bytes_ sh n p :
  @data_at_ ZCS sh (tarray tuchar n) p = @data_at_ HCS sh (tarray tuchar n) p.
Proof. erewrite (@data_at__change_composite ZCS HCS CCE_any_info sh (tarray tuchar n)); [reflexivity | reflexivity]. Qed.

Lemma cs_uint sh v p : @data_at ZCS sh tuint v p = @data_at HCS sh tuint v p.
Proof. erewrite (@data_at_change_composite ZCS HCS CCE_any_info sh tuint v v); [reflexivity | apply JMeq_refl | reflexivity]. Qed.

Lemma cs_uint_ sh p : @data_at_ ZCS sh tuint p = @data_at_ HCS sh tuint p.
Proof. erewrite (@data_at__change_composite ZCS HCS CCE_any_info sh tuint); [reflexivity | reflexivity]. Qed.

Lemma cs_fh_pres : cs_preserve_type ZCS HCS (@coeq _ _ CCE_any_info) t_fh = true.
Proof. vm_compute. reflexivity. Qed.

Lemma cs_fh_ sh p : @data_at_ ZCS sh t_fh p = @data_at_ HCS sh t_fh p.
Proof. erewrite (@data_at__change_composite ZCS HCS CCE_any_info sh t_fh); [reflexivity | apply cs_fh_pres]. Qed.

Lemma cs_fh sh (v: @reptype ZCS t_fh) p : @data_at ZCS sh t_fh v p = @data_at HCS sh t_fh v p.
Proof. erewrite (@data_at_change_composite ZCS HCS CCE_any_info sh t_fh v v); [reflexivity | apply JMeq_refl | apply cs_fh_pres]. Qed.

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

Lemma assert_le x m : 0 <= x <= Int64.max_unsigned -> 0 <= m <= Int64.max_unsigned -> x <= m ->
  Int.repr (if Int64.ltu (Int64.repr m) (Int64.repr x) then 0 else 1) <> Int.zero.
Proof.
  intros Hx Hm H. rewrite ltu_Z by lia.
  destruct (m <? x) eqn:E; [apply Z.ltb_lt in E; lia | discriminate].
Qed.

Lemma iserr_false r : Int.repr (if is_error_code r then 1 else 0) = Int.zero -> is_error_code r = false.
Proof. destruct (is_error_code r); auto; intro H; inv H. Qed.

Lemma iserr_true r : Int.repr (if is_error_code r then 1 else 0) <> Int.zero -> is_error_code r = true.
Proof. destruct (is_error_code r); auto; intro H; contradiction H; reflexivity. Qed.

Lemma repr64_zero k : 0 <= k <= Int64.max_unsigned -> Int64.repr k = Int64.zero -> k = 0.
Proof.
  intros Hk H. apply (f_equal Int64.unsigned) in H.
  rewrite Int64.unsigned_repr in H by lia. exact H.
Qed.

Lemma assert_lt x m : 0 <= x <= Int64.max_unsigned -> 0 <= m <= Int64.max_unsigned -> x < m ->
  Int.repr (if Int64.ltu (Int64.repr x) (Int64.repr m) then 1 else 0) <> Int.zero.
Proof.
  intros Hx Hm H. rewrite ltu_Z by lia.
  destruct (x <? m) eqn:E; [discriminate | apply Z.ltb_ge in E; lia].
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
    (QPprog_vars Zstd.contracts.x_any_info.whole_prog).
Proof.
  apply Forall_forall. intros [i v] Hin. apply make_tycontext_g_isSome.
  unfold Vprog, QPvarspecs. rewrite map_map.
  apply in_map_iff. exists (i, v). split; [reflexivity | exact Hin].
Qed.

(* main's precondition: the decoder's globals (MainPre6) *)
Lemma pre_globals gv : globals_ok gv ->
  InitGPred (Vardefs Zstd.contracts.x_any_info.whole_prog) gv |-- zstd_globals gv * TT.
Proof.
  intros Hgv. eapply derives_trans.
  - apply (Zstd.proof.top.MainPre6.main_pre_fact6 Zstd.contracts.x_any_info.whole_prog); [|exact Hgv].
    unfold Zstd.proof.top.MainPre6.all_progs. do 2 right. left. reflexivity.
  - apply sepcon_derives; [apply derives_refl | apply TT_right].
Qed.

Lemma body_main_G0 : semax_body Vprog G0 f_main main_spec.
Proof.
  change (semax_body Vprog G0 f_main (_main, WITH gv: globals PRE [] VST.floyd.VSU.main_pre
    Zstd.contracts.x_any_info.whole_prog tt gv POST [tint] (fun _ : environ => TT))).
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
  forward.
  forward_call (Int.repr (if Int64.ltu (Int64.repr 4096) (Int64.repr n) then 0 else 1)).
  1: entailer!; simpl; destruct (Int64.ltu _ _); reflexivity.
  match goal with H: Int.repr _ <> Int.zero |- _ => apply assume_le in H; [|rep_lia|rep_lia] end.
  forward_call (tarray tuchar n, gv).
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros src.
  forward_if (PROP (src <> nullval) LOCAL (temp _src src; temp _n (Vlong (Int64.repr n)); lvar _zfh t_fh v_zfh;
      lvar _variant tuint v_variant; gvars gv)
    SEP (data_at_ Tsh t_fh v_zfh; data_at Tsh tuint (Vint (Int.repr 0)) v_variant; mem_mgr gv; zstd_globals gv;
      malloc_token Ews (tarray tuchar n) src; data_at_ Ews (tarray tuchar n) src; TT)).
  { if_tac; entailer!. }
  { forward; entailer!. }
  { forward. rewrite if_false by auto. entailer!. }
  Intros.
  forward_call (src, n, Ews).
  Intros bs.
  forward_call tt.
  Intros cap.
  forward_call (Int.repr (if Int64.ltu (Int64.repr 65536) (Int64.repr cap) then 0 else 1)).
  1: entailer!; simpl; destruct (Int64.ltu _ _); reflexivity.
  match goal with H: Int.repr _ <> Int.zero |- _ => apply assume_le in H; [|rep_lia|rep_lia] end.
  forward_call (tarray tuchar cap, gv).
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros dst.
  forward_if (PROP (dst <> nullval) LOCAL (temp _dst dst; temp _cap (Vlong (Int64.repr cap)); temp _src src;
      temp _n (Vlong (Int64.repr n)); lvar _zfh t_fh v_zfh; lvar _variant tuint v_variant; gvars gv)
    SEP (data_at_ Tsh t_fh v_zfh; data_at Tsh tuint (Vint (Int.repr 0)) v_variant; mem_mgr gv; zstd_globals gv;
      malloc_token Ews (tarray tuchar n) src; data_at Ews (tarray tuchar n) (zbytes bs) src;
      malloc_token Ews (tarray tuchar cap) dst; data_at_ Ews (tarray tuchar cap) dst; TT)).
  { if_tac; entailer!. }
  { forward_call (tarray tuchar n, src, gv).
    { rewrite (if_false (src = nullval)) by auto. cancel. }
    forward; entailer!. }
  { forward. rewrite if_false by auto. entailer!. }
  Intros.
  subst n.
  assert (Hbs: src_spec_pre Ews bs).
  { split; [auto|]. split; [rep_lia|]. eapply Forall_impl; [|eassumption]. intros b Hb; red; rep_lia. }
  rewrite <- cs_bytes.
  forward_call (gv, Ews, src, bs).
  Intros r.
  forward_call r.
  match goal with |- semax _ ?P _ _ => forward_if P end.
  { match goal with H: Int.repr _ = Int.zero |- _ => apply iserr_false in H end.
    destruct (frame_compressed_size bs) as [k|] eqn:Ek; [subst r | congruence].
    apply IL_fcs_le in Ek.
    forward_call (Int.repr (if Int64.ltu (Int64.repr (Zlength bs)) (Int64.repr k) then 0 else 1)).
    1: entailer!; simpl; destruct (Int64.ltu _ _); reflexivity.
    1: match goal with H: _ = Int.zero |- False => revert H; apply assert_le; rep_lia end.
    entailer!. }
  { forward. entailer!. }
  rewrite <- cs_fh_.
  forward_call (gv, Tsh, v_zfh, default_val t_fh, Ews, src, bs).
  { rewrite data_at__eq. cancel. }
  Intros vr. destruct vr as [r2 v]. cbn [fst snd] in *.
  forward_call r2.
  match goal with |- semax _ ?P _ _ => forward_if P end.
  { match goal with H: Int.repr _ = Int.zero |- _ => apply iserr_false in H end.
    unfold fh_post in H9.
    destruct (get_frame_header bs) as [|k|h] eqn:Eg; [destruct H9 as [[H9 _] _]; congruence | destruct H9 as [-> _] | destruct H9 as [-> ->]].
    - apply IL_gfh_more in Eg.
      forward_if.
      + apply repr64_zero in H9; lia.
      + forward_call (Int.repr (if Int64.ltu (Int64.repr (Zlength bs)) (Int64.repr k) then 1 else 0)).
        1: match goal with H: _ = Int.zero |- False => revert H; apply assert_lt; rep_lia end.
        entailer!.
    - apply IL_gfh_ok in Eg.
      forward_if; [| match goal with H: Int64.repr 0 <> _ |- _ => contradiction H; reflexivity end].
      rewrite cs_fh.
      forward.
      forward_call (Int.repr (if Int64.ltu (Int64.repr (Zlength bs)) (Int64.repr (fh_headerSize h)) then 0 else 1)).
      1: entailer!; simpl; destruct (Int64.ltu _ _); reflexivity.
      1: match goal with H: _ = Int.zero |- False => revert H; apply assert_le; rep_lia end.
      rewrite <- cs_fh. entailer!. }
  { forward. entailer!. }
  rewrite <- cs_bytes.
  match goal with |- semax _ ?P _ _ => forward_if P end.
  { match goal with H: Int64.unsigned _ < Int64.unsigned _ |- _ => rewrite !Int64.unsigned_repr in H by rep_lia end.
    forward_call (Ews, src, bs).
    rewrite (IL_is_frame_small bs) by lia.
    forward_call Int.one.
    forward_call (Ews, src, bs).
    rewrite (IL_is_skippable_small bs) by lia.
    forward_call Int.one.
    entailer!. }
  { forward_call (Ews, src, bs).
    forward_call (Ews, src, bs).
    entailer!. }
  rewrite <- cs_bytes_, <- cs_uint.
  forward_call (Ews, dst, cap, Tsh, v_variant, Ews, src, bs).
  Intros vr. destruct vr as [[r3 out] vv]. cbn [fst snd] in *.
  forward_call r3.
  match goal with |- semax _ ?P _ _ => forward_if P end.
  { match goal with H: Int.repr _ = Int.zero |- _ => apply iserr_false in H end.
    destruct (read_skippable bs cap) as [[u var]|] eqn:Er; [| congruence].
    apply IL_read_skippable_le in Er; [| lia].
    match goal with H: r3 = Zlength u /\ _ |- _ => destruct H as [-> _] end.
    forward_call (Int.repr (if Int64.ltu (Int64.repr cap) (Int64.repr (Zlength u)) then 0 else 1)).
    1: entailer!; simpl; destruct (Int64.ltu _ _); reflexivity.
    1: match goal with H: _ = Int.zero |- False => revert H; apply assert_le; rep_lia end.
    entailer!. }
  { forward. entailer!. }
  forward_call (gv, Ews, src, bs).
  forward_call (gv, Ews, src, bs).
  forward_call (gv, Ews, src, bs).
  forward_call (gv, Ews, src, bs).
  Intros r4.
  forward_call (gv, Ews, src, bs).
  rewrite cs_bytes.
  forward_call (tarray tuchar (Zlength bs), src, gv).
  { rewrite if_false by auto. cancel. }
  rewrite cs_bytes.
  forward_call (tarray tuchar cap, dst, gv).
  { rewrite if_false by auto. cancel. }
  rewrite cs_fh, cs_uint.
  forward.
  unfold t_fh.
  sep_apply (@data_at_data_at_ HCS Tsh tuint vv v_variant).
  sep_apply (@data_at_data_at_ HCS Tsh (Tstruct ___gp_ZSTD_FrameHeader noattr) v v_zfh).
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

Theorem any_info_ok :
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
