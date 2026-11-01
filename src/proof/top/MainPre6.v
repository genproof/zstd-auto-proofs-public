(* The decoder's globals from main's precondition, for every whole program.
   A harness main (spec QPmain_spec_ext' of its whole program) starts from InitGPred (Vardefs whole_prog) gv;
   this splits off the decoder's tables as zstd_globals gv (zstd/Globals.v) and keeps the other globals of
   the program (the harness's own, string literals) as InitGPred of the rest. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Zstd.proof.zstd.Globals.
Require Zstd.contracts.x_any_dict.
Require Zstd.contracts.x_any_dict_copy.
Require Zstd.contracts.x_any_info.
Require Zstd.contracts.x_any_oneshot.
Require Zstd.contracts.x_any_stream.
Require Zstd.contracts.x_bound.
Require Zstd.contracts.x_detect.
Require Zstd.contracts.x_stable_out.
Require Zstd.contracts.x_valid_dict.
Require Zstd.contracts.x_valid_dict_copy.
Require Zstd.contracts.x_valid_info.
Require Zstd.contracts.x_valid_oneshot.
Require Zstd.contracts.x_valid_stream.
Require Zstd.contracts.x_any_bufferless.
Require Zstd.contracts.x_any_info_extra.
Require Zstd.contracts.x_any_params.
Require Zstd.contracts.x_valid_bufferless.
Require Zstd.contracts.x_valid_dict_api.
Require Zstd.contracts.x_valid_params.

(* The decoder's global variables of zstd_globals, as definitions. *)
Definition zstd_vardefs : list (ident * globdef (fundef function) type) :=
  [(Zstd.zstd.code._g_debuglevel, Gvar Zstd.zstd.code.v_g_debuglevel); (Zstd.zstd.code._DeBruijnBytePos, Gvar Zstd.zstd.code.v_DeBruijnBytePos); (Zstd.zstd.code._DeBruijnClz, Gvar Zstd.zstd.code.v_DeBruijnClz); (Zstd.zstd.code._zeroFilled, Gvar Zstd.zstd.code.v_zeroFilled); (Zstd.zstd.code._ZSTD_defaultCMem, Gvar Zstd.zstd.code.v_ZSTD_defaultCMem); (Zstd.zstd.code._repStartValue, Gvar Zstd.zstd.code.v_repStartValue); (Zstd.zstd.code._ZSTD_fcs_fieldSize, Gvar Zstd.zstd.code.v_ZSTD_fcs_fieldSize); (Zstd.zstd.code._ZSTD_did_fieldSize, Gvar Zstd.zstd.code.v_ZSTD_did_fieldSize); (Zstd.zstd.code._ZSTD_blockHeaderSize, Gvar Zstd.zstd.code.v_ZSTD_blockHeaderSize); (Zstd.zstd.code._LL_bits, Gvar Zstd.zstd.code.v_LL_bits); (Zstd.zstd.code._ML_bits, Gvar Zstd.zstd.code.v_ML_bits); (Zstd.zstd.code._algoTime, Gvar Zstd.zstd.code.v_algoTime); (Zstd.zstd.code._LL_base, Gvar Zstd.zstd.code.v_LL_base); (Zstd.zstd.code._OF_base, Gvar Zstd.zstd.code.v_OF_base); (Zstd.zstd.code._OF_bits, Gvar Zstd.zstd.code.v_OF_bits); (Zstd.zstd.code._ML_base, Gvar Zstd.zstd.code.v_ML_base); (Zstd.zstd.code._LL_defaultDTable, Gvar Zstd.zstd.code.v_LL_defaultDTable); (Zstd.zstd.code._OF_defaultDTable, Gvar Zstd.zstd.code.v_OF_defaultDTable); (Zstd.zstd.code._ML_defaultDTable, Gvar Zstd.zstd.code.v_ML_defaultDTable); (Zstd.zstd.code._dec32table, Gvar Zstd.zstd.code.v_dec32table); (Zstd.zstd.code._dec64table, Gvar Zstd.zstd.code.v_dec64table); (Zstd.zstd.code._ZSTD_emptyBuffer, Gvar Zstd.zstd.code.v_ZSTD_emptyBuffer)].

Definition zstd_var_ids : list ident := map fst zstd_vardefs.

Definition all_progs : list (QP.program function) :=
  [Zstd.contracts.x_any_dict.whole_prog;
   Zstd.contracts.x_any_dict_copy.whole_prog;
   Zstd.contracts.x_any_info.whole_prog;
   Zstd.contracts.x_any_oneshot.whole_prog;
   Zstd.contracts.x_any_stream.whole_prog;
   Zstd.contracts.x_bound.whole_prog;
   Zstd.contracts.x_detect.whole_prog;
   Zstd.contracts.x_stable_out.whole_prog;
   Zstd.contracts.x_valid_dict.whole_prog;
   Zstd.contracts.x_valid_dict_copy.whole_prog;
   Zstd.contracts.x_valid_info.whole_prog;
   Zstd.contracts.x_valid_oneshot.whole_prog;
   Zstd.contracts.x_valid_stream.whole_prog;
   Zstd.contracts.x_any_bufferless.whole_prog;
   Zstd.contracts.x_any_info_extra.whole_prog;
   Zstd.contracts.x_any_params.whole_prog;
   Zstd.contracts.x_valid_bufferless.whole_prog;
   Zstd.contracts.x_valid_dict_api.whole_prog;
   Zstd.contracts.x_valid_params.whole_prog].

Definition MainPreFact6 : Prop :=
  forall p, In p all_progs ->
  forall gv, globals_ok gv ->
  InitGPred (Vardefs p) gv |--
    Zstd.proof.zstd.Globals.zstd_globals gv *
    InitGPred (filter (fun ig => negb (id_in_list (fst ig) zstd_var_ids)) (Vardefs p)) gv.

(* ---------------------------------------------------------------------- *)
(* Generic helpers: init data of a global as data_at.                         *)

Lemma MP_init_data_list2pred_app gv sh (a b: list init_data) (bk: block) (z: ptrofs):
  init_data_list2pred gv (a ++ b) sh (Vptr bk z) =
  (init_data_list2pred gv a sh (Vptr bk z) *
   init_data_list2pred gv b sh (offset_val (init_data_list_size a) (Vptr bk z)))%logic.
Proof.
  revert z; induction a as [|d a IH]; intros z; simpl.
  - rewrite emp_sepcon. rewrite Ptrofs.add_zero. reflexivity.
  - rewrite IH, sepcon_assoc. simpl. rewrite Ptrofs.add_assoc, ptrofs_add_repr. reflexivity.
Qed.

Lemma MP_align_array {cs: compspecs} t n:
  complete_legal_cosu_type t = true ->
  (hardware_alignof ha_env_cs t | sizeof t) ->
  align_compatible_rec cenv_cs t 0 ->
  align_compatible_rec cenv_cs (tarray t n) 0.
Proof.
  intros Hc Hd H0. apply align_compatible_rec_Tarray; intros i Hi.
  eapply align_compatible_rec_hardware_alignof_divide with (z2 := 0); auto.
  - apply cenv_consistent.
  - apply cenv_legal_su.
  - apply ha_env_cs_consistent.
  - apply ha_env_cs_complete.
  - rewrite Z.sub_0_r, Z.add_0_l. apply Z.divide_mul_l. exact Hd.
Qed.

Lemma MP_fc_elem0 {cs: compspecs} t n p:
  0 < n -> field_compatible (tarray t n) [] p -> field_compatible t [] p.
Proof.
  intros Hn Hfc.
  assert (H: field_compatible (tarray t n) (SUB 0) p).
  { apply field_compatible_cons. simpl. split; [lia | auto]. }
  apply (field_compatible_app []) in H.
  rewrite field_address_offset in H by auto.
  destruct p; try (destruct Hfc; contradiction). simpl in H. rewrite Z.mul_0_r, Ptrofs.add_zero in H. exact H.
Qed.

Lemma MP_init_array {cs: compspecs} gv sh t (f: reptype t -> list init_data) (ok: reptype t -> bool):
  (forall x, ok x = true -> init_data_list_size (f x) = sizeof t) ->
  (forall x q, ok x = true -> field_compatible t [] q ->
     init_data_list2pred gv (f x) sh q |-- data_at sh t x q) ->
  forall vs p, forallb ok vs = true -> field_compatible (tarray t (Zlength vs)) [] p ->
  init_data_list2pred gv (concat (map f vs)) sh p |-- data_at sh (tarray t (Zlength vs)) vs p.
Proof.
  intros Hsz Hel. induction vs as [|x vs IH]; intros p Hok Hfc.
  - simpl. apply data_at_zero_array; auto.
    destruct Hfc as [_ [Hc _]]. exact Hc.
  - simpl in Hok. apply andb_prop in Hok as [Hx Hvs].
    assert (Hp: isptr p) by (destruct Hfc; auto).
    destruct p; try contradiction.
    simpl concat. rewrite MP_init_data_list2pred_app, Hsz by auto.
    pose proof (Zlength_nonneg vs) as Hn.
    assert (Hlen: Zlength (x :: vs) = Zlength vs + 1) by (rewrite Zlength_cons; lia).
    forget (Zlength (x :: vs)) as n.
    change (x :: vs) with ([x] ++ vs).
    rewrite (split2_data_at_Tarray_app 1 n sh t [x] vs) by (rewrite ?Zlength_cons, ?Zlength_nil; lia).
    rewrite (data_at_singleton_array_eq sh t x [x]) by reflexivity.
    pose proof Hfc as Hfc'.
    rewrite (field_compatible_Tarray_split t 1) in Hfc' by lia. destruct Hfc' as [_ Hfc2].
    rewrite arr_field_address0 in * by (auto; lia).
    rewrite Z.mul_1_r in *.
    apply sepcon_derives.
    + apply Hel; auto. eapply MP_fc_elem0; [ | exact Hfc]. lia.
    + replace (n - 1) with (Zlength vs) in * by lia.
      apply IH; auto.
Qed.

(* The alignment of a struct of scalars, field by field. *)
Ltac MP_align_struct :=
  eapply align_compatible_rec_Tstruct; [reflexivity | reflexivity | ];
  let i0 := fresh "i0" in let H1 := fresh "H1" in let H2 := fresh "H2" in
  intros i0 ? ? H1 H2; simpl in H1;
  repeat match type of H1 with context [ident_eq i0 ?x] => destruct (ident_eq i0 x); [subst i0; inv H1 | ] end;
  try discriminate;
  vm_compute in H2; inv H2; (eapply align_compatible_rec_by_value; [reflexivity | ]);
  (apply Z.mod_divide; [simpl; lia | vm_compute; reflexivity]).

(* An element predicate: init data f x describe the value x of type t. *)
Definition MP_El {cs: compspecs} gv sh t (f: reptype t -> list init_data) (ok: reptype t -> bool) :=
  forall x q, ok x = true -> field_compatible t [] q ->
    init_data_list2pred gv (f x) sh q |-- data_at sh t x q.

Definition MP_Sz {cs: compspecs} t (f: reptype t -> list init_data) (ok: reptype t -> bool) :=
  forall x, ok x = true -> init_data_list_size (f x) = sizeof t.

Definition MP_arr_f {cs: compspecs} t (f: reptype t -> list init_data) (vs: list (reptype t)) :=
  concat (map f vs).
Definition MP_arr_ok {cs: compspecs} t (ok: reptype t -> bool) n (vs: list (reptype t)) :=
  andb (Z.eqb (Zlength vs) n) (forallb ok vs).

Lemma MP_El_array {cs: compspecs} gv sh t f ok n:
  MP_Sz t f ok -> MP_El gv sh t f ok ->
  MP_El gv sh (tarray t n) (MP_arr_f t f) (MP_arr_ok t ok n).
Proof.
  intros Hsz Hel vs q Hok Hfc. unfold MP_arr_ok in Hok.
  apply andb_prop in Hok as [Hn Hok]. apply Z.eqb_eq in Hn. rewrite <- Hn in Hfc |- *.
  unfold MP_arr_f. apply (MP_init_array gv sh t f ok); auto.
Qed.

Lemma MP_idls_app a b: init_data_list_size (a ++ b) = init_data_list_size a + init_data_list_size b.
Proof. induction a as [|d a IH]; simpl; [lia | rewrite IH; lia]. Qed.

Lemma MP_Sz_concat {cs: compspecs} t f ok:
  MP_Sz t f ok -> forall vs, forallb ok vs = true ->
  init_data_list_size (concat (map f vs)) = sizeof t * Zlength vs.
Proof.
  intros Hsz vs. induction vs as [|x vs IH]; intros Hok.
  - simpl. rewrite Zlength_nil. lia.
  - simpl in Hok. apply andb_prop in Hok as [Hx Hvs].
    simpl map. simpl concat. rewrite MP_idls_app, Hsz, IH, Zlength_cons by auto. lia.
Qed.

Lemma MP_Sz_array {cs: compspecs} t f ok n:
  MP_Sz t f ok -> MP_Sz (tarray t n) (MP_arr_f t f) (MP_arr_ok t ok n).
Proof.
  intros Hsz vs Hok. unfold MP_arr_ok in Hok.
  apply andb_prop in Hok as [Hn Hok]. apply Z.eqb_eq in Hn. rewrite <- Hn.
  unfold MP_arr_f. simpl sizeof. rewrite Z.max_r by apply Zlength_nonneg.
  apply (MP_Sz_concat t f ok); auto.
Qed.

Lemma MP_glob {cs: compspecs} gv i v t f ok x:
  MP_El gv (readonly2share (gvar_readonly v)) t f ok ->
  gvar_volatile v = false ->
  gvar_init v = f x ->
  ok x = true ->
  complete_legal_cosu_type t = true ->
  sizeof t < Ptrofs.modulus ->
  align_compatible_rec cenv_cs t 0 ->
  globs2pred gv (i, Gvar v) |-- data_at (readonly2share (gvar_readonly v)) t x (gv i).
Proof.
  intros Hel Hvol Hinit Hok Hc Hs Ha.
  unfold globs2pred, globvar2pred. simpl. rewrite Hvol, Hinit.
  apply derives_extract_prop; intros Hh.
  apply Hel; auto.
  apply headptr_field_compatible; auto. simpl; auto.
Qed.

(* ---------------------------------------------------------------------- *)
(* The element types of the decoder's tables, at the decoder's compspecs.     *)

Section Elements.
#[local] Existing Instance Zstd.units.Zstd.CS.
Variable gv: globals.
Variable sh: share.

Definition MP_isint (x: val) : bool := match x with Vint _ => true | _ => false end.
Definition MP_islong (x: val) : bool := match x with Vlong _ => true | _ => false end.
Definition MP_u8ok (x: val) : bool := match x with Vint i => Int.eq (Int.zero_ext 8 i) i | _ => false end.
Definition MP_u16ok (x: val) : bool := match x with Vint i => Int.eq (Int.zero_ext 16 i) i | _ => false end.
Definition MP_f32 (x: val) : list init_data := match x with Vint i => [Init_int32 i] | _ => [] end.
Definition MP_f8 (x: val) : list init_data := match x with Vint i => [Init_int8 i] | _ => [] end.
Definition MP_f16 (x: val) : list init_data := match x with Vint i => [Init_int16 i] | _ => [] end.
Definition MP_f64 (x: val) : list init_data := match x with Vlong i => [Init_int64 i] | _ => [] end.

Definition MP_seq_ok (x: val * (val * (val * val))) : bool :=
  match x with
  | (Vint a, (Vint b, (Vint c, Vint d))) =>
      Int.eq (Int.zero_ext 16 a) a && Int.eq (Int.zero_ext 8 b) b && Int.eq (Int.zero_ext 8 c) c
  | _ => false
  end.
Definition MP_seq_f (x: val * (val * (val * val))) : list init_data :=
  match x with
  | (Vint a, (Vint b, (Vint c, Vint d))) => [Init_int16 a; Init_int8 b; Init_int8 c; Init_int32 d]
  | _ => []
  end.

Lemma MP_seq_align: align_compatible_rec cenv_cs (Tstruct Zstd.zstd.code.___gp_ZSTD_seqSymbol noattr) 0.
Proof. MP_align_struct. Qed.

Lemma MP_seq_el x q: MP_seq_ok x = true -> field_compatible (Tstruct Zstd.zstd.code.___gp_ZSTD_seqSymbol noattr) [] q ->
  init_data_list2pred gv (MP_seq_f x) sh q |-- data_at sh (Tstruct Zstd.zstd.code.___gp_ZSTD_seqSymbol noattr) x q.
Proof.
  intros Hok Hfc.
  destruct x as [[] [[] [[] []]]]; try discriminate.
  simpl in Hok. rewrite !andb_true_iff in Hok. destruct Hok as [[Ha Hb] Hc].
  apply Int.same_if_eq in Ha, Hb, Hc.
  unfold_data_at (data_at _ _ _ q).
  assert (Hp: isptr q) by (destruct Hfc; auto). destruct q; try contradiction.
  simpl MP_seq_f. unfold init_data_list2pred. simpl init_data2pred. rewrite Ha, Hb, Hc, sepcon_emp.
  rewrite <- (mapsto_field_at _ _ _ (Vint i)) by (reflexivity || auto with field_compatible).
  rewrite <- (mapsto_field_at _ _ _ (Vint i0)) by (reflexivity || auto with field_compatible).
  rewrite <- (mapsto_field_at _ _ _ (Vint i1)) by (reflexivity || auto with field_compatible).
  rewrite <- (mapsto_field_at _ _ _ (Vint i2)) by (reflexivity || auto with field_compatible).
  rewrite !field_address_offset by auto with field_compatible.
  simpl. rewrite !Ptrofs.add_assoc, !ptrofs_add_repr. simpl.
  change (Ptrofs.repr 0) with Ptrofs.zero. rewrite Ptrofs.add_zero. apply derives_refl.
Qed.

Lemma MP_seq_size x: MP_seq_ok x = true -> init_data_list_size (MP_seq_f x) = sizeof (Tstruct Zstd.zstd.code.___gp_ZSTD_seqSymbol noattr).
Proof. intros Hok. destruct x as [[] [[] [[] []]]]; try discriminate; reflexivity. Qed.

Lemma MP_uint_el: MP_El gv sh tuint MP_f32 MP_isint.
Proof.
  intros x q Hok Hfc. destruct x; try discriminate.
  simpl. rewrite sepcon_emp. rewrite <- (mapsto_data_at' sh tuint (Vint i) (Vint i) q) by auto; apply derives_refl.
Qed.

Lemma MP_int_el: MP_El gv sh tint MP_f32 MP_isint.
Proof.
  intros x q Hok Hfc. destruct x; try discriminate.
  simpl. rewrite sepcon_emp. change (Tint I32 Unsigned noattr) with tuint. rewrite mapsto_tuint_tint.
  rewrite <- (mapsto_data_at' sh tint (Vint i) (Vint i) q) by auto; apply derives_refl.
Qed.

Lemma MP_uchar_el: MP_El gv sh tuchar MP_f8 MP_u8ok.
Proof.
  intros x q Hok Hfc. destruct x; try discriminate.
  simpl in Hok. apply Int.same_if_eq in Hok.
  simpl. rewrite sepcon_emp, Hok. rewrite <- (mapsto_data_at' sh tuchar (Vint i) (Vint i) q) by auto; apply derives_refl.
Qed.

Lemma MP_ulong_el: MP_El gv sh tulong MP_f64 MP_islong.
Proof.
  intros x q Hok Hfc. destruct x; try discriminate.
  simpl. rewrite sepcon_emp. rewrite <- (mapsto_data_at' sh tulong (Vlong i) (Vlong i) q) by auto; apply derives_refl.
Qed.

Lemma MP_uint_sz: MP_Sz tuint MP_f32 MP_isint.
Proof. intros x Hok. destruct x; try discriminate; reflexivity. Qed.
Lemma MP_int_sz: MP_Sz tint MP_f32 MP_isint.
Proof. intros x Hok. destruct x; try discriminate; reflexivity. Qed.
Lemma MP_uchar_sz: MP_Sz tuchar MP_f8 MP_u8ok.
Proof. intros x Hok. destruct x; try discriminate; reflexivity. Qed.
Lemma MP_ulong_sz: MP_Sz tulong MP_f64 MP_islong.
Proof. intros x Hok. destruct x; try discriminate; reflexivity. Qed.

Lemma MP_seq_El: MP_El gv sh (Tstruct Zstd.zstd.code.___gp_ZSTD_seqSymbol noattr) MP_seq_f MP_seq_ok.
Proof. intros x q. apply MP_seq_el. Qed.
Lemma MP_seq_Sz: MP_Sz (Tstruct Zstd.zstd.code.___gp_ZSTD_seqSymbol noattr) MP_seq_f MP_seq_ok.
Proof. intros x. apply MP_seq_size. Qed.

Definition MP_at_ok (x: val * val) : bool :=
  match x with (Vint _, Vint _) => true | _ => false end.
Definition MP_at_f (x: val * val) : list init_data :=
  match x with (Vint a, Vint b) => [Init_int32 a; Init_int32 b] | _ => [] end.

Lemma MP_at_El: MP_El gv sh (Tstruct Zstd.zstd.code.___gp_algo_time_t noattr) MP_at_f MP_at_ok.
Proof.
  intros x q Hok Hfc.
  destruct x as [[] []]; try discriminate.
  unfold_data_at (data_at _ _ _ q).
  assert (Hp: isptr q) by (destruct Hfc; auto). destruct q; try contradiction.
  simpl MP_at_f. unfold init_data_list2pred. simpl init_data2pred. rewrite sepcon_emp.
  rewrite <- (mapsto_field_at _ _ _ (Vint i)) by (reflexivity || auto with field_compatible).
  rewrite <- (mapsto_field_at _ _ _ (Vint i0)) by (reflexivity || auto with field_compatible).
  rewrite !field_address_offset by auto with field_compatible.
  simpl. rewrite ?Ptrofs.add_assoc, ?ptrofs_add_repr. simpl.
  change (Ptrofs.repr 0) with Ptrofs.zero. rewrite Ptrofs.add_zero. apply derives_refl.
Qed.

Lemma MP_at_Sz: MP_Sz (Tstruct Zstd.zstd.code.___gp_algo_time_t noattr) MP_at_f MP_at_ok.
Proof. intros x Hok. destruct x as [[] []]; try discriminate; reflexivity. Qed.

Definition MP_isnull (x: val) : bool := match x with Vlong i => Int64.eq i Int64.zero | _ => false end.
Definition MP_cm_ok (x: val * (val * val)) : bool :=
  match x with (a, (b, c)) => MP_isnull a && MP_isnull b && MP_isnull c end.
Definition MP_cm_f (x: val * (val * val)) : list init_data :=
  [Init_int64 Int64.zero; Init_int64 Int64.zero; Init_int64 Int64.zero].

Lemma MP_isnull_eq x: MP_isnull x = true -> x = nullval.
Proof.
  destruct x; try discriminate. simpl. intros H. apply Int64.same_if_eq in H. subst. reflexivity.
Qed.

Lemma MP_cm_El: MP_El gv sh (Tstruct Zstd.zstd.code.___gp_ZSTD_customMem noattr) MP_cm_f MP_cm_ok.
Proof.
  intros x q Hok Hfc.
  destruct x as [a [b c]]. simpl in Hok. rewrite !andb_true_iff in Hok. destruct Hok as [[Ha Hb] Hc].
  apply MP_isnull_eq in Ha, Hb, Hc. subst a b c.
  unfold_data_at (data_at _ _ _ q).
  assert (Hp: isptr q) by (destruct Hfc; auto). destruct q; try contradiction.
  unfold MP_cm_f, init_data_list2pred. simpl init_data2pred. rewrite sepcon_emp.
  rewrite <- (mapsto_field_at sh (Tstruct Zstd.zstd.code.___gp_ZSTD_customMem noattr) (DOT Zstd.zstd.code._customAlloc)
    nullval ltac:(exact nullval) (Vptr b i)) by (reflexivity || auto with field_compatible).
  rewrite <- (mapsto_field_at sh (Tstruct Zstd.zstd.code.___gp_ZSTD_customMem noattr) (DOT Zstd.zstd.code._customFree)
    nullval ltac:(exact nullval) (Vptr b i)) by (reflexivity || auto with field_compatible).
  rewrite <- (mapsto_field_at sh (Tstruct Zstd.zstd.code.___gp_ZSTD_customMem noattr) (DOT Zstd.zstd.code._opaque)
    nullval ltac:(exact nullval) (Vptr b i)) by (reflexivity || auto with field_compatible).
  rewrite !field_address_offset by auto with field_compatible.
  simpl nested_field_type. unfold tptr. rewrite !mapsto_size_t_tptr_nullval.
  simpl. rewrite ?Ptrofs.add_assoc, ?ptrofs_add_repr. simpl.
  change (Ptrofs.repr 0) with Ptrofs.zero. rewrite Ptrofs.add_zero. apply derives_refl.
Qed.

Lemma MP_cm_Sz: MP_Sz (Tstruct Zstd.zstd.code.___gp_ZSTD_customMem noattr) MP_cm_f MP_cm_ok.
Proof. intros x Hok. reflexivity. Qed.

End Elements.


(* ---------------------------------------------------------------------- *)
(* The decoder's globals: InitGPred zstd_vardefs |-- zstd_globals.              *)

Lemma MP_glob' {cs: compspecs} gv i v t f ok x sh:
  readonly2share (gvar_readonly v) = sh ->
  MP_El gv sh t f ok ->
  gvar_volatile v = false ->
  gvar_init v = f x ->
  ok x = true ->
  complete_legal_cosu_type t = true ->
  sizeof t < Ptrofs.modulus ->
  align_compatible_rec cenv_cs t 0 ->
  globs2pred gv (i, Gvar v) |-- data_at sh t x (gv i).
Proof. intros <-. apply MP_glob. Qed.

Section Globals.
#[local] Existing Instance Zstd.units.Zstd.CS.

Ltac MP_F t :=
  lazymatch t with
  | tarray ?u _ => let f := MP_F u in constr:(@MP_arr_f Zstd.units.Zstd.CS u f)
  | tuint => constr:(MP_f32)
  | tint => constr:(MP_f32)
  | tuchar => constr:(MP_f8)
  | tulong => constr:(MP_f64)
  | Tstruct Zstd.zstd.code.___gp_ZSTD_seqSymbol noattr => constr:(MP_seq_f)
  | Tstruct Zstd.zstd.code.___gp_algo_time_t noattr => constr:(MP_at_f)
  | Tstruct Zstd.zstd.code.___gp_ZSTD_customMem noattr => constr:(MP_cm_f)
  end.

Ltac MP_O t :=
  lazymatch t with
  | tarray ?u ?n => let o := MP_O u in constr:(@MP_arr_ok Zstd.units.Zstd.CS u o n)
  | tuint => constr:(MP_isint)
  | tint => constr:(MP_isint)
  | tuchar => constr:(MP_u8ok)
  | tulong => constr:(MP_islong)
  | Tstruct Zstd.zstd.code.___gp_ZSTD_seqSymbol noattr => constr:(MP_seq_ok)
  | Tstruct Zstd.zstd.code.___gp_algo_time_t noattr => constr:(MP_at_ok)
  | Tstruct Zstd.zstd.code.___gp_ZSTD_customMem noattr => constr:(MP_cm_ok)
  end.

Ltac MP_el :=
  repeat first [ apply MP_El_array | apply MP_Sz_array
               | apply MP_uint_el | apply MP_uint_sz | apply MP_int_el | apply MP_int_sz
               | apply MP_uchar_el | apply MP_uchar_sz | apply MP_ulong_el | apply MP_ulong_sz
               | apply MP_seq_El | apply MP_seq_Sz | apply MP_at_El | apply MP_at_Sz
               | apply MP_cm_El | apply MP_cm_Sz ].

Ltac MP_one :=
  lazymatch goal with
  | |- globs2pred _ _ |-- data_at _ ?t _ _ =>
      let F := MP_F t in let O := MP_O t in
      eapply (@MP_glob' Zstd.units.Zstd.CS _ _ _ t F O);
      [ reflexivity | MP_el | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
      | vm_compute; reflexivity | vm_compute; reflexivity | apply la_env_cs_sound; vm_compute; reflexivity ]
  end.

Lemma zstd_vardefs_globals gv:
  InitGPred zstd_vardefs gv |-- Zstd.proof.zstd.Globals.zstd_globals gv.
Proof.
  unfold InitGPred, zstd_vardefs, Zstd.proof.zstd.Globals.zstd_globals.
  cbn [map fold_right]. rewrite sepcon_emp. rewrite <- !sepcon_assoc.
  repeat apply sepcon_derives; try MP_one.
  (* ZSTD_emptyBuffer: eb_res at the initial share Ers *)
  unfold Zstd.proof.zstd.Globals.eb_res. Exists Ers. rewrite prop_true_andp by apply readable_Ers. MP_one.
Qed.

End Globals.

Fixpoint MP_nodupb (l: list ident) : bool :=
  match l with
  | nil => true
  | x :: l' => negb (existsb (Pos.eqb x) l') && MP_nodupb l'
  end.

Lemma MP_nodupb_NoDup l: MP_nodupb l = true -> NoDup l.
Proof.
  induction l as [|x l IH]; simpl; intros H; constructor.
  - apply andb_prop in H as [H _]. intros Hin.
    assert (existsb (Pos.eqb x) l = true) by (apply existsb_exists; exists x; split; auto; apply Pos.eqb_refl).
    rewrite H0 in H; discriminate.
  - apply andb_prop in H as [_ H]; auto.
Qed.

Lemma MP_incl_Vardefs (p: QP.program function) l:
  map (fun ig => Maps.PTree.get (fst ig) (QP.prog_defs p)) l = map (fun ig => Some (snd ig)) l ->
  forallb isGvar l = true ->
  incl l (Vardefs p).
Proof.
  induction l as [|[i g] l IH]; simpl; intros Hm Hg.
  - intros ? [].
  - injection Hm as H1 H2. apply andb_prop in Hg as [Hg1 Hg2].
    intros x [<- | Hx].
    + unfold Vardefs. apply filter_In. split; auto. apply Maps.PTree.elements_correct; auto.
    + apply IH; auto.
Qed.

Lemma MP_zstd_vardefs_NoDup: NoDup zstd_vardefs.
Proof.
  apply NoDup_map_inv with (f := fst). apply MP_nodupb_NoDup. vm_compute. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* InitGPred is a separating fold: it splits along filter and permutations.   *)

Lemma MP_InitGPred_filter (h: ident * globdef (fundef function) type -> bool) l gv:
  InitGPred l gv = (InitGPred (filter h l) gv * InitGPred (filter (fun x => negb (h x)) l) gv)%logic.
Proof.
  induction l as [|a l IH]; simpl.
  - rewrite InitGPred_nilD, sepcon_emp. reflexivity.
  - rewrite InitGPred_consD, IH. destruct (h a); simpl; rewrite InitGPred_consD.
    + rewrite sepcon_assoc. reflexivity.
    + rewrite <- !sepcon_assoc. rewrite (sepcon_comm (globs2pred gv a)). reflexivity.
Qed.

Lemma MP_InitGPred_perm l1 l2 gv: Permutation l1 l2 -> InitGPred l1 gv = InitGPred l2 gv.
Proof.
  induction 1.
  - reflexivity.
  - rewrite !InitGPred_consD, IHPermutation. reflexivity.
  - rewrite !InitGPred_consD, <- !sepcon_assoc, (sepcon_comm (globs2pred gv y)). reflexivity.
  - congruence.
Qed.

Lemma MP_keys_unique {A B: Type} (l: list (A * B)) i x y:
  NoDup (map fst l) -> In (i, x) l -> In (i, y) l -> x = y.
Proof.
  induction l as [|[j z] l IH]; simpl; intros Hnd Hx Hy; [contradiction | ].
  inv Hnd. destruct Hx as [Hx | Hx], Hy as [Hy | Hy].
  - inv Hx; inv Hy; auto.
  - inv Hx. exfalso. apply H1. apply (in_map fst) in Hy. exact Hy.
  - inv Hy. exfalso. apply H1. apply (in_map fst) in Hx. exact Hx.
  - auto.
Qed.

Lemma MP_NoDup_map_filter {A B: Type} (f: A * B -> bool) l:
  NoDup (map fst l) -> NoDup (map fst (filter f l)).
Proof.
  induction l as [|a l IH]; simpl; intros Hnd; [constructor | ].
  inv Hnd. destruct (f a); simpl; auto.
  constructor; auto. intros Hin. apply H1.
  apply in_map_iff in Hin as [b [Hb Hin]]. apply filter_In in Hin as [Hin _].
  rewrite <- Hb. apply in_map. exact Hin.
Qed.

Lemma MP_Vardefs_keys (p: QP.program function): NoDup (map fst (Vardefs p)).
Proof.
  unfold Vardefs. apply MP_NoDup_map_filter.
  apply list_norepet_NoDup. apply Maps.PTree.elements_keys_norepet.
Qed.

Lemma MP_id_in_list_true_i i l: In i l -> id_in_list i l = true.
Proof.
  induction l as [|j l IH]; simpl; [contradiction | ].
  intros [<- | H]; [rewrite Pos.eqb_refl; reflexivity | rewrite IH by auto; apply orb_true_r].
Qed.

Lemma MP_split_zstd (p: QP.program function) gv:
  incl zstd_vardefs (Vardefs p) ->
  InitGPred (Vardefs p) gv =
    (InitGPred zstd_vardefs gv *
     InitGPred (filter (fun ig => negb (id_in_list (fst ig) zstd_var_ids)) (Vardefs p)) gv)%logic.
Proof.
  intros Hincl.
  rewrite (MP_InitGPred_filter (fun ig => id_in_list (fst ig) zstd_var_ids)).
  f_equal. apply MP_InitGPred_perm.
  pose proof (MP_Vardefs_keys p) as Hk.
  apply NoDup_Permutation.
  - apply NoDup_map_inv with (f := fst). apply MP_NoDup_map_filter. exact Hk.
  - apply MP_zstd_vardefs_NoDup.
  - intros [i g]. rewrite filter_In. cbn [fst]. split.
    + intros [Hin Hid]. apply id_in_list_true in Hid.
      unfold zstd_var_ids in Hid. apply in_map_iff in Hid as [[j g'] [Hj Hin']]. simpl in Hj. subst j.
      rewrite (MP_keys_unique (Vardefs p) i g g'); auto.
    + intros Hin. split; [apply Hincl; exact Hin | ].
      apply MP_id_in_list_true_i. unfold zstd_var_ids. apply (in_map fst) in Hin. exact Hin.
Qed.

Lemma main_pre_fact6 : MainPreFact6.
Proof.
  intros p Hp gv Hgv.
  assert (Hincl: incl zstd_vardefs (Vardefs p)).
  { apply MP_incl_Vardefs; [ | vm_compute; reflexivity].
    unfold all_progs in Hp.
    repeat destruct Hp as [<- | Hp]; try contradiction; vm_compute; reflexivity. }
  rewrite (MP_split_zstd p gv Hincl).
  apply sepcon_derives; [apply zstd_vardefs_globals | apply derives_refl].
Qed.
