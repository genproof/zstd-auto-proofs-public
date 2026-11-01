(* Generic lemmas for the writer's init_ok (InitGPred wvardefs gv |-- WG_impl gv), over any compspecs.  The per-unit
   proofs are generated from the template WB_init.
   - WI_perm: InitGPred of the filter of a program's Vardefs on a list of idents is InitGPred of an
     explicit list of (ident, Gvar v) (checked by computation);
   - WI_zero: a zero-initialised global (Init_space) is data_at of zero_val;
   - WI_glob + element lemmas: a global with scalar init data is data_at of its values (uint, uchar,
     signed short). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.

(* ---------------------------------------------------------------------- *)
(* InitGPred along permutations.                                           *)

Lemma WI_InitGPred_perm l1 l2 gv: Permutation l1 l2 -> InitGPred l1 gv = InitGPred l2 gv.
Proof.
  induction 1.
  - reflexivity.
  - rewrite !InitGPred_consD, IHPermutation. reflexivity.
  - rewrite !InitGPred_consD, <- !sepcon_assoc, (sepcon_comm (globs2pred gv y)). reflexivity.
  - congruence.
Qed.

Fixpoint WI_nodupb (l: list ident) : bool :=
  match l with
  | nil => true
  | x :: l' => negb (existsb (Pos.eqb x) l') && WI_nodupb l'
  end.

Lemma WI_nodupb_NoDup l: WI_nodupb l = true -> NoDup l.
Proof.
  induction l as [|x l IH]; simpl; intros H; constructor.
  - apply andb_prop in H as [H _]. intros Hin.
    assert (existsb (Pos.eqb x) l = true) by (apply existsb_exists; exists x; split; auto; apply Pos.eqb_refl).
    rewrite H0 in H; discriminate.
  - apply andb_prop in H as [_ H]; auto.
Qed.

Lemma WI_keys_unique {A B: Type} (l: list (A * B)) i x y:
  NoDup (map fst l) -> In (i, x) l -> In (i, y) l -> x = y.
Proof.
  induction l as [|[j z] l IH]; simpl; intros Hnd Hx Hy; [contradiction | ].
  inv Hnd. destruct Hx as [Hx | Hx], Hy as [Hy | Hy].
  - inv Hx; inv Hy; auto.
  - inv Hx. exfalso. apply H1. apply (in_map fst) in Hy. exact Hy.
  - inv Hy. exfalso. apply H1. apply (in_map fst) in Hx. exact Hx.
  - auto.
Qed.

Lemma WI_NoDup_map_filter {A B: Type} (f: A * B -> bool) l:
  NoDup (map fst l) -> NoDup (map fst (filter f l)).
Proof.
  induction l as [|a l IH]; simpl; intros Hnd; [constructor | ].
  inv Hnd. destruct (f a); simpl; auto.
  constructor; auto. intros Hin. apply H1.
  apply in_map_iff in Hin as [b [Hb Hin]]. apply filter_In in Hin as [Hin _].
  rewrite <- Hb. apply in_map. exact Hin.
Qed.

Lemma WI_Vardefs_keys (p: QP.program function): NoDup (map fst (Vardefs p)).
Proof.
  unfold Vardefs. apply WI_NoDup_map_filter.
  apply list_norepet_NoDup. apply Maps.PTree.elements_keys_norepet.
Qed.

Lemma WI_id_in_list_true_i i l: In i l -> id_in_list i l = true.
Proof.
  induction l as [|j l IH]; simpl; [contradiction | ].
  intros [<- | H]; [rewrite Pos.eqb_refl; reflexivity | rewrite IH by auto; apply orb_true_r].
Qed.

Lemma WI_incl_Vardefs (p: QP.program function) l:
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

Definition WI_subb (l1 l2: list ident) : bool := forallb (fun i => existsb (Pos.eqb i) l2) l1.

Lemma WI_subb_In l1 l2 i: WI_subb l1 l2 = true -> In i l1 -> In i l2.
Proof.
  unfold WI_subb. rewrite forallb_forall. intros H Hi. specialize (H i Hi).
  apply existsb_exists in H as [j [Hj Heq]]. apply Pos.eqb_eq in Heq. subst j. exact Hj.
Qed.

(* the hypotheses are closed by computation (vm_compute; reflexivity) *)
Lemma WI_perm (p: QP.program function) (ids: list ident) (L: list (ident * globdef (fundef function) type)) gv:
  WI_nodupb (map fst L) = true ->
  WI_subb ids (map fst L) = true ->
  WI_subb (map fst L) ids = true ->
  map (fun ig => Maps.PTree.get (fst ig) (QP.prog_defs p)) L = map (fun ig => Some (snd ig)) L ->
  forallb isGvar L = true ->
  InitGPred (filter (fun ig => id_in_list (fst ig) ids) (Vardefs p)) gv = InitGPred L gv.
Proof.
  intros Hnd Hs1 Hs2 Hget Hgv.
  assert (Hincl: incl L (Vardefs p)) by (apply WI_incl_Vardefs; auto).
  apply WI_nodupb_NoDup in Hnd.
  pose proof (WI_Vardefs_keys p) as Hk.
  apply WI_InitGPred_perm, NoDup_Permutation.
  - apply NoDup_map_inv with (f := fst). apply WI_NoDup_map_filter. exact Hk.
  - apply NoDup_map_inv with (f := fst). exact Hnd.
  - intros [i g]. rewrite filter_In. cbn [fst]. split.
    + intros [Hin Hid]. apply id_in_list_true in Hid. apply (WI_subb_In _ _ _ Hs1) in Hid.
      apply in_map_iff in Hid as [[j g'] [Hj Hin']]. simpl in Hj. subst j.
      rewrite (WI_keys_unique (Vardefs p) i g g'); auto.
    + intros Hin. split; [apply Hincl; exact Hin | ].
      apply WI_id_in_list_true_i. apply (WI_subb_In _ _ _ Hs2). apply (in_map fst) in Hin. exact Hin.
Qed.

(* ---------------------------------------------------------------------- *)
(* Init data as data_at.                                                   *)

Lemma WI_init_data_list2pred_app gv sh (a b: list init_data) (bk: block) (z: ptrofs):
  init_data_list2pred gv (a ++ b) sh (Vptr bk z) =
  (init_data_list2pred gv a sh (Vptr bk z) *
   init_data_list2pred gv b sh (offset_val (init_data_list_size a) (Vptr bk z)))%logic.
Proof.
  revert z; induction a as [|d a IH]; intros z; simpl.
  - rewrite emp_sepcon. rewrite Ptrofs.add_zero. reflexivity.
  - rewrite IH, sepcon_assoc. simpl. rewrite Ptrofs.add_assoc, ptrofs_add_repr. reflexivity.
Qed.

Section Generic.
Context {cs: compspecs}.

Lemma WI_zero gv i v t sh:
  readonly2share (gvar_readonly v) = sh ->
  gvar_volatile v = false ->
  gvar_init v = [Init_space (sizeof t)] ->
  complete_legal_cosu_type t = true ->
  fully_nonvolatile (rank_type cenv_cs t) t = true ->
  sizeof t < Ptrofs.modulus ->
  align_compatible_rec cenv_cs t 0 ->
  globs2pred gv (i, Gvar v) |-- data_at sh t (zero_val t) (gv i).
Proof.
  intros <- Hvol Hinit Hc Hnv Hs Ha.
  unfold globs2pred, globvar2pred. simpl. rewrite Hvol, Hinit.
  apply derives_extract_prop; intros Hh.
  simpl. rewrite sepcon_emp.
  apply mapsto_zero_data_at_zero; auto.
  - apply readable_readonly2share.
  - apply headptr_field_compatible; auto. simpl; auto.
Qed.

Lemma WI_fc_elem0 t n p:
  0 < n -> field_compatible (tarray t n) [] p -> field_compatible t [] p.
Proof.
  intros Hn Hfc.
  assert (H: field_compatible (tarray t n) (SUB 0) p).
  { apply field_compatible_cons. simpl. split; [lia | auto]. }
  apply (field_compatible_app []) in H.
  rewrite field_address_offset in H by auto.
  destruct p; try (destruct Hfc; contradiction). simpl in H. rewrite Z.mul_0_r, Ptrofs.add_zero in H. exact H.
Qed.

Definition WI_El gv sh t (f: reptype t -> list init_data) (ok: reptype t -> bool) :=
  forall x q, ok x = true -> field_compatible t [] q ->
    init_data_list2pred gv (f x) sh q |-- data_at sh t x q.

Definition WI_Sz t (f: reptype t -> list init_data) (ok: reptype t -> bool) :=
  forall x, ok x = true -> init_data_list_size (f x) = sizeof t.

Lemma WI_init_array gv sh t (f: reptype t -> list init_data) (ok: reptype t -> bool):
  WI_Sz t f ok -> WI_El gv sh t f ok ->
  forall vs p, forallb ok vs = true -> field_compatible (tarray t (Zlength vs)) [] p ->
  init_data_list2pred gv (concat (map f vs)) sh p |-- data_at sh (tarray t (Zlength vs)) vs p.
Proof.
  intros Hsz Hel. induction vs as [|x vs IH]; intros p Hok Hfc.
  - simpl. apply data_at_zero_array; auto.
    destruct Hfc as [_ [Hc _]]. exact Hc.
  - simpl in Hok. apply andb_prop in Hok as [Hx Hvs].
    assert (Hp: isptr p) by (destruct Hfc; auto).
    destruct p; try contradiction.
    simpl concat. rewrite WI_init_data_list2pred_app, Hsz by auto.
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
    + apply Hel; auto. eapply WI_fc_elem0; [ | exact Hfc]. lia.
    + replace (n - 1) with (Zlength vs) in * by lia.
      apply IH; auto.
Qed.

Definition WI_arr_f t (f: reptype t -> list init_data) (vs: list (reptype t)) := concat (map f vs).

(* a global whose init data are the elements' init data *)
Lemma WI_glob gv i v t n f ok (vs: list (reptype t)) sh:
  readonly2share (gvar_readonly v) = sh ->
  WI_Sz t f ok -> WI_El gv sh t f ok ->
  gvar_volatile v = false ->
  gvar_init v = WI_arr_f t f vs ->
  Zlength vs = n ->
  forallb ok vs = true ->
  complete_legal_cosu_type (tarray t n) = true ->
  sizeof (tarray t n) < Ptrofs.modulus ->
  align_compatible_rec cenv_cs (tarray t n) 0 ->
  globs2pred gv (i, Gvar v) |-- data_at sh (tarray t n) vs (gv i).
Proof.
  intros <- Hsz Hel Hvol Hinit <- Hok Hc Hs Ha.
  unfold globs2pred, globvar2pred. simpl. rewrite Hvol, Hinit.
  apply derives_extract_prop; intros Hh.
  unfold WI_arr_f. apply (WI_init_array gv _ t f ok); auto.
  apply headptr_field_compatible; auto. simpl; auto.
Qed.

Definition WI_isint (x: val) : bool := match x with Vint _ => true | _ => false end.
Definition WI_u8ok (x: val) : bool := match x with Vint i => Int.eq (Int.zero_ext 8 i) i | _ => false end.
Definition WI_s16ok (x: val) : bool := match x with Vint i => Int.eq (Int.sign_ext 16 i) i | _ => false end.
Definition WI_f32 (x: val) : list init_data := match x with Vint i => [Init_int32 i] | _ => [] end.
Definition WI_f8 (x: val) : list init_data := match x with Vint i => [Init_int8 i] | _ => [] end.
Definition WI_f16 (x: val) : list init_data := match x with Vint i => [Init_int16 i] | _ => [] end.

Lemma WI_uint_el gv sh: WI_El gv sh tuint WI_f32 WI_isint.
Proof.
  intros x q Hok Hfc. destruct x; try discriminate.
  simpl. rewrite sepcon_emp. rewrite <- (mapsto_data_at' sh tuint (Vint i) (Vint i) q) by auto; apply derives_refl.
Qed.

Lemma WI_uchar_el gv sh: WI_El gv sh tuchar WI_f8 WI_u8ok.
Proof.
  intros x q Hok Hfc. destruct x; try discriminate.
  simpl in Hok. apply Int.same_if_eq in Hok.
  simpl. rewrite sepcon_emp, Hok. rewrite <- (mapsto_data_at' sh tuchar (Vint i) (Vint i) q) by auto; apply derives_refl.
Qed.

Lemma WI_short_el gv sh: WI_El gv sh tshort WI_f16 WI_s16ok.
Proof.
  intros x q Hok Hfc. destruct x; try discriminate.
  simpl in Hok. apply Int.same_if_eq in Hok.
  simpl. rewrite sepcon_emp.
  change (Int.zero_ext 16 i) with (Cop.cast_int_int I16 Unsigned i).
  rewrite (mapsto_unsigned_signed Unsigned Signed). simpl Cop.cast_int_int. rewrite Hok.
  rewrite <- (mapsto_data_at' sh tshort (Vint i) (Vint i) q) by auto; apply derives_refl.
Qed.

Lemma WI_uint_sz: WI_Sz tuint WI_f32 WI_isint.
Proof. intros x Hok. destruct x; try discriminate; reflexivity. Qed.
Lemma WI_uchar_sz: WI_Sz tuchar WI_f8 WI_u8ok.
Proof. intros x Hok. destruct x; try discriminate; reflexivity. Qed.
Lemma WI_short_sz: WI_Sz tshort WI_f16 WI_s16ok.
Proof. intros x Hok. destruct x; try discriminate; reflexivity. Qed.

End Generic.

(* a scalar-array global: globs2pred gv (i, Gvar v) |-- data_at sh (tarray t n) vs (gv i).
   NB: no vm_compute on goals that mention the compspecs (it evaluates the composite env's proofs and
   hangs); compute / reflexivity are fast. *)
Ltac WI_arr :=
  lazymatch goal with
  | |- globs2pred _ _ |-- @data_at ?cs _ (tarray ?t _) _ _ =>
      let F := lazymatch t with tuint => constr:(WI_f32) | tuchar => constr:(WI_f8) | tshort => constr:(WI_f16) end in
      let O := lazymatch t with tuint => constr:(WI_isint) | tuchar => constr:(WI_u8ok) | tshort => constr:(WI_s16ok) end in
      eapply (@WI_glob cs _ _ _ t _ F O);
      [ reflexivity
      | first [apply WI_uint_sz | apply WI_uchar_sz | apply WI_short_sz]
      | first [apply WI_uint_el | apply WI_uchar_el | apply WI_short_el]
      | reflexivity | reflexivity | reflexivity
      | reflexivity | compute; reflexivity | compute; reflexivity
      | apply la_env_cs_sound; compute; reflexivity ]
  end.

(* a zero-initialised global: data_at of zero_val *)
Ltac WI_zero_tac :=
  lazymatch goal with
  | |- globs2pred _ _ |-- @data_at ?cs _ ?t _ _ =>
      eapply (@WI_zero cs _ _ _ t);
        [ reflexivity | reflexivity | compute; reflexivity | compute; reflexivity | compute; reflexivity
        | compute; reflexivity | apply la_env_cs_sound; compute; reflexivity ]
  end.

(* a zero-initialised global as data_at_ *)
Ltac WI_space :=
  lazymatch goal with
  | |- globs2pred _ _ |-- @data_at_ ?cs ?sh ?t ?p =>
      apply derives_trans with (@data_at cs sh t (zero_val t) p); [WI_zero_tac | apply data_at_data_at_ ]
  end.
