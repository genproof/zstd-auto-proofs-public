(* FS3 set part: helpers of the body of ZSTD_DDictHashSet_emplaceDDict (SetBodyEmplace.v): arithmetic of the probe,
   the table accesses as lemmas, the loop's invariant and exit. *)
Require Import Zstd.proof.dec.v3.FS.set.SetDefs.
Local Open Scope logic.

Section CM_SetEmplaceAux_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma emp_land_mod (a n k: Z) : 0 <= k -> n = 2 ^ k -> Z.land a (n - 1) = a mod n.
Proof.
  intros Hk ->. replace (2 ^ k - 1) with (Z.ones k) by (rewrite Z.ones_equiv; lia). apply Z.land_ones; lia.
Qed.

Lemma emp_home_range (id n k: Z) : 0 <= k -> n = 2 ^ k -> 0 <= hs_home id n < n.
Proof.
  intros Hk Hn. unfold hs_home. rewrite (emp_land_mod _ n k) by auto.
  apply Z.mod_pos_bound. subst; apply Z.pow_pos_nonneg; lia.
Qed.

Lemma emp_slot_range (h t n: Z) : 0 < n -> 0 <= hs_slot h t n < n.
Proof. intros. unfold hs_slot. apply Z.mod_pos_bound; lia. Qed.

Lemma emp_slot_next (h t n: Z) : 0 < n -> hs_slot h (t + 1) n = (hs_slot h t n + 1) mod n.
Proof. intros. unfold hs_slot. rewrite Z.add_mod_idemp_l by lia. f_equal; lia. Qed.

Lemma emp_slot0 (h n: Z) : 0 <= h < n -> hs_slot h 0 n = h.
Proof. intros. unfold hs_slot. rewrite Z.add_0_r. apply Z.mod_small; auto. Qed.

Lemma emp_pon (v: val) : v = nullval \/ isptr v -> is_pointer_or_null v.
Proof. intros [-> | H]; [simpl; auto | destruct v; try contradiction; exact I]. Qed.

Lemma emp_next_idx (j n k: Z) : 0 <= k -> n = 2 ^ k -> n <= 2 ^ 30 -> 0 <= j < n ->
  Int64.and (Int64.add (Int64.repr j) (Int64.repr 1)) (Int64.repr (n - 1)) = Int64.repr ((j + 1) mod n).
Proof.
  intros Hk Hn Hn30 Hj.
  assert (2 ^ 30 < Int64.max_unsigned) by (cbn; lia).
  assert (0 < n) by (subst; apply Z.pow_pos_nonneg; lia).
  unfold Int64.and, Int64.add. rewrite (Int64.unsigned_repr j) by lia. rewrite (Int64.unsigned_repr 1) by rep_lia.
  rewrite (Int64.unsigned_repr (j + 1)) by lia. rewrite (Int64.unsigned_repr (n - 1)) by lia. rewrite (emp_land_mod _ n k) by auto. reflexivity.
Qed.

(* one more probe: slot t holds a DDict of another ID; the table's NULL slot is further on *)
Lemma emp_step (l: list (val * ddict_st)) (tbl: list val) (n h t id: Z) : PF_notfull ->
  hs_inv0 l tbl -> n = Zlength tbl -> 0 <= h < n -> 0 <= t < n ->
  (forall t', 0 <= t' < t -> Znth (hs_slot h t' n) tbl <> nullval /\ set_id_of l (Znth (hs_slot h t' n) tbl) <> id) ->
  Znth (hs_slot h t n) tbl <> nullval -> set_id_of l (Znth (hs_slot h t n) tbl) <> id ->
  0 <= t + 1 < n /\
  (forall t', 0 <= t' < t + 1 -> Znth (hs_slot h t' n) tbl <> nullval /\ set_id_of l (Znth (hs_slot h t' n) tbl) <> id).
Proof.
  intros Pnf Hinv Hn Hh Ht Hall Hz Hi. subst n.
  destruct (Pnf l tbl h Hinv Hh) as [t0 [Ht0 Hz0]].
  assert (t < t0).
  { destruct (Z_lt_le_dec t t0) as [|Hle]; auto. exfalso.
    destruct (Z.eq_dec t0 t) as [->|Hne]; [contradiction|]. apply (proj1 (Hall t0 ltac:(lia))); auto. }
  split; [lia|]. intros t' Ht'. destruct (Z.eq_dec t' t) as [->|]; [auto | apply Hall; lia].
Qed.

Lemma emp_replace (l: list (val * ddict_st)) (tbl: list val) (q: val) (dd: ddict_st) (t n h: Z) : PF_replace ->
  n = Zlength tbl -> h = hs_home (dd_id dd) n ->
  hs_inv0 l tbl -> isptr q -> ~ In q (map fst l) -> 0 <= t < n ->
  Znth (hs_slot h t n) tbl <> nullval -> set_id_of l (Znth (hs_slot h t n) tbl) = dd_id dd ->
  Zlength (set_add l q dd) = Zlength l /\ hs_inv0 (set_add l q dd) (upd_Znth (hs_slot h t n) tbl q).
Proof. intros P -> ->. apply P. Qed.

Lemma emp_insert (l: list (val * ddict_st)) (tbl: list val) (q: val) (dd: ddict_st) (t n h: Z) : PF_insert ->
  n = Zlength tbl -> h = hs_home (dd_id dd) n ->
  hs_inv0 l tbl -> Zlength l + 1 < n -> isptr q -> ~ In q (map fst l) -> 0 <= t < n ->
  Znth (hs_slot h t n) tbl = nullval ->
  (forall t', 0 <= t' < t ->
     Znth (hs_slot h t' n) tbl <> nullval /\ set_id_of l (Znth (hs_slot h t' n) tbl) <> dd_id dd) ->
  set_add l q dd = l ++ [(q, dd)] /\ hs_inv0 (l ++ [(q, dd)]) (upd_Znth (hs_slot h t n) tbl q).
Proof. intros P -> ->. apply P. Qed.

Transparent denote_tc_test_eq.
Lemma emp_tc_null (v: val) (R: mpred) :
  isptr v -> weak_valid_pointer v * R |-- denote_tc_test_eq v (Vlong (Int64.repr 0)).
Proof.
  intros Hv. destruct v; try contradiction. unfold denote_tc_test_eq; simpl.
  apply andp_right; [apply prop_right; reflexivity |].
  apply sepcon_weak_valid_pointer1. apply derives_refl.
Qed.
Opaque denote_tc_test_eq.

(* ---------- the table accesses, proved apart: done by forward inside the body, their kernel check exceeds
   10 minutes (the body's context); stated with the function's tycontext and framed with semax_frame_PQR ---------- *)

Lemma emp_closed_assign (e1 e2: expr) (F: environ -> mpred) : closed_wrt_modvars (Sassign e1 e2) F.
Proof.
  unfold closed_wrt_modvars, closed_wrt_vars. intros rho te' H. f_equal.
  destruct rho as [g v te]; simpl in *. f_equal. extensionality i.
  destruct (H i) as [Hm|E]; [| exact E]. exfalso. revert Hm. unfold modifiedvars. simpl. auto.
Qed.

Lemma emp_ld10_0 {Espec: OracleKind} (tp: val) (tbl: list val) (j n: Z) :
  0 <= j < n -> Zlength tbl = n -> Znth j tbl = nullval \/ isptr (Znth j tbl) ->
  semax (func_tycontext f_ZSTD_DDictHashSet_emplaceDDict Vprog G_emplace nil)
    (PROP () LOCAL (temp _t'9 tp; temp _idx (Vlong (Int64.repr j))) SEP (data_at Ews (tarray (tptr t_ddict) n) tbl tp))
    (Sset _t'10 (Ederef (Ebinop Oadd (Etempvar _t'9 (tptr (tptr (Tstruct _ZSTD_DDict_s noattr)))) (Etempvar _idx tulong) (tptr (tptr (Tstruct _ZSTD_DDict_s noattr)))) (tptr (Tstruct _ZSTD_DDict_s noattr))))
    (normal_ret_assert (PROP () LOCAL (temp _t'10 (Znth j tbl); temp _t'9 tp; temp _idx (Vlong (Int64.repr j)))
       SEP (data_at Ews (tarray (tptr t_ddict) n) tbl tp))).
Proof. intros. forward. { entailer!. apply emp_pon; exact H1. } entailer!. Qed.

Lemma emp_ld10 {Espec: OracleKind} (tp: val) (tbl: list val) (j n: Z) :
  0 <= j < n -> Zlength tbl = n -> Znth j tbl = nullval \/ isptr (Znth j tbl) ->
  forall (Q2: list localdef) (R2: list mpred),
  closed_wrt_modvars (Sset _t'10 (Ederef (Ebinop Oadd (Etempvar _t'9 (tptr (tptr (Tstruct _ZSTD_DDict_s noattr)))) (Etempvar _idx tulong) (tptr (tptr (Tstruct _ZSTD_DDict_s noattr)))) (tptr (Tstruct _ZSTD_DDict_s noattr)))) (LOCALx Q2 (SEPx R2)) ->
  semax (func_tycontext f_ZSTD_DDictHashSet_emplaceDDict Vprog G_emplace nil)
    (PROPx [] (LOCALx ([temp _t'9 tp; temp _idx (Vlong (Int64.repr j))] ++ Q2)
       (SEPx ([data_at Ews (tarray (tptr t_ddict) n) tbl tp] ++ R2))))
    (Sset _t'10 (Ederef (Ebinop Oadd (Etempvar _t'9 (tptr (tptr (Tstruct _ZSTD_DDict_s noattr)))) (Etempvar _idx tulong) (tptr (tptr (Tstruct _ZSTD_DDict_s noattr)))) (tptr (Tstruct _ZSTD_DDict_s noattr))))
    (normal_ret_assert (PROPx [] (LOCALx ([temp _t'10 (Znth j tbl); temp _t'9 tp; temp _idx (Vlong (Int64.repr j))] ++ Q2)
       (SEPx ([data_at Ews (tarray (tptr t_ddict) n) tbl tp] ++ R2))))).
Proof. intros. apply semax_frame_PQR; auto. apply emp_ld10_0; auto. Qed.

Lemma emp_ld8_0 {Espec: OracleKind} (tp: val) (tbl: list val) (j n: Z) :
  0 <= j < n -> Zlength tbl = n -> Znth j tbl = nullval \/ isptr (Znth j tbl) ->
  semax (func_tycontext f_ZSTD_DDictHashSet_emplaceDDict Vprog G_emplace nil)
    (PROP () LOCAL (temp _t'7 tp; temp _idx (Vlong (Int64.repr j))) SEP (data_at Ews (tarray (tptr t_ddict) n) tbl tp))
    (Sset _t'8 (Ederef (Ebinop Oadd (Etempvar _t'7 (tptr (tptr (Tstruct _ZSTD_DDict_s noattr)))) (Etempvar _idx tulong) (tptr (tptr (Tstruct _ZSTD_DDict_s noattr)))) (tptr (Tstruct _ZSTD_DDict_s noattr))))
    (normal_ret_assert (PROP () LOCAL (temp _t'8 (Znth j tbl); temp _t'7 tp; temp _idx (Vlong (Int64.repr j)))
       SEP (data_at Ews (tarray (tptr t_ddict) n) tbl tp))).
Proof. intros. forward. { entailer!. apply emp_pon; exact H1. } entailer!. Qed.

Lemma emp_ld8 {Espec: OracleKind} (tp: val) (tbl: list val) (j n: Z) :
  0 <= j < n -> Zlength tbl = n -> Znth j tbl = nullval \/ isptr (Znth j tbl) ->
  forall (Q2: list localdef) (R2: list mpred),
  closed_wrt_modvars (Sset _t'8 (Ederef (Ebinop Oadd (Etempvar _t'7 (tptr (tptr (Tstruct _ZSTD_DDict_s noattr)))) (Etempvar _idx tulong) (tptr (tptr (Tstruct _ZSTD_DDict_s noattr)))) (tptr (Tstruct _ZSTD_DDict_s noattr)))) (LOCALx Q2 (SEPx R2)) ->
  semax (func_tycontext f_ZSTD_DDictHashSet_emplaceDDict Vprog G_emplace nil)
    (PROPx [] (LOCALx ([temp _t'7 tp; temp _idx (Vlong (Int64.repr j))] ++ Q2)
       (SEPx ([data_at Ews (tarray (tptr t_ddict) n) tbl tp] ++ R2))))
    (Sset _t'8 (Ederef (Ebinop Oadd (Etempvar _t'7 (tptr (tptr (Tstruct _ZSTD_DDict_s noattr)))) (Etempvar _idx tulong) (tptr (tptr (Tstruct _ZSTD_DDict_s noattr)))) (tptr (Tstruct _ZSTD_DDict_s noattr))))
    (normal_ret_assert (PROPx [] (LOCALx ([temp _t'8 (Znth j tbl); temp _t'7 tp; temp _idx (Vlong (Int64.repr j))] ++ Q2)
       (SEPx ([data_at Ews (tarray (tptr t_ddict) n) tbl tp] ++ R2))))).
Proof. intros. apply semax_frame_PQR; auto. apply emp_ld8_0; auto. Qed.

Lemma emp_st6_0 {Espec: OracleKind} (tp q: val) (tbl: list val) (j n: Z) :
  0 <= j < n -> Zlength tbl = n -> isptr q ->
  semax (func_tycontext f_ZSTD_DDictHashSet_emplaceDDict Vprog G_emplace nil)
    (PROP () LOCAL (temp _t'6 tp; temp _idx (Vlong (Int64.repr j)); temp _ddict q)
       SEP (data_at Ews (tarray (tptr t_ddict) n) tbl tp))
    (Sassign (Ederef (Ebinop Oadd (Etempvar _t'6 (tptr (tptr (Tstruct _ZSTD_DDict_s noattr)))) (Etempvar _idx tulong) (tptr (tptr (Tstruct _ZSTD_DDict_s noattr)))) (tptr (Tstruct _ZSTD_DDict_s noattr))) (Etempvar _ddict (tptr (Tstruct _ZSTD_DDict_s noattr))))
    (normal_ret_assert (PROP () LOCAL (temp _t'6 tp; temp _idx (Vlong (Int64.repr j)); temp _ddict q)
       SEP (data_at Ews (tarray (tptr t_ddict) n) (upd_Znth j tbl q) tp))).
Proof. intros. forward. entailer!. Qed.

Lemma emp_st6 {Espec: OracleKind} (tp q: val) (tbl: list val) (j n: Z) :
  0 <= j < n -> Zlength tbl = n -> isptr q ->
  forall (Q2: list localdef) (R2: list mpred),
  semax (func_tycontext f_ZSTD_DDictHashSet_emplaceDDict Vprog G_emplace nil)
    (PROPx [] (LOCALx ([temp _t'6 tp; temp _idx (Vlong (Int64.repr j)); temp _ddict q] ++ Q2)
       (SEPx ([data_at Ews (tarray (tptr t_ddict) n) tbl tp] ++ R2))))
    (Sassign (Ederef (Ebinop Oadd (Etempvar _t'6 (tptr (tptr (Tstruct _ZSTD_DDict_s noattr)))) (Etempvar _idx tulong) (tptr (tptr (Tstruct _ZSTD_DDict_s noattr)))) (tptr (Tstruct _ZSTD_DDict_s noattr))) (Etempvar _ddict (tptr (Tstruct _ZSTD_DDict_s noattr))))
    (normal_ret_assert (PROPx [] (LOCALx ([temp _t'6 tp; temp _idx (Vlong (Int64.repr j)); temp _ddict q] ++ Q2)
       (SEPx ([data_at Ews (tarray (tptr t_ddict) n) (upd_Znth j tbl q) tp] ++ R2))))).
Proof. intros. apply semax_frame_PQR; [apply emp_closed_assign |]. apply emp_st6_0; auto. Qed.

Lemma emp_st5_0 {Espec: OracleKind} (tp q: val) (tbl: list val) (j n: Z) :
  0 <= j < n -> Zlength tbl = n -> isptr q ->
  semax (func_tycontext f_ZSTD_DDictHashSet_emplaceDDict Vprog G_emplace nil)
    (PROP () LOCAL (temp _t'5 tp; temp _idx (Vlong (Int64.repr j)); temp _ddict q)
       SEP (data_at Ews (tarray (tptr t_ddict) n) tbl tp))
    (Sassign (Ederef (Ebinop Oadd (Etempvar _t'5 (tptr (tptr (Tstruct _ZSTD_DDict_s noattr)))) (Etempvar _idx tulong) (tptr (tptr (Tstruct _ZSTD_DDict_s noattr)))) (tptr (Tstruct _ZSTD_DDict_s noattr))) (Etempvar _ddict (tptr (Tstruct _ZSTD_DDict_s noattr))))
    (normal_ret_assert (PROP () LOCAL (temp _t'5 tp; temp _idx (Vlong (Int64.repr j)); temp _ddict q)
       SEP (data_at Ews (tarray (tptr t_ddict) n) (upd_Znth j tbl q) tp))).
Proof. intros. forward. entailer!. Qed.

Lemma emp_st5 {Espec: OracleKind} (tp q: val) (tbl: list val) (j n: Z) :
  0 <= j < n -> Zlength tbl = n -> isptr q ->
  forall (Q2: list localdef) (R2: list mpred),
  semax (func_tycontext f_ZSTD_DDictHashSet_emplaceDDict Vprog G_emplace nil)
    (PROPx [] (LOCALx ([temp _t'5 tp; temp _idx (Vlong (Int64.repr j)); temp _ddict q] ++ Q2)
       (SEPx ([data_at Ews (tarray (tptr t_ddict) n) tbl tp] ++ R2))))
    (Sassign (Ederef (Ebinop Oadd (Etempvar _t'5 (tptr (tptr (Tstruct _ZSTD_DDict_s noattr)))) (Etempvar _idx tulong) (tptr (tptr (Tstruct _ZSTD_DDict_s noattr)))) (tptr (Tstruct _ZSTD_DDict_s noattr))) (Etempvar _ddict (tptr (Tstruct _ZSTD_DDict_s noattr))))
    (normal_ret_assert (PROPx [] (LOCALx ([temp _t'5 tp; temp _idx (Vlong (Int64.repr j)); temp _ddict q] ++ Q2)
       (SEPx ([data_at Ews (tarray (tptr t_ddict) n) (upd_Znth j tbl q) tp] ++ R2))))).
Proof. intros. apply semax_frame_PQR; [apply emp_closed_assign |]. apply emp_st5_0; auto. Qed.

End CM_SetEmplaceAux_1.

Ltac emp_rm_tbl l :=
  lazymatch l with
  | (@data_at _ _ (tarray _ _) _ _) :: ?r => r
  | ?a :: ?r => let r' := emp_rm_tbl r in constr:(a :: r')
  end.

Ltac emp_rm_temp i Q :=
  lazymatch Q with
  | temp i _ :: ?r => emp_rm_temp i r
  | ?a :: ?r => let r' := emp_rm_temp i r in constr:(a :: r')
  | _ => Q
  end.

(* run the table access L (a lemma above, applied to its values and facts) on the first statement: the frame is the
   LOCAL without the temps i1 i2 i3 (those of L's precondition) and the SEP without the table *)
Ltac emp_access L i1 i2 i3 :=
  repeat match goal with |- semax _ _ (Ssequence (Ssequence _ _) _) _ => apply -> seq_assoc end;
  match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?R))) (Ssequence _ _) _ =>
    let R2 := emp_rm_tbl R in
    let Q1 := emp_rm_temp i1 Q in let Q2 := emp_rm_temp i2 Q1 in let Q3 := emp_rm_temp i3 Q2 in
    eapply semax_seq'; [eapply semax_pre; [| apply (L Q3 R2)]; [simpl app; entailer! | ..]
                       | simpl app; try (match goal with |- semax _ _ ?M _ => is_var M; unfold M, abbreviate end); abbreviate_semax]
  end.

Section CM_SetEmplaceAux_2.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.

(* an equation hidden from VST's automation (it would substitute it and compute xxh64) *)
Definition emp_hide (P: Prop) : Prop := P.

(* the probing loop of ZSTD_DDictHashSet_emplaceDDict: its body, invariant (t probes done, none of the ID) and exit (a NULL
   slot after t probes), the function's postcondition (n = |tbl|, h = q's home slot) *)
Definition emp_LB : statement :=
  ltac:(let b := eval cbv beta iota zeta delta [f_ZSTD_DDictHashSet_emplaceDDict fn_body] in
          (fn_body f_ZSTD_DDictHashSet_emplaceDDict) in
        lazymatch b with context [Sloop ?x Sskip] => exact x end).

Definition emp_inv (sp tp: val) (L l: list (val * ddict_st)) (tbl: list val) (q: val) (dd: ddict_st) (n h: Z)
    : environ -> mpred := (
  EX t: Z,
    PROP (0 <= t < n; forall t', 0 <= t' < t -> Znth (hs_slot h t' n) tbl <> nullval /\
            set_id_of l (Znth (hs_slot h t' n) tbl) <> dd_id dd)
    LOCAL (temp _idxRangeMask (Vlong (Int64.repr (n - 1))); temp _idx (Vlong (Int64.repr (hs_slot h t n)));
           temp _dictID (Vint (Int.repr (dd_id dd))); temp _hashSet sp; temp _ddict q)
    SEP (set_ids L; data_at Ews t_hset (tp, (Vlong (Int64.repr n), Vlong (Int64.repr (Zlength l)))) sp;
         data_at Ews (tarray (tptr t_ddict) n) tbl tp))%assert.

Definition emp_brk (sp tp: val) (L l: list (val * ddict_st)) (tbl: list val) (q: val) (dd: ddict_st) (n h: Z)
    : environ -> mpred := (
  EX t: Z,
    PROP (0 <= t < n; Znth (hs_slot h t n) tbl = nullval; forall t', 0 <= t' < t ->
            Znth (hs_slot h t' n) tbl <> nullval /\ set_id_of l (Znth (hs_slot h t' n) tbl) <> dd_id dd)
    LOCAL (temp _idx (Vlong (Int64.repr (hs_slot h t n))); temp _hashSet sp; temp _ddict q)
    SEP (set_ids L; data_at Ews t_hset (tp, (Vlong (Int64.repr n), Vlong (Int64.repr (Zlength l)))) sp;
         data_at Ews (tarray (tptr t_ddict) n) tbl tp))%assert.

Definition emp_post (sp tp: val) (L l: list (val * ddict_st)) (q: val) (dd: ddict_st) (n: Z) : environ -> mpred := (
  EX tbl': list val,
    PROP (hs_inv0 (set_add l q dd) tbl'; Zlength tbl' = n)
    RETURN (Vlong (Int64.repr 0))
    SEP (data_at Ews t_hset (tp, (Vlong (Int64.repr n), Vlong (Int64.repr (Zlength (set_add l q dd))))) sp;
         data_at Ews (tarray (tptr t_ddict) n) tbl' tp; set_ids L))%assert.

End CM_SetEmplaceAux_2.
