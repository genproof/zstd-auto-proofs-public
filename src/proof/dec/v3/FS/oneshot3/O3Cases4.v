(* FS3 one-shot: with the selection (refMultipleDDicts and a set): how the caller's DDict memory
   (Spec_api6 dict_res + set_res) becomes MultiFrame3's (set_full + the argument's), and the claims *)
Require Import Zstd.proof.dec.v3.FS.FSOblig3 Zstd.proof.dec.v3.FS.oneshot3.O3Base Zstd.proof.dec.v3.FS.oneshot3.O3DCtxDef Zstd.proof.dec.v3.FS.oneshot3.O3ModelWalk Zstd.proof.dec.v3.FS.oneshot3.O3ModelPsel.
Local Open Scope logic.

Section CM_O3Cases4_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Section Res.
Variable DENT : dent_pred.
Variables (gv: globals) (shk: share).

(* every DDict of the set *)
Definition all_res (l: list (val * ddict_st)) : mpred :=
  fold_right sepcon emp (map (fun e => ddict_res (DD3x DENT) gv shk (fst e) (snd e)) l).

Lemma set_res_none (l: list (val * ddict_st)) cur :
  cur_ddict cur = None -> set_res (DD3x DENT) gv shk l cur = all_res l.
Proof. intros H. unfold set_res, all_res. rewrite H. reflexivity. Qed.

Lemma set_res_some (l: list (val * ddict_st)) cur q :
  cur_ddict cur = Some q -> set_res (DD3x DENT) gv shk l cur = set_full DENT gv shk l q.
Proof. intros H. unfold set_res, set_full. rewrite H. reflexivity. Qed.

Lemma set_full_notin (l: list (val * ddict_st)) q :
  ~ In q (map fst l) -> set_full DENT gv shk l q = all_res l.
Proof.
  induction l as [ | e l IH]; intros Hn; [reflexivity | ].
  unfold set_full, all_res in *. simpl in *. rewrite IH by tauto.
  destruct (Val.eq (fst e) q); [tauto | reflexivity].
Qed.

Lemma all_res_split (l: list (val * ddict_st)) q dd :
  NoDup (map fst l) -> In (q, dd) l -> all_res l = ddict_res (DD3x DENT) gv shk q dd * set_full DENT gv shk l q.
Proof.
  induction l as [ | e l IH]; intros Hnd Hin; [contradiction | ].
  simpl in Hnd. inv Hnd. unfold all_res, set_full in *. simpl.
  destruct Hin as [E | Hin].
  - subst e. simpl. destruct (Val.eq q q); [ | congruence]. rewrite emp_sepcon.
    f_equal. fold (all_res l). symmetry. apply set_full_notin. exact H1.
  - rewrite (IH H2 Hin).
    destruct (Val.eq (fst e) q) as [E | E].
    + exfalso. apply H1. rewrite E. apply in_map_iff. exists (q, dd); auto.
    + apply pred_ext; cancel; apply derives_refl.
Qed.

(* the argument q (a DDict of the set, entry dd) out of the caller's memory, the context's dictionary cur being a
   DDict of the set described like the set's entry, or not one of the set *)
Lemma res_regroup (l: list (val * ddict_st)) (cur: option dictref) q dd :
  NoDup (map fst l) -> In (q, dd) l ->
  (forall dr q0 dd0 dd', cur = Some dr -> dr_src dr = DSDDict q0 dd0 -> In (q0, dd') l -> dd' = dd0) ->
  exists R0, dict_res (DD3x DENT) gv shk cur * set_res (DD3x DENT) gv shk l cur =
             ddict_res (DD3x DENT) gv shk q dd * set_full DENT gv shk l q * R0.
Proof.
  intros Hnd Hin Hcur.
  destruct (cur_ddict cur) as [q0 | ] eqn:Ec.
  - rewrite (set_res_some l cur q0 Ec).
    destruct (in_dec Val.eq q0 (map fst l)) as [Hq0 | Hq0].
    + apply in_map_iff in Hq0. destruct Hq0 as [[q1 dd1] [E1 Hin1]]. simpl in E1. subst q1.
      destruct cur as [[[pk | | q2 dd2] raw once b] | ]; simpl in Ec; try discriminate. inv Ec.
      assert (dd1 = dd2) by (eapply Hcur; [reflexivity | reflexivity | exact Hin1]). subst dd1.
      exists emp. simpl dict_res. rewrite sepcon_emp.
      rewrite <- (all_res_split l q dd Hnd Hin), (all_res_split l q0 dd2 Hnd Hin1). apply pred_ext; cancel.
    + exists (dict_res (DD3x DENT) gv shk cur). rewrite (set_full_notin l q0 Hq0), (all_res_split l q dd Hnd Hin).
      apply pred_ext; cancel.
  - rewrite (set_res_none l cur Ec). exists (dict_res (DD3x DENT) gv shk cur).
    rewrite (all_res_split l q dd Hnd Hin). apply pred_ext; cancel.
Qed.

(* the loads of the set's DDicts *)
Lemma ddict_res_ld q dd : ddict_res (DD3_of DENT) gv shk q dd |-- !! ld_rel (dd_bytes dd) (dd_ld dd).
Proof.
  unfold ddict_res, DD3_of, ddict_rep_at, ddict_struct. Intros. apply prop_right.
  match goal with H: ld_rel _ _ |- _ => exact H end.
Qed.

Lemma set_full_ld (l: list (val * ddict_st)) q0 :
  set_full DENT gv shk l q0 |-- !! Forall (fun e => fst e <> q0 -> ld_rel (dd_bytes (snd e)) (dd_ld (snd e))) l.
Proof.
  induction l as [ | e l IH]; [apply prop_right; constructor | ].
  unfold set_full in *. simpl.
  destruct (Val.eq (fst e) q0) as [E | E].
  - rewrite emp_sepcon. eapply derives_trans; [exact IH | ]. apply prop_derives. intros H. constructor; auto.
    intros Hn; contradiction.
  - sep_apply (ddict_res_ld (fst e) (snd e)). Intros. sep_apply IH. Intros. apply prop_right.
    constructor; auto.
Qed.

End Res.

(* the claims with the selection, from MultiFrame's (under the probe's selection) *)
Lemma model_sel (st: dctx_st) (k: cst3) (tbl: list val) (cur: option dict_model) (s: list Z) (cap r: Z)
    (out: list val) :
  hs_probe_ok -> hs_inv (c3_set k) tbl -> Forall (fun e => ld_rel (dd_bytes (snd e)) (dd_ld (snd e))) (c3_set k) ->
  c3_par k = dc_par st -> c3_set k = dc_set st -> c3_set k <> nil -> bytes_ok s ->
  oneshot_sel (dmode_of (c3_par k)) (psel (c3_set k) tbl) cur s cap r out -> oneshot_dctx st s cap r out.
Proof.
  intros Hp Hi Hld Hpar Hset Hn Hb Ho. rewrite Hpar, Hset in *.
  unfold oneshot_dctx. destruct (dc_set st) as [ | e l] eqn:E; [contradiction | ].
  unfold st_sel. rewrite E.
  destruct (dc_dict st) as [dr | ]; [ | apply (proj1 o3_walk_facts _ _ _ _ _ _ _ Ho)].
  match goal with |- context [if ?c then _ else _] => destruct c eqn:Ec end;
    [ | apply (proj1 o3_walk_facts _ _ _ _ _ _ _ Ho)].
  apply andb_prop in Ec. destruct Ec as [Ec _]. apply andb_prop in Ec. destruct Ec as [_ Ec].
  apply (proj2 (proj2 o3_walk_facts) _ _ (psel (e :: l) tbl) cur); auto.
  intros id Hid. apply psel_set_sel; auto.
Qed.

(* ... and from MultiFrame's without a DDict argument (no selection in C): only without a configured dictionary,
   or when the parameter / set make st_sel the empty selection *)
Lemma model_null (st: dctx_st) (s: list Z) (cap r: Z) (out: list val) :
  dc_set st <> nil ->
  (forall dr, dc_dict st = Some dr ->
     match dr_src dr with DSDDict _ _ => false | _ => Nat.eqb (length (dr_bytes dr)) 0 end = true) ->
  oneshot_ok (dmode_of (dc_par st)) (Some no_dict) s cap r out -> oneshot_dctx st s cap r out.
Proof.
  intros Hn Hd Ho. unfold oneshot_dctx. destruct (dc_set st) as [ | e l] eqn:E; [contradiction | ].
  assert (Hs: st_sel st = (sel_none, None)).
  { unfold st_sel. rewrite E. destruct (dc_dict st) as [dr | ]; [ | reflexivity].
    specialize (Hd dr eq_refl). destruct (dr_src dr); try discriminate; rewrite Hd; simpl;
      rewrite andb_false_r; reflexivity. }
  rewrite Hs. simpl. apply (proj1 (proj2 o3_walk_facts) _ no_dict). exact Ho.
Qed.

End CM_O3Cases4_1.
