(* FS3 streaming, case zdss_loadHeader, piece C, segment s9: helpers and the case getDDict = NULL. *)
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3C_lib.
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3C_s9d.
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3C2_s10_lib.
Local Open Scope logic.

Section CM_LH3C2_s9n_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma lhC9_rel_uses od d : dict_rel3_of od d -> df_uses d = -1 \/ df_uses d = 0 \/ df_uses d = 1.
Proof.
  unfold dict_rel3_of. destruct od as [dr | ]; [ | intros [H _]; rewrite H; auto].
  destruct (dr_src dr); intros H.
  - destruct (Zlength (dr_bytes dr) =? 0).
    + destruct H as (_ & _ & H); rewrite H; destruct (dr_once dr); auto.
    + destruct H as (_ & _ & H & _); rewrite H; destruct (dr_once dr); auto.
  - destruct H as [_ H]. destruct (Zlength (dr_bytes dr) =? 0).
    + subst d; simpl; auto.
    + destruct H as (? & ? & ? & _ & _ & H & _); rewrite H; auto.
  - destruct H as (_ & _ & _ & _ & _ & H & _); rewrite H; auto.
Qed.

Lemma lhC9_rel_ddict od d : dict_rel3_of od d -> df_uses d <> 0 -> is_pointer_or_null (df_ddict d).
Proof.
  unfold dict_rel3_of. destruct od as [dr | ]; [ | intros [H _]; rewrite H; congruence].
  destruct (dr_src dr) as [pk | | q dd]; intros H Hu.
  - destruct (Zlength (dr_bytes dr) =? 0).
    + destruct H as (_ & H & _); rewrite H; simpl; auto.
    + destruct H as (Hp & H & _); rewrite H; destruct (df_local d); simpl in *; tauto.
  - destruct H as [_ H]. destruct (Zlength (dr_bytes dr) =? 0).
    + subst d; simpl; auto.
    + destruct H as (? & ? & ? & Hp & H & _); rewrite H; destruct (df_local d); simpl in *; tauto.
  - destruct H as (_ & _ & Hq & _ & H & _); rewrite H; destruct q; simpl in *; tauto.
Qed.

(* the dictionary fields after piece A's selection: Spec_api6's dictionary or a member of the set *)
Lemma lhC9_d1 (a: dsa) (w: lw) (hb: list Z) (h: frame_header) (tbl: list val) (d1: dfields) (did1: val) :
  hs_probe_ok -> lh_entry a w hb -> lhA_sel (w_k w) hb 0 (fh_val h) tbl d1 did1 ->
  Forall (fun e => isptr (fst e)) (dc_set (a_st a)) ->
  dict_rel3 (a_st a) d1 /\ (df_uses d1 = -1 \/ df_uses d1 = 0 \/ df_uses d1 = 1) /\
  (df_uses d1 <> 0 -> is_pointer_or_null (df_ddict d1)).
Proof.
intros Hpr He (_ & _ & id & _ & Hsb) Hfa.
destruct He as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hbc & _).
destruct Hbc as (_ & _ & Hset & Hrel & _).
assert (Hgen: dict_rel3 (a_st a) (c3_dict (w_k w)) ->
  dict_rel3 (a_st a) (c3_dict (w_k w)) /\
  (df_uses (c3_dict (w_k w)) = -1 \/ df_uses (c3_dict (w_k w)) = 0 \/ df_uses (c3_dict (w_k w)) = 1) /\
  (df_uses (c3_dict (w_k w)) <> 0 -> is_pointer_or_null (df_ddict (c3_dict (w_k w))))).
{ intros Hr. split; [exact Hr |].
  destruct Hr as [Hr | (_ & Hl & Hu & _ & Hin)].
  - split; [eapply lhC9_rel_uses; eauto | eapply lhC9_rel_ddict; eauto].
  - rewrite Hu. split; [auto |]. intros _.
    apply list_in_map_inv in Hin. destruct Hin as [e [-> Hin]].
    rewrite Forall_forall in Hfa. specialize (Hfa e Hin). destruct (fst e); try contradiction; simpl; auto. }
unfold sel_by in Hsb. destruct (sel_on (c3_par (w_k w)) (c3_sp (w_k w))).
- destruct Hsb as (Hinv & Hid & Hd1 & _).
  unfold sel_dict in Hd1. destruct (eq_dec (sel_r (c3_dict (w_k w)) (c3_set (w_k w)) tbl id) nullval) as [E | E].
  + subst d1. apply Hgen; exact Hrel.
  + subst d1. unfold sel_r in *.
    destruct (eq_dec (df_ddict (c3_dict (w_k w))) nullval); [contradiction |].
    destruct (Hpr _ _ _ Hinv Hid) as [[Hn | Hin] _]; [contradiction |].
    assert (Hp: isptr (hs_probe (c3_set (w_k w)) tbl id)).
    { destruct Hinv as (_ & _ & _ & _ & _ & Hfa2 & _).
      apply list_in_map_inv in Hin. destruct Hin as [e [-> Hin]].
      rewrite Forall_forall in Hfa2. apply Hfa2; exact Hin. }
    split; [| split].
    * right. rewrite <- Hset. split.
      { intros En. rewrite En in Hin. contradiction. }
      unfold dict_switched, switch_fields; cbn. auto.
    * cbn. auto.
    * cbn. intros _. destruct (hs_probe (c3_set (w_k w)) tbl id); try contradiction; simpl; auto.
- destruct Hsb as (-> & _). apply Hgen; exact Hrel.
Qed.

Lemma hset_t_isptr (am: option cmem) (sp: val) (l: list (val * ddict_st)) (hb: Z) (tbl: list val) :
  hset_t am sp l hb tbl |-- !! (Forall (fun e => isptr (fst e)) l).
Proof.
unfold hset_t, hset_tbl. destruct (eq_dec sp nullval).
- Intros. subst l. apply prop_right; constructor.
- Intros tp. apply prop_right. match goal with H: hs_inv _ _ |- _ => destruct H as (_ & _ & _ & _ & _ & Hfa & _) end.
  exact Hfa.
Qed.

(* the set's DDicts are pointers, and the set holds a nonnegative number of the allocator's bytes *)
Lemma hset_t_isptr' (am: option cmem) (sp: val) (l: list (val * ddict_st)) (hb: Z) (tbl: list val) :
  hset_t am sp l hb tbl |-- !! (Forall (fun e => isptr (fst e)) l) && !! (0 <= hb) && hset_t am sp l hb tbl.
Proof.
apply andp_right; [apply andp_right; [apply hset_t_isptr | apply hset_t_held] | apply derives_refl].
Qed.

Lemma tabs_uninit_of3 (TABS: tabs_pred) (gv: globals) (p: val) (t: tabs3) : TABS_OK TABS ->
  match t with TInit ox ts => TABS gv p ox ts | TUninit lxb => tables_uninit p lxb end |--
  EX lxb: list Z, !! (lxb = tabs_lxb t) && tables_uninit p lxb.
Proof.
intros HT. destruct t as [lxb|ox ts]; [Exists lxb | Exists (ts_lxb ts)]; (apply andp_right; [apply prop_right; reflexivity |]);
  [apply derives_refl | apply HT].
Qed.

(* do { c } while (0) *)
Lemma semax_dowhile0_gen3 : forall {CS: compspecs} {Espec: OracleKind} Delta P c R,
  semax Delta P c (loop1_ret_assert (RA_normal R) R) -> semax Delta P (Sloop c Sbreak) R.
Proof.
intros CS Espec Delta P c R H.
apply semax_loop with (Q' := RA_normal R); auto.
eapply semax_pre; [| apply semax_break]. destruct R; simpl; intros; apply andp_left2; auto.
Qed.

(* the common start: getDDict *)
Lemma lhC_seg9_none : forall (Espec: OracleKind) DENT TABS BR (a: dsa) (w: lw) (hb: list Z) (h: frame_header)
    (tbl: list val) (d1: dfields) (did1: val),
  lhC_hyps DENT TABS a w hb h tbl d1 did1 -> fst (getddict_res d1) = nullval ->
  let k1 := k_A (w_k w) (fh_val h) d1 did1 in
  semax (ds_Delta DENT TABS BR) (lhC_S1 DENT TABS a w k1 h tbl) lhC_s9
    (overridePost (lhC_S2 DENT TABS a w k1 h tbl) (lhC_post DENT TABS a w hb h k1)).
Proof.
intros Espec DENT TABS BR a w hb h tbl d1 did1 HP Hn.
set (k1 := k_A (w_k w) (fh_val h) d1 did1).
destruct HP as (Hsel & Hbeg & Hpr & HD & HT & Ha & He & Hs & Hg & Hf & HA).
unfold lhC_S1, lhC_post. lhC9_Delta DENT TABS BR. unfold lhC_s9, ds_LI_L. abbreviate_semax.
unfold ds_LI_St, ctx_rep3t, fgroup3, tabs_rep. Intros. cbn [lw_k w_k w_opc w_ipc w_smw w_oc].
sep_apply (hset_t_isptr' (sf_mem (c3_s k1)) (c3_sp k1) (c3_set k1) (sf_held (c3_s k1) - local_held (c3_dict k1)) tbl).
Intros.
assert (Hbc := He). destruct Hbc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hbc & _).
destruct Hbc as (_ & _ & Hset & Hrel & Hcur & _ & (_ & _ & Hlm0)).
assert (Hsdo: stream_dict_ok (a_W a) (a_st a)) by (destruct Ha as (_ & _ & _ & _ & _ & _ & _ & X & _); exact X).
assert (Hset1: c3_set k1 = dc_set (a_st a)) by exact Hset.
match goal with Hx: Forall _ (c3_set k1) |- _ => rename Hx into Hfa end.
match goal with Hx: 0 <= sf_held _ - _ |- _ => rename Hx into Hh0 end.
rewrite Hset1 in Hfa.
destruct (lhC9_d1 a w hb h tbl d1 did1 Hpr He HA Hfa) as (Hd1 & Hu & Hpn).
match goal with Hx: cold01 _ |- _ => rename Hx into Hcold end.
match goal with Hx: par_ok _ |- _ => rename Hx into Hpar end.
sep_apply (tabs_uninit_of3 TABS (a_gv a) (a_d a) (c3_tabs k1) HT). Intros lxb.
match goal with Hx: lxb = tabs_lxb _ |- _ => rename Hx into Hlxb end.
apply semax_dowhile0_gen3.
match goal with |- semax _ _ _ ?Q =>
  let Q' := eval cbv beta iota delta [overridePost loop1_ret_assert] in Q in change Q with Q' end.
change (c3_dict k1) with d1 in *.
assert (Hlm: local_mem (sf_mem (c3_s k1)) d1)
  by exact (local_mem_redict _ _ _ (lhA_sel_redict _ _ _ _ _ _ _ HA) Hlm0).
sep_apply (lhC_sg_take (a_d a) (c3_s k1) d1 Hh0). Intros.
forward_call (a_gv a, a_d a, d1, sf_mem (c3_s k1), sf_given (c3_s k1) - local_held d1).
rewrite Hn.
forward_call (a_gv a, a_d a, c3_fs k1, a_W a, @None ddx, nullval, dp_fmt (c3_par k1), lxb).
{ cancel. }
{ exact (proj1 Hpar). }
Intros cold.
forward. forward_call 0. forward_if.
{ exfalso. match goal with H: Int.repr _ <> Int.zero |- _ => apply H; reflexivity end. }
forward.
unfold lhC_S2. Exists (@None (ddx * val)) (fs_ddictIsCold (c3_fs k1)) lxb.
unfold ds_LI_St, ctx_rep3t, fgroup3, tabs_rep, ds_LI_L.
cbn [lw_k w_k w_opc w_ipc w_smw w_oc lhC_kx c3_fs c3_tabs c3_stable c3_dict c3_s c3_par c3_sp c3_set lh_dd_fs
     dd_ox option_map lhC_dd lh_dd_ts].
change (c3_dict k1) with d1.
rewrite lhC_hr_mem, held_redict_set.
match goal with Hx: cmem_ok _ |- _ => sep_apply (lhC_sg_put (a_d a) (c3_s k1) d1 (snd (getddict_res d1)) Hh0 Hx) end.
entailer!.
Time Qed.

End CM_LH3C2_s9n_1.
