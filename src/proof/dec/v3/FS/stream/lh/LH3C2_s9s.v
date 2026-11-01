(* FS3 streaming, case zdss_loadHeader, piece C, segment s9: the case getDDict <> NULL. *)
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3C_lib.
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3C_s9d.
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3C2_s9n.
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3C2_s10_lib.
Local Open Scope logic.

Section CM_LH3C2_s9s_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma lhC_seg9_some : forall (Espec: OracleKind) DENT TABS BR (a: dsa) (w: lw) (hb: list Z) (h: frame_header)
    (tbl: list val) (d1: dfields) (did1: val),
  lhC_hyps DENT TABS a w hb h tbl d1 did1 -> fst (getddict_res d1) <> nullval ->
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
assert (Hlm: local_mem (sf_mem (c3_s k1)) d1)
  by exact (local_mem_redict _ _ _ (lhA_sel_redict _ _ _ _ _ _ _ HA) Hlm0).
change (c3_dict k1) with d1 in Hh0.
sep_apply (lhC_sg_take (a_d a) (c3_s k1) d1 Hh0). Intros.
change (c3_dict k1) with d1.
forward_call (a_gv a, a_d a, d1, sf_mem (c3_s k1), sf_given (c3_s k1) - local_held d1).
pose proof (Hbeg DENT (a_gv a) (a_d a) (a_W a) (a_st a) k1 Hset1 Hd1 Hcur Hsdo Hn) as Hlend.
cbv zeta in Hlend. change (c3_dict k1) with d1 in Hlend.
sep_apply Hlend. Intros x buf.
match goal with H: lh_dd_ok _ _ _ _ |- _ => rename H into Hok end.
assert (Hq: dx_q x = fst (getddict_res d1)) by exact (proj1 Hok).
rewrite <- Hq.
forward_call (a_gv a, a_d a, c3_fs k1, a_W a, Some x, buf, dp_fmt (c3_par k1), lxb).
{ cancel. }
{ exact (proj1 Hpar). }
Intros cold.
sep_apply (modus_ponens_wand (ddict_struct x buf * DENT (a_gv a) (dx_q x) (ddx_ent x) * ddict_mem x buf)
  (dgroup DENT (a_gv a) (a_d a) (snd (getddict_res d1)) * dict_res (DD3x DENT) (a_gv a) Ews (dc_dict (a_st a)) *
   set_res (DD3x DENT) (a_gv a) Ews (dc_set (a_st a)) (dc_dict (a_st a)))).
Intros.
forward. forward_call 0. forward_if.
{ exfalso. match goal with H: Int.repr _ <> Int.zero |- _ => apply H; reflexivity end. }
forward.
assert (Hc2: cold01 (lh_dd_fs (c3_fs k1) (dp_fmt (c3_par k1)) (Some (x, buf)) cold))
  by (unfold cold01; simpl; auto).
unfold lhC_S2. Exists (Some (x, buf)) cold lxb.
unfold ds_LI_St, ctx_rep3t, fgroup3, tabs_rep, ds_LI_L.
cbn [lw_k w_k w_opc w_ipc w_smw w_oc lhC_kx c3_fs c3_tabs c3_stable c3_dict c3_s c3_par c3_sp c3_set lh_dd_fs
     dd_ox option_map lhC_dd fst lh_dd_ts] in *.
change (c3_dict k1) with d1.
rewrite lhC_hr_mem, held_redict_set.
match goal with Hx: cmem_ok _ |- _ => sep_apply (lhC_sg_put (a_d a) (c3_s k1) d1 (snd (getddict_res d1)) Hh0 Hx) end.
entailer!.
Time Qed.

End CM_LH3C2_s9s_1.
