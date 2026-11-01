(* FS3 set part: the body of ZSTD_DDictHashSet_emplaceDDict. *)
Require Import Zstd.proof.dec.v3.FS.set.SetDefs.
Require Import Zstd.proof.dec.v3.FS.set.SetEmplaceAux.
Require Import Zstd.proof.dec.v3.FS.set.SetEmplaceLoop.
Local Open Scope logic.

Section CM_SetBodyEmplace_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma set_body_emplace : MF_ddid_wvp -> MF_ddid_range -> MF_ids_focus -> PF_member -> PF_set_id -> PF_notfull ->
  PF_insert -> PF_replace ->
  semax_body Vprog G_emplace f_ZSTD_DDictHashSet_emplaceDDict emplace_spec3.
Proof.
  intros Mwvp Mrange Mfocus Pmember Psetid Pnotfull Pinsert Preplace.
  start_function.
  set (n := Zlength tbl) in *.
  pose proof H as Hinv. destruct H as [[k [Hk Hn]] [Hln _]].
  assert (Hl0: 0 <= Zlength l) by apply Zlength_nonneg.
  destruct (Mfocus L (q, dd) H2) as [L1 [L2 [HL HF]]]. rewrite HF. simpl fst; simpl snd.
  assert_PROP (isptr q) as Hq by (unfold ddid; Intros; entailer!).
  assert_PROP (0 <= dd_id dd <= Int.max_unsigned) as Hid by (sep_apply (Mrange q (dd_id dd) (ddb dd)); entailer!).
  forward_call (q, dd_id dd, ddb dd).
  { rewrite if_false by (intro; subst; contradiction). cancel. }
  destruct (eq_dec q nullval) as [Hqn|_]; [subst; contradiction|].
  forward_call (Ews, sp, tp, n, Vlong (Int64.repr (Zlength l)), dd_id dd).
  forward. forward.
  assert (Hh: 0 <= hs_home (dd_id dd) n < n) by (apply (emp_home_range _ _ k); lia).
  remember (hs_home (dd_id dd) n) as h eqn:Hhd0.
  assert (Hn0: 0 < n) by lia.
  assert (Hhd: emp_hide (h = hs_home (dd_id dd) n)) by exact Hhd0. clear Hhd0.
  assert (Hnd: emp_hide (n = Zlength tbl)) by reflexivity. clearbody n.
  simpl in HF. gather_SEP (ddid q _ _) (set_ids (L1 ++ L2)). rewrite <- HF. clear HF HL L1 L2.
  match goal with |- semax _ ?P _ _ => forward_loop P break: P end.
  { entailer!. }
  { forward. forward. forward_if.
    - exfalso. apply Int64.same_if_eq in H. apply repr_inj_unsigned64 in H; [lia | rep_lia | rep_lia].
    - forward. entailer!. }
  match goal with |- semax _ ?P _ _ => forward_loop P break: P end.
  { entailer!. }
  { forward. entailer!. }
  forward_loop (emp_inv sp tp L l tbl q dd n h) break: (emp_brk sp tp L l tbl q dd n h).
  { unfold emp_inv. Exists 0. rewrite emp_slot0 by auto. entailer!. }
  { apply (emp_loop_body sp tp L l tbl q dd k n h); auto. }
  unfold emp_brk. Intros t.
  destruct (emp_insert l tbl q dd t n h Pinsert Hnd Hhd Hinv H0 Hq H5 H H6 H7) as [HIadd HIinv].
  match goal with |- semax _ ?P _ _ => forward_loop P break: P end.
  { entailer!. }
  { forward. entailer!. }
  assert (Hs: 0 <= hs_slot h t n < n) by (apply emp_slot_range; lia).
  forward.
  emp_access (emp_st5 tp q tbl (hs_slot h t n) n Hs (eq_sym Hnd) Hq) _t'5 _idx _ddict.
  forward. forward.
  red in Hnd. subst n. forward.
  Exists (upd_Znth (hs_slot h t (Zlength tbl)) tbl q). rewrite HIadd. entailer!.
  rewrite Zlength_app, Zlength_cons, Zlength_nil. cancel.
Qed.

End CM_SetBodyEmplace_1.
