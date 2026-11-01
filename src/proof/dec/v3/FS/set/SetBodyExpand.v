(* FS3 set part: the body of ZSTD_DDictHashSet_expand. *)
Require Import Zstd.proof.dec.v3.FS.set.SetDefs Zstd.proof.dec.v3.FS.set.SetBodyExpandLoop Zstd.proof.dec.v3.FS.set.SetBodyExpandTail.
Local Open Scope logic.

Section CM_SetBodyExpand_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma set_body_expand : MF_ddid_wvp -> MF_ids_focus -> PF_member -> PF_set_id ->
  MF_calloc_tbl -> MF_tbl_bytes -> PF_inv0 -> PF_exp_init -> PF_exp_step -> PF_exp_skip -> PF_exp_end ->
  semax_body Vprog G_expand f_ZSTD_DDictHashSet_expand expand_spec3.
Proof.
intros Hwvp Hfocus Hmem Hsid Hcalloc Hbytes Hinv0 Hinit Hstep Hskip Hend.
start_function.
unfold hs_raw. Intros otp.
unfold hs_table. Intros.
assert (Hk: exists k, 6 <= k /\ Zlength tbl = 2 ^ k) by (destruct H; tauto).
destruct Hk as [k [Hk6 Hkn]].
assert (H64: 64 <= Zlength tbl). { rewrite Hkn. replace 64 with (2^6) by reflexivity. apply Z.pow_le_mono_r; lia. }
assert (H23: Zlength tbl <= 8388608) by (simpl in H0; lia).
forward.
forward.
replace (Int64.mul (Int64.repr (Zlength tbl)) (Int64.repr (Int.signed (Int.repr 2)))) with (Int64.repr (2 * Zlength tbl)) by (rewrite Int.signed_repr by rep_lia; rewrite mul64_repr; f_equal; lia).
(* split the call from the cast into _newTable (forward_call would absorb it: slow, _newTable/_newTableSize) *)
eapply semax_seq'. eapply semax_seq'.
forward_call (gv, (8 * (2 * Zlength tbl))%Z, shm, pm, am, h).
apply andp_left2; apply derives_refl.
match goal with |- semax _ (exp (fun vret => PROPx (@?P vret) (LOCALx (@?Q vret) (SEPx (@?R vret))))) _ (normal_ret_assert ?Post) =>
  unify Post (exp (fun vret: val => PROPx (P vret) (LOCALx (temp _newTable vret :: Q vret) (SEPx (R vret))))) end.
Intros q. forward. Exists q. entailer!.
Intros q.
abbreviate_semax.
forward.
forward.
skb.
destruct (eq_dec q nullval) as [Hq | Hq].
{ (* calloc failed *)
  subst q.
  unfold abbreviate. match goal with |- semax _ ?P _ _ => forward_loop P break: (PROP (False) LOCAL () SEP ()) end.
  { entailer!. }
  forward_if.
  2: { exfalso. match goal with Hx: _ <> _ |- _ => apply Hx; reflexivity end. }
  skb.
  if0.
  skb. skb.
  forward.
  Exists (err_code ZSTD_error_memory_allocation) tbl.
  apply andp_right; [apply prop_right; split; [right; auto | unfold err_code, ZSTD_error_memory_allocation; f_equal; apply Int64.eqm_samerepr; exists (-1); reflexivity] | ].
  try rewrite if_true by auto.
  unfold hs_raw, hs_table. Exists otp. entailer!.
  apply cm_have_eq. intros _. lia. }
destruct (eq_dec q nullval) as [Hq0|Hq0]; [contradiction|].
assert (Hc1: (0 <= 2 * Zlength tbl)%Z) by lia.
assert (Hc2: (8 * (2 * Zlength tbl))%Z <= Ptrofs.max_unsigned) by rep_lia.
Intros.
match goal with Hm: q <> nullval -> malloc_compatible _ q |- _ => pose proof (Hm Hq0) as Hmc end.
sep_apply (Hcalloc q (2 * Zlength tbl)%Z Hc1 Hc2 Hmc).
unabbr. unfold POSTCONDITION, abbreviate.
eapply semax_pre; [| exact (exp_tail Hwvp Hfocus Hmem Hbytes Hinv0 Hinit Hstep Hskip Hend gv sp l tbl shm pm am h otp q SH H H0 H1 H2 H3 Hq)].
entailer!.
Qed.

End CM_SetBodyExpand_1.
