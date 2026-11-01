(* FS3 set part: the body of ZSTD_DDictHashSet_getIndex (for SetBodyA.v). *)
Require Import Zstd.proof.dec.v3.FS.set.SetDefs.
Local Open Scope logic.

Section CM_SetBodyA_get_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma body_getIndex3 : MF_uint_bytes ->
  semax_body Vprog G_getIndex f_ZSTD_DDictHashSet_getIndex getIndex_spec3.
Proof.
  intros Hub.
  start_function.
  forward.
  assert_PROP (field_compatible tuint nil v_dictID) by entailer!.
  rewrite (Hub Tsh v_dictID id H H1).
  assert (Hlen: Zlength (le_bytes 4 id) = 4) by reflexivity.
  assert (Hok: bytes_ok (le_bytes 4 id)).
  { unfold bytes_ok, is_byte; simpl. repeat constructor; try apply Z.mod_pos_bound; lia. }
  remember (le_bytes 4 id) as bs eqn:Hbs.
  assert (Hbs4: exists b0 b1 b2 b3, bs = [b0;b1;b2;b3]) by (subst; simpl; eauto).
  destruct Hbs4 as (b0 & b1 & b2 & b3 & ->).
  change (tarray tuchar 4) with (tarray tuchar (Zlength [b0;b1;b2;b3])).
  (* forward_call by hand: its cancellation against pw_pred pw_none is very slow *)
  eapply semax_seq'.
  prove_call_setup (@nil Type) funspec_sub_refl (Tsh, v_dictID, [b0;b1;b2;b3], 0, pw_none).
  clear_Delta_specs. clear_MORE_POST.
  { simpl pw_pred. rewrite emp_sepcon. unfold fold_right_sepcon. instantiate (Frame := [_]).
    simpl. rewrite sepcon_emp. apply derives_refl. }
  forward_call_id1_y_wow.
  remember (xxh64 [b0;b1;b2;b3] 0) as hh eqn:Hhh.
  Intros vret.
  simpl app. unfold eq_no_post. Intros. subst vret. simpl pw_pred. simpl remove_localdef_temp.
  abbreviate_semax.
  forward.
  replace (data_at Tsh (tarray tuchar (Zlength [b0; b1; b2; b3])) _ v_dictID)
    with (data_at Tsh tuint (Vint (Int.repr id)) v_dictID).
  2:{ rewrite (Hub Tsh v_dictID id H H1), <- Hbs. reflexivity. }
  forward.
  entailer!.
  unfold hs_home. rewrite <- Hbs. reflexivity.
Qed.

End CM_SetBodyA_get_1.
