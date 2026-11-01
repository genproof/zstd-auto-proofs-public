(* FS3 set part: the body of ZSTD_createDDictHashSet (for SetBodyA.v). *)
Require Import Zstd.proof.dec.v3.FS.set.SetDefs.
Local Open Scope logic.

(* DEBUGLOG's do { } while (0) *)
Local Ltac setA_skip_loop :=
  repeat apply -> seq_assoc;
  match goal with |- semax _ ?P (Ssequence (Sloop Sskip Sbreak) _) _ =>
    forward_loop P break: P; [apply ENTAIL_refl | forward; apply ENTAIL_refl | ]
  end.

Section CM_SetBodyA_create_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma body_create3 : MF_calloc_tbl -> PF_init ->
  semax_body Vprog G_create f_ZSTD_createDDictHashSet ZSTD_createDDictHashSet_spec.
Proof.
  intros Hcal Hinit.
  start_function.
  assert (Hr: cm_room am h (sizeof t_hset + 512)) by exact H0.
  forward_call (gv, t_hset, shm, pm, am, h).
  { eapply cm_room_le; [exact Hr | simpl; lia]. }
  Intros ret.
  setA_skip_loop.
  forward_if (ret <> nullval).
  { if_tac; entailer!. }
  { forward. Exists nullval. entailer!. rewrite !if_true by auto. cancel. }
  { forward. entailer!. }
  Intros. rewrite if_false by auto. Intros.
  forward_call (gv, 512, shm, pm, am, h + sizeof t_hset).
  { apply cm_room_shift; [exact Hr | simpl; lia | lia]. }
  Intros tp.
  forward.
  forward.
  forward_if (tp <> nullval).
  { if_tac; entailer!. }
  { subst tp. rewrite if_true by auto.
    forward_call (gv, t_hset, ret, shm, pm, am, h + sizeof t_hset).
    { rewrite if_false by auto. cancel. }
    { destruct am; simpl in *; [lia | auto]. }
    forward. Exists nullval. rewrite if_false by auto. entailer!.
    apply cm_have_eq. intros _. lia. }
  { forward. entailer!. }
  Intros. destruct (eq_dec tp nullval); [contradiction |]. Intros.
  sep_apply (Hcal tp 64 ltac:(lia) ltac:(rep_lia) ltac:(auto)).
  forward.
  forward.
  forward.
  Exists ret. destruct (eq_dec ret nullval); [contradiction |].
  unfold hset_at, hset_tbl, hs_table. Exists (Zrepeat nullval 64) tp.
  change (Zlength (Zrepeat nullval 64)) with 64. change (Zlength (@nil (val * ddict_st))) with 0.
  entailer!.
  apply cm_have_eq. intros Hn. destruct am; [| contradiction]. simpl. lia.
Qed.

End CM_SetBodyA_create_1.
