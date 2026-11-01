(* FS3 set part: the body of ZSTD_freeDDictHashSet (for SetBodyA.v). *)
Require Import Zstd.proof.dec.v3.FS.set.SetDefs.
Local Open Scope logic.

(* DEBUGLOG's do { } while (0) *)
Local Ltac setA_skip_loop :=
  repeat apply -> seq_assoc;
  match goal with |- semax _ ?P (Ssequence (Sloop Sskip Sbreak) _) _ =>
    forward_loop P break: P; [apply ENTAIL_refl | forward; apply ENTAIL_refl | ]
  end.

Section CM_SetBodyA_free_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma body_free3 : MF_tbl_bytes ->
  semax_body Vprog G_free f_ZSTD_freeDDictHashSet ZSTD_freeDDictHashSet_spec.
Proof.
  intros Htb.
  start_function.
  setA_skip_loop.
  destruct (eq_dec sp nullval).
  - forward_if (PROP () LOCAL (temp _t'1 (Vint Int.zero); temp _hashSet sp; gvars gv; temp _customMem pm)
                SEP (mem_mgr gv; data_at shm t_cmem (cmem_v am) pm; cm_have am h)).
    { subst sp. contradiction. }
    { forward. entailer!. }
    forward_if (PROP () LOCAL (temp _hashSet sp; gvars gv; temp _customMem pm)
                SEP (mem_mgr gv; data_at shm t_cmem (cmem_v am) pm; cm_have am h)).
    { exfalso; lia. }
    { forward. entailer!. }
    forward_if.
    { subst sp. contradiction. }
    forward. entailer!.
  - unfold hset_at, hset_tbl, hs_table. Intros tbl tp.
    assert (Hhb: hb <= h) by auto.
    assert (Hn: 0 < Zlength tbl)
      by (match goal with Hi: hs_inv _ _ |- _ => destruct Hi as [[k [Hk Hk2]] _] end;
          rewrite Hk2; apply Z.pow_pos_nonneg; lia).
    match goal with Hb: hb = set_bytes _ _ |- _ => rename Hb into Hb0 end.
    assert (Hs: 0 < sizeof t_hset) by (vm_compute; reflexivity).
    assert_PROP (isptr tp) by (entailer!; auto with field_compatible).
    forward_if (PROP () LOCAL (temp _t'1 (Vint Int.one); gvars gv; temp _hashSet sp; temp _customMem pm)
      SEP (mem_mgr gv; data_at shm t_cmem (cmem_v am) pm; cm_have am h; blk_tok am t_hset sp;
           data_at Ews t_hset (tp, (Vlong (Int64.repr (Zlength tbl)), Vlong (Int64.repr (Zlength l)))) sp;
           blk_tok am (tarray tuchar (8 * Zlength tbl)) tp;
           data_at Ews (tarray (tptr t_ddict) (Zlength tbl)) tbl tp)).
    { forward. forward. entailer!. destruct tp; try contradiction; reflexivity. }
    { contradiction. }
    forward_if (PROP () LOCAL (gvars gv; temp _hashSet sp; temp _customMem pm)
      SEP (mem_mgr gv; data_at shm t_cmem (cmem_v am) pm; cm_have am (h - 8 * Zlength tbl); blk_tok am t_hset sp;
           data_at Ews t_hset (tp, (Vlong (Int64.repr (Zlength tbl)), Vlong (Int64.repr (Zlength l)))) sp)).
    { forward.
      sep_apply (Htb tp (Zlength tbl) tbl eq_refl).
      forward_call (gv, tarray tuchar (8 * Zlength tbl), tp, shm, pm, am, h).
      { destruct (eq_dec tp nullval); [subst tp; contradiction |]. cancel. }
      { try split; intros; destruct am; simpl in *; try rewrite Hb0 in *; auto; lia. }
      entailer!. destruct (eq_dec tp nullval); [subst tp; contradiction |].
      apply cm_have_eq. intros _. simpl. lia. }
    { match goal with Hc: Int.one = Int.zero |- _ => discriminate Hc end. }
    forward_if.
    { forward_call (gv, t_hset, sp, shm, pm, am, h - 8 * Zlength tbl).
      { destruct (eq_dec sp nullval); [contradiction |]. cancel. }
      { try split; intros; destruct am; simpl in *; try rewrite Hb0 in *; auto; lia. }
      forward. destruct (eq_dec sp nullval); [contradiction |]. entailer!.
      apply cm_have_eq. intros Hm. destruct am; [| contradiction]. simpl in *. lia. }
    { contradiction. }
Qed.

End CM_SetBodyA_free_1.
