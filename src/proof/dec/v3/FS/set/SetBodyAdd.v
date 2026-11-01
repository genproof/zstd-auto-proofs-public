(* FS3 set part: the body of ZSTD_DDictHashSet_addDDict. *)
Require Import Zstd.proof.dec.v3.FS.set.SetDefs.
Local Open Scope logic.

Ltac add_dw0 := repeat apply -> seq_assoc;
  match goal with
  | |- semax _ ?Pre (Ssequence (Sloop _ Sbreak) _) _ => forward_loop Pre break: Pre
  | |- semax _ ?Pre (Sloop _ Sbreak) _ => forward_loop Pre break: Pre
  end.
Ltac add_skip_loop := add_dw0; [entailer! | forward; entailer! | ].
Ltac add_if0_loop := add_dw0; [entailer! |
  match goal with |- semax _ ?P _ _ => forward_if P end; [contradiction | forward; entailer! | forward; entailer!] | ].
Ltac add_ret_err := add_skip_loop; add_if0_loop; add_skip_loop; add_skip_loop.

Section CM_SetBodyAdd_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma add_cond (c n: Z) : 0 <= c < 2 ^ 20 -> 64 <= n <= 2 ^ 23 ->
  (Int64.mul (Int64.divu (Int64.mul (Int64.repr c) (Int64.repr 4)) (Int64.repr n)) (Int64.repr 3) = Int64.zero <->
   (4 * c < n)%Z).
Proof.
  intros Hc Hn.
  assert (E1: Int64.mul (Int64.repr c) (Int64.repr 4) = Int64.repr (c * 4)).
  { unfold Int64.mul. rewrite !Int64.unsigned_repr by rep_lia. reflexivity. }
  rewrite E1. unfold Int64.divu.
  rewrite !Int64.unsigned_repr by rep_lia.
  assert (Hd: 0 <= c * 4 / n <= c * 4) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; nia).
  unfold Int64.mul. rewrite !Int64.unsigned_repr by rep_lia.
  split; intro H.
  - apply (f_equal Int64.unsigned) in H. rewrite Int64.unsigned_repr in H by rep_lia.
    rewrite Int64.unsigned_zero in H.
    assert (c * 4 / n = 0) by lia.
    destruct (Z_lt_le_dec (4 * c) n) as [|Hge]; [lia|].
    assert (1 <= c * 4 / n) by (apply Z.div_le_lower_bound; lia). lia.
  - rewrite Z.div_small by lia. reflexivity.
Qed.

Lemma hs_raw_fold (am: option cmem) (sp tp: val) (l: list (val * ddict_st)) (tbl: list val) :
  blk_tok am t_hset sp *
  data_at Ews t_hset (tp, (Vlong (Int64.repr (Zlength tbl)), Vlong (Int64.repr (Zlength l)))) sp *
  hs_table am tp tbl |-- hs_raw am sp l tbl.
Proof. unfold hs_raw. Exists tp. cancel. Qed.

Lemma ids_snoc_fold (HMF: MF_ids_app) (l: list (val * ddict_st)) (q: val) (dd: ddict_st) :
  set_ids l * ddid q (dd_id dd) (ddb dd) |-- set_ids (l ++ [(q, dd)]).
Proof. rewrite HMF. apply derives_refl. Qed.

Lemma ids_snoc_unfold (HMF: MF_ids_app) (l: list (val * ddict_st)) (q: val) (dd: ddict_st) :
  set_ids (l ++ [(q, dd)]) |-- set_ids l * ddid q (dd_id dd) (ddb dd).
Proof. rewrite HMF. apply derives_refl. Qed.

Lemma nodup_snoc (l: list (val * ddict_st)) (q: val) (dd: ddict_st) :
  NoDup (map fst l) -> ~ In q (map fst l) -> NoDup (map fst (l ++ [(q, dd)])).
Proof.
  intros H1 H2. rewrite map_app. simpl.
  apply Permutation_NoDup with (q :: map fst l); [apply Permutation_cons_append | constructor; auto].
Qed.

Lemma set_body_add : MF_ids_app -> PF_inv0 -> PF_add_noexp -> PF_add_exp ->
  semax_body Vprog G_add f_ZSTD_DDictHashSet_addDDict ZSTD_DDictHashSet_addDDict_spec.
Proof.
  intros HMF HPF0 HPFn HPFe.
  start_function.
  unfold hset_at, hset_tbl. Intros tbl. rename H5 into Hb. Intros tp. rename H5 into H2'.
  rename H2 into Hok, H3 into Hhb, H4 into Hroom, H2' into H2.
  assert (Hroom': cm_room am h (8 * (2 * Zlength tbl))).
  { destruct am; simpl in *; [| exact I]. subst hb. unfold set_grow in Hroom. simpl sizeof in Hroom.
    pose proof (Zlength_nonneg tbl). lia. }
  assert (Hn: exists k, 6 <= k /\ Zlength tbl = 2 ^ k) by (destruct H2; tauto).
  assert (Hn1: Zlength tbl <= Z.max 64 (8 * Zlength l)) by (destruct H2 as [_ [? _]]; tauto).
  assert (Hn2: Zlength l < Zlength tbl) by (destruct H2 as [_ [_ [? _]]]; tauto).
  assert (Hn64: 64 <= Zlength tbl).
  { destruct Hn as [k [Hk ->]]. replace 64 with (2 ^ 6) by reflexivity. apply Z.pow_le_mono_r; lia. }
  assert (Hn23: Zlength tbl <= 2 ^ 23) by (pose proof (Z.max_spec 64 (8 * Zlength l)); lia).
  add_skip_loop.
  forward. forward.
  assert (Hc: 0 <= Zlength l < 2 ^ 20 /\ 64 <= Zlength tbl <= 2 ^ 23) by (pose proof (Zlength_nonneg l); lia).
  forward_if (EX tbl1: list val, PROP (hs_inv0 l tbl1; Zlength l + 1 < Zlength tbl1; Zlength tbl1 <= 2 ^ 30;
      ((4 * Zlength l)%Z < Zlength tbl /\ tbl1 = tbl) \/
      (Zlength tbl <= (4 * Zlength l)%Z /\ Zlength tbl1 = (2 * Zlength tbl)%Z))
    LOCAL (gvars gv; temp _hashSet sp; temp _ddict q; temp _customMem pm)
    SEP (mem_mgr gv; data_at shm t_cmem (cmem_v am) pm; cm_have am (h + set_bytes am (Zlength tbl1) - set_bytes am (Zlength tbl)); hs_raw am sp l tbl1; set_ids l; ddid q (dd_id dd) (ddb dd))).
  { entailer!. match goal with Hz: Int64.repr (Zlength tbl) = Int64.zero |- _ => rename Hz into E end. apply (f_equal Int64.unsigned) in E.
    rewrite Int64.unsigned_repr, Int64.unsigned_zero in E by rep_lia. lia. }
  { change (Int.signed (Int.repr 3)) with 3 in H3. change (Int.signed (Int.repr 0)) with 0 in H3.
    assert (Hge: (Zlength tbl <= 4 * Zlength l)%Z) by (destruct (Z_lt_le_dec (4 * Zlength l) (Zlength tbl)); [|lia];
      exfalso; apply H3; apply add_cond; auto; lia).
    sep_apply (hs_raw_fold am sp tp l tbl).
    forward_loop (PROP () LOCAL (gvars gv; temp _hashSet sp; temp _ddict q; temp _customMem pm)
        SEP (mem_mgr gv; data_at shm t_cmem (cmem_v am) pm; cm_have am h; hs_raw am sp l tbl; set_ids l; ddid q (dd_id dd) (ddb dd)))
      continue: (EX tbl1: list val, PROP (hs_inv0 l tbl1; Zlength l + 1 < Zlength tbl1; Zlength tbl1 <= 2 ^ 30;
      ((4 * Zlength l)%Z < Zlength tbl /\ tbl1 = tbl) \/
      (Zlength tbl <= (4 * Zlength l)%Z /\ Zlength tbl1 = (2 * Zlength tbl)%Z))
    LOCAL (gvars gv; temp _hashSet sp; temp _ddict q; temp _customMem pm)
    SEP (mem_mgr gv; data_at shm t_cmem (cmem_v am) pm; cm_have am (h + set_bytes am (Zlength tbl1) - set_bytes am (Zlength tbl)); hs_raw am sp l tbl1; set_ids l; ddid q (dd_id dd) (ddb dd)))
      break: (EX tbl1: list val, PROP (hs_inv0 l tbl1; Zlength l + 1 < Zlength tbl1; Zlength tbl1 <= 2 ^ 30;
      ((4 * Zlength l)%Z < Zlength tbl /\ tbl1 = tbl) \/
      (Zlength tbl <= (4 * Zlength l)%Z /\ Zlength tbl1 = (2 * Zlength tbl)%Z))
    LOCAL (gvars gv; temp _hashSet sp; temp _ddict q; temp _customMem pm)
    SEP (mem_mgr gv; data_at shm t_cmem (cmem_v am) pm; cm_have am (h + set_bytes am (Zlength tbl1) - set_bytes am (Zlength tbl)); hs_raw am sp l tbl1; set_ids l; ddid q (dd_id dd) (ddb dd))).
    { entailer!. }
    { forward_call (gv, sp, l, tbl, shm, pm, am, h).
      Intros vret. destruct vret as [r tbl']. simpl fst in *; simpl snd in *.
      match goal with Hr: _ \/ _ |- _ => destruct Hr as [[-> [Hi0 Hlen]] | [-> ->]] end.
      - forward_call 0.
        forward_if.
        { contradiction. }
        { forward. Exists tbl'. entailer!. }
      - forward_call (err_code ZSTD_error_memory_allocation).
        { unfold err_code, ZSTD_error_memory_allocation; rep_lia. }
        forward_if.
        2: { exfalso. compute in H4. inversion H4. }
        add_ret_err.
        forward. Exists (err_code ZSTD_error_memory_allocation) (set_bytes am (Zlength tbl)).
        rewrite if_false by (unfold err_code, ZSTD_error_memory_allocation; lia).
        unfold hset_at, hset_tbl, hs_raw. Intros tp'. Exists tbl tp'. entailer!.
        { unfold set_grow. lia. }
        apply cm_have_eq. intros _. lia. }
    { Intros tbl1. forward. Exists tbl1. entailer!. }
    { simpl RA_normal. apply andp_left2. apply derives_refl. }
  }
  { forward. change (Int.signed (Int.repr 3)) with 3 in H3. apply add_cond in H3; [|lia..]. Exists tbl. unfold hs_raw. Exists tp.
    assert (hs_inv0 l tbl) by (apply HPF0; auto). entailer!.
    apply cm_have_eq. intros _. lia. }
  Intros tbl1. unfold hs_raw. Intros tp1. unfold hs_table. Intros.
  forward_loop (PROP () LOCAL (gvars gv; temp _hashSet sp; temp _ddict q; temp _customMem pm)
      SEP (mem_mgr gv; data_at shm t_cmem (cmem_v am) pm;
           cm_have am (h + set_bytes am (Zlength tbl1) - set_bytes am (Zlength tbl)); blk_tok am t_hset sp;
           data_at Ews t_hset (tp1, (Vlong (Int64.repr (Zlength tbl1)), Vlong (Int64.repr (Zlength l)))) sp;
           blk_tok am (tarray tuchar (8 * Zlength tbl1)) tp1;
           data_at Ews (tarray (tptr t_ddict) (Zlength tbl1)) tbl1 tp1; set_ids l; ddid q (dd_id dd) (ddb dd)))
    continue: (PROP () LOCAL (gvars gv; temp _hashSet sp; temp _ddict q; temp _customMem pm)
      SEP (mem_mgr gv; data_at shm t_cmem (cmem_v am) pm;
        cm_have am (h + set_bytes am (Zlength tbl1) - set_bytes am (Zlength tbl));
        hset_at am sp (set_add l q dd) (set_bytes am (Zlength tbl1)); set_ids l; ddid q (dd_id dd) (ddb dd)))
    break: (PROP () LOCAL (gvars gv; temp _hashSet sp; temp _ddict q; temp _customMem pm)
      SEP (mem_mgr gv; data_at shm t_cmem (cmem_v am) pm;
        cm_have am (h + set_bytes am (Zlength tbl1) - set_bytes am (Zlength tbl));
        hset_at am sp (set_add l q dd) (set_bytes am (Zlength tbl1)); set_ids l; ddid q (dd_id dd) (ddb dd))).
  { entailer!. }
  { sep_apply (ids_snoc_fold HMF l q dd).
    assert (Hnd: NoDup (map fst l)) by (destruct H3 as [_ [_ [? _]]]; auto).
    forward_call (sp, tp1, l ++ [(q, dd)], l, tbl1, q, dd).
    { split; [apply in_or_app; right; left; auto|].
      split; [apply nodup_snoc; auto | apply incl_appl, incl_refl]. }
    Intros tbl'. rename H8 into Hinv0', H9 into Hlen'.
    forward_call 0.
    forward_if.
    { contradiction. }
    forward.
    sep_apply (ids_snoc_unfold HMF l q dd).
    assert (Hinv: hs_inv (set_add l q dd) tbl').
    { destruct H6 as [[Hlt ->] | [Hle Hl2]].
      - eapply HPFn; eauto.
      - eapply HPFe; eauto; lia. }
    unfold hset_at, hset_tbl, hs_table. Exists tbl' tp1.
    rewrite Hlen'. entailer!. }
  { forward. entailer!. }
  forward. Exists 0 (set_bytes am (Zlength tbl1)). rewrite if_true by auto. entailer!.
  - destruct am; simpl; [| unfold set_grow; lia].
    unfold set_grow. destruct H6 as [[_ ->] | [_ ->]]; simpl sizeof; pose proof (Zlength_nonneg tbl); lia.
  - apply cm_have_eq. intros _. lia.
Qed.

End CM_SetBodyAdd_1.
