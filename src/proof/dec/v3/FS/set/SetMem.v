(* FS3 set part: memory facts (calloc'd bytes as a NULL table, a table as bytes, a uint as bytes, set_ids). *)
Require Import Zstd.proof.dec.v3.FS.set.SetDefs.
Local Open Scope logic.

Section CM_SetMem_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma sm_ids_app : MF_ids_app.
Proof.
  intros L x. unfold set_ids. rewrite map_app. simpl.
  induction L as [|a L IH]; simpl.
  - rewrite sepcon_emp, emp_sepcon; auto.
  - rewrite IH, sepcon_assoc; auto.
Qed.

Lemma sm_ids_focus : MF_ids_focus.
Proof.
  intros L e Hin. apply in_split in Hin. destruct Hin as [L1 [L2 ->]].
  exists L1, L2. split; auto.
  unfold set_ids. rewrite !map_app. simpl.
  induction L1 as [|a L1 IH]; simpl.
  - auto.
  - rewrite IH. rewrite <- !sepcon_assoc. f_equal. apply sepcon_comm.
Qed.

Lemma sm_calloc_tbl : MF_calloc_tbl.
Proof.
  intros p n Hn Hmax H.
  sep_apply (zero_bytes_mapsto_zeros Ews (8 * n) p); [auto | lia |].
  destruct p; try contradiction.
  destruct H as [Hal _].
  replace (8 * n)%Z with (Z.of_nat (Z.to_nat n) * size_chunk Mptr)%Z by (rewrite Z2Nat.id by lia; simpl; lia).
  replace (Zrepeat nullval n) with (repeat nullval (Z.to_nat n)) by reflexivity.
  replace (data_at Ews (tarray (tptr t_ddict) n)) with
    (data_at Ews (tarray (tptr t_ddict) (Z.of_nat (Z.to_nat n)))) by (rewrite Z2Nat.id by lia; auto).
  apply mapsto_zeros_data_atTarrayTptr_nullval_N; auto.
Qed.

Lemma sm_fc_bytes : forall t m p, field_compatible t nil p -> sizeof t = m ->
  field_compatible (tarray tuchar m) nil p.
Proof.
  intros t m p Hfc Hs. destruct Hfc as (Hp & _ & Hsz & _ & _).
  destruct p; try contradiction.
  split3; [exact I | reflexivity |]. split3; [| | exact I].
  - red in Hsz |- *. simpl sizeof in *. rewrite <- Hs. pose proof (sizeof_pos t). rewrite Z.max_r by lia. lia.
  - red. apply align_compatible_rec_Tarray. intros. econstructor; [reflexivity | apply Z.divide_1_l].
Qed.

Lemma sm_tbl_bytes : MF_tbl_bytes.
Proof.
  intros p n tbl Hlen.
  assert_PROP (field_compatible (tarray (tptr t_ddict) n) nil p) by entailer!.
  sep_apply (data_at_data_at_ Ews (tarray (tptr t_ddict) n) tbl p).
  rewrite !data_at__memory_block. normalize.
  rewrite prop_true_andp.
  2: { apply (sm_fc_bytes _ _ _ H). simpl. pose proof (Zlength_nonneg tbl). rewrite Z.max_r by lia. lia. }
  replace (sizeof (tarray tuchar (8 * n))) with (sizeof (tarray (tptr t_ddict) n)); auto.
  simpl. pose proof (Zlength_nonneg tbl). rewrite !Z.max_r by lia. lia.
Qed.

Lemma sm_fc_tail : forall k p, 0 <= k -> field_compatible (tarray tuchar (k + 1)) nil p ->
  field_compatible (tarray tuchar k) nil (offset_val 1 p).
Proof.
  intros k p Hk Hfc. destruct Hfc as (Hp & _ & Hsz & _ & _).
  destruct p; try contradiction.
  split3; [exact I | reflexivity |]. split3; [| | exact I].
  - red in Hsz |- *. simpl sizeof in *. rewrite Z.max_r in * by lia.
    pose proof (Ptrofs.unsigned_range i).
    simpl offset_val. unfold Ptrofs.add. rewrite (Ptrofs.unsigned_repr 1) by rep_lia.
    rewrite Ptrofs.unsigned_repr by rep_lia. lia.
  - red. apply align_compatible_rec_Tarray. intros. econstructor; [reflexivity | apply Z.divide_1_l].
Qed.

Lemma sm_arr_cons : forall sh k (v: val) (vs: list val) p, Zlength vs = k ->
  field_compatible (tarray tuchar (k + 1)) nil p ->
  data_at sh (tarray tuchar (k + 1)) (v :: vs) p =
  data_at sh tuchar v p * data_at sh (tarray tuchar k) vs (offset_val 1 p).
Proof.
  intros sh k v vs p Hk Hfc. pose proof (Zlength_nonneg vs).
  unfold tarray at 1.
  rewrite (split2_data_at_Tarray_tuchar sh (k + 1) 1) by (try rewrite Zlength_cons; lia).
  rewrite field_address0_offset by auto with field_compatible.
  simpl nested_field_offset.
  rewrite sublist_one by (rewrite ?Zlength_cons; lia).
  rewrite sublist_S_cons by lia. replace (Z.succ 0 - 1) with 0 by lia. replace (k + 1 - 1) with k by lia.
  rewrite sublist_same by lia. simpl Znth.
  change (Tarray tuchar 1 noattr) with (tarray tuchar 1). rewrite data_at_tuchar_singleton_array_eq.
  replace (0 + 1 * 1) with 1 by lia. reflexivity.
Qed.

Lemma sm_le4 : forall id, 0 <= id <= Int.max_unsigned ->
  decode_int [Byte.repr (id mod 256); Byte.repr (id / 256 mod 256);
              Byte.repr (id / 256 / 256 mod 256); Byte.repr (id / 256 / 256 / 256 mod 256)] = id.
Proof.
  intros id Hid. unfold decode_int, rev_if_be. change Archi.big_endian with false. cbv iota. unfold int_of_bytes.
  rewrite !Byte.unsigned_repr_eq. change Byte.modulus with 256.
  rewrite !Z.mod_mod by lia.
  change Int.max_unsigned with 4294967295 in Hid.
  Z.to_euclidean_division_equations. lia.
Qed.

Lemma sm_uint_bytes : MF_uint_bytes.
Proof.
  intros sh p id Hid Hfc.
  pose proof (sm_fc_bytes tuint 4 p Hfc eq_refl) as F4.
  pose proof (sm_fc_tail 3 p ltac:(lia) F4) as F3.
  pose proof (sm_fc_tail 2 _ ltac:(lia) F3) as F2.
  unfold xxh_bytes. cbn [le_bytes map].
  rewrite (sm_arr_cons sh 3) by (auto; reflexivity).
  rewrite (sm_arr_cons sh 2) by (auto; reflexivity).
  rewrite (sm_arr_cons sh 1) by (auto; reflexivity).
  rewrite data_at_tuchar_singleton_array_eq.
  rewrite !offset_offset_val. simpl Z.add.
  rewrite <- (sm_le4 id Hid) at 1.
  rewrite <- data_at_int_bytes by (auto || reflexivity).
  unfold Vubyte. rewrite !Byte.unsigned_repr_eq. change Byte.modulus with 256. rewrite !Z.mod_mod by lia.
  rewrite !sepcon_assoc. reflexivity.
Qed.

Lemma set_mem_ok : MF_calloc_tbl /\ MF_tbl_bytes /\ MF_uint_bytes /\ MF_ids_focus /\ MF_ids_app.
Proof.
  exact (conj sm_calloc_tbl (conj sm_tbl_bytes (conj sm_uint_bytes (conj sm_ids_focus sm_ids_app)))).
Qed.

End CM_SetMem_1.
