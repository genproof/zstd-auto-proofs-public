(* memcpy_ok (libc/LibcSpec.v) for the objects of subtree B that the decoder copies with the typed memcpy
   (libc.c's byte loop, so every copied byte must be a defined byte):
   - memcpy_ok_dtdesc: a Huffman table descriptor DTableDesc {maxTableLog; tableType; tableLog; reserved}, four
     unsigned chars, each a defined byte (HUF_getDTableDesc, the builders' copy back into the table);
     memcpy_ok_hufdt_desc(_k): the descriptor {12, tableType, L, reserved} of a built table (BRep.hufdt_x_at);
   - memcpy_ok_seqhdr: a ZSTD_seqSymbol_header {fastMode; tableLog}, two U32 (ZSTD_buildFSETable_body);
   - memcpy_ok_fhdr: an FSE_DTableHeader {tableLog; fastMode}, two U16 (FSE_buildDTable_internal);
   - memcpy_ok_uint_array: an array of U32 (the repcodes repStartValue, ZSTD_decompressBegin).
   Each object is equal (for the field_compatible address) to its little-endian bytes as a tarray tuchar; the
   tactic memcpy_side_B solves the side condition of memcpy_spec for them and for LibcOk's objects. *)
Require Export Zstd.proof.dec.B.BRep.
Require Import Zstd.proof.libc.LibcOk Zstd.proof.zstd.PickLemmas.
Local Open Scope logic.

(* the defined bytes of a 32-bit value *)
Definition u32_bytes (x: int) : list val := map (fun b => Vint (Int.repr b)) (le_bytes 4 (Int.unsigned x)).

Lemma Zlength_u32_bytes: forall x, Zlength (u32_bytes x) = 4.
Proof. intros. unfold u32_bytes. rewrite Zlength_map, Zlength_le_bytes. reflexivity. Qed.

Lemma byte_val_u32_bytes: forall x, Forall byte_val (u32_bytes x).
Proof. intros. apply byte_val_zbytes_range, le_bytes_bytes. Qed.

Lemma byte_val_Vubyte: forall b, byte_val (Vubyte b).
Proof.
  intros. exists (Byte.unsigned b). pose proof (Byte.unsigned_range b).
  split; [change Byte.modulus with 256 in *; lia | reflexivity].
Qed.

(* a byte array of n + m cells is its first n cells and its last m cells *)
Lemma bytes_split: forall sh n m (l1 l2: list val) p,
  0 <= n -> 0 <= m -> Zlength l1 = n -> Zlength l2 = m ->
  field_compatible (tarray tuchar (n + m)) [] p ->
  data_at sh (tarray tuchar (n + m)) (l1 ++ l2) p =
  data_at sh (tarray tuchar n) l1 p * data_at sh (tarray tuchar m) l2 (offset_val n p).
Proof.
  intros sh n m l1 l2 p Hn Hm H1 H2 FC.
  assert (H2': Zlength l2 = n + m - n) by lia.
  rewrite (split2_data_at_Tarray_app n (n + m) sh tuchar l1 l2 p) by assumption.
  rewrite field_address0_offset by auto with field_compatible.
  simpl nested_field_offset. rewrite Z.mul_1_l, Z.add_0_l. replace (n + m - n) with m by lia. reflexivity.
Qed.

Lemma fc_bytes_tail: forall n m p,
  0 <= n -> 0 <= m -> field_compatible (tarray tuchar (n + m)) [] p ->
  field_compatible (tarray tuchar m) [] (offset_val n p).
Proof.
  intros n m p Hn Hm FC.
  destruct (field_compatible_Tarray_split tuchar n (n + m) p) as [FWD _]; [lia |].
  destruct (FWD FC) as [_ FC2].
  rewrite field_address0_offset in FC2 by auto with field_compatible.
  simpl nested_field_offset in FC2. rewrite Z.mul_1_l, Z.add_0_l in FC2.
  replace (n + m - n) with m in FC2 by lia. exact FC2.
Qed.

(* the four unsigned chars of a DTableDesc *)
Lemma dtdesc_bytes: forall sh a b c d p,
  field_compatible t_dtdesc [] p ->
  data_at sh t_dtdesc (a, (b, (c, d))) p = data_at sh (tarray tuchar 4) [a; b; c; d] p.
Proof.
  intros sh a b c d p FCd.
  assert (FC4: field_compatible (tarray tuchar 4) [] p)
    by (apply (fc_scalar_bytes t_dtdesc); [reflexivity | apply Z.divide_1_l | exact FCd]).
  unfold_data_at (data_at _ t_dtdesc _ _).
  rewrite !field_at_data_at.
  rewrite !field_compatible_field_address by auto with field_compatible.
  simpl nested_field_offset. simpl nested_field_type.
  rewrite isptr_offset_val_zero by auto with field_compatible.
  assert (FC3: field_compatible (tarray tuchar 3) [] (offset_val 1 p))
    by (apply (pk_tail_fc 3 p); [lia | exact FC4]).
  assert (FC2: field_compatible (tarray tuchar 2) [] (offset_val 1 (offset_val 1 p)))
    by (apply (pk_tail_fc 2 (offset_val 1 p)); [lia | exact FC3]).
  rewrite (pk_peel1 sh 4 3 a [b; c; d] p) by first [lia | list_solve | exact FC4].
  rewrite (pk_peel1 sh 3 2 b [c; d] (offset_val 1 p)) by first [lia | list_solve | exact FC3].
  rewrite (pk_peel1 sh 2 1 c [d] (offset_val 1 (offset_val 1 p))) by first [lia | list_solve | exact FC2].
  rewrite data_at_tuchar_singleton_array_eq.
  rewrite !offset_offset_val. simpl Z.add.
  apply pred_ext; cancel.
Qed.

Lemma memcpy_ok_dtdesc: forall a b c d,
  byte_val a -> byte_val b -> byte_val c -> byte_val d -> memcpy_ok t_dtdesc (a, (b, (c, d))).
Proof.
  intros a b c d Ha Hb Hc Hd. exists [a; b; c; d].
  split; [reflexivity |]. split; [repeat constructor; auto |].
  change (sizeof t_dtdesc) with 4.
  split; intros sh p Hsh.
  - assert_PROP (field_compatible t_dtdesc [] p) as FC by entailer!.
    rewrite dtdesc_bytes by exact FC. apply derives_refl.
  - intros FC. rewrite dtdesc_bytes by exact FC. apply derives_refl.
Qed.

(* the descriptor of a built table (hufdt_x_at): {12, tableType 0 or 1, tableLog L <= 12, reserved} *)
Lemma byte_val_if: forall (b: bool) x y, 0 <= x < 256 -> 0 <= y < 256 ->
  byte_val (Vint (Int.repr (if b then x else y))).
Proof. intros. destruct b; apply byte_val_repr; auto. Qed.

Lemma memcpy_ok_hufdt_desc_k: forall k ht L res,
  0 <= k < 256 -> huf_ok ht -> ht_log ht <= L <= HUF_TABLELOG_MAX -> byte_val res ->
  memcpy_ok t_dtdesc (Vint (Int.repr 12), (Vint (Int.repr k), (Vint (Int.repr L), res))).
Proof.
  intros k ht L res Hk [Hl _] HL Hr. unfold HUF_TABLELOG_MAX in *.
  apply memcpy_ok_dtdesc; auto; apply byte_val_repr; lia.
Qed.

Lemma memcpy_ok_hufdt_desc: forall (x2: bool) ht L res,
  huf_ok ht -> ht_log ht <= L <= HUF_TABLELOG_MAX -> byte_val res ->
  memcpy_ok t_dtdesc (Vint (Int.repr 12), (Vint (Int.repr (if x2 then 1 else 0)), (Vint (Int.repr L), res))).
Proof. intros. apply (memcpy_ok_hufdt_desc_k _ ht); auto. destruct x2; lia. Qed.

(* a U32 field at p is its four little-endian bytes *)
Lemma u32_field_bytes: forall sh x p,
  field_compatible tuint [] p ->
  data_at sh tuint (Vint x) p = data_at sh (tarray tuchar 4) (u32_bytes x) p.
Proof.
  intros sh x p FC. unfold u32_bytes. rewrite <- (tuint_bytes4 sh (Int.unsigned x) p FC).
  rewrite Int.repr_unsigned. reflexivity.
Qed.

(* the two U32 of a ZSTD_seqSymbol_header *)
Lemma seqhdr_bytes: forall sh x y p,
  field_compatible t_seqhdr [] p ->
  data_at sh t_seqhdr (Vint x, Vint y) p = data_at sh (tarray tuchar 8) (u32_bytes x ++ u32_bytes y) p.
Proof.
  intros sh x y p FCh.
  assert (FC8: field_compatible (tarray tuchar 8) [] p)
    by (apply (fc_scalar_bytes t_seqhdr); [reflexivity | apply Z.divide_1_l | exact FCh]).
  unfold_data_at (data_at _ t_seqhdr _ _).
  rewrite !field_at_data_at.
  rewrite !field_compatible_field_address by auto with field_compatible.
  simpl nested_field_offset. simpl nested_field_type.
  rewrite isptr_offset_val_zero by auto with field_compatible.
  assert (FCx: field_compatible tuint [] p).
  { assert (FCf: field_compatible t_seqhdr (DOT _fastMode) p) by auto with field_compatible.
    apply field_compatible_nested_field in FCf. simpl in FCf.
    rewrite isptr_offset_val_zero in FCf by auto with field_compatible.
    exact FCf. }
  assert (FCy: field_compatible tuint [] (offset_val 4 p)).
  { assert (FCf: field_compatible t_seqhdr (DOT _tableLog) p) by auto with field_compatible.
    apply field_compatible_nested_field in FCf. simpl in FCf. exact FCf. }
  rewrite (u32_field_bytes sh x p FCx), (u32_field_bytes sh y (offset_val 4 p) FCy).
  change 8 with (4 + 4) in FC8 |- *.
  rewrite (bytes_split sh 4 4) by (auto; try lia; apply Zlength_u32_bytes).
  reflexivity.
Qed.

Lemma memcpy_ok_seqhdr: forall x y, memcpy_ok t_seqhdr (Vint x, Vint y).
Proof.
  intros x y. exists (u32_bytes x ++ u32_bytes y).
  split; [rewrite Zlength_app, !Zlength_u32_bytes; reflexivity |].
  split; [apply Forall_app; split; apply byte_val_u32_bytes |].
  change (sizeof t_seqhdr) with 8.
  split; intros sh p Hsh.
  - assert_PROP (field_compatible t_seqhdr [] p) as FC by entailer!.
    rewrite seqhdr_bytes by exact FC. apply derives_refl.
  - intros FC. rewrite seqhdr_bytes by exact FC. apply derives_refl.
Qed.

(* the defined bytes of a 16-bit value *)
Definition u16_bytes (z: Z) : list val := map (fun b => Vint (Int.repr b)) (le_bytes 2 z).

Lemma Zlength_u16_bytes: forall z, Zlength (u16_bytes z) = 2.
Proof. intros. unfold u16_bytes. rewrite Zlength_map, Zlength_le_bytes. reflexivity. Qed.

(* the two U16 of an FSE_DTableHeader *)
Lemma fhdr_bytes: forall sh x y p,
  0 <= x < 2 ^ 16 -> 0 <= y < 2 ^ 16 ->
  field_compatible (Tstruct ___gp_FSE_DTableHeader noattr) [] p ->
  data_at sh (Tstruct ___gp_FSE_DTableHeader noattr) (Vint (Int.repr x), Vint (Int.repr y)) p =
  data_at sh (tarray tuchar 4) (u16_bytes x ++ u16_bytes y) p.
Proof.
  intros sh x y p Hx Hy FCh.
  assert (FC4: field_compatible (tarray tuchar 4) [] p)
    by (apply (fc_scalar_bytes (Tstruct ___gp_FSE_DTableHeader noattr));
        [reflexivity | apply Z.divide_1_l | exact FCh]).
  unfold_data_at (data_at _ (Tstruct ___gp_FSE_DTableHeader noattr) _ _).
  rewrite !field_at_data_at.
  rewrite !field_compatible_field_address by auto with field_compatible.
  simpl nested_field_offset. simpl nested_field_type.
  rewrite isptr_offset_val_zero by auto with field_compatible.
  assert (FCx: field_compatible tushort [] p).
  { assert (FCf: field_compatible (Tstruct ___gp_FSE_DTableHeader noattr) (DOT _tableLog) p)
      by auto with field_compatible.
    apply field_compatible_nested_field in FCf. simpl in FCf.
    rewrite isptr_offset_val_zero in FCf by auto with field_compatible.
    exact FCf. }
  assert (FCy: field_compatible tushort [] (offset_val 2 p)).
  { assert (FCf: field_compatible (Tstruct ___gp_FSE_DTableHeader noattr) (DOT _fastMode) p)
      by auto with field_compatible.
    apply field_compatible_nested_field in FCf. simpl in FCf. exact FCf. }
  unfold u16_bytes.
  rewrite (tushort_bytes2 sh x p FCx Hx), (tushort_bytes2 sh y (offset_val 2 p) FCy Hy).
  change 4 with (2 + 2) in FC4 |- *.
  rewrite (bytes_split sh 2 2) by (auto; try lia; rewrite Zlength_map, Zlength_le_bytes; reflexivity).
  reflexivity.
Qed.

Lemma memcpy_ok_fhdr: forall x y, 0 <= x < 2 ^ 16 -> 0 <= y < 2 ^ 16 ->
  memcpy_ok (Tstruct ___gp_FSE_DTableHeader noattr) (Vint (Int.repr x), Vint (Int.repr y)).
Proof.
  intros x y Hx Hy. exists (u16_bytes x ++ u16_bytes y).
  split; [rewrite Zlength_app, !Zlength_u16_bytes; reflexivity |].
  split; [apply Forall_app; split; apply byte_val_zbytes_range, le_bytes_bytes |].
  change (sizeof (Tstruct ___gp_FSE_DTableHeader noattr)) with 4.
  split; intros sh p Hsh.
  - assert_PROP (field_compatible (Tstruct ___gp_FSE_DTableHeader noattr) [] p) as FC by entailer!.
    rewrite fhdr_bytes by auto. apply derives_refl.
  - intros FC. rewrite fhdr_bytes by auto. apply derives_refl.
Qed.

(* an array of U32: the bytes of its cells, one after the other *)
Fixpoint u32s_bytes (l: list val) : list val :=
  match l with
  | Vint x :: l' => u32_bytes x ++ u32s_bytes l'
  | _ :: l' => u32s_bytes l'
  | [] => []
  end.

Definition is_vint (v: val) : Prop := exists i, v = Vint i.

Lemma Zlength_u32s_bytes: forall l, Forall is_vint l -> Zlength (u32s_bytes l) = (4 * Zlength l)%Z.
Proof.
  intros l H. induction H as [| v l [i ->] _ IH]; [reflexivity |].
  cbn [u32s_bytes]. rewrite Zlength_app, Zlength_u32_bytes, IH, Zlength_cons. lia.
Qed.

Lemma byte_val_u32s_bytes: forall l, Forall byte_val (u32s_bytes l).
Proof.
  induction l as [| v l IH]; [constructor |].
  destruct v; cbn [u32s_bytes]; auto. apply Forall_app; split; [apply byte_val_u32_bytes | exact IH].
Qed.

Lemma u32s_bytes_eq: forall sh l p,
  Forall is_vint l -> field_compatible (tarray tuint (Zlength l)) [] p ->
  data_at sh (tarray tuint (Zlength l)) l p = data_at sh (tarray tuchar (4 * Zlength l)) (u32s_bytes l) p.
Proof.
  intros sh l. induction l as [| v l IH]; intros p Hl FC.
  - cbn [u32s_bytes]. change (Zlength (@nil val)) with 0. simpl Z.mul.
    rewrite !data_at_zero_array_eq by (auto; destruct FC as [? _]; exact H). reflexivity.
  - inversion Hl as [| ? ? [i ->] Hl']; subst.
    pose proof (Zlength_nonneg l) as Hn.
    rewrite Zlength_cons in FC |- *.
    change (Vint i :: l) with ([Vint i] ++ l).
    rewrite (split2_data_at_Tarray_app 1 (Z.succ (Zlength l)) sh tuint [Vint i] l p) by (auto; list_solve).
    rewrite field_address0_offset by auto with field_compatible.
    simpl nested_field_offset. replace (Z.succ (Zlength l) - 1) with (Zlength l) by lia.
    erewrite (data_at_singleton_array_eq sh tuint) by reflexivity.
    assert (FC0: field_compatible tuint [] p).
    { assert (H0: field_compatible (tarray tuint (Z.succ (Zlength l))) (SUB 0) p)
        by auto with field_compatible.
      apply field_compatible_nested_field in H0. simpl in H0.
      rewrite isptr_offset_val_zero in H0 by auto with field_compatible. exact H0. }
    assert (FCt: field_compatible (tarray tuint (Zlength l)) [] (offset_val 4 p)).
    { destruct (field_compatible_Tarray_split tuint 1 (Z.succ (Zlength l)) p) as [FWD _]; [lia |].
      destruct (FWD FC) as [_ FC2].
      rewrite field_address0_offset in FC2 by auto with field_compatible.
      simpl nested_field_offset in FC2. replace (Z.succ (Zlength l) - 1) with (Zlength l) in FC2 by lia.
      exact FC2. }
    rewrite (IH (offset_val 4 p) Hl' FCt).
    rewrite (u32_field_bytes sh i p FC0).
    cbn [u32s_bytes app].
    assert (FCb: field_compatible (tarray tuchar (4 + 4 * Zlength l)) [] p).
    { apply (fc_scalar_bytes (tarray tuint (Z.succ (Zlength l)))); auto.
      - simpl sizeof. rewrite Z.max_r by lia. lia.
      - apply Z.divide_1_l. }
    replace (4 * Z.succ (Zlength l))%Z with (4 + 4 * Zlength l)%Z by lia.
    rewrite (bytes_split sh 4 (4 * Zlength l))
      by first [lia | apply Zlength_u32_bytes | apply Zlength_u32s_bytes; exact Hl' | exact FCb].
    reflexivity.
Qed.

Lemma memcpy_ok_uint_array: forall n l, Zlength l = n -> Forall is_vint l -> memcpy_ok (tarray tuint n) l.
Proof.
  intros n l Hn Hl. subst n. exists (u32s_bytes l).
  pose proof (Zlength_nonneg l).
  assert (Hs: sizeof (tarray tuint (Zlength l)) = (4 * Zlength l)%Z)
    by (simpl sizeof; rewrite Z.max_r by lia; lia).
  split; [rewrite Hs; apply Zlength_u32s_bytes; exact Hl |].
  split; [apply byte_val_u32s_bytes |].
  rewrite Hs.
  split; intros sh p Hsh.
  - assert_PROP (field_compatible (tarray tuint (Zlength l)) [] p) as FC by entailer!.
    rewrite u32s_bytes_eq by auto. apply derives_refl.
  - intros FC. rewrite u32s_bytes_eq by auto. apply derives_refl.
Qed.

(* the side condition 0 <= sizeof t <= Int64.max_unsigned /\ memcpy_ok t v of a typed memcpy call
   (LibcSpec.memcpy_spec) of subtree B's objects, and of the byte strings and U32 of LibcOk.memcpy_side *)
(* the tactics only apply lemmas whose conclusion matches the goal syntactically: unifying a computed value
   with a pattern such as (if ?b then 1 else 0) or map ?f ?l can take minutes *)
Ltac byte_val_solve :=
  lazymatch goal with
  | |- byte_val (Vubyte _) => apply byte_val_Vubyte
  | |- byte_val (Vint (Int.repr (if _ then _ else _))) => apply byte_val_if; rep_lia
  | |- byte_val (Vint (Int.repr _)) =>
      first [ assumption | apply byte_val_repr; rep_lia
            | apply byte_val_repr; unfold HUF_TABLELOG_MAX in *; rep_lia ]
  | |- byte_val _ => assumption
  end.
(* Forall byte_val / bytes_ok of a list written out cell by cell (forward_call may have computed the map) *)
Ltac byte_list_solve :=
  first [ assumption
        | repeat (apply Forall_cons; [byte_val_solve |]); first [apply Forall_nil | assumption] ].
Ltac zbyte_list_solve :=
  first [ assumption
        | unfold bytes_ok; repeat (apply Forall_cons; [unfold is_byte; rep_lia |]);
          first [apply Forall_nil | assumption] ].
Ltac memcpy_ok_B :=
  lazymatch goal with
  | |- memcpy_ok t_dtdesc (Vint (Int.repr 12), (Vint (Int.repr ?k), (Vint (Int.repr ?L), ?r))) =>
      first [ solve [apply memcpy_ok_dtdesc; byte_val_solve]
            | match goal with Hh: huf_ok ?ht, HL: ht_log ?ht <= L <= HUF_TABLELOG_MAX |- _ =>
                apply (memcpy_ok_hufdt_desc_k k ht L r);
                [ lazymatch goal with
                  | |- _ <= (if ?b then _ else _) < _ => destruct b; lia
                  | |- _ => rep_lia end
                | exact Hh | exact HL | byte_val_solve ] end
            | apply memcpy_ok_dtdesc; try byte_val_solve ]
  | |- memcpy_ok t_dtdesc (_, (_, (_, _))) => apply memcpy_ok_dtdesc; try byte_val_solve
  | |- memcpy_ok t_seqhdr _ => apply memcpy_ok_seqhdr
  | |- memcpy_ok (tarray tuint _) _ =>
      apply memcpy_ok_uint_array;
      [ first [reflexivity | list_solve]
      | unfold is_vint; repeat (apply Forall_cons; [eexists; reflexivity |]); apply Forall_nil ]
  | |- memcpy_ok tuint _ => apply memcpy_ok_uint
  | |- memcpy_ok (tarray tuchar _) (map _ _) =>
      first [ solve [memcpy_ok_solve]
            | apply memcpy_ok_zbytes; [first [reflexivity | list_solve] | zbyte_list_solve] ]
  | |- memcpy_ok (tarray tuchar _) (sublist _ _ (map _ _)) =>
      rewrite sublist_map; apply memcpy_ok_zbytes;
      [list_solve | unfold bytes_ok in *; apply Forall_sublist; assumption]
  | |- memcpy_ok (tarray tuchar _) _ =>
      apply memcpy_ok_bytes; [first [reflexivity | list_solve] | byte_list_solve]
  | |- memcpy_ok (Tstruct ___gp_FSE_DTableHeader noattr) _ => apply memcpy_ok_fhdr; try rep_lia
  | |- memcpy_ok _ (Vint _, Vint _) => first [apply memcpy_ok_seqhdr | apply memcpy_ok_fhdr; try rep_lia]
  end.
Ltac memcpy_side_B := cbn [projT1 projT2]; split; [simpl; rep_lia | memcpy_ok_B].
