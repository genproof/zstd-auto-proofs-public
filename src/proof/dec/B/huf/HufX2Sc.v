(* X2T: the 2^L U32 cells of x2_u32s are HUF_DEltX2 cells that are
   x2_cell_ok (HufX2S.x2_cells_stmt), from the model facts x2_fill (xf_range, xf_cell_ok); they are exactly
   ExHuf's xh_cells_x2 (x2c_of is xh_x2_fields read as the struct's fields). *)
Require Import Zstd.proof.dec.B.huf.HufX2S.
Require Import Zstd.proof.model.ExHuf.
Local Open Scope logic.

(* a HUF_DEltX2 {U16; BYTE; BYTE} at a 4-aligned offset is aligned *)
Lemma x2c_align: forall z, (4 | z) -> align_compatible_rec cenv_cs t_deltx2 z.
Proof.
  intros z Hz.
  eapply align_compatible_rec_Tstruct; [reflexivity|reflexivity|].
  intros i0 t0 z0 Ht Ho; simpl in Ht, Ho.
  repeat (destruct (ident_eq _ _) in Ht; [inv Ht; inv Ho; eapply align_compatible_rec_by_value; [reflexivity|]; simpl |]);
    try discriminate.
  - rewrite Z.add_0_r. apply Z.divide_trans with 4; [exists 2; reflexivity | auto].
  - apply Z.divide_1_l.
  - apply Z.divide_1_l.
Qed.

Lemma x2c_fc1: forall q, field_compatible tuint [] q -> field_compatible t_deltx2 [] q.
Proof.
  intros q [A [B [C [D E]]]]. repeat split; auto.
  destruct q; try contradiction. unfold align_compatible in D |- *. apply x2c_align.
  eapply align_compatible_rec_by_value_inv in D; [|reflexivity]. auto.
Qed.

Lemma x2c_fc: forall n p, field_compatible (tarray tuint n) [] p -> field_compatible (tarray t_deltx2 n) [] p.
Proof.
  intros n p [A [B [C [D E]]]]. repeat split; auto.
  destruct p; try contradiction. unfold align_compatible in D |- *.
  apply align_compatible_rec_Tarray. intros j Hj.
  pose proof (align_compatible_rec_Tarray_inv _ _ _ _ _ D j Hj) as D1.
  change (sizeof t_deltx2) with (sizeof tuint). apply x2c_align.
  eapply align_compatible_rec_by_value_inv in D1; [|reflexivity]. auto.
Qed.

Lemma x2c_fcs: forall q, field_compatible tuint [] q -> field_compatible tushort [] q.
Proof.
  intros q [A [B [C [D E]]]]. repeat split; auto.
  - destruct q; try contradiction. unfold size_compatible in C |- *. simpl sizeof in *. lia.
  - destruct q; try contradiction. unfold align_compatible in D |- *.
    eapply align_compatible_rec_by_value_inv in D; [|reflexivity].
    eapply align_compatible_rec_by_value; [reflexivity|].
    apply Z.divide_trans with 4; [exists 2; reflexivity | auto].
Qed.

(* the little-endian bytes of a U32 *)
Lemma x2c_bytes: forall e, 0 <= e < Int.modulus ->
  e = decode_int [Byte.repr e; Byte.repr (e / 256); Byte.repr (e / 65536); Byte.repr (e / 16777216)] /\
  e mod 65536 = decode_int [Byte.repr e; Byte.repr (e / 256)].
Proof.
  intros e He. unfold decode_int, rev_if_be. change Archi.big_endian with false.
  cbv iota beta delta [int_of_bytes]. rewrite !Byte.unsigned_repr_eq. change Byte.modulus with 256.
  replace (e / 65536) with (e / 256 / 256) by (rewrite !Z.div_div by lia; reflexivity).
  replace (e / 16777216) with (e / 256 / 256 / 256) by (rewrite !Z.div_div by lia; reflexivity).
  set (a := e / 256). set (b := a / 256). set (c := b / 256).
  assert (Ha := Z.div_mod e 256 ltac:(lia)). assert (Hb := Z.div_mod a 256 ltac:(lia)).
  assert (Hc := Z.div_mod b 256 ltac:(lia)).
  assert (Hc0: 0 <= c < 256).
  { subst c b a. rewrite !Z.div_div by lia. change Int.modulus with 4294967296 in He.
    split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  rewrite (Z.mod_small c 256) by lia.
  assert (He0 := Z.mod_pos_bound e 256 ltac:(lia)). assert (Ha0 := Z.mod_pos_bound a 256 ltac:(lia)).
  split; [lia|].
  change 65536 with (256*256)%Z. rewrite Z.rem_mul_r by lia. subst a. lia.
Qed.

(* one cell: the U32 e is the HUF_DEltX2 {e mod 2^16; byte 2; byte 3} *)
Lemma x2c_cell: forall sh e q, 0 <= e < Int.modulus -> field_compatible tuint [] q ->
  data_at sh tuint (Vint (Int.repr e)) q |--
  data_at sh t_deltx2
    (Vint (Int.repr (e mod 65536)), (Vint (Int.repr ((e / 65536) mod 256)), Vint (Int.repr (e / 16777216)))) q.
Proof.
  intros sh e q He FC.
  destruct (x2c_bytes e He) as [E4 E2].
  rewrite E4 at 1.
  rewrite <- (data_at_int_bytes eq_refl sh _ _ _ _ q FC).
  rewrite (data_at_short_bytes sh _ _ q (x2c_fcs q FC)). rewrite <- E2.
  pose proof (x2c_fc1 q FC) as FCd.
  unfold_data_at (data_at _ t_deltx2 _ q).
  rewrite !field_at_data_at. rewrite !field_address_offset by auto with field_compatible.
  simpl nested_field_type. simpl nested_field_offset. rewrite !isptr_offset_val_zero by auto.
  unfold Vubyte. rewrite !Byte.unsigned_repr_eq. change Byte.modulus with 256.
  rewrite (Z.mod_small (e / 16777216) 256).
  - rewrite sepcon_assoc; apply derives_refl.
  - change Int.modulus with 4294967296 in He.
    split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

(* the HUF_DEltX2 of a U32 *)
Definition x2c_of (e: Z) : val * (val * val) :=
  (Vint (Int.repr (e mod 65536)), (Vint (Int.repr ((e / 65536) mod 256)), Vint (Int.repr (e / 16777216)))).

Lemma x2c_peel: forall sh t (w: reptype t) (ws: list (reptype t)) n p,
  Zlength ws = n ->
  data_at sh (tarray t (n + 1)) (w :: ws) p =
  data_at sh t w p * data_at sh (tarray t n) ws (field_address0 (tarray t (n + 1)) (SUB 1) p).
Proof.
  intros sh t w ws n p Hn.
  change (w :: ws) with ([w] ++ ws).
  rewrite (split2_data_at_Tarray_app 1 (n + 1) sh t [w] ws p); [| reflexivity | lia].
  rewrite (data_at_singleton_array_eq sh t w [w]) by auto.
  replace (n + 1 - 1) with n by lia. reflexivity.
Qed.

Lemma x2c_array: forall sh (l: list Z) p,
  Forall (fun e => 0 <= e < Int.modulus) l -> field_compatible (tarray tuint (Zlength l)) [] p ->
  data_at sh (tarray tuint (Zlength l)) (map (fun e => Vint (Int.repr e)) l) p |--
  data_at sh (tarray t_deltx2 (Zlength l)) (map x2c_of l) p.
Proof.
  intros sh l. induction l as [|e l IH]; intros p HF FC.
  - rewrite !Zlength_nil. simpl map.
    rewrite !data_at_zero_array_eq; auto; destruct FC as [? _]; auto.
  - inv HF. rewrite Zlength_cons in FC |- *. unfold Z.succ in FC |- *. simpl map. pose proof (Zlength_nonneg l) as Hl.
    pose proof (x2c_fc _ _ FC) as FCd.
    rewrite (x2c_peel sh tuint _ _ (Zlength l)) by (rewrite Zlength_map; reflexivity).
    rewrite (x2c_peel sh t_deltx2 _ _ (Zlength l)) by (rewrite Zlength_map; reflexivity).
    destruct (field_compatible_Tarray_split tuint 1 (Zlength l + 1) p) as [S _]; [lia|].
    destruct (S FC) as [FC1 FCt]. replace (Zlength l + 1 - 1) with (Zlength l) in FCt by lia.
    replace (field_address0 (tarray t_deltx2 (Zlength l + 1)) (SUB 1) p)
      with (field_address0 (tarray tuint (Zlength l + 1)) (SUB 1) p).
    2:{ rewrite !field_address0_offset by (apply arr_field_compatible0; auto; lia).
        reflexivity. }
    apply sepcon_derives.
    + assert_PROP (field_compatible tuint [] p) by entailer!.
      apply x2c_cell; auto.
    + apply IH; auto.
Qed.

Lemma x2_u32s_cells : x2_fill -> x2_cells_stmt.
Proof.
  intros XF sh ht L p Hht HL.
  assert (HP: 0 < 2 ^ L) by (apply Z.pow_pos_nonneg; [lia | destruct Hht as [[H1 _] _]; lia]).
  set (l := map (fun n => x2_elt ht L (Z.of_nat n)) (seq 0 (Z.to_nat (2 ^ L)))).
  assert (Hlen: Zlength l = 2 ^ L).
  { unfold l. rewrite Zlength_map, Zlength_correct, length_seq. lia. }
  assert (Hu: x2_u32s ht L = map (fun e => Vint (Int.repr e)) l).
  { unfold x2_u32s, l. rewrite map_map. reflexivity. }
  assert (Hz: forall v, 0 <= v < 2 ^ L -> Znth v l = x2_elt ht L v).
  { intros v Hv. unfold l.
    rewrite Znth_map by (rewrite Zlength_correct, length_seq; lia).
    unfold Znth. rewrite if_false by lia. rewrite seq_nth by lia. simpl. f_equal. lia. }
  assert (HF: Forall (fun e => 0 <= e < Int.modulus) l).
  { apply Forall_Znth. intros i Hi. rewrite Hlen in Hi. rewrite Hz by lia.
    pose proof (xf_range XF ht L i Hht HL Hi). change Int.modulus with 4294967296. lia. }
  rewrite Hu.
  assert_PROP (field_compatible (tarray tuint (2 ^ L)) [] p) as FC by entailer!.
  Exists (map x2c_of l).
  apply andp_right.
  - apply prop_right. split; [|split].
    + rewrite Zlength_map. auto.
    + intros v Hv. rewrite Znth_map by lia. rewrite Hz by lia.
      apply (xf_cell_ok XF); auto.
    + unfold l, xh_cells_x2. rewrite !map_map. apply map_ext. intros n. reflexivity.
  - rewrite <- Hlen. apply x2c_array; auto. rewrite Hlen. auto.
Qed.
