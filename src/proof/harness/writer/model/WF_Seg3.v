(* Arithmetic and block facts of w_frame's blocks loop (segment 3 of its body, the template WB_frame_s3): the ranges of
   the window and of Block_Maximum_Size, the block
   header's value and bytes, and one block (wbody_ok: the body the loop's branch wrote) as a wblock_ok. *)
Require Import VST.floyd.proofauto.
Require Export Zstd.proof.harness.writer.model.WF_Defs.
Local Open Scope Z_scope.

Lemma wf3_window_range : forall dm p, hp_ok dm p -> 0 <= hp_window p <= 2 ^ 42.
Proof.
  intros dm p Hp. destruct Hp as (Hn & _ & _ & _ & He & Hm & _).
  unfold hp_window. destruct (hp_single p); [lia |].
  assert (2 ^ (10 + hp_e p) <= 2 ^ 41) by (apply Z.pow_le_mono_r; lia).
  assert (0 < 2 ^ (10 + hp_e p)) by (apply Z.pow_pos_nonneg; lia).
  assert (0 <= 2 ^ (10 + hp_e p) / 8 <= 2 ^ (10 + hp_e p)).
  { split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia. }
  assert (2 ^ (10 + hp_e p) / 8 * 8 <= 2 ^ (10 + hp_e p)) by (rewrite Z.mul_comm; apply Z.mul_div_le; lia).
  change (2 ^ 42) with (2 * 2 ^ 41). nia.
Qed.

Lemma wf3_bsm_range : forall dm p, hp_ok dm p -> 0 <= hp_bsm p <= 2 ^ 17.
Proof. intros. pose proof (wf3_window_range dm p H). unfold hp_bsm. lia. Qed.

Lemma wf3_lor_add : forall a b r, 0 <= a < 2 ^ r -> 0 <= b -> 0 <= r ->
  Z.lor a (Z.shiftl b r) = a + b * 2 ^ r.
Proof.
  intros a b r Ha Hb Hr.
  assert (D: Z.land a (Z.shiftl b r) = 0).
  { destruct (Z.eq_dec a 0) as [-> | Ha0]; [apply Z.land_0_l |].
    apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases n r).
    - rewrite Z.shiftl_spec_low by lia. apply Bool.andb_false_r.
    - assert (Z.log2 a < r) by (apply Z.log2_lt_pow2; lia).
      rewrite (Z.bits_above_log2 a n) by lia. reflexivity. }
  rewrite Z.shiftl_mul_pow2 in D |- * by lia.
  rewrite <- Z.lxor_lor by exact D.
  rewrite Z.add_nocarry_lxor by exact D. reflexivity.
Qed.

Lemma wf3_zb_range : forall b, 0 <= zb b <= 1.
Proof. destruct b; simpl; lia. Qed.

Lemma wf3_hv_eq : forall last ty bsize, 0 <= ty < 4 -> 0 <= bsize ->
  blk_hv last ty bsize = zb last + 2 * ty + 8 * bsize.
Proof.
  intros. unfold blk_hv. pose proof (wf3_zb_range last).
  rewrite (wf3_lor_add (zb last) ty 1) by (change (2 ^ 1) with 2; lia).
  rewrite wf3_lor_add by (change (2 ^ 3) with 8; change (2 ^ 1) with 2; lia).
  change (2 ^ 1) with 2. change (2 ^ 3) with 8. lia.
Qed.

Lemma wf3_hv_range : forall last ty bsize, 0 <= ty < 4 -> 0 <= bsize <= 2 ^ 17 ->
  0 <= blk_hv last ty bsize < 2 ^ 21.
Proof. intros. rewrite wf3_hv_eq by lia. pose proof (wf3_zb_range last). lia. Qed.

Lemma wf3_le3 : forall v, le_bytes 3 v = [v mod 256; (v / 2 ^ 8) mod 256; (v / 2 ^ 16) mod 256].
Proof.
  intros. unfold le_bytes. rewrite !Z.div_div by lia. reflexivity.
Qed.

(* the body a branch of the loop wrote (type ty, t bytes of content c) *)
Definition wf3_bsize (ty t: Z) (body: list Z) : Z := if ty =? 1 then t else Zlength body.

Definition wbody_ok (bsm wsize: Z) (hist: list Z) (st: dstate) (out: list Z) (ty t: Z)
    (body: list Z) (st': dstate) (c: list Z) : Prop :=
  bytes_ok body /\ bytes_ok c /\ Zlength c = t /\ 0 <= t <= bsm /\
  ((ty = 0 /\ body = c /\ st' = st) \/
   (ty = 1 /\ 1 <= bsm /\ (exists x, body = [x] /\ c = repeat x (Z.to_nat t)) /\ st' = st) \/
   (ty = 2 /\ Zlength body <= bsm /\ decode_block st hist out body bsm wsize = Some (st', c))).

Lemma wf3_ty_range : forall bsm wsize hist st out ty t body st' c,
  wbody_ok bsm wsize hist st out ty t body st' c -> 0 <= ty <= 2.
Proof. intros. destruct H as (_ & _ & _ & _ & [(-> & _) | [(-> & _) | (-> & _)]]); lia. Qed.

Lemma wf3_bsize_range : forall bsm wsize hist st out ty t body st' c,
  wbody_ok bsm wsize hist st out ty t body st' c -> 0 <= wf3_bsize ty t body <= bsm.
Proof.
  intros. destruct H as (_ & _ & Hc & Ht & [(-> & -> & _) | [(-> & _) | (-> & Hb & _)]]);
    unfold wf3_bsize; simpl; try lia; pose proof (Zlength_nonneg body); lia.
Qed.

Lemma wf3_block_ok : forall bsm wsize hist st out ty t body st' c last,
  wbody_ok bsm wsize hist st out ty t body st' c ->
  wblock_ok bsm wsize hist st out last (le_bytes 3 (blk_hv last ty (wf3_bsize ty t body)) ++ body) st' c.
Proof.
  intros. pose proof (wf3_bsize_range _ _ _ _ _ _ _ _ _ _ H) as Hr.
  destruct H as (Hb & Hc & Hl & Ht & Hk).
  exists ty, (wf3_bsize ty t body), body. split; [reflexivity |]. split; [exact Hb |]. split; [exact Hc |].
  split; [exact Hr |].
  destruct Hk as [(-> & -> & ->) | [(-> & Hb1 & Hx & ->) | (-> & Hbl & Hd)]].
  - left. unfold wf3_bsize. simpl. auto.
  - right; left. unfold wf3_bsize. simpl. auto.
  - right; right. unfold wf3_bsize. simpl. auto.
Qed.

(* the C value of hv = last | (type << 1) | ((unsigned long long) bsize << 3) *)
Lemma wf3_hv_val : forall lb ty bs, 0 <= ty < 4 -> 0 <= bs <= 2 ^ 17 ->
  Int64.or (Int64.repr (Int.unsigned (Int.or (Int.repr (zb lb)) (Int.shl (Int.repr ty) (Int.repr 1)))))
           (Int64.shl (Int64.repr bs) (Int64.repr (Int.unsigned (Int.repr 3)))) =
  Int64.repr (blk_hv lb ty bs).
Proof.
  intros lb ty bs Hty Hbs. pose proof (wf3_zb_range lb).
  unfold blk_hv, Int.or, Int.shl, Int64.or, Int64.shl.
  rewrite (Int.unsigned_repr (zb lb)), (Int.unsigned_repr ty), (Int.unsigned_repr 1), (Int.unsigned_repr 3)
    by rep_lia.
  rewrite (Int.unsigned_repr (Z.shiftl ty 1)) by (rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 1) with 2; rep_lia).
  rewrite (wf3_lor_add (zb lb) ty 1) by (change (2 ^ 1) with 2; lia). change (2 ^ 1) with 2.
  rewrite (Int.unsigned_repr (zb lb + ty * 2)) by rep_lia.
  rewrite (Int64.unsigned_repr (zb lb + ty * 2)), (Int64.unsigned_repr bs), (Int64.unsigned_repr 3) by rep_lia.
  rewrite (Int64.unsigned_repr (Z.shiftl bs 3)) by (rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 3) with 8; rep_lia).
  reflexivity.
Qed.

Lemma wf3_land255 : forall x, Z.land x 255 = x mod 256.
Proof. intros. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma wf3_zext8 : forall z, 0 <= z < 256 -> Int.zero_ext 8 (Int.repr z) = Int.repr z.
Proof.
  intros. rewrite Int.zero_ext_and by lia. change (two_p 8 - 1) with 255.
  unfold Int.and. rewrite !Int.unsigned_repr by rep_lia. rewrite wf3_land255, Z.mod_small by lia. reflexivity.
Qed.

Lemma wf3_mm : forall x, 0 <= x <= Int64.max_unsigned -> Int64.Z_mod_modulus x = x.
Proof. intros. rewrite Int64.Z_mod_modulus_eq. apply Z.mod_small. unfold Int64.max_unsigned in H. lia. Qed.

(* the bytes of the block header stored: (unsigned char) ((hv >> 8k) & 255) *)
Lemma wf3_byte0 : forall hv, 0 <= hv < 2 ^ 21 ->
  Int.zero_ext 8 (Int.zero_ext 8 (Int.repr (Int64.Z_mod_modulus (Z.land (Int64.Z_mod_modulus hv) 255)))) =
  Int.repr (hv mod 256).
Proof.
  intros. pose proof (Z.mod_pos_bound hv 256 ltac:(lia)).
  rewrite (wf3_mm hv) by rep_lia. rewrite wf3_land255. rewrite wf3_mm by rep_lia.
  rewrite !wf3_zext8 by lia. reflexivity.
Qed.

Lemma wf3_byte : forall hv k, 0 <= hv < 2 ^ 21 -> 0 <= k < 64 ->
  Int.zero_ext 8 (Int.zero_ext 8 (Int.repr (Int64.Z_mod_modulus
    (Z.land (Int64.Z_mod_modulus (Z.shiftr (Int64.Z_mod_modulus hv) k)) 255)))) =
  Int.repr ((hv / 2 ^ k) mod 256).
Proof.
  intros. pose proof (Z.mod_pos_bound (hv / 2 ^ k) 256 ltac:(lia)).
  assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  assert (0 <= hv / 2 ^ k <= hv) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; nia).
  rewrite (wf3_mm hv) by rep_lia. rewrite Z.shiftr_div_pow2 by lia. rewrite (wf3_mm (hv / 2 ^ k)) by rep_lia.
  rewrite wf3_land255. rewrite wf3_mm by rep_lia.
  rewrite !wf3_zext8 by lia. reflexivity.
Qed.

Lemma wf3_le_bytes_ok : forall k v, bytes_ok (le_bytes k v).
Proof.
  induction k; intros; simpl; constructor; auto.
  unfold is_byte. apply Z.mod_pos_bound. lia.
  apply IHk.
Qed.

Lemma wf3_len_le3 : forall v, Zlength (le_bytes 3 v) = 3.
Proof. intros. reflexivity. Qed.

Lemma wf3_bytes_hdr : forall pre body hv, bytes_ok ((pre ++ [0; 0; 0]) ++ body) ->
  bytes_ok (pre ++ le_bytes 3 hv ++ body).
Proof.
  unfold bytes_ok. intros. rewrite !Forall_app in *. destruct H as [[H1 _] H3].
  split; [exact H1 | split; [apply wf3_le_bytes_ok | exact H3]].
Qed.
