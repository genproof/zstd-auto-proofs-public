(* w_frame's blocks: what the format model's block walks (Series.decode_blocks,
   Frame.blocks_size) make of the blocks w_frame writes, followed by anything. *)
Require Import Zstd.proof.harness.writer.model.WF_Defs.
Local Open Scope bool_scope.

Local Ltac pl := repeat match goal with
  | |- context [2 ^ ?n] => let v := eval vm_compute in (2 ^ n) in change (2 ^ n) with v in *
  | H: context [2 ^ ?n] |- _ => let v := eval vm_compute in (2 ^ n) in change (2 ^ n) with v in *
  end; lia.

Lemma wfb_le_value_bytes : forall k v,
  le_value (le_bytes k v) = v mod 2 ^ (8 * Z.of_nat k).
Proof.
  induction k; intros v.
  - simpl. rewrite Z.mod_1_r. reflexivity.
  - cbn [le_bytes le_value]. rewrite IHk.
    replace (8 * Z.of_nat (S k)) with (8 + 8 * Z.of_nat k) by lia.
    rewrite Z.pow_add_r by lia.
    rewrite Z.rem_mul_r by (try apply Z.pow_pos_nonneg; lia). reflexivity.
Qed.

Lemma wfb_le_bytes_ok : forall k v, bytes_ok (le_bytes k v).
Proof.
  induction k; intros v; simpl; constructor.
  - unfold is_byte. pose proof (Z.mod_pos_bound v 256). lia.
  - apply IHk.
Qed.

Lemma wfb_zlen_nonneg : forall (l: list Z), 0 <= Zlength l.
Proof. intros; rewrite Zlength_correct; lia. Qed.

Lemma wfb_zlen_app : forall (l1 l2: list Z), Zlength (l1 ++ l2) = Zlength l1 + Zlength l2.
Proof. intros; rewrite !Zlength_correct, app_length; lia. Qed.

Lemma wfb_gtb_false : forall a b, a <= b -> (a >? b) = false.
Proof. intros; rewrite Z.gtb_ltb; apply Z.ltb_ge; lia. Qed.

Lemma wfb_le_bytes_len : forall k v, length (le_bytes k v) = k.
Proof. induction k; intros; simpl; auto. Qed.

Lemma wfb_lor_add : forall a b r, 0 <= a < 2 ^ r -> 0 <= b -> 0 <= r ->
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
  rewrite <- Z.lxor_lor by exact D.
  rewrite <- Z.add_nocarry_lxor by exact D. rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.

Lemma wfb_hv : forall last ty bsize, 0 <= ty <= 2 -> 0 <= bsize ->
  blk_hv last ty bsize = zb last + 2 * ty + 8 * bsize.
Proof.
  intros last ty bsize Hty Hb. unfold blk_hv.
  assert (Hl: 0 <= zb last <= 1) by (destruct last; simpl; lia).
  rewrite (wfb_lor_add (zb last) ty 1) by pl.
  rewrite (wfb_lor_add _ bsize 3) by pl.
  pl.
Qed.

Lemma wfb_props : forall last ty bsize body t, 0 <= ty <= 2 -> 0 <= bsize <= 2 ^ 17 ->
  block_props_of ((le_bytes 3 (blk_hv last ty bsize) ++ body) ++ t) =
  {| bp_last := zb last; bp_type := ty; bp_origSize := bsize |}.
Proof.
  intros last ty bsize body t Hty Hb.
  assert (Hl: 0 <= zb last <= 1) by (destruct last; simpl; lia).
  unfold block_props_of, le_field, slice. rewrite <- app_assoc.
  change (Z.to_nat 0) with O. rewrite skipn_O.
  rewrite firstn_app, wfb_le_bytes_len, Nat.sub_diag, firstn_O, app_nil_r.
  rewrite firstn_all2 by (rewrite wfb_le_bytes_len; lia).
  rewrite wfb_le_value_bytes. rewrite wfb_hv by lia.
  rewrite Z.mod_small by pl.
  f_equal.
  - change 1 with (Z.ones 1). rewrite Z.land_ones by lia.
    replace (zb last + 2 * ty + 8 * bsize) with (zb last + (ty + 4 * bsize) * 2 ^ 1) by pl.
    rewrite Z.mod_add by pl. apply Z.mod_small; simpl; lia.
  - change 3 with (Z.ones 2). rewrite Z.land_ones by lia. rewrite Z.shiftr_div_pow2 by lia.
    replace (zb last + 2 * ty + 8 * bsize) with (zb last + (ty + 4 * bsize) * 2 ^ 1) by pl.
    rewrite Z.div_add by pl. rewrite (Z.div_small (zb last)) by pl.
    replace (0 + (ty + 4 * bsize)) with (ty + bsize * 2 ^ 2) by pl.
    rewrite Z.mod_add by pl. apply Z.mod_small; simpl; lia.
  - rewrite Z.shiftr_div_pow2 by lia.
    replace (zb last + 2 * ty + 8 * bsize) with ((zb last + 2 * ty) + bsize * 2 ^ 3) by pl.
    rewrite Z.div_add by pl. rewrite Z.div_small by pl. lia.
Qed.

Lemma wfb_step : forall bsm wsize hist st out last b st' c f t,
  bsm <= 2 ^ 17 ->
  wblock_ok bsm wsize hist st out last b st' c ->
  bytes_ok b /\ bytes_ok c /\ 3 <= Zlength b /\
  decode_blocks (S f) st hist (b ++ t) out bsm wsize =
    (if last then Some (out ++ c, Zlength b)
     else match decode_blocks f st' hist t (out ++ c) bsm wsize with
          | Some (o, k) => Some (o, Zlength b + k) | None => None end) /\
  blocks_size (S f) (b ++ t) =
    (if last then Some (Zlength b, 1)
     else match blocks_size f t with
          | Some (k, n) => Some (Zlength b + k, n + 1) | None => None end).
Proof.
  intros bsm wsize hist st out last b st' c f t Hbsm
    (ty & bsize & body & -> & Hbody & Hc & Hbs & Hcase).
  assert (Hty: 0 <= ty <= 2) by (destruct Hcase as [(-> & _) | [(-> & _) | (-> & _)]]; lia).
  pose proof (wfb_props last ty bsize body t Hty ltac:(lia)) as Hp.
  pose proof (wfb_zlen_nonneg t).
  pose proof (wfb_zlen_nonneg body).
  assert (Hlen3: Zlength (le_bytes 3 (blk_hv last ty bsize)) = 3).
  { rewrite Zlength_correct, wfb_le_bytes_len. reflexivity. }
  assert (Hskip: skipn (Z.to_nat (3 + Zlength body)) ((le_bytes 3 (blk_hv last ty bsize) ++ body) ++ t) = t).
  { rewrite Zlength_correct.
    replace (Z.to_nat (3 + Z.of_nat (length body))) with (length (le_bytes 3 (blk_hv last ty bsize) ++ body))
      by (rewrite app_length, wfb_le_bytes_len; lia).
    rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity. }
  assert (Hslice: slice ((le_bytes 3 (blk_hv last ty bsize) ++ body) ++ t) 3 (Zlength body) = body).
  { unfold slice. rewrite <- app_assoc. change (Z.to_nat 3) with 3%nat.
    rewrite skipn_app, wfb_le_bytes_len. rewrite skipn_all2 by (rewrite wfb_le_bytes_len; lia).
    simpl. rewrite firstn_app, Zlength_correct, Nat2Z.id, firstn_all, Nat.sub_diag, firstn_O, app_nil_r.
    reflexivity. }
  assert (HlenS: Zlength ((le_bytes 3 (blk_hv last ty bsize) ++ body) ++ t) = 3 + Zlength body + Zlength t).
  { rewrite !wfb_zlen_app, Hlen3. lia. }
  assert (Hbl: Zlength (le_bytes 3 (blk_hv last ty bsize) ++ body) = 3 + Zlength body).
  { rewrite wfb_zlen_app, Hlen3. lia. }
  split; [apply Forall_app; split; auto; apply wfb_le_bytes_ok |].
  split; [exact Hc |]. split; [lia |].
  unfold cblock_size. cbn [decode_blocks blocks_size]. unfold cblock_size.
  rewrite Hp, HlenS. cbn [bp_type bp_last bp_origSize]. unfold ZSTD_blockHeaderSize.
  replace (3 + Zlength body + Zlength t <? 3) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite Hbl.
  destruct Hcase as [(-> & -> & -> & ->) | [(-> & Hb1 & (x & -> & ->) & ->) | (-> & -> & Hd)]].
  - simpl (0 =? 1); simpl (0 =? 3); simpl (0 =? 0); cbv iota.
    rewrite Hslice, Hskip. repeat (rewrite wfb_gtb_false by lia).
    destruct last; cbn; auto.
  - change (Zlength [x]) with 1 in *. simpl (1 =? 1); simpl (1 =? 0); cbv iota.
    rewrite Hslice, Hskip.
    repeat (rewrite wfb_gtb_false by lia).
    destruct last; cbn; auto.
  - simpl (2 =? 1); simpl (2 =? 3); simpl (2 =? 0); cbv iota.
    rewrite Hslice, Hd, Hskip. repeat (rewrite wfb_gtb_false by lia).
    destruct last; cbn; auto.
Qed.

Lemma wfb_pre : forall bsm wsize hist st0 bb st out nb,
  bsm <= 2 ^ 17 ->
  wblocks_pre bsm wsize hist st0 bb st out nb ->
  bytes_ok bb /\ bytes_ok out /\ 0 <= nb /\ 3 * nb <= Zlength bb /\
  (forall f t, decode_blocks (Z.to_nat nb + f) st0 hist (bb ++ t) nil bsm wsize =
     match decode_blocks f st hist t out bsm wsize with
     | Some (o, k) => Some (o, Zlength bb + k) | None => None end) /\
  (forall f t, blocks_size (Z.to_nat nb + f) (bb ++ t) =
     match blocks_size f t with
     | Some (k, n) => Some (Zlength bb + k, n + nb) | None => None end).
Proof.
  intros bsm wsize hist st0 bb st out nb Hbsm H.
  induction H as [| bb st out nb b st' c Hpre IH Hb].
  - split; [constructor |]. split; [constructor |]. split; [lia |]. split; [rewrite Zlength_correct; simpl; lia |].
    split; intros f t; simpl;
      [destruct (decode_blocks f st0 hist t [] bsm wsize) as [[o k]|] | destruct (blocks_size f t) as [[k n]|]];
      auto; f_equal; f_equal; lia.
  - destruct IH as (Hbb & Hout & Hnb & Hlen & IHd & IHs).
    split; [| split; [| split; [lia | split]]].
    + apply Forall_app; split; auto. apply (wfb_step _ _ _ _ _ _ _ _ _ O nil Hbsm Hb).
    + apply Forall_app; split; auto. apply (wfb_step _ _ _ _ _ _ _ _ _ O nil Hbsm Hb).
    + destruct (wfb_step _ _ _ _ _ _ _ _ _ O nil Hbsm Hb) as (_ & _ & H3 & _).
      rewrite wfb_zlen_app. lia.
    + split; intros f t; replace (Z.to_nat (nb + 1) + f)%nat with (Z.to_nat nb + S f)%nat by lia;
        rewrite <- app_assoc.
      * rewrite IHd. destruct (wfb_step _ _ _ _ _ _ _ _ _ f t Hbsm Hb) as (_ & _ & _ & -> & _).
        destruct (decode_blocks f st' hist t (out ++ c) bsm wsize) as [[o k]|]; auto.
        rewrite wfb_zlen_app. f_equal. f_equal. lia.
      * rewrite IHs. destruct (wfb_step _ _ _ _ _ _ _ _ _ f t Hbsm Hb) as (_ & _ & _ & _ & ->).
        destruct (blocks_size f t) as [[k n]|]; auto.
        rewrite wfb_zlen_app. f_equal; f_equal; lia.
Qed.

Lemma wf_blocks : forall bsm wsize hist st0 bb st out nb b st' c t fuel,
  0 <= bsm <= 2 ^ 17 ->
  wblocks_pre bsm wsize hist st0 bb st out nb ->
  wblock_ok bsm wsize hist st out true b st' c ->
  (length (bb ++ b) <= fuel)%nat ->
  bytes_ok (bb ++ b) /\ bytes_ok (out ++ c) /\ 3 <= Zlength b /\
  decode_blocks fuel st0 hist (bb ++ b ++ t) nil bsm wsize = Some (out ++ c, Zlength (bb ++ b)) /\
  blocks_size fuel (bb ++ b ++ t) = Some (Zlength (bb ++ b), nb + 1).
Proof.
  intros bsm wsize hist st0 bb st out nb b st' c t fuel Hbsm Hpre Hb Hfuel.
  destruct (wfb_pre bsm wsize hist st0 bb st out nb ltac:(lia) Hpre) as (Hbb & Hout & Hnb & Hlen & Hd & Hs).
  destruct (wfb_step bsm wsize hist st out true b st' c O nil ltac:(lia) Hb) as (Hbo & Hc & H3 & _).
  rewrite app_length in Hfuel.
  rewrite Zlength_correct in Hlen, H3.
  replace fuel with (Z.to_nat nb + S (fuel - Z.to_nat nb - 1))%nat by lia.
  rewrite Hd, Hs.
  destruct (wfb_step bsm wsize hist st out true b st' c (fuel - Z.to_nat nb - 1) t ltac:(lia) Hb)
    as (_ & _ & _ & -> & ->).
  rewrite wfb_zlen_app, !Zlength_correct.
  split; [apply Forall_app; auto |]. split; [apply Forall_app; auto |]. split; [lia |].
  split; f_equal; f_equal; lia.
Qed.
