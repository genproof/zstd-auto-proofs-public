(* FSE table descriptions written by fse_put_description, read by the model's read_ncount (plain Coq). *)
Require Import Zstd.proof.harness.writer.model.WModel.
Require Import Zstd.proof.harness.writer.model.WM_Bits.

(* ---------------------------------------------------------------------------------------------- *)
(* widths of fields *)

Fixpoint wsum (fs: list (Z * Z)) : Z :=
  match fs with nil => 0 | f :: fs' => snd f + wsum fs' end.

Lemma wsum_cons : forall f fs, wsum (f :: fs) = snd f + wsum fs.
Proof. reflexivity. Qed.

Lemma wsum_app : forall a b, wsum (a ++ b) = wsum a + wsum b.
Proof. induction a as [|f a IH]; intros; simpl; [lia|]. rewrite IH; lia. Qed.

Lemma wsum_repeat : forall f n, wsum (repeat f n) = snd f * Z.of_nat n.
Proof. induction n as [|n IH]; simpl repeat; [simpl; lia|]. rewrite wsum_cons, IH; lia. Qed.

Lemma fields_wl_snd : forall fs W L, snd (fields_wl fs W L) = L + wsum fs.
Proof. induction fs as [|[v nb] fs IH]; intros; simpl; [lia|]. rewrite IH. lia. Qed.

Lemma fields_L_wsum : forall fs, fields_L fs = wsum fs.
Proof. intros. unfold fields_L. rewrite fields_wl_snd. lia. Qed.

Lemma wsum_nonneg : forall fs, fields_ok fs -> 0 <= wsum fs.
Proof. induction 1 as [|f fs [H1 H2] _ IH]; simpl in *; lia. Qed.

Lemma Zmod_pow2_le : forall x k n, 0 <= k <= n -> (x mod 2 ^ n) mod 2 ^ k = x mod 2 ^ k.
Proof.
  intros x k n Hk.
  assert (E: 2 ^ n = 2 ^ (n - k) * 2 ^ k) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite (Z.mod_eq x (2 ^ n)) by lia.
  replace (x - 2 ^ n * (x / 2 ^ n)) with (x + (- (2 ^ (n - k) * (x / 2 ^ n))) * 2 ^ k) by (rewrite E; ring).
  apply Z.mod_add. lia.
Qed.

(* the padded bytes of fs, then anything *)
Definition bpad (fs: list (Z * Z)) (rest: list Z) : list Z := bw_pad (fields_W fs) (fields_L fs) ++ rest.

Lemma bpad_facts : forall fs rest, fields_ok fs ->
  0 <= fields_L fs /\ 0 <= fields_W fs < 2 ^ fields_L fs /\
  bytes_ok (bw_pad (fields_W fs) (fields_L fs)) /\
  Zlength (bw_pad (fields_W fs) (fields_L fs)) = (fields_L fs + 7) / 8 /\
  (fields_L fs + 7) / 8 <= Zlength (bpad fs rest).
Proof.
  intros fs rest Hok.
  destruct (fields_wl_range fs 0 0 Hok) as [HL HW]; try (simpl; lia).
  fold (fields_L fs) in HL, HW. fold (fields_W fs) in HW.
  destruct (bw_pad_len (fields_W fs) (fields_L fs)) as [Hb Hl]; try lia.
  assert (Za: forall a b: list Z, Zlength (a ++ b) = Zlength a + Zlength b)
    by (intros; rewrite !Zlength_correct, length_app; lia).
  unfold bpad. rewrite Za, Hl. assert (0 <= Zlength rest) by (rewrite Zlength_correct; lia). repeat split; try lia; auto.
Qed.

(* k <= nb bits read at the start of a field *)
Lemma read_field : forall fs rest pre v nb post k,
  fs = pre ++ (v, nb) :: post -> fields_ok fs -> 0 <= k <= nb ->
  fbits (bpad fs rest) (fields_L pre) k = v mod 2 ^ k.
Proof.
  intros fs rest pre v nb post k E Hok Hk.
  destruct (bpad_facts fs rest Hok) as (HL & HW & _).
  assert (Hok' := Hok). rewrite E in Hok'.
  apply Forall_app in Hok' as [Hpre Hpost]. inversion Hpost as [|? ? [Hnb Hv] Hpost']; subst x l. simpl in Hnb, Hv.
  unfold bpad. rewrite fbits_pad; try lia.
  - rewrite <- (Zmod_pow2_le _ k nb) by lia. subst fs. rewrite fields_field; auto.
  - rewrite fields_L_wsum. apply wsum_nonneg; auto.
  - rewrite !fields_L_wsum. rewrite E, wsum_app, wsum_cons. simpl snd.
    pose proof (wsum_nonneg _ Hpost'). lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* one count field *)

Lemma hb_bounds : forall R, 1 <= R <= 512 ->
  2 ^ highbit (R + 1) <= R + 1 < 2 ^ (highbit (R + 1) + 1) /\ 1 <= highbit (R + 1) <= 9.
Proof.
  intros R HR. unfold highbit.
  pose proof (Z.log2_spec (R + 1) ltac:(lia)) as Hs. rewrite <- Z.add_1_r in Hs.
  assert (H1: Z.log2 2 <= Z.log2 (R + 1)) by (apply Z.log2_le_mono; lia).
  assert (H9: Z.log2 (R + 1) <= Z.log2 1023) by (apply Z.log2_le_mono; lia).
  change (Z.log2 2) with 1 in H1. change (Z.log2 1023) with 9 in H9. lia.
Qed.

Lemma hb_same : forall x y, 1 <= x -> 2 ^ highbit x <= y <= x -> highbit y = highbit x.
Proof.
  intros x y Hx Hy. unfold highbit in *.
  pose proof (Z.log2_spec x ltac:(lia)) as Hs.
  apply Z.log2_unique; [apply Z.log2_nonneg | lia].
Qed.

Lemma ncf_spec : forall q R, 1 <= R <= 512 -> -1 <= q <= R ->
  (q + 1 < 2 ^ (highbit (R + 1) + 1) - 1 - (R + 1) /\ ncount_field q R = (q + 1, highbit (R + 1))) \/
  (2 ^ (highbit (R + 1) + 1) - 1 - (R + 1) <= q + 1 < 2 ^ highbit (R + 1) /\
     ncount_field q R = (q + 1, highbit (R + 1) + 1)) \/
  (2 ^ highbit (R + 1) <= q + 1 /\
     ncount_field q R = (q + 1 + (2 ^ (highbit (R + 1) + 1) - 1 - (R + 1)), highbit (R + 1) + 1)).
Proof.
  intros q R HR Hq. unfold ncount_field. cbv zeta.
  replace (highbit (R + 1) + 1 - 1) with (highbit (R + 1)) by lia.
  destruct (q + 1 <? 2 ^ (highbit (R + 1) + 1) - 1 - (R + 1)) eqn:E1.
  - left. apply Z.ltb_lt in E1. auto.
  - apply Z.ltb_ge in E1. destruct (q + 1 <=? 2 ^ highbit (R + 1) - 1) eqn:E2.
    + right; left. apply Z.leb_le in E2. split; [lia | reflexivity].
    + right; right. apply Z.leb_gt in E2. split; [lia | reflexivity].
Qed.

Lemma ncount_field_ok : forall q R, 1 <= R <= 512 -> -1 <= q <= R ->
  0 <= snd (ncount_field q R) <= 10 /\ 0 <= fst (ncount_field q R) < 2 ^ snd (ncount_field q R).
Proof.
  intros q R HR Hq. destruct (hb_bounds R HR) as [Hb Hh].
  assert (E: 2 ^ (highbit (R + 1) + 1) = 2 * 2 ^ highbit (R + 1)) by (rewrite Z.pow_add_r by lia; change (2 ^ 1) with 2; lia).
  destruct (ncf_spec q R HR Hq) as [[H1 ->]|[[H1 ->]|[H1 ->]]]; simpl fst; simpl snd; lia.
Qed.

(* the decoder reads one count: rdc is the reading part of ncount_loop *)
Definition rdc (b: list Z) (p remaining threshold nbBits: Z) : Z * Z :=
  let max := (2 * threshold - 1) - remaining in
  let low := fbits b p (nbBits - 1) in
  if low <? max then (low, p + nbBits - 1)
  else let c := fbits b p nbBits in
       ((if c >=? threshold then c - max else c), p + nbBits).

Lemma rdc_ok : forall fs rest pre q R post,
  fs = pre ++ ncount_field q R :: post -> fields_ok fs -> 1 <= R <= 512 -> -1 <= q <= R ->
  rdc (bpad fs rest) (fields_L pre) (R + 1) (2 ^ highbit (R + 1)) (highbit (R + 1) + 1) =
    (q + 1, fields_L pre + snd (ncount_field q R)).
Proof.
  intros fs rest pre q R post E Hok HR Hq. destruct (hb_bounds R HR) as [Hb Hh].
  assert (E2: 2 ^ (highbit (R + 1) + 1) = 2 * 2 ^ highbit (R + 1)) by (rewrite Z.pow_add_r by lia; change (2 ^ 1) with 2; lia).
  unfold rdc. cbv zeta. replace (highbit (R + 1) + 1 - 1) with (highbit (R + 1)) by lia.
  destruct (ncf_spec q R HR Hq) as [[H1 Hf]|[[H1 Hf]|[H1 Hf]]]; rewrite Hf in E |- *; simpl snd.
  - rewrite (read_field fs rest pre _ _ post (highbit (R + 1)) E Hok) by lia.
    rewrite Z.mod_small by lia.
    replace (2 * 2 ^ highbit (R + 1) - 1 - (R + 1)) with (2 ^ (highbit (R + 1) + 1) - 1 - (R + 1)) by lia.
    destruct (q + 1 <? _) eqn:C; [|apply Z.ltb_ge in C; lia]. f_equal; lia.
  - rewrite (read_field fs rest pre _ _ post (highbit (R + 1)) E Hok) by lia.
    rewrite (read_field fs rest pre _ _ post (highbit (R + 1) + 1) E Hok) by lia.
    rewrite !Z.mod_small by lia.
    destruct (q + 1 <? _) eqn:C; [apply Z.ltb_lt in C; lia|].
    destruct (q + 1 >=? _) eqn:C2; [apply Z.geb_le in C2; lia|]. f_equal; lia.
  - rewrite (read_field fs rest pre _ _ post (highbit (R + 1)) E Hok) by lia.
    rewrite (read_field fs rest pre _ _ post (highbit (R + 1) + 1) E Hok) by lia.
    rewrite (Z.mod_small _ (2 ^ (highbit (R + 1) + 1))) by lia.
    rewrite <- (Z.mod_unique (q + 1 + (2 ^ (highbit (R + 1) + 1) - 1 - (R + 1))) (2 ^ highbit (R + 1)) 1
                  (q + 1 + (2 ^ (highbit (R + 1) + 1) - 1 - (R + 1)) - 2 ^ highbit (R + 1))) by lia.
    destruct (_ <? _) eqn:C; [apply Z.ltb_lt in C; lia|].
    destruct (_ >=? _) eqn:C2; [|rewrite Z.geb_leb, Z.leb_gt in C2; lia]. f_equal; lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* distributions *)

Lemma zsum_cons : forall a l, zsum (a :: l) = a + zsum l.
Proof. reflexivity. Qed.

Lemma zsum_app : forall a b, zsum (a ++ b) = zsum a + zsum b.
Proof. induction a as [|x a IH]; intros; simpl; [lia|]. unfold zsum in *. simpl. rewrite IH. lia. Qed.

Lemma ncount_of_facts : forall p, -1 <= p ->
  0 <= ncount_of p /\ p <= ncount_of p /\ (p <> 0 -> 1 <= ncount_of p) /\
  ((p = -1 /\ ncount_of p = 1) \/ (p <> -1 /\ ncount_of p = p)).
Proof. intros p Hp. unfold ncount_of. destruct (p =? -1) eqn:E; [apply Z.eqb_eq in E | apply Z.eqb_neq in E]; lia. Qed.

Lemma zsum_nonneg : forall l, Forall (fun p => -1 <= p) l -> 0 <= zsum (map ncount_of l).
Proof.
  induction 1 as [|x l Hx _ IH]; [simpl; lia|]. cbn [map]. rewrite zsum_cons.
  pose proof (ncount_of_facts x Hx). lia.
Qed.

Lemma zsum_pos : forall l, l <> nil -> last l 0 <> 0 -> Forall (fun p => -1 <= p) l -> 1 <= zsum (map ncount_of l).
Proof.
  induction l as [|x l IH]; intros Hne Hl Hf; [congruence|].
  inversion Hf as [|? ? Hx Hf']; subst. cbn [map]. rewrite zsum_cons.
  pose proof (ncount_of_facts x Hx). pose proof (zsum_nonneg l Hf').
  destruct l as [|y l']; [simpl in Hl |- *; unfold zsum; simpl; lia|].
  assert (1 <= zsum (map ncount_of (y :: l'))) by (apply IH; auto; congruence). lia.
Qed.

Lemma zrun_split : forall l, l <> nil -> last l 0 <> 0 ->
  exists q l2, l = repeat 0 (zrun l) ++ q :: l2 /\ q <> 0 /\ skipn (zrun l) l = q :: l2.
Proof.
  induction l as [|x l IH]; intros Hne Hl; [congruence|].
  simpl zrun. destruct (x =? 0) eqn:E.
  - apply Z.eqb_eq in E. subst x. destruct l as [|y l']; [simpl in Hl; congruence|].
    destruct (IH ltac:(congruence) Hl) as (q & l2 & H1 & H2 & H3).
    exists q, l2. split; [cbn [repeat app]; rewrite <- H1; reflexivity|]. split; [auto | exact H3].
  - apply Z.eqb_neq in E. exists x, l. simpl. auto.
Qed.

Lemma last_app_cons : forall (a: list Z) q l, last (a ++ q :: l) 0 = last (q :: l) 0.
Proof.
  induction a as [|x a IH]; intros; [reflexivity|]. simpl.
  destruct (a ++ q :: l) eqn:E; [destruct a; discriminate|].
  rewrite <- E. apply IH.
Qed.

Lemma zsum_repeat0 : forall n, zsum (map ncount_of (repeat 0 n)) = 0.
Proof. induction n as [|n IH]; [reflexivity|]. simpl. unfold zsum in *. simpl. rewrite IH. reflexivity. Qed.

Lemma last_cons_cons : forall (x y: Z) l, last (x :: y :: l) 0 = last (y :: l) 0.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the size of a description: at most 9 bits per symbol plus a potential of the remaining count
   (Atab; Ntab when the next count is non-zero), checked by computation *)

Definition Atab (R: Z) : Z :=
  if R <=? 0 then 0 else if R <=? 2 then -7 else if R <=? 6 then -6 else if R <=? 14 then -5 else if R <=? 30 then -4 else if R <=? 62 then -3 else if R <=? 126 then -2 else if R <=? 252 then -1 else if R <=? 254 then 0 else if R <=? 381 then 1 else if R <=? 445 then 2 else if R <=? 477 then 3 else if R <=? 493 then 4 else if R <=? 501 then 5 else if R <=? 505 then 6 else if R <=? 507 then 7 else if R <=? 508 then 8 else if R <=? 509 then 10 else if R <=? 510 then 12 else if R <=? 511 then 14 else 16.

Definition Ntab (R: Z) : Z := Atab R - Z.max 0 (snd (ncount_field 0 R) - 7).

Fixpoint all_upto (f: Z -> bool) (n: nat) : bool :=
  match n with O => true | S m => f (Z.of_nat n) && all_upto f m end.

Lemma all_upto_ok : forall f n k, all_upto f n = true -> 1 <= k <= Z.of_nat n -> f k = true.
Proof.
  induction n as [|n IH]; intros k H Hk; [lia|].
  simpl in H. apply andb_prop in H as [H1 H2].
  destruct (Z.eq_dec k (Z.of_nat (S n))) as [->|Hne]; [exact H1|].
  apply IH; [exact H2 | lia].
Qed.

Definition chk_p (R p: Z) : bool := snd (ncount_field p R) + Atab (R - ncount_of p) <=? 9 + Ntab R.

Definition chk_R (R: Z) : bool := chk_p R (-1) && all_upto (chk_p R) (Z.to_nat R).

Lemma chk_all_true : all_upto chk_R 512 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma chk_ok : forall R p, 1 <= R <= 512 -> (p = -1 \/ 1 <= p <= R) ->
  snd (ncount_field p R) + Atab (R - ncount_of p) <= 9 + Ntab R.
Proof.
  intros R p HR Hp.
  assert (HR': chk_R R = true).
  { apply (all_upto_ok chk_R 512 R chk_all_true). change (Z.of_nat 512) with 512. lia. }
  unfold chk_R in HR'. apply andb_prop in HR' as [H1 H2].
  apply Z.leb_le. change (chk_p R p = true).
  destruct Hp as [->|Hp]; [exact H1|].
  apply (all_upto_ok (chk_p R) (Z.to_nat R) p H2). lia.
Qed.

Lemma nf_props : forall f l R, (length l <= f)%nat -> (l = nil \/ last l 0 <> 0) ->
  Forall (fun p => -1 <= p) l -> zsum (map ncount_of l) = R -> R <= 512 ->
  fields_ok (ncount_fields f l R) /\ wsum (ncount_fields f l R) <= 9 * Zlength l + Atab R /\
  (forall q l', l = q :: l' -> q <> 0 -> wsum (ncount_fields f l R) <= 9 * Zlength l + Ntab R).
Proof.
  induction f as [|f IH]; intros l R Hlen Hl Hf Hs HR.
  - destruct l; [|simpl in Hlen; lia]. simpl in Hs |- *. subst R.
    split; [constructor|]. split; [vm_compute; congruence|]. intros; discriminate.
  - destruct l as [|q l'].
    { simpl in Hs |- *. subst R. split; [constructor|]. split; [vm_compute; congruence|]. intros; discriminate. }
    inversion Hf as [|? ? Hq Hf']; subst.
    cbn [map] in HR |- *. rewrite zsum_cons in HR |- *.
    pose proof (ncount_of_facts q Hq) as Hc. pose proof (zsum_nonneg l' Hf') as Hs'.
    assert (HR1: 1 <= ncount_of q + zsum (map ncount_of l')).
    { change (1 <= zsum (map ncount_of (q :: l'))). apply zsum_pos; auto. congruence.
      destruct Hl; [discriminate|auto]. }
    assert (Hlast': l' = nil \/ last l' 0 <> 0).
    { destruct l' as [|y l'']; [left; auto|right]. destruct Hl as [Hl|Hl]; [discriminate|].
      rewrite last_cons_cons in Hl. auto. }
    simpl in Hlen. rewrite Zlength_cons.
    cbn [ncount_fields]. destruct (q =? 0) eqn:Eq.
    + apply Z.eqb_eq in Eq. subst q.
      replace (ncount_of 0 + zsum (map ncount_of l') - ncount_of 0) with (zsum (map ncount_of l')) by lia.
      replace (ncount_of 0) with 0 in * by reflexivity. rewrite !Z.add_0_l in *.
      destruct Hlast' as [->|Hlast']; [simpl in HR1; unfold zsum in HR1; simpl in HR1; lia|].
      assert (Hne: l' <> nil) by (intro; subst; simpl in Hlast'; congruence).
      destruct (zrun_split l' Hne Hlast') as (q2 & l2 & El & Hq2 & Es).
      set (z := zrun l') in *. rewrite Es.
      assert (Hf2: Forall (fun p => -1 <= p) (q2 :: l2)) by (rewrite El in Hf'; apply Forall_app in Hf'; tauto).
      assert (Hs2: zsum (map ncount_of (q2 :: l2)) = zsum (map ncount_of l')).
      { rewrite El. rewrite map_app, zsum_app, zsum_repeat0. lia. }
      assert (Hlen2: length l' = (z + S (length l2))%nat) by (rewrite El at 1; rewrite length_app, repeat_length; reflexivity).
      assert (Hl2: q2 :: l2 = nil \/ last (q2 :: l2) 0 <> 0) by (right; rewrite El, last_app_cons in Hlast'; auto).
      destruct (IH (q2 :: l2) (zsum (map ncount_of l')) ltac:(simpl; lia) Hl2 Hf2 Hs2 ltac:(lia))
        as (Hok2 & _ & Hb2).
      specialize (Hb2 q2 l2 eq_refl Hq2).
      assert (H0: 0 <= snd (ncount_field 0 (zsum (map ncount_of l'))) <= 10 /\
                  0 <= fst (ncount_field 0 (zsum (map ncount_of l'))) < 2 ^ snd (ncount_field 0 (zsum (map ncount_of l'))))
        by (apply ncount_field_ok; lia).
      split; [|split].
      * constructor; [split; [lia | apply H0]|]. apply Forall_app. split.
        { apply Forall_forall. intros x Hx. apply repeat_spec in Hx. subst x. cbn [fst snd]. change (2 ^ 2) with 4. lia. }
        apply Forall_app. split; auto. constructor; [|constructor]. cbn [fst snd].
        pose proof (Nat.mod_upper_bound z 3 ltac:(lia)). change (2 ^ 2) with 4. lia.
      * rewrite wsum_cons, !wsum_app, wsum_repeat, wsum_cons. simpl wsum. simpl snd.
        rewrite Zlength_correct, Hlen2. rewrite Zlength_correct in Hb2. simpl length in Hb2.
        assert (Hz: (z / 3 <= z)%nat) by (apply Nat.div_le_upper_bound; lia).
        unfold Ntab in Hb2. pose proof (Z.le_max_r 0 (snd (ncount_field 0 (zsum (map ncount_of l'))) - 7)). lia.
      * intros q l'' Heq Hq0. injection Heq as Hq' _. congruence.
    + apply Z.eqb_neq in Eq.
      set (R2 := ncount_of q + zsum (map ncount_of l') - ncount_of q).
      assert (ER2: R2 = zsum (map ncount_of l')) by (unfold R2; lia).
      destruct (IH l' R2 ltac:(lia) Hlast' Hf' ltac:(lia) ltac:(lia)) as (Hok2 & Hb2 & _).
      assert (Hp: q = -1 \/ 1 <= q <= ncount_of q + zsum (map ncount_of l')) by lia.
      pose proof (chk_ok (ncount_of q + zsum (map ncount_of l')) q ltac:(lia) Hp) as Hchk. fold R2 in Hchk.
      assert (Hnb: wsum (ncount_field q (ncount_of q + zsum (map ncount_of l')) :: ncount_fields f l' R2) <=
                   9 * Z.succ (Zlength l') + Ntab (ncount_of q + zsum (map ncount_of l'))).
      { rewrite wsum_cons. lia. }
      split; [|split].
      * constructor; auto.
        destruct (ncount_field_ok q (ncount_of q + zsum (map ncount_of l'))) as [A1 A2]; lia.
      * unfold Ntab in Hnb. pose proof (Z.le_max_l 0 (snd (ncount_field 0 (ncount_of q + zsum (map ncount_of l'))) - 7)). lia.
      * intros. auto.
Qed.


(* ---------------------------------------------------------------------------------------------- *)
(* the decoder's loop reads the fields back *)

Lemma Zlen_nn : forall (l: list Z), 0 <= Zlength l.
Proof. intros. rewrite Zlength_correct. lia. Qed.

Lemma Zlen_app : forall (a b: list Z), Zlength (a ++ b) = Zlength a + Zlength b.
Proof. intros. rewrite !Zlength_correct, length_app. lia. Qed.

Lemma fields_L_app : forall a c, fields_L (a ++ c) = fields_L a + fields_L c.
Proof. intros. rewrite !fields_L_wsum, wsum_app. lia. Qed.

Lemma fields_L_cons : forall x c, fields_L (x :: c) = snd x + fields_L c.
Proof. intros. rewrite !fields_L_wsum, wsum_cons. lia. Qed.

Lemma fields_L_prefix : forall fs a c, fs = a ++ c -> fields_ok fs -> 0 <= fields_L a <= fields_L fs.
Proof.
  intros fs a c E Hok. rewrite E in Hok. apply Forall_app in Hok as [Ha Hc].
  subst fs. rewrite fields_L_app, !fields_L_wsum.
  pose proof (wsum_nonneg _ Ha). pose proof (wsum_nonneg _ Hc). lia.
Qed.

Lemma repeat_split : forall (x: Z * Z) i k, (i < k)%nat -> repeat x k = repeat x i ++ x :: repeat x (k - i - 1).
Proof.
  intros x i k H. replace k with (i + S (k - i - 1))%nat at 1 by lia.
  rewrite repeat_app. reflexivity.
Qed.

Lemma app_L1 : forall {A} (pre: list A) x R r Y, pre ++ x :: R ++ [r] ++ Y = (pre ++ x :: R ++ [r]) ++ Y.
Proof. intros. induction pre as [|a pre IH]; simpl; [rewrite <- app_assoc; reflexivity | f_equal; exact IH]. Qed.

Lemma app_L2 : forall {A} (pre: list A) x a c b r Y,
  (pre ++ x :: (a ++ c :: b) ++ [r]) ++ Y = (pre ++ x :: a) ++ c :: (b ++ [r] ++ Y).
Proof.
  intros. induction pre as [|u pre IH]; simpl; [|f_equal; exact IH].
  f_equal. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma app_L3 : forall {A} (pre: list A) x R r Y, (pre ++ x :: R ++ [r]) ++ Y = (pre ++ x :: R) ++ r :: Y.
Proof.
  intros. induction pre as [|u pre IH]; simpl; [|f_equal; exact IH].
  f_equal. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma ncount_zeros_ok : forall b k r fuel p,
  (k < fuel)%nat -> (forall i, (i < k)%nat -> fbits b (p + 2 * Z.of_nat i) 2 = 3) ->
  fbits b (p + 2 * Z.of_nat k) 2 = r -> r <> 3 ->
  ncount_zeros fuel b p = (3 * Z.of_nat k + r, p + 2 * Z.of_nat k + 2).
Proof.
  induction k as [|k IH]; intros r fuel p Hf Hi Hr H3; destruct fuel as [|fuel]; try lia; cbn [ncount_zeros].
  - replace (p + 2 * Z.of_nat 0) with p in Hr by lia. rewrite Hr.
    destruct (r =? 3) eqn:E; [apply Z.eqb_eq in E; lia|]. f_equal; lia.
  - assert (H0: fbits b p 2 = 3).
    { specialize (Hi 0%nat ltac:(lia)). replace (p + 2 * Z.of_nat 0) with p in Hi by lia. exact Hi. }
    rewrite H0, Z.eqb_refl.
    rewrite (IH r fuel (p + 2)).
    + cbv beta iota. f_equal; lia.
    + lia.
    + intros i Hi'. replace (p + 2 + 2 * Z.of_nat i) with (p + 2 * Z.of_nat (S i)) by lia. apply Hi. lia.
    + replace (p + 2 + 2 * Z.of_nat k) with (p + 2 * Z.of_nat (S k)) by lia. exact Hr.
    + exact H3.
Qed.

Local Open Scope bool_scope.

(* the parts of one iteration of ncount_loop: the zero repeats, the reading (rdc), the rest *)
Definition zpart (b: list Z) (maxsv1 p: Z) (prev0: bool) (acc: list Z) : list Z * Z * bool :=
  if prev0 then
    let '(z, p') := ncount_zeros (Z.to_nat (8 * Zlength b + 8)) b p in
    let acc := acc ++ repeat 0 (Z.to_nat z) in
    (acc, p', Zlength acc >=? maxsv1)
  else (acc, p, false).

Definition cont (f: nat) (b: list Z) (maxsv1 p remaining threshold nbBits count: Z) (acc: list Z)
    : option (list Z * Z * Z) :=
  let count := count - 1 in
  let remaining := if count >=? 0 then remaining - count else remaining + count in
  let acc := acc ++ [count] in
  let prev0 := count =? 0 in
  if (remaining <? threshold) && (remaining <=? 1) then Some (acc, remaining, p) else
  let '(nbBits, threshold) :=
    if remaining <? threshold then (highbit remaining + 1, 2 ^ highbit remaining)
    else (nbBits, threshold) in
  if Zlength acc >=? maxsv1 then Some (acc, remaining, p) else
  ncount_loop f b maxsv1 p remaining threshold nbBits prev0 acc.

Lemma ncount_loop_S : forall f b maxsv1 p remaining threshold nbBits prev0 acc,
  ncount_loop (S f) b maxsv1 p remaining threshold nbBits prev0 acc =
  let '(acc, p, stop) := zpart b maxsv1 p prev0 acc in
  if stop then Some (acc, remaining, p) else
  let '(count, p) := rdc b p remaining threshold nbBits in
  cont f b maxsv1 p remaining threshold nbBits count acc.
Proof. reflexivity. Qed.

Definition ncond (l: list Z) (R: Z) : Prop :=
  l <> nil /\ last l 0 <> 0 /\ Forall (fun p => -1 <= p) l /\ zsum (map ncount_of l) = R /\ R <= 512.

Lemma loop_ok : forall fs rest maxsv1, fields_ok fs ->
  forall n fd f todo pre R acc,
  (length todo <= n)%nat -> fs = pre ++ ncount_fields f todo R ->
  (length todo <= f)%nat -> (length todo <= fd)%nat -> ncond todo R ->
  Zlength acc + Zlength todo <= maxsv1 ->
  ncount_loop fd (bpad fs rest) maxsv1 (fields_L pre) (R + 1) (2 ^ highbit (R + 1)) (highbit (R + 1) + 1) false acc
    = Some (acc ++ todo, 1, fields_L fs).
Proof.
  intros fs rest maxsv1 Hok.
  induction n as [|n IH]; intros fd f todo pre R acc Hn E Hf Hfd Hc Hm.
  { destruct todo; [destruct Hc as [Hc _]; congruence | simpl in Hn; lia]. }
  assert (NZ: forall fd f q rest' pre R acc, (length rest' <= n)%nat -> q <> 0 ->
     fs = pre ++ ncount_field q R :: ncount_fields f rest' (R - ncount_of q) ->
     (length rest' <= f)%nat -> (length rest' <= fd)%nat -> ncond (q :: rest') R ->
     Zlength acc + Zlength (q :: rest') <= maxsv1 ->
     cont fd (bpad fs rest) maxsv1 (fields_L pre + snd (ncount_field q R)) (R + 1) (2 ^ highbit (R + 1))
       (highbit (R + 1) + 1) (q + 1) acc = Some (acc ++ q :: rest', 1, fields_L fs)).
  { intros fd' f' q rest' pre' R' acc' Hn' Hq E' Hf' Hfd' Hc' Hm'.
    destruct Hc' as (_ & Hlast & Hge & Hsum & HR).
    pose proof (Forall_inv Hge) as Hq1. pose proof (Forall_inv_tail Hge) as Hge'.
    pose proof (ncount_of_facts q Hq1) as Hcq. pose proof (zsum_nonneg rest' Hge') as Hs'.
    change (zsum (map ncount_of (q :: rest'))) with (ncount_of q + zsum (map ncount_of rest')) in Hsum.
    assert (HR1: 1 <= R') by lia.
    destruct (hb_bounds R' ltac:(lia)) as [Hb Hh].
    unfold cont. cbv zeta.
    replace (q + 1 - 1) with q by lia.
    assert (Erem: (if q >=? 0 then R' + 1 - q else R' + 1 + q) = (R' - ncount_of q) + 1).
    { destruct (q >=? 0) eqn:Eg; [apply Z.geb_le in Eg | rewrite Z.geb_leb, Z.leb_gt in Eg]; lia. }
    rewrite Erem.
    set (R2 := R' - ncount_of q) in *.
    destruct rest' as [|q2 rest2].
    - change (zsum (map ncount_of [])) with 0 in Hsum.
      assert (H2: 2 ^ 1 <= 2 ^ highbit (R' + 1)) by (apply Z.pow_le_mono_r; lia).
      change (2 ^ 1) with 2 in H2.
      replace (R2 + 1 <? 2 ^ highbit (R' + 1)) with true by (symmetry; apply Z.ltb_lt; lia).
      replace (R2 + 1 <=? 1) with true by (symmetry; apply Z.leb_le; lia).
      cbv beta iota delta [andb].
      replace (R2 + 1) with 1 by lia. f_equal. f_equal.
      rewrite E'. destruct f'; cbn [ncount_fields]; rewrite fields_L_app, fields_L_cons;
        change (fields_L []) with 0; lia.
    - assert (H1: 1 <= zsum (map ncount_of (q2 :: rest2))).
      { apply zsum_pos; [congruence | rewrite last_cons_cons in Hlast; auto | auto]. }
      replace ((R2 + 1 <? 2 ^ highbit (R' + 1)) && (R2 + 1 <=? 1)) with false
        by (rewrite (proj2 (Z.leb_gt _ _)) by lia; destruct (_ <? _); reflexivity).
      cbv beta iota.
      replace (Zlength (acc' ++ [q]) >=? maxsv1) with false.
      2:{ symmetry. rewrite Z.geb_leb. apply Z.leb_gt. rewrite Zlen_app. rewrite !Zlength_cons in Hm'.
          change (Zlength [q]) with 1. pose proof (Zlen_nn rest2). lia. }
      rewrite (proj2 (Z.eqb_neq q 0) Hq).
      assert (Hpre: fields_L pre' + snd (ncount_field q R') = fields_L (pre' ++ [ncount_field q R']))
        by (rewrite fields_L_app, fields_L_cons; change (fields_L []) with 0; lia).
      rewrite Hpre.
      replace (acc' ++ q :: q2 :: rest2) with ((acc' ++ [q]) ++ q2 :: rest2) by (rewrite <- app_assoc; reflexivity).
      assert (HIH: ncount_loop fd' (bpad fs rest) maxsv1 (fields_L (pre' ++ [ncount_field q R'])) (R2 + 1)
                     (2 ^ highbit (R2 + 1)) (highbit (R2 + 1) + 1) false (acc' ++ [q]) =
                   Some ((acc' ++ [q]) ++ q2 :: rest2, 1, fields_L fs)).
      { apply (IH fd' f' (q2 :: rest2) (pre' ++ [ncount_field q R']) R2 (acc' ++ [q])).
        - simpl in Hn' |- *; lia.
        - rewrite E', <- app_assoc. reflexivity.
        - lia.
        - lia.
        - split; [congruence|]. split; [rewrite last_cons_cons in Hlast; auto|]. split; [auto|].
          split; [unfold R2; lia | unfold R2; lia].
        - rewrite Zlen_app. rewrite !Zlength_cons in Hm' |- *. change (Zlength (@nil Z)) with 0. lia. }
      destruct (R2 + 1 <? 2 ^ highbit (R' + 1)) eqn:Et; cbv beta iota.
      + exact HIH.
      + assert (Hhb: highbit (R2 + 1) = highbit (R' + 1)) by (apply hb_same; [lia | apply Z.ltb_ge in Et; lia]).
        rewrite <- Hhb. exact HIH. }
  destruct todo as [|q rest']; [destruct Hc as [Hc _]; congruence|].
  destruct f as [|f']; [simpl in Hf; lia|]. destruct fd as [|fd']; [simpl in Hfd; lia|].
  destruct Hc as (Hne & Hlast & Hge & Hsum & HR).
  pose proof (Forall_inv Hge) as Hq1. pose proof (Forall_inv_tail Hge) as Hge'.
  pose proof (ncount_of_facts q Hq1) as Hc. pose proof (zsum_nonneg rest' Hge') as Hs'.
  assert (HR1: 1 <= R) by (rewrite <- Hsum; apply zsum_pos; auto).
  assert (Hsum': ncount_of q + zsum (map ncount_of rest') = R) by (rewrite <- Hsum; reflexivity).
  rewrite ncount_loop_S. cbn [zpart].
  cbn [ncount_fields] in E.
  destruct (q =? 0) eqn:Eq; cbv beta iota in E.
  - apply Z.eqb_eq in Eq. subst q.
    replace (R - ncount_of 0) with R in E by (change (ncount_of 0) with 0; lia).
    rewrite (rdc_ok fs rest pre 0 R _ E Hok ltac:(lia) ltac:(lia)).
    cbv beta iota. unfold cont. cbv zeta.
    replace (0 + 1 - 1) with 0 by lia.
    change (0 >=? 0) with true. change (0 =? 0) with true. cbv beta iota.
    replace (R + 1 - 0) with (R + 1) by lia.
    destruct (hb_bounds R ltac:(lia)) as [Hb Hh].
    replace (R + 1 <? 2 ^ highbit (R + 1)) with false by (symmetry; apply Z.ltb_ge; lia).
    cbv beta iota delta [andb].
    assert (Hne': rest' <> nil) by (intro; subst; simpl in Hlast; congruence).
    assert (Hlast': last rest' 0 <> 0)
      by (destruct rest' as [|y r]; [congruence | rewrite last_cons_cons in Hlast; exact Hlast]).
    destruct (zrun_split rest' Hne' Hlast') as (q2 & l2 & El & Hq2 & Es).
    set (z := zrun rest') in *.
    assert (Hlen2: length rest' = (z + S (length l2))%nat)
      by (rewrite El at 1; rewrite length_app, repeat_length; reflexivity).
    assert (HZ2: Zlength rest' = Z.of_nat z + 1 + Zlength l2)
      by (rewrite !Zlength_correct, Hlen2; lia).
    rewrite Zlength_cons in Hm.
    replace (Zlength (acc ++ [0]) >=? maxsv1) with false.
    2:{ symmetry. rewrite Z.geb_leb. apply Z.leb_gt. rewrite Zlen_app. change (Zlength [0]) with 1.
        pose proof (Zlen_nn l2). lia. }
    cbv beta iota.
    rewrite Es in E.
    destruct f' as [|f'']; [simpl in Hf; lia|].
    cbn [ncount_fields] in E. rewrite (proj2 (Z.eqb_neq q2 0) Hq2) in E. cbv beta iota in E.
    destruct fd' as [|fd'']; [simpl in Hfd; lia|].
    rewrite ncount_loop_S. unfold zpart.
    set (k := (z / 3)%nat) in *. set (r := Z.of_nat (z mod 3)) in *.
    set (P1 := fields_L pre + snd (ncount_field 0 R)).
    assert (Hr3: 0 <= r < 3) by (unfold r; pose proof (Nat.mod_upper_bound z 3 ltac:(lia)); lia).
    set (pre2 := pre ++ ncount_field 0 R :: repeat (3, 2) k ++ [(r, 2)]).
    assert (E2: fs = pre2 ++ ncount_field q2 R :: ncount_fields f'' l2 (R - ncount_of q2)).
    { rewrite E. unfold pre2. apply app_L1. }
    assert (HP2: fields_L pre2 = P1 + 2 * Z.of_nat k + 2).
    { unfold pre2, P1. rewrite fields_L_app, fields_L_cons, fields_L_app, !fields_L_wsum, wsum_repeat, wsum_cons.
      cbn [snd wsum]. lia. }
    assert (Hz: ncount_zeros (Z.to_nat (8 * Zlength (bpad fs rest) + 8)) (bpad fs rest) P1 =
                (3 * Z.of_nat k + r, P1 + 2 * Z.of_nat k + 2)).
    { destruct (bpad_facts fs rest Hok) as (HL & _ & _ & _ & Hlenb).
      destruct (fields_L_prefix fs pre2 _ E2 Hok) as [HP0 HPL].
      assert (HP1: 0 <= P1) by (unfold P1; rewrite fields_L_wsum; pose proof (fields_L_prefix fs pre _ E Hok); 
        rewrite fields_L_wsum in *; destruct (ncount_field_ok 0 R) as [A1 _]; lia).
      apply ncount_zeros_ok.
      - assert (fields_L fs <= 8 * Zlength (bpad fs rest)) by (pose proof (Z.div_mod (fields_L fs + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (fields_L fs + 7) 8 ltac:(lia)); lia). lia.
      - intros i Hi.
        assert (Ei: fs = (pre ++ ncount_field 0 R :: repeat (3, 2) i) ++ (3, 2) ::
                   (repeat (3, 2) (k - i - 1) ++ [(r, 2)] ++ ncount_field q2 R :: ncount_fields f'' l2 (R - ncount_of q2))).
        { rewrite E2. unfold pre2. rewrite (repeat_split (3, 2) i k Hi). apply app_L2. }
        assert (HPi: fields_L (pre ++ ncount_field 0 R :: repeat (3, 2) i) = P1 + 2 * Z.of_nat i).
        { unfold P1. rewrite fields_L_app, fields_L_cons, !fields_L_wsum, wsum_repeat. cbn [snd]. lia. }
        rewrite <- HPi. rewrite (read_field fs rest _ 3 2 _ 2 Ei Hok) by lia. reflexivity.
      - assert (Ek: fs = (pre ++ ncount_field 0 R :: repeat (3, 2) k) ++ (r, 2) ::
                   (ncount_field q2 R :: ncount_fields f'' l2 (R - ncount_of q2))).
        { rewrite E2. unfold pre2. apply app_L3. }
        assert (HPk: fields_L (pre ++ ncount_field 0 R :: repeat (3, 2) k) = P1 + 2 * Z.of_nat k).
        { unfold P1. rewrite fields_L_app, fields_L_cons, !fields_L_wsum, wsum_repeat. cbn [snd]. lia. }
        rewrite <- HPk. rewrite (read_field fs rest _ r 2 _ 2 Ek Hok) by lia.
        apply Z.mod_small. change (2 ^ 2) with 4. lia.
      - lia. }
    rewrite Hz. cbv beta iota.
    assert (Hzk: Z.to_nat (3 * Z.of_nat k + r) = z).
    { unfold k, r. pose proof (Nat.div_mod_eq z 3). lia. }
    rewrite Hzk.
    replace (Zlength ((acc ++ [0]) ++ repeat 0 z) >=? maxsv1) with false.
    2:{ symmetry. rewrite Z.geb_leb. apply Z.leb_gt. rewrite !Zlen_app. change (Zlength [0]) with 1.
        rewrite (Zlength_correct (repeat 0 z)), repeat_length. pose proof (Zlen_nn l2). lia. }
    cbv beta iota.
    rewrite <- HP2.
    assert (Hsum2: zsum (map ncount_of (q2 :: l2)) = R).
    { rewrite <- Hsum', El, map_app, zsum_app, zsum_repeat0. change (ncount_of 0) with 0. lia. }
    assert (Hge2: Forall (fun p => -1 <= p) (q2 :: l2)) by (rewrite El in Hge'; apply Forall_app in Hge'; tauto).
    assert (Hq2b: -1 <= q2 <= R).
    { pose proof (Forall_inv Hge2) as Hq21. pose proof (ncount_of_facts q2 Hq21).
      pose proof (zsum_nonneg l2 (Forall_inv_tail Hge2)).
      change (zsum (map ncount_of (q2 :: l2))) with (ncount_of q2 + zsum (map ncount_of l2)) in Hsum2. lia. }
    rewrite (rdc_ok fs rest pre2 q2 R _ E2 Hok ltac:(lia) Hq2b). cbv beta iota.
    replace (acc ++ 0 :: rest') with (((acc ++ [0]) ++ repeat 0 z) ++ q2 :: l2)
      by (rewrite El; rewrite <- !app_assoc; reflexivity).
    apply (NZ fd'' f'' q2 l2 pre2 R ((acc ++ [0]) ++ repeat 0 z)).
    + simpl in Hn. lia.
    + exact Hq2.
    + exact E2.
    + simpl in Hf. lia.
    + simpl in Hfd. lia.
    + split; [congruence|]. split; [rewrite El, last_app_cons in Hlast'; auto|]. split; [auto|]. split; [auto | lia].
    + rewrite !Zlen_app. change (Zlength [0]) with 1.
      rewrite Zlength_cons, (Zlength_correct (repeat 0 z)), repeat_length. lia.
  - apply Z.eqb_neq in Eq.
    rewrite (rdc_ok fs rest pre q R _ E Hok ltac:(lia) ltac:(lia)). cbv beta iota.
    apply (NZ fd' f' q rest' pre R acc); auto; try (simpl in *; lia).
    repeat split; auto.
Qed.

(* ---------------------------------------------------------------------------------------------- *)

Lemma ndist_ncond : forall log norm, ndist_ok log norm -> ncond norm (2 ^ log) /\ 2 ^ log <= 512.
Proof.
  intros log norm (Hlog & Hlen & Hb & Hs & H2 & Hl).
  assert (2 ^ log <= 2 ^ 9) by (apply Z.pow_le_mono_r; lia).
  change (2 ^ 9) with 512 in *.
  split; [|lia]. split; [intro; subst; change (Zlength (@nil Z)) with 0 in Hlen; lia|]. split; [auto|].
  split; [|split; [auto | lia]]. eapply Forall_impl; [|exact Hb]. intros a Ha; simpl in Ha; lia.
Qed.

Lemma desc_L : forall norm log, ndist_ok log norm ->
  fields_ok (fse_desc_fields norm log) /\ 4 <= fields_L (fse_desc_fields norm log) <= 512.
Proof.
  intros norm log Hd. destruct (ndist_ncond log norm Hd) as [(Hne & Hl & Hf & Hs & HR) HR'].
  destruct Hd as (Hlog & Hlen & _).
  destruct (nf_props (length norm) norm (2 ^ log) ltac:(lia) (or_intror Hl) Hf Hs HR) as (Hok & Hb & _).
  assert (HA: Atab (2 ^ log) <= 16).
  { assert (log = 5 \/ log = 6 \/ log = 7 \/ log = 8 \/ log = 9) as Hc by lia.
    destruct Hc as [-> | [-> | [-> | [-> | ->]]]]; vm_compute; congruence. }
  unfold fse_desc_fields. split.
  - constructor; auto. cbn [fst snd]. change (2 ^ 4) with 16. lia.
  - rewrite fields_L_wsum, wsum_cons. cbn [snd]. pose proof (wsum_nonneg _ Hok). lia.
Qed.

Lemma fse_desc_fields_ok : forall norm log, ndist_ok log norm -> fields_ok (fse_desc_fields norm log).
Proof.
  intros. apply desc_L. auto.
Qed.

Lemma fse_desc_bytes_ok : forall norm log, ndist_ok log norm ->
  bytes_ok (fse_desc_bytes norm log) /\ 1 <= Zlength (fse_desc_bytes norm log) <= 64.
Proof.
  intros norm log Hd. destruct (desc_L norm log Hd) as [Hok HL].
  destruct (bpad_facts _ [] Hok) as (_ & _ & Hb & Hl & _).
  unfold fse_desc_bytes, fields_pad. split; auto. rewrite Hl.
  assert ((fields_L (fse_desc_fields norm log) + 7) / 8 < 65) by (apply Z.div_lt_upper_bound; lia).
  split; [apply Z.div_le_lower_bound; lia | lia].
Qed.

Theorem fse_desc_read : forall norm log maxsv rest,
  ndist_ok log norm -> Zlength norm <= maxsv + 1 -> maxsv <= 255 ->
  read_ncount (fse_desc_bytes norm log ++ rest) maxsv = Some (norm, log, Zlength (fse_desc_bytes norm log)).
Proof.
  intros norm log maxsv rest Hd Hn Hm.
  destruct (desc_L norm log Hd) as [Hok HL].
  destruct (ndist_ncond log norm Hd) as [Hc HR].
  assert (Hlog: 5 <= log <= 9) by apply Hd.
  assert (Hlen: 1 <= Zlength norm) by apply Hd.
  set (fs := fse_desc_fields norm log) in *.
  assert (Eb: fse_desc_bytes norm log ++ rest = bpad fs rest) by reflexivity.
  assert (Eb2: fse_desc_bytes norm log = bw_pad (fields_W fs) (fields_L fs)) by reflexivity.
  rewrite Eb, Eb2.
  destruct (bpad_facts fs rest Hok) as (HL0 & HW & Hbo & Hl & Hl2).
  rewrite Hl.
  assert (H18: 1 <= (fields_L fs + 7) / 8) by (apply Z.div_le_lower_bound; lia).
  unfold read_ncount.
  replace (Zlength (bpad fs rest) =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  pose proof (read_field fs rest [] (log - 5) 4 (ncount_fields (length norm) norm (2 ^ log)) 4 eq_refl Hok
                ltac:(lia)) as H4.
  change (fields_L []) with 0 in H4. rewrite H4.
  rewrite Z.mod_small by (change (2 ^ 4) with 16; lia).
  replace (log - 5 + FSE_MIN_TABLELOG) with log by (unfold FSE_MIN_TABLELOG; lia).
  destruct (log >? FSE_TABLELOG_ABSOLUTE_MAX) eqn:Eg.
  { unfold FSE_TABLELOG_ABSOLUTE_MAX in Eg. rewrite Z.gtb_ltb, Z.ltb_lt in Eg. lia. }
  assert (Hhb: highbit (2 ^ log + 1) = log).
  { unfold highbit. apply Z.log2_unique; [lia|]. rewrite Z.pow_succ_r by lia.
    assert (2 ^ 1 <= 2 ^ log) by (apply Z.pow_le_mono_r; lia). change (2 ^ 1) with 2 in *. lia. }
  pose proof (loop_ok fs rest (maxsv + 1) Hok (length norm) (Z.to_nat (maxsv + 2)) (length norm) norm
                [(log - 5, 4)] (2 ^ log) []) as HH.
  rewrite Hhb in HH. change (fields_L [(log - 5, 4)]) with 4 in HH.
  rewrite HH; [| auto | reflexivity | auto | rewrite Zlength_correct in Hn; lia | auto
               | change (Zlength (@nil Z)) with 0; lia].
  cbv beta iota zeta. change (negb (1 =? 1)) with false. change (@nil Z ++ norm) with norm. cbv beta iota.
  destruct (Zlength norm >? maxsv + 1) eqn:E1; [rewrite Z.gtb_ltb, Z.ltb_lt in E1; lia|].
  destruct ((fields_L fs + 7) / 8 >? Zlength (bpad fs rest)) eqn:E2; [rewrite Z.gtb_ltb, Z.ltb_lt in E2; lia|].
  reflexivity.
Qed.

(* every lemma above together (fse_desc_fields_ok, fse_desc_bytes_ok, fse_desc_read) *)
Theorem wm_ncount_all :
  (forall norm log, ndist_ok log norm -> fields_ok (fse_desc_fields norm log)) /\
  (forall norm log, ndist_ok log norm -> bytes_ok (fse_desc_bytes norm log) /\ 1 <= Zlength (fse_desc_bytes norm log) <= 64) /\
  (forall norm log maxsv rest, ndist_ok log norm -> Zlength norm <= maxsv + 1 -> maxsv <= 255 -> read_ncount (fse_desc_bytes norm log ++ rest) maxsv = Some (norm, log, Zlength (fse_desc_bytes norm log))).
Proof.
  split; [exact fse_desc_fields_ok | split; [exact fse_desc_bytes_ok | exact fse_desc_read]].
Qed.
