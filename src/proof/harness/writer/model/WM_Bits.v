(* The bit writer against the format model's readers (plain Coq):
   forward streams (NCount.fbits) and backward streams (Bitstream/BitsFast). *)
Require Import Zstd.proof.harness.writer.model.WModel.

(* ---- helpers (arithmetic on powers of 2 and little-endian bytes) ---- *)

Lemma wmb_pow_pos : forall a, 0 <= a -> 0 < 2 ^ a.
Proof. intros; apply Z.pow_pos_nonneg; lia. Qed.

(* bits [r, r+n) of A + 2^M X are those of A when r + n <= M *)
Lemma wmb_div_mod_add : forall A X r n M, 0 <= r -> 0 <= n -> r + n <= M ->
  (A + 2 ^ M * X) / 2 ^ r mod 2 ^ n = A / 2 ^ r mod 2 ^ n.
Proof.
  intros A X r n M Hr Hn HM.
  assert (E1: 2 ^ M = 2 ^ (M - r) * 2 ^ r) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (E2: 2 ^ (M - r) = 2 ^ (M - r - n) * 2 ^ n) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  replace (2 ^ M * X) with ((2 ^ (M - r) * X) * 2 ^ r) by (rewrite E1; ring).
  rewrite Z.div_add by (pose proof (wmb_pow_pos r Hr); lia).
  replace (2 ^ (M - r) * X) with ((2 ^ (M - r - n) * X) * 2 ^ n) by (rewrite E2; ring).
  rewrite Z.mod_add by (pose proof (wmb_pow_pos n Hn); lia). reflexivity.
Qed.

Lemma wmb_mod_div_mod : forall x r n M, 0 <= r -> 0 <= n -> r + n <= M ->
  (x mod 2 ^ M) / 2 ^ r mod 2 ^ n = x / 2 ^ r mod 2 ^ n.
Proof.
  intros x r n M Hr Hn HM.
  assert (0 < 2 ^ M) by (apply wmb_pow_pos; lia).
  rewrite (Z.div_mod x (2 ^ M)) at 2 by lia.
  rewrite Z.add_comm, wmb_div_mod_add by lia. reflexivity.
Qed.

Lemma wmb_le_value_app : forall l1 l2,
  le_value (l1 ++ l2) = le_value l1 + 2 ^ (8 * Z.of_nat (length l1)) * le_value l2.
Proof.
  induction l1; intros; cbn [app le_value length].
  - rewrite Z.mul_1_l, Z.add_0_l. reflexivity.
  - rewrite IHl1. rewrite Nat2Z.inj_succ.
    replace (8 * Z.succ (Z.of_nat (length l1))) with (8 + 8 * Z.of_nat (length l1)) by lia.
    rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256. ring.
Qed.

Lemma wmb_le_value_le_bytes : forall k v, le_value (le_bytes k v) = v mod 2 ^ (8 * Z.of_nat k).
Proof.
  induction k; intros; cbn [le_bytes le_value].
  - simpl. rewrite Z.mod_1_r. reflexivity.
  - rewrite IHk. rewrite Nat2Z.inj_succ.
    replace (8 * Z.succ (Z.of_nat k)) with (8 + 8 * Z.of_nat k) by lia.
    rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256.
    rewrite Z.rem_mul_r; [lia | lia |]. apply wmb_pow_pos; lia.
Qed.

Lemma wmb_le_bytes_ok : forall k v, bytes_ok (le_bytes k v).
Proof.
  induction k; intros; cbn [le_bytes].
  - constructor.
  - constructor; [unfold is_byte; apply Z.mod_pos_bound; lia | apply IHk].
Qed.

Lemma wmb_length_le_bytes : forall k v, length (le_bytes k v) = k.
Proof. induction k; intros; simpl; auto. Qed.

Lemma wmb_skipn_le_bytes : forall i k v, (i <= k)%nat ->
  skipn i (le_bytes k v) = le_bytes (k - i) (v / 2 ^ (8 * Z.of_nat i)).
Proof.
  induction i; intros k v Hi.
  - simpl. rewrite Z.div_1_r, Nat.sub_0_r. reflexivity.
  - destruct k; [lia |]. simpl skipn. simpl Nat.sub. rewrite IHi by lia.
    f_equal. rewrite Z.div_div by (try lia; apply wmb_pow_pos; lia).
    f_equal. rewrite Nat2Z.inj_succ.
    replace (8 * Z.succ (Z.of_nat i)) with (8 + 8 * Z.of_nat i) by lia.
    rewrite Z.pow_add_r by lia. reflexivity.
Qed.

Lemma wmb_firstn_le_bytes : forall j k v rest,
  firstn j (le_bytes k v ++ rest) = le_bytes (Nat.min j k) v ++ firstn (j - k) rest.
Proof.
  induction j; intros k v rest.
  - simpl. reflexivity.
  - destruct k; simpl; [reflexivity |]. rewrite IHj. reflexivity.
Qed.

(* the window of 5 bytes at byte p/8 of a little-endian encoding (and whatever follows it) *)
Lemma wmb_window : forall K Y rest p n, 0 <= p -> 0 <= n <= 32 -> p + n <= 8 * Z.of_nat K ->
  (le_value (slice (le_bytes K Y ++ rest) (p / 8) 5) / 2 ^ (p mod 8)) mod 2 ^ n = (Y / 2 ^ p) mod 2 ^ n.
Proof.
  intros K Y rest p n Hp Hn HK.
  assert (Hq: 0 <= p / 8 <= Z.of_nat K) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
  pose proof (Z.mod_pos_bound p 8 ltac:(lia)) as Hr.
  pose proof (Z.div_mod p 8 ltac:(lia)) as Hpd.
  unfold slice. rewrite skipn_app.
  rewrite wmb_skipn_le_bytes by lia. rewrite wmb_length_le_bytes.
  replace (Z.to_nat (p / 8) - K)%nat with O by lia. simpl skipn.
  rewrite wmb_firstn_le_bytes. rewrite wmb_le_value_app. rewrite wmb_le_value_le_bytes.
  rewrite wmb_length_le_bytes.
  rewrite wmb_div_mod_add by lia.
  rewrite wmb_mod_div_mod by lia.
  rewrite Z.div_div by (try lia; apply wmb_pow_pos; lia).
  rewrite <- Z.pow_add_r by lia. rewrite Z2Nat.id by lia.
  replace (8 * (p / 8) + p mod 8) with p by lia. reflexivity.
Qed.

Lemma wmb_last_le_bytes : forall k v, last (le_bytes (S k) v) 0 = (v / 2 ^ (8 * Z.of_nat k)) mod 256.
Proof.
  induction k; intros v.
  - simpl. rewrite Z.div_1_r. reflexivity.
  - change (le_bytes (S (S k)) v) with ((v mod 256) :: le_bytes (S k) (v / 256)).
    change (last ((v mod 256) :: le_bytes (S k) (v / 256)) 0) with (last (le_bytes (S k) (v / 256)) 0).
    rewrite IHk. rewrite Z.div_div by (try lia; apply wmb_pow_pos; lia).
    f_equal. f_equal. rewrite Nat2Z.inj_succ.
    replace (8 * Z.succ (Z.of_nat k)) with (8 + 8 * Z.of_nat k) by lia.
    rewrite Z.pow_add_r by lia. reflexivity.
Qed.

Lemma wmb_fields_wl_shift : forall fs W L, fields_ok fs -> 0 <= L ->
  fst (fields_wl fs W L) = W + 2 ^ L * fst (fields_wl fs 0 0) /\
  snd (fields_wl fs W L) = L + snd (fields_wl fs 0 0).
Proof.
  induction fs as [| [v nb] fs IH]; intros W L Hok HL; simpl.
  - lia.
  - inversion Hok as [| ? ? [Hnb Hv] Hok']; subst; simpl in *.
    destruct (IH (W + v * 2 ^ L) (L + nb) Hok' ltac:(lia)) as [H1 H2].
    destruct (IH (v * 1) nb Hok' ltac:(lia)) as [H3 H4].
    rewrite H1, H2, H3, H4. rewrite Z.pow_add_r by lia. split; ring.
Qed.

Lemma fields_wl_app : forall a b W L,
  fields_wl (a ++ b) W L = fields_wl b (fst (fields_wl a W L)) (snd (fields_wl a W L)).
Proof.
  induction a as [| [v nb] a IH]; intros; simpl; auto.
Qed.

(* the value stays below 2^L *)
Lemma fields_wl_range : forall fs W L,
  fields_ok fs -> 0 <= L -> 0 <= W < 2 ^ L ->
  L <= snd (fields_wl fs W L) /\ 0 <= fst (fields_wl fs W L) < 2 ^ snd (fields_wl fs W L).
Proof.
  induction fs as [| [v nb] fs IH]; intros W L Hok HL HW; simpl.
  - lia.
  - inversion Hok as [| ? ? [Hnb Hv] Hok']; subst; simpl in *.
    assert (E: 2 ^ (L + nb) = 2 ^ L * 2 ^ nb) by (apply Z.pow_add_r; lia).
    assert (0 < 2 ^ L) by (apply wmb_pow_pos; lia).
    destruct (IH (W + v * 2 ^ L) (L + nb) Hok' ltac:(lia)) as [H1 H2].
    + rewrite E. split; [nia |].
      assert (v * 2 ^ L <= (2 ^ nb - 1) * 2 ^ L) by (apply Z.mul_le_mono_nonneg_r; lia). nia.
    + split; lia.
Qed.

(* a field of the written bits *)
Lemma fields_field : forall pre v nb post,
  fields_ok (pre ++ (v, nb) :: post) ->
  (fields_W (pre ++ (v, nb) :: post) / 2 ^ fields_L pre) mod 2 ^ nb = v.
Proof.
  intros pre v nb post Hok.
  assert (Hpre: fields_ok pre) by (apply Forall_app in Hok; tauto).
  assert (Hrest: fields_ok ((v, nb) :: post)) by (apply Forall_app in Hok; tauto).
  inversion Hrest as [| ? ? [Hnb Hv] Hpost]; subst; simpl in *.
  destruct (fields_wl_range pre 0 0 Hpre ltac:(lia) ltac:(simpl; lia)) as [HL0 HW0].
  unfold fields_W, fields_L. rewrite fields_wl_app.
  set (W0 := fst (fields_wl pre 0 0)) in *. set (L0 := snd (fields_wl pre 0 0)) in *.
  simpl. destruct (wmb_fields_wl_shift post (0 + W0 + v * 2 ^ L0) (L0 + nb) Hpost ltac:(lia)) as [H1 _].
  simpl in H1. rewrite H1.
  assert (E: 2 ^ (L0 + nb) = 2 ^ nb * 2 ^ L0) by (rewrite Z.pow_add_r; lia).
  assert (0 < 2 ^ L0) by (apply wmb_pow_pos; lia).
  assert (0 < 2 ^ nb) by (apply wmb_pow_pos; lia).
  replace (W0 + v * 2 ^ L0 + 2 ^ (L0 + nb) * fst (fields_wl post 0 0))
    with (W0 + (v + 2 ^ nb * fst (fields_wl post 0 0)) * 2 ^ L0) by (rewrite E; ring).
  rewrite Z.div_add by lia. rewrite Z.div_small by lia. rewrite Z.add_0_l.
  rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_small; lia.
Qed.

Lemma bw_pad_len : forall W L, 0 <= L -> 0 <= W < 2 ^ L ->
  bytes_ok (bw_pad W L) /\ Zlength (bw_pad W L) = (L + 7) / 8.
Proof.
  intros W L HL HW. unfold bw_pad. split; [apply wmb_le_bytes_ok |].
  rewrite Zlength_correct, wmb_length_le_bytes. apply Z2Nat.id. apply Z.div_pos; lia.
Qed.

Lemma bw_mark_len : forall W L, 0 <= L -> 0 <= W < 2 ^ L ->
  bytes_ok (bw_mark W L) /\ Zlength (bw_mark W L) = L / 8 + 1.
Proof.
  intros W L HL HW. unfold bw_mark. split; [apply wmb_le_bytes_ok |].
  rewrite Zlength_correct, wmb_length_le_bytes. apply Z2Nat.id.
  assert (0 <= L / 8) by (apply Z.div_pos; lia). lia.
Qed.

(* forward: the bits [p, p+n) of a padded stream, whatever follows it *)
Lemma fbits_pad : forall W L p n rest,
  0 <= L -> 0 <= W < 2 ^ L -> 0 <= p -> 0 <= n <= 32 -> p + n <= L ->
  fbits (bw_pad W L ++ rest) p n = (W / 2 ^ p) mod 2 ^ n.
Proof.
  intros W L p n rest HL HW Hp Hn HpL. unfold fbits, bw_pad.
  apply wmb_window; try lia.
  rewrite Z2Nat.id by (apply Z.div_pos; lia).
  pose proof (Z.div_mod (L + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (L + 7) 8 ltac:(lia)). lia.
Qed.

(* backward: a marked stream is a bitstream of L payload bits whose reads are those of W *)
Lemma bw_mark_stream : forall W L,
  0 <= L -> 0 <= W < 2 ^ L ->
  bs_okb (bw_mark W L) = true /\ bs_total (bw_mark W L) = L.
Proof.
  intros W L HL HW. unfold bw_mark.
  assert (Hq: 0 <= L / 8) by (apply Z.div_pos; lia).
  pose proof (Z.div_mod L 8 ltac:(lia)) as HLd. pose proof (Z.mod_pos_bound L 8 ltac:(lia)) as Hr.
  set (q := L / 8) in *. set (r := L mod 8) in *.
  replace (Z.to_nat (q + 1)) with (S (Z.to_nat q)) by lia.
  assert (E: 2 ^ L = 2 ^ r * 2 ^ (8 * q)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (H8: 0 < 2 ^ (8 * q)) by (apply wmb_pow_pos; lia).
  assert (Hr1: 2 ^ r <= 128) by (change 128 with (2 ^ 7); apply Z.pow_le_mono_r; lia).
  assert (HWq: 0 <= W / 2 ^ (8 * q) < 2 ^ r)
    by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  assert (Hlast: last (le_bytes (S (Z.to_nat q)) (W + 2 ^ L)) 0 = W / 2 ^ (8 * q) + 2 ^ r).
  { rewrite wmb_last_le_bytes, Z2Nat.id by lia. rewrite E, Z.div_add by lia.
    apply Z.mod_small. lia. }
  split.
  - unfold bs_okb. rewrite Hlast.
    assert (Hf: forallb (fun b => (0 <=? b) && (b <? 256))%bool (le_bytes (S (Z.to_nat q)) (W + 2 ^ L)) = true).
    { apply forallb_forall. intros x Hx.
      pose proof (wmb_le_bytes_ok (S (Z.to_nat q)) (W + 2 ^ L)) as Hok.
      unfold bytes_ok in Hok. rewrite Forall_forall in Hok. specialize (Hok x Hx). unfold is_byte in Hok.
      apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
    rewrite Hf. replace (W / 2 ^ (8 * q) + 2 ^ r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    reflexivity.
  - unfold bs_total. rewrite Hlast, wmb_length_le_bytes. unfold highbit.
    rewrite (Z.log2_unique (W / 2 ^ (8 * q) + 2 ^ r) r) by (try lia; rewrite Z.pow_succ_r by lia; lia).
    lia.
Qed.

Lemma bs_peek_mark : forall W L pos nb,
  0 <= L -> 0 <= W < 2 ^ L -> 0 <= pos <= L -> 0 <= nb <= 32 ->
  bs_peek_s (bw_mark W L) pos nb = bs_peek W pos nb.
Proof.
  intros W L pos nb HL HW Hpos Hnb. unfold bs_peek_s, bs_peek.
  assert (Hq: 0 <= L / 8) by (apply Z.div_pos; lia).
  pose proof (Z.div_mod L 8 ltac:(lia)) as HLd. pose proof (Z.mod_pos_bound L 8 ltac:(lia)) as Hr.
  assert (HK: L < 8 * Z.of_nat (Z.to_nat (L / 8 + 1))) by (rewrite Z2Nat.id; lia).
  assert (Hp0: 0 < 2 ^ pos) by (apply wmb_pow_pos; lia).
  destruct (Z.ltb_spec pos 0); [lia |].
  unfold bw_mark. rewrite <- (app_nil_r (le_bytes _ (W + 2 ^ L))).
  destruct (Z.geb_spec (pos - nb) 0).
  - rewrite wmb_window by lia.
    replace (W + 2 ^ L) with (W + 2 ^ L * 1) by ring.
    rewrite wmb_div_mod_add by lia.
    assert (E: 2 ^ pos = 2 ^ nb * 2 ^ (pos - nb)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    assert (0 < 2 ^ nb) by (apply wmb_pow_pos; lia).
    assert (0 < 2 ^ (pos - nb)) by (apply wmb_pow_pos; lia).
    rewrite E at 2. rewrite (Z.mul_comm (W mod 2 ^ pos)), Z.div_mul_cancel_l by lia.
    rewrite <- (wmb_mod_div_mod W (pos - nb) nb pos) by lia.
    apply Z.mod_small. split; [apply Z.div_pos; [apply Z.mod_pos_bound|]; lia |].
    apply Z.div_lt_upper_bound; [lia |]. rewrite Z.mul_comm, <- E. apply Z.mod_pos_bound; lia.
  - pose proof (wmb_window (Z.to_nat (L / 8 + 1)) (W + 2 ^ L) nil 0 pos ltac:(lia) ltac:(lia) ltac:(lia)) as Hw.
    change (0 / 8) with 0 in Hw. change (0 mod 8) with 0 in Hw. change (2 ^ 0) with 1 in Hw.
    rewrite !Z.div_1_r in Hw. rewrite Hw.
    replace (W + 2 ^ L) with (W + 2 ^ L * 1) by ring.
    pose proof (wmb_div_mod_add W 1 0 pos L ltac:(lia) ltac:(lia) ltac:(lia)) as Hm.
    change (2 ^ 0) with 1 in Hm. rewrite !Z.div_1_r in Hm. rewrite Hm.
    assert (E: 2 ^ nb = 2 ^ (- (pos - nb)) * 2 ^ pos) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    rewrite E, Z.mul_assoc, Z.div_mul by lia. reflexivity.
Qed.

(* every lemma above together (fields_wl_app, fields_wl_range, fields_field, bw_pad_len, bw_mark_len, fbits_pad, bw_mark_stream, bs_peek_mark) *)
Theorem wm_bits_all :
  (forall a b W L, fields_wl (a ++ b) W L = fields_wl b (fst (fields_wl a W L)) (snd (fields_wl a W L))) /\
  (forall fs W L, fields_ok fs -> 0 <= L -> 0 <= W < 2 ^ L -> L <= snd (fields_wl fs W L) /\ 0 <= fst (fields_wl fs W L) < 2 ^ snd (fields_wl fs W L)) /\
  (forall pre v nb post, fields_ok (pre ++ (v, nb) :: post) -> (fields_W (pre ++ (v, nb) :: post) / 2 ^ fields_L pre) mod 2 ^ nb = v) /\
  (forall W L, 0 <= L -> 0 <= W < 2 ^ L -> bytes_ok (bw_pad W L) /\ Zlength (bw_pad W L) = (L + 7) / 8) /\
  (forall W L, 0 <= L -> 0 <= W < 2 ^ L -> bytes_ok (bw_mark W L) /\ Zlength (bw_mark W L) = L / 8 + 1) /\
  (forall W L p n rest, 0 <= L -> 0 <= W < 2 ^ L -> 0 <= p -> 0 <= n <= 32 -> p + n <= L -> fbits (bw_pad W L ++ rest) p n = (W / 2 ^ p) mod 2 ^ n) /\
  (forall W L, 0 <= L -> 0 <= W < 2 ^ L -> bs_okb (bw_mark W L) = true /\ bs_total (bw_mark W L) = L) /\
  (forall W L pos nb, 0 <= L -> 0 <= W < 2 ^ L -> 0 <= pos <= L -> 0 <= nb <= 32 -> bs_peek_s (bw_mark W L) pos nb = bs_peek W pos nb).
Proof.
  exact (conj fields_wl_app (conj fields_wl_range (conj fields_field (conj bw_pad_len
    (conj bw_mark_len (conj fbits_pad (conj bw_mark_stream bs_peek_mark))))))).
Qed.
