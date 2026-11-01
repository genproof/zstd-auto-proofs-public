(* The body of new_frame (harness/frames.h) satisfies new_frame_spec (FSpecs.v), at any compspecs, in the
   context of the functions it calls (G_new_frame).

   The proof follows the code: the header flags drawn by nondet_u8 and corrected (nf_fcs_flag, nf_did_flag,
   nf_single below) give the header choices h with nh_ok; the header is written into the buffer of 26 + 4 n
   bytes (FNewFrameHeader.v); the block loop keeps the blocks chosen so far, none of them last until the loop
   ends (invariant of forward_while, one iteration in the model: FNewFrameStep.v), Raw blocks copying their
   part of the data, RLE blocks repeating its first byte in the data array; the checksum is the low 4 bytes of
   ZSTD_XXH64 of the data so changed; the frame is copied out (copy_of) and the buffer freed. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zstd.harness.api_split_invariant.code.
Require Import Zstd.proof.zstd.PickLemmas Zstd.proof.harness.HCsConv.
Require Import Zstd.proof.harness.frames.FSpecs Zstd.proof.harness.frames.FLemmas.
Require Import Zstd.proof.harness.frames.FNewFrameFacts Zstd.proof.harness.frames.FNewFrameInts.
Require Import Zstd.proof.harness.frames.FNewFrameHeader Zstd.proof.harness.frames.FNewFrameStep.

(* ---------- CompCert integer arithmetic of the code, as arithmetic on Z ---------- *)

Lemma fk_and_ones : forall b k, 0 <= b <= Int.max_unsigned -> 0 <= k < 32 ->
  Int.and (Int.repr b) (Int.repr (Z.ones k)) = Int.repr (b mod 2 ^ k).
Proof.
  intros b k Hb Hk. unfold Int.and. rewrite !Int.unsigned_repr; [| | rep_lia].
  - rewrite Z.land_ones by lia. reflexivity.
  - rewrite Z.ones_equiv. assert (2 ^ k <= 2 ^ 32) by (apply Z.pow_le_mono_r; lia).
    assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia). rep_lia.
Qed.

Lemma fk_and1 : forall b, 0 <= b <= Int.max_unsigned -> Int.and (Int.repr b) (Int.repr 1) = Int.repr (b mod 2).
Proof. intros. apply (fk_and_ones b 1); lia. Qed.
Lemma fk_and3 : forall b, 0 <= b <= Int.max_unsigned -> Int.and (Int.repr b) (Int.repr 3) = Int.repr (b mod 4).
Proof. intros. apply (fk_and_ones b 2); lia. Qed.

Lemma fk_cmpu64 : forall c a b, 0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int64.cmpu c (Int64.repr a) (Int64.repr b) =
  match c with Ceq => a =? b | Cne => negb (a =? b) | Clt => a <? b | Cle => a <=? b
             | Cgt => b <? a | Cge => b <=? a end.
Proof.
  intros c a b Ha Hb. unfold Int64.cmpu, Int64.ltu, Int64.eq.
  rewrite !Int64.unsigned_repr by lia.
  destruct c; repeat first [destruct (zlt _ _) | destruct (zeq _ _)];
    first [destruct (Z.eqb_spec a b) | destruct (Z.ltb_spec a b) | destruct (Z.leb_spec a b)
          | destruct (Z.ltb_spec b a) | destruct (Z.leb_spec b a)]; simpl; auto; lia.
Qed.

Lemma fk_cmpu32 : forall c a b, 0 <= a <= Int.max_unsigned -> 0 <= b <= Int.max_unsigned ->
  Int.cmpu c (Int.repr a) (Int.repr b) =
  match c with Ceq => a =? b | Cne => negb (a =? b) | Clt => a <? b | Cle => a <=? b
             | Cgt => b <? a | Cge => b <=? a end.
Proof.
  intros c a b Ha Hb. unfold Int.cmpu, Int.ltu, Int.eq.
  rewrite !Int.unsigned_repr by lia.
  destruct c; repeat first [destruct (zlt _ _) | destruct (zeq _ _)];
    first [destruct (Z.eqb_spec a b) | destruct (Z.ltb_spec a b) | destruct (Z.leb_spec a b)
          | destruct (Z.ltb_spec b a) | destruct (Z.leb_spec b a)]; simpl; auto; lia.
Qed.

Lemma fk_ltu64 : forall a b, 0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int64.ltu (Int64.repr a) (Int64.repr b) = (a <? b).
Proof.
  intros a b Ha Hb. unfold Int64.ltu. rewrite !Int64.unsigned_repr by lia.
  destruct (zlt a b); destruct (Z.ltb_spec a b); auto; lia.
Qed.

(* the parity test b & 1 *)
Lemma fk_odd_and1 : forall b, 0 <= b <= Int.max_unsigned ->
  (Int.and (Int.repr b) (Int.repr 1) = Int.zero <-> Z.odd b = false).
Proof.
  intros b Hb. rewrite fk_and1 by lia. rewrite Zmod_odd.
  split; intro E.
  - apply (f_equal Int.unsigned) in E. destruct (Z.odd b); auto.
    rewrite Int.unsigned_repr in E by rep_lia. discriminate.
  - rewrite E. reflexivity.
Qed.

(* new_frame's header flags as computed from its nondet_u8 values: Single_Segment_flag (b the byte drawn),
   Frame_Content_Size_flag (f the 2-bit value drawn, corrected to 3 when fcs does not fit its field),
   Dictionary_ID_flag (g drawn, corrected to 3 when did does not fit) *)
Definition nf_single (b fcs maxw: Z) : bool := (Z.odd b && (fcs <=? maxw))%bool.
Definition nf_fc1 (f: Z) (sg: bool) (fcs: Z) : bool := ((f =? 0) && sg && (255 <? fcs))%bool.
Definition nf_fc2 (f fcs: Z) : bool := ((f =? 1) && ((fcs <? 256) || (65791 <? fcs)))%bool.
Definition nf_fc3 (f fcs: Z) : bool := ((f =? 2) && (4294967295 <? fcs))%bool.
Definition nf_fcs_flag (f: Z) (sg: bool) (fcs: Z) : Z :=
  if (nf_fc1 f sg fcs || nf_fc2 f fcs || nf_fc3 f fcs)%bool then 3 else f.
Definition nf_dc1 (g did: Z) : bool := ((g =? 0) && negb (did =? 0))%bool.
Definition nf_dc2 (g did: Z) : bool := ((g =? 1) && (255 <? did))%bool.
Definition nf_dc3 (g did: Z) : bool := ((g =? 2) && (65535 <? did))%bool.
Definition nf_did_flag (g did: Z) : Z :=
  if (nf_dc1 g did || nf_dc2 g did || nf_dc3 g did)%bool then 3 else g.

(* every case of the integer tests in the goal *)
Ltac fk_zcase :=
  repeat match goal with
  | |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b)
  | |- context [Z.ltb ?a ?b] => destruct (Z.ltb_spec a b)
  | |- context [Z.leb ?a ?b] => destruct (Z.leb_spec a b)
  end; cbn; lia.

(* Window_Size for Single_Segment sg and Window_Descriptor wd (nh_window of FModel.v) *)
Definition nf_win (sg: bool) (fcs wd: Z) : Z :=
  if sg then fcs else 2 ^ (10 + wd / 8) + 2 ^ (10 + wd / 8) / 8 * (wd mod 8).

Lemma nf_single_le : forall b fcs maxw, nf_single b fcs maxw = true -> fcs <= maxw.
Proof. unfold nf_single. intros. apply andb_prop in H as [_ H]. apply Z.leb_le; auto. Qed.

(* the corrected Frame_Content_Size_flag fits fcs (the conditions of nh_ok) *)
Lemma nf_fcs_flag_ok : forall f sg fcs, 0 <= f <= 3 ->
  0 <= nf_fcs_flag f sg fcs <= 3
  /\ (nf_fcs_flag f sg fcs = 0 -> sg = true -> fcs <= 255)
  /\ (nf_fcs_flag f sg fcs = 1 -> 256 <= fcs <= 65791)
  /\ (nf_fcs_flag f sg fcs = 2 -> fcs <= 4294967295).
Proof.
  intros f sg fcs Hf. unfold nf_fcs_flag, nf_fc1, nf_fc2, nf_fc3.
  destruct sg; fk_zcase.
Qed.

(* the corrected Dictionary_ID_flag fits did *)
Lemma nf_did_flag_ok : forall g did, 0 <= g <= 3 -> 0 <= did ->
  0 <= nf_did_flag g did <= 3
  /\ (nf_did_flag g did = 0 -> did = 0)
  /\ (nf_did_flag g did = 1 -> did <= 255)
  /\ (nf_did_flag g did = 2 -> did <= 65535).
Proof.
  intros g did Hg Hd. unfold nf_did_flag, nf_dc1, nf_dc2, nf_dc3.
  fk_zcase.
Qed.

Lemma fk_shr3 : forall b, 0 <= b <= 255 -> Int.shr (Int.repr b) (Int.repr 3) = Int.repr (b / 8).
Proof.
  intros b Hb. unfold Int.shr. rewrite Int.signed_repr by rep_lia.
  rewrite Int.unsigned_repr by rep_lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma fk_shl1 : forall k, 0 <= k < 64 -> Int64.shl (Int64.repr 1) (Int64.repr k) = Int64.repr (2 ^ k).
Proof.
  intros k Hk. unfold Int64.shl. rewrite !Int64.unsigned_repr by rep_lia.
  rewrite Z.shiftl_1_l. reflexivity.
Qed.

(* the exponent 10 + (wd >> 3) of Window_Descriptor wd *)
Lemma fk_wexp : forall b, 0 <= b <= 255 ->
  Int.add (Int.repr 10) (Int.shr (Int.repr b) (Int.repr 3)) = Int.repr (10 + b / 8).
Proof.
  intros b Hb. rewrite fk_shr3 by lia.
  assert (0 <= b / 8 < 32) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  unfold Int.add. rewrite !Int.unsigned_repr by rep_lia. reflexivity.
Qed.

(* Window_Size from Window_Descriptor b as new_frame computes it: base + base / 8 * (b & 7), base = 2^(10 + b/8) *)
Lemma fk_window : forall b fcs, 0 <= b <= 255 ->
  Int64.add (Int64.repr (2 ^ (10 + b / 8)))
    (Int64.mul (Int64.divu (Int64.repr (2 ^ (10 + b / 8))) (Int64.repr 8))
       (Int64.repr (Int.signed (Int.repr (Z.land b 7))))) =
  Int64.repr (nf_win false fcs b).
Proof.
  intros b fcs Hb. unfold nf_win.
  assert (He: 0 <= b / 8 < 32) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  assert (Hp: 0 < 2 ^ (10 + b / 8) <= 2 ^ 41)
    by (split; [apply Z.pow_pos_nonneg | apply Z.pow_le_mono_r]; lia).
  change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
  assert (Hm: 0 <= b mod 8 < 8) by (apply Z.mod_pos_bound; lia).
  set (P := 2 ^ (10 + b / 8)) in *.
  assert (Hq: 0 <= P / 8 <= P) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
  change (2 ^ 41) with 2199023255552 in Hp.
  rewrite Int.signed_repr by rep_lia.
  unfold Int64.add, Int64.mul, Int64.divu. rewrite !Int64.unsigned_repr; try rep_lia.
  all: change (Int64.unsigned (Int64.repr 8)) with 8;
    rewrite ?(Int64.unsigned_repr (P / 8)), ?(Int64.unsigned_repr (b mod 8)) by rep_lia;
    try reflexivity; try rep_lia.
  assert (P / 8 * (b mod 8) <= P * 8) by nia. rep_lia.
Qed.

Lemma nf_win_range : forall sg fcs b, 0 <= fcs <= Int64.max_unsigned -> 0 <= b <= 255 ->
  0 <= nf_win sg fcs b <= Int64.max_unsigned.
Proof.
  intros sg fcs b Hf Hb. unfold nf_win. destruct sg; auto.
  assert (He: 0 <= b / 8 < 32) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  assert (Hp: 0 < 2 ^ (10 + b / 8) <= 2 ^ 41)
    by (split; [apply Z.pow_pos_nonneg | apply Z.pow_le_mono_r]; lia).
  assert (Hm: 0 <= b mod 8 < 8) by (apply Z.mod_pos_bound; lia).
  set (P := 2 ^ (10 + b / 8)) in *.
  assert (Hq: 0 <= P / 8 <= P) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
  change (2 ^ 41) with 2199023255552 in Hp.
  assert (0 <= P / 8 * (b mod 8) <= P * 8) by nia. rep_lia.
Qed.

Lemma fk_zext8 : forall b, 0 <= b <= 255 -> Int.zero_ext 8 (Int.repr b) = Int.repr b.
Proof.
  intros b Hb. apply Int.same_bits_eq. intros i Hi.
  rewrite Int.bits_zero_ext by lia. destruct (zlt i 8); auto.
  rewrite !Int.testbit_repr by lia. symmetry.
  apply (Z.bits_above_log2 b i); [lia |].
  destruct (Z.eq_dec b 0); [subst; simpl; lia |].
  assert (Z.log2 b < 8) by (apply Z.log2_lt_pow2; lia). lia.
Qed.

(* ---------- the byte lists of the frame buffer and of the data array ---------- *)

Lemma fk_mem_written_length : forall (c: list val) i k v, 0 <= i -> 0 <= k -> i + k <= Zlength c ->
  Zlength (Spec_util.mem_written c i k v) = Zlength c.
Proof.
  intros c i k v Hi Hk Hc. unfold Spec_util.mem_written.
  pose proof (Zlength_le_bytes (Z.to_nat k) v) as L. rewrite Z2Nat.id in L by lia.
  rewrite !Zlength_app, Zlength_map, L. rewrite !Zlength_sublist by lia. lia.
Qed.

Lemma fk_add64 : forall a b, Int64.add (Int64.repr a) (Int64.repr b) = Int64.repr (a + b).
Proof.
  intros. rewrite Int64.add_unsigned. apply Int64.eqm_samerepr.
  apply Int64.eqm_add; apply Int64.eqm_sym, Int64.eqm_unsigned_repr.
Qed.

Lemma fk_sub64 : forall a b, Int64.sub (Int64.repr a) (Int64.repr b) = Int64.repr (a - b).
Proof.
  intros. unfold Int64.sub. apply Int64.eqm_samerepr.
  apply Int64.eqm_sub; apply Int64.eqm_sym, Int64.eqm_unsigned_repr.
Qed.

Lemma fk_repr64_zero : forall a, 0 <= a <= Int64.max_unsigned -> Int64.repr a = Int64.zero -> a = 0.
Proof.
  intros a Ha E. apply (f_equal Int64.unsigned) in E. rewrite Int64.unsigned_repr in E by lia. exact E.
Qed.

Lemma fk_eq64 : forall a b, 0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int64.eq (Int64.repr a) (Int64.repr b) = (a =? b).
Proof.
  intros a b Ha Hb. unfold Int64.eq. rewrite !Int64.unsigned_repr by lia.
  destruct (zeq a b); destruct (Z.eqb_spec a b); auto; lia.
Qed.

(* a value below 8 or'ed with a multiple of 8 is their sum *)
Lemma fk_lor_small : forall k s, 0 <= k < 8 -> 0 <= s -> Z.lor k (s * 8) = k + s * 8.
Proof.
  intros k s Hk Hs.
  assert (L: Z.land k (s * 8) = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    change 8 with (2 ^ 3). destruct (Z.lt_ge_cases i 3).
    - rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
    - destruct (Z.eq_dec k 0); [subst; rewrite Z.bits_0; reflexivity |].
      rewrite (Z.bits_above_log2 k i); [reflexivity | lia |].
      assert (Z.log2 k < 3) by (apply Z.log2_lt_pow2; lia). lia. }
  rewrite <- Z.lxor_lor by exact L. rewrite Z.add_nocarry_lxor by exact L. reflexivity.
Qed.

(* the Block_Header value last | rle << 1 | size << 3 as new_frame computes it *)
Lemma fk_blkhdr : forall a r sz, 0 <= sz <= 2305843009213693945 ->
  Int64.or (Int64.repr (Z.lor (Int.signed (Int.repr (zb a))) (Int.unsigned (Int.shl (Int.repr (zb r)) (Int.repr 1)))))
    (Int64.shl (Int64.repr sz) (Int64.repr 3)) =
  Int64.repr (zb a + 2 * zb r + 8 * sz).
Proof.
  intros a r sz Hs.
  assert (E: Z.lor (Int.signed (Int.repr (zb a))) (Int.unsigned (Int.shl (Int.repr (zb r)) (Int.repr 1))) =
             zb a + 2 * zb r) by (destruct a, r; reflexivity).
  rewrite E. unfold Int64.shl, Int64.or.
  rewrite (Int64.unsigned_repr sz), (Int64.unsigned_repr 3) by rep_lia.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
  rewrite !Int64.unsigned_repr by (destruct a, r; simpl; rep_lia).
  rewrite fk_lor_small by (destruct a, r; simpl; lia). f_equal. lia.
Qed.

(* the model's slice and byte_at (model/Bytes.v) as VST's sublist and Znth *)
Lemma fk_slice_sublist : forall (l: list Z) i k, 0 <= i -> 0 <= k -> slice l i k = sublist i (i + k) l.
Proof. intros. unfold slice, sublist. rewrite firstn_skipn_comm, Z2Nat.inj_add by lia. reflexivity. Qed.

Lemma fk_byte_at_Znth : forall (l: list Z) i, 0 <= i -> byte_at l i = Znth i l.
Proof. intros. unfold byte_at, Znth. destruct (Z_lt_dec i 0); [lia | reflexivity]. Qed.

(* storing byte x just after the bytes l written so far into a buffer whose rest is not written *)
Lemma fk_upd_tail : forall (l: list Z) k M x, k = Zlength l -> 1 <= M ->
  upd_Znth k (zbytes l ++ Zrepeat Vundef M) (Vint (Int.repr x)) = zbytes (l ++ [x]) ++ Zrepeat Vundef (M - 1).
Proof. intros. subst k. apply upd_Znth_prefix. lia. Qed.

Lemma fk_sublist_snoc : forall (l: list Z) a i, 0 <= a -> 0 <= i -> a + i < Zlength l ->
  sublist a (a + (i + 1)) l = sublist a (a + i) l ++ [Znth (a + i) l].
Proof.
  intros. replace (a + (i + 1)) with (a + i + 1) by lia.
  rewrite (sublist_split a (a + i) (a + i + 1)) by lia.
  rewrite sublist_len_1 by lia. reflexivity.
Qed.

(* the k low bytes of x depend only on x modulo 256^m, for k <= m *)
Lemma fk_le_bytes_mod : forall k m x, (k <= m)%nat -> le_bytes k (x mod 256 ^ Z.of_nat m) = le_bytes k x.
Proof.
  induction k; intros m x Hk; [reflexivity |].
  destruct m as [|m]; [lia |].
  assert (P: 0 < 256 ^ Z.of_nat m) by (apply Z.pow_pos_nonneg; lia).
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
  rewrite Z.rem_mul_r by lia.
  cbn [le_bytes]. f_equal.
  - rewrite Z.mul_comm, Z_mod_plus_full. apply Z.mod_mod. lia.
  - rewrite Z.add_comm, Z.mul_comm, Z.div_add_l by lia.
    rewrite (Z.div_small (x mod 256)) by (apply Z.mod_pos_bound; lia). rewrite Z.add_0_r.
    apply IHk. lia.
Qed.

(* the 4 low bytes of a 64-bit value as put_le writes them *)
Lemma fk_le_bytes_u64 : forall x, le_bytes 4 (Int64.unsigned (Int64.repr x)) = le_bytes 4 x.
Proof.
  intros. rewrite Int64.unsigned_repr_eq. change Int64.modulus with (256 ^ Z.of_nat 8).
  apply fk_le_bytes_mod. lia.
Qed.

(* 64-bit comparisons in hypotheses, as comparisons of Z *)
Ltac fk_u64 :=
  change (Int64.repr 0) with Int64.zero in *;
  repeat match goal with
  | Hx: context [Int64.unsigned (Int64.repr ?a)] |- _ => rewrite (Int64.unsigned_repr a) in Hx by rep_lia
  | Hx: Int64.repr ?a = Int64.zero |- _ => apply fk_repr64_zero in Hx; [| rep_lia]
  | Hx: Int64.eq (Int64.repr ?a) (Int64.repr ?b) = true |- _ =>
      rewrite (fk_eq64 a b) in Hx by rep_lia; apply Z.eqb_eq in Hx
  | Hx: Int64.eq (Int64.repr ?a) (Int64.repr ?b) = false |- _ =>
      rewrite (fk_eq64 a b) in Hx by rep_lia; apply Z.eqb_neq in Hx
  | Hx: Int64.repr ?a <> Int64.zero |- _ =>
      let E := fresh in assert (a <> 0) by (intro E; rewrite E in Hx; apply Hx; reflexivity); clear Hx
  | Hx: Int64.repr ?a <> Int64.repr ?b |- _ =>
      let E := fresh in assert (a <> b) by (intro E; rewrite E in Hx; apply Hx; reflexivity); clear Hx
  end.

(* a branch on b & 1 as a fact on Z.odd b *)
Ltac fk_odd :=
  match goal with
  | Hx: Int.and (Int.repr ?b) (Int.repr 1) <> Int.zero |- _ =>
      let O := fresh "Odd" in
      assert (O: Z.odd b = true)
        by (destruct (Z.odd b) eqn:E; auto; exfalso; apply Hx, fk_odd_and1; [rep_lia | exact E]);
      clear Hx
  | Hx: Int.and (Int.repr ?b) (Int.repr 1) = Int.zero |- _ =>
      let O := fresh "Odd" in
      assert (O: Z.odd b = false) by (apply fk_odd_and1; [rep_lia | exact Hx]);
      clear Hx
  end.

(* a goal on boolean tests of integers: comparisons of C to Z, then every case *)
Ltac fk_bcase :=
  unfold nf_fcs_flag, nf_did_flag, nf_single, nf_fc1, nf_fc2, nf_fc3, nf_dc1, nf_dc2, nf_dc3 in *;
  rewrite ?fk_cmpu64, ?fk_cmpu32 by rep_lia; cbv beta iota;
  change (Int.unsigned (Int.repr (-1))) with 4294967295 in *;
  repeat match goal with
  | Hx: context [Int64.unsigned (Int64.repr ?a)] |- _ => rewrite (Int64.unsigned_repr a) in Hx by rep_lia
  | Hx: context [Int.unsigned (Int.repr ?a)] |- _ => rewrite (Int.unsigned_repr a) in Hx by rep_lia
  end;
  repeat match goal with
  | O: Z.odd ?a = _ |- context [Z.odd ?a] => rewrite O
  | |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b); try lia
  | |- context [Z.ltb ?a ?b] => destruct (Z.ltb_spec a b); try lia
  | |- context [Z.leb ?a ?b] => destruct (Z.leb_spec a b); try lia
  | |- context [Z.odd ?a] => destruct (Z.odd a)
  | |- context [zeq ?a ?b] => destruct (zeq a b); try lia
  | |- context [zlt ?a ?b] => destruct (zlt a b); try lia
  | Hx: context [Z.eqb ?a ?b] |- _ => destruct (Z.eqb_spec a b); try lia
  | Hx: context [Z.ltb ?a ?b] |- _ => destruct (Z.ltb_spec a b); try lia
  | Hx: context [Z.leb ?a ?b] |- _ => destruct (Z.leb_spec a b); try lia
  | Hx: context [Z.odd ?a] |- _ => destruct (Z.odd a)
  end; cbn [andb orb negb zb] in *;
  try reflexivity; try discriminate; try lia;
  try (exfalso; match goal with Hx: ?a <> ?a |- _ => apply Hx; reflexivity end).

(* the leaves of a chain of ifs that only set a temporary *)
Ltac fk_leaf := repeat (first [forward_if | forward]); entailer!; fk_bcase.

Local Open Scope logic.

Section Body.
Context {cs: compspecs}.

Lemma body_new_frame : semax_body [] G_new_frame f_new_frame new_frame_spec.
Proof.
  start_function.
  forward_if (EX f: val,
    PROP (f <> nullval -> Zlength d <= (PTRDIFF_MAX - 26) / 4)
    LOCAL (temp _t'1 f; gvars gv; temp _data p; temp _n (Vlong (Int64.repr (Zlength d)));
      temp _fcs (Vlong (Int64.repr fcs)); temp _max_window (Vlong (Int64.repr maxw));
      temp _dict_id (Vint (Int.repr did)); temp _len lp)
    SEP (mem_mgr gv; data_at sh (tarray tuchar (Zlength d)) (zbytes d) p;
      Spec_xxh.pw_pred w; data_at_ shl tulong lp;
      if eq_dec f nullval then emp
      else malloc_token Ews (tarray tuchar (26 + 4 * Zlength d)) f *
           data_at_ Ews (tarray tuchar (26 + 4 * Zlength d)) f)).
  { assert (HN: Zlength d <= 2305843009213693945).
    { rewrite Int64.unsigned_repr in H5 by rep_lia.
      change (Int64.unsigned (Int64.divs (Int64.sub (Int64.repr 9223372036854775807) (Int64.repr 26))
        (Int64.repr 4))) with 2305843009213693945 in H5. lia. }
    forward_call (tarray tuchar (26 + 4 * Zlength d), gv).
    { simpl sizeof. rewrite Z.max_r by rep_lia. rep_lia. }
    Intros f. forward. Exists f. entailer!. }
  { forward. Exists nullval. entailer!. }
  (* the header flags *)
  Intros f. forward.
  forward_call tt. Intros b0. forward.
  forward_call tt. Intros b1. forward.
  forward_call tt. Intros b2.
  rewrite !fk_and3 by rep_lia.
  forward_if (temp _t'6 (Vint (Int.repr (zb (nf_single b2 fcs maxw))))).
  { fk_odd. forward. entailer!. fk_bcase. }
  { fk_odd. forward. entailer!. fk_bcase. }
  forward.
  assert (Hf0: 0 <= b0 mod 4 < 4) by (apply Z.mod_pos_bound; lia).
  assert (Hd0: 0 <= b1 mod 4 < 4) by (apply Z.mod_pos_bound; lia).
  forward_if (temp _t'7 (Vint (Int.repr (zb ((b0 mod 4 =? 0) && nf_single b2 fcs maxw)%bool)))); [fk_leaf .. |].
  forward_if (temp _t'8 (Vint (Int.repr (zb (nf_fc1 (b0 mod 4) (nf_single b2 fcs maxw) fcs)))));
    [fk_leaf .. |].
  forward_if (temp _t'9 (Vint (Int.repr (zb (nf_fc1 (b0 mod 4) (nf_single b2 fcs maxw) fcs ||
    nf_fc2 (b0 mod 4) fcs)%bool)))); [fk_leaf .. |].
  forward_if (temp _t'10 (Vint (Int.repr (zb (nf_fc1 (b0 mod 4) (nf_single b2 fcs maxw) fcs ||
    nf_fc2 (b0 mod 4) fcs || nf_fc3 (b0 mod 4) fcs)%bool)))); [fk_leaf .. |].
  forward_if (temp _fcs_flag (Vint (Int.repr (nf_fcs_flag (b0 mod 4) (nf_single b2 fcs maxw) fcs))));
    [fk_leaf .. |].
  forward_if (temp _t'11 (Vint (Int.repr (zb (nf_dc1 (b1 mod 4) did))))); [fk_leaf .. |].
  forward_if (temp _t'12 (Vint (Int.repr (zb (nf_dc1 (b1 mod 4) did || nf_dc2 (b1 mod 4) did)%bool))));
    [fk_leaf .. |].
  forward_if (temp _t'13 (Vint (Int.repr (zb (nf_dc1 (b1 mod 4) did || nf_dc2 (b1 mod 4) did ||
    nf_dc3 (b1 mod 4) did)%bool)))); [fk_leaf .. |].
  forward_if (temp _did_flag (Vint (Int.repr (nf_did_flag (b1 mod 4) did)))); [fk_leaf .. |].
  pose proof (nf_fcs_flag_ok (b0 mod 4) (nf_single b2 fcs maxw) fcs ltac:(lia)) as HFF.
  pose proof (nf_did_flag_ok (b1 mod 4) did ltac:(lia) ltac:(lia)) as HDF.
  pose proof (nf_single_le b2 fcs maxw) as HSG.
  forget (nf_fcs_flag (b0 mod 4) (nf_single b2 fcs maxw) fcs) as FF.
  forget (nf_did_flag (b1 mod 4) did) as DF.
  forget (nf_single b2 fcs maxw) as SG.
  forward_if (temp _t'14 (Vint (Int.repr (if FF =? 0 then zb SG else 2 ^ FF)))).
  { forward. entailer!. }
  { forward; entailer!; destruct (Z.eqb_spec FF 0); try lia;
    assert (FF = 1 \/ FF = 2 \/ FF = 3) as [-> | [-> | ->]] by lia; reflexivity. }
  forward.
  forward_if (temp _t'15 (Vint (Int.repr (if DF =? 3 then 4 else DF)))).
  { forward. entailer!. }
  { forward. entailer!. destruct (Z.eqb_spec DF 3); [lia | reflexivity]. }
  forward.
  forward_call tt. Intros b3.
  deadvars!.
  assert (Hb3: 0 <= b3 / 8 < 32) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; rep_lia).
  forward.
  { entailer!. rewrite fk_wexp by rep_lia. rewrite fk_shr3 by rep_lia.
    rewrite !Int.unsigned_repr by rep_lia. rewrite Int.signed_repr by rep_lia.
    change (Int.unsigned Int64.iwordsize') with 64. rep_lia. }
  rewrite fk_wexp by rep_lia. rewrite Int.unsigned_repr by rep_lia.
  change (Int.signed (Int.repr 1)) with 1. rewrite fk_shl1 by lia.
  forward_if (temp _t'17 (Vlong (Int64.repr (nf_win SG fcs b3)))).
  { forward. entailer!. }
  { forward. entailer!. rewrite (fk_window b3 fcs) by rep_lia. reflexivity. }
  pose proof (nf_win_range SG fcs b3 H1 ltac:(rep_lia)) as Hwin.
  forward.
  (* gp_assume(window <= max_window) *)
  forward_call (Int.repr (zb (nf_win SG fcs b3 <=? maxw))).
  { entailer!. simpl. rewrite fk_ltu64 by rep_lia.
    destruct (Z.ltb_spec maxw (nf_win SG fcs b3)), (Z.leb_spec (nf_win SG fcs b3) maxw);
      try reflexivity; lia. }
  assert (Hwm: nf_win SG fcs b3 <= maxw)
    by (destruct (Z.leb_spec (nf_win SG fcs b3) maxw); [lia | contradiction]).
  forward_if.
  { destruct (eq_dec f nullval); entailer!. }
  { forward. Exists nullval d. entailer!. }
  rewrite if_false by auto. Intros.
  specialize (H5 ltac:(auto)).
  change ((PTRDIFF_MAX - 26) / 4) with 2305843009213693945 in H5.
  assert (HN: 0 <= Zlength d <= 2305843009213693945) by (split; [apply Zlength_nonneg | ]; lia).
  replace_SEP 5 (data_at Ews (tarray tuchar (Zlength (Zrepeat Vundef (26 + 4 * Zlength d))))
                  (Zrepeat Vundef (26 + 4 * Zlength d)) f).
  { entailer!. rewrite Zlength_Zrepeat by lia. apply derives_refl. }
  forward_call (Ews, f, Zrepeat Vundef (26 + 4 * Zlength d), 0, ZSTD_MAGICNUMBER, 4).
  { entailer!. }
  { rewrite Zlength_Zrepeat; rep_lia. }
  rewrite Zlength_Zrepeat by lia.
  forward_call tt. Intros b4.
  forward. forward.
  (* from here on the header is the record h of FModel.v *)
  rewrite fk_fhd, fk_zext8 by rep_lia.
  remember (Build_nf_header FF SG (Z.land b4 20) DF b3) as h eqn:Hh.
  assert (Hok: nh_ok fcs maxw did h).
  { subst h. unfold nh_ok; cbn. pose proof (fk_bits b4 ltac:(rep_lia)).
    unfold nf_win in Hwm. destruct SG; rep_lia || (repeat split; auto; rep_lia). }
  assert (Efhd: FF * 64 + zb SG * 32 + Z.land b4 20 + DF = nh_fhd h) by (subst h; reflexivity).
  rewrite Efhd.
  assert (E1: FF = nh_fcs_flag h) by (subst h; reflexivity).
  assert (E2: SG = nh_single h) by (subst h; reflexivity).
  assert (E3: DF = nh_did_flag h) by (subst h; reflexivity).
  assert (E4: b3 = nh_wd h) by (subst h; reflexivity).
  clear Hh Efhd. subst FF SG DF b3.
  change (nf_win (nh_single h) fcs (nh_wd h)) with (nh_window fcs h) in *.
  forward_if (temp _t'19 (Vint (Int.repr (if nh_single h then 5 else 6)))).
  { forward. entailer!. match goal with E: nh_single h = _ |- _ => rewrite E end. reflexivity. }
  { forward. entailer!. match goal with E: nh_single h = _ |- _ => rewrite E end. reflexivity. }
  forward. forward.
  forward_if (temp _t'20 (Vlong (Int64.repr (nh_max_block fcs h)))).
  { forward. entailer!. rewrite !Int64.unsigned_repr in H13 by rep_lia. unfold nh_max_block. rewrite Z.min_l by lia. auto. }
  { forward. entailer!. rewrite !Int64.unsigned_repr in H13 by rep_lia. unfold nh_max_block. rewrite Z.min_r by lia. auto. }
  forward.
  change (if nh_did_flag h =? 3 then 4 else nh_did_flag h) with (nh_did_size h).
  change (if nh_fcs_flag h =? 0 then zb (nh_single h) else 2 ^ nh_fcs_flag h) with (nh_fcs_size h).
  assert (Hds: 0 <= nh_did_size h <= 4) by (unfold nh_did_size; destruct (Z.eqb_spec (nh_did_flag h) 3); lia).
  assert (Hfs: 0 <= nh_fcs_size h <= 8).
  { unfold nh_fcs_size. assert (nh_fcs_flag h = 0 \/ nh_fcs_flag h = 1 \/ nh_fcs_flag h = 2 \/
      nh_fcs_flag h = 3) as [E|[E|[E|E]]] by lia; rewrite E; simpl; try lia; destruct (nh_single h); simpl; lia. }
  deadvars!.
  set (X3 := upd_Znth 5 (upd_Znth 4 (Spec_util.mem_written (Zrepeat Vundef (26 + 4 * Zlength d)) 0 4
                ZSTD_MAGICNUMBER) (Vint (Int.repr (nh_fhd h)))) (Vint (Int.repr (nh_wd h)))).
  assert (LX3: Zlength X3 = 26 + 4 * Zlength d).
  { assert (Zlength (Spec_util.mem_written (Zrepeat Vundef (26 + 4 * Zlength d)) 0 4 ZSTD_MAGICNUMBER) =
      26 + 4 * Zlength d) by (rewrite fk_mem_written_length; rewrite ?Zlength_Zrepeat; lia).
    subst X3. list_solve. }
  replace_SEP 0 (data_at Ews (tarray tuchar (Zlength X3)) X3 f).
  { entailer!. rewrite LX3. apply derives_refl. }
  replace (Int.signed (Int.repr (if nh_single h then 5 else 6))) with (if nh_single h then 5 else 6)
    by (destruct (nh_single h); reflexivity).
  change (Int.signed (Int.repr 0)) with 0.
  forward_call (Ews, f, X3, if nh_single h then 5 else 6, did, nh_did_size h).
  { entailer!. simpl. destruct f; try contradiction; simpl. rewrite !Int.unsigned_repr by rep_lia.
    reflexivity. }
  { rewrite LX3. destruct (nh_single h); lia. }
  forward_if (temp _t'21 (Vlong (Int64.repr (nh_fcs_value fcs h)))).
  { forward. entailer!. unfold nh_fcs_value. match goal with E: nh_fcs_flag h = _ |- _ => rewrite E end.
    reflexivity. }
  { forward. entailer!. unfold nh_fcs_value. destruct (Z.eqb_spec (nh_fcs_flag h) 1); [contradiction | auto]. }
  set (A0 := if nh_single h then 5 else 6) in *.
  set (X4 := Spec_util.mem_written X3 A0 (nh_did_size h) did).
  assert (LX4: Zlength X4 = Zlength X3) by (subst X4 A0; apply fk_mem_written_length; destruct (nh_single h); lia).
  replace_SEP 0 (data_at Ews (tarray tuchar (Zlength X4)) X4 f).
  { entailer!. rewrite LX4. apply derives_refl. }
  forward_call (Ews, f, X4, A0 + nh_did_size h, nh_fcs_value fcs h, nh_fcs_size h).
  { entailer!. simpl. destruct f; try contradiction; simpl.
    rewrite Int.unsigned_repr by rep_lia. reflexivity. }
  { rewrite LX4, LX3. subst A0. split; [destruct (nh_single h); lia |]. split; [destruct (nh_single h); lia |].
    unfold nh_fcs_value. destruct (Z.eqb_spec (nh_fcs_flag h) 1); lia. }
  forward.
  pose proof (nh_bytes_length fcs maxw did h Hok) as HL.
  pose proof (nh_bytes_ok fcs maxw did h Hok) as HBok.
  replace (Int64.add (Int64.repr A0) (Int64.repr (Int.unsigned (Int.add (Int.repr (nh_did_size h))
     (Int.repr (nh_fcs_size h))))))
    with (Int64.repr (Zlength (nh_bytes fcs did h))).
  2: { unfold Int.add. rewrite (Int.unsigned_repr (nh_did_size h)), (Int.unsigned_repr (nh_fcs_size h))
         by rep_lia.
       rewrite Int.unsigned_repr by rep_lia. rewrite fk_add64. f_equal.
       rewrite HL. subst A0. destruct (nh_single h); lia. }
  replace_SEP 0 (data_at Ews (tarray tuchar (26 + 4 * Zlength d))
    (zbytes (nh_bytes fcs did h) ++ Zrepeat Vundef (26 + 4 * Zlength d - Zlength (nh_bytes fcs did h))) f).
  { entailer!. rewrite LX4, LX3. subst X4 X3 A0.
    rewrite (nf_header_written fcs maxw did h (26 + 4 * Zlength d)) by (auto; lia). apply derives_refl. }
  clear X4 LX4 X3 LX3. deadvars!.
  forward.
  (* the block loop: the blocks bl written so far, the last one marked last (lst) only at the end *)
  forward_while (EX bl: list nf_block, EX lst: bool,
    PROP (if lst then nf_blocks_ok (nh_max_block fcs h) (Zlength d) 0 bl
          else nfb_open_ok (nh_max_block fcs h) (Zlength d) 0 bl;
          0 <= nfb_size bl <= Zlength d;
          Zlength (nf_content d 0 bl) = nfb_size bl;
          bytes_ok (nf_content d 0 bl);
          bytes_ok (nfb_bytes lst d 0 bl);
          Zlength (nh_bytes fcs did h) + Zlength (nfb_bytes lst d 0 bl) <= (if lst then 22 else 18) + 4 * nfb_size bl)
    LOCAL (temp _last (Vint (Int.repr (zb lst))); temp _done (Vlong (Int64.repr (nfb_size bl)));
           temp _at (Vlong (Int64.repr (Zlength (nh_bytes fcs did h) + Zlength (nfb_bytes lst d 0 bl))));
           temp _max_block (Vlong (Int64.repr (nh_max_block fcs h))); temp _f f; gvars gv; temp _data p;
           temp _n (Vlong (Int64.repr (Zlength d))); temp _len lp)
    SEP (data_at Ews (tarray tuchar (26 + 4 * Zlength d))
           (zbytes (nh_bytes fcs did h ++ nfb_bytes lst d 0 bl) ++
            Zrepeat Vundef ((26 + 4 * Zlength d) - (Zlength (nh_bytes fcs did h) + Zlength (nfb_bytes lst d 0 bl)))) f;
         mem_mgr gv;
         data_at sh (tarray tuchar (Zlength d)) (zbytes (nf_content d 0 bl ++ sublist (nfb_size bl) (Zlength d) d)) p;
         Spec_xxh.pw_pred w; data_at_ shl tulong lp; malloc_token Ews (tarray tuchar (26 + 4 * Zlength d)) f)).
  { Exists (@nil nf_block) false. cbn [nfb_bytes nf_content nfb_size nfb_open_ok zb].
    rewrite Zlength_nil, !app_nil_r, Z.add_0_r, sublist_same by lia.
    entailer!. split; [constructor |]. split; [constructor |]. destruct (nh_single h); lia. }
  { entailer!. }
  { destruct lst; [discriminate HRE |]. clear HRE.
    set (D := nfb_size bl) in *. set (B := nfb_bytes false d 0 bl) in *. set (CT := nf_content d 0 bl) in *.
    set (HB := nh_bytes fcs did h) in *. set (mb := nh_max_block fcs h) in *. set (n := Zlength d) in *.
    assert (Hmb: 0 <= mb <= 131072) by (subst mb; unfold nh_max_block; lia).
    forward. rewrite fk_sub64.
    forward_if (temp _t'22 (Vlong (Int64.repr (Z.min (n - D) mb)))).
    { forward. entailer!. fk_u64. rewrite Z.min_l by lia. auto. }
    { forward. entailer!. fk_u64. rewrite Z.min_r by lia. auto. }
    forward.
    set (most := Z.min (n - D) mb).
    assert (Hmost: 0 <= most <= n - D /\ most <= mb) by (subst most; lia).
    forward_if (EX sz: Z, PROP ((D = n /\ sz = 0) \/ (D < n /\ 1 <= sz <= Z.max 1 most))
      LOCAL (temp _t'23 (Vlong (Int64.repr sz)); temp _done (Vlong (Int64.repr D)); temp _at (Vlong (Int64.repr (Zlength HB + Zlength B))); temp _max_block (Vlong (Int64.repr mb)); temp _f f; gvars gv; temp _data p; temp _n (Vlong (Int64.repr n)); temp _len lp) SEP (data_at Ews (tarray tuchar (26 + 4 * n)) (zbytes (HB ++ B) ++ Zrepeat Vundef (26 + 4 * n - (Zlength HB + Zlength B))) f; mem_mgr gv; data_at sh (tarray tuchar n) (zbytes (CT ++ sublist D n d)) p; Spec_xxh.pw_pred w; data_at_ shl tulong lp; malloc_token Ews (tarray tuchar (26 + 4 * n)) f)).
    { forward. Exists 0. entailer!. fk_u64. lia. }
    { forward_if (temp _t'24 (Vlong (Int64.repr (if most =? 0 then 0 else most - 1)))).
      { forward. entailer!. fk_u64. destruct (Z.eqb_spec most 0); [reflexivity | lia]. }
      { forward. entailer!. fk_u64. rewrite ?fk_sub64. destruct (Z.eqb_spec most 0); [lia | try reflexivity]. }
      forward_call (if most =? 0 then 0 else most - 1).
      { destruct (Z.eqb_spec most 0); rep_lia. }
      Intros v. forward. Exists (1 + v). entailer!. fk_u64. right. destruct (Z.eqb_spec most 0); lia. }
    Intros sz. forward.
    forward_call tt. Intros b5.
    forward_if (temp _t'27 (Vint (Int.repr (zb (Z.odd b5 && (0 <? mb))%bool)))).
    { fk_odd. forward. entailer!. fk_bcase. }
    { fk_odd. forward. entailer!. fk_bcase. }
    forward.
    assert (HRL: (Z.odd b5 && (0 <? mb))%bool = true -> 0 < mb)
      by (intro X; apply andb_prop in X as [_ X]; apply Z.ltb_lt; auto).
    forget (Z.odd b5 && (0 <? mb))%bool as RL.
    deadvars!.
    forward_if (EX lst': bool, PROP ((lst' = true -> (D + sz = n)%Z) /\ (lst' = false -> (0 < sz)%Z))
      LOCAL (temp _t'28 (Vint (Int.repr (zb lst'))); temp _rle (Vint (Int.repr (zb RL)));
             temp _size (Vlong (Int64.repr sz)); temp _done (Vlong (Int64.repr D)); temp _at (Vlong (Int64.repr (Zlength HB + Zlength B))); temp _max_block (Vlong (Int64.repr mb)); temp _f f; gvars gv; temp _data p; temp _n (Vlong (Int64.repr n)); temp _len lp)
      SEP (data_at Ews (tarray tuchar (26 + 4 * n)) (zbytes (HB ++ B) ++ Zrepeat Vundef (26 + 4 * n - (Zlength HB + Zlength B))) f; mem_mgr gv; data_at sh (tarray tuchar n) (zbytes (CT ++ sublist D n d)) p; Spec_xxh.pw_pred w; data_at_ shl tulong lp; malloc_token Ews (tarray tuchar (26 + 4 * n)) f)).
    { forward_if.
      { forward. Exists true. entailer!. fk_u64. lia. }
      { forward_call tt. Intros b6. forward. forward. Exists (Z.odd b6). entailer!.
        fk_u64. split; [intros; lia |]. split; [intros; lia |].
        change (Z.land b6 1) with (Z.land b6 (Z.ones 1)). rewrite Z.land_ones by lia.
        change (2 ^ 1) with 2. rewrite Zmod_odd. destruct (Z.odd b6); reflexivity. }
    }
    { forward. Exists false. entailer!. fk_u64. lia. }
    Intros lst'. forward.
    set (T := Zlength HB + Zlength B) in *.
    assert (HT: 5 <= T <= 18 + 4 * D) by (subst T; pose proof (Zlength_nonneg B); destruct (nh_single h); lia).
    set (c := zbytes (HB ++ B) ++ Zrepeat Vundef (26 + 4 * n - T)).
    assert (Lc: Zlength c = 26 + 4 * n) by (subst c T; rewrite Zlength_app, Zlength_map, Zlength_app, Zlength_Zrepeat; lia).
    replace_SEP 0 (data_at Ews (tarray tuchar (Zlength c)) c f).
    { entailer!. rewrite Lc. apply derives_refl. }
    forward_call (Ews, f, c, T, zb lst' + 2 * zb RL + 8 * sz, 3).
    { entailer!. simpl. rewrite fk_blkhdr by lia. reflexivity. }
    { destruct lst', RL; simpl; rep_lia. }
    set (hb := le_bytes 3 (zb lst' + 2 * zb RL + 8 * sz)).
    assert (Lhb: Zlength hb = 3) by (subst hb; rewrite Zlength_le_bytes; reflexivity).
    assert (LHBB: Zlength (HB ++ B) = T) by (subst T; rewrite Zlength_app; reflexivity).
    assert (Ec: Spec_util.mem_written c T 3 (zb lst' + 2 * zb RL + 8 * sz) =
                zbytes ((HB ++ B) ++ hb) ++ Zrepeat Vundef (26 + 4 * n - (T + 3))).
    { subst c. rewrite mem_written_prefix by (rewrite ?LHBB; lia). rewrite LHBB, sublist_same by lia.
      f_equal. f_equal. lia. }
    rewrite Ec, Lc. clear Ec.
    forward.
    destruct RL.
    (* an RLE block: its part of the data becomes its first byte repeated, one byte in the frame *)
    { change (Int.signed (Int.repr 3)) with 3. rewrite fk_add64.
      assert (Hmb0: 0 < mb) by (apply HRL; reflexivity).
      assert (Hbd: sz > 0 -> 0 <= Znth D d < 256) by (intro; apply (proj1 (Forall_Znth _ _) H); lia).
      forward_for_simple_bound sz (EX i: Z,
        PROP ()
        LOCAL (temp _at (Vlong (Int64.repr (T + 3))); temp _rle (Vint (Int.repr (zb true)));
               temp _size (Vlong (Int64.repr sz)); temp _last (Vint (Int.repr (zb lst'))); temp _done (Vlong (Int64.repr D)); temp _max_block (Vlong (Int64.repr mb)); temp _f f; gvars gv; temp _data p; temp _n (Vlong (Int64.repr n)); temp _len lp)
        SEP (data_at Ews (tarray tuchar (26 + 4 * n))
               (zbytes ((HB ++ B) ++ hb) ++ Zrepeat Vundef (26 + 4 * n - (T + 3))) f;
             mem_mgr gv; data_at sh (tarray tuchar n) (zbytes (CT ++ Zrepeat (Znth D d) i ++ sublist (D + i) n d)) p;
             Spec_xxh.pw_pred w; data_at_ shl tulong lp; malloc_token Ews (tarray tuchar (26 + 4 * n)) f)).
      { rewrite Z.add_0_r. change (Zrepeat (Znth D d) 0) with (@nil Z). rewrite app_nil_l. entailer!. }
      { forward_if.
        2: { exfalso. match goal with Hx: Int.repr 1 = Int.zero |- _ => discriminate Hx end. }
        assert (Hin: D + i < n) by lia.
        assert (Ex: Znth D (CT ++ Zrepeat (Znth D d) i ++ sublist (D + i) n d) = Znth D d).
        { rewrite Znth_app2 by lia. rewrite H15, Z.sub_diag. destruct (Z.eq_dec i 0).
          - subst i. change (Zrepeat (Znth D d) 0) with (@nil Z). rewrite app_nil_l, Znth_sublist by lia.
            f_equal. lia.
          - rewrite Znth_app1 by (rewrite Zlength_Zrepeat; lia). apply Znth_Zrepeat. lia. }
        specialize (Hbd ltac:(lia)).
        forward.
        { entailer!. rewrite Ex. simpl. rep_lia. }
        rewrite Ex.
        forward.
        entailer!. apply derives_refl'. f_equal. list_solve. }
      apply semax_if_seq. forward_if.
      2: { exfalso. match goal with Hx: Int.repr 1 = Int.zero |- _ => discriminate Hx end. }
      forward. forward.
      change (Int.signed (Int.repr 1)) with 1. rewrite fk_add64.
      apply semax_if_seq. forward_if.
      { forward_call tt. Intros b7. forward. forward.
      fk_u64. rewrite fk_zext8 by rep_lia.
      rewrite fk_upd_tail by (rewrite ?Zlength_app, ?Lhb, ?LHBB; lia).
      set (b := {| nb_size := sz; nb_rle := true; nb_byte := b7 |}).
      assert (Hblk: blk_ok mb n D b).
      { unfold blk_ok; simpl. split; [lia|]. split; [lia|]. split; [intros _; lia | rep_lia]. }
      destruct (nf_step d HB mb bl b lst' H H13 H14 H15 H16 H17 H18 Hblk H21 H22) as (S1 & S2 & S3 & S4 & S5 & S6).
      Exists (bl ++ [b], lst'). simpl fst; simpl snd.
      rewrite nfb_size_snoc, nf_content_snoc, nfb_bytes_snoc in *. rewrite ?Z.add_0_l in *.
      assert (Ehd: nb_header lst' b = hb) by reflexivity.
      assert (Epl: nb_payload d (nfb_size bl) b = [b7])
        by (unfold nb_payload; simpl; fk_u64; destruct (Z.eqb_spec sz 0); [reflexivity | lia]).
      assert (Ect: nb_content d (nfb_size bl) b = Zrepeat (Znth D d) sz)
        by (unfold nb_content; simpl; rewrite fk_byte_at_Znth by lia; reflexivity).
      rewrite ?Ehd, ?Epl, ?Ect in *. change (nb_size b) with sz in *.
      change (nfb_bytes false d 0 bl) with B. change (nf_content d 0 bl) with CT.
      change (nfb_bytes false d 0 bl) with B in S6.
      assert (Ecnt: Zlength HB + Zlength (B ++ hb ++ [b7]) = T + 3 + 1)
        by (rewrite !Zlength_app, Lhb; simpl; lia).
      rewrite Ecnt. rewrite <- !app_assoc.
      rewrite Ecnt in S6.
      entailer!. apply derives_refl'. do 2 f_equal. apply (f_equal (Zrepeat Vundef)). lia. }
      { fk_u64.
        specialize (Hbd ltac:(lia)).
        assert (LCT: Zlength (CT ++ Zrepeat (Znth D d) sz ++ sublist (D + sz) n d) = n)
          by (rewrite !Zlength_app, Zlength_Zrepeat, Zlength_sublist by lia; lia).
        assert (Ex: Znth D (CT ++ Zrepeat (Znth D d) sz ++ sublist (D + sz) n d) = Znth D d).
        { rewrite Znth_app2 by lia. rewrite H15, Z.sub_diag, Znth_app1 by (rewrite Zlength_Zrepeat; lia).
          apply Znth_Zrepeat. lia. }
        forward.
        { entailer!. rewrite Ex. simpl. rep_lia. }
        rewrite Ex. forward. forward. forward.
      rewrite ?fk_zext8 by rep_lia.
      rewrite fk_upd_tail by (rewrite ?Zlength_app, ?Lhb, ?LHBB; lia).
      set (b := {| nb_size := sz; nb_rle := true; nb_byte := 0 |}).
      assert (Hblk: blk_ok mb n D b).
      { unfold blk_ok; simpl. split; [lia|]. split; [lia|]. split; [intros _; lia | rep_lia]. }
      destruct (nf_step d HB mb bl b lst' H H13 H14 H15 H16 H17 H18 Hblk H21 H22) as (S1 & S2 & S3 & S4 & S5 & S6).
      Exists (bl ++ [b], lst'). simpl fst; simpl snd.
      rewrite nfb_size_snoc, nf_content_snoc, nfb_bytes_snoc in *. rewrite ?Z.add_0_l in *.
      assert (Ehd: nb_header lst' b = hb) by reflexivity.
      assert (Epl: nb_payload d (nfb_size bl) b = [Znth D d])
        by (unfold nb_payload; simpl; fk_u64; destruct (Z.eqb_spec sz 0); [lia | rewrite fk_byte_at_Znth by lia; reflexivity]).
      assert (Ect: nb_content d (nfb_size bl) b = Zrepeat (Znth D d) sz)
        by (unfold nb_content; simpl; rewrite fk_byte_at_Znth by lia; reflexivity).
      rewrite ?Ehd, ?Epl, ?Ect in *. change (nb_size b) with sz in *.
      change (nfb_bytes false d 0 bl) with B. change (nf_content d 0 bl) with CT.
      change (nfb_bytes false d 0 bl) with B in S6.
      assert (Ecnt: Zlength HB + Zlength (B ++ hb ++ [Znth D d]) = T + 3 + 1)
        by (rewrite !Zlength_app, Lhb; simpl; lia).
      rewrite Ecnt. rewrite <- !app_assoc.
      rewrite Ecnt in S6.
      entailer!. apply derives_refl'. do 2 f_equal. apply (f_equal (Zrepeat Vundef)). lia. }
    }
    (* a Raw block: its part of the data copied into the frame *)
    { forward_for_simple_bound sz (EX i: Z,
        PROP ()
        LOCAL (temp _at (Vlong (Int64.repr (T + 3 + i))); temp _rle (Vint (Int.repr (zb false)));
               temp _size (Vlong (Int64.repr sz)); temp _last (Vint (Int.repr (zb lst'))); temp _done (Vlong (Int64.repr D)); temp _max_block (Vlong (Int64.repr mb)); temp _f f; gvars gv; temp _data p; temp _n (Vlong (Int64.repr n)); temp _len lp)
        SEP (data_at Ews (tarray tuchar (26 + 4 * n))
               (zbytes ((HB ++ B) ++ hb ++ sublist D (D + i) d) ++ Zrepeat Vundef (26 + 4 * n - (T + 3 + i))) f;
             mem_mgr gv; data_at sh (tarray tuchar n) (zbytes (CT ++ sublist D n d)) p;
             Spec_xxh.pw_pred w; data_at_ shl tulong lp; malloc_token Ews (tarray tuchar (26 + 4 * n)) f)).
      { change (Int.signed (Int.repr 3)) with 3. rewrite fk_add64, !Z.add_0_r, sublist_nil, app_nil_r.
        entailer!. }
      { forward_if.
        { exfalso; lia. }
        forward. forward.
        change (Int.signed (Int.repr 1)) with 1. rewrite fk_add64.
        assert (Hin: D + i < n) by lia.
        assert (Ex: Znth (D + i) (CT ++ sublist D n d) = Znth (D + i) d).
        { rewrite Znth_app2 by lia. rewrite H15, Znth_sublist by lia. f_equal. lia. }
        assert (Hbx: 0 <= Znth (D + i) d < 256) by (apply (proj1 (Forall_Znth _ _) H); lia).
        forward.
        { entailer!. rewrite Ex. simpl. rep_lia. }
        rewrite Ex.
        forward.
        entailer!.
        { do 2 f_equal. lia. }
        apply derives_refl'. f_equal.
        rewrite fk_upd_tail by (rewrite ?Zlength_app, ?Lhb, ?Zlength_sublist; lia).
        rewrite fk_sublist_snoc by lia. rewrite !app_assoc. f_equal. f_equal. lia. }
      apply semax_if_seq. forward_if. { exfalso; lia. }
      forward.
      set (b := {| nb_size := sz; nb_rle := false; nb_byte := 0 |}).
      assert (Hblk: blk_ok mb n D b).
      { unfold blk_ok; simpl. split; [lia|]. split; [lia|]. split; [discriminate | lia]. }
      destruct (nf_step d HB mb bl b lst' H H13 H14 H15 H16 H17 H18 Hblk H21 H22) as (S1 & S2 & S3 & S4 & S5 & S6).
      Exists (bl ++ [b], lst'). simpl fst; simpl snd.
      rewrite nfb_size_snoc, nf_content_snoc, nfb_bytes_snoc in *. rewrite ?Z.add_0_l in *.
      assert (Ehd: nb_header lst' b = hb) by reflexivity.
      assert (Epl: nb_payload d (nfb_size bl) b = sublist D (D + sz) d)
        by (unfold nb_payload; simpl; apply fk_slice_sublist; lia).
      assert (Ect: nb_content d (nfb_size bl) b = sublist D (D + sz) d)
        by (unfold nb_content; simpl; apply fk_slice_sublist; lia).
      rewrite ?Ehd, ?Epl, ?Ect in *. change (nb_size b) with sz in *.
      change (nfb_bytes false d 0 bl) with B. change (nf_content d 0 bl) with CT.
      change (nfb_bytes false d 0 bl) with B in S6.
      assert (Ecnt: Zlength HB + Zlength (B ++ hb ++ sublist D (D + sz) d) = T + 3 + sz)
        by (rewrite !Zlength_app, Lhb, Zlength_sublist by lia; lia).
      rewrite Ecnt. rewrite <- !app_assoc. rewrite sublist_rejoin by lia.
      rewrite Ecnt in S6.
      entailer!. }
    }
  (* after the loop: the choices c, the checksum, copy_of, free *)
  destruct lst; [| exfalso; apply HRE; reflexivity]. clear HRE.
  set (c := {| nc_hdr := h; nc_blocks := bl |}).
  assert (Hsz: nfb_size bl = Zlength d) by (pose proof (nf_blocks_ok_size _ _ _ _ H13); lia).
  assert (Hnf: nf_ok (Zlength d) fcs maxw did c) by (split; [exact Hok | exact H13]).
  rewrite Hsz, sublist_nil, app_nil_r.
  rewrite nfb_bytes_closed in *.
  change (nf_content d 0 bl) with (nf_data d c) in *.
  set (HB := nh_bytes fcs did h) in *. set (BB := nf_blocks_bytes d 0 bl) in *. set (DD := nf_data d c) in *.
  set (T := Zlength HB + Zlength BB) in *.
  set (F := nf_bytes d fcs did c).
  assert (EF: F = HB ++ BB ++ (if nh_checksum h then le_bytes 4 (xxh64 DD 0) else [])) by reflexivity.
  assert (LF: Zlength F = T + (if nh_checksum h then 4 else 0)).
  { rewrite EF, !Zlength_app. subst T. destruct (nh_checksum h); [rewrite Zlength_le_bytes |]; rewrite ?Zlength_nil; simpl; lia. }
  assert (HFok: bytes_ok F).
  { rewrite EF. apply Forall_app; split; [exact HBok |]. apply Forall_app; split; [exact H17 |].
    destruct (nh_checksum h); [apply le_bytes_ok | constructor]. }
  assert (LDD: Zlength DD = Zlength d) by (rewrite H15; exact Hsz).
  assert (E4: Znth 4 HB = nh_fhd h) by (subst HB; unfold nh_bytes; reflexivity).
  assert (L5: 5 <= Zlength HB) by (rewrite HL; destruct (nh_single h); lia).
  assert (Hfhd: 0 <= nh_fhd h < 256) by (rewrite <- E4; apply (proj1 (Forall_Znth _ _) HBok); lia).
  forward.
  { entailer!. all: rewrite ?Int.unsigned_repr by rep_lia; rep_lia. }
  forward_if (PROP ()
    LOCAL (temp _at (Vlong (Int64.repr (Zlength F))); temp _f f; gvars gv; temp _data p;
           temp _n (Vlong (Int64.repr (Zlength d))); temp _len lp)
    SEP (data_at Ews (tarray tuchar (26 + 4 * Zlength d)) (zbytes F ++ Zrepeat Vundef ((26 + 4 * Zlength d) - Zlength F)) f; mem_mgr gv;
         data_at sh (tarray tuchar (Zlength d)) (zbytes DD) p; Spec_xxh.pw_pred w; data_at_ shl tulong lp;
         malloc_token Ews (tarray tuchar (26 + 4 * Zlength d)) f)).
  { assert (Hck: nh_checksum h = true)
      by (destruct (nh_checksum h) eqn:E; auto; apply (fk_cksum _ _ _ _ Hok) in E; contradiction).
    replace_SEP 2 (@data_at Zstd.proof.zstd.Base.CompSpecs sh (tarray tuchar (Zlength DD))
                     (Spec_xxh.xxh_bytes DD) p).
    { entailer!. rewrite LDD, (data_at_bytes_cs cs Zstd.proof.zstd.Base.CompSpecs). apply derives_refl. }
    forward_call (sh, p, DD, 0, w).
    { entailer!. simpl. rewrite LDD. destruct p; try contradiction; reflexivity. }
    { apply H4; lia. }
    replace_SEP 0 (data_at sh (tarray tuchar (Zlength d)) (zbytes DD) p).
    { entailer!. rewrite LDD, (data_at_bytes_cs Zstd.proof.zstd.Base.CompSpecs cs). apply derives_refl. }
    set (X := xxh64 DD 0).
    set (cc := zbytes (HB ++ BB) ++ Zrepeat Vundef (26 + 4 * Zlength d - T)).
    assert (LHBB: Zlength (HB ++ BB) = T) by (subst T; apply Zlength_app).
    assert (Lcc: Zlength cc = 26 + 4 * Zlength d)
      by (subst cc; rewrite Zlength_app, Zlength_map, LHBB, Zlength_Zrepeat; lia).
    replace_SEP 2 (data_at Ews (tarray tuchar (Zlength cc)) cc f).
    { entailer!. rewrite Lcc. apply derives_refl. }
    forward_call (Ews, f, cc, T, Int64.unsigned (Int64.repr X), 4).
    { entailer!. simpl. replace (Int64.Z_mod_modulus X) with (Int64.unsigned (Int64.repr X)) by reflexivity.
      rewrite Int64.repr_unsigned. reflexivity. }
    assert (Ecc: Spec_util.mem_written cc T 4 (Int64.unsigned (Int64.repr X)) =
                 zbytes ((HB ++ BB) ++ le_bytes 4 X) ++ Zrepeat Vundef (26 + 4 * Zlength d - (T + 4))).
    { subst cc T. pose proof (Zlength_nonneg HB). pose proof (Zlength_nonneg BB).
      rewrite mem_written_prefix by (rewrite ?LHBB; lia). rewrite LHBB, sublist_same by lia.
      change (Z.to_nat 4) with 4%nat. rewrite fk_le_bytes_u64. f_equal. f_equal. lia. }
    rewrite Ecc, Lcc. clear Ecc.
    forward.
    change (Int.signed (Int.repr 4)) with 4. rewrite fk_add64.
    rewrite Hck in LF, EF. rewrite EF. rewrite EF in LF. rewrite LF. rewrite <- app_assoc.
    entailer!. }
  { forward. assert (Hck: nh_checksum h = false) by (apply (fk_cksum _ _ _ _ Hok); auto).
    rewrite Hck in LF, EF. rewrite EF, app_nil_r. rewrite EF, app_nil_r in LF.
    rewrite LF, Z.add_0_r. entailer!. }
  forward.
  assert (LF2: 0 <= Zlength F <= (26 + 4 * Zlength d))
    by (rewrite LF; subst T; pose proof (Zlength_nonneg HB); pose proof (Zlength_nonneg BB); destruct (nh_checksum h); lia).
  rewrite (split2_data_at_Tarray_app (Zlength F) (26 + 4 * Zlength d) Ews tuchar (zbytes F) (Zrepeat Vundef ((26 + 4 * Zlength d) - Zlength F)) f)
    by (rewrite ?Zlength_map, ?Zlength_Zrepeat; lia).
  forward_call (gv, Ews, f, F).
  { cancel. }
  Intros q.
  gather_SEP 1 3.
  replace_SEP 0 (data_at_ Ews (tarray tuchar (26 + 4 * Zlength d)) f).
  { entailer!.
    rewrite <- split2_data_at_Tarray_app by (rewrite ?Zlength_map, ?Zlength_Zrepeat; lia).
    apply data_at_data_at_. }
  forward_call (tarray tuchar (26 + 4 * Zlength d), f, gv).
  { rewrite if_false by auto. cancel. }
  forward.
  Exists q DD.
  entailer!.
  destruct (eq_dec q nullval).
  - unfold mbytes. rewrite if_true by auto. rewrite emp_sepcon. apply data_at_data_at_.
  - Exists c. entailer!.
Qed.

End Body.
