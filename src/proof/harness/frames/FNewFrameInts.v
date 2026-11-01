(* Byte arithmetic of new_frame's Frame_Header_Descriptor (harness/frames.h), in CompCert's 32-bit integers:
   the descriptor is computed as (unsigned char) (fcs_flag << 6 | single << 5 | (b & 0x14) | did_flag) for a
   byte b drawn by nondet_u8, and the checksum is written when (f[4] & 4) is set. *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.harness.frames.FModel.

(* The three facts are checked over all their (finitely many) cases by computation: [z_range n] lists 0..n-1,
   and the boolean checks below are evaluated by vm_compute. *)
Definition z_range (n: nat) : list Z := map Z.of_nat (seq 0 n).

Lemma in_z_range : forall n x, 0 <= x < Z.of_nat n -> In x (z_range n).
Proof.
  intros n x Hx. unfold z_range. apply in_map_iff. exists (Z.to_nat x). split.
  - apply Z2Nat.id; lia.
  - apply in_seq. lia.
Qed.

(* the descriptor computed by new_frame, in CompCert integers *)
Definition fk_fhd_int (ff: Z) (sg: bool) (b df: Z) : int :=
  Int.zero_ext 8 (Int.zero_ext 8 (Int.or (Int.or (Int.or (Int.shl (Int.repr ff) (Int.repr 6))
    (Int.shl (Int.repr (zb sg)) (Int.repr 5))) (Int.and (Int.repr b) (Int.repr 20))) (Int.repr df))).

Definition fk_fhd_check : bool :=
  forallb (fun ff => forallb (fun sg => forallb (fun b => forallb (fun df =>
    Int.eq (fk_fhd_int ff sg b df) (Int.repr (ff * 64 + zb sg * 32 + Z.land b 20 + df)))
    (z_range 4)) (z_range 256)) [true; false]) (z_range 4).

Lemma fk_fhd_check_true : fk_fhd_check = true.
Proof. vm_compute. reflexivity. Qed.

(* the descriptor byte as an integer sum (nh_fhd of FModel.v) *)
Lemma fk_fhd : forall ff sg b df, 0 <= ff <= 3 -> 0 <= df <= 3 -> 0 <= b <= 255 ->
  Int.zero_ext 8 (Int.zero_ext 8 (Int.or (Int.or (Int.or (Int.shl (Int.repr ff) (Int.repr 6))
    (Int.shl (Int.repr (zb sg)) (Int.repr 5))) (Int.and (Int.repr b) (Int.repr 20))) (Int.repr df))) =
  Int.repr (ff * 64 + zb sg * 32 + Z.land b 20 + df).
Proof.
  intros ff sg b df Hff Hdf Hb.
  pose proof fk_fhd_check_true as H. unfold fk_fhd_check in H.
  rewrite forallb_forall in H. specialize (H ff (in_z_range 4 ff ltac:(lia))).
  rewrite forallb_forall in H. specialize (H sg ltac:(destruct sg; simpl; auto)).
  rewrite forallb_forall in H. specialize (H b (in_z_range 256 b ltac:(lia))).
  rewrite forallb_forall in H. specialize (H df (in_z_range 4 df ltac:(lia))).
  apply Int.same_if_eq in H. exact H.
Qed.

(* bits 4 and 2 of a byte: Unused_bit and Content_Checksum_flag *)
Definition fk_bits_check : bool :=
  forallb (fun b => existsb (Z.eqb (Z.land b 20)) [0; 4; 16; 20]) (z_range 256).

Lemma fk_bits_check_true : fk_bits_check = true.
Proof. vm_compute. reflexivity. Qed.

Lemma fk_bits : forall b, 0 <= b <= 255 -> In (Z.land b 20) [0; 4; 16; 20].
Proof.
  intros b Hb.
  pose proof fk_bits_check_true as H. unfold fk_bits_check in H.
  rewrite forallb_forall in H. specialize (H b (in_z_range 256 b ltac:(lia))).
  apply existsb_exists in H. destruct H as [x [Hx Heq]].
  apply Z.eqb_eq in Heq. rewrite Heq. exact Hx.
Qed.

Definition fk_cksum_check : bool :=
  forallb (fun ff => forallb (fun sg => forallb (fun bits => forallb (fun df =>
    Bool.eqb (Int.eq (Int.and (Int.repr (ff * 64 + zb sg * 32 + bits + df)) (Int.repr 4)) Int.zero)
      (negb (Z.testbit bits 2)))
    (z_range 4)) [0; 4; 16; 20]) [true; false]) (z_range 4).

Lemma fk_cksum_check_true : fk_cksum_check = true.
Proof. vm_compute. reflexivity. Qed.

(* the test f[4] & 4 reads the Content_Checksum_flag of the descriptor *)
Lemma fk_cksum : forall fcs maxw did h, nh_ok fcs maxw did h ->
  (Int.and (Int.repr (nh_fhd h)) (Int.repr 4) = Int.zero <-> nh_checksum h = false).
Proof.
  intros fcs maxw did h Hok.
  destruct Hok as (Hff & _ & _ & _ & _ & Hbits & Hdf & _).
  pose proof fk_cksum_check_true as H. unfold fk_cksum_check in H.
  rewrite forallb_forall in H. specialize (H (nh_fcs_flag h) (in_z_range 4 (nh_fcs_flag h) ltac:(lia))).
  rewrite forallb_forall in H. specialize (H (nh_single h) ltac:(destruct (nh_single h); simpl; auto)).
  rewrite forallb_forall in H. specialize (H (nh_bits h) Hbits).
  rewrite forallb_forall in H. specialize (H (nh_did_flag h) (in_z_range 4 (nh_did_flag h) ltac:(lia))).
  unfold nh_fhd, nh_checksum.
  apply Bool.eqb_prop in H. pose proof (Int.eq_spec
    (Int.and (Int.repr (nh_fcs_flag h * 64 + zb (nh_single h) * 32 + nh_bits h + nh_did_flag h)) (Int.repr 4))
    Int.zero) as E.
  rewrite H in E. destruct (Z.testbit (nh_bits h) 2); simpl in E; split; intro; congruence.
Qed.

(* the three facts above, for the record of what this file proves *)
Lemma nf_new_frame_ints :
  (forall ff sg b df, 0 <= ff <= 3 -> 0 <= df <= 3 -> 0 <= b <= 255 ->
    Int.zero_ext 8 (Int.zero_ext 8 (Int.or (Int.or (Int.or (Int.shl (Int.repr ff) (Int.repr 6))
      (Int.shl (Int.repr (zb sg)) (Int.repr 5))) (Int.and (Int.repr b) (Int.repr 20))) (Int.repr df))) =
    Int.repr (ff * 64 + zb sg * 32 + Z.land b 20 + df)) /\
  (forall b, 0 <= b <= 255 -> In (Z.land b 20) [0; 4; 16; 20]) /\
  (forall fcs maxw did h, nh_ok fcs maxw did h ->
    (Int.and (Int.repr (nh_fhd h)) (Int.repr 4) = Int.zero <-> nh_checksum h = false)).
Proof. exact (conj fk_fhd (conj fk_bits fk_cksum)). Qed.
