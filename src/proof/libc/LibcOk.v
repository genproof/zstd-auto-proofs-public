(* The typed memcpy of the callers (LibcSpec.memcpy_spec) from libc.c's byte loop (LibcSpec.memcpy_bytes_spec),
   and memcpy_ok for the objects the decoder and the harnesses copy: byte strings and 32-bit scalars.
   Stated for any compspecs. *)
From Coq Require Import List.
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.model.Bytes Zstd.proof.zstd.PickLemmas.
Require Export Zstd.proof.libc.LibcSpec.
Import ListNotations.

Section LibcOk.
Context {cs: compspecs}.

Lemma sizeof_tuchar_arr: forall n, 0 <= n -> sizeof (tarray tuchar n) = n.
Proof. intros n H. simpl. rewrite Z.max_r by lia. lia. Qed.

Lemma byte_val_repr: forall z, 0 <= z < 256 -> byte_val (Vint (Int.repr z)).
Proof. intros z H. exists z. auto. Qed.

Lemma byte_val_zbytes: forall l, bytes_ok l -> Forall byte_val (map (fun b => Vint (Int.repr b)) l).
Proof.
  intros l H. induction H; simpl; constructor; auto.
  apply byte_val_repr. exact H.
Qed.

Lemma byte_val_zbytes_range: forall l, Forall (fun b => 0 <= b <= Byte.max_unsigned) l ->
  Forall byte_val (map (fun b => Vint (Int.repr b)) l).
Proof.
  intros l H. induction H; simpl; constructor; auto.
  apply byte_val_repr. rep_lia.
Qed.

Lemma byte_val_sublist: forall lo hi l, Forall byte_val l -> Forall byte_val (sublist lo hi l).
Proof. intros. apply Forall_sublist. exact H. Qed.

Lemma memcpy_ok_bytes: forall n (l: list val), Zlength l = n -> Forall byte_val l ->
  memcpy_ok (tarray tuchar n) l.
Proof.
  intros n l Hn Hb. exists l. pose proof (Zlength_nonneg l).
  unfold obj_bytes. rewrite sizeof_tuchar_arr by lia.
  split; [lia |]. split; [exact Hb |].
  split; intros; apply derives_refl.
Qed.

Lemma memcpy_ok_zbytes: forall n (l: list Z), Zlength l = n -> bytes_ok l ->
  memcpy_ok (tarray tuchar n) (map (fun b => Vint (Int.repr b)) l).
Proof.
  intros n l Hn Hb. apply memcpy_ok_bytes; [rewrite Zlength_map; exact Hn | apply byte_val_zbytes; exact Hb].
Qed.

Lemma memcpy_ok_zbytes_range: forall n (l: list Z), Zlength l = n ->
  Forall (fun b => 0 <= b <= Byte.max_unsigned) l ->
  memcpy_ok (tarray tuchar n) (map (fun b => Vint (Int.repr b)) l).
Proof.
  intros n l Hn Hb. apply memcpy_ok_bytes; [rewrite Zlength_map; exact Hn | apply byte_val_zbytes_range; exact Hb].
Qed.

Lemma memcpy_ok_uint: forall x, memcpy_ok tuint (Vint x).
Proof.
  intros x. exists (map (fun b => Vint (Int.repr b)) (le_bytes 4 (Int.unsigned x))).
  unfold obj_bytes. change (sizeof tuint) with 4.
  split; [rewrite Zlength_map, Zlength_le_bytes; reflexivity |].
  split; [apply byte_val_zbytes_range, le_bytes_bytes |].
  split; intros sh p Hsh.
  - assert_PROP (field_compatible tuint [] p) as FC by entailer!.
    rewrite <- (tuint_bytes4 sh (Int.unsigned x) p FC). rewrite Int.repr_unsigned. apply derives_refl.
  - intros FC. rewrite <- (tuint_bytes4 sh (Int.unsigned x) p FC). rewrite Int.repr_unsigned. apply derives_refl.
Qed.

(* the typed memcpy is a weakening of the byte loop's specification *)
Lemma memcpy_sub_typed: funspec_sub (snd memcpy_bytes_spec) (snd memcpy_spec).
Proof.
  apply NDsubsume_subsume; [split; reflexivity|].
  split; [split; reflexivity|].
  intros x gargs. destruct x as [[[[shs shd] src] dst] [t v]]. destruct gargs as [g args]. simpl.
  unfold PROPx; simpl. unfold_for_go_lower; simpl. normalize.
  destruct H4 as [l [Hlen [Hdef [Fwd Bwd]]]].
  assert_PROP (field_compatible t nil src /\ field_compatible t nil dst) as FC by entailer!.
  destruct FC as [FCs FCd].
  assert (FCA: forall p, field_compatible t nil p -> field_compatible (tarray tuchar (sizeof t)) nil p).
  { intros p Hp. apply (fc_scalar_bytes t); auto. simpl. apply Z.divide_1_l. }
  Exists (shs, shd, src, dst, l) (@emp mpred _ _).
  rewrite emp_sepcon. simpl. rewrite Hlen.
  apply andp_right.
  - apply andp_right; [apply prop_right; split; [auto | split; [auto | split; [lia | split; auto]]] |].
    apply andp_right; [apply prop_right; reflexivity |].
    apply andp_right; [apply TT_right |].
    rewrite sepcon_emp. apply sepcon_derives; [apply Fwd; auto |].
    rewrite !data_at__memory_block. rewrite sizeof_tuchar_arr by lia. normalize.
    apply andp_right; [apply prop_right; apply FCA; auto | apply derives_refl].
  - apply prop_right; intros rho'. rewrite emp_sepcon. apply andp_left2.
    normalize. apply andp_right; [apply prop_right; auto |].
    apply sepcon_derives.
    + apply Bwd; auto.
    + apply Bwd; auto.
Qed.

End LibcOk.

(* The side condition of a typed memcpy call (LibcSpec.memcpy_spec) of a byte string or a 32-bit scalar:
   0 <= sizeof t <= Int64.max_unsigned /\ memcpy_ok t v. *)
Ltac memcpy_ok_solve :=
  lazymatch goal with
  | |- memcpy_ok tuint _ => apply memcpy_ok_uint
  | |- memcpy_ok (tarray tuchar _) (map _ _) =>
      first [ apply memcpy_ok_zbytes;
                [ try list_solve; try (rewrite ?Zlength_map, ?Zlength_sublist; lia)
                | first [assumption | unfold bytes_ok in *; apply Forall_sublist; assumption] ]
            | apply memcpy_ok_zbytes_range;
                [ try (rewrite ?Zlength_le_bytes; reflexivity); try list_solve | apply le_bytes_bytes ] ]
  | |- memcpy_ok (tarray tuchar _) _ => apply memcpy_ok_bytes; [try list_solve | try assumption]
  end.
Ltac memcpy_side := cbn [projT1 projT2]; split; [simpl; rep_lia | memcpy_ok_solve].
