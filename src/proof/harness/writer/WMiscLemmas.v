(* Unit-independent lemmas of the writer-internals body group `misc` (WB_misc): ll_code / ml_code (lcode),
   fse_has, fse_predefined (the predefined distributions). *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.harness.writer.model.WModel.

Lemma lcode_hit (base: list Z) (c: nat) (x: Z) : nth c base 0 <= x -> lcode base c x = Z.of_nat c.
Proof.
  destruct c as [|c']; simpl; auto. intros H. destruct (nth (S c') base 0 <=? x) eqn:E; auto. lia.
Qed.

Lemma lcode_step (base: list Z) (c: nat) (x: Z) : (1 <= c)%nat -> x < nth c base 0 ->
  lcode base c x = lcode base (c - 1) x.
Proof.
  destruct c as [|c']; [lia|]. intros _ H. simpl. replace (c' - 0)%nat with c' by lia.
  destruct (nth (S c') base 0 <=? x) eqn:E; auto. lia.
Qed.

Lemma lcode_range (base: list Z) (c: nat) (x: Z) : 0 <= lcode base c x <= Z.of_nat c.
Proof.
  induction c as [|c' IH]; simpl; [lia|]. destruct (nth (S c') base 0 <=? x); lia.
Qed.

(* Znth over a list of values with different (convertible) Inhabitant instances (reptype defaults, the two
   Inhabitant_val of VST): normalize them all to @Znth val Vundef, so that rewriting works *)
Ltac norm_znth :=
  repeat match goal with
  | |- context [@Znth ?A ?d ?i ?l] =>
      tryif constr_eq d Vundef then fail
      else (unify A val; change (@Znth A d i l) with (@Znth val Vundef i l))
  | H: context [@Znth ?A ?d ?i ?l] |- _ =>
      tryif constr_eq d Vundef then fail
      else (unify A val; change (@Znth A d i l) with (@Znth val Vundef i l) in H)
  end.

(* unsigned 64-bit comparisons of in-range values (stall_error) *)
Lemma cmpu_eq_bool (a b: Z) : 0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int64.cmpu Ceq (Int64.repr a) (Int64.repr b) = (a =? b).
Proof.
  intros Ha Hb. simpl. unfold Int64.eq. rewrite !Int64.unsigned_repr by lia.
  destruct (zeq a b), (Z.eqb_spec a b); auto; lia.
Qed.

Lemma cmpu_ne_bool (a b: Z) : 0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int64.cmpu Cne (Int64.repr a) (Int64.repr b) = negb (a =? b).
Proof.
  intros Ha Hb. simpl. unfold Int64.eq. rewrite !Int64.unsigned_repr by lia.
  destruct (zeq a b), (Z.eqb_spec a b); auto; lia.
Qed.

Lemma cmpu_lt_bool (a b: Z) : 0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int64.cmpu Clt (Int64.repr a) (Int64.repr b) = (a <? b).
Proof.
  intros Ha Hb. simpl. unfold Int64.ltu. rewrite !Int64.unsigned_repr by lia.
  destruct (zlt a b), (Z.ltb_spec a b); auto; lia.
Qed.
