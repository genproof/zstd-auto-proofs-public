(* Cutting a function body (a right-nested Ssequence) into segments proved separately.

   sq_drop n s = s without its first n statements; sq_with n s k = the first n statements of s,
   followed by the statement k.  A segment lemma of statements a..a+n-1 of the body reads
     forall K R, semax Delta Q K R -> semax Delta P (sq_with n (sq_drop a body) K) R
   (continuation style: no inversion of semax is needed to chain segments).  For a closed body,
   sq_drop a body and sq_with n (sq_drop a body) (sq_drop (a + n) body) are convertible. *)
Require Import VST.floyd.proofauto.

Fixpoint sq_drop (n: nat) (s: statement) : statement :=
  match n with
  | O => s
  | S n' => match s with Ssequence _ b => sq_drop n' b | _ => Sskip end
  end.

Fixpoint sq_with (n: nat) (s: statement) (k: statement) : statement :=
  match n with
  | O => k
  | S n' => match s with Ssequence a b => Ssequence a (sq_with n' b k) | _ => Ssequence s k end
  end.

(* the number of statements of a right-nested sequence *)
Fixpoint sq_len (s: statement) : nat :=
  match s with Ssequence _ b => S (sq_len b) | _ => 1%nat end.
