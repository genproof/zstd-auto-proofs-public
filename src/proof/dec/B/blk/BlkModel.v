(* Group BLK of subtree B: plain-Coq facts about the model (model/Block.v) that the C-side body proofs
   need, independent of VST and of the C code.v (so immune to contract updates).

   - lz_copy (one match copy, byte by byte): it extends `out` on the right, by exactly `ml` bytes, and the
     j-th new byte is the model's overlap byte; so the output region a sequence writes is determined.
   - exec_seqs (the whole sequence list): it extends `out` on the right, consuming a prefix of the literals.
     These let a loop invariant "op = dst + |out_i|" line up with the model. *)
Require Export Zstd.proof.model.Block.
Require Import Zstd.proof.model.Bytes.
Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.micromega.Lia.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------- lz_copy ---------- *)

(* a match copy only appends to out *)
Lemma lz_copy_app (hist out: list Z) (off: Z) (ml: nat) :
  exists tail, lz_copy hist out off ml = out ++ tail /\ length tail = ml.
Proof.
  revert out. induction ml as [|m IH]; intros out.
  - exists []. rewrite app_nil_r. split; reflexivity.
  - simpl.
    destruct (IH (out ++ [byte_at (hist ++ out) (Zlength hist + Zlength out - off)]))
      as [tl [Htl Hlen]].
    exists (byte_at (hist ++ out) (Zlength hist + Zlength out - off) :: tl).
    rewrite Htl. split.
    + rewrite <- app_assoc. reflexivity.
    + simpl. rewrite Hlen. reflexivity.
Qed.

Lemma lz_copy_length (hist out: list Z) (off: Z) (ml: nat) :
  Zlength (lz_copy hist out off ml) = Zlength out + Z.of_nat ml.
Proof.
  destruct (lz_copy_app hist out off ml) as [tl [H Hl]].
  rewrite H, !Zlength_correct, length_app, Hl. lia.
Qed.

(* a copy of a+b bytes = a bytes then b more from the extended output *)
Lemma lz_copy_add (hist out: list Z) (off: Z) (a b: nat) :
  lz_copy hist out off (a + b) = lz_copy hist (lz_copy hist out off a) off b.
Proof.
  revert out. induction a as [|a IH]; intros out; simpl; [reflexivity|]. apply IH.
Qed.

(* the j-th byte a match copy produces (j < ml): the model's overlap byte at distance off, reading the
   history hist ++ (the bytes produced so far, lz_copy hist out off j) *)
Lemma lz_copy_nth (hist out: list Z) (off: Z) (ml j: nat) :
  (j < ml)%nat ->
  byte_at (lz_copy hist out off ml) (Zlength out + Z.of_nat j) =
  byte_at (hist ++ lz_copy hist out off j) (Zlength hist + Zlength out + Z.of_nat j - off).
Proof.
  intros Hj.
  assert (Hoj: Zlength (lz_copy hist out off j) = Zlength out + Z.of_nat j) by apply lz_copy_length.
  replace ml with (j + (ml - j))%nat by lia.
  rewrite lz_copy_add.
  set (oj := lz_copy hist out off j) in *.
  destruct (ml - j)%nat as [|r] eqn:E; [lia|].
  simpl.
  set (bj := byte_at (hist ++ oj) (Zlength hist + Zlength oj - off)).
  destruct (lz_copy_app hist (oj ++ [bj]) off r) as [tl [Htl _]].
  rewrite Htl, <- app_assoc. simpl.
  (* RHS first: its index equals |hist| + |oj| - off, so it is bj *)
  replace (Zlength hist + Zlength out + Z.of_nat j - off)
    with (Zlength hist + Zlength oj - off) by lia.
  fold bj.
  (* LHS: nth at |oj| of oj ++ bj :: (tl) *)
  unfold byte_at.
  replace (Z.to_nat (Zlength out + Z.of_nat j)) with (length oj).
  2:{ rewrite Zlength_correct in Hoj. lia. }
  rewrite nth_middle. reflexivity.
Qed.

(* ---------- repeat offsets ---------- *)

(* resolve_offset keeps the three repeat offsets >= 1 and returns an offset >= 1 (so a match pointer is
   strictly before op): the loop invariant rep_ok is preserved and matches never have offset 0. *)
Lemma resolve_offset_ok (r1 r2 r3 ll ov off: Z) (rep': Z * Z * Z) :
  1 <= r1 -> 1 <= r2 -> 1 <= r3 ->
  resolve_offset (r1, r2, r3) ll ov = Some (off, rep') ->
  1 <= off /\ (let '(a, b, c) := rep' in 1 <= a /\ 1 <= b /\ 1 <= c).
Proof.
  intros H1 H2 H3 H. unfold resolve_offset in H.
  destruct (ov >? 3) eqn:E.
  - apply Z.gtb_lt in E. inversion H; subst. repeat split; lia.
  - remember (if ll =? 0 then ov + 1 else ov) as idx.
    destruct (idx =? 1); [inversion H; subst; repeat split; lia|].
    destruct (idx =? 2); [inversion H; subst; repeat split; lia|].
    destruct (idx =? 3); [inversion H; subst; repeat split; lia|].
    destruct (r1 - 1 <=? 0) eqn:E4; [discriminate|].
    apply Z.leb_gt in E4. inversion H; subst. repeat split; lia.
Qed.

(* ---------- exec_seqs ---------- *)

(* executing the sequence list only extends out on the right *)
Lemma exec_seqs_app (wsize: Z) (rep: Z * Z * Z) (hist lits out: list Z) (seqs: list sequence)
    (out' lits': list Z) (rep': Z * Z * Z) :
  exec_seqs wsize rep hist lits out seqs = Some (out', lits', rep') ->
  exists mid, out' = out ++ mid.
Proof.
  revert rep lits out. induction seqs as [|sq rest IH]; intros rep lits out H.
  - simpl in H. inversion H; subst. exists []. rewrite app_nil_r; reflexivity.
  - simpl in H.
    destruct (sq_ll sq >? Zlength lits); [discriminate|].
    destruct (resolve_offset rep (sq_ll sq) (sq_ov sq)) as [[offset rep2]|] eqn:E2; [|discriminate].
    destruct (offset >? Zlength hist + Zlength (out ++ firstn (Z.to_nat (sq_ll sq)) lits)); [discriminate|].
    destruct (offset >? wsize + Zlength hist); [discriminate|].
    destruct (IH rep2 (skipn (Z.to_nat (sq_ll sq)) lits)
                (lz_copy hist (out ++ firstn (Z.to_nat (sq_ll sq)) lits) offset (Z.to_nat (sq_ml sq))) H)
      as [mid Hmid].
    destruct (lz_copy_app hist (out ++ firstn (Z.to_nat (sq_ll sq)) lits) offset
                (Z.to_nat (sq_ml sq))) as [tl [Htl _]].
    exists (firstn (Z.to_nat (sq_ll sq)) lits ++ tl ++ mid).
    rewrite Hmid, Htl, <- !app_assoc. reflexivity.
Qed.

(* the literals left are a suffix of the literals given *)
Lemma exec_seqs_lits (wsize: Z) (rep: Z * Z * Z) (hist lits out: list Z) (seqs: list sequence)
    (out' lits': list Z) (rep': Z * Z * Z) :
  exec_seqs wsize rep hist lits out seqs = Some (out', lits', rep') ->
  exists k, lits' = skipn k lits /\ (k <= length lits)%nat.
Proof.
  revert rep lits out. induction seqs as [|sq rest IH]; intros rep lits out H.
  - simpl in H. inversion H; subst. exists 0%nat. split; [reflexivity | lia].
  - simpl in H.
    destruct (sq_ll sq >? Zlength lits) eqn:Ell; [discriminate|].
    destruct (resolve_offset rep (sq_ll sq) (sq_ov sq)) as [[offset rep2]|] eqn:E2; [|discriminate].
    destruct (offset >? Zlength hist + Zlength (out ++ firstn (Z.to_nat (sq_ll sq)) lits)); [discriminate|].
    destruct (offset >? wsize + Zlength hist); [discriminate|].
    destruct (IH rep2 (skipn (Z.to_nat (sq_ll sq)) lits)
                (lz_copy hist (out ++ firstn (Z.to_nat (sq_ll sq)) lits) offset (Z.to_nat (sq_ml sq))) H)
      as [k [Hk Hkle]].
    exists (k + Z.to_nat (sq_ll sq))%nat.
    rewrite Hk, skipn_skipn. split; [reflexivity|].
    rewrite skipn_length in Hkle.
    assert (Z.to_nat (sq_ll sq) <= length lits)%nat.
    { rewrite Z.gtb_ltb in Ell. apply Z.ltb_ge in Ell.
      rewrite Zlength_correct in Ell. lia. }
    lia.
Qed.
