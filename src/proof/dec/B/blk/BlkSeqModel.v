(* Group BLK of subtree B: plain-Coq counting facts about the model's sequence decoder (model/Block.v),
   needed for the C sequence loops' count invariants (the loop runs nbSeq times, producing nbSeq sequences).
   Independent of VST and of code.v (rebase-proof).  One bundling theorem `blk_seq_model` proves both
   facts; the named corollaries follow by projection. *)
Require Export Zstd.proof.model.Block.
Require Import Zstd.proof.model.Bytes.
Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.micromega.Lia.
Import ListNotations.
Local Open Scope Z_scope.

Definition blk_seq_model : Prop :=
  (forall (k: nat) tLL tOF tML V sLL sOF sML pos l p,
     decode_seqs tLL tOF tML V k sLL sOF sML pos = Some (l, p) -> length l = k)
  /\ (forall tLL tOF tML s nbSeq seqs,
     0 <= nbSeq ->
     decode_seq_stream tLL tOF tML s nbSeq = Some seqs -> Zlength seqs = nbSeq).

Lemma blk_seq_model_ok : blk_seq_model.
Proof.
  assert (H1: forall (k: nat) tLL tOF tML V sLL sOF sML pos l p,
     decode_seqs tLL tOF tML V k sLL sOF sML pos = Some (l, p) -> length l = k).
  { induction k as [|k IH]; intros tLL tOF tML V sLL sOF sML pos l p H; simpl in H.
    - inversion H; reflexivity.
    - repeat match type of H with
             | context [match ?e with None => _ | Some _ => _ end] =>
                 destruct e as [[? ?]|]; [|discriminate]
             end.
      destruct k as [|k'].
      + inversion H; reflexivity.
      + repeat match type of H with
               | context [match ?e with None => _ | Some _ => _ end] =>
                   let E := fresh "E" in
                   destruct e as [[? ?]|] eqn:E; [|discriminate]
               end.
        inversion H; subst; simpl; f_equal; eapply IH; eassumption. }
  split; [exact H1|].
  intros tLL tOF tML s nbSeq seqs Hn H.
  unfold decode_seq_stream in H.
  match type of H with context [if ?b then _ else _] => destruct b; [discriminate|] end.
  repeat match type of H with
         | context [match ?e with None => _ | Some _ => _ end] =>
             let E := fresh "E" in
             destruct e as [[? ?]|] eqn:E; [|discriminate]
         end.
  match type of H with
  | context [match ?z with 0 => _ | _ => _ end] => destruct z; try discriminate
  end.
  inversion H; subst.
  apply H1 in E2. rewrite Zlength_correct, E2. apply Z2Nat.id; exact Hn.
Qed.

(* convenience corollaries (projections of the bundle) *)
Lemma decode_seqs_length (k: nat) tLL tOF tML V sLL sOF sML pos l p :
  decode_seqs tLL tOF tML V k sLL sOF sML pos = Some (l, p) -> length l = k.
Proof. apply (proj1 blk_seq_model_ok). Qed.

Lemma decode_seq_stream_length tLL tOF tML s nbSeq seqs :
  0 <= nbSeq -> decode_seq_stream tLL tOF tML s nbSeq = Some seqs -> Zlength seqs = nbSeq.
Proof. apply (proj2 blk_seq_model_ok). Qed.
