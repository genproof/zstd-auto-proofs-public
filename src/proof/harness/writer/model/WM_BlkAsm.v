(* w_compressed_block, the whole body (plain Coq): a literals section and a sequences section decode (decode_block) to
   the
   content the sequences execute to. *)
Require Import Zstd.proof.harness.writer.model.WM_BlkDefs.

Theorem decode_block_ok : forall st hist out lb sb bsm wsize lits seqs hnew tabs cont trail rep',
  lit_ok (st_huf st) bsm lits hnew lb ->
  seqsec_ok (st_seq st) seqs tabs sb ->
  exec_seqs wsize (st_rep st) hist lits out seqs = Some (out ++ cont, trail, rep') ->
  Zlength (lb ++ sb) <= bsm -> Zlength (cont ++ trail) <= bsm ->
  decode_block st hist out (lb ++ sb) bsm wsize =
    Some ({| st_huf := hnew; st_seq := tabs; st_rep := rep' |}, cont ++ trail).
Proof.
  intros st hist out lb sb bsm wsize lits seqs hnew tabs cont trail rep' Hlit Hseq Hex Hlen Hc.
  destruct Hseq as [_ [Hsb [hused [Hhdr Hstr]]]].
  destruct Hlit as [_ Hlit].
  specialize (Hlit sb Hsb).
  unfold decode_block.
  destruct (Zlength (lb ++ sb) >? bsm) eqn:E1; [apply Z.gtb_lt in E1; lia |].
  rewrite Hlit.
  rewrite Zlength_correct, Nat2Z.id, skipn_app, skipn_all, Nat.sub_diag, skipn_O; simpl app.
  rewrite Hhdr.
  assert (Hs: (if Zlength seqs =? 0 then Some nil else
     match tabs with
     | Some (tLL, tOF, tML) => decode_seq_stream tLL tOF tML (skipn (Z.to_nat hused) sb) (Zlength seqs)
     | None => None
     end) = Some seqs).
  { destruct Hstr as [-> | [tLL [tOF [tML [-> Hd]]]]]; [reflexivity |].
    destruct (Zlength seqs =? 0) eqn:E2; [| exact Hd].
    apply Z.eqb_eq, Zlength_nil_inv in E2; subst; reflexivity. }
  rewrite Hs, Hex.
  rewrite <- app_assoc, skipn_app, skipn_all, Nat.sub_diag, skipn_O; simpl app.
  destruct (Zlength (cont ++ trail) >? bsm) eqn:E3; [apply Z.gtb_lt in E3; lia |].
  reflexivity.
Qed.
