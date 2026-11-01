(* Plain-Coq facts of phase C of segment E of w_compressed_block: the
   sequences section the C has written (header + bitstream) is a seqsec_ok section. *)
Require Import VST.zlist.sublist.
Require Import Zstd.proof.harness.writer.model.WM_BlkDefs.
Require Import Zstd.proof.harness.writer.WBlkE_C_SibHdr.
Require Import Zstd.proof.harness.writer.WBlkE_C_SibStream.

Lemma blkEC_seqsec : forall (prev: option (wfse * wfse * wfse)) f seqs m0 m1 m2 F0 F1 F2 s0 s1 s2,
  1 <= Zlength seqs -> nseq_form_ok f (Zlength seqs) -> Forall seq_ok seqs ->
  mode_ok 0 m0 (option_map wtabs_ll prev) F0 ->
  mode_ok 1 m1 (option_map wtabs_of prev) F1 ->
  mode_ok 2 m2 (option_map wtabs_ml prev) F2 ->
  wf_ok F0 -> wf_ok F1 -> wf_ok F2 ->
  fse_chain (wf_table F0) (map (sq_code 0) seqs) s0 ->
  fse_chain (wf_table F1) (map (sq_code 1) seqs) s1 ->
  fse_chain (wf_table F2) (map (sq_code 2) seqs) s2 ->
  bytes_ok (seq_hdr_bytes f (Zlength seqs) m0 m1 m2 F0 F1 F2 ++
            fields_mark (seq_fields (wf_table F0) (wf_table F1) (wf_table F2) s0 s1 s2 seqs)) ->
  seqsec_ok (option_map (fun '(a, b, c) => (wf_table a, wf_table b, wf_table c)) prev) seqs
    (Some (wf_table F0, wf_table F1, wf_table F2))
    (seq_hdr_bytes f (Zlength seqs) m0 m1 m2 F0 F1 F2 ++
     fields_mark (seq_fields (wf_table F0) (wf_table F1) (wf_table F2) s0 s1 s2 seqs)).
Proof.
  intros prev f seqs m0 m1 m2 F0 F1 F2 s0 s1 s2 Hn Hf Hsq Hm0 Hm1 Hm2 Hw0 Hw1 Hw2 Hc0 Hc1 Hc2 Hb.
  split; [exact Hb |]. split.
  { rewrite Zlength_app. unfold seq_hdr_bytes. rewrite !Zlength_app, Zlength_cons, Zlength_nil.
    pose proof (Zlength_nonneg (fields_mark (seq_fields (wf_table F0) (wf_table F1) (wf_table F2) s0 s1 s2 seqs))).
    pose proof (Zlength_nonneg (nseq_bytes f (Zlength seqs))).
    pose proof (Zlength_nonneg (wtab_desc m0 F0)). pose proof (Zlength_nonneg (wtab_desc m1 F1)).
    pose proof (Zlength_nonneg (wtab_desc m2 F2)). lia. }
  exists (Zlength (seq_hdr_bytes f (Zlength seqs) m0 m1 m2 F0 F1 F2)).
  split; [apply seq_hdr_ok; auto |].
  right. exists (wf_table F0), (wf_table F1), (wf_table F2). split; [reflexivity |].
  rewrite Zlength_correct, Nat2Z.id, skipn_app, skipn_all, Nat.sub_diag. simpl.
  apply seq_stream_ok; auto.
Qed.

Lemma blkEC_wt_ok : forall S F0 F1 F2,
  wt_ok S -> wf_ok F0 -> wf_ok F1 -> wf_ok F2 -> wt_ok (set_tabs S (F0, F1, F2)).
Proof.
  intros S F0 F1 F2 (Hr & Hh & _) H0 H1 H2. split; [exact Hr |]. split; [exact Hh |].
  intros a b c Heq. cbn in Heq. inversion Heq; subst. auto.
Qed.
