(* FS3 streaming: the model facts MF3 (S3ModelStmts, revision R1: dictionary
   window rule, history H, lenient shortcut claims).  The proofs of R0 are in model/M3*.v
   (on the v2 template src/proof/dec/FS/StreamModelFacts.v).
   R1: modelw/MW3*.v, the R0 proofs on the strict stream model (dw), MW3Hist (B's history H). *)
Require Import Zstd.proof.dec.v3.FS.stream.S3ModelStmts.
Require Import Zstd.proof.dec.v3.FS.stream.modelw.MW3Series Zstd.proof.dec.v3.FS.stream.modelw.MW3Hdr Zstd.proof.dec.v3.FS.stream.modelw.MW3Unit.

Lemma MF3_of : P_shortcut_ok -> MF3.
Proof.
  intros Hok.
  destruct M3_hdr as [H1 [H2 [H3 [H4 [H5 H6]]]]].
  destruct M3_unit as [U1 [U2 [U3 U4]]].
  exact (conj m3_frames_done_app (conj m3_dead_of_fdead (conj m3_bad_of_fbad (conj m3_dead_app (conj m3_fdead_app
    (conj m3_fbad_app (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj U1 (conj U2 (conj U3 (conj U4
    (conj m3_cur_complete (conj Hok (conj m3_shortcut_unk (conj m3_shortcut_det
    (conj m3_shortcut_capacity (conj m3_shortcut_sel m3_shortcut_sel_ref)))))))))))))))))))))).
Qed.

Lemma MF3_ok : MF3.
Proof. apply MF3_of. exact m3_shortcut_ok_b. Qed.
