(* FS3 streaming, case zdss_load: the case from the model facts, the error returns (L3VRest) and the obligations of its pieces (LD3). *)
Require Import Zstd.proof.dec.v3.FS.stream.load.L3Stmts Zstd.proof.dec.v3.FS.stream.load.L3VUBuf Zstd.proof.dec.v3.FS.stream.load.L3VRest.
Require Import Zstd.proof.dec.v3.FS.stream.load.L3ContSt Zstd.proof.dec.v3.FS.stream.load.L3ContBuf Zstd.proof.dec.v3.FS.stream.load.L3ErrWhy Zstd.proof.dec.v3.FS.stream.load.L3HistSt Zstd.proof.dec.v3.FS.stream.load.L3HistBuf.

Section CM_L3All_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma LD3_ok : LD3.
Proof.
unfold LD3. exact (conj load_cont_hist_st_ok (conj load_cont_hist_buf_ok (conj load_cont_stable_ok
  (conj load_cont_buf_ok load_err_why_ok)))).
Qed.

Lemma seg_load_all : MF3 -> RET3x -> seg_case_x 3.
Proof. intros M R. exact (seg_load_gen M R LD3_ok). Qed.

End CM_L3All_1.
