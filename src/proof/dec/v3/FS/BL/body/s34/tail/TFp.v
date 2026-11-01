(* FS3-bl BODY, stages 3/4, the tail: fp_ok of the frame fields the tail builds (fParams is never written). *)
Require Export Zstd.proof.dec.v3.FS.BL.body.s34.tail.TDefs.

Section CM_TFp_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.

Lemma t34_fp_fsm fs ob osz opos pcs c e' cold :
  fp_ok (fs_fParams fs) -> fp_ok (fs_fParams (t34_fsm fs ob osz opos pcs c e' cold)).
Proof. unfold t34_fsm, bl_fs1, continuity. destruct (cont_moves _ _ _); cbn; auto. Qed.

Lemma t34_fp_fsB fsx ds r x ob opos :
  fp_ok (fs_fParams fsx) -> fp_ok (fs_fParams (t34_fsB fsx ds r x ob opos)).
Proof. auto. Qed.

Lemma t34_fp_fsE fsx stg e :
  fp_ok (fs_fParams fsx) -> fp_ok (fs_fParams (t34_fsE fsx stg e)).
Proof. auto. Qed.

End CM_TFp_1.

(* fp_ok of a tail state from s34_tail_spec's premise *)
Ltac t34_fp H := repeat first [ apply t34_fp_fsE | apply t34_fp_fsB | apply t34_fp_fsm ]; exact H.

