(* FS3-bl stages 3/4, compressed block: D13, the frame's output so far (as the model has it) is bytes:
   the block decoder's correctness clause (block_ok) needs it of its hc_out, and hist_def needs the output cells
   [f0, opos) to be bytes.  bl_mrel gives it. *)
Require Export Zstd.proof.dec.v3.FS.BL.body.s34.S34Defs.

Section CM_CompD13_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma comp_d13 md ba fs ts v :
  bl_mrel md ba fs ts v -> forall b, ba_st ba = Some b -> bytes_ok (bs_out b).
Proof. intros Hm b Hb. destruct (Hm b Hb) as (_ & _ & _ & _ & Hby & _). exact Hby. Qed.

End CM_CompD13_1.
