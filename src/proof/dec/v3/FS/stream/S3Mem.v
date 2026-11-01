(* The context's allocator within a call of ZSTD_decompressStream (S3Main.mem_call): the call raises the concrete
   bound on entry as set_ss raises the abstract one (FSRep3.c3_raise), so every return state, built by set_ss and
   setters that keep the allocator, gets FSRep3.mem_rel3 back. *)
Require Export Zstd.proof.dec.v3.FS.stream.S3Main.
Local Open Scope logic.

Section CM_S3Mem_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.

(* on entry: the context of a valid state, raised for the window limit, keeps the call's facts *)
Lemma mem_call_raise (st: dctx_st) (k: cst3) :
  mem_rel3 st k -> mem_call st (c3_raise k (dp_wmax (dc_par st))).
Proof.
  intros H. destruct (mem_rel3_raise st k ss_init H) as (Hm & Hh & Hn).
  unfold mem_call. split; [exact Hm | split; [exact Hh | exact Hn]].
Qed.

Lemma base_call_raise (st: dctx_st) (k: cst3) :
  base_rel3 st k -> base_call st (c3_raise k (dp_wmax (dc_par st))).
Proof.
  intros (H1 & H2 & H3 & H4 & H5 & H6 & _ & _ & Hm).
  unfold base_call. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
  split; [exact H5|]. split; [exact H6|]. apply mem_call_raise; exact Hm.
Qed.

(* on return: a state built by set_ss from the call's state *)
Lemma mem_call_rel3 (st: dctx_st) (k: cst3) (ss: sstate) :
  mem_call st k -> mem_rel3 (set_ss st ss) k.
Proof.
  intros (Hm & Hh & Hn). unfold mem_rel3, set_ss; simpl. split; [exact Hm | split; [exact Hh | exact Hn]].
Qed.

End CM_S3Mem_1.

(* mem_rel3 st' k' for a return state st' built by set_ss from st (and setters that keep the allocator) and a
   context k' that keeps k's allocator fields and local DDict, from mem_call st k *)
Ltac mem_call_tac :=
  match goal with H: mem_call _ _ |- mem_rel3 _ _ =>
    let Hm := fresh "Hm" in let Hh := fresh "Hh" in let Hn := fresh "Hn" in
    pose proof H as (Hm & Hh & Hn); unfold mem_rel3; simpl in Hm, Hh, Hn |- *;
    split; [exact Hm | split; [exact Hh | exact Hn]]
  end.
