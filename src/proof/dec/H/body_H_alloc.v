(* Subtree H: the allocation helpers (allocator {NULL,NULL,NULL}), startingInputLength, DStreamOutSize.  Prove each body against H_G (HSpecs.v); helper lemmas go above. *)
Require Import Zstd.proof.dec.H.HLemmas.
Local Open Scope logic.

Lemma body_ZSTD_startingInputLength :
  semax_body Vprog H_G f_ZSTD_startingInputLength ZSTD_startingInputLength_spec.
Proof.
  start_function.
  forward_if (temp _t'1 (Vint (Int.repr 5))).
  - forward. entailer!.
  - contradiction.
  - forward. forward.
Qed.

Lemma body_ZSTD_DStreamOutSize :
  semax_body Vprog H_G f_ZSTD_DStreamOutSize ZSTD_DStreamOutSize_spec.
Proof.
  start_function.
  forward.
Qed.

Lemma body_ZSTD_customMem_copy :
  semax_body Vprog H_G f_ZSTD_customMem_copy ZSTD_customMem_copy_spec.
Proof.
  start_function.
  unfold cmem_null.
  forward. forward. forward. forward. forward. forward.
  entailer!.
Qed.

Lemma body_ZSTD_customMallocP :
  semax_body Vprog H_G f_ZSTD_customMallocP ZSTD_customMallocP_spec.
Proof.
  start_function.
  unfold cmem_null.
  forward.
  forward_if (PROP () LOCAL (temp _size (Vlong (Int64.repr (sizeof t))); temp _customMem pm; gvars gv)
    SEP (mem_mgr gv; data_at shm t_cmem (nullval, (nullval, nullval)) pm)).
  - contradiction.
  - forward. entailer!.
  - forward_call (t, gv).
    Intros q.
    forward.
    Exists q.
    destruct (eq_dec q nullval).
    + subst. entailer!.
    + entailer!.
Qed.

Lemma body_ZSTD_customCallocP :
  semax_body Vprog H_G f_ZSTD_customCallocP ZSTD_customCallocP_spec.
Proof.
  start_function.
  unfold cmem_null.
  forward.
  forward_if (PROP () LOCAL (temp _size (Vlong (Int64.repr n)); temp _customMem pm; gvars gv)
    SEP (mem_mgr gv; data_at shm t_cmem (nullval, (nullval, nullval)) pm)).
  - contradiction.
  - forward. entailer!.
  - forward_call (1, n, gv).
    Intros q.
    forward.
    Exists q.
    entailer!.
Qed.

Lemma body_ZSTD_customFreeP :
  semax_body Vprog H_G f_ZSTD_customFreeP ZSTD_customFreeP_spec.
Proof.
  start_function.
  unfold cmem_null.
  destruct (eq_dec q nullval).
  - subst q.
    forward_if.
    + first [contradiction | discriminate].
    + forward. entailer!.
  - Intros.
    forward_if.
    + forward.
      forward_if.
      * first [contradiction | discriminate].
      * forward_call (t, q, gv).
        { rewrite if_false by auto. cancel. }
        entailer!.
    + first [contradiction | discriminate].
Qed.

Lemma bodies_H_alloc :
  semax_body Vprog H_G f_ZSTD_customMallocP ZSTD_customMallocP_spec /\
  semax_body Vprog H_G f_ZSTD_customCallocP ZSTD_customCallocP_spec /\
  semax_body Vprog H_G f_ZSTD_customFreeP ZSTD_customFreeP_spec /\
  semax_body Vprog H_G f_ZSTD_customMem_copy ZSTD_customMem_copy_spec /\
  semax_body Vprog H_G f_ZSTD_startingInputLength ZSTD_startingInputLength_spec /\
  semax_body Vprog H_G f_ZSTD_DStreamOutSize ZSTD_DStreamOutSize_spec.
Proof.
  split. apply body_ZSTD_customMallocP.
  split. apply body_ZSTD_customCallocP.
  split. apply body_ZSTD_customFreeP.
  split. apply body_ZSTD_customMem_copy.
  split. apply body_ZSTD_startingInputLength.
  apply body_ZSTD_DStreamOutSize.
Qed.
