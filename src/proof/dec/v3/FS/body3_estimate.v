(* The memory estimates of zstd.h (the res_memory laws): ZSTD_estimateDCtxSize (sizeof(ZSTD_DCtx)),
   ZSTD_decodingBufferSize_min and ZSTD_estimateDStreamSize (the context, one block of input, the output buffer
   for an unknown content size), against CMem's specifications.  Each body is proved against the list of the
   specifications it calls (G_est), then lifted to the decoder's context FS3_G (FSOblig3.FS3_body). *)
Require Import Zstd.proof.dec.v3.FS.FSOblig3.
Require Export Zstd.proof.zstd.CMem.
Local Open Scope logic.

Section CM_body3_estimate_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* ZSTD_decodingBufferSize_min_spec: FSSpecs3 *)
Definition G_est : funspecs :=
  [ ZSTD_decodingBufferSize_internal_spec; ZSTD_decodingBufferSize_min_spec; ZSTD_estimateDCtxSize_spec ].

Lemma body_ZSTD_estimateDCtxSize :
  semax_body Vprog G_est f_ZSTD_estimateDCtxSize ZSTD_estimateDCtxSize_spec.
Proof.
  start_function.
  forward.
Qed.

Lemma body_ZSTD_decodingBufferSize_min :
  semax_body Vprog G_est f_ZSTD_decodingBufferSize_min ZSTD_decodingBufferSize_min_spec.
Proof.
  start_function.
  forward_call (ws, fcs, ZSTD_BLOCKSIZE_MAX).
  { unfold ZSTD_BLOCKSIZE_MAX; rep_lia. }
  forward.
  entailer!.
  rewrite (Z.min_l (Z.min ws ZSTD_BLOCKSIZE_MAX) ZSTD_BLOCKSIZE_MAX) by lia.
  reflexivity.
Qed.

Lemma body_ZSTD_estimateDStreamSize :
  semax_body Vprog G_est f_ZSTD_estimateDStreamSize ZSTD_estimateDStreamSize_spec.
Proof.
  start_function.
  forward_if (temp _t'1 (Vlong (Int64.repr (Z.min w ZSTD_BLOCKSIZE_MAX)))).
  - forward. entailer!.
    rewrite Z.min_l; [reflexivity |].
    change (Int.signed (Int.shl (Int.repr 1) (Int.repr 17))) with 131072 in H0.
    unfold Int64.ltu in H0. rewrite !Int64.unsigned_repr in H0 by rep_lia.
    destruct (zlt w 131072); [unfold ZSTD_BLOCKSIZE_MAX; lia | discriminate].
  - forward. entailer!.
    rewrite Z.min_r; [reflexivity |].
    change (Int.signed (Int.shl (Int.repr 1) (Int.repr 17))) with 131072 in H0.
    unfold Int64.ltu in H0. rewrite !Int64.unsigned_repr in H0 by rep_lia.
    destruct (zlt w 131072); [discriminate | unfold ZSTD_BLOCKSIZE_MAX; lia].
  - forward. forward.
    forward_call (w, Int64.max_unsigned).
    { entailer!. cbn. do 3 f_equal. apply Int64.eqm_samerepr. exists (-1). reflexivity. }
    forward_call tt.
    forward.
    entailer!.
    unfold dstream_size, WILDCOPY_OVERLENGTH.
    pose proof (Z.le_min_l w ZSTD_BLOCKSIZE_MAX). pose proof (Z.le_min_r w ZSTD_BLOCKSIZE_MAX).
    rewrite (Z.min_r Int64.max_unsigned) by (unfold ZSTD_BLOCKSIZE_MAX in *; rep_lia).
    do 2 f_equal. lia.
Qed.

(* all three *)
Lemma estimate3_done :
  semax_body Vprog G_est f_ZSTD_estimateDCtxSize ZSTD_estimateDCtxSize_spec /\
  semax_body Vprog G_est f_ZSTD_decodingBufferSize_min ZSTD_decodingBufferSize_min_spec /\
  semax_body Vprog G_est f_ZSTD_estimateDStreamSize ZSTD_estimateDStreamSize_spec.
Proof.
  split; [apply body_ZSTD_estimateDCtxSize | split; [apply body_ZSTD_decodingBufferSize_min | apply body_ZSTD_estimateDStreamSize]].
Qed.

(* ---------- the three bodies in the decoder's context (G_est is part of FS3_G: Layer.body_ok_mono) ---------- *)

Lemma est3_nodup DENT TABS SR BR : NoDup (map fst Vprog ++ map fst (FS3_G DENT TABS SR BR)).
Proof. apply list_norepet_NoDup. apply compute_list_norepet_e. vm_compute. reflexivity. Qed.

Lemma est3_incl DENT TABS SR BR : incl G_est (FS3_G DENT TABS SR BR).
Proof.
  assert (HG: Forall (fun x => initial_world.find_id (fst x) (FS3_G DENT TABS SR BR) = Some (snd x)) G_est)
    by (repeat constructor; reflexivity).
  intros [i phi] Hx. rewrite Forall_forall in HG. apply initial_world.find_id_e. exact (HG _ Hx).
Qed.

Lemma body_estimateDCtxSize3 : FS3_body (fun DENT TABS SR BR => ZSTD_estimateDCtxSize_spec).
Proof.
  intros DENT TABS SR BR _ _. apply (body_ok_mono G_est); [ | apply est3_incl | apply est3_nodup].
  exists f_ZSTD_estimateDCtxSize; split; [reflexivity | split; [reflexivity | apply body_ZSTD_estimateDCtxSize]].
Qed.

Lemma body_decodingBufferSize_min3 : FS3_body (fun DENT TABS SR BR => ZSTD_decodingBufferSize_min_spec).
Proof.
  intros DENT TABS SR BR _ _. apply (body_ok_mono G_est); [ | apply est3_incl | apply est3_nodup].
  exists f_ZSTD_decodingBufferSize_min;
    split; [reflexivity | split; [reflexivity | apply body_ZSTD_decodingBufferSize_min]].
Qed.

Lemma body_estimateDStreamSize3 : FS3_body (fun DENT TABS SR BR => ZSTD_estimateDStreamSize_spec).
Proof.
  intros DENT TABS SR BR _ _. apply (body_ok_mono G_est); [ | apply est3_incl | apply est3_nodup].
  exists f_ZSTD_estimateDStreamSize;
    split; [reflexivity | split; [reflexivity | apply body_ZSTD_estimateDStreamSize]].
Qed.

End CM_body3_estimate_1.
