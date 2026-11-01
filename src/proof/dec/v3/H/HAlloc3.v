(* The allocation helpers for any allocator (the res_ laws): ZSTD_customCallocP, ZSTD_customFreeP and
   ZSTD_customMem_copy with the ZSTD_customMem of the default allocator ({ NULL, NULL, NULL }: calloc, free) or of
   a context's own allocator (CMem.cmem: customAlloc / customFree called through their pointers, with the law's
   cm_alloc_spec / cm_free_spec).  For the default allocator they are DecIface's specifications (which follow by
   funspec_sub; the decoder's proofs that only use the default allocator keep those). *)
Require Export Zstd.proof.zstd.CMem.
Local Open Scope logic.

Definition t_cmem3 : type := Tstruct ___gp_ZSTD_customMem noattr.

Section HAlloc.
Context {CMI: cmem_preds}.

(* calloc of n bytes through the allocator am, which has given out h bytes.  With a context's own allocator, n > 0:
   the code compares the block customAlloc returns with NULL, which CompCert defines only for a pointer that is
   (weakly) valid, and a block of 0 bytes gives no valid pointer (zstd allocates a context or a non-empty stream
   buffer).  cmem_ok: the code loads the opaque field and passes it on, which needs a defined pointer. *)
Definition ZSTD_customCallocP_cm_spec : ident * funspec :=
  DECLARE _ZSTD_customCallocP
  WITH gv: globals, n: Z, shm: share, pm: val, am: option cmem, h: Z
  PRE [ tulong, tptr t_cmem3 ]
    PROP (readable_share shm; 0 <= n <= Ptrofs.max_unsigned; cm_room am h n; am <> None -> 0 < n; cmem_ok am)
    PARAMS (Vlong (Int64.repr n); pm) GLOBALS (gv)
    SEP (mem_mgr gv; data_at shm t_cmem3 (cmem_v am) pm; cm_have am h)
  POST [ tptr tvoid ]
    EX q: val,
    PROP (is_pointer_or_null q; q <> nullval -> malloc_compatible n q)
    RETURN (q)
    SEP (mem_mgr gv; data_at shm t_cmem3 (cmem_v am) pm;
         if eq_dec q nullval then cm_have am h
         else cm_have am (h + n) * blk_tok am (tarray tuchar n) q *
              data_at Ews (tarray tuchar n) (Zrepeat (Vint Int.zero) n) q).

(* malloc of an object of type t (the caller chooses t, as with malloc_spec') through the allocator am, which has
   given out h bytes: the default one (malloc's typed token) or a context's own (customAlloc, the DDict and its copy,
   the DDict hash set) *)
Definition ZSTD_customMallocP_cm_spec : ident * funspec :=
  DECLARE _ZSTD_customMallocP
  WITH gv: globals, t: type, shm: share, pm: val, am: option cmem, h: Z
  PRE [ tulong, tptr t_cmem3 ]
    PROP (readable_share shm; 0 <= sizeof t <= Ptrofs.max_unsigned;
          complete_legal_cosu_type t = true; natural_aligned natural_alignment t = true;
          cm_room am h (sizeof t); cmem_ok am)
    PARAMS (Vlong (Int64.repr (sizeof t)); pm) GLOBALS (gv)
    SEP (mem_mgr gv; data_at shm t_cmem3 (cmem_v am) pm; cm_have am h)
  POST [ tptr tvoid ]
    EX q: val,
    PROP (is_pointer_or_null q)
    RETURN (q)
    SEP (mem_mgr gv; data_at shm t_cmem3 (cmem_v am) pm;
         if eq_dec q nullval then cm_have am h
         else cm_have am (h + sizeof t) * blk_tok am t q * data_at_ Ews t q).

(* free of an object of type t (NULL: nothing) through the allocator am, which has given out h bytes; with a
   context's own allocator the object is not empty (the comparison with NULL needs a valid pointer, as above) *)
Definition ZSTD_customFreeP_cm_spec : ident * funspec :=
  DECLARE _ZSTD_customFreeP
  WITH gv: globals, t: type, q: val, shm: share, pm: val, am: option cmem, h: Z
  PRE [ tptr tvoid, tptr t_cmem3 ]
    PROP (readable_share shm; q <> nullval -> cm_held am h t; q <> nullval -> am <> None -> 0 < sizeof t;
          cmem_ok am)
    PARAMS (q; pm) GLOBALS (gv)
    SEP (mem_mgr gv; data_at shm t_cmem3 (cmem_v am) pm; cm_have am h;
         if eq_dec q nullval then emp else blk_tok am t q * data_at_ Ews t q)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (mem_mgr gv; data_at shm t_cmem3 (cmem_v am) pm;
         cm_have am (if eq_dec q nullval then h else h - sizeof t)).

(* the field-by-field copy of any allocator *)
Definition ZSTD_customMem_copy_cm_spec : ident * funspec :=
  DECLARE _ZSTD_customMem_copy
  WITH shd: share, pd: val, shs: share, ps: val, am: option cmem
  PRE [ tptr t_cmem3, tptr t_cmem3 ]
    PROP (writable_share shd; readable_share shs; cmem_ok am)
    PARAMS (pd; ps)
    SEP (data_at_ shd t_cmem3 pd; data_at shs t_cmem3 (cmem_v am) ps)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at shd t_cmem3 (cmem_v am) pd; data_at shs t_cmem3 (cmem_v am) ps).

Lemma body_ZSTD_customCallocP_cm :
  semax_body Vprog Gprog f_ZSTD_customCallocP ZSTD_customCallocP_cm_spec.
Proof.
  start_function.
  destruct am as [m|]; unfold cmem_v, cm_have in *; unfold cm_room, cmem_ok in *.
  - unfold cmem_val, cm_funs. Intros. destruct H2 as [? [? ?]].
    assert (0 < n) by (apply H1; discriminate).
    forward.
    forward_if.
    + forward. forward.
      forward_call (cm_opaque m, cm_bound m, h, n).
      Intros p. forward.
      destruct (eq_dec p nullval).
      * subst p. forward_if; [|contradiction].
        forward. Exists nullval. entailer!.
        rewrite if_true by auto. unfold cm_funs. cancel.
      * Intros. forward_if; [contradiction|].
        destruct H7 as [?|Hmc]; [contradiction|].
        forward_call (Ews, p, 0, n).
        forward. Exists p. entailer!.
        rewrite if_false by auto. unfold cm_funs, blk_tok.
        replace (sizeof (tarray tuchar n)) with n by (simpl; lia).
        cancel.
    + assert_PROP (isptr (cm_alloc m)) by entailer!.
      destruct m as [ca cf co cb]; simpl in *; subst ca; contradiction.
  - forward.
    forward_if (PROP () LOCAL (temp _size (Vlong (Int64.repr n)); temp _customMem pm; gvars gv)
      SEP (mem_mgr gv; data_at shm t_cmem3 (nullval, (nullval, nullval)) pm; emp)).
    + contradiction.
    + forward. entailer!.
    + forward_call (1, n, gv).
      Intros q.
      forward.
      Exists q.
      destruct (eq_dec q nullval).
      * entailer!. all: try (intros C; contradiction).
      * sep_apply (malloc_token_local_facts Ews (tarray tuchar n) q). Intros.
        replace (sizeof (tarray tuchar n)) with n in * by (simpl; lia).
        entailer!.
Qed.

Lemma body_ZSTD_customMallocP_cm :
  semax_body Vprog Gprog f_ZSTD_customMallocP ZSTD_customMallocP_cm_spec.
Proof.
  start_function.
  destruct am as [m|]; unfold cmem_v, cm_have in *; unfold cm_room, cmem_ok in *.
  - unfold cmem_val, cm_funs. Intros. destruct H3 as [? [? ?]].
    forward.
    forward_if.
    + forward. forward.
      forward_call (cm_opaque m, cm_bound m, h, sizeof t).
      Intros p.
      forward.
      Exists p.
      destruct (eq_dec p nullval).
      * subst p. entailer!. unfold cm_funs. cancel.
      * destruct H7 as [?|Hmc]; [contradiction|].
        entailer!.
        unfold cmem_val, cm_funs, blk_tok. cancel.
        rewrite memory_block_data_at_; [cancel | apply malloc_compatible_field_compatible; auto].
    + assert_PROP (isptr (cm_alloc m)) by entailer!.
      destruct m as [ca cf co cb]; simpl in *; subst ca; contradiction.
  - forward.
    forward_if (PROP () LOCAL (temp _size (Vlong (Int64.repr (sizeof t))); temp _customMem pm; gvars gv)
      SEP (mem_mgr gv; data_at shm t_cmem3 (nullval, (nullval, nullval)) pm; emp)).
    + contradiction.
    + forward. entailer!.
    + forward_call (t, gv).
      Intros q.
      forward.
      Exists q.
      destruct (eq_dec q nullval).
      * entailer!.
      * unfold blk_tok. entailer!.
Qed.

Lemma body_ZSTD_customFreeP_cm :
  semax_body Vprog Gprog f_ZSTD_customFreeP ZSTD_customFreeP_cm_spec.
Proof.
  start_function.
  destruct am as [m|]; unfold cmem_v, cm_have in *; unfold cm_held, cmem_ok in *.
  - unfold cmem_val, cm_funs. Intros. destruct H1 as [? [? ?]].
    destruct (eq_dec q nullval).
    + subst q. forward_if.
      * first [contradiction | discriminate].
      * forward. entailer!. unfold cm_funs. cancel.
    + Intros.
      assert (0 < sizeof t) by (apply H0; auto; discriminate).
      specialize (H n).
      rewrite data_at__memory_block. Intros.
      forward_if; [|contradiction].
      forward.
      forward_if.
      * forward. forward. unfold blk_tok.
        forward_call (cm_opaque m, cm_bound m, h, q, sizeof t).
        entailer!. unfold cmem_val, cm_funs. cancel.
      * assert_PROP (isptr (cm_free m)) by entailer!.
        destruct m as [ca cf co cb]; simpl in *; subst cf; contradiction.
  - unfold blk_tok. destruct (eq_dec q nullval).
    + subst q.
      forward_if.
      * first [contradiction | discriminate].
      * forward. entailer!.
    + Intros.
      forward_if.
      * forward.
        forward_if.
        -- first [contradiction | discriminate].
        -- forward_call (t, q, gv).
           { rewrite if_false by auto. cancel. }
           entailer!.
      * first [contradiction | discriminate].
Qed.

Lemma body_ZSTD_customMem_copy_cm :
  semax_body Vprog Gprog f_ZSTD_customMem_copy ZSTD_customMem_copy_cm_spec.
Proof.
  start_function.
  destruct am as [m|]; unfold cmem_v in *.
  - unfold cmem_val. destruct H as [? [? ?]].
    forward. forward. forward. forward. forward. forward.
    entailer!.
  - forward. forward. forward. forward. forward. forward.
    entailer!.
Qed.

(* all of the above *)
Lemma halloc3_done :
  semax_body Vprog Gprog f_ZSTD_customMallocP ZSTD_customMallocP_cm_spec /\
  semax_body Vprog Gprog f_ZSTD_customCallocP ZSTD_customCallocP_cm_spec /\
  semax_body Vprog Gprog f_ZSTD_customFreeP ZSTD_customFreeP_cm_spec /\
  semax_body Vprog Gprog f_ZSTD_customMem_copy ZSTD_customMem_copy_cm_spec.
Proof.
  exact (conj body_ZSTD_customMallocP_cm
           (conj body_ZSTD_customCallocP_cm (conj body_ZSTD_customFreeP_cm body_ZSTD_customMem_copy_cm))).
Qed.

End HAlloc.
