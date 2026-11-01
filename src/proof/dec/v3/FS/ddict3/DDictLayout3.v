(* FS3 ddict3: the layout of ZSTD_DDict_s (offsets 0, 8, 16, 24, 27316, 27320, pad 27324, cMem 27328; size 27352)
   as memory blocks: split/merge of the struct without unfolding its (huge) representation type. *)
Require Import Zstd.proof.dec.v3.FS.FSOblig3.
Local Open Scope logic.

Section CM_DDictLayout3_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma mb_split_at (sh: share) (n m k: Z) (q: val) :
  isptr q -> 0 <= n -> 0 <= m -> 0 <= k ->
  (match q with Vptr _ o => Ptrofs.unsigned o + k + n + m < Ptrofs.modulus | _ => True end) ->
  memory_block sh (n + m) (offset_val k q) =
  memory_block sh n (offset_val k q) * memory_block sh m (offset_val (k + n) q).
Proof.
  intros Hp Hn Hm Hk Hq.
  destruct q; try contradiction.
  simpl offset_val.
  pose proof (Ptrofs.unsigned_range i).
  rewrite <- (Ptrofs.repr_unsigned i).
  rewrite !ptrofs_add_repr.
  rewrite (memory_block_split sh b (Ptrofs.unsigned i + k) n m) by lia.
  rewrite Z.add_assoc. reflexivity.
Qed.

Section L.
Let t := Tstruct _ZSTD_DDict_s noattr.

Lemma ddict_fc_field (f: ident) (q: val) :
  in_members f (co_members (get_co _ZSTD_DDict_s)) -> field_compatible t [] q -> field_compatible t (DOT f) q.
Proof. intros Hi Hfc. apply field_compatible_cons. split; [exact Hi | exact Hfc]. Qed.

Lemma ddict_fa_mb (f: ident) (n ofs: Z) (q: val) :
  field_compatible t (DOT f) q -> sizeof (nested_field_type t (DOT f)) = n -> nested_field_offset t (DOT f) = ofs ->
  field_at_ Ews t (DOT f) q = memory_block Ews n (offset_val ofs q).
Proof.
  intros Hfc Hn Ho. rewrite field_at__memory_block, field_compatible_field_address by exact Hfc.
  rewrite Hn, Ho. reflexivity.
Qed.

Lemma ddict_fc_root (f: ident) (q: val) : field_compatible t (DOT f) q -> field_compatible t [] q.
Proof. intros H. apply field_compatible_cons in H. simpl in H. destruct H; auto. Qed.

Ltac dd_side := first [ reflexivity | apply ddict_fc_field; [ unfold in_members; simpl; auto 10 | assumption ] ].

Lemma ddict_pieces_eq (q: val) :
  field_compatible t [] q ->
  memory_block Ews 27352 q =
  field_at_ Ews t (DOT _dictBuffer) q *
  field_at_ Ews t (DOT _dictContent) q *
  field_at_ Ews t (DOT _dictSize) q *
  field_at_ Ews t (DOT _entropy) q *
  field_at_ Ews t (DOT _dictID) q *
  field_at_ Ews t (DOT _entropyPresent) q *
  memory_block Ews 24 (field_address t (DOT _cMem) q) *
  ddict_pad q.
Proof.
  intros Hfc.
  assert (Hm: match q with Vptr _ o => Ptrofs.unsigned o + 27352 < Ptrofs.modulus | _ => True end).
  { destruct Hfc as (Hp & _ & Hsz & _). destruct q; try exact I. simpl in Hsz. unfold size_compatible in Hsz.
    change (sizeof t) with 27352 in Hsz. lia. }
  rewrite (ddict_fa_mb _dictBuffer 8 0) by dd_side.
  rewrite (ddict_fa_mb _dictContent 8 8) by dd_side.
  rewrite (ddict_fa_mb _dictSize 8 16) by dd_side.
  rewrite (ddict_fa_mb _entropy 27292 24) by dd_side.
  rewrite (ddict_fa_mb _dictID 4 27316) by dd_side.
  rewrite (ddict_fa_mb _entropyPresent 4 27320) by dd_side.
  rewrite field_compatible_field_address by dd_side.
  change (nested_field_offset t (DOT _cMem)) with 27328.
  unfold ddict_pad.
  assert (Hp: isptr q) by (destruct Hfc; auto).
  assert (Hq: q = offset_val 0 q) by (destruct q; try contradiction; simpl; rewrite Ptrofs.add_zero; auto).
  rewrite Hq at 1.
  change 27352 with (8 + 27344). rewrite (mb_split_at Ews 8 27344 0) by (try assumption; try lia; destruct q; auto; lia).
  change 27344 with (8 + 27336). rewrite (mb_split_at Ews 8 27336 (0+8)) by (try assumption; try lia; destruct q; auto; lia).
  change 27336 with (8 + 27328). rewrite (mb_split_at Ews 8 27328 (0+8+8)) by (try assumption; try lia; destruct q; auto; lia).
  change 27328 with (27292 + 36) at 1. rewrite (mb_split_at Ews 27292 36 (0+8+8+8)) by (try assumption; try lia; destruct q; auto; lia).
  change 36 with (4 + 32). rewrite (mb_split_at Ews 4 32 (0+8+8+8+27292)) by (try assumption; try lia; destruct q; auto; lia).
  change 32 with (4 + 28). rewrite (mb_split_at Ews 4 28 (0+8+8+8+27292+4)) by (try assumption; try lia; destruct q; auto; lia).
  change 28 with (4 + 24). rewrite (mb_split_at Ews 4 24 (0+8+8+8+27292+4+4)) by (try assumption; try lia; destruct q; auto; lia).
  rewrite <- Hq. simpl Z.add.
  apply pred_ext; cancel.
Qed.

Lemma ddict_cmem_mb (q: val) :
  field_compatible t [] q ->
  memory_block Ews 24 (field_address t (DOT _cMem) q) = data_at_ Ews t_cmem (field_address t (DOT _cMem) q).
Proof.
  intros Hfc. rewrite data_at__memory_block.
  assert (Hc: field_compatible t (DOT _cMem) q) by dd_side.
  pose proof (field_compatible_nested_field _ _ _ Hc) as Hn.
  rewrite <- field_compatible_field_address in Hn by exact Hc.
  change (nested_field_type t (DOT _cMem)) with t_cmem in Hn.
  rewrite prop_true_andp by exact Hn. reflexivity.
Qed.

Lemma ddict_split3 (q: val) :
  data_at_ Ews t q |--
  field_at_ Ews t (DOT _dictBuffer) q *
  field_at_ Ews t (DOT _dictContent) q *
  field_at_ Ews t (DOT _dictSize) q *
  field_at_ Ews t (DOT _entropy) q *
  field_at_ Ews t (DOT _dictID) q *
  field_at_ Ews t (DOT _entropyPresent) q *
  data_at_ Ews t_cmem (field_address t (DOT _cMem) q) *
  ddict_pad q.
Proof.
  rewrite data_at__memory_block. Intros. change (sizeof t) with 27352.
  rewrite ddict_pieces_eq by assumption. rewrite ddict_cmem_mb by assumption. apply derives_refl.
Qed.

Lemma ddict_merge3 (q: val) :
  field_at_ Ews t (DOT _dictBuffer) q *
  field_at_ Ews t (DOT _dictContent) q *
  field_at_ Ews t (DOT _dictSize) q *
  field_at_ Ews t (DOT _entropy) q *
  field_at_ Ews t (DOT _dictID) q *
  field_at_ Ews t (DOT _entropyPresent) q *
  data_at_ Ews t_cmem (field_address t (DOT _cMem) q) *
  ddict_pad q
  |-- data_at_ Ews t q.
Proof.
  assert_PROP (field_compatible t (DOT _dictBuffer) q) as Hc.
  { unfold field_at_. sep_apply (field_at_local_facts Ews t (DOT _dictBuffer)
      (default_val (nested_field_type t (DOT _dictBuffer))) q). Intros. apply prop_right. tauto. }
  pose proof (ddict_fc_root _ _ Hc) as Hfc.
  rewrite (data_at__memory_block Ews t q). rewrite prop_true_andp by exact Hfc. change (sizeof t) with 27352.
  rewrite ddict_pieces_eq by assumption. rewrite ddict_cmem_mb by assumption. apply derives_refl.
Qed.

End L.

(* small facts of the DDict representation (v2 body_FS_ddict.v) *)

Lemma cmem_field_back (q: val) :
  data_at Ews t_cmem cmem_null (field_address (Tstruct _ZSTD_DDict_s noattr) (DOT _cMem) q)
  |-- field_at_ Ews (Tstruct _ZSTD_DDict_s noattr) (DOT _cMem) q.
Proof.
  unfold field_at_. rewrite field_at_data_at. apply data_at_data_at_.
Qed.

Lemma ddict_rep_at_props (DENT: dent_pred) gv x buf :
  ddict_rep_at DENT gv x buf |--
  !! (isptr (dx_q x) /\ (dx_raw x = true \/ dict_auto_c (dx_bytes x) (dx_ld x) <> None)) && ddict_rep_at DENT gv x buf.
Proof. apply andp_right; [ | apply derives_refl]. unfold ddict_rep_at, ddict_struct. Intros. entailer!. Qed.

Lemma ddict_rep_at_valid (DENT: dent_pred) gv x buf :
  ddict_rep_at DENT gv x buf |-- valid_pointer (dx_q x).
Proof.
  unfold ddict_rep_at, ddict_struct. Intros.
  sep_apply (field_at_valid_ptr0 Ews (Tstruct _ZSTD_DDict_s noattr) (DOT _dictBuffer)); auto.
  entailer!.
Qed.

Lemma ddict_any_valid (q: val) : ddict_any q |-- valid_pointer q.
Proof.
  unfold ddict_any, ddict_failed. Intros n db.
  sep_apply (field_at_valid_ptr0 Ews (Tstruct _ZSTD_DDict_s noattr) (DOT _dictBuffer) db q); auto.
  repeat apply sepcon_valid_pointer1; apply derives_refl.
Qed.

Lemma ddict_fresh_fold (q: val) :
  field_at_ Ews (Tstruct _ZSTD_DDict_s noattr) (DOT _dictBuffer) q *
  field_at_ Ews (Tstruct _ZSTD_DDict_s noattr) (DOT _dictContent) q *
  field_at_ Ews (Tstruct _ZSTD_DDict_s noattr) (DOT _dictSize) q *
  field_at_ Ews (Tstruct _ZSTD_DDict_s noattr) (DOT _entropy) q *
  field_at_ Ews (Tstruct _ZSTD_DDict_s noattr) (DOT _dictID) q *
  field_at_ Ews (Tstruct _ZSTD_DDict_s noattr) (DOT _entropyPresent) q *
  data_at Ews t_cmem cmem_null (field_address (Tstruct _ZSTD_DDict_s noattr) (DOT _cMem) q)
  |-- ddict_fresh q.
Proof.
  unfold ddict_fresh.
  rewrite (field_at_data_at Ews (Tstruct _ZSTD_DDict_s noattr) (DOT _cMem)).
  cancel.
Qed.

Lemma failed_buf_ptr (n: Z) (db: val) :
  (if eq_dec db nullval then emp
   else malloc_token Ews (tarray tuchar n) db * data_at_ Ews (tarray tuchar n) db) |--
  !! is_pointer_or_null db &&
  (if eq_dec db nullval then emp
   else malloc_token Ews (tarray tuchar n) db * data_at_ Ews (tarray tuchar n) db).
Proof.
  apply andp_right; [ | apply derives_refl].
  destruct (eq_dec db nullval) as [->|?]; entailer!.
Qed.


(* ---------- the same facts for a DDict of the allocator am (FSSpecs3.ddict_any3, DecIface3.ddict_fresh3) ---------- *)

Lemma ddict_any3_valid (am: option cmem) (q: val) (nb: Z) : ddict_any3 am q nb |-- valid_pointer q.
Proof.
  unfold ddict_any3, ddict_failed3. Intros n db.
  sep_apply (field_at_valid_ptr0 Ews (Tstruct _ZSTD_DDict_s noattr) (DOT _dictBuffer) db q); auto.
  repeat apply sepcon_valid_pointer1; apply derives_refl.
Qed.

Lemma ddict_fresh3_fold (am: option cmem) (q: val) :
  field_at_ Ews (Tstruct _ZSTD_DDict_s noattr) (DOT _dictBuffer) q *
  field_at_ Ews (Tstruct _ZSTD_DDict_s noattr) (DOT _dictContent) q *
  field_at_ Ews (Tstruct _ZSTD_DDict_s noattr) (DOT _dictSize) q *
  field_at_ Ews (Tstruct _ZSTD_DDict_s noattr) (DOT _entropy) q *
  field_at_ Ews (Tstruct _ZSTD_DDict_s noattr) (DOT _dictID) q *
  field_at_ Ews (Tstruct _ZSTD_DDict_s noattr) (DOT _entropyPresent) q *
  data_at Ews t_cmem (cmem_v am) (field_address (Tstruct _ZSTD_DDict_s noattr) (DOT _cMem) q)
  |-- ddict_fresh3 am q.
Proof.
  unfold ddict_fresh3.
  rewrite (field_at_data_at Ews (Tstruct _ZSTD_DDict_s noattr) (DOT _cMem)).
  cancel.
Qed.

Lemma failed_buf_ptr3 (am: option cmem) (n: Z) (db: val) :
  (if eq_dec db nullval then emp
   else blk_tok am (tarray tuchar n) db * data_at_ Ews (tarray tuchar n) db) |--
  !! is_pointer_or_null db &&
  (if eq_dec db nullval then emp
   else blk_tok am (tarray tuchar n) db * data_at_ Ews (tarray tuchar n) db).
Proof.
  apply andp_right; [ | apply derives_refl].
  destruct (eq_dec db nullval) as [->|?]; entailer!.
Qed.

(* a live DDict is one ZSTD_freeDDict can free: its copy (if any) has its |b| bytes; DENT_OK gives back the entropy
   field's memory *)
Lemma ddict_rep_at_any3_mem (DENT: dent_pred) (HD: DENT_OK DENT) gv x buf :
  ddict_rep_at DENT gv x buf |--
  ddict_any3 (dx_mem x) (dx_q x) (if ddx_copied x then Zlength (dx_bytes x) else 0).
Proof.
  unfold ddict_rep_at, ddict_any3, ddict_failed3, ddict_struct, ddict_mem.
  Intros.
  sep_apply (HD gv (dx_q x) (ddx_ent x)).
  Exists (Zlength (dx_bytes x)) (if ddx_copied x then buf else nullval).
  destruct (ddx_copied x) eqn:Hc.
  - match goal with H: isptr buf \/ _ |- _ => pose proof (ddx_buf_copied x buf Hc H) end.
    rewrite if_false by (intro Heq; subst buf; contradiction).
    entailer!.
    rewrite if_false by (intro Heq; subst buf; contradiction). cancel.
  - rewrite if_true by auto. entailer!.
Qed.


(* the functions of a context's own allocator are valid pointers (the code tests them against NULL) *)
Lemma dd_cm_have_ptrs (m: cmem) (h: Z) :
  cm_have (Some m) h |-- !! (isptr (cm_alloc m) /\ isptr (cm_free m)).
Proof.
  unfold cm_have, cm_funs.
  sep_apply (func_ptr'_isptr cm_alloc_spec (cm_alloc m)). sep_apply (func_ptr'_isptr cm_free_spec (cm_free m)).
  entailer!.
Qed.

Lemma dd_cm_have_valid (m: cmem) (h: Z) :
  cm_have (Some m) h |-- valid_pointer (cm_alloc m) && valid_pointer (cm_free m).
Proof.
  unfold cm_have, cm_funs. apply andp_right.
  - apply sepcon_valid_pointer1. apply sepcon_valid_pointer1. apply func_ptr'_valid_pointer.
  - apply sepcon_valid_pointer1. apply sepcon_valid_pointer2. apply func_ptr'_valid_pointer.
Qed.

(* the copy of a DDict of an own allocator whose initialisation failed has nb >= 0 bytes *)
Lemma ddict_failed3_nb (am: option cmem) (q: val) (n nb: Z) :
  ddict_failed3 am q n nb |-- !! (am <> None -> 0 <= nb) && ddict_failed3 am q n nb.
Proof.
  apply andp_right; [ | apply derives_refl].
  unfold ddict_failed3. Intros db. apply prop_right. intros Ham.
  destruct (eq_dec db nullval); [lia | ]. match goal with H: db <> nullval -> _ |- _ => specialize (H n0 Ham) end. lia.
Qed.

(* a leftover DDict of the default allocator (FSRepC.ddict_any) is one ZSTD_freeDDict can free *)
Lemma ddict_any_any3 (q: val) : ddict_any q |-- EX nb: Z, ddict_any3 None q nb.
Proof.
  unfold ddict_any, ddict_failed, ddict_any3, ddict_failed3. Intros n db.
  Exists (if eq_dec db nullval then 0 else n) n db.
  unfold blk_tok. entailer!.
Qed.

End CM_DDictLayout3_1.
