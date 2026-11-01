(* Subtree B: the facts of B's predicates that DecSubtrees.B_obligation asks for:
   the tables group, whatever it holds, is the group's uninitialised fields; a DDict's entropy, whatever it
   holds, is its entropy field. *)
Require Export Zstd.proof.dec.B.BRep.
Local Open Scope logic.

(* two adjacent memory blocks are one *)
Lemma mb_join : forall sh n m p, 0 <= n -> 0 <= m ->
  memory_block sh n p * memory_block sh m (offset_val n p) |-- memory_block sh (n + m) p.
Proof.
  intros sh n m p Hn Hm.
  assert_PROP (isptr p /\ size_compatible' n p) as Hp1.
  { sep_apply (memory_block_local_facts sh n p). entailer!. }
  assert_PROP (size_compatible' m (offset_val n p)) as Hs2.
  { sep_apply (memory_block_local_facts sh m (offset_val n p)). entailer!. }
  destruct Hp1 as [Hp Hs].
  destruct p; try contradiction. simpl in Hs, Hs2. simpl offset_val.
  pose proof (Ptrofs.unsigned_range i).
  rewrite Ptrofs.add_unsigned, Ptrofs.unsigned_repr in Hs2 by (rewrite Ptrofs.unsigned_repr; rep_lia).
  rewrite Ptrofs.unsigned_repr in Hs2 by rep_lia.
  rewrite <- (Ptrofs.repr_unsigned i).
  rewrite (memory_block_split sh b (Ptrofs.unsigned i) n m) by lia.
  rewrite Ptrofs.add_unsigned. rewrite (Ptrofs.unsigned_repr n) by rep_lia.
  rewrite Ptrofs.repr_unsigned. cancel.
Qed.

Example test_sizes : sizeof t_seqSymbol = 8 /\ sizeof t_seqhdr = 8 /\ sizeof t_dtdesc = 4 /\
  sizeof t_deltx1 = 2 /\ sizeof t_deltx2 = 4.
Proof. repeat split; reflexivity. Qed.

Lemma sizeof_arr : forall t n, (0 <= n)%Z -> sizeof (tarray t n) = (sizeof t * n)%Z.
Proof. intros. unfold tarray. rewrite sizeof_Tarray. f_equal. lia. Qed.

(* a sequence table field, whatever it holds, is its sk_size k cells of memory *)
Lemma seqspace_mb : forall sh k ot p,
  seqspace_at sh k ot p |-- memory_block sh (8 * sk_size k) p.
Proof.
  intros sh k ot p.
  assert (Hs: 2 ^ sk_maxlog k <= 512 /\ sk_size k = 1 + 2 ^ sk_maxlog k)
    by (destruct k; split; reflexivity || (vm_compute; discriminate)).
  destruct ot as [t|]; simpl.
  - unfold seqtab_at, seqtab_at_fm. Intros fm. destruct H as [[Hlog0 Hlog] _].
    assert (Hk: 2 ^ ft_log t <= 2 ^ sk_maxlog k) by (apply Z.pow_le_mono_r; lia).
    assert (0 < 2 ^ ft_log t) by (apply Z.pow_pos_nonneg; lia).
    sep_apply (data_at_memory_block sh t_seqhdr).
    sep_apply (data_at_memory_block sh (tarray t_seqSymbol (2 ^ ft_log t))).
    sep_apply (data_at__memory_block_cancel sh (tarray t_seqSymbol (sk_size k - 1 - 2 ^ ft_log t))).
    rewrite !sizeof_arr by lia.
    change (sizeof t_seqhdr) with 8. change (sizeof t_seqSymbol) with 8.
    sep_apply (mb_join sh 8 (8 * 2 ^ ft_log t) p); try lia.
    replace (8 * (1 + 2 ^ ft_log t))%Z with (8 + 8 * 2 ^ ft_log t)%Z by lia.
    sep_apply (mb_join sh (8 + 8 * 2 ^ ft_log t) (8 * (sk_size k - 1 - 2 ^ ft_log t)) p); try lia.
    replace (8 + 8 * 2 ^ ft_log t + 8 * (sk_size k - 1 - 2 ^ ft_log t))%Z with (8 * sk_size k)%Z by lia.
    cancel.
  - sep_apply (data_at__memory_block_cancel sh (tarray t_seqSymbol (sk_size k))).
    rewrite sizeof_arr by lia. change (sizeof t_seqSymbol) with 8. cancel.
Qed.

(* the 4097 U32s of a Huffman table, to be built or built *)
Lemma hufhdr_mb : forall sh p, hufhdr_at sh p |-- memory_block sh 16388 p.
Proof.
  intros. unfold hufhdr_at. Intros ty lg res.
  sep_apply (data_at_memory_block sh t_dtdesc). change (sizeof t_dtdesc) with 4.
  unfold HUF_CELLBYTES.
  sep_apply (mb_join sh 4 16384 p); try lia. simpl Z.add. cancel.
Qed.

Lemma hufdt_mb : forall sh ht p, hufdt_at sh ht p |-- memory_block sh 16388 p.
Proof.
  intros. unfold hufdt_at, hufdt_x_at. Intros x2 L res. destruct H as [Hok [HL Hal]].
  destruct Hok as [Hlog _].
  assert (0 < 2 ^ L) by (apply Z.pow_pos_nonneg; lia).
  assert (2 ^ L <= 2 ^ 12) by (apply Z.pow_le_mono_r; unfold HUF_TABLELOG_MAX in *; lia).
  change (2 ^ 12) with 4096 in *.
  sep_apply (data_at_memory_block sh t_dtdesc). change (sizeof t_dtdesc) with 4.
  unfold HUF_CELLBYTES.
  destruct x2.
  - Intros c2.
    sep_apply (data_at_memory_block sh (tarray t_deltx2 (2 ^ L))).
    rewrite sizeof_arr by lia. change (sizeof t_deltx2) with 4.
    sep_apply (mb_join sh 4 (4 * 2 ^ L) p); try lia.
    sep_apply (mb_join sh (4 + 4 * 2 ^ L) (16384 - 4 * 2 ^ L) p); try lia.
    replace (4 + 4 * 2 ^ L + (16384 - 4 * 2 ^ L))%Z with 16388 by lia. cancel.
  - sep_apply (data_at_memory_block sh (tarray t_deltx1 (2 ^ L))).
    rewrite sizeof_arr by lia. change (sizeof t_deltx1) with 2.
    sep_apply (mb_join sh 4 (2 * 2 ^ L) p); try lia.
    sep_apply (mb_join sh (4 + 2 * 2 ^ L) (16384 - 2 * 2 ^ L) p); try lia.
    replace (4 + 2 * 2 ^ L + (16384 - 2 * 2 ^ L))%Z with 16388 by lia. cancel.
Qed.

Lemma mb_join_at : forall sh p a n m b c, (0 <= n)%Z -> (0 <= m)%Z -> b = (a + n)%Z -> c = (n + m)%Z ->
  memory_block sh n (offset_val a p) * memory_block sh m (offset_val b p) |-- memory_block sh c (offset_val a p).
Proof.
  intros; subst. rewrite <- offset_offset_val. apply mb_join; auto.
Qed.

(* a built table can be rebuilt: only its descriptor's maxTableLog stays *)
Lemma hufdt_hdr : forall sh ht p, hufdt_at sh ht p |-- hufhdr_at sh p.
Proof.
  intros. unfold hufdt_at, hufdt_x_at, hufhdr_at. Intros x2 L res. destruct H as [Hlog _].
  match goal with HL: L = hufdt_log _ _ |- _ => clear HL end.
  assert (0 < 2 ^ L) by (apply Z.pow_pos_nonneg; lia).
  assert (2 ^ L <= 2 ^ 12) by (apply Z.pow_le_mono_r; unfold HUF_TABLELOG_MAX in *; lia).
  change (2 ^ 12) with 4096 in *.
  Exists (Vint (Int.repr (if x2 then 1 else 0))) (Vint (Int.repr L)) res.
  (* the descriptor bytes tableType (0 or 1) and tableLog (L <= 12) are defined bytes *)
  assert (byte_val (Vint (Int.repr (if x2 then 1 else 0))))
    by (exists (if x2 then 1 else 0); destruct x2; split; auto; lia).
  assert (byte_val (Vint (Int.repr L))) by (exists L; split; auto; unfold HUF_TABLELOG_MAX in *; lia).
  unfold HUF_CELLBYTES. entailer!.
  destruct x2.
  - Intros c2.
    sep_apply (data_at_memory_block sh (tarray t_deltx2 (2 ^ L))).
    rewrite sizeof_arr by lia. change (sizeof t_deltx2) with 4.
    sep_apply (mb_join_at sh p 4 (4 * 2 ^ L) (16384 - 4 * 2 ^ L) (4 + 4 * 2 ^ L) 16384); try lia. cancel.
  - sep_apply (data_at_memory_block sh (tarray t_deltx1 (2 ^ L))).
    rewrite sizeof_arr by lia. change (sizeof t_deltx1) with 2.
    sep_apply (mb_join_at sh p 4 (2 * 2 ^ L) (16384 - 2 * 2 ^ L) (4 + 2 * 2 ^ L) 16384); try lia. cancel.
Qed.

(* evaluate the offsets and sizes of fields *)
Ltac eval_fields :=
  repeat match goal with
  | |- context [nested_field_offset ?t ?g] =>
      let x := eval vm_compute in (nested_field_offset t g) in change (nested_field_offset t g) with x
  | |- context [sizeof (nested_field_type ?t ?g)] =>
      let x := eval vm_compute in (sizeof (nested_field_type t g)) in change (sizeof (nested_field_type t g)) with x
  end.

Lemma ent_ctx_join : forall sh p,
  field_at_ sh t_dctx (DOT _entropy DOT _LLTable) p * field_at_ sh t_dctx (DOT _entropy DOT _OFTable) p *
  field_at_ sh t_dctx (DOT _entropy DOT _MLTable) p * field_at_ sh t_dctx (DOT _entropy DOT _hufTable) p *
  field_at_ sh t_dctx (DOT _entropy DOT _rep) p * field_at_ sh t_dctx (DOT _entropy DOT _workspace) p
  |-- field_at_ sh t_dctx (DOT _entropy) p.
Proof.
  intros.
  assert_PROP (field_compatible t_dctx (DOT _entropy DOT _LLTable) p /\
               field_compatible t_dctx (DOT _entropy DOT _OFTable) p /\
               field_compatible t_dctx (DOT _entropy DOT _MLTable) p /\
               field_compatible t_dctx (DOT _entropy DOT _hufTable) p /\
               field_compatible t_dctx (DOT _entropy DOT _rep) p /\
               field_compatible t_dctx (DOT _entropy DOT _workspace) p) as FC by entailer!.
  destruct FC as (F1 & F2 & F3 & F4 & F5 & F6).
  assert (F0: field_compatible t_dctx (DOT _entropy) p)
    by (apply field_compatible_cons in F1; destruct F1; auto).
  rewrite !field_at__memory_block. unfold field_address. rewrite !if_true by auto.
  eval_fields.
  sep_apply (mb_join_at sh p 32 4104 2056 4136 6160); try lia.
  sep_apply (mb_join_at sh p 32 6160 4104 6192 10264); try lia.
  sep_apply (mb_join_at sh p 32 10264 16388 10296 26652); try lia.
  sep_apply (mb_join_at sh p 32 26652 12 26684 26664); try lia.
  sep_apply (mb_join_at sh p 32 26664 628 26696 27292); try lia.
  cancel.
Qed.

Lemma ent_dd_join : forall sh q,
  field_at_ sh t_entropy_dd (DOT _entropy DOT _LLTable) q *
  field_at_ sh t_entropy_dd (DOT _entropy DOT _OFTable) q *
  field_at_ sh t_entropy_dd (DOT _entropy DOT _MLTable) q *
  field_at_ sh t_entropy_dd (DOT _entropy DOT _hufTable) q *
  field_at_ sh t_entropy_dd (DOT _entropy DOT _rep) q *
  field_at_ sh t_entropy_dd (DOT _entropy DOT _workspace) q
  |-- field_at_ sh t_entropy_dd (DOT _entropy) q.
Proof.
  intros.
  assert_PROP (field_compatible t_entropy_dd (DOT _entropy DOT _LLTable) q /\
               field_compatible t_entropy_dd (DOT _entropy DOT _OFTable) q /\
               field_compatible t_entropy_dd (DOT _entropy DOT _MLTable) q /\
               field_compatible t_entropy_dd (DOT _entropy DOT _hufTable) q /\
               field_compatible t_entropy_dd (DOT _entropy DOT _rep) q /\
               field_compatible t_entropy_dd (DOT _entropy DOT _workspace) q) as FC by entailer!.
  destruct FC as (F1 & F2 & F3 & F4 & F5 & F6).
  assert (F0: field_compatible t_entropy_dd (DOT _entropy) q)
    by (apply field_compatible_cons in F1; destruct F1; auto).
  rewrite !field_at__memory_block. unfold field_address. rewrite !if_true by auto.
  eval_fields.
  sep_apply (mb_join_at sh q 24 4104 2056 4128 6160); try lia.
  sep_apply (mb_join_at sh q 24 6160 4104 6184 10264); try lia.
  sep_apply (mb_join_at sh q 24 10264 16388 10288 26652); try lia.
  sep_apply (mb_join_at sh q 24 26652 12 26676 26664); try lia.
  sep_apply (mb_join_at sh q 24 26664 628 26688 27292); try lia.
  cancel.
Qed.

(* the table fields, whatever they hold, are their fields of the context / the DDict *)
Lemma seqspace_ctx : forall k ot p,
  seqspace_at Ews k ot (ctx_seq k p) |-- field_at_ Ews t_dctx (DOT _entropy DOT sk_tfield k) p.
Proof.
  intros. sep_apply seqspace_mb. rewrite field_at__memory_block. unfold ctx_seq.
  apply derives_refl'. f_equal. destruct k; reflexivity.
Qed.

Lemma seqspace_dd : forall k ot q,
  seqspace_at Ews k ot (dd_seq k q) |-- field_at_ Ews t_entropy_dd (DOT _entropy DOT sk_tfield k) q.
Proof.
  intros. sep_apply seqspace_mb. rewrite field_at__memory_block. unfold dd_seq.
  apply derives_refl'. f_equal. destruct k; reflexivity.
Qed.

Lemma hufdt_ctx : forall ht p,
  hufdt_at Ews ht (ctx_huf p) |-- field_at_ Ews t_dctx (DOT _entropy DOT _hufTable) p.
Proof.
  intros. sep_apply hufdt_mb. rewrite field_at__memory_block. unfold ctx_huf.
  apply derives_refl'. f_equal.
Qed.

Lemma hufhdr_ctx : forall p,
  hufhdr_at Ews (ctx_huf p) |-- field_at_ Ews t_dctx (DOT _entropy DOT _hufTable) p.
Proof.
  intros. sep_apply hufhdr_mb. rewrite field_at__memory_block. unfold ctx_huf.
  apply derives_refl'. f_equal.
Qed.

Lemma hufdt_dd : forall ht q,
  hufdt_at Ews ht (dd_huf q) |-- field_at_ Ews t_entropy_dd (DOT _entropy DOT _hufTable) q.
Proof.
  intros. sep_apply hufdt_mb. rewrite field_at__memory_block. unfold dd_huf.
  apply derives_refl'. f_equal.
Qed.

Lemma dent_def_entropy : DENT_OK dent_def.
Proof.
  intros gv q oe. unfold dent_def. destruct oe as [st|]; [|apply derives_refl].
  destruct (st_huf st) as [ht|], (st_seq st) as [[[a b] c]|]; cbv beta iota; try apply FF_left.
  Intros.
  sep_apply hufdt_dd.
  sep_apply (seqspace_dd KLL). sep_apply (seqspace_dd KOF). sep_apply (seqspace_dd KML).
  simpl sk_tfield.
  sep_apply (field_at_field_at_ Ews t_entropy_dd (DOT _entropy DOT _rep)).
  sep_apply (ent_dd_join Ews q). cancel.
Qed.

Lemma tabs_huf_fields : forall gv p ox oh x2,
  tabs_huf gv p ox oh x2 |--
  field_at_ Ews t_dctx (DOT _HUFptr) p * field_at_ Ews t_dctx (DOT _litEntropy) p *
  field_at_ Ews t_dctx (DOT _entropy DOT _hufTable) p.
Proof.
  intros. unfold tabs_huf. Intros hp.
  destruct oh as [ht|].
  - Intros w. destruct w; Intros.
    + assert (Hx: hufdt_x_at x2 Ews ht (ctx_huf p) |-- hufdt_at Ews ht (ctx_huf p))
        by (unfold hufdt_at; Exists x2; apply derives_refl).
      sep_apply Hx. sep_apply hufdt_ctx. cancel.
    + sep_apply hufhdr_ctx. cancel.
  - Intros. sep_apply hufhdr_ctx. cancel.
Qed.

Lemma seq_where_fields : forall gv p ox k t,
  seq_where gv p ox k t |-- (EX tp: val, seq_ptr_at p k tp) *
  field_at_ Ews t_dctx (DOT _entropy DOT sk_tfield k) p.
Proof.
  intros. unfold seq_where. Intros tp w. Exists tp.
  destruct w; Intros; sep_apply seqspace_ctx; cancel.
Qed.

Lemma tabs_seq_fields : forall gv p ox os fe,
  tabs_seq gv p ox os fe |--
  field_at_ Ews t_dctx (DOT _fseEntropy) p *
  field_at_ Ews t_dctx (DOT _LLTptr) p * field_at_ Ews t_dctx (DOT _OFTptr) p *
  field_at_ Ews t_dctx (DOT _MLTptr) p *
  field_at_ Ews t_dctx (DOT _entropy DOT _LLTable) p *
  field_at_ Ews t_dctx (DOT _entropy DOT _OFTable) p *
  field_at_ Ews t_dctx (DOT _entropy DOT _MLTable) p.
Proof.
  intros. unfold tabs_seq. destruct os as [[[a b] c]|].
  - sep_apply (seq_where_fields gv p ox KLL a). sep_apply (seq_where_fields gv p ox KOF b).
    sep_apply (seq_where_fields gv p ox KML c).
    Intros t1 t2 t3. simpl seq_ptr_at. simpl sk_tfield. cancel.
  - sep_apply (seqspace_ctx KLL). sep_apply (seqspace_ctx KOF). sep_apply (seqspace_ctx KML).
    simpl sk_tfield. cancel.
Qed.

Lemma tabs_def_uninit : TABS_OK tabs_def.
Proof.
  intros gv p ox ts. unfold tabs_def, tables_uninit, tabs_scratch. Intros.
  sep_apply tabs_huf_fields. sep_apply tabs_seq_fields.
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _entropy DOT _rep)).
  sep_apply (ent_ctx_join Ews p). cancel.
Qed.

Lemma B_preds_ok : TABS_OK tabs_def /\ DENT_OK dent_def.
Proof. exact (conj tabs_def_uninit dent_def_entropy). Qed.

Lemma tabs_def_ok : TABS_OK tabs_def.
Proof. exact (proj1 B_preds_ok). Qed.

Lemma dent_def_ok : DENT_OK dent_def.
Proof. exact (proj2 B_preds_ok). Qed.
