(* Sub-group HDR of group BLK (BlkGroups.v): ZSTD_buildSeqTable_rle,
   ZSTD_buildSeqTable, ZSTD_decodeSeqHeaders.  Choose one specification per function of ids_HDR (containing
   HDR_exports) and prove every body against G_BLK ++ HDR_imports and them. *)
Require Export Zstd.proof.dec.B.blk.BlkGroups.
Require Import Zstd.proof.model.ExHuf Zstd.proof.model.ExBlock.
Local Open Scope logic.


(* ===================== helpers (layout, globals) ===================== *)

Lemma hdr_sk_max_bounds (k: seqkind) : 31 <= sk_max k <= 52 /\ 8 <= sk_maxlog k <= 9.
Proof. destruct k; simpl; unfold MaxLL, MaxOff, MaxML, LLFSELog, OffFSELog, MLFSELog; lia. Qed.

Lemma hdr_sk_size (k: seqkind) : sk_size k = 1 + 2 ^ sk_maxlog k /\ 257 <= sk_size k <= 513.
Proof. destruct k; unfold sk_size, sk_maxlog, LLFSELog, OffFSELog, MLFSELog; simpl; lia. Qed.

(* the base / extra-bits tables of kind k inside zstd_globals (as in ent/body_ent_buildfse.v) *)
Definition hdr_bvals (k: seqkind) : list val :=
  match k with KLL => LL_base_val | KOF => OF_base_val | KML => ML_base_val end.
Definition hdr_nvals (k: seqkind) : list val :=
  match k with KLL => LL_bits_val | KOF => OF_bits_val | KML => ML_bits_val end.

Definition hdr_zg_common (gv: globals) : mpred :=
  data_at Ews tint g_debuglevel_val (gv _g_debuglevel) *
  data_at Ers (tarray tuint 32) DeBruijnBytePos_val (gv _DeBruijnBytePos) *
  data_at Ers (tarray tuint 32) DeBruijnClz_val (gv _DeBruijnClz) *
  data_at Ers tulong zeroFilled_val (gv _zeroFilled) *
  data_at Ers (Tstruct ___gp_ZSTD_customMem noattr) ZSTD_defaultCMem_val (gv _ZSTD_defaultCMem) *
  data_at Ers (tarray tuint 3) repStartValue_val (gv _repStartValue) *
  data_at Ers (tarray tulong 4) ZSTD_fcs_fieldSize_val (gv _ZSTD_fcs_fieldSize) *
  data_at Ers (tarray tulong 4) ZSTD_did_fieldSize_val (gv _ZSTD_did_fieldSize) *
  data_at Ers tulong ZSTD_blockHeaderSize_val (gv _ZSTD_blockHeaderSize) *
  data_at Ers (tarray (tarray (Tstruct ___gp_algo_time_t noattr) 2) 16) algoTime_val (gv _algoTime) *
  data_at Ers (tarray (Tstruct ___gp_ZSTD_seqSymbol noattr) 65) LL_defaultDTable_val (gv _LL_defaultDTable) *
  data_at Ers (tarray (Tstruct ___gp_ZSTD_seqSymbol noattr) 33) OF_defaultDTable_val (gv _OF_defaultDTable) *
  data_at Ers (tarray (Tstruct ___gp_ZSTD_seqSymbol noattr) 65) ML_defaultDTable_val (gv _ML_defaultDTable) *
  data_at Ers (tarray tuint 8) dec32table_val (gv _dec32table) *
  data_at Ers (tarray tint 8) dec64table_val (gv _dec64table) *
  eb_res gv.

Definition hdr_zg_rest (k: seqkind) (gv: globals) : mpred :=
  hdr_zg_common gv *
  match k with
  | KLL => data_at Ers (tarray tuchar 53) ML_bits_val (gv _ML_bits) *
           data_at Ers (tarray tuint 32) OF_base_val (gv _OF_base) *
           data_at Ers (tarray tuchar 32) OF_bits_val (gv _OF_bits) *
           data_at Ers (tarray tuint 53) ML_base_val (gv _ML_base)
  | KOF => data_at Ers (tarray tuchar 36) LL_bits_val (gv _LL_bits) *
           data_at Ers (tarray tuchar 53) ML_bits_val (gv _ML_bits) *
           data_at Ers (tarray tuint 36) LL_base_val (gv _LL_base) *
           data_at Ers (tarray tuint 53) ML_base_val (gv _ML_base)
  | KML => data_at Ers (tarray tuchar 36) LL_bits_val (gv _LL_bits) *
           data_at Ers (tarray tuint 36) LL_base_val (gv _LL_base) *
           data_at Ers (tarray tuint 32) OF_base_val (gv _OF_base) *
           data_at Ers (tarray tuchar 32) OF_bits_val (gv _OF_bits)
  end.

Lemma hdr_zg_split (k: seqkind) (gv: globals) :
  zstd_globals gv =
  data_at Ers (tarray tuint (sk_max k + 1)) (hdr_bvals k) (gv (sk_gbase k)) *
  data_at Ers (tarray tuchar (sk_max k + 1)) (hdr_nvals k) (gv (sk_gbits k)) * hdr_zg_rest k gv.
Proof.
  destruct k; unfold zstd_globals, hdr_zg_rest, hdr_zg_common, sk_max, hdr_bvals, hdr_nvals, sk_gbase, sk_gbits;
    simpl; apply pred_ext; cancel.
Qed.

Lemma hdr_bvals_eq (k: seqkind) :
  hdr_bvals k = map (fun i => Vint (Int.repr (sk_base k i))) (upto (Z.to_nat (sk_max k + 1))).
Proof. destruct k; vm_compute; reflexivity. Qed.

Lemma hdr_nvals_eq (k: seqkind) :
  hdr_nvals k = map (fun i => Vint (Int.repr (sk_bits k i))) (upto (Z.to_nat (sk_max k + 1))).
Proof. destruct k; vm_compute; reflexivity. Qed.

(* the loaded values (VST's loads use the Vundef instance of Znth) *)
Lemma hdr_bvals_nth (k: seqkind) (s: Z) : 0 <= s <= sk_max k ->
  @Znth val Vundef s (hdr_bvals k) = Vint (Int.repr (sk_base k s)).
Proof.
  intros Hs. change (@Znth val Vundef s (hdr_bvals k)) with (@Znth val Inhabitant_val s (hdr_bvals k)).
  rewrite hdr_bvals_eq, Znth_map, Znth_upto by (rewrite ?Zlength_upto; lia). auto.
Qed.

Lemma hdr_nvals_nth (k: seqkind) (s: Z) : 0 <= s <= sk_max k ->
  @Znth val Vundef s (hdr_nvals k) = Vint (Int.repr (sk_bits k s)).
Proof.
  intros Hs. change (@Znth val Vundef s (hdr_nvals k)) with (@Znth val Inhabitant_val s (hdr_nvals k)).
  rewrite hdr_nvals_eq, Znth_map, Znth_upto by (rewrite ?Zlength_upto; lia). auto.
Qed.

Lemma hdr_sk_ranges_b (k: seqkind) :
  forallb (fun i => ((0 <=? sk_base k i) && (sk_base k i <=? 2147483645) && (0 <=? sk_bits k i) && (sk_bits k i <=? 31))%bool)
    (upto (Z.to_nat (sk_max k + 1))) = true.
Proof. destruct k; vm_compute; reflexivity. Qed.

Lemma hdr_sk_ranges (k: seqkind) (s: Z) : 0 <= s <= sk_max k ->
  0 <= sk_base k s <= 2147483645 /\ 0 <= sk_bits k s <= 31.
Proof.
  intros Hs. pose proof (hdr_sk_ranges_b k) as H. rewrite forallb_forall in H.
  specialize (H s). rewrite In_upto in H by (rewrite ?Z2Nat.id; lia).
  specialize (H ltac:(lia)). rewrite !andb_true_iff, !Z.leb_le in H. lia.
Qed.

(* the table field: header cell, S cells, the rest (as ent/body_ent_buildfse.v's dt_split) *)
Lemma hdr_dt_split (shd: share) (dt: val) (N S: Z) :
  0 <= S -> 1 + S <= N <= 1000 -> field_compatible (tarray t_seqSymbol N) [] dt ->
  data_at_ shd (tarray t_seqSymbol N) dt =
  data_at_ shd t_seqhdr dt * data_at_ shd (tarray t_seqSymbol S) (offset_val 8 dt) *
  data_at_ shd (tarray t_seqSymbol (N - 1 - S)) (offset_val (8 * (1 + S)) dt).
Proof.
  intros HS HN Hf.
  pose proof (proj1 (field_compatible_Tarray_split t_seqSymbol 1 N dt ltac:(lia)) Hf) as [Hf1 Hf2].
  rewrite (arr_field_address0 _ _ _ _ Hf) in Hf2 by lia.
  rewrite (split2_data_at__Tarray_app 1 N) by lia.
  rewrite (split2_data_at__Tarray_app S (N - 1)) by lia.
  rewrite (arr_field_address0 _ _ _ _ Hf) by lia.
  rewrite (arr_field_address0 _ _ _ _ Hf2) by lia.
  change (sizeof t_seqSymbol) with 8. rewrite offset_offset_val.
  replace (8 * 1 + 8 * S)%Z with (8 * (1 + S))%Z by lia. rewrite sepcon_assoc. f_equal.
  destruct dt as [| | | | | b o]; try (destruct Hf as [Hp _]; contradiction).
  pose proof Hf1 as (_ & _ & Hsz & Hal & _).
  assert (H4: (4 | Ptrofs.unsigned o)).
  { red in Hal. eapply align_compatible_rec_Tarray_inv with (i := 0) in Hal; [|lia].
    unfold t_seqSymbol in Hal. inv Hal; [discriminate|].
    vm_compute in H1. inv H1.
    assert (Hb: align_compatible_rec cenv_cs tuint
                  (Ptrofs.unsigned o + Ctypes.sizeof (Tstruct ___gp_ZSTD_seqSymbol noattr) * 0 + 4)).
    { apply H4 with (i0 := _baseValue); reflexivity. }
    inv Hb. simpl in H. inv H. rewrite Z.mul_0_r, Z.add_0_r in H0. simpl in H0.
    replace (Ptrofs.unsigned o) with (Ptrofs.unsigned o + 4 - 4)%Z by lia.
    apply Z.divide_sub_r; [auto|apply Z.divide_refl]. }
  rewrite !data_at__memory_block. rewrite (prop_true_andp _ _ Hf1).
  rewrite prop_true_andp; [reflexivity|].
  split3; [auto | reflexivity |]. split3; [ | | split; auto].
  - unfold size_compatible in *. change (sizeof t_seqhdr) with 8.
    change (sizeof (tarray t_seqSymbol 1)) with 8 in Hsz. lia.
  - red. eapply align_compatible_rec_Tstruct; [vm_compute; reflexivity | reflexivity |].
    intros i0 t0 z0 Ht Ho. unfold Ctypes.field_type in Ht. simpl co_members in Ht.
    cbn beta iota in Ht. simpl name_member in Ht.
    destruct (ident_eq i0 343967563891343%positive);
      [subst; inv Ht; vm_compute in Ho; inv Ho; eapply align_compatible_rec_by_value; [reflexivity|];
       simpl; rewrite Z.add_0_r; auto|].
    destruct (ident_eq i0 353543694627485%positive);
      [subst; inv Ht; vm_compute in Ho; inv Ho; eapply align_compatible_rec_by_value; [reflexivity|];
       simpl; apply Z.divide_add_r; [auto | apply Z.divide_refl]|].
    discriminate.
Qed.

(* ===================== one kind's table state in the context ===================== *)

(* the context's pointer field of kind k *)
Definition kptr_ (p: val) (k: seqkind) : mpred := field_at_ Ews t_dctx (DOT sk_pfield k) p.

(* the state of kind k after an error: the pointer and the context's table field are anything *)
Definition kjunk (p: val) (k: seqkind) : mpred := kptr_ p k * seqspace_at Ews k None (ctx_seq k p).

(* the state of kind k: no table (o = None, fseEntropy 0), or the table t where seq_where says *)
Definition kstate (gv: globals) (p: val) (ox: option ddx) (k: seqkind) (o: option fse_table) : mpred :=
  match o with
  | None => kjunk p k
  | Some t => seq_where gv p ox k t
  end.

Definition fe_of (o: option fse_table) : Z := match o with Some _ => 1 | None => 0 end.


(* the context's table field of kind k is a whole array *)
Lemma hdr_ctx_seq_fc (k: seqkind) (p: val) :
  field_compatible t_dctx [] p -> field_compatible (tarray t_seqSymbol (sk_size k)) [] (ctx_seq k p).
Proof.
  intros Hf. unfold ctx_seq.
  assert (H: field_compatible t_dctx (DOT _entropy DOT sk_tfield k) p).
  { destruct Hf as (H1 & H2 & H3 & H4 & H5).
    destruct k; repeat split; auto; unfold in_members; cbv [map name_member]; simpl;
      repeat (first [left; reflexivity | right]). }
  apply (field_compatible_app [] t_dctx) in H. destruct k; exact H.
Qed.

(* a table field with or without a table is a whole array of cells *)
Lemma hdr_seqspace_weak (sh: share) (k: seqkind) (o: option fse_table) (q: val) :
  field_compatible (tarray t_seqSymbol (sk_size k)) [] q ->
  seqspace_at sh k o q |-- data_at_ sh (tarray t_seqSymbol (sk_size k)) q.
Proof.
  intros Hf. destruct o as [t|]; [|unfold seqspace_at; auto].
  unfold seqspace_at, seqtab_at, seqtab_at_fm. Intros fm.
  destruct H as ((Hl0 & Hl1) & Hlen & _).
  destruct (hdr_sk_size k) as [Hs1 Hs2].
  assert (2 ^ ft_log t <= 2 ^ sk_maxlog k) by (apply Z.pow_le_mono_r; lia).
  rewrite (hdr_dt_split sh q (sk_size k) (2 ^ ft_log t)) by (auto; lia).
  cancel.
Qed.

Lemma hdr_kstate_junk (gv: globals) (p: val) (ox: option ddx) (k: seqkind) (o: option fse_table) :
  field_compatible t_dctx [] p -> kstate gv p ox k o |-- kjunk p k.
Proof.
  intros Hf. destruct o as [t|]; [|unfold kstate; auto]. unfold kstate, kjunk, seq_where, kptr_. Intros tp w.
  assert (Hp: seq_ptr_at p k tp |-- field_at_ Ews t_dctx (DOT sk_pfield k) p)
    by (destruct k; unfold seq_ptr_at; simpl; cancel).
  sep_apply Hp. destruct w; Intros; cancel.
  unfold seqspace_at at 2. apply hdr_seqspace_weak, hdr_ctx_seq_fc; auto.
Qed.

(* ===================== specifications ===================== *)

(* ZSTD_buildSeqTable_rle(dt, baseValue, nbAddBits): the one-cell table of the symbol sym of kind k *)
Definition ZSTD_buildSeqTable_rle_spec : ident * funspec :=
  DECLARE _ZSTD_buildSeqTable_rle
  WITH k: seqkind, sym: Z, dt: val
  PRE [ tptr t_seqSymbol, tuint, tuchar ]
    PROP (0 <= sym <= sk_max k)
    PARAMS (dt; Vint (Int.repr (sk_base k sym)); Vint (Int.repr (sk_bits k sym)))
    SEP (data_at_ Ews (tarray t_seqSymbol (sk_size k)) dt)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (seqspace_at Ews k (Some (fse_rle sym)) dt).

(* ZSTD_buildSeqTable(dctx->entropy.XTable, &dctx->XTptr, mode, MaxX, XFSELog, src, srcSize, X_base, X_bits,
   X_defaultDTable, dctx->fseEntropy, dctx->ddictIsCold, nbSeq, dctx->workspace, sizeof(dctx->workspace), 0):
   the table of kind k from its mode and the window s.  zstd's result res (C-result form, as FSE_readNCount's:
   zstd may accept a description the model rejects): the model's seq_table whenever the model reads it; on
   success a well-formed table and the bytes it takes; kind k's state becomes the new table (kstate), or
   anything after an error.  o is kind k's current table (None iff fseEntropy = 0).  Exactly (last PROP): res
   is ExBlock.x_seq_table's, zstd's own outcome on every window. *)
Definition ZSTD_buildSeqTable_spec : ident * funspec :=
  DECLARE _ZSTD_buildSeqTable
  WITH gv: globals, p: val, ox: option ddx, k: seqkind, o: option fse_table, mode: Z, dd: Z, nbSeq: Z,
       sh: share, base: val, N: Z, c: list val, off: Z, s: list Z
  PRE [ tptr t_seqSymbol, tptr (tptr t_seqSymbol), tint, tuint, tuint, tptr tvoid, tulong, tptr tuint,
        tptr tuchar, tptr t_seqSymbol, tuint, tint, tint, tptr tuint, tulong, tint ]
    PROP (0 <= mode <= 3; dd = 0 \/ dd = 1; 0 <= nbSeq <= Int.max_signed; win_ok sh N c off (Zlength s) s;
          match o with Some t => fse_ok k t | None => True end; Zlength s <= ZSTD_BLOCKSIZE_MAX)
    PARAMS (ctx_seq k p; field_address t_dctx (DOT sk_pfield k) p; Vint (Int.repr mode);
            Vint (Int.repr (sk_max k)); Vint (Int.repr (sk_maxlog k)); offset_val off base;
            Vlong (Int64.repr (Zlength s)); gv (sk_gbase k); gv (sk_gbits k); gv (sk_gdefault k);
            Vint (Int.repr (fe_of o)); Vint (Int.repr dd); Vint (Int.repr nbSeq);
            field_address t_dctx (DOT _workspace) p; Vlong (Int64.repr 2560); Vint (Int.repr 0))
    GLOBALS (gv)
    SEP (zstd_globals gv; kstate gv p ox k o; dent_of dent_def gv ox; field_at_ Ews t_dctx (DOT _workspace) p;
         data_at sh (tarray tuchar N) c base)
  POST [ tulong ]
    EX r: Z, EX res: option (fse_table * Z),
    PROP (0 <= r <= Int64.max_unsigned;
          forall x, seq_table mode (sk_predef k) o (sk_max k) (sk_maxlog k) s = Some x -> res = Some x;
          match res with
          | Some (t, used) => r = used /\ used <= Zlength s /\ fse_ok k t
          | None => is_error_code r = true
          end;
          res = x_seq_table ncount_c mode (sk_predef k) o (sk_max k) (sk_maxlog k) s)
    RETURN (Vlong (Int64.repr r))
    SEP (zstd_globals gv; dent_of dent_def gv ox; field_at_ Ews t_dctx (DOT _workspace) p;
         data_at sh (tarray tuchar N) c base;
         match res with
         | Some (t, _) => kstate gv p ox k (Some t)
         | None => kjunk p k
         end).

Definition HDR_S : funspecs :=
  [ ZSTD_buildSeqTable_rle_spec; ZSTD_buildSeqTable_spec; ZSTD_decodeSeqHeaders_spec ].
Definition HDR_G : funspecs := (G_BLK ++ HDR_imports) ++ HDR_S.

(* ===================== bodies ===================== *)

Lemma body_buildSeqTable_rle :
  semax_body Vprog HDR_G f_ZSTD_buildSeqTable_rle ZSTD_buildSeqTable_rle_spec.
Proof.
  start_function.
  destruct (hdr_sk_size k) as [Hs1 Hs2].
  destruct (hdr_sk_ranges k sym H) as [Hb Hn].
  assert_PROP (field_compatible (tarray t_seqSymbol (sk_size k)) [] dt) as Hf by entailer!.
  rewrite (hdr_dt_split Ews dt (sk_size k) 1) by (auto; lia).
  rewrite data__at_singleton_array_eq. Intros.
  forward. forward. forward.
  replace (force_val (sem_binary_operation' Oadd (tptr (Tstruct ___gp_ZSTD_seqSymbol noattr)) tint dt
             (Vint (Int.repr 1)))) with (offset_val 8 dt)
    by (destruct dt; try (destruct Hf; contradiction); reflexivity).
  forward. forward. forward. forward. forward. forward.
  unfold seqspace_at, seqtab_at, seqtab_at_fm. Exists 0. simpl ft_log. simpl ft_cells. change (2 ^ 0) with 1.
  erewrite data_at_singleton_array_eq by reflexivity.
  unfold seqcell; simpl fe_base; simpl fe_nb; simpl fe_sym.
  rewrite !zero_ext_inrange by (rewrite ?Int.unsigned_repr; simpl; rep_lia).
  entailer!.
  destruct (hdr_sk_max_bounds k). unfold fse_ok, fse_rle; simpl. split; [lia|]. split; [reflexivity|].
  repeat constructor; simpl; lia.
Qed.

(* ---------- helpers of body_buildSeqTable ---------- *)

Lemma bst_ptr_at (p: val) (k: seqkind) (tp: val) :
  seq_ptr_at p k tp = data_at Ews (tptr t_seqSymbol) tp (field_address t_dctx (DOT sk_pfield k) p).
Proof. destruct k; unfold seq_ptr_at; simpl; rewrite field_at_data_at; reflexivity. Qed.

Lemma bst_kptr_eq (p: val) (k: seqkind) :
  kptr_ p k = data_at_ Ews (tptr t_seqSymbol) (field_address t_dctx (DOT sk_pfield k) p).
Proof. destruct k; unfold kptr_; simpl; rewrite field_at__data_at_; reflexivity. Qed.

Lemma bst_zg_fold (k: seqkind) (gv: globals) (pb pbits: val) :
  pb = gv (sk_gbase k) -> pbits = gv (sk_gbits k) ->
  data_at Ers (tarray tuint (sk_max k + 1)) (hdr_bvals k) pb *
  data_at Ers (tarray tuchar (sk_max k + 1)) (hdr_nvals k) pbits * hdr_zg_rest k gv |-- zstd_globals gv.
Proof. intros -> ->. rewrite (hdr_zg_split k gv). cancel. Qed.

Lemma bst_ncount_size (b: list Z) (m: Z) (norm: list Z) (lg size: Z) :
  read_ncount b m = Some (norm, lg, size) -> size <= Zlength b.
Proof.
  intros R. unfold read_ncount in R.
  destruct (Zlength b =? 0); [discriminate|].
  destruct (_ >? FSE_TABLELOG_ABSOLUTE_MAX); [discriminate|].
  destruct (ncount_loop _ _ _ _ _ _ _ _ _) as [[[nm rem] q]|]; [|discriminate].
  destruct (negb (rem =? 1)); [discriminate|].
  destruct (Zlength nm >? m + 1); [discriminate|].
  destruct ((q + 7) / 8 >? Zlength b) eqn:L; [discriminate|]. rewrite Z.gtb_ltb, Z.ltb_ge in L.
  inv R. exact L.
Qed.

(* a table field holding a table is at a pointer *)
Lemma bst_seqspace_ptr (sh: share) (k: seqkind) (t: fse_table) (q: val) :
  seqspace_at sh k (Some t) q |-- !! isptr q.
Proof. unfold seqspace_at, seqtab_at, seqtab_at_fm. Intros fm. entailer!. Qed.

(* the table pointer of seq_where is a pointer, wherever the table lives *)
Lemma bst_tp_ptr (gv: globals) (p: val) (ox: option ddx) (k: seqkind) (t: fse_table) (tp: val) (w: tloc)
    (pdef: val) : pdef = gv (sk_gdefault k) ->
  zstd_globals gv * dent_of dent_def gv ox *
  match w with
  | TCtx => !! (tp = ctx_seq k p) && seqspace_at Ews k (Some t) (ctx_seq k p)
  | TDict => !! (ox_seq k ox = Some t /\ tp = dd_seq k (ox_q ox)) && seqspace_at Ews k None (ctx_seq k p)
  | TGlob => !! (t = sk_predef k /\ tp = pdef) && seqspace_at Ews k None (ctx_seq k p)
  end |-- !! is_pointer_or_null tp.
Proof.
  intros Hpdef. destruct w; Intros; subst.
  - sep_apply (bst_seqspace_ptr Ews k t (ctx_seq k p)). Intros. apply prop_right.
    destruct (ctx_seq k p); try contradiction; exact I.
  - rename H into Ho. unfold ox_seq in Ho.
    destruct ox as [x|]; [|discriminate]. unfold ox_ent in Ho. simpl ox_q. unfold dent_of.
    destruct (ddx_ent x) as [st|]; [|discriminate].
    unfold dent_def. destruct (st_huf st) as [ht|]; [|destruct (st_seq st) as [[[a b] c']|]; entailer!].
    destruct (st_seq st) as [[[a b] c']|]; [|discriminate]. Intros.
    destruct k; simpl in Ho; inv Ho.
    + sep_apply (bst_seqspace_ptr Ews KLL t (dd_seq KLL (dx_q x))). Intros. apply prop_right.
      destruct (dd_seq KLL (dx_q x)); try contradiction; exact I.
    + sep_apply (bst_seqspace_ptr Ews KOF t (dd_seq KOF (dx_q x))). Intros. apply prop_right.
      destruct (dd_seq KOF (dx_q x)); try contradiction; exact I.
    + sep_apply (bst_seqspace_ptr Ews KML t (dd_seq KML (dx_q x))). Intros. apply prop_right.
      destruct (dd_seq KML (dx_q x)); try contradiction; exact I.
  - rewrite (hdr_zg_split k gv). unfold hdr_zg_rest, hdr_zg_common.
    destruct k; simpl; entailer!.
Qed.

Lemma bst_tp_ptr' (gv: globals) (p: val) (ox: option ddx) (k: seqkind) (t: fse_table) (tp: val) (w: tloc)
    (pdef: val) (R: mpred) : pdef = gv (sk_gdefault k) ->
  zstd_globals gv * dent_of dent_def gv ox *
  match w with
  | TCtx => !! (tp = ctx_seq k p) && seqspace_at Ews k (Some t) (ctx_seq k p)
  | TDict => !! (ox_seq k ox = Some t /\ tp = dd_seq k (ox_q ox)) && seqspace_at Ews k None (ctx_seq k p)
  | TGlob => !! (t = sk_predef k /\ tp = pdef) && seqspace_at Ews k None (ctx_seq k p)
  end * R |-- !! is_pointer_or_null tp.
Proof.
  intros Hpdef. assert (A := bst_tp_ptr gv p ox k t tp w pdef Hpdef).
  apply derives_trans with (!! is_pointer_or_null tp * TT); [apply sepcon_derives; [exact A | apply TT_right]|].
  rewrite <- (andp_TT (!! is_pointer_or_null tp)) at 1. rewrite sepcon_andp_prop'. apply andp_left1, derives_refl.
Qed.

Lemma bst_shl1 (m: Z) : 0 <= m <= 9 -> Int.shl (Int.repr 1) (Int.repr m) = Int.repr (2 ^ m).
Proof.
  intros Hm. rewrite Int.shl_mul_two_p, Int.unsigned_repr by rep_lia.
  rewrite two_p_equiv, mul_repr. f_equal. lia.
Qed.

(* the byte at offset j of the window, in the array *)
Lemma bst_win_byte (sh: share) (N: Z) (c: list val) (off: Z) (S: list Z) (j: Z) :
  win_ok sh N c off (Zlength S) S -> 0 <= j < Zlength S ->
  Znth (off + j) c = Vint (Int.repr (byte_at S j)) /\ 0 <= byte_at S j < 256.
Proof.
  intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) Hj.
  assert (E: Znth (off + j) c = Znth j (sublist off (off + Zlength S) c))
    by (rewrite Znth_sublist by lia; f_equal; lia).
  rewrite E, H8, Znth_map by lia. unfold byte_at.
  assert (Hn: nth (Z.to_nat j) S 0 = Znth j S).
  { unfold Znth. destruct (Z_lt_dec j 0); [lia|]. reflexivity. }
  rewrite Hn. split; [reflexivity|].
  unfold bytes_ok in H7. rewrite Forall_forall in H7. apply H7. apply Znth_In; lia.
Qed.

Lemma bst_fa (N i: Z) (base: val) : 0 <= i < N -> field_compatible (tarray tuchar N) [] base ->
  offset_val i base = field_address (tarray tuchar N) (SUB i) base.
Proof. intros. rewrite arr_field_address by auto. simpl. f_equal. lia. Qed.

(* do { c } while (0) as Clight's Sloop c Sbreak *)
Ltac bst_reassoc := repeat match goal with
  |- semax _ _ (Ssequence (Ssequence _ _) _) _ => apply -> seq_assoc end.
Ltac bst_once_body P :=
  first [ forward_if P;
          [ contradiction
          | forward; try (apply andp_left2, derives_refl)
          | forward; apply andp_left2, derives_refl ]
        | forward; apply andp_left2, derives_refl ].
Ltac bst_once_skip := bst_reassoc;
  match goal with |- semax _ ?P (Ssequence (Sloop _ Sbreak) _) _ =>
    forward_loop P break: P; [apply andp_left2, derives_refl | bst_once_body P | ] end.
(* the error exit of RETURN_ERROR_IF: four empty loops, then the return *)
Ltac bst_err_exit := bst_once_skip; bst_once_skip; bst_once_skip; bst_once_skip; forward.
(* the post of an error return: the model says None (E), the table becomes junk *)
Ltac bst_err_post E Hf :=
  rewrite E;
  match goal with |- context [Vlong (Int64.repr (- ?n)) = Vlong (Int64.repr _)] =>
    Exists (Int64.unsigned (Int64.repr (- n))) end;
  rewrite Int64.repr_unsigned;
  match goal with |- context [kstate ?gv ?p ?ox ?k ?o] => sep_apply (hdr_kstate_junk gv p ox k o Hf) end;
  entailer!.

(* ---------- helpers of body_buildSeqTable (C-result spec) ---------- *)

Lemma bst2_seqspace_ok (sh: share) (k: seqkind) (t: fse_table) (q: val) :
  seqspace_at sh k (Some t) q |-- !! fse_ok k t.
Proof. unfold seqspace_at, seqtab_at, seqtab_at_fm. Intros fm. entailer!. Qed.

Lemma bst2_rle_ok (k: seqkind) (sym: Z) : 0 <= sym <= sk_max k -> fse_ok k (fse_rle sym).
Proof.
  intros H. destruct (hdr_sk_max_bounds k). unfold fse_ok, fse_rle; simpl. split; [lia|]. split; [reflexivity|].
  repeat constructor; simpl; lia.
Qed.

Lemma bst2_predef_ok (k: seqkind) : fse_ok k (sk_predef k).
Proof. destruct predef_ok as (A & B & C). destruct k; assumption. Qed.

Lemma bst2_comp_none (k: seqkind) (o: option fse_table) (s: list Z) :
  (forall x, read_ncount s (sk_max k) = Some x -> @None (list Z * Z * Z) = Some x) ->
  seq_table 2 (sk_predef k) o (sk_max k) (sk_maxlog k) s = None.
Proof.
  intros H. unfold seq_table. simpl Z.eqb. cbv iota beta.
  destruct (read_ncount s (sk_max k)) as [x|]; [discriminate (H x eq_refl) | reflexivity].
Qed.

Lemma bst2_comp_some (k: seqkind) (o: option fse_table) (s: list Z) (norm: list Z) (lg size: Z) :
  (forall x, read_ncount s (sk_max k) = Some x -> Some (norm, lg, size) = Some x) ->
  forall x, seq_table 2 (sk_predef k) o (sk_max k) (sk_maxlog k) s = Some x ->
  lg <= sk_maxlog k /\ x = (fse_build norm lg, size).
Proof.
  intros H x E. unfold seq_table in E. simpl Z.eqb in E. cbv iota beta in E.
  destruct (read_ncount s (sk_max k)) as [y|]; [|discriminate].
  specialize (H y eq_refl). inv H.
  destruct (lg >? sk_maxlog k) eqn:G; [discriminate|]. inv E.
  rewrite Z.gtb_ltb, Z.ltb_ge in G. auto.
Qed.

(* the exact model: modes 0, 1, 3 read no description, as the format model's seq_table; mode 2 reads it with
   zstd's FSE_readNCount (ExHuf.x_ncount, the reading FSE_readNCount_spec gives exactly) *)
Lemma xst_eq (m: Z) (pre: fse_table) (prev: option fse_table) (mx ml: Z) (b: list Z) :
  m = 0 \/ m = 1 \/ m = 3 -> x_seq_table ncount_c m pre prev mx ml b = seq_table m pre prev mx ml b.
Proof. intros [->|[->| ->]]; reflexivity. Qed.

Lemma xst_2 (pre: fse_table) (prev: option fse_table) (mx ml: Z) (b: list Z) :
  x_seq_table ncount_c 2 pre prev mx ml b =
  match ExHuf.x_ncount b mx with
  | None => None
  | Some (norm, log, size) => if log >? ml then None else Some (fse_build norm log, size)
  end.
Proof. reflexivity. Qed.

(* the post of an error return: zstd's result is None (and the exact model's), the table becomes junk *)
Ltac bst2_err_post E Hf :=
  match goal with |- context [Vlong (Int64.repr (- ?n)) = Vlong (Int64.repr _)] =>
    Exists (Int64.unsigned (Int64.repr (- n))) end;
  Exists (@None (fse_table * Z));
  rewrite Int64.repr_unsigned;
  match goal with |- context [kstate ?gv ?p ?ox ?k ?o] => sep_apply (hdr_kstate_junk gv p ox k o Hf) end;
  entailer!; try (intros ?x ?Hx; rewrite E in Hx; discriminate);
  try (rewrite xst_eq by auto; rewrite E; reflexivity).

Lemma body_buildSeqTable :
  semax_body Vprog HDR_G f_ZSTD_buildSeqTable ZSTD_buildSeqTable_spec.
Proof.
  start_function. rename H3 into Hoo. rename H4 into Hslen.
  remember (gv (sk_gbase k)) as pb eqn:Hpb. remember (gv (sk_gbits k)) as pbits eqn:Hpbits.
  remember (gv (sk_gdefault k)) as pdef eqn:Hpdef.
  pose proof H2 as Hw. destruct H2 as (Hrs & Hoff & HoffN & HN & Hc & _ & Hbytes & Hsub).
  destruct (hdr_sk_max_bounds k) as [Hmk Hlk]. destruct (hdr_sk_size k) as [Hs1 Hs2].
  assert_PROP (field_compatible (tarray tuchar N) [] base) as Hfb by entailer!.
  assert_PROP (field_compatible t_dctx (DOT _workspace) p) as Hfp by entailer!.
  assert (Hfp0: field_compatible t_dctx [] p)
    by (destruct Hfp as (A & B & C & D & _); repeat split; auto).
  forward.
  forward_switch'.
  - (* 1: RLE *)
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_loop (PROPx P (LOCALx Q (SEPx R))) break: (PROPx ((1 <= Zlength s) :: P) (LOCALx Q (SEPx R))) end.
    { apply andp_left2, derives_refl. }
    { forward_if.
      { bst_err_exit.
        assert (Hz: Zlength s = 0).
        { match goal with H: Int64.repr (Zlength s) = Int64.zero |- _ =>
            apply (f_equal Int64.unsigned) in H; rewrite Int64.unsigned_repr in H by rep_lia; exact H end. }
        assert (E: seq_table 1 (sk_predef k) o (sk_max k) (sk_maxlog k) s = None)
          by (unfold seq_table; rewrite Hz; reflexivity).
        bst2_err_post E Hfp0. }
      { forward. entailer!. pose proof (Zlength_nonneg s). destruct (Z.eq_dec (Zlength s) 0) as [Ez|]; [rewrite Ez in H2; contradiction | lia]. } }
    Intros.
    destruct (bst_win_byte sh N c off s 0 Hw ltac:(lia)) as [Hb0 Hb0r].
    rewrite Z.add_0_r in Hb0.
    assert (Hb0u: @Znth val Vundef off c = Vint (Int.repr (byte_at s 0))) by exact Hb0.
    rewrite (bst_fa N off base) by (auto; lia).
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_loop (PROPx P (LOCALx Q (SEPx R)))
        break: (PROPx ((byte_at s 0 <= sk_max k) :: P) (LOCALx Q (SEPx R))) end.
    { apply andp_left2, derives_refl. }
    { forward.
      { rewrite Hb0u. entailer!. rep_lia. }
      rewrite Hb0u.
      forward.
      forward_if.
      { bst_err_exit.
        assert (E: seq_table 1 (sk_predef k) o (sk_max k) (sk_maxlog k) s = None).
        { unfold seq_table. simpl Z.eqb. cbv iota beta.
          replace (Zlength s <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
          replace (byte_at s 0 >? sk_max k) with true by (symmetry; apply Z.gtb_lt; lia). reflexivity. }
        bst2_err_post E Hfp0. }
      { forward. entailer!. } }
    Intros.
    forward.
    { rewrite Hb0u. entailer!. rep_lia. }
    rewrite Hb0u.
    rewrite (hdr_zg_split k gv), <- Hpb, <- Hpbits. Intros.
    destruct (hdr_sk_ranges k (byte_at s 0) ltac:(lia)) as [Hbr Hnr].
    forward.
    { entailer!. rewrite hdr_bvals_nth by lia. exact I. }
    rewrite hdr_bvals_nth by lia.
    forward.
    { entailer!. rewrite hdr_nvals_nth by lia. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    rewrite hdr_nvals_nth by lia.
    forward.
    sep_apply (hdr_kstate_junk gv p ox k o Hfp0). unfold kjunk. rewrite bst_kptr_eq. unfold seqspace_at. Intros.
    forward_call (k, byte_at s 0, ctx_seq k p).
    forward. forward.
    assert (E: seq_table 1 (sk_predef k) o (sk_max k) (sk_maxlog k) s = Some (fse_rle (byte_at s 0), 1)).
    { unfold seq_table. simpl Z.eqb. cbv iota beta.
      replace (Zlength s <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
      replace (byte_at s 0 >? sk_max k) with false by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; lia). reflexivity. }
    assert (HXs: Some (fse_rle (byte_at s 0), 1) = x_seq_table ncount_c 1 (sk_predef k) o (sk_max k) (sk_maxlog k) s)
      by (rewrite xst_eq by auto; rewrite E; reflexivity).
    Exists 1 (Some (fse_rle (byte_at s 0), 1)).
    assert (Hrok := bst2_rle_ok k (byte_at s 0) ltac:(lia)).
    unfold kstate, seq_where. Exists (ctx_seq k p) TCtx. rewrite bst_ptr_at.
    sep_apply (bst_zg_fold k gv (gv (sk_gbase k)) (gv (sk_gbits k)) eq_refl eq_refl).
    entailer!; intros x Hx; rewrite E in Hx; exact Hx.
  - (* 0: predefined *)
    sep_apply (hdr_kstate_junk gv p ox k o Hfp0). unfold kjunk. rewrite bst_kptr_eq. Intros.
    forward. forward.
    assert (HXs: Some (sk_predef k, 0) = x_seq_table ncount_c 0 (sk_predef k) o (sk_max k) (sk_maxlog k) s) by reflexivity.
    Exists 0 (Some (sk_predef k, 0)). pose proof (bst2_predef_ok k) as Hpok.
    unfold kstate, seq_where. Exists (gv (sk_gdefault k)) TGlob. rewrite bst_ptr_at.
    entailer!.
  - (* 3: repeat *)
    destruct o as [t|]; simpl fe_of.
    2: {
      match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
        forward_loop (PROPx P (LOCALx Q (SEPx R))) break: (PROPx (False :: P) (LOCALx Q (SEPx R))) end.
      { apply andp_left2, derives_refl. }
      { forward_if.
        { bst_err_exit.
          assert (E: seq_table 3 (sk_predef k) None (sk_max k) (sk_maxlog k) s = None) by reflexivity.
          bst2_err_post E Hfp0. }
        { exfalso; apply H2; reflexivity. } } }
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_loop (PROPx P (LOCALx Q (SEPx R))) break: (PROPx P (LOCALx Q (SEPx R))) end.
    { apply andp_left2, derives_refl. }
    { forward_if.
      { exfalso; apply Int.one_not_zero; exact H2. }
      { forward. entailer!. } }
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (EX v: Z, PROPx P (LOCALx (temp _t'1 (Vint (Int.repr v)) :: Q) (SEPx R))) end.
    { forward. Exists (if zlt 24 nbSeq then 1 else 0). destruct (zlt 24 nbSeq); entailer!. }
    { forward. Exists 0. entailer!. }
    Intros v.
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx Q (SEPx R))) end.
    { unfold kstate, seq_where. Intros tp w. rewrite bst_ptr_at.
      rewrite <- Hpdef.
      assert_PROP (is_pointer_or_null tp) as Htp.
      { go_lower. eapply derives_trans; [|apply (bst_tp_ptr' gv p ox k t tp w pdef TT); exact Hpdef]. cancel. }
      forward. forward.
      { entailer!. rewrite bst_shl1 by lia. rewrite Int.signed_repr by rep_lia.
        change (Int.unsigned Int.iwordsize) with 32. rep_lia. }
      rewrite bst_shl1 by lia. rewrite add_repr, Int.signed_repr by rep_lia.
      match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
        forward_loop (PROPx P (LOCALx Q (SEPx R))) break: (PROPx P (LOCALx Q (SEPx R))) end.
      { apply andp_left2, derives_refl. }
      2: { unfold kstate, seq_where. rewrite <- Hpdef. Exists tp w. rewrite bst_ptr_at. entailer!. }
      forward. forward.
      match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
        forward_loop (EX i: int64, PROPx P (LOCALx (temp __pos (Vlong i) :: Q) (SEPx R)))
          continue: (EX i: int64, PROPx P (LOCALx (temp __pos (Vlong i) :: Q) (SEPx R)))
          break: (PROPx P (LOCALx Q (SEPx R))) end.
      { forward. Exists (Int64.repr 0). entailer!. }
      { Intros i. forward_if.
        { match goal with |- semax _ ?Pre _ _ => forward_loop Pre break: Pre end.
          { apply andp_left2, derives_refl. }
          { forward. apply andp_left2, derives_refl. }
          Exists i. entailer!. }
        { forward. entailer!. } }
      { Intros i. forward. Exists (Int64.add i (Int64.repr 64)). entailer!. }
      { forward. try entailer!. } }
    { forward. entailer!. }
    forward.
    assert (HXs: Some (t, 0) = x_seq_table ncount_c 3 (sk_predef k) (Some t) (sk_max k) (sk_maxlog k) s) by reflexivity.
    Exists 0 (Some (t, 0)). entailer!.
  - (* 2: compressed *)
    assert (Hs28: Zlength s <= 2 ^ 28) by (unfold ZSTD_BLOCKSIZE_MAX in Hslen; lia).
    forward_call (gv, Tsh, v_norm, 53, Tsh, v_max, Tsh, v_tableLog, sk_max k, sh, base, N, c, off, s).
    Intros vret. destruct vret as [[r nc] res]. simpl fst in *. simpl snd in *.
    destruct res as [[[norm lg] size]|].
    2: {
      match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
        forward_loop (PROPx P (LOCALx Q (SEPx R))) break: (PROPx (False :: P) (LOCALx Q (SEPx R))) end.
      { apply andp_left2, derives_refl. }
      { forward_call r. rewrite H5. forward_if.
        { bst_err_exit.
          assert (E: seq_table 2 (sk_predef k) o (sk_max k) (sk_maxlog k) s = None)
            by (apply bst2_comp_none; auto).
          assert (HXs: None = x_seq_table ncount_c 2 (sk_predef k) o (sk_max k) (sk_maxlog k) s)
            by (rewrite xst_2; match goal with h: None = ExHuf.x_ncount _ _ |- _ => rewrite <- h end; reflexivity).
          bst2_err_post E Hfp0. }
        { exfalso; apply Int.one_not_zero; assumption. } } }
    destruct H5 as (-> & Hsz & Hok & Hsubn). Intros.
    pose proof (bst2_comp_some k o s norm lg size H4) as Hmod.
    assert (Hnerr: is_error_code size = false) by (unfold is_error_code; apply Z.ltb_ge; lia).
    destruct Hok as (Hlg & Hnl & Hrng & Hsum).
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_loop (PROPx P (LOCALx Q (SEPx R))) break: (PROPx P (LOCALx Q (SEPx R))) end.
    { apply andp_left2, derives_refl. }
    { forward_call size. rewrite Hnerr. forward_if.
      { exfalso; auto. }
      { forward. entailer!. } }
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_loop (PROPx P (LOCALx Q (SEPx R)))
        break: (PROPx ((lg <= sk_maxlog k) :: P) (LOCALx Q (SEPx R))) end.
    { apply andp_left2, derives_refl. }
    { forward. forward_if.
      { bst_err_exit.
        assert (E: seq_table 2 (sk_predef k) o (sk_max k) (sk_maxlog k) s = None).
        { destruct (seq_table 2 (sk_predef k) o (sk_max k) (sk_maxlog k) s) as [x|] eqn:Ex; [|reflexivity].
          destruct (Hmod x eq_refl). lia. }
        assert (HXs: None = x_seq_table ncount_c 2 (sk_predef k) o (sk_max k) (sk_maxlog k) s)
          by (rewrite xst_2; match goal with h: Some _ = ExHuf.x_ncount _ _ |- _ => rewrite <- h end;
              rewrite (proj2 (Z.gtb_lt _ _)) by lia; reflexivity).
        bst2_err_post E Hfp0. }
      { forward. entailer!. } }
    Intros.
    forward. forward.
    sep_apply (hdr_kstate_junk gv p ox k o Hfp0). unfold kjunk. rewrite bst_kptr_eq. unfold seqspace_at. Intros.
    assert (Hws: field_at_ Ews t_dctx (DOT _workspace) p =
                 data_at_ Ews (tarray tuint 640) (field_address t_dctx (DOT _workspace) p))
      by (rewrite field_at__data_at_; reflexivity).
    assert (Hn53: data_at Tsh (tarray tshort 53) nc v_norm = data_at Tsh (tarray tshort (Zlength nc)) nc v_norm)
      by (rewrite H3; reflexivity).
    specialize (Hsubn ltac:(lia)).
    assert (HXs: Some (fse_build norm lg, size) = x_seq_table ncount_c 2 (sk_predef k) o (sk_max k) (sk_maxlog k) s)
      by (rewrite xst_2; match goal with h: Some _ = ExHuf.x_ncount _ _ |- _ => rewrite <- h end;
          rewrite Z.gtb_ltb, (proj2 (Z.ltb_ge _ _)) by lia; reflexivity).
    rewrite Hws, Hn53.
    destruct k; subst pb pbits pdef;
    match goal with |- context [ctx_seq ?kk p] =>
      forward_call (gv, kk, Ews, ctx_seq kk p, Tsh, v_norm, nc, norm, lg, Ews,
                    field_address t_dctx (DOT _workspace) p, 640) end.
    all: try solve [unfold ncount_ok; repeat split; auto; lia].
    all: rewrite <- bst_kptr_eq; unfold kptr_; simpl sk_pfield;
      match goal with |- context [seqspace_at Ews ?kk (Some ?t) ?q] =>
        assert_PROP (fse_ok kk t) as Hfok by (sep_apply (bst2_seqspace_ok Ews kk t q); entailer!) end;
      forward; forward; Exists size (Some (fse_build norm lg, size)); unfold kstate, seq_where;
      match goal with |- context [ctx_seq ?kk ?pp] => Exists (ctx_seq kk pp) TCtx end;
      unfold seq_ptr_at; rewrite <- Hws, <- Hn53; entailer!;
      intros x Hx; destruct (Hmod x Hx) as [_ ->]; reflexivity.
  - (* default *)
    exfalso. rewrite !Int.unsigned_repr in * by rep_lia. lia.
Qed.

Lemma hdr_tabs_seq_eq (gv: globals) (p: val) (ox: option ddx) (os: option (fse_table * fse_table * fse_table))
    (fe: Z) :
  tabs_seq gv p ox os fe =
  field_at Ews t_dctx (DOT _fseEntropy) (Vint (Int.repr fe)) p *
  kstate gv p ox KLL (seq_of KLL os) * kstate gv p ox KOF (seq_of KOF os) * kstate gv p ox KML (seq_of KML os).
Proof.
  destruct os as [[[a b] c]|]; unfold tabs_seq, kstate, kjunk, kptr_, seq_of; simpl; apply pred_ext; cancel.
Qed.

Lemma hdr_seq_junk_eq (p: val) :
  seq_junk p = field_at_ Ews t_dctx (DOT _fseEntropy) p * kjunk p KLL * kjunk p KOF * kjunk p KML.
Proof. unfold seq_junk, kjunk, kptr_; simpl; apply pred_ext; cancel. Qed.

(* ---------- the model of ZSTD_decodeSeqHeaders, cut where the C checks ---------- *)

(* nbSeq, the bytes it takes, and whether they are there *)
Definition hdr_head (S: list Z) : Z * Z * bool :=
  let b0 := byte_at S 0 in
  if b0 <=? 127 then (b0, 1, true)
  else if b0 =? 255 then (le_field S 1 2 + LONGNBSEQ, 3, 3 <=? Zlength S)
  else ((b0 - 128) * 256 + byte_at S 1, 2, 2 <=? Zlength S).

(* the tables after the nbSeq field (pos bytes) *)
Definition hdr_tables (os: option (fse_table * fse_table * fse_table)) (S: list Z) (nbSeq pos: Z)
    : option (Z * option (fse_table * fse_table * fse_table) * Z) :=
  let modes := byte_at S pos in
  match seq_table (Z.shiftr modes 6) LL_predef (seq_of KLL os) MaxLL LLFSELog (skipn (Z.to_nat (pos + 1)) S) with
  | None => None
  | Some (tLL, k1) =>
    match seq_table (Z.land (Z.shiftr modes 4) 3) OF_predef (seq_of KOF os) MaxOff OffFSELog
            (skipn (Z.to_nat (pos + 1 + k1)) S) with
    | None => None
    | Some (tOF, k2) =>
      match seq_table (Z.land (Z.shiftr modes 2) 3) ML_predef (seq_of KML os) MaxML MLFSELog
              (skipn (Z.to_nat (pos + 1 + k1 + k2)) S) with
      | None => None
      | Some (tML, k3) => Some (nbSeq, Some (tLL, tOF, tML), pos + 1 + k1 + k2 + k3)
      end
    end
  end.

Lemma hdr_dsh_eq (os: option (fse_table * fse_table * fse_table)) (S: list Z) :
  1 <= Zlength S ->
  decode_seq_header os S =
  let '(nbSeq, pos, ok) := hdr_head S in
  if negb ok then None else
  if nbSeq =? 0 then (if pos =? Zlength S then Some (0, os, pos) else None) else
  if pos + 1 >? Zlength S then None else
  if negb (Z.land (byte_at S pos) 3 =? 0) then None else
  hdr_tables os S nbSeq pos.
Proof.
  intros H. unfold decode_seq_header, hdr_head, hdr_tables.
  destruct (Zlength S <? 1) eqn:E; [apply Z.ltb_lt in E; lia|].
  destruct os as [[[a b] c]|]; reflexivity.
Qed.

(* the exact model ExBlock.x_seq_header (BlkIface.xb_seq_header), cut at the same places *)
Definition hdr_xtables (os: option (fse_table * fse_table * fse_table)) (S: list Z) (nbSeq pos: Z)
    : option (Z * option (fse_table * fse_table * fse_table) * Z) :=
  let modes := byte_at S pos in
  match x_seq_table ncount_c (Z.shiftr modes 6) LL_predef (seq_of KLL os) MaxLL LLFSELog
          (skipn (Z.to_nat (pos + 1)) S) with
  | None => None
  | Some (tLL, k1) =>
    match x_seq_table ncount_c (Z.land (Z.shiftr modes 4) 3) OF_predef (seq_of KOF os) MaxOff OffFSELog
            (skipn (Z.to_nat (pos + 1 + k1)) S) with
    | None => None
    | Some (tOF, k2) =>
      match x_seq_table ncount_c (Z.land (Z.shiftr modes 2) 3) ML_predef (seq_of KML os) MaxML MLFSELog
              (skipn (Z.to_nat (pos + 1 + k1 + k2)) S) with
      | None => None
      | Some (tML, k3) => Some (nbSeq, Some (tLL, tOF, tML), pos + 1 + k1 + k2 + k3)
      end
    end
  end.

Lemma hdr_xsh_eq (os: option (fse_table * fse_table * fse_table)) (S: list Z) :
  1 <= Zlength S ->
  xb_seq_header os S =
  let '(nbSeq, pos, ok) := hdr_head S in
  if negb ok then None else
  if nbSeq =? 0 then (if pos =? Zlength S then Some (0, os, pos) else None) else
  if pos + 1 >? Zlength S then None else
  if negb (Z.land (byte_at S pos) 3 =? 0) then None else
  hdr_xtables os S nbSeq pos.
Proof.
  intros H. unfold xb_seq_header, x_seq_header, hdr_head, hdr_xtables.
  destruct (Zlength S <? 1) eqn:E; [apply Z.ltb_lt in E; lia|].
  destruct os as [[[a b] c]|]; reflexivity.
Qed.

(* the exact outcome from the three ZSTD_buildSeqTable results (given as Some r = Some (model), the form in
   which the proof keeps them out of VST's substitutions) *)
Lemma hdr_xtables_none1 (os: option (fse_table * fse_table * fse_table)) (S: list Z) (nb pos: Z) :
  let modes := byte_at S pos in
  Some (@None (fse_table * Z)) = Some (x_seq_table ncount_c (Z.shiftr modes 6) LL_predef (seq_of KLL os) MaxLL LLFSELog
                                        (skipn (Z.to_nat (pos + 1)) S)) ->
  hdr_xtables os S nb pos = None.
Proof.
  intros modes H1. injection H1 as H1. unfold hdr_xtables. fold modes. rewrite <- H1. reflexivity.
Qed.

Lemma hdr_xtables_none2 (os: option (fse_table * fse_table * fse_table)) (S: list Z) (nb pos: Z)
    (tLL: fse_table) (k1: Z) :
  let modes := byte_at S pos in
  Some (Some (tLL, k1)) = Some (x_seq_table ncount_c (Z.shiftr modes 6) LL_predef (seq_of KLL os) MaxLL LLFSELog
                                  (skipn (Z.to_nat (pos + 1)) S)) ->
  Some (@None (fse_table * Z)) = Some (x_seq_table ncount_c (Z.land (Z.shiftr modes 4) 3) OF_predef (seq_of KOF os) MaxOff
                                        OffFSELog (skipn (Z.to_nat (pos + 1 + k1)) S)) ->
  hdr_xtables os S nb pos = None.
Proof.
  intros modes H1 H2. injection H1 as H1. injection H2 as H2. unfold hdr_xtables. fold modes.
  rewrite <- H1. rewrite <- H2. reflexivity.
Qed.

Lemma hdr_xtables_none3 (os: option (fse_table * fse_table * fse_table)) (S: list Z) (nb pos: Z)
    (tLL tOF: fse_table) (k1 k2: Z) :
  let modes := byte_at S pos in
  Some (Some (tLL, k1)) = Some (x_seq_table ncount_c (Z.shiftr modes 6) LL_predef (seq_of KLL os) MaxLL LLFSELog
                                  (skipn (Z.to_nat (pos + 1)) S)) ->
  Some (Some (tOF, k2)) = Some (x_seq_table ncount_c (Z.land (Z.shiftr modes 4) 3) OF_predef (seq_of KOF os) MaxOff
                                  OffFSELog (skipn (Z.to_nat (pos + 1 + k1)) S)) ->
  Some (@None (fse_table * Z)) = Some (x_seq_table ncount_c (Z.land (Z.shiftr modes 2) 3) ML_predef (seq_of KML os) MaxML
                                        MLFSELog (skipn (Z.to_nat (pos + 1 + k1 + k2)) S)) ->
  hdr_xtables os S nb pos = None.
Proof.
  intros modes H1 H2 H3. injection H1 as H1. injection H2 as H2. injection H3 as H3. unfold hdr_xtables.
  fold modes. rewrite <- H1. rewrite <- H2. rewrite <- H3. reflexivity.
Qed.

Lemma hdr_xtables_some (os: option (fse_table * fse_table * fse_table)) (S: list Z) (nb pos: Z)
    (tLL tOF tML: fse_table) (k1 k2 k3: Z) :
  let modes := byte_at S pos in
  Some (Some (tLL, k1)) = Some (x_seq_table ncount_c (Z.shiftr modes 6) LL_predef (seq_of KLL os) MaxLL LLFSELog
                                  (skipn (Z.to_nat (pos + 1)) S)) ->
  Some (Some (tOF, k2)) = Some (x_seq_table ncount_c (Z.land (Z.shiftr modes 4) 3) OF_predef (seq_of KOF os) MaxOff
                                  OffFSELog (skipn (Z.to_nat (pos + 1 + k1)) S)) ->
  Some (Some (tML, k3)) = Some (x_seq_table ncount_c (Z.land (Z.shiftr modes 2) 3) ML_predef (seq_of KML os) MaxML
                                  MLFSELog (skipn (Z.to_nat (pos + 1 + k1 + k2)) S)) ->
  hdr_xtables os S nb pos = Some (nb, Some (tLL, tOF, tML), pos + 1 + k1 + k2 + k3).
Proof.
  intros modes H1 H2 H3. injection H1 as H1. injection H2 as H2. injection H3 as H3. unfold hdr_xtables.
  fold modes. rewrite <- H1. rewrite <- H2. rewrite <- H3. reflexivity.
Qed.

(* ---------- zstd's tables agree with the model's whenever the model reads them ---------- *)

Lemma hdr_seqs_ok_k (os: option (fse_table * fse_table * fse_table)) (k: seqkind) :
  seqs_ok os -> match seq_of k os with Some t => fse_ok k t | None => True end.
Proof. destruct os as [[[a b] c]|]; [intros (H1 & H2 & H3); destruct k; auto | auto]. Qed.

Lemma hdr_tables_ok (os: option (fse_table * fse_table * fse_table)) (S: list Z) (nb pos: Z)
    (tLL tOF tML: fse_table) (k1 k2 k3: Z) :
  let modes := byte_at S pos in
  (forall x, seq_table (Z.shiftr modes 6) LL_predef (seq_of KLL os) MaxLL LLFSELog
               (skipn (Z.to_nat (pos + 1)) S) = Some x -> Some (tLL, k1) = Some x) ->
  (forall x, seq_table (Z.land (Z.shiftr modes 4) 3) OF_predef (seq_of KOF os) MaxOff OffFSELog
               (skipn (Z.to_nat (pos + 1 + k1)) S) = Some x -> Some (tOF, k2) = Some x) ->
  (forall x, seq_table (Z.land (Z.shiftr modes 2) 3) ML_predef (seq_of KML os) MaxML MLFSELog
               (skipn (Z.to_nat (pos + 1 + k1 + k2)) S) = Some x -> Some (tML, k3) = Some x) ->
  forall x, hdr_tables os S nb pos = Some x -> Some (nb, Some (tLL, tOF, tML), pos + 1 + k1 + k2 + k3) = Some x.
Proof.
  intros modes H1 H2 H3 x. unfold hdr_tables. fold modes.
  destruct (seq_table (Z.shiftr modes 6) _ _ _ _ _) as [[a1 b1]|] eqn:E1; [|discriminate].
  specialize (H1 _ eq_refl). inv H1.
  destruct (seq_table (Z.land (Z.shiftr modes 4) 3) _ _ _ _ _) as [[a2 b2]|] eqn:E2; [|discriminate].
  specialize (H2 _ eq_refl). inv H2.
  destruct (seq_table (Z.land (Z.shiftr modes 2) 3) _ _ _ _ _) as [[a3 b3]|] eqn:E3; [|discriminate].
  specialize (H3 _ eq_refl). inv H3. auto.
Qed.

Lemma hdr_tables_none1 (os: option (fse_table * fse_table * fse_table)) (S: list Z) (nb pos: Z) :
  let modes := byte_at S pos in
  (forall x, seq_table (Z.shiftr modes 6) LL_predef (seq_of KLL os) MaxLL LLFSELog
               (skipn (Z.to_nat (pos + 1)) S) = Some x -> @None (fse_table * Z) = Some x) ->
  hdr_tables os S nb pos = None.
Proof.
  intros modes H1. unfold hdr_tables. fold modes.
  destruct (seq_table (Z.shiftr modes 6) _ _ _ _ _) as [x|] eqn:E1; [discriminate (H1 x eq_refl) | auto].
Qed.

Lemma hdr_tables_none2 (os: option (fse_table * fse_table * fse_table)) (S: list Z) (nb pos: Z)
    (tLL: fse_table) (k1: Z) :
  let modes := byte_at S pos in
  (forall x, seq_table (Z.shiftr modes 6) LL_predef (seq_of KLL os) MaxLL LLFSELog
               (skipn (Z.to_nat (pos + 1)) S) = Some x -> Some (tLL, k1) = Some x) ->
  (forall x, seq_table (Z.land (Z.shiftr modes 4) 3) OF_predef (seq_of KOF os) MaxOff OffFSELog
               (skipn (Z.to_nat (pos + 1 + k1)) S) = Some x -> @None (fse_table * Z) = Some x) ->
  hdr_tables os S nb pos = None.
Proof.
  intros modes H1 H2. unfold hdr_tables. fold modes.
  destruct (seq_table (Z.shiftr modes 6) _ _ _ _ _) as [[a1 b1]|] eqn:E1; [|auto].
  specialize (H1 _ eq_refl). inv H1.
  destruct (seq_table (Z.land (Z.shiftr modes 4) 3) _ _ _ _ _) as [x|] eqn:E2; [discriminate (H2 x eq_refl) | auto].
Qed.

Lemma hdr_tables_none3 (os: option (fse_table * fse_table * fse_table)) (S: list Z) (nb pos: Z)
    (tLL tOF: fse_table) (k1 k2: Z) :
  let modes := byte_at S pos in
  (forall x, seq_table (Z.shiftr modes 6) LL_predef (seq_of KLL os) MaxLL LLFSELog
               (skipn (Z.to_nat (pos + 1)) S) = Some x -> Some (tLL, k1) = Some x) ->
  (forall x, seq_table (Z.land (Z.shiftr modes 4) 3) OF_predef (seq_of KOF os) MaxOff OffFSELog
               (skipn (Z.to_nat (pos + 1 + k1)) S) = Some x -> Some (tOF, k2) = Some x) ->
  (forall x, seq_table (Z.land (Z.shiftr modes 2) 3) ML_predef (seq_of KML os) MaxML MLFSELog
               (skipn (Z.to_nat (pos + 1 + k1 + k2)) S) = Some x -> @None (fse_table * Z) = Some x) ->
  hdr_tables os S nb pos = None.
Proof.
  intros modes H1 H2 H3. unfold hdr_tables. fold modes.
  destruct (seq_table (Z.shiftr modes 6) _ _ _ _ _) as [[a1 b1]|] eqn:E1; [|auto].
  specialize (H1 _ eq_refl). inv H1.
  destruct (seq_table (Z.land (Z.shiftr modes 4) 3) _ _ _ _ _) as [[a2 b2]|] eqn:E2; [|auto].
  specialize (H2 _ eq_refl). inv H2.
  destruct (seq_table (Z.land (Z.shiftr modes 2) 3) _ _ _ _ _) as [x|] eqn:E3; [discriminate (H3 x eq_refl) | auto].
Qed.

Lemma hdr_seq_table_used (mode: Z) (pre: fse_table) (prev: option fse_table) (mx mlog: Z) (b: list Z)
    (t: fse_table) (k: Z) :
  seq_table mode pre prev mx mlog b = Some (t, k) -> k <= Zlength b.
Proof.
  pose proof (Zlength_nonneg b). unfold seq_table.
  destruct (mode =? 0); [intros E; inv E; lia|].
  destruct (mode =? 1).
  { destruct (Zlength b <? 1) eqn:L; [discriminate|]. apply Z.ltb_ge in L.
    destruct (byte_at b 0 >? mx); [discriminate|]. intros E; inv E; lia. }
  destruct (mode =? 3); [destruct prev; intros E; inv E; lia|].
  destruct (read_ncount b mx) as [[[norm lg] size]|] eqn:R; [|discriminate].
  destruct (lg >? mlog); [discriminate|]. intros E; inv E.
  unfold read_ncount in R.
  destruct (Zlength b =? 0); [discriminate|].
  destruct (_ >? FSE_TABLELOG_ABSOLUTE_MAX); [discriminate|].
  destruct (ncount_loop _ _ _ _ _ _ _ _ _) as [[[nm rem] q]|]; [|discriminate].
  destruct (negb (rem =? 1)); [discriminate|].
  destruct (Zlength nm >? mx + 1); [discriminate|].
  destruct ((q + 7) / 8 >? Zlength b) eqn:L; [discriminate|]. rewrite Z.gtb_ltb, Z.ltb_ge in L.
  inv R. exact L.
Qed.

Lemma hdr_to_junk (gv: globals) (p: val) (ox: option ddx) (fe: Z) (o1 o2 o3: option fse_table) :
  field_compatible t_dctx [] p ->
  field_at Ews t_dctx (DOT _fseEntropy) (Vint (Int.repr fe)) p *
  kstate gv p ox KLL o1 * kstate gv p ox KOF o2 * kstate gv p ox KML o3 |-- seq_junk p.
Proof.
  intros Hf. rewrite hdr_seq_junk_eq.
  sep_apply (hdr_kstate_junk gv p ox KLL o1 Hf). sep_apply (hdr_kstate_junk gv p ox KOF o2 Hf).
  sep_apply (hdr_kstate_junk gv p ox KML o3 Hf). cancel.
Qed.

(* the rest of the window after j bytes *)
Lemma hdr_win_skip (sh: share) (N: Z) (c: list val) (off: Z) (S: list Z) (j: Z) :
  win_ok sh N c off (Zlength S) S -> 0 <= j <= Zlength S ->
  win_ok sh N c (off + j) (Zlength (skipn (Z.to_nat j) S)) (skipn (Z.to_nat j) S).
Proof.
  intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) Hj.
  assert (Hs: skipn (Z.to_nat j) S = sublist j (Zlength S) S)
    by (rewrite sublist_skip by lia; auto).
  rewrite Hs. unfold win_ok. rewrite Zlength_sublist by lia.
  repeat split; auto; try lia.
  - unfold bytes_ok in *. apply Forall_sublist; auto.
  - replace (off + j + (Zlength S - j)) with (off + Zlength S) by lia.
    rewrite <- sublist_map, <- H8. list_solve.
Qed.

(* the byte at offset j of the window, in the array *)
Lemma hdr_win_byte (sh: share) (N: Z) (c: list val) (off: Z) (S: list Z) (j: Z) :
  win_ok sh N c off (Zlength S) S -> 0 <= j < Zlength S ->
  Znth (off + j) c = Vint (Int.repr (byte_at S j)) /\ 0 <= byte_at S j < 256.
Proof.
  intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) Hj.
  assert (E: Znth (off + j) c = Znth j (sublist off (off + Zlength S) c))
    by (rewrite Znth_sublist by lia; f_equal; lia).
  rewrite E, H8, Znth_map by lia. unfold byte_at.
  assert (Hn: nth (Z.to_nat j) S 0 = Znth j S).
  { unfold Znth. destruct (Z_lt_dec j 0); [lia|]. reflexivity. }
  rewrite Hn. split; [reflexivity|].
  unfold bytes_ok in H7. rewrite Forall_forall in H7. apply H7. apply Znth_In; lia.
Qed.

(* do { c } while (0) as Clight's Sloop c Sbreak (from H's body_H_fh.v) *)
Ltac hdr_reassoc := repeat match goal with
  |- semax _ _ (Ssequence (Ssequence _ _) _) _ => apply -> seq_assoc end.
Ltac hdr_once_body P :=
  first [ forward_if P;
          [ contradiction
          | forward; try (apply andp_left2, derives_refl)
          | forward; apply andp_left2, derives_refl ]
        | forward; apply andp_left2, derives_refl ].
Ltac hdr_once_skip := hdr_reassoc;
  match goal with |- semax _ ?P (Ssequence (Sloop _ Sbreak) _) _ =>
    forward_loop P break: P; [apply andp_left2, derives_refl | hdr_once_body P | ] end.
(* the error exit of RETURN_ERROR_IF: four empty loops, then the return *)
Ltac hdr_err_exit := hdr_once_skip; hdr_once_skip; hdr_once_skip; hdr_once_skip; forward.

(* the post of an error return: the model says None (E), the tables become junk *)
(* the error codes decodeSeqHeaders returns are constants ERROR(x), never the noForwardProgress ones *)
Lemma hdr_dec_err (k: Z) : 0 < k < 120 -> k <> 80 -> k <> 82 -> dec_err (Int64.unsigned (Int64.repr (- k))).
Proof.
  intros Hk H80 H82. rewrite Int64.unsigned_repr_eq.
  change Int64.modulus with (2 ^ 64).
  rewrite <- (Z_mod_plus_full (- k) 1 (2 ^ 64)). rewrite Z.mod_small by lia.
  unfold dec_err, is_error_code, ZSTD_error_noForwardProgress_destFull, ZSTD_error_noForwardProgress_inputEmpty.
  split; [apply Z.ltb_lt; lia | lia].
Qed.

Lemma hdr_not_err (r: Z) : 0 <= r <= ZSTD_BLOCKSIZE_MAX -> is_error_code r = true -> dec_err r.
Proof. intros Hr Hc. exfalso. unfold is_error_code, ZSTD_BLOCKSIZE_MAX in *. apply Z.ltb_lt in Hc. lia. Qed.

Lemma hdr_skip_len (S: list Z) (j: Z) : Zlength S <= ZSTD_BLOCKSIZE_MAX ->
  Zlength (skipn (Z.to_nat j) S) <= ZSTD_BLOCKSIZE_MAX.
Proof. intros H. rewrite Zlength_correct, length_skipn. rewrite Zlength_correct in H. lia. Qed.

Ltac hdr_dec_tac :=
  match goal with |- context [dec_err _] => idtac end;
  first [ intros; apply hdr_dec_err; lia
        | intros; apply hdr_not_err; [rep_lia | assumption]
        | intros; unfold dec_err, is_error_code, ZSTD_error_noForwardProgress_destFull,
            ZSTD_error_noForwardProgress_inputEmpty; split; [apply Z.ltb_lt; lia | lia] ].

Ltac hdr_ok_post :=
  match goal with |- (is_error_code ?r = true -> dec_err ?r) /\ _ =>
    split; [intros; apply hdr_not_err; [rep_lia | assumption] |] | _ => idtac end.

Ltac hdr_err_begin := cbn [iw_s iw_sh iw_N iw_c iw_base].
Ltac hdr_err_end Hf E HXs :=
  match type of E with decode_seq_header ?os ?S = None =>
    assert (Hsh: shdr_ok os S None) by (split; [intros ?x ?Hx; rewrite E in Hx; discriminate | exact I]);
    assert (HX: None = xb_seq_header os S) by (symmetry; exact HXs) end;
  match goal with |- context [Vlong (Int64.repr (- ?k)) = Vlong (Int64.repr _)] =>
    Exists (Int64.unsigned (Int64.repr (- k))) end;
  Exists (@None (Z * option (fse_table * fse_table * fse_table) * Z));
  rewrite Int64.repr_unsigned;
  match goal with |- context [kstate ?gv ?p ?ox KLL ?o1] =>
  match goal with |- context [kstate _ _ _ KOF ?o2] =>
  match goal with |- context [kstate _ _ _ KML ?o3] =>
  match goal with |- context [field_at Ews t_dctx (DOT _fseEntropy) (Vint (Int.repr ?fe)) _] =>
    sep_apply (hdr_to_junk gv p ox fe o1 o2 o3 Hf) end end end end;
  entailer!; try hdr_dec_tac.
Ltac hdr_err_post Hf E HXs := hdr_err_begin; hdr_err_end Hf E HXs.

Lemma hdr_shdr_intro (os: option (fse_table * fse_table * fse_table)) (S: list Z) (nb: Z)
    (os': option (fse_table * fse_table * fse_table)) (used: Z) :
  (forall x, decode_seq_header os S = Some x -> Some (nb, os', used) = Some x) ->
  1 <= used <= Zlength S -> 0 <= nb <= LONGNBSEQ + 65535 -> seqs_ok os' ->
  (nb = 0 -> os' = os) -> (0 < nb -> os' <> None) -> shdr_ok os S (Some (nb, os', used)).
Proof. intros H1 H2 H3 H4 H5 H6. split; [intros x Hx; apply H1; auto | auto 10]. Qed.

Lemma hdr_fa (N i: Z) (base: val) : 0 <= i < N -> field_compatible (tarray tuchar N) [] base ->
  offset_val i base = field_address (tarray tuchar N) (SUB i) base.
Proof. intros. rewrite arr_field_address by auto. simpl. f_equal. lia. Qed.

(* the input window, cut out of the caller's array (from HufX1D4.v) *)
Lemma hdr_win_split (sh: share) (N: Z) (c: list val) (off: Z) (s: list Z) (base: val) :
  0 <= off -> off + Zlength s <= N -> Zlength c = N -> sublist off (off + Zlength s) c = zbytes s ->
  field_compatible (tarray tuchar N) [] base ->
  data_at sh (tarray tuchar N) c base =
  data_at sh (tarray tuchar off) (sublist 0 off c) base *
  data_at sh (tarray tuchar (Zlength s)) (zbytes s) (offset_val off base) *
  data_at sh (tarray tuchar (N - (off + Zlength s))) (sublist (off + Zlength s) N c)
    (offset_val (off + Zlength s) base).
Proof.
  intros Hoff HN Hc Hsub Hfc. unfold tarray.
  rewrite (split3_data_at_Tarray_tuchar sh N off (off + Zlength s)) by (try rep_lia; list_solve).
  pose proof (Zlength_nonneg s).
  rewrite !field_address0_offset by (apply field_compatible0_cons; split; [simpl; lia | auto with field_compatible]).
  simpl. rewrite !Z.mul_1_l, Hsub. replace (off + Zlength s - off) with (Zlength s) by lia. reflexivity.
Qed.

Lemma hdr_oadd_long (p: val) (n: Z) : isptr p ->
  force_val (sem_binary_operation' Oadd (tptr tuchar) tulong p (Vlong (Int64.repr n))) = offset_val n p.
Proof.
  intros Hp. destruct p; try contradiction. simpl. f_equal. f_equal.
  unfold Ptrofs.of_int64. rewrite Int64.unsigned_repr_eq. rewrite Ptrofs.mul_commut, Ptrofs.mul_one.
  apply Ptrofs.eqm_samerepr. apply Ptrofs.eqm_sym. unfold Ptrofs.eqm. apply Zbits.eqmod_mod. reflexivity.
Qed.

Lemma hdr_oadd_int (p: val) (j: Z) : isptr p -> Int.min_signed <= j <= Int.max_signed ->
  force_val (sem_binary_operation' Oadd (tptr tuchar) tint p (Vint (Int.repr j))) = offset_val j p.
Proof.
  intros Hp Hj. destruct p; try contradiction. simpl. f_equal. f_equal.
  rewrite Ptrofs.mul_commut, Ptrofs.mul_one. unfold ptrofs_of_int, Ptrofs.of_ints.
  rewrite Int.signed_repr by rep_lia. reflexivity.
Qed.

Lemma hdr_sameblock (b: val) (i j: Z) : isptr b -> is_true (sameblock (offset_val i b) (offset_val j b)).
Proof. intros Hb. destruct b; try contradiction. simpl. destruct (peq b b); [reflexivity | congruence]. Qed.

Lemma hdr_sameblock' (b: val) (i j: Z) : isptr b -> sameblock (offset_val i b) (offset_val j b) = true.
Proof. intros Hb. destruct b; try contradiction. simpl. destruct (peq b b); [reflexivity | congruence]. Qed.

Lemma hdr_sub_pp (b: val) (i j: Z) : isptr b ->
  force_val (sem_sub_pp tuchar (offset_val i b) (offset_val j b)) = Vlong (Int64.repr (i - j)).
Proof.
  intros Hb. destruct b; try contradiction. unfold sem_sub_pp. simpl.
  destruct (eq_block b b); [|congruence]. simpl.
  assert (E: Ptrofs.sub (Ptrofs.add i0 (Ptrofs.repr i)) (Ptrofs.add i0 (Ptrofs.repr j)) = Ptrofs.repr (i - j)).
  { rewrite (Ptrofs.add_commut i0 (Ptrofs.repr i)), (Ptrofs.add_commut i0 (Ptrofs.repr j)), Ptrofs.sub_shifted.
    unfold Ptrofs.sub. apply Ptrofs.eqm_samerepr. apply Ptrofs.eqm_sub; apply Ptrofs.eqm_sym, Ptrofs.eqm_unsigned_repr. }
  rewrite E. change (Ptrofs.repr 1) with Ptrofs.one. rewrite Ptrofs.divs_one by reflexivity.
  unfold Vptrofs. simpl. f_equal. unfold Ptrofs.to_int64. apply Int64.eqm_samerepr.
  apply Int64.eqm_sym. change Int64.modulus with Ptrofs.modulus. apply Ptrofs.eqm_unsigned_repr.
Qed.

Lemma hdr_lt_true (a k: Z) : Int64.min_signed <= a <= Int64.max_signed -> 0 <= k <= 100 ->
  typed_true tint (match both_long (fun n1 n2 : int64 => Some (bool2val (Int64.lt n1 n2)))
                     sem_cast_pointer (sem_cast_i2l Signed) (Vlong (Int64.repr a)) (Vint (Int.repr k)) with
                   | Some v' => v' | None => Vundef end) -> a < k.
Proof.
  intros Ha Hk H. simpl in H. unfold sem_cast_i2l, cast_int_long in H. simpl in H.
  unfold Int64.lt in H. rewrite Int.signed_repr in H by rep_lia. rewrite !Int64.signed_repr in H by rep_lia.
  destruct (zlt a k); auto. inv H.
Qed.

Lemma hdr_lt_false (a k: Z) : Int64.min_signed <= a <= Int64.max_signed -> 0 <= k <= 100 ->
  typed_false tint (match both_long (fun n1 n2 : int64 => Some (bool2val (Int64.lt n1 n2)))
                     sem_cast_pointer (sem_cast_i2l Signed) (Vlong (Int64.repr a)) (Vint (Int.repr k)) with
                   | Some v' => v' | None => Vundef end) -> k <= a.
Proof.
  intros Ha Hk H. simpl in H. unfold sem_cast_i2l, cast_int_long in H. simpl in H.
  unfold Int64.lt in H. rewrite Int.signed_repr in H by rep_lia. rewrite !Int64.signed_repr in H by rep_lia.
  destruct (zlt a k); [inv H | lia].
Qed.

Lemma hdr_le2 (S: list Z) : 3 <= Zlength S -> le_field S 1 2 = byte_at S 1 + 256 * byte_at S 2.
Proof.
  intros H. destruct S as [|a [|b [|c t]]];
    try (rewrite ?Zlength_cons, ?Zlength_nil in H; try pose proof (Zlength_nonneg t); lia).
  unfold le_field, slice, byte_at. simpl. lia.
Qed.

Lemma hdr_weak_valid (sh: share) (n: Z) (c: list val) (p: val) (i: Z) :
  readable_share sh -> 0 <= i <= n -> 0 < n ->
  data_at sh (tarray tuchar n) c p |-- weak_valid_pointer (offset_val i p).
Proof.
  intros. sep_apply (data_at_memory_block sh (tarray tuchar n) c p).
  simpl sizeof. rewrite Z.max_r by lia. rewrite Z.mul_1_l.
  apply memory_block_weak_valid_pointer; [lia | lia | apply readable_nonidentity; auto].
Qed.

Transparent denote_tc_test_order.
Lemma hdr_test_order (P: mpred) (x y: val) : sameblock x y = true ->
  P |-- weak_valid_pointer x -> P |-- weak_valid_pointer y -> P |-- denote_tc_test_order x y.
Proof.
  intros Hs Hx Hy. destruct x; try discriminate; destruct y; try discriminate.
  unfold denote_tc_test_order, test_order_ptrs. rewrite Hs. apply andp_right; auto.
Qed.
Opaque denote_tc_test_order.

Transparent denote_tc_test_eq.
Lemma hdr_test_eq (P: mpred) (x y: val) : sameblock x y = true ->
  P |-- weak_valid_pointer x -> P |-- weak_valid_pointer y -> P |-- denote_tc_test_eq x y.
Proof.
  intros Hs Hx Hy. destruct x; try discriminate; destruct y; try discriminate.
  unfold denote_tc_test_eq, test_eq_ptrs. rewrite Hs. apply andp_right; auto.
Qed.
Opaque denote_tc_test_eq.

Lemma hdr_wv_frame (R: mpred) (sh: share) (n: Z) (c: list val) (p: val) (i: Z) :
  readable_share sh -> 0 <= i <= n -> 0 < n ->
  R * data_at sh (tarray tuchar n) c p |-- weak_valid_pointer (offset_val i p).
Proof.
  intros. eapply derives_trans; [apply sepcon_derives; [apply derives_refl | apply hdr_weak_valid; eauto] |].
  rewrite sepcon_comm. apply extend_weak_valid_pointer.
Qed.

Lemma hdr_cmp (cmp: comparison) (base: val) (N i j: Z) : field_compatible (tarray tuchar N) [] base ->
  0 <= i <= N -> 0 <= j <= N ->
  sem_cmp_pp cmp (offset_val i base) (offset_val j base) =
  Some (bool2val (Ptrofs.cmpu cmp (Ptrofs.repr i) (Ptrofs.repr j))).
Proof.
  intros Hf Hi Hj. destruct base; try (destruct Hf; contradiction).
  destruct Hf as (_ & _ & Hsz & _). simpl in Hsz. rewrite Z.max_r in Hsz by lia.
  pose proof (Ptrofs.unsigned_range i0).
  assert (Hu: forall k, 0 <= k <= N -> Ptrofs.unsigned (Ptrofs.add i0 (Ptrofs.repr k)) = Ptrofs.unsigned i0 + k).
  { intros k Hk. rewrite Ptrofs.add_unsigned, (Ptrofs.unsigned_repr k), Ptrofs.unsigned_repr;
      unfold Ptrofs.max_unsigned; lia. }
  assert (E: Ptrofs.cmpu cmp (Ptrofs.add i0 (Ptrofs.repr i)) (Ptrofs.add i0 (Ptrofs.repr j)) =
             Ptrofs.cmpu cmp (Ptrofs.repr i) (Ptrofs.repr j)).
  { unfold Ptrofs.cmpu, Ptrofs.ltu, Ptrofs.eq. rewrite (Hu i Hi), (Hu j Hj).
    rewrite !Ptrofs.unsigned_repr by (unfold Ptrofs.max_unsigned; lia).
    destruct cmp; repeat (first [destruct (zeq _ _) | destruct (zlt _ _)]); auto; lia. }
  unfold sem_cmp_pp. simpl. destruct (eq_block b b); [|congruence]. simpl. rewrite E. reflexivity.
Qed.

Lemma hdr_cmpu (cmp: comparison) (a b: Z) : 0 <= a <= Ptrofs.max_unsigned -> 0 <= b <= Ptrofs.max_unsigned ->
  Ptrofs.cmpu cmp (Ptrofs.repr a) (Ptrofs.repr b) =
  match cmp with Ceq => a =? b | Cne => negb (a =? b) | Clt => a <? b | Cle => a <=? b
               | Cgt => b <? a | Cge => b <=? a end.
Proof.
  intros Ha Hb. unfold Ptrofs.cmpu, Ptrofs.ltu, Ptrofs.eq. rewrite !Ptrofs.unsigned_repr by lia.
  destruct cmp; repeat (first [destruct (zeq _ _) | destruct (zlt _ _)]); simpl; symmetry;
    first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge | apply Z.leb_le | apply Z.leb_gt
          | apply negb_true_iff, Z.eqb_neq | apply negb_false_iff, Z.eqb_eq | idtac]; lia.
Qed.

Lemma hdr_tt (x: bool) : typed_true tint (bool2val x) -> x = true.
Proof. destruct x; auto. intros H. inv H. Qed.
Lemma hdr_tf (x: bool) : typed_false tint (bool2val x) -> x = false.
Proof. destruct x; auto. intros H. inv H. Qed.

Lemma hdr_offset_inj (b: val) (i j: Z) : isptr b -> 0 <= i <= Ptrofs.max_unsigned -> 0 <= j <= Ptrofs.max_unsigned ->
  offset_val i b = offset_val j b -> i = j.
Proof.
  intros Hb Hi Hj E. destruct b; try contradiction. simpl in E.
  assert (H0: Ptrofs.add i0 (Ptrofs.repr i) = Ptrofs.add i0 (Ptrofs.repr j)) by congruence. clear E.
  apply (f_equal (fun x => Ptrofs.sub x i0)) in H0. cbv beta in H0.
  rewrite !Ptrofs.sub_add_l, Ptrofs.sub_idem, !Ptrofs.add_zero_l in H0.
  rename H0 into E. apply (f_equal Ptrofs.unsigned) in E. rewrite !Ptrofs.unsigned_repr in E by lia. auto.
Qed.

Lemma hdr_mode_vals (m: Z) : 0 <= m < 256 ->
  force_val (sem_cast tint tint (eval_binop Oshr tuchar tint (Vint (Int.repr m)) (Vint (Int.repr 6)))) =
    Vint (Int.repr (Z.shiftr m 6)) /\
  force_val (sem_cast tint tint (eval_binop Oand tint tint
    (eval_binop Oshr tuchar tint (Vint (Int.repr m)) (Vint (Int.repr 4))) (Vint (Int.repr 3)))) =
    Vint (Int.repr (Z.land (Z.shiftr m 4) 3)) /\
  force_val (sem_cast tint tint (eval_binop Oand tint tint
    (eval_binop Oshr tuchar tint (Vint (Int.repr m)) (Vint (Int.repr 2))) (Vint (Int.repr 3)))) =
    Vint (Int.repr (Z.land (Z.shiftr m 2) 3)).
Proof.
  intros Hm. unfold eval_binop. simpl. unfold Int.shr. rewrite Int.signed_repr by rep_lia.
  rewrite !and_repr. split3; reflexivity.
Qed.

Lemma hdr_mode_range (m k: Z) : 0 <= m < 256 ->
  0 <= Z.shiftr m 6 <= 3 /\ 0 <= Z.land (Z.shiftr m k) 3 <= 3.
Proof.
  intros Hm. split.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 6) with 64. split; [apply Z.div_pos; lia|].
    assert (m / 64 < 4) by (apply Z.div_lt_upper_bound; lia). lia.
  - assert (E3: Z.land (Z.shiftr m k) 3 = Z.shiftr m k mod 4)
      by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; reflexivity).
    rewrite E3. pose proof (Z.mod_pos_bound (Z.shiftr m k) 4 ltac:(lia)). lia.
Qed.

Lemma hdr_dctx_fc (gfs: list gfield) (p: val) :
  field_compatible t_dctx [] p -> legal_nested_field t_dctx gfs -> field_compatible t_dctx gfs p.
Proof. intros (A & B & C & D & _) L. repeat split; auto. Qed.

(* the arguments of a ZSTD_buildSeqTable call match the specification's *)
Ltac hdr_args Hfe Hfp0 :=
  simpl; rewrite hdr_sub_pp by auto; rewrite Hfe; unfold ctx_seq; rewrite Zlength_skipn;
  rewrite !field_address_offset
    by (apply hdr_dctx_fc; [exact Hfp0|]; simpl; repeat split; auto; unfold in_members;
        cbv [map name_member]; simpl; repeat (first [left; reflexivity | right]));
  simpl; rewrite !offset_offset_val; unfold MaxLL, LLFSELog, MaxOff, OffFSELog, MaxML, MLFSELog;
  repeat (f_equal; try lia).

Lemma body_decodeSeqHeaders :
  semax_body Vprog HDR_G f_ZSTD_decodeSeqHeaders ZSTD_decodeSeqHeaders_spec.
Proof.
  start_function. rename H3 into Hslen.
  destruct i as [sh base N c off S]. unfold inwin_ok in H.
  cbn [iw_sh iw_base iw_N iw_c iw_off iw_s] in H |- *. cbn [iw_s] in Hslen.
  pose proof H as Hw. destruct H as (Hrs & Hoff & HoffN & HN & Hc & _ & Hbytes & Hsub).
  rewrite hdr_tabs_seq_eq. Intros.
  assert_PROP (field_compatible (tarray tuchar N) [] base) as Hfb by entailer!.
  assert_PROP (field_compatible t_dctx (DOT _fseEntropy) p) as Hfp by entailer!.
  assert (Hfp0: field_compatible t_dctx [] p)
    by (destruct Hfp as (A & B & C & D & _); repeat split; auto).
  assert (Hpb: isptr base) by (destruct Hfb; auto).
  forward. forward.
  rewrite hdr_oadd_long by (destruct base; try contradiction; exact I). rewrite offset_offset_val.
  forward.
  hdr_once_skip.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_loop (PROPx P (LOCALx Q (SEPx R))) break: (PROPx ((1 <= Zlength S) :: P) (LOCALx Q (SEPx R))) end.
  { apply andp_left2, derives_refl. }
  { forward_if.
    { hdr_err_exit.
      rewrite !Int64.unsigned_repr in H by rep_lia.
      assert (E: decode_seq_header os S = None)
        by (unfold decode_seq_header; replace (Zlength S <? 1) with true by lia; reflexivity).
      assert (HXs: xb_seq_header os S = None)
        by (unfold xb_seq_header, x_seq_header; replace (Zlength S <? 1) with true by lia; reflexivity).
      hdr_err_post Hfp0 E HXs. }
    { forward. entailer!. rewrite !Int64.unsigned_repr in H by rep_lia. lia. } }
  Intros.
  destruct (hdr_win_byte sh N c off S 0 Hw ltac:(lia)) as [Hb0 Hb0r].
  rewrite Z.add_0_r in Hb0.
  assert (Hb0u: @Znth val Vundef off c = Vint (Int.repr (byte_at S 0))) by exact Hb0.
  forward. forward.
  rewrite (hdr_fa N off base) by (auto; lia).
  forward.
  { rewrite Hb0u. entailer!. rep_lia. }
  rewrite <- (hdr_fa N off base) by (auto; lia).
  rewrite Hb0u, hdr_oadd_int, offset_offset_val by (auto; rep_lia).
  forward_if ((EX nb: Z, EX pos: Z,
    PROP (hdr_head S = (nb, pos, true); 0 <= nb <= 98047; 1 <= pos <= Zlength S)
    LOCAL (temp _nbSeq (Vint (Int.repr nb)); temp _ip (offset_val (off + pos) base);
           temp _iend (offset_val (off + Zlength S) base); temp _istart (offset_val off base); gvars gv;
           temp _dctx p; temp _nbSeqPtr pn; temp _src (offset_val off base);
           temp _srcSize (Vlong (Int64.repr (Zlength S))))
    SEP (zstd_globals gv; frame_fields p fs; field_at Ews t_dctx (DOT _fseEntropy) (Vint (Int.repr fe)) p;
         kstate gv p ox KLL (seq_of KLL os); kstate gv p ox KOF (seq_of KOF os);
         kstate gv p ox KML (seq_of KML os); dent_of dent_def gv ox;
         field_at_ Ews t_dctx (DOT _workspace) p; data_at_ shn tint pn;
         data_at sh (tarray tuchar N) c base))%assert).
  { forward_if.
    { (* 0xFF: two more bytes *)
      match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
        forward_loop (PROPx P (LOCALx Q (SEPx R))) break: (PROPx ((3 <= Zlength S) :: P) (LOCALx Q (SEPx R))) end.
      { apply andp_left2, derives_refl. }
      { forward_if.
        { apply prop_right. apply hdr_sameblock; auto. }
        { rewrite hdr_sub_pp in H5 by auto. apply hdr_lt_true in H5; [|rep_lia|lia].
          hdr_err_exit.
          assert (E: decode_seq_header os S = None).
          { rewrite hdr_dsh_eq by lia. unfold hdr_head. rewrite H4.
            replace (3 <=? Zlength S) with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
          assert (HXs: xb_seq_header os S = None).
          { rewrite hdr_xsh_eq by lia. unfold hdr_head. rewrite H4.
            replace (3 <=? Zlength S) with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
          hdr_err_post Hfp0 E HXs. }
        { rewrite hdr_sub_pp in H5 by auto. apply hdr_lt_false in H5; [|rep_lia|lia].
          forward. entailer!. } }
      Intros.
      destruct (hdr_win_byte sh N c off S 1 Hw ltac:(lia)) as [_ Hb1r].
      destruct (hdr_win_byte sh N c off S 2 Hw ltac:(lia)) as [_ Hb2r].
      rewrite (hdr_win_split sh N c off S base) by auto. Intros.
      forward_call (sh, offset_val off base, S, 1).
      { unfold mem_read_pre. split; [auto|]. split; [lia|]. split; [lia|]. apply Forall_sublist; auto. }
      forward. forward.
      rewrite hdr_oadd_int, offset_offset_val by (auto; rep_lia).
      Exists (le_field S 1 2 + LONGNBSEQ) 3. rewrite hdr_le2 in * by lia.
      entailer!.
      unfold hdr_head. rewrite ?H4, ?hdr_le2 by lia.
      replace (3 <=? Zlength S) with true by (symmetry; apply Z.leb_le; lia).
      unfold LONGNBSEQ. split; [reflexivity|]. split; [lia|]. f_equal; lia. }
    { (* 0x80 .. 0xFE: one more byte *)
      match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
        forward_loop (PROPx P (LOCALx Q (SEPx R))) break: (PROPx ((2 <= Zlength S) :: P) (LOCALx Q (SEPx R))) end.
      { apply andp_left2, derives_refl. }
      { forward_if.
        { apply hdr_test_order; [apply hdr_sameblock'; auto | apply hdr_wv_frame; auto; lia | apply hdr_wv_frame; auto; lia]. }
        { rewrite (hdr_cmp Cge base N) in H5 by (auto; lia). rewrite hdr_cmpu in H5 by rep_lia.
          apply hdr_tt, Z.leb_le in H5.
          hdr_err_exit.
          assert (E: decode_seq_header os S = None).
          { rewrite hdr_dsh_eq by lia. unfold hdr_head.
            replace (byte_at S 0 <=? 127) with false by (symmetry; apply Z.leb_gt; lia).
            replace (byte_at S 0 =? 255) with false by (symmetry; apply Z.eqb_neq; lia).
            replace (2 <=? Zlength S) with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
          assert (HXs: xb_seq_header os S = None).
          { rewrite hdr_xsh_eq by lia. unfold hdr_head.
            replace (byte_at S 0 <=? 127) with false by (symmetry; apply Z.leb_gt; lia).
            replace (byte_at S 0 =? 255) with false by (symmetry; apply Z.eqb_neq; lia).
            replace (2 <=? Zlength S) with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
          hdr_err_post Hfp0 E HXs. }
        { rewrite (hdr_cmp Cge base N) in H5 by (auto; lia). rewrite hdr_cmpu in H5 by rep_lia.
          apply hdr_tf, Z.leb_gt in H5.
          forward. entailer!. } }
      Intros.
      destruct (hdr_win_byte sh N c off S 1 Hw ltac:(lia)) as [Hb1 Hb1r].
      assert (Hb1u: @Znth val Vundef (off + 1) c = Vint (Int.repr (byte_at S 1))) by exact Hb1.
      forward. forward.
      rewrite (hdr_fa N (off + 1) base) by (auto; lia).
      forward.
      { rewrite Hb1u. entailer!. rep_lia. }
      rewrite <- (hdr_fa N (off + 1) base) by (auto; lia).
      rewrite Hb1u, hdr_oadd_int, offset_offset_val by (auto; rep_lia).
      forward.
      Exists ((byte_at S 0 - 128) * 256 + byte_at S 1) 2.
      entailer!.
      split3.
      { unfold hdr_head.
        replace (byte_at S 0 <=? 127) with false by (symmetry; apply Z.leb_gt; lia).
        replace (byte_at S 0 =? 255) with false by (symmetry; apply Z.eqb_neq; lia).
        replace (2 <=? Zlength S) with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
      { rewrite Int.shl_mul_two_p. rewrite mul_repr, add_repr. reflexivity. }
      { f_equal; lia. } } }
  { forward. Exists (byte_at S 0) 1. entailer!.
    unfold hdr_head. replace (byte_at S 0 <=? 127) with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
  Intros nb pos.
  assert (Hdsh := hdr_dsh_eq os S H). rewrite H3 in Hdsh. cbv beta iota zeta in Hdsh.
  assert (Hxsh := hdr_xsh_eq os S H). rewrite H3 in Hxsh. cbv beta iota zeta in Hxsh.
  forward.
  forward_if.
  { (* no sequences *)
    subst nb.
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_loop (PROPx P (LOCALx Q (SEPx R))) break: (PROPx ((pos = Zlength S) :: P) (LOCALx Q (SEPx R))) end.
    { apply andp_left2, derives_refl. }
    { forward_if.
      { apply hdr_test_eq; [apply hdr_sameblock'; auto | apply hdr_wv_frame; auto; lia | apply hdr_wv_frame; auto; lia]. }
      { assert (H7: pos <> Zlength S) by (intro E; apply H6; rewrite E; reflexivity).
        hdr_err_exit.
        assert (E: decode_seq_header os S = None).
        { rewrite Hdsh. simpl. replace (pos =? Zlength S) with false by (symmetry; apply Z.eqb_neq; lia).
          reflexivity. }
        assert (HXs: xb_seq_header os S = None).
        { rewrite Hxsh. simpl. replace (pos =? Zlength S) with false by (symmetry; apply Z.eqb_neq; lia).
          reflexivity. }
        hdr_err_post Hfp0 E HXs. }
      { apply hdr_offset_inj in H6; [|auto|rep_lia|rep_lia].
        forward. entailer!. } }
    Intros. forward.
    { apply prop_right; apply hdr_sameblock; auto. }
    assert (E: decode_seq_header os S = Some (0, os, Zlength S))
      by (rewrite Hdsh; simpl; rewrite Z.eqb_refl; reflexivity).
    assert (HXs: Some (0, os, Zlength S) = xb_seq_header os S)
      by (rewrite Hxsh; simpl; rewrite Z.eqb_refl; reflexivity).
    assert (Hsh: shdr_ok os S (Some (0, os, Zlength S))).
    { apply hdr_shdr_intro; auto; try (unfold LONGNBSEQ; lia). intros x Hx; rewrite E in Hx; congruence. }
    cbn [iw_s iw_sh iw_N iw_c iw_base]. Exists (Zlength S) (Some (0, os, Zlength S)).
    rewrite hdr_sub_pp by auto. rewrite hdr_tabs_seq_eq.
    entailer!. hdr_ok_post. f_equal. f_equal. lia. }
  rewrite (proj2 (Z.eqb_neq nb 0) H6) in Hdsh. cbn [negb] in Hdsh.
  rewrite (proj2 (Z.eqb_neq nb 0) H6) in Hxsh. cbn [negb] in Hxsh.
  (* the symbol-modes byte *)
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_loop (PROPx P (LOCALx Q (SEPx R))) break: (PROPx ((pos + 1 <= Zlength S) :: P) (LOCALx Q (SEPx R))) end.
  { apply andp_left2, derives_refl. }
  { forward_if.
    { apply prop_right. apply hdr_sameblock; auto. }
    { rewrite hdr_sub_pp in H7 by auto. apply hdr_lt_true in H7; [|rep_lia|lia].
      hdr_err_exit.
      assert (E: decode_seq_header os S = None).
      { rewrite Hdsh. replace (pos + 1 >? Zlength S) with true by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_lt; lia).
        reflexivity. }
      assert (HXs: xb_seq_header os S = None).
      { rewrite Hxsh. replace (pos + 1 >? Zlength S) with true by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_lt; lia).
        reflexivity. }
      hdr_err_post Hfp0 E HXs. }
    { rewrite hdr_sub_pp in H7 by auto. apply hdr_lt_false in H7; [|rep_lia|lia].
      forward. entailer!. } }
  Intros.
  replace (pos + 1 >? Zlength S) with false in Hdsh by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
  replace (pos + 1 >? Zlength S) with false in Hxsh by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
  destruct (hdr_win_byte sh N c off S pos Hw ltac:(lia)) as [Hbp Hbpr].
  assert (Hbpu: @Znth val Vundef (off + pos) c = Vint (Int.repr (byte_at S pos))) by exact Hbp.
  set (modes := byte_at S pos) in *.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_loop (PROPx P (LOCALx Q (SEPx R))) break: (PROPx ((Z.land modes 3 = 0) :: P) (LOCALx Q (SEPx R))) end.
  { apply andp_left2, derives_refl. }
  { rewrite (hdr_fa N (off + pos) base) by (auto; lia).
    forward.
    { rewrite Hbpu. entailer!. rep_lia. }
    rewrite <- (hdr_fa N (off + pos) base) by (auto; lia). rewrite Hbpu.
    forward_if.
    { rewrite !Int.unsigned_repr in H8' by rep_lia.
      hdr_err_exit.
      assert (E: decode_seq_header os S = None).
      { rewrite Hdsh. replace (Z.land modes 3 =? 0) with false by (symmetry; apply Z.eqb_neq; auto).
        reflexivity. }
      assert (HXs: xb_seq_header os S = None).
      { rewrite Hxsh. replace (Z.land modes 3 =? 0) with false by (symmetry; apply Z.eqb_neq; auto).
        reflexivity. }
      hdr_err_post Hfp0 E HXs. }
    { forward. entailer!.
      assert (0 <= Z.land modes 3 <= 3).
      { assert (E3: Z.land modes 3 = modes mod 4)
          by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; reflexivity).
        rewrite E3. pose proof (Z.mod_pos_bound modes 4 ltac:(lia)). lia. }
      rewrite and_repr in H8. apply repr_inj_unsigned in H8; [auto | rep_lia | rep_lia]. } }
  Intros.
  rewrite H8 in Hdsh. cbn [Z.eqb negb] in Hdsh.
  rewrite H8 in Hxsh. cbn [Z.eqb negb] in Hxsh.
  rewrite (hdr_fa N (off + pos) base) by (auto; lia).
  do 6 (forward; try (rewrite Hbpu; entailer!; rep_lia)).
  rewrite <- (hdr_fa N (off + pos) base) by (auto; lia). rewrite Hbpu.
  forward.
  rewrite hdr_oadd_int, offset_offset_val by (auto; rep_lia).
  destruct (hdr_mode_vals modes Hbpr) as (Em1 & Em2 & Em3). rewrite Em1, Em2, Em3.
  destruct (hdr_mode_range modes 4 Hbpr) as [Hm1 Hm2]. destruct (hdr_mode_range modes 2 Hbpr) as [_ Hm3].
  assert (Hdd: exists dd, fs_ddictIsCold fs = Vint (Int.repr dd) /\ (dd = 0 \/ dd = 1)) by (destruct H2; eauto).
  destruct Hdd as (dd & Hdd & Hdd01).
  assert (Hfe: forall k, fe_of (seq_of k os) = fe) by (intros k; subst fe; destruct os as [[[a b] c']|]; reflexivity).
  unfold frame_fields. rewrite Hdd. Intros.
  (* table KLL *)
  forward_call p.
  forward. forward.
  forward_call (gv, p, ox, KLL, seq_of KLL os, Z.shiftr modes 6, dd, nb, sh, base, N, c, off + (pos + 1),
                skipn (Z.to_nat (pos + 1)) S).
  { apply prop_right; apply hdr_sameblock; auto. }
  { entailer!. hdr_args Hfe Hfp0. }
  { split; [apply hdr_win_skip; auto; lia | split; [apply hdr_seqs_ok_k; auto | apply hdr_skip_len; auto]]. }
  Intros vr.
  match goal with H: forall x, seq_table _ _ _ _ _ _ = Some x -> snd vr = Some x |- _ => rename H into Hmr1 end.
  match goal with H: match snd vr with _ => _ end |- _ => rename H into Hr1 end.
  match goal with H: 0 <= fst vr <= _ |- _ => rename H into Hr1r end.
  match goal with H: snd vr = x_seq_table ncount_c _ _ _ _ _ _ |- _ => apply (f_equal Some) in H; rename H into Hx1 end.
  destruct vr as [r1 resr1]. cbn [fst snd] in Hmr1, Hr1, Hr1r, Hx1 |- *.
  forward.
  destruct resr1 as [[tLL k1]|].
  2:{ change (kjunk p KLL) with (kstate gv p ox KLL None).
      match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
        forward_loop (PROPx P (LOCALx Q (SEPx R))) break: (PROPx (False :: P) (LOCALx Q (SEPx R))) end.
      { apply andp_left2, derives_refl. }
      { forward_call r1. rewrite Hr1.
        forward_if.
        { hdr_err_exit.
          assert (E: decode_seq_header os S = None) by (rewrite Hdsh; apply hdr_tables_none1; exact Hmr1).
          assert (HXs: xb_seq_header os S = None) by (rewrite Hxsh; apply hdr_xtables_none1; exact Hx1).
          hdr_err_begin. unfold frame_fields. rewrite Hdd. hdr_err_end Hfp0 E HXs. }
        { match goal with H: Int.repr 1 = Int.zero |- _ => inv H end. } } }
  destruct Hr1 as (-> & Hk1 & Hokk1).
  rewrite Zlength_skipn in Hk1.
  assert (Hk1e: is_error_code k1 = false) by (unfold is_error_code; apply Z.ltb_ge; rep_lia).
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_loop (PROPx P (LOCALx Q (SEPx R))) break: (PROPx P (LOCALx Q (SEPx R))) end.
  { apply andp_left2, derives_refl. }
  { forward_call k1. rewrite Hk1e.
    forward_if.
    { exfalso. match goal with H: Int.repr 0 <> Int.zero |- _ => apply H; reflexivity end. }
    { forward. entailer!. } }
  forward.
  rewrite hdr_oadd_long, offset_offset_val by auto.
  (* table KOF *)
  forward_call p. forward. forward.
  forward_call (gv, p, ox, KOF, seq_of KOF os, Z.land (Z.shiftr modes 4) 3, dd, nb, sh, base, N, c, off + (pos + 1 + k1),
                skipn (Z.to_nat (pos + 1 + k1)) S).
  { apply prop_right; apply hdr_sameblock; auto. }
  { entailer!. hdr_args Hfe Hfp0. }
  { split; [apply hdr_win_skip; auto; lia | split; [apply hdr_seqs_ok_k; auto | apply hdr_skip_len; auto]]. }
  Intros vr.
  match goal with H: forall x, seq_table _ _ _ _ _ _ = Some x -> snd vr = Some x |- _ => rename H into Hmr2 end.
  match goal with H: match snd vr with _ => _ end |- _ => rename H into Hr2 end.
  match goal with H: 0 <= fst vr <= _ |- _ => rename H into Hr2r end.
  match goal with H: snd vr = x_seq_table ncount_c _ _ _ _ _ _ |- _ => apply (f_equal Some) in H; rename H into Hx2 end.
  destruct vr as [r2 resr2]. cbn [fst snd] in Hmr2, Hr2, Hr2r, Hx2 |- *.
  forward.
  destruct resr2 as [[tOF k2]|].
  2:{ change (kjunk p KOF) with (kstate gv p ox KOF None).
      match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
        forward_loop (PROPx P (LOCALx Q (SEPx R))) break: (PROPx (False :: P) (LOCALx Q (SEPx R))) end.
      { apply andp_left2, derives_refl. }
      { forward_call r2. rewrite Hr2.
        forward_if.
        { hdr_err_exit.
          assert (E: decode_seq_header os S = None) by (rewrite Hdsh; eapply hdr_tables_none2; [exact Hmr1 | exact Hmr2]).
          assert (HXs: xb_seq_header os S = None) by (rewrite Hxsh; eapply hdr_xtables_none2; [exact Hx1 | exact Hx2]).
          hdr_err_begin. unfold frame_fields. rewrite Hdd. hdr_err_end Hfp0 E HXs. }
        { match goal with H: Int.repr 1 = Int.zero |- _ => inv H end. } } }
  destruct Hr2 as (-> & Hk2 & Hokk2).
  rewrite Zlength_skipn in Hk2.
  assert (Hk2e: is_error_code k2 = false) by (unfold is_error_code; apply Z.ltb_ge; rep_lia).
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_loop (PROPx P (LOCALx Q (SEPx R))) break: (PROPx P (LOCALx Q (SEPx R))) end.
  { apply andp_left2, derives_refl. }
  { forward_call k2. rewrite Hk2e.
    forward_if.
    { exfalso. match goal with H: Int.repr 0 <> Int.zero |- _ => apply H; reflexivity end. }
    { forward. entailer!. } }
  forward.
  rewrite hdr_oadd_long, offset_offset_val by auto.
  (* table KML *)
  forward_call p. forward. forward.
  forward_call (gv, p, ox, KML, seq_of KML os, Z.land (Z.shiftr modes 2) 3, dd, nb, sh, base, N, c, off + (pos + 1 + k1 + k2),
                skipn (Z.to_nat (pos + 1 + k1 + k2)) S).
  { apply prop_right; apply hdr_sameblock; auto. }
  { entailer!. hdr_args Hfe Hfp0. }
  { split; [apply hdr_win_skip; auto; lia | split; [apply hdr_seqs_ok_k; auto | apply hdr_skip_len; auto]]. }
  Intros vr.
  match goal with H: forall x, seq_table _ _ _ _ _ _ = Some x -> snd vr = Some x |- _ => rename H into Hmr3 end.
  match goal with H: match snd vr with _ => _ end |- _ => rename H into Hr3 end.
  match goal with H: 0 <= fst vr <= _ |- _ => rename H into Hr3r end.
  match goal with H: snd vr = x_seq_table ncount_c _ _ _ _ _ _ |- _ => apply (f_equal Some) in H; rename H into Hx3 end.
  destruct vr as [r3 resr3]. cbn [fst snd] in Hmr3, Hr3, Hr3r, Hx3 |- *.
  forward.
  destruct resr3 as [[tML k3]|].
  2:{ change (kjunk p KML) with (kstate gv p ox KML None).
      match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
        forward_loop (PROPx P (LOCALx Q (SEPx R))) break: (PROPx (False :: P) (LOCALx Q (SEPx R))) end.
      { apply andp_left2, derives_refl. }
      { forward_call r3. rewrite Hr3.
        forward_if.
        { hdr_err_exit.
          assert (E: decode_seq_header os S = None) by (rewrite Hdsh; eapply hdr_tables_none3; [exact Hmr1 | exact Hmr2 | exact Hmr3]).
          assert (HXs: xb_seq_header os S = None)
            by (rewrite Hxsh; eapply hdr_xtables_none3; [exact Hx1 | exact Hx2 | exact Hx3]).
          hdr_err_begin. unfold frame_fields. rewrite Hdd. hdr_err_end Hfp0 E HXs. }
        { match goal with H: Int.repr 1 = Int.zero |- _ => inv H end. } } }
  destruct Hr3 as (-> & Hk3 & Hokk3).
  rewrite Zlength_skipn in Hk3.
  assert (Hk3e: is_error_code k3 = false) by (unfold is_error_code; apply Z.ltb_ge; rep_lia).
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_loop (PROPx P (LOCALx Q (SEPx R))) break: (PROPx P (LOCALx Q (SEPx R))) end.
  { apply andp_left2, derives_refl. }
  { forward_call k3. rewrite Hk3e.
    forward_if.
    { exfalso. match goal with H: Int.repr 0 <> Int.zero |- _ => apply H; reflexivity end. }
    { forward. entailer!. } }
  forward.
  rewrite hdr_oadd_long, offset_offset_val by auto.
  (* the end *)
  forward.
  { apply prop_right; apply hdr_sameblock; auto. }
  assert (Hsh: shdr_ok os S (Some (nb, Some (tLL, tOF, tML), pos + 1 + k1 + k2 + k3))).
  { apply hdr_shdr_intro; try lia.
    - intros x Hx. rewrite Hdsh in Hx. revert Hx. apply hdr_tables_ok; [exact Hmr1 | exact Hmr2 | exact Hmr3].
    - unfold LONGNBSEQ; lia.
    - split3; auto.
    - intros _; discriminate. }
  assert (Hub: 1 <= pos + 1 + k1 + k2 + k3 <= Zlength S) by exact (proj1 (proj2 Hsh)).
  assert (HXs: Some (nb, Some (tLL, tOF, tML), pos + 1 + k1 + k2 + k3) = xb_seq_header os S)
    by (rewrite Hxsh; symmetry; apply hdr_xtables_some; [exact Hx1 | exact Hx2 | exact Hx3]).
  cbn [iw_s iw_sh iw_N iw_c iw_base]. Exists (pos + 1 + k1 + k2 + k3) (Some (nb, Some (tLL, tOF, tML), pos + 1 + k1 + k2 + k3)).
  rewrite hdr_sub_pp by auto. rewrite hdr_tabs_seq_eq. unfold frame_fields. rewrite Hdd. simpl seq_of.
  entailer!. hdr_ok_post.
  f_equal; f_equal; lia.
Qed.

(* ===================== the group ===================== *)

Lemma HDR_ok : HDR_obligation.
Proof.
  exists HDR_S. split; [reflexivity | split].
  - intros x Hx; unfold HDR_exports in Hx; simpl in Hx; unfold HDR_S; simpl; tauto.
  - repeat apply Forall_cons; try apply Forall_nil.
    + exists f_ZSTD_buildSeqTable_rle; split; [reflexivity | split; [reflexivity | exact body_buildSeqTable_rle]].
    + exists f_ZSTD_buildSeqTable; split; [reflexivity | split; [reflexivity | exact body_buildSeqTable]].
    + exists f_ZSTD_decodeSeqHeaders; split; [reflexivity | split; [reflexivity | exact body_decodeSeqHeaders]].
Qed.
