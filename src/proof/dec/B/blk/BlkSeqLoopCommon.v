(* LOOP: what the three loop bodies share on the VST side.

   - LOOP_GB: the context the loop bodies are proved in (BlkSeqLoopShort / Split / Long): G_BLK, the COPY
     helpers, DEC (initFseState, decodeSequence), EXEC (the executors) and ZSTD_prefetchMatch (LG_prefetchMatch
     = BlkSeqLOOP.ZSTD_prefetchMatch_spec, copied: BlkSeqLOOP requires this file).  BlkSeqLOOP.LOOP_ok lifts
     the bodies to its context with body_ok_mono.
   - seqtabs_borrow: the three sequence tables (wherever they live: the context, the DDict, the globals'
     predefined tables via GLOBALS_obligation) and the context's pointers to them, out of tabs_seq, and back.
   - inwin_bits: the input array as a readable array (for the literals in it) plus the sequences bitstream
     as a bit_src (BIT_initDStream / decodeSequence / endOfDStream), by splitting its share.
   - litextra_data_at: litExtraBuffer as a byte array (the literals of LExtra / the tail of LSplit). *)
Require Export Zstd.proof.dec.B.blk.BlkSeqLoopModel Zstd.proof.dec.B.blk.BlkSeqDEC.
(* the exact model of the sequences section: the C stores as the model's (BlkSeqXKitL), the model's outcome (BlkSeqXKitD) *)
Require Export Zstd.proof.dec.B.blk.BlkSeqXKitL Zstd.proof.dec.B.blk.BlkSeqXKitD.
Local Open Scope logic.

(* = BlkSeqLOOP.ZSTD_prefetchMatch_spec *)
Definition LG_prefetchMatch_spec : ident * funspec :=
  DECLARE _ZSTD_prefetchMatch
  WITH shq: share, sp: val, ll: Z, ml: Z, off: Z, pos: Z, pS: val, dE: val, W: list ptr_witness
  PRE [ tulong, tptr t_seq, tptr tuchar, tptr tuchar ]
    PROP (readable_share shq; 0 <= ll <= Int64.max_unsigned; 0 <= ml <= Int64.max_unsigned;
          0 <= off <= Int64.max_unsigned; 0 <= pos <= Int64.max_unsigned;
          isptr pS; pws_pred W |-- weak_valid_pointer pS;
          dE = nullval \/ (isptr dE /\ (pws_pred W |-- weak_valid_pointer dE)))
    PARAMS (Vlong (Int64.repr pos); sp; pS; dE)
    SEP (data_at shq t_seq (seqrep ll ml off) sp; pws_pred W)
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr (pos + ll + ml)))
    SEP (data_at shq t_seq (seqrep ll ml off) sp; pws_pred W).

(* the context of the three loop bodies *)
Definition LOOP_GB : funspecs :=
  (G_BLK ++ COPY_exports) ++ DEC_exports ++ EXEC_exports ++ [LG_prefetchMatch_spec].

(* the context's pointers to its three sequence tables *)
Definition seq_ptrs (p: val) (tp: val * val * val) : mpred :=
  let '(a, b, c) := tp in
  field_at Ews t_dctx (DOT _LLTptr) a p * field_at Ews t_dctx (DOT _OFTptr) b p *
  field_at Ews t_dctx (DOT _MLTptr) c p.

(* the pool of seqtabs_borrow: a DDict's sequence table of kind k, a predefined table of kind k *)
Definition sb_ddslot (ox: option ddx) (k: seqkind) : mpred :=
  match ox_seq k ox with
  | Some t => seqspace_at Ews k (Some t) (dd_seq k (ox_q ox))
  | None => emp
  end.
Definition sb_gslot (gv: globals) (k: seqkind) : mpred :=
  seqtab_at_fm Ers k (sk_predef k) predef_fm (gv (sk_gdefault k)).

Lemma sb_dent_split (gv: globals) (ox: option ddx) :
  exists Rd: mpred, dent_of dent_def gv ox = sb_ddslot ox KLL * sb_ddslot ox KOF * sb_ddslot ox KML * Rd.
Proof.
  unfold sb_ddslot, ox_seq.
  destruct ox as [x|].
  2: { exists emp. simpl. rewrite !emp_sepcon. reflexivity. }
  simpl dent_of. simpl ox_ent. simpl ox_q.
  destruct (ddx_ent x) as [st|].
  2: { exists (dent_def gv (dx_q x) None). rewrite !emp_sepcon. reflexivity. }
  unfold dent_def.
  destruct (st_seq st) as [[[a b] c]|] eqn:Hs.
  2: { simpl seq_of. exists (match st_huf st with Some _ => FF | None => FF end).
       rewrite !emp_sepcon. destruct (st_huf st); reflexivity. }
  simpl seq_of.
  destruct (st_huf st) as [ht|].
  - match goal with |- exists Rd, (andp ?P (?H * _ * _ * _ * ?Rp * ?W)) = _ =>
      exists (andp P (H * Rp * W)) end.
    apply pred_ext; entailer!.
  - exists FF. rewrite sepcon_FF. reflexivity.
Qed.

Lemma sb_one (gv: globals) (p: val) (ox: option ddx) (k: seqkind) (t: fse_table) :
  seq_where gv p ox k t * sb_ddslot ox k * sb_gslot gv k |--
  EX tp: val, EX sh: share, EX fm: Z, EX Rk: mpred,
    !! (readable_share sh /\
        (seq_ptr_at p k tp * seqtab_at_fm sh k t fm tp * Rk
         |-- seq_where gv p ox k t * sb_ddslot ox k * sb_gslot gv k)) &&
    (seq_ptr_at p k tp * seqtab_at_fm sh k t fm tp * Rk).
Proof.
  unfold seq_where. Intros tp w. destruct w.
  - Intros. subst tp. unfold seqspace_at at 1, seqtab_at. Intros fm.
    Exists (ctx_seq k p) Ews fm
      (data_at_ Ews (tarray t_seqSymbol (sk_size k - 1 - 2 ^ ft_log t))
         (offset_val (8 * (1 + 2 ^ ft_log t)) (ctx_seq k p)) * sb_ddslot ox k * sb_gslot gv k).
    apply andp_right; [apply prop_right | cancel].
    split; [auto with share |].
    Exists (ctx_seq k p) TCtx. unfold seqspace_at, seqtab_at. Exists fm. entailer!.
  - Intros. rename H into Ho. subst tp. unfold sb_ddslot at 1. rewrite Ho.
    unfold seqspace_at at 2, seqtab_at. Intros fm.
    Exists (dd_seq k (ox_q ox)) Ews fm
      (seqspace_at Ews k None (ctx_seq k p) *
       data_at_ Ews (tarray t_seqSymbol (sk_size k - 1 - 2 ^ ft_log t))
         (offset_val (8 * (1 + 2 ^ ft_log t)) (dd_seq k (ox_q ox))) * sb_gslot gv k).
    apply andp_right; [apply prop_right | cancel].
    split; [auto with share |].
    Exists (dd_seq k (ox_q ox)) TDict. try (unfold sb_ddslot; rewrite Ho).
    unfold seqspace_at, seqtab_at. Exists fm. entailer!.
  - Intros. subst t tp. unfold sb_gslot at 1.
    Exists (gv (sk_gdefault k)) Ers predef_fm
      (seqspace_at Ews k None (ctx_seq k p) * sb_ddslot ox k).
    apply andp_right; [apply prop_right | cancel].
    split; [auto with share |].
    Exists (gv (sk_gdefault k)) TGlob. unfold sb_gslot. entailer!.
Qed.

(* the tables of tabs_seq (with the DDict's and the globals' resources), borrowed: their pointers tp, the
   tables at tp (seqtabs_at, readable shares), the rest R; giving them back restores tabs_seq with any
   fseEntropy *)
Lemma seqtabs_borrow (HG: GLOBALS_obligation) (gv: globals) (p: val) (ox: option ddx)
    (t: fse_table * fse_table * fse_table) (fe: Z) :
  tabs_seq gv p ox (Some t) fe * dent_of dent_def gv ox * zstd_globals gv |--
  EX tp: val * val * val, EX sht: share * share * share, EX fm: Z * Z * Z, EX R: mpred,
    !! (seqtabs_sh_ok sht /\
        forall fe': Z,
          field_at Ews t_dctx (DOT _fseEntropy) (Vint (Int.repr fe')) p * seq_ptrs p tp *
          seqtabs_at sht t fm tp * R
          |-- tabs_seq gv p ox (Some t) fe' * dent_of dent_def gv ox * zstd_globals gv) &&
    (field_at Ews t_dctx (DOT _fseEntropy) (Vint (Int.repr fe)) p * seq_ptrs p tp *
     seqtabs_at sht t fm tp * R).
Proof.
  destruct t as [[a b] c].
  destruct (sb_dent_split gv ox) as [Rd Hd]. destruct (HG gv) as [Rg Hg].
  rewrite Hd, Hg. unfold predef_tabs.
  change (seqtab_at_fm Ers KLL LL_predef predef_fm (gv _LL_defaultDTable)) with (sb_gslot gv KLL).
  change (seqtab_at_fm Ers KOF OF_predef predef_fm (gv _OF_defaultDTable)) with (sb_gslot gv KOF).
  change (seqtab_at_fm Ers KML ML_predef predef_fm (gv _ML_defaultDTable)) with (sb_gslot gv KML).
  unfold tabs_seq.
  sep_apply (sb_one gv p ox KLL a). Intros tpa sha fma Ra.
  sep_apply (sb_one gv p ox KOF b). Intros tpb shb fmb Rb.
  sep_apply (sb_one gv p ox KML c). Intros tpc shc fmc Rc.
  Exists (tpa, tpb, tpc) (sha, shb, shc) (fma, fmb, fmc) (Ra * Rb * Rc * Rd * Rg).
  unfold seq_ptrs, seqtabs_at.
  unfold seq_ptr_at in *.
  apply andp_right; [apply prop_right | cancel].
  split; [simpl; auto |].
  intros fe'.
  sep_apply H0. sep_apply H2. sep_apply H4. cancel.
Qed.

(* the input array: a readable copy (the literals LIn) and the window as the bitstream's bit_src *)
Lemma inwin_bits (i: inwin) :
  inwin_ok i ->
  exists sh1 sh2: share, exists R: mpred,
    readable_share sh1 /\ readable_share sh2 /\
    data_at (iw_sh i) (tarray tuchar (iw_N i)) (iw_c i) (iw_base i) =
    data_at sh1 (tarray tuchar (iw_N i)) (iw_c i) (iw_base i) *
    bit_src sh2 (offset_val (iw_off i) (iw_base i)) (iw_s i) * R.
Proof.
  destruct i as [sh base N c off s]; cbn [iw_sh iw_base iw_N iw_c iw_off iw_s].
  intros (Hsh & Hoff & Hn & HN & Hc & _ & Hb & Hsub); cbn [iw_sh iw_base iw_N iw_c iw_off iw_s] in *.
  set (n := Zlength s) in *.
  set (sh1 := fst (slice.cleave sh)). set (sh2 := snd (slice.cleave sh)).
  exists sh1, sh2,
    (!! field_compatible (tarray tuchar N) [] base &&
     (data_at sh2 (tarray tuchar off) (sublist 0 off c) base *
      data_at sh2 (tarray tuchar (N - (off + n))) (sublist (off + n) N c) (offset_val (off + n) base))).
  split; [apply slice.cleave_readable1; exact Hsh|].
  split; [apply slice.cleave_readable2; exact Hsh|].
  rewrite <- (data_at_share_join sh1 sh2 sh) by apply slice.cleave_join.
  rewrite !sepcon_assoc. f_equal.
  unfold bit_src. fold n.
  pose proof (Zlength_nonneg s).
  assert (Hsplit: field_compatible (tarray tuchar N) [] base ->
    data_at sh2 (tarray tuchar N) c base =
    data_at sh2 (tarray tuchar off) (sublist 0 off c) base *
    data_at sh2 (tarray tuchar n) (zbytes s) (offset_val off base) *
    data_at sh2 (tarray tuchar (N - (off + n))) (sublist (off + n) N c) (offset_val (off + n) base)).
  { intros Hfc. unfold tarray. rewrite (split3_data_at_Tarray_tuchar sh2 N off (off + n)) by lia.
    rewrite !field_address0_offset by auto with field_compatible.
    replace (off + n - off) with n by lia. rewrite Hsub. cbn.
    replace (0 + 1 * off) with off by lia. replace (0 + 1 * (off + n)) with (off + n) by lia.
    reflexivity. }
  apply pred_ext.
  - assert_PROP (field_compatible (tarray tuchar N) [] base) as Hfc by entailer!.
    rewrite (Hsplit Hfc). entailer!.
  - Intros. rewrite (Hsplit H0). cancel.
Qed.

(* litExtraBuffer as a byte array *)
Lemma litextra_data_at (p: val) (v: list val) :
  field_at Ews t_dctx (DOT _litExtraBuffer) v p = data_at Ews (tarray tuchar LITEXTRA_N) v (lit_extra p).
Proof.
  unfold lit_extra. rewrite field_at_data_at. reflexivity.
Qed.

(* dictEnd for ZSTD_prefetchMatch's `matchBase != NULL`: either dictend_ok with a non-empty separate
   dictionary (NULL, inside the output array, or inside a non-empty ExtSep dictionary: weakly valid from that
   array), or, for an empty ExtSep dictionary (en = 0), weakly valid from seqs_spec's witnesses W (ext0_ok). *)
Definition dictend_ok_ne (fs: fstate) (o: outarr) (e: ext_seg) : Prop :=
  fs_dictEnd fs = nullval \/
  (exists k, 0 <= k <= oa_N o /\ fs_dictEnd fs = offset_val k (oa_base o)) \/
  (match e with ExtSep _ eb en _ e1 _ => fs_dictEnd fs = offset_val e1 eb /\ 0 <= e1 <= en /\ 0 < en | _ => False end).

Lemma dictend_ok_split (W: list ptr_witness) (fs: fstate) (o: outarr) (e: ext_seg) :
  dictend_ok fs o e -> ext0_ok W fs e ->
  dictend_ok_ne fs o e \/ (pws_pred W |-- weak_valid_pointer (fs_dictEnd fs)).
Proof.
  intros [H|[H|H]] H0; [left; left; exact H | left; right; left; exact H |].
  destruct e as [| e1 elen | sh eb en ec e1 elen]; try contradiction.
  destruct H as [Hd He]. cbn in H0.
  destruct (Z.eq_dec en 0) as [->|Hn].
  - right. apply H0. reflexivity.
  - left. right. right. split; [exact Hd | lia].
Qed.

(* ---------- what the executors read stays defined ----------
   memcpy and memmove are libc.c's byte loops, so the executors need the history, the extDict and the literals
   they read to be defined bytes (exec_spec).  seqs_spec gives this at the start (hist_def, lits_at,
   lit_slack_def); each execution leaves every cell unchanged or a defined byte (exec_spec's xd_ub clause) and
   defines the bytes it writes, so it stays true along the loops. *)

(* the history before dst *)
Lemma hist_def_prefix (oc: list val) (d ps: Z) (e: ext_seg) :
  hist_def oc d ps e -> 0 <= ps <= d -> d <= Zlength oc -> 0 <= ext_len e -> Forall is_byte_val (sublist ps d oc).
Proof.
  intros Hh Hps Hd Hel. apply xd_rng_Forall; [lia | lia |]. intros q Hq.
  specialize (Hh (d - q) ltac:(lia)). unfold chist in Hh.
  rewrite (proj2 (Z.leb_le _ _)) in Hh by lia. replace (d - (d - q)) with q in Hh by lia. exact Hh.
Qed.

(* the extDict *)
Lemma hist_def_ext (oc: list val) (d ps: Z) (e: ext_seg) :
  hist_def oc d ps e -> 0 <= ps <= d -> exec_ext_ok e oc -> ext_def e oc.
Proof.
  intros Hh Hps Hx. destruct e as [|e1 elen|sh eb en ec e1 elen]; simpl; auto.
  - destruct Hx as [Hel [He1 He2]]. simpl in Hel.
    apply xd_rng_Forall; [lia | lia |]. intros q Hq.
    specialize (Hh (d - ps + (e1 - q))). simpl in Hh. specialize (Hh ltac:(lia)). unfold chist in Hh.
    rewrite (proj2 (Z.leb_gt _ _)) in Hh by lia.
    replace (e1 - (d - ps + (e1 - q) - (d - ps))) with q in Hh by lia. exact Hh.
  - destruct Hx as [Hel [_ [Hen [_ [He1 He2]]]]]. simpl in Hel.
    apply xd_rng_Forall; [lia | lia |]. intros q Hq.
    specialize (Hh (d - ps + (e1 - q))). simpl in Hh. specialize (Hh ltac:(lia)). unfold chist in Hh.
    rewrite (proj2 (Z.leb_gt _ _)) in Hh by lia.
    replace (e1 - (d - ps + (e1 - q) - (d - ps))) with q in Hh by lia. exact Hh.
Qed.

(* a defined range stays defined when every cell is unchanged or a defined byte *)
Lemma Forall_def_ub (c c': list val) (a b: Z) :
  Zlength c' = Zlength c -> xd_ub c c' -> 0 <= a -> b <= Zlength c ->
  Forall is_byte_val (sublist a b c) -> Forall is_byte_val (sublist a b c').
Proof.
  intros HL Hu Ha Hb H. destruct (Z_le_gt_dec a b) as [Hab|Hab].
  - apply xd_rng_Forall; [lia | lia |]. apply (xd_rng_ub c); auto. apply xd_Forall_rng; auto.
  - rewrite sublist_nil_gen by lia. constructor.
Qed.

Lemma ext_def_ub (x: ext_seg) (c c': list val) :
  Zlength c' = Zlength c -> xd_ub c c' -> exec_ext_ok x c -> ext_def x c -> ext_def x c'.
Proof.
  intros HL Hu Hx Hd. destruct x as [|e1 elen|sh eb en ec e1 elen]; simpl in *; auto.
  destruct Hx as [_ [He1 He2]]. apply (Forall_def_ub c); auto; lia.
Qed.

Lemma lit_def_ub (ls: litsrc) (c c': list val) (a b: Z) :
  Zlength c' = Zlength c -> xd_ub c c' -> 0 <= a -> b <= Zlength (lit_arr ls c) ->
  Forall is_byte_val (sublist a b (lit_arr ls c)) -> Forall is_byte_val (sublist a b (lit_arr ls c')).
Proof. intros HL Hu Ha Hb H. destruct ls; simpl in *; auto. apply (Forall_def_ub c); auto. Qed.

(* two adjacent defined ranges *)
Lemma Forall_def_join (l: list val) (a b d: Z) :
  0 <= a <= b -> b <= d -> d <= Zlength l ->
  Forall is_byte_val (sublist a b l) -> Forall is_byte_val (sublist b d l) -> Forall is_byte_val (sublist a d l).
Proof. intros. rewrite (sublist_split a b d) by lia. apply Forall_app; auto. Qed.
