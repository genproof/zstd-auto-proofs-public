(* API v3, subtree B, group BLK, sub-group TOP: v2's B/blk/BlkTOP.v with
   ZSTD_decompressBlock_internal holding cfg_lit p instead of cfg_lit p (DecIface3.ZSTD_decompressBlock_internal_spec3)
   and calling BSpecs3.ZSTD_decodeLiteralsBlock_spec3. *)
Require Export Zstd.proof.dec.v3.B.BSpecs3.
Require Import Zstd.proof.dec.v3.B.BlkTOPExact.
Require Import Zstd.proof.model.ExHuf Zstd.proof.model.ExBlock.
Local Open Scope logic.

(* ===================== the helpers' specifications ===================== *)

Definition t_offinfo : type := Tstruct ___gp_ZSTD_OffsetInfo noattr.

(* ZSTD_totalHistorySize(curPtr, virtualStart): curPtr - virtualStart, two pointers of one block; the
   difference may be any size_t (CompCert's pointer subtraction wraps modulo 2^64, and the result is cast to
   size_t): the history of an output buffer and a separate dictionary of up to 2^63 - 1 bytes each *)
Definition ZSTD_totalHistorySize_spec : ident * funspec :=
  DECLARE _ZSTD_totalHistorySize
  WITH b: val, i: Z, j: Z
  PRE [ tptr tvoid, tptr tvoid ]
    PROP (isptr b; 0 <= i - j <= Int64.max_unsigned)
    PARAMS (offset_val i b; offset_val j b) SEP ()
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr (i - j))) SEP ().

(* ZSTD_getOffsetInfo(&info, offTable, nbSeq): reads the offset table t (wherever it is: a context, a
   DDict, the globals); the two counters are some numbers (they only choose between equivalent
   sequence decoders) *)
Definition ZSTD_getOffsetInfo_spec : ident * funspec :=
  DECLARE _ZSTD_getOffsetInfo
  WITH shi: share, pi: val, sh: share, t: fse_table, fm: Z, tp: val, nbSeq: Z
  PRE [ tptr t_offinfo, tptr t_seqSymbol, tint ]
    PROP (writable_share shi; readable_share sh; Int.min_signed <= nbSeq <= Int.max_signed)
    PARAMS (pi; tp; Vint (Int.repr nbSeq))
    SEP (data_at_ shi t_offinfo pi; seqtab_at_fm sh KOF t fm tp)
  POST [ tvoid ]
    EX ls: Z, EX mx: Z,
    PROP () RETURN ()
    SEP (data_at shi t_offinfo (Vint (Int.repr ls), Vint (Int.repr mx)) pi; seqtab_at_fm sh KOF t fm tp).

(* ZSTD_maxShortOffset(): (size_t)-1 (64 bits) *)
Definition ZSTD_maxShortOffset_spec : ident * funspec :=
  DECLARE _ZSTD_maxShortOffset
  WITH u: unit
  PRE [ ] PROP () PARAMS () SEP ()
  POST [ tulong ] PROP () RETURN (Vlong (Int64.repr (-1))) SEP ().

(* The export with its one defect repaired (the block export needs the history to be
   defined): a success gives defined bytes when the history zstd may read is defined (hist_def) and an
   extDict in the output array is out of the block's way (ext_clean), as the sequence decoders promise.
   Everything else is DecIface3.ZSTD_decompressBlock_internal_spec3 dent_def tabs_def. *)
Definition ZSTD_decompressBlock_internal_fixed_spec : ident * funspec :=
  DECLARE _ZSTD_decompressBlock_internal
  WITH gv: globals, p: val, fs: fstate, ox: option ddx, ts: tstate, bsm: Z, streaming: Z,
       W: list ptr_witness, o: outarr, i: inwin, h: hctx
  PRE [ tptr t_dctx, tptr tvoid, tulong, tptr tvoid, tulong, tint ]
    PROP (outarr_ok o; inwin_ok i;
          streaming = 0 \/ streaming = 1;
          0 <= bsm <= ZSTD_BLOCKSIZE_MAX;
          fp_blockSizeMax (fs_fParams fs) = Vint (Int.repr bsm);
          fs_isFrameDecompression fs = Vint (Int.repr 1);
          fs_ddictIsCold fs = Vint (Int.repr 0) \/ fs_ddictIsCold fs = Vint (Int.repr 1);
          oa_cap o = 0 -> (pws_pred W |-- weak_valid_pointer (offset_val (oa_d o) (oa_base o)));
          0 < oa_cap o -> layout_ok fs (oa_base o) (oa_N o) (oa_d o) (hc_ps h) (hc_ext h);
          (match hc_ext h with ExtIn _ _ => streaming = 1 | _ => True end);
          hist_ptrs_ok fs o (hc_ext h); ext0_ok W fs (hc_ext h);
          (* the history the matches copy holds defined bytes (memcpy and memmove are libc.c's byte loops) *)
          hist_def (oa_c o) (oa_d o) (hc_ps h) (hc_ext h))
    PARAMS (p; offset_val (oa_d o) (oa_base o); Vlong (Int64.repr (oa_cap o));
            offset_val (iw_off i) (iw_base i); Vlong (Int64.repr (Zlength (iw_s i))); Vint (Int.repr streaming))
    GLOBALS (gv)
    SEP (zstd_globals gv; pws_pred W; cfg_lit p; frame_fields p fs; tabs_def gv p ox ts; dent_of dent_def gv ox;
         data_at (oa_sh o) (tarray tuchar (oa_N o)) (oa_c o) (oa_base o);
         data_at (iw_sh i) (tarray tuchar (iw_N i)) (iw_c i) (iw_base i); ext_res (hc_ext h))
  POST [ tulong ]
    EX r: Z, EX oc': list val, EX cold: val, EX ts': option tstate,
    PROP (0 <= r <= Int64.max_unsigned; Zlength oc' = oa_N o;
          unchanged_outside (oa_c o) oc' (oa_d o) (oa_d o + oa_cap o);
          (byte_cells (oa_c o) -> byte_cells (iw_c i) -> ext_bytes (hc_ext h) -> byte_cells oc');
          is_error_code r = false ->
            r <= oa_cap o /\ cold = Vint (Int.repr 0) /\ ts' <> None /\
            (streaming = 1 -> r <= bsm ->
             unchanged_outside (oa_c o) oc' (oa_d o) (oa_d o + Z.min (oa_cap o) (bsm + WILDCOPY_OVERLENGTH))) /\
            (hist_def (oa_c o) (oa_d o) (hc_ps h) (hc_ext h) ->
             (ext_clean (oa_d o) (oa_cap o) (hc_ext h) \/ (r <= bsm /\ ext_far (oa_d o) (oa_cap o) bsm (hc_ext h))) ->
             exists cnt, sublist (oa_d o) (oa_d o + r) oc' = zbytes cnt /\ bytes_ok cnt);
          is_error_code r = true -> ts' = None /\ dec_err r;
          cold = fs_ddictIsCold fs \/ cold = Vint (Int.repr 0);
          oa_cap o = 0 \/
          (hist_view (oa_c o) (oa_d o) (hc_ps h) (hc_ext h) (hc_hist h) (hc_out h) (hc_wsize h) /\
           ext_clear (oa_d o) (hc_ps h) (oa_cap o) bsm (hc_ext h) (hc_hist h) (hc_out h) (hc_wsize h)) ->
            bytes_ok (hc_hist h) -> bytes_ok (hc_out h) ->
            block_ok ts (hc_hist h) (hc_out h) (iw_s i) bsm (hc_wsize h) streaming (oa_c o) oc'
              (oa_d o) (oa_cap o) r (option_map ts_d ts');
          ox = None -> block_exact ts o i h bsm streaming r oc' ts')
    RETURN (Vlong (Int64.repr r))
    SEP (zstd_globals gv; pws_pred W; cfg_lit p; frame_fields p (fs_set_cold fs cold);
         match ts' with Some ts2 => tabs_def gv p ox ts2 | None => EX lxb: list Z, tables_uninit p lxb end;
         dent_of dent_def gv ox;
         data_at (oa_sh o) (tarray tuchar (oa_N o)) oc' (oa_base o);
         data_at (iw_sh i) (tarray tuchar (iw_N i)) (iw_c i) (iw_base i); ext_res (hc_ext h)).

Definition TOP3_S : funspecs :=
  [ ZSTD_totalHistorySize_spec; ZSTD_getOffsetInfo_spec; ZSTD_maxShortOffset_spec;
    ZSTD_decompressBlock_internal_spec3 dent_def tabs_def ].
Definition TOP3_G : funspecs := (G_BLK ++ TOP3_imports) ++ TOP3_S.

(* ===================== model facts ===================== *)

Section TopDsh.
Local Open Scope Z_scope.

Lemma top_dsh_le_value_bound (l: list Z) :
  Forall is_byte l -> 0 <= le_value l < 256 ^ Zlength l.
Proof.
  induction l as [|x l IH]; intros H; cbn [le_value].
  - rewrite ?Zlength_nil. simpl. lia.
  - inversion H as [|? ? Hx Hl]; subst. specialize (IH Hl). unfold is_byte in Hx.
    rewrite Zlength_cons, Z.pow_succ_r by (rewrite Zlength_correct; lia). nia.
Qed.

Lemma top_dsh_le_field_bound (b: list Z) :
  bytes_ok b -> 0 <= le_field b 1 2 <= 65535.
Proof.
  intros Hb. unfold le_field, slice.
  assert (Hf: Forall is_byte (firstn (Z.to_nat 2) (skipn (Z.to_nat 1) b))).
  { pose proof (firstn_skipn (Z.to_nat 1) b) as E1. rewrite <- E1 in Hb.
    apply Forall_app in Hb as [_ Hb].
    pose proof (firstn_skipn (Z.to_nat 2) (skipn (Z.to_nat 1) b)) as E2. rewrite <- E2 in Hb.
    apply Forall_app in Hb as [Hb _]. exact Hb. }
  pose proof (top_dsh_le_value_bound _ Hf) as [H0 H1].
  assert (Hl: Zlength (firstn (Z.to_nat 2) (skipn (Z.to_nat 1) b)) <= 2).
  { rewrite Zlength_correct, firstn_length. lia. }
  assert (256 ^ Zlength (firstn (Z.to_nat 2) (skipn (Z.to_nat 1) b)) <= 256 ^ 2).
  { apply Z.pow_le_mono_r; [lia | exact Hl]. }
  lia.
Qed.

Lemma top_dsh_byte_at_bound (b: list Z) i :
  bytes_ok b -> 0 <= byte_at b i < 256.
Proof.
  intros Hb. unfold byte_at.
  destruct (lt_dec (Z.to_nat i) (length b)) as [Hi|Hi].
  - eapply Forall_forall in Hb; [exact Hb | apply nth_In, Hi].
  - rewrite nth_overflow by lia. lia.
Qed.

Lemma top_dsh_seq_table_le mode predef prev max maxLog (b: list Z) t k :
  seq_table mode predef prev max maxLog b = Some (t, k) -> k <= Zlength b.
Proof.
  assert (Hn: 0 <= Zlength b) by (rewrite Zlength_correct; lia).
  unfold seq_table. intros H.
  destruct (mode =? 0); [inversion H; lia|].
  destruct (mode =? 1).
  { destruct (Zlength b <? 1) eqn:E; [discriminate|].
    destruct (byte_at b 0 >? max); [discriminate|]. inversion H; subst. lia. }
  destruct (mode =? 3).
  { destruct prev; inversion H; lia. }
  unfold read_ncount in H.
  destruct (Zlength b =? 0); [discriminate|].
  destruct (_ >? FSE_TABLELOG_ABSOLUTE_MAX); [discriminate|].
  destruct (ncount_loop _ _ _ _ _ _ _ _ _) as [[[norm rem] p]|]; [|discriminate].
  destruct (negb _); [discriminate|].
  destruct (Zlength norm >? _); [discriminate|].
  destruct ((p + 7) / 8 >? Zlength b) eqn:E; [discriminate|].
  destruct (_ >? maxLog); [discriminate|].
  rewrite Z.gtb_ltb in E. apply Z.ltb_ge in E. injection H as _ <-. exact E.
Qed.

Lemma top_dsh_skipn_le (b: list Z) p :
  p <= Zlength b -> p + Zlength (skipn (Z.to_nat p) b) <= Zlength b.
Proof.
  intros H. rewrite !Zlength_correct in *. rewrite skipn_length. lia.
Qed.

End TopDsh.

(* the sequences section's header: the number of sequences, the tables, the bytes it takes *)
Lemma top_dsh_facts (prev: option (fse_table * fse_table * fse_table)) (b: list Z) nb t used :
  bytes_ok b -> decode_seq_header prev b = Some (nb, t, used) ->
  0 <= nb <= LONGNBSEQ + 65535 /\ used <= Zlength b /\ (nb = 0 -> t = prev) /\ (nb <> 0 -> t <> None).
Proof.
  intros Hb H. unfold decode_seq_header in H.
  pose proof (top_dsh_byte_at_bound b 0 Hb) as B0.
  pose proof (top_dsh_byte_at_bound b 1 Hb) as B1.
  pose proof (top_dsh_le_field_bound b Hb) as LF.
  unfold LONGNBSEQ in *.
  destruct (Zlength b <? 1) eqn:En; [discriminate|].
  assert (Hnb: exists nbSeq pos ok,
             (if byte_at b 0 <=? 127 then (byte_at b 0, 1, true)
              else if byte_at b 0 =? 255 then (le_field b 1 2 + 32512, 3, 3 <=? Zlength b)
              else ((byte_at b 0 - 128) * 256 + byte_at b 1, 2, 2 <=? Zlength b))%Z = (nbSeq, pos, ok) /\
             (0 <= nbSeq <= 32512 + 65535)%Z).
  { destruct (byte_at b 0 <=? 127) eqn:E1; [eexists _, _, _; split; [reflexivity|lia]|].
    destruct (byte_at b 0 =? 255) eqn:E2; [eexists _, _, _; split; [reflexivity|lia]|].
    eexists _, _, _; split; [reflexivity|]. apply Z.leb_gt in E1. apply Z.eqb_neq in E2. lia. }
  destruct Hnb as (nbSeq & pos & ok & Heq & Hr).
  rewrite Heq in H. clear Heq.
  destruct (negb ok); [discriminate|].
  destruct (nbSeq =? 0) eqn:Ez.
  { destruct (pos =? Zlength b) eqn:Ep; [|discriminate].
    inversion H; subst. apply Z.eqb_eq in Ep. split; [lia|]. split; [lia|]. split; [auto|]. lia. }
  destruct (pos + 1 >? Zlength b) eqn:Ep; [discriminate|]. rewrite Z.gtb_ltb in Ep. apply Z.ltb_ge in Ep.
  destruct (negb _); [discriminate|].
  destruct (seq_table _ LL_predef _ MaxLL LLFSELog _) as [[tLL k1]|] eqn:T1; [|discriminate].
  destruct (seq_table _ OF_predef _ MaxOff OffFSELog _) as [[tOF k2]|] eqn:T2; [|discriminate].
  destruct (seq_table _ ML_predef _ MaxML MLFSELog _) as [[tML k3]|] eqn:T3; [|discriminate].
  inversion H; subst. apply Z.eqb_neq in Ez.
  apply top_dsh_seq_table_le in T1, T2, T3.
  pose proof (top_dsh_skipn_le b (pos + 1) Ep).
  pose proof (top_dsh_skipn_le b (pos + 1 + k1) ltac:(lia)).
  pose proof (top_dsh_skipn_le b (pos + 1 + k1 + k2) ltac:(lia)).
  split; [lia|]. split; [lia|]. split; [lia|]. discriminate.
Qed.

(* executing sequences never loses bytes: what is output plus the literals left grows *)
Lemma top_exec_len (wsize: Z) (rep: Z * Z * Z) (hist lits out: list Z) (seqs: list sequence)
    (out' lits': list Z) (rep': Z * Z * Z) :
  exec_seqs wsize rep hist lits out seqs = Some (out', lits', rep') ->
  Zlength out + Zlength lits <= Zlength out' + Zlength lits'.
Proof.
  revert rep lits out. induction seqs as [|sq rest IH]; intros rep lits out H.
  - simpl in H. inversion H; subst. lia.
  - simpl in H.
    destruct (sq_ll sq >? Zlength lits) eqn:Ell; [discriminate|].
    destruct (resolve_offset rep (sq_ll sq) (sq_ov sq)) as [[offset rep2]|]; [|discriminate].
    destruct (offset >? Zlength hist + Zlength (out ++ firstn (Z.to_nat (sq_ll sq)) lits)); [discriminate|].
    destruct (offset >? wsize + Zlength hist); [discriminate|].
    apply IH in H.
    rewrite BlkModel.lz_copy_length in H.
    assert (E: Zlength (out ++ firstn (Z.to_nat (sq_ll sq)) lits) + Zlength (skipn (Z.to_nat (sq_ll sq)) lits)
               = Zlength out + Zlength lits).
    { rewrite Zlength_app, !Zlength_correct, length_firstn, length_skipn.
      rewrite Z.gtb_ltb in Ell. apply Z.ltb_ge in Ell. rewrite Zlength_correct in Ell. lia. }
    lia.
Qed.

Lemma top_nth_forall {A} (P: A -> Prop) (l: list A) (d: A) (n: nat) : Forall P l -> P d -> P (nth n l d).
Proof. intros H Hd. revert n; induction H; intros [|n]; simpl; auto. Qed.

Lemma top_peek_nonneg (s: list Z) (pos nb: Z) : 0 <= nb -> 0 <= bs_peek_s s pos nb.
Proof.
  intros Hnb. unfold bs_peek_s. destruct (pos <? 0) eqn:E1; [lia|]. apply Z.ltb_ge in E1.
  destruct (pos - nb >=? 0).
  - apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
  - apply Z.mul_nonneg_nonneg.
    + apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
    + apply Z.pow_nonneg; lia.
Qed.

Lemma top_ml_base (c: Z) : 0 <= c <= MaxML -> 3 <= nth (Z.to_nat c) ML_base_tab 0.
Proof.
  intros Hc. assert (F: Forall (fun x => 3 <= x) ML_base_tab) by (repeat constructor; lia).
  rewrite Forall_forall in F. apply F, nth_In. unfold ML_base_tab, MaxML in *. simpl. lia.
Qed.

Lemma top_seqs_first tLL tOF tML V k sLL sOF sML pos l p :
  fse_ok KML tML -> decode_seqs tLL tOF tML V (S k) sLL sOF sML pos = Some (l, p) ->
  exists sq rest, l = sq :: rest /\ 3 <= sq_ml sq.
Proof.
  intros Hok H.
  assert (Hc: 0 <= fe_sym (fse_cell tML sML) <= MaxML).
  { destruct Hok as (_ & _ & F). unfold fse_cell.
    apply (top_nth_forall (fun e => 0 <= fe_sym e <= MaxML)); [|simpl; unfold MaxML; lia].
    eapply Forall_impl; [|exact F]. intros e He. simpl in He. lia. }
  assert (Hb: 0 <= nth (Z.to_nat (fe_sym (fse_cell tML sML))) ML_bits_tab 0).
  { apply top_nth_forall; [repeat constructor; lia | lia]. }
  pose proof (top_ml_base _ Hc) as Hbase.
  cbn [decode_seqs] in H.
  pose proof (top_peek_nonneg V (pos - fe_sym (fse_cell tOF sOF))
                (nth (Z.to_nat (fe_sym (fse_cell tML sML))) ML_bits_tab 0) Hb) as Hpk.
  set (b0 := nth (Z.to_nat (fe_sym (fse_cell tML sML))) ML_base_tab 0) in *. clearbody b0.
  set (n0 := nth (Z.to_nat (fe_sym (fse_cell tML sML))) ML_bits_tab 0) in *. clearbody n0.
  unfold rd at 1 in H. destruct (_ <? 0); [discriminate|].
  unfold rd at 1 in H. destruct (_ <? 0); [discriminate|].
  unfold rd at 1 in H. destruct (_ <? 0); [discriminate|].
  destruct k as [|k']; [inversion H; subst; eexists _, _; split; [reflexivity|cbn [sq_ml]; lia]|].
  repeat match type of H with
  | context [match rd ?a ?b ?c with _ => _ end] => destruct (rd a b c) as [[? ?]|]; [|discriminate]
  end.
  match type of H with
  | context [match ?d with Some _ => _ | None => _ end] =>
      match d with decode_seqs _ _ _ _ _ _ _ _ _ => destruct d as [[? ?]|]; [|discriminate] end
  end.
  inversion H; subst; eexists _, _; split; [reflexivity|cbn [sq_ml]; lia].
Qed.

(* ... and strictly when there is a sequence: a match is at least 3 bytes (ML_base) *)
Lemma top_exec_pos (wsize: Z) (rep: Z * Z * Z) (hist lits out: list Z) tLL tOF tML (s: list Z) (nb: Z)
    (seqs: list sequence) (out' lits': list Z) (rep': Z * Z * Z) :
  fse_ok KML tML -> 0 < nb ->
  decode_seq_stream tLL tOF tML s nb = Some seqs ->
  exec_seqs wsize rep hist lits out seqs = Some (out', lits', rep') ->
  Zlength out + Zlength lits < Zlength out' + Zlength lits'.
Proof.
  intros Hok Hnb Hd He.
  unfold decode_seq_stream in Hd.
  destruct (negb (bs_okb s)); [discriminate|].
  destruct (rd s (bs_total s) (ft_log tLL)) as [[sLL p1]|]; [|discriminate].
  destruct (rd s p1 (ft_log tOF)) as [[sOF p2]|]; [|discriminate].
  destruct (rd s p2 (ft_log tML)) as [[sML p3]|]; [|discriminate].
  destruct (decode_seqs tLL tOF tML s (Z.to_nat nb) sLL sOF sML p3) as [[l p]|] eqn:Ed; [|discriminate].
  destruct p; try discriminate. inversion Hd; subst l.
  destruct (Z.to_nat nb) as [|k] eqn:En; [lia|].
  destruct (top_seqs_first _ _ _ _ _ _ _ _ _ _ _ Hok Ed) as (sq & rest & -> & Hml).
  simpl in He.
  destruct (sq_ll sq >? Zlength lits) eqn:Ell; [discriminate|].
  destruct (resolve_offset rep (sq_ll sq) (sq_ov sq)) as [[offset rep2]|]; [|discriminate].
  destruct (offset >? Zlength hist + Zlength (out ++ firstn (Z.to_nat (sq_ll sq)) lits)); [discriminate|].
  destruct (offset >? wsize + Zlength hist); [discriminate|].
  apply top_exec_len in He.
  rewrite BlkModel.lz_copy_length, Z2Nat.id in He by lia.
  assert (E: Zlength (out ++ firstn (Z.to_nat (sq_ll sq)) lits) + Zlength (skipn (Z.to_nat (sq_ll sq)) lits)
             = Zlength out + Zlength lits).
  { rewrite Zlength_app, !Zlength_correct, length_firstn, length_skipn.
    rewrite Z.gtb_ltb in Ell. apply Z.ltb_ge in Ell. rewrite Zlength_correct in Ell. lia. }
  lia.
Qed.

(* the input window after k bytes *)
Definition iw_skip (i: inwin) (k: Z) : inwin :=
  {| iw_sh := iw_sh i; iw_base := iw_base i; iw_N := iw_N i; iw_c := iw_c i; iw_off := iw_off i + k;
     iw_s := skipn (Z.to_nat k) (iw_s i) |}.

Lemma tp_skip_len (s: list Z) (k: Z) : 0 <= k <= Zlength s -> Zlength (skipn (Z.to_nat k) s) = Zlength s - k.
Proof. intros H. rewrite !Zlength_correct, length_skipn. rewrite Zlength_correct in H. lia. Qed.

Lemma tp_bytes_skip (s: list Z) (k: nat) : bytes_ok s -> bytes_ok (skipn k s).
Proof. unfold bytes_ok. intros H. apply Forall_skipn. exact H. Qed.

Lemma tp_win_skip (i: inwin) (k: Z) :
  inwin_ok i -> 0 <= k <= Zlength (iw_s i) ->
  inwin_ok (iw_skip i k) /\ Zlength (iw_s (iw_skip i k)) = Zlength (iw_s i) - k.
Proof.
  intros (Hsh & Ho & Hn & HN & Hc & _ & Hb & Hw) Hk.
  assert (L: Zlength (iw_s (iw_skip i k)) = Zlength (iw_s i) - k) by (apply tp_skip_len; lia).
  split; [| exact L].
  unfold inwin_ok, win_ok. simpl in *. rewrite L.
  repeat split; auto; try lia.
  - apply tp_bytes_skip; auto.
  - replace (iw_off i + k + (Zlength (iw_s i) - k)) with (iw_off i + Zlength (iw_s i)) by lia.
    assert (E: sublist (iw_off i + k) (iw_off i + Zlength (iw_s i)) (iw_c i) =
               sublist k (Zlength (iw_s i)) (sublist (iw_off i) (iw_off i + Zlength (iw_s i)) (iw_c i))).
    { rewrite sublist_sublist by lia. f_equal; lia. }
    rewrite E, Hw, sublist_map. f_equal. unfold sublist.
    rewrite firstn_same; [reflexivity | rewrite Zlength_correct; lia].
Qed.

Lemma tp_db_hdr_none ts hist out s bsm wsize r1 lits oh' :
  match decode_literals (st_huf ts) s bsm with
  | Some (lits0, used, huf') => r1 = used /\ lits = lits0 /\ oh' = huf'
  | None => True
  end ->
  decode_seq_header (st_seq ts) (skipn (Z.to_nat r1) s) = None ->
  decode_block ts hist out s bsm wsize = None.
Proof.
  intros Hdl Hn. unfold decode_block.
  destruct (Zlength s >? bsm); [reflexivity |].
  destruct (decode_literals (st_huf ts) s bsm) as [[[lits0 u] hf]|]; [|reflexivity].
  destruct Hdl as [-> _]. rewrite Hn. reflexivity.
Qed.

(* the content of a block that decodes holds all its literals *)
Lemma tp_content_len (out out' lits': list Z) :
  (exists mid, out' = out ++ mid) ->
  Zlength (skipn (length out) (out' ++ lits')) = Zlength out' + Zlength lits' - Zlength out.
Proof.
  intros [mid ->]. rewrite <- app_assoc, skipn_app, skipn_all, Nat.sub_diag. simpl.
  rewrite !Zlength_app. lia.
Qed.

Lemma tp_db_lits ts hist out s bsm wsize ts2 cnt :
  decode_block ts hist out s bsm wsize = Some (ts2, cnt) ->
  exists lits0 u hf, decode_literals (st_huf ts) s bsm = Some (lits0, u, hf) /\
    Zlength lits0 <= Zlength cnt <= bsm.
Proof.
  unfold decode_block. intros H.
  destruct (Zlength s >? bsm); [discriminate |].
  destruct (decode_literals (st_huf ts) s bsm) as [[[lits0 u] hf]|]; [|discriminate].
  exists lits0, u, hf. split; [reflexivity |].
  destruct (decode_seq_header _ _) as [[[nb tabs] hu]|]; [|discriminate].
  match type of H with context [match ?X with Some _ => _ | None => None end] =>
    destruct X as [seqs|] end; [|discriminate].
  destruct (exec_seqs wsize (st_rep ts) hist lits0 out seqs) as [[[out' lits'] rep']|] eqn:E; [|discriminate].
  destruct (Zlength (skipn (length out) (out' ++ lits')) >? bsm) eqn:Eb; [discriminate |].
  inversion H; subst cnt. rewrite Z.gtb_ltb in Eb. apply Z.ltb_ge in Eb.
  pose proof (top_exec_len _ _ _ _ _ _ _ _ _ E).
  rewrite tp_content_len by (eapply exec_seqs_app; eauto). split; [lia |].
  rewrite tp_content_len in Eb by (eapply exec_seqs_app; eauto). lia.
Qed.

(* ---------- the output array across the two writers ---------- *)

Lemma tp_unch_trans (a b c: list val) (lo hi lo' hi': Z) :
  Zlength a = Zlength b ->
  unchanged_outside a b lo hi -> unchanged_outside b c lo' hi' -> lo <= lo' -> hi' <= hi ->
  unchanged_outside a c lo hi.
Proof.
  intros L H1 H2 Hl Hh k Hk Hn. rewrite (H2 k) by lia. apply H1; auto.
Qed.

Lemma tp_unch_mono (a b: list val) (lo hi lo' hi': Z) :
  unchanged_outside a b lo hi -> lo' <= lo -> hi <= hi' -> unchanged_outside a b lo' hi'.
Proof. intros H Hl Hh k Hk Hn. apply H; auto. lia. Qed.

(* streaming, a block of r <= bsm bytes: the literals' and the sequences' write bounds compose *)
Lemma tp_stream_unch (oc oc1 oc': list val) (d cap bsm r streaming: Z) :
  Zlength oc = Zlength oc1 ->
  (streaming = 1 -> unchanged_outside oc oc1 d (d + Z.min cap bsm)) ->
  unchanged_outside oc1 oc' d (d + Z.min cap (r + WILDCOPY_OVERLENGTH)) ->
  0 <= cap -> 0 <= bsm -> r <= bsm -> streaming = 1 ->
  unchanged_outside oc oc' d (d + Z.min cap (bsm + WILDCOPY_OVERLENGTH)).
Proof.
  intros L Us U2 Hc Hb Hr Hs. specialize (Us Hs).
  apply (tp_unch_trans oc oc1 oc' d (d + Z.min cap (bsm + WILDCOPY_OVERLENGTH)) d
           (d + Z.min cap (r + WILDCOPY_OVERLENGTH))); auto; try (unfold WILDCOPY_OVERLENGTH; lia).
  apply (tp_unch_mono _ _ d (d + Z.min cap bsm)); auto; unfold WILDCOPY_OVERLENGTH; lia.
Qed.

(* an index outside [lo, hi) keeps its byte, also outside the array *)
Lemma tp_unch_at (a b: list val) (lo hi k: Z) :
  Zlength a = Zlength b -> unchanged_outside a b lo hi -> ~ (lo <= k < hi) -> Znth k b = Znth k a.
Proof.
  intros L H Hn. destruct (zlt k 0).
  - rewrite !Znth_underflow by lia. reflexivity.
  - destruct (zlt k (Zlength a)).
    + apply H; auto. lia.
    + rewrite !Znth_overflow by lia. reflexivity.
Qed.

Lemma tp_hist_def_transfer (oc oc1: list val) (d cap ps: Z) (e: ext_seg) :
  Zlength oc = Zlength oc1 -> unchanged_outside oc oc1 d (d + cap) -> 0 <= cap -> 0 <= ps <= d ->
  ext_clean d cap e -> hist_def oc d ps e -> hist_def oc1 d ps e.
Proof.
  intros L U Hc Hps Hcl Hd k Hk. specialize (Hd k Hk). unfold chist in *.
  destruct (k <=? d - ps) eqn:E.
  - apply Z.leb_le in E. rewrite (tp_unch_at oc oc1 d (d + cap)) by (auto; lia). exact Hd.
  - apply Z.leb_gt in E. destruct e as [| e1 elen | sh eb en ec e1 elen]; simpl in *; auto.
    rewrite (tp_unch_at oc oc1 d (d + cap)) by (auto; unfold WILDCOPY_OVERLENGTH in *; lia). exact Hd.
Qed.

Lemma tp_hist_def_far (oc oc1: list val) (d cap bsm ps: Z) (e: ext_seg) (streaming: Z) :
  Zlength oc = Zlength oc1 -> unchanged_outside oc oc1 d (d + cap) ->
  (streaming = 1 -> unchanged_outside oc oc1 d (d + Z.min cap bsm)) ->
  (match e with ExtIn _ _ => streaming = 1 | _ => True end) -> 0 <= cap -> 0 <= bsm -> 0 <= ps <= d ->
  ext_far d cap bsm e -> hist_def oc d ps e -> hist_def oc1 d ps e.
Proof.
  intros L U Us Hs Hc Hb Hps Hfar Hd k Hk. specialize (Hd k Hk). unfold chist in *.
  destruct (k <=? d - ps) eqn:E.
  - apply Z.leb_le in E. rewrite (tp_unch_at oc oc1 d (d + cap)) by (auto; lia). exact Hd.
  - apply Z.leb_gt in E. destruct e as [| e1 elen | sh eb en ec e1 elen]; simpl in *; auto.
    specialize (Us Hs).
    rewrite (tp_unch_at oc oc1 d (d + Z.min cap bsm)) by (auto; unfold WILDCOPY_OVERLENGTH in *; lia). exact Hd.
Qed.

(* a write of defined bytes only (a defined cell stays defined) keeps the history defined, wherever the extDict is *)
Lemma tp_hist_def_keep (oc oc1: list val) (d ps: Z) (e: ext_seg) :
  (forall j, 0 <= j < Zlength oc -> is_byte_val (Znth j oc) -> is_byte_val (Znth j oc1)) ->
  hist_def oc d ps e -> hist_def oc1 d ps e.
Proof.
  intros K Hd k Hk. specialize (Hd k Hk). unfold chist in *.
  assert (R: forall j, is_byte_val (Znth j oc) -> is_byte_val (Znth j oc1)).
  { intros j Hj. apply K; [| exact Hj].
    destruct (zlt j 0); [rewrite Znth_underflow in Hj by lia; destruct Hj as (z & _ & Ez); discriminate |].
    destruct (zlt j (Zlength oc)); [lia |].
    rewrite Znth_overflow in Hj by lia. destruct Hj as (z & _ & Ez); discriminate. }
  destruct (k <=? d - ps); [apply R; exact Hd |].
  destruct e; auto.
Qed.

Lemma tp_hist_view_transfer (oc oc1: list val) (d cap bsm ps: Z) (e: ext_seg) (hist out: list Z) (w streaming: Z) :
  Zlength oc = Zlength oc1 -> unchanged_outside oc oc1 d (d + cap) ->
  (streaming = 1 -> unchanged_outside oc oc1 d (d + Z.min cap bsm)) ->
  (match e with ExtIn _ _ => streaming = 1 | _ => True end) -> 0 <= cap -> 0 <= bsm -> 0 <= ps <= d ->
  hist_view oc d ps e hist out w -> ext_clear d ps cap bsm e hist out w -> hist_view oc1 d ps e hist out w.
Proof.
  intros L U Us He Hc Hb Hps Hv Hcl k Hk. destruct (Hv k Hk) as [Hk1 Hv1]. split; [exact Hk1 |].
  rewrite <- Hv1. unfold chist.
  destruct (k <=? d - ps) eqn:E.
  - apply Z.leb_le in E. apply (tp_unch_at oc oc1 d (d + cap)); auto. lia.
  - apply Z.leb_gt in E. destruct e as [| e1 elen | sh eb en ec e1 elen]; auto.
    specialize (Us He). specialize (Hcl k ltac:(lia)).
    apply (tp_unch_at oc oc1 d (d + Z.min cap bsm)); auto.
    unfold WILDCOPY_OVERLENGTH in Hcl. lia.
Qed.

(* ---------- the block in the model, piece by piece ---------- *)

Lemma tp_db_some ts hist out s bsm wsize r1 lits oh' nb os' used ts2 cnt :
  match decode_literals (st_huf ts) s bsm with
  | Some (lits0, u, huf') => r1 = u /\ lits = lits0 /\ oh' = huf'
  | None => True
  end ->
  (forall x, decode_seq_header (st_seq ts) (skipn (Z.to_nat r1) s) = Some x -> Some (nb, os', used) = Some x) ->
  decode_block ts hist out s bsm wsize = Some (ts2, cnt) ->
  seqs_model os' (skipn (Z.to_nat used) (skipn (Z.to_nat r1) s)) nb (st_rep ts) hist out lits wsize =
    Some (cnt, st_rep ts2) /\
  Zlength cnt <= bsm /\ ts2 = {| st_huf := oh'; st_seq := os'; st_rep := st_rep ts2 |}.
Proof.
  intros Hdl Hh Hb. unfold decode_block in Hb.
  destruct (Zlength s >? bsm); [discriminate |].
  destruct (decode_literals (st_huf ts) s bsm) as [[[lits0 u] hf]|]; [|discriminate].
  destruct Hdl as (-> & -> & ->).
  destruct (decode_seq_header (st_seq ts) (skipn (Z.to_nat u) s)) as [x|] eqn:Ex; [| discriminate].
  specialize (Hh _ eq_refl). injection Hh as Hx. subst x. cbv beta iota in Hb.
  unfold seqs_model.
  match type of Hb with context [match ?X with Some _ => _ | None => None end] =>
    destruct X as [seqs|] end; [|discriminate].
  destruct (exec_seqs wsize (st_rep ts) hist lits0 out seqs) as [[[out' lits'] rep']|]; [|discriminate].
  destruct (Zlength (skipn (length out) (out' ++ lits')) >? bsm) eqn:Eb; [discriminate |].
  inversion Hb; subst. simpl. rewrite Z.gtb_ltb in Eb. apply Z.ltb_ge in Eb. auto.
Qed.

Lemma tp_db_nbpos ts hist out s bsm wsize r1 lits oh' nb os' used ts2 cnt :
  match decode_literals (st_huf ts) s bsm with
  | Some (lits0, u, huf') => r1 = u /\ lits = lits0 /\ oh' = huf'
  | None => True
  end ->
  (forall x, decode_seq_header (st_seq ts) (skipn (Z.to_nat r1) s) = Some x -> Some (nb, os', used) = Some x) ->
  decode_block ts hist out s bsm wsize = Some (ts2, cnt) -> 0 < nb -> seqs_ok os' ->
  0 < Zlength cnt.
Proof.
  intros Hdl Hh Hb Hnb Hok. unfold decode_block in Hb.
  destruct (Zlength s >? bsm); [discriminate |].
  destruct (decode_literals (st_huf ts) s bsm) as [[[lits0 u] hf]|]; [|discriminate].
  destruct Hdl as (-> & -> & ->).
  destruct (decode_seq_header (st_seq ts) (skipn (Z.to_nat u) s)) as [x|] eqn:Ex; [| discriminate].
  specialize (Hh _ eq_refl). injection Hh as Hx. subst x. cbv beta iota in Hb.
  rewrite (proj2 (Z.eqb_neq nb 0)) in Hb by lia.
  destruct os' as [[[tLL tOF] tML]|]; [|discriminate].
  destruct (decode_seq_stream tLL tOF tML _ nb) as [seqs|] eqn:Es; [|discriminate].
  destruct (exec_seqs wsize (st_rep ts) hist lits0 out seqs) as [[[out' lits'] rep']|] eqn:Ee; [|discriminate].
  destruct (Zlength (skipn (length out) (out' ++ lits')) >? bsm); [discriminate |].
  inversion Hb; subst.
  pose proof (top_exec_pos _ _ _ _ _ _ _ _ _ _ _ _ _ _ (proj2 (proj2 Hok)) Hnb Es Ee).
  rewrite tp_content_len by (eapply exec_seqs_app; eauto).
  pose proof (Zlength_nonneg lits0). lia.
Qed.

Lemma tp_fe (nb: Z) (os os': option (fse_table * fse_table * fse_table)) :
  (nb = 0 -> os' = os) -> (nb <> 0 -> os' <> None) ->
  (if nb =? 0 then match os with Some _ => 1 | None => 0 end else 1) = match os' with Some _ => 1 | None => 0 end.
Proof.
  intros H0 H1. destruct (Z.eqb_spec nb 0) as [E|E].
  - rewrite (H0 E). reflexivity.
  - destruct os' as [x|]; [reflexivity | exfalso; apply (H1 E); reflexivity].
Qed.

(* ---------- the model's output is bytes when its inputs are ---------- *)

Lemma tp_byte_at_ok (l: list Z) (i: Z) : bytes_ok l -> is_byte (byte_at l i).
Proof.
  unfold byte_at, bytes_ok. intros H. destruct (lt_dec (Z.to_nat i) (length l)) as [Hi | Hi].
  - eapply Forall_forall; [exact H | apply nth_In; exact Hi].
  - rewrite nth_overflow by lia. unfold is_byte. lia.
Qed.

Lemma tp_lz_bytes (hist out: list Z) (off: Z) (ml: nat) :
  bytes_ok hist -> bytes_ok out -> bytes_ok (lz_copy hist out off ml).
Proof.
  revert out. induction ml as [|m IH]; intros out Hh Ho; simpl; [exact Ho |].
  apply IH; [exact Hh |]. unfold bytes_ok in *. apply Forall_app. split; [exact Ho |].
  constructor; [| constructor]. apply tp_byte_at_ok. unfold bytes_ok. apply Forall_app; auto.
Qed.

Lemma tp_exec_bytes (wsize: Z) (rep: Z * Z * Z) (hist lits out: list Z) (seqs: list sequence)
    (out' lits': list Z) (rep': Z * Z * Z) :
  bytes_ok hist -> bytes_ok lits -> bytes_ok out ->
  exec_seqs wsize rep hist lits out seqs = Some (out', lits', rep') -> bytes_ok out' /\ bytes_ok lits'.
Proof.
  revert rep lits out. induction seqs as [|sq rest IH]; intros rep lits out Hh Hl Ho H.
  - simpl in H. inversion H; subst. auto.
  - simpl in H.
    destruct (sq_ll sq >? Zlength lits); [discriminate |].
    destruct (resolve_offset rep (sq_ll sq) (sq_ov sq)) as [[offset rep2]|]; [|discriminate].
    destruct (offset >? Zlength hist + Zlength (out ++ firstn (Z.to_nat (sq_ll sq)) lits)); [discriminate |].
    destruct (offset >? wsize + Zlength hist); [discriminate |].
    eapply IH; [exact Hh | | | exact H].
    + unfold bytes_ok in *. apply Forall_skipn. exact Hl.
    + apply tp_lz_bytes; [exact Hh |]. unfold bytes_ok in *. apply Forall_app. split; [exact Ho |].
      apply Forall_firstn. exact Hl.
Qed.

Lemma tp_db_bytes ts hist out s bsm wsize ts2 cnt :
  decode_block ts hist out s bsm wsize = Some (ts2, cnt) ->
  (forall lits0 u hf, decode_literals (st_huf ts) s bsm = Some (lits0, u, hf) -> bytes_ok lits0) ->
  bytes_ok hist -> bytes_ok out -> bytes_ok cnt.
Proof.
  intros Hb Hl Hh Ho. unfold decode_block in Hb.
  destruct (Zlength s >? bsm); [discriminate |].
  destruct (decode_literals (st_huf ts) s bsm) as [[[lits0 u] hf]|] eqn:El; [|discriminate].
  specialize (Hl _ _ _ eq_refl).
  destruct (decode_seq_header _ _) as [[[nb tabs] hu]|]; [|discriminate].
  match type of Hb with context [match ?X with Some _ => _ | None => None end] =>
    destruct X as [seqs|] end; [|discriminate].
  destruct (exec_seqs wsize (st_rep ts) hist lits0 out seqs) as [[[out' lits'] rep']|] eqn:E; [|discriminate].
  destruct (Zlength (skipn (length out) (out' ++ lits')) >? bsm); [discriminate |].
  inversion Hb; subst cnt.
  destruct (tp_exec_bytes _ _ _ _ _ _ _ _ _ Hh Hl Ho E) as [B1 B2].
  unfold bytes_ok in *. apply Forall_skipn. apply Forall_app; auto.
Qed.

(* the block's outcome from the sequences section's (the model part) *)
Lemma tp_block_ok ts hist out s bsm wsize streaming (oc oc1 oc': list val) d cap r1 lits oh' nb os' used r3 rep' :
  Zlength oc = Zlength oc1 ->
  (streaming = 1 -> unchanged_outside oc oc1 d (d + Z.min cap bsm)) ->
  match decode_literals (st_huf ts) s bsm with
  | Some (lits0, u, huf') => r1 = u /\ lits = lits0 /\ oh' = huf'
  | None => True
  end ->
  (forall x, decode_seq_header (st_seq ts) (skipn (Z.to_nat r1) s) = Some x -> Some (nb, os', used) = Some x) ->
  (is_error_code r3 = false ->
     unchanged_outside oc1 oc' d (d + Z.min cap (r3 + WILDCOPY_OVERLENGTH))) ->
  match seqs_model os' (skipn (Z.to_nat used) (skipn (Z.to_nat r1) s)) nb (st_rep ts) hist out lits wsize with
  | Some (cnt, rep2) =>
      Zlength cnt <= bsm ->
      (is_error_code r3 = false /\ r3 = Zlength cnt /\ sublist d (d + r3) oc' = zbytes cnt /\ rep' = rep2) \/
      (is_error_code r3 = true /\ cap < Zlength cnt)
  | None => True
  end ->
  (is_error_code r3 = true -> dec_err r3) ->
  (forall ts2 cnt, decode_block ts hist out s bsm wsize = Some (ts2, cnt) -> is_error_code r3 = false ->
     r3 = Zlength cnt -> bytes_ok cnt) ->
  block_ok ts hist out s bsm wsize streaming oc oc' d cap r3
    (if is_error_code r3 then None else Some {| st_huf := oh'; st_seq := os'; st_rep := rep' |}).
Proof.
  intros L Us Hdl Hh Us2 Hm Hde Hbyt. unfold block_ok.
  destruct (decode_block ts hist out s bsm wsize) as [[ts2 cnt]|] eqn:Edb; [|exact I].
  destruct (tp_db_some _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hdl Hh Edb) as (Hsm & Hcb & Ets2).
  rewrite Hsm in Hm. specialize (Hm Hcb).
  destruct Hm as [(Er & Er3 & Eb & Erep) | (Er & Ec)].
  - left. rewrite Er. split; [reflexivity |]. split; [exact Er3 |]. split; [exact Eb |].
    split; [exact (Hbyt _ _ eq_refl Er Er3) |]. split.
    + rewrite Ets2, Erep. reflexivity.
    + intros Hs. specialize (Us Hs). specialize (Us2 Er).
      apply (tp_unch_trans oc oc1 oc' d (d + Z.min cap (bsm + WILDCOPY_OVERLENGTH)) d
               (d + Z.min cap (r3 + WILDCOPY_OVERLENGTH))); auto; try lia.
      apply (tp_unch_mono _ _ d (d + Z.min cap bsm)); auto; unfold WILDCOPY_OVERLENGTH; lia.
  - right. split; auto.
Qed.

(* ===================== the tables after an error ===================== *)

Lemma tp_mb_join (sh: share) (n m: Z) (q: val) :
  0 <= n -> 0 <= m ->
  memory_block sh n q * memory_block sh m (offset_val n q) |-- memory_block sh (n + m) q.
Proof.
  intros Hn Hm. destruct q as [| | | | | b i]; try (unfold memory_block at 1; rewrite FF_sepcon; apply FF_left).
  pose proof (Ptrofs.unsigned_range i) as Ri.
  unfold memory_block at 1. Intros. simpl offset_val.
  assert (E: Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr n)) = Ptrofs.unsigned i + n).
  { rewrite Ptrofs.add_unsigned, (Ptrofs.unsigned_repr n) by rep_lia. apply Ptrofs.unsigned_repr. rep_lia. }
  unfold memory_block at 1. rewrite E. Intros.
  replace (Vptr b i) with (Vptr b (Ptrofs.repr (Ptrofs.unsigned i))) by (rewrite Ptrofs.repr_unsigned; auto).
  rewrite (memory_block_split sh b (Ptrofs.unsigned i) n m) by lia.
  unfold memory_block at 1 2. rewrite !Ptrofs.unsigned_repr by rep_lia. entailer!.
Qed.

Lemma tp_mb_join_at sh p a n m b c : 0 <= n -> 0 <= m -> b = a + n -> c = n + m ->
  memory_block sh n (offset_val a p) * memory_block sh m (offset_val b p) |-- memory_block sh c (offset_val a p).
Proof. intros; subst. rewrite <- offset_offset_val. apply tp_mb_join; auto. Qed.

Lemma tp_hufhdr_mb (sh: share) (q: val) :
  hufhdr_at sh q |-- memory_block sh (4 + HUF_CELLBYTES) q.
Proof.
  unfold hufhdr_at. Intros ty lg res.
  sep_apply (data_at_memory_block sh t_dtdesc). simpl sizeof.
  sep_apply (tp_mb_join sh 4 HUF_CELLBYTES q); try (unfold HUF_CELLBYTES; lia); cancel.
Qed.

Lemma tp_hufdt_mb (sh: share) (ht: huf_table) (q: val) :
  hufdt_at sh ht q |-- memory_block sh (4 + HUF_CELLBYTES) q.
Proof.
  unfold hufdt_at, hufdt_x_at. Intros x2 L res.
  match goal with H: huf_ok _ |- _ => destruct H as [Hl _] end.
  unfold HUF_TABLELOG_MAX in *.
  assert (Hpw: 0 < 2 ^ L <= 4096).
  { split; [apply Z.pow_pos_nonneg; lia |]. change 4096 with (2 ^ 12). apply Z.pow_le_mono_r; lia. }
  sep_apply (data_at_memory_block sh t_dtdesc). simpl sizeof.
  destruct x2.
  - Intros c2. sep_apply data_at_memory_block. simpl sizeof. rewrite Z.max_r by lia.
    rewrite <- (offset_offset_val q 4 (4 * 2 ^ L)).
    sep_apply (tp_mb_join sh (4 * 2 ^ L) (HUF_CELLBYTES - 4 * 2 ^ L) (offset_val 4 q));
      try (unfold HUF_CELLBYTES; lia).
    replace (4 * 2 ^ L + (HUF_CELLBYTES - 4 * 2 ^ L)) with HUF_CELLBYTES by lia.
    sep_apply (tp_mb_join sh 4 HUF_CELLBYTES q); try (unfold HUF_CELLBYTES; lia); cancel.
  - sep_apply data_at_memory_block. simpl sizeof. rewrite Z.max_r by lia.
    rewrite <- (offset_offset_val q 4 (2 * 2 ^ L)).
    sep_apply (tp_mb_join sh (2 * 2 ^ L) (HUF_CELLBYTES - 2 * 2 ^ L) (offset_val 4 q));
      try (unfold HUF_CELLBYTES; lia).
    replace (2 * 2 ^ L + (HUF_CELLBYTES - 2 * 2 ^ L)) with HUF_CELLBYTES by lia.
    sep_apply (tp_mb_join sh 4 HUF_CELLBYTES q); try (unfold HUF_CELLBYTES; lia); cancel.
Qed.

Lemma tp_huf_junk (gv: globals) (p: val) (ox: option ddx) (oh: option huf_table) (x2: bool) :
  tabs_huf gv p ox oh x2 |-- huf_junk p.
Proof.
  unfold tabs_huf, huf_junk. Intros hp.
  destruct oh as [ht |].
  - Intros w. destruct w; Intros.
    + assert (Hx: hufdt_x_at x2 Ews ht (ctx_huf p) |-- hufdt_at Ews ht (ctx_huf p))
        by (unfold hufdt_at; Exists x2; apply derives_refl).
      sep_apply Hx. sep_apply tp_hufdt_mb. cancel.
    + sep_apply tp_hufhdr_mb. cancel.
  - Intros. sep_apply tp_hufhdr_mb. cancel.
Qed.

Lemma tp_sizeof_arr t n : 0 <= n -> sizeof (tarray t n) = (sizeof t * n)%Z.
Proof. intros. unfold tarray. rewrite sizeof_Tarray. f_equal. lia. Qed.

Lemma tp_seqspace_mb sh k ot p : seqspace_at sh k ot p |-- memory_block sh (8 * sk_size k)%Z p.
Proof.
  assert (Hs: 2 ^ sk_maxlog k <= 512 /\ sk_size k = 1 + 2 ^ sk_maxlog k)
    by (destruct k; split; reflexivity || (vm_compute; discriminate)).
  destruct ot as [t|]; simpl.
  - unfold seqtab_at, seqtab_at_fm. Intros fm. destruct H as [[Hlog0 Hlog] _].
    assert (Hk: 2 ^ ft_log t <= 2 ^ sk_maxlog k) by (apply Z.pow_le_mono_r; lia).
    assert (0 < 2 ^ ft_log t) by (apply Z.pow_pos_nonneg; lia).
    sep_apply (data_at_memory_block sh t_seqhdr).
    sep_apply (data_at_memory_block sh (tarray t_seqSymbol (2 ^ ft_log t))).
    sep_apply (data_at__memory_block_cancel sh (tarray t_seqSymbol (sk_size k - 1 - 2 ^ ft_log t))).
    rewrite !tp_sizeof_arr by lia.
    change (sizeof t_seqhdr) with 8. change (sizeof t_seqSymbol) with 8.
    sep_apply (tp_mb_join sh 8 (8 * 2 ^ ft_log t) p); try lia.
    replace (8 * (1 + 2 ^ ft_log t))%Z with (8 + 8 * 2 ^ ft_log t)%Z by lia.
    sep_apply (tp_mb_join sh (8 + 8 * 2 ^ ft_log t) (8 * (sk_size k - 1 - 2 ^ ft_log t)) p); try lia.
    replace (8 + 8 * 2 ^ ft_log t + 8 * (sk_size k - 1 - 2 ^ ft_log t))%Z with (8 * sk_size k)%Z by lia.
    cancel.
  - sep_apply (data_at__memory_block_cancel sh (tarray t_seqSymbol (sk_size k))).
    rewrite tp_sizeof_arr by lia. change (sizeof t_seqSymbol) with 8. cancel.
Qed.

(* the entropy struct of a context, field by field *)
Ltac tp_eval_fields :=
  repeat match goal with
  | |- context [nested_field_offset ?t ?g] =>
      let x := eval vm_compute in (nested_field_offset t g) in change (nested_field_offset t g) with x
  | |- context [sizeof (nested_field_type ?t ?g)] =>
      let x := eval vm_compute in (sizeof (nested_field_type t g)) in change (sizeof (nested_field_type t g)) with x
  end.

Lemma tp_ent_join sh p :
  field_at_ sh t_dctx (DOT _entropy DOT _LLTable) p * field_at_ sh t_dctx (DOT _entropy DOT _OFTable) p *
  field_at_ sh t_dctx (DOT _entropy DOT _MLTable) p * field_at_ sh t_dctx (DOT _entropy DOT _hufTable) p *
  field_at_ sh t_dctx (DOT _entropy DOT _rep) p * field_at_ sh t_dctx (DOT _entropy DOT _workspace) p
  |-- field_at_ sh t_dctx (DOT _entropy) p.
Proof.
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
  tp_eval_fields.
  sep_apply (tp_mb_join_at sh p 32 4104 2056 4136 6160); try lia.
  sep_apply (tp_mb_join_at sh p 32 6160 4104 6192 10264); try lia.
  sep_apply (tp_mb_join_at sh p 32 10264 16388 10296 26652); try lia.
  sep_apply (tp_mb_join_at sh p 32 26652 12 26684 26664); try lia.
  sep_apply (tp_mb_join_at sh p 32 26664 628 26696 27292); try lia.
  cancel.
Qed.

Lemma tp_seqspace_ctx k ot p :
  seqspace_at Ews k ot (ctx_seq k p) |-- field_at_ Ews t_dctx (DOT _entropy DOT sk_tfield k) p.
Proof.
  sep_apply tp_seqspace_mb. rewrite field_at__memory_block. unfold ctx_seq.
  apply derives_refl'. f_equal. destruct k; reflexivity.
Qed.

Lemma tp_huf_ctx p :
  memory_block Ews (4 + HUF_CELLBYTES) (ctx_huf p) |-- field_at_ Ews t_dctx (DOT _entropy DOT _hufTable) p.
Proof. rewrite field_at__memory_block. unfold ctx_huf. apply derives_refl'. f_equal. Qed.

(* the sequence part, whatever it holds *)
Definition seq_fields (p: val) : mpred :=
  field_at_ Ews t_dctx (DOT _fseEntropy) p *
  field_at_ Ews t_dctx (DOT _LLTptr) p * field_at_ Ews t_dctx (DOT _OFTptr) p *
  field_at_ Ews t_dctx (DOT _MLTptr) p *
  field_at_ Ews t_dctx (DOT _entropy DOT _LLTable) p *
  field_at_ Ews t_dctx (DOT _entropy DOT _OFTable) p *
  field_at_ Ews t_dctx (DOT _entropy DOT _MLTable) p.

Lemma tp_seq_where_fields gv p ox k t :
  seq_where gv p ox k t |-- (EX tp: val, seq_ptr_at p k tp) * field_at_ Ews t_dctx (DOT _entropy DOT sk_tfield k) p.
Proof.
  unfold seq_where. Intros tp w. Exists tp.
  destruct w; Intros; sep_apply tp_seqspace_ctx; cancel.
Qed.

Lemma tp_tabs_seq_fields gv p ox os fe : tabs_seq gv p ox os fe |-- seq_fields p.
Proof.
  unfold tabs_seq, seq_fields. destruct os as [[[a b] c]|].
  - sep_apply (tp_seq_where_fields gv p ox KLL a). sep_apply (tp_seq_where_fields gv p ox KOF b).
    sep_apply (tp_seq_where_fields gv p ox KML c).
    Intros t1 t2 t3. simpl seq_ptr_at. simpl sk_tfield. cancel.
  - sep_apply (tp_seqspace_ctx KLL). sep_apply (tp_seqspace_ctx KOF). sep_apply (tp_seqspace_ctx KML).
    simpl sk_tfield. cancel.
Qed.

Lemma tp_seq_junk_fields p : seq_junk p |-- seq_fields p.
Proof.
  unfold seq_junk, seq_fields.
  sep_apply (tp_seqspace_ctx KLL). sep_apply (tp_seqspace_ctx KOF). sep_apply (tp_seqspace_ctx KML).
  simpl sk_tfield. cancel.
Qed.

Lemma tp_uninit (p: val) :
  huf_junk p * seq_fields p * field_at_ Ews t_dctx (DOT _entropy DOT _rep) p *
  field_at_ Ews t_dctx (DOT _entropy DOT _workspace) p * field_at_ Ews t_dctx (DOT _workspace) p * lit_scratch p
  |-- EX lxb: list Z, tables_uninit p lxb.
Proof.
  unfold huf_junk, seq_fields, lit_scratch.
  sep_apply lit_extra_bytes_at. Intros lxb. Exists lxb. unfold tables_uninit.
  sep_apply tp_huf_ctx.
  sep_apply (tp_ent_join Ews p). cancel.
Qed.

(* litExtraBuffer's exact bytes forgotten *)
Lemma tp_scratch_x_any (p: val) (lxb: list Z) : lit_scratch_x p lxb |-- lit_scratch p.
Proof. unfold lit_scratch_x, lit_scratch. sep_apply lit_extra_at_bytes. cancel. Qed.

(* ===================== the tables in use ===================== *)

Lemma tp_vf_byte_cells n l : value_fits (tarray tuchar n) l -> Forall (fun v => v <> Vundef) l -> byte_cells l.
Proof.
  intros Hv Hd. rewrite value_fits_eq in Hv. simpl in Hv. destruct Hv as [_ Hv].
  unfold byte_cells. rewrite Forall_forall in *. intros v Hin.
  specialize (Hv v Hin). specialize (Hd v Hin). rewrite value_fits_eq in Hv. simpl in Hv.
  unfold tc_val' in Hv. specialize (Hv Hd).
  destruct v; simpl in Hv; try contradiction.
  exists (Int.unsigned i). split; [rep_lia | rewrite Int.repr_unsigned; auto].
Qed.

Lemma tp_zbytes_def l : Forall (fun v => v <> Vundef) (zbytes l).
Proof. rewrite Forall_forall. intros v Hin. apply in_map_iff in Hin. destruct Hin as [? [<- _]]. discriminate. Qed.

Lemma tp_litfields_scratch p ob ib l lits lxb : litfields p ob ib l lits lxb |-- lit_scratch p.
Proof.
  unfold litfields, lit_scratch.
  destruct l; Intros.
  all: sep_apply (field_at_field_at_ Ews t_dctx (DOT _litPtr)); sep_apply (field_at_field_at_ Ews t_dctx (DOT _litSize));
    sep_apply (field_at_field_at_ Ews t_dctx (DOT _litBufferLocation));
    sep_apply (field_at_field_at_ Ews t_dctx (DOT _litBufferEnd)).
  2,3,4: sep_apply (field_at_field_at_ Ews t_dctx (DOT _litBuffer)).
  all: sep_apply lit_extra_at_bytes; cancel.
Qed.

(* the tables the context uses are well formed (wherever they are) *)
Lemma tp_seq_where_ok gv p ox k t :
  seq_where gv p ox k t * dent_of dent_def gv ox |-- !! fse_ok k t.
Proof.
  unfold seq_where. Intros tp w. destruct w; Intros.
  - simpl seqspace_at. unfold seqtab_at, seqtab_at_fm. Intros fm. apply prop_right; tauto.
  - match goal with H: ox_seq k ox = Some t |- _ => rename H into Hs end.
    unfold ox_seq, ox_ent in Hs. destruct ox as [x|]; [|discriminate].
    simpl dent_of. destruct (ddx_ent x) as [st|]; [|discriminate].
    unfold dent_def. destruct (st_huf st) as [ht|], (st_seq st) as [[[a b] c]|] eqn:Eq; try discriminate;
      try (rewrite FF_sepcon || rewrite sepcon_FF); try apply FF_left.
    Intros. apply prop_right.
    match goal with H: dstate_ok st |- _ => destruct H as [_ [Hq _]] end.
    rewrite Eq in Hq. simpl in Hq, Hs. inversion Hs; subst. destruct k; tauto.
  - match goal with H: t = sk_predef k |- _ => rewrite H end.
    apply prop_right. destruct predef_ok as (A & B & C). destruct k; assumption.
Qed.

Lemma tp_seqs_ok gv p ox os fe :
  tabs_seq gv p ox os fe * dent_of dent_def gv ox |-- !! seqs_ok os.
Proof.
  unfold tabs_seq. destruct os as [[[a b] c]|]; [|apply prop_right; exact I].
  assert_PROP (fse_ok KLL a) by (sep_apply (tp_seq_where_ok gv p ox KLL a); entailer!).
  assert_PROP (fse_ok KOF b) by (sep_apply (tp_seq_where_ok gv p ox KOF b); entailer!).
  assert_PROP (fse_ok KML c) by (sep_apply (tp_seq_where_ok gv p ox KML c); entailer!).
  apply prop_right. simpl. tauto.
Qed.

(* the offset table, borrowed for ZSTD_getOffsetInfo: in the context, a DDict, or the globals *)
Lemma tp_of_access (GL: GLOBALS_obligation) gv p ox b :
  seq_where gv p ox KOF b * dent_of dent_def gv ox * zstd_globals gv |--
  EX tp: val, EX sh: share, EX fm: Z,
    !! readable_share sh &&
    (field_at Ews t_dctx (DOT _OFTptr) tp p * seqtab_at_fm sh KOF b fm tp *
     (field_at Ews t_dctx (DOT _OFTptr) tp p * seqtab_at_fm sh KOF b fm tp -*
      seq_where gv p ox KOF b * dent_of dent_def gv ox * zstd_globals gv)).
Proof.
  unfold seq_where at 1. Intros tp w. destruct w; Intros.
  - (* in the context *)
    simpl seqspace_at. unfold seqtab_at at 1. Intros fm.
    Exists tp Ews fm. rewrite prop_true_andp by auto. simpl seq_ptr_at.
    match goal with H: tp = _ |- _ => rewrite H end. cancel.
    rewrite <- wand_sepcon_adjoint.
    unfold seq_where. Exists (ctx_seq KOF p) TCtx. simpl seq_ptr_at. simpl seqspace_at.
    unfold seqtab_at. Exists fm. entailer!.
  - (* in the DDict *)
    match goal with H: ox_seq KOF ox = Some b |- _ => rename H into Hs end.
    match goal with H: tp = _ |- _ => rename H into Htp end.
    unfold ox_seq, ox_ent in Hs. destruct ox as [x|]; [|discriminate].
    simpl dent_of. simpl ox_q in Htp.
    destruct (ddx_ent x) as [st|] eqn:Est; [|discriminate].
    unfold dent_def at 1. destruct (st_huf st) as [ht|] eqn:Eh, (st_seq st) as [[[a b'] c]|] eqn:Eq;
      try discriminate; try (rewrite FF_sepcon || rewrite sepcon_FF); try (rewrite FF_sepcon || rewrite sepcon_FF);
      try apply FF_left.
    simpl in Hs. inversion Hs; subst b'. Intros.
    change (seqspace_at Ews KOF (Some b) (dd_seq KOF (dx_q x))) with
      (seqtab_at Ews KOF b (dd_seq KOF (dx_q x)) *
       data_at_ Ews (tarray t_seqSymbol (sk_size KOF - 1 - 2 ^ ft_log b)%Z)
         (offset_val (8 * (1 + 2 ^ ft_log b))%Z (dd_seq KOF (dx_q x)))).
    unfold seqtab_at. Intros fm.
    Exists tp Ews fm. rewrite prop_true_andp by auto. simpl seq_ptr_at. subst tp. cancel.
    rewrite <- wand_sepcon_adjoint.
    unfold seq_where. Exists (dd_seq KOF (dx_q x)) TDict. simpl seq_ptr_at.
    unfold dent_def. rewrite Eh, Eq.
    change (seqspace_at Ews KOF (Some b) (dd_seq KOF (dx_q x))) with
      (seqtab_at Ews KOF b (dd_seq KOF (dx_q x)) *
       data_at_ Ews (tarray t_seqSymbol (sk_size KOF - 1 - 2 ^ ft_log b)%Z)
         (offset_val (8 * (1 + 2 ^ ft_log b))%Z (dd_seq KOF (dx_q x)))).
    unfold seqtab_at. Exists fm.
    assert (Hox: ox_seq KOF (Some x) = Some b) by (unfold ox_seq, ox_ent; rewrite Est, Eq; reflexivity).
    simpl ox_q. entailer!.
  - (* the globals *)
    match goal with H: b = sk_predef KOF |- _ => rename H into Hb end.
    match goal with H: tp = _ |- _ => rename H into Htp end.
    destruct (GL gv) as [R HR]. rewrite HR. unfold predef_tabs.
    Exists tp Ers predef_fm. rewrite prop_true_andp by auto. simpl seq_ptr_at.
    simpl in Hb, Htp. subst b tp. cancel.
    rewrite <- wand_sepcon_adjoint.
    unfold seq_where. Exists (gv _OF_defaultDTable) TGlob. simpl seq_ptr_at. entailer!.
Qed.

(* ===================== borrowing fields ===================== *)

Lemma tp_scratch_eq p lxb :
  tabs_scratch p * lit_extra_at p lxb =
  field_at_ Ews t_dctx (DOT _entropy DOT _workspace) p * field_at_ Ews t_dctx (DOT _workspace) p *
  lit_scratch_x p lxb.
Proof. unfold tabs_scratch, lit_scratch_x. apply pred_ext; cancel. Qed.

Lemma tp_scratch_to p lxb :
  tabs_scratch p * lit_extra_at p lxb |--
  field_at_ Ews t_dctx (DOT _entropy DOT _workspace) p * field_at_ Ews t_dctx (DOT _workspace) p *
  lit_scratch_x p lxb.
Proof. rewrite tp_scratch_eq. apply derives_refl. Qed.

Lemma tp_set_cold_same fs : fs_set_cold fs (fs_ddictIsCold fs) = fs.
Proof. destruct fs; reflexivity. Qed.

Lemma tp_ff_vs p fs :
  frame_fields p fs |-- field_at Ews t_dctx (DOT _virtualStart) (fs_virtualStart fs) p *
    (field_at Ews t_dctx (DOT _virtualStart) (fs_virtualStart fs) p -* frame_fields p fs).
Proof.
  unfold frame_fields at 1. cancel. rewrite <- wand_sepcon_adjoint. unfold frame_fields. cancel.
Qed.

Lemma tp_ff_cold p fs v :
  frame_fields p fs |-- field_at Ews t_dctx (DOT _ddictIsCold) (fs_ddictIsCold fs) p *
    (field_at Ews t_dctx (DOT _ddictIsCold) v p -* frame_fields p (fs_set_cold fs v)).
Proof.
  unfold frame_fields at 1. cancel. rewrite <- wand_sepcon_adjoint. unfold frame_fields. simpl. cancel.
Qed.

Lemma tp_lf_loc p ob ib l lits lxb :
  litfields p ob ib l lits lxb |-- field_at Ews t_dctx (DOT _litBufferLocation) (Vint (Int.repr (loc_code l))) p *
    (field_at Ews t_dctx (DOT _litBufferLocation) (Vint (Int.repr (loc_code l))) p -* litfields p ob ib l lits lxb).
Proof.
  unfold litfields at 1. destruct l; Intros; cancel; rewrite <- wand_sepcon_adjoint; unfold litfields;
    entailer!.
Qed.

(* the output array's dst is comparable (with NULL) *)
Lemma tp_dst_wvp W (o: outarr) (c: list val) :
  outarr_ok o -> (oa_cap o = 0 -> (pws_pred W |-- weak_valid_pointer (offset_val (oa_d o) (oa_base o)))) ->
  pws_pred W * data_at (oa_sh o) (tarray tuchar (oa_N o)) c (oa_base o) |--
  weak_valid_pointer (offset_val (oa_d o) (oa_base o)).
Proof.
  intros (Hw & HN & _ & Hd & Hc & Hdc) Hz.
  destruct (Z.eq_dec (oa_cap o) 0) as [E|E].
  - sep_apply (Hz E). apply sepcon_weak_valid_pointer1. apply derives_refl.
  - apply sepcon_weak_valid_pointer2.
    sep_apply data_at_memory_block. simpl sizeof. rewrite Z.max_r by lia. rewrite Z.mul_1_l.
    apply memory_block_weak_valid_pointer; try lia.
    apply readable_nonidentity; auto.
Qed.

Lemma tp_parts_uninit gv p ox oh x2 os fe rep lxb :
  tabs_huf gv p ox oh x2 * tabs_seq gv p ox os fe * field_at Ews t_dctx (DOT _entropy DOT _rep) (rep_vals rep) p *
  tabs_scratch p * lit_extra_at p lxb |-- EX lxb': list Z, tables_uninit p lxb'.
Proof.
  sep_apply tp_scratch_to. sep_apply tp_scratch_x_any.
  sep_apply tp_huf_junk. sep_apply tp_tabs_seq_fields.
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _entropy DOT _rep)).
  sep_apply tp_uninit. cancel.
Qed.

Lemma tp_db_big ts hist out s bsm wsize :
  bsm < Zlength s -> decode_block ts hist out s bsm wsize = None.
Proof. intros H. unfold decode_block. rewrite (proj2 (Z.gtb_lt _ _) H). reflexivity. Qed.

Section TcNull.
Local Transparent denote_tc_test_eq.
Lemma tp_tc_null W (o: outarr) (c: list val) :
  outarr_ok o -> (oa_cap o = 0 -> (pws_pred W |-- weak_valid_pointer (offset_val (oa_d o) (oa_base o)))) ->
  pws_pred W * data_at (oa_sh o) (tarray tuchar (oa_N o)) c (oa_base o) * TT |--
  denote_tc_test_eq (offset_val (oa_d o) (oa_base o)) (Vlong (Int64.repr 0)).
Proof.
  intros Ho Hz.
  assert_PROP (isptr (oa_base o)) as Hb by entailer!.
  destruct (oa_base o) eqn:Eb; try contradiction. rewrite <- Eb.
  replace (offset_val (oa_d o) (oa_base o)) with (Vptr b (Ptrofs.add i (Ptrofs.repr (oa_d o)))) by (rewrite Eb; reflexivity).
  unfold denote_tc_test_eq. simpl. apply andp_right; [apply prop_right; reflexivity |].
  apply sepcon_weak_valid_pointer1.
  replace (Vptr b (Ptrofs.add i (Ptrofs.repr (oa_d o)))) with (offset_val (oa_d o) (oa_base o)) by (rewrite Eb; reflexivity).
  apply tp_dst_wvp; auto. rewrite Eb. exact Hz.
Qed.
End TcNull.

Lemma tp_tabs_fold gv p ox oh x2 os rep lxb :
  dstate_ok {| st_huf := oh; st_seq := os; st_rep := rep |} ->
  tabs_huf gv p ox oh x2 * tabs_seq gv p ox os (match os with Some _ => 1 | None => 0 end) *
  field_at Ews t_dctx (DOT _entropy DOT _rep) (rep_vals rep) p *
  field_at_ Ews t_dctx (DOT _entropy DOT _workspace) p * field_at_ Ews t_dctx (DOT _workspace) p * lit_scratch_x p lxb
  |-- tabs_def gv p ox (mk_tstate {| st_huf := oh; st_seq := os; st_rep := rep |} x2 lxb).
Proof.
  intros Hd. unfold tabs_def, tabs_scratch, lit_scratch_x. cbn [ts_d ts_x2 ts_lxb].
  simpl st_huf; simpl st_seq; simpl st_rep.
  rewrite prop_true_andp by exact Hd. cancel.
Qed.

(* ===================== tactics for zstd's macro loops (as BlkLIT) ===================== *)

Ltac tp_body :=
  solve [ forward; entailer!
        | match goal with |- semax _ ?Q _ _ => forward_if Q end;
          [ contradiction | forward; entailer! | forward; entailer! ]
        | match goal with |- semax _ ?Q _ _ => forward_if Q end;
          [ contradiction | forward; entailer! ] ].

Ltac tp_skiploop :=
  repeat match goal with |- semax _ _ (Ssequence (Ssequence _ _) _) _ => apply -> seq_assoc end;
  match goal with
  | |- semax _ ?P (Ssequence (Sloop _ Sbreak) _) _ =>
      forward_loop P break: P; [ entailer! | tp_body | ]
  | |- semax _ ?P (Sloop _ Sbreak) _ =>
      forward_loop P break: P; [ entailer! | tp_body | ]
  end.

Ltac tp_errpath := do 4 tp_skiploop; forward.

Ltac tp_check C :=
  repeat match goal with |- semax _ _ (Ssequence (Ssequence _ _) _) _ => apply -> seq_assoc end;
  match goal with |- semax _ (PROPx ?Ps (LOCALx ?Qs (SEPx ?Rs))) (Ssequence (Sloop _ Sbreak) _) _ =>
    forward_loop (PROPx Ps (LOCALx Qs (SEPx Rs)))
      break: (PROPx (C :: Ps) (LOCALx Qs (SEPx Rs))) end.

Lemma tp_err_true (e: Z) : 1 <= e <= 119 -> is_error_code (err_code e) = true.
Proof. intros H. unfold is_error_code, err_code. apply Z.ltb_lt. lia. Qed.

Lemma tp_err_val (e: Z) :
  1 <= e <= 119 -> Vlong (Int64.repr (- e)) = Vlong (Int64.repr (err_code e)) /\ 0 <= err_code e <= Int64.max_unsigned.
Proof.
  intros H. split; [| unfold err_code; rep_lia].
  f_equal. apply Int64.eqm_samerepr. exists (-1). unfold err_code. change Int64.modulus with (2 ^ 64). lia.
Qed.

Lemma tp_dec_err (e: Z) : 1 <= e <= 119 -> e <> 80 -> e <> 82 -> dec_err (err_code e).
Proof.
  intros H H80 H82. unfold dec_err, err_code, ZSTD_error_noForwardProgress_destFull,
    ZSTD_error_noForwardProgress_inputEmpty. split; [apply tp_err_true; lia | lia].
Qed.

Lemma tp_unch (oc: list val) (lo hi: Z) : unchanged_outside oc oc lo hi.
Proof. intros k _ _. reflexivity. Qed.

Lemma tp_cmpu_gt (a b: Z) :
  0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int64.cmpu Cgt (Int64.repr a) (Int64.repr b) = (b <? a).
Proof.
  intros Ha Hb. simpl. unfold Int64.ltu. rewrite !Int64.unsigned_repr by lia.
  destruct (zlt b a); symmetry; [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Qed.

Lemma tp_cmpu_lt (a b: Z) :
  0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int64.cmpu Clt (Int64.repr a) (Int64.repr b) = (a <? b).
Proof.
  intros Ha Hb. simpl. unfold Int64.ltu. rewrite !Int64.unsigned_repr by lia.
  destruct (zlt a b); symmetry; [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Qed.

Lemma tp_add_l (q: val) (b: Z) :
  isptr q -> force_val (sem_add_ptr_long tuchar q (Vlong (Int64.repr b))) = offset_val b q.
Proof.
  intros Hq. destruct q; try contradiction. simpl. f_equal.
  rewrite Ptrofs.mul_commut, Ptrofs.mul_one. unfold Ptrofs.of_int64. f_equal.
  apply Ptrofs.eqm_samerepr. rewrite Int64.unsigned_repr_eq. unfold Ptrofs.eqm. apply Zbits.eqmod_sym.
  change Ptrofs.modulus with Int64.modulus. apply Zbits.eqmod_mod. reflexivity.
Qed.

Lemma tp_sub64 (a b: Z) : Int64.sub (Int64.repr a) (Int64.repr b) = Int64.repr (a - b).
Proof.
  unfold Int64.sub. apply Int64.eqm_samerepr. apply Int64.eqm_sub; apply Int64.eqm_sym, Int64.eqm_unsigned_repr.
Qed.

Lemma tp_r64_zero (a: Z) : 0 <= a <= Int64.max_unsigned -> (Int64.repr a = Int64.zero <-> a = 0).
Proof.
  intros Ha. split; intros H.
  - apply (f_equal Int64.unsigned) in H. rewrite Int64.unsigned_repr in H by lia. exact H.
  - subst. reflexivity.
Qed.

(* the tables after an error, from their pieces in the body *)
Ltac tp_err_tabs gv p ox :=
  first [sep_apply tp_huf_junk | idtac];
  first [sep_apply tp_litfields_scratch | idtac];
  first [sep_apply tp_scratch_x_any | idtac];
  first [sep_apply (tp_tabs_seq_fields gv p ox) | sep_apply tp_seq_junk_fields];
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _entropy DOT _rep));
  sep_apply tp_uninit; cancel.

Lemma tp_lt_int (a b: Z) :
  Int.min_signed <= a <= Int.max_signed -> Int.min_signed <= b <= Int.max_signed ->
  bool2val (Int.lt (Int.repr a) (Int.repr b)) = Vint (Int.repr (if a <? b then 1 else 0)).
Proof.
  intros Ha Hb. unfold Int.lt. rewrite !Int.signed_repr by lia.
  destruct (zlt a b), (Z.ltb_spec a b); try lia; reflexivity.
Qed.

Ltac tp_int_false :=
  exfalso; match goal with H: Int.repr ?a = Int.zero |- _ =>
    apply (f_equal Int.unsigned) in H; rewrite Int.unsigned_repr in H by rep_lia; vm_compute in H; discriminate end.

(* ===================== the bodies ===================== *)

Lemma body_totalHistorySize : body_ok TOP3_G ZSTD_totalHistorySize_spec.
Proof.
  exists f_ZSTD_totalHistorySize; split; [reflexivity | split; [reflexivity |]].
  start_function.
  forward.
  all: destruct b; try contradiction; apply prop_right.
  - unfold sameblock; simpl. destruct (peq b b); [reflexivity | congruence].
  - unfold sem_sub_pp; simpl. rewrite if_true by auto. simpl.
    rewrite (Ptrofs.add_commut i0 (Ptrofs.repr i)), (Ptrofs.add_commut i0 (Ptrofs.repr j)), Ptrofs.sub_shifted.
    assert (E: Ptrofs.sub (Ptrofs.repr i) (Ptrofs.repr j) = Ptrofs.repr (i - j)).
    { unfold Ptrofs.sub. apply Ptrofs.eqm_samerepr.
      apply Ptrofs.eqm_sub; apply Ptrofs.eqm_sym, Ptrofs.eqm_unsigned_repr. }
    rewrite E. unfold Ptrofs.divs. rewrite (Ptrofs.signed_repr 1) by rep_lia.
    rewrite Z.quot_1_r, Ptrofs.repr_signed.
    unfold Vptrofs. simpl. f_equal. unfold Ptrofs.to_int64. rewrite Ptrofs.unsigned_repr_eq.
    apply Int64.eqm_samerepr. apply Int64.eqm_sym. unfold Int64.eqm. change Int64.modulus with Ptrofs.modulus.
    apply Zbits.eqmod_mod. reflexivity.
Qed.

Lemma sk_bits_OF_range (s: Z) : 0 <= sk_bits KOF s <= 31.
Proof.
  unfold sk_bits, OF_bits_tab.
  destruct (List.nth_in_or_default (Z.to_nat s) (map Z.of_nat (seq 0 32)) 0) as [Hin | ->]; [| lia].
  apply in_map_iff in Hin. destruct Hin as [n [<- Hn]]. apply in_seq in Hn. lia.
Qed.

Local Ltac offinfo_cell Hz e :=
  match goal with |- context [@Znth ?A ?d ?i ?l] =>
    replace (@Znth A d i l) with (seqcell KOF e) by (symmetry; exact Hz) end;
  change (let (x, _) := let (_, y) := seqcell KOF e in y in x) with (Vint (Int.repr (sk_bits KOF (fe_sym e)))).
Local Ltac offinfo_tc :=
  cbv beta iota delta [is_int]; rewrite Int.unsigned_repr by rep_lia; rep_lia.

Lemma body_getOffsetInfo : body_ok TOP3_G ZSTD_getOffsetInfo_spec.
Proof.
  exists f_ZSTD_getOffsetInfo; split; [reflexivity | split; [reflexivity |]].
  start_function.
  unfold seqtab_at_fm. Intros.
  forward. forward.
  forward_if (PROP () LOCAL (lvar _info t_offinfo v_info; temp _gp_info pi)
    SEP (EX ls: Z, EX mx: Z, data_at Tsh t_offinfo (Vint (Int.repr ls), Vint (Int.repr mx)) v_info;
         data_at_ shi t_offinfo pi;
         data_at sh t_seqhdr (Vint (Int.repr fm), Vint (Int.repr (ft_log t))) tp;
         data_at sh (tarray t_seqSymbol (2 ^ ft_log t)) (map (seqcell KOF) (ft_cells t)) (offset_val 8 tp))).
  - destruct H0 as [Hlog [Hlen Hcells]]. simpl in Hlog. unfold OffFSELog in Hlog.
    assert (Hpow: 1 <= 2 ^ ft_log t <= 256).
    { split; [assert (0 < 2 ^ ft_log t) by (apply Z.pow_pos_nonneg; lia); lia|]. change 256 with (2 ^ 8). apply Z.pow_le_mono_r; lia. }
    forward.
    assert_PROP (offset_val 4 (force_val (sem_add_ptr_int t_seqhdr Signed tp (Vint (Int.repr 0)))) =
                 field_address t_seqhdr (DOT _tableLog) tp).
    { entailer!. unfold field_address; rewrite if_true by auto with field_compatible.
      destruct tp; try contradiction; try (destruct H5; contradiction). simpl. reflexivity. }
    forward. forward. forward.
    { entailer!. change (Int.unsigned Int.iwordsize) with 32; lia. }
    assert (Hmax: Int.shl (Int.repr 1) (Int.repr (ft_log t)) = Int.repr (2 ^ ft_log t)).
    { rewrite Int.shl_mul_two_p, Int.mul_commut, Int.mul_one, Int.unsigned_repr by rep_lia.
      rewrite two_p_equiv; reflexivity. }
    rewrite Hmax.
    assert_PROP (force_val (sem_binary_operation' Oadd (tptr (Tstruct ___gp_ZSTD_seqSymbol noattr)) tint tp (Vint (Int.repr 1)))
                 = offset_val 8 tp) as Htab.
    { entailer!. }
    rewrite Htab.
    match goal with |- semax _ ?P _ _ => forward_loop P break: P end.
    { entailer!. }
    { forward. entailer!. }
    forward_for_simple_bound (2 ^ ft_log t) (EX u: Z,
      PROP () LOCAL (temp _max (Vint (Int.repr (2 ^ ft_log t))); temp _table (offset_val 8 tp);
                     temp _tableLog (Vint (Int.repr (ft_log t)));
                     lvar _info t_offinfo v_info; temp _gp_info pi)
      SEP (EX ls: Z, EX mx: Z, data_at Tsh t_offinfo (Vint (Int.repr ls), Vint (Int.repr mx)) v_info;
           data_at_ shi t_offinfo pi;
           data_at sh t_seqhdr (Vint (Int.repr fm), Vint (Int.repr (ft_log t))) tp;
           data_at sh (tarray t_seqSymbol (2 ^ ft_log t)) (map (seqcell KOF) (ft_cells t)) (offset_val 8 tp)))%assert.
    { Exists 0 0. entailer!. }
    { Intros ls mx.
      assert (Hz: exists e, Znth i (map (seqcell KOF) (ft_cells t)) = seqcell KOF e).
      { assert (Hin: In (Znth i (map (seqcell KOF) (ft_cells t))) (map (seqcell KOF) (ft_cells t)))
          by (apply Znth_In; rewrite Zlength_map; lia).
        apply in_map_iff in Hin. destruct Hin as [e [He _]]. eauto. }
      destruct Hz as [e Hz].
      pose proof (sk_bits_OF_range (fe_sym e)) as Hb.
      forward. forward.
      { entailer!. offinfo_cell Hz e. offinfo_tc. }
      offinfo_cell Hz e.
      forward_if (EX m: Z, PROP ()
        LOCAL (temp _t'1 (Vint (Int.repr m)); temp _u (Vint (Int.repr i));
               temp _max (Vint (Int.repr (2 ^ ft_log t))); temp _table (offset_val 8 tp);
               temp _tableLog (Vint (Int.repr (ft_log t)));
               lvar _info t_offinfo v_info; temp _gp_info pi)
        SEP (data_at Tsh t_offinfo (Vint (Int.repr ls), Vint (Int.repr mx)) v_info;
             data_at_ shi t_offinfo pi;
             data_at sh t_seqhdr (Vint (Int.repr fm), Vint (Int.repr (ft_log t))) tp;
             data_at sh (tarray t_seqSymbol (2 ^ ft_log t)) (map (seqcell KOF) (ft_cells t)) (offset_val 8 tp)))%assert.
      - forward. forward. Exists mx. entailer!.
      - forward.
        { entailer!. offinfo_cell Hz e. offinfo_tc. }
        offinfo_cell Hz e.
        forward. Exists (sk_bits KOF (fe_sym e)). entailer!.
      - Intros m. forward. forward.
        { entailer!. offinfo_cell Hz e. offinfo_tc. }
        offinfo_cell Hz e.
        forward_if (EX ls': Z, PROP ()
          LOCAL (temp _u (Vint (Int.repr i));
                 temp _max (Vint (Int.repr (2 ^ ft_log t))); temp _table (offset_val 8 tp);
                 temp _tableLog (Vint (Int.repr (ft_log t)));
                 lvar _info t_offinfo v_info; temp _gp_info pi)
          SEP (data_at Tsh t_offinfo (Vint (Int.repr ls'), Vint (Int.repr m)) v_info;
               data_at_ shi t_offinfo pi;
               data_at sh t_seqhdr (Vint (Int.repr fm), Vint (Int.repr (ft_log t))) tp;
               data_at sh (tarray t_seqSymbol (2 ^ ft_log t)) (map (seqcell KOF) (ft_cells t)) (offset_val 8 tp)))%assert.
        + forward. forward. Exists (ls + 1). entailer!.
        + forward. Exists ls. entailer!.
        + Intros ls'. Exists ls' m. entailer!. }
    Intros ls mx. forward. forward.
    { entailer!. change (Int.unsigned Int.iwordsize) with 32; lia. }
    Exists (Int.unsigned (Int.shl (Int.repr ls) (Int.sub (Int.repr 8) (Int.repr (ft_log t))))) mx.
    rewrite Int.repr_unsigned. entailer!.
  - forward. Exists 0 0. entailer!.
  - Intros ls mx. forward. forward. forward. forward.
    Exists ls mx. unfold seqtab_at_fm. entailer!.
Qed.

Lemma body_maxShortOffset : body_ok TOP3_G ZSTD_maxShortOffset_spec.
Proof.
  exists f_ZSTD_maxShortOffset; split; [reflexivity | split; [reflexivity |]].
  start_function.
  forward_call tt.
  forward_if.
  - forward.
  - discriminate.
Qed.

Lemma body_decompressBlock_internal_fixed :
  GLOBALS_obligation -> body_ok TOP3_G ZSTD_decompressBlock_internal_fixed_spec.
Proof.
  intros GL. exists f_ZSTD_decompressBlock_internal; split; [reflexivity | split; [reflexivity |]].
  start_function.
  rename H9 into Hptrs. rename H10 into Hext0. rename H11 into Hhd0.
  pose proof H as Ho. pose proof H0 as Hi.
  destruct H as (Hosh & HoN & HoN32 & Hd & Hcap & Hdc).
  destruct H0 as (Hish & Hioff & Hin & HiN32 & HiN & Hsl & Hbytes & Hwin).
  assert (Hbsm: 0 <= bsm <= 131072) by (unfold ZSTD_BLOCKSIZE_MAX in H2; lia).
  unfold tabs_def. Intros. rename H into Hts.
  forward.
  tp_skiploop.
  tp_check (Zlength (iw_s i) <= bsm).
  { entailer!. }
  { forward_call (p, fs, bsm).
    forward_if.
    - tp_errpath.
      Exists (err_code 72) (oa_c o) (fs_ddictIsCold fs) (@None tstate).
      rewrite tp_set_cold_same, (tp_err_true 72) by lia. destruct (tp_err_val 72) as [EV ER]; [lia |].
      assert (BX: ox = None -> block_exact ts o i h bsm streaming (err_code 72) (oa_c o) None)
        by (intros _; apply bx_big; [lia | apply tp_err_true; lia]).
      entailer!.
      all: try (split; [intros _; split; [reflexivity | apply tp_dec_err; lia] |]).
      all: try (intros; unfold block_ok; rewrite tp_db_big by lia; exact I).
      all: try apply tp_unch.
      apply tp_parts_uninit.
    - forward. entailer!. }
  Intros. rename H into Hsmall.
  sep_apply (tp_scratch_to p (ts_lxb ts)). Intros.
  assert (Hhuf: match st_huf ts with Some ht => huf_ok ht | None => True end) by (destruct Hts; auto).
  forward_call (gv, p, fs, ox, st_huf ts, ts_x2 ts, ts_lxb ts, bsm, streaming, W, o, i).
  Intros vret. destruct vret as [[[[[[r1 oc1] l] lits] oh'] x2'] lxb']. simpl fst in *; simpl snd in *.
  match goal with Hx: ox = None -> lits_exact _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rename Hx into HLX end.
  match goal with Hx: byte_cells (oa_c o) -> byte_cells (iw_c i) -> byte_cells oc1 |- _ => rename Hx into HB1 end.
  match goal with Hx: is_error_code r1 = false -> forall j, 0 <= j < oa_N o -> _ |- _ => rename Hx into HK1 end.
  tp_skiploop.
  forward_call r1.
  forward_if.
  { (* the literals section fails *)
    destruct (is_error_code r1) eqn:Er1; [| lia].
    forward.
    Exists r1 oc1 (fs_ddictIsCold fs) (@None tstate).
    assert (BX: ox = None -> block_exact ts o i h bsm streaming r1 oc1 None)
      by (intros Hox; eapply bx_lits_err; [exact Hsmall | exact (HLX Hox) | exact Er1]).
    rewrite tp_set_cold_same. rewrite Er1. entailer!.
    - unfold block_ok.
      destruct (decode_block ts (hc_hist h) (hc_out h) (iw_s i) bsm (hc_wsize h)) as [[ts2 cnt]|] eqn:Edb; [|exact I].
      right. split; [apply H13; reflexivity |].
      destruct (tp_db_lits _ _ _ _ _ _ _ _ Edb) as (lits0 & u & hf & Edl & Hl1 & Hl2).
      rewrite Edl in H12. destruct H12 as [H12 | H12]; [discriminate |].
      destruct (Z.min_spec (oa_cap o) bsm) as [[? Em] | [? Em]]; rewrite Em in H12; lia.
    - sep_apply (tp_tabs_seq_fields gv p ox). sep_apply (field_at_field_at_ Ews t_dctx (DOT _entropy DOT _rep)).
      sep_apply tp_uninit. cancel. }
  destruct (is_error_code r1) eqn:Er1; [tp_int_false |].
  specialize (H11 eq_refl). specialize (HK1 eq_refl). destruct H11 as (Hr1 & Hlat & Hllen & HlDst & Hoh' & Hdl & Hlpos & Hlsl).
  assert_PROP (isptr (iw_base i) /\ isptr (oa_base o)) as Hbases by entailer!.
  destruct Hbases as [Hib Hob]. Intros.
  forward. forward.
  assert (Eip: force_val (sem_binary_operation' Oadd (tptr tuchar) tulong (offset_val (iw_off i) (iw_base i))
     (Vlong (Int64.repr r1))) = offset_val (iw_off i + r1) (iw_base i)).
  { rewrite <- offset_offset_val. apply tp_add_l. destruct (iw_base i); try contradiction; exact I. }
  rewrite Eip, tp_sub64. clear Eip.
  forward_call (p, fs, bsm).
  forward_if (temp _t'5 (Vlong (Int64.repr (Z.min (oa_cap o) bsm)))).
  { forward. entailer!. do 2 f_equal. lia. }
  { forward_call (p, fs, bsm). forward. entailer!. do 2 f_equal. lia. }
  forward.
  set (TH := if oa_cap o =? 0 then 0
             else oa_d o + Z.min (oa_cap o) bsm - (hc_ps h - ext_len (hc_ext h))).
  forward_if (temp _t'7 (Vlong (Int64.repr TH))).
  { forward. entailer!. apply tp_r64_zero in H11; [| rep_lia]. unfold TH. rewrite H11. reflexivity. }
  { assert (Hc0: oa_cap o <> 0) by (intro E; apply H11; rewrite E; reflexivity).
    assert (Hlay: layout_ok fs (oa_base o) (oa_N o) (oa_d o) (hc_ps h) (hc_ext h)) by (apply H7; lia).
    destruct Hlay as (Hps & Hpsv & Hvs & Helen & Hext).
    forward_call (offset_val (oa_d o) (oa_base o), Z.min (oa_cap o) bsm).
    sep_apply (tp_ff_vs p fs). Intros.
    forward.
    { entailer!. rewrite Hvs. destruct (oa_base o); try contradiction; exact I. }
    sep_apply modus_ponens_wand.
    replace (if 0 <? Z.min (oa_cap o) bsm then offset_val (Z.min (oa_cap o) bsm) (offset_val (oa_d o) (oa_base o))
             else offset_val (oa_d o) (oa_base o)) with (offset_val (oa_d o + Z.min (oa_cap o) bsm) (oa_base o)).
    2: { destruct (0 <? Z.min (oa_cap o) bsm) eqn:E; [rewrite offset_offset_val; reflexivity |].
         apply Z.ltb_ge in E. replace (Z.min (oa_cap o) bsm) with 0 by lia. rewrite Z.add_0_r. reflexivity. }
    rewrite Hvs.
    forward_call (oa_base o, oa_d o + Z.min (oa_cap o) bsm, hc_ps h - ext_len (hc_ext h)).
    forward. entailer!. unfold TH. rewrite (proj2 (Z.eqb_neq _ _) Hc0). reflexivity. }
  forward.
  forward_call tt.
  forward_if (temp _t'11 (Vint (Int.repr 0))).
  { exfalso. lia. }
  { forward. entailer!. }
  forward.
  assert (Hcold: exists c, fs_ddictIsCold fs = Vint (Int.repr c) /\ (c = 0 \/ c = 1)).
  { destruct H5 as [E | E]; eexists; split; [exact E | auto | exact E | auto]. }
  destruct Hcold as (cold0 & Ecold & Hc01).
  sep_apply (tp_ff_cold p fs (fs_ddictIsCold fs)). Intros.
  forward.
  { entailer!. rewrite Ecold. exact I. }
  sep_apply modus_ponens_wand. rewrite tp_set_cold_same.
  destruct (tp_win_skip i r1 Hi) as [Hi2 Hl2]; [lia |].
  replace (Zlength (iw_s i) - r1) with (Zlength (iw_s (iw_skip i r1))) by lia.
  change (offset_val (iw_off i + r1) (iw_base i)) with (offset_val (iw_off (iw_skip i r1)) (iw_base (iw_skip i r1))).
  assert (Hseq: seqs_ok (st_seq ts)) by (destruct Hts as [_ [? _]]; auto).
  forward_call (gv, p, fs, ox, st_seq ts, (match st_seq ts with Some _ => 1 | None => 0 end), Tsh, v_nbSeq,
                iw_skip i r1).
  Intros vret. destruct vret as [r2 res]. simpl fst in *; simpl snd in *.
  match goal with Hx: res = xb_seq_header _ _ |- _ => rename Hx into HSH end.
  change (iw_sh (iw_skip i r1)) with (iw_sh i). change (iw_N (iw_skip i r1)) with (iw_N i).
  change (iw_c (iw_skip i r1)) with (iw_c i). change (iw_base (iw_skip i r1)) with (iw_base i).
  match goal with Hx: shdr_ok _ _ res |- _ => rename Hx into Hsh end.
  destruct res as [[[nb os'] used]|].
  2: { (* the sequences header is invalid *)
    assert (Edsh: decode_seq_header (st_seq ts) (iw_s (iw_skip i r1)) = None).
    { destruct (decode_seq_header _ _) eqn:E; [| reflexivity].
      destruct Hsh as [Hm _]. specialize (Hm _ E). discriminate. }
    Intros. forward_call r2.
    match goal with Hr: is_error_code r2 = true |- _ => rewrite Hr end.
    forward_if; [| tp_int_false].
    forward.
    Exists r2 oc1 (fs_ddictIsCold fs) (@None tstate).
    assert (BX: ox = None -> block_exact ts o i h bsm streaming r2 oc1 None)
      by (intros Hox; eapply bx_hdr_err; [exact Hsmall | exact (HLX Hox) | exact Er1 | exact (eq_sym HSH) |
                                          assumption]).
    rewrite tp_set_cold_same. entailer!.
    - unfold block_ok. rewrite (tp_db_hdr_none _ _ _ _ _ _ _ _ _ Hdl Edsh). exact I.
    - sep_apply tp_huf_junk. sep_apply tp_litfields_scratch. sep_apply tp_seq_junk_fields.
      sep_apply (field_at_field_at_ Ews t_dctx (DOT _entropy DOT _rep)).
      sep_apply tp_uninit. cancel. }
  Intros. subst r2.
  set (rest := iw_s (iw_skip i r1)) in *.
  assert (Hrb: bytes_ok rest) by (apply tp_bytes_skip; auto).
  destruct Hsh as [Edsh ((Hu1 & Hused) & Hnb & Hos0 & Hnb0 & Hnb1')].
  assert (Hnb1: nb <> 0 -> os' <> None) by (intros; apply Hnb1'; lia).
  assert (Herr2: is_error_code used = false).
  { unfold is_error_code. apply Z.ltb_ge. rewrite Hl2 in Hused. unfold ZSTD_BLOCKSIZE_MAX in *. lia. }
  forward_call used. rewrite Herr2.
  forward_if; [exfalso; lia |].
  forward. forward.
  assert (Eip: force_val (sem_binary_operation' Oadd (tptr tuchar) tulong (offset_val (iw_off (iw_skip i r1)) (iw_base i))
     (Vlong (Int64.repr used))) = offset_val (iw_off (iw_skip (iw_skip i r1) used)) (iw_base (iw_skip (iw_skip i r1) used))).
  { simpl. rewrite <- (offset_offset_val (iw_base i) (iw_off i + r1) used). apply tp_add_l.
    destruct (iw_base i); try contradiction; exact I. }
  rewrite Eip, tp_sub64. clear Eip.
  assert (Hu0: 0 <= used) by lia.
  destruct (tp_win_skip (iw_skip i r1) used Hi2) as [Hi3 Hl3]; [fold rest; lia |].
  replace (Zlength (iw_s (iw_skip i r1)) - used) with (Zlength (iw_s (iw_skip (iw_skip i r1) used))) by lia.
  tp_check (oa_cap o = 0 -> nb = 0).
  { entailer!. }
  { forward_if (temp _t'15 (Vint (Int.repr (if oa_cap o =? 0 then 1 else 0)))).
    { eapply derives_trans; [| apply (tp_tc_null W o oc1 Ho H6)]. cancel. }
    { exfalso. match goal with Hn: offset_val (oa_d o) (oa_base o) = nullval |- _ =>
        destruct (oa_base o); try contradiction; simpl in Hn; discriminate Hn end. }
    { forward. entailer!. destruct (Z.eqb_spec (oa_cap o) 0) as [E | E].
      - rewrite E. reflexivity.
      - rewrite Int64.eq_false; [reflexivity |]. intros X. apply tp_r64_zero in X; [lia | rep_lia]. }
    forward_if (temp _t'16 (Vint (Int.repr (if andb (oa_cap o =? 0) (0 <? nb) then 1 else 0)))).
    { forward. forward. entailer!.
      destruct (Z.eqb_spec (oa_cap o) 0) as [E | E]; [| exfalso; lia]. simpl.
      symmetry; apply tp_lt_int; unfold LONGNBSEQ in Hnb; rep_lia. }
    { forward. entailer!. destruct (Z.eqb_spec (oa_cap o) 0) as [E | E]; [tp_int_false | reflexivity]. }
    forward_if.
    { (* no room for the sequences *)
      assert (Hc0: oa_cap o = 0 /\ 0 < nb).
      { match goal with Hx: (if andb _ _ then 1 else 0) <> 0 |- _ => rename Hx into Hx16 end.
        destruct (Z.eqb_spec (oa_cap o) 0), (Z.ltb_spec 0 nb); cbn in Hx16; try (exfalso; lia); auto. }
      assert_PROP (seqs_ok os') as Hos' by (sep_apply (tp_seqs_ok gv p ox os'); entailer!).
      tp_errpath.
      Exists (err_code 70) oc1 (fs_ddictIsCold fs) (@None tstate).
      rewrite tp_set_cold_same, (tp_err_true 70) by lia. destruct (tp_err_val 70) as [EV ER]; [lia |].
      assert (BX: ox = None -> block_exact ts o i h bsm streaming (err_code 70) oc1 None)
        by (intros Hox; eapply bx_room_err; [exact Hsmall | exact (HLX Hox) | exact Er1 | exact (eq_sym HSH) |
                                             exact (proj1 Hc0) | exact (proj2 Hc0) | apply tp_err_true; lia]).
      entailer!.
      - split; [intros _; split; [reflexivity | apply tp_dec_err; lia] |]. intros. unfold block_ok.
        destruct (decode_block ts (hc_hist h) (hc_out h) (iw_s i) bsm (hc_wsize h)) as [[ts2 cnt]|] eqn:Edb; [|exact I].
        right. split; [apply tp_dec_err; lia |].
        pose proof (tp_db_nbpos _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hdl Edsh Edb (proj2 Hc0) Hos'). lia.
      - tp_err_tabs gv p ox. }
    { forward. entailer!.
      match goal with Hx: Int.repr (if andb _ _ then 1 else 0) = Int.zero |- _ => rename Hx into Hx16 end.
      destruct (Z.eqb_spec (oa_cap o) 0), (Z.ltb_spec 0 nb); cbn in Hx16; try tp_int_false; lia. }
  }
  Intros. match goal with Hx: oa_cap o = 0 -> nb = 0 |- _ => rename Hx into Hcnb end.
  tp_skiploop.
  rewrite Ecold.
  assert (HTH: 0 <= TH <= Int64.max_unsigned).
  { unfold TH. destruct (oa_cap o =? 0) eqn:Ec; [rep_lia |].
    apply Z.eqb_neq in Ec. destruct (H7 ltac:(lia)) as (Hps & _ & _ & Hel & _).
    unfold ZSTD_BLOCKSIZE_MAX in *. rep_lia. }
  set (V23 := if cold0 =? 0 then (if 16777216 <? TH then 1 else 0) else 0).
  set (V22 := if V23 =? 0 then 0 else if 8 <? nb then 1 else 0).
  forward_if (temp _t'22 (Vint (Int.repr V22))).
  { exfalso; lia. }
  { forward_if (temp _t'23 (Vint (Int.repr V23))).
    - forward. entailer!.
      assert (Hc0: cold0 = 0) by (destruct Hc01 as [E|E]; [exact E | subst cold0; tp_int_false]).
      unfold V23. rewrite Hc0. simpl Z.eqb. cbv iota.
      change (Int.unsigned (Int.shl (Int.repr 1) (Int.repr 24))) with 16777216.
      rewrite tp_cmpu_gt by rep_lia. destruct (16777216 <? TH); reflexivity.
    - forward. entailer!.
      assert (Hc1: cold0 = 1) by (destruct Hc01 as [E|E]; [subst cold0; contradiction | exact E]).
      unfold V23. rewrite Hc1. reflexivity.
    - forward_if (temp _t'22 (Vint (Int.repr V22))).
      + forward. forward. forward. entailer!.
        unfold V22. rewrite (proj2 (Z.eqb_neq _ _)) by auto.
        first [apply tp_lt_int | symmetry; apply tp_lt_int]; unfold LONGNBSEQ in Hnb; rep_lia.
      + forward. entailer!.
        assert (E23: V23 = 0).
        { unfold V23 in *. destruct (cold0 =? 0), (16777216 <? TH); auto; tp_int_false. }
        unfold V22. rewrite E23. reflexivity.
      + entailer!. }
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (EX up: Z, PROPx ((up = 0 \/ up = 1) :: P)
       (LOCALx [temp _usePrefetchDecoder (Vint (Int.repr up)); temp _isLongOffset (Vint (Int.repr 0));
                temp _ip (offset_val (iw_off (iw_skip (iw_skip i r1) used)) (iw_base (iw_skip (iw_skip i r1) used)));
                temp _srcSize (Vlong (Int64.repr (Zlength rest - used)));
                lvar _info (Tstruct ___gp_ZSTD_OffsetInfo noattr) v_info; lvar _nbSeq tint v_nbSeq; gvars gv;
                temp _dctx p; temp _dst (offset_val (oa_d o) (oa_base o));
                temp _dstCapacity (Vlong (Int64.repr (oa_cap o)))]
         (SEPx R))) end.
  { (* the offset table's statistics *)
    assert (HV: cold0 = 0 /\ 8 < nb).
    { match goal with Hx: V22 <> 0 |- _ => rename Hx into H22 end.
      unfold V22, V23 in H22. destruct (cold0 =? 0) eqn:E1, (16777216 <? TH), (8 <? nb) eqn:E2;
        simpl in H22; try lia; try (split; [apply Z.eqb_eq; auto | apply Z.ltb_lt; auto]). }
    destruct os' as [[[ta tb] tc]|]; [| exfalso; apply (Hnb1 ltac:(lia)); reflexivity].
    unfold tabs_seq at 1. Intros.
    sep_apply (tp_of_access GL gv p ox tb). Intros tp sh fm.
    forward.
    { unfold seqtab_at_fm. Intros. entailer!. }
    forward.
    forward_call (Tsh, v_info, sh, tb, fm, tp, nb).
    { unfold LONGNBSEQ in Hnb. rep_lia. }
    Intros vret. destruct vret as [ls mx]. simpl fst in *; simpl snd in *.
    sep_apply (modus_ponens_wand (field_at Ews t_dctx (DOT _OFTptr) tp p * seqtab_at_fm sh KOF tb fm tp)).
    Intros.
    forward_if (temp _t'17 (Vint (Int.repr 0))).
    { exfalso; lia. }
    { forward. entailer!. }
    match goal with |- semax _ ?Pre _ _ => forward_if Pre end.
    { exfalso; lia. }
    { forward. entailer!. }
    destruct HV as [Hc0 H8nb]. subst cold0.
    forward_if.
    2: { exfalso. match goal with Hx: Int.repr 0 <> Int.zero |- _ => apply Hx; reflexivity end. }
    forward_call tt.
    forward_if (temp _t'21 (Vint (Int.repr 7))).
    { forward. entailer!. }
    { tp_int_false. }
    forward. forward. forward.
    Exists (Z.b2z (negb (Int.ltu (Int.repr ls) (Int.repr 7)))). unfold tabs_seq. entailer!.
    all: try (destruct (Int.ltu _ _); simpl; auto).
    all: try (sep_apply (data_at_data_at_ Tsh t_offinfo); cancel). }
  { forward. Exists cold0. entailer!. }
  Intros up.
  sep_apply (tp_ff_cold p fs (Vint (Int.repr 0))). Intros.
  forward.
  sep_apply (modus_ponens_wand (field_at Ews t_dctx (DOT _ddictIsCold) (Vint (Int.repr 0)) p)).
  assert_PROP (seqs_ok os') as Hos' by (sep_apply (tp_seqs_ok gv p ox os'); entailer!).
  set (fs' := fs_set_cold fs (Vint (Int.repr 0))).
  set (o1 := {| oa_sh := oa_sh o; oa_base := oa_base o; oa_N := oa_N o; oa_c := oc1; oa_d := oa_d o;
                oa_cap := oa_cap o |}).
  set (i3 := iw_skip (iw_skip i r1) used).
  assert (Ho1: outarr_ok o1)
    by (unfold o1, outarr_ok; cbn [oa_sh oa_base oa_N oa_c oa_d oa_cap];
        exact (conj Hosh (conj H0 (conj HoN32 (conj Hd (conj Hcap Hdc)))))).
  assert (Hlay1: 0 < oa_cap o1 -> layout_ok fs' (oa_base o1) (oa_N o1) (oa_d o1) (hc_ps h) (hc_ext h)) by exact H7.
  assert (Hlat1: lits_at l (oa_c o1) (oa_d o1) (oa_cap o1) i3 lits) by exact Hlat.
  replace (Zlength rest - used) with (Zlength (iw_s i3)) by (unfold i3, rest; rewrite Hl3; reflexivity).
  change (offset_val (iw_off (iw_skip (iw_skip i r1) used)) (iw_base (iw_skip (iw_skip i r1) used)))
    with (offset_val (iw_off i3) (iw_base i3)).
  change (data_at (oa_sh o) (tarray tuchar (oa_N o)) oc1 (oa_base o))
    with (data_at (oa_sh o1) (tarray tuchar (oa_N o1)) (oa_c o1) (oa_base o1)).
  change (data_at (iw_sh i) (tarray tuchar (iw_N i)) (iw_c i) (iw_base i))
    with (data_at (iw_sh i3) (tarray tuchar (iw_N i3)) (iw_c i3) (iw_base i3)).
  change (litfields p (oa_base o) (iw_base i) l lits lxb') with (litfields p (oa_base o1) (iw_base i3) l lits lxb').
  change (offset_val (oa_d o) (oa_base o)) with (offset_val (oa_d o1) (oa_base o1)).
  change (Vlong (Int64.repr (oa_cap o))) with (Vlong (Int64.repr (oa_cap o1))).
  assert (Hrep: rep_ok (st_rep ts)) by (destruct Hts as [_ [_ ?]]; auto).
  assert (Hptrs1: hist_ptrs_ok fs' o1 (hc_ext h)) by exact Hptrs.
  assert (Hext1: ext0_ok W fs' (hc_ext h)) by exact Hext0.
  assert (Hlpos1: lit_pos l (oa_d o1) (oa_cap o1) bsm (Zlength lits)) by exact Hlpos.
  assert (Hnbp: nb > 0 -> os' <> None /\ 0 < oa_cap o1) by (intros; split; [apply Hnb1; lia | unfold o1; simpl; destruct (Z.eq_dec (oa_cap o) 0); [specialize (Hcnb e); lia | lia]]).
  assert (Hfe: (match st_seq ts with Some _ => 1 | None => 0 end) = 0 \/ (match st_seq ts with Some _ => 1 | None => 0 end) = 1)
    by (destruct (st_seq ts); auto).
  (* what the sequences copy is defined: the history (the literals decoder keeps defined cells defined, also an
     extDict that the block's area overlaps) and the 32 cells after literals in dst *)
  assert (Hhd1: hist_def (oa_c o1) (oa_d o1) (hc_ps h) (hc_ext h)).
  { apply (tp_hist_def_keep (oa_c o)); [rewrite HoN; exact HK1 | exact Hhd0]. }
  assert (Hsl1: lit_slack_def l (oa_c o1) (Zlength lits)) by exact Hlsl.
  forward_if.
  { forward.
    forward_call (gv, p, fs', ox, os', (match st_seq ts with Some _ => 1 | None => 0 end), st_rep ts, l, lits, lxb',
                  nb, bsm, W, o1, i3, h).
    Intros vret. destruct vret as [[r3 oc'] rep']. cbn [fst snd] in *.
    match goal with Hx: seqs_exact _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rename Hx into HSX end.
    assert (BX: ox = None -> block_exact ts o i h bsm streaming r3 oc'
                  (if is_error_code r3 then None
                   else Some (mk_tstate {| st_huf := oh'; st_seq := os'; st_rep := rep' |} x2' lxb'))).
    { intros Hox. apply (bx_seqs ts o i h bsm streaming r1 oc1 l lits oh' x2' lxb' nb os' used o1 i3 r3 oc' rep');
        [exact Ho | exact Hi | exact Hsmall | exact (HLX Hox) | exact Er1 |
        exact (eq_sym HSH) | exact Hcnb | reflexivity | reflexivity | reflexivity | reflexivity |
        reflexivity | reflexivity | reflexivity | exact HSX]. }
    forward.
    match goal with Hx: unchanged_outside (oa_c o1) oc' _ (oa_d o1 + oa_cap o1) |- _ => rename Hx into Hs4 end.
    match goal with Hx: is_error_code r3 = false -> _ |- _ => rename Hx into Hs6 end.
    match goal with Hx: oa_cap o1 = 0 \/ _ -> _ |- _ => rename Hx into Hs7 end.
    match goal with Hx: Zlength oc' = _ |- _ => rename Hx into Hs2 end.
    assert (HBo: byte_cells (oa_c o) -> byte_cells (iw_c i) -> ext_bytes (hc_ext h) -> byte_cells oc').
    { intros Hb1 Hb2 Hb3. match goal with Hx: byte_cells (oa_c o1) -> _ |- _ => apply Hx end;
        [exact (HB1 Hb1 Hb2) | exact Hb2 | exact Hb3]. }
    assert (U: unchanged_outside (oa_c o) oc' (oa_d o) (oa_d o + oa_cap o)).
    { apply (tp_unch_trans _ oc1 _ (oa_d o) (oa_d o + oa_cap o) (oa_d o) (oa_d o + oa_cap o)); auto; [congruence | lia | lia]. }
    assert (B: oa_cap o = 0 \/
               (hist_view (oa_c o) (oa_d o) (hc_ps h) (hc_ext h) (hc_hist h) (hc_out h) (hc_wsize h) /\
                ext_clear (oa_d o) (hc_ps h) (oa_cap o) bsm (hc_ext h) (hc_hist h) (hc_out h) (hc_wsize h)) ->
               bytes_ok (hc_hist h) -> bytes_ok (hc_out h) ->
               block_ok ts (hc_hist h) (hc_out h) (iw_s i) bsm (hc_wsize h) streaming (oa_c o) oc' (oa_d o) (oa_cap o) r3
                 (if is_error_code r3 then None else Some {| st_huf := oh'; st_seq := os'; st_rep := rep' |})).
    { intros HH Hbh Hbo. apply (tp_block_ok ts _ _ _ _ _ _ _ oc1 _ _ _ r1 lits oh' nb os' used); auto.
      - congruence.
      - intros E. destruct (Hs6 E) as (_ & X & _). exact X.
      - apply Hs7. destruct HH as [E | [Hv Hc]]; [left; exact E |].
        destruct (Z.eq_dec (oa_cap o) 0) as [E | E]; [left; exact E |]. right. split; [| exact Hc].
        destruct (H7 ltac:(lia)) as (Hps & _).
        apply (tp_hist_view_transfer (oa_c o) oc1 (oa_d o) (oa_cap o) bsm (hc_ps h) _ _ _ _ streaming); auto;
          [congruence | lia].
      - intros ts2' cnt' Edb' Er' Ercnt. destruct (Z.eq_dec (oa_cap o) 0) as [E0 | E0].
        + destruct (Hs6 Er') as (Hle & _). cbn [oa_cap o1] in Hle.
          destruct cnt'; [constructor | rewrite Zlength_cons in Ercnt; pose proof (Zlength_nonneg cnt'); lia].
        + apply (tp_db_bytes _ _ _ _ _ _ _ _ Edb'); auto.
          intros lits0 u hf E. rewrite E in Hdl. destruct Hdl as (_ & <- & _). exact (proj1 Hlat). }
    destruct (is_error_code r3) eqn:Er3.
    + Exists r3 oc' (Vint (Int.repr 0)) (@None tstate). entailer!.
      sep_apply tp_huf_junk. sep_apply (tp_tabs_seq_fields gv p ox). sep_apply tp_scratch_x_any.
      sep_apply (field_at_field_at_ Ews t_dctx (DOT _entropy DOT _rep)).
      sep_apply tp_uninit. Intros lxb0. Exists lxb0. unfold fs'. cancel.
    + assert (Hbt: hist_def (oa_c o) (oa_d o) (hc_ps h) (hc_ext h) ->
                   (ext_clean (oa_d o) (oa_cap o) (hc_ext h) \/ (r3 <= bsm /\ ext_far (oa_d o) (oa_cap o) bsm (hc_ext h))) ->
                   exists cnt, sublist (oa_d o) (oa_d o + r3) oc' = zbytes cnt /\ bytes_ok cnt).
      { intros Hhd Hcl. destruct (Hs6 eq_refl) as (Hr3c & _ & Hb). destruct (Z.eq_dec (oa_cap o) 0) as [E | E].
        - exists []. replace r3 with 0 by (cbn [oa_cap o1] in Hr3c; lia). rewrite Z.add_0_r, sublist_nil.
          split; [reflexivity | constructor].
        - apply Hb; [| exact Hcl]. destruct (H7 ltac:(lia)) as (Hps & _).
          destruct Hcl as [Hcl | [_ Hfar]].
          + apply (tp_hist_def_transfer (oa_c o) oc1 (oa_d o) (oa_cap o)); auto; try congruence; try lia.
          + apply (tp_hist_def_far (oa_c o) oc1 (oa_d o) (oa_cap o) bsm (hc_ps h) (hc_ext h) streaming);
              auto; try congruence; try lia. }
      assert (Hsb: streaming = 1 -> r3 <= bsm ->
                   unchanged_outside (oa_c o) oc' (oa_d o) (oa_d o + Z.min (oa_cap o) (bsm + WILDCOPY_OVERLENGTH))).
      { intros Hs Hr. destruct (Hs6 eq_refl) as (_ & Hu & _).
        apply (tp_stream_unch (oa_c o) oc1 oc' (oa_d o) (oa_cap o) bsm r3 streaming); auto; try congruence; try lia; exact Hu. }
      destruct (Hs6 eq_refl) as (Hr3c & _).
      assert (Hdok: dstate_ok {| st_huf := oh'; st_seq := os'; st_rep := rep' |})
        by (unfold dstate_ok; cbn [st_huf st_seq st_rep]; split; [destruct oh' as [hh|]; [exact Hoh' | exact I] | split; assumption]).
      rewrite (tp_fe nb (st_seq ts) os') by auto.
      sep_apply (tp_tabs_fold gv p ox oh' x2' os' rep' lxb' Hdok).
      Exists r3 oc' (Vint (Int.repr 0)) (Some (mk_tstate {| st_huf := oh'; st_seq := os'; st_rep := rep' |} x2' lxb')).
      unfold fs'. entailer!.
      split; [exact Hr3c |]. split; [reflexivity |]. split; [discriminate | split; [exact Hsb | exact Hbt]]. }
  sep_apply (tp_lf_loc p (oa_base o1) (iw_base i3) l lits lxb'). Intros.
  forward.
  sep_apply (modus_ponens_wand (field_at Ews t_dctx (DOT _litBufferLocation) (Vint (Int.repr (loc_code l))) p)).
  forward_if.
  { assert (Hspl: is_split l).
    { destruct l; simpl; auto; exfalso;
        match goal with Hx: Int.repr (loc_code _) = Int.repr 2 |- _ =>
          apply (f_equal Int.unsigned) in Hx; vm_compute in Hx; discriminate end. }
    forward.
    forward_call (gv, p, fs', ox, os', (match st_seq ts with Some _ => 1 | None => 0 end), st_rep ts, l, lits, lxb',
                  nb, bsm, W, o1, i3, h).
    Intros vret. destruct vret as [[r3 oc'] rep']. cbn [fst snd] in *.
    match goal with Hx: seqs_exact _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rename Hx into HSX end.
    assert (BX: ox = None -> block_exact ts o i h bsm streaming r3 oc'
                  (if is_error_code r3 then None
                   else Some (mk_tstate {| st_huf := oh'; st_seq := os'; st_rep := rep' |} x2' lxb'))).
    { intros Hox. apply (bx_seqs ts o i h bsm streaming r1 oc1 l lits oh' x2' lxb' nb os' used o1 i3 r3 oc' rep');
        [exact Ho | exact Hi | exact Hsmall | exact (HLX Hox) | exact Er1 |
        exact (eq_sym HSH) | exact Hcnb | reflexivity | reflexivity | reflexivity | reflexivity |
        reflexivity | reflexivity | reflexivity | exact HSX]. }
    forward.
    match goal with Hx: unchanged_outside (oa_c o1) oc' _ (oa_d o1 + oa_cap o1) |- _ => rename Hx into Hs4 end.
    match goal with Hx: is_error_code r3 = false -> _ |- _ => rename Hx into Hs6 end.
    match goal with Hx: oa_cap o1 = 0 \/ _ -> _ |- _ => rename Hx into Hs7 end.
    match goal with Hx: Zlength oc' = _ |- _ => rename Hx into Hs2 end.
    assert (HBo: byte_cells (oa_c o) -> byte_cells (iw_c i) -> ext_bytes (hc_ext h) -> byte_cells oc').
    { intros Hb1 Hb2 Hb3. match goal with Hx: byte_cells (oa_c o1) -> _ |- _ => apply Hx end;
        [exact (HB1 Hb1 Hb2) | exact Hb2 | exact Hb3]. }
    assert (U: unchanged_outside (oa_c o) oc' (oa_d o) (oa_d o + oa_cap o)).
    { apply (tp_unch_trans _ oc1 _ (oa_d o) (oa_d o + oa_cap o) (oa_d o) (oa_d o + oa_cap o)); auto; [congruence | lia | lia]. }
    assert (B: oa_cap o = 0 \/
               (hist_view (oa_c o) (oa_d o) (hc_ps h) (hc_ext h) (hc_hist h) (hc_out h) (hc_wsize h) /\
                ext_clear (oa_d o) (hc_ps h) (oa_cap o) bsm (hc_ext h) (hc_hist h) (hc_out h) (hc_wsize h)) ->
               bytes_ok (hc_hist h) -> bytes_ok (hc_out h) ->
               block_ok ts (hc_hist h) (hc_out h) (iw_s i) bsm (hc_wsize h) streaming (oa_c o) oc' (oa_d o) (oa_cap o) r3
                 (if is_error_code r3 then None else Some {| st_huf := oh'; st_seq := os'; st_rep := rep' |})).
    { intros HH Hbh Hbo. apply (tp_block_ok ts _ _ _ _ _ _ _ oc1 _ _ _ r1 lits oh' nb os' used); auto.
      - congruence.
      - intros E. destruct (Hs6 E) as (_ & X & _). exact X.
      - apply Hs7. destruct HH as [E | [Hv Hc]]; [left; exact E |].
        destruct (Z.eq_dec (oa_cap o) 0) as [E | E]; [left; exact E |]. right. split; [| exact Hc].
        destruct (H7 ltac:(lia)) as (Hps & _).
        apply (tp_hist_view_transfer (oa_c o) oc1 (oa_d o) (oa_cap o) bsm (hc_ps h) _ _ _ _ streaming); auto;
          [congruence | lia].
      - intros ts2' cnt' Edb' Er' Ercnt. destruct (Z.eq_dec (oa_cap o) 0) as [E0 | E0].
        + destruct (Hs6 Er') as (Hle & _). cbn [oa_cap o1] in Hle.
          destruct cnt'; [constructor | rewrite Zlength_cons in Ercnt; pose proof (Zlength_nonneg cnt'); lia].
        + apply (tp_db_bytes _ _ _ _ _ _ _ _ Edb'); auto.
          intros lits0 u hf E. rewrite E in Hdl. destruct Hdl as (_ & <- & _). exact (proj1 Hlat). }
    destruct (is_error_code r3) eqn:Er3.
    + Exists r3 oc' (Vint (Int.repr 0)) (@None tstate). entailer!.
      sep_apply tp_huf_junk. sep_apply (tp_tabs_seq_fields gv p ox). sep_apply tp_scratch_x_any.
      sep_apply (field_at_field_at_ Ews t_dctx (DOT _entropy DOT _rep)).
      sep_apply tp_uninit. Intros lxb0. Exists lxb0. unfold fs'. cancel.
    + assert (Hbt: hist_def (oa_c o) (oa_d o) (hc_ps h) (hc_ext h) ->
                   (ext_clean (oa_d o) (oa_cap o) (hc_ext h) \/ (r3 <= bsm /\ ext_far (oa_d o) (oa_cap o) bsm (hc_ext h))) ->
                   exists cnt, sublist (oa_d o) (oa_d o + r3) oc' = zbytes cnt /\ bytes_ok cnt).
      { intros Hhd Hcl. destruct (Hs6 eq_refl) as (Hr3c & _ & Hb). destruct (Z.eq_dec (oa_cap o) 0) as [E | E].
        - exists []. replace r3 with 0 by (cbn [oa_cap o1] in Hr3c; lia). rewrite Z.add_0_r, sublist_nil.
          split; [reflexivity | constructor].
        - apply Hb; [| exact Hcl]. destruct (H7 ltac:(lia)) as (Hps & _).
          destruct Hcl as [Hcl | [_ Hfar]].
          + apply (tp_hist_def_transfer (oa_c o) oc1 (oa_d o) (oa_cap o)); auto; try congruence; try lia.
          + apply (tp_hist_def_far (oa_c o) oc1 (oa_d o) (oa_cap o) bsm (hc_ps h) (hc_ext h) streaming);
              auto; try congruence; try lia. }
      assert (Hsb: streaming = 1 -> r3 <= bsm ->
                   unchanged_outside (oa_c o) oc' (oa_d o) (oa_d o + Z.min (oa_cap o) (bsm + WILDCOPY_OVERLENGTH))).
      { intros Hs Hr. destruct (Hs6 eq_refl) as (_ & Hu & _).
        apply (tp_stream_unch (oa_c o) oc1 oc' (oa_d o) (oa_cap o) bsm r3 streaming); auto; try congruence; try lia; exact Hu. }
      destruct (Hs6 eq_refl) as (Hr3c & _).
      assert (Hdok: dstate_ok {| st_huf := oh'; st_seq := os'; st_rep := rep' |})
        by (unfold dstate_ok; cbn [st_huf st_seq st_rep]; split; [destruct oh' as [hh|]; [exact Hoh' | exact I] | split; assumption]).
      rewrite (tp_fe nb (st_seq ts) os') by auto.
      sep_apply (tp_tabs_fold gv p ox oh' x2' os' rep' lxb' Hdok).
      Exists r3 oc' (Vint (Int.repr 0)) (Some (mk_tstate {| st_huf := oh'; st_seq := os'; st_rep := rep' |} x2' lxb')).
      unfold fs'. entailer!.
      split; [exact Hr3c |]. split; [reflexivity |]. split; [discriminate | split; [exact Hsb | exact Hbt]]. }
  { assert (Hnspl: not_split l).
    { destruct l; simpl; auto; try (match goal with Hx: Int.repr (loc_code _) <> Int.repr 2 |- _ => apply Hx; reflexivity end). }
    forward.
    forward_call (gv, p, fs', ox, os', (match st_seq ts with Some _ => 1 | None => 0 end), st_rep ts, l, lits, lxb',
                  nb, bsm, W, o1, i3, h).
    Intros vret. destruct vret as [[r3 oc'] rep']. cbn [fst snd] in *.
    match goal with Hx: seqs_exact _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rename Hx into HSX end.
    assert (BX: ox = None -> block_exact ts o i h bsm streaming r3 oc'
                  (if is_error_code r3 then None
                   else Some (mk_tstate {| st_huf := oh'; st_seq := os'; st_rep := rep' |} x2' lxb'))).
    { intros Hox. apply (bx_seqs ts o i h bsm streaming r1 oc1 l lits oh' x2' lxb' nb os' used o1 i3 r3 oc' rep');
        [exact Ho | exact Hi | exact Hsmall | exact (HLX Hox) | exact Er1 |
        exact (eq_sym HSH) | exact Hcnb | reflexivity | reflexivity | reflexivity | reflexivity |
        reflexivity | reflexivity | reflexivity | exact HSX]. }
    forward.
    match goal with Hx: unchanged_outside (oa_c o1) oc' _ (oa_d o1 + oa_cap o1) |- _ => rename Hx into Hs4 end.
    match goal with Hx: is_error_code r3 = false -> _ |- _ => rename Hx into Hs6 end.
    match goal with Hx: oa_cap o1 = 0 \/ _ -> _ |- _ => rename Hx into Hs7 end.
    match goal with Hx: Zlength oc' = _ |- _ => rename Hx into Hs2 end.
    assert (HBo: byte_cells (oa_c o) -> byte_cells (iw_c i) -> ext_bytes (hc_ext h) -> byte_cells oc').
    { intros Hb1 Hb2 Hb3. match goal with Hx: byte_cells (oa_c o1) -> _ |- _ => apply Hx end;
        [exact (HB1 Hb1 Hb2) | exact Hb2 | exact Hb3]. }
    assert (U: unchanged_outside (oa_c o) oc' (oa_d o) (oa_d o + oa_cap o)).
    { apply (tp_unch_trans _ oc1 _ (oa_d o) (oa_d o + oa_cap o) (oa_d o) (oa_d o + oa_cap o)); auto; [congruence | lia | lia]. }
    assert (B: oa_cap o = 0 \/
               (hist_view (oa_c o) (oa_d o) (hc_ps h) (hc_ext h) (hc_hist h) (hc_out h) (hc_wsize h) /\
                ext_clear (oa_d o) (hc_ps h) (oa_cap o) bsm (hc_ext h) (hc_hist h) (hc_out h) (hc_wsize h)) ->
               bytes_ok (hc_hist h) -> bytes_ok (hc_out h) ->
               block_ok ts (hc_hist h) (hc_out h) (iw_s i) bsm (hc_wsize h) streaming (oa_c o) oc' (oa_d o) (oa_cap o) r3
                 (if is_error_code r3 then None else Some {| st_huf := oh'; st_seq := os'; st_rep := rep' |})).
    { intros HH Hbh Hbo. apply (tp_block_ok ts _ _ _ _ _ _ _ oc1 _ _ _ r1 lits oh' nb os' used); auto.
      - congruence.
      - intros E. destruct (Hs6 E) as (_ & X & _). exact X.
      - apply Hs7. destruct HH as [E | [Hv Hc]]; [left; exact E |].
        destruct (Z.eq_dec (oa_cap o) 0) as [E | E]; [left; exact E |]. right. split; [| exact Hc].
        destruct (H7 ltac:(lia)) as (Hps & _).
        apply (tp_hist_view_transfer (oa_c o) oc1 (oa_d o) (oa_cap o) bsm (hc_ps h) _ _ _ _ streaming); auto;
          [congruence | lia].
      - intros ts2' cnt' Edb' Er' Ercnt. destruct (Z.eq_dec (oa_cap o) 0) as [E0 | E0].
        + destruct (Hs6 Er') as (Hle & _). cbn [oa_cap o1] in Hle.
          destruct cnt'; [constructor | rewrite Zlength_cons in Ercnt; pose proof (Zlength_nonneg cnt'); lia].
        + apply (tp_db_bytes _ _ _ _ _ _ _ _ Edb'); auto.
          intros lits0 u hf E. rewrite E in Hdl. destruct Hdl as (_ & <- & _). exact (proj1 Hlat). }
    destruct (is_error_code r3) eqn:Er3.
    + Exists r3 oc' (Vint (Int.repr 0)) (@None tstate). entailer!.
      sep_apply tp_huf_junk. sep_apply (tp_tabs_seq_fields gv p ox). sep_apply tp_scratch_x_any.
      sep_apply (field_at_field_at_ Ews t_dctx (DOT _entropy DOT _rep)).
      sep_apply tp_uninit. Intros lxb0. Exists lxb0. unfold fs'. cancel.
    + assert (Hbt: hist_def (oa_c o) (oa_d o) (hc_ps h) (hc_ext h) ->
                   (ext_clean (oa_d o) (oa_cap o) (hc_ext h) \/ (r3 <= bsm /\ ext_far (oa_d o) (oa_cap o) bsm (hc_ext h))) ->
                   exists cnt, sublist (oa_d o) (oa_d o + r3) oc' = zbytes cnt /\ bytes_ok cnt).
      { intros Hhd Hcl. destruct (Hs6 eq_refl) as (Hr3c & _ & Hb). destruct (Z.eq_dec (oa_cap o) 0) as [E | E].
        - exists []. replace r3 with 0 by (cbn [oa_cap o1] in Hr3c; lia). rewrite Z.add_0_r, sublist_nil.
          split; [reflexivity | constructor].
        - apply Hb; [| exact Hcl]. destruct (H7 ltac:(lia)) as (Hps & _).
          destruct Hcl as [Hcl | [_ Hfar]].
          + apply (tp_hist_def_transfer (oa_c o) oc1 (oa_d o) (oa_cap o)); auto; try congruence; try lia.
          + apply (tp_hist_def_far (oa_c o) oc1 (oa_d o) (oa_cap o) bsm (hc_ps h) (hc_ext h) streaming);
              auto; try congruence; try lia. }
      assert (Hsb: streaming = 1 -> r3 <= bsm ->
                   unchanged_outside (oa_c o) oc' (oa_d o) (oa_d o + Z.min (oa_cap o) (bsm + WILDCOPY_OVERLENGTH))).
      { intros Hs Hr. destruct (Hs6 eq_refl) as (_ & Hu & _).
        apply (tp_stream_unch (oa_c o) oc1 oc' (oa_d o) (oa_cap o) bsm r3 streaming); auto; try congruence; try lia; exact Hu. }
      destruct (Hs6 eq_refl) as (Hr3c & _).
      assert (Hdok: dstate_ok {| st_huf := oh'; st_seq := os'; st_rep := rep' |})
        by (unfold dstate_ok; cbn [st_huf st_seq st_rep]; split; [destruct oh' as [hh|]; [exact Hoh' | exact I] | split; assumption]).
      rewrite (tp_fe nb (st_seq ts) os') by auto.
      sep_apply (tp_tabs_fold gv p ox oh' x2' os' rep' lxb' Hdok).
      Exists r3 oc' (Vint (Int.repr 0)) (Some (mk_tstate {| st_huf := oh'; st_seq := os'; st_rep := rep' |} x2' lxb')).
      unfold fs'. entailer!.
      split; [exact Hr3c |]. split; [reflexivity |]. split; [discriminate | split; [exact Hsb | exact Hbt]]. }
Qed.

(* The export as DecIface3 states it: the specification above (the history the matches copy is defined, a
   precondition since memcpy and memmove are libc.c's byte loops; a success gives defined bytes when an extDict
   in the output array is out of the block's way). *)
Lemma body_decompressBlock_internal :
  GLOBALS_obligation -> body_ok TOP3_G (ZSTD_decompressBlock_internal_spec3 dent_def tabs_def).
Proof. intros GL. exact (body_decompressBlock_internal_fixed GL). Qed.

Lemma TOP3_ok : GLOBALS_obligation -> TOP3_obligation.
Proof.
  intros GL. exists TOP3_S. split; [reflexivity |]. split.
  - intros x Hx. simpl in Hx |- *. tauto.
  - change ((G_BLK ++ TOP3_imports) ++ TOP3_S) with TOP3_G.
    repeat constructor.
    + apply body_totalHistorySize.
    + apply body_getOffsetInfo.
    + apply body_maxShortOffset.
    + apply body_decompressBlock_internal; auto.
Qed.
