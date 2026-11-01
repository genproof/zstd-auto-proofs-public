(* Sub-group LOOP of CORE: the three sequence loops, their _default
   wrappers (bmi2 = 0), the dispatchers, ZSTD_prefetchMatch.

   Exports the three dispatchers' seqs_spec (BlkIface: SEQ_exports); imports DEC (the FSE machine) and EXEC
   (the executors), on top of G_BLK and COPY_exports.  GLOBALS_obligation: the predefined tables (TGlob)
   are split out of zstd_globals.  Internal specifications: CORE's (BlkSeqCORE.v). *)
Require Export Zstd.proof.dec.B.blk.BlkSeqDEC Zstd.proof.dec.B.blk.BlkSeqEXEC.
Require Import Zstd.proof.dec.B.BCompose.
Require Import Zstd.proof.dec.B.blk.BlkSeqLoopShort Zstd.proof.dec.B.blk.BlkSeqLoopSplit Zstd.proof.dec.B.blk.BlkSeqLoopLong.
Local Open Scope logic.

(* ZSTD_prefetchMatch(prefetchPos, &seq, prefixStart, dictEnd): no memory effect (PREFETCH_L1 is empty;
   the address is formed only from a non-NULL base, which the comparison `matchBase != NULL` needs weakly
   valid: W are the arrays the caller lends to show it, Spec_xxh.ptr_witness / Spec_api6.pws_pred;
   a WITH of type mpred is a universe inconsistency); returns prefetchPos + ll + ml (size_t). *)
Definition ZSTD_prefetchMatch_spec : ident * funspec :=
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

(* the loops and their _default wrappers: the dispatchers' seqs_spec (BlkIface), for the literal places each
   handles (the short loop: not split; the split-literal loop: split; the long loop: any) *)
Definition ZSTD_decompressSequences_body_spec : ident * funspec :=
  DECLARE _ZSTD_decompressSequences_body seqs_spec not_split.
Definition ZSTD_decompressSequences_default_spec : ident * funspec :=
  DECLARE _ZSTD_decompressSequences_default seqs_spec not_split.
Definition ZSTD_decompressSequences_bodySplitLitBuffer_spec : ident * funspec :=
  DECLARE _ZSTD_decompressSequences_bodySplitLitBuffer seqs_spec is_split.
Definition ZSTD_decompressSequencesSplitLitBuffer_default_spec : ident * funspec :=
  DECLARE _ZSTD_decompressSequencesSplitLitBuffer_default seqs_spec is_split.
Definition ZSTD_decompressSequencesLong_body_spec : ident * funspec :=
  DECLARE _ZSTD_decompressSequencesLong_body seqs_spec (fun _ => True).
Definition ZSTD_decompressSequencesLong_default_spec : ident * funspec :=
  DECLARE _ZSTD_decompressSequencesLong_default seqs_spec (fun _ => True).

Definition LOOP_ids : list ident :=
  [ _ZSTD_decompressSequences_bodySplitLitBuffer; _ZSTD_decompressSequences_body;
    _ZSTD_decompressSequences_default; _ZSTD_decompressSequencesSplitLitBuffer_default; _ZSTD_prefetchMatch;
    _ZSTD_decompressSequencesLong_body; _ZSTD_decompressSequencesLong_default;
    _ZSTD_decompressSequences; _ZSTD_decompressSequencesSplitLitBuffer; _ZSTD_decompressSequencesLong ].
Definition LOOP_exports : funspecs := SEQ_exports.
Definition LOOP_imports : funspecs := DEC_exports ++ EXEC_exports.
Definition LOOP_obligation : Prop :=
  subtree_ok LOOP_ids LOOP_exports ((G_BLK ++ COPY_exports) ++ LOOP_imports).

(* the specifications of the ten functions, in LOOP_ids order, and the context of their bodies *)
Definition LOOP_S : funspecs :=
  [ ZSTD_decompressSequences_bodySplitLitBuffer_spec; ZSTD_decompressSequences_body_spec;
    ZSTD_decompressSequences_default_spec; ZSTD_decompressSequencesSplitLitBuffer_default_spec;
    ZSTD_prefetchMatch_spec; ZSTD_decompressSequencesLong_body_spec; ZSTD_decompressSequencesLong_default_spec;
    ZSTD_decompressSequences_spec; ZSTD_decompressSequencesSplitLitBuffer_spec; ZSTD_decompressSequencesLong_spec ].
Definition LOOP_G : funspecs := ((G_BLK ++ COPY_exports) ++ LOOP_imports) ++ LOOP_S.

Lemma loop_tc_null (P R: mpred) (p: val) :
  isptr p -> (R |-- weak_valid_pointer p) -> P * R |-- denote_tc_test_eq p (Vlong (Int64.repr 0)).
Proof.
  intros Hp HR. destruct p; try contradiction.
  change (denote_tc_test_eq (Vptr b i) (Vlong (Int64.repr 0))) with
    (!! (Int64.repr 0 = Int64.zero) && weak_valid_pointer (Vptr b i)).
  apply andp_right; [apply prop_right; reflexivity |].
  eapply derives_trans; [apply sepcon_derives; [apply derives_refl | exact HR] |].
  apply sepcon_weak_valid_pointer2, derives_refl.
Qed.

Lemma body_ZSTD_prefetchMatch : semax_body Vprog LOOP_G f_ZSTD_prefetchMatch ZSTD_prefetchMatch_spec.
Proof.
  start_function.
  forward_call (shq, sp, ll, ml, off, Tsh, v_sequence).
  unfold seqrep. forward. forward. forward.
  set (pp := Int64.add (Int64.repr pos) (Int64.repr ll)).
  set (sq := (Vlong (Int64.repr ll), (Vlong (Int64.repr ml), Vlong (Int64.repr off)))).
  forward_if (EX mb: val,
    PROP (mb = pS \/ mb = dE)
    LOCAL (temp _t'1 mb; temp _prefetchPos (Vlong pp); lvar _sequence (Tstruct ___gp_seq_t noattr) v_sequence;
           temp _gp_sequence sp; temp _prefixStart pS; temp _dictEnd dE)
    SEP (data_at shq t_seq sq sp; data_at Tsh t_seq sq v_sequence; pws_pred W))%assert.
  { forward. Exists dE. entailer!. }
  { forward. Exists pS. entailer!. }
  Intros mb. forward.
  forward_if (PROP ()
    LOCAL (temp _prefetchPos (Vlong pp); lvar _sequence (Tstruct ___gp_seq_t noattr) v_sequence)
    SEP (data_at shq t_seq sq sp; data_at Tsh t_seq sq v_sequence; pws_pred W)).
  { destruct H6 as [-> | ->].
    - entailer!. apply loop_tc_null; auto.
    - destruct H5 as [-> | [Hp Hw]]; entailer!. apply loop_tc_null; auto. }
  { assert (Hmb: isptr mb).
    { destruct H6 as [-> | ->]; [exact H3 |]. destruct H5 as [-> | [Hp _]]; [|exact Hp].
      exfalso. apply H7. reflexivity. }
    forward_call (mb, Int64.signed pp).
    { rewrite Int64.repr_signed. entailer!. }
    forward. forward_call (offset_val (Int64.signed pp) mb, Int64.signed (Int64.repr off)).
    { rewrite Int64.repr_signed. entailer!. }
    forward.
    lazymatch goal with |- semax _ ?P _ _ => forward_loop P break: P end.
    - apply ENTAIL_refl.
    - forward. apply ENTAIL_refl.
    - lazymatch goal with |- semax _ ?P _ _ => forward_loop P break: P end.
      + apply ENTAIL_refl.
      + forward_call (offset_val (- Int64.signed (Int64.repr off)) (offset_val (Int64.signed pp) mb), 64).
        forward. first [apply ENTAIL_refl | entailer!].
      + entailer!. }
  { forward. entailer!. }
  unfold sq, pp. forward. forward. entailer!.
Qed.

Lemma body_ZSTD_decompressSequences_default :
  semax_body Vprog LOOP_G f_ZSTD_decompressSequences_default ZSTD_decompressSequences_default_spec.
Proof.
  start_function. forward_call (gv, p, fs, ox, os, fe, rep, l, lits, lxb, nbSeq, bsm, W, o, i, h).
  Intros vret. destruct vret as [[r oc'] rep']; cbn [fst snd] in *. forward. Exists r oc' rep'. entailer!.
Qed.

Lemma body_ZSTD_decompressSequencesSplitLitBuffer_default :
  semax_body Vprog LOOP_G f_ZSTD_decompressSequencesSplitLitBuffer_default
    ZSTD_decompressSequencesSplitLitBuffer_default_spec.
Proof.
  start_function. forward_call (gv, p, fs, ox, os, fe, rep, l, lits, lxb, nbSeq, bsm, W, o, i, h).
  Intros vret. destruct vret as [[r oc'] rep']; cbn [fst snd] in *. forward. Exists r oc' rep'. entailer!.
Qed.

Lemma body_ZSTD_decompressSequencesLong_default :
  semax_body Vprog LOOP_G f_ZSTD_decompressSequencesLong_default ZSTD_decompressSequencesLong_default_spec.
Proof.
  start_function. forward_call (gv, p, fs, ox, os, fe, rep, l, lits, lxb, nbSeq, bsm, W, o, i, h).
  Intros vret. destruct vret as [[r oc'] rep']; cbn [fst snd] in *. forward. Exists r oc' rep'. entailer!.
Qed.

Lemma body_ZSTD_decompressSequences :
  semax_body Vprog LOOP_G f_ZSTD_decompressSequences ZSTD_decompressSequences_spec.
Proof.
  start_function.
  lazymatch goal with |- semax _ ?P _ _ => forward_loop P break: P end.
  - apply ENTAIL_refl.
  - forward. apply ENTAIL_refl.
  - forward_if; [exfalso; congruence|].
    forward_call (gv, p, fs, ox, os, fe, rep, l, lits, lxb, nbSeq, bsm, W, o, i, h).
    Intros vret. destruct vret as [[r oc'] rep']; cbn [fst snd] in *. forward. Exists r oc' rep'. entailer!.
Qed.

Lemma body_ZSTD_decompressSequencesSplitLitBuffer :
  semax_body Vprog LOOP_G f_ZSTD_decompressSequencesSplitLitBuffer ZSTD_decompressSequencesSplitLitBuffer_spec.
Proof.
  start_function.
  lazymatch goal with |- semax _ ?P _ _ => forward_loop P break: P end.
  - apply ENTAIL_refl.
  - forward. apply ENTAIL_refl.
  - forward_if; [exfalso; congruence|].
    forward_call (gv, p, fs, ox, os, fe, rep, l, lits, lxb, nbSeq, bsm, W, o, i, h).
    Intros vret. destruct vret as [[r oc'] rep']; cbn [fst snd] in *. forward. Exists r oc' rep'. entailer!.
Qed.

Lemma body_ZSTD_decompressSequencesLong :
  semax_body Vprog LOOP_G f_ZSTD_decompressSequencesLong ZSTD_decompressSequencesLong_spec.
Proof.
  start_function.
  lazymatch goal with |- semax _ ?P _ _ => forward_loop P break: P end.
  - apply ENTAIL_refl.
  - forward. apply ENTAIL_refl.
  - forward_if; [exfalso; congruence|].
    forward_call (gv, p, fs, ox, os, fe, rep, l, lits, lxb, nbSeq, bsm, W, o, i, h).
    Intros vret. destruct vret as [[r oc'] rep']; cbn [fst snd] in *. forward. Exists r oc' rep'. entailer!.
Qed.

Ltac loop_in_spec := solve [repeat (first [left; reflexivity | right])].

Lemma LOOP_GB_incl : incl LOOP_GB LOOP_G.
Proof.
  unfold LOOP_GB, LOOP_G, LOOP_imports. rewrite <- !app_assoc.
  apply incl_app; [apply incl_appl, incl_refl|]. apply incl_appr.
  apply incl_app; [apply incl_appl, incl_refl|]. apply incl_appr.
  apply incl_app; [apply incl_appl, incl_refl|]. apply incl_appr.
  apply incl_app; [apply incl_appl, incl_refl|]. apply incl_appr.
  intros x [<-|[]]. unfold LOOP_S. loop_in_spec.
Qed.

Lemma LOOP_G_nodup : NoDup (map fst Vprog ++ map fst LOOP_G).
Proof. apply nodupb_ok. vm_compute. reflexivity. Qed.

Lemma loop_lift (ix: ident * funspec) (f: function) :
  zstd_fun (fst ix) f -> fn_callconv f = callingconvention_of_funspec (snd ix) ->
  semax_body Vprog LOOP_GB f ix -> body_ok LOOP_G ix.
Proof.
  intros Hf Hc Hb. apply body_ok_mono with LOOP_GB; [exists f; auto | exact LOOP_GB_incl | exact LOOP_G_nodup].
Qed.

Lemma LOOP_ok : GLOBALS_obligation -> LOOP_obligation.
Proof.
  intro HG. unfold LOOP_obligation, subtree_ok.
  exists LOOP_S. split; [reflexivity | split].
  { unfold LOOP_exports, SEQ_exports, LOOP_S. intros x Hx.
    repeat (destruct Hx as [<-|Hx]; [loop_in_spec|]); contradiction. }
  fold LOOP_G. repeat apply Forall_cons; try apply Forall_nil.
  - apply loop_lift with f_ZSTD_decompressSequences_bodySplitLitBuffer; [reflexivity | reflexivity |].
    exact (body_ZSTD_decompressSequences_bodySplitLitBuffer HG).
  - apply loop_lift with f_ZSTD_decompressSequences_body; [reflexivity | reflexivity |].
    exact (body_ZSTD_decompressSequences_body HG).
  - exists f_ZSTD_decompressSequences_default.
    split; [reflexivity | split; [reflexivity | apply body_ZSTD_decompressSequences_default]].
  - exists f_ZSTD_decompressSequencesSplitLitBuffer_default.
    split; [reflexivity | split; [reflexivity | apply body_ZSTD_decompressSequencesSplitLitBuffer_default]].
  - exists f_ZSTD_prefetchMatch. split; [reflexivity | split; [reflexivity | apply body_ZSTD_prefetchMatch]].
  - apply loop_lift with f_ZSTD_decompressSequencesLong_body; [reflexivity | reflexivity |].
    exact (body_ZSTD_decompressSequencesLong_body HG).
  - exists f_ZSTD_decompressSequencesLong_default.
    split; [reflexivity | split; [reflexivity | apply body_ZSTD_decompressSequencesLong_default]].
  - exists f_ZSTD_decompressSequences.
    split; [reflexivity | split; [reflexivity | apply body_ZSTD_decompressSequences]].
  - exists f_ZSTD_decompressSequencesSplitLitBuffer.
    split; [reflexivity | split; [reflexivity | apply body_ZSTD_decompressSequencesSplitLitBuffer]].
  - exists f_ZSTD_decompressSequencesLong.
    split; [reflexivity | split; [reflexivity | apply body_ZSTD_decompressSequencesLong]].
Qed.
