(* FS3 streaming, case zdss_loadHeader, piece C: the split of lh_C into
   s7 (stable check), s9 (Begin_usingDDict(getDDict)), s10 (skippable / ZSTD_decodeFrameHeader), s12 (windowSize),
   s13 (maxWindowSize), the states between them and the statements of the segments. *)
Require Export Zstd.proof.dec.v3.FS.stream.lh.LH3Stmts.
Local Open Scope logic.

Section CM_LH3C_lib_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* ---------- the statements of lh_C ---------- *)

Definition lhC_s7 : statement := ltac:(
  let t := eval cbv delta [lh_C] in lh_C in let x := lh_take 1%nat t in exact x).
Definition lhC_s9 : statement := ltac:(
  let t := eval cbv delta [lh_C] in lh_C in let r := lh_drop 2%nat t in let x := lh_take 1%nat r in exact x).
Definition lhC_s10 : statement := ltac:(
  let t := eval cbv delta [lh_C] in lh_C in let r := lh_drop 3%nat t in let x := lh_take 1%nat r in exact x).
Definition lhC_s12 : statement := ltac:(
  let t := eval cbv delta [lh_C] in lh_C in let r := lh_drop 5%nat t in let x := lh_take 1%nat r in exact x).
Definition lhC_s13 : statement := ltac:(
  let t := eval cbv delta [lh_C] in lh_C in let r := lh_drop 6%nat t in exact r).

Lemma lh_C_split : lh_C = Ssequence lhC_s7 (Ssequence (Sloop Sskip Sbreak) (Ssequence lhC_s9
  (Ssequence lhC_s10 (Ssequence (Sloop Sskip Sbreak) (Ssequence lhC_s12 lhC_s13))))).
Proof. reflexivity. Qed.

(* do { } while (0) *)
Lemma semax_dowhile0 : forall {CS: compspecs} {Espec: OracleKind} Delta P c R,
  semax Delta P c R -> semax Delta P (Ssequence (Sloop Sskip Sbreak) c) R.
Proof.
intros CS Espec Delta P c R H.
apply semax_seq with P; [| exact H].
destruct R as [Rn Rb Rc Rr]; simpl.
apply semax_loop with (Q' := P).
- eapply semax_post_flipped; [apply semax_skip | ..]; simpl; intros; try apply andp_left2; auto;
    try apply FF_left.
- eapply semax_pre; [| apply semax_break]. simpl. intros; apply andp_left2; auto.
Qed.

(* ---------- the contexts between the segments ---------- *)

(* the context after Begin_usingDDict with the DDict dd (frame fields fs): tables in dd (litExtraBuffer holding
   lxb), dictionary fields getDDict's (which may have freed the local DDict: the stream fields' held bytes follow) *)
Definition lhC_kx (k1: cst3) (fs: fstate) (dd: option (ddx * val)) (lxb: list Z) : cst3 :=
  {| c3_fs := fs;
     c3_tabs := TInit (dd_ox dd) (lh_dd_ts dd lxb);
     c3_stable := c3_stable k1; c3_dict := snd (getddict_res (c3_dict k1));
     c3_s := held_redict (c3_s k1) (c3_dict k1) (snd (getddict_res (c3_dict k1)));
     c3_par := c3_par k1; c3_sp := c3_sp k1; c3_set := c3_set k1 |}.

Lemma lhC_k_kx (k1: cst3) (hb: list Z) (h: frame_header) (c: lhc) :
  lhC_k k1 hb h c = lhC_kx k1 (lhC_fs k1 hb h c) (lc_dd c) (lc_lxb c).
Proof. reflexivity. Qed.

(* lhC_fs before windowSize = MAX(windowSize, 1 KiB): fParams = the header's *)
Definition lhC_fs0 (k1: cst3) (hb: list Z) (h: frame_header) (c: lhc) : fstate :=
  let fsB := lh_dd_fs (c3_fs k1) (dp_fmt (c3_par k1)) (lc_dd c) (lc_cold c) in
  if fh_frameType h =? 1 then
    fsu_fParams (fsu_stage (fsu_expected fsB (vlong (le_field hb 4 4))) (Vint (Int.repr ds_skipFrame))) (fh_val h)
  else
    let vck := andb (fh_checksumFlag h =? 1) (negb (dp_ignore (c3_par k1) =? 1)) in
    fsu_fParams
      (fsu_stage
         (fsu_expected
            (fsu_processedCSize
               (fsu_xxh (fsu_validateChecksum (fsu_dictID (fsu_fParams fsB (fh_val h)) (Vint (Int.repr (lc_did c))))
                           (Vint (Int.repr (if vck then 1 else 0))))
                  (if vck then Some nil else fs_xxh fsB))
               (Vlong (Int64.repr (Zlength hb))))
            (vlong ZSTD_blockHeaderSize))
         (Vint (Int.repr ds_decodeBlockHeader)))
      (fh_val h).

Lemma lhC_fs_eq (k1: cst3) (hb: list Z) (h: frame_header) (c: lhc) :
  lhC_fs k1 hb h c = fsu_fParams (lhC_fs0 k1 hb h c) (fh_val (fh_adj h (fh_blockSizeMax h))).
Proof. unfold lhC_fs, lhC_fs0. destruct (fh_frameType h =? 1); reflexivity. Qed.

(* the stable buffer is too small for the frame's content *)
Definition lhC_small (a: dsa) (w: lw) (k1: cst3) (h: frame_header) : bool :=
  andb (andb (andb (c3_stable k1) (negb (fh_frameType h =? 1)))
    (negb (fh_contentSize h =? ZSTD_CONTENTSIZE_UNKNOWN))) (a_osz a - w_opc w <? fh_contentSize h).

(* the facts piece C starts from *)
Definition lhC_hyps (DENT: dent_pred) (TABS: tabs_pred) (a: dsa) (w: lw) (hb: list Z) (h: frame_header)
    (tbl: list val) (d1: dfields) (did1: val) : Prop :=
  lend_sel_ok /\ lend_begin_ok /\ hs_probe_ok /\
  DENT_OK DENT /\ TABS_OK TABS /\ dsa_ok a /\ lh_entry a w hb /\ lh_sel_pre a w /\
  get_frame_header_m (lh_mg (w_k w)) hb = FH_ok h /\ gfh3_facts (lh_mg (w_k w)) hb h /\
  lhA_sel (w_k w) hb 0 (fh_val h) tbl d1 did1.

Section States.
Variable DENT : dent_pred.
Variable TABS : tabs_pred.

(* after s7: the stable-buffer check passed *)
Definition lhC_S1 (a: dsa) (w: lw) (k1: cst3) (h: frame_header) (tbl: list val) : environ -> mpred :=
  PROPx [lhC_small a w k1 h = false]
  (LOCALx (ds_LI_L a (lw_k w k1)) (SEPx (ds_LI_St DENT TABS a (lw_k w k1) tbl))).

(* after s9: ZSTD_decompressBegin_usingDDict(zds, ZSTD_getDDict(zds)) with the DDict dd, ddictIsCold cold,
   litExtraBuffer holding lxb, the bytes it held before (Begin keeps them) *)
Definition lhC_S2 (a: dsa) (w: lw) (k1: cst3) (h: frame_header) (tbl: list val) : environ -> mpred :=
  EX dd: option (ddx * val), EX cold: val, EX lxb: list Z,
  PROPx [lxb = tabs_lxb (c3_tabs k1); lhC_small a w k1 h = false; lhC_dd a k1 dd; cold = Vint (Int.repr 0) \/ cold = Vint (Int.repr 1)]
  (LOCALx (ds_LI_L a (lw_k w k1))
  (SEPx (ds_LI_St DENT TABS a (lw_k w (lhC_kx k1 (lh_dd_fs (c3_fs k1) (dp_fmt (c3_par k1)) dd cold) dd lxb)) tbl))).

(* the facts of piece C's choice c known after s10 (litExtraBuffer: the bytes before piece C) *)
Definition lhC_cfacts (a: dsa) (w: lw) (k1: cst3) (h: frame_header) (c: lhc) : Prop :=
  lhC_small a w k1 h = false /\ lhC_dd a k1 (lc_dd c) /\
  (lc_cold c = Vint (Int.repr 0) \/ lc_cold c = Vint (Int.repr 1)) /\
  0 <= lc_did c <= Int.max_unsigned /\
  (fh_frameType h <> 1 -> fh_dictID h = 0 \/ fh_dictID h = lc_did c) /\
  (lc_dd c = None -> lc_did c = 0) /\
  lc_lxb c = tabs_lxb (c3_tabs k1).

(* after s10: the skippable frame, or ZSTD_decodeFrameHeader succeeded *)
Definition lhC_S3 (a: dsa) (w: lw) (k1: cst3) (hb: list Z) (h: frame_header) (tbl: list val) : environ -> mpred :=
  EX c: lhc,
  PROPx [lhC_cfacts a w k1 h c]
  (LOCALx (ds_LI_L a (lw_k w k1))
  (SEPx (ds_LI_St DENT TABS a (lw_k w (lhC_kx k1 (lhC_fs0 k1 hb h c) (lc_dd c) (lc_lxb c))) tbl))).

(* after s12: windowSize = MAX(windowSize, 1 KiB) *)
Definition lhC_S4 (a: dsa) (w: lw) (k1: cst3) (hb: list Z) (h: frame_header) (tbl: list val) : environ -> mpred :=
  EX c: lhc,
  PROPx [lhC_cfacts a w k1 h c]
  (LOCALx (ds_LI_L a (lw_k w k1))
  (SEPx (ds_LI_St DENT TABS a (lw_k w (lhC_k k1 hb h c)) tbl))).

End States.

(* piece C's post with, at the normal exit, litExtraBuffer kept through ZSTD_decompressBegin_usingDDict (the
   exact claim's LH3XDefs.lhC_x) *)
Definition lhC_post_l (DENT: dent_pred) (TABS: tabs_pred) (a: dsa) (w: lw) (hb: list Z) (h: frame_header)
    (k1: cst3) : ret_assert :=
  {| RA_normal := EX c: lhc,
       PROPx [lhC_facts a w k1 h c; lc_lxb c = tabs_lxb (c3_tabs k1)]
       (LOCALx (ds_LI_L a (lw_k w (lhC_k k1 hb h c))) (SEPx (ds_LI_S DENT TABS a (lw_k w (lhC_k k1 hb h c)))));
     RA_break := FF;
     RA_continue := FF;
     RA_return := lh_ret DENT TABS a w hb |}.

(* lhC_stmt with that post *)
Definition lhC_l_stmt : Prop :=
  lend_sel_ok -> lend_begin_ok -> hs_probe_ok ->
  forall (Espec: OracleKind) DENT TABS BR (a: dsa) (w: lw) (hb: list Z) (h: frame_header) (tbl: list val)
         (d1: dfields) (did1: val),
    DENT_OK DENT -> TABS_OK TABS -> dsa_ok a -> lh_entry a w hb -> lh_sel_pre a w ->
    get_frame_header_m (lh_mg (w_k w)) hb = FH_ok h -> gfh3_facts (lh_mg (w_k w)) hb h ->
    lhA_sel (w_k w) hb 0 (fh_val h) tbl d1 did1 ->
    let k1 := k_A (w_k w) (fh_val h) d1 did1 in
    semax (ds_Delta DENT TABS BR) (lh_stt DENT TABS a (lw_k w k1) tbl) lh_C (lhC_post_l DENT TABS a w hb h k1).

(* ---------- the segments ---------- *)

Definition lhC_seg7_stmt : Prop :=
  forall (Espec: OracleKind) DENT TABS BR (a: dsa) (w: lw) (hb: list Z) (h: frame_header) (tbl: list val)
         (d1: dfields) (did1: val),
    lhC_hyps DENT TABS a w hb h tbl d1 did1 ->
    let k1 := k_A (w_k w) (fh_val h) d1 did1 in
    semax (ds_Delta DENT TABS BR) (lh_stt DENT TABS a (lw_k w k1) tbl) lhC_s7
      (overridePost (lhC_S1 DENT TABS a w k1 h tbl) (lhC_post DENT TABS a w hb h k1)).

Definition lhC_seg9_stmt : Prop :=
  forall (Espec: OracleKind) DENT TABS BR (a: dsa) (w: lw) (hb: list Z) (h: frame_header) (tbl: list val)
         (d1: dfields) (did1: val),
    lhC_hyps DENT TABS a w hb h tbl d1 did1 ->
    let k1 := k_A (w_k w) (fh_val h) d1 did1 in
    semax (ds_Delta DENT TABS BR) (lhC_S1 DENT TABS a w k1 h tbl) lhC_s9
      (overridePost (lhC_S2 DENT TABS a w k1 h tbl) (lhC_post DENT TABS a w hb h k1)).

Definition lhC_seg10_stmt : Prop :=
  forall (Espec: OracleKind) DENT TABS BR (a: dsa) (w: lw) (hb: list Z) (h: frame_header) (tbl: list val)
         (d1: dfields) (did1: val),
    lhC_hyps DENT TABS a w hb h tbl d1 did1 ->
    let k1 := k_A (w_k w) (fh_val h) d1 did1 in
    semax (ds_Delta DENT TABS BR) (lhC_S2 DENT TABS a w k1 h tbl) lhC_s10
      (overridePost (lhC_S3 DENT TABS a w k1 hb h tbl) (lhC_post DENT TABS a w hb h k1)).

Definition lhC_seg12_stmt : Prop :=
  forall (Espec: OracleKind) DENT TABS BR (a: dsa) (w: lw) (hb: list Z) (h: frame_header) (tbl: list val)
         (d1: dfields) (did1: val),
    lhC_hyps DENT TABS a w hb h tbl d1 did1 ->
    let k1 := k_A (w_k w) (fh_val h) d1 did1 in
    semax (ds_Delta DENT TABS BR) (lhC_S3 DENT TABS a w k1 hb h tbl) lhC_s12
      (overridePost (lhC_S4 DENT TABS a w k1 hb h tbl) (lhC_post DENT TABS a w hb h k1)).

Definition lhC_seg13_stmt : Prop :=
  forall (Espec: OracleKind) DENT TABS BR (a: dsa) (w: lw) (hb: list Z) (h: frame_header) (tbl: list val)
         (d1: dfields) (did1: val),
    lhC_hyps DENT TABS a w hb h tbl d1 did1 ->
    let k1 := k_A (w_k w) (fh_val h) d1 did1 in
    semax (ds_Delta DENT TABS BR) (lhC_S4 DENT TABS a w k1 hb h tbl) lhC_s13 (lhC_post_l DENT TABS a w hb h k1).

Lemma lhC_compose : lhC_seg7_stmt -> lhC_seg9_stmt -> lhC_seg10_stmt -> lhC_seg12_stmt -> lhC_seg13_stmt ->
  lhC_l_stmt.
Proof.
intros H7 H9 H10 H12 H13.
unfold lhC_l_stmt. intros Hsel Hbeg Hpr Espec DENT TABS BR a w hb h tbl d1 did1 HD HT Ha He Hs Hg Hf HA.
set (k1 := k_A (w_k w) (fh_val h) d1 did1).
assert (HP: lhC_hyps DENT TABS a w hb h tbl d1 did1) 
  by exact (conj Hsel (conj Hbeg (conj Hpr (conj HD (conj HT (conj Ha (conj He (conj Hs (conj Hg (conj Hf HA)))))))))).
rewrite lh_C_split.
apply semax_seq with (lhC_S1 DENT TABS a w k1 h tbl); [apply H7; exact HP |].
apply semax_dowhile0.
apply semax_seq with (lhC_S2 DENT TABS a w k1 h tbl); [apply H9; exact HP |].
apply semax_seq with (lhC_S3 DENT TABS a w k1 hb h tbl); [apply H10; exact HP |].
apply semax_dowhile0.
apply semax_seq with (lhC_S4 DENT TABS a w k1 hb h tbl); [apply H12; exact HP |].
apply H13; exact HP.
Qed.

End CM_LH3C_lib_1.
