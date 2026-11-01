(* FS3 streaming, case zdss_loadHeader: the obligations of the
   pieces (A..D, the glue from their posts to the loop invariant / read's precondition, the returns)
   and the GAPS (statements the fixed specifications did not give at first). *)
Require Export Zstd.proof.dec.v3.FS.stream.lh.LH3Defs.
Require Export Zstd.proof.dec.v3.FS.stream.S3ModelStmts.
Local Open Scope logic.

Section CM_LH3Stmts_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* the facts at the entry of case 1 *)
Definition lh_ctx (a: dsa) (w: lw) (hb: list Z) : Prop :=
  dsa_ok a /\ start_ok a /\ call_inv a (w_k w) (w_sv w) (w_ipc w) (w_opc w) (w_oc w) (w_dl w) /\ w_smw w = 1 /\
  loop_extra w /\ lh_entry a w hb /\ sv_fp (w_sv w) = FP_hdr hb /\ w_dl w = nil /\ sv_ahead (w_sv w) = nil /\
  sv_pend (w_sv w) = nil /\ entry_ok a w /\ untouched_ok a w.

(* what ZSTD_DCtx_selectFrameDDict needs at the entry (selection on): fParams' dictID is an int, and without a
   dictionary the context's DDict pointer is NULL or the local one *)
Definition lh_sel_pre (a: dsa) (w: lw) : Prop :=
  let k := w_k w in
  sel_on (c3_par k) (c3_sp k) = true ->
  fp_id_ok (fs_fParams (c3_fs k)) /\
  (dc_dict (a_st a) = None -> df_ddict (c3_dict k) = nullval \/ df_ddict (c3_dict k) = df_local (c3_dict k) \/
     In (df_ddict (c3_dict k)) (map fst (dc_set (a_st a)))).

(* ---------- GAPS (false or unprovable today, true after the fixes) ---------- *)

(* G-fherr (settled by API v3.4: fh_post_m's FH_err leaves the struct or clears its dictID): a header error keeps
   fParams' dictID an int (lh_fherr_ok) *)
Definition GAP_fherr : Prop :=
  forall mg s r v0 v, fh_post_m mg s r v0 v -> get_frame_header_m mg s = FH_err -> fp_id_ok v0 -> fp_id_ok v.

Lemma lh_fherr_ok : GAP_fherr.
Proof.
intros mg s r v0 v Hp He Hv0. unfold fh_post_m in Hp. rewrite He in Hp.
destruct Hp as (_ & _ & [-> | E]); [ exact Hv0 | ].
exists 0. split; [ exact E | rep_lia ].
Qed.


(* G-cap0: usingDDict_int_spec3's darg_ok3 asks a strictly valid dst for a by-reference (0-byte) DDict even at
   capacity 0, where zstd compares nothing (checkContinuity tests n > 0 first) *)
(* G-dd-bytes (settled by stream R2: FSRep3.dict_rel3_of's DSDDict case has dr_bytes dr = dd_bytes dd,
   and without a set dict_rel3 is dict_rel3_of): lh_dd_bytes_ok *)
Definition GAP_dd_bytes : Prop := forall a w hb, lh_ctx a w hb -> dd_bytes_ok (a_st a).

Lemma lh_dd_bytes_ok : GAP_dd_bytes.
Proof.
intros a w hb Hc Hnil dr q dd Ed Es.
destruct Hc as (_ & _ & _ & _ & _ & He & _).
destruct He as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hbc & _).
destruct Hbc as (_ & _ & _ & Hrel & _).
destruct Hrel as [Hr | [Hne _]]; [ | contradiction ].
unfold dict_rel3_of in Hr. rewrite Ed in Hr. cbv zeta in Hr. rewrite Es in Hr. tauto.
Qed.

(* the header bytes read from the current input are its bytes (the shortcut's frame starts with them) *)
Definition lh_hb_in (a: dsa) (w: lw) (hb: list Z) : Prop :=
  w_ipc w - a_ipos a = Zlength hb -> hb = sublist (a_ipos a) (w_ipc w) (a_ibs a).

Lemma lh_hb_in_of : forall a w hb, lh_ctx a w hb -> lh_hb_in a w hb.
Proof.
  intros a w hb Hc Hl.
  destruct Hc as (Ha & _ & Hci & _ & _ & He & Hfp & _).
  assert (Hst: sf_stage (c3_s (w_k w)) = zdss_loadHeader) by (unfold lh_entry in He; tauto).
  assert (Hip: a_ipos a <= w_ipc w <= a_isz a) by (unfold lh_entry in He; tauto).
  assert (Hip0: 0 <= a_ipos a /\ Zlength (a_ibs a) = a_isz a) by (unfold dsa_ok in Ha; tauto).
  destruct Hci as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlast & _).
  destruct (Hlast Hst hb Hfp) as (pre & j & Hj & Hhb & ->).
  destruct pre as [ | p pre ].
  - rewrite app_nil_l in Hhb. exact Hhb.
  - exfalso.
    rewrite Hhb, Zlength_app, Zlength_sublist, Zlength_cons in Hl by lia.
    pose proof (Zlength_nonneg pre). lia.
Qed.

(* ---------- the pieces (C level) ---------- *)

Definition lhA_stmt : Prop :=
  lend_sel_ok -> GAP_fherr ->
  forall (Espec: OracleKind) DENT TABS BR (a: dsa) (w: lw) (hb: list Z),
    DENT_OK DENT -> TABS_OK TABS -> dsa_ok a -> lh_entry a w hb -> lh_sel_pre a w ->
    semax (ds_Delta DENT TABS BR) (lh_st DENT TABS a w) lh_A (lhA_post DENT TABS a w hb).

(* the shortcut (selection on or off) *)
Definition lhB_stmt : Prop :=
  MF3 -> lend_use_ok -> hs_probe_ok ->
  forall (Espec: OracleKind) DENT TABS BR (a: dsa) (w: lw) (hb: list Z) (h: frame_header) (tbl: list val)
         (d1: dfields) (did1: val),
    DENT_OK DENT -> TABS_OK TABS -> dsa_ok a -> lh_entry a w hb -> dd_bytes_ok (a_st a) -> lh_hb_in a w hb ->
    get_frame_header_m (lh_mg (w_k w)) hb = FH_ok h -> gfh3_facts (lh_mg (w_k w)) hb h ->
    lhA_sel (w_k w) hb 0 (fh_val h) tbl d1 did1 ->
    let k1 := k_A (w_k w) (fh_val h) d1 did1 in
    semax (ds_Delta DENT TABS BR) (lh_stt DENT TABS a (lw_k w k1) tbl) lh_B (lhB_post DENT TABS a w hb h k1 tbl).

Definition lhC_stmt : Prop :=
  lend_sel_ok -> lend_begin_ok -> hs_probe_ok ->
  forall (Espec: OracleKind) DENT TABS BR (a: dsa) (w: lw) (hb: list Z) (h: frame_header) (tbl: list val)
         (d1: dfields) (did1: val),
    DENT_OK DENT -> TABS_OK TABS -> dsa_ok a -> lh_entry a w hb -> lh_sel_pre a w ->
    get_frame_header_m (lh_mg (w_k w)) hb = FH_ok h -> gfh3_facts (lh_mg (w_k w)) hb h ->
    lhA_sel (w_k w) hb 0 (fh_val h) tbl d1 did1 ->
    let k1 := k_A (w_k w) (fh_val h) d1 did1 in
    semax (ds_Delta DENT TABS BR) (lh_stt DENT TABS a (lw_k w k1) tbl) lh_C (lhC_post DENT TABS a w hb h k1).

Definition lhD_stmt : Prop :=
  forall (Espec: OracleKind) DENT TABS BR (a: dsa) (w: lw) (hb: list Z) (h: frame_header) (tbl: list val)
         (d1: dfields) (did1: val) (c: lhc),
    DENT_OK DENT -> TABS_OK TABS -> dsa_ok a -> lh_entry a w hb ->
    get_frame_header_m (lh_mg (w_k w)) hb = FH_ok h -> gfh3_facts (lh_mg (w_k w)) hb h ->
    lhA_sel (w_k w) hb 0 (fh_val h) tbl d1 did1 ->
    let k1 := k_A (w_k w) (fh_val h) d1 did1 in
    lhC_facts a w k1 h c ->
    let k3 := lhC_k k1 hb h c in
    semax (ds_Delta DENT TABS BR) (lh_st DENT TABS a (lw_k w k3)) lh_D (lhD_post DENT TABS a w hb h k3).

(* ---------- facts of a parsed header ---------- *)

Definition gfh3_stmt : Prop :=
  forall mg hb h, get_frame_header_m mg hb = FH_ok h -> bytes_ok hb -> gfh3_facts mg hb h.

(* ---------- glue: the loop invariant around the pieces ---------- *)

(* G1: the break after a complete load of the header bytes *)
Definition lh_brkA_stmt : Prop :=
  MF3 -> hs_probe_ok ->
  forall DENT TABS (a: dsa) (w: lw) (hb: list Z) (kk: Z) (v: reptype t_fh) (tbl: list val) (d1: dfields) (did1: val),
    lh_ctx a w hb -> lhA_sel (w_k w) hb kk v tbl d1 did1 ->
    get_frame_header_m (lh_mg (w_k w)) hb = FH_more kk -> kk - Zlength hb <= a_isz a - w_ipc w ->
    lh_st DENT TABS a (lhA_brk a w (k_A (w_k w) v d1 did1) hb kk) |-- ds_inv DENT TABS a.

(* G2: the break after a successful shortcut *)
Definition lh_brkB_stmt : Prop :=
  MF3 -> hs_probe_ok -> GAP_dd_bytes ->
  forall DENT TABS (a: dsa) (w: lw) (hb: list Z) (h: frame_header) (tbl: list val) (d1: dfields) (did1: val)
         (cSize r: Z) (out: list val) (c: list Z) (fs': fstate) (d': dfields) (lxb': list Z),
    lh_ctx a w hb -> get_frame_header_m (lh_mg (w_k w)) hb = FH_ok h -> gfh3_facts (lh_mg (w_k w)) hb h ->
    lhA_sel (w_k w) hb 0 (fh_val h) tbl d1 did1 ->
    let k1 := k_A (w_k w) (fh_val h) d1 did1 in
    lhB_facts a w k1 hb h cSize r out -> is_error_code r = false ->
    bytes_ok c -> Zlength c = r -> sublist 0 r out = zbytes c -> lhB_dict k1 d' -> fp_ok (fs_fParams fs') ->
    lhB_sel_fp k1 tbl (sublist (a_ipos a) (a_ipos a + cSize) (a_ibs a)) fs' d' ->
    lhB_sw k1 tbl (sublist (a_ipos a) (a_ipos a + cSize) (a_ibs a)) d' ->
    sublist (w_opc w + r) (a_osz a) (sublist 0 (w_opc w) (w_oc w) ++ out) = sublist (w_opc w + r) (a_osz a) (w_oc w) ->
    lh_st DENT TABS a (lhB_brk w k1 fs' d' lxb' (a_ipos a + cSize) r out c) |-- ds_inv DENT TABS a.

(* G4: after piece D, zdss_read's precondition (seg_case 2's call_inv) *)
Definition lh_read_stmt : Prop :=
  MF3 -> hs_probe_ok -> GAP_dd_bytes ->
  forall DENT TABS (a: dsa) (w: lw) (hb: list Z) (h: frame_header) (tbl: list val) (d1: dfields) (did1: val)
         (c: lhc) (s3: sfields),
    lh_ctx a w hb -> get_frame_header_m (lh_mg (w_k w)) hb = FH_ok h -> gfh3_facts (lh_mg (w_k w)) hb h ->
    lhA_sel (w_k w) hb 0 (fh_val h) tbl d1 did1 ->
    let k1 := k_A (w_k w) (fh_val h) d1 did1 in
    lhC_facts a w k1 h c ->
    let k3 := lhC_k k1 hb h c in
    lhD_facts (c3_stable k3) (c3_s k3) s3 h (lh_bsm k3 h) ->
    let w3 := lw_k w (lhD_k k3 h s3) in
    lh_st DENT TABS a w3 |-- !! exists sv, call_inv a (w_k w3) sv (w_ipc w3) (w_opc w3) (w_oc w3) nil /\
      loop_extra {| w_smw := w_smw w3; w_k := w_k w3; w_sv := sv; w_ipc := w_ipc w3; w_opc := w_opc w3;
                    w_oc := w_oc w3; w_dl := nil |}.

(* ---------- the returns ---------- *)

(* returning r with input->pos = ipos' (output->pos unchanged) from the state w' *)
Definition lh_ret_goal (DENT: dent_pred) (TABS: tabs_pred) (BR: blrel) (a: dsa) (w': lw) (r ipos': Z) : Prop :=
  PROPx [] (LOCALx (ds_LI_L a w') (SEPx (ds_S_ip DENT TABS a w' ipos')))
    |-- RA_return (ds_R DENT TABS BR a) (Some (Vlong (Int64.repr r))).

(* the hint return (lh_rc's RC_hint) *)
Definition lh_rc_hint (a: dsa) (w: lw) (hb: list Z) (r ipos': Z) (w': lw) : Prop :=
  exists kk v tbl d1 did1 r' v',
    lhA_sel (w_k w) hb kk v tbl d1 did1 /\ get_frame_header_m (lh_mg (w_k w)) hb = FH_more kk /\
    a_isz a - w_ipc w < kk - Zlength hb /\
    fh_post_m (lh_mg (w_k w)) (hb ++ sublist (w_ipc w) (a_isz a) (a_ibs a)) r' v v' /\
    get_frame_header_m (lh_mg (w_k w)) (hb ++ sublist (w_ipc w) (a_isz a) (a_ibs a)) <> FH_err /\ fp_ok v' /\
    r = lh_hint (lh_mg (w_k w)) (hb ++ sublist (w_ipc w) (a_isz a) (a_ibs a)) kk /\ ipos' = a_isz a /\
    w' = lw_k w (lh_k_load a w (k_A (w_k w) v d1 did1) hb (a_isz a - w_ipc w) v').

(* every return; the hint's case is given (lh_hint_stmt) *)
Definition lh_ret_stmt : Prop :=
  MF3 -> RET3 -> hs_probe_ok -> GAP_dd_bytes ->
  forall DENT TABS BR (a: dsa) (w: lw) (hb: list Z) (r ipos': Z) (w': lw),
    TABS_OK TABS -> lh_ctx a w hb -> 0 <= r <= Int64.max_unsigned -> lh_rc a w hb r ipos' w' ->
    (lh_rc_hint a w hb r ipos' w' -> lh_ret_goal DENT TABS BR a w' r ipos') ->
    lh_ret_goal DENT TABS BR a w' r ipos'.

Definition lh_hint_stmt : Prop :=
  MF3 -> hs_probe_ok ->
  forall DENT TABS BR (a: dsa) (w: lw) (hb: list Z) (r ipos': Z) (w': lw),
    TABS_OK TABS -> lh_ctx a w hb -> 0 <= r <= Int64.max_unsigned -> lh_rc_hint a w hb r ipos' w' ->
    lh_ret_goal DENT TABS BR a w' r ipos'.

End CM_LH3Stmts_1.
