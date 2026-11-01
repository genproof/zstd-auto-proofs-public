(* ZSTD_decompressStream, case zdss_loadHeader with the exact claim (Spec_api6.stream_exact).  The relational pieces
   (LH3Stmts: pieces A..D, the glue G1/G2/G4, the returns) are the template; here is what their exact versions state
   in addition, so that every exit of the case rebuilds the loop invariant's exact conjunct (S3Main.ex_call) or
   reaches the full specification's postcondition (S3Main.ds_R_x):
   - lhx_entry: at the entry of the case, nothing delivered yet, and (from the configuration of a new context) the
     model's loop state (S3XKit.ex_loop) whose fields the context represents (S3XRel.zrel);
   - lh_xok / lh_ret_x: a return of the case is an error the model has too (S3Main.ex_err: model/ExStream.v's
     iteration fails, or the error is a memory allocation), or the hint (lh_rc_hint);
   - lhB_none: piece B's normal exit: the single-pass shortcut's conditions fail (zstd_decompress.c 2241-2246);
   - lhB_x: the shortcut's ZSTD_decompress_usingDDict is the model's one-shot decoding (FSSpecs3.os_match) and
     leaves litExtraBuffer as the frame's model does (the last PROP of usingDDict_int's post);
   - lhC_x: ZSTD_decompressBegin_usingDDict keeps litExtraBuffer (piece C's normal exit);
   - lhD_x: the buffers as ExStream.st_header_done sizes them (oversizedDuration, the sizes, a new zeroed buffer
     when one is too small or the buffers were oversized for too long). *)
Require Export Zstd.proof.dec.v3.FS.stream.lh.LH3Stmts.
Require Export Zstd.proof.dec.v3.FS.stream.S3XKit.
Require Import Zstd.proof.model.ExCall Zstd.proof.model.ExStreamFacts.
Require Zstd.proof.model.ExStream Zstd.proof.model.ExHuf Zstd.proof.model.ExBlock Zstd.proof.model.Exact.
Local Open Scope logic.

Section CM_LH3XDefs_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.

(* ---------- the entry ---------- *)

(* at the entry of case 1 (stage zdss_loadHeader, someMoreWork = 1): no byte delivered in this call, and from the
   configuration of a new context the model's loop is at a state zi the fields represent (S3XKit.ex_call_go gives it
   from either disjunct of ex_call) *)
Definition lhx_entry (a: dsa) (w: lw) : Prop :=
  w_dl w = nil /\
  (fresh_cfg (a_st a) ->
   exists z0 zi f, ex_loop a z0 zi f (w_ipc w - a_ipos a) (w_dl w) /\ zrel zi (w_sx w) (w_fs w) (w_tabs w)).

(* zbytes is injective on byte lists *)
Lemma lhx_zbytes_inj (a b: list Z) : bytes_ok a -> bytes_ok b -> zbytes a = zbytes b -> a = b.
Proof.
  revert b. induction a as [ | x a IH]; intros [ | y b] Ha Hb E; simpl in E; try discriminate; auto.
  assert (Hx: Vint (Int.repr x) = Vint (Int.repr y)) by congruence.
  assert (Ht: zbytes a = zbytes b) by congruence.
  inv Ha. inv Hb. f_equal; [| apply IH; auto].
  unfold is_byte in *.
  apply (f_equal (fun v => match v with Vint i => Int.unsigned i | _ => 0 end)) in Hx. simpl in Hx.
  rewrite !Int.unsigned_repr in Hx by rep_lia. auto.
Qed.

(* the model's state at the entry: stage zdss_loadHeader with the header bytes hb loaded so far, nothing delivered;
   the model's iteration from it is st_load_header (ExStreamFacts.one_iter_lh) *)
Lemma lhx_view (a: dsa) (w: lw) (hb: list Z) :
  lh_entry a w hb -> lhx_entry a w -> fresh_cfg (a_st a) ->
  exists z0 zi f, ex_loop a z0 zi f (w_ipc w - a_ipos a) nil /\ zrel zi (w_sx w) (w_fs w) (w_tabs w) /\
    ExStream.zs_stage XS zi = ExStream.ZDSS_loadHeader /\ ExStream.zs_hbuf XS zi = hb /\
    one_iter_x (a_xin a) (a_xroom a) zi (w_ipc w - a_ipos a) nil =
    ExStream.st_load_header XS (ExBlock.xst_begin ExHuf.xhuf) Exact.xblock xframe1 (a_xin a) (a_xroom a) zi
      (w_ipc w - a_ipos a) nil.
Proof.
  intros He (Hdl & Hx) Hf. destruct (Hx Hf) as (z0 & zi & f & Hl & Hz). rewrite Hdl in Hl.
  destruct He as (Hs & Hlh & Hl18 & Hbo & Hsub & _).
  assert (Hst: ExStream.zs_stage XS zi = ExStream.ZDSS_loadHeader).
  { destruct Hz as (E & _). unfold w_sx in E. cbn [sf_strip sf_stage] in E. rewrite Hs in E.
    unfold zdss_loadHeader, ExStream.ZDSS_loadHeader in *. lia. }
  pose proof Hz as Hz0.
  destruct Hz as (Hz1 & Hz2 & Hz3 & Hz4 & Hz5 & Hz6 & Hz7 & Hz8 & Hz9 & Hz10 & Hzl & Hzr).
  destruct (Hzl Hst) as (Ezl & Ez18 & Ezb & Ezs & _).
  unfold w_sx in Ezl, Ezs. cbn [sf_strip sf_lhSize sf_hbuf] in Ezl, Ezs.
  assert (Hlen: Zlength (ExStream.zs_hbuf XS zi) = Zlength hb).
  { rewrite Hlh in Ezl. unfold vlong in Ezl.
    apply (f_equal (fun v => match v with Vlong i => Int64.unsigned i | _ => 0 end)) in Ezl.
    pose proof (Zlength_nonneg hb). pose proof (Zlength_nonneg (ExStream.zs_hbuf XS zi)).
    cbv beta iota in Ezl. rewrite !Int64.unsigned_repr in Ezl by rep_lia. lia. }
  exists z0, zi, f. split; [exact Hl|]. split; [exact Hz0 |]. split; [exact Hst|]. split.
  - apply lhx_zbytes_inj; auto. rewrite <- Ezs, <- Hsub, Hlen. reflexivity.
  - unfold one_iter_x. apply one_iter_lh. exact Hst.
Qed.

(* ---------- the returns ---------- *)

(* a return of the case (lh_rc a w hb r ipos' w') is an error of the model's call too, or the hint *)
Definition lh_xok (a: dsa) (w: lw) (hb: list Z) (r ipos': Z) (w': lw) : Prop :=
  lhx_entry a w -> ex_err a r \/ lh_rc_hint a w hb r ipos' w'.

(* returning r: the relational facts (lh_ret) and the exact one *)
Definition lh_ret_goal_x (DENT: dent_pred) (TABS: tabs_pred) (BR: blrel) (a: dsa) (w': lw) (r ipos': Z) : Prop :=
  PROPx [] (LOCALx (ds_LI_L a w') (SEPx (ds_S_ip DENT TABS a w' ipos')))
    |-- RA_return (ds_R_x DENT TABS BR a) (Some (Vlong (Int64.repr r))).

(* ---------- piece B: the shortcut ---------- *)

(* the shortcut is not taken (zstd_decompress.c 2241-2246): the declared content size, a Zstandard frame, room for
   the content, the whole header in this call, the frame's compressed size within the input: one of them fails *)
Definition lhB_none (a: dsa) (w: lw) (hb: list Z) (h: frame_header) : Prop :=
  fh_contentSize h <> ZSTD_CONTENTSIZE_UNKNOWN -> fh_frameType h <> 1 -> fh_contentSize h <= a_osz a - w_opc w ->
  w_ipc w - a_ipos a = Zlength hb ->
  forall cSize, frame_compressed_size_m (lh_mg (w_k w)) (sublist (a_ipos a) (a_isz a) (a_ibs a)) = Some cSize ->
    a_isz a - a_ipos a < cSize.

(* the shortcut's decoding of the frame x = input[ipos, ipos + cSize) with capacity fh_contentSize h (fix F7), from
   the configuration of a new context: the one-shot model's result (out: the output space from op, whose first
   fh_contentSize h cells the call writes), and litExtraBuffer lxb' after it is the frame model's (model/ExFrame.v
   x_frame from the tables' litExtraBuffer of the context k1 after piece A) *)
Definition lhB_x (a: dsa) (w: lw) (k1: cst3) (h: frame_header) (cSize r: Z) (out: list val) (lxb': list Z) : Prop :=
  let x := sublist (a_ipos a) (a_ipos a + cSize) (a_ibs a) in
  fresh_cfg (a_st a) ->
  os_match x (fh_contentSize h) r (sublist 0 (fh_contentSize h) out) /\
  Zlength (tabs_lxb (c3_tabs k1)) = ExBlock.XLITEXTRA + ExBlock.XWILDCOPY /\
  (is_error_code r = false -> is_skippable_magic (le_field x 0 4) = false ->
   forall (st e: XS) (c: list Z), ExBlock.x_lxb ExHuf.xhuf st = tabs_lxb (c3_tabs k1) ->
     xframe1 st x (fh_contentSize h) = Some (c, Zlength x, e) -> lxb' = ExBlock.x_lxb ExHuf.xhuf e).

(* the model's shortcut against the one-shot model (plain Coq): x_frame on exactly one Zstandard frame x (not a
   skippable one), from any state whose litExtraBuffer has its full size, succeeds taking all of x iff the one-shot
   decoding of x (Exact.os_res, from a new context) succeeds, with the same content (model/ExOneshot.v) *)
Definition lh_short_model : Prop :=
  forall (st: XS) (x: list Z) (cap: Z),
    bytes_ok x -> frame_compressed_size x = Some (Zlength x) -> is_skippable_magic (le_field x 0 4) = false ->
    Zlength (ExBlock.x_lxb ExHuf.xhuf st) = ExBlock.XLITEXTRA + ExBlock.XWILDCOPY ->
    Exact.os_res x cap =
    match xframe1 st x cap with
    | Some (c, k, _) => if k =? Zlength x then Some c else None
    | None => None
    end.

(* ---------- piece C: the frame's beginning ---------- *)

(* ZSTD_decompressBegin_usingDDict keeps litExtraBuffer (the tables' bytes after piece A) *)
Definition lhC_x (k1: cst3) (c: lhc) : Prop := lc_lxb c = tabs_lxb (c3_tabs k1).

(* ---------- piece D: the buffers ---------- *)

(* buffered output (stable = false): before piece D the stream fields s, after it s3; the header h with the
   effective block size bsm.  neededInBuffSize, neededOutBuffSize (S3Defs.ring_needed: ZSTD_decodingBufferSize_internal),
   ZSTD_DCtx_updateOversizedDuration, then a new calloc'd buffer (zeros) when one of the sizes is too small or the
   buffers were oversized for ZSTD_WORKSPACETOOLARGE_MAXDURATION frames, else the same buffer.  oversizedDuration is
   below its maximum: C's oversizedDuration++ is on a size_t, which wraps at 2^64, where the model's counter does not
   (a reached state's counter stays far below it) *)
Definition lhD_x (stable: bool) (s s3: sfields) (h: frame_header) (bsm: Z) : Prop :=
  stable = false -> sf_over s < Int64.max_unsigned ->
  let needIn := Z.max bsm 4 in
  let needOut := ring_needed h bsm in
  let over := if sf_inSize s + sf_outSize s >=? (needIn + needOut) * ExStream.ZS_WORKSPACETOOLARGE_FACTOR
              then sf_over s + 1 else 0 in
  sf_over s3 = over /\
  if orb (orb (sf_inSize s <? needIn) (sf_outSize s <? needOut)) (over >=? ExStream.ZS_WORKSPACETOOLARGE_MAXDURATION)
  then sf_inSize s3 = needIn /\ sf_outSize s3 = needOut /\
       sublist needIn (needIn + needOut) (sf_ring s3) = zbytes (ExStream.ring_fresh needOut)
  else sf_inSize s3 = sf_inSize s /\ sf_outSize s3 = sf_outSize s /\ sf_ring s3 = sf_ring s.

(* ---------- the posts of the pieces with the exact facts ---------- *)

Section Posts.
Variable DENT : dent_pred.
Variable TABS : tabs_pred.

Definition lh_ret_x (a: dsa) (w: lw) (hb: list Z) : option val -> environ -> mpred :=
  fun vl =>
  EX r: Z, EX ipos': Z, EX w': lw,
  PROPx [vl = Some (Vlong (Int64.repr r)); 0 <= r <= Int64.max_unsigned; lh_rc a w hb r ipos' w';
         lh_xok a w hb r ipos' w']
  (LOCALx (ds_LI_L a w') (SEPx (ds_S_ip DENT TABS a w' ipos'))).

Definition lhA_post_x (a: dsa) (w: lw) (hb: list Z) : ret_assert :=
  {| RA_normal := RA_normal (lhA_post DENT TABS a w hb);
     RA_break := RA_break (lhA_post DENT TABS a w hb);
     RA_continue := FF;
     RA_return := lh_ret_x a w hb |}.

Definition lhB_post_x (a: dsa) (w: lw) (hb: list Z) (h: frame_header) (k1: cst3) (tbl: list val) : ret_assert :=
  {| RA_normal := PROPx [lhB_none a w hb h] (LOCALx (ds_LI_L a (lw_k w k1)) (SEPx (ds_LI_St DENT TABS a (lw_k w k1) tbl)));
     RA_break := EX cSize: Z, EX r: Z, EX out: list val, EX c: list Z, EX fs': fstate, EX d': dfields, EX lxb': list Z,
       PROPx [lhB_facts a w k1 hb h cSize r out; is_error_code r = false; bytes_ok c; Zlength c = r;
              sublist 0 r out = zbytes c; lhB_dict k1 d'; fp_ok (fs_fParams fs');
              lhB_sel_fp k1 tbl (sublist (a_ipos a) (a_ipos a + cSize) (a_ibs a)) fs' d';
              lhB_sw k1 tbl (sublist (a_ipos a) (a_ipos a + cSize) (a_ibs a)) d';
              sublist (w_opc w + r) (a_osz a) (sublist 0 (w_opc w) (w_oc w) ++ out) = sublist (w_opc w + r) (a_osz a) (w_oc w);
              lhB_x a w k1 h cSize r out lxb']
       (LOCALx (ds_LI_L a (lhB_brk w k1 fs' d' lxb' (a_ipos a + cSize) r out c))
       (SEPx (ds_LI_S DENT TABS a (lhB_brk w k1 fs' d' lxb' (a_ipos a + cSize) r out c))));
     RA_continue := FF;
     RA_return := lh_ret_x a w hb |}.

Definition lhC_post_x (a: dsa) (w: lw) (hb: list Z) (h: frame_header) (k1: cst3) : ret_assert :=
  {| RA_normal := EX c: lhc,
       PROPx [lhC_facts a w k1 h c; lhC_x k1 c]
       (LOCALx (ds_LI_L a (lw_k w (lhC_k k1 hb h c))) (SEPx (ds_LI_S DENT TABS a (lw_k w (lhC_k k1 hb h c)))));
     RA_break := FF;
     RA_continue := FF;
     RA_return := lh_ret_x a w hb |}.

Definition lhD_post_x (a: dsa) (w: lw) (hb: list Z) (h: frame_header) (k3: cst3) : ret_assert :=
  {| RA_normal := EX s3: sfields,
       PROPx [lhD_facts (c3_stable k3) (c3_s k3) s3 h (lh_bsm k3 h); lhD_x (c3_stable k3) (c3_s k3) s3 h (lh_bsm k3 h)]
       (LOCALx (ds_LI_L a (lw_k w (lhD_k k3 h s3))) (SEPx (ds_LI_S DENT TABS a (lw_k w (lhD_k k3 h s3)))));
     RA_break := FF;
     RA_continue := FF;
     RA_return := lh_ret_x a w hb |}.

End Posts.

(* ---------- the pieces (C level) ---------- *)

Definition lhA_x_stmt : Prop :=
  lend_sel_ok -> GAP_fherr ->
  forall (Espec: OracleKind) DENT TABS BR (a: dsa) (w: lw) (hb: list Z),
    DENT_OK DENT -> TABS_OK TABS -> dsa_ok a -> lh_entry a w hb -> lh_sel_pre a w -> lhx_entry a w ->
    semax (ds_Delta DENT TABS BR) (lh_st DENT TABS a w) lh_A (lhA_post_x DENT TABS a w hb).

Definition lhB_x_stmt : Prop :=
  MF3 -> lend_use_ok -> hs_probe_ok -> lh_short_model ->
  forall (Espec: OracleKind) DENT TABS BR (a: dsa) (w: lw) (hb: list Z) (h: frame_header) (tbl: list val)
         (d1: dfields) (did1: val),
    DENT_OK DENT -> TABS_OK TABS -> dsa_ok a -> lh_entry a w hb -> dd_bytes_ok (a_st a) -> lh_hb_in a w hb ->
    lhx_entry a w ->
    get_frame_header_m (lh_mg (w_k w)) hb = FH_ok h -> gfh3_facts (lh_mg (w_k w)) hb h ->
    lhA_sel (w_k w) hb 0 (fh_val h) tbl d1 did1 ->
    let k1 := k_A (w_k w) (fh_val h) d1 did1 in
    semax (ds_Delta DENT TABS BR) (lh_stt DENT TABS a (lw_k w k1) tbl) lh_B (lhB_post_x DENT TABS a w hb h k1 tbl).

Definition lhC_x_stmt : Prop :=
  lend_sel_ok -> lend_begin_ok -> hs_probe_ok ->
  forall (Espec: OracleKind) DENT TABS BR (a: dsa) (w: lw) (hb: list Z) (h: frame_header) (tbl: list val)
         (d1: dfields) (did1: val),
    DENT_OK DENT -> TABS_OK TABS -> dsa_ok a -> lh_entry a w hb -> lh_sel_pre a w -> lhx_entry a w -> lh_ctx a w hb ->
    get_frame_header_m (lh_mg (w_k w)) hb = FH_ok h -> gfh3_facts (lh_mg (w_k w)) hb h ->
    lhA_sel (w_k w) hb 0 (fh_val h) tbl d1 did1 -> lhB_none a w hb h ->
    let k1 := k_A (w_k w) (fh_val h) d1 did1 in
    semax (ds_Delta DENT TABS BR) (lh_stt DENT TABS a (lw_k w k1) tbl) lh_C (lhC_post_x DENT TABS a w hb h k1).

Definition lhD_x_stmt : Prop :=
  forall (Espec: OracleKind) DENT TABS BR (a: dsa) (w: lw) (hb: list Z) (h: frame_header) (tbl: list val)
         (d1: dfields) (did1: val) (c: lhc),
    DENT_OK DENT -> TABS_OK TABS -> dsa_ok a -> lh_entry a w hb -> lhx_entry a w ->
    get_frame_header_m (lh_mg (w_k w)) hb = FH_ok h -> gfh3_facts (lh_mg (w_k w)) hb h ->
    lhA_sel (w_k w) hb 0 (fh_val h) tbl d1 did1 ->
    let k1 := k_A (w_k w) (fh_val h) d1 did1 in
    lhC_facts a w k1 h c ->
    let k3 := lhC_k k1 hb h c in
    semax (ds_Delta DENT TABS BR) (lh_st DENT TABS a (lw_k w k3)) lh_D (lhD_post_x DENT TABS a w hb h k3).

(* ---------- the glue: the loop invariant with ex_call ---------- *)

(* G1: the break after a complete load of the header bytes (the model's LNext of st_load_header) *)
Definition lh_brkA_x_stmt : Prop :=
  MF3 -> hs_probe_ok ->
  forall DENT TABS (a: dsa) (w: lw) (hb: list Z) (kk: Z) (v: reptype t_fh) (tbl: list val) (d1: dfields) (did1: val),
    lh_ctx a w hb -> lhx_entry a w -> lhA_sel (w_k w) hb kk v tbl d1 did1 ->
    get_frame_header_m (lh_mg (w_k w)) hb = FH_more kk -> kk - Zlength hb <= a_isz a - w_ipc w ->
    lh_st DENT TABS a (lhA_brk a w (k_A (w_k w) v d1 did1) hb kk) |-- ds_inv_x DENT TABS a.

(* G2: the break after a successful shortcut (someMoreWork = 0: the model's LStop of st_header_done) *)
Definition lh_brkB_x_stmt : Prop :=
  MF3 -> hs_probe_ok -> GAP_dd_bytes -> lh_short_model ->
  forall DENT TABS (a: dsa) (w: lw) (hb: list Z) (h: frame_header) (tbl: list val) (d1: dfields) (did1: val)
         (cSize r: Z) (out: list val) (c: list Z) (fs': fstate) (d': dfields) (lxb': list Z),
    lh_ctx a w hb -> lhx_entry a w -> get_frame_header_m (lh_mg (w_k w)) hb = FH_ok h ->
    gfh3_facts (lh_mg (w_k w)) hb h ->
    lhA_sel (w_k w) hb 0 (fh_val h) tbl d1 did1 ->
    let k1 := k_A (w_k w) (fh_val h) d1 did1 in
    lhB_facts a w k1 hb h cSize r out -> is_error_code r = false ->
    bytes_ok c -> Zlength c = r -> sublist 0 r out = zbytes c -> lhB_dict k1 d' -> fp_ok (fs_fParams fs') ->
    lhB_sel_fp k1 tbl (sublist (a_ipos a) (a_ipos a + cSize) (a_ibs a)) fs' d' ->
    lhB_sw k1 tbl (sublist (a_ipos a) (a_ipos a + cSize) (a_ibs a)) d' ->
    sublist (w_opc w + r) (a_osz a) (sublist 0 (w_opc w) (w_oc w) ++ out) = sublist (w_opc w + r) (a_osz a) (w_oc w) ->
    lhB_x a w k1 h cSize r out lxb' ->
    lh_st DENT TABS a (lhB_brk w k1 fs' d' lxb' (a_ipos a + cSize) r out c) |-- ds_inv_x DENT TABS a.

(* G4: after piece D, the fall-through into zdss_read: the model's iteration goes on from the stage-read state of
   st_header_done (S3XKit.ex_loop_fall), whose fields the context after piece D represents (zrel_end) *)
Definition lh_read_x_stmt : Prop :=
  MF3 -> hs_probe_ok -> GAP_dd_bytes ->
  forall DENT TABS (a: dsa) (w: lw) (hb: list Z) (h: frame_header) (tbl: list val) (d1: dfields) (did1: val)
         (c: lhc) (s3: sfields),
    lh_ctx a w hb -> lhx_entry a w -> get_frame_header_m (lh_mg (w_k w)) hb = FH_ok h ->
    gfh3_facts (lh_mg (w_k w)) hb h ->
    lhA_sel (w_k w) hb 0 (fh_val h) tbl d1 did1 -> lhB_none a w hb h ->
    let k1 := k_A (w_k w) (fh_val h) d1 did1 in
    lhC_facts a w k1 h c -> lhC_x k1 c ->
    let k3 := lhC_k k1 hb h c in
    lhD_facts (c3_stable k3) (c3_s k3) s3 h (lh_bsm k3 h) -> lhD_x (c3_stable k3) (c3_s k3) s3 h (lh_bsm k3 h) ->
    let w3 := lw_k w (lhD_k k3 h s3) in
    lh_st DENT TABS a w3 |-- !! ex_call a w3.

(* ---------- the returns against the full specification ---------- *)

Definition lh_ret_x_stmt : Prop :=
  MF3 -> RET3x -> hs_probe_ok -> GAP_dd_bytes ->
  forall DENT TABS BR (a: dsa) (w: lw) (hb: list Z) (r ipos': Z) (w': lw),
    TABS_OK TABS -> lh_ctx a w hb -> lhx_entry a w -> 0 <= r <= Int64.max_unsigned ->
    lh_rc a w hb r ipos' w' -> lh_xok a w hb r ipos' w' ->
    (lh_rc_hint a w hb r ipos' w' -> lh_ret_goal_x DENT TABS BR a w' r ipos') ->
    lh_ret_goal_x DENT TABS BR a w' r ipos'.

(* the hint: the model's early return (S3XKit.ex_loop_early): stream_exact, and the next context's exact relation *)
Definition lh_hint_x_stmt : Prop :=
  MF3 -> hs_probe_ok ->
  forall DENT TABS BR (a: dsa) (w: lw) (hb: list Z) (r ipos': Z) (w': lw),
    TABS_OK TABS -> lh_ctx a w hb -> lhx_entry a w -> 0 <= r <= Int64.max_unsigned -> lh_rc_hint a w hb r ipos' w' ->
    lh_ret_goal_x DENT TABS BR a w' r ipos'.

End CM_LH3XDefs_1.
