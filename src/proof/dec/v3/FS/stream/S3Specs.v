(* FS3 streaming: the specifications the streaming part chooses (FSOblig3.stream3_ids order):
   ZSTD_decompressContinue as ZSTD_decompressStream uses it, and ZSTD_decompressContinueStream.  Every streaming piece
   uses them.  v2's StreamSpecs
   with the frame's DDict: the tables TABS gv p ox ts and the DDict's entropy dent_of DENT gv ox (ox = the
   DDict the frame began with), the DDict content as the prefix / first extDict (lay_res: its cells, Ews),
   the parameters (format field, capped Block_Maximum_Size, ignored checksums).  As in v2, within the stream
   ZSTD_decompressContinue only sees the frame stages decodeBlockHeader, decompressBlock, decompressLastBlock,
   checkChecksum and skipFrame, with exactly the unit zstd expects. *)
Require Export Zstd.proof.dec.v3.FS.stream.S3Defs.
Require Zstd.proof.model.ExStream.
Local Open Scope logic.

Section CM_S3Specs_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* ---------- the layout through ZSTD_decompressContinue ---------- *)

(* checkContinuity on the layout l for a write at base + d with capacity cap (HL_stuck only at capacity 0) *)
Definition lmove (l: hlay) (base: val) (d cap: Z) : hlay :=
  if cap <=? 0 then l else
  match l with
  | HL_none => HL_seg base d d ExtNone
  | HL_dict eb ec _ => HL_seg base d d (ext_of_dict eb ec)
  | HL_stuck _ _ _ => l
  | HL_seg b ps pe e => if pe =? d then l else HL_seg base d d (ExtIn pe (pe - ps))
  end.

(* previousDstEnd := dst + r after a block *)
Definition lwrite (l: hlay) (base: val) (d r: Z) : hlay :=
  match l with
  | HL_seg b ps _ e => HL_seg b ps (d + r) e
  | HL_none => HL_stuck base (d + r) None
  | HL_dict eb ec gp => HL_stuck base (d + r) (Some (eb, ec, gp))
  | HL_stuck _ _ od => HL_stuck base (d + r) od
  end.

(* the history zstd reaches for a compressed block of z written at o (after the move) *)
Definition lay_H (z: zprog) (l: hlay) (o: outarr) : list Z :=
  match lmove l (oa_base o) (oa_d o) (oa_cap o) with
  | HL_seg _ _ _ e => hist_for e z
  | _ => zp_hist z
  end.

(* what zstd needs of the history for a compressed block written at base + d (after the move) *)
Definition hist_pre (fp: fprog) (l: hlay) (o: outarr) : Prop :=
  match fp with
  | FP_zstd _ z =>
      let h := zp_h z in
      match zp_ph z with
      | ZP_body bh =>
          bp_type (block_props_of bh) = 2 -> 0 < oa_cap o ->
          match lmove l (oa_base o) (oa_d o) (oa_cap o) with
          | HL_seg b ps pe e =>
              b = oa_base o /\ pe = oa_d o /\
              layout_ok_seg ps e (oa_N o) /\
              hist_view (oa_c o) (oa_d o) ps e (hist_for e z) (zp_out z) (fh_windowSize h) /\
              ext_clear (oa_d o) ps (oa_cap o) (zp_bsm z) e (hist_for e z) (zp_out z) (fh_windowSize h)
          | _ => False
          end
      | _ => True
      end
  | _ => True
  end.

(* the layout after the unit: checkContinuity's move, then previousDstEnd = dst + r after a block *)
Definition lnext (fp: fprog) (l: hlay) (o: outarr) (r: Z) : hlay :=
  let l1 := lmove l (oa_base o) (oa_d o) (oa_cap o) in
  match fp with
  | FP_zstd _ z => match zp_ph z with ZP_body _ => lwrite l1 (oa_base o) (oa_d o) r | _ => l1 end
  | _ => l
  end.

(* a success on the unit u: the new progress, layout, tables and cells (the model's step reads the tables'
   entropy state, the coercion DecRep.ts_d) *)
Definition cont_post (fp: fprog) (l: hlay) (dd: option (ddx * val)) (o: outarr) (u: list Z) (r: Z)
    (oc': list val) (fs': fstate) (tabs': option tstate) : Prop :=
  match fp with
  | FP_skip hdr got =>
      r = 0 /\ oc' = oa_c o /\ exists ts, tabs' = Some ts /\
      c_frame fs' (TInit (dd_ox dd) ts) (FP_skip hdr (le_field hdr 4 4)) l dd
  | FP_zstd hdr z =>
      exists cnt (ts': tstate),
        cnt_safe z u cnt ts' /\ (hist_pre fp l o -> cnt_ok z (lay_H z l o) u cnt ts') /\
        cont_checks z u cnt /\ r = Zlength cnt /\ tabs' = Some ts' /\
        sublist (oa_d o) (oa_d o + r) oc' = zbytes cnt /\
        unchanged_outside (oa_c o) oc' (oa_d o) (oa_d o + Z.min (oa_cap o) (zp_bsm z + WILDCOPY_OVERLENGTH)) /\
        c_frame fs' (TInit (dd_ox dd) ts') (FP_zstd hdr (zstep z u cnt ts')) (lnext fp l o r) dd
  | _ => False
  end.

(* where the layout may be: in the output array, a block written at its end (or the ring's restart) *)
Definition lay_at (l: hlay) (o: outarr) : Prop :=
  match l with
  | HL_none => True
  | HL_dict _ _ _ => True
  | HL_stuck b pe _ => b = oa_base o /\ pe = oa_d o /\ oa_cap o = 0
  | HL_seg b ps pe e =>
      b = oa_base o /\ 0 <= ps <= pe /\ pe <= oa_N o /\ ps <= oa_d o /\
      match e with ExtIn e1 elen => 0 <= elen <= e1 /\ e1 <= oa_N o | _ => True end
  end.

(* the dictionary's content in the layout: zstd's own copy (gpDictCopy = 1: no pointer comparison) or 0 bytes
   at a strictly valid pointer (compared with dst); at most 2^63-1 bytes *)
Definition pre_ok (W: list ptr_witness) (p: dpre) : Prop :=
  let '(eb, ec, gp) := p in
  Zlength ec <= 2 ^ 63 - 1 /\ (gp = 1 \/ (gp = 0 /\ ec = nil /\ (pws_pred W |-- valid_pointer eb))).

Definition lay_wit (W: list ptr_witness) (l: hlay) : Prop :=
  match l with
  | HL_dict eb ec gp => pre_ok W (eb, ec, gp)
  | HL_stuck _ _ (Some p) => pre_ok W p
  | HL_seg _ _ _ (ExtSep _ eb en ec _ _) => en <= 2 ^ 63 - 1 /\ (en = 0 -> (pws_pred W |-- valid_pointer eb))
  | _ => True
  end.

(* the memory of the dictionary's content the layout refers to *)
Definition lay_res (l: hlay) : mpred :=
  match l with
  | HL_dict eb ec _ => data_at Ews (tarray tuchar (Zlength ec)) ec eb
  | HL_stuck _ _ (Some (eb, ec, _)) => data_at Ews (tarray tuchar (Zlength ec)) ec eb
  | HL_seg _ _ _ e => ext_res e
  | _ => emp
  end.

(* ZSTD_decompressContinue's result r on the unit u *)
Definition cont_res (fp: fprog) (l: hlay) (dd: option (ddx * val)) (o: outarr) (u: list Z) (r: Z)
    (oc': list val) (fs': fstate) (tabs': option tstate) : Prop :=
  0 <= r <= Int64.max_unsigned /\ Zlength oc' = oa_N o /\
  unchanged_outside (oa_c o) oc' (oa_d o) (oa_d o + oa_cap o) /\
  (byte_cells (oa_c o) -> byte_cells oc') /\
  if is_error_code r
  then (hist_pre fp l o ->
          cont_err fp (match fp with FP_zstd _ z => lay_H z l o | _ => nil end) u (oa_cap o)) /\
       r <> err_code ZSTD_error_noForwardProgress_destFull /\ r <> err_code ZSTD_error_noForwardProgress_inputEmpty
  else cont_post fp l dd o u r oc' fs' tabs'.

(* the history of a compressed block is bytes, and its extDict is clear of the output or the whole output
   array is bytes (what the block decoder needs for byte output) *)
Definition cont_hist (fp: fprog) (l: hlay) (o: outarr) : Prop :=
  match fp with
  | FP_zstd _ z =>
      match zp_ph z with
      | ZP_body bh =>
          bp_type (block_props_of bh) = 2 -> 0 < oa_cap o ->
          match lmove l (oa_base o) (oa_d o) (oa_cap o) with
          | HL_seg _ ps _ e =>
              hist_def (oa_c o) (oa_d o) ps e /\ (ext_clean (oa_d o) (oa_cap o) e \/ byte_cells (oa_c o))
          | _ => True
          end
      | _ => True
      end
  | _ => True
  end.

(* ZSTD_decompressContinue exactly as the model (ExStream.d_continue): for any model state d of the frame with
   header fh that the frame fields fs and the tables ts represent (S3XRel.drel, ring offsets in the output array's
   base), and the output array's cells mem, the call's outcome on the unit u of n bytes is the model's, and the
   fields and tables after it represent the model's next state (the stream's exact claim, Spec_api6.stream_exact);
   for the context's own tables (no DDict: the stream's exact configuration) *)
Definition cont_exact (fs: fstate) (ts: tstate) (o: outarr) (u: list Z) (n r: Z) (oc': list val)
    (fs': fstate) (tabs': option tstate) : Prop :=
  forall fh d mem, drel fh d (oa_base o) fs ts -> oa_c o = zbytes mem -> bytes_ok mem ->
    (* a compressed block without room never reads an extDict (in the stream: an extDict exists only after the ring
       restarted, and then a block always has room) *)
    ((ExStream.d_stage XS d = ExStream.DS_decompressBlock \/ ExStream.d_stage XS d = ExStream.DS_decompressLastBlock) ->
       ExStream.d_btype XS d = 2 -> oa_cap o = 0 -> ExStream.d_de XS d = None) ->
    match ExStream.d_continue XS Exact.xblock fh d mem (oa_d o) (oa_cap o) u n with
    | None => is_error_code r = true
    | Some (d', mem', r0) =>
        r = r0 /\ oc' = zbytes mem' /\ exists ts', tabs' = Some ts' /\ drel fh d' (oa_base o) fs' ts'
    end.

Section Specs.
Variable DENT : dent_pred.
Variable TABS : tabs_pred.

(* the input array, when zstd reads the unit (not for a skippable frame) *)
Definition in_res (fp: fprog) (i: inwin) : mpred :=
  if is_skip fp then emp else data_at (iw_sh i) (tarray tuchar (iw_N i)) (iw_c i) (iw_base i).

Definition cont_pre (fs: fstate) (ts: tstate) (fp: fprog) (l: hlay) (dd: option (ddx * val)) (W: list ptr_witness)
    (o: outarr) (src: val) (i: inwin) (n f: Z) : Prop :=
  c_frame fs (TInit (dd_ox dd) ts) fp l dd /\ fp_complete fp = false /\ unit_ok fp n /\
  0 <= n <= Int64.max_unsigned /\ outarr_ok o /\ lay_at l o /\ cont_hist fp l o /\ lay_wit W l /\
  (is_skip fp = true -> oa_cap o = 0) /\
  (is_skip fp = false -> src = offset_val (iw_off i) (iw_base i) /\ inwin_ok i /\ Zlength (iw_s i) = n /\
     byte_cells (iw_c i)) /\
  (oa_N o = 0 -> (pws_pred W |-- weak_valid_pointer (oa_base o))) /\
  (f = 0 \/ f = 1).

Definition ZSTD_decompressContinue_spec3 : ident * funspec :=
  DECLARE _ZSTD_decompressContinue
  WITH gv: globals, p: val, fs: fstate, ts: tstate, fp: fprog, l: hlay, dd: option (ddx * val),
       W: list ptr_witness, o: outarr, src: val, i: inwin, n: Z, f: Z
  PRE [ tptr t_dctx, tptr tvoid, tulong, tptr tvoid, tulong ]
    PROP (cont_pre fs ts fp l dd W o src i n f)
    PARAMS (p; offset_val (oa_d o) (oa_base o); Vlong (Int64.repr (oa_cap o)); src; Vlong (Int64.repr n))
    GLOBALS (gv)
    SEP (zstd_globals gv; pws_pred W; cfg_fmt p f; cfg_lit p; frame_fields p fs; TABS gv p (dd_ox dd) ts;
         dent_of DENT gv (dd_ox dd); lay_res l;
         data_at (oa_sh o) (tarray tuchar (oa_N o)) (oa_c o) (oa_base o); in_res fp i)
  POST [ tulong ]
    EX r: Z, EX oc': list val, EX fs': fstate, EX tabs': option tstate,
    PROP (cont_res fp l dd o (iw_s i) r oc' fs' tabs';
          fs_ddictIsCold fs' = fs_ddictIsCold fs \/ fs_ddictIsCold fs' = Vint (Int.repr 0);
          (* an error leaves fParams as it was *)
          is_error_code r = true -> fs_fParams fs' = fs_fParams fs;
          dd = None -> cont_exact fs ts o (iw_s i) n r oc' fs' tabs')
    RETURN (Vlong (Int64.repr r))
    SEP (zstd_globals gv; pws_pred W; cfg_fmt p f; cfg_lit p; frame_fields p fs';
         match tabs' with Some ts' => TABS gv p (dd_ox dd) ts' | None => EX lxb: list Z, tables_uninit p lxb end;
         dent_of DENT gv (dd_ox dd); lay_res l;
         data_at (oa_sh o) (tarray tuchar (oa_N o)) oc' (oa_base o); in_res fp i).

(* ZSTD_decompressContinueStream(zds, &op, oend, src, n): ZSTD_decompressContinue into the output array o:
   buffered, the ring's output part at outStart (capacity outSize - outStart); stable, the caller's buffer at
   op (capacity oend - op); capacity 0 for a skippable frame.  Then the stream stage (and outEnd, or op) as
   zstd sets them; returns 0 or the error. *)
Definition ccs_out_ok (stable: bool) (fp: fprog) (o: outarr) (outBuff: val) (outSize ostart: Z)
    (opv oend: val) : Prop :=
  oa_cap o = (if is_skip fp then 0 else oa_N o - oa_d o) /\
  if stable then opv = offset_val (oa_d o) (oa_base o) /\ oend = offset_val (oa_N o) (oa_base o)
  else oa_base o = outBuff /\ oa_N o = outSize /\ oa_d o = ostart.

Definition ZSTD_decompressContinueStream_spec3 : ident * funspec :=
  DECLARE _ZSTD_decompressContinueStream
  WITH gv: globals, p: val, fs: fstate, ts: tstate, fp: fprog, l: hlay, dd: option (ddx * val),
       W: list ptr_witness, o: outarr, src: val, i: inwin, n: Z, f: Z,
       stable: bool, stage: Z, outBuff: val, outSize: Z, ostart: Z, oendv: val, opp: val, opv: val, oend: val
  PRE [ tptr t_dctx, tptr (tptr tschar), tptr tschar, tptr tvoid, tulong ]
    PROP (cont_pre fs ts fp l dd W o src i n f;
          ccs_out_ok stable fp o outBuff outSize ostart opv oend;
          0 <= ostart; ostart <= outSize; outSize <= Int64.max_unsigned; Int.min_signed <= stage <= Int.max_signed)
    PARAMS (p; opp; oend; src; Vlong (Int64.repr n))
    GLOBALS (gv)
    SEP (zstd_globals gv; pws_pred W; cfg_fmt p f; cfg_lit p; frame_fields p fs; TABS gv p (dd_ox dd) ts;
         dent_of DENT gv (dd_ox dd); lay_res l;
         data_at (oa_sh o) (tarray tuchar (oa_N o)) (oa_c o) (oa_base o); in_res fp i;
         field_at Ews t_dctx (DOT _streamStage) (Vint (Int.repr stage)) p;
         field_at Ews t_dctx (DOT _outBufferMode) (Vint (Int.repr (if stable then 1 else 0))) p;
         field_at Ews t_dctx (DOT _outBuff) outBuff p;
         field_at Ews t_dctx (DOT _outBuffSize) (vlong outSize) p;
         field_at Ews t_dctx (DOT _outStart) (vlong ostart) p;
         field_at Ews t_dctx (DOT _outEnd) oendv p;
         data_at Tsh (tptr tschar) opv opp)
  POST [ tulong ]
    EX rr: Z, EX oc': list val, EX fs': fstate, EX tabs': option tstate,
    PROP (cont_res fp l dd o (iw_s i) rr oc' fs' tabs';
          fs_ddictIsCold fs' = fs_ddictIsCold fs \/ fs_ddictIsCold fs' = Vint (Int.repr 0);
          is_error_code rr = true -> fs_fParams fs' = fs_fParams fs;
          stable = false -> dd = None -> cont_exact fs ts o (iw_s i) n rr oc' fs' tabs')
    RETURN (Vlong (Int64.repr (if is_error_code rr then rr else 0)))
    SEP (zstd_globals gv; pws_pred W; cfg_fmt p f; cfg_lit p; frame_fields p fs';
         match tabs' with Some ts' => TABS gv p (dd_ox dd) ts' | None => EX lxb: list Z, tables_uninit p lxb end;
         dent_of DENT gv (dd_ox dd); lay_res l;
         data_at (oa_sh o) (tarray tuchar (oa_N o)) oc' (oa_base o); in_res fp i;
         field_at Ews t_dctx (DOT _streamStage)
           (Vint (Int.repr (if is_error_code rr then stage
                            else if stable then zdss_read
                            else if andb (rr =? 0) (negb (is_skip fp)) then zdss_read else zdss_flush))) p;
         field_at Ews t_dctx (DOT _outBufferMode) (Vint (Int.repr (if stable then 1 else 0))) p;
         field_at Ews t_dctx (DOT _outBuff) outBuff p;
         field_at Ews t_dctx (DOT _outBuffSize) (vlong outSize) p;
         field_at Ews t_dctx (DOT _outStart) (vlong ostart) p;
         field_at Ews t_dctx (DOT _outEnd)
           (if is_error_code rr then oendv
            else if stable then oendv
            else if andb (rr =? 0) (negb (is_skip fp)) then oendv else vlong (ostart + rr)) p;
         data_at Tsh (tptr tschar)
           (if andb stable (negb (is_error_code rr)) then offset_val (oa_d o + rr) (oa_base o) else opv) opp).

End Specs.

(* the streaming part's specifications, in FSOblig3.stream3_ids order *)
Definition stream_ss3 (DENT: dent_pred) (TABS: tabs_pred) : funspecs :=
  [ ZSTD_decompressContinue_spec3 DENT TABS; ZSTD_decompressContinueStream_spec3 DENT TABS ].

Lemma stream_ss3_ids : forall DENT TABS, map fst (stream_ss3 DENT TABS) = stream3_ids.
Proof. reflexivity. Qed.

(* the context of every streaming body (any BR: the streaming bodies never touch a buffer-less frame) *)
Definition stream_G3 (DENT: dent_pred) (TABS: tabs_pred) (BR: blrel) : funspecs :=
  FS3_G DENT TABS SR3 BR ++ stream_ss3 DENT TABS.

Definition stream_body3 (f: dent_pred -> tabs_pred -> blrel -> ident * funspec) : Prop :=
  forall DENT TABS BR, DENT_OK DENT -> TABS_OK TABS -> body_ok (stream_G3 DENT TABS BR) (f DENT TABS BR).

End CM_S3Specs_1.
