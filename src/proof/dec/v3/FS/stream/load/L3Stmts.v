(* FS3 streaming, case zdss_load: the call ZSTD_decompressContinueStream(zds, &op, oend, inBuff,
   neededInSize) once the unit is loaded: its arguments (output array, input window), the context after it, and
   the pure obligations the VST pieces assume (P_load_*: proved in their own files, assembled in S3Seg_load). *)
Require Export Zstd.proof.dec.v3.FS.stream.load.L3Base.
Local Open Scope logic.

Section CM_L3Stmts_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* the C frame state does not depend on the part of the unit loaded so far: the call sees the unit view *)
Definition fp_unit (fp: fprog) : fprog :=
  match fp with
  | FP_skip hdr _ => FP_skip hdr 0
  | FP_zstd hdr z => FP_zstd hdr (zp_set_got z nil)
  | x => x
  end.

(* the unit: the bytes loaded before this call, then the ones loaded now *)
Definition ld_u (sv: sview) (ibs: list Z) (ipc L: Z) : list Z := fp_loaded (sv_fp sv) ++ sublist ipc (ipc + L) ibs.

(* stable mode: the caller's buffer at op; the input window is the whole stream buffer *)
Definition o_st (a: dsa) (sv: sview) (opc: Z) (oc: list val) : outarr :=
  {| oa_sh := a_shob a; oa_base := a_ob a; oa_N := a_osz a; oa_c := oc; oa_d := opc;
     oa_cap := if is_skip (sv_fp sv) then 0 else a_osz a - opc |}.
Definition i_st (s: sfields) (ring: list val) (u: list Z) : inwin :=
  {| iw_sh := Ews; iw_base := sf_inBuff s; iw_N := sf_inSize s + sf_outSize s; iw_c := ring; iw_off := 0;
     iw_s := u |}.

(* buffered mode: the ring's out part at outStart; the input window is the in part (half of the share; the
   other half is the witness of outBuff = the end of the in part) *)
Definition o_bf (s: sfields) (ring: list val) (ostart: Z) (sv: sview) : outarr :=
  {| oa_sh := Ews; oa_base := sf_outBuff s; oa_N := sf_outSize s;
     oa_c := sublist (sf_inSize s) (sf_inSize s + sf_outSize s) ring; oa_d := ostart;
     oa_cap := if is_skip (sv_fp sv) then 0 else sf_outSize s - ostart |}.
Definition i_bf (s: sfields) (ring: list val) (u: list Z) : inwin :=
  {| iw_sh := fst (slice.cleave Ews); iw_base := sf_inBuff s; iw_N := sf_inSize s;
     iw_c := sublist 0 (sf_inSize s) ring; iw_off := 0; iw_s := u |}.

(* the stream fields after ZSTD_decompressContinueStream (inPos was set to 0 before it) *)
Definition s_cont (s: sfields) (stage: Z) (oend: val) (ring: list val) : sfields :=
  {| sf_stage := stage; sf_inBuff := sf_inBuff s; sf_inSize := sf_inSize s; sf_inPos := vlong 0;
     sf_outBuff := sf_outBuff s; sf_outSize := sf_outSize s; sf_outStart := sf_outStart s;
     sf_outEnd := oend; sf_lhSize := sf_lhSize s; sf_hostage := sf_hostage s; sf_nfp := sf_nfp s;
     sf_expOut := sf_expOut s; sf_hbuf := sf_hbuf s; sf_over := sf_over s; sf_ring := ring; sf_mem := sf_mem s; sf_held := sf_held s |}.

(* the tables after the call: initialised ones still point into the frame's DDict; uninitialised ones keep the
   litExtraBuffer's bytes lxb *)
Definition tabs_of (dd: option (ddx * val)) (lxb: list Z) (t: option tstate) : tabs3 :=
  match t with Some ts => TInit (dd_ox dd) ts | None => TUninit lxb end.

(* the context after the call: frame fields fs', tables t' (litExtraBuffer lxb if uninitialised), stream fields s *)
Definition k_cont (k: cst3) (fs': fstate) (t': option tstate) (lxb: list Z) (dd: option (ddx * val)) (s: sfields) : cst3 :=
  {| c3_fs := fs'; c3_tabs := tabs_of dd lxb t'; c3_stable := c3_stable k; c3_dict := c3_dict k; c3_s := s;
     c3_par := c3_par k; c3_sp := c3_sp k; c3_set := c3_set k |}.

(* the frame's dictionary is one the model handles like zstd (from the DDict's representation: byte content,
   loaded tables) *)
Definition fp_dm_ok (fp: fprog) : Prop := forall hdr z, fp = FP_zstd hdr z -> dm_ok (zp_dm z).

(* the frame's DDict's facts (ddict_struct, via the borrow at the call): byte content of at most 2^63-1 bytes,
   a pointer, zstd's own copy is not empty *)
Definition ld_dd (dd: option (ddx * val)) : Prop :=
  forall x buf, dd = Some (x, buf) ->
    bytes_ok (dx_bytes x) /\ Zlength (dx_bytes x) <= 2 ^ 63 - 1 /\ (isptr buf \/ (buf = nullval /\ dx_ref x = Some nullval /\ dx_bytes x = nil)) /\
    (ddx_copied x = true -> 0 < Zlength (dx_bytes x)).

(* GAP (a fact the stream relation did not state at first): c_ring's buffered HL_seg lacks `pe <= Zlength (fp_content
   fp)` (needed at a ring wrap) *)
Definition lay_cbound (fp: fprog) (l: hlay) : Prop :=
  forall b ps pe e, l = HL_seg b ps pe e -> pe <= Zlength (fp_content fp).

(* in the alive case (the current dictionary cd as the model has it), the frame's dictionary is one the model
   handles *)
Definition ld_dm (st: dctx_st) (k: cst3) (fp: fprog) : Prop :=
  forall cd, cur_dict_ok st k (next_cd (sm_of st) fp cd) -> fp_dm_ok fp.

(* the stream buffer as loaded *)
Definition ld_ring (sv: sview) (s: sfields) (ibs: list Z) (ipc L: Z) : list val :=
  ring_load (sv_fp sv) (sf_ring s) (fp_inpos (sv_fp sv)) ibs ipc L.

(* ---------- the pure obligations ---------- *)

(* the premises shared by the obligations: the unit is loaded, L = what was missing of it *)
Definition ld_ok (a: dsa) (k0: cst3) (sv: sview) (ipc opc: Z) (oc: list val) (dl: list Z) (E L: Z) : Prop :=
  dsa_ok a /\ call_inv a k0 sv ipc opc oc dl /\ sf_stage (c3_s k0) = zdss_load /\
  fs_expected (c3_fs k0) = vlong E /\ 0 <= E < 2 ^ 32 /\
  L = Z.min (E - fp_inpos (sv_fp sv)) (a_isz a - ipc) /\ L = E - fp_inpos (sv_fp sv) /\
  0 <= sf_inSize (c3_s k0) /\ 0 <= sf_outSize (c3_s k0) /\
  Zlength (sf_ring (c3_s k0)) = sf_inSize (c3_s k0) + sf_outSize (c3_s k0) /\
  Zlength (ld_ring sv (c3_s k0) (a_ibs a) ipc L) = sf_inSize (c3_s k0) + sf_outSize (c3_s k0) /\
  byte_cells (ld_ring sv (c3_s k0) (a_ibs a) ipc L) /\ ld_dd (sv_dd sv).

(* stable mode: the history the call needs (DecIface's block spec) *)
Definition P_load_cont_hist_st : Prop :=
  forall a k0 sv ipc opc oc dl E L,
  ld_ok a k0 sv ipc opc oc dl E L -> dc_stable (a_st a) = true ->
  cont_hist (fp_unit (sv_fp sv)) (sv_lay sv) (o_st a sv opc oc).

(* buffered mode: the same in the ring at outStart *)
Definition P_load_cont_hist_buf : Prop :=
  forall a k0 sv ipc opc oc dl E L ostart,
  ld_ok a k0 sv ipc opc oc dl E L -> dc_stable (a_st a) = false ->
  sf_outStart (c3_s k0) = vlong ostart ->
  cont_hist (fp_unit (sv_fp sv)) (sv_lay sv) (o_bf (c3_s k0) (ld_ring sv (c3_s k0) (a_ibs a) ipc L) ostart sv).

(* stable mode, a success: the loop invariant at zdss_read, op advanced by rr *)
Definition P_load_cont_stable : Prop :=
  forall a k0 sv ipc opc oc dl E L rr oc' fs' tabs' lxb,
  MF3 -> ld_ok a k0 sv ipc opc oc dl E L -> dc_stable (a_st a) = true -> ld_dm (a_st a) k0 (sv_fp sv) ->
  cont_res (fp_unit (sv_fp sv)) (sv_lay sv) (sv_dd sv) (o_st a sv opc oc) (ld_u sv (a_ibs a) ipc L)
    rr oc' fs' tabs' ->
  is_error_code rr = false ->
  exists sv2 dl2,
    call_inv a (k_cont k0 fs' tabs' lxb (sv_dd sv)
                  (s_cont (c3_s k0) zdss_read (sf_outEnd (c3_s k0)) (ld_ring sv (c3_s k0) (a_ibs a) ipc L)))
      sv2 (ipc + L) (opc + rr) oc' dl2.

(* buffered mode, a success: the loop invariant at zdss_read (nothing written) or zdss_flush (rr bytes written
   at outStart) *)
Definition P_load_cont_buf : Prop :=
  forall a k0 sv ipc opc oc dl E L ostart rr oc' fs' tabs' lxb,
  MF3 -> ld_ok a k0 sv ipc opc oc dl E L -> dc_stable (a_st a) = false -> ld_dm (a_st a) k0 (sv_fp sv) ->
  lay_cbound (sv_fp sv) (sv_lay sv) ->
  sf_outStart (c3_s k0) = vlong ostart -> 0 <= ostart <= sf_outSize (c3_s k0) ->
  let ring1 := ld_ring sv (c3_s k0) (a_ibs a) ipc L in
  cont_res (fp_unit (sv_fp sv)) (sv_lay sv) (sv_dd sv) (o_bf (c3_s k0) ring1 ostart sv) (ld_u sv (a_ibs a) ipc L)
    rr oc' fs' tabs' ->
  is_error_code rr = false ->
  let rd := andb (rr =? 0) (negb (is_skip (sv_fp sv))) in
  exists sv2,
    call_inv a (k_cont k0 fs' tabs' lxb (sv_dd sv)
                  (s_cont (c3_s k0) (if rd then zdss_read else zdss_flush)
                     (if rd then sf_outEnd (c3_s k0) else vlong (ostart + rr))
                     (sublist 0 (sf_inSize (c3_s k0)) ring1 ++ oc')))
      sv2 (ipc + L) opc oc dl.

(* an error: why it is allowed (stream_claims' error clause) *)
Definition P_load_err_why : Prop :=
  forall a k0 sv ipc opc oc dl E L ostart rr oc' fs' tabs',
  MF3 -> ld_ok a k0 sv ipc opc oc dl E L -> start_ok a ->
  (dc_stable (a_st a) = false -> lay_cbound (sv_fp sv) (sv_lay sv)) ->
  sf_outStart (c3_s k0) = vlong ostart -> 0 <= ostart <= sf_outSize (c3_s k0) ->
  cont_res (fp_unit (sv_fp sv)) (sv_lay sv) (sv_dd sv)
    (if dc_stable (a_st a) then o_st a sv opc oc
     else o_bf (c3_s k0) (ld_ring sv (c3_s k0) (a_ibs a) ipc L) ostart sv)
    (ld_u sv (a_ibs a) ipc L) rr oc' fs' tabs' ->
  is_error_code rr = true ->
  err_why a rr.

Definition LD3 : Prop :=
  P_load_cont_hist_st /\ P_load_cont_hist_buf /\ P_load_cont_stable /\ P_load_cont_buf /\ P_load_err_why.

End CM_L3Stmts_1.
