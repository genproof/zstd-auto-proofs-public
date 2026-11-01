(* valid_bufferless: the main's loop invariants and the statements of its two loop bodies.
   The frame loop (k over sr's frames) and, inside it, the step loop (ZSTD_nextSrcSizeToDecompress /
   ZSTD_decompressContinue on exactly the asked bytes). *)
Require Import VST.floyd.proofauto.
Require Export Zstd.proof.harness.valid_bufferless.VBLBuf.
Require Export Zstd.proof.harness.valid_bufferless.VBL3Model.

Local Notation ZCS := Zstd.proof.zstd.Base.CompSpecs.
Local Notation HCS := Zstd.proof.harness.valid_bufferless.HOK_valid_bufferless.CompSpecs.

(* ---------- the run's data ---------- *)

(* the dictionary: mode 0 none (db = []), modes 1 and 2 the bytes db of vb_wd, which the model loads as dm *)
Definition VL_dfacts (mode: Z) (db: list Z) (dm: dict_model) : Prop :=
  (mode = 0 /\ db = [] /\ dm = no_dict) \/
  (mode <> 0 /\ bytes_ok db /\ 8 <= Zlength db <= 2 ^ 12 + 2048 /\ dict_auto db = Some dm).

(* the DDict of mode 2 (q, made by copy from db), NULL otherwise *)
Definition VL_qok (mode: Z) (q: val) : Prop := (mode = 2 -> isptr q) /\ (mode <> 2 -> q = nullval).

(* v3.2: the DDict's state dd (createDDict's post gives it existentially): the bytes db, zstd's own copy *)
Definition VL_ddok (db: list Z) (dd: ddict_st) : Prop := dd_bytes dd = db /\ dd_ref dd = None.

Definition VL_qres (DD: globals -> val -> ddict_st -> mpred) (gv: globals) (q: val) (dd: ddict_st) : mpred :=
  if eq_dec q nullval then emp else (DD gv q dd && valid_pointer q).

(* the dictionary every frame is begun with (ZSTD_decompressBegin / _usingDict(dict, dn) / _usingDDict(q)) *)
Definition VL_dr (mode: Z) (q dict: val) (db: list Z) (dd: ddict_st) : option dictref :=
  if mode =? 0 then None
  else if mode =? 1 then Some {| dr_src := DSRef dict; dr_raw := false; dr_once := false; dr_bytes := db |}
  else Some (ddict_ref q dd).

(* frame k of the series *)
Definition VL_f (ws: wseries) (k: Z) : winfo := nth (Z.to_nat k) (ws_frames ws) winfo0.

Definition VL_sr (gv: globals) : val := gv _x_valid_bufferless__sr.

(* ---------- the resources of both loops ---------- *)

Section Sep.
Variable DC : globals -> val -> dctx_st -> mpred.
Variable DD : globals -> val -> ddict_st -> mpred.

(* src = exact_copy of sr.bytes (n bytes in a max(1,n) block), buf = [dst: cap | 1 | dict: dn] with the
   dictionary's bytes copied in, the context in state st, the output cells oc *)
Definition VL_sep (gv: globals) (ws: wseries) (db: list Z) (dd: ddict_st) (src buf dctx q: val) (st: dctx_st) (oc: list val)
    : list mpred :=
  [mem_mgr gv; zstd_globals gv; DC gv dctx st; VL_qres DD gv q dd;
   @data_at ZCS Ews (tarray tuchar (Zlength db)) (zbytes db) (offset_val (Zlength (ws_content ws) + 1) buf);
   pws_pred (VLB_W src (Zlength (ws_bytes ws)) buf (Zlength (ws_content ws)));
   @data_at ZCS Ews (tarray tuchar (Zlength (ws_content ws))) oc buf;
   @data_at ZCS Ews (tarray tuchar (Zlength (ws_bytes ws))) (zbytes (ws_bytes ws)) src;
   @malloc_token HCS Ews (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws)))) src;
   @malloc_token HCS Ews (tarray tuchar (Zlength (ws_content ws) + 1 + Zlength db)) buf;
   @data_at HCS Ews t_wseries (wseries_val ws) (VL_sr gv);
   TT].

(* the locals both loops keep *)
Definition VL_loc (gv: globals) (ws: wseries) (db: list Z) (mode: Z) (src buf dctx q: val) : list localdef :=
  [temp _ddict q; temp _dctx dctx; temp _dst buf; temp _buf buf;
   temp _dict (offset_val (Zlength (ws_content ws) + 1) buf); temp _src src;
   temp _cap (Vlong (Int64.repr (Zlength (ws_content ws)))); temp _dn (Vlong (Int64.repr (Zlength db)));
   temp _mode (Vint (Int.repr mode)); gvars gv].

(* the frame loop, at its head: frames 0..k-1 done (stp = 0) or the run stopped (stp = 1); a buffer-less
   frame obl possibly begun; ex, the context's dc_ex (true only before the first ZSTD_decompressBegin*: the
   buffer-less calls clear it) *)
Definition VL_outer (gv: globals) (ws: wseries) (db: list Z) (dd: ddict_st) (mode: Z) (src buf dctx q: val) : environ -> mpred :=
  EX k: Z, EX stp: Z, EX ipos: Z, EX pos: Z, EX obl: option blabs, EX oc: list val, EX ex: bool,
  PROPx [0 <= k <= Zlength (ws_frames ws); stp = 0 \/ stp = 1; Zlength oc = Zlength (ws_content ws);
         stp = 0 -> VL_qok mode q /\
           (k < Zlength (ws_frames ws) -> ipos = wi_start (VL_f ws k) /\ pos = wi_cstart (VL_f ws k))]
  (LOCALx (temp _k (Vint (Int.repr k)) :: temp _stop (Vint (Int.repr stp)) :: temp _ipos (Vlong (Int64.repr ipos)) ::
           temp _pos (Vlong (Int64.repr pos)) :: VL_loc gv ws db mode src buf dctx q)
  (SEPx (VL_sep gv ws db dd src buf dctx q (set_ex (set_bl dctx_init obl) ex) oc))).

(* the frame loop's body done for frame k (before k++) *)
Definition VL_cont (gv: globals) (ws: wseries) (db: list Z) (dd: ddict_st) (mode: Z) (src buf dctx q: val) : environ -> mpred :=
  EX k: Z, EX stp: Z, EX ipos: Z, EX pos: Z, EX obl: option blabs, EX oc: list val, EX ex: bool,
  PROPx [0 <= k < Zlength (ws_frames ws); stp = 0 \/ stp = 1; Zlength oc = Zlength (ws_content ws);
         stp = 0 -> VL_qok mode q /\
           (k + 1 < Zlength (ws_frames ws) -> ipos = wi_start (VL_f ws (k + 1)) /\ pos = wi_cstart (VL_f ws (k + 1)))]
  (LOCALx (temp _k (Vint (Int.repr k)) :: temp _stop (Vint (Int.repr stp)) :: temp _ipos (Vlong (Int64.repr ipos)) ::
           temp _pos (Vlong (Int64.repr pos)) :: VL_loc gv ws db mode src buf dctx q)
  (SEPx (VL_sep gv ws db dd src buf dctx q (set_ex (set_bl dctx_init obl) ex) oc))).

(* after the frame loop *)
Definition VL_exit (gv: globals) (ws: wseries) (db: list Z) (dd: ddict_st) (mode: Z) (src buf dctx q: val) : environ -> mpred :=
  EX obl: option blabs, EX oc: list val, EX ex: bool,
  PROPx [Zlength oc = Zlength (ws_content ws)]
  (LOCALx (VL_loc gv ws db mode src buf dctx q)
  (SEPx (VL_sep gv ws db dd src buf dctx q (set_ex (set_bl dctx_init obl) ex) oc))).

(* the step loop of frame k (stop = 0), at its head: the frame's first i bytes fed, the model in state b,
   its output so far right before dst + pos; the frame is begun, so dc_ex is false *)
Definition VL_inner (gv: globals) (ws: wseries) (db: list Z) (dd: ddict_st) (dm: dict_model) (mode: Z) (src buf dctx q: val)
    (k: Z) : environ -> mpred :=
  EX i: Z, EX b: blst, EX ba: blabs, EX oc: list val,
  PROPx [vbl_reach dm (wi_bytes ws (VL_f ws k)) i b; ba_st ba = Some b; ba_expect ba = bs_expect b;
         ba_dict ba = VL_dr mode q (offset_val (Zlength (ws_content ws) + 1) buf) db dd;
         bl_hist_ok ba buf (Zlength (ws_content ws)) (wi_cstart (VL_f ws k) + Zlength (bs_out b)) oc; Zlength oc = Zlength (ws_content ws)]
  (LOCALx (temp _k (Vint (Int.repr k)) :: temp _stop (Vint (Int.repr 0)) ::
           temp _ipos (Vlong (Int64.repr (wi_start (VL_f ws k) + i))) ::
           temp _pos (Vlong (Int64.repr (wi_cstart (VL_f ws k) + Zlength (bs_out b)))) ::
           temp _end (Vlong (Int64.repr (wi_start (VL_f ws k) + wi_size (VL_f ws k)))) ::
           temp _cend (Vlong (Int64.repr (wi_cstart (VL_f ws k) + wi_csize (VL_f ws k)))) ::
           temp _f (field_address t_wseries [ArraySubsc k; StructField _f] (VL_sr gv)) ::
           VL_loc gv ws db mode src buf dctx q)
  (SEPx (VL_sep gv ws db dd src buf dctx q (set_ex (set_bl dctx_init (Some ba)) false) oc))).

(* after the step loop of frame k: the frame fully decoded (stp = 0), or the run stopped *)
Definition VL_inner_exit (gv: globals) (ws: wseries) (db: list Z) (dd: ddict_st) (mode: Z) (src buf dctx q: val) (k: Z)
    : environ -> mpred :=
  EX stp: Z, EX ipos: Z, EX pos: Z, EX obl: option blabs, EX oc: list val, EX ex: bool,
  PROPx [stp = 0 \/ stp = 1; Zlength oc = Zlength (ws_content ws);
         stp = 0 -> ipos = wi_start (VL_f ws k) + wi_size (VL_f ws k) /\
                    pos = wi_cstart (VL_f ws k) + wi_csize (VL_f ws k)]
  (LOCALx (temp _k (Vint (Int.repr k)) :: temp _stop (Vint (Int.repr stp)) :: temp _ipos (Vlong (Int64.repr ipos)) ::
           temp _pos (Vlong (Int64.repr pos)) :: VL_loc gv ws db mode src buf dctx q)
  (SEPx (VL_sep gv ws db dd src buf dctx q (set_ex (set_bl dctx_init obl) ex) oc))).

End Sep.

(* ---------- the context and the statements ---------- *)

Section G.
Variable DC : globals -> val -> dctx_st -> mpred.
Variable DD : globals -> val -> ddict_st -> mpred.
Variable WG : globals -> mpred.
Variable WDS : wdict -> reptype t_wstate -> Prop.

(* the functions main calls (lifted to G0 at the end) *)
Definition VL_G1 : funspecs :=
  [(_quickproof_malloc, malloc_spec'); (_quickproof_free, free_spec');
   ZSTD_isError_spec; ZSTD_createDCtx_spec DC; ZSTD_freeDCtx_spec DC; ZSTD_createDDict_spec DD; ZSTD_freeDDict_spec DD;
   ZSTD_decompressBegin_aspec DC; ZSTD_decompressBegin_usingDict_aspec DC; ZSTD_decompressBegin_usingDDict_aspec DC DD;
   ZSTD_nextSrcSizeToDecompress_aspec DC; ZSTD_nextInputType_aspec DC; ZSTD_decompressContinue_aspec DC DD;
   gp_assert_spec;
   choose_spec; exact_copy_spec; within_oneshot_spec; w_dict_spec WG WDS; w_series_spec WG WDS].
End G.

(* the frame loop's body after its test (k < nframes && !stop): frame k from f = &sr.f[k] to the end of its
   step loop *)
Definition VL_frame_s : statement := ltac:(
  let b := eval cbv delta [f_main fn_body] beta iota in (fn_body f_main) in
  lazymatch b with context [Sloop (Ssequence (Ssequence _ (Sifthenelse (Etempvar _x_valid_bufferless__t'8 _) Sskip Sbreak)) ?fr)
                                  (Sset _k _)] => exact fr end).

(* the step loop's body *)
Definition VL_inner_s : statement := ltac:(
  let b := eval cbv delta [f_main fn_body] beta iota in (fn_body f_main) in
  lazymatch b with context [Sloop (Ssequence Sskip ?x) Sskip] => exact x end).

(* the facts both bodies use, gathered *)
Definition VL_hyps (gv: globals) (ws: wseries) (db: list Z) (dm: dict_model) (mode: Z) (src buf dctx q: val)
    : Prop :=
  0 <= mode < 3 /\ series_facts dm ws /\ wseries_wf ws /\ VL_dfacts mode db dm /\
  (exists bs os, src = Vptr bs os) /\ (exists bb ob, buf = Vptr bb ob) /\ (exists bd od, dctx = Vptr bd od) /\
  field_compatible (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws)))) [] src /\
  field_compatible (tarray tuchar (Zlength (ws_content ws) + 1 + Zlength db)) [] buf.

(* the step loop's body: from VL_inner back to VL_inner, or out (break) to VL_inner_exit *)
Definition VL_inner_stmt : Prop :=
  forall {Espec: OracleKind} DC DD WG WDS gv ws db dd dm mode src buf dctx q k (R: ret_assert),
  VL_hyps gv ws db dm mode src buf dctx q -> 0 <= k < Zlength (ws_frames ws) -> VL_qok mode q -> VL_ddok db dd ->
  semax (func_tycontext f_main Vprog (VL_G1 DC DD WG WDS) nil)
    (VL_inner DC DD gv ws db dd dm mode src buf dctx q k)
    VL_inner_s
    (loop1_ret_assert (VL_inner DC DD gv ws db dd dm mode src buf dctx q k)
       (overridePost (VL_inner_exit DC DD gv ws db dd mode src buf dctx q k) R)).

(* the frame loop's body after its test: frame k begun, its steps, to VL_cont (or out, break, when the
   frame's ZSTD_decompressBegin* fails) *)
Definition VL_frame_stmt : Prop :=
  forall {Espec: OracleKind} DC DD WG WDS gv ws db dd dm mode src buf dctx q k ipos pos obl oc ex (R: ret_assert),
  VL_hyps gv ws db dm mode src buf dctx q -> 0 <= k < Zlength (ws_frames ws) -> VL_qok mode q -> VL_ddok db dd ->
  ipos = wi_start (VL_f ws k) -> pos = wi_cstart (VL_f ws k) -> Zlength oc = Zlength (ws_content ws) ->
  semax (func_tycontext f_main Vprog (VL_G1 DC DD WG WDS) nil)
    (PROPx []
     (LOCALx (temp _k (Vint (Int.repr k)) :: temp _stop (Vint (Int.repr 0)) :: temp _ipos (Vlong (Int64.repr ipos)) ::
              temp _pos (Vlong (Int64.repr pos)) :: VL_loc gv ws db mode src buf dctx q)
     (SEPx (VL_sep DC DD gv ws db dd src buf dctx q (set_ex (set_bl dctx_init obl) ex) oc))))
    VL_frame_s
    (loop1_ret_assert (VL_cont DC DD gv ws db dd mode src buf dctx q)
       (overridePost (VL_exit DC DD gv ws db dd mode src buf dctx q) R)).
