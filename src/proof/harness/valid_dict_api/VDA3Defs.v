(* valid_dict_api main: the shared interface of the main's segments.
   The main is proved in the small context VDA_G1 (lifted to G0 in WMain3_valid_dict_api.v) by composing:
     VDA_pro_ok   : from the start of main's body to the allocation check (state VDA_B);
     (assembly)   : the allocation check (early return) and the copy of the dictionary (state VDA_A);
     VDA_mode_ok m: the setup of mode m and its decoding (VDA_setup_s; VDA_dec_s), from VDA_A to VDA_E;
     VDA_epi_ok   : the frees and the return (VDA_epi_s), from VDA_E. *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.harness.valid_dict_api.WTopSpecs_valid_dict_api.

Local Notation ZCS := Zstd.proof.zstd.Base.CompSpecs.
Local Notation HCS := Zstd.proof.harness.valid_dict_api.HOK_valid_dict_api.CompSpecs.

(* ---------- the statements ---------- *)

(* after the allocation check: the dictionary copy loop, the setup, the decoding, the epilogue *)
Definition VDA_parts : statement * statement * statement * statement := ltac:(
  let b := eval cbv delta [f_main fn_body] beta iota in (fn_body f_main) in
  lazymatch b with
  | context [Ssequence (Ssequence (Sset _j ?z) (Sloop ?lb ?li))
               (Ssequence (Sifthenelse ?c (Ssequence (Ssequence (Scall ?o (Evar _ZSTD_DCtx_setParameter ?ft) ?args) ?s1) ?s2) ?e)
                 (Ssequence ?dec ?epi))] =>
      exact (Ssequence (Sset _j z) (Sloop lb li),
             Sifthenelse c (Ssequence (Ssequence (Scall o (Evar _ZSTD_DCtx_setParameter ft) args) s1) s2) e,
             dec, epi)
  end).
Definition VDA_copy_s : statement := ltac:(let x := eval cbv [VDA_parts fst snd] in (fst (fst (fst VDA_parts))) in exact x).
Definition VDA_setup_s : statement := ltac:(let x := eval cbv [VDA_parts fst snd] in (snd (fst (fst VDA_parts))) in exact x).
Definition VDA_dec_s : statement := ltac:(let x := eval cbv [VDA_parts fst snd] in (snd (fst VDA_parts)) in exact x).
Definition VDA_epi_s : statement := ltac:(let x := eval cbv [VDA_parts fst snd] in (snd VDA_parts) in exact x).

(* from the allocation check to the end of main's body *)
Definition VDA_rest_s : statement := ltac:(
  let b := eval cbv delta [f_main fn_body] beta iota in (fn_body f_main) in
  lazymatch b with
  | context [Ssequence (Ssequence (Ssequence (Sifthenelse (Ebinop Oeq (Etempvar _src ?t1) ?n1 ?t2) ?a1 ?b1) ?a2) ?a3) ?rest] =>
      exact (Ssequence (Ssequence (Ssequence (Sifthenelse (Ebinop Oeq (Etempvar _src t1) n1 t2) a1 b1) a2) a3) rest)
  end).

Lemma VDA_rest_eq : VDA_rest_s = Ssequence (Ssequence (Ssequence (Sifthenelse (Ebinop Oeq (Etempvar _src (tptr tuchar)) (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint) (Sset _x_valid_dict_api__t'14 (Econst_int (Int.repr 1) tint)) (Sset _x_valid_dict_api__t'14 (Ecast (Ebinop Oeq (Etempvar _buf (tptr tuchar)) (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint) tbool))) (Sifthenelse (Etempvar _x_valid_dict_api__t'14 tint) (Sset _x_valid_dict_api__t'15 (Econst_int (Int.repr 1) tint)) (Sset _x_valid_dict_api__t'15 (Ecast (Ebinop Oeq (Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr))) (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint) tbool)))) (Sifthenelse (Etempvar _x_valid_dict_api__t'15 tint) (Ssequence (Scall None (Evar _quickproof_free (Tfunction ((tptr tvoid) :: nil) tvoid cc_default)) ((Etempvar _src (tptr tuchar)) :: nil)) (Ssequence (Scall None (Evar _quickproof_free (Tfunction ((tptr tvoid) :: nil) tvoid cc_default)) ((Etempvar _buf (tptr tuchar)) :: nil)) (Ssequence (Scall None (Evar _ZSTD_freeDCtx (Tfunction ((tptr (Tstruct _ZSTD_DCtx_s noattr)) :: nil) tulong cc_default)) ((Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr))) :: nil)) (Sreturn (Some (Econst_int (Int.repr 0) tint)))))) Sskip)) (Ssequence VDA_copy_s (Ssequence VDA_setup_s (Ssequence VDA_dec_s VDA_epi_s))).
Proof. reflexivity. Qed.

(* ---------- the model-level facts the prologue establishes ---------- *)

Definition t_ddp : type := tarray (tptr t_ddict) 3.

(* the address of vd_wd[i] *)
Definition vda_wd_addr (gv: globals) (i: Z) : val := offset_val (i * @sizeof HCS t_wdict) (gv _vd_wd).

(* the dictionary the series is written for: mode 2 writes it for the raw content of wd's bytes (vd_raw) *)
Definition vda_dm (mode: Z) (wd: wdict) : dict_model := if mode =? 2 then dict_raw (wd_bytes wd) else wd_model wd.

(* after the prologue: the mode, the nd dictionaries wds of vd_wd (wd = wds[which] the series' one), the series ws,
   the one-shot capacity cap; with every gp_assume of the prologue *)
Definition vda_facts (mode nd which: Z) (wds: list wdict) (wd: wdict) (ws: wseries) (cap: Z) : Prop :=
  0 <= mode < 7 /\ Zlength wds = nd /\ (if mode =? 0 then 2 <= nd <= 3 else nd = 1) /\
  0 <= which < nd /\ (mode <> 0 -> which = 0) /\ nth_error wds (Z.to_nat which) = Some wd /\
  Forall dict_facts wds /\ Forall wdict_wf wds /\
  (mode = 0 -> Forall (fun w => wd_formatted w = true /\ wd_id w <> 0) wds /\ NoDup (map wd_id wds)) /\
  (mode = 1 \/ mode = 3 \/ mode = 4 -> wd_formatted wd = false) /\
  (mode = 2 -> wd_formatted wd = true /\ Zlength (wd_bytes wd) <= 4096) /\
  series_facts (vda_dm mode wd) ws /\ wseries_wf ws /\
  (mode = 0 -> Forall (fun f => wi_skippable f = true \/ (wi_did_size f <> 0 /\ wi_did f = wd_id wd)) (ws_frames ws)) /\
  (mode = 4 -> Zlength (ws_frames ws) = 1 /\ wi_skippable (hd winfo0 (ws_frames ws)) = false) /\
  (mode = 5 \/ mode = 6 -> cap = 0) /\ 0 <= cap <= Zlength (ws_content ws) + 16 /\
  series_dwin (vda_dm mode wd) ws.

(* mode 0's model fact (VDA3M0Model.v): the DDict set the setup leaves (the dictionaries of vd_wd, in order, made by
   copy, with the parameter refMultipleDDicts on) describes the series as wd does, for streaming (vds_desc) and for
   one-shot decoding (ZSTD_decompressDCtx's oneshot_dctx with a set: oneshot_sel under st_sel) *)
Definition VDA_m0_model : Prop :=
  forall (wds: list wdict) (wd: wdict) (ws: wseries) (st: dctx_st),
    In wd wds -> Forall dict_facts wds -> Forall (fun w => wd_id w <> 0) wds -> NoDup (map wd_id wds) ->
    series_facts (wd_model wd) ws -> wseries_wf ws -> series_dwin (wd_model wd) ws ->
    Forall (fun f => wi_skippable f = true \/ (wi_did_size f <> 0 /\ wi_did f = wd_id wd)) (ws_frames ws) ->
    dc_par st = {| dp_fmt := 0; dp_ignore := 0; dp_bmax := 0; dp_wmax := dp_wmax_dflt; dp_multi := 1 |} ->
    match dc_dict st with Some dr => match dr_src dr with DSDDict _ _ => True | _ => False end | None => False end ->
    map (fun e => dd_bytes (snd e)) (dc_set st) = map wd_bytes wds ->
    vds_desc st (wd_model wd) (ws_bytes ws) /\
    decode_series_m (dmode_of (dc_par st)) (fst (st_sel st)) (snd (st_sel st)) no_wlim (ws_bytes ws) =
      decode_series (wd_model wd) no_wlim (ws_bytes ws).

(* ---------- the context: the functions main calls ---------- *)

Section Ctx.
Variable DC : globals -> val -> dctx_st -> mpred.
Variable DD : globals -> val -> ddict_st -> mpred.
Variable WG : globals -> mpred.
Variable WDS : wdict -> reptype t_wstate -> Prop.

Definition VDA_G1 : funspecs :=
  [(_quickproof_malloc, malloc_spec'); (_quickproof_free, free_spec');
   ZSTD_isError_spec; ZSTD_getErrorCode_spec; ZSTD_decompressDCtx_spec DC DD;
   ZSTD_createDCtx_spec DC; ZSTD_freeDCtx_spec DC; ZSTD_DCtx_setParameter_spec DC; ZSTD_resetDStream_aspec DC;
   ZSTD_createDDict_spec DD; ZSTD_freeDDict_spec DD; ZSTD_DCtx_refDDict_spec DC DD;
   ZSTD_DCtx_loadDictionary_advanced_aspec DC; ZSTD_DCtx_refPrefix_advanced_aspec DC;
   ZSTD_initDStream_usingDict_aspec DC; ZSTD_initDStream_usingDDict_aspec DC DD;
   gp_assert_spec; gp_assume_spec;
   choose_spec; choose_in_spec; exact_copy_spec; within_oneshot_spec; w_dict_spec WG WDS; w_series_spec WG WDS;
   vd_stream_spec DC DD].

Definition VDA_Delta : tycontext := func_tycontext f_main Vprog VDA_G1 nil.

(* main's return: TT, and its stack frame (the array dd) *)
Definition VDA_R : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint (PROP () RETURN () SEP (TT))) (stackframe_of f_main).

(* ---------- the states between the segments ---------- *)

(* the dictionaries vd_wd[i], i < |l| *)
Fixpoint vda_wds_from (gv: globals) (i: Z) (l: list wdict) : mpred :=
  match l with
  | nil => emp
  | w :: l' => sepcon (wdict_rep WDS Ews w (vda_wd_addr gv i)) (vda_wds_from gv (i + 1) l')
  end.

(* VDA_B: at the allocation check (the end of VDA_pro_ok); src, buf, dctx may be NULL *)
Definition VDA_B (gv: globals) (v_dd: val) (mode nd which: Z) (wds: list wdict) (wd: wdict) (ws: wseries) (cap: Z)
    (src buf dctx: val) : environ -> mpred :=
  PROP (vda_facts mode nd which wds wd ws cap; is_pointer_or_null src; is_pointer_or_null buf;
        is_pointer_or_null dctx)
  LOCAL (temp _mode (Vint (Int.repr mode)); temp _nd (Vint (Int.repr nd)); temp _cap (Vlong (Int64.repr cap));
         temp _fail (Vint (Int.repr 0)); temp _wd (vda_wd_addr gv which); temp _src src; temp _buf buf; temp _dst buf;
         temp _dict (if eq_dec buf nullval then nullval else offset_val (cap + 1) buf); temp _dctx dctx;
         temp _dn (Vlong (Int64.repr (Zlength (wd_bytes wd)))); lvar _dd t_ddp v_dd; gvars gv)
  SEP (mem_mgr gv; zstd_globals gv; (if eq_dec dctx nullval then emp else andp (DC gv dctx dctx_init) (valid_pointer dctx));
       @data_at HCS Ews t_wseries (wseries_val ws) (gv _x_valid_dict_api__sr);
       vda_wds_from gv 0 wds;
       (if eq_dec src nullval then emp else
          sepcon (@malloc_token HCS Ews (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws)))) src)
                 (@data_at HCS Ews (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws))))
                    (zbytes (ws_bytes ws) ++ Zrepeat Vundef (Z.max 1 (Zlength (ws_bytes ws)) - Zlength (ws_bytes ws))) src));
       (if eq_dec buf nullval then emp else
          sepcon (@malloc_token HCS Ews (tarray tuchar (cap + 1 + Zlength (wd_bytes wd))) buf)
                 (@data_at_ HCS Ews (tarray tuchar (cap + 1 + Zlength (wd_bytes wd))) buf));
       @data_at HCS Tsh t_ddp (Zrepeat nullval 3) v_dd;
       TT).

(* VDA_A: after the dictionary's copy into [dst | 1 | dict] (buf = dst, dict = buf + cap + 1), before the setup *)
Definition VDA_A (gv: globals) (v_dd: val) (mode nd which: Z) (wds: list wdict) (wd: wdict) (ws: wseries) (cap: Z)
    (src buf dctx: val) : environ -> mpred :=
  PROP (vda_facts mode nd which wds wd ws cap; isptr src; isptr buf; isptr dctx;
        field_compatible (tarray tuchar (cap + 1 + Zlength (wd_bytes wd))) [] buf;
        field_compatible (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws)))) [] src)
  LOCAL (temp _mode (Vint (Int.repr mode)); temp _nd (Vint (Int.repr nd)); temp _cap (Vlong (Int64.repr cap));
         temp _fail (Vint (Int.repr 0)); temp _src src; temp _buf buf; temp _dst buf;
         temp _dict (offset_val (cap + 1) buf); temp _dctx dctx;
         temp _dn (Vlong (Int64.repr (Zlength (wd_bytes wd)))); lvar _dd t_ddp v_dd; gvars gv)
  SEP (mem_mgr gv; zstd_globals gv; DC gv dctx dctx_init;
       @data_at HCS Ews t_wseries (wseries_val ws) (gv _x_valid_dict_api__sr);
       vda_wds_from gv 0 wds;
       @malloc_token HCS Ews (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws)))) src;
       @data_at HCS Ews (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws))))
         (zbytes (ws_bytes ws) ++ Zrepeat Vundef (Z.max 1 (Zlength (ws_bytes ws)) - Zlength (ws_bytes ws))) src;
       @malloc_token HCS Ews (tarray tuchar (cap + 1 + Zlength (wd_bytes wd))) buf;
       @data_at_ HCS Ews (tarray tuchar (cap + 1)) buf;
       @data_at HCS Ews (tarray tuchar (Zlength (wd_bytes wd))) (zbytes (wd_bytes wd)) (offset_val (cap + 1) buf);
       @data_at HCS Tsh t_ddp (Zrepeat nullval 3) v_dd;
       TT).

(* the DDicts of dd[] (NULL: none) *)
Definition dd_res (gv: globals) (ddv: list val) : mpred :=
  fold_right sepcon emp (map (fun v => if eq_dec v nullval then emp else EX x: ddict_st, DD gv v x) ddv).

(* VDA_E: after the decoding, before the frees (n = |series|, dn = |dictionary|) *)
Definition VDA_E (gv: globals) (v_dd: val) (n cap dn: Z) (src buf dctx: val) (st: dctx_st) (ddv: list val)
    : environ -> mpred :=
  PROP (Zlength ddv = 3; Forall is_pointer_or_null ddv; isptr src; isptr buf; isptr dctx)
  LOCAL (temp _dctx dctx; temp _src src; temp _buf buf; lvar _dd t_ddp v_dd; gvars gv)
  SEP (mem_mgr gv; zstd_globals gv; DC gv dctx st; @data_at HCS Tsh t_ddp ddv v_dd; dd_res gv ddv;
       @malloc_token HCS Ews (tarray tuchar (Z.max 1 n)) src; @data_at_ HCS Ews (tarray tuchar (Z.max 1 n)) src;
       @malloc_token HCS Ews (tarray tuchar (cap + 1 + dn)) buf; @data_at_ HCS Ews (tarray tuchar (cap + 1 + dn)) buf;
       TT).

(* ---------- the segments' obligations ---------- *)

(* the prologue: main's start (its static data, WG from HWG) to the allocation check *)
Definition VDA_pro_ok : Prop :=
  (forall gv, InitGPred wvardefs gv |-- WG gv) ->
  (forall (Espec: OracleKind) gv v_dd mode nd which wds wd ws cap src buf dctx,
     @semax HCS Espec VDA_Delta (VDA_B gv v_dd mode nd which wds wd ws cap src buf dctx)
       (Ssequence VDA_rest_s (Sreturn (Some (Econst_int (Int.repr 0) tint)))) VDA_R) ->
  semax_body Vprog VDA_G1 f_main main_spec.

(* mode m: its setup and its decoding *)
Definition VDA_mode_ok (m: Z) : Prop :=
  forall (Espec: OracleKind) gv v_dd nd which wds wd ws cap src buf dctx,
    @semax HCS Espec VDA_Delta (VDA_A gv v_dd m nd which wds wd ws cap src buf dctx)
      (Ssequence VDA_setup_s VDA_dec_s)
      (normal_ret_assert (EX st: dctx_st, EX ddv: list val,
         VDA_E gv v_dd (Zlength (ws_bytes ws)) cap (Zlength (wd_bytes wd)) src buf dctx st ddv)).

(* the frees and the return *)
Definition VDA_epi_ok : Prop :=
  forall (Espec: OracleKind) gv v_dd n cap dn src buf dctx st ddv,
    @semax HCS Espec VDA_Delta (VDA_E gv v_dd n cap dn src buf dctx st ddv) VDA_epi_s VDA_R.

End Ctx.
