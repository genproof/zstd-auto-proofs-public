(* main of harness/valid_params.c: the shared definitions of its proof, cut into segments (CPS).
   main's body is the chain s0; ...; s19 (VP_body0) followed by `return 0` (VP_ret):
     A  s0..s11   mode, w_series, mode 0's checksum replacement, mode 3's gp_assume, src = exact_copy, dctx
     B  s12..s14  the parameter of the mode (mode 2: gp_assume(vp_blocks_within(blim))), gp_assert(documented ->
                  success), the error exit
     C  s15       mode 3: ZSTD_getFrameHeader_advanced and its asserts
     D  s16       one-shot (D1) or streaming (D2), on a mode-independent view of the series (VP_dfacts)
     E  s17..     ZSTD_freeDCtx, free(src), return 0
   Each segment lemma is stated in the context VP_Delta (only the functions main calls; lifted to MainOK's G0 in
   WMain3_valid_params.v).  The states between segments are VP_SA, VP_SB (and VP_SD0/VP_SD1 for D). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Export Zstd.proof.harness.valid_params.WTopSpecs_valid_params.
Require Export Zstd.proof.harness.valid_params.VPStream.


Local Notation HCS := Zstd.proof.harness.valid_params.HOK_valid_params.CompSpecs.
Local Notation ZCS := Zstd.proof.zstd.Base.CompSpecs.
Local Notation tout := (Tstruct _ZSTD_outBuffer_s noattr).
Local Notation tin := (Tstruct _ZSTD_inBuffer_s noattr).

(* ---------- the statements ---------- *)

Definition VP_body0 : statement := ltac:(
  let b := eval cbv delta [f_main fn_body] beta iota in (fn_body f_main) in
  lazymatch b with Ssequence ?x _ => exact x end).
Definition VP_ret : statement := ltac:(
  let b := eval cbv delta [f_main fn_body] beta iota in (fn_body f_main) in
  lazymatch b with Ssequence _ ?y => exact y end).

Fixpoint VP_drop (k: nat) (s: statement) : statement :=
  match k with O => s | S k' => match s with Ssequence _ b => VP_drop k' b | _ => s end end.

(* the statements from s_k to the end of main *)
Definition VP_rest (k: nat) : statement := Ssequence (VP_drop k VP_body0) VP_ret.

Lemma VP_rest0 : fn_body f_main = VP_rest 0.
Proof. reflexivity. Qed.

(* s16 = choose(2); if (.) VP_oneshot_s else VP_stream_s *)
Definition VP_s17_parts : statement * statement := ltac:(
  let s := eval cbv [VP_drop VP_body0] in (VP_drop 16 VP_body0) in
  lazymatch s with Ssequence (Ssequence _ (Sifthenelse _ ?a ?b)) _ => exact (a, b) end).
Definition VP_s16 : statement := ltac:(
  let s := eval cbv [VP_drop VP_body0] in (VP_drop 16 VP_body0) in
  lazymatch s with Ssequence ?x _ => exact x end).
Definition VP_oneshot_s : statement := ltac:(let x := eval cbv [VP_s17_parts fst] in (fst VP_s17_parts) in exact x).
Definition VP_stream_s : statement := ltac:(let x := eval cbv [VP_s17_parts snd] in (snd VP_s17_parts) in exact x).

(* main's return: anything (main_spec's post is TT), with main's stack frame *)
Definition VP_RR : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint (PROP () RETURN () SEP (TT))) (stackframe_of f_main).

(* ---------- the view of the series per mode ---------- *)

Definition vp_base (mode: Z) : Z := if mode =? 3 then 4 else 0.
(* the bytes main gives zstd: sr.bytes (b', checksums replaced in mode 0) from base *)
Definition vp_src (mode: Z) (b': list Z) : list Z := sublist (vp_base mode) (Zlength b') b'.
(* the series as zstd sees it (VPModel.vp_written) *)
Definition vp_view (mode: Z) (ws: wseries) (b': list Z) : wseries :=
  if mode =? 3 then ws_unmagic ws else ws_ck ws b'.

(* after A: the series ws written by w_series (no dictionary), sr's bytes b' *)
Definition VP_SA_facts (mode: Z) (ws: wseries) (b': list Z) : Prop :=
  0 <= mode < 4 /\ series_facts no_dict ws /\ wseries_wf ws /\ ck_agree (ws_frames ws) (ws_bytes ws) b' /\
  (mode <> 0 -> b' = ws_bytes ws) /\
  (mode = 3 -> exists f, ws_frames ws = [f] /\ wi_skippable f = false) /\
  0 < Zlength (vp_src mode b').

(* what D needs, independently of the mode: sr holds wsr, zstd decodes ws' (bytes from base of wsr's) under the
   parameters p; wlim is main's temp *)
Definition VP_dfacts (wsr ws': wseries) (p: dparams) (base wlim: Z) : Prop :=
  vp_written (dmode_of p) ws' /\
  ws_content ws' = ws_content wsr /\
  ws_bytes ws' = sublist base (Zlength (ws_bytes wsr)) (ws_bytes wsr) /\
  (base = 0 \/ base = 4) /\ 0 < Zlength (ws_bytes ws') /\
  bytes_ok (ws_bytes wsr) /\ bytes_ok (ws_content wsr) /\
  Zlength (ws_bytes wsr) <= 2 ^ 19 /\ Zlength (ws_content wsr) <= 2 ^ 18 /\
  (1 <= length (ws_frames wsr) <= 4)%nat /\ wseries_wf wsr /\
  Forall (fun f => base <= wi_start f + wi_size f <= Zlength (ws_bytes wsr) /\
                   0 <= wi_cstart f /\ 0 <= wi_csize f /\ wi_cstart f + wi_csize f <= Zlength (ws_content wsr))
    (ws_frames wsr) /\
  0 <= wlim <= Int64.max_unsigned /\
  (* one-shot: within_oneshot *)
  (within_oneshot_b (ws_frames wsr) = true -> all_ok no_wlim (ws_frames ws') = true) /\
  (* streaming: within_oneshot && vp_windows_within(wlim) *)
  (within_oneshot_b (ws_frames wsr) = true -> windows_within_b (ws_frames wsr) wlim = true ->
     all_ok (dp_wmax p) (ws_frames ws') = true) /\
  (* main's at_end check on sr's frames *)
  (forall ipos got, h_at_end (ws_frames ws') ipos got =
     existsb (fun f => andb (wi_start f + wi_size f - base =? ipos) (got =? wi_cstart f + wi_csize f)) (ws_frames wsr)).

(* after B: the parameters p are set *)
Definition VP_SB_facts (mode: Z) (ws: wseries) (b': list Z) (p: dparams) (wlim: Z) : Prop :=
  VP_SA_facts mode ws b' /\
  VP_dfacts (ws_ck ws b') (vp_view mode ws b') p (vp_base mode) wlim /\
  ws_bytes (vp_view mode ws b') = vp_src mode b' /\
  (mode = 3 -> forall f, ws_frames ws = [f] ->
     get_frame_header_m true (vp_src mode b') = if wi_big f then FH_err else FH_ok (fh_unshift (wi_header f))).

Section States.
Variable DC : globals -> val -> dctx_st -> mpred.
Variable WG : globals -> mpred.

(* main's state after main_pre and the stack frame *)
Definition VP_S0 (gv: globals) (vz vi vo: val) : environ -> mpred :=
  PROP ()
  LOCAL (lvar _zfh t_fh vz; lvar _in tin vi; lvar _out tout vo; gvars gv)
  SEP (mem_mgr gv; zstd_globals gv; WG gv; data_at Ews t_wseries (zero_val t_wseries) (gv _x_valid_params__sr);
       data_at_ Tsh t_fh vz; data_at_ Tsh tin vi; data_at_ Tsh tout vo; TT; has_ext tt).

Definition VP_SA (gv: globals) (vz vi vo: val) (mode: Z) (ws: wseries) (b': list Z) (src dctx: val)
    : environ -> mpred :=
  PROP (VP_SA_facts mode ws b'; isptr src; isptr dctx)
  LOCAL (temp _mode (Vint (Int.repr mode)); temp _wlim (vl (2 ^ 27)); temp _blim (vl (2 ^ 17));
         temp _base (vl (vp_base mode)); temp _documented (Vint (Int.repr 1));
         temp _n (vl (Zlength (vp_src mode b'))); temp _src src; temp _dctx dctx;
         lvar _zfh t_fh vz; lvar _in tin vi; lvar _out tout vo; gvars gv)
  SEP (mem_mgr gv; zstd_globals gv; WG gv; DC gv dctx dctx_init;
       data_at Ews t_wseries (wseries_val (ws_ck ws b')) (gv _x_valid_params__sr);
       malloc_token Ews (tarray tuchar (Zlength (vp_src mode b'))) src;
       data_at Ews (tarray tuchar (Zlength (vp_src mode b'))) (zbytes (vp_src mode b')) src;
       data_at_ Tsh t_fh vz; data_at_ Tsh tin vi; data_at_ Tsh tout vo; TT; has_ext tt).

Definition VP_SB (gv: globals) (vz vi vo: val) (mode: Z) (ws: wseries) (b': list Z) (p: dparams) (wlim: Z)
    (src dctx: val) : environ -> mpred :=
  PROP (VP_SB_facts mode ws b' p wlim; isptr src; isptr dctx)
  LOCAL (temp _mode (Vint (Int.repr mode)); temp _wlim (vl wlim);
         temp _base (vl (vp_base mode)); temp _n (vl (Zlength (vp_src mode b'))); temp _src src; temp _dctx dctx;
         lvar _zfh t_fh vz; lvar _in tin vi; lvar _out tout vo; gvars gv)
  SEP (mem_mgr gv; zstd_globals gv; WG gv; DC gv dctx (set_par dctx_init p);
       data_at Ews t_wseries (wseries_val (ws_ck ws b')) (gv _x_valid_params__sr);
       malloc_token Ews (tarray tuchar (Zlength (vp_src mode b'))) src;
       data_at Ews (tarray tuchar (Zlength (vp_src mode b'))) (zbytes (vp_src mode b')) src;
       data_at_ Tsh t_fh vz; data_at_ Tsh tin vi; data_at_ Tsh tout vo; TT; has_ext tt).

(* D's pre (mode-independent) and post *)
Definition VP_SD0 (gv: globals) (vz vi vo: val) (wsr ws': wseries) (p: dparams) (base wlim: Z) (src dctx: val)
    : environ -> mpred :=
  PROP (VP_dfacts wsr ws' p base wlim; isptr src; isptr dctx)
  LOCAL (temp _wlim (vl wlim); temp _base (vl base);
         temp _n (vl (Zlength (ws_bytes ws'))); temp _src src; temp _dctx dctx;
         lvar _zfh t_fh vz; lvar _in tin vi; lvar _out tout vo; gvars gv)
  SEP (mem_mgr gv; zstd_globals gv; WG gv; DC gv dctx (set_par dctx_init p);
       data_at Ews t_wseries (wseries_val wsr) (gv _x_valid_params__sr);
       malloc_token Ews (tarray tuchar (Zlength (ws_bytes ws'))) src;
       data_at Ews (tarray tuchar (Zlength (ws_bytes ws'))) (zbytes (ws_bytes ws')) src;
       data_at_ Tsh t_fh vz; data_at_ Tsh tin vi; data_at_ Tsh tout vo; TT; has_ext tt).

Definition VP_SD1 (gv: globals) (vz vi vo: val) (wsr ws': wseries) (src dctx: val) (st: dctx_st)
    : environ -> mpred :=
  PROP ()
  LOCAL (temp _src src; temp _dctx dctx; lvar _zfh t_fh vz; lvar _in tin vi; lvar _out tout vo; gvars gv)
  SEP (mem_mgr gv; zstd_globals gv; WG gv; DC gv dctx st;
       data_at Ews t_wseries (wseries_val wsr) (gv _x_valid_params__sr);
       malloc_token Ews (tarray tuchar (Zlength (ws_bytes ws'))) src;
       data_at Ews (tarray tuchar (Zlength (ws_bytes ws'))) (zbytes (ws_bytes ws')) src;
       data_at_ Tsh t_fh vz; data_at_ Tsh tin vi; data_at_ Tsh tout vo; TT; has_ext tt).

End States.

(* ---------- the context of main's proof: the functions it calls ---------- *)

Definition VP_G0 (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred)
    (WG: globals -> mpred) (WDS: wdict -> reptype t_wstate -> Prop) : funspecs :=
  [(_quickproof_malloc, @malloc_spec' HCS); (_quickproof_free, @free_spec' HCS);
   ZSTD_isError_spec; ZSTD_getErrorCode_spec; ZSTD_decompressDCtx_spec DC DD; ZSTD_createDCtx_spec DC;
   ZSTD_freeDCtx_spec DC; ZSTD_DCtx_setParameter_spec DC; ZSTD_DCtx_setFormat_aspec DC;
   ZSTD_DCtx_setMaxWindowSize_aspec DC; ZSTD_getFrameHeader_advanced_aspec; ZSTD_decompressStream_spec DC DD;
   gp_assert_spec; gp_assume_spec;
   choose_spec; choose_in_spec; exact_copy_spec; within_oneshot_spec; stall_error_spec; w_series_spec WG WDS;
   vp_chunk_spec; vp_windows_within_spec; vp_blocks_within_spec].

Definition VP_Delta (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred)
    (WG: globals -> mpred) (WDS: wdict -> reptype t_wstate -> Prop) : tycontext :=
  func_tycontext f_main Vprog (VP_G0 DC DD WG WDS) nil.

Lemma VP_tyc_g_isSome: forall (V: varspecs) G i, In i (map fst V) ->
  isSome (Maps.PTree.get i (make_tycontext_g V G)).
Proof.
  intros. unfold make_tycontext_g. induction G as [|[j f] G IH]; simpl.
  - induction V as [|[k t] V IHV]; simpl in *; [contradiction|].
    rewrite Maps.PTree.gsspec. destruct (peq i k); simpl; auto.
    apply IHV. destruct H; [congruence|auto].
  - rewrite Maps.PTree.gsspec. destruct (peq i j); simpl; auto.
Qed.
