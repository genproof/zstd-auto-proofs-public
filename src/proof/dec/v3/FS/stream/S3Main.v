(* FS3 streaming: the proof structure of ZSTD_decompressStream, API v3.
   The structure every streaming piece builds on.  v2's StreamMain with the v3 context
   (cst3, SR3, the streaming mode sm_of, the caller's dictionary memory dict_res/set_res in every state).

   The body is cut (StreamMainCode) into the prologue, the loop `while (someMoreWork) switch (streamStage)`
   with its six cases, and the epilogue.  Between the pieces the state is the loop invariant ds_LI:
   the call's arguments (dsa), the context k with an abstract view sv (StreamDefs.c_core), the input
   consumed so far in this call (ipc), the output delivered (opc, the bytes dl), and the model relation
   on the bytes read (ss_in ++ input[ipos, ipc) ++ the hostage byte). *)
Require Export Zstd.proof.dec.v3.FS.stream.S3Specs.
Require Export Zstd.proof.dec.FS.StreamMainCode.
Require Import Zstd.proof.model.ExCall Zstd.proof.model.ExStreamFacts.
Require Zstd.proof.model.ExStream Zstd.proof.model.ExHuf Zstd.proof.model.ExBlock Zstd.proof.model.Exact.
Local Open Scope logic.

Section CM_S3Main_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* the arguments of one call (the WITH of Spec_api6.ZSTD_decompressStream_spec) and the address of the
   local variable op.  a_obf / a_ibf are the buffers' pointers as the caller's structs hold them (NULL for an empty
   buffer, fix F9); a_W is the caller's witnesses with a part of ZSTD_emptyBuffer lent by zstd_globals
   (NullBuf.eb_wit, the witness of the base of an empty buffer passed as NULL) *)
Record dsa := {
  a_W : list ptr_witness; a_gv : globals; a_d : val; a_st : dctx_st; a_outp : val; a_inp : val;
  a_sho : share; a_shi : share; a_shob : share; a_obf : val; a_osz : Z; a_opos : Z; a_oc : list val;
  a_shb : share; a_ibf : val; a_isz : Z; a_ipos : Z; a_ibs : list Z; a_vop : val }.

(* the bases the code computes with (F9: `src = input->src != NULL ? input->src : ZSTD_emptyBuffer`, and dst) *)
Definition a_ob (a: dsa) : val := nbase (a_gv a) (a_obf a).
Definition a_ib (a: dsa) : val := nbase (a_gv a) (a_ibf a).
Arguments a_ob : simpl never.
Arguments a_ib : simpl never.

(* the precondition's facts *)
Definition dsa_ok (a: dsa) : Prop :=
  let st := a_st a in
  buf_ok (a_W a) (a_shob a) (a_osz a) (a_ob a) /\ buf_ok (a_W a) (a_shb a) (a_isz a) (a_ib a) /\
  (dc_stable st = true ->
     match ss_obuf (dc_ss st) with Some (ob', osz') => ob' = a_obf a /\ osz' = a_osz a | None => True end) /\
  writable_share (a_sho a) /\ writable_share (a_shi a) /\ writable_share (a_shob a) /\
  readable_share (a_shb a) /\ stream_dict_ok (a_W a) st /\ ss_err (dc_ss st) = false /\
  0 <= a_opos a <= a_osz a /\ a_osz a <= 2 ^ 63 - 1 /\ Zlength (a_oc a) = a_osz a /\
  0 <= a_ipos a <= a_isz a /\ a_isz a <= 2 ^ 63 - 1 /\ Zlength (a_ibs a) = a_isz a /\ bytes_ok (a_ibs a) /\
  (* API v2 (I2): the stable buffer holds the delivered bytes *)
  (dc_stable st = true -> sublist 0 (a_opos a) (a_oc a) = zbytes (ss_out (dc_ss st))) /\
  (* from buf_ok: an empty output buffer is weakly valid by the witnesses *)
  (a_osz a = 0 -> (pws_pred (a_W a) |-- weak_valid_pointer (a_ob a))) /\
  (dc_stable st = true -> a_opos a = Zlength (ss_out (dc_ss st))) /\
  (* the fields of the context's allocator are pointers or NULL (FSRepC.mgroup) *)
  cmem_ok (dc_mem st).

Lemma dsa_ok_mem (a: dsa) : dsa_ok a -> cmem_ok (dc_mem (a_st a)).
Proof. unfold dsa_ok; tauto. Qed.

(* the bytes read before the call without the hostage byte (API v2: ss_in includes it, ss_ahead counts it);
   within the call the model input is a_sin a ++ input[ipos, ipc) ++ the hostage byte *)
Definition a_sin (a: dsa) : list Z :=
  sublist 0 (Zlength (ss_in (dc_ss (a_st a))) - ss_ahead (dc_ss (a_st a))) (ss_in (dc_ss (a_st a))).

(* the context's allocator within a call: the abstract one with its bound raised for the window limit, as every
   return state has it (Spec_api6.set_ss; ZSTD_decompressStream raises it on entry, FSRep3.c3_raise), with room for
   the stream buffers next to the dictionaries' blocks and the local DDict of that allocator (FSRep3.mem_rel3) *)
Definition mem_call (st: dctx_st) (k: cst3) : Prop :=
  sf_mem (c3_s k) = cm_raise (dc_mem st) (dp_wmax (dc_par st)) /\ mem_room (c3_s k) /\
  local_mem (sf_mem (c3_s k)) (c3_dict k).

(* the abstract facts of the context a call keeps (FSRep3.base_rel3 without the stage of a fresh stream) *)
Definition base_call (st: dctx_st) (k: cst3) : Prop :=
  c3_stable k = dc_stable st /\ c3_par k = dc_par st /\ c3_set k = dc_set st /\
  dict_rel3 st (c3_dict k) /\ set_cur_ok st /\ fp_ok (fs_fParams (c3_fs k)) /\ mem_call st k.

(* the model the call's claims are on (Spec_api6.stream_claims_m with the window limit) *)
Definition a_series (a: dsa) (s: list Z) : list frec * Series.tail :=
  series_frames_m (dmode_w (dmode_of (dc_par (a_st a)))) (fst (st_sel (a_st a))) (snd (st_sel (a_st a)))
    (dp_wmax (dc_par (a_st a))) s.

(* the state within the call: the context k (view sv), input consumed up to ipc, output cells oc' with
   the bytes dl delivered at [opos, opc) *)
Definition call_inv (a: dsa) (k: cst3) (sv: sview) (ipc opc: Z) (oc': list val) (dl: list Z) : Prop :=
  let st := a_st a in
  let ss := dc_ss st in
  let sin := a_sin a ++ sublist (a_ipos a) ipc (a_ibs a) ++ sv_ahead sv in
  let sout := ss_out ss ++ dl in
  a_ipos a <= ipc <= a_isz a /\ a_opos a <= opc <= a_osz a /\
  Zlength oc' = a_osz a /\ sublist 0 (a_opos a) oc' = sublist 0 (a_opos a) (a_oc a) /\
  Zlength dl = opc - a_opos a /\ sublist (a_opos a) opc oc' = zbytes dl /\ bytes_ok dl /\
  base_call st k /\ bytes_ok (a_sin a) /\
  0 <= sf_nfp (c3_s k) <= ZSTD_NO_FORWARD_PROGRESS_MAX /\
  (ipc <> a_ipos a \/ opc <> a_opos a \/
   (sf_nfp (c3_s k) <= ss_stall ss /\ sf_nfp (c3_s k) < ZSTD_NO_FORWARD_PROGRESS_MAX) \/
   sf_stage (c3_s k) = zdss_init \/
   (sf_stage (c3_s k) = zdss_loadHeader /\ exists hb k0, sv_fp sv = FP_hdr hb /\
      get_frame_header_m (dp_fmt (c3_par k) =? 1) hb = FH_more k0)) /\
  (dc_ss st = ss_init -> sf_nfp (c3_s k) = 0) /\
  c_core (dc_stable st) (Some (a_ob a, a_osz a)) sout k sv /\
  sv_dd_ok st k sv /\
  (dc_stable st = true -> sublist 0 opc oc' = zbytes sout) /\
  (sv_ahead sv <> nil -> ipc = a_ipos a) /\
  (a_ipos a = a_isz a -> dc_stable st = false -> Zlength dl + Zlength (sv_pend sv) <= ZSTD_BLOCKSIZE_MAX) /\
  alive_ok st k sv sin sout /\
  (* the header being loaded: its bytes from this call are input[j, ipc); it began before the call only
     if j = ipos *)
  (sf_stage (c3_s k) = zdss_loadHeader -> forall hb, sv_fp sv = FP_hdr hb ->
     exists pre j, a_ipos a <= j <= ipc /\ hb = pre ++ sublist j ipc (a_ibs a) /\ j = a_ipos a) /\
  (* R4: the hostage byte held at the call's start stays in sv_ahead for the whole loop *)
  a_sin a ++ sv_ahead sv = ss_in ss /\
  (* R4: stable mode, the recorded output buffer is the caller's (zdss_init sets it, else SR + precondition) *)
  (dc_stable st = true -> sf_stage (c3_s k) <> zdss_init ->
     sf_expOut (c3_s k) = (a_obf a, (vlong (a_osz a), vlong (a_opos a)))) /\
  (* R4 (T): a frame completed in this call with output pending: its last unit was read in this call *)
  (sf_stage (c3_s k) = zdss_flush -> fp_complete (sv_fp sv) = true -> sv_pend sv <> nil ->
     sf_hostage (c3_s k) = Vint (Int.repr 0) -> a_ipos a < ipc).

(* what the call starts from (SR, or a fresh stream): the content claim on the bytes read and delivered *)
Definition start_ok (a: dsa) : Prop :=
  content_ok (sm_of (a_st a)) (ss_in (dc_ss (a_st a))) (ss_out (dc_ss (a_st a))) /\
  (ss_ahead (dc_ss (a_st a)) = 0 \/ ss_ahead (dc_ss (a_st a)) = 1) /\
  ss_ahead (dc_ss (a_st a)) <= Zlength (ss_in (dc_ss (a_st a))) /\
  0 <= ss_stall (dc_ss (a_st a)).

(* the bytes read before the call and the whole rest of the caller's input (an error return keeps in.pos) *)
Definition a_all (a: dsa) : list Z :=
  ss_in (dc_ss (a_st a)) ++ sublist (a_ipos a + ss_ahead (dc_ss (a_st a))) (a_isz a) (a_ibs a).

(* why an error r returned with the positions unchanged is allowed (stream_claims' error clause): memory,
   every series extending a_all fails the streaming model, or the stable buffer is too small *)
Definition err_why (a: dsa) (r: Z) : Prop :=
  dec_err r /\
  (r = 2 ^ 64 - ZSTD_error_memory_allocation \/
   (forall s, bytes_ok s -> is_prefix (a_all a) s -> snd (a_series a s) <> TEnd) \/
   (dc_stable (a_st a) = true /\
    forall s, bytes_ok s -> is_prefix (a_all a) s -> snd (a_series a s) = TEnd ->
      a_osz a < Zlength (flat_map fr_content (fst (a_series a s))))).



Section Main.
Variable DENT : dent_pred.
Variable TABS : tabs_pred.
Variable BR : blrel.

(* the loop's witnesses: someMoreWork, the context and its view, input/output positions, cells, bytes *)
Record lw := { w_smw : Z; w_k : cst3; w_sv : sview; w_ipc : Z; w_opc : Z; w_oc : list val; w_dl : list Z }.

(* while the loop goes on, a stream at zdss_init / zdss_loadHeader has delivered nothing in this call and
   holds no hostage byte *)
Definition loop_extra (w: lw) : Prop :=
  w_smw w = 1 -> sf_stage (c3_s (w_k w)) <= zdss_loadHeader -> w_dl w = nil /\ sv_ahead (w_sv w) = nil.

(* R4: the stage setter (the epilogue's "can't release the hostage" path sets zdss_read again) *)
Definition sf_set_stage (s: sfields) (st: Z) : sfields :=
  {| sf_stage := st; sf_inBuff := sf_inBuff s; sf_inSize := sf_inSize s; sf_inPos := sf_inPos s;
     sf_outBuff := sf_outBuff s; sf_outSize := sf_outSize s; sf_outStart := sf_outStart s;
     sf_outEnd := sf_outEnd s; sf_lhSize := sf_lhSize s; sf_hostage := sf_hostage s; sf_nfp := sf_nfp s;
     sf_expOut := sf_expOut s; sf_hbuf := sf_hbuf s; sf_over := sf_over s; sf_ring := sf_ring s; sf_mem := sf_mem s; sf_held := sf_held s |}.

(* R4: what the epilogue needs when the loop stops (someMoreWork = 0) *)
Definition exit_ok (a: dsa) (w: lw) : Prop :=
  let k := w_k w in let s := c3_s k in let sv := w_sv w in
  w_smw w = 0 ->
  (* X1 *) sf_stage s <> zdss_loadHeader /\
  (* X2 *) ((sf_stage s = zdss_read \/ sf_stage s = zdss_load) -> w_ipc w = a_isz a) /\
           (sf_stage s = zdss_flush -> w_opc w = a_osz a /\ sv_pend sv <> nil) /\
  (* X3 *) (w_ipc w = a_ipos a -> w_opc w = a_opos a ->
              sf_nfp s <= ss_stall (dc_ss (a_st a)) /\ sf_nfp s < ZSTD_NO_FORWARD_PROGRESS_MAX) /\
  (* X4 *) (sf_stage s = zdss_init ->
     fs_expected (c3_fs k) = vlong 0 /\
     (exists o, sf_outStart s = vlong o /\ sf_outEnd s = vlong o /\ 0 <= o <= Int64.max_unsigned) /\
     ((sf_hostage s = Vint (Int.repr 0) /\ sv_ahead sv = nil /\
       (fp_complete (sv_fp sv) = true \/ (sv_fp sv = FP_none /\ a_ipos a < w_ipc w))) \/
      (sf_hostage s = Vint (Int.repr 1) /\ Zlength (sv_ahead sv) = 1 /\
       c_core (dc_stable (a_st a)) (Some (a_ob a, a_osz a)) (ss_out (dc_ss (a_st a)) ++ w_dl w)
         (c3_with_s k (sf_set_stage s zdss_read)) sv /\
       (* the read-stage state keeps the frame's DDict facts *)
       sv_dd_ok (a_st a) (c3_with_s k (sf_set_stage s zdss_read)) sv /\
       (dead (sm_of (a_st a)) (a_sin a ++ sublist (a_ipos a) (w_ipc w) (a_ibs a) ++ sv_ahead sv) \/
        hist_ok (dc_stable (a_st a)) (c3_with_s k (sf_set_stage s zdss_read)) sv)))).

(* R5: zdss_init with someMoreWork = 1 only at the call's start (a frame's end stops the loop) *)
Definition entry_ok (a: dsa) (w: lw) : Prop :=
  w_smw w = 1 -> sf_stage (c3_s (w_k w)) = zdss_init -> w_ipc w = a_ipos a.

(* buffered mode: the output cells after the position reached are still the caller's (the flush writes exactly
   the bytes it delivers, the single-pass shortcut exactly the frame's content; everything else decodes into the
   context's own buffer); Spec_api6.stream_untouched *)
Definition untouched_ok (a: dsa) (w: lw) : Prop :=
  dc_stable (a_st a) = false -> sublist (w_opc w) (a_osz a) (w_oc w) = sublist (w_opc w) (a_osz a) (a_oc a).

Definition ds_LI_P (a: dsa) (w: lw) : list Prop :=
  [call_inv a (w_k w) (w_sv w) (w_ipc w) (w_opc w) (w_oc w) (w_dl w); w_smw w = 0 \/ w_smw w = 1;
   loop_extra w; exit_ok a w; entry_ok a w; untouched_ok a w].

Definition ds_LI_L (a: dsa) (w: lw) : list localdef :=
  [lvar _op (tptr tschar) (a_vop a); gvars (a_gv a); temp _zds (a_d a); temp _output (a_outp a);
   temp _input (a_inp a); temp _src (a_ib a); temp _istart (offset_val (a_ipos a) (a_ib a));
   temp _iend (offset_val (a_isz a) (a_ib a)); temp _ip (offset_val (w_ipc w) (a_ib a));
   temp _dst (a_ob a); temp _ostart (offset_val (a_opos a) (a_ob a));
   temp _oend (offset_val (a_osz a) (a_ob a)); temp _someMoreWork (Vint (Int.repr (w_smw w)))].

Definition ds_LI_S (a: dsa) (w: lw) : list mpred :=
  [data_at Tsh (tptr tschar) (offset_val (w_opc w) (a_ob a)) (a_vop a); pws_pred (a_W a); mem_mgr (a_gv a);
   zstd_globals (a_gv a); ctx_rep3 DENT TABS (a_gv a) (a_d a) (w_k w);
   dict_res (DD3x DENT) (a_gv a) Ews (dc_dict (a_st a)); set_res (DD3x DENT) (a_gv a) Ews (dc_set (a_st a)) (dc_dict (a_st a));
   data_at (a_sho a) t_outBuffer (a_obf a, (vlong (a_osz a), vlong (a_opos a))) (a_outp a);
   data_at (a_shi a) t_inBuffer (a_ibf a, (vlong (a_isz a), vlong (a_ipos a))) (a_inp a);
   data_at (a_shob a) (tarray tuchar (a_osz a)) (w_oc w) (a_ob a);
   data_at (a_shb a) (tarray tuchar (a_isz a)) (zbytes (a_ibs a)) (a_ib a)].

(* the loop invariant: at the loop head, someMoreWork = w_smw *)
Definition ds_LI (a: dsa) : environ -> mpred :=
  EX w: lw, PROPx (ds_LI_P a w) (LOCALx (ds_LI_L a w) (SEPx (ds_LI_S a w))).

Definition ds_inv (a: dsa) : environ -> mpred :=
  EX w: lw, PROPx (ds_LI_P a w) (LOCALx (ds_LI_L a w) (SEPx (ds_LI_S a w))).

(* the function's postcondition (Spec_api6.ZSTD_decompressStream_spec without stream_exact, the context without the
   exact relation: S3Defs.SR3r) for the arguments a: the relational pieces' *)
Definition ds_post (a: dsa) : environ -> mpred :=
  (EX r: Z, EX opos': Z, EX ipos': Z, EX oc': list val, EX st': dctx_st,
   PROP (0 <= r <= Int64.max_unsigned;
         stream_post (a_st a) st' r (a_obf a) (a_osz a) (a_opos a) opos' (a_oc a) oc' (a_ibs a) (a_isz a)
           (a_ipos a) ipos';
         stream_progress (a_st a) st' r (a_osz a) (a_opos a) opos' (a_isz a) (a_ipos a) ipos' (a_ibs a);
         stream_untouched (a_st a) r (a_osz a) opos' (a_oc a) oc')
   RETURN (Vlong (Int64.repr r))
   SEP (pws_pred (a_W a); mem_mgr (a_gv a); zstd_globals (a_gv a);
        (DC3x DENT TABS SR3r BR (a_gv a) (a_d a) st' && valid_pointer (a_d a));
        dict_res (DD3x DENT) (a_gv a) Ews (dc_dict (a_st a));
        set_res (DD3x DENT) (a_gv a) Ews (dc_set (a_st a)) (dc_dict (a_st a));
        data_at (a_sho a) t_outBuffer (a_obf a, (Vlong (Int64.repr (a_osz a)), Vlong (Int64.repr opos'))) (a_outp a);
        data_at (a_shi a) t_inBuffer (a_ibf a, (Vlong (Int64.repr (a_isz a)), Vlong (Int64.repr ipos'))) (a_inp a);
        data_at (a_shob a) (tarray tuchar (a_osz a)) oc' (a_ob a);
        data_at (a_shb a) (tarray tuchar (a_isz a)) (zbytes (a_ibs a)) (a_ib a)))%assert.

(* the function body's ret_assert *)
Definition ds_R (a: dsa) : ret_assert :=
  frame_ret_assert (function_body_ret_assert tulong (ds_post a)) (stackframe_of f_ZSTD_decompressStream).

Definition ds_Delta : tycontext := func_tycontext f_ZSTD_decompressStream Vprog (stream_G3 DENT TABS BR) nil.

End Main.

(* the switch's cases from case k on (fall-through) *)
Definition ds_tail (k: Z) : labeled_statements :=
  match k with
  | 0 => ds_switch_ls
  | 1 => LScons (Some 1) ds_case_loadHeader (LScons (Some 2) ds_case_read (LScons (Some 3) ds_case_load
           (LScons (Some 4) ds_case_flush (LScons None ds_case_default LSnil))))
  | 2 => LScons (Some 2) ds_case_read (LScons (Some 3) ds_case_load
           (LScons (Some 4) ds_case_flush (LScons None ds_case_default LSnil)))
  | 3 => LScons (Some 3) ds_case_load (LScons (Some 4) ds_case_flush (LScons None ds_case_default LSnil))
  | _ => LScons (Some 4) ds_case_flush (LScons None ds_case_default LSnil)
  end.

Lemma ds_select : forall k, 0 <= k <= 4 ->
  select_switch (Int.unsigned (Int.repr k)) ds_switch_ls = ds_tail k.
Proof.
intros k Hk.
assert (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4) as Hc by lia.
destruct Hc as [->|[->|[->|[->| ->]]]]; reflexivity.
Qed.

(* ---------- the pieces of the proof (proved in their own files) ---------- *)

(* a case of the switch, from its label to the end (fall-through included): from the loop invariant
   with someMoreWork = 1 and streamStage = k, to the loop invariant (break) or the function's
   postcondition (return) *)
Definition seg_case (k: Z) : Prop :=
  forall (Espec: OracleKind) DENT TABS BR (a: dsa) (w: lw) (R: ret_assert),
    DENT_OK DENT -> TABS_OK TABS -> dsa_ok a ->
    call_inv a (w_k w) (w_sv w) (w_ipc w) (w_opc w) (w_oc w) (w_dl w) -> w_smw w = 1 -> loop_extra w ->
    sf_stage (c3_s (w_k w)) = k ->
    RA_normal R = ds_inv DENT TABS a -> RA_return R = RA_return (ds_R DENT TABS BR a) -> start_ok a ->
    entry_ok a w -> untouched_ok a w ->
    semax (ds_Delta DENT TABS BR) (PROPx [] (LOCALx (ds_LI_L a w) (SEPx (ds_LI_S DENT TABS a w))))
      (seq_of_labeled_statement (ds_tail k)) (switch_ret_assert R).

(* the epilogue: from the loop invariant with someMoreWork = 0 to the function's postcondition *)
Definition seg_epilogue : Prop :=
  forall (Espec: OracleKind) DENT TABS BR (a: dsa) (w: lw),
    DENT_OK DENT -> TABS_OK TABS -> dsa_ok a ->
    call_inv a (w_k w) (w_sv w) (w_ipc w) (w_opc w) (w_oc w) (w_dl w) -> w_smw w = 0 -> start_ok a ->
    exit_ok a w -> untouched_ok a w ->
    semax (ds_Delta DENT TABS BR) (PROPx [] (LOCALx (ds_LI_L a w) (SEPx (ds_LI_S DENT TABS a w))))
      ds_epilogue (ds_R DENT TABS BR a).

(* the prologue: from the function's precondition to the loop invariant with someMoreWork = 1 *)
Definition seg_prologue : Prop :=
  forall (Espec: OracleKind) DENT TABS BR (a: dsa) (REST: statement),
    DENT_OK DENT -> TABS_OK TABS -> dsa_ok a ->
    (forall w, call_inv a (w_k w) (w_sv w) (w_ipc w) (w_opc w) (w_oc w) (w_dl w) -> w_smw w = 1 ->
       loop_extra w -> start_ok a -> exit_ok a w -> entry_ok a w -> untouched_ok a w ->
       semax (ds_Delta DENT TABS BR) (PROPx [] (LOCALx (ds_LI_L a w) (SEPx (ds_LI_S DENT TABS a w))))
         REST (ds_R DENT TABS BR a)) ->
    semax (ds_Delta DENT TABS BR)
      (PROP ()
       LOCAL (lvar _op (tptr tschar) (a_vop a); gvars (a_gv a); temp _zds (a_d a);
              temp _output (a_outp a); temp _input (a_inp a))
       SEP (data_at_ Tsh (tptr tschar) (a_vop a); pws_pred (a_W a); mem_mgr (a_gv a); zstd_globals (a_gv a);
            DC3x DENT TABS SR3 BR (a_gv a) (a_d a) (a_st a);
            dict_res (DD3x DENT) (a_gv a) Ews (dc_dict (a_st a));
            set_res (DD3x DENT) (a_gv a) Ews (dc_set (a_st a)) (dc_dict (a_st a));
            data_at (a_sho a) t_outBuffer (a_obf a, (Vlong (Int64.repr (a_osz a)), Vlong (Int64.repr (a_opos a)))) (a_outp a);
            data_at (a_shi a) t_inBuffer (a_ibf a, (Vlong (Int64.repr (a_isz a)), Vlong (Int64.repr (a_ipos a)))) (a_inp a);
            data_at (a_shob a) (tarray tuchar (a_osz a)) (a_oc a) (a_ob a);
            data_at (a_shb a) (tarray tuchar (a_isz a)) (zbytes (a_ibs a)) (a_ib a)))
      (ds_prologue REST) (ds_R DENT TABS BR a).

End CM_S3Main_1.


(* ---------- the exact claim (Spec_api6.stream_exact) ---------- *)

Section CM_S3Main_x.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.

(* the call as the model sees it: the bytes it may read and the output room *)
Definition a_xin (a: dsa) : list Z := sublist (a_ipos a) (a_isz a) (a_ibs a).
Definition a_xroom (a: dsa) : Z := a_osz a - a_opos a.

(* the model's loop (ExStream.z_loop at model/Exact.v's instance) *)
Definition z_loop_x (f: nat) (inp: list Z) (room: Z) (z: zstate_x) (ip: Z) (dl: list Z) : ExStream.lstep XS :=
  ExStream.z_loop XS (ExBlock.xst_begin ExHuf.xhuf) Exact.xblock xframe1 f inp room z ip dl.

(* the outcome of the call's whole loop, from the state z0 of the calls before it *)
Definition a_loop (a: dsa) (z0: zstate_x) : ExStream.lstep XS := z_loop_x (zfuel (a_xin a)) (a_xin a) (a_xroom a) z0 0 nil.

(* the loop invariant's exact conjunct: from the configuration of a new context, the calls before this one lead the
   model to z0 (with the exact relation at the call's start), and the loop state w is the model's loop state zi at
   ip = ipc - ipos with the bytes dl written: while the loop goes on, the model's loop from there (with fuel f above
   the potential) ends as the call's whole loop; once it stops, that is the call's loop outcome.  At the loop's first
   iteration only zrel holds (in zdss_init zstd rewrites the fields zrel_end pins); after an iteration zrel_end. *)
Definition ex_call (a: dsa) (w: lw) : Prop :=
  fresh_cfg (a_st a) ->
  exists (z0 zi: zstate_x) (f: nat),
    zs_run_x (ss_calls (dc_ss (a_st a))) = Some z0 /\ zinv_x z0 /\ zinv_x zi /\
    (w_smw w = 1 ->
       zpot XS (a_xin a) zi (w_ipc w - a_ipos a) < Z.of_nat f /\
       z_loop_x f (a_xin a) (a_xroom a) zi (w_ipc w - a_ipos a) (w_dl w) = a_loop a z0 /\
       ((w_ipc w = a_ipos a /\ w_dl w = nil /\ zi = z0 /\
         zrel zi (sf_strip (c3_s (w_k w))) (c3_fs (w_k w)) (c3_tabs (w_k w))) \/
        zrel_end zi (sf_strip (c3_s (w_k w))) (c3_fs (w_k w)) (c3_tabs (w_k w)))) /\
    (w_smw w = 0 ->
       a_loop a z0 = ExStream.LStop XS zi (w_ipc w - a_ipos a) (w_dl w) /\
       zrel_end zi (sf_strip (c3_s (w_k w))) (c3_fs (w_k w)) (c3_tabs (w_k w))).

(* an error return: the model fails on this call too, or the error is a memory allocation *)
Definition ex_err (a: dsa) (r: Z) : Prop :=
  fresh_cfg (a_st a) -> r = err_code ZSTD_error_memory_allocation \/
  Exact.zs_call (ss_calls (dc_ss (a_st a))) (a_xin a, a_xroom a) = None.

Section MainX.
Variable DENT : dent_pred.
Variable TABS : tabs_pred.
Variable BR : blrel.

Definition ds_LI_Px (a: dsa) (w: lw) : list Prop :=
  [call_inv a (w_k w) (w_sv w) (w_ipc w) (w_opc w) (w_oc w) (w_dl w); w_smw w = 0 \/ w_smw w = 1;
   loop_extra w; exit_ok a w; entry_ok a w; untouched_ok a w; ex_call a w].

(* the loop invariant with the exact conjunct *)
Definition ds_inv_x (a: dsa) : environ -> mpred :=
  EX w: lw, PROPx (ds_LI_Px a w) (LOCALx (ds_LI_L a w) (SEPx (ds_LI_S DENT TABS a w))).

(* the function's postcondition: Spec_api6.ZSTD_decompressStream_spec for the arguments a *)
Definition ds_post_x (a: dsa) : environ -> mpred :=
  (EX r: Z, EX opos': Z, EX ipos': Z, EX oc': list val, EX st': dctx_st,
   PROP (0 <= r <= Int64.max_unsigned;
         stream_post (a_st a) st' r (a_obf a) (a_osz a) (a_opos a) opos' (a_oc a) oc' (a_ibs a) (a_isz a)
           (a_ipos a) ipos';
         stream_progress (a_st a) st' r (a_osz a) (a_opos a) opos' (a_isz a) (a_ipos a) ipos' (a_ibs a);
         stream_untouched (a_st a) r (a_osz a) opos' (a_oc a) oc';
         stream_exact (a_st a) st' r (a_osz a) (a_opos a) opos' oc' (a_ibs a) (a_isz a) (a_ipos a) ipos')
   RETURN (Vlong (Int64.repr r))
   SEP (pws_pred (a_W a); mem_mgr (a_gv a); zstd_globals (a_gv a);
        (DC3x DENT TABS SR3 BR (a_gv a) (a_d a) st' && valid_pointer (a_d a));
        dict_res (DD3x DENT) (a_gv a) Ews (dc_dict (a_st a));
        set_res (DD3x DENT) (a_gv a) Ews (dc_set (a_st a)) (dc_dict (a_st a));
        data_at (a_sho a) t_outBuffer (a_obf a, (Vlong (Int64.repr (a_osz a)), Vlong (Int64.repr opos'))) (a_outp a);
        data_at (a_shi a) t_inBuffer (a_ibf a, (Vlong (Int64.repr (a_isz a)), Vlong (Int64.repr ipos'))) (a_inp a);
        data_at (a_shob a) (tarray tuchar (a_osz a)) oc' (a_ob a);
        data_at (a_shb a) (tarray tuchar (a_isz a)) (zbytes (a_ibs a)) (a_ib a)))%assert.

Definition ds_R_x (a: dsa) : ret_assert :=
  frame_ret_assert (function_body_ret_assert tulong (ds_post_x a)) (stackframe_of f_ZSTD_decompressStream).

End MainX.

(* the pieces with the exact claim: as seg_case, seg_epilogue and seg_prologue, with ex_call in the loop invariant
   and the full specification's postcondition *)
Definition seg_case_x (k: Z) : Prop :=
  forall (Espec: OracleKind) DENT TABS BR (a: dsa) (w: lw) (R: ret_assert),
    DENT_OK DENT -> TABS_OK TABS -> dsa_ok a ->
    call_inv a (w_k w) (w_sv w) (w_ipc w) (w_opc w) (w_oc w) (w_dl w) -> w_smw w = 1 -> loop_extra w ->
    sf_stage (c3_s (w_k w)) = k ->
    RA_normal R = ds_inv_x DENT TABS a -> RA_return R = RA_return (ds_R_x DENT TABS BR a) -> start_ok a ->
    entry_ok a w -> untouched_ok a w -> ex_call a w ->
    semax (ds_Delta DENT TABS BR) (PROPx [] (LOCALx (ds_LI_L a w) (SEPx (ds_LI_S DENT TABS a w))))
      (seq_of_labeled_statement (ds_tail k)) (switch_ret_assert R).

Definition seg_epilogue_x : Prop :=
  forall (Espec: OracleKind) DENT TABS BR (a: dsa) (w: lw),
    DENT_OK DENT -> TABS_OK TABS -> dsa_ok a ->
    call_inv a (w_k w) (w_sv w) (w_ipc w) (w_opc w) (w_oc w) (w_dl w) -> w_smw w = 0 -> start_ok a ->
    exit_ok a w -> untouched_ok a w -> ex_call a w ->
    semax (ds_Delta DENT TABS BR) (PROPx [] (LOCALx (ds_LI_L a w) (SEPx (ds_LI_S DENT TABS a w))))
      ds_epilogue (ds_R_x DENT TABS BR a).

Definition seg_prologue_x : Prop :=
  forall (Espec: OracleKind) DENT TABS BR (a: dsa) (REST: statement),
    DENT_OK DENT -> TABS_OK TABS -> dsa_ok a ->
    (forall w, call_inv a (w_k w) (w_sv w) (w_ipc w) (w_opc w) (w_oc w) (w_dl w) -> w_smw w = 1 ->
       loop_extra w -> start_ok a -> exit_ok a w -> entry_ok a w -> untouched_ok a w -> ex_call a w ->
       semax (ds_Delta DENT TABS BR) (PROPx [] (LOCALx (ds_LI_L a w) (SEPx (ds_LI_S DENT TABS a w))))
         REST (ds_R_x DENT TABS BR a)) ->
    semax (ds_Delta DENT TABS BR)
      (PROP ()
       LOCAL (lvar _op (tptr tschar) (a_vop a); gvars (a_gv a); temp _zds (a_d a);
              temp _output (a_outp a); temp _input (a_inp a))
       SEP (data_at_ Tsh (tptr tschar) (a_vop a); pws_pred (a_W a); mem_mgr (a_gv a); zstd_globals (a_gv a);
            DC3x DENT TABS SR3 BR (a_gv a) (a_d a) (a_st a);
            dict_res (DD3x DENT) (a_gv a) Ews (dc_dict (a_st a));
            set_res (DD3x DENT) (a_gv a) Ews (dc_set (a_st a)) (dc_dict (a_st a));
            data_at (a_sho a) t_outBuffer (a_obf a, (Vlong (Int64.repr (a_osz a)), Vlong (Int64.repr (a_opos a)))) (a_outp a);
            data_at (a_shi a) t_inBuffer (a_ibf a, (Vlong (Int64.repr (a_isz a)), Vlong (Int64.repr (a_ipos a)))) (a_inp a);
            data_at (a_shob a) (tarray tuchar (a_osz a)) (a_oc a) (a_ob a);
            data_at (a_shb a) (tarray tuchar (a_isz a)) (zbytes (a_ibs a)) (a_ib a)))
      (ds_prologue REST) (ds_R_x DENT TABS BR a).

End CM_S3Main_x.
