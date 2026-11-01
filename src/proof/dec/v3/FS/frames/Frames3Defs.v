(* FS3 one-shot frames: ZSTD_decompressFrame's body in segments (port of v2 body_frame.v): the statements of the body,
   the states between the
   segments and the segment obligations.  Fixed for the FRAMES3 part; the segment proofs are in
   Frame3_*.v.

   v3 changes against v2: the context is FR3_G; the frame group is fcore3 (format dp_fmt pr, forceIgnoreChecksum,
   maxBlockSizeParam, refMultipleDDicts, the set pointer dsp: listed field by field in fr_SEP); the selection's
   resources sel_res (fr_selR: with `lent`, the local DDict's entropy is outside, in dent_of); the header h of the
   loop is the parsed one with Block_Maximum_Size capped (fh_cap, Frames3Pure.fr_hdr3); validateChecksum is
   vck (flag && !forceIgnoreChecksum); the context's dictID after the header is fdid; the dictionary fields after
   the header are d1; the postcondition fr_R is ZSTD_decompressFrame_spec3's (frame_res3 when the selection is
   off; dict_after). *)
Require Export Zstd.proof.dec.v3.FS.frames.Frames3Pure.
Require Export Zstd.proof.dec.v3.FS.frames.Frames3ModelF.
Require Import Zstd.proof.model.ExHuf Zstd.proof.model.ExBlock Zstd.proof.model.ExFrame Zstd.proof.model.ExFrameFacts.
Require Import Zstd.proof.model.ExBlockBytes.
Local Open Scope logic.

Section CM_Frames3Defs_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.

(* ---------- the selection's resources with the local DDict's entropy taken out (`lent`) ---------- *)

(* sel_any lent with its pieces: whole sel_res, the entropy elsewhere (dent_of None), the extDict unless it is the
   copied local DDict's bytes (lent_rest) *)
Definition lent_rest (lent: bool) (d: dfields) (e: ext_seg) : mpred :=
  if lent then match df_lx d with Some (x, _) => if ddx_copied x then emp else ext_res e | None => ext_res e end
  else ext_res e.

Lemma lent_conv: forall DENT gv p pr sp d l tbl xq ox s e (lent: bool) am hb,
  (lent = true -> lent_ok pr sp d l tbl ox s /\ lent_ext d e) ->
  sel_any DENT gv p pr sp d l tbl xq lent am hb * dent_of DENT gv ox * ext_res e =
  sel_res DENT gv p pr sp d l tbl xq am hb * dent_of DENT gv (if lent then None else ox) * lent_rest lent d e.
Proof.
  intros DENT gv p pr sp d l tbl xq ox s e lent am hb H. unfold sel_any, lent_rest. destruct lent; [|reflexivity].
  destruct (H eq_refl) as [(Hon & (x & buf & -> & Hlx & Hloc) & _) He]. unfold lent_ext in He. rewrite Hlx in He.
  unfold sel_res, sel_hole. rewrite Hon. unfold dgroup, dgroup_hole, local_rep. rewrite Hlx.
  destruct (eq_dec (df_local d) nullval) as [E|E]; [contradiction|].
  unfold ddict_rep_at, ddict_mem, dent_of. destruct (ddx_copied x) eqn:Ec.
  - destruct (He eq_refl) as (e1 & elen & ->). unfold ext_res. apply pred_ext; Intros; entailer!.
  - apply pred_ext; Intros; entailer!.
Qed.

Lemma lent_to: forall DENT gv p pr sp d l tbl xq ox s e (lent: bool) am hb,
  (lent = true -> lent_ok pr sp d l tbl ox s /\ lent_ext d e) ->
  sel_any DENT gv p pr sp d l tbl xq lent am hb * dent_of DENT gv ox * ext_res e |--
  sel_res DENT gv p pr sp d l tbl xq am hb * dent_of DENT gv (if lent then None else ox) * lent_rest lent d e.
Proof. intros. erewrite lent_conv by eassumption. apply derives_refl. Qed.

Lemma lent_from: forall DENT gv p pr sp d l tbl xq ox s e (lent: bool) am hb,
  (lent = true -> lent_ok pr sp d l tbl ox s /\ lent_ext d e) ->
  sel_res DENT gv p pr sp d l tbl xq am hb * dent_of DENT gv (if lent then None else ox) * lent_rest lent d e |--
  sel_any DENT gv p pr sp d l tbl xq lent am hb * dent_of DENT gv ox * ext_res e.
Proof. intros. erewrite lent_conv by eassumption. apply derives_refl. Qed.

(* ======================================================================================
   The statements of the body (as v2): 18 top-level statements, 10 the block loop (17 statements).
   ====================================================================================== *)

(* the first k statements of a right-nested sequence s, followed by c *)
Fixpoint seq_cut (k: nat) (s c: statement) : statement :=
  match k, s with
  | O, _ => c
  | S k', Ssequence a b => Ssequence a (seq_cut k' b c)
  | S _, _ => Ssequence s c
  end.

(* s without its first k statements *)
Fixpoint seq_drop (k: nat) (s: statement) : statement :=
  match k, s with
  | O, _ => s
  | S k', Ssequence a b => seq_drop k' b
  | S _, _ => Sskip
  end.

(* the k-th statement *)
Fixpoint seq_nth (k: nat) (s: statement) : statement :=
  match k, s with
  | O, Ssequence a _ => a
  | S k', Ssequence _ b => seq_nth k' b
  | _, _ => s
  end.

Definition fr_body : statement := fn_body f_ZSTD_decompressFrame.
Definition fr_loop : statement := seq_nth 10 fr_body.
Definition fr_lb : statement := match fr_loop with Sloop b _ => b | _ => Sskip end.
Definition fr_sw : statement := seq_nth 8 fr_lb.

(* the call (and the assignment of decodedSize) of the case `lbl` of the switch *)
Fixpoint ls_find (lbl: Z) (ls: labeled_statements) : statement :=
  match ls with
  | LScons (Some l) b rest => if Z.eq_dec l lbl then b else ls_find lbl rest
  | LScons None _ rest => ls_find lbl rest
  | LSnil => Sskip
  end.
Definition fr_case (lbl: Z) : statement :=
  match seq_nth 1 fr_sw with
  | Sswitch _ ls => match ls_find lbl ls with Ssequence cs _ => cs | _ => Sskip end
  | _ => Sskip
  end.

Lemma fr_loop_shape: fr_loop = Sloop fr_lb Sskip.
Proof. reflexivity. Qed.

Lemma fr_lb_split: forall k,
  seq_cut 8 fr_lb k = seq_cut 8 fr_lb k /\
  fr_lb = seq_cut 8 fr_lb (Ssequence fr_sw (seq_drop 9 fr_lb)).
Proof. split; reflexivity. Qed.

Section FR.
Context (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR: blrel)
  (W: list ptr_witness) (gv: globals) (p: val) (fs: fstate) (ox: option ddx) (dm: dict_model) (e: ext_seg)
  (osh: share) (obase: val) (oN: Z) (oc: list val) (od ocap: Z)
  (ish: share) (ibase: val) (iN: Z) (ic: list val) (ioff: Z) (s: list Z) (sp ssp: val) (v_bp: val)
  (pr: dparams) (dsp: val) (d: dfields) (l: list (val * ddict_st)) (tbl: list val) (xq: option (val * val)) (lent: bool)
  (am: option cmem) (hb: Z) (h: frame_header) (hs: Z) (fdid: Z) (d1: dfields) (ts0: tstate).

Definition fr_Delta : tycontext := func_tycontext f_ZSTD_decompressFrame Vprog (FR3_G DENT TABS SR BR) nil.

(* the postcondition of the function (ZSTD_decompressFrame_spec3, o and i destructed) *)
Definition fr_R : ret_assert :=
  frame_ret_assert
    (function_body_ret_assert tulong
       (EX r: Z, EX oc': list val, EX fs': fstate, EX k: Z, EX d': dfields, EX lxb': list Z,
        PROP (0 <= r <= Int64.max_unsigned; Zlength oc' = oN;
              unchanged_outside oc oc' od (od + ocap);
              is_error_code r = false -> r <= ocap /\ 0 <= k <= Zlength s;
              is_error_code r = false ->
                exists c, bytes_ok c /\ Zlength c = r /\ sublist od (od + r) oc' = zbytes c;
              is_error_code r = true -> k = 0 /\ dec_err r;
              frame_res3 (dmode_of pr) dm s ocap r oc' od k;
              fs_dictEnd fs' = fs_dictEnd fs;
              fs_ddictIsCold fs' = Vint (Int.repr 0) \/ fs_ddictIsCold fs' = Vint (Int.repr 1);
              dict_after pr dsp l d d'; lent = true -> d' = d;
              is_error_code r = false -> sel_on pr dsp = true -> df_ddict d <> nullval ->
                exists id, fp_dictID (fs_fParams fs') = Vint (Int.repr id) /\ 0 <= id <= Int.max_unsigned /\
                  (hs_probe l tbl id = nullval \/ hs_probe l tbl id = df_ddict d');
              fp_ok (fs_fParams fs) -> fp_ok (fs_fParams fs');
              dict_sel pr dsp l tbl (sublist 0 (header_size_m (dp_fmt pr =? 1) s) s) d d';
              is_error_code r = false -> (dp_fmt pr = 1 \/ is_skippable_magic (le_field s 0 4) = false) ->
                frame_compressed_size_m (dp_fmt pr =? 1) s = Some k;
              frame_codes3 (dmode_of pr) dm s ocap r;
              is_error_code r = false -> forall h, get_frame_header_m (dp_fmt pr =? 1) s = FH_ok h ->
                fh_frameType h = 0 -> fh_contentSize h <> ZSTD_CONTENTSIZE_UNKNOWN -> r = fh_contentSize h;
              ox = None -> dm = no_dict -> pr = dparams_dflt -> e = ExtNone -> frame_exact ts0 s ocap r oc' od k lxb')
        RETURN (Vlong (Int64.repr r))
        SEP (zstd_globals gv; pws_pred W; fcore3 p fs' pr dsp; sel_any DENT gv p pr dsp d' l tbl xq lent am hb;
             tables_uninit p lxb'; dent_of DENT gv ox;
             data_at osh (tarray tuchar oN) oc' obase;
             data_at ish (tarray tuchar iN) ic ibase; ext_res e;
             data_at Tsh (tptr tvoid) (offset_val (ioff + k) ibase) sp;
             data_at Tsh tulong (Vlong (Int64.repr (Zlength s - k))) ssp)))
    (stackframe_of f_ZSTD_decompressFrame).

(* the facts of the whole body: the precondition's, the header's *)
Record fr_ctx : Prop := {
  fc_osh: writable_share osh; fc_oN: Zlength oc = oN; fc_oN32: oN <= 2 ^ 63 - 1;
  fc_od: 0 <= od; fc_ocap: 0 <= ocap; fc_odcap: od + ocap <= oN;
  fc_win: win_ok ish iN ic ioff (Zlength s) s;
  fc_ext: match e with ExtIn _ _ => False | _ => True end;
  fc_ifd: fs_isFrameDecompression fs = Vint (Int.repr 1);
  fc_cold: fs_ddictIsCold fs = Vint (Int.repr 0) \/ fs_ddictIsCold fs = Vint (Int.repr 1);
  fc_W: ocap = 0 -> (pws_pred W |-- weak_valid_pointer (offset_val od obase));
  fc_lay: 0 < ocap -> frame_hist fs obase oN oc od e (dm_content dm);
  fc_hp: hist_ptrs_e fs e; fc_hb: bytes_ok (dm_content dm); fc_ed: ext_def e; fc_e0: ext0_ok W fs e;
  fc_ob: isptr obase; fc_ib: isptr ibase;
  fc_par: par_ok pr;
  fc_hdr: fr_hdr3 (dmode_of pr) (sel_on pr dsp) dm s hs h;
  fc_d1: dict_after pr dsp l d d1;
  fc_lent: lent = true -> d1 = d /\ lent_ok pr dsp d l tbl ox s /\ lent_ext d e;
  fc_ds: dict_sel pr dsp l tbl (sublist 0 (header_size_m (dp_fmt pr =? 1) s) s) d d1;
  fc_ds2: sel_on pr dsp = true -> df_ddict d <> nullval ->
    0 <= fh_dictID h <= Int.max_unsigned /\
    (hs_probe l tbl (fh_dictID h) = nullval \/ hs_probe l tbl (fh_dictID h) = df_ddict d1) }.

(* whether the frame's checksum is validated *)
Definition fr_vck : bool := vck (dmode_of pr) h.

(* the frame fields during the loop: the header's values (fParams = h, capped), the checksum state of out,
   the dictID after the header (fdid) *)
Definition fr_xx (out: list Z) : option (list Z) :=
  if fr_vck then Some out else fs_xxh fs.

Definition fr_fs (cold: val) (xx: option (list Z)) : fstate :=
  {| fs_previousDstEnd := fs_previousDstEnd fs; fs_gpDictCopy := fs_gpDictCopy fs;
     fs_prefixStart := fs_prefixStart fs; fs_virtualStart := fs_virtualStart fs; fs_dictEnd := fs_dictEnd fs;
     fs_expected := fs_expected fs; fs_fParams := fh_val h; fs_processedCSize := Vlong (Int64.repr hs);
     fs_decodedSize := fs_decodedSize fs; fs_bType := fs_bType fs; fs_stage := fs_stage fs; fs_xxh := xx;
     fs_headerSize := fs_headerSize fs; fs_validateChecksum := Vint (Int.repr (if fr_vck then 1 else 0));
     fs_rleSize := fs_rleSize fs; fs_isFrameDecompression := fs_isFrameDecompression fs;
     fs_dictID := Vint (Int.repr fdid); fs_ddictIsCold := cold |}.

(* the frame fields after ZSTD_decodeFrameHeader (dfh3_ok0) and the shrink of blockSizeMax *)
Lemma fr_fs_init: forall h0 cold,
  h = fh_cap (dmode_of pr) h0 -> cold = fs_ddictIsCold fs ->
  fsu_fParams
    (fsu_processedCSize
      (fsu_xxh (fsu_validateChecksum (fsu_dictID (fsu_fParams fs (fh_val h0)) (Vint (Int.repr fdid)))
                  (Vint (Int.repr (if vck (dmode_of pr) h0 then 1 else 0))))
         (if vck (dmode_of pr) h0 then Some nil else fs_xxh fs))
      (Vlong (Int64.repr hs)))
    (fh_val h) = fr_fs cold (fr_xx nil).
Proof. intros h0 cold Hh Hc. subst cold. unfold fr_fs, fr_xx, fr_vck. rewrite Hh. reflexivity. Qed.

(* the loop's fParams carry a 32-bit dictID *)
Lemma fr_fp: fr_ctx -> forall cold xx, fp_ok (fs_fParams (fr_fs cold xx)).
Proof.
  intros HC cold xx. destruct (fc_hdr HC) as (Hb & _ & _ & _ & h0 & Hg & Eh & _).
  assert (Hbs: bytes_ok (sublist 0 hs s)) by (apply Forall_sublist; exact Hb).
  destruct (gfh3_range _ _ _ Hbs Hg) as (_ & _ & _ & _ & Hd).
  exists (fh_dictID h). split; [reflexivity | ]. rewrite Eh. cbn [fh_cap fh_dictID]. rep_lia.
Qed.

(* the selection's resources during the loop (with `lent` the local DDict's entropy is in dent_of) *)
Definition fr_selR : mpred := sel_any DENT gv p pr dsp d1 l tbl xq lent am hb.

Lemma fr_selR_post: fr_ctx ->
  fr_selR * dent_of DENT gv ox |-- sel_any DENT gv p pr dsp d1 l tbl xq lent am hb * dent_of DENT gv ox.
Proof. intros HC. pose proof (fc_hdr HC). pose proof (fc_lent HC). unfold fr_selR. cancel. Qed.

(* the resources of the loop: the blockProperties cell, the frame fields, the tables, the output *)
Definition fr_SEP (bpcell: mpred) (ff: fstate) (tabs: mpred) (oc1: list val) : list mpred :=
  [bpcell; data_at Ers tulong (Vlong (Int64.repr 3)) (gv _ZSTD_blockHeaderSize); zg_rest gv; pws_pred W;
   field_at Ews t_dctx (DOT _format) (Vint (Int.repr (dp_fmt pr))) p;
   field_at Ews t_dctx (DOT _disableHufAsm) (Vint (Int.repr 0)) p;
   frame_fields p ff;
   field_at Ews t_dctx (DOT _forceIgnoreChecksum) (Vint (Int.repr (dp_ignore pr))) p;
   field_at Ews t_dctx (DOT _maxBlockSizeParam) (Vint (Int.repr (dp_bmax pr))) p;
   field_at Ews t_dctx (DOT _refMultipleDDicts) (Vint (Int.repr (dp_multi pr))) p;
   field_at Ews t_dctx (DOT _ddictSet) dsp p;
   fr_selR; tabs; dent_of DENT gv ox;
   data_at osh (tarray tuchar oN) oc1 obase;
   data_at ish (tarray tuchar iN) ic ibase; ext_res e;
   data_at Tsh (tptr tvoid) (offset_val ioff ibase) sp;
   data_at Tsh tulong (Vlong (Int64.repr (Zlength s))) ssp].

(* the locals of the loop: ip at block j, op after out *)
Definition fr_LOC (j: Z) (out: list Z) : list localdef :=
  [temp _ip (offset_val (ioff + hs + j) ibase); temp _op (offset_val (od + Zlength out) obase);
   temp _remainingSrcSize (Vlong (Int64.repr (Zlength s - hs - j)));
   temp _ostart (offset_val od obase); temp _oend (offset_val (od + ocap) obase);
   temp _istart (offset_val ioff ibase);
   lvar _blockProperties (Tstruct ___gp_blockProperties_t noattr) v_bp; gvars gv; temp _dctx p;
   temp _srcPtr sp; temp _srcSizePtr ssp].

(* the output so far *)
Definition fr_outP (j: Z) (out: list Z) (oc1: list val) (cold: val) : list Prop :=
  [0 <= j; hs + j <= Zlength s; Zlength out <= ocap; bytes_ok out; Zlength oc1 = oN;
   unchanged_outside oc oc1 od (od + ocap); sublist od (od + Zlength out) oc1 = zbytes out;
   cold = fs_ddictIsCold fs \/ cold = Vint (Int.repr 0)].

(* ---------- the exact model (model/ExFrame.v, ExFrameFacts.v) along the loop ---------- *)

(* the exact claims are made for the context's own tables without a dictionary, with the default parameters *)
Definition fx_on : Prop := ox = None /\ dm = no_dict /\ pr = dparams_dflt /\ e = ExtNone.

(* the model's state the frame's blocks start from (x_frame's ZSTD_decompressBegin on the tables' state ts0) *)
Definition fr_X0 : xstate := xst_begin xhuf (ts_x ts0).

(* the model's blocks of the frame, from its first block, are those from block j (at offset j, after the output
   out, from the tables' state st), shifted by j; the tables' Huffman table emits bytes (ExBlockBytes.xh_good: the
   model's content is then bytes, which identifies it with what the C wrote) *)
Definition fr_xinv (j: Z) (out: list Z) (st: tstate) : Prop :=
  fx_on ->
  xh_good (x_huf xhuf (ts_x st)) /\
  xbs xstate xblock fr_X0 (fr_rest s hs) [] ocap (fh_blockSizeMax h) =
  xb_shift xstate j (xbs xstate xblock (ts_x st) (fr_t s hs j) out ocap (fh_blockSizeMax h)).

(* block j's decoding agrees with the model's step xb_one: an error iff the step fails; else its content cnt and
   the tables' state st2 are the step's *)
Definition fr_xdec (j: Z) (out: list Z) (st: tstate) (r: Z) (st2: tstate) (cnt: list Z) : Prop :=
  fx_on ->
  match xb_one xstate xblock (ts_x st) (fr_t s hs j) out ocap (fh_blockSizeMax h) with
  | None => is_error_code r = true
  | Some (st', cn, _, _) => is_error_code r = false /\ cn = cnt /\ ts_x st2 = st'
  end.

(* after the last block: the model's blocks of the frame end at j with the output out and the tables' state st *)
Definition fr_xaft (j: Z) (out: list Z) (st: tstate) : Prop :=
  fx_on -> xbs xstate xblock fr_X0 (fr_rest s hs) [] ocap (fh_blockSizeMax h) = Some (out, j, ts_x st).

(* without a dictionary the tables' state at the frame's start is already Begin's *)
Lemma fr_X0_begin: fx_on -> ts_d ts0 = dm_state dm -> ts_x ts0 = fr_X0.
Proof.
  intros (_ & Hdm & _) Hts. rewrite Hdm in Hts. cbn in Hts.
  unfold fr_X0, xst_begin, ts_x. rewrite Hts. reflexivity.
Qed.

(* the loop invariant's exact conjunct holds at the first block *)
Lemma fr_xinv_init: fr_ctx -> ts_d ts0 = dm_state dm -> fr_xinv 0 [] ts0.
Proof.
  intros _ Hts Hx. rewrite (fr_X0_begin Hx Hts). split.
  - (* Begin's state has no Huffman table *)
    unfold fr_X0, xst_begin. cbn. exact I.
  - rewrite xb_shift_0. unfold fr_t, fr_rest. rewrite Z.add_0_r. reflexivity.
Qed.

(* the exact frame (x_frame, from the tables' state ts0) is its header's checks, which the header of the frame
   passed (fr_hdr3), then the model's blocks from fr_X0, then the end of the frame (content size, checksum) *)
Lemma fr_x_frame: fr_ctx -> fx_on ->
  x_frame xstate (xst_begin xhuf) xblock (ts_x ts0) s ocap =
  match xbs xstate xblock fr_X0 (fr_rest s hs) [] ocap (fh_blockSizeMax h) with
  | None => None
  | Some (out, k, st') => x_fend xstate h s hs out k st'
  end.
(* stated over all the section's variables, as the segment proofs apply it *)
Proof using All.
  intros HC (Hox & Hdm & Hpr & He).
  pose proof (fc_hdr HC) as (Hb & Hl1 & Hhs & Hl2 & h0 & Hg & Eh & Hsel & _).
  rewrite Hpr in *. rewrite Hdm in *. cbn [dmode_of dparams_dflt md_magicless dp_fmt Z.eqb] in *.
  (* without the selection the header's dictID is 0 (no dictionary) *)
  assert (Hsel0: sel_on dparams_dflt dsp = false) by reflexivity.
  rewrite Hsel0 in Hsel. specialize (Hsel eq_refl). cbn in Hsel.
  unfold header_size_m in Hhs. rewrite get_frame_header_zstd1 in Hg.
  assert (Hbs: bytes_ok (sublist 0 hs s)) by (apply Forall_sublist; exact Hb).
  pose proof (gfh3_range false _ _ Hbs ltac:(rewrite get_frame_header_zstd1; exact Hg)) as Hr.
  rewrite (x_frame_eq xstate (xst_begin xhuf) xblock)
    by (unfold ZSTD_FRAMEHEADERSIZE_MIN, ZSTD_blockHeaderSize, mg_sh in *; cbn in *; lia).
  cbv zeta. rewrite <- Hhs.
  assert (Es: slice s 0 hs = sublist 0 hs s) by (unfold slice; rewrite sublist_firstn; reflexivity).
  rewrite Es, Hg.
  assert (Ed: fh_dictID h0 = 0) by (destruct Hsel; assumption). rewrite Ed. cbn [negb Z.eqb].
  (* the default parameters do not cap Block_Maximum_Size *)
  assert (Eh0: h = h0).
  { rewrite Eh. unfold fh_cap. cbn [dmode_of md_bmax dparams_dflt dp_bmax Z.eqb].
    rewrite Z.min_l by (unfold ZSTD_BLOCKSIZE_MAX in *; lia). destruct h0; reflexivity. }
  rewrite Eh0. unfold fr_rest. rewrite frm_sub_end. reflexivity.
Qed.

(* the loop invariant: at block j *)
Definition S_inv (j: Z) (out: list Z) (oc1: list val) (st: tstate) (cold: val) : environ -> mpred :=
  PROPx (fr_OT dm h s hs j out st :: fr_xinv j out st :: fr_outP j out oc1 cold)
  (LOCALx (fr_LOC j out)
  (SEPx (fr_SEP (data_at_ Tsh (Tstruct ___gp_blockProperties_t noattr) v_bp) (fr_fs cold (fr_xx out))
           (TABS gv p ox st) oc1))).

Definition fr_Inv : environ -> mpred :=
  EX j: Z, EX out: list Z, EX oc1: list val, EX st: tstate, EX cold: val, S_inv j out oc1 st cold.

(* after the loop: the last block ends at j; a refused frame's end is refused (fr_RE) *)
Definition S_aft (j: Z) (out: list Z) (oc1: list val) (st: tstate) (cold: val) : environ -> mpred :=
  PROPx ((forall o k, fr_DB dm h s hs = Some (o, k) -> o = out /\ k = j) :: fr_outP j out oc1 cold ++
         [exists f nb, blocks_size f (fr_rest s hs) = Some (j, nb); fr_RE dm h s hs j out; fr_xaft j out st])
  (LOCALx (fr_LOC j out)
  (SEPx (fr_SEP (data_at_ Tsh (Tstruct ___gp_blockProperties_t noattr) v_bp) (fr_fs cold (fr_xx out))
           (TABS gv p ox st) oc1))).

Definition fr_Brk : environ -> mpred :=
  EX j: Z, EX out: list Z, EX oc1: list val, EX st: tstate, EX cold: val, S_aft j out oc1 st cold.

(* the ret_assert of the loop body *)
Definition fr_LR : ret_assert := loop1_ret_assert fr_Inv (overridePost fr_Brk fr_R).

(* before the switch: the block header read (c = cblock_size of the bytes at block j), ip at its body *)
Definition S_sw (j: Z) (out: list Z) (oc1: list val) (st: tstate) (cold: val) (c: Z) : environ -> mpred :=
  PROPx (fr_OT dm h s hs j out st :: (cblock_size (fr_t s hs j) = Some c) ::
         (c <= Zlength (fr_t s hs j) - ZSTD_blockHeaderSize) :: fr_xinv j out st :: fr_outP j out oc1 cold)
  (LOCALx (temp _cBlockSize (Vlong (Int64.repr c)) :: temp _oBlockEnd (offset_val (od + ocap) obase) ::
           fr_LOC (j + ZSTD_blockHeaderSize) out)
  (SEPx (fr_SEP (data_at Tsh (Tstruct ___gp_blockProperties_t noattr) (bp_val (block_props_of (fr_t s hs j))) v_bp)
           (fr_fs cold (fr_xx out)) (TABS gv p ox st) oc1))).

(* after the block's decoding: r (decodedSize), the output oc2 (cnt written after out on a success), the
   tables' state st2 (after a success; after an error only its litExtraBuffer bytes ts_lxb st2 count: the tables are
   uninitialised), cold2; the model's step blk_res agrees, and so does zstd's rblock for a raw or RLE block (fr_RL) *)
Definition S_dec (j: Z) (out: list Z) (oc1: list val) (st: tstate) (cold: val) (c: Z)
    (r: Z) (oc2: list val) (st2: tstate) (cold2: val) (cnt: list Z) : environ -> mpred :=
  PROPx (fr_OT dm h s hs j out st :: (cblock_size (fr_t s hs j) = Some c) ::
         (c <= Zlength (fr_t s hs j) - ZSTD_blockHeaderSize) :: fr_outP j out oc1 cold ++
         [0 <= r <= Int64.max_unsigned; Zlength oc2 = oN;
          unchanged_outside oc1 oc2 (od + Zlength out) (od + ocap);
          is_error_code r = false ->
            r <= ocap - Zlength out /\ Zlength cnt = r /\ bytes_ok cnt /\
            sublist (od + Zlength out) (od + Zlength out + r) oc2 = zbytes cnt;
          is_error_code r = true -> dec_err r;
          forall st' out',
            blk_res st (dm_content dm) out (fr_t s hs j) c (fh_blockSizeMax h) (fh_windowSize h) = Some (st', out') ->
            (is_error_code r = false -> out' = out ++ cnt /\ ts_d st2 = st') /\
            (is_error_code r = true -> ocap < Zlength out');
          cold2 = fs_ddictIsCold fs \/ cold2 = Vint (Int.repr 0);
          (* a Raw or RLE block reports a too small capacity as dstSize_tooSmall *)
          bp_type (block_props_of (fr_t s hs j)) <> 2 -> is_error_code r = true ->
            r = err_code ZSTD_error_dstSize_tooSmall;
          fr_RL dm h s hs j out st c r cnt st2;
          fr_xinv j out st; fr_xdec j out st r st2 cnt])
  (LOCALx (temp _decodedSize (Vlong (Int64.repr r)) ::
           temp _cBlockSize (Vlong (Int64.repr c)) :: temp _oBlockEnd (offset_val (od + ocap) obase) ::
           fr_LOC (j + ZSTD_blockHeaderSize) out)
  (SEPx (fr_SEP (data_at Tsh (Tstruct ___gp_blockProperties_t noattr) (bp_val (block_props_of (fr_t s hs j))) v_bp)
           (fr_fs cold2 (fr_xx out)) (if is_error_code r then tables_uninit p (ts_lxb st2) else TABS gv p ox st2) oc2))).

(* ---------- the segments ---------- *)

(* loop body, statements 0..7: the block header *)
Definition fr_B1_stmt : Prop :=
  forall {Espec: OracleKind} (k: statement) j out oc1 st cold,
  fr_ctx ->
  (forall c, semax fr_Delta (S_sw j out oc1 st cold c) k fr_LR) ->
  semax fr_Delta (S_inv j out oc1 st cold) (seq_cut 8 fr_lb k) fr_LR.

(* the three block types: the call and decodedSize = its result *)
Definition fr_case_stmt (lbl: Z) : Prop :=
  forall {Espec: OracleKind} j out oc1 st cold c,
  fr_ctx -> bp_type (block_props_of (fr_t s hs j)) = lbl ->
  semax fr_Delta (S_sw j out oc1 st cold c) (fr_case lbl)
    (normal_ret_assert (EX r: Z, EX oc2: list val, EX st2: tstate, EX cold2: val, EX cnt: list Z,
                          S_dec j out oc1 st cold c r oc2 st2 cold2 cnt)).

(* loop body, statement 8: the switch *)
Definition fr_B2_stmt : Prop :=
  forall {Espec: OracleKind} (k: statement) j out oc1 st cold c,
  fr_ctx ->
  (forall r oc2 st2 cold2 cnt, semax fr_Delta (S_dec j out oc1 st cold c r oc2 st2 cold2 cnt) k fr_LR) ->
  semax fr_Delta (S_sw j out oc1 st cold c) (Ssequence fr_sw k) fr_LR.

(* loop body, statements 9..16: the error check, the checksum, the advance, the last block *)
Definition fr_B3_stmt : Prop :=
  forall {Espec: OracleKind} j out oc1 st cold c r oc2 st2 cold2 cnt,
  fr_ctx ->
  semax fr_Delta (S_dec j out oc1 st cold c r oc2 st2 cold2 cnt) (seq_drop 9 fr_lb) fr_LR.

(* statements 11..17: the content size, the checksum, the results *)
Definition fr_end_stmt : Prop :=
  forall {Espec: OracleKind} j out oc1 st cold,
  fr_ctx ->
  semax fr_Delta (S_aft j out oc1 st cold) (seq_drop 11 fr_body) fr_R.

(* the loop followed by any k (what fr_loop_ok3, Frame3_loop.v, gives from B1, B2, B3), from the tables' state
   ts0 the frame begins with (Begin's: the dictionary's entropy state) *)
Definition fr_loopk_stmt : Prop :=
  forall {Espec: OracleKind} (k: statement),
  fr_ctx -> ts_d ts0 = dm_state dm ->
  (forall j out oc1 st cold, semax fr_Delta (S_aft j out oc1 st cold) k fr_R) ->
  semax fr_Delta (S_inv 0 [] oc ts0 (fs_ddictIsCold fs)) (Ssequence fr_loop k) fr_R.

Definition fr_seg_pair : Prop := fr_loopk_stmt /\ fr_end_stmt.

End FR.

(* the loop and the end, for every frame (what ZSTD_decompressFrame's main proof assumes; Frame3_*.v prove
   them, FS3_frames.v assembles) *)
Definition fr_segs (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR: blrel) : Prop :=
  forall W gv p fs ox dm e osh obase oN oc od ocap ish ibase iN ic ioff s sp ssp v_bp pr dsp d l tbl xq lent am hb
         h hs fdid d1 ts0,
  fr_seg_pair DENT TABS SR BR W gv p fs ox dm e osh obase oN oc od ocap ish ibase iN ic ioff s sp ssp v_bp pr dsp
    d l tbl xq lent am hb h hs fdid d1 ts0.

(* frame_res3 for an error that cannot be a success of the model *)
Lemma fr_err3: forall md dm s cap r oc d k,
  is_error_code r = true ->
  (forall c sz, decode_frame_m md dm no_wlim s = FOk c sz -> cap < Zlength c) ->
  frame_res3 md dm s cap r oc d k.
Proof.
  intros. unfold frame_res3. destruct (decode_frame_m md dm no_wlim s) eqn:E; auto.
  split; intros; [congruence | eapply H0; eauto].
Qed.

(* ======================================================================================
   Tactics for the segments
   ====================================================================================== *)

End CM_Frames3Defs_1.

(* Int64.unsigned (Int64.repr x) = x in the hypotheses, when x is in range *)
Ltac urepr :=
  repeat match goal with
  | H: context [Int64.unsigned (Int64.repr ?x)] |- _ => rewrite (Int64.unsigned_repr x) in H by rep_lia
  | H: context [Int64.unsigned (Int64.add (Int64.repr ?x) (Int64.repr ?y))] |- _ =>
      rewrite (Int64.add_unsigned (Int64.repr x) (Int64.repr y)), (Int64.unsigned_repr x), (Int64.unsigned_repr y) in H by rep_lia
  | H: Int64.ltu (Int64.repr ?a) (Int64.repr ?b) = _ |- _ =>
      unfold Int64.ltu in H; rewrite (Int64.unsigned_repr a), (Int64.unsigned_repr b) in H by rep_lia;
      let Hl := fresh "Hl" in destruct (zlt a b) as [Hl | Hl]; try discriminate H; clear H
  end.

Ltac ctr := match goal with Hc: ?a <> ?b |- _ => exfalso; apply Hc; reflexivity end.

(* zstd's do { .. } while (0) *)
Ltac dw0 :=
  repeat (apply -> seq_assoc);
  lazymatch goal with
  | |- semax _ ?P (Ssequence (Sloop _ Sbreak) _) _ => forward_loop P break: P; [apply andp_left2; apply derives_refl | ..]
  | |- semax _ ?P (Sloop _ Sbreak) _ => forward_loop P break: P; [apply andp_left2; apply derives_refl | ..]
  end.

Ltac dw0p Q :=
  repeat (apply -> seq_assoc);
  lazymatch goal with
  | |- semax _ (PROPx ?Ps ?L) (Ssequence (Sloop _ Sbreak) _) _ =>
      forward_loop (PROPx Ps L) break: (PROPx (Q :: Ps) L); [apply andp_left2; apply derives_refl | ..]
  end.

Section CM_Frames3Defs_2.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.

Lemma zg_eq: forall gv,
  zstd_globals gv = data_at Ers tulong (Vlong (Int64.repr 3)) (gv _ZSTD_blockHeaderSize) * zg_rest gv.
Proof. intros. apply pred_ext; [apply zg_unfold | apply zg_fold]. Qed.

End CM_Frames3Defs_2.

(* the RETURN_ERROR block: four do-while(0) loops, then the return *)
Ltac errblk :=
  repeat (apply -> seq_assoc);
  dw0; [forward; apply andp_left2; apply derives_refl | ];
  repeat (apply -> seq_assoc);
  dw0; [forward_if True; [contradiction | forward; entailer! | forward; entailer!] | ];
  repeat (apply -> seq_assoc);
  dw0; [forward; apply andp_left2; apply derives_refl | ];
  repeat (apply -> seq_assoc);
  dw0; [forward; apply andp_left2; apply derives_refl | ].

(* a do-while(0) whose body changes x (the break assertion: some y with Q y in place of x) *)
Ltac dw0e x Q :=
  repeat (apply -> seq_assoc);
  lazymatch goal with
  | |- semax _ (PROPx ?Ps (LOCALx ?Ls (SEPx ?Rs))) (Ssequence (Sloop _ Sbreak) _) _ =>
      let F := eval pattern x in Rs in
      lazymatch F with
      | ?G _ =>
          forward_loop (PROPx Ps (LOCALx Ls (SEPx Rs)))
            break: (EX y, PROPx (Q y :: Ps) (LOCALx Ls (SEPx (G y))));
          [apply andp_left2; apply derives_refl | ..]
      end
  end.

(* an error return: r the C constant, oc' the output, fs' the frame fields, ts the tables' state;
   leaves the frame_res obligation (after fr_err) *)
(* an error code is a decoder error (not a noForwardProgress code): a constant, or from a hypothesis *)
Ltac solve_dec_err :=
  first [ assumption
        | (unfold dec_err; split; [reflexivity | split; let Hy := fresh in intro Hy; vm_compute in Hy; discriminate Hy])
        | match goal with Hd: dfh_post3 _ _ _ _ _ _ _ _ _ ?r _ _, He: is_error_code ?r = true |- dec_err ?r =>
            exact (dfh3_dec_err _ _ _ _ _ _ _ _ _ _ _ _ Hd He) end ].

(* the ddictIsCold field after an exit: unchanged by the header, cold = old \/ 0 in the loop *)
Ltac solve_cold :=
  cbn [fs_ddictIsCold fr_fs fsu_fParams fsu_processedCSize fsu_xxh fsu_validateChecksum fsu_dictID] in *;
  first [ assumption
        | match goal with Hd: dfh_post3 _ _ _ _ _ ?f _ _ _ _ ?f' _ |- context [fs_ddictIsCold ?f'] =>
            rewrite (dfh3_cold _ _ _ _ _ _ _ _ _ _ _ _ Hd); assumption end
        | match goal with Hc: ?c = fs_ddictIsCold ?f \/ ?c = Vint (Int.repr 0),
                          H': fs_ddictIsCold ?f = _ \/ _ |- _ =>
            destruct Hc as [Hc | Hc]; rewrite Hc; [exact H' | left; reflexivity] end ].

Section CM_Frames3Defs_3.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.

(* NOTE for the segment proofs: v2's errret/errretv (body_frame.v) close an error return against fr_R; in v3 the
   return also needs the dictionary fields d' (d before the header, d1 after it: Exists .. d1) and, in the loop,
   `sep_apply (fr_selR_post .. HC)` to give back sel_res and dent_of; write the variant you need in your file. *)

End CM_Frames3Defs_3.
