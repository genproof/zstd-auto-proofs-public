(* FS3 streaming, ZSTD_decompressStream case zdss_loadHeader: the four
   pieces of ds_case_loadHeader, the C states between them, the returns, and the obligations of the pieces.
   v2's StreamSeg_lhDefs.v (src/proof/dec/FS/) with API v3: the format (get_frame_header_m), the dictionary
   selection (ZSTD_DCtx_selectFrameDDict in piece A, again inside ZSTD_decodeFrameHeader in piece C: the set's
   table tbl is kept explicit from A to C so that both probes are the same), the DDict of the frame
   (ZSTD_decompressBegin_usingDDict(getDDict)), maxWindowSize, maxBlockSizeParam.

   ds_case_loadHeader = s1; ...; s21 (right-nested Ssequence; the Clight is v2's):
   - lh_A = s1..s5:   getFrameHeader_advanced on headerBuffer[0, lhSize), the selection (refMultipleDDicts &&
                      ddictSet), the error return, the "need more input" branch (return the hint / an error, or
                      break with the header loaded);
   - lh_B = s6:       the single-pass shortcut (findFrameCompressedSize_advanced + ZSTD_decompress_usingDDict);
   - lh_C = s7..s13:  the stable-buffer check, Begin_usingDDict(getDDict), the skippable frame or
                      ZSTD_decodeFrameHeader, windowSize = MAX(windowSize, 1 KiB) and maxWindowSize;
   - lh_D = s14..s21: the maxBlockSizeParam cap, the buffer sizes, the (re)allocation, streamStage = zdss_read. *)
Require Export Zstd.proof.dec.v3.FS.stream.S3RetStmts.
Local Open Scope logic.

(* ---------- the pieces of the statement ---------- *)

Ltac lh_drop n t :=
  lazymatch n with
  | O => t
  | S ?m => lazymatch t with Ssequence _ ?r => lh_drop m r end
  end.
Ltac lh_take n t :=
  lazymatch n with
  | S O => lazymatch t with Ssequence ?x _ => x end
  | S ?m => lazymatch t with Ssequence ?x ?r => let y := lh_take m r in constr:(Ssequence x y) end
  end.

Section CM_LH3Defs_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Definition lh_A : statement := ltac:(
  let t := eval cbv delta [ds_case_loadHeader] in ds_case_loadHeader in
  let x := lh_take 5%nat t in exact x).

Definition lh_B : statement := ltac:(
  let t := eval cbv delta [ds_case_loadHeader] in ds_case_loadHeader in
  let r := lh_drop 5%nat t in let x := lh_take 1%nat r in exact x).

Definition lh_C : statement := ltac:(
  let t := eval cbv delta [ds_case_loadHeader] in ds_case_loadHeader in
  let r := lh_drop 6%nat t in let x := lh_take 7%nat r in exact x).

Definition lh_D : statement := ltac:(
  let t := eval cbv delta [ds_case_loadHeader] in ds_case_loadHeader in
  let r := lh_drop 13%nat t in exact r).

Lemma lh_shape : exists s1 s2 s3 s4 s5 s7 s8 s9 s10 s11 s12 s13,
  ds_case_loadHeader =
    Ssequence s1 (Ssequence s2 (Ssequence s3 (Ssequence s4 (Ssequence s5 (Ssequence lh_B
      (Ssequence s7 (Ssequence s8 (Ssequence s9 (Ssequence s10 (Ssequence s11 (Ssequence s12
      (Ssequence s13 lh_D)))))))))))) /\
  lh_A = Ssequence s1 (Ssequence s2 (Ssequence s3 (Ssequence s4 s5))) /\
  lh_C = Ssequence s7 (Ssequence s8 (Ssequence s9 (Ssequence s10 (Ssequence s11 (Ssequence s12 s13))))).
Proof.
do 12 eexists. split; [ | split]; reflexivity.
Qed.

(* ---------- the context with the set's table explicit ---------- *)

(* hset_rep with its table tbl *)
Definition hset_t (am: option cmem) (sp: val) (l: list (val * ddict_st)) (hb: Z) (tbl: list val) : mpred :=
  if eq_dec sp nullval then !! (l = nil /\ hb = 0) && emp
  else !! (l <> nil /\ hb = set_bytes am (Zlength tbl)) && hset_tbl am sp l tbl.

Definition ctx_rep3t (DENT: dent_pred) (TABS: tabs_pred) (gv: globals) (p: val) (k: cst3) (tbl: list val) : mpred :=
  dctx_token p * dctx_pad p *
  (fgroup3 TABS gv p (c3_fs k) (c3_tabs k) (c3_par k) (c3_sp k) * cgroup3 p (c3_stable k) (dp_wmax (c3_par k)) *
   dgroup DENT gv p (c3_dict k) * sgroup p (c3_s k) *
   hset_t (sf_mem (c3_s k)) (c3_sp k) (c3_set k) (sf_held (c3_s k) - local_held (c3_dict k)) tbl).

Lemma hset_rep_t (am: option cmem) (sp: val) (l: list (val * ddict_st)) (hb: Z) :
  hset_rep am sp l hb = EX tbl: list val, hset_t am sp l hb tbl.
Proof.
unfold hset_rep, hset_t, hset_tbl. destruct (eq_dec sp nullval).
- apply pred_ext; [ Exists (@nil val); apply derives_refl | Intros tbl; entailer! ].
- apply pred_ext.
  + Intros tp tbl. Exists tbl. Exists tp. entailer!.
  + Intros tbl tp. Exists tp tbl. entailer!.
Qed.

(* the set holds a nonnegative number of the allocator's bytes *)
Lemma hset_t_held (am: option cmem) (sp: val) (l: list (val * ddict_st)) (hb: Z) (tbl: list val) :
  hset_t am sp l hb tbl |-- !! (0 <= hb).
Proof.
  unfold hset_t, set_bytes. destruct (eq_dec sp nullval); [entailer! |].
  Intros. apply prop_right. subst hb. destruct am; [pose proof (Zlength_nonneg tbl); simpl; lia | lia].
Qed.

Lemma hset_rep_held (am: option cmem) (sp: val) (l: list (val * ddict_st)) (hb: Z) :
  hset_rep am sp l hb |-- !! (0 <= hb).
Proof. rewrite hset_rep_t. Intros tbl. apply hset_t_held. Qed.

Lemma ctx_rep3_t (DENT: dent_pred) (TABS: tabs_pred) (gv: globals) (p: val) (k: cst3) :
  ctx_rep3 DENT TABS gv p k = EX tbl: list val, ctx_rep3t DENT TABS gv p k tbl.
Proof.
unfold ctx_rep3, ctx_rep3t, ctx_body3. rewrite hset_rep_t. apply pred_ext.
- Intros tbl. Exists tbl. cancel.
- Intros tbl. Exists tbl. cancel.
Qed.

Section States.
Variable DENT : dent_pred.
Variable TABS : tabs_pred.

(* ds_LI_S with the table tbl *)
Definition ds_LI_St (a: dsa) (w: lw) (tbl: list val) : list mpred :=
  [data_at Tsh (tptr tschar) (offset_val (w_opc w) (a_ob a)) (a_vop a); pws_pred (a_W a); mem_mgr (a_gv a);
   zstd_globals (a_gv a); ctx_rep3t DENT TABS (a_gv a) (a_d a) (w_k w) tbl;
   dict_res (DD3x DENT) (a_gv a) Ews (dc_dict (a_st a)); set_res (DD3x DENT) (a_gv a) Ews (dc_set (a_st a)) (dc_dict (a_st a));
   data_at (a_sho a) t_outBuffer (a_obf a, (vlong (a_osz a), vlong (a_opos a))) (a_outp a);
   data_at (a_shi a) t_inBuffer (a_ibf a, (vlong (a_isz a), vlong (a_ipos a))) (a_inp a);
   data_at (a_shob a) (tarray tuchar (a_osz a)) (w_oc w) (a_ob a);
   data_at (a_shb a) (tarray tuchar (a_isz a)) (zbytes (a_ibs a)) (a_ib a)].

(* the state at a point of the case: the loop invariant's locals and resources for the witnesses w *)
Definition lh_st (a: dsa) (w: lw) : environ -> mpred :=
  PROPx [] (LOCALx (ds_LI_L a w) (SEPx (ds_LI_S DENT TABS a w))).

Definition lh_stt (a: dsa) (w: lw) (tbl: list val) : environ -> mpred :=
  PROPx [] (LOCALx (ds_LI_L a w) (SEPx (ds_LI_St a w tbl))).

End States.

Lemma lh_st_t (DENT: dent_pred) (TABS: tabs_pred) (a: dsa) (w: lw) :
  lh_st DENT TABS a w = EX tbl: list val, lh_stt DENT TABS a w tbl.
Proof.
unfold lh_st, lh_stt, ds_LI_S, ds_LI_St. rewrite ctx_rep3_t.
apply pred_ext.
- Intros tbl. Exists tbl. apply derives_refl.
- Intros tbl. Exists tbl. apply derives_refl.
Qed.

(* ---------- witnesses ---------- *)

Definition lw_k (w: lw) (k: cst3) : lw :=
  {| w_smw := w_smw w; w_k := k; w_sv := w_sv w; w_ipc := w_ipc w; w_opc := w_opc w; w_oc := w_oc w;
     w_dl := w_dl w |}.

Definition lh_mg (k: cst3) : bool := dp_fmt (c3_par k) =? 1.

(* fParams' dictID is an int (zstd's DCtx is calloc'd; GAP: the representation does not say it) *)
Definition fp_id_ok (v: reptype t_fh) : Prop :=
  exists id, fp_dictID v = Vint (Int.repr id) /\ 0 <= id <= Int.max_unsigned.

(* the C facts at the entry of case 1 (from call_inv / c_core): hb = headerBuffer[0, lhSize) *)
Definition lh_entry (a: dsa) (w: lw) (hb: list Z) : Prop :=
  let k := w_k w in
  let s := c3_s k in
  sf_stage s = zdss_loadHeader /\ sf_lhSize s = vlong (Zlength hb) /\ Zlength hb <= 18 /\ bytes_ok hb /\
  sublist 0 (Zlength hb) (sf_hbuf s) = zbytes hb /\ sf_hostage s = Vint (Int.repr 0) /\
  sf_inPos s = vlong 0 /\ sf_outStart s = vlong 0 /\ sf_outEnd s = vlong 0 /\
  a_ipos a <= w_ipc w <= a_isz a /\ a_opos a <= w_opc w <= a_osz a /\ Zlength (w_oc w) = a_osz a /\
  w_smw w = 1 /\ base_call (a_st a) k /\ hdr_lenok (lh_mg k) hb.

(* facts of a parsed header (Params.get_frame_header_m mg hb = FH_ok h on bytes hb) *)
Definition gfh3_facts (mg: bool) (hb: list Z) (h: frame_header) : Prop :=
  starting_len mg <= Zlength hb /\ 0 <= fh_contentSize h <= Int64.max_unsigned /\
  0 <= fh_windowSize h <= Int64.max_unsigned /\
  fh_blockSizeMax h = Z.min (fh_windowSize h) ZSTD_BLOCKSIZE_MAX /\
  0 <= fh_blockSizeMax h <= ZSTD_BLOCKSIZE_MAX /\
  (fh_checksumFlag h = 0 \/ fh_checksumFlag h = 1) /\ (fh_frameType h = 0 \/ fh_frameType h = 1) /\
  (fh_frameType h = 1 <-> (mg = false /\ is_skippable_magic (le_field hb 0 4) = true)) /\
  (fh_frameType h = 1 ->
     ZSTD_SKIPPABLEHEADERSIZE <= Zlength hb /\ fh_windowSize h = 0 /\ fh_blockSizeMax h = 0 /\
     fh_contentSize h = le_field hb 4 4) /\
  0 <= fh_dictID h <= Int.max_unsigned /\ 0 <= fh_headerSize h <= 18.

(* ---------- the dictionary fields changed ---------- *)

(* the context k with the dictionary fields d1: a selection (ZSTD_DCtx_selectFrameDDict, ZSTD_decodeFrameHeader) or
   ZSTD_getDDict may free the local DDict through the context's allocator, which then holds its bytes
   (FSRepC.local_held) less among the other blocks (sf_held; the form of FSSpecs3.load_int_res) *)
Definition held_redict (s: sfields) (d d1: dfields) : sfields :=
  sf_with_held s (sf_held s - local_held d + local_held d1).

Definition k_redict (k: cst3) (d1: dfields) : cst3 :=
  c3_with_dict (c3_with_s k (held_redict (c3_s k) (c3_dict k) d1)) d1.

Lemma held_redict_same (s: sfields) (d: dfields) : held_redict s d d = s.
Proof.
  destruct s. unfold held_redict, sf_with_held; cbn. f_equal. lia.
Qed.

Lemma k_redict_same (k: cst3) : k_redict k (c3_dict k) = k.
Proof.
  unfold k_redict. rewrite held_redict_same. destruct k; reflexivity.
Qed.

(* the dictionary fields a selection or ZSTD_getDDict leaves: the same local DDict, or none *)
Definition redict_ok (d d1: dfields) : Prop :=
  (df_local d1 = df_local d /\ df_lx d1 = df_lx d) \/ df_local d1 = nullval.

Lemma redict_ok_getddict (d: dfields) : redict_ok d (snd (getddict_res d)).
Proof.
  unfold redict_ok, getddict_res.
  destruct (df_uses d =? 0); [right; reflexivity |]. destruct (df_uses d =? 1); left; split; reflexivity.
Qed.

Lemma redict_ok_sel (d: dfields) (r: val) : redict_ok d (sel_dict d r).
Proof.
  unfold redict_ok, sel_dict. destruct (eq_dec r nullval); [left; split; reflexivity | right; reflexivity].
Qed.

Lemma redict_ok_refl (d: dfields) : redict_ok d d.
Proof. left; split; reflexivity. Qed.

Lemma redict_ok_trans (d d1 d2: dfields) : redict_ok d d1 -> redict_ok d1 d2 -> redict_ok d d2.
Proof.
  unfold redict_ok. intros [[E1 E2] | E1] [[F1 F2] | F1]; try (right; congruence).
  left; split; congruence.
Qed.

Lemma ddx_held_nonneg (x: ddx) : 0 <= ddx_held x.
Proof.
  unfold ddx_held. destruct (dx_mem x); [| lia].
  pose proof (Zlength_nonneg (dx_bytes x)). destruct (ddx_copied x); simpl; lia.
Qed.

Lemma local_held_nonneg (d: dfields) : 0 <= local_held d.
Proof.
  unfold local_held. destruct (eq_dec (df_local d) nullval); [lia |].
  destruct (df_lx d) as [[x buf] |]; [apply ddx_held_nonneg | lia].
Qed.

Lemma local_held_redict (d d1: dfields) : redict_ok d d1 -> local_held d1 = local_held d \/ local_held d1 = 0.
Proof.
  unfold redict_ok, local_held. intros [[E1 E2] | E1]; [left; rewrite E1, E2; reflexivity |].
  right. rewrite E1. destruct (eq_dec nullval nullval); [reflexivity | congruence].
Qed.

Lemma local_mem_redict (am: option cmem) (d d1: dfields) : redict_ok d d1 -> local_mem am d -> local_mem am d1.
Proof.
  unfold redict_ok, local_mem. intros [[E1 E2] | E1] H Hn; [rewrite E1, E2 in *; auto | contradiction].
Qed.

(* the default allocator's local DDict is of the default allocator: it holds none of an own one *)
Lemma local_held_none (d: dfields) : local_mem None d -> local_held d = 0.
Proof.
  unfold local_mem, local_held. intros H. destruct (eq_dec (df_local d) nullval) as [E | E]; [reflexivity |].
  destruct (H E) as [_ H2]. destruct (df_lx d) as [[x buf] |] eqn:Ex; [| reflexivity].
  specialize (H2 x buf eq_refl). unfold ddx_held. destruct (dx_mem x); [contradiction | reflexivity].
Qed.

(* the allocator's bytes besides the context, the stream buffer and the local DDict do not change *)
Lemma held_redict_set (s: sfields) (d d1: dfields) :
  sf_held (held_redict s d d1) - local_held d1 = sf_held s - local_held d.
Proof. unfold held_redict, sf_with_held; cbn. lia. Qed.

Lemma sf_given_redict (s: sfields) (d d1: dfields) :
  sf_given (held_redict s d d1) = sf_given s - local_held d + local_held d1.
Proof. unfold sf_given, held_redict, sf_with_held; cbn. lia. Qed.

(* room for the stream buffers next to fewer bytes of the other blocks *)
Lemma mem_room_le (s s': sfields) :
  sf_mem s' = sf_mem s -> 0 <= sf_held s' <= sf_held s -> mem_room s -> mem_room s'.
Proof.
  unfold mem_room. intros Hm Hh Hr. rewrite Hm. destruct (sf_mem s); [| lia].
  destruct Hr as [Hr | Hr]; [left; lia |].
  destruct (Z.eq_dec (sf_held s') 0); [left; assumption | right; lia].
Qed.

(* a selection or ZSTD_getDDict frees the local DDict or keeps it: the allocator holds no more after it *)
Lemma local_held_redict_le (d d1: dfields) : redict_ok d d1 -> local_held d1 <= local_held d.
Proof.
  intros H. pose proof (local_held_nonneg d). destruct (local_held_redict _ _ H) as [E | E]; lia.
Qed.

(* the call's allocator facts (S3Main.mem_call) after the selection or ZSTD_getDDict: the allocator holds no more
   than before, the local DDict is the same or none *)
Lemma mem_call_redict (st: dctx_st) (k: cst3) (d1: dfields) :
  mem_call st k -> 0 <= sf_held (c3_s k) - local_held (c3_dict k) -> redict_ok (c3_dict k) d1 ->
  mem_call st (k_redict k d1).
Proof.
  intros (Hm & Hr & Hl) Hh Hd. unfold mem_call, k_redict, held_redict, sf_with_held, c3_with_dict, c3_with_s.
  cbn [c3_s c3_dict sf_mem sf_held]. split; [exact Hm |]. split; [| exact (local_mem_redict _ _ _ Hd Hl)].
  pose proof (local_held_nonneg d1) as N1. pose proof (local_held_nonneg (c3_dict k)) as N0.
  destruct (local_held_redict _ _ Hd) as [E | E]; rewrite E.
  - replace (sf_held (c3_s k) - local_held (c3_dict k) + local_held (c3_dict k)) with (sf_held (c3_s k)) by lia.
    exact Hr.
  - unfold mem_room in *. cbn [sf_mem sf_held] in *. destruct (sf_mem (c3_s k)) as [m |] eqn:Em.
    + destruct Hr as [Hr | Hr]; [left; lia | ].
      destruct (Z.eq_dec (sf_held (c3_s k) - local_held (c3_dict k) + 0) 0); [left; lia | right; lia].
    + rewrite (local_held_none _ Hl). lia.
Qed.

(* ---------- piece A ---------- *)

(* zds->fParams := v, then the selection: dictionary fields d1, the context's dictID did1 *)
Definition k_A (k: cst3) (v: reptype t_fh) (d1: dfields) (did1: val) : cst3 :=
  k_redict (c3_with_fs k (fsu_dictID (fsu_fParams (c3_fs k) v) did1) (c3_tabs k)) d1.

(* what ZSTD_DCtx_selectFrameDDict did for the dictID id with the set's table tbl (nothing when off) *)
Definition sel_by (k: cst3) (tbl: list val) (id: Z) (d1: dfields) (did1: val) : Prop :=
  if sel_on (c3_par k) (c3_sp k) then
    let r := sel_r (c3_dict k) (c3_set k) tbl id in
    hs_inv (c3_set k) tbl /\ 0 <= id <= Int.max_unsigned /\ d1 = sel_dict (c3_dict k) r /\
    did1 = (if eq_dec r nullval then fs_dictID (c3_fs k) else Vint (Int.repr id))
  else d1 = c3_dict k /\ did1 = fs_dictID (c3_fs k).

(* the whole of piece A's first two statements: hSize = getFrameHeader_advanced(..) with fParams v0 -> v, and
   the selection on v's dictID (read only when the selection is on: off, v's dictID may be anything) *)
Definition lhA_sel (k: cst3) (hb: list Z) (hSize: Z) (v: reptype t_fh) (tbl: list val) (d1: dfields) (did1: val)
    : Prop :=
  0 <= hSize <= Int64.max_unsigned /\ fh_post_m (lh_mg k) hb hSize (fs_fParams (c3_fs k)) v /\
  exists id, (sel_on (c3_par k) (c3_sp k) = true -> fp_dictID v = Vint (Int.repr id)) /\ sel_by k tbl id d1 did1.

(* piece A's selection keeps the local DDict or frees it *)
Lemma lhA_sel_redict (k: cst3) (hb: list Z) (hSize: Z) (v: reptype t_fh) (tbl: list val) (d1: dfields) (did1: val) :
  lhA_sel k hb hSize v tbl d1 did1 -> redict_ok (c3_dict k) d1.
Proof.
  intros (_ & _ & id & _ & Hs). unfold sel_by in Hs. destruct (sel_on (c3_par k) (c3_sp k)).
  - destruct Hs as (_ & _ & -> & _). apply redict_ok_sel.
  - destruct Hs as (-> & _). apply redict_ok_refl.
Qed.

(* lhSize := lh, headerBuffer := hbuf *)
Definition sf_lh (s: sfields) (lh: Z) (hbuf: list val) : sfields :=
  {| sf_stage := sf_stage s; sf_inBuff := sf_inBuff s; sf_inSize := sf_inSize s; sf_inPos := sf_inPos s;
     sf_outBuff := sf_outBuff s; sf_outSize := sf_outSize s; sf_outStart := sf_outStart s;
     sf_outEnd := sf_outEnd s; sf_lhSize := vlong lh; sf_hostage := sf_hostage s; sf_nfp := sf_nfp s;
     sf_expOut := sf_expOut s; sf_hbuf := hbuf; sf_over := sf_over s; sf_ring := sf_ring s; sf_mem := sf_mem s; sf_held := sf_held s |}.

(* the header buffer c after copying the bytes u at n *)
Definition hb_splice (c: list val) (n: Z) (u: list Z) : list val :=
  sublist 0 n c ++ zbytes u ++ sublist (n + Zlength u) 18 c.

(* the context k after copying the input bytes [ipc, ipc + m) behind hb (fParams := v) *)
Definition lh_k_load (a: dsa) (w: lw) (k: cst3) (hb: list Z) (m: Z) (v: reptype t_fh) : cst3 :=
  let u := sublist (w_ipc w) (w_ipc w + m) (a_ibs a) in
  c3_with_s (c3_with_fs k (fsu_fParams (c3_fs k) v) (c3_tabs k))
    (sf_lh (c3_s k) (Zlength hb + m) (hb_splice (sf_hbuf (c3_s k)) (Zlength hb) u)).

(* the break of the need-more branch (context k1 after the selection): the header loaded up to kk bytes,
   ip += kk - |hb| (no second getFrameHeader_advanced: fParams is the first call's) *)
Definition lhA_brk (a: dsa) (w: lw) (k1: cst3) (hb: list Z) (kk: Z) : lw :=
  {| w_smw := w_smw w; w_k := lh_k_load a w k1 hb (kk - Zlength hb) (fs_fParams (c3_fs k1)); w_sv := w_sv w;
     w_ipc := w_ipc w + (kk - Zlength hb); w_opc := w_opc w; w_oc := w_oc w; w_dl := w_dl w |}.

(* the hint returned when the input ends inside the header (fix F2; FRAMEHEADERSIZE_MIN(format) = 6
   or 2): hb' = the header bytes now loaded, hSize = what the first getFrameHeader_advanced asked for *)
Definition lh_hint (mg: bool) (hb': list Z) (hSize: Z) : Z :=
  if andb (negb mg) (orb (Zlength hb' <? 4) (is_skippable_frame hb' =? 1))
  then (if Zlength hb' <? 4 then ZSTD_SKIPPABLEHEADERSIZE else hSize) - Zlength hb'
  else Z.max (if mg then 2 else 6) hSize - Zlength hb' + ZSTD_blockHeaderSize.

(* ---------- piece B: the shortcut ---------- *)

Definition sf_stage_set (s: sfields) (st: Z) : sfields :=
  {| sf_stage := st; sf_inBuff := sf_inBuff s; sf_inSize := sf_inSize s; sf_inPos := sf_inPos s;
     sf_outBuff := sf_outBuff s; sf_outSize := sf_outSize s; sf_outStart := sf_outStart s;
     sf_outEnd := sf_outEnd s; sf_lhSize := sf_lhSize s; sf_hostage := sf_hostage s; sf_nfp := sf_nfp s;
     sf_expOut := sf_expOut s; sf_hbuf := sf_hbuf s; sf_over := sf_over s; sf_ring := sf_ring s; sf_mem := sf_mem s; sf_held := sf_held s |}.

(* the dictionary model zstd decodes the frame x with in the shortcut (context k1, after the selection): no set,
   the context's dictionary; a set (selection on), the set's DDict of the frame's Dictionary_ID, else the
   current DDict (a member) *)
Definition lh_fdm (a: dsa) (k1: cst3) (x: list Z) (dm: dict_model) : Prop :=
  let st := a_st a in
  (dc_set st = nil /\ dictref_model (dc_dict st) = Some dm) \/
  (dc_set st <> nil /\ sel_on (c3_par k1) (c3_sp k1) = true /\ set_clean (dc_set st) = true /\
   df_ddict (snd (getddict_res (c3_dict k1))) <> nullval /\
   exists h q dd, get_frame_header_m (lh_mg k1) x = FH_ok h /\ fh_frameType h = 0 /\
     frame_compressed_size_m (lh_mg k1) x = Some (Zlength x) /\
     q = (if eq_dec (set_find (dc_set st) (fh_dictID h)) nullval then df_ddict (c3_dict k1)
          else set_find (dc_set st) (fh_dictID h)) /\
     In (q, dd) (dc_set st) /\ dict_auto (dd_bytes dd) = Some dm).

(* the conditions of the shortcut (the header is complete, all of it came in this call) and the result of
   ZSTD_decompress_usingDDict on the frame [ipos, ipos + cSize) of the input into op[0, cap) *)
Definition lhB_facts (a: dsa) (w: lw) (k1: cst3) (hb: list Z) (h: frame_header) (cSize r: Z) (out: list val)
    : Prop :=
  let cap := a_osz a - w_opc w in
  let x := sublist (a_ipos a) (a_ipos a + cSize) (a_ibs a) in
  fh_frameType h <> 1 /\ fh_contentSize h <> ZSTD_CONTENTSIZE_UNKNOWN /\ fh_contentSize h <= cap /\
  w_ipc w - a_ipos a = Zlength hb /\
  frame_compressed_size_m (lh_mg k1) (sublist (a_ipos a) (a_isz a) (a_ibs a)) = Some cSize /\
  cSize <= a_isz a - a_ipos a /\
  0 <= r <= Int64.max_unsigned /\ Zlength out = cap /\
  (is_error_code r = false -> r <= cap) /\ (is_error_code r = true -> dec_err r) /\
  (forall dm, lh_fdm a k1 x dm -> oneshot_ok (dmode_of (c3_par k1)) (Some dm) x cap r out).

(* the stream fields after the shortcut: streamStage = zdss_init (code fix F10: the one-shot decoding sets it, on
   success and on error), the local DDict maybe freed (dictionary fields d') *)
Definition lhB_s (k1: cst3) (d': dfields) : sfields :=
  sf_stage_set (held_redict (c3_s k1) (c3_dict k1) d') zdss_init.

(* the context after ZSTD_getDDict + ZSTD_decompress_usingDDict (frame fields fs', tables uninitialized with the
   litExtraBuffer lxb' the one-shot decoding left, dictionary fields d') *)
Definition lhB_k (k1: cst3) (fs': fstate) (d': dfields) (lxb': list Z) : cst3 :=
  c3_with_dict (c3_with_fs (c3_with_s k1 (lhB_s k1 d')) fs' (TUninit lxb')) d'.

(* the dictionary fields after the shortcut: getDDict's, or (selection on) a member of the set *)
Definition lhB_dict (k1: cst3) (d': dfields) : Prop :=
  d' = snd (getddict_res (c3_dict k1)) \/
  (sel_on (c3_par k1) (c3_sp k1) = true /\ exists q, In q (map fst (c3_set k1)) /\ d' = switch_fields q).

(* D-S2: after a successful shortcut with the selection on and a current DDict, fParams' dictID probes nothing
   else than the DDict the context now has *)
Definition lhB_sel_fp (k1: cst3) (tbl: list val) (x: list Z) (fs': fstate) (d': dfields) : Prop :=
  sel_on (c3_par k1) (c3_sp k1) = true -> df_ddict (snd (getddict_res (c3_dict k1))) <> nullval ->
  (exists h, get_frame_header_m (lh_mg k1) x = FH_ok h /\ fh_frameType h = 0) ->
  exists id, fp_dictID (fs_fParams fs') = Vint (Int.repr id) /\ 0 <= id <= Int.max_unsigned /\
    (hs_probe (c3_set k1) tbl id = nullval \/ hs_probe (c3_set k1) tbl id = df_ddict d').

(* the dictionary fields after the shortcut, as zstd sets them: getDDict's, or (selection on) the member the
   probe finds for the frame's Dictionary_ID (FS3 R3: usingDDict_int_spec3's single-frame POST) *)
Definition lhB_sw (k1: cst3) (tbl: list val) (x: list Z) (d': dfields) : Prop :=
  d' = snd (getddict_res (c3_dict k1)) \/
  (sel_on (c3_par k1) (c3_sp k1) = true /\ exists q, In q (map fst (c3_set k1)) /\ d' = switch_fields q /\
     forall h, get_frame_header_m (lh_mg k1) x = FH_ok h -> q = hs_probe (c3_set k1) tbl (fh_dictID h)).

(* the break after a successful shortcut: expected = 0, streamStage = zdss_init, someMoreWork = 0,
   ip = istart + cSize, op += r, the bytes c delivered *)
Definition lhB_brk (w: lw) (k1: cst3) (fs': fstate) (d': dfields) (lxb': list Z) (ipc' r: Z) (out: list val)
    (c: list Z) : lw :=
  let k' := lhB_k k1 fs' d' lxb' in
  {| w_smw := 0;
     w_k := c3_with_s (c3_with_fs k' (fsu_expected fs' (vlong 0)) (TUninit lxb')) (lhB_s k1 d');
     w_sv := w_sv w; w_ipc := ipc'; w_opc := w_opc w + r; w_oc := sublist 0 (w_opc w) (w_oc w) ++ out;
     w_dl := w_dl w ++ c |}.

(* ---------- piece C ---------- *)

(* what piece C chose: the DDict ZSTD_getDDict returned and ZSTD_decompressBegin_usingDDict began the frame with
   (None: none) and its content buffer, ddictIsCold after it, the dictID ZSTD_decodeFrameHeader left, and the
   bytes litExtraBuffer kept through ZSTD_decompressBegin_usingDDict *)
Record lhc := { lc_dd : option (ddx * val); lc_cold : val; lc_did : Z; lc_lxb : list Z }.

(* the tables after ZSTD_decompressBegin_usingDDict with the DDict dd, litExtraBuffer holding lxb *)
Definition lh_dd_ts (dd: option (ddx * val)) (lxb: list Z) : tstate :=
  match dd with Some (x, _) => mk_tstate (ddx_state x) false lxb | None => tstate_begin lxb end.

(* ZSTD_decompressBegin_usingDDict's frame fields (format fmt) *)
Definition lh_dd_fs (fs: fstate) (fmt: Z) (dd: option (ddx * val)) (cold: val) : fstate :=
  match dd with
  | None => fs_begin3 fs fmt
  | Some (x, buf) =>
      fs_set_dictEnd
        (fs_with_dict (fs_set_cold (fs_begin3 fs fmt) cold) buf (ddx_end x buf)
           (if ddx_copied x then 1 else 0) (if dx_raw x then 0 else dict_id_of (dx_bytes x)))
        (ddx_end x buf)
  end.

(* the context's dictID after ZSTD_decompressBegin_usingDDict *)
Definition lh_dd_did (dd: option (ddx * val)) : Z :=
  match dd with None => 0 | Some (x, _) => if dx_raw x then 0 else dict_id_of (dx_bytes x) end.

(* the frame fields after piece C: Begin_usingDDict, then the skippable frame (expected = its size, stage =
   skipFrame) or ZSTD_decodeFrameHeader (dictID did, validateChecksum = flag && !ignore, processedCSize = |hb|;
   expected = 3, stage = decodeBlockHeader), then windowSize = MAX(windowSize, 1 KiB) *)
Definition lhC_fs (k1: cst3) (hb: list Z) (h: frame_header) (c: lhc) : fstate :=
  let fsB := lh_dd_fs (c3_fs k1) (dp_fmt (c3_par k1)) (lc_dd c) (lc_cold c) in
  let ha := fh_val (fh_adj h (fh_blockSizeMax h)) in
  if fh_frameType h =? 1 then
    fsu_fParams (fsu_stage (fsu_expected fsB (vlong (le_field hb 4 4))) (Vint (Int.repr ds_skipFrame))) ha
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
      ha.

(* the context after piece C (dictionary fields: getDDict's, which may have freed the local DDict; the second
   selection finds what the first one did) *)
Definition lhC_k (k1: cst3) (hb: list Z) (h: frame_header) (c: lhc) : cst3 :=
  {| c3_fs := lhC_fs k1 hb h c;
     c3_tabs := TInit (dd_ox (lc_dd c)) (lh_dd_ts (lc_dd c) (lc_lxb c));
     c3_stable := c3_stable k1; c3_dict := snd (getddict_res (c3_dict k1));
     c3_s := held_redict (c3_s k1) (c3_dict k1) (snd (getddict_res (c3_dict k1)));
     c3_par := c3_par k1; c3_sp := c3_sp k1; c3_set := c3_set k1 |}.

(* the DDict getDDict returns (x at its pointer, content buf): the context's local one, or a caller's; its content
   is at a pointer, or it is the DDict without content (buf = NULL) *)
Definition lh_dd_ok (st: dctx_st) (k: cst3) (x: ddx) (buf: val) : Prop :=
  dx_q x = fst (getddict_res (c3_dict k)) /\ dx_q x <> nullval /\
  dd_src st (c3_with_dict k (snd (getddict_res (c3_dict k)))) x buf /\
  ld_rel (dx_bytes x) (dx_ld x) /\ (isptr buf \/ (buf = nullval /\ dx_ref x = Some nullval /\ dx_bytes x = nil)) /\
  (dx_raw x = true \/ dict_auto_c (dx_bytes x) (dx_ld x) <> None).

(* the DDict of piece C: none when getDDict returns NULL *)
Definition lhC_dd (a: dsa) (k1: cst3) (dd: option (ddx * val)) : Prop :=
  match dd with
  | None => fst (getddict_res (c3_dict k1)) = nullval
  | Some (x, buf) => lh_dd_ok (a_st a) k1 x buf
  end.

(* what passing piece C means *)
Definition lhC_facts (a: dsa) (w: lw) (k1: cst3) (h: frame_header) (c: lhc) : Prop :=
  lhC_dd a k1 (lc_dd c) /\
  (lc_cold c = Vint (Int.repr 0) \/ lc_cold c = Vint (Int.repr 1)) /\
  0 <= lc_did c <= Int.max_unsigned /\
  (c3_stable k1 = true -> fh_frameType h <> 1 -> fh_contentSize h <> ZSTD_CONTENTSIZE_UNKNOWN ->
     fh_contentSize h <= a_osz a - w_opc w) /\
  (fh_frameType h <> 1 -> fh_dictID h = 0 \/ fh_dictID h = lc_did c) /\
  (lc_dd c = None -> lc_did c = 0) /\
  Z.max (fh_windowSize h) ZSTD_WINDOWSIZE_ABSMIN <= dp_wmax (c3_par k1).

(* ---------- piece D ---------- *)

(* the effective Block_Maximum_Size (maxBlockSizeParam cap) *)
Definition lh_bsm (k: cst3) (h: frame_header) : Z := Z.min (fh_blockSizeMax h) (md_bmax (dmode_of (c3_par k))).

(* fParams.blockSizeMax := MIN(blockSizeMax, maxBlockSizeParam) when the parameter is set *)
Definition lhD_k (k3: cst3) (h: frame_header) (s3: sfields) : cst3 :=
  c3_with_s (c3_with_fs k3 (fsu_fParams (c3_fs k3) (fh_val (fh_adj h (lh_bsm k3 h)))) (c3_tabs k3)) s3.

(* the stream buffer after piece D (s: before, s3: after): streamStage = zdss_read, a buffer of at least
   MAX(bsm, 4) + (buffered: the ring of ZSTD_decodingBufferSize_internal) bytes *)
Definition lhD_facts (stable: bool) (s s3: sfields) (h: frame_header) (bsm: Z) : Prop :=
  sf_stage s3 = zdss_read /\ sf_inPos s3 = sf_inPos s /\ sf_outStart s3 = sf_outStart s /\
  sf_outEnd s3 = sf_outEnd s /\ sf_lhSize s3 = sf_lhSize s /\ sf_hbuf s3 = sf_hbuf s /\
  sf_hostage s3 = sf_hostage s /\ sf_nfp s3 = sf_nfp s /\ sf_expOut s3 = sf_expOut s /\
  sf_inBuff s3 <> nullval /\ isptr (sf_inBuff s3) /\ Z.max bsm 4 <= sf_inSize s3 /\
  sf_inSize s3 + sf_outSize s3 <= 2 ^ 32 /\
  (stable = false -> sf_outSize s3 >= ring_needed h bsm) /\
  sf_mem s3 = sf_mem s /\ sf_held s3 = sf_held s.

(* the stream fields after a failed allocation: inBuff = NULL, both sizes 0 (the allocator fields kept) *)
Definition lhD_memfail (s s': sfields) : Prop :=
  sf_inBuff s' = nullval /\ sf_inSize s' = 0 /\ sf_outSize s' = 0 /\
  sf_stage s' = sf_stage s /\ sf_inPos s' = sf_inPos s /\ sf_outStart s' = sf_outStart s /\
  sf_outEnd s' = sf_outEnd s /\ sf_lhSize s' = sf_lhSize s /\ sf_hbuf s' = sf_hbuf s /\
  sf_hostage s' = sf_hostage s /\ sf_nfp s' = sf_nfp s /\ sf_expOut s' = sf_expOut s /\
  sf_mem s' = sf_mem s /\ sf_held s' = sf_held s.

(* ---------- the returns of case 1 ----------
   lh_rc a w hb r ipos' w': case 1, entered with the witnesses w and the header bytes hb, returns r with
   input->pos = ipos' (output->pos unchanged) in the state w' *)
Definition ZSTD_error_dstSize_tooSmall : Z := 70.
Definition ZSTD_error_frameParameter_windowTooLarge : Z := 16.

Inductive lh_rc (a: dsa) (w: lw) (hb: list Z) : Z -> Z -> lw -> Prop :=
(* the header is invalid *)
| RC_hdr : forall r v tbl d1 did1,
    lhA_sel (w_k w) hb r v tbl d1 did1 -> get_frame_header_m (lh_mg (w_k w)) hb = FH_err -> fp_ok v ->
    lh_rc a w hb r (a_ipos a) (lw_k w (k_A (w_k w) v d1 did1))
(* the input ends inside the header: all of it copied (fParams := v' by the second call), input->pos =
   input->size; the bytes are invalid *)
| RC_more_err : forall kk v tbl d1 did1 r v',
    lhA_sel (w_k w) hb kk v tbl d1 did1 -> get_frame_header_m (lh_mg (w_k w)) hb = FH_more kk ->
    a_isz a - w_ipc w < kk - Zlength hb ->
    fh_post_m (lh_mg (w_k w)) (hb ++ sublist (w_ipc w) (a_isz a) (a_ibs a)) r v v' ->
    get_frame_header_m (lh_mg (w_k w)) (hb ++ sublist (w_ipc w) (a_isz a) (a_ibs a)) = FH_err ->
    0 <= r <= Int64.max_unsigned -> fp_ok v' ->
    lh_rc a w hb r (a_isz a)
      (lw_k w (lh_k_load a w (k_A (w_k w) v d1 did1) hb (a_isz a - w_ipc w) v'))
(* ... or still a possible header: the hint *)
| RC_hint : forall kk v tbl d1 did1 r' v',
    lhA_sel (w_k w) hb kk v tbl d1 did1 -> get_frame_header_m (lh_mg (w_k w)) hb = FH_more kk ->
    a_isz a - w_ipc w < kk - Zlength hb ->
    fh_post_m (lh_mg (w_k w)) (hb ++ sublist (w_ipc w) (a_isz a) (a_ibs a)) r' v v' ->
    get_frame_header_m (lh_mg (w_k w)) (hb ++ sublist (w_ipc w) (a_isz a) (a_ibs a)) <> FH_err ->
    fp_ok v' ->
    lh_rc a w hb (lh_hint (lh_mg (w_k w)) (hb ++ sublist (w_ipc w) (a_isz a) (a_ibs a)) kk) (a_isz a)
      (lw_k w (lh_k_load a w (k_A (w_k w) v d1 did1) hb (a_isz a - w_ipc w) v'))
(* the shortcut failed *)
| RC_short : forall h tbl d1 did1 cSize r out fs' d' lxb',
    lhA_sel (w_k w) hb 0 (fh_val h) tbl d1 did1 -> get_frame_header_m (lh_mg (w_k w)) hb = FH_ok h ->
    lhB_facts a w (k_A (w_k w) (fh_val h) d1 did1) hb h cSize r out -> dec_err r ->
    lhB_dict (k_A (w_k w) (fh_val h) d1 did1) d' -> fp_ok (fs_fParams fs') ->
    lh_rc a w hb r (a_ipos a)
      {| w_smw := w_smw w; w_k := lhB_k (k_A (w_k w) (fh_val h) d1 did1) fs' d' lxb'; w_sv := w_sv w;
         w_ipc := w_ipc w; w_opc := w_opc w; w_oc := sublist 0 (w_opc w) (w_oc w) ++ out; w_dl := w_dl w |}
(* stable output buffer smaller than the frame's content *)
| RC_small : forall h tbl d1 did1,
    lhA_sel (w_k w) hb 0 (fh_val h) tbl d1 did1 -> get_frame_header_m (lh_mg (w_k w)) hb = FH_ok h ->
    c3_stable (w_k w) = true -> fh_frameType h <> 1 ->
    fh_contentSize h <> ZSTD_CONTENTSIZE_UNKNOWN -> a_osz a - w_opc w < fh_contentSize h ->
    lh_rc a w hb (err_code ZSTD_error_dstSize_tooSmall) (a_ipos a) (lw_k w (k_A (w_k w) (fh_val h) d1 did1))
(* ZSTD_decodeFrameHeader failed (Dictionary_ID not the context's): the frame fields fs' after it *)
| RC_dict : forall h tbl d1 did1 dd cold fs' r lxb,
    lhA_sel (w_k w) hb 0 (fh_val h) tbl d1 did1 -> get_frame_header_m (lh_mg (w_k w)) hb = FH_ok h ->
    fh_frameType h <> 1 -> dec_err r -> lhC_dd a (k_A (w_k w) (fh_val h) d1 did1) dd ->
    fh_dictID h <> 0 -> fh_dictID h <> lh_dd_did dd ->
    (cold = Vint (Int.repr 0) \/ cold = Vint (Int.repr 1)) ->
    fs_dictEnd fs' = fs_dictEnd (lh_dd_fs (c3_fs (k_A (w_k w) (fh_val h) d1 did1)) (dp_fmt (c3_par (w_k w))) dd cold) ->
    fs_ddictIsCold fs' = fs_ddictIsCold (lh_dd_fs (c3_fs (k_A (w_k w) (fh_val h) d1 did1)) (dp_fmt (c3_par (w_k w))) dd cold) ->
    fp_ok (fs_fParams fs') ->
    lh_rc a w hb r (a_ipos a)
      (lw_k w {| c3_fs := fs'; c3_tabs := TInit (dd_ox dd) (lh_dd_ts dd lxb);
                 c3_stable := c3_stable (w_k w);
                 c3_dict := snd (getddict_res (c3_dict (k_A (w_k w) (fh_val h) d1 did1)));
                 c3_s := held_redict (c3_s (k_A (w_k w) (fh_val h) d1 did1)) (c3_dict (k_A (w_k w) (fh_val h) d1 did1))
                           (snd (getddict_res (c3_dict (k_A (w_k w) (fh_val h) d1 did1))));
                 c3_par := c3_par (w_k w); c3_sp := c3_sp (w_k w); c3_set := c3_set (w_k w) |})
(* the window is beyond maxWindowSize *)
| RC_window : forall h tbl d1 did1 c,
    lhA_sel (w_k w) hb 0 (fh_val h) tbl d1 did1 -> get_frame_header_m (lh_mg (w_k w)) hb = FH_ok h ->
    lhC_dd a (k_A (w_k w) (fh_val h) d1 did1) (lc_dd c) ->
    (lc_cold c = Vint (Int.repr 0) \/ lc_cold c = Vint (Int.repr 1)) ->
    Z.max (fh_windowSize h) ZSTD_WINDOWSIZE_ABSMIN > dp_wmax (c3_par (w_k w)) ->
    lh_rc a w hb (err_code ZSTD_error_frameParameter_windowTooLarge) (a_ipos a)
      (lw_k w (lhC_k (k_A (w_k w) (fh_val h) d1 did1) hb h c))
(* the stream buffer cannot be allocated *)
| RC_mem : forall h tbl d1 did1 c s',
    lhA_sel (w_k w) hb 0 (fh_val h) tbl d1 did1 -> get_frame_header_m (lh_mg (w_k w)) hb = FH_ok h ->
    lhC_facts a w (k_A (w_k w) (fh_val h) d1 did1) h c ->
    lhD_memfail (c3_s (lhC_k (k_A (w_k w) (fh_val h) d1 did1) hb h c)) s' ->
    lh_rc a w hb (err_code ZSTD_error_memory_allocation) (a_ipos a)
      (lw_k w (lhD_k (lhC_k (k_A (w_k w) (fh_val h) d1 did1) hb h c) h s')).

Section Posts.
Variable DENT : dent_pred.
Variable TABS : tabs_pred.

Definition lh_ret (a: dsa) (w: lw) (hb: list Z) : option val -> environ -> mpred :=
  fun vl =>
  EX r: Z, EX ipos': Z, EX w': lw,
  PROPx [vl = Some (Vlong (Int64.repr r)); 0 <= r <= Int64.max_unsigned; lh_rc a w hb r ipos' w']
  (LOCALx (ds_LI_L a w') (SEPx (ds_S_ip DENT TABS a w' ipos'))).

(* ---------- the posts of the pieces ---------- *)

Definition lhA_post (a: dsa) (w: lw) (hb: list Z) : ret_assert :=
  {| RA_normal := EX h: frame_header, EX tbl: list val, EX d1: dfields, EX did1: val,
       PROPx [get_frame_header_m (lh_mg (w_k w)) hb = FH_ok h; lhA_sel (w_k w) hb 0 (fh_val h) tbl d1 did1]
       (LOCALx (ds_LI_L a (lw_k w (k_A (w_k w) (fh_val h) d1 did1)))
       (SEPx (ds_LI_St DENT TABS a (lw_k w (k_A (w_k w) (fh_val h) d1 did1)) tbl)));
     RA_break := EX kk: Z, EX v: reptype t_fh, EX tbl: list val, EX d1: dfields, EX did1: val,
       PROPx [lhA_sel (w_k w) hb kk v tbl d1 did1; get_frame_header_m (lh_mg (w_k w)) hb = FH_more kk;
              kk - Zlength hb <= a_isz a - w_ipc w]
       (LOCALx (ds_LI_L a (lhA_brk a w (k_A (w_k w) v d1 did1) hb kk))
       (SEPx (ds_LI_S DENT TABS a (lhA_brk a w (k_A (w_k w) v d1 did1) hb kk))));
     RA_continue := FF;
     RA_return := lh_ret a w hb |}.

(* k1: the context after piece A *)
Definition lhB_post (a: dsa) (w: lw) (hb: list Z) (h: frame_header) (k1: cst3) (tbl: list val) : ret_assert :=
  {| RA_normal := lh_stt DENT TABS a (lw_k w k1) tbl;
     RA_break := EX cSize: Z, EX r: Z, EX out: list val, EX c: list Z, EX fs': fstate, EX d': dfields, EX lxb': list Z,
       PROPx [lhB_facts a w k1 hb h cSize r out; is_error_code r = false; bytes_ok c; Zlength c = r;
              sublist 0 r out = zbytes c; lhB_dict k1 d'; fp_ok (fs_fParams fs');
              lhB_sel_fp k1 tbl (sublist (a_ipos a) (a_ipos a + cSize) (a_ibs a)) fs' d';
              lhB_sw k1 tbl (sublist (a_ipos a) (a_ipos a + cSize) (a_ibs a)) d';
              (* the cells after the frame's content are the output space's (fix F7) *)
              sublist (w_opc w + r) (a_osz a) (sublist 0 (w_opc w) (w_oc w) ++ out) = sublist (w_opc w + r) (a_osz a) (w_oc w)]
       (LOCALx (ds_LI_L a (lhB_brk w k1 fs' d' lxb' (a_ipos a + cSize) r out c))
       (SEPx (ds_LI_S DENT TABS a (lhB_brk w k1 fs' d' lxb' (a_ipos a + cSize) r out c))));
     RA_continue := FF;
     RA_return := lh_ret a w hb |}.

Definition lhC_post (a: dsa) (w: lw) (hb: list Z) (h: frame_header) (k1: cst3) : ret_assert :=
  {| RA_normal := EX c: lhc,
       PROPx [lhC_facts a w k1 h c]
       (LOCALx (ds_LI_L a (lw_k w (lhC_k k1 hb h c))) (SEPx (ds_LI_S DENT TABS a (lw_k w (lhC_k k1 hb h c)))));
     RA_break := FF;
     RA_continue := FF;
     RA_return := lh_ret a w hb |}.

(* k3: the context after piece C *)
Definition lhD_post (a: dsa) (w: lw) (hb: list Z) (h: frame_header) (k3: cst3) : ret_assert :=
  {| RA_normal := EX s3: sfields,
       PROPx [lhD_facts (c3_stable k3) (c3_s k3) s3 h (lh_bsm k3 h)]
       (LOCALx (ds_LI_L a (lw_k w (lhD_k k3 h s3)))
       (SEPx (ds_LI_S DENT TABS a (lw_k w (lhD_k k3 h s3)))));
     RA_break := FF;
     RA_continue := FF;
     RA_return := lh_ret a w hb |}.

End Posts.

(* ---------- what the pieces assume of the representation (proved in LH3Lend.v) ---------- *)

(* ZSTD_DCtx_selectFrameDDict's resources besides the context: the IDs of the set's DDicts and the token of
   the current DDict, lent by dict_res / set_res *)
Definition lend_sel_ok : Prop :=
  forall (DENT: dent_pred) (gv: globals) (W: list ptr_witness) (st: dctx_st) (d: dfields),
    dict_rel3 st d -> set_cur_ok st -> stream_dict_ok W st -> NoDup (map fst (dc_set st)) ->
    (dc_dict st = None -> df_ddict d = nullval \/ df_ddict d = df_local d \/ In (df_ddict d) (map fst (dc_set st))) ->
    exists xq: option (val * val), cur_ok d (dc_set st) xq /\
      (dict_res (DD3x DENT) gv Ews (dc_dict st) * set_res (DD3x DENT) gv Ews (dc_set st) (dc_dict st) |--
         set_ids (dc_set st) * opt_token xq *
         (set_ids (dc_set st) * opt_token xq -*
          dict_res (DD3x DENT) gv Ews (dc_dict st) * set_res (DD3x DENT) gv Ews (dc_set st) (dc_dict st))).

(* ZSTD_decompressBegin_usingDDict's DDict (getDDict's, not NULL): from the local DDict, dict_res or set_res *)
Definition lend_begin_ok : Prop :=
  forall (DENT: dent_pred) (gv: globals) (p: val) (W: list ptr_witness) (st: dctx_st) (k: cst3),
    c3_set k = dc_set st -> dict_rel3 st (c3_dict k) -> set_cur_ok st -> stream_dict_ok W st ->
    fst (getddict_res (c3_dict k)) <> nullval ->
    dgroup DENT gv p (snd (getddict_res (c3_dict k))) * dict_res (DD3x DENT) gv Ews (dc_dict st) *
    set_res (DD3x DENT) gv Ews (dc_set st) (dc_dict st) |--
      EX x: ddx, EX buf: val, !! (lh_dd_ok st k x buf) &&
        (ddict_struct x buf * DENT gv (dx_q x) (ddx_ent x) * ddict_mem x buf *
         (ddict_struct x buf * DENT gv (dx_q x) (ddx_ent x) * ddict_mem x buf -*
          dgroup DENT gv p (snd (getddict_res (c3_dict k))) * dict_res (DD3x DENT) gv Ews (dc_dict st) *
          set_res (DD3x DENT) gv Ews (dc_set st) (dc_dict st))).

(* without a set, the context's DDict's bytes are its DDict's (Spec_api6 v3.1 DSDDict q dd; stream R2:
   FSRep3.dict_rel3_of gives it, and without a set dict_rel3 is dict_rel3_of: LH3Stmts.lh_dd_bytes) *)
Definition dd_bytes_ok (st: dctx_st) : Prop :=
  dc_set st = nil ->
  forall dr q dd, dc_dict st = Some dr -> dr_src dr = DSDDict q dd -> dr_bytes dr = dd_bytes dd.

(* ZSTD_decompress_usingDDict's dictionary argument without the selection: getDDict's DDict (or none), lent by the
   local DDict, dict_res or set_res; without a set its model is the context's dictionary (when the model loads it).
   FS3 R3: a by-reference DDict (0 bytes) at cap 0 needs only its valid pointer (darg_ok3's dict_ptr_ok0) *)
Definition lend_use_ok : Prop :=
  forall (DENT: dent_pred) (gv: globals) (p: val) (W: list ptr_witness) (st: dctx_st) (k: cst3)
         (shd: share) (cap: Z) (dst: val),
    c3_set k = dc_set st -> dict_rel3 st (c3_dict k) -> set_cur_ok st -> stream_dict_ok W st -> dd_bytes_ok st ->
    writable_share shd -> buf_ok W shd cap dst -> 0 <= cap ->
    dgroup DENT gv p (snd (getddict_res (c3_dict k))) * dict_res (DD3x DENT) gv Ews (dc_dict st) *
    set_res (DD3x DENT) gv Ews (dc_set st) (dc_dict st) |--
      EX ad: darg,
        !! (darg_is_ddict ad /\ darg_ddict ad = fst (getddict_res (c3_dict k)) /\ darg_ok3 W ad shd cap dst /\
            (dc_set st = nil -> forall dm, dictref_model (dc_dict st) = Some dm -> darg_model ad = Some dm)) &&
        (darg_res DENT gv ad *
         (darg_res DENT gv ad -*
          dgroup DENT gv p (snd (getddict_res (c3_dict k))) * dict_res (DD3x DENT) gv Ews (dc_dict st) *
          set_res (DD3x DENT) gv Ews (dc_set st) (dc_dict st))).

End CM_LH3Defs_1.
