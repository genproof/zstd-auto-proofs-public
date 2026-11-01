(* FS3, the buffer-less part.

   - bl_step_nc / bl_claim_nc: Params.bl_step / Spec_api6.bl_claim as zstd's ZSTD_decompressContinue does them:
     Block_Maximum_Size NOT capped by ZSTD_d_maxBlockSize (defect D3; equal with the default parameter);
   - bldict: the dictionary a buffer-less frame was begun with, as the context sees it (the array holding it, where
     its content starts, its ID, the DDict the tables point into, gpDictCopy and dictEnd after the Begin);
   - BRc md od osz0 ba fs ts hb: the concrete relation of a buffer-less frame (FSRep3.blrel = BR, below): the C
     invariant of the frame fields (bl_cinv: stage, expected, header bytes, frame header, block type, history
     pointers), and, when the model describes the frame (ba_st = Some b), the model's view (bl_mrel);
   - ZSTD_decompressContinue_ispec: the internal specification of ZSTD_decompressContinue for the buffer-less
     API, over the context's pieces (fcore3 with the DDict set off, the tables, headerBuffer, the dictionary's
     memory).  BL3's API specification follows from it by funspec_sub (gaps D2, D3, D7, D8, D9 isolated there). *)
Require Export Zstd.proof.dec.v3.FS.FSOblig3.
Local Open Scope logic.

Section CM_BLDefs_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* ---------- the body's view of a buffer-less frame ----------
   Spec_api6 v3.1 records the frame's buffer size in ba_out = (ob, osz, start, end).  The body's statements use the
   view without it (this blabs, bl_hist_ok and bl_start shadow Spec_api6's; the size is BRc's osz0); BRp converts
   (bl_loc, bl_osz) and BLSub relates the two. *)
Record blabs := { ba_dict : option dictref; ba_st : option blst; ba_expect : Z; ba_out : option (val * Z * Z) }.

Definition bl_hist_ok (ba: blabs) (ob: val) (opos: Z) (oc: list val) : Prop :=
  match ba_out ba with
  | Some (ob', fs, pe) =>
      ob' = ob /\ pe = opos /\ 0 <= fs <= opos /\
      match ba_st ba with
      | Some b => sublist fs opos oc = zbytes (bs_out b)
      | None => cells_bytes (sublist fs opos oc)
      end
  | None => match ba_st ba with Some b => bs_out b = nil | None => True end
  end.

Definition bl_start (ba: blabs) (opos: Z) : Z :=
  match ba_out ba with Some (_, fs, _) => fs | None => opos end.

Definition blabs_api : Type := Spec_api6.blabs.

Definition bl_loc (ba: Spec_api6.blabs) : blabs :=
  {| ba_dict := Spec_api6.ba_dict ba; ba_st := Spec_api6.ba_st ba; ba_expect := Spec_api6.ba_expect ba;
     ba_out := match Spec_api6.ba_out ba with Some (ob, _, f0, pe) => Some (ob, f0, pe) | None => None end |}.

(* the frame's buffer size, once a call has given it *)
Definition bl_osz (ba: Spec_api6.blabs) : option Z :=
  match Spec_api6.ba_out ba with Some (_, osz, _, _) => Some osz | None => None end.

(* ---------- the model step without the block-size cap (D3) ---------- *)

Definition bl_step_nc (md: dmode) (dm: dict_model) (b: blst) (c: list Z) : blres :=
  match bs_stage b with
  | BHdrRest =>
      match get_frame_header_m (md_magicless md) (bs_hbuf b ++ c) with
      | FH_ok h =>
          if andb (negb (fh_dictID h =? 0)) (negb (fh_dictID h =? dm_id dm)) then BLErr else
          BLOk {| bs_stage := BBlkHdr; bs_expect := ZSTD_blockHeaderSize; bs_hbuf := bs_hbuf b ++ c; bs_hdr := h;
                  bs_ds := bs_ds b; bs_out := bs_out b; bs_btype := 0; bs_rle := 0 |} nil
      | _ => BLErr
      end
  | _ => bl_step md dm b c
  end.

Definition bl_claim_nc (md: dmode) (ba ba': blabs) (c: list Z) (r opos osz: Z) (oc': list val) : Prop :=
  match ba_st ba, dictref_model (ba_dict ba) with
  | Some b, Some dm =>
      Zlength c = bs_expect b ->
      match bl_step_nc md dm b c with
      | BLOk b' out =>
          (is_error_code r = false ->
             r = Zlength out /\ sublist opos (opos + r) oc' = zbytes out /\ ba_st ba' = Some b') /\
          (is_error_code r = true -> osz - opos < Zlength out)
      | BLErr => is_error_code r = true
      | BLUnk => True
      end
  | _, _ => True
  end.

(* ---------- zstd's frame stages (ZSTD_dStage) ---------- *)

Definition bl_stz (s: blstage) : Z :=
  match s with
  | BHdrPrefix => 0 | BHdrRest => 1 | BBlkHdr => 2 | BBlk => 3 | BLastBlk => 4 | BCk => 5
  | BSkipHdr => 6 | BSkip => 7
  end.

(* ---------- the dictionary of a buffer-less frame ---------- *)

(* the array bd_eb of the bytes bd_b holding the dictionary (the caller's bytes, a DDict's copy, or the caller's
   bytes a DDict refers to); zstd's history is its part [bd_ds0, |bd_b|) (Begin_usingDict: the content after the
   entropy header; a DDict: all of it); bd_id the context's dictID; bd_ox the DDict the tables point into (None:
   the context's own tables); bd_g0 gpDictCopy and bd_de0 dictEnd after the Begin (a copied DDict: 1 and its end;
   Begin_usingDict: 0 and NULL).  The DDict without content (ZSTD_createDDict(NULL, 0)) is the dictionary at NULL
   of no bytes (bd_nil): its pointers are NULL, as for no dictionary, but the tables still point into the DDict *)
Record bldict := { bd_eb : val; bd_b : list Z; bd_ds0 : Z; bd_id : Z; bd_ox : option ddx; bd_g0 : Z; bd_de0 : val }.

(* a pointer into the dictionary's array (NULL for the array at NULL) *)
Definition bd_off (n: Z) (v: val) : val := match v with Vptr _ _ => offset_val n v | _ => v end.

Lemma bd_off_ptr (n: Z) (v: val) : isptr v -> bd_off n v = offset_val n v.
Proof. intros Hp. destruct v; try contradiction. reflexivity. Qed.

Lemma bd_off_null (n: Z) : bd_off n nullval = nullval.
Proof. reflexivity. Qed.

Definition bd_start (od: option bldict) : val :=
  match od with None => nullval | Some d => bd_off (bd_ds0 d) (bd_eb d) end.
Definition bd_end (od: option bldict) : val :=
  match od with None => nullval | Some d => bd_off (Zlength (bd_b d)) (bd_eb d) end.
Definition bd_clen (od: option bldict) : Z :=
  match od with None => 0 | Some d => Zlength (bd_b d) - bd_ds0 d end.
Definition bd_idz (od: option bldict) : Z := match od with None => 0 | Some d => bd_id d end.
Definition bd_oxo (od: option bldict) : option ddx := match od with None => None | Some d => bd_ox d end.
Definition bd_g0o (od: option bldict) : Z := match od with None => 0 | Some d => bd_g0 d end.
Definition bd_de0o (od: option bldict) : val := match od with None => nullval | Some d => bd_de0 d end.

(* the C dictionary content (the history in front of the frame) *)
Definition bd_content (od: option bldict) : list Z :=
  match od with None => nil | Some d => sublist (bd_ds0 d) (Zlength (bd_b d)) (bd_b d) end.

(* the DDict without content: no bytes at NULL, ID 0, gpDictCopy 0, dictEnd NULL *)
Definition bd_nil (d: bldict) : Prop :=
  bd_eb d = nullval /\ bd_b d = nil /\ bd_ds0 d = 0 /\ bd_id d = 0 /\ bd_g0 d = 0 /\ bd_de0 d = nullval.

Definition bd_wf (od: option bldict) : Prop :=
  match od with
  | None => True
  | Some d =>
     (0 <= bd_ds0 d <= Zlength (bd_b d) /\ Zlength (bd_b d) <= 2 ^ 63 - 1 /\ bytes_ok (bd_b d) /\ isptr (bd_eb d) /\
      0 <= bd_id d <= Int.max_unsigned /\
      (bd_g0 d = 0 \/ (bd_g0 d = 1 /\ 0 < Zlength (bd_b d))) /\
      (bd_de0 d = nullval \/ bd_de0 d = offset_val (Zlength (bd_b d)) (bd_eb d)) /\
      (bd_de0 d = nullval -> 0 < Zlength (bd_b d))) \/ bd_nil d
  end.

(* the memory of the dictionary's bytes (the share of the caller's bytes, or Ews for a DDict's copy; none at
   NULL) *)
Definition bd_res (sh: share) (od: option bldict) : mpred :=
  match od with
  | None => emp
  | Some d => bytes_at sh (bd_b d) (bd_eb d)
  end.

(* zstd compares dst with the dictionary's end (previousDstEnd after the Begin) unless gpDictCopy = 1 or the end is
   NULL (no content) *)
Definition bd_buf_ok (W: list ptr_witness) (sh: share) (od: option bldict) (shd: share) (cap: Z) (dst: val) : Prop :=
  match od with
  | None => True
  | Some d => bd_g0 d = 0 -> isptr (bd_eb d) -> dict_ptr_ok W sh (Zlength (bd_b d)) (bd_eb d) shd cap dst
  end.

(* the model's dictionary, when it loads it, is the context's: same ID, its content a suffix of zstd's history *)
Definition bd_model_ok (odr: option dictref) (od: option bldict) : Prop :=
  forall dm, dictref_model odr = Some dm ->
    dm_id dm = bd_idz od /\ exists pre, bd_content od = pre ++ dm_content dm.

(* ---------- the C view of a buffer-less frame ---------- *)

(* the stage; the header bytes zstd keeps in headerBuffer (BHdrRest: the prefix; BSkipHdr: the 5 bytes read);
   headerSize (BHdrRest); the frame header in fParams (BBlkHdr .. BCk); bType and rleSize (BBlk, BLastBlk) *)
Record blv := { bv_stage : blstage; bv_hdr : list Z; bv_hs : Z; bv_h : frame_header; bv_bt : Z; bv_rle : Z }.

(* what zstd needs of a header it decoded *)
Definition hdr_ok (h: frame_header) : Prop :=
  0 <= fh_blockSizeMax h <= ZSTD_BLOCKSIZE_MAX /\ (fh_checksumFlag h = 0 \/ fh_checksumFlag h = 1) /\
  0 <= fh_contentSize h <= Int64.max_unsigned /\ fh_frameType h = 0.

(* validateChecksum = checksumFlag && !forceIgnoreChecksum *)
Definition bl_val (ign: bool) (h: frame_header) : bool := andb (fh_checksumFlag h =? 1) (negb ign).

Definition hdr_fields (ign: bool) (v: blv) (fs: fstate) : Prop :=
  hdr_ok (bv_h v) /\ fs_fParams fs = fh_val (bv_h v) /\
  fs_validateChecksum fs = Vint (Int.repr (if bl_val ign (bv_h v) then 1 else 0)) /\
  (bl_val ign (bv_h v) = true -> exists l, fs_xxh fs = Some l).

(* the stage-specific fields; e = dctx->expected *)
Definition bl_cstage (md: dmode) (v: blv) (e: Z) (fs: fstate) (hb: list val) : Prop :=
  let mg := md_magicless md in
  match bv_stage v with
  | BHdrPrefix => e = 0 \/ e = starting_len mg
  | BHdrRest =>
      Zlength (bv_hdr v) = starting_len mg /\ bytes_ok (bv_hdr v) /\
      sublist 0 (starting_len mg) hb = zbytes (bv_hdr v) /\
      bv_hs v = header_size_m mg (bv_hdr v) /\ fs_headerSize fs = vlong (bv_hs v) /\
      e = bv_hs v - starting_len mg /\
      (mg = false -> is_skippable_magic (le_field (bv_hdr v) 0 4) = false)
  | BBlkHdr => hdr_fields (md_ignore md) v fs /\ e = ZSTD_blockHeaderSize
  | BBlk | BLastBlk =>
      hdr_fields (md_ignore md) v fs /\
      fs_bType fs = Vint (Int.repr (bv_bt v)) /\ 0 <= bv_bt v <= 2 /\
      fs_rleSize fs = vlong (bv_rle v) /\ 0 <= bv_rle v < 2 ^ 21 /\
      0 < e <= fh_blockSizeMax (bv_h v) /\ (bv_bt v = 1 -> e = 1)
  | BCk => hdr_fields (md_ignore md) v fs /\ fh_checksumFlag (bv_h v) = 1 /\ e = 4
  | BSkipHdr =>
      mg = false /\ Zlength (bv_hdr v) = ZSTD_FRAMEHEADERSIZE_PREFIX /\ bytes_ok (bv_hdr v) /\
      sublist 0 ZSTD_FRAMEHEADERSIZE_PREFIX hb = zbytes (bv_hdr v) /\
      e = ZSTD_SKIPPABLEHEADERSIZE - ZSTD_FRAMEHEADERSIZE_PREFIX
  | BSkip => True
  end.

(* the history pointers: as the Begin left them (no call with a capacity yet; the output, if begun, at the
   frame's capacity end osz0); stuck (a block of 0 bytes at capacity 0: previousDstEnd moved, nothing else);
   or moved by ZSTD_checkContinuity to the output ob, the frame's output [f0, pe) behind the dictionary *)
Definition bl_lay (od: option bldict) (osz0: Z) (ba: blabs) (fs: fstate) : Prop :=
  (fs_previousDstEnd fs = bd_end od /\ fs_prefixStart fs = bd_start od /\ fs_virtualStart fs = bd_start od /\
   fs_dictEnd fs = bd_de0o od /\ fs_gpDictCopy fs = Vint (Int.repr (bd_g0o od)) /\
   match ba_out ba with None => True | Some (_, f0, pe) => pe = f0 /\ f0 = osz0 end) \/
  (exists ob f0, ba_out ba = Some (ob, f0, f0) /\ f0 = osz0 /\
   fs_previousDstEnd fs = offset_val f0 ob /\ fs_prefixStart fs = bd_start od /\
   fs_virtualStart fs = bd_start od /\ fs_dictEnd fs = bd_de0o od /\ fs_gpDictCopy fs = Vint (Int.repr 0)) \/
  (exists ob f0 pe, ba_out ba = Some (ob, f0, pe) /\ isptr ob /\ 0 <= f0 <= pe /\ pe <= osz0 /\
   fs_previousDstEnd fs = offset_val pe ob /\ fs_prefixStart fs = offset_val f0 ob /\
   fs_virtualStart fs = offset_val (f0 - bd_clen od) ob /\ fs_dictEnd fs = bd_end od /\
   fs_gpDictCopy fs = Vint (Int.repr 0)).

(* the C invariant (also when the model does not describe the frame) *)
Definition bl_cinv (md: dmode) (od: option bldict) (osz0: Z) (ba: blabs) (fs: fstate) (hb: list val) (v: blv)
    : Prop :=
  fs_expected fs = vlong (ba_expect ba) /\ 0 <= ba_expect ba < 2 ^ 32 /\
  fs_stage fs = Vint (Int.repr (bl_stz (bv_stage v))) /\
  fs_isFrameDecompression fs = Vint (Int.repr 1) /\ cold01 fs /\
  fs_dictID fs = Vint (Int.repr (bd_idz od)) /\
  (exists pcs, fs_processedCSize fs = vlong pcs /\ 0 <= pcs <= Int64.max_unsigned) /\
  (exists ds, fs_decodedSize fs = vlong ds /\ 0 <= ds <= Int64.max_unsigned) /\
  Zlength hb = 18 /\ bd_wf od /\
  bl_cstage md v (ba_expect ba) fs hb /\ bl_lay od osz0 ba fs.

(* the model's view (ba_st = Some b): stage, expected, entropy state (the tables), content so far (decodedSize,
   the checksum state), header bytes, header, block type *)
Definition bl_mrel (md: dmode) (ba: blabs) (fs: fstate) (ts: tstate) (v: blv) : Prop :=
  forall b, ba_st ba = Some b ->
    bs_stage b = bv_stage v /\ bs_expect b = ba_expect ba /\ bs_ds b = ts_d ts /\
    fs_decodedSize fs = vlong (Zlength (bs_out b)) /\ bytes_ok (bs_out b) /\
    match bv_stage v with
    | BHdrPrefix => bs_expect b <> 0 -> bs_out b = nil
    | BHdrRest => bs_hbuf b = bv_hdr v /\ bs_out b = nil
    | BSkipHdr => bs_hbuf b = bv_hdr v
    | BBlkHdr | BCk =>
        bs_hdr b = bv_h v /\ (bl_val (md_ignore md) (bv_h v) = true -> fs_xxh fs = Some (bs_out b))
    | BBlk | BLastBlk =>
        bs_hdr b = bv_h v /\ bs_btype b = bv_bt v /\ bs_rle b = bv_rle v /\
        (bl_val (md_ignore md) (bv_h v) = true -> fs_xxh fs = Some (bs_out b))
    | _ => True
    end.

Definition BRc (md: dmode) (od: option bldict) (osz0: Z) (ba: blabs) (fs: fstate) (ts: tstate) (hb: list val)
    : Prop :=
  exists v: blv, bl_cinv md od osz0 ba fs hb v /\ bl_mrel md ba fs ts v /\ bd_model_ok (ba_dict ba) od.

(* the API's dictionary of the frame and the context's view of it: none; the caller's bytes by reference
   (Begin_usingDict); a DDict (its pinned buffer dd_buf, its entropy in the tables, gpDictCopy 1 for a copy) *)
Definition bd_rel (odr: option dictref) (od: option bldict) : Prop :=
  match odr, od with
  | None, None => True
  | Some dr, Some d =>
      bd_b d = dr_bytes dr /\
      match dr_src dr with
      | DSRef p => dr_raw dr = false /\ bd_eb d = p /\ bd_ox d = None
      | DSDDict q dd =>
          bd_eb d = dd_buf dd /\ dr_bytes dr = dd_bytes dd /\ bd_ox d = Some (dd_x q dd) /\
          bd_g0 d = (match dd_xref dd with Some _ => 0 | None => 1 end)
      | DSOwn => False
      end
  | _, _ => False
  end.

(* BR with the parameters pr the frame was begun under (D2: they must be the context's at every call); osz0 the
   frame's buffer size *)
Definition BRp (pr: dparams) : blabs_api -> fstate -> tabs3 -> list val -> Prop :=
  fun ba fs t hb =>
    par_ok pr /\ exists od osz0 ts, t = TInit (bd_oxo od) ts /\ (forall o, bl_osz ba = Some o -> o = osz0) /\
      bd_rel (Spec_api6.ba_dict ba) od /\ BRc (dmode_of pr) od osz0 (bl_loc ba) fs ts hb.

(* FS3's buffer-less relation (FSRep3.blrel, given the context's parameters) *)
Definition BR : blrel := BRp.

(* ---------- the internal specification of ZSTD_decompressContinue (buffer-less use) ---------- *)

Section ISpec.
Variable DENT : dent_pred.
Variable TABS : tabs_pred.

Definition ZSTD_decompressContinue_ispec : ident * funspec :=
  DECLARE _ZSTD_decompressContinue
  WITH W: list ptr_witness, gv: globals, p: val, pr: dparams, od: option bldict, osz0: Z, ba: blabs,
       fs: fstate, ts: tstate, hb: list val, shk: share,
       shd: share, ob: val, osz: Z, opos: Z, oc: list val, shs: share, src: val, c: list Z
  PRE [ tptr t_dctx, tptr tvoid, tulong, tptr tvoid, tulong ]
    PROP (BRc (dmode_of pr) od osz0 ba fs ts hb; fp_ok (fs_fParams fs); ba_expect ba <> 0; bl_hist_ok ba ob opos oc;
          ba_out ba <> None -> osz = osz0;
          buf_ok W shd osz ob; buf_ok W shs (Zlength c) src; bd_buf_ok W shk od shd (osz - opos) (offset_val opos ob);
          writable_share shd; readable_share shs; readable_share shk;
          0 <= opos <= osz; osz <= 2 ^ 63 - 1; Zlength oc = osz; Zlength c <= 2 ^ 30; bytes_ok c)
    PARAMS (p; offset_val opos ob; Vlong (Int64.repr (osz - opos)); src; Vlong (Int64.repr (Zlength c)))
    GLOBALS (gv)
    SEP (pws_pred W; zstd_globals gv; fcore3 p fs pr nullval; TABS gv p (bd_oxo od) ts;
         field_at Ews t_dctx (DOT _headerBuffer) hb p; dent_of DENT gv (bd_oxo od); bd_res shk od;
         data_at shd (tarray tuchar osz) oc ob; data_at shs (tarray tuchar (Zlength c)) (zbytes c) src)
  POST [ tulong ]
    EX r: Z, EX oc': list val, EX ba': blabs, EX fs': fstate, EX t': tabs3, EX hb': list val,
    PROP (0 <= r <= Int64.max_unsigned; Zlength oc' = osz; sublist 0 opos oc' = sublist 0 opos oc;
          cold01 fs'; Zlength hb' = 18; fp_ok (fs_fParams fs');
          (is_error_code r = false ->
             r <= osz - opos /\ cells_bytes (sublist opos (opos + r) oc') /\ ba_dict ba' = ba_dict ba /\
             ba_out ba' = Some (pair (pair ob (bl_start ba opos)) (opos + r)%Z) /\
             bl_hist_ok ba' ob (opos + r) oc' /\
             (forall b', ba_st ba' = Some b' -> ba_expect ba' = bs_expect b') /\
             exists ts', t' = TInit (bd_oxo od) ts' /\ BRc (dmode_of pr) od osz ba' fs' ts' hb');
          bl_claim_nc (dmode_of pr) ba ba' c r opos osz oc')
    RETURN (Vlong (Int64.repr r))
    SEP (pws_pred W; zstd_globals gv; fcore3 p fs' pr nullval; tabs_rep TABS gv p t';
         field_at Ews t_dctx (DOT _headerBuffer) hb' p; dent_of DENT gv (bd_oxo od); bd_res shk od;
         data_at shd (tarray tuchar osz) oc' ob; data_at shs (tarray tuchar (Zlength c)) (zbytes c) src).

End ISpec.

End CM_BLDefs_1.
