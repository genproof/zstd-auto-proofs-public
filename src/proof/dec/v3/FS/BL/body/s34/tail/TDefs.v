(* FS3-bl BODY, stages 3/4, the tail: shared definitions of the parts of s34_tail_ok (Tail.v).
   The parts prove the lemmas stated with these definitions.

   s34_t = t34_chk; t34_bsm; t34_dw; t34_dsz; t34_xx; t34_pe; t34_gp; t34_ex; t34_stg; t34_ret
   - t34_chk: FORWARD_IF_ERROR(rSize); t34_bsm: rSize > fParams.blockSizeMax -> return -20; t34_dw: DEBUGLOG;
   - t34_dsz: decodedSize += rSize; t34_xx: if (validateChecksum) XXH64_update(&xxhState, dst, rSize);
     t34_pe: previousDstEnd = dst + rSize; t34_gp: gpDictCopy = 0;
   - t34_ex: if (expected > 0) return rSize;
   - t34_stg: if (stage == 4) { content size check (return -20); checksumFlag ? (expected 4, stage 5) :
     (trace_end, expected 0, stage 0) } else { stage 2, expected 3 }; t34_ret: return rSize.
   - t34_st: the state between the parts (s34_mid's LOCAL/SEP with rSize r, frame fields fsx, output oc', tables t');
   - the frame fields: t34_fsm (s34_mid's), t34_fsB (after t34_gp), t34_fsE (the new expected and stage);
   - t34_pp: the PROP of bl_post (the ispec's POST) for r oc' ba' fs' t' hb';
   - t34_H: the hypotheses of s34_tail_spec; t34_cnt: s34_mid_ok's success witnesses. *)
Require Export Zstd.proof.dec.v3.FS.BL.body.s34.S34Defs.
Local Open Scope logic.

Section CM_TDefs_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* ---------- the statements ---------- *)

Definition t34_chk : statement :=
  ltac:(let s := eval cbv [s34_t] in s34_t in
        lazymatch s with Ssequence ?a _ => exact a end).
Definition t34_bsm : statement :=
  ltac:(let s := eval cbv [s34_t] in s34_t in
        lazymatch s with Ssequence _ (Ssequence ?a _) => exact a end).
Definition t34_dw : statement :=
  ltac:(let s := eval cbv [s34_t] in s34_t in
        lazymatch s with Ssequence _ (Ssequence _ (Ssequence ?a _)) => exact a end).
Definition t34_dsz : statement :=
  ltac:(let s := eval cbv [s34_t] in s34_t in
        lazymatch s with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence ?a _))) => exact a end).
Definition t34_xx : statement :=
  ltac:(let s := eval cbv [s34_t] in s34_t in
        lazymatch s with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence ?a _)))) => exact a end).
Definition t34_pe : statement :=
  ltac:(let s := eval cbv [s34_t] in s34_t in
        lazymatch s with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence ?a _))))) =>
          exact a end).
Definition t34_gp : statement :=
  ltac:(let s := eval cbv [s34_t] in s34_t in
        lazymatch s with
        | Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence ?a _)))))) =>
          exact a end).
Definition t34_ex : statement :=
  ltac:(let s := eval cbv [s34_t] in s34_t in
        lazymatch s with
        | Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _
            (Ssequence ?a _))))))) => exact a end).
Definition t34_stg : statement :=
  ltac:(let s := eval cbv [s34_t] in s34_t in
        lazymatch s with
        | Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _
            (Ssequence _ (Ssequence ?a _)))))))) => exact a end).
Definition t34_ret : statement :=
  ltac:(let s := eval cbv [s34_t] in s34_t in
        lazymatch s with
        | Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _
            (Ssequence _ (Ssequence _ ?a)))))))) => exact a end).

Lemma t34_t_eq :
  s34_t = Ssequence t34_chk (Ssequence t34_bsm (Ssequence t34_dw (Ssequence t34_dsz (Ssequence t34_xx
            (Ssequence t34_pe (Ssequence t34_gp (Ssequence t34_ex (Ssequence t34_stg t34_ret)))))))).
Proof. reflexivity. Qed.

(* ---------- the frame fields ---------- *)

(* s34_mid's frame fields *)
Definition t34_fsm (fs: fstate) (ob: val) (osz opos pcs: Z) (c: list Z) (e': Z) (cold: val) : fstate :=
  fsu_ddictIsCold (fsu_expected (bl_fs1 fs ob osz opos pcs (Zlength c)) (vlong e')) cold.

(* validateChecksum *)
Definition t34_vc (pr: dparams) (v: blv) : bool := bl_val (md_ignore (dmode_of pr)) (bv_h v).

(* the checksum state after `if (validateChecksum) XXH64_update(.., cnt)` *)
Definition t34_xxh (vc: bool) (x: option (list Z)) (cnt: list Z) : option (list Z) :=
  if vc then option_map (fun l => l ++ cnt) x else x.

(* after t34_gp: decodedSize ds + r, the checksum state x, previousDstEnd dst + r, gpDictCopy 0 *)
Definition t34_fsB (fsx: fstate) (ds r: Z) (x: option (list Z)) (ob: val) (opos: Z) : fstate :=
  fsu_gpDictCopy (fsu_previousDstEnd (fsu_xxh (fsu_decodedSize fsx (vlong (ds + r))) x) (offset_val (opos + r) ob))
    (Vint (Int.repr 0)).

(* the new expected and stage *)
Definition t34_fsE (fsx: fstate) (stg: blstage) (e: Z) : fstate :=
  fsu_stage (fsu_expected fsx (vlong e)) (Vint (Int.repr (bl_stz stg))).

(* the stage and expected a successful call leaves (e' = expected after the block case) *)
Definition t34_next (v: blv) (e': Z) : blstage * Z :=
  if 0 <? e' then (bv_stage v, e')
  else match bv_stage v with
       | BLastBlk => if fh_checksumFlag (bv_h v) =? 1 then (BCk, 4) else (BHdrPrefix, 0)
       | _ => (BBlkHdr, ZSTD_blockHeaderSize)
       end.

(* the content size check at the last block passes (C: fcs != -1 && decodedSize != fcs, decodedSize = ds + r) *)
Definition t34_fcs_ok (v: blv) (ds r: Z) : Prop :=
  fh_contentSize (bv_h v) = ZSTD_CONTENTSIZE_UNKNOWN \/ (ds + r) mod 2 ^ 64 = fh_contentSize (bv_h v).

Lemma t34_fsm_fields fs ob osz opos pcs c e' cold :
  let f := t34_fsm fs ob osz opos pcs c e' cold in
  fs_validateChecksum f = fs_validateChecksum fs /\ fs_xxh f = fs_xxh fs /\ fs_decodedSize f = fs_decodedSize fs /\
  fs_processedCSize f = vlong (pcs + Zlength c) /\ fs_isFrameDecompression f = fs_isFrameDecompression fs /\
  fs_dictID f = fs_dictID fs /\ fs_ddictIsCold f = cold /\ fs_fParams f = fs_fParams fs /\
  fs_expected f = vlong e' /\ fs_stage f = fs_stage fs /\ fs_bType f = fs_bType fs /\
  fs_rleSize f = fs_rleSize fs /\ fs_headerSize f = fs_headerSize fs.
Proof.
  unfold t34_fsm, bl_fs1, continuity. destruct (cont_moves _ _ _); cbn; repeat split.
Qed.

Lemma t34_fsE_same fsx stg e :
  fs_expected fsx = vlong e -> fs_stage fsx = Vint (Int.repr (bl_stz stg)) -> t34_fsE fsx stg e = fsx.
Proof. destruct fsx; unfold t34_fsE, fsu_stage, fsu_expected; cbn; intros -> ->; reflexivity. Qed.

(* ---------- the post and the hypotheses ---------- *)

(* the PROP of bl_post *)
Definition t34_pp (md: dmode) (od: option bldict) (ba: blabs) (ob: val) (osz opos: Z) (oc: list val) (c: list Z)
    (r: Z) (oc': list val) (ba': blabs) (fs': fstate) (t': tabs3) (hb': list val) : Prop :=
  0 <= r <= Int64.max_unsigned /\ Zlength oc' = osz /\ sublist 0 opos oc' = sublist 0 opos oc /\
  cold01 fs' /\ Zlength hb' = 18 /\ fp_ok (fs_fParams fs') /\
  (is_error_code r = false ->
     r <= osz - opos /\ cells_bytes (sublist opos (opos + r) oc') /\ ba_dict ba' = ba_dict ba /\
     ba_out ba' = Some (pair (pair ob (bl_start ba opos)) (opos + r)%Z) /\
     bl_hist_ok ba' ob (opos + r) oc' /\
     (forall b', ba_st ba' = Some b' -> ba_expect ba' = bs_expect b') /\
     exists ts', t' = TInit (bd_oxo od) ts' /\ BRc md od osz ba' fs' ts' hb') /\
  bl_claim_nc md ba ba' c r opos osz oc'.

(* the hypotheses of s34_tail_spec *)
Definition t34_H (W: list ptr_witness) (pr: dparams) (od: option bldict) (osz0: Z) (ba: blabs) (fs: fstate)
    (ts: tstate) (hb: list val) (shk shd: share) (ob: val) (osz opos: Z) (oc: list val) (shs: share) (src: val)
    (c: list Z) (v: blv) (pcs: Z) : Prop :=
  par_ok pr /\ bl_pre_ok W od osz0 ba shk shd ob osz opos oc shs src c /\
  bl_cinv (dmode_of pr) od osz0 ba fs hb v /\ bl_mrel (dmode_of pr) ba fs ts v /\ bd_model_ok (ba_dict ba) od /\
  fp_ok (fs_fParams fs) /\ (bv_stage v = BBlk \/ bv_stage v = BLastBlk) /\
  fs_processedCSize fs = vlong pcs /\ 0 <= pcs <= Int64.max_unsigned /\
  bl_size_ok v (ba_expect ba) (Zlength c) /\
  bl_lay od osz (bl_moved ba ob opos) (continuity fs (offset_val opos ob) (osz - opos)).

(* s34_mid_ok's success witnesses: the content cnt written at [opos, opos + r), the entropy state ts' *)
Definition t34_cnt (od: option bldict) (ba: blabs) (c: list Z) (opos: Z) (oc': list val) (r: Z) (t': tabs3)
    (cnt: list Z) (ts': tstate) : Prop :=
  sublist opos (opos + r) oc' = zbytes cnt /\ bytes_ok cnt /\ Zlength cnt = r /\
  t' = TInit (bd_oxo od) ts' /\
  (forall b dm x, s34_fol ba c b dm -> blk_model dm b c = Some x -> x = (ts_d ts', cnt)).

(* ---------- the state between the parts ---------- *)

Section St.
Variable DENT : dent_pred.
Variable TABS : tabs_pred.

Definition t34_st (W: list ptr_witness) (gv: globals) (p: val) (pr: dparams) (od: option bldict) (hb: list val)
    (shk shd: share) (ob: val) (osz opos: Z) (shs: share) (src: val) (c: list Z) (v_bp: val)
    (r: Z) (fsx: fstate) (oc': list val) (t': tabs3) : environ -> mpred :=
  PROP ()
  LOCAL (temp _rSize (Vlong (Int64.repr r)); lvar _bp (Tstruct ___gp_blockProperties_t noattr) v_bp; gvars gv;
         temp _dctx p; temp _dst (offset_val opos ob); temp _dstCapacity (Vlong (Int64.repr (osz - opos)));
         temp _src src; temp _srcSize (Vlong (Int64.repr (Zlength c))))
  SEP (data_at_ Tsh (Tstruct ___gp_blockProperties_t noattr) v_bp;
       pws_pred W; zstd_globals gv; fcore3 p fsx pr nullval; tabs_rep TABS gv p t';
       field_at Ews t_dctx (DOT _headerBuffer) hb p; dent_of DENT gv (bd_oxo od); bd_res shk od;
       data_at shd (tarray tuchar osz) oc' ob; data_at shs (tarray tuchar (Zlength c)) (zbytes c) src).

(* the post of every part: returns as the ispec says, normal exit Q *)
Definition t34_R (W: list ptr_witness) (gv: globals) (p: val) (pr: dparams) (od: option bldict) (ba: blabs)
    (shk shd: share) (ob: val) (osz opos: Z) (oc: list val) (shs: share) (src: val) (c: list Z)
    (Q: environ -> mpred) : ret_assert :=
  overridePost Q (switch_ret_assert (bl_R DENT TABS W gv p pr od ba shk shd ob osz opos oc shs src c)).

End St.

End CM_TDefs_1.
