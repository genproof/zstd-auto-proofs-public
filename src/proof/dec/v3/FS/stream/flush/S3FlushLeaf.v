(* FS3 streaming, case zdss_flush: the loop invariant after a complete flush (port of v2 StreamSeg_flush.v
   flush_leaf_cpl), with the exact claim (S3Main.ex_call) from S3FlushX.flush_x_cpl. *)
Require Import Zstd.proof.dec.v3.FS.stream.S3RetStmts Zstd.proof.dec.v3.FS.stream.flush.S3FlushLem.
Require Import Zstd.proof.dec.v3.FS.stream.S3XKit Zstd.proof.dec.v3.FS.stream.flush.S3FlushX.
Local Open Scope logic.

(* loop_extra after the flush: streamStage is read or flush *)
Ltac close_lx :=
  unfold loop_extra; cbn [w_smw w_k c3_s c3_with_s sf_after sf_stage];
  intros _ Hx; unfold zdss_read, zdss_flush, zdss_loadHeader in Hx; lia.

(* exit_ok when the loop goes on *)
Ltac close_ex := unfold exit_ok; cbn [w_smw]; intros Hx; lia.

(* entry_ok: the flush never ends at zdss_init *)
Ltac close_en :=
  unfold entry_ok; cbn [w_smw w_k w_ipc c3_s c3_with_s sf_after sf_stage]; intros Hx Hy;
  unfold zdss_read, zdss_flush, zdss_init in *; lia.

Section CM_S3FlushLeaf_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* the output cells after a copy of m cells at od are those before it: in buffered mode the flush keeps the
   caller's cells after the position it reaches (untouched_ok) *)
Lemma sublist_after_copy : forall (oc oc0 cs: list val) (od os m n: Z),
  Zlength oc = n -> Zlength oc0 = n -> 0 <= od -> 0 <= m -> od + m <= n -> 0 <= os -> os + m <= Zlength cs ->
  sublist od n oc = sublist od n oc0 ->
  sublist (od + m) n (copy_cells oc od cs os m) = sublist (od + m) n oc0.
Proof.
intros oc oc0 cs od os m n Hl Hl0 Hod Hm Hn Hos Hcs H.
unfold copy_cells. rewrite Hl.
assert (E1: sublist (od + m) n (sublist 0 od oc ++ sublist os (os + m) cs ++ sublist (od + m) n oc) =
            sublist (od + m) n oc) by list_solve.
rewrite E1.
assert (E2: sublist (od + m) n oc = sublist m (n - od) (sublist od n oc)) by list_solve.
assert (E3: sublist (od + m) n oc0 = sublist m (n - od) (sublist od n oc0)) by list_solve.
rewrite E2, E3, H. reflexivity.
Qed.

End CM_S3FlushLeaf_1.

(* untouched_ok after the flush's copy (the bytes of the ring's output part at [ostart, ostart + m)) *)
Ltac close_un :=
  unfold untouched_ok; cbn [w_opc w_oc]; intros ?Hs;
  match goal with Hu: untouched_ok ?a ?w, Ha: dsa_ok ?a, Hi: call_inv ?a (w_k ?w) _ _ _ _ _ |- _ =>
    let H1 := fresh in let H2 := fresh in let H3 := fresh in
    pose proof Ha as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H1 & _ & H2 & _);
    pose proof Hi as (_ & H3 & _);
    apply sublist_after_copy;
    first [ apply Hu; assumption | assumption | lia
          | (unfold ring_out; rewrite Zlength_sublist by lia; lia) ]
  end.

Section CM_S3FlushLeaf_2.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.

(* a leaf where the flush completed (wr: the ring restarts), as one lemma: the loop invariant at the break; the
   exact claim of the loop state before the flush and the pending bytes as the ring's give it for the state after *)
Lemma flush_leaf_cpl : forall (Espec: OracleKind) (DENT: dent_pred) (TABS: tabs_pred) (a: dsa) (w: lw)
    (Delta: tycontext) (L: list localdef) (h: frame_header) (b ostart oend: Z) (wr: bool),
  dsa_ok a -> call_inv a (w_k w) (w_sv w) (w_ipc w) (w_opc w) (w_oc w) (w_dl w) -> untouched_ok a w ->
  w_smw w = 1 -> sf_stage (c3_s (w_k w)) = zdss_flush -> dc_stable (a_st a) = false ->
  sf_inBuff (c3_s (w_k w)) <> nullval ->
  (sf_inBuff (c3_s (w_k w)) <> nullval ->
   sf_outBuff (c3_s (w_k w)) = offset_val (sf_inSize (c3_s (w_k w))) (sf_inBuff (c3_s (w_k w)))) ->
  fs_fParams (c3_fs (w_k w)) = fh_val (fh_adj h b) ->
  sf_outStart (c3_s (w_k w)) = vlong ostart -> sf_outEnd (c3_s (w_k w)) = vlong oend ->
  0 <= ostart <= oend -> oend <= sf_outSize (c3_s (w_k w)) ->
  0 <= sf_inSize (c3_s (w_k w)) -> 0 <= sf_outSize (c3_s (w_k w)) ->
  sf_inSize (c3_s (w_k w)) + sf_outSize (c3_s (w_k w)) <= 2 ^ 32 ->
  Zlength (sf_ring (c3_s (w_k w))) = sf_inSize (c3_s (w_k w)) + sf_outSize (c3_s (w_k w)) ->
  Zlength (w_oc w) = a_osz a -> oend - ostart <= a_osz a - w_opc w ->
  cold01 (c3_fs (w_k w)) -> par_ok (c3_par (w_k w)) ->
  Int.min_signed <= sf_nfp (c3_s (w_k w)) <= Int.max_signed ->
  0 <= sf_over (c3_s (w_k w)) <= Int64.max_unsigned -> Zlength (sf_hbuf (c3_s (w_k w))) = 18 ->
  byte_cells (sf_ring (c3_s (w_k w))) -> 0 <= sf_held (c3_s (w_k w)) ->
  (sf_inBuff (c3_s (w_k w)) <> nullval -> 0 < sf_inSize (c3_s (w_k w)) + sf_outSize (c3_s (w_k w))) ->
  (wr = true -> Int64.ltu (Int64.repr (sf_outSize (c3_s (w_k w)))) (Int64.repr (fh_contentSize h)) = true /\
     Int64.unsigned (Int64.repr (sf_outSize (c3_s (w_k w)))) <
     Int64.unsigned (Int64.repr (oend + Int.unsigned (Int.repr b)))) ->
  (wr = false -> Int64.ltu (Int64.repr (sf_outSize (c3_s (w_k w)))) (Int64.repr (fh_contentSize h)) = false \/
     Int64.unsigned (Int64.repr (oend + Int.unsigned (Int.repr b))) <=
     Int64.unsigned (Int64.repr (sf_outSize (c3_s (w_k w))))) ->
  (forall d, In d (ds_LI_L a w) -> In d L) ->
  ex_call a w -> sublist ostart oend (ring_out (c3_s (w_k w))) = zbytes (sv_pend (w_sv w)) ->
  ENTAIL Delta, PROPx [] (LOCALx L (SEPx
   [data_at Ews (tarray tuchar (sf_inSize (c3_s (w_k w)) + sf_outSize (c3_s (w_k w))))
      (sf_ring (c3_s (w_k w))) (sf_inBuff (c3_s (w_k w)));
    data_at (a_shob a) (tarray tuchar (Zlength (w_oc w)))
      (copy_cells (w_oc w) (w_opc w) (ring_out (c3_s (w_k w))) ostart (oend - ostart)) (a_ob a);
    data_at Tsh (tptr tschar) (offset_val (w_opc w + (oend - ostart)) (a_ob a)) (a_vop a);
    pws_pred (a_W a); mem_mgr (a_gv a); zstd_globals (a_gv a);
    dctx_token (a_d a); dctx_pad (a_d a);
    cfg_fmt (a_d a) (dp_fmt (c3_par (w_k w))); cfg_lit (a_d a);
    field_at Ews t_dctx (DOT _previousDstEnd) (fs_previousDstEnd (c3_fs (w_k w))) (a_d a);
    field_at Ews t_dctx (DOT _gpDictCopy) (fs_gpDictCopy (c3_fs (w_k w))) (a_d a);
    field_at Ews t_dctx (DOT _prefixStart) (fs_prefixStart (c3_fs (w_k w))) (a_d a);
    field_at Ews t_dctx (DOT _virtualStart) (fs_virtualStart (c3_fs (w_k w))) (a_d a);
    field_at Ews t_dctx (DOT _dictEnd) (fs_dictEnd (c3_fs (w_k w))) (a_d a);
    field_at Ews t_dctx (DOT _expected) (fs_expected (c3_fs (w_k w))) (a_d a);
    field_at Ews t_dctx (DOT _fParams) (fh_val (fh_adj h b)) (a_d a);
    field_at Ews t_dctx (DOT _processedCSize) (fs_processedCSize (c3_fs (w_k w))) (a_d a);
    field_at Ews t_dctx (DOT _decodedSize) (fs_decodedSize (c3_fs (w_k w))) (a_d a);
    field_at Ews t_dctx (DOT _bType) (fs_bType (c3_fs (w_k w))) (a_d a);
    field_at Ews t_dctx (DOT _stage) (fs_stage (c3_fs (w_k w))) (a_d a);
    xxh_field (a_d a) (fs_xxh (c3_fs (w_k w)));
    field_at Ews t_dctx (DOT _headerSize) (fs_headerSize (c3_fs (w_k w))) (a_d a);
    field_at Ews t_dctx (DOT _validateChecksum) (fs_validateChecksum (c3_fs (w_k w))) (a_d a);
    field_at Ews t_dctx (DOT _rleSize) (fs_rleSize (c3_fs (w_k w))) (a_d a);
    field_at Ews t_dctx (DOT _isFrameDecompression) (fs_isFrameDecompression (c3_fs (w_k w))) (a_d a);
    field_at Ews t_dctx (DOT _dictID) (fs_dictID (c3_fs (w_k w))) (a_d a);
    field_at Ews t_dctx (DOT _ddictIsCold) (fs_ddictIsCold (c3_fs (w_k w))) (a_d a);
    tabs_rep TABS (a_gv a) (a_d a) (c3_tabs (w_k w));
    field_at Ews t_dctx (DOT _forceIgnoreChecksum) (Vint (Int.repr (dp_ignore (c3_par (w_k w))))) (a_d a);
    field_at Ews t_dctx (DOT _maxBlockSizeParam) (Vint (Int.repr (dp_bmax (c3_par (w_k w))))) (a_d a);
    field_at Ews t_dctx (DOT _refMultipleDDicts) (Vint (Int.repr (dp_multi (c3_par (w_k w))))) (a_d a);
    field_at Ews t_dctx (DOT _ddictSet) (c3_sp (w_k w)) (a_d a);
    cgroup3 (a_d a) (c3_stable (w_k w)) (dp_wmax (c3_par (w_k w)));
    dgroup DENT (a_gv a) (a_d a) (c3_dict (w_k w));
    field_at Ews t_dctx (DOT _streamStage) (Vint (Int.repr 2)) (a_d a);
    field_at Ews t_dctx (DOT _inBuff) (sf_inBuff (c3_s (w_k w))) (a_d a);
    field_at Ews t_dctx (DOT _inBuffSize) (Vlong (Int64.repr (sf_inSize (c3_s (w_k w))))) (a_d a);
    field_at Ews t_dctx (DOT _inPos) (sf_inPos (c3_s (w_k w))) (a_d a);
    field_at Ews t_dctx (DOT _outBuff) (offset_val (sf_inSize (c3_s (w_k w))) (sf_inBuff (c3_s (w_k w)))) (a_d a);
    field_at Ews t_dctx (DOT _outBuffSize) (Vlong (Int64.repr (sf_outSize (c3_s (w_k w))))) (a_d a);
    field_at Ews t_dctx (DOT _outStart) (Vlong (Int64.repr (if wr then 0 else oend))) (a_d a);
    field_at Ews t_dctx (DOT _outEnd) (Vlong (Int64.repr (if wr then 0 else oend))) (a_d a);
    field_at Ews t_dctx (DOT _lhSize) (sf_lhSize (c3_s (w_k w))) (a_d a);
    field_at Ews t_dctx (DOT _hostageByte) (sf_hostage (c3_s (w_k w))) (a_d a);
    field_at Ews t_dctx (DOT _noForwardProgress) (Vint (Int.repr (sf_nfp (c3_s (w_k w))))) (a_d a);
    field_at Ews t_dctx (DOT _expectedOutBuffer) (sf_expOut (c3_s (w_k w))) (a_d a);
    field_at Ews t_dctx (DOT _headerBuffer) (sf_hbuf (c3_s (w_k w))) (a_d a);
    field_at Ews t_dctx (DOT _oversizedDuration) (Vlong (Int64.repr (sf_over (c3_s (w_k w))))) (a_d a);
    blk_tok (sf_mem (c3_s (w_k w))) (tarray tuchar (sf_inSize (c3_s (w_k w)) + sf_outSize (c3_s (w_k w))))
      (sf_inBuff (c3_s (w_k w)));
    mgroup (sf_mem (c3_s (w_k w))) (a_d a) (sf_given (c3_s (w_k w)));
    hset_rep (sf_mem (c3_s (w_k w))) (c3_sp (w_k w)) (c3_set (w_k w)) (sf_held (c3_s (w_k w)) - local_held (c3_dict (w_k w)));
    dict_res (DD3x DENT) (a_gv a) Ews (dc_dict (a_st a));
    set_res (DD3x DENT) (a_gv a) Ews (dc_set (a_st a)) (dc_dict (a_st a));
    data_at (a_sho a) t_outBuffer (a_obf a, (Vlong (Int64.repr (a_osz a)), Vlong (Int64.repr (a_opos a))))
      (a_outp a);
    data_at (a_shi a) t_inBuffer (a_ibf a, (Vlong (Int64.repr (a_isz a)), Vlong (Int64.repr (a_ipos a))))
      (a_inp a);
    data_at (a_shb a) (tarray tuchar (a_isz a)) (zbytes (a_ibs a)) (a_ib a)]))
  |-- ds_inv_x DENT TABS a.
Proof.
intros Espec DENT TABS a w Delta L h b ostart oend wr Ha Hinv Hun Hsmw Hst Hs1 Hnn H6 Hfh Hos Hoe Ho Hoe2 H H0 H1 H7
  Hloc' Hcap Hcold Hpar Hnfpr Hover Hhb Hbyc Hheld Hpos Hwr Hnwr HL Hxw Hpend.
assert (Hpmax: sf_inSize (c3_s (w_k w)) + sf_outSize (c3_s (w_k w)) <= Ptrofs.max_unsigned) by rep_lia.
rewrite <- add64_repr in Hwr, Hnwr.
assert (Hci: call_inv a (c3_with_s (w_k w) (sf_after (c3_s (w_k w)) zdss_read
                (if wr then 0 else oend) (if wr then 0 else oend)))
    (sv_flushed (w_sv w) (oend - ostart)) (w_ipc w) (w_opc w + (oend - ostart))
    (copy_cells (w_oc w) (w_opc w) (ring_out (c3_s (w_k w))) ostart (oend - ostart))
    (w_dl w ++ sublist 0 (oend - ostart) (sv_pend (w_sv w))))
  by (eapply (flush_post_cpl _ _ _ _ _ _ _ h b _ _ wr); auto; lia).
assert (Hxc: ex_call a
         {| w_smw := w_smw w;
            w_k := c3_with_s (w_k w) (sf_after (c3_s (w_k w)) zdss_read
                     (if wr then 0 else oend) (if wr then 0 else oend));
            w_sv := sv_flushed (w_sv w) (oend - ostart); w_ipc := w_ipc w; w_opc := w_opc w + (oend - ostart);
            w_oc := copy_cells (w_oc w) (w_opc w) (ring_out (c3_s (w_k w))) ostart (oend - ostart);
            w_dl := w_dl w ++ sublist 0 (oend - ostart) (sv_pend (w_sv w)) |}).
{ pose proof Ha as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hip0 & _ & Hil & Hib & _).
  pose proof Hinv as (Hip & _ & _ & _ & Hdl & _).
  pose proof Hci as (_ & _ & _ & _ & _ & _ & Hbdl' & _).
  rewrite add64_repr in Hwr, Hnwr.
  eapply (flush_x_cpl a w _ (sv_pend (w_sv w)) ostart oend h b wr); try eassumption; try reflexivity; try lia. }
eapply derives_trans; [apply andp_left2; apply LOCALx_shuffle_derives; exact HL |].
unfold ds_inv_x.
Exists {| w_smw := w_smw w;
          w_k := c3_with_s (w_k w) (sf_after (c3_s (w_k w)) zdss_read
                   (if wr then 0 else oend) (if wr then 0 else oend));
          w_sv := sv_flushed (w_sv w) (oend - ostart); w_ipc := w_ipc w; w_opc := w_opc w + (oend - ostart);
          w_oc := copy_cells (w_oc w) (w_opc w) (ring_out (c3_s (w_k w))) ostart (oend - ostart);
          w_dl := w_dl w ++ sublist 0 (oend - ostart) (sv_pend (w_sv w)) |}.
unfold ds_LI_Px, ds_LI_L, ds_LI_S, ctx_rep3, ctx_body3, fgroup3, frame_fields, sgroup, ring_rep.
cbn [w_smw w_k w_sv w_ipc w_opc w_oc w_dl c3_with_s c3_fs c3_tabs c3_stable c3_dict c3_s c3_par c3_sp c3_set
     sf_after sf_stage sf_inBuff sf_inSize sf_inPos sf_outBuff sf_outSize sf_outStart sf_outEnd sf_lhSize sf_hostage
     sf_nfp sf_expOut sf_hbuf sf_over sf_ring sf_mem sf_held].
rewrite if_false by assumption.
rewrite Hfh, (H6 Hnn), Hloc'.
go_lowerx.
rewrite (prop_true_andp (cold01 _ /\ _)) by auto.
rewrite (prop_true_andp (0 <= sf_inSize _ /\ _)) by (unfold zdss_read; repeat split; auto; rep_lia).
rewrite (prop_true_andp (Zlength _ = _)) by auto.
apply andp_right.
{ apply prop_right. repeat match goal with |- _ /\ _ => split end;
  first [exact Hci | exact Hxc | close_lx | close_ex | close_en | close_un | lia | auto]. }
apply andp_right.
{ apply prop_right; repeat match goal with |- _ /\ _ => split end; auto. }
unfold vlong. cancel.
(* the allocator's part: the flush changes no size, so the bytes given out are the same *)
apply derives_refl.
Qed.

End CM_S3FlushLeaf_2.
