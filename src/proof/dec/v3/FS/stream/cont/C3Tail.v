(* FS3 streaming: ZSTD_decompressContinue, the part after the switch on the block type (port of
   v2 body_stream_continue.v blk_tail_ok). *)
Require Import Zstd.proof.dec.v3.FS.stream.S3Specs.
Require Import Zstd.proof.dec.v3.FS.stream.cont.C3Base.
Require Import Zstd.proof.dec.v3.FS.stream.cont.C3Mid.
Require Import Zstd.proof.zstd.XxhLemmas.
Require Import Zstd.proof.dec.v3.FS.stream.cont.C3XDefs.
Require Import Zstd.proof.dec.v3.FS.stream.cont.C3XBlk.

Section CM_C3Tail_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma blk_tail_ok (Espec: OracleKind) DENT TABS BR (HD: DENT_OK DENT) (HT: TABS_OK TABS) (Hsg: stuck_gap)
    gv p (f: Z) (dd: option (ddx * val)) (fs1: fstate) (ts: tstate) hdr z l W (o: outarr) src (i: inwin) n v_bp pcs st b ofs bh c'
    (Hst34: st = 3 \/ st = 4) (H0: fp_complete (FP_zstd hdr z) = false)
    (H1: exists c, Some c' = Some c /\
           (if bp_type (block_props_of bh) =? 0 then 1 <= n <= c - Zlength (zp_got z) else zp_got z = [] /\ n = c))
    (H2: 0 <= n <= Int64.max_unsigned) (Hsh: writable_share (oa_sh o)) (HcN: Zlength (oa_c o) = oa_N o)
    (HN32: oa_N o <= 2 ^ 63 - 1) (Hd: 0 <= oa_d o) (Hcap: 0 <= oa_cap o) (Hdc: oa_d o + oa_cap o <= oa_N o)
    (H4: lay_at l o) (H5: is_skip (FP_zstd hdr z) = true -> oa_cap o = 0)
    (H6: is_skip (FP_zstd hdr z) = false -> src = offset_val (iw_off i) (iw_base i) /\ inwin_ok i /\ Zlength (iw_s i) = n /\
          byte_cells (iw_c i))
    (H7: oa_N o = 0 -> pws_pred W |-- weak_valid_pointer (oa_base o))
    (H8: field_compatible (tarray tuchar (oa_N o)) [] (oa_base o))
    (Eb: oa_base o = Vptr b ofs) (HN: Ptrofs.unsigned ofs + oa_N o < Ptrofs.modulus)
    (Hcf1: c_frame fs1 (TInit (dd_ox dd) ts) (FP_zstd hdr z) (lmove l (oa_base o) (oa_d o) (oa_cap o)) dd)
    (Est1: fs_stage fs1 = Vint (Int.repr st)) (Ep1: fs_processedCSize fs1 = Vlong (Int64.repr pcs))
    (Hch: cont_hist (FP_zstd hdr z) l o)
    (Ez: zp_ph z = ZP_body bh) (Hl: bp_last (block_props_of bh) = 1 <-> st = 4)
    (Lf1: lay_fields fs1 (lmove l (oa_base o) (oa_d o) (oa_cap o)))
    (T0: fh_frameType (zp_h z) = 0) (Fp: fs_fParams fs1 = fh_val (fh_adj (zp_h z) (zp_bsm z)))
    (B1: 0 <= zp_bsm z <= fh_blockSizeMax (zp_h z))
    (B2: fh_blockSizeMax (zp_h z) = Z.min (fh_windowSize (zp_h z)) ZSTD_BLOCKSIZE_MAX)
    (W1: 0 <= fh_windowSize (zp_h z))
    (W2: Z.max (fh_windowSize (zp_h z)) ZSTD_WINDOWSIZE_ABSMIN <= 2 ^ 31)
    (Fc: 0 <= fh_contentSize (zp_h z) < 2 ^ 64)
    (Ck: fh_checksumFlag (zp_h z) = 0 \/ fh_checksumFlag (zp_h z) = 1)
    (Pst: fs_stage fs1 = Vint (Int.repr (if bp_last (block_props_of bh) =? 1 then ds_decompressLastBlock else ds_decompressBlock)))
    (Pbt: fs_bType fs1 = Vint (Int.repr (bp_type (block_props_of bh))))
    (Prle: fs_rleSize fs1 = Vlong (Int64.repr (bp_origSize (block_props_of bh))))
    (Pex: fs_expected fs1 = Vlong (Int64.repr (if bp_type (block_props_of bh) =? 0 then c' - Zlength (zp_got z) else c')))
    (Ed: fs_decodedSize fs1 = Vlong (Int64.repr (Zlength (zp_out z))))
    (Vc: fs_validateChecksum fs1 = Vint (Int.repr (if fcheck z then 1 else 0)))
    (Ex: fcheck z = true -> fs_xxh fs1 = Some (zp_out z))
    (Bo: bytes_ok (zp_out z)) (Lbh: Zlength bh = ZSTD_blockHeaderSize) (Bbh: bytes_ok bh)
    (Hgc: Zlength (zp_got z) < c') (Hcb: 0 < c' <= zp_bsm z) (Ec: cblock_size bh = Some c')
    (Ht3: bp_type (block_props_of bh) <> 3) (Bg: bytes_ok (zp_got z)) (Hu: unit_ok (FP_zstd hdr z) n)
    (Hsrc: src = offset_val (iw_off i) (iw_base i)) (Hiw: inwin_ok i) (Hlen: Zlength (iw_s i) = n)
    (XP: Z -> list val -> fstate -> option tstate -> Prop)
    (HXP: forall r oc' fs' tabs', (dd_ox dd = None -> cont_exact1 fs1 ts o (iw_s i) n r oc' fs' tabs') ->
            XP r oc' fs' tabs') :
  semax (func_tycontext f_ZSTD_decompressContinue Vprog (stream_G3 DENT TABS BR) nil)
    (EX r: Z, EX oc': list val, EX tso: option tstate, EX cold: val, EX e': Z,
      PROPx [dd_ox dd = None -> bres_exact fs1 ts o (iw_s i) n r oc' tso e';
             blk_mid hdr z bh c' l o (iw_s i) r oc' tso cold e' fs1]
      (LOCALx [temp _rSize (Vlong (Int64.repr r)); temp _t'20 (Vint (Int.repr st));
             temp _t'59 (Vlong (Int64.repr pcs));
             lvar _bp (Tstruct ___gp_blockProperties_t noattr) v_bp;
             gvars gv; temp _dctx p; temp _dst (offset_val (oa_d o) (oa_base o));
             temp _dstCapacity (Vlong (Int64.repr (oa_cap o)));
             temp _src src; temp _srcSize (Vlong (Int64.repr n))]
      (SEPx (blk_sep DENT TABS gv p f dd l fs1 pcs n (bp_type (block_props_of bh)) st W o i v_bp oc' tso cold e'))))%assert
    blk_tail
    (switch_ret_assert (dcc_R DENT TABS gv p f (FP_zstd hdr z) l dd W o i (fs_ddictIsCold fs1) (fs_fParams fs1) XP)).
Proof.
  set (l1 := lmove l (oa_base o) (oa_d o) (oa_cap o)) in *.
  unfold blk_tail, dcc_R. simplify_func_tycontext. abbreviate_semax.
  Intros r oc' tso cold e'. unfold blk_sep.
  match goal with Hm: blk_mid _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rename Hm into Hbm end.
  match goal with Hx: dd_ox dd = None -> bres_exact _ _ _ _ _ _ _ _ _ |- _ => rename Hx into Hbx end.
  assert (HoX: 0 <= oa_d o /\ 0 <= oa_cap o /\ oa_d o + oa_cap o <= oa_N o /\ oa_N o <= 2 ^ 63 - 1 /\
               Zlength (oa_c o) = oa_N o) by lia.
  assert (HbsmX: 0 <= zp_bsm z <= ZSTD_BLOCKSIZE_MAX) by (rewrite B2 in B1; unfold ZSTD_BLOCKSIZE_MAX in *; lia).
  pose proof Hbm as (Hr & HNoc & Hun & Hbc & Hcold & He' & Herr & Hsucc).
  set (PC := Vlong (Int64.add (Int64.repr pcs) (Int64.repr n))).
  unfold MORE_COMMANDS, abbreviate. abbreviate_semax.
  (* the error test *)
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_loop (PROPx P (LOCALx Q (SEPx R)))
      break: (PROPx ((is_error_code r = false) :: P) (LOCALx Q (SEPx R))) end.
  { entailer!. }
  { forward. forward_call r. forward_if.
    - dw0. dw0. dw0. dw0. forward.
      assert (Er: is_error_code r = true) by (destruct (is_error_code r); auto; contradiction).
      Exists r oc' (fsu_ddictIsCold (fsu_expected (fsu_processedCSize fs1 PC) (Vlong (Int64.repr e'))) cold) tso.
      unfold fsu_ddictIsCold, fsu_expected, fsu_processedCSize. ff_unfold. rewrite ?Pbt, ?Est1.
      unfold in_res; cbn [is_skip]. subst PC.
      match goal with |- context [XP ?a ?b ?c ?d] => assert (HX: XP a b c d)
        by (apply HXP; intros Hox; apply (cx_tail_err fs1 ts o (iw_s i) _ (zp_h z) (zp_bsm z) _ Est1 ltac:(lia) Fp ltac:(rep_lia) HbsmX Ck HoX r oc' tso e' a b c d (Hbx Hox) Er eq_refl)) end.
      entailer!.
      split; [auto |]. split; [auto |]. split; [auto |]. split; [exact Hbc |]. rewrite Er. auto.
    - forward. entailer!. destruct (is_error_code r); auto.
      exfalso. match goal with Hz: Int.repr 1 = Int.zero |- _ => exact (Int.one_not_zero Hz) end. }
  Intros. rename H into Ner.
  destruct (Hsucc Ner) as (Hrc & Hbig & Hok).
  assert (Hfh: fs_fParams fs1 = fh_val (fh_adj (zp_h z) (zp_bsm z))) by exact Fp.
  rewrite Fp. unfold fh_val, fh_adj; cbn [fh_contentSize fh_windowSize fh_blockSizeMax fh_frameType
    fh_headerSize fh_dictID fh_checksumFlag].
  assert (B1': zp_bsm z <= 131072) by (unfold ZSTD_BLOCKSIZE_MAX in B2; lia).
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_loop (PROPx P (LOCALx Q (SEPx R)))
      break: (PROPx ((r <= zp_bsm z) :: P) (LOCALx Q (SEPx R))) end.
  { entailer!. }
  { forward. forward_if.
    - dw0. dw0. dw0. dw0. forward.
      match goal with Hx: Int.unsigned (Int.repr (zp_bsm _)) < r |- _ =>
        rewrite Int.unsigned_repr in Hx by rep_lia end.
      Exists (2 ^ 64 - 20) oc' (fsu_ddictIsCold (fsu_expected (fsu_processedCSize fs1 PC) (Vlong (Int64.repr e'))) cold) tso.
      unfold fsu_ddictIsCold, fsu_expected, fsu_processedCSize. ff_unfold. rewrite ?Pbt, ?Est1, Fp.
      unfold in_res; cbn [is_skip]. subst PC. try rewrite <- repr_neg64.
      match goal with |- context [XP ?a ?b ?c ?d] => assert (HX: XP a b c d)
        by (apply HXP; intros Hox; apply (cx_tail_big fs1 ts o (iw_s i) _ (zp_h z) (zp_bsm z) _ Est1 ltac:(lia) Fp ltac:(rep_lia) HbsmX Ck HoX r oc' tso e' a b c d (Hbx Hox) ltac:(lia) eq_refl)) end.
      entailer!.
      split; [rep_lia |]. split; [auto |]. split; [auto |]. split; [exact Hbc |].
      replace (is_error_code (2 ^ 64 - 20)) with true by reflexivity.
      split; [apply Hbig; lia | apply nfp_ne; lia].
    - forward. entailer!.
      match goal with Hx: context [Int.unsigned (Int.repr (zp_bsm _))] |- _ =>
        rewrite Int.unsigned_repr in Hx by rep_lia end.
      lia. }
  Intros. rename H into Hrb.
  destruct (Hok Hrb) as (cnt & ts' & Ets' & Lcnt & Bcnt & Hsub & Hsafe & Hcnt & Hun2 & Hfcs & He'r).
  pose proof Hbc as Hby.
  dw0.
  rewrite Ed. forward. forward.
  rewrite Vc. forward.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    let R' := repl_item R (xxh_field p (fs_xxh fs1))
                (xxh_field p (if fcheck z then Some (zp_out z ++ cnt) else fs_xxh fs1)) in
    forward_if (PROPx P (LOCALx Q (SEPx R'))) end.
  { assert (Hf1: fcheck z = true).
    { destruct (fcheck z) eqn:E0; auto; exfalso; first [lia |
        match goal with Hx: Int.repr 0 <> Int.zero |- _ => apply Hx; reflexivity end]. }
    rewrite (Ex Hf1), Hf1. cbv iota. unfold xxh_field.
    assert_PROP (field_compatible t_dctx (DOT _expected) p) as Fce by entailer!.
    assert (Fcx: field_compatible t_dctx (DOT _xxhState) p).
    { apply field_compatible_cons in Fce. apply field_compatible_cons. simpl in Fce |- *.
      split; [| tauto]. unfold in_members. simpl. repeat (first [left; reflexivity | right]). }
    assert (Hrn: 0 <= oa_d o /\ oa_d o + r <= oa_N o) by lia.
    destruct (zlt 0 r) as [Hr0 | Hr0].
    - assert (Hsub': sublist (oa_d o) (oa_d o + Zlength cnt) oc' = zbytes cnt) by (rewrite Lcnt; auto).
      rewrite (arr_split (oa_sh o) (oa_N o) oc' (oa_base o) (oa_d o) cnt) by (auto; lia). Intros.
      forward_call (Ews, field_address t_dctx (DOT _xxhState) p, 0, zp_out z, oa_sh o,
                    offset_val (oa_d o) (oa_base o), cnt, @nil ptr_witness).
      { rewrite Lcnt. entailer!. simpl. rewrite field_compatible_field_address by auto. simpl. reflexivity. }
      { unfold pws_pred; simpl. cancel. }
      change (xxh_bytes cnt) with (zbytes cnt). change (pws_pred []) with (@emp mpred _ _).
      sep_apply (arr_join (oa_sh o) (oa_N o) oc' (oa_base o) (oa_d o) cnt); auto; try lia.
      try rewrite Hf1. cbv iota. unfold xxh_field.
      entailer!.
    - assert (Hr00: r = 0) by lia. rewrite Hr00 in *.
      destruct cnt; [| rewrite Zlength_cons in Lcnt; pose proof (Zlength_nonneg cnt); lia].
      assert (Ez0: data_at (oa_sh o) (tarray tuchar (Zlength (@nil Z))) (xxh_bytes []) (offset_val (oa_d o) (oa_base o)) = emp)
        by (apply data_at_zero_array_eq; auto; rewrite Eb; exact I).
      destruct (zlt 0 (oa_N o)) as [HN0 | HN0].
      + forward_call (Ews, field_address t_dctx (DOT _xxhState) p, 0, zp_out z, oa_sh o,
                      offset_val (oa_d o) (oa_base o), @nil Z, [pw_bytes (oa_sh o) (oa_N o) oc' (oa_base o)]).
        { rewrite Ez0. unfold pws_pred; simpl. unfold pw_pred. cancel. }
        { try intros _. unfold pws_pred; simpl. unfold pw_pred. rewrite sepcon_emp.
          apply arr_wvp; [apply readable_nonidentity, writable_readable; auto | lia | lia]. }
        rewrite Ez0. unfold pws_pred; cbn [map fold_right]. unfold pw_pred. rewrite sepcon_emp.
        try rewrite Hf1. cbv iota. unfold xxh_field. rewrite app_nil_r.
        entailer!.
      + assert (HN00: oa_N o = 0) by lia.
        match goal with Hw0: oa_N o = 0 -> (pws_pred W |-- _) |- _ => specialize (Hw0 HN00) as Hw end.
        forward_call (Ews, field_address t_dctx (DOT _xxhState) p, 0, zp_out z, oa_sh o,
                      offset_val (oa_d o) (oa_base o), @nil Z, W).
        { rewrite Ez0. cancel. }
        { try intros _. replace (oa_d o) with 0 by lia. rewrite isptr_offset_val_zero by (rewrite Eb; exact I). auto. }
        rewrite Ez0.
        try rewrite Hf1. cbv iota. unfold xxh_field. rewrite app_nil_r.
        entailer!. }
  { forward. entailer!.
    assert (Hf0: fcheck z = false).
    { destruct (fcheck z) eqn:E0; auto; exfalso; first [lia |
        match goal with Hz: Int.repr 1 = Int.zero |- _ => exact (Int.one_not_zero Hz) end]. }
    rewrite Hf0. cancel. }
  forward. forward. forward.
  assert (Eprev: force_val (sem_add_ptr_long tschar (offset_val (oa_d o) (oa_base o)) (Vlong (Int64.repr r)))
                 = offset_val (oa_d o + r) (oa_base o)).
  { rewrite Eb. simpl. unfold sem_add_ptr_long. simpl. f_equal. rewrite Ptrofs.add_assoc. f_equal.
    change (Ptrofs.repr 1) with Ptrofs.one. rewrite Ptrofs.mul_commut, Ptrofs.mul_one.
    unfold Ptrofs.of_int64. rewrite Int64.unsigned_repr by rep_lia. apply ptrofs_add_repr. }
  rewrite Eprev, add64_repr.
  subst r.
  forward_if.
  { (* a raw block not finished *)
    match goal with Hx: Int64.unsigned (Int64.repr 0) < Int64.unsigned (Int64.repr e') |- _ =>
      rewrite !Int64.unsigned_repr in Hx by rep_lia; rename Hx into He0 end.
    assert (Et0: bp_type (block_props_of bh) = 0).
    { destruct (bp_type (block_props_of bh) =? 0) eqn:E0 in He'r; [apply Z.eqb_eq; auto | lia]. }
    rewrite Et0 in He'r. cbn in He'r.
    destruct H1 as (c2 & Ec2 & Hn1). injection Ec2 as <-. rewrite Et0 in Hn1. cbn in Hn1.
    assert (Hinc: (Zlength (zp_got z ++ iw_s i) =? c') = false) by (apply Z.eqb_neq; lia).
    forward.
    assert (HC: cont_res (FP_zstd hdr z) l dd o (iw_s i) (Zlength cnt) oc'
      (fs_after fs1 (offset_val (oa_d o + Zlength cnt) (oa_base o)) (Vlong (Int64.repr (pcs + Zlength (iw_s i))))
         (Zlength (zp_out z)) (Zlength cnt) (bp_type (block_props_of bh))
         (if fcheck z then Some (zp_out z ++ cnt) else fs_xxh fs1) cold
         (Vlong (Int64.repr (c' - Zlength (zp_got z ++ iw_s i)))) (Vint (Int.repr st))) (Some ts')).
    { eapply cont_res_after; eauto.
      all: try (rewrite Hlen; auto; fail).
      all: try (rewrite Eb; exact I).
      all: try (destruct Hiw as (_ & _ & _ & _ & _ & _ & Hb_ & _); exact Hb_).
      all: unfold cont_checks, phase_fields, zstep; rewrite Ez; cbv zeta; rewrite Et0; cbn [Z.eqb];
        rewrite Ec, Hinc; cbn [zp_with zp_ph zp_got].
      - intros Hne; exfalso; apply Hne; reflexivity.
      - exists c'. split; [exact Ec |]. unfold fs_after; cbn [fs_stage fs_bType fs_rleSize fs_expected].
        unfold ds_decompressLastBlock, ds_decompressBlock in *. rewrite (stage_if st _ Hst34 Hl), Et0, Prle.
        split; [reflexivity |]. split; [reflexivity |]. split; reflexivity. }
    Exists (Zlength cnt) oc'
      (fs_after fs1 (offset_val (oa_d o + Zlength cnt) (oa_base o)) (Vlong (Int64.repr (pcs + Zlength (iw_s i))))
         (Zlength (zp_out z)) (Zlength cnt) (bp_type (block_props_of bh))
         (if fcheck z then Some (zp_out z ++ cnt) else fs_xxh fs1) cold
         (Vlong (Int64.repr (c' - Zlength (zp_got z ++ iw_s i)))) (Vint (Int.repr st))) (Some ts').
    match goal with |- context [XP ?a ?b ?c ?d] => assert (HX: XP a b c d)
      by (apply HXP; intros Hox;
          eapply (cx_tail_ok fs1 ts o (iw_s i) _ (zp_h z) (zp_bsm z) _ Est1 ltac:(lia) Fp ltac:(rep_lia) HbsmX Ck HoX (Zlength cnt) oc' ts' _ cnt (zp_out z) (fcheck z) _ (st) (c' - Zlength (zp_got z ++ iw_s i)));
          [ first [exact (Hbx Hox) | rewrite <- Ets'; exact (Hbx Hox)] | exact Ner | exact Hrb | lia | reflexivity | exact Bcnt | exact Hsub
          | exact Ed | exact Vc | exact Ex | reflexivity | reflexivity | reflexivity | reflexivity
          | rewrite Pbt; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
          | reflexivity | reflexivity | reflexivity | reflexivity
          | intros _; split; [reflexivity | first [reflexivity | symmetry; assumption]] | intros; lia | intros; lia ]) end.
    entailer!.
    unfold frame_fields, fs_after; cbn [fs_previousDstEnd fs_gpDictCopy fs_prefixStart fs_virtualStart fs_dictEnd fs_expected
      fs_fParams fs_processedCSize fs_decodedSize fs_bType fs_stage fs_xxh fs_headerSize fs_validateChecksum
      fs_rleSize fs_isFrameDecompression fs_dictID fs_ddictIsCold].
    rewrite Fp, Vc. unfold in_res; cbn [is_skip]. subst PC. rewrite add64_repr.
    cancel. }
  (* the block is finished *)
  assert (He0: e' = 0) by (rewrite !Int64.unsigned_repr in H by rep_lia; lia). subst e'.
  forward. apply semax_if_seq. forward_if.
  { (* stage 4: the end of the frame *)
    destruct Hst34 as [-> | ->]; [st_contra |].
    assert (El1: bp_last (block_props_of bh) = 1)
      by (apply Hl; reflexivity).
  dw0.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_loop (PROPx P (LOCALx Q (SEPx R)))
      break: (PROPx ((fh_contentSize (zp_h z) = ZSTD_CONTENTSIZE_UNKNOWN \/
                      (Zlength (zp_out z) + Zlength cnt) mod 2 ^ 64 = fh_contentSize (zp_h z)) :: P)
                (LOCALx Q (SEPx R))) end.
  { entailer!. }
  { forward. fif_set _t'16 (Vint (Int.repr (fcs_t15 (fh_contentSize (zp_h z)) (Zlength (zp_out z) + Zlength cnt)))).
    - forward. forward. forward. entailer!. apply fcs_then; auto.
    - forward. entailer!.
      match goal with Hx: Int64.eq _ _ = true |- _ => apply Int64.same_if_eq in Hx; rewrite fcs_else; auto end.
    - assert (F01: fcs_t15 (fh_contentSize (zp_h z)) (Zlength (zp_out z) + Zlength cnt) = 0 \/
                   fcs_t15 (fh_contentSize (zp_h z)) (Zlength (zp_out z) + Zlength cnt) = 1)
        by (unfold fcs_t15; repeat destruct (_ =? _); auto).
      forward_if.
      + dw0. dw0. dw0. dw0. forward.
        assert (F1: fcs_t15 (fh_contentSize (zp_h z)) (Zlength (zp_out z) + Zlength cnt) = 1).
        { destruct F01 as [E | E]; auto. rewrite E in *. contradiction. }
        assert (HE: cont_res (FP_zstd hdr z) l dd o (iw_s i) (2 ^ 64 - 20) oc'
          (fs_after fs1 (offset_val (oa_d o + Zlength cnt) (oa_base o)) PC (Zlength (zp_out z)) (Zlength cnt)
             (bp_type (block_props_of bh))
             (if fcheck z then Some (zp_out z ++ cnt) else fs_xxh fs1) cold
             (Vlong (Int64.repr 0)) (Vint (Int.repr 4))) (Some ts')).
        { split; [rep_lia |]. split; [auto |]. split; [auto |]. split; [exact Hbc |].
          replace (is_error_code (2 ^ 64 - 20)) with true by reflexivity.
          split; [| apply nfp_ne; lia]. intros Hp. apply Hfcs; auto.
          destruct (fcs_bad_of (Zlength (zp_out z) + Zlength cnt) (fh_contentSize (zp_h z)) Fc ltac:(lia))
            as [Q1 Q2].
          unfold fcs_bad, ZSTD_CONTENTSIZE_UNKNOWN. rewrite Zlength_app. auto. }
        Exists (2 ^ 64 - 20) oc'
          (fs_after fs1 (offset_val (oa_d o + Zlength cnt) (oa_base o)) PC (Zlength (zp_out z)) (Zlength cnt)
             (bp_type (block_props_of bh))
             (if fcheck z then Some (zp_out z ++ cnt) else fs_xxh fs1) cold
             (Vlong (Int64.repr 0)) (Vint (Int.repr 4))) (Some ts').
        try rewrite <- repr_neg64.
        match goal with |- context [XP ?a ?b ?c ?d] => assert (HX: XP a b c d)
          by (apply HXP; intros Hox;
              unfold fcs_t15 in F1; destruct (_ =? _) eqn:E1 in F1; [discriminate |];
              destruct (_ =? _) eqn:E2 in F1; [discriminate |]; apply Z.eqb_neq in E1, E2;
              apply (cx_tail_fcs fs1 ts o (iw_s i) _ (zp_h z) (zp_bsm z) _ Est1 ltac:(lia) Fp ltac:(rep_lia) HbsmX Ck HoX (Zlength cnt) oc' ts' 0 (zp_out z) a b c d
                       ltac:(first [exact (Hbx Hox) | rewrite <- Ets'; exact (Hbx Hox)]) Ner Hrb eq_refl eq_refl Ed E1 E2 eq_refl)) end.
        entailer!.
        unfold frame_fields, fs_after; cbn [fs_previousDstEnd fs_gpDictCopy fs_prefixStart fs_virtualStart fs_dictEnd
          fs_expected fs_fParams fs_processedCSize fs_decodedSize fs_bType fs_stage fs_xxh fs_headerSize
          fs_validateChecksum fs_rleSize fs_isFrameDecompression fs_dictID fs_ddictIsCold].
        rewrite Fp, Vc. unfold in_res; cbn [is_skip]. cancel.
      + forward. entailer!.
        destruct F01 as [E | E];
          [apply fcs_ok_of in E; unfold ZSTD_CONTENTSIZE_UNKNOWN; tauto
          | rewrite E in *; exfalso; match goal with Hz: Int.repr 1 = Int.zero |- _ => exact (Int.one_not_zero Hz) end]. }
  Intros. match goal with Hx: fh_contentSize (zp_h z) = ZSTD_CONTENTSIZE_UNKNOWN \/ _ |- _ => rename Hx into HF end.
  assert (Hcc: cont_checks z (iw_s i) cnt)
    by (unfold cont_checks; rewrite Ez; intros _ _; rewrite Zlength_app; exact HF).
  assert (Zph: zp_ph (zstep z (iw_s i) cnt ts') = next_phase (zp_h z) bh).
  { unfold zstep. rewrite Ez. cbv zeta. destruct (bp_type (block_props_of bh) =? 0) eqn:E0.
    { cbv iota in He'r. rewrite Ec.
      replace (Zlength (zp_got z ++ iw_s i) =? c') with true by (symmetry; apply Z.eqb_eq; lia). reflexivity. }
    { destruct (bp_type (block_props_of bh) =? 1); reflexivity. } }
  subst PC. rewrite add64_repr. try subst n.
  forward. apply semax_if_seq. forward_if.
  { (* another round for the checksum *)
    assert (Ef: fh_checksumFlag (zp_h z) = 1) by (destruct Ck as [E | E]; auto; rewrite E in *; contradiction).
    forward. forward. forward.
    assert (HC: cont_res (FP_zstd hdr z) l dd o (iw_s i) (Zlength cnt) oc'
      (fs_after fs1 (offset_val (oa_d o + Zlength cnt) (oa_base o)) (Vlong (Int64.repr (pcs + Zlength (iw_s i))))
        (Zlength (zp_out z)) (Zlength cnt) (bp_type (block_props_of bh))
        (if fcheck z then Some (zp_out z ++ cnt) else fs_xxh fs1) cold (Vlong (Int64.repr 4)) (Vint (Int.repr 5))) (Some ts')).
    { eapply cont_res_after; eauto.
      all: try (rewrite Eb; exact I).
      all: try (destruct Hiw as (_ & _ & _ & _ & _ & _ & Hb_ & _); exact Hb_).
      unfold phase_fields. rewrite Zph. unfold next_phase. rewrite El1, Ef. cbn. split; reflexivity. }
    Exists (Zlength cnt) oc'
      (fs_after fs1 (offset_val (oa_d o + Zlength cnt) (oa_base o)) (Vlong (Int64.repr (pcs + Zlength (iw_s i))))
        (Zlength (zp_out z)) (Zlength cnt) (bp_type (block_props_of bh))
        (if fcheck z then Some (zp_out z ++ cnt) else fs_xxh fs1) cold (Vlong (Int64.repr 4)) (Vint (Int.repr 5))) (Some ts').
    match goal with |- context [XP ?a ?b ?c ?d] => assert (HX: XP a b c d)
      by (apply HXP; intros Hox;
          eapply (cx_tail_ok fs1 ts o (iw_s i) _ (zp_h z) (zp_bsm z) _ Est1 ltac:(lia) Fp ltac:(rep_lia) HbsmX Ck HoX (Zlength cnt) oc' ts' _ cnt (zp_out z) (fcheck z) _ (5) (4));
          [ first [exact (Hbx Hox) | rewrite <- Ets'; exact (Hbx Hox)] | exact Ner | exact Hrb | lia | reflexivity | exact Bcnt | exact Hsub
          | exact Ed | exact Vc | exact Ex | reflexivity | reflexivity | reflexivity | reflexivity
          | rewrite Pbt; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
          | reflexivity | reflexivity | reflexivity | reflexivity
          | intros; lia | intros; lia | intros _ _; split; [ match goal with Hx: fh_contentSize (zp_h z) = ZSTD_CONTENTSIZE_UNKNOWN \/ _ |- _ => exact Hx end | rewrite Ef; split; reflexivity ] ]) end.
    entailer!.
    unfold frame_fields, fs_after; cbn [fs_previousDstEnd fs_gpDictCopy fs_prefixStart fs_virtualStart fs_dictEnd
      fs_expected fs_fParams fs_processedCSize fs_decodedSize fs_bType fs_stage fs_xxh fs_headerSize
      fs_validateChecksum fs_rleSize fs_isFrameDecompression fs_dictID fs_ddictIsCold].
    rewrite Fp, Vc. unfold in_res; cbn [is_skip]. cancel. }
  { (* the end of the frame *)
    assert (Ef: fh_checksumFlag (zp_h z) = 0).
    { destruct Ck as [E | E]; auto. exfalso.
      match goal with Hz: Int.repr (fh_checksumFlag _) = Int.zero |- _ =>
        rewrite E in Hz; exact (Int.one_not_zero Hz) end. }
    forward. forward. forward_call (p, Zlength (zp_out z) + Zlength cnt, pcs + Zlength (iw_s i), 1).
    forward. forward. forward.
    assert (HC: cont_res (FP_zstd hdr z) l dd o (iw_s i) (Zlength cnt) oc'
      (fs_after fs1 (offset_val (oa_d o + Zlength cnt) (oa_base o)) (Vlong (Int64.repr (pcs + Zlength (iw_s i))))
        (Zlength (zp_out z)) (Zlength cnt) (bp_type (block_props_of bh))
        (if fcheck z then Some (zp_out z ++ cnt) else fs_xxh fs1) cold (Vlong (Int64.repr 0)) (Vint (Int.repr 0))) (Some ts')).
    { eapply cont_res_after; eauto.
      all: try (rewrite Eb; exact I).
      all: try (destruct Hiw as (_ & _ & _ & _ & _ & _ & Hb_ & _); exact Hb_).
      unfold phase_fields. rewrite Zph. unfold next_phase. rewrite El1, Ef. cbn. split; reflexivity. }
    Exists (Zlength cnt) oc'
      (fs_after fs1 (offset_val (oa_d o + Zlength cnt) (oa_base o)) (Vlong (Int64.repr (pcs + Zlength (iw_s i))))
        (Zlength (zp_out z)) (Zlength cnt) (bp_type (block_props_of bh))
        (if fcheck z then Some (zp_out z ++ cnt) else fs_xxh fs1) cold (Vlong (Int64.repr 0)) (Vint (Int.repr 0))) (Some ts').
    match goal with |- context [XP ?a ?b ?c ?d] => assert (HX: XP a b c d)
      by (apply HXP; intros Hox;
          eapply (cx_tail_ok fs1 ts o (iw_s i) _ (zp_h z) (zp_bsm z) _ Est1 ltac:(lia) Fp ltac:(rep_lia) HbsmX Ck HoX (Zlength cnt) oc' ts' _ cnt (zp_out z) (fcheck z) _ (0) (0));
          [ first [exact (Hbx Hox) | rewrite <- Ets'; exact (Hbx Hox)] | exact Ner | exact Hrb | lia | reflexivity | exact Bcnt | exact Hsub
          | exact Ed | exact Vc | exact Ex | reflexivity | reflexivity | reflexivity | reflexivity
          | rewrite Pbt; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
          | reflexivity | reflexivity | reflexivity | reflexivity
          | intros; lia | intros; lia | intros _ _; split; [ match goal with Hx: fh_contentSize (zp_h z) = ZSTD_CONTENTSIZE_UNKNOWN \/ _ |- _ => exact Hx end | rewrite Ef; simpl; split; reflexivity ] ]) end.
    entailer!.
    unfold frame_fields, fs_after; cbn [fs_previousDstEnd fs_gpDictCopy fs_prefixStart fs_virtualStart fs_dictEnd
      fs_expected fs_fParams fs_processedCSize fs_decodedSize fs_bType fs_stage fs_xxh fs_headerSize
      fs_validateChecksum fs_rleSize fs_isFrameDecompression fs_dictID fs_ddictIsCold].
    rewrite Fp, Vc. unfold in_res; cbn [is_skip]. cancel. }
  }
  { (* stage 3: the next block header *)
    destruct Hst34 as [-> | ->]; [| st_contra].
  assert (El0: bp_last (block_props_of bh) <> 1) by (intros E1; apply Hl in E1; lia).
  assert (Hcc: cont_checks z (iw_s i) cnt) by (unfold cont_checks; rewrite Ez; intros _ E1; contradiction).
  assert (Zph: zp_ph (zstep z (iw_s i) cnt ts') = ZP_bhdr).
  { unfold zstep. rewrite Ez. cbv zeta. unfold next_phase.
    destruct (Z.eqb_spec (bp_last (block_props_of bh)) 1) as [E1 | _]; [contradiction |].
    destruct (bp_type (block_props_of bh) =? 0) eqn:E0.
    { cbv iota in He'r. rewrite Ec.
      replace (Zlength (zp_got z ++ iw_s i) =? c') with true by (symmetry; apply Z.eqb_eq; lia). reflexivity. }
    { destruct (bp_type (block_props_of bh) =? 1); reflexivity. } }
  subst PC. rewrite add64_repr. try subst n.
  forward. unfold zstd_globals. Intros. forward. sep_apply (zstd_globals_fold gv). forward. forward.
  assert (HC: cont_res (FP_zstd hdr z) l dd o (iw_s i) (Zlength cnt) oc'
    (fs_after fs1 (offset_val (oa_d o + Zlength cnt) (oa_base o)) (Vlong (Int64.repr (pcs + Zlength (iw_s i))))
      (Zlength (zp_out z)) (Zlength cnt) (bp_type (block_props_of bh))
      (if fcheck z then Some (zp_out z ++ cnt) else fs_xxh fs1) cold
      (Vlong (Int64.repr ZSTD_blockHeaderSize)) (Vint (Int.repr 2))) (Some ts')).
  { eapply cont_res_after; eauto.
    all: try (rewrite Eb; exact I).
    all: try (destruct Hiw as (_ & _ & _ & _ & _ & _ & Hb_ & _); exact Hb_).
    unfold phase_fields. rewrite Zph. cbn. split; reflexivity. }
  Exists (Zlength cnt) oc'
    (fs_after fs1 (offset_val (oa_d o + Zlength cnt) (oa_base o)) (Vlong (Int64.repr (pcs + Zlength (iw_s i))))
      (Zlength (zp_out z)) (Zlength cnt) (bp_type (block_props_of bh))
      (if fcheck z then Some (zp_out z ++ cnt) else fs_xxh fs1) cold
      (Vlong (Int64.repr ZSTD_blockHeaderSize)) (Vint (Int.repr 2))) (Some ts').
  match goal with |- context [XP ?a ?b ?c ?d] => assert (HX: XP a b c d)
      by (apply HXP; intros Hox;
          eapply (cx_tail_ok fs1 ts o (iw_s i) _ (zp_h z) (zp_bsm z) _ Est1 ltac:(lia) Fp ltac:(rep_lia) HbsmX Ck HoX (Zlength cnt) oc' ts' _ cnt (zp_out z) (fcheck z) _ (2) (ZSTD_blockHeaderSize));
          [ first [exact (Hbx Hox) | rewrite <- Ets'; exact (Hbx Hox)] | exact Ner | exact Hrb | lia | reflexivity | exact Bcnt | exact Hsub
          | exact Ed | exact Vc | exact Ex | reflexivity | reflexivity | reflexivity | reflexivity
          | rewrite Pbt; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
          | reflexivity | reflexivity | reflexivity | reflexivity
          | intros; lia | intros _ _; split; reflexivity | intros; lia ]) end.
  entailer!.
  unfold frame_fields, fs_after; cbn [fs_previousDstEnd fs_gpDictCopy fs_prefixStart fs_virtualStart fs_dictEnd
    fs_expected fs_fParams fs_processedCSize fs_decodedSize fs_bType fs_stage fs_xxh fs_headerSize
    fs_validateChecksum fs_rleSize fs_isFrameDecompression fs_dictID fs_ddictIsCold].
  rewrite Fp, Vc. unfold in_res; cbn [is_skip]. unfold ZSTD_blockHeaderSize_val. cancel.
  }
Qed.

End CM_C3Tail_1.
