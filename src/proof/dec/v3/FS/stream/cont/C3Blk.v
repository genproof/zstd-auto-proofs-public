(* FS3 streaming: ZSTD_decompressContinue, the block stages (decompressBlock = 3,
   decompressLastBlock = 4: the same code; port of v2 body_stream_continue.v blk_case_ok). *)
Require Import Zstd.proof.dec.v3.FS.stream.S3Specs.
Require Import Zstd.proof.dec.v3.FS.stream.cont.C3Base.
Require Import Zstd.proof.dec.v3.FS.stream.cont.C3Mid.
Require Import Zstd.proof.dec.v3.FS.stream.cont.C3Tail.
Require Import Zstd.proof.zstd.XxhLemmas.
Require Import Zstd.proof.dec.v3.FS.stream.cont.C3XDefs.
Require Import Zstd.proof.dec.v3.FS.stream.cont.C3XBlk.
Require Import Zstd.proof.dec.v3.FS.stream.cont.C3XDec.

Section CM_C3Blk_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* cap > 0: the DDict content the moved layout's extDict refers to, and the rest of lay_res *)
Definition lay_keep (l: hlay) (o: outarr) : mpred :=
  match lmove l (oa_base o) (oa_d o) (oa_cap o) with HL_seg _ _ _ (ExtSep _ _ _ _ _ _) => emp | _ => lay_res l end.

Lemma lay_res_seg l o ps ex :
  0 < oa_cap o -> lmove l (oa_base o) (oa_d o) (oa_cap o) = HL_seg (oa_base o) ps (oa_d o) ex ->
  lay_res l = (ext_res ex * lay_keep l o)%logic.
Proof.
  intros Hc El. unfold lay_keep. rewrite El. unfold lmove in El.
  replace (oa_cap o <=? 0) with false in El by (symmetry; apply Z.leb_gt; lia).
  destruct l as [ | eb ec gp | b pe od | b ps' pe e]; cbn in El.
  - inv El. cbn. rewrite sepcon_emp; auto.
  - inv El. cbn. rewrite sepcon_emp; auto.
  - discriminate.
  - destruct (pe =? oa_d o); inv El.
    + destruct ex; cbn; rewrite ?sepcon_emp; auto.
    + cbn. rewrite emp_sepcon. auto.
Qed.

(* without room, the extDict the block decoder is given: none, or one in the ring (which cont_exact's premise
   excludes) *)
Lemma ext0_exact fs l dd o b ofs :
  dd_ox dd = None -> lay_fields fs l -> lay_dd l dd -> lay_at l o -> oa_base o = Vptr b ofs -> oa_N o <= 2 ^ 63 - 1 ->
  ext0 l o = ExtNone \/ exists e1, fs_dictEnd fs = offset_val e1 (Vptr b ofs) /\ 0 <= e1 <= Ptrofs.max_unsigned.
Proof.
  intros Hox Lf Ld La Eb HN. destruct dd as [[x0 b0] |]; [discriminate Hox |].
  destruct l as [ | eb ec gp | b1 pe [[[eb ec] gp] |] | b1 ps pe [ | e1 elen | sh eb en ec e1 elen]]; cbn in Ld |- *;
    try (left; reflexivity).
  - destruct Ld as (x & Hx & _). discriminate.
  - destruct Ld as (x & Hx & _). discriminate.
  - right. exists e1. destruct Lf as (_ & _ & _ & _ & _ & _ & Hde & _). destruct La as [-> La].
    rewrite Eb in Hde. split; [exact Hde |]. change Ptrofs.max_unsigned with (2 ^ 64 - 1). decompose [and] La. lia.
  - destruct Ld as (_ & _ & _ & _ & gp & x & Hx & _). discriminate.
Qed.

Lemma blk_case_ok (Espec: OracleKind) DENT TABS BR (HD: DENT_OK DENT) (HT: TABS_OK TABS) (Hsg: stuck_gap) (Hdg: dd_gap)
    gv p (f: Z) (dd: option (ddx * val)) (fs1: fstate) ts fp l W (o: outarr) src (i: inwin) n v_bp pcs st b ofs
    (cold0: val) (fpar0: reptype t_fh) (XP: Z -> list val -> fstate -> option tstate -> Prop) :
  (st = 3 \/ st = 4) -> fp_complete fp = false -> unit_ok fp n -> 0 <= n <= Int64.max_unsigned ->
  writable_share (oa_sh o) -> Zlength (oa_c o) = oa_N o -> oa_N o <= 2 ^ 63 - 1 -> 0 <= oa_d o -> 0 <= oa_cap o ->
  oa_d o + oa_cap o <= oa_N o -> lay_at l o -> (is_skip fp = true -> oa_cap o = 0) ->
  (is_skip fp = false -> src = offset_val (iw_off i) (iw_base i) /\ inwin_ok i /\ Zlength (iw_s i) = n /\
     byte_cells (iw_c i)) ->
  (oa_N o = 0 -> (pws_pred W |-- weak_valid_pointer (oa_base o))) ->
  field_compatible (tarray tuchar (oa_N o)) [] (oa_base o) ->
  oa_base o = Vptr b ofs -> Ptrofs.unsigned ofs + oa_N o < Ptrofs.modulus ->
  c_frame fs1 (TInit (dd_ox dd) ts) fp (lmove l (oa_base o) (oa_d o) (oa_cap o)) dd ->
  fs_stage fs1 = Vint (Int.repr st) -> fs_processedCSize fs1 = Vlong (Int64.repr pcs) ->
  fs_ddictIsCold fs1 = cold0 -> fs_fParams fs1 = fpar0 -> cont_hist fp l o -> lay_dd l dd -> lay_wit W l ->
  (* the exact claim (C3XDefs.cont_exact1) gives the caller's *)
  (forall r oc' fs' tabs', (dd_ox dd = None -> cont_exact1 fs1 ts o (iw_s i) n r oc' fs' tabs') -> XP r oc' fs' tabs') ->
  semax (func_tycontext f_ZSTD_decompressContinue Vprog (stream_G3 DENT TABS BR) nil)
    (blk_pre DENT TABS gv p f dd l fs1 ts fp W o src i n v_bp pcs st) blk_cmd
    (switch_ret_assert (dcc_R DENT TABS gv p f fp l dd W o i cold0 fpar0 XP)).
Proof.
  intros Hst34 H0 H1 H2 Hsh HcN HN32 Hd Hcap Hdc H4 H5 H6 H7 H8 Eb HN Hcf1 Est1 Ep1 Ecold0 Efpar0 Hch Ld Hw HXP.
  subst cold0 fpar0.
  assert (HoX: 0 <= oa_d o /\ 0 <= oa_cap o /\ oa_d o + oa_cap o <= oa_N o /\ oa_N o <= 2 ^ 63 - 1 /\
               Zlength (oa_c o) = oa_N o) by lia.
  set (l1 := lmove l (oa_base o) (oa_d o) (oa_cap o)) in *.
  unfold blk_pre, blk_cmd, dcc_R. simplify_func_tycontext. abbreviate_semax.
    pose proof (stage_inv _ _ _ _ _ _ Hcf1 H0 Est1 ltac:(lia)) as Hfp.
    destruct fp as [ | | hdr got | hdr z]; try contradiction.
    { unfold ds_skipFrame in Hfp; lia. }
    destruct (zp_ph z) as [ | bh | | ] eqn:Ez; try contradiction;
      unfold ds_decodeBlockHeader, ds_checkChecksum, ds_decompressLastBlock, ds_decompressBlock in Hfp;
      try lia.
    (* the stage as an iff: VST's subst would otherwise eliminate st *)
    assert (Hl: bp_last (block_props_of bh) = 1 <-> st = 4)
      by (rewrite Hfp; destruct (Z.eqb_spec (bp_last (block_props_of bh)) 1); split; intros; auto; try contradiction; lia).
    clear Hfp.
    pose proof Hcf1 as Hc1. destruct Hc1 as (_ & _ & _ & Lf1 & Ld1 & M1).
    destruct M1 as (T0 & Fp & B1 & B2 & W1 & W2 & Fc & Ck & Dm & Ets & Ph & Ed & Vc & Ex & Bo & Mz & Bg).
    assert (Hbsm: 0 <= zp_bsm z <= ZSTD_BLOCKSIZE_MAX) by (rewrite B2 in B1; unfold ZSTD_BLOCKSIZE_MAX in *; lia).
    rewrite Ez in Mz. unfold phase_fields in Ph. rewrite Ez in Ph.
    destruct Mz as (Lbh & Bbh & c & Ec & Hcb & Hgc & Ht3).
    destruct Ph as (c' & Ec' & Pst & Pbt & Prle & Pex). rewrite Ec in Ec'. inv Ec'.
    pose proof H1 as Hu. cbn [unit_ok] in H1. rewrite Ez, Ec in H1.
    destruct (H6 eq_refl) as (Hsrc & Hiw & Hlen & Hbcin).
    destruct Ets as (ts0 & Ets & Ets'). injection Ets as Ets. subst ts0.
    unfold in_res; cbn [is_skip].
    dw0.
    rewrite Pbt. forward.
    apply semax_seq with (EX r: Z, EX oc': list val, EX tso: option tstate, EX cold: val, EX e': Z,
      PROPx [dd_ox dd = None -> bres_exact fs1 ts o (iw_s i) n r oc' tso e';
             blk_mid hdr z bh c' l o (iw_s i) r oc' tso cold e' fs1]
      (LOCALx [temp _rSize (Vlong (Int64.repr r)); temp _t'20 (Vint (Int.repr st));
             temp _t'59 (Vlong (Int64.repr pcs));
             lvar _bp (Tstruct ___gp_blockProperties_t noattr) v_bp;
             gvars gv; temp _dctx p; temp _dst (offset_val (oa_d o) (oa_base o));
             temp _dstCapacity (Vlong (Int64.repr (oa_cap o)));
             temp _src src; temp _srcSize (Vlong (Int64.repr n))]
      (SEPx (blk_sep DENT TABS gv p f dd l fs1 pcs n (bp_type (block_props_of bh)) st W o i v_bp oc' tso cold e'))))%assert.
    pose proof (bp_type_range bh) as Hbtr.
    forward_switch'.
    all: try (exfalso; lia).
    + (* compressed *)
      match goal with E: bp_type (block_props_of bh) = 2 |- _ => rename E into Et end.
      destruct H1 as (cc & Ecc & Hn). inv Ecc. rewrite Et in Hn. cbn in Hn. destruct Hn as [Hg0 Hn].
      pose proof Hiw as (Rs & Ho & Hon & HNi & Hci & Hsi & Hbi & Hwi).
      assert (Hoo: outarr_ok o) by (split; [exact Hsh |]; repeat split; auto; lia).
      dw0.
      set (fsc := fsu_stage (fsu_bType (fsu_processedCSize fs1
                   (Vlong (Int64.add (Int64.repr pcs) (Int64.repr (Zlength (iw_s i))))))
                   (Vint (Int.repr (bp_type (block_props_of bh))))) (Vint (Int.repr st))).
      pose proof (frame_fields_fold p fsc) as Hff.
      unfold fsc, fsu_stage, fsu_bType, fsu_processedCSize in Hff.
      cbn [fs_previousDstEnd fs_gpDictCopy fs_prefixStart fs_virtualStart fs_dictEnd fs_expected
        fs_fParams fs_processedCSize fs_decodedSize fs_bType fs_stage fs_xxh fs_headerSize fs_validateChecksum
        fs_rleSize fs_isFrameDecompression fs_dictID fs_ddictIsCold] in Hff.
      sep_apply Hff. clear Hff.
      assert (Fbsm: fp_blockSizeMax (fs_fParams fsc) = Vint (Int.repr (zp_bsm z)))
        by (unfold fsc; cbn; rewrite Fp; reflexivity).
      destruct (zlt 0 (oa_cap o)) as [Hc0 | Hc0].
      * (* cap > 0: the whole output array, the history as hist_pre says *)
        destruct (lmove_seg l dd W o H4 Ld Hw Hoo Hc0) as (ps & ex & El & Lseg & Hpsd).
        assert (Lfs: lay_fields fs1 (HL_seg (oa_base o) ps (oa_d o) ex))
          by (change l1 with (lmove l (oa_base o) (oa_d o) (oa_cap o)) in Lf1; rewrite El in Lf1; exact Lf1).
        assert (Lds: lay_dd (HL_seg (oa_base o) ps (oa_d o) ex) dd)
          by (change l1 with (lmove l (oa_base o) (oa_d o) (oa_cap o)) in Ld1; rewrite El in Ld1; exact Ld1).
        assert (EH: lay_H z l o = hist_for ex z) by (unfold lay_H; rewrite El; reflexivity).
        assert (HHb: bytes_ok (lay_H z l o)) by (apply (lay_H_bytes z l dd o Hdg); [exact Ld1 | exact Dm]).
        rewrite (lay_res_seg l o ps ex Hc0 El). Intros.
        assert_PROP (ext_ptr ex) as Hep by (sep_apply (ext_res_ptr ex); entailer!).
        (* the history the block's matches copy is defined (cont_hist) *)
        assert_PROP (bytes_ok (ts_lxb ts)) as Hlxb
          by (sep_apply (HT gv p (dd_ox dd) ts); unfold tables_uninit, lit_extra_at; entailer!).
        assert (Hhd0: hist_def (oa_c o) (oa_d o) ps ex).
        { assert (Hch0 := Hch). unfold cont_hist in Hch0. rewrite Ez in Hch0. specialize (Hch0 Et Hc0).
          rewrite El in Hch0. exact (proj1 Hch0). }
        forward_call (gv, p, fsc, dd_ox dd, ts, zp_bsm z, 1, W, o, i,
          {| hc_ext := ex; hc_ps := ps; hc_hist := lay_H z l o; hc_out := zp_out z; hc_wsize := fh_windowSize (zp_h z) |}).
        { cbn [hc_ext]. unfold fsc. ff_unfold. cancel. }
        { unfold fsc. ff_unfold.
          destruct Hcf1 as (I1 & I2 & _). split; [exact I1 |]. split; [exact I2 |].
          split; [| split; [destruct ex; cbn; auto | split; [cbn [hc_ext]; apply (hpo_seg _ _ ps); [exact Lfs | exact Lseg] |
                   cbn [hc_ext]; first [apply (ext0_ok_seg W fs1 l dd o ps ex El Hc0 Lfs Ld Hw Hdg Hep) |
                                        split; [apply (ext0_ok_seg W fs1 l dd o ps ex El Hc0 Lfs Ld Hw Hdg Hep) |
                                                exact Hhd0]]]]]. intros _.
          destruct Lfs as (_ & _ & Hps & _ & Hpre & Hvirt & Hde). destruct Lseg as (_ & Hel & Hm).
          unfold layout_ok. cbn [hc_ps hc_ext]. split; [lia |]. split; [exact Hpre |]. split; [exact Hvirt |].
          split; [exact Hel |]. destruct ex; [auto | destruct Hde, Hm; auto | ].
          destruct Hde as [? ?], Hm as (? & ? & ? & ? & ?). repeat split; auto. }
        Intros vret. destruct vret as [[[r oc'] cold] tso]; cbn [fst snd hc_ext hc_ps hc_hist hc_out hc_wsize] in *.
        match goal with Hx: dd_ox dd = None -> block_exact _ _ _ _ _ _ _ _ _ |- _ => rename Hx into Hbx end.
        rewrite Ets' in *.
        unfold fs_set_cold, fsc. ff_unfold. Intros.
        forward. forward.
        Exists r oc' tso cold 0. unfold blk_sep. rewrite (lay_res_seg l o ps ex Hc0 El). entailer!.
        split.
        { intros Hox. eapply (bres_comp fs1 ts o (iw_s i) _ st (zp_h z) (zp_bsm z) Est1 Hst34 ltac:(rewrite Pbt, Et; reflexivity) HoX Fp ltac:(rep_lia) Hbsm Ck Hbi Hlxb r oc' tso i _ b ofs ps ex Hc0 Eb Lfs Lseg Hpsd); auto; try reflexivity.
          destruct dd as [[x0 b0] |]; [discriminate Hox |].
          destruct ex as [ | | sh eb en ec e1 elen]; [exact I | exact I |].
          destruct Lds as (_ & _ & _ & _ & gp & x & Hx & _). discriminate. }
        assert (Hch' := Hch). unfold cont_hist in Hch'. rewrite Ez in Hch'. specialize (Hch' Et Hc0).
        rewrite El in Hch'. rename Hch' into Hhd.
        assert (Hwb: win_bytes (oa_c o) oc').
        { intros Hb. match goal with Hx: byte_cells (oa_c o) -> byte_cells (iw_c i) -> ext_bytes _ -> byte_cells oc' |- _ =>
            apply Hx; [exact Hb | exact Hbcin |] end.
          destruct ex as [ | | sh eb en ec e1 elen]; cbn; auto.
          destruct Lds as (_ & _ & _ & _ & gp & Hdd). apply (Hdg _ _ _ _ Hdd). }
        apply blk_mid_comp; auto.
        all: try (intros Er; match goal with Hx: is_error_code _ = false -> _ /\ _ /\ _ /\ _ /\ (hist_def _ _ _ _ -> _) |- _ =>
                    destruct (Hx Er) as (Q1 & Q2 & Q3 & Q4 & Q5); split; [exact Q1 |]; split; [exact Q2 |];
                    split; [exact Q3 |]; split;
                    [intros Hrb; exact (comp_hist_bytes _ _ _ _ _ _ _ _ Hhd Hwb Q5) |];
                    intros Hrb; exact (Q4 eq_refl Hrb) end).
        all: try (destruct Hbsm; lia).
        all: try (match goal with Hc: ?c = fs_ddictIsCold _ \/ _ |- _ => exact Hc end).
        all: try (intros Hp; unfold hist_pre in Hp; rewrite Ez in Hp; specialize (Hp Et Hc0); rewrite El in Hp;
                  destruct Hp as (_ & _ & _ & Hv & Hx); rewrite <- EH in Hv, Hx;
                  match goal with Hb: _ \/ _ -> _ -> _ -> block_ok _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
                    apply Hb; [right; split; auto | exact HHb | exact Bo] end).
        all: intros Er; match goal with Hx: is_error_code _ = true -> _ /\ dec_err _ |- _ => apply dec_nfp, (Hx Er) end.
      * (* cap = 0: an empty window at dst, the array lent to W *)
        assert (Hc00: oa_cap o = 0) by lia.
        assert (HHb: bytes_ok (lay_H z l o)) by (apply (lay_H_bytes z l dd o Hdg); [exact Ld1 | exact Dm]).
        assert_PROP (bytes_ok (ts_lxb ts)) as Hlxb
          by (sep_apply (HT gv p (dd_ox dd) ts); unfold tables_uninit, lit_extra_at; entailer!).
        rewrite <- (ext0_res l o) by (rewrite Eb; exact I).
        assert_PROP (ext_ptr (ext0 l o)) as Hep by (sep_apply (ext_res_ptr (ext0 l o)); entailer!).
        rewrite (out_split o) by auto. Intros.
        sep_apply (pws_app_fold W (side_W o)).
        forward_call (gv, p, fsc, dd_ox dd, ts, zp_bsm z, 1, W ++ side_W o, mid_o o, i,
          {| hc_ext := ext0 l o; hc_ps := 0; hc_hist := lay_H z l o; hc_out := zp_out z; hc_wsize := fh_windowSize (zp_h z) |}).
        { cbn [hc_ext]. unfold fsc. ff_unfold. cancel. }
        { assert (Hh: hist_ptrs_ok fs1 (mid_o o) (ext0 l o)) by (apply (hpo_zero fs1 l dd o); auto).
          assert (Hh0: ext0_ok (W ++ side_W o) fs1 (ext0 l o)) by (apply (ext0_ok_zero fs1 l dd o W); auto).
          (* the empty window's history: the extDict only *)
          assert (Hhd0: hist_def (oa_c (mid_o o)) (oa_d (mid_o o)) 0 (ext0 l o)).
          { replace (oa_c (mid_o o)) with (@nil val) by (cbn; rewrite Hc00, Z.add_0_r, sublist_nil; reflexivity).
            exact (hist_def_ext0 l o dd Hdg Ld). }
          unfold fsc. ff_unfold.
          destruct Hcf1 as (I1 & I2 & _).
          repeat (first [exact Hh | exact Hh0 | exact Hhd0 | split]); auto; try (apply mid_ok; auto); try (cbn [mid_o oa_cap]; lia);
            try (cbn [hc_ext]; destruct (ext0 l o); auto; fail).
          try intros _. cbn [oa_d oa_base mid_o]. rewrite isptr_offset_val_zero by (rewrite Eb; exact I).
          apply mid_wvp; auto. }
        Intros vret. destruct vret as [[[r ocm] cold] tso]; cbn [fst snd hc_ext hc_ps hc_hist hc_out hc_wsize] in *.
        match goal with Hx: dd_ox dd = None -> block_exact _ _ _ _ _ _ _ _ _ |- _ => rename Hx into Hbx end.
        rewrite Ets' in *.
        match goal with Hx: Zlength ocm = oa_N (mid_o o) |- _ => rename Hx into Locm end.
        assert (Eocm: ocm = oa_c (mid_o o)).
        { cbn [mid_o oa_N oa_c] in *. rewrite Hc00, Z.add_0_r, sublist_nil. rewrite Hc00 in Locm.
          destruct ocm; auto. rewrite Zlength_cons in Locm. pose proof (Zlength_nonneg ocm). lia. }
        subst ocm.
        sep_apply (pws_app_unfold W (side_W o)). Intros.
        change (oa_sh (mid_o o)) with (oa_sh o). change (oa_N (mid_o o)) with (oa_cap o).
        change (oa_base (mid_o o)) with (offset_val (oa_d o) (oa_base o)).
        sep_apply (out_unsplit o); auto.
        rewrite (ext0_res l o) by (rewrite Eb; exact I). unfold fs_set_cold, fsc. ff_unfold. Intros.
        forward. forward.
        Exists r (oa_c o) tso cold 0. unfold blk_sep. entailer!.
        split.
        { intros Hox. assert (El0: l1 = l) by (unfold l1, lmove; rewrite Hc00; reflexivity). rewrite El0 in Lf1, Ld1.
          eapply (bres_comp0 fs1 ts o (iw_s i) _ st (zp_h z) (zp_bsm z) Est1 Hst34 ltac:(rewrite Pbt, Et; reflexivity) HoX Fp ltac:(rep_lia) Hbsm Ck Hbi Hlxb r (oa_c (mid_o o)) tso i
                   {| hc_ext := ext0 l o; hc_ps := 0; hc_hist := lay_H z l o; hc_out := zp_out z;
                      hc_wsize := fh_windowSize (zp_h z) |} (mid_o o) b ofs Hc00 Eb
                   (ext0_exact fs1 l dd o b ofs Hox Lf1 Ld1 H4 Eb HN32) eq_refl eq_refl Hc00 ltac:(cbn; lia) eq_refl
                   (Hbx Hox)). }
        match goal with Hb: _ \/ _ -> _ -> _ -> block_ok _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rename Hb into Hbk end.
        assert (Emid: oa_c (mid_o o) = []) by (cbn; rewrite Hc00, Z.add_0_r, sublist_nil; auto).
        assert (Hbk': block_ok (zp_ts z) (lay_H z l o) (zp_out z) (iw_s i) (zp_bsm z)
                  (fh_windowSize (zp_h z)) 1 [] [] 0 0 r (option_map ts_d tso)).
        { assert (Hcm: oa_cap (mid_o o) = 0) by (cbn; lia).
          pose proof (Hbk (or_introl Hcm) HHb Bo) as Hb2. rewrite Emid in Hb2. cbn [mid_o oa_d oa_cap] in Hb2.
          rewrite Hc00 in Hb2. exact Hb2. }
        eapply blk_mid_comp0; eauto.
        all: try (destruct Hbsm; lia).
        all: try (match goal with Hc: ?c = fs_ddictIsCold _ \/ _ |- _ => exact Hc end).
        intros Er. match goal with Hok: is_error_code r = false -> _ |- _ => destruct (Hok Er) as (Hr0 & Hcd & Hts & _) end.
        cbn [mid_o oa_cap] in Hr0. split; [lia | auto].
        all: intros Er; match goal with Hx: is_error_code _ = true -> _ /\ dec_err _ |- _ => apply dec_nfp, (Hx Er) end.
    + (* raw *)
      match goal with E: bp_type (block_props_of bh) = 0 |- _ => rename E into Et end.
      destruct H1 as (cc & Ecc & Hn). inv Ecc. rewrite Et in Hn. cbn in Hn.
      pose proof Hiw as (Rs & Ho & Hon & HNi & Hci & Hsi & Hbi & Hwi).
      assert (Hoo: outarr_ok o) by (split; [exact Hsh |]; repeat split; auto; lia).
      rewrite (out_split o) by auto. Intros.
      sep_apply (pws_app_fold W (side_W o)).
      forward_call (W ++ side_W o, mid_o o, i).
      { split; [apply mid_ok; auto |]. try split; try exact Hiw.
        intros Hc0. cbn [oa_d oa_base mid_o]. rewrite isptr_offset_val_zero by (rewrite Eb; exact I).
        apply mid_wvp; auto. }
      Intros vret. destruct vret as [r ocm]; cbn [fst snd] in *.
      match goal with Hx: if _ >? _ then _ else _ |- _ => rename Hx into Hraw end.
      match goal with Hx: 0 <= r <= Int64.max_unsigned |- _ => rename Hx into Hr end.
      sep_apply (pws_app_unfold W (side_W o)). Intros.
      match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
        forward_loop (PROPx P (LOCALx Q (SEPx R)))
          break: (PROPx ((is_error_code r = false) :: P) (LOCALx Q (SEPx R))) end.
      { entailer!. }
      { forward. forward_call r. forward_if.
        - dw0. dw0. dw0. dw0. forward.
          assert (Er: is_error_code r = true) by (destruct (is_error_code r); auto; contradiction).
          destruct (Zlength (iw_s i) >? oa_cap (mid_o o)) eqn:Eg.
          2: { exfalso. destruct Hraw as [-> _]. unfold is_error_code in Er. apply Z.ltb_lt in Er. rep_lia. }
          destruct Hraw as [Hde ->]. apply tooSmall_dec in Hde.
          change (oa_sh (mid_o o)) with (oa_sh o). change (oa_N (mid_o o)) with (oa_cap o).
          change (oa_base (mid_o o)) with (offset_val (oa_d o) (oa_base o)).
          sep_apply (out_unsplit o); auto.
          Exists r (oa_c o) (fsu_processedCSize fs1 (Vlong (Int64.repr (pcs + Zlength (iw_s i))))) (Some ts).
          ff_unfold. rewrite Pbt, Est1. unfold in_res; cbn [is_skip]. rewrite conj_rot5. entailer!.
          split.
          { apply HXP. intros Hox.
            eapply (cx_tail_err fs1 ts o (iw_s i) _ (zp_h z) (zp_bsm z) st Est1 Hst34 Fp ltac:(rep_lia) Hbsm Ck HoX r (oa_c o) (Some ts) 0 r _ _ _
                     (bres_raw fs1 ts o (iw_s i) _ st (bp_type (block_props_of bh)) Est1 Hst34 Pbt (bp_type_range bh) HoX r (oa_c o) (Some ts) 0 (cc - Zlength (zp_got z)) Et
                        ltac:(rewrite Pex, Et; reflexivity) ltac:(pose proof (Zlength_nonneg (zp_got z)); rep_lia)
                        eq_refl Hbi ltac:(cbn [mid_o oa_cap] in Eg; rewrite Eg; exact Er))
                     Er eq_refl). }
          split; [auto |]. split; [auto |]. split; [intros j _ _; auto |]. split; [intros X; exact X |]. rewrite Er.
          split; [| apply dec_nfp; exact Hde].
          intros _. cbn [cont_err]. rewrite Ez, Et. simpl. left. cbn [mid_o oa_cap] in Eg. lia.
        - forward. entailer!. destruct (is_error_code r); auto.
          exfalso. match goal with Hz: Int.repr 1 = Int.zero |- _ => exact (Int.one_not_zero Hz) end. }
      Intros. rename H into Ner.
      destruct (Zlength (iw_s i) >? oa_cap (mid_o o)) eqn:Eg.
      { exfalso. destruct Hraw as [Er _]. apply tooSmall_dec in Er. destruct Er as [Er _]. congruence. }
      destruct Hraw as [-> ->]. cbn [mid_o oa_cap oa_d oa_c] in Eg |- *.
      rewrite Pex, Et. simpl Z.eqb. cbv iota.
      forward. forward. forward.
      Exists (Zlength (iw_s i)) (put_bytes (oa_c o) (oa_d o) (iw_s i)) (Some ts) (fs_ddictIsCold fs1)
        (cc - Zlength (zp_got z) - Zlength (iw_s i)).
      unfold blk_sep. rewrite Et, sub64_repr.
      change (oa_sh (mid_o o)) with (oa_sh o). change (oa_N (mid_o o)) with (oa_cap o).
      change (oa_base (mid_o o)) with (offset_val (oa_d o) (oa_base o)).
      change (sublist (oa_d o) (oa_d o + oa_cap o) (oa_c o)) with (oa_c (mid_o o)).
      sep_apply (out_join o (iw_s i)); auto; try lia.
      entailer!.
      split.
      { intros _. eapply (bres_raw fs1 ts o (iw_s i) _ st (bp_type (block_props_of bh)) Est1 Hst34 Pbt (bp_type_range bh) HoX _ _ _ _ (cc - Zlength (zp_got z)) Et
                   ltac:(rewrite Pex, Et; reflexivity) ltac:(pose proof (Zlength_nonneg (zp_got z)); rep_lia) eq_refl Hbi).
        rewrite Eg. split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |]. lia. }
      apply blk_mid_raw; auto; try lia.
    + (* RLE *)
      match goal with E: bp_type (block_props_of bh) = 1 |- _ => rename E into Et end.
      destruct H1 as (cc & Ecc & Hn). inv Ecc. rewrite Et in Hn. cbn in Hn. destruct Hn as [Hg0 Hn].
      pose proof Hiw as (Rs & Ho & Hon & HNi & Hci & Hsi & Hbi & Hwi).
      assert (Hoo: outarr_ok o) by (split; [exact Hsh |]; repeat split; auto; lia).
      assert_PROP (field_compatible (tarray tuchar (iw_N i)) [] (iw_base i)) as Fci by entailer!.
      rewrite (arr_split (iw_sh i) (iw_N i) (iw_c i) (iw_base i) (iw_off i) (iw_s i)) by (auto; lia).
      Intros.
      assert (Hu1: 1 <= Zlength (iw_s i)) by lia.
      set (q := offset_val (iw_off i) (iw_base i)).
      set (u := iw_s i) in *.
      assert_PROP (field_compatible (tarray tuchar (Zlength u)) [] q) as Fcq by entailer!.
      assert (Hs1: data_at (iw_sh i) (tarray tuchar (Zlength u)) (zbytes u) q =
         (data_at (iw_sh i) tuchar (Vint (Int.repr (Znth 0 u))) q *
          data_at (iw_sh i) (Tarray tuchar (Zlength u - 1) noattr) (sublist 1 (Zlength u) (zbytes u))
            (field_address0 (Tarray tuchar (Zlength u) noattr) (SUB 1) q))%logic).
      { unfold tarray. rewrite (split2_data_at_Tarray_tuchar (iw_sh i) (Zlength u) 1) by (try rewrite Zlength_map; lia).
        f_equal. apply (data_at_singleton_array_eq (iw_sh i) tuchar).
        rewrite sublist_one by (rewrite ?Zlength_map; lia). rewrite Znth_map by lia. reflexivity. }
      assert (Hb0: 0 <= Znth 0 u <= Byte.max_unsigned).
      { unfold bytes_ok in Hbi. pose proof (proj1 (Forall_Znth _ _) Hbi 0 ltac:(lia)) as Hz. unfold is_byte in Hz.
        rep_lia. }
      rewrite Hs1. Intros.
      forward.
      { entailer!. simpl. try rewrite Int.unsigned_repr by rep_lia. rep_lia. }
      rewrite Prle. forward.
      pose proof (bp_last01 bh) as _.
      assert (Hos: 0 <= bp_origSize (block_props_of bh) < 2 ^ 21).
      { unfold block_props_of; cbn [bp_origSize]. pose proof (lef_range bh 0 3 Bbh ltac:(lia)).
        rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia |].
        apply Z.div_lt_upper_bound; [lia |]. change (2 ^ 3 * 2 ^ 21) with (2 ^ (8 * 3)). lia. }
      rewrite (out_split o) by auto. Intros.
      sep_apply (pws_app_fold W (side_W o)).
      forward_call (W ++ side_W o, mid_o o, Znth 0 u, bp_origSize (block_props_of bh)).
      { split; [apply mid_ok; auto |].
        intros Hc0. cbn [oa_d oa_base mid_o]. rewrite isptr_offset_val_zero by (rewrite Eb; exact I).
        apply mid_wvp; auto. }
      Intros vret. destruct vret as [r ocm]; cbn [fst snd] in *.
      match goal with Hx: if _ >? _ then _ else _ |- _ => rename Hx into Hrle end.
      match goal with Hx: 0 <= r <= Int64.max_unsigned |- _ => rename Hx into Hr end.
      sep_apply (pws_app_unfold W (side_W o)). Intros.
      assert (Hj1: data_at (iw_sh i) tuchar (Vint (Int.repr (Znth 0 u))) q *
          data_at (iw_sh i) (Tarray tuchar (Zlength u - 1) noattr) (sublist 1 (Zlength u) (zbytes u))
            (field_address0 (Tarray tuchar (Zlength u) noattr) (SUB 1) q)
          |-- data_at (iw_sh i) (tarray tuchar (Zlength u)) (zbytes u) q) by (rewrite Hs1; apply derives_refl).
      sep_apply Hj1.
      sep_apply (arr_join (iw_sh i) (iw_N i) (iw_c i) (iw_base i) (iw_off i) u); auto; try lia.
      change (oa_sh (mid_o o)) with (oa_sh o). change (oa_N (mid_o o)) with (oa_cap o).
      change (oa_base (mid_o o)) with (offset_val (oa_d o) (oa_base o)).
      destruct (bp_origSize (block_props_of bh) >? oa_cap (mid_o o)) eqn:Eg.
      { destruct Hrle as [Hde ->]. apply tooSmall_dec in Hde. pose proof (proj1 Hde) as Er. sep_apply (out_unsplit o); auto.
        forward. forward. forward.
        Exists r (oa_c o) (Some ts) (fs_ddictIsCold fs1) 0.
        unfold blk_sep. rewrite Prle. entailer!.
        split.
        { intros _. eapply (bres_rle fs1 ts o u _ st (bp_type (block_props_of bh)) Est1 Hst34 Pbt (bp_type_range bh) HoX _ _ _ _ _ Et Prle ltac:(rep_lia) ltac:(lia) Hbi).
          cbn [mid_o oa_cap] in Eg. rewrite Eg. exact Er. }
        apply blk_mid_err; auto; try rep_lia.
        all: try (intros _; cbn [cont_err]; rewrite Ez, Et; simpl; left; cbn [mid_o oa_cap] in Eg;
                  apply Z.gtb_lt in Eg; apply Z.lt_gt; exact Eg).
        all: destruct (dec_nfp r Hde) as [N1 N2]; auto. }
      destruct Hrle as [-> ->]. cbn [mid_o oa_cap oa_d oa_c] in Eg |- *.
      change (sublist (oa_d o) (oa_d o + oa_cap o) (oa_c o)) with (oa_c (mid_o o)).
      sep_apply (out_join o (Zrepeat (Znth 0 u) (bp_origSize (block_props_of bh)))); auto;
        try (rewrite Zlength_Zrepeat; lia).
      forward. forward. forward.
      Exists (bp_origSize (block_props_of bh))
        (put_bytes (oa_c o) (oa_d o) (Zrepeat (Znth 0 u) (bp_origSize (block_props_of bh))))
        (Some ts) (fs_ddictIsCold fs1) 0.
      unfold blk_sep. rewrite Prle. entailer!.
      split.
      { intros _. eapply (bres_rle fs1 ts o u _ st (bp_type (block_props_of bh)) Est1 Hst34 Pbt (bp_type_range bh) HoX _ _ _ _ _ Et Prle ltac:(rep_lia) ltac:(lia) Hbi).
        rewrite Eg. split; [reflexivity |]. split; [reflexivity |]. split; reflexivity. }
      apply blk_mid_rle; auto; try lia.
    + (* reserved *)
      exfalso.
      repeat match goal with Hx: Int.unsigned (Int.repr _) <> Int.unsigned (Int.repr _) |- _ =>
        rewrite !Int.unsigned_repr in Hx by rep_lia; revert Hx end.
      intros. lia.
    + (* after the block decoder (the abbreviations unfolded and the lemma's arguments given: a bare eapply's
         unification does not finish) *)
      change Delta with (func_tycontext f_ZSTD_decompressContinue Vprog (stream_G3 DENT TABS BR) nil).
      change MORE_COMMANDS with blk_tail.
      change POSTCONDITION with
        (switch_ret_assert (dcc_R DENT TABS gv p f (FP_zstd hdr z) l dd W o i (fs_ddictIsCold fs1) (fs_fParams fs1) XP)).
      eapply (blk_tail_ok Espec DENT TABS BR HD HT Hsg gv p f dd fs1 ts hdr z l W o src i n v_bp pcs st b ofs bh c')
        with (XP := XP); eassumption.
Qed.

End CM_C3Blk_1.
