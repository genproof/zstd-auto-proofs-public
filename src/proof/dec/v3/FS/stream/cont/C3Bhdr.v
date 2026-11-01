(* FS3 streaming: ZSTD_decompressContinue, the block header stage (port of v2
   body_stream_continue.v bhdr_case_ok). *)
Require Import Zstd.proof.dec.v3.FS.stream.S3Specs.
Require Import Zstd.proof.dec.v3.FS.stream.cont.C3Base.
Require Import Zstd.proof.dec.v3.FS.stream.cont.C3Mid.
Require Import Zstd.proof.zstd.XxhLemmas.
Require Import Zstd.proof.dec.v3.FS.stream.cont.C3XDefs.
Require Import Zstd.proof.dec.v3.FS.stream.cont.C3XHdr.

Section CM_C3Bhdr_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma bhdr_case_ok (Espec: OracleKind) DENT TABS BR (HD: DENT_OK DENT) (HT: TABS_OK TABS)
    gv p (f: Z) (dd: option (ddx * val)) (fs1: fstate) ts fp l W (o: outarr) src (i: inwin) n v_bp pcs b ofs
    (cold0: val) (fpar0: reptype t_fh) (XP: Z -> list val -> fstate -> option tstate -> Prop) :
  fp_complete fp = false -> unit_ok fp n -> 0 <= n <= Int64.max_unsigned ->
  writable_share (oa_sh o) -> Zlength (oa_c o) = oa_N o -> oa_N o <= 2 ^ 63 - 1 -> 0 <= oa_d o -> 0 <= oa_cap o ->
  oa_d o + oa_cap o <= oa_N o -> lay_at l o -> (is_skip fp = true -> oa_cap o = 0) ->
  (is_skip fp = false -> src = offset_val (iw_off i) (iw_base i) /\ inwin_ok i /\ Zlength (iw_s i) = n /\
     byte_cells (iw_c i)) ->
  (oa_N o = 0 -> (pws_pred W |-- weak_valid_pointer (oa_base o))) ->
  field_compatible (tarray tuchar (oa_N o)) [] (oa_base o) ->
  oa_base o = Vptr b ofs -> Ptrofs.unsigned ofs + oa_N o < Ptrofs.modulus ->
  c_frame fs1 (TInit (dd_ox dd) ts) fp (lmove l (oa_base o) (oa_d o) (oa_cap o)) dd ->
  fs_stage fs1 = Vint (Int.repr 2) -> fs_processedCSize fs1 = Vlong (Int64.repr pcs) ->
  fs_ddictIsCold fs1 = cold0 -> fs_fParams fs1 = fpar0 ->
  (* the exact claim (C3XDefs.cont_exact1) gives the caller's *)
  (forall r oc' fs' tabs', (dd_ox dd = None -> cont_exact1 fs1 ts o (iw_s i) n r oc' fs' tabs') -> XP r oc' fs' tabs') ->
  semax (func_tycontext f_ZSTD_decompressContinue Vprog (stream_G3 DENT TABS BR) nil)
    (blk_pre DENT TABS gv p f dd l fs1 ts fp W o src i n v_bp pcs 2) bhdr_cmd
    (switch_ret_assert (dcc_R DENT TABS gv p f fp l dd W o i cold0 fpar0 XP)).
Proof.
  intros H0 H1 H2 Hsh HcN HN32 Hd Hcap Hdc H4 H5 H6 H7 H8 Eb HN Hcf1 Est1 Ep1 Ecold0 Efpar0 HXP. subst cold0 fpar0.
  set (l1 := lmove l (oa_base o) (oa_d o) (oa_cap o)) in *.
  unfold blk_pre, bhdr_cmd, dcc_R. simplify_func_tycontext. abbreviate_semax.
  pose proof (stage_inv _ _ _ _ _ _ Hcf1 H0 Est1 ltac:(lia)) as Hfp.
  destruct fp as [ | | hdr got | hdr z]; try contradiction.
  { unfold ds_skipFrame in Hfp; lia. }
  destruct (zp_ph z) as [ | bh | | ] eqn:Ez; try contradiction;
    unfold ds_decodeBlockHeader, ds_checkChecksum, ds_decompressLastBlock, ds_decompressBlock in Hfp;
    try (destruct (_ =? 1) in Hfp); try lia.
  pose proof Hcf1 as Hc1. destruct Hc1 as (_ & _ & _ & Lf1 & Ld1 & M1).
  destruct M1 as (T0 & Fp & B1 & B2 & W1 & W2 & Fc & Ck & Dm & Ets & Ph & Ed & Vc & Ex & Bo & Mz & Bg).
  assert (Bm: zp_bsm z <= ZSTD_BLOCKSIZE_MAX) by (rewrite B2 in B1; lia).
  rewrite Ez in Mz. unfold phase_fields in Ph. rewrite Ez in Ph.
  cbn [unit_ok] in H1. rewrite Ez in H1. destruct H1 as [Hg0 Hn3]. subst n.
  destruct (H6 eq_refl) as (Hsrc & Hiw & Hlen & Hbcin).
  destruct Ets as (ts0 & Ets & Ets'). injection Ets as Ets. subst ts0.
  unfold in_res; cbn [is_skip].
  unfold zstd_globals. Intros.
  forward.
  sep_apply (zstd_globals_fold gv).
  forward_call (gv, Tsh, v_bp, iw_sh i, iw_base i, iw_N i, iw_c i, iw_off i, iw_s i).
  { rewrite Hsrc, Hlen. unfold ZSTD_blockHeaderSize_val, ZSTD_blockHeaderSize. entailer!. }
  Intros vret. destruct vret as [r v]; cbn [fst snd] in *.
  match goal with Hm: match cblock_size _ with Some _ => _ | None => _ end |- _ => rename Hm into Hcb end.
  match goal with Hm: 0 <= r <= Int64.max_unsigned |- _ => rename Hm into Hr end.
  forward.
  forward_call r.
  forward_if.
  { (* getcBlockSize failed *)
    forward.
    sep_apply (data_at_data_at_ Tsh t_bp v v_bp).
    Exists r (oa_c o) (fsu_processedCSize fs1 (Vlong (Int64.repr (pcs + ZSTD_blockHeaderSize)))) (Some ts).
    ff_unfold. rewrite Est1. try rewrite add64_repr.
    rewrite conj_rot5. entailer!.
    assert (Er: is_error_code r = true) by (destruct (is_error_code r); auto; contradiction).
    split; [apply HXP; intros _; apply (cx_bhdr_bad fs1 ts o (iw_s i) _ (zp_h z) (zp_bsm z) Est1 Fp ltac:(rep_lia) ltac:(rep_lia) Ck); [| exact Er];
      destruct (cblock_size (iw_s i)) as [k |] eqn:Ek; [exfalso | reflexivity]; destruct Hcb as [-> _];
      destruct Hiw as (_ & _ & _ & _ & _ & _ & Hbi' & _);
      rewrite is_error_small in Er by (eapply cblock_size_range; eauto); discriminate |].
    split; [auto |]. split; [auto |]. split; [intros j _ _; auto |]. split; [intros X; exact X |]. rewrite Er.
    cbn [cont_err]. rewrite Ez.
    destruct (cblock_size (iw_s i)) as [k |] eqn:Ek; [| split; [intros _; exact I | apply dec_nfp; exact Hcb]].
    exfalso. destruct Hcb as [-> _]. destruct Hiw as (_ & _ & _ & _ & _ & _ & Hbi & _).
    rewrite is_error_small in Er by (eapply cblock_size_range; eauto). discriminate. }
  assert (Ner: is_error_code r = false).
  { destruct (is_error_code r); [| reflexivity]. exfalso.
    match goal with Hz: Int.repr 1 = Int.zero |- _ => exact (Int.one_not_zero Hz) end. }
  destruct (cblock_size (iw_s i)) as [c |] eqn:Ec; [| destruct Hcb as [Hcb _]; rewrite Hcb in Ner; discriminate].
  destruct Hcb as [-> ->].
  destruct Hiw as (Rs & Ho & Hon & HNi & Hci & Hsi & Hbi & Hwi).
  pose proof (cblock_size_range _ _ Hbi Ec) as Hcr.
  rewrite Fp. unfold fh_val, fh_adj; cbn [fh_contentSize fh_windowSize fh_blockSizeMax fh_frameType
    fh_headerSize fh_dictID fh_checksumFlag].
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_loop (PROPx P (LOCALx Q (SEPx R)))
      break: (PROPx ((c <= zp_bsm z) :: P) (LOCALx Q (SEPx R))) end.
  { entailer!. }
  { forward.
    forward_if.
    - dw0. dw0. dw0. dw0. forward.
      sep_apply (data_at_data_at_ Tsh t_bp (bp_val (block_props_of (iw_s i))) v_bp).
      Exists (2 ^ 64 - 20) (oa_c o) (fsu_processedCSize fs1 (Vlong (Int64.repr (pcs + ZSTD_blockHeaderSize))))
        (Some ts).
      ff_unfold. rewrite Est1, Fp. try rewrite add64_repr. try rewrite <- repr_neg64.
      rewrite conj_rot5. entailer!.
      split; [apply HXP; intros _; apply (cx_bhdr_big fs1 ts o (iw_s i) _ (zp_h z) (zp_bsm z) Est1 Fp ltac:(rep_lia) ltac:(rep_lia) Ck _ _ _ _ c); [exact Ec | | reflexivity];
        match goal with Hx: Int.unsigned (Int.repr (zp_bsm z)) < c |- _ =>
          rewrite Int.unsigned_repr in Hx by rep_lia; exact Hx end |].
      unfold ZSTD_BLOCKSIZE_MAX in Bm.
      match goal with Hx: Int.unsigned (Int.repr (zp_bsm z)) < c |- _ =>
        rewrite Int.unsigned_repr in Hx by rep_lia end.
      split; [rep_lia |]. split; [auto |]. split; [intros j _ _; auto |]. split; [intros X; exact X |].
      replace (is_error_code (2 ^ 64 - 20)) with true by reflexivity.
      split; [intros _; cbn [cont_err]; rewrite Ez, Ec; left; lia | apply nfp_ne; lia].
    - forward. entailer!.
      unfold ZSTD_BLOCKSIZE_MAX in Bm.
      match goal with Hx: context [Int.unsigned (Int.repr (zp_bsm z))] |- _ =>
        rewrite Int.unsigned_repr in Hx by rep_lia end.
      lia. }
  Intros.
  forward.
  unfold bp_val. forward. forward. forward. forward.
  pose proof (bp_last01 (iw_s i)) as Hl01.
  forward_if.
  { forward.
    fif_set _t'9 (Vint (Int.repr (if bp_last (block_props_of (iw_s i)) =? 1 then 4 else 3))).
    { forward. entailer!.
      change (Z.land (le_field (iw_s i) 0 3) 1) with (bp_last (block_props_of (iw_s i))) in *.
      destruct Hl01 as [E | E]; rewrite E in *; [contradiction | reflexivity]. }
    { forward. entailer!.
      change (Z.land (le_field (iw_s i) 0 3) 1) with (bp_last (block_props_of (iw_s i))) in *.
      destruct Hl01 as [E | E]; rewrite E in *; [reflexivity |].
      exfalso. match goal with Hz: Int.repr 1 = Int.zero |- _ => exact (Int.one_not_zero Hz) end. }
    forward. forward.
    sep_apply (data_at_data_at_ Tsh t_bp (bp_val (block_props_of (iw_s i))) v_bp).
      Exists 0 (oa_c o) (fsu_stage (fsu_expected (fsu_rleSize (fsu_bType (fsu_expected
        (fsu_processedCSize fs1 (Vlong (Int64.repr (pcs + ZSTD_blockHeaderSize)))) (Vlong (Int64.repr c)))
        (Vint (Int.repr (Z.land (Z.shiftr (le_field (iw_s i) 0 3) 1) 3))))
        (Vlong (Int64.repr (Int.unsigned (Int.repr (Z.shiftr (le_field (iw_s i) 0 3) 3)))))) (Vlong (Int64.repr c))) (Vint (Int.repr (if bp_last (block_props_of (iw_s i)) =? 1 then 4 else 3)))) (Some ts).
      ff_unfold. try rewrite add64_repr.
      rewrite conj_rot5. entailer!.
      all: try (rewrite Fp; apply derives_refl).
      split; [apply HXP; intros _; apply (cx_bhdr_ok fs1 ts o (iw_s i) _ (zp_h z) (zp_bsm z) Est1 Fp ltac:(rep_lia) ltac:(rep_lia) Ck c (if bp_last (block_props_of (iw_s i)) =? 1 then 4 else 3) c);
        [exact Ec | assumption | exact Hbi | repeat split; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | | | ];
        [intros; split; reflexivity
        | intros E; subst c; exfalso; match goal with Hx: Int64.repr 0 <> Int64.zero |- _ => apply Hx; reflexivity end ..] |].
      assert (Hc0: c <> 0).
      { intros ->. match goal with Hx: Int64.repr 0 <> Int64.zero |- _ => apply Hx; reflexivity end. }
      assert (Hf6: c = 0 -> bp_last (block_props_of (iw_s i)) = 1 -> fcs_okm (zp_h z) (zp_out z))
        by (intros E; contradiction).
      eapply cont_res_bhdr with (fs1 := fs1) (c := c); eauto; try reflexivity; try lia.
      all: try (eexists; reflexivity).
      assert (Hos: 0 <= Z.shiftr (le_field (iw_s i) 0 3) 3 < 2 ^ 21).
      { pose proof (lef_range (iw_s i) 0 3 Hbi ltac:(lia)). rewrite Z.shiftr_div_pow2 by lia.
        split; [apply Z.div_pos; lia |]. apply Z.div_lt_upper_bound; [lia |].
        change (2 ^ 3 * 2 ^ 21) with (2 ^ (8 * 3)). lia. }
      unfold zstep, phase_fields. rewrite Ez, Ec. replace (c =? 0) with false by (symmetry; apply Z.eqb_neq; auto).
      cbn [zp_with zp_ph zp_got]. exists c. split; [auto |].
      split; [unfold ds_decompressLastBlock, ds_decompressBlock; destruct (_ =? 1); reflexivity |].
      split; [reflexivity |].
      split; [rewrite Int.unsigned_repr by rep_lia; reflexivity |].
      unfold fsu_stage, fsu_expected; cbn [fs_expected]. rewrite Zlength_nil.
      destruct (bp_type _ =? 0); do 2 f_equal; lia. }
  assert (c = 0) as ->.
  { match goal with Hx: Int64.repr c = Int64.zero |- _ =>
      apply (f_equal Int64.unsigned) in Hx; rewrite Int64.unsigned_repr in Hx by rep_lia; exact Hx end. }
  forward. apply semax_if_seq. forward_if.
  { (* last block *)
    assert (El: bp_last (block_props_of (iw_s i)) = 1).
    { change (Z.land (le_field (iw_s i) 0 3) 1) with (bp_last (block_props_of (iw_s i))) in *. destruct Hl01 as [E | E]; auto. rewrite E in *. contradiction. }
    (* the end of the frame: the content size check (an error when the frame declares another size) *)
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_loop (PROPx P (LOCALx Q (SEPx R)))
        break: (PROPx ((fh_contentSize (zp_h z) = ZSTD_CONTENTSIZE_UNKNOWN \/
                        Zlength (zp_out z) mod 2 ^ 64 = fh_contentSize (zp_h z)) :: P)
                  (LOCALx Q (SEPx R))) end.
    { entailer!. }
    { rewrite Ed. forward. fif_set _t'10 (Vint (Int.repr (fcs_t15 (fh_contentSize (zp_h z)) (Zlength (zp_out z))))).
      - forward. forward. forward. entailer!. apply fcs_then; auto.
      - forward. entailer!.
        match goal with Hx: Int64.eq _ _ = true |- _ => apply Int64.same_if_eq in Hx; rewrite fcs_else; auto end.
      - assert (F01: fcs_t15 (fh_contentSize (zp_h z)) (Zlength (zp_out z)) = 0 \/
                     fcs_t15 (fh_contentSize (zp_h z)) (Zlength (zp_out z)) = 1)
          by (unfold fcs_t15; repeat destruct (_ =? _); auto).
        forward_if.
        + dw0. dw0. dw0. dw0. forward.
          assert (F1: fcs_t15 (fh_contentSize (zp_h z)) (Zlength (zp_out z)) = 1).
          { destruct F01 as [E | E]; auto. rewrite E in *. contradiction. }
          destruct (fcs_bad_of (Zlength (zp_out z)) (fh_contentSize (zp_h z)) Fc ltac:(lia)) as [Q1 Q2].
          sep_apply (data_at_data_at_ Tsh t_bp (bp_val (block_props_of (iw_s i))) v_bp).
          Exists (2 ^ 64 - 20) (oa_c o) (fsu_rleSize (fsu_bType (fsu_expected
            (fsu_processedCSize fs1 (Vlong (Int64.repr (pcs + ZSTD_blockHeaderSize)))) (Vlong (Int64.repr 0)))
            (Vint (Int.repr (Z.land (Z.shiftr (le_field (iw_s i) 0 3) 1) 3))))
            (Vlong (Int64.repr (Int.unsigned (Int.repr (Z.shiftr (le_field (iw_s i) 0 3) 3)))))) (Some ts).
          ff_unfold. rewrite Est1, Fp, Ed. try rewrite add64_repr. try rewrite <- repr_neg64.
          rewrite conj_rot5. entailer!.
          split; [apply HXP; intros _;
            unfold fcs_t15 in F1; destruct (_ =? _) eqn:E1 in F1; [discriminate |];
            destruct (_ =? _) eqn:E2 in F1; [discriminate |]; apply Z.eqb_neq in E1, E2;
            apply (cx_bhdr_fcs fs1 ts o (iw_s i) _ (zp_h z) (zp_bsm z) Est1 Fp ltac:(rep_lia) ltac:(rep_lia) Ck _ _ _ _ (Zlength (zp_out z))); auto |].
          split; [rep_lia |]. split; [auto |]. split; [intros j _ _; auto |]. split; [intros X; exact X |].
          replace (is_error_code (2 ^ 64 - 20)) with true by reflexivity.
          split; [| apply nfp_ne; lia].
          intros _. cbn [cont_err]. rewrite Ez, Ec. right. split; [reflexivity |]. split; [exact El |].
          unfold fcs_bad, ZSTD_CONTENTSIZE_UNKNOWN. auto.
        + forward. entailer!.
          { destruct F01 as [E | E];
              [apply fcs_ok_of in E; unfold ZSTD_CONTENTSIZE_UNKNOWN; tauto
              | rewrite E in *; exfalso; match goal with Hz: Int.repr 1 = Int.zero |- _ => exact (Int.one_not_zero Hz) end]. }
          rewrite Ed. apply derives_refl. }
    Intros.
    (* the F6 check passed: what cont_checks requires of an empty last block *)
    assert (Hf6: 0 = 0 -> bp_last (block_props_of (iw_s i)) = 1 -> fcs_okm (zp_h z) (zp_out z))
      by (intros _ _; unfold fcs_okm; assumption).
    forward. apply semax_if_seq. forward_if.
    { assert (Ef: fh_checksumFlag (zp_h z) = 1).
      { destruct Ck as [E | E]; auto. rewrite E in *. contradiction. }
      forward. forward. forward.
      sep_apply (data_at_data_at_ Tsh t_bp (bp_val (block_props_of (iw_s i))) v_bp).
      Exists 0 (oa_c o) (fsu_stage (fsu_expected (fsu_rleSize (fsu_bType (fsu_expected
        (fsu_processedCSize fs1 (Vlong (Int64.repr (pcs + ZSTD_blockHeaderSize)))) (Vlong (Int64.repr 0)))
        (Vint (Int.repr (Z.land (Z.shiftr (le_field (iw_s i) 0 3) 1) 3))))
        (Vlong (Int64.repr (Int.unsigned (Int.repr (Z.shiftr (le_field (iw_s i) 0 3) 3)))))) (Vlong (Int64.repr 4))) (Vint (Int.repr 5))) (Some ts).
      ff_unfold. try rewrite add64_repr.
      rewrite conj_rot5. entailer!.
      all: try (rewrite Fp; apply derives_refl).
      split; [apply HXP; intros _; apply (cx_bhdr_ok fs1 ts o (iw_s i) _ (zp_h z) (zp_bsm z) Est1 Fp ltac:(rep_lia) ltac:(rep_lia) Ck 0 5 4); [exact Ec | assumption | exact Hbi | repeat split; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | | | ];
        [intros; lia | intros _ E; rewrite El in E; contradiction |
         intros _ _; split;
         [ match goal with Hx: fh_contentSize (zp_h z) = ZSTD_CONTENTSIZE_UNKNOWN \/ _ |- _ =>
             destruct Hx as [Hx | Hx]; [left; exact Hx | right; exists (Zlength (zp_out z)); split; [exact Ed | exact Hx]] end
         | rewrite Ef; split; reflexivity ]] |].
      eapply cont_res_bhdr with (fs1 := fs1) (c := 0); eauto; try reflexivity; try lia.
      all: try (eexists; reflexivity).
      unfold zstep, phase_fields, next_phase. rewrite Ez, Ec. cbn [Z.eqb zp_with zp_ph zp_h].
      rewrite El, Ef. cbn. auto. }
    { assert (Ef: fh_checksumFlag (zp_h z) = 0).
      { destruct Ck as [E | E]; auto. rewrite E in *.
        exfalso. match goal with Hz: Int.repr 1 = Int.zero |- _ => exact (Int.one_not_zero Hz) end. }
      forward. forward. forward.
      sep_apply (data_at_data_at_ Tsh t_bp (bp_val (block_props_of (iw_s i))) v_bp).
      Exists 0 (oa_c o) (fsu_stage (fsu_expected (fsu_rleSize (fsu_bType (fsu_expected
        (fsu_processedCSize fs1 (Vlong (Int64.repr (pcs + ZSTD_blockHeaderSize)))) (Vlong (Int64.repr 0)))
        (Vint (Int.repr (Z.land (Z.shiftr (le_field (iw_s i) 0 3) 1) 3))))
        (Vlong (Int64.repr (Int.unsigned (Int.repr (Z.shiftr (le_field (iw_s i) 0 3) 3)))))) (Vlong (Int64.repr 0))) (Vint (Int.repr 0))) (Some ts).
      ff_unfold. try rewrite add64_repr.
      rewrite conj_rot5. entailer!.
      all: try (rewrite Fp; apply derives_refl).
      split; [apply HXP; intros _; apply (cx_bhdr_ok fs1 ts o (iw_s i) _ (zp_h z) (zp_bsm z) Est1 Fp ltac:(rep_lia) ltac:(rep_lia) Ck 0 0 0); [exact Ec | assumption | exact Hbi | repeat split; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | | | ];
        [intros; lia | intros _ E; rewrite El in E; contradiction |
         intros _ _; split;
         [ match goal with Hx: fh_contentSize (zp_h z) = ZSTD_CONTENTSIZE_UNKNOWN \/ _ |- _ =>
             destruct Hx as [Hx | Hx]; [left; exact Hx | right; exists (Zlength (zp_out z)); split; [exact Ed | exact Hx]] end
         | rewrite Ef; split; reflexivity ]] |].
      eapply cont_res_bhdr with (fs1 := fs1) (c := 0); eauto; try reflexivity; try lia.
      all: try (eexists; reflexivity).
      unfold zstep, phase_fields, next_phase. rewrite Ez, Ec. cbn [Z.eqb zp_with zp_ph zp_h].
      rewrite El, Ef. cbn. auto. } }
  { (* not the last block *)
    assert (El: bp_last (block_props_of (iw_s i)) = 0).
    { change (Z.land (le_field (iw_s i) 0 3) 1) with (bp_last (block_props_of (iw_s i))) in *. destruct Hl01 as [E | E]; auto. rewrite E in *.
      exfalso. match goal with Hz: Int.repr 1 = Int.zero |- _ => exact (Int.one_not_zero Hz) end. }
    assert (Hf6: 0 = 0 -> bp_last (block_props_of (iw_s i)) = 1 -> fcs_okm (zp_h z) (zp_out z))
      by (intros _ E; rewrite El in E; discriminate).
    unfold zstd_globals. Intros. forward. sep_apply (zstd_globals_fold gv).
    forward. forward. forward.
    sep_apply (data_at_data_at_ Tsh t_bp (bp_val (block_props_of (iw_s i))) v_bp).
      Exists 0 (oa_c o) (fsu_stage (fsu_expected (fsu_rleSize (fsu_bType (fsu_expected
        (fsu_processedCSize fs1 (Vlong (Int64.repr (pcs + ZSTD_blockHeaderSize)))) (Vlong (Int64.repr 0)))
        (Vint (Int.repr (Z.land (Z.shiftr (le_field (iw_s i) 0 3) 1) 3))))
        (Vlong (Int64.repr (Int.unsigned (Int.repr (Z.shiftr (le_field (iw_s i) 0 3) 3)))))) ZSTD_blockHeaderSize_val) (Vint (Int.repr 2))) (Some ts).
      ff_unfold. try rewrite add64_repr.
      rewrite conj_rot5. entailer!.
      all: try (rewrite Fp; apply derives_refl).
      split; [apply HXP; intros _; apply (cx_bhdr_ok fs1 ts o (iw_s i) _ (zp_h z) (zp_bsm z) Est1 Fp ltac:(rep_lia) ltac:(rep_lia) Ck 0 2 3); [exact Ec | assumption | exact Hbi | repeat split; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | | | ];
        [intros; lia | intros _ _; split; reflexivity | intros _ E; rewrite El in E; discriminate] |].
      eapply cont_res_bhdr with (fs1 := fs1) (c := 0); eauto; try reflexivity; try lia.
      all: try (eexists; reflexivity).
      unfold zstep, phase_fields, next_phase. rewrite Ez, Ec. cbn [Z.eqb zp_with zp_ph zp_h].
      rewrite El. cbn. auto. }
Qed.

End CM_C3Bhdr_1.
