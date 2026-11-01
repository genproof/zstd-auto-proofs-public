(* FS3 streaming: the body of ZSTD_decompressContinue against S3Specs.ZSTD_decompressContinue_spec3,
   modulo the two S3Defs gaps stuck_gap / dd_gap (C3Base; port of v2 body_stream_continue.v). *)
Require Import Zstd.proof.dec.v3.FS.stream.S3Specs.
Require Import Zstd.proof.dec.v3.FS.stream.cont.C3Base.
Require Import Zstd.proof.dec.v3.FS.stream.cont.C3Mid.
Require Import Zstd.proof.dec.v3.FS.stream.cont.C3Bhdr.
Require Import Zstd.proof.dec.v3.FS.stream.cont.C3Blk.
Require Import Zstd.proof.zstd.XxhLemmas.
Require Import Zstd.proof.dec.v3.FS.stream.cont.C3XDefs.
Require Import Zstd.proof.dec.v3.FS.stream.cont.C3XKit.
Require Import Zstd.proof.dec.v3.FS.stream.cont.C3XHdr.

Section CM_C3Main_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma lay_res_ptr l : lay_res l |-- !! lay_ptr l.
Proof.
  destruct l as [ | eb ec gp | b pe od | b ps pe e]; cbn; try (apply prop_right; exact I).
  entailer!. destruct (fc_arr (Zlength ec) eb) as (bb & ofs & -> & HN); auto; [apply Zlength_nonneg |].
  exists bb, ofs. split; auto.
Qed.

Lemma lay_res_fold l : pws_pred (lay_W l) * lay_rest l |-- lay_res l.
Proof. rewrite lay_res_split. apply derives_refl. Qed.

Lemma lay_res_unfold l : lay_res l |-- pws_pred (lay_W l) * lay_rest l.
Proof. rewrite lay_res_split. apply derives_refl. Qed.

Lemma body3_stream_continue_gen (Hsg: stuck_gap) (Hdg: dd_gap) :
  stream_body3 (fun DENT TABS BR => ZSTD_decompressContinue_spec3 DENT TABS).
Proof.
  intros DENT TABS BR HD HT; exists f_ZSTD_decompressContinue; split; [reflexivity | split; [reflexivity | ]].
  start_function.
  destruct H as (H & H0 & H1 & H2 & H3 & H4 & Hch & Hw & H5 & H6 & H7 & Hf).
  destruct (cf_stage _ _ _ _ _ _ H H0 H1 H2) as (st & e & Hst & Hex & He & Hstv & Hbt & Hns).
  dw0.
  unfold frame_fields. rewrite Hst, Hex. Intros.
  match goal with |- semax _ ?P _ _ => forward_loop P break: P end.
  { entailer!. }
  { forward_call (p, st, fs_bType fs, e, n).
    { repeat match goal with |- _ /\ _ => split end; try rep_lia;
      try (destruct Hstv as [-> | [-> | [-> | [-> | ->]]]]; rep_lia).
      all: unfold ds_decompressBlock, ds_decompressLastBlock in *.
      all: match goal with Hs: _ \/ _ |- _ => destruct (Hbt Hs) as (b & -> & Hb) end; exists b; split; auto; rep_lia. }
    rewrite Hns.
    forward_if.
    { exfalso. auto. }
    forward. entailer!. }
  rewrite <- Hst, <- Hex. sep_apply (frame_fields_fold p fs).
  assert_PROP (field_compatible (tarray tuchar (oa_N o)) [] (oa_base o)) by entailer!.
  assert_PROP (lay_ptr l) as Hlp by (sep_apply (lay_res_ptr l); entailer!).
  pose proof H3 as Hoo.
  destruct H3 as (Hsh & HcN & HN32 & Hd & Hcap & Hdc).
  destruct (fc_arr (oa_N o) (oa_base o)) as (b & ofs & Eb & HN); auto; [rep_lia |].
  sep_apply (lay_res_unfold l).
  sep_apply (pws_app_fold (lay_W l) W).
  sep_apply (pws_cons_fold (oa_sh o) (oa_N o) (oa_c o) (oa_base o) (lay_W l ++ W)).
  pose proof H as Hcf. destruct H as (A1 & A2 & A3 & Lf & Ld & M).
  destruct (cont_pre_ok fs l dd o b ofs W Lf Ld H4 Hw Hdg Hsh Hd Hcap Hdc Eb) as (Cp0 & Cp1 & Cp2).
  forward_call (p, fs, pw_bytes (oa_sh o) (oa_N o) (oa_c o) (oa_base o) :: lay_W l ++ W,
                offset_val (oa_d o) (oa_base o), oa_cap o).
  rewrite pws_cons_bytes. Intros.
  sep_apply (pws_app_unfold (lay_W l) W). sep_apply (lay_res_fold l).
  pose proof (cont_cframe _ _ _ _ _ _ b ofs W Hcf H4 Hoo H5 Hw Hlp Eb HN) as Hcf1.
  set (fs1 := continuity fs (offset_val (oa_d o) (oa_base o)) (oa_cap o)) in *.
  set (l1 := lmove l (oa_base o) (oa_d o) (oa_cap o)) in *.
  assert (Est1: fs_stage fs1 = Vint (Int.repr st)) by (subst fs1; unfold continuity; destruct cont_moves; auto).
  destruct A3 as [pcs Hpcs].
  assert (Ep1: fs_processedCSize fs1 = Vlong (Int64.repr pcs))
    by (subst fs1; unfold continuity; destruct cont_moves; auto).
  assert (Ecold: fs_ddictIsCold fs1 = fs_ddictIsCold fs)
    by (subst fs1; unfold continuity; destruct cont_moves; auto).
  assert (Efpar: fs_fParams fs1 = fs_fParams fs)
    by (subst fs1; unfold continuity; destruct cont_moves; auto).
  unfold frame_fields. rewrite Ep1, Est1. Intros.
  (* the exact claim of the cases gives the specification's (C3XKit.cont_exact_of) *)
  assert (Hst7: st = 7 -> oa_cap o = 0).
  { intros E7. pose proof (stage_inv _ _ _ _ _ _ Hcf H0 Hst ltac:(lia)) as Hfp7.
    destruct fp as [ | | hdr0 got0 | hdr0 z0]; try contradiction; [apply H5; reflexivity |].
    destruct (zp_ph z0); try contradiction; unfold ds_decodeBlockHeader, ds_checkChecksum, ds_decompressLastBlock,
      ds_decompressBlock in Hfp7; try (destruct (_ =? 1) in Hfp7); lia. }
  assert (HXm: forall r oc' fs' tabs', (dd_ox dd = None -> cont_exact1 fs1 ts o (iw_s i) n r oc' fs' tabs') ->
            dd = None -> cont_exact fs ts o (iw_s i) n r oc' fs' tabs').
  { intros r oc' fs' tabs' Hx Hdd. apply (cont_exact_of fs fs1 ts o (iw_s i) n r oc' fs' tabs' b ofs st e);
      auto; try reflexivity; try rep_lia.
    apply Hx. rewrite Hdd. reflexivity. }
  forward. forward.
  forward.
  forward_switch'.
  all: try (exfalso; clear - Hstv; lia).
  - (* decodeBlockHeader (Delta unfolded first: unifying the abbreviated one with the lemma's does not finish) *)
    change Delta with (func_tycontext f_ZSTD_decompressContinue Vprog (stream_G3 DENT TABS BR) nil).
    eapply semax_pre; [| apply (bhdr_case_ok Espec DENT TABS BR HD HT gv p f dd fs1 ts fp l W o src i n v_bp pcs b ofs
                                  (fs_ddictIsCold fs) (fs_fParams fs) (fun r oc' fs' tabs' => dd = None -> cont_exact fs ts o (iw_s i) n r oc' fs' tabs')); assumption].
    unfold blk_pre. entailer!.
  - (* decompressLastBlock *)
    change Delta with (func_tycontext f_ZSTD_decompressContinue Vprog (stream_G3 DENT TABS BR) nil).
    eapply semax_pre; [| apply (blk_case_ok Espec DENT TABS BR HD HT Hsg Hdg gv p f dd fs1 ts fp l W o src i n v_bp pcs 4
                                  b ofs (fs_ddictIsCold fs) (fs_fParams fs) (fun r oc' fs' tabs' => dd = None -> cont_exact fs ts o (iw_s i) n r oc' fs' tabs') (or_intror eq_refl)); assumption].
    unfold blk_pre. entailer!.
  - (* decompressBlock: the same code *)
    change Delta with (func_tycontext f_ZSTD_decompressContinue Vprog (stream_G3 DENT TABS BR) nil).
    eapply semax_pre; [| apply (blk_case_ok Espec DENT TABS BR HD HT Hsg Hdg gv p f dd fs1 ts fp l W o src i n v_bp pcs 3
                                  b ofs (fs_ddictIsCold fs) (fs_fParams fs) (fun r oc' fs' tabs' => dd = None -> cont_exact fs ts o (iw_s i) n r oc' fs' tabs') (or_introl eq_refl)); assumption].
    unfold blk_pre. entailer!.
  - (* checkChecksum *)
    pose proof (stage_inv _ _ _ _ _ _ Hcf1 H0 Est1 ltac:(lia)) as Hfp.
    destruct fp as [ | | hdr got | hdr z]; try contradiction.
    { unfold ds_skipFrame in Hfp; lia. }
    destruct (zp_ph z) as [ | bh | | ] eqn:Ez; try contradiction;
      unfold ds_decodeBlockHeader, ds_checkChecksum, ds_decompressLastBlock, ds_decompressBlock in Hfp;
      try (destruct (_ =? 1) in Hfp); try lia.
    pose proof Hcf1 as Hc1. destruct Hc1 as (_ & _ & _ & Lf1 & Ld1 & M1).
    destruct M1 as (T0 & Fp & B1 & B2 & W1 & W2 & Fc & Ck & Dm & Ets & Ph & Ed & Vc & Ex & Bo & Mz & Bg).
    rewrite Ez in Mz. unfold phase_fields in Ph. rewrite Ez in Ph.
    cbn [unit_ok] in H1. rewrite Ez in H1. destruct H1 as [Hg0 Hn4]. subst n.
    destruct (H6 eq_refl) as (Hsrc & Hiw & Hlen & Hbcin).
    destruct Ets as (ts0 & Ets & Ets'). injection Ets as Ets. subst ts0.
    unfold in_res; cbn [is_skip].
    destruct Mz as [_ Hf1]. rewrite Hf1 in Vc, Ex.
    replace (1 =? 1) with true in Vc, Ex by reflexivity.
    destruct (zp_ign z) eqn:Eign; cbn [negb andb] in Vc, Ex.
    + (* checksums ignored: no comparison *)
      rewrite Vc.
      forward.
      match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
        forward_if (PROPx P (LOCALx Q (SEPx R))) end.
      { exfalso. match goal with Hz: Int.repr 0 <> Int.zero |- _ => apply Hz; reflexivity end. }
      { forward. entailer!. }
      rewrite Ed. forward. forward.
      forward_call (p, Zlength (zp_out z), pcs + 4, 1).
      forward. forward. forward.
      Exists 0 (oa_c o)
        (fsu_stage (fsu_expected (fsu_processedCSize fs1 (Vlong (Int64.repr (pcs + 4)))) (Vlong (Int64.repr 0)))
           (Vint (Int.repr 0))) (Some ts).
      unfold frame_fields. cbn [fs_previousDstEnd fs_gpDictCopy fs_prefixStart fs_virtualStart fs_dictEnd fs_expected
        fs_fParams fs_processedCSize fs_decodedSize fs_bType fs_stage fs_xxh fs_headerSize fs_validateChecksum
        fs_rleSize fs_isFrameDecompression fs_dictID fs_ddictIsCold fsu_stage fsu_expected fsu_processedCSize].
      rewrite Vc, Ed. try rewrite add64_repr.
      match goal with |- context [cont_exact fs ts o (iw_s i) ?nn ?a ?b ?c ?d] =>
        assert (HX: dd = None -> cont_exact fs ts o (iw_s i) nn a b c d) by (apply HXm; intros _; apply (cx_ck_ok fs1 ts o (iw_s i) _ _ false (zp_out z) (proj1 Ph) Vc
                                   ltac:(intros E; discriminate E) ltac:(intros E; discriminate E));
                                [repeat split; reflexivity | reflexivity | reflexivity]) end.
      entailer!.
      apply cont_res_ck; auto; try lia. destruct Hiw as (_ & _ & _ & _ & _ & _ & Hbi' & _); auto.
    + specialize (Ex eq_refl). rewrite Vc, Ex. unfold xxh_field.
      forward.
      fif_prop (le_field (iw_s i) 0 4 = xxh64 (zp_out z) 0 mod 2 ^ 32).
      2: { exfalso. match goal with Hz: Int.repr 1 = Int.zero |- _ => exact (Int.one_not_zero Hz) end. }
      { assert_PROP (field_compatible t_dctx (DOT _expected) p) as Fce by entailer!.
        assert (Fcx: field_compatible t_dctx (DOT _xxhState) p).
        { apply field_compatible_cons in Fce. apply field_compatible_cons. simpl in Fce |- *.
          split; [| tauto]. unfold in_members. simpl. repeat (first [left; reflexivity | right]). }
        apply -> seq_assoc.
        forward_call (Ews, field_address t_dctx (DOT _xxhState) p, 0, zp_out z).
        forward.
        pose proof Hiw as (Rs & Ho & Hon & HNi & Hci & Hsi & Hbi & Hwi).
        assert_PROP (field_compatible (tarray tuchar (iw_N i)) [] (iw_base i)) by entailer!.
        rewrite (arr_split (iw_sh i) (iw_N i) (iw_c i) (iw_base i) (iw_off i) (iw_s i)) by (auto; lia).
        Intros.
        forward_call (iw_sh i, offset_val (iw_off i) (iw_base i), iw_s i, 0).
        { unfold mem_read_pre. split; [auto |]. split; [lia |]. split; [lia |]. apply Forall_sublist; auto. }
        dw0.
        match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
          forward_loop (PROPx P (LOCALx Q (SEPx R)))
            break: (PROPx ((le_field (iw_s i) 0 4 = xxh64 (zp_out z) 0 mod 2 ^ 32) :: P) (LOCALx Q (SEPx R))) end.
        { entailer!. }
        { forward_if.
          - dw0. dw0. dw0. dw0.
            forward.
            sep_apply (arr_join (iw_sh i) (iw_N i) (iw_c i) (iw_base i) (iw_off i) (iw_s i)); [auto; lia .. |].
            Exists (2 ^ 64 - 22) (oa_c o) (fsu_processedCSize fs1 (Vlong (Int64.repr (pcs + 4)))) (Some ts).
            unfold frame_fields, xxh_field. cbn [fs_previousDstEnd fs_gpDictCopy fs_prefixStart fs_virtualStart fs_dictEnd fs_expected
              fs_fParams fs_processedCSize fs_decodedSize fs_bType fs_stage fs_xxh fs_headerSize fs_validateChecksum
              fs_rleSize fs_isFrameDecompression fs_dictID fs_ddictIsCold fsu_processedCSize].
            rewrite Est1, Vc, Ex. try rewrite add64_repr. try rewrite <- repr_neg64.
            match goal with |- context [cont_exact fs ts o (iw_s i) ?nn ?a ?b ?c ?d] =>
        assert (HX: dd = None -> cont_exact fs ts o (iw_s i) nn a b c d) by (apply HXm; intros _; apply (cx_ck_bad fs1 ts o (iw_s i) _ _ _ _ _ (zp_out z) (proj1 Ph) Vc Ex);
                                [ intros E; assert (Hle := lef_range (iw_s i) 0 4 Hbi ltac:(lia));
                                  rewrite xxh64_digest_model_eq_all in *;
                                  match goal with Hn: Int.repr _ <> Int.repr _ |- _ => apply Hn end;
                                  apply ck_iff; [rep_lia | exact E]
                                | reflexivity ]) end.
            entailer!.
            assert (Hle := lef_range (iw_s i) 0 4 Hbi ltac:(lia)).
            rewrite xxh64_digest_model_eq_all in *.
            split; [rep_lia |]. split; [auto |]. split; [intros j _ _; auto |]. split; [intros X; exact X |].
            replace (is_error_code (2 ^ 64 - 22)) with true by reflexivity.
            split; [| apply nfp_ne; lia].
            intros _. cbn [cont_err]. rewrite Ez, Eign. split; [reflexivity |]. intros E.
            match goal with Hn: Int.repr _ <> Int.repr _ |- _ => apply Hn end. apply ck_iff; auto; rep_lia.
          - forward. entailer!.
            assert (Hle := lef_range (iw_s i) 0 4 Hbi ltac:(lia)).
            rewrite xxh64_digest_model_eq_all in *.
            apply ck_iff; [rep_lia |].
            match goal with Hn: ~ (Int.repr _ <> Int.repr _) |- _ => apply Classical_Prop.NNPP in Hn; exact Hn
                       | Hn: Int.repr _ = Int.repr _ |- _ => exact Hn end. }
        Intros.
        sep_apply (arr_join (iw_sh i) (iw_N i) (iw_c i) (iw_base i) (iw_off i) (iw_s i)); [auto; lia .. |].
        entailer!. }
      Intros. match goal with Hx: le_field (iw_s i) 0 4 = _ |- _ => rename Hx into Hck end.
      rewrite Ed. forward. forward.
      forward_call (p, Zlength (zp_out z), pcs + 4, 1).
      forward. forward. forward.
      Exists 0 (oa_c o)
        (fsu_stage (fsu_expected (fsu_processedCSize fs1 (Vlong (Int64.repr (pcs + 4)))) (Vlong (Int64.repr 0)))
           (Vint (Int.repr 0))) (Some ts).
      unfold frame_fields, xxh_field. cbn [fs_previousDstEnd fs_gpDictCopy fs_prefixStart fs_virtualStart fs_dictEnd fs_expected
        fs_fParams fs_processedCSize fs_decodedSize fs_bType fs_stage fs_xxh fs_headerSize fs_validateChecksum
        fs_rleSize fs_isFrameDecompression fs_dictID fs_ddictIsCold fsu_stage fsu_expected fsu_processedCSize].
      rewrite Vc, Ex, Ed. try rewrite add64_repr.
      match goal with |- context [cont_exact fs ts o (iw_s i) ?nn ?a ?b ?c ?d] =>
        assert (HX: dd = None -> cont_exact fs ts o (iw_s i) nn a b c d) by (apply HXm; intros _; apply (cx_ck_ok fs1 ts o (iw_s i) _ _ true (zp_out z) (proj1 Ph) Vc (fun _ => Ex) (fun _ => Hck));
                                [repeat split; reflexivity | reflexivity | reflexivity]) end.
      entailer!.
      apply cont_res_ck; auto; try lia. destruct Hiw as (_ & _ & _ & _ & _ & _ & Hbi' & _); auto.
  - (* skipFrame *)
    pose proof (stage_inv _ _ _ _ _ _ Hcf1 H0 Est1 ltac:(lia)) as Hfp.
    destruct fp as [ | | hdr got | hdr z]; try contradiction.
    2: { destruct (zp_ph z); unfold ds_decodeBlockHeader, ds_checkChecksum, ds_decompressLastBlock, ds_decompressBlock in Hfp;
         try destruct (_ =? 1); try lia; contradiction. }
    destruct H1 as [-> Hn]. assert (Hl1: l1 = l) by (subst l1; unfold lmove; rewrite H5 by reflexivity; reflexivity).
    rewrite Hl1 in Hcf1.
    forward. forward. forward.
    Exists 0 (oa_c o)
      (fsu_stage (fsu_expected (fsu_processedCSize fs1 (Vlong (Int64.repr (pcs + le_field hdr 4 4)))) (Vlong (Int64.repr 0)))
         (Vint (Int.repr 0))) (Some ts).
    unfold frame_fields. cbn [fs_previousDstEnd fs_gpDictCopy fs_prefixStart fs_virtualStart fs_dictEnd fs_expected
      fs_fParams fs_processedCSize fs_decodedSize fs_bType fs_stage fs_xxh fs_headerSize fs_validateChecksum
      fs_rleSize fs_isFrameDecompression fs_dictID fs_ddictIsCold fsu_stage fsu_expected fsu_processedCSize].
    try rewrite add64_repr.
    match goal with |- context [cont_exact fs ts o (iw_s i) ?nn ?a ?b ?c ?d] =>
        assert (HX: dd = None -> cont_exact fs ts o (iw_s i) nn a b c d) by (apply HXm; intros _; apply (cx_skip fs1 ts o (iw_s i) _ _ ltac:(rewrite Est1, Hfp; reflexivity));
                                [repeat split; reflexivity | reflexivity | reflexivity]) end.
    entailer!.
    split; [rep_lia |]. split; auto. split; [intros j _ _; auto |]. split; [intros X; exact X |].
    replace (is_error_code 0) with false by reflexivity. cbn [cont_post].
    split; auto. split; auto. exists ts. split; [reflexivity |]. apply cf_skip_done; auto.
  - (* default: no other stage is possible *)
    exfalso. destruct Hstv as [-> | [-> | [-> | [-> | ->]]]];
      match goal with Hx: Int.unsigned (Int.repr ?a) <> Int.unsigned (Int.repr ?a) |- _ => apply Hx; reflexivity end.
Qed.

End CM_C3Main_1.
