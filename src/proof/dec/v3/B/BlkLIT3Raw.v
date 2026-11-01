(* ZSTD_decodeLiteralsBlock, the arm set_basic of its switch (raw literals): copied into the literal buffer
   ZSTD_allocateLiteralsBuffer chose (in dst, in litExtraBuffer, or split between them), or referenced in place
   when 32 more bytes of the block follow them; exactly as model/ExBlock.v (BlkLIT3Exact.lx_raw_ref, lx_raw_copy). *)
Require Export Zstd.proof.dec.v3.B.BlkLIT3Exact.
Local Open Scope logic.

(* litExtraBuffer exactly, forgotten to bytes (the scratch of an error return after the allocation) *)
Lemma lit_extra_at_weak (p: val) (lxb: list Z) : lit_extra_at p lxb |-- lit_extra_bytes p.
Proof.
  unfold lit_extra_at, lit_extra_bytes. Intros. Exists (zbytes lxb). entailer!. apply litc_bc_zbytes. assumption.
Qed.

(* the output array after the copy of input cells holding the bytes l, as the exact lemmas state it (cwr) *)
Lemma lit_cwr_eq (c ic: list val) (N k a m: Z) (l: list Z) :
  Zlength c = N -> sublist a (a + m) ic = zbytes l -> Zlength l = m ->
  sublist 0 k c ++ sublist a (a + m) ic ++ sublist (k + m) N c = cwr c k (zbytes l).
Proof. intros Hc Hw Hl. unfold cwr. rewrite Hw, Hc, Zlength_map, Hl. reflexivity. Qed.

(* litExtraBuffer after the copy of the bytes l into its first cells *)
Lemma lit_xb_app (l lxb: list Z) (k: Z) :
  zbytes l ++ sublist k LITEXTRA_N (zbytes lxb) = zbytes (l ++ sublist k LITEXTRA_N lxb).
Proof. rewrite map_app, sublist_map. reflexivity. Qed.

Lemma lit_xb_ok (l lxb: list Z) (k: Z) :
  Zlength l = k -> 0 <= k <= LITEXTRA_N -> Zlength lxb = LITEXTRA_N -> bytes_ok l -> bytes_ok lxb ->
  Zlength (l ++ sublist k LITEXTRA_N lxb) = LITEXTRA_N /\ bytes_ok (l ++ sublist k LITEXTRA_N lxb).
Proof.
  intros Hl Hk Hx Bl Bx. split; [rewrite Zlength_app, Zlength_sublist by lia; lia |].
  unfold bytes_ok in *. apply Forall_app. split; [exact Bl | apply Forall_sublist; exact Bx].
Qed.

Lemma seg_basic : lit_seg 0 0 (fun _ => True).
Proof.
  intros Espec gv p fs ox oh x2 lxb bsm streaming W o i R HY Hty _ HR.
  apply semax_post with (R' := switch_ret_assert (lit_R gv p fs ox oh x2 lxb bsm streaming W o i)).
  { intros. unfold lit_R. simpl. intros. normalize. }
  { intros. unfold lit_R. simpl. intros. normalize. }
  { intros. unfold lit_R. simpl. intros. normalize. }
  { intros vl. destruct R as [r1 r2 r3 r4]. simpl in HR. subst r4. simpl. intros.
    apply andp_left2. apply derives_refl. }
  assert_PROP (Zlength lxb = LITEXTRA_N /\ bytes_ok lxb) as Hlx.
  { unfold lit_S, lit_L, lit_scratch_x, lit_extra_at. Intros. apply prop_right. auto. }
  destruct Hlx as [Hlxb Hlxbb].
  assert (LXH: lx_hyps o i bsm streaming lxb).
  { destruct HY as (A1 & A2 & A3 & A4 & A5 & _). exact (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 Hlxb))))). }
  destruct o as [osh ob oN oc d cap]; destruct i as [ish ib iN ic ioff s].
  destruct HY as ((Hosh & HoN & HoN32 & Hd & Hcap & Hdc) & (Hish & Hioff & Hin & HiN32 & HiN & _ & Hbytes & Hwin)
                  & Hstr & Hbsm & Hsb & Hfp & Hfd & Hcold & Hweak & Hhuf & H2).
  unfold lit_L, lit_S, lit_R, lit_post.
  cbn [oa_sh oa_base oa_N oa_c oa_d oa_cap iw_sh iw_base iw_N iw_c iw_off iw_s] in *.
  subst iN oN.
  assert (Hbsm': 0 <= bsm <= 131072) by (unfold ZSTD_BLOCKSIZE_MAX in Hbsm; lia).
  change (Int.unsigned (Int.repr 0)) with 0.
  cbv [lit_sw f_ZSTD_decodeLiteralsBlock fn_body]. simpl select_switch. simpl seq_of_labeled_statement.
  abbreviate_semax.
  assert_PROP (force_val (sem_add_ptr_int tuchar Signed (offset_val ioff ib) (Vint (Int.repr 0))) =
               field_address (tarray tuchar (Zlength ic)) [ArraySubsc ioff] ib) as FA0.
  { entailer!. rewrite lit_fa by (auto; lia). reflexivity. }
  assert (B0: @Znth val Vundef ioff ic = Vint (Int.repr (byte_at s 0))).
  { rewrite <- (Z.add_0_r ioff) at 1. apply lit_win_byte; auto; lia. }
  pose proof (lit_byte_range s 0 Hbytes) as R0.
  forward.
  { entailer!. rewrite B0. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
  rewrite B0.
  forward.
  forward_if (temp _t'26 (Vlong (Int64.repr (Z.min bsm cap)))).
  { forward. entailer!. do 2 f_equal. lia. }
  { forward. entailer!. do 2 f_equal. lia. }
  forward.
  pose proof (lit_shiftr_range (byte_at s 0) 2 ltac:(lia) ltac:(lia)) as RS2.
  rewrite (lit_shr (byte_at s 0) 2) by rep_lia.
  rewrite lit_band3 by lia.
  pose proof (lit_band3_range (Z.shiftr (byte_at s 0) 2)) as Hl.
  forward_if (EX lh: Z, EX ls: Z,
    PROP (lit_rawhdr s = (lh, ls); Z.land (Z.shiftr (byte_at s 0) 2) 3 = 3 -> 3 <= Zlength s)
    LOCAL (temp _lhSize__1 (Vlong (Int64.repr lh)); temp _litSize__1 (Vlong (Int64.repr ls));
           temp _expectedWriteSize__1 (Vlong (Int64.repr (Z.min bsm cap)));
           temp _blockSizeMax (Vlong (Int64.repr bsm)); temp _istart (offset_val ioff ib);
           gvars gv; temp _dctx p; temp _srcSize (Vlong (Int64.repr (Zlength s)));
           temp _dst (offset_val d ob); temp _dstCapacity (Vlong (Int64.repr cap));
           temp _streaming (Vint (Int.repr streaming)))
    SEP (frame_fields p fs; zstd_globals gv; pws_pred W; cfg_lit p; tabs_huf gv p ox oh x2; dent_of dent_def gv ox;
         field_at_ Ews t_dctx (DOT _workspace) p; lit_scratch_x p lxb;
         data_at osh (tarray tuchar (Zlength oc)) oc ob;
         data_at ish (tarray tuchar (Zlength ic)) ic ib)).
  { (* lhlCode 0 *)
    forward. forward.
    { entailer!. rewrite B0. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    rewrite B0. forward. forward.
    Exists 1 (Z.shiftr (byte_at s 0) 3). entailer!.
    split; [unfold lit_rawhdr; rewrite E; reflexivity |].
    pose proof (lit_shiftr_range (byte_at s 0) 3 ltac:(lia) ltac:(lia)).
    rewrite lit_shr by rep_lia. rewrite Int.signed_repr by rep_lia. reflexivity. }
  { (* lhlCode 2 *)
    forward. forward.
    { entailer!. rewrite B0. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    rewrite B0. forward. forward.
    Exists 1 (Z.shiftr (byte_at s 0) 3). entailer!.
    split; [unfold lit_rawhdr; rewrite E; reflexivity |].
    pose proof (lit_shiftr_range (byte_at s 0) 3 ltac:(lia) ltac:(lia)).
    rewrite lit_shr by rep_lia. rewrite Int.signed_repr by rep_lia. reflexivity. }
  { (* lhlCode 1 *)
    forward.
    assert_PROP (field_compatible (tarray tuchar (Zlength ic)) [] ib) as FCi by entailer!.
    rewrite (lit_split3 ish (Zlength ic) ioff (Zlength s) ic ib) by (auto; lia).
    rewrite Hwin. Intros.
    forward_call (ish, offset_val ioff ib, s, 0).
    { unfold mem_read_pre. split; [auto | split; [lia | split; [lia |]]].
      unfold bytes_ok in *. apply Forall_sublist. exact Hbytes. }
    forward.
    pose proof (lit_le_field s 2 Hbytes ltac:(lia)) as L.
    forward.
    Exists 2 (Z.shiftr (le_field s 0 2) 4).
    rewrite (lit_split3 ish (Zlength ic) ioff (Zlength s) ic ib) by (auto; lia).
    rewrite Hwin. entailer!.
    split; [unfold lit_rawhdr; rewrite E; reflexivity |].
    pose proof (lit_shiftr_range (le_field s 0 2) 4 ltac:(lia) ltac:(lia)).
    rewrite lit_shr by rep_lia. rewrite Int.signed_repr by rep_lia. reflexivity. }
  { (* lhlCode 3 *)
    forward.
    lit_check (3 <= Zlength s).
    { entailer!. }
    { forward_if.
      - lit_errpath. lit_err 20 oc oh x2 lxb.
        rewrite lit_dl_raw3 by (auto; rewrite !Int64.unsigned_repr in * by rep_lia; lia). auto.
        cbn [iw_s oa_cap]. apply xl_raw3; auto. rewrite !Int64.unsigned_repr in * by rep_lia; lia.
      - forward. entailer!. rewrite !Int64.unsigned_repr in * by rep_lia. lia. }
    Intros.
    assert_PROP (field_compatible (tarray tuchar (Zlength ic)) [] ib) as FCi by entailer!.
    rewrite (lit_split3 ish (Zlength ic) ioff (Zlength s) ic ib) by (auto; lia).
    rewrite Hwin. Intros.
    forward_call (ish, offset_val ioff ib, s, 0).
    { unfold mem_read_pre. split; [auto | split; [lia | split; [lia |]]].
      unfold bytes_ok in *. apply Forall_sublist. exact Hbytes. }
    forward.
    pose proof (lit_le_field s 3 Hbytes ltac:(lia)) as L.
    forward.
    Exists 3 (Z.shiftr (le_field s 0 3) 4).
    rewrite (lit_split3 ish (Zlength ic) ioff (Zlength s) ic ib) by (auto; lia).
    rewrite Hwin. entailer!.
    split; [unfold lit_rawhdr; rewrite E; reflexivity |].
    pose proof (lit_shiftr_range (le_field s 0 3) 4 ltac:(lia) ltac:(lia)).
    rewrite lit_shru by rep_lia. rewrite Int.unsigned_repr by rep_lia. reflexivity. }
  { (* default: impossible *)
    exfalso. rewrite !Int.unsigned_repr in * by rep_lia. lia. }
  Intros lh ls.
  match goal with H: lit_rawhdr s = _ |- _ => rename H into Hh end.
  match goal with H: _ -> 3 <= Zlength s |- _ => rename H into H3 end.
  destruct (lit_rawhdr_range s lh ls Hbytes H2 H3 Hh) as (Hlh & Hlhn & Hls).
  pose proof (lit_dl_raw oh s bsm lh ls Hty H2 H3 Hh) as DL.
  pose proof (xl_raw (option_map (xhuf_of x2) oh) s bsm (Z.min bsm cap) (streaming =? 1) lh ls Hty H2 H3 Hh) as XL.
  assert_PROP (isptr ob) as Pob by entailer!.
  (* RETURN_ERROR_IF(litSize > 0 && dst == NULL): dst is never NULL *)
  lit_check True.
  { entailer!. }
  { forward_if (temp _t'29 (Vint (Int.repr 0))).
    - forward.
      + entailer!. apply lit_test_eq_null; [destruct ob; try contradiction; exact I |].
        eapply derives_trans; [| apply (lit_dst_wvp W osh oc ob d cap); auto]. cancel.
      + entailer!. destruct ob; try contradiction. reflexivity.
    - forward. entailer!.
    - forward_if.
      + match goal with H: Int.repr 0 <> Int.zero |- _ => exfalso; apply H; reflexivity end.
      + forward. entailer!. }
  Intros.
  (* RETURN_ERROR_IF(litSize > blockSizeMax) *)
  lit_check (ls <= bsm).
  { entailer!. }
  { forward_if.
    - lit_errpath. lit_err 20 oc oh x2 lxb. rewrite DL.
      replace (ls >? bsm) with true by (symmetry; apply Z.gtb_lt; lia). auto.
      cbn [iw_s oa_cap]. rewrite XL. replace (ls >? bsm) with true by (symmetry; apply Z.gtb_lt; lia).
      reflexivity.
    - forward. entailer!; rewrite !Int64.unsigned_repr in * by rep_lia; lia. }
  Intros.
  (* RETURN_ERROR_IF(expectedWriteSize < litSize) *)
  lit_check (ls <= Z.min bsm cap).
  { entailer!. }
  { forward_if.
    - lit_errpath. lit_err 70 oc oh x2 lxb. rewrite DL.
      destruct (ls >? bsm); auto. destruct (lh + ls >? Zlength s) eqn:E; auto.
      rewrite Z.gtb_ltb in E. apply Z.ltb_ge in E. right. rewrite lit_slice_len by lia.
      lia.
      cbn [iw_s oa_cap]. rewrite XL.
      replace (ls >? bsm) with false by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
      replace (Z.min bsm cap <? ls) with true
        by (symmetry; apply Z.ltb_lt; first [lia | rewrite !Int64.unsigned_repr in * by rep_lia; lia]).
      reflexivity.
    - forward. entailer!; rewrite !Int64.unsigned_repr in * by rep_lia; lia. }
  Intros.
  unfold lit_scratch_x. Intros.
  forward_call (p, fs, bsm, ob, d, cap, ls, streaming, 1, osh, oc).
  destruct (lit_alloc_out oc streaming cap bsm ls d 1 ltac:(lia) ltac:(lia) ltac:(lia))
    as (AL & AU & AUs & AB & AD & AS1 & AS2 & AE).
  pose proof (lx_raw_ref (option_map (xhuf_of x2) oh) lxb _ _ bsm streaming lh ls LXH Hty H2 H3 Hh
                ltac:(cbn; lia) ltac:(cbn; lia)) as LXR.
  pose proof (lx_raw_copy (option_map (xhuf_of x2) oh) lxb _ _ bsm streaming lh ls LXH Hty H2 H3 Hh
                ltac:(cbn; lia) ltac:(cbn; lia)) as LXC.
  cbn [oa_c oa_cap oa_d iw_s iw_off] in LXR, LXC.
  set (oc1 := alloc_out oc streaming cap bsm ls d (Z.min bsm cap) 1) in *. clearbody oc1.
  forward_if.
  { (* copy into the literals buffer *)
    assert (Hlt: Zlength s < lh + ls + WILDCOPY_OVERLENGTH).
    { clear -H1 Hls Hlh Hlhn H2 HiN32 Hin Hioff. revert H1. rewrite !Int64.add_unsigned.
      rewrite (Int64.unsigned_repr lh), (Int64.unsigned_repr ls), (Int64.unsigned_repr 32) by rep_lia.
      rewrite (Int64.unsigned_repr (lh + ls)), !Int64.unsigned_repr by rep_lia.
      unfold WILDCOPY_OVERLENGTH. lia. }
    lit_check (lh + ls <= Zlength s).
    { entailer!. }
    { forward_if.
      - lit_errpath.
        Exists (err_code 20) oc1 LExtra (@nil Z) oh x2 lxb.
        rewrite (lit_err_true 20) by lia.
        destruct (lit_err_val 20) as [LEV LER]; [lia |].
        unfold lit_scratch. sep_apply (lit_extra_at_weak p lxb). entailer!.
        + apply Int64.ltu_inv in H4. rewrite !Int64.unsigned_repr in H4 by rep_lia.
          split; [| split; [intros _; apply lit_dec_err; lia |]].
          * rewrite DL. replace (ls >? bsm) with false by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
            replace (lh + ls >? Zlength s) with true by (symmetry; apply Z.gtb_lt; lia). auto.
          * intros _. apply lx_err; [apply lit_err_true; lia |]. cbn [iw_s oa_cap]. rewrite XL.
            replace (ls >? bsm) with false by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
            replace (Z.min bsm cap <? ls) with false by (symmetry; apply Z.ltb_ge; lia).
            replace (lh + ls >? Zlength s) with true by (symmetry; apply Z.gtb_lt; lia). reflexivity.
        + apply lit_huf_junk.
      - forward. entailer!.
        match goal with H: Int64.ltu _ _ = false |- _ =>
          unfold Int64.ltu in H; rewrite !Int64.unsigned_repr in H by rep_lia;
          destruct (zlt _ _) in H; [discriminate | lia] end. }
    Intros.
    forward.
    apply semax_if_seq. forward_if.
    - (* split: the first litSize - 65536 bytes in dst, the last 65536 in litExtraBuffer *)
      assert (HL: alloc_loc streaming cap bsm ls = LOC_SPLIT /\ 65536 < ls).
      { destruct (lit_alloc_cases streaming cap bsm ls) as [(E & _) | [(E & _) | (E & E2)]];
          rewrite E in *; auto;
          apply (f_equal Int.unsigned) in H5; unfold LOC_IN_DST, LOC_NOT_IN_DST in H5;
          rewrite !Int.unsigned_repr in H5 by rep_lia; discriminate. }
      destruct HL as [HL Hbig].
      replace (alloc_buf p ob streaming cap bsm ls d (Z.min bsm cap) 1)
        with (offset_val (d + Z.min bsm cap - ls + 65504) ob, offset_val (d + Z.min bsm cap - 32) ob)
        by (unfold alloc_buf; rewrite HL; cbn -[offset_val Z.min];
            unfold LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH; f_equal; f_equal; lia).
      cbn [fst snd].
      forward_if (temp _t'30 (Vint (Int.repr 65536))).
      { forward. entailer!. }
      { discriminate. }
      forward_if (temp _t'31 (Vint (Int.repr 65536))).
      { discriminate. }
      { forward_if (temp _t'31 (Vint (Int.repr 65536))).
        - forward. forward. entailer!.
        - discriminate. }
      forward.
      assert_PROP (field_compatible (tarray tuchar (Zlength oc)) [] ob) as FCo by entailer!.
      assert_PROP (field_compatible (tarray tuchar (Zlength ic)) [] ib) as FCi by entailer!.
      assert_PROP (field_compatible t_dctx (DOT _litBuffer) p) as FCx by entailer!.
      apply (lit_fc _litBuffer _litExtraBuffer) in FCx; [| apply compute_in_members_true_iff; reflexivity].
      assert (Pib: isptr ib) by (destruct FCi; auto).
      set (lb := d + Z.min bsm cap - ls + 65504) in *.
      rewrite (lit_split3 ish (Zlength ic) (ioff + lh) (ls - 65536) ic ib) by (auto; lia).
      rewrite (lit_split3 osh (Zlength oc) lb (ls - 65536) oc1 ob) by (auto; lia).
      Intros.
      sep_apply (data_at_data_at_ osh (tarray tuchar (ls - 65536)) (sublist lb (lb + (ls - 65536)) oc1)
                   (offset_val lb ob)).
      forward_call (ish, osh, offset_val (ioff + lh) ib, offset_val lb ob,
                    existT (fun t => reptype t) (tarray tuchar (ls - 65536))
                      (sublist (ioff + lh) (ioff + lh + (ls - 65536)) ic)).
      { cbn [projT1 projT2]. split; [rewrite sizeof_tarray_tuchar by lia; rep_lia |].
        apply memcpy_ok_bytes; [list_solve | apply (lit_win_bv ic ioff _ _ s); auto; lia]. }
      cbn [projT1 projT2].
      assert (J1 := lit_join3_same ish (Zlength ic) (ioff + lh) (ls - 65536) ic ib
                      ltac:(lia) ltac:(lia) ltac:(lia) eq_refl FCi).
      sep_apply J1. clear J1.
      assert (J2 := lit_join3 osh (Zlength oc) lb (ls - 65536) oc1
                      (sublist (ioff + lh) (ioff + lh + (ls - 65536)) ic) ob
                      ltac:(lia) ltac:(lia) ltac:(lia) AL ltac:(rewrite Zlength_sublist; lia) FCo).
      sep_apply J2. clear J2.
      forward_if (temp _t'32 (Vint (Int.repr 65536))).
      { forward. entailer!. }
      { discriminate. }
      forward_if (temp _t'33 (Vint (Int.repr 65536))).
      { discriminate. }
      { forward_if (temp _t'33 (Vint (Int.repr 65536))).
        - forward. forward. entailer!.
        - discriminate. }
      forward_if (temp _t'34 (Vint (Int.repr 65536))).
      { forward. entailer!. }
      { discriminate. }
      forward_if (temp _t'35 (Vint (Int.repr 65536))).
      { discriminate. }
      { forward_if (temp _t'35 (Vint (Int.repr 65536))).
        - forward. forward. entailer!.
        - discriminate. }
      rewrite (lit_split3 ish (Zlength ic) (ioff + lh + (ls - 65536)) 65536 ic ib) by (auto; lia).
      unfold lit_extra_at. Intros.
      assert (Hxl: Zlength (zbytes lxb) = LITEXTRA_N) by (rewrite Zlength_map; exact Hlxb).
      set (xl := zbytes lxb) in *.
      assert (J0 := lit_xb_take 65536 xl p
                      ltac:(unfold LITEXTRA_N, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH; lia) Hxl FCx).
      replace_SEP 16 (data_at_ Ews (tarray tuchar 65536) (lit_extra p) *
                      data_at Ews (tarray tuchar (LITEXTRA_N - 65536)) (sublist 65536 LITEXTRA_N xl)
                        (offset_val 65536 (lit_extra p))).
      { go_lower. apply J0. }
      clear J0. Intros.
      forward_call (ish, Ews, offset_val (ioff + lh + (ls - 65536)) ib, lit_extra p,
                    existT (fun t => reptype t) (tarray tuchar 65536)
                      (sublist (ioff + lh + (ls - 65536)) (ioff + lh + (ls - 65536) + 65536) ic)).
      + rewrite (lit_add_l (offset_val ioff ib) lh) by (destruct ib; try contradiction; exact I).
        rewrite (lit_add_l (offset_val lh (offset_val ioff ib)) ls) by (destruct ib; try contradiction; exact I).
        destruct ib; try contradiction; exact I.
      + entailer!.
        unfold lit_extra; rewrite field_address_offset by auto.
        rewrite (lit_add_l (offset_val ioff ib) lh) by (destruct ib; try contradiction; exact I).
        rewrite (lit_add_l (offset_val lh (offset_val ioff ib)) ls) by (destruct ib; try contradiction; exact I).
        rewrite lit_sub_i by (try (destruct ib; try contradiction; exact I); rep_lia).
        rewrite !offset_offset_val.
        destruct ib; try contradiction. destruct p; try (destruct FCx; contradiction).
        simpl. replace (ioff + (lh + (ls + -65536))) with (ioff + lh + (ls - 65536)) by lia. reflexivity.
      + cbn [projT1 projT2]. split; [rewrite sizeof_tarray_tuchar by lia; rep_lia |].
        apply memcpy_ok_bytes; [list_solve | apply (lit_win_bv ic ioff _ _ s); auto; lia].
      + cbn [projT1 projT2].
        assert (J3 := lit_join3_same ish (Zlength ic) (ioff + lh + (ls - 65536)) 65536 ic ib
                        ltac:(lia) ltac:(lia) ltac:(lia) eq_refl FCi).
        sep_apply J3. clear J3.
        assert (J4 := lit_xb_give 65536
                        (sublist (ioff + lh + (ls - 65536)) (ioff + lh + (ls - 65536) + 65536) ic) xl p
                        ltac:(rewrite Zlength_sublist; lia)
                        ltac:(unfold LITEXTRA_N, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH; lia) Hxl FCx).
        gather_SEP 1 15.
        replace_SEP 0 (field_at Ews t_dctx (DOT _litExtraBuffer)
                         (sublist (ioff + lh + (ls - 65536)) (ioff + lh + (ls - 65536) + 65536) ic ++
                          sublist 65536 LITEXTRA_N xl) p).
        { go_lower. apply J4. }
        clear J4.
        forward. forward. forward. forward.
        Exists (lh + ls) (sublist 0 lb oc1 ++ sublist (ioff + lh) (ioff + lh + (ls - 65536)) ic ++
                          sublist (lb + (ls - 65536)) (Zlength oc) oc1)
               (LSplit lb) (slice s lh ls) oh x2
               (sublist (ls - LITBUFFEREXTRASIZE) ls (slice s lh ls) ++ sublist 65536 LITEXTRA_N lxb).
        rewrite lit_not_err by lia. unfold litfields, lit_extra_at. rewrite lit_slice_len by lia.
        assert (Ex: sublist (ioff + lh + (ls - 65536)) (ioff + lh + (ls - 65536) + 65536) ic =
                    zbytes (sublist (ls - LITBUFFEREXTRASIZE) ls (slice s lh ls))).
        { replace (ioff + lh + (ls - 65536) + 65536) with (ioff + lh + ls) by lia.
          unfold LITBUFFEREXTRASIZE. apply lit_win_sub2; auto; lia. }
        rewrite Ex. clear Ex. subst xl. rewrite lit_xb_app.
        assert (Hsl: Zlength (slice s lh ls) = ls) by (apply lit_slice_len; lia).
        destruct (lit_xb_ok (sublist (ls - LITBUFFEREXTRASIZE) ls (slice s lh ls)) lxb 65536) as [XB1 XB2].
        { rewrite Zlength_sublist by (unfold LITBUFFEREXTRASIZE; lia). unfold LITBUFFEREXTRASIZE; lia. }
        { unfold LITEXTRA_N, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH; lia. }
        { exact Hlxb. }
        { unfold bytes_ok. apply Forall_sublist. apply lit_bytes_slice; auto; lia. }
        { exact Hlxbb. }
        assert (XS: sublist 0 LITBUFFEREXTRASIZE
                      (sublist (ls - LITBUFFEREXTRASIZE) ls (slice s lh ls) ++ sublist 65536 LITEXTRA_N lxb) =
                    sublist (ls - LITBUFFEREXTRASIZE) ls (slice s lh ls)).
        { rewrite sublist_app1 by (rewrite ?Zlength_sublist; unfold LITBUFFEREXTRASIZE; lia).
          apply sublist_same; [reflexivity | rewrite Zlength_sublist; unfold LITBUFFEREXTRASIZE; lia]. }
        assert (W2: sublist (ioff + lh) (ioff + lh + (ls - 65536)) ic =
                    zbytes (sublist 0 (ls - LITBUFFEREXTRASIZE) (slice s lh ls))).
        { rewrite <- (Z.add_0_r (ioff + lh)) at 1. unfold LITBUFFEREXTRASIZE. apply lit_win_sub2; auto; lia. }
        pose proof (proj2 (proj2 (LXC ltac:(lia) Hlt)) HL) as XE.
        change LITBUFFEREXTRASIZE with 65536 in XE. change WILDCOPY_OVERLENGTH with 32 in XE.
        replace (d + Z.min bsm cap - ls + 65536 - 32) with lb in XE by (unfold lb; lia).
        rewrite <- (lit_cwr_eq oc1 ic (Zlength oc) lb (ioff + lh) (ls - 65536)
                      (sublist 0 (ls - 65536) (slice s lh ls)) AL W2) in XE
          by (rewrite Zlength_sublist by lia; lia).
        clear LXR LXC.
        replace (d + Z.min bsm cap - 32) with (lb + (ls - LITBUFFEREXTRASIZE))
          by (unfold lb, LITBUFFEREXTRASIZE; lia).
        rewrite HL. cbn [loc_code].
        entailer!.
        assert (DLs: decode_literals oh s bsm = Some (slice s lh ls, lh + ls, oh)).
        { rewrite DL. replace (ls >? bsm) with false by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
          replace (lh + ls >? Zlength s) with false by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
          reflexivity. }
        rewrite DLs.
        assert (Hlen: Zlength (sublist (ioff + lh) (ioff + lh + (ls - 65536)) ic) = ls - 65536)
          by (rewrite Zlength_sublist; lia).
        split; [apply lit_unch_after; auto; unfold lb; lia |].
        split.
        { intros Hs1; apply lit_unch_after; auto.
          all: unfold lb; try rewrite (Z.min_comm cap bsm); lia. }
        split; [| split; [left; reflexivity | split; [intros BC BI; apply lit_bc_mid; auto |]]].
        2: { intros _. apply lit_dk_after; auto; try (unfold lb; lia).
             apply (lit_win_bv ic ioff _ _ s); auto; lia. }
        intros _. unfold lits_ok, lits_at, lit_pos, lit_slack_def; cbn [oa_d oa_cap iw_N iw_c iw_s].
        rewrite DLs. rewrite lit_slice_len by lia.
        subst lb. unfold ZSTD_BLOCKSIZE_MAX, WILDCOPY_OVERLENGTH, LITBUFFEREXTRASIZE in *.
        repeat split; try lia.
        * apply lit_bytes_slice; auto; lia.
        * replace (sublist (d + Z.min bsm cap - ls + 65504) (d + Z.min bsm cap - ls + 65504 + (ls - 65536))
                    (sublist 0 (d + Z.min bsm cap - ls + 65504) oc1 ++
                     sublist (ioff + lh) (ioff + lh + (ls - 65536)) ic ++
                     sublist (d + Z.min bsm cap - ls + 65504 + (ls - 65536)) (Zlength oc) oc1))
            with (sublist (ioff + lh) (ioff + lh + (ls - 65536)) ic) by list_solve.
          rewrite <- (Z.add_0_r (ioff + lh)) at 1. apply lit_win_sub2; auto; lia.
        * destruct oh; auto.
        * replace (sublist (d + Z.min bsm cap - ls + 65504 + (ls - 65536)) (d + Z.min bsm cap - ls + 65504 + (ls - 65536) + 32)
                    (sublist 0 (d + Z.min bsm cap - ls + 65504) oc1 ++
                     sublist (ioff + lh) (ioff + lh + (ls - 65536)) ic ++
                     sublist (d + Z.min bsm cap - ls + 65504 + (ls - 65536)) (Zlength oc) oc1))
            with (sublist (d + Z.min bsm cap - 32) (d + Z.min bsm cap) oc1).
          { apply AS2; auto. }
          replace (d + Z.min bsm cap - ls + 65504 + (ls - 65536)) with (d + Z.min bsm cap - 32) by lia.
          list_solve.
    - (* not split: the literals in dst or in litExtraBuffer *)
      assert (HL: (alloc_loc streaming cap bsm ls = LOC_IN_DST /\ streaming = 0 /\ bsm + 32 + ls + 32 < cap) \/
                  (alloc_loc streaming cap bsm ls = LOC_NOT_IN_DST /\ ls <= 65536)).
      { destruct (lit_alloc_cases streaming cap bsm ls) as [? | [? | (E & _)]]; auto.
        rewrite E in H5. exfalso. apply H5. reflexivity. }
      assert_PROP (field_compatible (tarray tuchar (Zlength oc)) [] ob) as FCo by entailer!.
      assert_PROP (field_compatible (tarray tuchar (Zlength ic)) [] ib) as FCi by entailer!.
      assert_PROP (field_compatible t_dctx (DOT _litBuffer) p) as FCx by entailer!.
      apply (lit_fc _litBuffer _litExtraBuffer) in FCx; [| apply compute_in_members_true_iff; reflexivity].
      assert (Pib: isptr ib) by (destruct FCi; auto).
      assert (DLs: decode_literals oh s bsm = Some (slice s lh ls, lh + ls, oh)).
      { rewrite DL. replace (ls >? bsm) with false by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
        replace (lh + ls >? Zlength s) with false by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
        reflexivity. }
      assert (Ew := lit_win_sub ic ioff lh ls s Hwin Hioff Hin ltac:(lia) ltac:(lia) H4).
      rewrite (lit_split3 ish (Zlength ic) (ioff + lh) ls ic ib) by (auto; lia).
      Intros.
      destruct HL as [(HL & Hs0 & Hroom) | (HL & Hsmall)].
      + (* in dst, after the block's room *)
        replace (alloc_buf p ob streaming cap bsm ls d (Z.min bsm cap) 1)
          with (offset_val (d + bsm + 32) ob, offset_val (d + bsm + 32 + ls) ob)
          by (unfold alloc_buf; rewrite HL; reflexivity).
        cbn [fst snd].
        forward.
        rewrite (lit_split3 osh (Zlength oc) (d + bsm + 32) ls oc1 ob) by (auto; lia).
        Intros.
        sep_apply (data_at_data_at_ osh (tarray tuchar ls) (sublist (d + bsm + 32) (d + bsm + 32 + ls) oc1)
                     (offset_val (d + bsm + 32) ob)).
        forward_call (ish, osh, offset_val (ioff + lh) ib, offset_val (d + bsm + 32) ob,
                      existT (fun t => reptype t) (tarray tuchar ls) (sublist (ioff + lh) (ioff + lh + ls) ic)).
        { cbn [projT1 projT2]. split; [rewrite sizeof_tarray_tuchar by lia; rep_lia |].
          apply memcpy_ok_bytes; [list_solve | apply (lit_win_bv ic ioff _ _ s); auto; lia]. }
        cbn [projT1 projT2].
        assert (J1 := lit_join3_same ish (Zlength ic) (ioff + lh) ls ic ib
                        ltac:(lia) ltac:(lia) ltac:(lia) eq_refl FCi).
        sep_apply J1. clear J1.
        assert (J2 := lit_join3 osh (Zlength oc) (d + bsm + 32) ls oc1
                        (sublist (ioff + lh) (ioff + lh + ls) ic) ob
                        ltac:(lia) ltac:(lia) ltac:(lia) AL ltac:(rewrite Zlength_sublist; lia) FCo).
        sep_apply J2. clear J2.
        forward. forward. forward. forward.
        Exists (lh + ls) (sublist 0 (d + bsm + 32) oc1 ++ sublist (ioff + lh) (ioff + lh + ls) ic ++
                          sublist (d + bsm + 32 + ls) (Zlength oc) oc1)
               (LDst (d + bsm + 32)) (slice s lh ls) oh x2 lxb.
        rewrite lit_not_err by lia. unfold litfields. rewrite lit_slice_len by lia.
        pose proof (proj1 (LXC ltac:(lia) Hlt) HL) as XE.
        change WILDCOPY_OVERLENGTH with 32 in XE.
        rewrite <- (lit_cwr_eq oc1 ic (Zlength oc) (d + bsm + 32) (ioff + lh) ls (slice s lh ls) AL Ew) in XE
          by (apply lit_slice_len; lia).
        clear LXR LXC.
        rewrite HL. cbn [loc_code].
        entailer!.
        rewrite DLs.
        split; [apply lit_unch_after; auto; try lia; rewrite Zlength_sublist; lia |].
        split; [| split; [left; reflexivity | split; [intros BC BI; apply lit_bc_mid; auto |]]].
        2: { intros _. apply lit_dk_after; auto; try lia; [rewrite Zlength_sublist; lia |].
             apply (lit_win_bv ic ioff _ _ s); auto; lia. }
        intros _. unfold lits_ok, lits_at, lit_pos, lit_slack_def; cbn [oa_d oa_cap iw_N iw_c iw_s].
        rewrite DLs. rewrite lit_slice_len by lia.
        specialize (AS1 HL). unfold ZSTD_BLOCKSIZE_MAX, WILDCOPY_OVERLENGTH in *.
        repeat split; try lia.
        * apply lit_bytes_slice; auto; lia.
        * replace (sublist (d + bsm + 32) (d + bsm + 32 + ls)
                    (sublist 0 (d + bsm + 32) oc1 ++ sublist (ioff + lh) (ioff + lh + ls) ic ++
                     sublist (d + bsm + 32 + ls) (Zlength oc) oc1))
            with (sublist (ioff + lh) (ioff + lh + ls) ic) by list_solve.
          exact Ew.
        * destruct oh; auto.
        * replace (sublist (d + bsm + 32 + ls) (d + bsm + 32 + ls + 32)
                    (sublist 0 (d + bsm + 32) oc1 ++ sublist (ioff + lh) (ioff + lh + ls) ic ++
                     sublist (d + bsm + 32 + ls) (Zlength oc) oc1))
            with (sublist (d + bsm + 32 + ls) (d + bsm + 32 + ls + 32) oc1) by list_solve.
          exact AS1.
      + (* in litExtraBuffer *)
        assert (E1: oc1 = oc) by (apply AE; left; exact HL). subst oc1.
        replace (alloc_buf p ob streaming cap bsm ls d (Z.min bsm cap) 1)
          with (lit_extra p, offset_val ls (lit_extra p))
          by (unfold alloc_buf; rewrite HL; reflexivity).
        cbn [fst snd].
        forward.
        { entailer!. unfold lit_extra. rewrite field_address_offset by auto.
          destruct FCx as [Pp _]. destruct p; try contradiction. exact I. }
        unfold lit_extra_at. Intros.
        assert (Hxl: Zlength (zbytes lxb) = LITEXTRA_N) by (rewrite Zlength_map; exact Hlxb).
        set (xl := zbytes lxb) in *.
        sep_apply (lit_xb_take ls xl p
                     ltac:(unfold LITEXTRA_N, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH; lia) Hxl FCx).
        Intros.
        forward_call (ish, Ews, offset_val (ioff + lh) ib, lit_extra p,
                      existT (fun t => reptype t) (tarray tuchar ls) (sublist (ioff + lh) (ioff + lh + ls) ic)).
        { cbn [projT1 projT2]. split; [rewrite sizeof_tarray_tuchar by lia; rep_lia |].
          apply memcpy_ok_bytes; [list_solve | apply (lit_win_bv ic ioff _ _ s); auto; lia]. }
        cbn [projT1 projT2].
        assert (J1 := lit_join3_same ish (Zlength ic) (ioff + lh) ls ic ib
                        ltac:(lia) ltac:(lia) ltac:(lia) eq_refl FCi).
        sep_apply J1. clear J1.
        assert (J4 := lit_xb_give ls (sublist (ioff + lh) (ioff + lh + ls) ic) xl p
                        ltac:(rewrite Zlength_sublist; lia)
                        ltac:(unfold LITEXTRA_N, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH; lia) Hxl FCx).
        sep_apply J4. clear J4.
        forward. forward. forward. forward.
        Exists (lh + ls) oc LExtra (slice s lh ls) oh x2 (slice s lh ls ++ sublist ls LITEXTRA_N lxb).
        rewrite lit_not_err by lia. unfold litfields, lit_extra_at. rewrite lit_slice_len by lia.
        rewrite Ew. subst xl. rewrite lit_xb_app.
        destruct (lit_xb_ok (slice s lh ls) lxb ls) as [XB1 XB2].
        { apply lit_slice_len; lia. }
        { unfold LITEXTRA_N, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH; lia. }
        { exact Hlxb. }
        { apply lit_bytes_slice; auto; lia. }
        { exact Hlxbb. }
        assert (XS: sublist 0 ls (slice s lh ls ++ sublist ls LITEXTRA_N lxb) = slice s lh ls).
        { assert (Hsl: Zlength (slice s lh ls) = ls) by (apply lit_slice_len; lia).
          rewrite sublist_app1 by lia. apply sublist_same; lia. }
        pose proof (proj1 (proj2 (LXC ltac:(lia) Hlt)) HL) as XE.
        clear LXR LXC.
        rewrite HL. cbn [loc_code].
        entailer!.
        rewrite DLs.
        split; [| left; reflexivity].
        intros _. unfold lits_ok, lits_at, lit_pos; cbn [oa_d oa_cap iw_N iw_c iw_s].
        rewrite DLs. rewrite lit_slice_len by lia.
        unfold ZSTD_BLOCKSIZE_MAX, LITBUFFEREXTRASIZE.
        repeat split; try lia.
        * apply lit_bytes_slice; auto; lia.
        * destruct oh; auto. }
  (* direct reference into the input *)
  assert (Hn: lh + ls + 32 <= Zlength s).
  { rewrite !Int64.add_unsigned in H1.
    rewrite (Int64.unsigned_repr lh), (Int64.unsigned_repr ls), (Int64.unsigned_repr 32) in H1 by rep_lia.
    rewrite (Int64.unsigned_repr (lh + ls)), Int64.unsigned_repr in H1
      by rep_lia.
    rewrite Int64.unsigned_repr in H1 by rep_lia. lia. }
  assert_PROP (isptr ib) as Pib by entailer!.
  forward. rewrite lit_add_l by (destruct ib; try contradiction; exact I). rewrite offset_offset_val.
  forward. forward. forward. rewrite lit_add_l by (destruct ib; try contradiction; exact I).
  rewrite offset_offset_val. forward. forward.
  pose proof (LXR ltac:(unfold WILDCOPY_OVERLENGTH; lia)) as XE. clear LXR LXC.
  Exists (lh + ls) oc1 (LIn (ioff + lh)) (slice s lh ls) oh x2 lxb.
  rewrite lit_not_err by lia. unfold litfields.
  rewrite lit_slice_len by lia.
  entailer!.
  assert (DLs: decode_literals oh s bsm = Some (slice s lh ls, lh + ls, oh)).
  { rewrite DL. replace (ls >? bsm) with false by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
    replace (lh + ls >? Zlength s) with false by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
    reflexivity. }
  rewrite DLs.
  split; [| left; reflexivity].
  intros _. unfold lits_ok, lits_at, lit_pos, lit_slack_def; cbn [oa_d oa_cap iw_N iw_c iw_s].
  rewrite DLs. rewrite lit_slice_len by lia. unfold ZSTD_BLOCKSIZE_MAX, WILDCOPY_OVERLENGTH.
  repeat split; try lia.
  - apply lit_bytes_slice; auto; lia.
  - apply lit_win_sub; auto; lia.
  - apply (lit_win_bv ic ioff _ _ s); auto; lia.
  - destruct oh; auto.
Qed.
