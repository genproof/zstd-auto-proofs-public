(* ZSTD_decodeLiteralsBlock, set_compressed / set_repeat, part 4: the end of the arm (HUF_isError check, the
   literal fields, the result) from lit_T, with the postcondition for the output array the function got: the facts
   about the array after ZSTD_allocateLiteralsBuffer carry over (lit_o1), the exact clause by BlkLIT3Exact.lx_huf. *)
Require Export Zstd.proof.dec.v3.B.BlkLIT3Comp3.
Local Open Scope logic.
Local Ltac solve_load_rule_evaluation ::= lit_slre.

(* the output array o1 after ZSTD_allocateLiteralsBuffer (n literals, split = 0) and the one the function got (o0) *)
Definition lit_o1 (o0 o1: outarr) (streaming bsm n: Z) : Prop :=
  oa_sh o1 = oa_sh o0 /\ oa_base o1 = oa_base o0 /\ oa_N o1 = oa_N o0 /\ oa_d o1 = oa_d o0 /\
  oa_cap o1 = oa_cap o0 /\
  oa_c o1 = alloc_out (oa_c o0) streaming (oa_cap o0) bsm n (oa_d o0) (Z.min bsm (oa_cap o0)) 0.

(* the literal fields at the end (success): litExtraBuffer holds exactly lxb2 *)
Lemma lit_fields_fold (p ob ib: val) (streaming cap bsm n d: Z) (i: inwin) (oc2 ex2: list val) (l lxb2: list Z) :
  lit_tok streaming cap bsm n d i oc2 ex2 l -> ex2 = zbytes lxb2 -> Zlength lxb2 = LITEXTRA_N -> bytes_ok lxb2 ->
  field_at Ews t_dctx (DOT _litPtr) (fst (alloc_buf p ob streaming cap bsm n d (Z.min bsm cap) 1)) p *
  field_at Ews t_dctx (DOT _litSize) (Vlong (Int64.repr n)) p *
  field_at Ews t_dctx (DOT _litBuffer) (fst (alloc_buf p ob streaming cap bsm n d (Z.min bsm cap) 1)) p *
  field_at Ews t_dctx (DOT _litBufferEnd) (snd (alloc_buf p ob streaming cap bsm n d (Z.min bsm cap) 1)) p *
  field_at Ews t_dctx (DOT _litBufferLocation) (Vint (Int.repr (alloc_loc streaming cap bsm n))) p *
  field_at Ews t_dctx (DOT _litExtraBuffer) ex2 p
  |-- litfields p ob ib (lit_lloc streaming cap bsm n d) l lxb2.
Proof.
  intros (Hat & Hz & Hdst & Hx & _) Hex Hlx Hbx. subst ex2. unfold litfields, lit_extra_at. rewrite Hz.
  assert (Hbl: bytes_ok l) by (destruct Hat as [Hb _]; exact Hb).
  unfold lit_lloc, alloc_buf in *.
  destruct (lit_loc3 streaming cap bsm n) as [E | [E | E]]; rewrite E in *;
    unfold LOC_IN_DST, LOC_NOT_IN_DST, LOC_SPLIT in *; cbn [Z.eqb Pos.eqb fst snd loc_code] in *.
  - entailer!.
  - unfold lits_at in Hat. rewrite Hz in Hat. destruct Hat as (_ & Hn & Hle).
    assert (Hs: sublist 0 n lxb2 = l).
    { apply lit_zbytes_inj; [apply lit_bytes_sub, Hbx | exact Hbl | rewrite <- sublist_map; exact Hx]. }
    entailer!.
  - unfold lits_at in Hat. rewrite Hz in Hat. destruct Hat as (_ & Hn & Hsp & _).
    assert (Hs: sublist 0 LITBUFFEREXTRASIZE lxb2 = sublist (n - LITBUFFEREXTRASIZE) n l).
    { apply lit_zbytes_inj; [apply lit_bytes_sub, Hbx | apply lit_bytes_sub, Hbl | rewrite <- sublist_map; exact Hx]. }
    unfold LITEXTRA_N, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *.
    replace (d + Z.min bsm cap - n + 65536 - 32 + (n - 65536)) with (d + Z.min bsm cap - 32) by lia.
    entailer!.
Qed.

(* litExtraBuffer at the end holds bytes *)
Lemma lit_lxb2_ok (streaming cap bsm n: Z) (lxb l: list Z) :
  Zlength lxb = LITEXTRA_N -> bytes_ok lxb -> bytes_ok l -> Zlength l = n -> 0 <= n ->
  (alloc_loc streaming cap bsm n = LOC_NOT_IN_DST -> n <= LITBUFFEREXTRASIZE) ->
  (alloc_loc streaming cap bsm n = LOC_SPLIT -> LITBUFFEREXTRASIZE < n) ->
  Zlength (lit_lxb2 streaming cap bsm n lxb l) = LITEXTRA_N /\ bytes_ok (lit_lxb2 streaming cap bsm n lxb l).
Proof.
  intros Hlx Hbx Hbl Hl Hn HX HS. unfold lit_lxb2.
  unfold LITEXTRA_N, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *.
  destruct (lit_loc3 streaming cap bsm n) as [E | [E | E]]; rewrite E in *;
    unfold LOC_IN_DST, LOC_NOT_IN_DST, LOC_SPLIT in *; cbn [Z.eqb Pos.eqb] in *.
  - auto.
  - specialize (HX eq_refl). split; [rewrite Zlength_app, Zlength_sublist by lia; lia |].
    unfold bytes_ok in *. apply Forall_app. split; [exact Hbl | apply Forall_sublist; exact Hbx].
  - specialize (HS eq_refl). split; [rewrite Zlength_app, !Zlength_sublist by lia; lia |].
    unfold bytes_ok in *. apply Forall_app. split; apply Forall_sublist; assumption.
Qed.

(* the model's literals section fails when the Huffman part fails (the header's checks passed) *)
Lemma lit_xb_none_huf (ox: option ddx) (oh: option huf_table) (x2: bool) (s: list Z) (bsm cap e lh n cs r: Z)
    (single: bool) (st: bool) (l: list Z) (ht: huf_table) :
  bytes_ok s -> lit_kfacts oh bsm cap e s lh n cs single -> is_error_code r = true ->
  lit_xfacts e ox oh x2 single (sublist lh (lh + cs) s) n r l ht -> ox = None ->
  xb_lits (option_map (xhuf_of x2) oh) s bsm (Z.min bsm cap) st = None.
Proof.
  intros Hb (He & Hty & Hx & H5 & Hh & Hlh & Hcs & Hsg & Hn & Hs6 & Hcl) Er XF Hox.
  pose proof (Z.le_min_l bsm cap). pose proof (lit_hdr_range s lh n cs single Hb H5 Hh) as (_ & Hn0 & _ & _).
  rewrite (xl_comp (option_map (xhuf_of x2) oh) s bsm (Z.min bsm cap) st e lh n cs single Hb H5 Hty He
             ltac:(intros E; destruct oh; [discriminate | exfalso; apply Hx; auto]) Hh).
  replace (n >? bsm) with false by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
  replace (andb (negb single) (n <? 6)) with false
    by (destruct single; [reflexivity | cbn [negb andb]; symmetry; apply Z.ltb_ge; auto]).
  replace (cs + lh >? Zlength s) with false by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
  replace (Z.min bsm cap <? n) with false by (symmetry; apply Z.ltb_ge; lia).
  specialize (XF Hox). destruct (x_lits_huf _ _ _ _ _) as [[l0 t0] |]; [| reflexivity].
  destruct XF as (-> & _). unfold is_error_code in Er. apply Z.ltb_lt in Er. lia.
Qed.

(* the exact clause on success (lit_oc2 / lit_lxb2 from the array after ZSTD_allocateLiteralsBuffer) *)
Lemma lit_exact_ok (ox: option ddx) (oh: option huf_table) (x2: bool) (lxb: list Z) (o: outarr) (i: inwin)
    (bsm streaming e lh n cs r: Z) (single: bool) (l: list Z) (ht: huf_table) (oc2: list val) :
  lx_hyps o i bsm streaming lxb -> lit_kfacts oh bsm (oa_cap o) e (iw_s i) lh n cs single ->
  is_error_code r = false -> Zlength l = n ->
  lit_xfacts e ox oh x2 single (sublist lh (lh + cs) (iw_s i)) n r l ht ->
  oc2 = lit_oc2 streaming (oa_cap o) bsm n (oa_d o)
          (alloc_out (oa_c o) streaming (oa_cap o) bsm n (oa_d o) (Z.min bsm (oa_cap o)) 0) l ->
  ox = None ->
  lits_exact (option_map (xhuf_of x2) oh) lxb o i bsm streaming (cs + lh) oc2
    (lit_lloc streaming (oa_cap o) bsm n (oa_d o)) l
    (option_map (xhuf_of (lit_x2' e x2 single n (sublist lh (lh + cs) (iw_s i)))) (Some ht))
    (lit_lxb2 streaming (oa_cap o) bsm n lxb l).
Proof.
  intros LX HK Er Hl XF Hoc Hox.
  pose proof LX as (Hoo & Hio & _ & _ & _ & _).
  destruct Hoo as (_ & HoN & _ & Hd & Hcap & Hdc).
  pose proof HK as (He & Hty & Hx & H5 & Hh & Hlh & Hcs & Hsg & Hn & Hs6 & Hcl).
  specialize (XF Hox).
  destruct (x_lits_huf (option_map (xhuf_of x2) oh) e single (sublist lh (lh + cs) (iw_s i)) n) as [[l0 t0] |] eqn:XL;
    [| rewrite XF in Er; discriminate].
  destruct XF as (_ & <- & Ht0).
  assert (Hn0: 0 <= n) by (rewrite <- Hl; apply Zlength_nonneg).
  pose proof (Z.le_min_l bsm (oa_cap o)).
  destruct (lx_huf (option_map (xhuf_of x2) oh) lxb o i bsm streaming e lh n cs single l t0 LX H5 Hty He
              ltac:(intros E; destruct oh; [discriminate | exfalso; apply Hx; auto]) Hh ltac:(lia) Hs6 Hcl
              Hn XL Hl) as (C1 & C2 & C3).
  rewrite Ht0 in C1, C2, C3. cbn [option_map]. replace (cs + lh) with (lh + cs) by lia.
  destruct (lit_alloc_out (oa_c o) streaming (oa_cap o) bsm n (oa_d o) 0 Hd ltac:(lia) ltac:(lia))
    as (_ & _ & _ & _ & _ & _ & _ & AE).
  subst oc2. unfold lit_lloc, lit_oc2, lit_lxb2.
  destruct (lit_loc3 streaming (oa_cap o) bsm n) as [E | [E | E]]; rewrite E in *;
    unfold LOC_IN_DST, LOC_NOT_IN_DST, LOC_SPLIT in *; cbn [Z.eqb Pos.eqb] in *.
  - apply C1; reflexivity.
  - rewrite AE by auto. apply C2; reflexivity.
  - rewrite AE by (right; split; [reflexivity | discriminate]). apply C3; reflexivity.
Qed.

Lemma lit_tail_rest (Espec: OracleKind) (gv: globals) (p: val) (fs: fstate) (ox: option ddx) (oh: option huf_table)
    (x2: bool) (lxb: list Z) (bsm streaming: Z) (W: list ptr_witness) (o0 o: outarr) (i: inwin) (e lh n cs: Z)
    (single: bool) (r: Z) (oc1 ex1: list val) (l: list Z) (ht: huf_table) :
  lit_hyps fs oh bsm streaming W o0 i -> lit_hyps fs oh bsm streaming W o i -> lit_o1 o0 o streaming bsm n ->
  lit_kfacts oh bsm (oa_cap o) e (iw_s i) lh n cs single -> Zlength lxb = LITEXTRA_N -> bytes_ok lxb ->
  lit_hfacts e ox oh x2 single (sublist lh (lh + cs) (iw_s i)) streaming (oa_cap o) bsm n (oa_d o) (oa_c o) oc1 lxb ex1
    r l ht ->
  semax lit_Delta (lit_T gv p fs ox lxb bsm streaming W o i e lh n cs single r ht
                     (lit_x2' e x2 single n (sublist lh (lh + cs) (iw_s i))) l) lit_rest
    (overridePost FF (switch_ret_assert (lit_R gv p fs ox oh x2 lxb bsm streaming W o0 i))).
Proof.
  intros HY0 HY HO HK Hlxb Hlxbb HF.
  assert (LX: lx_hyps o0 i bsm streaming lxb).
  { destruct HY0 as (A1 & A2 & A3 & A4 & A5 & _). exact (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 Hlxb))))). }
  apply semax_post with (R' := switch_ret_assert (lit_R gv p fs ox oh x2 lxb bsm streaming W o0 i));
    [ intros; unfold lit_R, switch_ret_assert, frame_ret_assert, function_body_ret_assert, overridePost; simpl;
      first [normalize; fail | intros ?; apply andp_left2, derives_refl | apply andp_left2, derives_refl] .. | ].
  unfold lit_R, lit_post.
  pose proof HK as HK0.
  destruct o0 as [osh0 ob0 oN0 oc0 d0 cap0]; destruct o as [osh ob oN oc d cap]; destruct i as [ish ib iN ic ioff s].
  destruct HO as (E1 & E2 & E3 & E4 & E5 & E6).
  cbn [oa_sh oa_base oa_N oa_c oa_d oa_cap iw_sh iw_base iw_N iw_c iw_off iw_s] in *.
  subst osh0 ob0 oN0 d0 cap0.
  destruct HY0 as ((_ & HoN0 & _) & _).
  destruct HY as (Hoo & Hio & Hstr & Hbsm0 & Hsb & Hfp & Hfd & Hcold & HW & Hoh & Hs2).
  destruct Hoo as (Hosh & HoN & HoN32 & Hd & Hcap & Hdc).
  destruct Hio as (Hish & Hioff & Hin & HiN32 & HiN & _ & Hbytes & Hwin).
  cbn [oa_sh oa_base oa_N oa_c oa_d oa_cap iw_sh iw_base iw_N iw_c iw_off iw_s] in *.
  subst iN oN.
  assert (Hbsm: 0 <= bsm <= 131072) by (unfold ZSTD_BLOCKSIZE_MAX in Hbsm0; lia).
  destruct HK as (He & Hty & Hx & H5 & Hh & Hlh & Hcs & Hsg & Hn & Hs6 & Hcl).
  pose proof (lit_hdr_range s lh n cs single Hbytes H5 Hh) as (_ & Hn0 & _ & _).
  destruct (lit_alloc_out oc0 streaming cap bsm n d 0 Hd ltac:(lia) ltac:(pose proof (Z.le_min_l bsm cap); lia))
    as (AL & AU & AUs & AB & AD & _ & _ & _).
  rewrite <- E6 in AL, AU, AUs, AB, AD.
  unfold lit_hfacts in HF. cbv zeta in HF.
  destruct HF as (Hr & Hoc1 & Hex1 & Hbx1 & Hbo1 & _ & HSc & He3 & Hmod & _ & XF).
  assert (DL: decode_literals oh s bsm =
    match lit_model e oh (negb single) (sublist lh (lh + cs) s) n with
    | Some (l0, t) => Some (l0, lh + cs, Some t) | None => None end).
  { rewrite (lit_dl_comp oh s bsm e lh n cs single H5 Hty He Hx Hh ltac:(lia) ltac:(lia)).
    replace (n >? bsm) with false by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; pose proof (Z.le_min_l bsm cap); lia).
    replace (andb (negb single) (n <? 6)) with false
      by (destruct single; [reflexivity | cbn [negb andb]; symmetry; apply Z.ltb_ge; auto]).
    replace (cs + lh >? Zlength s) with false by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
    reflexivity. }
  unfold lit_T, lit_KL. cbn [oa_sh oa_base oa_N oa_c oa_d oa_cap iw_sh iw_base iw_N iw_c iw_off iw_s].
  Intros oc2 ex2.
  match goal with H: is_error_code r = false -> oc2 = _ /\ _ |- _ => rename H into HX2 end.
  match goal with H: is_error_code r = false -> lit_dk _ _ |- _ => rename H into HD2 end.
  match goal with H: is_error_code r = false -> lit_tok _ _ _ _ _ _ _ _ _ |- _ => rename H into HT2 end.
  match goal with H: Zlength oc2 = _ |- _ => rename H into Hl2 end.
  match goal with H: Zlength ex2 = _ |- _ => rename H into Hx2 end.
  match goal with H: byte_cells ex2 |- _ => rename H into Hbx2 end.
  match goal with H: byte_cells oc -> byte_cells oc2 |- _ => rename H into Hbo2 end.
  match goal with H: unchanged_outside oc oc2 d (d + cap) |- _ => rename H into HU2 end.
  match goal with H: streaming = 1 -> unchanged_outside oc oc2 _ _ |- _ => rename H into HS2 end.
  (* the facts about the array the function got *)
  assert (Q1: Zlength oc2 = Zlength oc0) by lia.
  assert (Q2: unchanged_outside oc0 oc2 d (d + cap)) by (apply (lit_unch_trans oc0 oc); auto).
  assert (Q3: streaming = 1 -> unchanged_outside oc0 oc2 d (d + Z.min cap bsm))
    by (intros Hs1; apply (lit_unch_trans oc0 oc); auto).
  assert (Q4: byte_cells oc0 -> byte_cells oc2) by auto.
  assert (Q5: is_error_code r = false -> lit_dk oc0 oc2)
    by (intros Er; apply (lit_dk_trans oc0 oc); auto; rewrite AL in HD2; apply HD2, Er).
  clear HU2 HS2 Hbo2.
  let x := eval cbv [lit_rest lit_tail lit_drop lit_c2 lit_sw f_ZSTD_decodeLiteralsBlock fn_body] in lit_rest in
  change lit_rest with x.
  abbreviate_semax.
  lit_check (is_error_code r = false).
  { entailer!. }
  { forward_call r.
    forward_if.
    - destruct (is_error_code r) eqn:Er;
        [| exfalso; match goal with H: Int.repr 0 <> Int.zero |- _ => apply H; reflexivity end].
      lit_errp.
      Exists (err_code 20) oc2 LExtra (@nil Z) oh x2 lxb.
      rewrite (lit_err_true 20) by lia. destruct (lit_err_val 20) as [LEV LER]; [lia |].
      unfold lit_hpart. rewrite Er.
      entailer!.
      + repeat match goal with |- _ /\ _ => split end;
          try (intros ?; lit_dec_close);
          try (intros Hox; apply lx_err; [apply lit_err_true; lia |]; cbn [iw_s oa_cap];
               eapply lit_xb_none_huf; eauto).
        rewrite DL. destruct (lit_model _ _ _ _ _) as [[l0 t0] |]; [| exact I].
        destruct Hmod as (-> & _). unfold is_error_code in Er. apply Z.ltb_lt in Er. lia.
      + unfold lit_scratch, lit_extra_bytes. Exists ex2.
        sep_apply (field_at_field_at_ Ews t_dctx (DOT _litBuffer)).
        sep_apply (field_at_field_at_ Ews t_dctx (DOT _litBufferEnd)).
        sep_apply (field_at_field_at_ Ews t_dctx (DOT _litBufferLocation)). entailer!.
    - forward. entailer!. destruct (is_error_code r); [discriminate | reflexivity]. }
  Intros.
  match goal with H: is_error_code r = false |- _ => rename H into Hok end.
  destruct (HSc Hok) as (Hrn & Hbl & Hlen & Hht & _).
  pose proof (HT2 Hok) as Htok.
  pose proof (HX2 Hok) as XX.
  destruct (lit_lxb2_ok streaming cap bsm n lxb l Hlxb Hlxbb Hbl Hlen ltac:(lia) (lit_loc_extra streaming cap bsm n)
              (lit_loc_split streaming cap bsm n)) as [Y1 Y2].
  assert (XE: ox = None ->
    lits_exact (option_map (xhuf_of x2) oh) lxb
      {| oa_sh := osh; oa_base := ob; oa_N := Zlength oc0; oa_c := oc0; oa_d := d; oa_cap := cap |}
      {| iw_sh := ish; iw_base := ib; iw_N := Zlength ic; iw_c := ic; iw_off := ioff; iw_s := s |}
      bsm streaming (cs + lh) oc2 (lit_lloc streaming cap bsm n d) l
      (option_map (xhuf_of (lit_x2' e x2 single n (sublist lh (lh + cs) s))) (Some ht))
      (lit_lxb2 streaming cap bsm n lxb l)).
  { apply (lit_exact_ok ox oh x2 lxb _ _ bsm streaming e lh n cs r single l ht oc2 LX HK0 Hok Hlen XF).
    cbn [oa_c oa_cap oa_d]. rewrite <- E6. exact (proj1 XX). }
  clear HX2 HD2 HT2 XF.
  assert_PROP (isptr p) as Pp by (unfold frame_fields; entailer!).
  assert_PROP (isptr ob) as Pob by entailer!.
  assert_PROP (field_compatible t_dctx (DOT _litBuffer) p) as FCb by entailer!.
  destruct (lit_buf_ptr p ob streaming cap bsm n d (Z.min bsm cap) 1 Pob Pp FCb) as [Pb1 Pb2].
  forward. forward. forward.
  unfold lit_hpart. rewrite Hok.
  destruct He as [-> | ->]; cbn [Z.eqb Pos.eqb].
  - Intros. forward. apply semax_if_seq. unfold MORE_COMMANDS, abbreviate. clear MORE_COMMANDS.
    forward_if; [forward; forward | lit_false].
    assert (FC0: field_compatible t_dctx [] p)
      by (pose proof FCb as X; apply field_compatible_cons in X; destruct X as [_ X]; exact X).
    assert (HC: ctx_huf p = offset_val (32 + 10264) p).
    { unfold ctx_huf. rewrite field_address_offset by auto with field_compatible. reflexivity. }
    assert (Hcok: is_error_code (cs + lh) = false) by (unfold is_error_code; apply Z.ltb_ge; rep_lia).
    Exists (cs + lh) oc2 (lit_lloc streaming cap bsm (Zlength l) d) l (Some ht)
      (lit_x2' 2 x2 single (Zlength l) (sublist lh (lh + cs) s)) (lit_lxb2 streaming cap bsm (Zlength l) lxb l).
    entailer!.
    + repeat match goal with |- _ /\ _ => split end;
        try (intros _; eapply lit_final_ok; eauto; lia);
        try (destruct (decode_literals oh s bsm) as [[[? ?] ?] |]; auto; fail);
        try (intros HX; exfalso; first [rewrite Hcok in HX | idtac]; discriminate);
        try (intros _; apply (Q5 Hok)); try exact XE.
    + rewrite Hcok. unfold tabs_huf. Exists (offset_val (32 + 10264) p) true.
      sep_apply (lit_fields_fold p ob ib streaming cap bsm (Zlength l) d _ oc2 ex2 l (lit_lxb2 streaming cap bsm (Zlength l) lxb l)
                   Htok (proj2 XX) Y1 Y2).
      entailer!.
  - unfold tabs_huf. Intros hp w. forward.
    apply semax_if_seq. unfold MORE_COMMANDS, abbreviate. clear MORE_COMMANDS.
    forward_if; [lit_false | forward].
    assert (Hcok: is_error_code (cs + lh) = false) by (unfold is_error_code; apply Z.ltb_ge; rep_lia).
    Exists (cs + lh) oc2 (lit_lloc streaming cap bsm (Zlength l) d) l (Some ht)
      (lit_x2' 3 x2 single (Zlength l) (sublist lh (lh + cs) s)) (lit_lxb2 streaming cap bsm (Zlength l) lxb l).
    entailer!.
    + repeat match goal with |- _ /\ _ => split end;
        try (intros _; eapply lit_final_ok; eauto; lia);
        try (destruct (decode_literals oh s bsm) as [[[? ?] ?] |]; auto; fail);
        try (intros HX; exfalso; first [rewrite Hcok in HX | idtac]; discriminate);
        try (intros _; apply (Q5 Hok)); try exact XE.
    + rewrite Hcok. unfold tabs_huf. Exists hp w.
      sep_apply (lit_fields_fold p ob ib streaming cap bsm (Zlength l) d _ oc2 ex2 l (lit_lxb2 streaming cap bsm (Zlength l) lxb l)
                   Htok (proj2 XX) Y1 Y2).
      entailer!.
Qed.
