(* ZSTD_decodeLiteralsBlock, set_compressed / set_repeat, part 2: the Huffman call (one of the four decoders) from
   lit_K to lit_J (BlkLIT3Comp1.v), with the facts of the decoders' specifications, exactly as model/ExHuf.v's
   x_lits_huf (lit_xfacts). *)
Require Export Zstd.proof.dec.v3.B.BlkLIT3Comp1.
Local Open Scope logic.
Local Ltac solve_load_rule_evaluation ::= lit_slre.

Lemma lit_huf_gen (Espec: OracleKind) (gv: globals) (p: val) (ox: option ddx) (oh: option huf_table) (x2: bool)
    (bsm streaming: Z) (ob: val) (d cap: Z) (ib: val) (ish: share) (ic: list val) (ioff: Z) (s: list Z)
    (e lh n cs: Z) (single: bool) (sho: share) (db: val) (dc: list val) (dd: Z) (Fr: mpred) :
  (e = 2 \/ e = 3) -> (e = 3 -> oh <> None) -> match oh with Some ht => huf_ok ht | None => True end ->
  0 <= lh -> 0 <= cs -> cs + lh <= Zlength s -> win_ok ish (Zlength ic) ic ioff (Zlength s) s ->
  Zlength s <= 131072 -> 0 <= n <= 131072 -> (single = false -> 6 <= n) ->
  writable_share sho -> 0 <= dd -> dd + n <= Zlength dc -> 1 <= Zlength dc ->
  semax lit_Delta
    (PROPx [] (LOCALx (lit_KL gv p bsm streaming e ob d cap ib ioff s lh n cs single)
      (SEPx (tabs_huf gv p ox oh x2 :: dent_of dent_def gv ox :: field_at_ Ews t_dctx (DOT _workspace) p ::
             zstd_globals gv :: data_at sho (tarray tuchar (Zlength dc)) dc db ::
             data_at ish (tarray tuchar (Zlength ic)) ic ib ::
             field_at Ews t_dctx (DOT _litBuffer) (offset_val dd db) p :: Fr :: nil))))
    lit_huf
    (normal_ret_assert (EX r: Z, EX dc1: list val, EX l: list Z, EX ht: huf_table,
      PROPx [lit_gfacts e ox oh x2 single (sublist lh (lh + cs) s) n dd dc dc1 r l ht]
      (LOCALx (temp _hufSuccess (Vlong (Int64.repr r)) :: lit_KL gv p bsm streaming e ob d cap ib ioff s lh n cs single)
      (SEPx (lit_hpart gv p ox e r ht (lit_x2' e x2 single n (sublist lh (lh + cs) s)) :: dent_of dent_def gv ox ::
             field_at_ Ews t_dctx (DOT _workspace) p ::
             zstd_globals gv :: data_at sho (tarray tuchar (Zlength dc)) dc1 db ::
             data_at ish (tarray tuchar (Zlength ic)) ic ib ::
             field_at Ews t_dctx (DOT _litBuffer) (offset_val dd db) p :: Fr :: nil))))%assert).
Proof.
  intros He Hx Hoh Hlh Hcs Hcl Hwin Hs Hn Hs6 Hsho Hdd Hdn H1dc.
  set (s' := sublist lh (lh + cs) s).
  assert (Hs': Zlength s' = cs) by (unfold s'; rewrite Zlength_sublist by lia; lia).
  assert (Hw': win_ok ish (Zlength ic) ic (ioff + lh) (Zlength s') s').
  { destruct Hwin as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8).
    rewrite Hs'. repeat split; auto; try lia.
    - unfold s', bytes_ok. apply Forall_sublist. exact W7.
    - unfold s'.
      replace (sublist (ioff + lh) (ioff + lh + cs) ic) with
        (sublist lh (lh + cs) (sublist ioff (ioff + Zlength s) ic))
        by (rewrite sublist_sublist by lia; f_equal; lia).
      rewrite W8. apply sublist_map. }
  assert (Hsb': Zlength s' <= ZSTD_BLOCKSIZE_MAX) by (unfold ZSTD_BLOCKSIZE_MAX; lia).
  assert (Hnb: n <= ZSTD_BLOCKSIZE_MAX) by (unfold ZSTD_BLOCKSIZE_MAX; lia).
  unfold lit_KL.
  assert_PROP (isptr db /\ isptr ib) as Pdi by entailer!. destruct Pdi as [Pdb Pib].
  cbv [lit_huf lit_drop lit_c2 lit_sw f_ZSTD_decodeLiteralsBlock fn_body].
  forward_if.
  - (* set_repeat *)
    subst e. destruct oh as [ht |]; [| exfalso; apply Hx; auto].
    sep_apply (lit_tab3 gv p ox ht x2). Intros hp xh. rename H into Hxh.
    assert_PROP (isptr hp) as Php by (sep_apply lit_hufdtx_ptr; entailer!).
    forward_if.
    + forward. forward.
      replace (Vlong (Int64.repr cs)) with (Vlong (Int64.repr (Zlength s'))) by (rewrite Hs'; reflexivity).
      forward_call (gv, Ews, hp, ht, xh, sho, db, dc, dd, n, ish, ib, Zlength ic, ic, ioff + lh, s').
      all: try (match goal with |- 1 <= Zlength _ => assumption end).
      Intros vret. destruct vret as [r dc1]; simpl fst in *; simpl snd in *.
      forward.
      destruct single; [| exfalso; auto].
      match goal with H1: out_after _ _ _ _, HB: byte_cells _ -> byte_cells _,
                      H3: match huf_lits_with _ _ _ _ with _ => _ end,
                      H4: match x_huf_decode _ _ _ _ with _ => _ end |- _ =>
        destruct (lit_gf3 ox (Some ht) x2 xh true ht s' n dd dc dc1 r Hdd Hn Hdn Hoh eq_refl Hxh
                    ltac:(assumption) H1 HB H3 H4) as [l GF] end.
      sep_apply (modus_ponens_wand (field_at Ews t_dctx (DOT _HUFptr) hp p * hufdt_x_at xh Ews ht hp)).
      Exists r dc1 l ht. rewrite Hs'. entailer!.
      unfold lit_hpart, lit_x2'. cbn [Z.eqb Pos.eqb]. destruct (is_error_code r); [sep_apply lit_huf_junk |]; cancel.
    + forward. forward.
      replace (Vlong (Int64.repr cs)) with (Vlong (Int64.repr (Zlength s'))) by (rewrite Hs'; reflexivity).
      destruct single; [apply (f_equal Int.unsigned) in H; vm_compute in H; discriminate |].
      pose proof (Hs6 eq_refl) as Hs6'.
      forward_call (gv, Ews, hp, ht, xh, sho, db, dc, dd, n, ish, ib, Zlength ic, ic, ioff + lh, s').
      all: try (match goal with |- 1 <= Zlength _ => assumption end).
      Intros vret. destruct vret as [r dc1]; simpl fst in *; simpl snd in *.
      forward.
      match goal with H1: out_after _ _ _ _, HB: byte_cells _ -> byte_cells _,
                      H3: match huf_lits_with _ _ _ _ with _ => _ end,
                      H4: match x_huf_decode _ _ _ _ with _ => _ end |- _ =>
        destruct (lit_gf3 ox (Some ht) x2 xh false ht s' n dd dc dc1 r Hdd Hn Hdn Hoh eq_refl Hxh
                    ltac:(assumption) H1 HB H3 H4) as [l GF] end.
      sep_apply (modus_ponens_wand (field_at Ews t_dctx (DOT _HUFptr) hp p * hufdt_x_at xh Ews ht hp)).
      Exists r dc1 l ht. rewrite Hs'. entailer!.
      unfold lit_hpart, lit_x2'. cbn [Z.eqb Pos.eqb]. destruct (is_error_code r); [sep_apply lit_huf_junk |]; cancel.
  - (* set_compressed *)
    assert (E2: e = 2) by (destruct He; [auto | subst e; exfalso; auto]). subst e.
    sep_apply (lit_tab2 gv p ox oh x2). rewrite lit_wk. Intros.
    assert_PROP (field_compatible t_dctx (DOT _litBuffer) p) as FCp by entailer!.
    forward_if.
    + forward.
      replace (Vlong (Int64.repr cs)) with (Vlong (Int64.repr (Zlength s'))) by (rewrite Hs'; reflexivity).
      rewrite (lit_ctx_huf_eq p FCp), (lit_wk_eq p FCp).
      forward_call (gv, Ews, offset_val 10296 p, sho, db, dc, dd, n, ish, ib, Zlength ic, ic, ioff + lh, s',
                    Ews, offset_val 27324 p, 640).
      all: try (match goal with |- 1 <= Zlength _ => assumption end).
      destruct single; [| exfalso; apply H0; reflexivity].
      Intros vret. destruct vret as [r dc1]; simpl fst in *; simpl snd in *.
      forward.
      rewrite <- (lit_ctx_huf_eq p FCp), <- (lit_wk_eq p FCp).
      unfold huf_built. destruct (is_error_code r) eqn:Er.
      * Exists r dc1 (@nil Z) (Build_huf_table 0 nil). rewrite Hs', lit_wk. entailer!.
        -- apply lit_gf2e; auto.
           match goal with H: match xh_dctx _ _ _ _ with _ => _ end |- _ => revert H end.
           cbn [negb]. destruct (xh_dctx _ _ _ _) as [[? ?] |]; auto.
        -- unfold lit_hpart. rewrite Er. unfold huf_junk. cancel.
      * Intros ht0. assert_PROP (huf_ok ht0) as Hht0 by (sep_apply lit_hufdtx_ok; entailer!).
        destruct (lit_gf2 ox oh x2 true ht0 s' n dd dc dc1 r Hdd Hn Hdn Hht0 Er Hs6
                    ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)
                    ltac:(assumption) ltac:(assumption)) as [l GF].
        Exists r dc1 l ht0. rewrite Hs', lit_wk. entailer!.
        unfold lit_hpart, lit_x2'. rewrite Er. cbn [Z.eqb Pos.eqb negb]. cancel.
    + forward.
      replace (Vlong (Int64.repr cs)) with (Vlong (Int64.repr (Zlength s'))) by (rewrite Hs'; reflexivity).
      destruct single; [apply (f_equal Int.unsigned) in H0; vm_compute in H0; discriminate |].
      pose proof (Hs6 eq_refl) as Hs6'.
      rewrite (lit_ctx_huf_eq p FCp), (lit_wk_eq p FCp).
      forward_call (gv, Ews, offset_val 10296 p, sho, db, dc, dd, n, ish, ib, Zlength ic, ic, ioff + lh, s',
                    Ews, offset_val 27324 p, 640).
      all: try (match goal with |- 1 <= Zlength _ => assumption end).
      Intros vret. destruct vret as [r dc1]; simpl fst in *; simpl snd in *.
      forward.
      rewrite <- (lit_ctx_huf_eq p FCp), <- (lit_wk_eq p FCp).
      unfold huf_built. destruct (is_error_code r) eqn:Er.
      * Exists r dc1 (@nil Z) (Build_huf_table 0 nil). rewrite Hs', lit_wk. entailer!.
        -- apply lit_gf2e; auto.
           match goal with H: match xh_dctx _ _ _ _ with _ => _ end |- _ => revert H end.
           cbn [negb]. destruct (xh_dctx _ _ _ _) as [[? ?] |]; auto.
        -- unfold lit_hpart. rewrite Er. unfold huf_junk. cancel.
      * Intros ht0. assert_PROP (huf_ok ht0) as Hht0 by (sep_apply lit_hufdtx_ok; entailer!).
        destruct (lit_gf2 ox oh x2 false ht0 s' n dd dc dc1 r Hdd Hn Hdn Hht0 Er Hs6
                    ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)
                    ltac:(assumption) ltac:(assumption)) as [l GF].
        Exists r dc1 l ht0. rewrite Hs', lit_wk. entailer!.
        unfold lit_hpart, lit_x2'. rewrite Er. cbn [Z.eqb Pos.eqb negb]. cancel.
Qed.

(* the call's facts as lit_hfacts: literals in the output array (litExtraBuffer unchanged) *)
Lemma lit_hf_dst (e: Z) (ox: option ddx) (oh: option huf_table) (x2 single: bool) (cb: list Z)
    (streaming cap bsm n d: Z) (oc oc1: list val) (lxb: list Z) (ex1: list val) (r: Z) (l: list Z) (ht: huf_table) :
  alloc_loc streaming cap bsm n <> LOC_NOT_IN_DST -> Zlength ex1 = LITEXTRA_N -> byte_cells ex1 -> ex1 = zbytes lxb ->
  lit_gfacts e ox oh x2 single cb n (lit_hd streaming cap bsm n d) oc oc1 r l ht ->
  lit_hfacts e ox oh x2 single cb streaming cap bsm n d oc oc1 lxb ex1 r l ht.
Proof.
  intros HL Hex Hbx Hx1 (G1 & [G2a G2b] & Gb & G3 & G4 & G5 & G6). unfold lit_hfacts. cbv zeta.
  rewrite (proj2 (Z.eqb_neq _ _) HL).
  split; [exact G1 |]. split; [exact G2a |]. split; [exact Hex |]. split; [exact Hbx |]. split; [exact Gb |].
  split; [exact G2b |].
  split; [exact G3 |]. split; [exact G4 |]. split; [exact G5 |]. split; [intros _; exact Hx1 | exact G6].
Qed.

(* literals in litExtraBuffer (lxb before the call) *)
Lemma lit_hf_extra (e: Z) (ox: option ddx) (oh: option huf_table) (x2 single: bool) (cb: list Z)
    (streaming cap bsm n d: Z) (oc: list val) (lxb: list Z) (ex1: list val) (r: Z) (l: list Z) (ht: huf_table) :
  alloc_loc streaming cap bsm n = LOC_NOT_IN_DST -> Zlength lxb = LITEXTRA_N -> bytes_ok lxb -> 0 <= n ->
  lit_gfacts e ox oh x2 single cb n 0 (zbytes lxb) ex1 r l ht ->
  lit_hfacts e ox oh x2 single cb streaming cap bsm n d oc oc lxb ex1 r l ht.
Proof.
  intros HL Hlx Hbx Hn0 (G1 & [G2a G2b] & Gb & G3 & G4 & G5 & G6). unfold lit_hfacts. cbv zeta.
  assert (Hn: n <= LITBUFFEREXTRASIZE).
  { unfold alloc_loc in HL. destruct (andb _ _); [discriminate |].
    destruct (n <=? _) eqn:E; [apply Z.leb_le; auto | discriminate]. }
  assert (Hz: Zlength (zbytes lxb) = LITEXTRA_N) by (rewrite Zlength_map; exact Hlx).
  rewrite HL. cbn [Z.eqb Pos.eqb LOC_NOT_IN_DST].
  split; [exact G1 |]. split; [reflexivity |]. split; [rewrite G2a; exact Hz |].
  split; [apply Gb, litc_bc_zbytes, Hbx |]. split; [exact (fun x => x) |]. split; [reflexivity |].
  split; [exact G3 |]. split; [exact G4 |]. split; [exact G5 |]. split; [| exact G6].
  intros Er. destruct (G3 Er) as (_ & _ & Hl & _ & Hsub).
  rewrite (lit_cwr_of (zbytes lxb) ex1 (zbytes l) 0 n)
    by (rewrite ?Zlength_map; auto; unfold LITEXTRA_N, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *; lia).
  unfold cwr. rewrite !Zlength_map, Hl, Hlx, Z.add_0_l, sublist_nil, sublist_map, map_app. reflexivity.
Qed.

Lemma lit_exbuf (v: list val) (p: val) :
  field_at Ews t_dctx (DOT _litExtraBuffer) v p = data_at Ews (tarray tuchar LITEXTRA_N) v (lit_extra p).
Proof. rewrite field_at_data_at. reflexivity. Qed.

Lemma seg_comp_huf (Espec: OracleKind) (gv: globals) (p: val) (fs: fstate) (ox: option ddx) (oh: option huf_table)
    (x2: bool) (lxb: list Z) (bsm streaming: Z) (W: list ptr_witness) (o: outarr) (i: inwin) (e lh n cs: Z)
    (single: bool) :
  lit_hyps fs oh bsm streaming W o i -> lit_kfacts oh bsm (oa_cap o) e (iw_s i) lh n cs single ->
  semax lit_Delta (lit_K gv p fs ox oh x2 lxb bsm streaming W o i e lh n cs single) lit_huf
    (normal_ret_assert (lit_J gv p fs ox oh x2 lxb bsm streaming W o i e lh n cs single)).
Proof.
  intros HY HK.
  destruct o as [osh ob oN oc d cap]; destruct i as [ish ib iN ic ioff s].
  destruct HY as (Hoo & Hio & Hstr & Hbsm0 & Hsb & Hfp & Hfd & Hcold & HW & Hoh & Hs2).
  destruct Hoo as (Hosh & HoN & HoN32 & Hd & Hcap & Hdc).
  rename Hio into Hwin. unfold inwin_ok in Hwin.
  destruct HK as (He & Hty & Hx & H5 & Hh & Hlh & Hcs & Hsg & Hnm & Hs6 & Hcl).
  cbn [oa_sh oa_base oa_N oa_c oa_d oa_cap iw_sh iw_base iw_N iw_c iw_off iw_s] in *.
  assert (Hwin' := Hwin). destruct Hwin' as (Hish & Hioff & Hin & HiN32 & HiN & _ & Hbytes & Hw8).
  subst iN oN.
  assert (Hbsm: 0 <= bsm <= 131072) by (unfold ZSTD_BLOCKSIZE_MAX in Hbsm0; lia).
  pose proof (lit_hdr_range s lh n cs single Hbytes H5 Hh) as (_ & Hnr & _ & _).
  assert (Hn0: 0 <= n <= 131072) by (pose proof (Z.le_min_l bsm cap); lia).
  unfold lit_K, lit_J, lit_KF. cbn [oa_sh oa_base oa_N oa_c oa_d oa_cap iw_sh iw_base iw_N iw_c iw_off iw_s app].
  unfold lit_extra_at. Intros.
  match goal with H: Zlength lxb = LITEXTRA_N |- _ => rename H into Hlxb end.
  match goal with H: bytes_ok lxb |- _ => rename H into Hlxbb end.
  remember (zbytes lxb) as ex0 eqn:Eex0.
  assert (Hbx0: byte_cells ex0) by (subst ex0; apply litc_bc_zbytes, Hlxbb).
  assert (Hex0: @Zlength val ex0 = LITEXTRA_N) by (subst ex0; rewrite Zlength_map; exact Hlxb).
  assert_PROP (field_compatible t_dctx (DOT _litBuffer) p) as FCp by (unfold lit_KL; entailer!).
  assert (Pp: isptr p) by (destruct FCp; auto).
  destruct (Z.eq_dec (alloc_loc streaming cap bsm n) LOC_NOT_IN_DST) as [HL | HL].
  - (* litExtraBuffer *)
    assert (Hn64: n <= 65536).
    { unfold alloc_loc in HL. destruct (andb _ _); [discriminate |].
      destruct (n <=? LITBUFFEREXTRASIZE) eqn:E; [apply Z.leb_le in E; unfold LITBUFFEREXTRASIZE in E; lia | discriminate]. }
    assert (Hlb: fst (alloc_buf p ob streaming cap bsm n d (Z.min bsm cap) 0) = offset_val 0 (lit_extra p)).
    { unfold alloc_buf. rewrite HL. simpl. rewrite lit_extra_eq by auto. rewrite offset_offset_val. reflexivity. }
    rewrite Hlb, lit_exbuf.
    match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx [?A1; _; ?A3; ?A4; _; _; _; _; ?A9; _; _; ?A12; ?A13; ?A14; ?A15]))) _ _ =>
    eapply semax_pre; [| eapply semax_post; [| | | |
      apply (lit_huf_gen Espec gv p ox oh x2 bsm streaming ob d cap ib ish ic ioff s e lh n cs single Ews (lit_extra p) ex0 0
        (A1 * A3 * A4 * A9 * A12 * A13 * A14 * A15))]] end;
      try (rewrite ?Hex0; unfold LITEXTRA_N, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH;
           first [lia | assumption | apply writable_Ews]).
    + rewrite Hex0. unfold lit_KL. entailer!.
    + cbn [RA_normal normal_ret_assert]. Intros r dc1 l ht. Exists r oc dc1 l ht.
      rewrite Hex0, <- lit_exbuf. unfold lit_KL. entailer!. try subst ex0. apply lit_hf_extra; auto. lia.
    + intros. apply andp_left2. simpl. normalize.
    + intros. apply andp_left2. simpl. normalize.
    + intros. apply andp_left2. simpl. normalize.
  - (* the output array *)
    assert (H1oc: 1 <= Zlength oc).
    { unfold alloc_loc in HL.
      destruct (andb (streaming =? 0) (bsm + WILDCOPY_OVERLENGTH + n + WILDCOPY_OVERLENGTH <? cap)) eqn:E2.
      - apply andb_prop in E2 as [_ E2]. apply Z.ltb_lt in E2. unfold WILDCOPY_OVERLENGTH in E2. lia.
      - destruct (n <=? LITBUFFEREXTRASIZE) eqn:E; [exfalso; apply HL; reflexivity |].
        apply Z.leb_gt in E. unfold LITBUFFEREXTRASIZE in E. pose proof (Z.le_min_r bsm cap). lia. }
    set (hd := lit_hd streaming cap bsm n d).
    assert (Hlb: fst (alloc_buf p ob streaming cap bsm n d (Z.min bsm cap) 0) = offset_val hd ob).
    { unfold hd, lit_hd, alloc_buf. destruct (alloc_loc streaming cap bsm n =? LOC_IN_DST); [reflexivity |].
      rewrite (proj2 (Z.eqb_neq _ _) HL). reflexivity. }
    assert (Hhd: d <= hd /\ hd + n <= d + cap).
    { unfold hd, lit_hd. destruct (alloc_loc streaming cap bsm n =? LOC_IN_DST) eqn:E1.
      - apply Z.eqb_eq in E1. unfold alloc_loc in E1. destruct (andb _ _) eqn:E2.
        + apply andb_prop in E2 as [_ E2]. apply Z.ltb_lt in E2. unfold WILDCOPY_OVERLENGTH in *. lia.
        + destruct (n <=? LITBUFFEREXTRASIZE); discriminate.
      - pose proof (Z.le_min_r bsm cap). lia. }
    rewrite Hlb.
    match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx [?A1; _; ?A3; ?A4; _; _; _; ?A8; _; _; _; ?A12; ?A13; ?A14; ?A15]))) _ _ =>
    eapply semax_pre; [| eapply semax_post; [| | | |
      apply (lit_huf_gen Espec gv p ox oh x2 bsm streaming ob d cap ib ish ic ioff s e lh n cs single osh ob oc hd
        (A1 * A3 * A4 * A8 * A12 * A13 * A14 * A15))]] end;
      try (first [lia | assumption]).
    + unfold lit_KL. entailer!.
    + cbn [RA_normal normal_ret_assert]. Intros r oc1 l ht. Exists r oc1 ex0 l ht.
      unfold lit_KL. entailer!. apply lit_hf_dst; auto.
    + intros. apply andp_left2. simpl. normalize.
    + intros. apply andp_left2. simpl. normalize.
    + intros. apply andp_left2. simpl. normalize.
Qed.
