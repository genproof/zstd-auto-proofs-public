(* FS3-bl BODY stage 0: a Zstandard frame: the prefix into headerBuffer, expected = headerSize - srcSize,
   stage = ZSTDds_decodeFrameHeader, return 0. *)
Require Export Zstd.proof.dec.v3.FS.BL.body.s0.S0Defs.
Local Open Scope logic.

Section CM_S0HdrB_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma s0_hdrB_ok : forall (Espec: OracleKind) (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR': blrel)
  (W: list ptr_witness) (gv: globals) (p: val) (pr: dparams) (od: option bldict) (osz0: Z) (ba: blabs) (fs: fstate)
  (ts: tstate) (hb: list val) (shk shd: share) (ob: val) (osz opos: Z) (oc: list val) (shs: share) (src: val)
  (c: list Z) (v_bp: val) (v: blv) (pcs st: Z) (tl: statement),
  s0_ok pr od osz0 ba fs ts hb v ob osz opos oc shs c ->
  s0_skip (md_magicless (dmode_of pr)) c = false ->
  semax (s0_D DENT TABS SR BR')
    (s0_preH DENT TABS W gv p pr od fs ts hb shk shd ob osz opos oc shs src c v_bp pcs st
       (header_size_m (md_magicless (dmode_of pr)) c))
    (Ssequence s0_HB tl) (s0_RA DENT TABS W gv p pr od ba shk shd ob osz opos oc shs src c).
Proof.
  intros Espec DENT TABS SR BR' W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v_bp v pcs st tl
    Hok Hk.
  destruct Hok as (Hpr & Hho & Hop & Hoc & Hci0 & Hmr & Hmd & Hst & Hn & Hcb & Hlay & Hrs & Hhb & Hne0 & Hfp).
  assert (Hn5: 1 <= Zlength c <= 5).
  { rewrite Hn. unfold starting_len. destruct (md_magicless _); cbv; split; congruence. }
  unfold s0_D, s0_preH, s0_HB, s0_RA, bl_R, bl_post. s0_simplify. abbreviate_semax.
  set (mg := md_magicless (dmode_of pr)) in *.
  set (fs1 := bl_fs1 fs ob osz opos pcs (Zlength c)) in *.
  rewrite s0_hb_eq.
  assert_PROP (field_compatible (tarray tuchar 18) [] (field_address t_dctx (DOT _headerBuffer) p)) as Hfc by entailer!.
  sep_apply (s0_hb_before hb (Zlength c) (field_address t_dctx (DOT _headerBuffer) p) Hhb ltac:(lia) Hfc).
  forward_call (shs, Ews, src, field_address t_dctx (DOT _headerBuffer) p,
                existT (fun t => reptype t) (tarray tuchar (Zlength c)) (zbytes c)).
  { cbn [projT1]. cancel. }
  { memcpy_side. }
  cbn [projT1 projT2].
  forward. forward. forward.
  sep_apply (s0_hb_after hb c (field_address t_dctx (DOT _headerBuffer) p) Hhb ltac:(lia) Hfc).
  rewrite <- s0_hb_eq.
  assert (E1: s0_stv mg c = Vint (Int.repr 1)) by (unfold s0_stv; rewrite Hk; reflexivity).
  assert (E2: vlong (s0_e mg c) = Vlong (Int64.sub (Int64.repr (header_size_m mg c)) (Int64.repr (Zlength c)))).
  { unfold s0_e. rewrite Hk. unfold vlong. rewrite sub64_repr. reflexivity. }
  assert (E3: s0_hsv mg c (fs_headerSize fs1) = Vlong (Int64.repr (header_size_m mg c))).
  { unfold s0_hsv. rewrite Hk. reflexivity. }
  rewrite <- E1, <- E2, <- E3.
  sep_apply (s0_fcore3_join p fs1 pr (s0_hsv mg c (fs_headerSize fs1)) (vlong (s0_e mg c)) (s0_stv mg c) Hpr).
  change (s0_fs fs1 (s0_hsv mg c (fs_headerSize fs1)) (vlong (s0_e mg c)) (s0_stv mg c))
    with (s0_fs' mg fs ob osz opos pcs c).
  forward.
  pose proof (s0_post_pure (dmode_of pr) od (Zlength oc) osz0 ba fs ts hb v ob opos oc c pcs
                Hho Hop eq_refl Hci0 Hmr Hmd Hst Hn Hcb Hlay Hne0) as P.
  cbv zeta in P. rewrite !Z.add_0_r in P.
  Exists 0 oc (s0_ba mg ba c ob opos) (s0_fs' mg fs ob (Zlength oc) opos pcs c) (TInit (bd_oxo od) ts) (s0_hb hb c).
  rewrite !Z.add_0_r. unfold tabs_rep.
  apply andp_right.
  { apply prop_right. destruct P as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
    exact (conj P1 (conj P2 (conj P3 (conj P4 (conj P5 (conj (s0_fs'_fp_ok _ _ _ _ _ _ _ Hfp)
             (conj P6 (conj P7 eq_refl)))))))). }
  cancel.
Qed.

End CM_S0HdrB_1.
