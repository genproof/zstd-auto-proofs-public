(* FS3-bl BODY stage 0: headerSize = ZSTD_frameHeaderSize_internal(src, srcSize, format) and its
   ZSTD_isError test (never an error: srcSize is the format's prefix length). *)
Require Export Zstd.proof.dec.v3.FS.BL.body.s0.S0HdrB.
Local Open Scope logic.

Section CM_S0HdrA_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma s0_hdrA_ok : forall (Espec: OracleKind) (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR': blrel)
  (W: list ptr_witness) (gv: globals) (p: val) (pr: dparams) (od: option bldict) (osz0: Z) (ba: blabs) (fs: fstate)
  (ts: tstate) (hb: list val) (shk shd: share) (ob: val) (osz opos: Z) (oc: list val) (shs: share) (src: val)
  (c: list Z) (v_bp: val) (v: blv) (pcs st: Z) (tl: statement),
  s0_ok pr od osz0 ba fs ts hb v ob osz opos oc shs c -> isptr src ->
  semax (s0_D DENT TABS SR BR')
    (s0_mid DENT TABS W gv p pr od fs ts hb shk shd ob osz opos oc shs src c v_bp pcs st)
    (Ssequence s0_REST tl) (s0_RA DENT TABS W gv p pr od ba shk shd ob osz opos oc shs src c).
Proof.
  intros Espec DENT TABS SR BR' W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v_bp v pcs st tl
    Hok Hsrc.
  pose proof Hok as Hok0.
  destruct Hok as (Hpr & Hho & Hop & Hoc & Hci0 & Hmr & Hmd & Hst & Hn & Hcb & Hlay & Hrs & Hhb & Hne0 & Hfp).
  assert (Hfmt: dp_fmt pr = 0 \/ dp_fmt pr = 1) by (destruct Hpr; tauto).
  assert (Hn5: 1 <= Zlength c <= 5).
  { rewrite Hn. unfold starting_len. destruct (md_magicless _); cbv; split; congruence. }
  unfold s0_D, s0_mid, s0_REST, s0_RA, bl_R, bl_post. s0_simplify. abbreviate_semax.
  Intros. rename H into Hns.
  assert (Hk: s0_skip (md_magicless (dmode_of pr)) c = false).
  { unfold s0_skip. destruct Hfmt as [E|E].
    - rewrite (Hns E). apply andb_false_r.
    - unfold dmode_of. cbn [md_magicless]. rewrite E. reflexivity. }
  forward.
  forward_call (gv, shs, src, Zlength c, zbytes c, 0, c, dp_fmt pr).
  { unfold win_ok. split; [auto|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [list_solve|].
    split; [reflexivity|]. split; [auto|]. rewrite Z.add_0_l. rewrite sublist_same by list_solve. reflexivity. }
  Intros r.
  forward. forward. forward_call r.
  match goal with H: match frame_header_size_m _ _ with _ => _ end |- _ => rename H into Hr end.
  change (fmt_mg (dp_fmt pr)) with (md_magicless (dmode_of pr)) in Hr.
  rewrite (s0_fhs (md_magicless (dmode_of pr)) c Hn) in Hr. subst r.
  pose proof (s0_hs_range (md_magicless (dmode_of pr)) c) as Hhs.
  assert (Hie: is_error_code (header_size_m (md_magicless (dmode_of pr)) c) = false)
    by (unfold is_error_code; apply Z.ltb_ge; lia).
  rewrite Hie.
  forward_if.
  { exfalso. auto. }
  unfold MORE_COMMANDS, POSTCONDITION, abbreviate.
  exact (s0_hdrB_ok Espec DENT TABS SR BR' W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v_bp v
           pcs st tl Hok0 Hk).
Qed.

End CM_S0HdrA_1.
