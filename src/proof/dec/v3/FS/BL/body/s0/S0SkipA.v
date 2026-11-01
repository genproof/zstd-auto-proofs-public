(* FS3-bl BODY stage 0: the zstd1 format: MEM_readLE32(src) and the skippable magic test. *)
Require Export Zstd.proof.dec.v3.FS.BL.body.s0.S0SkipB.
Local Open Scope logic.

Section CM_S0SkipA_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma s0_skipA_ok : forall (Espec: OracleKind) (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR': blrel)
  (W: list ptr_witness) (gv: globals) (p: val) (pr: dparams) (od: option bldict) (osz0: Z) (ba: blabs) (fs: fstate)
  (ts: tstate) (hb: list val) (shk shd: share) (ob: val) (osz opos: Z) (oc: list val) (shs: share) (src: val)
  (c: list Z) (v_bp: val) (v: blv) (pcs st: Z),
  s0_ok pr od osz0 ba fs ts hb v ob osz opos oc shs c -> isptr src -> dp_fmt pr = 0 ->
  semax (s0_D DENT TABS SR BR')
    (s0_preA DENT TABS W gv p pr od fs ts hb shk shd ob osz opos oc shs src c v_bp pcs st)
    s0_THEN
    (overridePost (s0_mid DENT TABS W gv p pr od fs ts hb shk shd ob osz opos oc shs src c v_bp pcs st)
       (s0_RA DENT TABS W gv p pr od ba shk shd ob osz opos oc shs src c)).
Proof.
  intros Espec DENT TABS SR BR' W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v_bp v pcs st
    Hok Hsrc Hf0.
  pose proof Hok as Hok0.
  destruct Hok as (Hpr & Hho & Hop & Hoc & Hci0 & Hmr & Hmd & Hst & Hn & Hcb & Hlay & Hrs & Hhb & Hne0 & Hfp).
  assert (Hc5: Zlength c = 5) by (rewrite Hn; unfold dmode_of; cbn [md_magicless]; rewrite Hf0; reflexivity).
  unfold s0_D, s0_preA, s0_THEN, s0_mid, s0_RA, bl_R, bl_post. s0_simplify. abbreviate_semax.
  forward_call (shs, src, c, 0).
  { unfold mem_read_pre. rewrite Hc5. split; [auto | split; [lia | split; [lia |]]]. apply Forall_sublist; auto. }
  pose proof (s0_le_field_range c 0 Hcb) as Hm.
  forward_if.
  - assert (Hsk: is_skippable_magic (le_field c 0 4) = true).
    { rewrite <- s0_skip_magic_eq by exact Hm. rewrite H. apply Int.eq_true. }
    unfold POSTCONDITION, abbreviate.
    exact (s0_skipB_ok Espec DENT TABS SR BR' W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v_bp v
             pcs st _ Hok0 Hf0 Hsk).
  - forward. entailer!. rewrite <- s0_skip_magic_eq by exact Hm. apply Int.eq_false. auto.
Qed.

End CM_S0SkipA_1.
