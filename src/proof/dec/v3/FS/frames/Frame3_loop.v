(* FS3 one-shot frames: the block loop of ZSTD_decompressFrame from its body's segments B1, B2, B3 (port of
   v2 body_frame.v's fr_loop_ok). *)
Require Import Zstd.proof.dec.v3.FS.frames.Frames3Defs.
Local Open Scope logic.

Section CM_Frame3_loop_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Section Seg.
Context (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR: blrel)
  (W: list ptr_witness) (gv: globals) (p: val) (fs: fstate) (ox: option ddx) (dm: dict_model) (e: ext_seg)
  (osh: share) (obase: val) (oN: Z) (oc: list val) (od ocap: Z)
  (ish: share) (ibase: val) (iN: Z) (ic: list val) (ioff: Z) (s: list Z) (sp ssp: val) (v_bp: val)
  (pr: dparams) (dsp: val) (d: dfields) (l: list (val * ddict_st)) (tbl: list val) (xq: option (val * val)) (lent: bool)
  (am: option cmem) (hb: Z) (h: frame_header) (hs: Z) (fdid: Z) (d1: dfields) (ts0: tstate).

Lemma fr_loop_ok3: DENT_OK DENT -> TABS_OK TABS ->
  fr_B1_stmt DENT TABS SR BR W gv p fs ox dm e osh obase oN oc od ocap ish ibase iN ic ioff s sp ssp v_bp pr dsp d l tbl xq lent am hb h hs fdid d1 ts0 -> fr_B2_stmt DENT TABS SR BR W gv p fs ox dm e osh obase oN oc od ocap ish ibase iN ic ioff s sp ssp v_bp pr dsp d l tbl xq lent am hb h hs fdid d1 ts0 -> fr_B3_stmt DENT TABS SR BR W gv p fs ox dm e osh obase oN oc od ocap ish ibase iN ic ioff s sp ssp v_bp pr dsp d l tbl xq lent am hb h hs fdid d1 ts0 ->
  fr_loopk_stmt DENT TABS SR BR W gv p fs ox dm e osh obase oN oc od ocap ish ibase iN ic ioff s sp ssp v_bp pr dsp d l tbl xq lent am hb h hs fdid d1 ts0.
Proof.
  intros HD HT HB1 HB2 HB3 Espec k HC Hts0 Hk.
  rewrite fr_loop_shape.
  apply semax_seq with (Q := fr_Brk DENT TABS W gv p fs ox dm e osh obase oN oc od ocap ish ibase iN ic ioff s sp ssp v_bp pr dsp l tbl xq lent am hb h hs fdid d1 ts0).
  2: { unfold fr_Brk. repeat (apply extract_exists_pre; intro). apply Hk. }
  apply semax_pre with (P' := fr_Inv DENT TABS W gv p fs ox dm e osh obase oN oc od ocap ish ibase iN ic ioff s sp ssp v_bp pr dsp l tbl xq lent am hb h hs fdid d1 ts0).
  { unfold fr_Inv. apply andp_left2. Exists 0 (@nil Z) oc ts0 (fs_ddictIsCold fs). apply derives_refl. }
  apply semax_loop with (Q' := fr_Inv DENT TABS W gv p fs ox dm e osh obase oN oc od ocap ish ibase iN ic ioff s sp ssp v_bp pr dsp l tbl xq lent am hb h hs fdid d1 ts0).
  - unfold fr_Inv at 1. repeat (apply extract_exists_pre; intro).
    destruct (fr_lb_split Sskip) as [_ E]. rewrite E.
    apply HB1; auto.
  - apply (semax_post (normal_ret_assert (fr_Inv DENT TABS W gv p fs ox dm e osh obase oN oc od ocap ish ibase iN ic ioff s sp ssp v_bp pr dsp l tbl xq lent am hb h hs fdid d1 ts0))).
    + simpl_ret_assert. apply andp_left2. apply derives_refl.
    + apply ENTAIL_break_normal.
    + apply ENTAIL_continue_normal.
    + intros. apply ENTAIL_return_normal.
    + apply semax_skip.
Qed.

End Seg.

End CM_Frame3_loop_1.
