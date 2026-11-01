(* FS3 one-shot frames: the switch on the block type (statement 8), from the three cases (port of v2 body_frame.v's fr_B2_ok). *)
Require Import Zstd.proof.dec.v3.FS.frames.Frames3Defs Zstd.proof.dec.v3.FS.frames.Frames3Model.
Local Open Scope logic.

Section CM_Frame3_B2_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Section Seg.
Context (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR: blrel)
  (W: list ptr_witness) (gv: globals) (p: val) (fs: fstate) (ox: option ddx) (dm: dict_model) (e: ext_seg)
  (osh: share) (obase: val) (oN: Z) (oc: list val) (od ocap: Z)
  (ish: share) (ibase: val) (iN: Z) (ic: list val) (ioff: Z) (s: list Z) (sp ssp: val) (v_bp: val)
  (pr: dparams) (dsp: val) (d: dfields) (l: list (val * ddict_st)) (tbl: list val) (xq: option (val * val)) (lent: bool)
  (am: option cmem) (hb: Z) (h: frame_header) (hs: Z) (fdid: Z) (d1: dfields) (ts0: tstate).

Lemma fr_B2_ok3: DENT_OK DENT -> TABS_OK TABS ->
  fr_case_stmt DENT TABS SR BR W gv p fs ox dm e osh obase oN oc od ocap ish ibase iN ic ioff s sp ssp v_bp pr dsp d l tbl xq lent am hb h hs fdid d1 ts0 0 ->
  fr_case_stmt DENT TABS SR BR W gv p fs ox dm e osh obase oN oc od ocap ish ibase iN ic ioff s sp ssp v_bp pr dsp d l tbl xq lent am hb h hs fdid d1 ts0 1 ->
  fr_case_stmt DENT TABS SR BR W gv p fs ox dm e osh obase oN oc od ocap ish ibase iN ic ioff s sp ssp v_bp pr dsp d l tbl xq lent am hb h hs fdid d1 ts0 2 ->
  fr_B2_stmt DENT TABS SR BR W gv p fs ox dm e osh obase oN oc od ocap ish ibase iN ic ioff s sp ssp v_bp pr dsp d l tbl xq lent am hb h hs fdid d1 ts0.
Proof.
  intros HD HT Hraw Hrle Hcmp Espec k j out oc1 st cold c HC Hk.
  unfold fr_Delta in *. unfold fr_LR, fr_R.
  cbv [fr_sw Frames3Defs.seq_nth fr_lb fr_loop fr_body f_ZSTD_decompressFrame fn_body].
  unfold S_sw at 1. unfold fr_SEP, fr_LOC, fr_outP.
  abbreviate_semax.
  Intros.
  unfold bp_val at 1.
  forward.
  apply semax_seq with (EX r: Z, EX oc2: list val, EX st2: tstate, EX cold2: val, EX cnt: list Z,
      S_dec DENT TABS W gv p fs ox dm e osh obase oN oc od ocap ish ibase iN ic ioff s sp ssp v_bp pr dsp l tbl xq lent am hb h hs fdid d1 ts0
        j out oc1 st cold c r oc2 st2 cold2 cnt).
  2: { Intros r oc2 st2 cold2 cnt. apply Hk. }
  eapply (semax_switch_PQR (bp_type (block_props_of (fr_t s hs j)))); [reflexivity | entailer! | entailer! | ].
  match goal with Hc: cblock_size (fr_t s hs j) = Some c |- _ => pose proof (bt_range _ _ Hc) as Bts end.
  destruct Bts as [Bt | [Bt | Bt]].
  - pose (HH := Hraw Espec j out oc1 st cold c HC Bt).
    rewrite Bt.
    match goal with |- semax _ _ ?S _ => let S' := eval vm_compute in S in change S with S' end.
    apply semax_seq with (Q := FF); [ | apply semax_ff ].
    apply semax_seq with (Q := (EX r: Z, EX oc2: list val, EX st2: tstate, EX cold2: val, EX cnt: list Z,
      S_dec DENT TABS W gv p fs ox dm e osh obase oN oc od ocap ish ibase iN ic ioff s sp ssp v_bp pr dsp l tbl xq lent am hb h hs fdid d1 ts0
        j out oc1 st cold c r oc2 st2 cold2 cnt)).
    2: (forward; try apply ENTAIL_refl).
    apply (semax_post (normal_ret_assert (EX r: Z, EX oc2: list val, EX st2: tstate, EX cold2: val, EX cnt: list Z,
      S_dec DENT TABS W gv p fs ox dm e osh obase oN oc od ocap ish ibase iN ic ioff s sp ssp v_bp pr dsp l tbl xq lent am hb h hs fdid d1 ts0
        j out oc1 st cold c r oc2 st2 cold2 cnt))).
    { simpl_ret_assert. apply ENTAIL_refl. }
    { apply ENTAIL_break_normal. }
    { apply ENTAIL_continue_normal. }
    { intros. apply ENTAIL_return_normal. }
    eapply semax_pre; [ | exact HH ].
    unfold S_sw, fr_SEP, fr_LOC, fr_outP, bp_val. rewrite Bt. entailer!.
  - pose (HH := Hrle Espec j out oc1 st cold c HC Bt).
    rewrite Bt.
    match goal with |- semax _ _ ?S _ => let S' := eval vm_compute in S in change S with S' end.
    apply semax_seq with (Q := FF); [ | apply semax_ff ].
    apply semax_seq with (Q := (EX r: Z, EX oc2: list val, EX st2: tstate, EX cold2: val, EX cnt: list Z,
      S_dec DENT TABS W gv p fs ox dm e osh obase oN oc od ocap ish ibase iN ic ioff s sp ssp v_bp pr dsp l tbl xq lent am hb h hs fdid d1 ts0
        j out oc1 st cold c r oc2 st2 cold2 cnt)).
    2: (forward; try apply ENTAIL_refl).
    apply (semax_post (normal_ret_assert (EX r: Z, EX oc2: list val, EX st2: tstate, EX cold2: val, EX cnt: list Z,
      S_dec DENT TABS W gv p fs ox dm e osh obase oN oc od ocap ish ibase iN ic ioff s sp ssp v_bp pr dsp l tbl xq lent am hb h hs fdid d1 ts0
        j out oc1 st cold c r oc2 st2 cold2 cnt))).
    { simpl_ret_assert. apply ENTAIL_refl. }
    { apply ENTAIL_break_normal. }
    { apply ENTAIL_continue_normal. }
    { intros. apply ENTAIL_return_normal. }
    eapply semax_pre; [ | exact HH ].
    unfold S_sw, fr_SEP, fr_LOC, fr_outP, bp_val. rewrite Bt. entailer!.
  - pose (HH := Hcmp Espec j out oc1 st cold c HC Bt).
    rewrite Bt.
    match goal with |- semax _ _ ?S _ => let S' := eval vm_compute in S in change S with S' end.
    apply semax_seq with (Q := FF); [ | apply semax_ff ].
    apply semax_seq with (Q := (EX r: Z, EX oc2: list val, EX st2: tstate, EX cold2: val, EX cnt: list Z,
      S_dec DENT TABS W gv p fs ox dm e osh obase oN oc od ocap ish ibase iN ic ioff s sp ssp v_bp pr dsp l tbl xq lent am hb h hs fdid d1 ts0
        j out oc1 st cold c r oc2 st2 cold2 cnt)).
    2: (forward; try apply ENTAIL_refl).
    apply (semax_post (normal_ret_assert (EX r: Z, EX oc2: list val, EX st2: tstate, EX cold2: val, EX cnt: list Z,
      S_dec DENT TABS W gv p fs ox dm e osh obase oN oc od ocap ish ibase iN ic ioff s sp ssp v_bp pr dsp l tbl xq lent am hb h hs fdid d1 ts0
        j out oc1 st cold c r oc2 st2 cold2 cnt))).
    { simpl_ret_assert. apply ENTAIL_refl. }
    { apply ENTAIL_break_normal. }
    { apply ENTAIL_continue_normal. }
    { intros. apply ENTAIL_return_normal. }
    eapply semax_pre; [ | exact HH ].
    unfold S_sw, fr_SEP, fr_LOC, fr_outP, bp_val. rewrite Bt. entailer!.
Qed.

End Seg.

End CM_Frame3_B2_1.
