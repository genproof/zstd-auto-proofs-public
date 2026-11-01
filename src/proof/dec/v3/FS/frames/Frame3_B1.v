(* FS3 one-shot frames: the loop body's block header (statements 0..7) (port of v2 body_frame.v's fr_B1_ok). *)
Require Import Zstd.proof.dec.v3.FS.frames.Frames3Defs Zstd.proof.dec.v3.FS.frames.Frames3Model.
Require Import Zstd.proof.dec.v3.FS.frames.Frame3_codes.
Require Import Zstd.proof.model.ExHuf Zstd.proof.model.ExBlock Zstd.proof.model.ExFrame Zstd.proof.model.ExFrameFacts.

Local Open Scope Z_scope.

Local Open Scope logic.

Section CM_Frame3_B1_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* an error exit at block j where the model fails too: frame_res3 *)
Lemma b1_err3: forall pr dsp dm s hs h j out st r ocap oc od,
  fr_hdr3 (dmode_of pr) (sel_on pr dsp) dm s hs h -> fr_OT dm h s hs j out st -> 0 <= j -> hs + j <= Zlength s ->
  is_error_code r = true ->
  (cblock_size (fr_t s hs j) = None \/
   exists c, cblock_size (fr_t s hs j) = Some c /\ c > Zlength (fr_t s hs j) - ZSTD_blockHeaderSize) ->
  frame_res3 (dmode_of pr) dm s ocap r oc od 0.
Proof.
  intros pr dsp dm s hs h j out st r ocap oc od Hh HOT Hj Hhj Hr Hc.
  apply fr_err3; [exact Hr | ]. intros c0 sz0 Hd0.
  destruct (fr_frame_ok3_any _ _ _ _ _ _ _ _ Hh Hd0) as (k0 & Hdb & _).
  exfalso. refine (fr_OT_none _ _ _ _ _ _ _ HOT Hj Hhj _ _ _ Hdb).
  destruct Hc as [Hc | Hc]; [left; exact Hc | right; left; exact Hc].
Qed.

(* ... and frame_codes3: the model's blocks fail, no claim *)
Lemma b1_codes3: forall pr dsp dm s hs h j out st r ocap,
  fr_hdr3 (dmode_of pr) (sel_on pr dsp) dm s hs h -> fr_OT dm h s hs j out st -> 0 <= j -> hs + j <= Zlength s ->
  (cblock_size (fr_t s hs j) = None \/
   exists c, cblock_size (fr_t s hs j) = Some c /\ c > Zlength (fr_t s hs j) - ZSTD_blockHeaderSize) ->
  frame_codes3 (dmode_of pr) dm s ocap r.
Proof.
  intros pr dsp dm s hs h j out st r ocap Hh HOT Hj Hhj Hc.
  apply (fr_codes_noDB _ _ _ _ _ _ _ _ Hh). intros o k Hdb.
  refine (fr_OT_none _ _ _ _ _ _ _ HOT Hj Hhj _ _ _ Hdb).
  destruct Hc as [Hc | Hc]; [left; exact Hc | right; left; exact Hc].
Qed.

Section Seg.
Context (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR: blrel)
  (W: list ptr_witness) (gv: globals) (p: val) (fs: fstate) (ox: option ddx) (dm: dict_model) (e: ext_seg)
  (osh: share) (obase: val) (oN: Z) (oc: list val) (od ocap: Z)
  (ish: share) (ibase: val) (iN: Z) (ic: list val) (ioff: Z) (s: list Z) (sp ssp: val) (v_bp: val)
  (pr: dparams) (dsp: val) (d: dfields) (l: list (val * ddict_st)) (tbl: list val) (xq: option (val * val)) (lent: bool)
  (am: option cmem) (hb: Z) (h: frame_header) (hs: Z) (fdid: Z) (d1: dfields) (ts0: tstate).

(* an error exit at block j whose header the model refuses too (its size field is invalid, or the block does not
   fit in the input): the model's blocks of the frame fail from block j on, so the exact frame fails *)
Lemma b1_exact: forall j out st r oc' lxb',
  fr_ctx W fs ox dm e osh obase oN oc od ocap ish ibase iN ic ioff s pr dsp d l tbl lent h hs d1 ->
  fr_xinv ox dm e ocap s pr h hs ts0 j out st ->
  (cblock_size (fr_t s hs j) = None \/
   exists c, cblock_size (fr_t s hs j) = Some c /\ c > Zlength (fr_t s hs j) - ZSTD_blockHeaderSize) ->
  is_error_code r = true ->
  ox = None -> dm = no_dict -> pr = dparams_dflt -> e = ExtNone -> frame_exact ts0 s ocap r oc' od 0 lxb'.
Proof.
  intros j out st r oc' lxb' HC Hx Hc Hr Hox Hdm Hpr He.
  assert (Hon: fx_on ox dm e pr) by (repeat split; assumption).
  unfold frame_exact.
  rewrite (fr_x_frame DENT TABS SR BR W gv p fs ox dm e osh obase oN oc od ocap ish ibase iN ic ioff s sp ssp v_bp
             pr dsp d l tbl xq lent am hb h hs fdid d1 ts0 HC Hon).
  rewrite (proj2 (Hx Hon)), xbs_err; [exact Hr | ].
  unfold xb_one. destruct Hc as [-> | (c & -> & Hc)]; [reflexivity | ].
  replace (c >? Zlength (fr_t s hs j) - ZSTD_blockHeaderSize) with true by (symmetry; apply Z.gtb_lt; lia).
  reflexivity.
Qed.

Lemma fr_B1_ok3: DENT_OK DENT -> TABS_OK TABS ->
  fr_B1_stmt DENT TABS SR BR W gv p fs ox dm e osh obase oN oc od ocap ish ibase iN ic ioff s sp ssp v_bp pr dsp d l tbl xq lent am hb h hs fdid d1 ts0.
Proof.
  intros HD HT Espec k j out oc1 st cold HC Hk.
  unfold fr_Delta in *. unfold fr_LR, fr_R.
  cbv [Frames3Defs.seq_cut Frames3Defs.fr_lb Frames3Defs.fr_loop Frames3Defs.seq_nth Frames3Defs.fr_body f_ZSTD_decompressFrame fn_body].
  unfold S_inv, fr_SEP, fr_LOC, fr_outP.
  abbreviate_semax.
  Intros.
  rename H0 into Hxinv.
  pose proof HC as HC0.
  destruct HC0 as [Hosh HoN HoN32 Hod Hocap Hodcap Hwin Hext Hifd Hcold HW Hlay Hhp Hhb Hed He0 Hob Hib
                   Hpar Hhdr Hd1 Hlent].
  pose proof Hhdr as (Hs & Hlen9 & Hhs & Hlenh & Hgfh).
  pose proof Hwin as (Hish & Hioff & HiN & HiN32 & HicN & _ & _ & Hics).
  assert (Hhs6: 0 <= hs).
  { rewrite Hhs. pose proof (hs3_range (md_magicless (dmode_of pr)) s Hs) as X.
    unfold mg_sh in *. destruct (md_magicless (dmode_of pr)); unfold starting_len, ZSTD_FRAMEHEADERSIZE_PREFIX,
      ZSTD_FRAMEHEADERSIZE_MIN, ZSTD_blockHeaderSize in *; lia. }
  clear Hhs.
  forward. forward.
  assert (Hlt: Zlength (fr_t s hs j) = Zlength s - hs - j)
    by (unfold fr_t; rewrite Zlength_sublist; unfold ZSTD_blockHeaderSize in *; lia).
  forward_call (gv, Tsh, v_bp, ish, ibase, iN, ic, ioff + hs + j, fr_t s hs j).
  { entailer!. rewrite Hlt. reflexivity. }
  { sep_apply (zg_fold gv). cancel. }
  { unfold fr_t. apply (win_sub _ _ _ _ _ (hs + j) (Zlength s) (ioff + hs + j) Hwin);
      unfold ZSTD_blockHeaderSize in *; lia. }
  Intros vret. destruct vret as [cb bpv]; cbn [fst snd] in *.
  rewrite zg_eq. Intros.
  assert (Htb: bytes_ok (fr_t s hs j)) by (unfold fr_t; apply Forall_sublist; auto).
  forward_call cb.
  forward_if.
  { destruct (is_error_code cb) eqn:Hcb; [ | ctr].
    assert (Hde: dec_err cb).
    { destruct (cblock_size (fr_t s hs j)) eqn:Ec; [ | exact H9].
      exfalso. destruct H9 as [-> _]. apply cblock_size_range in Ec; auto.
      unfold is_error_code in Hcb. apply Z.ltb_lt in Hcb. lia. }
    assert (Hn: cblock_size (fr_t s hs j) = None).
    { destruct (cblock_size (fr_t s hs j)) eqn:Ec; auto.
      exfalso. destruct H9 as [-> _]. apply cblock_size_range in Ec; auto.
      unfold is_error_code in Hcb. apply Z.ltb_lt in Hcb. lia. }
    assert (Hxe: ox = None -> dm = no_dict -> pr = dparams_dflt -> e = ExtNone ->
                 frame_exact ts0 s ocap cb oc1 od 0 (ts_lxb st))
      by (apply (b1_exact j out st); auto).
    forward.
    Exists cb oc1 (fr_fs fs pr h hs fdid cold (fr_xx fs pr h out)) 0 d1 (ts_lxb st).
    rewrite Z.add_0_r, Z.sub_0_r.
    sep_apply (HT gv p ox st).
    sep_apply (fr_selR_post DENT W gv p fs ox dm e osh obase _ oc od ocap ish ibase _ ic ioff s pr dsp d l tbl xq
                 lent am hb h _ d1 HC).
    sep_apply (zg_fold gv). unfold fcore3, cfg_fmt, cfg_lit. entailer!.
    split; [ | split; [solve_cold | split; [intro Hl; apply Hlent; exact Hl | split; [intros _; eapply fr_fp; exact HC | ]]]].
    - apply (b1_err3 pr dsp dm s hs h j out st); auto.
    - apply (b1_codes3 pr dsp dm s hs h j out st); auto. }
  assert (Hcb: cblock_size (fr_t s hs j) = Some cb /\ bpv = bp_val (block_props_of (fr_t s hs j))).
  { destruct (cblock_size (fr_t s hs j)) eqn:Ec.
    - destruct H9 as [-> ->]. auto.
    - rewrite (proj1 H9) in H10. vm_compute in H10. discriminate H10. }
  clear H9 H10. destruct Hcb as [Hcb ->].
  assert (Hcbr: 0 <= cb < 2 ^ 21) by (eapply cblock_size_range; eauto).
  assert (H3t: 3 <= Zlength (fr_t s hs j)).
  { revert Hcb. unfold cblock_size. destruct (Zlength _ <? ZSTD_blockHeaderSize) eqn:E; [discriminate | ].
    intros _. apply Z.ltb_ge in E. unfold ZSTD_blockHeaderSize in E. lia. }
  forward. forward. forward. forward.
  rewrite add_uchar_long by auto. rewrite sub64_repr.
  dw0p (cb <= Zlength (fr_t s hs j) - ZSTD_blockHeaderSize).
  { forward_if.
    { errblk.
      assert (Hxe: ox = None -> dm = no_dict -> pr = dparams_dflt -> e = ExtNone ->
                   frame_exact ts0 s ocap (Int64.unsigned (Int64.repr (-72))) oc1 od 0 (ts_lxb st)).
      { apply (b1_exact j out st); auto. right. exists cb. split; auto. urepr. rewrite Hlt. unfold ZSTD_blockHeaderSize. lia. }
      forward.
      Exists (Int64.unsigned (Int64.repr (-72))) oc1 (fr_fs fs pr h hs fdid cold (fr_xx fs pr h out)) 0 d1 (ts_lxb st).
      rewrite Z.add_0_r, Z.sub_0_r. try rewrite Int64.repr_unsigned.
      sep_apply (HT gv p ox st).
      sep_apply (fr_selR_post DENT W gv p fs ox dm e osh obase _ oc od ocap ish ibase _ ic ioff s pr dsp d l tbl xq
                   lent am hb h _ d1 HC).
      sep_apply (zg_fold gv). unfold fcore3, cfg_fmt, cfg_lit. entailer!.
      assert (He72: is_error_code (Int64.unsigned (Int64.repr (-72))) = true) by reflexivity.
      split; [intro Hx; congruence | ]. split; [intro Hx; congruence | ].
      split; [intros _; split; [reflexivity | solve_dec_err] | ].
      assert (Hbig: exists c, cblock_size (fr_t s hs j) = Some c /\ c > Zlength (fr_t s hs j) - ZSTD_blockHeaderSize).
      { exists cb. split; auto. rewrite Hlt. unfold ZSTD_blockHeaderSize. lia. }
      split; [ | split; [solve_cold | split; [intro Hl; apply Hlent; exact Hl | split; [intro Hx; congruence | split; [intros _; eapply fr_fp; exact HC | split; [intro Hx; congruence | split; [ | intro Hx; congruence]]]]]]].
      - apply (b1_err3 pr dsp dm s hs h j out st); auto.
      - apply (b1_codes3 pr dsp dm s hs h j out st); auto. }
    forward. entailer!. urepr. rewrite Hlt. unfold ZSTD_blockHeaderSize. lia. }
  Intros. match goal with Hx: cb <= _ |- _ => rename Hx into Hcbl end.
  forward_if True. { ctr. } { forward. entailer!. }
  Intros.
  eapply semax_pre; [ | apply (Hk cb) ].
  unfold S_sw, fr_SEP, fr_LOC, fr_outP.
  entailer!.
  unfold ZSTD_blockHeaderSize; split; [f_equal; lia | do 2 f_equal; lia].
Qed.

End Seg.

End CM_Frame3_B1_1.
