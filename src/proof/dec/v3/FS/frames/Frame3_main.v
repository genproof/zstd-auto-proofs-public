(* FS3 one-shot frames: ZSTD_decompressFrame's body against ZSTD_decompressFrame_spec3: the prelude and the
   header (statements 0..9), then the loop and the end from fr_segs (port of v2 body_frame.v's
   body_decompressFrame). *)
Require Import Zstd.proof.dec.v3.FS.frames.Frames3Defs Zstd.proof.dec.v3.FS.frames.Frames3Model.
Require Import Zstd.proof.dec.v3.FS.frames.Frame3_codes.
Require Import Zstd.proof.model.ExHuf Zstd.proof.model.ExBlock Zstd.proof.model.ExFrame Zstd.proof.model.ExFrameFacts.
Local Open Scope logic.

Section CM_Frame3_main_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* the selection's set invariant *)
Lemma sel_res_hs_inv: forall DENT gv p pr sp d l tbl xq am hb,
  sel_res DENT gv p pr sp d l tbl xq am hb |-- !! (sel_on pr sp = true -> hs_inv l tbl).
Proof.
  intros. unfold sel_res. destruct (sel_on pr sp).
  - unfold hset_tbl. Intros tp. entailer!.
  - entailer!.
Qed.

(* the dictionary fields after ZSTD_decodeFrameHeader *)
Lemma dfh_dict_after: forall pr sp d l tbl fs did pcs x r fs' d',
  dfh_post3 (dmode_of pr) (sel_on pr sp) d l tbl fs did pcs x r fs' d' ->
  (sel_on pr sp = true -> hs_inv l tbl) -> dict_after pr sp l d d'.
Proof.
  intros pr sp d l tbl fs did pcs x r fs' d' Hd Hi.
  destruct (dfh3_dict _ _ _ _ _ _ _ _ _ _ _ _ Hd) as [-> | (h & _ & Hon & Hn & ->)].
  - left; reflexivity.
  - right. split; auto. exists (sel_r d l tbl (fh_dictID h)). split; auto.
    unfold sel_r in *. destruct (eq_dec (df_ddict d) nullval); [contradiction | ].
    apply hs_probe_in; auto.
Qed.

(* which DDict the header bytes selected through ZSTD_decodeFrameHeader *)
Lemma dfh_dict_sel: forall pr sp d l tbl fs did pcs x r fs' d',
  dfh_post3 (dmode_of pr) (sel_on pr sp) d l tbl fs did pcs x r fs' d' ->
  dict_sel pr sp l tbl x d d'.
Proof.
  intros pr sp d l tbl fs did pcs x r fs' d' Hd. unfold dict_sel. intros Hon h' Hg'.
  destruct (dfh3_dict _ _ _ _ _ _ _ _ _ _ _ _ Hd) as [-> | (h & Hg & _ & Hn & ->)].
  - left; reflexivity.
  - right. change (md_magicless (dmode_of pr)) with (dp_fmt pr =? 1) in Hg.
    rewrite Hg in Hg'. injection Hg' as <-.
    unfold sel_r in *. destruct (eq_dec (df_ddict d) nullval); [contradiction | ].
    split; [exact Hn | reflexivity].
Qed.

(* with the local DDict lent, the selection finds nothing *)
Lemma dfh_lent: forall pr sp d l tbl ox s fs did pcs r fs' d',
  lent_ok pr sp d l tbl ox s ->
  dfh_post3 (dmode_of pr) (sel_on pr sp) d l tbl fs did pcs
    (sublist 0 (header_size_m (dp_fmt pr =? 1) s) s) r fs' d' -> d' = d.
Proof.
  intros pr sp d l tbl ox s fs did pcs r fs' d' Hl Hd.
  destruct (dfh3_dict _ _ _ _ _ _ _ _ _ _ _ _ Hd) as [-> | (h & Hg & _ & Hn & _)]; [reflexivity | ].
  exfalso. apply Hn. destruct Hl as (_ & _ & Hf). apply Hf. exact Hg.
Qed.

(* fParams' dictID stays a 32-bit value through ZSTD_decodeFrameHeader *)
Lemma dfh3_fp: forall md sel d l tbl fs did pcs x r fs' d',
  dfh_post3 md sel d l tbl fs did pcs x r fs' d' -> bytes_ok x ->
  fp_ok (fs_fParams fs) -> fp_ok (fs_fParams fs').
Proof.
  intros md sel d l tbl fs did pcs x r fs' d' H Hb Hf. unfold dfh_post3 in H.
  destruct (get_frame_header_m (md_magicless md) x) as [|k|h] eqn:G.
  1,2: destruct H as (_ & _ & v & -> & [-> | E]); [exact Hf | exists 0; split; [exact E | rep_lia]].
  destruct (gfh3_range _ _ _ Hb G) as (_ & _ & _ & _ & Hd).
  destruct H as [_ H]. destruct (_ || _)%bool; destruct H as [_ ->];
    exists (fh_dictID h); (split; [reflexivity | rep_lia]).
Qed.

Lemma mg_sh_range: forall b, 0 <= mg_sh b <= 4.
Proof. intros []; simpl; lia. Qed.

Lemma fmin_signed: forall b, Int.signed (Int.repr (6 - mg_sh b)) = 6 - mg_sh b.
Proof. intros []; reflexivity. Qed.

(* the exact model (ExFrame.x_frame) refuses a frame whose header ZSTD_decodeFrameHeader refuses, without a
   dictionary (dictID 0) and with the default parameters: an unparsable header, or a Dictionary_ID other than 0 *)
Lemma fm_hdr_err_x: forall sel d l tbl fs pcs s cap r fs' d' (st: xstate),
  dfh_post3 (dmode_of dparams_dflt) sel d l tbl fs 0 pcs (sublist 0 (fhd_header_size (byte_at s 4)) s) r fs' d' ->
  is_error_code r = true ->
  ZSTD_FRAMEHEADERSIZE_MIN + ZSTD_blockHeaderSize <= Zlength s ->
  fhd_header_size (byte_at s 4) + ZSTD_blockHeaderSize <= Zlength s ->
  x_frame xstate (xst_begin xhuf) xblock st s cap = None.
Proof.
  intros sel d l tbl fs pcs s cap r fs' d' st Hd Hr H1 H2.
  rewrite x_frame_eq by assumption. cbv zeta.
  assert (Esl: slice s 0 (fhd_header_size (byte_at s 4)) = sublist 0 (fhd_header_size (byte_at s 4)) s)
    by (unfold slice; rewrite sublist_firstn; reflexivity).
  rewrite Esl. unfold dfh_post3 in Hd.
  change (get_frame_header_m (md_magicless (dmode_of dparams_dflt)) ?x) with (get_frame_header x) in Hd.
  destruct (get_frame_header (sublist 0 (fhd_header_size (byte_at s 4)) s)) as [ | k | h] eqn:G; try reflexivity.
  destruct (Z.eqb_spec (fh_dictID h) 0) as [E | E]; [ | reflexivity].
  exfalso. cbv zeta in Hd. destruct Hd as [_ Hd]. rewrite E in Hd. cbn [orb Z.eqb] in Hd.
  destruct Hd as [-> _]. discriminate Hr.
Qed.

(* an error return before the frame's block loop: the dictionary fields d'; the tables ts become uninitialised,
   litExtraBuffer keeping its bytes *)
Ltac err0 HT gv p ox ts rr oc' fs' d' LF :=
  Exists rr oc' fs' 0 d' (ts_lxb ts);
  rewrite ?Z.add_0_r, ?Z.sub_0_r; try rewrite Int64.repr_unsigned;
  sep_apply LF;
  sep_apply (HT gv p ox ts); try sep_apply (zg_fold gv); unfold fcore3, cfg_fmt, cfg_lit; entailer!;
  repeat match goal with
  | |- _ /\ _ => split
  | |- is_error_code _ = false -> _ =>
      let Hx := fresh "Hx" in intro Hx; first [vm_compute in Hx; discriminate Hx | congruence]
  | |- frame_res3 _ _ _ _ _ _ _ _ => apply fr_err3; [first [reflexivity | assumption] | ]
  | |- frame_codes3 _ _ _ _ _ => assumption
  | |- fs_dictEnd _ = fs_dictEnd _ => first [reflexivity | eapply dfh3_dictEnd; eassumption]
  | |- _ = Vint (Int.repr 0) \/ _ = Vint (Int.repr 1) => solve_cold
  | |- is_error_code _ = true -> _ /\ dec_err _ =>
      let Hx := fresh "Hx" in intro Hx; split; [reflexivity | solve_dec_err]
  | |- is_error_code _ = true -> dec_err _ => let Hx := fresh "Hx" in intro Hx; solve_dec_err
  | |- dec_err _ => solve_dec_err
  | Hxn: fx_on _ _ _ _ -> x_frame _ _ _ _ _ _ = None |- _ -> _ -> _ -> _ -> frame_exact _ _ _ _ _ _ _ _ =>
      let a := fresh "Ha" in let b := fresh "Hb" in let c := fresh "Hc" in let f := fresh "Hf" in
      intros a b c f; unfold frame_exact; rewrite (Hxn (conj a (conj b (conj c f))));
      first [reflexivity | assumption]
  | |- fp_ok ?a -> fp_ok ?a => exact (fun Hx => Hx)
  | |- fp_ok _ -> fp_ok _ => eapply dfh3_fp; [eassumption | apply Forall_sublist; assumption]
  | |- dict_after _ _ _ ?dd ?dd => left; reflexivity
  | |- _ = true -> ?dd = ?dd => intros; reflexivity
  | |- dict_after _ _ _ _ _ => eapply dfh_dict_after; eassumption
  | |- dict_sel _ _ _ _ _ ?dd ?dd => intros ? ? ?; left; reflexivity
  | |- dict_sel _ _ _ _ _ _ _ => eapply dfh_dict_sel; eassumption
  | Hl: ?b = true -> lent_ok _ _ _ _ _ _ _ /\ _ |- ?b = true -> _ = _ =>
      let Hx := fresh "Hx" in intro Hx; eapply dfh_lent; [apply (proj1 (Hl Hx)) | eassumption]
  end.

(* zstd's do { .. } while (0) changing x and y *)
Ltac dw0e2 x y Q :=
  repeat (apply -> seq_assoc);
  lazymatch goal with
  | |- semax _ (PROPx ?Ps (LOCALx ?Ls (SEPx ?Rs))) (Ssequence (Sloop _ Sbreak) _) _ =>
      let F := eval pattern x, y in Rs in
      lazymatch F with
      | ?G _ _ =>
          forward_loop (PROPx Ps (LOCALx Ls (SEPx Rs)))
            break: (EX x', EX y', PROPx (Q x' y' :: Ps) (LOCALx Ls (SEPx (G x' y'))));
          [apply andp_left2; apply derives_refl | ..]
      end
  end.

Ltac uurepr :=
  repeat match goal with Hx: context [Int.unsigned (Int.repr ?a)] |- _ =>
    rewrite (Int.unsigned_repr a) in Hx by rep_lia end.

Lemma body_decompressFrame3: forall DENT TABS SR BR, DENT_OK DENT -> TABS_OK TABS ->
  fr_segs DENT TABS SR BR ->
  body_ok (FR3_G DENT TABS SR BR) (ZSTD_decompressFrame_spec3 DENT TABS).
Proof.
  intros DENT TABS SR BR HD HT HSEG.
  exists f_ZSTD_decompressFrame; split; [reflexivity | split; [reflexivity | ]].
  start_function.
  match goal with Hx: ts_d ts = dm_state dm |- _ => rename Hx into Hts0 end.
  rename H14 into Hsm, H15 into H14.
  destruct o as [osh obase oN oc od ocap]; destruct i as [ish ibase iN ic ioff s].
  cbn [oa_sh oa_base oa_N oa_c oa_d oa_cap iw_sh iw_base iw_N iw_c iw_off iw_s] in *.
  unfold outarr_ok, inwin_ok, win_ok in H, H0; cbn [oa_sh oa_base oa_N oa_c oa_d oa_cap iw_sh iw_base iw_N iw_c iw_off iw_s] in H, H0.
  destruct H as (Hosh & HoN & HoN32 & Hod & Hocap & Hodcap).
  assert (Hwin: win_ok ish iN ic ioff (Zlength s) s) by exact H0.
  destruct H0 as (Hish & Hioff & HiN & HiN32 & HicN & _ & Hs & Hics).
  sep_apply (lent_to DENT gv p pr dsp d l tbl xq ox s e lent am hb H14). Intros.
  assert_PROP (isptr obase) as Hob by entailer!.
  assert_PROP (isptr ibase) as Hib by entailer!.
  forward. forward. forward. forward.
  forward_if (temp _t'1 (offset_val (od + ocap) obase)).
  { forward. entailer!. }
  { forward. entailer!.
    assert (ocap = 0) by (apply repr_inj_unsigned64; [rep_lia | rep_lia | exact H]).
    subst ocap; rewrite Z.add_0_r; auto. }
  forward. forward. forward.
  dw0. { forward. entailer!. }
  unfold fcore3, cfg_fmt, cfg_lit. Intros.
  match goal with Hx: par_ok pr |- _ => rename Hx into Hpar end.
  assert (Hfmt: dp_fmt pr = 0 \/ dp_fmt pr = 1) by apply Hpar.
  assert_PROP (sel_on pr dsp = true -> hs_inv l tbl) as Hinv by (sep_apply sel_res_hs_inv; entailer!).
  rewrite zg_eq. Intros.
  dw0p (ZSTD_FRAMEHEADERSIZE_MIN - mg_sh (dp_fmt pr =? 1) + ZSTD_blockHeaderSize <= Zlength s).
  { forward.
    forward_if (temp _t'2 (Vint (Int.repr (6 - mg_sh (dp_fmt pr =? 1))))).
    { forward. entailer!. match goal with Hx: dp_fmt pr = 0 |- _ => rewrite Hx; reflexivity end. }
    { forward. entailer!. destruct Hfmt as [E | E]; rewrite E in *; [ctr | reflexivity]. }
    forward.
    forward_if.
    { assert (Hcodes: frame_codes3 (dmode_of pr) dm s ocap (Int64.unsigned (Int64.repr (-72)))).
      { assert (Hu: decode_frame_m (dmode_of pr) dm no_wlim s = FUnk).
        { apply decode_frame3_short. left.
          cbn [md_magicless dmode_of]. rewrite fmin_signed in *.
          pose proof (mg_sh_range (dp_fmt pr =? 1)). urepr.
          unfold ZSTD_FRAMEHEADERSIZE_MIN, ZSTD_blockHeaderSize. lia. }
        apply fr_codes_none; rewrite Hu; [intros c sz Hd; discriminate | discriminate]. }
      assert (Hxn: fx_on ox dm e pr -> x_frame xstate (xst_begin xhuf) xblock (ts_x ts) s ocap = None).
      { intros _. apply x_frame_short. rewrite fmin_signed in *.
        pose proof (mg_sh_range (dp_fmt pr =? 1)). urepr.
        unfold ZSTD_FRAMEHEADERSIZE_MIN, ZSTD_blockHeaderSize. lia. }
      errblk. forward.
      err0 HT gv p ox ts (Int64.unsigned (Int64.repr (-72))) oc fs d (lent_from DENT gv p pr dsp d l tbl xq ox s e lent am hb H14).
      intros c sz Hd. rewrite decode_frame3_short in Hd; [discriminate | left].
      cbn [md_magicless dmode_of]. rewrite fmin_signed in *.
      pose proof (mg_sh_range (dp_fmt pr =? 1)). urepr.
      unfold ZSTD_FRAMEHEADERSIZE_MIN, ZSTD_blockHeaderSize. lia. }
    forward. entailer!. rewrite fmin_signed in *.
    pose proof (mg_sh_range (dp_fmt pr =? 1)). urepr.
    unfold ZSTD_FRAMEHEADERSIZE_MIN, ZSTD_blockHeaderSize. lia. }
  Intros. match goal with Hx: ZSTD_FRAMEHEADERSIZE_MIN - _ + _ <= _ |- _ => rename Hx into Hlen9 end.
  pose proof (mg_sh_range (dp_fmt pr =? 1)) as Hsh.
  assert (Hst: 1 <= starting_len (dp_fmt pr =? 1) <= 5 /\
               starting_len (dp_fmt pr =? 1) <= ZSTD_FRAMEHEADERSIZE_MIN - mg_sh (dp_fmt pr =? 1))
    by (destruct (dp_fmt pr =? 1); simpl; unfold ZSTD_FRAMEHEADERSIZE_PREFIX, ZSTD_FRAMEHEADERSIZE_MIN; lia).
  forward.
  forward_if (temp _t'3 (Vint (Int.repr (starting_len (dp_fmt pr =? 1))))).
  { forward. entailer!. match goal with Hx: dp_fmt pr = 0 |- _ => rewrite Hx; reflexivity end. }
  { forward. entailer!. destruct Hfmt as [E | E]; rewrite E in *; [ctr | reflexivity]. }
  forward.
  forward_call (gv, ish, ibase, iN, ic, ioff, sublist 0 (starting_len (dp_fmt pr =? 1)) s, dp_fmt pr).
  { entailer!. rewrite Zlength_sublist by (unfold ZSTD_blockHeaderSize in Hlen9; lia).
    rewrite Z.sub_0_r. destruct (dp_fmt pr =? 1); reflexivity. }
  { sep_apply (zg_fold gv). cancel. }
  {
    apply (win_sub _ _ _ _ _ 0 (starting_len (dp_fmt pr =? 1)) ioff Hwin); unfold ZSTD_blockHeaderSize in Hlen9; lia. }
  Intros vfhs.
  match goal with Hm: match frame_header_size_m _ _ with _ => _ end |- _ => rename Hm into Hfh end.
  unfold fmt_mg in Hfh. rewrite hsz3_prefix in Hfh by (unfold ZSTD_blockHeaderSize in Hlen9; lia).
  subst vfhs. set (hs := header_size_m (dp_fmt pr =? 1) s) in *.
  assert (Hhs: 6 - mg_sh (dp_fmt pr =? 1) <= hs <= 18 - mg_sh (dp_fmt pr =? 1))
    by (apply hs3_range; auto; unfold ZSTD_blockHeaderSize in Hlen9; lia).
  assert (Hhse: is_error_code hs = false) by (unfold is_error_code; apply Z.ltb_ge; lia).
  forward.
  forward_call hs. rewrite Hhse.
  forward_if True. { ctr. } { forward. entailer!. }
  Intros.
  rewrite zg_eq. Intros.
  dw0p (hs + ZSTD_blockHeaderSize <= Zlength s).
  { forward.
    forward_if.
    { assert (Hcodes: frame_codes3 (dmode_of pr) dm s ocap (Int64.unsigned (Int64.repr (-72)))).
      { assert (Hu: decode_frame_m (dmode_of pr) dm no_wlim s = FUnk).
        { apply decode_frame3_short. right.
          cbn [md_magicless dmode_of]. fold hs.
          match goal with Hx: Int64.ltu _ (Int64.add _ _) = _ |- _ => rewrite add64_repr in Hx end.
          urepr. unfold ZSTD_blockHeaderSize. lia. }
        apply fr_codes_none; rewrite Hu; [intros c sz Hd; discriminate | discriminate]. }
      assert (Hxn: fx_on ox dm e pr -> x_frame xstate (xst_begin xhuf) xblock (ts_x ts) s ocap = None).
      { intros (_ & _ & Hpr & _). apply x_frame_short_hs.
        assert (Ehs: hs = fhd_header_size (byte_at s 4)) by (unfold hs; rewrite Hpr; reflexivity).
        rewrite <- Ehs.
        match goal with Hx: Int64.ltu _ (Int64.add _ _) = _ |- _ => rewrite add64_repr in Hx end.
        urepr. unfold ZSTD_blockHeaderSize. lia. }
      errblk. forward.
      err0 HT gv p ox ts (Int64.unsigned (Int64.repr (-72))) oc fs d (lent_from DENT gv p pr dsp d l tbl xq ox s e lent am hb H14).
      intros c sz Hd. rewrite decode_frame3_short in Hd; [discriminate | right].
      cbn [md_magicless dmode_of]. fold hs. urepr. unfold ZSTD_blockHeaderSize. lia. }
    forward. entailer!. urepr. unfold ZSTD_blockHeaderSize. lia. }
  Intros. match goal with Hx: hs + ZSTD_blockHeaderSize <= _ |- _ => rename Hx into Hlenh end.
  dw0e2 fs d (fun fs' d' => dfh_post3 (dmode_of pr) (sel_on pr dsp) d l tbl fs (dm_id dm) 0 (sublist 0 hs s) 0 fs' d').
  { forward_call (gv, p, fs, dm_id dm, 0, pr, dsp, d, l, tbl, xq, ish, ibase, iN, ic, ioff, sublist 0 hs s, am, hb).
    { entailer!. rewrite Zlength_sublist by (unfold ZSTD_blockHeaderSize in Hlenh; lia).
      rewrite Z.sub_0_r. reflexivity. }
    { sep_apply (zg_fold gv). unfold fcore3, cfg_fmt, cfg_lit. entailer!. }
    {
      apply (win_sub _ _ _ _ _ 0 hs ioff Hwin); unfold ZSTD_blockHeaderSize in Hlenh; lia. }
    Intros vret. destruct vret as [[vr fs1] d1]; cbn [fst snd] in *.
    assert (Hl1: lent = true -> lent_ok pr dsp d1 l tbl ox s /\ lent_ext d1 e).
    { intros El. assert (Ed: d1 = d) by (eapply dfh_lent; [apply (proj1 (H14 El)) | eassumption]).
      rewrite Ed. exact (H14 El). }
    assert (Er: lent_rest lent d e = lent_rest lent d1 e).
    { destruct lent eqn:El; [ | reflexivity].
      rewrite (dfh_lent pr dsp d l tbl ox s _ _ _ _ _ _ (proj1 (H14 eq_refl)) ltac:(eassumption)). reflexivity. }
    rewrite Er. clear Er.
    unfold fcore3, cfg_fmt, cfg_lit. rewrite zg_eq. Intros.
    forward_call vr.
    forward_if.
    { destruct (is_error_code vr) eqn:Hvr; [ | ctr].
      assert (Hcodes: frame_codes3 (dmode_of pr) dm s ocap vr).
      { apply fr_codes_none.
        - intros c0 sz0 Hd0.
          match goal with Hd: dfh_post3 _ _ _ _ _ _ _ _ _ vr _ _ |- _ =>
            eapply (hdr_err_model3_any (dmode_of pr) (sel_on pr dsp) dm s _ _ _ _ _ _ _ eq_refl); eauto end.
        - match goal with Hd: dfh_post3 _ _ _ _ _ _ _ _ _ vr _ _ |- _ =>
            eapply (hdr_err_model3_ck (dmode_of pr) (sel_on pr dsp) dm s _ _ _ _ _ _ _ eq_refl); eauto end. }
      assert (Hxn: fx_on ox dm e pr -> x_frame xstate (xst_begin xhuf) xblock (ts_x ts) s ocap = None).
      { intros (_ & Hdm & Hpr & _).
        assert (Ehs: hs = fhd_header_size (byte_at s 4)) by (unfold hs; rewrite Hpr; reflexivity).
        assert (Emg: mg_sh (dp_fmt pr =? 1) = 0) by (rewrite Hpr; reflexivity).
        match goal with Hd: dfh_post3 _ _ _ _ _ _ _ _ _ vr _ _ |- _ =>
          rewrite Hpr, Hdm, Ehs in Hd; eapply fm_hdr_err_x; [exact Hd | exact Hvr | | ] end;
          unfold ZSTD_FRAMEHEADERSIZE_MIN, ZSTD_blockHeaderSize in *; lia. }
      errblk. forward.
      err0 HT gv p ox ts vr oc fs1 d1 (lent_from DENT gv p pr dsp d1 l tbl xq ox s e lent am hb Hl1).
      intros c0 sz0 Hd0. exfalso.
      match goal with Hd: dfh_post3 _ _ _ _ _ _ _ _ _ vr _ _ |- _ =>
        eapply (hdr_err_model3_any (dmode_of pr) (sel_on pr dsp) dm s _ _ _ _ _ _ _ eq_refl); eauto end. }
    match goal with Hx: Int.repr (if is_error_code vr then 1 else 0) = Int.zero |- _ =>
      destruct (is_error_code vr) eqn:Hvr; [vm_compute in Hx; discriminate Hx | ] end.
    match goal with Hx: dfh_post3 _ _ _ _ _ _ _ _ _ vr _ _ |- _ => pose proof (dfh3_r0 _ _ _ _ _ _ _ _ _ _ _ _ Hx Hvr) as Hvr0 end.
    subst vr.
    forward. Exists fs1 d1. entailer!. }
  Intros fs1 d1.
  match goal with Hx: dfh_post3 _ _ _ _ _ _ _ _ _ 0 fs1 d1 |- _ => rename Hx into Hdfh end.
  destruct (dfh3_ok0 _ _ _ _ _ _ _ _ _ _ _ Hdfh) as (h0 & Hgfh & Hd1 & Hdid & Efs1).
  rewrite Zlength_sublist, Z.sub_0_r, Z.add_0_l in Efs1 by (unfold ZSTD_blockHeaderSize in Hlenh; lia).
  forward. forward.
  rewrite add_uchar_long by auto. rewrite sub64_repr.
  forward.
  assert (Hbs: bytes_ok (sublist 0 hs s)) by (apply Forall_sublist; auto).
  destruct (gfh3_range _ _ _ Hbs Hgfh) as (Hbsm & Hck & Hcs & Hws & Hdi).
  set (fdid := if eq_dec (if sel_on pr dsp then sel_r d l tbl (fh_dictID h0) else nullval) nullval
               then dm_id dm else fh_dictID h0) in *.
  subst fs1.
  unfold frame_fields.
  cbn [fs_previousDstEnd fs_gpDictCopy fs_prefixStart fs_virtualStart fs_dictEnd fs_expected fs_fParams
       fs_processedCSize fs_decodedSize fs_bType fs_stage fs_xxh fs_headerSize fs_validateChecksum fs_rleSize
       fs_isFrameDecompression fs_dictID fs_ddictIsCold
       fsu_processedCSize fsu_xxh fsu_validateChecksum fsu_dictID fsu_fParams].
  Intros.
  assert (Hbmax: dp_bmax pr = 0 \/ 1024 <= dp_bmax pr <= ZSTD_BLOCKSIZE_MAX) by apply Hpar.
  assert (HB: ZSTD_BLOCKSIZE_MAX = 131072) by reflexivity.
  lazymatch goal with |- semax _ (PROPx ?Ps (LOCALx ?Ls (SEPx ?Rs))) _ _ =>
    let F := eval pattern (fh_val h0) in Rs in
    lazymatch F with ?G _ =>
      forward_if (PROPx Ps (LOCALx Ls (SEPx (G (fh_val (fh_cap (dmode_of pr) h0)))))) end end.
  { assert (Hbm: 1024 <= dp_bmax pr <= ZSTD_BLOCKSIZE_MAX).
    { destruct Hbmax as [E | E]; [ | exact E]. rewrite E in *. ctr. }
    forward. forward.
    forward_if (temp _t'8 (Vint (Int.repr (Z.min (fh_blockSizeMax h0) (dp_bmax pr))))).
    { forward. forward. entailer!. uurepr. rewrite Z.min_l by lia. reflexivity. }
    { forward. forward. entailer!. uurepr. rewrite Z.min_r by lia. reflexivity. }
    forward. entailer!.
    apply derives_refl'. f_equal. unfold fh_val, fh_cap, dmode_of. simpl.
    replace (dp_bmax pr =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
  { forward. entailer!.
    apply derives_refl'. f_equal. unfold fh_cap, dmode_of. cbn [md_bmax].
    match goal with Hx: dp_bmax pr = 0 |- _ => rewrite Hx end. simpl Z.eqb. cbv iota.
    rewrite Z.min_l by lia. destruct h0; reflexivity. }
  (* the loop and the end: the segment lemmas *)
  unfold MORE_COMMANDS, abbreviate.
  match goal with |- semax _ _ (Ssequence ?L ?K) _ =>
    change L with fr_loop; change K with (seq_drop 11 fr_body) end.
  set (h := fh_cap (dmode_of pr) h0).
  assert (HC: fr_ctx W fs ox dm e osh obase oN oc od ocap ish ibase iN ic ioff s pr dsp d l tbl lent h hs d1).
  { constructor; auto.
    - split; [exact Hs | ]. split; [exact Hlen9 | ]. split; [reflexivity | ]. split; [exact Hlenh | ].
      exists h0. split; [exact Hgfh | ]. split; [reflexivity | ]. split; [ | reflexivity].
      intros Hsel. unfold fdid in Hdid. rewrite Hsel in Hdid.
      destruct (eq_dec nullval nullval) as [_ | Hn]; [exact Hdid | contradiction Hn; reflexivity].
    - eapply dfh_dict_after; eassumption.
    - intros El. split; [eapply dfh_lent; [apply (proj1 (H14 El)) | eassumption] | exact (H14 El)].
    - eapply dfh_dict_sel; eassumption.
    - intros Hsel Hdd. unfold h; cbn [fh_cap fh_dictID]. split; [rep_lia | ].
      rewrite Hd1, Hsel. unfold sel_r. destruct (eq_dec (df_ddict d) nullval) as [E | _]; [contradiction | ].
      unfold sel_dict. destruct (eq_dec (hs_probe l tbl (fh_dictID h0)) nullval) as [E | E];
        [left; exact E | right; reflexivity]. }
  destruct (HSEG W gv p fs ox dm e osh obase oN oc od ocap ish ibase iN ic ioff s sp ssp v_blockProperties
              pr dsp d l tbl xq lent am hb h hs fdid d1 ts) as [Hloop Hend].
  eapply semax_pre; [ | apply (Hloop Espec (seq_drop 11 fr_body) HC Hts0); intros; apply Hend; exact HC ].
  (* the exact conjunct of the loop invariant at the first block *)
  assert (Hxi: fr_xinv ox dm e ocap s pr h hs ts 0 [] ts) by (eapply fr_xinv_init; eassumption).
  unfold S_inv, fr_SEP, fr_LOC, fr_outP, fr_selR.
  pose proof (fr_OT_init dm h s hs) as Hot0. rewrite <- Hts0 in Hot0.
  replace (vck (dmode_of pr) h0) with (vck (dmode_of pr) h) by reflexivity.
  assert (Hl1: lent = true -> lent_ok pr dsp d1 l tbl ox s /\ lent_ext d1 e).
  { intros El. assert (Ed: d1 = d) by (eapply dfh_lent; [apply (proj1 (H14 El)) | exact Hdfh]). rewrite Ed. exact (H14 El). }
  sep_apply (lent_from DENT gv p pr dsp d1 l tbl xq ox s e lent am hb Hl1).
  unfold frame_fields, fr_fs, fr_xx, fr_vck.
  cbn [fs_previousDstEnd fs_gpDictCopy fs_prefixStart fs_virtualStart fs_dictEnd fs_expected fs_fParams
       fs_processedCSize fs_decodedSize fs_bType fs_stage fs_xxh fs_headerSize fs_validateChecksum fs_rleSize
       fs_isFrameDecompression fs_dictID fs_ddictIsCold].
  entailer!.
  split3; [unfold ZSTD_blockHeaderSize in Hlenh; lia | constructor | apply sublist_nil].
Qed.

End CM_Frame3_main_1.
