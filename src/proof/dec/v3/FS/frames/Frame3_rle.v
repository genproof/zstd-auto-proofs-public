(* FS3 one-shot frames: an RLE block (case 1 of the switch) (port of v2 body_frame.v's fr_rle_ok). *)
Require Import Zstd.proof.dec.v3.FS.frames.Frames3Defs Zstd.proof.dec.v3.FS.frames.Frames3Model.
Require Import Zstd.proof.model.ExHuf Zstd.proof.model.ExBlock Zstd.proof.model.ExFrame Zstd.proof.model.ExFrameFacts.
Local Open Scope logic.

Section CM_Frame3_rle_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Section FrRle3.
Local Open Scope Z_scope.
Lemma fr_rle_c_r3: forall t c, bp_type (block_props_of t) = 1 -> cblock_size t = Some c -> c = 1.
Proof.
  intros t c Ht Hc. unfold cblock_size in Hc. rewrite Ht in Hc.
  destruct (Zlength t <? ZSTD_blockHeaderSize); [discriminate | ]. simpl in Hc. congruence.
Qed.

Lemma fr_rle_le_value_r3: forall l, bytes_ok l -> 0 <= le_value l < 2 ^ (8 * Zlength l).
Proof.
  induction l as [|b l IH]; intros Hl.
  - simpl. lia.
  - inversion Hl as [|? ? Hb Hl']; subst. specialize (IH Hl'). unfold is_byte in Hb.
    rewrite Zlength_cons. replace (8 * Z.succ (Zlength l)) with (8 + 8 * Zlength l) by lia.
    rewrite Z.pow_add_r by (pose proof (Zlength_nonneg l); lia). simpl le_value.
    change (2 ^ 8) with 256. nia.
Qed.

Lemma fr_rle_osz_r3: forall t, bytes_ok t -> 0 <= bp_origSize (block_props_of t) < 2 ^ 21.
Proof.
  intros t Ht.
  set (l := firstn (Z.to_nat 3) (skipn (Z.to_nat 0) t)).
  replace (bp_origSize (block_props_of t)) with (Z.shiftr (le_value l) 3) by reflexivity.
  assert (Hl: bytes_ok l) by (unfold l, bytes_ok in *; apply Forall_firstn; simpl; auto).
  assert (Hlen: Zlength l <= 3).
  { unfold l. rewrite Zlength_correct, firstn_length.
    pose proof (Nat.le_min_l (Z.to_nat 3) (length (skipn (Z.to_nat 0) t))). lia. }
  pose proof (fr_rle_le_value_r3 l Hl) as [A B].
  assert (2 ^ (8 * Zlength l) <= 2 ^ 24) by (apply Z.pow_le_mono_r; pose proof (Zlength_nonneg l); lia).
  rewrite Z.shiftr_div_pow2 by lia. split.
  - apply Z.div_pos; lia.
  - apply Z.div_lt_upper_bound; [lia | ]. change (2 ^ 3 * 2 ^ 21) with (2 ^ 24). lia.
Qed.

Lemma fr_rle_body_r3: forall t, byte_at (slice t 3 1) 0 = byte_at t 3.
Proof. intros t. destruct t as [|? [|? [|? [|? ?]]]]; reflexivity. Qed.

Lemma fr_rle_res_r3: forall st hist out t bsm ws st' out',
  bp_type (block_props_of t) = 1 ->
  blk_res st hist out t 1 bsm ws = Some (st', out') ->
  st' = st /\ out' = out ++ Zrepeat (byte_at t 3) (bp_origSize (block_props_of t)).
Proof.
  intros st hist out t bsm ws st' out' Ht Hr. unfold blk_res in Hr. rewrite Ht in Hr. simpl in Hr.
  change (Z.shiftr (le_field t 0 3) 3) with (bp_origSize (block_props_of t)) in Hr.
  destruct (orb _ _); [discriminate | ].
  inversion Hr. unfold ZSTD_blockHeaderSize. rewrite fr_rle_body_r3. unfold Zrepeat. auto.
Qed.

Lemma fr_put_sub_r3: forall oc d bs, 0 <= d -> d + Zlength bs <= Zlength oc ->
  sublist d (d + Zlength bs) (put_bytes oc d bs) = zbytes bs.
Proof. intros. unfold put_bytes. list_solve. Qed.

Lemma fr_put_unch_r3: forall oc d bs lo hi, 0 <= d -> d + Zlength bs <= Zlength oc -> lo <= d -> d + Zlength bs <= hi ->
  unchanged_outside oc (put_bytes oc d bs) lo hi.
Proof. intros. unfold unchanged_outside, put_bytes. intros. list_solve. Qed.

Lemma fr_out_wvp_r3: forall sh n c b i, writable_share sh -> 0 <= i <= n -> 0 < n ->
  data_at sh (tarray tuchar n) c b |-- weak_valid_pointer (offset_val i b).
Proof.
  intros. eapply derives_trans; [apply data_at_memory_block | ].
  simpl sizeof. rewrite Z.max_r by lia. replace (1 * n) with n by lia.
  apply memory_block_weak_valid_pointer; try lia; auto; apply writable_nonidentity; auto.
Qed.

Lemma fr_small_ok_r3: forall x, 0 <= x < 2 ^ 21 -> is_error_code x = false.
Proof. intros. unfold is_error_code. apply Z.ltb_ge. lia. Qed.

Lemma fr_rep_ok_r3: forall b n, 0 <= b < 256 -> bytes_ok (Zrepeat b n).
Proof. intros. unfold bytes_ok, Zrepeat. apply Forall_forall. intros x Hx. apply repeat_spec in Hx. subst. auto. Qed.

Lemma fr_pws_snoc_r3: forall WW w, pws_pred (WW ++ [w]) = (pws_pred WW * pw_pred w)%logic.
Proof.
  intros. unfold pws_pred. rewrite map_app, fold_right_sepcon_app. simpl. rewrite sepcon_emp. reflexivity.
Qed.

Lemma fr_wext_r3: forall WW sh n c base q, isptr q ->
  (pws_pred WW * data_at sh (tarray tuchar n) c base |--
   pws_pred (WW ++ [pw_bytes sh n c base]) * data_at sh (tarray tuchar 0) [] q)%logic.
Proof.
  intros. rewrite fr_pws_snoc_r3. simpl pw_pred.
  rewrite (data_at_zero_array_eq sh tuchar [] q) by auto. rewrite sepcon_emp. apply derives_refl.
Qed.

Lemma fr_wback_r3: forall WW sh n c base q,
  (pws_pred (WW ++ [pw_bytes sh n c base]) * data_at sh (tarray tuchar 0) [] q |--
   pws_pred WW * data_at sh (tarray tuchar n) c base)%logic.
Proof.
  intros. rewrite fr_pws_snoc_r3. simpl pw_pred.
  sep_apply (data_at_zero_array_inv sh tuchar [] q (eq_refl _) (eq_refl _)). cancel.
Qed.

Lemma fr_sub_pp_r3: forall p a c, isptr p ->
  force_val (sem_sub_pp tuchar (offset_val a p) (offset_val c p)) = Vlong (Int64.repr (a - c)).
Proof.
  intros. destruct p; try contradiction. unfold sem_sub_pp. simpl. rewrite if_true by auto. simpl.
  rewrite (Ptrofs.add_commut i (Ptrofs.repr a)), (Ptrofs.add_commut i (Ptrofs.repr c)).
  rewrite Ptrofs.sub_shifted. change (Ptrofs.repr 1) with Ptrofs.one. rewrite Ptrofs.divs_one by reflexivity.
  unfold Vptrofs. simpl. f_equal. unfold Ptrofs.to_int64. apply repr_eqm.
  unfold Ptrofs.sub. rewrite !Ptrofs.unsigned_repr_eq. change Ptrofs.modulus with (2^64).
  rewrite Zmod_mod. rewrite <- Zminus_mod. reflexivity.
Qed.

Lemma fr_pws_app_r3: forall W x, pws_pred (W ++ [x]) = (pws_pred W * pw_pred x)%logic.
Proof.
  intros. unfold pws_pred. induction W as [|a W IH]; simpl.
  - rewrite sepcon_emp, emp_sepcon. auto.
  - unfold pws_pred in IH. rewrite IH, sepcon_assoc. auto.
Qed.

End FrRle3.

(* the exact model's step on an RLE block (ExFrameFacts.xb_one): n copies of the block's byte when n fits in the
   room left (ocap minus the output so far), else the step fails; the tables are untouched *)
Lemma fr3l_xdec: forall ox dm e ocap s pr h hs j out st r n b,
  cblock_size (fr_t s hs j) = Some 1 -> 1 <= Zlength (fr_t s hs j) - 3 ->
  bp_type (block_props_of (fr_t s hs j)) = 1 -> bp_origSize (block_props_of (fr_t s hs j)) = n ->
  byte_at (fr_t s hs j) 3 = b ->
  (n >? ocap - Zlength out = true -> is_error_code r = true) ->
  (n >? ocap - Zlength out = false -> is_error_code r = false) ->
  fr_xdec ox dm e ocap s pr h hs j out st r st (Zrepeat b n).
Proof.
  intros ox dm e ocap s pr h hs j out st r n b Hc Hle Hty Hn Hb He Hok _.
  unfold xb_one. rewrite Hc. unfold ZSTD_blockHeaderSize.
  replace (1 >? Zlength (fr_t s hs j) - 3) with false by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
  cbv zeta. rewrite Hty, Hn. cbn [Z.eqb Pos.eqb].
  assert (Hb': byte_at (slice (fr_t s hs j) 3 1) 0 = b).
  { rewrite <- Hb. unfold byte_at, slice. change (Z.to_nat 3) with 3%nat. change (Z.to_nat 1) with 1%nat.
    change (Z.to_nat 0) with 0%nat. generalize (fr_t s hs j) as u. intros u.
    destruct u as [|? [|? [|? [|? ?]]]]; reflexivity. }
  rewrite Hb'. destruct (n >? ocap - Zlength out); [exact (He eq_refl) | auto].
Qed.

Section Seg.
Context (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR: blrel)
  (W: list ptr_witness) (gv: globals) (p: val) (fs: fstate) (ox: option ddx) (dm: dict_model) (e: ext_seg)
  (osh: share) (obase: val) (oN: Z) (oc: list val) (od ocap: Z)
  (ish: share) (ibase: val) (iN: Z) (ic: list val) (ioff: Z) (s: list Z) (sp ssp: val) (v_bp: val)
  (pr: dparams) (dsp: val) (d: dfields) (l: list (val * ddict_st)) (tbl: list val) (xq: option (val * val)) (lent: bool)
  (am: option cmem) (hb: Z) (h: frame_header) (hs: Z) (fdid: Z) (d1: dfields) (ts0: tstate).

Lemma fr_rle_ok3: DENT_OK DENT -> TABS_OK TABS ->
  fr_case_stmt DENT TABS SR BR W gv p fs ox dm e osh obase oN oc od ocap ish ibase iN ic ioff s sp ssp v_bp pr dsp d l tbl xq lent am hb h hs fdid d1 ts0 1.
Proof.
  intros HD HT. unfold fr_case_stmt. intros Espec j out oc1 st cold c Hctx Hty.
  change (fr_case 1) with
    (Ssequence
      (Ssequence
        (Sset _t'24 (Ederef (Etempvar _ip (tptr tuchar)) tuchar))
        (Ssequence
          (Sset _t'25 (Efield (Evar _blockProperties (Tstruct ___gp_blockProperties_t noattr)) _origSize tuint))
          (Scall (Some _t'13)
            (Evar _ZSTD_setRleBlock (Tfunction ((tptr tvoid) :: tulong :: tuchar :: tulong :: nil) tulong cc_default))
            ((Etempvar _op (tptr tuchar)) ::
             (Ecast (Ebinop Osub (Etempvar _oBlockEnd (tptr tuchar)) (Etempvar _op (tptr tuchar)) tlong) tulong) ::
             (Etempvar _t'24 tuchar) :: (Etempvar _t'25 tuint) :: nil))))
      (Sset _decodedSize (Etempvar _t'13 tulong))).
  destruct Hctx. unfold S_sw, S_dec, fr_SEP, fr_LOC, fr_outP. simpl app. Intros.
  pose proof fc_hdr as (Hbs & Hmin & Hhs & Hhs3 & _).
  assert (Hhs0: 0 <= hs).
  { unfold ZSTD_FRAMEHEADERSIZE_MIN, ZSTD_blockHeaderSize, mg_sh in Hmin. rewrite Hhs. unfold header_size_m.
    destruct (md_magicless (dmode_of pr)).
    - pose proof (fhs_range (byte_at s 0) (byte_at_range s 0 Hbs ltac:(lia))). lia.
    - pose proof (fhs_range (byte_at s 4) (byte_at_range s 4 Hbs ltac:(lia))). lia. }
  pose proof (fr_rle_c_r3 _ _ Hty H0) as Hc1. subst c.
  set (t := fr_t s hs j) in *.
  assert (Hbt: bytes_ok t) by (unfold t, fr_t; apply Forall_sublist; auto).
  assert (Hlt: Zlength t = Zlength s - (hs + j)) by (unfold t, fr_t; rewrite Zlength_sublist; lia).
  unfold ZSTD_blockHeaderSize in *.
  pose proof fc_win as (Hish & Hioff & HiN & HiN32 & HicN & _ & Hs & Hcs).
  assert (Hbyte: Znth (ioff + hs + (j + 3)) ic = Vint (Int.repr (byte_at t 3))).
  { replace (Znth (ioff + hs + (j + 3)) ic) with (Znth (hs + j + 3) (sublist ioff (ioff + Zlength s) ic))
      by (rewrite Znth_sublist by lia; f_equal; lia).
    rewrite Hcs, Znth_map by lia. f_equal. f_equal. unfold byte_at, t, fr_t.
    rewrite (@nth_Znth Z 0) by (rewrite Zlength_sublist; lia). rewrite Znth_sublist by lia. f_equal. lia. }
  pose proof (fr_rle_osz_r3 t Hbt) as Hosz.
  pose proof (byte_at_range t 3 Hbt ltac:(lia)) as Hb3.
  unfold fr_Delta. simplify_func_tycontext. abbreviate_semax.
  assert_PROP (offset_val (ioff + hs + (j + 3)) ibase =
               field_address (tarray tuchar iN) [ArraySubsc (ioff + hs + (j + 3))] ibase) as Hfa.
  { entailer!. rewrite field_address_offset by auto with field_compatible. simpl. f_equal. lia. }
  forward.
  { set (zz := Znth _ ic) in *. rewrite Hbyte. entailer!. rep_lia. }
  set (zz := Znth _ ic) in *. rewrite Hbyte. clear zz Hbyte.
  forward.
  match goal with |- context [temp _t'25 ?x] => change x with (Vint (Int.repr (bp_origSize (block_props_of t)))) end.
  set (n := bp_origSize (block_props_of t)) in *.
  set (b := byte_at t 3) in *.
  pose proof (Zlength_nonneg out) as Hol0.
  assert (Hcase: (0 < ocap - Zlength out \/ ocap = 0) \/ (0 < ocap /\ Zlength out = ocap)) by lia.
  destruct Hcase as [Hpos | [Hop Hfull]].
  - forward_call (W, Build_outarr osh obase oN oc1 (od + Zlength out) (ocap - Zlength out), b, n).
    { apply prop_right. destruct obase; try contradiction. unfold sameblock; simpl; destruct (peq b0 b0); [reflexivity | contradiction]. }
    { entailer!. rewrite fr_sub_pp_r3 by auto. simpl.
      rewrite zero_ext_inrange by (rewrite Int.unsigned_repr by rep_lia; change (two_p 8) with 256; lia).
      rewrite Int.unsigned_repr by rep_lia. do 2 f_equal. f_equal. f_equal. lia. }
    { split; [split; [assumption | simpl; repeat split; lia] | simpl; intros ].
      destruct Hpos; [lia | ]. replace (od + Zlength out) with od by lia. apply fc_W; lia. }
    Intros vret. destruct vret as [r oc']. cbn [fst snd oa_sh oa_base oa_N oa_c oa_d oa_cap] in *.
    forward.
    assert (Hrl: fr_RL dm h s hs j out st 1 r (Zrepeat b n) st).
    { intros _ _ st' out' Hb. rewrite rblock_rle in Hb by exact Hty. injection Hb as <- <-. split; reflexivity. }
    Exists r oc' st cold (Zrepeat b n).
    unfold S_dec, fr_SEP, fr_LOC, fr_outP. simpl app.
    match goal with Hif: if n >? _ then _ else _ |- _ => rename Hif into Hres end.
    destruct (n >? ocap - Zlength out) eqn:Egt.
    + destruct Hres as [Herr ->].
      assert (Hxd: fr_xdec ox dm e ocap s pr h hs j out st r st (Zrepeat b n)).
      { apply (fr3l_xdec ox dm e ocap s pr h hs j out st r n b); auto;
          [intros _; rewrite Herr; apply err_dst_is | intros Hx; congruence]. }
      rewrite Herr, err_dst_is. sep_apply (HT gv p ox st). entailer!.
      split; [intros _; exact dec_err_dst | ].
      intros st' out' Hr. apply fr_rle_res_r3 in Hr; [ | exact Hty]. destruct Hr as [-> ->].
      split; [discriminate | intros _]. rewrite Zlength_app, Zlength_Zrepeat by lia.
      apply Z.gtb_lt in Egt. lia.
    + destruct Hres as [-> ->].
      assert (Hxd: fr_xdec ox dm e ocap s pr h hs j out st n st (Zrepeat b n)).
      { apply (fr3l_xdec ox dm e ocap s pr h hs j out st n n b); auto;
          [intros Hx; congruence | intros _; exact (fr_small_ok_r3 n Hosz)]. }
      rewrite (fr_small_ok_r3 n Hosz). entailer!.
      rewrite Z.gtb_ltb, Z.ltb_ge in Egt.
      assert (Hzl: Zlength (Zrepeat b n) = n) by (apply Zlength_Zrepeat; lia).
      split; [apply fr_put_unch_r3; lia | ].
      split.
      * intros _. split; [lia | ]. split; [exact Hzl | ]. split; [apply fr_rep_ok_r3; lia | ].
        replace (od + Zlength out + n) with (od + Zlength out + Zlength (Zrepeat b n)) by lia.
        apply fr_put_sub_r3; lia.
      * intros st' out' Hr. apply fr_rle_res_r3 in Hr; [ | exact Hty]. destruct Hr as [-> ->].
        split; [auto | discriminate].
  - sep_apply (fr_wext_r3 W osh oN oc1 obase (offset_val (od + Zlength out) obase) ltac:(auto)).
    flatten_sepcon_in_SEP.
    forward_call (W ++ [pw_bytes osh oN oc1 obase],
                  Build_outarr osh (offset_val (od + Zlength out) obase) 0 [] 0 0, b, n).
    { apply prop_right. destruct obase; try contradiction. unfold sameblock; simpl; destruct (peq b0 b0); [reflexivity | contradiction]. }
    { entailer!. rewrite fr_sub_pp_r3 by auto. simpl.
      rewrite zero_ext_inrange by (rewrite Int.unsigned_repr by rep_lia; change (two_p 8) with 256; lia).
      rewrite Int.unsigned_repr by rep_lia. try rewrite offset_offset_val, Z.add_0_r.
      do 2 f_equal. f_equal. f_equal. lia. }
    { split; [split; [assumption | simpl; repeat split; try reflexivity; lia] | simpl; intros ].
      rewrite fr_pws_snoc_r3. apply sepcon_weak_valid_pointer2. simpl pw_pred.
      rewrite offset_offset_val, Z.add_0_r. apply fr_out_wvp_r3; auto; lia. }
    Intros vret. destruct vret as [r oc']. cbn [fst snd oa_sh oa_base oa_N oa_c oa_d oa_cap] in *.
    forward.
    assert (Hrl: fr_RL dm h s hs j out st 1 r (Zrepeat b n) st).
    { intros _ _ st' out' Hb. rewrite rblock_rle in Hb by exact Hty. injection Hb as <- <-. split; reflexivity. }
    Exists r oc1 st cold (Zrepeat b n).
    unfold S_dec, fr_SEP, fr_LOC, fr_outP. simpl app.
    match goal with Hif: if n >? _ then _ else _ |- _ => rename Hif into Hres end.
    destruct (n >? 0) eqn:Egt.
    + destruct Hres as [Herr ->].
      assert (Hxd: fr_xdec ox dm e ocap s pr h hs j out st r st (Zrepeat b n)).
      { apply (fr3l_xdec ox dm e ocap s pr h hs j out st r n b); auto;
          [intros _; rewrite Herr; apply err_dst_is | intros Hx; rewrite Hfull, Z.sub_diag in Hx; congruence]. }
      sep_apply (fr_wback_r3 W osh oN oc1 obase (offset_val (od + Zlength out) obase)).
      rewrite Herr, err_dst_is. sep_apply (HT gv p ox st). entailer!.
      try (split; [intros i Hi _; reflexivity | ]).
      split; [intros _; exact dec_err_dst | ].
      intros st' out' Hr. apply fr_rle_res_r3 in Hr; [ | exact Hty]. destruct Hr as [-> ->].
      split; [discriminate | intros _]. rewrite Zlength_app, Zlength_Zrepeat by lia.
      apply Z.gtb_lt in Egt. lia.
    + destruct Hres as [-> ->].
      assert (Hxd: fr_xdec ox dm e ocap s pr h hs j out st n st (Zrepeat b n)).
      { apply (fr3l_xdec ox dm e ocap s pr h hs j out st n n b); auto;
          [intros Hx; rewrite Hfull, Z.sub_diag in Hx; congruence | intros _; exact (fr_small_ok_r3 n Hosz)]. }
      assert (Hn0: n = 0) by (rewrite Z.gtb_ltb, Z.ltb_ge in Egt; lia).
      replace (put_bytes [] 0 (Zrepeat b n)) with (@nil val) by (rewrite Hn0; reflexivity).
      rewrite (fr_small_ok_r3 n Hosz).
      assert (Hzl: Zrepeat b n = []) by (rewrite Hn0; reflexivity).
      sep_apply (fr_wback_r3 W osh oN oc1 obase (offset_val (od + Zlength out) obase)).
      entailer!.
      try (split; [intros i Hi _; reflexivity | ]).
      split.
      * intros _. rewrite ?Hzl, ?Hn0, Z.add_0_r, sublist_nil. split; [lia | ]. split; [reflexivity | ].
        split; [constructor | reflexivity].
      * intros st' out' Hr. apply fr_rle_res_r3 in Hr; [ | exact Hty]. destruct Hr as [-> ->].
        split; [auto | discriminate].
Qed.

End Seg.

End CM_Frame3_rle_1.
