(* FS3 one-shot frames: a raw block (case 0 of the switch) (port of v2 body_frame.v's fr_raw_ok). *)
Require Import Zstd.proof.dec.v3.FS.frames.Frames3Defs Zstd.proof.dec.v3.FS.frames.Frames3Model.
Require Import Zstd.proof.model.ExHuf Zstd.proof.model.ExBlock Zstd.proof.model.ExFrame Zstd.proof.model.ExFrameFacts.
Local Open Scope logic.

Section CM_Frame3_raw_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* ---------- helpers of the raw block (v2 body_frame.v) ---------- *)

Lemma fr3r_le_value_nonneg: forall l, bytes_ok l -> 0 <= le_value l.
Proof.
  induction l as [|a l IH]; simpl; intros Hb; [lia | ].
  inversion Hb; subst. unfold is_byte in *. specialize (IH H2). lia.
Qed.

Lemma fr3r_raw_size: forall t c,
  bytes_ok t -> bp_type (block_props_of t) = 0 -> cblock_size t = Some c ->
  c = bp_origSize (block_props_of t) /\ 0 <= c.
Proof.
  intros t c Hb Ht Hc. unfold cblock_size in Hc. rewrite Ht in Hc. simpl in Hc.
  destruct (Zlength t <? ZSTD_blockHeaderSize); [discriminate | ]. inversion Hc; subst.
  split; auto. unfold block_props_of; simpl. apply Z.shiftr_nonneg. unfold le_field.
  apply fr3r_le_value_nonneg. unfold slice. apply Forall_firstn, Forall_skipn; auto.
Qed.

Lemma fr3r_slice_sub: forall (l: list Z) i k,
  0 <= i -> 0 <= k -> slice l i k = sublist i (i + k) l.
Proof.
  intros. unfold slice, sublist. rewrite firstn_skipn_comm. f_equal. f_equal. lia.
Qed.

Lemma fr3r_put_out: forall oc d bs lo hi,
  0 <= d -> d + Zlength bs <= Zlength oc -> lo <= d -> d + Zlength bs <= hi ->
  unchanged_outside oc (put_bytes oc d bs) lo hi.
Proof.
  intros. unfold unchanged_outside, put_bytes. intros i Hi Hn. pose proof (Zlength_nonneg bs).
  destruct (zlt i d).
  - rewrite app_Znth1 by (rewrite Zlength_sublist; lia). rewrite Znth_sublist by lia. f_equal; lia.
  - assert (d + Zlength bs <= i) by lia.
    rewrite app_Znth2 by (rewrite Zlength_sublist; lia).
    rewrite app_Znth2 by (rewrite Zlength_sublist, Zlength_map; lia).
    rewrite Znth_sublist by (rewrite ?Zlength_sublist, ?Zlength_map; lia).
    f_equal. rewrite Zlength_sublist, Zlength_map by lia. lia.
Qed.

Lemma fr3r_put_in: forall oc d bs,
  0 <= d -> d + Zlength bs <= Zlength oc -> sublist d (d + Zlength bs) (put_bytes oc d bs) = zbytes bs.
Proof. intros. unfold put_bytes. list_solve. Qed.

Lemma fr3r_sub_pp: forall p a c, isptr p ->
  force_val (sem_sub_pp tuchar (offset_val a p) (offset_val c p)) = Vlong (Int64.repr (a - c)).
Proof.
  intros. destruct p; try contradiction. unfold sem_sub_pp. simpl. rewrite if_true by auto. simpl.
  rewrite (Ptrofs.add_commut i (Ptrofs.repr a)), (Ptrofs.add_commut i (Ptrofs.repr c)).
  rewrite Ptrofs.sub_shifted. change (Ptrofs.repr 1) with Ptrofs.one. rewrite Ptrofs.divs_one by reflexivity.
  unfold Vptrofs. simpl. f_equal. unfold Ptrofs.to_int64. apply repr_eqm.
  unfold Ptrofs.sub. rewrite !Ptrofs.unsigned_repr_eq. change Ptrofs.modulus with (2^64).
  rewrite Zmod_mod. rewrite <- Zminus_mod. reflexivity.
Qed.

Lemma fr3r_pws_app: forall W x, pws_pred (W ++ [x]) = pws_pred W * pw_pred x.
Proof.
  intros. unfold pws_pred. induction W as [|a W IH]; simpl.
  - rewrite sepcon_emp, emp_sepcon. auto.
  - unfold pws_pred in IH. rewrite IH, sepcon_assoc. auto.
Qed.

(* the header size is nonnegative *)
Lemma fr3r_hs0: forall md sel dm s hs h, fr_hdr3 md sel dm s hs h -> 0 <= hs.
Proof.
  intros md sel dm s hs h (Hb & Hm & Hhs & _). subst hs. unfold header_size_m, mg_sh in *.
  unfold ZSTD_FRAMEHEADERSIZE_MIN, ZSTD_blockHeaderSize in Hm.
  destruct (md_magicless md).
  - pose proof (fhs_range _ (byte_at_range s 0 Hb ltac:(lia))). lia.
  - pose proof (fhs_range _ (byte_at_range s 4 Hb ltac:(lia))). lia.
Qed.

(* the exact model's step on a raw block (ExFrameFacts.xb_one): the block's body is copied when it fits in the room
   left (ocap minus the output so far), else the step fails; the tables are untouched *)
Lemma fr3r_xdec: forall ox dm e ocap s pr h hs j out st r c body,
  cblock_size (fr_t s hs j) = Some c -> c <= Zlength (fr_t s hs j) - 3 ->
  bp_type (block_props_of (fr_t s hs j)) = 0 -> slice (fr_t s hs j) 3 c = body ->
  (c >? ocap - Zlength out = true -> is_error_code r = true) ->
  (c >? ocap - Zlength out = false -> is_error_code r = false) ->
  fr_xdec ox dm e ocap s pr h hs j out st r st body.
Proof.
  intros ox dm e ocap s pr h hs j out st r c body Hc Hle Hty Hbd He Hok _.
  unfold xb_one. rewrite Hc. unfold ZSTD_blockHeaderSize.
  replace (c >? Zlength (fr_t s hs j) - 3) with false by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
  cbv zeta. rewrite Hty, Hbd. cbn [Z.eqb Pos.eqb].
  destruct (c >? ocap - Zlength out); [exact (He eq_refl) | auto].
Qed.

Section Seg.
Context (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR: blrel)
  (W: list ptr_witness) (gv: globals) (p: val) (fs: fstate) (ox: option ddx) (dm: dict_model) (e: ext_seg)
  (osh: share) (obase: val) (oN: Z) (oc: list val) (od ocap: Z)
  (ish: share) (ibase: val) (iN: Z) (ic: list val) (ioff: Z) (s: list Z) (sp ssp: val) (v_bp: val)
  (pr: dparams) (dsp: val) (d: dfields) (l: list (val * ddict_st)) (tbl: list val) (xq: option (val * val)) (lent: bool)
  (am: option cmem) (hb: Z) (h: frame_header) (hs: Z) (fdid: Z) (d1: dfields) (ts0: tstate).

Lemma fr_raw_ok3: DENT_OK DENT -> TABS_OK TABS ->
  fr_case_stmt DENT TABS SR BR W gv p fs ox dm e osh obase oN oc od ocap ish ibase iN ic ioff s sp ssp v_bp pr dsp d l tbl xq lent am hb h hs fdid d1 ts0 0.
Proof.
  intros HD HT. unfold fr_case_stmt. intros Espec j out oc1 st cold c Hctx Hty.
  change (fr_case 0) with
    (Ssequence
      (Scall (Some _t'12)
        (Evar _ZSTD_copyRawBlock (Tfunction ((tptr tvoid) :: tulong :: (tptr tvoid) :: tulong :: nil) tulong cc_default))
        ((Etempvar _op (tptr tuchar)) ::
         (Ecast (Ebinop Osub (Etempvar _oend (tptr tuchar)) (Etempvar _op (tptr tuchar)) tlong) tulong) ::
         (Etempvar _ip (tptr tuchar)) :: (Etempvar _cBlockSize tulong) :: nil))
      (Sset _decodedSize (Etempvar _t'12 tulong))).
  destruct Hctx. unfold S_sw, S_dec, fr_SEP, fr_LOC, fr_outP. simpl app. Intros.
  pose proof (fr3r_hs0 _ _ _ _ _ _ fc_hdr) as Hhs0.
  pose proof fc_hdr as (Hbs & Hmin & Hhs & Hhs3 & Hgfh).
  set (t := fr_t s hs j) in *.
  assert (Hbt: bytes_ok t) by (unfold t, fr_t; apply Forall_sublist; auto).
  destruct (fr3r_raw_size t c Hbt Hty H0) as [Hco Hc0].
  assert (Hlt: Zlength t = Zlength s - (hs + j)) by (unfold t, fr_t; rewrite Zlength_sublist; lia).
  unfold ZSTD_blockHeaderSize in *.
  set (body := slice t 3 c).
  assert (Hbody: body = sublist (hs + j + 3) (hs + j + 3 + c) s).
  { unfold body. rewrite fr3r_slice_sub by lia. unfold t, fr_t. rewrite sublist_sublist by lia. f_equal; lia. }
  assert (Hlb: Zlength body = c) by (rewrite Hbody, Zlength_sublist; lia).
  assert (Hwin: inwin_ok (Build_inwin ish ibase iN ic (ioff + hs + (j + 3)) body)).
  { unfold inwin_ok; simpl. rewrite Hbody. eapply win_sub; eauto; lia. }
  assert (Hbd: slice t 3 c = body) by reflexivity. clear Hco Hhs. clearbody body.
  unfold fr_Delta. abbreviate_semax.
  freeze [0;1;2;4;5;6;7;8;9;10;11;12;13;16;17;18] FR1.
  pose proof (Zlength_nonneg out) as Hout0.
  destruct (zlt (Zlength out) ocap) as [Hol | Hoe].
  - forward_call (W, Build_outarr osh obase oN oc1 (od + Zlength out) (ocap - Zlength out),
                  Build_inwin ish ibase iN ic (ioff + hs + (j + 3)) body).
    { entailer!. destruct obase; try contradiction. simpl. destruct (peq b b); [reflexivity | congruence]. }
    { entailer!. simpl. rewrite fr3r_sub_pp by auto. rewrite Zlength_sublist by lia.
      replace (hs + j + 3 + c - (hs + j + 3)) with c by lia.
      replace (od + ocap - (od + Zlength out)) with (ocap - Zlength out) by lia. reflexivity. }
    { unfold outarr_ok; cbn [oa_cap oa_d oa_sh oa_N oa_c oa_base].
      split; [refine (conj fc_osh _); repeat split; lia | intros; lia]. }
    cbn [oa_cap oa_d oa_sh oa_N oa_c oa_base iw_s iw_sh iw_N iw_c iw_base iw_off].
    Intros vret. destruct vret as [r oc2]; simpl fst in *; simpl snd in *.
    forward. thaw FR1. rewrite Hlb in *.
    assert (Hcs: c <= Zlength s) by lia.
    assert (Hcerr: is_error_code c = false) by (unfold is_error_code; apply Z.ltb_ge; destruct fc_win as (_ & ? & ? & ? & _); lia).
    assert (Hbb: bytes_ok body) by (rewrite Hbody; apply Forall_sublist; auto).
    assert (Hblk: blk_res st (dm_content dm) out t c (fh_blockSizeMax h) (fh_windowSize h) =
                  if c >? fh_blockSizeMax h then None else Some (ts_d st, out ++ body)).
    { unfold blk_res. rewrite Hty. simpl. unfold ZSTD_blockHeaderSize. rewrite Hbd. reflexivity. }
    match goal with Hif: context [if (c >? ocap - Zlength out) then _ else _] |- _ =>
      destruct (c >? ocap - Zlength out) eqn:Hcmp; destruct Hif as [Hr Hoc] end.
    + (* the output is too small *)
      subst oc2.
      assert (Hrl: fr_RL dm h s hs j out st c r body st).
      { intros _ _ st' out' Hb. rewrite rblock_raw in Hb by exact Hty. injection Hb as <- <-.
        split; [f_equal; exact Hbd | reflexivity]. }
      Exists r oc1 st cold body.
      assert (Herr: is_error_code r = true) by (rewrite Hr; apply err_dst_is).
      assert (Hxd: fr_xdec ox dm e ocap s pr h hs j out st r st body)
        by (apply (fr3r_xdec ox dm e ocap s pr h hs j out st r c body); auto; congruence).
      rewrite Herr. sep_apply (HT gv p ox st). entailer!.
      split; [intros _; exact dec_err_dst | ].
      intros st' out' Hb. rewrite Hblk in Hb. destruct (c >? fh_blockSizeMax h); inversion Hb; subst.
      split; intros Hx; [discriminate Hx | ]. rewrite Zlength_app, Zlength_sublist by lia.
      apply Z.gtb_lt in Hcmp. lia.
    + subst r oc2.
      assert (Hrl: fr_RL dm h s hs j out st c c body st).
      { intros _ _ st' out' Hb. rewrite rblock_raw in Hb by exact Hty. injection Hb as <- <-.
        split; [f_equal; exact Hbd | reflexivity]. }
      assert (Hxd: fr_xdec ox dm e ocap s pr h hs j out st c st body)
        by (apply (fr3r_xdec ox dm e ocap s pr h hs j out st c c body); auto; congruence).
      Exists c (put_bytes oc1 (od + Zlength out) body) st cold body. rewrite Hcerr. entailer!.
      assert (Hcm: c <= ocap - Zlength out) by (rewrite Z.gtb_ltb in Hcmp; apply Z.ltb_ge in Hcmp; lia).
      set (B := sublist (hs + j + 3) (hs + j + 3 + c) s) in *.
      assert (HL: Zlength B = c) by (unfold B; rewrite Zlength_sublist; lia).
      split; [ | split].
      { apply fr3r_put_out; lia. }
      { intros _. split; [lia | split; [auto | split; [auto | ]]].
        replace (od + Zlength out + c) with (od + Zlength out + Zlength B) by lia. apply fr3r_put_in; lia. }
      { intros st' out' Hb. rewrite Hblk in Hb. destruct (c >? fh_blockSizeMax h); [discriminate | ].
        injection Hb as <- <-. split; intros; [split; auto | discriminate]. }
  - (* no room left: op = oend; the callee's weak validity of op comes from the output array, moved
       into its witness list; its output is the empty array at op *)
    assert (Heq: Zlength out = ocap) by lia.
    assert (Hop: isptr (offset_val (od + Zlength out) obase)) by (destruct obase; try contradiction; simpl; auto).
    assert (Hwv: pws_pred W * data_at osh (tarray tuchar oN) oc1 obase |--
                 weak_valid_pointer (offset_val (od + Zlength out) obase)).
    { destruct (Z.eq_dec ocap 0) as [Hz | Hz].
      - rewrite Heq, Hz, Z.add_0_r.
        eapply derives_trans; [apply sepcon_derives; [apply fc_W; auto | apply derives_refl] | ].
        apply extend_weak_valid_pointer.
      - rewrite sepcon_comm.
        eapply derives_trans; [apply sepcon_derives; [apply data_at_memory_block | apply derives_refl] | ].
        eapply derives_trans; [apply sepcon_derives; [apply memory_block_weak_valid_pointer | apply derives_refl] | ].
        4: apply extend_weak_valid_pointer.
        all: simpl; try rewrite Z.max_r by lia; try lia.
        apply readable_nonidentity, writable_readable; auto. }
    gather_SEP (pws_pred W) (data_at osh (tarray tuchar oN) oc1 obase).
    replace_SEP 0 (pws_pred (W ++ [pw_bytes osh oN oc1 obase]) *
                   data_at osh (tarray tuchar 0) [] (offset_val (od + Zlength out) obase)).
    { entailer!. rewrite fr3r_pws_app. simpl pw_pred. rewrite data_at_tuchar_zero_array_eq by auto. cancel. }
    flatten_sepcon_in_SEP.
    forward_call (W ++ [pw_bytes osh oN oc1 obase],
                  Build_outarr osh (offset_val (od + Zlength out) obase) 0 [] 0 0,
                  Build_inwin ish ibase iN ic (ioff + hs + (j + 3)) body).
    { entailer!. destruct obase; try contradiction. simpl. destruct (peq b b); [reflexivity | congruence]. }
    { entailer!. simpl. rewrite fr3r_sub_pp by auto. rewrite Zlength_sublist by lia.
      replace (hs + j + 3 + c - (hs + j + 3)) with c by lia.
      replace (od + Zlength out - (od + Zlength out)) with 0 by lia.
      try rewrite isptr_offset_val_zero by auto. reflexivity. }
    { unfold outarr_ok; cbn [oa_cap oa_d oa_sh oa_N oa_c oa_base].
      split; [refine (conj fc_osh _); repeat split; try reflexivity; lia | ].
      intros _. try rewrite isptr_offset_val_zero by auto. rewrite fr3r_pws_app. exact Hwv. }
    cbn [oa_cap oa_d oa_sh oa_N oa_c oa_base iw_s iw_sh iw_N iw_c iw_base iw_off].
    Intros vret. destruct vret as [r oc2]; simpl fst in *; simpl snd in *.
    forward. thaw FR1. rewrite Hlb in *. rewrite fr3r_pws_app. simpl pw_pred.
    assert (Hblk: blk_res st (dm_content dm) out t c (fh_blockSizeMax h) (fh_windowSize h) =
                  if c >? fh_blockSizeMax h then None else Some (ts_d st, out ++ body)).
    { unfold blk_res. rewrite Hty. simpl. unfold ZSTD_blockHeaderSize. rewrite Hbd. reflexivity. }
    match goal with Hif: context [if (c >? 0) then _ else _] |- _ =>
      destruct (c >? 0) eqn:Hcmp; destruct Hif as [Hr Hoc] end.
    + (* c > 0: the output is too small *)
      subst oc2. sep_apply (data_at_tuchar_zero_array_inv osh (offset_val (od + Zlength out) obase)).
      assert (Hrl: fr_RL dm h s hs j out st c r body st).
      { intros _ _ st' out' Hb. rewrite rblock_raw in Hb by exact Hty. injection Hb as <- <-.
        split; [f_equal; exact Hbd | reflexivity]. }
      Exists r oc1 st cold body.
      assert (Herr: is_error_code r = true) by (rewrite Hr; apply err_dst_is).
      assert (Hxd: fr_xdec ox dm e ocap s pr h hs j out st r st body)
        by (apply (fr3r_xdec ox dm e ocap s pr h hs j out st r c body); auto;
            rewrite Heq, Z.sub_diag; congruence).
      rewrite Herr. sep_apply (HT gv p ox st). entailer!.
      split; [intros _; exact dec_err_dst | ].
      intros st' out' Hb. rewrite Hblk in Hb. destruct (c >? fh_blockSizeMax h); inversion Hb; subst.
      split; intros Hx; [discriminate Hx | ]. rewrite Zlength_app, Zlength_sublist by lia.
      apply Z.gtb_lt in Hcmp. lia.
    + assert (c = 0) by (rewrite Z.gtb_ltb in Hcmp; apply Z.ltb_ge in Hcmp; lia). subst c r.
      assert (Hb0: body = []) by (apply Zlength_nil_inv; auto). subst body. subst oc2.
      change (put_bytes [] 0 []) with (@nil val).
      sep_apply (data_at_tuchar_zero_array_inv osh (offset_val (od + Zlength out) obase)).
      assert (Hrl: fr_RL dm h s hs j out st 0 0 [] st).
      { intros _ _ st' out' Hb. rewrite rblock_raw in Hb by exact Hty. injection Hb as <- <-.
        split; [f_equal; exact Hbd | reflexivity]. }
      assert (Hxd: fr_xdec ox dm e ocap s pr h hs j out st 0 st [])
        by (apply (fr3r_xdec ox dm e ocap s pr h hs j out st 0 0 []); auto; rewrite Heq, Z.sub_diag; easy).
      Exists 0 oc1 st cold (@nil Z). change (is_error_code 0) with false. entailer!.
      split.
      { intros _. split; [lia | split; [reflexivity | split; [constructor | apply sublist_nil]]]. }
      { intros st' out' Hb. rewrite Hblk in Hb. destruct (_ >? _); [discriminate | ]. injection Hb as <- <-.
        split; intros; [split; auto | discriminate]. }
Qed.

End Seg.

End CM_Frame3_raw_1.
