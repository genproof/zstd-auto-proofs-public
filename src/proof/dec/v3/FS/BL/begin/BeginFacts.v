(* FS3-bl BEGIN: facts for BL_begin_sub: BR of a frame just begun, base_rel3 after set_bl
   (and set_ex: the buffer-less API clears dc_ex), the context split into what B's Begin specs take and the rest,
   dictionary model facts. *)
Require Export Zstd.proof.dec.v3.FS.BL.BLDefs.
Local Open Scope logic.

Section CM_BeginFacts_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* ---------- dictionary models (copied from v2 body_multiframe) ---------- *)

Lemma bgf_le_value_range: forall l, bytes_ok l -> 0 <= le_value l < 256 ^ Zlength l.
Proof.
  induction l as [| b l IH]; intros Hb; simpl; [lia |].
  inversion Hb as [| ? ? Hb1 Hb2]; subst. specialize (IH Hb2). unfold is_byte in Hb1.
  rewrite Zlength_cons, Z.pow_succ_r by (apply Zlength_nonneg). nia.
Qed.

Lemma bgf_le_field_4_range: forall l i, bytes_ok l -> 0 <= le_field l i 4 <= Int.max_unsigned.
Proof.
  intros. unfold le_field, slice.
  assert (Hok: bytes_ok (firstn (Z.to_nat 4) (skipn (Z.to_nat i) l))).
  { unfold bytes_ok in *. apply Forall_firstn, Forall_skipn. auto. }
  pose proof (bgf_le_value_range _ Hok).
  assert (Zlength (firstn (Z.to_nat 4) (skipn (Z.to_nat i) l)) <= 4).
  { rewrite Zlength_correct, firstn_length. lia. }
  assert (256 ^ Zlength (firstn (Z.to_nat 4) (skipn (Z.to_nat i) l)) <= 256 ^ 4)
    by (apply Z.pow_le_mono_r; [lia | auto]).
  rep_lia.
Qed.

Lemma bgf_dict_id_of_range: forall b, bytes_ok b -> 0 <= dict_id_of b <= Int.max_unsigned.
Proof.
  intros. unfold dict_id_of. destruct (Zlength b <? 8); [rep_lia |].
  destruct (negb _); [rep_lia | apply bgf_le_field_4_range; auto].
Qed.

Lemma bgf_dict_auto_c_suffix: forall b ores dm, dict_auto_c b ores = Some dm -> exists pre, b = pre ++ dm_content dm.
Proof.
  unfold dict_auto_c. intros b ores dm H.
  destruct (Zlength b <? 8); [inversion H; subst; exists nil; reflexivity |].
  destruct (negb _); [inversion H; subst; exists nil; reflexivity |].
  destruct ores as [[st es] |]; inversion H; subst; simpl.
  exists (firstn (Z.to_nat es) b). symmetry. apply firstn_skipn.
Qed.

Lemma bgf_dict_auto_c_id: forall b ores dm, dict_auto_c b ores = Some dm -> dm_id dm = dict_id_of b.
Proof.
  unfold dict_auto_c, dict_id_of. intros b ores dm H.
  destruct (Zlength b <? 8); [inversion H; subst; reflexivity |].
  destruct (negb _); [inversion H; subst; reflexivity |].
  destruct ores as [[st es] |]; inversion H; subst; reflexivity.
Qed.

Lemma bgf_ddx_model_facts: forall x dm, ddx_model x = Some dm ->
  dm_id dm = (if dx_raw x then 0 else dict_id_of (dx_bytes x)) /\ dm_state dm = ddx_state x /\
  exists pre, dx_bytes x = pre ++ dm_content dm.
Proof.
  intros x dm H. unfold ddx_model, ddx_state, ddx_ent, ddict_ent_c in *.
  destruct (dx_raw x).
  - inversion H; subst. simpl. split; [auto | split; [auto | exists nil; auto]].
  - pose proof (bgf_dict_auto_c_suffix _ _ _ H) as Hs. split; [| split; [| auto]].
    + eapply bgf_dict_auto_c_id; eauto.
    + unfold dict_auto_c, is_formatted in *.
      destruct (Zlength (dx_bytes x) <? 8) eqn:E1.
      * inversion H; subst. simpl. rewrite Z.ltb_lt in E1. replace (8 <=? Zlength (dx_bytes x)) with false
          by (symmetry; apply Z.leb_gt; lia). reflexivity.
      * rewrite Z.ltb_ge in E1. replace (8 <=? Zlength (dx_bytes x)) with true by (symmetry; apply Z.leb_le; lia).
        simpl. destruct (le_field (dx_bytes x) 0 4 =? ZSTD_MAGIC_DICTIONARY); simpl in *.
        -- destruct (dx_ld x) as [[st es] |]; inversion H; auto.
        -- inversion H; auto.
Qed.

Lemma bgf_suffix_sublist (b c: list Z) : (exists pre, b = pre ++ c) ->
  sublist (Zlength b - Zlength c) (Zlength b) b = c.
Proof.
  intros [pre ->]. rewrite Zlength_app.
  replace (Zlength pre + Zlength c - Zlength c) with (Zlength pre) by lia.
  rewrite sublist_app2 by (pose proof (Zlength_nonneg pre); lia).
  replace (Zlength pre - Zlength pre) with 0 by lia.
  replace (Zlength pre + Zlength c - Zlength pre) with (Zlength c) by lia.
  apply sublist_same; auto.
Qed.

Lemma bgf_suffix_len (b c: list Z) : (exists pre, b = pre ++ c) -> 0 <= Zlength b - Zlength c <= Zlength b.
Proof. intros [pre ->]. rewrite Zlength_app. pose proof (Zlength_nonneg pre). pose proof (Zlength_nonneg c). lia. Qed.

(* ---------- BR of a frame just begun ---------- *)

Definition bgf_v0 : blv :=
  {| bv_stage := BHdrPrefix; bv_hdr := nil; bv_hs := 0; bv_h := fh_none; bv_bt := 0; bv_rle := 0 |}.

Lemma BR_begin (st: dctx_st) (odr: option dictref) (od: option bldict) (fs: fstate) (ts: tstate) (hb: list val) :
  par_ok (dc_par st) ->
  fs_expected fs = Vlong (Int64.repr (starting_len (dp_fmt (dc_par st) =? 1))) ->
  fs_stage fs = Vint (Int.repr 0) ->
  fs_isFrameDecompression fs = Vint (Int.repr 1) -> cold01 fs ->
  fs_dictID fs = Vint (Int.repr (bd_idz od)) ->
  fs_processedCSize fs = Vlong (Int64.repr 0) -> fs_decodedSize fs = Vlong (Int64.repr 0) ->
  Zlength hb = 18 -> bd_wf od ->
  fs_previousDstEnd fs = bd_end od -> fs_prefixStart fs = bd_start od -> fs_virtualStart fs = bd_start od ->
  fs_dictEnd fs = bd_de0o od -> fs_gpDictCopy fs = Vint (Int.repr (bd_g0o od)) ->
  (forall dm, dictref_model odr = Some dm -> dm_state dm = ts_d ts) ->
  bd_model_ok odr od -> bd_rel odr od ->
  BR (dc_par st) (bl_begin st odr) fs (TInit (bd_oxo od) ts) hb.
Proof.
  intros Hpar He Hs Hi Hc Hid Hp Hd Hhb Hwf Hpe Hps Hvs Hde Hg Hts Hmo Hrel.
  split; [exact Hpar|]. exists od, 0, ts. split; [reflexivity|].
  split; [intros o Ho; unfold bl_osz, bl_begin in Ho; simpl in Ho; discriminate Ho|].
  split; [exact Hrel|].
  exists bgf_v0. split; [| split].
  - unfold bl_cinv, bl_loc, bl_begin, bgf_v0; simpl.
    assert (Hsl: 0 <= starting_len (dp_fmt (dc_par st) =? 1) < 2 ^ 32)
      by (unfold starting_len, ZSTD_FRAMEHEADERSIZE_PREFIX; destruct (_ =? 1); lia).
    split; [unfold vlong; exact He|]. split; [exact Hsl|]. split; [exact Hs|]. split; [exact Hi|].
    split; [exact Hc|]. split; [exact Hid|].
    split; [exists 0; split; [unfold vlong; exact Hp | rep_lia]|].
    split; [exists 0; split; [unfold vlong; exact Hd | rep_lia]|].
    split; [exact Hhb|]. split; [exact Hwf|]. split; [right; reflexivity|].
    left. repeat split; auto.
  - intros b Hb. unfold bl_loc, bl_begin in Hb; simpl in Hb.
    destruct (dictref_model odr) as [dm|] eqn:E; inversion Hb; subst; clear Hb.
    unfold bl_init, bgf_v0; simpl. repeat split; auto. constructor.
  - exact Hmo.
Qed.

(* ---------- base_rel3 after a Begin ---------- *)

Lemma base_rel3_fp_ok (st: dctx_st) (k: cst3) : base_rel3 st k -> fp_ok (fs_fParams (c3_fs k)).
Proof. intros (_ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma base_rel3_begin (st: dctx_st) (k: cst3) (fs: fstate) (t: tabs3) (ob: option Spec_api6.blabs) (x: bool) :
  base_rel3 st k -> dc_ss st = ss_init ->
  (ob <> None -> fs_isFrameDecompression fs = Vint (Int.repr 1)) ->
  fp_ok (fs_fParams fs) ->
  base_rel3 (set_ex (set_bl st ob) x) (c3_with_fs k fs t).
Proof.
  intros [H1 [H2 [H3 [H4 [H5 [_ [H6 [H7 Hm]]]]]]]] Hss Hi Hfp.
  unfold base_rel3, set_ex, set_bl, c3_with_fs; simpl.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  split; [exact H4|]. split; [exact H5|]. split; [exact Hfp|]. split; [exact H6|].
  split; [intros Hn; split; [exact Hss | exact (Hi Hn)] | exact Hm].
Qed.

(* ---------- the context: what B's Begin specs take, and the rest ---------- *)

Definition bgf_rest (DENT: dent_pred) (gv: globals) (p: val) (k: cst3) : mpred :=
  field_at Ews t_dctx (DOT _forceIgnoreChecksum) (Vint (Int.repr (dp_ignore (c3_par k)))) p *
  field_at Ews t_dctx (DOT _maxBlockSizeParam) (Vint (Int.repr (dp_bmax (c3_par k)))) p *
  field_at Ews t_dctx (DOT _refMultipleDDicts) (Vint (Int.repr (dp_multi (c3_par k)))) p *
  field_at Ews t_dctx (DOT _ddictSet) (c3_sp k) p *
  cgroup3 p (c3_stable k) (dp_wmax (c3_par k)) *
  dgroup DENT gv p (c3_dict k) * sgroup p (c3_s k) *
  hset_rep (sf_mem (c3_s k)) (c3_sp k) (c3_set k) (sf_held (c3_s k) - local_held (c3_dict k)) *
  dctx_token p * dctx_pad p.

Lemma ctx_rep3_split (DENT: dent_pred) (TABS: tabs_pred) gv p k :
  ctx_rep3 DENT TABS gv p k =
  !! (cold01 (c3_fs k) /\ par_ok (c3_par k)) &&
  (cfg_fmt p (dp_fmt (c3_par k)) * cfg_lit p * frame_fields p (c3_fs k) * tabs_rep TABS gv p (c3_tabs k) *
   bgf_rest DENT gv p k).
Proof.
  unfold ctx_rep3, ctx_body3, fgroup3, bgf_rest.
  apply pred_ext; Intros; entailer!.
Qed.

Lemma bgf_rest_with_fs DENT gv p k fs t : bgf_rest DENT gv p (c3_with_fs k fs t) = bgf_rest DENT gv p k.
Proof. reflexivity. Qed.

Lemma bgf_rest_hb DENT gv p k : bgf_rest DENT gv p k |-- !! (Zlength (sf_hbuf (c3_s k)) = 18).
Proof. unfold bgf_rest, sgroup. entailer!. Qed.

(* the tables in any state are uninitialised tables, litExtraBuffer holding some bytes *)
Lemma tabs_rep_uninit (TABS: tabs_pred) :
  TABS_OK TABS -> forall gv p t, tabs_rep TABS gv p t |-- EX lxb: list Z, tables_uninit p lxb.
Proof.
  intros HT gv p [lxb | ox ts]; simpl.
  - Exists lxb. apply derives_refl.
  - Exists (ts_lxb ts). apply HT.
Qed.

Lemma tabs_rep_none (TABS: tabs_pred) gv p lxb : tables_uninit p lxb |-- tabs_rep TABS gv p (TUninit lxb).
Proof. apply derives_refl. Qed.

(* folding the context back after a Begin (which clears dc_ex) *)
Lemma DC3_begin (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) gv p (st: dctx_st) (k: cst3) (fs: fstate) (t: tabs3)
    (ob: option Spec_api6.blabs) :
  base_rel3 st k -> dc_ss st = ss_init -> cold01 fs -> par_ok (c3_par k) ->
  (ob <> None -> fs_isFrameDecompression fs = Vint (Int.repr 1)) ->
  (forall ba, ob = Some ba -> BR (c3_par k) ba fs t (sf_hbuf (c3_s k))) ->
  fp_ok (fs_fParams fs) ->
  cfg_fmt p (dp_fmt (c3_par k)) * cfg_lit p * frame_fields p fs * tabs_rep TABS gv p t * bgf_rest DENT gv p k
  |-- DC3x DENT TABS SR BR gv p (set_ex (set_bl st ob) false).
Proof.
  intros Hb Hss Hc Hpar Hi HBR Hfp.
  unfold DC3x, DC3_of. Exists (c3_with_fs k fs t).
  rewrite ctx_rep3_split. simpl. rewrite bgf_rest_with_fs.
  apply andp_right; [| apply andp_right; [apply prop_right; split; auto | cancel]].
  apply prop_right. split; [apply base_rel3_begin; auto|]. split; [| split].
  - unfold set_ex, set_bl; simpl. intros Hn; contradiction.
  - unfold set_ex, set_bl; simpl. intros ba Hba. apply HBR; auto.
  - apply ex_on3_noex. reflexivity.
Qed.

End CM_BeginFacts_1.
