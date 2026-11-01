(* FS3-bl stages 3/4, compressed block: from the block decoder's post to s34_mid_ok. *)
Require Export Zstd.proof.dec.v3.FS.BL.body.s34.comp.CompHist.
Local Open Scope Z_scope.

Section CM_CompPost_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma comp_zbytes_inj (a b: list Z) : bytes_ok a -> bytes_ok b -> zbytes a = zbytes b -> a = b.
Proof.
  revert b. induction a as [ | x a IH]; intros [ | y b] Ha Hb E; simpl in E; try discriminate; auto.
  assert (Hx: Vint (Int.repr x) = Vint (Int.repr y)) by congruence.
  assert (Ht: zbytes a = zbytes b) by congruence.
  inv Ha. inv Hb. f_equal; [| apply IH; auto].
  unfold is_byte in *.
  apply (f_equal (fun v => match v with Vint i => Int.unsigned i | _ => 0 end)) in Hx. simpl in Hx.
  rewrite !Int.unsigned_repr in Hx by rep_lia. auto.
Qed.

Lemma comp_hist_bytes od ba : bd_wf od -> bd_model_ok (ba_dict ba) od -> bytes_ok (comp_hist ba).
Proof.
  intros Hwf Hm. unfold comp_hist. destruct (dictref_model (ba_dict ba)) as [dm |] eqn:E; [| constructor].
  apply (comp_hist_suffix od _ Hwf Hm dm E).
Qed.

Lemma comp_out_bytes ba : (forall b, ba_st ba = Some b -> bytes_ok (bs_out b)) -> bytes_ok (comp_out ba).
Proof. intros H. unfold comp_out. destruct (ba_st ba) as [b |]; [apply H; auto | constructor]. Qed.

Lemma comp_ext_clean shk od d cap : ext_clean d cap (comp_ext shk od).
Proof. destruct od as [d'|]; [unfold comp_ext; destruct (eq_dec (bd_eb d') nullval) |]; exact I. Qed.

Lemma comp_ext_clear shk od d ps cap bsm h o ws : ext_clear d ps cap bsm (comp_ext shk od) h o ws.
Proof. destruct od as [d'|]; [unfold comp_ext; destruct (eq_dec (bd_eb d') nullval) |]; exact I. Qed.

Lemma comp_cold01 fs1 cold : cold01 fs1 -> (cold = fs_ddictIsCold fs1 \/ cold = Vint (Int.repr 0)) ->
  cold = Vint (Int.repr 0) \/ cold = Vint (Int.repr 1).
Proof. intros [H | H] [-> | ->]; auto. Qed.

(* the model's block under s34_fol *)
Lemma comp_fol md ba fs ts v c b dm :
  bl_mrel md ba fs ts v -> (bv_stage v = BBlk \/ bv_stage v = BLastBlk) -> bv_bt v = 2 -> s34_fol ba c b dm ->
  comp_hist ba = dm_content dm /\ comp_out ba = bs_out b /\
  blk_model dm b c = decode_block ts (comp_hist ba) (comp_out ba) c (fh_blockSizeMax (bv_h v)) (fh_windowSize (bv_h v)).
Proof.
  intros Hm Hst Hbt (Hb & Hdm & _).
  destruct (comp_mrel md ba fs ts v b Hm Hst Hb) as (Hds & Hh & Ht).
  assert (E1: comp_hist ba = dm_content dm) by (unfold comp_hist; rewrite Hdm; reflexivity).
  assert (E2: comp_out ba = bs_out b) by (unfold comp_out; rewrite Hb; reflexivity).
  rewrite E1, E2. split; [auto |]. split; [auto |]. apply comp_blk_model; congruence.
Qed.

Lemma comp_prefix (oc oc': list val) opos cap :
  0 <= opos <= Zlength oc -> Zlength oc' = Zlength oc -> unchanged_outside oc oc' opos (opos + cap) ->
  sublist 0 opos oc' = sublist 0 opos oc.
Proof.
  intros Hl Hl' Hu. apply Znth_eq_ext; [rewrite !Zlength_sublist by lia; lia |].
  intros i Hi. rewrite Zlength_sublist in Hi by lia. rewrite !Znth_sublist by lia.
  rewrite Z.add_0_r. apply Hu; lia.
Qed.

(* cap > 0: the whole output array *)
(* the tables after the block call: TInit with the new state, or (an error) uninitialised holding the bytes lxb *)
Definition comp_t (ox: option ddx) (ts': option tstate) (lxb: list Z) : tabs3 :=
  match ts' with Some ts2 => TInit ox ts2 | None => TUninit lxb end.

Lemma comp_pos_post md od ba fs ts v ob osz opos oc c r oc' cold (ts': option tstate) lxb fs1 shk (SX: Prop) :
  bl_hist_ok ba ob opos oc -> Zlength oc = osz -> 0 <= opos -> opos < osz ->
  bd_wf od -> bd_model_ok (ba_dict ba) od -> bl_mrel md ba fs ts v ->
  (bv_stage v = BBlk \/ bv_stage v = BLastBlk) -> bv_bt v = 2 -> cold01 fs1 ->
  (forall b, ba_st ba = Some b -> bytes_ok (bs_out b)) ->
  0 <= r <= Int64.max_unsigned -> Zlength oc' = osz ->
  unchanged_outside oc oc' opos (opos + (osz - opos)) ->
  (is_error_code r = false ->
     r <= osz - opos /\ cold = Vint (Int.repr 0) /\ ts' <> None /\ SX /\
     (hist_def oc opos (bl_start ba opos) (comp_ext shk od) ->
      (ext_clean opos (osz - opos) (comp_ext shk od) \/
       (r <= fh_blockSizeMax (bv_h v) /\ ext_far opos (osz - opos) (fh_blockSizeMax (bv_h v)) (comp_ext shk od))) ->
      exists cnt, sublist opos (opos + r) oc' = zbytes cnt /\ bytes_ok cnt)) ->
  (is_error_code r = true -> ts' = None /\ dec_err r) ->
  (cold = fs_ddictIsCold fs1 \/ cold = Vint (Int.repr 0)) ->
  (osz - opos = 0 \/
   (hist_view oc opos (bl_start ba opos) (comp_ext shk od) (comp_hist ba) (comp_out ba) (fh_windowSize (bv_h v)) /\
    ext_clear opos (bl_start ba opos) (osz - opos) (fh_blockSizeMax (bv_h v)) (comp_ext shk od) (comp_hist ba)
      (comp_out ba) (fh_windowSize (bv_h v))) ->
   bytes_ok (comp_hist ba) -> bytes_ok (comp_out ba) ->
   block_ok ts (comp_hist ba) (comp_out ba) c (fh_blockSizeMax (bv_h v)) (fh_windowSize (bv_h v)) 1 oc oc'
     opos (osz - opos) r (option_map ts_d ts')) ->
  s34_mid_ok od ba v osz opos oc c r oc' 0 cold (comp_t (bd_oxo od) ts' lxb).
Proof.
  intros Hh Lo Hp0 Hpc Hwf Hm Hmr Hst Hbt Hc1 HD Hr Lo' Hun Hok Herr Hcold Hbk.
  assert (Hbk': forall b dm, s34_fol ba c b dm ->
            block_ok ts (comp_hist ba) (comp_out ba) c (fh_blockSizeMax (bv_h v)) (fh_windowSize (bv_h v)) 1 oc oc'
              opos (osz - opos) r (option_map ts_d ts')).
  { intros b dm (Hb & Hdm & Hl). apply Hbk.
    - right. split; [| apply comp_ext_clear].
      unfold comp_hist, comp_out. rewrite Hb, Hdm. apply (comp_hist_view shk od ba ob); auto; lia.
    - apply (comp_hist_bytes od); auto.
    - apply comp_out_bytes; auto. }
  clear Hbk.
  split; [exact Hr |]. split; [exact Lo' |]. split; [apply (comp_prefix oc oc' opos (osz - opos)); auto; lia |].
  split; [apply (comp_cold01 fs1); auto |].
  split.
  - intros Er b dm Hf. destruct (comp_fol md ba fs ts v c b dm Hmr Hst Hbt Hf) as (_ & _ & Eb).
    specialize (Hbk' b dm Hf). unfold block_ok in Hbk'. rewrite Eb.
    destruct (decode_block _ _ _ _ _ _) as [[ts3 cnt3] |]; auto.
    destruct Hbk' as [(Er2 & _) | (_ & Hlt)]; [congruence | exact Hlt].
  - intros Er. destruct (Hok Er) as (Hrc & Hcd & Hts & _ & Hcnt).
    destruct (Hcnt (comp_hist_def shk od ba ob opos oc Hh ltac:(lia) Hwf HD) (or_introl (comp_ext_clean _ _ _ _)))
      as (cnt & Hsub & Bc).
    assert (Lc: Zlength cnt = r).
    { apply (f_equal (@Zlength val)) in Hsub. rewrite Zlength_sublist, Zlength_map in Hsub by lia. lia. }
    split; [exact Hrc |]. split; [rewrite Hbt; reflexivity |]. split; [intros E; rewrite Hbt in E; discriminate |].
    destruct ts' as [ts2 |]; [| contradiction].
    exists cnt, ts2. split; [exact Hsub |]. split; [exact Bc |]. split; [exact Lc |]. split; [reflexivity |].
    intros b dm x Hf Hx. destruct (comp_fol md ba fs ts v c b dm Hmr Hst Hbt Hf) as (_ & _ & Eb).
    specialize (Hbk' b dm Hf). unfold block_ok in Hbk'. rewrite Eb in Hx. rewrite Hx in Hbk'. destruct x as [ts3 cnt3].
    destruct Hbk' as [(_ & Lr & Hsub3 & Bc3 & Ets & _) | ((Er2 & _) & _)]; [| congruence].
    cbn [option_map] in Ets. injection Ets as <-. f_equal. apply comp_zbytes_inj; auto. rewrite <- Hsub, <- Hsub3. reflexivity.
Qed.

(* cap = 0: an empty window, the output array unchanged *)
Lemma comp_zero_post md od ba fs ts v osz opos oc c r ocm cold (ts': option tstate) lxb fs1 cap (SX SY: Prop) (hv: Prop) :
  Zlength oc = osz -> opos = osz -> cap = 0 -> bd_wf od -> bd_model_ok (ba_dict ba) od -> bl_mrel md ba fs ts v ->
  (bv_stage v = BBlk \/ bv_stage v = BLastBlk) -> bv_bt v = 2 -> cold01 fs1 ->
  (forall b, ba_st ba = Some b -> bytes_ok (bs_out b)) ->
  0 <= r <= Int64.max_unsigned ->
  (is_error_code r = false -> r <= cap /\ cold = Vint (Int.repr 0) /\ ts' <> None /\ SX /\ SY) ->
  (is_error_code r = true -> ts' = None /\ dec_err r) ->
  (cold = fs_ddictIsCold fs1 \/ cold = Vint (Int.repr 0)) ->
  (cap = 0 \/ hv -> bytes_ok (comp_hist ba) -> bytes_ok (comp_out ba) ->
   block_ok ts (comp_hist ba) (comp_out ba) c (fh_blockSizeMax (bv_h v)) (fh_windowSize (bv_h v)) 1 nil ocm
     0 cap r (option_map ts_d ts')) ->
  s34_mid_ok od ba v osz opos oc c r oc 0 cold (comp_t (bd_oxo od) ts' lxb).
Proof.
  intros Lo Ep Ec Hwf Hm Hmr Hst Hbt Hc1 HD Hr Hok Herr Hcold Hbk. subst cap.
  specialize (Hbk (or_introl eq_refl) (comp_hist_bytes od ba Hwf Hm) (comp_out_bytes ba HD)).
  unfold block_ok in Hbk.
  split; [exact Hr |]. split; [exact Lo |]. split; [reflexivity |].
  split; [apply (comp_cold01 fs1); auto |].
  split.
  - intros Er b dm Hf. destruct (comp_fol md ba fs ts v c b dm Hmr Hst Hbt Hf) as (_ & _ & Eb). rewrite Eb.
    destruct (decode_block _ _ _ _ _ _) as [[ts3 cnt3] |]; auto.
    destruct Hbk as [(Er2 & _) | (_ & Hlt)]; [congruence | lia].
  - intros Er. destruct (Hok Er) as (Hrc & Hcd & Hts & _).
    assert (Er0: r = 0) by lia. subst r.
    split; [lia |]. split; [rewrite Hbt; reflexivity |]. split; [intros E; rewrite Hbt in E; discriminate |].
    destruct ts' as [ts2 |]; [| contradiction].
    exists nil, ts2. split; [rewrite Z.add_0_r, sublist_nil; reflexivity |]. split; [constructor |].
    split; [reflexivity |]. split; [reflexivity |].
    intros b dm x Hf Hx. destruct (comp_fol md ba fs ts v c b dm Hmr Hst Hbt Hf) as (_ & _ & Eb).
    rewrite Eb in Hx. rewrite Hx in Hbk. destruct x as [ts3 cnt3].
    destruct Hbk as [(_ & Lr & _ & _ & Ets & _) | ((Er2 & _) & _)]; [| congruence].
    cbn [option_map] in Ets. injection Ets as <-. f_equal. destruct cnt3; [reflexivity |].
    rewrite Zlength_cons in Lr. pose proof (Zlength_nonneg cnt3). lia.
Qed.

(* ---------- for the VST script ---------- *)

(* the tables after the block call: its new state, or (an error) uninitialised with some litExtraBuffer bytes *)
Lemma comp_tabs (TABS: tabs_pred) gv p ox (ts': option tstate) :
  match ts' with Some ts2 => TABS gv p ox ts2 | None => EX lxb: list Z, tables_uninit p lxb end |--
  EX lxb: list Z, tabs_rep TABS gv p (comp_t ox ts' lxb).
Proof.
  destruct ts' as [ts2 |]; simpl.
  - Exists (@nil Z). apply derives_refl.
  - Intros lxb. Exists lxb. apply derives_refl.
Qed.

Lemma comp_join p fs1 cold pr :
  par_ok pr ->
  field_at Ews t_dctx (DOT _stage) (fs_stage (fs_set_cold fs1 cold)) p *
  field_at Ews t_dctx (DOT _bType) (fs_bType (fs_set_cold fs1 cold)) p *
  field_at Ews t_dctx (DOT _expected) (Vlong (Int64.repr 0)) p * fc_rest p (fs_set_cold fs1 cold) pr
  |-- fcore3 p (fsu_ddictIsCold (fsu_expected fs1 (vlong 0)) cold) pr nullval.
Proof. intros H. apply (fcore3_join p (fsu_ddictIsCold (fsu_expected fs1 (vlong 0)) cold) pr H). Qed.

Lemma comp_win shs (src: val) c :
  readable_share shs -> Zlength c <= 2 ^ 30 -> bytes_ok c ->
  inwin_ok {| iw_sh := shs; iw_base := src; iw_N := Zlength c; iw_c := zbytes c; iw_off := 0; iw_s := c |}.
Proof.
  intros Hs Hl Hb. pose proof (Zlength_nonneg c). unfold inwin_ok, win_ok; cbn [iw_sh iw_N iw_c iw_off iw_s iw_base].
  split; [exact Hs |]. split; [lia |]. split; [lia |]. split; [lia |]. split; [apply Zlength_map |].
  split; [reflexivity |]. split; [exact Hb |]. rewrite Z.add_0_l, sublist_same; auto. rewrite Zlength_map; reflexivity.
Qed.

End CM_CompPost_1.
