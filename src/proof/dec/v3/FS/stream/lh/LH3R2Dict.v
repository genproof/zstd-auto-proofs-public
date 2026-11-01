(* FS3 streaming, case zdss_loadHeader (on the stream relation's revision R2): err_why of ZSTD_decodeFrameHeader's
   dictionary_wrong: the model's dictionary of the frame is the DDict zstd began it with (getDDict's). *)
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3Stmts.
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3R2Lib Zstd.proof.dec.v3.FS.stream.lh.LH3RetGfh Zstd.proof.dec.v3.FS.stream.lh.LH3R2Why Zstd.proof.dec.v3.FS.stream.lh.LH3R2Short.
Local Open Scope logic.

Section CM_LH3R2Dict_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma rd_auto_id : forall b dm, dict_auto b = Some dm -> dm_id dm = dict_id_of b.
Proof.
  intros b dm H. unfold dict_auto, dict_id_of in *.
  destruct (Zlength b <? 8); [ injection H as <-; reflexivity | ].
  destruct (negb (le_field b 0 4 =? ZSTD_MAGIC_DICTIONARY)); [ injection H as <-; reflexivity | ].
  destruct (load_dentropy b) as [[st es]|]; [ injection H as <-; reflexivity | discriminate ].
Qed.

Lemma rd_getdd_m1 : forall d, df_uses d = -1 -> getddict_res d = (df_ddict d, d).
Proof. intros d H. unfold getddict_res. rewrite H. reflexivity. Qed.

Lemma rd_nodup_in : forall (l: list (val * ddict_st)) q d1 d2, NoDup (map fst l) -> In (q, d1) l -> In (q, d2) l -> d1 = d2.
Proof.
  induction l as [ | [q0 e0] l IH ]; intros q d1 d2 Hn H1 H2; [ contradiction | ].
  cbn [map fst] in Hn. inversion Hn as [ | ? ? Hni Hnd ]; subst.
  destruct H1 as [E1 | H1]; destruct H2 as [E2 | H2].
  - congruence.
  - injection E1 as -> ->. exfalso. apply Hni. change q with (fst (q, d2)). apply in_map. exact H2.
  - injection E2 as -> ->. exfalso. apply Hni. change q with (fst (q, d1)). apply in_map. exact H1.
  - eapply IH; eauto.
Qed.

(* a caller's DDict q of the set (dd') is the one dd_caller describes *)
Lemma rd_caller_bytes : forall st q dd' dd'', NoDup (map fst (dc_set st)) -> set_cur_ok st ->
  In (q, dd') (dc_set st) -> dd_caller st q dd'' -> dd_bytes dd'' = dd_bytes dd'.
Proof.
  intros st q dd' dd'' Hn Hs Hin [Hin2 | (dr & Ed & Esrc)].
  - rewrite (rd_nodup_in _ _ _ _ Hn Hin2 Hin). reflexivity.
  - rewrite (Hs dr q dd'' dd' Ed Esrc Hin). reflexivity.
Qed.

(* the context's dictionary is one zstd selects with (Spec_api6.st_sel v3.4): a DDict, or one with bytes *)
Definition dr_sel (st: dctx_st) : Prop :=
  exists dr, dc_dict st = Some dr /\
    match dr_src dr with DSDDict _ _ => True | _ => negb (Nat.eqb (length (dr_bytes dr)) 0) = true end.

Lemma rd_ddict_of_get : forall d, df_ddict (snd (getddict_res d)) <> nullval -> df_ddict d <> nullval.
Proof.
  intros d H. unfold getddict_res in H.
  destruct (df_uses d =? 0); [ cbn in H; contradiction | ].
  destruct (df_uses d =? 1); exact H.
Qed.

Lemma rl_dm_did : hs_probe_ok -> forall a w hb h tbl d1 did1 dd dm, dd_bytes_ok (a_st a) ->
  base_call (a_st a) (w_k w) -> not_ref (dc_dict (a_st a)) -> bytes_ok hb ->
  get_frame_header_m (lh_mg (w_k w)) hb = FH_ok h ->
  lhA_sel (w_k w) hb 0 (fh_val h) tbl d1 did1 ->
  (dc_set (a_st a) <> nil -> dr_sel (a_st a) -> dp_multi (dc_par (a_st a)) = 1 ->
     set_clean (dc_set (a_st a)) = true -> df_ddict (c3_dict (w_k w)) <> nullval) ->
  (forall dd0, df_local (snd (getddict_res d1)) <> nullval -> cur_ddict (dc_dict (a_st a)) = None ->
     ~ In (df_local (snd (getddict_res d1)), dd0) (dc_set (a_st a))) ->
  (dc_set (a_st a) <> nil -> dr_sel (a_st a) /\ dp_multi (dc_par (a_st a)) = 1 /\
     set_clean (dc_set (a_st a)) = true) ->
  lh_fdm0 a (k_A (w_k w) (fh_val h) d1 did1) hb dm ->
  lhC_dd a (k_A (w_k w) (fh_val h) d1 did1) dd ->
  dm_id dm = lh_dd_did dd.
Proof.
  intros Hpr a w hb h tbl d1 did1 dd dm Hbytes Hb Hnr Hbh Hh Hsel HNN Hdisj Hon Hfdm Hdd.
  pose proof (rl_dict_rel Hpr _ _ _ _ _ _ _ _ Hb Hsel) as Hdr1.
  destruct Hb as (Hstab & Hpar & Hset & Hdr & Hsco).
  assert (Hk1: c3_dict (k_A (w_k w) (fh_val h) d1 did1) = d1) by reflexivity.
  unfold lhC_dd, lh_dd_ok, dd_src in Hdd. change (c3_dict (k_A (w_k w) (fh_val h) d1 did1)) with d1 in Hdd.
  cbn [c3_dict c3_with_dict] in Hdd.
  unfold lh_fdm0 in Hfdm.
  destruct Hfdm as [(Hnil & Hdm) | (Hne & Hso & _ & _ & h' & q & dd' & Hh' & Hq & Hin & Hauto)].
  - (* no set: the context's dictionary *)
    destruct Hdr1 as [Hdr1 | [Hne _]]; [ | contradiction ].
    destruct (dc_dict (a_st a)) as [dr|] eqn:Ed.
    + specialize (Hnr dr eq_refl). unfold dict_rel3_of in Hdr1. unfold dictref_model in Hdm.
      destruct (dr_src dr) as [ pk | | q pref ] eqn:Es; [ contradiction | | ].
      * (* own copy *)
        destruct Hdr1 as (_ & Hd1).
        destruct (Zlength (dr_bytes dr) =? 0) eqn:Ez.
        -- subst d1. destruct dd as [[x buf]|].
           ++ destruct Hdd as (Hq & Hqn & _). exfalso. apply Hqn. rewrite Hq. reflexivity.
           ++ destruct (dr_raw dr); [ injection Hdm as <-; reflexivity | ].
              apply Z.eqb_eq in Ez. unfold dict_auto in Hdm. rewrite Ez in Hdm. cbn in Hdm.
              injection Hdm as <-. reflexivity.
        -- destruct Hd1 as (buf0 & ld & am0 & Hloc & Hdl & Hu & Hlx).
           rewrite (rd_getdd_m1 _ Hu) in Hdd. cbn [fst snd] in Hdd.
           destruct dd as [[x buf]|].
           ++ destruct Hdd as (Hq & Hqn & Hsrc & _).
              destruct Hsrc as [(Hl & _ & _ & Hlx') | (dd'' & Hc & Hx & _)].
              ** cbn [c3_dict c3_with_dict] in Hl, Hlx'. rewrite Hlx in Hlx'. injection Hlx' as <- _.
                 cbn. destruct (dr_raw dr); [ injection Hdm as <-; reflexivity | ].
                 rewrite (rd_auto_id _ _ Hdm). reflexivity.
              ** destruct Hc as [Hin | (dr' & Ed' & Es')]; [ rewrite Hnil in Hin; contradiction | ].
                 rewrite Ed in Ed'. injection Ed' as <-. rewrite Es in Es'. discriminate.
           ++ exfalso. unfold isptr in Hloc. rewrite <- Hdl in Hloc. rewrite Hdd in Hloc. exact Hloc.
      * (* a caller's DDict *)
        destruct Hdr1 as (Hraw & _ & Hqp & Hl & Hdq & Hu & _). rewrite Hraw in Hdm.
        rewrite (rd_getdd_m1 _ Hu) in Hdd. cbn [fst snd] in Hdd.
        destruct dd as [[x buf]|].
        -- destruct Hdd as (Hq & Hqn & Hsrc & _).
           destruct Hsrc as [(Hl' & _) | (dd'' & Hc & Hx & _)].
           ++ exfalso. cbn [c3_dict c3_with_dict] in Hl'. apply Hqn. rewrite <- Hl', Hl. reflexivity.
           ++ destruct Hc as [Hin | (dr' & Ed' & Es')]; [ rewrite Hnil in Hin; contradiction | ].
              rewrite Ed in Ed'. injection Ed' as <-. rewrite Es in Es'. injection Es' as _ Epref. subst pref.
              rewrite Hx. cbn. rewrite <- (Hbytes Hnil dr q dd'' Ed Es).
              apply rd_auto_id; auto.
        -- exfalso. rewrite Hdq in Hdd. subst q. exact Hqp.
    + (* no dictionary *)
      cbn in Hdm. injection Hdm as <-. unfold dict_rel3_of in Hdr1. destruct Hdr1 as [Hu0 _].
      unfold getddict_res in Hdd. rewrite Hu0 in Hdd. cbn in Hdd.
      destruct dd as [[x buf]|]; [ | reflexivity ].
      destruct Hdd as (Hq & Hqn & _). exfalso. apply Hqn. exact Hq.
  - (* the set *)
    specialize (Hon Hne).
    assert (Hmg1: lh_mg (k_A (w_k w) (fh_val h) d1 did1) = lh_mg (w_k w)) by reflexivity.
    rewrite Hmg1, Hh in Hh'. injection Hh' as <-.
    destruct Hon as (Hdsome & Hmulti & Hclean).
    assert (Hdn: df_ddict (c3_dict (w_k w)) <> nullval) by (apply HNN; auto).
    destruct Hsel as (_ & _ & id & Hid & Hsb). specialize (Hid Hso).
    unfold sel_by in Hsb.
    change (sel_on (c3_par (k_A (w_k w) (fh_val h) d1 did1)) (c3_sp (k_A (w_k w) (fh_val h) d1 did1)))
      with (sel_on (c3_par (w_k w)) (c3_sp (w_k w))) in Hso.
    rewrite Hso in Hsb. destruct Hsb as (Hinv & Hidr & Hd1 & _).
    destruct (rl_gfh3 _ _ _ Hh Hbh) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hidh & _).
    assert (Hide: id = fh_dictID h).
    { change (fp_dictID (fh_val h)) with (Vint (Int.repr (fh_dictID h))) in Hid. apply Vint_inj in Hid.
      apply (f_equal Int.unsigned) in Hid. rewrite !Int.unsigned_repr in Hid by lia. lia. }
    subst id.
    pose proof (rs_clean_ids _ Hclean) as Hnz.
    assert (Hnd: NoDup (map fst (dc_set (a_st a)))) by (destruct Hinv as (_ & _ & _ & Hnd & _); rewrite <- Hset; exact Hnd).
    assert (Hr: sel_r (c3_dict (w_k w)) (c3_set (w_k w)) tbl (fh_dictID h) = set_find (dc_set (a_st a)) (fh_dictID h)).
    { unfold sel_r. destruct (eq_dec (df_ddict (c3_dict (w_k w))) nullval); [ contradiction | ].
      destruct (Hpr _ _ _ Hinv Hidr) as [_ Hf']. rewrite Hf'; [ rewrite Hset; reflexivity | rewrite Hset; auto ]. }
    rewrite Hr in Hd1. unfold sel_dict in Hd1.
    destruct (eq_dec (set_find (dc_set (a_st a)) (fh_dictID h)) nullval) as [Hf0 | Hf0].
    + (* nothing selected: the current DDict *)
      subst d1 q.
      assert (Hu: df_uses (c3_dict (w_k w)) = -1).
      { destruct Hdr as [Hdr | (_ & (_ & Hu & _))]; [ | exact Hu ].
        destruct Hdsome as [dr [Ed _]]. rewrite Ed in Hdr.
        specialize (Hnr dr Ed). unfold dict_rel3_of in Hdr.
        destruct (dr_src dr); [ contradiction | | tauto ].
        destruct (Zlength (dr_bytes dr) =? 0).
        - destruct Hdr as (_ & Hd). rewrite Hd in Hdn. contradiction.
        - destruct Hdr as (_ & _ & _ & _ & _ & _ & Hu & _). exact Hu. }
      rewrite (rd_getdd_m1 _ Hu) in Hdd, Hdisj. cbn [fst snd] in Hdd, Hdisj.
      destruct dd as [[x buf]|]; [ | contradiction ].
      destruct Hdd as (Hq & Hqn & Hsrc & _).
      destruct Hsrc as [(Hl & _ & _ & Hlx) | (dd'' & Hc & Hx & _)].
      * exfalso. cbn [c3_dict c3_with_dict] in Hl.
        assert (Hcur: cur_ddict (dc_dict (a_st a)) = None).
        { destruct Hdr as [Hdr | (_ & (Hl0 & _))].
          - destruct (dc_dict (a_st a)) as [dr|] eqn:Ed; [ | reflexivity ].
            unfold cur_ddict. specialize (Hnr dr eq_refl). unfold dict_rel3_of in Hdr.
            destruct (dr_src dr); [ contradiction | reflexivity | ].
            exfalso. destruct Hdr as (_ & _ & _ & Hl0 & _). apply Hqn. rewrite <- Hl, Hl0. reflexivity.
          - exfalso. apply Hqn. rewrite <- Hl, Hl0. reflexivity. }
        apply (Hdisj dd'); [ rewrite Hl; exact Hqn | exact Hcur | ]. rewrite Hl, Hq. exact Hin.
      * rewrite Hx. cbn. rewrite (rd_caller_bytes (a_st a) (dx_q x) dd' dd'' Hnd (proj1 Hsco)); [ | | exact Hc ].
        -- apply rd_auto_id; auto.
        -- rewrite Hq. exact Hin.
    + (* the frame's DDict selected *)
      subst d1. destruct (eq_dec (set_find (dc_set (a_st a)) (fh_dictID h)) nullval) in Hq; [ contradiction | ].
      subst q.
      rewrite (rd_getdd_m1 (switch_fields _) eq_refl) in Hdd. cbn [fst snd df_ddict switch_fields] in Hdd.
      destruct dd as [[x buf]|]; [ | contradiction ].
      destruct Hdd as (Hq & Hqn & Hsrc & _).
      destruct Hsrc as [(Hl & _) | (dd'' & Hc & Hx & _)].
      * exfalso. cbn [c3_dict c3_with_dict switch_fields df_local] in Hl. apply Hqn. rewrite <- Hl. reflexivity.
      * rewrite Hx. cbn. rewrite (rd_caller_bytes (a_st a) (dx_q x) dd' dd'' Hnd (proj1 Hsco)); [ | | exact Hc ].
        -- apply rd_auto_id; auto.
        -- rewrite Hq. exact Hin.
Qed.

Lemma rl_sel_on : forall a w hb dsin recs cd mg x dm hx, lh_split_ok a w hb dsin recs cd ->
  get_frame_header_m mg x = FH_ok hx -> frame_dict mg (fst (st_sel (a_st a))) cd x = Some dm -> dc_set (a_st a) <> nil ->
  dr_sel (a_st a) /\ dp_multi (dc_par (a_st a)) = 1 /\ set_clean (dc_set (a_st a)) = true.
Proof.
  intros a w hb dsin recs cd mg x dm hx Hsp Hx Fd Hne.
  pose proof (rl_cd_none _ _ _ _ _ _ Hsp) as Hcd0.
  unfold st_sel in Fd, Hcd0. destruct (dc_set (a_st a)) as [ | e0 l0 ]; [ exfalso; apply Hne; reflexivity | ].
  destruct (dc_dict (a_st a)) as [dr|] eqn:Edd.
  - match type of Fd with context [if ?b then _ else _] => destruct b eqn:Em end.
    + apply andb_prop in Em. destruct Em as [Em Edr]. apply andb_prop in Em. destruct Em as [Em Ec].
      apply Z.eqb_eq in Em. split; [ | auto ]. exists dr. split; [ exact Edd | ]. destruct (dr_src dr); auto.
    + rewrite (Hcd0 eq_refl) in Fd. cbn [fst] in Fd. rewrite (rs_frame_dict_none _ _ _ _ Hx) in Fd. discriminate.
  - rewrite (Hcd0 eq_refl) in Fd. cbn [fst] in Fd. rewrite (rs_frame_dict_none _ _ _ _ Hx) in Fd. discriminate.
Qed.

Lemma why_dict : MF3 -> hs_probe_ok -> forall a w hb h tbl d1 did1 dd r, dd_bytes_ok (a_st a) ->
  lh_ctx a w hb -> par_ok (dc_par (a_st a)) -> (dc_set (a_st a) <> nil -> c3_sp (w_k w) <> nullval) ->
  (dc_set (a_st a) <> nil -> dr_sel (a_st a) -> dp_multi (dc_par (a_st a)) = 1 ->
     set_clean (dc_set (a_st a)) = true -> df_ddict (c3_dict (w_k w)) <> nullval) ->
  (forall dd0, df_local (snd (getddict_res d1)) <> nullval -> cur_ddict (dc_dict (a_st a)) = None ->
     ~ In (df_local (snd (getddict_res d1)), dd0) (dc_set (a_st a))) ->
  lhA_sel (w_k w) hb 0 (fh_val h) tbl d1 did1 -> get_frame_header_m (lh_mg (w_k w)) hb = FH_ok h ->
  fh_frameType h <> 1 -> dec_err r -> lhC_dd a (k_A (w_k w) (fh_val h) d1 did1) dd ->
  fh_dictID h <> 0 -> fh_dictID h <> lh_dd_did dd -> err_why a r.
Proof.
  intros HMF Hpr a w hb h tbl d1 did1 dd r Hbytes Hc Hp Hsp HNN Hdisj Hsel Hh Ht Hd Hdd Hid0 Hid.
  apply why_fails; auto.
  destruct (rl_entry a w hb Hc) as (Hb & Hbh & Hok & Ha).
  destruct (rl_split a w hb Hc (rl_wmax _ Hp)) as [F | (dsin & recs & cd & Hsp')]; [ exact F | ].
  destruct (rl_gfh3 _ _ _ Hh Hbh) as (_ & _ & _ & _ & _ & _ & Hft01 & _).
  assert (Ht0: fh_frameType h = 0) by lia.
  assert (Hsz: fh_headerSize h = Zlength hb) by (unfold hdr_lenok in Hok; rewrite Hh in Hok; auto).
  assert (Hmg: sm_mg (sm_of (a_st a)) = lh_mg (w_k w)) by apply (rl_mg _ _ Hb).
  apply (rl_fails_fdead HMF a w hb dsin recs cd nil (rl_wmax _ Hp) Hsp' (prefix_nil _)).
  rewrite app_nil_r.
  assert (Hh' := Hh). rewrite <- Hmg in Hh'.
  destruct (mf_hdr_zstd HMF (sm_of (a_st a)) cd hb h Hbh Hh' Ht0 (eq_sym Hsz)) as (Hn & Hm & _).
  rewrite Hmg in Hn, Hm. cbn [sm_of sm_sel] in Hn, Hm.
  destruct (frame_dict (lh_mg (w_k w)) (fst (st_sel (a_st a))) cd hb) as [dm|] eqn:Fd; [ | apply Hn; reflexivity ].
  apply (Hm dm eq_refl Hid0).
  pose proof (rl_fdm0 Hpr a w hb h tbl d1 did1 cd hb dm Hb Hsp Hbh Hh Hsel (proj2 (proj2 (proj2 (proj2 (proj2 Hsp')))))
                (rl_cd_none _ _ _ _ _ _ Hsp') Hh Fd) as Hfdm.
  rewrite (rl_dm_did Hpr a w hb h tbl d1 did1 dd dm Hbytes Hb (rl_not_ref a Ha) Hbh Hh Hsel HNN Hdisj
             (rl_sel_on _ _ _ _ _ _ _ _ _ _ Hsp' Hh Fd) Hfdm Hdd).
  intro E. apply Hid. auto.
Qed.

(* a context selecting from its set has a DDict *)
Lemma rl_hnn : forall a w hb h tbl d1 did1,
  base_call (a_st a) (w_k w) -> lhA_sel (w_k w) hb 0 (fh_val h) tbl d1 did1 ->
  (dc_set (a_st a) <> nil -> c3_sp (w_k w) <> nullval) ->
  dc_set (a_st a) <> nil -> dr_sel (a_st a) -> dp_multi (dc_par (a_st a)) = 1 ->
  set_clean (dc_set (a_st a)) = true -> df_ddict (c3_dict (w_k w)) <> nullval.
Proof.
  intros a w hb h tbl d1 did1 Hb Hsel Hsp Hne Hdr Hm Hcl.
  destruct Hb as (_ & Hpar & Hset & Hrel & _).
  assert (Hso: sel_on (c3_par (w_k w)) (c3_sp (w_k w)) = true).
  { unfold sel_on. rewrite Hpar, Hm. cbn.
    assert (c3_sp (w_k w) <> nullval) by (apply Hsp; exact Hne).
    unfold veqb. destruct (Val.eq (c3_sp (w_k w)) _) as [E|E]; [ exfalso; apply H; exact E | reflexivity ]. }
  destruct Hsel as (_ & _ & id & _ & Hsb). unfold sel_by in Hsb. rewrite Hso in Hsb. destruct Hsb as (Hinv & _).
  apply rd_ddict_of_get. apply (rs_getdd_nn (a_st a) _ Hrel); [ | exact Hdr ].
  intros q Hq. apply in_map_iff in Hq. destruct Hq as [e [<- He]].
  destruct Hinv as (_ & _ & _ & _ & _ & Hptr & _). rewrite Forall_forall in Hptr. rewrite <- Hset in He.
  exact (Hptr e He).
Qed.

End CM_LH3R2Dict_1.
