(* FS3 streaming, case zdss_loadHeader (on the stream relation's revision R2): err_why of a failed shortcut
   (ZSTD_decompress_usingDDict on the whole frame): the frame's dictionary in the model is the one zstd used. *)
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3Stmts.
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3R2Lib Zstd.proof.dec.v3.FS.stream.lh.LH3RetGfh Zstd.proof.dec.v3.FS.stream.lh.LH3R2Why.
Require Zstd.proof.dec.v3.FS.stream.lh.LH3RetG.
Require Zstd.proof.dec.FS.StreamModelFacts.
Local Open Scope logic.

Section CM_LH3R2Short_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* copies of LH3G1's helpers *)
Lemma rs_dec_nohdr : forall md d wl s, (forall h, get_frame_header_m (md_magicless md) s <> FH_ok h) ->
  forall out k, decode_frame_m md d wl s <> FOk out k.
Proof.
intros md d wl s H out k. unfold decode_frame_m. cbv zeta.
destruct (get_frame_header_m (md_magicless md) s) eqn:E; try (exfalso; exact (H _ eq_refl));
repeat match goal with |- context [if ?b then _ else _] => destruct b end; discriminate.
Qed.

Lemma rs_walk_cur_none : forall fuel md wl s, walk_cur fuel md sel_none None wl s = None.
Proof.
induction fuel; intros md wl s; cbn [walk_cur]; auto.
destruct (Zlength s <? starting_len (md_magicless md)); auto.
destruct (negb (md_magicless md) && is_skippable_magic (le_field s 0 4))%bool.
- destruct (skippable_frame_size s); auto. unfold skip_cd, sel_none. destruct (md_dwin md); apply IHfuel.
- unfold frame_dict, sel_none. destruct (get_frame_header_m _ s) eqn:E; auto;
  destruct (decode_frame_m md no_dict wl s) eqn:D; auto;
  exfalso; refine (rs_dec_nohdr md no_dict wl s _ _ _ D); intros h; rewrite E; discriminate.
Qed.

Lemma rs_clean_ids : forall l, set_clean l = true -> Forall (fun e => dd_id (snd e) <> 0) l.
Proof.
intros l Hc. unfold set_clean in Hc. apply andb_prop in Hc. destruct Hc as [_ Hc].
rewrite forallb_forall in Hc. apply Forall_forall. intros e He. specialize (Hc e He).
apply andb_prop in Hc. destruct Hc as [Hc _]. apply negb_true_iff in Hc. apply Z.eqb_neq in Hc. exact Hc.
Qed.

Lemma rs_clean_auto : forall l e, set_clean l = true -> In e l -> dict_auto (dd_bytes (snd e)) <> None.
Proof.
intros l e Hc Hin. unfold set_clean in Hc. apply andb_prop in Hc. destruct Hc as [_ Hc].
rewrite forallb_forall in Hc. specialize (Hc e Hin).
apply andb_prop in Hc. destruct Hc as [_ Hc]. destruct (dict_auto _); [ discriminate | discriminate ].
Qed.

Lemma rs_find0 : forall l, Forall (fun e => dd_id (snd e) <> 0) l -> set_find l 0 = nullval.
Proof.
intros l Hl. unfold set_find. destruct (find (fun e => dd_id (snd e) =? 0) l) eqn:E; auto.
apply find_some in E. destruct E as [Hin Heq]. apply Z.eqb_eq in Heq.
rewrite Forall_forall in Hl. exfalso. exact (Hl _ Hin Heq).
Qed.

Lemma rs_frame_dict_none : forall mg cd x h, get_frame_header_m mg x = FH_ok h -> frame_dict mg sel_none cd x = cd.
Proof. intros mg cd x h E. unfold frame_dict, sel_none. rewrite E. reflexivity. Qed.

(* lh_fdm without the facts on the frame's bytes x (its type and size) *)
Definition lh_fdm0 (a: dsa) (k1: cst3) (x: list Z) (dm: dict_model) : Prop :=
  let st := a_st a in
  (dc_set st = nil /\ dictref_model (dc_dict st) = Some dm) \/
  (dc_set st <> nil /\ sel_on (c3_par k1) (c3_sp k1) = true /\ set_clean (dc_set st) = true /\
   df_ddict (snd (getddict_res (c3_dict k1))) <> nullval /\
   exists h q dd, get_frame_header_m (lh_mg k1) x = FH_ok h /\
     q = (if eq_dec (set_find (dc_set st) (fh_dictID h)) nullval then df_ddict (c3_dict k1)
          else set_find (dc_set st) (fh_dictID h)) /\
     In (q, dd) (dc_set st) /\ dict_auto (dd_bytes dd) = Some dm).

Lemma fdm_of0 : forall a k1 x dm, lh_fdm0 a k1 x dm ->
  (forall h, get_frame_header_m (lh_mg k1) x = FH_ok h -> fh_frameType h = 0) ->
  frame_compressed_size_m (lh_mg k1) x = Some (Zlength x) -> lh_fdm a k1 x dm.
Proof.
  intros a k1 x dm [H | (Hne & Hso & Hcl & Hnn & h & q & dd & Hh & Hq & Hin & Ha)] Ht Hf; [ left; exact H | ].
  right. do 4 (split; [ assumption | ]). exists h, q, dd.
  split; [ exact Hh | ]. split; [ exact (Ht h Hh) | ]. split; [ exact Hf | ]. auto.
Qed.

(* getDDict's DDict is not NULL when the context's dictionary is a DDict or has bytes *)
Lemma rs_getdd_nn : forall st d, dict_rel3 st d -> (forall q, In q (map fst (dc_set st)) -> isptr q) ->
  (exists dr, dc_dict st = Some dr /\
     match dr_src dr with DSDDict _ _ => True | _ => negb (Nat.eqb (length (dr_bytes dr)) 0) = true end) ->
  df_ddict (snd (getddict_res d)) <> nullval.
Proof.
  intros st d Hd Hpt (dr & Ed & Hb).
  destruct Hd as [Hd | (Hne & Hl & Hu & Hlx & Hin)].
  - rewrite Ed in Hd. unfold dict_rel3_of in Hd. unfold getddict_res.
    destruct (dr_src dr) as [pk | | q dd] eqn:Es.
    + destruct (Zlength (dr_bytes dr) =? 0) eqn:Ez.
      * exfalso. apply Z.eqb_eq in Ez. apply Zlength_nil_inv in Ez. rewrite Ez in Hb. cbn in Hb. discriminate.
      * destruct Hd as (Hp & Hdd & Hu & _). rewrite Hu.
        destruct (dr_once dr); cbn; rewrite Hdd; intro X; rewrite X in Hp; exact Hp.
    + destruct Hd as (_ & Hd). destruct (Zlength (dr_bytes dr) =? 0) eqn:Ez.
      * exfalso. apply Z.eqb_eq in Ez. apply Zlength_nil_inv in Ez. rewrite Ez in Hb. cbn in Hb. discriminate.
      * destruct Hd as (buf & ld & am & Hp & Hdd & Hu & _). rewrite Hu. cbn. rewrite Hdd. intro X; rewrite X in Hp; exact Hp.
    + destruct Hd as (_ & _ & Hp & _ & Hdd & Hu & _). rewrite Hu. cbn. rewrite Hdd. intro X; rewrite X in Hp; exact Hp.
  - unfold getddict_res. rewrite Hu. cbn. specialize (Hpt _ Hin). intro X; rewrite X in Hpt; exact Hpt.
Qed.

(* the frame's dictionary in the model is the DDict the shortcut decodes with *)
Lemma rl_fdm0 : hs_probe_ok -> forall a w hb h tbl d1 did1 cd x dm,
  base_call (a_st a) (w_k w) -> (dc_set (a_st a) <> nil -> c3_sp (w_k w) <> nullval) -> bytes_ok hb ->
  get_frame_header_m (lh_mg (w_k w)) hb = FH_ok h ->
  lhA_sel (w_k w) hb 0 (fh_val h) tbl d1 did1 -> cur_dict_ok (a_st a) (w_k w) cd ->
  (st_sel (a_st a) = (sel_none, None) -> cd = None) ->
  get_frame_header_m (lh_mg (w_k w)) x = FH_ok h ->
  frame_dict (lh_mg (w_k w)) (fst (st_sel (a_st a))) cd x = Some dm ->
  lh_fdm0 a (k_A (w_k w) (fh_val h) d1 did1) x dm.
Proof.
  intros Hpr a w hb h tbl d1 did1 cd x dm Hb Hsp Hbh Hh Hsel Hcd Hcd0 Hx Hf.
  pose proof (rl_dict_rel Hpr _ _ _ _ _ _ _ _ Hb Hsel) as Hdr1.
  destruct Hb as (Hstab & Hpar & Hset & Hdr & Hsco).
  unfold lh_fdm0.
  destruct (dc_set (a_st a)) as [ | e0 l0 ] eqn:Es.
  - left. split; [ reflexivity | ].
    unfold st_sel in Hf. rewrite Es in Hf. cbn [fst] in Hf. rewrite (rs_frame_dict_none _ _ _ _ Hx) in Hf.
    destruct (Hcd dm Hf) as [[_ H] | [H _]]; [ exact H | congruence ].
  - right. split; [ discriminate | ].
    rewrite <- Es in *.
    assert (Hon: dp_multi (dc_par (a_st a)) = 1 /\ set_clean (dc_set (a_st a)) = true /\
                 (exists dr, dc_dict (a_st a) = Some dr /\
                    match dr_src dr with DSDDict _ _ => True | _ => negb (Nat.eqb (length (dr_bytes dr)) 0) = true end) /\
                 fst (st_sel (a_st a)) = set_sel (dc_set (a_st a))).
    { unfold st_sel in Hf, Hcd0 |- *. rewrite Es in Hf, Hcd0 |- *.
      destruct (dc_dict (a_st a)) as [dr|].
      - match goal with |- context [if ?b then _ else _] => destruct b eqn:Em end.
        + apply andb_prop in Em. destruct Em as [Em Edr]. apply andb_prop in Em. destruct Em as [Em Ec].
          apply Z.eqb_eq in Em. split; [ exact Em | ]. split; [ exact Ec | ]. split; [ | reflexivity ].
          exists dr. split; [ reflexivity | ]. destruct (dr_src dr); auto.
        + rewrite (Hcd0 eq_refl) in Hf. cbn [fst] in Hf. rewrite (rs_frame_dict_none _ _ _ _ Hx) in Hf. discriminate.
      - rewrite (Hcd0 eq_refl) in Hf. cbn [fst] in Hf. rewrite (rs_frame_dict_none _ _ _ _ Hx) in Hf. discriminate. }
    destruct Hon as (Hmulti & Hclean & Hdrok & Hsel0).
    assert (Hso: sel_on (c3_par (w_k w)) (c3_sp (w_k w)) = true).
    { unfold sel_on. rewrite Hpar, Hmulti. cbn.
      assert (c3_sp (w_k w) <> nullval) by (apply Hsp; rewrite Es; discriminate).
      unfold veqb. destruct (Val.eq (c3_sp (w_k w)) _) as [E|E]; [ exfalso; apply H; exact E | reflexivity ]. }
    split; [ exact Hso | ].
    destruct Hsel as (_ & _ & id & Hid & Hsb). specialize (Hid Hso).
    unfold sel_by in Hsb. rewrite Hso in Hsb. destruct Hsb as (Hinv & Hidr & Hd1 & _).
    destruct (rl_gfh3 _ _ _ Hh Hbh) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hidh & _).
    assert (Hide: id = fh_dictID h).
    { change (fp_dictID (fh_val h)) with (Vint (Int.repr (fh_dictID h))) in Hid. apply Vint_inj in Hid.
      apply (f_equal Int.unsigned) in Hid. rewrite !Int.unsigned_repr in Hid by lia. lia. }
    subst id.
    pose proof (rs_clean_ids _ Hclean) as Hnz.
    assert (Hr: sel_r (c3_dict (w_k w)) (c3_set (w_k w)) tbl (fh_dictID h) =
                if eq_dec (df_ddict (c3_dict (w_k w))) nullval then nullval else set_find (dc_set (a_st a)) (fh_dictID h)).
    { unfold sel_r. destruct (eq_dec (df_ddict (c3_dict (w_k w))) nullval); [ reflexivity | ].
      destruct (Hpr _ _ _ Hinv Hidr) as [_ Hf']. rewrite Hf'; [ rewrite Hset; reflexivity | rewrite Hset; auto ]. }
    rewrite Hr in Hd1.
    unfold frame_dict in Hf. rewrite Hx, Hsel0 in Hf.
    split; [ exact Hclean | ].
    split.
    { apply (rs_getdd_nn (a_st a) d1 Hdr1); [ | exact Hdrok ].
      intros q Hq. apply in_map_iff in Hq. destruct Hq as [e [<- He]].
      destruct Hinv as (_ & _ & _ & _ & _ & Hptr & _). rewrite Forall_forall in Hptr.
      rewrite Hset in Hptr. exact (Hptr e He). }
    exists h.
    assert (Hk1: c3_dict (k_A (w_k w) (fh_val h) d1 did1) = d1) by reflexivity.
    assert (Hmg1: lh_mg (k_A (w_k w) (fh_val h) d1 did1) = lh_mg (w_k w)) by reflexivity.
    rewrite Hk1, Hmg1.
    destruct (set_sel (dc_set (a_st a)) (fh_dictID h)) as [d|] eqn:Hss.
    + injection Hf as <-.
      unfold set_sel in Hss. destruct (fh_dictID h =? 0); [ discriminate | ].
      destruct (find (fun e => dd_id (snd e) =? fh_dictID h) (dc_set (a_st a))) as [e|] eqn:Ef; [ | discriminate ].
      assert (Hfind: set_find (dc_set (a_st a)) (fh_dictID h) = fst e) by (unfold set_find; rewrite Ef; reflexivity).
      apply find_some in Ef. destruct Ef as [Hin _].
      assert (Hne: fst e <> nullval).
      { destruct Hinv as (_ & _ & _ & _ & _ & Hptr & _). rewrite Forall_forall in Hptr.
        rewrite Hset in Hptr. specialize (Hptr _ Hin). intro E; rewrite E in Hptr; exact Hptr. }
      exists (fst e), (snd e). rewrite Hfind.
      destruct (eq_dec (fst e) nullval); [ contradiction | ].
      split; [ exact Hx | ]. split; [ reflexivity | ]. split; [ destruct e; exact Hin | exact Hss ].
    + assert (Hnull: set_find (dc_set (a_st a)) (fh_dictID h) = nullval).
      { unfold set_sel in Hss. destruct (fh_dictID h =? 0) eqn:E0.
        - apply Z.eqb_eq in E0. rewrite E0. apply rs_find0; auto.
        - unfold set_find. destruct (find _ _) as [e|] eqn:Ef; [ | reflexivity ].
          apply find_some in Ef. destruct Ef as [Hin _]. exfalso. exact (rs_clean_auto _ _ Hclean Hin Hss). }
      rewrite Hnull in Hd1.
      assert (Hd1': d1 = c3_dict (w_k w)).
      { rewrite Hd1. unfold sel_dict. destruct (eq_dec (df_ddict (c3_dict (w_k w))) nullval);
        destruct (eq_dec nullval nullval); congruence. }
      clear Hd1. subst d1.
      destruct (Hcd dm Hf) as [[Hn _] | (_ & _ & (dd & Hin & Hauto) & _)]; [ congruence | ].
      exists (df_ddict (c3_dict (w_k w))), dd. rewrite Hnull.
      destruct (eq_dec nullval nullval) as [_ | Hn]; [ | congruence ].
      split; [ exact Hx | ]. split; [ reflexivity | ]. split; [ exact Hin | exact Hauto ].
Qed.

Lemma rl_fdm : hs_probe_ok -> forall a w hb h tbl d1 did1 cd x dm,
  base_call (a_st a) (w_k w) -> (dc_set (a_st a) <> nil -> c3_sp (w_k w) <> nullval) -> bytes_ok hb ->
  get_frame_header_m (lh_mg (w_k w)) hb = FH_ok h ->
  lhA_sel (w_k w) hb 0 (fh_val h) tbl d1 did1 -> cur_dict_ok (a_st a) (w_k w) cd ->
  (st_sel (a_st a) = (sel_none, None) -> cd = None) ->
  get_frame_header_m (lh_mg (w_k w)) x = FH_ok h -> fh_frameType h = 0 ->
  frame_compressed_size_m (lh_mg (w_k w)) x = Some (Zlength x) ->
  frame_dict (lh_mg (w_k w)) (fst (st_sel (a_st a))) cd x = Some dm ->
  lh_fdm a (k_A (w_k w) (fh_val h) d1 did1) x dm.
Proof.
  intros Hpr a w hb h tbl d1 did1 cd x dm Hb Hsp Hbh Hh Hsel Hcd Hcd0 Hx Ht Hfx Hf.
  apply fdm_of0; [ exact (rl_fdm0 Hpr a w hb h tbl d1 did1 cd x dm Hb Hsp Hbh Hh Hsel Hcd Hcd0 Hx Hf) | | exact Hfx ].
  intros h' Hh'. change (lh_mg (k_A (w_k w) (fh_val h) d1 did1)) with (lh_mg (w_k w)) in Hh'.
  rewrite Hx in Hh'. injection Hh' as <-. exact Ht.
Qed.

Lemma rl_cd_none : forall a w hb dsin recs cd, lh_split_ok a w hb dsin recs cd ->
  st_sel (a_st a) = (sel_none, None) -> cd = None.
Proof.
  intros a w hb dsin recs cd (_ & _ & Hcur & _) E. rewrite <- Hcur.
  unfold sm_curafter, series_cur, sm_of. cbn [sm_md sm_sel sm_cur]. rewrite E. cbn [fst snd].
  apply rs_walk_cur_none.
Qed.

(* the header's bytes all came in this call when the frame is decoded in one go *)
Lemma rl_hb_input : forall a w hb, lh_ctx a w hb -> w_ipc w - a_ipos a = Zlength hb ->
  hb = sublist (a_ipos a) (w_ipc w) (a_ibs a).
Proof.
  intros a w hb Hc Hl.
  destruct Hc as (Ha & _ & Hci & _ & _ & He & Hfp & _).
  assert (Hst: sf_stage (c3_s (w_k w)) = zdss_loadHeader) by (unfold lh_entry in He; tauto).
  assert (Hip: a_ipos a <= w_ipc w <= a_isz a) by (unfold lh_entry in He; tauto).
  assert (Hip0: 0 <= a_ipos a /\ Zlength (a_ibs a) = a_isz a) by (unfold dsa_ok in Ha; tauto).
  destruct Hci as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlast & _).
  destruct (Hlast Hst hb Hfp) as (pre & j & Hj & Hhb & ->).
  destruct pre as [ | p pre ].
  - rewrite app_nil_l in Hhb. exact Hhb.
  - exfalso.
    rewrite Hhb, Zlength_app, Zlength_sublist, Zlength_cons in Hl by lia.
    pose proof (Zlength_nonneg pre). lia.
Qed.

Lemma why_short : MF3 -> hs_probe_ok -> forall a w hb h tbl d1 did1 cSize r out,
  lh_ctx a w hb -> par_ok (dc_par (a_st a)) -> (dc_set (a_st a) <> nil -> c3_sp (w_k w) <> nullval) ->
  lhA_sel (w_k w) hb 0 (fh_val h) tbl d1 did1 -> get_frame_header_m (lh_mg (w_k w)) hb = FH_ok h ->
  lhB_facts a w (k_A (w_k w) (fh_val h) d1 did1) hb h cSize r out -> dec_err r -> err_why a r.
Proof.
  intros HMF Hpr a w hb h tbl d1 did1 cSize r out Hc Hp Hsp Hsel Hh HB Hd.
  split; [ exact Hd | ].
  destruct (rl_entry a w hb Hc) as (Hb & Hbh & Hok & Ha).
  destruct (rl_split a w hb Hc (rl_wmax _ Hp)) as [F | (dsin & recs & cd & Hsp')]; [ right; left; exact F | ].
  assert (Hib: bytes_ok (a_ibs a) /\ 0 <= a_ipos a /\ Zlength (a_ibs a) = a_isz a) by (unfold dsa_ok in Ha; tauto).
  destruct Hib as (Hibb & Hip0 & Hibl).
  assert (Hip: a_ipos a <= w_ipc w <= a_isz a)
    by (destruct Hc as (_ & _ & _ & _ & _ & He & _); unfold lh_entry in He; tauto).
  destruct HB as (Hft & Hcs & Hcap & Hl & Hfcs & HcS & Hr & Hlo & _ & _ & Hos).
  set (k1 := k_A (w_k w) (fh_val h) d1 did1) in *.
  assert (Hmg1: lh_mg k1 = lh_mg (w_k w)) by reflexivity.
  rewrite Hmg1 in Hfcs.
  pose proof (rl_hb_input a w hb Hc Hl) as Hhb.
  assert (Hsz: fh_headerSize h = Zlength hb) by (unfold hdr_lenok in Hok; rewrite Hh in Hok; auto).
  pose proof (LH3RetG.RG.gap_of_hdr_m _ (a_ibs a) (a_ipos a) (w_ipc w) (a_isz a) hb h cSize Hibb Hibl Hip0
                ltac:(lia) ltac:(lia) (eq_sym Hhb) Hh Hsz Hfcs) as Hgap.
  set (x := sublist (a_ipos a) (a_ipos a + cSize) (a_ibs a)) in *.
  set (y := sublist (w_ipc w) (a_ipos a + cSize) (a_ibs a)).
  assert (Hx: x = hb ++ y) by (unfold x, y; rewrite Hhb, <- sublist_split; auto; lia).
  assert (Hy: is_prefix y (sublist (w_ipc w) (a_isz a) (a_ibs a))).
  { rewrite (sublist_split (w_ipc w) (a_ipos a + cSize) (a_isz a)) by lia. apply StreamModelFacts.is_prefix_app. }
  assert (Hbx: bytes_ok x) by (unfold x, bytes_ok in *; apply Forall_sublist; auto).
  assert (Hlx: Zlength x = cSize) by (unfold x; rewrite Zlength_sublist; lia).
  assert (Hfx: frame_compressed_size_m (lh_mg (w_k w)) x = Some (Zlength x)).
  { assert (Hbs: bytes_ok (sublist (a_ipos a) (a_isz a) (a_ibs a))) by (unfold bytes_ok in *; apply Forall_sublist; auto).
    destruct (LH3RetG.RG.fcs_m_trunc _ _ _ Hbs Hfcs) as [_ Ht]. rewrite <- sublist_firstn, sublist_sublist in Ht by lia.
    rewrite Hlx. unfold x. rewrite <- Ht. f_equal. f_equal; lia. }
  assert (Hfb: fbad (sm_of (a_st a)) cd x -> lh_fails a).
  { intros Hf. apply (rl_fails_fbad HMF a w hb dsin recs cd y Hsp' Hy). rewrite <- Hx. exact Hf. }
  assert (Hfd: fdead (sm_of (a_st a)) cd x -> lh_fails a).
  { intros Hf. apply (rl_fails_fdead HMF a w hb dsin recs cd y (rl_wmax _ Hp) Hsp' Hy). rewrite <- Hx. exact Hf. }
  assert (Hmg: sm_mg (sm_of (a_st a)) = lh_mg (w_k w)) by apply (rl_mg _ _ Hb).
  destruct (rl_gfh3 _ _ _ Hh Hbh) as (_ & _ & _ & _ & _ & _ & Hft01 & _).
  assert (Ht0: fh_frameType h = 0) by lia.
  assert (Hgx: get_frame_header_m (lh_mg (w_k w)) x = FH_ok h) by (rewrite Hx; apply LH3RetG.RG.gfh_m_ext; auto).
  assert (Hfdx: frame_dict (lh_mg (w_k w)) (fst (st_sel (a_st a))) cd x =
                frame_dict (lh_mg (w_k w)) (fst (st_sel (a_st a))) cd hb) by (unfold frame_dict; rewrite Hgx, Hh; reflexivity).
  destruct (frame_dict (lh_mg (w_k w)) (fst (st_sel (a_st a))) cd x) as [dm|] eqn:Fd.
  2: { right; left. apply Hfd. rewrite Hx. apply (mf_fdead_app HMF).
       rewrite <- Hmg in Hh.
       destruct (mf_hdr_zstd HMF (sm_of (a_st a)) cd hb h Hbh Hh Ht0 (eq_sym Hsz)) as (Hn & _).
       apply Hn. rewrite Hmg. cbn [sm_of sm_sel]. rewrite <- Hfdx. reflexivity. }
  assert (Hsf: shortcut_frame (sm_of (a_st a)) cd x dm).
  { unfold shortcut_frame. rewrite Hmg. split; [ exact Hfx | ]. split; [ exists h; auto | ]. exact Fd. }
  pose proof (rl_fdm Hpr a w hb h tbl d1 did1 cd x dm Hb Hsp Hbh Hh Hsel (proj2 (proj2 (proj2 (proj2 (proj2 Hsp')))))
                (rl_cd_none _ _ _ _ _ _ Hsp') Hgx Ht0 Hfx Fd) as Hfdm.
  specialize (Hos dm Hfdm).
  assert (Hmd: dmode_of (c3_par k1) = md_len (sm_md (sm_of (a_st a)))) by (destruct Hb as (_ & Hpar & _); cbn; rewrite Hpar; reflexivity).
  rewrite Hmd in Hos.
  assert (Herr: is_error_code r = true) by apply Hd.
  destruct Hos as [_ Hos].
  revert Hos. destruct (decode_series_m (md_len (sm_md (sm_of (a_st a)))) sel_none (Some dm) no_wlim x) as [c | | ] eqn:Hdx; intros Hos.
  - destruct Hos as [_ Hos]. destruct (Hos Herr) as [Hlt | Hm].
    2: { left. exact Hm. }
    right; left. apply Hfb. intros t Ht E.
    destruct (mf_shortcut_capacity HMF (sm_of (a_st a)) cd x dm t Hbx Hsf Ht E) as (c' & Hc' & Hcl).
    rewrite Hdx in Hc'. injection Hc' as <-.
    rewrite Hmg in Hcl. specialize (Hcl h Hgx Hcs). lia.
  - right; left. apply Hfb. apply (mf_shortcut_det HMF _ _ _ dm); auto.
  - (* no extension the model decodes: it would decode the frame (the frame may be refused, so no fdead) *)
    right; left. apply Hfb. intros t Ht E.
    destruct (mf_shortcut_capacity HMF (sm_of (a_st a)) cd x dm t Hbx Hsf Ht E) as (c' & Hc' & _).
    rewrite Hdx in Hc'. discriminate.
Qed.

End CM_LH3R2Short_1.
