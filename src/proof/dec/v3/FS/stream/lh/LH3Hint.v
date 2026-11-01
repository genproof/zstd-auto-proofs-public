(* FS3 streaming, case zdss_loadHeader: the hint return (input ends inside the header): stream_post with SR3. *)
Require Zstd.proof.dec.v3.FS.stream.lh.LHH4Model.
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3Stmts Zstd.proof.dec.v3.FS.stream.lh.LH3R2Lib.
Require Import Zstd.proof.model.StreamProgress Zstd.proof.dec.v3.FS.stream.epi.E3Prog.
Local Open Scope logic.

Section CM_LH3Hint_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* ---------- the dictionary after the selection (v2 had none; G1's g1_cd with the second call's fParams) ---------- *)

Lemma h_clean_ids : forall l, set_clean l = true -> Forall (fun e => dd_id (snd e) <> 0) l.
Proof.
intros l Hc. unfold set_clean in Hc. apply andb_prop in Hc. destruct Hc as [_ Hc].
rewrite forallb_forall in Hc. apply Forall_forall. intros e He. specialize (Hc e He).
apply andb_prop in Hc. destruct Hc as [Hc _]. apply negb_true_iff in Hc. apply Z.eqb_neq in Hc. exact Hc.
Qed.

Lemma h_find0 : forall l, Forall (fun e => dd_id (snd e) <> 0) l -> set_find l 0 = nullval.
Proof.
intros l Hl. unfold set_find. destruct (find (fun e => dd_id (snd e) =? 0) l) eqn:E; auto.
apply find_some in E. destruct E as [Hin Heq]. apply Z.eqb_eq in Heq.
rewrite Forall_forall in Hl. exfalso. exact (Hl _ Hin Heq).
Qed.

Lemma h_walk_cur_none : forall fuel md wl s, walk_cur fuel md sel_none None wl s = None.
Proof.
induction fuel; intros md wl s; cbn [walk_cur]; auto.
destruct (Zlength s <? starting_len (md_magicless md)); auto.
destruct (negb (md_magicless md) && is_skippable_magic (le_field s 0 4))%bool.
- destruct (skippable_frame_size s); auto.
  replace (skip_cd md sel_none s None) with (@None dict_model)
    by (unfold skip_cd, sel_none; destruct (md_dwin md); reflexivity).
  apply IHfuel.
- unfold frame_dict, sel_none. destruct (get_frame_header_m _ s) eqn:G; auto.
  all: destruct (decode_frame_m md no_dict wl s) eqn:D; auto.
  all: destruct (LHH4FrameM.dfm_hdr_inv md no_dict wl s) as (h & Gh & _);
         [ rewrite D; discriminate | rewrite D; discriminate | congruence ].
Qed.

Lemma h_repr_inj : forall a b, 0 <= a <= Int.max_unsigned -> 0 <= b <= Int.max_unsigned ->
  Vint (Int.repr a) = Vint (Int.repr b) -> a = b.
Proof.
intros a b Ha Hb E. apply Vint_inj in E. apply (f_equal Int.unsigned) in E.
rewrite !Int.unsigned_repr in E by lia. exact E.
Qed.

Lemma h_cd : hs_probe_ok -> forall st k hb kk v tbl d1 did1 cd k',
  base_call st k -> lhA_sel k hb kk v tbl d1 did1 -> get_frame_header_m (lh_mg k) hb = FH_more kk ->
  (st_sel st = (sel_none, None) -> cd = None) ->
  cur_dict_ok st k cd -> c3_dict k' = d1 ->
  (fs_fParams (c3_fs k') = v \/ fs_fParams (c3_fs k') = fh_val fh_zero) -> cur_dict_ok st k' cd.
Proof.
intros Hpr st k hb kk v tbl d1 did1 cd k' Hb Hsel Hk Hcd Hold Hd' Hv'.
intros dm Hdm. destruct (Hold dm Hdm) as [H1 | (Hne & Huses & (dd & Hin & Hauto) & (id0 & Hid0 & Hr0 & Hf0))].
{ left; exact H1. }
right.
destruct Hb as (Hstab & Hpar & Hset & Hdr & Hsco).
assert (Hon: dp_multi (dc_par st) = 1 /\ set_clean (dc_set st) = true).
{ unfold st_sel in Hcd. destruct (dc_set st) eqn:Es; [ congruence | ].
  destruct (dc_dict st); [ | rewrite Hcd in Hdm by auto; discriminate ].
  destruct (dp_multi (dc_par st) =? 1) eqn:Em; [ | rewrite Hcd in Hdm by auto; discriminate ].
  destruct (set_clean (_ :: _)) eqn:Ec; [ | rewrite Hcd in Hdm by auto; discriminate ].
  split; [ apply Z.eqb_eq; auto | auto ]. }
destruct Hon as [Hmulti Hclean].
pose proof (h_clean_ids _ Hclean) as Hnz.
destruct Hsel as (_ & Hfh & id & Hid & Hsb).
unfold fh_post_m in Hfh. rewrite Hk in Hfh. destruct Hfh as [_ Hv].
(* v's dictID: the entry's or 0 *)
assert (Hvid: fp_dictID v = Vint (Int.repr id0) \/ fp_dictID v = Vint (Int.repr 0)).
{ destruct (Zlength hb <? starting_len (lh_mg k)); subst v; [ left; exact Hid0 | right; reflexivity ]. }
(* the selection keeps the DDict pointer (a hit is the current DDict) *)
assert (Hd1: df_ddict d1 = df_ddict (c3_dict k) /\ df_uses d1 = -1).
{ unfold sel_by in Hsb. destruct (sel_on (c3_par k) (c3_sp k)) eqn:Eso.
  - specialize (Hid eq_refl). destruct Hsb as (Hinv & Hidr & Hd1 & _). subst d1. unfold sel_dict, sel_r.
    destruct (eq_dec (df_ddict (c3_dict k)) nullval) as [E|E].
    { destruct (eq_dec nullval nullval); [ auto | congruence ]. }
    assert (Hnz': Forall (fun e => dd_id (snd e) <> 0) (c3_set k)) by (rewrite Hset; exact Hnz).
    destruct (Hpr _ _ _ Hinv Hidr) as [_ Hf]. rewrite (Hf Hnz').
    rewrite Hset.
    assert (Hcase: id = id0 \/ id = 0).
    { destruct Hvid as [Hv0|Hv0]; rewrite Hv0 in Hid.
      - left. apply h_repr_inj; auto; lia.
      - right. apply h_repr_inj; auto; rep_lia. }
    destruct Hcase as [-> | ->].
    + destruct Hf0 as [Hf0 | Hf0]; rewrite Hf0.
      * destruct (eq_dec nullval nullval); [ auto | congruence ].
      * destruct (eq_dec (df_ddict (c3_dict k)) nullval); [ contradiction | ]. cbn. auto.
    + rewrite (h_find0 _ Hnz). destruct (eq_dec nullval nullval); [ auto | congruence ].
  - destruct Hsb as [-> _]. auto. }
destruct Hd1 as [Hdd1 Hu1].
rewrite Hd'. rewrite Hdd1.
split; [ exact Hne | split; [ exact Hu1 | split; [ exists dd; split; [ exact Hin | exact Hauto ] | ] ] ].
assert (Hfin: fp_dictID (fs_fParams (c3_fs k')) = Vint (Int.repr id0) \/
              fp_dictID (fs_fParams (c3_fs k')) = Vint (Int.repr 0)).
{ destruct Hv' as [-> | ->]; [ exact Hvid | right; reflexivity ]. }
destruct Hfin as [Hf | Hf].
- exists id0. auto.
- exists 0. split; [ exact Hf | split; [ rep_lia | left; apply h_find0; auto ] ].
Qed.

Lemma h_dict_rel : hs_probe_ok -> forall st k hb kk v tbl d1 did1,
  base_call st k -> lhA_sel k hb kk v tbl d1 did1 -> dict_rel3 st d1.
Proof.
intros Hpr st k hb kk v tbl d1 did1 Hb Hsel.
destruct Hb as (_ & _ & Hset & Hdr & _).
destruct Hsel as (_ & _ & id & _ & Hsb). unfold sel_by in Hsb.
destruct (sel_on (c3_par k) (c3_sp k)).
- destruct Hsb as (Hinv & Hidr & Hd1 & _). subst d1. unfold sel_dict.
  destruct (eq_dec (sel_r (c3_dict k) (c3_set k) tbl id) nullval) as [E|E]; [ exact Hdr | ].
  right. unfold sel_r in *.
  destruct (eq_dec (df_ddict (c3_dict k)) nullval); [ contradiction | ].
  destruct (Hpr _ _ _ Hinv Hidr) as [[Hn | Hin] _]; [ contradiction | ].
  rewrite Hset in Hin. split.
  + intro Hnil. rewrite Hnil in Hin. contradiction.
  + unfold dict_switched, switch_fields. cbn. rewrite Hset. auto.
- destruct Hsb as [Hd1 _]. subst d1. exact Hdr.
Qed.


(* ---------- the bytes of this call ---------- *)

Definition h_u (a: dsa) (w: lw) : list Z := sublist (w_ipc w) (a_isz a) (a_ibs a).

Lemma h_prefix_app_l : forall (p q s: list Z), is_prefix (p ++ q) s -> is_prefix p s.
Proof.
unfold is_prefix; intros p q s H.
pose proof (firstn_skipn (length (p ++ q)) s) as E. rewrite H in E. rewrite <- E, <- app_assoc.
rewrite firstn_app, Nat.sub_diag, firstn_O, app_nil_r, firstn_all. reflexivity.
Qed.

Lemma h_facts : forall a w hb, lh_ctx a w hb ->
  ss_ahead (dc_ss (a_st a)) = 0 /\ a_sin a = ss_in (dc_ss (a_st a)) /\
  (hb = nil -> w_ipc w = a_ipos a) /\ bytes_ok (hb ++ h_u a w) /\ Zlength (h_u a w) = a_isz a - w_ipc w /\
  0 <= a_ipos a <= w_ipc w /\ w_ipc w <= a_isz a /\ Zlength (a_ibs a) = a_isz a /\ bytes_ok (a_ibs a) /\
  0 <= ss_stall (dc_ss (a_st a)).
Proof.
intros a w hb Hc.
destruct Hc as (Ha & Hst & Hci & Hsmw & Hle & He & Hfp & Hdl & Hah & Hpend & Hentry & Hunt).
destruct Hci as (Hipc & Hopc & Hloc & Hpre & Hdll & Hdlc & Hdlb & Hbase & Hsinb & Hnfp1 & Hnfp2 & Hnfp0 & Hcore &
                 Hddok & Hstout & Hahd & Hblk & Halive & Hlh & Hsin & Hexp & HTf).
destruct He as (Hst1 & Hlh' & H18 & Hbo & Hsub & Hhost & HinPos & Hos & Hoe & Hipc' & Hopc' & Hlo & Hsmw' & Hbase' & Hlenok).
destruct Hst as (_ & Hah01 & Hahl & Hstall).
assert (Hib: Zlength (a_ibs a) = a_isz a /\ bytes_ok (a_ibs a) /\ 0 <= a_ipos a) by (unfold dsa_ok in Ha; tauto).
destruct Hib as (Hibl & Hibb & Hip0).
rewrite Hah, app_nil_r in Hsin.
assert (H0: ss_ahead (dc_ss (a_st a)) = 0).
{ unfold a_sin in Hsin. apply (f_equal (@Zlength Z)) in Hsin.
  rewrite Zlength_sublist in Hsin by lia. lia. }
assert (Hlu: Zlength (h_u a w) = a_isz a - w_ipc w) by (unfold h_u; rewrite Zlength_sublist; lia).
split; [ exact H0 | ]. split; [ exact Hsin | ]. split.
{ intros ->. destruct (Hlh Hst1 nil Hfp) as (pre & j & Hj & Hhb & ->).
  apply (f_equal (@Zlength Z)) in Hhb. rewrite Zlength_nil, Zlength_app, Zlength_sublist in Hhb by lia.
  pose proof (Zlength_nonneg pre). lia. }
split; [ unfold bytes_ok in *; apply Forall_app; split; auto; unfold h_u; apply Forall_sublist; auto | ].
split; [ exact Hlu | ]. split; [ lia | ]. split; [ lia | ]. auto.
Qed.

(* the model at the entry, on all the bytes read once the rest of the input is in the header *)
Lemma h_split : MF3 -> forall a w hb, lh_ctx a w hb ->
  let sm := sm_of (a_st a) in
  dead sm (ss_in (dc_ss (a_st a)) ++ sublist (a_ipos a) (a_isz a) (a_ibs a)) \/
  exists dsin recs cd, bytes_ok dsin /\
    series_frames_m (sm_md sm) (sm_sel sm) (sm_cur sm) no_wlim dsin = (recs, TEnd) /\
    series_cur (sm_md sm) (sm_sel sm) (sm_cur sm) no_wlim dsin = cd /\
    ss_in (dc_ss (a_st a)) ++ sublist (a_ipos a) (a_isz a) (a_ibs a) = dsin ++ hb ++ h_u a w /\
    ss_out (dc_ss (a_st a)) = flat_map fr_content recs /\ cur_dict_ok (a_st a) (w_k w) cd.
Proof.
intros HMF a w hb Hc sm.
destruct (h_facts a w hb Hc) as (H0 & Hsin & _ & _ & _ & Hip & Hipc & Hibl & Hibb & _).
pose proof Hc as (Ha & Hst & Hci & Hsmw & Hle & He & Hfp & Hdl & Hah & Hpend & Hentry & Hunt).
destruct Hci as (_ & _ & _ & _ & _ & _ & _ & _ & Hsinb & _ & _ & _ & _ & _ & _ & _ & _ & Halive & _).
rewrite Hah, Hdl, !app_nil_r in Halive.
assert (Hall: ss_in (dc_ss (a_st a)) ++ sublist (a_ipos a) (a_isz a) (a_ibs a) =
              (a_sin a ++ sublist (a_ipos a) (w_ipc w) (a_ibs a)) ++ h_u a w).
{ rewrite <- Hsin, <- app_assoc. f_equal. unfold h_u. rewrite <- sublist_split; auto; lia. }
rewrite Hall.
destruct Halive as [Hd | (cd & Hm & Hcd & _)].
- left. apply (mf_dead_app HMF); auto.
- right. destruct Hm as (dsin & fb & recs & Hs & Hser & Hcur & Hcr & Hout).
  rewrite Hfp in Hcr, Hcd, Hout. rewrite Hpend in Hout. cbn [cur_rel] in Hcr. destruct Hcr as [Hfb _]. subst fb.
  cbn [next_cd fp_content] in Hcd, Hout. rewrite !app_nil_r in Hout.
  assert (Hbs: bytes_ok (dsin ++ hb)).
  { rewrite <- Hs. unfold bytes_ok in *. apply Forall_app; split; auto. apply Forall_sublist; auto. }
  exists dsin, recs, cd. split; [ unfold bytes_ok in *; apply Forall_app in Hbs; tauto | ].
  split; [ exact Hser | ]. split; [ exact Hcur | ]. split; [ rewrite Hs, <- app_assoc; reflexivity | ].
  split; [ exact Hout | exact Hcd ].
Qed.


(* ---------- the hint and stream_post ---------- *)

Lemma h_mg : forall a w hb, lh_ctx a w hb -> lh_mg (w_k w) = md_magicless (dmode_of (dc_par (a_st a))).
Proof.
intros a w hb Hc. destruct Hc as (_ & _ & Hci & _).
destruct Hci as (_ & _ & _ & _ & _ & _ & _ & Hbase & _). destruct Hbase as (_ & Hpar & _).
unfold lh_mg. cbn. rewrite Hpar. reflexivity.
Qed.

Lemma h_rng : forall mg hb u kk, get_frame_header_m mg hb = FH_more kk -> Zlength (hb ++ u) < kk ->
  0 < lh_hint mg (hb ++ u) kk <= 21.
Proof. intros. exact (LHH4Model.lhh_hint_rng mg hb u kk H H0). Qed.

Lemma h_noerr : forall r, 0 < r <= 21 -> is_error_code r = false.
Proof. intros r Hr. unfold is_error_code. apply Z.ltb_ge. lia. Qed.

(* the state after the hint return: all the input read, no output; stall' = 0 after reading input, one more
   call without progress otherwise *)
Definition hint_st (a: dsa) (r: Z) : dctx_st :=
  let st := a_st a in let ss := dc_ss st in
  set_last
    (set_ss st {| ss_in := ss_in ss ++ sublist (a_ipos a + ss_ahead ss) (a_isz a + 0) (a_ibs a);
                  ss_out := ss_out ss ++ nil;
                  ss_stall := if a_ipos a =? a_isz a then ss_stall ss + 1 else 0;
                  ss_err := is_error_code r;
                  ss_obuf := if dc_stable st then Some (a_obf a, a_osz a) else None; ss_ahead := 0 ;
                  ss_calls := ss_calls ss ++ [(sublist (a_ipos a) (a_isz a) (a_ibs a), a_osz a - a_opos a)] |})
    (Some stream_mark).

Lemma h_claims : MF3 -> forall a w hb kk ocap, lh_ctx a w hb ->
  get_frame_header_m (lh_mg (w_k w)) hb = FH_more kk -> Zlength (hb ++ h_u a w) < kk ->
  let st := a_st a in let ss := dc_ss st in
  let r := lh_hint (lh_mg (w_k w)) (hb ++ h_u a w) kk in
  let sin' := ss_in ss ++ sublist (a_ipos a + ss_ahead ss) (a_isz a + 0) (a_ibs a) in
  stream_claims_m (dmode_w (dmode_of (dc_par st))) (fst (st_sel st)) (snd (st_sel st)) (dp_wmax (dc_par st))
    (sublist 0 (Zlength (ss_in ss) - ss_ahead ss) (ss_in ss)) (ss_out ss) sin'
    (sin' ++ sublist (a_isz a + 0) (a_isz a) (a_ibs a)) (ss_out ss ++ nil) 0 ocap r.
Proof.
intros HMF a w hb kk ocap Hc Hk Hlt st ss r sin'.
destruct (h_facts a w hb Hc) as (H0 & Hsin & Hnil & Hbu & Hlu & Hip & Hipc & Hibl & Hibb & Hstall).
pose proof (h_rng _ hb (h_u a w) kk Hk Hlt) as Hr. fold r in Hr.
pose proof (h_noerr r Hr) as Herr.
pose proof Hc as (Ha & Hst & _).
destruct Hst as (Hcont & _).
pose proof (h_mg a w hb Hc) as Hmg.
subst sin' ss st. rewrite H0, !Z.add_0_r, Z.sub_0_r, sublist_same by lia.
unfold stream_claims_m. intros s Hs Hp. cbv zeta.
split; [ | split; [ | split ] ].
- intros Ht. rewrite app_nil_r. apply Hcont; [ | exact Ht ]. eapply h_prefix_app_l; exact Hp.
- intros E. lia.
- intros Ht _ _ Hex.
  eapply Z.le_trans; [ | apply Z.le_max_r ].
  destruct (h_split HMF a w hb Hc) as [Hd | (dsin & recs & cd & Bd & Hrecs & _ & Hall & Hout & _)].
  { exfalso. pose proof (proj1 Hd s Hp) as Hd0; clear Hd; rename Hd0 into Hd. cbn [sm_of sm_md sm_sel sm_cur] in Hd. rewrite Hd in Ht. destruct Ht; discriminate. }
  cbn [sm_of sm_md sm_sel sm_cur] in Hrecs.
  rewrite Hall in Hp |- *. unfold r. rewrite Hmg in Hk |- *.
  change (md_magicless (dmode_of (dc_par (a_st a)))) with (md_magicless (dmode_w (dmode_of (dc_par (a_st a))))) in Hk |- *.
  apply (LHH4Model.lhh_hint_bound _ _ _ dsin recs hb (h_u a w) kk); auto.
  + rewrite Hout, app_nil_r. lia.
  + destruct (hb ++ h_u a w) as [|b l] eqn:Eh; [ | right; discriminate ].
    left. intros ->. destruct Hex as [Hex|Hex].
    * assert (Hl0: Zlength (ss_in (dc_ss (a_st a))) = Zlength dsin).
      { apply (f_equal (@Zlength Z)) in Hall. rewrite Zlength_app, app_nil_r in Hall.
        destruct (app_eq_nil _ _ Eh) as [Hhb Hu0].
        rewrite (Hnil Hhb), Hu0, Zlength_nil in Hlu.
        rewrite Zlength_sublist in Hall by lia. lia. }
      rewrite app_nil_r in Hex. lia.
    * rewrite app_nil_r in Hex. rewrite Hrecs in Hex. cbn [fst] in Hex. rewrite Hout in Hex. lia.
- intros _ _ E. rewrite Herr in E. discriminate.
Qed.


Lemma h_post : MF3 -> forall a w hb kk oc', lh_ctx a w hb ->
  get_frame_header_m (lh_mg (w_k w)) hb = FH_more kk -> Zlength (hb ++ h_u a w) < kk ->
  Zlength oc' = a_osz a -> sublist 0 (a_opos a) oc' = sublist 0 (a_opos a) (a_oc a) ->
  let r := lh_hint (lh_mg (w_k w)) (hb ++ h_u a w) kk in
  stream_post (a_st a) (hint_st a r) r (a_obf a) (a_osz a) (a_opos a) (a_opos a) (a_oc a) oc' (a_ibs a)
    (a_isz a) (a_ipos a) (a_isz a).
Proof.
intros HMF a w hb kk oc' Hc Hk Hlt Hoc Hpre r.
destruct (h_facts a w hb Hc) as (H0 & Hsin & Hnil & Hbu & Hlu & Hip & Hipc & Hibl & Hibb & Hstall).
pose proof (h_rng _ hb (h_u a w) kk Hk Hlt) as Hr. fold r in Hr.
pose proof (h_noerr r Hr) as Herr.
pose proof (h_claims HMF a w hb kk (if dc_stable (a_st a) then Some (a_osz a) else None) Hc Hk Hlt) as Hcl.
cbv zeta in Hcl. fold r in Hcl.
pose proof Hc as (Ha & _).
assert (Hb: 0 <= a_opos a <= a_osz a) by (unfold dsa_ok in Ha; tauto).
unfold stream_post.
exists nil, (if a_ipos a =? a_isz a then ss_stall (dc_ss (a_st a)) + 1 else 0), 0.
cbv zeta.
split; [ lia | ]. split; [ lia | ]. split; [ exact Hoc | ]. split; [ exact Hpre | ].
split; [ rewrite Zlength_nil; lia | ].
split; [ intros _; split; [ rewrite sublist_nil; reflexivity | constructor ] | ].
split; [ lia | ]. split; [ rewrite H0; lia | ]. split; [ left; lia | ].
split; [ intros E; discriminate | ].
split; [ unfold hint_st; reflexivity | ].
split; [ intros _ [E|E]; [ | lia ]; destruct (Z.eqb_spec (a_ipos a) (a_isz a)); [ lia | reflexivity ] | ].
split; [ intros _ E _; rewrite E, Z.eqb_refl; lia | ].
split; [ intros _ _; rewrite Z.sub_diag; unfold ZSTD_BLOCKSIZE_MAX; lia | ].
split; [ unfold stall_ok; intros [E|E]; rewrite E in Herr; discriminate | ].
split; [ exact Hcl | ].
(* stream_zero_ref: the hint is not 0 *)
intros ? _ _ _ E; lia.
Qed.


(* the progress claim of the hint return: in.pos := in.size, so no progress only with all the input read before;
   the header loaded so far is then incomplete (not a frame the model decodes), or empty at a frame boundary *)
Lemma h_prog : forall a w hb kk, lh_ctx a w hb ->
  get_frame_header_m (lh_mg (w_k w)) hb = FH_more kk -> Zlength (hb ++ h_u a w) < kk ->
  let r := lh_hint (lh_mg (w_k w)) (hb ++ h_u a w) kk in
  ep_prog_st a (hint_st a r) r (a_isz a) (a_opos a).
Proof.
intros a w hb kk Hc Hk Hlt r.
destruct (h_facts a w hb Hc) as (H0 & Hsin & Hnil & Hbu & Hlu & Hip & Hipc & Hibl & Hibb & Hstall).
pose proof (h_rng _ hb (h_u a w) kk Hk Hlt) as Hr. fold r in Hr.
pose proof (h_mg a w hb Hc) as Hmg.
pose proof Hc as (Ha & Hst & Hci & Hsmw & Hle & He & Hfp & Hdl & Hah & Hpend & Hentry).
pose proof Hci as (_ & _ & _ & _ & Hdll & _).
change (ep_prog a r (a_isz a) (a_opos a) 0 (if a_ipos a =? a_isz a then ss_stall (dc_ss (a_st a)) + 1 else 0)).
destruct (Z.eq_dec (a_ipos a) (a_isz a)) as [Ei|Ei]; [|apply ep_prog_moved; lia].
assert (Hopc: w_opc w = a_opos a) by (rewrite Hdl, Zlength_nil in Hdll; lia).
assert (Hipc': w_ipc w = a_isz a) by lia.
assert (X: ep_prog a r (a_isz a) (w_opc w) 0 (if a_ipos a =? a_isz a then ss_stall (dc_ss (a_st a)) + 1 else 0)).
{ apply (ep_prog_of a (w_k w) (w_sv w) (w_ipc w) (w_opc w) (w_oc w) (w_dl w)); auto.
  - rewrite H0, Hah, Hsin, Hipc', !Z.add_0_r, app_nil_r. reflexivity.
  - intros _ _ _. split; [intros E; lia|]. intros _. right.
    split; [exact Ei|]. split; [lia|]. right.
    destruct hb as [|b hb'].
    + right. split; [exact Hpend|]. split; [right; right; exact Hfp|].
      rewrite Hah, Hipc', <- Ei, sublist_nil, ?app_nil_r, ?app_nil_l, Hsin. lia.
    + left. exists (b :: hb'), kk. split; [exact Hfp|]. split; [discriminate|].
      rewrite <- Hmg. exact Hk. }
rewrite Hopc in X. exact X.
Qed.

(* ---------- the context after the hint return ---------- *)

Lemma h_kfacts : forall a w hb k v d1 did1 v',
  let k' := lh_k_load a w (k_A k v d1 did1) hb (a_isz a - w_ipc w) v' in
  c3_s k' = sf_lh (held_redict (c3_s k) (c3_dict k) d1) (Zlength hb + (a_isz a - w_ipc w))
              (hb_splice (sf_hbuf (c3_s k)) (Zlength hb) (h_u a w)) /\
  c3_par k' = c3_par k /\ c3_stable k' = c3_stable k /\ c3_set k' = c3_set k /\ c3_dict k' = d1 /\
  fs_fParams (c3_fs k') = v' /\ fs_ddictIsCold (c3_fs k') = fs_ddictIsCold (c3_fs k).
Proof.
intros. subst k'. unfold lh_k_load, h_u. replace (w_ipc w + (a_isz a - w_ipc w)) with (a_isz a) by lia.
repeat split; reflexivity.
Qed.

Lemma h_base : hs_probe_ok -> forall a w hb kk v tbl d1 did1 v' r, lh_ctx a w hb ->
  lhA_sel (w_k w) hb kk v tbl d1 did1 -> get_frame_header_m (lh_mg (w_k w)) hb = FH_more kk ->
  Zlength (hb ++ h_u a w) < kk -> fp_ok v' ->
  0 <= sf_held (c3_s (lh_k_load a w (k_A (w_k w) v d1 did1) hb (a_isz a - w_ipc w) v')) - local_held d1 ->
  base_rel3 (hint_st a r) (lh_k_load a w (k_A (w_k w) v d1 did1) hb (a_isz a - w_ipc w) v').
Proof.
intros Hpr a w hb kk v tbl d1 did1 v' r Hc Hsel Hk Hlt Hfpv Hheld.
destruct (h_facts a w hb Hc) as (H0 & Hsin & Hnil & Hbu & Hlu & Hip & Hipc & Hibl & Hibb & Hstall).
destruct (h_kfacts a w hb (w_k w) v d1 did1 v') as (Hs' & Hpar' & Hstab' & Hset' & Hdict' & Hfp' & Hcold').
pose proof Hc as (Ha & _ & Hci & _).
destruct Hci as (_ & _ & _ & _ & _ & _ & _ & Hbase & _ & Hnfp & _).
pose proof (h_dict_rel Hpr _ _ _ _ _ _ _ _ Hbase Hsel) as Hdr.
pose proof Hbase as (Hb1 & Hb2 & Hb3 & Hb4 & Hb5).
assert (Hbl: dc_bl (a_st a) = None) by (destruct Ha as (_ & _ & _ & _ & _ & _ & _ & (_ & _ & Hbl) & _); exact Hbl).
unfold base_rel3. rewrite Hpar', Hstab', Hset', Hdict'.
unfold hint_st. cbn [dc_stable dc_par dc_set dc_dict dc_ss dc_bl set_last set_ss].
split; [ exact Hb1 | ]. split; [ exact Hb2 | ]. split; [ exact Hb3 | ]. split; [ exact Hdr | ].
split; [ exact (proj1 Hb5) | ]. split; [ rewrite Hfp'; exact Hfpv | ]. split.
2: split; [ intros E; contradiction | ].
2: { assert (Hmc: mem_call (a_st a) (lh_k_load a w (k_A (w_k w) v d1 did1) hb (a_isz a - w_ipc w) v')).
     { apply (rl_mem_call_with _ (w_k w)); [ exact (proj2 (proj2 Hb5)) | exact (lhA_sel_redict _ _ _ _ _ _ _ Hsel) |
         reflexivity | exact (proj2 (rl_kA_held (w_k w) v d1 did1)) | exact Hheld ]. }
     mem_call_tac. }
split; [ intros _; exact Hnfp | ].
intros E. exfalso. pose proof (f_equal ss_in E) as E1. pose proof (f_equal ss_stall E) as E3.
  unfold ss_init in E1, E3. cbn [ss_in ss_stall] in E1, E3.
  destruct (Z.eqb_spec (a_ipos a) (a_isz a)) as [Ei|Ei]; [ lia | ].
  apply (f_equal (@Zlength Z)) in E1. rewrite H0, !Z.add_0_r in E1.
  rewrite Zlength_app, Zlength_sublist, Zlength_nil in E1 by lia.
  pose proof (Zlength_nonneg (ss_in (dc_ss (a_st a)))). lia.
Qed.


Lemma h_SR : MF3 -> hs_probe_ok -> forall a w hb kk v tbl d1 did1 r' v' r, lh_ctx a w hb ->
  lhA_sel (w_k w) hb kk v tbl d1 did1 -> get_frame_header_m (lh_mg (w_k w)) hb = FH_more kk ->
  Zlength (hb ++ h_u a w) < kk ->
  fh_post_m (lh_mg (w_k w)) (hb ++ h_u a w) r' v v' ->
  get_frame_header_m (lh_mg (w_k w)) (hb ++ h_u a w) <> FH_err ->
  SR3 (a_gv a) (hint_st a r) (lh_k_load a w (k_A (w_k w) v d1 did1) hb (a_isz a - w_ipc w) v').
Proof.
intros HMF Hpr a w hb kk v tbl d1 did1 r' v' r Hc Hsel Hk Hlt Hfh2 Hne2.
destruct (h_facts a w hb Hc) as (H0 & Hsin & Hnil & Hbu & Hlu & Hip & Hipc & Hibl & Hibb & Hstall).
destruct (h_kfacts a w hb (w_k w) v d1 did1 v') as (Hs' & Hpar' & Hstab' & Hset' & Hdict' & Hfp' & Hcold').
set (k' := lh_k_load a w (k_A (w_k w) v d1 did1) hb (a_isz a - w_ipc w) v') in *.
set (u := h_u a w) in *.
pose proof (LHH4Model.lhh_more_le18 _ hb kk Hk) as Hk18.
assert (Hx: hdr_lenok (lh_mg (w_k w)) (hb ++ u)).
{ pose proof (mf_hdr_more_ext HMF _ hb u kk Hbu Hk ltac:(lia)) as Hx.
  unfold hdr_lenok. destruct (get_frame_header_m _ (hb ++ u)); auto. }
assert (Hmore: exists k0, get_frame_header_m (lh_mg (w_k w)) (hb ++ u) = FH_more k0).
{ apply (LHH4Model.lhh_more_ext _ hb u kk Hbu Hk Hlt Hne2).
  intros h G. unfold hdr_lenok in Hx. rewrite G in Hx. exact Hx. }
assert (Hv': v' = v \/ v' = fh_val fh_zero).
{ destruct Hmore as [k0 Hk0]. unfold fh_post_m in Hfh2. rewrite Hk0 in Hfh2. destruct Hfh2 as [_ ->].
  destruct (_ <? _); auto. }
pose proof Hc as (Ha & Hst & Hci & Hsmw & Hle & He & Hfp & Hdl & Hah & Hpend & Hentry & Hunt).
destruct Hci as (Hipc0 & Hopc & Hloc & Hpre & Hdll & Hdlc & Hdlb & Hbase & Hsinb & Hnfp1 & Hnfp2 & Hnfp0 & Hcore &
                 Hddok & Hstout & Hahd & Hblk & Halive & Hlh & Hsin2 & Hexp & HTf).
destruct He as (Hst1 & Hlh' & H18 & Hbo & Hsub & Hhost & HinPos & Hos & Hoe & Hipc' & Hopc' & Hlo & Hsmw' & Hbase' & Hlenok).
destruct Hcore as (_ & Hcold & Hsz & _).
assert (Hopos: dc_stable (a_st a) = true -> a_opos a = Zlength (ss_out (dc_ss (a_st a)))) by (unfold dsa_ok in Ha; tauto).
assert (Hmg: md_magicless (sm_md (sm_of (a_st a))) = lh_mg (w_k w)).
{ unfold lh_mg. cbn. destruct Hbase as (_ & Hpar & _). rewrite Hpar. reflexivity. }
exists {| sv_fp := FP_hdr (hb ++ u); sv_pend := nil; sv_ahead := nil; sv_lay := sv_lay (w_sv w);
          sv_dd := sv_dd (w_sv w) |}.
unfold hint_st.
cbn [dc_stable dc_par dc_set dc_dict dc_ss dc_bl set_last set_ss ss_in ss_out ss_stall ss_err ss_obuf ss_ahead ss_calls
     sv_fp sv_pend sv_ahead sv_lay sv_dd].
split; [ | split; [ | split; [ | split ] ] ].
- (* c_rel *)
  unfold c_rel. cbv zeta.
  cbn [dc_stable dc_par dc_set dc_dict dc_ss dc_bl set_last set_ss ss_in ss_out ss_stall ss_err ss_obuf ss_ahead ss_calls
       sv_fp sv_pend sv_ahead sv_lay sv_dd].
  rewrite Hs', Hpar'. unfold sf_lh, held_redict, sf_with_held.
  cbn [sf_stage sf_hostage sf_inPos sf_outStart sf_outEnd sf_lhSize sf_hbuf sf_inSize sf_outSize sf_nfp sf_expOut].
  split; [ destruct (a_ipos a =? a_isz a); lia | ].
  split; [ exact Hnfp1 | ].
  split; [ right; right; split; [ exact Hst1 | ]; destruct Hmore as [k0 Hk0]; exists (hb ++ u), k0; auto | ].
  split; [ intros E; rewrite Hst1 in E; discriminate | ].
  split; [ intros Hs1 _; exists (a_obf a), (a_osz a); rewrite Hs1; split; [ reflexivity | ];
           rewrite (Hexp Hs1 ltac:(rewrite Hst1; discriminate)), app_nil_r, <- (Hopos Hs1); reflexivity | ].
  split; [ auto | ].
  split; [ unfold sv_dd_ok; rewrite Hs'; unfold sf_lh, held_redict, sf_with_held; cbn [sf_stage]; rewrite Hst1; unfold zdss_read, zdss_loadHeader; lia | ].
  unfold c_core. rewrite Hs', Hpar', Hcold'. unfold sf_lh, held_redict, sf_with_held.
  cbn [sf_stage sf_hostage sf_inPos sf_outStart sf_outEnd sf_lhSize sf_hbuf sf_inSize sf_outSize sv_fp sv_pend sv_ahead].
  rewrite Hst1. split; [ right; left; auto | ]. split; [ exact Hcold | ]. split; [ exact Hsz | ].
  unfold zdss_init, zdss_loadHeader. change (1 =? 0) with false. change (1 =? 1) with true. cbv beta iota.
  split; [ auto | ]. split; [ exact Hhost | ]. split; [ exact HinPos | ]. split; [ exact Hos | ].
  split; [ exact Hoe | ].
  exists (hb ++ u). split; [ auto | ]. split; [ lia | ].
  split; [ exact Hbu | ].
  split; [ rewrite Zlength_app, Hlu; auto | ].
  split; [ | exact Hx ].
  unfold hb_splice. rewrite Hsub, map_app, app_assoc.
  replace (Zlength (hb ++ u)) with (Zlength (zbytes hb ++ zbytes u)) by (rewrite !Zlength_app, !Zlength_map; auto).
  rewrite sublist0_app1 by (split; [ apply Zlength_nonneg | rewrite !Zlength_app, !Zlength_map; lia ]).
  apply sublist_same; auto.
- (* bytes *)
  rewrite H0, !Z.add_0_r, <- Hsin. unfold bytes_ok in *. apply Forall_app; split; auto. apply Forall_sublist; auto.
- rewrite Zlength_nil. reflexivity.
- exists (ss_in (dc_ss (a_st a)) ++ sublist (a_ipos a + ss_ahead (dc_ss (a_st a))) (a_isz a + 0) (a_ibs a)).
  rewrite app_nil_r. reflexivity.
- (* the model *)
  unfold alive_ok. rewrite H0, !Z.add_0_r.
  assert (Hsm: forall x y, sm_of (set_last (set_ss (a_st a) x) y) = sm_of (a_st a)) by reflexivity.
  rewrite !Hsm.
  destruct (h_split HMF a w hb Hc) as [Hd | (dsin & recs & cd & Bd & Hrecs & Hcur & Hall & Hout & Hcd)].
  + left. exact Hd.
  + right. exists cd. split; [ | split ].
    * exists dsin, (hb ++ u), recs. split; [ exact Hall | ]. split; [ exact Hrecs | ].
      split; [ exact Hcur | ]. split; [ cbn [cur_rel]; split; [ reflexivity | rewrite Hmg; exact Hx ] | ].
      cbn [fp_content]. rewrite !app_nil_r. exact Hout.
    * cbn [next_cd].
      apply (h_cd Hpr (a_st a) (w_k w) hb kk v tbl d1 did1 cd k'); auto.
      -- intro E. rewrite <- Hcur. unfold series_cur, sm_of. cbn [sm_sel sm_cur]. rewrite E. cbn [fst snd].
         apply h_walk_cur_none.
    * unfold hist_ok. intros _ _ Hne'. exfalso. apply Hne'. rewrite Hs'. unfold sf_lh, held_redict, sf_with_held. cbn [sf_stage]. exact Hst1.
Qed.

(* ---------- the return ---------- *)

Lemma h_ctx_valid : forall DENT TABS (gv: globals) (p: val) (k: cst3),
  TABS_OK TABS -> ctx_rep3 DENT TABS gv p k |-- valid_pointer p.
Proof.
intros DENT TABS gv p k HT. unfold ctx_rep3, ctx_body3, fgroup3, tabs_rep. normalize.
assert (V: field_at_ Ews t_dctx (DOT _LLTptr) p |-- valid_pointer p)
  by (apply field_at_valid_ptr0; auto; reflexivity).
destruct (c3_tabs k) as [lxb|ox ts].
- unfold tables_uninit.
  apply (derives_trans _ (field_at_ Ews t_dctx (DOT _LLTptr) p * TT)); [cancel | ].
  apply sepcon_valid_pointer1. exact V.
- sep_apply (HT gv p ox ts). unfold tables_uninit.
  apply (derives_trans _ (field_at_ Ews t_dctx (DOT _LLTptr) p * TT)); [cancel | ].
  apply sepcon_valid_pointer1. exact V.
Qed.

Lemma h_DC : forall DENT TABS BR (gv: globals) (p: val) (k: cst3) (st: dctx_st),
  TABS_OK TABS -> base_rel3 st k -> SR3 gv st k -> dc_bl st = None ->
  ctx_rep3 DENT TABS gv p k |-- DC3x DENT TABS SR3r BR gv p st && valid_pointer p.
Proof.
intros DENT TABS BR gv p k st HT Hb HS Hbl.
apply andp_right; [| apply h_ctx_valid; auto].
unfold DC3x, DC3_of. Exists k. apply andp_right; [| apply derives_refl].
apply prop_right. split; [exact Hb|]. split; [|split].
- intros _ _; left; exact HS.
- intros ba H; congruence.
- (* the relational post makes no exact claim *)
  intros _ _ _. exact I.
Qed.

(* the allocator's bytes besides the context, the stream buffer and the local DDict: nonnegative (the set's) *)
Lemma h_held : forall DENT TABS a w' ip,
  PROPx [] (LOCALx (ds_LI_L a w') (SEPx (ds_S_ip DENT TABS a w' ip))) |--
    !! (0 <= sf_held (c3_s (w_k w')) - local_held (c3_dict (w_k w'))).
Proof.
intros. unfold ds_S_ip. go_lowerx. sep_apply rl_ctx_held. entailer!.
Qed.

Lemma lh_hint_ok : lh_hint_stmt.
Proof.
intros HMF Hpr DENT TABS BR a w hb r ipos' w' HT Hc Hr0 Hrc.
destruct Hrc as (kk & v & tbl & d1 & did1 & r' & v' & Hsel & Hk & Hlt0 & Hfh2 & Hne2 & Hfpv & -> & -> & ->).
destruct (h_facts a w hb Hc) as (Hah0 & Hsin & Hnil & Hbu & Hlu & Hip & Hipc & Hibl & Hibb & Hstall).
fold (h_u a w) in *.
assert (Hlt: Zlength (hb ++ h_u a w) < kk) by (rewrite Zlength_app; lia).
set (r := lh_hint (lh_mg (w_k w)) (hb ++ h_u a w) kk) in *.
unfold lh_ret_goal.
eapply derives_trans; [ apply andp_right; [ apply h_held | apply derives_refl ] | ].
apply derives_extract_prop. intros Hheld. cbn [w_k lw_k] in Hheld.
set (k' := lh_k_load a w (k_A (w_k w) v d1 did1) hb (a_isz a - w_ipc w) v') in *.
pose proof Hc as (Ha & _ & Hci & _).
destruct Hci as (_ & _ & Hloc & Hpre & _).
pose proof (h_post HMF a w hb kk (w_oc w) Hc Hk Hlt Hloc Hpre) as Hpost. fold r in Hpost.
pose proof (h_prog a w hb kk Hc Hk Hlt) as Hprog. fold r in Hprog.
change (stream_progress (a_st a) (hint_st a r) r (a_osz a) (a_opos a) (a_opos a) (a_isz a) (a_ipos a) (a_isz a)
          (a_ibs a)) in Hprog.
pose proof (h_base Hpr a w hb kk v tbl d1 did1 v' r Hc Hsel Hk Hlt Hfpv Hheld) as Hbase. fold k' in Hbase.
pose proof (h_SR HMF Hpr a w hb kk v tbl d1 did1 r' v' r Hc Hsel Hk Hlt Hfh2 Hne2) as HSR. fold k' in HSR.
assert (Hbl: dc_bl (hint_st a r) = None)
  by (destruct Ha as (_ & _ & _ & _ & _ & _ & _ & (_ & _ & Hbl) & _); exact Hbl).
(* nothing was delivered (w_opc = a_opos): the output cells are the caller's *)
assert (Hun: stream_untouched (a_st a) r (a_osz a) (a_opos a) (a_oc a) (w_oc w)).
{ pose proof Hc as (_ & _ & Hci' & _ & _ & _ & _ & Hdl & _ & _ & _ & Hunt).
  pose proof Hci' as (_ & _ & _ & _ & Hdll & _).
  rewrite Hdl, Zlength_nil in Hdll.
  intros Hs _. replace (a_opos a) with (w_opc w) by lia. exact (Hunt Hs). }
unfold lh_ret_goal, ds_R, RA_return, frame_ret_assert, function_body_ret_assert.
unfold ds_LI_L, ds_S_ip, ds_post, stackframe_of; simpl fn_vars.
unfold lw_k; cbn [w_k w_opc w_oc w_ipc w_smw].
go_lowerx.
sep_apply (h_DC DENT TABS BR (a_gv a) (a_d a) k' (hint_st a r) HT Hbase HSR Hbl).
unfold liftx, lift; simpl.
Exists r (a_opos a) (a_isz a) (w_oc w) (hint_st a r).
unfold var_block, eval_lvar; simpl.
unfold lvar_denote in H0.
destruct (Map.get (ve_of rho) _op) as [[b t]|] eqn:E; [|contradiction].
destruct H0 as [<- ->].
unfold liftx, lift; simpl. rewrite E. simpl.
sep_apply (data_at_data_at_ Tsh (tptr tschar) (offset_val (w_opc w) (a_ob a)) (Vptr b Ptrofs.zero)).
rewrite data_at__memory_block. entailer!.
apply derives_refl.
Qed.

End CM_LH3Hint_1.
