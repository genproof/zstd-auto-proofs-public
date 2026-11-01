(* FS3 one-shot frames: ZSTD_decompressMultiFrame's body against ZSTD_decompressMultiFrame_spec3, with
   ZSTD_decompressFrame_spec3 (port of v2 body_multiframe.v). *)
Require Import Zstd.proof.dec.v3.FS.frames.Frames3Spec Zstd.proof.dec.v3.FS.frames.Frames3Series.
Require Import Zstd.proof.dec.v3.FS.frames.Multi3Probe Zstd.proof.dec.v3.FS.frames.Multi3FD Zstd.proof.dec.v3.FS.frames.Multi3Split.
Require Import Zstd.proof.zstd.NullBufOk.
Require Import Zstd.proof.dec.v3.FS.frames.Frames3Model Zstd.proof.dec.v3.FS.frames.Multi3Aux Zstd.proof.dec.v3.FS.frames.Multi3QV Zstd.proof.dec.v3.FS.frames.Multi3Pp.
Require Import Zstd.proof.dec.v3.FS.frames.Multi3Codes.
Require Import Zstd.proof.model.ExHuf Zstd.proof.model.ExBlock Zstd.proof.model.ExFrame Zstd.proof.model.Exact.
Require Zstd.proof.model.ExOneshot.
Local Open Scope logic.

Section CM_Multi3_body_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* G1: a local darg is not in the set (msel_ok's last conjunct) *)
Lemma mf_gap_G1: forall W d l a shk shd cap dst,
  msel_ok W d l a shk shd cap dst -> darg_local d a = true -> ~ In (darg_ddict a) (map fst l).
Proof. intros W d l a shk shd cap dst H. apply H. Qed.

Definition dg_fields (p: val) (d: dfields) : mpred :=
  field_at Ews t_dctx (DOT _ddictLocal) (df_local d) p *
  field_at Ews t_dctx (DOT _ddict) (df_ddict d) p *
  field_at Ews t_dctx (DOT _dictUses) (Vint (Int.repr (df_uses d))) p.

(* the DDict argument's struct, for ZSTD_DDict_dictContent / dictSize (in dgroup when it is the local one) *)
Lemma mf_struct: forall DENT gv p pr sp d l tbl shk a W shd cap dst x buf sh am hb,
  a = DA_ddict x buf sh -> (sel_on pr sp = true -> msel_ok W d l a shk shd cap dst) ->
  exists K: mpred,
    (msel_res DENT gv p pr sp d l tbl shk a am hb * darg_res3 DENT gv pr sp d a |-- ddict_struct x buf * K) /\
    (ddict_struct x buf * K |-- msel_res DENT gv p pr sp d l tbl shk a am hb * darg_res3 DENT gv pr sp d a).
Proof.
  intros DENT gv p pr sp d l tbl shk a W shd cap dst x buf sh am hb -> Hok.
  unfold darg_res3, msel_res. destruct (sel_on pr sp) eqn:Hs; cbn [andb].
  - destruct (darg_local d (DA_ddict x buf sh)) eqn:Hl.
    + destruct (Hok eq_refl) as (_ & _ & Hloc & _). destruct (Hloc Hl) as (x' & buf' & sh' & E & Hlx).
      inversion E; subst x' buf' sh'. clear E.
      unfold darg_local in Hl. apply andb_prop in Hl. destruct Hl as [Hq Hn].
      unfold veqb in Hq, Hn. destruct (Val.eq _ _) as [Eq|]; [|discriminate]. simpl darg_ddict in Eq.
      destruct (Val.eq (df_local d) nullval); [discriminate|].
      exists (mem_mgr gv * dg_fields p d *
        (DENT gv (dx_q x) (ddx_ent x) * ddict_mem x buf * ddict_pad (dx_q x)) * cm_have am (hb + local_held d) *
        hset_tbl am sp l tbl *
        set_full DENT gv shk l (darg_ddict (DA_ddict x buf sh)) *
        (if ddx_copied x then emp else bytes_at sh (dx_bytes x) buf)).
      unfold dgroup, dg_fields, local_rep. rewrite Hlx. rewrite if_false by auto.
      split; unfold ddict_rep_at; Intros; entailer!.
    + exists (mem_mgr gv * dgroup DENT gv p d * cm_have am (hb + local_held d) * hset_tbl am sp l tbl * set_full DENT gv shk l (darg_ddict (DA_ddict x buf sh)) *
        (DENT gv (dx_q x) (ddx_ent x) * ddict_mem x buf * ddict_pad (dx_q x)) *
        (if ddx_copied x then emp else bytes_at sh (dx_bytes x) buf)).
      unfold darg_res, ddict_rep_at. split; cancel.
  - exists ((DENT gv (dx_q x) (ddx_ent x) * ddict_mem x buf * ddict_pad (dx_q x)) *
        (if ddx_copied x then emp else bytes_at sh (dx_bytes x) buf)).
    unfold darg_res, ddict_rep_at. split; cancel.
Qed.

Lemma mf_sp_pon: forall DENT gv p pr sp dcur l tbl shk a am hb, dp_multi pr = 1 ->
  msel_res DENT gv p pr sp dcur l tbl shk a am hb |-- !! is_pointer_or_null sp.
Proof.
  intros. unfold msel_res, sel_on. rewrite H. cbn [Z.eqb Pos.eqb andb].
  destruct (veqb sp nullval) eqn:E; cbn [negb].
  - apply veqb_true in E. subst. entailer!.
  - unfold hset_tbl. Intros tp. entailer!.
Qed.

(* uninitialised tables, litExtraBuffer holding lxb *)
Lemma tabs_rep_uninit_intro: forall TABS gv p lxb, tables_uninit p lxb |-- tabs_rep TABS gv p (TUninit lxb).
Proof. intros. apply derives_refl. Qed.

(* ZSTD_decompressMultiFrame treats the tables as uninitialised (every frame begins them): litExtraBuffer keeps
   its bytes *)
Lemma fgroup3_uninit: forall TABS gv p fs t pr sp, TABS_OK TABS ->
  fgroup3 TABS gv p fs t pr sp |-- fgroup3 TABS gv p fs (TUninit (tabs_lxb t)) pr sp.
Proof.
  intros TABS gv p fs t pr sp HT. unfold fgroup3. destruct t as [lxb | ox ts]; [apply derives_refl |].
  cbn [tabs_rep tabs_lxb]. Intros. sep_apply (HT gv p ox ts).
  apply andp_right; [apply prop_right; auto | cancel].
Qed.

(* the claims of the spec from the body's oneshot_g *)
Definition mf_DS2 (l: list (val * ddict_st)) (tbl: list val) (fs1: fstate) (dcur: dfields) : Prop :=
  exists id, fp_dictID (fs_fParams fs1) = Vint (Int.repr id) /\ 0 <= id <= Int.max_unsigned /\
    (hs_probe l tbl id = nullval \/ hs_probe l tbl id = df_ddict dcur).

(* ---------- the exact result (model/Exact.v's os_res) along the loop ---------- *)

Local Notation XF := (x_frame xstate (xst_begin xhuf) xblock).

(* without a dictionary and with the default parameters: the output so far is the bytes acc, and os_res of all of
   s is what the model gives for the rest of s after acc (model/ExOneshot.v's xs_rest) *)
Definition mf_x (a: darg) (pr: dparams) (s: list Z) (cap off u: Z) (oc: list val) : Prop :=
  a = DA_none -> pr = dparams_dflt -> exists acc, Zlength acc = u /\ sublist 0 u oc = zbytes acc /\
    os_res s cap = ExOneshot.xs_rest (sublist off (Zlength s) s) cap acc.

Lemma skipn_sublist_end: forall (s: list Z) off k, 0 <= off <= Zlength s -> 0 <= k <= Zlength s - off ->
  skipn (Z.to_nat k) (sublist off (Zlength s) s) = sublist (off + k) (Zlength s) s.
Proof.
  intros s off k Ho Hk. unfold sublist. rewrite Zlength_correct in *.
  rewrite !firstn_same by (rewrite ?skipn_length; lia). rewrite skipn_skipn. f_equal. lia.
Qed.

Lemma mf_x_init: forall a pr s cap oc, mf_x a pr s cap 0 0 oc.
Proof.
  intros a pr s cap oc _ _. exists nil. split; [reflexivity |]. split; [rewrite sublist_nil; reflexivity |].
  rewrite sublist_same by lia. apply ExOneshot.os_res_rest.
Qed.

(* a skippable frame of r bytes *)
Lemma mf_x_skip: forall a pr s cap off u oc r, mf_x a pr s cap off u oc ->
  bytes_ok s -> 0 <= off -> ZSTD_FRAMEHEADERSIZE_PREFIX <= Zlength s - off ->
  is_skippable_magic (le_field (sublist off (Zlength s) s) 0 4) = true ->
  skippable_frame_size (sublist off (Zlength s) s) = Some r -> 0 <= r <= Zlength s - off ->
  mf_x a pr s cap (off + r) u oc.
Proof.
  intros a pr s cap off u oc r H Hb Ho Hl Hm Hk Hr Ha Hp. destruct (H Ha Hp) as (acc & H1 & H2 & H3).
  exists acc. split; [exact H1 | split; [exact H2 |]]. rewrite H3.
  rewrite ExOneshot.xs_rest_skip by (try apply bytes_ok_sublist; auto; rewrite Zlength_sublist by lia; lia).
  rewrite Hk. rewrite skipn_sublist_end by lia. reflexivity.
Qed.

(* readSkippableFrameSize's error *)
Lemma mf_x_skip_err: forall a pr s cap off u oc, mf_x a pr s cap off u oc ->
  bytes_ok s -> 0 <= off -> ZSTD_FRAMEHEADERSIZE_PREFIX <= Zlength s - off ->
  is_skippable_magic (le_field (sublist off (Zlength s) s) 0 4) = true ->
  skippable_frame_size (sublist off (Zlength s) s) = None ->
  a = DA_none -> pr = dparams_dflt -> os_res s cap = None.
Proof.
  intros a pr s cap off u oc H Hb Ho Hl Hm Hk Ha Hp. destruct (H Ha Hp) as (acc & H1 & H2 & H3).
  assert (off <= Zlength s) by (unfold ZSTD_FRAMEHEADERSIZE_PREFIX in Hl; lia).
  rewrite H3.
  rewrite ExOneshot.xs_rest_skip by (try apply bytes_ok_sublist; auto; rewrite Zlength_sublist by lia; lia).
  rewrite Hk. reflexivity.
Qed.

(* a Zstandard frame that the model refuses, decoded from any state with a full-size litExtraBuffer *)
Lemma mf_x_frame_err: forall a pr s cap off u oc st, mf_x a pr s cap off u oc ->
  bytes_ok s -> 0 <= off -> ZSTD_FRAMEHEADERSIZE_PREFIX <= Zlength s - off ->
  is_skippable_magic (le_field (sublist off (Zlength s) s) 0 4) = false ->
  ExOneshot.lxb_ok st -> XF st (sublist off (Zlength s) s) (cap - u) = None ->
  a = DA_none -> pr = dparams_dflt -> os_res s cap = None.
Proof.
  intros a pr s cap off u oc st H Hb Ho Hl Hm Hst Hf Ha Hp. destruct (H Ha Hp) as (acc & H1 & H2 & H3).
  assert (off <= Zlength s) by (unfold ZSTD_FRAMEHEADERSIZE_PREFIX in Hl; lia).
  rewrite H3. apply (ExOneshot.xs_rest_frame_err st); auto;
    [apply bytes_ok_sublist; auto | rewrite Zlength_sublist by lia; lia | rewrite H1; exact Hf].
Qed.

(* a Zstandard frame of k bytes that the model decodes into c, written as the r = |c| bytes oc' *)
Lemma mf_x_frame: forall a pr s cap off u oc r oc' k,
  mf_x a pr s cap off u oc -> bytes_ok s -> 0 <= off -> 0 <= k <= Zlength s - off -> 0 <= u -> Zlength oc >= u ->
  r <= Zlength oc' ->
  (a = DA_none -> pr = dparams_dflt -> ZSTD_FRAMEHEADERSIZE_PREFIX <= Zlength s - off /\
     is_skippable_magic (le_field (sublist off (Zlength s) s) 0 4) = false /\
     exists st c st', ExOneshot.lxb_ok st /\ XF st (sublist off (Zlength s) s) (cap - u) = Some (c, k, st') /\
       Zlength c = r /\ sublist 0 r oc' = zbytes c) ->
  mf_x a pr s cap (off + k) (u + r) (sublist 0 u oc ++ oc').
Proof.
  intros a pr s cap off u oc r oc' k H Hb Ho Hk Hu Hoc Hr Hf Ha Hp.
  destruct (H Ha Hp) as (acc & H1 & H2 & H3).
  destruct (Hf Ha Hp) as (Hl & Hm & st & c & st' & Hst & Hx & Hc1 & Hc2).
  assert (off <= Zlength s) by (unfold ZSTD_FRAMEHEADERSIZE_PREFIX in Hl; lia).
  exists (acc ++ c). split; [rewrite Zlength_app; lia |].
  split; [apply bytes_step; auto |].
  rewrite H3. rewrite (ExOneshot.xs_rest_frame_res st _ _ _ c k st');
    [| apply bytes_ok_sublist; auto | rewrite Zlength_sublist by lia; lia | auto | auto | rewrite H1; exact Hx].
  rewrite skipn_sublist_end by lia. reflexivity.
Qed.

(* the loop's end (fewer than 5 bytes left): the series' end iff nothing is left *)
Lemma mf_x_end: forall a pr s cap off u oc, mf_x a pr s cap off u oc ->
  0 <= off <= Zlength s -> Zlength s - off < ZSTD_FRAMEHEADERSIZE_PREFIX -> a = DA_none -> pr = dparams_dflt ->
  (off = Zlength s -> os_match s cap u oc) /\ (off <> Zlength s -> os_res s cap = None).
Proof.
  intros a pr s cap off u oc H Ho Hl Ha Hp. destruct (H Ha Hp) as (acc & H1 & H2 & H3).
  rewrite ExOneshot.xs_rest_end in H3 by (rewrite Zlength_sublist by lia; lia).
  rewrite Zlength_sublist in H3 by lia. split; intros E.
  - unfold os_match. rewrite H3. replace (Zlength s - off =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
    split; auto.
  - rewrite H3. replace (Zlength s - off =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.

Lemma os_match_err: forall s cap r out, os_res s cap = None -> is_error_code r = true -> os_match s cap r out.
Proof. intros s cap r out E He. unfold os_match. rewrite E. exact He. Qed.

(* the loop's pure invariant: at src offset off, u bytes written into oc, the frame fields fs1, moreThan1Frame m,
   the variable `ddict` qv, the context's dictionary fields dcur *)
Record mf_pi (pr: dparams) (sp: val) (d: dfields) (l: list (val * ddict_st)) (tbl: list val) (shk: share)
    (a: darg) (fs: fstate) (s: list Z) (cap: Z) (off u: Z) (oc: list val) (fs1: fstate) (m: Z) (qv: val)
    (dcur: dfields) : Prop := {
  mi_off: 0 <= off <= Zlength s;
  mi_u: 0 <= u <= cap;
  mi_oc: Zlength oc = cap;
  mi_m: m = 0 \/ m = 1;
  mi_acc: exists acc, bytes_ok acc /\ Zlength acc = u /\ sublist 0 u oc = zbytes acc;
  mi_ser: series_inv (dmode_of pr) (mf_sel pr sp a l tbl) (darg_model a) (darg_model (mf_dict a l shk qv)) s off u oc;
  mi_cur: darg_model a <> None -> darg_model (mf_dict a l shk qv) <> None;
  mi_qv: qv_ok pr sp a l qv;
  mi_dc: dc_ok pr sp l d dcur;
  mi_loc: darg_local d a = true -> qv = darg_ddict a -> dcur = d;
  mi_fp: fp_ok (fs_fParams fs) -> fp_ok (fs_fParams fs1);
  mi_ds2: m = 1 -> sel_on pr sp = true -> df_ddict d <> nullval -> mf_DS2 l tbl fs1 dcur;
  mi_m0: m = 0 -> off = 0 \/ (forall h, get_frame_header_m (dp_fmt pr =? 1) s = FH_ok h -> fh_frameType h <> 0);
  mi_d0: m = 0 -> dcur = d;
  (* a single frame of all of s was decoded at once, with the selection of its Dictionary_ID *)
  mi_sf: m = 1 -> sel_on pr sp = true ->
    frame_compressed_size_m (dp_fmt pr =? 1) s = Some (Zlength s) ->
    forall h, get_frame_header_m (dp_fmt pr =? 1) s = FH_ok h -> fh_frameType h = 0 ->
      (off = Zlength s) /\ (dcur = d \/ (exists q, In q (map fst l) /\ dcur = switch_fields q /\ q = hs_probe l tbl (fh_dictID h)));
  (* the error codes (Multi3Codes) *)
  mi_codes: darg_model a <> None ->
    codes_inv (dmode_of pr) (mf_sel pr sp a l tbl) (darg_model a) (darg_model (mf_dict a l shk qv)) s off u;
  (* nothing is written before the first frame; a single frame of all of s that declares its content size wrote
     exactly that many bytes (ZSTD_decompressFrame's end check) *)
  mi_u0: m = 0 -> u = 0;
  mi_cs: m = 1 -> frame_compressed_size_m (dp_fmt pr =? 1) s = Some (Zlength s) ->
    forall h, get_frame_header_m (dp_fmt pr =? 1) s = FH_ok h -> fh_frameType h = 0 ->
      off = Zlength s /\ (fh_contentSize h <> ZSTD_CONTENTSIZE_UNKNOWN -> u = fh_contentSize h);
  (* the exact result (mf_x) *)
  mi_x: mf_x a pr s cap off u oc }.

Lemma mf_pi_skip: forall pr sp d l tbl shk a fs s cap off u oc fs1 m qv dcur r,
  mf_pi pr sp d l tbl shk a fs s cap off u oc fs1 m qv dcur ->
  dp_fmt pr = 0 -> bytes_ok s -> ZSTD_FRAMEHEADERSIZE_PREFIX <= Zlength s - off ->
  is_skippable_magic (le_field (sublist off (Zlength s) s) 0 4) = true ->
  skippable_frame_size (sublist off (Zlength s) s) = Some r -> 8 <= r <= Zlength s - off ->
  mf_pi pr sp d l tbl shk a fs s cap (off + r) u oc fs1 m qv dcur.
Proof.
  intros pr sp d l tbl shk a fs s cap off u oc fs1 m qv dcur r HI E0 Hb Hl Hm Hk Hr.
  destruct HI as [Hoff Hu Hoc Hm0 Hacc Hser Hcur Hqv Hdc Hloc Hfp Hds2 Hmm Hd0 Hsf Hcd Hu0 Hcfs Hx].
  constructor; auto; try lia.
  - eapply series_inv_skip; eauto; [unfold dmode_of; cbn [md_magicless]; rewrite E0; reflexivity | lia].
  - intros Hm1. right. destruct (Hmm Hm1) as [-> | H]; auto.
    intros h Hh. rewrite E0 in Hh. apply (gfh_skip_type s h); auto.
    rewrite sublist_same in Hm by lia. exact Hm.
  - intros Hm1 Hs Hf h Hh Ht. destruct (Hsf Hm1 Hs Hf h Hh Ht) as [E _]. unfold ZSTD_FRAMEHEADERSIZE_PREFIX in Hl. lia.
  - intros Hn. eapply codes_inv_skip; eauto; try lia; try reflexivity.
    unfold dmode_of; cbn [md_magicless]; rewrite E0; reflexivity.
  - intros Hm1 Hf h Hh Ht. destruct (Hcfs Hm1 Hf h Hh Ht) as [E _]. unfold ZSTD_FRAMEHEADERSIZE_PREFIX in Hl. lia.
  - exact (mf_x_skip a pr s cap off u oc r Hx Hb ltac:(lia) Hl Hm Hk ltac:(lia)).
Qed.



Lemma mf_post: forall pr sp a l tbl s cap r out,
  oneshot_g (dmode_of pr) (mf_sel pr sp a l tbl) (darg_model a) s cap r out ->
  (darg_ddict a <> nullval -> darg_model a <> None) ->
  (sel_on pr sp = false \/ darg_ddict a = nullval -> oneshot_ok (dmode_of pr) (darg_model a) s cap r out) /\
  (sel_on pr sp = true -> darg_ddict a <> nullval ->
     oneshot_sel (dmode_of pr) (psel l tbl) (darg_model a) s cap r out).
Proof.
  intros pr sp a l tbl s cap r out H Hm. unfold mf_sel in H. split.
  - intros Hc. apply oneshot_g_ok.
    replace (andb (sel_on pr sp) (negb (veqb (darg_ddict a) nullval))) with false in H; [exact H|].
    destruct Hc as [-> | ->]; [reflexivity|]. unfold veqb. destruct (Val.eq nullval nullval); [|congruence].
    destruct (sel_on pr sp); reflexivity.
  - intros Hs Hn. apply oneshot_g_sel; [| auto].
    rewrite Hs in H. replace (negb (veqb (darg_ddict a) nullval)) with true in H; [exact H|].
    unfold veqb. destruct (Val.eq (darg_ddict a) nullval); [contradiction | reflexivity].
Qed.

(* the postcondition's facts after an error return *)
Lemma mf_err_post: forall pr sp a l tbl s cap r out (fs1: fstate) (d dcur: dfields),
  is_error_code r = true -> dec_err r -> series_err (dmode_of pr) (mf_sel pr sp a l tbl) (darg_model a) s cap ->
  (darg_ddict a <> nullval -> darg_model a <> None) ->
  (is_error_code r = false -> r <= cap) /\
  (sel_on pr sp = false \/ darg_ddict a = nullval -> oneshot_ok (dmode_of pr) (darg_model a) s cap r out) /\
  (sel_on pr sp = true -> darg_ddict a <> nullval -> oneshot_sel (dmode_of pr) (psel l tbl) (darg_model a) s cap r out) /\
  (is_error_code r = false -> exists c : list Z, bytes_ok c /\ Zlength c = r /\ sublist 0 r out = zbytes c) /\
  (is_error_code r = true -> dec_err r) /\
  (is_error_code r = false -> sel_on pr sp = true ->
     frame_compressed_size_m (dp_fmt pr =? 1) s = Some (Zlength s) ->
     forall h, get_frame_header_m (dp_fmt pr =? 1) s = FH_ok h -> fh_frameType h = 0 ->
       dcur = d \/ (exists q, In q (map fst l) /\ dcur = switch_fields q /\ q = hs_probe l tbl (fh_dictID h))) /\
  (is_error_code r = false -> sel_on pr sp = true -> df_ddict d <> nullval ->
     (exists h, get_frame_header_m (dp_fmt pr =? 1) s = FH_ok h /\ fh_frameType h = 0) ->
     exists id, fp_dictID (fs_fParams fs1) = Vint (Int.repr id) /\ 0 <= id <= Int.max_unsigned /\
       (hs_probe l tbl id = nullval \/ hs_probe l tbl id = df_ddict dcur)) /\
  (is_error_code r = false -> frame_compressed_size_m (dp_fmt pr =? 1) s = Some (Zlength s) ->
    forall h, get_frame_header_m (dp_fmt pr =? 1) s = FH_ok h -> fh_frameType h = 0 ->
       fh_contentSize h <> ZSTD_CONTENTSIZE_UNKNOWN -> r = fh_contentSize h).
Proof.
  intros pr sp a l tbl s cap r out fs1 d dcur He Hd Hse Hm.
  destruct (mf_post pr sp a l tbl s cap r out (oneshot_err _ _ _ _ _ _ _ He Hse) Hm) as [H1 H2].
  rewrite He. refine (conj _ (conj H1 (conj H2 (conj _ (conj _ (conj _ (conj _ _))))))); intros; try discriminate; auto.
Qed.

(* the state after ZSTD_decompressBegin_usingDict / usingDDict: the frame's dictionary a' (`ddict` qv' after the
   probe), Begin's model dm, the tables' state ts (dm's entropy state, litExtraBuffer kept: lxb), the resources ZSTD_decompressFrame takes
   (and the way back, MK2) *)
Definition mf_ab3 (DENT: dent_pred) (TABS: tabs_pred) (gv: globals) (p: val) (W: list ptr_witness) (pr: dparams)
    (sp: val) (d: dfields) (l: list (val * ddict_st)) (tbl: list val) (shk: share) (a: darg) (s: list Z)
    (cap: Z) (shd: share) (dst: val) (shs: share) (src v_src v_srcSize v_zfh: val)
    (off u: Z) (oc: list val) (fs1: fstate) (m: Z) (qv: val) (dcur: dfields) (am: option cmem) (hb: Z)
    (lxb: list Z) : environ -> mpred :=
  @exp (environ -> mpred) _ val (fun qv' => @exp (environ -> mpred) _ val (fun cold =>
  @exp (environ -> mpred) _ dict_model (fun dm => @exp (environ -> mpred) _ mpred (fun MK2 =>
  @exp (environ -> mpred) _ (option (val * val)) (fun xq => @exp (environ -> mpred) _ bool (fun lent =>
  @exp (environ -> mpred) _ tstate (fun ts =>
  PROP (qv_ok pr sp a l qv'; darg_c (mf_dict a l shk qv') dm; cold_ok cold;
        darg_wf (mf_dict a l shk qv'); darg_ok3 W (mf_dict a l shk qv') shd cap dst;
        sel_on pr sp = true -> cur_ok dcur l xq;
        lent = true -> lent_ok pr sp dcur l tbl (darg_ox (mf_dict a l shk qv')) (sublist off (Zlength s) s) /\
                       lent_ext dcur (ext_of (mf_dict a l shk qv') dm);
        darg_local d a = true -> qv' = darg_ddict a -> sel_on pr sp = true -> lent = true;
        darg_local d a = true -> qv' = darg_ddict a -> dcur = d;
        forall dcur', dict_after pr sp l dcur dcur' -> (lent = true -> dcur' = dcur) ->
          mf_fsel DENT gv p pr sp dcur' l tbl xq lent am hb (darg_ox (mf_dict a l shk qv')) *
          ext_res (ext_of (mf_dict a l shk qv') dm) * MK2 |--
          msel_res DENT gv p pr sp dcur' l tbl shk a am hb * darg_res3 DENT gv pr sp d a;
        darg_model a <> None ->
          frame_dict (dp_fmt pr =? 1) (mf_sel pr sp a l tbl) (darg_model (mf_dict a l shk qv))
            (sublist off (Zlength s) s) = Some dm /\ darg_model (mf_dict a l shk qv') = Some dm;
        ts_d ts = dm_state dm; ts_lxb ts = lxb)
  LOCAL (temp _moreThan1Frame (Vint (Int.repr m)); temp _dststart dst;
    lvar _zfh (Tstruct ___gp_ZSTD_FrameHeader noattr) v_zfh;
    lvar _srcSize tulong v_srcSize; lvar _src (tptr tvoid) v_src; gvars gv; temp _dctx p;
    temp _dst (offset_val u dst); temp _dstCapacity (Vlong (Int64.repr (cap - u)));
    temp _dict (darg_dictv a); temp _dictSize (Vlong (Int64.repr (darg_dsize a))); temp _ddict qv')
  SEP (data_at_ Tsh (Tstruct ___gp_ZSTD_FrameHeader noattr) v_zfh;
    data_at Tsh tulong (Vlong (Int64.repr (Zlength s - off))) v_srcSize;
    data_at Tsh (tptr tvoid) (offset_val off src) v_src; pws_pred W; zstd_globals gv;
    cfg_fmt p (dp_fmt pr); cfg_lit p; frame_fields p (fs_after_begin (mf_dict a l shk qv') fs1 cold dm (dp_fmt pr));
    TABS gv p (darg_ox (mf_dict a l shk qv')) ts;
    field_at Ews t_dctx (DOT _forceIgnoreChecksum) (Vint (Int.repr (dp_ignore pr))) p;
    field_at Ews t_dctx (DOT _maxBlockSizeParam) (Vint (Int.repr (dp_bmax pr))) p;
    field_at Ews t_dctx (DOT _refMultipleDDicts) (Vint (Int.repr (dp_multi pr))) p;
    field_at Ews t_dctx (DOT _ddictSet) sp p;
    mf_fsel DENT gv p pr sp dcur l tbl xq lent am hb (darg_ox (mf_dict a l shk qv'));
    ext_res (ext_of (mf_dict a l shk qv') dm); MK2;
    data_at shd (tarray tuchar cap) oc dst; data_at shs (tarray tuchar (Zlength s)) (zbytes s) src;
    field_at Ews t_dctx (DOT _streamStage) (Vint (Int.repr 0)) p)))))))).

(* the allocator facts of the selection hold for the current dictionary fields (a DDict of the set has no local one) *)
Lemma sel_mem_dc: forall pr sp l d dcur am hb,
  dc_ok pr sp l d dcur -> sel_mem pr sp d am hb -> sel_mem pr sp dcur am hb.
Proof.
  intros pr sp l d dcur am hb [-> | (Hs & q & Hq & ->)] Hm; auto.
  intros _. destruct (Hm Hs) as (_ & Hc & Hh). split; [| split; auto].
  intros E. exfalso. apply E. reflexivity.
Qed.

Lemma dc_after: forall pr sp l d dcur d', dc_ok pr sp l d dcur -> dict_after pr sp l dcur d' -> dc_ok pr sp l d d'.
Proof.
  intros pr sp l d dcur d' Hd [-> | (Hs & q & Hq & ->)]; auto. right. eauto.
Qed.

Lemma dc_ddict_nonnull: forall pr sp l tbl d dcur, dc_ok pr sp l d dcur -> (sel_on pr sp = true -> hs_inv l tbl) ->
  df_ddict d <> nullval -> df_ddict dcur <> nullval.
Proof.
  intros pr sp l tbl d dcur [-> | (Hs & q & Hq & ->)] Hh Hn; auto. simpl.
  destruct (Hh Hs) as (_ & _ & _ & _ & _ & Hptr & _).
  apply list_in_map_inv in Hq. destruct Hq as (e & -> & Hin).
  rewrite Forall_forall in Hptr. specialize (Hptr e Hin). intro E. rewrite E in Hptr. exact Hptr.
Qed.

Lemma fp_after_begin: forall a fs1 cold dm f d n,
  fs_fParams (continuity (fs_after_begin a fs1 cold dm f) d n) = fs_fParams fs1.
Proof.
  intros. unfold continuity. destruct (cont_moves _ _ _); destruct a as [| ? ? b | ? ? ?]; simpl;
    try destruct (Zlength b =? 0); reflexivity.
Qed.

Lemma mf_err_frame: forall pr sp d l tbl shk a fs s cap off u oc fs1 m qv dcur dm r oc' k,
  mf_pi pr sp d l tbl shk a fs s cap off u oc fs1 m qv dcur ->
  (darg_model a <> None -> frame_dict (dp_fmt pr =? 1) (mf_sel pr sp a l tbl) (darg_model (mf_dict a l shk qv))
     (sublist off (Zlength s) s) = Some dm) ->
  starting_len (dp_fmt pr =? 1) <= Zlength s - off ->
  ((dp_fmt pr =? 1) = true \/ is_skippable_magic (le_field (sublist off (Zlength s) s) 0 4) = false) ->
  frame_res3 (dmode_of pr) dm (sublist off (Zlength s) s) (cap - u) r oc' 0 k ->
  is_error_code r = true ->
  series_err (dmode_of pr) (mf_sel pr sp a l tbl) (darg_model a) s cap.
Proof.
  intros pr sp d l tbl shk a fs s cap off u oc fs1 m qv dcur dm r oc' k HI Hfd Hl Hmg Hf He.
  destruct (darg_model a) as [dm0|] eqn:Ea; [| exact I].
  pose proof (Hfd ltac:(discriminate)) as Hfd1.
  destruct HI as [Hoff Hu _ _ _ Hser _ _ _ _ _ _ _ _ _ _ _ _]. rewrite <- Ea in *.
  eapply series_err_frame; eauto; lia.
Qed.

(* the postcondition's facts after an error return, with the error codes *)
Lemma mf_err_post2: forall pr sp a l tbl s cap r out (fs1: fstate) (d dcur: dfields),
  is_error_code r = true -> dec_err r -> series_err (dmode_of pr) (mf_sel pr sp a l tbl) (darg_model a) s cap ->
  (darg_ddict a <> nullval -> darg_model a <> None) -> 0 <= cap ->
  (darg_model a <> None -> oneshot_codes (dmode_of pr) (mf_sel pr sp a l tbl) (darg_model a) s cap r) ->
  (a = DA_none -> pr = dparams_dflt -> os_res s cap = None) ->
  (is_error_code r = false -> r <= cap) /\
  (sel_on pr sp = false \/ darg_ddict a = nullval -> oneshot_ok (dmode_of pr) (darg_model a) s cap r out) /\
  (sel_on pr sp = true -> darg_ddict a <> nullval -> oneshot_sel (dmode_of pr) (psel l tbl) (darg_model a) s cap r out) /\
  (is_error_code r = false -> exists c : list Z, bytes_ok c /\ Zlength c = r /\ sublist 0 r out = zbytes c) /\
  (is_error_code r = true -> dec_err r) /\
  (is_error_code r = false -> sel_on pr sp = true ->
     frame_compressed_size_m (dp_fmt pr =? 1) s = Some (Zlength s) ->
     forall h, get_frame_header_m (dp_fmt pr =? 1) s = FH_ok h -> fh_frameType h = 0 ->
       dcur = d \/ (exists q, In q (map fst l) /\ dcur = switch_fields q /\ q = hs_probe l tbl (fh_dictID h))) /\
  (is_error_code r = false -> sel_on pr sp = true -> df_ddict d <> nullval ->
     (exists h, get_frame_header_m (dp_fmt pr =? 1) s = FH_ok h /\ fh_frameType h = 0) ->
     exists id, fp_dictID (fs_fParams fs1) = Vint (Int.repr id) /\ 0 <= id <= Int.max_unsigned /\
       (hs_probe l tbl id = nullval \/ hs_probe l tbl id = df_ddict dcur)) /\
  (sel_on pr sp = false \/ darg_ddict a = nullval -> oneshot_codes (dmode_of pr) sel_none (darg_model a) s cap r) /\
  (sel_on pr sp = true -> darg_ddict a <> nullval -> oneshot_codes (dmode_of pr) (psel l tbl) (darg_model a) s cap r) /\
  (is_error_code r = false -> frame_compressed_size_m (dp_fmt pr =? 1) s = Some (Zlength s) ->
    forall h, get_frame_header_m (dp_fmt pr =? 1) s = FH_ok h -> fh_frameType h = 0 ->
       fh_contentSize h <> ZSTD_CONTENTSIZE_UNKNOWN -> r = fh_contentSize h) /\
  (a = DA_none -> pr = dparams_dflt -> os_match s cap r out).
Proof.
  intros pr sp a l tbl s cap r out fs1 d dcur He Hd Hse Hm Hc Hcd Hx.
  destruct (mf_err_post pr sp a l tbl s cap r out fs1 d dcur He Hd Hse Hm) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
  destruct (mf_codes_post pr sp a l tbl s cap r Hc Hcd Hm) as [C1 C2].
  exact (conj E1 (conj E2 (conj E3 (conj E4 (conj E5 (conj E6 (conj E7 (conj C1 (conj C2 (conj E8 (fun Ha Hp => os_match_err s cap r out (Hx Ha Hp) He))))))))))).
Qed.

(* the claims of mf_err_post2 with one more at the end *)
Lemma conj_last11: forall A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 B: Prop,
  A1 /\ A2 /\ A3 /\ A4 /\ A5 /\ A6 /\ A7 /\ A8 /\ A9 /\ A10 /\ A11 -> B ->
  A1 /\ A2 /\ A3 /\ A4 /\ A5 /\ A6 /\ A7 /\ A8 /\ A9 /\ A10 /\ A11 /\ B.
Proof. tauto. Qed.

(* the error codes after an error of the frame at off *)
Lemma mf_codes_err: forall pr sp d l tbl shk a fs s cap off u oc fs1 m qv dcur dm r oc' k,
  mf_pi pr sp d l tbl shk a fs s cap off u oc fs1 m qv dcur ->
  (darg_model a <> None -> frame_dict (dp_fmt pr =? 1) (mf_sel pr sp a l tbl) (darg_model (mf_dict a l shk qv))
     (sublist off (Zlength s) s) = Some dm) ->
  starting_len (dp_fmt pr =? 1) <= Zlength s - off ->
  ((dp_fmt pr =? 1) = true \/ is_skippable_magic (le_field (sublist off (Zlength s) s) 0 4) = false) ->
  frame_res3 (dmode_of pr) dm (sublist off (Zlength s) s) (cap - u) r oc' 0 k ->
  frame_codes3 (dmode_of pr) dm (sublist off (Zlength s) s) (cap - u) r ->
  is_error_code r = true -> darg_model a <> None ->
  codes_exact (dmode_of pr) (mf_sel pr sp a l tbl) (darg_model a) s cap r.
Proof.
  intros pr sp d l tbl shk a fs s cap off u oc fs1 m qv dcur dm r oc' k HI Hfd Hl Hmg Hf Hc He Hn.
  destruct HI as [Hoff Hu _ _ _ _ _ _ _ _ _ _ _ _ _ Hcd _ _].
  eapply codes_err_frame; eauto.
Qed.

Lemma mf_pi_frame: forall pr sp d l tbl shk a fs s cap off u oc fs1 m qv dcur qv' dm lent d' r oc' k fs1' fs',
  mf_pi pr sp d l tbl shk a fs s cap off u oc fs1 m qv dcur ->
  (darg_model a <> None -> frame_dict (dp_fmt pr =? 1) (mf_sel pr sp a l tbl) (darg_model (mf_dict a l shk qv))
     (sublist off (Zlength s) s) = Some dm /\ darg_model (mf_dict a l shk qv') = Some dm) ->
  qv_ok pr sp a l qv' ->
  (darg_local d a = true -> qv' = darg_ddict a -> dcur = d) ->
  (darg_local d a = true -> qv' = darg_ddict a -> sel_on pr sp = true -> lent = true) ->
  dict_after pr sp l dcur d' -> (lent = true -> d' = dcur) ->
  (sel_on pr sp = true -> hs_inv l tbl) ->
  starting_len (dp_fmt pr =? 1) <= Zlength s - off ->
  ((dp_fmt pr =? 1) = true \/ is_skippable_magic (le_field (sublist off (Zlength s) s) 0 4) = false) ->
  frame_res3 (dmode_of pr) dm (sublist off (Zlength s) s) (cap - u) r oc' 0 k ->
  is_error_code r = false -> 0 <= r <= cap - u -> 0 <= k <= Zlength s - off ->
  Zlength oc' = cap - u ->
  (exists c, bytes_ok c /\ Zlength c = r /\ sublist 0 r oc' = zbytes c) ->
  fs_fParams fs1' = fs_fParams fs1 ->
  (fp_ok (fs_fParams fs1') -> fp_ok (fs_fParams fs')) ->
  (sel_on pr sp = true -> df_ddict dcur <> nullval -> exists id, fp_dictID (fs_fParams fs') = Vint (Int.repr id) /\
     0 <= id <= Int.max_unsigned /\ (hs_probe l tbl id = nullval \/ hs_probe l tbl id = df_ddict d')) ->
  bytes_ok s ->
  ((dp_fmt pr = 1 \/ is_skippable_magic (le_field (sublist off (Zlength s) s) 0 4) = false) ->
     frame_compressed_size_m (dp_fmt pr =? 1) (sublist off (Zlength s) s) = Some k) ->
  dict_sel pr sp l tbl (sublist 0 (header_size_m (dp_fmt pr =? 1) (sublist off (Zlength s) s)) (sublist off (Zlength s) s))
    dcur d' ->
  (forall h, get_frame_header_m (dp_fmt pr =? 1) (sublist off (Zlength s) s) = FH_ok h -> fh_frameType h = 0 ->
     fh_contentSize h <> ZSTD_CONTENTSIZE_UNKNOWN -> r = fh_contentSize h) ->
  (a = DA_none -> pr = dparams_dflt -> exists st c st', ExOneshot.lxb_ok st /\
     XF st (sublist off (Zlength s) s) (cap - u) = Some (c, k, st') /\ Zlength c = r /\ sublist 0 r oc' = zbytes c) ->
  mf_pi pr sp d l tbl shk a fs s cap (off + k) (u + r) (sublist 0 u oc ++ oc') fs' 1 qv' d'.
Proof.
  intros pr sp d l tbl shk a fs s cap off u oc fs1 m qv dcur qv' dm lent d' r oc' k fs1' fs'
    HI Hfd Hqv' Hloc' Hll Hda Hlt Hhs Hl Hmg Hf He Hr Hk Hoc' Hc Hfp1 Hfp2 Hds Hb Hfcs Hdsel Hrc Hxf.
  destruct HI as [Hoff Hu Hoc Hm Hacc Hser Hcur Hqv Hdc Hloc Hfp Hds2 Hm0 Hd0 Hsf Hcd Hu0 Hcfs Hx].
  destruct Hacc as (acc & Hab & Hal & Has). destruct Hc as (c & Hcb & Hcl & Hcs).
  constructor; auto; try lia.
  - rewrite Zlength_app, Zlength_sublist by lia. lia.
  - exists (acc ++ c). split; [unfold bytes_ok in *; apply Forall_app; auto |].
    split; [rewrite Zlength_app; lia |]. apply bytes_step; auto; lia.
  - destruct (darg_model a) as [dm0|] eqn:Ea; [| exact I].
    destruct (Hfd ltac:(discriminate)) as [Hfd1 Hfd2]. rewrite Hfd2. rewrite <- Ea in *.
    eapply series_inv_frame; eauto; try lia.
  - intros Hn. destruct (Hfd Hn) as [_ ->]. discriminate.
  - eapply dc_after; eauto.
  - intros Hl1 Hq. rewrite <- (Hloc' Hl1 Hq).
    destruct (sel_on pr sp) eqn:Hs.
    + apply Hlt. apply Hll; auto.
    + destruct Hda as [-> | (Hs' & _)]; [reflexivity | congruence].
  - intros Hp. apply Hfp2. rewrite Hfp1. auto.
  - intros _ Hs Hn. apply Hds; auto. eapply dc_ddict_nonnull; eauto.
  - intros _ Hs Hf1 h Hh Ht. destruct Hm as [-> | ->].
    + rewrite (Hd0 eq_refl) in *.
      destruct (Hm0 eq_refl) as [-> | Hnz]; [| exfalso; exact (Hnz h Hh Ht)].
      rewrite (sublist_same 0 (Zlength s) s) in Hfcs, Hdsel, Hmg by lia.
      assert (Hk1: k = Zlength s).
      { assert (Hm': dp_fmt pr = 1 \/ is_skippable_magic (le_field s 0 4) = false)
          by (destruct Hmg as [E | E]; [left; apply Z.eqb_eq; auto | right; auto]).
        rewrite Hf1 in Hfcs. specialize (Hfcs Hm'). congruence. }
      split; [lia |].
      destruct (gfh3_prefix (dp_fmt pr =? 1) s Hb ltac:(lia) Hmg) as [E | (N1 & N2)];
        [| exfalso; exact (N2 h Hh)].
      rewrite Hh in E. destruct (Hdsel Hs h E) as [-> | (Hn & ->)]; [left; auto | right].
      exists (hs_probe l tbl (fh_dictID h)). split; [apply hs_probe_in; auto | auto].
    + destruct (Hsf eq_refl Hs Hf1 h Hh Ht) as [E _]. pose proof (starting_len_pos (dp_fmt pr =? 1)). lia.
  - intros Hn. destruct (Hfd Hn) as [Hfd1 Hfd2]. rewrite Hfd2.
    eapply codes_inv_frame; eauto; lia.
  - intros _ Hf1 h Hh Ht. destruct Hm as [-> | ->].
    + destruct (Hm0 eq_refl) as [-> | Hnz]; [| exfalso; exact (Hnz h Hh Ht)].
      rewrite (Hu0 eq_refl), Z.add_0_l.
      rewrite (sublist_same 0 (Zlength s) s) in Hfcs, Hmg, Hrc by lia.
      assert (Hk1: k = Zlength s).
      { assert (Hm': dp_fmt pr = 1 \/ is_skippable_magic (le_field s 0 4) = false)
          by (destruct Hmg as [E | E]; [left; apply Z.eqb_eq; auto | right; auto]).
        rewrite Hf1 in Hfcs. specialize (Hfcs Hm'). congruence. }
      split; [lia |]. intros Hcu. exact (Hrc h Hh Ht Hcu).
    + destruct (Hcfs eq_refl Hf1 h Hh Ht) as [E _]. pose proof (starting_len_pos (dp_fmt pr =? 1)). lia.
  - apply mf_x_frame; auto; try lia.
    intros Ha Hp. destruct (Hxf Ha Hp) as (xs & xc & xs' & X1 & X2 & X3 & X4).
    rewrite Hp in Hl, Hmg. change (dp_fmt dparams_dflt =? 1) with false in Hl, Hmg.
    destruct Hmg as [E | E]; [discriminate E |].
    split; [exact Hl | split; [exact E | eauto 10]].
Qed.

Lemma mf_dict_q0: forall a l shk, mf_dict a l shk (darg_ddict a) = a.
Proof. intros. unfold mf_dict, veqb. destruct (Val.eq _ _); [reflexivity | congruence]. Qed.

(* ZSTD_decompressFrame's exact claim (frame_exact) at the call of the loop: without a dictionary argument and with the
   default parameters, the frame is begun with no dictionary (ox = None, no_dict, no extDict), so the claim holds; it
   is on the tables' state ts, whose litExtraBuffer has its full size, and on dst's part of the output *)
Lemma mf_fx: forall pr sp a l shk qv' a' dm ts t shd cap oc dst u r oc0 k lxbf,
  a' = mf_dict a l shk qv' -> qv_ok pr sp a l qv' -> darg_c a' dm -> Zlength (ts_lxb ts) = LITEXTRA_N ->
  (darg_ox a' = None -> dm = no_dict -> pr = dparams_dflt -> mf_e a' dm dst cap u = ExtNone ->
     frame_exact ts t (oa_cap (mf_oa a' shd cap oc dst u)) r oc0 (oa_d (mf_oa a' shd cap oc dst u)) k lxbf) ->
  a = DA_none -> pr = dparams_dflt ->
  ExOneshot.lxb_ok (ts_x ts) /\
  match XF (ts_x ts) t (cap - u) with
  | None => is_error_code r = true
  | Some (c, k', _) => r = Zlength c /\ sublist 0 r (mf_back a' dst cap u oc0) = zbytes c /\ k = k'
  end.
Proof.
  intros pr sp a l shk qv' a' dm ts t shd cap oc dst u r oc0 k lxbf Ea Hq Hc Hl Hf -> ->.
  assert (E: a' = DA_none).
  { rewrite Ea. destruct Hq as [Eq | (Hs & _)].
    - rewrite Eq. apply mf_dict_q0.
    - unfold sel_on in Hs. simpl in Hs. discriminate Hs. }
  rewrite E in Hc, Hf |- *. clear Ea. unfold darg_c in Hc. subst dm.
  split.
  - unfold ExOneshot.lxb_ok. cbn [ts_x x_lxb]. rewrite Hl. reflexivity.
  - assert (Ee: mf_e DA_none no_dict dst cap u = ExtNone) by (unfold mf_e; destruct (gap0 _ _ _ _); reflexivity).
    specialize (Hf eq_refl eq_refl eq_refl Ee). unfold frame_exact in Hf.
    replace (oa_cap (mf_oa DA_none shd cap oc dst u)) with (cap - u) in Hf
      by (unfold mf_oa; destruct (gap0 _ _ _ _); reflexivity).
    replace (oa_d (mf_oa DA_none shd cap oc dst u)) with 0 in Hf
      by (unfold mf_oa; destruct (gap0 _ _ _ _); reflexivity).
    replace (mf_back DA_none dst cap u oc0) with oc0 by (unfold mf_back; destruct (gap0 _ _ _ _); reflexivity).
    destruct (XF (ts_x ts) t (cap - u)) as [[[c k'] e]|]; [| exact Hf].
    destruct Hf as (H1 & H2 & H3 & _). rewrite Z.add_0_l in H2. auto.
Qed.

(* bytes read from the start of an array are no more than its cells *)
Lemma sublist_zbytes_le: forall (c: list Z) (l: list val), sublist 0 (Zlength c) l = zbytes c -> Zlength c <= Zlength l.
Proof.
  intros c l H. apply (f_equal (@Zlength val)) in H. rewrite Zlength_map in H.
  unfold sublist in H. change (Z.to_nat 0) with O in H. cbn [skipn] in H.
  rewrite !Zlength_correct in *. rewrite firstn_length in H. lia.
Qed.

(* the frame failed: by its exact claim the model refuses it too (a success of the model is no error code: its
   content fits in dst's part), so os_res fails *)
Lemma mf_x_ferr: forall a pr s cap off u oc st r l k,
  mf_x a pr s cap off u oc -> bytes_ok s -> 0 <= off -> 0 <= u <= cap -> cap <= 2 ^ 63 - 1 -> Zlength l = cap - u ->
  starting_len (dp_fmt pr =? 1) <= Zlength s - off ->
  ((dp_fmt pr =? 1) = true \/ is_skippable_magic (le_field (sublist off (Zlength s) s) 0 4) = false) ->
  is_error_code r = true ->
  (a = DA_none -> pr = dparams_dflt -> ExOneshot.lxb_ok st /\
     match XF st (sublist off (Zlength s) s) (cap - u) with
     | None => is_error_code r = true
     | Some (c, k', _) => r = Zlength c /\ sublist 0 r l = zbytes c /\ k = k'
     end) ->
  a = DA_none -> pr = dparams_dflt -> os_res s cap = None.
Proof.
  intros a pr s cap off u oc st r l k Hx Hb Ho Hu Hc Hl Hlen Hmg He Hf Ha Hp.
  destruct (Hf Ha Hp) as [Hst Hm].
  rewrite Hp in Hlen, Hmg. change (dp_fmt dparams_dflt =? 1) with false in Hlen, Hmg.
  destruct Hmg as [E | E]; [discriminate E |].
  apply (mf_x_frame_err a pr s cap off u oc st Hx Hb Ho Hlen E Hst); auto.
  destruct (XF st _ _) as [[[c k'] e]|] eqn:Exf; [exfalso | reflexivity].
  destruct Hm as (-> & H2 & _).
  pose proof (sublist_zbytes_le _ _ H2) as Hle.
  assert (is_error_code (Zlength c) = false) by (unfold is_error_code; apply Z.ltb_ge; lia).
  congruence.
Qed.

(* the frame succeeded: so did the model, with the same content and size *)
Lemma mf_x_fok: forall st t cap u r l k, is_error_code r = false ->
  ExOneshot.lxb_ok st /\
  match XF st t (cap - u) with
  | None => is_error_code r = true
  | Some (c, k', _) => r = Zlength c /\ sublist 0 r l = zbytes c /\ k = k'
  end ->
  exists st0 c st', ExOneshot.lxb_ok st0 /\ XF st0 t (cap - u) = Some (c, k, st') /\ Zlength c = r /\
    sublist 0 r l = zbytes c.
Proof.
  intros st t cap u r l k He [Hst Hm]. destruct (XF st t (cap - u)) as [[[c k'] e]|] eqn:Exf; [| congruence].
  destruct Hm as (H1 & H2 & ->). exists st, c, e. repeat split; auto.
Qed.

(* ---------- litExtraBuffer after one frame (the stream's single-pass shortcut) ---------- *)

(* x_frame begins with ZSTD_decompressBegin (xst_begin), which keeps only litExtraBuffer *)
Lemma xf_lxb: forall st1 st2 t cap, x_lxb xhuf st1 = x_lxb xhuf st2 -> XF st1 t cap = XF st2 t cap.
Proof. intros st1 st2 t cap E. unfold x_frame, xst_begin. rewrite E. reflexivity. Qed.

(* a frame the model decodes has at least a frame header and a block header *)
Lemma xf_len: forall st t cap x, XF st t cap = Some x -> ZSTD_FRAMEHEADERSIZE_MIN + ZSTD_blockHeaderSize <= Zlength t.
Proof.
  intros st t cap x E. unfold x_frame in E.
  destruct (Z.ltb_spec (Zlength t) (ZSTD_FRAMEHEADERSIZE_MIN + ZSTD_blockHeaderSize)); [discriminate | lia].
Qed.

(* the tables' litExtraBuffer lxb along the loop: without a dictionary and with the default parameters, when s is
   exactly one Zstandard frame that the model decodes from the first litExtraBuffer lxb0, it is lxb0 before that
   frame and the frame's final litExtraBuffer after it *)
Definition mf_l (a: darg) (pr: dparams) (lxb0 s: list Z) (cap off u: Z) (lxb: list Z) : Prop :=
  a = DA_none -> pr = dparams_dflt -> is_skippable_magic (le_field s 0 4) = false ->
  forall (st e: xstate) (c: list Z), x_lxb xhuf st = lxb0 -> XF st s cap = Some (c, Zlength s, e) ->
    (off = 0 /\ u = 0 /\ lxb = lxb0) \/ (off = Zlength s /\ lxb = x_lxb xhuf e).

(* the specification's claim on the final litExtraBuffer lxb' *)
Definition mf_lpost (a: darg) (pr: dparams) (lxb0 s: list Z) (cap: Z) (lxb': list Z) : Prop :=
  a = DA_none -> pr = dparams_dflt -> is_skippable_magic (le_field s 0 4) = false ->
  forall (st e: xstate) (c: list Z), x_lxb xhuf st = lxb0 -> XF st s cap = Some (c, Zlength s, e) ->
    lxb' = x_lxb xhuf e.

Lemma mf_l_init: forall a pr lxb0 s cap, mf_l a pr lxb0 s cap 0 0 lxb0.
Proof. intros a pr lxb0 s cap _ _ _ st e c _ _. left. auto. Qed.

(* a skippable frame at off: not the case of the claim (s does not begin with one, and a frame of all of s is no
   longer ahead after a frame) *)
Lemma mf_l_skip_post: forall a pr lxb0 s cap off u lxb lxb',
  mf_l a pr lxb0 s cap off u lxb -> 0 <= off -> 1 <= Zlength s - off ->
  is_skippable_magic (le_field (sublist off (Zlength s) s) 0 4) = true -> mf_lpost a pr lxb0 s cap lxb'.
Proof.
  intros a pr lxb0 s cap off u lxb lxb' H Ho Hl Hm Ha Hp Hn st e c Hst Hx.
  destruct (H Ha Hp Hn st e c Hst Hx) as [(E & _ & _) | (E & _)]; [| lia].
  subst off. rewrite sublist_same in Hm by lia. congruence.
Qed.

Lemma mf_l_skip: forall a pr lxb0 s cap off u lxb off' u',
  mf_l a pr lxb0 s cap off u lxb -> 0 <= off -> 1 <= Zlength s - off ->
  is_skippable_magic (le_field (sublist off (Zlength s) s) 0 4) = true -> mf_l a pr lxb0 s cap off' u' lxb.
Proof.
  intros a pr lxb0 s cap off u lxb off' u' H Ho Hl Hm Ha Hp Hn st e c Hst Hx. exfalso.
  destruct (H Ha Hp Hn st e c Hst Hx) as [(E & _ & _) | (E & _)]; [| lia].
  subst off. rewrite sublist_same in Hm by lia. congruence.
Qed.

(* ZSTD_decompressFrame's exact claim on litExtraBuffer (frame_exact) at the call of the loop *)
Lemma mf_fx_l: forall pr sp a l shk qv' a' dm ts t shd cap oc dst u r oc0 k lxbf,
  a' = mf_dict a l shk qv' -> qv_ok pr sp a l qv' -> darg_c a' dm ->
  (darg_ox a' = None -> dm = no_dict -> pr = dparams_dflt -> mf_e a' dm dst cap u = ExtNone ->
     frame_exact ts t (oa_cap (mf_oa a' shd cap oc dst u)) r oc0 (oa_d (mf_oa a' shd cap oc dst u)) k lxbf) ->
  a = DA_none -> pr = dparams_dflt ->
  forall c k' e, XF (ts_x ts) t (cap - u) = Some (c, k', e) -> lxbf = x_lxb xhuf e.
Proof.
  intros pr sp a l shk qv' a' dm ts t shd cap oc dst u r oc0 k lxbf Ea Hq Hc Hf -> -> c k' e Ex.
  assert (E: a' = DA_none).
  { rewrite Ea. destruct Hq as [Eq | (Hs & _)].
    - rewrite Eq. apply mf_dict_q0.
    - unfold sel_on in Hs. simpl in Hs. discriminate Hs. }
  rewrite E in Hc, Hf. clear Ea. unfold darg_c in Hc. subst dm.
  assert (Ee: mf_e DA_none no_dict dst cap u = ExtNone) by (unfold mf_e; destruct (gap0 _ _ _ _); reflexivity).
  specialize (Hf eq_refl eq_refl eq_refl Ee). unfold frame_exact in Hf.
  replace (oa_cap (mf_oa DA_none shd cap oc dst u)) with (cap - u) in Hf
    by (unfold mf_oa; destruct (gap0 _ _ _ _); reflexivity).
  rewrite Ex in Hf. destruct Hf as (_ & _ & _ & H4). exact H4.
Qed.

(* the frame at off decoded (begun with the tables' litExtraBuffer lxb): if it is the frame of all of s, the
   tables now hold its final litExtraBuffer *)
Lemma mf_l_frame: forall a pr lxb0 s cap off u lxb ts r k lxbf (l: list val),
  mf_l a pr lxb0 s cap off u lxb -> 0 <= off -> 1 <= Zlength s - off -> ts_lxb ts = lxb ->
  (a = DA_none -> pr = dparams_dflt -> ExOneshot.lxb_ok (ts_x ts) /\
     match XF (ts_x ts) (sublist off (Zlength s) s) (cap - u) with
     | None => is_error_code r = true
     | Some (c, k', _) => r = Zlength c /\ sublist 0 r l = zbytes c /\ k = k'
     end) ->
  (a = DA_none -> pr = dparams_dflt ->
     forall c k' e, XF (ts_x ts) (sublist off (Zlength s) s) (cap - u) = Some (c, k', e) -> lxbf = x_lxb xhuf e) ->
  mf_l a pr lxb0 s cap (off + k) (u + r) lxbf.
Proof.
  intros a pr lxb0 s cap off u lxb ts r k lxbf l H Ho Hl Ht Hf Hfl Ha Hp Hn st e c Hst Hx.
  destruct (H Ha Hp Hn st e c Hst Hx) as [(E1 & E2 & Eb) | (E & _)]; [| lia]. subst off u.
  rewrite sublist_same in Hf, Hfl by lia. rewrite Z.sub_0_r in Hf, Hfl.
  assert (Ex: XF (ts_x ts) s cap = Some (c, Zlength s, e)).
  { rewrite (xf_lxb _ st); [exact Hx | cbn [ts_x x_lxb]; congruence]. }
  destruct (Hf Ha Hp) as [_ Hm]. rewrite Ex in Hm. destruct Hm as (_ & _ & ->).
  right. split; [lia | exact (Hfl Ha Hp c _ e Ex)].
Qed.

(* the loop ended at the end of s: the claim *)
Lemma mf_l_end: forall a pr lxb0 s cap off u lxb,
  mf_l a pr lxb0 s cap off u lxb -> off = Zlength s -> mf_lpost a pr lxb0 s cap lxb.
Proof.
  intros a pr lxb0 s cap off u lxb H Ho Ha Hp Hn st e c Hst Hx.
  pose proof (xf_len _ _ _ _ Hx) as Hlen.
  destruct (H Ha Hp Hn st e c Hst Hx) as [(E & _ & _) | (_ & E)]; [| exact E].
  unfold ZSTD_FRAMEHEADERSIZE_MIN, ZSTD_blockHeaderSize in Hlen. lia.
Qed.

(* an error: then s is no frame that the model decodes from a full-size litExtraBuffer (os_res would succeed) *)
Lemma mf_l_err: forall a pr lxb0 s cap r out lxb',
  (a = DA_none -> pr = dparams_dflt -> os_match s cap r out) -> is_error_code r = true ->
  Zlength out <= 2 ^ 63 - 1 -> bytes_ok s -> Zlength lxb0 = LITEXTRA_N -> mf_lpost a pr lxb0 s cap lxb'.
Proof.
  intros a pr lxb0 s cap r out lxb' Hm He Ho Hb Hl Ha Hp Hn st e c Hst Hx. exfalso.
  specialize (Hm Ha Hp). unfold os_match in Hm. rewrite ExOneshot.os_res_rest in Hm.
  pose proof (xf_len _ _ _ _ Hx) as Hlen.
  rewrite (ExOneshot.xs_rest_frame_res st s cap nil c (Zlength s) e) in Hm;
    [| exact Hb | unfold ZSTD_FRAMEHEADERSIZE_PREFIX, ZSTD_FRAMEHEADERSIZE_MIN, ZSTD_blockHeaderSize in *; lia
     | exact Hn | unfold ExOneshot.lxb_ok; rewrite Hst, Hl; reflexivity | rewrite Zlength_nil, Z.sub_0_r; exact Hx].
  rewrite Zlength_correct, Nat2Z.id, skipn_all in Hm.
  rewrite ExOneshot.xs_rest_end in Hm by (rewrite Zlength_nil; unfold ZSTD_FRAMEHEADERSIZE_PREFIX; lia).
  cbn [app] in Hm. change (Zlength (@nil Z) =? 0) with true in Hm. cbv iota in Hm.
  destruct Hm as [-> Hs]. pose proof (sublist_zbytes_le _ _ Hs) as Hle.
  assert (is_error_code (Zlength c) = false) by (unfold is_error_code; apply Z.ltb_ge; lia).
  congruence.
Qed.

Ltac skip_loop :=
  match goal with |- semax _ ?P _ _ => forward_loop P break: P; [apply ENTAIL_refl | forward | ]; [apply ENTAIL_refl | ] end.
(* do { if (0) debug(...); } while (0) *)
Ltac dbg_loop :=
  match goal with |- semax _ ?P _ _ =>
    forward_loop P break: P;
    [apply ENTAIL_refl
    | forward_if P; [exfalso; match goal with H: 0 <> 0 |- _ => apply H; reflexivity end | forward | forward]
    | ]; try apply ENTAIL_refl end.
Ltac dloop := first [skip_loop | dbg_loop].

(* The window on the unread suffix of the source, for a source of any length up to
   PTRDIFF_MAX ([win_ok_suffix] is stated for sources up to 2^30 bytes). *)
Lemma win_ok_suffix63: forall sh s off, readable_share sh -> bytes_ok s -> Zlength s <= 2 ^ 63 - 1 ->
  0 <= off <= Zlength s ->
  win_ok sh (Zlength s) (zbytes s) off (Zlength (sublist off (Zlength s) s)) (sublist off (Zlength s) s).
Proof.
  intros. unfold win_ok. rewrite Zlength_sublist by lia.
  repeat split; auto; try lia.
  - rewrite Zlength_map. auto.
  - apply bytes_ok_sublist. auto.
  - rewrite sublist_map. f_equal. f_equal. lia.
Qed.

(* The end of the series loop gives the one-shot result, for a destination of any capacity
   up to PTRDIFF_MAX ([oneshot_end] is stated for capacities up to 2^30). *)
Lemma oneshot_end63: forall md sel odm0 cur s off u oc cap,
  series_inv md sel odm0 cur s off u oc -> off = Zlength s -> 0 <= u <= cap -> cap <= 2 ^ 63 - 1 ->
  oneshot_g md sel odm0 s cap u oc.
Proof.
  intros md sel odm0 cur s off u oc cap Hinv -> Hu Hc.
  assert (Hne: is_error_code u = false) by (unfold is_error_code; apply Z.ltb_ge; lia).
  unfold oneshot_g, series_inv in *. split; [intros; lia |].
  destruct odm0 as [dm |]; auto.
  destruct Hinv as [[-> Hnr] | (acc & Hl & Hs & Hd & _)]; [intros Hr; contradiction |]. rewrite Hd.
  rewrite sublist_nil.
  rewrite decode_seriesS_short by (rewrite Zlength_nil; pose proof (starting_len_pos (md_magicless md)); lia).
  simpl. rewrite app_nil_r. split; [intros; split; [lia | congruence] | rewrite Hne; discriminate].
Qed.

(* [op - ostart] for an output pointer [u] bytes into dst, for any [u] up to PTRDIFF_MAX
   ([sub_pp_offset] is stated for [u] up to 2^30). *)
Lemma sub_pp_offset63: forall b o u, 0 <= u <= 2 ^ 63 - 1 -> Ptrofs.unsigned o + u <= Ptrofs.max_unsigned ->
  force_val (sem_sub_pp tuchar (offset_val u (Vptr b o)) (Vptr b o)) = Vlong (Int64.repr u).
Proof.
  intros. unfold sem_sub_pp. simpl. rewrite if_true by auto.
  simpl. pose proof (Ptrofs.unsigned_range o).
  rewrite Ptrofs.sub_add_l, Ptrofs.sub_idem, Ptrofs.add_zero_l. unfold Ptrofs.divs.
  rewrite (Ptrofs.signed_repr 1) by rep_lia. rewrite (Ptrofs.signed_repr u) by rep_lia.
  rewrite Z.quot_1_r. unfold Vptrofs. simpl. unfold Ptrofs.to_int64.
  rewrite Ptrofs.unsigned_repr by rep_lia. reflexivity.
Qed.

(* The body's proof works on the base dst the code computes with (F9: `dststart = dst != NULL ? dst :
   ZSTD_emptyBuffer`): dst0 is the argument, NULL (and then cap = 0) or the base itself.  The specification
   ZSTD_decompressMultiFrame_spec3 follows (funspec_sub below), the empty base's witness lent by zstd_globals. *)
Definition ZSTD_decompressMultiFrame_spec3b (DENT: dent_pred) (TABS: tabs_pred) : ident * funspec :=
  DECLARE _ZSTD_decompressMultiFrame
  WITH W: list ptr_witness, gv: globals, p: val, fs: fstate, tabs: tabs3, pr: dparams, sp: val, d: dfields,
       l: list (val * ddict_st), tbl: list val, shk: share,
       shd: share, dst0: val, dst: val, cap: Z, shs: share, src: val, s: list Z, a: darg, am: option cmem, hb: Z
  PRE [ tptr t_dctx, tptr tvoid, tulong, tptr tvoid, tulong, tptr tvoid, tulong, tptr t_ddict ]
    PROP (buf_ok W shd cap dst; buf_ok W shs (Zlength s) src; writable_share shd; readable_share shs;
          0 <= cap <= 2 ^ 63 - 1; Zlength s <= 2 ^ 63 - 1; bytes_ok s; darg_ok3 W a shd cap dst;
          sel_on pr sp = true -> msel_ok W d l a shk shd cap dst;
          dst0 = dst \/ (dst0 = nullval /\ dst = gv _ZSTD_emptyBuffer); sel_mem pr sp d am hb)
    PARAMS (p; dst0; Vlong (Int64.repr cap); src; Vlong (Int64.repr (Zlength s));
            darg_dict a; Vlong (Int64.repr (darg_size a)); darg_ddict a)
    GLOBALS (gv)
    SEP (pws_pred W; zstd_globals gv; fgroup3 TABS gv p fs tabs pr sp; msel_res DENT gv p pr sp d l tbl shk a am hb;
         darg_res3 DENT gv pr sp d a; data_at_ shd (tarray tuchar cap) dst;
         data_at shs (tarray tuchar (Zlength s)) (zbytes s) src;
         field_at_ Ews t_dctx (DOT _streamStage) p)
  POST [ tulong ]
    EX r: Z, EX out: list val, EX fs': fstate, EX d': dfields, EX lxb': list Z,
    PROP (0 <= r <= Int64.max_unsigned; Zlength out = cap; is_error_code r = false -> r <= cap;
          sel_on pr sp = false \/ darg_ddict a = nullval -> oneshot_ok (dmode_of pr) (darg_model a) s cap r out;
          sel_on pr sp = true -> darg_ddict a <> nullval ->
            oneshot_sel (dmode_of pr) (psel l tbl) (darg_model a) s cap r out;
          is_error_code r = false -> exists c, bytes_ok c /\ Zlength c = r /\ sublist 0 r out = zbytes c;
          is_error_code r = true -> dec_err r;
          d' = d \/ (sel_on pr sp = true /\ exists q, In q (map fst l) /\ d' = switch_fields q);
          (* one frame: selectFrameDDict ran once, on its Dictionary_ID *)
          is_error_code r = false -> sel_on pr sp = true ->
            frame_compressed_size_m (dp_fmt pr =? 1) s = Some (Zlength s) ->
            forall h, get_frame_header_m (dp_fmt pr =? 1) s = FH_ok h -> fh_frameType h = 0 ->
              d' = d \/ (exists q, In q (map fst l) /\ d' = switch_fields q /\ q = hs_probe l tbl (fh_dictID h));
          (* D-S2 (441): after a success on bytes starting with a Zstandard frame, with a current DDict *)
          is_error_code r = false -> sel_on pr sp = true -> df_ddict d <> nullval ->
            (exists h, get_frame_header_m (dp_fmt pr =? 1) s = FH_ok h /\ fh_frameType h = 0) ->
            exists id, fp_dictID (fs_fParams fs') = Vint (Int.repr id) /\ 0 <= id <= Int.max_unsigned /\
              (hs_probe l tbl id = nullval \/ hs_probe l tbl id = df_ddict d');
          (* fParams' dictID stays a 32-bit value *)
          fp_ok (fs_fParams fs) -> fp_ok (fs_fParams fs');
          (* the error codes (Spec_codes.oneshot_codes) *)
          sel_on pr sp = false \/ darg_ddict a = nullval -> oneshot_codes (dmode_of pr) sel_none (darg_model a) s cap r;
          sel_on pr sp = true -> darg_ddict a <> nullval -> oneshot_codes (dmode_of pr) (psel l tbl) (darg_model a) s cap r;
          (* the end-of-frame check: a success on one Zstandard frame that declares its content size decodes
             exactly that many bytes (the single-pass shortcut of ZSTD_decompressStream, fix F7) *)
          is_error_code r = false -> frame_compressed_size_m (dp_fmt pr =? 1) s = Some (Zlength s) ->
            forall h, get_frame_header_m (dp_fmt pr =? 1) s = FH_ok h -> fh_frameType h = 0 ->
              fh_contentSize h <> ZSTD_CONTENTSIZE_UNKNOWN -> r = fh_contentSize h;
          (* the exact result, without a dictionary and with the default parameters (model/Exact.v) *)
          a = DA_none -> pr = dparams_dflt -> os_match s cap r out;
          (* litExtraBuffer afterwards, when s is exactly one Zstandard frame that the model decodes from the
             tables' litExtraBuffer: the frame's *)
          a = DA_none -> pr = dparams_dflt -> is_skippable_magic (le_field s 0 4) = false ->
            forall (st e: xstate) (c: list Z), x_lxb xhuf st = tabs_lxb tabs ->
            x_frame xstate (xst_begin xhuf) xblock st s cap = Some (c, Zlength s, e) -> lxb' = x_lxb xhuf e)
    RETURN (Vlong (Int64.repr r))
    SEP (pws_pred W; zstd_globals gv; fgroup3 TABS gv p fs' (TUninit lxb') pr sp; msel_res DENT gv p pr sp d' l tbl shk a am hb;
         darg_res3 DENT gv pr sp d a; data_at shd (tarray tuchar cap) out dst;
         data_at shs (tarray tuchar (Zlength s)) (zbytes s) src;
         field_at Ews t_dctx (DOT _streamStage) (Vint (Int.repr 0)) p).

Lemma body_decompressMultiFrame3b: forall DENT TABS SR BR, DENT_OK DENT -> TABS_OK TABS ->
  semax_body Vprog (FR3_G DENT TABS SR BR) f_ZSTD_decompressMultiFrame (ZSTD_decompressMultiFrame_spec3b DENT TABS).
Proof.
  intros DENT TABS SR BR HDENT HTABS.
  start_function.
  rename H7 into Hsm.
  forward. forward.
  (* F9: dststart = dst0 != NULL ? dst0 : ZSTD_emptyBuffer, the base dst *)
  assert_PROP (isptr dst) as Hdst by entailer!.
  match goal with Hb: dst0 = dst \/ _ |- _ => rename Hb into Hdst0 end.
  forward_if (temp _t'1 dst).
  { destruct Hdst0 as [-> | [-> _]].
    - apply test_eq_null_weak; [auto |].
      assert (Hw: pws_pred W * data_at_ shd (tarray tuchar cap) dst |-- weak_valid_pointer dst)
        by (eapply derives_trans; [apply H | apply andp_left1, derives_refl]).
      sep_apply Hw. auto with valid_pointer.
    - entailer!. }
  { forward. destruct Hdst0 as [-> | [-> _]]; [entailer! | contradiction]. }
  { forward. destruct Hdst0 as [-> | [_ ->]]; [subst dst; contradiction | entailer!]. }
  forward. forward. dloop.
  (* F10: streamStage = zdss_init *)
  forward. forward.
  drop_LOCAL 11%nat. drop_LOCAL 10%nat. drop_LOCAL 3%nat.
  assert_PROP (cold01 fs /\ par_ok pr) as Hfg by (unfold fgroup3; entailer!).
  sep_apply (fgroup3_uninit TABS gv p fs tabs pr sp HTABS).
  assert_PROP (Zlength (tabs_lxb tabs) = LITEXTRA_N) as Hlx0
    by (unfold fgroup3; cbn [tabs_rep]; unfold tables_uninit, lit_extra_at; entailer!).
  forward_if (PROP (darg_ddict a <> nullval -> darg_model a <> None)
    LOCAL (temp _moreThan1Frame (Vint (Int.repr 0)); temp _dststart dst;
      lvar _zfh (Tstruct ___gp_ZSTD_FrameHeader noattr) v_zfh;
      lvar _srcSize tulong v_srcSize; lvar _src (tptr tvoid) v_src; gvars gv; temp _dctx p; temp _dst dst;
      temp _dstCapacity (Vlong (Int64.repr cap)); temp _dict (darg_dictv a);
      temp _dictSize (Vlong (Int64.repr (darg_dsize a))); temp _ddict (darg_ddict a))
    SEP (data_at_ Tsh (Tstruct ___gp_ZSTD_FrameHeader noattr) v_zfh;
      data_at Tsh tulong (Vlong (Int64.repr (Zlength s))) v_srcSize; data_at Tsh (tptr tvoid) src v_src;
      pws_pred W; zstd_globals gv; fgroup3 TABS gv p fs (TUninit (tabs_lxb tabs)) pr sp;
      msel_res DENT gv p pr sp d l tbl shk a am hb;
      darg_res3 DENT gv pr sp d a; data_at_ shd (tarray tuchar cap) dst;
      data_at shs (tarray tuchar (Zlength s)) (zbytes s) src;
      field_at Ews t_dctx (DOT _streamStage) (Vint (Int.repr 0)) p))%assert.
  { destruct a as [| sh pk b | x buf sh]; simpl darg_ddict; [entailer! | entailer! |].
    destruct (mf_struct DENT gv p pr sp d l tbl shk _ W shd cap dst x buf sh am hb eq_refl H5) as (K & HK1 & _).
    sep_apply HK1. unfold ddict_struct. Intros. entailer!.
    apply denote_tc_test_eq_split; [ | apply valid_pointer_null].
    sep_apply (field_at_valid_ptr0 Ews (Tstruct _ZSTD_DDict_s noattr) (DOT _dictBuffer)
      (if ddx_copied x then buf else nullval) (dx_q x)); auto.
    apply extend_valid_pointer. }
  { destruct a as [| sh pk b | x buf sh]; simpl in H6; try contradiction.
    destruct (mf_struct DENT gv p pr sp d l tbl shk _ W shd cap dst x buf sh am hb eq_refl H5) as (K & HK1 & HK2).
    sep_apply HK1.
    assert_PROP (ddx_model x <> None) as Hxm.
    { unfold ddict_struct. entailer!.
      match goal with Hn: ddx_model x = None, Hr: dx_raw x = true \/ _ |- _ =>
        unfold ddx_model in Hn; destruct (dx_raw x); [discriminate | destruct Hr; [discriminate | contradiction]] end. }
    cbn [darg_dict darg_size darg_ddict]. drop_LOCALs [_dictSize].
    forward_call (x, buf). { cancel. } forward_call (x, buf). forward.
    entailer!. sep_apply HK2. cancel. }
  { forward. destruct a as [| sh pk b | x buf sh]; simpl in H6.
    - entailer!.
    - entailer!.
    - destruct (mf_struct DENT gv p pr sp d l tbl shk _ W shd cap dst x buf sh am hb eq_refl H5) as (K & HK1 & HK2).
      sep_apply HK1. unfold ddict_struct. Intros. match goal with Hn: dx_q x = nullval, Hp: isptr (dx_q x) |- _ => rewrite Hn in Hp; contradiction end. }
  Intros. rename H6 into Hdm0.
  (* the loop *)
  forward_loop (EX off: Z, EX u: Z, EX oc: list val, EX fs1: fstate, EX m: Z, EX qv: val, EX dcur: dfields,
    EX lxb: list Z,
    PROP (mf_pi pr sp d l tbl shk a fs s cap off u oc fs1 m qv dcur; mf_l a pr (tabs_lxb tabs) s cap off u lxb)
    LOCAL (temp _moreThan1Frame (Vint (Int.repr m)); temp _dststart dst;
      lvar _zfh (Tstruct ___gp_ZSTD_FrameHeader noattr) v_zfh;
      lvar _srcSize tulong v_srcSize; lvar _src (tptr tvoid) v_src; gvars gv; temp _dctx p;
      temp _dst (offset_val u dst); temp _dstCapacity (Vlong (Int64.repr (cap - u)));
      temp _dict (darg_dictv a); temp _dictSize (Vlong (Int64.repr (darg_dsize a))); temp _ddict qv)
    SEP (data_at_ Tsh (Tstruct ___gp_ZSTD_FrameHeader noattr) v_zfh;
      data_at Tsh tulong (Vlong (Int64.repr (Zlength s - off))) v_srcSize;
      data_at Tsh (tptr tvoid) (offset_val off src) v_src; pws_pred W; zstd_globals gv;
      fgroup3 TABS gv p fs1 (TUninit lxb) pr sp; msel_res DENT gv p pr sp dcur l tbl shk a am hb;
      darg_res3 DENT gv pr sp d a; data_at shd (tarray tuchar cap) oc dst;
      data_at shs (tarray tuchar (Zlength s)) (zbytes s) src;
      field_at Ews t_dctx (DOT _streamStage) (Vint (Int.repr 0)) p))%assert
  break: (EX off: Z, EX u: Z, EX oc: list val, EX fs1: fstate, EX m: Z, EX qv: val, EX dcur: dfields,
    EX lxb: list Z,
    PROP (mf_pi pr sp d l tbl shk a fs s cap off u oc fs1 m qv dcur; mf_l a pr (tabs_lxb tabs) s cap off u lxb;
          Zlength s - off < starting_len (dp_fmt pr =? 1))
    LOCAL (temp _dststart dst; lvar _zfh (Tstruct ___gp_ZSTD_FrameHeader noattr) v_zfh;
      lvar _srcSize tulong v_srcSize; lvar _src (tptr tvoid) v_src; gvars gv; temp _dst (offset_val u dst))
    SEP (data_at_ Tsh (Tstruct ___gp_ZSTD_FrameHeader noattr) v_zfh;
      data_at Tsh tulong (Vlong (Int64.repr (Zlength s - off))) v_srcSize;
      data_at Tsh (tptr tvoid) (offset_val off src) v_src; pws_pred W; zstd_globals gv;
      fgroup3 TABS gv p fs1 (TUninit lxb) pr sp; msel_res DENT gv p pr sp dcur l tbl shk a am hb;
      darg_res3 DENT gv pr sp d a; data_at shd (tarray tuchar cap) oc dst;
      data_at shs (tarray tuchar (Zlength s)) (zbytes s) src;
      field_at Ews t_dctx (DOT _streamStage) (Vint (Int.repr 0)) p))%assert.
  { (* entry *)
    Exists 0 0 (Zrepeat Vundef cap) fs 0 (darg_ddict a) d (tabs_lxb tabs). entailer!. 2: cancel.
    split; [| apply mf_l_init].
    pose proof (Zlength_nonneg s). apply Build_mf_pi; rewrite ?mf_dict_q0; first [apply mf_x_init | lia | list_solve | (exists nil; split; [constructor | split; [reflexivity | list_solve]])
        | apply series_inv_init | (left; reflexivity) | solve [auto] | (intros; lia) | (intros; apply codes_inv_init) | (intros Hx; discriminate Hx)]. }
  { (* the loop body *)
    Intros off u oc fs1 m qv dcur lxb. rename H6 into HI, H7 into HL.
    pose proof HI as [Hoff Hu Hoc Hm Hacc Hser Hcur Hqv Hdc Hloc Hfp Hds2 Hm0 Hd0 Hsf Hcd Hu0 Hcfs Hx].
    destruct Hacc as (acc & Hacc & Hlacc & Hsacc).
    unfold fgroup3, cfg_fmt. Intros. rename H6 into Hcold1. rename H7 into Hpar.
    pose proof Hpar as (Hfmt & _).
    forward. forward_call (dp_fmt pr). forward.
    assert (Hsl: 1 <= starting_len (fmt_mg (dp_fmt pr)) <= 5)
      by (unfold starting_len, fmt_mg, ZSTD_FRAMEHEADERSIZE_PREFIX; destruct (dp_fmt pr =? 1); lia).
    forward_if.
    2: { forward. Exists off u oc fs1 m qv dcur lxb. unfold fgroup3, cfg_fmt. entailer!. }
    rename H6 into Hlen. unfold fmt_mg in Hlen, Hsl.
    forward.
    match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?S))) _ _ =>
      forward_if (PROPx P (LOCALx (temp _t'8 (Vint (Int.repr (if dp_fmt pr =? 0 then 1 else 0))) :: L) (SEPx S))) end.
    { forward. forward. entailer!.
      assert (E0: dp_fmt pr = 0) by (destruct Hfmt as [E|E]; rewrite E in *; auto; discriminate).
      rewrite E0 in *. unfold starting_len, ZSTD_FRAMEHEADERSIZE_PREFIX in Hlen. cbn in Hlen.
      unfold Int64.cmpu. rewrite ltu64_repr by rep_lia.
      replace (Zlength s - off <? 4) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
    { forward. entailer!.
      destruct Hfmt as [E|E]; rewrite E in *; [contradiction | reflexivity]. }
    pose proof (win_ok_suffix63 shs s off SH0 H3 H2 Hoff) as Hwin.
    match goal with |- semax _ (PROPx ?P (LOCALx (_ :: ?L) (SEPx ?S))) _ _ =>
      forward_if (PROPx (((dp_fmt pr =? 1) = true \/ is_skippable_magic (le_field (sublist off (Zlength s) s) 0 4) = false) :: P)
                    (LOCALx L (SEPx S))) end.
    { (* zstd1: the magic number *)
      assert (E0: dp_fmt pr = 0).
      { destruct Hfmt as [E|E]; auto. rewrite E in *. simpl in H6. contradiction. }
      rewrite E0 in Hlen. unfold starting_len, ZSTD_FRAMEHEADERSIZE_PREFIX in Hlen. cbn [Z.eqb] in Hlen.
      forward.
      forward_call (shs, src, s, off).
      { unfold mem_read_pre. repeat split; auto; try lia. apply bytes_ok_sublist. auto. }
      rewrite (le_field_sublist4 s off) by lia.
      pose proof (le_field_4_range (sublist off (Zlength s) s) 0 (bytes_ok_sublist _ _ _ H3)) as Hmr.
      forward. dloop.
      forward_if.
      { (* a skippable frame *)
        match goal with Hm: Int.and _ _ = _ |- _ => apply magic_test in Hm; [| auto]; rename Hm into Hsk end.
        forward. forward.
        forward_call (shs, src, Zlength s, zbytes s, off, sublist off (Zlength s) s).
        { entailer!. rewrite Zlength_sublist by lia. reflexivity. }
        Intros r. forward.
        match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?S))) _ _ =>
          forward_loop (PROPx P (LOCALx L (SEPx S)))
            continue: (PROPx ((is_error_code r = false) :: P) (LOCALx L (SEPx S)))
            break: (PROPx ((is_error_code r = false) :: P) (LOCALx L (SEPx S))) end.
        { apply ENTAIL_refl. }
        { forward. forward_call r.
          forward_if.
          - dloop. dloop. dloop. dloop. forward.
            Exists r oc fs1 dcur lxb. unfold fgroup3, cfg_fmt. entailer!.
            assert (He: is_error_code r = true) by (destruct (is_error_code r); auto; contradiction).
            match goal with Hx: match skippable_frame_size _ with _ => _ end |- _ => rename Hx into Hskr end.
            assert (Hsk0: skippable_frame_size (sublist off (Zlength s) s) = None).
            { destruct (skippable_frame_size (sublist off (Zlength s) s)) eqn:Ek; auto.
              simpl in Hskr. subst.
              pose proof (skippable_frame_size_bound _ _ (bytes_ok_sublist _ _ _ H3) Ek) as Hb8.
              rewrite Zlength_sublist in Hb8 by lia.
              unfold is_error_code in He. apply Z.ltb_lt in He. rep_lia. }
            rewrite Hsk0 in Hskr.
            assert (HLp: mf_lpost a pr (tabs_lxb tabs) s (Zlength oc) lxb)
              by (eapply mf_l_skip_post; eauto; lia).
            assert (Hmg0: md_magicless (dmode_of pr) = false)
              by (unfold dmode_of; cbn [md_magicless]; rewrite E0; reflexivity).
            apply conj_last11; [| exact HLp].
            apply mf_err_post2; auto; [ | lia | | ].
            { eapply series_err_unk; [exact Hser |]. intros _.
              apply decode_seriesS_skip_bad; auto; [rewrite Zlength_sublist by lia; unfold ZSTD_FRAMEHEADERSIZE_PREFIX; lia]. }
            { intros Hn. eapply codes_dead; [ | | exact (Hcd Hn)]; intros c Hc.
              - exact (dead_skip_ck _ _ _ _ _ Hmg0 Hsk Hsk0 Hc).
              - refine (dead_skip_rr _ _ _ _ _ Hmg0 Hsk Hsk0 _ Hc). rewrite Zlength_sublist by lia; lia. }
            { exact (mf_x_skip_err a pr s (Zlength oc) off (Zlength acc) oc Hx H3 ltac:(lia)
                ltac:(unfold ZSTD_FRAMEHEADERSIZE_PREFIX; lia) Hsk Hsk0). }
          - forward. entailer!.
            destruct (is_error_code r); auto. exfalso. apply Int.one_not_zero. auto. }
        { forward. entailer!. }
        Intros. match goal with Hx: is_error_code r = false |- _ => rename Hx into Hre end.
        forward. forward.
        forward. forward.
        forward.
        match goal with Hx: match skippable_frame_size _ with _ => _ end |- _ => rename Hx into Hskr end.
        assert (Hskr': match skippable_frame_size (sublist off (Zlength s) s) with
                      | Some k => r = k | None => is_error_code r = true end)
          by (destruct (skippable_frame_size (sublist off (Zlength s) s)); auto; destruct Hskr; auto).
        destruct (skip_size_ok s off r H3 Hoff Hskr' Hre) as [Hk Hr]. clear Hskr'.
        Exists (off + r) u oc fs1 m qv dcur lxb. unfold fgroup3, cfg_fmt. entailer!.
        - split; [apply mf_pi_skip; auto; unfold ZSTD_FRAMEHEADERSIZE_PREFIX; lia |].
          eapply mf_l_skip; eauto; lia.
        - replace (Zlength s - off - r) with (Zlength s - (off + r)) by lia. cancel. }
      { forward. entailer!. right.
        destruct (is_skippable_magic (le_field (sublist off (Zlength s) s) 0 4)) eqn:Em; auto.
        exfalso. apply magic_test in Em; auto. }
    }
    { forward. entailer!. left.
      destruct Hfmt as [E|E]; rewrite E in *; [discriminate | reflexivity]. }
    Intros. match goal with Hx: (dp_fmt pr =? 1) = true \/ _ |- _ => rename Hx into Hmg end.
    assert_PROP (sel_on pr sp = true -> hs_inv l tbl) as Hhs.
    { sep_apply (mf_hs DENT gv p pr sp dcur l tbl shk a am hb). entailer!. }
    assert (Hg1: sel_on pr sp = true -> darg_local d a = true -> ~ In (darg_ddict a) (map fst l))
      by (intros Hs; exact (mf_gap_G1 W d l a shk shd cap dst (H5 Hs))).
    assert (Hsb: bytes_ok (sublist off (Zlength s) s)) by (apply bytes_ok_sublist; auto).
    assert (Hsl2: starting_len (dp_fmt pr =? 1) <= Zlength (sublist off (Zlength s) s))
      by (rewrite Zlength_sublist by lia; lia).
    forward_if (mf_ab3 DENT TABS gv p W pr sp d l tbl shk a s cap shd dst shs src v_src v_srcSize v_zfh
                  off u oc fs1 m qv dcur am hb lxb).
    { entailer!. apply denote_tc_test_eq_split; [| apply valid_pointer_null].
      sep_apply (mf_qv_valid DENT gv p pr sp d l tbl shk a W shd _ dst dcur qv am hb H5 Hg1 Hqv Hdc Hloc).
      apply extend_valid_pointer. }
    { (* a DDict: fix F4's probe, then ZSTD_decompressBegin_usingDDict *)
      rename H6 into Hqvp.
      assert (Hq0: darg_ddict a <> nullval).
      { destruct Hqv as [Eq | (_ & Hn & _)]; auto. rewrite <- Eq. intro N. rewrite N in Hqvp. exact Hqvp. }
      forward.
      match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?S))) _ _ =>
        forward_if (PROPx P (LOCALx (temp _t'11 (Vint (Int.repr (if sel_on pr sp then 1 else 0))) :: L) (SEPx S))) end.
      { assert (Hm1: dp_multi pr = 1) by (destruct Hpar as (_ & _ & _ & _ & [E|E]); rewrite E in *; auto; discriminate).
        assert_PROP (is_pointer_or_null sp) as Hspn by (sep_apply (mf_sp_pon DENT gv p pr sp dcur l tbl shk a am hb Hm1); entailer!).
        forward. forward.
        { entailer!. apply denote_tc_test_eq_split; [| apply valid_pointer_null].
          sep_apply (mf_sp_valid DENT gv p pr sp dcur l tbl shk a am hb Hm1 Hspn). apply extend_valid_pointer. }
        entailer!. unfold sel_on. rewrite Hm1. cbn [Z.eqb Pos.eqb andb].
        destruct sp; try contradiction; simpl in Hspn |- *; [subst; reflexivity|].
        unfold veqb. destruct (Val.eq _ _); [discriminate | reflexivity]. }
      { forward. entailer!. unfold sel_on.
        replace (dp_multi pr =? 1) with false; [reflexivity|]. symmetry. apply Z.eqb_neq. intro E. rewrite E in *. contradiction. }
      forward_if (mf_pp DENT TABS gv p W pr sp d l tbl shk a s cap shd dst shs src v_src v_srcSize v_zfh
                    off u oc fs1 m qv dcur am hb lxb).
      { (* the probe *)
        assert (Hs: sel_on pr sp = true) by (destruct (sel_on pr sp); auto; contradiction).
        assert (Hm1: dp_multi pr = 1)
          by (unfold sel_on in Hs; apply andb_prop in Hs; destruct Hs as [Hs _]; apply Z.eqb_eq; auto).
        assert_PROP (is_pointer_or_null sp) as Hspn
          by (sep_apply (mf_sp_pon DENT gv p pr sp dcur l tbl shk a am hb Hm1); entailer!).
        forward. forward. forward.
        forward_call (gv, Tsh, v_zfh, default_val (Tstruct ___gp_ZSTD_FrameHeader noattr), shs, src,
                      Zlength s, zbytes s, off, sublist off (Zlength s) s, dp_fmt pr).
        { entailer!. rewrite Zlength_sublist by lia. reflexivity. }
        Intros vret. destruct vret as [r v]. cbn [fst snd] in *.
        match goal with Hx: fh_post_m _ _ _ _ _ |- _ => rename Hx into Hfh end. unfold fmt_mg in Hfh.
        forward_if.
        { (* a header: the set's DDict of its Dictionary_ID *)
          destruct (fh_post_zero _ _ _ _ _ Hsb Hfh) as (h & Hh & ->).
          { match goal with Hx: Int64.repr r = _ |- _ => apply (f_equal Int64.unsigned) in Hx end.
            rewrite Int64.unsigned_repr in * by rep_lia. auto. }
          forward. forward.
          destruct (mf_probe_split DENT gv p pr sp d l tbl shk a W shd cap dst dcur am hb Hs (H5 Hs) (Hg1 Hs) Hdc)
            as (MK0 & HP1 & HP2).
          sep_apply HP1.
          pose proof (gfh3_range _ _ _ Hsb Hh) as (_ & _ & _ & _ & Hid).
          forward_call (sp, l, tbl, fh_dictID h, am).
          { cancel. }
          pose proof (hs_probe_in l tbl (fh_dictID h) (Hhs Hs)) as Hpin.
          pose proof (mf_probe_hit pr sp a l tbl qv _ h Hs Hq0 Hh) as Hph.
          remember (hs_probe l tbl (fh_dictID h)) as X eqn:HX. clear HX.
          forward.
          forward_if (mf_pp DENT TABS gv p W pr sp d l tbl shk a s cap shd dst shs src v_src v_srcSize v_zfh
                        off u oc fs1 m qv dcur am hb lxb).
          { entailer!. apply denote_tc_test_eq_split; [| apply valid_pointer_null].
            destruct (eq_dec X nullval) as [E|E].
            - rewrite E. apply valid_pointer_null.
            - sep_apply (set_ids_valid l _ (Hpin E)). apply extend_valid_pointer. }
          { forward. sep_apply HP2. sep_apply (data_at_data_at_ Tsh t_fh (fh_val h) v_zfh).
            unfold mf_pp. rewrite Hph.
            rewrite if_false by (intro E; rewrite E in *; contradiction). entailer!. }
          { forward. sep_apply HP2. sep_apply (data_at_data_at_ Tsh t_fh (fh_val h) v_zfh).
            unfold mf_pp. rewrite Hph. rewrite if_true by auto. entailer!. } }
        { forward.
          assert (Hnh: forall h, get_frame_header_m (dp_fmt pr =? 1) (sublist off (Zlength s) s) <> FH_ok h).
          { apply (fh_post_nz _ _ _ _ _ Hfh). intro E. subst r.
            match goal with Hx: Int64.repr 0 <> _ |- _ => apply Hx; reflexivity end. }
          sep_apply (data_at_data_at_ Tsh (Tstruct ___gp_ZSTD_FrameHeader noattr) v v_zfh).
          unfold mf_pp. rewrite (mf_probe_nohdr pr sp a l tbl qv _ Hnh). entailer!. } }
      { forward. unfold mf_pp. rewrite mf_probe_off.
        2:{ destruct (sel_on pr sp); [exfalso; apply Int.one_not_zero; auto | reflexivity]. }
        entailer!. }
      unfold mf_pp.
      remember (mf_probe pr sp a l tbl qv (sublist off (Zlength s) s)) as qv' eqn:Hqv'.
      assert (Hqv'ok: qv_ok pr sp a l qv') by (subst qv'; apply mf_probe_ok; auto).
      assert (Hpp: forall h, get_frame_header_m (dp_fmt pr =? 1) (sublist off (Zlength s) s) = FH_ok h ->
                sel_on pr sp = true -> darg_ddict a <> nullval ->
                hs_probe l tbl (fh_dictID h) = nullval \/ hs_probe l tbl (fh_dictID h) = qv')
        by (intros; subst qv'; apply mf_probe_pp; auto).
      assert (Hloc': darg_local d a = true -> qv' = darg_ddict a -> dcur = d).
      { intros Hl Eq. apply Hloc; auto. subst qv'. eapply mf_probe_loc; eauto. }
      destruct (mf_dict_ddict pr sp a l shk qv' Hq0 Hqv'ok) as (x & buf & sh & Ha' & Hxq).
      pose proof (mf_split DENT gv p pr sp d l tbl shk a W shd cap dst dcur qv' (sublist off (Zlength s) s) am hb
        H5 H4 Hg1 Hhs Hqv'ok Hdc Hloc' Hsb Hsl2 Hmg Hpp) as HS. cbv zeta in HS.
      destruct HS as (MK & MK2 & xq & lent & Hcx & Hlt & Hll & S1 & Swf & S2 & S3 & S4).
      rewrite Ha' in Hlt, S1, Swf, S2, S3, S4. cbn [begin_res darg_ox] in *.
      sep_apply S1.
      assert_PROP (darg_wf (DA_ddict x buf sh) /\ darg_ok3 W (DA_ddict x buf sh) shd cap dst) as Hwo
        by (sep_apply Swf; entailer!).
      destruct Hwo as [Hwf' Hok'].
      assert (Hdm: exists dm, ddx_model x = Some dm).
      { destruct Hwf' as (_ & _ & _ & Hraw & _). unfold ddx_model. destruct (dx_raw x); [eauto|].
        destruct Hraw as [Hraw|Hraw]; [discriminate|]. destruct (dict_auto_c _ _); [eauto | congruence]. }
      destruct Hdm as [dm Hdm].
      match goal with |- semax _ ?P _ _ =>
        forward_loop P continue: (mf_ab3 DENT TABS gv p W pr sp d l tbl shk a s cap shd dst shs src v_src v_srcSize v_zfh off u oc fs1 m qv dcur am hb lxb)
          break: (mf_ab3 DENT TABS gv p W pr sp d l tbl shk a s cap shd dst shs src v_src v_srcSize v_zfh off u oc fs1 m qv dcur am hb lxb) end.
      { apply ENTAIL_refl. }
      { fold (cfg_fmt p (dp_fmt pr)).
        cbn [tabs_rep]. rewrite <- Hxq.
        forward_call (gv, p, fs1, W, Some x, buf, dp_fmt pr, lxb).
        { cancel. }
        Intros cold.
        forward_call 0.
        forward_if.
        { exfalso. match goal with Hz: Int.repr _ <> Int.zero |- _ => apply Hz; reflexivity end. }
        forward.
        destruct (ddx_model_facts _ _ Hdm) as (_ & Hst & _).
        unfold mf_ab3. Exists qv' cold dm MK2 xq lent (mk_tstate (ddx_state x) false lxb).
        rewrite Ha'. rewrite Hst. rewrite <- Hxq. 
        sep_apply (S3 dm).
        cbn [fs_after_begin darg_ox]. entailer!.
        split; [intros Hl; destruct (Hlt Hl) as [Hl1 Hl2]; split; auto |].
        split; [intros; apply Hll; auto; congruence |].
        split; [intros; apply Hloc'; auto; congruence |].
        intros Hn. split; [| exact Hdm].
        apply (mf_frame_dict2 pr sp a l tbl shk qv _ dm W d shd _ dst Hhs H5); [| apply Hcur; auto].
        rewrite ?Ha'. exact Hdm. }
      { forward. apply ENTAIL_refl. }
      { subst POSTCONDITION; unfold abbreviate; simpl RA_normal; apply ENTAIL_refl. } }
    { (* no DDict: ZSTD_decompressBegin_usingDict *)
      rename H6 into Hqn.
      assert (Hq0: darg_ddict a = nullval).
      { destruct Hqv as [Eq | (Hs & _ & Hin)]; [rewrite <- Eq; auto |]. exfalso.
        destruct (Hhs Hs) as (_ & _ & _ & _ & _ & Hptr & _).
        apply list_in_map_inv in Hin. destruct Hin as (e & Ee & Hin).
        rewrite Forall_forall in Hptr. specialize (Hptr e Hin). rewrite <- Ee, Hqn in Hptr. exact Hptr. }
      assert (Hpp: forall h, get_frame_header_m (dp_fmt pr =? 1) (sublist off (Zlength s) s) = FH_ok h ->
                sel_on pr sp = true -> darg_ddict a <> nullval ->
                hs_probe l tbl (fh_dictID h) = nullval \/ hs_probe l tbl (fh_dictID h) = qv)
        by (intros; contradiction).
      pose proof (mf_split DENT gv p pr sp d l tbl shk a W shd cap dst dcur qv (sublist off (Zlength s) s) am hb
        H5 H4 Hg1 Hhs Hqv Hdc Hloc Hsb Hsl2 Hmg Hpp) as HS. cbv zeta in HS.
      destruct HS as (MK & MK2 & xq & lent & Hcx & Hlt & Hll & S1 & Swf & S2 & S3 & S4).
      assert (Ha': mf_dict a l shk qv = a) by (rewrite Hqn, <- Hq0; apply mf_dict_q0).
      assert (Hfd: forall dm, darg_model (mf_dict a l shk qv) = Some dm ->
        frame_dict (dp_fmt pr =? 1) (mf_sel pr sp a l tbl) (darg_model (mf_dict a l shk qv)) (sublist off (Zlength s) s) = Some dm).
      { intros dm E. apply (mf_frame_dict2 pr sp a l tbl shk qv _ dm W d shd cap dst Hhs H5); [| congruence].
        rewrite mf_probe_off; auto. rewrite Hq0. unfold veqb. destruct (Val.eq nullval nullval); [| congruence].
        destruct (sel_on pr sp); reflexivity. }
      rewrite Ha' in *.
      sep_apply S1.
      assert_PROP (darg_wf a /\ darg_ok3 W a shd cap dst) as Hwo by (sep_apply Swf; entailer!).
      destruct Hwo as [Hwf' Hok'].
      destruct a as [| sh pk b | x buf sh].
      3: { exfalso. destruct Hwf' as [Hqp _]. simpl in Hq0. rewrite Hq0 in Hqp. exact Hqp. }
      - (* no dictionary *)
        cbn [begin_res darg_dictv darg_dict darg_dsize darg_size darg_ox] in *.
        match goal with |- semax _ ?P _ _ =>
          forward_loop P continue: (mf_ab3 DENT TABS gv p W pr sp d l tbl shk DA_none s cap shd dst shs src v_src v_srcSize v_zfh off u oc fs1 m qv dcur am hb lxb)
            break: (mf_ab3 DENT TABS gv p W pr sp d l tbl shk DA_none s cap shd dst shs src v_src v_srcSize v_zfh off u oc fs1 m qv dcur am hb lxb) end.
        { apply ENTAIL_refl. }
        { fold (cfg_fmt p (dp_fmt pr)). cbn [tabs_rep].
          forward_call (gv, p, fs1, W, Tsh, nullval, @nil Z, dp_fmt pr, lxb).
          { rewrite if_true by auto. cancel. }
          { repeat split; auto; try (rewrite Zlength_nil; rep_lia); try constructor. }
          Intros vret. destruct vret as [r ores]. cbn [fst snd] in *. unfold usingdict_model.
          rewrite !if_true by auto. Intros x2. subst r.
          forward_call 0.
          forward_if.
          { exfalso. match goal with Hz: Int.repr _ <> Int.zero |- _ => apply Hz; reflexivity end. }
          forward.
          unfold mf_ab3. Exists qv (fs_ddictIsCold fs1) no_dict MK2 xq lent (mk_tstate (dm_state no_dict) x2 lxb).
          rewrite Ha'. sep_apply (S3 no_dict).
          cbn [fs_after_begin darg_ox dm_state]. entailer!.
          all: destruct (Hlt ltac:(auto)) as [Hl1 Hl2]; split; auto. }
        { forward. apply ENTAIL_refl. }
        { subst POSTCONDITION; unfold abbreviate; simpl RA_normal; apply ENTAIL_refl. }
      - (* the caller's bytes *)
        cbn [begin_res darg_dictv darg_dict darg_dsize darg_size darg_ox] in *.
        pose proof Hwf' as (Hsh & Hlb & Hb & Hpk & _).
        assert (Hpkn: pk <> nullval) by (destruct pk; try contradiction; discriminate).
        match goal with |- semax _ ?P _ _ =>
          forward_loop P continue: (mf_ab3 DENT TABS gv p W pr sp d l tbl shk (DA_dict sh pk b) s cap shd dst shs src v_src v_srcSize v_zfh off u oc fs1 m qv dcur am hb lxb)
            break: (mf_ab3 DENT TABS gv p W pr sp d l tbl shk (DA_dict sh pk b) s cap shd dst shs src v_src v_srcSize v_zfh off u oc fs1 m qv dcur am hb lxb) end.
        { apply ENTAIL_refl. }
        { fold (cfg_fmt p (dp_fmt pr)). cbn [tabs_rep].
          sep_apply (pws_fold1 W shd cap oc dst).
          forward_call (gv, p, fs1, W ++ [pw_bytes shd cap oc dst], sh, pk, b, dp_fmt pr, lxb).
          { rewrite if_false by auto. cancel. }
          { pose proof H4 as (_ & Hlb28 & _ & Hdp).
            repeat split; auto. right. apply dict_buf_ok_ext_any; [exact Hdp | auto]. }
          Intros vret. destruct vret as [r ores]. cbn [fst snd] in *.
          match goal with H: ld_rel b ores |- _ => rename H into Hld end. rewrite if_false by auto.
          destruct (usingdict_model pk b ores) as [dm |] eqn:Eu.
          + Intros x2. subst r. sep_apply (pws_unfold1 W shd cap oc dst).
            forward_call 0.
            forward_if.
            { exfalso. match goal with Hz: Int.repr _ <> Int.zero |- _ => apply Hz; reflexivity end. }
            forward.
            destruct (usingdict_dict sh pk b ores dm fs1 (fs_ddictIsCold fs1) (dp_fmt pr) Hpk Hld Eu) as [Ed Efs].
            unfold mf_ab3. Exists qv (fs_ddictIsCold fs1) dm MK2 xq lent (mk_tstate (dm_state dm) x2 lxb).
            rewrite Ha'. sep_apply (S3 dm). rewrite Efs.
            cbn [darg_ox]. entailer!.
            { split; [intros Hl; destruct (Hlt Hl) as [Hl1 Hl2]; split; auto |].
              intros Hn. destruct (darg_model (DA_dict sh pk b)) as [dm0|] eqn:Em; [| contradiction].
              rewrite (darg_c_model _ _ _ Ed Em) in *. split; auto. }
            { rewrite if_false by auto. apply derives_refl. }
          + (* a corrupted formatted dictionary: Begin fails *)
            Intros fs'. sep_apply (pws_unfold1 W shd cap oc dst).
            match goal with Hd: dec_err r |- _ => rename Hd into Hder end.
            assert (He: is_error_code r = true) by (destruct Hder; auto).
            forward_call r.
            forward_if.
            2: { exfalso. match goal with Hz: Int.repr _ = Int.zero |- _ =>
                   rewrite He in Hz; apply Int.one_not_zero; exact Hz end. }
            dloop. dloop. dloop. dloop.
            forward.
            assert (Hfpg: fp_ok (fs_fParams fs) -> fp_ok (fs_fParams fs')).
            { intros Hp. match goal with Hx: fs_fParams fs' = fs_fParams fs1 |- _ => rewrite Hx end. auto. }
            Exists r oc fs' dcur lxb. sep_apply S2. sep_apply (tabs_rep_uninit_intro TABS gv p lxb). unfold fgroup3. entailer!.
            assert (Hda: dict_auto b = None).
            { unfold usingdict_model in Eu. rewrite if_false in Eu by auto.
              destruct (Zlength b =? 0); [discriminate | eapply ld_rel_auto_none; eauto]. }
            repeat match goal with |- _ /\ _ => split end;
              first [ (intros _; simpl darg_model; rewrite Hda; apply oneshot_codes_none; lia)
                    | (intros _ Hx; exfalso; apply Hx; reflexivity)
                    | (intros _; unfold oneshot_ok; simpl darg_model; rewrite Hda; split; auto; rewrite He; discriminate)
                    | (unfold cold01; match goal with Hx: fs_ddictIsCold fs' = fs_ddictIsCold fs1 |- _ => rewrite Hx end;
                       exact Hcold1)
                    | (intros Hx; rewrite He in Hx; discriminate) | (intros Hx; discriminate Hx) | auto ]. }
        { forward. apply ENTAIL_refl. }
        { subst POSTCONDITION; unfold abbreviate; simpl RA_normal; apply ENTAIL_refl. } }
    (* checkContinuity *)
    unfold mf_ab3. Intros qv' cold dm MK2 xq lent ts.
    match goal with H: ts_lxb ts = lxb |- _ => rename H into Htl end.
    (* litExtraBuffer has its full size: the exact model's lxb_ok *)
    assert_PROP (Zlength (ts_lxb ts) = LITEXTRA_N) as Htsl.
    { sep_apply (HTABS gv p (darg_ox (mf_dict a l shk qv')) ts). unfold tables_uninit, lit_extra_at. entailer!. }
    match goal with H: ts_d ts = dm_state dm |- _ => rename H into Hts end.
    match goal with H: darg_c _ dm |- _ => rename H into Hdc' end.
    match goal with H: cold_ok cold |- _ => rename H into Hcold end.
    match goal with H: darg_wf _ |- _ => rename H into Hwf' end.
    match goal with H: darg_ok3 W _ shd cap dst |- _ => rename H into Hok' end.
    match goal with H: sel_on pr sp = true -> cur_ok dcur l xq |- _ => rename H into Hcx end.
    match goal with H: lent = true -> lent_ok _ _ _ _ _ _ _ /\ _ |- _ => rename H into Hlt end.
    match goal with H: darg_local d a = true -> qv' = _ -> sel_on _ _ = true -> lent = true |- _ => rename H into Hll end.
    match goal with H: darg_local d a = true -> qv' = _ -> dcur = d |- _ => rename H into Hloc' end.
    match goal with H: forall dcur', dict_after _ _ _ _ _ -> _ |- _ => rename H into S4 end.
    match goal with H: darg_model a <> None -> frame_dict _ _ _ _ = _ /\ _ |- _ => rename H into Hfd end.
    match goal with H: qv_ok pr sp a l qv' |- _ => rename H into Hqv' end.
    remember (mf_dict a l shk qv') as a' eqn:Ea'.
    assert (Hc1: cold_ok (fs_ddictIsCold fs1)) by exact Hcold1.
    destruct (begin_fields a' fs1 cold dm (dp_fmt pr) Hdc' Hwf' Hc1 Hcold) as (Hfd1 & Hfc & Hfid & Hidr & Hpcs & Hgp).
    assert_PROP (field_compatible (tarray tuchar cap) [] dst) as Hfcd by entailer!.
    sep_apply (wcont_fold W shd cap oc dst a' dm).
    destruct (cont_pre W shd cap oc dst a' fs1 cold dm (dp_fmt pr) u Hok' Hwf' Hdc' Hoc Hfcd (writable_readable SH) Hu) as [Hcp1 Hcp2].
    forward_call (p, fs_after_begin a' fs1 cold dm (dp_fmt pr), wcont W shd cap oc dst a' dm, offset_val u dst, cap - u).
    sep_apply (wcont_unfold W shd cap oc dst a' dm).
    Intros.
    rewrite (split_out shd cap oc dst u) by auto.
    sep_apply (pws_fold1 W shd u (sublist 0 u oc) dst).
    unfold mf_fsel.
    gather_SEP (cfg_fmt p _) (cfg_lit p) (frame_fields p _) (field_at Ews t_dctx (DOT _forceIgnoreChecksum) _ p)
      (field_at Ews t_dctx (DOT _maxBlockSizeParam) _ p) (field_at Ews t_dctx (DOT _refMultipleDDicts) _ p)
      (field_at Ews t_dctx (DOT _ddictSet) _ p).
    replace_SEP 0 (fcore3 p (continuity (fs_after_begin a' fs1 cold dm (dp_fmt pr)) (offset_val u dst) (cap - u)) pr sp)
      by (unfold fcore3; entailer!).
    replace (Zlength s - off) with (Zlength (sublist off (Zlength s) s)) by (rewrite Zlength_sublist; lia).
    (* the frame's output array: dst's rest, or with the dictionary as its prefix [dict | dst] (gap0) *)
    assert (Hdp: isptr dst) by (destruct Hfcd; auto).
    sep_apply (mf_pre_sep W shd cap oc dst a' dm u Hok' Hwf' Hoc Hfcd ltac:(lia)).
    destruct (mf_oa_dst a' shd cap oc dst u Hdp) as [Eod Eoc].
    pose proof (mf_lent pr sp dcur l tbl a' dm dst cap u (sublist off (Zlength s) s) lent Hlt) as Hlt'.
    pose proof (sel_mem_dc pr sp l d dcur am hb Hdc Hsm) as Hsmc.
    forward_call (W ++ [pw_bytes shd u (sublist 0 u oc) dst], gv, p,
      continuity (fs_after_begin a' fs1 cold dm (dp_fmt pr)) (offset_val u dst) (cap - u), darg_ox a', dm,
      mf_e a' dm dst cap u, mf_oa a' shd cap oc dst u,
      Build_inwin shs src (Zlength s) (zbytes s) off (sublist off (Zlength s) s), v_src, v_srcSize,
      pr, sp, dcur, l, tbl, xq, lent, am, hb, ts).
    { entailer!. rewrite Eod, Eoc. auto. }
    { cancel. }
    { destruct (continuity_keeps (fs_after_begin a' fs1 cold dm (dp_fmt pr)) (offset_val u dst) (cap - u)) as (K1 & K2 & K3 & K4).
      rewrite K1, K2, K3, K4.
      split; [eapply mf_oa_ok; eauto; lia |].
      split; [apply mf_e_not_in |].
      split; [auto | split; [exact Hfc | split; [auto | split; [auto | split]]]].
      - intros Hz. apply (mf_wv W shd cap oc dst a' u); auto; lia.
      - split; [apply hist_ptrs_mf; auto |].
        split; [eapply darg_c_content; eauto |].
        split; [eapply ext_def_mf; eauto |].
        split; [eapply ext0_mf; eauto |].
        first [ intros Hp; rewrite Eoc in Hp; eapply cont_layout_any; eauto; lia
              | split; [intros Hp; rewrite Eoc in Hp; eapply cont_layout_any; eauto; lia | exact Hts] ]. }
    Intros vret. destruct vret as [[[[[r oc0] fs'] k] d'] lxbf]. cbn [fst snd iw_sh iw_base iw_N iw_c iw_off iw_s] in *.
    (* the frame's exact claim, on dst's part of its output *)
    match goal with Hx: darg_ox a' = None -> _ -> _ -> _ -> frame_exact _ _ _ _ _ _ _ _ |- _ =>
      pose proof (mf_fx_l pr sp a l shk qv' a' dm ts _ shd cap oc dst u r oc0 k lxbf Ea' Hqv' Hdc' Hx) as Hfxl;
      pose proof (mf_fx pr sp a l shk qv' a' dm ts _ shd cap oc dst u r oc0 k lxbf Ea' Hqv' Hdc' Htsl Hx) as Hfx;
      clear Hx end.
    (* the frame leaves the tables uninitialised, litExtraBuffer holding lxbf *)
    sep_apply (tabs_rep_uninit_intro TABS gv p lxbf).
    (* back to dst's part oc' of the frame's output *)
    match goal with Hx: Zlength oc0 = _ |- _ => rename Hx into Hl0 end.
    match goal with Hx: unchanged_outside _ oc0 _ _ |- _ => rename Hx into Hun0 end.
    sep_apply (mf_post_sep W shd cap oc dst a' dm u oc0 Hok' Hwf' Hoc Hfcd ltac:(lia) Hl0 Hun0).
    destruct (mf_back_facts a' shd cap oc dst u oc0 ltac:(lia) Hoc Hl0) as [Hlb Hsbk].
    match goal with Hx: is_error_code r = false -> r <= _ /\ _ |- _ => rewrite Eoc in Hx; rename Hx into Hok0 end.
    match goal with Hx: 0 <= r <= Int64.max_unsigned |- _ => rename Hx into Hr0 end.
    match goal with Hx: frame_res3 _ _ _ _ _ oc0 _ _ |- _ =>
      rewrite Eoc in Hx; apply (frame_res3_shift _ _ _ _ _ _ _ _ (mf_back a' dst cap u oc0)) in Hx;
      [| intros He; apply Hsbk; split; [lia | apply (proj1 (Hok0 He))]] end.
    match goal with Hx: is_error_code r = false -> exists c, _ |- _ =>
      assert (Hby0: is_error_code r = false -> exists c, bytes_ok c /\ Zlength c = r /\
                      sublist 0 (0 + r) (mf_back a' dst cap u oc0) = zbytes c)
        by (intros He; destruct (Hx He) as (c & Hcb0 & Hcl0 & Hcs0); exists c; split; [auto | split; [auto |]];
            rewrite Z.add_0_l, <- Hsbk; [auto | split; [lia | apply (proj1 (Hok0 He))]]);
      clear Hx end.
    clear Hl0 Hun0 Hsbk.
    set (oc' := mf_back a' dst cap u oc0) in *.
    match goal with Hx: frame_res3 _ _ _ _ _ _ _ _ |- _ => rename Hx into Hfr end.
    match goal with Hx: frame_codes3 _ _ _ _ _ |- _ => rewrite Eoc in Hx; rename Hx into Hfc3 end.
    match goal with Hx: Zlength oc' = _ |- _ => rename Hx into Hloc2 end.
    match goal with Hx: is_error_code r = false -> r <= _ /\ _ |- _ => rename Hx into Hok2 end.
    match goal with Hx: is_error_code r = false -> exists c, _ |- _ => rename Hx into Hby2 end.
    match goal with Hx: is_error_code r = true -> k = 0 /\ _ |- _ => rename Hx into Herr2 end.
    match goal with Hx: 0 <= r <= Int64.max_unsigned |- _ => rename Hx into Hr end.
    match goal with Hx: dict_after pr sp l dcur d' |- _ => rename Hx into Hda end.
    match goal with Hx: lent = true -> d' = dcur |- _ => rename Hx into Hlt2 end.
    match goal with Hx: fs_ddictIsCold fs' = _ \/ _ |- _ => rename Hx into Hcold' end.
    match goal with Hx: is_error_code r = false -> sel_on pr sp = true -> _ |- _ => rename Hx into Hds' end.
    match goal with Hx: fp_ok _ -> fp_ok (fs_fParams fs') |- _ => rename Hx into Hfp' end.
    match goal with Hx: dict_sel _ _ _ _ _ _ _ |- _ => rename Hx into Hdsel end.
    match goal with Hx: is_error_code r = false -> _ -> frame_compressed_size_m _ _ = Some k |- _ => rename Hx into Hfcsx end.
    unfold mf_fsel in S4.
    sep_apply (S4 d' Hda Hlt2).
    sep_apply (pws_unfold1 W shd u (sublist 0 u oc) dst). Intros.
    assert (Hfde: darg_model a <> None -> frame_dict (dp_fmt pr =? 1) (mf_sel pr sp a l tbl) (darg_model (mf_dict a l shk qv))
         (sublist off (Zlength s) s) = Some dm) by (intros Hn; exact (proj1 (Hfd Hn))).
    (* prefix_unknown after a frame: srcSize_wrong *)
    match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?S))) _ _ =>
      forward_loop (PROPx P (LOCALx L (SEPx S))) continue: (PROPx P (LOCALx L (SEPx S)))
        break: (PROPx P (LOCALx L (SEPx S))) end.
    { apply ENTAIL_refl. }
    { forward_call r.
      pose proof (error_of_range r Hr) as Her.
      match goal with |- semax _ (PROPx _ (LOCALx ?L (SEPx ?S))) _ _ =>
        forward_if (PROPx [] (LOCALx (temp _t'18 (Vint (Int.repr (if andb (error_of r =? 10) (m =? 1) then 1 else 0))) :: L)
                     (SEPx S))) end.
      { forward. entailer!.
        match goal with Hx: error_of r = 10 |- _ => rewrite Hx end.
        destruct Hm; subst m; reflexivity. }
      { forward. entailer!.
        replace (error_of r =? 10) with false; [reflexivity |].
        symmetry. apply Z.eqb_neq. intro E. rewrite E in *. contradiction. }
      forward_if.
      { (* srcSize_wrong: the frame failed with prefix_unknown after another frame *)
        assert (Hpu: error_of r = 10).
        { destruct (error_of r =? 10) eqn:E; [apply Z.eqb_eq; auto |].
          exfalso. match goal with Hz: Int.repr _ <> Int.zero |- _ => apply Hz; reflexivity end. }
        pose proof (error_of_10 r Hpu) as He10.
        pose proof (mf_x_ferr a pr s cap off u oc (ts_x ts) r oc' k Hx H3 ltac:(lia) Hu ltac:(lia) Hloc2 ltac:(lia)
          Hmg He10 Hfx) as Hxn.
        pose proof (mf_err_frame pr sp d l tbl shk a fs s cap off u oc fs1 m qv dcur dm r oc' k HI Hfde
          ltac:(lia) Hmg Hfr He10) as Hse.
        assert (Hcodes: darg_model a <> None ->
                  oneshot_codes (dmode_of pr) (mf_sel pr sp a l tbl) (darg_model a) s cap (2 ^ 64 - 72))
          by (intros Hn; exact (codes_exact_pu _ _ _ _ _ r _ (mf_codes_err pr sp d l tbl shk a fs s cap off u oc fs1 m
                qv dcur dm r oc' k HI Hfde ltac:(lia) Hmg Hfr Hfc3 He10 Hn) Hpu)).
        dloop. dloop. dloop. dloop.
        forward.
        assert (Hfpg: fp_ok (fs_fParams fs) -> fp_ok (fs_fParams fs')).
        { intros Hp. apply Hfp'. rewrite fp_after_begin. auto. }
        Exists (2 ^ 64 - 72) (sublist 0 (Zlength acc) oc ++ oc') fs' d' lxbf.
        unfold fgroup3, fcore3. Intros. entailer!.
        - split; [rewrite Zlength_app, Zlength_sublist by lia; lia |].
          destruct (mf_err_post2 pr sp a l tbl s (Zlength oc) (2^64-72) (sublist 0 (Zlength acc) oc ++ oc') fs' d d'
            ltac:(reflexivity) dec_err72 Hse Hdm0 ltac:(lia) Hcodes Hxn) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11).
          assert (HLp: mf_lpost a pr (tabs_lxb tabs) s (Zlength oc) lxbf)
            by (eapply mf_l_err; [exact E11 | reflexivity | rewrite Zlength_app, Zlength_sublist by lia; lia | auto | auto]).
          repeat match goal with |- _ /\ _ => split end;
            first [assumption | exact HLp | apply ret_err72 | (eapply dc_after; eauto) | auto].
        - rewrite <- (merge_out shd (Zlength oc) oc oc' dst (Zlength acc)) by (auto; lia). cancel. }
      { forward. entailer!. } }
    { forward. apply ENTAIL_refl. }
    (* an error of the frame *)
    forward_call r.
    forward_if.
    { assert (He: is_error_code r = true).
      { destruct (is_error_code r); auto;
        exfalso; match goal with Hz: Int.repr 0 <> Int.zero |- _ => apply Hz; reflexivity end. }
      pose proof (mf_err_frame pr sp d l tbl shk a fs s cap off u oc fs1 m qv dcur dm r oc' k HI Hfde
        ltac:(lia) Hmg Hfr He) as Hse.
      pose proof (mf_x_ferr a pr s cap off u oc (ts_x ts) r oc' k Hx H3 ltac:(lia) Hu ltac:(lia) Hloc2 ltac:(lia)
        Hmg He Hfx) as Hxn.
      assert (Hcodes: darg_model a <> None ->
                oneshot_codes (dmode_of pr) (mf_sel pr sp a l tbl) (darg_model a) s cap r)
        by (intros Hn; exact (codes_exact_ok _ _ _ _ _ _ (mf_codes_err pr sp d l tbl shk a fs s cap off u oc fs1 m
              qv dcur dm r oc' k HI Hfde ltac:(lia) Hmg Hfr Hfc3 He Hn))).
      forward.
      assert (Hfpg: fp_ok (fs_fParams fs) -> fp_ok (fs_fParams fs')).
      { intros Hp. apply Hfp'. rewrite fp_after_begin. auto. }
      Exists r (sublist 0 (Zlength acc) oc ++ oc') fs' d' lxbf.
      unfold fgroup3, fcore3. Intros. entailer!.
      - split; [rewrite Zlength_app, Zlength_sublist by lia; lia |].
        destruct (mf_err_post2 pr sp a l tbl s (Zlength oc) r (sublist 0 (Zlength acc) oc ++ oc') fs' d d'
          He (proj2 (Herr2 He)) Hse Hdm0 ltac:(lia) Hcodes Hxn) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11).
        assert (HLp: mf_lpost a pr (tabs_lxb tabs) s (Zlength oc) lxbf)
          by (eapply mf_l_err; [exact E11 | exact He | rewrite Zlength_app, Zlength_sublist by lia; lia | auto | auto]).
        repeat match goal with |- _ /\ _ => split end;
          first [assumption | exact HLp | (eapply dc_after; eauto) | auto].
      - rewrite <- (merge_out shd (Zlength oc) oc oc' dst (Zlength acc)) by (auto; lia). cancel. }
    (* the frame decoded: advance *)
    assert (Hne: is_error_code r = false).
    { destruct (is_error_code r) eqn:E; auto;
      exfalso; match goal with Hz: Int.repr 1 = Int.zero |- _ => apply Int.one_not_zero; exact Hz end. }
    destruct (Hok2 Hne) as [Hrc Hk].
    match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx ?S))) _ _ =>
      forward_if (PROP () LOCAL (temp _res (Vlong (Int64.repr r)); temp _moreThan1Frame (Vint (Int.repr m));
        temp _dststart dst; lvar _zfh (Tstruct ___gp_ZSTD_FrameHeader noattr) v_zfh;
        lvar _srcSize tulong v_srcSize; lvar _src (tptr tvoid) v_src; gvars gv; temp _dctx p;
        temp _dst (offset_val (u + r) dst); temp _dstCapacity (Vlong (Int64.repr (cap - u)));
        temp _dict (darg_dictv a); temp _dictSize (Vlong (Int64.repr (darg_dsize a))); temp _ddict qv')
        (SEPx S)) end.
    { forward. entailer!. }
    { forward. entailer!.
      match goal with Hz: Int64.repr ?x = Int64.zero |- _ =>
        apply (f_equal Int64.unsigned) in Hz; rewrite Int64.unsigned_repr in Hz by rep_lia;
        rewrite Int64.unsigned_zero in Hz; rewrite Hz, Z.add_0_r; auto end. }
    forward. forward.
    (* the invariant again *)
    rewrite Zlength_sublist in Hk by lia.
    pose proof (mf_pi_frame pr sp d l tbl shk a fs s cap off u oc fs1 m qv dcur qv' dm lent d' r oc' k
      (continuity (fs_after_begin a' fs1 cold dm (dp_fmt pr)) (offset_val u dst) (cap - u)) fs'
      HI ltac:(rewrite <- Ea'; exact Hfd) Hqv' Hloc' Hll Hda Hlt2 Hhs ltac:(lia) Hmg Hfr Hne ltac:(lia) ltac:(lia) Hloc2
      ltac:(destruct (Hby2 Hne) as (c & ? & ? & ?); exists c; rewrite Z.add_0_l in *; auto)
      (fp_after_begin _ _ _ _ _ _ _) Hfp' ltac:(intros; apply Hds'; auto) H3 (Hfcsx Hne) Hdsel
      ltac:(match goal with Hx: is_error_code r = false -> forall h, get_frame_header_m _ _ = FH_ok h -> _ |- _ =>
              exact (Hx Hne) end)
      (fun Ha Hp => mf_x_fok _ _ _ _ _ _ _ Hne (Hfx Ha Hp))) as HI'.
    pose proof (mf_l_frame a pr (tabs_lxb tabs) s cap off u lxb ts r k lxbf oc' HL ltac:(lia) ltac:(lia) Htl
      Hfx Hfxl) as HL'.
    Exists (off + k) (u + r) (sublist 0 u oc ++ oc') fs' 1 qv' d' lxbf.
    unfold fgroup3, fcore3. entailer!.
    - f_equal. f_equal. lia.
    - rewrite Zlength_sublist by lia. replace (Zlength s - off - k) with (Zlength s - (off + k)) by lia.
      rewrite <- (merge_out shd (Zlength oc) oc oc' dst (Zlength acc)) by (auto; lia). cancel. }
  (* after the loop *)
  Intros off u oc fs1 m qv dcur lxb. rename H6 into HI. rename H7 into HL. rename H8 into Hend.
  pose proof HI as [Hoff Hu Hoc Hm Hacc Hser Hcur Hqv Hdc Hloc Hfp Hds2 Hm0 Hd0 Hsf Hcd Hu0 Hcfs Hx].
  destruct Hacc as (acc & Hacc & Hlacc & Hsacc).
  match goal with |- semax _ ?P _ _ =>
    forward_loop P continue: (PROP (off = Zlength s) LOCAL (temp _dststart dst;
      lvar _zfh (Tstruct ___gp_ZSTD_FrameHeader noattr) v_zfh; lvar _srcSize tulong v_srcSize;
      lvar _src (tptr tvoid) v_src; gvars gv; temp _dst (offset_val u dst))
    SEP (data_at_ Tsh (Tstruct ___gp_ZSTD_FrameHeader noattr) v_zfh;
      data_at Tsh tulong (Vlong (Int64.repr (Zlength s - off))) v_srcSize;
      data_at Tsh (tptr tvoid) (offset_val off src) v_src; pws_pred W; zstd_globals gv;
      fgroup3 TABS gv p fs1 (TUninit lxb) pr sp; msel_res DENT gv p pr sp dcur l tbl shk a am hb;
      darg_res3 DENT gv pr sp d a; data_at shd (tarray tuchar cap) oc dst;
      data_at shs (tarray tuchar (Zlength s)) (zbytes s) src;
      field_at Ews t_dctx (DOT _streamStage) (Vint (Int.repr 0)) p))%assert
    break: (PROP (off = Zlength s) LOCAL (temp _dststart dst;
      lvar _zfh (Tstruct ___gp_ZSTD_FrameHeader noattr) v_zfh; lvar _srcSize tulong v_srcSize;
      lvar _src (tptr tvoid) v_src; gvars gv; temp _dst (offset_val u dst))
    SEP (data_at_ Tsh (Tstruct ___gp_ZSTD_FrameHeader noattr) v_zfh;
      data_at Tsh tulong (Vlong (Int64.repr (Zlength s - off))) v_srcSize;
      data_at Tsh (tptr tvoid) (offset_val off src) v_src; pws_pred W; zstd_globals gv;
      fgroup3 TABS gv p fs1 (TUninit lxb) pr sp; msel_res DENT gv p pr sp dcur l tbl shk a am hb;
      darg_res3 DENT gv pr sp d a; data_at shd (tarray tuchar cap) oc dst;
      data_at shs (tarray tuchar (Zlength s)) (zbytes s) src;
      field_at Ews t_dctx (DOT _streamStage) (Vint (Int.repr 0)) p))%assert end.
  { apply ENTAIL_refl. }
  { forward.
    forward_if.
    - dloop. dloop. dloop. dloop.
      forward.
      Exists (2 ^ 64 - 72) oc fs1 dcur lxb. entailer!.
      assert (Hse: series_err (dmode_of pr) (mf_sel pr sp a l tbl) (darg_model a) s (Zlength oc)).
      { eapply series_err_unk; [exact Hser |]. intros _.
        assert (Hne: off <> Zlength s).
        { intro E. subst off. match goal with Hz: Int64.repr _ <> Int64.zero |- _ => apply Hz end.
          rewrite Z.sub_diag. reflexivity. }
        rewrite decode_seriesS_short by (rewrite Zlength_sublist by lia; unfold dmode_of; cbn [md_magicless]; lia).
        rewrite Zlength_sublist by lia. replace (Zlength s - off =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
        reflexivity. }
      assert (Hcodes: darg_model a <> None ->
                oneshot_codes (dmode_of pr) (mf_sel pr sp a l tbl) (darg_model a) s (Zlength oc) (2 ^ 64 - 72)).
      { intros Hn. assert (Hne: sublist off (Zlength s) s <> nil).
        { intro E. match goal with Hz: Int64.repr _ <> Int64.zero |- _ => apply Hz end.
          assert (Zlength (sublist off (Zlength s) s) = 0) by (rewrite E; reflexivity).
          rewrite Zlength_sublist in * by lia. replace (Zlength s - off) with 0 by lia. reflexivity. }
        assert (Hsh: Zlength (sublist off (Zlength s) s) < starting_len (md_magicless (dmode_of pr)))
          by (rewrite Zlength_sublist by lia; exact Hend).
        eapply codes_dead; [ | | exact (Hcd Hn)]; intros c Hc.
        - exact (dead_short_ck _ _ _ _ _ Hsh Hc).
        - exact (dead_short_rr _ _ _ _ _ Hne Hsh Hc). }
      assert (Hxn: a = DA_none -> pr = dparams_dflt -> os_res s (Zlength oc) = None).
      { intros Ha Hp. assert (Hne: off <> Zlength s).
        { intro E. subst off. match goal with Hz: Int64.repr _ <> Int64.zero |- _ => apply Hz end.
          rewrite Z.sub_diag. reflexivity. }
        refine (proj2 (mf_x_end a pr s (Zlength oc) off _ oc Hx Hoff _ Ha Hp) Hne).
        rewrite Hp in Hend. exact Hend. }
      destruct (mf_err_post2 pr sp a l tbl s (Zlength oc) (2^64-72) oc fs1 d dcur ltac:(reflexivity) dec_err72 Hse Hdm0
        ltac:(lia) Hcodes Hxn) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11).
      assert (HLp: mf_lpost a pr (tabs_lxb tabs) s (Zlength oc) lxb)
        by (eapply mf_l_err; [exact E11 | reflexivity | lia | auto | auto]).
      repeat match goal with |- _ /\ _ => split end; first [assumption | exact HLp | apply ret_err72 | auto].
    - forward. entailer!.
      match goal with Hz: Int64.repr _ = Int64.zero |- _ =>
        apply (f_equal Int64.unsigned) in Hz; rewrite Int64.unsigned_repr in Hz by rep_lia;
        rewrite Int64.unsigned_zero in Hz end. lia. }
  { forward. entailer!. }
  forward.
  { entailer!. destruct (fc_bound (Zlength oc) dst) as (bd & od & -> & Hod); [lia | auto |].
    simpl. unfold is_true. destruct (peq bd bd); auto; congruence. }
  pose proof (mf_l_end _ _ _ _ _ _ _ _ HL ltac:(first [assumption | reflexivity | lia])) as HLp.
  Exists (Zlength acc) oc fs1 dcur lxb. entailer!.
  assert (Hne: is_error_code (Zlength acc) = false) by (unfold is_error_code; apply Z.ltb_ge; rep_lia).
  pose proof (oneshot_end63 _ _ _ _ s (Zlength s) (Zlength acc) oc (Zlength oc) Hser eq_refl ltac:(lia) ltac:(lia)) as Hos.
  destruct (mf_post pr sp a l tbl s (Zlength oc) (Zlength acc) oc Hos Hdm0) as [P1 P2].
  assert (Hcodes: darg_model a <> None ->
            oneshot_codes (dmode_of pr) (mf_sel pr sp a l tbl) (darg_model a) s (Zlength oc) (Zlength acc)).
  { intros Hn. exact (codes_end _ _ _ _ s (Zlength acc) (Zlength oc) _ ltac:(lia) (Hcd Hn)). }
  destruct (mf_codes_post pr sp a l tbl s (Zlength oc) (Zlength acc) ltac:(lia) Hcodes Hdm0) as [C1 C2].
  split; [auto|]. split; [auto|]. split; [intros _; exists acc; auto|].
  split; [intros E; rewrite Hne in E; discriminate|].
  split.
  { intros _ Hs Hf1 h Hh Ht. destruct Hm as [-> | ->].
    - exfalso. destruct (Hm0 eq_refl) as [E | Hnz]; [| exact (Hnz h Hh Ht)].
      assert (s = nil) by (apply Zlength_nil_inv; lia). subst s.
      destruct (dp_fmt pr =? 1); simpl in Hh; discriminate.
    - destruct (Hsf eq_refl Hs Hf1 h Hh Ht) as [_ ?]; auto. }
  split; [ | split; [exact C1 | split; [exact C2 | split]]].
  - intros _ Hs Hn (h & Hh & Ht). destruct Hm as [-> | ->].
    + exfalso. destruct (Hm0 eq_refl) as [E | Hnz]; [| exact (Hnz h Hh Ht)].
      assert (s = nil) by (apply Zlength_nil_inv; lia). subst s.
      destruct (dp_fmt pr =? 1); simpl in Hh; discriminate.
    + destruct (Hds2 eq_refl Hs Hn) as (id & ?); eauto.
  - (* a single frame that declares its content size: exactly that many bytes *)
    intros _ Hf1 h Hh Ht Hcu. destruct Hm as [-> | ->].
    + exfalso. destruct (Hm0 eq_refl) as [E | Hnz]; [| exact (Hnz h Hh Ht)].
      assert (s = nil) by (apply Zlength_nil_inv; lia). subst s.
      destruct (dp_fmt pr =? 1); simpl in Hh; discriminate.
    + exact (proj2 (Hcfs eq_refl Hf1 h Hh Ht) Hcu).
  - split.
    { (* the exact result: the end of the series *)
      intros Ha Hp. refine (proj1 (mf_x_end a pr s (Zlength oc) _ _ oc Hx ltac:(lia) _ Ha Hp) _); [| lia].
      unfold ZSTD_FRAMEHEADERSIZE_PREFIX. lia. }
    destruct (fc_bound (Zlength oc) dst) as (bd & od & -> & Hod); [lia | auto |].
    rewrite sub_pp_offset63 by lia. reflexivity.
Qed.

End CM_Multi3_body_1.

(* ---------- the specification ZSTD_decompressMultiFrame_spec3: the argument may be NULL (F9) ---------- *)
Require Import Zstd.proof.zstd.NullBuf.

Section CM_Multi3_body_2.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* the dictionary facts survive a witness more ... *)
Lemma dict_ptr_ok_cons : forall w W sh n p shd cap dst,
  dict_ptr_ok W sh n p shd cap dst -> dict_ptr_ok (w :: W) sh n p shd cap dst.
Proof.
  intros w W sh n p shd cap dst [(A & B & C) | (A & B & C)].
  - left. split; [exact A | split; [exact B | apply buf_ok_cons; exact C]].
  - right. split; [exact A | split].
    + rewrite pws_pred_cons. apply sepcon_valid_pointer2. exact B.
    + rewrite pws_pred_cons, sepcon_assoc. apply sepcon_valid_pointer2. exact C.
Qed.

Lemma dict_ptr_ok0_cons : forall w W sh n p shd cap dst,
  dict_ptr_ok0 W sh n p shd cap dst -> dict_ptr_ok0 (w :: W) sh n p shd cap dst.
Proof.
  intros w W sh n p shd cap dst [H | (A & B & C)].
  - left. apply dict_ptr_ok_cons; exact H.
  - right. split; [exact A | split; [exact B |]]. rewrite pws_pred_cons. apply sepcon_valid_pointer2. exact C.
Qed.

(* ... and hold at the base ZSTD_emptyBuffer of an empty dst passed as NULL, with its witness *)
Lemma dict_ptr_ok_null : forall gv shw W sh n p shd,
  readable_share shw -> dict_ptr_ok W sh n p shd 0 nullval ->
  dict_ptr_ok (eb_wit gv shw :: W) sh n p shd 0 (gv _ZSTD_emptyBuffer).
Proof.
  intros gv shw W sh n p shd Hr [(A & _ & _) | (A & B & C)].
  - discriminate A.
  - right. split; [exact A | split].
    + rewrite pws_pred_cons. apply sepcon_valid_pointer2. exact B.
    + apply sepcon_valid_pointer1. apply eb_wit_valid; exact Hr.
Qed.

Lemma dict_ptr_ok0_null : forall gv shw W sh n p shd,
  readable_share shw -> dict_ptr_ok0 W sh n p shd 0 nullval ->
  dict_ptr_ok0 (eb_wit gv shw :: W) sh n p shd 0 (gv _ZSTD_emptyBuffer).
Proof.
  intros gv shw W sh n p shd Hr [H | (A & B & C)].
  - left. apply dict_ptr_ok_null; auto.
  - right. split; [exact A | split; [exact B |]]. rewrite pws_pred_cons. apply sepcon_valid_pointer2. exact C.
Qed.

(* the same for a dictionary given by the caller, which may also lie before dst (Spec_api6.dict_ptr_ok_any) *)
Lemma dict_ptr_ok_any_cons : forall w W sh n p shd cap dst,
  dict_ptr_ok_any W sh n p shd cap dst -> dict_ptr_ok_any (w :: W) sh n p shd cap dst.
Proof.
  intros w W sh n p shd cap dst [H | (A & B & C)].
  - left. apply dict_ptr_ok_cons; exact H.
  - right. split; [exact A | split; [exact B | apply buf_ok_cons; exact C]].
Qed.

Lemma dict_ptr_ok_any_null : forall gv shw W sh n p shd,
  readable_share shw -> dict_ptr_ok_any W sh n p shd 0 nullval ->
  dict_ptr_ok_any (eb_wit gv shw :: W) sh n p shd 0 (gv _ZSTD_emptyBuffer).
Proof.
  intros gv shw W sh n p shd Hr [H | (A & _ & _)].
  - left. apply dict_ptr_ok_null; auto.
  - discriminate A.
Qed.

(* the witness list and the base of the body's specification *)
Lemma darg_ok3_base : forall gv shw W a shd cap dst,
  readable_share shw -> (dst = nullval -> cap = 0) -> darg_ok3 W a shd cap dst ->
  darg_ok3 (eb_wit gv shw :: W) a shd cap (nbase gv dst).
Proof.
  intros gv shw W a shd cap dst Hr Hc H.
  destruct (nbase_cases gv dst) as [[Hn ->] | [Hn ->]].
  - destruct a as [| sh pk b | x buf sh]; simpl in *; auto.
    + destruct H as (A & B & C & D). split; [exact A | split; [exact B | split; [exact C | apply dict_ptr_ok_any_cons; exact D]]].
    + intros Hx Hb. destruct (H Hx Hb) as [A B]. split; [exact A | apply dict_ptr_ok0_cons; exact B].
  - subst dst. rewrite (Hc eq_refl) in *. destruct a as [| sh pk b | x buf sh]; simpl in *; auto.
    + destruct H as (A & B & C & D). split; [exact A | split; [exact B | split; [exact C | apply dict_ptr_ok_any_null; auto]]].
    + intros Hx Hb. destruct (H Hx Hb) as [A B]. split; [exact A | apply dict_ptr_ok0_null; auto].
Qed.

Lemma msel_ok_base : forall gv shw W d l a shk shd cap dst,
  readable_share shw -> (dst = nullval -> cap = 0) -> msel_ok W d l a shk shd cap dst ->
  msel_ok (eb_wit gv shw :: W) d l a shk shd cap (nbase gv dst).
Proof.
  intros gv shw W d l a shk shd cap dst Hr Hc (A & B & C & D & E & F).
  split; [exact A | split; [exact B | split; [exact C | split; [exact D | split; [| exact F]]]]].
  eapply Forall_impl; [| exact E]. intros e He Hne. specialize (He Hne). unfold ddict_buf_ok0 in *.
  destruct (dd_ref (snd e)); auto.
  destruct (nbase_cases gv dst) as [[Hn ->] | [Hn ->]].
  - apply dict_ptr_ok0_cons; exact He.
  - subst dst. rewrite (Hc eq_refl) in *. apply dict_ptr_ok0_null; auto.
Qed.

Lemma multi3_sub : forall DENT TABS,
  funspec_sub (snd (ZSTD_decompressMultiFrame_spec3b DENT TABS)) (snd (ZSTD_decompressMultiFrame_spec3 DENT TABS)).
Proof.
  intros DENT TABS.
  apply NDsubsume_subsume; [split; reflexivity|].
  split; [split; reflexivity|].
  intros [[[[[[[[[[[[[[[[[[[W gv] p] fs] tabs] pr] sp] d] l] tbl] shk] shd] dst] cap] shs] src] s] a] am] hb] [g args].
  simpl.
  unfold PROPx, LOCALx, SEPx, PARAMSx, GLOBALSx; simpl. normalize.
  rename H into Hbd, H0 into Hbs, H1 into Hwd, H2 into Hrs, H3 into Hcap, H4 into Hsl, H5 into Hby, H6 into Hda,
    H7 into Hms.
  unfold LOCALx at 1, argsassert2assert at 1; simpl.
  assert_PROP (dst = nullval -> cap = 0) as Hc0.
  { apply andp_left2. sep_apply (mbuf_local_facts shd cap (Zrepeat Vundef cap) dst ltac:(lia)). entailer!. tauto. }
  (* lend a part of ZSTD_emptyBuffer as the witness of the base *)
  eapply derives_trans; [apply andp_derives; [apply derives_refl | apply sepcon_derives; [apply derives_refl |
    apply sepcon_derives; [apply zstd_globals_lend | apply derives_refl]]] |].
  normalize. rename sh into shw, H into Hrw.
  Exists (eb_wit gv shw :: W, gv, p, fs, tabs, pr, sp, d, l, tbl, shk, shd, dst, nbase gv dst, cap, shs, src, s, a,
          am, hb) emp.
  simpl. apply andp_right.
  unfold LOCALx, argsassert2assert; simpl. entailer!.
  - split; [apply buf_ok_base; auto |]. split; [apply buf_ok_cons; auto |].
    split; [apply darg_ok3_base; auto |]. split; [intros Hs; apply msel_ok_base; auto |].
    destruct (nbase_cases gv dst) as [[Hn ->] | [Hn ->]]; [left; reflexivity | right; split; auto].
  - apply andp_derives; [apply derives_refl |].
    change (data_at shw (tarray tuchar 1) eb_cells (gv _ZSTD_emptyBuffer)) with (pw_pred (eb_wit gv shw)).
    sep_apply (mbuf_base gv shw shd cap (Zrepeat Vundef cap) dst).
    rewrite pws_pred_cons. unfold data_at_. cancel.
  - (* give the witness back; the array at the base is mbuf at dst *)
    apply prop_right. intros rho'. rewrite emp_sepcon. normalize.
    match goal with |- context [data_at shd (tarray tuchar (Zlength ?o)) ?o (nbase gv dst)] => rename o into out end.
    match goal with |- context [fgroup3 TABS gv p ?f (TUninit ?x) pr sp] => rename f into fs', x into lxb' end.
    match goal with |- context [msel_res DENT gv p pr sp ?q l tbl shk a am hb] => rename q into d' end.
    match goal with H: 0 <= ?r <= Int64.max_unsigned |- _ => rename r into rr end.
    Exists rr out fs' d' lxb'. rewrite pws_pred_cons. entailer!.
    apply andp_derives; [apply derives_refl |].
    sep_apply (base_mbuf gv shd (Zlength out) out dst Hc0). sep_apply (zstd_globals_return gv shw). cancel.
Qed.

Lemma body_decompressMultiFrame3: forall DENT TABS SR BR, DENT_OK DENT -> TABS_OK TABS ->
  body_ok (FR3_G DENT TABS SR BR) (ZSTD_decompressMultiFrame_spec3 DENT TABS).
Proof.
  intros DENT TABS SR BR HDENT HTABS.
  exists f_ZSTD_decompressMultiFrame; split; [reflexivity | split; [reflexivity | ]].
  eapply semax_body_funspec_sub; [apply body_decompressMultiFrame3b; auto | apply multi3_sub |].
  apply compute_list_norepet_e; reflexivity.
Qed.

End CM_Multi3_body_2.
