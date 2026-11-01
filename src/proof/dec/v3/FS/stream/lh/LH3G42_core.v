(* FS3 streaming, case zdss_loadHeader, G4: zdss_read's call_inv for the new frame (pure part). *)
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3Stmts Zstd.proof.dec.v3.FS.stream.lh.LH3R2Lib Zstd.proof.dec.v3.FS.stream.lh.LH3G42_dict Zstd.proof.dec.v3.FS.stream.lh.LH3G42_frame Zstd.proof.dec.v3.FS.stream.lh.LH3G42_alive.
Local Open Scope Z_scope.

Section CM_LH3G42_core_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma g4_lev_range (l: list Z) : bytes_ok l -> 0 <= le_value l < 2 ^ (8 * Zlength l).
Proof.
  intros H. induction H; cbn [le_value].
  - rewrite Zlength_nil. simpl. lia.
  - unfold is_byte in H. rewrite Zlength_cons. replace (8 * Z.succ (Zlength l)) with (8 + 8 * Zlength l) by lia.
    rewrite Z.pow_add_r by (pose proof (Zlength_nonneg l); lia).
    change (2^8) with 256. lia.
Qed.

Lemma g4_lef_range (l: list Z) i k : bytes_ok l -> 0 <= k -> 0 <= le_field l i k < 2 ^ (8 * k).
Proof.
  intros H Hk. unfold le_field, slice.
  assert (Hb: bytes_ok (firstn (Z.to_nat k) (skipn (Z.to_nat i) l))).
  { unfold bytes_ok in *. apply Forall_firstn, Forall_skipn; auto. }
  pose proof (g4_lev_range _ Hb).
  assert (Zlength (firstn (Z.to_nat k) (skipn (Z.to_nat i) l)) <= k).
  { rewrite Zlength_correct, firstn_length. lia. }
  assert (2 ^ (8 * Zlength (firstn (Z.to_nat k) (skipn (Z.to_nat i) l))) <= 2 ^ (8 * k)).
  { apply Z.pow_le_mono_r; [lia |]. pose proof (Zlength_nonneg (firstn (Z.to_nat k) (skipn (Z.to_nat i) l))). lia. }
  lia.
Qed.

Lemma g4_bmax : forall p, par_ok p -> 0 <= md_bmax (dmode_of p).
Proof.
intros p (_ & _ & Hb & _). unfold dmode_of. cbn [md_bmax].
destruct (Z.eqb_spec (dp_bmax p) 0); unfold ZSTD_BLOCKSIZE_MAX in *; lia.
Qed.

(* the new frame's view satisfies c_core *)
Lemma g4_ccore : forall a w hb h tbl d1 did1 c s3,
  let k := w_k w in
  let k1 := k_A k (fh_val h) d1 did1 in
  let k3 := lhC_k k1 hb h c in
  let st := a_st a in
  c3_stable k = dc_stable st -> c3_par k = dc_par st -> par_ok (c3_par k) ->
  lh_entry a w hb -> get_frame_header_m (lh_mg k) hb = FH_ok h -> gfh3_facts (lh_mg k) hb h ->
  lhA_sel k hb 0 (fh_val h) tbl d1 did1 ->
  lhC_facts a w k1 h c -> lhD_facts (c3_stable k3) (c3_s k3) s3 h (lh_bsm k3 h) ->
  (fs_ddictIsCold (c3_fs k) = Vint (Int.repr 0) \/ fs_ddictIsCold (c3_fs k) = Vint (Int.repr 1)) ->
  (forall x buf, lc_dd c = Some (x, buf) -> ddx_model x <> None) ->
  (forall x buf, lc_dd c = Some (x, buf) -> bytes_ok (dx_bytes x) /\ (ddx_copied x = true -> 0 < Zlength (dx_bytes x))) ->
  0 <= sf_outSize s3 ->
  forall sout, c_core (dc_stable st) (Some (a_ob a, a_osz a)) sout (lhD_k k3 h s3) (g4_sv st hb h c).
Proof.
intros a w hb h tbl d1 did1 c s3 k k1 k3 st Hstab Hpar Hpok Hent Hgfh Hgf Hsel HC HD Hcold Gap2 Hbo Hout0 sout.
destruct Hent as (Hstg & Hlh' & Hhb18 & Hbhb & Hhbuf & Hhost & Hinp & Hos & Hoe & _).
fold k in Hstg, Hlh', Hhbuf, Hhost, Hinp, Hos, Hoe.
destruct HD as (Hs3 & Hip3 & Hos3 & Hoe3 & Hlh3 & Hhb3 & Hho3 & Hnfp3 & Hexp3 & Hnn3 & Hptr3 & Hin3 & Hsum3 & Hout3).
destruct Hgf as (G5 & Gfcs & Gws & Gbsm & Gbsm2 & Gck & Gft & Gskm & Gsk & Gdid & Ghs).
destruct HC as (HCdd & HCcold & HCdidr & HCst & HCid & _ & HCwin).
assert (Hbuf: forall x buf, lc_dd c = Some (x, buf) ->
               isptr buf \/ (buf = nullval /\ dx_ref x = Some nullval /\ dx_bytes x = nil)).
{ intros x buf E. rewrite E in HCdd. cbn [lhC_dd] in HCdd. unfold lh_dd_ok in HCdd. tauto. }
assert (Hbsm: lh_bsm k3 h = sm_bsm (sm_of st) h).
{ unfold lh_bsm, sm_bsm, k3, k1, sm_of. cbn [lhC_k c3_par sm_md]. unfold k_A, c3_with_dict, c3_with_fs.
  cbn [c3_par]. rewrite Hpar. reflexivity. }
pose proof (g4_bmax _ Hpok) as Hbm0.
assert (Hbsm0: 0 <= sm_bsm (sm_of st) h <= fh_blockSizeMax h).
{ unfold sm_bsm, sm_of. cbn [sm_md dmode_w md_bmax]. rewrite <- Hpar. lia. }
(* piece C changed only the allocator's count of the stream fields (held_redict) *)
repeat match goal with H: ?f s3 = ?f (c3_s k3) |- _ => change (f s3 = f (c3_s k)) in H end.
change (c3_stable k3) with (c3_stable k) in Hout3.
rewrite Hbsm in Hin3, Hout3.
unfold c_core. change (c3_s (lhD_k k3 h s3)) with s3.
rewrite Hs3.
split; [ right; left; split; [ rewrite Hho3; exact Hhost | reflexivity ] | ].
split.
{ change (c3_fs (lhD_k k3 h s3)) with (fsu_fParams (lhC_fs k1 hb h c) (fh_val (fh_adj h (lh_bsm k3 h)))).
  apply g4_cold; [ exact HCcold | exact Hcold ]. }
split; [ exact Hsum3 | ].
replace (zdss_read =? zdss_init) with false by reflexivity.
replace (zdss_read =? zdss_loadHeader) with false by reflexivity.
split; [ left; reflexivity | ].
change (c3_fs (lhD_k k3 h s3)) with (fsu_fParams (lhC_fs k1 hb h c) (fh_val (fh_adj h (lh_bsm k3 h)))).
change (c3_tabs (lhD_k k3 h s3))
  with (TInit (dd_ox (lc_dd c)) (lh_dd_ts (lc_dd c) (lc_lxb c))).
rewrite Hbsm.
assert (Hlf: 0 <= le_field hb 4 4 < 2 ^ 32) by (apply (g4_lef_range hb 4 4 Hbhb); lia).
destruct Gft as [Ft | Ft].
- (* a Zstandard frame *)
  unfold g4_sv. replace (fh_frameType h =? 1) with false by (symmetry; apply Z.eqb_neq; lia).
  cbn [sv_fp sv_pend sv_ahead sv_lay sv_dd].
  split.
  { apply g4_cframe_zstd; auto.
    all: try lia.
    all: try (apply g4_dm_of_ok; exact Gap2).
    all: try (unfold k1, k_A, k_redict, c3_with_s, c3_with_dict, c3_with_fs; cbn [c3_par]; rewrite Hpar; reflexivity).
    all: try (unfold Int64.max_unsigned, Int64.modulus, Int64.wordsize, Wordsize_64.wordsize in Gfcs;
              simpl in Gfcs; lia).
    all: destruct Hpok as (_ & _ & _ & Hw & _); unfold k1, k_A, k_redict, c3_with_s, c3_with_dict, c3_with_fs in HCwin;
         cbn [c3_par] in HCwin; lia. }
  split.
  { unfold c_ring. cbn [fp_bsm zp_bsm z_start fp_content zp_out zp_h].
    split; [ exact Hnn3 | ]. split; [ exact Hptr3 | ]. split; [ exact Hin3 | ].
    exists 0, 0. rewrite Hos3, Hoe3, Hos, Hoe. split; [ reflexivity | ]. split; [ reflexivity | ]. split; [ lia | ].
    destruct (dc_stable st) eqn:Est.
    - split; [ reflexivity | ]. split; [ reflexivity | ]. split; [ reflexivity | ].
      exists (a_ob a), (a_osz a). split; [ reflexivity | ]. unfold g4_lay. destruct (lc_dd c) as [[x buf]|]; [ destruct (eq_dec buf nullval) | ]; reflexivity.
    - split; [ lia | ]. split; [ rewrite sublist_nil; reflexivity | ]. split; [ rewrite Zlength_nil; lia | ].
      split; [ apply Hout3; rewrite Hstab; reflexivity | ].
      unfold g4_lay. destruct (lc_dd c) as [[x buf]|]; [ destruct (eq_dec buf nullval) | ]; cbn; repeat split. }
  split; [ intros _; unfold zdss_read, zdss_flush; lia | ].
  split; [ intros Hx; unfold zdss_read, zdss_load in Hx; lia | ].
  split; [ intros _; rewrite Hip3, Hinp; split; [ reflexivity | ]; split; [ right; left; reflexivity | exact I ] | ].
  intros _; split; [ reflexivity | ]; rewrite Hos3, Hoe3, Hos, Hoe; reflexivity.
- (* a skippable frame *)
  unfold g4_sv. rewrite Ft. change (1 =? 1) with true. cbv iota.
  cbn [sv_fp sv_pend sv_ahead sv_lay sv_dd].
  destruct (Gsk Ft) as (_ & Gw0 & Gb0 & _).
  assert (Hb0: sm_bsm (sm_of st) h = fh_blockSizeMax h) by lia.
  split.
  { rewrite Hb0. apply g4_cframe_skip; auto.
    destruct (proj1 Gskm Ft) as [Hmg _]. rewrite Hmg in Hgfh. exact Hgfh. }
  split.
  { unfold c_ring. cbn [fp_bsm fp_content].
    split; [ exact Hnn3 | ]. split; [ exact Hptr3 | ].
    split; [ pose proof (Z.le_max_r (sm_bsm (sm_of st) h) 4); change (Z.max 0 4) with 4; lia | ].
    exists 0, 0. rewrite Hos3, Hoe3, Hos, Hoe. split; [ reflexivity | ]. split; [ reflexivity | ]. split; [ lia | ].
    destruct (dc_stable st) eqn:Est.
    - split; [ reflexivity | ]. split; [ reflexivity | ]. split; [ reflexivity | ].
      exists (a_ob a), (a_osz a). split; [ reflexivity | ]. unfold g4_lay. destruct (lc_dd c) as [[x buf]|]; [ destruct (eq_dec buf nullval) | ]; reflexivity.
    - split; [ lia | ]. split; [ rewrite sublist_nil; reflexivity | ]. split; [ rewrite Zlength_nil; lia | ].
      split; [ exact I | ].
      unfold g4_lay. destruct (lc_dd c) as [[x buf]|]; [ destruct (eq_dec buf nullval) | ]; cbn; repeat split. }
  split; [ intros _; unfold zdss_read, zdss_flush; lia | ].
  split; [ intros Hx; unfold zdss_read, zdss_load in Hx; lia | ].
  split; [ intros _; rewrite Hip3, Hinp; split; [ reflexivity | ]; split; [ right; left; reflexivity | left; reflexivity ] | ].
  intros _; split; [ reflexivity | ]; rewrite Hos3, Hoe3, Hos, Hoe; reflexivity.
Qed.

(* G4, the pure part: the facts of the representation it needs are premises *)
Lemma g4_pure : MF3 -> hs_probe_ok -> forall a w hb h tbl d1 did1 c s3,
  lh_ctx a w hb -> get_frame_header_m (lh_mg (w_k w)) hb = FH_ok h -> gfh3_facts (lh_mg (w_k w)) hb h ->
  lhA_sel (w_k w) hb 0 (fh_val h) tbl d1 did1 ->
  let k1 := k_A (w_k w) (fh_val h) d1 did1 in
  lhC_facts a w k1 h c ->
  let k3 := lhC_k k1 hb h c in
  lhD_facts (c3_stable k3) (c3_s k3) s3 h (lh_bsm k3 h) ->
  let w3 := lw_k w (lhD_k k3 h s3) in
  g4_gaps a w h c ->
  par_ok (c3_par (w_k w)) -> (c3_set (w_k w) <> nil -> c3_sp (w_k w) <> nullval) ->
  (c3_set (w_k w) = nil -> c3_sp (w_k w) = nullval) ->
  g4_local_ok (a_st a) (snd (getddict_res d1)) -> 0 <= sf_outSize s3 ->
  0 <= sf_held (c3_s (w_k w3)) - local_held (c3_dict (w_k w3)) ->
  (forall x buf, lc_dd c = Some (x, buf) -> bytes_ok (dx_bytes x) /\ (ddx_copied x = true -> 0 < Zlength (dx_bytes x))) ->
  exists sv, call_inv a (w_k w3) sv (w_ipc w3) (w_opc w3) (w_oc w3) nil /\
    loop_extra {| w_smw := w_smw w3; w_k := w_k w3; w_sv := sv; w_ipc := w_ipc w3; w_opc := w_opc w3;
                  w_oc := w_oc w3; w_dl := nil |}.
Proof.
intros HMF Hpr a w hb h tbl d1 did1 c s3 Hctx Hgfh Hgf Hsel k1 HC k3 HD w3 Hgaps Hpok Hsp1 Hsp0 Hloc Hout0 Hheld Hbo.
exists (g4_sv (a_st a) hb h c).
destruct Hctx as (Ha & Hstart & Hci & Hsmw & Hle & Hent & Hfp & Hdl & Hah & Hpend & Hentry & Hunt).
pose proof Hent as Hent'.
destruct Hent' as (Hstg & Hlh' & Hhb18 & Hbhb & Hhbuf & Hhost & Hinp & Hos & Hoe & Hipr & Hopr & Hlo' & Hsmw' &
                   Hbase' & Hlenok).
destruct Hci as (Hip & Hop & Hlo & Hpre & Hdll & Hsub & Hbdl & Hbase & Hbin & Hnfp & Hnfp2 & Hnfp0 & Hcore & Hddok &
                 Hstb & Hahd & Hblk & Halive & Hlh & Hsin & Hexp & Hfl).
rewrite Hfp, Hpend, Hah, Hdl in *.
pose proof Hbase as (Hstab & Hpar & Hset & Hdr & Hsco & Hfpok).
assert (Hsdo: stream_dict_ok (a_W a) (a_st a)) by (unfold dsa_ok in Ha; tauto).
assert (Hibs: bytes_ok (a_ibs a)) by (unfold dsa_ok in Ha; tauto).
assert (Hlen: fh_headerSize h = Zlength hb) by (unfold hdr_lenok in Hlenok; rewrite Hgfh in Hlenok; exact Hlenok).
pose proof HD as (Hs3 & Hip3 & Hos3 & Hoe3 & Hlh3 & Hhb3 & Hho3 & Hnfp3 & Hexp3 & _).
repeat match goal with H: ?f s3 = ?f (c3_s k3) |- _ => change (f s3 = f (c3_s (w_k w))) in H end.
destruct Hcore as (_ & Hcold & _).
split.
2: { unfold loop_extra. cbn [w_smw w_k w3 lw_k]. intros _ Hx. exfalso. change (c3_s (lhD_k k3 h s3)) with s3 in Hx.
     rewrite Hs3 in Hx. unfold zdss_read, zdss_loadHeader in Hx. lia. }
unfold call_inv. cbn [w_ipc w_opc w_oc w_k w3 lw_k].
change (c3_s (lhD_k k3 h s3)) with s3.
split; [ exact Hip | ]. split; [ exact Hop | ]. split; [ exact Hlo | ]. split; [ exact Hpre | ].
split; [ exact Hdll | ]. split; [ exact Hsub | ]. split; [ constructor | ].
split.
{ unfold base_call. split; [ exact Hstab | ]. split; [ exact Hpar | ]. split; [ exact Hset | ].
  split; [ | split; [ exact Hsco | ] ].
  2: { split.
       { destruct Hgf as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Gdid & _). exists (fh_dictID h). split; [ | exact Gdid ].
         reflexivity. }
       (* the allocator fields: kept by piece D; the dictionary fields: getDDict's of the selection's *)
       pose proof Hbase as (_ & _ & _ & _ & _ & _ & Hmc).
       assert (Hm3: sf_mem s3 = sf_mem (c3_s k3) /\ sf_held s3 = sf_held (c3_s k3))
         by (destruct HD as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hm & Hh); auto).
       destruct (rl_kA_held (w_k w) (fh_val h) d1 did1) as [EmA EhA].
       destruct (rl_lhC_held k1 hb h c) as [EmC EhC].
       apply (rl_mem_call_with _ (w_k w)); [ exact Hmc | | | | exact Hheld ].
       - exact (redict_ok_trans _ _ _ (lhA_sel_redict _ _ _ _ _ _ _ Hsel) (redict_ok_getddict d1)).
       - etransitivity; [ exact (proj1 Hm3) | ]. etransitivity; [ exact EmC | exact EmA ].
       - etransitivity; [ | etransitivity; [ exact EhC | exact EhA ] ].
         change (sf_held s3 - local_held (c3_dict k3) = sf_held (c3_s k3) - local_held (c3_dict k3)).
         rewrite (proj2 Hm3). reflexivity. }
  exact (g4_dict_rel2 (a_W a) (a_st a) d1 Hsdo (g4_dict_rel1 Hpr (a_st a) (w_k w) hb 0 (fh_val h) tbl d1 did1 Hbase Hsel)). }
split; [ exact Hbin | ].
split; [ rewrite Hnfp3; exact Hnfp | ].
split.
{ rewrite Hnfp3. destruct Hnfp2 as [Hq|[Hq|[Hq|[Hq|(Hq & hb0 & k0 & Hf & Hm)]]]].
  - left; exact Hq.
  - right; left; exact Hq.
  - right; right; left; exact Hq.
  - exfalso. rewrite Hstg in Hq. unfold zdss_loadHeader, zdss_init in Hq. lia.
  - exfalso. injection Hf as <-. unfold lh_mg in Hgfh. congruence. }
split; [ intros E; rewrite Hnfp3; exact (Hnfp0 E) | ].
split.
{ apply (g4_ccore a w hb h tbl d1 did1 c s3); auto. apply Hgaps. }
split.
{ unfold sv_dd_ok. intros _ x buf E. cbn [sv_dd g4_sv] in E. destruct HC as (HCdd & _).
  rewrite E in HCdd. cbn [lhC_dd] in HCdd. destruct HCdd as (_ & _ & Hsrc & _). exact Hsrc. }
split; [ exact Hstb | ].
split; [ cbn; intros Hx; contradiction | ].
split; [ intros _ _; cbn; unfold ZSTD_BLOCKSIZE_MAX; lia | ].
split.
{ change (sv_ahead (g4_sv (a_st a) hb h c)) with (@nil Z).
  apply (g4_alive HMF Hpr (a_W a) a w hb h tbl d1 did1 c s3 (w_sv w)); auto.
  unfold bytes_ok in *. apply Forall_app. split; [ exact Hbin | ]. apply Forall_app. split; [ | constructor ].
  apply Forall_sublist. exact Hibs. }
split; [ intros Hx; exfalso; rewrite Hs3 in Hx; unfold zdss_read, zdss_loadHeader in Hx; lia | ].
split; [ exact Hsin | ].
split.
{ intros Hst _. rewrite Hexp3. apply Hexp; [ exact Hst | rewrite Hstg; unfold zdss_loadHeader, zdss_init; lia ]. }
intros Hx; exfalso; rewrite Hs3 in Hx; unfold zdss_read, zdss_flush in Hx; lia.
Qed.

End CM_LH3G42_core_1.
