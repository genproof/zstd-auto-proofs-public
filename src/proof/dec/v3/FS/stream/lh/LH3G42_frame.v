(* FS3 streaming, case zdss_loadHeader, G4: the frame fields after pieces C and D (c_frame). *)
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3Stmts Zstd.proof.dec.v3.FS.stream.lh.LH3G42_dict.
Local Open Scope Z_scope.

Section CM_LH3G42_frame_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* the history layout of a frame begun with the DDict dd: its content as the prefix, or nothing (no DDict, or the
   DDict without content: buf = NULL) *)
Definition g4_lay (dd: option (ddx * val)) : hlay :=
  match dd with
  | Some (x, buf) =>
      if eq_dec buf nullval then HL_none else HL_dict buf (zbytes (dx_bytes x)) (if ddx_copied x then 1 else 0)
  | None => HL_none
  end.

(* the dictionary model of the DDict dd (no_dict when none, or not described) *)
Definition g4_dm_of (dd: option (ddx * val)) : dict_model :=
  match dd with
  | Some (x, _) => match ddx_model x with Some dm => dm | None => no_dict end
  | None => no_dict
  end.

Lemma g4_dm_of_eq : forall dd dm, dd_model dd dm -> g4_dm_of dd = dm.
Proof.
intros [[x buf]|] dm H; cbn in *; [ rewrite H; reflexivity | subst; reflexivity ].
Qed.

Lemma g4_dm_of_ok : forall dd, (forall x buf, dd = Some (x, buf) -> ddx_model x <> None) -> dd_model dd (g4_dm_of dd).
Proof.
intros [[x buf]|] H; cbn; [ | reflexivity ].
specialize (H x buf eq_refl). destruct (ddx_model x); [ reflexivity | contradiction ].
Qed.

Lemma g4_tabs : forall dd lxb dm, dd_model dd dm -> ts_d (lh_dd_ts dd lxb) = dm_state dm.
Proof.
intros [[x buf]|] lxb dm H; cbn in *; [ apply g4_state; exact H | subst; reflexivity ].
Qed.

Lemma g4_lay_fields : forall fs fmt dd cold,
  (forall x buf, dd = Some (x, buf) -> isptr buf \/ (buf = nullval /\ dx_ref x = Some nullval /\ dx_bytes x = nil)) ->
  (forall x buf, dd = Some (x, buf) -> bytes_ok (dx_bytes x) /\ (ddx_copied x = true -> 0 < Zlength (dx_bytes x))) ->
  lay_fields (lh_dd_fs fs fmt dd cold) (g4_lay dd) /\ lay_dd (g4_lay dd) dd.
Proof.
intros fs fmt [[x buf]|] cold Hp Hbo; unfold g4_lay, lh_dd_fs.
- specialize (Hp x buf eq_refl). specialize (Hbo x buf eq_refl).
  destruct (eq_dec buf nullval) as [En | En].
  + (* the DDict without content: the fields of no dictionary *)
    subst buf. destruct Hp as [Hp | (_ & Hr & Hb)]; [ contradiction | ].
    assert (Hc: ddx_copied x = false) by (unfold ddx_copied; rewrite Hr; reflexivity).
    rewrite Hc, ddx_end_null. cbn. split; [ split; [ repeat split | reflexivity ] | repeat split; auto ].
  + destruct Hp as [Hp | (E & _)]; [ | contradiction ].
    rewrite ddx_end_ptr by exact Hp. cbn. rewrite Zlength_map.
    split; [ split; [ split; [ exact Hp | auto ] | reflexivity ] | ].
    exists x. tauto.
- cbn. split; [ split; [ auto | reflexivity ] | exact I ].
Qed.

(* the frame fields lay_fields reads are not touched by lhC_fs's updates *)
Lemma g4_lay_lhC : forall k1 hb h c bsm,
  (forall x buf, lc_dd c = Some (x, buf) -> isptr buf \/ (buf = nullval /\ dx_ref x = Some nullval /\ dx_bytes x = nil)) ->
  (forall x buf, lc_dd c = Some (x, buf) -> bytes_ok (dx_bytes x) /\ (ddx_copied x = true -> 0 < Zlength (dx_bytes x))) ->
  lay_fields (fsu_fParams (lhC_fs k1 hb h c) (fh_val (fh_adj h bsm))) (g4_lay (lc_dd c)).
Proof.
intros k1 hb h c bsm Hp Hbo.
destruct (g4_lay_fields (c3_fs k1) (dp_fmt (c3_par k1)) (lc_dd c) (lc_cold c) Hp Hbo) as [H _].
unfold lhC_fs. destruct (fh_frameType h =? 1); destruct (g4_lay (lc_dd c)); exact H.
Qed.

Lemma g4_cold : forall k1 hb h c bsm,
  (lc_cold c = Vint (Int.repr 0) \/ lc_cold c = Vint (Int.repr 1)) ->
  (fs_ddictIsCold (c3_fs k1) = Vint (Int.repr 0) \/ fs_ddictIsCold (c3_fs k1) = Vint (Int.repr 1)) ->
  let F := fsu_fParams (lhC_fs k1 hb h c) (fh_val (fh_adj h bsm)) in
  fs_ddictIsCold F = Vint (Int.repr 0) \/ fs_ddictIsCold F = Vint (Int.repr 1).
Proof.
intros k1 hb h c bsm H1 H2 F. subst F.
unfold lhC_fs, lh_dd_fs. destruct (lc_dd c) as [[x buf]|]; destruct (fh_frameType h =? 1); cbn; auto.
Qed.

Lemma g4_cframe_zstd : forall k1 hb h c bsm dm ign,
  fh_frameType h = 0 ->
  (forall x buf, lc_dd c = Some (x, buf) -> isptr buf \/ (buf = nullval /\ dx_ref x = Some nullval /\ dx_bytes x = nil)) ->
  (forall x buf, lc_dd c = Some (x, buf) -> bytes_ok (dx_bytes x) /\ (ddx_copied x = true -> 0 < Zlength (dx_bytes x))) ->
  (lc_cold c = Vint (Int.repr 0) \/ lc_cold c = Vint (Int.repr 1)) ->
  (fs_ddictIsCold (c3_fs k1) = Vint (Int.repr 0) \/ fs_ddictIsCold (c3_fs k1) = Vint (Int.repr 1)) ->
  0 <= bsm <= fh_blockSizeMax h -> fh_blockSizeMax h = Z.min (fh_windowSize h) ZSTD_BLOCKSIZE_MAX ->
  0 <= fh_windowSize h -> Z.max (fh_windowSize h) ZSTD_WINDOWSIZE_ABSMIN <= 2 ^ 31 ->
  0 <= fh_contentSize h < 2 ^ 64 -> (fh_checksumFlag h = 0 \/ fh_checksumFlag h = 1) ->
  dd_model (lc_dd c) dm -> ign = (dp_ignore (c3_par k1) =? 1) ->
  c_frame (fsu_fParams (lhC_fs k1 hb h c) (fh_val (fh_adj h bsm)))
          (TInit (dd_ox (lc_dd c)) (lh_dd_ts (lc_dd c) (lc_lxb c)))
          (FP_zstd hb (z_start h dm bsm ign)) (g4_lay (lc_dd c)) (lc_dd c).
Proof.
intros k1 hb h c bsm dm ign Ht Hp Hbo Hc1 Hc2 Hbsm Hbm Hws Hwin Hfcs Hck Hdm Hign.
pose proof (g4_lay_lhC k1 hb h c bsm Hp Hbo) as Hlay.
pose proof (proj2 (g4_lay_fields (c3_fs k1) (dp_fmt (c3_par k1)) (lc_dd c) (lc_cold c) Hp Hbo)) as Hldd.
pose proof (g4_cold k1 hb h c bsm Hc1 Hc2) as Hcold. cbv zeta in Hcold.
pose proof (g4_tabs _ (lc_lxb c) _ Hdm) as Htabs.
unfold c_frame. cbn [zp_h z_start zp_bsm zp_ign zp_dm zp_ts zp_out zp_ph zp_got].
split; [ | split; [ exact Hcold | split; [ | split; [ exact Hlay | split; [ exact Hldd | ] ] ] ] ].
- unfold lhC_fs, lh_dd_fs. replace (fh_frameType h =? 1) with false by (symmetry; apply Z.eqb_neq; lia).
  destruct (lc_dd c) as [[x buf]|]; reflexivity.
- unfold lhC_fs. replace (fh_frameType h =? 1) with false by (symmetry; apply Z.eqb_neq; lia). cbn. eexists; reflexivity.
- split; [ exact Ht | ]. split; [ reflexivity | ]. split; [ exact Hbsm | ]. split; [ exact Hbm | ].
  split; [ exact Hws | ]. split; [ exact Hwin | ]. split; [ exact Hfcs | ]. split; [ exact Hck | ].
  split; [ exact Hdm | ]. split; [ exists (lh_dd_ts (lc_dd c) (lc_lxb c)); split; [ reflexivity | exact Htabs ] | ].
  unfold lhC_fs. replace (fh_frameType h =? 1) with false by (symmetry; apply Z.eqb_neq; lia). subst ign. cbn.
  split; [ split; reflexivity | ].
  split; [ unfold lh_dd_fs; destruct (lc_dd c) as [[x buf]|]; reflexivity | ].
  split; [ reflexivity | ].
  split; [ intros Hv; rewrite Hv; reflexivity | ].
  split; [ constructor | ]. split; [ unfold ZSTD_blockHeaderSize; lia | constructor ].
Qed.

Lemma g4_cframe_skip : forall k1 hb h c bsm,
  fh_frameType h = 1 -> get_frame_header hb = FH_ok h -> bsm = fh_blockSizeMax h ->
  (forall x buf, lc_dd c = Some (x, buf) -> isptr buf \/ (buf = nullval /\ dx_ref x = Some nullval /\ dx_bytes x = nil)) ->
  (forall x buf, lc_dd c = Some (x, buf) -> bytes_ok (dx_bytes x) /\ (ddx_copied x = true -> 0 < Zlength (dx_bytes x))) ->
  (lc_cold c = Vint (Int.repr 0) \/ lc_cold c = Vint (Int.repr 1)) ->
  (fs_ddictIsCold (c3_fs k1) = Vint (Int.repr 0) \/ fs_ddictIsCold (c3_fs k1) = Vint (Int.repr 1)) ->
  0 <= le_field hb 4 4 < 2 ^ 32 ->
  c_frame (fsu_fParams (lhC_fs k1 hb h c) (fh_val (fh_adj h bsm)))
          (TInit (dd_ox (lc_dd c)) (lh_dd_ts (lc_dd c) (lc_lxb c)))
          (FP_skip hb 0) (g4_lay (lc_dd c)) (lc_dd c).
Proof.
intros k1 hb h c bsm Ht Hg Hb Hp Hbo Hc1 Hc2 Hlf. subst bsm.
pose proof (g4_lay_lhC k1 hb h c (fh_blockSizeMax h) Hp Hbo) as Hlay.
pose proof (proj2 (g4_lay_fields (c3_fs k1) (dp_fmt (c3_par k1)) (lc_dd c) (lc_cold c) Hp Hbo)) as Hldd.
pose proof (g4_cold k1 hb h c (fh_blockSizeMax h) Hc1 Hc2) as Hcold. cbv zeta in Hcold.
unfold c_frame.
split; [ | split; [ exact Hcold | split; [ | split; [ exact Hlay | split; [ exact Hldd | ] ] ] ] ].
- unfold lhC_fs, lh_dd_fs. rewrite Ht. destruct (lc_dd c) as [[x buf]|]; reflexivity.
- unfold lhC_fs, lh_dd_fs. rewrite Ht. destruct (lc_dd c) as [[x buf]|]; cbn; eexists; reflexivity.
- split; [ unfold g4_lay; destruct (lc_dd c) as [[x buf]|];
           [ destruct (eq_dec buf nullval); [ left; reflexivity | right; do 3 eexists; reflexivity ] | left; reflexivity ] | ].
  split; [ eexists; reflexivity | ].
  split; [ exists h; split; [ exact Hg | split; [ exact Ht | reflexivity ] ] | ].
  split; [ lia | ]. split; [ lia | ].
  unfold lhC_fs. rewrite Ht. change (1 =? 1) with true. cbv iota.
  cbn [fsu_fParams fsu_stage fsu_expected fs_stage fs_expected].
  destruct (Z.eqb_spec 0 (le_field hb 4 4)) as [E|E].
  + split; [ right; reflexivity | unfold vlong; rewrite <- E; reflexivity ].
  + split; reflexivity.
Qed.

End CM_LH3G42_frame_1.
