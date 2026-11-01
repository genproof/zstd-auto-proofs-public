(* FS3 one-shot frames, ZSTD_decompressMultiFrame: the model's dictionary of a frame after fix F4's probe *)
Require Export Zstd.proof.dec.v3.FS.frames.Multi3Res.
Local Open Scope logic.

Section CM_Multi3FD_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* helpers (copies of Frames3Model's f3m_probe / hs_probe_in, not in this file's dependencies) *)
Lemma mfd_probe: forall fuel l tbl j n id, n = Zlength tbl -> 0 <= j < n ->
  hs_probe_f fuel l tbl j n id <> nullval -> In (hs_probe_f fuel l tbl j n id) tbl.
Proof.
  induction fuel as [|f IH]; intros l tbl j n id En Hj H; cbn [hs_probe_f] in *; [contradiction|].
  destruct (eq_dec (Znth j tbl) nullval) as [N|N]; [contradiction|].
  destruct (orb _ _).
  - apply Znth_In. lia.
  - apply IH; auto. apply Z.mod_pos_bound. lia.
Qed.

Lemma mfd_probe_in: forall l tbl id,
  hs_inv l tbl -> hs_probe l tbl id <> nullval -> In (hs_probe l tbl id) (map fst l).
Proof.
  intros l tbl id Hi Hn. destruct Hi as ([k [Hk En]] & _ & _ & _ & _ & _ & Hp & _).
  unfold hs_probe in *.
  assert (Hj: 0 <= hs_home id (Zlength tbl) < Zlength tbl).
  { unfold hs_home. rewrite En. replace (2 ^ k - 1) with (Z.ones k) by (rewrite Z.ones_equiv; lia).
    rewrite Z.land_ones by lia. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia. }
  pose proof (mfd_probe _ l tbl _ _ id eq_refl Hj Hn) as Hin.
  eapply Permutation_in; [exact Hp|]. apply filter_In. split; [exact Hin|].
  unfold veqb. destruct (Val.eq _ nullval); [contradiction|reflexivity].
Qed.

(* the model's dictionary of the frame is the one `ddict` holds after the probe *)
Lemma mf_frame_dict: forall pr sp a l tbl shk qv sfr dm,
  hs_inv l tbl ->
  (forall x buf sh dd, a = DA_ddict x buf sh -> In (dx_q x, dd) l -> x = dd_x (dx_q x) dd) ->
  darg_model (mf_dict a l shk (mf_probe pr sp a l tbl qv sfr)) = Some dm ->
  darg_model (mf_dict a l shk qv) <> None ->
  frame_dict (dp_fmt pr =? 1) (mf_sel pr sp a l tbl) (darg_model (mf_dict a l shk qv)) sfr = Some dm.
Proof.
  intros pr sp a l tbl shk qv sfr dm Hi Ha Hd Hn.
  unfold frame_dict, mf_sel. unfold mf_probe in Hd.
  destruct (andb (sel_on pr sp) (negb (veqb (darg_ddict a) nullval))) eqn:Es.
  2:{ unfold sel_none. destruct (get_frame_header_m (dp_fmt pr =? 1) sfr); rewrite Hd; reflexivity. }
  destruct (get_frame_header_m (dp_fmt pr =? 1) sfr) as [ | k | h] eqn:Eh;
    try (rewrite Hd; reflexivity).
  unfold psel.
  destruct (eq_dec (hs_probe l tbl (fh_dictID h)) nullval) as [E0|E0]; [rewrite Hd; reflexivity|].
  set (x := hs_probe l tbl (fh_dictID h)) in *.
  pose proof (mfd_probe_in l tbl (fh_dictID h) Hi E0) as Hin. fold x in Hin.
  destruct (find (fun e => veqb (fst e) x) l) as [e|] eqn:Ef.
  2:{ exfalso. apply in_map_iff in Hin. destruct Hin as [e [He1 He2]].
      eapply find_none in Ef; [|exact He2]. unfold veqb in Ef.
      destruct (Val.eq (fst e) x); [discriminate|contradiction]. }
  pose proof (find_some _ _ Ef) as [Hel Hex]. unfold veqb in Hex.
  destruct (Val.eq (fst e) x) as [Hfx|]; [|discriminate]. clear Hex.
  assert (Hm: darg_model (mf_dict a l shk x) = ddx_model (dd_x (fst e) (snd e))).
  { unfold mf_dict. destruct (veqb x (darg_ddict a)) eqn:Eq.
    - unfold veqb in Eq. destruct (Val.eq x (darg_ddict a)) as [Exa|]; [|discriminate].
      destruct a as [| | y buf sh]; simpl in Exa; try (subst; contradiction).
      simpl. rewrite (Ha y buf sh (snd e) eq_refl).
      + rewrite Hfx, Exa. reflexivity.
      + rewrite <- Exa, <- Hfx. destruct e; exact Hel.
    - rewrite Ef. simpl. rewrite Hfx. reflexivity. }
  rewrite Hm in Hd. rewrite Hd. reflexivity.
Qed.

End CM_Multi3FD_1.
