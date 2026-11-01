(* Bodies of vp_windows_within and vp_blocks_within of the unit valid_params (harness/valid_params.c: read the
   static sr) against their specifications in the v3 template WTopSpecs (same loop as within_stream in
   the template WB_misc_within_body).  Kept out of the generated WB_new3_valid_params.v;
   WB3_within.wb3_within concludes from them. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zstd.proof.harness.valid_params.WSpecs_valid_params.
Import compcert.lib.Maps.
Local Open Scope logic.

(* the frame k of sr.f (as VST reads it) is winfo_val of the k-th frame; the helpers below also serve
   vp_blocks_within (both functions exist only in valid_params) *)
#[local] Instance Inhabitant_winfo3 : Inhabitant winfo := winfo0.

Lemma windows_within_b_snoc (fs: list winfo) (lim k: Z) :
  0 <= k < Zlength fs ->
  windows_within_b (sublist 0 (k + 1) fs) lim =
  andb (windows_within_b (sublist 0 k fs) lim) (wi_skippable (Znth k fs) || (wi_window (Znth k fs) <=? lim))%bool.
Proof.
  intros Hk. unfold windows_within_b. rewrite (sublist_split 0 k (k + 1)) by lia.
  rewrite forallb_app, sublist_len_1 by lia. simpl. rewrite andb_true_r. reflexivity.
Qed.

Ltac wf_rw3 ws fs k :=
  match goal with |- context [Znth k ?L] =>
    replace (Znth k L) with (winfo_val (Znth k fs))
      by (unfold wseries_val; cbn [fst snd]; change (ws_frames ws) with fs;
          rewrite Znth_app1 by (rewrite Zlength_map; lia); rewrite Znth_map by lia; reflexivity)
  end.

Ltac ws_fold3 :=
  match goal with |- _ |-- data_at ?sh t_wseries ?v ?p => unfold_data_at (data_at sh t_wseries v p) end.

Lemma wb_vp_windows_within : body_vp_windows_within.
Proof.
  intros DC DD. start_function.
  destruct H0 as [Hwf [Hz Hl]].
  unfold_data_at (data_at _ _ _ _).
  set (fs := ws_frames ws) in *.
  assert (Hn: Zlength fs <= 4) by (rewrite Zlength_correct; lia).
  forward.
  match goal with |- semax _ (PROP () LOCAL (_; _; _) (SEP (?A; ?B; ?C; ?D; ?E; ?Fd; ?G))) _ _ =>
  forward_loop (EX k: Z,
      PROP (0 <= k <= Zlength fs; windows_within_b (sublist 0 k fs) lim = true)
      LOCAL (temp _k (vu k); gvars gv; temp _lim (Vlong (Int64.repr lim)))
      SEP (A; B; C; D; E; Fd; G))
    continue: (EX k: Z,
      PROP (0 <= k < Zlength fs; windows_within_b (sublist 0 (k + 1) fs) lim = true)
      LOCAL (temp _k (vu k); gvars gv; temp _lim (Vlong (Int64.repr lim)))
      SEP (A; B; C; D; E; Fd; G))
    break: (PROP (windows_within_b fs lim = true)
      LOCAL (gvars gv)
      SEP (A; B; C; D; E; Fd; G))
  end.
  - Exists 0. entailer!.
  - Intros k. forward.
    match goal with |- context [temp _x_valid_params__t'4 ?v] => change v with (vu (Zlength fs)) end.
    forward_if.
    + forward.
      { wf_rw3 ws fs k. unfold winfo_val; cbv beta iota.
        entailer!; destruct (wi_skippable (Znth k fs)); exact I. }
      wf_rw3 ws fs k. unfold winfo_val at 1; cbv beta iota.
      assert (Hf: winfo_wf (Znth k fs)) by (rewrite Forall_forall in Hwf; apply Hwf, Znth_In; lia).
      set (f := Znth k fs) in *.
      match goal with |- semax _ (PROP () LOCAL (_; _; _; _; _) (SEP (?A; ?B; ?C; ?D; ?E; ?Fd; ?G))) _ _ =>
      forward_if (PROP () LOCAL (temp _x_valid_params__t'1
                                   (vb (negb (wi_skippable f || (wi_window f <=? lim))%bool));
                                 temp _k (vu k); gvars gv; temp _lim (Vlong (Int64.repr lim)))
                  SEP (A; B; C; D; E; Fd; G)) end.
      * forward.
        { wf_rw3 ws fs k. unfold winfo_val; cbv beta iota. entailer!. }
        wf_rw3 ws fs k. unfold winfo_val at 1; cbv beta iota. fold f.
        forward.
        entailer!.
        clear - Hf H4 H1. destruct Hf as (_&_&_&_&_&_&_&_&Hw&_). unfold u64 in Hw. clearbody f.
        unfold Int64.cmpu, Int64.ltu. rewrite !Int64.unsigned_repr by rep_lia.
        destruct (wi_skippable f); [vm_compute in H4; discriminate |]. cbn [orb].
        destruct (zlt lim (wi_window f)), (Z.leb_spec (wi_window f) lim); try reflexivity; lia.
      * forward.
        entailer!.
        fold f. clear - H4. clearbody f. unfold vb in *.
        destruct (wi_skippable f); try (contradiction H4; reflexivity); reflexivity.
      * forward_if.
        -- forward.
           assert (Hb: windows_within_b fs lim = false).
           { destruct (windows_within_b fs lim) eqn:E; [|reflexivity]. unfold windows_within_b in E.
             rewrite forallb_forall in E.
             assert (Hi: In f fs) by (apply Znth_In; lia). specialize (E _ Hi).
             rewrite E in H4'. simpl in H4'. contradiction H4'; reflexivity. }
           rewrite Hb. apply andp_right; [apply prop_right; reflexivity |]. ws_fold3. cancel.
        -- forward. Exists k. entailer!.
           rewrite windows_within_b_snoc by lia. rewrite H2. fold f. clear - H4. clearbody f.
           destruct (wi_skippable f || (wi_window f <=? lim))%bool; [reflexivity |].
           contradiction (Int.one_not_zero H4).
    + forward. entailer!.
      replace k with (Zlength fs) in H2 by lia. rewrite sublist_same in H2 by lia. exact H2.
  - Intros k. forward. Exists (k + 1). entailer!.
  - Intros. forward.
    match goal with H: windows_within_b fs lim = true |- _ => rewrite H end.
    apply andp_right; [apply prop_right; reflexivity |]. ws_fold3. cancel.
Qed.


Lemma blocks_within_b_snoc (fs: list winfo) (lim k: Z) :
  0 <= k < Zlength fs ->
  blocks_within_b (sublist 0 (k + 1) fs) lim =
  andb (blocks_within_b (sublist 0 k fs) lim)
    (wi_skippable (Znth k fs) || ((wi_csize (Znth k fs) <=? lim) && (wi_size (Znth k fs) <=? lim)))%bool.
Proof.
  intros Hk. unfold blocks_within_b. rewrite (sublist_split 0 k (k + 1)) by lia.
  rewrite forallb_app, sublist_len_1 by lia. simpl. rewrite andb_true_r. reflexivity.
Qed.

Lemma wb_vp_blocks_within : body_vp_blocks_within.
Proof.
  intros DC DD. start_function.
  destruct H0 as [Hwf [Hz Hl]].
  unfold_data_at (data_at _ _ _ _).
  set (fs := ws_frames ws) in *.
  assert (Hn: Zlength fs <= 4) by (rewrite Zlength_correct; lia).
  forward.
  match goal with |- semax _ (PROP () LOCAL (_; _; _) (SEP (?A; ?B; ?C; ?D; ?E; ?Fd; ?G))) _ _ =>
  forward_loop (EX k: Z,
      PROP (0 <= k <= Zlength fs; blocks_within_b (sublist 0 k fs) lim = true)
      LOCAL (temp _k (vu k); gvars gv; temp _lim (Vlong (Int64.repr lim)))
      SEP (A; B; C; D; E; Fd; G))
    continue: (EX k: Z,
      PROP (0 <= k < Zlength fs; blocks_within_b (sublist 0 (k + 1) fs) lim = true)
      LOCAL (temp _k (vu k); gvars gv; temp _lim (Vlong (Int64.repr lim)))
      SEP (A; B; C; D; E; Fd; G))
    break: (PROP (blocks_within_b fs lim = true)
      LOCAL (gvars gv)
      SEP (A; B; C; D; E; Fd; G))
  end.
  - Exists 0. entailer!.
  - Intros k. forward.
    match goal with |- context [temp _x_valid_params__t'5 ?v] => change v with (vu (Zlength fs)) end.
    forward_if.
    + forward.
      { wf_rw3 ws fs k. unfold winfo_val; cbv beta iota.
        entailer!; destruct (wi_skippable (Znth k fs)); exact I. }
      wf_rw3 ws fs k. unfold winfo_val at 1; cbv beta iota.
      assert (Hf: winfo_wf (Znth k fs)) by (rewrite Forall_forall in Hwf; apply Hwf, Znth_In; lia).
      set (f := Znth k fs) in *.
      match goal with |- semax _ (PROP () LOCAL (_; _; _; _; _) (SEP (?A; ?B; ?C; ?D; ?E; ?Fd; ?G))) _ _ =>
      forward_if (PROP () LOCAL (temp _x_valid_params__t'1
                   (vb (negb (wi_skippable f || ((wi_csize f <=? lim) && (wi_size f <=? lim))))%bool);
                                 temp _k (vu k); gvars gv; temp _lim (Vlong (Int64.repr lim)))
                  SEP (A; B; C; D; E; Fd; G)) end.
      * assert (Hs: wi_skippable f = false)
          by (clear - H4; destruct (wi_skippable f); [vm_compute in H4; discriminate | reflexivity]).
        destruct Hf as (_&_&Hsz&_&Hcs&_). unfold u64 in Hsz, Hcs.
        forward.
        { wf_rw3 ws fs k. unfold winfo_val; cbv beta iota. entailer!. }
        wf_rw3 ws fs k. unfold winfo_val at 1; cbv beta iota. fold f.
        match goal with |- semax _ (PROP () LOCAL (_; _; _; _; _; _) (SEP (?A; ?B; ?C; ?D; ?E; ?Fd; ?G))) _ _ =>
        forward_if (PROP () LOCAL (temp _x_valid_params__t'1
                     (vb (negb (wi_skippable f || ((wi_csize f <=? lim) && (wi_size f <=? lim))))%bool);
                                   temp _k (vu k); gvars gv; temp _lim (Vlong (Int64.repr lim)))
                    SEP (A; B; C; D; E; Fd; G)) end.
        -- forward. entailer!. rewrite Hs. cbn [orb].
           destruct (Z.leb_spec (wi_csize f) lim); [lia | reflexivity].
        -- forward.
           { wf_rw3 ws fs k. unfold winfo_val; cbv beta iota. entailer!. }
           wf_rw3 ws fs k. unfold winfo_val at 1; cbv beta iota. fold f.
           forward. forward.
           entailer!. rewrite Hs. cbn [orb].
           destruct (Z.leb_spec (wi_csize f) lim); [|lia]. cbn [andb].
           unfold Int64.cmpu, Int64.ltu. rewrite !Int64.unsigned_repr by rep_lia.
           destruct (zlt lim (wi_size f)), (Z.leb_spec (wi_size f) lim); try reflexivity; lia.
      * forward.
        entailer!.
        fold f. clear - H4. clearbody f. unfold vb in *.
        destruct (wi_skippable f); try (contradiction H4; reflexivity); reflexivity.
      * forward_if.
        -- forward.
           assert (Hb: blocks_within_b fs lim = false).
           { destruct (blocks_within_b fs lim) eqn:E; [|reflexivity]. unfold blocks_within_b in E.
             rewrite forallb_forall in E.
             assert (Hi: In f fs) by (apply Znth_In; lia). specialize (E _ Hi).
             rewrite E in H4'. simpl in H4'. contradiction H4'; reflexivity. }
           rewrite Hb. apply andp_right; [apply prop_right; reflexivity |]. ws_fold3. cancel.
        -- forward. Exists k. entailer!.
           rewrite blocks_within_b_snoc by lia. rewrite H2. fold f. clear - H4. clearbody f.
           destruct (wi_skippable f || ((wi_csize f <=? lim) && (wi_size f <=? lim)))%bool; [reflexivity |].
           contradiction (Int.one_not_zero H4).
    + forward. entailer!.
      replace k with (Zlength fs) in H2 by lia. rewrite sublist_same in H2 by lia. exact H2.
  - Intros k. forward. Exists (k + 1). entailer!.
  - Intros. forward.
    match goal with H: blocks_within_b fs lim = true |- _ => rewrite H end.
    apply andp_right; [apply prop_right; reflexivity |]. ws_fold3. cancel.
Qed.
