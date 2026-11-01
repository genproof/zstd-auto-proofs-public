(* FS3-bl stages 3/4, compressed block: the history zstd sees at the call (cap > 0). *)
Require Export Zstd.proof.dec.v3.FS.BL.body.s34.comp.CompPure.
Local Open Scope Z_scope.

Section CM_CompHist_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma comp_ext_len shk od : bd_wf od -> ext_len (comp_ext shk od) = bd_clen od.
Proof.
  intros Hwf. destruct od as [d|]; [| reflexivity].
  destruct Hwf as [(_ & _ & _ & Hp & _) | (Hn & Hbn & Hds0 & _)].
  - rewrite comp_ext_ptr by exact Hp. reflexivity.
  - rewrite comp_ext_nil by exact Hn. cbn. rewrite Hbn, Hds0. reflexivity.
Qed.

Lemma comp_seg_len ba opos oc (bs: list Z) :
  0 <= bl_start ba opos <= opos -> opos <= Zlength oc -> sublist (bl_start ba opos) opos oc = zbytes bs ->
  Zlength bs = opos - bl_start ba opos.
Proof.
  intros Hf Hl E. apply (f_equal (@Zlength val)) in E. rewrite Zlength_sublist, Zlength_map in E by lia. lia.
Qed.

Lemma comp_seg_at ba opos oc (bs: list Z) k :
  0 <= bl_start ba opos <= opos -> opos <= Zlength oc -> sublist (bl_start ba opos) opos oc = zbytes bs ->
  1 <= k <= opos - bl_start ba opos ->
  Znth (opos - k) oc = Vint (Int.repr (Znth (opos - k - bl_start ba opos) bs)).
Proof.
  intros Hf Hl E Hk.
  assert (Lb: Zlength bs = opos - bl_start ba opos)
    by (apply (f_equal (@Zlength val)) in E; rewrite Zlength_sublist, Zlength_map in E by lia; lia).
  replace (Znth (opos - k) oc) with (Znth (opos - k - bl_start ba opos) (sublist (bl_start ba opos) opos oc))
    by (rewrite Znth_sublist by lia; f_equal; lia).
  rewrite E, Znth_map by lia. reflexivity.
Qed.

(* the bytes zstd may copy from: the output so far and the dictionary *)
Lemma comp_hist_def shk od ba ob opos oc :
  bl_hist_ok ba ob opos oc -> 0 <= opos <= Zlength oc -> bd_wf od ->
  (forall b, ba_st ba = Some b -> bytes_ok (bs_out b)) ->
  hist_def oc opos (bl_start ba opos) (comp_ext shk od).
Proof.
  intros Hh Hl Hwf HD k Hk.
  destruct (comp_seg _ _ _ _ Hh Hl) as (Hf & Hs & Hn).
  assert (Hcb: cells_bytes (sublist (bl_start ba opos) opos oc)).
  { destruct (ba_st ba) as [b |] eqn:Eb.
    - exists (bs_out b). split; [apply Hs; auto | apply HD; auto].
    - apply Hn; auto. }
  destruct Hcb as (bs & Ebs & Bbs). rewrite (comp_ext_len shk od Hwf) in Hk.
  unfold chist. destruct (Z.leb_spec k (opos - bl_start ba opos)) as [Ek | Ek].
  - rewrite (comp_seg_at ba opos oc bs k) by (auto; lia).
    pose proof (comp_seg_len ba opos oc bs Hf ltac:(lia) Ebs).
    exists (Znth (opos - k - bl_start ba opos) bs). split; [| reflexivity].
    apply (proj1 (Forall_Znth _ _) Bbs). lia.
  - destruct od as [d |]; [| cbn [bd_clen] in *; lia].
    destruct Hwf as [(Hds & _ & Hb & Hp & _) | (_ & Hbn & Hds0 & _)].
    2:{ cbn [bd_clen] in *. rewrite Hbn, Hds0, Zlength_nil in Hk. lia. }
    rewrite comp_ext_ptr by exact Hp. cbn [bd_clen] in *.
    rewrite Znth_map by lia.
    exists (Znth (Zlength (bd_b d) - (k - (opos - bl_start ba opos))) (bd_b d)). split; [| reflexivity].
    apply (proj1 (Forall_Znth _ _) Hb). lia.
Qed.

(* the empty window at the end of the output (no room, cap = 0): its history is the dictionary only *)
Lemma comp_hist_def0 shk od ps :
  0 <= ps -> bd_wf od -> hist_def [] 0 ps (comp_ext shk od).
Proof.
  intros Hps Hwf k Hk. rewrite (comp_ext_len shk od Hwf) in Hk.
  unfold chist. replace (k <=? 0 - ps) with false by (symmetry; apply Z.leb_gt; lia).
  destruct od as [d |]; [| cbn [bd_clen] in *; lia].
  destruct Hwf as [(Hds & _ & Hb & Hp & _) | (_ & Hbn & Hds0 & _)].
  2:{ cbn [bd_clen] in *. rewrite Hbn, Hds0, Zlength_nil in Hk. lia. }
  rewrite comp_ext_ptr by exact Hp. cbn [bd_clen] in *.
  rewrite Znth_map by lia.
  exists (Znth (Zlength (bd_b d) - (k - (0 - ps))) (bd_b d)). split; [| reflexivity].
  apply (proj1 (Forall_Znth _ _) Hb). lia.
Qed.

(* the model's history (dictionary content, frame output so far) is what zstd sees *)
Lemma comp_hist_view shk od ba ob opos oc b dm ws :
  bl_hist_ok ba ob opos oc -> 0 <= opos <= Zlength oc -> bd_wf od -> bd_model_ok (ba_dict ba) od ->
  ba_st ba = Some b -> dictref_model (ba_dict ba) = Some dm ->
  hist_view oc opos (bl_start ba opos) (comp_ext shk od) (dm_content dm) (bs_out b) ws.
Proof.
  intros Hh Hl Hwf Hm Hb Hdm k Hk.
  destruct (comp_seg _ _ _ _ Hh Hl) as (Hf & Hs & _). specialize (Hs b Hb).
  destruct (comp_hist_suffix od _ Hwf Hm dm Hdm) as (Lh & _ & Hsuf).
  pose proof (comp_seg_len ba opos oc (bs_out b) Hf ltac:(lia) Hs) as Lo.
  rewrite Zlength_app in Hk.
  assert (Hk1: 1 <= k <= Zlength (dm_content dm) + Zlength (bs_out b)) by lia.
  rewrite (comp_ext_len shk od Hwf). split; [lia |].
  rewrite Zlength_app. rewrite byte_at_Znth by lia.
  unfold chist. destruct (Z.leb_spec k (opos - bl_start ba opos)) as [Ek | Ek].
  - rewrite (comp_seg_at ba opos oc (bs_out b) k) by (auto; lia).
    rewrite Znth_app2 by lia. do 3 f_equal. lia.
  - destruct od as [d |]; [| cbn [bd_clen] in *; lia].
    destruct Hwf as [(Hds & _ & Hb' & Hp & _) | (_ & Hbn & Hds0 & _)].
    2:{ cbn [bd_clen] in *. rewrite Hbn, Hds0, Zlength_nil in Lh. pose proof (Zlength_nonneg (dm_content dm)). lia. }
    rewrite comp_ext_ptr by exact Hp. cbn [bd_clen] in *.
    assert (Hz: forall i, 0 <= i < Zlength (dm_content dm) ->
               Znth i (dm_content dm) = Znth (i + (Zlength (bd_b d) - Zlength (dm_content dm))) (bd_b d)).
    { intros i Hi. pose proof (Hsuf d eq_refl) as E. remember (Zlength (dm_content dm)) as lh.
      rewrite E. rewrite Znth_sublist by lia. reflexivity. }
    rewrite Znth_map by lia. rewrite Znth_app1 by lia. rewrite Hz by lia.
    do 3 f_equal. lia.
Qed.

End CM_CompHist_1.
