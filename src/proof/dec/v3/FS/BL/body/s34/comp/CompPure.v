(* FS3-bl stages 3/4, compressed block: the history context of the block decoder's call and the pure
   facts about it (layout, history pointers, the history zstd sees). *)
Require Export Zstd.proof.dec.v3.FS.BL.body.s34.S34Defs.
Local Open Scope Z_scope.

Section CM_CompPure_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* ---------- the call's history context ---------- *)

(* the dictionary as a separate extDict: its whole array, ending at its end, its content clen bytes long; none for
   the dictionary at NULL (the DDict without content: zstd's history pointers are those of no dictionary) *)
Definition comp_ext (shk: share) (od: option bldict) : ext_seg :=
  match od with
  | None => ExtNone
  | Some d =>
      if eq_dec (bd_eb d) nullval then ExtNone
      else ExtSep shk (bd_eb d) (Zlength (bd_b d)) (zbytes (bd_b d)) (Zlength (bd_b d)) (bd_clen od)
  end.

Lemma comp_ext_ptr shk d : isptr (bd_eb d) ->
  comp_ext shk (Some d) =
  ExtSep shk (bd_eb d) (Zlength (bd_b d)) (zbytes (bd_b d)) (Zlength (bd_b d)) (bd_clen (Some d)).
Proof.
  intros Hp. unfold comp_ext. destruct (eq_dec (bd_eb d) nullval) as [E|E]; [rewrite E in Hp; contradiction | reflexivity].
Qed.

Lemma comp_ext_nil shk d : bd_eb d = nullval -> comp_ext shk (Some d) = ExtNone.
Proof. intros E. unfold comp_ext. destruct (eq_dec (bd_eb d) nullval) as [_|E']; [reflexivity | contradiction]. Qed.

Lemma comp_ext_res shk od : ext_res (comp_ext shk od) = bd_res shk od.
Proof.
  destruct od as [d|]; [| reflexivity]. unfold comp_ext, bd_res, bytes_at.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; first [reflexivity | congruence].
Qed.

Definition comp_hist (ba: blabs) : list Z :=
  match dictref_model (ba_dict ba) with Some dm => dm_content dm | None => nil end.
Definition comp_out (ba: blabs) : list Z :=
  match ba_st ba with Some b => bs_out b | None => nil end.

Definition comp_h (shk: share) (od: option bldict) (ba: blabs) (v: blv) (opos: Z) : hctx :=
  {| hc_ext := comp_ext shk od; hc_ps := bl_start ba opos; hc_hist := comp_hist ba; hc_out := comp_out ba;
     hc_wsize := fh_windowSize (bv_h v) |}.

(* ---------- small facts ---------- *)

Lemma byte_at_Znth (l: list Z) i : 0 <= i -> byte_at l i = Znth i l.
Proof. intros. unfold byte_at, Znth. destruct (Z_lt_dec i 0); [lia | reflexivity]. Qed.

Lemma fs1_keep fs ob osz opos pcs n :
  fs_fParams (bl_fs1 fs ob osz opos pcs n) = fs_fParams fs /\
  fs_isFrameDecompression (bl_fs1 fs ob osz opos pcs n) = fs_isFrameDecompression fs /\
  fs_ddictIsCold (bl_fs1 fs ob osz opos pcs n) = fs_ddictIsCold fs.
Proof. unfold bl_fs1, continuity. destruct (cont_moves _ _ _); repeat split. Qed.

Lemma comp_cinv md od osz0 ba fs hb v :
  bl_cinv md od osz0 ba fs hb v -> (bv_stage v = BBlk \/ bv_stage v = BLastBlk) ->
  hdr_ok (bv_h v) /\ fs_fParams fs = fh_val (bv_h v) /\ fs_isFrameDecompression fs = Vint (Int.repr 1) /\
  cold01 fs /\ bd_wf od.
Proof.
  intros (_ & _ & _ & Hif & Hc & _ & _ & _ & _ & Hwf & Hcs & _) Hst. unfold bl_cstage in Hcs.
  destruct Hst as [Hs | Hs]; rewrite Hs in Hcs; destruct Hcs as ((Hh & Hf & _) & _); auto.
Qed.

Lemma comp_mrel md ba fs ts v b :
  bl_mrel md ba fs ts v -> (bv_stage v = BBlk \/ bv_stage v = BLastBlk) -> ba_st ba = Some b ->
  bs_ds b = ts /\ bs_hdr b = bv_h v /\ bs_btype b = bv_bt v.
Proof.
  intros Hm Hst Hb. destruct (Hm b Hb) as (_ & _ & Hds & _ & _ & Hx).
  destruct Hst as [Hs | Hs]; rewrite Hs in Hx; destruct Hx as (Hh & Hbt & _); auto.
Qed.

Lemma comp_blk_model dm b c ts v :
  bs_ds b = ts -> bs_hdr b = bv_h v -> bs_btype b = 2 ->
  blk_model dm b c = decode_block ts (dm_content dm) (bs_out b) c (fh_blockSizeMax (bv_h v)) (fh_windowSize (bv_h v)).
Proof. intros Hd Hh Ht. unfold blk_model. rewrite Ht, Hd, Hh. reflexivity. Qed.

(* the model's dictionary content is a suffix of zstd's *)
Lemma comp_hist_suffix od odr :
  bd_wf od -> bd_model_ok odr od -> forall dm, dictref_model odr = Some dm ->
  Zlength (dm_content dm) <= bd_clen od /\ bytes_ok (dm_content dm) /\
  (forall d, od = Some d -> dm_content dm = sublist (Zlength (bd_b d) - Zlength (dm_content dm)) (Zlength (bd_b d)) (bd_b d)).
Proof.
  intros Hwf Hm dm Hdm. destruct (Hm dm Hdm) as (_ & pre & Hc).
  destruct od as [d |]; cbn [bd_content bd_clen bd_wf] in *.
  - destruct Hwf as [(Hds & _ & Hb & _) | (_ & Hbn & Hds0 & _)].
    2:{ rewrite Hbn, Hds0 in *. rewrite sublist_of_nil in Hc. symmetry in Hc. apply app_eq_nil in Hc.
        destruct Hc as [_ ->]. split; [rewrite Zlength_nil; lia |]. split; [constructor |].
        intros d' E. inv E. rewrite Hbn, sublist_of_nil. reflexivity. }
    assert (Lc: Zlength (pre ++ dm_content dm) = Zlength (bd_b d) - bd_ds0 d)
      by (rewrite <- Hc, Zlength_sublist; lia).
    rewrite Zlength_app in Lc. pose proof (Zlength_nonneg pre). pose proof (Zlength_nonneg (dm_content dm)).
    assert (Hdm2: dm_content dm = sublist (Zlength pre) (Zlength pre + Zlength (dm_content dm)) (pre ++ dm_content dm))
      by (rewrite sublist_app2 by lia; rewrite Z.sub_diag, Z.add_simpl_l, sublist_same; auto).
    split; [lia |]. split.
    + rewrite Hdm2, <- Hc. apply Forall_sublist, Forall_sublist, Hb.
    + intros d' E. inv E. rewrite Hdm2 at 1. rewrite <- Hc. rewrite sublist_sublist by lia. f_equal; lia.
  - symmetry in Hc. apply app_eq_nil in Hc. destruct Hc as [_ ->]. split; [reflexivity |]. split; [constructor |].
    intros; discriminate.
Qed.

(* ---------- the history pointers ---------- *)

Lemma comp_lay_ptrs od osz ba ob opos fs' :
  bd_wf od -> bl_lay od osz (bl_moved ba ob opos) fs' ->
  is_pointer_or_null (fs_prefixStart fs') /\ is_pointer_or_null (fs_virtualStart fs') /\
  (fs_dictEnd fs' = nullval \/ fs_dictEnd fs' = bd_end od).
Proof.
  intros Hwf Hl.
  assert (Hs: is_pointer_or_null (bd_start od)).
  { destruct od as [d |]; cbn [bd_start bd_wf] in *; [| apply mapsto_memory_block.is_pointer_or_null_nullval].
    destruct Hwf as [(_ & _ & _ & Hp & _) | (Hn & _)].
    - destruct (bd_eb d); try contradiction; exact I.
    - rewrite Hn. exact mapsto_memory_block.is_pointer_or_null_nullval. }
  assert (He: bd_de0o od = nullval \/ bd_de0o od = bd_end od).
  { destruct od as [d |]; cbn [bd_de0o bd_end bd_wf] in *; [| left; reflexivity].
    destruct Hwf as [(_ & _ & _ & Hp & _ & _ & H & _) | (_ & _ & _ & _ & _ & H)]; [| left; exact H].
    rewrite bd_off_ptr by exact Hp. exact H. }
  destruct Hl as [(_ & Hp & Hv & Hd & _) | [(ob' & f0 & _ & _ & _ & Hp & Hv & Hd & _) |
                                           (ob' & f0 & pe & _ & Hob & _ & _ & _ & Hp & Hv & Hd & _)]].
  - rewrite Hp, Hv, Hd. auto.
  - rewrite Hp, Hv, Hd. auto.
  - rewrite Hp, Hv, Hd. destruct ob'; try contradiction. split; [exact I |]. split; [exact I | auto].
Qed.

Lemma comp_hpo od osz ba ob opos fs' shk o :
  bd_wf od -> bl_lay od osz (bl_moved ba ob opos) fs' -> hist_ptrs_ok fs' o (comp_ext shk od).
Proof.
  intros Hwf Hl. destruct (comp_lay_ptrs _ _ _ _ _ _ Hwf Hl) as (H1 & H2 & H3).
  split; [exact H1 |]. split; [exact H2 |]. unfold dictend_ok.
  destruct H3 as [H3 | H3]; [left; exact H3 |].
  destruct od as [d |]; [| cbn in H3 |- *; left; exact H3].
  destruct Hwf as [(_ & _ & _ & Hp & _) | (Hn & _)].
  2:{ left. rewrite H3. cbn [bd_end]. rewrite Hn. reflexivity. }
  rewrite comp_ext_ptr by exact Hp. cbn [bd_end] in H3. rewrite bd_off_ptr in H3 by exact Hp.
  right; right. split; [exact H3 |]. pose proof (Zlength_nonneg (bd_b d)); lia.
Qed.

Lemma pws_wvp_null W : pws_pred W |-- weak_valid_pointer nullval.
Proof. eapply derives_trans; [apply valid_pointer_null | apply valid_pointer_weak]. Qed.

Lemma comp_ext0 W shk od shd cap dst fs' :
  bd_wf od -> bd_buf_ok W shk od shd cap dst -> (fs_dictEnd fs' = nullval \/ fs_dictEnd fs' = bd_end od) ->
  ext0_ok W fs' (comp_ext shk od).
Proof.
  intros Hwf Hb Hd. destruct od as [d |]; [| exact I].
  destruct Hwf as [(_ & _ & _ & Hp & _ & Hg & _) | (Hn & _)]; [| rewrite comp_ext_nil by exact Hn; exact I].
  rewrite comp_ext_ptr by exact Hp. cbn. intros H0.
  destruct Hd as [-> | ->]; [apply pws_wvp_null |]. cbn [bd_end]. rewrite bd_off_ptr by exact Hp.
  assert (Hg0: bd_g0 d = 0) by (destruct Hg as [| [_ Hl]]; [auto | lia]).
  specialize (Hb Hg0 Hp). rewrite H0, isptr_offset_val_zero by exact Hp.
  destruct Hb as [(_ & _ & Hbo) | (_ & Hv & _)].
  - unfold buf_ok in Hbo. rewrite H0 in Hbo.
    eapply derives_trans; [| eapply derives_trans; [exact Hbo | apply andp_left1, derives_refl]].
    rewrite data_at__eq, data_at_zero_array_eq; auto. rewrite sepcon_emp. apply derives_refl.
  - eapply derives_trans; [exact Hv | apply valid_pointer_weak].
Qed.

Lemma pws_cons_wvp pw W q : (pws_pred W |-- weak_valid_pointer q) -> pws_pred (pw :: W) |-- weak_valid_pointer q.
Proof. intros H. unfold pws_pred; simpl. apply sepcon_weak_valid_pointer2. exact H. Qed.

Lemma ext0_ok_cons pw W fs' e : ext0_ok W fs' e -> ext0_ok (pw :: W) fs' e.
Proof. destruct e; cbn; auto. intros H H0. apply pws_cons_wvp, H, H0. Qed.

(* cap > 0: the layout is the moved one *)
Lemma comp_lay_pos od osz ba ob opos fs' shk :
  bd_wf od -> readable_share shk -> opos < osz -> bl_lay od osz (bl_moved ba ob opos) fs' ->
  isptr ob /\ layout_ok fs' ob osz opos (bl_start ba opos) (comp_ext shk od) /\ fs_dictEnd fs' = bd_end od.
Proof.
  intros Hwf Hsh Hc Hl.
  destruct Hl as [(_ & _ & _ & _ & _ & Hm) | [(ob' & f0 & E & Hf & _) | (ob' & f0 & pe & E & Hob & Hf & Hpe & Hp & Hpr & Hv & Hd & _)]];
    cbn [bl_moved ba_out] in *.
  - destruct Hm as (Hm1 & Hm2). lia.
  - inv E. lia.
  - inv E. split; [exact Hob |]. split; [| exact Hd].
    unfold layout_ok. split; [lia |]. split; [exact Hpr |].
    destruct od as [d |].
    + destruct Hwf as [(Hds & Hbl & _ & Heb & _) | (Hn & Hbn & Hds0 & _)].
      * rewrite comp_ext_ptr by exact Heb. cbn [ext_len bd_clen] in *. split; [exact Hv |]. split; [lia |].
        split; [cbn [bd_end] in Hd; rewrite bd_off_ptr in Hd by exact Heb; exact Hd |].
        split; [exact Hsh |]. split; [apply Zlength_map |]. lia.
      * rewrite comp_ext_nil by exact Hn. cbn [ext_len bd_clen] in *. rewrite Hbn, Hds0, Zlength_nil in Hv.
        split; [rewrite Hv; f_equal; lia |]. split; [lia | exact I].
    + cbn [comp_ext ext_len bd_clen] in *. split; [rewrite Hv; f_equal; lia |]. split; [lia | exact I].
Qed.

(* ---------- the output so far ---------- *)

Lemma comp_seg ba ob opos oc :
  bl_hist_ok ba ob opos oc -> 0 <= opos <= Zlength oc ->
  0 <= bl_start ba opos <= opos /\
  (forall b, ba_st ba = Some b -> sublist (bl_start ba opos) opos oc = zbytes (bs_out b)) /\
  (ba_st ba = None -> cells_bytes (sublist (bl_start ba opos) opos oc)).
Proof.
  unfold bl_hist_ok, bl_start. intros H Hl.
  destruct (ba_out ba) as [[[ob' f0] pe] |].
  - destruct H as (_ & -> & Hf & Hs). split; [lia |].
    split; [intros b Hb; rewrite Hb in Hs; exact Hs | intros Hb; rewrite Hb in Hs; exact Hs].
  - rewrite sublist_nil.
    destruct (ba_st ba) as [b |].
    + split; [lia |]. split; [intros b' E; inv E; rewrite H; reflexivity | discriminate].
    + split; [lia |]. split; [discriminate | intros _; exists nil; split; [reflexivity | constructor]].
Qed.

End CM_CompPure_1.
