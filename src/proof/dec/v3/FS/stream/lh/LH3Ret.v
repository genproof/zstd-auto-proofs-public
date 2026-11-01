(* FS3 streaming, case zdss_loadHeader: the returns of case 1 (errors through RET3; the hint case is given). *)
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3Stmts.
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3R2Lib Zstd.proof.dec.v3.FS.stream.lh.LH3R2Why Zstd.proof.dec.v3.FS.stream.lh.LH3R2Sep Zstd.proof.dec.v3.FS.stream.lh.LH3RetGfh Zstd.proof.dec.v3.FS.stream.lh.LH3R2Small Zstd.proof.dec.v3.FS.stream.lh.LH3R2Short Zstd.proof.dec.v3.FS.stream.lh.LH3R2Dict.
Local Open Scope logic.

(* the allocator premises of rl_base_with for a return context: its dictionary fields are the selection's (or
   getDDict's of them, or the shortcut's), which keep the local DDict or have none; the allocator and its other
   bytes are the entry's (held_redict) *)
Ltac lr_held_tac :=
  cbn [w_k lw_k c3_s c3_dict];
  first [ exact (proj2 (rl_kA_held _ _ _ _))
        | rewrite held_redict_set; exact (proj2 (rl_kA_held _ _ _ _))
        | etransitivity; [ exact (proj2 (rl_lhC_held _ _ _ _)) | exact (proj2 (rl_kA_held _ _ _ _)) ]
        | etransitivity; [ exact (proj2 (rl_lhB_held _ _ _ _)) | exact (proj2 (rl_kA_held _ _ _ _)) ] ].

Ltac lr_mem_tac :=
  match goal with
  | |- sf_mem _ = _ => first [ reflexivity | assumption ]
  | |- redict_ok _ _ =>
      match goal with Hsel: lhA_sel _ _ _ _ _ _ _ |- _ =>
        eapply redict_ok_trans; [ exact (lhA_sel_redict _ _ _ _ _ _ _ Hsel) | ];
        first [ apply redict_ok_refl | apply redict_ok_getddict
              | match goal with Hd: lhB_dict _ _ |- _ => exact (rl_lhB_redict _ _ Hd) end ]
      end
  | |- _ - _ = _ - _ => lr_held_tac
  end.

Section CM_LH3Ret_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* what the context's representation says: the parameters' values, a set has a struct *)
Lemma lr_sep : forall DENT TABS BR a w' r ip,
  (par_ok (c3_par (w_k w')) -> (c3_set (w_k w') <> nil -> c3_sp (w_k w') <> nullval) ->
   0 <= sf_held (c3_s (w_k w')) - local_held (c3_dict (w_k w')) ->
   lh_ret_goal DENT TABS BR a w' r ip) ->
  lh_ret_goal DENT TABS BR a w' r ip.
Proof.
  intros DENT TABS BR a w' r ip H. unfold lh_ret_goal.
  assert (HP: PROPx [] (LOCALx (ds_LI_L a w') (SEPx (ds_S_ip DENT TABS a w' ip))) |--
              !! (par_ok (c3_par (w_k w')) /\ (c3_set (w_k w') <> nil -> c3_sp (w_k w') <> nullval))).
  { unfold ds_S_ip, ctx_rep3, ctx_body3, fgroup3, hset_rep.
    destruct (eq_dec (c3_sp (w_k w')) nullval).
    - go_lowerx. Intros. apply prop_right. split; [ auto | intros Hn; contradiction ].
    - go_lowerx. Intros. apply prop_right. auto. }
  assert (HH: PROPx [] (LOCALx (ds_LI_L a w') (SEPx (ds_S_ip DENT TABS a w' ip))) |--
              !! (0 <= sf_held (c3_s (w_k w')) - local_held (c3_dict (w_k w')))).
  { unfold ds_S_ip. go_lowerx. sep_apply rl_ctx_held. entailer!. }
  eapply derives_trans; [ apply andp_right; [ exact HP | apply andp_right; [ exact HH | apply derives_refl ] ] | ].
  apply derives_extract_prop. intros [Hp Hs]. apply derives_extract_prop. intros Hh. apply H; auto.
Qed.

(* the context's local DDict is not one of the set's (both would own its pad) *)
Lemma lr_sep_local : forall DENT TABS BR a w' r ip,
  ((forall dd, df_local (c3_dict (w_k w')) <> nullval -> cur_ddict (dc_dict (a_st a)) = None ->
      ~ In (df_local (c3_dict (w_k w')), dd) (dc_set (a_st a))) ->
   lh_ret_goal DENT TABS BR a w' r ip) ->
  lh_ret_goal DENT TABS BR a w' r ip.
Proof.
  intros DENT TABS BR a w' r ip H. unfold lh_ret_goal.
  assert (HP: PROPx [] (LOCALx (ds_LI_L a w') (SEPx (ds_S_ip DENT TABS a w' ip))) |--
              !! (forall dd, df_local (c3_dict (w_k w')) <> nullval -> cur_ddict (dc_dict (a_st a)) = None ->
                    ~ In (df_local (c3_dict (w_k w')), dd) (dc_set (a_st a)))).
  { destruct (Classical_Prop.classic (forall dd, df_local (c3_dict (w_k w')) <> nullval ->
                 cur_ddict (dc_dict (a_st a)) = None -> ~ In (df_local (c3_dict (w_k w')), dd) (dc_set (a_st a))))
      as [Hy | Hn].
    { go_lowerx. apply prop_right. exact Hy. }
    apply Classical_Pred_Type.not_all_ex_not in Hn. destruct Hn as [dd Hn].
    apply Classical_Prop.imply_to_and in Hn. destruct Hn as [Hq Hn].
    apply Classical_Prop.imply_to_and in Hn. destruct Hn as [Hc Hn]. apply Classical_Prop.NNPP in Hn.
    unfold ds_S_ip, ctx_rep3, ctx_body3, dgroup. go_lowerx.
    sep_apply (rsep_disj DENT (a_gv a) _ (df_lx (c3_dict (w_k w'))) _ _ dd Hn Hq Hc).
    rewrite FF_sepcon. apply FF_left. }
  eapply derives_trans; [ apply andp_right; [ exact HP | apply derives_refl ] | ].
  apply derives_extract_prop. intros Hp. apply H; auto.
Qed.

Lemma lr_ret_gen : RET3 -> forall DENT TABS BR a w hb w' r ipos',
  TABS_OK TABS -> lh_ctx a w hb -> 0 <= r <= Int64.max_unsigned -> err_why a r ->
  base_call (a_st a) (w_k w') ->
  Zlength (w_oc w') = a_osz a -> sublist 0 (a_opos a) (w_oc w') = sublist 0 (a_opos a) (a_oc a) ->
  (ipos' = a_ipos a \/ ipos' = a_isz a) ->
  lh_ret_goal DENT TABS BR a w' r ipos'.
Proof.
  intros HR DENT TABS BR a w hb w' r ipos' HT Hc Hr Hw Hb Hl Hp Hip.
  pose proof (rl_ahead0 a w hb Hc) as [H0 _].
  destruct Hc as (Ha & Hst & _).
  unfold lh_ret_goal. destruct Hip as [-> | ->].
  - replace (ds_S_ip DENT TABS a w' (a_ipos a)) with (ds_LI_S DENT TABS a w') by reflexivity.
    apply (ret3_err_ok HR); auto.
  - apply (ret3_err_end_ok HR); auto.
Qed.

(* fParams after a parsed header: its dictID is a 32-bit value *)
Lemma lr_fp_val : forall h, 0 <= fh_dictID h <= Int.max_unsigned -> fp_ok (fh_val h).
Proof. intros h H. exists (fh_dictID h). split; [ reflexivity | exact H ]. Qed.

Lemma lr_fp_gfh : forall mg hb h bsm, get_frame_header_m mg hb = FH_ok h -> bytes_ok hb ->
  fp_ok (fh_val h) /\ fp_ok (fh_val (fh_adj h bsm)).
Proof.
  intros mg hb h bsm E Hb. destruct (rl_gfh3 _ _ _ E Hb) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hid & _).
  split; apply lr_fp_val; exact Hid.
Qed.

Lemma lh_ret_ok : lh_ret_stmt.
Proof.
  intros HMF HR Hpr Hdb DENT TABS BR a w hb r ipos' w' HT Hc Hr Hrc Hhint.
  apply lr_sep. intros Hpar' Hsp' Hheld.
  destruct (rl_entry a w hb Hc) as (Hb & Hbh & Hok & Ha).
  assert (Hoc: Zlength (w_oc w) = a_osz a /\ sublist 0 (a_opos a) (w_oc w) = sublist 0 (a_opos a) (a_oc a) /\
               a_opos a <= w_opc w <= a_osz a).
  { destruct Hc as (_ & _ & Hci & _). destruct Hci as (_ & Hop & Hlo & Hpre & _). auto. }
  destruct Hoc as (Hlo & Hpre & Hopc).
  assert (Hop0: 0 <= a_opos a) by (unfold dsa_ok in Ha; tauto).
  pose proof (rl_not_ref a Ha) as Hnr.
  assert (Hbp: c3_par (w_k w) = dc_par (a_st a)) by (destruct Hb as (_ & E & _); exact E).
  assert (Hbs: c3_set (w_k w) = dc_set (a_st a)) by (destruct Hb as (_ & _ & E & _); exact E).
  destruct Hrc as [ r v tbl d1 did1 Hsel Hh Hfp
                  | kk v tbl d1 did1 r v' Hsel Hh Hlt Hpost Herr Hr0 Hfp
                  | kk v tbl d1 did1 r' v' Hsel Hh Hlt Hpost Hne Hfp
                  | h tbl d1 did1 cSize r out fs' d' lxb' Hsel Hh HB Hd Hdict Hfp
                  | h tbl d1 did1 Hsel Hh Hst Ht Hu Hlt
                  | h tbl d1 did1 dd cold fs' r lxb Hsel Hh Ht Hd Hdd Hid0 Hid Hcold Hde Hdc Hfp
                  | h tbl d1 did1 c Hsel Hh Hdd Hcold Hwin
                  | h tbl d1 did1 c s' Hsel Hh HC HD ].
  all: assert (Hp: par_ok (dc_par (a_st a))) by (rewrite <- Hbp; exact Hpar').
  all: assert (Hsp: dc_set (a_st a) <> nil -> c3_sp (w_k w) <> nullval) by (rewrite <- Hbs; exact Hsp').
  - (* the header is invalid *)
    assert (Hd: dec_err r) by (destruct Hsel as (_ & Hfh & _); unfold fh_post_m in Hfh; rewrite Hh in Hfh; exact (proj1 Hfh)).
    apply (lr_ret_gen HR DENT TABS BR a w hb); auto.
    + apply (why_hdr HMF a w hb r Hc Hp Hh Hd).
    + apply (rl_base_with _ (w_k w)); auto; try lr_mem_tac. exact (rl_dict_rel Hpr _ _ _ _ _ _ _ _ Hb Hsel).
  - (* the input ends inside an invalid header *)
    assert (Hd: dec_err r) by (unfold fh_post_m in Hpost; rewrite Herr in Hpost; exact (proj1 Hpost)).
    apply (lr_ret_gen HR DENT TABS BR a w hb); auto.
    + apply (why_more HMF a w hb r Hc Hp Herr Hd).
    + apply (rl_base_with _ (w_k w)); auto; try lr_mem_tac. exact (rl_dict_rel Hpr _ _ _ _ _ _ _ _ Hb Hsel).
  - (* the hint *)
    apply Hhint. exists kk, v, tbl, d1, did1, r', v'.
    split; [ exact Hsel | split; [ exact Hh | split; [ exact Hlt | split; [ exact Hpost | split; [ exact Hne | auto ] ] ] ] ].
  - (* the shortcut failed *)
    assert (HB' := HB). destruct HB' as (_ & _ & _ & _ & _ & _ & _ & Hlout & _).
    apply (lr_ret_gen HR DENT TABS BR a w hb); auto.
    + apply (why_short HMF Hpr a w hb h tbl d1 did1 cSize r out Hc Hp Hsp Hsel Hh HB Hd).
    + apply (rl_base_with _ (w_k w)); auto; try lr_mem_tac.
      destruct Hdict as [-> | (_ & q & Hin & ->)].
      * apply rl_getddict_rel3; auto. exact (rl_dict_rel Hpr _ _ _ _ _ _ _ _ Hb Hsel).
      * right. change (c3_set (k_A (w_k w) (fh_val h) d1 did1)) with (c3_set (w_k w)) in Hin. rewrite Hbs in Hin.
        split.
        -- intro E. rewrite E in Hin. contradiction.
        -- unfold dict_switched, switch_fields. cbn. auto.
    + cbn [w_oc]. rewrite Zlength_app, Zlength_sublist by lia. lia.
    + cbn [w_oc]. rewrite sublist0_app1 by (rewrite Zlength_sublist; lia). rewrite sublist_sublist00 by lia. exact Hpre.
  - (* a stable buffer smaller than the frame *)
    apply (lr_ret_gen HR DENT TABS BR a w hb); auto.
    + apply (why_small HMF a w hb h Hc Hp Hh Hst Ht Hu Hlt).
    + apply (rl_base_with _ (w_k w)); auto; try lr_mem_tac. exact (rl_dict_rel Hpr _ _ _ _ _ _ _ _ Hb Hsel).
      exact (proj1 (lr_fp_gfh _ _ _ 0 Hh Hbh)).
  - (* the frame's Dictionary_ID is not the context's *)
    apply lr_sep_local. intros Hdisj.
    apply (lr_ret_gen HR DENT TABS BR a w hb); auto.
    + apply (why_dict HMF Hpr a w hb h tbl d1 did1 dd r (Hdb a w hb Hc) Hc Hp Hsp
               (rl_hnn a w hb h tbl d1 did1 Hb Hsel Hsp) Hdisj Hsel Hh Ht Hd Hdd Hid0 Hid).
    + apply (rl_base_with _ (w_k w)); auto; try lr_mem_tac. apply rl_getddict_rel3; auto.
      exact (rl_dict_rel Hpr _ _ _ _ _ _ _ _ Hb Hsel).
  - (* the window *)
    apply (lr_ret_gen HR DENT TABS BR a w hb); auto.
    + apply (why_window HMF a w hb h Hc Hp Hh). rewrite <- Hbp. exact Hwin.
    + apply (rl_base_with _ (w_k w)); auto; try lr_mem_tac. apply rl_getddict_rel3; auto.
      exact (rl_dict_rel Hpr _ _ _ _ _ _ _ _ Hb Hsel).
      unfold lhC_k, lhC_fs. cbn [c3_fs w_k lw_k]. destruct (fh_frameType h =? 1);
        exact (proj2 (lr_fp_gfh _ _ _ _ Hh Hbh)).
  - (* memory *)
    assert (Hms: sf_mem s' = sf_mem (c3_s (w_k w)) /\
                 sf_held s' = sf_held (c3_s (lhC_k (k_A (w_k w) (fh_val h) d1 did1) hb h c)))
      by (unfold lhD_memfail in HD; tauto).
    destruct Hms as [Hms1 Hms2].
    apply (lr_ret_gen HR DENT TABS BR a w hb); auto.
    + apply why_mem.
    + apply (rl_base_with _ (w_k w)); auto; try lr_mem_tac. apply rl_getddict_rel3; auto.
      exact (rl_dict_rel Hpr _ _ _ _ _ _ _ _ Hb Hsel).
      exact (proj2 (lr_fp_gfh _ _ _ _ Hh Hbh)).
      change (sf_held s' - local_held (c3_dict (lhC_k (k_A (w_k w) (fh_val h) d1 did1) hb h c)) =
              sf_held (c3_s (w_k w)) - local_held (c3_dict (w_k w))).
      rewrite Hms2. etransitivity; [ exact (proj2 (rl_lhC_held _ _ _ _)) | exact (proj2 (rl_kA_held _ _ _ _)) ].
Qed.

End CM_LH3Ret_1.
