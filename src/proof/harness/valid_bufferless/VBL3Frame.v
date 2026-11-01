(* valid_bufferless: the body of the frame loop (VBLInv.VL_frame_stmt), given the step loop's body. *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.harness.valid_bufferless.VBL3Inv.

Local Notation ZCS := Zstd.proof.zstd.Base.CompSpecs.
Local Notation HCS := Zstd.proof.harness.valid_bufferless.HOK_valid_bufferless.CompSpecs.

Lemma VLF_znth ws k : 0 <= k < Zlength (ws_frames ws) ->
  Znth k (map winfo_val (ws_frames ws) ++ Zrepeat (winfo_val winfo0) (4 - Zlength (ws_frames ws))) =
  winfo_val (VL_f ws k).
Proof.
  intros Hk. rewrite Znth_app1 by (rewrite Zlength_map; lia).
  unfold Znth. rewrite if_false by lia. unfold VL_f.
  rewrite Zlength_correct in Hk.
  rewrite (nth_indep _ _ (winfo_val winfo0)) by (rewrite length_map; lia).
  apply map_nth.
Qed.

Definition VLF_fa (k: Z) (p: val) : val := @field_address HCS t_wseries [ArraySubsc k; StructField _f] p.

Definition VLF_hole (ws: wseries) (k: Z) (p: val) : mpred :=
  @data_at HCS Ews t_winfo (winfo_val (VL_f ws k)) (VLF_fa k p) -* @data_at HCS Ews t_wseries (wseries_val ws) p.

Lemma VLF_f_split (L: list (reptype t_winfo)) k p : 0 <= k < 4 -> Zlength L = 4 ->
  @field_at HCS Ews t_wseries (DOT _f) L p =
  (@data_at HCS Ews t_winfo (Znth k L) (VLF_fa k p) *
   (@array_at HCS Ews t_wseries (DOT _f) 0 k (sublist 0 k L) p *
    @array_at HCS Ews t_wseries (DOT _f) (k + 1) 4 (sublist (k + 1) 4 L) p))%logic.
Proof.
  intros Hk HL.
  erewrite field_at_Tarray; [ | constructor | reflexivity | lia | apply JMeq_refl].
  erewrite (split3_array_at _ _ _ 0 k 4); [ | lia | exact HL | apply JMeq_refl | ..].
  all: try (simpl; auto; fail).
  - rewrite field_at_data_at. unfold VLF_fa. rewrite Z.sub_0_r.
    replace (4 - 0) with 4 by lia. replace (k + 1 - 0) with (k + 1) by lia.
    change (nested_field_type t_wseries [ArraySubsc k; StructField _f]) with t_winfo.
    apply pred_ext; cancel.
  - simpl; unfold in_members; simpl; auto 20.
Qed.

Lemma VLF_take ws k p : 0 <= k < Zlength (ws_frames ws) -> Zlength (ws_frames ws) <= 4 ->
  Zlength (ws_bytes ws) <= 2 ^ 19 ->
  @data_at HCS Ews t_wseries (wseries_val ws) p |--
  @data_at HCS Ews t_winfo (winfo_val (VL_f ws k)) (VLF_fa k p) * VLF_hole ws k p.
Proof.
  intros Hk H4 Hb. unfold VLF_hole.
  assert (HL: Zlength (map winfo_val (ws_frames ws) ++ Zrepeat (winfo_val winfo0) (4 - Zlength (ws_frames ws))) = 4)
    by (rewrite Zlength_app, Zlength_map, Zlength_Zrepeat; lia).
  sep_apply (VLB_ws_unfold ws p Hb). unfold VLB_sr_rest.
  rewrite (VLF_f_split _ k p) by (auto; lia).
  match goal with |- context [@Znth _ ?d k ?l] => replace (@Znth _ d k l) with (winfo_val (VL_f ws k))
    by (rewrite <- (VLF_znth ws k Hk); reflexivity) end.
  rewrite <- !sepcon_assoc.
  match goal with |- ?L |-- _ => match L with context [@data_at ?cs ?sh ?t ?v (VLF_fa k p)] =>
    pull_left (@data_at cs sh t v (VLF_fa k p)) end end.
  rewrite !sepcon_assoc.
  apply sepcon_derives; [apply derives_refl |].
  apply -> wand_sepcon_adjoint.
  eapply derives_trans; [| apply (VLB_ws_fold ws p Hb)]. unfold VLB_sr_rest.
  rewrite (VLF_f_split _ k p) by (auto; lia).
  match goal with |- context [@Znth _ ?d k ?l] => replace (@Znth _ d k l) with (winfo_val (VL_f ws k))
    by (rewrite <- (VLF_znth ws k Hk); reflexivity) end.
  cancel.
Qed.

Lemma VLF_dr_model mode db dd dm q d : 0 <= mode < 3 -> VL_dfacts mode db dm -> VL_ddok db dd ->
  dictref_model (VL_dr mode q d db dd) = Some dm.
Proof.
  intros Hm Hd Hdd. unfold VL_dr.
  destruct Hd as [(-> & -> & ->) | (Hm0 & _ & _ & Hda)]; [reflexivity |].
  rewrite (proj2 (Z.eqb_neq mode 0) Hm0).
  destruct (mode =? 1); simpl; [exact Hda | rewrite (proj1 Hdd); exact Hda].
Qed.

Lemma VLF_begin mode db dd dm q d obl ob osz opos oc : 0 <= mode < 3 -> VL_dfacts mode db dm -> VL_ddok db dd ->
  ba_st (bl_begin (set_bl dctx_init obl) (VL_dr mode q d db dd)) = Some (bl_init md_dflt dm) /\
  ba_expect (bl_begin (set_bl dctx_init obl) (VL_dr mode q d db dd)) = bs_expect (bl_init md_dflt dm) /\
  ba_dict (bl_begin (set_bl dctx_init obl) (VL_dr mode q d db dd)) = VL_dr mode q d db dd /\
  bl_hist_ok (bl_begin (set_bl dctx_init obl) (VL_dr mode q d db dd)) ob osz opos oc.
Proof.
  intros Hm Hd Hdd. unfold bl_begin, bl_hist_ok. cbn [ba_st ba_expect ba_dict ba_out].
  rewrite (VLF_dr_model mode db dd dm q d Hm Hd Hdd).
  change (dmode_of (dc_par (set_bl dctx_init obl))) with (dmode_of dparams_dflt).
  replace (dmode_of dparams_dflt) with md_dflt by reflexivity. auto.
Qed.

Lemma VLF_next dm ws k : series_facts dm ws -> wseries_wf ws -> 0 <= k -> k + 1 < Zlength (ws_frames ws) ->
  wi_start (VL_f ws (k + 1)) = wi_start (VL_f ws k) + wi_size (VL_f ws k) /\
  wi_cstart (VL_f ws (k + 1)) = wi_cstart (VL_f ws k) + wi_csize (VL_f ws k).
Proof.
  intros Hs Hw Hk Hk1. unfold VL_f.
  replace (Z.to_nat (k + 1)) with (S (Z.to_nat k)) by lia.
  apply (vbl_tiles_next dm ws (Z.to_nat k) Hs Hw). rewrite Zlength_correct in Hk1. lia.
Qed.

Ltac VLF_simp := unfold winfo_val at 1; cbv beta iota.

Lemma VLF_vp_drop (P: mpred) q : (P && valid_pointer q) |-- P.
Proof. apply andp_left1, derives_refl. Qed.


Lemma VL_frame_ok : VL_inner_stmt -> VL_frame_stmt.
Proof.
  intros Hin. unfold VL_frame_stmt.
  intros Espec DC DD WG WDS gv ws db dd dm mode src buf dctx q k ipos pos obl oc ex R Hh Hk Hq Hdd Hip Hp Hoc.
  destruct R as [Rn Rb Rc Rr]. unfold VL_frame_s, VL_sep, VL_loc, VL_sr. abbreviate_semax.
  forward.
  assert_PROP (field_compatible t_wseries [] (gv _x_valid_bufferless__sr)) as Hfc by entailer!.
  pose proof Hh as Hh0.
  destruct Hh as (Hm & Hs & Hw & Hd & Hsrc & Hbuf & Hdc & Hfs & Hfb).
  pose proof Hs as (Hbok & Hcok & Hnb & Hnc & Hnf & _).
  assert (Hk4: 0 <= k < 4) by (rewrite Zlength_correct in Hk; lia).
  match goal with |- context [temp _f ?v] =>
    replace v with (field_address t_wseries [ArraySubsc k; StructField _f] (gv _x_valid_bufferless__sr)) end.
  2:{ unfold field_address. rewrite if_true.
      - destruct (gv _x_valid_bufferless__sr); try (destruct Hfc; contradiction). simpl.
        rewrite Ptrofs.add_assoc. f_equal. f_equal. unfold Ptrofs.of_intu, Ptrofs.of_int.
        rewrite Int.unsigned_repr by rep_lia. rewrite ptrofs_mul_repr, ptrofs_add_repr. reflexivity.
      - auto with field_compatible. }
  sep_apply (VLF_take ws k (gv _x_valid_bufferless__sr) Hk ltac:(rewrite Zlength_correct; lia) Hnb).
  Intros. unfold VLF_fa.
  match goal with |- context [@data_at _ _ t_winfo _ ?a] => remember a as fp eqn:Hfp end.
  assert_PROP (field_compatible (Tstruct ___gp_winfo_t noattr) [] fp) as Hfcw by entailer!.
  assert (Ho8: offset_val 8 fp = field_address (Tstruct ___gp_winfo_t noattr) [StructField _start] fp)
    by (unfold field_address; rewrite if_true by auto with field_compatible; reflexivity).
  assert (Ho16: offset_val 16 fp = field_address (Tstruct ___gp_winfo_t noattr) [StructField _size] fp)
    by (unfold field_address; rewrite if_true by auto with field_compatible; reflexivity).
  assert (Ho24: offset_val 24 fp = field_address (Tstruct ___gp_winfo_t noattr) [StructField _cstart] fp)
    by (unfold field_address; rewrite if_true by auto with field_compatible; reflexivity).
  assert (Ho32: offset_val 32 fp = field_address (Tstruct ___gp_winfo_t noattr) [StructField _csize] fp)
    by (unfold field_address; rewrite if_true by auto with field_compatible; reflexivity).
  forward. VLF_simp. forward. VLF_simp. forward.
  forward. VLF_simp. forward. VLF_simp. forward.
  match goal with |- semax _ (PROPx _ (LOCALx ?L (SEPx ?S))) _ _ =>
    match S with context C [DC gv dctx (set_ex (set_bl dctx_init obl) ex)] =>
      let S' := context C [DC gv dctx (set_ex (set_bl dctx_init (Some (bl_begin (set_bl dctx_init obl)
                  (VL_dr mode q (offset_val (Zlength (ws_content ws) + 1) buf) db dd)))) false)] in
      forward_if (PROPx [] (LOCALx (temp _x_valid_bufferless__t'9 (Vlong (Int64.repr 0)) :: L) (SEPx S')))
    end end.
  - forward_call (gv, dctx, set_ex (set_bl dctx_init obl) ex).
    forward.
    entailer!. apply derives_refl.
  - assert (Hdn: mode <> 0 /\ bytes_ok db /\ 8 <= Zlength db <= 2 ^ 12 + 2048 /\ dict_auto db = Some dm)
      by (destruct Hd as [(? & _) | ?]; [lia | auto]).
    destruct Hdn as (Hm0 & Hdok & Hdl & Hda).
    destruct Hbuf as (bb & ob & ->).
    forward_if.
    + forward_call (VLB_W src (Zlength (ws_bytes ws)) (Vptr bb ob) (Zlength (ws_content ws)), gv, dctx,
                    set_ex (set_bl dctx_init obl) ex, Ews, offset_val (Zlength (ws_content ws) + 1) (Vptr bb ob), db).
      { apply VLB_buf_ok_dict; [exact I | apply Zlength_nonneg | apply Zlength_nonneg]. }
      all: try (split; [lia | auto]).
      Intros vret. destruct vret as [r st']. cbn [fst snd] in *.
      match goal with Hx: (r = 0 /\ _) \/ _ |- _ => destruct Hx as [(-> & ->) | (_ & Hx & _)] end.
      2: congruence.
      forward.
      rewrite (proj2 (Z.eqb_neq (Zlength db) 0)) by lia.
      entailer!. apply derives_refl.
    + assert (Hm2: mode = 2) by lia. subst mode.
      destruct Hq as (Hq2 & _). specialize (Hq2 eq_refl).
      unfold VL_qres. rewrite if_false by (destruct q; try contradiction; discriminate).
      sep_apply (VLF_vp_drop (DD gv q dd) q).
      forward_call (gv, dctx, set_ex (set_bl dctx_init obl) ex, q, Some dd).
      forward.
      unfold VL_qres. rewrite if_false by (destruct q; try contradiction; discriminate).
      entailer!. apply derives_refl.
  - forward.
    forward_call 0.
    forward_if.
    { exfalso. vm_compute in H. congruence. }
    forward.
    subst ipos pos.
    forward_if (temp _x_valid_bufferless__t'14 (Vint (Int.repr 1))).
    { forward. forward. entailer!. unfold Int64.cmpu. rewrite Int64.eq_true. reflexivity. }
    { exfalso. congruence. }
    forward_call (Int.repr 1).
    subst fp. unfold VLF_hole, VLF_fa.
    sep_apply (modus_ponens_wand
      (@data_at HCS Ews t_winfo (winfo_val (VL_f ws k)) (field_address t_wseries [ArraySubsc k; StructField _f] (gv _x_valid_bufferless__sr)))
      (@data_at HCS Ews t_wseries (wseries_val ws) (gv _x_valid_bufferless__sr))).
    eapply semax_pre with (P' := VL_inner DC DD gv ws db dd dm mode src buf dctx q k).
    { destruct (VLF_begin mode db dd dm q (offset_val (Zlength (ws_content ws) + 1) buf) obl buf (Zlength (ws_content ws))
                  (wi_cstart (VL_f ws k) + Zlength (bs_out (bl_init md_dflt dm))) oc Hm Hd Hdd) as (B1 & B2 & B3 & B4).
      unfold VL_inner, VL_sep, VL_loc, VL_sr.
      Exists 0 (bl_init md_dflt dm) (bl_begin (set_bl dctx_init obl) (VL_dr mode q (offset_val (Zlength (ws_content ws) + 1) buf) db dd)) oc.
      entailer!.
      apply vbl_init. }
    match goal with |- semax _ _ _ ?RR =>
      apply semax_loop with (Q' := VL_inner DC DD gv ws db dd dm mode src buf dctx q k);
      [ apply -> semax_skip_seq;
        eapply semax_post; [ | | | | exact (Hin Espec DC DD WG WDS gv ws db dd dm mode src buf dctx q k RR Hh0 Hk Hq Hdd)]
      | eapply semax_post; [ | | | | apply semax_skip] ] end.
    all: unfold abbreviate in POSTCONDITION; subst POSTCONDITION;
      lazymatch goal with |- forall _ : option val, _ => intros vl | _ => idtac end;
      simpl RA_normal; simpl RA_break; simpl RA_continue; simpl RA_return;
      try solve [apply andp_left2; first [apply derives_refl | intros ?; simpl; normalize]].
    unfold VL_inner_exit, VL_cont.
    Intros stp ip ps ob oc' ex'. Exists k stp ip ps ob oc' ex'.
    unfold VL_sep, VL_loc.
    entailer!.
    all: try intros H0'; split; [auto | intros Hk1].
    all: destruct H2 as [-> ->]; [first [assumption | reflexivity] |].
    destruct (VLF_next dm ws k Hs Hw (proj1 Hk) Hk1) as [-> ->]. auto.
Qed.
