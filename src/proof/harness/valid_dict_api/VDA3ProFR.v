(* valid_dict_api main, prologue segment: frames/mode 4 gp_assumes, dn, cap (s12..s15): VDA_P4 -> VDA_P5 (VDA3ProDefs.v). *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.harness.valid_dict_api.WTopSpecs_valid_dict_api.
Require Import Zstd.proof.harness.valid_dict_api.VDA3Defs.
Require Import Zstd.proof.harness.valid_dict_api.VDA3ProDefs.

Local Notation HCS := Zstd.proof.harness.valid_dict_api.HOK_valid_dict_api.CompSpecs.

(* sr by fields: the ones s12..s15 read (content_n, f, nframes) and the rest *)
Definition vfr_sr_rest (ws: wseries) (p: val) : mpred :=
  (@field_at HCS Ews t_wseries (DOT _bytes) (zbytes (ws_bytes ws) ++ Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength (ws_bytes ws))) p *
   @field_at HCS Ews t_wseries (DOT _n) (vl (Zlength (ws_bytes ws))) p *
   @field_at HCS Ews t_wseries (DOT _content)
     (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws))) p *
   spacer Ews 786932 786936 p)%logic.

Lemma vfr_ws_unfold ws p :
  @data_at HCS Ews t_wseries (wseries_val ws) p |--
  (vfr_sr_rest ws p *
   @field_at HCS Ews t_wseries (DOT _content_n) (vl (Zlength (ws_content ws))) p *
   @field_at HCS Ews t_wseries (DOT _f)
     (map winfo_val (ws_frames ws) ++ Zrepeat (winfo_val winfo0) (4 - Zlength (ws_frames ws))) p *
   @field_at HCS Ews t_wseries (DOT _nframes) (vu (Zlength (ws_frames ws))) p)%logic.
Proof. unfold vfr_sr_rest. unfold_data_at (data_at _ _ _ p). cbn [fst snd wseries_val]. cancel. Qed.

Lemma vfr_ws_fold ws p :
  (vfr_sr_rest ws p *
   @field_at HCS Ews t_wseries (DOT _content_n) (vl (Zlength (ws_content ws))) p *
   @field_at HCS Ews t_wseries (DOT _f)
     (map winfo_val (ws_frames ws) ++ Zrepeat (winfo_val winfo0) (4 - Zlength (ws_frames ws))) p *
   @field_at HCS Ews t_wseries (DOT _nframes) (vu (Zlength (ws_frames ws))) p)%logic |--
  @data_at HCS Ews t_wseries (wseries_val ws) p.
Proof. unfold vfr_sr_rest. unfold_data_at (data_at _ _ _ p). cbn [fst snd wseries_val]. cancel. Qed.

(* wd by fields: id and n (read by s12..s15) and the rest *)
Definition vfr_wd_rest (wd: wdict) (p: val) (stv: reptype t_wstate) : mpred :=
  (@field_at HCS Ews t_wdict (DOT _bytes) (zbytes (wd_bytes wd) ++ Zrepeat (Vint Int.zero) (6144 - Zlength (wd_bytes wd))) p *
   @field_at HCS Ews t_wdict (DOT _formatted) (vb (wd_formatted wd)) p *
   @field_at HCS Ews t_wdict (DOT _content) (offset_val (Zlength (wd_bytes wd) - Zlength (wd_content wd)) p) p *
   @field_at HCS Ews t_wdict (DOT _content_n) (vl (Zlength (wd_content wd))) p *
   @field_at HCS Ews t_wdict (DOT _x_valid_dict_api__st) stv p *
   spacer Ews 13980 13984 p)%logic.

Lemma vfr_wd_unfold wd p stv :
  @data_at HCS Ews t_wdict (wdict_val wd p stv) p |--
  (vfr_wd_rest wd p stv * @field_at HCS Ews t_wdict (DOT _id) (vu (wd_id wd)) p *
   @field_at HCS Ews t_wdict (DOT _n) (vl (Zlength (wd_bytes wd))) p)%logic.
Proof. unfold vfr_wd_rest. unfold_data_at (data_at _ _ _ p). cbn [fst snd wdict_val]. cancel. Qed.

Lemma vfr_wd_fold wd p stv :
  (vfr_wd_rest wd p stv * @field_at HCS Ews t_wdict (DOT _id) (vu (wd_id wd)) p *
   @field_at HCS Ews t_wdict (DOT _n) (vl (Zlength (wd_bytes wd))) p)%logic |--
  @data_at HCS Ews t_wdict (wdict_val wd p stv) p.
Proof. unfold vfr_wd_rest. unfold_data_at (data_at _ _ _ p). cbn [fst snd wdict_val]. cancel. Qed.

Lemma vfr_wd_rep WDS wd p stv : WDS wd stv ->
  (vfr_wd_rest wd p stv * @field_at HCS Ews t_wdict (DOT _id) (vu (wd_id wd)) p *
   @field_at HCS Ews t_wdict (DOT _n) (vl (Zlength (wd_bytes wd))) p)%logic |-- wdict_rep WDS Ews wd p.
Proof. intros. unfold wdict_rep. Exists stv. sep_apply (vfr_wd_fold wd p stv). entailer!. Qed.

#[local] Instance vfr_winfo_inh : Inhabitant winfo := winfo0.

(* mode 0's gp_assume on a frame *)
Definition vfr_ok (wd: wdict) (f: winfo) : Prop := wi_skippable f = true \/ (wi_did_size f <> 0 /\ wi_did f = wd_id wd).
Definition vfr_okb (wd: wdict) (f: winfo) : bool :=
  orb (wi_skippable f) (andb (negb (wi_did_size f =? 0)) (wi_did f =? wd_id wd)).
Lemma vfr_okb_ok wd f : vfr_okb wd f = true -> vfr_ok wd f.
Proof.
  unfold vfr_okb, vfr_ok. destruct (wi_skippable f); [auto|]. simpl.
  intros E. apply andb_prop in E as [E1 E2]. apply negb_true_iff, Z.eqb_neq in E1. apply Z.eqb_eq in E2. auto.
Qed.

Lemma vda_fr_ok : VDA_fr_ok.
Proof.
  unfold VDA_fr_ok; intros. unfold VDA_P4, VDA_s12_15, VDA_Delta. abbreviate_semax.
  Intros. unfold wdict_rep at 1. Intros stv.
  sep_apply (vfr_wd_unfold wd (vda_wd_addr gv which) stv).
  sep_apply (vfr_ws_unfold ws (gv _x_valid_dict_api__sr)).
  Intros.
  freeze FR := (vfr_sr_rest _ _) (vfr_wd_rest _ _ _) (mem_mgr _) (zstd_globals _) (wand _ _) (data_at _ t_ddp _ _) TT.
  pose proof H3 as (_ & (Hbok & Hcok & Hnb & Hnc & Hnf & _) & Hwf & _).
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
    forward_if (PROPx ((mode = 0 -> Forall (fun f => wi_skippable f = true \/ (wi_did_size f <> 0 /\ wi_did f = wd_id wd))
                                     (ws_frames ws)) :: P) (LOCALx L (SEPx R))) end.
  { match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
      forward;
      forward_loop (EX k: Z, PROPx ((0 <= k <= Zlength (ws_frames ws)) :: Forall (vfr_ok wd) (sublist 0 k (ws_frames ws)) :: P)
                               (LOCALx (temp _k (vu k) :: L) (SEPx R)))
        continue: (EX k: Z, PROPx ((0 <= k < Zlength (ws_frames ws)) :: Forall (vfr_ok wd) (sublist 0 (k + 1) (ws_frames ws)) :: P)
                               (LOCALx (temp _k (vu k) :: L) (SEPx R)))
        break: (PROPx (Forall (vfr_ok wd) (ws_frames ws) :: P) (LOCALx L (SEPx R)))
    end.
    { Exists 0. entailer!. }
    { Intros k.
      assert (Hnf': 1 <= Zlength (ws_frames ws) <= 4) by (rewrite Zlength_correct; lia).
      forward.
      match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
        forward_if (PROPx ((k < Zlength (ws_frames ws)) :: P) (LOCALx L (SEPx R))) end.
      - forward. entailer!.
      - assert (Hk: k = Zlength (ws_frames ws)) by lia.
        rewrite Hk, sublist_same in H7 by lia.
        forward. entailer!.
      - Intros.
        assert (Fk: forall d, @Znth (reptype t_winfo) d k
                  (map winfo_val (ws_frames ws) ++ Zrepeat (winfo_val winfo0) (4 - Zlength (ws_frames ws))) =
                  winfo_val (Znth k (ws_frames ws))).
        { intros. rewrite app_Znth1 by (rewrite Zlength_map; lia). rewrite Znth_map by lia. reflexivity. }
        assert (Hfwf: winfo_wf (Znth k (ws_frames ws))).
        { destruct Hwf as [Hw _]. apply Forall_Znth; auto; lia. }
        assert (Hwdwf: wdict_wf wd).
        { destruct H1 as (_ & _ & Hw & _). destruct H2 as (_ & _ & Hn & _).
          eapply Forall_forall; [exact Hw|]. eapply nth_error_In; exact Hn. }
        destruct Hfwf as (_ & _ & _ & _ & _ & _ & Hds & Hdid & _).
        destruct Hwdwf as (Hid & _).
        unfold u32 in *.
        forward.
        { entailer!. rewrite Fk. unfold winfo_val, vb. destruct (wi_skippable _); exact I. }
        rewrite Fk. unfold winfo_val at 1. cbv beta iota zeta.
        remember (Znth k (ws_frames ws)) as f eqn:Ef.
        match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
          forward_if (PROPx P (LOCALx (temp _x_valid_dict_api__t'7 (vb (vfr_okb wd f)) :: L) (SEPx R))) end.
        + clear Ef. forward. entailer!.
          destruct (wi_skippable f) eqn:Es; [unfold vfr_okb; rewrite Es; reflexivity | contradiction].
        + clear Ef. assert (Es: wi_skippable f = false).
          { destruct (wi_skippable f); [discriminate | reflexivity]. }
          forward.
          { entailer!. rewrite Fk. exact I. }
          rewrite Fk. unfold winfo_val at 1. cbv beta iota zeta.
          match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
            forward_if (PROPx P (LOCALx (temp _x_valid_dict_api__t'7 (vb (vfr_okb wd f)) :: L) (SEPx R))) end.
          * forward.
            { entailer!. rewrite Fk. exact I. }
            rewrite Fk. unfold winfo_val at 1. cbv beta iota zeta.
            forward. forward. forward.
            entailer!.
            unfold vfr_okb. rewrite Es. simpl orb.
            assert (Hd0: wi_did_size f <> 0) by (intros E; rewrite E in *; contradiction).
            destruct (Z.eqb_spec (wi_did_size f) 0); [contradiction|]. simpl negb. simpl andb.
            unfold vb. destruct (Z.eqb_spec (wi_did f) (wd_id wd)); destruct (zeq (wi_did f) (wd_id wd));
              try reflexivity; contradiction.
          * forward. entailer!.
            unfold vfr_okb. rewrite Es. simpl orb.
            assert (Hd0: wi_did_size f = 0).
            { first [assumption |
                match goal with X: Int.repr (wi_did_size f) = Int.zero |- _ =>
                  apply repr_inj_unsigned in X; [exact X | rep_lia | rep_lia] end]. }
            rewrite Hd0. reflexivity.
          * entailer!.
        + forward_call (Int.repr (if vfr_okb wd f then 1 else 0)).
          Intros. Exists k. entailer!.
          rewrite (sublist_split 0 k (k + 1)) by lia. rewrite sublist_len_1 by lia.
          apply Forall_app; split; [exact H7|]. constructor; [|constructor].
          apply vfr_okb_ok. match goal with X: Int.repr (if vfr_okb ?w ?g then 1 else 0) <> Int.zero |- _ => destruct (vfr_okb w g); [reflexivity | contradiction] end. }
    { Intros k. forward. Exists (k + 1). entailer!. }
    { unfold POSTCONDITION, abbreviate. simpl_ret_assert. entailer!. } }
  { forward. entailer!. }
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
    forward_if (PROPx ((mode = 4 -> Zlength (ws_frames ws) = 1 /\ wi_skippable (hd winfo0 (ws_frames ws)) = false) :: P)
                  (LOCALx L (SEPx R))) end.
  { forward.
    forward_if (temp _x_valid_dict_api__t'8 (vb (andb (Zlength (ws_frames ws) =? 1) (negb (wi_skippable (hd winfo0 (ws_frames ws))))))).
    - assert (Hl: Zlength (ws_frames ws) = 1).
      { match goal with Hx: Int.repr (Zlength (ws_frames ws)) = Int.repr 1 |- _ =>
          rewrite Zlength_correct in *; apply repr_inj_unsigned in Hx; rep_lia end. }
      forward.
      { entailer!. destruct (ws_frames ws) as [|f0 fs]; [rewrite Zlength_nil in Hl; lia |].
        cbn [map app]. rewrite Znth_0_cons. unfold winfo_val. destruct (wi_skippable f0); exact I. }
      forward.
      entailer!. destruct (ws_frames ws) as [|f0 fs]; [rewrite Zlength_nil in Hl; lia |].
      cbn [map app hd]. rewrite Znth_0_cons. unfold winfo_val, vb. rewrite Hl. destruct (wi_skippable f0); reflexivity.
    - forward. entailer!.
      destruct (Zlength (ws_frames ws) =? 1) eqn:E; [|reflexivity].
      apply Z.eqb_eq in E. rewrite E in *. contradiction.
    - forward_call (Int.repr (if andb (Zlength (ws_frames ws) =? 1) (negb (wi_skippable (hd winfo0 (ws_frames ws)))) then 1 else 0)).
      Intros. entailer!.
      destruct (andb (Zlength (ws_frames ws) =? 1) (negb (wi_skippable (hd winfo0 (ws_frames ws))))) eqn:E; [|contradiction].
      apply andb_prop in E as [E1 E2]. apply Z.eqb_eq in E1. apply negb_true_iff in E2. auto. }
  { forward. entailer!. }
  forward.
  forward_if (temp _x_valid_dict_api__t'10 (vu (if orb (mode =? 5) (mode =? 6) then 0 else 1))).
  { forward. entailer!.
    destruct (Z.eqb_spec mode 5); destruct (Z.eqb_spec mode 6); destruct (zeq mode 6); subst; try lia; reflexivity. }
  { forward. entailer!. }
  forward_if.
  { forward.
    forward_call (0, Zlength (ws_content ws) + 16).
    Intros c. forward. Exists c. unfold VDA_P5. thaw FR.
    sep_apply (vfr_wd_rep WDS wd (vda_wd_addr gv which) stv H4).
    sep_apply (vfr_ws_fold ws (gv _x_valid_dict_api__sr)).
    go_lower. apply andp_right; [apply prop_right | cancel].
    pose proof (Zlength_nonneg (ws_content ws)).
    assert (Hm: mode <> 5 /\ mode <> 6).
    { destruct (Z.eqb_spec mode 5); destruct (Z.eqb_spec mode 6); simpl in *; try contradiction; lia. }
    refine (conj H (conj H0 (conj H1 (conj H2 (conj H3 (conj _ _)))))).
    { unfold vda_cap_facts. split; [exact H6 | split; [exact H5 | split; [intros; lia | lia]]]. }
    rewrite eqb_type_refl. repeat split; auto. }
  { forward. Exists 0. unfold VDA_P5. thaw FR.
    sep_apply (vfr_wd_rep WDS wd (vda_wd_addr gv which) stv H4).
    sep_apply (vfr_ws_fold ws (gv _x_valid_dict_api__sr)).
    go_lower. apply andp_right; [apply prop_right | cancel].
    pose proof (Zlength_nonneg (ws_content ws)).
    refine (conj H (conj H0 (conj H1 (conj H2 (conj H3 (conj _ _)))))).
    { unfold vda_cap_facts. split; [exact H6 | split; [exact H5 | split; [intros; lia | lia]]]. }
    rewrite eqb_type_refl. repeat split; auto. }
Qed.
