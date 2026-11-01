(* valid_dict_api main, prologue segment: w_dict loop (s7): VDA_P1 -> VDA_P2 (VDA3ProDefs.v). *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.harness.valid_dict_api.WTopSpecs_valid_dict_api.
Require Import Zstd.proof.harness.valid_dict_api.VDA3Defs.
Require Import Zstd.proof.harness.valid_dict_api.VDA3ProDefs.

Local Notation HCS := Zstd.proof.harness.valid_dict_api.HOK_valid_dict_api.CompSpecs.

(* the head of a constant array *)
Lemma vda_arr_take1 {cs: compspecs} sh (t: type) (v: reptype t) n p :
  0 < n ->
  @data_at cs sh (tarray t n) (Zrepeat v n) p |--
  @data_at cs sh t v p * @data_at cs sh (tarray t (n - 1)) (Zrepeat v (n - 1)) (offset_val (@sizeof cs t) p).
Proof.
  intros Hn.
  assert_PROP (field_compatible (tarray t n) [] p) as FC by entailer!.
  replace (Zrepeat v n) with ([v] ++ Zrepeat v (n - 1)).
  2: { unfold Zrepeat. replace (Z.to_nat n) with (S (Z.to_nat (n - 1))) by lia. reflexivity. }
  rewrite (split2_data_at_Tarray_app 1 n sh t [v] (Zrepeat v (n - 1)) p) by (rewrite ?Zlength_Zrepeat; auto; lia).
  rewrite (data_at_singleton_array_eq sh t v [v] p) by reflexivity.
  rewrite field_address0_offset.
  2: { auto with field_compatible. }
  simpl nested_field_offset. replace (0 + @sizeof cs t * 1) with (@sizeof cs t) by lia. cancel.
Qed.

Lemma vda_wand_take (P A R W: mpred) : (P |-- A * R) -> (R * A |-- W) -> P |-- A * (A -* W).
Proof.
  intros H1 H2. eapply derives_trans; [apply H1|]. apply sepcon_derives; [apply derives_refl|].
  apply wand_sepcon_adjoint; auto.
Qed.

Lemma vda_pull3 (B N F X: mpred) : (B * (N * (F * X)) = F * (B * (N * X)))%logic.
Proof. apply pred_ext; cancel. Qed.

Lemma vda_pull4 (B N F I X: mpred) : (B * (N * (F * (I * X))) = I * (B * (N * (F * X))))%logic.
Proof. apply pred_ext; cancel. Qed.

Lemma vda_wand_frame_r (F W X: mpred) : (F -* W) * X |-- F -* (W * X).
Proof.
  rewrite <- wand_sepcon_adjoint. rewrite sepcon_assoc, (sepcon_comm X F), <- sepcon_assoc.
  apply sepcon_derives; [rewrite sepcon_comm; apply wand_frame_elim | apply derives_refl].
Qed.

Lemma vda_wand_frame_l (F W X: mpred) : X * (F -* W) |-- F -* (X * W).
Proof.
  rewrite <- wand_sepcon_adjoint. rewrite sepcon_assoc.
  apply sepcon_derives; [apply derives_refl | rewrite sepcon_comm; apply wand_frame_elim].
Qed.

Local Instance vda_wd_inh : Inhabitant wdict := {| wd_bytes := []; wd_formatted := false; wd_id := 0; wd_content := [] |}.

Lemma vda_addr_eq (gv: globals) (i: Z) :
  0 <= i <= 3 -> isptr (gv _vd_wd) ->
  force_val (sem_add_ptr_int (Tstruct ___gp_wdict_t noattr) Unsigned (gv _vd_wd) (vu i)) = vda_wd_addr gv i.
Proof.
  intros Hi P. unfold vda_wd_addr, vu. destruct (gv _vd_wd); try contradiction.
  unfold sem_add_ptr_int. simpl. f_equal. f_equal.
  unfold Ptrofs.of_intu, Ptrofs.of_int. rewrite Int.unsigned_repr by rep_lia.
  rewrite ptrofs_mul_repr. f_equal. lia.
Qed.

Lemma vda_nodup_snoc (l: list Z) (x: Z) : NoDup l -> ~ In x l -> NoDup (l ++ [x]).
Proof.
  intros Hn Hx. apply (Permutation_NoDup (l := x :: l)).
  - apply Permutation_cons_append.
  - constructor; auto.
Qed.

Lemma vda_facts_snoc mode i wds wi :
  vda_wds_facts mode i wds -> dict_facts wi -> wdict_wf wi -> (wd_formatted wi = true -> wd_id wi <> 0) ->
  (mode = 0 -> wd_formatted wi = true /\ Forall (fun w => wd_id w <> wd_id wi) wds) ->
  vda_wds_facts mode (i + 1) (wds ++ [wi]).
Proof.
  intros (Hl & Hdf & Hwf & Hm & Hid) Hd Hw Hidi H0.
  split; [rewrite Zlength_app, Zlength_cons, Zlength_nil; lia|].
  split; [apply Forall_app; split; auto|].
  split; [apply Forall_app; split; auto|].
  split; [|apply Forall_app; split; auto].
  intros Hmode. destruct (Hm Hmode) as [Hf Hn]. destruct (H0 Hmode) as [Hfi Hdi].
  split; [apply Forall_app; split; auto|].
  rewrite map_app. apply vda_nodup_snoc; auto.
  intros Hin. apply in_map_iff in Hin. destruct Hin as (w & Ew & Hw').
  rewrite Forall_forall in Hdi. apply (Hdi w Hw'). auto.
Qed.

Section WD.
Variable WG : globals -> mpred.
Variable WDS : wdict -> reptype t_wstate -> Prop.

Lemma vda_rest_take (gv: globals) (i: Z) :
  0 <= i < 3 ->
  vda_rest gv i |-- @data_at HCS Ews t_wdict (@zero_val HCS t_wdict) (vda_wd_addr gv i) * vda_rest gv (i + 1).
Proof.
  intros Hi. unfold vda_rest.
  sep_apply (vda_arr_take1 Ews t_wdict (@zero_val HCS t_wdict) (3 - i) (vda_wd_addr gv i) ltac:(lia)).
  replace (3 - i - 1) with (3 - (i + 1)) by lia.
  unfold vda_wd_addr. rewrite offset_offset_val. replace (i * @sizeof HCS t_wdict + @sizeof HCS t_wdict) with ((i + 1) * @sizeof HCS t_wdict) by lia.
  cancel.
Qed.

(* borrow one scalar field of a dictionary *)
Lemma vda_wd_take_fmt sh wd p :
  wdict_rep WDS sh wd p |--
  @field_at HCS sh t_wdict (DOT _formatted) (vb (wd_formatted wd)) p *
  (@field_at HCS sh t_wdict (DOT _formatted) (vb (wd_formatted wd)) p -* wdict_rep WDS sh wd p).
Proof.
  unfold wdict_rep. Intros stv.
  eapply vda_wand_take.
  - unfold_data_at (data_at _ _ _ p). cbn [fst snd wdict_val].
    rewrite vda_pull3. apply derives_refl.
  - Exists stv. entailer!. unfold_data_at (data_at _ _ _ p). cbn [fst snd wdict_val]. cancel.
Qed.

Lemma vda_wd_take_id sh wd p :
  wdict_rep WDS sh wd p |--
  @field_at HCS sh t_wdict (DOT _id) (vu (wd_id wd)) p *
  (@field_at HCS sh t_wdict (DOT _id) (vu (wd_id wd)) p -* wdict_rep WDS sh wd p).
Proof.
  unfold wdict_rep. Intros stv.
  eapply vda_wand_take.
  - unfold_data_at (data_at _ _ _ p). cbn [fst snd wdict_val].
    rewrite vda_pull4. apply derives_refl.
  - Exists stv. entailer!. unfold_data_at (data_at _ _ _ p). cbn [fst snd wdict_val]. cancel.
Qed.

(* borrow the id of element k of vd_wd[j..) *)
Lemma vda_wds_take_id gv : forall wds j k, 0 <= k < Zlength wds ->
  vda_wds_from WDS gv j wds |--
  @field_at HCS Ews t_wdict (DOT _id) (vu (wd_id (Znth k wds))) (vda_wd_addr gv (j + k)) *
  (@field_at HCS Ews t_wdict (DOT _id) (vu (wd_id (Znth k wds))) (vda_wd_addr gv (j + k)) -* vda_wds_from WDS gv j wds).
Proof.
  induction wds as [|w wds IH]; intros j k Hk.
  - rewrite Zlength_nil in Hk; lia.
  - rewrite Zlength_cons in Hk. simpl vda_wds_from.
    destruct (Z.eq_dec k 0) as [->|Hk0].
    + rewrite Znth_0_cons, Z.add_0_r.
      eapply derives_trans; [apply sepcon_derives; [apply (vda_wd_take_id Ews w (vda_wd_addr gv j)) | apply derives_refl]|].
      rewrite sepcon_assoc. apply sepcon_derives; [apply derives_refl | apply vda_wand_frame_r].
    + rewrite Znth_pos_cons by lia. replace (j + k) with ((j + 1) + (k - 1)) by lia.
      eapply derives_trans; [apply sepcon_derives; [apply derives_refl | apply (IH (j + 1) (k - 1) ltac:(lia))]|].
      rewrite <- sepcon_assoc, (sepcon_comm (wdict_rep _ _ _ _)), sepcon_assoc.
      apply sepcon_derives; [apply derives_refl | apply vda_wand_frame_l].
Qed.

Lemma vda_wds_from_app gv : forall wds j w,
  vda_wds_from WDS gv j (wds ++ [w]) = (vda_wds_from WDS gv j wds * wdict_rep WDS Ews w (vda_wd_addr gv (j + Zlength wds)))%logic.
Proof.
  induction wds as [|w0 wds IH]; intros j w.
  - simpl. rewrite Zlength_nil, Z.add_0_r. apply pred_ext; cancel.
  - simpl app. simpl vda_wds_from. rewrite IH, Zlength_cons. replace (j + 1 + Zlength wds) with (j + Z.succ (Zlength wds)) by lia.
    apply pred_ext; cancel.
Qed.

End WD.

Lemma vda_wd_ok : VDA_wd_ok.
Proof.
  unfold VDA_wd_ok; intros. unfold VDA_P1, VDA_s7, VDA_Delta. abbreviate_semax.
  Intros.
  assert (Hnd: 1 <= nd <= 3) by (destruct (mode =? 0); lia).
  forward.
  forward_loop (EX i: Z, EX wds: list wdict,
     PROP (0 <= i <= nd; vda_wds_facts mode i wds)
     LOCAL (temp _i (vu i); temp _mode (vu mode); temp _nd (vu nd); temp _which (vu 0); temp _cap (vl 0);
            temp _fail (vu 0); lvar _dd t_ddp v_dd; gvars gv)
     SEP (mem_mgr gv; zstd_globals gv; WG gv;
          @data_at HCS Ews t_wseries (@zero_val HCS t_wseries) (gv _x_valid_dict_api__sr);
          vda_wds_from WDS gv 0 wds; vda_rest gv i;
          @data_at HCS Ews t_wdict (@zero_val HCS t_wdict) (gv _vd_raw);
          @data_at HCS Tsh t_ddp (Zrepeat nullval 3) v_dd;
          TT))
    continue: (EX i: Z, EX wds: list wdict,
     PROP (0 <= i < nd; vda_wds_facts mode (i + 1) wds)
     LOCAL (temp _i (vu i); temp _mode (vu mode); temp _nd (vu nd); temp _which (vu 0); temp _cap (vl 0);
            temp _fail (vu 0); lvar _dd t_ddp v_dd; gvars gv)
     SEP (mem_mgr gv; zstd_globals gv; WG gv;
          @data_at HCS Ews t_wseries (@zero_val HCS t_wseries) (gv _x_valid_dict_api__sr);
          vda_wds_from WDS gv 0 wds; vda_rest gv (i + 1);
          @data_at HCS Ews t_wdict (@zero_val HCS t_wdict) (gv _vd_raw);
          @data_at HCS Tsh t_ddp (Zrepeat nullval 3) v_dd;
          TT))
    break: (EX wds: list wdict, VDA_P2 WG WDS gv v_dd mode nd wds).
  - Exists 0 (@nil wdict). entailer!.
    unfold vda_wds_facts; split; [reflexivity|]; split; [constructor|]; split; [constructor|]; split; [intros; split; constructor | constructor].
  - Intros i wds.
    forward_if.
    2: { forward. Exists wds. assert (i = nd) by lia. subst i. unfold VDA_P2. entailer!. }
    sep_apply (vda_rest_take gv i ltac:(lia)). Intros.
    forward_call (gv, Ews, vda_wd_addr gv i).
    { entailer!. simpl. f_equal. apply vda_addr_eq; auto; lia. }
    Intros wi.
    forward_if (PROP (mode = 0 -> wd_formatted wi = true /\ Forall (fun w => wd_id w <> wd_id wi) wds)
     LOCAL (temp _i (vu i); temp _mode (vu mode); temp _nd (vu nd); temp _which (vu 0); temp _cap (vl 0);
            temp _fail (vu 0); lvar _dd t_ddp v_dd; gvars gv)
     SEP (WG gv; wdict_rep WDS Ews wi (vda_wd_addr gv i); vda_rest gv (i + 1); mem_mgr gv; zstd_globals gv;
          @data_at HCS Ews t_wseries (@zero_val HCS t_wseries) (gv _x_valid_dict_api__sr);
          vda_wds_from WDS gv 0 wds;
          @data_at HCS Ews t_wdict (@zero_val HCS t_wdict) (gv _vd_raw);
          @data_at HCS Tsh t_ddp (Zrepeat nullval 3) v_dd;
          TT)).
    + (* mode 0: the gp_assumes *)
      sep_apply (vda_wd_take_fmt WDS Ews wi (vda_wd_addr gv i)). Intros.
      assert_PROP (offset_val 6152 (force_val (sem_add_ptr_int (Tstruct ___gp_wdict_t noattr) Unsigned (gv _vd_wd) (vu i)))
        = field_address t_wdict (DOT _formatted) (vda_wd_addr gv i)) as Ea.
      { entailer!. rewrite vda_addr_eq by (auto; lia). unfold field_address. rewrite if_true by auto. reflexivity. }
      forward. clear Ea.
      forward_call (Int.repr (if wd_formatted wi then 1 else 0)).
      Intros. assert (Hf: wd_formatted wi = true) by (destruct (wd_formatted wi); [reflexivity | contradiction]).
      sep_apply (wand_frame_elim (@field_at HCS Ews t_wdict (DOT _formatted) (vb (wd_formatted wi)) (vda_wd_addr gv i))).
      deadvars!.
      forward.
      forward_loop (EX k: Z,
        PROP (0 <= k <= i; Forall (fun w => wd_id w <> wd_id wi) (sublist 0 k wds))
        LOCAL (temp _k (vu k); temp _i (vu i); temp _mode (vu mode); temp _nd (vu nd); temp _which (vu 0); temp _cap (vl 0);
            temp _fail (vu 0); lvar _dd t_ddp v_dd; gvars gv)
     SEP (WG gv; wdict_rep WDS Ews wi (vda_wd_addr gv i); vda_rest gv (i + 1); mem_mgr gv; zstd_globals gv;
          @data_at HCS Ews t_wseries (@zero_val HCS t_wseries) (gv _x_valid_dict_api__sr);
          vda_wds_from WDS gv 0 wds;
          @data_at HCS Ews t_wdict (@zero_val HCS t_wdict) (gv _vd_raw);
          @data_at HCS Tsh t_ddp (Zrepeat nullval 3) v_dd;
          TT))
       continue: (EX k: Z,
        PROP (0 <= k < i; Forall (fun w => wd_id w <> wd_id wi) (sublist 0 (k + 1) wds))
        LOCAL (temp _k (vu k); temp _i (vu i); temp _mode (vu mode); temp _nd (vu nd); temp _which (vu 0); temp _cap (vl 0);
            temp _fail (vu 0); lvar _dd t_ddp v_dd; gvars gv)
     SEP (WG gv; wdict_rep WDS Ews wi (vda_wd_addr gv i); vda_rest gv (i + 1); mem_mgr gv; zstd_globals gv;
          @data_at HCS Ews t_wseries (@zero_val HCS t_wseries) (gv _x_valid_dict_api__sr);
          vda_wds_from WDS gv 0 wds;
          @data_at HCS Ews t_wdict (@zero_val HCS t_wdict) (gv _vd_raw);
          @data_at HCS Tsh t_ddp (Zrepeat nullval 3) v_dd;
          TT))
       break: (PROP (mode = 0 -> wd_formatted wi = true /\ Forall (fun w => wd_id w <> wd_id wi) wds)
        LOCAL (temp _i (vu i); temp _mode (vu mode); temp _nd (vu nd); temp _which (vu 0); temp _cap (vl 0);
            temp _fail (vu 0); lvar _dd t_ddp v_dd; gvars gv)
     SEP (WG gv; wdict_rep WDS Ews wi (vda_wd_addr gv i); vda_rest gv (i + 1); mem_mgr gv; zstd_globals gv;
          @data_at HCS Ews t_wseries (@zero_val HCS t_wseries) (gv _x_valid_dict_api__sr);
          vda_wds_from WDS gv 0 wds;
          @data_at HCS Ews t_wdict (@zero_val HCS t_wdict) (gv _vd_raw);
          @data_at HCS Tsh t_ddp (Zrepeat nullval 3) v_dd;
          TT)).
      * Exists 0. entailer!.
      * Intros k.
        forward_if.
        -- sep_apply (vda_wd_take_id WDS Ews wi (vda_wd_addr gv i)). Intros.
           assert_PROP (offset_val 6156 (force_val (sem_add_ptr_int (Tstruct ___gp_wdict_t noattr) Unsigned (gv _vd_wd) (vu i)))
             = field_address t_wdict (DOT _id) (vda_wd_addr gv i)) as Ea.
           { entailer!. rewrite vda_addr_eq by (auto; lia). unfold field_address. rewrite if_true by auto. reflexivity. }
           forward. clear Ea.
           sep_apply (wand_frame_elim (@field_at HCS Ews t_wdict (DOT _id) (vu (wd_id wi)) (vda_wd_addr gv i))).
           assert (Hlw: Zlength wds = i) by apply H2.
           sep_apply (vda_wds_take_id WDS gv wds 0 k ltac:(lia)). Intros. rewrite Z.add_0_l.
           assert_PROP (offset_val 6156 (force_val (sem_add_ptr_int (Tstruct ___gp_wdict_t noattr) Unsigned (gv _vd_wd) (vu k)))
             = field_address t_wdict (DOT _id) (vda_wd_addr gv k)) as Ea.
           { entailer!. rewrite vda_addr_eq by (auto; lia). unfold field_address. rewrite if_true by auto. reflexivity. }
           forward. clear Ea.
           sep_apply (wand_frame_elim (@field_at HCS Ews t_wdict (DOT _id) (vu (wd_id (Znth k wds))) (vda_wd_addr gv k))).
           forward_call (if Int.eq (Int.repr (wd_id wi)) (Int.repr (wd_id (Znth k wds))) then Int.zero else Int.one).
           { entailer!. simpl. unfold vu. destruct (Int.eq _ _); reflexivity. }
           Intros.
           assert (Hne: wd_id (Znth k wds) <> wd_id wi).
           { match goal with Hc: (if Int.eq _ _ then _ else _) <> Int.zero |- _ =>
               intro E; rewrite E, Int.eq_true in Hc; contradiction end. }
           Exists k. entailer!.
           rewrite (sublist_split 0 k (k + 1)) by lia. rewrite Forall_app. split; auto.
           rewrite sublist_len_1 by lia. constructor; auto.
        -- forward. entailer!. split; auto.
           destruct H2 as [Hl _].
           match goal with Hs: Forall _ (sublist 0 k wds) |- _ => rewrite sublist_same in Hs by lia; exact Hs end.
      * Intros k. forward. Exists (k + 1). entailer!.
      * unfold POSTCONDITION, abbreviate. simpl_ret_assert. apply ENTAIL_refl.
    + forward. entailer!.
    + Intros. Exists i (wds ++ [wi]). rewrite vda_wds_from_app.
      assert (Hlw: Zlength wds = i) by apply H2. rewrite Hlw, Z.add_0_l.
      entailer!.
      apply (vda_facts_snoc mode (Zlength wds) wds wi); auto.
  - Intros i wds. forward. Exists (i + 1) wds. entailer!.
  - unfold POSTCONDITION, abbreviate. simpl_ret_assert. apply ENTAIL_refl.
Qed.
