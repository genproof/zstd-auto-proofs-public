(* valid_dict_api main, prologue segment: mode 2's vd_raw and w_series (s11): VDA_P3 -> VDA_P4 (VDA3ProDefs.v). *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.harness.valid_dict_api.WTopSpecs_valid_dict_api.
Require Import Zstd.proof.harness.valid_dict_api.VDA3Defs.
Require Import Zstd.proof.harness.valid_dict_api.VDA3ProDefs.

Local Notation HCS := Zstd.proof.harness.valid_dict_api.HOK_valid_dict_api.CompSpecs.

Lemma vws_wand_take (P A R W: mpred) : (P |-- A * R) -> (R * A |-- W) -> P |-- A * (A -* W).
Proof.
  intros H1 H2. eapply derives_trans; [apply H1|]. apply sepcon_derives; [apply derives_refl|].
  apply wand_sepcon_adjoint; auto.
Qed.

Lemma vws_pull_fn (B N F X: mpred) : (B * (N * (F * X)) = (F * N) * (B * X))%logic.
Proof. apply pred_ext; cancel. Qed.

Lemma vws_zero_wdict :
  @zero_val HCS t_wdict =
  (@zero_val HCS (tarray tuchar 6144), (@zero_val HCS tulong, (@zero_val HCS tint, (@zero_val HCS tuint,
   (@zero_val HCS (tptr tuchar), (@zero_val HCS tulong, @zero_val HCS t_wstate)))))).
Proof.
  rewrite zero_val_eq. unfold fold_reptype. apply JMeq_eq.
  match goal with |- JMeq (@eq_rect_r ?A ?x ?F ?v ?y ?H) _ =>
    eapply JMeq_trans; [apply (@eq_rect_r_JMeq A x y F v H)|] end.
  apply JMeq_refl.
Qed.

Lemma vws_zero_wstate :
  @zero_val HCS t_wstate =
  (@zero_val HCS (tarray tuint 3), (raw_huf, (@zero_val HCS tint, (raw_tabs, @zero_val HCS tint)))).
Proof.
  rewrite zero_val_eq. unfold fold_reptype. apply JMeq_eq.
  match goal with |- JMeq (@eq_rect_r ?A ?x ?F ?v ?y ?H) _ =>
    eapply JMeq_trans; [apply (@eq_rect_r_JMeq A x y F v H)|] end.
  apply JMeq_refl.
Qed.

(* the zeroed vd_raw, field by field (the bytes, huf and tab fields keep their zeros) *)
Lemma vws_raw_open sh q :
  @data_at HCS sh t_wdict (@zero_val HCS t_wdict) q |--
  @field_at HCS sh t_wdict (DOT _bytes) (@zero_val HCS (tarray tuchar 6144)) q *
  @field_at HCS sh t_wdict (DOT _n) (vl 0) q *
  @field_at_ HCS sh t_wdict (DOT _formatted) q *
  @field_at_ HCS sh t_wdict (DOT _id) q *
  @field_at_ HCS sh t_wdict (DOT _content) q *
  @field_at_ HCS sh t_wdict (DOT _content_n) q *
  @field_at_ HCS sh t_wdict (DOT _x_valid_dict_api__st DOT _rep) q *
  @field_at HCS sh t_wdict (DOT _x_valid_dict_api__st DOT _huf) raw_huf q *
  @field_at_ HCS sh t_wdict (DOT _x_valid_dict_api__st DOT _have_huf) q *
  @field_at HCS sh t_wdict (DOT _x_valid_dict_api__st DOT _tab) raw_tabs q *
  @field_at_ HCS sh t_wdict (DOT _x_valid_dict_api__st DOT _have_tab) q *
  spacer sh 13980 13984 q.
Proof.
  unfold_data_at (data_at _ _ _ q). unfold_field_at 7%nat.
  rewrite vws_zero_wdict, vws_zero_wstate. cbn [fst snd]. rewrite zero_val_tulong. cancel.
Qed.

Lemma vws_st_split sh (v: reptype t_wstate) q :
  @field_at HCS sh t_wdict (DOT _x_valid_dict_api__st) v q =
  (@field_at HCS sh t_wdict (DOT _x_valid_dict_api__st DOT _rep) (fst v) q *
   (@field_at HCS sh t_wdict (DOT _x_valid_dict_api__st DOT _huf) (fst (snd v)) q *
    (@field_at HCS sh t_wdict (DOT _x_valid_dict_api__st DOT _have_huf) (fst (snd (snd v))) q *
     (@field_at HCS sh t_wdict (DOT _x_valid_dict_api__st DOT _tab) (fst (snd (snd (snd v)))) q *
      @field_at HCS sh t_wdict (DOT _x_valid_dict_api__st DOT _have_tab) (snd (snd (snd (snd v)))) q))))%logic.
Proof.
  unfold_field_at (field_at _ _ (DOT _x_valid_dict_api__st) _ _). reflexivity.
Qed.

(* vd_raw after the stores: the wdict_t of WAExt c cq *)
Lemma vws_raw_close sh q (c: list Z) (cq: val) (r: list val) :
  r = map vu [1; 4; 8] ->
  @field_at HCS sh t_wdict (DOT _bytes) (@zero_val HCS (tarray tuchar 6144)) q *
  @field_at HCS sh t_wdict (DOT _n) (vl 0) q *
  @field_at HCS sh t_wdict (DOT _formatted) (vu 0) q *
  @field_at HCS sh t_wdict (DOT _id) (vu 0) q *
  @field_at HCS sh t_wdict (DOT _content) cq q *
  @field_at HCS sh t_wdict (DOT _content_n) (vl (Zlength c)) q *
  @field_at HCS sh t_wdict (DOT _x_valid_dict_api__st DOT _rep) r q *
  @field_at HCS sh t_wdict (DOT _x_valid_dict_api__st DOT _huf) raw_huf q *
  @field_at HCS sh t_wdict (DOT _x_valid_dict_api__st DOT _have_huf) (vu 0) q *
  @field_at HCS sh t_wdict (DOT _x_valid_dict_api__st DOT _tab) raw_tabs q *
  @field_at HCS sh t_wdict (DOT _x_valid_dict_api__st DOT _have_tab) (vu 0) q *
  spacer sh 13980 13984 q
  |-- @data_at HCS sh t_wdict (wdict_ext_val (@zero_val HCS (tarray tuchar 6144)) (vl 0) (vu 0) c cq) q.
Proof.
  intros ->. unfold_data_at (data_at _ _ _ q). rewrite vws_st_split.
  unfold wdict_ext_val, raw_stv. cbn [fst snd]. cancel.
Qed.

Lemma vws_bytes_split sh (c: list Z) p :
  Zlength c <= 6144 -> field_compatible t_wdict [] p ->
  @field_at HCS sh t_wdict (DOT _bytes) (zbytes c ++ Zrepeat (Vint Int.zero) (6144 - Zlength c)) p =
  (@data_at HCS sh (tarray tuchar (Zlength c)) (zbytes c) p *
   @data_at HCS sh (tarray tuchar (6144 - Zlength c)) (Zrepeat (Vint Int.zero) (6144 - Zlength c))
     (@field_address0 HCS (tarray tuchar 6144) (SUB (Zlength c)) p))%logic.
Proof.
  intros Hn FC.
  rewrite field_at_data_at.
  assert (E: @field_address HCS t_wdict (DOT _bytes) p = p).
  { unfold field_address. rewrite if_true by auto with field_compatible.
    simpl. rewrite isptr_offset_val_zero; auto. }
  rewrite E. change (@nested_field_type HCS t_wdict (DOT _bytes)) with (tarray tuchar 6144).
  rewrite (split2_data_at_Tarray_app (Zlength c) 6144 sh tuchar (zbytes c)); auto.
  - rewrite Zlength_map; auto.
  - rewrite Zlength_Zrepeat; Zlength_solve.
Qed.

Section WS.
Variable WG : globals -> mpred.
Variable WDS : wdict -> reptype t_wstate -> Prop.

(* borrow formatted and n of a dictionary *)
Lemma vws_take_fn sh wd p :
  wdict_rep WDS sh wd p |--
  (@field_at HCS sh t_wdict (DOT _formatted) (vb (wd_formatted wd)) p *
   @field_at HCS sh t_wdict (DOT _n) (vl (Zlength (wd_bytes wd))) p) *
  ((@field_at HCS sh t_wdict (DOT _formatted) (vb (wd_formatted wd)) p *
    @field_at HCS sh t_wdict (DOT _n) (vl (Zlength (wd_bytes wd))) p) -* wdict_rep WDS sh wd p).
Proof.
  unfold wdict_rep. Intros stv.
  eapply vws_wand_take.
  - unfold_data_at (data_at _ _ _ p). cbn [fst snd wdict_val].
    rewrite vws_pull_fn. apply derives_refl.
  - Exists stv. entailer!. unfold_data_at (data_at _ _ _ p). cbn [fst snd wdict_val]. cancel.
Qed.

(* borrow the bytes of a dictionary (its first n bytes of the bytes field) *)
Lemma vws_take_bytes sh wd p :
  Zlength (wd_bytes wd) <= 6144 ->
  wdict_rep WDS sh wd p |--
  @data_at HCS sh (tarray tuchar (Zlength (wd_bytes wd))) (zbytes (wd_bytes wd)) p *
  (@data_at HCS sh (tarray tuchar (Zlength (wd_bytes wd))) (zbytes (wd_bytes wd)) p -* wdict_rep WDS sh wd p).
Proof.
  intros Hn. unfold wdict_rep. Intros stv.
  assert_PROP (field_compatible t_wdict [] p) as FC by entailer!.
  eapply vws_wand_take.
  - unfold_data_at (data_at _ _ _ p). cbn [fst snd wdict_val].
    rewrite vws_bytes_split by (auto; lia). rewrite !sepcon_assoc. apply derives_refl.
  - Exists stv. apply andp_right; [apply prop_right; auto|].
    unfold_data_at (data_at _ t_wdict _ p). cbn [fst snd wdict_val].
    rewrite vws_bytes_split by (auto; lia). cancel.
Qed.

Lemma vws_ext_arg d q (c: list Z) bv nv fv :
  bytes_ok c -> Zlength c <= 4096 ->
  @data_at HCS Ews t_wdict (wdict_ext_val bv nv fv c q) d *
  @data_at HCS Ews (tarray tuchar (Zlength c)) (zbytes c) q
  |-- wdict_arg WDS d (WAExt c q Ews Ews).
Proof.
  intros Hb Hc. unfold wdict_arg. Exists bv nv fv. entailer!.
Qed.

Lemma vws_own_arg p wd :
  dict_facts wd -> wdict_wf wd -> wdict_rep WDS Ews wd p |-- wdict_arg WDS p (WAOwn wd Ews).
Proof.
  intros Hd Hw. unfold wdict_arg. entailer!.
Qed.

End WS.

Lemma vda_ws_ok : VDA_ws_ok.
Proof.
  unfold VDA_ws_ok; intros. unfold VDA_P3, VDA_s11, VDA_Delta. abbreviate_semax.
  Intros.
  pose proof H1 as (Hlen & Hdf & Hwf & _). pose proof H2 as (Hw & Hw0 & Hnth & _).
  assert (Hdfw: dict_facts wd) by (eapply Forall_forall; [apply Hdf | eapply nth_error_In; eauto]).
  assert (Hwfw: wdict_wf wd) by (eapply Forall_forall; [apply Hwf | eapply nth_error_In; eauto]).
  forward_if.
  - (* mode 2: vd_raw *)
    sep_apply (vws_take_fn WDS Ews wd (vda_wd_addr gv which)). Intros.
    forward.
    assert (Hn: 8 <= Zlength (wd_bytes wd) <= 6144) by (destruct Hdfw as (_ & Hb & _); simpl in Hb; lia).
    forward_if (PROP () LOCAL (temp _x_valid_dict_api__t'6 (vb (andb (wd_formatted wd) (Zlength (wd_bytes wd) <=? 4096)));
        temp _mode (vu mode); temp _nd (vu nd); temp _cap (vl 0); temp _fail (vu 0);
        temp _wd (vda_wd_addr gv which); lvar _dd t_ddp v_dd; gvars gv)
      SEP (@field_at HCS Ews t_wdict (DOT _formatted) (vb (wd_formatted wd)) (vda_wd_addr gv which);
        @field_at HCS Ews t_wdict (DOT _n) (vl (Zlength (wd_bytes wd))) (vda_wd_addr gv which);
        (@field_at HCS Ews t_wdict (DOT _formatted) (vb (wd_formatted wd)) (vda_wd_addr gv which) *
         @field_at HCS Ews t_wdict (DOT _n) (vl (Zlength (wd_bytes wd))) (vda_wd_addr gv which)) -*
          wdict_rep WDS Ews wd (vda_wd_addr gv which);
        mem_mgr gv; zstd_globals gv; WG gv;
        @data_at HCS Ews t_wseries (@zero_val HCS t_wseries) (gv _x_valid_dict_api__sr);
        wdict_rep WDS Ews wd (vda_wd_addr gv which) -* vda_wds_from WDS gv 0 wds;
        @data_at HCS Ews t_wdict (@zero_val HCS t_wdict) (gv _vd_raw);
        @data_at HCS Tsh t_ddp (Zrepeat nullval 3) v_dd; TT)).
    + forward. forward. entailer!.
      destruct (wd_formatted wd); [|contradiction]. simpl andb.
      change (Int.unsigned (Int.shl (Int.repr 1) (Int.repr 12))) with 4096. unfold Int64.cmpu, Int64.ltu.
      rewrite !Int64.unsigned_repr by rep_lia.
      destruct (zlt 4096 (Zlength (wd_bytes wd))); destruct (Zlength (wd_bytes wd) <=? 4096) eqn:E; try reflexivity;
        [apply Z.leb_le in E | apply Z.leb_gt in E]; lia.
    + forward. entailer!. destruct (wd_formatted wd) eqn:Ef; [|reflexivity].
      match goal with Hx: Int.repr 1 = Int.zero |- _ => inversion Hx end.
    + forward_call (Int.repr (if andb (wd_formatted wd) (Zlength (wd_bytes wd) <=? 4096) then 1 else 0)).
      Intros.
      assert (Hf: wd_formatted wd = true /\ Zlength (wd_bytes wd) <= 4096).
      { destruct (andb (wd_formatted wd) (Zlength (wd_bytes wd) <=? 4096)) eqn:E; [|contradiction].
        apply andb_prop in E. destruct E as [E1 E2]. apply Z.leb_le in E2. auto. }
      sep_apply (vws_raw_open Ews (gv _vd_raw)).
      Intros.
      forward. forward. forward. forward. forward.
      forward. forward. forward. forward. forward.
      assert_PROP (isptr (vda_wd_addr gv which)) as Pw by entailer!.
      rewrite (isptr_offset_val_zero _ Pw).
      sep_apply (vws_raw_close Ews (gv _vd_raw) (wd_bytes wd) (vda_wd_addr gv which)).
      sep_apply (wand_frame_elim
        (@field_at HCS Ews t_wdict (DOT _formatted) (vb (wd_formatted wd)) (vda_wd_addr gv which) *
         @field_at HCS Ews t_wdict (DOT _n) (vl (Zlength (wd_bytes wd))) (vda_wd_addr gv which))%logic).
      sep_apply (vws_take_bytes WDS Ews wd (vda_wd_addr gv which) ltac:(lia)).
      sep_apply (vws_ext_arg WDS (gv _vd_raw) (vda_wd_addr gv which) (wd_bytes wd)
        (@zero_val HCS (tarray tuchar 6144)) (vl 0) (vu 0) ltac:(destruct Hdfw; auto) ltac:(lia)).
      forward_call (gv, Ews, gv _x_valid_dict_api__sr, gv _vd_raw, WAExt (wd_bytes wd) (vda_wd_addr gv which) Ews Ews).
      Intros ws. unfold wdict_arg. Intros bv nv fv.
      sep_apply (wand_frame_elim (@data_at HCS Ews (tarray tuchar (Zlength (wd_bytes wd))) (zbytes (wd_bytes wd)) (vda_wd_addr gv which))).
      Exists ws. unfold VDA_P4. entailer!.
      unfold vda_series_facts, vda_dm. simpl. auto.
  - (* the dictionary itself *)
    sep_apply (vws_own_arg WDS (vda_wd_addr gv which) wd Hdfw Hwfw).
    forward_call (gv, Ews, gv _x_valid_dict_api__sr, vda_wd_addr gv which, WAOwn wd Ews).
    Intros ws. unfold wdict_arg. Intros.
    Exists ws. unfold VDA_P4. entailer!.
    unfold vda_series_facts, vda_dm. assert (E: mode =? 2 = false) by (apply Z.eqb_neq; auto).
    rewrite E. simpl. split; [intros; contradiction | auto].
Qed.
