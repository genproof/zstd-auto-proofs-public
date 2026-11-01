(* valid_dict_api main: the prologue, from main's start to the allocation check (VDA3Defs.VDA_pro_ok). *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.harness.valid_dict_api.WTopSpecs_valid_dict_api.
Require Import Zstd.proof.harness.valid_dict_api.VDA3Defs.
Require Import Zstd.proof.harness.valid_dict_api.VDA3ProDefs Zstd.proof.harness.valid_dict_api.VDA3ProWD Zstd.proof.harness.valid_dict_api.VDA3ProWS Zstd.proof.harness.valid_dict_api.VDA3ProFR.
Require Zstd.proof.top.MainPre6.

Local Notation HCS := Zstd.proof.harness.valid_dict_api.HOK_valid_dict_api.CompSpecs.

Local Notation VDA_restg :=
  (filter (fun ig : ident * globdef (fundef function) type => negb (id_in_list (fst ig) wvar_ids))
    (filter (fun ig : ident * globdef (fundef function) type => negb (id_in_list (fst ig) MainPre6.zstd_var_ids))
       (Vardefs Zstd.contracts.x_valid_dict_api.whole_prog))).

(* ---------- main's precondition: the decoder's tables, the writer's statics, sr, vd_wd, vd_raw ---------- *)

Lemma VDA_filter_filter {A: Type} (f g: A -> bool) l :
  filter f (filter g l) = filter (fun x => andb (g x) (f x)) l.
Proof.
  induction l as [|a l IH]; simpl; auto.
  destruct (g a); simpl; [destruct (f a); simpl; rewrite IH; auto | exact IH].
Qed.

Lemma VDA_wvar_not_zstd : forallb (fun i => negb (id_in_list i MainPre6.zstd_var_ids)) wvar_ids = true.
Proof. vm_compute. reflexivity. Qed.

Lemma VDA_wvardefs :
  filter (fun ig => id_in_list (fst ig) wvar_ids)
    (filter (fun ig => negb (id_in_list (fst ig) MainPre6.zstd_var_ids)) (Vardefs Zstd.contracts.x_valid_dict_api.whole_prog))
  = wvardefs.
Proof.
  rewrite VDA_filter_filter. unfold wvardefs. apply filter_ext. intros [i g]; cbn [fst].
  destruct (id_in_list i wvar_ids) eqn:E; [|apply andb_false_r].
  rewrite andb_true_r.
  pose proof VDA_wvar_not_zstd as H. rewrite forallb_forall in H.
  apply id_in_list_true in E. exact (H i E).
Qed.

(* the remaining globals in the order of their identifiers (PTree order): sr at position 82 of 86, one other
   global, then vd_wd and vd_raw *)
Lemma VDA_rest_skip :
  skipn 82 VDA_restg =
  (_x_valid_dict_api__sr, Gvar v_x_valid_dict_api__sr) :: firstn 1 (skipn 83 VDA_restg) ++
  [(_vd_wd, Gvar v_vd_wd); (_vd_raw, Gvar v_vd_raw)].
Proof.
  vm_compute. reflexivity.
Qed.

Lemma VDA_sr_zero gv :
  globs2pred gv (_x_valid_dict_api__sr, Gvar v_x_valid_dict_api__sr) |--
  @data_at HCS Ews t_wseries (@zero_val HCS t_wseries) (gv _x_valid_dict_api__sr).
Proof.
  unfold globs2pred. apply derives_extract_prop; intros Hh.
  unfold globvar2pred. simpl. rewrite sepcon_emp.
  change 786936 with (@sizeof HCS t_wseries).
  apply mapsto_zero_data_at_zero.
  - auto.
  - reflexivity.
  - reflexivity.
  - destruct Hh as [b ->]. repeat split; auto.
    hnf. rewrite Ptrofs.unsigned_zero. apply la_env_cs_sound; vm_compute; reflexivity.
Qed.

Lemma VDA_raw_zero gv :
  globs2pred gv (_vd_raw, Gvar v_vd_raw) |-- @data_at HCS Ews t_wdict (@zero_val HCS t_wdict) (gv _vd_raw).
Proof.
  unfold globs2pred. apply derives_extract_prop; intros Hh.
  unfold globvar2pred. simpl. rewrite sepcon_emp.
  change 13984 with (@sizeof HCS t_wdict).
  apply mapsto_zero_data_at_zero.
  - auto.
  - reflexivity.
  - reflexivity.
  - destruct Hh as [b ->]. repeat split; auto.
    hnf. rewrite Ptrofs.unsigned_zero. apply la_env_cs_sound; vm_compute; reflexivity.
Qed.

Lemma VDA_wd_zero gv :
  globs2pred gv (_vd_wd, Gvar v_vd_wd) |-- vda_rest gv 0.
Proof.
  unfold globs2pred. apply derives_extract_prop; intros Hh.
  unfold globvar2pred. simpl. rewrite sepcon_emp.
  change 41952 with (@sizeof HCS (tarray t_wdict 3)).
  eapply derives_trans; [apply mapsto_zero_data_at_zero|].
  - auto.
  - reflexivity.
  - reflexivity.
  - destruct Hh as [b ->]. repeat split; auto.
    hnf. rewrite Ptrofs.unsigned_zero. apply la_env_cs_sound; vm_compute; reflexivity.
  - unfold vda_rest, vda_wd_addr. rewrite Z.mul_0_l. rewrite <- data_at_offset_zero.
    rewrite (@zero_val_tarray HCS t_wdict 3). apply derives_refl.
Qed.

Lemma VDA_rest_zero gv :
  InitGPred VDA_restg gv |--
  @data_at HCS Ews t_wseries (@zero_val HCS t_wseries) (gv _x_valid_dict_api__sr) *
  (vda_rest gv 0 * (@data_at HCS Ews t_wdict (@zero_val HCS t_wdict) (gv _vd_raw) * TT)).
Proof.
  rewrite <- (firstn_skipn 82 VDA_restg). rewrite InitGPred_app. rewrite VDA_rest_skip.
  rewrite InitGPred_consD, InitGPred_app, !InitGPred_consD, InitGPred_nilD, sepcon_emp.
  sep_apply VDA_sr_zero. sep_apply VDA_wd_zero. sep_apply VDA_raw_zero. cancel.
Qed.

Lemma VDA_pre (WG: globals -> mpred) (HWG: forall gv, InitGPred wvardefs gv |-- WG gv) gv :
  globals_ok gv ->
  InitGPred (Vardefs Zstd.contracts.x_valid_dict_api.whole_prog) gv |--
  zstd_globals gv * (WG gv * (@data_at HCS Ews t_wseries (@zero_val HCS t_wseries) (gv _x_valid_dict_api__sr) *
    (vda_rest gv 0 * (@data_at HCS Ews t_wdict (@zero_val HCS t_wdict) (gv _vd_raw) * TT)))).
Proof.
  intros Hgv. eapply derives_trans.
  - apply (MainPre6.main_pre_fact6 Zstd.contracts.x_valid_dict_api.whole_prog); [|exact Hgv].
    unfold MainPre6.all_progs. do 17 right; left; reflexivity.
  - apply sepcon_derives; [apply derives_refl|].
    rewrite (MainPre6.MP_InitGPred_filter (fun ig => id_in_list (fst ig) wvar_ids)).
    rewrite VDA_wvardefs. apply sepcon_derives; [apply HWG|].
    exact (VDA_rest_zero gv).
Qed.

(* ---------- borrowing vd_wd[which] ---------- *)

Lemma VDA_borrow (A P R: mpred) : (P |-- A * R) -> (A * R |-- P) -> P |-- A * (A -* P).
Proof.
  intros H1 H2. eapply derives_trans; [exact H1|]. apply sepcon_derives; [apply derives_refl|].
  apply wand_sepcon_adjoint. rewrite sepcon_comm. exact H2.
Qed.

Lemma VDA_wds_split WDS gv (l: list wdict) : forall i k w, nth_error l k = Some w ->
  vda_wds_from WDS gv i l =
  (vda_wds_from WDS gv i (firstn k l) *
   (wdict_rep WDS Ews w (vda_wd_addr gv (i + Z.of_nat k)) * vda_wds_from WDS gv (i + Z.of_nat k + 1) (skipn (S k) l)))%logic.
Proof.
  induction l as [|a l IH]; intros i k w Hk; [destruct k; discriminate|].
  destruct k as [|k]; simpl in Hk.
  - inv Hk. simpl. rewrite emp_sepcon, Z.add_0_r. reflexivity.
  - simpl. rewrite (IH (i + 1) k w Hk). rewrite sepcon_assoc.
    replace (i + 1 + Z.of_nat k) with (i + Z.pos (Pos.of_succ_nat k)) by lia. reflexivity.
Qed.

Lemma VDA_wds_borrow WDS gv (wds: list wdict) (which: Z) (wd: wdict) :
  0 <= which -> nth_error wds (Z.to_nat which) = Some wd ->
  vda_wds_from WDS gv 0 wds |--
  wdict_rep WDS Ews wd (vda_wd_addr gv which) * (wdict_rep WDS Ews wd (vda_wd_addr gv which) -* vda_wds_from WDS gv 0 wds).
Proof.
  intros Hw Hn.
  apply VDA_borrow with (R := (vda_wds_from WDS gv 0 (firstn (Z.to_nat which) wds) *
                               vda_wds_from WDS gv (which + 1) (skipn (S (Z.to_nat which)) wds))%logic).
  - rewrite (VDA_wds_split WDS gv wds 0 (Z.to_nat which) wd Hn).
    rewrite Z2Nat.id by lia. rewrite Z.add_0_l. cancel.
  - rewrite (VDA_wds_split WDS gv wds 0 (Z.to_nat which) wd Hn).
    rewrite Z2Nat.id by lia. rewrite Z.add_0_l. cancel.
Qed.

(* ---------- s10: gp_assume(!wd->formatted) for modes 1, 3, 4 ---------- *)

Definition VDA_s10 : statement := ltac:(let x := eval cbv [vda_seq_nth VDA_spine] in (vda_seq_nth 10 VDA_spine) in exact x).

Lemma VDA_wd_eq p w : isptr p -> 0 <= w < 3 ->
  force_val (@sem_binary_operation' HCS Oadd (tarray t_wdict 3) tuint p (vu w)) = offset_val (w * @sizeof HCS t_wdict) p.
Proof.
  intros Hp Hw. destruct p; try contradiction. unfold vu. simpl.
  f_equal. unfold Ptrofs.of_intu, Ptrofs.of_int. rewrite Int.unsigned_repr by rep_lia.
  rewrite ptrofs_mul_repr. rewrite Z.mul_comm. reflexivity.
Qed.

Ltac kill :=
  match goal with
  | H: false = true |- _ => discriminate H
  | H: true = false |- _ => discriminate H
  | H: ?x <> ?x |- _ => exfalso; exact (H eq_refl)
  | H: Int.repr ?x = Int.repr ?y |- _ =>
      exfalso; apply repr_inj_unsigned in H; [lia | rep_lia | rep_lia]
  | H: Int.repr ?x = Int.zero |- _ =>
      exfalso; apply (f_equal Int.unsigned) in H; rewrite Int.unsigned_repr in H by rep_lia;
      rewrite Int.unsigned_zero in H; lia
  | H: typed_true _ _ |- _ => inv H
  | H: typed_false _ _ |- _ => inv H
  end.

Ltac ifs := repeat apply -> seq_assoc; apply semax_if_seq; forward_if; try solve [kill | exfalso; lia].

Section S10.
Variable DC : globals -> val -> dctx_st -> mpred.
Variable DD : globals -> val -> ddict_st -> mpred.
Variable WG : globals -> mpred.
Variable WDS : wdict -> reptype t_wstate -> Prop.

Definition VDA_Q3 (gv: globals) (v_dd: val) (mode nd which: Z) (wds: list wdict) (wd: wdict) : environ -> mpred :=
  PROP (0 <= mode < 7; if mode =? 0 then 2 <= nd <= 3 else nd = 1; vda_wds_facts mode nd wds;
        0 <= which < nd; mode <> 0 -> which = 0; nth_error wds (Z.to_nat which) = Some wd)
  LOCAL (temp _mode (vu mode); temp _nd (vu nd); temp _cap (vl 0); temp _fail (vu 0);
         temp _wd (vda_wd_addr gv which); lvar _dd t_ddp v_dd; gvars gv)
  SEP (mem_mgr gv; zstd_globals gv; WG gv;
       @data_at HCS Ews t_wseries (@zero_val HCS t_wseries) (gv _x_valid_dict_api__sr);
       wdict_rep WDS Ews wd (vda_wd_addr gv which);
       wdict_rep WDS Ews wd (vda_wd_addr gv which) -* vda_wds_from WDS gv 0 wds;
       @data_at HCS Ews t_wdict (@zero_val HCS t_wdict) (gv _vd_raw);
       @data_at HCS Tsh t_ddp (Zrepeat nullval 3) v_dd;
       TT).

Lemma VDA_s10_ok (Espec: OracleKind) gv v_dd mode nd which wds wd :
  semax (VDA_Delta DC DD WG WDS) (VDA_Q3 gv v_dd mode nd which wds wd) VDA_s10
    (normal_ret_assert (VDA_P3 WG WDS gv v_dd mode nd which wds wd)).
Proof.
  unfold VDA_Q3, VDA_P3, VDA_s10, VDA_Delta. abbreviate_semax. Intros.
  assert (Hm: mode = 0 \/ mode = 1 \/ mode = 2 \/ mode = 3 \/ mode = 4 \/ mode = 5 \/ mode = 6) by lia.
  destruct Hm as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]].
  all: ifs; forward; ifs; forward; forward_if; try solve [kill].
  (* the gp_assume: modes 1, 3, 4 *)
  all: match goal with
       | |- semax _ _ (Ssequence (Sset _x_valid_dict_api__t'81 _) _) _ =>
           unfold wdict_rep; Intros stv; forward;
           forward_call (Int.repr (if wd_formatted wd then 0 else 1));
           [ entailer!; unfold wdict_val; simpl; destruct (wd_formatted wd); reflexivity
           | unfold wdict_rep; Exists stv; entailer!; split; [|split; [|split]]; auto; intros _;
             destruct (wd_formatted wd); auto; contradiction ]
       | _ => forward; entailer!; split; [|split; [|split]]; auto; intros; lia
       end.
Qed.

End S10.

(* ---------- s16..s21: src, buf, dctx, dst, dict ---------- *)

Definition VDA_s16_21 : statement := ltac:(let x := eval cbv [vda_seq_nth VDA_spine] in
  (Ssequence (Ssequence (Ssequence (Ssequence (Ssequence (vda_seq_nth 16 VDA_spine) (vda_seq_nth 17 VDA_spine))
     (vda_seq_nth 18 VDA_spine)) (vda_seq_nth 19 VDA_spine)) (vda_seq_nth 20 VDA_spine)) (vda_seq_nth 21 VDA_spine)) in exact x).

Lemma VDA_dict_val buf cap : isptr buf -> 0 <= cap <= Int64.max_unsigned - 1 ->
  force_val (@sem_binary_operation' HCS Oadd (tptr tuchar) tint
     (eval_binop Oadd (tptr tuchar) tulong buf (Vlong (Int64.repr cap))) (Vint (Int.repr 1)))
  = offset_val (cap + 1) buf.
Proof.
  intros Hp Hc. destruct buf; try contradiction. simpl.
  rewrite !(Ptrofs.mul_commut (Ptrofs.repr 1)), !Ptrofs.mul_one.
  rewrite Ptrofs.add_assoc.
  replace (Ptrofs.of_int64 (Int64.repr cap)) with (Ptrofs.repr cap)
    by (unfold Ptrofs.of_int64; rewrite Int64.unsigned_repr by rep_lia; reflexivity).
  rewrite ptrofs_add_repr. reflexivity.
Qed.

Lemma VDA_bytes_split sh (bs: list Z) p : Zlength bs <= 2 ^ 19 ->
  @field_at HCS sh t_wseries (DOT _bytes) (zbytes bs ++ Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength bs)) p =
  (@data_at HCS sh (tarray tuchar (Zlength bs)) (zbytes bs) (@field_address HCS t_wseries (DOT _bytes) p) *
   @data_at HCS sh (tarray tuchar (2 ^ 19 - Zlength bs)) (Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength bs))
     (@field_address0 HCS (tarray tuchar (2 ^ 19)) (SUB (Zlength bs)) (@field_address HCS t_wseries (DOT _bytes) p)))%logic.
Proof.
  intros Hn. rewrite field_at_data_at.
  change (nested_field_type t_wseries (DOT _bytes)) with (tarray tuchar (2 ^ 19)).
  apply split2_data_at_Tarray_app.
  - rewrite Zlength_map. reflexivity.
  - rewrite Zlength_Zrepeat; [reflexivity|]. pose proof (Zlength_nonneg bs). lia.
Qed.

(* sr without its bytes and n *)
Definition VDA_sr_rest (ws: wseries) (p: val) : mpred :=
  (@data_at HCS Ews (tarray tuchar (2 ^ 19 - Zlength (ws_bytes ws))) (Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength (ws_bytes ws)))
     (@field_address0 HCS (tarray tuchar (2 ^ 19)) (SUB (Zlength (ws_bytes ws))) (@field_address HCS t_wseries (DOT _bytes) p)) *
   @field_at HCS Ews t_wseries (DOT _content)
     (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws))) p *
   @field_at HCS Ews t_wseries (DOT _content_n) (vl (Zlength (ws_content ws))) p *
   @field_at HCS Ews t_wseries (DOT _f)
     (map winfo_val (ws_frames ws) ++ Zrepeat (winfo_val winfo0) (4 - Zlength (ws_frames ws))) p *
   @field_at HCS Ews t_wseries (DOT _nframes) (vu (Zlength (ws_frames ws))) p *
   spacer Ews 786932 786936 p)%logic.

Lemma VDA_ws_unfold ws p : Zlength (ws_bytes ws) <= 2 ^ 19 ->
  @data_at HCS Ews t_wseries (wseries_val ws) p |--
  @data_at HCS Ews (tarray tuchar (Zlength (ws_bytes ws))) (zbytes (ws_bytes ws)) (@field_address HCS t_wseries (DOT _bytes) p) *
  @field_at HCS Ews t_wseries (DOT _n) (vl (Zlength (ws_bytes ws))) p * VDA_sr_rest ws p.
Proof.
  intros Hn. unfold VDA_sr_rest. unfold_data_at (data_at _ _ _ p). cbn [fst snd wseries_val].
  rewrite (VDA_bytes_split Ews (ws_bytes ws) p Hn). cancel.
Qed.

Lemma VDA_ws_fold ws p : Zlength (ws_bytes ws) <= 2 ^ 19 ->
  @data_at HCS Ews (tarray tuchar (Zlength (ws_bytes ws))) (zbytes (ws_bytes ws)) (@field_address HCS t_wseries (DOT _bytes) p) *
  @field_at HCS Ews t_wseries (DOT _n) (vl (Zlength (ws_bytes ws))) p * VDA_sr_rest ws p |--
  @data_at HCS Ews t_wseries (wseries_val ws) p.
Proof.
  intros Hn. unfold VDA_sr_rest. unfold_data_at (data_at _ _ _ p). cbn [fst snd wseries_val].
  rewrite (VDA_bytes_split Ews (ws_bytes ws) p Hn). cancel.
Qed.

Section S16.
Variable DC : globals -> val -> dctx_st -> mpred.
Variable DD : globals -> val -> ddict_st -> mpred.
Variable WG : globals -> mpred.
Variable WDS : wdict -> reptype t_wstate -> Prop.

(* the facts of the allocation check, from those of the segments *)
Lemma VDA_facts_of mode nd which wds wd ws cap :
  0 <= mode < 7 -> (if mode =? 0 then 2 <= nd <= 3 else nd = 1) -> vda_wds_facts mode nd wds ->
  vda_which_facts mode nd which wds wd -> vda_series_facts mode wd ws -> vda_cap_facts mode wd ws cap ->
  vda_facts mode nd which wds wd ws cap.
Proof.
  intros Hm Hnd (Hl & Hdf & Hwf & Hm0 & Hid) (Hw & Hw0 & Hn & Hf134) (Hm2 & Hsf & Hwsf & Hdw)
    (Hfr & Hm4 & Hc56 & Hc).
  unfold vda_facts.
  refine (conj Hm (conj Hl (conj Hnd (conj Hw (conj Hw0 (conj Hn (conj Hdf (conj Hwf (conj _
    (conj Hf134 (conj Hm2 (conj Hsf (conj Hwsf (conj Hfr (conj Hm4 (conj Hc56 (conj Hc Hdw))))))))))))))))).
  intros E. destruct (Hm0 E) as [Hfm Hnd0]. split; [|exact Hnd0].
  apply Forall_forall. intros w Hin. rewrite Forall_forall in Hfm, Hid.
  pose proof (Hfm w Hin) as Hf. split; auto.
Qed.

Lemma VDA_s16_ok (Espec: OracleKind) gv v_dd mode nd which wds wd ws cap :
  semax (VDA_Delta DC DD WG WDS) (VDA_P5 WDS gv v_dd mode nd which wds wd ws cap) VDA_s16_21
    (normal_ret_assert (EX src: val, EX buf: val, EX dctx: val,
       VDA_B DC WDS gv v_dd mode nd which wds wd ws cap src buf dctx)).
Proof.
  unfold VDA_P5, VDA_s16_21, VDA_Delta. abbreviate_semax. Intros.
  match goal with Hs: vda_series_facts _ _ _ |- _ => pose proof Hs as (_ & Hsf & _) end.
  pose proof Hsf as (Hbok & Hcok & Hnb & Hnc & _).
  sep_apply (VDA_ws_unfold ws (gv _x_valid_dict_api__sr) Hnb). Intros.
  forward.
  forward_call (gv, Ews, @field_address HCS t_wseries (DOT _bytes) (gv _x_valid_dict_api__sr), ws_bytes ws).
  { entailer!.
    match goal with H: field_compatible _ [] (field_address t_wseries (DOT _bytes) ?p) |- _ =>
      unfold field_address in *; destruct (field_compatible_dec t_wseries (DOT _bytes) p) as [Hfc|Hfc];
      [| destruct H as [Hx _]; contradiction] end.
    simpl. destruct (gv _x_valid_dict_api__sr); try contradiction. reflexivity. }
  Intros src. forward.
  sep_apply (VDA_ws_fold ws (gv _x_valid_dict_api__sr) Hnb).
  match goal with Hc: vda_cap_facts _ _ _ _ |- _ => pose proof Hc as (_ & _ & _ & Hcap) end.
  assert (Hdn: 0 <= Zlength (wd_bytes wd) <= 2 ^ 12 + 2048).
  { match goal with Hw: vda_which_facts _ _ _ _ _, Hd: vda_wds_facts _ _ _ |- _ =>
      destruct Hw as (_ & _ & Hn & _); destruct Hd as (_ & Hdf & _) end.
    apply nth_error_In in Hn. rewrite Forall_forall in Hdf. destruct (Hdf wd Hn) as (_ & Hl & _).
    pose proof (Zlength_nonneg (wd_bytes wd)). lia. }
  forward_call (tarray tuchar (cap + 1 + Zlength (wd_bytes wd)), gv).
  { simpl. rep_lia. }
  Intros buf.
  forward_call gv. Intros dctx.
  forward. forward.
  sep_apply (modus_ponens_wand (wdict_rep WDS Ews wd (vda_wd_addr gv which)) (vda_wds_from WDS gv 0 wds)).
  assert (Hf: vda_facts mode nd which wds wd ws cap) by (apply VDA_facts_of; auto).
  destruct (eq_dec buf nullval) as [Hb|Hb].
  - subst buf. forward_if; [discriminate|].
    forward. Exists src nullval dctx. unfold VDA_B. entailer!.
  - Intros. assert_PROP (isptr buf) as Hpb by entailer!.
    forward_if; [|contradiction].
    forward.
    { entailer!. destruct buf; try contradiction; simpl; auto. }
    Exists src buf dctx. unfold VDA_B. entailer!.
    + rewrite if_false by auto. symmetry. apply VDA_dict_val; auto. rep_lia.
    + rewrite if_false by auto. cancel.
Qed.

End S16.

(* ---------- regrouping the spine: Ssequence seg rest ---------- *)

Fixpoint vda_fold_seq (l: list statement) : statement :=
  match l with
  | nil => Sskip
  | s :: nil => s
  | s :: l' => Ssequence s (vda_fold_seq l')
  end.

Ltac vda_seg S :=
  let k := eval cbv [S unfold_Ssequence length app] in (length (unfold_Ssequence S)) in
  match goal with |- semax _ _ ?c _ =>
    let r := eval cbv [vda_fold_seq skipn unfold_Ssequence app] in (vda_fold_seq (skipn k (unfold_Ssequence c))) in
    apply (semax_unfold_Ssequence (Ssequence S r)); [reflexivity|]
  end.

Lemma VDA_tyc_g_isSome: forall (V: varspecs) G i, In i (map fst V) ->
  isSome (Maps.PTree.get i (make_tycontext_g V G)).
Proof.
  intros. unfold make_tycontext_g. induction G as [|[j f] G IH]; simpl.
  - induction V as [|[k t] V IHV]; simpl in *; [contradiction|].
    rewrite Maps.PTree.gsspec. destruct (peq i k); simpl; auto.
    apply IHV. destruct H; [congruence|auto].
  - rewrite Maps.PTree.gsspec. destruct (peq i j); simpl; auto.
Qed.

Lemma vda_pro_ok DC DD WG WDS : VDA_pro_ok DC DD WG WDS.
Proof.
intros HWG HC.
unfold main_spec, QPmain_spec_ext', NDmk_funspec.
split3; [reflexivity | reflexivity |].
intros Espec DTL gv.
simpl fn_body; simpl fn_params; simpl fn_return.
change (map fst []) with (@nil ident).
eapply (main_pre_InitGpred
          (sepcon (zstd_globals gv) (sepcon (WG gv) (sepcon (@data_at HCS Ews t_wseries (@zero_val HCS t_wseries) (gv _x_valid_dict_api__sr))
             (sepcon (vda_rest gv 0) (sepcon (@data_at HCS Ews t_wdict (@zero_val HCS t_wdict) (gv _vd_raw)) TT)))))
          _ _ _ Zstd.contracts.x_valid_dict_api.whole_prog).
4: idtac.
- intros. apply VDA_pre; auto.
- reflexivity.
- apply Forall_forall; intros [i g] Hin; simpl fst.
  apply VDA_tyc_g_isSome. unfold Vprog, QPvarspecs. rewrite map_map.
  apply in_map_iff. exists (i, g); auto.
- process_stackframe_of.
  repeat rewrite <- data_at__offset_zero.
  try simple apply start_function_aux1.
  match goal with |- semax ?D ?P ?c (frame_ret_assert (function_body_ret_assert ?t _) ?F) =>
    apply (semax_post (frame_ret_assert (function_body_ret_assert t (PROP () LOCAL () (SEP (TT)))) F))
  end.
  1,2,3: intros; simpl; normalize.
  1: intros [v|]; simpl; unfold bind_ret; simpl; normalize;
       try (intros x; apply andp_left2; apply sepcon_derives; [unfold_lift; apply TT_right | auto]).
  abbreviate_semax.
  sep_apply (create_mem_mgr gv).
  (* s0..s6 *)
  forward_call 7. Intros mode. forward. forward. forward. forward. forward.
  forward_loop (EX i: Z, PROP (0 <= i <= 3) LOCAL (temp _i (Vint (Int.repr i)); temp _fail (Vint (Int.repr 0)); temp _cap (Vlong (Int64.repr 0)); temp _which (Vint (Int.repr 0)); temp _nd (Vint (Int.repr 1)); temp _mode (Vint (Int.repr mode)); lvar _dd t_ddp v_dd; gvars gv)
    SEP (mem_mgr gv; @data_at HCS Tsh t_ddp (Zrepeat nullval i ++ Zrepeat Vundef (3 - i)) v_dd; zstd_globals gv; WG gv;
     @data_at HCS Ews t_wseries (@zero_val HCS t_wseries) (gv _x_valid_dict_api__sr);
     vda_rest gv 0; @data_at HCS Ews t_wdict (@zero_val HCS t_wdict) (gv _vd_raw); TT; has_ext tt))
   break: (PROP () LOCAL (temp _fail (Vint (Int.repr 0)); temp _cap (Vlong (Int64.repr 0)); temp _which (Vint (Int.repr 0)); temp _nd (Vint (Int.repr 1)); temp _mode (Vint (Int.repr mode)); lvar _dd t_ddp v_dd; gvars gv)
    SEP (mem_mgr gv; @data_at HCS Tsh t_ddp (Zrepeat nullval 3) v_dd; zstd_globals gv; WG gv;
     @data_at HCS Ews t_wseries (@zero_val HCS t_wseries) (gv _x_valid_dict_api__sr);
     vda_rest gv 0; @data_at HCS Ews t_wdict (@zero_val HCS t_wdict) (gv _vd_raw); TT; has_ext tt)).
  { Exists 0. entailer!. }
  { Intros i. forward_if.
    - forward. forward. Exists (i + 1). entailer!.
      apply derives_refl'. f_equal.
      assert (i = 0 \/ i = 1 \/ i = 2) as [-> | [-> | ->]] by lia; reflexivity.
    - forward. entailer!. replace i with 3 by lia. simpl. apply derives_refl. }
  forward_if (EX nd: Z, PROP (if mode =? 0 then 2 <= nd <= 3 else nd = 1)
    LOCAL (temp _fail (Vint (Int.repr 0)); temp _cap (Vlong (Int64.repr 0)); temp _which (Vint (Int.repr 0)); temp _nd (Vint (Int.repr nd)); temp _mode (Vint (Int.repr mode)); lvar _dd t_ddp v_dd; gvars gv)
    SEP (mem_mgr gv; @data_at HCS Tsh t_ddp (Zrepeat nullval 3) v_dd; zstd_globals gv; WG gv;
     @data_at HCS Ews t_wseries (@zero_val HCS t_wseries) (gv _x_valid_dict_api__sr);
     vda_rest gv 0; @data_at HCS Ews t_wdict (@zero_val HCS t_wdict) (gv _vd_raw); TT; has_ext tt)).
  { forward_call 2. Intros c. forward. Exists (2 + c). entailer!.
    simpl. lia. }
  { forward. Exists 1. entailer!.
    destruct (Z.eqb_spec mode 0); auto. subst. contradiction. }
  Intros nd.
  (* s7: the w_dict loop *)
  apply -> seq_assoc. eapply semax_seq'.
  { eapply semax_pre; [| apply (vda_wd_ok DC DD WG WDS Espec gv v_dd mode nd)].
    unfold VDA_P1. entailer!. }
  Intros wds.
  (* s8..s10: which, wd, gp_assume(!wd->formatted) for modes 1/3/4 *)
  unfold VDA_P2. Intros.
  match goal with Hf: vda_wds_facts _ _ _ |- _ => pose proof Hf as (Hlen & Hdf & Hwf & Hm0 & Hid0) end.
  forward_if (EX which: Z, PROP (0 <= which < nd; mode <> 0 -> which = 0)
    LOCAL (temp _mode (vu mode); temp _nd (vu nd); temp _which (vu which); temp _cap (vl 0); temp _fail (vu 0);
           lvar _dd t_ddp v_dd; gvars gv)
    SEP (mem_mgr gv; zstd_globals gv; WG gv;
         @data_at HCS Ews t_wseries (@zero_val HCS t_wseries) (gv _x_valid_dict_api__sr);
         vda_wds_from WDS gv 0 wds; vda_rest gv nd;
         @data_at HCS Ews t_wdict (@zero_val HCS t_wdict) (gv _vd_raw);
         @data_at HCS Tsh t_ddp (Zrepeat nullval 3) v_dd; TT)).
  { forward_call nd.
    { destruct (Z.eqb_spec mode 0); [rep_lia | subst; contradiction]. }
    Intros w. forward. Exists w. entailer!. }
  { forward. Exists 0. entailer!.
    destruct (Z.eqb_spec mode 0); [subst; contradiction | lia]. }
  Intros which.
  destruct (nth_error wds (Z.to_nat which)) as [wd|] eqn:Hn.
  2: { exfalso. apply nth_error_None in Hn. rewrite Zlength_correct in Hlen. lia. }
  sep_apply (VDA_wds_borrow WDS gv wds which wd ltac:(lia) Hn). Intros.
  assert_PROP (isptr (gv _vd_wd)) as Hpwd.
  { unfold wdict_rep. Intros stv. entailer!. }
  forward.
  assert (Hw3: 0 <= which < 3) by (destruct (mode =? 0); lia).
  match goal with |- context [temp _wd ?v] => replace v with (vda_wd_addr gv which)
    by (unfold vda_wd_addr; symmetry; apply (VDA_wd_eq (gv _vd_wd) which Hpwd Hw3)) end.
  apply -> seq_assoc. eapply semax_seq'.
  { eapply semax_pre; [| apply (VDA_s10_ok DC DD WG WDS Espec gv v_dd mode nd which wds wd)].
    unfold VDA_Q3. entailer!. }
  (* s11: w_series *)
  subst MORE_COMMANDS; unfold abbreviate.
  vda_seg VDA_s11. eapply semax_seq'; [apply (vda_ws_ok DC DD WG WDS Espec gv v_dd mode nd which wds wd)|].
  Intros ws.
  (* s12..s15 *)
  vda_seg VDA_s12_15. eapply semax_seq'; [apply (vda_fr_ok DC DD WG WDS Espec gv v_dd mode nd which wds wd ws)|].
  Intros cap.
  (* s16..s21 *)
  vda_seg VDA_s16_21. eapply semax_seq'; [apply (VDA_s16_ok DC DD WG WDS Espec gv v_dd mode nd which wds wd ws cap)|].
  Intros src buf dctx.
  vda_seg VDA_rest_s.
  exact (HC Espec gv v_dd mode nd which wds wd ws cap src buf dctx).
Qed.
