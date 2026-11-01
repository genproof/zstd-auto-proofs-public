(* valid_dict_api main, mode 0: the states of mode 0's setup (ZSTD_d_refMultipleDDicts, a DDict per
   dictionary of vd_wd, each referenced with ZSTD_DCtx_refDDict) and the facts about its DDict set. *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.harness.valid_dict_api.WTopSpecs_valid_dict_api.
Require Import Zstd.proof.harness.valid_dict_api.VDA3Defs.
Require Import Zstd.proof.harness.valid_dict_api.VDA3M0Lemmas.

Local Notation ZCS := Zstd.proof.zstd.Base.CompSpecs.
Local Notation HCS := Zstd.proof.harness.valid_dict_api.HOK_valid_dict_api.CompSpecs.

#[export] Instance M0_wdict_inh : Inhabitant wdict :=
  {| wd_bytes := nil; wd_formatted := false; wd_id := 0; wd_content := nil |}.

#[export] Instance M0_ddict_inh : Inhabitant ddict_st :=
  {| dd_bytes := nil; dd_ref := None; dd_buf := Vundef; dd_ld := None |}.

(* ---------- the model of the setup ---------- *)

(* the parameters after ZSTD_DCtx_setParameter(dctx, ZSTD_d_refMultipleDDicts, 1) on a new context *)
Definition M0_par : dparams :=
  {| dp_fmt := 0; dp_ignore := 0; dp_bmax := 0; dp_wmax := dp_wmax_dflt; dp_multi := 1 |}.

(* the context during the setup: its current DDict d and its set l *)
Definition M0_st (d: option dictref) (l: list (val * ddict_st)) : dctx_st :=
  set_set (set_dict (set_par dctx_init M0_par) d) l.

(* the current DDict after the successful refDDicts of l: the last one *)
Definition M0_cur (l: list (val * ddict_st)) : option dictref :=
  match rev l with nil => None | e :: _ => Some (ddict_ref (fst e) (snd e)) end.

(* the DDicts made so far: non-NULL, copies (dd_ref = None) of the first |l| dictionaries of wds *)
Definition M0_ok (l: list (val * ddict_st)) (wds: list wdict) : Prop :=
  Forall (fun e => isptr (fst e) /\ dd_ref (snd e) = None) l /\
  map (fun e => dd_bytes (snd e)) l = map wd_bytes (sublist 0 (Zlength l) wds).

Lemma M0_cur_snoc l e : M0_cur (l ++ [e]) = Some (ddict_ref (fst e) (snd e)).
Proof. unfold M0_cur. rewrite rev_app_distr. reflexivity. Qed.

Lemma M0_ok_nil wds : M0_ok nil wds.
Proof. split; [constructor | reflexivity]. Qed.

Lemma M0_ok_snoc l wds q dd : M0_ok l wds -> isptr q -> dd_ref dd = None ->
  Zlength l < Zlength wds -> dd_bytes dd = wd_bytes (Znth (Zlength l) wds) -> M0_ok (l ++ [(q, dd)]) wds.
Proof.
  intros [Hf Hm] Hq Hr Hl Hb. split.
  - apply Forall_app; split; auto.
  - rewrite map_app, Zlength_app, Zlength_cons, Zlength_nil, Hm. simpl.
    pose proof (Zlength_nonneg l).
    rewrite (sublist_split 0 (Zlength l) (Zlength l + 1) wds) by lia.
    rewrite (sublist_len_1 (Zlength l) wds) by lia. rewrite map_app. simpl. rewrite Hb. reflexivity.
Qed.

Lemma M0_dd_id w b : dict_facts w -> b = wd_bytes w -> dict_id_of b = wd_id w.
Proof. intros (_ & _ & _ & _ & _ & H & _) ->. exact H. Qed.

(* the bytes of the k-th DDict *)
Lemma M0_ok_bytes l wds k : M0_ok l wds -> Zlength l <= Zlength wds -> 0 <= k < Zlength l ->
  dd_bytes (snd (Znth k l)) = wd_bytes (Znth k wds).
Proof.
  intros [_ Hm] Hl Hk.
  rewrite <- (Znth_map k (fun e => dd_bytes (snd e)) l) by lia. rewrite Hm.
  rewrite Znth_map by list_solve. rewrite Znth_sublist by list_solve. rewrite Z.add_0_r. reflexivity.
Qed.

(* ZSTD_DCtx_refDDict of the next dictionary joins the set: its ID is new *)
Lemma M0_set_add l wds q dd :
  Forall dict_facts wds -> NoDup (map wd_id wds) -> M0_ok l wds -> Zlength l < Zlength wds ->
  dd_bytes dd = wd_bytes (Znth (Zlength l) wds) ->
  set_add l q dd = l ++ [(q, dd)].
Proof.
  intros Hf Hn Hok Hl Hb. unfold set_add.
  replace (existsb _ _) with false; [reflexivity|].
  symmetry. apply Bool.not_true_iff_false. intros Hx. apply existsb_exists in Hx as [e [Hin He]].
  apply Z.eqb_eq in He.
  apply In_Znth_iff in Hin as [k [Hk Ek]]. subst e.
  rewrite Forall_forall in Hf.
  pose proof (Zlength_nonneg l).
  unfold dd_id in He.
  rewrite (M0_ok_bytes l wds k Hok ltac:(lia) Hk) in He. rewrite Hb in He.
  rewrite (M0_dd_id (Znth k wds) _ ltac:(apply Hf, Znth_In; lia) eq_refl) in He.
  rewrite (M0_dd_id (Znth (Zlength l) wds) _ ltac:(apply Hf, Znth_In; lia) eq_refl) in He.
  rewrite <- (Znth_map k wd_id wds) in He by lia. rewrite <- (Znth_map (Zlength l) wd_id wds) in He by lia.
  apply (NoDup_Znth_inj _ _ _ Hn) in He; rewrite ?Zlength_map; lia.
Qed.

(* the bytes of the whole set (VDA_m0_model's premise) *)
Lemma M0_ok_all l wds : M0_ok l wds -> Zlength l = Zlength wds ->
  map (fun e => dd_bytes (snd e)) l = map wd_bytes wds.
Proof. intros [_ Hm] Hl. rewrite Hm, Hl, sublist_same by lia. reflexivity. Qed.

Lemma M0_ok_ref l wds : M0_ok l wds -> Forall (fun e => dd_ref (snd e) = None) l.
Proof. intros [H _]. eapply Forall_impl; [| exact H]. intros e [_ He]. exact He. Qed.

Lemma M0_ok_ptr l wds : M0_ok l wds -> Forall (fun e => isptr (fst e)) l.
Proof. intros [H _]. eapply Forall_impl; [| exact H]. intros e [He _]. exact He. Qed.

(* ---------- the DDicts held by main ---------- *)

Section Res.
Variable DD : globals -> val -> ddict_st -> mpred.

Definition M0_dds (gv: globals) (l: list (val * ddict_st)) : mpred :=
  fold_right sepcon emp (map (fun e => andp (DD gv (fst e) (snd e)) (valid_pointer (fst e))) l).

(* the DDicts of l at the pointer q (the current one's pointer): set_res leaves them out *)
Definition M0_fr (gv: globals) (l: list (val * ddict_st)) (q: val) : mpred :=
  fold_right sepcon emp
    (map (fun e => if Val.eq (fst e) q then andp (DD gv (fst e) (snd e)) (valid_pointer (fst e)) else emp) l).

Lemma M0_dds_app gv l1 l2 : M0_dds gv (l1 ++ l2) = (M0_dds gv l1 * M0_dds gv l2)%logic.
Proof.
  unfold M0_dds. rewrite map_app. induction l1 as [|e l1 IH]; simpl.
  - rewrite emp_sepcon. reflexivity.
  - rewrite IH, sepcon_assoc. reflexivity.
Qed.

Lemma M0_dds_one gv q d : M0_dds gv [(q, d)] = (DD gv q d && valid_pointer q)%logic.
Proof. unfold M0_dds. simpl. rewrite sepcon_emp. reflexivity. Qed.

Lemma M0_split_set gv l q d :
  Forall (fun e => dd_ref (snd e) = None) l ->
  M0_dds gv l = (set_res DD gv Ews l (Some (ddict_ref q d)) * M0_fr gv l q)%logic.
Proof.
  intros Hl. unfold M0_dds, M0_fr, set_res. cbn [cur_ddict ddict_ref dr_src]. induction l as [|e l IH]; simpl.
  - rewrite sepcon_emp. reflexivity.
  - inv Hl. rewrite IH by auto. unfold ddict_res.
    match goal with H: dd_ref (snd e) = None |- _ => rewrite H end.
    destruct (Val.eq (fst e) q); rewrite ?sepcon_emp, ?emp_sepcon;
    apply pred_ext; cancel.
Qed.

(* the DDicts of l: the current one (dict_res), the others of the set (set_res), and a frame F (the DDicts at the
   current one's pointer that set_res leaves out) *)
Lemma M0_res gv l : Forall (fun e => dd_ref (snd e) = None) l ->
  exists F: mpred, M0_dds gv l = (dict_res DD gv Ews (M0_cur l) * set_res DD gv Ews l (M0_cur l) * F)%logic.
Proof.
  intros Hl. destruct l as [|e0 l0] using rev_ind.
  - exists emp. unfold M0_dds, set_res. simpl. rewrite !sepcon_emp. reflexivity.
  - clear IHl0. destruct e0 as [q d]. rewrite M0_cur_snoc. cbn [fst snd].
    apply Forall_app in Hl as [Hl Hd]. inv Hd. cbn [snd] in *.
    exists (M0_fr gv l0 q).
    rewrite M0_dds_app, M0_dds_one, (M0_split_set gv l0 q d Hl).
    replace (set_res DD gv Ews (l0 ++ [(q, d)]) (Some (ddict_ref q d))) with (set_res DD gv Ews l0 (Some (ddict_ref q d))).
    2: { unfold set_res. rewrite map_app, fold_right_app. cbn [cur_ddict ddict_ref dr_src map fold_right fst].
         destruct (Val.eq q q) as [_|]; [|congruence]. rewrite sepcon_emp. reflexivity. }
    unfold dict_res, ddict_ref, ddict_res. cbn [dr_src dr_bytes].
    match goal with H: dd_ref d = None |- _ => rewrite H end. rewrite sepcon_emp.
    apply pred_ext; cancel.
Qed.

(* every DDict of dd[] (the pointers of l, then NULLs) for VDA_E *)
Lemma M0_dd_res gv l k :
  Forall (fun e => isptr (fst e)) l ->
  M0_dds gv l |-- dd_res DD gv (map fst l ++ Zrepeat nullval k).
Proof.
  induction l as [|e l IH]; intros Hp.
  - unfold M0_dds, dd_res, Zrepeat. simpl. induction (Z.to_nat k) as [|n IHn]; simpl; [apply derives_refl|].
    rewrite emp_sepcon. exact IHn.
  - inv Hp. unfold M0_dds, dd_res in *. simpl.
    rewrite if_false by (destruct (fst e); try contradiction; discriminate).
    apply sepcon_derives; [Exists (snd e); apply andp_left1, derives_refl|].
    apply IH; auto.
Qed.

End Res.

(* ---------- vd_wd, element by element ---------- *)

Section Wds.
Variable WDS : wdict -> reptype t_wstate -> Prop.

Lemma M0_wds_app gv k l1 l2 :
  vda_wds_from WDS gv k (l1 ++ l2) = (vda_wds_from WDS gv k l1 * vda_wds_from WDS gv (k + Zlength l1) l2)%logic.
Proof.
  revert k. induction l1 as [|w l1 IH]; intros k; simpl.
  - rewrite emp_sepcon, Zlength_nil, Z.add_0_r. reflexivity.
  - rewrite IH, Zlength_cons, sepcon_assoc. replace (k + 1 + Zlength l1) with (k + Z.succ (Zlength l1)) by lia.
    reflexivity.
Qed.

(* the i-th dictionary of vd_wd out of the others *)
Lemma M0_wds_split gv wds i : 0 <= i < Zlength wds ->
  vda_wds_from WDS gv 0 wds =
  (wdict_rep WDS Ews (Znth i wds) (vda_wd_addr gv i) *
   (vda_wds_from WDS gv 0 (sublist 0 i wds) * vda_wds_from WDS gv (i + 1) (sublist (i + 1) (Zlength wds) wds)))%logic.
Proof.
  intros Hi.
  assert (E: wds = sublist 0 i wds ++ Znth i wds :: sublist (i + 1) (Zlength wds) wds).
  { rewrite <- sublist_next by lia. rewrite sublist_rejoin by lia. rewrite sublist_same by lia. reflexivity. }
  rewrite E at 1. rewrite M0_wds_app. simpl. rewrite Zlength_sublist by lia. rewrite Z.sub_0_r, Z.add_0_l.
  apply pred_ext; cancel.
Qed.

End Wds.

(* ---------- the states of mode 0 ---------- *)

Section States.
Variable DC : globals -> val -> dctx_st -> mpred.
Variable DD : globals -> val -> ddict_st -> mpred.
Variable WDS : wdict -> reptype t_wstate -> Prop.

(* the buffers of VDA_A at the decoder's compspecs, the witnesses folded *)
Definition M0_bufs (ws: wseries) (wd: wdict) (cap: Z) (src buf: val) : mpred :=
  (@malloc_token HCS Ews (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws)))) src *
   @malloc_token HCS Ews (tarray tuchar (cap + 1 + Zlength (wd_bytes wd))) buf *
   pws_pred (VB_W src (Zlength (ws_bytes ws)) buf cap) *
   @data_at ZCS Ews (tarray tuchar (Zlength (ws_bytes ws))) (zbytes (ws_bytes ws)) src *
   @data_at_ ZCS Ews (tarray tuchar cap) buf *
   @data_at ZCS Ews (tarray tuchar (Zlength (wd_bytes wd))) (zbytes (wd_bytes wd)) (offset_val (cap + 1) buf))%logic.

(* VDA_A of mode 0, the buffers converted *)
Definition M0_P (gv: globals) (v_dd: val) (nd: Z) (wds: list wdict) (wd: wdict) (ws: wseries) (cap: Z)
    (src buf dctx: val) : environ -> mpred :=
  PROP ()
  LOCAL (temp _mode (Vint (Int.repr 0)); temp _nd (Vint (Int.repr nd)); temp _cap (Vlong (Int64.repr cap));
         temp _fail (Vint (Int.repr 0)); temp _src src; temp _buf buf; temp _dst buf;
         temp _dctx dctx; lvar _dd t_ddp v_dd; gvars gv)
  SEP (mem_mgr gv; zstd_globals gv; DC gv dctx dctx_init;
       @data_at HCS Ews t_wseries (wseries_val ws) (gv _x_valid_dict_api__sr);
       vda_wds_from WDS gv 0 wds; M0_bufs ws wd cap src buf;
       @data_at HCS Tsh t_ddp (Zrepeat nullval 3) v_dd; TT).

(* after the setup: dd[] = the DDicts of l then NULLs; when no step failed, every dictionary of wds has its DDict
   in the set, the last one current *)
Definition M0_M (gv: globals) (v_dd: val) (nd: Z) (wds: list wdict) (wd: wdict) (ws: wseries) (cap: Z)
    (src buf dctx: val) (fail: Z) (l: list (val * ddict_st)) (st: dctx_st) : environ -> mpred :=
  PROP (fail = 0 \/ fail = 1; M0_ok l wds; Zlength l <= nd;
        fail = 0 -> Zlength l = nd /\ st = M0_st (M0_cur l) l)
  LOCAL (temp _mode (Vint (Int.repr 0)); temp _cap (Vlong (Int64.repr cap)); temp _fail (Vint (Int.repr fail));
         temp _src src; temp _buf buf; temp _dst buf; temp _dctx dctx; lvar _dd t_ddp v_dd; gvars gv)
  SEP (mem_mgr gv; zstd_globals gv; DC gv dctx st;
       @data_at HCS Ews t_wseries (wseries_val ws) (gv _x_valid_dict_api__sr);
       vda_wds_from WDS gv 0 wds; M0_bufs ws wd cap src buf;
       @data_at HCS Tsh t_ddp (map fst l ++ Zrepeat nullval (3 - Zlength l)) v_dd;
       M0_dds DD gv l; TT).

End States.
