(* valid_params main, segment B (see the header of VPMain.v). *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.harness.valid_params.VPMain.

Local Notation HCS := Zstd.proof.harness.valid_params.HOK_valid_params.CompSpecs.
Local Notation ZCS := Zstd.proof.zstd.Base.CompSpecs.
Local Notation tout := (Tstruct _ZSTD_outBuffer_s noattr).
Local Notation tin := (Tstruct _ZSTD_inBuffer_s noattr).


(* ---------- the facts after B, from the mode's model theorem ---------- *)

Lemma VPB_tiles_csize : forall fs off coff n cn, tiles fs off coff n cn -> Forall (fun f => 0 <= wi_csize f) fs.
Proof.
  induction fs as [|f fs IH]; simpl; intros off coff n cn H; constructor.
  - lia.
  - destruct H as (_ & _ & _ & _ & _ & H). eapply IH; exact H.
Qed.

Lemma VPB_all_ok_unmagic wl fs : all_ok wl (map wi_unmagic fs) = all_ok wl fs.
Proof. induction fs as [|f fs IH]; simpl; auto. rewrite IH. reflexivity. Qed.

Lemma VPB_skipn_sublist (l: list Z) : skipn 4 l = sublist 4 (Zlength l) l.
Proof.
  unfold sublist. rewrite Zlength_correct, Nat2Z.id, firstn_all. reflexivity.
Qed.

Lemma VPB_blocks_within fs lim : blocks_within_b fs lim = true ->
  Forall (fun f => wi_skippable f = false -> wi_csize f <= lim /\ wi_size f <= lim) fs.
Proof.
  unfold blocks_within_b. induction fs as [|f fs IH]; simpl; intros H; constructor.
  - apply andb_prop in H. destruct H as [H _]. intros Hs. rewrite Hs in H. simpl in H.
    apply andb_prop in H. destruct H as [A B]. apply Z.leb_le in A. apply Z.leb_le in B. lia.
  - apply IH. apply andb_prop in H. apply H.
Qed.

Lemma VPB_ws_ck_id ws : ws_ck ws (ws_bytes ws) = ws.
Proof. destruct ws; reflexivity. Qed.

Lemma VPB_sb mode ws b' p wlim :
  VP_SA_facts mode ws b' -> vp_written (dmode_of p) (vp_view mode ws b') ->
  0 <= wlim <= dp_wmax p -> dp_wmax p <= Int64.max_unsigned ->
  VP_SB_facts mode ws b' p wlim.
Proof.
  intros HA Hw Hwl Hwm. pose proof HA as (Hm & Hsf & Hwf & Hck & Hb & H3 & Hn).
  pose proof Hsf as (Hbo & Hco & Hbl & Hcl & Hnf & Ht & _).
  pose proof Hck as (Hlen & Hbo' & _).
  pose proof (sl_tiles_bounds _ _ _ _ _ Ht) as (_ & _ & Hbd).
  pose proof (VPB_tiles_csize _ _ _ _ _ Ht) as Hcs.
  assert (Hsrc : ws_bytes (vp_view mode ws b') = vp_src mode b').
  { unfold vp_view, vp_src, vp_base. destruct (mode =? 3) eqn:E3.
    - apply Z.eqb_eq in E3. rewrite (Hb ltac:(lia)). cbn [ws_unmagic ws_bytes]. apply VPB_skipn_sublist.
    - cbn [ws_ck ws_bytes]. rewrite sublist_same; reflexivity. }
  split; [exact HA|]. split; [|split; [exact Hsrc|]].
  2:{ intros E3 f Hf. subst mode. destruct (H3 eq_refl) as (f' & Hf' & Hsk). rewrite Hf in Hf'.
      inversion Hf'; subst f'. rewrite <- Hsrc. unfold vp_view. cbn [Z.eqb].
      apply (vp_mg_written ws f Hsf Hwf Hf Hsk). }
  unfold VP_dfacts. cbn [ws_ck ws_bytes ws_content ws_frames].
  split; [exact Hw|]. split; [unfold vp_view; destruct (mode =? 3); reflexivity|].
  split; [rewrite Hsrc; reflexivity|].
  split; [unfold vp_base; destruct (mode =? 3); auto|].
  split; [rewrite Hsrc; exact Hn|].
  split; [exact Hbo'|]. split; [exact Hco|]. split; [lia|]. split; [exact Hcl|]. split; [exact Hnf|].
  split; [exact Hwf|].
  split.
  { unfold vp_base. destruct (mode =? 3) eqn:E3.
    - apply Z.eqb_eq in E3. destruct (H3 E3) as (f & Hf & _). rewrite Hf. constructor; [|constructor].
      rewrite Hf in Ht, Hbd, Hcs. simpl in Ht. inversion Hcs as [|? ? Hc0 _]. subst mode.
      unfold vp_src in Hn. change (vp_base 3) with 4 in Hn.
      rewrite (Hb ltac:(lia)) in Hn |- *. destruct Ht as (Hst & Hcst & Hsz & Hcsz & _ & Hn0 & Hcn).
      destruct (zlt (Zlength (ws_bytes ws)) 4).
      + rewrite sublist_nil_gen in Hn by lia. rewrite Zlength_nil in Hn. lia.
      + rewrite Zlength_sublist in Hn by lia. lia.
    - eapply Forall_impl; [|exact (Forall_and Hbd Hcs)]. simpl. intros f ((A & B & C & D & E) & F).
      unfold wi_end in C. lia. }
  split; [lia|].
  assert (Hok : forall wl, all_ok wl (ws_frames (vp_view mode ws b')) = all_ok wl (ws_frames ws)).
  { intros wl. unfold vp_view. destruct (mode =? 3); [apply VPB_all_ok_unmagic | reflexivity]. }
  split; [intros H; rewrite Hok, <- VPS_all_ok_oneshot by exact Hwf; exact H|].
  split; [intros H1 H2; rewrite Hok; apply (VPS_all_ok_within _ wlim); [lia | exact H1 | exact H2]|].
  intros ipos got. unfold h_at_end, vp_view, vp_base. destruct (mode =? 3); cbn [ws_ck ws_unmagic ws_frames];
    clear; induction (ws_frames ws) as [|f fs IH]; simpl; auto; rewrite IH; unfold wi_end; simpl.
  - replace (wi_start f + (wi_size f - 4)) with (wi_start f + wi_size f - 4) by lia. reflexivity.
  - rewrite Z.sub_0_r. reflexivity.
Qed.

Lemma VPB_m0 ws b' p : VP_SA_facts 0 ws b' ->
  dp_fmt p = 0 -> dp_ignore p = 1 -> dp_bmax p = 0 -> dp_wmax p = dp_wmax_dflt ->
  VP_SB_facts 0 ws b' p (2 ^ 27).
Proof.
  intros HA Hf Hi Hb Hw. pose proof HA as (_ & Hsf & Hwf & Hck & _).
  apply VPB_sb; auto.
  - unfold dmode_of. rewrite Hf, Hi, Hb. change (vp_view 0 ws b') with (ws_ck ws b').
    apply vp_ck_written; auto.
  - rewrite Hw. unfold dp_wmax_dflt. lia.
  - rewrite Hw. unfold dp_wmax_dflt. rep_lia.
Qed.

Lemma VPB_dflt mode ws b' p wlim : VP_SA_facts mode ws b' -> mode = 1 \/ mode = 2 ->
  dp_fmt p = 0 -> dp_ignore p = 0 -> dp_bmax p = 0 -> 0 <= wlim <= dp_wmax p -> dp_wmax p <= Int64.max_unsigned ->
  VP_SB_facts mode ws b' p wlim.
Proof.
  intros HA Hm Hf Hi Hb Hw1 Hw2. pose proof HA as (_ & Hsf & Hwf & Hck & Hbb & _).
  apply VPB_sb; auto.
  unfold dmode_of. rewrite Hf, Hi, Hb.
  unfold vp_view. replace (mode =? 3) with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite (Hbb ltac:(lia)), VPB_ws_ck_id. apply vp_dflt_written; auto.
Qed.

Lemma VPB_m2 ws b' p b : VP_SA_facts 2 ws b' ->
  dp_fmt p = 0 -> dp_ignore p = 0 -> dp_bmax p = b -> 1024 <= b <= ZSTD_BLOCKSIZE_MAX -> dp_wmax p = dp_wmax_dflt ->
  blocks_within_b (ws_frames ws) b = true ->
  VP_SB_facts 2 ws b' p (2 ^ 27).
Proof.
  intros HA Hf Hi Hb Hbl Hw Hbw. pose proof HA as (_ & Hsf & Hwf & Hck & Hbb & _).
  apply VPB_sb; auto.
  - unfold dmode_of. rewrite Hf, Hi, Hb.
    replace (b =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    change (vp_view 2 ws b') with (ws_ck ws b').
    rewrite (Hbb ltac:(lia)), VPB_ws_ck_id. apply vp_bm_written; auto.
    apply VPB_blocks_within; auto.
  - rewrite Hw. unfold dp_wmax_dflt. lia.
  - rewrite Hw. unfold dp_wmax_dflt. rep_lia.
Qed.

Lemma VPB_m3 ws b' p : VP_SA_facts 3 ws b' ->
  dp_fmt p = 1 -> dp_ignore p = 0 -> dp_bmax p = 0 -> dp_wmax p = dp_wmax_dflt ->
  VP_SB_facts 3 ws b' p (2 ^ 27).
Proof.
  intros HA Hf Hi Hb Hw. pose proof HA as (_ & Hsf & Hwf & Hck & _ & H3 & _).
  destruct (H3 eq_refl) as (f & Hfs & Hsk).
  apply VPB_sb; auto.
  - unfold dmode_of. rewrite Hf, Hi, Hb. change (vp_view 3 ws b') with (ws_unmagic ws).
    apply (vp_mg_written ws f); auto.
  - rewrite Hw. unfold dp_wmax_dflt. lia.
  - rewrite Hw. unfold dp_wmax_dflt. rep_lia.
Qed.

Lemma VPB_ps_bmax b : b = 0 \/ 1024 <= b <= 2 ^ 17 ->
  param_set (dc_par dctx_init) ZSTD_d_maxBlockSize b =
  Some {| dp_fmt := 0; dp_ignore := 0; dp_bmax := b; dp_wmax := dp_wmax_dflt; dp_multi := 0 |}.
Proof.
  intros H. unfold param_set.
  change (ZSTD_d_maxBlockSize =? ZSTD_d_windowLogMax) with false.
  change (ZSTD_d_maxBlockSize =? ZSTD_d_format) with false.
  change (ZSTD_d_maxBlockSize =? ZSTD_d_forceIgnoreChecksum) with false.
  change (ZSTD_d_maxBlockSize =? ZSTD_d_refMultipleDDicts) with false.
  change (ZSTD_d_maxBlockSize =? ZSTD_d_maxBlockSize) with true. cbv beta iota.
  replace ((b =? 0) || ((1024 <=? b) && (b <=? ZSTD_BLOCKSIZE_MAX)))%bool with true; [reflexivity|].
  symmetry. unfold ZSTD_BLOCKSIZE_MAX. destruct H as [->|H]; [reflexivity|].
  apply orb_true_iff. right. apply andb_true_iff. split; apply Z.leb_le; lia.
Qed.

Lemma VPB_ps_wl wl : wl = 0 \/ 10 <= wl <= 31 ->
  param_set (dc_par dctx_init) ZSTD_d_windowLogMax wl =
  Some {| dp_fmt := 0; dp_ignore := 0; dp_bmax := 0; dp_wmax := 2 ^ (if wl =? 0 then 27 else wl); dp_multi := 0 |}.
Proof.
  intros H. unfold param_set.
  change (ZSTD_d_windowLogMax =? ZSTD_d_windowLogMax) with true. cbv beta iota zeta.
  destruct H as [->|H]; [reflexivity|].
  replace (wl =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  replace ((10 <=? wl) && (wl <=? 31))%bool with true; [reflexivity|].
  symmetry. apply andb_true_iff. split; apply Z.leb_le; lia.
Qed.

Lemma VPB_shl wl : 0 <= wl < 64 -> Int64.shl (Int64.repr 1) (Int64.repr wl) = Int64.repr (2 ^ wl).
Proof.
  intros H. rewrite Int64.shl_mul_two_p, Int64.mul_commut, Int64.mul_one.
  rewrite Int64.unsigned_repr by rep_lia. rewrite two_p_equiv. reflexivity.
Qed.

(* ---------- the statements s12, s13, s14 ---------- *)

Definition VPB_s12 : statement := ltac:(
  let s := eval cbv [VP_drop VP_body0] in (VP_drop 12 VP_body0) in
  lazymatch s with Ssequence ?x _ => exact x end).
Definition VPB_s13 : statement := ltac:(
  let s := eval cbv [VP_drop VP_body0] in (VP_drop 13 VP_body0) in
  lazymatch s with Ssequence ?x _ => exact x end).
Definition VPB_s14 : statement := ltac:(
  let s := eval cbv [VP_drop VP_body0] in (VP_drop 14 VP_body0) in
  lazymatch s with Ssequence ?x _ => exact x end).

Lemma VPB_drop12 : VP_drop 12 VP_body0 = Ssequence VPB_s12 (VP_drop 13 VP_body0).
Proof. reflexivity. Qed.
Lemma VPB_drop13 : VP_drop 13 VP_body0 = Ssequence VPB_s13 (VP_drop 14 VP_body0).
Proof. reflexivity. Qed.
Lemma VPB_drop14 : VP_drop 14 VP_body0 = Ssequence VPB_s14 (VP_drop 15 VP_body0).
Proof. reflexivity. Qed.

Section Seg.
Context {Espec: OracleKind}.
Variable DC : globals -> val -> dctx_st -> mpred.
Variable DD : globals -> val -> ddict_st -> mpred.
Variable WG : globals -> mpred.
Variable WDS : wdict -> reptype t_wstate -> Prop.
Local Notation Delta := (VP_Delta DC DD WG WDS).


Lemma VPB_step {Espec': OracleKind} Delta' k s P :
  VP_drop k VP_body0 = Ssequence s (VP_drop (S k) VP_body0) ->
  semax Delta' P (Ssequence s (VP_rest (S k))) VP_RR -> semax Delta' P (VP_rest k) VP_RR.
Proof. intros H H1. unfold VP_rest in *. rewrite H. apply seq_assoc. exact H1. Qed.

Lemma VPB_tail (gv: globals) (vz vi vo: val) (mode: Z) (ws: wseries) (b': list Z) (p: dparams) (wlim doc: Z)
    (src dctx: val) :
  VP_SB_facts mode ws b' p wlim -> isptr src -> isptr dctx ->
  (forall p wlim, VP_SB_facts mode ws b' p wlim ->
     semax Delta (VP_SB DC WG gv vz vi vo mode ws b' p wlim src dctx) (VP_rest 15) VP_RR) ->
  semax Delta
   (PROP ()
    LOCAL (temp _r (vl 0); temp _documented (Vint (Int.repr doc));
           temp _mode (Vint (Int.repr mode)); temp _wlim (vl wlim);
           temp _base (vl (vp_base mode)); temp _n (vl (Zlength (vp_src mode b'))); temp _src src; temp _dctx dctx;
           lvar _zfh t_fh vz; lvar _in tin vi; lvar _out tout vo; gvars gv)
    SEP (mem_mgr gv; zstd_globals gv; WG gv; DC gv dctx (set_par dctx_init p);
         data_at Ews t_wseries (wseries_val (ws_ck ws b')) (gv _x_valid_params__sr);
         malloc_token Ews (tarray tuchar (Zlength (vp_src mode b'))) src;
         data_at Ews (tarray tuchar (Zlength (vp_src mode b'))) (zbytes (vp_src mode b')) src;
         data_at_ Tsh t_fh vz; data_at_ Tsh tin vi; data_at_ Tsh tout vo; TT; has_ext tt))
   (VP_rest 13) VP_RR.
Proof.
  intros HB Hs Hd Hk.
  apply (VPB_step _ 13 VPB_s13); [exact VPB_drop13|].
  unfold VPB_s13, vl.
  unfold VP_Delta, VP_RR. abbreviate_semax.
  forward_if (PROP () LOCAL (temp _x_valid_params__t'29 (Vint Int.one); temp _r (Vlong (Int64.repr 0));
           temp _mode (Vint (Int.repr mode)); temp _wlim (Vlong (Int64.repr wlim));
           temp _base (Vlong (Int64.repr (vp_base mode))); temp _n (Vlong (Int64.repr (Zlength (vp_src mode b'))));
           temp _src src; temp _dctx dctx;
           lvar _zfh t_fh vz; lvar _in tin vi; lvar _out tout vo; gvars gv)
    SEP (mem_mgr gv; zstd_globals gv; WG gv; DC gv dctx (set_par dctx_init p);
         data_at Ews t_wseries (wseries_val (ws_ck ws b')) (gv _x_valid_params__sr);
         malloc_token Ews (tarray tuchar (Zlength (vp_src mode b'))) src;
         data_at Ews (tarray tuchar (Zlength (vp_src mode b'))) (zbytes (vp_src mode b')) src;
         data_at_ Tsh t_fh vz; data_at_ Tsh tin vi; data_at_ Tsh tout vo; TT; has_ext tt)).
  { forward. entailer!. }
  { forward_call 0. forward. entailer!. }
  forward_call Int.one.
  unfold POSTCONDITION, abbreviate.
  apply (VPB_step _ 14 VPB_s14); [exact VPB_drop14|]. unfold VPB_s14. abbreviate_semax.
  forward_call 0.
  forward_if. { exfalso. apply H'. reflexivity. }
  unfold POSTCONDITION, abbreviate.
  eapply semax_pre; [|apply (Hk p wlim HB)]. unfold VP_SB, vl. entailer!.
Qed.

Ltac VPB_fif_add t v :=
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp t v :: L) (SEPx R))) end.

(* B: s12..s14 *)
Lemma VP_segB (gv: globals) (vz vi vo: val) (mode: Z) (ws: wseries) (b': list Z) (src dctx: val) :
  (forall p wlim, VP_SB_facts mode ws b' p wlim ->
     semax Delta (VP_SB DC WG gv vz vi vo mode ws b' p wlim src dctx) (VP_rest 15) VP_RR) ->
  semax Delta (VP_SA DC WG gv vz vi vo mode ws b' src dctx) (VP_rest 12) VP_RR.
Proof.
  intros Hk.
  apply (VPB_step _ 12 VPB_s12); [exact VPB_drop12|].
  unfold VP_SA. Intros. rename H into HA, Psrc into Hs, Pdctx into Hd.
  unfold VPB_s12, VP_Delta, VP_RR, vl. abbreviate_semax.
  forward_if (EX p: dparams, EX wlim: Z, EX doc: Z,
    PROP (VP_SB_facts mode ws b' p wlim)
    LOCAL (temp _r (Vlong (Int64.repr 0)); temp _documented (Vint (Int.repr doc));
           temp _mode (Vint (Int.repr mode)); temp _wlim (Vlong (Int64.repr wlim));
           temp _base (Vlong (Int64.repr (vp_base mode))); temp _n (Vlong (Int64.repr (Zlength (vp_src mode b'))));
           temp _src src; temp _dctx dctx;
           lvar _zfh t_fh vz; lvar _in tin vi; lvar _out tout vo; gvars gv)
    SEP (mem_mgr gv; zstd_globals gv; WG gv; DC gv dctx (set_par dctx_init p);
         data_at Ews t_wseries (wseries_val (ws_ck ws b')) (gv _x_valid_params__sr);
         malloc_token Ews (tarray tuchar (Zlength (vp_src mode b'))) src;
         data_at Ews (tarray tuchar (Zlength (vp_src mode b'))) (zbytes (vp_src mode b')) src;
         data_at_ Tsh t_fh vz; data_at_ Tsh tin vi; data_at_ Tsh tout vo; TT; has_ext tt))%assert.
  { (* mode 0 *)
    assert (mode = 0) by (pose proof (proj1 HA); apply repr_inj_unsigned in H; rep_lia). subst mode.
    forward_call (gv, dctx, dctx_init, 1002, 1).
    { cbv; tauto. }
    Intros vret. destruct vret as [r st']. cbn [fst snd] in *.
    match goal with Hp: after_stage _ _ _ _ |- _ =>
      apply after_stage_init in Hp; [unfold setpar_res in Hp | reflexivity] end.
    match goal with Hp: if _ then _ else _ |- _ =>
      cbv - [set_par dctx_init is_error_code] in Hp; destruct Hp as [-> ->] end.
    forward.
    Exists {| dp_fmt := 0; dp_ignore := 1; dp_bmax := 0; dp_wmax := dp_wmax_dflt; dp_multi := 0 |} (2 ^ 27) 1.
    entailer!. apply VPB_m0; auto. apply derives_refl. }
  assert (Hm0 : mode <> 0) by (intro; subst; apply H; reflexivity). clear H.
  forward_if.
  { (* mode 1 *)
    assert (mode = 1) by (pose proof (proj1 HA);
      match goal with Hr: Int.repr mode = Int.repr 1 |- _ => apply repr_inj_unsigned in Hr; rep_lia end).
    subst mode.
    forward_call 2. Intros c.
    forward_if.
    2:{ (* ZSTD_DCtx_setMaxWindowSize *)
      VPB_fif_add _x_valid_params__t'16 (Vint (Int.repr 31)).
      { exfalso. match goal with Hq: Int64.eq _ _ = true |- _ => vm_compute in Hq; discriminate Hq end. }
      { forward. entailer!. }
      forward_call (2 ^ 10, 2 ^ 31). Intros m.
      forward. forward. forward.
      forward_call (gv, dctx, dctx_init, m).
      Intros vret. destruct vret as [r st']. cbn [fst snd] in *.
      match goal with Hp: context [Z.leb (2 ^ 10) m] |- _ =>
        replace ((2 ^ 10 <=? m) && (m <=? 2 ^ 31))%bool with true in Hp
          by (symmetry; apply andb_true_iff; split; apply Z.leb_le; lia);
        destruct Hp as [-> ->] end.
      forward.
      Exists {| dp_fmt := 0; dp_ignore := 0; dp_bmax := 0; dp_wmax := m; dp_multi := 0 |} m 0.
      entailer!. apply VPB_dflt; auto; cbn; rep_lia. apply derives_refl. }
    (* ZSTD_d_windowLogMax *)
    forward_call 2. Intros c2.
    match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
      forward_if (EX wl: Z, PROPx ((wl = 0 \/ 10 <= wl <= 31) :: P)
                    (LOCALx (temp _x_valid_params__t'12 (Vint (Int.repr wl)) :: L) (SEPx R))) end.
    { forward. Exists 0. entailer!. }
    { VPB_fif_add _x_valid_params__t'13 (Vint (Int.repr 31)).
      { exfalso. match goal with Hq: Int64.eq _ _ = true |- _ => vm_compute in Hq; discriminate Hq end. }
      { forward. entailer!. }
      forward_call (10, 31). Intros wl. forward. Exists wl. entailer!. }
    Intros wl. forward.
    forward_if (PROP ()
      LOCAL (temp _wl (Vint (Int.repr wl)); temp _mode (Vint (Int.repr 1));
             temp _wlim (Vlong (Int64.repr (2 ^ (if wl =? 0 then 27 else wl))));
             temp _base (Vlong (Int64.repr (vp_base 1)));
             temp _documented (Vint (Int.repr (if wl =? 0 then 1 else 0)));
             temp _n (Vlong (Int64.repr (Zlength (vp_src 1 b'))));
             temp _src src; temp _dctx dctx; lvar _zfh t_fh vz; lvar _in tin vi; lvar _out tout vo; gvars gv)
      SEP (mem_mgr gv; zstd_globals gv; WG gv; DC gv dctx dctx_init;
           data_at Ews t_wseries (wseries_val (ws_ck ws b')) (gv _x_valid_params__sr);
           malloc_token Ews (tarray tuchar (Zlength (vp_src 1 b'))) src;
           data_at Ews (tarray tuchar (Zlength (vp_src 1 b'))) (zbytes (vp_src 1 b')) src;
           data_at_ Tsh t_fh vz; data_at_ Tsh tin vi; data_at_ Tsh tout vo; TT; has_ext tt)).
    { forward.
      { entailer!. change (Int.unsigned Int64.iwordsize') with 64. lia. }
      forward. entailer!.
      rewrite (proj2 (Z.eqb_neq wl 0)) by assumption.
      rewrite VPB_shl by lia. auto. }
    { forward. entailer!. }
    forward_call (gv, dctx, dctx_init, 100, wl).
    { cbv; tauto. }
    Intros vret. destruct vret as [r st']. cbn [fst snd] in *.
    match goal with Hp: after_stage _ _ _ _ |- _ =>
      apply after_stage_init in Hp; [unfold setpar_res in Hp | reflexivity] end.
    match goal with Hp: context [param_set] |- _ =>
      rewrite (VPB_ps_wl wl H3 : param_set (dc_par dctx_init) 100 wl = _) in Hp;
      change (100 =? ZSTD_d_stableOutBuffer) with false in Hp; cbv beta iota in Hp; destruct Hp as [-> ->] end.
    forward.
    Exists {| dp_fmt := 0; dp_ignore := 0; dp_bmax := 0; dp_wmax := 2 ^ (if wl =? 0 then 27 else wl);
              dp_multi := 0 |} (2 ^ (if wl =? 0 then 27 else wl)) (if wl =? 0 then 1 else 0).
    assert (Hp2 : 0 <= 2 ^ (if wl =? 0 then 27 else wl) <= 2 ^ 31).
    { destruct (wl =? 0); [rep_lia|]. split; [apply Z.pow_nonneg; lia | apply Z.pow_le_mono_r; lia]. }
    entailer!. apply VPB_dflt; auto; cbn [dp_wmax]; rep_lia. }
  forward_if.
  { (* mode 2 *)
    assert (mode = 2) by (pose proof (proj1 HA);
      match goal with Hr: Int.repr mode = Int.repr 2 |- _ => apply repr_inj_unsigned in Hr; rep_lia end).
    subst mode.
    forward_call 2. Intros c.
    forward_if (EX b: Z,
      PROP (b = 0 \/ 1024 <= b <= 2 ^ 17)
      LOCAL (temp _x_valid_params__t'21 (Vint (Int.repr b)); temp _mode (Vint (Int.repr 2));
             temp _wlim (Vlong (Int64.repr (2 ^ 27))); temp _blim (Vlong (Int64.repr (2 ^ 17)));
             temp _base (Vlong (Int64.repr (vp_base 2)));
             temp _documented (Vint (Int.repr 1)); temp _n (Vlong (Int64.repr (Zlength (vp_src 2 b'))));
             temp _src src; temp _dctx dctx; lvar _zfh t_fh vz; lvar _in tin vi; lvar _out tout vo; gvars gv)
      SEP (mem_mgr gv; zstd_globals gv; DC gv dctx dctx_init; WG gv;
           data_at Ews t_wseries (wseries_val (ws_ck ws b')) (gv _x_valid_params__sr);
           malloc_token Ews (tarray tuchar (Zlength (vp_src 2 b'))) src;
           data_at Ews (tarray tuchar (Zlength (vp_src 2 b'))) (zbytes (vp_src 2 b')) src; data_at_ Tsh t_fh vz;
           data_at_ Tsh tin vi; data_at_ Tsh tout vo; TT; has_ext tt)).
    { forward. Exists 0. entailer!. }
    { forward_call (1024, 2 ^ 17). Intros bv. forward. Exists bv. entailer!. }
    Intros b. forward.
    forward_if (PROP ()
      LOCAL (temp _b (Vint (Int.repr b)); temp _mode (Vint (Int.repr 2));
             temp _wlim (Vlong (Int64.repr (2 ^ 27)));
             temp _blim (Vlong (Int64.repr (if b =? 0 then 2 ^ 17 else b)));
             temp _base (Vlong (Int64.repr (vp_base 2)));
             temp _documented (Vint (Int.repr 1)); temp _n (Vlong (Int64.repr (Zlength (vp_src 2 b'))));
             temp _src src; temp _dctx dctx; lvar _zfh t_fh vz; lvar _in tin vi; lvar _out tout vo; gvars gv)
      SEP (mem_mgr gv; zstd_globals gv; DC gv dctx dctx_init; WG gv;
           data_at Ews t_wseries (wseries_val (ws_ck ws b')) (gv _x_valid_params__sr);
           malloc_token Ews (tarray tuchar (Zlength (vp_src 2 b'))) src;
           data_at Ews (tarray tuchar (Zlength (vp_src 2 b'))) (zbytes (vp_src 2 b')) src; data_at_ Tsh t_fh vz;
           data_at_ Tsh tin vi; data_at_ Tsh tout vo; TT; has_ext tt)).
    { forward. entailer!. rewrite (proj2 (Z.eqb_neq b 0)) by assumption. reflexivity. }
    { forward. entailer!. }
    forward_call (gv, dctx, dctx_init, 1005, b).
    { cbv; tauto. }
    Intros vret. destruct vret as [r st']. cbn [fst snd] in *.
    match goal with Hp: after_stage _ _ _ _ |- _ =>
      apply after_stage_init in Hp; [unfold setpar_res in Hp | reflexivity] end.
    match goal with Hp: context [param_set] |- _ =>
      rewrite (VPB_ps_bmax b H2 : param_set (dc_par dctx_init) 1005 b = _) in Hp;
      change (1005 =? ZSTD_d_stableOutBuffer) with false in Hp; cbv beta iota in Hp; destruct Hp as [-> ->] end.
    pose proof HA as (_ & _ & Hwf & _).
    pose proof HA as (_ & (_ & _ & _ & _ & Hnf & _) & _).
    forward_call (gv, Ews, ws_ck ws b', if b =? 0 then 2 ^ 17 else b).
    { split; [cbn [ws_ck ws_frames]; lia | destruct (b =? 0); rep_lia]. }
    forward_call (Int.repr (if blocks_within_b (ws_frames (ws_ck ws b')) (if b =? 0 then 2 ^ 17 else b) then 1 else 0)).
    match goal with Hp: Int.repr (if blocks_within_b _ _ then 1 else 0) <> Int.zero |- _ => rename Hp into Hbw end.
    assert (Hbw' : blocks_within_b (ws_frames ws) (if b =? 0 then 2 ^ 17 else b) = true).
    { destruct (blocks_within_b _ _); [reflexivity|]. exfalso. apply Hbw. reflexivity. }
    clear Hbw.
    Exists {| dp_fmt := 0; dp_ignore := 0; dp_bmax := b; dp_wmax := dp_wmax_dflt; dp_multi := 0 |} (2 ^ 27) 1.
    entailer!.
    destruct (Z.eq_dec b 0) as [->|Hb0].
    - apply VPB_dflt; auto; cbn; unfold dp_wmax_dflt; rep_lia.
    - rewrite (proj2 (Z.eqb_neq b 0) Hb0) in Hbw'. eapply VPB_m2; eauto; cbn; unfold ZSTD_BLOCKSIZE_MAX; lia. }
  { (* mode 3 *)
    assert (mode = 3) by (pose proof (proj1 HA); assert (mode <> 1) by (intro; subst; auto);
                          assert (mode <> 2) by (intro; subst; auto); lia). subst mode.
    forward_call 2. Intros c.
    forward_if (EX r: Z, EX st': dctx_st,
      PROP (r = 0 /\ st' = set_par dctx_init
              {| dp_fmt := 1; dp_ignore := 0; dp_bmax := 0; dp_wmax := dp_wmax_dflt; dp_multi := 0 |})
      LOCAL (temp _x_valid_params__t'26 (Vlong (Int64.repr r)); temp _mode (Vint (Int.repr 3));
             temp _wlim (Vlong (Int64.repr (2 ^ 27))); temp _base (Vlong (Int64.repr (vp_base 3)));
             temp _documented (Vint (Int.repr 1)); temp _n (Vlong (Int64.repr (Zlength (vp_src 3 b'))));
             temp _src src; temp _dctx dctx; lvar _zfh t_fh vz; lvar _in tin vi; lvar _out tout vo; gvars gv)
      SEP (mem_mgr gv; zstd_globals gv; DC gv dctx st'; WG gv;
           data_at Ews t_wseries (wseries_val (ws_ck ws b')) (gv _x_valid_params__sr);
           malloc_token Ews (tarray tuchar (Zlength (vp_src 3 b'))) src;
           data_at Ews (tarray tuchar (Zlength (vp_src 3 b'))) (zbytes (vp_src 3 b')) src; data_at_ Tsh t_fh vz;
           data_at_ Tsh tin vi; data_at_ Tsh tout vo; TT; has_ext tt)).
    { forward_call (gv, dctx, dctx_init, 1000, 1).
      { cbv; tauto. }
      Intros vret. destruct vret as [r st']. cbn [fst snd] in *.
 match goal with Hp: after_stage _ _ _ _ |- _ =>
   apply after_stage_init in Hp; [unfold setpar_res in Hp | reflexivity] end.
      match goal with Hp: context [param_set] |- _ =>
        cbv - [set_par dctx_init is_error_code] in Hp; destruct Hp as [-> ->] end.
      forward.
      Exists 0 (set_par dctx_init
        {| dp_fmt := 1; dp_ignore := 0; dp_bmax := 0; dp_wmax := dp_wmax_dflt; dp_multi := 0 |}).
      entailer!. apply derives_refl. }
    { forward_call (gv, dctx, dctx_init, 1).
      Intros vret. destruct vret as [r st']. cbn [fst snd] in *.
      match goal with Hp: context [param_set] |- _ =>
        cbv - [set_par dctx_init is_error_code] in Hp; destruct Hp as [-> ->] end.
      forward.
      Exists 0 (set_par dctx_init
        {| dp_fmt := 1; dp_ignore := 0; dp_bmax := 0; dp_wmax := dp_wmax_dflt; dp_multi := 0 |}).
      entailer!. apply derives_refl. }
    Intros r st'. subst r st'.
    forward.
    Exists {| dp_fmt := 1; dp_ignore := 0; dp_bmax := 0; dp_wmax := dp_wmax_dflt; dp_multi := 0 |} (2 ^ 27) 1.
    entailer!. apply VPB_m3; auto. }
  Intros p wlim doc.
  unfold POSTCONDITION, abbreviate.
  apply (VPB_tail gv vz vi vo mode ws b' p wlim doc src dctx); auto.
Qed.

End Seg.
