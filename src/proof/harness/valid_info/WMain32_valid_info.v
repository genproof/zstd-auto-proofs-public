(* main of harness/valid_info.c against API v3.2: a copy of WMain_valid_info.v (v2 proof) adapted to getFrameHeader's
   v3.2 FH_err post (dec_err r /\ r = fh_err_code_m false s). *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.harness.valid_info.WTopSpecs_valid_info.
Require Import Zstd.proof.harness.valid_info.VIModel Zstd.proof.harness.valid_info.VIVst Zstd.proof.harness.valid_info.VIAux.
Require Zstd.proof.top.MainPre6.

Local Notation ZCS := Zstd.proof.zstd.Base.CompSpecs.
Local Notation HCS := Zstd.proof.harness.valid_info.HOK_valid_info.CompSpecs.

(* ---------- main's precondition: the decoder's tables, the writer's statics, sr, wd ---------- *)

Lemma VI_filter_filter {A: Type} (f g: A -> bool) l :
  filter f (filter g l) = filter (fun x => andb (g x) (f x)) l.
Proof.
  induction l as [|a l IH]; simpl; auto.
  destruct (g a); simpl; [destruct (f a); simpl; rewrite IH; auto | exact IH].
Qed.

Lemma VI_wvar_not_zstd : forallb (fun i => negb (id_in_list i MainPre6.zstd_var_ids)) wvar_ids = true.
Proof. vm_compute. reflexivity. Qed.

Lemma VI_wvardefs :
  filter (fun ig => id_in_list (fst ig) wvar_ids)
    (filter (fun ig => negb (id_in_list (fst ig) MainPre6.zstd_var_ids)) (Vardefs Zstd.contracts.x_valid_info.whole_prog))
  = wvardefs.
Proof.
  rewrite VI_filter_filter. unfold wvardefs. apply filter_ext. intros [i g]; cbn [fst].
  destruct (id_in_list i wvar_ids) eqn:E; [|apply andb_false_r].
  rewrite andb_true_r.
  pose proof VI_wvar_not_zstd as H. rewrite forallb_forall in H.
  apply id_in_list_true in E. exact (H i E).
Qed.

Lemma VI_InitGPred_in x l gv : In x l -> InitGPred l gv |-- globs2pred gv x * TT.
Proof.
  intros Hin. apply in_split in Hin as [l1 [l2 ->]].
  rewrite InitGPred_middleD. rewrite sepcon_assoc. apply sepcon_derives; [apply derives_refl | apply TT_right].
Qed.

Definition VI_rest : list (ident * globdef (fundef function) type) :=
  filter (fun ig => negb (id_in_list (fst ig) wvar_ids))
    (filter (fun ig => negb (id_in_list (fst ig) MainPre6.zstd_var_ids)) (Vardefs Zstd.contracts.x_valid_info.whole_prog)).

Lemma VI_in_rest i v : Maps.PTree.get i (QP.prog_defs Zstd.contracts.x_valid_info.whole_prog) = Some (Gvar v) ->
  id_in_list i wvar_ids = false -> id_in_list i MainPre6.zstd_var_ids = false ->
  In (i, Gvar v) VI_rest.
Proof.
  intros Hg H1 H2. unfold VI_rest. rewrite !filter_In. split; [split|].
  - unfold Vardefs. apply filter_In. split; [|reflexivity].
    apply Maps.PTree.elements_correct. exact Hg.
  - cbn [fst]. rewrite H2. reflexivity.
  - cbn [fst]. rewrite H1. reflexivity.
Qed.

Lemma VI_sr_zero gv :
  globs2pred gv (_x_valid_info__sr, Gvar v_x_valid_info__sr) |-- data_at Ews t_wseries (zero_val t_wseries) (gv _x_valid_info__sr).
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

Lemma VI_wd_zero gv :
  globs2pred gv (_x_valid_info__wd, Gvar v_x_valid_info__wd) |-- data_at Ews t_wdict (zero_val t_wdict) (gv _x_valid_info__wd).
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

Lemma VI_rest_split gv :
  InitGPred VI_rest gv |--
  data_at Ews t_wseries (zero_val t_wseries) (gv _x_valid_info__sr) *
  (data_at Ews t_wdict (zero_val t_wdict) (gv _x_valid_info__wd) * TT).
Proof.
  rewrite (MainPre6.MP_InitGPred_filter (fun ig => Pos.eqb (fst ig) _x_valid_info__sr)).
  eapply derives_trans; [apply sepcon_derives |].
  - eapply derives_trans; [apply (VI_InitGPred_in (_x_valid_info__sr, Gvar v_x_valid_info__sr)) |].
    + apply filter_In. split; [apply VI_in_rest; reflexivity | reflexivity].
    + apply sepcon_derives; [apply VI_sr_zero | apply derives_refl].
  - eapply derives_trans; [apply (VI_InitGPred_in (_x_valid_info__wd, Gvar v_x_valid_info__wd)) |].
    + apply filter_In. split; [apply VI_in_rest; reflexivity | reflexivity].
    + apply sepcon_derives; [apply VI_wd_zero | apply derives_refl].
  - cancel.
Qed.

Lemma VI_pre (WG: globals -> mpred) (HWG: forall gv, InitGPred wvardefs gv |-- WG gv) gv :
  globals_ok gv ->
  InitGPred (Vardefs Zstd.contracts.x_valid_info.whole_prog) gv |--
  zstd_globals gv * (WG gv * (data_at Ews t_wseries (zero_val t_wseries) (gv _x_valid_info__sr) *
    (data_at Ews t_wdict (zero_val t_wdict) (gv _x_valid_info__wd) * TT))).
Proof.
  intros Hgv. eapply derives_trans.
  - apply (MainPre6.main_pre_fact6 Zstd.contracts.x_valid_info.whole_prog); [|exact Hgv].
    unfold MainPre6.all_progs. do 10 right; left; reflexivity.
  - apply sepcon_derives; [apply derives_refl|].
    rewrite (MainPre6.MP_InitGPred_filter (fun ig => id_in_list (fst ig) wvar_ids)).
    rewrite VI_wvardefs. apply sepcon_derives; [apply HWG|].
    cbv beta. match goal with |- InitGPred ?L _ |-- _ => replace L with VI_rest by (unfold VI_rest; reflexivity) end.
    apply VI_rest_split.
Qed.

(* ---------- compspecs: the API's (decoder) and main's (this unit) ---------- *)

Definition VI_cce (cs1 cs2: compspecs) : change_composite_env cs1 cs2 :=
  {| coeq := cs_preserve_env cs1 cs2;
     coeq_consistent := cs_preserve_env_consistent cs1 cs2 _ eq_refl;
     coeq_complete := cs_preserve_completeness cs1 cs2 _ eq_refl |}.

Lemma VI_arr: forall sh n (v: list val) p,
  @data_at ZCS sh (tarray tuchar n) v p = @data_at HCS sh (tarray tuchar n) v p.
Proof.
  intros. pose proof (@data_at_change_composite ZCS HCS (VI_cce ZCS HCS) sh (tarray tuchar n) v v
    (JMeq_refl _) ltac:(reflexivity)) as E. rewrite E; reflexivity.
Qed.

Lemma VI_arr_: forall sh n p,
  @data_at_ ZCS sh (tarray tuchar n) p = @data_at_ HCS sh (tarray tuchar n) p.
Proof.
  intros. pose proof (@data_at__change_composite ZCS HCS (VI_cce ZCS HCS) sh (tarray tuchar n)
    ltac:(reflexivity)) as E. rewrite E; reflexivity.
Qed.

Lemma VI_uint sh v p : @data_at ZCS sh tuint v p = @data_at HCS sh tuint v p.
Proof.
  pose proof (@data_at_change_composite ZCS HCS (VI_cce ZCS HCS) sh tuint v v (JMeq_refl _) ltac:(reflexivity)) as E.
  rewrite E; reflexivity.
Qed.

Lemma VI_uint_ sh p : @data_at_ ZCS sh tuint p = @data_at_ HCS sh tuint p.
Proof.
  pose proof (@data_at__change_composite ZCS HCS (VI_cce ZCS HCS) sh tuint ltac:(reflexivity)) as E.
  rewrite E; reflexivity.
Qed.

Lemma VI_fh_pres : cs_preserve_type ZCS HCS (@coeq _ _ (VI_cce ZCS HCS)) t_fh = true.
Proof. vm_compute. reflexivity. Qed.

Lemma VI_fh_ sh p : @data_at_ ZCS sh t_fh p = @data_at_ HCS sh t_fh p.
Proof.
  pose proof (@data_at__change_composite ZCS HCS (VI_cce ZCS HCS) sh t_fh VI_fh_pres) as E. rewrite E; reflexivity.
Qed.

Lemma VI_fh sh (v: @reptype ZCS t_fh) p : @data_at ZCS sh t_fh v p = @data_at HCS sh t_fh v p.
Proof.
  pose proof (@data_at_change_composite ZCS HCS (VI_cce ZCS HCS) sh t_fh v v (JMeq_refl _) VI_fh_pres) as E.
  rewrite E; reflexivity.
Qed.

Lemma VI_tyc_g_isSome: forall (V: varspecs) G i, In i (map fst V) ->
  isSome (Maps.PTree.get i (make_tycontext_g V G)).
Proof.
  intros. unfold make_tycontext_g. induction G as [|[j f] G IH]; simpl.
  - induction V as [|[k t] V IHV]; simpl in *; [contradiction|].
    rewrite Maps.PTree.gsspec. destruct (peq i k); simpl; auto.
    apply IHV. destruct H; [congruence|auto].
  - rewrite Maps.PTree.gsspec. destruct (peq i j); simpl; auto.
Qed.

(* ---------- tactics for main's loop body ---------- *)

Ltac vi_rm i L :=
  lazymatch L with
  | nil => constr:(@nil localdef)
  | temp i _ :: ?L' => vi_rm i L'
  | ?x :: ?L' => let r := vi_rm i L' in constr:(x :: r)
  end.

(* an if followed by code: join with the temp i set to v *)
Ltac vi_join i v :=
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
    let L' := vi_rm i L in forward_if (PROPx P (LOCALx (temp i v :: L') (SEPx R))) end.

Ltac vi_join2 i v j w :=
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
    let L' := vi_rm i L in let L'' := vi_rm j L' in
    forward_if (PROPx P (LOCALx (temp i v :: temp j w :: L'') (SEPx R))) end.

Ltac vi_join0 :=
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ => forward_if (PROPx P (LOCALx L (SEPx R))) end.

(* the boolean behind an if's condition *)
Ltac vi_b :=
  repeat match goal with
  | H: Int.repr (if ?b then 1 else 0) = Int.zero |- _ =>
      destruct b eqn:?; [exfalso; apply Int.one_not_zero; exact H | clear H]
  | H: Int.repr (if ?b then 1 else 0) <> Int.zero |- _ =>
      destruct b eqn:?; [clear H | exfalso; apply H; reflexivity]
  end.

Ltac vi_dead :=
  first [ match goal with H: ?a <> ?a |- _ => contradiction (H eq_refl) end
        | match goal with H: Int.repr ?a = Int.zero |- _ =>
            apply (f_equal Int.unsigned) in H; rewrite Int.unsigned_repr in H by rep_lia; discriminate end
        | match goal with H: Int64.repr ?a = Int64.zero |- _ =>
            apply (f_equal Int64.unsigned) in H; rewrite Int64.unsigned_repr in H by rep_lia; discriminate end ].

(* ---------- the loop over the frames ---------- *)

Definition vi_body : statement :=
  ltac:(let b := eval cbv [f_main fn_body] in (fn_body f_main) in
        lazymatch b with context [Sloop ?body _] => exact body end).

Definition vi_inv (gv: globals) (ws: wseries) (cap: Z) (src dst v_v v_zfh: val) (k: Z) (out: list val) (vv: val)
  : environ -> mpred :=
  PROP (0 <= k <= Zlength (ws_frames ws))
  LOCAL (temp _k (Vint (Int.repr k));
         temp _bound (Vlong (Int64.repr (vi_bsum (sublist 0 k (ws_frames ws)))));
         temp _allfcs (vb (vi_allfcs (sublist 0 k (ws_frames ws))));
         temp _anybig (vb (vi_anybig (sublist 0 k (ws_frames ws))));
         temp _src src; temp _dst dst; temp _cap (Vlong (Int64.repr cap));
         lvar _v tuint v_v; lvar _zfh (Tstruct ___gp_ZSTD_FrameHeader noattr) v_zfh; gvars gv)
  SEP (mem_mgr gv; data_at Tsh tuint vv v_v; data_at_ Tsh (Tstruct ___gp_ZSTD_FrameHeader noattr) v_zfh;
       zstd_globals gv;
       field_at Ews t_wseries (DOT _n) (vl (Zlength (ws_bytes ws))) (gv _x_valid_info__sr);
       field_at Ews t_wseries (DOT _content_n) (vl (Zlength (ws_content ws))) (gv _x_valid_info__sr);
       @data_at HCS Ews (tarray t_winfo 4) (VI_frecs (ws_frames ws)) (field_address t_wseries (DOT _f) (gv _x_valid_info__sr));
       field_at Ews t_wseries (DOT _nframes) (vu (Zlength (ws_frames ws))) (gv _x_valid_info__sr);
       malloc_token Ews (tarray tuchar (Zlength (ws_bytes ws))) src;
       data_at Ews (tarray tuchar (Zlength (ws_bytes ws))) (zbytes (ws_bytes ws)) src;
       malloc_token Ews (tarray tuchar (Z.max 1 cap)) dst;
       data_at Ews (tarray tuchar cap) out dst;
       data_at_ Ews (tarray tuchar (Z.max 1 cap - cap)) (offset_val cap dst);
       TT; has_ext tt).

Definition vi_cont (gv: globals) (ws: wseries) (cap: Z) (src dst v_v v_zfh: val) (k: Z) (out: list val) (vv: val)
  : environ -> mpred :=
  PROP (0 <= k < Zlength (ws_frames ws))
  LOCAL (temp _k (Vint (Int.repr k));
         temp _bound (Vlong (Int64.repr (vi_bsum (sublist 0 (k + 1) (ws_frames ws)))));
         temp _allfcs (vb (vi_allfcs (sublist 0 (k + 1) (ws_frames ws))));
         temp _anybig (vb (vi_anybig (sublist 0 (k + 1) (ws_frames ws))));
         temp _src src; temp _dst dst; temp _cap (Vlong (Int64.repr cap));
         lvar _v tuint v_v; lvar _zfh (Tstruct ___gp_ZSTD_FrameHeader noattr) v_zfh; gvars gv)
  SEP (mem_mgr gv; data_at Tsh tuint vv v_v; data_at_ Tsh (Tstruct ___gp_ZSTD_FrameHeader noattr) v_zfh;
       zstd_globals gv;
       field_at Ews t_wseries (DOT _n) (vl (Zlength (ws_bytes ws))) (gv _x_valid_info__sr);
       field_at Ews t_wseries (DOT _content_n) (vl (Zlength (ws_content ws))) (gv _x_valid_info__sr);
       @data_at HCS Ews (tarray t_winfo 4) (VI_frecs (ws_frames ws)) (field_address t_wseries (DOT _f) (gv _x_valid_info__sr));
       field_at Ews t_wseries (DOT _nframes) (vu (Zlength (ws_frames ws))) (gv _x_valid_info__sr);
       malloc_token Ews (tarray tuchar (Zlength (ws_bytes ws))) src;
       data_at Ews (tarray tuchar (Zlength (ws_bytes ws))) (zbytes (ws_bytes ws)) src;
       malloc_token Ews (tarray tuchar (Z.max 1 cap)) dst;
       data_at Ews (tarray tuchar cap) out dst;
       data_at_ Ews (tarray tuchar (Z.max 1 cap - cap)) (offset_val cap dst);
       TT; has_ext tt).

Definition vi_brk (gv: globals) (ws: wseries) (cap: Z) (src dst v_v v_zfh: val) (out: list val) (vv: val)
  : environ -> mpred :=
  PROP ()
  LOCAL (temp _bound (Vlong (Int64.repr (vi_bsum (ws_frames ws))));
         temp _allfcs (vb (vi_allfcs (ws_frames ws)));
         temp _anybig (vb (vi_anybig (ws_frames ws)));
         temp _src src; temp _dst dst; temp _cap (Vlong (Int64.repr cap));
         lvar _v tuint v_v; lvar _zfh (Tstruct ___gp_ZSTD_FrameHeader noattr) v_zfh; gvars gv)
  SEP (mem_mgr gv; data_at Tsh tuint vv v_v; data_at_ Tsh (Tstruct ___gp_ZSTD_FrameHeader noattr) v_zfh;
       zstd_globals gv;
       field_at Ews t_wseries (DOT _n) (vl (Zlength (ws_bytes ws))) (gv _x_valid_info__sr);
       field_at Ews t_wseries (DOT _content_n) (vl (Zlength (ws_content ws))) (gv _x_valid_info__sr);
       malloc_token Ews (tarray tuchar (Zlength (ws_bytes ws))) src;
       data_at Ews (tarray tuchar (Zlength (ws_bytes ws))) (zbytes (ws_bytes ws)) src;
       malloc_token Ews (tarray tuchar (Z.max 1 cap)) dst;
       data_at Ews (tarray tuchar cap) out dst;
       data_at_ Ews (tarray tuchar (Z.max 1 cap - cap)) (offset_val cap dst);
       TT; has_ext tt).

(* The loop body is proved in parts (each with a small Qed): vi_head (loop test, the frame's
   record, p and rest) up to vi_mid, then one lemma per kind of frame from vi_mid on (vi_rest_skip, _big, _zstd); the skippable
   frame's tail from ZSTD_readSkippableFrame on is vi_skip_tail_ok, from vi_skpre. *)

Definition vi_rest : statement :=
  ltac:(let b := eval cbv [vi_body] in vi_body in
        lazymatch b with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ ?r))) => exact r end).

Definition vi_skip_tail : statement :=
  ltac:(let b := eval cbv [vi_body] in vi_body in
        lazymatch b with context [Sifthenelse _ (Ssequence (Sassign (Evar _v tuint) _) ?t) Sskip] => exact t end).

Definition vi_mid (gv: globals) (ws: wseries) (cap: Z) (src dst v_v v_zfh: val) (k: Z) (out: list val) (vv: val)
  : environ -> mpred :=
  let f := Znth k (ws_frames ws) in
  let s := skipn (Z.to_nat (wi_start f)) (ws_bytes ws) in
  PROP ()
  LOCAL (temp _rest (Vlong (Int64.repr (Zlength s)));
         temp _x_valid_info__t'88 (vl (wi_start f));
         temp _x_valid_info__t'87 (vl (Zlength (ws_bytes ws)));
         temp _p (offset_val (wi_start f) src);
         temp _x_valid_info__t'89 (vl (wi_start f));
         temp _f (offset_val (@sizeof HCS t_winfo * k) (field_address t_wseries (DOT _f) (gv _x_valid_info__sr)));
         temp _x_valid_info__t'90 (vu (Zlength (ws_frames ws)));
         temp _k (Vint (Int.repr k));
         temp _bound (Vlong (Int64.repr (vi_bsum (sublist 0 k (ws_frames ws)))));
         temp _allfcs (vb (vi_allfcs (sublist 0 k (ws_frames ws))));
         temp _anybig (vb (vi_anybig (sublist 0 k (ws_frames ws))));
         temp _src src; temp _dst dst; temp _cap (Vlong (Int64.repr cap));
         lvar _v tuint v_v; lvar _zfh (Tstruct ___gp_ZSTD_FrameHeader noattr) v_zfh; gvars gv)
  SEP (mem_mgr gv; data_at Tsh tuint vv v_v; data_at_ Tsh (Tstruct ___gp_ZSTD_FrameHeader noattr) v_zfh;
       zstd_globals gv;
       field_at Ews t_wseries (DOT _n) (vl (Zlength (ws_bytes ws))) (gv _x_valid_info__sr);
       field_at Ews t_wseries (DOT _content_n) (vl (Zlength (ws_content ws))) (gv _x_valid_info__sr);
       @data_at HCS Ews (tarray t_winfo k) (sublist 0 k (VI_frecs (ws_frames ws))) (field_address t_wseries (DOT _f) (gv _x_valid_info__sr));
       @data_at HCS Ews t_winfo (winfo_val f) (offset_val (@sizeof HCS t_winfo * k) (field_address t_wseries (DOT _f) (gv _x_valid_info__sr)));
       @data_at HCS Ews (tarray t_winfo (4 - (k + 1))) (sublist (k + 1) 4 (VI_frecs (ws_frames ws)))
         (offset_val (@sizeof HCS t_winfo * (k + 1)) (field_address t_wseries (DOT _f) (gv _x_valid_info__sr)));
       field_at Ews t_wseries (DOT _nframes) (vu (Zlength (ws_frames ws))) (gv _x_valid_info__sr);
       malloc_token Ews (tarray tuchar (Zlength (ws_bytes ws))) src;
       data_at Ews (tarray tuchar (wi_start f)) (zbytes (firstn (Z.to_nat (wi_start f)) (ws_bytes ws))) src;
       data_at Ews (tarray tuchar (Zlength s)) (zbytes s) (offset_val (wi_start f) src);
       malloc_token Ews (tarray tuchar (Z.max 1 cap)) dst;
       data_at Ews (tarray tuchar cap) out dst;
       data_at_ Ews (tarray tuchar (Z.max 1 cap - cap)) (offset_val cap dst);
       TT; has_ext tt).

Definition vi_skpre (gv: globals) (ws: wseries) (cap: Z) (src dst v_v v_zfh: val) (k: Z)
    (vfh: @reptype ZCS t_fh) : environ -> mpred :=
  let f := Znth k (ws_frames ws) in
  let s := skipn (Z.to_nat (wi_start f)) (ws_bytes ws) in
  PROP ()
  LOCAL (temp _anybig (Vint (Int.or (Int.repr (if vi_anybig (sublist 0 k (ws_frames ws)) then 1 else 0)) (Int.repr 0)));
         temp _rest (Vlong (Int64.repr (Zlength s)));
         temp _p (offset_val (wi_start f) src);
         temp _f (offset_val (@sizeof HCS t_winfo * k) (field_address t_wseries (DOT _f) (gv _x_valid_info__sr)));
         temp _k (Vint (Int.repr k));
         temp _bound (Vlong (Int64.repr (vi_bsum (sublist 0 k (ws_frames ws)))));
         temp _allfcs (vb (vi_allfcs (sublist 0 k (ws_frames ws))));
         temp _src src; temp _dst dst; temp _cap (Vlong (Int64.repr cap));
         lvar _v tuint v_v; lvar _zfh (Tstruct ___gp_ZSTD_FrameHeader noattr) v_zfh; gvars gv)
  SEP (@data_at_ ZCS Tsh tuint v_v; @data_at_ ZCS Ews (tarray tuchar cap) dst;
       zstd_globals gv;
       @data_at HCS Tsh t_fh vfh v_zfh;
       @data_at ZCS Ews (tarray tuchar (Zlength s)) (zbytes s) (offset_val (wi_start f) src); mem_mgr gv;
       field_at Ews t_wseries (DOT _n) (vl (Zlength (ws_bytes ws))) (gv _x_valid_info__sr);
       field_at Ews t_wseries (DOT _content_n) (vl (Zlength (ws_content ws))) (gv _x_valid_info__sr);
       @data_at HCS Ews (tarray t_winfo k) (sublist 0 k (VI_frecs (ws_frames ws))) (field_address t_wseries (DOT _f) (gv _x_valid_info__sr));
       @data_at HCS Ews (tarray t_winfo (4 - (k + 1))) (sublist (k + 1) 4 (VI_frecs (ws_frames ws)))
         (offset_val (@sizeof HCS t_winfo * (k + 1)) (field_address t_wseries (DOT _f) (gv _x_valid_info__sr)));
       field_at Ews t_wseries (DOT _nframes) (vu (Zlength (ws_frames ws))) (gv _x_valid_info__sr);
       malloc_token Ews (tarray tuchar (Zlength (ws_bytes ws))) src;
       data_at Ews (tarray tuchar (wi_start f)) (zbytes (firstn (Z.to_nat (wi_start f)) (ws_bytes ws))) src;
       malloc_token Ews (tarray tuchar (Z.max 1 cap)) dst;
       data_at_ Ews (tarray tuchar (Z.max 1 cap - cap)) (offset_val cap dst); TT;
       @data_at HCS Ews t_winfo
         (vb true, (vu (wi_variant f), (vl (wi_start f), (vl (wi_size f), (vl (wi_cstart f),
         (vl (wi_csize f), (vb (wi_fcs_present f), (vl (wi_fcs f), (vu (wi_did_size f), (vu (wi_did f),
         (vb (wi_single f), (vl (wi_window f), (vu (wi_window_log f), (vb (wi_checksum f), (vu (wi_blocks f),
         (vl (wi_skip_n f), (vl (wi_hsize f), vb (wi_uses_dict f))))))))))))))))))
         (offset_val (@sizeof HCS t_winfo * k) (field_address t_wseries (DOT _f) (gv _x_valid_info__sr)));
       has_ext tt).

Lemma vi_head DC DD WG WDS {Espec: OracleKind} (gv: globals) (ws: wseries) (dm: dict_model) (cap: Z)
    (src dst v_v v_zfh: val) (k: Z) (out: list val) (vv: val) :
  series_facts dm ws -> wseries_wf ws -> 0 <= cap <= 68 -> src <> nullval -> dst <> nullval -> isptr dst ->
  isptr src -> field_compatible (tarray tuchar (Z.max 1 cap)) [] dst ->
  (0 <= k < Zlength (ws_frames ws) -> isptr (field_address t_wseries (DOT _f) (gv _x_valid_info__sr)) ->
  field_compatible (tarray t_winfo 4) [] (field_address t_wseries (DOT _f) (gv _x_valid_info__sr)) ->
  field_compatible (tarray tuchar (Zlength (ws_bytes ws))) [] src ->
   semax (func_tycontext f_main Vprog (G0 (Specs_api DC DD) WG WDS) nil)
     (vi_mid gv ws cap src dst v_v v_zfh k out vv) vi_rest
    (normal_ret_assert (EX k: Z, EX out: list val, EX vv: val, vi_cont gv ws cap src dst v_v v_zfh k out vv)%assert)) ->
  semax (func_tycontext f_main Vprog (G0 (Specs_api DC DD) WG WDS) nil)
    (vi_inv gv ws cap src dst v_v v_zfh k out vv) vi_body
    (loop1_ret_assert (EX k: Z, EX out: list val, EX vv: val, vi_cont gv ws cap src dst v_v v_zfh k out vv)%assert
       (overridePost (EX out: list val, EX vv: val, vi_brk gv ws cap src dst v_v v_zfh out vv)%assert
          (frame_ret_assert (function_body_ret_assert tint (PROP () RETURN () SEP (TT))) (stackframe_of f_main)))).
Proof.
  intros HSF HWF H0 Hs0 Hd0 Hpd Hps Hfd HR.
  pose proof HSF as (Hsb & Hsc & Hsn & Hscn & Hnf & Ht & Hff & Hfcs & Hfds & Hbd).
  assert (Hnf': 1 <= Zlength (ws_frames ws) <= 4) by (rewrite Zlength_correct; lia).
  assert (Hn1: 1 <= Zlength (ws_bytes ws)).
  { destruct (vi_tiles_nth _ _ _ _ _ Ht 0%nat ltac:(lia)) as (A & B & C). lia. }
  unfold vi_inv, vi_cont, vi_brk, vi_body.
  abbreviate_semax.
  Intros.
    forward.
    match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
      forward_if (PROPx ((k < Zlength (ws_frames ws)) :: P) (LOCALx L (SEPx R))) end.
    { forward. entailer!. }
    { forward. assert (k = Zlength (ws_frames ws)) by lia. subst k.
      rewrite sublist_same by lia. Exists out vv. entailer!. }
    Intros.
    forward.
    assert_PROP (isptr (field_address t_wseries (DOT _f) (gv _x_valid_info__sr))) as Hfp by entailer!.
    match goal with |- context [temp _f ?v] =>
      replace v with (offset_val (@sizeof HCS t_winfo * k) (field_address t_wseries (DOT _f) (gv _x_valid_info__sr)))
        by (rewrite <- (VI_fptr (gv _x_valid_info__sr) k Hfp) by lia; reflexivity) end.
    destruct (VI_frame_k dm ws k HSF HWF ltac:(lia)) as (Hfk & Hwfk & Hzk & Hst0 & Hst1 & Hsz & Hfck).
    assert_PROP (field_compatible (tarray t_winfo 4) [] (field_address t_wseries (DOT _f) (gv _x_valid_info__sr))) as Hfa
      by entailer!.
    rewrite (@VI_elem_gen HCS Ews t_winfo 4 (VI_frecs (ws_frames ws)) _ k VI_winfo_aligned
      (VI_frecs_len (ws_frames ws) ltac:(lia)) ltac:(lia) Hfa).
    rewrite (VI_frecs_nth (ws_frames ws) k) by lia.
    Intros.
    unfold winfo_val.
    forward. forward. forward. forward. forward.
    set (f := Znth k (ws_frames ws)) in *.
    match goal with |- context [temp _p ?v] => replace v with (offset_val (wi_start f) src) end.
    2: { destruct src; try contradiction. simpl. unfold sem_add_ptr_long. simpl. f_equal. f_equal.
         unfold Ptrofs.of_int64. rewrite Int64.unsigned_repr by rep_lia.
         rewrite Ptrofs.mul_commut, Ptrofs.mul_one. reflexivity. }
    rewrite sub64_repr.
    assert_PROP (field_compatible (tarray tuchar (Zlength (ws_bytes ws))) [] src) as Hfs by entailer!.
    rewrite (VI_src_split Ews (ws_bytes ws) (wi_start f) src) by (auto; lia).
    rewrite <- (VI_len_skipn (ws_bytes ws) (wi_start f)) by lia.
    unfold frame_facts in Hfk. cbv zeta in Hfk.
    destruct Hfk as (Hisf & Hiss & Hfcsz & Hgfh & Hfcont & Hdid & Hfhs & Hskp & _).
    set (s := skipn (Z.to_nat (wi_start f)) (ws_bytes ws)) in *.
    assert (Hs: src_spec_pre Ews s).
    { split; [auto|]. split.
      - unfold s. rewrite VI_len_skipn by lia. lia.
      - apply VI_bytes_skipn; auto. }
    Intros.
    refine (HR _ Hfp Hfa Hfs). lia.
Qed.

Lemma vi_skip_tail_ok DC DD WG WDS {Espec: OracleKind} (gv: globals) (ws: wseries) (dm: dict_model) (cap: Z)
    (src dst v_v v_zfh: val) (k: Z) (vfh: @reptype ZCS t_fh) :
  wi_skippable (Znth k (ws_frames ws)) = true ->
  series_facts dm ws -> wseries_wf ws -> 0 <= cap <= 68 -> src <> nullval -> dst <> nullval -> isptr dst ->
  isptr src -> field_compatible (tarray tuchar (Z.max 1 cap)) [] dst ->
  0 <= k < Zlength (ws_frames ws) -> isptr (field_address t_wseries (DOT _f) (gv _x_valid_info__sr)) ->
  field_compatible (tarray t_winfo 4) [] (field_address t_wseries (DOT _f) (gv _x_valid_info__sr)) ->
  field_compatible (tarray tuchar (Zlength (ws_bytes ws))) [] src ->
  semax (func_tycontext f_main Vprog (G0 (Specs_api DC DD) WG WDS) nil)
    (vi_skpre gv ws cap src dst v_v v_zfh k vfh) vi_skip_tail
    (normal_ret_assert (EX k: Z, EX out: list val, EX vv: val, vi_cont gv ws cap src dst v_v v_zfh k out vv)%assert).
Proof.
  intros Esk HSF HWF H0 Hs0 Hd0 Hpd Hps Hfd H Hfp Hfa Hfs.
  pose proof HSF as (Hsb & Hsc & Hsn & Hscn & Hnf & Ht & Hff & Hfcs & Hfds & Hbd).
  assert (Hnf': 1 <= Zlength (ws_frames ws) <= 4) by (rewrite Zlength_correct; lia).
  assert (Hn1: 1 <= Zlength (ws_bytes ws)).
  { destruct (vi_tiles_nth _ _ _ _ _ Ht 0%nat ltac:(lia)) as (A & B & C). lia. }
  destruct (VI_frame_k dm ws k HSF HWF H) as (Hfk & Hwfk & Hzk & Hst0 & Hst1 & Hsz & Hfck).
  unfold vi_skpre, vi_skip_tail, vi_cont. cbv zeta.
  abbreviate_semax.
  set (f := Znth k (ws_frames ws)) in *.
  unfold frame_facts in Hfk. cbv zeta in Hfk.
  destruct Hfk as (Hisf & Hiss & Hfcsz & Hgfh & Hfcont & Hdid & Hfhs & Hskp & _).
  set (s := skipn (Z.to_nat (wi_start f)) (ws_bytes ws)) in *.
  assert (Hs: src_spec_pre Ews s).
  { split; [auto|]. split.
    - unfold s. rewrite VI_len_skipn by lia. lia.
    - apply VI_bytes_skipn; auto. }
  assert (Ebig: wi_big f = false) by (unfold wi_big; rewrite Esk; reflexivity).
  unfold t_fh.
  freeze [2;3;5;6;7;8;9;10;11;12;13;14;15] FR.
      forward_call (Ews, dst, cap, Tsh, v_v, Ews, offset_val (wi_start f) src, s).
      Intros vr. destruct vr as [[r3 out'] vv']. cbn [fst snd] in *.
      match goal with H: match read_skippable _ _ with _ => _ end |- _ => rename H into H8 end.
      destruct (Hskp Esk) as (Hsz8 & Hfbl & Hmag & Hsfs & Hrs).
      rewrite Hrs in *.
      destruct Hwfk as (Wvar & Wst & Wsz & Wcst & Wcsz & Wfcs & Wdsz & Wdid & Wwin & Wwl & Wbl & Wskn & Whs).
      unfold u64, u32 in Wvar, Wst, Wsz, Wcst, Wcsz, Wfcs, Wdsz, Wdid, Wwin, Wwl, Wbl, Wskn, Whs.
      forward.
      forward_if.
      { rewrite Z.geb_leb, (proj2 (Z.leb_le _ _)) in H8 by lia.
        destruct H8 as (Hr3 & Hout & Hvv). subst vv'.
        assert (Hfbl': Zlength (wi_bytes ws f) = wi_size f).
        { unfold wi_bytes. apply VI_slice_len; lia. }
        assert (Hu: Zlength (slice (wi_bytes ws f) ZSTD_SKIPPABLEHEADERSIZE (wi_skip_n f)) = wi_skip_n f).
        { apply VI_slice_len; unfold ZSTD_SKIPPABLEHEADERSIZE in *; lia. }
        rewrite Hu in Hr3. subst r3.
        rewrite (VI_arr Ews cap), (VI_arr Ews (Zlength s)), VI_uint.
        forward.
        forward_call (Int.repr 1).
        { entailer!. unfold vl. simpl. rewrite Int64.eq_true. reflexivity. }
        forward. forward.
        forward_call (Int.repr 1).
        { entailer!. unfold vu. simpl. rewrite Int.eq_true. reflexivity. }
        forward.
        match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
          let L' := vi_rm _i L in
          forward_loop (EX i: Z, PROPx ((0 <= i <= wi_skip_n f) :: P)
              (LOCALx (temp _i (Vlong (Int64.repr i)) :: L') (SEPx R)))%assert
            continue: (EX i: Z, PROPx ((0 <= i < wi_skip_n f) :: P)
              (LOCALx (temp _i (Vlong (Int64.repr i)) :: L') (SEPx R)))%assert
            break: (PROPx P (LOCALx L' (SEPx R)))
        end.
        { Exists 0. entailer!. }
        { Intros i.
          match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
            forward_if (PROPx ((i < wi_skip_n f) :: P) (LOCALx L (SEPx R))) end.
          { forward. entailer!. }
          { forward. entailer!. }
          Intros.
          assert (Hbyte: Znth i (slice (wi_bytes ws f) ZSTD_SKIPPABLEHEADERSIZE (wi_skip_n f)) = Znth (8 + i) s).
          { unfold wi_bytes, s.
            replace (wi_skip_n f) with (wi_size f - 8) by (unfold ZSTD_SKIPPABLEHEADERSIZE in Hsz8; lia).
            apply VI_skip_byte; unfold ZSTD_SKIPPABLEHEADERSIZE in *; lia. }
          assert (Hls: wi_size f <= Zlength s) by (unfold s; rewrite VI_len_skipn by lia; lia).
          assert (Hdi: Znth i out' = Vint (Int.repr (Znth (8 + i) s))).
          { rewrite <- Hbyte. replace (Znth i out') with (Znth i (sublist 0 (wi_skip_n f) out'))
              by (rewrite Znth_sublist, Z.add_0_r by lia; reflexivity).
            rewrite Hout, Znth_map by lia. reflexivity. }
          assert (Hix: 0 <= 8 + i < Zlength s) by (unfold ZSTD_SKIPPABLEHEADERSIZE in *; lia).
          assert (Hbr: 0 <= Znth (8 + i) s < 256).
          { destruct Hs as (_ & _ & Hbs). unfold bytes_ok in Hbs. rewrite Forall_Znth in Hbs. apply Hbs. lia. }
          forward.
          { entailer!. match goal with |- context [@Znth ?A ?I i out'] =>
              replace (@Znth A I i out') with (Vint (Int.repr (Znth (8 + i) s))) by (rewrite <- Hdi; reflexivity) end.
            simpl. try rewrite Int.unsigned_repr by rep_lia. rep_lia. }
          forward.
          { entailer!. simpl. try rewrite Int.unsigned_repr by rep_lia. rep_lia. }
          match goal with |- context [@Znth ?A ?I i out'] =>
            replace (@Znth A I i out') with (Vint (Int.repr (Znth (8 + i) s))) by (rewrite <- Hdi; reflexivity) end.
          forward_call (Int.repr 1).
          { entailer!. simpl. rewrite Int.eq_true. reflexivity. }
          Exists i. entailer!. }
        { Intros i. forward. Exists (i + 1). entailer!. }
        thaw FR.
        Exists k out' (Vint (Int.repr (wi_variant f))).
        rewrite (@VI_elem_gen HCS Ews t_winfo 4 (VI_frecs (ws_frames ws)) _ k VI_winfo_aligned
          (VI_frecs_len (ws_frames ws) ltac:(lia)) ltac:(lia) Hfa).
        rewrite (VI_frecs_nth (ws_frames ws) k) by lia.
        rewrite (VI_src_split Ews (ws_bytes ws) (wi_start f) src) by (auto; lia).
        rewrite VI_bsum_S, VI_allfcs_S, VI_anybig_S by lia.
        change (Znth k (ws_frames ws)) with f.
        unfold winfo_val.
        rewrite Esk, Ebig.
        unfold vi_bterm. rewrite Esk.
        rewrite Z.add_0_r, Bool.orb_false_r, Bool.andb_true_r.
        go_lower. apply andp_right.
        { apply prop_right. rewrite !eqb_type_refl.
          destruct (vi_anybig (sublist 0 k (ws_frames ws))); repeat split; auto; lia. }
        sep_apply (@data_at_data_at_ HCS Tsh (Tstruct ___gp_ZSTD_FrameHeader noattr)).
        cancel. }
      { rewrite Z.geb_leb, (proj2 (Z.leb_gt _ _)) in H8 by lia.
        forward_call r3.
        forward_call (Int.repr 1).
        { entailer!. rewrite H8. reflexivity. }
        rewrite (VI_arr Ews cap), (VI_arr Ews (Zlength s)), VI_uint.
        thaw FR.
        Exists k out' vv'.
        rewrite (@VI_elem_gen HCS Ews t_winfo 4 (VI_frecs (ws_frames ws)) _ k VI_winfo_aligned
          (VI_frecs_len (ws_frames ws) ltac:(lia)) ltac:(lia) Hfa).
        rewrite (VI_frecs_nth (ws_frames ws) k) by lia.
        rewrite (VI_src_split Ews (ws_bytes ws) (wi_start f) src) by (auto; lia).
        rewrite VI_bsum_S, VI_allfcs_S, VI_anybig_S by lia.
        change (Znth k (ws_frames ws)) with f.
        unfold winfo_val.
        rewrite Esk, Ebig.
        unfold vi_bterm. rewrite Esk.
        rewrite Z.add_0_r, Bool.orb_false_r, Bool.andb_true_r.
        go_lower. apply andp_right.
        { apply prop_right. rewrite !eqb_type_refl.
          destruct (vi_anybig (sublist 0 k (ws_frames ws))); repeat split; auto; lia. }
        sep_apply (@data_at_data_at_ HCS Tsh (Tstruct ___gp_ZSTD_FrameHeader noattr)).
        cancel. }
Qed.

Lemma vi_rest_skip DC DD WG WDS {Espec: OracleKind} (gv: globals) (ws: wseries) (dm: dict_model) (cap: Z)
    (src dst v_v v_zfh: val) (k: Z) (out: list val) (vv: val) :
  wi_skippable (Znth k (ws_frames ws)) = true ->
  series_facts dm ws -> wseries_wf ws -> 0 <= cap <= 68 -> src <> nullval -> dst <> nullval -> isptr dst ->
  isptr src -> field_compatible (tarray tuchar (Z.max 1 cap)) [] dst ->
  0 <= k < Zlength (ws_frames ws) -> isptr (field_address t_wseries (DOT _f) (gv _x_valid_info__sr)) ->
  field_compatible (tarray t_winfo 4) [] (field_address t_wseries (DOT _f) (gv _x_valid_info__sr)) ->
  field_compatible (tarray tuchar (Zlength (ws_bytes ws))) [] src ->
  semax (func_tycontext f_main Vprog (G0 (Specs_api DC DD) WG WDS) nil)
    (vi_mid gv ws cap src dst v_v v_zfh k out vv) vi_rest
    (normal_ret_assert (EX k: Z, EX out: list val, EX vv: val, vi_cont gv ws cap src dst v_v v_zfh k out vv)%assert).
Proof.
  intros Hkind HSF HWF H0 Hs0 Hd0 Hpd Hps Hfd H Hfp Hfa Hfs.
  pose proof HSF as (Hsb & Hsc & Hsn & Hscn & Hnf & Ht & Hff & Hfcs & Hfds & Hbd).
  assert (Hnf': 1 <= Zlength (ws_frames ws) <= 4) by (rewrite Zlength_correct; lia).
  assert (Hn1: 1 <= Zlength (ws_bytes ws)).
  { destruct (vi_tiles_nth _ _ _ _ _ Ht 0%nat ltac:(lia)) as (A & B & C). lia. }
  destruct (VI_frame_k dm ws k HSF HWF H) as (Hfk & Hwfk & Hzk & Hst0 & Hst1 & Hsz & Hfck).
  unfold vi_mid, vi_rest, vi_cont. cbv zeta.
  abbreviate_semax.
  set (f := Znth k (ws_frames ws)) in *.
  unfold frame_facts in Hfk. cbv zeta in Hfk.
  destruct Hfk as (Hisf & Hiss & Hfcsz & Hgfh & Hfcont & Hdid & Hfhs & Hskp & _).
  set (s := skipn (Z.to_nat (wi_start f)) (ws_bytes ws)) in *.
  assert (Hs: src_spec_pre Ews s).
  { split; [auto|]. split.
    - unfold s. rewrite VI_len_skipn by lia. lia.
    - apply VI_bytes_skipn; auto. }
  unfold winfo_val.
  freeze [0;1;4;5;6;8;9;10;11;13;14;15;16] FR.
    destruct (wi_skippable f) eqn:Esk.
    { (* a skippable frame *)
      assert (Ebig: wi_big f = false) by (unfold wi_big; rewrite Esk; reflexivity).
      rewrite Ebig in *.
      forward.
      vi_join _x_valid_info__t'9 (Vint (Int.repr 0)).
      all: try solve [vi_dead | forward; entailer!].
      vi_join _x_valid_info__t'10 (Vint (Int.repr 0)).
      all: try solve [vi_dead | forward; entailer!].
      forward. forward. forward.
      vi_join0.
      all: try solve [vi_dead | forward; entailer!].
      cbv beta iota in Hiss, Hfcsz, Hgfh, Hfcont, Hdid.
      rewrite <- (VI_arr Ews (Zlength s)).
      forward_call (gv, Ews, offset_val (wi_start f) src, s).
      Intros r1.
      rewrite Hfcsz in *. cbv beta iota in *. subst r1.
      forward.
      vi_join _x_valid_info__t'14 (Vint (Int.repr 1)).
      all: try solve [vi_dead | forward; entailer!].
      forward_call (Int.repr 1).
      try deadvars!.
      forward_call (gv, Ews, offset_val (wi_start f) src, s).
      rewrite Hfcont.
      forward.
      vi_join0.
      all: try solve [vi_dead | forward_call (Int.repr 1); entailer!].
      forward_call (gv, Ews, offset_val (wi_start f) src, s).
      rewrite Hdid.
      forward.
      vi_join _x_valid_info__t'20 (Vint (Int.repr 0)).
      all: try solve [vi_dead | forward; entailer!].
      vi_join _x_valid_info__t'21 (Vint (Int.repr 1)).
      all: try solve [vi_dead | forward; entailer!].
      forward_call (Int.repr 1).
      try deadvars!.
      forward_call (Ews, offset_val (wi_start f) src, s).
      rewrite Hisf.
      forward_call (Int.repr 1).
      try deadvars!.
      forward_call (Ews, offset_val (wi_start f) src, s).
      rewrite Hiss.
      forward.
      forward_call (Int.repr 1).
      try deadvars!.
      replace (@data_at_ HCS Tsh (Tstruct ___gp_ZSTD_FrameHeader noattr) v_zfh) with (@data_at_ ZCS Tsh t_fh v_zfh)
        by (rewrite VI_fh_; reflexivity).
      change (@data_at_ ZCS Tsh t_fh v_zfh) with (@data_at ZCS Tsh t_fh (@default_val ZCS t_fh) v_zfh).
      forward_call (gv, Tsh, v_zfh, @default_val ZCS t_fh, Ews, offset_val (wi_start f) src, s).
      Intros vr. destruct vr as [r2 vfh]. cbn [fst snd] in *.
      match goal with H: fh_post _ _ _ _ |- _ => unfold fh_post in H; rewrite Hgfh in H; destruct H as [-> ->] end.
      rewrite VI_fh. unfold t_fh.
      unfold fh_val, wi_header. rewrite Esk.
      cbn [fh_contentSize fh_windowSize fh_blockSizeMax fh_frameType fh_headerSize fh_dictID fh_checksumFlag].
      vi_join _x_valid_info__t'25 (Vint (Int.repr 1)).
      all: try solve [vi_dead | forward; entailer!].
      forward_call (Int.repr 1).
      try deadvars!.
      vi_join _x_valid_info__t'29 (Vint (Int.repr 1)).
      all: try solve [vi_dead | forward; forward; entailer!].
      vi_join0.
      { forward.
        forward_call (Int.repr 1).
        try deadvars!.
        forward. forward.
        forward_call (Int.repr 1).
        { entailer!. unfold vl. simpl. rewrite Int64.eq_true. reflexivity. }
        forward. forward.
        forward_call (Int.repr 1).
        { entailer!. unfold vu. simpl. rewrite Int.eq_true. reflexivity. }
        entailer!. }
      { exfalso; apply Int.one_not_zero; assumption. }
      forward.
      vi_join0.
      all: try solve [vi_dead | forward; entailer!].
      forward.
      forward_if.
      2: { exfalso; apply Int.one_not_zero; assumption. }
      thaw FR.
      forward.
      sep_apply (data_at_data_at_ Ews (tarray tuchar cap) out dst).
      rewrite <- (VI_arr_ Ews cap dst).
      sep_apply (data_at_data_at_ Tsh tuint (Vint (Int.repr 0)) v_v).
      rewrite <- VI_uint_.
      deadvars!.
      exact (vi_skip_tail_ok DC DD WG WDS gv ws dm cap src dst v_v v_zfh k _ Esk HSF HWF H0 Hs0 Hd0 Hpd Hps Hfd
        H Hfp Hfa Hfs). }
    exfalso; congruence.
Qed.

Lemma vi_rest_big DC DD WG WDS {Espec: OracleKind} (gv: globals) (ws: wseries) (dm: dict_model) (cap: Z)
    (src dst v_v v_zfh: val) (k: Z) (out: list val) (vv: val) :
  wi_skippable (Znth k (ws_frames ws)) = false /\ wi_big (Znth k (ws_frames ws)) = true ->
  series_facts dm ws -> wseries_wf ws -> 0 <= cap <= 68 -> src <> nullval -> dst <> nullval -> isptr dst ->
  isptr src -> field_compatible (tarray tuchar (Z.max 1 cap)) [] dst ->
  0 <= k < Zlength (ws_frames ws) -> isptr (field_address t_wseries (DOT _f) (gv _x_valid_info__sr)) ->
  field_compatible (tarray t_winfo 4) [] (field_address t_wseries (DOT _f) (gv _x_valid_info__sr)) ->
  field_compatible (tarray tuchar (Zlength (ws_bytes ws))) [] src ->
  semax (func_tycontext f_main Vprog (G0 (Specs_api DC DD) WG WDS) nil)
    (vi_mid gv ws cap src dst v_v v_zfh k out vv) vi_rest
    (normal_ret_assert (EX k: Z, EX out: list val, EX vv: val, vi_cont gv ws cap src dst v_v v_zfh k out vv)%assert).
Proof.
  intros Hkind HSF HWF H0 Hs0 Hd0 Hpd Hps Hfd H Hfp Hfa Hfs.
  pose proof HSF as (Hsb & Hsc & Hsn & Hscn & Hnf & Ht & Hff & Hfcs & Hfds & Hbd).
  assert (Hnf': 1 <= Zlength (ws_frames ws) <= 4) by (rewrite Zlength_correct; lia).
  assert (Hn1: 1 <= Zlength (ws_bytes ws)).
  { destruct (vi_tiles_nth _ _ _ _ _ Ht 0%nat ltac:(lia)) as (A & B & C). lia. }
  destruct (VI_frame_k dm ws k HSF HWF H) as (Hfk & Hwfk & Hzk & Hst0 & Hst1 & Hsz & Hfck).
  unfold vi_mid, vi_rest, vi_cont. cbv zeta.
  abbreviate_semax.
  set (f := Znth k (ws_frames ws)) in *.
  unfold frame_facts in Hfk. cbv zeta in Hfk.
  destruct Hfk as (Hisf & Hiss & Hfcsz & Hgfh & Hfcont & Hdid & Hfhs & Hskp & _).
  set (s := skipn (Z.to_nat (wi_start f)) (ws_bytes ws)) in *.
  assert (Hs: src_spec_pre Ews s).
  { split; [auto|]. split.
    - unfold s. rewrite VI_len_skipn by lia. lia.
    - apply VI_bytes_skipn; auto. }
  unfold winfo_val.
  freeze [0;1;4;5;6;8;9;10;11;13;14;15;16] FR.
    destruct (wi_skippable f) eqn:Esk.
    { exfalso; destruct Hkind; congruence. }
    (* a Zstandard frame *)
    assert (Hzk' := Hzk). unfold winfo_zeros in Hzk'. rewrite Esk in Hzk'. destruct Hzk' as (Hvar0 & Hskn0).
    destruct Hwfk as (Wvar & Wst & Wsz & Wcst & Wcsz & Wfcs & Wdsz & Wdid & Wwin & Wwl & Wbl & Wskn & Whs).
    unfold u64, u32 in Wvar, Wst, Wsz, Wcst, Wcsz, Wfcs, Wdsz, Wdid, Wwin, Wwl, Wbl, Wskn, Whs.
    forward.
    vi_join _x_valid_info__t'9 (vb (negb (wi_single f))).
    { forward. forward. entailer!. destruct (wi_single f); reflexivity. }
    { exfalso; match goal with H: _ <> Int.zero |- _ => apply H; reflexivity end. }
    vi_join _x_valid_info__t'10 (vb (wi_big f)).
    { match goal with H: Int.repr (if negb (wi_single f) then 1 else 0) <> Int.zero |- _ =>
        assert (Esg: wi_single f = false) by (destruct (wi_single f); [contradiction H; reflexivity | reflexivity]) end.
      vi_join _x_valid_info__t'11 (Vint (Int.repr 31)).
      all: try solve [vi_dead | match goal with H: Int64.eq _ _ = true |- _ => vm_compute in H; discriminate end
                     | forward; entailer!].
      forward. forward. entailer!.
      unfold wi_big, ZSTD_WINDOWLOG_MAX. rewrite Esk, Esg. cbn [negb andb]. rewrite Z.gtb_ltb.
      destruct (zlt 31 (wi_window_log f));
        [rewrite (proj2 (Z.ltb_lt _ _)) by lia | rewrite (proj2 (Z.ltb_ge _ _)) by lia]; reflexivity. }
    { match goal with H: Int.repr (if negb (wi_single f) then 1 else 0) = Int.zero |- _ =>
        assert (Esg: wi_single f = true)
          by (destruct (wi_single f); [reflexivity | exfalso; apply Int.one_not_zero; exact H]) end.
      forward. entailer!. unfold wi_big. rewrite Esk, Esg. reflexivity. }
    forward. forward. forward.
    vi_join2 _bound (Vlong (Int64.repr (vi_bsum (sublist 0 k (ws_frames ws)) + vi_bterm f)))
      _allfcs (vb (vi_allfcs (sublist 0 k (ws_frames ws)) && (wi_skippable f || wi_fcs_present f))).
    { forward.
      forward_if.
      { match goal with H: Int.repr (if wi_fcs_present f then 1 else 0) <> Int.zero |- _ =>
          assert (Efp: wi_fcs_present f = true)
            by (destruct (wi_fcs_present f); [reflexivity | contradiction H; reflexivity]) end.
        forward. forward. entailer!. unfold vi_bterm. rewrite Esk, Efp.
        split; [reflexivity | destruct (vi_allfcs _); reflexivity]. }
      match goal with H: Int.repr (if wi_fcs_present f then 1 else 0) = Int.zero |- _ =>
        assert (Efp: wi_fcs_present f = false)
          by (destruct (wi_fcs_present f); [exfalso; apply Int.one_not_zero; exact H | reflexivity]) end.
      forward.
      vi_join _x_valid_info__t'12 (Vlong (Int64.repr (Z.min (wi_window f) ZSTD_BLOCKSIZE_MAX))).
      { match goal with H: Int64.unsigned _ < Int64.unsigned (Int64.shl _ _) |- _ =>
          change (Int64.shl (Int64.repr 1) (Int64.repr 17)) with (Int64.repr 131072) in H;
          rewrite !Int64.unsigned_repr in H by rep_lia end.
        forward. forward. entailer!. rewrite Z.min_l by (unfold ZSTD_BLOCKSIZE_MAX; lia). reflexivity. }
      { match goal with H: Int64.unsigned _ >= Int64.unsigned (Int64.shl _ _) |- _ =>
          change (Int64.shl (Int64.repr 1) (Int64.repr 17)) with (Int64.repr 131072) in H;
          rewrite !Int64.unsigned_repr in H by rep_lia end.
        forward. entailer!. rewrite Z.min_r by (unfold ZSTD_BLOCKSIZE_MAX; lia). reflexivity. }
      forward. forward. forward.
      entailer!. unfold vi_bterm. rewrite Esk, Efp.
      split; [reflexivity | destruct (vi_allfcs _); reflexivity]. }
    { exfalso; match goal with H: _ <> Int.zero |- _ => apply H; reflexivity end. }
    cbv beta iota in Hiss, Hdid.
    rewrite <- (VI_arr Ews (Zlength s)).
    destruct (wi_big f) eqn:Ebig.
    { (* a frame whose window is beyond zstd's range *)
      cbv beta iota in Hfcsz, Hgfh, Hfcont, Hdid.
      forward_call (gv, Ews, offset_val (wi_start f) src, s).
      Intros r1.
      rewrite Hfcsz in *. cbv beta iota in *.
      forward.
      vi_join _x_valid_info__t'14 (Vint (Int.repr 1)).
      { forward. entailer!. }
      { forward_if.
        { apply -> seq_assoc. forward_call r1. forward. forward. entailer!.
          match goal with H: is_error_code r1 = true |- _ => rewrite H end. reflexivity. }
        { exfalso; apply Int.one_not_zero; assumption. } }
      forward_call (Int.repr 1).
      try deadvars!.
      forward_call (gv, Ews, offset_val (wi_start f) src, s).
      rewrite Hfcont.
      forward.
      vi_join0.
      { exfalso; match goal with H: _ <> Int.zero |- _ => apply H; reflexivity end. }
      { forward.
        vi_join _x_valid_info__t'17
          (Vlong (Int64.repr (if wi_fcs_present f then wi_fcs f else ZSTD_CONTENTSIZE_UNKNOWN))).
        { match goal with H: Int.repr (if wi_fcs_present f then 1 else 0) <> Int.zero |- _ =>
            assert (Efp: wi_fcs_present f = true)
              by (destruct (wi_fcs_present f); [reflexivity | contradiction H; reflexivity]) end.
          forward. forward. entailer!. rewrite Efp. reflexivity. }
        { match goal with H: Int.repr (if wi_fcs_present f then 1 else 0) = Int.zero |- _ =>
            assert (Efp: wi_fcs_present f = false)
              by (destruct (wi_fcs_present f); [exfalso; apply Int.one_not_zero; exact H | reflexivity]) end.
          forward. entailer!. rewrite Efp. f_equal. apply Int64.eqm_samerepr.
          first [exists (-1); reflexivity | exists 1; reflexivity]. }
        vi_join _x_valid_info__t'18 (Vint (Int.repr 1)).
        { forward. entailer!. }
        { forward_if.
          { forward. forward. entailer!. }
          { exfalso; apply Int.one_not_zero; assumption. } }
        forward_call (Int.repr 1).
        try deadvars!.
        entailer!. }
      forward_call (gv, Ews, offset_val (wi_start f) src, s).
      rewrite Hdid.
      forward.
      vi_join _x_valid_info__t'20 (Vint (Int.repr (wi_did f))).
      { exfalso; match goal with H: _ <> Int.zero |- _ => apply H; reflexivity end. }
      { forward. forward. entailer!. }
      vi_join _x_valid_info__t'21 (Vint (Int.repr 1)).
      { forward. entailer!. }
      { forward. entailer!. }
      forward_call (Int.repr 1).
      try deadvars!.
      forward_call (Ews, offset_val (wi_start f) src, s).
      rewrite Hisf.
      forward_call (Int.repr 1).
      try deadvars!.
      forward_call (Ews, offset_val (wi_start f) src, s).
      rewrite Hiss.
      forward.
      forward_call (Int.repr 1).
      try deadvars!.
      replace (@data_at_ HCS Tsh (Tstruct ___gp_ZSTD_FrameHeader noattr) v_zfh) with (@data_at_ ZCS Tsh t_fh v_zfh)
        by (rewrite VI_fh_; reflexivity).
      change (@data_at_ ZCS Tsh t_fh v_zfh) with (@data_at ZCS Tsh t_fh (@default_val ZCS t_fh) v_zfh).
      forward_call (gv, Tsh, v_zfh, @default_val ZCS t_fh, Ews, offset_val (wi_start f) src, s).
      Intros vr. destruct vr as [r2 vfh]. cbn [fst snd] in *.
      match goal with H: fh_post _ _ _ _ |- _ => unfold fh_post in H; rewrite Hgfh in H; cbv beta iota in H; unfold dec_err in H; destruct H as [[H _] _] end.
      rewrite VI_fh. unfold t_fh.
      assert (Hr2: r2 <> 0) by (intro; subst r2; discriminate).
      vi_join _x_valid_info__t'25 (Vint (Int.repr 1)).
      { forward. entailer!. }
      { forward_if.
        { apply -> seq_assoc. forward_call r2. forward. forward. entailer!.
          match goal with H: is_error_code r2 = true |- _ => rewrite H end. reflexivity. }
        { exfalso; apply Int.one_not_zero; assumption. } }
      forward_call (Int.repr 1).
      try deadvars!.
      vi_join _x_valid_info__t'29 (Vint (Int.repr 0)).
      { forward. forward. entailer!. }
      { forward. entailer!. }
      vi_join0.
      { exfalso; match goal with H: _ <> Int.zero |- _ => apply H; reflexivity end. }
      { forward_if.
        { exfalso. match goal with H: Int64.repr r2 = Int64.zero |- _ =>
            apply (f_equal Int64.unsigned) in H; rewrite Int64.unsigned_repr in H by rep_lia end.
          apply Hr2. assumption. }
        { forward. entailer!. } }
      forward.
      vi_join0.
      { forward_call (gv, Ews, offset_val (wi_start f) src, s).
        Intros r4.
        rewrite (Hfhs eq_refl) in *. cbv beta iota in *. subst r4.
        forward.
        forward_call (Int.repr 1).
        { entailer!. unfold vl. simpl. rewrite Int64.eq_true. reflexivity. }
        entailer!. }
      { exfalso; match goal with H: _ <> Int.zero |- _ => apply H; reflexivity end. }
      forward.
      forward_if.
      { exfalso; match goal with H: _ <> Int.zero |- _ => apply H; reflexivity end. }
      forward.
      rewrite (VI_arr Ews (Zlength s)).
      thaw FR.
      Exists k out vv.
      rewrite (@VI_elem_gen HCS Ews t_winfo 4 (VI_frecs (ws_frames ws)) _ k VI_winfo_aligned
        (VI_frecs_len (ws_frames ws) ltac:(lia)) ltac:(lia) Hfa).
      rewrite (VI_frecs_nth (ws_frames ws) k) by lia.
      rewrite (VI_src_split Ews (ws_bytes ws) (wi_start f) src) by (auto; lia).
      rewrite VI_bsum_S, VI_allfcs_S, VI_anybig_S by lia.
      change (Znth k (ws_frames ws)) with f.
      unfold winfo_val.
      rewrite Esk, Ebig.
      go_lower. apply andp_right.
      { apply prop_right. rewrite !eqb_type_refl.
        destruct (vi_anybig (sublist 0 k (ws_frames ws))); repeat split; auto; lia. }
      sep_apply (@data_at_data_at_ HCS Tsh (Tstruct ___gp_ZSTD_FrameHeader noattr)).
      cancel. }
    exfalso; destruct Hkind; congruence.
Qed.

Lemma vi_rest_zstd DC DD WG WDS {Espec: OracleKind} (gv: globals) (ws: wseries) (dm: dict_model) (cap: Z)
    (src dst v_v v_zfh: val) (k: Z) (out: list val) (vv: val) :
  wi_skippable (Znth k (ws_frames ws)) = false /\ wi_big (Znth k (ws_frames ws)) = false ->
  series_facts dm ws -> wseries_wf ws -> 0 <= cap <= 68 -> src <> nullval -> dst <> nullval -> isptr dst ->
  isptr src -> field_compatible (tarray tuchar (Z.max 1 cap)) [] dst ->
  0 <= k < Zlength (ws_frames ws) -> isptr (field_address t_wseries (DOT _f) (gv _x_valid_info__sr)) ->
  field_compatible (tarray t_winfo 4) [] (field_address t_wseries (DOT _f) (gv _x_valid_info__sr)) ->
  field_compatible (tarray tuchar (Zlength (ws_bytes ws))) [] src ->
  semax (func_tycontext f_main Vprog (G0 (Specs_api DC DD) WG WDS) nil)
    (vi_mid gv ws cap src dst v_v v_zfh k out vv) vi_rest
    (normal_ret_assert (EX k: Z, EX out: list val, EX vv: val, vi_cont gv ws cap src dst v_v v_zfh k out vv)%assert).
Proof.
  intros Hkind HSF HWF H0 Hs0 Hd0 Hpd Hps Hfd H Hfp Hfa Hfs.
  pose proof HSF as (Hsb & Hsc & Hsn & Hscn & Hnf & Ht & Hff & Hfcs & Hfds & Hbd).
  assert (Hnf': 1 <= Zlength (ws_frames ws) <= 4) by (rewrite Zlength_correct; lia).
  assert (Hn1: 1 <= Zlength (ws_bytes ws)).
  { destruct (vi_tiles_nth _ _ _ _ _ Ht 0%nat ltac:(lia)) as (A & B & C). lia. }
  destruct (VI_frame_k dm ws k HSF HWF H) as (Hfk & Hwfk & Hzk & Hst0 & Hst1 & Hsz & Hfck).
  unfold vi_mid, vi_rest, vi_cont. cbv zeta.
  abbreviate_semax.
  set (f := Znth k (ws_frames ws)) in *.
  unfold frame_facts in Hfk. cbv zeta in Hfk.
  destruct Hfk as (Hisf & Hiss & Hfcsz & Hgfh & Hfcont & Hdid & Hfhs & Hskp & _).
  set (s := skipn (Z.to_nat (wi_start f)) (ws_bytes ws)) in *.
  assert (Hs: src_spec_pre Ews s).
  { split; [auto|]. split.
    - unfold s. rewrite VI_len_skipn by lia. lia.
    - apply VI_bytes_skipn; auto. }
  unfold winfo_val.
  freeze [0;1;4;5;6;8;9;10;11;13;14;15;16] FR.
    destruct (wi_skippable f) eqn:Esk.
    { exfalso; destruct Hkind; congruence. }
    (* a Zstandard frame *)
    assert (Hzk' := Hzk). unfold winfo_zeros in Hzk'. rewrite Esk in Hzk'. destruct Hzk' as (Hvar0 & Hskn0).
    destruct Hwfk as (Wvar & Wst & Wsz & Wcst & Wcsz & Wfcs & Wdsz & Wdid & Wwin & Wwl & Wbl & Wskn & Whs).
    unfold u64, u32 in Wvar, Wst, Wsz, Wcst, Wcsz, Wfcs, Wdsz, Wdid, Wwin, Wwl, Wbl, Wskn, Whs.
    forward.
    vi_join _x_valid_info__t'9 (vb (negb (wi_single f))).
    { forward. forward. entailer!. destruct (wi_single f); reflexivity. }
    { exfalso; match goal with H: _ <> Int.zero |- _ => apply H; reflexivity end. }
    vi_join _x_valid_info__t'10 (vb (wi_big f)).
    { match goal with H: Int.repr (if negb (wi_single f) then 1 else 0) <> Int.zero |- _ =>
        assert (Esg: wi_single f = false) by (destruct (wi_single f); [contradiction H; reflexivity | reflexivity]) end.
      vi_join _x_valid_info__t'11 (Vint (Int.repr 31)).
      all: try solve [vi_dead | match goal with H: Int64.eq _ _ = true |- _ => vm_compute in H; discriminate end
                     | forward; entailer!].
      forward. forward. entailer!.
      unfold wi_big, ZSTD_WINDOWLOG_MAX. rewrite Esk, Esg. cbn [negb andb]. rewrite Z.gtb_ltb.
      destruct (zlt 31 (wi_window_log f));
        [rewrite (proj2 (Z.ltb_lt _ _)) by lia | rewrite (proj2 (Z.ltb_ge _ _)) by lia]; reflexivity. }
    { match goal with H: Int.repr (if negb (wi_single f) then 1 else 0) = Int.zero |- _ =>
        assert (Esg: wi_single f = true)
          by (destruct (wi_single f); [reflexivity | exfalso; apply Int.one_not_zero; exact H]) end.
      forward. entailer!. unfold wi_big. rewrite Esk, Esg. reflexivity. }
    forward. forward. forward.
    vi_join2 _bound (Vlong (Int64.repr (vi_bsum (sublist 0 k (ws_frames ws)) + vi_bterm f)))
      _allfcs (vb (vi_allfcs (sublist 0 k (ws_frames ws)) && (wi_skippable f || wi_fcs_present f))).
    { forward.
      forward_if.
      { match goal with H: Int.repr (if wi_fcs_present f then 1 else 0) <> Int.zero |- _ =>
          assert (Efp: wi_fcs_present f = true)
            by (destruct (wi_fcs_present f); [reflexivity | contradiction H; reflexivity]) end.
        forward. forward. entailer!. unfold vi_bterm. rewrite Esk, Efp.
        split; [reflexivity | destruct (vi_allfcs _); reflexivity]. }
      match goal with H: Int.repr (if wi_fcs_present f then 1 else 0) = Int.zero |- _ =>
        assert (Efp: wi_fcs_present f = false)
          by (destruct (wi_fcs_present f); [exfalso; apply Int.one_not_zero; exact H | reflexivity]) end.
      forward.
      vi_join _x_valid_info__t'12 (Vlong (Int64.repr (Z.min (wi_window f) ZSTD_BLOCKSIZE_MAX))).
      { match goal with H: Int64.unsigned _ < Int64.unsigned (Int64.shl _ _) |- _ =>
          change (Int64.shl (Int64.repr 1) (Int64.repr 17)) with (Int64.repr 131072) in H;
          rewrite !Int64.unsigned_repr in H by rep_lia end.
        forward. forward. entailer!. rewrite Z.min_l by (unfold ZSTD_BLOCKSIZE_MAX; lia). reflexivity. }
      { match goal with H: Int64.unsigned _ >= Int64.unsigned (Int64.shl _ _) |- _ =>
          change (Int64.shl (Int64.repr 1) (Int64.repr 17)) with (Int64.repr 131072) in H;
          rewrite !Int64.unsigned_repr in H by rep_lia end.
        forward. entailer!. rewrite Z.min_r by (unfold ZSTD_BLOCKSIZE_MAX; lia). reflexivity. }
      forward. forward. forward.
      entailer!. unfold vi_bterm. rewrite Esk, Efp.
      split; [reflexivity | destruct (vi_allfcs _); reflexivity]. }
    { exfalso; match goal with H: _ <> Int.zero |- _ => apply H; reflexivity end. }
    cbv beta iota in Hiss, Hdid.
    rewrite <- (VI_arr Ews (Zlength s)).
    destruct (wi_big f) eqn:Ebig.
    { exfalso; destruct Hkind; congruence. }
    (* a Zstandard frame within zstd's range *)
    cbv beta iota in Hfcsz, Hgfh, Hfcont, Hdid.
    forward_call (gv, Ews, offset_val (wi_start f) src, s).
    Intros r1.
    rewrite Hfcsz in *. cbv beta iota in *. subst r1.
    forward.
    vi_join _x_valid_info__t'14 (Vint (Int.repr 1)).
    all: try solve [vi_dead | forward; entailer!].
    forward_call (Int.repr 1).
    try deadvars!.
    forward_call (gv, Ews, offset_val (wi_start f) src, s).
    rewrite Hfcont.
    forward.
    vi_join0.
    { exfalso; match goal with H: _ <> Int.zero |- _ => apply H; reflexivity end. }
    { forward.
      vi_join _x_valid_info__t'17 (Vlong (Int64.repr (if wi_fcs_present f then wi_fcs f else ZSTD_CONTENTSIZE_UNKNOWN))).
      { match goal with H: Int.repr (if wi_fcs_present f then 1 else 0) <> Int.zero |- _ =>
          assert (Efp: wi_fcs_present f = true)
            by (destruct (wi_fcs_present f); [reflexivity | contradiction H; reflexivity]) end.
        forward. forward. entailer!. rewrite Efp. reflexivity. }
      { match goal with H: Int.repr (if wi_fcs_present f then 1 else 0) = Int.zero |- _ =>
          assert (Efp: wi_fcs_present f = false)
            by (destruct (wi_fcs_present f); [exfalso; apply Int.one_not_zero; exact H | reflexivity]) end.
        forward. entailer!. rewrite Efp. f_equal. apply Int64.eqm_samerepr.
        first [exists (-1); reflexivity | exists 1; reflexivity]. }
      vi_join _x_valid_info__t'18 (Vint (Int.repr 1)).
      all: try solve [vi_dead | forward; entailer!].
      forward_call (Int.repr 1).
      try deadvars!.
      entailer!. }
    forward_call (gv, Ews, offset_val (wi_start f) src, s).
    rewrite Hdid.
    forward.
    vi_join _x_valid_info__t'20 (Vint (Int.repr (wi_did f))).
    { exfalso; match goal with H: _ <> Int.zero |- _ => apply H; reflexivity end. }
    { forward. forward. entailer!. }
    vi_join _x_valid_info__t'21 (Vint (Int.repr 1)).
    all: try solve [vi_dead | forward; entailer!].
    forward_call (Int.repr 1).
    try deadvars!.
    forward_call (Ews, offset_val (wi_start f) src, s).
    rewrite Hisf.
    forward_call (Int.repr 1).
    try deadvars!.
    forward_call (Ews, offset_val (wi_start f) src, s).
    rewrite Hiss.
    forward.
    forward_call (Int.repr 1).
    try deadvars!.
    replace (@data_at_ HCS Tsh (Tstruct ___gp_ZSTD_FrameHeader noattr) v_zfh) with (@data_at_ ZCS Tsh t_fh v_zfh)
      by (rewrite VI_fh_; reflexivity).
    change (@data_at_ ZCS Tsh t_fh v_zfh) with (@data_at ZCS Tsh t_fh (@default_val ZCS t_fh) v_zfh).
    forward_call (gv, Tsh, v_zfh, @default_val ZCS t_fh, Ews, offset_val (wi_start f) src, s).
    Intros vr. destruct vr as [r2 vfh]. cbn [fst snd] in *.
    match goal with H: fh_post _ _ _ _ |- _ => unfold fh_post in H; rewrite Hgfh in H; destruct H as [-> ->] end.
    rewrite VI_fh. unfold t_fh.
    unfold fh_val, wi_header. rewrite Esk.
    cbn [fh_contentSize fh_windowSize fh_blockSizeMax fh_frameType fh_headerSize fh_dictID fh_checksumFlag].
    vi_join _x_valid_info__t'25 (Vint (Int.repr 1)).
    all: try solve [vi_dead | forward; entailer!].
    forward_call (Int.repr 1).
    try deadvars!.
    vi_join _x_valid_info__t'29 (Vint (Int.repr 0)).
    all: try solve [vi_dead | forward; forward; entailer!].
    assert (Hhs: 5 <= wi_hsize f <= 19) by (apply (VI_fhs_bound s); apply Hfhs; reflexivity).
    vi_join0.
    { exfalso; match goal with H: _ <> Int.zero |- _ => apply H; reflexivity end. }
    { forward_if.
      { forward.
        forward_call (Int.repr 1).
        try deadvars!.
        forward.
        vi_join _x_valid_info__t'27
          (Vlong (Int64.repr (if wi_fcs_present f then wi_fcs f else ZSTD_CONTENTSIZE_UNKNOWN))).
        { match goal with H: Int.repr (if wi_fcs_present f then 1 else 0) <> Int.zero |- _ =>
            assert (Efp: wi_fcs_present f = true)
              by (destruct (wi_fcs_present f); [reflexivity | contradiction H; reflexivity]) end.
          forward. forward. entailer!. rewrite Efp. reflexivity. }
        { match goal with H: Int.repr (if wi_fcs_present f then 1 else 0) = Int.zero |- _ =>
            assert (Efp: wi_fcs_present f = false)
              by (destruct (wi_fcs_present f); [exfalso; apply Int.one_not_zero; exact H | reflexivity]) end.
          forward. entailer!. rewrite Efp. f_equal. apply Int64.eqm_samerepr.
          first [exists (-1); reflexivity | exists 1; reflexivity]. }
        forward.
        forward_call (Int.repr 1).
        { entailer!. simpl. rewrite Int64.eq_true. reflexivity. }
        forward. forward.
        forward_call (Int.repr 1).
        { entailer!. unfold vl. simpl. rewrite Int64.eq_true. reflexivity. }
        forward.
        vi_join _x_valid_info__t'28 (Vlong (Int64.repr (Z.min (wi_window f) ZSTD_BLOCKSIZE_MAX))).
        { match goal with H: Int64.unsigned _ < Int64.unsigned (Int64.shl _ _) |- _ =>
            change (Int64.shl (Int64.repr 1) (Int64.repr 17)) with (Int64.repr 131072) in H;
            rewrite !Int64.unsigned_repr in H by rep_lia end.
          forward. forward. entailer!. rewrite Z.min_l by (unfold ZSTD_BLOCKSIZE_MAX; lia). reflexivity. }
        { match goal with H: Int64.unsigned _ >= Int64.unsigned (Int64.shl _ _) |- _ =>
            change (Int64.shl (Int64.repr 1) (Int64.repr 17)) with (Int64.repr 131072) in H;
            rewrite !Int64.unsigned_repr in H by rep_lia end.
          forward. entailer!. rewrite Z.min_r by (unfold ZSTD_BLOCKSIZE_MAX; lia). reflexivity. }
        forward.
        forward_call (Int.repr 1).
        { entailer!. simpl. try rewrite Int.unsigned_repr by (unfold ZSTD_BLOCKSIZE_MAX; rep_lia).
          rewrite Int64.eq_true. reflexivity. }
        forward. forward.
        forward_call (Int.repr 1).
        { entailer!. unfold vl. simpl. try rewrite Int.unsigned_repr by rep_lia. rewrite Int64.eq_true. reflexivity. }
        forward. forward.
        forward_call (Int.repr 1).
        { entailer!. unfold vu. simpl. rewrite Int.eq_true. reflexivity. }
        forward. forward.
        forward_call (Int.repr 1).
        { entailer!. unfold vb. simpl. rewrite Int.eq_true. reflexivity. }
        entailer!. }
      { vi_dead. } }
    forward.
    vi_join0.
    { forward_call (gv, Ews, offset_val (wi_start f) src, s).
      Intros r4.
      rewrite (Hfhs eq_refl) in *. cbv beta iota in *. subst r4.
      forward.
      forward_call (Int.repr 1).
      { entailer!. unfold vl. simpl. rewrite Int64.eq_true. reflexivity. }
      entailer!. }
    { exfalso; match goal with H: _ <> Int.zero |- _ => apply H; reflexivity end. }
    forward.
    forward_if.
    { exfalso; match goal with H: _ <> Int.zero |- _ => apply H; reflexivity end. }
    forward.
    rewrite (VI_arr Ews (Zlength s)).
    thaw FR.
    Exists k out vv.
    rewrite (@VI_elem_gen HCS Ews t_winfo 4 (VI_frecs (ws_frames ws)) _ k VI_winfo_aligned
      (VI_frecs_len (ws_frames ws) ltac:(lia)) ltac:(lia) Hfa).
    rewrite (VI_frecs_nth (ws_frames ws) k) by lia.
    rewrite (VI_src_split Ews (ws_bytes ws) (wi_start f) src) by (auto; lia).
    rewrite VI_bsum_S, VI_allfcs_S, VI_anybig_S by lia.
    change (Znth k (ws_frames ws)) with f.
    unfold winfo_val.
    rewrite Esk, Ebig.
    go_lower. apply andp_right.
    { apply prop_right. rewrite !eqb_type_refl.
      destruct (vi_anybig (sublist 0 k (ws_frames ws))); repeat split; auto; lia. }
    sep_apply (@data_at_data_at_ HCS Tsh (Tstruct ___gp_ZSTD_FrameHeader noattr)).
    cancel.
Qed.

Lemma vi_body_skip DC DD WG WDS {Espec: OracleKind} (gv: globals) (ws: wseries) (dm: dict_model) (cap: Z)
    (src dst v_v v_zfh: val) (k: Z) (out: list val) (vv: val) :
  wi_skippable (Znth k (ws_frames ws)) = true ->
  series_facts dm ws -> wseries_wf ws -> 0 <= cap <= 68 -> src <> nullval -> dst <> nullval -> isptr dst ->
  isptr src -> field_compatible (tarray tuchar (Z.max 1 cap)) [] dst ->
  semax (func_tycontext f_main Vprog (G0 (Specs_api DC DD) WG WDS) nil)
    (vi_inv gv ws cap src dst v_v v_zfh k out vv) vi_body
    (loop1_ret_assert (EX k: Z, EX out: list val, EX vv: val, vi_cont gv ws cap src dst v_v v_zfh k out vv)%assert
       (overridePost (EX out: list val, EX vv: val, vi_brk gv ws cap src dst v_v v_zfh out vv)%assert
          (frame_ret_assert (function_body_ret_assert tint (PROP () RETURN () SEP (TT))) (stackframe_of f_main)))).
Proof.
  intros Hkind HSF HWF H0 Hs0 Hd0 Hpd Hps Hfd.
  apply (vi_head DC DD WG WDS gv ws dm); auto. intros.
  eapply (vi_rest_skip DC DD WG WDS gv ws dm); eauto.
Qed.

Lemma vi_body_big DC DD WG WDS {Espec: OracleKind} (gv: globals) (ws: wseries) (dm: dict_model) (cap: Z)
    (src dst v_v v_zfh: val) (k: Z) (out: list val) (vv: val) :
  wi_skippable (Znth k (ws_frames ws)) = false /\ wi_big (Znth k (ws_frames ws)) = true ->
  series_facts dm ws -> wseries_wf ws -> 0 <= cap <= 68 -> src <> nullval -> dst <> nullval -> isptr dst ->
  isptr src -> field_compatible (tarray tuchar (Z.max 1 cap)) [] dst ->
  semax (func_tycontext f_main Vprog (G0 (Specs_api DC DD) WG WDS) nil)
    (vi_inv gv ws cap src dst v_v v_zfh k out vv) vi_body
    (loop1_ret_assert (EX k: Z, EX out: list val, EX vv: val, vi_cont gv ws cap src dst v_v v_zfh k out vv)%assert
       (overridePost (EX out: list val, EX vv: val, vi_brk gv ws cap src dst v_v v_zfh out vv)%assert
          (frame_ret_assert (function_body_ret_assert tint (PROP () RETURN () SEP (TT))) (stackframe_of f_main)))).
Proof.
  intros Hkind HSF HWF H0 Hs0 Hd0 Hpd Hps Hfd.
  apply (vi_head DC DD WG WDS gv ws dm); auto. intros.
  eapply (vi_rest_big DC DD WG WDS gv ws dm); eauto.
Qed.

Lemma vi_body_zstd DC DD WG WDS {Espec: OracleKind} (gv: globals) (ws: wseries) (dm: dict_model) (cap: Z)
    (src dst v_v v_zfh: val) (k: Z) (out: list val) (vv: val) :
  wi_skippable (Znth k (ws_frames ws)) = false /\ wi_big (Znth k (ws_frames ws)) = false ->
  series_facts dm ws -> wseries_wf ws -> 0 <= cap <= 68 -> src <> nullval -> dst <> nullval -> isptr dst ->
  isptr src -> field_compatible (tarray tuchar (Z.max 1 cap)) [] dst ->
  semax (func_tycontext f_main Vprog (G0 (Specs_api DC DD) WG WDS) nil)
    (vi_inv gv ws cap src dst v_v v_zfh k out vv) vi_body
    (loop1_ret_assert (EX k: Z, EX out: list val, EX vv: val, vi_cont gv ws cap src dst v_v v_zfh k out vv)%assert
       (overridePost (EX out: list val, EX vv: val, vi_brk gv ws cap src dst v_v v_zfh out vv)%assert
          (frame_ret_assert (function_body_ret_assert tint (PROP () RETURN () SEP (TT))) (stackframe_of f_main)))).
Proof.
  intros Hkind HSF HWF H0 Hs0 Hd0 Hpd Hps Hfd.
  apply (vi_head DC DD WG WDS gv ws dm); auto. intros.
  eapply (vi_rest_zstd DC DD WG WDS gv ws dm); eauto.
Qed.

Lemma vi_loop_body DC DD WG WDS {Espec: OracleKind} (gv: globals) (ws: wseries) (dm: dict_model) (cap: Z)
    (src dst v_v v_zfh: val) (k: Z) (out: list val) (vv: val) :
  series_facts dm ws -> wseries_wf ws -> 0 <= cap <= 68 -> src <> nullval -> dst <> nullval -> isptr dst ->
  isptr src -> field_compatible (tarray tuchar (Z.max 1 cap)) [] dst ->
  semax (func_tycontext f_main Vprog (G0 (Specs_api DC DD) WG WDS) nil)
    (vi_inv gv ws cap src dst v_v v_zfh k out vv) vi_body
    (loop1_ret_assert (EX k: Z, EX out: list val, EX vv: val, vi_cont gv ws cap src dst v_v v_zfh k out vv)%assert
       (overridePost (EX out: list val, EX vv: val, vi_brk gv ws cap src dst v_v v_zfh out vv)%assert
          (frame_ret_assert (function_body_ret_assert tint (PROP () RETURN () SEP (TT))) (stackframe_of f_main)))).
Proof.
  intros. destruct (wi_skippable (Znth k (ws_frames ws))) eqn:E1.
  - eapply vi_body_skip; eauto.
  - destruct (wi_big (Znth k (ws_frames ws))) eqn:E2.
    + eapply vi_body_big; eauto.
    + eapply vi_body_zstd; eauto.
Qed.

Theorem main_ok_valid_info : MainOK.
Proof.
intros DC DD WG WDS HWG.
unfold main_spec, QPmain_spec_ext', NDmk_funspec.
split3; [reflexivity | reflexivity |].
intros Espec DTL gv.
simpl fn_body; simpl fn_params; simpl fn_return.
change (map fst []) with (@nil ident).
eapply (main_pre_InitGpred
          (sepcon (zstd_globals gv) (sepcon (WG gv) (sepcon (data_at Ews t_wseries (zero_val t_wseries) (gv _x_valid_info__sr))
             (sepcon (data_at Ews t_wdict (zero_val t_wdict) (gv _x_valid_info__wd)) TT))))
          _ _ _ Zstd.contracts.x_valid_info.whole_prog).
4: idtac.
- intros. apply VI_pre; auto.
- reflexivity.
- apply Forall_forall; intros [i g] Hin; simpl fst.
  apply VI_tyc_g_isSome. unfold Vprog, QPvarspecs. rewrite map_map.
  apply in_map_iff. exists (i, g); auto.
- process_stackframe_of.
  repeat rewrite <- data_at__offset_zero.
  try simple apply start_function_aux1.
  match goal with |- semax ?D ?P ?c (frame_ret_assert (function_body_ret_assert ?t _) ?F) =>
    apply (semax_post (frame_ret_assert (function_body_ret_assert t (PROP () LOCAL () (SEP (TT)))) F))
  end.
  1,2,3: intros; simpl; normalize.
  1: intros [v|]; simpl; unfold bind_ret; simpl; normalize;
       intros x; apply andp_left2; apply sepcon_derives; [unfold_lift; apply TT_right | auto].
  abbreviate_semax.
  sep_apply (create_mem_mgr gv).
  forward_call 2.
  Intros withdict.
  forward. forward. forward.
  forward_if (EX ws: wseries, EX dm: dict_model,
    PROP (series_facts dm ws; wseries_wf ws)
    LOCAL (temp _bound (Vlong (Int64.repr 0)); temp _allfcs (Vint (Int.repr 1)); temp _anybig (Vint (Int.repr 0));
           lvar _v tuint v_v; lvar _zfh (Tstruct ___gp_ZSTD_FrameHeader noattr) v_zfh; gvars gv)
    SEP (mem_mgr gv; data_at_ Tsh tuint v_v; data_at_ Tsh (Tstruct ___gp_ZSTD_FrameHeader noattr) v_zfh;
         zstd_globals gv; WG gv; data_at Ews t_wseries (wseries_val ws) (gv _x_valid_info__sr); TT; has_ext tt)).
  + forward_call (gv, Ews, gv _x_valid_info__wd).
    Intros wd.
    forward_call (gv, Ews, gv _x_valid_info__sr, gv _x_valid_info__wd, Some (wd, Ews)).
    { unfold wdict_arg. entailer!. }
    Intros ws.
    unfold wdict_arg, wdict_model, wdict_rep in *.
    Intros stv.
    destruct H1 as (Hb1 & Hb2 & Hb3 & Hb4 & Hb5 & Hb6 & Hb7).
    simpl in Hb2.
    sep_apply (VI_wd_fields Ews (wdict_val wd (gv _x_valid_info__wd) stv) (gv _x_valid_info__wd)).
    unfold wdict_val; cbn [fst snd].
    sep_apply (VI_wd_bytes Ews (wd_bytes wd) (Zrepeat (Vint Int.zero) (6144 - Zlength (wd_bytes wd))) (gv _x_valid_info__wd)); [lia|].
    Intros.
    forward.
    rewrite <- VI_arr.
    forward_call (Ews, field_address t_wdict (DOT _bytes) (gv _x_valid_info__wd), wd_bytes wd).
    { entailer!. simpl. rewrite field_compatible_field_address by auto with field_compatible. reflexivity. }
    forward.
    forward_if (PROP () LOCAL (temp _x_valid_info__t'2 (Vint (Int.repr (dict_id_of (wd_bytes wd)))); temp _x_valid_info__t'3 (Vint (Int.repr (wd_id wd)));
       gvars gv; lvar _v tuint v_v; lvar _zfh (Tstruct ___gp_ZSTD_FrameHeader noattr) v_zfh;
       temp _bound (Vlong (Int64.repr 0)); temp _allfcs (Vint (Int.repr 1)); temp _anybig (Vint (Int.repr 0)))
     SEP (WG gv; data_at Ews t_wseries (wseries_val ws) (gv _x_valid_info__sr);
       mem_mgr gv; data_at_ Tsh tuint v_v; data_at_ Tsh (Tstruct ___gp_ZSTD_FrameHeader noattr) v_zfh;
       zstd_globals gv; TT; has_ext tt)).
    * forward. forward. entailer!.
    * forward. destruct (wd_formatted wd) eqn:Ef; [discriminate|]. destruct (Hb7 eq_refl) as [_ ->]. entailer!.
    * forward_call (Int.repr 1).
      { entailer!. rewrite Hb6, Int.eq_true. reflexivity. }
      Exists ws (wd_model wd). entailer!.
  + forward_call (gv, Ews, gv _x_valid_info__sr, nullval, @None (wdict * share)).
    { unfold wdict_arg. entailer!. }
    Intros ws. unfold wdict_arg, wdict_model in *. Intros.
    Exists ws no_dict. entailer!.
  + Intros ws dm.
    rename H0 into HSF, H1 into HWF.
    pose proof HSF as (Hsb & Hsc & Hsn & Hscn & Hnf & Ht & Hff & Hfcs & Hfds & Hbd).
    assert (Hnf': 1 <= Zlength (ws_frames ws) <= 4) by (rewrite Zlength_correct; lia).
    assert (Hn1: 1 <= Zlength (ws_bytes ws)).
    { destruct (vi_tiles_nth _ _ _ _ _ Ht 0%nat ltac:(lia)) as (A & B & C). lia. }
    forward_call (0, 68).
    Intros cap.
    sep_apply (VI_sr_fields Ews (wseries_val ws) (gv _x_valid_info__sr)).
    unfold wseries_val; cbn [fst snd].
    sep_apply (VI_sr_bytes Ews (ws_bytes ws) (Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength (ws_bytes ws))) (gv _x_valid_info__sr)); try lia.
    Intros.
    forward.
    forward_call (gv, Ews, field_address t_wseries (DOT _bytes) (gv _x_valid_info__sr), ws_bytes ws).
    { entailer!. simpl. rewrite field_compatible_field_address by auto with field_compatible. reflexivity. }
    Intros src.
    rewrite (Z.max_r 1 (Zlength (ws_bytes ws))) by lia. rewrite Z.sub_diag, Zrepeat_0, app_nil_r.
    forward.
    match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp _x_valid_info__t'6 (Vlong (Int64.repr (Z.max 1 cap))) :: L) (SEPx R))) end.
    { match goal with H: Int64.unsigned _ < Int64.unsigned _ |- _ => rewrite !Int64.unsigned_repr in H by rep_lia end.
      forward. rewrite Z.max_r by lia. entailer!. }
    { match goal with H: Int64.unsigned _ >= Int64.unsigned _ |- _ => rewrite !Int64.unsigned_repr in H by rep_lia end.
      forward. rewrite Z.max_l by lia. entailer!. }
    forward_call (tarray tuchar (Z.max 1 cap), gv).
    { simpl. rewrite Z.max_r by lia. rep_lia. }
    Intros dst.
    forward.
    destruct (eq_dec src nullval) as [Hs0|Hs0]; [| destruct (eq_dec dst nullval) as [Hd0|Hd0]].
    { subst src. Intros.
      match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
        forward_if (PROPx P (LOCALx (temp _x_valid_info__t'8 (Vint Int.one) :: L) (SEPx R))) end.
      { forward. entailer!. }
      { match goal with H: ?a <> ?a |- _ => contradiction (H eq_refl) end. }
      forward_if (PROP (False) LOCAL () SEP ()).
      { forward_call (tarray tuchar (Zlength (ws_bytes ws)), nullval, gv).
        { rewrite (if_true (nullval = nullval)) by auto. cancel. }
        forward_call (tarray tuchar (Z.max 1 cap), dst, gv).
        forward. cancel. }
      { exfalso. apply Int.one_not_zero. assumption. } }
    { subst dst. Intros.
      assert_PROP (isptr src) as Hps by entailer!.
      match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
        forward_if (PROPx P (LOCALx (temp _x_valid_info__t'8 (Vint Int.one) :: L) (SEPx R))) end.
      { contradiction. }
      { forward. entailer!. }
      forward_if (PROP (False) LOCAL () SEP ()).
      { forward_call (tarray tuchar (Zlength (ws_bytes ws)), src, gv).
        { rewrite (if_false (src = nullval)) by auto. cancel. }
        forward_call (tarray tuchar (Z.max 1 cap), nullval, gv).
        { rewrite (if_true (nullval = nullval)) by auto. cancel. }
        forward. cancel. }
      { exfalso. apply Int.one_not_zero. assumption. } }
    Intros.
    assert_PROP (isptr dst) as Hpd by entailer!.
    assert_PROP (isptr src) as Hps by entailer!.
    match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp _x_valid_info__t'8 (Vint Int.zero) :: L) (SEPx R))) end.
    { contradiction. }
    { forward. destruct dst; try contradiction. entailer!. }
    match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx L (SEPx R))) end.
    { match goal with H: _ <> _ |- _ => exfalso; apply H; reflexivity end. }
    { forward. entailer!. }
    assert_PROP (field_compatible (tarray tuchar (Z.max 1 cap)) [] dst) as Hfd by entailer!.
    rewrite (VI_dst_split Ews cap dst) by (auto; lia).
    Intros.
    change (map winfo_val (ws_frames ws) ++ Zrepeat (winfo_val winfo0) (4 - Zlength (ws_frames ws)))
      with (VI_frecs (ws_frames ws)).
    forward.
    forward_loop (EX k: Z, EX out: list val, EX vv: val, vi_inv gv ws cap src dst v_v v_zfh k out vv)%assert
      continue: (EX k: Z, EX out: list val, EX vv: val, vi_cont gv ws cap src dst v_v v_zfh k out vv)%assert
      break: (EX out: list val, EX vv: val, vi_brk gv ws cap src dst v_v v_zfh out vv)%assert.
    { Exists 0 (Zrepeat Vundef cap) Vundef. unfold vi_inv. entailer!. }
    { Intros k out vv. apply (vi_loop_body DC DD WG WDS gv ws dm); auto. }
    { Intros k out vv. unfold vi_cont. Intros. forward. Exists (k + 1) out vv. unfold vi_inv. entailer!. }
    Intros out vv. unfold vi_brk.
    rewrite <- (VI_arr Ews (Zlength (ws_bytes ws)) (zbytes (ws_bytes ws)) src).
    forward.
    forward_call (gv, Ews, src, ws_bytes ws).
    { split; [auto | split; [rep_lia | auto]]. }
    forward. forward.
    forward_call (gv, Ews, src, ws_bytes ws).
    { split; [auto | split; [rep_lia | auto]]. }
    forward.
    vi_join _x_valid_info__t'35
      (Vlong (Int64.repr (if vi_allfcs (ws_frames ws) then Zlength (ws_content ws) else ZSTD_CONTENTSIZE_UNKNOWN))).
    { match goal with H: Int.repr (if vi_allfcs (ws_frames ws) then 1 else 0) <> Int.zero |- _ =>
        assert (Ea: vi_allfcs (ws_frames ws) = true)
          by (destruct (vi_allfcs (ws_frames ws)); [reflexivity | contradiction H; reflexivity]) end.
      forward. forward. entailer!. rewrite Ea. reflexivity. }
    { match goal with H: Int.repr (if vi_allfcs (ws_frames ws) then 1 else 0) = Int.zero |- _ =>
        assert (Ea: vi_allfcs (ws_frames ws) = false)
          by (destruct (vi_allfcs (ws_frames ws)); [exfalso; apply Int.one_not_zero; exact H | reflexivity]) end.
      forward. entailer!. rewrite Ea. f_equal. apply Int64.eqm_samerepr.
      first [exists (-1); reflexivity | exists 1; reflexivity]. }
    vi_join _x_valid_info__t'36 (Vint (Int.repr 1)).
    { forward. entailer!. }
    { destruct (vi_fds dm ws HSF) as [[Eab Efd] | Efd]; rewrite Efd in *.
      { forward_if.
        { forward. forward. entailer!. }
        { exfalso. rewrite Eab in *. apply Int.one_not_zero; assumption. } }
      { vi_dead. } }
    forward_call (Int.repr 1).
    vi_join _x_valid_info__t'37 (Vint (Int.repr 1)).
    { forward. entailer!. }
    { destruct (vi_bound dm ws HSF) as [[Eab Ebd] | Ebd]; rewrite Ebd in *.
      { forward_if.
        { forward. forward. entailer!. }
        { exfalso. rewrite Eab in *. apply Int.one_not_zero; assumption. } }
      { vi_dead. } }
    forward_call (Int.repr 1).
    rewrite (VI_arr Ews (Zlength (ws_bytes ws)) (zbytes (ws_bytes ws)) src).
    sep_apply (data_at_data_at_ Ews (tarray tuchar (Zlength (ws_bytes ws))) (zbytes (ws_bytes ws)) src).
    forward_call (tarray tuchar (Zlength (ws_bytes ws)), src, gv).
    { rewrite if_false by auto. cancel. }
    sep_apply (data_at_data_at_ Ews (tarray tuchar cap) out dst).
    forward_call (tarray tuchar (Z.max 1 cap), dst, gv).
    { rewrite if_false by auto. rewrite (VI_dst_split Ews cap dst) by (auto; lia). cancel. }
    forward.
    cancel.
Qed.
