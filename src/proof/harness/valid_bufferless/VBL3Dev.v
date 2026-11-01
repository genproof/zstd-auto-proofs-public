Require Import VST.floyd.proofauto.
Require Import Zstd.proof.harness.valid_bufferless.VBL3Inv.
Require Import Zstd.proof.harness.valid_bufferless.VBL3Inner.
Require Import Zstd.proof.harness.valid_bufferless.VBL3Frame.
Require Zstd.proof.top.MainPre6.
Require Import Zstd.proof.harness.ApiAfterKit.

Local Notation ZCS := Zstd.proof.zstd.Base.CompSpecs.
Local Notation HCS := Zstd.proof.harness.valid_bufferless.HOK_valid_bufferless.CompSpecs.

(* vb_wd's bytes, read by the dictionary copy (nothing in mode 0, where dn = 0) *)
Definition VL_wdb (db: list Z) (p: val) : mpred :=
  if Zlength db =? 0 then emp
  else @field_at HCS Ews t_wdict (DOT _bytes) (zbytes db ++ Zrepeat (Vint Int.zero) (6144 - Zlength db)) p.

Lemma VL_wd_take wd p stv :
  @data_at HCS Ews t_wdict (wdict_val wd p stv) p |-- VL_wdb (wd_bytes wd) p * TT.
Proof.
  unfold VL_wdb. destruct (Zlength (wd_bytes wd) =? 0); [rewrite emp_sepcon; apply TT_right|].
  unfold_data_at (data_at _ _ _ p). cbn [fst snd wdict_val]. cancel.
Qed.

(* the DDict state carried when there is no DDict (modes 0 and 1) *)
Definition VL_dd0 (db: list Z) : ddict_st := {| dd_bytes := db; dd_ref := None; dd_buf := nullval; dd_ld := None |}.

Ltac VL_cx := exfalso; match goal with
  | H: Int.repr _ = Int.zero |- _ => vm_compute in H; discriminate H
  | H: Int.repr _ <> Int.zero |- _ => apply H; vm_compute; reflexivity
  | H: typed_true _ _ |- _ => vm_compute in H; discriminate H
  | H: typed_false _ _ |- _ => vm_compute in H; discriminate H
  end.
Ltac VL_ifs2 := repeat apply -> seq_assoc; apply semax_if_seq; forward_if; try solve [VL_kill | VL_cx].

Ltac VL_side := try (match goal with |- _ |-- _ =>
  first [rewrite if_true by auto | rewrite if_false by auto | idtac]; cancel end).


Section Body.
Variable DC : globals -> val -> dctx_st -> mpred.
Variable DD : globals -> val -> ddict_st -> mpred.
Variable WG : globals -> mpred.
Variable WDS : wdict -> reptype t_wstate -> Prop.
Variable HWG : forall gv, InitGPred wvardefs gv |-- WG gv.

Ltac VL_fail Hvp ws db gv :=
  (repeat match goal with H: ?x = nullval |- _ => is_var x; subst x end;
        repeat match goal with H: ?x <> nullval, P: is_pointer_or_null ?x |- _ => is_var x;
          let Hp := fresh in assert (Hp: isptr x) by (destruct x; simpl in *; try contradiction; auto; subst; contradiction);
          destruct x; try contradiction end;
        repeat match goal with H: ?x <> nullval |- _ => is_var x;
          let Hp := fresh in assert_PROP (isptr x) as Hp by entailer!; destruct x; try contradiction end;
        Intros;
        repeat (first [VL_ifs2 | forward]);
        match goal with |- context [temp _src ?x] =>
          forward_call (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws))), x, gv); [VL_side | ] end;
        match goal with |- context [temp _buf ?x] =>
          forward_call (tarray tuchar (Zlength (ws_content ws) + 1 + Zlength db), x, gv); [VL_side | ] end;
        first [ match goal with |- context [temp _dctx nullval] => forward_call (gv, nullval, @None dctx_st) end
              | match goal with |- context [temp _dctx ?x] =>
                  sep_apply (Hvp (DC gv x dctx_init) x); forward_call (gv, x, Some dctx_init) end ];
        try (match goal with |- _ |-- _ => cancel end);
        eapply semax_pre with (P' := PROP () LOCAL () SEP (TT)); [go_lower; apply TT_right |];
        forward).

Lemma VL_body_main : semax_body Vprog (VL_G1 DC DD WG WDS) f_main main_spec.
Proof.
unfold main_spec, QPmain_spec_ext', NDmk_funspec.
split3; [reflexivity | reflexivity |].
intros Espec DTL gv.
simpl fn_body; simpl fn_params; simpl fn_return.
change (map fst []) with (@nil ident).
eapply (main_pre_InitGpred
          (sepcon (zstd_globals gv) (sepcon (WG gv) (sepcon (data_at Ews t_wseries (zero_val t_wseries) (gv _x_valid_bufferless__sr))
             (sepcon (data_at Ews t_wdict (zero_val t_wdict) (gv _vb_wd)) TT))))
          _ _ _ Zstd.contracts.x_valid_bufferless.whole_prog).
4: idtac.
- intros. apply VLD_pre; auto.
- reflexivity.
- apply Forall_forall; intros [i g] Hin; simpl fst.
  apply VLD_tyc_g_isSome. unfold Vprog, QPvarspecs. rewrite map_map.
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
  forward_call 3.
  Intros mode.
  forward. forward. forward. forward. forward.
  forward_if (EX ws: wseries, EX db: list Z, EX dm: dict_model,
    PROP (series_facts dm ws; wseries_wf ws; VL_dfacts mode db dm)
    LOCAL (temp _stop (Vint (Int.repr 0)); temp _ddict nullval; temp _pos (Vlong (Int64.repr 0));
           temp _ipos (Vlong (Int64.repr 0)); temp _dn (Vlong (Int64.repr (Zlength db)));
           temp _mode (Vint (Int.repr mode)); gvars gv)
    SEP (mem_mgr gv; zstd_globals gv; WG gv; data_at Ews t_wseries (wseries_val ws) (gv _x_valid_bufferless__sr);
         VL_wdb db (gv _vb_wd); TT)).
  { forward_call (gv, Ews, gv _vb_wd).
    Intros wd. unfold wdict_rep. Intros stv.
    forward.
    forward_call (gv, Ews, gv _x_valid_bufferless__sr, gv _vb_wd, WAOwn wd Ews).
    { unfold wdict_arg, wdict_rep. Exists stv. entailer!. }
    Intros ws. unfold wdict_arg, wdict_rep. Intros stv'.
    sep_apply (VL_wd_take wd (gv _vb_wd) stv').
    Exists ws (wd_bytes wd) (wd_model wd). entailer!.
    pose proof H1 as (Hdok & Hdl & Hda & _). right. split; [auto|]. split; [auto|]. split; [lia|].
    unfold wd_model. destruct (dict_auto (wd_bytes wd)); [reflexivity | contradiction]. }
  { forward_call (gv, Ews, gv _x_valid_bufferless__sr, nullval, WANone).
    { unfold wdict_arg. entailer!. }
    Intros ws. unfold wdict_arg. Intros.
    Exists ws (@nil Z) no_dict. unfold VL_wdb. simpl Zlength. simpl Z.eqb. cbv iota. entailer!.
    left. split; [lia | auto]. }
  Intros ws db dm.
  assert (Hdb: 0 <= Zlength db <= 6144).
  { match goal with Hd: VL_dfacts _ _ _ |- _ => destruct Hd as [(_ & -> & _) | (_ & _ & Hl & _)] end;
    [rewrite Zlength_nil | ]; lia. }
  match goal with Hs: series_facts dm ws |- _ => pose proof Hs as (Hbok & Hcok & Hnb & Hnc & Hnf & _) end.
  sep_apply (VLB_ws_unfold ws (gv _x_valid_bufferless__sr) Hnb). unfold VLB_sr_rest. Intros.
  forward. forward.
  forward_call (gv, Ews, field_address t_wseries (DOT _bytes) (gv _x_valid_bufferless__sr), ws_bytes ws).
  { entailer!.
    match goal with H: field_compatible _ [] (field_address t_wseries (DOT _bytes) ?p) |- _ =>
      unfold field_address in *; destruct (field_compatible_dec t_wseries (DOT _bytes) p) as [Hfc|Hfc];
      [| destruct H as [Hx _]; contradiction] end.
    simpl. destruct (gv _x_valid_bufferless__sr); try contradiction. reflexivity. }
  Intros src.
  forward.
  forward_call (tarray tuchar (Zlength (ws_content ws) + 1 + Zlength db), gv).
  { simpl. rep_lia. }
  Intros buf.
  forward_call gv. Intros dctx.
  forward. forward.
  assert (Hvp: forall (P: mpred) q, (P && valid_pointer q) |-- P) by (intros; apply andp_left1, derives_refl).
  destruct (eq_dec src nullval) as [Hs|Hs]; destruct (eq_dec buf nullval) as [Hb|Hb];
    destruct (eq_dec dctx nullval) as [Hd|Hd].
  1: VL_fail Hvp ws db gv.
  1: VL_fail Hvp ws db gv.
  1: VL_fail Hvp ws db gv.
  1: VL_fail Hvp ws db gv.
  1: VL_fail Hvp ws db gv.
  1: VL_fail Hvp ws db gv.
  1: VL_fail Hvp ws db gv.
  assert (Hps: isptr src) by (destruct src; simpl in *; try contradiction; auto; subst; contradiction).
  destruct src as [| | | | | bs os]; try contradiction.
  assert_PROP (isptr buf) as Hpb by entailer!. destruct buf as [| | | | | bb ob]; try contradiction.
  assert (Hpd: isptr dctx) by (destruct dctx; simpl in *; try contradiction; auto; subst; contradiction).
  destruct dctx as [| | | | | bd od]; try contradiction.
  Intros.
  VL_ifs. forward. VL_ifs. forward. VL_ifs. forward.
  match goal with |- context [temp _dict ?v] => replace v with (offset_val (Zlength (ws_content ws) + 1) (Vptr bb ob))
    by (rewrite <- (VLB_dict_val (Vptr bb ob) (Zlength (ws_content ws)) I ltac:(rep_lia)); reflexivity) end.
  assert_PROP (field_compatible (tarray tuchar (Zlength (ws_content ws) + 1 + Zlength db)) [] (Vptr bb ob)) as Hfb by entailer!.
  rewrite (VLB_split3_ Ews (Zlength (ws_content ws)) (Zlength db) (Vptr bb ob)) by (auto; rep_lia). Intros.
  rewrite (VLB_Zrepeat Ews (Zlength db)).
  sep_apply (VLB_rest_fold ws (gv _x_valid_bufferless__sr)).
  sep_apply (VLB_ws_fold ws (gv _x_valid_bufferless__sr) Hnb).
  VL_ifs. forward.
  freeze [0;1;2;3;4;5;6;8;9;10;12] FR1.
  match goal with |- semax _ (PROPx _ (LOCALx (_ :: ?L) (SEPx (?F :: _ :: ?R)))) _ _ =>
    forward_loop (EX j: Z, PROPx [0 <= j <= Zlength db] (LOCALx (temp _j (Vlong (Int64.repr j)) :: L)
         (SEPx (F :: data_at Ews (tarray tuchar (Zlength db)) (zbytes (sublist 0 j db) ++ Zrepeat Vundef (Zlength db - j)) (offset_val (Zlength (ws_content ws) + 1) (Vptr bb ob)) :: R))))
      continue: (EX j: Z, PROPx [0 <= j < Zlength db] (LOCALx (temp _j (Vlong (Int64.repr j)) :: L)
         (SEPx (F :: data_at Ews (tarray tuchar (Zlength db)) (zbytes (sublist 0 (j + 1) db) ++ Zrepeat Vundef (Zlength db - (j + 1))) (offset_val (Zlength (ws_content ws) + 1) (Vptr bb ob)) :: R))))
      break: (PROPx [] (LOCALx (temp _j (Vlong (Int64.repr (Zlength db))) :: L)
         (SEPx (F :: data_at Ews (tarray tuchar (Zlength db)) (zbytes db) (offset_val (Zlength (ws_content ws) + 1) (Vptr bb ob)) :: R))))
  end.
  { Exists 0. entailer!. simpl app. cancel. }
  { Intros j. VL_ifs.
    1: assert (Hdn: Zlength db <> 0) by lia.
    1: assert (Hbj: is_byte (Znth j db)).
    1: { destruct H2 as [(_ & -> & _) | (_ & Hdok & _)]; [rewrite Zlength_nil in *; lia | apply Forall_Znth; auto; lia]. }
    1: unfold is_byte in Hbj.
    1: unfold VL_wdb; rewrite (proj2 (Z.eqb_neq _ _) Hdn).
    1: forward.
    1: { entailer!. rewrite VLB_content_at by lia. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    1: rewrite VLB_content_at by lia.
    1: forward.
    1: Exists j. 1: entailer!.
    1: rewrite (VLB_copy_step db j (Zlength db)) by (auto; lia). 1: cancel.
    assert (Hin: j = Zlength db) by lia. subst j.
    forward. entailer!. rewrite sublist_same by lia. rewrite Z.sub_diag. simpl. rewrite app_nil_r. cancel. }
  { Intros j. forward. Exists (j + 1). entailer!. }
  thaw FR1.
  rewrite (VLB_cs HCS ZCS Ews (Zlength db) (zbytes db) (offset_val (Zlength (ws_content ws) + 1) (Vptr bb ob))).
  match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
  forward_if (EX q: val, EX dd: ddict_st, EX stp: Z,
    PROPx [stp = 0 \/ stp = 1; stp = 0 -> VL_qok mode q; VL_ddok db dd]
    (LOCALx (temp _stop (Vint (Int.repr stp)) :: temp _ipos (Vlong (Int64.repr 0)) ::
             temp _pos (Vlong (Int64.repr 0)) :: VL_loc gv ws db mode (Vptr bs os) (Vptr bb ob) (Vptr bd od) q)
    (SEPx (VL_qres DD gv q dd :: R))))
  end.
  { assert (Hm2: mode = 2) by auto.
    assert (Hdn: 8 <= Zlength db /\ bytes_ok db)
      by (destruct H2 as [(? & _) | (_ & ? & ? & _)]; [lia | split; [lia | auto]]).
    forward_call ([] : list ptr_witness, gv, Ews, offset_val (Zlength (ws_content ws) + 1) (Vptr bb ob), db).
    { unfold pws_pred. cbn [map fold_right]. try rewrite bytes_at_ptr by exact I. cancel. }
    { split; [intro E; discriminate E | split; [intros _; apply VLB_buf_ok_nil; lia | tauto]]. }
    Intros vret. destruct vret as [q dd]. cbn [fst snd] in *. unfold pws_pred. cbn [map fold_right].
    rewrite bytes_at_ptr by exact I.
    match goal with H: dd_ref dd = _ |- _ => rewrite if_false in H by discriminate end.
    rewrite (proj2 (Z.eqb_neq (Zlength db) 0)) in * by lia.
    assert (Hdd: VL_ddok db dd) by (split; auto).
    destruct (eq_dec q nullval) as [Hq|Hq].
    - subst q. forward_if.
      + forward. Exists nullval dd 1. unfold VL_qres, VL_loc. rewrite if_true by auto. entailer!.
      + exfalso. auto.
    - assert (Hpq: isptr q) by (destruct q; simpl in *; try contradiction; auto; subst; contradiction).
      destruct q as [| | | | | bq oq]; try contradiction.
      forward_if.
      + discriminate.
      + forward. Exists (Vptr bq oq) dd 0.
        unfold VL_qres, VL_loc. rewrite if_false by discriminate. entailer!.
        split; intros; [auto | congruence]. }
  { forward. Exists nullval (VL_dd0 db) 0. unfold VL_qres, VL_loc. rewrite if_true by auto. entailer!.
    split; [split; [intros; lia | auto] | split; reflexivity]. }
  Intros q dd stp. unfold VL_loc.
  assert_PROP (field_compatible (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws)))) [] (Vptr bs os)) as Hfs by entailer!.
  rewrite (VLB_src_split (Vptr bs os) (ws_bytes ws) Hfs). Intros.
  rewrite (VLB_cs_ HCS ZCS Ews 1 (offset_val (Zlength (ws_content ws)) (Vptr bb ob))).
  sep_apply (VLB_wit_fold (Vptr bs os) (Zlength (ws_bytes ws)) (Vptr bb ob) (Zlength (ws_content ws))).
  rewrite (VLB_cs_ HCS ZCS Ews (Zlength (ws_content ws)) (Vptr bb ob)).
  rewrite (VLB_Zrepeat Ews (Zlength (ws_content ws)) (Vptr bb ob)).
  sep_apply (Hvp (DC gv (Vptr bd od) dctx_init) (Vptr bd od)).
  change (DC gv (Vptr bd od) dctx_init) with (DC gv (Vptr bd od) (set_ex (set_bl dctx_init None) true)).
  forward.
  forward_loop (VL_outer DC DD gv ws db dd mode (Vptr bs os) (Vptr bb ob) (Vptr bd od) q)
    continue: (VL_cont DC DD gv ws db dd mode (Vptr bs os) (Vptr bb ob) (Vptr bd od) q)
    break: (VL_exit DC DD gv ws db dd mode (Vptr bs os) (Vptr bb ob) (Vptr bd od) q).
  { unfold VL_outer, VL_sep, VL_loc.
    Exists 0 stp 0 0 (@None blabs) (Zrepeat Vundef (Zlength (ws_content ws))) true.
    entailer!.
    split; [apply Zlength_Zrepeat; rep_lia |].
    intros Hs0. split; [auto |]. intros _. unfold VL_f. change (Z.to_nat 0) with O.
    destruct (vbl_tiles_first dm ws H0 H1) as [-> ->]. auto. }
  { unfold VL_outer. Intros k stp' ipos pos obl oc ex. unfold VL_sep, VL_loc, VL_sr.
    match goal with Hx: 0 <= k <= _ |- _ => rename Hx into Hk end.
    match goal with Hx: stp' = 0 \/ stp' = 1 |- _ => rename Hx into Hstp end.
    match goal with Hx: stp' = 0 -> _ |- _ => rename Hx into Hst0 end.
    sep_apply (VLB_ws_unfold ws (gv _x_valid_bufferless__sr) Hnb). unfold VLB_sr_rest. Intros.
    forward.
    sep_apply (VLB_rest_fold ws (gv _x_valid_bufferless__sr)).
    sep_apply (VLB_ws_fold ws (gv _x_valid_bufferless__sr) Hnb).
    assert (Hnf': 1 <= Zlength (ws_frames ws) <= 4) by (rewrite Zlength_correct; lia).
    destruct (zlt k (Zlength (ws_frames ws))) as [Hlt|Hge]; [destruct Hstp as [-> | ->] |].
    - forward_if (temp _x_valid_bufferless__t'8 (Vint (Int.repr 1))).
      { forward. entailer!. }
      { exfalso. rep_lia. }
      forward_if; [| exfalso; match goal with Hx: Int.repr 1 = Int.zero |- _ => exact (Int.one_not_zero Hx) end].
      destruct (Hst0 eq_refl) as [Hqok Hpos]. destruct (Hpos Hlt) as [-> ->].
      eapply semax_pre; [| apply (VL_frame_ok VL_inner_ok Espec DC DD WG WDS gv ws db dd dm mode (Vptr bs os) (Vptr bb ob) (Vptr bd od) q k
                                   (wi_start (VL_f ws k)) (wi_cstart (VL_f ws k)) obl oc ex)].
      + unfold VL_sep, VL_loc, VL_sr. entailer!.
      + split; [lia | split; [auto | split; [auto | split; [auto | split; [eauto | split; [eauto | split; [eauto | split; auto]]]]]]].
      + lia.
      + auto.
      + auto.
      + reflexivity.
      + reflexivity.
      + auto.
    - forward_if (temp _x_valid_bufferless__t'8 (Vint (Int.repr 0))).
      { forward. entailer!. }
      { exfalso. rep_lia. }
      forward_if; [exfalso; match goal with Hx: Int.repr 0 <> Int.zero |- _ => exact (Hx eq_refl) end |].
      forward. unfold VL_exit, VL_sep, VL_loc, VL_sr. Exists obl oc ex. entailer!.
    - forward_if (temp _x_valid_bufferless__t'8 (Vint (Int.repr 0))).
      { exfalso. rep_lia. }
      { forward. entailer!. }
      forward_if; [exfalso; match goal with Hx: Int.repr 0 <> Int.zero |- _ => exact (Hx eq_refl) end |].
      forward. unfold VL_exit, VL_sep, VL_loc, VL_sr. Exists obl oc ex. entailer!. }
  { unfold VL_cont. Intros k stp' ipos pos obl oc ex. unfold VL_loc.
    forward. unfold VL_outer, VL_loc. Exists (k + 1) stp' ipos pos obl oc ex. entailer!. }
  unfold VL_exit, VL_sep, VL_loc, VL_sr. Intros obl oc ex.
  assert (Hqd: VL_qres DD gv q dd |--
    match (if eq_dec q nullval then None else Some dd) with None => emp | Some x => DD gv q x end)
    by (unfold VL_qres; destruct (eq_dec q nullval); [apply derives_refl | apply Hvp]).
  sep_apply Hqd.
  forward_call (gv, q, if eq_dec q nullval then None else Some dd).
  { destruct (eq_dec q nullval); auto. }
  forward_call (gv, Vptr bd od, Some (set_ex (set_bl dctx_init obl) ex)).
  sep_apply (VLB_final_merge (Vptr bs os) (Zlength (ws_bytes ws)) (Vptr bb ob) (Zlength (ws_content ws)) (Zlength db) oc
               (zbytes db) (zbytes (ws_bytes ws)) ltac:(rep_lia) ltac:(rep_lia) ltac:(rep_lia) Hfs Hfb).
  forward_call (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws))), Vptr bs os, gv).
  { rewrite if_false by discriminate. cancel. }
  forward_call (tarray tuchar (Zlength (ws_content ws) + 1 + Zlength db), Vptr bb ob, gv).
  { rewrite if_false by discriminate. cancel. }
  eapply semax_pre with (P' := PROP () LOCAL () SEP (TT)).
  { go_lower. apply TT_right. }
  forward.
Qed.
End Body.
