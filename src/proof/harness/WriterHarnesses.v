(* The harness obligations of the 10 harnesses that use the writer (harness/writer.h), under the decoder's API v3:
   for ANY predicates DC, DD of the decoder's API (Spec_api6), specifications of each harness's helpers (the
   writer's functions, zlimits.h, its own) such that every helper and main satisfy them (the facts the writer must
   establish: model/WriterFacts.v).
   The 7 harnesses detect, stable_out, valid_dict, valid_dict_copy, valid_info, valid_oneshot, valid_stream were
   first proved against API v2 (WriterInternals, MainLift, WMain_<h>, WriterOK_<h>) and adapted to v3;
   valid_bufferless, valid_dict_api and valid_params were added by a later revision of the contract. *)
Require Import VST.floyd.proofauto.
Require Export Zstd.proof.zstd.Spec_api6.
Require Zstd.proof.harness.detect.HOK_detect.
Require Zstd.proof.harness.stable_out.HOK_stable_out.
Require Zstd.proof.harness.valid_bufferless.HOK_valid_bufferless.
Require Zstd.proof.harness.valid_dict.HOK_valid_dict.
Require Zstd.proof.harness.valid_dict_api.HOK_valid_dict_api.
Require Zstd.proof.harness.valid_dict_copy.HOK_valid_dict_copy.
Require Zstd.proof.harness.valid_info.HOK_valid_info.
Require Zstd.proof.harness.valid_oneshot.HOK_valid_oneshot.
Require Zstd.proof.harness.valid_params.HOK_valid_params.
Require Zstd.proof.harness.valid_stream.HOK_valid_stream.
Require Zstd.proof.harness.detect.WMain3_detect.
Require Zstd.proof.harness.stable_out.WMain3_stable_out.
Require Zstd.proof.harness.valid_bufferless.WMain3_valid_bufferless.
Require Zstd.proof.harness.valid_dict.WMain3_valid_dict.
Require Zstd.proof.harness.valid_dict_api.WMain3_valid_dict_api.
Require Zstd.proof.harness.valid_dict_copy.WMain3_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WMain3_valid_info.
Require Zstd.proof.harness.valid_oneshot.WMain3_valid_oneshot.
Require Zstd.proof.harness.valid_params.WMain3_valid_params.
Require Zstd.proof.harness.valid_stream.WMain3_valid_stream.
Require Zstd.proof.harness.writer.WriterInternals Zstd.proof.harness.writer.MainLift.
Require Zstd.proof.harness.writer.WriterInternals3.
Require Zstd.proof.harness.valid_dict_api.WSide_valid_dict_api.
Import compcert.lib.Maps.

(* one v2 unit: the writer's internals (WriterOK), main in G0 (MainOK, v3), lifted to Gprog (LiftOK) *)
Lemma unit_ok_detect :
  Zstd.proof.harness.detect.WriterOK_detect.WriterOK -> Zstd.proof.harness.detect.WriterOK_detect.LiftOK ->
  forall (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred),
    exists Hs, Zstd.proof.harness.detect.HOK_detect.HarnessOK (Specs_api DC DD) Hs.
Proof.
  intros [WG [WDS [Hs [Hinit [Hfst [Htop Hbodies]]]]]] Hlift DC DD.
  exists Hs. split; [exact Hfst |].
  apply Forall_app; split; [apply Hbodies |].
  constructor; [| constructor].
  exists Zstd.harness.x_detect.code.f_main. split; [vm_compute; reflexivity |]. split; [reflexivity |].
  apply (Hlift DC DD WG WDS Hs Hfst Htop). exact (Zstd.proof.harness.detect.WMain3_detect.main_ok3_detect DC DD WG WDS Hinit).
Qed.

(* one v2 unit: the writer's internals (WriterOK), main in G0 (MainOK, v3), lifted to Gprog (LiftOK) *)
Lemma unit_ok_stable_out :
  Zstd.proof.harness.stable_out.WriterOK_stable_out.WriterOK -> Zstd.proof.harness.stable_out.WriterOK_stable_out.LiftOK ->
  forall (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred),
    exists Hs, Zstd.proof.harness.stable_out.HOK_stable_out.HarnessOK (Specs_api DC DD) Hs.
Proof.
  intros [WG [WDS [Hs [Hinit [Hfst [Htop Hbodies]]]]]] Hlift DC DD.
  exists Hs. split; [exact Hfst |].
  apply Forall_app; split; [apply Hbodies |].
  constructor; [| constructor].
  exists Zstd.harness.x_stable_out.code.f_main. split; [vm_compute; reflexivity |]. split; [reflexivity |].
  apply (Hlift DC DD WG WDS Hs Hfst Htop). exact (Zstd.proof.harness.stable_out.WMain3_stable_out.main_ok3_stable_out DC DD WG WDS Hinit).
Qed.

(* one v2 unit: the writer's internals (WriterOK), main in G0 (MainOK, v3), lifted to Gprog (LiftOK) *)
Lemma unit_ok_valid_dict :
  Zstd.proof.harness.valid_dict.WriterOK_valid_dict.WriterOK -> Zstd.proof.harness.valid_dict.WriterOK_valid_dict.LiftOK ->
  forall (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred),
    exists Hs, Zstd.proof.harness.valid_dict.HOK_valid_dict.HarnessOK (Specs_api DC DD) Hs.
Proof.
  intros [WG [WDS [Hs [Hinit [Hfst [Htop Hbodies]]]]]] Hlift DC DD.
  exists Hs. split; [exact Hfst |].
  apply Forall_app; split; [apply Hbodies |].
  constructor; [| constructor].
  exists Zstd.harness.x_valid_dict.code.f_main. split; [vm_compute; reflexivity |]. split; [reflexivity |].
  apply (Hlift DC DD WG WDS Hs Hfst Htop). exact (Zstd.proof.harness.valid_dict.WMain3_valid_dict.main_ok3_valid_dict DC DD WG WDS Hinit).
Qed.

(* one v2 unit: the writer's internals (WriterOK), main in G0 (MainOK, v3), lifted to Gprog (LiftOK) *)
Lemma unit_ok_valid_dict_copy :
  Zstd.proof.harness.valid_dict_copy.WriterOK_valid_dict_copy.WriterOK -> Zstd.proof.harness.valid_dict_copy.WriterOK_valid_dict_copy.LiftOK ->
  forall (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred),
    exists Hs, Zstd.proof.harness.valid_dict_copy.HOK_valid_dict_copy.HarnessOK (Specs_api DC DD) Hs.
Proof.
  intros [WG [WDS [Hs [Hinit [Hfst [Htop Hbodies]]]]]] Hlift DC DD.
  exists Hs. split; [exact Hfst |].
  apply Forall_app; split; [apply Hbodies |].
  constructor; [| constructor].
  exists Zstd.harness.x_valid_dict_copy.code.f_main. split; [vm_compute; reflexivity |]. split; [reflexivity |].
  apply (Hlift DC DD WG WDS Hs Hfst Htop). exact (Zstd.proof.harness.valid_dict_copy.WMain3_valid_dict_copy.main_ok3_valid_dict_copy DC DD WG WDS Hinit).
Qed.

(* one v2 unit: the writer's internals (WriterOK), main in G0 (MainOK, v3), lifted to Gprog (LiftOK) *)
Lemma unit_ok_valid_info :
  Zstd.proof.harness.valid_info.WriterOK_valid_info.WriterOK -> Zstd.proof.harness.valid_info.WriterOK_valid_info.LiftOK ->
  forall (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred),
    exists Hs, Zstd.proof.harness.valid_info.HOK_valid_info.HarnessOK (Specs_api DC DD) Hs.
Proof.
  intros [WG [WDS [Hs [Hinit [Hfst [Htop Hbodies]]]]]] Hlift DC DD.
  exists Hs. split; [exact Hfst |].
  apply Forall_app; split; [apply Hbodies |].
  constructor; [| constructor].
  exists Zstd.harness.x_valid_info.code.f_main. split; [vm_compute; reflexivity |]. split; [reflexivity |].
  apply (Hlift DC DD WG WDS Hs Hfst Htop). exact (Zstd.proof.harness.valid_info.WMain3_valid_info.main_ok3_valid_info DC DD WG WDS Hinit).
Qed.

(* one v2 unit: the writer's internals (WriterOK), main in G0 (MainOK, v3), lifted to Gprog (LiftOK) *)
Lemma unit_ok_valid_oneshot :
  Zstd.proof.harness.valid_oneshot.WriterOK_valid_oneshot.WriterOK -> Zstd.proof.harness.valid_oneshot.WriterOK_valid_oneshot.LiftOK ->
  forall (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred),
    exists Hs, Zstd.proof.harness.valid_oneshot.HOK_valid_oneshot.HarnessOK (Specs_api DC DD) Hs.
Proof.
  intros [WG [WDS [Hs [Hinit [Hfst [Htop Hbodies]]]]]] Hlift DC DD.
  exists Hs. split; [exact Hfst |].
  apply Forall_app; split; [apply Hbodies |].
  constructor; [| constructor].
  exists Zstd.harness.x_valid_oneshot.code.f_main. split; [vm_compute; reflexivity |]. split; [reflexivity |].
  apply (Hlift DC DD WG WDS Hs Hfst Htop). exact (Zstd.proof.harness.valid_oneshot.WMain3_valid_oneshot.main_ok3_valid_oneshot DC DD WG WDS Hinit).
Qed.

(* one v2 unit: the writer's internals (WriterOK), main in G0 (MainOK, v3), lifted to Gprog (LiftOK) *)
Lemma unit_ok_valid_stream :
  Zstd.proof.harness.valid_stream.WriterOK_valid_stream.WriterOK -> Zstd.proof.harness.valid_stream.WriterOK_valid_stream.LiftOK ->
  forall (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred),
    exists Hs, Zstd.proof.harness.valid_stream.HOK_valid_stream.HarnessOK (Specs_api DC DD) Hs.
Proof.
  intros [WG [WDS [Hs [Hinit [Hfst [Htop Hbodies]]]]]] Hlift DC DD.
  exists Hs. split; [exact Hfst |].
  apply Forall_app; split; [apply Hbodies |].
  constructor; [| constructor].
  exists Zstd.harness.x_valid_stream.code.f_main. split; [vm_compute; reflexivity |]. split; [reflexivity |].
  apply (Hlift DC DD WG WDS Hs Hfst Htop). exact (Zstd.proof.harness.valid_stream.WMain3_valid_stream.main_ok3_valid_stream DC DD WG WDS Hinit).
Qed.

(* ---------- the 3 v3 units (the v3 template WriterOK: Hs per API, main-side helpers proved in G0) ---------- *)

Lemma wh_forall_filter {A} (P: A -> Prop) (f: A -> bool) (l: list A) :
  Forall P (filter f l) -> Forall P (filter (fun x => negb (f x)) l) -> Forall P l.
Proof.
  rewrite !Forall_forall. intros H1 H2 x Hx.
  destruct (f x) eqn:E; [apply H1 | apply H2]; apply filter_In; rewrite ?E; auto.
Qed.

Lemma wh_find_id_in (l: funspecs) i fs :
  NoDup (map fst l) -> In (i, fs) l -> initial_world.find_id i l = Some fs.
Proof.
  induction l as [|[j gs] l IH]; simpl; [tauto|]. intros Hnd [E|Hin].
  - inversion E; subst. rewrite if_true by reflexivity. reflexivity.
  - inversion Hnd as [|? ? Hj Hnd']; subst.
    rewrite if_false. { apply IH; auto. }
    intros ->. apply Hj. apply (in_map fst) in Hin. exact Hin.
Qed.

(* a helper of Hs whose ident is main-side is the top-level specification of that ident *)
Lemma wh_side_in (Hs W: funspecs) (S: list ident) ix :
  NoDup (map fst Hs) -> Forall (fun jx => initial_world.find_id (fst jx) Hs = Some (snd jx)) W ->
  (forall i, id_in_list i S = true -> In i (map fst W)) ->
  In ix Hs -> id_in_list (fst ix) S = true ->
  In ix (filter (fun jx => id_in_list (fst jx) S) W).
Proof.
  intros Hnd HW HS Hin Hs'. destruct ix as [i fs].
  pose proof (HS i Hs') as Hi. apply list_in_map_inv in Hi as [[j gs] [Ej Hj]]. simpl in Ej; subst j.
  rewrite Forall_forall in HW. pose proof (HW _ Hj) as Hf. simpl in Hf.
  rewrite (wh_find_id_in Hs i fs Hnd Hin) in Hf. inversion Hf; subst gs.
  apply filter_In. split; auto.
Qed.

Ltac unit3_ok U MS WT :=
  intros [WG [WDS [Hinit Hw]]] Hside Hmain DC DD;
  destruct (Hw DC DD) as [Hs [Hfst [Htop Hbodies]]];
  exists Hs; split; [exact Hfst |];
  apply Forall_app; split;
  [ apply (wh_forall_filter _ (fun ix => id_in_list (fst ix) MS)); [| exact Hbodies];
    rewrite Forall_forall; intros ix Hix; apply filter_In in Hix as [Hix Hsd];
    pose proof (Hside DC DD WG WDS) as HS; rewrite Forall_forall in HS;
    assert (Hin: In ix (filter (fun jx => id_in_list (fst jx) MS) (WT DC DD WG WDS)));
    [ apply (wh_side_in Hs (WT DC DD WG WDS) MS ix); auto;
      [ rewrite Hfst; vm_compute; repeat constructor; simpl; intuition discriminate
      | intros i Hi; apply id_in_list_true in Hi; unfold MS in Hi; simpl in Hi;
        repeat (destruct Hi as [<-|Hi]; [vm_compute; tauto|]); contradiction ]
    | destruct (HS ix Hin) as [f [Hf [Hcc Hb]]];
      exists f; split; [exact Hf|]; split; [exact Hcc|];
      eapply Zstd.proof.harness.writer.MainLift.ml_lift; [exact Htop | | exact Hb];
      rewrite map_app, Hfst; apply Zstd.proof.harness.writer.MainLift.ml_disj; vm_compute; reflexivity ]
  | constructor; [| constructor];
    exists U; split; [vm_compute; reflexivity |]; split; [reflexivity |];
    eapply Zstd.proof.harness.writer.MainLift.ml_lift; [exact Htop | | exact (Hmain DC DD WG WDS Hinit)];
    rewrite map_app, Hfst; apply Zstd.proof.harness.writer.MainLift.ml_disj; vm_compute; reflexivity ].

Lemma unit_ok_valid_bufferless :
  Zstd.proof.harness.valid_bufferless.WriterOK_valid_bufferless.WriterOK -> Zstd.proof.harness.valid_bufferless.WriterOK_valid_bufferless.SideOK -> Zstd.proof.harness.valid_bufferless.WTopSpecs_valid_bufferless.MainOK ->
  forall (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred),
    exists Hs, Zstd.proof.harness.valid_bufferless.HOK_valid_bufferless.HarnessOK (Specs_api DC DD) Hs.
Proof.
  unit3_ok Zstd.harness.x_valid_bufferless.code.f_main Zstd.proof.harness.valid_bufferless.WTopSpecs_valid_bufferless.main_side_ids Zstd.proof.harness.valid_bufferless.WTopSpecs_valid_bufferless.wtop_specs.
Qed.

Lemma unit_ok_valid_dict_api :
  Zstd.proof.harness.valid_dict_api.WriterOK_valid_dict_api.WriterOK -> Zstd.proof.harness.valid_dict_api.WriterOK_valid_dict_api.SideOK -> Zstd.proof.harness.valid_dict_api.WTopSpecs_valid_dict_api.MainOK ->
  forall (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred),
    exists Hs, Zstd.proof.harness.valid_dict_api.HOK_valid_dict_api.HarnessOK (Specs_api DC DD) Hs.
Proof.
  unit3_ok Zstd.harness.x_valid_dict_api.code.f_main Zstd.proof.harness.valid_dict_api.WTopSpecs_valid_dict_api.main_side_ids Zstd.proof.harness.valid_dict_api.WTopSpecs_valid_dict_api.wtop_specs.
Qed.

Lemma unit_ok_valid_params :
  Zstd.proof.harness.valid_params.WriterOK_valid_params.WriterOK -> Zstd.proof.harness.valid_params.WriterOK_valid_params.SideOK -> Zstd.proof.harness.valid_params.WTopSpecs_valid_params.MainOK ->
  forall (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred),
    exists Hs, Zstd.proof.harness.valid_params.HOK_valid_params.HarnessOK (Specs_api DC DD) Hs.
Proof.
  unit3_ok Zstd.harness.x_valid_params.code.f_main Zstd.proof.harness.valid_params.WTopSpecs_valid_params.main_side_ids Zstd.proof.harness.valid_params.WTopSpecs_valid_params.wtop_specs.
Qed.

Theorem writer_harnesses_ok :
  forall (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred),
    (exists Hs, Zstd.proof.harness.detect.HOK_detect.HarnessOK (Specs_api DC DD) Hs) /\
    (exists Hs, Zstd.proof.harness.stable_out.HOK_stable_out.HarnessOK (Specs_api DC DD) Hs) /\
    (exists Hs, Zstd.proof.harness.valid_bufferless.HOK_valid_bufferless.HarnessOK (Specs_api DC DD) Hs) /\
    (exists Hs, Zstd.proof.harness.valid_dict.HOK_valid_dict.HarnessOK (Specs_api DC DD) Hs) /\
    (exists Hs, Zstd.proof.harness.valid_dict_api.HOK_valid_dict_api.HarnessOK (Specs_api DC DD) Hs) /\
    (exists Hs, Zstd.proof.harness.valid_dict_copy.HOK_valid_dict_copy.HarnessOK (Specs_api DC DD) Hs) /\
    (exists Hs, Zstd.proof.harness.valid_info.HOK_valid_info.HarnessOK (Specs_api DC DD) Hs) /\
    (exists Hs, Zstd.proof.harness.valid_oneshot.HOK_valid_oneshot.HarnessOK (Specs_api DC DD) Hs) /\
    (exists Hs, Zstd.proof.harness.valid_params.HOK_valid_params.HarnessOK (Specs_api DC DD) Hs) /\
    (exists Hs, Zstd.proof.harness.valid_stream.HOK_valid_stream.HarnessOK (Specs_api DC DD) Hs).
Proof.
  intros DC DD.
  destruct Zstd.proof.harness.writer.WriterInternals.writer_internals_ok as [W1 [W2 [W3 [W4 [W5 [W6 W7]]]]]].
  destruct Zstd.proof.harness.writer.MainLift.main_lift_ok as [L1 [L2 [L3 [L4 [L5 [L6 L7]]]]]].
  destruct Zstd.proof.harness.writer.WriterInternals3.writer_internals3_ok as [N1 [N2 N3]].
  split; [apply unit_ok_detect; assumption |].
  split; [apply unit_ok_stable_out; assumption |].
  split; [apply unit_ok_valid_bufferless;
          [exact N1 | | exact Zstd.proof.harness.valid_bufferless.WMain3_valid_bufferless.main_ok3_valid_bufferless] |].
  { intros DC' DD' WG WDS. constructor. }
  split; [apply unit_ok_valid_dict; assumption |].
  split; [apply unit_ok_valid_dict_api;
          [exact N2 | exact Zstd.proof.harness.valid_dict_api.WSide_valid_dict_api.side_ok_valid_dict_api
           | exact Zstd.proof.harness.valid_dict_api.WMain3_valid_dict_api.main_ok3_valid_dict_api] |].
  split; [apply unit_ok_valid_dict_copy; assumption |].
  split; [apply unit_ok_valid_info; assumption |].
  split; [apply unit_ok_valid_oneshot; assumption |].
  split; [apply unit_ok_valid_params;
          [exact N3 | | exact Zstd.proof.harness.valid_params.WMain3_valid_params.main_ok3_valid_params] |].
  { intros DC' DD' WG WDS. constructor. }
  apply unit_ok_valid_stream; assumption.
Qed.
