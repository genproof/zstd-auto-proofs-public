(* main_pre of valid_params's whole program, split for main: the
   decoder's globals, the writer's statics (wvardefs, which MainOK turns into WG gv), and the harness's static
   sr, zero-initialized. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Export Zstd.proof.harness.valid_params.WTopSpecs_valid_params.
Require Zstd.proof.top.MainPre6.

Lemma VPP_filter_filter {A: Type} (g h: A -> bool) l:
  (forall x, h x = true -> g x = true) -> filter h (filter g l) = filter h l.
Proof.
  intros Hgh. induction l as [|a l IH]; simpl; auto.
  destruct (g a) eqn:Ha; simpl; rewrite ?IH; auto.
  destruct (h a) eqn:Hb; auto. rewrite (Hgh a Hb) in Ha. discriminate.
Qed.

Lemma VPP_InitGPred_in x l gv: In x l -> InitGPred l gv |-- globs2pred gv x * TT.
Proof.
  intros Hin. apply in_split in Hin as [l1 [l2 ->]].
  rewrite (Zstd.proof.top.MainPre6.MP_InitGPred_perm _ (x :: l1 ++ l2) gv)
    by (symmetry; apply Permutation_middle).
  rewrite InitGPred_consD. apply sepcon_derives; [apply derives_refl | apply TT_right].
Qed.

Lemma VPP_wnot_zstd:
  forallb (fun i => negb (id_in_list i Zstd.proof.top.MainPre6.zstd_var_ids)) wvar_ids = true.
Proof. vm_compute. reflexivity. Qed.

Lemma VPP_sr_in:
  In (_x_valid_params__sr, Gvar v_x_valid_params__sr) (Vardefs Zstd.contracts.x_valid_params.whole_prog).
Proof.
  unfold Vardefs. apply filter_In. split; [ | reflexivity].
  apply Maps.PTree.elements_correct. vm_compute. reflexivity.
Qed.

Lemma VPP_sr_data gv:
  globs2pred gv (_x_valid_params__sr, Gvar v_x_valid_params__sr) |--
    @data_at Zstd.proof.harness.valid_params.HOK_valid_params.CompSpecs Ews t_wseries
      (@zero_val Zstd.proof.harness.valid_params.HOK_valid_params.CompSpecs t_wseries)
      (gv _x_valid_params__sr).
Proof.
  unfold globs2pred, globvar2pred. simpl.
  apply derives_extract_prop; intros Hh. rewrite sepcon_emp.
  change 786936 with (@sizeof Zstd.proof.harness.valid_params.HOK_valid_params.CompSpecs t_wseries).
  apply mapsto_zero_data_at_zero.
  - apply writable_readable. apply writable_Ews.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - apply headptr_field_compatible; auto.
    all: first [ apply la_env_cs_sound; vm_compute; reflexivity | solve [simpl; auto]
               | vm_compute; reflexivity ].
Qed.

Lemma VP_pre gv : globals_ok gv ->
  InitGPred (Vardefs Zstd.contracts.x_valid_params.whole_prog) gv |--
    Zstd.proof.zstd.Globals.zstd_globals gv *
    (InitGPred wvardefs gv *
     (@data_at Zstd.proof.harness.valid_params.HOK_valid_params.CompSpecs Ews t_wseries
        (@zero_val Zstd.proof.harness.valid_params.HOK_valid_params.CompSpecs t_wseries)
        (gv _x_valid_params__sr) * TT)).
Proof.
  intros Hgv.
  eapply derives_trans.
  { apply (Zstd.proof.top.MainPre6.main_pre_fact6 Zstd.contracts.x_valid_params.whole_prog); auto.
    unfold Zstd.proof.top.MainPre6.all_progs. do 18 right; left; reflexivity. }
  apply sepcon_derives; [apply derives_refl | ].
  rewrite (Zstd.proof.top.MainPre6.MP_InitGPred_filter (fun ig => id_in_list (fst ig) wvar_ids)).
  apply sepcon_derives.
  - unfold wvardefs. rewrite VPP_filter_filter; [apply derives_refl | ].
    intros [i g] Hi. simpl in Hi |- *.
    pose proof VPP_wnot_zstd as Hw. rewrite forallb_forall in Hw.
    apply Hw. apply id_in_list_true. exact Hi.
  - eapply derives_trans; [apply VPP_InitGPred_in | ].
    + apply filter_In. split; [apply filter_In; split; [apply VPP_sr_in | ] | ];
        vm_compute; reflexivity.
    + apply sepcon_derives; [apply VPP_sr_data | apply derives_refl].
Qed.
