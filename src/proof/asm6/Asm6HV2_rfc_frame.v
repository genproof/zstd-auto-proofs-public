(* The law rfc_frame: harness_safe of its whole program from the units' obligations (Asm6Generic.law_safe);
   here only the conditions on the code of the harness unit and of the whole program, by computation. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.veric.Clight_initial_world.
Require Import QuickProof.Contract.
Require Import Zstd.proof.asm6.Asm6Lib Zstd.proof.asm6.Asm6LinkLib Zstd.proof.asm6.Asm6GenericV2.
Require Import Zstd.proof.top.ZstdOK6 Zstd.proof.top.HarnessDefs.
Require Import Zstd.proof.libc.LibcBodies.
Require Zstd.proof.harness.rfc_frame.HOK_rfc_frame.
Require Zstd.units Zstd.contracts.rfc_frame Zstd.harness.rfc_frame.code Zstd.proof.zstd.Base.
Import compcert.lib.Maps.

Module P := Zstd.contracts.rfc_frame.

Lemma L1 : QPlink_progs Zstd.units.Libc.qp Zstd.units.Zstd.qp = Errors.OK P.link_Libc.
Proof. vm_compute. reflexivity. Qed.
Lemma L2 : QPlink_progs Zstd.units.Malloc.qp P.link_Libc = Errors.OK P.link_Malloc.
Proof. vm_compute. reflexivity. Qed.
Lemma L3 : QPlink_progs P.Harness.qp P.link_Malloc = Errors.OK P.whole_prog.
Proof. vm_compute. reflexivity. Qed.

Lemma OKH : QPprogram_OK P.Harness.qp.
Proof.
  split; [apply compute_list_norepet_e; reflexivity | ].
  let HA := fresh in let LA := fresh in
  assert (HA: PTree_samedom (@cenv_cs P.Harness.CS) (@ha_env_cs P.Harness.CS)) by repeat constructor;
  assert (LA: PTree_samedom (@cenv_cs P.Harness.CS) (@la_env_cs P.Harness.CS)) by repeat constructor;
  exact (@QPcompspecs_OK_i P.Harness.CS HA LA).
Qed.

Lemma CSeqH : P.Harness.CS = compspecs_of_QPcomposite_env _ (proj2 OKH).
Proof. apply (compspecs_eq_of_QPcomposite_env P.Harness.CS Zstd.harness.rfc_frame.code.prog). reflexivity. Qed.

Lemma FOKH : prog_funs_ok P.Harness.CS P.Harness.qp = true.
Proof. vm_compute. reflexivity. Qed.

Lemma CBC: forall H, cenv_built_correctly
        (map compdef_of_compenv_element (sort_rank (PTree.elements (QP.prog_comp_env P.whole_prog)) []))
        (composite_env_of_QPcomposite_env (QP.prog_comp_env P.whole_prog) H) = Errors.OK tt.
Proof. intros. vm_compute. reflexivity. Qed.

Lemma UNSPEC: all_unspecified_OK P.whole_prog.
Proof. vm_compute. reflexivity. Qed.

Lemma ALIGNED: QPall_initializers_aligned P.whole_prog = true.
Proof. vm_compute. reflexivity. Qed.

Lemma NOTBUILTIN: forallb not_builtin (PTree.elements (QP.prog_defs P.whole_prog)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma MAINDEF: isSome (PTree.get (QP.prog_main P.whole_prog) (QP.prog_defs P.whole_prog)).
Proof. vm_compute. exact I. Qed.

Lemma MAIN_eq : QP.prog_main P.whole_prog = Zstd.harness.rfc_frame.code._main.
Proof. vm_compute. reflexivity. Qed.

Lemma NR_W : list_norepet (map fst (QPvarspecs P.whole_prog) ++
                           ids_W P.Harness.qp P.whole_prog Zstd.harness.rfc_frame.code._main).
Proof. apply compute_list_norepet_e. vm_compute. reflexivity. Qed.

Lemma DOM_W : forall i, In i (IntIDs P.whole_prog ++ Eids P.whole_prog) <->
                        In i (ids_W P.Harness.qp P.whole_prog Zstd.harness.rfc_frame.code._main).
Proof. apply same_ids; vm_compute; reflexivity. Qed.

Lemma EXTDEF : forall i, In i (Eids P.whole_prog) -> (QP.prog_defs P.whole_prog) ! i = env_def i.
Proof.
  intros i Hi. vm_compute in Hi.
  repeat (destruct Hi as [<-|Hi]; [vm_compute; reflexivity|]). destruct Hi.
Qed.

Lemma EMF : In _quickproof_malloc (Eids P.whole_prog) /\ In _quickproof_free (Eids P.whole_prog).
Proof. split; apply id_in_list_true; vm_compute; reflexivity. Qed.

Lemma EXTH : forall i, In i env_harness_ids -> In i (ExtIDs P.Harness.qp) -> In i (Eids P.whole_prog).
Proof.
  intros i H1 H2. unfold env_harness_ids in H1.
  (* both id lists computed once, so that each case below works on short literal lists *)
  let e := eval vm_compute in (Eids P.whole_prog) in replace (Eids P.whole_prog) with e by (vm_compute; reflexivity).
  let x := eval vm_compute in (ExtIDs P.Harness.qp) in replace (ExtIDs P.Harness.qp) with x in H2 by (vm_compute; reflexivity).
  repeat (destruct H1 as [<-|H1];
    [first [apply id_in_list_true; vm_compute; reflexivity
           | apply assoclists.id_in_list_true_i in H2; vm_compute in H2; discriminate] |]).
  destruct H1.
Qed.

Lemma VZ : vars_in Zstd.proof.zstd.Base.Vprog (QPvarspecs P.whole_prog) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma VL : vars_in Zstd.proof.libc.LibcBodies.Vprog (QPvarspecs P.whole_prog) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma NR_H : list_norepet (helper_ids_g P.Harness.qp Zstd.harness.rfc_frame.code._main ++ [Zstd.harness.rfc_frame.code._main]).
Proof. apply compute_list_norepet_e. vm_compute. reflexivity. Qed.

Lemma HOK_conv API Hs : Zstd.proof.harness.rfc_frame.HOK_rfc_frame.HarnessOK API Hs ->
  HarnessOK_g P.Harness.qp P.Harness.CS P.whole_prog Zstd.harness.rfc_frame.code._main API Hs.
Proof.
  unfold Zstd.proof.harness.rfc_frame.HOK_rfc_frame.HarnessOK, HarnessOK_g, Zstd.proof.harness.rfc_frame.HOK_rfc_frame.helper_ids, helper_ids_g, Zstd.proof.harness.rfc_frame.HOK_rfc_frame.Gprog, Gprog_g,
    Zstd.proof.harness.rfc_frame.HOK_rfc_frame.Imports, Imports_g, Zstd.proof.harness.rfc_frame.HOK_rfc_frame.Externals, Externals_g, Zstd.proof.harness.rfc_frame.HOK_rfc_frame.main_spec, main_spec_g,
    Zstd.proof.harness.rfc_frame.HOK_rfc_frame.hbody_ok, hbody_ok_g, Zstd.proof.harness.rfc_frame.HOK_rfc_frame.Vprog, Zstd.proof.harness.rfc_frame.HOK_rfc_frame.CompSpecs.
  intros X. exact X.
Qed.

Theorem safe_rfc_frame : forall (Int API: funspecs),
  ZstdOK Int -> api_sub API Int -> ~ In _memcpy (map fst API) -> LibcBodies ->
  forall Hs, Zstd.proof.harness.rfc_frame.HOK_rfc_frame.HarnessOK API Hs -> harness_safe P.whole_prog.
Proof.
  intros Int API ZOK ASUB NMC LB Hs HOK.
  exact (law_safe P.Harness.qp P.Harness.CS Zstd.harness.rfc_frame.code._main P.whole_prog P.link_Libc P.link_Malloc
           L1 L2 L3 OKH CSeqH FOKH CBC UNSPEC ALIGNED NOTBUILTIN MAINDEF MAIN_eq NR_W DOM_W EXTDEF EMF EXTH
           VZ VL NR_H Int API ZOK ASUB NMC LB Hs (HOK_conv API Hs HOK)).
Qed.
