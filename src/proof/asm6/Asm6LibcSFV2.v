(* The libc unit's and the malloc unit's functions in a whole program: their SF obligations at the
   whole program's compspecs CSW, in any whole function context G' containing the libc unit's
   specifications verbatim and the environment's malloc at CSW.  The malloc unit's only function,
   malloc_placeholder, has the vacuous specification. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Env.
Require Import Zstd.proof.asm6.Asm6Lib Zstd.proof.asm6.Asm6CS Zstd.proof.asm6.Asm6Transfer.
Require Import Zstd.proof.libc.LibcBodies.
Require Zstd.units Zstd.malloc.code Zstd.proof.zstd.Base.
Require Import VST.veric.Clight_initial_world.
Import compcert.lib.Maps.

Lemma OK_Libc : QPprogram_OK Zstd.units.Libc.qp.
Proof.
  split; [apply compute_list_norepet_e; reflexivity | ].
  let HA := fresh in let LA := fresh in
  assert (HA: PTree_samedom (@cenv_cs Zstd.units.Libc.CS) (@ha_env_cs Zstd.units.Libc.CS)) by repeat constructor;
  assert (LA: PTree_samedom (@cenv_cs Zstd.units.Libc.CS) (@la_env_cs Zstd.units.Libc.CS)) by repeat constructor;
  exact (@QPcompspecs_OK_i Zstd.units.Libc.CS HA LA).
Qed.

Lemma CSeq_Libc : Zstd.units.Libc.CS = compspecs_of_QPcomposite_env _ (proj2 OK_Libc).
Proof. apply (compspecs_eq_of_QPcomposite_env Zstd.units.Libc.CS Zstd.libc.code.prog). reflexivity. Qed.

Lemma OK_Malloc : QPprogram_OK Zstd.units.Malloc.qp.
Proof.
  split; [apply compute_list_norepet_e; reflexivity | ].
  let HA := fresh in let LA := fresh in
  assert (HA: PTree_samedom (@cenv_cs Zstd.units.Malloc.CS) (@ha_env_cs Zstd.units.Malloc.CS)) by repeat constructor;
  assert (LA: PTree_samedom (@cenv_cs Zstd.units.Malloc.CS) (@la_env_cs Zstd.units.Malloc.CS)) by repeat constructor;
  exact (@QPcompspecs_OK_i Zstd.units.Malloc.CS HA LA).
Qed.

Lemma CSeq_Malloc : Zstd.units.Malloc.CS = compspecs_of_QPcomposite_env _ (proj2 OK_Malloc).
Proof. apply (compspecs_eq_of_QPcomposite_env Zstd.units.Malloc.CS Zstd.malloc.code.prog). reflexivity. Qed.

Lemma FOK_Libc : Asm6Lib.prog_funs_ok Zstd.units.Libc.CS Zstd.units.Libc.qp = true.
Proof. vm_compute. reflexivity. Qed.

Lemma Libc_Internal_eq : Libc_Internal =
  [(Zstd.libc.code._memset, snd memset_spec);
   (Zstd.libc.code._memcmp, snd memcmp_spec); (Zstd.libc.code._calloc, snd calloc_spec);
   (Zstd.libc.code._memcpy, snd memcpy_bytes_spec); (Zstd.libc.code._memmove, snd memmove_spec)].
Proof. reflexivity. Qed.

Section LibcSF.
Context (p: QP.program function) (OKp: QPprogram_OK p) (CSW: compspecs)
  (CSUB: cspecs_sub Zstd.units.Libc.CS CSW)
  (LINK: forall i f, (QP.prog_defs Zstd.units.Libc.qp) ! i = Some (Gfun (Internal f)) ->
                     (QP.prog_defs p) ! i = Some (Gfun (Internal f)))
  (V': varspecs) (G': funspecs)
  (HVL: forall j t, find_id j Zstd.proof.libc.LibcBodies.Vprog = Some t -> find_id j G' = None /\ find_id j V' = Some t)
  (Gmalloc: find_id _quickproof_malloc G' = Some (@malloc_spec' CSW))
  (GLibc: forall j psi, find_id j Libc_Internal = Some psi -> find_id j G' = Some psi)
  (LB: LibcBodies).

Lemma SF_libc: forall i phi fd, find_id i Libc_Internal = Some phi ->
  (QP.prog_defs p) ! i = Some (Gfun fd) ->
  @SF (@HonestEspec CSW) CSW V' (QPglobalenv p) G' i fd phi.
Proof.
  intros i phi fd Hi.
  rewrite Libc_Internal_eq in Hi. simpl in Hi.
  assert (HG: ctx_sub Gprog G').
  { unfold Gprog, Libc_Imports. apply ctx_sub_app.
    - apply ctx_sub_cons; [| apply ctx_sub_nil].
      exists (@malloc_spec' CSW); split; [exact Gmalloc |].
      exact (proj1 (env_specs_sub _ _ CSUB (cs_preserve_of_sub _ _ CSUB))).
    - intros j psi H. exists psi; split; [apply GLibc; auto | apply funspec_sub_refl]. }
  assert (LNR: list_norepet (map fst Gprog)) by (apply compute_list_norepet_e; reflexivity).
  assert (HV: forall j t, find_id j Gprog = None -> find_id j Vprog = Some t ->
                          find_id j G' = None /\ find_id j V' = Some t) by (intros; apply HVL; auto).
  repeat match type of Hi with (if ?c then _ else _) = _ => destruct c as [-> | ?]; [inv Hi | ] end;
    [ .. | discriminate].
  - apply (SF_unit Zstd.units.Libc.CS CSW Zstd.units.Libc.qp p OKp FOK_Libc CSUB LINK
             Vprog V' Gprog G' HG HV _ _ Zstd.libc.code.f_memset); [reflexivity | reflexivity | apply (bd_memset LB) | compute; auto 10].
  - apply (SF_unit Zstd.units.Libc.CS CSW Zstd.units.Libc.qp p OKp FOK_Libc CSUB LINK
             Vprog V' Gprog G' HG HV _ _ Zstd.libc.code.f_memcmp); [reflexivity | reflexivity | apply (bd_memcmp LB) | compute; auto 10].
  - apply (SF_unit Zstd.units.Libc.CS CSW Zstd.units.Libc.qp p OKp FOK_Libc CSUB LINK
             Vprog V' Gprog G' HG HV _ _ Zstd.libc.code.f_calloc); [reflexivity | reflexivity | apply (bd_calloc LB) | compute; auto 10].
  - apply (SF_unit Zstd.units.Libc.CS CSW Zstd.units.Libc.qp p OKp FOK_Libc CSUB LINK
             Vprog V' Gprog G' HG HV _ _ Zstd.libc.code.f_memcpy); [reflexivity | reflexivity | apply (bd_memcpy LB) | compute; auto 10].
  - apply (SF_unit Zstd.units.Libc.CS CSW Zstd.units.Libc.qp p OKp FOK_Libc CSUB LINK
             Vprog V' Gprog G' HG HV _ _ Zstd.libc.code.f_memmove); [reflexivity | reflexivity | apply (bd_memmove LB) | compute; auto 10].
Qed.
End LibcSF.

Definition placeholder_spec : ident * funspec :=
  (Zstd.malloc.code._malloc_placeholder, vacuous_funspec (Internal Zstd.malloc.code.f_malloc_placeholder)).

Lemma SF_placeholder (p: QP.program function) (OKp: QPprogram_OK p) (CSW: compspecs) (V': varspecs) (G': funspecs)
  (LINK: (QP.prog_defs p) ! Zstd.malloc.code._malloc_placeholder =
         Some (Gfun (Internal Zstd.malloc.code.f_malloc_placeholder)))
  (IN: In Zstd.malloc.code._malloc_placeholder (map fst G')) :
  forall fd, (QP.prog_defs p) ! Zstd.malloc.code._malloc_placeholder = Some (Gfun fd) ->
  @SF (@HonestEspec CSW) CSW V' (QPglobalenv p) G' (fst placeholder_spec) fd (snd placeholder_spec).
Proof.
  intros fd H. simpl fst in H. rewrite LINK in H. inv H.
  apply SF_of_fun_ok;
    [reflexivity | apply Zstd.proof.zstd.Base.semax_body_vacuous | reflexivity | apply (QPprogdefs_GFF OKp LINK) | exact IN].
Qed.
