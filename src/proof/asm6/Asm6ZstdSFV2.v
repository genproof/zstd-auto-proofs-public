(* The decoder unit's functions in a whole program: their SF obligations at the whole program's
   compspecs CSW and in any whole function context G' that holds the specifications the decoder's
   context (Zstd_Imports ++ Int) needs: the decoder's own Int entries verbatim, malloc/free of the
   environment at CSW, memset/calloc/memcpy/memmove of the libc unit (at its compspecs Libc.CS; memcpy as its
   byte specification).
   Generic: never unfolds a decoder specification (ZstdOK only). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Env.
Require Import Zstd.proof.asm6.Asm6Lib Zstd.proof.asm6.Asm6CS Zstd.proof.asm6.Asm6Zstd Zstd.proof.asm6.Asm6Transfer.
Require Import Zstd.proof.top.ZstdOK6.
Require Zstd.proof.libc.LibcBodies.
Require Zstd.units.
Require Import VST.veric.Clight_initial_world.
Import compcert.lib.Maps.

Lemma Zstd_Imports_ids: map fst Zstd.proof.zstd.Gprog.Zstd_Imports =
  [_quickproof_malloc; _quickproof_free; _memmove;
   Zstd.proof.libc.LibcSpec._memset; Zstd.proof.libc.LibcSpec._calloc].
Proof. reflexivity. Qed.

Lemma Zstd_Imports_not_ids_b:
  forallb (fun x => negb (id_in_list x zstd_ids))
    [_quickproof_malloc; _quickproof_free; _memmove;
     Zstd.proof.libc.LibcSpec._memset; Zstd.proof.libc.LibcSpec._calloc] = true.
Proof. vm_compute. reflexivity. Qed.

Lemma Zstd_Imports_not_ids: forall x, In x (map fst Zstd.proof.zstd.Gprog.Zstd_Imports) -> ~ In x zstd_ids.
Proof.
  intros x H. rewrite Zstd_Imports_ids in H.
  pose proof Zstd_Imports_not_ids_b as B. rewrite forallb_forall in B. specialize (B x H).
  intros H'. apply assoclists.id_in_list_true_i in H'. rewrite H' in B. discriminate.
Qed.

Lemma ctx_sub_cons_ix ix A G':
  (exists psi', find_id (fst ix) G' = Some psi' /\ funspec_sub psi' (snd ix)) -> ctx_sub A G' -> ctx_sub (ix :: A) G'.
Proof. destruct ix; apply ctx_sub_cons. Qed.

Section ZstdSF.
Context (p: QP.program function) (OKp: QPprogram_OK p) (CSW: compspecs)
  (CSUB: cspecs_sub Zstd.units.Zstd.CS CSW)
  (LINK: forall i f, (QP.prog_defs Zstd.units.Zstd.qp) ! i = Some (Gfun (Internal f)) ->
                     (QP.prog_defs p) ! i = Some (Gfun (Internal f)))
  (V': varspecs) (G': funspecs)
  (* the decoder's global variables are in V' with the same types, and are not functions of G' *)
  (HVZ: forall j t, find_id j Zstd.proof.zstd.Base.Vprog = Some t -> find_id j G' = None /\ find_id j V' = Some t)
  (Gmalloc: find_id _quickproof_malloc G' = Some (@malloc_spec' CSW))
  (Gfree: find_id _quickproof_free G' = Some (@free_spec' CSW))
  (Gmemcpy: find_id _memcpy G' = Some (snd (@Zstd.proof.libc.LibcSpec.memcpy_bytes_spec Zstd.units.Libc.CS)))
  (Gmemmove: find_id _memmove G' = Some (snd (@Zstd.proof.libc.LibcSpec.memmove_spec Zstd.units.Libc.CS)))
  (Gmemset: find_id Zstd.proof.libc.LibcSpec._memset G' =
             Some (snd (@Zstd.proof.libc.LibcSpec.memset_spec Zstd.units.Libc.CS)))
  (Gcalloc: find_id Zstd.proof.libc.LibcSpec._calloc G' =
             Some (snd (@Zstd.proof.libc.LibcSpec.calloc_spec Zstd.units.Libc.CS)))
  (LB: Zstd.proof.libc.LibcBodies.LibcBodies)
  (Int: funspecs) (ZOK: ZstdOK Int)
  (GInt: forall j psi, j <> _memcpy -> find_id j Int = Some psi -> find_id j G' = Some psi).

Lemma SF_zstd: forall i phi fd, i <> _memcpy -> find_id i Int = Some phi ->
  (QP.prog_defs p) ! i = Some (Gfun fd) ->
  @SF (@HonestEspec CSW) CSW V' (QPglobalenv p) G' i fd phi.
Proof.
  intros i phi fd Hne Hfind Hp.
  destruct ZOK as [ND [IDS [MC BODIES]]].
  pose proof (Asm6CS.env_specs_sub Zstd.units.Zstd.CS CSW CSUB (Asm6CS.cs_preserve_of_sub _ _ CSUB))
    as [Smalloc [Sfree _]].
  rewrite Forall_forall in BODIES.
  destruct (BODIES (i, phi) (find_id_e _ _ _ Hfind) Hne) as [f [Hf [CC SB]]].
  simpl fst in Hf. simpl snd in CC.
  eapply (SF_unit Zstd.units.Zstd.CS CSW Zstd.units.Zstd.qp p OKp funs_ok_Zstd CSUB LINK
            Zstd.proof.zstd.Base.Vprog V' (Zstd.proof.zstd.Gprog.Zstd_Imports ++ Int) G');
    [ | | exact Hf | exact CC | exact SB | | exact Hp ].
  - apply ctx_sub_app.
    + unfold Zstd.proof.zstd.Gprog.Zstd_Imports.
      apply ctx_sub_cons; [exists (@malloc_spec' CSW); split; [exact Gmalloc | exact Smalloc] |].
      apply ctx_sub_cons; [exists (@free_spec' CSW); split; [exact Gfree | exact Sfree] |].
      apply ctx_sub_cons_ix; [ | apply ctx_sub_cons_ix; [ | apply ctx_sub_cons_ix; [ | apply ctx_sub_nil]]].
      * eexists; split; [exact Gmemmove | exact (Zstd.proof.libc.LibcBodies.sub_memmove LB Zstd.units.Zstd.CS)].
      * eexists; split; [exact Gmemset | exact (Zstd.proof.libc.LibcBodies.sub_memset LB)].
      * eexists; split; [exact Gcalloc | exact (Zstd.proof.libc.LibcBodies.sub_calloc LB)].
    + intros j psi H. destruct (Memory.EqDec_ident j _memcpy) as [E|E].
      * subst j. rewrite MC in H. inv H. eexists. split; [exact Gmemcpy | exact (Zstd.proof.libc.LibcBodies.sub_memcpy LB Zstd.units.Zstd.CS)].
      * exists psi. split; [apply GInt; auto | apply funspec_sub_refl].
  - intros j t _ Hj. apply HVZ; exact Hj.
  - rewrite map_app. apply in_or_app. right. apply (find_id_In_map_fst _ _ _ Hfind).
Qed.

End ZstdSF.
