(* The assembly of ONE law, generic in its harness unit.
   A whole program W = Harness + (Malloc + (Libc + Zstd)) is harness_safe when the decoder satisfies
   ZstdOK Int, the libc unit LibcBodies, and the harness HarnessOK_g API Hs (the shape of every
   src/proof/harness/<h>/HOK_<h>.v, for any API implied by Int (api_sub) without memcpy).  memcpy and memmove
   are the libc unit's (QuickProof v0.1.0-beta.1): the decoder's and the harnesses' typed memcpy_spec and the
   decoder's memmove_spec are weakenings of its specifications (LibcBodies.sub_memcpy, sub_memmove).  The conditions on the
   code of the harness and of W (links, side conditions of VST, names) are computed per harness
   (Asm6H_<h>.v).  Never unfolds a specification of the decoder or of the harness. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.veric.Clight_initial_world.
Require Import QuickProof.Contract.
Require Import Zstd.proof.asm6.Asm6Lib Zstd.proof.asm6.Asm6CS Zstd.proof.asm6.Asm6EnvSF Zstd.proof.asm6.Asm6Zstd.
Require Import Zstd.proof.asm6.Asm6Transfer Zstd.proof.asm6.Asm6Whole Zstd.proof.asm6.Asm6LinkLib.
Require Import Zstd.proof.asm6.Asm6ZstdSFV2 Zstd.proof.asm6.Asm6LibcSFV2.
Require Import Zstd.proof.top.ZstdOK6.
Require Import Zstd.proof.top.HarnessDefs.
Require Import Zstd.proof.libc.LibcBodies.
Require Zstd.units Zstd.malloc.code Zstd.proof.zstd.Base.
Import compcert.lib.Maps.

(* ---------- the harness obligation, generic in the harness unit ---------- *)
Section HOK.
Context (pH: QP.program function) (csH: compspecs) (W: QP.program function) (mainid: ident).

Definition main_spec_g : ident * funspec := (mainid, QPmain_spec_ext' W tt (fun _ _ => TT)).
Definition Imports_g (API: funspecs) : funspecs :=
  (_quickproof_malloc, @malloc_spec' csH) :: (_quickproof_free, @free_spec' csH) :: API.
Definition Externals_g : funspecs := present (ExtIDs pH) (@env_harness csH).
Definition helper_ids_g : list ident := filter (fun i => negb (Pos.eqb i mainid)) (IntIDs pH).
Definition Gprog_g (API Hs: funspecs) : funspecs := Imports_g API ++ Externals_g ++ Hs ++ [main_spec_g].
Definition hbody_ok_g (G: funspecs) (ix: ident * funspec) : Prop :=
  exists f, (QP.prog_defs pH) ! (fst ix) = Some (Gfun (Internal f)) /\
            fn_callconv f = callingconvention_of_funspec (snd ix) /\
            @semax_body (QPvarspecs W) G csH f ix.
Definition HarnessOK_g (API Hs: funspecs) : Prop :=
  map fst Hs = helper_ids_g /\ Forall (hbody_ok_g (Gprog_g API Hs)) (Hs ++ [main_spec_g]).
End HOK.

(* ---------- names ---------- *)
Definition env_ids : list ident :=
  [_quickproof_malloc; _quickproof_free; _nondet_u8; _nondet_u32; _nondet_size; _nondet_bytes;
   _gp_assert; _gp_assume].
Lemma env_specs_ids cs : map fst (@env_specs cs) = env_ids.
Proof. reflexivity. Qed.

(* the environment's functions among those a harness may call (env_harness); its last one, memcpy, is the libc
   unit's *)
Definition env_harness_ids : list ident :=
  [_nondet_u8; _nondet_u32; _nondet_size; _nondet_bytes; _gp_assert; _gp_assume].
Lemma env_harness_ids_eq cs : map fst (@env_harness cs) = env_harness_ids ++ [_memcpy].
Proof. reflexivity. Qed.

Lemma present_In ids (fs: funspecs) i phi : In (i, phi) (present ids fs) <-> In (i, phi) fs /\ In i ids.
Proof.
  unfold present. rewrite filter_In. simpl. split; intros [A B]; split; auto.
  - apply id_in_list_true; auto.
  - apply assoclists.id_in_list_true_i; auto.
Qed.

Lemma present_ids ids (fs: funspecs) : map fst (present ids fs) = filter (fun i => id_in_list i ids) (map fst fs).
Proof.
  unfold present. induction fs as [|[j p] fs IH]; simpl; auto.
  destruct (id_in_list j ids); simpl; congruence.
Qed.

(* the environment's functions that W declares *)
Definition Eids (W: QP.program function) : list ident := filter (fun i => id_in_list i (ExtIDs W)) env_ids.

Lemma Eids_In W i : In i (Eids W) <-> In i env_ids /\ In i (ExtIDs W).
Proof.
  unfold Eids. rewrite filter_In. split; intros [A B]; split; auto.
  - apply id_in_list_true; auto.
  - apply assoclists.id_in_list_true_i; auto.
Qed.

(* the definitions of the environment's functions, as the units declare them *)
Definition env_def (i: ident) : option (globdef (fundef function) type) :=
  if Pos.eqb i _quickproof_malloc then Some (Gfun (External
     (EF_external "quickproof_malloc" (mksignature (AST.Xlong :: nil) AST.Xptr cc_default))
     (tulong :: nil) (tptr tvoid) cc_default)) else
  if Pos.eqb i _quickproof_free then Some (Gfun (External
     (EF_external "quickproof_free" (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr tvoid) :: nil) tvoid cc_default)) else
  if Pos.eqb i _nondet_u8 then Some (Gfun (External
     (EF_external "nondet_u8" (mksignature nil AST.Xint8unsigned cc_default)) nil tuchar cc_default)) else
  if Pos.eqb i _nondet_u32 then Some (Gfun (External
     (EF_external "nondet_u32" (mksignature nil AST.Xint cc_default)) nil tuint cc_default)) else
  if Pos.eqb i _nondet_size then Some (Gfun (External
     (EF_external "nondet_size" (mksignature nil AST.Xlong cc_default)) nil tulong cc_default)) else
  if Pos.eqb i _nondet_bytes then Some (Gfun (External
     (EF_external "nondet_bytes" (mksignature (AST.Xptr :: AST.Xlong :: nil) AST.Xvoid cc_default))
     ((tptr tuchar) :: tulong :: nil) tvoid cc_default)) else
  if Pos.eqb i _gp_assert then Some (Gfun (External
     (EF_external "gp_assert" (mksignature (AST.Xint :: nil) AST.Xvoid cc_default)) (tint :: nil) tvoid cc_default)) else
  if Pos.eqb i _gp_assume then Some (Gfun (External
     (EF_external "gp_assume" (mksignature (AST.Xint :: nil) AST.Xvoid cc_default)) (tint :: nil) tvoid cc_default)) else
  None.

Definition ids_L : list ident :=
  [ Zstd.proof.libc.LibcSpec._memset; Zstd.proof.libc.LibcSpec._memcmp; Zstd.proof.libc.LibcSpec._calloc;
    Zstd.proof.libc.LibcSpec._memcpy; Zstd.proof.libc.LibcSpec._memmove ].
Lemma ids_L_eq : map fst Libc_Internal = ids_L.
Proof. reflexivity. Qed.
Lemma NR_L : list_norepet (map fst Libc_Internal).
Proof. rewrite ids_L_eq. apply compute_list_norepet_e. reflexivity. Qed.

Lemma memcpy_notin : ~ In _memcpy (IntIDs Zstd.units.Zstd.qp).
Proof. intros H. apply assoclists.id_in_list_true_i in H. vm_compute in H. discriminate. Qed.

Lemma NoDup_IntIDs : NoDup (IntIDs Zstd.units.Zstd.qp).
Proof. apply NoDup_norepet. apply compute_list_norepet_e. vm_compute. reflexivity. Qed.

Lemma PH_Malloc : (QP.prog_defs Zstd.units.Malloc.qp) ! Zstd.malloc.code._malloc_placeholder =
               Some (Gfun (Internal Zstd.malloc.code.f_malloc_placeholder)).
Proof. vm_compute. reflexivity. Qed.

Definition ids_W (pH W: QP.program function) (mainid: ident) : list ident :=
  mainid :: Eids W ++ ids_L ++ IntIDs Zstd.units.Zstd.qp ++ helper_ids_g pH mainid ++
  [Zstd.malloc.code._malloc_placeholder].

(* ---------- the law ---------- *)
Section Law.
Context (pH: QP.program function) (csH: compspecs) (mainid: ident) (W l1 l2: QP.program function)
  (L1: QPlink_progs Zstd.units.Libc.qp Zstd.units.Zstd.qp = Errors.OK l1)
  (L2: QPlink_progs Zstd.units.Malloc.qp l1 = Errors.OK l2)
  (L3: QPlink_progs pH l2 = Errors.OK W)
  (OKH: QPprogram_OK pH)
  (CSeqH: csH = compspecs_of_QPcomposite_env _ (proj2 OKH))
  (FOKH: prog_funs_ok csH pH = true)
  (CBC: forall H, cenv_built_correctly
        (map compdef_of_compenv_element (sort_rank (PTree.elements (QP.prog_comp_env W)) []))
        (composite_env_of_QPcomposite_env (QP.prog_comp_env W) H) = Errors.OK tt)
  (UNSPEC: all_unspecified_OK W)
  (ALIGNED: QPall_initializers_aligned W = true)
  (NOTBUILTIN: forallb not_builtin (PTree.elements (QP.prog_defs W)) = true)
  (MAINDEF: isSome (PTree.get (QP.prog_main W) (QP.prog_defs W)))
  (MAIN_eq: QP.prog_main W = mainid)
  (NR_W: list_norepet (map fst (QPvarspecs W) ++ ids_W pH W mainid))
  (DOM_W: forall i, In i (IntIDs W ++ Eids W) <-> In i (ids_W pH W mainid))
  (EXTDEF: forall i, In i (Eids W) -> (QP.prog_defs W) ! i = env_def i)
  (EMF: In _quickproof_malloc (Eids W) /\ In _quickproof_free (Eids W))
  (EXTH: forall i, In i env_harness_ids -> In i (ExtIDs pH) -> In i (Eids W))
  (VZ: vars_in Zstd.proof.zstd.Base.Vprog (QPvarspecs W) = true)
  (VL: vars_in Zstd.proof.libc.LibcBodies.Vprog (QPvarspecs W) = true)
  (NR_H: list_norepet (helper_ids_g pH mainid ++ [mainid])).

Definition OKW : QPprogram_OK W := OKw _ _ _ _ _ _ _ L1 L2 L3 OK_Zstd OK_Libc OK_Malloc OKH.

Definition CSW : compspecs := compspecs_of_QPcomposite_env _ (proj2 OKW).

Lemma CS_all: cspecs_sub Zstd.units.Zstd.CS CSW /\ cspecs_sub Zstd.units.Libc.CS CSW /\
              cspecs_sub Zstd.units.Malloc.CS CSW /\ cspecs_sub csH CSW.
Proof.
  destruct (chain_ce _ _ _ _ _ _ _ L1 L2 L3 OK_Zstd OK_Libc OK_Malloc OKH) as [A [B [C D]]].
  split; [|split; [|split]].
  - exact (chain_cs _ _ OK_Zstd OKW _ CSeq_Zstd A).
  - exact (chain_cs _ _ OK_Libc OKW _ CSeq_Libc B).
  - exact (chain_cs _ _ OK_Malloc OKW _ CSeq_Malloc C).
  - exact (chain_cs _ _ OKH OKW _ CSeqH D).
Qed.

Definition LINK_all := chain_link _ _ _ _ _ _ _ L1 L2 L3.

Lemma PH_def : (QP.prog_defs W) ! Zstd.malloc.code._malloc_placeholder =
               Some (Gfun (Internal Zstd.malloc.code.f_malloc_placeholder)).
Proof. destruct LINK_all as [_ [_ [LM _]]]. apply LM. exact PH_Malloc. Qed.

(* The environment's functions in this program, at the whole program's compspecs. *)
Definition E : funspecs := present (ExtIDs W) (@env_specs CSW).
Lemma E_ids : map fst E = Eids W.
Proof. unfold E, Eids. rewrite present_ids, env_specs_ids. reflexivity. Qed.

Definition mainspec : funspec := QPmain_spec_ext' W tt (fun _ _ => TT).
Definition G (Int Hs: funspecs) : funspecs := E ++ Libc_Internal ++ Zrest Int ++ Hs ++ [placeholder_spec].
Definition GG (Int Hs: funspecs) : funspecs := (QP.prog_main W, mainspec) :: G Int Hs.

Section Safe.
Context (Int API: funspecs) (ZOK: ZstdOK Int) (ASUB: api_sub API Int) (NMC: ~ In _memcpy (map fst API))
  (LB: LibcBodies) (Hs: funspecs) (HOK: HarnessOK_g pH csH W mainid API Hs).

Lemma perm_GG : Permutation (map fst (GG Int Hs)) (ids_W pH W mainid).
Proof.
  destruct ZOK as [ND [DOMZ _]]. destruct HOK as [HHs _].
  unfold GG, ids_W. rewrite MAIN_eq. cbn [map fst]. apply perm_skip. unfold G.
  rewrite !map_app, E_ids, ids_L_eq, HHs. apply Permutation_app_head. apply Permutation_app_head.
  apply Permutation_app_tail. apply perm_ids.
  - apply Zrest_NoDup; auto.
  - exact NoDup_IntIDs.
  - apply Zrest_ids; [exact DOMZ | exact memcpy_notin].
Qed.

Lemma LNR_GG : list_norepet (map fst (QPvarspecs W) ++ map fst (GG Int Hs)).
Proof.
  apply NoDup_norepet. eapply Permutation_NoDup; [| apply NoDup_norepet, NR_W].
  apply Permutation_app_head. symmetry. apply perm_GG.
Qed.

Lemma LNR_GG' : list_norepet (map fst (GG Int Hs)).
Proof. pose proof LNR_GG as H. apply list_norepet_append_right in H. exact H. Qed.

Lemma In_GG j psi : In (j, psi) (GG Int Hs) -> find_id j (GG Int Hs) = Some psi.
Proof. apply find_id_of_In, LNR_GG'. Qed.

Lemma In_G j psi : In (j, psi) (G Int Hs) -> find_id j (GG Int Hs) = Some psi.
Proof. intros H. apply In_GG. right. exact H. Qed.

Lemma main_notin_G : find_id (QP.prog_main W) (G Int Hs) = None.
Proof.
  pose proof LNR_GG' as H. unfold GG in H. cbn [map fst] in H. inv H.
  apply assoclists.find_id_None_iff. auto.
Qed.

Lemma NR_E : list_norepet (map fst E).
Proof.
  pose proof LNR_GG' as H. unfold GG in H. cbn [map fst] in H. inv H.
  unfold G in H3. rewrite map_app in H3. apply list_norepet_append_left in H3. exact H3.
Qed.

Lemma GG_E i : In i (map fst E) -> find_id i E = find_id i (GG Int Hs).
Proof.
  intros Hi. unfold GG. cbn [find_id fst].
  destruct (Memory.EqDec_ident i (QP.prog_main W)) as [->|NE].
  - pose proof main_notin_G as H. apply assoclists.find_id_None_iff in H.
    exfalso. apply H. unfold G. rewrite map_app. apply in_or_app. left. exact Hi.
  - unfold G. rewrite find_id_app_in; auto. rewrite if_false; auto.
Qed.

Lemma In_E x : In x (@env_specs CSW) -> In (fst x) (Eids W) -> find_id (fst x) (GG Int Hs) = Some (snd x).
Proof.
  intros H1 H2. apply In_G. unfold G. apply in_or_app. left. unfold E.
  destruct x as [i phi]. apply present_In. split; auto. apply Eids_In in H2. tauto.
Qed.

Lemma HV_GG Vu: vars_in Vu (QPvarspecs W) = true ->
  forall j t, find_id j Vu = Some t -> find_id j (GG Int Hs) = None /\ find_id j (QPvarspecs W) = Some t.
Proof.
  intros VI j t H. apply (vars_in_e _ _ _ _ VI) in H. split; auto.
  exact (assoclists.list_norepet_find_id_app_exclusive1 LNR_GG H).
Qed.

Lemma id_in_GG i phi : In (i, phi) (GG Int Hs) -> id_in_list i (map fst (GG Int Hs)) = true.
Proof. intros H. apply assoclists.id_in_list_true_i. change i with (fst (i, phi)). apply in_map; auto. Qed.

Ltac env_in := cbv beta delta [env_specs]; repeat (first [left; reflexivity | right]).
Ltac in_L := unfold G; apply in_or_app; right; apply in_or_app; left; unfold Libc_Internal;
             repeat (first [left; reflexivity | right]).
Ltac in_Z := unfold G; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left.
Ltac in_H := unfold G; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right;
             apply in_or_app; left.

Lemma GInt : forall j psi, j <> _memcpy -> find_id j Int = Some psi -> find_id j (GG Int Hs) = Some psi.
Proof. intros j psi Hj H. apply find_id_e in H. apply In_G. in_Z. apply Zrest_In; auto. Qed.

Lemma GHs : forall j psi, find_id j (Hs ++ [main_spec_g W mainid]) = Some psi -> find_id j (GG Int Hs) = Some psi.
Proof.
  intros j psi H. apply find_id_e in H. apply in_app_or in H as [H | [H | []]].
  - apply In_G. in_H. exact H.
  - apply In_GG. left. rewrite MAIN_eq. exact H.
Qed.

Lemma GMalloc : find_id _quickproof_malloc (GG Int Hs) = Some (@malloc_spec' CSW).
Proof. apply (In_E (_quickproof_malloc, @malloc_spec' CSW)); [env_in | apply EMF]. Qed.
Lemma GFree : find_id _quickproof_free (GG Int Hs) = Some (@free_spec' CSW).
Proof. apply (In_E (_quickproof_free, @free_spec' CSW)); [env_in | apply EMF]. Qed.
Lemma GMemcpy : find_id _memcpy (GG Int Hs) = Some (snd (@Zstd.proof.libc.LibcSpec.memcpy_bytes_spec Zstd.units.Libc.CS)).
Proof. apply In_G. in_L. Qed.
Lemma GMemmove : find_id _memmove (GG Int Hs) = Some (snd (@Zstd.proof.libc.LibcSpec.memmove_spec Zstd.units.Libc.CS)).
Proof. apply In_G. in_L. Qed.

(* the harness's context Gprog_g is weakened by GG *)
Lemma ctx_harness : ctx_sub (Gprog_g pH csH W mainid API Hs) (GG Int Hs).
Proof.
  pose proof CS_all as [_ [_ [_ CSH]]].
  destruct (env_specs_sub _ _ CSH (cs_preserve_of_sub _ _ CSH)) as [Smalloc [Sfree Sbytes]].
  unfold Gprog_g, Imports_g. rewrite <- !app_comm_cons.
  apply ctx_sub_cons. { exists (@malloc_spec' CSW); split; [exact GMalloc | exact Smalloc]. }
  apply ctx_sub_cons. { exists (@free_spec' CSW); split; [exact GFree | exact Sfree]. }
  apply ctx_sub_app; [| apply ctx_sub_app].
  - intros j psi H. apply find_id_e in H.
    unfold api_sub in ASUB. rewrite Forall_forall in ASUB. destruct (ASUB _ H) as [s [Hs' Hsub]]. simpl in Hs', Hsub.
    exists s; split; [| exact Hsub]. apply GInt; [| exact Hs'].
    intros ->. apply NMC. change _memcpy with (fst (_memcpy, psi)). apply in_map; auto.
  - intros j psi H. apply find_id_e in H. unfold Externals_g in H. apply present_In in H as [H1 H2].
    (* the environment's functions among them are declared by W too *)
    assert (HE0: j <> _memcpy -> In j (Eids W)).
    { intros Hj. apply EXTH; auto.
      assert (Hin: In j (map fst (@env_harness csH))) by (change j with (fst (j, psi)); apply in_map; auto).
      rewrite env_harness_ids_eq in Hin. apply in_app_or in Hin as [Hin | [Hin | []]]; [exact Hin | congruence]. }
    cbv beta delta [env_harness] in H1.
    destruct H1 as [H|[H|[H|[H|[H|[H|[H|[]]]]]]]];
      match type of H with ?X = _ =>
        assert (Ej: j = fst X) by (rewrite H; reflexivity);
        assert (Ep: psi = snd X) by (rewrite H; reflexivity); subst j psi end;
      try (assert (HE := HE0 ltac:(intro E; vm_compute in E; discriminate))).
    + exists (snd nondet_u8_spec); split; [apply (In_E nondet_u8_spec); [env_in | exact HE] | apply funspec_sub_refl].
    + exists (snd nondet_u32_spec); split; [apply (In_E nondet_u32_spec); [env_in | exact HE] | apply funspec_sub_refl].
    + exists (snd nondet_size_spec); split; [apply (In_E nondet_size_spec); [env_in | exact HE] | apply funspec_sub_refl].
    + exists (snd (@nondet_bytes_spec CSW)); split; [apply (In_E (@nondet_bytes_spec CSW)); [env_in | exact HE] |].
      exact (funspec_sub_trans _ _ _ (@nondet_bytes_nn_sub CSW) Sbytes).
    + exists (snd gp_assert_spec); split; [apply (In_E gp_assert_spec); [env_in | exact HE] | apply funspec_sub_refl].
    + exists (snd gp_assume_spec); split; [apply (In_E gp_assume_spec); [env_in | exact HE] | apply funspec_sub_refl].
    + (* memcpy: the libc unit's *)
      eexists; split; [exact GMemcpy | exact (Zstd.proof.libc.LibcBodies.sub_memcpy LB csH)].
  - intros j psi H. exists psi; split; [apply GHs; auto | apply funspec_sub_refl].
Qed.

Lemma SF_harness: forall i phi fd, find_id i (Hs ++ [main_spec_g W mainid]) = Some phi ->
  (QP.prog_defs W) ! i = Some (Gfun fd) ->
  @SF (@HonestEspec CSW) CSW (QPvarspecs W) (QPglobalenv W) (GG Int Hs) i fd phi.
Proof.
  intros i phi fd Hfind Hp.
  pose proof CS_all as [_ [_ [_ CSH]]].
  pose proof LINK_all as [_ [_ [_ LH]]].
  pose proof HOK as [Hids HF].
  pose proof (find_id_e _ _ _ Hfind) as Hin.
  rewrite Forall_forall in HF. destruct (HF _ Hin) as [f [Hf [CC SB]]]. simpl fst in Hf. simpl snd in CC.
  apply (SF_unit csH CSW pH W OKW FOKH CSH LH (QPvarspecs W) (QPvarspecs W)
           (Gprog_g pH csH W mainid API Hs) (GG Int Hs)) with (f := f); auto.
  - exact ctx_harness.
  - intros j t _ HV. split; auto.
    exact (assoclists.list_norepet_find_id_app_exclusive1 LNR_GG HV).
  - unfold Gprog_g. rewrite !map_app. apply in_or_app; right. apply in_or_app; right.
    rewrite <- map_app. apply (in_map fst) in Hin. exact Hin.
Qed.

Lemma SF_env : forall i phi fd, In (i, phi) E -> (QP.prog_defs W) ! i = Some (Gfun fd) ->
  @SF (@HonestEspec CSW) CSW (QPvarspecs W) (QPglobalenv W) (GG Int Hs) i fd phi.
Proof.
  intros i phi fd HE Hdef.
  assert (IDIN: id_in_list i (map fst (GG Int Hs)) = true).
  { apply (id_in_GG i phi). right. unfold G. apply in_or_app; left; exact HE. }
  unfold E in HE. apply present_In in HE as [HE HX].
  assert (Hi: In i (Eids W)).
  { apply Eids_In. split; auto. rewrite <- (env_specs_ids CSW). change i with (fst (i, phi)). apply in_map; auto. }
  pose proof (EXTDEF i Hi) as D.
  cbv beta delta [env_specs] in HE.
  destruct HE as [H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]; inv H.
  - apply (SF_ok_malloc (cs:=CSW) (V:=QPvarspecs W) CSW W OKW (GG Int Hs));
      first [exact IDIN | exact Hdef | (rewrite D; vm_compute; reflexivity)].
  - apply (SF_ok_free (cs:=CSW) (V:=QPvarspecs W) CSW W OKW (GG Int Hs));
      first [exact IDIN | exact Hdef | (rewrite D; vm_compute; reflexivity)].
  - apply (SF_ok_nondet_u8 (cs:=CSW) (V:=QPvarspecs W) CSW W OKW (GG Int Hs));
      first [exact IDIN | exact Hdef | (rewrite D; vm_compute; reflexivity)].
  - apply (SF_ok_nondet_u32 (cs:=CSW) (V:=QPvarspecs W) CSW W OKW (GG Int Hs));
      first [exact IDIN | exact Hdef | (rewrite D; vm_compute; reflexivity)].
  - apply (SF_ok_nondet_size (cs:=CSW) (V:=QPvarspecs W) CSW W OKW (GG Int Hs));
      first [exact IDIN | exact Hdef | (rewrite D; vm_compute; reflexivity)].
  - apply (SF_ok_nondet_bytes (cs:=CSW) (V:=QPvarspecs W) CSW W OKW (GG Int Hs));
      first [exact IDIN | exact Hdef | (rewrite D; vm_compute; reflexivity)].
  - apply (SF_ok_gp_assert (cs:=CSW) (V:=QPvarspecs W) CSW W OKW (GG Int Hs));
      first [exact IDIN | exact Hdef | (rewrite D; vm_compute; reflexivity)].
  - apply (SF_ok_gp_assume (cs:=CSW) (V:=QPvarspecs W) CSW W OKW (GG Int Hs));
      first [exact IDIN | exact Hdef | (rewrite D; vm_compute; reflexivity)].
Qed.

Lemma JUST_all : forall i phi fd, (QP.prog_defs W) ! i = Some (Gfun fd) ->
  find_id i (GG Int Hs) = Some phi ->
  @SF (@HonestEspec CSW) CSW (QPvarspecs W) (QPglobalenv W) (GG Int Hs) i fd phi.
Proof.
  pose proof CS_all as [CSZ [CSL [CSM CSH]]].
  pose proof LINK_all as [LZ [LL [LM LH]]].
  pose proof ZOK as [ND [DOMZ [MC _]]].
  pose proof HOK as [HHs _].
  assert (NRHM: list_norepet (map fst (Hs ++ [main_spec_g W mainid]))).
  { rewrite map_app, HHs. exact NR_H. }
  intros i phi fd Hdef Hf.
  pose proof (find_id_e _ _ _ Hf) as HIn. pose proof (id_in_GG _ _ HIn) as IDIN.
  destruct HIn as [Hm | HIn].
  - (* main *)
    injection Hm as <- <-. apply SF_harness; auto. apply find_id_i; auto. apply in_or_app; right; left.
    unfold main_spec_g. rewrite MAIN_eq. reflexivity.
  - apply in_app_or in HIn as [HE | HIn].
    + (* the environment *)
      apply SF_env; auto.
    + apply in_app_or in HIn as [HL | HIn].
      * (* the libc unit *)
        refine (SF_libc W OKW CSW CSL LL (QPvarspecs W) (GG Int Hs) (HV_GG _ VL)
                  GMalloc _ LB i phi fd _ Hdef).
        -- intros j psi H. apply find_id_e in H. apply In_G. unfold G. apply in_or_app; right; apply in_or_app; left; exact H.
        -- apply find_id_i; auto. exact NR_L.
      * apply in_app_or in HIn as [HZ | HIn].
        -- (* the decoder *)
           apply Zrest_In in HZ as [HZ Hne].
           refine (SF_zstd W OKW CSW CSZ LZ (QPvarspecs W) (GG Int Hs) (HV_GG _ VZ)
                     GMalloc GFree GMemcpy GMemmove _ _ LB Int ZOK GInt i phi fd Hne _ Hdef).
           ++ apply In_G; in_L.
           ++ apply In_G; in_L.
           ++ apply find_id_i; auto. apply NoDup_norepet; auto.
        -- apply in_app_or in HIn as [HH | [HP | []]].
           ++ (* the harness's helpers *)
              apply SF_harness; auto. apply find_id_i; auto. apply in_or_app; left; auto.
           ++ (* the malloc unit's placeholder *)
              unfold placeholder_spec in HP; injection HP as <- <-. apply (SF_placeholder W OKW CSW (QPvarspecs W) (GG Int Hs) PH_def); auto.
              apply id_in_list_true; auto.
Qed.

Theorem law_safe : harness_safe W.
Proof.
  apply (harness_safe_of_parts W OKW E (G Int Hs) (fun _ _ => TT)).
  - exact main_notin_G.
  - exact MAINDEF.
  - exact UNSPEC.
  - exact ALIGNED.
  - exact NOTBUILTIN.
  - exact CBC.
  - exact LNR_GG.
  - exact NR_E.
  - intros i Hi. rewrite E_ids in Hi. rewrite (EXTDEF i Hi).
    apply Eids_In in Hi as [Hi _].
    repeat (destruct Hi as [<-|Hi]; [do 4 eexists; vm_compute; reflexivity|]). destruct Hi.
  - intros i. rewrite E_ids, DOM_W. split; apply Permutation_in; [symmetry|]; apply perm_GG.
  - exact GG_E.
  - exact JUST_all.
Qed.
End Safe.
End Law.
