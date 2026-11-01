(* API v3: the decoder's assembly.  As v2's DecAsm.v (which no longer
   compiles: its final lemma is about the v2 API): the three subtree obligations of DecSubtrees3.v, the proved
   L0 layer and vacuous specifications for the functions no law reaches (ids_DEAD3) give the decoder's
   obligation (Zstd6.zstd_ok): Int = memcpy_spec :: Specs_L0 ++ S_H ++ S_B ++ S_FS ++ dead specs. *)
Require Export Zstd.proof.dec.v3.DecLift.
Require Import Zstd.proof.zstd.AllBodies_util_bits Zstd.proof.zstd.AllBodies_xxh.
Import compcert.lib.Maps.

(* ---------- identifiers (computations on ident lists only) ---------- *)

Definition ids_L0 : list ident :=
  [ _ZSTD_wrappedPtrAdd;
    _ZSTD_wrappedPtrSub;
    _ZSTD_maybeNullPtrAdd;
    _MEM_32bits;
    _MEM_64bits;
    _MEM_isLittleEndian;
    _MEM_read16;
    _MEM_read32;
    _MEM_read64;
    _MEM_write16;
    _MEM_write32;
    _MEM_write64;
    _MEM_swap32_fallback;
    _MEM_swap32;
    _MEM_swap64_fallback;
    _MEM_swap64;
    _MEM_readLE16;
    _MEM_readLE24;
    _MEM_readLE32;
    _MEM_writeLE32;
    _MEM_readLE64;
    _MEM_readLEST;
    _ERR_isError;
    _ERR_getErrorCode;
    __force_has_format_string;
    _ZSTD_countTrailingZeros32_fallback;
    _ZSTD_countTrailingZeros32;
    _ZSTD_countLeadingZeros32_fallback;
    _ZSTD_countLeadingZeros32;
    _ZSTD_countTrailingZeros64;
    _ZSTD_highbit32;
    _FSE_isError;
    _ZSTD_copy8;
    _ZSTD_copy16;
    _ZSTD_isError;
    _ZSTD_getErrorCode;
    _ZSTD_DCtx_get_bmi2;
    _ZSTD_copy4;
    _BIT_initDStream;
    _BIT_getMiddleBits;
    _BIT_lookBits;
    _BIT_lookBitsFast;
    _BIT_skipBits;
    _BIT_readBits;
    _BIT_readBitsFast;
    _BIT_reloadDStream_internal;
    _BIT_reloadDStreamFast;
    _BIT_reloadDStream;
    _BIT_endOfDStream;
    _XXH_memcpy;
    _XXH_read32;
    _XXH_readLE32;
    _XXH_readLE32_align;
    _XXH_read64;
    _XXH_readLE64;
    _XXH_readLE64_align;
    _XXH64_round;
    _XXH64_mergeRound;
    _XXH64_avalanche;
    _XXH64_finalize;
    _XXH64_endian_align;
    _ZSTD_XXH64;
    _ZSTD_XXH64_reset;
    _ZSTD_XXH64_update;
    _ZSTD_XXH64_digest ].

Lemma Specs_L0_ids : map fst Specs_L0 = ids_L0.
Proof. reflexivity. Qed.

Definition ids_imports : list ident := [ _quickproof_malloc; _quickproof_free; _memmove; _memset; _calloc ].

Lemma Zstd_Imports_ids : map fst Zstd_Imports = ids_imports.
Proof. reflexivity. Qed.

Definition is_internal (i: ident) : bool :=
  match (QP.prog_defs Zstd.units.Zstd.qp) ! i with Some (Gfun (Internal _)) => true | _ => false end.

Fixpoint nodupb (l: list ident) : bool :=
  match l with [] => true | x :: r => andb (negb (existsb (Pos.eqb x) r)) (nodupb r) end.

Lemma nodupb_NoDup (l: list ident) : nodupb l = true -> NoDup l.
Proof.
  induction l as [|x r IH]; simpl; intros H; constructor.
  - apply andb_prop in H as [H _]. intros Hin. apply negb_true_iff in H.
    assert (existsb (Pos.eqb x) r = true) by (apply existsb_exists; exists x; split; [exact Hin | apply Pos.eqb_refl]).
    congruence.
  - apply andb_prop in H as [_ H]. auto.
Qed.

Definition inclb (l1 l2: list ident) : bool := forallb (fun i => existsb (Pos.eqb i) l2) l1.

Lemma inclb_incl (l1 l2: list ident) : inclb l1 l2 = true -> incl l1 l2.
Proof.
  unfold inclb; intros H i Hi. rewrite forallb_forall in H. apply H in Hi.
  apply existsb_exists in Hi as [j [Hj E]]. apply Pos.eqb_eq in E. subst; exact Hj.
Qed.

Definition ids_all : list ident := _memcpy :: ids_L0 ++ ids_H3 ++ ids_B3 ++ ids_FS3 ++ ids_DEAD3.

Lemma ids_all_check :
  andb (andb (andb (nodupb (map fst Vprog ++ ids_imports ++ ids_all))
  (inclb ids_all zstd_ids)) (inclb zstd_ids ids_all)) (forallb is_internal ids_DEAD3) = true.
Proof. vm_compute. reflexivity. Qed.

(* ---------- the dead functions: vacuous specifications ---------- *)

Definition dead_spec (i: ident) : ident * funspec :=
  match (QP.prog_defs Zstd.units.Zstd.qp) ! i with
  | Some (Gfun (Internal f)) => (i, vacuous_funspec (Internal f))
  | _ => (i, snd memcpy_spec)
  end.

Definition Specs_dead : funspecs := map dead_spec ids_DEAD3.

Lemma Specs_dead_ids : map fst Specs_dead = ids_DEAD3.
Proof.
  unfold Specs_dead. rewrite map_map. rewrite <- (map_id ids_DEAD3) at 2. apply map_ext.
  intros i. unfold dead_spec. destruct ((QP.prog_defs Zstd.units.Zstd.qp) ! i) as [[[f|]|]|]; reflexivity.
Qed.

Lemma Specs_dead_ok (G: funspecs) : Forall (body_ok G) Specs_dead.
Proof.
  pose proof ids_all_check as H. rewrite !andb_true_iff in H. destruct H as [[[_ _] _] H].
  rewrite forallb_forall in H. apply Forall_forall. intros x Hx.
  unfold Specs_dead in Hx. apply in_map_iff in Hx as [i [<- Hi]]. apply H in Hi.
  unfold is_internal, dead_spec in *.
  destruct ((QP.prog_defs Zstd.units.Zstd.qp) ! i) as [[[f|]|]|] eqn:E; try discriminate.
  apply body_ok_vacuous. exact E.
Qed.

(* ---------- L0: the proved bodies ---------- *)

Lemma body_ok_intro (G: funspecs) (f: function) (ix: ident * funspec) :
  semax_body Vprog G f ix -> zstd_fun (fst ix) f ->
  fn_callconv f = callingconvention_of_funspec (snd ix) -> body_ok G ix.
Proof. intros Hb Hf Hc. exists f; auto. Qed.

(* the conjuncts of bodies_util_bits / bodies_xxh are in the order of Specs_util ++ Specs_bits / Specs_xxh *)
Ltac forall_bodies H :=
  lazymatch type of H with
  | _ /\ _ =>
      let H1 := fresh "Hb" in let H2 := fresh "Hb" in destruct H as [H1 H2];
      apply Forall_cons; [apply (body_ok_intro _ _ _ H1); reflexivity | forall_bodies H2]
  | _ => apply Forall_cons; [apply (body_ok_intro _ _ _ H); reflexivity | ]
  end.

Lemma Specs_L0_ok : Forall (body_ok Gprog) Specs_L0.
Proof.
  pose proof bodies_util_bits as H1. pose proof bodies_xxh as H2.
  unfold Specs_L0, Specs_util, Specs_bits, Specs_xxh. cbn [app].
  forall_bodies H1. forall_bodies H2. apply Forall_nil.
Qed.

(* membership in an explicit list, by syntactic equality of the elements *)
Ltac in_list :=
  repeat match goal with
         | |- In ?a (?b :: _) => tryif constr_eq a b then (left; reflexivity) else right
         end.

(* an entry of an api_sub list whose specification sits in a part of Int *)
Lemma api_sub_part (A S Int: funspecs) (x: ident * funspec) :
  api_sub A S -> In x A -> incl S Int ->
  (forall y, In y Int -> initial_world.find_id (fst y) Int = Some (snd y)) ->
  exists s, initial_world.find_id (fst x) Int = Some s /\ funspec_sub s (snd x).
Proof.
  intros HA Hx HS Hfind. unfold api_sub in HA. rewrite Forall_forall in HA.
  destruct (HA x Hx) as [s [Hs Hsub]]. exists s; split; [| exact Hsub].
  apply initial_world.find_id_e in Hs. apply (Hfind _ (HS _ Hs)).
Qed.

(* a context whose every entry is implied by an entry of G' *)
Lemma refines_of (G' G: funspecs) :
  (forall x, In x G -> exists s, initial_world.find_id (fst x) G' = Some s /\ funspec_sub s (snd x)) ->
  refines G' G.
Proof.
  intros H i phi Hf. apply initial_world.find_id_e in Hf. exact (H (i, phi) Hf).
Qed.

(* for any allocator class CMI: H, B and FS are proved for CMI (B's ZSTD_initDDict_internal copies a DDict's bytes
   through the DDict's allocator) *)
(* also: Int holds Specs_L0 itself (Int = memcpy_spec :: Specs_L0 ++ ...), for the harnesses that call the layer L0
   (top/Zstd6L0) *)
Lemma dec_assemble3_full {CMI: cmem_preds} :
  H3_obligation -> B3_obligation -> FS3_obligation ->
  exists (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred) (Int: funspecs),
    ZstdOK Int /\ api_sub (Specs_api DC DD) Int /\ dc_cm_ok DC /\ api_sub Specs_L0 Int.
Proof.
  intros HH [DENT [TABS [HD [HT HB]]]] HFS.
  destruct (HB CMI) as [SB [HidB [HapiB HokB]]].
  destruct (HH CMI) as [SH [HidH [HexH [HapiH HokH]]]].
  destruct (HFS CMI DENT TABS HD HT) as [DC [DD [[SFS [HidFS [HapiFS HokFS]]] [HBapi Hcm]]]].
  exists DC, DD, (memcpy_spec :: Specs_L0 ++ SH ++ SB ++ SFS ++ Specs_dead).
  set (Int := memcpy_spec :: Specs_L0 ++ SH ++ SB ++ SFS ++ Specs_dead).
  assert (Hids: map fst Int = ids_all).
  { subst Int; unfold ids_all. cbn [map]. rewrite !map_app, Specs_L0_ids, HidH, HidB, HidFS, Specs_dead_ids.
    reflexivity. }
  pose proof ids_all_check as Hc. rewrite !andb_true_iff in Hc. destruct Hc as [[[Hnd Hi1] Hi2] _].
  assert (Hnd': NoDup (map fst Vprog ++ map fst (Zstd_Imports ++ Int))).
  { rewrite map_app, Zstd_Imports_ids, Hids. apply nodupb_NoDup; exact Hnd. }
  assert (HndInt: NoDup (map fst Int)).
  { rewrite map_app in Hnd'. do 2 apply NoDup_app_remove_l in Hnd'. exact Hnd'. }
  assert (Hin: forall l, incl l Int -> incl l (Zstd_Imports ++ Int)).
  { intros l H. apply incl_appr. exact H. }
  assert (HL0: incl Specs_L0 Int).
  { intros x Hx. right. apply in_or_app. left. exact Hx. }
  assert (HSH: incl SH Int).
  { intros x Hx. right. apply in_or_app. right. apply in_or_app. left. exact Hx. }
  assert (HSB: incl SB Int).
  { intros x Hx. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hx. }
  assert (HSFS: incl SFS Int).
  { intros x Hx. do 4 (right; apply in_or_app). left. exact Hx. }
  assert (HG: incl Gprog (Zstd_Imports ++ Int)).
  { unfold Gprog. apply incl_app; [apply incl_appl, incl_refl | apply Hin].
    intros x [<- | Hx]; [left; reflexivity | apply HL0; exact Hx]. }
  assert (HHex: incl H_exports3 (Zstd_Imports ++ Int)).
  { apply Hin. intros x Hx. apply HSH, HexH, in_or_app. left. exact Hx. }
  assert (HHapi: incl H_api3 (Zstd_Imports ++ Int)).
  { apply Hin. intros x Hx. apply HSH, HexH, in_or_app. right. exact Hx. }
  assert (Hfind: forall x, In x Int -> initial_world.find_id (fst x) Int = Some (snd x)).
  { intros [i f] Hx. apply initial_world.find_id_i; [exact Hx |]. apply list_norepet_NoDup. exact HndInt. }
  assert (Hlit: forall x, In x Int -> exists s, initial_world.find_id (fst x) Int = Some s /\ funspec_sub s (snd x)).
  { intros x Hx. exists (snd x). split; [apply Hfind; exact Hx | apply funspec_sub_refl]. }
  assert (HndAll: list_norepet (map fst (Zstd_Imports ++ Int))).
  { apply list_norepet_NoDup. rewrite map_app in Hnd'. apply NoDup_app_remove_l in Hnd'.
    rewrite <- map_app in Hnd'. exact Hnd'. }
  assert (HfindAll: forall x, In x (Zstd_Imports ++ Int) ->
            initial_world.find_id (fst x) (Zstd_Imports ++ Int) = Some (snd x)).
  { intros [i f] Hx. apply initial_world.find_id_i; [exact Hx | exact HndAll]. }
  (* B's specifications imply B's exports *)
  assert (HBx: forall x, In x (B_exports3 DENT TABS) ->
            exists s, initial_world.find_id (fst x) Int = Some s /\ funspec_sub s (snd x)).
  { intros x Hx. exact (api_sub_part _ _ _ _ HapiB Hx HSB Hfind). }
  assert (HBapi3: forall x, In x (B_api3 DC DD) ->
            exists s, initial_world.find_id (fst x) Int = Some s /\ funspec_sub s (snd x)).
  { intros x Hx. unfold api_sub in HBapi. rewrite Forall_forall in HBapi.
    destruct (HBapi x Hx) as [s0 [Hs0 Hsub0]]. apply initial_world.find_id_e in Hs0.
    destruct (HBx _ Hs0) as [s [Hs Hsub]]. exists s. split; [exact Hs |].
    eapply funspec_sub_trans; [exact Hsub | exact Hsub0]. }
  assert (HndFS: NoDup (map fst Vprog ++ map fst (Gprog ++ H_exports3 ++ H_api3 ++ B_exports3 DENT TABS ++ SFS))).
  { rewrite !map_app, HidFS. apply nodupb_NoDup. vm_compute. reflexivity. }
  assert (HndB: NoDup (map fst Vprog ++ map fst ((Gprog ++ H_exports3 (CMI:=CMI)) ++ SB))).
  { rewrite !map_app, HidB. apply nodupb_NoDup. vm_compute. reflexivity. }
  pose proof (Specs_dead_ok (Zstd_Imports ++ Int)) as Hd0.
  split; [split; [| split; [| split]] | split; [| split; [exact Hcm |]]].
  - exact HndInt.
  - intros i. rewrite Hids. split; [apply inclb_incl; exact Hi1 | apply inclb_incl; exact Hi2].
  - subst Int. unfold initial_world.find_id. rewrite (surjective_pairing memcpy_spec).
    change (fst memcpy_spec) with _memcpy. rewrite if_true by reflexivity. reflexivity.
  - subst Int. constructor; [intros Hm; exfalso; apply Hm; reflexivity |].
    apply Forall_app; split; [| apply Forall_app; split; [| apply Forall_app; split; [| apply Forall_app; split]]].
    + eapply Forall_impl; [| exact Specs_L0_ok]. intros a Ha _. eapply body_ok_mono; eauto.
    + eapply Forall_impl; [| exact HokH]. intros a Ha _. eapply body_ok_mono; [exact Ha | | exact Hnd'].
      apply incl_app; [exact HG | apply Hin; exact HSH].
    + eapply Forall_impl; [| exact HokB]. intros a Ha _. eapply body_ok_sub; [exact Ha | | exact HndB | exact Hnd'].
      apply refines_of. intros x Hx. rewrite !in_app_iff in Hx.
      destruct Hx as [[Hx | Hx] | Hx].
      * exists (snd x). split; [apply HfindAll, HG, Hx | apply funspec_sub_refl].
      * exists (snd x). split; [apply HfindAll, HHex, Hx | apply funspec_sub_refl].
      * exists (snd x). split; [apply HfindAll, in_or_app; right; apply HSB, Hx | apply funspec_sub_refl].
    + eapply Forall_impl; [| exact HokFS]. intros a Ha _. eapply body_ok_sub; [exact Ha | | exact HndFS | exact Hnd'].
      apply refines_of. intros x Hx. rewrite !in_app_iff in Hx.
      destruct Hx as [[Hx | [Hx | [Hx | Hx]]] | Hx].
      * exists (snd x). split; [apply HfindAll, HG, Hx | apply funspec_sub_refl].
      * exists (snd x). split; [apply HfindAll, HHex, Hx | apply funspec_sub_refl].
      * exists (snd x). split; [apply HfindAll, HHapi, Hx | apply funspec_sub_refl].
      * destruct (HBx x Hx) as [s [Hs Hsub]]. exists s. split; [| exact Hsub].
        apply initial_world.find_id_e in Hs. apply (HfindAll (fst x, s)). apply in_or_app; right; exact Hs.
      * exists (snd x). split; [apply HfindAll, in_or_app; right; apply HSFS, Hx | apply funspec_sub_refl].
    + eapply Forall_impl; [| exact Hd0]. intros a Ha _. exact Ha.
  - unfold api_sub. apply Forall_forall. intros x Hx. unfold Specs_api in Hx.
    repeat (destruct Hx as [<- | Hx]; [| ]); try contradiction.
    all: first
      [ solve [ apply Hlit, HL0; unfold Specs_L0, Specs_util; apply in_or_app; left; in_list ]
      | solve [ apply Hlit, HSH, HexH, in_or_app; right; unfold H_api3; apply in_or_app; left; unfold H_api; in_list ]
      | solve [ apply Hlit, HSH, HexH, in_or_app; right; unfold H_api3; apply in_or_app; right; in_list ]
      | solve [ apply (api_sub_part _ _ _ _ HapiH); [in_list | exact HSH | exact Hfind] ]
      | solve [ apply (api_sub_part _ _ _ _ HapiFS); [unfold FS_api3; in_list | exact HSFS | exact Hfind] ]
      | solve [ apply HBapi3; unfold B_api3; in_list ] ].
  - unfold api_sub. apply Forall_forall. intros x Hx. apply Hlit, HL0, Hx.
Qed.

Lemma dec_assemble3 {CMI: cmem_preds} :
  H3_obligation -> B3_obligation -> FS3_obligation ->
  exists (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred) (Int: funspecs),
    ZstdOK Int /\ api_sub (Specs_api DC DD) Int /\ dc_cm_ok DC.
Proof.
  intros HH HB HFS. destruct (dec_assemble3_full HH HB HFS) as (DC & DD & Int & H1 & H2 & H3 & _).
  exists DC, DD, Int. auto.
Qed.
