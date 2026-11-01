(* FS3: the DDict hash set: the specifications of getIndex, emplaceDDict and expand (the set
   part's choice), the bodies of the seven set functions, what the probe means (hs_probe_ok). *)
Require Import Zstd.proof.dec.v3.FS.FSOblig3.
Require Import Zstd.proof.dec.v3.FS.set.SetDefs Zstd.proof.dec.v3.FS.set.SetProbe Zstd.proof.dec.v3.FS.set.SetEmplacePure Zstd.proof.dec.v3.FS.set.SetExpandPure Zstd.proof.dec.v3.FS.set.SetMem Zstd.proof.dec.v3.FS.set.SetBodyA Zstd.proof.dec.v3.FS.set.SetBodyExpand Zstd.proof.dec.v3.FS.set.SetBodyAdd Zstd.proof.dec.v3.FS.set.SetBodyGet Zstd.proof.dec.v3.FS.set.SetBodyEmplace.
Local Open Scope logic.

Section CM_body3_set_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Definition set3_specs : funspecs := [ getIndex_spec3; emplace_spec3; expand_spec3 ].

Section Lift.
Variables (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR: blrel).

Let G := FS3_G DENT TABS SR BR ++ set3_specs.

Lemma set3_nodup : NoDup (map fst Vprog ++ map fst G).
Proof.
  subst G. apply list_norepet_NoDup. apply compute_list_norepet_e. vm_compute. reflexivity.
Qed.

Lemma set3_lift (Gs: funspecs) (i: ident) (f: function) (phi: funspec) :
  zstd_fun i f -> fn_callconv f = callingconvention_of_funspec phi ->
  semax_body Vprog Gs f (i, phi) -> incl Gs G -> body_ok G (i, phi).
Proof.
  intros Hf Hcc Hb Hinc. apply (body_ok_mono Gs); [ | exact Hinc | exact set3_nodup ].
  exists f; split; [exact Hf | split; [exact Hcc | exact Hb]].
Qed.

End Lift.

Ltac in_find := repeat first [ left; reflexivity | right ].

Ltac lift_tac Gs i f phi :=
  let B := fresh "B" in intros B;
  apply (set3_lift _ _ _ _ Gs i f (snd phi)); [reflexivity | reflexivity | exact B | ];
  let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; simpl in Hx;
  repeat (destruct Hx as [<- | Hx]; [ in_find | ]); contradiction.

Lemma lift_getIndex DENT TABS SR BR :
  semax_body Vprog G_getIndex f_ZSTD_DDictHashSet_getIndex getIndex_spec3 -> body_ok (FS3_G DENT TABS SR BR ++ set3_specs) getIndex_spec3.
Proof. lift_tac G_getIndex _ZSTD_DDictHashSet_getIndex f_ZSTD_DDictHashSet_getIndex getIndex_spec3. Qed.

Lemma lift_emplace DENT TABS SR BR :
  semax_body Vprog G_emplace f_ZSTD_DDictHashSet_emplaceDDict emplace_spec3 -> body_ok (FS3_G DENT TABS SR BR ++ set3_specs) emplace_spec3.
Proof. lift_tac G_emplace _ZSTD_DDictHashSet_emplaceDDict f_ZSTD_DDictHashSet_emplaceDDict emplace_spec3. Qed.

Lemma lift_expand DENT TABS SR BR :
  semax_body Vprog G_expand f_ZSTD_DDictHashSet_expand expand_spec3 -> body_ok (FS3_G DENT TABS SR BR ++ set3_specs) expand_spec3.
Proof. lift_tac G_expand _ZSTD_DDictHashSet_expand f_ZSTD_DDictHashSet_expand expand_spec3. Qed.

Lemma lift_getDDict DENT TABS SR BR :
  semax_body Vprog G_getDDict f_ZSTD_DDictHashSet_getDDict ZSTD_DDictHashSet_getDDict_spec -> body_ok (FS3_G DENT TABS SR BR ++ set3_specs) ZSTD_DDictHashSet_getDDict_spec.
Proof. lift_tac G_getDDict _ZSTD_DDictHashSet_getDDict f_ZSTD_DDictHashSet_getDDict ZSTD_DDictHashSet_getDDict_spec. Qed.

Lemma lift_create DENT TABS SR BR :
  semax_body Vprog G_create f_ZSTD_createDDictHashSet ZSTD_createDDictHashSet_spec -> body_ok (FS3_G DENT TABS SR BR ++ set3_specs) ZSTD_createDDictHashSet_spec.
Proof. lift_tac G_create _ZSTD_createDDictHashSet f_ZSTD_createDDictHashSet ZSTD_createDDictHashSet_spec. Qed.

Lemma lift_free DENT TABS SR BR :
  semax_body Vprog G_free f_ZSTD_freeDDictHashSet ZSTD_freeDDictHashSet_spec -> body_ok (FS3_G DENT TABS SR BR ++ set3_specs) ZSTD_freeDDictHashSet_spec.
Proof. lift_tac G_free _ZSTD_freeDDictHashSet f_ZSTD_freeDDictHashSet ZSTD_freeDDictHashSet_spec. Qed.

Lemma lift_add DENT TABS SR BR :
  semax_body Vprog G_add f_ZSTD_DDictHashSet_addDDict ZSTD_DDictHashSet_addDDict_spec -> body_ok (FS3_G DENT TABS SR BR ++ set3_specs) ZSTD_DDictHashSet_addDDict_spec.
Proof. lift_tac G_add _ZSTD_DDictHashSet_addDDict f_ZSTD_DDictHashSet_addDDict ZSTD_DDictHashSet_addDDict_spec. Qed.

Lemma set3_ddid_wvp : MF_ddid_wvp.
Proof.
  intros q id db. unfold ddid. Intros.
  sep_apply (field_at_valid_ptr0 Ews t_ddict (DOT _dictBuffer) db q); auto.
  apply sepcon_weak_valid_pointer1. apply valid_pointer_weak.
Qed.

Lemma set3_ddid_range : MF_ddid_range.
Proof. intros q id db. unfold ddid. entailer!. Qed.

Lemma SET3_ok : SET3_obligation.
Proof.
  destruct set_probe_ok as (Hprobe & Hmem & Hsid & Hnf & Hinv0).
  destruct set_emplace_pure as (Hins & Hrep).
  destruct set_expand_pure as (Hinit & Hei & Hes & Hesk & Hee & Han & Hae).
  destruct set_mem_ok as (Mc & Mt & Mu & Mf & Ma).
  pose proof set3_ddid_wvp as Mw. pose proof set3_ddid_range as Mr.
  destruct (set_bodyA Mu Mc Mt Hinit) as (Bi & Bc & Bf).
  pose proof (set_body_expand Mw Mf Hmem Hsid Mc Mt Hinv0 Hei Hes Hesk Hee) as Bx.
  pose proof (set_body_add Ma Hinv0 Han Hae) as Ba.
  pose proof (set_body_get Mw Mr Mf Hmem Hsid Hnf) as Bg.
  pose proof (set_body_emplace Mw Mr Mf Hmem Hsid Hnf Hins Hrep) as Be.
  split; [exact Hprobe |].
  intros DENT TABS HD HT. exists set3_specs. split; [reflexivity |]. intros SR BR.
  repeat apply Forall_cons; try apply Forall_nil.
  - apply lift_getIndex; exact Bi.
  - apply lift_emplace; exact Be.
  - apply lift_expand; exact Bx.
  - apply lift_getDDict; exact Bg.
  - apply lift_create; exact Bc.
  - apply lift_free; exact Bf.
  - apply lift_add; exact Ba.
Qed.

End CM_body3_set_1.
