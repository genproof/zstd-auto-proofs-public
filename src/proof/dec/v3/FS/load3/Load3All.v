(* FS3 load3: the obligations of the part that combine several load3 files *)
Require Import Zstd.proof.dec.v3.FS.FSOblig3.
Require Import Zstd.proof.dec.v3.FS.FSLift3.
Require Import Zstd.proof.dec.v3.FS.load3.Load3Lift Zstd.proof.dec.v3.FS.load3.Load3Adv Zstd.proof.dec.v3.FS.load3.Load3RefSub Zstd.proof.dec.v3.FS.load3.Load3InitDD.
Local Open Scope logic.

Section CM_Load3All_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma body_loadDictionary_advanced3 : FS3_body (fun DENT TABS SR BR => ZSTD_DCtx_loadDictionary_advanced_spec3 DENT TABS).
Proof.
  intros DENT TABS SR BR HD HT.
  apply (load3_lift (G_loadadv DENT)); [unfold G_loadadv; load3_in | apply body_loadDictionary_advanced3_small].
Qed.

(* ZSTD_initDStream_usingDDict calls ZSTD_DCtx_refDDict, specified internally in FS3_G *)
Definition G_initddict_int (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR: blrel) : funspecs :=
  [ZSTD_DCtx_reset_spec (DC3x DENT TABS SR BR); ZSTD_DCtx_refDDict_int_spec3 DENT TABS;
   ERR_isError_spec; ZSTD_startingInputLength_spec3].

Lemma body_initDStream_usingDDict3 :
  FS3_body (fun DENT TABS SR BR => ZSTD_initDStream_usingDDict_aspec (DC3x DENT TABS SR BR) (DD3x DENT)).
Proof.
  intros DENT TABS SR BR HD HT.
  apply (load3_lift (G_initddict_int DENT TABS SR BR)); [unfold G_initddict_int; load3_in |].
  apply (fs3_body_ok_sub (G_initddict DENT TABS SR BR)); [apply body_initDStream_usingDDict3_small | |].
  - apply (fs3_refines_but (G_initddict_int DENT TABS SR BR) (G_initddict DENT TABS SR BR) _ZSTD_DCtx_refDDict
             (snd (ZSTD_DCtx_refDDict_int_spec3 DENT TABS))).
    + apply list_norepet_NoDup. apply compute_list_norepet_e. vm_compute. reflexivity.
    + simpl. auto.
    + intros i phi Hin. simpl in Hin.
      destruct Hin as [E | [E | [E | [E | []]]]]; inversion E; subst; clear E.
      * left. simpl. auto.
      * right. split; [reflexivity | exact (@refDDict_rsub CMI DENT TABS SR BR HD HT)].
      * left. simpl. auto.
      * left. simpl. auto.
  - apply list_norepet_NoDup. apply compute_list_norepet_e. vm_compute. reflexivity.
Qed.

Lemma refDDict_sub3 :
  FS3_sub (fun DENT TABS SR BR => ZSTD_DCtx_refDDict_int_spec3 DENT TABS)
          (fun DENT TABS SR BR => ZSTD_DCtx_refDDict_spec (DC3x DENT TABS SR BR) (DD3x DENT)).
Proof. intros DENT TABS SR BR HD HT. apply refDDict_rsub; auto. Qed.

End CM_Load3All_1.
