(* Subtree H of the decoder, API v3.  Prove H3_obligation (DecSubtrees3.v). *)
Require Export Zstd.proof.dec.v3.DecSubtrees3.
Require Import Zstd.proof.dec.H.HSpecs.
Require Import Zstd.proof.dec.H.body_H_alloc Zstd.proof.dec.H.body_H_magic Zstd.proof.dec.H.body_H_skip Zstd.proof.dec.H.body_H_fhsize Zstd.proof.dec.v3.H.body_H33_fhapi Zstd.proof.dec.v3.H.body_H33_fsi2 Zstd.proof.dec.H.body_H_loops.
Require Import Zstd.proof.dec.v3.H.HAlloc3Sub.
Require Import Zstd.proof.dec.v3.H.HLift34 Zstd.proof.dec.v3.H.H34Api Zstd.proof.dec.v3.H.body_H34_fhsize Zstd.proof.dec.v3.H.body_H34_fh Zstd.proof.dec.v3.H.body_H34_fsi.

(* API v3.3 (exact getFrameHeader error codes): v2's body_H_fh is not needed (getFrameHeader_advanced is v3's),
   body_H_fhapi / body_H_fsi / body_H3_fh / body_H3_fsi are replaced by their v3.3 copies v3/H/body_H33_*.v.
   S = HSpecs3.H3_specs: v2's bodies lift by HLift3.lift_H_body (the v3 specs refine the v2 ones), the bodies
   with the format are proved against H3_G (body_H3_*.v).
   API v3.4 (fh_post FH_err struct disjunct) / the revised usingDict specification (DecLift's B part no longer
   checks): the files importing
   HLift3 are replaced by copies v3/H/{HLift34, H34Api, body_H34_fhsize, body_H34_fh, body_H34_fsi}.v (HLift34
   without DecLift; body_H34_fh with the v3.4 error post) *)
(* the bodies of H against H3_G, where the allocation helpers have DecIface's default-allocator specifications *)
Lemma H3_bodies : Forall (body_ok H3_G) H3_specs.
Proof.
  pose proof bodies_H_alloc. pose proof bodies_H_magic. pose proof bodies_H_skip.
  pose proof bodies_H_fhsize. pose proof bodies_H_fhapi.
  pose proof bodies_H_fsi. pose proof bodies_H_loops.
  pose proof bodies_H3_fhsize. pose proof body_H3_fh. pose proof body_H3_fsi.
  repeat match goal with H: _ /\ _ |- _ => destruct H end.
  unfold H3_specs, H3_core. cbn [app].
    repeat apply Forall_cons; try apply Forall_nil.
    + apply lift_H_body with f_ZSTD_customMallocP; [reflexivity | reflexivity | assumption].
    + apply lift_H_body with f_ZSTD_customCallocP; [reflexivity | reflexivity | assumption].
    + apply lift_H_body with f_ZSTD_customFreeP; [reflexivity | reflexivity | assumption].
    + apply lift_H_body with f_ZSTD_customMem_copy; [reflexivity | reflexivity | assumption].
    + apply body_H3 with f_ZSTD_startingInputLength; [reflexivity | reflexivity | assumption].
    + apply lift_H_body with f_ZSTD_isFrame; [reflexivity | reflexivity | assumption].
    + apply lift_H_body with f_ZSTD_isSkippableFrame; [reflexivity | reflexivity | assumption].
    + apply body_H3 with f_ZSTD_frameHeaderSize_internal; [reflexivity | reflexivity | assumption].
    + apply lift_H_body with f_ZSTD_frameHeaderSize; [reflexivity | reflexivity | assumption].
    + apply body_H3 with f_ZSTD_getFrameHeader_advanced; [reflexivity | reflexivity | assumption].
    + apply lift_H_body with f_ZSTD_getFrameHeader; [reflexivity | reflexivity | assumption].
    + apply lift_H_body with f_ZSTD_getFrameContentSize; [reflexivity | reflexivity | assumption].
    + apply lift_H_body with f_readSkippableFrameSize; [reflexivity | reflexivity | assumption].
    + apply lift_H_body with f_ZSTD_readSkippableFrame; [reflexivity | reflexivity | assumption].
    + apply lift_H_body with f_ZSTD_findDecompressedSize; [reflexivity | reflexivity | assumption].
    + apply lift_H_body with f_ZSTD_errorFrameSizeInfo; [reflexivity | reflexivity | assumption].
    + apply body_H3 with f_ZSTD_findFrameSizeInfo; [reflexivity | reflexivity | assumption].
    + apply body_H3 with f_ZSTD_findFrameCompressedSize_advanced; [reflexivity | reflexivity | assumption].
    + apply lift_H_body with f_ZSTD_findFrameCompressedSize; [reflexivity | reflexivity | assumption].
    + apply lift_H_body with f_ZSTD_decompressBound; [reflexivity | reflexivity | assumption].
    + apply lift_H_body with f_ZSTD_getDictID_fromDict; [reflexivity | reflexivity | assumption].
    + apply lift_H_body with f_ZSTD_getDictID_fromFrame; [reflexivity | reflexivity | assumption].
    + apply lift_H_body with f_ZSTD_DStreamOutSize; [reflexivity | reflexivity | assumption].
    + apply lift_H_body with f_ZSTD_getcBlockSize; [reflexivity | reflexivity | assumption].
    + apply body_H3 with f_ZSTD_getDecompressedSize; [reflexivity | reflexivity | assumption].
Qed.

(* H for an allocator class: the helpers ZSTD_customMallocP, ZSTD_customCallocP, ZSTD_customFreeP and ZSTD_customMem_copy with HAlloc3's
   specifications (proved against Gprog alone); the other bodies keep their proofs, since these specifications imply
   the default-allocator ones (HAlloc3Sub) *)
Section HCM.
Context {CMI: cmem_preds}.

Definition H3_specs_cm : funspecs :=
  ZSTD_customMallocP_cm_spec :: ZSTD_customCallocP_cm_spec :: ZSTD_customFreeP_cm_spec ::
  ZSTD_customMem_copy_cm_spec :: skipn 4 H3_specs.

Lemma H3_specs_cm_names : map fst H3_specs_cm = ids_H3.
Proof. reflexivity. Qed.

Lemma H3_cm_refines : refines (Gprog ++ H3_specs_cm) H3_G.
Proof.
  unfold H3_G. apply refines_prefix_h, refines_pointwise_h. unfold H3_specs_cm, H3_specs, H3_core. cbn [skipn app].
  repeat apply Forall2_cons; try apply Forall2_nil; (split; [reflexivity |]);
    first [ apply funspec_sub_refl | apply customMallocP_cm_sub_dflt | apply customCallocP_cm_sub_dflt
          | apply customFreeP_cm_sub_dflt
          | apply customMem_copy_cm_sub_dflt ].
Qed.

Lemma H3_cm_nodup : NoDup (map fst Vprog ++ map fst (Gprog ++ H3_specs_cm)).
Proof.
  rewrite map_app, H3_specs_cm_names.
  apply list_norepet_NoDup. apply compute_list_norepet_e. vm_compute. reflexivity.
Qed.

Lemma H3_cm_bodies : Forall (body_ok (Gprog ++ H3_specs_cm)) H3_specs_cm.
Proof.
  destruct halloc3_done as (a0 & a1 & a2 & a3).
  assert (Hg: forall x, body_ok Gprog x -> body_ok (Gprog ++ H3_specs_cm) x).
  { intros x Hx. eapply body_ok_mono; [exact Hx | apply incl_appl, incl_refl | exact H3_cm_nodup]. }
  assert (Hl: forall x, In x H3_specs -> body_ok (Gprog ++ H3_specs_cm) x).
  { intros x Hx. pose proof H3_bodies as Hb. rewrite Forall_forall in Hb.
    exact (body_ok_sub_h _ _ _ (Hb x Hx) H3_cm_refines H3_cm_nodup). }
  apply Forall_forall. intros x Hx. unfold H3_specs_cm in Hx.
  destruct Hx as [<- | [<- | [<- | [<- | Hx]]]].
  - apply Hg. exists f_ZSTD_customMallocP. split; [reflexivity | split; [reflexivity | exact a0]].
  - apply Hg. exists f_ZSTD_customCallocP. split; [reflexivity | split; [reflexivity | exact a1]].
  - apply Hg. exists f_ZSTD_customFreeP. split; [reflexivity | split; [reflexivity | exact a2]].
  - apply Hg. exists f_ZSTD_customMem_copy. split; [reflexivity | split; [reflexivity | exact a3]].
  - apply Hl. rewrite <- (firstn_skipn 4 H3_specs). apply in_or_app. right. exact Hx.
Qed.

End HCM.

Lemma H3_ok : H3_obligation.
Proof.
  intros CMI. exists H3_specs_cm. split; [exact H3_specs_cm_names | split; [| split]].
  - intros x Hx; unfold H_exports3, H_api3, H_api in Hx; simpl in Hx; unfold H3_specs_cm, H3_specs, H3_core.
    cbn [skipn app].
    repeat (destruct Hx as [<- | Hx]; [simpl; tauto | ]); contradiction.
  - pose proof H3_api_sub as Ha. unfold api_sub in *.
    inversion Ha as [|? ? [s [Hs Hsub]] _]; subst.
    constructor; [| constructor]. exists s. split; [exact Hs | exact Hsub].
  - exact H3_cm_bodies.
Qed.
