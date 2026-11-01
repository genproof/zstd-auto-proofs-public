(* FS3 set part: the bodies of ZSTD_DDictHashSet_getIndex, ZSTD_createDDictHashSet, ZSTD_freeDDictHashSet. *)
Require Import Zstd.proof.dec.v3.FS.set.SetDefs.
Require Import Zstd.proof.dec.v3.FS.set.SetBodyA_get Zstd.proof.dec.v3.FS.set.SetBodyA_create Zstd.proof.dec.v3.FS.set.SetBodyA_free.
Local Open Scope logic.

Section CM_SetBodyA_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma set_bodyA : MF_uint_bytes -> MF_calloc_tbl -> MF_tbl_bytes -> PF_init ->
  semax_body Vprog G_getIndex f_ZSTD_DDictHashSet_getIndex getIndex_spec3 /\
  semax_body Vprog G_create f_ZSTD_createDDictHashSet ZSTD_createDDictHashSet_spec /\
  semax_body Vprog G_free f_ZSTD_freeDDictHashSet ZSTD_freeDDictHashSet_spec.
Proof.
  intros Hub Hcal Htb Hinit.
  split; [| split].
  - exact (body_getIndex3 Hub).
  - exact (body_create3 Hcal Hinit).
  - exact (body_free3 Htb).
Qed.

End CM_SetBodyA_1.
