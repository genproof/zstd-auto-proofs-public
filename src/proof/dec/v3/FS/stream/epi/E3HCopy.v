(* FS3 streaming: the epilogue's head, piece: ZSTD_outBuffer_copy(&expectedOutBuffer, output). *)
Require Import Zstd.proof.dec.v3.FS.stream.S3Main Zstd.proof.dec.v3.FS.stream.epi.E3Defs Zstd.proof.dec.v3.FS.stream.epi.E3Vst Zstd.proof.dec.v3.FS.stream.epi.E3T0 Zstd.proof.dec.v3.FS.stream.epi.E3H0.
Local Open Scope logic.

Section CM_E3HCopy_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma head_copy : forall (Espec: OracleKind) DENT TABS (a: dsa) (k: cst3) (ipc opc: Z) (oc1: list val),
  dsa_ok a -> a_opos a <= opc <= a_osz a ->
  semax (epi_Delta1 ZSTD_outBuffer_copy_spec) (hpre DENT TABS a k ipc ipc opc opc oc1 []) ds_h3
    (normal_ret_assert (hpre DENT TABS a (k_nfp a k opc (sf_nfp (c3_s k))) ipc ipc opc opc oc1 [])).
Proof.
intros Espec DENT TABS a k ipc opc oc1 Ha Hop.
pose proof Ha as (Hbufo & Hbufi & Hstbuf & Hwso & Hwsi & Hwsob & Hrsb & Hdict & Herr & Hopos & Hosz & Hloc0 &
                  Hipos & Hisz & Hlibs & Hbibs & Hstout0 & Hw0 & Hstpos & _).
epi_hstart. unfold ds_h3.
assert_PROP (field_compatible t_dctx (DOT _expectedOutBuffer) (a_d a)) as Hfce by entailer!.
assert_PROP (isptr (a_ob a)) as Pob by entailer!.
forward_call (Ews, field_address t_dctx (DOT _expectedOutBuffer) (a_d a), a_sho a, a_outp a, a_obf a, a_osz a, opc).
{ rewrite (field_at_data_at Ews t_dctx (DOT _expectedOutBuffer)). simpl nested_field_type. cancel. }
{ (* the struct's pointer: NULL, or the base itself (a pointer) *)
  unfold a_ob in Pob; destruct (nbase_cases (a_gv a) (a_obf a)) as [[_ E]|[E _]];
  [rewrite E in Pob; destruct (a_obf a); try contradiction; simpl; auto | rewrite E; simpl; auto]. }
change (data_at Ews t_outBuffer ?v (field_address t_dctx (DOT _expectedOutBuffer) ?p))
  with (data_at Ews (nested_field_type t_dctx (DOT _expectedOutBuffer)) v
          (field_address t_dctx (DOT _expectedOutBuffer) p)).
rewrite <- field_at_data_at.
epi_hend.
Time Qed.

End CM_E3HCopy_1.
