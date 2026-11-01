(* FS3 streaming: the epilogue's head, piece: output->pos = op - dst.  Since F9 dst is the temp the prologue
   set (not a new read of output->dst); the temps src and dst are dropped after this piece. *)
Require Import Zstd.proof.dec.v3.FS.stream.S3Main Zstd.proof.dec.v3.FS.stream.epi.E3Defs Zstd.proof.dec.v3.FS.stream.epi.E3Vst Zstd.proof.dec.v3.FS.stream.epi.E3T0 Zstd.proof.dec.v3.FS.stream.epi.E3H0.
Local Open Scope logic.

Section CM_E3HOut_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* epi_sub_pp0 for any buffer offset up to PTRDIFF_MAX: op - ostart of a caller's buffer of any size *)
Lemma epi_sub_pp0_any_out : forall p i, isptr p -> 0 <= i <= 2 ^ 63 - 1 ->
  force_val (sem_sub_pp tschar (offset_val i p) p) = Vlong (Int64.repr i).
Proof.
intros p i Hp Hi. destruct p; try contradiction.
unfold sem_sub_pp; simpl. rewrite if_true by auto. simpl. f_equal.
rewrite Ptrofs.sub_add_l, Ptrofs.sub_idem, Ptrofs.add_zero_l. rewrite Ptrofs.divs_one by reflexivity.
unfold Vptrofs. unfold Ptrofs.to_int64. rewrite Ptrofs.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma head_out : forall (Espec: OracleKind) DENT TABS (a: dsa) (k: cst3) (ipc opc: Z) (oc1: list val),
  dsa_ok a -> a_opos a <= opc <= a_osz a ->
  semax epi_Delta0 (hpre DENT TABS a k ipc ipc (a_opos a) opc oc1 [temp _src (a_ib a); temp _dst (a_ob a)]) ds_h2
    (normal_ret_assert (hpre DENT TABS a k ipc ipc opc opc oc1 [])).
Proof.
intros Espec DENT TABS a k ipc opc oc1 Ha Hop.
pose proof Ha as (Hbufo & Hbufi & Hstbuf & Hwso & Hwsi & Hwsob & Hrsb & Hdict & Herr & Hopos & Hosz & Hloc0 &
                  Hipos & Hisz & Hlibs & Hbibs & Hstout0 & Hw0 & Hstpos & _).
epi_fstart. unfold ds_h2.
assert_PROP (isptr (a_ob a)) as Pob by entailer!.
forward.
forward.
{ entailer!. apply prop_right. destruct (a_ob a); try contradiction. simpl. destruct (peq b b); [reflexivity | congruence]. }
rewrite epi_sub_pp0_any_out by (auto; lia).
try entailer!.
Qed.

End CM_E3HOut_1.
