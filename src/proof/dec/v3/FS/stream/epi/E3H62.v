(* FS3 streaming: the epilogue's head, piece: t'62 = (ip == istart) && (op == ostart), when ip == istart. 
   2026-10-24: the temps renamed after F9. *)
Require Import Zstd.proof.dec.v3.FS.stream.S3Main Zstd.proof.dec.v3.FS.stream.epi.E3Defs Zstd.proof.dec.v3.FS.stream.epi.E3Vst Zstd.proof.dec.v3.FS.stream.epi.E3T0 Zstd.proof.dec.v3.FS.stream.epi.E3H0.
Local Open Scope logic.

Section CM_E3H62_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* epi_off_inj for offsets up to PTRDIFF_MAX: two positions of a caller's buffer of any size are equal pointers
   only if they are equal offsets *)
Lemma epi_off_inj_any : forall p i j, isptr p -> 0 <= i <= 2 ^ 63 - 1 -> 0 <= j <= 2 ^ 63 - 1 ->
  offset_val i p = offset_val j p -> i = j.
Proof.
intros p i j Hp Hi Hj E. destruct p as [| | | | |b o]; try contradiction.
unfold offset_val in E. injection E as E.
pose proof (Ptrofs.unsigned_range o).
rewrite (Ptrofs.unsigned_repr i), (Ptrofs.unsigned_repr j), !Ptrofs.Z_mod_modulus_eq in E by rep_lia.
set (u := Ptrofs.unsigned o) in *. set (M := Ptrofs.modulus) in *.
assert (HM: M = 2 ^ 64) by reflexivity. rewrite HM in *.
pose proof (Z.div_mod (u + i) (2 ^ 64) ltac:(lia)). pose proof (Z.mod_pos_bound (u + i) (2 ^ 64) ltac:(lia)).
pose proof (Z.div_mod (u + j) (2 ^ 64) ltac:(lia)). pose proof (Z.mod_pos_bound (u + j) (2 ^ 64) ltac:(lia)).
lia.
Qed.

(* this piece never touches the context's fields: keep it folded *)
Ltac epi_hstart0 :=
  unfold hpre, hS, epi_L; cbn [app]; unfold ds_Delta, epi_Delta0, epi_Delta1, ds_R_x, ds_post_x; abbreviate_semax.
Ltac epi_hend0 := unfold hpre, hS, epi_L; cbn [app]; entailer!.

Lemma head_62_eq : forall (Espec: OracleKind) DENT TABS (a: dsa) (k: cst3) (ipc opc: Z) (oc1: list val),
  dsa_ok a -> a_ipos a <= ipc <= a_isz a -> a_opos a <= opc <= a_osz a -> Zlength oc1 = a_osz a -> ipc = a_ipos a ->
  semax epi_Delta0 (hpre DENT TABS a k ipc ipc opc opc oc1 []) ds_h62
    (normal_ret_assert (hpre DENT TABS a k ipc ipc opc opc oc1
       [temp _t'64 (Val.of_bool (andb (ipc =? a_ipos a) (opc =? a_opos a)))])).
Proof.
intros Espec DENT TABS a k ipc opc oc1 Ha Hip Hop Hloc Hc.
pose proof Ha as (Hbufo & Hbufi & Hstbuf & Hwso & Hwsi & Hwsob & Hrsb & Hdict & Herr & Hopos & Hosz & Hloc0 &
                  Hipos & Hisz & Hlibs & Hbibs & Hstout0 & Hw0 & Hstpos & _).
epi_hstart0. unfold ds_h62.
assert_PROP (isptr (a_ib a)) as Pib by entailer!.
assert_PROP (isptr (a_ob a)) as Pob by entailer!.
forward_if (temp _t'64 (Val.of_bool (andb (ipc =? a_ipos a) (opc =? a_opos a)))).
{ entailer!. apply epi_tc_test_eq; auto; epi_wvp (a_W a) (a_shb a) (zbytes (a_ibs a)) (a_ib a). }
{ forward. forward.
  { entailer!. apply epi_tc_test_eq; auto; epi_wvp (a_W a) (a_shob a) oc1 (a_ob a). }
  entailer!.
  try rewrite Hc; rewrite Z.eqb_refl. simpl andb.
  destruct (eq_dec _ _) as [E|E].
  + apply epi_off_inj_any in E; [|auto; lia..]. rewrite E, Z.eqb_refl. reflexivity.
  + destruct (Z.eqb_spec opc (a_opos a)) as [E'|E']; [rewrite E' in E; contradiction|]. reflexivity. }
{ exfalso. match goal with H: offset_val ipc _ <> offset_val (a_ipos a) _ |- _ => apply H; rewrite Hc; reflexivity end. }
Time Qed.

End CM_E3H62_1.
