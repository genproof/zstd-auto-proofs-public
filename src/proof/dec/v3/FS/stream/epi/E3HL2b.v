(* FS3 streaming: the epilogue's head, piece: the 16th call without progress, input left: on to the tail. *)
Require Import Zstd.proof.dec.v3.FS.stream.S3Main Zstd.proof.dec.v3.FS.stream.epi.E3Defs Zstd.proof.dec.v3.FS.stream.epi.E3Vst Zstd.proof.dec.v3.FS.stream.epi.E3T0 Zstd.proof.dec.v3.FS.stream.epi.E3H0.
Local Open Scope logic.

Section CM_E3HL2b_1.
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

Lemma head_l2_ok : forall (Espec: OracleKind) DENT TABS BR (a: dsa) (k: cst3) (ipc opc: Z) (oc1: list val) (n: Z),
  dsa_ok a -> a_ipos a <= ipc <= a_isz a -> a_opos a <= opc <= a_osz a -> Zlength oc1 = a_osz a ->
  ipc <> a_isz a -> tail_ok a (k_nfp a k opc n) ipc opc oc1 ->
  semax epi_Delta0 (hpre DENT TABS a (k_nfp a k opc n) ipc ipc opc opc oc1 []) ds_l2
    (overridePost (emid DENT TABS a k ipc opc oc1) (ds_R_x DENT TABS BR a)).
Proof.
intros Espec DENT TABS BR a k ipc opc oc1 n Ha Hip Hop Hloc Ei Pnp.
pose proof Ha as (Hbufo & Hbufi & Hstbuf & Hwso & Hwsi & Hwsob & Hrsb & Hdict & Herr & Hopos & Hosz & Hloc0 &
                  Hipos & Hisz & Hlibs & Hbibs & Hstout0 & Hw0 & Hstpos & _).
unfold emid. epi_fstart. unfold ds_l2.
assert_PROP (isptr (a_ib a)) as Pib by entailer!.
apply semax_dowhile0_gen.
match goal with |- semax _ _ _ ?Q =>
  let Q' := eval cbv beta iota delta [overridePost loop1_ret_assert] in Q in change Q with Q' end.
abbreviate_semax.
forward_if.
{ entailer!. apply epi_tc_test_eq; auto; epi_wvp (a_W a) (a_shb a) (zbytes (a_ibs a)) (a_ib a). }
{ match goal with H: offset_val ipc _ = offset_val (a_isz a) _ |- _ =>
    apply epi_off_inj_any in H; [contradiction|auto; lia..] end. }
{ forward. Exists n. unfold epi_S. entailer!. }
Time Qed.

End CM_E3HL2b_1.
