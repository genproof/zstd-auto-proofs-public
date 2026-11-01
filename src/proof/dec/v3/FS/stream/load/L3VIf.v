(* FS3 streaming, case zdss_load: after loadedSize: `if (loadedSize) ip += ..; inPos += ..` (ld_if1) and
   `if (loadedSize < toLoad) { someMoreWork = 0; break; }` (ld_if2).  Port of v2 ld_if1_ok / ld_if2_ok. *)
Require Import Zstd.proof.dec.v3.FS.stream.load.L3Stmts Zstd.proof.dec.v3.FS.stream.load.L3Dsub.
Require Import Zstd.proof.dec.v3.FS.stream.load.L3Ex.
Local Open Scope logic.

Section CM_L3VIf_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* ld_join once the whole unit is known to be loaded (L = E - inPos) *)
Definition ld_join_full (DENT: dent_pred) (TABS: tabs_pred) (a: dsa) (k: cst3) (sv: sview) (ipc opc: Z)
    (oc: list val) (dl: list Z) (E L: Z) : environ -> mpred :=
  let w := {| w_smw := 1; w_k := k; w_sv := sv; w_ipc := ipc; w_opc := opc; w_oc := oc; w_dl := dl |} in
  PROPx [L = E - fp_inpos (sv_fp sv)]
    (LOCALx (temp _loadedSize (vlong L) :: temp _toLoad__1 (vlong (E - fp_inpos (sv_fp sv))) ::
             temp _neededInSize__1 (vlong E) :: ds_LI_L a w)
           (SEPx (ds_LI_S DENT TABS a w))).

(* ld_rest = if (loadedSize) ...; if (loadedSize < toLoad) { ... break; }; ld_unit *)
Definition ld_if1 : statement := match ld_rest with Ssequence s _ => s | _ => Sskip end.
Definition ld_if2 : statement := match ld_rest with Ssequence _ (Ssequence s _) => s | _ => Sskip end.
Definition ld_unit : statement :=
  match ld_rest with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ u))) => u | _ => Sskip end.
Definition ld_unit0 : statement :=
  match ld_rest with Ssequence _ (Ssequence _ u) => u | _ => Sskip end.
Lemma ld_rest_eq : ld_rest = Ssequence ld_if1 (Ssequence ld_if2 ld_unit0).
Proof. reflexivity. Qed.

End CM_L3VIf_1.

Ltac ldunf := unfold ld_join, ds_LI_L, ds_LI_S, k_load, c3_with_s, ctx_rep3, ctx_body3, fgroup3, sgroup, sf_given, frame_fields;
  cbn [w_k w_sv w_ipc w_opc w_oc w_dl w_smw c3_fs c3_tabs c3_stable c3_dict c3_s c3_par c3_sp c3_set s_load
       sf_stage sf_inBuff sf_inSize sf_inPos sf_outBuff sf_outSize sf_outStart sf_outEnd sf_lhSize
       sf_hostage sf_nfp sf_expOut sf_hbuf sf_over sf_ring sf_mem sf_held sf_given].

Section CM_L3VIf_2.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.

Lemma ld_if1_ok : forall (Espec: OracleKind) DENT TABS BR a k0 sv ipc opc oc dl E L R,
  dsa_ok a -> call_inv a k0 sv ipc opc oc dl -> sf_stage (c3_s k0) = zdss_load ->
  fs_expected (c3_fs k0) = vlong E -> 0 <= E < 2 ^ 32 ->
  L = Z.min (E - fp_inpos (sv_fp sv)) (a_isz a - ipc) ->
  semax (ds_Delta DENT TABS BR) (ld_join DENT TABS a
       (k_load k0 (fp_inpos (sv_fp sv))
          (ring_load (sv_fp sv) (sf_ring (c3_s k0)) (fp_inpos (sv_fp sv)) (a_ibs a) ipc L))
       sv ipc opc oc dl E L) ld_if1 (overridePost (ld_join DENT TABS a
       (k_load k0 (fp_inpos (sv_fp sv) + L)
          (ring_load (sv_fp sv) (sf_ring (c3_s k0)) (fp_inpos (sv_fp sv)) (a_ibs a) ipc L))
       sv (ipc + L) opc oc dl E L) R).
Proof.
intros Espec DENT TABS BR a k0 sv ipc opc oc dl E L R Ha Hinv Hstage HE HE0 HL.
destruct R as [Rn Rb Rc Rr].
apply (ld_Delta_lift DENT TABS BR nil); [intros sp []|]. unfold ld_DeltaG.
cbv beta iota delta [ld_if1 ld_rest ds_case_load].
set (P := fp_inpos (sv_fp sv)) in *.
set (ring1 := ring_load (sv_fp sv) (sf_ring (c3_s k0)) P (a_ibs a) ipc L).
pose proof Ha as Ha'.
destruct Ha' as (Hbo & Hbi & Hstb & Hwo & Hwi & Hwob & Hrb & Hdict & Herr & Hopos & Hosz & Hloc0 & Hipos & Hisz & Hlibs & Hbibs & Hstbuf & Hwit).
pose proof Hinv as Hinv'.
destruct Hinv' as (Hipc & Hopc & Hloc & Hpre & Hldl & Hdl & Hbdl & Hbase & Hbin & Hnfp1 & Hnfp2 & Hnfp3 & Hcore &
                  Hdd & Hstout & Hahead & Hbsm & Hmodel & Hlh & Hsah & Hexp & HTT).
destruct (load_facts _ _ _ _ _ Hcore Hstage) as (E' & fstg & HE' & HP & HPE & HE32 & Hfst & Hfst7 & Hskip & HEin & [ts Hts] & Hib).
rewrite HE in HE'. unfold vlong in HE'. inversion HE' as [HEq].
rewrite !Int64.Z_mod_modulus_eq, !Z.mod_small in HEq by rep_lia. subst E'. clear HE'.
assert (HL0: 0 <= L <= E - P) by (subst L; lia).
ldunf. Intros.
forward_if (ld_join DENT TABS a (k_load k0 (P + L) ring1) sv (ipc + L) opc oc dl E L).
{ forward. forward. forward. ldunf. entailer!. rewrite add_ptr_long_off by (auto; rep_lia). reflexivity. }
{ match goal with H: Int64.repr L = Int64.zero |- _ =>
    apply (f_equal Int64.unsigned) in H; rewrite Int64.unsigned_repr in H by rep_lia; rewrite Int64.unsigned_zero in H end.
  forward. ldunf. replace (ipc + L) with ipc by lia. replace (P + L) with P by lia. entailer!. }
ldunf. entailer!.
Qed.

Lemma ld_if2_ok : forall (Espec: OracleKind) DENT TABS BR a k0 sv ipc opc oc dl E L R,
  MF3 -> dsa_ok a -> call_inv a k0 sv ipc opc oc dl -> (dc_stable (a_st a) = false -> sublist opc (a_osz a) oc = sublist opc (a_osz a) (a_oc a)) ->
  sf_stage (c3_s k0) = zdss_load ->
  fs_expected (c3_fs k0) = vlong E -> 0 <= E < 2 ^ 32 ->
  L = Z.min (E - fp_inpos (sv_fp sv)) (a_isz a - ipc) ->
  Zlength (sf_ring (c3_s k0)) = sf_inSize (c3_s k0) + sf_outSize (c3_s k0) ->
  ex_call a (ld_w0 k0 sv ipc opc oc dl) ->
  RA_break R = ds_inv_x DENT TABS a ->
  semax (ds_Delta DENT TABS BR) (ld_join DENT TABS a
       (k_load k0 (fp_inpos (sv_fp sv) + L)
          (ring_load (sv_fp sv) (sf_ring (c3_s k0)) (fp_inpos (sv_fp sv)) (a_ibs a) ipc L))
       sv (ipc + L) opc oc dl E L) ld_if2
    (overridePost ((ld_join_full DENT TABS a
       (k_load k0 (fp_inpos (sv_fp sv) + L)
          (ring_load (sv_fp sv) (sf_ring (c3_s k0)) (fp_inpos (sv_fp sv)) (a_ibs a) ipc L))
       sv (ipc + L) opc oc dl E L)) R).
Proof.
intros Espec DENT TABS BR a k0 sv ipc opc oc dl E L R HMF Ha Hinv Hun Hstage HE HE0 HL Hrl Hx HRb.
destruct R as [Rn Rb Rc Rr]; cbn [RA_break] in HRb; subst Rb.
apply (ld_Delta_lift DENT TABS BR nil); [intros sp []|]. unfold ld_DeltaG.
cbv beta iota delta [ld_if2 ld_rest ds_case_load].
set (P := fp_inpos (sv_fp sv)) in *.
set (ring1 := ring_load (sv_fp sv) (sf_ring (c3_s k0)) P (a_ibs a) ipc L).
pose proof Ha as Ha'.
destruct Ha' as (Hbo & Hbi & Hstb & Hwo & Hwi & Hwob & Hrb & Hdict & Herr & Hopos & Hosz & Hloc0 & Hipos & Hisz & Hlibs & Hbibs & Hstbuf & Hwit).
pose proof Hinv as Hinv'.
destruct Hinv' as (Hipc & Hopc & Hloc & Hpre & Hldl & Hdl & Hbdl & Hbase & Hbin & Hnfp1 & Hnfp2 & Hnfp3 & Hcore &
                  Hdd & Hstout & Hahead & Hbsm & Hmodel & Hlh & Hsah & Hexp & HTT).
destruct (load_facts _ _ _ _ _ Hcore Hstage) as (E' & fstg & HE' & HP & HPE & HE32 & Hfst & Hfst7 & Hskip & HEin & [ts Hts] & Hib).
rewrite HE in HE'. unfold vlong in HE'. inversion HE' as [HEq].
rewrite !Int64.Z_mod_modulus_eq, !Z.mod_small in HEq by rep_lia. subst E'. clear HE'.
assert (HL0: 0 <= L <= E - P) by (subst L; lia).
ldunf. Intros.
forward_if (L = E - P).
{ forward. forward.
  unfold ds_inv_x.
  Exists {| w_smw := 0; w_k := k_load k0 (P + L) ring1; w_sv := sv_load sv (sublist ipc (ipc + L) (a_ibs a));
            w_ipc := ipc + L; w_opc := opc; w_oc := oc; w_dl := dl |}.
  assert (Hlt: L < E - P) by first [lia | cond64h; lia].
  pose proof (load_partial_inv a k0 sv ipc opc oc dl E L HMF Ha Hinv Hstage HE HE0 HL Hlt) as Hpi.
  assert (Hle: loop_extra {| w_smw := 0; w_k := k_load k0 (P + L) ring1;
     w_sv := sv_load sv (sublist ipc (ipc + L) (a_ibs a)); w_ipc := ipc + L; w_opc := opc; w_oc := oc; w_dl := dl |})
    by (intro Hc; discriminate).
  pose proof (load_partial_exit a k0 sv ipc opc oc dl L ring1 Hinv Hstage
                ltac:(destruct (Z.min_spec (E - P) (a_isz a - ipc)); lia)) as Hex.
  assert (Hent: entry_ok a {| w_smw := 0; w_k := k_load k0 (P + L) ring1;
     w_sv := sv_load sv (sublist ipc (ipc + L) (a_ibs a)); w_ipc := ipc + L; w_opc := opc; w_oc := oc; w_dl := dl |})
    by (intro Hc; discriminate).
  assert (Hun': untouched_ok a {| w_smw := 0; w_k := k_load k0 (P + L) ring1;
     w_sv := sv_load sv (sublist ipc (ipc + L) (a_ibs a)); w_ipc := ipc + L; w_opc := opc; w_oc := oc; w_dl := dl |})
    by exact Hun.
  assert (Hxs: ex_call a {| w_smw := 0; w_k := k_load k0 (P + L) ring1;
     w_sv := sv_load sv (sublist ipc (ipc + L) (a_ibs a)); w_ipc := ipc + L; w_opc := opc; w_oc := oc; w_dl := dl |})
    by exact (ld_x_stop a k0 sv ipc opc oc dl E L Ha Hinv Hstage HE HE0 HL Hlt Hrl Hx).
  unfold ds_LI_Px. ldunf.
  entailer!. }
{ forward. entailer!. all: first [lia | cond64h; lia]. }
unfold ld_join_full. ldunf. entailer!.
Qed.

End CM_L3VIf_2.
