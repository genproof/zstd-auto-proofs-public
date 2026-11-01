(* FS3 streaming, case zdss_load: ld_rest from ld_join (ld_if1; ld_if2; the unit), and the whole case
   seg_case_x 3 (with the exact claim, load/L3Ex.v) from the pure obligations LD3. *)
Require Import Zstd.proof.dec.v3.FS.stream.load.L3Stmts Zstd.proof.dec.v3.FS.stream.load.L3Borrow Zstd.proof.dec.v3.FS.stream.load.L3Dsub Zstd.proof.dec.v3.FS.stream.load.L3VIf Zstd.proof.dec.v3.FS.stream.load.L3VCall Zstd.proof.dec.v3.FS.stream.load.L3VUBuf Zstd.proof.dec.v3.FS.stream.load.L3VUSt Zstd.proof.dec.v3.FS.stream.load.L3VTop.
Local Open Scope logic.

Section CM_L3VRest_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* buffered mode: the segment holds frame output only (c_ring, R1c) *)
Lemma ld_cbound : forall a k sv ipc opc oc dl, call_inv a k sv ipc opc oc dl -> sf_stage (c3_s k) = zdss_load ->
  dc_stable (a_st a) = false -> lay_cbound (sv_fp sv) (sv_lay sv).
Proof.
intros a k sv ipc opc oc dl Hi Hs Hst.
destruct Hi as (_&_&_&_&_&_&_&_&_&_&_&_&Hcore&_).
unfold c_core in Hcore. destruct Hcore as (_&_&_&Hc). rewrite Hs in Hc. simpl in Hc.
destruct Hc as (_&_&Hring&_). rewrite Hst in Hring.
destruct Hring as (_&_&_&os&oe&_&_&_&Hr). cbv beta iota in Hr.
destruct Hr as (_&_&_&_&Hl).
intros b ps pe e El. rewrite El in Hl. destruct Hl as (_&_&_&Hpc&_). exact Hpc.
Qed.

Lemma ld_rest_ok : MF3 -> RET3x -> LD3 -> P_ld_rest.
Proof.
intros HMF HRET [Hhs [Hhb [Hcs [Hcb Hew]]]].
intros Espec DENT TABS BR a k0 sv ipc opc oc dl E L R HD HT Ha Hs0 Hinv Hun Hstage HE HE0 HL Hrl0 Hx HRn HRr.
rewrite ld_rest_eq.
eapply semax_seq; [apply (ld_if1_ok Espec DENT TABS BR a k0 sv ipc opc oc dl E L _ Ha Hinv Hstage HE HE0 HL)|].
eapply semax_seq.
{ apply (ld_if2_ok Espec DENT TABS BR a k0 sv ipc opc oc dl E L _ HMF Ha Hinv Hun Hstage HE HE0 HL Hrl0 Hx).
  destruct R; cbn in HRn |- *; exact HRn. }
destruct (dc_stable (a_st a)) eqn:Hstable.
- exact (ld_unit_st Espec DENT TABS BR a k0 sv ipc opc oc dl E L R HMF HRET Hhs Hcs Hew HD HT Ha Hs0
           Hinv Hstage HE HE0 HL Hrl0 Hstable HRn HRr).
- exact (ld_unit_buf Espec DENT TABS BR a k0 sv ipc opc oc dl E L R HMF HRET Hhb Hcb Hew
           (ld_cbound a k0 sv ipc opc oc dl Hinv Hstage Hstable) HD HT Ha Hs0
           Hinv (fun _ => Hun eq_refl) Hstage HE HE0 HL Hrl0 Hstable Hx HRn HRr).
Qed.

Lemma seg_load_gen : MF3 -> RET3x -> LD3 -> seg_case_x 3.
Proof. intros. apply seg_load_top. apply ld_rest_ok; assumption. Qed.

End CM_L3VRest_1.
