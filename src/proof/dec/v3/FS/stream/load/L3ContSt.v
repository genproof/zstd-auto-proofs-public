(* FS3 streaming, case zdss_load: stable-mode success after the call (P_load_cont_stable, statement in L3Stmts). *)
Require Import Zstd.proof.dec.v3.FS.stream.load.L3Stmts.
Require Import Zstd.proof.dec.v3.FS.stream.load.L3StZ Zstd.proof.dec.v3.FS.stream.load.L3StS.
Local Open Scope logic.

Section CM_L3ContSt_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma load_cont_stable_ok : P_load_cont_stable.
Proof.
unfold P_load_cont_stable.
intros a k0 sv ipc opc oc dl E L rr oc' fs' tabs' lxb M Hld Hst Hdm Hres Hok.
case_eq (sv_fp sv); [intros Hfp|intros hb Hfp|intros hdr got Hfp|intros hdr z Hfp].
- destruct (ld_st_facts _ _ _ _ _ _ _ _ _ Hld Hst) as (_&_&_&Hcf&_). rewrite Hfp in Hcf.
  destruct Hcf as (_&_&_&_&_&[]).
- destruct (ld_st_facts _ _ _ _ _ _ _ _ _ Hld Hst) as (_&_&_&Hcf&_). rewrite Hfp in Hcf.
  destruct Hcf as (_&_&_&_&_&[]).
- exact (load_cont_stable_s a k0 sv ipc opc oc dl E L rr oc' fs' tabs' lxb hdr got M Hld Hst Hfp Hres Hok).
- exact (load_cont_stable_z a k0 sv ipc opc oc dl E L rr oc' fs' tabs' lxb hdr z M Hld Hst Hdm Hfp Hres Hok).
Qed.

End CM_L3ContSt_1.
