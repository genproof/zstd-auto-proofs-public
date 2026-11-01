(* FS3 streaming, case zdss_load: buffered-mode success after the call (P_load_cont_buf, statement in L3Stmts). *)
Require Import Zstd.proof.dec.v3.FS.stream.load.L3Stmts.
Require Import Zstd.proof.dec.v3.FS.stream.load.L3BfZ Zstd.proof.dec.v3.FS.stream.load.L3BfS.
Local Open Scope logic.

Section CM_L3ContBuf_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma load_cont_buf_ok : P_load_cont_buf.
Proof.
unfold P_load_cont_buf.
intros a k0 sv ipc opc oc dl E L ostart rr oc' fs' tabs' lxb M Hld Hst Hdm Hcb Hos Hor Hres Hok. cbv zeta.
case_eq (sv_fp sv); [intros Hfp|intros hb Hfp|intros hdr got Hfp|intros hdr z Hfp].
- destruct (lb_facts _ _ _ _ _ _ _ _ _ Hld Hst) as (_&_&_&Hcf&_). rewrite Hfp in Hcf.
  destruct Hcf as (_&_&_&_&_&[]).
- destruct (lb_facts _ _ _ _ _ _ _ _ _ Hld Hst) as (_&_&_&Hcf&_). rewrite Hfp in Hcf.
  destruct Hcf as (_&_&_&_&_&[]).
- cbn [is_skip negb]. rewrite andb_false_r.
  exact (load_cont_buf_s a k0 sv ipc opc oc dl E L ostart rr oc' fs' tabs' lxb hdr got M Hld Hst Hos Hor Hfp Hres Hok).
- cbn [is_skip negb]. rewrite andb_true_r.
  exact (load_cont_buf_z a k0 sv ipc opc oc dl E L ostart rr oc' fs' tabs' lxb hdr z M Hld Hst Hdm Hcb Hos Hor Hfp Hres
           Hok).
Qed.

End CM_L3ContBuf_1.
