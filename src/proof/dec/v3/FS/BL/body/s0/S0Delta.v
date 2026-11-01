(* FS3-bl BODY stage 0: the function specs of ZSTD_decompressContinue's context, computed once as a
   ground PTree (VST's simplify_func_tycontext recomputes it in every proof: 7 s), and the tactic using it. *)
Require Export Zstd.proof.dec.v3.FS.BL.body.s0.S0Pure.
Local Open Scope logic.

Section CM_S0Delta_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Definition s0_DS (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR': blrel) : Maps.PTree.t funspec :=
  ltac:(let d := make_ground_PTree (make_tycontext_s (FS3_G DENT TABS SR BR')) in exact d).

End CM_S0Delta_1.


(* simplify_func_tycontext with the precomputed specs *)
Ltac s0_simplify :=
  match goal with |- semax (func_tycontext ?f ?V (FS3_G ?DENT ?TABS ?SR ?BR') ?A) _ _ _ =>
    let D1 := fresh "D1" in let Delta := fresh "Delta" in
    pose (D1 := (func_tycontext f V (FS3_G DENT TABS SR BR') A));
    pose (Delta := @abbreviate tycontext D1);
    change (func_tycontext f V (FS3_G DENT TABS SR BR') A) with Delta;
    unfold func_tycontext, make_tycontext in D1;
    let DS := fresh "Delta_specs" in
    let d := eval unfold s0_DS in (s0_DS DENT TABS SR BR') in
    pose (DS := @abbreviate (Maps.PTree.t funspec) d);
    change (make_tycontext_s (FS3_G DENT TABS SR BR')) with DS in D1;
    cbv beta iota zeta delta - [DS] in D1;
    subst D1;
    check_ground_Delta
  end.
