(* FS3-bl BODY stages 3/4: the function specs of ZSTD_decompressContinue's context, computed once as a ground PTree
   (copy of s0/S0Delta: VST's simplify_func_tycontext recomputes it in every proof). *)
Require Export Zstd.proof.dec.v3.FS.BL.body.s34.S34Defs.
Local Open Scope logic.

Section CM_S34Delta_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Definition s34c_DS (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR': blrel) : Maps.PTree.t funspec :=
  ltac:(let d := make_ground_PTree (make_tycontext_s (FS3_G DENT TABS SR BR')) in exact d).

End CM_S34Delta_1.


(* simplify_func_tycontext with the precomputed specs *)
Ltac s34c_simplify :=
  match goal with |- semax (func_tycontext ?f ?V (FS3_G ?DENT ?TABS ?SR ?BR') ?A) _ _ _ =>
    let D1 := fresh "D1" in let Delta := fresh "Delta" in
    pose (D1 := (func_tycontext f V (FS3_G DENT TABS SR BR') A));
    pose (Delta := @abbreviate tycontext D1);
    change (func_tycontext f V (FS3_G DENT TABS SR BR') A) with Delta;
    unfold func_tycontext, make_tycontext in D1;
    let DS := fresh "Delta_specs" in
    let d := eval unfold s34c_DS in (s34c_DS DENT TABS SR BR') in
    pose (DS := @abbreviate (Maps.PTree.t funspec) d);
    change (make_tycontext_s (FS3_G DENT TABS SR BR')) with DS in D1;
    cbv beta iota zeta delta - [DS] in D1;
    subst D1;
    check_ground_Delta
  end.
