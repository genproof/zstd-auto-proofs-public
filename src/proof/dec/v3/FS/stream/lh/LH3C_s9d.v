(* FS3 streaming, case zdss_loadHeader, piece C, segment s9: ds_Delta precomputed once
   (simplify_func_tycontext's make_ground_PTree on stream_G3 costs ~15 s per use). *)
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3C_lib.
Local Open Scope logic.

Section CM_LH3C_s9d_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Definition lhC9_DS (DENT: dent_pred) (TABS: tabs_pred) (BR: blrel) : Maps.PTree.t funspec :=
  ltac:(let d := make_ground_PTree (make_tycontext_s (stream_G3 DENT TABS BR)) in exact d).

Definition lhC9_D (DENT: dent_pred) (TABS: tabs_pred) (BR: blrel) : tycontext := ltac:(
  let t := eval unfold ds_Delta, func_tycontext, make_tycontext in (ds_Delta DENT TABS BR) in
  let t := match t with context C [make_tycontext_s ?g] => context C [lhC9_DS DENT TABS BR] end in
  let t := eval cbv beta iota zeta delta - [lhC9_DS] in t in exact t).

End CM_LH3C_s9d_1.


(* simplify_func_tycontext for ds_Delta DENT TABS BR, with the precomputed table of specs *)
Ltac lhC9_Delta DENT TABS BR :=
  let D1 := fresh "D1" in let Delta := fresh "Delta" in
  pose (D1 := lhC9_D DENT TABS BR);
  pose (Delta := @abbreviate tycontext D1);
  change (ds_Delta DENT TABS BR) with Delta;
  unfold lhC9_D in D1;
  let DS := fresh "Delta_specs" in
  let d := eval cbv beta delta [lhC9_DS] in (lhC9_DS DENT TABS BR) in
  pose (DS := @abbreviate (Maps.PTree.t funspec) d);
  change (lhC9_DS DENT TABS BR) with DS in D1;
  subst D1; check_ground_Delta.
