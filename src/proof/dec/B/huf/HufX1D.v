(* Sub-group X1D of group HUF (HufGroups.v): decoding with an X1 table: HUF_decodeSymbolX1, HUF_decodeStreamX1, the 1X1/4X1 bodies and internal entry points.
   Choose one specification per function of ids_X1D (containing X1D_exports) and prove every body against
   G_HUF ++ X1D_imports and them. *)
Require Export Zstd.proof.dec.B.huf.HufGroups.
Require Export Zstd.proof.dec.B.huf.HufMPeek.
Require Import Zstd.proof.dec.B.BCompose.
Require Import Zstd.proof.dec.B.huf.HufX1DSpecsBC Zstd.proof.dec.B.huf.HufX1DSym Zstd.proof.dec.B.huf.HufX1DStream Zstd.proof.dec.B.huf.HufX1D1BC Zstd.proof.dec.B.huf.HufX1D4BC.
Local Open Scope logic.

(* ---------- the wrappers (internal specifications in HufX1DSpecs.v) ---------- *)

Lemma body_HUF_decompress4X1_usingDTable_internal_default :
  semax_body Vprog [HUF_decompress4X1_usingDTable_internal_body_bc_spec]
    f_HUF_decompress4X1_usingDTable_internal_default HUF_decompress4X1_usingDTable_internal_default_bc_spec.
Proof.
  start_function.
  forward_call (gv, sht, dt, ht, sho, ob, oc, d, n, sh, base, N, c, off, s).
  Intros r. destruct r as [r oc']. simpl fst in *; simpl snd in *.
  forward.
  Exists r oc'. entailer!.
Qed.

Definition G_4X1int : funspecs :=
  [ HUF_decompress4X1_usingDTable_internal_default_bc_spec; HUF_decompress4X1_usingDTable_internal_fast_c_loop_spec;
    HUF_decompress4X1_usingDTable_internal_fast_spec ].

(* `fallbackFn = &HUF_decompress4X1_usingDTable_internal_default;` (contract item 8): the pointer's spec by
   make_func_ptr, the dead `if (0)` branches, the call through the pointer. *)
Lemma x1d_gap_fn_designator :
  semax_body Vprog G_4X1int f_HUF_decompress4X1_usingDTable_internal HUF_decompress4X1_usingDTable_internal_spec.
Proof.
  start_function.
  make_func_ptr _HUF_decompress4X1_usingDTable_internal_default.
  forward.
  make_func_ptr _HUF_decompress4X1_usingDTable_internal_fast_c_loop.
  forward.
  match goal with |- semax _ ?P _ _ => forward_if P end.
  { contradiction. }
  { forward_if; [contradiction | forward; entailer!]. }
  forward.
  match goal with |- semax _ ?P _ _ => forward_if P end.
  { contradiction. }
  { forward. entailer!. }
  forward_call (gv, sht, dt, ht, sho, ob, oc, d, n, sh, base, N, c, off, s).
  Intros r. destruct r as [r oc']. simpl fst in *; simpl snd in *.
  forward.
  Exists r oc'. entailer!.
  unfold func_ptr'. eapply derives_trans; [apply sepcon_derives; apply andp_left2; apply derives_refl|].
  rewrite emp_sepcon; apply derives_refl.
Qed.

Lemma body_HUF_decompress1X1_usingDTable_internal :
  semax_body Vprog [HUF_decompress1X1_usingDTable_internal_body_bc_spec]
    f_HUF_decompress1X1_usingDTable_internal HUF_decompress1X1_usingDTable_internal_spec.
Proof.
  start_function.
  forward_call (gv, sht, dt, ht, sho, ob, oc, d, n, sh, base, N, c, off, s).
  Intros r. destruct r as [r oc']. simpl fst in *; simpl snd in *.
  forward.
  Exists r oc'. entailer!.
Qed.

(* ---------- assembly ---------- *)

Definition G_X1Dall : funspecs := (G_HUF ++ X1D_imports) ++ X1D_specs_bc.

(* membership in a list of named specifications, by syntactic comparison (reflexivity on two different
   specifications unfolds them: slow) *)
Ltac in_spec :=
  solve [repeat match goal with |- In ?x (?y :: _) => first [constr_eq x y; left; reflexivity | right] end].

Lemma x1d_incl_util : incl Specs_util G_X1Dall.
Proof.
  intros x Hx. unfold G_X1Dall, G_HUF, G_B0, Gprog, Specs_L0.
  do 4 (apply in_or_app; left). apply in_or_app; right. apply in_cons. apply in_or_app; left. exact Hx.
Qed.

Lemma x1d_incl_bits : incl Specs_bits G_X1Dall.
Proof.
  intros x Hx. unfold G_X1Dall, G_HUF, G_B0, Gprog, Specs_L0.
  do 4 (apply in_or_app; left). apply in_or_app; right. apply in_cons. apply in_or_app; right.
  apply in_or_app; left. exact Hx.
Qed.

Lemma x1d_incl_imports : incl X1D_imports G_X1Dall.
Proof. intros x Hx. unfold G_X1Dall. apply in_or_app; left. apply in_or_app; right. exact Hx. Qed.

Lemma x1d_incl_specs : incl X1D_specs_bc G_X1Dall.
Proof. intros x Hx. unfold G_X1Dall. apply in_or_app; right. exact Hx. Qed.

Ltac x1d_incl :=
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx;
  repeat (destruct Hx as [<-|Hx];
          [ first [ apply x1d_incl_specs; unfold X1D_specs_bc; in_spec
                  | apply x1d_incl_imports; unfold X1D_imports; in_spec
                  | apply x1d_incl_bits; unfold Specs_bits; in_spec
                  | apply x1d_incl_util; unfold Specs_util; in_spec ] |]);
  contradiction.

Lemma x1d_nodup : NoDup (map fst Vprog ++ map fst G_X1Dall).
Proof. apply nodupb_ok. lazy. reflexivity. Qed.

Lemma X1D_ok : X1D_obligation.
Proof.
  unfold X1D_obligation, subtree_ok. exists X1D_specs_bc. split; [reflexivity | split].
  - intros x Hx. destruct Hx as [<- | [<- | []]]; unfold X1D_specs_bc; in_spec.
  - change ((G_HUF ++ X1D_imports) ++ X1D_specs_bc) with G_X1Dall.
    unfold X1D_specs_bc at 1. repeat apply Forall_cons; try apply Forall_nil.
    + apply (body_ok_mono G_sym); [ | unfold G_sym; x1d_incl | exact x1d_nodup ].
      exists f_HUF_decodeSymbolX1; split; [reflexivity | split; [reflexivity | exact body_HUF_decodeSymbolX1]].
    + apply (body_ok_mono G_stream); [ | unfold G_stream; x1d_incl | exact x1d_nodup ].
      exists f_HUF_decodeStreamX1; split; [reflexivity | split; [reflexivity | exact body_HUF_decodeStreamX1]].
    + apply (body_ok_mono G_1X1); [ | unfold G_1X1; x1d_incl | exact x1d_nodup ].
      exists f_HUF_decompress1X1_usingDTable_internal_body; split; [reflexivity | split; [reflexivity |
        exact body_HUF_decompress1X1_usingDTable_internal_body]].
    + apply (body_ok_mono G_4X1); [ | unfold G_4X1; x1d_incl | exact x1d_nodup ].
      exists f_HUF_decompress4X1_usingDTable_internal_body; split; [reflexivity | split; [reflexivity |
        exact body_HUF_decompress4X1_usingDTable_internal_body]].
    + apply (body_ok_mono [HUF_decompress4X1_usingDTable_internal_body_bc_spec]); [ | x1d_incl | exact x1d_nodup ].
      exists f_HUF_decompress4X1_usingDTable_internal_default; split; [reflexivity | split; [reflexivity |
        exact body_HUF_decompress4X1_usingDTable_internal_default]].
    + apply (body_ok_mono [HUF_decompress1X1_usingDTable_internal_body_bc_spec]); [ | x1d_incl | exact x1d_nodup ].
      exists f_HUF_decompress1X1_usingDTable_internal; split; [reflexivity | split; [reflexivity |
        exact body_HUF_decompress1X1_usingDTable_internal]].
    + apply (body_ok_mono G_4X1int); [ | unfold G_4X1int; x1d_incl | exact x1d_nodup ].
      exists f_HUF_decompress4X1_usingDTable_internal; split; [reflexivity | split; [reflexivity |
        exact x1d_gap_fn_designator]].
Qed.

