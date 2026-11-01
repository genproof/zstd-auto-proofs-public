(* Sub-group X2D of group HUF (HufGroups.v): decoding with an X2 table: HUF_decodeSymbolX2, HUF_decodeLastSymbolX2, HUF_decodeStreamX2, the 1X2/4X2 bodies and internal entry points.
   Choose one specification per function of ids_X2D (containing X2D_exports) and prove every body against
   G_HUF ++ X2D_imports and them. *)
Require Export Zstd.proof.dec.B.huf.HufGroups.
Require Export Zstd.proof.dec.B.huf.HufMAlign.
Require Import Zstd.proof.dec.B.BCompose.
Require Import Zstd.proof.dec.B.huf.HufX2DSpecs Zstd.proof.dec.B.huf.HufX2DSym Zstd.proof.dec.B.huf.HufX2DLast Zstd.proof.dec.B.huf.HufX2DStream Zstd.proof.dec.B.huf.HufX2D1 Zstd.proof.dec.B.huf.HufX2D4.
Local Open Scope logic.

(* ---------- the wrappers (internal specifications in HufX2DSpecs.v) ---------- *)

Lemma body_HUF_decompress4X2_usingDTable_internal_default :
  semax_body Vprog [HUF_decompress4X2_usingDTable_internal_body_spec]
    f_HUF_decompress4X2_usingDTable_internal_default HUF_decompress4X2_usingDTable_internal_default_spec.
Proof.
  start_function.
  forward_call (gv, sht, dt, ht, sho, ob, oc, d, n, sh, base, N, c, off, s).
  Intros r. destruct r as [r oc']. simpl fst in *; simpl snd in *.
  forward.
  Exists r oc'. entailer!.
Qed.

Definition G_4X2int : funspecs :=
  [ HUF_decompress4X2_usingDTable_internal_default_spec; HUF_decompress4X2_usingDTable_internal_fast_c_loop_spec;
    HUF_decompress4X2_usingDTable_internal_fast_spec ].

Lemma body_HUF_decompress4X2_usingDTable_internal :
  semax_body Vprog G_4X2int f_HUF_decompress4X2_usingDTable_internal HUF_decompress4X2_usingDTable_internal_spec.
Proof.
  start_function.
  make_func_ptr _HUF_decompress4X2_usingDTable_internal_default.
  forward.
  make_func_ptr _HUF_decompress4X2_usingDTable_internal_fast_c_loop.
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

Lemma body_HUF_decompress1X2_usingDTable_internal :
  semax_body Vprog [HUF_decompress1X2_usingDTable_internal_body_spec]
    f_HUF_decompress1X2_usingDTable_internal HUF_decompress1X2_usingDTable_internal_spec.
Proof.
  start_function.
  forward_call (gv, sht, dt, ht, sho, ob, oc, d, n, sh, base, N, c, off, s).
  Intros r. destruct r as [r oc']. simpl fst in *; simpl snd in *.
  forward.
  Exists r oc'. entailer!.
Qed.

(* ---------- assembly ---------- *)

Definition G_X2D : funspecs := (G_HUF ++ X2D_imports) ++ X2D_specs.

Lemma X2D_nodup : NoDup (map fst Vprog ++ map fst G_X2D).
Proof. apply nodupb_ok. vm_compute. reflexivity. Qed.

Ltac in_spec := solve [repeat (first [left; reflexivity | right])].

(* In x l for a list of spec names l (syntactic search, no unfolding of the specs) *)
Ltac in_syn := match goal with
  | |- In ?x (?x :: _) => left; reflexivity
  | |- In ?x (_ :: _) => right; in_syn
  end.
Ltac in_X2D := unfold G_X2D, G_HUF, G_B0, Gprog, Specs_L0, Specs_util, Specs_bits, Specs_xxh, ENT_exports,
  H_exports, Zstd_Imports, X2D_imports, X2D_specs; cbn [app]; in_syn.

Lemma X2D_lift (G: funspecs) (ix: ident * funspec) :
  incl G G_X2D -> Layer.body_ok G ix -> Layer.body_ok G_X2D ix.
Proof. intros Hi Hb. exact (body_ok_mono G G_X2D ix Hb Hi X2D_nodup). Qed.

Ltac incl_X2D := let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; cbv [G_sym2 G_stream2 G_1X2 G_4X2 G_4X2int] in Hx;
  repeat (destruct Hx as [<-|Hx]; [in_X2D|]); contradiction.

Ltac body_X2D G f := apply (X2D_lift G); [incl_X2D | exists f; split; [reflexivity | split; [reflexivity|]]].

Lemma X2D_ok_from (Hf: hsym_facts) : X2D_obligation.
Proof.
  unfold X2D_obligation, subtree_ok. exists X2D_specs. split; [reflexivity | split].
  - intros x Hx. unfold X2D_exports in Hx. unfold X2D_specs.
    repeat (destruct Hx as [<-|Hx]; [in_spec|]); contradiction.
  - change ((G_HUF ++ X2D_imports) ++ X2D_specs) with G_X2D. unfold X2D_specs.
    repeat apply Forall_cons; try apply Forall_nil.
    + body_X2D G_sym2 f_HUF_decodeSymbolX2. apply body_HUF_decodeSymbolX2.
    + body_X2D G_sym2 f_HUF_decodeLastSymbolX2. apply body_HUF_decodeLastSymbolX2.
    + body_X2D G_stream2 f_HUF_decodeStreamX2. apply body_HUF_decodeStreamX2; exact Hf.
    + body_X2D G_1X2 f_HUF_decompress1X2_usingDTable_internal_body.
      apply body_HUF_decompress1X2_usingDTable_internal_body.
    + body_X2D G_4X2 f_HUF_decompress4X2_usingDTable_internal_body.
      apply body_HUF_decompress4X2_usingDTable_internal_body; exact Hf.
    + body_X2D [HUF_decompress4X2_usingDTable_internal_body_spec] f_HUF_decompress4X2_usingDTable_internal_default.
      apply body_HUF_decompress4X2_usingDTable_internal_default.
    + body_X2D G_4X2int f_HUF_decompress4X2_usingDTable_internal.
      apply body_HUF_decompress4X2_usingDTable_internal.
    + body_X2D [HUF_decompress1X2_usingDTable_internal_body_spec] f_HUF_decompress1X2_usingDTable_internal.
      apply body_HUF_decompress1X2_usingDTable_internal.
Qed.

Lemma X2D_ok : X2D_obligation.
Proof.
  apply X2D_ok_from. split.
  - intros ht s L pos. apply hsym_peek.
  - intros ht s L pos v n1. apply hsym_pair.
Qed.
