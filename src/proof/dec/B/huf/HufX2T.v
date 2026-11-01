(* Sub-group X2T of group HUF (HufGroups.v): building an X2 table: HUF_buildDEltX2U32, HUF_buildDEltX2, HUF_fillDTableX2ForWeight, HUF_fillDTableX2Level2, HUF_fillDTableX2, HUF_readDTableX2_wksp.
   Choose one specification per function of ids_X2T (containing X2T_exports) and prove every body against
   G_HUF ++ X2T_imports and them. *)
Require Export Zstd.proof.dec.B.huf.HufGroups.
Require Export Zstd.proof.dec.B.huf.HufMAlign Zstd.proof.dec.B.huf.HufMDesc.
(* the specifications and the model, the bodies *)
Require Import Zstd.proof.dec.B.huf.HufX2S Zstd.proof.dec.B.huf.HufX2Mc Zstd.proof.dec.B.huf.HufX2Ml Zstd.proof.dec.B.huf.HufX2Mf Zstd.proof.dec.B.huf.HufX2Sc.
Require Import Zstd.proof.dec.B.huf.HufX2Bu Zstd.proof.dec.B.huf.HufX2Bw Zstd.proof.dec.B.huf.HufX2Bl Zstd.proof.dec.B.huf.HufX2Bf Zstd.proof.dec.B.huf.HufX2Br.

Lemma X2T_ok : X2T_obligation.
Proof.
  pose proof x2_count_ok as XC. pose proof x2_layout_ok as XL. pose proof (x2_fill_ok XC XL) as XF.
  pose proof (x2_u32s_cells XF) as XS.
  unfold X2T_obligation, subtree_ok. exists X2T_specs. split; [reflexivity | split].
  - intros x Hx. destruct Hx as [<- | []]. unfold X2T_specs. right; right; right; right; right; left; reflexivity.
  - change ((G_HUF ++ X2T_imports) ++ X2T_specs) with G_X2. unfold X2T_specs.
    repeat apply Forall_cons; try apply Forall_nil.
    + exists f_HUF_buildDEltX2U32; split; [reflexivity | split; [reflexivity | apply body_HUF_buildDEltX2U32]].
    + exists f_HUF_buildDEltX2; split; [reflexivity | split; [reflexivity | apply body_HUF_buildDEltX2]].
    + exists f_HUF_fillDTableX2ForWeight; split; [reflexivity | split; [reflexivity | apply body_HUF_fillDTableX2ForWeight]].
    + exists f_HUF_fillDTableX2Level2; split; [reflexivity | split; [reflexivity | apply body_HUF_fillDTableX2Level2; assumption]].
    + exists f_HUF_fillDTableX2; split; [reflexivity | split; [reflexivity | apply body_HUF_fillDTableX2; assumption]].
    + exists f_HUF_readDTableX2_wksp; split; [reflexivity | split; [reflexivity | apply body_HUF_readDTableX2_wksp; assumption]].
Qed.
