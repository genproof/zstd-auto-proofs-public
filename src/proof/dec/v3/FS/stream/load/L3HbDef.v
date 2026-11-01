(* FS3 streaming, case zdss_load: the history cells of a segment [0, d) of an array of bytes and
   an extDict (in the array, or a separate array of bytes) are bytes (helpers of load_cont_hist_buf_ok). *)
Require Import Zstd.proof.dec.v3.FS.stream.load.L3Stmts.
Local Open Scope logic.

Section CM_L3HbDef_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma hb_byte_Znth : forall (l: list val) j, byte_cells l -> 0 <= j < Zlength l -> is_byte_val (Znth j l).
Proof. intros l j H Hj. unfold byte_cells in H. rewrite Forall_Znth in H. exact (H j Hj). Qed.

Lemma hb_zbytes_cells : forall l, bytes_ok l -> byte_cells (zbytes l).
Proof.
intros l H. unfold byte_cells, zbytes. induction H as [|b l Hb Hl IH]; simpl; constructor; auto.
exists b. split; [exact Hb|reflexivity].
Qed.

Definition hb_ext_ok (oc: list val) (e: ext_seg) : Prop :=
  match e with
  | ExtNone => True
  | ExtIn e1 elen => 0 <= e1 - elen /\ e1 <= Zlength oc
  | ExtSep _ _ _ ec e1 elen => byte_cells ec /\ 0 <= e1 - elen /\ e1 <= Zlength ec
  end.

Lemma hb_hist_def : forall oc d ps e, byte_cells oc -> 0 <= ps \/ d <= ps -> d <= Zlength oc -> hb_ext_ok oc e ->
  hist_def oc d ps e.
Proof.
intros oc d ps e Hb Hps Hd He k Hk. unfold chist. destruct (k <=? d - ps) eqn:E.
- apply Z.leb_le in E. apply hb_byte_Znth; auto; lia.
- apply Z.leb_gt in E. destruct e as [|e1 elen|sh eb en ec e1 elen]; cbn [ext_len hb_ext_ok] in Hk, He.
  + lia.
  + apply hb_byte_Znth; auto; lia.
  + destruct He as (Hc&?&?). apply hb_byte_Znth; auto; lia.
Qed.

End CM_L3HbDef_1.
