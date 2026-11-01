(* FS3 one-shot: a DDict pointer is valid (its first field) *)
Require Import Zstd.proof.dec.v3.FS.FSOblig3.
Local Open Scope logic.

Section CM_O3Valid_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma ddict_rep_at_valid DENT gv x buf : ddict_rep_at DENT gv x buf |-- valid_pointer (dx_q x).
Proof.
  unfold ddict_rep_at, ddict_struct. Intros.
  apply derives_trans with (field_at_ Ews (Tstruct _ZSTD_DDict_s noattr) (DOT _dictBuffer) (dx_q x) * TT); [cancel | ].
  apply sepcon_valid_pointer1. unfold field_at_.
  apply field_at_valid_ptr0; [auto | simpl; lia | reflexivity].
Qed.

Lemma DD3_valid DENT gv q dd : DD3_of DENT gv q dd = (DD3_of DENT gv q dd && valid_pointer q).
Proof.
  apply pred_ext; [apply andp_right; [auto | ] | apply andp_left1; auto].
  unfold DD3_of. apply (ddict_rep_at_valid DENT gv (dd_x q dd) (dd_buf dd)).
Qed.

End CM_O3Valid_1.
