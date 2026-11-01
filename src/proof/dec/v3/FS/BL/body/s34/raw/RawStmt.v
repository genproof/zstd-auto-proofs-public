(* FS3-bl BODY, stages 3/4, raw block: the statements of case 0 after ZSTD_copyRawBlock, the
   arrays of the call. *)
Require Export Zstd.proof.dec.v3.FS.BL.body.s34.raw.RawDbg.
Local Open Scope logic.

Section CM_RawStmt_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Definition raw_s0 : statement :=
  ltac:(let s := eval cbv [s34_ls] in s34_ls in
        lazymatch s with LScons (Some 2) _ (LScons (Some 0) ?s0 _) => exact s0 end).

Definition raw_more : statement :=
  ltac:(let s := eval cbv [s34_ls] in s34_ls in
        lazymatch s with LScons (Some 2) _ (LScons (Some 0) _ ?r) => exact (seq_of_labeled_statement r) end).

(* after `rSize = ZSTD_copyRawBlock(...)` *)
Definition raw_after : statement :=
  ltac:(let s := eval cbv [raw_s0] in raw_s0 in lazymatch s with Ssequence _ ?t => exact t end).

Definition raw_o (shd: share) (ob: val) (oc: list val) (opos: Z) : outarr :=
  {| oa_sh := shd; oa_base := ob; oa_N := Zlength oc; oa_c := oc; oa_d := opos; oa_cap := Zlength oc - opos |}.

Definition raw_i (shs: share) (src: val) (c: list Z) : inwin :=
  {| iw_sh := shs; iw_base := src; iw_N := Zlength c; iw_c := zbytes c; iw_off := 0; iw_s := c |}.

Lemma raw_sel : seq_of_labeled_statement (select_switch 0 s34_ls) =
  Ssequence (Ssequence (ltac:(let s := eval cbv [raw_s0] in raw_s0 in
                              lazymatch s with Ssequence ?h _ => exact h end)) raw_after) raw_more.
Proof. reflexivity. Qed.

End CM_RawStmt_1.
