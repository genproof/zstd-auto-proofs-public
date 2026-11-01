(* FS3 streaming, case zdss_loadHeader, piece C, segment s9 (LH3C_lib.v). *)
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3C_lib.
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3C2_s9n.
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3C2_s9s.
Local Open Scope logic.

Section CM_LH3C2_s9_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma lhC_seg9_ok : lhC_seg9_stmt.
Proof.
unfold lhC_seg9_stmt.
intros Espec DENT TABS BR a w hb h tbl d1 did1 HP.
destruct (eq_dec (fst (getddict_res d1)) nullval) as [Hn | Hn].
- exact (lhC_seg9_none Espec DENT TABS BR a w hb h tbl d1 did1 HP Hn).
- exact (lhC_seg9_some Espec DENT TABS BR a w hb h tbl d1 did1 HP Hn).
Qed.

End CM_LH3C2_s9_1.
