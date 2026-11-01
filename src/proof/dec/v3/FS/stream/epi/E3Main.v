(* FS3 streaming: the epilogue of ZSTD_decompressStream, assembled from the VST walk (E3HTop) and the pure
   obligations (E3Pure), with the exact claim (E3X: the loop invariant's ex_call at the loop's exit). *)
Require Import Zstd.proof.dec.v3.FS.stream.S3Main Zstd.proof.dec.v3.FS.stream.epi.E3Defs Zstd.proof.dec.v3.FS.stream.epi.E3Pure Zstd.proof.dec.v3.FS.stream.epi.E3HTop.
Require Import Zstd.proof.dec.v3.FS.stream.epi.E3X.
Local Open Scope logic.

Section CM_E3Main_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* exit_ok X4 gives the read-stage DDict facts the "can't release the hostage byte" return needs *)
Lemma epi_dd_gap_ok : forall (a: dsa) (w: lw), w_smw w = 0 -> exit_ok a w -> epi_dd_gap a w.
Proof.
intros a w Hs Hex Hi Hh.
destruct (Hex Hs) as (_ & _ & _ & _ & X4).
destruct (X4 Hi) as (_ & _ & [(H0 & _)|(_ & _ & _ & Hdd & _)]).
- rewrite Hh in H0. discriminate.
- exact Hdd.
Qed.

Lemma seg_epilogue_x_all : seg_epilogue_x.
Proof.
intros Espec DENT TABS BR a w HD HT Ha Hinv Hsmw Hst Hex Hun Hx.
pose proof Hinv as (Hip & Hop & Hloc & _).
apply epi_head; auto.
apply epi_pure; auto.
- apply epi_dd_gap_ok; auto.
- apply epi_xm_of; auto.
Qed.

End CM_E3Main_1.
