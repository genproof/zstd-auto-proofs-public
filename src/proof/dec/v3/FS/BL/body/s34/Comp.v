(* FS3-bl BODY, stages 3/4: the compressed block (case 2) part (S34Defs.v). *)
Require Export Zstd.proof.dec.v3.FS.BL.body.s34.S34Defs.
Require Import Zstd.proof.dec.v3.FS.BL.body.s34.comp.CompPos.
Require Import Zstd.proof.dec.v3.FS.BL.body.s34.comp.CompZero.
Require Import Zstd.proof.dec.v3.FS.BL.body.s34.comp.CompD13.
Local Open Scope logic.

Section CM_Comp_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* comp/: CompPure (the call's history context, layout and pointer facts), CompHist (the history zstd sees),
   CompPost (the callee's post to s34_mid_ok), CompPos (capacity > 0: the whole output array), CompZero
   (capacity 0: an empty window, the array lent to the witnesses), CompD13 (bytes_ok of the model's output) *)
Lemma s34_comp_ok : s34_case_spec 2.
Proof.
  intros Espec DENT TABS SR BR' HD HT W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v_bp v pcs st
    Hpr Hpre Hci Hmr Hbm Hfpok Hst Hstz Hpcs Hpcsr Hsz Hlay Hbt.
  pose proof (comp_d13 _ _ _ _ _ Hmr) as HD13.
  assert (Hop: 0 <= opos <= osz) by (destruct Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H & _); exact H).
  destruct (zlt 0 (osz - opos)) as [Hc | Hc].
  - exact (comp_pos_ok Espec DENT TABS SR BR' HD HT W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c
             v_bp v pcs st Hpr Hpre Hci Hmr Hbm Hst Hstz Hpcs Hpcsr Hsz Hlay Hbt Hc HD13).
  - exact (comp_zero_ok Espec DENT TABS SR BR' HD HT W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c
             v_bp v pcs st Hpr Hpre Hci Hmr Hbm Hst Hstz Hpcs Hpcsr Hsz Hlay Hbt ltac:(lia) HD13).
Qed.

End CM_Comp_1.
