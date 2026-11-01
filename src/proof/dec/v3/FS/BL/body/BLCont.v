(* FS3-bl BODY: ZSTD_checkContinuity in ZSTD_decompressContinue.  Its preconditions with the witness list
   W' = [the output array; the dictionary's bytes; W] (pointer comparisons need them), and the history pointers
   afterwards: bl_lay for the frame's output begun at the call (bl_moved). *)
Require Export Zstd.proof.dec.v3.FS.BL.body.BLCase.
Require Import Zstd.proof.dec.v3.FS.BL.body.cont.ContSep.
Local Open Scope logic.

Section CM_BLCont_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma bl_cont_ok W md od osz0 ba fs hb v shk shd ob osz opos oc shs src c :
  bl_pre_ok W od osz0 ba shk shd ob osz opos oc shs src c -> bl_cinv md od osz0 ba fs hb v ->
  field_compatible (tarray tuchar osz) nil ob ->
  match od with
  | None => True
  | Some d => isptr (bd_eb d) -> field_compatible (tarray tuchar (Zlength (bd_b d))) nil (bd_eb d)
  end ->
  (fs_gpDictCopy fs = Vint (Int.repr 0) \/ fs_gpDictCopy fs = Vint (Int.repr 1)) /\
  (0 < osz - opos -> fs_gpDictCopy fs = Vint (Int.repr 0) ->
     (pws_pred (pw_bytes shd osz oc ob :: bd_pw shk od :: W)
        |-- denote_tc_test_eq (offset_val opos ob) (fs_previousDstEnd fs))) /\
  (cont_moves fs (offset_val opos ob) (osz - opos) = true ->
     isptr (offset_val opos ob) /\
     (pws_pred (pw_bytes shd osz oc ob :: bd_pw shk od :: W) |-- denote_tc_test_eq (fs_previousDstEnd fs) nullval) /\
     (fs_previousDstEnd fs <> nullval -> sameblock (fs_previousDstEnd fs) (fs_prefixStart fs) = true)) /\
  bl_lay od osz (bl_moved ba ob opos) (continuity fs (offset_val opos ob) (osz - opos)).
Proof.
  intros Hpre Hci Fob Fod.
  apply (bc_all W md od osz0 ba fs hb v shk shd ob osz opos oc shs src c Hpre Hci Fob Fod).
  intros d Ed. subst od. destruct Hci as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hwf & _).
  intros Hd Heb. destruct Hwf as [(_ & _ & _ & _ & _ & _ & _ & D12) | (Hn & _)]; [exact (D12 Hd) |].
  rewrite Hn in Heb. contradiction.
Qed.

End CM_BLCont_1.
