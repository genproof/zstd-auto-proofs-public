(* FS3 streaming, case zdss_loadHeader (on the stream relation's revision R2): what the representation says about
   the context's local DDict and the set's DDicts: they are different objects (both own the DDict's pad). *)
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3Stmts.
Local Open Scope logic.

Section CM_LH3R2Sep_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma rsep_fold_in : forall (f: val * ddict_st -> mpred) l e, In e l -> fold_right sepcon emp (map f l) |-- f e * TT.
Proof.
  induction l as [ | a l IH ]; intros e H; [ contradiction | ].
  destruct H as [<- | H]; cbn [map fold_right].
  - cancel.
  - eapply derives_trans; [ apply sepcon_derives; [ apply derives_refl | apply (IH e H) ] | ]. cancel.
Qed.

Lemma rsep_DD_pad : forall DENT gv q dd, DD3x DENT gv q dd |-- ddict_pad q * TT.
Proof.
  intros. unfold DD3x, DD3_of, ddict_rep_at. cbn [dx_q dd_x]. cancel.
Qed.

Lemma rsep_local_pad : forall DENT gv q lx, q <> nullval -> local_rep DENT gv q lx |-- ddict_pad q * TT.
Proof.
  intros DENT gv q lx Hq. unfold local_rep. destruct (eq_dec q nullval); [ contradiction | ].
  destruct lx as [[x buf] | ].
  - Intros. unfold ddict_rep_at. rewrite <- H. cancel.
  - unfold ddict_any. Intros n0. cancel.
Qed.

Lemma rsep_pad_conflict : forall q, ddict_pad q * ddict_pad q |-- FF.
Proof.
  intros q. unfold ddict_pad. apply memory_block_conflict.
  - apply sepalg.nonidentity_nonunit. apply readable_nonidentity. apply writable_readable. apply writable_Ews.
  - rep_lia.
  - rep_lia.
Qed.

Lemma rsep_disj : forall DENT gv q lx l cur dd, In (q, dd) l -> q <> nullval -> cur_ddict cur = None ->
  local_rep DENT gv q lx * set_res (DD3x DENT) gv Ews l cur |-- FF.
Proof.
  intros DENT gv q lx l cur dd Hin Hq Hc.
  unfold set_res. rewrite Hc.
  eapply derives_trans.
  { apply sepcon_derives; [ apply (rsep_local_pad DENT gv q lx Hq) | apply (rsep_fold_in _ _ _ Hin) ]. }
  cbn [fst snd]. unfold ddict_res.
  eapply derives_trans.
  { apply sepcon_derives; [ apply derives_refl | apply sepcon_derives; [ apply sepcon_derives; [ eapply derives_trans; [ apply andp_left1, derives_refl | apply rsep_DD_pad ] | apply derives_refl ] | apply derives_refl ] ]. }
  apply derives_trans with (ddict_pad q * ddict_pad q * TT); [ cancel | ].
  eapply derives_trans; [ apply sepcon_derives; [ apply rsep_pad_conflict | apply derives_refl ] | ].
  rewrite FF_sepcon. apply derives_refl.
Qed.

End CM_LH3R2Sep_1.
