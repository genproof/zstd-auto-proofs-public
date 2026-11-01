(* FS3 one-shot: the probe's selection (FSSpecs3.psel, what ZSTD_decompressMultiFrame claims under
   refMultipleDDicts) is Spec_api6's set_sel on a clean set, given what the probe means (hs_probe_ok) and zstd's
   loads of the set's DDicts (ld_rel) *)
Require Import Zstd.proof.dec.v3.FS.FSOblig3.

Section CM_O3ModelPsel_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma psel_find_ptr (l: list (val * ddict_st)) (e: val * ddict_st) :
  NoDup (map fst l) -> In e l -> find (fun e' => veqb (fst e') (fst e)) l = Some e.
Proof.
  induction l as [|a r IH]; simpl; intros HN HI; [contradiction|].
  inversion HN as [|x y Hnin HN' Hxy]; subst.
  destruct HI as [<-|HI].
  - unfold veqb. destruct (Val.eq (fst a) (fst a)); [reflexivity|congruence].
  - unfold veqb at 1. destruct (Val.eq (fst a) (fst e)) as [E|E].
    + exfalso. apply Hnin. rewrite E. apply in_map. exact HI.
    + apply IH; assumption.
Qed.

Lemma psel_set_sel (l: list (val * ddict_st)) (tbl: list val) :
  hs_probe_ok -> hs_inv l tbl -> set_clean l = true ->
  Forall (fun e => ld_rel (dd_bytes (snd e)) (dd_ld (snd e))) l ->
  forall id, 0 <= id <= Int.max_unsigned -> psel l tbl id = set_sel l id.
Proof.
  intros Hp Hinv Hc Hld id Hid.
  unfold set_clean in Hc. apply andb_prop in Hc. destruct Hc as [_ Hc].
  rewrite forallb_forall in Hc.
  assert (Hnz: Forall (fun e => dd_id (snd e) <> 0) l).
  { rewrite Forall_forall. intros e He. specialize (Hc e He).
    apply andb_prop in Hc. destruct Hc as [Hc _]. apply negb_true_iff in Hc. apply Z.eqb_neq in Hc. exact Hc. }
  destruct (Hp l tbl id Hinv Hid) as [_ Heq]. specialize (Heq Hnz).
  destruct Hinv as (_ & _ & _ & HND & _ & Hptr & _).
  unfold psel, set_sel. rewrite Heq. unfold set_find.
  destruct (id =? 0) eqn:Hz.
  - apply Z.eqb_eq in Hz. subst id.
    destruct (find (fun e => dd_id (snd e) =? 0) l) eqn:Hf.
    + exfalso. apply find_some in Hf. destruct Hf as [Hin Hf]. apply Z.eqb_eq in Hf.
      rewrite Forall_forall in Hnz. exact (Hnz _ Hin Hf).
    + destruct (eq_dec nullval nullval); [reflexivity|congruence].
  - destruct (find (fun e => dd_id (snd e) =? id) l) as [e|] eqn:Hf.
    + apply find_some in Hf. destruct Hf as [Hin _].
      rewrite Forall_forall in Hptr. specialize (Hptr e Hin).
      destruct (eq_dec (fst e) nullval) as [E|E].
      { rewrite E in Hptr. contradiction. }
      rewrite (psel_find_ptr l e HND Hin).
      specialize (Hc e Hin). apply andb_prop in Hc. destruct Hc as [_ Hc].
      destruct (dict_auto (dd_bytes (snd e))) as [dm|] eqn:Ha; [|discriminate].
      rewrite Forall_forall in Hld.
      unfold ddx_model, dd_x; simpl.
      exact (ld_rel_auto_some _ _ _ (Hld e Hin) Ha).
    + destruct (eq_dec nullval nullval); [reflexivity|congruence].
Qed.

End CM_O3ModelPsel_1.
