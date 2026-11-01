(* FS3 set part: the body of the probing loop of ZSTD_DDictHashSet_emplaceDDict (used by SetBodyEmplace.v). *)
Require Import Zstd.proof.dec.v3.FS.set.SetDefs.
Require Import Zstd.proof.dec.v3.FS.set.SetEmplaceAux.
Local Open Scope logic.

Section CM_SetEmplaceLoop_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma emp_loop_body {Espec: OracleKind} (sp tp: val) (L l: list (val * ddict_st)) (tbl: list val) (q: val)
    (dd: ddict_st) (k n h: Z) :
  MF_ddid_wvp -> MF_ddid_range -> MF_ids_focus -> PF_member -> PF_set_id -> PF_notfull -> PF_replace ->
  6 <= k -> Zlength tbl = 2 ^ k -> Zlength l < Zlength tbl -> Zlength l + 1 < n -> n <= 2 ^ 30 -> In (q, dd) L ->
  NoDup (map fst L) -> incl l L -> ~ In q (map fst l) -> hs_inv0 l tbl -> 0 <= Zlength l -> isptr q ->
  0 <= dd_id dd <= Int.max_unsigned -> 0 <= h < n -> 0 < n ->
  emp_hide (h = hs_home (dd_id dd) n) -> emp_hide (n = Zlength tbl) ->
  semax (func_tycontext f_ZSTD_DDictHashSet_emplaceDDict Vprog G_emplace nil)
    (emp_inv sp tp L l tbl q dd n h)
    (Ssequence emp_LB Sskip)
    (loop_nocontinue_ret_assert (emp_inv sp tp L l tbl q dd n h)
       (overridePost (emp_brk sp tp L l tbl q dd n h)
          (frame_ret_assert (function_body_ret_assert tulong (emp_post sp tp L l q dd n))
             (stackframe_of f_ZSTD_DDictHashSet_emplaceDDict)))).
Proof.
  intros Mwvp Mrange Mfocus Pmember Psetid Pnotfull Preplace Hk Hn Hln H0 H1 H2 H3 H4 H5 Hinv Hl0 Hq Hid Hh Hn0 Hhd Hnd.
  unfold emp_LB, emp_inv, emp_brk, emp_post. Intros t. assert (Hs: 0 <= hs_slot h t n < n) by (apply emp_slot_range; lia).
  assert (Hv: Znth (hs_slot h t n) tbl = nullval \/ isptr (Znth (hs_slot h t n) tbl)).
  { destruct Hinv as (_ & _ & _ & _ & _ & _ & Hf & _). rewrite Forall_forall in Hf. apply Hf, Znth_In. red in Hnd; lia. }
  forward.
  emp_access (emp_ld10 tp tbl (hs_slot h t n) n Hs (eq_sym Hnd) Hv) _t'9 _idx _t'10; [auto 50 with closed |].
  destruct (eq_dec (Znth (hs_slot h t n) tbl) nullval) as [Hz|Hnz].
  - forward_if.
    + rewrite Hz. entailer!.
    + contradiction.
    + forward. Exists t. entailer!.
  - destruct (Pmember l tbl (hs_slot h t n) Hinv ltac:(red in Hnd; lia) Hnz) as [e [He Hfe]].
    destruct (Mfocus L e (H4 _ He)) as [L1 [L2 [_ HF]]].
    assert (Hsid: set_id_of l (Znth (hs_slot h t n) tbl) = dd_id (snd e)).
    { rewrite <- Hfe. apply Psetid; auto. destruct Hinv as (_ & _ & Hnd' & _); auto. }
    rewrite HF, <- Hfe. Intros.
    assert_PROP (0 <= dd_id (snd e) <= Int.max_unsigned) as Hide by (sep_apply (Mrange (fst e) (dd_id (snd e)) (ddb (snd e))); entailer!).
    forward_if.
    + assert (Hep: isptr (fst e)) by (destruct Hv as [Hv|Hv]; [contradiction | rewrite Hfe; exact Hv]).
      sep_apply (Mwvp (fst e) (dd_id (snd e)) (ddb (snd e))). apply emp_tc_null; auto.
    + forward.
      emp_access (emp_ld8 tp tbl (hs_slot h t n) n Hs (eq_sym Hnd) Hv) _t'7 _idx _t'8; [auto 50 with closed |].
      rewrite <- Hfe.
      forward_call (fst e, dd_id (snd e), ddb (snd e)).
      { rewrite if_false by auto. cancel. }
      destruct (eq_dec (fst e) nullval) as [Hen|_]; [contradiction|].
      forward_if.
      * destruct (emp_replace l tbl q dd t n h Preplace Hnd Hhd Hinv Hq H5 H Hnz ltac:(rewrite Hsid; auto))
          as [HRlen HRinv].
        match goal with |- semax _ ?P _ _ => forward_loop P break: P end.
        { entailer!. }
        { forward. entailer!. }
        forward.
        emp_access (emp_st6 tp q tbl (hs_slot h t n) n Hs (eq_sym Hnd) Hq) _t'6 _idx _ddict.
        gather_SEP (ddid _ _ _) (set_ids (L1 ++ L2)). rewrite <- HF.
        red in Hnd. subst n. forward.
        Exists (upd_Znth (hs_slot h t (Zlength tbl)) tbl q). rewrite HRlen. entailer!.
      * destruct (emp_step l tbl n h t (dd_id dd) Pnotfull Hinv Hnd Hh H H6 Hnz ltac:(rewrite Hsid; auto))
          as [Ht1 Hall1].
        forward. change (Int.signed (Int.repr 1)) with 1.
        rewrite (emp_next_idx _ n k) by (auto; red in Hnd; lia). rewrite <- emp_slot_next by lia.
        gather_SEP (ddid _ _ _) (set_ids (L1 ++ L2)). rewrite <- HF.
        Exists (t + 1). entailer!.
    + exfalso. apply Hnz. rewrite <- Hfe. exact H7.
Qed.

End CM_SetEmplaceLoop_1.
