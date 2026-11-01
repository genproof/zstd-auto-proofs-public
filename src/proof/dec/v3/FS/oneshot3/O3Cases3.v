(* FS3 one-shot: the lending of ZSTD_decompressDCtx without the selection, when an earlier frame
   switched the context to a DDict of the set (FSRep3.dict_switched); set_res lemmas *)
Require Import Zstd.proof.dec.v3.FS.FSOblig3 Zstd.proof.dec.v3.FS.oneshot3.O3Base Zstd.proof.dec.v3.FS.oneshot3.O3DCtxDef Zstd.proof.dec.v3.FS.oneshot3.O3Cases1.
Local Open Scope logic.

Section CM_O3Cases3_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma set_res_cons DD gv sh e (l: list (val * ddict_st)) cur :
  set_res DD gv sh (e :: l) cur =
  (match cur_ddict cur with
   | Some q => if Val.eq (fst e) q then emp else ddict_res DD gv sh (fst e) (snd e)
   | None => ddict_res DD gv sh (fst e) (snd e)
   end) * set_res DD gv sh l cur.
Proof. reflexivity. Qed.

(* a DDict of the set other than the current one, out of set_res *)
Lemma set_res_extract DD gv sh (l: list (val * ddict_st)) cur q dd :
  In (q, dd) l -> NoDup (map fst l) -> cur_ddict cur <> Some q ->
  exists R, set_res DD gv sh l cur = ddict_res DD gv sh q dd * R.
Proof.
  induction l as [ | e l IH]; intros Hin Hnd Hc; [contradiction | ].
  simpl in Hnd. inv Hnd. rewrite set_res_cons.
  destruct Hin as [E | Hin].
  - subst e. exists (set_res DD gv sh l cur). simpl fst; simpl snd. f_equal.
    destruct (cur_ddict cur) as [q0 | ]; [ | reflexivity].
    destruct (Val.eq q q0); [subst; congruence | reflexivity].
  - destruct (IH Hin H2 Hc) as [R HR]. rewrite HR.
    match goal with |- exists _, ?T * (?D * R) = _ => exists (T * R) end.
    apply pred_ext; cancel.
Qed.

Lemma lend_switched DENT gv p W shk shd cap dst s st k am hb hs :
  sel_on (c3_par k) (c3_sp k) = false -> dctx_pre W shk shd cap dst st k ->
  dc_set st <> nil -> dict_switched (dc_set st) (c3_dict k) ->
  dctx_lend DENT gv p W shk shd cap dst s st k am hb hs.
Proof.
  intros Hsel Hpre Hn [Hl [Hu [Hlx Hin]]].
  assert (Hcap0: 0 <= cap) by (unfold dctx_pre in Hpre; tauto).
  destruct Hpre as [Hbr [Hhs [Hdbo [Hsp [SH1 _]]]]].
  pose proof Hhs as [_ [_ Hnd]].
  pose proof Hbr as [_ [Hpar [Hset [_ [Hcur _]]]]].
  rewrite Hset in Hnd.
  assert (Hgd: getddict_res (c3_dict k) = (df_ddict (c3_dict k), c3_dict k))
    by (unfold getddict_res; rewrite Hu; reflexivity).
  apply in_map_iff in Hin. destruct Hin as [[q dd] [Eq Hin]]. simpl in Eq.
  assert (Hrel: dict_rel3 (after_use st) (snd (getddict_res (c3_dict k)))).
  { rewrite Hgd. right. destruct (after_use_parts st) as [_ [_ [E3 _]]]. rewrite E3.
    split; auto. split; auto. split; auto. split; auto. rewrite <- Eq. apply in_map_iff. exists (q, dd); auto. }
  assert (Hptr: forall p0, dd_ref dd = Some p0 -> readable_share shk /\ dict_ptr_ok W shk (Zlength (dd_bytes dd)) p0 shd cap dst).
  { intros p0 E. split; auto. rewrite Forall_forall in Hsp. specialize (Hsp _ Hin). unfold ddict_buf_ok in Hsp.
    simpl in Hsp. rewrite E in Hsp. exact Hsp. }
  assert (Hg: fst (getddict_res (c3_dict k)) = q) by (rewrite Hgd; auto).
  destruct (cur_ddict (dc_dict st)) as [q0 | ] eqn:Ecur; [destruct (Val.eq q0 q) as [E0 | E0] | ].
  - (* the context's DDict: its memory is in dict_res *)
    subst q0. destruct (dc_dict st) as [[dsrc raw once b] | ] eqn:Hdd; [ | discriminate].
    destruct dsrc as [pk | | q1 dd1]; simpl in Ecur; try discriminate. injection Ecur as Ecur. subst q1.
    assert (Edd: dd = dd1) by (apply (Hcur _ q dd1 dd Hdd); auto).
    subst dd1.
    apply (lend_ddict_gen DENT gv p W shk shd cap dst s st k am hb hs Hset Hhs q dd
             (set_res (DD3x DENT) gv shk (dc_set st) (dc_dict st))); auto.
    + rewrite Hdd. reflexivity.
    + intros E; contradiction.
    + intros E; contradiction.
  - (* another DDict of the set: its memory is in set_res *)
    assert (Hc: cur_ddict (dc_dict st) <> Some q) by (rewrite Ecur; congruence).
    destruct (set_res_extract (DD3x DENT) gv shk (dc_set st) (dc_dict st) q dd Hin Hnd Hc) as [R HR].
    apply (lend_ddict_gen DENT gv p W shk shd cap dst s st k am hb hs Hset Hhs q dd
             (dict_res (DD3x DENT) gv shk (dc_dict st) * R)); auto.
    + rewrite HR. apply pred_ext; cancel.
    + intros E; contradiction.
    + intros E; contradiction.
  - assert (Hc: cur_ddict (dc_dict st) <> Some q) by (rewrite Ecur; congruence).
    destruct (set_res_extract (DD3x DENT) gv shk (dc_set st) (dc_dict st) q dd Hin Hnd Hc) as [R HR].
    apply (lend_ddict_gen DENT gv p W shk shd cap dst s st k am hb hs Hset Hhs q dd
             (dict_res (DD3x DENT) gv shk (dc_dict st) * R)); auto.
    + rewrite HR. apply pred_ext; cancel.
    + intros E; contradiction.
    + intros E; contradiction.
Qed.

End CM_O3Cases3_1.
