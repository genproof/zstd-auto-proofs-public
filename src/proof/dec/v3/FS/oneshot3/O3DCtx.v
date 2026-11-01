(* FS3 one-shot: ZSTD_decompressDCtx, the cases assembled.  The open premises of dctx_cases_of:
   none (hs_probe_ok is SetProbe's). *)
Require Import Zstd.proof.dec.v3.FS.FSOblig3 Zstd.proof.dec.v3.FS.oneshot3.O3Base Zstd.proof.dec.v3.FS.oneshot3.O3DCtxDef Zstd.proof.dec.v3.FS.oneshot3.O3Cases1 Zstd.proof.dec.v3.FS.oneshot3.O3Cases2 Zstd.proof.dec.v3.FS.oneshot3.O3Cases3 Zstd.proof.dec.v3.FS.oneshot3.O3Cases6 Zstd.proof.dec.v3.FS.set.SetProbe.
Local Open Scope logic.

Section CM_O3DCtx_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma dict_rel_uses3 od d : dict_rel3_of od d -> df_uses d = -1 \/ df_uses d = 0 \/ df_uses d = 1.
Proof.
  unfold dict_rel3_of. destruct od as [dr | ]; [ | intros [H _]; rewrite H; auto].
  destruct (dr_src dr); intros H.
  - destruct (Zlength (dr_bytes dr) =? 0).
    + destruct H as [_ [_ H]]; rewrite H; destruct (dr_once dr); auto.
    + destruct H as [_ [_ [H _]]]; rewrite H; destruct (dr_once dr); auto.
  - destruct H as [_ H]. destruct (Zlength (dr_bytes dr) =? 0).
    + subst d; simpl; auto.
    + destruct H as [? [? [? [_ [_ [H _]]]]]]; rewrite H; auto.
  - destruct H as [_ [_ [_ [_ [_ [H _]]]]]]; rewrite H; auto.
Qed.

Lemma dict_rel_ddict3 od d : dict_rel3_of od d -> df_uses d <> 0 -> is_pointer_or_null (df_ddict d).
Proof.
  unfold dict_rel3_of. destruct od as [dr | ]; [ | intros [H _]; rewrite H; congruence].
  destruct (dr_src dr) as [pk | | q dd]; intros H Hu.
  - destruct (Zlength (dr_bytes dr) =? 0).
    + destruct H as [_ [H _]]; rewrite H; simpl; auto.
    + destruct H as [Hp [H _]]; rewrite H; destruct (df_local d); simpl in *; tauto.
  - destruct H as [_ H]. destruct (Zlength (dr_bytes dr) =? 0).
    + subst d; simpl; auto.
    + destruct H as [? [? [? [Hp [H _]]]]]; rewrite H; destruct (df_local d); simpl in *; tauto.
  - destruct H as [_ [_ [Hp [_ [H _]]]]]; rewrite H; destruct q; simpl in *; tauto.
Qed.

Lemma getddict_pre_ok W shk shd cap dst st k : dctx_pre W shk shd cap dst st k -> getddict_pre (c3_dict k).
Proof.
  intros [Hbr [[_ [Hp _]] _]]. destruct Hbr as [_ [_ [Hset [Hd _]]]].
  destruct Hd as [Hd | [Hn [Hl [Hu [Hlx Hin]]]]].
  - split; [apply (dict_rel_uses3 _ _ Hd) | apply (dict_rel_ddict3 _ _ Hd)].
  - split; [auto | intros _].
    rewrite <- Hset in Hin. apply in_map_iff in Hin. destruct Hin as [e [E Hin]].
    rewrite Forall_forall in Hp. specialize (Hp e Hin). rewrite E in Hp.
    destruct (df_ddict (c3_dict k)); simpl in *; tauto.
Qed.

(* the cases, given the open premises *)
Lemma dctx_cases_of DENT :
  dctx_cases_ok DENT.
Proof.
  intros gv p W shk shd cap dst s st k am hb hs Hpre.
  pose proof (proj1 set_probe_ok) as Hprobe.
  split; [apply (getddict_pre_ok W shk shd cap dst st k Hpre) | ].
  destruct (sel_on (c3_par k) (c3_sp k)) eqn:Es; [apply lend_sel_all; auto | ].
  pose proof Hpre as [[_ [_ [_ [Hd _]]]] _].
  destruct Hd as [Hd | [Hn Hsw]].
  - apply lend_rel; auto.
  - apply lend_switched; eauto.
Qed.

End CM_O3DCtx_1.
