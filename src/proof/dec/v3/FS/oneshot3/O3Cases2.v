(* FS3 one-shot: the lending of ZSTD_decompressDCtx without the selection, for each of Spec_api6's
   dictionaries (FSRep3.dict_rel3_of) *)
Require Import Zstd.proof.dec.v3.FS.FSOblig3 Zstd.proof.dec.v3.FS.oneshot3.O3Base Zstd.proof.dec.v3.FS.oneshot3.O3DCtxDef Zstd.proof.dec.v3.FS.oneshot3.O3Cases1.
Require Import Zstd.proof.zstd.Spec_codes_facts.
Local Open Scope logic.

Section CM_O3Cases2_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma lend_rel DENT gv p W shk shd cap dst s st k am hb hs :
  sel_on (c3_par k) (c3_sp k) = false -> dctx_pre W shk shd cap dst st k ->
  dict_rel3_of (dc_dict st) (c3_dict k) ->
  dctx_lend DENT gv p W shk shd cap dst s st k am hb hs.
Proof.
  intros Hsel Hpre Hdr.
  assert (Hcap0: 0 <= cap) by (unfold dctx_pre in Hpre; tauto).
  destruct Hpre as [Hbr [Hhs [Hdbo [_ [SH1 _]]]]].
  pose proof Hbr as [_ [Hpar [Hset _]]].
  destruct (dc_dict st) as [[dsrc raw once b] | ] eqn:Hdd.
  2:{ (* no dictionary *)
    destruct Hdr as [Hu _].
    apply lend_null; auto.
    - unfold getddict_res. rewrite Hu. reflexivity.
    - left. unfold after_use. rewrite Hdd. rewrite Hdd. unfold getddict_res. rewrite Hu. simpl. auto.
    - intros _ md r out H. rewrite Hdd. exact H.
    - intros _ md r H. rewrite Hdd. exact H. }
  destruct dsrc as [pk | | q dd]; simpl in Hdr.
  - (* by reference *)
    destruct (Zlength b =? 0) eqn:Hb0.
    + apply Z.eqb_eq in Hb0. apply Zlength_nil_inv in Hb0. subst b.
      destruct Hdr as [Hl [Hdk Hu]].
      apply lend_null; auto.
      * unfold getddict_res. rewrite Hu. destruct once; simpl; auto.
      * left. unfold after_use. rewrite Hdd. unfold getddict_res. rewrite Hu.
        destruct once; simpl; [split; [reflexivity | left; exact Hdk] | ]. rewrite Hdd. simpl. auto.
      * intros _ md r out H. rewrite Hdd. simpl. destruct raw; exact H.
      * intros _ md r H. rewrite Hdd. simpl. destruct raw; exact H.
    + destruct Hdr as [Hq [Hdk [Hu [ld [xam Hlx]]]]].
      set (x0 := {| dx_q := df_local (c3_dict k); dx_bytes := b; dx_ref := Some pk; dx_raw := raw; dx_ld := ld; dx_mem := xam |}).
      assert (Hgd: getddict_res (c3_dict k) =
                   (df_local (c3_dict k), if once then df_set_uses (c3_dict k) 0 else c3_dict k))
        by (unfold getddict_res; rewrite Hu, Hdk; destruct once; simpl; auto).
      apply (lend_local DENT gv p W shk shd cap dst s st k am hb hs Hset Hhs x0 pk); auto; rewrite ?Hgd; simpl fst; simpl snd.
      * reflexivity.
      * destruct once; reflexivity.
      * destruct once; exact Hlx.
      * rewrite Hdd. reflexivity.
      * unfold after_use. rewrite Hdd. destruct once; simpl; left; [split; [reflexivity | right; exact Hdk] | ].
        rewrite Hdd. simpl. rewrite Hb0. split; auto. split; auto. split; auto. exists ld, xam; auto.
      * intros _ md r out Hld H. rewrite Hdd. simpl. unfold ddx_model in H. simpl in H.
        destruct raw; [exact H | apply (oneshot_ok_c3 _ _ ld); auto].
      * intros _ md r Hld H. rewrite Hdd. simpl. unfold ddx_model in H. simpl in H.
        destruct raw; [exact H | apply (oneshot_codes_c3 _ _ ld); auto].
  - (* the context's own copy *)
    destruct Hdr as [Ho Hdr]. subst once.
    destruct (Zlength b =? 0) eqn:Hb0.
    + apply Z.eqb_eq in Hb0. apply Zlength_nil_inv in Hb0. subst b.
      apply lend_null; auto; try rewrite Hdr.
      * reflexivity.
      * left. unfold after_use. rewrite Hdd. simpl. rewrite Hdd. simpl. auto.
      * intros _ md r out H. rewrite Hdd. simpl. destruct raw; exact H.
      * intros _ md r H. rewrite Hdd. simpl. destruct raw; exact H.
    + destruct Hdr as [buf [ld [xam [Hq [Hdk [Hu Hlx]]]]]].
      set (x0 := {| dx_q := df_local (c3_dict k); dx_bytes := b; dx_ref := None; dx_raw := raw; dx_ld := ld; dx_mem := xam |}).
      assert (Hgd: getddict_res (c3_dict k) = (df_local (c3_dict k), c3_dict k))
        by (unfold getddict_res; rewrite Hu, Hdk; simpl; auto).
      apply (lend_local DENT gv p W shk shd cap dst s st k am hb hs Hset Hhs x0 buf); auto; rewrite ?Hgd; simpl fst; simpl snd; auto.
      * rewrite Hdd. reflexivity.
      * intros Hc; discriminate.
      * unfold after_use. rewrite Hdd. simpl. left. rewrite Hdd. simpl. rewrite Hb0.
        split; auto. exists buf, ld, xam; auto.
      * intros _ md r out Hld H. rewrite Hdd. simpl. unfold ddx_model in H. simpl in H.
        destruct raw; [exact H | apply (oneshot_ok_c3 _ _ ld); auto].
      * intros _ md r Hld H. rewrite Hdd. simpl. unfold ddx_model in H. simpl in H.
        destruct raw; [exact H | apply (oneshot_codes_c3 _ _ ld); auto].
  - (* a DDict *)
    destruct Hdr as [Hr [Ho [Hq [Hl [Hdk [Hu Eb]]]]]]. subst raw once.
    assert (Hgd: getddict_res (c3_dict k) = (q, c3_dict k))
      by (unfold getddict_res; rewrite Hu, Hdk; simpl; auto).
    apply (lend_ddict_gen DENT gv p W shk shd cap dst s st k am hb hs Hset Hhs q dd
             (set_res (DD3x DENT) gv shk (dc_set st) (dc_dict st))); auto; rewrite ?Hgd; simpl fst; simpl snd; auto.
    + rewrite Hdd. reflexivity.
    + intros p0 E. split; [auto | ]. simpl in Hdbo. rewrite E in Hdbo. exact Hdbo.
    + unfold after_use. rewrite Hdd. simpl. left. rewrite Hdd. simpl. auto 10.
    + intros _ md r out H. rewrite Hdd. simpl. subst b. exact H.
    + intros _ md r H. rewrite Hdd. simpl. subst b. exact H.
Qed.

End CM_O3Cases2_1.
