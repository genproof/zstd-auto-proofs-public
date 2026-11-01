(* FS3 one-shot: the lending of ZSTD_decompressDCtx WITH the selection, for each dictionary *)
Require Import Zstd.proof.dec.v3.FS.FSOblig3 Zstd.proof.dec.v3.FS.oneshot3.O3Base Zstd.proof.dec.v3.FS.oneshot3.O3DCtxDef Zstd.proof.dec.v3.FS.oneshot3.O3Cases1 Zstd.proof.dec.v3.FS.oneshot3.O3Cases4 Zstd.proof.dec.v3.FS.oneshot3.O3Cases5.
Local Open Scope logic.

Section CM_O3Cases6_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma lend_sel_all DENT gv p W shk shd cap dst s st k am hb hs :
  hs_probe_ok ->
  sel_on (c3_par k) (c3_sp k) = true -> dctx_pre W shk shd cap dst st k ->
  dctx_lend DENT gv p W shk shd cap dst s st k am hb hs.
Proof.
  intros Hprobe Hsel Hpre.
  destruct Hpre as [Hbr [Hhs [Hdbo [Hsp [SH1 _]]]]].
  pose proof Hhs as [_ [_ Hnd]].
  pose proof Hbr as [_ [Hpar [Hset [Hdr [Hcur _]]]]].
  assert (Hsp': Forall (fun e => ddict_buf_ok W shk (snd e) shd cap dst) (c3_set k)) by (rewrite Hset; exact Hsp).
  destruct Hdr as [Hdr | [Hn [Hl [Hu [Hlx Hin]]]]].
  - destruct (dc_dict st) as [[dsrc raw once b] | ] eqn:Hdd.
    2:{ (* no dictionary *)
      destruct Hdr as [Hu _].
      apply (lend_sel_null DENT gv p W shk shd cap dst s st k am hb hs Hsel Hpar Hset Hhs Hsp' SH1); auto.
      - unfold getddict_res. rewrite Hu. reflexivity.
      - rewrite Hdd. reflexivity.
      - unfold getddict_res. rewrite Hu. simpl. split; auto.
      - left. unfold after_use. rewrite Hdd. rewrite Hdd. unfold getddict_res. rewrite Hu. simpl. auto.
      - intros dr E; rewrite Hdd in E; discriminate. }
    destruct dsrc as [pk | | q dd]; simpl in Hdr.
    + (* by reference *)
      destruct (Zlength b =? 0) eqn:Hb0.
      * apply Z.eqb_eq in Hb0. apply Zlength_nil_inv in Hb0. subst b.
        destruct Hdr as [Hl [Hdk Hu]].
        apply (lend_sel_null DENT gv p W shk shd cap dst s st k am hb hs Hsel Hpar Hset Hhs Hsp' SH1); auto.
        -- unfold getddict_res. rewrite Hu. destruct once; simpl; auto.
        -- rewrite Hdd. reflexivity.
        -- unfold getddict_res. rewrite Hu. destruct once; simpl; split; auto.
        -- left. unfold after_use. rewrite Hdd. unfold getddict_res. rewrite Hu.
           destruct once; simpl; [split; [reflexivity | left; exact Hdk] | ]. rewrite Hdd. simpl. auto.
        -- intros dr E; rewrite Hdd in E; inv E; reflexivity.
      * destruct Hdr as [Hq [Hdk [Hu [ld [xam Hlx]]]]].
        set (x0 := {| dx_q := df_local (c3_dict k); dx_bytes := b; dx_ref := Some pk; dx_raw := raw; dx_ld := ld; dx_mem := xam |}).
        assert (Hgd: getddict_res (c3_dict k) =
                     (df_local (c3_dict k), if once then df_set_uses (c3_dict k) 0 else c3_dict k))
          by (unfold getddict_res; rewrite Hu, Hdk; destruct once; simpl; auto).
        apply (lend_sel_local DENT gv p W shk shd cap dst s st k am hb hs Hsel Hpar Hset Hhs Hsp' SH1 x0 pk Hprobe);
          auto; rewrite ?Hgd; simpl fst; simpl snd.
        -- reflexivity.
        -- destruct once; reflexivity.
        -- destruct once; exact Hlx.
        -- rewrite Hdd. reflexivity.
        -- rewrite Hdd. reflexivity.
        -- split; [destruct once; simpl; rewrite ?Hu; auto | right; left; destruct once; simpl; auto].
        -- unfold after_use. rewrite Hdd. destruct once; simpl; left; [split; [reflexivity | right; exact Hdk] | ].
           rewrite Hdd. simpl. rewrite Hb0. split; auto. split; auto. split; auto. exists ld, xam; auto.
    + (* the context's own copy *)
      destruct Hdr as [Ho Hdr]. subst once.
      destruct (Zlength b =? 0) eqn:Hb0.
      * apply Z.eqb_eq in Hb0. apply Zlength_nil_inv in Hb0. subst b.
        apply (lend_sel_null DENT gv p W shk shd cap dst s st k am hb hs Hsel Hpar Hset Hhs Hsp' SH1); auto; try rewrite Hdr.
        -- reflexivity.
        -- rewrite Hdd. reflexivity.
        -- simpl. split; auto.
        -- left. unfold after_use. rewrite Hdd. simpl. rewrite Hdd. simpl. auto.
        -- intros dr E; rewrite Hdd in E; inv E; reflexivity.
      * destruct Hdr as [buf [ld [xam [Hq [Hdk [Hu Hlx]]]]]].
        set (x0 := {| dx_q := df_local (c3_dict k); dx_bytes := b; dx_ref := None; dx_raw := raw; dx_ld := ld; dx_mem := xam |}).
        assert (Hgd: getddict_res (c3_dict k) = (df_local (c3_dict k), c3_dict k))
          by (unfold getddict_res; rewrite Hu, Hdk; simpl; auto).
        apply (lend_sel_local DENT gv p W shk shd cap dst s st k am hb hs Hsel Hpar Hset Hhs Hsp' SH1 x0 buf Hprobe);
          auto; rewrite ?Hgd; simpl fst; simpl snd; auto.
        -- rewrite Hdd. reflexivity.
        -- rewrite Hdd. reflexivity.
        -- intros Hc; discriminate.
        -- split; [rewrite Hu; auto | right; left; exact Hdk].
        -- unfold after_use. rewrite Hdd. simpl. left. rewrite Hdd. simpl. rewrite Hb0.
           split; auto. exists buf, ld, xam; auto.
    + (* a DDict *)
      destruct Hdr as [Hr [Ho [Hq [Hl [Hdk [Hu Eb]]]]]]. subst raw once.
      assert (Hgd: getddict_res (c3_dict k) = (q, c3_dict k))
        by (unfold getddict_res; rewrite Hu, Hdk; simpl; auto).
      apply (lend_sel_dd DENT gv p W shk shd cap dst s st k am hb hs Hsel Hpar Hset Hhs Hsp' SH1 q dd emp Hprobe);
        auto; rewrite ?Hgd; simpl fst; simpl snd; auto.
      * rewrite Hdd. simpl. rewrite (set_res_some DENT gv shk _ _ q) by reflexivity.
        rewrite <- Hset. rewrite sepcon_emp. reflexivity.
      * intros dd' Hin. rewrite Hset in Hin. apply (Hcur _ q dd dd' Hdd); auto.
      * split; [rewrite Hu; auto | right; right; right; exact Hdk].
      * intros p0 E. simpl in Hdbo. rewrite E in Hdbo. exact Hdbo.
      * unfold after_use. rewrite Hdd. simpl. left. rewrite Hdd. simpl. auto 10.
  - (* switched to a DDict of the set *)
    apply in_map_iff in Hin. destruct Hin as [[q dd] [Eq Hin]]. simpl in Eq.
    assert (Hgd: getddict_res (c3_dict k) = (df_ddict (c3_dict k), c3_dict k))
      by (unfold getddict_res; rewrite Hu; reflexivity).
    assert (Hin': In (q, dd) (c3_set k)) by (rewrite Hset; exact Hin).
    rewrite Hset in Hnd.
    destruct (res_regroup DENT gv shk (dc_set st) (dc_dict st) q dd Hnd Hin) as [R0 HR0].
    { intros dr q0 dd0 dd' E1 E2 Hin2. apply (Hcur dr q0 dd0 dd' E1 E2 Hin2). }
    apply (lend_sel_dd DENT gv p W shk shd cap dst s st k am hb hs Hsel Hpar Hset Hhs Hsp' SH1 q dd R0 Hprobe);
      auto; rewrite ?Hgd; simpl fst; simpl snd; auto.
    + rewrite HR0. rewrite <- Hset. reflexivity.
    + intros dd' Hin2. rewrite Hset in Hin2.
      clear - Hnd Hin Hin2. induction (dc_set st) as [ | e l IH]; [contradiction | ].
      simpl in Hnd. inv Hnd. destruct Hin as [E | Hin]; destruct Hin2 as [E2 | Hin2].
      * subst. inv E2. reflexivity.
      * subst e. exfalso. apply H1. apply in_map_iff. exists (q, dd'); auto.
      * subst e. exfalso. apply H1. apply in_map_iff. exists (q, dd); auto.
      * auto.
    + split; [rewrite Hu; auto | right; right; left; rewrite <- Eq; apply in_map_iff; exists (q, dd); auto].
    + intros p0 E. rewrite Forall_forall in Hsp. specialize (Hsp _ Hin). unfold ddict_buf_ok in Hsp.
      simpl in Hsp. rewrite E in Hsp. exact Hsp.
    + right. destruct (after_use_parts st) as [_ [_ [E3 _]]]. rewrite E3.
      split; auto. split; auto. split; auto. split; auto. rewrite <- Eq. apply in_map_iff. exists (q, dd); auto.
Qed.

End CM_O3Cases6_1.
