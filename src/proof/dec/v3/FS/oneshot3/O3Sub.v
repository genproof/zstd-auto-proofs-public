(* FS3 one-shot: the internal specifications of ZSTD_decompress_usingDDict and ZSTD_freeDDict imply the API ones *)
Require Import Zstd.proof.dec.v3.FS.FSOblig3 Zstd.proof.dec.v3.FS.oneshot3.O3Base Zstd.proof.dec.v3.FS.oneshot3.O3Valid.
Require Import Zstd.proof.zstd.NullBuf.
Local Open Scope logic.

Section CM_O3Sub_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma usingDDict_sub3 DENT TABS SR BR : DENT_OK DENT -> TABS_OK TABS ->
  funspec_sub (snd (ZSTD_decompress_usingDDict_int_spec3 DENT TABS))
              (snd (ZSTD_decompress_usingDDict_spec (DC3x DENT TABS SR BR) (DD3x DENT))).
Proof.
  intros HD HT.
  apply NDsubsume_subsume; [split; reflexivity|].
  split; [split; reflexivity|].
  intros [[[[[[[[[[[[W gv] d] st] shd] dst] cap] shs] src] s] shk] q] dd] [g args]. simpl.
  unfold PROPx, LOCALx, SEPx, PARAMSx, GLOBALSx; simpl. normalize.
  unfold DC3x, DC3_of, ctx_rep3, ctx_body3, ddict_res, DD3x.
  rewrite <- DD3_valid. unfold DD3_of.
  unfold LOCALx at 1, argsassert2assert at 1; simpl.
  Intros k.
  match goal with H: ddict_buf_ok _ _ _ _ _ _ |- _ => rename H into Hbo end.
  match goal with H: dc_set st = [] |- _ => rename H into Hsetnil end.
  match goal with H: base_rel3 st k |- _ => rename H into Hbr end.
  pose proof Hbr as Hbr0. destruct Hbr0 as [_ [Hpar [Hset [_ [_ [Hfp _]]]]]].
  rewrite Hsetnil in Hset. rewrite Hset, hset_rep_nil. Intros.
  match goal with H: c3_sp k = nullval |- _ => rename H into Hsp end. rewrite Hsp.
  set (x := dd_x q dd). set (buf := dd_buf dd).
  assert_PROP (match dx_ref x with Some p => buf = p | None => True end) as Hbuf.
  { unfold ddict_rep_at, ddict_struct. entailer!. }
  assert_PROP (ld_rel (dx_bytes x) (dx_ld x)) as Hld.
  { unfold ddict_rep_at, ddict_struct. entailer!. }
  assert (Hxb: dx_bytes x = dd_bytes dd) by reflexivity.
  (* the caller's bytes of a DDict by reference are at a pointer *)
  assert_PROP (match dd_ref dd with Some p => isptr p | None => True end) as Hrp.
  { apply andp_left2. destruct (dd_ref dd); entailer!. }
  assert (Hok: darg_ok3 W (DA_ddict x buf shk) shd cap dst).
  { apply dd_darg_ok3; auto. intros p0 E. unfold ddict_buf_ok in Hbo. rewrite E in Hbo. auto. }
  pose proof (dd_darg_bytes shk q dd Hrp Hbuf) as Hm. fold x buf in Hm.
  rewrite Hm.
  assert_PROP (isptr dst) as Hdst by (apply andp_left2; entailer!).
  (* streamStage is already zdss_init (dc_ss st = ss_init); MultiFrame writes it again (F10) *)
  assert (Hst0: sf_stage (c3_s k) = 0).
  { match goal with E: dc_ss st = ss_init |- _ =>
      pose proof Hbr as Hc; destruct Hc as [_ [_ [_ [_ [_ [_ [Hs _]]]]]]]; exact (proj1 (proj2 Hs E)) end. }
  Exists (W, gv, d, c3_fs k, c3_tabs k, c3_par k, nullval, c3_dict k, @nil (val * ddict_st), @nil val,
          shk, shd, dst, cap, shs, src, s, DA_ddict x buf shk, sf_mem (c3_s k), 0)
    (mem_mgr gv * dctx_token d * dctx_pad d * cgroup3 d (c3_stable k) (dp_wmax (c3_par k)) *
     dgroup DENT gv d (c3_dict k) *
     (field_at Ews t_dctx (DOT _streamStage) (Vint (Int.repr 0)) d -* sgroup d (sf_end_stage (c3_s k)))).
  simpl. rewrite msel_res_off, darg_res3_off by apply sel_on_null.
  apply andp_right.
  { unfold LOCALx, argsassert2assert; simpl. entailer!.
    2: { unfold local, lift1; simpl. normalize. sep_apply (sgroup_take_stage d (c3_s k)). sep_apply (data_at__mbuf shd cap dst). cancel. }
    1: split; [| unfold sel_mem]; rewrite sel_on_null; discriminate. }
  apply prop_right. intros rho'.
  normalize.
  rename x0 into r, x1 into out, x2 into fs', x3 into d', x4 into lxb'.
  rewrite msel_res_off by apply sel_on_null.
  match goal with HO: sel_on _ _ = false \/ _ -> oneshot_ok _ _ _ _ _ _ |- _ =>
    specialize (HO (or_introl (sel_on_null _))); unfold ddx_model in HO;
    replace (dx_raw x) with false in HO by reflexivity;
    apply oneshot_ok_c3 in HO; [ | exact Hld]; rewrite Hxb, Hpar in HO end.
  assert (Hb': base_rel3 st (c3_with_fs k fs' (TUninit lxb')))
    by (apply base_rel3_with_fs; auto; match goal with H: fp_ok _ -> fp_ok (fs_fParams fs') |- _ => exact (H Hfp) end).
  assert (Hsr: dc_ss st <> ss_init -> ss_err (dc_ss st) = false -> SR gv st (c3_with_fs k fs' (TUninit lxb')))
    by (intros E; contradiction).
  assert (Hbl: forall ba, dc_bl st = Some ba ->
            BR (c3_par (c3_with_fs k fs' (TUninit lxb'))) ba (c3_fs (c3_with_fs k fs' (TUninit lxb'))) (c3_tabs (c3_with_fs k fs' (TUninit lxb'))) (sf_hbuf (c3_s (c3_with_fs k fs' (TUninit lxb')))))
    by (intros ba E; congruence).
  (* the decoding clears dc_ex (after_decode), which the representation does not see *)
  assert (Hb'x: base_rel3 (set_ex st false) (c3_with_fs k fs' (TUninit lxb'))) by exact Hb'.
  assert (Hsrx: dc_ss (set_ex st false) <> ss_init -> ss_err (dc_ss (set_ex st false)) = false ->
                SR gv (set_ex st false) (c3_with_fs k fs' (TUninit lxb')))
    by (intros E; exfalso; apply E; assumption).
  assert (Hblx: forall ba, dc_bl (set_ex st false) = Some ba ->
            BR (c3_par (c3_with_fs k fs' (TUninit lxb'))) ba (c3_fs (c3_with_fs k fs' (TUninit lxb'))) (c3_tabs (c3_with_fs k fs' (TUninit lxb'))) (sf_hbuf (c3_s (c3_with_fs k fs' (TUninit lxb')))))
    by exact Hbl.
  assert (Hexx: ex_on3 SR (set_ex st false) (c3_with_fs k fs' (TUninit lxb'))) by (apply ex_on3_noex; reflexivity).
  assert (Ha: after_decode st (set_ex st false) (Some (ddict_ref q dd))) by (left; reflexivity).
  Exists r out (set_ex st false) (c3_with_fs k fs' (TUninit lxb')).
  simpl. rewrite Hset, Hsp, hset_rep_nil. simpl darg_res. entailer!.
  unfold local, lift1; simpl. Intros. rewrite prop_true_andp by auto.
  sep_apply (modus_ponens_wand (field_at Ews t_dctx (DOT _streamStage) (Vint (Int.repr 0)) d)
    (sgroup d (sf_end_stage (c3_s k)))). rewrite (sf_end_stage_init _ Hst0).
  rewrite mbuf_isptr by auto. cancel.
Qed.

End CM_O3Sub_1.
