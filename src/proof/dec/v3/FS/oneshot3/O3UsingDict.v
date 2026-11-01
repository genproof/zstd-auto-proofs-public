(* FS3 one-shot: ZSTD_decompress_usingDict *)
Require Import Zstd.proof.dec.v3.FS.FSOblig3 Zstd.proof.dec.v3.FS.oneshot3.O3Base.
Require Import Zstd.proof.zstd.NullBuf.
Local Open Scope logic.

Section CM_O3UsingDict_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Section Oneshot.
Variable DENT : dent_pred.
Variable TABS : tabs_pred.
Variable SR : srel3.
Variable BR : blrel.

Lemma body_usingDict3 :
  body_ok (FS3_G DENT TABS SR BR) (ZSTD_decompress_usingDict_spec (DC3x DENT TABS SR BR)).
Proof.
  exists f_ZSTD_decompress_usingDict; split; [reflexivity | split; [reflexivity | ]].
  start_function.
  unfold DC3x, DC3_of, ctx_rep3, ctx_body3. Intros k.
  match goal with H: base_rel3 _ _ |- _ => pose proof H as Hbr; destruct H as [_ [Hpar [Hset [_ [_ [Hfp _]]]]]] end.
  match goal with H: dc_set st = nil |- _ => rewrite H in Hset end.
  rewrite Hset, hset_rep_nil. Intros. match goal with H: c3_sp k = nullval |- _ => rename H into Hsp end.
  rewrite Hsp.
  (* streamStage is already zdss_init (no stream runs, dc_ss st = ss_init); MultiFrame writes it again (F10) *)
  assert (Hst0: sf_stage (c3_s k) = 0)
    by (match goal with H: dc_ss st = ss_init |- _ => pose proof Hbr as Hc; destruct Hc as [_ [_ [_ [_ [_ [_ [Hs _]]]]]]]; exact (proj1 (proj2 Hs H)) end).
  sep_apply (sgroup_take_stage d (c3_s k)).
  assert_PROP (isptr dst) as Hdst by entailer!.
  forward_call (W, gv, d, c3_fs k, c3_tabs k, c3_par k, nullval, c3_dict k, @nil (val * ddict_st), @nil val,
                shk, shd, dst, cap, shs, src, s, DA_dict shk pk b, sf_mem (c3_s k), 0).
  { rewrite msel_res_off, darg_res3_off by apply sel_on_null. simpl darg_res. sep_apply (data_at__mbuf shd cap dst). cancel. }
  { split; [simpl; split3; auto; split; auto | split; [|unfold sel_mem]; rewrite sel_on_null; discriminate]. }
  Intros vret. destruct vret as [[[[r out] fs'] d'] lxb']. simpl fst in *; simpl snd in *.
  rewrite msel_res_off, darg_res3_off by apply sel_on_null.
  sep_apply (modus_ponens_wand (field_at Ews t_dctx (DOT _streamStage) (Vint (Int.repr 0)) d)
    (sgroup d (sf_end_stage (c3_s k)))). rewrite (sf_end_stage_init _ Hst0).
  forward.
  assert (HO: oneshot_ok (dmode_of (dc_par st)) (dict_auto b) s (Zlength out) r out).
  { match goal with HO: sel_on _ _ = false \/ _ -> oneshot_ok _ _ _ _ _ _ |- _ =>
      rewrite <- Hpar; apply HO; left; apply sel_on_null end. }
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
  Exists r out (set_ex st false). unfold DC3x, DC3_of, ctx_rep3, ctx_body3. Exists (c3_with_fs k fs' (TUninit lxb')).
  simpl. rewrite Hset, Hsp, hset_rep_nil. rewrite mbuf_isptr by auto. entailer!.
  left; reflexivity.
Qed.

End Oneshot.

End CM_O3UsingDict_1.
