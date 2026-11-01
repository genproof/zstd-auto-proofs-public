(* FS3-bl BODY, stages 3/4, raw block: the pure facts of the raw case. *)
Require Export Zstd.proof.dec.v3.FS.BL.body.s34.raw.RawHelp.
Local Open Scope logic.

Section CM_RawFacts_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma raw_fs1 fs ob osz opos pcs n :
  fs_expected (bl_fs1 fs ob osz opos pcs n) = fs_expected fs /\
  fs_ddictIsCold (bl_fs1 fs ob osz opos pcs n) = fs_ddictIsCold fs.
Proof. unfold bl_fs1, continuity. destruct (cont_moves _ _ _); split; reflexivity. Qed.

Lemma raw_cold_same fs x : fsu_ddictIsCold (fsu_expected fs x) (fs_ddictIsCold fs) = fsu_expected fs x.
Proof. destruct fs; reflexivity. Qed.

Lemma raw_cold01 fs ob osz opos pcs n : cold01 fs -> cold01 (bl_fs1 fs ob osz opos pcs n).
Proof. unfold cold01. rewrite (proj2 (raw_fs1 fs ob osz opos pcs n)). auto. Qed.

Lemma raw_tooSmall_err : is_error_code (err_code ZSTD_error_dstSize_tooSmall) = true.
Proof. reflexivity. Qed.

Lemma raw_small_noerr n : 0 <= n <= 2 ^ 30 -> is_error_code n = false.
Proof. intros. unfold is_error_code. apply Z.ltb_ge. lia. Qed.

(* the error return: the model's step at a raw block is the whole content c (or an error) *)
Lemma raw_claim_err md ba ba' fs ts v c r opos osz oc' :
  bl_mrel md ba fs ts v -> (bv_stage v = BBlk \/ bv_stage v = BLastBlk) -> bv_bt v = 0 ->
  is_error_code r = true -> osz - opos < Zlength c ->
  bl_claim_nc md ba ba' c r opos osz oc'.
Proof.
  intros Hmr Hst Hbt Er Hc. unfold bl_claim_nc.
  destruct (ba_st ba) as [b |] eqn:B; auto. destruct (dictref_model _) as [dm |]; auto. intros _.
  destruct (Hmr b B) as (Hs & _ & _ & _ & _ & Hx).
  assert (Hbt': bs_btype b = 0).
  { destruct Hst as [E | E]; rewrite E in Hx; destruct Hx as (_ & Hb & _); lia. }
  unfold bl_step_nc. rewrite Hs.
  destruct Hst as [E | E]; rewrite E; unfold bl_step; rewrite Hs, E; rewrite Hbt'; cbn [Z.eqb];
    unfold bl_block_done; rewrite Hs, E.
  - destruct (_ >? _); [exact Er |]. split; [intros X; congruence | intros _; exact Hc].
  - destruct (_ >? _); [exact Er |].
    destruct (andb _ _); [exact Er |]. destruct (bl_frame_end _).
    split; [intros X; congruence | intros _; exact Hc].
Qed.

(* the success: s34_mid's facts *)
Lemma raw_mid_ok md od ba fs ts v osz opos oc c :
  bl_mrel md ba fs ts v -> (bv_stage v = BBlk \/ bv_stage v = BLastBlk) -> bv_bt v = 0 -> cold01 fs ->
  Zlength c <= osz - opos -> Zlength c <= 2 ^ 30 -> bytes_ok c -> Zlength oc = osz -> 0 <= opos ->
  s34_mid_ok od ba v osz opos oc c (Zlength c) (put_bytes oc opos c) (ba_expect ba - Zlength c)
    (fs_ddictIsCold fs) (TInit (bd_oxo od) ts).
Proof.
  intros Hmr Hst Hbt Hcold Hc Hc30 Hb Hoc Hop. pose proof (Zlength_nonneg c).
  assert (Hz: Zlength (zbytes c) = Zlength c) by apply Zlength_map.
  unfold s34_mid_ok. split; [rep_lia |]. split.
  { unfold put_bytes. rewrite !Zlength_app, Hz, !Zlength_sublist by lia. lia. }
  split. { unfold put_bytes. list_solve. }
  split. { exact Hcold. }
  split. { intros E. rewrite raw_small_noerr in E by lia. discriminate. }
  intros _. split; [lia |]. split; [rewrite Hbt; reflexivity |]. split; [auto |].
  exists c, ts. split. { unfold put_bytes. list_solve. }
  split; [exact Hb |]. split; [reflexivity |]. split; [reflexivity |].
  intros b dm x (B & _ & _) Hm.
  destruct (Hmr b B) as (_ & _ & Hds & _ & _ & Hx).
  assert (Hbt': bs_btype b = 0).
  { destruct Hst as [E | E]; rewrite E in Hx; destruct Hx as (_ & Hb' & _); lia. }
  unfold blk_model in Hm. rewrite Hbt' in Hm. cbn in Hm. rewrite Hds in Hm. congruence.
Qed.

(* the frame group with expected stored *)
Lemma raw_join p fs pr e :
  par_ok pr ->
  field_at Ews t_dctx (DOT _stage) (fs_stage fs) p * field_at Ews t_dctx (DOT _bType) (fs_bType fs) p *
  field_at Ews t_dctx (DOT _expected) (Vlong (Int64.repr e)) p * fc_rest p fs pr
  |-- fcore3 p (fsu_ddictIsCold (fsu_expected fs (vlong e)) (fs_ddictIsCold fs)) pr nullval.
Proof. intros H. rewrite raw_cold_same. exact (fcore3_join p (fsu_expected fs (vlong e)) pr H). Qed.

End CM_RawFacts_1.
