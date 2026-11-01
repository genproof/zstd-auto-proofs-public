(* FS3 streaming, case zdss_loadHeader (on the stream relation's revision R2): why each error return of case 1
   is allowed (S3Main.err_why): the header, the window, memory. *)
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3Stmts.
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3R2Lib Zstd.proof.dec.v3.FS.stream.lh.LH3RetGfh.
Require Zstd.proof.dec.FS.StreamModelFacts.
Local Open Scope logic.

Section CM_LH3R2Why_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma rl_mg : forall st k, base_call st k -> sm_mg (sm_of st) = lh_mg k.
Proof. intros st k (_ & Hp & _). unfold sm_mg, sm_of, lh_mg. cbn. rewrite Hp. reflexivity. Qed.

Lemma rl_wmax : forall st, par_ok (dc_par st) -> dp_wmax (dc_par st) <= no_wlim.
Proof. intros st (_ & _ & _ & Hw & _). unfold no_wlim. lia. Qed.

Lemma rl_entry : forall a w hb, lh_ctx a w hb ->
  base_call (a_st a) (w_k w) /\ bytes_ok hb /\ hdr_lenok (lh_mg (w_k w)) hb /\ dsa_ok a.
Proof.
  intros a w hb (Ha & _ & _ & _ & _ & He & _). unfold lh_entry in He. tauto.
Qed.

Lemma dec_err_code : forall e, 0 < e < 120 -> e <> ZSTD_error_noForwardProgress_destFull ->
  e <> ZSTD_error_noForwardProgress_inputEmpty -> dec_err (err_code e).
Proof.
  intros e H1 H2 H3. unfold dec_err, err_code, is_error_code.
  split; [ apply Z.ltb_lt; lia | ]. split; intro E; [ apply H2 | apply H3 ]; lia.
Qed.

Lemma why_mem : forall a, err_why a (err_code ZSTD_error_memory_allocation).
Proof.
  intros a. split.
  - apply dec_err_code; unfold ZSTD_error_memory_allocation, ZSTD_error_noForwardProgress_destFull,
      ZSTD_error_noForwardProgress_inputEmpty; lia.
  - left. reflexivity.
Qed.

Lemma why_fails : forall a r, dec_err r -> lh_fails a -> err_why a r.
Proof. intros a r H1 H2. split; [ exact H1 | right; left; exact H2 ]. Qed.

Lemma prefix_nil : forall l, is_prefix nil l.
Proof. intros. reflexivity. Qed.

Lemma why_hdr : MF3 -> forall a w hb r, lh_ctx a w hb -> par_ok (dc_par (a_st a)) ->
  get_frame_header_m (lh_mg (w_k w)) hb = FH_err -> dec_err r -> err_why a r.
Proof.
  intros HMF a w hb r Hc Hp Hh Hd. apply why_fails; auto.
  destruct (rl_entry a w hb Hc) as (Hb & Hbh & Hok & _).
  destruct (rl_split a w hb Hc (rl_wmax _ Hp)) as [F | (dsin & recs & cd & Hsp)]; [ exact F | ].
  apply (rl_fails_fbad HMF a w hb dsin recs cd nil Hsp (prefix_nil _)).
  rewrite app_nil_r. apply (mf_hdr_err_bad HMF); auto.
  - unfold hdr_lenok in Hok. rewrite Hh in Hok. exact Hok.
  - rewrite (rl_mg _ _ Hb). exact Hh.
Qed.

Lemma gfhm_nil : forall mg, get_frame_header_m mg nil <> FH_err.
Proof. intros [|]; vm_compute; discriminate. Qed.

Lemma why_more : MF3 -> forall a w hb r, lh_ctx a w hb -> par_ok (dc_par (a_st a)) ->
  get_frame_header_m (lh_mg (w_k w)) (hb ++ sublist (w_ipc w) (a_isz a) (a_ibs a)) = FH_err -> dec_err r ->
  err_why a r.
Proof.
  intros HMF a w hb r Hc Hp Hh Hd. apply why_fails; auto.
  destruct (rl_entry a w hb Hc) as (Hb & Hbh & Hok & Ha).
  assert (Hi: a_ipos a <= w_ipc w <= a_isz a) by (destruct Hc as (_ & _ & _ & _ & _ & He & _); unfold lh_entry in He; tauto).
  assert (Hib: bytes_ok (a_ibs a)) by (unfold dsa_ok in Ha; tauto).
  destruct (rl_split a w hb Hc (rl_wmax _ Hp)) as [F | (dsin & recs & cd & Hsp)]; [ exact F | ].
  apply (rl_fails_fbad HMF a w hb dsin recs cd (sublist (w_ipc w) (a_isz a) (a_ibs a)) Hsp).
  { apply firstn_all. }
  apply (mf_hdr_err_bad HMF); auto.
  - unfold bytes_ok in *. apply Forall_app; split; auto. apply Forall_sublist; auto.
  - intro E. rewrite E in Hh. apply (gfhm_nil _ Hh).
  - rewrite (rl_mg _ _ Hb). exact Hh.
Qed.

Lemma why_window : MF3 -> forall a w hb h, lh_ctx a w hb -> par_ok (dc_par (a_st a)) ->
  get_frame_header_m (lh_mg (w_k w)) hb = FH_ok h ->
  Z.max (fh_windowSize h) ZSTD_WINDOWSIZE_ABSMIN > dp_wmax (dc_par (a_st a)) ->
  err_why a (err_code ZSTD_error_frameParameter_windowTooLarge).
Proof.
  intros HMF a w hb h Hc Hp Hh Hwin.
  assert (Hdec: dec_err (err_code ZSTD_error_frameParameter_windowTooLarge)).
  { apply dec_err_code; unfold ZSTD_error_frameParameter_windowTooLarge, ZSTD_error_noForwardProgress_destFull,
      ZSTD_error_noForwardProgress_inputEmpty; lia. }
  apply why_fails; auto.
  destruct (rl_entry a w hb Hc) as (Hb & Hbh & Hok & _).
  assert (Hw0: 2 ^ 10 <= dp_wmax (dc_par (a_st a))) by (destruct Hp as (_ & _ & _ & ? & _); lia).
  destruct (rl_gfh3 _ _ _ Hh Hbh) as (_ & _ & _ & _ & _ & _ & Hft & _ & Hsk & _).
  assert (Ht0: fh_frameType h = 0).
  { destruct Hft as [Hft | Hft]; auto. destruct (Hsk Hft) as (_ & Hw & _). rewrite Hw in Hwin.
    unfold ZSTD_WINDOWSIZE_ABSMIN in Hwin. lia. }
  destruct (rl_split a w hb Hc (rl_wmax _ Hp)) as [F | (dsin & recs & cd & Hsp)]; [ exact F | ].
  apply (rl_fails_fbad HMF a w hb dsin recs cd nil Hsp (prefix_nil _)).
  rewrite app_nil_r.
  rewrite <- (rl_mg _ _ Hb) in Hh, Hok.
  assert (Hsz: Zlength hb = fh_headerSize h) by (unfold hdr_lenok in Hok; rewrite Hh in Hok; auto).
  destruct (mf_hdr_zstd HMF (sm_of (a_st a)) cd hb h Hbh Hh Ht0 Hsz) as (_ & _ & Hbad & _).
  apply Hbad; cbn [sm_of sm_wl]; unfold ZSTD_WINDOWSIZE_ABSMIN in *; lia.
Qed.

End CM_LH3R2Why_1.
