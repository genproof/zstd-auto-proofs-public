(* FS3 streaming: the epilogue's pure obligations from the loop invariant at someMoreWork = 0; port of
   v2 src/proof/dec/FS/StreamEpiPure.v. *)
Require Import Zstd.proof.dec.v3.FS.stream.S3Main Zstd.proof.dec.v3.FS.stream.epi.E3Defs Zstd.proof.dec.v3.FS.stream.epi.E3Rem.
Require Import Zstd.proof.dec.v3.FS.stream.epi.E3Content Zstd.proof.dec.v3.FS.stream.epi.E3Zero Zstd.proof.dec.v3.FS.stream.epi.E3Hint Zstd.proof.dec.v3.FS.stream.epi.E3Fields.
Require Import Zstd.proof.model.StreamProgress Zstd.proof.dec.v3.FS.stream.epi.E3Prog Zstd.proof.dec.v3.FS.stream.epi.E3X.

Section CM_E3Pure_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* stream_claims_m for a non-error return r, from the model relation on the bytes read *)
Lemma epi_claims : forall (sm: smode) (sin0 sout0 sin sall sout: list Z) (fp: fprog) (pend: list Z) (a1 r: Z)
    (ocap: option Z),
  bytes_ok sin -> dead sm sin \/ (exists cd, m_rel_cd sm sin sout fp pend cd) ->
  is_error_code r = false ->
  (r = 0 -> pend = nil /\ (fp_complete fp = true \/ (fp = FP_none /\ sin <> nil))) ->
  (0 < r -> (r = 1 /\ a1 = 1) \/ r <= fp_rem fp) ->
  stream_claims_m (sm_md sm) (sm_sel sm) (sm_cur sm) (sm_wl sm) sin0 sout0 sin sall sout a1 ocap r.
Proof.
intros sm sin0 sout0 sin sall sout fp pend a1 r ocap Hb Hm Herr Hz Hh.
unfold stream_claims_m. intros s Hbs Hp.
destruct Hm as [Hd|[cd Hm]].
{ pose proof (proj1 Hd s Hp) as Ht. cbv zeta.
  split; [intros [E|E]; congruence|]. split; [intros _ E; contradiction|].
  split; [intros [E|E]; congruence|]. intros _ _ Hf; congruence. }
split; [|split; [|split]].
- intros Ht. exact (epi3_content sm sin sout fp pend cd Hb Hm s Hp Ht).
- intros Hr Ht. destruct (Hz Hr) as [-> Hc]. eapply epi3_zero; eauto.
- intros Ht _ Hr _. destruct (Hh Hr) as [[-> ->]|Hle].
  + apply Z.max_le_iff. left. destruct (_ || _)%bool; lia.
  + pose proof (epi3_hint sm sin sout fp pend cd Hb Hm s Hp Hbs Ht). apply Z.max_le_iff. right. lia.
- intros _ _ Hf. congruence.
Qed.

Lemma epi_ahead_bytes : forall stable obuf sout k sv,
  c_core stable obuf sout k sv -> bytes_ok (sv_ahead sv).
Proof.
intros stable obuf sout k sv (Hh & _).
destruct Hh as [(_ & ->)|[(_ & ->)|(_ & _ & _ & _ & Hb & _)]]; auto; constructor.
Qed.

(* the model input of the call at the epilogue *)
Definition epi_sin (a: dsa) (w: lw) : list Z :=
  a_sin a ++ sublist (a_ipos a) (w_ipc w) (a_ibs a) ++ sv_ahead (w_sv w).

(* a non-error return: Spec_api6's postcondition from the loop invariant, given the new context k' and its view
   sv' (same frame progress and pending output) and the stream relation's concrete part *)
Lemma epi_post_gen : forall (a: dsa) (w: lw) (k': cst3) (sv': sview) (r ipos' a' stall': Z),
  let ss := dc_ss (a_st a) in
  let st' := epi_st a r ipos' a' stall' (w_dl w) in
  dsa_ok a -> call_inv a (w_k w) (w_sv w) (w_ipc w) (w_opc w) (w_oc w) (w_dl w) -> start_ok a ->
  untouched_ok a w ->
  a_ipos a <= ipos' <= a_isz a -> 0 <= a' <= 1 -> a_ipos a + ss_ahead ss <= ipos' + a' ->
  (ipos' + a' <= a_isz a \/ ipos' + a' = a_ipos a + ss_ahead ss) ->
  ss_in ss ++ sublist (a_ipos a + ss_ahead ss) (ipos' + a') (a_ibs a) = epi_sin a w ->
  0 <= r <= Int64.max_unsigned -> is_error_code r = false -> (a' = 1 -> r = 1) ->
  (r = 0 -> sv_pend (w_sv w) = nil /\
     (fp_complete (sv_fp (w_sv w)) = true \/ (sv_fp (w_sv w) = FP_none /\ epi_sin a w <> nil))) ->
  (0 < r -> (r = 1 /\ a' = 1) \/ r <= fp_rem (sv_fp (w_sv w))) ->
  ((ipos' <> a_ipos a \/ w_opc w <> a_opos a) -> stall' = 0) ->
  (ipos' = a_ipos a -> w_opc w = a_opos a -> 0 <= stall' <= ss_stall ss + 1) ->
  (dc_ss st' = ss_init -> sf_stage (c3_s k') = 0 /\ sf_nfp (c3_s k') = 0) ->
  0 <= sf_nfp (c3_s k') <= ZSTD_NO_FORWARD_PROGRESS_MAX ->
  base_call (a_st a) k' ->
  (forall cd, cur_dict_ok (a_st a) (w_k w) cd -> cur_dict_ok (a_st a) k' cd) ->
  c_rel (a_gv a) st' k' sv' ->
  sv_fp sv' = sv_fp (w_sv w) -> sv_pend sv' = sv_pend (w_sv w) ->
  a' = Zlength (sv_ahead sv') -> (exists sin0, epi_sin a w = sin0 ++ sv_ahead sv') ->
  ((hist_ok (dc_stable (a_st a)) (w_k w) (w_sv w) -> hist_ok (dc_stable (a_st a)) k' sv') \/
   dead (sm_of (a_st a)) (epi_sin a w)) ->
  ep_prog a r ipos' (w_opc w) a' stall' ->
  (* the exact part: the model at the loop's exit and the branch of its epilogue this return takes *)
  epi_xm a w ->
  (w_ipc w = a_ipos a -> w_opc w = a_opos a ->
     ~ (sf_nfp (c3_s (w_k w)) + 1 >= ZSTD_NO_FORWARD_PROGRESS_MAX /\ (w_opc w = a_osz a \/ w_ipc w = a_isz a))) ->
  epi_xbr a w k' r ipos' a' ->
  epi_ok a k' r ipos' (w_opc w) (w_oc w).
Proof.
intros a w k' sv' r ipos' a' stall' ss st' Ha CI Hst Hun Hip' Ha' Hia Hia2 Hsin Hr Herr Ha1 Hz Hh Hs1 Hs2
  Hinit Hnfp' Hbc' Hcd' Hcrel Hfp' Hpend' Hah' Hsin0' Hhist' Hprog Hxm Hxg Hxb.
pose proof CI as (Hip & Hop & Hloc & Hpre & Hdl & Hdlc & Hdlb & Hbc & Hbin & Hn1 & Hn2 & Hn3 &
  Hcore & Hdd & Hstout & Hahead & Hblk & Hmodel & Hlh & Hsinh & Hexp & HT).
pose proof Ha as (_ & _ & _ & _ & _ & _ & _ & Hdict & Herr0 & Hopos & Hosz & Hloc0 & Hipos & Hisz & Hlibs & Hbibs & _).
assert (Hbsin: bytes_ok (epi_sin a w)).
{ unfold epi_sin. apply Forall_app. split; [exact Hbin|]. apply Forall_app. split.
  - apply Forall_sublist. exact Hbibs.
  - eapply epi_ahead_bytes; eauto. }
assert (Hmodel': dead (sm_of (a_st a)) (epi_sin a w) \/
  exists cd, m_rel_cd (sm_of (a_st a)) (epi_sin a w) (ss_out ss ++ w_dl w) (sv_fp (w_sv w)) (sv_pend (w_sv w)) cd).
{ destruct Hmodel as [Hd|(cd & Hm & _)]; [left; exact Hd|right; exists cd; exact Hm]. }
split; [exact Hr|].
exists st'. split; [|exact (epi_x_ret a w k' r ipos' a' Ha CI Hst Hxm Hxg Hia Hia2 Hxb stall')].
unfold epi_okr. split.
- unfold stream_post. exists (w_dl w), stall', a'. cbv zeta.
  fold ss. rewrite Hsin.
  split; [lia|]. split; [lia|]. split; [exact Hloc|]. split; [exact Hpre|].
  split; [lia|]. split; [intros _; split; [exact Hdlc|exact Hdlb]|].
  split; [lia|]. split; [lia|]. split; [exact Hia2|].
  split; [intros E _; auto|].
  split; [unfold st', epi_st; fold ss; rewrite Hsin; reflexivity|].
  split; [intros _ H; apply Hs1; exact H|].
  split; [intros _ H1 H2; apply Hs2; auto|].
  split; [intros H1 H2; specialize (Hblk H2 H1); pose proof (Zlength_nonneg (sv_pend (w_sv w))); lia|].
  split.
  + unfold stall_ok. intros [E|E]; subst r; discriminate Herr.
  + split.
    * apply (epi_claims (sm_of (a_st a)) _ _ _ _ _ (sv_fp (w_sv w)) (sv_pend (w_sv w))); auto.
    * exact (epi3_zero_ref (sm_of (a_st a)) _ _ (sv_fp (w_sv w)) (sv_pend (w_sv w)) r Hbsin Hmodel' Hz).
- split; [apply epi_base; auto; intros _; exact Hnfp'|]. split; [|split; [apply epi_bl; exact Ha|split; [exact Hprog|intros Hs _; exact (Hun Hs)]]].
  intros _ _. unfold SR3. exists sv'.
  assert (Hin': ss_in (dc_ss st') = epi_sin a w) by (unfold st', epi_st; simpl; fold ss; exact Hsin).
  rewrite Hin'.
  split; [exact Hcrel|]. split; [exact Hbsin|]. split; [unfold st', epi_st; simpl; exact Hah'|].
  split; [exact Hsin0'|].
  assert (Hout': ss_out (dc_ss st') = ss_out ss ++ w_dl w) by reflexivity. rewrite Hout'.
  change (alive_ok (a_st a) k' sv' (epi_sin a w) (ss_out ss ++ w_dl w)).
  unfold alive_ok. rewrite Hfp', Hpend'.
  destruct Hhist' as [Hhist'|Hd]; [|left; exact Hd].
  destruct Hmodel as [Hd|(cd & Hm & Hc0 & Hh0)]; [left; exact Hd|right; exists cd].
  split; [exact Hm|]. split; [apply Hcd'; exact Hc0|apply Hhist'; exact Hh0].
Qed.

(* ---------- the concrete relation of the new state ---------- *)

Lemma c_core_obuf : forall stable obuf obuf' sout k sv,
  (stable = true -> obuf' = obuf) -> c_core stable obuf sout k sv -> c_core stable obuf' sout k sv.
Proof.
intros stable obuf obuf' sout k sv E H. destruct stable; [rewrite E by auto; exact H|exact H].
Qed.

Lemma c_core_epi : forall stable obuf sout k sv n ev,
  c_core stable obuf sout k sv ->
  c_core stable obuf sout (k_epi k (sf_stage (c3_s k)) n (sf_hostage (c3_s k)) ev) sv.
Proof. intros. exact H. Qed.

Lemma hist_ok_epi : forall stable k sv n h ev,
  hist_ok stable k sv -> hist_ok stable (k_epi k (sf_stage (c3_s k)) n h ev) sv.
Proof. intros. exact H. Qed.

Lemma epi_ss_ahead : forall (a: dsa) (ah: list Z),
  start_ok a -> a_sin a ++ ah = ss_in (dc_ss (a_st a)) -> ss_ahead (dc_ss (a_st a)) = Zlength ah.
Proof.
intros a ah (_ & Ha & Hle) E. apply (f_equal (@Zlength Z)) in E. rewrite Zlength_app in E.
unfold a_sin in E. rewrite Zlength_sublist in E; [lia| |lia].
pose proof (Zlength_nonneg (ss_in (dc_ss (a_st a)))). lia.
Qed.

Lemma epi_crel : forall (a: dsa) (w: lw) (k': cst3) (sv': sview) (r ipos' a' stall': Z),
  let st' := epi_st a r ipos' a' stall' (w_dl w) in
  let s' := c3_s k' in
  dsa_ok a -> call_inv a (w_k w) (w_sv w) (w_ipc w) (w_opc w) (w_oc w) (w_dl w) ->
  0 <= stall' ->
  sf_expOut s' = epi_ev a (w_opc w) ->
  0 <= sf_nfp s' <= ZSTD_NO_FORWARD_PROGRESS_MAX ->
  ((sf_nfp s' <= stall' /\ sf_nfp s' < ZSTD_NO_FORWARD_PROGRESS_MAX) \/ sf_stage s' = zdss_init) ->
  (sf_stage s' = zdss_flush -> fp_complete (sv_fp sv') = true -> sv_pend sv' <> nil ->
     sf_hostage s' = Vint (Int.repr 1)) ->
  (sf_stage s' <= zdss_loadHeader -> sv_ahead sv' = nil) ->
  sv_dd_ok (a_st a) k' sv' ->
  c_core (dc_stable (a_st a)) (Some (a_ob a, a_osz a)) (ss_out (dc_ss (a_st a)) ++ w_dl w) k' sv' ->
  c_rel (a_gv a) st' k' sv'.
Proof.
intros a w k' sv' r ipos' a' stall' st' s' Ha CI Hst0 Hexp Hn1 Hn2 HT Hlh Hdd' Hcore.
pose proof CI as (Hip & Hop & Hloc & Hpre & Hdl & _).
pose proof Ha as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstpos & _).
unfold c_rel. fold s'.
split; [exact Hst0|]. split; [exact Hn1|]. split; [destruct Hn2 as [H|H]; [left; exact H|right; left; exact H]|].
split; [exact HT|]. split.
- intros Hs _. change (dc_stable st') with (dc_stable (a_st a)) in Hs.
  unfold st', epi_st; simpl. rewrite Hs. exists (a_obf a), (a_osz a). split; [reflexivity|].
  rewrite Hexp. unfold epi_ev. rewrite Zlength_app, <- (Hstpos Hs), Hdl. f_equal. f_equal. f_equal. lia.
- split; [exact Hlh|]. split; [exact Hdd'|].
  change (dc_stable st') with (dc_stable (a_st a)).
  eapply c_core_obuf; [|exact Hcore]. intros Hs. unfold st', epi_st; simpl. rewrite Hs. reflexivity.
Qed.

(* ---------- the paths of the tail ---------- *)

(* the loop's state at the epilogue, with the facts R4a/R4b (exit_ok X2, start_ok: epi_R4ab) *)
Definition epi_hyp (a: dsa) (w: lw) : Prop :=
  dsa_ok a /\ call_inv a (w_k w) (w_sv w) (w_ipc w) (w_opc w) (w_oc w) (w_dl w) /\ w_smw w = 0 /\
  start_ok a /\ exit_ok a w /\
  (sf_stage (c3_s (w_k w)) = zdss_flush -> sv_pend (w_sv w) <> nil) /\
  0 <= ss_stall (dc_ss (a_st a)) /\ untouched_ok a w.

Definition epi_np (a: dsa) (w: lw) : bool := (w_ipc w =? a_ipos a) && (w_opc w =? a_opos a).
Definition epi_n' (a: dsa) (w: lw) : Z := if epi_np a w then sf_nfp (c3_s (w_k w)) + 1 else 0.
Definition epi_k1 (a: dsa) (w: lw) : cst3 := k_nfp a (w_k w) (w_opc w) (epi_n' a w).

(* the no-progress guard did not fire *)
Definition epi_guard (a: dsa) (w: lw) : Prop :=
  epi_np a w = true ->
  ~ (sf_nfp (c3_s (w_k w)) + 1 >= ZSTD_NO_FORWARD_PROGRESS_MAX /\ (w_opc w = a_osz a \/ w_ipc w = a_isz a)).

(* the read-stage DDict facts for the "can't release the hostage byte" path (from exit_ok X4: E3Main.epi_dd_gap_ok), which
   sets streamStage := zdss_read again *)
Definition epi_dd_gap (a: dsa) (w: lw) : Prop :=
  sf_stage (c3_s (w_k w)) = zdss_init -> sf_hostage (c3_s (w_k w)) = Vint (Int.repr 1) ->
  sv_dd_ok (a_st a) (c3_with_s (w_k w) (sf_set_stage (c3_s (w_k w)) zdss_read)) (w_sv w).

Lemma epi_np_true : forall a w, epi_np a w = true <-> (w_ipc w = a_ipos a /\ w_opc w = a_opos a).
Proof.
intros a w. unfold epi_np. rewrite Bool.andb_true_iff, !Z.eqb_eq. tauto.
Qed.

Lemma epi_stage_cases : forall stable obuf sout k sv,
  c_core stable obuf sout k sv -> sf_stage (c3_s k) <> zdss_init -> sf_stage (c3_s k) <> zdss_loadHeader ->
  sf_stage (c3_s k) = zdss_read \/ sf_stage (c3_s k) = zdss_load \/ sf_stage (c3_s k) = zdss_flush.
Proof.
intros stable obuf sout k sv (_ & _ & _ & H) H1 H2.
rewrite (proj2 (Z.eqb_neq _ _) H1), (proj2 (Z.eqb_neq _ _) H2) in H. tauto.
Qed.

(* the facts of the loop state the paths share *)
Lemma epi_n'_facts : forall a w, epi_hyp a w -> epi_guard a w ->
  let n := sf_nfp (c3_s (w_k w)) in
  0 <= epi_n' a w <= ZSTD_NO_FORWARD_PROGRESS_MAX /\
  (epi_np a w = false -> epi_n' a w = 0) /\
  (epi_np a w = true -> epi_n' a w = n + 1 /\ 0 <= n + 1 <= ss_stall (dc_ss (a_st a)) + 1) /\
  (sf_stage (c3_s (w_k w)) <> zdss_init -> epi_n' a w < ZSTD_NO_FORWARD_PROGRESS_MAX).
Proof.
intros a w (Ha & CI & Hsmw & Hst & Hex & R4a & R4b) Hg n.
destruct (Hex Hsmw) as (X1 & X2rl & X2f & X3 & X4).
pose proof CI as (Hip & Hop & Hloc & Hpre & Hdl & Hdlc & Hdlb & Hbc & Hbin & Hn1 & Hn2 & Hn3 &
  Hcore & _).
unfold epi_n'. destruct (epi_np a w) eqn:E.
- apply epi_np_true in E. destruct E as [E1 E2]. destruct (X3 E1 E2) as [X3a X3b]. fold n in X3a, X3b.
  split; [unfold ZSTD_NO_FORWARD_PROGRESS_MAX in *; lia|]. split; [discriminate|]. split; [intros _; lia|].
  intros Hni. destruct (epi_stage_cases _ _ _ _ _ Hcore Hni X1) as [Hs|[Hs|Hs]].
  + destruct (Z.lt_ge_cases (n + 1) ZSTD_NO_FORWARD_PROGRESS_MAX); auto. exfalso.
    apply (Hg (proj2 (epi_np_true a w) (conj E1 E2))). split; [unfold n in *; lia|]. right. apply X2rl. auto.
  + destruct (Z.lt_ge_cases (n + 1) ZSTD_NO_FORWARD_PROGRESS_MAX); auto. exfalso.
    apply (Hg (proj2 (epi_np_true a w) (conj E1 E2))). split; [unfold n in *; lia|]. right. apply X2rl. auto.
  + destruct (Z.lt_ge_cases (n + 1) ZSTD_NO_FORWARD_PROGRESS_MAX); auto. exfalso.
    apply (Hg (proj2 (epi_np_true a w) (conj E1 E2))). split; [unfold n in *; lia|]. left. apply X2f. auto.
- split; [unfold ZSTD_NO_FORWARD_PROGRESS_MAX; lia|]. split; [auto|]. split; [discriminate|].
  intros _. unfold ZSTD_NO_FORWARD_PROGRESS_MAX; lia.
Qed.

Lemma epi_sin_same : forall a w, start_ok a ->
  call_inv a (w_k w) (w_sv w) (w_ipc w) (w_opc w) (w_oc w) (w_dl w) ->
  let ss := dc_ss (a_st a) in
  ss_in ss ++ sublist (a_ipos a + ss_ahead ss) (w_ipc w + ss_ahead ss) (a_ibs a) = epi_sin a w.
Proof.
intros a w Hst CI ss.
pose proof CI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hahead & _ & _ & _ & Hsinh & _).
pose proof (epi_ss_ahead a _ Hst Hsinh) as Hssa. fold ss in Hssa, Hsinh.
unfold epi_sin. destruct (sv_ahead (w_sv w)) as [|b l] eqn:Ea.
- rewrite Zlength_nil in Hssa. rewrite Hssa, !Z.add_0_r. rewrite app_nil_r in Hsinh.
  rewrite <- Hsinh, app_nil_r. reflexivity.
- rewrite Hahead by discriminate. rewrite sublist_nil, app_nil_r. rewrite sublist_nil, app_nil_l.
  exact (eq_sym Hsinh).
Qed.

Lemma epi_hostage0 : forall stable obuf sout k sv,
  c_core stable obuf sout k sv -> sf_hostage (c3_s k) = Vint Int.zero -> sv_ahead sv = nil.
Proof.
intros stable obuf sout k sv (Hh & _) E.
destruct Hh as [(_ & A)|[(_ & A)|(E1 & _)]]; auto. rewrite E in E1. discriminate.
Qed.

Lemma epi_not_init : forall a w r ipos' a' stall', dsa_ok a ->
  call_inv a (w_k w) (w_sv w) (w_ipc w) (w_opc w) (w_oc w) (w_dl w) ->
  ss_in (dc_ss (epi_st a r ipos' a' stall' (w_dl w))) = epi_sin a w ->
  (w_ipc w = a_ipos a -> w_opc w = a_opos a -> sv_ahead (w_sv w) = nil -> stall' <> 0) ->
  dc_ss (epi_st a r ipos' a' stall' (w_dl w)) <> ss_init.
Proof.
intros a w r ipos' a' stall' Ha CI Hin Hs E.
pose proof CI as (Hip & Hop & _ & _ & Hdl & _).
pose proof Ha as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hipos & _ & Hlibs & _).
assert (Hin0: epi_sin a w = nil) by (rewrite <- Hin, E; reflexivity).
assert (Hout0: ss_out (dc_ss (a_st a)) ++ w_dl w = nil)
  by (change (ss_out (dc_ss (epi_st a r ipos' a' stall' (w_dl w))) = nil); rewrite E; reflexivity).
assert (Hst0: stall' = 0) by (change (ss_stall (dc_ss (epi_st a r ipos' a' stall' (w_dl w))) = 0); rewrite E; reflexivity).
unfold epi_sin in Hin0. apply app_eq_nil in Hin0. destruct Hin0 as [_ Hin0]. apply app_eq_nil in Hin0.
destruct Hin0 as [Hsub Hah]. apply app_eq_nil in Hout0. destruct Hout0 as [_ Hdl0].
apply (Hs); auto.
- apply (f_equal (@Zlength Z)) in Hsub. rewrite Zlength_sublist in Hsub by lia. rewrite Zlength_nil in Hsub. lia.
- rewrite Hdl0, Zlength_nil in Hdl. lia.
Qed.

(* the returns that keep stage, hostage byte and view: the hint, return 0 without hostage, return 1 with the
   hostage byte held *)
Lemma epi_path_same : forall a w r n', epi_hyp a w -> epi_guard a w ->
  0 <= r <= Int64.max_unsigned -> is_error_code r = false ->
  (sv_ahead (w_sv w) <> nil -> r = 1) ->
  (r = 0 -> sv_pend (w_sv w) = nil /\
     (fp_complete (sv_fp (w_sv w)) = true \/ (sv_fp (w_sv w) = FP_none /\ epi_sin a w <> nil))) ->
  (0 < r -> (r = 1 /\ sv_ahead (w_sv w) <> nil) \/ r <= fp_rem (sv_fp (w_sv w))) ->
  (sf_stage (c3_s (w_k w)) = zdss_flush -> fp_complete (sv_fp (w_sv w)) = true -> sv_pend (w_sv w) <> nil ->
     sf_hostage (c3_s (w_k w)) = Vint (Int.repr 1)) ->
  (sf_stage (c3_s (w_k w)) = zdss_init -> sv_ahead (w_sv w) = nil) ->
  (* the stall count after the call: zstd's, or 0 at zdss_init (c_rel leaves it free there) *)
  (n' = epi_n' a w \/ (n' = 0 /\ sf_stage (c3_s (w_k w)) = zdss_init /\ epi_sin a w <> nil)) ->
  ep_prog a r (w_ipc w) (w_opc w) (ss_ahead (dc_ss (a_st a))) n' ->
  epi_xm a w -> epi_xbr a w (epi_k1 a w) r (w_ipc w) (ss_ahead (dc_ss (a_st a))) ->
  epi_ok a (epi_k1 a w) r (w_ipc w) (w_opc w) (w_oc w).
Proof.
intros a w r n' H Hg Hr Herr Hah1 Hz Hh HT1 Hinah Hn' Hprog Hxm Hxb.
pose proof H as (Ha & CI & Hsmw & Hst & Hex & R4a & R4b & Hun).
destruct (Hex Hsmw) as (X1 & X2rl & X2f & X3 & X4).
pose proof CI as (Hip & Hop & Hloc & Hpre & Hdl & Hdlc & Hdlb & Hbc & Hbin & Hn1 & Hn2 & Hn3 &
  Hcore & Hdd & Hstout & Hahead & Hblk & Hmodel & Hlh & Hsinh & Hexp & HT).
pose proof (epi_ss_ahead a _ Hst Hsinh) as Hssa.
destruct (epi_n'_facts a w H Hg) as (Hn'1 & Hn'2 & Hn'3 & Hn'4).
pose proof Hst as (_ & Hah01 & _).
assert (Hlen1: sv_ahead (w_sv w) <> nil -> Zlength (sv_ahead (w_sv w)) = 1).
{ intros Hne. destruct (sv_ahead (w_sv w)); [congruence|]. rewrite Zlength_cons in *. 
  pose proof (Zlength_nonneg l). lia. }
apply (epi_post_gen a w (epi_k1 a w) (w_sv w) r (w_ipc w) (ss_ahead (dc_ss (a_st a))) n').
- exact Ha.
- exact CI.
- exact Hst.
- exact Hun.
- lia.
- lia.
- lia.
- destruct (sv_ahead (w_sv w)) eqn:E.
  + left. rewrite Hssa, Zlength_nil. lia.
  + right. rewrite Hahead by congruence. reflexivity.
- apply epi_sin_same; auto.
- exact Hr.
- exact Herr.
- intros E. apply Hah1. intro E'. rewrite E', Zlength_nil in Hssa. lia.
- exact Hz.
- intros Hr0. destruct (Hh Hr0) as [[E1 E2]|E]; [left; split; auto; rewrite Hssa; auto|right; exact E].
- intros Hp. destruct Hn' as [->|(-> & _)]; [|reflexivity].
  apply Hn'2. destruct (epi_np a w) eqn:E; auto. apply epi_np_true in E. lia.
- intros E1 E2. destruct Hn' as [->|(-> & _)]; [|lia].
  assert (E: epi_np a w = true) by (apply epi_np_true; auto). destruct (Hn'3 E). lia.
- intros E. destruct Hn' as [->|(-> & _ & Hne)].
  + exfalso. revert E. apply (epi_not_init a w r (w_ipc w) (ss_ahead (dc_ss (a_st a))) (epi_n' a w) Ha CI).
    * unfold epi_st. simpl. apply epi_sin_same; auto.
    * intros E1 E2 _. assert (E: epi_np a w = true) by (apply epi_np_true; auto). destruct (Hn'3 E). lia.
  + exfalso. apply Hne. rewrite <- (epi_sin_same a w Hst CI).
    change (ss_in (dc_ss (epi_st a r (w_ipc w) (ss_ahead (dc_ss (a_st a))) 0 (w_dl w))) = nil).
    rewrite E. reflexivity.
- cbn [epi_k1 k_sh k_nfp k_epi sf_epi c3_with_s c3_s sf_nfp]; exact Hn'1.
- exact Hbc.
- intros cd0 Hcd0; exact Hcd0.
- apply epi_crel; cbn [epi_k1 k_nfp k_epi sf_epi c3_with_s c3_s sf_nfp sf_stage sf_hostage sf_expOut]; auto.
  + destruct Hn' as [->|(-> & _)]; lia.
  + destruct (Z.eq_dec (sf_stage (c3_s (w_k w))) zdss_init) as [Ei|Ei]; [right; exact Ei|left].
    destruct Hn' as [->|(_ & Ei' & _)]; [|contradiction].
    split; [lia|]. apply Hn'4. exact Ei.
  + intros Hs. apply Hinah. destruct (Z.eq_dec (sf_stage (c3_s (w_k w))) zdss_init) as [Ei|Ei]; auto.
    destruct (epi_stage_cases _ _ _ _ _ Hcore Ei X1) as [E|[E|E]]; simpl in Hs; rewrite E in Hs;
      unfold zdss_read, zdss_load, zdss_flush, zdss_loadHeader in Hs; lia.
- reflexivity.
- reflexivity.
- exact Hssa.
- exists (a_sin a ++ sublist (a_ipos a) (w_ipc w) (a_ibs a)). unfold epi_sin. rewrite app_assoc. reflexivity.
- left. apply hist_ok_epi.
- exact Hprog.
- exact Hxm.
- intros E1 E2; apply Hg; apply epi_np_true; auto.
- exact Hxb.
Qed.

(* the hostage byte is held: one byte ahead, the frame complete, buffered mode *)
Lemma epi_hostage1 : forall a w, epi_hyp a w ->
  sf_hostage (c3_s (w_k w)) = Vint (Int.repr 1) ->
  Zlength (sv_ahead (w_sv w)) = 1 /\ fp_complete (sv_fp (w_sv w)) = true /\ dc_stable (a_st a) = false /\
  (sf_stage (c3_s (w_k w)) = zdss_init \/ sf_stage (c3_s (w_k w)) = zdss_read \/
   sf_stage (c3_s (w_k w)) = zdss_flush).
Proof.
intros a w (Ha & CI & Hsmw & Hst & Hex & R4a & R4b) Hh.
destruct (Hex Hsmw) as (X1 & X2rl & X2f & X3 & X4).
pose proof CI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcore & _).
pose proof Hcore as (Hd & _).
destruct Hd as [(Hi & Hnil)|[(H0 & _)|(_ & Hstab & Hc & Hl & _ & Hs)]].
- destruct (X4 Hi) as (_ & _ & [(H0 & _)|(_ & Hl & _)]); [rewrite Hh in H0; discriminate|].
  rewrite Hnil in Hl. discriminate.
- rewrite Hh in H0. discriminate.
- auto.
Qed.

(* ---------- the progress claim of each return (E3Prog.ep_prog_of) ---------- *)

(* the output is full and output is held back (the loop stopped in zdss_flush) *)
Lemma epi_prog_full : forall a w r ipos' a' stall', epi_hyp a w ->
  sf_stage (c3_s (w_k w)) = zdss_flush -> r <> 0 ->
  let ss := dc_ss (a_st a) in
  ss_in ss ++ sublist (a_ipos a + ss_ahead ss) (ipos' + a') (a_ibs a) = epi_sin a w ->
  ep_prog a r ipos' (w_opc w) a' stall'.
Proof.
intros a w r ipos' a' stall' H Hfl Hr0 ss Hsin.
pose proof H as (Ha & CI & Hsmw & Hst & Hex & R4a & R4b).
destruct (Hex Hsmw) as (X1 & X2rl & X2f & X3 & X4).
destruct (X2f Hfl) as [Hoo Hpn].
apply (ep_prog_of a (w_k w) (w_sv w) (w_ipc w) (w_opc w) (w_oc w) (w_dl w)); auto.
intros _ _ _. split; [intros E; contradiction|]. intros _. left. auto.
Qed.

(* return 0 without the hostage byte: at zdss_init the stall count restarts (stall' = 0), after zdss_read all the
   input was read *)
Lemma epi_prog_zero : forall a w, epi_hyp a w ->
  (sf_stage (c3_s (w_k w)) = zdss_init \/ fp_complete (sv_fp (w_sv w)) = true) -> sv_pend (w_sv w) = nil ->
  ep_prog a 0 (w_ipc w) (w_opc w) (ss_ahead (dc_ss (a_st a)))
    (if sf_stage (c3_s (w_k w)) =? zdss_init then 0 else epi_n' a w).
Proof.
intros a w H Hic Hpend.
pose proof H as (Ha & CI & Hsmw & Hst & Hex & R4a & R4b).
destruct (Hex Hsmw) as (X1 & X2rl & X2f & X3 & X4).
pose proof CI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcore & _).
apply (ep_prog_of a (w_k w) (w_sv w) (w_ipc w) (w_opc w) (w_oc w) (w_dl w)); auto.
- apply epi_sin_same; auto.
- intros _ Hi _. split; [|intros E; congruence]. intros _.
  destruct (Z.eqb_spec (sf_stage (c3_s (w_k w))) zdss_init) as [Ei|Ei]; [right; reflexivity|left].
  destruct (epi_stage_cases _ _ _ _ _ Hcore Ei X1) as [E|[E|E]].
  + rewrite <- Hi. apply X2rl. left. exact E.
  + rewrite <- Hi. apply X2rl. right. exact E.
  + exfalso. exact (R4a E Hpend).
Qed.

(* the hint (the frame not complete): all the input read, or the output full *)
Lemma epi_prog_hint : forall a w r stall', epi_hyp a w ->
  sf_stage (c3_s (w_k w)) <> zdss_init -> 0 < fp_rem (sv_fp (w_sv w)) -> r <> 0 ->
  ep_prog a r (w_ipc w) (w_opc w) (ss_ahead (dc_ss (a_st a))) stall'.
Proof.
intros a w r stall' H Hni Hrem Hr0.
pose proof H as (Ha & CI & Hsmw & Hst & Hex & R4a & R4b).
destruct (Hex Hsmw) as (X1 & X2rl & X2f & X3 & X4).
pose proof CI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcore & _).
pose proof Hst as (_ & Hah01 & _).
destruct (epi_stage_cases _ _ _ _ _ Hcore Hni X1) as [E|[E|E]].
2-3: try (apply epi_prog_full; auto; apply epi_sin_same; auto).
all: apply (ep_prog_of a (w_k w) (w_sv w) (w_ipc w) (w_opc w) (w_oc w) (w_dl w)); auto;
  [apply epi_sin_same; auto|].
all: intros _ Hi _; split; [intros; contradiction|]; intros _; right.
all: assert (Hiz: w_ipc w = a_isz a) by (apply X2rl; auto).
all: split; [lia|]; split; [lia|]; left; exact Hrem.
Qed.

(* return 1 when the hostage byte cannot be released: all read and delivered *)
Lemma epi_prog_cr : forall a w stall', epi_hyp a w ->
  sv_pend (w_sv w) = nil -> sf_hostage (c3_s (w_k w)) = Vint (Int.repr 1) -> a_isz a <= w_ipc w ->
  ep_prog a 1 (w_ipc w) (w_opc w) (ss_ahead (dc_ss (a_st a))) stall'.
Proof.
intros a w stall' H Hpend Hh Hge.
destruct (epi_hostage1 a w H Hh) as (Hl1 & Hc & Hstab & Hs).
pose proof H as (Ha & CI & Hsmw & Hst & Hex & R4a & R4b).
pose proof CI as (Hip & Hop & Hloc & Hpre & Hdl & Hdlc & Hdlb & Hbc & Hbin & Hn1 & Hn2 & Hn3 &
  Hcore & Hdd & Hstout & Hahead & Hblk & Hmodel & Hlh & Hsinh & Hexp & HT).
pose proof (epi_ss_ahead a _ Hst Hsinh) as Hssa.
assert (Hne: sv_ahead (w_sv w) <> nil) by (intro E; rewrite E, Zlength_nil in Hl1; discriminate).
assert (Hipc: w_ipc w = a_ipos a) by (apply Hahead; exact Hne).
apply (ep_prog_of a (w_k w) (w_sv w) (w_ipc w) (w_opc w) (w_oc w) (w_dl w)); auto.
- apply epi_sin_same; auto.
- intros _ _ _. split; [intros E; discriminate|]. intros _. right.
  split; [lia|]. split; [lia|]. right; right.
  split; [exact Hpend|]. split; [left; exact Hc|].
  rewrite Hipc, sublist_nil, app_nil_l, Hsinh. lia.
Qed.

Definition sv_noahead (sv: sview) : sview :=
  {| sv_fp := sv_fp sv; sv_pend := sv_pend sv; sv_ahead := nil; sv_lay := sv_lay sv; sv_dd := sv_dd sv |}.

(* return 0 releasing the hostage byte (in.pos + 1) *)
Lemma epi_path_rel : forall a w, epi_hyp a w -> epi_guard a w ->
  sv_pend (w_sv w) = nil -> sf_hostage (c3_s (w_k w)) = Vint (Int.repr 1) -> w_ipc w < a_isz a ->
  epi_xm a w -> epi_xbr a w (epi_k1 a w) 0 (w_ipc w + 1) 0 ->
  epi_ok a (epi_k1 a w) 0 (w_ipc w + 1) (w_opc w) (w_oc w).
Proof.
intros a w H Hg Hpend Hh Hlt Hxm Hxb.
destruct (epi_hostage1 a w H Hh) as (Hl1 & Hc & Hstab & Hs).
pose proof H as (Ha & CI & Hsmw & Hst & Hex & R4a & R4b & Hun).
destruct (Hex Hsmw) as (X1 & X2rl & X2f & X3 & X4).
pose proof CI as (Hip & Hop & Hloc & Hpre & Hdl & Hdlc & Hdlb & Hbc & Hbin & Hn1 & Hn2 & Hn3 &
  Hcore & Hdd & Hstout & Hahead & Hblk & Hmodel & Hlh & Hsinh & Hexp & HT).
pose proof (epi_ss_ahead a _ Hst Hsinh) as Hssa.
destruct (epi_n'_facts a w H Hg) as (Hn'1 & Hn'2 & Hn'3 & Hn'4).
assert (Hne: sv_ahead (w_sv w) <> nil) by (intro E; rewrite E, Zlength_nil in Hl1; discriminate).
assert (Hipc: w_ipc w = a_ipos a) by (apply Hahead; exact Hne).
assert (Hinit: sf_stage (c3_s (w_k w)) = zdss_init).
{ destruct Hs as [E|[E|E]]; auto.
  - rewrite (X2rl (or_introl E)) in Hlt. lia.
  - exfalso. exact (R4a E Hpend). }
apply (epi_post_gen a w (epi_k1 a w) (sv_noahead (w_sv w)) 0 (w_ipc w + 1) 0 0).
- exact Ha.
- exact CI.
- exact Hst.
- exact Hun.
- lia.
- lia.
- lia.
- left. lia.
- rewrite Hssa, Hl1, Hipc, Z.add_0_r, sublist_nil. unfold epi_sin. rewrite Hipc, sublist_nil, app_nil_l, app_nil_r.
  exact (eq_sym Hsinh).
- rep_lia.
- reflexivity.
- intros E; discriminate.
- intros _. split; [exact Hpend|left; exact Hc].
- intros E; lia.
- intros _; reflexivity.
- intros E; lia.
- intros E. exfalso. revert E. apply (epi_not_init a w 0 (w_ipc w + 1) 0 0 Ha CI).
  + unfold epi_st. simpl. rewrite Hssa, Hl1, Hipc, Z.add_0_r, sublist_nil, app_nil_r. unfold epi_sin.
    rewrite Hipc, sublist_nil, app_nil_l. exact (eq_sym Hsinh).
  + intros _ _ E. contradiction.
- cbn [epi_k1 k_sh k_nfp k_epi sf_epi c3_with_s c3_s sf_nfp]; exact Hn'1.
- exact Hbc.
- intros cd0 Hcd0; exact Hcd0.
- apply epi_crel; cbn [epi_k1 k_nfp k_epi sf_epi c3_with_s c3_s sf_nfp sf_stage sf_hostage sf_expOut sv_noahead
    sv_ahead sv_fp sv_pend]; auto;
  first [ lia | right; exact Hinit | intros E; rewrite Hinit in E; discriminate
        | (unfold sv_dd_ok; intros C; exfalso; cbn [c3_s sf_stage] in C; rewrite Hinit in C;
           unfold zdss_read, zdss_init in C; lia)
        | destruct Hcore as (_ & Hrest); split; [left; split; [exact Hinit|reflexivity]|exact Hrest] ].
- reflexivity.
- reflexivity.
- reflexivity.
- exists (epi_sin a w). rewrite app_nil_r. reflexivity.
- left. intros _. unfold hist_ok. intros _ E. exfalso. apply E. exact Hinit.
- apply ep_prog_moved. lia.
- exact Hxm.
- intros E1 E2; apply Hg; apply epi_np_true; auto.
- exact Hxb.
Qed.

Lemma c_core_stage : forall stable obuf sout k sv x n h ev,
  c_core stable obuf sout k sv -> sf_stage (c3_s k) = x -> h = sf_hostage (c3_s k) ->
  c_core stable obuf sout (k_epi k x n h ev) sv.
Proof. intros. subst h. rewrite <- H0. exact H. Qed.

Lemma hist_ok_stage : forall stable k sv x n h ev,
  hist_ok stable k sv -> sf_stage (c3_s k) = x -> hist_ok stable (k_epi k x n h ev) sv.
Proof. intros. rewrite <- H0. exact H. Qed.

(* return 1, the hostage byte not in this call's input (streamStage := zdss_read) *)
Lemma epi_path_cr : forall a w, epi_hyp a w -> epi_guard a w -> epi_dd_gap a w ->
  sv_pend (w_sv w) = nil -> sf_hostage (c3_s (w_k w)) = Vint (Int.repr 1) -> a_isz a <= w_ipc w ->
  epi_xm a w -> epi_xbr a w (k_sh (epi_k1 a w) zdss_read (sf_hostage (c3_s (epi_k1 a w)))) 1 (w_ipc w) 1 ->
  epi_ok a (k_sh (epi_k1 a w) zdss_read (sf_hostage (c3_s (epi_k1 a w)))) 1 (w_ipc w) (w_opc w) (w_oc w).
Proof.
intros a w H Hg Hgap Hpend Hh Hge Hxm Hxb.
destruct (epi_hostage1 a w H Hh) as (Hl1 & Hc & Hstab & Hs).
pose proof H as (Ha & CI & Hsmw & Hst & Hex & R4a & R4b & Hun).
destruct (Hex Hsmw) as (X1 & X2rl & X2f & X3 & X4).
pose proof CI as (Hip & Hop & Hloc & Hpre & Hdl & Hdlc & Hdlb & Hbc & Hbin & Hn1 & Hn2 & Hn3 &
  Hcore & Hdd & Hstout & Hahead & Hblk & Hmodel & Hlh & Hsinh & Hexp & HT).
pose proof (epi_ss_ahead a _ Hst Hsinh) as Hssa.
destruct (epi_n'_facts a w H Hg) as (Hn'1 & Hn'2 & Hn'3 & Hn'4).
assert (Hne: sv_ahead (w_sv w) <> nil) by (intro E; rewrite E, Zlength_nil in Hl1; discriminate).
assert (Hipc: w_ipc w = a_ipos a) by (apply Hahead; exact Hne).
assert (Hs': sf_stage (c3_s (w_k w)) = zdss_init \/ sf_stage (c3_s (w_k w)) = zdss_read).
{ destruct Hs as [E|[E|E]]; auto. exfalso. exact (R4a E Hpend). }
assert (Hn'16: epi_n' a w < ZSTD_NO_FORWARD_PROGRESS_MAX).
{ destruct (epi_np a w) eqn:E.
  - destruct (Hn'3 eq_refl) as [E1 _]. rewrite E1. destruct (Z.lt_ge_cases (sf_nfp (c3_s (w_k w)) + 1) ZSTD_NO_FORWARD_PROGRESS_MAX); auto.
    exfalso. apply (Hg E). split; [lia|]. right. lia.
  - rewrite (Hn'2 eq_refl). unfold ZSTD_NO_FORWARD_PROGRESS_MAX. lia. }
apply (epi_post_gen a w _ (w_sv w) 1 (w_ipc w) (ss_ahead (dc_ss (a_st a))) (epi_n' a w)).
- exact Ha.
- exact CI.
- exact Hst.
- exact Hun.
- lia.
- rewrite Hssa, Hl1. lia.
- lia.
- right. rewrite Hipc. reflexivity.
- apply epi_sin_same; auto.
- rep_lia.
- reflexivity.
- auto.
- intros E; discriminate.
- intros _. left. split; auto. rewrite Hssa. exact Hl1.
- intros Hp. apply Hn'2. destruct (epi_np a w) eqn:E; auto. apply epi_np_true in E. lia.
- intros E1 E2. assert (E: epi_np a w = true) by (apply epi_np_true; auto). destruct (Hn'3 E). lia.
- intros E. exfalso. revert E. apply (epi_not_init a w 1 (w_ipc w) (ss_ahead (dc_ss (a_st a))) (epi_n' a w) Ha CI).
  + unfold epi_st. simpl. apply epi_sin_same; auto.
  + intros _ _ E. contradiction.
- cbn [epi_k1 k_sh k_nfp k_epi sf_epi c3_with_s c3_s sf_nfp]; exact Hn'1.
- exact Hbc.
- intros cd0 Hcd0; exact Hcd0.
- apply epi_crel; cbn [epi_k1 k_sh k_nfp k_epi sf_epi c3_with_s c3_s sf_nfp sf_stage sf_hostage sf_expOut].
  + exact Ha.
  + exact CI.
  + lia.
  + reflexivity.
  + exact Hn'1.
  + left. lia.
  + intros E. unfold zdss_read, zdss_flush in E. lia.
  + intros E. unfold zdss_read, zdss_loadHeader in E. lia.
  + destruct Hs' as [E|E].
    * exact (Hgap E Hh).
    * unfold sv_dd_ok in *. intros _ x buf Hx. apply Hdd; [rewrite E; lia|exact Hx].
  + destruct Hs' as [E|E].
    * destruct (X4 E) as (_ & _ & [(H0 & _)|(_ & _ & Hc4 & _)]); [rewrite Hh in H0; discriminate|exact Hc4].
    * eapply c_core_stage; [exact Hcore|exact E|reflexivity].
- reflexivity.
- reflexivity.
- exact Hssa.
- exists (a_sin a ++ sublist (a_ipos a) (w_ipc w) (a_ibs a)). unfold epi_sin. rewrite app_assoc. reflexivity.
- destruct Hs' as [E|E].
  + destruct (X4 E) as (_ & _ & [(H0 & _)|(_ & _ & _ & _ & [Hd|Hh4])]).
    * rewrite Hh in H0; discriminate.
    * right. exact Hd.
    * left. intros _. exact Hh4.
  + left. intros Hh0. eapply hist_ok_stage; [exact Hh0|exact E].
- apply epi_prog_cr; auto.
- exact Hxm.
- intros E1 E2; apply Hg; apply epi_np_true; auto.
- rewrite Hssa, Hl1. exact Hxb.
Qed.

Lemma epi_pend_flush : forall stable obuf sout k sv,
  c_core stable obuf sout k sv -> sv_pend sv <> nil ->
  sf_stage (c3_s k) = zdss_flush /\ stable = false.
Proof.
intros stable obuf sout k sv (_ & _ & _ & Hrest) Hp. cbv zeta in Hrest.
destruct (Z.eqb_spec (sf_stage (c3_s k)) zdss_init) as [Ei|Ei].
{ destruct Hrest as [_ Hn]. contradiction. }
destruct (Z.eqb_spec (sf_stage (c3_s k)) zdss_loadHeader) as [El|El].
{ destruct Hrest as [Hn _]. contradiction. }
destruct Hrest as (Hs & _ & _ & Hstf & Hload & _ & Hread).
destruct Hs as [E|[E|E]].
- destruct (Hread E). contradiction.
- destruct (Hload E). contradiction.
- split; [exact E|]. destruct stable; auto. exfalso. exact (Hstf eq_refl E).
Qed.

Definition sv_take (sv: sview) (b: list Z) : sview :=
  {| sv_fp := sv_fp sv; sv_pend := sv_pend sv; sv_ahead := b; sv_lay := sv_lay sv; sv_dd := sv_dd sv |}.

Lemma c_core_take : forall obuf sout k sv b n ev,
  c_core false obuf sout k sv -> sf_stage (c3_s k) = zdss_flush -> fp_complete (sv_fp sv) = true ->
  Zlength b = 1 -> bytes_ok b ->
  c_core false obuf sout (k_epi k (sf_stage (c3_s k)) n (Vint (Int.repr 1)) ev) (sv_take sv b).
Proof.
intros obuf sout k sv b n ev (_ & Hcold & Hsz & Hrest) Hs Hc Hl Hb. cbv zeta in Hrest.
split.
{ right; right. cbn [k_epi sf_epi c3_with_s c3_s sf_hostage sf_stage sv_take sv_fp sv_ahead].
  repeat split; auto. }
split; [exact Hcold|]. split; [exact Hsz|].
cbn [k_epi sf_epi c3_with_s c3_s c3_fs c3_tabs c3_dict c3_par c3_sp c3_set c3_stable sf_stage sf_hostage sf_inPos sf_outStart sf_outEnd sf_lhSize sf_hbuf
     sf_ring sf_inBuff sf_inSize sf_outBuff sf_outSize sv_take sv_fp sv_pend sv_lay sv_ahead sv_dd].
rewrite Hs in Hrest |- *. exact Hrest.
Qed.

(* return 1 taking the hostage byte (in.pos - 1): a complete frame with output pending *)
Lemma epi_path_take : forall a w, epi_hyp a w -> epi_guard a w ->
  (sf_stage (c3_s (w_k w)) = zdss_init \/ fp_complete (sv_fp (w_sv w)) = true) ->
  sv_pend (w_sv w) <> nil -> sf_hostage (c3_s (w_k w)) = Vint Int.zero ->
  epi_xm a w -> epi_xbr a w (k_sh (epi_k1 a w) (sf_stage (c3_s (epi_k1 a w))) (Vint (Int.repr 1))) 1 (w_ipc w - 1) 1 ->
  epi_ok a (k_sh (epi_k1 a w) (sf_stage (c3_s (epi_k1 a w))) (Vint (Int.repr 1))) 1 (w_ipc w - 1) (w_opc w) (w_oc w).
Proof.
intros a w H Hg Hic Hpend Hh Hxm Hxb.
pose proof H as (Ha & CI & Hsmw & Hst & Hex & R4a & R4b & Hun).
destruct (Hex Hsmw) as (X1 & X2rl & X2f & X3 & X4).
pose proof CI as (Hip & Hop & Hloc & Hpre & Hdl & Hdlc & Hdlb & Hbc & Hbin & Hn1 & Hn2 & Hn3 &
  Hcore & Hdd & Hstout & Hahead & Hblk & Hmodel & Hlh & Hsinh & Hexp & HT).
pose proof Ha as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hipos & Hisz & Hlibs & Hbibs & _).
pose proof (epi_ss_ahead a _ Hst Hsinh) as Hssa.
pose proof (epi_hostage0 _ _ _ _ _ Hcore Hh) as Hnil.
rewrite Hnil, Zlength_nil in Hssa.
destruct (epi_pend_flush _ _ _ _ _ Hcore Hpend) as [Hfl Hstab].
assert (Hc: fp_complete (sv_fp (w_sv w)) = true) by (destruct Hic as [E|E]; auto; rewrite Hfl in E; discriminate).
assert (Hlt: a_ipos a < w_ipc w) by (apply HT; auto).
assert (Hn0: epi_n' a w = 0).
{ unfold epi_n'. destruct (epi_np a w) eqn:E; auto. apply epi_np_true in E. lia. }
assert (Hb1: Zlength (sublist (w_ipc w - 1) (w_ipc w) (a_ibs a)) = 1) by (rewrite Zlength_sublist; lia).
apply (epi_post_gen a w _ (sv_take (w_sv w) (sublist (w_ipc w - 1) (w_ipc w) (a_ibs a))) 1 (w_ipc w - 1) 1 0).
- exact Ha.
- exact CI.
- exact Hst.
- exact Hun.
- lia.
- lia.
- lia.
- left. lia.
- rewrite Hssa, Z.add_0_r. replace (w_ipc w - 1 + 1) with (w_ipc w) by lia.
  unfold epi_sin. rewrite Hnil, app_nil_r. rewrite Hnil, app_nil_r in Hsinh. rewrite Hsinh. reflexivity.
- rep_lia.
- reflexivity.
- auto.
- intros E; discriminate.
- intros _. left. auto.
- intros _; reflexivity.
- intros _ _. lia.
- intros E. exfalso. revert E. apply (epi_not_init a w 1 (w_ipc w - 1) 1 0 Ha CI).
  + unfold epi_st. simpl. rewrite Hssa, Z.add_0_r. replace (w_ipc w - 1 + 1) with (w_ipc w) by lia.
    unfold epi_sin. rewrite Hnil, app_nil_r. rewrite Hnil, app_nil_r in Hsinh. rewrite Hsinh. reflexivity.
  + intros E. lia.
- cbn [epi_k1 k_sh k_nfp k_epi sf_epi c3_with_s c3_s sf_nfp]; rewrite Hn0; unfold ZSTD_NO_FORWARD_PROGRESS_MAX; lia.
- exact Hbc.
- intros cd0 Hcd0; exact Hcd0.
- apply epi_crel; cbn [epi_k1 k_sh k_nfp k_epi sf_epi c3_with_s c3_s sf_nfp sf_stage sf_hostage sf_expOut sv_take
    sv_fp sv_pend sv_ahead].
  + exact Ha.
  + exact CI.
  + lia.
  + reflexivity.
  + rewrite Hn0. unfold ZSTD_NO_FORWARD_PROGRESS_MAX. lia.
  + left. rewrite Hn0. unfold ZSTD_NO_FORWARD_PROGRESS_MAX. lia.
  + intros _ _ _. reflexivity.
  + intros E. rewrite Hfl in E. unfold zdss_flush, zdss_loadHeader in E. lia.
  + exact Hdd.
  + rewrite Hstab. rewrite Hstab in Hcore.
    exact (c_core_take _ _ _ _ _ (epi_n' a w) (epi_ev a (w_opc w)) Hcore Hfl Hc Hb1
             ltac:(apply Forall_sublist; exact Hbibs)).
- reflexivity.
- reflexivity.
- cbn [sv_take sv_ahead]. rewrite Hb1. reflexivity.
- exists (a_sin a ++ sublist (a_ipos a) (w_ipc w - 1) (a_ibs a)). cbn [sv_take sv_ahead].
  unfold epi_sin. rewrite Hnil, app_nil_r, <- app_assoc. f_equal.
  rewrite (sublist_split (a_ipos a) (w_ipc w - 1) (w_ipc w)) by lia. reflexivity.
- left. intros Hh0. exact Hh0.
- apply epi_prog_full; auto; [discriminate|].
  rewrite Hssa, Z.add_0_r. replace (w_ipc w - 1 + 1) with (w_ipc w) by lia.
  unfold epi_sin. rewrite Hnil, app_nil_r. rewrite Hnil, app_nil_r in Hsinh. rewrite Hsinh. reflexivity.
- exact Hxm.
- intros E1 E2; apply Hg; apply epi_np_true; auto.
- exact Hxb.
Qed.

Lemma epi_vlong_inj : forall x y, 0 <= x <= Int64.max_unsigned -> 0 <= y <= Int64.max_unsigned ->
  vlong x = vlong y -> x = y.
Proof.
intros x y Hx Hy H. unfold vlong in H.
apply (f_equal (fun v => match v with Vlong i => Int64.unsigned i | _ => 0 end)) in H.
cbv beta iota in H. rewrite !Int64.unsigned_repr in H by lia. exact H.
Qed.

(* every return of the tail *)
Lemma epi_tail_ok : forall a w, epi_hyp a w -> epi_guard a w -> epi_dd_gap a w -> epi_xm a w ->
  tail_ok a (epi_k1 a w) (w_ipc w) (w_opc w) (w_oc w).
Proof.
intros a w H Hg Hgap Hxm.
pose proof H as (Ha & CI & Hsmw & Hst & Hex & R4a & R4b & Hun).
pose proof (Hex Hsmw) as (X1 & X2rl & X2f & X3 & X4).
pose proof CI as (Hip & Hop & Hloc & Hpre & Hdl & Hdlc & Hdlb & Hbc & Hbin & Hn1 & Hn2 & Hn3 &
  Hcore & Hdd & Hstout & Hahead & Hblk & Hmodel & Hlh & Hsinh & Hexp & HT).
pose proof Hcore as (_ & _ & Hsz & _).
pose proof (epi_ss_ahead a _ Hst Hsinh) as Hssa.
destruct (epi_fields a w CI Hex Hsmw) as (e & He & Her & H0 & Hne).
unfold tail_ok. exists e.
split; [exact He|]. split; [exact Her|]. split.
- intros E0. destruct (H0 E0) as (Hic & os & oe & h & Hos & Hoe & Hh & Hosr & Hoer & Hh01 & Hpo1 & Hpo2).
  assert (Hh1: h <> Int.zero -> sf_hostage (c3_s (w_k w)) = Vint (Int.repr 1)).
  { intros Hnz. rewrite Hh. destruct Hh01 as [E|E]; [contradiction|rewrite E; reflexivity]. }
  exists os, oe, h.
  split; [exact Hos|]. split; [exact Hoe|]. split; [exact Hh|]. split; [exact Hosr|]. split; [exact Hoer|].
  split; [|split; [|split; [|split]]].
  + intros Eo Hnz Hge. apply epi_path_cr; auto.
    subst oe. apply (epi_x_cr a w os); auto. rewrite <- E0. exact He.
  + intros Eo Hnz Hlt. apply epi_path_rel; auto.
    subst oe. apply (epi_x_rel a w os); auto. rewrite <- E0. exact He.
  + intros Eo Hz. rewrite Hz in Hh. pose proof (epi_hostage0 _ _ _ _ _ Hcore Hh) as Hnil.
    apply (epi_path_same a w 0 (if sf_stage (c3_s (w_k w)) =? zdss_init then 0 else epi_n' a w)); auto.
    * rep_lia.
    * intros E; contradiction.
    * intros _. split; [apply Hpo1; auto|].
      destruct Hic as [Ei|Hc]; [|left; exact Hc].
      destruct (X4 Ei) as (_ & _ & [(_ & _ & [Hc|(Hfp & Hlt)])|(H1 & _)]).
      -- left; exact Hc.
      -- right. split; [exact Hfp|]. unfold epi_sin. intro E. apply app_eq_nil in E. destruct E as [_ E].
         apply app_eq_nil in E. destruct E as [E _]. apply (f_equal (@Zlength Z)) in E.
         pose proof Ha as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hipos & _ & Hlibs & _).
         rewrite Zlength_sublist, Zlength_nil in E by lia. lia.
      -- rewrite Hh in H1. discriminate.
    * first [intros E; lia | intros _ _ Hp; exfalso; apply Hp; apply Hpo1; auto].
    * destruct (Z.eqb_spec (sf_stage (c3_s (w_k w))) zdss_init) as [Ei|Ei]; [right|left; reflexivity].
      split; [reflexivity|]. split; [exact Ei|].
      assert (Hal: ep_alive (sm_of (a_st a)) (epi_sin a w) (ss_out (dc_ss (a_st a)) ++ w_dl w) (sv_fp (w_sv w))
                     (sv_pend (w_sv w)))
        by (destruct Hmodel as [Hd|(cd & Hm & _)]; [left; exact Hd|right; exists cd; exact Hm]).
      destruct (X4 Ei) as (_ & _ & [(_ & _ & [Hc|(Hfp & Hlt)])|(H1 & _)]).
      -- exact (ep_complete_nonnil _ _ _ _ _ Hal Hc).
      -- unfold epi_sin. intro E. apply app_eq_nil in E. destruct E as [_ E].
         apply app_eq_nil in E. destruct E as [E _]. apply (f_equal (@Zlength Z)) in E.
         pose proof Ha as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hipos & _ & Hlibs & _).
         rewrite Zlength_sublist, Zlength_nil in E by lia. lia.
      -- rewrite Hh in H1. discriminate.
    * apply epi_prog_zero; auto.
    * replace (ss_ahead (dc_ss (a_st a))) with 0 by (rewrite Hssa, Hnil; reflexivity).
      subst oe. apply (epi_x_zero a w os); auto. rewrite <- E0. exact He.
  + intros Eo Hz. rewrite Hz in Hh. apply epi_path_take; auto.
    apply (epi_x_take a w os oe); auto. rewrite <- E0. exact He.
  + intros Eo Hnz. pose proof (Hh1 Hnz) as Hh'. destruct (epi_hostage1 a w H Hh') as (Hl1 & _ & _ & _).
    assert (Hne': sv_ahead (w_sv w) <> nil) by (intro E; rewrite E, Zlength_nil in Hl1; discriminate).
    apply (epi_path_same a w 1 (epi_n' a w)); auto.
    * rep_lia.
    * intros E; discriminate.
    * intros Ei. exfalso. destruct (X4 Ei) as (_ & (o & Ho1 & Ho2 & Hor) & _).
      apply Eo. rewrite Hos in Ho1. rewrite Hoe in Ho2.
      apply epi_vlong_inj in Ho1; auto. apply epi_vlong_inj in Ho2; auto. lia.
    * apply epi_prog_full; auto; [discriminate|apply epi_sin_same; auto].
    * replace (ss_ahead (dc_ss (a_st a))) with 1 by (rewrite Hssa; symmetry; exact Hl1).
      apply (epi_x_held a w os oe); auto. rewrite <- E0. exact He.
- intros Hne0. destruct (Hne Hne0) as (Hni & Hnc & fstg & ip0 & Hfst & Hfr & Hip0 & Hip0r & Hrem & Hrpos & Hrle).
  exists fstg, ip0. split; [exact Hfst|]. split; [exact Hfr|]. split; [exact Hip0|]. split; [exact Hip0r|].
  rewrite Hrem.
  assert (Hnil: sv_ahead (w_sv w) = nil).
  { destruct Hcore as (Hd & _). destruct Hd as [(Ei & _)|[(_ & A)|(_ & _ & Hc & _)]]; auto.
    - contradiction. - rewrite Hc in Hnc. discriminate. }
  assert (Hh0: sf_hostage (c3_s (w_k w)) = Vint (Int.repr 0)).
  { destruct Hcore as (Hd & _). destruct Hd as [(Ei & _)|[(Hh0 & _)|(_ & _ & Hc & _)]].
    - contradiction. - exact Hh0. - rewrite Hc in Hnc. discriminate. }
  apply (epi_path_same a w _ (epi_n' a w)); auto;
    try first [ rep_lia | (unfold is_error_code; apply Z.ltb_ge; lia) | (intros _ Hc; rewrite Hc in Hnc; discriminate)
          | (intros E; contradiction) | (intros E; lia) ].
  apply epi_prog_hint; auto. lia.
  rewrite <- Hrem. replace (ss_ahead (dc_ss (a_st a))) with 0 by (rewrite Hssa, Hnil; reflexivity).
  apply (epi_x_hint a w e fstg ip0); auto.
Qed.

(* R4a/R4b (revision R5: exit_ok X2, start_ok) *)
Lemma epi_R4ab : forall (a: dsa) (w: lw),
  dsa_ok a -> call_inv a (w_k w) (w_sv w) (w_ipc w) (w_opc w) (w_oc w) (w_dl w) -> w_smw w = 0 -> start_ok a ->
  exit_ok a w ->
  (sf_stage (c3_s (w_k w)) = zdss_flush -> sv_pend (w_sv w) <> nil) /\ 0 <= ss_stall (dc_ss (a_st a)).
Proof.
intros a w Ha CI Hsmw Hst Hex.
destruct (Hex Hsmw) as (_ & _ & X2f & _).
destruct Hst as (_ & _ & _ & Hs).
split; [intros E; exact (proj2 (X2f E))|exact Hs].
Qed.

Lemma epi_pure : forall (a: dsa) (w: lw),
  dsa_ok a -> call_inv a (w_k w) (w_sv w) (w_ipc w) (w_opc w) (w_oc w) (w_dl w) -> w_smw w = 0 -> start_ok a ->
  exit_ok a w -> epi_dd_gap a w -> untouched_ok a w -> epi_xm a w ->
  head_ok a (w_k w) (w_ipc w) (w_opc w) (w_oc w).
Proof.
intros a w Ha CI Hsmw Hst Hex Hgap Hun Hxm.
destruct (epi_R4ab a w Ha CI Hsmw Hst Hex) as [R4a R4b].
assert (H: epi_hyp a w) by exact (conj Ha (conj CI (conj Hsmw (conj Hst (conj Hex (conj R4a (conj R4b Hun))))))). 
pose proof (Hex Hsmw) as (X1 & X2rl & X2f & X3 & X4).
pose proof CI as (Hip & Hop & Hloc & Hpre & Hdl & Hdlc & Hdlb & Hbc & Hbin & Hn1 & Hn2 & Hn3 & _).
pose proof Ha as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hopos & _).
unfold head_ok.
split; [exact Hn1|]. split; [|split; [|split]].
- intros E1 E2 Hge Eo.
  assert (Hx0 := epi_x_err a w Ha CI Hxm E1 E2 ltac:(cbv zeta in *; unfold ZSTD_NO_FORWARD_PROGRESS_MAX; lia)
                   (or_introl Eo)).
  rewrite E1, E2.
  apply epi_err_ok; auto;
    first [ (destruct (X3 E1 E2); unfold ZSTD_NO_FORWARD_PROGRESS_MAX in *; lia) | (left; split; [reflexivity|lia])
          | (rewrite <- E2; exact Hpre) ].
- intros E1 E2 Hge Eo Ei.
  assert (Hx0 := epi_x_err a w Ha CI Hxm E1 E2 ltac:(cbv zeta in *; unfold ZSTD_NO_FORWARD_PROGRESS_MAX; lia)
                   (or_intror Ei)).
  rewrite E1, E2.
  apply epi_err_ok; auto;
    first [ (destruct (X3 E1 E2); unfold ZSTD_NO_FORWARD_PROGRESS_MAX in *; lia) | (right; split; [reflexivity|lia])
          | (rewrite <- E2; exact Hpre) ].
- intros E1 E2 Hnot.
  assert (Enp: epi_np a w = true) by (apply epi_np_true; auto).
  replace (k_nfp a (w_k w) (w_opc w) (sf_nfp (c3_s (w_k w)) + 1)) with (epi_k1 a w)
    by (unfold epi_k1, epi_n'; rewrite Enp; reflexivity).
  apply epi_tail_ok; auto. intros _. exact Hnot.
- intros Hp.
  assert (Enp: epi_np a w = false).
  { destruct (epi_np a w) eqn:E; auto. apply epi_np_true in E. lia. }
  replace (k_nfp a (w_k w) (w_opc w) 0) with (epi_k1 a w)
    by (unfold epi_k1, epi_n'; rewrite Enp; reflexivity).
  apply epi_tail_ok; auto. intros E. congruence.
Qed.

End CM_E3Pure_1.
