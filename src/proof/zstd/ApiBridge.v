(* API v3 at zstd's default parameters, without a DDict set or a buffer-less frame: the v2 forms; for the proofs written
   against API v2. *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.zstd.Spec_api6 Zstd.proof.model.ParamsDflt.

Lemma dmode_of_dflt : dmode_of dparams_dflt = md_dflt.
Proof. reflexivity. Qed.

(* the v2 form, without v3's claim on a refused series (Refuse.series_refused_m) *)
Lemma oneshot_ok_dflt (odm: option dict_model) (s: list Z) (cap r: Z) (out: list val) :
  oneshot_ok md_dflt odm s cap r out -> oneshot_ok2 odm s cap r out.
Proof.
  unfold oneshot_ok, oneshot_ok2. destruct odm as [dm|]; [|tauto].
  rewrite decode_series_m_dflt. intros [H1 H2]. split; [exact H1 |].
  destruct (decode_series dm no_wlim s); auto.
Qed.

Lemma st_sel_nil (st: dctx_st) :
  dc_set st = nil -> st_sel st = (sel_none, dictref_model (dc_dict st)).
Proof. intros H. unfold st_sel. rewrite H. reflexivity. Qed.

Lemma set_res_nil (DD: globals -> val -> ddict_st -> mpred) (gv: globals) (sh: share) (cur: option dictref) :
  set_res DD gv sh nil cur = emp.
Proof. reflexivity. Qed.

Lemma oneshot_dm_nil (st: dctx_st) (dm: option dict_model) :
  dc_set st = nil -> oneshot_dm st dm = dm.
Proof. intros H. unfold oneshot_dm. rewrite H. reflexivity. Qed.

(* ---------- v3.1 ---------- *)
Require Import Zstd.proof.model.ParamsW.

Lemma oneshot_dctx_nil (st: dctx_st) (s: list Z) (cap r: Z) (out: list val) :
  dc_set st = nil ->
  (oneshot_dctx st s cap r out <-> oneshot_ok (dmode_of (dc_par st)) (dictref_model (dc_dict st)) s cap r out).
Proof. intros H. unfold oneshot_dctx. rewrite H. tauto. Qed.

(* streaming without a dictionary at the default parameters: the v2 claims *)
Lemma stream_alive_v3_dflt (st: dctx_st) (sin: list Z) :
  dc_par st = dparams_dflt -> dc_set st = nil -> dc_dict st = None ->
  (stream_alive_m (dmode_w (dmode_of (dc_par st))) (fst (st_sel st)) (snd (st_sel st)) sin <-> stream_alive sin).
Proof.
  intros Hp Hs Hd. rewrite (st_sel_nil st Hs), Hd, Hp, dmode_of_dflt. simpl fst. simpl snd.
  rewrite <- stream_alive_m_dflt. unfold stream_alive_m.
  split; intros [s0 [H1 [H2 H3]]]; exists s0; repeat split; auto;
  rewrite ?series_frames_m_w_nodict in *; auto.
Qed.

Lemma stream_claims_v3_dflt (st: dctx_st) (sin0 sout0 sin sall sout: list Z) (a1: Z) (ocap: option Z) (r: Z) :
  dc_par st = dparams_dflt -> dc_set st = nil -> dc_dict st = None ->
  (stream_claims_m (dmode_w (dmode_of (dc_par st))) (fst (st_sel st)) (snd (st_sel st)) (dp_wmax (dc_par st))
     sin0 sout0 sin sall sout a1 ocap r <-> stream_claims sin0 sout0 sin sall sout a1 ocap r).
Proof.
  intros Hp Hs Hd. rewrite (st_sel_nil st Hs), Hd, Hp, dmode_of_dflt. simpl fst. simpl snd.
  change (dp_wmax dparams_dflt) with stream_wlim.
  rewrite <- stream_claims_m_dflt. unfold stream_claims_m.
  split; intros H s0 Hb Hpre; specialize (H s0 Hb Hpre);
  rewrite ?series_frames_m_w_nodict in *; exact H.
Qed.
