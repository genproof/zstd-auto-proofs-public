(* stream_all (harness/frames.h) on a series in which the model finds no complete frame: no call returns 0.

   A call of ZSTD_decompressStream that returns 0 has ended a frame: stream_post's claims (Params.stream_claims_m,
   the clause for r = 0) give, for every series s of bytes the bytes read so far begin, whose walk the model
   decides (its tail is not TUnk), a complete frame of s ending where the reading stopped.  The bytes a run of
   stream_all has read are always a prefix of its input s (stream_post: the bytes read before the call, then the
   call's chunk of s).  So when the model's walk over s itself finds no frame (its list is empty) and decides s
   (refused at a header, TDetHdr, or by a checksum, TDetCk), no call returns 0 and *completed stays 0.  Laws
   rj_bad_checksum, rj_reserved_bit: the stream never reports the frame complete.  stream_no_end_ext: the same with
   a decided extension of the input (rj_truncated). *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.harness.frames.FStreamSpec.

(* a prefix of a prefix: the first k bytes of s begin every extension of s *)
Lemma is_prefix_sublist0 : forall (k: Z) (s s': list Z),
  0 <= k <= Zlength s -> is_prefix s s' -> is_prefix (sublist 0 k s) s'.
Proof.
  unfold is_prefix; intros k s s' Hk Hp.
  rewrite sublist_firstn.
  assert (Hl: length (firstn (Z.to_nat k) s) = Z.to_nat k).
  { rewrite firstn_length_le; auto. rewrite Zlength_correct in Hk; lia. }
  rewrite Hl, <- Hp, firstn_firstn.
  replace (Nat.min (Z.to_nat k) (length s)) with (Z.to_nat k); auto.
  rewrite Zlength_correct in Hk; lia.
Qed.

(* the invariant of a run that has seen no 0 return: the context keeps the parameters and dictionaries of the
   start (stream_post only changes its stream state and last dictionary), and the bytes it has read are the first
   in.pos + ahead bytes of the input *)
Definition no_end_inv (s: list Z) (st: dctx_st) (x: sa_state) : Prop :=
  sa_done x = 0 /\ dc_par (sa_st x) = dc_par st /\ st_sel (sa_st x) = st_sel st /\
  0 <= sa_ipos x /\ 0 <= ss_ahead (dc_ss (sa_st x)) /\
  sa_ipos x + ss_ahead (dc_ss (sa_st x)) <= Zlength s /\
  ss_in (dc_ss (sa_st x)) = sublist 0 (sa_ipos x + ss_ahead (dc_ss (sa_st x))) s.

(* one call from a state of the invariant: it does not return 0 (stream_claims_m would give a frame of s' ending
   within the bytes read, hence within s), and the invariant holds after it *)
Lemma no_end_step : forall s s' cap dst st y r z,
  bytes_ok s' -> is_prefix s s' ->
  snd (series_frames_m (dmode_w (dmode_of (dc_par st))) (fst (st_sel st)) (snd (st_sel st)) no_wlim s') <> TUnk ->
  Forall (fun fr => Zlength s < fr_end fr)
    (fst (series_frames_m (dmode_w (dmode_of (dc_par st))) (fst (st_sel st)) (snd (st_sel st)) no_wlim s')) ->
  no_end_inv s st y -> stream_call s cap dst y r z ->
  r <> 0 /\ no_end_inv s st z.
Proof.
  intros s s' cap dst st y r z Hb Hp Ht Hf Hinv Hc.
  destruct Hinv as (Hd & Hpar & Hsel & Hip & Ha & Hle & Hin).
  destruct Hc as (isz & osz & oc' & Hisz & Hosz & Hr & Hpost & Hdone).
  (* the count of 0 returns is the last conjunct of stream_call (stage 2 (P) adds stream_progress before it) *)
  repeat match type of Hdone with _ /\ _ => destruct Hdone as [_ Hdone] end.
  assert (Hisz': isz <= Zlength s).
  { unfold sa_size in Hisz. destruct (sa_ipos y =? Zlength s); lia. }
  destruct Hpost as (dl & stall' & a' & Hpost). cbv zeta in Hpost.
  destruct Hpost as (_ & Hipos & _ & _ & _ & _ & Ha' & Hia & Hia2 & _ & Hz & _ & _ & _ & _ & Hcl).
  set (sin' := ss_in (dc_ss (sa_st y)) ++
               sublist (sa_ipos y + ss_ahead (dc_ss (sa_st y))) (sa_ipos z + a') (sublist 0 isz s)) in *.
  assert (Hend: sa_ipos z + a' <= Zlength s) by lia.
  assert (Hsin: sin' = sublist 0 (sa_ipos z + a') s).
  { subst sin'. rewrite Hin.
    destruct Hia2 as [Hia2|Hia2].
    - rewrite sublist_sublist by lia. rewrite !Z.add_0_r.
      rewrite sublist_rejoin by lia. reflexivity.
    - rewrite Hia2, sublist_nil, app_nil_r. reflexivity. }
  assert (Hr0: r <> 0).
  { intros E.
    assert (Hpre: is_prefix sin' s') by (rewrite Hsin; apply is_prefix_sublist0; auto; lia).
    (* with stage 2 (R), stream_post's last conjunct is the claims followed by stream_zero_ref *)
    first [ destruct (Hcl s' Hb Hpre) as (_ & Hc0 & _) | destruct (proj1 Hcl s' Hb Hpre) as (_ & Hc0 & _) ].
    rewrite Hpar, Hsel in Hc0.
    destruct (Hc0 E Ht) as (n & Hn & Hfe & _).
    rewrite Forall_nth in Hf.
    specialize (Hf (n - 1)%nat fr_dflt ltac:(lia)).
    rewrite Hsin, Zlength_sublist in Hfe by lia. lia. }
  split; auto.
  unfold no_end_inv. rewrite Hz; simpl.
  rewrite Hdone, Hd. rewrite (proj2 (Z.eqb_neq r 0) Hr0).
  repeat split; try lia; auto.
Qed.

Lemma no_end_run : forall s s' cap dst st x y,
  bytes_ok s' -> is_prefix s s' ->
  snd (series_frames_m (dmode_w (dmode_of (dc_par st))) (fst (st_sel st)) (snd (st_sel st)) no_wlim s') <> TUnk ->
  Forall (fun fr => Zlength s < fr_end fr)
    (fst (series_frames_m (dmode_w (dmode_of (dc_par st))) (fst (st_sel st)) (snd (st_sel st)) no_wlim s')) ->
  stream_run s cap dst x y -> no_end_inv s st x -> no_end_inv s st y.
Proof.
  intros s s' cap dst st x y Hb Hp Ht Hf Hrun Hx.
  induction Hrun as [x|x y r z Hrun IH Hc _]; auto.
  exact (proj2 (no_end_step s s' cap dst st y r z Hb Hp Ht Hf (IH Hx) Hc)).
Qed.

(* the same for a series s' that extends the input s and whose walk the model decides (TDetHdr, TDetCk or TEnd),
   every frame of which ends beyond s (rj_truncated: s a cut frame, s' the whole frame) *)
Theorem stream_no_end_ext : forall s s' cap dst st oc y r z,
  bytes_ok s' -> is_prefix s s' ->
  ss_in (dc_ss st) = nil -> ss_ahead (dc_ss st) = 0 ->
  snd (series_frames_m (dmode_w (dmode_of (dc_par st))) (fst (st_sel st)) (snd (st_sel st)) no_wlim s') <> TUnk ->
  Forall (fun fr => Zlength s < fr_end fr)
    (fst (series_frames_m (dmode_w (dmode_of (dc_par st))) (fst (st_sel st)) (snd (st_sel st)) no_wlim s')) ->
  stream_run s cap dst (sa_init st oc) y -> stream_call s cap dst y r z ->
  sa_done z = 0.
Proof.
  intros s s' cap dst st oc y r z Hb Hp Hin Ha Ht Hf Hrun Hc.
  assert (Hx: no_end_inv s st (sa_init st oc)).
  { unfold no_end_inv, sa_init; simpl. rewrite Ha, Hin, sublist_nil.
    repeat split; try lia; auto. apply Zlength_nonneg. }
  pose proof (no_end_run s s' cap dst st _ _ Hb Hp Ht Hf Hrun Hx) as Hy.
  destruct (no_end_step s s' cap dst st y r z Hb Hp Ht Hf Hy Hc) as (_ & Hz).
  apply Hz.
Qed.

(* the run from a context that has read nothing (a new context, or one after a reset), on a series s the model's
   walk decides without a complete frame, in the mode and with the dictionaries of that context *)
Theorem stream_no_end : forall s cap dst st oc y r z,
  bytes_ok s ->
  ss_in (dc_ss st) = nil -> ss_ahead (dc_ss st) = 0 ->
  fst (series_frames_m (dmode_w (dmode_of (dc_par st))) (fst (st_sel st)) (snd (st_sel st)) no_wlim s) = nil ->
  snd (series_frames_m (dmode_w (dmode_of (dc_par st))) (fst (st_sel st)) (snd (st_sel st)) no_wlim s) <> TUnk ->
  stream_run s cap dst (sa_init st oc) y -> stream_call s cap dst y r z ->
  sa_done z = 0.
Proof.
  intros s cap dst st oc y r z Hb Hin Ha Hnil Ht Hrun Hc.
  apply (stream_no_end_ext s s cap dst st oc y r z); auto.
  - unfold is_prefix. apply firstn_all.
  - rewrite Hnil. constructor.
Qed.
