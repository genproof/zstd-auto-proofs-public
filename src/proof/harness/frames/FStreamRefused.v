(* stream_all (harness/frames.h) on a series zstd certainly refuses, with no complete frame before the refused
   one: no call returns 0.

   A call of ZSTD_decompressStream that returns 0 on a refused series has ended a frame before the refused one
   (stream_post's last claim, Refuse.stream_zero_ref, for every series of bytes that the bytes read so far
   begin).  The bytes a run of stream_all has read are always a prefix of its input s (stream_post: the bytes
   read before the call, then the call's chunk of s).  So when s itself is refused and the model's walk over s
   finds no frame before the refused one (its list is empty), no call returns 0 and *completed stays 0.  Laws
   rj_reserved_block (a block of type 3), rj_truncated, rj_content_size: the stream never reports the frame
   complete. *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.harness.frames.FStreamSpec.

(* the bytes of s before position k begin s *)
Lemma sr_prefix_sublist: forall (s: list Z) k, 0 <= k <= Zlength s -> is_prefix (sublist 0 k s) s.
Proof.
  intros s k Hk. unfold is_prefix.
  rewrite <- ZtoNat_Zlength, Zlength_sublist by lia. rewrite sublist_firstn. f_equal. lia.
Qed.

(* the state of the loop between two calls on s, when the run started from st with nothing read: no call has
   returned 0, the context keeps st's parameters and dictionaries, and the bytes it has read (with a hostage
   byte read ahead) are the first in.pos + ahead bytes of s *)
Definition sr_inv (s: list Z) (st: dctx_st) (x: sa_state) : Prop :=
  sa_done x = 0 /\ dc_par (sa_st x) = dc_par st /\ st_sel (sa_st x) = st_sel st /\
  0 <= sa_ipos x /\ 0 <= ss_ahead (dc_ss (sa_st x)) /\
  sa_ipos x + ss_ahead (dc_ss (sa_st x)) <= Zlength s /\
  ss_in (dc_ss (sa_st x)) = sublist 0 (sa_ipos x + ss_ahead (dc_ss (sa_st x))) s.

(* one call keeps the invariant and does not return 0: the bytes read after it still begin s, which the model
   refuses with no frame before the refused one, so stream_zero_ref rules a return of 0 out *)
Lemma sr_step: forall s cap dst st x r y,
  bytes_ok s ->
  series_refused_m (dmode_w (dmode_of (dc_par st))) (fst (st_sel st)) (snd (st_sel st)) no_wlim s ->
  fst (series_frames_m (dmode_w (dmode_of (dc_par st))) (fst (st_sel st)) (snd (st_sel st)) no_wlim s) = nil ->
  sr_inv s st x -> stream_call s cap dst x r y -> r <> 0 /\ sr_inv s st y.
Proof.
  intros s cap dst st x r y Hb Href Hnil (Hd & Hpar & Hsel & Hi0 & Ha0 & Hle & Hin) Hc.
  destruct Hc as (isz & osz & oc' & Hisz & _ & _ & Hp & Hrest).
  (* the count of 0 returns is stream_call's last conjunct (after the output cells and, with the progress
     claim, stream_progress) *)
  assert (Hdy: sa_done y = sa_done x + (if r =? 0 then 1 else 0)) by (clear - Hrest; tauto).
  clear Hrest.
  assert (Hisz': sa_ipos x <= isz <= Zlength s).
  { unfold sa_size in Hisz. destruct (Z.eqb_spec (sa_ipos x) (Zlength s)); lia. }
  destruct Hp as (dl & stall' & a' & Hp). cbv zeta in Hp.
  destruct Hp as (_ & Hip & _ & _ & _ & _ & Ha' & Hia & Hia' & _ & Hst' & _ & _ & _ & _ & _ & Hz).
  set (sin' := ss_in (dc_ss (sa_st x)) ++
         sublist (sa_ipos x + ss_ahead (dc_ss (sa_st x))) (sa_ipos y + a') (sublist 0 isz s)) in *.
  assert (Hk: sa_ipos y + a' <= Zlength s) by lia.
  assert (Hs': sin' = sublist 0 (sa_ipos y + a') s).
  { unfold sin'. rewrite Hin. destruct Hia' as [H|H].
    - rewrite sublist_sublist0 by lia. apply sublist_rejoin; lia.
    - rewrite H, sublist_nil, app_nil_r. reflexivity. }
  rewrite Hpar, Hsel in Hz. fold sin' in Hz.
  assert (Hr: r <> 0).
  { intro E. rewrite Hs' in Hz.
    destruct (Hz s Hb (sr_prefix_sublist s (sa_ipos y + a') ltac:(lia)) Href E) as (n & Hn & _).
    rewrite Hnil in Hn. simpl in Hn. lia. }
  split; [exact Hr|].
  unfold sr_inv. rewrite Hst'. cbn [set_last set_ss dc_ss dc_par ss_in ss_ahead].
  assert (Hsel': forall ss, st_sel (set_last (set_ss (sa_st x) ss) (Some stream_mark)) = st_sel (sa_st x))
    by reflexivity.
  rewrite Hsel', Hsel. rewrite Hdy, Hd. apply Z.eqb_neq in Hr. rewrite Hr.
  repeat split; try lia; assumption.
Qed.

(* the run from a context that has read nothing (a new context, or one after a reset), on a series s refused
   in the mode and with the dictionaries of that context, without a frame before the refused one *)
Theorem stream_refused_no_end : forall s cap dst st oc y r z,
  bytes_ok s ->
  ss_in (dc_ss st) = nil -> ss_ahead (dc_ss st) = 0 ->
  series_refused_m (dmode_w (dmode_of (dc_par st))) (fst (st_sel st)) (snd (st_sel st)) no_wlim s ->
  fst (series_frames_m (dmode_w (dmode_of (dc_par st))) (fst (st_sel st)) (snd (st_sel st)) no_wlim s) = nil ->
  stream_run s cap dst (sa_init st oc) y -> stream_call s cap dst y r z ->
  sa_done z = 0.
Proof.
  intros s cap dst st oc y r z Hb Hin0 Ha0 Href Hnil Hrun Hc.
  assert (Hy: sr_inv s st y).
  { clear Hc. remember (sa_init st oc) as x eqn:Ex.
    induction Hrun as [x|x y0 r0 z0 Hrun IH Hc0 _].
    - subst x. unfold sr_inv, sa_init. cbn [sa_done sa_st sa_ipos].
      rewrite Hin0, Ha0. rewrite sublist_nil.
      repeat split; try reflexivity; try lia. apply Zlength_nonneg.
    - exact (proj2 (sr_step s cap dst st y0 r0 z0 Hb Href Hnil (IH Ex) Hc0)). }
  destruct (sr_step s cap dst st y r z Hb Href Hnil Hy Hc) as (_ & Hz & _). exact Hz.
Qed.
