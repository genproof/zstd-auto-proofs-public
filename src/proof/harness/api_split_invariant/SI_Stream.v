(* api_split_invariant (harness/api_split_invariant.c): how stream_all ends on a series the model decodes.

   stream_all's specification (frames/FStreamSpec.v) is the trace of its calls of ZSTD_decompressStream: a run
   from the start to y, then the last call y -> z (result r), after which the loop stops.  Here the context
   starts a fresh stream (no dictionary, no DDict set, buffered output) and the series s (not empty) decodes to
   c under the stream's model, without a window limit and with the context's own (windowLogMax).  Then the
   stream ends in one of three ways:
   - zstd runs out of memory (ZSTD_error_memory_allocation: the harness stops);
   - the capacity is below the content and the last call does not return 0;
   - the last call returns 0, having delivered exactly c into dst[0 .. |c|).
   Why (each call's stream_post and stream_progress, by induction on the run): the bytes read are a prefix of s,
   those delivered a prefix of c, and zstd's count of calls without progress stays 0 (every call the loop goes
   on after made progress, or returned 0 with input left); so an error can only be memory
   (stream_error_memory); a 0 return with all of s read has delivered all of c (stream_claims_m's zero clause);
   a positive return without progress has the output full while c is not all delivered, since everything read
   and delivered already before the call is excluded (the call before it would have returned 0 and the loop
   would have stopped there, as its hint clause shows). *)
Require Import VST.floyd.proofauto.
Require Export Zstd.proof.harness.frames.FStreamSpec.

Definition si_stream_stmt : Prop := forall s c cap dst st oc y r z,
  dc_ss st = ss_init -> dc_stable st = false -> dc_set st = nil -> dc_dict st = None ->
  bytes_ok s -> s <> [] -> 0 <= cap -> Zlength oc = cap ->
  decode_series_m (dmode_w (dmode_of (dc_par st))) sel_none (Some no_dict) no_wlim s = SOk c ->
  decode_series_m (dmode_w (dmode_of (dc_par st))) sel_none (Some no_dict) (dp_wmax (dc_par st)) s = SOk c ->
  stream_run s cap dst (sa_init st oc) y -> stream_call s cap dst y r z -> ~ stream_more (Zlength s) y r z ->
  r = 2 ^ 64 - ZSTD_error_memory_allocation \/
  (cap < Zlength c /\ r <> 0) \/
  (r = 0 /\ sa_opos z = Zlength c /\ Zlength c <= cap /\ sublist 0 (Zlength c) (sa_out z) = zbytes c).

(* model facts on walks (plain Coq, independent of the API specifications) *)
Require Zstd.proof.dec.v3.FS.stream.epi.E3Hint Zstd.proof.dec.v3.FS.stream.epi.content.EC3Walk.
Require Zstd.proof.dec.v3.FS.stream.epi.content.EC3Base.
Module E3Hint := Zstd.proof.dec.v3.FS.stream.epi.E3Hint.
Module EC3Walk := Zstd.proof.dec.v3.FS.stream.epi.content.EC3Walk.
Module EC3Base := Zstd.proof.dec.v3.FS.stream.epi.content.EC3Base.

(* ---------- the frames of a series the model decodes to its end ---------- *)

(* every frame of a walk ends after the walk's start offset (a frame has at least one byte) *)
Lemma si_walk_after : forall md sel f cur w s off l t, walk_m f md sel cur w s off = (l, t) -> t <> TUnk ->
  forall x, In x l -> off < fr_end x.
Proof.
  intros md sel. induction f; intros cur w s off l t H Ht x Hx. { simpl in H. inversion H; subst. destruct Hx. }
  rewrite EC3Walk.walk_S in H. destruct (EC3Walk.wfirst md sel cur w s) as [[[[k c] sk] cur']|t'] eqn:E.
  - destruct (walk_m f md sel cur' w (skipn (Z.to_nat k) s) (off + k)) as [l0 t0] eqn:E2.
    inversion H; subst; clear H.
    assert (Hk: Z.to_nat k <> 0%nat).
    { intro Hk. pose proof (EC3Walk.walk_loop md sel cur w s k c sk cur' E Hk f (off + k)). rewrite Hk in E2.
      simpl in E2. rewrite E2 in H. simpl in H. congruence. }
    destruct Hx as [<-|Hx].
    + unfold fr_end, EC3Walk.mkrec. simpl. lia.
    + specialize (IHf _ _ _ _ _ _ E2 Ht x Hx). lia.
  - inversion H; subst. destruct Hx.
Qed.

(* in a walk that reaches the end of its bytes, a frame that ends at their end is the last one *)
Lemma si_walk_last : forall md sel f cur w s off l, walk_m f md sel cur w s off = (l, TEnd) -> bytes_ok s ->
  forall n, (1 <= n <= length l)%nat -> fr_end (nth (n - 1) l fr_dflt) = off + Zlength s -> n = length l.
Proof.
  intros md sel. induction f; intros cur w s off l H Hb n Hn He; [discriminate|].
  rewrite EC3Walk.walk_S in H. destruct (EC3Walk.wfirst md sel cur w s) as [[[[k c] sk] cur']|t'] eqn:E.
  - destruct (walk_m f md sel cur' w (skipn (Z.to_nat k) s) (off + k)) as [l0 t0] eqn:E2.
    inversion H; subst; clear H.
    destruct (EC3Walk.wfirst_ext md sel cur w s k c sk cur' nil E Hb) as [Hkl _].
    assert (Hk: Z.to_nat k <> 0%nat).
    { intro Hk. pose proof (EC3Walk.walk_loop md sel cur w s k c sk cur' E Hk f (off + k)). rewrite Hk in E2.
      simpl in E2. rewrite E2 in H. simpl in H. congruence. }
    pose proof (Zlength_nonneg s).
    assert (Hsk: Zlength (skipn (Z.to_nat k) s) = Zlength s - k) by (apply EC3Base.Zlength_skipn; lia).
    destruct n as [|n]; [lia|]. destruct n as [|n].
    + simpl in He. unfold fr_end, EC3Walk.mkrec in He. simpl in He.
      destruct l0 as [|x l0]; [reflexivity|]. exfalso.
      pose proof (si_walk_after _ _ _ _ _ _ _ _ _ E2 ltac:(discriminate) x (or_introl eq_refl)).
      pose proof (E3Hint.eh3_walk_ends _ _ _ _ _ _ _ _ _ E2 ltac:(discriminate) (EC3Base.bytes_ok_skipn _ _ Hb) x
                    (or_introl eq_refl)). lia.
    + simpl in Hn, He |- *.
      assert (IH := IHf _ _ _ _ _ E2 (EC3Base.bytes_ok_skipn _ _ Hb) (S n) ltac:(lia)).
      simpl in IH. rewrite Nat.sub_0_r in IH. rewrite IH; [reflexivity|]. rewrite He, Hsk. lia.
  - inversion H; subst. simpl in Hn. lia.
Qed.

(* the current frame's end, once all bytes are read and all content delivered: the default *)
Lemma si_cur_end_all : forall fl ipos got cacc dflt, (forall x, In x fl -> fr_end x <= ipos) ->
  cacc + Zlength (flat_map fr_content fl) <= got -> cur_end_aux fl ipos got cacc dflt = dflt.
Proof.
  induction fl as [|f fl IH]; intros ipos got cacc dflt Hin Hc; simpl; [reflexivity|].
  simpl in Hc. rewrite Zlength_app in Hc. pose proof (Zlength_nonneg (flat_map fr_content fl)).
  pose proof (Hin f (or_introl eq_refl)).
  replace (fr_end f >? ipos) with false by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
  replace (got <? cacc + Zlength (fr_content f)) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite andb_false_r. simpl. apply IH; [intros; apply Hin; right; auto | lia].
Qed.

(* ---------- prefixes ---------- *)

Lemma si_prefix_sub : forall (s: list Z) k, 0 <= k <= Zlength s -> is_prefix (sublist 0 k s) s.
Proof.
  intros s k Hk. unfold is_prefix. rewrite sublist_firstn, firstn_length_le by (rewrite Zlength_correct in Hk; lia).
  reflexivity.
Qed.

Lemma si_prefix_len : forall (p l: list Z), is_prefix p l -> Zlength p <= Zlength l.
Proof.
  unfold is_prefix. intros p l H. rewrite <- H, !Zlength_correct, firstn_length. lia.
Qed.

Lemma si_prefix_full : forall (p l: list Z), is_prefix p l -> Zlength l <= Zlength p -> p = l.
Proof.
  unfold is_prefix. intros p l H Hl. rewrite <- H. apply firstn_all2. rewrite !Zlength_correct in Hl. lia.
Qed.

(* ---------- the state of the stream along stream_all's calls ---------- *)

(* before each call on the series s (content c), from a fresh stream in the state st: the context keeps st's
   parameters, no dictionary and buffered output; zstd has read s[0, in.pos + a) (a the hostage byte), delivered
   ss_out = dst[0, out.pos), a prefix of c *)
Definition si_inv (s c: list Z) (cap: Z) (st: dctx_st) (x: sa_state) : Prop :=
  let ss := dc_ss (sa_st x) in
  dc_par (sa_st x) = dc_par st /\ dc_set (sa_st x) = nil /\ dc_dict (sa_st x) = None /\
  dc_stable (sa_st x) = false /\
  0 <= ss_ahead ss <= 1 /\ 0 <= sa_ipos x /\ sa_ipos x + ss_ahead ss <= Zlength s /\
  ss_in ss = sublist 0 (sa_ipos x + ss_ahead ss) s /\
  0 <= sa_opos x <= cap /\ Zlength (sa_out x) = cap /\ Zlength (ss_out ss) = sa_opos x /\
  sublist 0 (sa_opos x) (sa_out x) = zbytes (ss_out ss) /\ is_prefix (ss_out ss) c.

(* open one call x -> y on si_inv x: stream_call's sizes, stream_post's clauses (the bytes read as a prefix of s),
   stream_progress; Hpost0 keeps stream_post whole *)
Ltac si_open s cap x y Hinv Hcall :=
  destruct Hcall as (isz & osz & oc' & Hisz & Hosz & Hr & Hpost & Hprog & Hout & Hdone);
  pose proof Hpost as Hpost0;
  destruct Hinv as (Hpar & Hset & Hdict & Hstab & Ha & Hip & Hipl & Hin & Hop & Hol & Hsol & Hcells & Hpre);
  destruct Hpost as (dl & stall' & a' & Hp); cbv zeta in Hp;
  destruct Hp as (Ho & Hi & Hoc' & Hsub & Hdl & Halive & Ha' & Hia & Hia2 & Hhost & Hst' & Hpr & Hnp & Hbsm & Hstok & Hcl & Hzref);
  unfold stream_progress in Hprog; rewrite Hst' in Hprog;
  cbn [set_last set_ss dc_ss ss_in ss_out ss_ahead ss_stall] in Hprog;
  assert (Hsel: st_sel (sa_st x) = (sel_none, Some no_dict)) by (unfold st_sel; rewrite Hset, Hdict; reflexivity);
  rewrite Hsel, Hpar, Hstab in *; cbn [fst snd] in *;
  unfold sa_size in Hisz, Hosz;
  assert (Hisz': sa_ipos x + ss_ahead (dc_ss (sa_st x)) <= isz <= Zlength s)
    by (destruct (Z.eqb_spec (sa_ipos x) (Zlength s)); lia);
  assert (Hosz': sa_opos x <= osz <= cap)
    by (destruct (Z.eqb_spec (sa_opos x) cap); lia);
  assert (Hle: sa_ipos y + a' <= isz) by lia;
  assert (Hsin: ss_in (dc_ss (sa_st x)) ++ sublist (sa_ipos x + ss_ahead (dc_ss (sa_st x))) (sa_ipos y + a')
                  (sublist 0 isz s) = sublist 0 (sa_ipos y + a') s) by (rewrite Hin; list_solve);
  rewrite Hsin in *.

(* every call keeps si_inv: stream_post on the series s, which extends all the bytes read *)
Lemma si_call : forall s c cap dst st x r y fl0,
  bytes_ok s ->
  series_frames_m (dmode_w (dmode_of (dc_par st))) sel_none (Some no_dict) no_wlim s = (fl0, TEnd) ->
  c = flat_map fr_content fl0 ->
  si_inv s c cap st x -> stream_call s cap dst x r y -> si_inv s c cap st y.
Proof.
  intros s c cap dst st x r y fl0 Hb Hs0 Hc Hinv Hcall.
  si_open s cap x y Hinv Hcall.
  assert (Hpfx: is_prefix (sublist 0 (sa_ipos y + a') s) s) by (apply si_prefix_sub; lia).
  destruct (Halive (or_intror (ex_intro _ s (conj Hb (conj Hpfx (or_introl (f_equal snd Hs0))))))) as [Hdel Hdlb].
  destruct (Hcl s Hb Hpfx) as (Hc1 & _ & _ & _). rewrite Hs0 in Hc1. cbn [fst snd] in Hc1.
  specialize (Hc1 (or_introl eq_refl)). rewrite <- Hc in Hc1.
  unfold si_inv. rewrite Hst'. cbn [set_last set_ss dc_ss dc_par dc_set dc_dict dc_stable ss_in ss_out ss_ahead].
  rewrite Hout.
  split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [auto|]. split; [lia|]. split; [list_solve|]. split; [list_solve|]. split; [|auto].
  rewrite map_app, <- Hdel, <- Hcells.
  rewrite (sublist_split 0 (sa_opos x) (sa_opos y)) by list_solve. f_equal; [|list_solve].
  rewrite sublist_app1 by list_solve. rewrite Hsub. list_solve.
Qed.

(* between the calls of the run: besides si_inv, no error, no call without progress counted, and not everything
   of s read and all of c delivered (the call that got there returned 0 by its hint clause, and the loop
   stopped after it) *)
Definition si_run_inv (s c: list Z) (cap: Z) (st: dctx_st) (x: sa_state) : Prop :=
  si_inv s c cap st x /\ ss_err (dc_ss (sa_st x)) = false /\ ss_stall (dc_ss (sa_st x)) = 0 /\
  ~ (sa_ipos x = Zlength s /\ Zlength c <= Zlength (ss_out (dc_ss (sa_st x)))).

Lemma si_more : forall s c cap dst st x r y fl0,
  bytes_ok s ->
  series_frames_m (dmode_w (dmode_of (dc_par st))) sel_none (Some no_dict) no_wlim s = (fl0, TEnd) ->
  c = flat_map fr_content fl0 ->
  si_run_inv s c cap st x -> stream_call s cap dst x r y -> stream_more (Zlength s) x r y ->
  si_run_inv s c cap st y.
Proof.
  intros s c cap dst st x r y fl0 Hb Hs0 Hc Hrun Hcall Hmore.
  destruct Hrun as (Hinv & Herr & Hstall & HJ).
  pose proof (si_call s c cap dst st x r y fl0 Hb Hs0 Hc Hinv Hcall) as Hy.
  si_open s cap x y Hinv Hcall.
  destruct Hmore as (Hne & Hm).
  split; [exact Hy|]. rewrite Hst'. cbn [set_last set_ss dc_ss ss_err ss_stall ss_out].
  split; [exact Hne|]. split.
  - destruct (Z.eqb_spec r 0) as [E|E].
    + destruct (Z.eq_dec (sa_ipos y) (sa_ipos x)) as [Ei|Ei]; [|apply Hpr; auto].
      destruct (Z.eq_dec (sa_opos y) (sa_opos x)) as [Eo|Eo]; [|apply Hpr; auto].
      destruct (Hprog Hne Ei Eo) as [H0 _]. destruct (H0 E) as [H1|H1]; [|exact H1].
      exfalso. destruct (Z.eqb_spec (sa_ipos x) (Zlength s)); lia.
    + apply Hpr; auto.
  - intros [Hiy Hcy].
    assert (Hpfx: is_prefix (sublist 0 (sa_ipos y + a') s) s) by (apply si_prefix_sub; lia).
    destruct (Hcl s Hb Hpfx) as (Hc1 & _ & Hh & _). rewrite Hs0 in Hc1, Hh. cbn [fst snd] in Hc1, Hh.
    specialize (Hc1 (or_introl eq_refl)). rewrite <- Hc in Hc1, Hh.
    assert (Ea: a' = 0) by lia. subst a'.
    destruct (Z.eqb_spec r 0) as [E|E]; [lia|].
    assert (Hl0: Zlength (sublist 0 (Zlength (ss_in (dc_ss (sa_st x))) - ss_ahead (dc_ss (sa_st x)))
                           (ss_in (dc_ss (sa_st x)))) = sa_ipos x) by (rewrite Hin; list_solve).
    rewrite Hl0 in Hh.
    assert (Hlc: Zlength (ss_out (dc_ss (sa_st x)) ++ dl) = Zlength c).
    { pose proof (si_prefix_len _ _ Hc1). lia. }
    rewrite Hlc in Hh. rewrite Zlength_sublist in Hh by lia. rewrite Hiy in Hh.
    replace (Zlength s + 0 - 0) with (Zlength s) in Hh by lia.
    rewrite Z.ltb_irrefl in Hh. cbn [orb] in Hh.
    assert (Hce: cur_end fl0 (Zlength s) (Zlength c) (Zlength s) = Zlength s).
    { unfold cur_end. apply si_cur_end_all; [|subst c; lia].
      intros f Hf. unfold series_frames_m in Hs0.
      pose proof (E3Hint.eh3_walk_ends _ _ _ _ _ _ _ _ _ Hs0 ltac:(discriminate) Hb f Hf). lia. }
    rewrite Hce in Hh.
    assert (Hx: sa_ipos x < Zlength s \/ Zlength (ss_out (dc_ss (sa_st x))) < Zlength c).
    { destruct (Z.eq_dec (sa_ipos x) (Zlength s)) as [Ex|Ex]; [right|left; lia].
      destruct (Z_lt_le_dec (Zlength (ss_out (dc_ss (sa_st x)))) (Zlength c)); [auto|]. exfalso; apply HJ; auto. }
    specialize (Hh (or_introl eq_refl) Hne ltac:(lia) Hx). rewrite Z.ltb_irrefl in Hh. lia.
Qed.

Lemma si_run : forall s c cap dst st x y fl0,
  bytes_ok s ->
  series_frames_m (dmode_w (dmode_of (dc_par st))) sel_none (Some no_dict) no_wlim s = (fl0, TEnd) ->
  c = flat_map fr_content fl0 ->
  stream_run s cap dst x y -> si_run_inv s c cap st x -> si_run_inv s c cap st y.
Proof.
  intros s c cap dst st x y fl0 Hb Hs0 Hc Hrun. induction Hrun as [x|x y r z Hrun IH Hcall Hmore]; intros Hx; auto.
  apply (si_more s c cap dst st y r z fl0 Hb Hs0 Hc (IH Hx) Hcall Hmore).
Qed.

Lemma si_stream : si_stream_stmt.
Proof.
  intros s c cap dst st oc y r z Hss Hstb Hset0 Hdict0 Hb Hne Hcap Hoc Hd0 Hd1 Hrun Hcall Hstop.
  unfold decode_series_m in Hd0, Hd1.
  destruct (series_frames_m (dmode_w (dmode_of (dc_par st))) sel_none (Some no_dict) no_wlim s) as [fl0 t0] eqn:Hs0.
  destruct t0; try discriminate. injection Hd0 as Hc.
  destruct (series_frames_m (dmode_w (dmode_of (dc_par st))) sel_none (Some no_dict) (dp_wmax (dc_par st)) s)
    as [fl1 t1] eqn:Hs1.
  destruct t1; try discriminate. injection Hd1 as Hc1. symmetry in Hc, Hc1.
  assert (Hlen: 0 < Zlength s) by (destruct s; [congruence|rewrite Zlength_cons; pose proof (Zlength_nonneg s); lia]).
  assert (Hx0: si_run_inv s c cap st (sa_init st oc)).
  { unfold si_run_inv, si_inv, sa_init. cbn [sa_st sa_ipos sa_opos sa_out]. rewrite Hss. unfold ss_init.
    cbn [ss_in ss_out ss_ahead ss_err ss_stall].
    rewrite Hstb, Hset0, Hdict0. repeat split; try lia; try reflexivity; try list_solve. }
  destruct (si_run s c cap dst st _ y fl0 Hb Hs0 Hc Hrun Hx0) as (Hinv & Herr & Hstall & HJ).
  pose proof (si_call s c cap dst st y r z fl0 Hb Hs0 Hc Hinv Hcall) as Hz.
  si_open s cap y z Hinv Hcall.
  assert (Hpfx: is_prefix (sublist 0 (sa_ipos z + a') s) s) by (apply si_prefix_sub; lia).
  assert (Hsall: sublist 0 (sa_ipos z + a') s ++ sublist (sa_ipos z + a') isz (sublist 0 isz s) = sublist 0 isz s)
    by list_solve.
  assert (Hpfx': is_prefix (sublist 0 isz s) s) by (apply si_prefix_sub; lia).
  destruct (is_error_code r) eqn:Hrerr.
  - (* an error: only memory, as zstd counted no call without progress *)
    left. apply (stream_error_memory _ _ r dst osz (sa_opos y) (sa_opos z) _ oc' (sublist 0 isz s) isz (sa_ipos y)
      (sa_ipos z) s Hpost0); auto.
    + rewrite Hstall. unfold ZSTD_NO_FORWARD_PROGRESS_MAX. lia.
    + rewrite Hst'. cbn [set_last set_ss dc_ss ss_in ss_ahead]. rewrite Hsall. exact Hpfx'.
    + rewrite Hsel, Hpar. cbn [fst snd]. rewrite Hs1. reflexivity.
  - destruct (Z.eqb_spec r 0) as [E0|E0].
    + (* 0 with all of s read: the last frame ends there, all of c is delivered *)
      right; right.
      assert (Hiz: Zlength s <= sa_ipos z).
      { destruct (Z_lt_le_dec (sa_ipos z) (Zlength s)) as [Hl|Hl]; [|exact Hl]. exfalso. apply Hstop.
        unfold stream_more. rewrite Hrerr, E0. cbn. auto. }
      assert (Ea: a' = 0) by (destruct (Z.eq_dec a' 1) as [E1|E1]; [specialize (Hhost E1 eq_refl); lia|lia]).
      subst a'.
      destruct (Hcl s Hb Hpfx) as (_ & Hz0 & _ & _). rewrite Hs0 in Hz0. cbn [fst snd] in Hz0.
      destruct (Hz0 E0 ltac:(discriminate)) as (n & Hn & Hend & Hout').
      rewrite Zlength_sublist in Hend by lia.
      unfold series_frames_m in Hs0.
      assert (En: n = length fl0) by (apply (si_walk_last _ _ _ _ _ _ _ _ Hs0 Hb n Hn); lia).
      rewrite En, firstn_all, <- Hc in Hout'.
      destruct Hz as (_ & _ & _ & _ & _ & _ & _ & _ & Hop' & _ & Hsol' & Hcells' & _).
      rewrite Hst' in Hsol', Hcells'. cbn [set_last set_ss dc_ss ss_out] in Hsol', Hcells'.
      rewrite Hout' in Hsol', Hcells'. rewrite Hsol'. split; [exact E0|]. split; [reflexivity|]. split; [lia|].
      exact Hcells'.
    + (* positive without progress: the output is full and c not all delivered *)
      assert (Hip': sa_ipos z = sa_ipos y /\ sa_opos z = sa_opos y).
      { destruct (Z.eq_dec (sa_ipos z) (sa_ipos y)) as [Ei|Ei];
          [destruct (Z.eq_dec (sa_opos z) (sa_opos y)) as [Eo|Eo]; [auto|]|];
          exfalso; apply Hstop; unfold stream_more; rewrite Hrerr;
          replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; auto); auto. }
      destruct Hip' as [Ei Eo].
      destruct (Hprog Hrerr Ei Eo) as [_ Hp2]. destruct (Hp2 E0) as [_ Hall].
      rewrite Hsall in Hall. specialize (Hall s Hb Hpfx'). rewrite Hs1 in Hall. cbn [fst snd] in Hall.
      rewrite <- Hc1 in Hall. destruct (Hall eq_refl) as [[Hf Hlt]|[Hf [Hlt|[Hl1 Hl2]]]].
      * right; left. split; [|exact E0].
        assert (sa_opos y = cap) by (destruct (Z.eqb_spec (sa_opos y) cap); lia). lia.
      * exfalso. rewrite Zlength_sublist in Hlt by lia.
        destruct (Z.eqb_spec (sa_ipos y) (Zlength s)); lia.
      * exfalso. apply HJ. split; [|exact Hl2].
        rewrite Hin, Zlength_sublist in Hl1 by lia. lia.
Qed.
