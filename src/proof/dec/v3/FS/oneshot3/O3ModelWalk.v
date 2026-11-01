(* FS3 one-shot: model facts relating the claims of ZSTD_decompress_usingDDict (internal) to the
   API's oneshot_dctx (Spec_api6 v3.3): the walk over a series (Params.walk_m) does not depend on the current
   dictionary or the selection once a less informed walk (cur = None, or the empty selection) decides it; nor
   does the refusal of a series (Refuse.walk_refused), which follows the same walk. *)
Require Import Zstd.proof.dec.v3.FS.FSOblig3 Zstd.proof.dec.v3.FS.frames.Frames3SeriesRef.

Section CM_O3ModelWalk_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* ---------- the Dictionary_ID of a parsed header is a 32-bit value (local copies of body_frame.v's) ---------- *)

Lemma o3w_le_value_bound: forall l, bytes_ok l -> 0 <= le_value l < 2 ^ (8 * Z.of_nat (length l)).
Proof.
  induction l; intros H; cbn [le_value length]. simpl. lia.
  inversion H; subst. unfold is_byte in *. destruct (IHl H3).
  replace (8 * Z.of_nat (S (length l))) with (8 + 8 * Z.of_nat (length l)) by lia.
  rewrite Z.pow_add_r by lia. change (2^8) with 256. nia.
Qed.

Lemma o3w_Forall_firstn: forall (P: Z -> Prop) n l, Forall P l -> Forall P (firstn n l).
Proof. induction n; intros; destruct l; simpl; auto. inversion H; subst; auto. Qed.

Lemma o3w_Forall_skipn: forall (P: Z -> Prop) n l, Forall P l -> Forall P (skipn n l).
Proof. induction n; intros; destruct l; simpl; auto. inversion H; subst; auto. Qed.

Lemma o3w_le_field_bound: forall s i k, bytes_ok s -> 0 <= k -> 0 <= le_field s i k < 2 ^ (8 * k).
Proof.
  intros. unfold le_field, slice.
  assert (bytes_ok (firstn (Z.to_nat k) (skipn (Z.to_nat i) s))).
  { unfold bytes_ok in *. apply o3w_Forall_firstn, o3w_Forall_skipn. auto. }
  destruct (o3w_le_value_bound _ H1). split; auto.
  eapply Z.lt_le_trans; [eassumption|]. apply Z.pow_le_mono_r; [lia|].
  rewrite firstn_length. lia.
Qed.

Lemma o3w_skip_range: forall m, 0 <= m < 2 ^ 32 -> is_skippable_magic m = true ->
  0 <= m - ZSTD_MAGIC_SKIPPABLE_START < 16.
Proof.
  intros m Hm H. unfold is_skippable_magic, ZSTD_MAGIC_SKIPPABLE_MASK in H. apply Z.eqb_eq in H.
  assert (E: Z.land m 4294967280 = Z.ldiff (Z.land m (Z.ones 32)) (Z.ones 4)).
  { change 4294967280 with (Z.ldiff (Z.ones 32) (Z.ones 4)). apply Z.bits_inj'; intros i Hi.
    rewrite Z.land_spec, !Z.ldiff_spec, Z.land_spec.
    destruct (Z.testbit m i), (Z.testbit (Z.ones 32) i), (Z.testbit (Z.ones 4) i); reflexivity. }
  rewrite Z.land_ones in E by lia. rewrite Z.mod_small in E by lia.
  rewrite Z.ldiff_ones_r in E by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 in E by lia.
  change (2 ^ 4) with 16 in E. rewrite E in H.
  pose proof (Z.mod_pos_bound m 16 ltac:(lia)). pose proof (Z.div_mod m 16 ltac:(lia)). lia.
Qed.

Lemma o3w_gfh_dictID: forall s h, bytes_ok s -> get_frame_header s = FH_ok h ->
  0 <= fh_dictID h <= Int.max_unsigned.
Proof.
  intros s h Hb H. unfold get_frame_header in H. cbv zeta in H.
  change Int.max_unsigned with 4294967295.
  destruct (Zlength s <? 5).
  { destruct (Zlength s >? 0); [destruct (andb _ _)|]; discriminate. }
  destruct (le_field s 0 4 =? ZSTD_MAGICNUMBER) eqn:Em; cbn [negb] in H.
  - destruct (Zlength s <? fhd_header_size (byte_at s 4)); [discriminate|].
    destruct (negb (Z.land (byte_at s 4) 8 =? 0)); [discriminate|].
    destruct (andb _ _); [discriminate|].
    injection H as <-. cbn [fh_dictID].
    match goal with |- context [le_field s ?p ?k0] =>
      assert (D: 0 <= k0 <= 4) by (destruct (Z.to_nat (Z.land (byte_at s 4) 3)) as [|[|[|[|[|]]]]]; simpl; lia);
      pose proof (o3w_le_field_bound s p k0 Hb ltac:(lia)) as B;
      remember k0 as k end.
    assert (2 ^ (8 * k) <= 2 ^ 32) by (apply Z.pow_le_mono_r; lia). lia.
  - destruct (is_skippable_magic (le_field s 0 4)) eqn:Es; [|discriminate].
    destruct (Zlength s <? ZSTD_SKIPPABLEHEADERSIZE); [discriminate|].
    injection H as <-. cbn [fh_dictID].
    pose proof (o3w_le_field_bound s 0 4 Hb ltac:(lia)) as B2.
    pose proof (o3w_skip_range (le_field s 0 4) ltac:(change (2 ^ (8 * 4)) with (2 ^ 32) in B2; lia) Es).
    lia.
Qed.

Lemma o3w_le_bytes_ok: forall k v, Forall is_byte (le_bytes k v).
Proof.
  induction k; intros v; cbn [le_bytes]; constructor; [|apply IHk].
  unfold is_byte. apply Z.mod_pos_bound. lia.
Qed.

Lemma o3w_gfhm_dictID: forall mg s h, bytes_ok s -> get_frame_header_m mg s = FH_ok h ->
  0 <= fh_dictID h <= Int.max_unsigned.
Proof.
  intros mg s h Hb H. unfold get_frame_header_m in H. destruct mg; cbn [negb] in H.
  - destruct (Zlength s <? 1); [discriminate|].
    destruct (get_frame_header (magic_bytes ++ s)) eqn:E; try discriminate.
    injection H as <-. cbn [fh_unshift fh_dictID]. apply (o3w_gfh_dictID (magic_bytes ++ s)); [|exact E].
    unfold bytes_ok. apply Forall_app. split; [|exact Hb].
    apply o3w_le_bytes_ok.
  - exact (o3w_gfh_dictID _ _ Hb H).
Qed.

(* ---------- a header zstd cannot parse decides the frame with any dictionary, never as a success ---------- *)

Lemma o3w_dfm_nofh: forall md d wlim s, (forall h, get_frame_header_m (md_magicless md) s <> FH_ok h) ->
  decode_frame_m md d wlim s = decode_frame_m md no_dict wlim s /\
  (forall c k, decode_frame_m md no_dict wlim s <> FOk c k).
Proof.
  intros md d wlim s Hn. unfold decode_frame_m. cbv zeta.
  destruct (get_frame_header_m (md_magicless md) s) eqn:E; try (exfalso; eapply Hn; reflexivity);
  repeat match goal with |- context [if ?c then _ else _] => destruct c end;
  (split; [reflexivity | intros; discriminate]).
Qed.

Ltac o3w_nodict Hn :=
  repeat match goal with
  | H0: context [decode_frame_m ?md ?d ?wlim ?s] |- _ =>
      lazymatch d with no_dict => fail | _ => rewrite (proj1 (o3w_dfm_nofh md d wlim s Hn)) in H0 end
  | |- context [decode_frame_m ?md ?d ?wlim ?s] =>
      lazymatch d with no_dict => fail | _ => rewrite (proj1 (o3w_dfm_nofh md d wlim s Hn)) end
  end.

(* ---------- the walk without selection nor current dictionary ---------- *)

Lemma o3w_walk_none: forall fuel md sel cur wlim s off l t,
  walk_m fuel md sel_none None wlim s off = (l, t) -> t <> TUnk -> walk_m fuel md sel cur wlim s off = (l, t).
Proof.
  induction fuel; intros md sel cur wlim s off l t H Ht; cbn [walk_m] in H |- *.
  - injection H as _ <-. congruence.
  - destruct (Zlength s <? starting_len (md_magicless md)); [exact H|].
    destruct (negb (md_magicless md) && is_skippable_magic (le_field s 0 4))%bool.
    + destruct (skippable_frame_size s) as [k|]; [|exact H].
      match type of H with context [walk_m fuel md sel_none ?c0 wlim ?s' ?o'] =>
        assert (Hc0: c0 = None) by (unfold sel_none; destruct (md_dwin md); reflexivity);
        destruct (walk_m fuel md sel_none c0 wlim s' o') as [l0 t0] eqn:E end.
      injection H as <- <-. rewrite Hc0 in E.
      match goal with |- context [walk_m fuel md sel ?c2 wlim ?s' ?o'] =>
        rewrite (IHfuel _ sel c2 _ _ _ _ _ E Ht) end. reflexivity.
    + unfold frame_dict in H |- *. destruct (get_frame_header_m (md_magicless md) s) eqn:Eh.
      * assert (Hn: forall h, get_frame_header_m (md_magicless md) s <> FH_ok h) by congruence.
        destruct cur as [d|]; cbv beta iota in H |- *; o3w_nodict Hn;
        destruct (decode_frame_m md no_dict wlim s) eqn:Ed; try exact H;
        exfalso; eapply (proj2 (o3w_dfm_nofh md no_dict wlim s Hn)); eauto.
      * assert (Hn: forall h, get_frame_header_m (md_magicless md) s <> FH_ok h) by congruence.
        destruct cur as [d|]; cbv beta iota in H |- *; o3w_nodict Hn;
        destruct (decode_frame_m md no_dict wlim s) eqn:Ed; try exact H;
        exfalso; eapply (proj2 (o3w_dfm_nofh md no_dict wlim s Hn)); eauto.
      * unfold sel_none in H. injection H as _ <-. congruence.
Qed.

(* ---------- two selections that agree on the 32-bit IDs, a less informed current dictionary ---------- *)

Lemma o3w_walk_sel: forall fuel md sel1 sel2 cur1 cur2 wlim s off l t,
  bytes_ok s -> (forall id, 0 <= id <= Int.max_unsigned -> sel2 id = sel1 id) -> (cur1 = None \/ cur1 = cur2) ->
  walk_m fuel md sel1 cur1 wlim s off = (l, t) -> t <> TUnk -> walk_m fuel md sel2 cur2 wlim s off = (l, t).
Proof.
  induction fuel; intros md sel1 sel2 cur1 cur2 wlim s off l t Hb Hs Hc H Ht; cbn [walk_m] in H |- *.
  - injection H as _ <-. congruence.
  - destruct (Zlength s <? starting_len (md_magicless md)); [exact H|].
    destruct (negb (md_magicless md) && is_skippable_magic (le_field s 0 4))%bool.
    + destruct (skippable_frame_size s) as [k|]; [|exact H].
      match type of H with context [walk_m fuel md sel1 ?c1 wlim ?s' ?o'] =>
      match goal with |- context [walk_m fuel md sel2 ?c2 wlim s' o'] =>
        assert (Hc': c1 = None \/ c1 = c2);
        [ | destruct (walk_m fuel md sel1 c1 wlim s' o') as [l0 t0] eqn:E;
            injection H as <- <-;
            rewrite (IHfuel _ sel1 sel2 c1 c2 _ _ _ _ _ ltac:(apply o3w_Forall_skipn; exact Hb) Hs Hc' E Ht);
            reflexivity ] end end.
      destruct (md_dwin md); [ | exact Hc].
      rewrite (Hs (Z.land (le_field s 0 4) 15)).
      * destruct (sel1 (Z.land (le_field s 0 4) 15)); [right; reflexivity | exact Hc].
      * change 15 with (Z.ones 4). rewrite Z.land_ones by lia.
        pose proof (Z.mod_pos_bound (le_field s 0 4) (2 ^ 4) ltac:(lia)). rep_lia.
    + unfold frame_dict in H |- *. destruct (get_frame_header_m (md_magicless md) s) as [|k0|f] eqn:Eh.
      * assert (Hn: forall h, get_frame_header_m (md_magicless md) s <> FH_ok h) by congruence.
        clear Hc. cbv beta iota in H |- *.
        destruct cur1 as [d1|], cur2 as [d2|]; cbv beta iota in H |- *; o3w_nodict Hn;
        destruct (decode_frame_m md no_dict wlim s) eqn:Ed; try exact H;
        exfalso; eapply (proj2 (o3w_dfm_nofh md no_dict wlim s Hn)); eauto.
      * assert (Hn: forall h, get_frame_header_m (md_magicless md) s <> FH_ok h) by congruence.
        clear Hc. cbv beta iota in H |- *.
        destruct cur1 as [d1|], cur2 as [d2|]; cbv beta iota in H |- *; o3w_nodict Hn;
        destruct (decode_frame_m md no_dict wlim s) eqn:Ed; try exact H;
        exfalso; eapply (proj2 (o3w_dfm_nofh md no_dict wlim s Hn)); eauto.
      * rewrite (Hs _ (o3w_gfhm_dictID _ _ _ Hb Eh)).
        assert (Ho: forall d, match sel1 (fh_dictID f) with Some d => Some d | None => cur1 end = Some d ->
                     match sel1 (fh_dictID f) with Some d => Some d | None => cur2 end = Some d).
        { intros d. destruct (sel1 (fh_dictID f)); [auto|]. destruct Hc as [->|<-]; [discriminate | auto]. }
        destruct (match sel1 (fh_dictID f) with Some d => Some d | None => cur1 end) as [d|].
        2:{ injection H as _ <-. congruence. }
        rewrite (Ho d eq_refl).
        destruct (decode_frame_m md d wlim s) as [c k| | |]; try exact H.
        destruct (walk_m fuel md sel1 (Some d) wlim (skipn (Z.to_nat k) s) (off + k)) as [l0 t0] eqn:E.
        injection H as <- <-.
        rewrite (IHfuel _ sel1 sel2 (Some d) (Some d) _ _ _ _ _ ltac:(apply o3w_Forall_skipn; exact Hb) Hs
                   (or_intror eq_refl) E Ht).
        reflexivity.
Qed.

(* ---------- the same for the refusal of a series ---------- *)

(* a frame whose header zstd cannot parse is refused (its header cut) with any dictionary or none *)
Lemma o3w_fref_nofh: forall md d d' wlim s, (forall h, get_frame_header_m (md_magicless md) s <> FH_ok h) ->
  frame_refused_m md d wlim s -> frame_refused_m md d' wlim s.
Proof.
  intros md d d' wlim s Hn H. unfold frame_refused_m in *.
  destruct (Zlength s <? header_size_m (md_magicless md) s); [exact I |].
  destruct (get_frame_header_m (md_magicless md) s) eqn:E; try exact H. exfalso; eapply Hn; eauto.
Qed.

Lemma o3w_wref_none: forall fuel md sel cur wlim s,
  walk_refused fuel md sel_none None wlim s -> walk_refused fuel md sel cur wlim s.
Proof.
  induction fuel; intros md sel cur wlim s H; [destruct H |]. cbn [walk_refused] in H |- *.
  destruct (Zlength s <? starting_len (md_magicless md)); [exact H |].
  destruct (negb (md_magicless md) && is_skippable_magic (le_field s 0 4))%bool.
  - destruct (skippable_frame_size s) as [k |]; [| destruct H].
    match type of H with walk_refused fuel md sel_none ?c0 wlim ?s' =>
      assert (Hc0: c0 = None) by (unfold sel_none; destruct (md_dwin md); reflexivity);
      rewrite Hc0 in H end.
    apply IHfuel. exact H.
  - unfold frame_dict in H |- *. destruct (get_frame_header_m (md_magicless md) s) eqn:Eh.
    1, 2: assert (Hn: forall h, get_frame_header_m (md_magicless md) s <> FH_ok h) by congruence;
      destruct cur as [d |]; cbv beta iota in H |- *; o3w_nodict Hn;
      destruct (decode_frame_m md no_dict wlim s) eqn:Ed;
      first [exact H | exact (False_ind _ (proj2 (o3w_dfm_nofh md no_dict wlim s Hn) _ _ Ed))
            | exact (o3w_fref_nofh _ _ _ _ _ Hn H)].
    + unfold sel_none in H. destruct H.
Qed.

Lemma o3w_wref_sel: forall fuel md sel1 sel2 cur1 cur2 wlim s,
  bytes_ok s -> (forall id, 0 <= id <= Int.max_unsigned -> sel2 id = sel1 id) -> (cur1 = None \/ cur1 = cur2) ->
  walk_refused fuel md sel1 cur1 wlim s -> walk_refused fuel md sel2 cur2 wlim s.
Proof.
  induction fuel; intros md sel1 sel2 cur1 cur2 wlim s Hb Hs Hc H; [destruct H |].
  cbn [walk_refused] in H |- *.
  destruct (Zlength s <? starting_len (md_magicless md)); [exact H |].
  destruct (negb (md_magicless md) && is_skippable_magic (le_field s 0 4))%bool.
  - destruct (skippable_frame_size s) as [k |]; [| destruct H].
    match type of H with walk_refused fuel md sel1 ?c1 wlim ?s' =>
    match goal with |- walk_refused fuel md sel2 ?c2 wlim s' =>
      assert (Hc': c1 = None \/ c1 = c2);
      [ | exact (IHfuel md sel1 sel2 c1 c2 wlim s' ltac:(apply o3w_Forall_skipn; exact Hb) Hs Hc' H) ] end end.
    destruct (md_dwin md); [| exact Hc].
    rewrite (Hs (Z.land (le_field s 0 4) 15)).
    + destruct (sel1 (Z.land (le_field s 0 4) 15)); [right; reflexivity | exact Hc].
    + change 15 with (Z.ones 4). rewrite Z.land_ones by lia.
      pose proof (Z.mod_pos_bound (le_field s 0 4) (2 ^ 4) ltac:(lia)). rep_lia.
  - unfold frame_dict in H |- *. destruct (get_frame_header_m (md_magicless md) s) as [|k0|f] eqn:Eh.
    1, 2: assert (Hn: forall h, get_frame_header_m (md_magicless md) s <> FH_ok h) by congruence;
      clear Hc; destruct cur1 as [d1 |], cur2 as [d2 |]; cbv beta iota in H |- *; o3w_nodict Hn;
      destruct (decode_frame_m md no_dict wlim s) eqn:Ed;
      first [exact H | exact (False_ind _ (proj2 (o3w_dfm_nofh md no_dict wlim s Hn) _ _ Ed))
            | exact (o3w_fref_nofh _ _ _ _ _ Hn H)].
    + rewrite (Hs _ (o3w_gfhm_dictID _ _ _ Hb Eh)).
      assert (Ho: forall d, match sel1 (fh_dictID f) with Some d => Some d | None => cur1 end = Some d ->
                   match sel1 (fh_dictID f) with Some d => Some d | None => cur2 end = Some d).
      { intros d. destruct (sel1 (fh_dictID f)); [auto |]. destruct Hc as [-> | <-]; [discriminate | auto]. }
      destruct (match sel1 (fh_dictID f) with Some d => Some d | None => cur1 end) as [d |]; [| destruct H].
      rewrite (Ho d eq_refl).
      destruct (decode_frame_m md d wlim s) as [c k | | |]; try exact H.
      exact (IHfuel md sel1 sel2 (Some d) (Some d) wlim _ ltac:(apply o3w_Forall_skipn; exact Hb) Hs
               (or_intror eq_refl) H).
Qed.

Lemma o3_walk_facts :
  (* the empty selection without a current dictionary: its claims follow from any other's *)
  (forall (md: dmode) (sel: Z -> option dict_model) (cur: option dict_model) (s: list Z) (cap r: Z) (out: list val),
     oneshot_sel md sel cur s cap r out -> oneshot_sel md sel_none None s cap r out) /\
  (forall (md: dmode) (dm: dict_model) (s: list Z) (cap r: Z) (out: list val),
     oneshot_ok md (Some dm) s cap r out -> oneshot_sel md sel_none None s cap r out) /\
  (* two selections that agree on the 32-bit IDs; the target has no current dictionary *)
  (forall (md: dmode) (sel1 sel2: Z -> option dict_model) (cur: option dict_model) (s: list Z) (cap r: Z)
     (out: list val),
     bytes_ok s -> (forall id, 0 <= id <= Int.max_unsigned -> sel2 id = sel1 id) ->
     oneshot_sel md sel2 cur s cap r out -> oneshot_sel md sel1 None s cap r out).
Proof.
  assert (P1: forall (md: dmode) (sel: Z -> option dict_model) (cur: option dict_model) (s: list Z) (cap r: Z)
     (out: list val), oneshot_sel md sel cur s cap r out -> oneshot_sel md sel_none None s cap r out).
  { intros md sel cur s cap r out [H1 H2]. split; [exact H1|].
    unfold decode_series_m, series_frames_m in *.
    destruct (walk_m (S (length s)) md sel_none None no_wlim s 0) as [l t] eqn:E.
    destruct t; try (rewrite (o3w_walk_none _ _ sel cur _ _ _ _ _ E ltac:(discriminate)) in H2; exact H2).
    intros Hr. unfold series_refused_m in Hr. apply (o3w_wref_none _ _ sel cur) in Hr.
    pose proof (wref_tunk _ _ _ _ _ _ 0 Hr) as Ht.
    destruct (walk_m (S (length s)) md sel cur no_wlim s 0) as [l2 t2]. simpl in Ht. subst t2.
    apply H2. exact Hr. }
  split; [exact P1|]. split.
  - intros md dm s cap r out H. exact (P1 md sel_none (Some dm) s cap r out H).
  - intros md sel1 sel2 cur s cap r out Hb Hs [H1 H2]. split; [exact H1|].
    unfold decode_series_m, series_frames_m in *.
    destruct (walk_m (S (length s)) md sel1 None no_wlim s 0) as [l t] eqn:E.
    destruct t;
      try (rewrite (o3w_walk_sel _ _ sel1 sel2 None cur _ _ _ _ _ Hb Hs (or_introl eq_refl) E ltac:(discriminate))
             in H2; exact H2).
    intros Hr. unfold series_refused_m in Hr.
    apply (o3w_wref_sel _ _ sel1 sel2 None cur _ _ Hb Hs (or_introl eq_refl)) in Hr.
    pose proof (wref_tunk _ _ _ _ _ _ 0 Hr) as Ht.
    destruct (walk_m (S (length s)) md sel2 cur no_wlim s 0) as [l2 t2]. simpl in Ht. subst t2.
    apply H2. exact Hr.
Qed.

End CM_O3ModelWalk_1.
