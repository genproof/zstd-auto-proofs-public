(* FS3 one-shot frames, ZSTD_decompressMultiFrame: the error codes of the loop (Spec_codes.oneshot_codes).

   The loop keeps codes_inv next to Multi3Ser.series_inv: every walk of the whole series that ends at a frame
   refused by its checksum (series_ck_m) or that decodes all of it with Raw/RLE frames only (series_rr_m) goes
   through the frames the loop has decoded so far (u bytes of content) and continues from the source offset off
   with the current dictionary cur.  At an exit, the walk's next step is the C's: a frame error carries the code
   of ZSTD_decompressFrame (Frames3Spec.frame_codes3), every other exit is one the relations cannot take. *)
Require Export Zstd.proof.dec.v3.FS.frames.Multi3Res.
Require Export Zstd.proof.zstd.Spec_codes_facts.
Local Open Scope Z_scope.

Section CM_Multi3Codes_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* the frame model's facts and the void claims without a dictionary (oneshot_codes_none): Spec_codes_facts.v *)

(* ---------- the invariant ---------- *)

(* at source offset off, u bytes of content written, the current dictionary cur: the walks of the whole series s
   from odm0 continue at off from cur, after u bytes *)
Definition codes_inv (md: dmode) (sel: Z -> option dict_model) (odm0 cur: option dict_model) (s: list Z)
    (off u: Z) : Prop :=
  (forall c, series_ck_m md sel no_wlim odm0 s c ->
     exists c', series_ck_m md sel no_wlim cur (sublist off (Zlength s) s) c' /\ Zlength c = u + Zlength c') /\
  (forall c, series_rr_m md sel no_wlim odm0 s c ->
     exists c', series_rr_m md sel no_wlim cur (sublist off (Zlength s) s) c' /\ Zlength c = u + Zlength c').

Lemma codes_inv_init: forall md sel odm s, codes_inv md sel odm odm s 0 0.
Proof.
  intros. unfold codes_inv. rewrite sublist_same by lia. split; intros c H; exists c; split; auto; lia.
Qed.

(* a skippable frame of k bytes at off *)
Lemma codes_inv_skip: forall md sel odm0 cur s off u k,
  md_magicless md = false -> md_dwin md = false -> 0 <= off -> 0 <= k -> off + k <= Zlength s ->
  is_skippable_magic (le_field (sublist off (Zlength s) s) 0 4) = true ->
  skippable_frame_size (sublist off (Zlength s) s) = Some k ->
  codes_inv md sel odm0 cur s off u -> codes_inv md sel odm0 cur s (off + k) u.
Proof.
  intros md sel odm0 cur s off u k Hmg Hdw Hoff Hk Hks Hm Hsk [Hck Hrr].
  assert (Hsd: forall t, skip_dict md sel cur t = cur) by (intros; unfold skip_dict; rewrite Hdw; reflexivity).
  unfold codes_inv. rewrite <- (skipn_sublist_end s off k) by lia.
  split.
  - intros c H. destruct (Hck c H) as (c' & H' & Hl).
    inversion H' as [cur1 s1 k1 c1 _ _ Hk1 Hn | cur1 s1 d1 c01 k1 c1 _ Hm1 | cur1 s1 d1 c1 _ Hm1]; subst.
    + rewrite Hsk in Hk1. injection Hk1 as <-. rewrite Hsd in Hn. eauto.
    + rewrite Hmg, Hm in Hm1. discriminate.
    + rewrite Hmg, Hm in Hm1. discriminate.
  - intros c H. destruct (Hrr c H) as (c' & H' & Hl).
    inversion H' as [cur1 | cur1 s1 k1 c1 _ _ Hk1 Hn | cur1 s1 d1 c01 k1 c1 _ Hm1]; subst.
    + match goal with E: [] = _ |- _ => rewrite <- E in Hsk end. discriminate.
    + rewrite Hsk in Hk1. injection Hk1 as <-. rewrite Hsd in Hn. eauto.
    + rewrite Hmg, Hm in Hm1. discriminate.
Qed.

(* a Zstandard frame at off, decoded with dm (the model's frame_dict) to r bytes, k bytes taken *)
Lemma codes_inv_frame: forall md sel odm0 cur dm s off u cap' r oc' k,
  0 <= off -> 0 <= k -> off + k <= Zlength s -> starting_len (md_magicless md) <= Zlength s - off ->
  (md_magicless md = true \/ is_skippable_magic (le_field (sublist off (Zlength s) s) 0 4) = false) ->
  frame_dict (md_magicless md) sel cur (sublist off (Zlength s) s) = Some dm ->
  frame_res3 md dm (sublist off (Zlength s) s) cap' r oc' 0 k -> is_error_code r = false ->
  codes_inv md sel odm0 cur s off u -> codes_inv md sel odm0 (Some dm) s (off + k) (u + r).
Proof.
  intros md sel odm0 cur dm s off u cap' r oc' k Hoff Hk Hks Hsl Hm Hfd Hf He [Hck Hrr].
  assert (Hne: sublist off (Zlength s) s <> nil).
  { intro E. pose proof (starting_len_pos (md_magicless md)).
    assert (Zlength (sublist off (Zlength s) s) = 0) by (rewrite E; reflexivity).
    rewrite Zlength_sublist in * by lia. lia. }
  assert (Hns: (negb (md_magicless md) && is_skippable_magic (le_field (sublist off (Zlength s) s) 0 4))%bool = false)
    by (destruct Hm as [-> | ->]; [reflexivity | apply andb_false_r]).
  unfold frame_res3 in Hf.
  unfold codes_inv. rewrite <- (skipn_sublist_end s off k) by lia.
  split.
  - intros c H. destruct (Hck c H) as (c' & H' & Hl).
    inversion H' as [cur1 s1 k1 c1 _ Hm1 | cur1 s1 d1 c01 k1 c1 _ _ Hd1 Hf1 Hn | cur1 s1 d1 c1 _ _ Hd1 Hf1]; subst.
    + rewrite Hns in Hm1. discriminate.
    + rewrite Hfd in Hd1. injection Hd1 as <-. rewrite Hf1 in Hf. destruct Hf as [Hf _].
      destruct (Hf He) as (-> & _ & ->). exists c1. split; [exact Hn |]. rewrite Zlength_app in Hl. lia.
    + rewrite Hfd in Hd1. injection Hd1 as <-. rewrite Hf1, He in Hf. discriminate.
  - intros c H. destruct (Hrr c H) as (c' & H' & Hl).
    inversion H' as [cur1 | cur1 s1 k1 c1 _ Hm1 | cur1 s1 d1 c01 k1 c1 _ _ Hd1 Hf1 _ Hn]; subst.
    + exfalso. apply Hne. congruence.
    + rewrite Hns in Hm1. discriminate.
    + rewrite Hfd in Hd1. injection Hd1 as <-. rewrite Hf1 in Hf. destruct Hf as [Hf _].
      destruct (Hf He) as (-> & _ & ->). exists c1. split; [exact Hn |]. rewrite Zlength_app in Hl. lia.
Qed.

(* ---------- the exits ---------- *)

(* the codes an error r answers for: a checksum refusal with room, a Raw/RLE series without room *)
Definition codes_exact (md: dmode) (sel: Z -> option dict_model) (odm0: option dict_model) (s: list Z)
    (cap r: Z) : Prop :=
  (forall c, series_ck_m md sel no_wlim odm0 s c -> Zlength c <= cap -> r = err_code ZSTD_error_checksum_wrong) /\
  (forall c, series_rr_m md sel no_wlim odm0 s c -> cap < Zlength c -> r = err_code ZSTD_error_dstSize_tooSmall).

Lemma codes_exact_ok: forall md sel odm0 s cap r, codes_exact md sel odm0 s cap r -> oneshot_codes md sel odm0 s cap r.
Proof. intros md sel odm0 s cap r [H1 H2]. split; intros; left; eauto. Qed.

(* ZSTD_decompressMultiFrame turns a frame's prefix_unknown into srcSize_wrong: neither code above is
   prefix_unknown, so no walk reaches such an exit *)
Lemma codes_exact_pu: forall md sel odm0 s cap r r', codes_exact md sel odm0 s cap r ->
  error_of r = ZSTD_error_prefix_unknown -> oneshot_codes md sel odm0 s cap r'.
Proof.
  intros md sel odm0 s cap r r' [H1 H2] He. split; intros c H Hc; exfalso.
  - rewrite (H1 c H Hc) in He. vm_compute in He. discriminate.
  - rewrite (H2 c H Hc) in He. vm_compute in He. discriminate.
Qed.

(* the frame at off failed with r *)
Lemma codes_err_frame: forall md sel odm0 cur dm s off u cap r oc' k,
  0 <= off <= Zlength s -> 0 <= u <= cap -> starting_len (md_magicless md) <= Zlength s - off ->
  (md_magicless md = true \/ is_skippable_magic (le_field (sublist off (Zlength s) s) 0 4) = false) ->
  frame_dict (md_magicless md) sel cur (sublist off (Zlength s) s) = Some dm ->
  frame_res3 md dm (sublist off (Zlength s) s) (cap - u) r oc' 0 k ->
  frame_codes3 md dm (sublist off (Zlength s) s) (cap - u) r ->
  is_error_code r = true ->
  codes_inv md sel odm0 cur s off u -> codes_exact md sel odm0 s cap r.
Proof.
  intros md sel odm0 cur dm s off u cap r oc' k Hoff Hu Hsl Hm Hfd Hf [Hc1 Hc2] He [Hck Hrr].
  assert (Hns: (negb (md_magicless md) && is_skippable_magic (le_field (sublist off (Zlength s) s) 0 4))%bool = false)
    by (destruct Hm as [-> | ->]; [reflexivity | apply andb_false_r]).
  unfold frame_res3 in Hf.
  split.
  - intros c H Hc. destruct (Hck c H) as (c' & H' & Hl).
    inversion H' as [cur1 s1 k1 c1 _ Hm1 | cur1 s1 d1 c01 k1 c1 _ _ Hd1 Hf1 Hn | cur1 s1 d1 c1 _ _ Hd1 Hf1 Ho]; subst.
    + rewrite Hns in Hm1. discriminate.
    + rewrite Hfd in Hd1. injection Hd1 as <-. rewrite Hf1 in Hf. destruct Hf as [_ Hf].
      specialize (Hf He). rewrite Zlength_app in Hl. pose proof (Zlength_nonneg c1). lia.
    + rewrite Hfd in Hd1. injection Hd1 as <-. apply (Hc2 Hf1 c' Ho). lia.
  - intros c H Hc. destruct (Hrr c H) as (c' & H' & Hl).
    inversion H' as [cur1 | cur1 s1 k1 c1 _ Hm1 | cur1 s1 d1 c01 k1 c1 _ _ Hd1 Hf1 Hrr1 Hn]; subst.
    + pose proof (starting_len_pos (md_magicless md)).
      assert (Zlength (sublist off (Zlength s) s) = 0)
        by (match goal with E: [] = _ |- _ => rewrite <- E end; reflexivity).
      rewrite Zlength_sublist in * by lia. lia.
    + rewrite Hns in Hm1. discriminate.
    + rewrite Hfd in Hd1. injection Hd1 as <-. exact (Hc1 c01 k1 Hf1 Hrr1 He).
Qed.

(* the rest of the series admits no walk: the error exits before a frame is decoded *)
Lemma codes_dead: forall md sel odm0 cur s off u cap r,
  (forall c, series_ck_m md sel no_wlim cur (sublist off (Zlength s) s) c -> False) ->
  (forall c, series_rr_m md sel no_wlim cur (sublist off (Zlength s) s) c -> False) ->
  codes_inv md sel odm0 cur s off u -> oneshot_codes md sel odm0 s cap r.
Proof.
  intros md sel odm0 cur s off u cap r H1 H2 [Hck Hrr]. split; intros c H _; exfalso.
  - destruct (Hck c H) as (c' & H' & _). eauto.
  - destruct (Hrr c H) as (c' & H' & _). eauto.
Qed.

(* a nonempty rest shorter than a frame's start (the final srcSize_wrong) *)
Lemma dead_short_ck: forall md sel cur t c,
  Zlength t < starting_len (md_magicless md) -> series_ck_m md sel no_wlim cur t c -> False.
Proof. intros md sel cur t c Hl H. inversion H; lia. Qed.

Lemma dead_short_rr: forall md sel cur t c, t <> nil ->
  Zlength t < starting_len (md_magicless md) -> series_rr_m md sel no_wlim cur t c -> False.
Proof. intros md sel cur t c Hn Hl H. inversion H; subst; [congruence | lia | lia]. Qed.

(* a skippable frame whose size zstd refuses (readSkippableFrameSize's error) *)
Lemma dead_skip_ck: forall md sel cur t c,
  md_magicless md = false -> is_skippable_magic (le_field t 0 4) = true -> skippable_frame_size t = None ->
  series_ck_m md sel no_wlim cur t c -> False.
Proof.
  intros md sel cur t c Hmg Hm Hk H.
  inversion H as [cur1 s1 k1 c1 _ _ Hk1 | cur1 s1 d1 c01 k1 c1 _ Hm1 | cur1 s1 d1 c1 _ Hm1]; subst.
  - congruence.
  - rewrite Hmg, Hm in Hm1. discriminate.
  - rewrite Hmg, Hm in Hm1. discriminate.
Qed.

Lemma dead_skip_rr: forall md sel cur t c,
  md_magicless md = false -> is_skippable_magic (le_field t 0 4) = true -> skippable_frame_size t = None ->
  1 <= Zlength t -> series_rr_m md sel no_wlim cur t c -> False.
Proof.
  intros md sel cur t c Hmg Hm Hk Hl H.
  inversion H as [cur1 | cur1 s1 k1 c1 _ _ Hk1 | cur1 s1 d1 c01 k1 c1 _ Hm1]; subst.
  - rewrite Zlength_nil in Hl. lia.
  - congruence.
  - rewrite Hmg, Hm in Hm1. discriminate.
Qed.

(* the whole series read (off = |s|) with u bytes written, u within the capacity: no claim applies *)
Lemma codes_end: forall md sel odm0 cur s u cap r,
  u <= cap -> codes_inv md sel odm0 cur s (Zlength s) u -> oneshot_codes md sel odm0 s cap r.
Proof.
  intros md sel odm0 cur s u cap r Hu [Hck Hrr]. rewrite sublist_nil in Hck, Hrr.
  pose proof (starting_len_pos (md_magicless md)) as Hsl.
  split; intros c H Hc; exfalso.
  - destruct (Hck c H) as (c' & H' & _). inversion H'; rewrite ?Zlength_nil in *; lia.
  - destruct (Hrr c H) as (c' & H' & Hl). inversion H'; subst; rewrite ?Zlength_nil in *; lia.
Qed.

(* ---------- the postcondition ---------- *)

(* the two claims of the spec from the loop's, which holds under the probe's selection mf_sel *)
Lemma mf_codes_post: forall pr sp a l tbl s cap r, 0 <= cap ->
  (darg_model a <> None -> oneshot_codes (dmode_of pr) (mf_sel pr sp a l tbl) (darg_model a) s cap r) ->
  (darg_ddict a <> nullval -> darg_model a <> None) ->
  (sel_on pr sp = false \/ darg_ddict a = nullval -> oneshot_codes (dmode_of pr) sel_none (darg_model a) s cap r) /\
  (sel_on pr sp = true -> darg_ddict a <> nullval -> oneshot_codes (dmode_of pr) (psel l tbl) (darg_model a) s cap r).
Proof.
  intros pr sp a l tbl s cap r Hc H Hm. unfold mf_sel in H. split.
  - intros Hs. destruct (darg_model a) as [dm |] eqn:Ea; [| apply oneshot_codes_none; auto].
    specialize (H ltac:(discriminate)).
    replace (andb (sel_on pr sp) (negb (veqb (darg_ddict a) nullval))) with false in H; [exact H |].
    destruct Hs as [-> | ->]; [reflexivity |]. unfold veqb. destruct (Val.eq nullval nullval); [| congruence].
    destruct (sel_on pr sp); reflexivity.
  - intros Hs Hn. specialize (H (Hm Hn)).
    rewrite Hs in H. replace (negb (veqb (darg_ddict a) nullval)) with true in H; [exact H |].
    unfold veqb. destruct (Val.eq (darg_ddict a) nullval); [contradiction | reflexivity].
Qed.

End CM_Multi3Codes_1.
