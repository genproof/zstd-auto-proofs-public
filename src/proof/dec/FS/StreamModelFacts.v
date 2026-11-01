(* FS streaming: the model facts ZSTD_decompressStream's proof uses.
   Plain Coq.  The statements are fixed for the streaming proof; their proofs follow them.

   fdead x: every series that starts with the bytes x of a frame stops there with TUnk (no claim);
   fbad x:  no series that starts with x is decoded completely with the streaming window limit (zstd may
            fail on x: the error clause of stream_claims holds). *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Block Zstd.proof.model.Xxh64
  Zstd.proof.model.Info Zstd.proof.model.Series Zstd.proof.model.StreamModel.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Require Import Zstd.proof.dec.FS.StreamModelDefs.
Import ListNotations.
Local Open Scope Z_scope.




(* ==================== helper lemmas ==================== *)

Local Open Scope bool_scope.

(* ---------- helpers: lists and fields ---------- *)

Lemma Zlength_nonneg : forall (l: list Z), 0 <= Zlength l.
Proof. intros. rewrite Zlength_correct. lia. Qed.

Lemma Zlength_app : forall (a b: list Z), Zlength (a ++ b) = Zlength a + Zlength b.
Proof. intros. rewrite !Zlength_correct, length_app. lia. Qed.

Lemma is_prefix_ex : forall p s, is_prefix p s -> exists r, s = p ++ r.
Proof.
  unfold is_prefix; intros p s H. exists (skipn (length p) s).
  pose proof (firstn_skipn (length p) s) as E. rewrite H in E. auto.
Qed.

Lemma is_prefix_app : forall p r, is_prefix p (p ++ r).
Proof.
  unfold is_prefix; intros. rewrite firstn_app, Nat.sub_diag, firstn_O, app_nil_r, firstn_all. auto.
Qed.

Lemma is_prefix_app_l : forall p q s, is_prefix (p ++ q) s -> is_prefix p s.
Proof.
  intros p q s H. apply is_prefix_ex in H. destruct H as [r ->]. rewrite <- app_assoc. apply is_prefix_app.
Qed.

Lemma Zlength_skipn : forall (l: list Z) n, 0 <= n <= Zlength l -> Zlength (skipn (Z.to_nat n) l) = Zlength l - n.
Proof. intros. rewrite !Zlength_correct, length_skipn. rewrite Zlength_correct in H. lia. Qed.

Lemma skipn_app_le : forall (l1 l2: list Z) n, (n <= length l1)%nat -> skipn n (l1 ++ l2) = skipn n l1 ++ l2.
Proof.
  intros. rewrite skipn_app. replace (n - length l1)%nat with O by lia. auto.
Qed.

Lemma firstn_app_le : forall (l1 l2: list Z) n, (n <= length l1)%nat -> firstn n (l1 ++ l2) = firstn n l1.
Proof.
  intros. rewrite firstn_app. replace (n - length l1)%nat with O by lia. rewrite firstn_O, app_nil_r. auto.
Qed.

Lemma slice_app : forall x r i k, 0 <= i -> 0 <= k -> i + k <= Zlength x ->
  slice (x ++ r) i k = slice x i k.
Proof.
  intros. unfold slice. rewrite Zlength_correct in H1.
  rewrite skipn_app_le by lia. rewrite firstn_app_le; auto.
  rewrite length_skipn. lia.
Qed.

Lemma le_field_app : forall x r i k, 0 <= i -> 0 <= k -> i + k <= Zlength x ->
  le_field (x ++ r) i k = le_field x i k.
Proof. intros. unfold le_field. rewrite slice_app; auto. Qed.

Lemma byte_at_app : forall x r i, 0 <= i < Zlength x -> byte_at (x ++ r) i = byte_at x i.
Proof.
  intros. unfold byte_at. rewrite Zlength_correct in H. rewrite app_nth1; auto. lia.
Qed.

Lemma bytes_ok_byte_at : forall x i, bytes_ok x -> 0 <= byte_at x i < 256.
Proof.
  intros x i H. unfold byte_at. destruct (lt_dec (Z.to_nat i) (length x)).
  - eapply Forall_forall in H; [exact H|]. apply nth_In; auto.
  - rewrite nth_overflow by lia. lia.
Qed.

(* ---------- frame headers ---------- *)

Lemma fhd_cases : forall fhd, 0 <= fhd < 256 ->
  (Z.land fhd 3 = 0 \/ Z.land fhd 3 = 1 \/ Z.land fhd 3 = 2 \/ Z.land fhd 3 = 3) /\
  (Z.land (Z.shiftr fhd 5) 1 = 0 \/ Z.land (Z.shiftr fhd 5) 1 = 1) /\
  (Z.shiftr fhd 6 = 0 \/ Z.shiftr fhd 6 = 1 \/ Z.shiftr fhd 6 = 2 \/ Z.shiftr fhd 6 = 3).
Proof.
  intros fhd H.
  change 3 with (Z.ones 2) at 1 2 3 4. change 1 with (Z.ones 1) at 1 2 3.
  rewrite !Z.land_ones by lia. rewrite !Z.shiftr_div_pow2 by lia.
  change (Z.ones 1) with 1. change (2 ^ 2) with 4. change (2 ^ 1) with 2. change (2 ^ 5) with 32. change (2 ^ 6) with 64.
  split; [|split]; Z.div_mod_to_equations; lia.
Qed.

Lemma gfh_len : forall x h, get_frame_header x = FH_ok h -> 5 <= Zlength x.
Proof.
  intros x h H. unfold get_frame_header in H. cbv zeta in H.
  destruct (Zlength x <? 5) eqn:E; [|apply Z.ltb_ge in E; lia].
  destruct (Zlength x >? 0); [destruct (_ && _)|]; discriminate.
Qed.

Lemma gfh_ext : forall x r h, get_frame_header x = FH_ok h -> 0 <= byte_at x 4 < 256 ->
  get_frame_header (x ++ r) = FH_ok h.
Proof.
  intros x r h H Hb. pose proof (gfh_len _ _ H) as Hn.
  pose proof (Zlength_nonneg r).
  unfold get_frame_header in *. cbv zeta in *.
  rewrite Zlength_app. rewrite (le_field_app x r 0 4) by lia. rewrite (byte_at_app x r 4) by lia.
  replace (Zlength x <? 5) with false in H by (symmetry; apply Z.ltb_ge; lia).
  replace (Zlength x + Zlength r <? 5) with false by (symmetry; apply Z.ltb_ge; lia).
  destruct (negb (le_field x 0 4 =? ZSTD_MAGICNUMBER)) eqn:Em.
  - destruct (is_skippable_magic _); [|discriminate].
    destruct (Zlength x <? ZSTD_SKIPPABLEHEADERSIZE) eqn:E8; [discriminate|].
    apply Z.ltb_ge in E8. unfold ZSTD_SKIPPABLEHEADERSIZE in *.
    replace (Zlength x + Zlength r <? 8) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite (le_field_app x r 4 4) by lia. exact H.
  - set (fhd := byte_at x 4) in *.
    destruct (Zlength x <? fhd_header_size fhd) eqn:Ef; [discriminate|].
    apply Z.ltb_ge in Ef.
    replace (Zlength x + Zlength r <? fhd_header_size fhd) with false by (symmetry; apply Z.ltb_ge; lia).
    unfold fhd_header_size in Ef.
    destruct (fhd_cases fhd Hb) as [Hd [Hs Hc]].
    destruct Hd as [Hd|[Hd|[Hd|Hd]]]; rewrite Hd in *;
    destruct Hs as [Hs|Hs]; rewrite Hs in *;
    destruct Hc as [Hc|[Hc|[Hc|Hc]]]; rewrite Hc in *;
    simpl nth in *; simpl Z.eqb in *; simpl andb in *; cbv iota in *;
    rewrite ?(le_field_app x r) by lia; rewrite ?(byte_at_app x r) by lia; exact H.
Qed.

(* ---------- blocks ---------- *)

Lemma Zgtb_le : forall a b, (a >? b) = false <-> a <= b.
Proof. intros. rewrite Z.gtb_ltb, Z.ltb_ge. lia. Qed.

Lemma Zgtb_gt : forall a b, (a >? b) = true <-> a > b.
Proof. intros. rewrite Z.gtb_ltb, Z.ltb_lt. lia. Qed.

Lemma cblock_size_len : forall s c, cblock_size s = Some c -> 3 <= Zlength s.
Proof.
  unfold cblock_size; intros. destruct (Zlength s <? ZSTD_blockHeaderSize) eqn:E; [discriminate|].
  apply Z.ltb_ge in E. unfold ZSTD_blockHeaderSize in E. lia.
Qed.

Lemma block_props_app : forall s r, 3 <= Zlength s -> block_props_of (s ++ r) = block_props_of s.
Proof. intros. unfold block_props_of. rewrite le_field_app by lia. auto. Qed.

Lemma cblock_size_app : forall s r, 3 <= Zlength s -> cblock_size (s ++ r) = cblock_size s.
Proof.
  intros. unfold cblock_size. rewrite block_props_app by auto. rewrite Zlength_app.
  pose proof (Zlength_nonneg r). unfold ZSTD_blockHeaderSize.
  replace (Zlength s + Zlength r <? 3) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (Zlength s <? 3) with false by (symmetry; apply Z.ltb_ge; lia). auto.
Qed.

Definition oshift (d: Z) (r: option (list Z * Z)) : option (list Z * Z) :=
  match r with Some (o, k) => Some (o, d + k) | None => None end.

Ltac dmatch :=
  match goal with
  | |- context [match ?e with _ => _ end] => let E := fresh "E" in destruct e eqn:E
  end.
Ltac dmatchH H :=
  match type of H with
  | context [match ?e with _ => _ end] => let E := fresh "E" in destruct e eqn:E
  end.

Lemma db_S_eq : forall st s out bsm ws f,
  decode_blocks (S f) st nil s out bsm ws =
  match block_res st s out bsm ws with
  | None => None
  | Some (st', out', k, last) =>
      if last then Some (out', k) else oshift k (decode_blocks f st' nil (skipn (Z.to_nat k) s) out' bsm ws)
  end.
Proof.
  intros. unfold block_res. cbn [decode_blocks].
  destruct (cblock_size s) as [c|]; auto.
  destruct (c >? Zlength s - ZSTD_blockHeaderSize); auto. cbv zeta.
  match goal with |- match ?e with None => None | Some _ => _ end = _ => destruct e as [[st2 out2]|] end; auto.
Qed.

Lemma br_step : forall st s out bsm ws st' out' k last f,
  block_res st s out bsm ws = Some (st', out', k, last) ->
  decode_blocks (S f) st nil s out bsm ws =
    if last then Some (out', k) else oshift k (decode_blocks f st' nil (skipn (Z.to_nat k) s) out' bsm ws).
Proof. intros. rewrite db_S_eq, H. auto. Qed.

Lemma br_none : forall st s out bsm ws f,
  block_res st s out bsm ws = None -> decode_blocks (S f) st nil s out bsm ws = None.
Proof. intros. rewrite db_S_eq, H. auto. Qed.

Lemma slice_app' : forall x r i k, 0 <= i -> i + k <= Zlength x ->
  slice (x ++ r) i k = slice x i k.
Proof.
  intros. destruct (Z_lt_dec k 0).
  - unfold slice. replace (Z.to_nat k) with O by lia. auto.
  - apply slice_app; lia.
Qed.

Lemma br_app : forall st s out bsm ws res t,
  block_res st s out bsm ws = Some res -> block_res st (s ++ t) out bsm ws = Some res.
Proof.
  intros. unfold block_res in *.
  destruct (cblock_size s) as [c|] eqn:Ec; [|discriminate].
  pose proof (cblock_size_len _ _ Ec).
  rewrite cblock_size_app, Ec by auto.
  destruct (c >? Zlength s - ZSTD_blockHeaderSize) eqn:E; [discriminate|].
  apply Zgtb_le in E. pose proof (Zlength_nonneg t).
  replace (c >? Zlength (s ++ t) - ZSTD_blockHeaderSize) with false
    by (symmetry; apply Zgtb_le; rewrite Zlength_app; lia).
  rewrite block_props_app by auto. rewrite slice_app' by (unfold ZSTD_blockHeaderSize in *; lia).
  exact H.
Qed.

Lemma br_some_len : forall st s out bsm ws st' out' k last,
  block_res st s out bsm ws = Some (st', out', k, last) -> k <= Zlength s.
Proof.
  intros. unfold block_res in H.
  destruct (cblock_size s) as [c|] eqn:Ec; [|discriminate].
  destruct (c >? Zlength s - ZSTD_blockHeaderSize) eqn:E; [discriminate|]. cbv zeta in *.
  apply Zgtb_le in E.
  match type of H with context [match ?e with None => None | Some _ => _ end] =>
    destruct e as [[st2 out2]|] end; [|discriminate].
  assert (k = ZSTD_blockHeaderSize + c) by congruence. lia.
Qed.

(* the output only grows *)
Lemma br_out : forall st s out bsm ws st' out' k last,
  block_res st s out bsm ws = Some (st', out', k, last) -> exists d, out' = out ++ d.
Proof.
  intros. unfold block_res in H.
  destruct (cblock_size s) as [c|] eqn:Ec; [|discriminate].
  destruct (c >? Zlength s - ZSTD_blockHeaderSize) eqn:E; [discriminate|]. cbv zeta in *.
  destruct (bp_type _ =? 0); [|destruct (bp_type _ =? 1)].
  - destruct (c >? bsm); [discriminate|]. inversion H; subst. eauto.
  - destruct ((bp_origSize _ >? bsm) || _); [discriminate|]. inversion H; subst. eauto.
  - destruct (decode_block _ _ _ _ _ _) as [[st2 c2]|]; [|discriminate]. inversion H; subst. eauto.
Qed.

Lemma db_out : forall f st s out bsm ws o k,
  decode_blocks f st nil s out bsm ws = Some (o, k) -> exists d, o = out ++ d.
Proof.
  induction f; intros; [discriminate|].
  destruct (block_res st s out bsm ws) as [[[[st' out'] k1] last]|] eqn:Eb.
  - rewrite (br_step _ _ _ _ _ _ _ _ _ f Eb) in H. destruct (br_out _ _ _ _ _ _ _ _ _ Eb) as [d1 ->].
    destruct last; [inversion H; subst; eauto|].
    unfold oshift in H. destruct (decode_blocks f st' nil _ _ _ _) as [[o2 k2]|] eqn:E2; [|discriminate].
    inversion H; subst. destruct (IHf _ _ _ _ _ _ _ E2) as [d2 ->]. exists (d1 ++ d2). rewrite app_assoc. auto.
  - rewrite br_none in H by auto. discriminate.
Qed.

(* the complete blocks of a frame *)
Lemma bp_db : forall bsm ws bl ts outc last, blocks_pre bsm ws bl ts outc last -> last = false ->
  exists n, (n <= length bl)%nat /\ forall fuel t,
    decode_blocks (n + fuel) dstate_init nil (bl ++ t) nil bsm ws =
    oshift (Zlength bl) (decode_blocks fuel ts nil t outc bsm ws).
Proof.
  induction 1; intros.
  - exists O. split; auto. intros. simpl. unfold oshift.
    destruct (decode_blocks fuel _ _ _ _ _ _) as [[o k]|]; auto.
  - subst last. destruct (IHblocks_pre eq_refl) as [n [Hn IH]].
    assert (Hb3: 3 <= Zlength b).
    { unfold block_res in H0. destruct (cblock_size b) eqn:Ec; [|discriminate]. eapply cblock_size_len; eauto. }
    exists (S n). split.
    { rewrite length_app. rewrite Zlength_correct in Hb3. lia. }
    intros. replace (S n + fuel)%nat with (n + S fuel)%nat by lia.
    rewrite <- app_assoc, IH.
    rewrite (br_step _ _ _ _ _ _ _ _ _ fuel (br_app _ _ _ _ _ _ t H0)).
    rewrite skipn_app_le by (rewrite Zlength_correct; lia).
    replace (Z.to_nat (Zlength b)) with (length b) by (rewrite Zlength_correct; lia).
    rewrite skipn_all, app_nil_l.
    unfold oshift. destruct (decode_blocks fuel ts' nil t out' bsm ws) as [[o k]|]; auto.
    rewrite Zlength_app. f_equal. f_equal. lia.
Qed.

Lemma bp_db_last : forall bsm ws bl ts outc, blocks_pre bsm ws bl ts outc true ->
  forall fuel t, (length bl <= fuel)%nat ->
    decode_blocks fuel dstate_init nil (bl ++ t) nil bsm ws = Some (outc, Zlength bl).
Proof.
  intros. inversion H; subst.
  destruct (bp_db _ _ _ _ _ _ H1 eq_refl) as [n [Hn IH]].
  assert (Hb3: 3 <= Zlength b).
  { unfold block_res in H2. destruct (cblock_size b) eqn:Ec; [|discriminate]. eapply cblock_size_len; eauto. }
  rewrite length_app in H0. rewrite Zlength_correct in Hb3.
  replace fuel with (n + S (fuel - n - 1))%nat by lia.
  rewrite <- app_assoc, IH.
  rewrite (br_step _ _ _ _ _ _ _ _ _ _ (br_app _ _ _ _ _ _ t H2)).
  simpl. rewrite Zlength_app. auto.
Qed.

Lemma br_inv : forall st s out bsm ws st' out' k last,
  block_res st s out bsm ws = Some (st', out', k, last) ->
  exists c, cblock_size s = Some c /\ c <= Zlength s - 3 /\ k = 3 + c /\
            last = (bp_last (block_props_of s) =? 1).
Proof.
  intros. unfold block_res in H.
  destruct (cblock_size s) as [c|] eqn:Ec; [|discriminate].
  destruct (c >? Zlength s - ZSTD_blockHeaderSize) eqn:E; [discriminate|]. cbv zeta in *.
  apply Zgtb_le in E.
  match type of H with context [match ?e with None => None | Some _ => _ end] =>
    destruct e as [[st2 out2]|] end; [|discriminate].
  exists c. unfold ZSTD_blockHeaderSize in *. split; auto. split; [lia|].
  split; congruence.
Qed.

Lemma br_app_eq : forall st t out bsm ws c r,
  cblock_size t = Some c -> c <= Zlength t - 3 ->
  block_res st (t ++ r) out bsm ws = block_res st t out bsm ws.
Proof.
  intros. pose proof (cblock_size_len _ _ H). unfold block_res.
  rewrite cblock_size_app, H by auto. pose proof (Zlength_nonneg r).
  unfold ZSTD_blockHeaderSize.
  replace (c >? Zlength t - 3) with false by (symmetry; apply Zgtb_le; lia).
  replace (c >? Zlength (t ++ r) - 3) with false by (symmetry; apply Zgtb_le; rewrite Zlength_app; lia).
  rewrite block_props_app by auto. rewrite slice_app' by lia. auto.
Qed.

Lemma bs_S_eq : forall f t,
  blocks_size (S f) t =
  match cblock_size t with
  | None => None
  | Some c =>
      if ZSTD_blockHeaderSize + c >? Zlength t then None else
      if bp_last (block_props_of t) =? 1 then Some (ZSTD_blockHeaderSize + c, 1)
      else match blocks_size f (skipn (Z.to_nat (ZSTD_blockHeaderSize + c)) t) with
           | Some (k, nb) => Some (ZSTD_blockHeaderSize + c + k, nb + 1)
           | None => None
           end
  end.
Proof. reflexivity. Qed.

Lemma bs_len : forall f t k nb, blocks_size f t = Some (k, nb) -> 3 <= Zlength t /\ k <= Zlength t.
Proof.
  induction f; intros; [discriminate|]. rewrite bs_S_eq in H.
  destruct (cblock_size t) as [c|] eqn:Ec; [|discriminate].
  pose proof (cblock_size_len _ _ Ec). unfold ZSTD_blockHeaderSize in *.
  destruct (3 + c >? Zlength t) eqn:E; [discriminate|]. apply Zgtb_le in E.
  destruct (bp_last _ =? 1). { assert (k = 3 + c) by congruence. lia. }
  destruct (blocks_size f _) as [[k2 nb2]|] eqn:E2; [|discriminate].
  assert (k = 3 + c + k2) as -> by congruence. destruct (IHf _ _ _ E2) as [_ Hk].
  rewrite Zlength_correct, length_skipn in Hk. rewrite Zlength_correct in *. lia.
Qed.

Lemma db_ext_bs : forall f t k nb, blocks_size f t = Some (k, nb) ->
  forall fuel st out bsm ws r,
    decode_blocks fuel st nil (t ++ r) out bsm ws = decode_blocks fuel st nil t out bsm ws.
Proof.
  induction f; intros; [discriminate|]. destruct fuel; [auto|].
  rewrite bs_S_eq in H.
  destruct (cblock_size t) as [c|] eqn:Ec; [|discriminate].
  pose proof (cblock_size_len _ _ Ec). unfold ZSTD_blockHeaderSize in *.
  destruct (3 + c >? Zlength t) eqn:E; [discriminate|]. apply Zgtb_le in E.
  rewrite !db_S_eq. rewrite (br_app_eq _ _ _ _ _ c) by (auto; lia).
  destruct (block_res st t out bsm ws) as [[[[st' out'] k1] last]|] eqn:Eb; auto.
  destruct (br_inv _ _ _ _ _ _ _ _ _ Eb) as [c' [Ec' [_ [-> ->]]]].
  rewrite Ec in Ec'. inversion Ec'; subst c'.
  destruct (bp_last _ =? 1); auto.
  destruct (blocks_size f _) as [[k2 nb2]|] eqn:E2; [|discriminate].
  rewrite skipn_app_le by (rewrite Zlength_correct in *; lia).
  erewrite IHf by eauto. auto.
Qed.

Lemma db_fuel_bs : forall f t k nb, blocks_size f t = Some (k, nb) ->
  forall fuel st out bsm ws, (f <= fuel)%nat ->
    decode_blocks fuel st nil t out bsm ws = decode_blocks f st nil t out bsm ws.
Proof.
  induction f; intros; [discriminate|]. destruct fuel; [lia|].
  rewrite bs_S_eq in H.
  destruct (cblock_size t) as [c|] eqn:Ec; [|discriminate].
  unfold ZSTD_blockHeaderSize in *.
  destruct (3 + c >? Zlength t) eqn:E; [discriminate|].
  rewrite !db_S_eq.
  destruct (block_res st t out bsm ws) as [[[[st' out'] k1] last]|] eqn:Eb; auto.
  destruct (br_inv _ _ _ _ _ _ _ _ _ Eb) as [c' [Ec' [_ [-> ->]]]].
  rewrite Ec in Ec'. inversion Ec'; subst c'.
  destruct (bp_last _ =? 1); auto.
  destruct (blocks_size f _) as [[k2 nb2]|] eqn:E2; [|discriminate].
  erewrite IHf by (eauto; lia). auto.
Qed.

Lemma db_bs : forall f st s out bsm ws o k,
  decode_blocks f st nil s out bsm ws = Some (o, k) -> exists nb, blocks_size f s = Some (k, nb).
Proof.
  induction f; intros; [discriminate|]. rewrite db_S_eq in H. rewrite bs_S_eq.
  destruct (block_res st s out bsm ws) as [[[[st' out'] k1] last]|] eqn:Eb; [|discriminate].
  destruct (br_inv _ _ _ _ _ _ _ _ _ Eb) as [c [Ec [Hc [-> ->]]]].
  rewrite Ec. unfold ZSTD_blockHeaderSize.
  replace (3 + c >? Zlength s) with false by (symmetry; apply Zgtb_le; lia).
  destruct (bp_last _ =? 1). { exists 1. congruence. }
  unfold oshift in H. destruct (decode_blocks f st' nil _ out' bsm ws) as [[o2 k2]|] eqn:E2; [|discriminate].
  assert (k = 3 + c + k2) as -> by congruence. destruct (IHf _ _ _ _ _ _ _ E2) as [nb ->]. eauto.
Qed.

(* ---------- frames ---------- *)

Lemma land1_cases : forall y, Z.land y 1 = 0 \/ Z.land y 1 = 1.
Proof.
  intros. pose proof (Z.land_ones y 1 ltac:(lia)) as E.
  change (Z.ones 1) with 1 in E. change (2 ^ 1) with 2 in E. rewrite E.
  Z.div_mod_to_equations. lia.
Qed.

Lemma fhs_ge6 : forall fhd, 0 <= fhd < 256 -> 6 <= fhd_header_size fhd.
Proof.
  intros. destruct (fhd_cases fhd H) as [Hd [Hs Hc]]. unfold fhd_header_size.
  destruct Hd as [Hd|[Hd|[Hd|Hd]]]; rewrite Hd;
  destruct Hs as [Hs|Hs]; rewrite Hs;
  destruct Hc as [Hc|[Hc|[Hc|Hc]]]; rewrite Hc; simpl; lia.
Qed.

Lemma skip_not_magic : forall m, is_skippable_magic m = true -> (m =? ZSTD_MAGICNUMBER) = false.
Proof.
  intros. destruct (Z.eqb_spec m ZSTD_MAGICNUMBER); auto. subst. discriminate.
Qed.

Lemma gfh_info : forall s h, get_frame_header s = FH_ok h ->
  (fh_frameType h = 1 /\ 8 <= Zlength s /\ (le_field s 0 4 =? ZSTD_MAGICNUMBER) = false /\
   is_skippable_magic (le_field s 0 4) = true /\ fh_headerSize h = 8 /\ fh_contentSize h = le_field s 4 4) \/
  (fh_frameType h = 0 /\ 5 <= Zlength s /\ le_field s 0 4 = ZSTD_MAGICNUMBER /\
   fh_headerSize h = fhd_header_size (byte_at s 4) /\ fh_headerSize h <= Zlength s /\
   Z.land (byte_at s 4) 8 = 0 /\
   (negb (Z.land (Z.shiftr (byte_at s 4) 5) 1 =? 1) &&
     (Z.shiftr (byte_at s 5) 3 + ZSTD_WINDOWLOG_ABSOLUTEMIN >? ZSTD_WINDOWLOG_MAX)) = false).
Proof.
  intros s h H. pose proof (gfh_len _ _ H) as Hn.
  unfold get_frame_header in H. cbv zeta in H.
  replace (Zlength s <? 5) with false in H by (symmetry; apply Z.ltb_ge; lia).
  destruct (le_field s 0 4 =? ZSTD_MAGICNUMBER) eqn:Em; simpl negb in H.
  - right. apply Z.eqb_eq in Em.
    destruct (Zlength s <? fhd_header_size (byte_at s 4)) eqn:Ef; [discriminate|]. apply Z.ltb_ge in Ef.
    destruct (Z.land (byte_at s 4) 8 =? 0) eqn:Er; simpl negb in H; [|discriminate]. apply Z.eqb_eq in Er.
    destruct ((Z.land (Z.shiftr (byte_at s 4) 5) 1 =? 0) &&
              (Z.shiftr (byte_at s 5) 3 + ZSTD_WINDOWLOG_ABSOLUTEMIN >? ZSTD_WINDOWLOG_MAX)) eqn:Ew; [discriminate|].
    inversion H; subst; clear H. simpl. repeat split; auto.
    destruct (land1_cases (Z.shiftr (byte_at s 4) 5)) as [E|E]; rewrite E in *; auto.
  - left. destruct (is_skippable_magic (le_field s 0 4)) eqn:Es; [|discriminate].
    destruct (Zlength s <? ZSTD_SKIPPABLEHEADERSIZE) eqn:E8; [discriminate|]. apply Z.ltb_ge in E8.
    inversion H; subst; clear H. simpl. repeat split; auto.
Qed.

Definition df_tail (h: frame_header) (s: list Z) : fres :=
  let hs := fh_headerSize h in
  let rest := skipn (Z.to_nat hs) s in
  match decode_blocks (length rest) dstate_init nil rest nil (fh_blockSizeMax h) (fh_windowSize h) with
  | None => FUnk
  | Some (out, k) =>
      if negb (fh_contentSize h =? ZSTD_CONTENTSIZE_UNKNOWN) && negb (Zlength out =? fh_contentSize h)
      then FUnk else
      if fh_checksumFlag h =? 1 then
        (if Zlength s - hs - k <? 4 then FUnk
         else if negb (le_field s (hs + k) 4 =? xxh64 out 0 mod 2 ^ 32) then FDetCk
         else FOk out (hs + k + 4))
      else FOk out (hs + k)
  end.

Lemma df_unfold : forall w s h, get_frame_header s = FH_ok h -> fh_frameType h = 0 ->
  9 <= Zlength s -> fh_headerSize h + 3 <= Zlength s ->
  decode_frame no_dict w s =
    if fh_windowSize h >? w then FDetHdr else if negb (fh_dictID h =? 0) then FUnk else df_tail h s.
Proof.
  intros w s h H Ht H9 H3.
  destruct (gfh_info _ _ H) as [[Ht' _]|[_ [_ [Hm [Hs [_ [Hr Hw]]]]]]]; [congruence|].
  unfold decode_frame. cbv zeta.
  replace (Zlength s <? ZSTD_FRAMEHEADERSIZE_MIN + ZSTD_blockHeaderSize) with false
    by (symmetry; apply Z.ltb_ge; unfold ZSTD_FRAMEHEADERSIZE_MIN, ZSTD_blockHeaderSize; lia).
  rewrite Hm, Z.eqb_refl. cbn [negb].
  replace (Zlength s <? fhd_header_size (byte_at s 4) + ZSTD_blockHeaderSize) with false
    by (symmetry; apply Z.ltb_ge; unfold ZSTD_blockHeaderSize; lia).
  rewrite Hr. cbn [negb Z.eqb]. rewrite Hw, H, Ht. cbn [negb Z.eqb].
  destruct (fh_windowSize h >? w); auto.
  cbn [dm_id no_dict dict_raw dm_state dm_content].
  destruct (fh_dictID h =? 0); reflexivity.
Qed.

Lemma le_field_app_max : forall x r i k, 0 <= k -> Z.max 0 i + k <= Zlength x ->
  le_field (x ++ r) i k = le_field x i k.
Proof.
  intros. unfold le_field, slice. replace (Z.to_nat i) with (Z.to_nat (Z.max 0 i)) by lia.
  fold (slice (x ++ r) (Z.max 0 i) k) (slice x (Z.max 0 i) k). rewrite slice_app; auto; lia.
Qed.

Lemma df_skip : forall w s, 4 <= Zlength s -> is_skippable_magic (le_field s 0 4) = true ->
  decode_frame no_dict w s = FUnk.
Proof.
  intros. unfold decode_frame. destruct (Zlength s <? _); auto. rewrite skip_not_magic by auto. auto.
Qed.

Lemma df_hdr_inv : forall w s, decode_frame no_dict w s <> FUnk -> decode_frame no_dict w s <> FDetHdr ->
  exists h, get_frame_header s = FH_ok h /\ fh_frameType h = 0 /\ 9 <= Zlength s /\
    fh_headerSize h + 3 <= Zlength s /\ fh_windowSize h <= w /\ fh_dictID h = 0 /\
    decode_frame no_dict w s = df_tail h s.
Proof.
  intros w s H1 H2.
  assert (A: exists h, get_frame_header s = FH_ok h /\ fh_frameType h = 0 /\ 9 <= Zlength s /\
                       fh_headerSize h + 3 <= Zlength s).
  { unfold decode_frame in H1, H2. cbv zeta in H1, H2.
    destruct (Zlength s <? ZSTD_FRAMEHEADERSIZE_MIN + ZSTD_blockHeaderSize) eqn:E1; [congruence|].
    destruct (negb (le_field s 0 4 =? ZSTD_MAGICNUMBER)) eqn:E2; [congruence|].
    destruct (Zlength s <? fhd_header_size (byte_at s 4) + ZSTD_blockHeaderSize) eqn:E3; [congruence|].
    destruct (negb (Z.land (byte_at s 4) 8 =? 0)) eqn:E4; [congruence|].
    destruct (_ && _) eqn:E5; [congruence|].
    destruct (get_frame_header s) as [| |h] eqn:G; try congruence.
    destruct (fh_windowSize h >? w); [congruence|].
    destruct (negb (fh_frameType h =? 0)) eqn:E6; [congruence|].
    exists h. apply Z.ltb_ge in E1, E3. unfold ZSTD_FRAMEHEADERSIZE_MIN, ZSTD_blockHeaderSize in *.
    destruct (gfh_info _ _ G) as [[Ht _]|[Ht [_ [_ [Hs _]]]]].
    - rewrite Ht in E6. discriminate.
    - repeat split; auto; lia. }
  destruct A as [h [G [Ht [H9 H3]]]].
  rewrite (df_unfold w s h G Ht H9 H3) in *.
  exists h. repeat split; auto.
  - destruct (fh_windowSize h >? w) eqn:E; [congruence|]. apply Zgtb_le in E; auto.
  - destruct (fh_windowSize h >? w); [congruence|].
    destruct (fh_dictID h =? 0) eqn:E; cbn [negb] in *; [apply Z.eqb_eq; auto|congruence].
  - destruct (fh_windowSize h >? w); [congruence|].
    destruct (fh_dictID h =? 0) eqn:E; cbn [negb] in *; [auto|congruence].
Qed.

Lemma df_fcs : forall w s c k, decode_frame no_dict w s = FOk c k -> frame_compressed_size s = Some k.
Proof.
  intros w s c k H.
  destruct (df_hdr_inv w s) as [h [G [Ht [H9 [H3 [_ [_ E]]]]]]]; try congruence.
  rewrite E in H. clear E.
  destruct (gfh_info _ _ G) as [[Ht' _]|[_ [_ [Hm _]]]]; [congruence|].
  unfold frame_compressed_size. rewrite Hm. change (is_skippable_magic ZSTD_MAGICNUMBER) with false.
  rewrite Bool.andb_false_r. rewrite G. cbv zeta.
  unfold df_tail in H. cbv zeta in H.
  destruct (decode_blocks _ _ _ _ _ _ _) as [[out kb]|] eqn:D; [|discriminate].
  destruct (db_bs _ _ _ _ _ _ _ _ D) as [nb ->].
  destruct (_ && _); [discriminate|].
  destruct (fh_checksumFlag h =? 1).
  - destruct (Zlength s - fh_headerSize h - kb <? 4) eqn:E4; [discriminate|].
    replace (Zlength s - (fh_headerSize h + kb) <? 4) with false by (rewrite <- E4; f_equal; lia).
    destruct (negb _); [discriminate|]. congruence.
  - congruence.
Qed.

Lemma df_ext : forall w x k r, frame_compressed_size x = Some k -> 0 <= byte_at x 4 < 256 ->
  decode_frame no_dict w (x ++ r) = decode_frame no_dict w x.
Proof.
  intros w x k r H Hb. unfold frame_compressed_size in H.
  destruct ((Zlength x >=? ZSTD_SKIPPABLEHEADERSIZE) && is_skippable_magic (le_field x 0 4)) eqn:Ea.
  - apply Bool.andb_true_iff in Ea. destruct Ea as [E8 Es]. apply Z.geb_le in E8.
    unfold ZSTD_SKIPPABLEHEADERSIZE in E8. pose proof (Zlength_nonneg r).
    rewrite !df_skip; auto; try (rewrite ?Zlength_app; lia).
    rewrite le_field_app by lia. auto.
  - destruct (get_frame_header x) as [| |h] eqn:G; try discriminate. cbv zeta in H.
    destruct (blocks_size _ _) as [[kb nb]|] eqn:B; [|discriminate].
    destruct (gfh_info _ _ G) as [[_ [E8 [_ [Es _]]]]|[Ht [H5 [Hm [Hs [Hle _]]]]]].
    { unfold ZSTD_SKIPPABLEHEADERSIZE in Ea. rewrite Es in Ea.
      replace (Zlength x >=? 8) with true in Ea by (symmetry; apply Z.geb_le; lia). discriminate. }
    pose proof (fhs_ge6 _ Hb) as H6. rewrite <- Hs in H6.
    destruct (bs_len _ _ _ _ B) as [B3 Bk].
    rewrite Zlength_skipn in B3, Bk by lia.
    pose proof (Zlength_nonneg r).
    assert (G' := gfh_ext x r h G Hb).
    rewrite (df_unfold w x h), (df_unfold w (x ++ r) h); auto; try (rewrite ?Zlength_app; lia).
    destruct (fh_windowSize h >? w); auto. destruct (negb _); auto.
    unfold df_tail. cbv zeta.
    rewrite skipn_app_le by (rewrite Zlength_correct in *; lia).
    rewrite (db_ext_bs _ _ _ _ B).
    rewrite (db_fuel_bs _ _ _ _ B) by (rewrite length_app; lia).
    destruct (decode_blocks _ _ _ _ _ _ _) as [[out kb']|] eqn:D; auto.
    destruct (db_bs _ _ _ _ _ _ _ _ D) as [nb' D']. rewrite B in D'. inversion D'; subst kb' nb'.
    destruct (negb (fh_contentSize h =? ZSTD_CONTENTSIZE_UNKNOWN) && negb (Zlength out =? fh_contentSize h)); auto.
    destruct (fh_checksumFlag h =? 1); auto.
    destruct (Zlength x - (fh_headerSize h + kb) <? 4) eqn:E4; [discriminate|]. apply Z.ltb_ge in E4.
    rewrite Zlength_app.
    replace (Zlength x + Zlength r - fh_headerSize h - kb <? 4) with false by (symmetry; apply Z.ltb_ge; lia).
    replace (Zlength x - fh_headerSize h - kb <? 4) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite le_field_app_max by lia. auto.
Qed.

(* ---------- walks ---------- *)

Definition wfirst (w: Z) (s: list Z) : (Z * list Z * bool) + Zstd.proof.model.Series.tail :=
  if Zlength s <? ZSTD_FRAMEHEADERSIZE_PREFIX then inr (if Zlength s =? 0 then TEnd else TUnk) else
  if is_skippable_magic (le_field s 0 4) then
    match skippable_frame_size s with None => inr TUnk | Some k => inl (k, nil, true) end
  else
    match decode_frame no_dict w s with
    | FOk c k => inl (k, c, false)
    | FDetHdr => inr TDetHdr
    | FDetCk => inr TDetCk
    | FUnk => inr TUnk
    end.

Definition mkrec (off k: Z) (c: list Z) (sk: bool) : frec :=
  {| fr_start := off; fr_size := k; fr_content := c; fr_skippable := sk |}.

Lemma walk_S : forall f w s off, walk (S f) no_dict w s off =
  match wfirst w s with
  | inr t => (nil, t)
  | inl (k, c, sk) => let '(l, t) := walk f no_dict w (skipn (Z.to_nat k) s) (off + k) in (mkrec off k c sk :: l, t)
  end.
Proof.
  intros. unfold wfirst. cbn [walk].
  destruct (Zlength s <? ZSTD_FRAMEHEADERSIZE_PREFIX); auto.
  destruct (is_skippable_magic _); [destruct (skippable_frame_size s)|destruct (decode_frame _ _ _)]; auto.
Qed.

Definition fshift (d: Z) (f: frec) : frec :=
  {| fr_start := d + fr_start f; fr_size := fr_size f; fr_content := fr_content f; fr_skippable := fr_skippable f |}.

Lemma walk_off : forall f w s off,
  walk f no_dict w s off = (map (fshift off) (fst (walk f no_dict w s 0)), snd (walk f no_dict w s 0)).
Proof.
  induction f; intros; [auto|]. rewrite !walk_S.
  destruct (wfirst w s) as [[[k c] sk]|t]; auto.
  rewrite (IHf w _ (off + k)), (IHf w _ (0 + k)). simpl. f_equal. f_equal.
  - unfold fshift, mkrec. simpl. f_equal. lia.
  - rewrite map_map. apply map_ext. intros. unfold fshift. simpl. f_equal. lia.
Qed.

Lemma walk_mono : forall f w s off l t, walk f no_dict w s off = (l, t) -> t <> TUnk ->
  forall f', (f <= f')%nat -> walk f' no_dict w s off = (l, t).
Proof.
  induction f; intros. { simpl in H. inversion H; subst. congruence. }
  destruct f' as [|f']; [lia|]. rewrite walk_S in *.
  destruct (wfirst w s) as [[[k c] sk]|t0]; auto.
  destruct (walk f no_dict w _ _) as [l0 t0] eqn:E. inversion H; subst.
  erewrite IHf; eauto. lia.
Qed.

Lemma walk_len : forall f w s off l t, walk f no_dict w s off = (l, t) -> t <> TUnk -> (length l < f)%nat.
Proof.
  induction f; intros. { simpl in H. inversion H; subst. congruence. }
  rewrite walk_S in H. destruct (wfirst w s) as [[[k c] sk]|t0].
  - destruct (walk f no_dict w _ _) as [l0 t0] eqn:E. inversion H; subst.
    simpl. specialize (IHf _ _ _ _ _ E H0). lia.
  - inversion H; subst. simpl. lia.
Qed.

Lemma walk_loop : forall w s k c sk, wfirst w s = inl (k, c, sk) -> (Z.to_nat k = 0)%nat ->
  forall f off, snd (walk f no_dict w s off) = TUnk.
Proof.
  intros w s k c sk H Hk. induction f; intros; [auto|].
  rewrite walk_S, H, Hk. simpl skipn.
  specialize (IHf (off + k)). destruct (walk f no_dict w s (off + k)). auto.
Qed.

Lemma wfirst_len : forall w s k c sk, wfirst w s = inl (k, c, sk) -> 5 <= Zlength s.
Proof.
  unfold wfirst; intros. destruct (Zlength s <? ZSTD_FRAMEHEADERSIZE_PREFIX) eqn:E; [discriminate|].
  apply Z.ltb_ge in E. unfold ZSTD_FRAMEHEADERSIZE_PREFIX in E. auto.
Qed.

Lemma walk_snd_fuel : forall n s, (length s <= n)%nat -> forall w f1 f2 off1 off2,
  (S (length s) <= f1)%nat -> (S (length s) <= f2)%nat ->
  snd (walk f1 no_dict w s off1) = snd (walk f2 no_dict w s off2).
Proof.
  induction n; intros.
  - destruct f1 as [|f1]; [lia|]. destruct f2 as [|f2]; [lia|].
    rewrite !walk_S. destruct (wfirst w s) as [[[k c] sk]|t] eqn:E; auto.
    apply wfirst_len in E. rewrite Zlength_correct in E. lia.
  - destruct f1 as [|f1]; [lia|]. destruct f2 as [|f2]; [lia|].
    destruct (wfirst w s) as [[[k c] sk]|t] eqn:E.
    + destruct (Nat.eq_dec (Z.to_nat k) 0).
      * rewrite (walk_loop _ _ _ _ _ E e), (walk_loop _ _ _ _ _ E e). auto.
      * rewrite !walk_S, E. pose proof (wfirst_len _ _ _ _ _ E). rewrite Zlength_correct in H2.
        assert (length (skipn (Z.to_nat k) s) < length s)%nat by (rewrite length_skipn; lia).
        specialize (IHn (skipn (Z.to_nat k) s) ltac:(lia) w f1 f2 (off1 + k) (off2 + k) ltac:(lia) ltac:(lia)).
        destruct (walk f1 _ _ _ (off1 + k)), (walk f2 _ _ _ (off2 + k)). simpl in *. auto.
    + rewrite !walk_S, E. auto.
Qed.

Lemma bytes_ok_skipn : forall n l, bytes_ok l -> bytes_ok (skipn n l).
Proof.
  unfold bytes_ok. induction n; intros; auto. destruct l; simpl; auto. inversion H; subst. auto.
Qed.

Lemma bytes_ok_app : forall a b, bytes_ok (a ++ b) <-> bytes_ok a /\ bytes_ok b.
Proof. unfold bytes_ok. intros. apply Forall_app. Qed.

Ltac some_eq H := match type of H with Some ?a = Some ?b => assert (b = a) by congruence end.

Lemma fhs_ge5 : forall fhd, 5 <= fhd_header_size fhd.
Proof.
  intros. unfold fhd_header_size.
  assert (forall n l, Forall (fun v => 0 <= v) l -> 0 <= nth n l 0).
  { induction n; destruct l; simpl; intros; try lia; inversion H; auto. }
  pose proof (H (Z.to_nat (Z.land fhd 3)) [0; 1; 2; 4] ltac:(repeat constructor; lia)).
  pose proof (H (Z.to_nat (Z.shiftr fhd 6)) [0; 2; 4; 8] ltac:(repeat constructor; lia)).
  destruct (land1_cases (Z.shiftr fhd 5)) as [E|E]; rewrite E;
  destruct (_ && _); lia.
Qed.

Lemma sfs_ext : forall s y k, skippable_frame_size s = Some k ->
  skippable_frame_size (s ++ y) = Some k /\ k <= Zlength s.
Proof.
  unfold skippable_frame_size; intros.
  destruct (Zlength s <? ZSTD_SKIPPABLEHEADERSIZE) eqn:E1; [discriminate|]. apply Z.ltb_ge in E1.
  unfold ZSTD_SKIPPABLEHEADERSIZE in *. pose proof (Zlength_nonneg y).
  rewrite le_field_app by lia. rewrite Zlength_app.
  replace (Zlength s + Zlength y <? 8) with false by (symmetry; apply Z.ltb_ge; lia).
  destruct (le_field s 4 4 + 8 >? Zlength s) eqn:E2; [discriminate|]. apply Zgtb_le in E2.
  replace (le_field s 4 4 + 8 >? Zlength s + Zlength y) with false by (symmetry; apply Zgtb_le; lia).
  split; [auto|]. inversion H. lia.
Qed.

Lemma fcs_le : forall s k, frame_compressed_size s = Some k -> k <= Zlength s.
Proof.
  unfold frame_compressed_size; intros.
  destruct (_ && _). { apply (sfs_ext s nil) in H. tauto. }
  destruct (get_frame_header s) as [| |h] eqn:G; try discriminate. cbv zeta in H.
  destruct (blocks_size _ _) as [[kb nb]|] eqn:B; [|discriminate].
  destruct (bs_len _ _ _ _ B) as [B3 Bk].
  destruct (gfh_info _ _ G) as [[_ [H8 [_ [_ [Hs _]]]]]|[_ [_ [_ [Hs [Hle _]]]]]].
  - rewrite Hs in *. rewrite Zlength_skipn in B3, Bk by lia.
    destruct (fh_checksumFlag h =? 1); [destruct (Zlength s - (8 + kb) <? 4) eqn:E4; [discriminate|]; apply Z.ltb_ge in E4|];
    some_eq H; lia.
  - assert (0 <= fh_headerSize h) by (rewrite Hs; pose proof (fhs_ge5 (byte_at s 4)); lia).
    rewrite Zlength_skipn in B3, Bk by lia.
    destruct (fh_checksumFlag h =? 1); [destruct (Zlength s - (fh_headerSize h + kb) <? 4) eqn:E4; [discriminate|]; apply Z.ltb_ge in E4|];
    some_eq H; lia.
Qed.

Lemma wfirst_ext : forall w s k c sk y, wfirst w s = inl (k, c, sk) -> 0 <= byte_at s 4 < 256 ->
  k <= Zlength s /\ forall w2, wfirst w2 (s ++ y) = wfirst w2 s.
Proof.
  intros w s k c sk y H Hb. pose proof (wfirst_len _ _ _ _ _ H) as H5.
  pose proof (Zlength_nonneg y).
  unfold wfirst in *. unfold ZSTD_FRAMEHEADERSIZE_PREFIX in *.
  replace (Zlength s <? 5) with false in * by (symmetry; apply Z.ltb_ge; lia).
  rewrite Zlength_app. replace (Zlength s + Zlength y <? 5) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite le_field_app by lia.
  destruct (is_skippable_magic (le_field s 0 4)).
  - destruct (skippable_frame_size s) as [k'|] eqn:E; [|discriminate].
    destruct (sfs_ext _ y _ E) as [-> Hk]. inversion H; subst. auto.
  - destruct (decode_frame no_dict w s) eqn:E; try discriminate. inversion H; subst.
    pose proof (df_fcs _ _ _ _ E) as F. split; [eapply fcs_le; eauto|].
    intros. rewrite (df_ext w2 s k y F Hb). auto.
Qed.

Lemma wfirst_end : forall w s, wfirst w s = inr TEnd -> s = nil.
Proof.
  unfold wfirst; intros.
  destruct (Zlength s <? ZSTD_FRAMEHEADERSIZE_PREFIX).
  - destruct (Zlength s =? 0) eqn:E; [|discriminate]. apply Z.eqb_eq in E.
    rewrite Zlength_correct in E. destruct s; [auto|simpl in E; lia].
  - destruct (is_skippable_magic _); [destruct (skippable_frame_size s)|destruct (decode_frame _ _ _)]; discriminate.
Qed.

Lemma wfirst_wlim : forall w1 w2 s k c sk, w2 <= w1 -> wfirst w1 s = inl (k, c, sk) ->
  wfirst w2 s = inl (k, c, sk) \/ wfirst w2 s = inr TDetHdr.
Proof.
  unfold wfirst; intros.
  destruct (Zlength s <? ZSTD_FRAMEHEADERSIZE_PREFIX); [discriminate|].
  destruct (is_skippable_magic _); auto.
  destruct (decode_frame no_dict w1 s) eqn:E; try discriminate. inversion H0; subst.
  destruct (df_hdr_inv w1 s) as [h [G [Ht [H9 [H3 [Hw [Hd E']]]]]]]; try congruence.
  rewrite (df_unfold w2 s h G Ht H9 H3).
  destruct (fh_windowSize h >? w2); auto.
  rewrite Hd. simpl. rewrite E in E'. rewrite <- E'. auto.
Qed.

Lemma walk_app : forall f w s off l, walk f no_dict w s off = (l, TEnd) -> bytes_ok s ->
  forall y F, (length l <= F)%nat ->
  walk F no_dict w (s ++ y) off =
    (l ++ fst (walk (F - length l) no_dict w y (off + Zlength s)),
     snd (walk (F - length l) no_dict w y (off + Zlength s))).
Proof.
  induction f; intros w s off l H Hs y F HF; [discriminate|].
  rewrite walk_S in H. destruct (wfirst w s) as [[[k c] sk]|t] eqn:E.
  - destruct (walk f no_dict w (skipn (Z.to_nat k) s) (off + k)) as [l0 t0] eqn:E2.
    inversion H; subst; clear H.
    assert (Hk: Z.to_nat k <> 0%nat).
    { intro Hk. pose proof (walk_loop _ _ _ _ _ E Hk f (off + k)). rewrite Hk in E2. simpl in E2.
      rewrite E2 in H. discriminate. }
    destruct (wfirst_ext _ _ _ _ _ y E (bytes_ok_byte_at _ _ Hs)) as [Hkl Hext].
    destruct F as [|F]; [simpl in HF; lia|]. simpl in HF.
    rewrite walk_S, Hext, E.
    rewrite skipn_app_le by (rewrite Zlength_correct in Hkl; lia).
    rewrite (IHf _ _ _ _ E2 (bytes_ok_skipn _ _ Hs) y F) by lia.
    rewrite Zlength_skipn by lia.
    replace (off + k + (Zlength s - k)) with (off + Zlength s) by lia.
    simpl. auto.
  - inversion H; subst; clear H. apply wfirst_end in E. subst s.
    simpl. rewrite Nat.sub_0_r, Z.add_0_r. destruct (walk F _ _ _ _); auto.
Qed.

Lemma walk_app_wlim : forall f w1 w2 s off l, walk f no_dict w1 s off = (l, TEnd) -> bytes_ok s -> w2 <= w1 ->
  forall y F, (length l <= F)%nat ->
  snd (walk F no_dict w2 (s ++ y) off) = TDetHdr \/
  snd (walk F no_dict w2 (s ++ y) off) = snd (walk (F - length l) no_dict w2 y (off + Zlength s)).
Proof.
  induction f; intros w1 w2 s off l H Hs Hw y F HF; [discriminate|].
  rewrite walk_S in H. destruct (wfirst w1 s) as [[[k c] sk]|t] eqn:E.
  - destruct (walk f no_dict w1 (skipn (Z.to_nat k) s) (off + k)) as [l0 t0] eqn:E2.
    inversion H; subst; clear H.
    assert (Hk: Z.to_nat k <> 0%nat).
    { intro Hk. pose proof (walk_loop _ _ _ _ _ E Hk f (off + k)). rewrite Hk in E2. simpl in E2.
      rewrite E2 in H. discriminate. }
    destruct (wfirst_ext _ _ _ _ _ y E (bytes_ok_byte_at _ _ Hs)) as [Hkl Hext].
    destruct F as [|F]; [simpl in HF; lia|]. simpl in HF.
    rewrite walk_S, Hext.
    destruct (wfirst_wlim _ _ _ _ _ _ Hw E) as [E'|E']; rewrite E'; [|auto].
    rewrite skipn_app_le by (rewrite Zlength_correct in Hkl; lia).
    destruct (IHf _ _ _ _ _ E2 (bytes_ok_skipn _ _ Hs) Hw y F ltac:(lia)) as [IH|IH];
    destruct (walk F no_dict w2 (skipn (Z.to_nat k) s ++ y) (off + k)) eqn:W; simpl in *; auto.
    right. rewrite IH. rewrite Zlength_skipn by lia.
    replace (off + k + (Zlength s - k)) with (off + Zlength s) by lia. auto.
  - inversion H; subst; clear H. apply wfirst_end in E. subst s.
    simpl. rewrite Nat.sub_0_r, Z.add_0_r. auto.
Qed.

(* ---------- series ---------- *)

Lemma series_app_snd : forall w dsin recs y, series_frames no_dict w dsin = (recs, TEnd) -> bytes_ok dsin ->
  snd (series_frames no_dict w (dsin ++ y)) = snd (series_frames no_dict w y).
Proof.
  unfold series_frames. intros.
  pose proof (walk_len _ _ _ _ _ _ H ltac:(discriminate)) as HL.
  rewrite (walk_app _ _ _ _ _ H H0 y (S (length (dsin ++ y)))) by (rewrite length_app; lia).
  cbn [snd]. apply walk_snd_fuel with (n := length y); auto; rewrite length_app in *; lia.
Qed.

Lemma series_app_full : forall w dsin recs y l t, series_frames no_dict w dsin = (recs, TEnd) -> bytes_ok dsin ->
  series_frames no_dict w y = (l, t) -> t <> TUnk ->
  series_frames no_dict w (dsin ++ y) = (recs ++ map (fshift (Zlength dsin)) l, t).
Proof.
  unfold series_frames. intros.
  pose proof (walk_len _ _ _ _ _ _ H ltac:(discriminate)) as HL.
  rewrite (walk_app _ _ _ _ _ H H0 y (S (length (dsin ++ y)))) by (rewrite length_app; lia).
  rewrite walk_off. rewrite (walk_mono _ _ _ _ _ _ H1 H2 (S (length (dsin ++ y)) - length recs))
    by (rewrite length_app; lia).
  cbn [fst snd]. auto.
Qed.

Lemma series_app_wlim : forall dsin recs y, series_frames no_dict no_wlim dsin = (recs, TEnd) -> bytes_ok dsin ->
  snd (series_frames no_dict stream_wlim (dsin ++ y)) = TDetHdr \/
  snd (series_frames no_dict stream_wlim (dsin ++ y)) = snd (series_frames no_dict stream_wlim y).
Proof.
  unfold series_frames. intros.
  pose proof (walk_len _ _ _ _ _ _ H ltac:(discriminate)) as HL.
  destruct (walk_app_wlim _ _ stream_wlim _ _ _ H H0 ltac:(unfold stream_wlim, no_wlim; lia) y
             (S (length (dsin ++ y)))) as [E|E]; [rewrite length_app; lia|auto|].
  right. rewrite E. apply walk_snd_fuel with (n := length y); auto; rewrite length_app in *; lia.
Qed.

(* ---------- bounds on fields of bytes ---------- *)

Lemma le_value_bound : forall l, bytes_ok l -> 0 <= le_value l < 2 ^ (8 * Z.of_nat (length l)).
Proof.
  induction l; intros; cbn [le_value length]; [simpl; lia|]. inversion H; subst. unfold is_byte in H2.
  destruct (IHl H3). rewrite Nat2Z.inj_succ.
  replace (8 * Z.succ (Z.of_nat (length l))) with (8 + 8 * Z.of_nat (length l)) by lia.
  rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256. nia.
Qed.

Lemma bytes_ok_firstn : forall n l, bytes_ok l -> bytes_ok (firstn n l).
Proof.
  unfold bytes_ok. induction n; intros; simpl; auto. destruct l; auto. inversion H; subst. constructor; auto.
Qed.

Lemma le_field_bound : forall s i k, bytes_ok s -> 0 <= k -> 0 <= le_field s i k < 2 ^ (8 * k).
Proof.
  intros. unfold le_field, slice.
  assert (Hb: bytes_ok (firstn (Z.to_nat k) (skipn (Z.to_nat i) s)))
    by (apply bytes_ok_firstn, bytes_ok_skipn; auto).
  destruct (le_value_bound _ Hb). split; auto.
  eapply Z.lt_le_trans; [eauto|]. apply Z.pow_le_mono_r; [lia|].
  rewrite length_firstn. lia.
Qed.

Lemma gfh_ws : forall s h, get_frame_header s = FH_ok h -> bytes_ok s -> fh_windowSize h <= no_wlim.
Proof.
  intros s h H Hb. pose proof (gfh_len _ _ H) as Hn.
  unfold get_frame_header in H. cbv zeta in H.
  replace (Zlength s <? 5) with false in H by (symmetry; apply Z.ltb_ge; lia).
  unfold no_wlim.
  destruct (negb (le_field s 0 4 =? ZSTD_MAGICNUMBER)).
  { destruct (is_skippable_magic _); [|discriminate].
    destruct (Zlength s <? ZSTD_SKIPPABLEHEADERSIZE); [discriminate|]. inversion H; subst. simpl. lia. }
  destruct (Zlength s <? _); [discriminate|].
  destruct (negb _); [discriminate|].
  destruct (_ && _) eqn:Ew; [discriminate|].
  inversion H; subst; clear H. cbn [fh_windowSize].
  pose proof (bytes_ok_byte_at s 5 Hb) as B5.
  destruct (Z.land (Z.shiftr (byte_at s 4) 5) 1 =? 1) eqn:Es.
  - repeat match goal with |- context [if ?b then _ else _] => destruct b end;
    try match goal with |- context [byte_at s ?p] => pose proof (bytes_ok_byte_at s p Hb) end;
    try match goal with |- context [le_field s ?p ?k] => pose proof (le_field_bound s p k Hb ltac:(lia)) end;
    unfold ZSTD_CONTENTSIZE_UNKNOWN in *; simpl in *; lia.
  - destruct (land1_cases (Z.shiftr (byte_at s 4) 5)) as [E|E]; rewrite E in *; [|discriminate].
    simpl in Ew. apply Zgtb_le in Ew. unfold ZSTD_WINDOWLOG_ABSOLUTEMIN, ZSTD_WINDOWLOG_MAX in *.
    set (wl := Z.shiftr (byte_at s 5) 3 + 10) in *.
    assert (0 <= Z.shiftr (byte_at s 5) 3) by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_pos; lia).
    assert (0 <= 2 ^ wl <= 2 ^ 31) by (split; [apply Z.pow_nonneg; lia|apply Z.pow_le_mono_r; lia]).
    assert (0 <= Z.land (byte_at s 5) 7 <= 7).
    { pose proof (Z.land_ones (byte_at s 5) 3 ltac:(lia)) as E7.
      change (Z.ones 3) with 7 in E7. change (2 ^ 3) with 8 in E7. rewrite E7.
      pose proof (Z.mod_pos_bound (byte_at s 5) 8). lia. }
    rewrite (Z.shiftr_div_pow2 (2 ^ wl) 3) by lia. change (2 ^ 3) with 8.
    assert (0 <= 2 ^ wl / 8 <= 2 ^ 31) by (split; [apply Z.div_pos; lia|apply Z.div_le_upper_bound; lia]).
    nia.
Qed.

(* ---------- single frames ---------- *)

Lemma walk_single : forall s c sk, wfirst no_wlim s = inl (Zlength s, c, sk) ->
  series_frames no_dict no_wlim s = ([mkrec 0 (Zlength s) c sk], TEnd).
Proof.
  intros. pose proof (wfirst_len _ _ _ _ _ H) as H5. unfold series_frames. rewrite walk_S, H.
  replace (skipn (Z.to_nat (Zlength s)) s) with (@nil Z)
    by (symmetry; apply skipn_all2; rewrite Zlength_correct; lia).
  rewrite Zlength_correct in H5. destruct (length s) as [|n] eqn:E; [simpl in H5; lia|].
  rewrite walk_S. auto.
Qed.

Lemma le_field_app_r : forall a b i k, 0 <= i -> le_field (a ++ b) (Zlength a + i) k = le_field b i k.
Proof.
  intros. unfold le_field, slice. rewrite skipn_app.
  rewrite Zlength_correct. replace (Z.to_nat (Z.of_nat (length a) + i)) with (length a + Z.to_nat i)%nat by lia.
  rewrite skipn_all2 by lia. simpl. f_equal. f_equal. f_equal. lia.
Qed.

Lemma bp_last_len : forall bsm ws bl ts out, blocks_pre bsm ws bl ts out true -> 3 <= Zlength bl.
Proof.
  intros. inversion H; subst.
  unfold block_res in H1. destruct (cblock_size b) eqn:Ec; [|discriminate].
  apply cblock_size_len in Ec. rewrite Zlength_app. pose proof (Zlength_nonneg bl0). lia.
Qed.

Lemma skip_magic_false : is_skippable_magic ZSTD_MAGICNUMBER = false.
Proof. reflexivity. Qed.

Definition df_fin (h: frame_header) (s: list Z) (r: option (list Z * Z)) : fres :=
  let hs := fh_headerSize h in
  match r with
  | None => FUnk
  | Some (out, k) =>
      if negb (fh_contentSize h =? ZSTD_CONTENTSIZE_UNKNOWN) && negb (Zlength out =? fh_contentSize h)
      then FUnk else
      if fh_checksumFlag h =? 1 then
        (if Zlength s - hs - k <? 4 then FUnk
         else if negb (le_field s (hs + k) 4 =? xxh64 out 0 mod 2 ^ 32) then FDetCk
         else FOk out (hs + k + 4))
      else FOk out (hs + k)
  end.

Lemma df_cur_pre : forall w hdr h r,
  get_frame_header hdr = FH_ok h -> Zlength hdr = fh_headerSize h -> fh_frameType h = 0 ->
  fh_dictID h = 0 -> bytes_ok hdr -> 3 <= Zlength r ->
  decode_frame no_dict w (hdr ++ r) =
    if fh_windowSize h >? w then FDetHdr else
    df_fin h (hdr ++ r) (decode_blocks (length r) dstate_init nil r nil (fh_blockSizeMax h) (fh_windowSize h)).
Proof.
  intros w hdr h r G Hl Ht Hd Hb H3.
  pose proof (bytes_ok_byte_at hdr 4 Hb) as B4.
  pose proof (gfh_ext _ r _ G B4) as G'.
  destruct (gfh_info _ _ G) as [[Ht' _]|[_ [_ [_ [Hs _]]]]]; [congruence|].
  pose proof (fhs_ge6 _ B4).
  rewrite (df_unfold w _ h G' Ht) by (rewrite Zlength_app; lia).
  destruct (fh_windowSize h >? w); auto. rewrite Hd. simpl negb. cbv iota.
  unfold df_tail. cbv zeta. rewrite <- Hl.
  replace (skipn (Z.to_nat (Zlength hdr)) (hdr ++ r)) with r.
  2:{ rewrite skipn_app, Zlength_correct, Nat2Z.id, skipn_all, Nat.sub_diag. auto. }
  unfold df_fin. rewrite <- Hl. auto.
Qed.

Lemma df_cur : forall w hdr h bl ts outc t,
  get_frame_header hdr = FH_ok h -> Zlength hdr = fh_headerSize h -> fh_frameType h = 0 ->
  fh_dictID h = 0 -> bytes_ok hdr ->
  blocks_pre (fh_blockSizeMax h) (fh_windowSize h) bl ts outc false -> 3 <= Zlength (bl ++ t) ->
  exists fuel, (length t <= fuel)%nat /\
    decode_frame no_dict w (hdr ++ bl ++ t) =
    if fh_windowSize h >? w then FDetHdr else
    df_fin h (hdr ++ bl ++ t) (oshift (Zlength bl) (decode_blocks fuel ts nil t outc (fh_blockSizeMax h) (fh_windowSize h))).
Proof.
  intros w hdr h bl ts outc t G Hl Ht Hd Hb Hbp H3.
  destruct (bp_db _ _ _ _ _ _ Hbp eq_refl) as [n [Hn Hdb]].
  exists (length (bl ++ t) - n)%nat. split; [rewrite length_app; lia|].
  rewrite (df_cur_pre w hdr h (bl ++ t)) by auto.
  replace (length (bl ++ t)) with (n + (length (bl ++ t) - n))%nat at 1 by (rewrite length_app; lia).
  rewrite Hdb. auto.
Qed.

Lemma df_cur_last : forall w hdr h bl ts outc t,
  get_frame_header hdr = FH_ok h -> Zlength hdr = fh_headerSize h -> fh_frameType h = 0 ->
  fh_dictID h = 0 -> bytes_ok hdr ->
  blocks_pre (fh_blockSizeMax h) (fh_windowSize h) bl ts outc true ->
  decode_frame no_dict w (hdr ++ bl ++ t) =
    if fh_windowSize h >? w then FDetHdr else df_fin h (hdr ++ bl ++ t) (Some (outc, Zlength bl)).
Proof.
  intros w hdr h bl ts outc t G Hl Ht Hd Hb Hbp.
  pose proof (bp_last_len _ _ _ _ _ Hbp).
  rewrite (df_cur_pre w hdr h (bl ++ t)) by (auto; rewrite Zlength_app; pose proof (Zlength_nonneg t); lia).
  rewrite (bp_db_last _ _ _ _ _ Hbp) by (rewrite length_app; lia). auto.
Qed.

(* ---------- complete frames ---------- *)

Lemma fcs_ok_cond : forall h out, fcs_ok h out ->
  (negb (fh_contentSize h =? ZSTD_CONTENTSIZE_UNKNOWN) && negb (Zlength out =? fh_contentSize h)) = false.
Proof.
  unfold fcs_ok; intros h out [E|E]; rewrite E, Z.eqb_refl; auto. apply Bool.andb_false_r.
Qed.

Lemma cur_complete_b : forall fb fp, bytes_ok fb ->
  cur_rel fb fp -> fp_complete fp = true ->
  exists rec, series_frames no_dict no_wlim fb = ([rec], TEnd) /\ fr_content rec = fp_content fp /\
              fr_start rec = 0 /\ fr_size rec = Zlength fb.
Proof.
  intros fb fp Hb H Hc. destruct fp as [|hb|hdr got|hdr z]; simpl in Hc; try discriminate.
  - unfold cur_rel in H. destruct H as [H8 [Hm [Hlt [Hg [sk [-> Hsk]]]]]]. apply Z.eqb_eq in Hc. subst got.
    unfold ZSTD_SKIPPABLEHEADERSIZE in *. pose proof (Zlength_nonneg sk).
    exists (mkrec 0 (Zlength (hdr ++ sk)) nil true). rewrite (walk_single _ nil true); [repeat split; auto|].
    unfold wfirst. rewrite Zlength_app. unfold ZSTD_FRAMEHEADERSIZE_PREFIX.
    replace (Zlength hdr + Zlength sk <? 5) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite le_field_app by lia. rewrite Hm.
    unfold skippable_frame_size. rewrite Zlength_app, !le_field_app by lia. unfold ZSTD_SKIPPABLEHEADERSIZE.
    replace (Zlength hdr + Zlength sk <? 8) with false by (symmetry; apply Z.ltb_ge; lia).
    replace (le_field hdr 4 4 + 8 >=? 2 ^ 32) with false by (symmetry; rewrite Z.geb_leb; apply Z.leb_gt; lia).
    replace (le_field hdr 4 4 + 8 >? Zlength hdr + Zlength sk) with false by (symmetry; apply Zgtb_le; lia).
    do 3 f_equal. lia.
  - destruct (zp_ph z) eqn:Eph; try discriminate. unfold cur_rel in H. rewrite Eph in H.
    destruct H as [G [Hl [Ht [Hd [outc [last [Hbp [Hfb [-> [Ho [Hf Hck]]]]]]]]]]]. subst fb.
    apply bytes_ok_app in Hb. destruct Hb as [Hbh _].
    pose proof (bytes_ok_byte_at hdr 4 Hbh) as B4.
    destruct (gfh_info _ _ G) as [[Ht' _]|[_ [_ [Hm [Hs _]]]]]; [congruence|].
    pose proof (fhs_ge6 _ B4). pose proof (bp_last_len _ _ _ _ _ Hbp).
    pose proof (Zlength_nonneg (zp_got z)).
    exists (mkrec 0 (Zlength (hdr ++ zp_bl z ++ zp_got z)) outc false).
    rewrite (walk_single _ outc false); [repeat split; auto|].
    unfold wfirst. rewrite !Zlength_app. unfold ZSTD_FRAMEHEADERSIZE_PREFIX.
    replace (Zlength hdr + (Zlength (zp_bl z) + Zlength (zp_got z)) <? 5) with false
      by (symmetry; apply Z.ltb_ge; lia).
    rewrite le_field_app by lia. rewrite Hm, skip_magic_false.
    rewrite (df_cur_last _ _ _ _ _ _ _ G Hl Ht Hd Hbh Hbp).
    replace (fh_windowSize (zp_h z) >? no_wlim) with false by (symmetry; apply Zgtb_le; eapply gfh_ws; eauto).
    unfold df_fin. cbv zeta. rewrite fcs_ok_cond by auto.
    rewrite !Zlength_app.
    destruct Hck as [[Hc0 Hg0]|[Hc1 [Hg4 Hx]]].
    + rewrite Hc0. simpl. rewrite Hg0.
      match goal with |- inl (?A, _, _) = inl (?B, _, _) => replace B with A by (change (Zlength (@nil Z)) with 0; lia) end; reflexivity.
    + rewrite Hc1, Z.eqb_refl.
      replace (Zlength hdr + (Zlength (zp_bl z) + Zlength (zp_got z)) - fh_headerSize (zp_h z) - Zlength (zp_bl z) <? 4)
        with false by (symmetry; apply Z.ltb_ge; lia).
      rewrite app_assoc. replace (fh_headerSize (zp_h z) + Zlength (zp_bl z)) with (Zlength (hdr ++ zp_bl z) + 0)
        by (rewrite Zlength_app; lia).
      rewrite le_field_app_r by lia. rewrite Hx, Z.eqb_refl. simpl.
      match goal with |- inl (?A, _, _) = inl (?B, _, _) => replace B with A by (rewrite ?Zlength_app; lia) end; reflexivity.
Qed.

Lemma frames_done_app_b : forall dsin recs fb fp, bytes_ok dsin -> bytes_ok fb ->
  series_frames no_dict no_wlim dsin = (recs, TEnd) ->
  cur_rel fb fp -> fp_complete fp = true ->
  exists recs', series_frames no_dict no_wlim (dsin ++ fb) = (recs', TEnd) /\
    flat_map fr_content recs' = flat_map fr_content recs ++ fp_content fp /\
    length recs' = S (length recs).
Proof.
  intros dsin recs fb fp Hd Hf H Hc Hcp.
  destruct (cur_complete_b fb fp Hf Hc Hcp) as [rec [E [Ec _]]].
  rewrite (series_app_full _ _ _ _ _ _ H Hd E) by discriminate.
  eexists. split; [eauto|]. split.
  - rewrite flat_map_app. simpl. rewrite app_nil_r. rewrite <- Ec. auto.
  - rewrite length_app. simpl. lia.
Qed.

Lemma dead_of_fdead_b : forall dsin recs x, bytes_ok dsin ->
  series_frames no_dict no_wlim dsin = (recs, TEnd) -> fdead x -> dead (dsin ++ x).
Proof.
  intros dsin recs x Hb H Hx s Hp. apply is_prefix_ex in Hp. destruct Hp as [r ->].
  rewrite <- app_assoc. rewrite (series_app_snd _ _ _ _ H Hb). apply Hx. apply is_prefix_app.
Qed.

Lemma bad_of_fbad_b : forall dsin recs x s, bytes_ok dsin ->
  series_frames no_dict no_wlim dsin = (recs, TEnd) -> fbad x -> is_prefix (dsin ++ x) s ->
  snd (series_frames no_dict stream_wlim s) <> TEnd.
Proof.
  intros dsin recs x s Hb H Hx Hp. apply is_prefix_ex in Hp. destruct Hp as [r ->].
  rewrite <- app_assoc. destruct (series_app_wlim _ _ (x ++ r) H Hb) as [E|E]; rewrite E; [discriminate|].
  apply Hx. apply is_prefix_app.
Qed.

(* ---------- one whole frame ---------- *)

Lemma wfirst_fcs : forall w s k c sk, wfirst w s = inl (k, c, sk) -> frame_compressed_size s = Some k.
Proof.
  unfold wfirst; intros.
  destruct (Zlength s <? ZSTD_FRAMEHEADERSIZE_PREFIX); [discriminate|].
  destruct (is_skippable_magic (le_field s 0 4)) eqn:Es.
  - destruct (skippable_frame_size s) as [k'|] eqn:E; [|discriminate]. inversion H; subst.
    unfold frame_compressed_size. rewrite Es.
    unfold skippable_frame_size in E. destruct (Zlength s <? ZSTD_SKIPPABLEHEADERSIZE) eqn:E8; [discriminate|].
    apply Z.ltb_ge in E8. replace (Zlength s >=? ZSTD_SKIPPABLEHEADERSIZE) with true
      by (symmetry; apply Z.geb_le; lia).
    simpl. unfold skippable_frame_size.
    replace (Zlength s <? ZSTD_SKIPPABLEHEADERSIZE) with false by (symmetry; apply Z.ltb_ge; lia). auto.
  - destruct (decode_frame no_dict w s) eqn:E; try discriminate. inversion H; subst.
    eapply df_fcs; eauto.
Qed.

Lemma fcs_len : forall s k, frame_compressed_size s = Some k -> 5 <= Zlength s.
Proof.
  unfold frame_compressed_size; intros.
  destruct (_ && _) eqn:E.
  - apply Bool.andb_true_iff in E. destruct E as [E _]. apply Z.geb_le in E.
    unfold ZSTD_SKIPPABLEHEADERSIZE in E. lia.
  - destruct (get_frame_header s) eqn:G; try discriminate. eapply gfh_len; eauto.
Qed.

Lemma wfirst_fcs_ext : forall x k r w, frame_compressed_size x = Some k -> 0 <= byte_at x 4 < 256 ->
  wfirst w (x ++ r) = wfirst w x.
Proof.
  intros x k r w H Hb. pose proof (fcs_len _ _ H) as H5. pose proof (Zlength_nonneg r).
  unfold wfirst. unfold ZSTD_FRAMEHEADERSIZE_PREFIX. rewrite Zlength_app.
  replace (Zlength x <? 5) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (Zlength x + Zlength r <? 5) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite le_field_app by lia.
  destruct (is_skippable_magic (le_field x 0 4)) eqn:Es.
  - unfold frame_compressed_size in H. rewrite Es in H.
    destruct (Zlength x >=? ZSTD_SKIPPABLEHEADERSIZE) eqn:E8; simpl in H.
    + destruct (sfs_ext _ r _ H) as [-> _]. rewrite H. auto.
    + rewrite Z.geb_leb, Z.leb_gt in E8. unfold get_frame_header in H. cbv zeta in H.
      replace (Zlength x <? 5) with false in H by (symmetry; apply Z.ltb_ge; lia).
      rewrite skip_not_magic in H by auto. simpl in H. rewrite Es in H.
      rewrite (proj2 (Z.ltb_lt _ _) E8) in H. discriminate.
  - rewrite (df_ext w x k r H Hb). auto.
Qed.

Lemma df_wlim_rev : forall w1 w2 s c k, w2 <= w1 -> decode_frame no_dict w2 s = FOk c k ->
  decode_frame no_dict w1 s = FOk c k.
Proof.
  intros. destruct (df_hdr_inv w2 s) as [h [G [Ht [H9 [H3 [Hw [Hd E]]]]]]]; try congruence.
  rewrite (df_unfold w1 s h G Ht H9 H3).
  replace (fh_windowSize h >? w1) with false by (symmetry; apply Zgtb_le; lia).
  rewrite Hd. simpl. congruence.
Qed.

Lemma wfirst_wlim_rev : forall w1 w2 s k c sk, w2 <= w1 -> wfirst w2 s = inl (k, c, sk) ->
  wfirst w1 s = inl (k, c, sk).
Proof.
  unfold wfirst; intros.
  destruct (Zlength s <? ZSTD_FRAMEHEADERSIZE_PREFIX); [discriminate|].
  destruct (is_skippable_magic _); auto.
  destruct (decode_frame no_dict w2 s) eqn:E; try discriminate.
  rewrite (df_wlim_rev w1 w2 s c0 size H E). auto.
Qed.

Lemma shortcut_ok_b : forall x c,
  frame_compressed_size x = Some (Zlength x) -> decode_series no_dict no_wlim x = SOk c ->
  exists rec, series_frames no_dict no_wlim x = ([rec], TEnd) /\ fr_content rec = c /\
              fr_start rec = 0 /\ fr_size rec = Zlength x.
Proof.
  intros x c H Hd. unfold decode_series in Hd.
  destruct (wfirst no_wlim x) as [[[k c1] sk]|t] eqn:E.
  - pose proof (wfirst_fcs _ _ _ _ _ E) as F. rewrite H in F. inversion F; subst k.
    rewrite (walk_single _ _ _ E) in *. inversion Hd; subst.
    eexists. split; [eauto|]. simpl. rewrite app_nil_r. auto.
  - unfold series_frames in Hd. rewrite walk_S, E in Hd.
    destruct t; try discriminate. apply wfirst_end in E. subst x. discriminate.
Qed.

Lemma shortcut_unk_b : forall x, bytes_ok x ->
  frame_compressed_size x = Some (Zlength x) -> decode_series no_dict no_wlim x = SUnk -> fdead x.
Proof.
  intros x Hb H Hd s Hp. apply is_prefix_ex in Hp. destruct Hp as [r ->].
  unfold decode_series in Hd.
  destruct (wfirst no_wlim x) as [[[k c1] sk]|t] eqn:E.
  - pose proof (wfirst_fcs _ _ _ _ _ E) as F. rewrite H in F. inversion F; subst k.
    rewrite (walk_single _ _ _ E) in Hd. discriminate.
  - unfold series_frames in *. rewrite walk_S, E in Hd. rewrite walk_S.
    rewrite (wfirst_fcs_ext x _ r no_wlim H (bytes_ok_byte_at _ _ Hb)), E.
    destruct t; try discriminate. auto.
Qed.

Lemma shortcut_det_b : forall x, bytes_ok x ->
  frame_compressed_size x = Some (Zlength x) -> decode_series no_dict no_wlim x = SDet -> fbad x.
Proof.
  intros x Hb H Hd s Hp. apply is_prefix_ex in Hp. destruct Hp as [r ->].
  unfold decode_series in Hd.
  destruct (wfirst no_wlim x) as [[[k c1] sk]|t] eqn:E.
  - pose proof (wfirst_fcs _ _ _ _ _ E) as F. rewrite H in F. inversion F; subst k.
    rewrite (walk_single _ _ _ E) in Hd. discriminate.
  - unfold series_frames in *. rewrite walk_S, E in Hd. rewrite walk_S.
    rewrite (wfirst_fcs_ext x _ r stream_wlim H (bytes_ok_byte_at _ _ Hb)).
    destruct (wfirst stream_wlim x) as [[[k c1] sk]|t'] eqn:E'.
    + apply (wfirst_wlim_rev no_wlim) in E'; [|unfold stream_wlim, no_wlim; lia]. congruence.
    + simpl. intro. subst t'. apply wfirst_end in E'. subst x. discriminate.
Qed.

Lemma shortcut_capacity_b : forall x s, bytes_ok x ->
  frame_compressed_size x = Some (Zlength x) -> is_prefix x s ->
  snd (series_frames no_dict stream_wlim s) = TEnd ->
  exists c, decode_series no_dict no_wlim x = SOk c /\
    (forall h, get_frame_header x = FH_ok h -> fh_frameType h = 0 ->
       fh_contentSize h <> ZSTD_CONTENTSIZE_UNKNOWN -> Zlength c = fh_contentSize h).
Proof.
  intros x s Hb H Hp Hs. apply is_prefix_ex in Hp. destruct Hp as [r ->].
  unfold series_frames in Hs. rewrite walk_S in Hs.
  rewrite (wfirst_fcs_ext x _ r stream_wlim H (bytes_ok_byte_at _ _ Hb)) in Hs.
  destruct (wfirst stream_wlim x) as [[[k c1] sk]|t] eqn:E.
  2:{ simpl in Hs. subst t. apply wfirst_end in E. subst x. discriminate. }
  apply (wfirst_wlim_rev no_wlim) in E; [|unfold stream_wlim, no_wlim; lia].
  pose proof (wfirst_fcs _ _ _ _ _ E) as F. rewrite H in F. inversion F; subst k.
  exists c1. split.
  { unfold decode_series. rewrite (walk_single _ _ _ E). simpl. rewrite app_nil_r. auto. }
  intros h G Ht Hu.
  destruct (gfh_info _ _ G) as [[Ht' _]|[_ [_ [Hm _]]]]; [congruence|].
  unfold wfirst in E. destruct (Zlength x <? ZSTD_FRAMEHEADERSIZE_PREFIX); [discriminate|].
  rewrite Hm, skip_magic_false in E.
  destruct (decode_frame no_dict no_wlim x) eqn:D; try discriminate. inversion E; subst.
  destruct (df_hdr_inv no_wlim x) as [h' [G' [_ [_ [_ [_ [_ D']]]]]]]; try congruence.
  rewrite G in G'. inversion G'; subst h'. rewrite D in D'.
  unfold df_tail in D'. cbv zeta in D'.
  destruct (decode_blocks _ _ _ _ _ _ _) as [[out kb]|]; [|discriminate].
  destruct (negb (fh_contentSize h =? ZSTD_CONTENTSIZE_UNKNOWN) && negb (Zlength out =? fh_contentSize h)) eqn:C;
    [discriminate|].
  assert (out = c1).
  { repeat match type of D' with context [if ?b then _ else _] => destruct b end; congruence. }
  subst out. apply Bool.andb_false_iff in C. destruct C as [C|C].
  - apply Bool.negb_false_iff, Z.eqb_eq in C. contradiction.
  - apply Bool.negb_false_iff, Z.eqb_eq in C. auto.
Qed.

(* ---------- frame headers: the first frame of every extension ---------- *)

Lemma skip_char : forall m, is_skippable_magic m = true <-> (m mod 2 ^ 32) / 16 = 25481893.
Proof.
  intros. unfold is_skippable_magic, ZSTD_MAGIC_SKIPPABLE_MASK, ZSTD_MAGIC_SKIPPABLE_START.
  replace 4294967280 with (Z.ldiff (Z.ones 32) (Z.ones 4)) by reflexivity.
  rewrite Z.ldiff_land, Z.land_assoc, <- Z.ldiff_land, Z.ldiff_ones_r, Z.land_ones by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
  rewrite Z.eqb_eq. lia.
Qed.

Lemma le_value_app : forall a b, le_value (a ++ b) = le_value a + 2 ^ (8 * Zlength a) * le_value b.
Proof.
  induction a; intros.
  - cbn [app]. change (Zlength (@nil Z)) with 0. change (le_value []) with 0. change (2 ^ (8 * 0)) with 1. lia.
  - cbn [app le_value]. rewrite IHa. rewrite Zlength_cons.
    replace (8 * Z.succ (Zlength a0)) with (8 + 8 * Zlength a0) by lia.
    rewrite Z.pow_add_r by (pose proof (Zlength_nonneg a0); lia). change (2 ^ 8) with 256. ring.
Qed.

Lemma df_nonmagic : forall w s, le_field s 0 4 <> ZSTD_MAGICNUMBER -> decode_frame no_dict w s = FUnk.
Proof.
  intros. unfold decode_frame. destruct (Zlength s <? _); auto.
  replace (le_field s 0 4 =? ZSTD_MAGICNUMBER) with false by (symmetry; apply Z.eqb_neq; auto). auto.
Qed.

Lemma df_short : forall w s, Zlength s < fhd_header_size (byte_at s 4) + 3 -> decode_frame no_dict w s = FUnk.
Proof.
  intros. unfold decode_frame. destruct (Zlength s <? _); auto. destruct (negb _); auto. cbv zeta.
  unfold ZSTD_blockHeaderSize. replace (Zlength s <? fhd_header_size (byte_at s 4) + 3) with true
    by (symmetry; apply Z.ltb_lt; auto). auto.
Qed.

(* a nonempty series whose first frame is neither skippable nor Ok does not end well *)
Lemma series_not_end : forall w s, s <> nil -> is_skippable_magic (le_field s 0 4) = false ->
  (forall c k, decode_frame no_dict w s <> FOk c k) ->
  snd (series_frames no_dict w s) <> TEnd.
Proof.
  intros w s Hs Hk Hd. unfold series_frames. rewrite walk_S.
  destruct (wfirst w s) as [[[k c] sk]|t] eqn:E.
  - unfold wfirst in E. destruct (Zlength s <? _); [discriminate|]. rewrite Hk in E.
    destruct (decode_frame no_dict w s) eqn:D; try discriminate. exfalso; eapply Hd; eauto.
  - simpl. intro. subst t. apply wfirst_end in E. auto.
Qed.

Lemma series_not_end_unk : forall w s, s <> nil -> is_skippable_magic (le_field s 0 4) = false ->
  decode_frame no_dict w s = FUnk -> snd (series_frames no_dict w s) = TUnk.
Proof.
  intros w s Hs Hk Hd. unfold series_frames. rewrite walk_S.
  unfold wfirst. destruct (Zlength s <? _).
  - destruct (Zlength s =? 0) eqn:E; auto. apply Z.eqb_eq in E. rewrite Zlength_correct in E.
    destruct s; [congruence|simpl in E; lia].
  - rewrite Hk, Hd. auto.
Qed.

Lemma df_bad_hdr : forall w s c k,
  Z.land (byte_at s 4) 8 <> 0 \/
  ((Z.land (Z.shiftr (byte_at s 4) 5) 1 =? 0) &&
   (Z.shiftr (byte_at s 5) 3 + ZSTD_WINDOWLOG_ABSOLUTEMIN >? ZSTD_WINDOWLOG_MAX)) = true ->
  decode_frame no_dict w s <> FOk c k.
Proof.
  intros w s c k H. unfold decode_frame. cbv zeta.
  destruct (Zlength s <? _); [discriminate|]. destruct (negb _); [discriminate|].
  destruct (Zlength s <? _); [discriminate|].
  destruct H as [H|H].
  - replace (Z.land (byte_at s 4) 8 =? 0) with false by (symmetry; apply Z.eqb_neq; auto). discriminate.
  - destruct (negb (Z.land (byte_at s 4) 8 =? 0)); [discriminate|].
    destruct (land1_cases (Z.shiftr (byte_at s 4) 5)) as [E|E]; rewrite E in *; [|discriminate].
    simpl in H. simpl. rewrite H. discriminate.
Qed.

Lemma prefix_arith : forall n lv K, 1 <= n <= 4 -> 0 <= lv < 2 ^ (8 * n) ->
  (lv + 2 ^ (8 * n) * K = ZSTD_MAGICNUMBER ->
   lv + 2 ^ (8 * n) * le_value (skipn (Z.to_nat n) (le_bytes 4 ZSTD_MAGICNUMBER)) = ZSTD_MAGICNUMBER) /\
  (is_skippable_magic (lv + 2 ^ (8 * n) * K) = true ->
   is_skippable_magic (lv + 2 ^ (8 * n) * le_value (skipn (Z.to_nat n) (le_bytes 4 ZSTD_MAGIC_SKIPPABLE_START))) = true).
Proof.
  intros n lv K Hn Hl. rewrite !skip_char. unfold ZSTD_MAGICNUMBER.
  assert (n = 1 \/ n = 2 \/ n = 3 \/ n = 4) as Hc by lia.
  destruct Hc as [-> | [-> | [-> | ->]]].
  - replace (le_value (skipn (Z.to_nat 1) (le_bytes 4 4247762216))) with 16592821 by (vm_compute; reflexivity).
    replace (le_value (skipn (Z.to_nat 1) (le_bytes 4 ZSTD_MAGIC_SKIPPABLE_START))) with 1592618 by (vm_compute; reflexivity).
    change (2 ^ (8 * 1)) with 256 in *. split; intros; Z.div_mod_to_equations; lia.
  - replace (le_value (skipn (Z.to_nat 2) (le_bytes 4 4247762216))) with 64815 by (vm_compute; reflexivity).
    replace (le_value (skipn (Z.to_nat 2) (le_bytes 4 ZSTD_MAGIC_SKIPPABLE_START))) with 6221 by (vm_compute; reflexivity).
    change (2 ^ (8 * 2)) with 65536 in *. split; intros; Z.div_mod_to_equations; lia.
  - replace (le_value (skipn (Z.to_nat 3) (le_bytes 4 4247762216))) with 253 by (vm_compute; reflexivity).
    replace (le_value (skipn (Z.to_nat 3) (le_bytes 4 ZSTD_MAGIC_SKIPPABLE_START))) with 24 by (vm_compute; reflexivity).
    change (2 ^ (8 * 3)) with 16777216 in *. split; intros; Z.div_mod_to_equations; lia.
  - replace (le_value (skipn (Z.to_nat 4) (le_bytes 4 4247762216))) with 0 by (vm_compute; reflexivity).
    replace (le_value (skipn (Z.to_nat 4) (le_bytes 4 ZSTD_MAGIC_SKIPPABLE_START))) with 0 by (vm_compute; reflexivity).
    change (2 ^ (8 * 4)) with 4294967296 in *. split; intros; Z.div_mod_to_equations; lia.
Qed.

Lemma hdr_err_bad_b : forall x, bytes_ok x -> x <> nil -> get_frame_header x = FH_err -> fbad x.
Proof.
  intros x Hb Hx H s Hp. apply is_prefix_ex in Hp. destruct Hp as [r ->].
  assert (Hs: x ++ r <> nil) by (destruct x; [congruence|discriminate]).
  pose proof (Zlength_nonneg r).
  destruct (Z_lt_dec (Zlength x) 5) as [Hn|Hn].
  - (* fewer than 5 bytes: the magic number is already wrong *)
    unfold get_frame_header in H. cbv zeta in H.
    replace (Zlength x <? 5) with true in H by (symmetry; apply Z.ltb_lt; auto).
    assert (Hn0: 0 < Zlength x) by (rewrite Zlength_correct; destruct x; [congruence|simpl; lia]).
    replace (Zlength x >? 0) with true in H by (symmetry; apply Zgtb_gt; lia).
    destruct (negb (magic_prefix x ZSTD_MAGICNUMBER =? ZSTD_MAGICNUMBER) &&
              negb (is_skippable_magic (magic_prefix x ZSTD_MAGIC_SKIPPABLE_START))) eqn:E; [|discriminate].
    apply Bool.andb_true_iff in E. destruct E as [E1 E2].
    apply Bool.negb_true_iff, Z.eqb_neq in E1. apply Bool.negb_true_iff in E2.
    destruct (Z_lt_dec (Zlength (x ++ r)) 5) as [Hl|Hl].
    { unfold series_frames. rewrite walk_S. unfold wfirst, ZSTD_FRAMEHEADERSIZE_PREFIX.
      rewrite (proj2 (Z.ltb_lt _ _) Hl). rewrite Zlength_app.
      replace (Zlength x + Zlength r =? 0) with false by (symmetry; apply Z.eqb_neq; lia). discriminate. }
    rewrite Zlength_app in Hl.
    (* the first 4 bytes of x ++ r: x, then 4 - n bytes of r *)
    assert (Hm: exists K, le_field (x ++ r) 0 4 = le_value x + 2 ^ (8 * Zlength x) * K).
    { unfold le_field, slice. simpl skipn. rewrite firstn_app.
      replace (firstn (Z.to_nat 4) x) with x by (symmetry; apply firstn_all2; rewrite Zlength_correct in Hn; lia).
      rewrite le_value_app. eauto. }
    destruct Hm as [K Hm].
    assert (Hp: forall fill, magic_prefix x fill =
               le_value x + 2 ^ (8 * Zlength x) * le_value (skipn (Z.to_nat (Zlength x)) (le_bytes 4 fill))).
    { intros. unfold magic_prefix. rewrite Z.min_r by lia.
      rewrite firstn_all2 by (rewrite Zlength_correct; lia). apply le_value_app. }
    rewrite Hp in E1, E2. clear Hp.
    destruct (le_value_bound x Hb) as [L0 L1]. rewrite <- Zlength_correct in L1.
    assert (HM: le_field (x ++ r) 0 4 <> ZSTD_MAGICNUMBER /\
                is_skippable_magic (le_field (x ++ r) 0 4) = false).
    { destruct (prefix_arith (Zlength x) (le_value x) K ltac:(lia) ltac:(lia)) as [A1 A2].
      rewrite Hm. split.
      - intro E. apply E1. auto.
      - destruct (is_skippable_magic (le_value x + 2 ^ (8 * Zlength x) * K)) eqn:S; auto.
        specialize (A2 eq_refl). congruence. }
    destruct HM as [HM1 HM2].
    apply series_not_end; auto. intros c k. rewrite df_nonmagic; auto. discriminate.
  - (* a complete prefix: magic number, descriptor, window byte *)
    unfold get_frame_header in H. cbv zeta in H.
    replace (Zlength x <? 5) with false in H by (symmetry; apply Z.ltb_ge; lia).
    destruct (le_field x 0 4 =? ZSTD_MAGICNUMBER) eqn:Em; cbn [negb] in H.
    + apply Z.eqb_eq in Em.
      destruct (Zlength x <? fhd_header_size (byte_at x 4)) eqn:Ef; [discriminate|]. apply Z.ltb_ge in Ef.
      pose proof (fhs_ge6 _ (bytes_ok_byte_at x 4 Hb)).
      apply series_not_end; auto.
      { rewrite le_field_app, Em by lia. reflexivity. }
      intros c k.
      destruct (Z.land (byte_at x 4) 8 =? 0) eqn:Er; cbn [negb] in H.
      * destruct ((Z.land (Z.shiftr (byte_at x 4) 5) 1 =? 0) &&
                  (Z.shiftr (byte_at x 5) 3 + ZSTD_WINDOWLOG_ABSOLUTEMIN >? ZSTD_WINDOWLOG_MAX)) eqn:Ew;
          [|discriminate].
        apply (df_bad_hdr stream_wlim (x ++ r) c k). rewrite (byte_at_app x r 4), (byte_at_app x r 5) by lia. auto.
      * apply (df_bad_hdr stream_wlim (x ++ r) c k). rewrite (byte_at_app x r 4) by lia. left. apply Z.eqb_neq. auto.
    + destruct (is_skippable_magic (le_field x 0 4)) eqn:Es; [destruct (_ <? _); discriminate|].
      apply series_not_end; auto.
      { rewrite le_field_app by lia. auto. }
      intros c k. rewrite df_nonmagic; [discriminate|]. rewrite le_field_app by lia. apply Z.eqb_neq. auto.
Qed.

Lemma hdr_skip_b : forall x h, bytes_ok x ->
  get_frame_header x = FH_ok h -> fh_frameType h = 1 -> Zlength x = fh_headerSize h ->
  Zlength x = ZSTD_SKIPPABLEHEADERSIZE /\ fh_contentSize h = le_field x 4 4 /\
  is_skippable_magic (le_field x 0 4) = true /\
  (le_field x 4 4 + ZSTD_SKIPPABLEHEADERSIZE < 2 ^ 32 -> cur_rel x (FP_skip x 0)).
Proof.
  intros x h Hb G Ht Hl.
  destruct (gfh_info _ _ G) as [[_ [H8 [_ [Hs [Hhs Hc]]]]]|[Ht' _]]; [|congruence].
  unfold ZSTD_SKIPPABLEHEADERSIZE. rewrite Hhs in Hl.
  pose proof (le_field_bound x 4 4 Hb ltac:(lia)).
  split; auto. split; auto. split; auto.
  intros Hlt. unfold cur_rel. unfold ZSTD_SKIPPABLEHEADERSIZE. repeat split; auto; try lia.
  exists nil. rewrite app_nil_r. auto.
Qed.



(* ---------- a Zstandard frame whose current block fails in the model ---------- *)

Definition blk_fails (h: frame_header) (res: option (dstate * list Z * Z * bool)) : Prop :=
  match res with
  | None => True
  | Some (_, out2, _, last) =>
      (last = true /\ ~ fcs_ok h out2) \/
      (fh_contentSize h <> ZSTD_CONTENTSIZE_UNKNOWN /\ fh_contentSize h < Zlength out2)
  end.

Lemma fcs_bad_cond : forall h out, ~ fcs_ok h out ->
  (negb (fh_contentSize h =? ZSTD_CONTENTSIZE_UNKNOWN) && negb (Zlength out =? fh_contentSize h)) = true.
Proof.
  unfold fcs_ok; intros.
  destruct (fh_contentSize h =? ZSTD_CONTENTSIZE_UNKNOWN) eqn:E1; [apply Z.eqb_eq in E1; tauto|].
  destruct (Zlength out =? fh_contentSize h) eqn:E2; [apply Z.eqb_eq in E2; tauto|]. auto.
Qed.

Lemma cblock_none_res : forall st s out bsm ws, cblock_size s = None -> block_res st s out bsm ws = None.
Proof. intros. unfold block_res. rewrite H. auto. Qed.

Lemma zstd_unk_core : forall hdr h bl ts outc rest,
  get_frame_header hdr = FH_ok h -> Zlength hdr = fh_headerSize h -> fh_frameType h = 0 ->
  fh_dictID h = 0 -> bytes_ok hdr ->
  blocks_pre (fh_blockSizeMax h) (fh_windowSize h) bl ts outc false -> 3 <= Zlength rest ->
  (forall r, blk_fails h (block_res ts (rest ++ r) outc (fh_blockSizeMax h) (fh_windowSize h))) ->
  forall w r, decode_frame no_dict w (hdr ++ bl ++ rest ++ r) = if fh_windowSize h >? w then FDetHdr else FUnk.
Proof.
  intros hdr h bl ts outc rest G Hl Ht Hd Hb Hbp H3 Hr w r.
  pose proof (Zlength_nonneg r). pose proof (Zlength_nonneg bl).
  destruct (df_cur w hdr h bl ts outc (rest ++ r) G Hl Ht Hd Hb Hbp) as [fuel [Hf E]];
    [rewrite !Zlength_app; lia|].
  rewrite E. destruct (fh_windowSize h >? w); auto.
  destruct fuel as [|fuel].
  { rewrite length_app in Hf. rewrite Zlength_correct in H3. lia. }
  rewrite db_S_eq. specialize (Hr r).
  destruct (block_res ts (rest ++ r) outc _ _) as [[[[st2 out2] k] last]|]; [|reflexivity].
  simpl in Hr. destruct last.
  - simpl. unfold df_fin. destruct Hr as [[_ Hr]|[Hu Hlt]].
    + rewrite fcs_bad_cond by auto. auto.
    + rewrite fcs_bad_cond; auto. unfold fcs_ok. lia.
  - destruct Hr as [[Hr _]|[Hu Hlt]]; [discriminate|].
    unfold oshift. destruct (decode_blocks fuel st2 nil _ out2 _ _) as [[o k2]|] eqn:D; [|reflexivity].
    destruct (db_out _ _ _ _ _ _ _ _ D) as [d ->]. unfold df_fin.
    rewrite fcs_bad_cond; auto. unfold fcs_ok. rewrite Zlength_app. pose proof (Zlength_nonneg d). lia.
Qed.

Lemma hdr_skip_false : forall hdr h r, get_frame_header hdr = FH_ok h -> fh_frameType h = 0 ->
  is_skippable_magic (le_field (hdr ++ r) 0 4) = false.
Proof.
  intros. destruct (gfh_info _ _ H) as [[Ht _]|[_ [H5 [Hm _]]]]; [congruence|].
  rewrite le_field_app, Hm by lia. reflexivity.
Qed.

Lemma app_ne_nil_l : forall (a b: list Z), a <> nil -> a ++ b <> nil.
Proof. intros. destruct a; [congruence|discriminate]. Qed.

Lemma hdr_ne_nil : forall hdr h, get_frame_header hdr = FH_ok h -> hdr <> nil.
Proof.
  intros. apply gfh_len in H. intro E. subst. change (Zlength (@nil Z)) with 0 in H. lia.
Qed.

Lemma fdead_zstd : forall hdr h bl ts outc rest,
  get_frame_header hdr = FH_ok h -> Zlength hdr = fh_headerSize h -> fh_frameType h = 0 ->
  fh_dictID h = 0 -> bytes_ok hdr ->
  blocks_pre (fh_blockSizeMax h) (fh_windowSize h) bl ts outc false -> 3 <= Zlength rest ->
  (forall r, blk_fails h (block_res ts (rest ++ r) outc (fh_blockSizeMax h) (fh_windowSize h))) ->
  fdead (hdr ++ bl ++ rest).
Proof.
  intros hdr h bl ts outc rest G Hl Ht Hd Hb Hbp H3 Hr s Hp.
  apply is_prefix_ex in Hp. destruct Hp as [r ->]. rewrite <- !app_assoc.
  apply series_not_end_unk.
  - apply app_ne_nil_l. eapply hdr_ne_nil; eauto.
  - eapply hdr_skip_false; eauto.
  - rewrite (zstd_unk_core hdr h bl ts outc rest G Hl Ht Hd Hb Hbp H3 Hr).
    replace (fh_windowSize h >? no_wlim) with false by (symmetry; apply Zgtb_le; eapply gfh_ws; eauto). auto.
Qed.

Lemma fbad_zstd : forall hdr h bl ts outc rest,
  get_frame_header hdr = FH_ok h -> Zlength hdr = fh_headerSize h -> fh_frameType h = 0 ->
  fh_dictID h = 0 -> bytes_ok hdr ->
  blocks_pre (fh_blockSizeMax h) (fh_windowSize h) bl ts outc false -> 3 <= Zlength rest ->
  (forall r, blk_fails h (block_res ts (rest ++ r) outc (fh_blockSizeMax h) (fh_windowSize h))) ->
  fbad (hdr ++ bl ++ rest).
Proof.
  intros hdr h bl ts outc rest G Hl Ht Hd Hb Hbp H3 Hr s Hp.
  apply is_prefix_ex in Hp. destruct Hp as [r ->]. rewrite <- !app_assoc.
  apply series_not_end.
  - apply app_ne_nil_l. eapply hdr_ne_nil; eauto.
  - eapply hdr_skip_false; eauto.
  - intros c k. rewrite (zstd_unk_core hdr h bl ts outc rest G Hl Ht Hd Hb Hbp H3 Hr).
    destruct (_ >? _); discriminate.
Qed.

(* ---------- one block, unfolded ---------- *)

Definition blk_body (st: dstate) (bp: block_props) (body out: list Z) (c bsm ws: Z) : option (dstate * list Z) :=
  if bp_type bp =? 0 then (if c >? bsm then None else Some (st, out ++ body))
  else if bp_type bp =? 1 then
    (if (bp_origSize bp >? bsm) || (c >? bsm) then None
     else Some (st, out ++ repeat (byte_at body 0) (Z.to_nat (bp_origSize bp))))
  else match decode_block st nil out body bsm ws with
       | Some (st', content) => Some (st', out ++ content)
       | None => None
       end.

Lemma br_eq : forall st s out bsm ws c, cblock_size s = Some c -> c <= Zlength s - 3 ->
  block_res st s out bsm ws =
  match blk_body st (block_props_of s) (slice s 3 c) out c bsm ws with
  | None => None
  | Some (st', out') => Some (st', out', 3 + c, bp_last (block_props_of s) =? 1)
  end.
Proof.
  intros. unfold block_res. rewrite H. unfold ZSTD_blockHeaderSize.
  replace (c >? Zlength s - 3) with false by (symmetry; apply Zgtb_le; lia). reflexivity.
Qed.

Lemma slice_hdr : forall bh t k, Zlength bh = 3 -> slice (bh ++ t) 3 k = firstn (Z.to_nat k) t.
Proof.
  intros. unfold slice. rewrite skipn_app. rewrite Zlength_correct in H.
  replace (Z.to_nat 3) with (length bh) by lia. rewrite skipn_all, Nat.sub_diag. auto.
Qed.

Lemma cblock_nonneg : forall s c, bytes_ok s -> cblock_size s = Some c -> 0 <= c.
Proof.
  unfold cblock_size; intros. destruct (Zlength s <? ZSTD_blockHeaderSize); [discriminate|].
  destruct (bp_type _ =? 1); [inversion H0; lia|]. destruct (bp_type _ =? 3); [discriminate|].
  inversion H0; subst. unfold block_props_of. cbn [bp_origSize].
  rewrite Z.shiftr_div_pow2 by lia. pose proof (le_field_bound s 0 3 H ltac:(lia)). apply Z.div_pos; lia.
Qed.

Lemma cblock_types : forall s c, cblock_size s = Some c ->
  (bp_type (block_props_of s) = 1 /\ c = 1) \/
  (bp_type (block_props_of s) <> 1 /\ bp_type (block_props_of s) <> 3 /\ c = bp_origSize (block_props_of s)).
Proof.
  unfold cblock_size; intros. destruct (Zlength s <? ZSTD_blockHeaderSize); [discriminate|].
  destruct (bp_type _ =? 1) eqn:E1; [left; apply Z.eqb_eq in E1; inversion H; auto|].
  destruct (bp_type _ =? 3) eqn:E3; [discriminate|]. right. apply Z.eqb_neq in E1, E3. inversion H; auto.
Qed.

Lemma decode_block_len : forall st hist out b bsm ws st' c,
  decode_block st hist out b bsm ws = Some (st', c) -> Zlength c <= bsm.
Proof.
  unfold decode_block; intros.
  repeat match type of H with
  | context [if ?b then _ else _] => let E := fresh "E" in destruct b eqn:E; try discriminate
  | context [match ?e with _ => _ end] => let E := fresh "E" in destruct e eqn:E; try discriminate
  end.
  all: inversion H; subst; apply Zgtb_le; auto.
Qed.

Lemma decode_block_big : forall st hist out b bsm ws, Zlength b > bsm -> decode_block st hist out b bsm ws = None.
Proof.
  unfold decode_block; intros. replace (Zlength b >? bsm) with true by (symmetry; apply Zgtb_gt; auto). auto.
Qed.

Lemma decode_block_nil : forall st hist out bsm ws, decode_block st hist out nil bsm ws = None.
Proof.
  intros. unfold decode_block. destruct (Zlength [] >? bsm); reflexivity.
Qed.

(* ---------- the model's content is bytes (for cnt_ok's comparison mod 2^32) ---------- *)

Definition huf_ok (o: option Huffman.huf_table) : Prop :=
  match o with None => True | Some t => (length (Huffman.ht_weights t) <= 256)%nat end.

Definition st_ok (st: dstate) : Prop := huf_ok (st_huf st).

Lemma bytes_ok_repeat : forall x n, is_byte x -> bytes_ok (repeat x n).
Proof. unfold bytes_ok. induction n; simpl; auto. Qed.

Lemma is_byte_byte_at : forall l i, bytes_ok l -> is_byte (byte_at l i).
Proof. intros. apply bytes_ok_byte_at. auto. Qed.

Lemma bytes_ok_slice : forall l i k, bytes_ok l -> bytes_ok (slice l i k).
Proof. intros. unfold slice. apply bytes_ok_firstn, bytes_ok_skipn. auto. Qed.

Lemma huf_cells_range : forall t a b, In (a, b) (Huffman.huf_cells t) ->
  0 <= a < Z.of_nat (length (Huffman.ht_weights t)).
Proof.
  intros t a b H. unfold Huffman.huf_cells in H.
  apply in_flat_map in H. destruct H as [w [_ H]].
  apply in_flat_map in H. destruct H as [s [Hs H]].
  apply in_seq in Hs.
  destruct (_ =? w); [|contradiction].
  apply repeat_spec in H. inversion H; subst. lia.
Qed.

Lemma huf_syms_range : forall t V k pos l p, Huffman.huf_decode_syms t V k pos = Some (l, p) ->
  Forall (fun x => 0 <= x < Z.of_nat (length (Huffman.ht_weights t)) \/ x = 0) l.
Proof.
  induction k; intros; simpl in H. { inversion H; subst; constructor. }
  destruct (nth _ (Huffman.huf_cells t) (0, 0)) as [s nb] eqn:E.
  destruct (pos - nb <? 0); [discriminate|].
  destruct (Huffman.huf_decode_syms t V k (pos - nb)) as [[l' p']|] eqn:E2; [|discriminate].
  inversion H; subst. constructor; eauto.
  match type of E with nth ?i _ _ = _ => destruct (lt_dec i (length (Huffman.huf_cells t))) end.
  - left. eapply huf_cells_range. rewrite <- E. apply nth_In. auto.
  - right. rewrite nth_overflow in E by lia. inversion E; auto.
Qed.

Lemma range_bytes : forall t l, (length (Huffman.ht_weights t) <= 256)%nat ->
  Forall (fun x => 0 <= x < Z.of_nat (length (Huffman.ht_weights t)) \/ x = 0) l -> bytes_ok l.
Proof.
  intros. unfold bytes_ok. eapply Forall_impl; [|eauto]. intros a [Ha|Ha]; unfold is_byte; lia.
Qed.

Lemma huf_stream_bytes : forall t s k l, (length (Huffman.ht_weights t) <= 256)%nat ->
  Huffman.huf_decode_stream t s k = Some l -> bytes_ok l.
Proof.
  unfold Huffman.huf_decode_stream; intros.
  destruct (negb _); [discriminate|].
  destruct (Huffman.huf_decode_syms _ _ _ _) as [[l' p]|] eqn:E; [|discriminate].
  destruct p; try discriminate. inversion H0; subst.
  eapply range_bytes; eauto. eapply huf_syms_range; eauto.
Qed.

Lemma huf_4streams_bytes : forall t s k l, (length (Huffman.ht_weights t) <= 256)%nat ->
  Huffman.huf_decode_4streams t s k = Some l -> bytes_ok l.
Proof.
  unfold Huffman.huf_decode_4streams; intros.
  repeat match type of H0 with context [if ?b then _ else _] => destruct b; [discriminate|] end.
  repeat match type of H0 with
  | context [match Huffman.huf_decode_stream ?a ?b ?c with _ => _ end] =>
      let E := fresh "E" in destruct (Huffman.huf_decode_stream a b c) eqn:E; [|discriminate]
  end.
  inversion H0; subst.
  repeat (apply bytes_ok_app; split); eapply huf_stream_bytes; eauto.
Qed.

Lemma huf_desc_len : forall b ws size, bytes_ok b -> Huffman.huf_desc_weights b = Some (ws, size) ->
  (length ws <= 255)%nat.
Proof.
  unfold Huffman.huf_desc_weights; intros.
  destruct (Zlength b <? 1); [discriminate|].
  pose proof (bytes_ok_byte_at b 0 H).
  destruct (byte_at b 0 >=? 128) eqn:E.
  - destruct (Zlength b <? _); [discriminate|]. inversion H0; subst.
    unfold Huffman.huf_direct_weights. rewrite length_map, length_seq. lia.
  - destruct (Zlength b <? _); [discriminate|].
    destruct (Huffman.huf_fse_weights _) as [ws'|] eqn:F; [|discriminate]. inversion H0; subst.
    unfold Huffman.huf_fse_weights in F.
    repeat match type of F with
    | context [match ?e with _ => _ end] => let E := fresh "E" in destruct e eqn:E; try discriminate
    | context [if ?b then _ else _] => let E := fresh "E" in destruct b eqn:E; try discriminate
    end.
    all: inversion F; subst; apply Zgtb_le in E5 || idtac; rewrite Zlength_correct in *; lia.
Qed.

Lemma huf_parse_len : forall b t size, bytes_ok b -> Huffman.huf_parse_desc b = Some (t, size) ->
  (length (Huffman.ht_weights t) <= 256)%nat.
Proof.
  unfold Huffman.huf_parse_desc; intros.
  destruct (Huffman.huf_desc_weights b) as [[ws sz]|] eqn:E; [|discriminate].
  pose proof (huf_desc_len _ _ _ H E).
  repeat match type of H0 with context [if ?c then _ else _] => destruct c; [discriminate|] end.
  inversion H0; subst. simpl. rewrite length_app. simpl. lia.
Qed.

Lemma decode_literals_bytes : forall hprev b bsm lits used huf, bytes_ok b -> huf_ok hprev ->
  decode_literals hprev b bsm = Some (lits, used, huf) -> bytes_ok lits /\ huf_ok huf.
Proof.
  intros hprev b bsm lits used huf Hb Hh H. unfold decode_literals in H.
  repeat match type of H with
  | context [match ?e with _ => _ end] => let E := fresh "E" in destruct e eqn:E; try discriminate
  | context [if ?c then _ else _] => let E := fresh "E" in destruct c eqn:E; try discriminate
  end.
  all: inversion H; subst; clear H.
  all: try (split; [apply bytes_ok_slice; auto | auto]).
  all: try (split; [apply bytes_ok_repeat, is_byte_byte_at; auto | auto]).
  all: match goal with
       | E10: (if _ then _ else _) = Some (?h, ?z2), E12: (if ?b0 then _ else _) = Some ?ll |- _ =>
         assert (Hh': (length (Huffman.ht_weights h) <= 256)%nat);
         [ destruct (Z.land (byte_at b 0) 3 =? 2);
           [ destruct (Huffman.huf_parse_desc _) as [[t hs]|] eqn:P; [|discriminate];
             destruct (_ >=? _); [discriminate|]; inversion E10; subst;
             eapply huf_parse_len; [|exact P]; apply bytes_ok_slice; auto
           | destruct hprev; [|discriminate]; inversion E10; subst; exact Hh ]
         | split; [destruct b0; [eapply huf_stream_bytes | eapply huf_4streams_bytes]; eauto | simpl; auto] ]
       end.
Qed.

Lemma lz_copy_bytes : forall hist out offset ml, bytes_ok hist -> bytes_ok out ->
  bytes_ok (lz_copy hist out offset ml).
Proof.
  intros hist out offset ml. revert out. induction ml; intros; simpl; auto.
  apply IHml; auto. apply bytes_ok_app. split; auto.
  constructor; [|constructor]. apply is_byte_byte_at. apply bytes_ok_app; auto.
Qed.

Lemma exec_seqs_bytes : forall wsize seqs rep hist lits out out' lits' rep',
  bytes_ok hist -> bytes_ok lits -> bytes_ok out ->
  exec_seqs wsize rep hist lits out seqs = Some (out', lits', rep') -> bytes_ok out' /\ bytes_ok lits'.
Proof.
  intros wsize seqs. induction seqs; intros; simpl in H2.
  - inversion H2; subst. auto.
  - destruct (_ >? _); [discriminate|].
    destruct (resolve_offset _ _ _) as [[offset rep2]|]; [|discriminate].
    destruct (_ >? _); [discriminate|]. destruct (_ >? _); [discriminate|].
    eapply IHseqs; [| | |exact H2]; auto.
    + apply bytes_ok_skipn; auto.
    + apply lz_copy_bytes; auto. apply bytes_ok_app. split; auto. apply bytes_ok_firstn; auto.
Qed.

Lemma decode_block_bytes : forall st out b bsm ws st' c, bytes_ok out -> bytes_ok b -> st_ok st ->
  decode_block st nil out b bsm ws = Some (st', c) -> bytes_ok c /\ st_ok st'.
Proof.
  intros st out b bsm ws st' c Ho Hb Hs H. unfold decode_block in H.
  destruct (_ >? _); [discriminate|].
  destruct (decode_literals _ _ _) as [[[lits lused] huf]|] eqn:L; [|discriminate].
  destruct (decode_literals_bytes _ _ _ _ _ _ Hb Hs L) as [Hl Hh].
  destruct (decode_seq_header _ _) as [[[nbSeq tabs] hused]|]; [|discriminate].
  match type of H with context [match ?e with Some _ => _ | None => None end] =>
    destruct e as [seqs|]; [|discriminate] end.
  destruct (exec_seqs _ _ _ _ _ _) as [[[out' lits'] rep']|] eqn:X; [|discriminate].
  destruct (_ >? _); [discriminate|]. inversion H; subst.
  destruct (exec_seqs_bytes _ _ _ _ _ _ _ _ _ ltac:(constructor) Hl Ho X).
  split; [|unfold st_ok; simpl; auto].
  apply bytes_ok_skipn. apply bytes_ok_app; auto.
Qed.

Lemma block_res_bytes : forall st s out bsm ws st' out' k last, bytes_ok s -> bytes_ok out -> st_ok st ->
  block_res st s out bsm ws = Some (st', out', k, last) -> bytes_ok out' /\ st_ok st'.
Proof.
  intros. unfold block_res in H2.
  destruct (cblock_size s); [|discriminate]. destruct (_ >? _); [discriminate|]. cbv zeta in H2.
  destruct (bp_type _ =? 0); [|destruct (bp_type _ =? 1)].
  - destruct (_ >? _); [discriminate|]. inversion H2; subst.
    split; auto. apply bytes_ok_app. split; auto. apply bytes_ok_slice; auto.
  - destruct (_ || _); [discriminate|]. inversion H2; subst.
    split; auto. apply bytes_ok_app. split; auto. apply bytes_ok_repeat, is_byte_byte_at, bytes_ok_slice; auto.
  - destruct (decode_block _ _ _ _ _ _) as [[st2 c2]|] eqn:D; [|discriminate]. inversion H2; subst.
    destruct (decode_block_bytes _ _ _ _ _ _ _ H0 (bytes_ok_slice _ _ _ H) H1 D).
    split; auto. apply bytes_ok_app; auto.
Qed.

Lemma bp_bytes : forall bsm ws bl ts out last, blocks_pre bsm ws bl ts out last -> bytes_ok bl ->
  bytes_ok out /\ st_ok ts.
Proof.
  induction 1; intros.
  - split; [constructor|]. unfold st_ok. simpl. auto.
  - apply bytes_ok_app in H1. destruct H1. destruct (IHblocks_pre H1).
    exact (block_res_bytes _ _ _ _ _ _ _ _ _ H2 H3 H4 H0).
Qed.

Lemma map_mod_bytes : forall l, bytes_ok l -> map (fun b => b mod 2 ^ 32) l = l.
Proof.
  induction l; intros; cbn [map]; auto. inversion H; subst. unfold is_byte in H2.
  rewrite IHl by auto. rewrite Z.mod_small by lia. auto.
Qed.

(* ---------- zunit_step, phase by phase ---------- *)

Lemma fcs_ok_dec : forall h out, fcs_ok h out \/ ~ fcs_ok h out.
Proof.
  unfold fcs_ok; intros.
  destruct (Z.eq_dec (fh_contentSize h) ZSTD_CONTENTSIZE_UNKNOWN); [tauto|].
  destruct (Z.eq_dec (Zlength out) (fh_contentSize h)); tauto.
Qed.

Lemma gfh_ck : forall s h, get_frame_header s = FH_ok h -> fh_checksumFlag h = 0 \/ fh_checksumFlag h = 1.
Proof.
  intros s h H. pose proof (gfh_len _ _ H) as Hn.
  unfold get_frame_header in H. cbv zeta in H.
  replace (Zlength s <? 5) with false in H by (symmetry; apply Z.ltb_ge; lia).
  destruct (negb (le_field s 0 4 =? ZSTD_MAGICNUMBER)).
  { destruct (is_skippable_magic _); [|discriminate].
    destruct (Zlength s <? ZSTD_SKIPPABLEHEADERSIZE); [discriminate|]. inversion H; subst. auto. }
  destruct (Zlength s <? _); [discriminate|]. destruct (negb _); [discriminate|].
  destruct (_ && _); [discriminate|]. inversion H; subst. simpl. apply land1_cases.
Qed.

Lemma step_bhdr : forall hdr z u cnt ts' outc,
  get_frame_header hdr = FH_ok (zp_h z) -> Zlength hdr = fh_headerSize (zp_h z) -> fh_frameType (zp_h z) = 0 ->
  fh_dictID (zp_h z) = 0 -> bytes_ok hdr ->
  (forall c, cblock_size u = Some c -> c <> 0 -> c <= fh_blockSizeMax (zp_h z)) ->
  blocks_pre (fh_blockSizeMax (zp_h z)) (fh_windowSize (zp_h z)) (zp_bl z) (zp_ts z) outc false ->
  zp_ph z = ZP_bhdr -> zp_got z = nil -> zp_out z = outc -> Zlength u = 3 -> bytes_ok u ->
  cur_rel (hdr ++ zp_bl z ++ u) (FP_zstd hdr (zstep z u cnt ts')) \/ fdead (hdr ++ zp_bl z ++ u).
Proof.
  intros hdr z u cnt ts' outc G Hl Ht Hd Hb Hbsm Hbp Eph Eg Eo H3 Hu.
  assert (Hfd: (forall r, blk_fails (zp_h z) (block_res (zp_ts z) (u ++ r) outc
                  (fh_blockSizeMax (zp_h z)) (fh_windowSize (zp_h z)))) -> fdead (hdr ++ zp_bl z ++ u))
    by (intros; eapply fdead_zstd; eauto; lia).
  unfold zstep. rewrite Eph.
  destruct (cblock_size u) as [c|] eqn:Ec.
  2:{ right. apply Hfd. intros r. rewrite cblock_none_res; [exact I|]. rewrite cblock_size_app, Ec by lia. auto. }
  pose proof (cblock_nonneg _ _ Hu Ec) as Hc0.
  destruct (c =? 0) eqn:E0.
  - apply Z.eqb_eq in E0. subst c.
    assert (Er: forall r, block_res (zp_ts z) (u ++ r) outc (fh_blockSizeMax (zp_h z)) (fh_windowSize (zp_h z)) =
                          block_res (zp_ts z) u outc (fh_blockSizeMax (zp_h z)) (fh_windowSize (zp_h z)))
      by (intros; apply (br_app_eq _ _ _ _ _ 0); auto; lia).
    pose proof (br_eq (zp_ts z) u outc (fh_blockSizeMax (zp_h z)) (fh_windowSize (zp_h z)) 0 Ec ltac:(lia)) as Bu.
    replace (slice u 3 0) with (@nil Z) in Bu by reflexivity.
    unfold blk_body in Bu.
    destruct (cblock_types _ _ Ec) as [[Ty1 C1]|[Ty1 [Ty3 Co]]]; [discriminate|].
    destruct (bp_type (block_props_of u) =? 0) eqn:T0.
    + destruct (0 >? fh_blockSizeMax (zp_h z)) eqn:Eb.
      { right. apply Hfd. intro r. rewrite Er, Bu. exact I. }
      rewrite app_nil_r in Bu.
      assert (Hbp': blocks_pre (fh_blockSizeMax (zp_h z)) (fh_windowSize (zp_h z)) (zp_bl z ++ u) (zp_ts z) outc
                      (bp_last (block_props_of u) =? 1)).
      { eapply BPre_snoc; eauto. rewrite Bu, H3. auto. }
      unfold next_phase.
      destruct (bp_last (block_props_of u) =? 1) eqn:L.
      * destruct (fcs_ok_dec (zp_h z) outc) as [Hf|Hf].
        -- left. unfold cur_rel, zp_with. cbn [zp_h zp_bl zp_ts zp_out zp_ph zp_got].
           repeat split; auto. exists outc, true. split; auto.
           destruct (fh_checksumFlag (zp_h z) =? 1) eqn:Ck.
           ++ rewrite !app_nil_r, app_assoc. repeat split; auto.
              all: try (apply Z.eqb_eq; auto); try (change (Zlength (@nil Z)) with 0; lia).
           ++ rewrite !app_nil_r, app_assoc. repeat split; auto. left. split; auto.
              destruct (gfh_ck _ _ G); auto. rewrite H in Ck. discriminate.
        -- right. apply Hfd. intro r. rewrite Er, Bu. simpl. left. auto.
      * left. unfold cur_rel, zp_with. cbn [zp_h zp_bl zp_ts zp_out zp_ph zp_got].
        repeat split; auto. exists outc, false. split; auto. rewrite !app_nil_r, app_assoc. repeat split; auto.
        all: try (change (Zlength (@nil Z)) with 0; unfold ZSTD_blockHeaderSize; lia).
    + replace (bp_type (block_props_of u) =? 1) with false in Bu by (symmetry; apply Z.eqb_neq; auto).
      rewrite decode_block_nil in Bu.
      right. apply Hfd. intro r. rewrite Er, Bu. exact I.
  - apply Z.eqb_neq in E0.
    destruct (Z_le_gt_dec c (fh_blockSizeMax (zp_h z))) as [Hle|Hgt].
    + left. unfold cur_rel, zp_with. cbn [zp_h zp_bl zp_ts zp_out zp_ph zp_got].
      repeat split; auto. exists outc, false. split; auto. rewrite !app_nil_r. repeat split; auto.
      exists c. repeat split; auto; try lia.
      all: try (change (Zlength (@nil Z)) with 0; lia).
      all: destruct (bp_type (block_props_of u) =? 0); auto.
    + right. apply Hfd. intro r. pose proof (Zlength_nonneg r).
      destruct (Z_le_gt_dec c (Zlength (u ++ r) - 3)) as [Hin|Hout].
      * rewrite (br_eq _ _ _ _ _ c) by (auto; rewrite cblock_size_app, Ec by lia; auto).
        unfold blk_body. rewrite block_props_app by lia.
        destruct (cblock_types _ _ Ec) as [[Ty1 C1]|[Ty1 [Ty3 Co]]]; [pose proof (Hbsm c eq_refl E0); lia|].
        destruct (bp_type (block_props_of u) =? 0).
        { replace (c >? fh_blockSizeMax (zp_h z)) with true by (symmetry; apply Zgtb_gt; lia). exact I. }
        replace (bp_type (block_props_of u) =? 1) with false by (symmetry; apply Z.eqb_neq; auto).
        rewrite decode_block_big; [exact I|].
        unfold slice. rewrite Zlength_correct, length_firstn, length_skipn. rewrite Zlength_correct in Hin. lia.
      * unfold block_res. rewrite cblock_size_app, Ec by lia. unfold ZSTD_blockHeaderSize.
        replace (c >? Zlength (u ++ r) - 3) with true by (symmetry; apply Zgtb_gt; lia). exact I.
Qed.

Lemma cur_after_block : forall hdr z bl ts out last,
  get_frame_header hdr = FH_ok (zp_h z) -> Zlength hdr = fh_headerSize (zp_h z) -> fh_frameType (zp_h z) = 0 ->
  fh_dictID (zp_h z) = 0 ->
  blocks_pre (fh_blockSizeMax (zp_h z)) (fh_windowSize (zp_h z)) bl ts out last ->
  (last = true -> fcs_ok (zp_h z) out) ->
  cur_rel (hdr ++ bl)
    (FP_zstd hdr (zp_with z bl ts out
       (if last then (if fh_checksumFlag (zp_h z) =? 1 then ZP_ck else ZP_end) else ZP_bhdr) nil)).
Proof.
  intros hdr z bl ts out last G Hl Ht Hd Hbp Hf.
  unfold cur_rel, zp_with. cbn [zp_h zp_bl zp_ts zp_out zp_ph zp_got].
  repeat split; auto. exists out, last. split; auto.
  destruct last; [destruct (fh_checksumFlag (zp_h z) =? 1) eqn:Ck|]; rewrite app_nil_r; repeat split; auto.
  all: try (change (Zlength (@nil Z)) with 0; unfold ZSTD_blockHeaderSize; lia).
  all: try (apply Z.eqb_eq; auto; fail).
  all: left; split; auto; destruct (gfh_ck _ _ G) as [E|E]; auto; rewrite E in Ck; discriminate.
Qed.

Lemma next_phase_eq : forall h bh, next_phase h bh =
  if (bp_last (block_props_of bh) =? 1) then (if fh_checksumFlag h =? 1 then ZP_ck else ZP_end) else ZP_bhdr.
Proof. reflexivity. Qed.

Lemma next_phase_not_body : forall h bh bh', next_phase h bh <> ZP_body bh'.
Proof. intros. unfold next_phase. destruct (_ =? 1); [destruct (_ =? 1)|]; discriminate. Qed.

Lemma step_body_raw : forall hdr z u cnt ts' outc bh c,
  get_frame_header hdr = FH_ok (zp_h z) -> Zlength hdr = fh_headerSize (zp_h z) -> fh_frameType (zp_h z) = 0 ->
  fh_dictID (zp_h z) = 0 -> bytes_ok hdr ->
  blocks_pre (fh_blockSizeMax (zp_h z)) (fh_windowSize (zp_h z)) (zp_bl z) (zp_ts z) outc false ->
  zp_ph z = ZP_body bh -> Zlength bh = 3 -> cblock_size bh = Some c -> 0 < c <= fh_blockSizeMax (zp_h z) ->
  Zlength (zp_got z) < c -> bp_type (block_props_of bh) = 0 -> zp_out z = outc ++ zp_got z ->
  1 <= Zlength u <= c - Zlength (zp_got z) -> cnt = u -> ts' = zp_ts z ->
  cur_rel (hdr ++ zp_bl z ++ (bh ++ zp_got z) ++ u) (FP_zstd hdr (zstep z u cnt ts')) \/
  fdead (hdr ++ zp_bl z ++ (bh ++ zp_got z) ++ u).
Proof.
  intros hdr z u cnt ts' outc bh c G Hl Ht Hd Hbh Hbp Eph H3 Ec Hc Hg Ty Eo Hu -> ->.
  unfold zstep in *. rewrite Eph in *. rewrite Ty in *. cbn [Z.eqb] in *. rewrite Ec in *.
  rewrite Zlength_app in *.
  destruct (Zlength (zp_got z) + Zlength u =? c) eqn:Ecmp.
  - apply Z.eqb_eq in Ecmp.
    assert (Hb: block_res (zp_ts z) (bh ++ zp_got z ++ u) outc (fh_blockSizeMax (zp_h z)) (fh_windowSize (zp_h z)) =
                Some (zp_ts z, outc ++ zp_got z ++ u, Zlength (bh ++ zp_got z ++ u), bp_last (block_props_of bh) =? 1)).
    { rewrite (br_eq _ _ _ _ _ c); [| rewrite cblock_size_app; auto; lia | rewrite !Zlength_app; lia].
      unfold blk_body. rewrite block_props_app by lia. rewrite Ty. cbn [Z.eqb].
      replace (c >? fh_blockSizeMax (zp_h z)) with false by (symmetry; apply Zgtb_le; lia).
      rewrite slice_hdr by auto. rewrite firstn_all2 by (rewrite length_app; rewrite !Zlength_correct in Ecmp; lia).
      replace (Zlength (bh ++ zp_got z ++ u)) with (3 + c) by (rewrite !Zlength_app; lia). reflexivity. }
    pose proof (BPre_snoc _ _ _ _ _ _ _ _ _ Hbp Hb) as Hbp'.
    assert (Hcase: ((bp_last (block_props_of bh) =? 1) = true -> fcs_ok (zp_h z) (outc ++ zp_got z ++ u)) \/
                   fdead (hdr ++ zp_bl z ++ (bh ++ zp_got z) ++ u)).
    { destruct (fcs_ok_dec (zp_h z) (outc ++ zp_got z ++ u)) as [Hf|Hf]; [left; auto|].
      destruct (bp_last (block_props_of bh) =? 1) eqn:L; [right|left; discriminate].
      rewrite <- (app_assoc bh). eapply fdead_zstd; eauto.
      + rewrite !Zlength_app. pose proof (Zlength_nonneg (zp_got z)). lia.
      + intro r. rewrite (br_app_eq _ _ _ _ _ c);
          [rewrite Hb; simpl; left; auto | rewrite cblock_size_app; auto; lia | rewrite !Zlength_app; lia]. }
    destruct Hcase as [Hf|Hdead]; [left|right; exact Hdead].
    rewrite next_phase_eq. rewrite !app_assoc.
    replace (((hdr ++ zp_bl z) ++ bh) ++ zp_got z) with (hdr ++ zp_bl z ++ bh ++ zp_got z) by (rewrite !app_assoc; auto).
    rewrite <- !app_assoc. rewrite Eo, <- app_assoc.
    apply cur_after_block; auto.
  - apply Z.eqb_neq in Ecmp. left.
    unfold cur_rel, zp_with. cbn [zp_h zp_bl zp_ts zp_out zp_ph zp_got].
    repeat split; auto. exists outc, false. split; auto. split; [rewrite !app_assoc; auto|].
    repeat split; auto. exists c. rewrite Ty. cbn [Z.eqb]. rewrite Zlength_app. repeat split; auto; try lia.
    rewrite Eo, app_assoc. auto.
Qed.


Lemma cms_lift : forall A B C : Prop, B -> A \/ C -> (A /\ B) \/ C.
Proof. tauto. Qed.

Lemma step_body_nraw : forall hdr z u cnt ts' outc bh c,
  get_frame_header hdr = FH_ok (zp_h z) -> Zlength hdr = fh_headerSize (zp_h z) -> fh_frameType (zp_h z) = 0 ->
  fh_dictID (zp_h z) = 0 -> bytes_ok hdr ->
  blocks_pre (fh_blockSizeMax (zp_h z)) (fh_windowSize (zp_h z)) (zp_bl z) (zp_ts z) outc false ->
  zp_ph z = ZP_body bh -> Zlength bh = 3 -> cblock_size bh = Some c -> 0 < c <= fh_blockSizeMax (zp_h z) ->
  (bp_type (block_props_of bh) =? 0) = false -> zp_got z = nil -> zp_out z = outc ->
  Zlength u = c -> cnt_ok z u cnt ts' -> cont_checks z u cnt ->
  bytes_ok outc -> st_ok (zp_ts z) -> bytes_ok u ->
  (cur_rel (hdr ++ zp_bl z ++ bh ++ u) (FP_zstd hdr (zstep z u cnt ts')) /\ cnt_model_some z u) \/
  fdead (hdr ++ zp_bl z ++ bh ++ u).
Proof.
  intros hdr z u cnt ts' outc bh c G Hl Ht Hd Hb Hbp Eph H3 Ec Hc Ty Eg Eo Hu Hcnt Hck Hbo Hst Hbu.
  unfold cont_checks, cnt_ok in *. rewrite Eph in *. rewrite Ty in Hcnt.
  unfold zstep in *. rewrite Eph, Ty in *.
  assert (Hbr: block_res (zp_ts z) (bh ++ u) outc (fh_blockSizeMax (zp_h z)) (fh_windowSize (zp_h z)) =
     match blk_body (zp_ts z) (block_props_of bh) u outc c (fh_blockSizeMax (zp_h z)) (fh_windowSize (zp_h z)) with
     | None => None
     | Some (st', out') => Some (st', out', Zlength (bh ++ u), bp_last (block_props_of bh) =? 1)
     end).
  { rewrite (br_eq _ _ _ _ _ c); [| rewrite cblock_size_app; auto; lia | rewrite Zlength_app; lia].
    rewrite block_props_app by lia. rewrite slice_hdr by auto.
    rewrite firstn_all2 by (rewrite Zlength_correct in Hu; lia).
    replace (Zlength (bh ++ u)) with (3 + c) by (rewrite Zlength_app; lia). auto. }
  assert (Hblk: blk_body (zp_ts z) (block_props_of bh) u outc c (fh_blockSizeMax (zp_h z)) (fh_windowSize (zp_h z))
                = Some (ts', outc ++ cnt) \/
                blk_body (zp_ts z) (block_props_of bh) u outc c (fh_blockSizeMax (zp_h z)) (fh_windowSize (zp_h z))
                = None).
  { unfold blk_body. rewrite Ty.
    destruct (bp_type (block_props_of bh) =? 1).
    - destruct Hcnt as [-> ->]. destruct (_ || _); auto.
    - destruct Hcnt as [Hbc [_ Hdb]]. rewrite Eo in Hdb.
      destruct (decode_block _ _ _ _ _ _) as [[ts2 c2]|] eqn:D; auto. destruct Hdb as [Hm ->].
      destruct (decode_block_bytes _ _ _ _ _ _ _ Hbo Hbu Hst D) as [Hc2 _].
      rewrite !map_mod_bytes in Hm by auto. subst. auto. }
  assert (Hfd: blk_fails (zp_h z) (block_res (zp_ts z) (bh ++ u) outc
                  (fh_blockSizeMax (zp_h z)) (fh_windowSize (zp_h z))) -> fdead (hdr ++ zp_bl z ++ bh ++ u)).
  { intros Hr. eapply fdead_zstd; eauto.
    + rewrite Zlength_app. lia.
    + intro r. rewrite (br_app_eq _ _ _ _ _ c); [apply Hr| |].
      * rewrite cblock_size_app; auto; lia.
      * rewrite Zlength_app. lia. }
  destruct Hblk as [Hblk|Hblk]; rewrite Hblk in Hbr.
  - apply cms_lift.
    { unfold cnt_model_some. rewrite Eph, Eo. intros T2 E. unfold blk_body in Hblk. rewrite T2 in Hblk.
      cbn [Z.eqb] in Hblk. rewrite E in Hblk. discriminate. }
    pose proof (BPre_snoc _ _ _ _ _ _ _ _ _ Hbp Hbr) as Hbp'.
    destruct (fcs_ok_dec (zp_h z) (outc ++ cnt)) as [Hf|Hf].
    + left. rewrite next_phase_eq, Eo.
      apply cur_after_block; auto.
    + destruct (bp_last (block_props_of bh) =? 1) eqn:L.
      * right. apply Hfd. rewrite Hbr. simpl. left. auto.
      * left. rewrite next_phase_eq, Eo, L.
        apply (cur_after_block hdr z (zp_bl z ++ bh ++ u) ts' (outc ++ cnt) false); auto. discriminate.
  - right. apply Hfd. rewrite Hbr. exact I.
Qed.

Lemma step_ck : forall hdr z u cnt ts' outc,
  get_frame_header hdr = FH_ok (zp_h z) -> Zlength hdr = fh_headerSize (zp_h z) -> fh_frameType (zp_h z) = 0 ->
  fh_dictID (zp_h z) = 0 ->
  blocks_pre (fh_blockSizeMax (zp_h z)) (fh_windowSize (zp_h z)) (zp_bl z) (zp_ts z) outc true ->
  zp_ph z = ZP_ck -> zp_out z = outc -> fcs_ok (zp_h z) outc -> fh_checksumFlag (zp_h z) = 1 ->
  Zlength u = 4 -> cont_checks z u cnt ->
  cur_rel (hdr ++ zp_bl z ++ u) (FP_zstd hdr (zstep z u cnt ts')).
Proof.
  intros hdr z u cnt ts' outc G Hl Ht Hd Hbp Eph Eo Hf Hc1 Hu Hck.
  unfold cont_checks in Hck. rewrite Eph in Hck.
  unfold zstep. rewrite Eph. unfold cur_rel, zp_with. cbn [zp_h zp_bl zp_ts zp_out zp_ph zp_got].
  repeat split; auto. exists outc, true. split; auto. repeat split; auto.
  right. repeat split; auto. rewrite Hck, Eo. auto.
Qed.

Lemma zunit_step_b : forall fb hdr z u cnt ts', bytes_ok fb ->
  (forall bh c, zp_ph (zstep z u cnt ts') = ZP_body bh -> cblock_size bh = Some c -> c <= fh_blockSizeMax (zp_h z)) ->
  cur_rel fb (FP_zstd hdr z) ->
  (match zp_ph z with
   | ZP_body bh => bp_type (block_props_of bh) = 0 \/ zp_got z = nil
   | _ => zp_got z = nil
   end) ->
  unit_ok (FP_zstd hdr z) (Zlength u) -> bytes_ok u ->
  cnt_ok z u cnt ts' -> cont_checks z u cnt ->
  (cur_rel (fb ++ u) (FP_zstd hdr (zstep z u cnt ts')) /\ cnt_model_some z u) \/ fdead (fb ++ u).
Proof.
  intros fb hdr z u cnt ts' Hbf Hbsm H Hph Hun Hu Hcnt Hck.
  unfold cur_rel in H. destruct H as [G [Hl [Ht [Hd [outc [last [Hbp [Hfb Hp]]]]]]]].
  subst fb. apply bytes_ok_app in Hbf. destruct Hbf as [Hbh Hbr].
  unfold unit_ok in Hun.
  destruct (zp_ph z) as [|bh| |] eqn:Eph.
  - destruct Hp as [-> [Eo _]]. destruct Hun as [Eg H3]. rewrite Eg, app_nil_r.
    assert (Hb0: forall c, cblock_size u = Some c -> c <> 0 -> c <= fh_blockSizeMax (zp_h z)).
    { intros c Ec Ec0. apply (Hbsm u c); [|exact Ec].
      unfold zstep. rewrite Eph, Ec. replace (c =? 0) with false by (symmetry; apply Z.eqb_neq; auto).
      reflexivity. }
    apply cms_lift; [unfold cnt_model_some; rewrite Eph; exact I|].
    rewrite <- app_assoc. eapply step_bhdr; eauto.
  - destruct Hp as [-> [H3 [c [Ec [Hc [Hg Eo]]]]]]. destruct Hun as [c' [Ec' Hn]].
    rewrite Ec in Ec'. inversion Ec'; subst c'.
    destruct (bp_type (block_props_of bh) =? 0) eqn:T.
    + rewrite <- !app_assoc. apply Z.eqb_eq in T.
      unfold cnt_ok in Hcnt. rewrite Eph in Hcnt. rewrite T in Hcnt. cbn [Z.eqb] in Hcnt.
      destruct Hcnt as [Hc1 Hc2].
      apply cms_lift; [unfold cnt_model_some; rewrite Eph; intro X; rewrite T in X; discriminate|].
      rewrite (app_assoc bh). eapply step_body_raw; eauto.
    + destruct Hph as [Hph|Hph]; [apply Z.eqb_neq in T; contradiction|].
      destruct Hn as [_ Hn]. rewrite Hph, app_nil_r. rewrite <- !app_assoc.
      apply bytes_ok_app in Hbr. destruct Hbr as [Hbl _].
      destruct (bp_bytes _ _ _ _ _ _ Hbp Hbl) as [Hbo Hst].
      eapply step_body_nraw; eauto.
  - destruct Hp as [-> [Eo [Hf [Hc1 _]]]]. destruct Hun as [Eg H4]. left.
    split; [|unfold cnt_model_some; rewrite Eph; exact I].
    rewrite Eg, app_nil_r, <- app_assoc. eapply step_ck; eauto.
  - contradiction.
Qed.


(* ---------- finished frames ---------- *)

(* a complete frame appended to finished frames *)
Lemma frames_done_app : forall dsin recs fb fp, bytes_ok dsin -> bytes_ok fb ->
  series_frames no_dict no_wlim dsin = (recs, TEnd) ->
  cur_rel fb fp -> fp_complete fp = true ->
  exists recs', series_frames no_dict no_wlim (dsin ++ fb) = (recs', TEnd) /\
    flat_map fr_content recs' = flat_map fr_content recs ++ fp_content fp /\
    length recs' = S (length recs).
Proof. exact frames_done_app_b. Qed.

Lemma dead_of_fdead : forall dsin recs x, bytes_ok dsin ->
  series_frames no_dict no_wlim dsin = (recs, TEnd) -> fdead x -> dead (dsin ++ x).
Proof. exact dead_of_fdead_b. Qed.

Lemma bad_of_fbad : forall dsin recs x s, bytes_ok dsin ->
  series_frames no_dict no_wlim dsin = (recs, TEnd) -> fbad x -> is_prefix (dsin ++ x) s ->
  snd (series_frames no_dict stream_wlim s) <> TEnd.
Proof. exact bad_of_fbad_b. Qed.

Lemma dead_app : forall x y, dead x -> dead (x ++ y).
Proof. intros x y H s Hp. apply H. eapply is_prefix_app_l; eauto. Qed.

Lemma fdead_app : forall x y, fdead x -> fdead (x ++ y).
Proof. intros x y H s Hp. apply H. eapply is_prefix_app_l; eauto. Qed.

Lemma fbad_app : forall x y, fbad x -> fbad (x ++ y).
Proof. intros x y H s Hp. apply H. eapply is_prefix_app_l; eauto. Qed.

(* ---------- frame headers (zdss_loadHeader) ---------- *)

Lemma hdr_err_bad : forall x, bytes_ok x -> x <> nil -> get_frame_header x = FH_err -> fbad x.
Proof. exact hdr_err_bad_b. Qed.

(* a complete skippable header *)
Lemma hdr_skip : forall x h, bytes_ok x ->
  get_frame_header x = FH_ok h -> fh_frameType h = 1 -> Zlength x = fh_headerSize h ->
  Zlength x = ZSTD_SKIPPABLEHEADERSIZE /\ fh_contentSize h = le_field x 4 4 /\
  is_skippable_magic (le_field x 0 4) = true /\
  (le_field x 4 4 + ZSTD_SKIPPABLEHEADERSIZE < 2 ^ 32 -> cur_rel x (FP_skip x 0)).
Proof. exact hdr_skip_b. Qed.

(* a complete Zstandard frame header *)

Lemma hdr_zstd_b : forall x h, bytes_ok x ->
  get_frame_header x = FH_ok h -> fh_frameType h = 0 -> Zlength x = fh_headerSize h ->
  (fh_dictID h <> 0 -> fdead x) /\
  (Z.max (fh_windowSize h) 1024 > stream_wlim -> fbad x) /\
  (fh_dictID h = 0 -> cur_rel x (FP_zstd x (z_start h))).
Proof.
  intros x h Hb G Ht Hl.
  destruct (gfh_info _ _ G) as [[Ht' _]|[_ [H5 [Hm [Hs [Hle _]]]]]]; [congruence|].
  pose proof (fhs_ge6 _ (bytes_ok_byte_at x 4 Hb)) as H6.
  assert (Hfr: forall w r, decode_frame no_dict w (x ++ r) = FUnk \/
            (3 <= Zlength r /\ decode_frame no_dict w (x ++ r) =
               if fh_windowSize h >? w then FDetHdr else if negb (fh_dictID h =? 0) then FUnk else df_tail h (x ++ r))).
  { intros w r. pose proof (Zlength_nonneg r). destruct (Z_lt_dec (Zlength r) 3).
    - left. apply df_short. rewrite (byte_at_app x r 4), Zlength_app by lia. lia.
    - right. split; [lia|]. apply df_unfold; auto.
      + apply gfh_ext; auto. apply bytes_ok_byte_at; auto.
      + rewrite Zlength_app. lia.
      + rewrite Zlength_app. lia. }
  assert (Hsk: forall r, is_skippable_magic (le_field (x ++ r) 0 4) = false)
    by (intros; rewrite le_field_app, Hm by lia; reflexivity).
  assert (Hne: forall r, x ++ r <> nil) by (intros r E; apply (f_equal (@length Z)) in E; rewrite length_app in E;
        rewrite Zlength_correct in H5; simpl in E; lia).
  split; [|split].
  - intros Hd s Hp. apply is_prefix_ex in Hp. destruct Hp as [r ->].
    apply series_not_end_unk; auto.
    destruct (Hfr no_wlim r) as [E|[_ E]]; auto. rewrite E.
    replace (fh_windowSize h >? no_wlim) with false by (symmetry; apply Zgtb_le; eapply gfh_ws; eauto).
    replace (fh_dictID h =? 0) with false by (symmetry; apply Z.eqb_neq; auto). auto.
  - intros Hw s Hp. apply is_prefix_ex in Hp. destruct Hp as [r ->].
    apply series_not_end; auto. intros c k.
    destruct (Hfr stream_wlim r) as [E|[_ E]]; rewrite E; [discriminate|].
    replace (fh_windowSize h >? stream_wlim) with true
      by (symmetry; apply Zgtb_gt; unfold stream_wlim in *; lia). discriminate.
  - intros Hd. unfold cur_rel, z_start. cbn [zp_h zp_bl zp_ts zp_out zp_ph zp_got].
    repeat split; auto. exists nil, false. split; [constructor|]. rewrite !app_nil_r. repeat split; auto.
    all: change (Zlength (@nil Z)) with 0; unfold ZSTD_blockHeaderSize; lia.
Qed.

Lemma hdr_zstd : forall x h, bytes_ok x ->
  get_frame_header x = FH_ok h -> fh_frameType h = 0 -> Zlength x = fh_headerSize h ->
  (fh_dictID h <> 0 -> fdead x) /\
  (Z.max (fh_windowSize h) 1024 > stream_wlim -> fbad x) /\
  (fh_dictID h = 0 -> cur_rel x (FP_zstd x (z_start h))).
Proof. exact hdr_zstd_b. Qed.

(* the header loading never sees a complete header of a size other than the one it asked for *)
Lemma hdr_more_size : forall x k, get_frame_header x = FH_more k -> Zlength x < k.
Proof.
  intros x k H. unfold get_frame_header in H. cbv zeta in H.
  destruct (Zlength x <? 5) eqn:E1.
  { apply Z.ltb_lt in E1. destruct (Zlength x >? 0); [destruct (_ && _)|]; inversion H; subst; lia. }
  destruct (negb (le_field x 0 4 =? ZSTD_MAGICNUMBER)).
  { destruct (is_skippable_magic _); [|discriminate].
    destruct (Zlength x <? ZSTD_SKIPPABLEHEADERSIZE) eqn:E; [|discriminate].
    inversion H; subst. apply Z.ltb_lt in E. auto. }
  destruct (Zlength x <? fhd_header_size (byte_at x 4)) eqn:E.
  { inversion H; subst. apply Z.ltb_lt in E. auto. }
  destruct (negb _); [discriminate|]. destruct (_ && _); discriminate.
Qed.

(* loading at most the asked-for bytes: the header is still incomplete, or exactly complete *)
Lemma hdr_more_ext : forall x y k, bytes_ok (x ++ y) ->
  get_frame_header x = FH_more k -> Zlength (x ++ y) <= k ->
  match get_frame_header (x ++ y) with
  | FH_ok h => fh_headerSize h = Zlength (x ++ y)
  | FH_more k' => Zlength (x ++ y) < k'
  | FH_err => True
  end.
Proof.
  intros x y k Hb Hx Hk.
  destruct (get_frame_header (x ++ y)) as [|k'|h] eqn:G; auto.
  { eapply hdr_more_size; eauto. }
  pose proof (Zlength_nonneg y).
  unfold get_frame_header in Hx. cbv zeta in Hx.
  destruct (gfh_info _ _ G) as [[Ht [H8 [Em [Es [Hs _]]]]]|[Ht [H5 [Em [Hs [Hle _]]]]]].
  - (* skippable *)
    destruct (Zlength x <? 5) eqn:E5.
    { destruct (Zlength x >? 0); [destruct (_ && _)|]; inversion Hx; subst; lia. }
    apply Z.ltb_ge in E5. rewrite Zlength_app in *.
    rewrite le_field_app in Em, Es by lia. rewrite Em, Es in Hx. cbn [negb] in Hx.
    destruct (Zlength x <? ZSTD_SKIPPABLEHEADERSIZE); inversion Hx; subst.
    unfold ZSTD_SKIPPABLEHEADERSIZE in *. lia.
  - (* Zstandard *)
    apply bytes_ok_app in Hb. destruct Hb as [Hbx Hby].
    destruct (Zlength x <? 5) eqn:E5.
    { pose proof (fhs_ge6 (byte_at (x ++ y) 4) (bytes_ok_byte_at _ _ (proj2 (bytes_ok_app x y) (conj Hbx Hby)))).
      destruct (Zlength x >? 0); [destruct (_ && _)|]; inversion Hx; subst; lia. }
    apply Z.ltb_ge in E5. rewrite Zlength_app in *.
    rewrite le_field_app in Em by lia. rewrite (byte_at_app x y 4) in Hs by lia.
    rewrite Em, Z.eqb_refl in Hx. cbn [negb] in Hx.
    destruct (Zlength x <? fhd_header_size (byte_at x 4)) eqn:Ef.
    + inversion Hx; subst. lia.
    + destruct (negb _); [discriminate|]. destruct (_ && _); discriminate.
Qed.

(* ---------- skippable frames ---------- *)

Lemma skip_more : forall fb hdr got u,
  cur_rel fb (FP_skip hdr got) -> got + Zlength u <= le_field hdr 4 4 ->
  cur_rel (fb ++ u) (FP_skip hdr (got + Zlength u)).
Proof.
  intros fb hdr got u H Hle. simpl in *.
  destruct H as [H8 [Hm [Hlt [Hg [sk [-> Hsk]]]]]].
  pose proof (Zlength_nonneg u).
  repeat split; auto; try lia.
  exists (sk ++ u). split; [rewrite app_assoc; auto|rewrite Zlength_app; lia].
Qed.

(* ---------- Zstandard frames: units ---------- *)

(* bytes of a unit loaded so far (zdss_load) *)
Lemma zunit_partial : forall fb hdr z g,
  cur_rel fb (FP_zstd hdr z) -> zp_got z = nil ->
  match zp_ph z with
  | ZP_bhdr => Zlength g < ZSTD_blockHeaderSize
  | ZP_body bh => bp_type (block_props_of bh) <> 0 /\ exists c, cblock_size bh = Some c /\ Zlength g < c
  | ZP_ck => Zlength g < 4
  | ZP_end => False
  end ->
  cur_rel (fb ++ g) (FP_zstd hdr (zp_set_got z g)).
Proof.
  intros fb hdr z g H Hg Hph. unfold cur_rel in *.
  destruct H as [G [Hl [Ht [Hd [outc [last [Hbp [Hfb Hp]]]]]]]].
  cbn [zp_h zp_bl zp_ts zp_out zp_ph zp_got zp_set_got].
  repeat split; auto. exists outc, last. split; auto.
  rewrite Hg in Hfb, Hp. subst fb.
  destruct (zp_ph z) as [|bh| |]; try contradiction.
  - destruct Hp as [-> [-> _]]. rewrite app_nil_r, <- ?app_assoc. repeat split; auto.
  - destruct Hph as [Hty [c' [Hc' Hlt]]]. destruct Hp as [-> [H3 [c [Hc [Hcb [_ Ho]]]]]].
    rewrite app_nil_r. rewrite <- !app_assoc. split; auto. split; auto. split; auto.
    exists c. rewrite Hc in Hc'. inversion Hc'; subst c'. repeat split; auto; try lia.
    rewrite Ho. destruct (bp_type (block_props_of bh) =? 0) eqn:E; auto.
    apply Z.eqb_eq in E. contradiction.
  - destruct Hp as [-> [-> [Hf [Hck _]]]]. rewrite app_nil_r, <- ?app_assoc. repeat split; auto.
Qed.

(* a unit decoded by ZSTD_decompressContinue (the unit u: a block header, a block body or a chunk of a raw
   body, the checksum; cnt/ts': what zstd produced): the model agrees, or the frame is dead *)
Lemma zunit_step : forall fb hdr z u cnt ts', bytes_ok fb ->
  (forall bh c, zp_ph (zstep z u cnt ts') = ZP_body bh -> cblock_size bh = Some c -> c <= fh_blockSizeMax (zp_h z)) ->
  cur_rel fb (FP_zstd hdr z) ->
  (match zp_ph z with
   | ZP_body bh => bp_type (block_props_of bh) = 0 \/ zp_got z = nil
   | _ => zp_got z = nil
   end) ->
  unit_ok (FP_zstd hdr z) (Zlength u) -> bytes_ok u ->
  cnt_ok z u cnt ts' -> cont_checks z u cnt ->
  (cur_rel (fb ++ u) (FP_zstd hdr (zstep z u cnt ts')) /\ cnt_model_some z u) \/ fdead (fb ++ u).
Proof. exact zunit_step_b. Qed.

(* the room zstd has for a block's content: a whole block, or the rest of the declared content *)

(* a failure of ZSTD_decompressContinue with room for the block: the frame is bad *)
(* ---------- zunit_err, phase by phase ---------- *)

Lemma br_big : forall st s out bsm ws c, cblock_size s = Some c -> c > bsm -> 0 < bsm ->
  block_res st s out bsm ws = None.
Proof.
  intros. destruct (Z_le_gt_dec c (Zlength s - 3)) as [Hin|Hout].
  - rewrite (br_eq _ _ _ _ _ c) by auto. unfold blk_body.
    destruct (cblock_types _ _ H) as [[Ty1 C1]|[Ty1 [Ty3 Co]]]; [lia|].
    destruct (bp_type (block_props_of s) =? 0).
    { replace (c >? bsm) with true by (symmetry; apply Zgtb_gt; lia). auto. }
    replace (bp_type (block_props_of s) =? 1) with false by (symmetry; apply Z.eqb_neq; auto).
    rewrite decode_block_big; auto.
    unfold slice. rewrite Zlength_correct, length_firstn, length_skipn. rewrite Zlength_correct in Hin. lia.
  - unfold block_res. rewrite H. unfold ZSTD_blockHeaderSize.
    replace (c >? Zlength s - 3) with true by (symmetry; apply Zgtb_gt; lia). auto.
Qed.

Lemma origSize_nonneg : forall s, bytes_ok s -> 0 <= bp_origSize (block_props_of s).
Proof.
  intros. unfold block_props_of. cbn [bp_origSize]. rewrite Z.shiftr_div_pow2 by lia.
  pose proof (le_field_bound s 0 3 H ltac:(lia)). apply Z.div_pos; lia.
Qed.

Lemma err_body_raw : forall hdr z u outc bh c cap,
  get_frame_header hdr = FH_ok (zp_h z) -> Zlength hdr = fh_headerSize (zp_h z) -> fh_frameType (zp_h z) = 0 ->
  fh_dictID (zp_h z) = 0 -> bytes_ok hdr ->
  blocks_pre (fh_blockSizeMax (zp_h z)) (fh_windowSize (zp_h z)) (zp_bl z) (zp_ts z) outc false ->
  Zlength bh = 3 -> cblock_size bh = Some c -> 0 < c <= fh_blockSizeMax (zp_h z) ->
  Zlength (zp_got z) < c -> bp_type (block_props_of bh) = 0 -> zp_out z = outc ++ zp_got z ->
  1 <= Zlength u <= c - Zlength (zp_got z) ->
  (Zlength u > cap \/ (Some (Zlength (zp_got z ++ u)) = cblock_size bh /\
     bp_last (block_props_of bh) = 1 /\ fcs_bad (zp_h z) (zp_out z ++ u))) ->
  cap_room z cap ->
  fbad (hdr ++ zp_bl z ++ (bh ++ zp_got z) ++ u).
Proof.
  intros hdr z u outc bh c cap G Hl Ht Hd Hb Hbp H3 Ec Hc Hg Ty Eo Hu Herr Hroom.
  rewrite <- app_assoc. eapply fbad_zstd; eauto; [rewrite !Zlength_app; pose proof (Zlength_nonneg (zp_got z)); lia|].
  intro r. rewrite <- !app_assoc.
  set (t := bh ++ zp_got z ++ u ++ r).
  assert (Ect: cblock_size t = Some c) by (unfold t; rewrite cblock_size_app; auto; lia).
  pose proof (Zlength_nonneg r). pose proof (Zlength_nonneg (zp_got z)).
  destruct (Z_le_gt_dec c (Zlength t - 3)) as [Hin|Hout].
  2:{ unfold block_res. rewrite Ect. unfold ZSTD_blockHeaderSize.
      replace (c >? Zlength t - 3) with true by (symmetry; apply Zgtb_gt; lia). exact I. }
  rewrite (br_eq _ _ _ _ _ c) by auto. unfold blk_body. unfold t at 1. rewrite block_props_app by lia.
  rewrite Ty. cbn [Z.eqb]. replace (c >? fh_blockSizeMax (zp_h z)) with false by (symmetry; apply Zgtb_le; lia).
  unfold t. rewrite slice_hdr by auto. rewrite app_assoc, firstn_app.
  rewrite firstn_all2 by (rewrite length_app; rewrite !Zlength_correct in *; lia).
  set (d := firstn _ r). unfold blk_fails. rewrite (block_props_app bh) by lia.
  destruct Herr as [Hcap|[Hcmp [L Hbad]]].
  - right. destruct Hroom as [Hr|[Hu' Hr]]; [lia|]. split; auto.
    rewrite Eo, !Zlength_app in Hr. rewrite !Zlength_app. pose proof (Zlength_nonneg d). lia.
  - left. rewrite L. split; auto.
    rewrite Ec in Hcmp. inversion Hcmp as [Hcmp']. rewrite Hcmp' in *.
    replace d with (@nil Z).
    2:{ unfold d. rewrite Zlength_app in Hcmp'. rewrite length_app. rewrite !Zlength_correct in Hcmp'.
        replace (Z.to_nat c - (length (zp_got z) + length u))%nat with O by lia. auto. }
    rewrite app_nil_r, app_assoc, <- Eo. intros Hf. destruct Hbad as [Hb1 Hb2]. destruct Hf; contradiction.
Qed.

Lemma Zlength_repeat : forall (x: Z) n, Zlength (repeat x n) = Z.of_nat n.
Proof. intros. rewrite Zlength_correct, repeat_length. auto. Qed.

Lemma err_body_nraw : forall hdr z u outc bh c cap,
  get_frame_header hdr = FH_ok (zp_h z) -> Zlength hdr = fh_headerSize (zp_h z) -> fh_frameType (zp_h z) = 0 ->
  fh_dictID (zp_h z) = 0 -> bytes_ok hdr -> bytes_ok bh ->
  blocks_pre (fh_blockSizeMax (zp_h z)) (fh_windowSize (zp_h z)) (zp_bl z) (zp_ts z) outc false ->
  Zlength bh = 3 -> cblock_size bh = Some c -> 0 < c <= fh_blockSizeMax (zp_h z) ->
  (bp_type (block_props_of bh) =? 0) = false -> zp_out z = outc -> Zlength u = c ->
  cont_err (FP_zstd hdr z) u cap -> zp_ph z = ZP_body bh -> cap_room z cap ->
  fbad (hdr ++ zp_bl z ++ bh ++ u).
Proof.
  intros hdr z u outc bh c cap G Hl Ht Hd Hb Hbh Hbp H3 Ec Hc Ty Eo Hu Herr Eph Hroom.
  unfold cont_err in Herr. rewrite Eph, Ty, Eo in Herr. cbv zeta in Herr.
  eapply fbad_zstd; eauto; [rewrite Zlength_app; lia|].
  intro r. rewrite (br_app_eq _ _ _ _ _ c); [| rewrite cblock_size_app; auto; lia | rewrite Zlength_app; lia].
  rewrite (br_eq _ _ _ _ _ c); [| rewrite cblock_size_app; auto; lia | rewrite Zlength_app; lia].
  rewrite block_props_app by lia. rewrite slice_hdr by auto.
  rewrite firstn_all2 by (rewrite Zlength_correct in Hu; lia).
  unfold blk_body, blk_fails. rewrite Ty.
  pose proof (Zlength_nonneg outc).
  destruct (bp_type (block_props_of bh) =? 1).
  - replace (c >? fh_blockSizeMax (zp_h z)) with false by (symmetry; apply Zgtb_le; lia).
    rewrite Bool.orb_false_r.
    destruct (bp_origSize (block_props_of bh) >? fh_blockSizeMax (zp_h z)) eqn:Eb; [exact I|].
    apply Zgtb_le in Eb. pose proof (origSize_nonneg _ Hbh).
    rewrite Zlength_app, Zlength_repeat, Z2Nat.id by lia.
    destruct Herr as [Hcap|[Hbig|[L Hbad]]]; [|lia|].
    + right. destruct Hroom as [Hr|[Hu' Hr]]; [lia|]. rewrite Eo in Hr. split; auto. lia.
    + left. rewrite L. split; auto. intros Hf. destruct Hbad as [Hb1 Hb2].
      destruct Hf as [Hf|Hf]; [contradiction|]. apply Hb2.
      rewrite <- Hf, !Zlength_app, !Zlength_repeat, !Z2Nat.id by lia. auto.
  - destruct (decode_block _ _ _ _ _ _) as [[ts2 c2]|] eqn:Edb; [|exact I].
    pose proof (decode_block_len _ _ _ _ _ _ _ _ Edb).
    destruct Herr as [Hcap|[L Hbad]].
    + right. destruct Hroom as [Hr|[Hu' Hr]]; [lia|]. rewrite Eo in Hr. split; auto. rewrite Zlength_app. lia.
    + left. rewrite L. split; auto. intros Hf. destruct Hbad as [Hb1 Hb2]. destruct Hf; contradiction.
Qed.

Lemma err_ck : forall hdr z u outc,
  get_frame_header hdr = FH_ok (zp_h z) -> Zlength hdr = fh_headerSize (zp_h z) -> fh_frameType (zp_h z) = 0 ->
  fh_dictID (zp_h z) = 0 -> bytes_ok hdr ->
  blocks_pre (fh_blockSizeMax (zp_h z)) (fh_windowSize (zp_h z)) (zp_bl z) (zp_ts z) outc true ->
  fcs_ok (zp_h z) outc -> fh_checksumFlag (zp_h z) = 1 -> Zlength u = 4 ->
  le_field u 0 4 <> xxh64 outc 0 mod 2 ^ 32 ->
  fbad (hdr ++ zp_bl z ++ u).
Proof.
  intros hdr z u outc G Hl Ht Hd Hb Hbp Hf Hc1 Hu Hx s Hp.
  apply is_prefix_ex in Hp. destruct Hp as [r ->]. rewrite <- !app_assoc.
  apply series_not_end.
  - apply app_ne_nil_l. eapply hdr_ne_nil; eauto.
  - eapply hdr_skip_false; eauto.
  - intros c k. rewrite (df_cur_last _ _ _ _ _ _ (u ++ r) G Hl Ht Hd Hb Hbp).
    destruct (_ >? _); [discriminate|].
    unfold df_fin. cbv zeta. rewrite fcs_ok_cond by auto. rewrite Hc1. cbn [Z.eqb].
    pose proof (Zlength_nonneg r). pose proof (Zlength_nonneg (zp_bl z)).
    rewrite !Zlength_app.
    replace (Zlength hdr + (Zlength (zp_bl z) + (Zlength u + Zlength r)) - fh_headerSize (zp_h z) - Zlength (zp_bl z) <? 4)
      with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite app_assoc. replace (fh_headerSize (zp_h z) + Zlength (zp_bl z)) with (Zlength (hdr ++ zp_bl z) + 0)
      by (rewrite Zlength_app; lia).
    rewrite le_field_app_r by lia. rewrite le_field_app by lia.
    replace (le_field u 0 4 =? xxh64 outc 0 mod 2 ^ 32) with false by (symmetry; apply Z.eqb_neq; auto).
    discriminate.
Qed.

Lemma err_bhdr : forall hdr z u outc,
  get_frame_header hdr = FH_ok (zp_h z) -> Zlength hdr = fh_headerSize (zp_h z) -> fh_frameType (zp_h z) = 0 ->
  fh_dictID (zp_h z) = 0 -> bytes_ok hdr -> 0 < fh_blockSizeMax (zp_h z) ->
  blocks_pre (fh_blockSizeMax (zp_h z)) (fh_windowSize (zp_h z)) (zp_bl z) (zp_ts z) outc false ->
  Zlength u = 3 ->
  match cblock_size u with None => True | Some c => c > fh_blockSizeMax (zp_h z) end ->
  fbad (hdr ++ zp_bl z ++ u).
Proof.
  intros hdr z u outc G Hl Ht Hd Hb Hbsm Hbp H3 Herr.
  eapply fbad_zstd; eauto; [lia|]. intro r.
  destruct (cblock_size u) as [c|] eqn:Ec.
  - rewrite (br_big _ _ _ _ _ c); [exact I| |auto|auto]. rewrite cblock_size_app, Ec by lia. auto.
  - rewrite cblock_none_res; [exact I|]. rewrite cblock_size_app, Ec by lia. auto.
Qed.

Lemma zunit_err_b : forall fb hdr z u cap, bytes_ok fb -> 0 < fh_blockSizeMax (zp_h z) ->
  cur_rel fb (FP_zstd hdr z) ->
  (match zp_ph z with
   | ZP_body bh => bp_type (block_props_of bh) = 0 \/ zp_got z = nil
   | _ => zp_got z = nil
   end) ->
  unit_ok (FP_zstd hdr z) (Zlength u) -> bytes_ok u ->
  cont_err (FP_zstd hdr z) u cap -> cap_room z cap ->
  fbad (fb ++ u).
Proof.
  intros fb hdr z u cap Hbf Hbsm H Hph Hun Hu Herr Hroom.
  unfold cur_rel in H. destruct H as [G [Hl [Ht [Hd [outc [last [Hbp [Hfb Hp]]]]]]]].
  subst fb. apply bytes_ok_app in Hbf. destruct Hbf as [Hbh Hbr].
  unfold unit_ok in Hun.
  destruct (zp_ph z) as [|bh| |] eqn:Eph.
  - destruct Hp as [-> [Eo _]]. destruct Hun as [Eg H3]. rewrite Eg, app_nil_r, <- app_assoc.
    unfold cont_err in Herr. rewrite Eph in Herr.
    eapply err_bhdr; eauto.
  - destruct Hp as [-> [H3 [c [Ec [Hc [Hg Eo]]]]]]. destruct Hun as [c' [Ec' Hn]].
    rewrite Ec in Ec'. inversion Ec'; subst c'.
    apply bytes_ok_app in Hbr. destruct Hbr as [_ Hbr]. apply bytes_ok_app in Hbr. destruct Hbr as [Hbb _].
    destruct (bp_type (block_props_of bh) =? 0) eqn:T.
    + replace ((hdr ++ zp_bl z ++ bh ++ zp_got z) ++ u) with (hdr ++ zp_bl z ++ (bh ++ zp_got z) ++ u)
        by (rewrite !app_assoc; auto).
      apply Z.eqb_eq in T.
      unfold cont_err in Herr. rewrite Eph in Herr. cbv zeta in Herr. rewrite T in Herr. cbn [Z.eqb] in Herr.
      eapply err_body_raw; eauto.
    + destruct Hph as [Hph|Hph]; [apply Z.eqb_neq in T; contradiction|].
      destruct Hn as [_ Hn]. rewrite Hph, app_nil_r. rewrite <- !app_assoc.
      eapply err_body_nraw; eauto.
  - destruct Hp as [-> [Eo [Hf [Hc1 _]]]]. destruct Hun as [Eg H4].
    rewrite Eg, app_nil_r, <- app_assoc.
    unfold cont_err in Herr. rewrite Eph, Eo in Herr.
    eapply err_ck; eauto.
  - contradiction.
Qed.

Lemma zunit_err : forall fb hdr z u cap, bytes_ok fb -> 0 < fh_blockSizeMax (zp_h z) ->
  cur_rel fb (FP_zstd hdr z) ->
  (match zp_ph z with
   | ZP_body bh => bp_type (block_props_of bh) = 0 \/ zp_got z = nil
   | _ => zp_got z = nil
   end) ->
  unit_ok (FP_zstd hdr z) (Zlength u) -> bytes_ok u ->
  cont_err (FP_zstd hdr z) u cap -> cap_room z cap ->
  fbad (fb ++ u).
Proof. exact zunit_err_b. Qed.

(* a complete frame is decoded by the model *)
Lemma cur_complete : forall fb fp, bytes_ok fb ->
  cur_rel fb fp -> fp_complete fp = true ->
  exists rec, series_frames no_dict no_wlim fb = ([rec], TEnd) /\ fr_content rec = fp_content fp /\
              fr_start rec = 0 /\ fr_size rec = Zlength fb.
Proof. exact cur_complete_b. Qed.

(* ---------- the single-pass shortcut (one whole frame x decoded by ZSTD_decompress_usingDDict) ---------- *)

Lemma shortcut_ok : forall x c,
  frame_compressed_size x = Some (Zlength x) -> decode_series no_dict no_wlim x = SOk c ->
  exists rec, series_frames no_dict no_wlim x = ([rec], TEnd) /\ fr_content rec = c /\
              fr_start rec = 0 /\ fr_size rec = Zlength x.
Proof. exact shortcut_ok_b. Qed.

Lemma shortcut_unk : forall x, bytes_ok x ->
  frame_compressed_size x = Some (Zlength x) -> decode_series no_dict no_wlim x = SUnk -> fdead x.
Proof. exact shortcut_unk_b. Qed.

Lemma shortcut_det : forall x, bytes_ok x ->
  frame_compressed_size x = Some (Zlength x) -> decode_series no_dict no_wlim x = SDet -> fbad x.
Proof. exact shortcut_det_b. Qed.

(* a frame the model decodes with the streaming limit is decoded without it, to the same content *)
Lemma shortcut_capacity : forall x s, bytes_ok x ->
  frame_compressed_size x = Some (Zlength x) -> is_prefix x s ->
  snd (series_frames no_dict stream_wlim s) = TEnd ->
  exists c, decode_series no_dict no_wlim x = SOk c /\
    (forall h, get_frame_header x = FH_ok h -> fh_frameType h = 0 ->
       fh_contentSize h <> ZSTD_CONTENTSIZE_UNKNOWN -> Zlength c = fh_contentSize h).
Proof. exact shortcut_capacity_b. Qed.

(* all of the above, for a check (Print Assumptions on it would show any lemma left unproved) *)
Lemma stream_model_facts : True.
Proof.
  pose proof frames_done_app as _.
  pose proof dead_of_fdead as _.
  pose proof bad_of_fbad as _.
  pose proof dead_app as _.
  pose proof fdead_app as _.
  pose proof fbad_app as _.
  pose proof hdr_err_bad as _.
  pose proof hdr_skip as _.
  pose proof hdr_zstd as _.
  pose proof hdr_more_size as _.
  pose proof hdr_more_ext as _.
  pose proof skip_more as _.
  pose proof zunit_partial as _.
  pose proof zunit_step as _.
  pose proof zunit_err as _.
  pose proof cur_complete as _.
  pose proof shortcut_ok as _.
  pose proof shortcut_unk as _.
  pose proof shortcut_det as _.
  pose proof shortcut_capacity as _.
  exact I.
Qed.
