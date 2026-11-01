(* The streaming model facts of pro/P3* ported to the strict stream model (dbs dw: blocks decoder of the dmode;
   base_rel3 fp_ok). *)
(* FS3 streaming model facts: basic helpers, ported from v2 src/proof/dec/FS/StreamModelFacts.v; blocks behind a history
   hist, from a start state ts0. *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Block Zstd.proof.model.Xxh64 Zstd.proof.model.Info Zstd.proof.model.Series Zstd.proof.model.StreamModel Zstd.proof.model.Params Zstd.proof.model.ParamsH.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Require Import Zstd.proof.dec.v3.FS.stream.S3ModelDefs.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope bool_scope.


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

(* the blocks decoder of a dmode (Params.decode_frame_m): with the dictionary window rule or Block.v's *)
Definition dbs (dw: bool) : nat -> dstate -> list Z -> list Z -> list Z -> Z -> Z -> option (list Z * Z) :=
  if dw then decode_blocks_w else decode_blocks.

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

Section Blocks.
Variable dw : bool.
Variable hist : list Z.
Variable ts0 : dstate.

Lemma db_S_eq : forall st s out bsm ws f,
  dbs dw (S f) st hist s out bsm ws =
  match block_res dw st hist s out bsm ws with
  | None => None
  | Some (st', out', k, last) =>
      if last then Some (out', k) else oshift k (dbs dw f st' hist (skipn (Z.to_nat k) s) out' bsm ws)
  end.
Proof.
  intros. unfold block_res, dbs, dec_block. destruct dw; cbn [decode_blocks decode_blocks_w];
  destruct (cblock_size s) as [c|]; auto.
  all: try (destruct (c >? Zlength s - ZSTD_blockHeaderSize); auto; cbv zeta;
  match goal with |- match ?e with None => None | Some _ => _ end = _ => destruct e as [[st2 out2]|] end; auto).
Qed.

Lemma br_step : forall st s out bsm ws st' out' k last f,
  block_res dw st hist s out bsm ws = Some (st', out', k, last) ->
  dbs dw (S f) st hist s out bsm ws =
    if last then Some (out', k) else oshift k (dbs dw f st' hist (skipn (Z.to_nat k) s) out' bsm ws).
Proof. intros. rewrite db_S_eq, H. auto. Qed.

Lemma br_none : forall st s out bsm ws f,
  block_res dw st hist s out bsm ws = None -> dbs dw (S f) st hist s out bsm ws = None.
Proof. intros. rewrite db_S_eq, H. auto. Qed.

Lemma slice_app' : forall x r i k, 0 <= i -> i + k <= Zlength x ->
  slice (x ++ r) i k = slice x i k.
Proof.
  intros. destruct (Z_lt_dec k 0).
  - unfold slice. replace (Z.to_nat k) with O by lia. auto.
  - apply slice_app; lia.
Qed.

Lemma br_app : forall st s out bsm ws res t,
  block_res dw st hist s out bsm ws = Some res -> block_res dw st hist (s ++ t) out bsm ws = Some res.
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
  block_res dw st hist s out bsm ws = Some (st', out', k, last) -> k <= Zlength s.
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
  block_res dw st hist s out bsm ws = Some (st', out', k, last) -> exists d, out' = out ++ d.
Proof.
  intros. unfold block_res in H.
  destruct (cblock_size s) as [c|] eqn:Ec; [|discriminate].
  destruct (c >? Zlength s - ZSTD_blockHeaderSize) eqn:E; [discriminate|]. cbv zeta in *.
  destruct (bp_type _ =? 0); [|destruct (bp_type _ =? 1)].
  - destruct (c >? bsm); [discriminate|]. inversion H; subst. eauto.
  - destruct ((bp_origSize _ >? bsm) || _); [discriminate|]. inversion H; subst. eauto.
  - destruct (dec_block dw _ _ _ _ _ _) as [[st2 c2]|]; [|discriminate]. inversion H; subst. eauto.
Qed.

Lemma db_out : forall f st s out bsm ws o k,
  dbs dw f st hist s out bsm ws = Some (o, k) -> exists d, o = out ++ d.
Proof.
  induction f; intros; [destruct dw; discriminate|].
  destruct (block_res dw st hist s out bsm ws) as [[[[st' out'] k1] last]|] eqn:Eb.
  - rewrite (br_step _ _ _ _ _ _ _ _ _ f Eb) in H. destruct (br_out _ _ _ _ _ _ _ _ _ Eb) as [d1 ->].
    destruct last; [inversion H; subst; eauto|].
    unfold oshift in H. destruct (dbs dw f st' hist _ _ _ _) as [[o2 k2]|] eqn:E2; [|discriminate].
    inversion H; subst. destruct (IHf _ _ _ _ _ _ _ E2) as [d2 ->]. exists (d1 ++ d2). rewrite app_assoc. auto.
  - rewrite br_none in H by auto. discriminate.
Qed.

(* the complete blocks of a frame *)
Lemma bp_db : forall bsm ws bl ts outc last, blocks_pre dw hist bsm ws ts0 bl ts outc last -> last = false ->
  exists n, (n <= length bl)%nat /\ forall fuel t,
    dbs dw (n + fuel) ts0 hist (bl ++ t) nil bsm ws =
    oshift (Zlength bl) (dbs dw fuel ts hist t outc bsm ws).
Proof.
  induction 1; intros.
  - exists O. split; auto. intros. simpl. unfold oshift.
    destruct (dbs dw fuel _ _ _ _ _ _) as [[o k]|]; auto.
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
    unfold oshift. destruct (dbs dw fuel ts' hist t out' bsm ws) as [[o k]|]; auto.
    rewrite Zlength_app. f_equal. f_equal. lia.
Qed.

Lemma bp_db_last : forall bsm ws bl ts outc, blocks_pre dw hist bsm ws ts0 bl ts outc true ->
  forall fuel t, (length bl <= fuel)%nat ->
    dbs dw fuel ts0 hist (bl ++ t) nil bsm ws = Some (outc, Zlength bl).
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
  block_res dw st hist s out bsm ws = Some (st', out', k, last) ->
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
  block_res dw st hist (t ++ r) out bsm ws = block_res dw st hist t out bsm ws.
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
    dbs dw fuel st hist (t ++ r) out bsm ws = dbs dw fuel st hist t out bsm ws.
Proof.
  induction f; intros; [discriminate|]. destruct fuel; [destruct dw; reflexivity|].
  rewrite bs_S_eq in H.
  destruct (cblock_size t) as [c|] eqn:Ec; [|discriminate].
  pose proof (cblock_size_len _ _ Ec). unfold ZSTD_blockHeaderSize in *.
  destruct (3 + c >? Zlength t) eqn:E; [discriminate|]. apply Zgtb_le in E.
  rewrite !db_S_eq. rewrite (br_app_eq _ _ _ _ _ c) by (auto; lia).
  destruct (block_res dw st hist t out bsm ws) as [[[[st' out'] k1] last]|] eqn:Eb; auto.
  destruct (br_inv _ _ _ _ _ _ _ _ _ Eb) as [c' [Ec' [_ [-> ->]]]].
  rewrite Ec in Ec'. inversion Ec'; subst c'.
  destruct (bp_last _ =? 1); auto.
  destruct (blocks_size f _) as [[k2 nb2]|] eqn:E2; [|discriminate].
  rewrite skipn_app_le by (rewrite Zlength_correct in *; lia).
  erewrite IHf by eauto. auto.
Qed.

Lemma db_fuel_bs : forall f t k nb, blocks_size f t = Some (k, nb) ->
  forall fuel st out bsm ws, (f <= fuel)%nat ->
    dbs dw fuel st hist t out bsm ws = dbs dw f st hist t out bsm ws.
Proof.
  induction f; intros; [discriminate|]. destruct fuel; [lia|].
  rewrite bs_S_eq in H.
  destruct (cblock_size t) as [c|] eqn:Ec; [|discriminate].
  unfold ZSTD_blockHeaderSize in *.
  destruct (3 + c >? Zlength t) eqn:E; [discriminate|].
  rewrite !db_S_eq.
  destruct (block_res dw st hist t out bsm ws) as [[[[st' out'] k1] last]|] eqn:Eb; auto.
  destruct (br_inv _ _ _ _ _ _ _ _ _ Eb) as [c' [Ec' [_ [-> ->]]]].
  rewrite Ec in Ec'. inversion Ec'; subst c'.
  destruct (bp_last _ =? 1); auto.
  destruct (blocks_size f _) as [[k2 nb2]|] eqn:E2; [|discriminate].
  erewrite IHf by (eauto; lia). auto.
Qed.

Lemma db_bs : forall f st s out bsm ws o k,
  dbs dw f st hist s out bsm ws = Some (o, k) -> exists nb, blocks_size f s = Some (k, nb).
Proof.
  induction f; intros; [destruct dw; discriminate|]. rewrite db_S_eq in H. rewrite bs_S_eq.
  destruct (block_res dw st hist s out bsm ws) as [[[[st' out'] k1] last]|] eqn:Eb; [|discriminate].
  destruct (br_inv _ _ _ _ _ _ _ _ _ Eb) as [c [Ec [Hc [-> ->]]]].
  rewrite Ec. unfold ZSTD_blockHeaderSize.
  replace (3 + c >? Zlength s) with false by (symmetry; apply Zgtb_le; lia).
  destruct (bp_last _ =? 1). { exists 1. congruence. }
  unfold oshift in H. destruct (dbs dw f st' hist _ out' bsm ws) as [[o2 k2]|] eqn:E2; [|discriminate].
  assert (k = 3 + c + k2) as -> by congruence. destruct (IHf _ _ _ _ _ _ _ E2) as [nb ->]. eauto.
Qed.

End Blocks.

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

(* ---------- more general helpers ---------- *)

Lemma le_field_app_max : forall x r i k, 0 <= k -> Z.max 0 i + k <= Zlength x ->
  le_field (x ++ r) i k = le_field x i k.
Proof.
  intros. unfold le_field, slice. replace (Z.to_nat i) with (Z.to_nat (Z.max 0 i)) by lia.
  fold (slice (x ++ r) (Z.max 0 i) k) (slice x (Z.max 0 i) k). rewrite slice_app; auto; lia.
Qed.

Lemma bytes_ok_skipn : forall n l, bytes_ok l -> bytes_ok (skipn n l).
Proof.
  unfold bytes_ok. induction n; intros; auto. destruct l; simpl; auto. inversion H; subst. auto.
Qed.

Lemma bytes_ok_app : forall a b, bytes_ok (a ++ b) <-> bytes_ok a /\ bytes_ok b.
Proof. unfold bytes_ok. intros. apply Forall_app. Qed.

Ltac some_eq H := match type of H with Some ?a = Some ?b => assert (b = a) by congruence end.


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


Lemma le_field_app_r : forall a b i k, 0 <= i -> le_field (a ++ b) (Zlength a + i) k = le_field b i k.
Proof.
  intros. unfold le_field, slice. rewrite skipn_app.
  rewrite Zlength_correct. replace (Z.to_nat (Z.of_nat (length a) + i)) with (length a + Z.to_nat i)%nat by lia.
  rewrite skipn_all2 by lia. simpl. f_equal. f_equal. f_equal. lia.
Qed.


Lemma cblock_nonneg : forall s c, bytes_ok s -> cblock_size s = Some c -> 0 <= c.
Proof.
  unfold cblock_size; intros. destruct (Zlength s <? ZSTD_blockHeaderSize); [discriminate|].
  destruct (bp_type _ =? 1); [inversion H0; lia|]. destruct (bp_type _ =? 3); [discriminate|].
  inversion H0; subst. unfold block_props_of. cbn [bp_origSize].
  rewrite Z.shiftr_div_pow2 by lia. pose proof (le_field_bound s 0 3 H ltac:(lia)). apply Z.div_pos; lia.
Qed.

Lemma bs_pos : forall f t k nb, blocks_size f t = Some (k, nb) -> bytes_ok t -> 3 <= k.
Proof.
  induction f; intros; [discriminate|]. rewrite bs_S_eq in H.
  destruct (cblock_size t) as [c|] eqn:Ec; [|discriminate].
  pose proof (cblock_nonneg _ _ H0 Ec). unfold ZSTD_blockHeaderSize in *.
  destruct (3 + c >? Zlength t); [discriminate|].
  destruct (bp_last _ =? 1). { assert (k = 3 + c) by congruence. lia. }
  destruct (blocks_size f _) as [[k2 nb2]|] eqn:E2; [|discriminate].
  assert (k = 3 + c + k2) as -> by congruence. pose proof (IHf _ _ _ E2 (bytes_ok_skipn _ _ H0)). lia.
Qed.

Lemma db_pos : forall dw f st hist s out bsm ws o k,
  dbs dw f st hist s out bsm ws = Some (o, k) -> bytes_ok s -> 3 <= k.
Proof. intros. destruct (db_bs _ _ _ _ _ _ _ _ _ _ H) as [nb B]. eapply bs_pos; eauto. Qed.
