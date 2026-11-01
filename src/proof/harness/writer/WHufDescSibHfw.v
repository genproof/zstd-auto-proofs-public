(* The lemmas of the Huffman weights used by wb_huf_desc (first written as a model file WM_Hfw.v, which this tree
   does not have). *)
(* The FSE-compressed Huffman weights of huf_put_fse_weights against the model's huf_fse_weights (plain
   Coq). *)
Require Import Zstd.proof.harness.writer.model.WModel.
Require Import Zstd.proof.harness.writer.model.WM_Bits Zstd.proof.harness.writer.model.WM_NCount
  Zstd.proof.harness.writer.model.WM_FseTab.

Lemma hfw_fwl_snd : forall fs W L, snd (fields_wl fs W L) = L + zsum (map snd fs).
Proof.
  induction fs as [|[v nb] fs IH]; intros; simpl; [lia|]. rewrite IH. lia.
Qed.

Lemma hfw_zsum_app : forall a b, zsum (a ++ b) = zsum a + zsum b.
Proof. induction a; intros; simpl; [lia|]. unfold zsum in *. rewrite IHa. lia. Qed.

Lemma hfw_zsum_nonneg : forall fs, fields_ok fs -> 0 <= zsum (map snd fs).
Proof.
  induction fs as [|f fs IH]; intros Hok; simpl; [lia|]. inversion Hok; subst.
  specialize (IH H2). unfold zsum in *. lia.
Qed.

(* the field (v, nb) after pre, read back from the marked stream *)
Lemma hfw_peek_field : forall pre v nb post,
  fields_ok (pre ++ (v, nb) :: post) ->
  bs_peek_s (fields_mark (pre ++ (v, nb) :: post)) (fields_L pre + nb) nb = v.
Proof.
  intros pre v nb post Hok.
  assert (Hok' := Hok). unfold fields_ok in Hok'. rewrite Forall_app in Hok'.
  destruct Hok' as [Hpre Hpost]. inversion Hpost; subst. simpl in H1.
  assert (HL : fields_L (pre ++ (v, nb) :: post) = fields_L pre + nb + zsum (map snd post)).
  { unfold fields_L. rewrite !hfw_fwl_snd, map_app, hfw_zsum_app. simpl. unfold zsum. lia. }
  assert (Hp0 := hfw_zsum_nonneg pre Hpre). assert (Hp1 := hfw_zsum_nonneg post H2).
  assert (HLp : fields_L pre = zsum (map snd pre)) by (unfold fields_L; rewrite hfw_fwl_snd; lia).
  destruct (fields_wl_range (pre ++ (v, nb) :: post) 0 0 Hok ltac:(lia) ltac:(simpl; lia)) as [_ Hr].
  unfold fields_mark. rewrite bs_peek_mark; try (unfold fields_W, fields_L in *; lia).
  unfold bs_peek. transitivity ((fields_W (pre ++ (v, nb) :: post) / 2 ^ fields_L pre) mod 2 ^ nb);
  [| apply fields_field; auto].
  set (W := fields_W _). set (a := fields_L pre).
  assert (Ha : 0 < 2 ^ a) by (apply Z.pow_pos_nonneg; lia).
  assert (Hb : 0 < 2 ^ nb) by (apply Z.pow_pos_nonneg; lia).
  rewrite Z.pow_add_r by lia.
  rewrite Z.div_mul_cancel_r by lia.
  rewrite Z.rem_mul_r by lia.
  rewrite Z.mul_comm, Z.div_add by lia.
  rewrite Z.div_small by (apply Z.mod_pos_bound; lia). lia.
Qed.

Lemma hfw_firstn_S : forall (l: list Z) k, 0 <= k < Zlength l ->
  firstn (Z.to_nat (k + 1)) l = firstn (Z.to_nat k) l ++ [zn l k].
Proof.
  intros l k Hk. unfold zn. rewrite Zlength_correct in Hk.
  replace (Z.to_nat (k + 1)) with (S (Z.to_nat k)) by lia.
  assert (Hk' : (Z.to_nat k < length l)%nat) by lia. clear Hk.
  revert l Hk'. induction (Z.to_nat k) as [|m IH]; intros [|x l] Hl; simpl in *; try lia; auto.
  rewrite IH by lia. auto.
Qed.

(* fse2_loop on the states sts: R k = the payload bits left when state k is about to be updated *)
Lemma hfw_loop : forall t V (sts ws: list Z) n (R: Z -> Z),
  Zlength ws = n -> 2 <= n ->
  (forall i, 0 <= i < n -> fe_sym (fse_cell t (zn sts i)) = zn ws i) ->
  (forall k, 0 <= k <= n - 2 -> 0 <= R k) ->
  (forall k, 0 <= k <= n - 3 ->
     R k = R (k + 1) + fe_nb (fse_cell t (zn sts k)) /\
     fe_base (fse_cell t (zn sts k)) + bs_peek_s V (R k) (fe_nb (fse_cell t (zn sts k))) = zn sts (k + 2)) ->
  R (n - 2) = 0 -> 0 < fe_nb (fse_cell t (zn sts (n - 2))) ->
  forall fuel k, 0 <= k <= n - 2 -> n - 2 - k < 2 * Z.of_nat fuel ->
  fse2_loop fuel t V (R k) (zn sts k) (zn sts (k + 1)) (firstn (Z.to_nat k) ws) = Some ws.
Proof.
  intros t V sts ws n R Hlen Hn Hsym HR0 Hstep HRn Hcn.
  assert (Hend : forall acc, acc = firstn (Z.to_nat (n - 2)) ws ->
            (acc ++ [zn ws (n - 2)]) ++ [zn ws (n - 2 + 1)] = ws).
  { intros acc ->. rewrite <- hfw_firstn_S by lia. rewrite <- hfw_firstn_S by lia.
    replace (n - 2 + 1 + 1) with (Zlength ws) by lia. rewrite Zlength_correct, Nat2Z.id.
    apply firstn_all. }
  induction fuel as [|f IH]; intros k Hk Hf; [simpl in Hf; lia|].
  cbn [fse2_loop].
  rewrite Hsym by lia.
  destruct (Z.eq_dec k (n - 2)) as [->|Hk2].
  { rewrite HRn. destruct (Z.ltb_spec (0 - fe_nb (fse_cell t (zn sts (n - 2)))) 0); [|lia].
    rewrite Hsym by lia. f_equal. apply Hend. auto. }
  destruct (Hstep k ltac:(lia)) as [HRk Hpk].
  replace (R k - fe_nb (fse_cell t (zn sts k))) with (R (k + 1)) by lia.
  destruct (Z.ltb_spec (R (k + 1)) 0); [specialize (HR0 (k + 1)); lia|].
  replace (R (k + 1) + fe_nb (fse_cell t (zn sts k))) with (R k) by lia.
  rewrite Hpk. rewrite Hsym by lia.
  rewrite <- hfw_firstn_S by lia.
  destruct (Z.eq_dec (k + 1) (n - 2)) as [Hk1|Hk1].
  { rewrite Hk1, HRn. destruct (Z.ltb_spec (0 - fe_nb (fse_cell t (zn sts (n - 2)))) 0); [|lia].
    replace (k + 2) with (n - 2 + 1) by lia. rewrite Hsym by lia. f_equal. apply Hend.
    try rewrite Hk1; auto. }
  destruct (Hstep (k + 1) ltac:(lia)) as [HRk1 Hpk1].
  replace (R (k + 1) - fe_nb (fse_cell t (zn sts (k + 1)))) with (R (k + 2)) by (replace (k + 2) with (k + 1 + 1) by lia; lia).
  destruct (Z.ltb_spec (R (k + 2)) 0); [specialize (HR0 (k + 2)); lia|].
  replace (R (k + 2) + fe_nb (fse_cell t (zn sts (k + 1)))) with (R (k + 1)) by (replace (k + 2) with (k + 1 + 1) in *; lia).
  rewrite Hpk1. rewrite <- hfw_firstn_S by lia.
  replace (k + 1 + 2) with (k + 2 + 1) by lia. replace (k + 1 + 1) with (k + 2) by lia.
  apply IH; lia.
Qed.

Lemma hfw_nb_range : forall H norm log sts i,
  hfw_ok H norm log sts -> 0 <= i < wh_last H ->
  0 <= fe_nb (fse_cell (fse_build norm log) (zn sts i)) <= log.
Proof.
  intros H norm log sts i Hok Hi. destruct Hok as (_ & _ & Hnd & _ & _ & Hst & _).
  destruct Hnd as (Hl & Hn & Hf & Hs & _).
  destruct (fse_build_cells norm log ltac:(repeat split; auto; lia)) as (_ & _ & Hc).
  destruct (Hst i Hi) as [Hsi _]. destruct (Hc _ Hsi) as (_ & _ & ? & _). lia.
Qed.

Lemma hfw_fields_ok : forall H norm log sts,
  huf_ok H -> hfw_ok H norm log sts -> fields_ok (hfw_fields H norm log sts).
Proof.
  intros H norm log sts _ Hok. assert (Hok' := Hok).
  destruct Hok' as (Hn & Hlog & _ & _ & _ & Hst & Hch & _).
  unfold hfw_fields, fields_ok. apply Forall_app. split.
  - apply Forall_forall. intros f Hf. apply in_map_iff in Hf. destruct Hf as (j & <- & Hj).
    apply in_seq in Hj. simpl.
    assert (Hi : 0 <= wh_last H - 3 - Z.of_nat j < wh_last H - 2) by lia.
    assert (Hnb := hfw_nb_range H norm log sts (wh_last H - 3 - Z.of_nat j) Hok ltac:(lia)).
    destruct (Hch _ Hi) as [Hb1 Hb2]. lia.
  - destruct (Hst 0 ltac:(lia)). destruct (Hst 1 ltac:(lia)).
    repeat constructor; simpl; lia.
Qed.

Lemma hfw_wl_range : forall fs, fields_ok fs -> 0 <= fields_L fs /\ 0 <= fields_W fs < 2 ^ fields_L fs.
Proof.
  intros fs Hok. destruct (fields_wl_range fs 0 0 Hok ltac:(lia) ltac:(simpl; lia)).
  unfold fields_L, fields_W. lia.
Qed.

Lemma hfw_bytes_ok : forall H norm log sts,
  huf_ok H -> hfw_ok H norm log sts -> bytes_ok (hfw_bytes H norm log sts) /\ 1 <= Zlength (hfw_bytes H norm log sts).
Proof.
  intros H norm log sts Hh Hok. assert (Hf := hfw_fields_ok H norm log sts Hh Hok).
  destruct (hfw_wl_range _ Hf) as [HL HW].
  destruct Hok as (_ & _ & Hnd & _).
  destruct (fse_desc_bytes_ok norm log Hnd) as [Hb1 Hl1].
  destruct (bw_mark_len _ _ HL HW) as [Hb2 Hl2].
  unfold hfw_bytes, fields_mark, bytes_ok in *. split.
  - apply Forall_app. auto.
  - rewrite !Zlength_correct, app_length in *. lia.
Qed.

Lemma hfw_peek_at : forall fs pre v nb post,
  fs = pre ++ (v, nb) :: post -> fields_ok fs ->
  bs_peek_s (fields_mark fs) (fields_L pre + nb) nb = v.
Proof. intros; subst; apply hfw_peek_field; auto. Qed.

Lemma hfw_split_at : forall (l: list (Z * Z)) m d, (m < length l)%nat ->
  l = firstn m l ++ nth m l d :: skipn (S m) l.
Proof.
  induction l as [|x l IH]; intros [|m] d Hm; simpl in *; try lia; auto.
  f_equal. apply IH. lia.
Qed.

Lemma hfw_firstn_Sn : forall (l: list (Z * Z)) m d, (m < length l)%nat ->
  firstn (S m) l = firstn m l ++ [nth m l d].
Proof.
  induction l as [|x l IH]; intros [|m] d Hm; simpl in *; try lia; auto.
  f_equal. apply IH. lia.
Qed.

Lemma hfw_fields_L_nonneg : forall fs m, fields_ok fs -> 0 <= fields_L (firstn m fs).
Proof.
  intros fs m Hok. unfold fields_L. rewrite hfw_fwl_snd. apply hfw_zsum_nonneg.
  rewrite <- (firstn_skipn m fs) in Hok. unfold fields_ok in *. apply Forall_app in Hok. tauto.
Qed.

Lemma hfw_fields_L_app : forall a b, fields_L (a ++ b) = fields_L a + fields_L b.
Proof. intros. unfold fields_L. rewrite !hfw_fwl_snd, map_app, hfw_zsum_app. lia. Qed.

(* the field of the update from sts[i] to sts[i+2], i = n - 3 - j (the j-th field written) *)
Definition hfw_g (n: Z) (tab: fse_table) (sts: list Z) (j: nat) : Z * Z :=
  let i := n - 3 - Z.of_nat j in
  (zn sts (i + 2) - fe_base (fse_cell tab (zn sts i)), fe_nb (fse_cell tab (zn sts i))).

Lemma hfw_fields_eq : forall H norm log sts,
  hfw_fields H norm log sts =
  map (hfw_g (wh_last H) (fse_build norm log) sts) (seq 0 (Z.to_nat (wh_last H - 2))) ++
  [(zn sts 1, log); (zn sts 0, log)].
Proof. reflexivity. Qed.

Theorem hfw_decode : forall H norm log sts,
  huf_ok H -> hfw_ok H norm log sts -> huf_fse_weights (hfw_bytes H norm log sts) = Some (hfw_weights H).
Proof.
  intros H norm log sts Hh Hok.
  assert (Hf := hfw_fields_ok H norm log sts Hh Hok).
  destruct (hfw_wl_range _ Hf) as [HL HW].
  assert (Hok' := Hok). destruct Hok' as (Hn & Hlog & Hnd & Hneed & Hlen & Hst & Hch & Hcn).
  assert (Hws : Zlength (hfw_weights H) = wh_last H).
  { destruct Hh as (Hw & _). unfold hfw_weights. rewrite Zlength_correct in *.
    rewrite firstn_length. lia. }
  unfold huf_fse_weights, hfw_bytes.
  rewrite fse_desc_read by (try assumption; destruct Hnd as (? & ? & _); lia).
  destruct (Z.gtb_spec log 6); [lia|].
  destruct (Z.gtb_spec (4 * ((2 ^ log + 1) + 1 + (2 * Zlength norm + 2 ^ log + 8 + 3) / 4 + 129)) 876)
    as [Hwk|_]; [exfalso|].
  { destruct Hneed as [Hnl _].
    assert (Hd : (2 * Zlength norm + 2 ^ log + 8 + 3) / 4 <= (2 * 12 + 2 ^ log + 8 + 3) / 4)
      by (apply Z.div_le_mono; lia).
    assert (Hl : log = 5 \/ log = 6) by lia.
    assert (Hpw : 2 ^ log = 32 \/ 2 ^ log = 64) by (destruct Hl as [-> | ->]; [left | right]; reflexivity).
    clear Hl. remember (2 ^ log) as P. remember (Zlength norm) as nl. clear - Hpw Hd Hwk Hnl.
    destruct Hpw; subst P; Z.to_euclidean_division_equations; lia. }
  assert (Hsk : forall (D M: list Z), skipn (Z.to_nat (Zlength D)) (D ++ M) = M).
  { intros D M. rewrite Zlength_correct, Nat2Z.id, skipn_app, skipn_all, Nat.sub_diag, skipn_O. auto. }
  rewrite Hsk.
  destruct (bw_mark_stream _ _ HL HW) as [Hbs Htot]. fold (fields_mark (hfw_fields H norm log sts)) in *.
  rewrite Hbs, Htot. cbn [negb].
  set (F := hfw_fields H norm log sts) in *.
  set (n := wh_last H) in *.
  set (P := map (hfw_g n (fse_build norm log) sts) (seq 0 (Z.to_nat (n - 2)))).
  assert (HF : F = P ++ [(zn sts 1, log); (zn sts 0, log)]) by apply hfw_fields_eq.
  clearbody F.
  assert (HP : length P = Z.to_nat (n - 2)) by (unfold P; rewrite map_length, seq_length; auto).
  assert (HFL : fields_L F = fields_L P + log + log).
  { rewrite HF. unfold fields_L. rewrite !hfw_fwl_snd, map_app, hfw_zsum_app.
    cbn [map snd]. unfold zsum. cbn [fold_right]. lia. }
  assert (HPF : firstn (Z.to_nat (n - 2)) F = P).
  { rewrite HF. rewrite firstn_app, <- HP, firstn_all, Nat.sub_diag.
    rewrite firstn_O. apply app_nil_r. }
  assert (HFlen : length F = (Z.to_nat (n - 2) + 2)%nat).
  { rewrite HF. rewrite app_length, HP. cbn [length]. lia. }
  set (R := fun k => fields_L (firstn (Z.to_nat (n - 2 - k)) F)).
  assert (HR0 : R 0 = fields_L P) by (unfold R; rewrite Z.sub_0_r, HPF; auto).
  assert (HP0 : 0 <= fields_L P) by (rewrite <- HR0; apply hfw_fields_L_nonneg; auto).
  destruct (Z.ltb_spec (fields_L F - 2 * log) 0); [lia|].
  replace (bs_peek_s (fields_mark F) (fields_L F) log) with (zn sts 0).
  2:{ symmetry. replace (fields_L F) with (fields_L (P ++ [(zn sts 1, log)]) + log).
      - apply hfw_peek_at with (post := nil); auto. rewrite HF.
        rewrite <- app_assoc. auto.
      - rewrite hfw_fields_L_app, HFL. unfold fields_L at 2. simpl. lia. }
  replace (bs_peek_s (fields_mark F) (fields_L F - log) log) with (zn sts (0 + 1)).
  2:{ symmetry. replace (fields_L F - log) with (fields_L P + log) by lia.
      apply hfw_peek_at with (post := [(zn sts 0, log)]); auto. }
  replace (fields_L F - 2 * log) with (R 0) by lia.
  rewrite (hfw_loop (fse_build norm log) (fields_mark F) sts (hfw_weights H) n R) with (k := 0);
    auto; try lia.
  - destruct (Z.gtb_spec (Zlength (hfw_weights H)) 255); [lia|]. auto.
  - intros i Hi. apply Hst; auto.
  - intros k Hk. apply hfw_fields_L_nonneg; auto.
  - intros k Hk.
    set (m := Z.to_nat (n - 3 - k)).
    assert (Hm : (m < length P)%nat) by (unfold m; lia).
    assert (Hnth : nth m F (0, 0) =
                   (zn sts (k + 2) - fe_base (fse_cell (fse_build norm log) (zn sts k)),
                    fe_nb (fse_cell (fse_build norm log) (zn sts k)))).
    { rewrite HF. rewrite app_nth1 by auto. unfold P.
      rewrite nth_indep with (d' := hfw_g n (fse_build norm log) sts 0%nat)
        by (rewrite map_length, seq_length; lia).
      rewrite map_nth, seq_nth by lia. unfold hfw_g, m.
      replace (n - 3 - Z.of_nat (0 + Z.to_nat (n - 3 - k))) with k by lia. auto. }
    assert (HRk : R k = R (k + 1) + fe_nb (fse_cell (fse_build norm log) (zn sts k))).
    { unfold R. replace (Z.to_nat (n - 2 - k)) with (S m) by (unfold m; lia).
      replace (Z.to_nat (n - 2 - (k + 1))) with m by (unfold m; lia).
      rewrite (hfw_firstn_Sn F m (0, 0)) by lia. rewrite Hnth.
      unfold fields_L. rewrite !hfw_fwl_snd, map_app, hfw_zsum_app. cbn [map snd]. unfold zsum.
      cbn [fold_right]. lia. }
    split; auto.
    rewrite HRk. unfold R at 1. replace (Z.to_nat (n - 2 - (k + 1))) with m by (unfold m; lia).
    rewrite (hfw_peek_at F (firstn m F)
               (zn sts (k + 2) - fe_base (fse_cell (fse_build norm log) (zn sts k)))
               (fe_nb (fse_cell (fse_build norm log) (zn sts k))) (skipn (S m) F));
      [lia | rewrite <- Hnth; apply hfw_split_at; lia | auto].
  - unfold R. replace (n - 2 - (n - 2)) with 0 by lia. auto.
Qed.

(* every lemma above together (hfw_fields_ok, hfw_bytes_ok, hfw_decode) *)
Theorem wm_hfw_all :
  (forall H norm log sts, huf_ok H -> hfw_ok H norm log sts -> fields_ok (hfw_fields H norm log sts)) /\
  (forall H norm log sts, huf_ok H -> hfw_ok H norm log sts -> bytes_ok (hfw_bytes H norm log sts) /\ 1 <= Zlength (hfw_bytes H norm log sts)) /\
  (forall H norm log sts, huf_ok H -> hfw_ok H norm log sts -> huf_fse_weights (hfw_bytes H norm log sts) = Some (hfw_weights H)).
Proof.
  split; [exact hfw_fields_ok | split; [exact hfw_bytes_ok | exact hfw_decode]].
Qed.
