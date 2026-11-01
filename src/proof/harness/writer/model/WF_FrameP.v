(* Local copy of WF_Frame.wf_zframe_ok with its proof (same statement), used by the proof of wb_frame_s4 in place
   of WF_Frame.wf_zframe_ok. *)
(* w_frame's frame: the frame w_frame writes satisfies WModel.zframe_ok (the post of
   w_frame_spec), from the header (WF_Header) and blocks (WF_Blocks) facts. *)
Require Import Zstd.proof.harness.writer.model.WF_Defs.
Require Import Zstd.proof.harness.writer.model.WF_Header.
Require Import Zstd.proof.harness.writer.model.WF_Blocks.
Local Open Scope bool_scope.

(* ---------- helpers ---------- *)

Lemma wfz_le_value_le_bytes : forall k v, le_value (le_bytes k v) = v mod 2 ^ (8 * Z.of_nat k).
Proof.
  induction k; intros; cbn [le_bytes le_value].
  - simpl. rewrite Z.mod_1_r. reflexivity.
  - rewrite IHk. rewrite Nat2Z.inj_succ.
    replace (8 * Z.succ (Z.of_nat k)) with (8 + 8 * Z.of_nat k) by lia.
    rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256.
    rewrite Z.rem_mul_r; [lia | lia |]. apply Z.pow_pos_nonneg; lia.
Qed.

Lemma wfz_le_bytes_ok : forall k v, bytes_ok (le_bytes k v).
Proof.
  induction k; intros; cbn [le_bytes].
  - constructor.
  - constructor; [unfold is_byte; apply Z.mod_pos_bound; lia | apply IHk].
Qed.

Lemma wfz_length_le_bytes : forall k v, length (le_bytes k v) = k.
Proof. induction k; intros; simpl; auto. Qed.

Lemma wfz_Zlength_app : forall (a b: list Z), Zlength (a ++ b) = Zlength a + Zlength b.
Proof. intros. rewrite !Zlength_correct, length_app. lia. Qed.

Lemma wfz_Zlength_nonneg : forall (a: list Z), 0 <= Zlength a.
Proof. intros. rewrite Zlength_correct. lia. Qed.

Lemma wfz_Zlength4 : forall a b c d : Z, Zlength [a; b; c; d] = 4.
Proof. reflexivity. Qed.

Lemma wfz_le_field_app : forall (a b: list Z) p k,
  0 <= p -> 0 <= k -> p + k <= Zlength a -> le_field (a ++ b) p k = le_field a p k.
Proof.
  intros a b p k Hp Hk H. unfold le_field, slice. f_equal.
  rewrite Zlength_correct in H. rewrite skipn_app, firstn_app, length_skipn.
  replace (Z.to_nat k - (length a - Z.to_nat p))%nat with 0%nat by lia.
  simpl. rewrite app_nil_r. reflexivity.
Qed.

Lemma wfz_skipn_app : forall (a b: list Z), skipn (Z.to_nat (Zlength a)) (a ++ b) = b.
Proof.
  intros. rewrite Zlength_correct, Nat2Z.id, skipn_app, skipn_all, Nat.sub_diag. reflexivity.
Qed.

Lemma wfz_le_field_app_r : forall (a b: list Z) k, le_field (a ++ b) (Zlength a) k = le_field b 0 k.
Proof. intros. unfold le_field, slice. rewrite wfz_skipn_app. reflexivity. Qed.

Lemma wfz_byte_at_app : forall (a b: list Z) i, 0 <= i < Zlength a -> byte_at (a ++ b) i = byte_at a i.
Proof.
  intros. unfold byte_at. rewrite app_nth1; auto. rewrite Zlength_correct in H. lia.
Qed.

Lemma wfz_nth_map_seq : forall (g: nat -> Z) n i, (i < n)%nat -> nth i (map g (seq 0 n)) 0 = g i.
Proof.
  intros g n i H. rewrite (nth_indep _ 0 (g 0%nat)) by (rewrite length_map, length_seq; lia).
  rewrite map_nth, seq_nth by lia. reflexivity.
Qed.

Lemma wfz_set_bit3_length : forall l pos, length (set_bit3 l pos) = length l.
Proof. intros. unfold set_bit3. rewrite length_map, length_seq. reflexivity. Qed.

Lemma wfz_set_bit3_nth : forall l pos i, (i < length l)%nat ->
  nth i (set_bit3 l pos) 0 = if Z.of_nat i =? pos then Z.lor (nth i l 0) 8 else nth i l 0.
Proof.
  intros. unfold set_bit3. rewrite wfz_nth_map_seq by auto. unfold byte_at. rewrite Nat2Z.id. reflexivity.
Qed.

Lemma wfz_xor4_tail : forall a c0 c1 c2 c3 x,
  xor4 (a ++ [c0; c1; c2; c3]) (Zlength a) x =
  a ++ [Z.lxor c0 (Z.land (Z.shiftr x 0) 255); Z.lxor c1 (Z.land (Z.shiftr x 8) 255);
        Z.lxor c2 (Z.land (Z.shiftr x 16) 255); Z.lxor c3 (Z.land (Z.shiftr x 24) 255)].
Proof.
  intros. apply nth_ext with (d := 0) (d' := 0).
  - unfold xor4. rewrite length_map, length_seq, !length_app. reflexivity.
  - intros i Hi. unfold xor4 in Hi. rewrite length_map, length_seq, length_app in Hi. simpl in Hi.
    unfold xor4. rewrite wfz_nth_map_seq by (rewrite length_app; simpl; lia). unfold byte_at.
    rewrite Nat2Z.id, Zlength_correct.
    destruct (Nat.lt_ge_cases i (length a)) as [Hl | Hl].
    + rewrite !app_nth1 by lia.
      assert (Z.of_nat (length a) <=? Z.of_nat i = false) as -> by (apply Z.leb_gt; lia). reflexivity.
    + rewrite !app_nth2 by lia.
      assert ((Z.of_nat (length a) <=? Z.of_nat i) && (Z.of_nat i <? Z.of_nat (length a) + 4) = true) as ->
        by (apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      replace (Z.of_nat i - Z.of_nat (length a)) with (Z.of_nat (i - length a)) by lia.
      destruct (i - length a)%nat as [|[|[|[|j]]]] eqn:E; [reflexivity..| lia].
Qed.

Lemma wfz_lxor_byte : forall a b, 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lxor a b < 256.
Proof.
  intros a b Ha Hb.
  assert (N : 0 <= Z.lxor a b) by (apply Z.lxor_nonneg; split; intros; lia).
  split; [exact N|].
  destruct (Z.eq_dec (Z.lxor a b) 0) as [E|E]; [lia|].
  pose proof (Z.log2_lxor a b (proj1 Ha) (proj1 Hb)).
  assert (Z.log2 a < 8).
  { destruct (Z.eq_dec a 0); [subst; simpl; lia|]. apply Z.log2_lt_pow2; lia. }
  assert (Z.log2 b < 8).
  { destruct (Z.eq_dec b 0); [subst; simpl; lia|]. apply Z.log2_lt_pow2; lia. }
  change 256 with (2 ^ 8). apply Z.log2_lt_pow2; lia.
Qed.

Lemma wfz_lxor_same : forall c y, Z.lxor c y = c -> y = 0.
Proof.
  intros c y H. assert (E : Z.lxor c (Z.lxor c y) = Z.lxor c c) by (rewrite H; reflexivity).
  rewrite <- Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_l in E. exact E.
Qed.

Lemma wfz_land255 : forall y, Z.land y 255 = y mod 256.
Proof. intros. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma wfz_xor_ne : forall c0 c1 c2 c3 x,
  bytes_ok [c0; c1; c2; c3] -> 0 < x < 2 ^ 32 ->
  le_value [Z.lxor c0 (Z.land (Z.shiftr x 0) 255); Z.lxor c1 (Z.land (Z.shiftr x 8) 255);
            Z.lxor c2 (Z.land (Z.shiftr x 16) 255); Z.lxor c3 (Z.land (Z.shiftr x 24) 255)] <>
  le_value [c0; c1; c2; c3].
Proof.
  intros c0 c1 c2 c3 x Hb Hx Heq.
  inversion Hb as [|? ? B0 Hb1]; inversion Hb1 as [|? ? B1 Hb2]; inversion Hb2 as [|? ? B2 Hb3];
    inversion Hb3 as [|? ? B3 _]; unfold is_byte in *.
  rewrite !wfz_land255, !Z.shiftr_div_pow2 in Heq by lia.
  set (q0 := x / 2 ^ 0) in *. set (q1 := x / 2 ^ 8) in *. set (q2 := x / 2 ^ 16) in *.
  set (q3 := x / 2 ^ 24) in *.
  assert (R0 : 0 <= q0 mod 256 < 256) by (apply Z.mod_pos_bound; lia).
  assert (R1 : 0 <= q1 mod 256 < 256) by (apply Z.mod_pos_bound; lia).
  assert (R2 : 0 <= q2 mod 256 < 256) by (apply Z.mod_pos_bound; lia).
  assert (R3 : 0 <= q3 mod 256 < 256) by (apply Z.mod_pos_bound; lia).
  pose proof (wfz_lxor_byte c0 _ B0 R0). pose proof (wfz_lxor_byte c1 _ B1 R1).
  pose proof (wfz_lxor_byte c2 _ B2 R2). pose proof (wfz_lxor_byte c3 _ B3 R3).
  cbn [le_value] in Heq.
  assert (E0 : Z.lxor c0 (q0 mod 256) = c0) by lia.
  assert (E1 : Z.lxor c1 (q1 mod 256) = c1) by lia.
  assert (E2 : Z.lxor c2 (q2 mod 256) = c2) by lia.
  assert (E3 : Z.lxor c3 (q3 mod 256) = c3) by lia.
  apply wfz_lxor_same in E0, E1, E2, E3.
  assert (Q0 : q0 = x) by (subst q0; apply Z.div_1_r).
  assert (Q1 : q1 = q0 / 256) by (subst q0 q1; rewrite Z.div_1_r; reflexivity).
  assert (Q2 : q2 = q1 / 256) by (subst q1 q2; rewrite Z.div_div by lia; reflexivity).
  assert (Q3 : q3 = q2 / 256) by (subst q2 q3; rewrite Z.div_div by lia; reflexivity).
  assert (Q4 : q3 / 256 = 0).
  { rewrite Q3, Q2, Q1, Q0, !Z.div_div by lia. apply Z.div_small. lia. }
  pose proof (Z.div_mod q0 256 ltac:(lia)). pose proof (Z.div_mod q1 256 ltac:(lia)).
  pose proof (Z.div_mod q2 256 ltac:(lia)). pose proof (Z.div_mod q3 256 ltac:(lia)).
  lia.
Qed.

(* ---------- the frame ---------- *)

Lemma wfz_window_nonneg : forall dm p, hp_ok dm p -> 0 <= hp_window p.
Proof.
  intros dm p (Hn & _ & _ & _ & He & Hm & _). unfold hp_window. destruct (hp_single p); [lia|].
  assert (0 < 2 ^ (10 + hp_e p)) by (apply Z.pow_pos_nonneg; lia).
  assert (0 <= 2 ^ (10 + hp_e p) / 8) by (apply Z.div_pos; lia). nia.
Qed.

Lemma wfz_big : forall f0 p nb ud, wi_skippable f0 = false ->
  wi_big (hp_info f0 p nb ud) = negb (hp_single p) && (10 + hp_e p >? 31).
Proof.
  intros. unfold wi_big. cbn [wi_skippable wi_single wi_window_log hp_info]. rewrite H.
  unfold hp_window_log. destruct (hp_single p); reflexivity.
Qed.

Lemma wfz_header : forall f0 p nb ud, wi_skippable f0 = false ->
  wi_header (hp_info f0 p nb ud) =
  {| fh_contentSize := if hp_single p || negb (hp_fcs p =? 0) then hp_n p else ZSTD_CONTENTSIZE_UNKNOWN;
     fh_windowSize := hp_window p; fh_blockSizeMax := hp_bsm p;
     fh_frameType := 0; fh_headerSize := Zlength (hp_bytes p); fh_dictID := hp_did p;
     fh_checksumFlag := if hp_ck p then 1 else 0 |}.
Proof. intros. unfold wi_header. cbn [wi_skippable hp_info]. rewrite H. reflexivity. Qed.

Lemma wfz_blocks : forall dm p nb bb st out b st' c r,
  hp_ok dm p ->
  wblocks_pre (hp_bsm p) (hp_window p) (dm_content dm) (dm_state dm) bb st out nb ->
  wblock_ok (hp_bsm p) (hp_window p) (dm_content dm) st out true b st' c ->
  decode_blocks (length ((bb ++ b) ++ r)) (dm_state dm) (dm_content dm) ((bb ++ b) ++ r) nil (hp_bsm p)
    (hp_window p) = Some (out ++ c, Zlength (bb ++ b)) /\
  blocks_size (length ((bb ++ b) ++ r)) ((bb ++ b) ++ r) = Some (Zlength (bb ++ b), nb + 1).
Proof.
  intros dm p nb bb st out b st' c r Hok Hpre Hlast.
  pose proof (wfz_window_nonneg dm p Hok).
  edestruct (wf_blocks (hp_bsm p) (hp_window p) (dm_content dm) (dm_state dm) bb st out nb b st' c r
               (length ((bb ++ b) ++ r))) as (_ & _ & _ & H1 & H2); eauto.
  - unfold hp_bsm. lia.
  - rewrite !length_app. lia.
  - rewrite <- !app_assoc in *. auto.
Qed.

Lemma wfz_core : forall dm f0 p nb nb' ud bb st out b st' c wl r,
  hp_ok dm p -> wi_skippable f0 = false ->
  wblocks_pre (hp_bsm p) (hp_window p) (dm_content dm) (dm_state dm) bb st out nb ->
  wblock_ok (hp_bsm p) (hp_window p) (dm_content dm) st out true b st' c ->
  Zlength (out ++ c) = hp_n p ->
  decode_frame dm wl (hp_bytes p ++ (bb ++ b) ++ r) =
    if wi_rejected wl (hp_info f0 p nb' ud) then FDetHdr else
    if hp_ck p then (if Zlength r <? 4 then FUnk
                     else if negb (le_field r 0 4 =? xxh64 (out ++ c) 0 mod 2 ^ 32) then FDetCk
                     else FOk (out ++ c) (Zlength (hp_bytes p) + Zlength (bb ++ b) + 4))
    else FOk (out ++ c) (Zlength (hp_bytes p) + Zlength (bb ++ b)).
Proof.
  intros dm f0 p nb nb' ud bb st out b st' c wl r Hok Hsk Hpre Hlast Hn.
  pose proof (wfz_window_nonneg dm p Hok) as Hw0.
  edestruct (wf_blocks (hp_bsm p) (hp_window p) (dm_content dm) (dm_state dm) bb st out nb b st' c nil
               (length (bb ++ b))) as (_ & _ & Hb3 & _ & _); eauto; [unfold hp_bsm; lia|].
  pose proof (wfz_blocks dm p nb bb st out b st' c r Hok Hpre Hlast) as [HB _].
  pose proof (wf_hdr_bytes dm p ((bb ++ b) ++ r) Hok)
    as (Hh & _ & Hfhd & Hwb & Hmag & H4 & Hhs & _ & H8 & Hsg & _ & H5 & He).
  pose proof (wf_hdr_gfh dm f0 p nb' ud ((bb ++ b) ++ r) Hok Hsk) as Hg.
  rewrite wfz_header, wfz_big in Hg by auto.
  set (hdr := hp_bytes p) in *. set (blocks := bb ++ b) in *.
  assert (HL : Zlength (hdr ++ blocks ++ r) = Zlength hdr + Zlength blocks + Zlength r)
    by (rewrite !wfz_Zlength_app; lia).
  assert (Hbl : 3 <= Zlength blocks) by (subst blocks; rewrite wfz_Zlength_app; pose proof (wfz_Zlength_nonneg bb); lia).
  pose proof (wfz_Zlength_nonneg r).
  unfold decode_frame.
  rewrite HL, Hmag, H4, Hhs, H8.
  assert (E1 : Zlength hdr + Zlength blocks + Zlength r <? ZSTD_FRAMEHEADERSIZE_MIN + ZSTD_blockHeaderSize = false)
    by (apply Z.ltb_ge; unfold ZSTD_FRAMEHEADERSIZE_MIN, ZSTD_blockHeaderSize; lia).
  assert (E2 : Zlength hdr + Zlength blocks + Zlength r <? Zlength hdr + ZSTD_blockHeaderSize = false)
    by (apply Z.ltb_ge; unfold ZSTD_blockHeaderSize; lia).
  rewrite E1, E2, Z.eqb_refl. change (0 =? 0) with true. cbn [negb].
  assert (Ebig : negb (Z.land (Z.shiftr (hp_fhd p) 5) 1 =? 1) &&
                 (Z.shiftr (byte_at (hdr ++ blocks ++ r) 5) 3 + ZSTD_WINDOWLOG_ABSOLUTEMIN >? ZSTD_WINDOWLOG_MAX) =
                 negb (hp_single p) && (10 + hp_e p >? 31)).
  { rewrite Hsg. destruct (hp_single p) eqn:Es; [reflexivity|]. rewrite H5, He by reflexivity.
    unfold ZSTD_WINDOWLOG_ABSOLUTEMIN, ZSTD_WINDOWLOG_MAX. cbn [zb negb Z.eqb andb]. rewrite Z.add_comm. reflexivity. }
  assert (Hrej : wi_rejected wl (hp_info f0 p nb' ud) = (negb (hp_single p) && (10 + hp_e p >? 31)) || (hp_window p >? wl)).
  { unfold wi_rejected. rewrite wfz_big by auto. cbn [hp_info wi_skippable wi_window]. rewrite Hsk. reflexivity. }
  rewrite Ebig, Hg, Hrej.
  destruct (negb (hp_single p) && (10 + hp_e p >? 31)); [reflexivity|].
  cbn [orb fh_windowSize fh_frameType fh_dictID fh_headerSize fh_blockSizeMax fh_contentSize fh_checksumFlag].
  destruct (hp_window p >? wl); [reflexivity|].
  change (0 =? 0) with true. cbn [negb].
  pose proof Hok as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hdid).
  assert (Ed : negb (hp_did p =? 0) && negb (hp_did p =? dm_id dm) = false).
  { destruct Hdid as [E|E]; rewrite E, Z.eqb_refl; [reflexivity|apply Bool.andb_false_r]. }
  rewrite Ed, wfz_skipn_app, HB.
  assert (Ec : negb ((if hp_single p || negb (hp_fcs p =? 0) then hp_n p else ZSTD_CONTENTSIZE_UNKNOWN)
                       =? ZSTD_CONTENTSIZE_UNKNOWN) &&
               negb (Zlength (out ++ c) =? (if hp_single p || negb (hp_fcs p =? 0) then hp_n p
                                             else ZSTD_CONTENTSIZE_UNKNOWN)) = false).
  { destruct (hp_single p || negb (hp_fcs p =? 0)); [rewrite Hn, Z.eqb_refl; apply Bool.andb_false_r|].
    rewrite Z.eqb_refl. reflexivity. }
  rewrite Ec.
  destruct (hp_ck p); [|reflexivity]. change (1 =? 1) with true. cbv iota.
  replace (Zlength hdr + Zlength blocks + Zlength r - Zlength hdr - Zlength blocks) with (Zlength r) by lia.
  replace (le_field (hdr ++ blocks ++ r) (Zlength hdr + Zlength blocks) 4) with (le_field r 0 4).
  - reflexivity.
  - rewrite app_assoc, <- wfz_Zlength_app, wfz_le_field_app_r. reflexivity.
Qed.

Lemma wfz_fsi : forall dm f0 p nb ud bb st out b st' c r,
  hp_ok dm p -> wi_skippable f0 = false -> 0 <= nb < 6 ->
  wblocks_pre (hp_bsm p) (hp_window p) (dm_content dm) (dm_state dm) bb st out nb ->
  wblock_ok (hp_bsm p) (hp_window p) (dm_content dm) st out true b st' c ->
  (hp_ck p = true -> 4 <= Zlength r) ->
  frame_size_info (hp_bytes p ++ (bb ++ b) ++ r) =
    (if wi_big (hp_info f0 p (nb + 1) ud) then None
     else Some (Zlength (hp_bytes p) + Zlength (bb ++ b) + (if hp_ck p then 4 else 0),
                zframe_bound (hp_info f0 p (nb + 1) ud))) /\
  frame_compressed_size (hp_bytes p ++ (bb ++ b) ++ r) =
    (if wi_big (hp_info f0 p (nb + 1) ud) then None
     else Some (Zlength (hp_bytes p) + Zlength (bb ++ b) + (if hp_ck p then 4 else 0))).
Proof.
  intros dm f0 p nb ud bb st out b st' c r Hok Hsk Hnb Hpre Hlast Hr.
  pose proof (wfz_window_nonneg dm p Hok) as Hw0.
  pose proof (wfz_blocks dm p nb bb st out b st' c r Hok Hpre Hlast) as [_ HBs].
  pose proof (wf_hdr_bytes dm p ((bb ++ b) ++ r) Hok) as (_ & _ & _ & _ & Hmag & _).
  pose proof (wf_hdr_gfh dm f0 p (nb + 1) ud ((bb ++ b) ++ r) Hok Hsk) as Hg.
  pose proof Hok as (Hn0 & _).
  set (hdr := hp_bytes p) in *. set (blocks := bb ++ b) in *.
  assert (HL : Zlength (hdr ++ blocks ++ r) = Zlength hdr + Zlength blocks + Zlength r)
    by (rewrite !wfz_Zlength_app; lia).
  unfold frame_size_info, frame_compressed_size. rewrite Hmag.
  change (is_skippable_magic ZSTD_MAGICNUMBER) with false. rewrite !Bool.andb_false_r.
  rewrite Hg. destruct (wi_big (hp_info f0 p (nb + 1) ud)); [split; reflexivity|].
  rewrite wfz_header by auto.
  cbn [fh_windowSize fh_frameType fh_dictID fh_headerSize fh_blockSizeMax fh_contentSize fh_checksumFlag].
  fold hdr. rewrite wfz_skipn_app, HBs.
  assert (Hb : (if (if hp_single p || negb (hp_fcs p =? 0) then hp_n p else ZSTD_CONTENTSIZE_UNKNOWN)
                     =? ZSTD_CONTENTSIZE_UNKNOWN
                then (nb + 1) * hp_bsm p mod 2 ^ 64
                else if hp_single p || negb (hp_fcs p =? 0) then hp_n p else ZSTD_CONTENTSIZE_UNKNOWN) =
               zframe_bound (hp_info f0 p (nb + 1) ud)).
  { unfold zframe_bound. cbn [hp_info wi_fcs_present wi_fcs wi_blocks wi_window].
    destruct (hp_single p || negb (hp_fcs p =? 0)).
    - assert (hp_n p =? ZSTD_CONTENTSIZE_UNKNOWN = false) as ->
        by (apply Z.eqb_neq; unfold ZSTD_CONTENTSIZE_UNKNOWN; lia). reflexivity.
    - rewrite Z.eqb_refl. change (hp_bsm p) with (Z.min (hp_window p) ZSTD_BLOCKSIZE_MAX).
      apply Z.mod_small. unfold ZSTD_BLOCKSIZE_MAX. split; nia. }
  rewrite Hb. clear Hb.
  destruct (hp_ck p).
  - change (1 =? 1) with true. cbv iota beta zeta.
    assert (Zlength (hdr ++ blocks ++ r) - (Zlength hdr + Zlength blocks) <? 4 = false) as ->
      by (apply Z.ltb_ge; specialize (Hr eq_refl); lia).
    split; reflexivity.
  - change (0 =? 1) with false. cbv iota beta zeta. rewrite Z.add_0_r. split; reflexivity.
Qed.

Lemma wfz_set_bit3_facts : forall (l t: list Z), (5 <= length l)%nat ->
  Zlength (set_bit3 l 4 ++ t) = Zlength (l ++ t) /\
  le_field (set_bit3 l 4 ++ t) 0 4 = le_field (l ++ t) 0 4 /\
  byte_at (set_bit3 l 4 ++ t) 4 = Z.lor (byte_at (l ++ t) 4) 8.
Proof.
  intros l t Hl.
  assert (Hn : forall i, (i < length l)%nat ->
            nth i (set_bit3 l 4 ++ t) 0 = if Z.of_nat i =? 4 then Z.lor (nth i (l ++ t) 0) 8 else nth i (l ++ t) 0).
  { intros i Hi. rewrite app_nth1 by (rewrite wfz_set_bit3_length; lia). rewrite app_nth1 by lia.
    apply wfz_set_bit3_nth; auto. }
  split; [rewrite !Zlength_correct, !length_app, wfz_set_bit3_length; reflexivity|].
  split.
  - unfold le_field, slice. cbn [skipn Z.to_nat]. f_equal.
    apply nth_ext with (d := 0) (d' := 0).
    + rewrite !length_firstn, !length_app, wfz_set_bit3_length. reflexivity.
    + intros i Hi. rewrite length_firstn, length_app, wfz_set_bit3_length in Hi.
      rewrite !nth_firstn. destruct (i <? Pos.to_nat 4)%nat eqn:E; [|reflexivity].
      apply Nat.ltb_lt in E. rewrite Hn by lia.
      assert (Z.of_nat i =? 4 = false) as -> by (apply Z.eqb_neq; lia). reflexivity.
  - unfold byte_at. change (Z.to_nat 4) with 4%nat. rewrite Hn by lia. reflexivity.
Qed.

Theorem wf_zframe_ok : forall dm f0 p nb ud bb st out b st' c,
  hp_ok dm p -> wi_skippable f0 = false -> 0 <= nb < 6 ->
  wblocks_pre (hp_bsm p) (hp_window p) (dm_content dm) (dm_state dm) bb st out nb ->
  wblock_ok (hp_bsm p) (hp_window p) (dm_content dm) st out true b st' c ->
  Zlength (out ++ c) = hp_n p ->
  zframe_ok dm (hp_info f0 p (nb + 1) ud) (hp_bytes p ++ bb ++ b ++ hp_ck_bytes p (out ++ c)) (out ++ c).
Proof.
  intros dm f0 p nb ud bb st out b st' c Hok Hsk Hnb Hpre Hlast Hn.
  pose proof (wfz_window_nonneg dm p Hok) as Hw0.
  edestruct (wf_blocks (hp_bsm p) (hp_window p) (dm_content dm) (dm_state dm) bb st out nb b st' c nil
               (length (bb ++ b))) as (Hbb & Hoc & Hb3 & _ & _); eauto; [unfold hp_bsm; lia|].
  pose proof (wfz_fsi dm f0 p nb ud bb st out b st' c) as Hfsi.
  pose proof (wfz_core dm f0 p nb (nb + 1) ud bb st out b st' c) as Hcore.
  pose proof (wf_hdr_gfh dm f0 p (nb + 1) ud) as Hgfh.
  pose proof (wf_hdr_bytes dm p) as Hhdr.
  rewrite (app_assoc bb b).
  set (blocks := bb ++ b) in *.
  set (hdr := hp_bytes p) in *.
  set (ck := hp_ck_bytes p (out ++ c)).
  set (f := hp_info f0 p (nb + 1) ud).
  assert (Hck : bytes_ok ck /\ Zlength ck = if hp_ck p then 4 else 0).
  { unfold ck, hp_ck_bytes. destruct (hp_ck p).
    - split; [apply wfz_le_bytes_ok | rewrite Zlength_correct, wfz_length_le_bytes; reflexivity].
    - split; [constructor | reflexivity]. }
  destruct Hck as [Hckb Hckl].
  destruct (Hhdr nil Hok) as (Hh & Hhb & _).
  assert (Hbl : 3 <= Zlength blocks) by (subst blocks; rewrite wfz_Zlength_app; pose proof (wfz_Zlength_nonneg bb); lia).
  assert (HLfb : Zlength (hdr ++ blocks ++ ck) = Zlength hdr + Zlength blocks + (if hp_ck p then 4 else 0))
    by (rewrite !wfz_Zlength_app; lia).
  unfold zframe_ok.
  split; [unfold bytes_ok in *; rewrite !Forall_app; auto|].
  split; [exact Hoc|].
  split; [exact Hsk|].
  split; [symmetry; exact Hn|].
  split; [cbn [f hp_info wi_hsize wi_checksum]; fold hdr; rewrite HLfb; destruct (hp_ck p); lia|].
  intros t.
  assert (Ht : (hdr ++ blocks ++ ck) ++ t = hdr ++ blocks ++ (ck ++ t)) by (rewrite !app_assoc; reflexivity).
  assert (Hr4 : hp_ck p = true -> 4 <= Zlength (ck ++ t))
    by (intros E; rewrite wfz_Zlength_app, Hckl, E; pose proof (wfz_Zlength_nonneg t); lia).
  destruct (Hhdr (blocks ++ ck ++ t) Hok) as (_ & _ & Hfhd & _ & Hmag & H4 & Hhs & Hhs8 & H8 & _).
  destruct (Hfsi (ck ++ t) Hok Hsk Hnb Hpre Hlast Hr4) as [Hsi Hcs].
  fold hdr blocks f in Hsi, Hcs.
  pose proof (wfz_Zlength_nonneg (ck ++ t)).
  assert (HLs : Zlength (hdr ++ blocks ++ ck ++ t) = Zlength hdr + Zlength blocks + Zlength (ck ++ t))
    by (rewrite !wfz_Zlength_app; lia).
  split.
  { rewrite Ht. unfold is_frame. rewrite HLs, Hmag.
    assert (Zlength hdr + Zlength blocks + Zlength (ck ++ t) <? 4 = false) as -> by (apply Z.ltb_ge; lia).
    reflexivity. }
  split.
  { rewrite Ht. unfold is_skippable_frame. rewrite HLs, Hmag.
    assert (Zlength hdr + Zlength blocks + Zlength (ck ++ t) <? 4 = false) as -> by (apply Z.ltb_ge; lia).
    reflexivity. }
  split.
  { rewrite Ht, Hcs. destruct (wi_big f); [reflexivity|]. rewrite HLfb. reflexivity. }
  split.
  { rewrite Ht. apply Hgfh; auto. }
  split.
  { rewrite Ht. unfold frame_content_size. rewrite Hgfh by auto. fold f.
    destruct (wi_big f); [reflexivity|]. subst f. rewrite wfz_header by auto. reflexivity. }
  split.
  { rewrite Ht. unfold dict_id_from_frame. rewrite Hgfh by auto. fold f.
    destruct (wi_big f); [reflexivity|]. subst f. rewrite wfz_header by auto. reflexivity. }
  split.
  { rewrite Ht. unfold frame_header_size. rewrite HLs, H4, Hhs.
    assert (Zlength hdr + Zlength blocks + Zlength (ck ++ t) <? ZSTD_FRAMEHEADERSIZE_PREFIX = false) as ->
      by (apply Z.ltb_ge; unfold ZSTD_FRAMEHEADERSIZE_PREFIX; lia).
    reflexivity. }
  split.
  { rewrite Ht, Hsi. destruct (wi_big f); [reflexivity|]. rewrite HLfb. reflexivity. }
  split.
  { intros wl. rewrite Ht. subst f. rewrite (Hcore wl (ck ++ t)) by auto.
    destruct (wi_rejected wl (hp_info f0 p (nb + 1) ud)); [reflexivity|].
    rewrite HLfb. destruct (hp_ck p) eqn:Eck.
    - assert (Zlength (ck ++ t) <? 4 = false) as -> by (apply Z.ltb_ge; auto).
      assert (Hv : le_field (ck ++ t) 0 4 = xxh64 (out ++ c) 0 mod 2 ^ 32).
      { rewrite wfz_le_field_app by lia. unfold ck, hp_ck_bytes. rewrite Eck.
        unfold le_field, slice. cbn [skipn Z.to_nat].
        rewrite firstn_all2 by (rewrite wfz_length_le_bytes; lia).
        rewrite wfz_le_value_le_bytes. change (8 * Z.of_nat 4) with 32.
        change 4294967295 with (Z.ones 32). rewrite Z.land_ones by lia. apply Z.mod_mod.
        apply Z.pow_nonzero; lia. }
      rewrite Hv, Z.eqb_refl. reflexivity.
    - rewrite Z.add_0_r. reflexivity. }
  split.
  { intros wl.
    assert (Hl5 : (5 <= length (hdr ++ blocks ++ ck))%nat)
      by (rewrite Zlength_correct in HLfb; destruct (hp_ck p); lia).
    destruct (wfz_set_bit3_facts _ t Hl5) as (E1 & E2 & E3).
    rewrite Ht in E1, E2, E3.
    unfold decode_frame. rewrite E1, E2, E3, H4, HLs, Hmag, Hhs8.
    assert (E8 : Z.land (Z.lor (hp_fhd p) 8) 8 = 8) by (rewrite Z.land_lor_distr_l, H8; reflexivity).
    rewrite E8.
    assert (Zlength hdr + Zlength blocks + Zlength (ck ++ t) <? ZSTD_FRAMEHEADERSIZE_MIN + ZSTD_blockHeaderSize = false)
      as -> by (apply Z.ltb_ge; unfold ZSTD_FRAMEHEADERSIZE_MIN, ZSTD_blockHeaderSize; lia).
    assert (Zlength hdr + Zlength blocks + Zlength (ck ++ t) <? Zlength hdr + ZSTD_blockHeaderSize = false)
      as -> by (apply Z.ltb_ge; unfold ZSTD_blockHeaderSize; lia).
    rewrite Z.eqb_refl. reflexivity. }
  { intros Eck wl x Hx Hrej. cbn [f hp_info wi_checksum] in Eck.
    revert Hckb Hckl HLfb. unfold ck, hp_ck_bytes. rewrite Eck. intros Hckb Hckl HLfb.
    set (v := Z.land (xxh64 (out ++ c) 0) 4294967295) in *.
    assert (Hv : le_value (le_bytes 4 v) = xxh64 (out ++ c) 0 mod 2 ^ 32).
    { rewrite wfz_le_value_le_bytes. change (8 * Z.of_nat 4) with 32. subst v.
      change 4294967295 with (Z.ones 32). rewrite Z.land_ones by lia. apply Z.mod_mod.
      apply Z.pow_nonzero; lia. }
    revert Hckb Hv. cbn [le_bytes]. 
    set (c0 := v mod 256). set (c1 := v / 256 mod 256). set (c2 := v / 256 / 256 mod 256).
    set (c3 := v / 256 / 256 / 256 mod 256). intros Hckb Hv.
    replace (Zlength (hdr ++ blocks ++ [c0; c1; c2; c3]) - 4) with (Zlength (hdr ++ blocks))
      by (rewrite !wfz_Zlength_app; reflexivity || (cbn; lia)).
    rewrite (app_assoc hdr blocks), wfz_xor4_tail, <- !app_assoc.
    subst f. rewrite (Hcore wl) by auto. rewrite Hrej, Eck.
    assert (Zlength ([Z.lxor c0 (Z.land (Z.shiftr x 0) 255); Z.lxor c1 (Z.land (Z.shiftr x 8) 255);
                      Z.lxor c2 (Z.land (Z.shiftr x 16) 255); Z.lxor c3 (Z.land (Z.shiftr x 24) 255)] ++ t) <? 4 = false)
      as -> by (apply Z.ltb_ge; rewrite wfz_Zlength_app, wfz_Zlength4; pose proof (wfz_Zlength_nonneg t); lia).
    rewrite wfz_le_field_app by (rewrite ?wfz_Zlength4; lia).
    unfold le_field, slice. cbn [skipn firstn Z.to_nat Pos.to_nat].
    rewrite <- Hv.
    assert (Hne := wfz_xor_ne c0 c1 c2 c3 x Hckb Hx).
    apply Z.eqb_neq in Hne. rewrite firstn_all2 by apply le_n. rewrite Hne. reflexivity. }
Qed.
