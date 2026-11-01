(* FS3 one-shot frames: the pure helpers of ZSTD_decompressFrame's body (copied from v2 body_frame.v, which no
   longer loads) and the v3 model definitions of the frame being decoded.
   The model FACTS about them are in Frames3Model.v. *)
Require Export Zstd.proof.dec.v3.FS.frames.Frames3Spec.
Require Export Zstd.proof.zstd.XxhLemmas.
Require Export Zstd.proof.dec.FS.FramesHdr Zstd.proof.dec.FS.FramesSeries.
Local Open Scope logic.

Section CM_Frames3Pure_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.



(* ---------- zstd_globals without ZSTD_blockHeaderSize (read by the loop) ---------- *)
Definition zg_rest (gv: globals) : mpred := (
  data_at Ews tint g_debuglevel_val (gv _g_debuglevel) *
  data_at Ers (tarray tuint 32) DeBruijnBytePos_val (gv _DeBruijnBytePos) *
  data_at Ers (tarray tuint 32) DeBruijnClz_val (gv _DeBruijnClz) *
  data_at Ers tulong zeroFilled_val (gv _zeroFilled) *
  data_at Ers (Tstruct ___gp_ZSTD_customMem noattr) ZSTD_defaultCMem_val (gv _ZSTD_defaultCMem) *
  data_at Ers (tarray tuint 3) repStartValue_val (gv _repStartValue) *
  data_at Ers (tarray tulong 4) ZSTD_fcs_fieldSize_val (gv _ZSTD_fcs_fieldSize) *
  data_at Ers (tarray tulong 4) ZSTD_did_fieldSize_val (gv _ZSTD_did_fieldSize) *
  data_at Ers (tarray tuchar 36) LL_bits_val (gv _LL_bits) *
  data_at Ers (tarray tuchar 53) ML_bits_val (gv _ML_bits) *
  data_at Ers (tarray (tarray (Tstruct ___gp_algo_time_t noattr) 2) 16) algoTime_val (gv _algoTime) *
  data_at Ers (tarray tuint 36) LL_base_val (gv _LL_base) *
  data_at Ers (tarray tuint 32) OF_base_val (gv _OF_base) *
  data_at Ers (tarray tuchar 32) OF_bits_val (gv _OF_bits) *
  data_at Ers (tarray tuint 53) ML_base_val (gv _ML_base) *
  data_at Ers (tarray (Tstruct ___gp_ZSTD_seqSymbol noattr) 65) LL_defaultDTable_val (gv _LL_defaultDTable) *
  data_at Ers (tarray (Tstruct ___gp_ZSTD_seqSymbol noattr) 33) OF_defaultDTable_val (gv _OF_defaultDTable) *
  data_at Ers (tarray (Tstruct ___gp_ZSTD_seqSymbol noattr) 65) ML_defaultDTable_val (gv _ML_defaultDTable) *
  data_at Ers (tarray tuint 8) dec32table_val (gv _dec32table) *
  data_at Ers (tarray tint 8) dec64table_val (gv _dec64table) *
  eb_res gv)%logic.

Lemma zg_unfold: forall gv,
  zstd_globals gv |-- data_at Ers tulong (Vlong (Int64.repr 3)) (gv _ZSTD_blockHeaderSize) * zg_rest gv.
Proof. intros. unfold zstd_globals, zg_rest, ZSTD_blockHeaderSize_val. cancel. Qed.

Lemma zg_fold: forall gv,
  data_at Ers tulong (Vlong (Int64.repr 3)) (gv _ZSTD_blockHeaderSize) * zg_rest gv |-- zstd_globals gv.
Proof. intros. unfold zstd_globals, zg_rest, ZSTD_blockHeaderSize_val. cancel. Qed.

(* ---------- pure facts ---------- *)

Lemma win_sub: forall sh N c off s a b off',
  win_ok sh N c off (Zlength s) s -> 0 <= a <= b -> b <= Zlength s -> off' = off + a ->
  win_ok sh N c off' (Zlength (sublist a b s)) (sublist a b s).
Proof.
  intros sh N c off s a b off' (Hsh & Hoff & HN & HN32 & Hc & _ & Hs & Hcs) Hab Hb ->.
  unfold win_ok. rewrite Zlength_sublist by lia.
  refine (conj Hsh (conj _ (conj _ (conj HN32 (conj Hc (conj eq_refl (conj _ _))))))); [lia | lia | | ].
  - apply Forall_sublist; auto.
  - replace (off + a) with (a + off) by lia. replace (a + off + (b - a)) with (b + off) by lia.
    rewrite <- (sublist_sublist b (off + Zlength s) a off) by lia.
    rewrite Hcs, sublist_map. reflexivity.
Qed.

Lemma byte_at_range: forall s i, bytes_ok s -> 0 <= i < Zlength s -> 0 <= byte_at s i < 256.
Proof.
  intros s i Hs Hi. unfold byte_at. rewrite Zlength_correct in Hi.
  assert (Hn: (Z.to_nat i < length s)%nat) by lia.
  pose proof (nth_In s 0 Hn) as Hin. eapply Forall_forall in Hs; [exact Hs | exact Hin].
Qed.

Lemma fhs_range: forall b, 0 <= b < 256 -> 6 <= fhd_header_size b <= 18.
Proof.
  intros b Hb.
  assert (Hall: forallb (fun b => andb (6 <=? fhd_header_size b) (fhd_header_size b <=? 18))
                  (map Z.of_nat (seq 0 256)) = true) by reflexivity.
  rewrite forallb_forall in Hall. specialize (Hall b).
  assert (In b (map Z.of_nat (seq 0 256))).
  { apply in_map_iff. exists (Z.to_nat b). split; [lia | apply in_seq; lia]. }
  specialize (Hall H). apply andb_prop in Hall. destruct Hall as [A B]. apply Z.leb_le in A, B. lia.
Qed.

Lemma add_uchar_long: forall b a n, isptr b ->
  force_val (sem_binary_operation' Oadd (tptr tuchar) tulong (offset_val a b) (Vlong (Int64.repr n))) =
  offset_val (a + n) b.
Proof.
  intros. unfold sem_binary_operation'. simpl. rewrite sem_add_pl_ptr_special' by auto.
  simpl. rewrite offset_offset_val. f_equal. lia.
Qed.

(* the block type of a block ZSTD_getcBlockSize accepts *)
Lemma bt_range: forall t c, cblock_size t = Some c ->
  bp_type (block_props_of t) = 0 \/ bp_type (block_props_of t) = 1 \/ bp_type (block_props_of t) = 2.
Proof.
  intros t c H.
  assert (R: 0 <= bp_type (block_props_of t) < 4).
  { unfold block_props_of. cbn [bp_type]. change 3 with (Z.ones 2). rewrite Z.land_ones by lia.
    apply Z.mod_pos_bound. lia. }
  unfold cblock_size in H. destruct (Zlength t <? ZSTD_blockHeaderSize); [discriminate | ].
  destruct (bp_type (block_props_of t) =? 1) eqn:E1; [apply Z.eqb_eq in E1; auto | ].
  destruct (bp_type (block_props_of t) =? 3) eqn:E3; [discriminate | ].
  apply Z.eqb_neq in E1, E3. lia.
Qed.

(* a block's compressed size fits in 21 bits *)
Lemma cblock_size_range: forall t c, bytes_ok t -> cblock_size t = Some c -> 0 <= c < 2 ^ 21.
Proof.
  intros t c Ht H. unfold cblock_size in H.
  destruct (Zlength t <? ZSTD_blockHeaderSize) eqn:E0; [discriminate | ].
  destruct (bp_type (block_props_of t) =? 1); [inversion H; lia | ].
  destruct (bp_type (block_props_of t) =? 3); [discriminate | ].
  inversion H; subst c. clear H. unfold block_props_of; cbn [bp_origSize].
  assert (Hs: Forall (fun b => 0 <= b <= Byte.max_unsigned) (slice t 0 3)).
  { unfold slice. apply Forall_firstn, Forall_skipn. eapply Forall_impl; [ | exact Ht].
    intros a Ha. unfold is_byte in Ha. rep_lia. }
  pose proof (le_value_range _ Hs) as Hr.
  assert (Hl: Zlength (slice t 0 3) <= 3).
  { unfold slice. rewrite Zlength_correct, firstn_length. lia. }
  unfold le_field. rewrite Z.shiftr_div_pow2 by lia.
  assert (2 ^ (8 * Zlength (slice t 0 3)) <= 2 ^ 24) by (apply Z.pow_le_mono_r; lia).
  split; [apply Z.div_pos; lia | ]. apply Z.div_lt_upper_bound; lia.
Qed.

Lemma err_dst_is: is_error_code (err_code ZSTD_error_dstSize_tooSmall) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma dec_err_dst: dec_err (err_code ZSTD_error_dstSize_tooSmall).
Proof. unfold dec_err. split; [reflexivity | split; intro Hx; vm_compute in Hx; discriminate Hx]. Qed.

Ltac frm_lia := unfold ZSTD_FRAMEHEADERSIZE_PREFIX, ZSTD_FRAMEHEADERSIZE_MIN, ZSTD_blockHeaderSize in *; lia.

Section FrmHdr.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

Lemma frm_Zlength_firstn: forall (s: list Z) n, 0 <= n <= Zlength s -> Zlength (firstn (Z.to_nat n) s) = n.
Proof.
  intros. rewrite Zlength_correct, firstn_length. rewrite Zlength_correct in H. lia.
Qed.

Lemma frm_byte_at_firstn: forall s n i, 0 <= i < n -> byte_at (firstn (Z.to_nat n) s) i = byte_at s i.
Proof.
  intros. unfold byte_at. rewrite nth_firstn. destruct (Nat.ltb_spec (Z.to_nat i) (Z.to_nat n)); [reflexivity | lia].
Qed.

Lemma frm_le_field_firstn: forall s n i k, 0 <= i -> 0 <= k -> i + k <= n ->
  le_field (firstn (Z.to_nat n) s) i k = le_field s i k.
Proof.
  intros. unfold le_field, slice. rewrite skipn_firstn_comm, firstn_firstn. f_equal. f_equal. lia.
Qed.

Lemma frm_le_value_bound: forall l, bytes_ok l -> 0 <= le_value l < 2 ^ (8 * Z.of_nat (length l)).
Proof.
  induction l; intros H; cbn [le_value length]. simpl. lia.
  inversion H; subst. unfold is_byte in *. destruct (IHl H3).
  replace (8 * Z.of_nat (S (length l))) with (8 + 8 * Z.of_nat (length l)) by lia.
  rewrite Z.pow_add_r by lia. change (2^8) with 256. nia.
Qed.

Lemma frm_Forall_firstn: forall (P: Z -> Prop) n l, Forall P l -> Forall P (firstn n l).
Proof. induction n; intros; destruct l; simpl; auto. inversion H; subst; auto. Qed.

Lemma frm_Forall_skipn: forall (P: Z -> Prop) n l, Forall P l -> Forall P (skipn n l).
Proof. induction n; intros; destruct l; simpl; auto. inversion H; subst; auto. Qed.

Lemma frm_le_field_bound: forall s i k, bytes_ok s -> 0 <= k -> 0 <= le_field s i k < 2 ^ (8 * k).
Proof.
  intros. unfold le_field, slice.
  assert (bytes_ok (firstn (Z.to_nat k) (skipn (Z.to_nat i) s))).
  { unfold bytes_ok in *. apply frm_Forall_firstn, frm_Forall_skipn. auto. }
  destruct (frm_le_value_bound _ H1). split; auto.
  eapply Z.lt_le_trans; [eassumption|]. apply Z.pow_le_mono_r; [lia|].
  rewrite firstn_length. lia.
Qed.

Lemma frm_byte_at_bound: forall s i, bytes_ok s -> 0 <= byte_at s i < 256.
Proof.
  intros. unfold byte_at. destruct (Nat.lt_ge_cases (Z.to_nat i) (length s)).
  - unfold bytes_ok in H. rewrite Forall_forall in H. apply H. apply nth_In. auto.
  - rewrite nth_overflow by auto. lia.
Qed.

Lemma frm_land_mod: forall x n, 0 <= n -> Z.land x (Z.ones n) = x mod 2 ^ n.
Proof. intros. apply Z.land_ones. auto. Qed.

Lemma frm_fhd_bits: forall fhd, 0 <= fhd < 256 ->
  0 <= Z.land fhd 3 < 4 /\ 0 <= Z.land (Z.shiftr fhd 5) 1 < 2 /\ 0 <= Z.shiftr fhd 6 < 4 /\
  0 <= Z.land (Z.shiftr fhd 2) 1 < 2.
Proof.
  intros.
  change 3 with (Z.ones 2). change 1 with (Z.ones 1).
  rewrite !frm_land_mod by lia. rewrite !Z.shiftr_div_pow2 by lia.
  repeat split; try apply Z.mod_pos_bound; try lia.
  apply Z.div_pos; lia. apply Z.div_lt_upper_bound; simpl; lia.
Qed.

Lemma frm_hs_range: forall fhd, 0 <= fhd < 256 -> 6 <= fhd_header_size fhd <= 18.
Proof.
  intros. destruct (frm_fhd_bits fhd H) as (Hd & Hss & Hfc & _). unfold fhd_header_size.
  assert (Z.land fhd 3 = 0 \/ Z.land fhd 3 = 1 \/ Z.land fhd 3 = 2 \/ Z.land fhd 3 = 3) as Ed by lia.
  assert (Z.land (Z.shiftr fhd 5) 1 = 0 \/ Z.land (Z.shiftr fhd 5) 1 = 1) as Es by lia.
  assert (Z.shiftr fhd 6 = 0 \/ Z.shiftr fhd 6 = 1 \/ Z.shiftr fhd 6 = 2 \/ Z.shiftr fhd 6 = 3) as Ef by lia.
  destruct Ed as [-> | [-> | [-> | ->]]]; destruct Es as [-> | ->]; destruct Ef as [-> | [-> | [-> | ->]]];
    simpl; lia.
Qed.

Lemma frm_gfh_prefix: forall s,
  0 <= byte_at s 4 < 256 ->
  ZSTD_FRAMEHEADERSIZE_PREFIX <= Zlength s ->
  le_field s 0 4 = ZSTD_MAGICNUMBER ->
  fhd_header_size (byte_at s 4) <= Zlength s ->
  get_frame_header (firstn (Z.to_nat (fhd_header_size (byte_at s 4))) s) = get_frame_header s.
Proof.
  intros s Hb Hn Hm Hhs.
  pose proof (frm_hs_range _ Hb) as Hr.
  unfold get_frame_header.
  rewrite frm_Zlength_firstn by lia.
  rewrite (frm_le_field_firstn s _ 0 4) by lia.
  rewrite (frm_byte_at_firstn s _ 4) by lia.
  rewrite Hm. unfold ZSTD_FRAMEHEADERSIZE_PREFIX in Hn.
  destruct (Z.ltb_spec (fhd_header_size (byte_at s 4)) 5); [lia|].
  destruct (Z.ltb_spec (Zlength s) 5); [lia|].
  rewrite Z.eqb_refl. cbn [negb].
  destruct (Z.ltb_spec (fhd_header_size (byte_at s 4)) (fhd_header_size (byte_at s 4))); [lia|].
  destruct (Z.ltb_spec (Zlength s) (fhd_header_size (byte_at s 4))); [lia|].
  rewrite (frm_byte_at_firstn s _ 5) by lia.
  destruct (frm_fhd_bits _ Hb) as (Hd & Hss & Hfc & _).
  clear H H0 H1 H2.
  revert Hhs Hr. unfold fhd_header_size.
  remember (Z.land (byte_at s 4) 3) as d. remember (Z.land (Z.shiftr (byte_at s 4) 5) 1) as ss.
  remember (Z.shiftr (byte_at s 4) 6) as fc.
  intros Hhs Hr.
  assert (d = 0 \/ d = 1 \/ d = 2 \/ d = 3) as Ed by lia.
  assert (ss = 0 \/ ss = 1) as Es by lia.
  assert (fc = 0 \/ fc = 1 \/ fc = 2 \/ fc = 3) as Ef by lia.
  destruct Ed as [-> | [-> | [-> | ->]]]; destruct Es as [-> | ->]; destruct Ef as [-> | [-> | [-> | ->]]];
    cbn [Z.eqb Pos.eqb andb]; simpl in Hhs, Hr;
    rewrite ?frm_le_field_firstn, ?frm_byte_at_firstn by (simpl; lia); reflexivity.
Qed.

Lemma frm_window_bound: forall b, 0 <= b < 256 ->
  Z.shiftr b 3 + ZSTD_WINDOWLOG_ABSOLUTEMIN <= ZSTD_WINDOWLOG_MAX ->
  0 <= 2 ^ (Z.shiftr b 3 + ZSTD_WINDOWLOG_ABSOLUTEMIN) +
       Z.shiftr (2 ^ (Z.shiftr b 3 + ZSTD_WINDOWLOG_ABSOLUTEMIN)) 3 * Z.land b 7 < 2 ^ 64.
Proof.
  intros b Hb Hw. unfold ZSTD_WINDOWLOG_ABSOLUTEMIN, ZSTD_WINDOWLOG_MAX in *.
  rewrite Z.shiftr_div_pow2 in * by lia.
  rewrite (Z.shiftr_div_pow2 (2 ^ _)) by lia.
  change 7 with (Z.ones 3). rewrite frm_land_mod by lia.
  assert (0 <= b / 2 ^ 3) by (apply Z.div_pos; lia).
  assert (0 < 2 ^ (b / 2 ^ 3 + 10)) by (apply Z.pow_pos_nonneg; lia).
  assert (2 ^ (b / 2 ^ 3 + 10) <= 2 ^ 31) by (apply Z.pow_le_mono_r; lia).
  assert (0 <= 2 ^ (b / 2 ^ 3 + 10) / 2 ^ 3 <= 2 ^ (b / 2 ^ 3 + 10)).
  { split. apply Z.div_pos; lia. apply Z.div_le_upper_bound. lia. change (2 ^ 3) with 8. lia. }
  assert (0 <= b mod 2 ^ 3 < 2 ^ 3) by (apply Z.mod_pos_bound; lia).
  change (2 ^ 3) with 8 in *. change (2 ^ 31) with 2147483648 in *. change (2 ^ 64) with 18446744073709551616.
  nia.
Qed.

Ltac frm_bnd s Hb :=
  repeat match goal with
  | |- context [le_field s ?i ?k] =>
      let H := fresh "Hf" in
      pose proof (frm_le_field_bound s i k Hb ltac:(simpl; lia)) as H;
      revert H; generalize (le_field s i k); intros ? H
  | |- context [byte_at s ?i] =>
      tryif constr_eq i 4 then fail else
      let H := fresh "Hy" in
      pose proof (frm_byte_at_bound s i Hb) as H;
      revert H; generalize (byte_at s i); intros ? H
  end.

Lemma frm_gfh_ok: forall s h,
  bytes_ok s ->
  le_field s 0 4 = ZSTD_MAGICNUMBER ->
  get_frame_header s = FH_ok h ->
  fh_frameType h = 0 /\ fh_headerSize h = fhd_header_size (byte_at s 4) /\
  fh_headerSize h <= Zlength s /\ 6 <= fh_headerSize h <= 18 /\
  0 <= fh_blockSizeMax h <= ZSTD_BLOCKSIZE_MAX /\ fh_blockSizeMax h = Z.min (fh_windowSize h) ZSTD_BLOCKSIZE_MAX /\
  0 <= fh_windowSize h < 2 ^ 64 /\ 0 <= fh_contentSize h < 2 ^ 64 /\
  (fh_checksumFlag h = 0 \/ fh_checksumFlag h = 1) /\ 0 <= fh_dictID h < 2 ^ 32.
Proof.
  intros s h Hb Hm H. unfold get_frame_header in H.
  destruct (Z.ltb_spec (Zlength s) 5).
  { destruct (Zlength s >? 0); [destruct (_ && _)|]; discriminate. }
  rewrite Hm, Z.eqb_refl in H. cbn [negb] in H.
  destruct (Z.ltb_spec (Zlength s) (fhd_header_size (byte_at s 4))); [discriminate|].
  destruct (negb (Z.land (byte_at s 4) 8 =? 0)); [discriminate|].
  pose proof (frm_byte_at_bound s 4 Hb) as B4. pose proof (frm_byte_at_bound s 5 Hb) as B5.
  pose proof (frm_hs_range _ B4) as Hr.
  destruct (frm_fhd_bits _ B4) as (Hd & Hss & Hfc & Hck).
  destruct ((Z.land (Z.shiftr (byte_at s 4) 5) 1 =? 0) &&
            (Z.shiftr (byte_at s 5) 3 + ZSTD_WINDOWLOG_ABSOLUTEMIN >? ZSTD_WINDOWLOG_MAX)) eqn:Ew;
    [discriminate|].
  injection H as <-. cbn [fh_frameType fh_headerSize fh_blockSizeMax fh_windowSize fh_contentSize
    fh_checksumFlag fh_dictID].
  assert (Hck': Z.land (Z.shiftr (byte_at s 4) 2) 1 = 0 \/ Z.land (Z.shiftr (byte_at s 4) 2) 1 = 1) by lia.
  remember (Z.land (byte_at s 4) 3) as d. remember (Z.land (Z.shiftr (byte_at s 4) 5) 1) as ss.
  remember (Z.shiftr (byte_at s 4) 6) as fc.
  assert (Hwin: ss = 0 -> 0 <= 2 ^ (Z.shiftr (byte_at s 5) 3 + ZSTD_WINDOWLOG_ABSOLUTEMIN) +
       Z.shiftr (2 ^ (Z.shiftr (byte_at s 5) 3 + ZSTD_WINDOWLOG_ABSOLUTEMIN)) 3 * Z.land (byte_at s 5) 7 < 2 ^ 64).
  { intros ->. apply frm_window_bound; auto. cbn [Z.eqb andb] in Ew. rewrite Z.gtb_ltb in Ew. apply Z.ltb_ge in Ew. lia. }
  clear Ew.
  generalize dependent (2 ^ (Z.shiftr (byte_at s 5) 3 + ZSTD_WINDOWLOG_ABSOLUTEMIN) +
       Z.shiftr (2 ^ (Z.shiftr (byte_at s 5) 3 + ZSTD_WINDOWLOG_ABSOLUTEMIN)) 3 * Z.land (byte_at s 5) 7).
  intros w Hwin.
  assert (d = 0 \/ d = 1 \/ d = 2 \/ d = 3) as Ed by lia.
  assert (ss = 0 \/ ss = 1) as Es by lia.
  assert (fc = 0 \/ fc = 1 \/ fc = 2 \/ fc = 3) as Ef by lia.
  destruct Ed as [-> | [-> | [-> | ->]]]; destruct Es as [-> | ->]; destruct Ef as [-> | [-> | [-> | ->]]];
    cbn [Z.eqb Pos.eqb andb];
    try specialize (Hwin eq_refl);
    frm_bnd s Hb; unfold ZSTD_BLOCKSIZE_MAX, ZSTD_CONTENTSIZE_UNKNOWN in *; simpl in *;
    repeat split; try lia; try tauto.
Qed.

Lemma frm_decode_frame_short: forall dm s,
  Zlength s < ZSTD_FRAMEHEADERSIZE_MIN + ZSTD_blockHeaderSize \/
  le_field s 0 4 <> ZSTD_MAGICNUMBER \/
  Zlength s < fhd_header_size (byte_at s 4) + ZSTD_blockHeaderSize ->
  decode_frame dm no_wlim s = FUnk.
Proof.
  intros dm s H. unfold decode_frame.
  destruct (Z.ltb_spec (Zlength s) (ZSTD_FRAMEHEADERSIZE_MIN + ZSTD_blockHeaderSize)); [reflexivity|].
  destruct (Z.eqb_spec (le_field s 0 4) ZSTD_MAGICNUMBER); [|reflexivity]. cbn [negb].
  destruct (Z.ltb_spec (Zlength s) (fhd_header_size (byte_at s 4) + ZSTD_blockHeaderSize)); [reflexivity|].
  lia.
Qed.

Lemma frm_decode_frame_header_bad: forall dm s,
  ZSTD_FRAMEHEADERSIZE_MIN + ZSTD_blockHeaderSize <= Zlength s ->
  le_field s 0 4 = ZSTD_MAGICNUMBER ->
  fhd_header_size (byte_at s 4) + ZSTD_blockHeaderSize <= Zlength s ->
  (forall h, get_frame_header s <> FH_ok h) ->
  decode_frame dm no_wlim s = FDetHdr \/ decode_frame dm no_wlim s = FUnk.
Proof.
  intros dm s H1 H2 H3 H4. unfold decode_frame.
  destruct (Zlength s <? _); [auto|].
  destruct (negb (le_field s 0 4 =? ZSTD_MAGICNUMBER)); [auto|].
  destruct (Zlength s <? _); [auto|].
  destruct (negb (Z.land (byte_at s 4) 8 =? 0)); [auto|].
  destruct (_ && _); [auto|].
  destruct (get_frame_header s) eqn:E; auto. exfalso; eapply H4; eauto.
Qed.

Lemma frm_decode_frame_header_ok: forall dm s h,
  bytes_ok s ->
  ZSTD_FRAMEHEADERSIZE_MIN + ZSTD_blockHeaderSize <= Zlength s ->
  le_field s 0 4 = ZSTD_MAGICNUMBER ->
  fhd_header_size (byte_at s 4) + ZSTD_blockHeaderSize <= Zlength s ->
  get_frame_header s = FH_ok h ->
  decode_frame dm no_wlim s =
    if negb (fh_dictID h =? 0) && negb (fh_dictID h =? dm_id dm) then FUnk else
    let hs := fh_headerSize h in
    let rest := skipn (Z.to_nat hs) s in
    match decode_blocks (length rest) (dm_state dm) (dm_content dm) rest nil (fh_blockSizeMax h) (fh_windowSize h) with
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
Proof.
  intros dm s h Hb H1 Hm H3 Hg.
  destruct (frm_gfh_ok s h Hb Hm Hg) as (Ht & _ & _ & _ & _ & _ & Hw & _).
  unfold decode_frame.
  destruct (Z.ltb_spec (Zlength s) (ZSTD_FRAMEHEADERSIZE_MIN + ZSTD_blockHeaderSize)); [lia|].
  rewrite Hm, Z.eqb_refl. cbn [negb].
  destruct (Z.ltb_spec (Zlength s) (fhd_header_size (byte_at s 4) + ZSTD_blockHeaderSize)); [lia|].
  assert (Hg' := Hg). unfold get_frame_header in Hg'.
  destruct (Z.ltb_spec (Zlength s) 5); [unfold ZSTD_FRAMEHEADERSIZE_MIN, ZSTD_blockHeaderSize in *; lia|].
  rewrite Hm, Z.eqb_refl in Hg'. cbn [negb] in Hg'.
  destruct (Zlength s <? fhd_header_size (byte_at s 4)); [discriminate|].
  destruct (negb (Z.land (byte_at s 4) 8 =? 0)); [discriminate|].
  replace (negb (Z.land (Z.shiftr (byte_at s 4) 5) 1 =? 1)) with (Z.land (Z.shiftr (byte_at s 4) 5) 1 =? 0).
  2:{ pose proof (frm_byte_at_bound s 4 Hb) as B4. destruct (frm_fhd_bits _ B4) as (_ & Hss & _).
      assert (Z.land (Z.shiftr (byte_at s 4) 5) 1 = 0 \/ Z.land (Z.shiftr (byte_at s 4) 5) 1 = 1) as [-> | ->] by lia;
      reflexivity. }
  destruct (_ && _); [discriminate|].
  rewrite Hg.
  destruct (Z.gtb_spec (fh_windowSize h) no_wlim); [unfold no_wlim in *; lia|].
  rewrite Ht. reflexivity.
Qed.

Lemma frm_sub_end: forall (s: list Z) a, sublist a (Zlength s) s = skipn (Z.to_nat a) s.
Proof.
  intros. unfold sublist. rewrite firstn_all2 by (rewrite Zlength_correct; lia). reflexivity.
Qed.

Lemma frm_skip_range: forall m, 0 <= m < 2 ^ 32 -> is_skippable_magic m = true ->
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

End FrmHdr.

(* ======================================================================================
   The model side of the block loop (plain Coq).  The C reads the frame of s: the header
   (hs = fhd_header_size s[4] bytes, parsed into h), then blocks from rest = s[hs..]; j is the
   offset of the current block in rest, out the frame's output so far, st the tables' state.
   ====================================================================================== *)

Definition fr_rest (s: list Z) (hs: Z) : list Z := sublist hs (Zlength s) s.

(* the bytes from the block at offset j of rest on *)
Definition fr_t (s: list Z) (hs j: Z) : list Z := sublist (hs + j) (Zlength s) s.

(* the model's blocks of the frame (Series.decode_frame, after the header) *)
Definition fr_DB (dm: dict_model) (h: frame_header) (s: list Z) (hs: Z) : option (list Z * Z) :=
  decode_blocks (length (fr_rest s hs)) (dm_state dm) (dm_content dm) (fr_rest s hs) [] (fh_blockSizeMax h)
    (fh_windowSize h).

(* the C's block walk so far is ZSTD_findFrameCompressedSize's (Frame.blocks_size): whatever the walk finds from
   block j on extends to the whole frame's *)
Definition fr_BS (s: list Z) (hs j: Z) : Prop :=
  forall f kk nb, blocks_size f (fr_t s hs j) = Some (kk, nb) ->
    exists f' nb', blocks_size f' (fr_rest s hs) = Some (j + kk, nb').

(* the C's block j is one of the blocks of the frame: if all of them are Raw/RLE (ErrCodes.blocks_rr), so are the
   blocks from j on (for the error code of a too small capacity, Frames3Spec.frame_codes3) *)
Definition fr_RR (s: list Z) (hs j: Z) : Prop := blocks_rr (fr_rest s hs) -> blocks_rr (fr_t s hs j).

(* the refusal walk (Refuse.blocks_refused; the dictionary window rule is off in a one-shot frame) from block j on,
   after the C's output out and with the tables' state st: when zstd certainly refuses the frame's blocks, it
   refuses them from block j on (the blocks before j were accepted with the content the C wrote) *)
Definition fr_RF (dm: dict_model) (h: frame_header) (s: list Z) (hs j: Z) (out: list Z) (st: dstate) : Prop :=
  forall f0, blocks_refused false f0 h (dm_state dm) (dm_content dm) (fr_rest s hs) [] (fh_blockSizeMax h) ->
    exists f, blocks_refused false f h st (dm_content dm) (fr_t s hs j) out (fh_blockSizeMax h).

(* on track: whatever the model decodes, it decodes from block j on, after out, with the state st; the block
   walk (fr_BS); Raw/RLE blocks only from j on (fr_RR); the refusal walk (fr_RF) *)
Definition fr_OT (dm: dict_model) (h: frame_header) (s: list Z) (hs j: Z) (out: list Z) (st: dstate) : Prop :=
  (forall o k, fr_DB dm h s hs = Some (o, k) ->
    exists f, decode_blocks f st (dm_content dm) (fr_t s hs j) out (fh_blockSizeMax h) (fh_windowSize h) =
              Some (o, k - j)) /\ fr_BS s hs j /\ fr_RR s hs j /\ fr_RF dm h s hs j out st.

(* after the last block, which ends at j: when zstd certainly refuses the frame's blocks, the end of the frame
   (the content out and the bytes after the last block) is refused *)
Definition fr_RE (dm: dict_model) (h: frame_header) (s: list Z) (hs j: Z) (out: list Z) : Prop :=
  forall f0, blocks_refused false f0 h (dm_state dm) (dm_content dm) (fr_rest s hs) [] (fh_blockSizeMax h) ->
    frame_end_refused h out (fr_t s hs j).

(* a successful raw or RLE block (r not an error) wrote the content zstd gives it (Refuse.rblock: no comparison
   with Block_Maximum_Size), cnt after out, and left the tables' state st2 as rblock's; for a compressed block,
   rblock is blk_res and S_dec's other link gives it *)
Definition fr_RL (dm: dict_model) (h: frame_header) (s: list Z) (hs j: Z) (out: list Z) (st: dstate) (c r: Z)
    (cnt: list Z) (st2: dstate) : Prop :=
  is_error_code r = false -> bp_type (block_props_of (fr_t s hs j)) <> 2 ->
  forall st' out', rblock false st (dm_content dm) (fr_t s hs j) out c (fh_blockSizeMax h) (fh_windowSize h) =
                   Some (st', out') -> out' = out ++ cnt /\ st2 = st'.

(* blocks_size: more fuel gives the same result; the length of the bytes is enough fuel *)
Lemma bs_mono: forall f t r, blocks_size f t = Some r -> forall g, (f <= g)%nat -> blocks_size g t = Some r.
Proof.
  induction f as [|f IH]; intros t r H g Hg; [discriminate|].
  destruct g as [|g]; [lia|]. cbn [blocks_size] in *.
  destruct (cblock_size t) as [c|]; [|discriminate].
  destruct (ZSTD_blockHeaderSize + c >? Zlength t); [discriminate|].
  destruct (bp_last (block_props_of t) =? 1); [exact H|].
  destruct (blocks_size f _) as [[k nb]|] eqn:E; [|discriminate].
  rewrite (IH _ _ E g ltac:(lia)). exact H.
Qed.

Lemma bs_fuel: forall f t r, bytes_ok t -> blocks_size f t = Some r -> blocks_size (length t) t = Some r.
Proof.
  induction f as [|f IH]; intros t r Hb H; [discriminate|].
  cbn [blocks_size] in H.
  destruct (cblock_size t) as [c|] eqn:Ec; [|discriminate].
  destruct (ZSTD_blockHeaderSize + c >? Zlength t) eqn:El; [discriminate|].
  rewrite Z.gtb_ltb in El. apply Z.ltb_ge in El.
  assert (Hc0: 0 <= c) by (apply (cblock_size_range t c Hb Ec)).
  assert (Hlen: (0 < length t)%nat) by (rewrite Zlength_correct in El; unfold ZSTD_blockHeaderSize in El; lia).
  destruct (length t) as [|n] eqn:Lt; [lia|]. cbn [blocks_size]. rewrite Ec.
  replace (ZSTD_blockHeaderSize + c >? Zlength t) with false by (rewrite Z.gtb_ltb; symmetry; apply Z.ltb_ge; exact El).
  destruct (bp_last (block_props_of t) =? 1); [exact H|].
  destruct (blocks_size f _) as [[k nb]|] eqn:E; [|discriminate].
  rewrite (bs_mono _ _ _ (IH _ _ (frm_Forall_skipn _ _ _ Hb) E) n); [exact H|].
  rewrite skipn_length. rewrite Zlength_correct in El. unfold ZSTD_blockHeaderSize in *. lia.
Qed.

(* the model's step on the block of t (cblock_size t = Some c): Series.decode_blocks's `res` *)
Definition blk_res (st: dstate) (hist out t: list Z) (c bsm wsize: Z) : option (dstate * list Z) :=
  let bp := block_props_of t in
  let body := slice t ZSTD_blockHeaderSize c in
  if bp_type bp =? 0 then
    (if c >? bsm then None else Some (st, out ++ body))
  else if bp_type bp =? 1 then
    (if orb (bp_origSize bp >? bsm) (c >? bsm) then None
     else Some (st, out ++ repeat (byte_at body 0) (Z.to_nat (bp_origSize bp))))
  else
    match decode_block st hist out body bsm wsize with
    | Some (st', content) => Some (st', out ++ content)
    | None => None
    end.

(* rblock on the three block types: a raw block's body, an RLE block's byte (its content is 1 byte), a compressed
   block as blk_res *)
Lemma rblock_raw: forall dw st hist t out c bsm ws, bp_type (block_props_of t) = 0 ->
  rblock dw st hist t out c bsm ws = Some (st, out ++ slice t ZSTD_blockHeaderSize c).
Proof. intros. unfold rblock. rewrite H. reflexivity. Qed.

Lemma rblock_rle: forall dw st hist t out bsm ws, bp_type (block_props_of t) = 1 ->
  rblock dw st hist t out 1 bsm ws =
  Some (st, out ++ Zrepeat (byte_at t 3) (bp_origSize (block_props_of t))).
Proof.
  intros. unfold rblock. rewrite H. simpl. unfold Zrepeat. do 3 f_equal.
  destruct t as [|? [|? [|? [|? ?]]]]; reflexivity.
Qed.

Lemma rblock_cmp: forall st hist t out c bsm ws, bp_type (block_props_of t) = 2 ->
  rblock false st hist t out c bsm ws = blk_res st hist out t c bsm ws.
Proof. intros. unfold rblock, blk_res, rdec_block. rewrite H. reflexivity. Qed.

(* the bytes after the block at j (of c content bytes) *)
Lemma fr_t_next: forall s hs j c, 0 <= hs -> 0 <= j -> 0 <= c ->
  fr_t s hs (j + ZSTD_blockHeaderSize + c) = skipn (Z.to_nat (ZSTD_blockHeaderSize + c)) (fr_t s hs j).
Proof.
  intros. unfold fr_t. rewrite !frm_sub_end, skipn_skipn. f_equal. unfold ZSTD_blockHeaderSize. lia.
Qed.

(* the refusal walk through a block that is not the last: the C's content out' and state st' are rblock's *)
Lemma fr_RF_next: forall dm h s hs j out st c st' out',
  fr_RF dm h s hs j out st -> 0 <= hs -> 0 <= j ->
  cblock_size (fr_t s hs j) = Some c -> 0 <= c -> c <= Zlength (fr_t s hs j) - ZSTD_blockHeaderSize ->
  bp_last (block_props_of (fr_t s hs j)) <> 1 ->
  (forall st'' out'', rblock false st (dm_content dm) (fr_t s hs j) out c (fh_blockSizeMax h) (fh_windowSize h) =
     Some (st'', out'') -> out'' = out' /\ st'' = st') ->
  fr_RF dm h s hs (j + ZSTD_blockHeaderSize + c) out' st'.
Proof.
  intros dm h s hs j out st c st' out' HRF Hhs Hj Hc Hc0 Hle Hlast Hrb f0 H0.
  destruct (HRF f0 H0) as [f Hf]. destruct f as [|f]; [contradiction|]. cbn [blocks_refused] in Hf.
  assert (Hl3: (Zlength (fr_t s hs j) <? ZSTD_blockHeaderSize) = false) by (apply Z.ltb_ge; lia).
  rewrite Hl3 in Hf.
  assert (Ht3: (bp_type (block_props_of (fr_t s hs j)) =? 3) = false).
  { apply Z.eqb_neq. destruct (bt_range _ _ Hc) as [E|[E|E]]; rewrite E; discriminate. }
  rewrite Ht3, Hc in Hf.
  replace (c >? Zlength (fr_t s hs j) - ZSTD_blockHeaderSize) with false in Hf
    by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
  destruct (rblock false st _ _ _ c _ _) as [[st'' out'']|] eqn:Er; [|contradiction].
  destruct (Hrb _ _ eq_refl) as [-> ->].
  destruct (Z.eqb_spec (bp_last (block_props_of (fr_t s hs j))) 1); [contradiction|].
  exists f. rewrite fr_t_next by assumption. exact Hf.
Qed.

(* ... through the last block: the end of the frame is refused *)
Lemma fr_RF_last: forall dm h s hs j out st c st' out',
  fr_RF dm h s hs j out st -> 0 <= hs -> 0 <= j ->
  cblock_size (fr_t s hs j) = Some c -> 0 <= c -> c <= Zlength (fr_t s hs j) - ZSTD_blockHeaderSize ->
  bp_last (block_props_of (fr_t s hs j)) = 1 ->
  (forall st'' out'', rblock false st (dm_content dm) (fr_t s hs j) out c (fh_blockSizeMax h) (fh_windowSize h) =
     Some (st'', out'') -> out'' = out' /\ st'' = st') ->
  fr_RE dm h s hs (j + ZSTD_blockHeaderSize + c) out'.
Proof.
  intros dm h s hs j out st c st' out' HRF Hhs Hj Hc Hc0 Hle Hlast Hrb f0 H0.
  destruct (HRF f0 H0) as [f Hf]. destruct f as [|f]; [contradiction|]. cbn [blocks_refused] in Hf.
  assert (Hl3: (Zlength (fr_t s hs j) <? ZSTD_blockHeaderSize) = false) by (apply Z.ltb_ge; lia).
  rewrite Hl3 in Hf.
  assert (Ht3: (bp_type (block_props_of (fr_t s hs j)) =? 3) = false).
  { apply Z.eqb_neq. destruct (bt_range _ _ Hc) as [E|[E|E]]; rewrite E; discriminate. }
  rewrite Ht3, Hc in Hf.
  replace (c >? Zlength (fr_t s hs j) - ZSTD_blockHeaderSize) with false in Hf
    by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
  destruct (rblock false st _ _ _ c _ _) as [[st'' out'']|] eqn:Er; [|contradiction].
  destruct (Hrb _ _ eq_refl) as [-> ->].
  rewrite Hlast, Z.eqb_refl in Hf.
  rewrite fr_t_next by assumption. exact Hf.
Qed.

Section FrmModel.
Local Open Scope Z_scope.
Local Open Scope bool_scope.


Lemma frm_db_step: forall f st hist t out bsm w c,
  cblock_size t = Some c -> c <= Zlength t - ZSTD_blockHeaderSize ->
  decode_blocks (S f) st hist t out bsm w =
  match blk_res st hist out t c bsm w with
  | None => None
  | Some (st', out') =>
      if bp_last (block_props_of t) =? 1 then Some (out', ZSTD_blockHeaderSize + c)
      else match decode_blocks f st' hist (skipn (Z.to_nat (ZSTD_blockHeaderSize + c)) t) out' bsm w with
           | Some (o, k) => Some (o, ZSTD_blockHeaderSize + c + k)
           | None => None
           end
  end.
Proof.
  intros. rewrite decode_blocks_step, H. destruct (Z.gtb_spec c (Zlength t - ZSTD_blockHeaderSize)); [lia|].
  reflexivity.
Qed.

Lemma frm_db_out: forall f st hist t out bsm w o k,
  decode_blocks f st hist t out bsm w = Some (o, k) -> exists u, o = out ++ u.
Proof.
  induction f; intros st hist t out bsm w o k H; [discriminate|].
  cbn [decode_blocks] in H.
  destruct (cblock_size t) as [c|]; [|discriminate].
  destruct (c >? Zlength t - ZSTD_blockHeaderSize); [discriminate|].
  match type of H with context [match ?r with None => None | Some _ => _ end] =>
    destruct r as [[st' out']|] eqn:Er; [|discriminate] end.
  assert (Ho: exists u, out' = out ++ u).
  { destruct (bp_type (block_props_of t) =? 0).
    - destruct (c >? bsm); [discriminate|]. injection Er as _ <-. eauto.
    - destruct (bp_type (block_props_of t) =? 1).
      + destruct (orb _ _); [discriminate|]. injection Er as _ <-. eauto.
      + destruct (decode_block _ _ _ _ _ _) as [[? ?]|]; [|discriminate]. injection Er as _ <-. eauto. }
  destruct Ho as [u ->].
  destruct (bp_last (block_props_of t) =? 1).
  - injection H as <- _. eauto.
  - destruct (decode_blocks f st' hist _ (out ++ u) bsm w) as [[o' k']|] eqn:Ed; [|discriminate].
    injection H as <- _. destruct (IHf _ _ _ _ _ _ _ _ Ed) as [u' ->]. exists (u ++ u'). rewrite <- app_assoc. reflexivity.
Qed.

(* the header of a frame with the magic number, as fr_hdr gives it, and decode_frame after it *)

(* fr_OT_next with 0 <= hs (fr_t clamps a negative offset to 0, and fr_OT_next is false then) *)
Lemma frm_OT_next: forall dm h s hs j out st c st' out',
  0 <= hs ->
  fr_OT dm h s hs j out st -> 0 <= j -> hs + j <= Zlength s ->
  cblock_size (fr_t s hs j) = Some c -> 0 <= c -> c <= Zlength (fr_t s hs j) - ZSTD_blockHeaderSize ->
  blk_res st (dm_content dm) out (fr_t s hs j) c (fh_blockSizeMax h) (fh_windowSize h) = Some (st', out') ->
  bp_last (block_props_of (fr_t s hs j)) <> 1 ->
  (forall st'' out'', rblock false st (dm_content dm) (fr_t s hs j) out c (fh_blockSizeMax h) (fh_windowSize h) =
     Some (st'', out'') -> out'' = out' /\ st'' = st') ->
  fr_OT dm h s hs (j + ZSTD_blockHeaderSize + c) out' st'.
Proof.
  intros dm h s hs j out st c st' out' Hhs [HOT [HBS [HRR HRF]]] Hj Hl Hc Hc0 Hle Hres Hlast Hrb.
  assert (Ht: fr_t s hs (j + ZSTD_blockHeaderSize + c) =
              skipn (Z.to_nat (ZSTD_blockHeaderSize + c)) (fr_t s hs j)).
  { unfold fr_t. rewrite !frm_sub_end, skipn_skipn. f_equal. unfold ZSTD_blockHeaderSize. lia. }
  refine (conj _ (conj _ (conj _ _))).
  4: { eapply fr_RF_next; eauto. }
  - intros o k HDB.
    destruct (HOT o k HDB) as [f Hf]. destruct f as [|f]; [discriminate|].
    rewrite (frm_db_step _ _ _ _ _ _ _ c Hc Hle), Hres in Hf.
    destruct (Z.eqb_spec (bp_last (block_props_of (fr_t s hs j))) 1); [contradiction|].
    match type of Hf with (match ?d with Some _ => _ | None => _ end) = _ =>
        destruct d as [[o' k']|] eqn:E; [|discriminate] end.
    injection Hf as <- Hk. exists f.
    rewrite Ht, E. f_equal. f_equal. lia.
  - intros f kk nb Hb. rewrite Ht in Hb.
    destruct (HBS (S f) (ZSTD_blockHeaderSize + c + kk) (nb + 1)) as (f' & nb' & Hr).
    + cbn [blocks_size]. rewrite Hc.
      replace (ZSTD_blockHeaderSize + c >? Zlength (fr_t s hs j)) with false
        by (rewrite Z.gtb_ltb; symmetry; apply Z.ltb_ge; unfold ZSTD_blockHeaderSize in *; lia).
      destruct (Z.eqb_spec (bp_last (block_props_of (fr_t s hs j))) 1); [contradiction|].
      rewrite Hb. reflexivity.
    + exists f', nb'. rewrite Hr. f_equal. f_equal. lia.
  - intros Hr. specialize (HRR Hr). rewrite Ht. inversion HRR as [t0 c0 _ _ Hl1 | t0 c0 Hc1 _ _ Hn]; subst.
    + contradiction.
    + rewrite Hc in Hc1. injection Hc1 as <-. exact Hn.
Qed.

End FrmModel.

(* ---------- model facts (pure) ---------- *)


(* the values of a parsed header the C reads back *)
Lemma gfh_range: forall x h,
  bytes_ok x -> get_frame_header x = FH_ok h ->
  0 <= fh_blockSizeMax h <= ZSTD_BLOCKSIZE_MAX /\ (fh_checksumFlag h = 0 \/ fh_checksumFlag h = 1) /\
  0 <= fh_contentSize h < 2 ^ 64 /\ 0 <= fh_windowSize h < 2 ^ 64 /\ 0 <= fh_dictID h < 2 ^ 32.
Proof.
  intros x h Hb H.
  destruct (Z.eqb_spec (le_field x 0 4) ZSTD_MAGICNUMBER) as [Hm|Hm].
  - destruct (frm_gfh_ok x h Hb Hm H) as (_&_&_&_&A&_&B&C&D&E). tauto.
  - unfold get_frame_header in H.
    destruct (Z.ltb_spec (Zlength x) 5).
    { destruct (Zlength x >? 0); [destruct (andb _ _)|]; discriminate. }
    destruct (Z.eqb_spec (le_field x 0 4) ZSTD_MAGICNUMBER); [contradiction|]. cbn [negb] in H.
    destruct (is_skippable_magic (le_field x 0 4)) eqn:Es; [|discriminate].
    destruct (Zlength x <? ZSTD_SKIPPABLEHEADERSIZE); [discriminate|].
    injection H as <-. cbn [fh_blockSizeMax fh_checksumFlag fh_contentSize fh_windowSize fh_dictID].
    pose proof (frm_le_field_bound x 4 4 Hb ltac:(lia)) as B1.
    pose proof (frm_le_field_bound x 0 4 Hb ltac:(lia)) as B2.
    pose proof (frm_skip_range (le_field x 0 4) ltac:(change (2 ^ (8 * 4)) with (2 ^ 32) in B2; lia) Es) as B3.
    unfold ZSTD_BLOCKSIZE_MAX, ZSTD_MAGIC_SKIPPABLE_START in *. simpl in B1, B2.
    split; [lia|]. split; [left; reflexivity|]. lia.
Qed.

Lemma fr_OT_init: forall dm h s hs, fr_OT dm h s hs 0 [] (dm_state dm).
Proof.
  intros dm h s hs. refine (conj _ (conj _ (conj _ _))).
  - intros o k E. exists (length (fr_rest s hs)). unfold fr_t. rewrite Z.add_0_r, Z.sub_0_r. exact E.
  - intros f kk nb E. exists f, nb. unfold fr_t in E. rewrite Z.add_0_r in E. exact E.
  - intros E. unfold fr_t. rewrite Z.add_0_r. exact E.
  - intros f0 E. exists f0. unfold fr_t. rewrite Z.add_0_r. exact E.
Qed.

(* with only Raw/RLE blocks, the C's block j is a Raw or RLE block *)
Lemma fr_OT_rr: forall dm h s hs j out st,
  fr_OT dm h s hs j out st -> blocks_rr (fr_rest s hs) -> bp_type (block_props_of (fr_t s hs j)) < 2.
Proof.
  intros dm h s hs j out st (_ & _ & HRR & _) Hr. specialize (HRR Hr).
  inversion HRR; assumption.
Qed.

(* the model stops (None) at the block j: it decodes nothing *)
Lemma fr_OT_none: forall dm h s hs j out st,
  fr_OT dm h s hs j out st -> 0 <= j -> hs + j <= Zlength s ->
  let t := fr_t s hs j in
  (cblock_size t = None \/
   (exists c, cblock_size t = Some c /\ c > Zlength t - ZSTD_blockHeaderSize) \/
   (exists c, cblock_size t = Some c /\ 0 <= c /\ c <= Zlength t - ZSTD_blockHeaderSize /\
              blk_res st (dm_content dm) out t c (fh_blockSizeMax h) (fh_windowSize h) = None)) ->
  forall o k, fr_DB dm h s hs <> Some (o, k).
Proof.
  intros dm h s hs j out st HOT Hj Hl. cbv zeta. intros Hcase o k HDB.
  destruct (proj1 HOT o k HDB) as [f Hf]. destruct f as [|f]; [discriminate|].
  destruct Hcase as [Hn | [[c [Hc Hgt]] | [c [Hc [_ [Hle Hres]]]]]].
  - rewrite decode_blocks_step, Hn in Hf. discriminate.
  - rewrite decode_blocks_step, Hc in Hf.
    destruct (Z.gtb_spec c (Zlength (fr_t s hs j) - ZSTD_blockHeaderSize)); [discriminate | lia].
  - rewrite (frm_db_step _ _ _ _ _ _ _ c Hc Hle), Hres in Hf. discriminate.
Qed.

(* the model's step gives out': whatever the model decodes extends out' *)
Lemma fr_OT_grow: forall dm h s hs j out st c st' out',
  fr_OT dm h s hs j out st -> 0 <= j -> hs + j <= Zlength s ->
  let t := fr_t s hs j in
  cblock_size t = Some c -> 0 <= c -> c <= Zlength t - ZSTD_blockHeaderSize ->
  blk_res st (dm_content dm) out t c (fh_blockSizeMax h) (fh_windowSize h) = Some (st', out') ->
  forall o k, fr_DB dm h s hs = Some (o, k) -> Zlength out' <= Zlength o.
Proof.
  intros dm h s hs j out st c st' out' HOT Hj Hl. cbv zeta. intros Hc Hc0 Hle Hres o k HDB.
  destruct (proj1 HOT o k HDB) as [f Hf]. destruct f as [|f]; [discriminate|].
  rewrite (frm_db_step _ _ _ _ _ _ _ c Hc Hle), Hres in Hf.
  destruct (bp_last (block_props_of (fr_t s hs j)) =? 1).
  - injection Hf as <- _. lia.
  - match type of Hf with (match ?d with Some _ => _ | None => _ end) = _ =>
      destruct d as [[o' k']|] eqn:E; [|discriminate] end.
    injection Hf as <- _. destruct (frm_db_out _ _ _ _ _ _ _ _ _ E) as [u ->].
    rewrite Zlength_app. pose proof (Zlength_nonneg u). lia.
Qed.

(* the last block *)
Lemma fr_OT_last: forall dm h s hs j out st c st' out',
  fr_OT dm h s hs j out st -> 0 <= j -> hs + j <= Zlength s ->
  let t := fr_t s hs j in
  cblock_size t = Some c -> 0 <= c -> c <= Zlength t - ZSTD_blockHeaderSize ->
  blk_res st (dm_content dm) out t c (fh_blockSizeMax h) (fh_windowSize h) = Some (st', out') ->
  bp_last (block_props_of t) = 1 ->
  forall o k, fr_DB dm h s hs = Some (o, k) -> o = out' /\ k = j + ZSTD_blockHeaderSize + c.
Proof.
  intros dm h s hs j out st c st' out' HOT Hj Hl. cbv zeta. intros Hc Hc0 Hle Hres Hlast o k HDB.
  destruct (proj1 HOT o k HDB) as [f Hf]. destruct f as [|f]; [discriminate|].
  rewrite (frm_db_step _ _ _ _ _ _ _ c Hc Hle), Hres, Hlast, Z.eqb_refl in Hf.
  injection Hf as <- Hk. split; [reflexivity | lia].
Qed.

(* the last block: the C's block walk is ZSTD_findFrameCompressedSize's *)
Lemma fr_OT_last_bs: forall dm h s hs j out st c,
  fr_OT dm h s hs j out st ->
  let t := fr_t s hs j in
  cblock_size t = Some c -> c <= Zlength t - ZSTD_blockHeaderSize ->
  bp_last (block_props_of t) = 1 ->
  exists f nb, blocks_size f (fr_rest s hs) = Some (j + ZSTD_blockHeaderSize + c, nb).
Proof.
  intros dm h s hs j out st c [_ [HBS _]]. cbv zeta. intros Hc Hle Hlast.
  destruct (HBS 1%nat (ZSTD_blockHeaderSize + c) 1) as (f & nb & Hr).
  - cbn [blocks_size]. rewrite Hc.
    replace (ZSTD_blockHeaderSize + c >? Zlength (fr_t s hs j)) with false
      by (rewrite Z.gtb_ltb; symmetry; apply Z.ltb_ge; unfold ZSTD_blockHeaderSize in *; lia).
    rewrite Hlast. reflexivity.
  - exists f, nb. rewrite Hr. f_equal. f_equal. lia.
Qed.

(* a block that is not the last *)
Lemma fr_OT_next: forall dm h s hs j out st c st' out',
  fr_OT dm h s hs j out st -> 0 <= hs -> 0 <= j -> hs + j <= Zlength s ->
  let t := fr_t s hs j in
  cblock_size t = Some c -> 0 <= c -> c <= Zlength t - ZSTD_blockHeaderSize ->
  blk_res st (dm_content dm) out t c (fh_blockSizeMax h) (fh_windowSize h) = Some (st', out') ->
  bp_last (block_props_of t) <> 1 ->
  (forall st'' out'', rblock false st (dm_content dm) t out c (fh_blockSizeMax h) (fh_windowSize h) =
     Some (st'', out'') -> out'' = out' /\ st'' = st') ->
  fr_OT dm h s hs (j + ZSTD_blockHeaderSize + c) out' st'.
Proof.
  intros dm h s hs j out st c st' out' HOT Hhs Hj Hl. cbv zeta. intros.
  eapply frm_OT_next; eauto.
Qed.

(* ======================================================================================
   v3: the frame under the decoding mode md (Params.decode_frame_m)
   ====================================================================================== *)

(* the frame header with Block_Maximum_Size capped by ZSTD_d_maxBlockSize (md_bmax): dctx->fParams after
   ZSTD_decompressFrame's shrink *)
Definition fh_cap (md: dmode) (h: frame_header) : frame_header :=
  {| fh_contentSize := fh_contentSize h; fh_windowSize := fh_windowSize h;
     fh_blockSizeMax := Z.min (fh_blockSizeMax h) (md_bmax md); fh_frameType := fh_frameType h;
     fh_headerSize := fh_headerSize h; fh_dictID := fh_dictID h; fh_checksumFlag := fh_checksumFlag h |}.

(* the bytes the magicless format drops (the magic number) *)
Definition mg_sh (mg: bool) : Z := if mg then 4 else 0.

(* what the C knows after ZSTD_decodeFrameHeader succeeded: s is long enough (ZSTD_FRAMEHEADERSIZE_MIN(format)
   + a block header), its header has hs bytes (ZSTD_frameHeaderSize_internal) and parses into h0, the loop's
   header h is h0 capped; without the selection (sel = false) the dictID check passed for dm *)
Definition fr_hdr3 (md: dmode) (sel: bool) (dm: dict_model) (s: list Z) (hs: Z) (h: frame_header) : Prop :=
  bytes_ok s /\ ZSTD_FRAMEHEADERSIZE_MIN - mg_sh (md_magicless md) + ZSTD_blockHeaderSize <= Zlength s /\
  hs = header_size_m (md_magicless md) s /\ hs + ZSTD_blockHeaderSize <= Zlength s /\
  exists h0, get_frame_header_m (md_magicless md) (sublist 0 hs s) = FH_ok h0 /\ h = fh_cap md h0 /\
    (sel = false -> fh_dictID h0 = 0 \/ fh_dictID h0 = dm_id dm) /\ md_dwin md = false.

(* whether the frame's checksum is validated (dctx->validateChecksum) *)
Definition vck (md: dmode) (h: frame_header) : bool := andb (fh_checksumFlag h =? 1) (negb (md_ignore md)).

(* ---------- ZSTD_decodeFrameHeader's result (FSSpecs3.dfh_post3) ---------- *)

Lemma dfh3_dictEnd: forall md sel d l tbl fs did pcs x r fs' d',
  dfh_post3 md sel d l tbl fs did pcs x r fs' d' -> fs_dictEnd fs' = fs_dictEnd fs.
Proof.
  intros. unfold dfh_post3 in H. destruct (get_frame_header_m _ x).
  - destruct H as [_ [_ [v [-> _]]]]. reflexivity.
  - destruct H as [_ [_ [v [-> _]]]]. reflexivity.
  - destruct H as [_ H]. destruct (_ || _)%bool; destruct H as [_ ->]; reflexivity.
Qed.

Lemma dfh3_cold: forall md sel d l tbl fs did pcs x r fs' d',
  dfh_post3 md sel d l tbl fs did pcs x r fs' d' -> fs_ddictIsCold fs' = fs_ddictIsCold fs.
Proof.
  intros. unfold dfh_post3 in H. destruct (get_frame_header_m _ x).
  - destruct H as [_ [_ [v [-> _]]]]. reflexivity.
  - destruct H as [_ [_ [v [-> _]]]]. reflexivity.
  - destruct H as [_ H]. destruct (_ || _)%bool; destruct H as [_ ->]; reflexivity.
Qed.

Lemma dfh3_r0: forall md sel d l tbl fs did pcs x r fs' d',
  dfh_post3 md sel d l tbl fs did pcs x r fs' d' -> is_error_code r = false -> r = 0.
Proof.
  intros. unfold dfh_post3 in H. destruct (get_frame_header_m _ x).
  - destruct H as [[H _] _]; congruence.
  - destruct H as [[H _] _]; congruence.
  - destruct H as [_ H]. destruct (_ || _)%bool; destruct H as [H _]; [congruence | destruct H; congruence].
Qed.

Lemma dfh3_dec_err: forall md sel d l tbl fs did pcs x r fs' d',
  dfh_post3 md sel d l tbl fs did pcs x r fs' d' -> is_error_code r = true -> dec_err r.
Proof.
  intros. unfold dfh_post3 in H. destruct (get_frame_header_m _ x).
  - destruct H as [H _]; exact H.
  - destruct H as [H _]; exact H.
  - destruct H as [_ H]. destruct (_ || _)%bool; destruct H as [H _]; [subst r; discriminate | exact H].
Qed.

(* the dictionary fields after the header: unchanged, or the DDict rq the selection found *)
Lemma dfh3_dict: forall md sel d l tbl fs did pcs x r fs' d',
  dfh_post3 md sel d l tbl fs did pcs x r fs' d' ->
  d' = d \/ exists h, get_frame_header_m (md_magicless md) x = FH_ok h /\ sel = true /\
                      sel_r d l tbl (fh_dictID h) <> nullval /\ d' = switch_fields (sel_r d l tbl (fh_dictID h)).
Proof.
  intros. unfold dfh_post3 in H. destruct (get_frame_header_m _ x) as [|k|h] eqn:E.
  - left. tauto.
  - left. tauto.
  - destruct H as [Hd _]. unfold sel_dict in Hd.
    destruct sel; [|left; exact Hd].
    destruct (eq_dec (sel_r d l tbl (fh_dictID h)) nullval) as [Hn|Hn]; [left; exact Hd|].
    right. exists h. auto.
Qed.

(* ZSTD_decodeFrameHeader succeeded: the header h, the new frame fields (did' the context's dictID after the
   selection) *)
Lemma dfh3_ok0: forall md sel d l tbl fs did pcs x fs' d',
  dfh_post3 md sel d l tbl fs did pcs x 0 fs' d' ->
  exists h, get_frame_header_m (md_magicless md) x = FH_ok h /\
    let rq := if sel then sel_r d l tbl (fh_dictID h) else nullval in
    let did' := if eq_dec rq nullval then did else fh_dictID h in
    d' = sel_dict d rq /\ (fh_dictID h = 0 \/ fh_dictID h = did') /\
    fs' = fsu_processedCSize
            (fsu_xxh (fsu_validateChecksum (fsu_dictID (fsu_fParams fs (fh_val h)) (Vint (Int.repr did')))
                        (Vint (Int.repr (if vck md h then 1 else 0))))
               (if vck md h then Some nil else fs_xxh fs))
            (Vlong (Int64.repr (pcs + Zlength x))).
Proof.
  intros. unfold dfh_post3 in H. destruct (get_frame_header_m _ x) as [ | k | h0].
  - destruct H as [[H _] _]. vm_compute in H. discriminate.
  - destruct H as [[H _] _]. vm_compute in H. discriminate.
  - exists h0. split; [reflexivity|]. cbv zeta in *. destruct H as [Hd H]. split; [exact Hd|].
    destruct (_ || _)%bool eqn:E.
    + destruct H as [_ ->]. split; [|reflexivity].
      apply orb_true_iff in E. destruct E as [E | E]; apply Z.eqb_eq in E; auto.
    + destruct H as [[H _] _]. vm_compute in H. discriminate.
Qed.

End CM_Frames3Pure_1.
