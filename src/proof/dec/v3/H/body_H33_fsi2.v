(* Subtree H: ZSTD_getcBlockSize, ZSTD_findFrameSizeInfo (the blocks walk), against H_G (HSpecs.v).
   API v3.3: src/proof/dec/H/body_H_fsi.v with the exact error code of fh_post_adv (FH_err => dec_err r /\ r = code). *)
Require Import Zstd.proof.dec.H.HLemmas.
Local Open Scope logic.

(* ZSTD_blockHeaderSize out of zstd_globals *)
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

Lemma zg_bhs: forall gv,
  zstd_globals gv = data_at Ers tulong (Vlong (Int64.repr 3)) (gv _ZSTD_blockHeaderSize) * zg_rest gv.
Proof.
  intros gv. unfold zstd_globals, zg_rest, ZSTD_blockHeaderSize_val.
  apply pred_ext; cancel.
Qed.

Lemma win_ok_len: forall sh N c off n s, win_ok sh N c off n s ->
  0 <= n <= 2 ^ 63 - 1 /\ 0 <= off /\ off + n <= N /\ Zlength s = n /\ Zlength c = N.
Proof. intros. destruct H as [? [? [? [? [? [? ?]]]]]]. subst. pose proof (Zlength_nonneg s). lia. Qed.

Lemma le_value_rng: forall l, bytes_ok l -> 0 <= le_value l < 2 ^ (8 * Zlength l).
Proof.
  intros l H. induction H; cbn [le_value].
  - rewrite Zlength_nil. simpl. lia.
  - rewrite Zlength_cons.
    rewrite <- Z.add_1_r, Z.mul_add_distr_l, Z.pow_add_r by (pose proof (Zlength_nonneg l); lia).
    unfold is_byte in H. change (2^(8*1)) with 256. nia.
Qed.

Lemma le_field_rng: forall s i k, bytes_ok s -> 0 <= k -> 0 <= le_field s i k < 2 ^ (8 * k).
Proof.
  intros s i k H Hk. unfold le_field, slice.
  assert (Hb: bytes_ok (firstn (Z.to_nat k) (skipn (Z.to_nat i) s))).
  { unfold bytes_ok in *. apply Forall_firstn. apply Forall_skipn. auto. }
  pose proof (le_value_rng _ Hb).
  assert (Zlength (firstn (Z.to_nat k) (skipn (Z.to_nat i) s)) <= k).
  { rewrite Zlength_correct, firstn_length. lia. }
  split; [lia|]. eapply Z.lt_le_trans; [apply H0|]. apply Z.pow_le_mono_r; lia.
Qed.

Lemma bp_ints: forall h, 0 <= h < 2 ^ 24 ->
  Int.and (Int.shru (Int.repr h) (Int.repr 1)) (Int.repr 3) = Int.repr (Z.land (Z.shiftr h 1) 3) /\
  Int.and (Int.repr h) (Int.repr 1) = Int.repr (Z.land h 1) /\
  Int.shru (Int.repr h) (Int.repr 3) = Int.repr (Z.shiftr h 3) /\
  0 <= Z.land (Z.shiftr h 1) 3 <= 3 /\ 0 <= Z.shiftr h 3 < 2 ^ 21.
Proof.
  intros h Hh.
  assert (E1: Z.shiftr h 1 = h / 2) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (E3: Z.shiftr h 3 = h / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (E4: Z.land (Z.shiftr h 1) 3 = (h / 2) mod 4).
  { rewrite E1. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. }
  unfold Int.and, Int.shru.
  rewrite (Int.unsigned_repr h), (Int.unsigned_repr 1), (Int.unsigned_repr 3) by rep_lia.
  rewrite (Int.unsigned_repr (Z.shiftr h 1)) by (rewrite E1; split; [apply Z.div_pos | apply Z.div_le_upper_bound]; rep_lia).
  repeat split; try reflexivity; try rewrite E4; try rewrite E3; try lia.
  all: try (pose proof (Z.mod_pos_bound (h / 2) 4); lia).
  - apply Z.div_pos; lia.
  - apply Z.div_lt_upper_bound; lia.
Qed.

Ltac dw0 := repeat apply -> seq_assoc;
  match goal with
  | |- semax _ ?Pre (Ssequence (Sloop _ Sbreak) _) _ => forward_loop Pre break: Pre
  | |- semax _ ?Pre (Sloop _ Sbreak) _ => forward_loop Pre break: Pre
  end.

Ltac dw0P Q := repeat apply -> seq_assoc;
  match goal with |- semax _ (PROPx ?P ?QR) (Ssequence (Sloop _ Sbreak) _) _ =>
    forward_loop (PROPx P QR) break: (PROPx (Q :: P) QR) end.

Ltac skip_loop := dw0; [entailer! | forward; entailer! | ].
Ltac if0_loop := dw0; [entailer! |
  match goal with |- semax _ ?P _ _ => forward_if P end; [contradiction | forward; entailer! | forward; entailer!] | ].
Ltac ret_err := skip_loop; if0_loop; skip_loop; skip_loop.

Ltac dec_err_c :=
  unfold dec_err, ZSTD_error_noForwardProgress_destFull, ZSTD_error_noForwardProgress_inputEmpty;
  split; [reflexivity | split; let E := fresh "E" in intro E; compute in E; discriminate].

Lemma body_getcBlockSize: semax_body Vprog H_G f_ZSTD_getcBlockSize ZSTD_getcBlockSize_spec.
Proof.
  start_function.
  destruct (win_ok_len _ _ _ _ _ _ H) as [Hn [Hoff [HoN [_ HcN]]]].
  rewrite zg_bhs. Intros.
  dw0P (3 <= Zlength s); [entailer! | |].
  { forward. forward_if.
    { ret_err. forward. Exists (Int64.unsigned (Int64.repr (-72))) (default_val t_bp).
      entailer!.
      - unfold cblock_size. rewrite (proj2 (Z.ltb_lt _ _)) by (unfold ZSTD_blockHeaderSize; lia).
        split; [dec_err_c | rewrite Int64.repr_unsigned; reflexivity].
      - rewrite zg_bhs. cancel. }
    forward. entailer!. }
  Intros.
  assert_PROP (field_compatible (tarray tuchar N) [] base) as FC by entailer!.
  rewrite (win_split sh N c off s base H FC). Intros.
  pose proof H as Hw. destruct H as [Hsh [_ [_ [HN [_ [_ [Hb _]]]]]]].
  apply -> seq_assoc. forward_call (sh, offset_val off base, s, 0).
  { unfold mem_read_pre. repeat split; auto; try lia. unfold bytes_ok in *. apply Forall_sublist; auto. }
  pose proof (le_field_rng s 0 3 Hb ltac:(lia)) as Hh.
  set (h := le_field s 0 3) in *.
  forward. forward. forward. forward. forward.
  destruct (bp_ints h ltac:(lia)) as [E1 [E2 [E3 [Rt Ro]]]]. rewrite E1, E2, E3.
  assert (Hbp: block_props_of s = {| bp_last := Z.land h 1; bp_type := Z.land (Z.shiftr h 1) 3;
                                     bp_origSize := Z.shiftr h 3 |}) by reflexivity.
  set (os := Z.shiftr h 3) in *.
  assert (Hlt: (Zlength s <? ZSTD_blockHeaderSize) = false) by (apply Z.ltb_ge; unfold ZSTD_blockHeaderSize; lia).
  forward. forward_if.
  { forward. Exists 1 (bp_val (block_props_of s)). entailer!.
    - unfold cblock_size. rewrite Hlt, Hbp. cbn [bp_type]. rewrite H. simpl. auto.
    - rewrite zg_bhs, (win_split _ _ _ _ _ _ Hw FC). cancel. }
  dw0P (Z.land (Z.shiftr h 1) 3 <> 3); [entailer! | |].
  { forward. forward_if.
    { ret_err. forward. Exists (Int64.unsigned (Int64.repr (-20))) (bp_val (block_props_of s)). entailer!.
      - unfold cblock_size. rewrite Hlt, Hbp. cbn [bp_type]. rewrite H1. split; [dec_err_c | rewrite Int64.repr_unsigned; reflexivity].
      - rewrite zg_bhs, (win_split _ _ _ _ _ _ Hw FC). cancel. }
    forward. entailer!. }
  Intros. forward. Exists os (bp_val (block_props_of s)). entailer!.
  - unfold cblock_size. rewrite Hlt, Hbp. cbn [bp_type bp_origSize].
    rewrite (proj2 (Z.eqb_neq _ _)) by auto. rewrite (proj2 (Z.eqb_neq _ _)) by auto. auto.
  - rewrite zg_bhs, (win_split _ _ _ _ _ _ Hw FC). cancel.
Qed.

(* ---------- ZSTD_findFrameSizeInfo: the model side ---------- *)

Lemma skipn_sublist_Z: forall (l: list Z) k, 0 <= k <= Zlength l ->
  skipn (Z.to_nat k) l = sublist k (Zlength l) l.
Proof.
  intros l k Hk. unfold sublist. rewrite firstn_all2; auto.
  rewrite Zlength_correct, Nat2Z.id. lia.
Qed.

Lemma bytes_ok_skipn: forall n l, bytes_ok l -> bytes_ok (skipn n l).
Proof. intros. unfold bytes_ok in *. apply Forall_skipn. auto. Qed.

Lemma cblock_size_nonneg: forall l c, bytes_ok l -> cblock_size l = Some c -> 3 <= Zlength l /\ 0 <= c.
Proof.
  intros l c Hb H. unfold cblock_size in H. unfold ZSTD_blockHeaderSize in H.
  destruct (Zlength l <? 3) eqn:E; [discriminate|]. apply Z.ltb_ge in E.
  destruct (bp_type (block_props_of l) =? 1); [inversion H; lia|].
  destruct (bp_type (block_props_of l) =? 3); [discriminate|]. inversion H; subst.
  split; auto. unfold block_props_of; simpl. apply Z.shiftr_nonneg.
  apply (le_field_rng l 0 3 Hb); lia.
Qed.

Lemma cblock_size_bound: forall l c, bytes_ok l -> cblock_size l = Some c -> 0 <= c < 2 ^ 21.
Proof.
  intros l c Hb H. unfold cblock_size in H. unfold ZSTD_blockHeaderSize in H.
  destruct (Zlength l <? 3) eqn:E; [discriminate|].
  destruct (bp_type (block_props_of l) =? 1); [inversion H; lia|].
  destruct (bp_type (block_props_of l) =? 3); [discriminate|]. inversion H; subst.
  unfold block_props_of; simpl. pose proof (le_field_rng l 0 3 Hb ltac:(lia)).
  rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

Lemma blocks_size_fuel: forall f1 f2 l, bytes_ok l -> (length l <= f1)%nat -> (length l <= f2)%nat ->
  blocks_size f1 l = blocks_size f2 l.
Proof.
  induction f1 as [|f1 IH]; intros f2 l Hb H1 H2.
  - destruct l; [|simpl in H1; lia]. destruct f2; reflexivity.
  - destruct f2 as [|f2]. { destruct l; [reflexivity | simpl in H2; lia]. }
    simpl. destruct (cblock_size l) as [c|] eqn:E; auto.
    destruct (cblock_size_nonneg _ _ Hb E) as [Hl Hc].
    destruct (_ >? _) eqn:E2; auto. destruct (_ =? 1); auto.
    rewrite (IH f2); auto.
    + apply bytes_ok_skipn; auto.
    + rewrite length_skipn. unfold ZSTD_blockHeaderSize. lia.
    + rewrite length_skipn. unfold ZSTD_blockHeaderSize. lia.
Qed.

(* one block of the walk, with fuel = the length of the rest *)
Lemma blocks_size_step: forall l c, bytes_ok l -> cblock_size l = Some c -> 3 + c <= Zlength l ->
  bp_last (block_props_of l) <> 1 ->
  blocks_size (length l) l =
  match blocks_size (length (sublist (3 + c) (Zlength l) l)) (sublist (3 + c) (Zlength l) l) with
  | Some (k, nb) => Some (3 + c + k, nb + 1)
  | None => None
  end.
Proof.
  intros l c Hb E Hle Hlast. destruct (cblock_size_nonneg _ _ Hb E) as [Hl Hc].
  destruct l as [|b l']; [rewrite Zlength_nil in Hl; lia|].
  set (l := b :: l') in *. change (length l) with (S (length l')). cbn [blocks_size].
  rewrite E. unfold ZSTD_blockHeaderSize.
  rewrite Z.gtb_ltb, (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.eqb_neq _ _)) by auto.
  rewrite <- skipn_sublist_Z by lia.
  rewrite (blocks_size_fuel (length l') (length (skipn (Z.to_nat (3 + c)) l))); auto.
  - apply bytes_ok_skipn; auto.
  - rewrite length_skipn. unfold l; simpl length. lia.
Qed.

Lemma blocks_size_last: forall l c, bytes_ok l -> cblock_size l = Some c -> 3 + c <= Zlength l ->
  bp_last (block_props_of l) = 1 -> blocks_size (length l) l = Some (3 + c, 1).
Proof.
  intros l c Hb E Hle Hlast. destruct (cblock_size_nonneg _ _ Hb E) as [Hl Hc].
  destruct l as [|b l']; [rewrite Zlength_nil in Hl; lia|].
  set (l := b :: l') in *. change (length l) with (S (length l')). cbn [blocks_size].
  rewrite E. unfold ZSTD_blockHeaderSize.
  rewrite Z.gtb_ltb, (proj2 (Z.ltb_ge _ _)) by lia. rewrite Hlast. reflexivity.
Qed.

Lemma blocks_size_err1: forall l, cblock_size l = None -> blocks_size (length l) l = None.
Proof. intros l E. destruct l; [reflexivity|]. simpl length. cbn [blocks_size]. rewrite E. reflexivity. Qed.

Lemma blocks_size_err2: forall l c, cblock_size l = Some c -> 3 + c > Zlength l ->
  blocks_size (length l) l = None.
Proof.
  intros l c E Hgt. destruct l; [discriminate|]. simpl length. cbn [blocks_size]. rewrite E.
  unfold ZSTD_blockHeaderSize. rewrite Z.gtb_ltb, (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Qed.

Lemma byte_at_rng: forall s i, bytes_ok s -> 0 <= byte_at s i < 256.
Proof.
  intros s i Hb. unfold byte_at. destruct (nth_in_or_default (Z.to_nat i) s 0) as [Hin|Heq].
  - unfold bytes_ok in Hb. rewrite Forall_forall in Hb. apply Hb in Hin. unfold is_byte in Hin. lia.
  - rewrite Heq. lia.
Qed.

Lemma land1_rng: forall x, 0 <= Z.land x 1 <= 1.
Proof.
  intros. replace (Z.land x 1) with (Z.land x (Z.ones 1)) by reflexivity. rewrite Z.land_ones by lia.
  pose proof (Z.mod_pos_bound x (2^1) ltac:(lia)). change (2^1) with 2 in *. lia.
Qed.

Lemma nth4_rng: forall n a b c d, 0 <= a <= 8 -> 0 <= b <= 8 -> 0 <= c <= 8 -> 0 <= d <= 8 ->
  0 <= nth n [a; b; c; d] 0 <= 8.
Proof. intros. destruct n as [|[|[|[|]]]]; simpl; try lia. destruct n; lia. Qed.

Lemma fhd_header_size_rng: forall fhd, 5 <= fhd_header_size fhd <= 18.
Proof.
  intros. unfold fhd_header_size. pose proof (land1_rng (Z.shiftr fhd 5)).
  assert (0 <= nth (Z.to_nat (Z.land fhd 3)) [0; 1; 2; 4] 0 <= 4).
  { destruct (Z.to_nat _) as [|[|[|[|]]]]; simpl; try lia. destruct n; lia. }
  assert (0 <= nth (Z.to_nat (Z.shiftr fhd 6)) [0; 2; 4; 8] 0 <= 8) by (apply nth4_rng; lia).
  set (a := nth (Z.to_nat (Z.land fhd 3)) [0; 1; 2; 4] 0) in *. clearbody a.
  destruct (Z.shiftr fhd 6 =? 0) eqn:E6.
  - apply Z.eqb_eq in E6. rewrite E6. change (nth (Z.to_nat 0) [0; 2; 4; 8] 0) with 0.
    destruct (_ && _)%bool; lia.
  - rewrite andb_false_r. lia.
Qed.

Lemma fcs_rng: forall s p (A B C D: bool), bytes_ok s ->
  0 <= (if A then (if B then byte_at s p else ZSTD_CONTENTSIZE_UNKNOWN)
        else (if C then le_field s p 2 + 256 else if D then le_field s p 4 else le_field s p 8))
    <= Int64.max_unsigned.
Proof.
  intros s p A B C D Hb.
  pose proof (byte_at_rng s p Hb). pose proof (le_field_rng s p 2 Hb ltac:(lia)).
  pose proof (le_field_rng s p 4 Hb ltac:(lia)). pose proof (le_field_rng s p 8 Hb ltac:(lia)).
  unfold ZSTD_CONTENTSIZE_UNKNOWN. destruct A, B, C, D; simpl in *; rep_lia.
Qed.

Lemma gfh_more: forall s k, get_frame_header s = FH_more k -> 5 <= k <= 18.
Proof.
  intros s k H. unfold get_frame_header in H.
  destruct (Zlength s <? 5).
  { destruct (Zlength s >? 0); [destruct (_ && _)%bool|]; inversion H; lia. }
  destruct (negb _).
  { destruct (is_skippable_magic _); [|discriminate]. destruct (_ <? _); inversion H. unfold ZSTD_SKIPPABLEHEADERSIZE; lia. }
  cbv zeta in H. destruct (Zlength s <? fhd_header_size _).
  { inversion H. apply fhd_header_size_rng. }
  destruct (negb _); [discriminate|]. destruct (_ && _)%bool; discriminate.
Qed.

Lemma gfh_ok: forall s h, bytes_ok s -> get_frame_header s = FH_ok h ->
  0 <= fh_headerSize h <= Zlength s /\ fh_headerSize h <= 18 /\ (fh_checksumFlag h = 0 \/ fh_checksumFlag h = 1) /\
  0 <= fh_contentSize h <= Int64.max_unsigned /\ 0 <= fh_blockSizeMax h <= ZSTD_BLOCKSIZE_MAX.
Proof.
  intros s h Hb H. unfold get_frame_header in H.
  destruct (Zlength s <? 5) eqn:E5.
  { destruct (Zlength s >? 0); [destruct (_ && _)%bool|]; discriminate. }
  apply Z.ltb_ge in E5.
  destruct (negb _).
  { destruct (is_skippable_magic _); [|discriminate].
    destruct (Zlength s <? ZSTD_SKIPPABLEHEADERSIZE) eqn:E8; [discriminate|].
    apply Z.ltb_ge in E8. inversion H; subst; clear H. simpl.
    pose proof (le_field_rng s 4 4 Hb ltac:(lia)).
    unfold ZSTD_SKIPPABLEHEADERSIZE, ZSTD_BLOCKSIZE_MAX in *. rep_lia. }
  cbv zeta in H. destruct (Zlength s <? fhd_header_size _) eqn:Ef; [discriminate|].
  apply Z.ltb_ge in Ef.
  destruct (negb _); [discriminate|]. destruct (_ && _)%bool; [discriminate|].
  inversion H; subst; clear H. simpl.
  pose proof (fhd_header_size_rng (byte_at s 4)).
  pose proof (land1_rng (Z.shiftr (byte_at s 4) 2)).
  pose proof (byte_at_rng s 5 Hb) as H5.
  match goal with |- context [if ?A then (if ?B then byte_at s ?p else ZSTD_CONTENTSIZE_UNKNOWN)
                             else (if ?C then le_field s ?p 2 + 256 else if ?D then le_field s ?p 4
                                   else le_field s ?p 8)] =>
    pose proof (fcs_rng s p A B C D Hb) as Hfcs;
    set (fcs := (if A then (if B then byte_at s p else ZSTD_CONTENTSIZE_UNKNOWN)
                 else (if C then le_field s p 2 + 256 else if D then le_field s p 4 else le_field s p 8))) in *
  end.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [auto|].
  split; [| apply Z.le_min_r]. apply Z.min_glb; [| unfold ZSTD_BLOCKSIZE_MAX; lia].
  destruct (_ =? 1); [lia|].
  assert (0 <= Z.shiftr (byte_at s 5) 3) by (apply Z.shiftr_nonneg; lia).
  assert (0 <= Z.land (byte_at s 5) 7) by (apply Z.land_nonneg; lia).
  set (w := Z.shiftr (byte_at s 5) 3 + ZSTD_WINDOWLOG_ABSOLUTEMIN).
  assert (0 < 2 ^ w) by (apply Z.pow_pos_nonneg; unfold w, ZSTD_WINDOWLOG_ABSOLUTEMIN; lia).
  assert (0 <= Z.shiftr (2 ^ w) 3) by (apply Z.shiftr_nonneg; lia).
  nia.
Qed.

Lemma skip_magic_int: forall m,
  Int.eq (Int.repr (Z.land m (-16))) (Int.repr 407710288) = is_skippable_magic m.
Proof.
  intros m. unfold Int.eq. rewrite !Int.unsigned_repr_eq.
  assert (E: Z.land m (-16) mod Int.modulus = Z.land m ZSTD_MAGIC_SKIPPABLE_MASK).
  { change Int.modulus with (2 ^ 32). rewrite <- Z.land_ones by lia. rewrite <- Z.land_assoc. reflexivity. }
  rewrite E. unfold is_skippable_magic. change (407710288 mod Int.modulus) with ZSTD_MAGIC_SKIPPABLE_START.
  destruct (zeq _ _); symmetry; [apply Z.eqb_eq | apply Z.eqb_neq]; auto.
Qed.

Ltac fif_temp i V := match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
  forward_if (PROPx P (LOCALx (temp i V :: Q) (SEPx R))) end.

Lemma zero_val_fsi: zero_val t_fsi = (Vlong Int64.zero, (Vlong Int64.zero, Vlong Int64.zero)).
Proof.
  assert (Z1: fst (zero_val t_fsi) = zero_val tulong) by (rewrite (zero_val_eq t_fsi); reflexivity).
  assert (Z2: fst (snd (zero_val t_fsi)) = zero_val tulong) by (rewrite (zero_val_eq t_fsi); reflexivity).
  assert (Z3: snd (snd (zero_val t_fsi)) = zero_val tulong) by (rewrite (zero_val_eq t_fsi); reflexivity).
  unfold tulong in Z1, Z2, Z3. rewrite zero_val_Tlong in Z1, Z2, Z3.
  destruct (zero_val t_fsi) as [a [b d]]. simpl in *. subst. reflexivity.
Qed.

Lemma body_findFrameSizeInfo: semax_body Vprog H_G f_ZSTD_findFrameSizeInfo ZSTD_findFrameSizeInfo_spec.
Proof.
  start_function.
  pose proof H as Hw. destruct (win_ok_len _ _ _ _ _ _ H) as [Hn [Hoff [HoN [_ HcN]]]].
  destruct H as [Hsh [_ [_ [HN [_ [_ [Hb _]]]]]]].
  assert_PROP (field_compatible (tarray tuchar N) [] base) as FC by entailer!.
  assert_PROP (field_compatible t_fsi [] pf) as FCf by entailer!.
  sep_apply (data_at__memory_block_cancel shf t_fsi pf).
  forward_call (shf, pf, 0, sizeof t_fsi).
  sep_apply (memset_zero_data_at shf t_fsi pf); auto.
  rewrite zero_val_fsi.
  fif_temp _t'7 (Vint (if Zlength s >=? 8 then Int.one else Int.zero)).
  { forward. entailer!. unfold Int64.cmpu, Int64.ltu. change (Int.signed (Int.repr 8)) with 8.
    rewrite !Int64.unsigned_repr by rep_lia.
    destruct (zlt _ _); destruct (Zlength s >=? 8) eqn:E; simpl; auto; rewrite Z.geb_leb in E;
      [apply Z.leb_le in E | apply Z.leb_gt in E]; lia. }
  { elim H; reflexivity. }
  set (skp := ((Zlength s >=? ZSTD_SKIPPABLEHEADERSIZE) && is_skippable_magic (le_field s 0 4))%bool).
  fif_temp _t'8 (Vint (if skp then Int.one else Int.zero)).
  { destruct (Zlength s >=? 8) eqn:E8; [|elim H; reflexivity].
    rewrite Z.geb_leb in E8. apply Z.leb_le in E8.
    rewrite (win_split sh N c off s base Hw FC). Intros.
    forward_call (sh, offset_val off base, s, 0).
    { unfold mem_read_pre. repeat split; auto; try lia. unfold bytes_ok in *. apply Forall_sublist; auto. }
    forward. entailer!.
    - rewrite skip_magic_int. unfold skp, ZSTD_SKIPPABLEHEADERSIZE.
      rewrite (proj2 (Z.geb_le _ _)) by lia. simpl. destruct (is_skippable_magic _); reflexivity.
    - rewrite (win_split sh _ c off s base Hw FC). cancel. }
  { forward. entailer!. unfold skp, ZSTD_SKIPPABLEHEADERSIZE.
    destruct (Zlength s >=? 8) eqn:E8; [discriminate|]. reflexivity. }
  assert (Hfsi: frame_size_info s = if skp then match skippable_frame_size s with
                                    Some k => Some (k, 0) | None => None end
                else match get_frame_header s with
                | FH_ok h =>
                    let rest := skipn (Z.to_nat (fh_headerSize h)) s in
                    match blocks_size (length rest) rest with
                    | None => None
                    | Some (k, nb) =>
                        let sz := fh_headerSize h + k in
                        let bound := if fh_contentSize h =? ZSTD_CONTENTSIZE_UNKNOWN
                                     then (nb * fh_blockSizeMax h) mod 2 ^ 64 else fh_contentSize h in
                        if fh_checksumFlag h =? 1 then
                          (if Zlength s - sz <? 4 then None else Some (sz + 4, bound))
                        else Some (sz, bound)
                    end
                | _ => None
                end) by reflexivity.
  clearbody skp.
  forward_if.
  { destruct skp; [|elim H; reflexivity].
    forward_call (sh, base, N, c, off, s).
    Intros r. forward. forward.
    Exists (Vlong Int64.zero) r 0. entailer!.
    rewrite Hfsi. destruct (skippable_frame_size s); auto. apply dec_err_is_error; assumption. }
  destruct skp; [apply Int.one_not_zero in H; contradiction|].
  forward. forward. forward. forward.
  forward_call (gv, Tsh, v_zfh, default_val t_fh, sh, base, N, c, off, s).
  Intros vret. destruct vret as [r v]. simpl fst in *. simpl snd in *.
  unfold fh_post_adv, fh_post in H1. destruct (get_frame_header s) as [|k|h] eqn:Eg.
  { (* FH_err *)
    destruct H1 as [H1 _]. pose proof (dec_err_is_error _ H1) as H1e. forward_call r. rewrite H1e.
    forward_if; [| apply Int.one_not_zero in H2; contradiction].
    forward_call (shf, pf, Vlong Int64.zero, Vlong Int64.zero, Vlong Int64.zero, r).
    forward. Exists (Vlong Int64.zero) r ZSTD_CONTENTSIZE_ERROR.
    apply andp_right. { apply prop_right. unfold ZSTD_CONTENTSIZE_ERROR. rewrite Hfsi. split; [auto | split; [rep_lia | auto]]. }
    sep_apply (data_at_data_at_ Tsh t_fh v v_zfh). cancel. }
  { (* FH_more *)
    destruct H1 as [H1 _]. subst r. pose proof (gfh_more s k Eg) as Hk.
    forward_call k.
    replace (is_error_code k) with false by (unfold is_error_code; symmetry; apply Z.ltb_ge; lia).
    forward_if; [exfalso; match goal with Hx: Int.repr 0 <> _ |- _ => apply Hx; reflexivity end |].
    forward_if; [| exfalso; match goal with Hx: Int64.unsigned _ >= Int64.unsigned _ |- _ =>
      rewrite !Int64.unsigned_repr in Hx by rep_lia; lia end].
    forward_call (shf, pf, Vlong Int64.zero, Vlong Int64.zero, Vlong Int64.zero, Int64.unsigned (Int64.repr (-72))).
    { entailer!. rewrite Int64.repr_unsigned. reflexivity. }
    forward. Exists (Vlong Int64.zero) (Int64.unsigned (Int64.repr (-72))) ZSTD_CONTENTSIZE_ERROR.
    apply andp_right. { apply prop_right. unfold ZSTD_CONTENTSIZE_ERROR. rewrite Hfsi. split; [rep_lia | split; [rep_lia | auto]]. }
    sep_apply (data_at_data_at_ Tsh t_fh v v_zfh). cancel. }
  (* FH_ok *)
  destruct H1 as [-> ->].
  destruct (gfh_ok s h Hb Eg) as [Hhs [Hhs18 [Hcf [Hfcs Hbsm]]]].
  forward_call 0.
  change (is_error_code 0) with false.
  forward_if; [exfalso; match goal with Hx: Int.repr 0 <> _ |- _ => apply Hx; reflexivity end |].
  forward_if; [exfalso; match goal with Hx: Int64.unsigned _ < Int64.unsigned _ |- _ =>
      rewrite !Int64.unsigned_repr in Hx by rep_lia; lia end |].
  unfold fh_val. forward. forward. forward. forward.
  cbv zeta in Hfsi. fold (fh_val h).
  set (hs := fh_headerSize h) in *.
  set (rest0 := skipn (Z.to_nat hs) s) in *.
  forward_loop (EX p: Z, EX nb: Z, EX vbp: reptype t_bp,
    PROP (hs <= p <= Zlength s; 0 <= nb <= p;
          blocks_size (length rest0) rest0 =
          match blocks_size (length (sublist p (Zlength s) s)) (sublist p (Zlength s) s) with
          | Some (k, n) => Some ((p - hs + k)%Z, (nb + n)%Z) | None => None end)
    LOCAL (temp _remainingSize (Vlong (Int64.repr (Zlength s - p))); temp _ip (offset_val (off + p) base);
           temp _nbBlocks (Vlong (Int64.repr nb)); temp _ipstart (offset_val off base);
           lvar _blockProperties (Tstruct ___gp_blockProperties_t noattr) v_blockProperties;
           lvar _zfh (Tstruct ___gp_ZSTD_FrameHeader noattr) v_zfh; gvars gv; temp _frameSizeInfo pf)
    SEP (zstd_globals gv; data_at Tsh t_fh (fh_val h) v_zfh; data_at sh (tarray tuchar N) c base;
         data_at shf t_fsi (Vlong Int64.zero, (Vlong Int64.zero, Vlong Int64.zero)) pf;
         data_at Tsh t_bp vbp v_blockProperties))%assert
  break: (EX p: Z, EX nb: Z, EX vbp: reptype t_bp,
    PROP (hs <= p <= Zlength s; 0 <= nb <= p; blocks_size (length rest0) rest0 = Some ((p - hs)%Z, nb))
    LOCAL (temp _remainingSize (Vlong (Int64.repr (Zlength s - p))); temp _ip (offset_val (off + p) base);
           temp _nbBlocks (Vlong (Int64.repr nb)); temp _ipstart (offset_val off base);
           lvar _blockProperties (Tstruct ___gp_blockProperties_t noattr) v_blockProperties;
           lvar _zfh (Tstruct ___gp_ZSTD_FrameHeader noattr) v_zfh; gvars gv; temp _frameSizeInfo pf)
    SEP (zstd_globals gv; data_at Tsh t_fh (fh_val h) v_zfh; data_at sh (tarray tuchar N) c base;
         data_at shf t_fsi (Vlong Int64.zero, (Vlong Int64.zero, Vlong Int64.zero)) pf;
         data_at Tsh t_bp vbp v_blockProperties))%assert.
  { Exists hs 0 (default_val t_bp). entailer!.
    unfold rest0. rewrite skipn_sublist_Z by lia.
    destruct (blocks_size (length (sublist hs (Zlength s) s)) (sublist hs (Zlength s) s)) as [[k n]|]; auto.
    f_equal; f_equal; lia. }
  { Intros p nb vbp.
    set (cur := sublist p (Zlength s) s) in *.
    assert (Hcl: Zlength cur = Zlength s - p) by (unfold cur; rewrite Zlength_sublist; lia).
    assert (Hwc: win_ok sh N c (off + p) (Zlength cur) cur) by (rewrite Hcl; apply win_ok_skip; auto; lia).
    assert (Hbc: bytes_ok cur) by (unfold cur, bytes_ok in *; apply Forall_sublist; auto).
    sep_apply (data_at_data_at_ Tsh t_bp vbp v_blockProperties).
    rewrite <- Hcl.
    forward_call (gv, Tsh, v_blockProperties, sh, base, N, c, off + p, cur).
    Intros vr. destruct vr as [cb vb]. simpl fst in *. simpl snd in *.
    destruct (cblock_size cur) as [k|] eqn:Ec.
    2: { destruct H7 as [H7 _]. forward_call cb. rewrite H7.
      forward_if; [| match goal with Hx: Int.repr 1 = Int.zero |- _ =>
                       apply Int.one_not_zero in Hx; contradiction end].
      forward_call (shf, pf, Vlong Int64.zero, Vlong Int64.zero, Vlong Int64.zero, cb).
      forward. Exists (Vlong Int64.zero) cb ZSTD_CONTENTSIZE_ERROR.
      apply andp_right.
      { apply prop_right. split; auto. split; [unfold ZSTD_CONTENTSIZE_ERROR; rep_lia|].
        rewrite Hfsi, H5, (blocks_size_err1 cur Ec). auto. }
      sep_apply (data_at_data_at_ Tsh t_fh (fh_val h) v_zfh).
      sep_apply (data_at_data_at_ Tsh t_bp vb v_blockProperties). cancel. }
    destruct H7 as [-> ->].
    destruct (cblock_size_bound cur k Hbc Ec) as [Hk0 Hk1].
    forward_call k.
    replace (is_error_code k) with false by (unfold is_error_code; symmetry; apply Z.ltb_ge; lia).
    forward_if; [exfalso; match goal with Hx: Int.repr 0 <> _ |- _ => apply Hx; reflexivity end |].
    rewrite zg_bhs. Intros. forward.
    forward_if.
    { gather_SEP (data_at Ers tulong _ _) (zg_rest gv). rewrite <- zg_bhs.
      forward_call (shf, pf, Vlong Int64.zero, Vlong Int64.zero, Vlong Int64.zero, Int64.unsigned (Int64.repr (-72))).
      { entailer!. rewrite Int64.repr_unsigned. reflexivity. }
      forward. Exists (Vlong Int64.zero) (Int64.unsigned (Int64.repr (-72))) ZSTD_CONTENTSIZE_ERROR.
      apply andp_right.
      { apply prop_right. split; [rep_lia|]. split; [unfold ZSTD_CONTENTSIZE_ERROR; rep_lia|].
        match goal with Hx: Int64.ltu _ _ = true |- _ => apply ltu_inv64 in Hx;
          rewrite !Int64.unsigned_repr in Hx by rep_lia end.
        rewrite Hfsi, H5, (blocks_size_err2 cur k Ec) by lia. reflexivity. }
      sep_apply (data_at_data_at_ Tsh t_fh (fh_val h) v_zfh).
      sep_apply (data_at_data_at_ Tsh t_bp (bp_val (block_props_of cur)) v_blockProperties). cancel. }
    apply ltu_false_inv64 in H8.
    rewrite Int64.add_unsigned, (Int64.unsigned_repr 3), (Int64.unsigned_repr k), Int64.unsigned_repr,
      (Int64.unsigned_repr (3 + k)) in H8 by rep_lia.
    assert (Hl: bp_last (block_props_of cur) = 0 \/ bp_last (block_props_of cur) = 1)
      by (unfold block_props_of; simpl; pose proof (land1_rng (le_field cur 0 3)); lia).
    unfold bp_val. forward. forward. forward. forward. forward. forward.
    forward_if.
    { forward. Exists (p + (3 + k)) (nb + 1) (bp_val (block_props_of cur)). entailer!.
      2: { rewrite zg_bhs. cancel. }
      change (bp_last (block_props_of cur)) with (Z.land (le_field cur 0 3) 1) in Hl.
      split.
      { rewrite H5, (blocks_size_last cur k Hbc Ec) by (try lia; change (bp_last (block_props_of cur)) with (Z.land (le_field cur 0 3) 1); lia).
        f_equal; f_equal; lia. }
      split; [rewrite Hcl; f_equal; f_equal; lia | f_equal; lia]. }
    forward. Exists (p + (3 + k)) (nb + 1) (bp_val (block_props_of cur)). entailer!.
    2: { rewrite zg_bhs. cancel. }
    assert (Hl0: bp_last (block_props_of cur) <> 1).
    { intro E. change (bp_last (block_props_of cur)) with (Z.land (le_field cur 0 3) 1) in E.
      rewrite E in H9. apply Int.one_not_zero. auto. }
    split.
    { rewrite H5, (blocks_size_step cur k Hbc Ec ltac:(lia) Hl0).
      replace (sublist (3 + k) (Zlength cur) cur) with (sublist (p + (3 + k)) (Zlength s) s)
        by (unfold cur; rewrite Zlength_sublist by lia; rewrite sublist_sublist by lia; f_equal; lia).
      destruct (blocks_size (length (sublist (p + (3 + k)) (Zlength s) s)) (sublist (p + (3 + k)) (Zlength s) s))
        as [[k0 n]|]; auto.
      f_equal; f_equal; lia. }
    split; [rewrite Hcl; f_equal; f_equal; lia | f_equal; lia]. }
  Intros p nb vbp.
  unfold fh_val. forward. fold (fh_val h).
  set (q := if fh_checksumFlag h =? 1 then 4 else 0).
  forward_if (PROP (p + q <= Zlength s)
    LOCAL (temp _remainingSize (Vlong (Int64.repr (Zlength s - p))); temp _ip (offset_val (off + p + q) base);
           temp _nbBlocks (Vlong (Int64.repr nb)); temp _ipstart (offset_val off base);
           lvar _blockProperties (Tstruct ___gp_blockProperties_t noattr) v_blockProperties;
           lvar _zfh (Tstruct ___gp_ZSTD_FrameHeader noattr) v_zfh; gvars gv; temp _frameSizeInfo pf)
    SEP (zstd_globals gv; data_at Tsh t_fh (fh_val h) v_zfh; data_at sh (tarray tuchar N) c base;
         data_at shf t_fsi (Vlong Int64.zero, (Vlong Int64.zero, Vlong Int64.zero)) pf;
         data_at Tsh t_bp vbp v_blockProperties)).
  { assert (Hc1: fh_checksumFlag h = 1) by lia.
    forward_if.
    { forward_call (shf, pf, Vlong Int64.zero, Vlong Int64.zero, Vlong Int64.zero, Int64.unsigned (Int64.repr (-72))).
      { entailer!. rewrite Int64.repr_unsigned. reflexivity. }
      forward. Exists (Vlong Int64.zero) (Int64.unsigned (Int64.repr (-72))) ZSTD_CONTENTSIZE_ERROR.
      apply andp_right.
      { apply prop_right. split; [rep_lia|]. split; [unfold ZSTD_CONTENTSIZE_ERROR; rep_lia|].
        match goal with Hx: Int64.unsigned (Int64.repr _) < Int64.unsigned (Int64.repr _) |- _ =>
          rewrite !Int64.unsigned_repr in Hx by rep_lia end.
        rewrite Hfsi, H5, Hc1, Z.eqb_refl, (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
      sep_apply (data_at_data_at_ Tsh t_fh (fh_val h) v_zfh).
      sep_apply (data_at_data_at_ Tsh t_bp vbp v_blockProperties). cancel. }
    forward. entailer!.
    match goal with Hx: Int64.unsigned (Int64.repr _) >= Int64.unsigned (Int64.repr _) |- _ =>
      rewrite !Int64.unsigned_repr in Hx by rep_lia end.
    unfold q. rewrite Hc1, Z.eqb_refl. split; [lia | f_equal; lia]. }
  { forward. entailer!. unfold q.
    assert (Hc0: fh_checksumFlag h = 0).
    { destruct Hcf as [Hc|Hc]; auto. rewrite Hc in *. exfalso; apply Int.one_not_zero; auto. }
    rewrite Hc0. simpl. split; [lia | f_equal; lia]. }
  Intros.
  assert (Hq: q = 0 \/ q = 4) by (unfold q; destruct (_ =? 1); auto).
  assert (Hsub: force_val (sem_sub_pp tuchar (offset_val (off + p + q) base) (offset_val off base)) =
                Vlong (Int64.repr (p + q))).
  { destruct FC as [Hp _]. destruct base; try contradiction. unfold sem_sub_pp. simpl.
    rewrite if_true by auto. simpl. rewrite !(Ptrofs.add_commut i), Ptrofs.sub_shifted.
    unfold Vptrofs. simpl. rewrite Ptrofs.divs_one by (compute; congruence). unfold Ptrofs.sub, Ptrofs.to_int64.
    rewrite (Ptrofs.unsigned_repr (off + p + q)), (Ptrofs.unsigned_repr off), Ptrofs.unsigned_repr by rep_lia.
    f_equal. f_equal. lia. }
  forward. forward.
  { entailer!. destruct FC as [Hp _]. destruct base; try contradiction. simpl. unfold sameblock.
    destruct (peq b b); [auto | contradiction]. }
  rewrite Hsub.
  set (bnd := if fh_contentSize h =? ZSTD_CONTENTSIZE_UNKNOWN then (nb * fh_blockSizeMax h) mod 2 ^ 64
              else fh_contentSize h).
  unfold fh_val. forward.
  fif_temp _t'6 (Vlong (Int64.repr bnd)).
  { forward. forward. entailer!. unfold bnd.
    destruct (fh_contentSize h =? ZSTD_CONTENTSIZE_UNKNOWN) eqn:E; auto.
    apply Z.eqb_eq in E. exfalso. match goal with Hx: Int64.repr _ <> Int64.repr _ |- _ => apply Hx end.
    rewrite E. unfold ZSTD_CONTENTSIZE_UNKNOWN. apply Int64.eqm_samerepr. exists 1. reflexivity. }
  { forward. forward. entailer!. unfold bnd.
    match goal with Hx: Int64.eq _ _ = true |- _ => apply Int64.same_if_eq in Hx; rename Hx into Ef end.
    assert (E: fh_contentSize h = ZSTD_CONTENTSIZE_UNKNOWN).
    { apply (f_equal Int64.unsigned) in Ef. rewrite Int64.unsigned_repr in Ef by rep_lia. rewrite Ef. reflexivity. }
    rewrite E, Z.eqb_refl. rewrite Int.unsigned_repr by (unfold ZSTD_BLOCKSIZE_MAX in Hbsm; rep_lia).
    change (2 ^ 64) with Int64.modulus. rewrite <- Int64.unsigned_repr_eq, Int64.repr_unsigned. reflexivity. }
  forward. forward.
  Exists (Vlong (Int64.repr nb)) (p + q) bnd.
  apply andp_right.
  { apply prop_right. split; [rep_lia|]. split.
    { unfold bnd. destruct (fh_contentSize h =? ZSTD_CONTENTSIZE_UNKNOWN); [pose proof (Z.mod_pos_bound (nb * fh_blockSizeMax h) (2 ^ 64)); rep_lia | rep_lia]. }
    rewrite Hfsi, H5. unfold q in *. destruct Hcf as [Hc|Hc]; rewrite Hc in *; simpl in H6 |- *.
    - split; [lia | reflexivity].
    - rewrite (proj2 (Z.ltb_ge _ _)) by lia. split; [lia | reflexivity]. }
  sep_apply (data_at_data_at_ Tsh t_fh (fh_val h) v_zfh).
  sep_apply (data_at_data_at_ Tsh t_bp vbp v_blockProperties). cancel.
Qed.

Lemma bodies_H_fsi :
  semax_body Vprog H_G f_ZSTD_getcBlockSize ZSTD_getcBlockSize_spec /\
  semax_body Vprog H_G f_ZSTD_findFrameSizeInfo ZSTD_findFrameSizeInfo_spec.
Proof. split; [apply body_getcBlockSize | apply body_findFrameSizeInfo]. Qed.
