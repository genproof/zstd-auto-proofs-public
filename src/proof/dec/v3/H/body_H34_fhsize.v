(* Subtree H, API v3: the bodies with the format argument f in {0,1}
   (ZSTD_startingInputLength, ZSTD_frameHeaderSize_internal, ZSTD_findFrameCompressedSize_advanced) and
   ZSTD_getDecompressedSize, against H3_G (HSpecs3.v).  v2 proofs to generalise: src/proof/dec/H/body_H_alloc.v,
   body_H_fhsize.v.  Helper lemmas go above. *)
Require Import Zstd.proof.dec.H.HLemmas.
Require Import Zstd.proof.dec.v3.H.HLift34.
Local Open Scope logic.

(* ---------- ranges of the model (copied from v2's body_H_loops.v, prefixed h3_) ---------- *)

Lemma h3_le_value_rng: forall l, bytes_ok l -> 0 <= le_value l < 2 ^ (8 * Zlength l).
Proof.
  intros l H. induction H; cbn [le_value].
  - rewrite Zlength_nil. simpl. lia.
  - rewrite Zlength_cons.
    rewrite <- Z.add_1_r, Z.mul_add_distr_l, Z.pow_add_r by (pose proof (Zlength_nonneg l); lia).
    unfold is_byte in H. change (2^(8*1)) with 256. nia.
Qed.

Lemma h3_le_field_rng: forall s i k, bytes_ok s -> 0 <= k -> 0 <= le_field s i k < 2 ^ (8 * k).
Proof.
  intros s i k H Hk. unfold le_field, slice.
  assert (Hb: bytes_ok (firstn (Z.to_nat k) (skipn (Z.to_nat i) s))).
  { unfold bytes_ok in *. apply Forall_firstn. apply Forall_skipn. auto. }
  pose proof (h3_le_value_rng _ Hb).
  assert (Zlength (firstn (Z.to_nat k) (skipn (Z.to_nat i) s)) <= k).
  { rewrite Zlength_correct, firstn_length. lia. }
  split; [lia|]. eapply Z.lt_le_trans; [apply H0|]. apply Z.pow_le_mono_r; lia.
Qed.

Lemma h3_skipn_sublist_Z: forall (l: list Z) k, 0 <= k <= Zlength l ->
  skipn (Z.to_nat k) l = sublist k (Zlength l) l.
Proof.
  intros l k Hk. unfold sublist. rewrite firstn_all2; auto.
  rewrite Zlength_correct, Nat2Z.id. lia.
Qed.

Lemma h3_bytes_ok_skipn: forall n l, bytes_ok l -> bytes_ok (skipn n l).
Proof. intros. unfold bytes_ok in *. apply Forall_skipn. auto. Qed.

Lemma h3_cblock_size_nonneg: forall l c, bytes_ok l -> cblock_size l = Some c -> 3 <= Zlength l /\ 0 <= c.
Proof.
  intros l c Hb H. unfold cblock_size in H. unfold ZSTD_blockHeaderSize in H.
  destruct (Zlength l <? 3) eqn:E; [discriminate|]. apply Z.ltb_ge in E.
  destruct (bp_type (block_props_of l) =? 1); [inversion H; lia|].
  destruct (bp_type (block_props_of l) =? 3); [discriminate|]. inversion H; subst.
  split; auto. unfold block_props_of; simpl. apply Z.shiftr_nonneg.
  apply (h3_le_field_rng l 0 3 Hb); lia.
Qed.

Lemma h3_byte_at_rng: forall s i, bytes_ok s -> 0 <= byte_at s i < 256.
Proof.
  intros s i Hb. unfold byte_at. destruct (nth_in_or_default (Z.to_nat i) s 0) as [Hin|Heq].
  - unfold bytes_ok in Hb. rewrite Forall_forall in Hb. apply Hb in Hin. unfold is_byte in Hin. lia.
  - rewrite Heq. lia.
Qed.

Lemma h3_land1_rng: forall x, 0 <= Z.land x 1 <= 1.
Proof.
  intros. replace (Z.land x 1) with (Z.land x (Z.ones 1)) by reflexivity. rewrite Z.land_ones by lia.
  pose proof (Z.mod_pos_bound x (2^1) ltac:(lia)). change (2^1) with 2 in *. lia.
Qed.

Lemma h3_nth4_rng: forall n a b c d, 0 <= a <= 8 -> 0 <= b <= 8 -> 0 <= c <= 8 -> 0 <= d <= 8 ->
  0 <= nth n [a; b; c; d] 0 <= 8.
Proof. intros. destruct n as [|[|[|[|]]]]; simpl; try lia. destruct n; lia. Qed.

Lemma h3_fhd_header_size_rng: forall fhd, 5 <= fhd_header_size fhd <= 18.
Proof.
  intros. unfold fhd_header_size. pose proof (h3_land1_rng (Z.shiftr fhd 5)).
  assert (0 <= nth (Z.to_nat (Z.land fhd 3)) [0; 1; 2; 4] 0 <= 4).
  { destruct (Z.to_nat _) as [|[|[|[|]]]]; simpl; try lia. destruct n; lia. }
  assert (0 <= nth (Z.to_nat (Z.shiftr fhd 6)) [0; 2; 4; 8] 0 <= 8) by (apply h3_nth4_rng; lia).
  set (a := nth (Z.to_nat (Z.land fhd 3)) [0; 1; 2; 4] 0) in *. clearbody a.
  destruct (Z.shiftr fhd 6 =? 0) eqn:E6.
  - apply Z.eqb_eq in E6. rewrite E6. change (nth (Z.to_nat 0) [0; 2; 4; 8] 0) with 0.
    destruct (_ && _)%bool; lia.
  - rewrite andb_false_r. lia.
Qed.

Lemma h3_fcs_rng: forall s p (A B C D: bool), bytes_ok s ->
  0 <= (if A then (if B then byte_at s p else ZSTD_CONTENTSIZE_UNKNOWN)
        else (if C then le_field s p 2 + 256 else if D then le_field s p 4 else le_field s p 8))
    <= Int64.max_unsigned.
Proof.
  intros s p A B C D Hb.
  pose proof (h3_byte_at_rng s p Hb). pose proof (h3_le_field_rng s p 2 Hb ltac:(lia)).
  pose proof (h3_le_field_rng s p 4 Hb ltac:(lia)). pose proof (h3_le_field_rng s p 8 Hb ltac:(lia)).
  unfold ZSTD_CONTENTSIZE_UNKNOWN. destruct A, B, C, D; simpl in *; rep_lia.
Qed.

Lemma h3_gfh_more: forall s k, get_frame_header s = FH_more k -> 5 <= k <= 18.
Proof.
  intros s k H. unfold get_frame_header in H.
  destruct (Zlength s <? 5).
  { destruct (Zlength s >? 0); [destruct (_ && _)%bool|]; inversion H; lia. }
  destruct (negb _).
  { destruct (is_skippable_magic _); [|discriminate]. destruct (_ <? _); inversion H. unfold ZSTD_SKIPPABLEHEADERSIZE; lia. }
  cbv zeta in H. destruct (Zlength s <? fhd_header_size _).
  { inversion H. apply h3_fhd_header_size_rng. }
  destruct (negb _); [discriminate|]. destruct (_ && _)%bool; discriminate.
Qed.

Lemma h3_gfh_ok: forall s h, bytes_ok s -> get_frame_header s = FH_ok h ->
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
    pose proof (h3_le_field_rng s 4 4 Hb ltac:(lia)).
    unfold ZSTD_SKIPPABLEHEADERSIZE, ZSTD_BLOCKSIZE_MAX in *. rep_lia. }
  cbv zeta in H. destruct (Zlength s <? fhd_header_size _) eqn:Ef; [discriminate|].
  apply Z.ltb_ge in Ef.
  destruct (negb _); [discriminate|]. destruct (_ && _)%bool; [discriminate|].
  inversion H; subst; clear H. simpl.
  pose proof (h3_fhd_header_size_rng (byte_at s 4)).
  pose proof (h3_land1_rng (Z.shiftr (byte_at s 4) 2)).
  pose proof (h3_byte_at_rng s 5 Hb) as H5.
  match goal with |- context [if ?A then (if ?B then byte_at s ?p else ZSTD_CONTENTSIZE_UNKNOWN)
                             else (if ?C then le_field s ?p 2 + 256 else if ?D then le_field s ?p 4
                                   else le_field s ?p 8)] =>
    pose proof (h3_fcs_rng s p A B C D Hb) as Hfcs;
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

Lemma h3_fcs_val_rng: forall s, bytes_ok s -> 0 <= frame_content_size s <= Int64.max_unsigned.
Proof.
  intros s Hb. unfold frame_content_size.
  destruct (get_frame_header s) as [| |h] eqn:E; try (unfold ZSTD_CONTENTSIZE_ERROR; rep_lia).
  destruct (fh_frameType h =? 1); [rep_lia|]. apply (h3_gfh_ok s h Hb E).
Qed.


Lemma body_H3_startingInputLength :
  semax_body Vprog H3_G f_ZSTD_startingInputLength ZSTD_startingInputLength_spec3.
Proof.
  start_function.
  forward_if (temp _t'1 (Vint (Int.repr (starting_len (fmt_mg f))))).
  - forward. entailer!.
  - forward. entailer!. destruct H as [-> | ->]; [contradiction | reflexivity].
  - forward. forward. entailer!. destruct H as [-> | ->]; reflexivity.
Qed.

Lemma body_H3_getDecompressedSize :
  semax_body Vprog H3_G f_ZSTD_getDecompressedSize ZSTD_getDecompressedSize_aspec.
Proof.
  start_function.
  forward_call (gv, sh, src, s).
  assert (Hr: 0 <= frame_content_size s <= Int64.max_unsigned) by (apply h3_fcs_val_rng; apply H).
  unfold ZSTD_CONTENTSIZE_ERROR.
  forward_if (temp _t'2 (Vlong (Int64.repr (if frame_content_size s >=? ZSTD_CONTENTSIZE_ERROR then 0 else frame_content_size s)))).
  - forward. entailer!. rewrite (Int64.unsigned_repr (frame_content_size s)) in H0 by rep_lia.
    change (Int64.unsigned (Int64.repr (- (2)))) with (2 ^ 64 - 2) in H0. unfold ZSTD_CONTENTSIZE_ERROR.
    rewrite (proj2 (Z.geb_le _ _)) by lia. reflexivity.
  - forward. entailer!. rewrite (Int64.unsigned_repr (frame_content_size s)) in H0 by rep_lia.
    change (Int64.unsigned (Int64.repr (- (2)))) with (2 ^ 64 - 2) in H0. unfold ZSTD_CONTENTSIZE_ERROR.
    destruct (Z.geb_spec (frame_content_size s) (2 ^ 64 - 2)); [lia | reflexivity].
  - forward.
Qed.

Lemma body_H3_findFrameCompressedSize_advanced :
  semax_body Vprog H3_G f_ZSTD_findFrameCompressedSize_advanced ZSTD_findFrameCompressedSize_advanced_spec3.
Proof.
  start_function.
  forward_call (gv, Tsh, v_frameSizeInfo, sh, base, N, c, off, s, f).
  Intros vret. destruct vret as [[nb cs] db]; simpl fst in *; simpl snd in *.
  forward. forward.
  Exists cs. entailer!.
  rewrite frame_compressed_size_info_m. destruct (frame_size_info_m (fmt_mg f) s) as [[k b]|]; simpl; tauto.
Qed.


(* the do { ... } while (0) blocks of zstd's error macros *)
Ltac dw0_side :=
  first [ solve [entailer!] | solve [forward; entailer!]
        | solve [match goal with |- semax _ ?Pre _ _ => forward_if Pre; [congruence | ..]; try forward; entailer! end] ].
Ltac dw0 :=
  match goal with |- semax _ ?Pre (Ssequence (Sloop _ Sbreak) _) _ =>
    forward_loop Pre break: Pre; [dw0_side .. | idtac] end.

(* the two tables read by ZSTD_frameHeaderSize_internal, apart from the other globals *)
Definition zg_rest_fhs (gv: globals) : mpred := (
  data_at Ews tint g_debuglevel_val (gv _g_debuglevel) *
  data_at Ers (tarray tuint 32) DeBruijnBytePos_val (gv _DeBruijnBytePos) *
  data_at Ers (tarray tuint 32) DeBruijnClz_val (gv _DeBruijnClz) *
  data_at Ers tulong zeroFilled_val (gv _zeroFilled) *
  data_at Ers (Tstruct ___gp_ZSTD_customMem noattr) ZSTD_defaultCMem_val (gv _ZSTD_defaultCMem) *
  data_at Ers (tarray tuint 3) repStartValue_val (gv _repStartValue) *
  data_at Ers tulong ZSTD_blockHeaderSize_val (gv _ZSTD_blockHeaderSize) *
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

Lemma zg_fhs gv : zstd_globals gv =
  (data_at Ers (tarray tulong 4) ZSTD_did_fieldSize_val (gv _ZSTD_did_fieldSize) *
   data_at Ers (tarray tulong 4) ZSTD_fcs_fieldSize_val (gv _ZSTD_fcs_fieldSize) * zg_rest_fhs gv)%logic.
Proof. unfold zstd_globals, zg_rest_fhs. apply pred_ext; cancel. Qed.

Lemma did_at (dflt: Inhabitant val) d: 0 <= d < 4 ->
  @Znth val dflt d ZSTD_did_fieldSize_val = Vlong (Int64.repr (nth (Z.to_nat d) [0; 1; 2; 4] 0)).
Proof. intros Hd. assert (d = 0 \/ d = 1 \/ d = 2 \/ d = 3) as [-> | [-> | [-> | ->]]] by lia; reflexivity. Qed.

Lemma fcs_at (dflt: Inhabitant val) f: 0 <= f < 4 ->
  @Znth val dflt f ZSTD_fcs_fieldSize_val = Vlong (Int64.repr (nth (Z.to_nat f) [0; 2; 4; 8] 0)).
Proof. intros Hf. assert (f = 0 \/ f = 1 \/ f = 2 \/ f = 3) as [-> | [-> | [-> | ->]]] by lia; reflexivity. Qed.

(* the bit fields of the frame header descriptor, checked on every byte *)
Definition fhd_bits_ok (b: Z) : bool :=
  Int.eq (Int.zero_ext 8 (Int.repr b)) (Int.repr b) &&
  Int.eq (Int.shr (Int.repr b) (Int.repr 6)) (Int.repr (Z.shiftr b 6)) &&
  Int.eq (Int.and (Int.shr (Int.repr b) (Int.repr 5)) (Int.repr 1)) (Int.repr (Z.land (Z.shiftr b 5) 1)) &&
  Int.eq (Int.and (Int.repr b) (Int.repr 3)) (Int.repr (Z.land b 3)) &&
  (0 <=? Z.shiftr b 6) && (Z.shiftr b 6 <? 4) && (0 <=? Z.land b 3) && (Z.land b 3 <? 4) &&
  ((Z.land (Z.shiftr b 5) 1 =? 0) || (Z.land (Z.shiftr b 5) 1 =? 1)).

Lemma fhd_bits_all: forallb fhd_bits_ok (map Z.of_nat (seq 0 256)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma fhd_bits: forall b, 0 <= b < 256 ->
  Int.zero_ext 8 (Int.repr b) = Int.repr b /\
  Int.shr (Int.repr b) (Int.repr 6) = Int.repr (Z.shiftr b 6) /\
  Int.and (Int.shr (Int.repr b) (Int.repr 5)) (Int.repr 1) = Int.repr (Z.land (Z.shiftr b 5) 1) /\
  Int.and (Int.repr b) (Int.repr 3) = Int.repr (Z.land b 3) /\
  0 <= Z.shiftr b 6 < 4 /\ 0 <= Z.land b 3 < 4 /\
  (Z.land (Z.shiftr b 5) 1 = 0 \/ Z.land (Z.shiftr b 5) 1 = 1).
Proof.
  intros b Hb. assert (Hin: In b (map Z.of_nat (seq 0 256))).
  { apply in_map_iff. exists (Z.to_nat b). split; [lia|]. apply in_seq. lia. }
  pose proof (proj1 (forallb_forall _ _) fhd_bits_all b Hin) as H. unfold fhd_bits_ok in H.
  repeat match goal with Hx: andb _ _ = true |- _ => apply andb_prop in Hx; destruct Hx end.
  repeat match goal with
         | Hx: Int.eq _ _ = true |- _ => apply Int.same_if_eq in Hx
         | Hx: (_ <=? _) = true |- _ => apply Z.leb_le in Hx
         | Hx: (_ <? _) = true |- _ => apply Z.ltb_lt in Hx
         | Hx: orb _ _ = true |- _ => apply orb_true_iff in Hx; rewrite !Z.eqb_eq in Hx
         end.
  tauto.
Qed.

Lemma h3_fhs_m (mg: bool) (s: list Z) :
  frame_header_size_m mg s =
  if Zlength s <? starting_len mg then None
  else Some (fhd_header_size (byte_at s (starting_len mg - 1)) - 5 + starting_len mg).
Proof.
  destruct mg; unfold frame_header_size_m, frame_header_size, starting_len; simpl negb; cbv iota.
  - destruct (Zlength s <? 1); [reflexivity|]. f_equal. change (1 - 1) with 0. lia.
  - destruct (Zlength s <? ZSTD_FRAMEHEADERSIZE_PREFIX); [reflexivity|]. f_equal.
    unfold ZSTD_FRAMEHEADERSIZE_PREFIX. change (5 - 1) with 4. lia.
Qed.

Lemma body_H3_frameHeaderSize_internal :
  semax_body Vprog H3_G f_ZSTD_frameHeaderSize_internal ZSTD_frameHeaderSize_internal_spec3.
Proof.
  start_function.
  forward_call f.
  set (m := starting_len (fmt_mg f)).
  assert (Hm: m = 1 \/ m = 5) by (unfold m; destruct H0 as [-> | ->]; [right | left]; reflexivity).
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_loop (PROPx P (LOCALx Q (SEPx R)))
      continue: (PROPx ((m <= Zlength s) :: P) (LOCALx Q (SEPx R)))
      break: (PROPx ((m <= Zlength s) :: P) (LOCALx Q (SEPx R))) end.
  { entailer!. }
  { forward_if.
    { do 4 dw0.
      forward.
      destruct H as (Hr & Ho & Hn & HN & Hc & Hs & Hb & Hsub).
      Exists (Int64.modulus - 72). entailer!.
      apply Int64.ltu_inv in H1.
      rewrite !Int64.unsigned_repr in H1 by rep_lia.
      rewrite h3_fhs_m. fold m. rewrite (proj2 (Z.ltb_lt _ _)) by lia.
      split; [unfold dec_err, ZSTD_error_noForwardProgress_destFull, ZSTD_error_noForwardProgress_inputEmpty;
              split; [reflexivity | split; let E := fresh "E" in intro E; compute in E; discriminate]|]. f_equal. apply Int64.eqm_samerepr. exists (-1). reflexivity. }
    { forward. destruct H as (Hr & Ho & Hn & HN & Hc & Hs & Hb & Hsub).
      unfold Int64.ltu in H1.
      rewrite !Int64.unsigned_repr in H1 by rep_lia. if_tac in H1; [discriminate|]. entailer!. } }
  { forward. entailer!. }
  Intros. pose proof H as Hw. destruct H as (Hr & Ho & Hn & HN & Hc & Hs & Hb & Hsub).
  assert_PROP (field_compatible (tarray tuchar N) [] base) as Hfc by entailer!.
  rewrite (win_split sh N c off s base Hw Hfc). Intros.
  assert (0 <= m - 1 < Zlength s) by lia.
  forward.
  all: assert (Hb4: 0 <= Znth (m - 1) s < 256) by (apply (proj1 (Forall_Znth _ _) Hb); lia).
  1: { entailer!. rep_lia. }
  assert (Hbat: byte_at s (m - 1) = Znth (m - 1) s)
    by (unfold byte_at, Znth; destruct (Z_lt_dec (m - 1) 0); [lia | reflexivity]).
  forget (Znth (m - 1) s) as b.
  forward. forward. forward. forward.
  destruct (fhd_bits b Hb4) as (E1 & E2 & E3 & E4 & Rf & Rd & Rs).
  rewrite E1, E2, E3, E4.
  set (fi := Z.shiftr b 6) in *. set (d := Z.land b 3) in *. set (ss := Z.land (Z.shiftr b 5) 1) in *.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _t'2 (Vint (Int.repr (if andb (ss =? 1) (fi =? 0) then 1 else 0))) :: Q) (SEPx R))) end.
  { forward. entailer!. destruct Rs as [Hz|Hz]; [contradiction|]. rewrite Hz. simpl.
    destruct (Z.eqb_spec fi 0) as [Ef|Ef]; [rewrite Ef; reflexivity|].
    rewrite Int.eq_false; [reflexivity|]. intro Hf. apply Ef. apply repr_inj_unsigned in Hf; rep_lia. }
  { forward. entailer!. destruct Rs as [Hz|Hz]; rewrite Hz in *; [reflexivity|].
    apply repr_inj_unsigned in H2; rep_lia. }
  assert (Hfhd: fhd_header_size b = 5 + (1 - ss) + nth (Z.to_nat d) [0; 1; 2; 4] 0 + nth (Z.to_nat fi) [0; 2; 4; 8] 0
                  + (if andb (ss =? 1) (fi =? 0) then 1 else 0)) by reflexivity.
  clearbody fi d ss.
  rewrite zg_fhs. Intros.
  forward.
  1: { rewrite (did_at _ d Rd). entailer!. }
  rewrite (did_at _ d Rd).
  forward.
  1: { rewrite (fcs_at _ fi Rf). entailer!. }
  rewrite (fcs_at _ fi Rf).
  forward. Exists (fhd_header_size (byte_at s (m - 1)) - 5 + m).
  rewrite zg_fhs. rewrite (win_split sh _ c off s base Hw Hfc). entailer!.
  rewrite h3_fhs_m. fold m. rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite Hfhd.
  assert (d = 0 \/ d = 1 \/ d = 2 \/ d = 3) as [-> | [-> | [-> | ->]]] by lia;
  assert (fi = 0 \/ fi = 1 \/ fi = 2 \/ fi = 3) as [-> | [-> | [-> | ->]]] by lia;
  destruct Rs as [-> | ->]; destruct Hm as [-> | ->]; (split; [compute; split; congruence | split; reflexivity]).
Qed.

Lemma bodies_H3_fhsize :
  semax_body Vprog H3_G f_ZSTD_startingInputLength ZSTD_startingInputLength_spec3 /\
  semax_body Vprog H3_G f_ZSTD_frameHeaderSize_internal ZSTD_frameHeaderSize_internal_spec3 /\
  semax_body Vprog H3_G f_ZSTD_findFrameCompressedSize_advanced ZSTD_findFrameCompressedSize_advanced_spec3 /\
  semax_body Vprog H3_G f_ZSTD_getDecompressedSize ZSTD_getDecompressedSize_aspec.
Proof.
  split; [apply body_H3_startingInputLength|].
  split; [apply body_H3_frameHeaderSize_internal|].
  split; [apply body_H3_findFrameCompressedSize_advanced | apply body_H3_getDecompressedSize].
Qed.
