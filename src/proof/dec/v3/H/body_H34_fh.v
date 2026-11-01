(* Subtree H, API v3: ZSTD_getFrameHeader_advanced with the format
   f in {0,1} (DecIface3.ZSTD_getFrameHeader_advanced_spec3: Spec_api6.fh_post_m, model Params.get_frame_header_m),
   against H3_G (HSpecs3.v).  v2 proof to generalise: src/proof/dec/H/body_H_fh.v.  Helper lemmas go above. *)
Require Import Zstd.proof.dec.H.HLemmas.
Require Import Zstd.proof.dec.v3.H.HLift34.
Local Open Scope logic.

(* do { c } while (0), as Clight's Sloop c Sbreak: Q holds after it *)
Ltac reassoc := repeat match goal with
  |- semax _ _ (Ssequence (Ssequence _ _) _) _ => apply -> seq_assoc end.
Ltac once_loop Q := reassoc;
  match goal with |- semax _ ?P (Ssequence (Sloop _ Sbreak) _) _ =>
    forward_loop P break: Q; [apply andp_left2, derives_refl | | ] end.
Ltac once_body P :=
  first [ forward_if P;
          [ contradiction
          | forward; try (apply andp_left2, derives_refl)
          | forward; apply andp_left2, derives_refl ]
        | forward; apply andp_left2, derives_refl ].
Ltac once_skip := reassoc;
  match goal with |- semax _ ?P (Ssequence (Sloop _ Sbreak) _) _ =>
    forward_loop P break: P; [apply andp_left2, derives_refl | once_body P | ] end.

Lemma arr_valid_ptr: forall sh N (c: list val) base i, readable_share sh -> 0 <= i < N -> Zlength c = N ->
  data_at sh (tarray tuchar N) c base |-- valid_pointer (offset_val i base).
Proof.
  intros. assert_PROP (field_compatible (tarray tuchar N) [] base) by entailer!.
  rewrite (arr_split3 sh N i 1 c base) by (auto; lia).
  apply sepcon_valid_pointer1, sepcon_valid_pointer2, data_at_valid_ptr;
    [apply readable_nonidentity; auto | simpl; lia].
Qed.


Lemma fh_arr_split2: forall sh n k (l: list val) p, 0 <= k <= n -> Zlength l = n ->
  field_compatible (tarray tuchar n) [] p ->
  data_at sh (tarray tuchar n) l p =
  data_at sh (tarray tuchar k) (sublist 0 k l) p *
  data_at sh (tarray tuchar (n - k)) (sublist k n l) (offset_val k p).
Proof.
  intros. rewrite (split2_data_at_Tarray_tuchar sh n k) by lia.
  change (Tarray tuchar n noattr) with (tarray tuchar n). rewrite arr_field_address0 by (auto; lia).
  simpl sizeof. rewrite Z.mul_1_l. reflexivity.
Qed.

Lemma fh_le_bytes_len: forall k v, Zlength (le_bytes k v) = Z.of_nat k.
Proof. induction k; intros v; simpl; auto. rewrite Zlength_cons, IHk. lia. Qed.

Lemma fh_le_bytes_ok: forall k v, bytes_ok (le_bytes k v).
Proof.
  unfold bytes_ok. induction k; intros v; simpl; constructor; [| apply IHk].
  unfold is_byte. pose proof (Z.mod_pos_bound v 256 ltac:(lia)). lia.
Qed.

(* hbuf after MEM_writeLE32(hbuf, fill) and memcpy(hbuf, src, k) *)
Definition hb (s: list Z) (k fill: Z) : list Z := sublist 0 k s ++ sublist k 4 (le_bytes 4 fill).

Lemma hb_len: forall s k fill, 0 <= k <= 4 -> k <= Zlength s -> Zlength (hb s k fill) = 4.
Proof.
  intros. unfold hb. pose proof (fh_le_bytes_len 4 fill). simpl Z.of_nat in H1.
  rewrite Zlength_app, !Zlength_sublist by lia. lia.
Qed.

Lemma hb_ok: forall s k fill, bytes_ok s -> 0 <= k <= 4 -> k <= Zlength s -> bytes_ok (hb s k fill).
Proof.
  intros. unfold hb, bytes_ok in *. apply Forall_app; split; apply Forall_sublist; auto.
  apply fh_le_bytes_ok.
Qed.

Lemma hb_magic: forall s fill, 0 < Zlength s ->
  le_field (hb s (Z.min 4 (Zlength s)) fill) 0 4 = magic_prefix s fill.
Proof.
  intros. unfold le_field, slice, magic_prefix, hb.
  set (k := Z.min 4 (Zlength s)).
  assert (Hk: 0 <= k <= 4 /\ k <= Zlength s) by (subst k; lia).
  pose proof (fh_le_bytes_len 4 fill) as Hl. simpl Z.of_nat in Hl.
  assert (Hlen: length (sublist 0 k s ++ sublist k 4 (le_bytes 4 fill)) = 4%nat).
  { rewrite <- ZtoNat_Zlength, Zlength_app, !Zlength_sublist by lia. replace (k - 0 + (4 - k)) with 4 by lia.
    reflexivity. }
  change (skipn (Z.to_nat 0) ?l) with l. rewrite firstn_all2 by (rewrite Hlen; lia).
  f_equal.
Qed.

Lemma fh_le_value_range: forall l, bytes_ok l ->
  0 <= le_value l < 256 ^ Z.of_nat (length l).
Proof.
  intros l H. induction H as [|b l Hb Hl IH]; cbn [le_value length].
  - simpl; lia.
  - unfold is_byte in Hb. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. nia.
Qed.

Lemma fh_le_field_range: forall s i k, bytes_ok s -> 0 <= k ->
  0 <= le_field s i k < 2 ^ (8 * k).
Proof.
  intros s i k H Hk. unfold le_field, slice.
  assert (Hb: bytes_ok (firstn (Z.to_nat k) (skipn (Z.to_nat i) s))).
  { unfold bytes_ok in *. apply Forall_firstn, Forall_skipn; auto. }
  pose proof (fh_le_value_range _ Hb) as [A B]. split; auto.
  assert (Hl: (length (firstn (Z.to_nat k) (skipn (Z.to_nat i) s)) <= Z.to_nat k)%nat)
    by (rewrite firstn_length; lia).
  eapply Z.lt_le_trans; [exact B|]. rewrite Z.pow_mul_r by lia. change (2 ^ 8) with 256.
  apply Z.pow_le_mono_r; lia.
Qed.

Lemma hbuf_before_copy: forall fill k p, 0 <= k <= 4 -> field_compatible (tarray tuchar 4) [] p ->
  data_at Tsh (tarray tuchar 4) (zbytes (le_bytes 4 fill)) p |--
  data_at_ Tsh (tarray tuchar k) p *
  data_at Tsh (tarray tuchar (4 - k)) (sublist k 4 (zbytes (le_bytes 4 fill))) (offset_val k p).
Proof.
  intros. pose proof (fh_le_bytes_len 4 fill). simpl Z.of_nat in H1.
  rewrite (fh_arr_split2 Tsh 4 k) by (rewrite ?Zlength_map; auto; lia).
  cancel.
Qed.

Lemma hbuf_after_copy: forall s fill k p, 0 <= k <= 4 -> k <= Zlength s -> field_compatible (tarray tuchar 4) [] p ->
  data_at Tsh (tarray tuchar k) (sublist 0 k (zbytes s)) p *
  data_at Tsh (tarray tuchar (4 - k)) (sublist k 4 (zbytes (le_bytes 4 fill))) (offset_val k p) |--
  data_at Tsh (tarray tuchar (Zlength (hb s k fill))) (zbytes (hb s k fill)) p.
Proof.
  intros. rewrite hb_len by lia. pose proof (fh_le_bytes_len 4 fill). simpl Z.of_nat in H2.
  rewrite (fh_arr_split2 Tsh 4 k (zbytes (hb s k fill))) by (rewrite ?Zlength_map, ?hb_len; auto; lia).
  unfold hb. rewrite map_app.
  rewrite sublist0_app1 by (rewrite Zlength_map, Zlength_sublist; lia).
  rewrite sublist_app2 by (rewrite Zlength_map, Zlength_sublist; lia).
  rewrite Zlength_map, Zlength_sublist by lia.
  apply sepcon_derives; apply derives_refl'; f_equal; rewrite !sublist_map; f_equal; list_solve.
Qed.

Lemma mem_written_full4: forall (c: list val) v, Zlength c = 4 -> mem_written c 0 4 v = zbytes (le_bytes 4 v).
Proof.
  intros. unfold mem_written. rewrite H. replace (0 + 4) with 4 by lia. rewrite !sublist_nil, app_nil_l, app_nil_r. reflexivity.
Qed.

(* the first k bytes of the window, and the rest of the array *)
Definition win_rest (sh: share) (N: Z) (c: list val) (off k: Z) (base: val) : mpred :=
  data_at sh (tarray tuchar off) (sublist 0 off c) base *
  data_at sh (tarray tuchar (N - (off + k))) (sublist (off + k) N c) (offset_val (off + k) base).

Lemma win_take: forall sh N c off s k base, win_ok sh N c off (Zlength s) s -> 0 <= k <= Zlength s ->
  field_compatible (tarray tuchar N) [] base ->
  data_at sh (tarray tuchar N) c base =
  data_at sh (tarray tuchar k) (sublist 0 k (zbytes s)) (offset_val off base) * win_rest sh N c off k base.
Proof.
  intros sh N c off s k base [H1 [H2 [H3 [H4 [H5 [H6 [H7 H8]]]]]]] Hk Hfc.
  rewrite (arr_split3 sh N off k c base) by (auto; lia). unfold win_rest.
  replace (sublist off (off + k) c) with (sublist 0 k (zbytes s)).
  - apply pred_ext; cancel.
  - rewrite <- H8. rewrite sublist_sublist by lia. f_equal; lia.
Qed.

Lemma land_mask_range: forall m, 0 <= m < 2 ^ 32 -> 0 <= Z.land m ZSTD_MAGIC_SKIPPABLE_MASK < 2 ^ 32.
Proof.
  intros m Hm. unfold ZSTD_MAGIC_SKIPPABLE_MASK.
  assert (0 <= Z.land m 4294967280) by (apply Z.land_nonneg; lia). split; auto.
  destruct (Z.eq_dec (Z.land m 4294967280) 0) as [E|E]; [lia|].
  apply Z.log2_lt_pow2; [lia|].
  pose proof (Z.log2_land m 4294967280 ltac:(lia) ltac:(lia)).
  destruct (Z.eq_dec m 0) as [->|Hm0]; [rewrite Z.land_0_l in E; lia|].
  assert (Z.log2 m < 32) by (apply Z.log2_lt_pow2; lia). lia.
Qed.

Lemma and_mask_repr: forall m, 0 <= m < 2 ^ 32 ->
  Int.and (Int.repr m) (Int.repr (-16)) = Int.repr (Z.land m ZSTD_MAGIC_SKIPPABLE_MASK).
Proof.
  intros. unfold Int.and. rewrite (Int.unsigned_repr m) by rep_lia. reflexivity.
Qed.

Lemma gfh_small: forall s, 0 < Zlength s < 5 ->
  get_frame_header s =
  if andb (negb (magic_prefix s ZSTD_MAGICNUMBER =? ZSTD_MAGICNUMBER))
          (negb (is_skippable_magic (magic_prefix s ZSTD_MAGIC_SKIPPABLE_START)))
  then FH_err else FH_more 5.
Proof.
  intros. unfold get_frame_header.
  replace (Zlength s <? 5) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (Zlength s >? 0) with true by (symmetry; apply Z.gtb_lt; lia). reflexivity.
Qed.

Lemma repr_inj32: forall a b, 0 <= a < 2 ^ 32 -> 0 <= b < 2 ^ 32 -> Int.repr a = Int.repr b -> a = b.
Proof.
  intros. apply (f_equal Int.unsigned) in H1. rewrite !Int.unsigned_repr in H1 by rep_lia. auto.
Qed.

Definition fh0 : frame_header :=
  {| fh_contentSize := 0; fh_windowSize := 0; fh_blockSizeMax := 0; fh_frameType := 0;
     fh_headerSize := 0; fh_dictID := 0; fh_checksumFlag := 0 |}.

Lemma fh_eta: forall (x: reptype t_fh),
  x = (fst x, (fst (snd x), (fst (snd (snd x)), (fst (snd (snd (snd x))), (fst (snd (snd (snd (snd x)))), (fst (snd (snd (snd (snd (snd x))))), (fst (snd (snd (snd (snd (snd (snd x)))))), (fst (snd (snd (snd (snd (snd (snd (snd x))))))), snd (snd (snd (snd (snd (snd (snd (snd x))))))))))))))).
Proof. intros. destruct x as [a [b [c [d [e [f [g [h i]]]]]]]]. reflexivity. Qed.

Lemma zero_val_fh: zero_val t_fh = fh_val fh0.
Proof.
  rewrite (fh_eta (zero_val t_fh)). rewrite zero_val_eq; unfold fold_reptype; simpl.
  rewrite ?zero_val_tulong, ?zero_val_tuint, ?zero_val_tint. reflexivity.
Qed.

Lemma memset_fh: forall sh p, readable_share sh -> field_compatible t_fh [] p ->
  data_at sh (tarray tuchar (sizeof t_fh)) (Zrepeat (Vint (Int.repr 0)) (sizeof t_fh)) p |--
  data_at sh t_fh (fh_val fh0) p.
Proof.
  intros. sep_apply (memset_zero_data_at sh t_fh p H). rewrite zero_val_fh. apply derives_refl.
Qed.

Lemma win_take_all: forall sh N c off s base, win_ok sh N c off (Zlength s) s ->
  field_compatible (tarray tuchar N) [] base ->
  data_at sh (tarray tuchar N) c base =
  data_at sh (tarray tuchar (Zlength s)) (zbytes s) (offset_val off base) *
  win_rest sh N c off (Zlength s) base.
Proof.
  intros. pose proof (Zlength_nonneg s).
  rewrite (win_take sh N c off s (Zlength s) base) by (auto; lia).
  rewrite sublist_same by (rewrite ?Zlength_map; auto). reflexivity.
Qed.

Lemma win_read: forall sh p s i k, readable_share sh -> bytes_ok s -> 0 <= i -> 0 <= k -> i + k <= Zlength s ->
  mem_read_pre sh p s i k.
Proof.
  intros. unfold mem_read_pre. repeat split; auto. unfold bytes_ok in *. apply Forall_sublist; auto.
Qed.

(* the rest of get_frame_header for a Zstandard magic number and n >= 5 *)
Definition gfh_main (s: list Z) : fh_result :=
  let n := Zlength s in
  let fhd := byte_at s 4 in
  let fhsize := fhd_header_size fhd in
  if n <? fhsize then FH_more fhsize else
  let dictIDSizeCode := Z.land fhd 3 in
  let checksumFlag := Z.land (Z.shiftr fhd 2) 1 in
  let singleSegment := Z.land (Z.shiftr fhd 5) 1 in
  let fcsID := Z.shiftr fhd 6 in
  if negb (Z.land fhd 8 =? 0) then FH_err else
  let wlByte := byte_at s 5 in
  let windowLog := Z.shiftr wlByte 3 + ZSTD_WINDOWLOG_ABSOLUTEMIN in
  if andb (singleSegment =? 0) (windowLog >? ZSTD_WINDOWLOG_MAX) then FH_err else
  let pos := 5 + (1 - singleSegment) in
  let dsz := nth (Z.to_nat dictIDSizeCode) [0; 1; 2; 4] 0 in
  let dictID := le_field s pos dsz in
  let pos := pos + dsz in
  let fcs :=
    if fcsID =? 0 then (if singleSegment =? 1 then byte_at s pos else ZSTD_CONTENTSIZE_UNKNOWN)
    else if fcsID =? 1 then le_field s pos 2 + 256
    else if fcsID =? 2 then le_field s pos 4
    else le_field s pos 8 in
  let windowSize :=
    if singleSegment =? 1 then fcs
    else 2 ^ windowLog + Z.shiftr (2 ^ windowLog) 3 * Z.land wlByte 7 in
  FH_ok {| fh_contentSize := fcs; fh_windowSize := windowSize;
           fh_blockSizeMax := Z.min windowSize ZSTD_BLOCKSIZE_MAX;
           fh_frameType := 0; fh_headerSize := fhsize; fh_dictID := dictID;
           fh_checksumFlag := checksumFlag |}.

Lemma gfh_is_main: forall s, Zlength s >= 5 -> le_field s 0 4 = ZSTD_MAGICNUMBER ->
  get_frame_header s = gfh_main s.
Proof.
  intros. unfold get_frame_header. replace (Zlength s <? 5) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite H0, Z.eqb_refl. reflexivity.
Qed.

Lemma byte_at_range: forall s i, bytes_ok s -> 0 <= byte_at s i < 256.
Proof.
  intros. unfold byte_at. destruct (lt_dec (Z.to_nat i) (length s)).
  - pose proof (proj1 (Forall_forall _ _) H (nth (Z.to_nat i) s 0) (nth_In _ _ l)). unfold is_byte in H0. lia.
  - rewrite nth_overflow by lia. lia.
Qed.

Lemma land3: forall x, Z.land x 3 = x mod 4.
Proof. intros. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma land1: forall x, Z.land x 1 = x mod 2.
Proof. intros. change 1 with (Z.ones 1). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma land7: forall x, Z.land x 7 = x mod 8.
Proof. intros. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma fhd_header_size_range: forall b, 5 <= fhd_header_size b <= 18.
Proof.
  intros. unfold fhd_header_size. rewrite land3, land1.
  pose proof (Z.mod_pos_bound b 4 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.shiftr b 5) 2 ltac:(lia)).
  assert (Hd: nth (Z.to_nat (b mod 4)) [0; 1; 2; 4] 0 <= 4 /\ 0 <= nth (Z.to_nat (b mod 4)) [0; 1; 2; 4] 0)
    by (destruct (Z.to_nat (b mod 4)) as [|[|[|[|n]]]]; simpl; try lia; destruct n; simpl; lia).
  assert (Hf: nth (Z.to_nat (Z.shiftr b 6)) [0; 2; 4; 8] 0 <= 8 /\ 0 <= nth (Z.to_nat (Z.shiftr b 6)) [0; 2; 4; 8] 0)
    by (destruct (Z.to_nat (Z.shiftr b 6)) as [|[|[|[|n]]]]; simpl; try lia; destruct n; simpl; lia).
  destruct (Z.shiftr b 5 mod 2 =? 1) eqn:E; cbn [andb]; [apply Z.eqb_eq in E; destruct (_ =? 0); lia | apply Z.eqb_neq in E; lia].
Qed.

Lemma zero_ext8: forall b, 0 <= b < 256 -> Int.zero_ext 8 (Int.repr b) = Int.repr b.
Proof.
  intros. rewrite <- (Int.repr_unsigned (Int.zero_ext 8 (Int.repr b))).
  rewrite Int.zero_ext_mod by (split; [lia | reflexivity]). rewrite Int.unsigned_repr by rep_lia.
  rewrite Z.mod_small; [reflexivity | change (two_p 8) with 256; lia].
Qed.

Lemma shiftr_byte_range: forall b k, 0 <= b < 256 -> 0 <= k -> 0 <= Z.shiftr b k < 256.
Proof.
  intros. rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia]|].
  apply Z.le_lt_trans with b; [apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia|] | lia].
  assert (1 <= 2 ^ k) by (apply Z.pow_le_mono_r with (a := 2) in H0; [simpl in H0; lia | lia]). nia.
Qed.

Lemma shr_byte: forall b k, 0 <= b < 256 -> 0 <= k < 32 -> Int.shr (Int.repr b) (Int.repr k) = Int.repr (Z.shiftr b k).
Proof.
  intros. unfold Int.shr. rewrite Int.signed_repr by rep_lia. rewrite Int.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma and_small: forall a m, 0 <= a <= Int.max_unsigned -> 0 <= m <= Int.max_unsigned ->
  Int.and (Int.repr a) (Int.repr m) = Int.repr (Z.land a m).
Proof.
  intros. unfold Int.and. rewrite !Int.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma land_range: forall a m n, 0 <= n -> 0 <= a < 2 ^ n -> 0 <= m -> 0 <= Z.land a m < 2 ^ n.
Proof.
  intros a m n Hn Ha Hm.
  assert (E: Z.land a m = Z.land (Z.land a m) (Z.ones n)).
  { rewrite <- Z.land_assoc, (Z.land_comm m), Z.land_assoc, (Z.land_ones a n) by lia.
    rewrite Z.mod_small by lia. reflexivity. }
  rewrite E, Z.land_ones by lia. apply Z.mod_pos_bound, Z.pow_pos_nonneg; lia.
Qed.

Definition wsz (w: Z) : Z :=
  2 ^ (Z.shiftr w 3 + ZSTD_WINDOWLOG_ABSOLUTEMIN) +
  Z.shiftr (2 ^ (Z.shiftr w 3 + ZSTD_WINDOWLOG_ABSOLUTEMIN)) 3 * Z.land w 7.

Lemma wl_pow_range: forall w, 0 <= w < 256 -> Z.shiftr w 3 + 10 <= 31 ->
  2 ^ 10 <= 2 ^ (Z.shiftr w 3 + 10) <= 2 ^ 31.
Proof.
  intros. pose proof (shiftr_byte_range w 3 H ltac:(lia)).
  split; apply Z.pow_le_mono_r; lia.
Qed.

Lemma wsz_range: forall w, 0 <= w < 256 -> Z.shiftr w 3 + 10 <= 31 -> 0 <= wsz w <= 2 ^ 31 * 2.
Proof.
  intros. pose proof (wl_pow_range w H H0). unfold wsz, ZSTD_WINDOWLOG_ABSOLUTEMIN.
  rewrite land7. pose proof (Z.mod_pos_bound w 8 ltac:(lia)).
  set (X := 2 ^ (Z.shiftr w 3 + 10)) in *.
  rewrite (Z.shiftr_div_pow2 X 3) by lia. change (2 ^ 3) with 8.
  assert (0 <= X / 8 <= 2 ^ 31 / 8)
    by (split; [apply Z.div_pos; lia | apply Z.div_le_mono; lia]).
  change (2 ^ 31 / 8) with 268435456 in H3. change (2 ^ 31) with 2147483648 in *. nia.
Qed.

Lemma wsz_eq: forall w, 0 <= w < 256 -> Z.shiftr w 3 + 10 <= 31 ->
  Int64.add (Int64.shl (Int64.repr 1) (Int64.repr (Z.shiftr w 3 + 10)))
    (Int64.mul (Int64.shru (Int64.shl (Int64.repr 1) (Int64.repr (Z.shiftr w 3 + 10))) (Int64.repr 3))
       (Int64.repr (Int.signed (Int.repr (Z.land w 7))))) = Int64.repr (wsz w).
Proof.
  intros. pose proof (wl_pow_range w H H0). pose proof (shiftr_byte_range w 3 H ltac:(lia)).
  assert (Hl: 0 <= Z.land w 7 < 8) by (rewrite land7; apply Z.mod_pos_bound; lia).
  assert (Hs: Int64.shl (Int64.repr 1) (Int64.repr (Z.shiftr w 3 + 10)) = Int64.repr (2 ^ (Z.shiftr w 3 + 10))).
  { unfold Int64.shl. rewrite !Int64.unsigned_repr by rep_lia. rewrite Z.shiftl_1_l. reflexivity. }
  rewrite Hs. unfold Int64.shru. rewrite !Int64.unsigned_repr by (change (2 ^ 31) with 2147483648 in *; rep_lia).
  rewrite Int.signed_repr by rep_lia. rewrite mul64_repr, add64_repr. reflexivity.
Qed.

Lemma le_field_sub: forall bs i k, 0 <= i -> 0 <= k ->
  le_field bs i k = le_value (sublist i (i + k) bs).
Proof.
  intros. unfold le_field, slice, sublist. f_equal.
  rewrite skipn_firstn_comm. f_equal. lia.
Qed.

Lemma le_field1: forall s p, 0 <= p < Zlength s -> le_field s p 1 = Znth p s.
Proof.
  intros. rewrite le_field_sub by lia. rewrite sublist_len_1 by lia. simpl. lia.
Qed.

Ltac dec_err_c0 :=
  unfold dec_err, ZSTD_error_noForwardProgress_destFull, ZSTD_error_noForwardProgress_inputEmpty;
  split; [reflexivity | split; let E := fresh "E" in intro E; compute in E; discriminate].

(* API v3.1: an error is the exact code fh_err_code_m (the error, then the code by tac).
   API v3.4: and the struct is untouched or its dictID is 0 *)
Ltac dec_err_c := split; [dec_err_c0 | split;
  [ | first [ left; reflexivity | right; reflexivity | right; unfold fp_dictID; simpl; reflexivity ] ] ].

Lemma fh_err_code_small: forall s, Zlength s < 5 -> fh_err_code s = 2 ^ 64 - ZSTD_error_prefix_unknown.
Proof. intros s H. unfold fh_err_code. cbv zeta. rewrite (proj2 (Z.ltb_lt _ _) H). reflexivity. Qed.

Lemma fh_err_code_magic: forall s, Zlength s >= 5 -> le_field s 0 4 <> ZSTD_MAGICNUMBER ->
  fh_err_code s = 2 ^ 64 - ZSTD_error_prefix_unknown.
Proof.
  intros s H M. unfold fh_err_code. cbv zeta.
  rewrite (proj2 (Z.ltb_ge (Zlength s) 5) ltac:(lia)), (proj2 (Z.eqb_neq _ _) M). reflexivity.
Qed.

Lemma fh_err_code_fhd: forall s, Zlength s >= 5 -> le_field s 0 4 = ZSTD_MAGICNUMBER ->
  fh_err_code s = if negb (Z.land (byte_at s 4) 8 =? 0) then 2 ^ 64 - ZSTD_error_frameParameter_unsupported
                  else 2 ^ 64 - ZSTD_error_frameParameter_windowTooLarge.
Proof.
  intros s H M. unfold fh_err_code. cbv zeta.
  rewrite (proj2 (Z.ltb_ge (Zlength s) 5) ltac:(lia)), M, Z.eqb_refl. reflexivity.
Qed.

(* ---------- the magicless reading: the C reads s at i - d, the model reads fsrc at i ---------- *)
Definition fsh (mg: bool) : Z := if mg then 4 else 0.
Definition fsrc (mg: bool) (s: list Z) : list Z := if mg then magic_bytes ++ s else s.

Lemma magic_bytes_eq : magic_bytes = [40; 181; 47; 253].
Proof. reflexivity. Qed.

Lemma fsrc_len mg s : Zlength (fsrc mg s) = Zlength s + fsh mg.
Proof.
  destruct mg; unfold fsh, fsrc; [| lia]. rewrite magic_bytes_eq. rewrite Zlength_app. change (Zlength [40; 181; 47; 253]) with 4. lia.
Qed.

Lemma fsrc_ok mg s : bytes_ok s -> bytes_ok (fsrc mg s).
Proof.
  intros H. destruct mg; unfold fsrc; auto. unfold bytes_ok in *. apply Forall_app; split; auto.
  rewrite magic_bytes_eq. repeat constructor; unfold is_byte; lia.
Qed.

Lemma fsrc_byte mg s i : fsh mg <= i -> byte_at s (i - fsh mg) = byte_at (fsrc mg s) i.
Proof.
  intros H. destruct mg; unfold fsh, fsrc in *; [| f_equal; lia].
  unfold byte_at. rewrite magic_bytes_eq.
  replace (Z.to_nat i) with (4 + Z.to_nat (i - 4))%nat by lia. reflexivity.
Qed.

Lemma fsrc_le mg s i k : fsh mg <= i -> le_field s (i - fsh mg) k = le_field (fsrc mg s) i k.
Proof.
  intros H. destruct mg; unfold fsh, fsrc in *; [| f_equal; lia].
  unfold le_field, slice. rewrite magic_bytes_eq.
  replace (Z.to_nat i) with (4 + Z.to_nat (i - 4))%nat by lia. reflexivity.
Qed.

Lemma fsrc_magic s : le_field (magic_bytes ++ s) 0 4 = ZSTD_MAGICNUMBER.
Proof. rewrite magic_bytes_eq. reflexivity. Qed.

(* API v3.1: the error code of a header with the magic number (fh_err_code_m) *)
Lemma fh_code_fsrc mg s : Zlength s >= starting_len mg -> (mg = false -> le_field s 0 4 = ZSTD_MAGICNUMBER) ->
  fh_err_code_m mg s = if negb (Z.land (byte_at (fsrc mg s) 4) 8 =? 0)
                       then 2 ^ 64 - ZSTD_error_frameParameter_unsupported
                       else 2 ^ 64 - ZSTD_error_frameParameter_windowTooLarge.
Proof.
  intros Hn Hm. unfold starting_len, ZSTD_FRAMEHEADERSIZE_PREFIX in Hn.
  destruct mg; unfold fh_err_code_m, fsrc; apply fh_err_code_fhd.
  - rewrite Zlength_app. rewrite magic_bytes_eq. change (Zlength [40; 181; 47; 253]) with 4. lia.
  - apply fsrc_magic.
  - lia.
  - auto.
Qed.

Definition fh_hsub (d: Z) (h: frame_header) : frame_header :=
  {| fh_contentSize := fh_contentSize h; fh_windowSize := fh_windowSize h; fh_blockSizeMax := fh_blockSizeMax h;
     fh_frameType := fh_frameType h; fh_headerSize := fh_headerSize h - d; fh_dictID := fh_dictID h;
     fh_checksumFlag := fh_checksumFlag h |}.

Definition fh_shift (d: Z) (r: fh_result) : fh_result :=
  match r with FH_ok h => FH_ok (fh_hsub d h) | FH_more k => FH_more (k - d) | FH_err => FH_err end.

Lemma gfh_m_main mg s : Zlength s >= starting_len mg -> (mg = false -> le_field s 0 4 = ZSTD_MAGICNUMBER) ->
  get_frame_header_m mg s = fh_shift (fsh mg) (gfh_main (fsrc mg s)).
Proof.
  intros Hn Hm. unfold starting_len, ZSTD_FRAMEHEADERSIZE_PREFIX in Hn.
  destruct mg; unfold get_frame_header_m; simpl negb; cbv iota beta.
  - replace (Zlength s <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite gfh_is_main.
    + unfold fsh, fsrc. destruct (gfh_main _); reflexivity.
    + rewrite Zlength_app. rewrite magic_bytes_eq. change (Zlength [40; 181; 47; 253]) with 4. lia.
    + apply fsrc_magic.
  - rewrite gfh_is_main by (auto; lia). unfold fsh, fsrc.
    destruct (gfh_main s); simpl; f_equal; try lia.
    all: try reflexivity. destruct h; unfold fh_hsub; simpl; f_equal; lia.
Qed.

Lemma fhs_m mg s : Zlength s >= starting_len mg ->
  frame_header_size_m mg s = Some (fhd_header_size (byte_at (fsrc mg s) 4) - fsh mg).
Proof.
  intros Hn. unfold starting_len, ZSTD_FRAMEHEADERSIZE_PREFIX in Hn.
  destruct mg; unfold frame_header_size_m; simpl negb; cbv iota beta.
  - replace (Zlength s <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite <- fsrc_byte by (simpl; lia). reflexivity.
  - unfold frame_header_size. replace (Zlength s <? ZSTD_FRAMEHEADERSIZE_PREFIX) with false
      by (symmetry; apply Z.ltb_ge; unfold ZSTD_FRAMEHEADERSIZE_PREFIX; lia).
    simpl. f_equal. lia.
Qed.

Lemma fh_post_m0 s r v0 v : fh_post_m (fmt_mg 0) s r v0 v = fh_post s r v0 v.
Proof. reflexivity. Qed.

Lemma Znth_byte_at s i : 0 <= i -> Znth i s = byte_at s i.
Proof. intros. unfold Znth, byte_at. rewrite if_false by lia. reflexivity. Qed.

Lemma body_H3_fh :
  semax_body Vprog H3_G f_ZSTD_getFrameHeader_advanced ZSTD_getFrameHeader_advanced_spec3.
Proof.
  start_function.
  rename H0 into Hf.
  pose proof H as Hw.
  destruct H as [Hsh [Hoff [HN [HN32 [Hc [_ [Hb Hsub]]]]]]].
  assert (Hs0: 0 <= Zlength s) by apply Zlength_nonneg.
  assert_PROP (field_compatible (tarray tuchar N) [] base) as Hfc by entailer!.
  assert (Hml: starting_len (fmt_mg f) = 5 - fsh (fmt_mg f)) by (destruct (fmt_mg f); reflexivity).
  assert (Hd: fsh (fmt_mg f) = 0 \/ fsh (fmt_mg f) = 4) by (destruct (fmt_mg f); auto).
  forward.
  forward_call f.
  rewrite Hml.
  once_skip.
  forward_if (PROP () LOCAL (temp _minInputSize (Vlong (Int64.repr (5 - fsh (fmt_mg f))));
   temp _ip (offset_val off base); lvar _hbuf (tarray tuchar 4) v_hbuf;
   gvars gv; temp _zfhPtr zfh; temp _src (offset_val off base);
   temp _srcSize (Vlong (Int64.repr (Zlength s)));
   temp _format (Vint (Int.repr f)))
   SEP (data_at_ Tsh (tarray tuchar 4) v_hbuf; zstd_globals gv;
   data_at shz t_fh v0 zfh; data_at sh (tarray tuchar N) c base)).
  { match goal with |- semax _ ?P _ _ => forward_loop P break: P end; [apply andp_left2, derives_refl | ].
    rewrite !Int64.unsigned_repr in H by rep_lia.
    forward_if.
    2: (assert (isptr base) by auto with field_compatible; destruct base; try contradiction; discriminate).
    1: (apply denote_tc_test_eq_split; [| apply valid_pointer_zero64; reflexivity]).
    1: (apply sepcon_valid_pointer2, arr_valid_ptr; auto; lia).
    forward. entailer!. }
  { forward. entailer!. }
  forward_if (PROP (Zlength s >= 5 - fsh (fmt_mg f)) LOCAL (temp _minInputSize (Vlong (Int64.repr (5 - fsh (fmt_mg f))));
   temp _ip (offset_val off base); lvar _hbuf (tarray tuchar 4) v_hbuf;
   gvars gv; temp _zfhPtr zfh; temp _src (offset_val off base);
   temp _srcSize (Vlong (Int64.repr (Zlength s)));
   temp _format (Vint (Int.repr f)))
   SEP (data_at_ Tsh (tarray tuchar 4) v_hbuf; zstd_globals gv;
   data_at shz t_fh v0 zfh; data_at sh (tarray tuchar N) c base)).
  {
    destruct Hf as [Hf | Hf]; subst f.
    2: { change (fsh (fmt_mg 1)) with 4 in *. change (5 - 4) with 1 in *.
         assert (Hs00: Zlength s = 0) by lia.
         forward_if (PROP () LOCAL (temp _t'5 (Vint Int.zero); temp _minInputSize (Vlong (Int64.repr 1));
           temp _ip (offset_val off base); lvar _hbuf (tarray tuchar 4) v_hbuf;
           gvars gv; temp _zfhPtr zfh; temp _src (offset_val off base);
           temp _srcSize (Vlong (Int64.repr (Zlength s))); temp _format (Vint (Int.repr 1)))
           SEP (data_at_ Tsh (tarray tuchar 4) v_hbuf; zstd_globals gv;
           data_at shz t_fh v0 zfh; data_at sh (tarray tuchar N) c base)).
         { rewrite Hs00 in H0. inversion H0. }
         { forward. entailer!. }
         forward_if (PROP () LOCAL (temp _minInputSize (Vlong (Int64.repr 1)); lvar _hbuf (tarray tuchar 4) v_hbuf; gvars gv)
           SEP (data_at_ Tsh (tarray tuchar 4) v_hbuf; zstd_globals gv;
           data_at shz t_fh v0 zfh; data_at sh (tarray tuchar N) c base)).
         { contradiction. }
         { forward. entailer!. }
         forward. Exists 1 v0. entailer!.
         unfold fh_post_m, get_frame_header_m. change (fmt_mg 1) with true. cbv iota beta. simpl negb.
         rewrite Hs00. split; reflexivity. }
    change (5 - fsh (fmt_mg 0)) with ZSTD_FRAMEHEADERSIZE_PREFIX in *.
    unfold ZSTD_FRAMEHEADERSIZE_PREFIX in H.
    forward_if (PROP () LOCAL (temp _t'5 (Vint (if Zlength s =? 0 then Int.zero else Int.one)); temp _minInputSize (Vlong (Int64.repr ZSTD_FRAMEHEADERSIZE_PREFIX));
   temp _ip (offset_val off base); lvar _hbuf (tarray tuchar 4) v_hbuf;
   gvars gv; temp _zfhPtr zfh; temp _src (offset_val off base);
   temp _srcSize (Vlong (Int64.repr (Zlength s)));
   temp _format (Vint (Int.repr 0)))
      SEP (data_at_ Tsh (tarray tuchar 4) v_hbuf; zstd_globals gv;
   data_at shz t_fh v0 zfh; data_at sh (tarray tuchar N) c base)).
    { forward. entailer!. rewrite !Int64.unsigned_repr in H0 by rep_lia.
      destruct (Zlength s =? 0) eqn:E; [apply Z.eqb_eq in E; lia | reflexivity]. }
    { forward. entailer!. rewrite !Int64.unsigned_repr in H0 by rep_lia.
      replace (Zlength s =? 0) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity. }
    forward_if (PROP (get_frame_header s = FH_more 5) LOCAL (temp _minInputSize (Vlong (Int64.repr ZSTD_FRAMEHEADERSIZE_PREFIX));
   temp _ip (offset_val off base); lvar _hbuf (tarray tuchar 4) v_hbuf;
   gvars gv; temp _zfhPtr zfh; temp _src (offset_val off base);
   temp _srcSize (Vlong (Int64.repr (Zlength s)));
   temp _format (Vint (Int.repr 0))) SEP (data_at_ Tsh (tarray tuchar 4) v_hbuf; zstd_globals gv;
   data_at shz t_fh v0 zfh; data_at sh (tarray tuchar N) c base)).
    { assert (Hn: 0 < Zlength s)
        by (destruct (Zlength s =? 0) eqn:E; [exfalso; apply H0; reflexivity | apply Z.eqb_neq in E; lia]).
      forward_if (PROP () LOCAL (temp _t'2 (Vlong (Int64.repr (Z.min 4 (Zlength s)))); temp _minInputSize (Vlong (Int64.repr ZSTD_FRAMEHEADERSIZE_PREFIX));
   temp _ip (offset_val off base); lvar _hbuf (tarray tuchar 4) v_hbuf;
   gvars gv; temp _zfhPtr zfh; temp _src (offset_val off base);
   temp _srcSize (Vlong (Int64.repr (Zlength s)));
   temp _format (Vint (Int.repr 0)))
        SEP (data_at_ Tsh (tarray tuchar 4) v_hbuf; zstd_globals gv;
   data_at shz t_fh v0 zfh; data_at sh (tarray tuchar N) c base)).
      { forward. entailer!. rewrite !Int64.unsigned_repr in H1 by rep_lia. do 2 f_equal. lia. }
      { forward. entailer!. rewrite !Int64.unsigned_repr in H1 by rep_lia. do 2 f_equal. lia. }
      forward.
      assert (Hm: Int.repr (-47205080) = Int.repr ZSTD_MAGICNUMBER)
        by (apply Int.eqm_samerepr; exists (-1); reflexivity).
      set (k := Z.min 4 (Zlength s)).
      assert (Hk: 0 <= k <= 4 /\ k <= Zlength s) by (subst k; lia).
      forward_call (Tsh, v_hbuf, default_val (tarray tuchar 4), 0, ZSTD_MAGICNUMBER).
      1: (entailer!; simpl; rewrite Hm; destruct v_hbuf; try contradiction; reflexivity).
      1: (unfold mem_write_pre, ZSTD_MAGICNUMBER; change (Zlength (default_val (tarray tuchar 4))) with 4;
          repeat split; try apply writable_share_top; lia).
      rewrite mem_written_full4 by reflexivity. change (Zlength (default_val (tarray tuchar 4))) with 4.
      assert_PROP (field_compatible (tarray tuchar 4) [] v_hbuf) as Hfh by entailer!.
      sep_apply (hbuf_before_copy ZSTD_MAGICNUMBER k v_hbuf ltac:(lia) Hfh).
      rewrite (win_take sh N c off s k base) by (auto; lia). Intros.
      forward_call (sh, Tsh, offset_val off base, v_hbuf,
        existT (fun t => reptype t) (tarray tuchar k) (sublist 0 k (zbytes s))).
      1: (cbn [projT1 projT2]; split; [simpl; rep_lia |];
          rewrite sublist_map; apply memcpy_ok_zbytes;
          [list_solve | unfold bytes_ok in *; apply Forall_sublist; assumption]).
      cbn [projT1 projT2].
      sep_apply (hbuf_after_copy s ZSTD_MAGICNUMBER k v_hbuf ltac:(lia) ltac:(lia) Hfh).
      sep_apply (derives_refl' _ _ (eq_sym (win_take sh N c off s k base Hw ltac:(lia) Hfc))).
      forward_call (Tsh, v_hbuf, hb s k ZSTD_MAGICNUMBER, 0).
      1: (unfold mem_read_pre; rewrite hb_len by lia; repeat split; try lia; auto;
          unfold bytes_ok; apply Forall_sublist, hb_ok; auto; lia).
      pose proof (hb_magic s ZSTD_MAGICNUMBER Hn) as Hmp1. fold k in Hmp1. rewrite Hmp1.
      assert (Hr1: 0 <= magic_prefix s ZSTD_MAGICNUMBER < 2 ^ 32)
        by (rewrite <- Hmp1; apply (fh_le_field_range _ 0 4); [apply hb_ok; auto; lia | lia]).
      rewrite hb_len by lia.
      sep_apply (data_at_data_at_ Tsh (tarray tuchar 4) (zbytes (hb s k ZSTD_MAGICNUMBER)) v_hbuf).
      forward_if.
      { assert (Hne: magic_prefix s ZSTD_MAGICNUMBER <> ZSTD_MAGICNUMBER)
          by (intro E; apply H1; rewrite Hm, E; reflexivity).
        forward_call (Tsh, v_hbuf, default_val (tarray tuchar 4), 0, ZSTD_MAGIC_SKIPPABLE_START).
        1: (unfold mem_write_pre, ZSTD_MAGIC_SKIPPABLE_START;
            change (Zlength (default_val (tarray tuchar 4))) with 4;
            repeat split; try apply writable_share_top; lia).
        rewrite mem_written_full4 by reflexivity. change (Zlength (default_val (tarray tuchar 4))) with 4.
        sep_apply (hbuf_before_copy ZSTD_MAGIC_SKIPPABLE_START k v_hbuf ltac:(lia) Hfh).
        rewrite (win_take sh N c off s k base) by (auto; lia). Intros.
        forward_call (sh, Tsh, offset_val off base, v_hbuf,
          existT (fun t => reptype t) (tarray tuchar k) (sublist 0 k (zbytes s))).
        1: (cbn [projT1 projT2]; split; [simpl; rep_lia |];
            rewrite sublist_map; apply memcpy_ok_zbytes;
            [list_solve | unfold bytes_ok in *; apply Forall_sublist; assumption]).
        cbn [projT1 projT2].
        sep_apply (hbuf_after_copy s ZSTD_MAGIC_SKIPPABLE_START k v_hbuf ltac:(lia) ltac:(lia) Hfh).
        sep_apply (derives_refl' _ _ (eq_sym (win_take sh N c off s k base Hw ltac:(lia) Hfc))).
        forward_call (Tsh, v_hbuf, hb s k ZSTD_MAGIC_SKIPPABLE_START, 0).
        1: (unfold mem_read_pre; rewrite hb_len by lia; repeat split; try lia; auto;
            unfold bytes_ok; apply Forall_sublist, hb_ok; auto; lia).
        pose proof (hb_magic s ZSTD_MAGIC_SKIPPABLE_START Hn) as Hmp2. fold k in Hmp2. rewrite Hmp2.
        assert (Hr2: 0 <= magic_prefix s ZSTD_MAGIC_SKIPPABLE_START < 2 ^ 32)
          by (rewrite <- Hmp2; apply (fh_le_field_range _ 0 4); [apply hb_ok; auto; lia | lia]).
        rewrite hb_len by lia.
        sep_apply (data_at_data_at_ Tsh (tarray tuchar 4) (zbytes (hb s k ZSTD_MAGIC_SKIPPABLE_START)) v_hbuf).
        pose proof (land_mask_range _ Hr2) as Hr3.
        forward_if.
        { rewrite and_mask_repr in H2 by auto.
          match goal with |- semax _ ?P _ _ => forward_loop P break: (PROP (False) LOCAL () SEP ()) end;
            [apply andp_left2, derives_refl | | Intros; contradiction].
          once_skip. once_skip. once_skip. once_skip. forward.
          Exists (Int64.unsigned (Int64.repr (-10))) v0. rewrite Int64.repr_unsigned. entailer!.
          rewrite fh_post_m0; unfold fh_post. rewrite gfh_small by lia.
          replace (magic_prefix s ZSTD_MAGICNUMBER =? ZSTD_MAGICNUMBER) with false
            by (symmetry; apply Z.eqb_neq; auto).
          unfold is_skippable_magic.
          replace (Z.land (magic_prefix s ZSTD_MAGIC_SKIPPABLE_START) ZSTD_MAGIC_SKIPPABLE_MASK =?
                   ZSTD_MAGIC_SKIPPABLE_START) with false
            by (symmetry; apply Z.eqb_neq; intro E; apply H2; rewrite E; reflexivity).
          dec_err_c. unfold fh_err_code_m; rewrite fh_err_code_small by lia; reflexivity. }
        { rewrite and_mask_repr in H2 by auto.
          forward. entailer!. rewrite gfh_small by lia.
          apply repr_inj32 in H2; [| auto | unfold ZSTD_MAGIC_SKIPPABLE_START; lia].
          unfold is_skippable_magic. rewrite H2, Z.eqb_refl. rewrite andb_false_r. reflexivity. } }
      { forward. entailer!. rewrite gfh_small by lia. rewrite Hm in H1.
        apply repr_inj32 in H1; [| auto | unfold ZSTD_MAGICNUMBER; lia].
        rewrite H1, Z.eqb_refl. reflexivity. } }
    { forward. entailer!. destruct (Zlength s =? 0) eqn:E; [| discriminate].
      apply Z.eqb_eq in E. apply Zlength_nil_inv in E. subst s. reflexivity. }
    forward. Exists 5 v0. entailer!. rewrite fh_post_m0; unfold fh_post. rewrite H0. split; [reflexivity|].
    destruct (Zlength s <? 5) eqn:E5; [reflexivity | apply Z.ltb_ge in E5; lia]. }
  { forward. entailer!. }
  Intros. assert (H5f: (Zlength s <? starting_len (fmt_mg f)) = false) by (apply Z.ltb_ge; lia).
  sep_apply (data_at_data_at_ shz t_fh v0 zfh). sep_apply (data_at__memory_block shz t_fh zfh). Intros.
  forward_call (shz, zfh, 0, sizeof t_fh).
  match goal with Hx: field_compatible t_fh [] zfh |- _ => sep_apply (memset_fh shz zfh ltac:(auto) Hx) end.
  rewrite (win_take_all sh N c off s base Hw Hfc).
  Intros.
  pose proof (fh_le_field_range s 0 4 Hb ltac:(lia)) as Hm0. change (2 ^ (8 * 4)) with (2 ^ 32) in Hm0.
  assert (Hm: Int.repr (-47205080) = Int.repr ZSTD_MAGICNUMBER)
    by (apply Int.eqm_samerepr; exists (-1); reflexivity).
  forward_if (PROP () LOCAL (temp _t'9 (Vint (if f =? 1 then Int.zero else if le_field s 0 4 =? ZSTD_MAGICNUMBER then Int.zero else Int.one)); temp _minInputSize (Vlong (Int64.repr (5 - fsh (fmt_mg f))));
     temp _ip (offset_val off base); lvar _hbuf (tarray tuchar 4) v_hbuf;
     gvars gv; temp _zfhPtr zfh; temp _src (offset_val off base);
     temp _srcSize (Vlong (Int64.repr (Zlength s))); temp _format (Vint (Int.repr f)))
    SEP (data_at shz t_fh (fh_val fh0) zfh; data_at_ Tsh (tarray tuchar 4) v_hbuf; zstd_globals gv;
     data_at sh (tarray tuchar (Zlength s)) (zbytes s) (offset_val off base);
     win_rest sh N c off (Zlength s) base)).
  { assert (Hf0: f = 0) by (destruct Hf as [-> | ->]; [reflexivity | contradiction]). subst f.
    change (fsh (fmt_mg 0)) with 0 in *.
    forward_call (sh, offset_val off base, s, 0).
    1: (apply win_read; auto; lia).
    forward. entailer!. rewrite Hm.
    destruct (Z.eqb_spec (le_field s 0 4) ZSTD_MAGICNUMBER) as [E|E].
    - rewrite E, Int.eq_true. reflexivity.
    - rewrite Int.eq_false; [reflexivity|]. intro X. apply repr_inj32 in X; auto.
      unfold ZSTD_MAGICNUMBER; lia. }
  { forward. entailer!. }
  forward_if (PROP (f = 1 \/ le_field s 0 4 = ZSTD_MAGICNUMBER) LOCAL (temp _minInputSize (Vlong (Int64.repr (5 - fsh (fmt_mg f))));
     temp _ip (offset_val off base); lvar _hbuf (tarray tuchar 4) v_hbuf;
     gvars gv; temp _zfhPtr zfh; temp _src (offset_val off base);
     temp _srcSize (Vlong (Int64.repr (Zlength s))); temp _format (Vint (Int.repr f)))
    SEP (data_at shz t_fh (fh_val fh0) zfh; data_at_ Tsh (tarray tuchar 4) v_hbuf; zstd_globals gv;
     data_at sh (tarray tuchar (Zlength s)) (zbytes s) (offset_val off base);
     win_rest sh N c off (Zlength s) base)).
  { destruct Hf as [Hf | Hf]; subst f.
    2: (exfalso; match goal with Hx: _ <> _ |- _ => apply Hx; reflexivity end).
    change (5 - fsh (fmt_mg 0)) with ZSTD_FRAMEHEADERSIZE_PREFIX in *.
    match goal with Hx: _ <> _ |- _ => rename Hx into H1 end.
    change (0 =? 1) with false in H1. cbv iota in H1.
    clear H5f. assert (H5f: (Zlength s <? 5) = false) by (apply Z.ltb_ge; unfold ZSTD_FRAMEHEADERSIZE_PREFIX in *; lia).
    assert (Hgfh: get_frame_header s =
      (let magic := le_field s 0 4 in
       if negb (magic =? ZSTD_MAGICNUMBER) then
         (if is_skippable_magic magic then
            (if Zlength s <? ZSTD_SKIPPABLEHEADERSIZE then FH_more ZSTD_SKIPPABLEHEADERSIZE
             else FH_ok {| fh_contentSize := le_field s 4 4; fh_windowSize := 0; fh_blockSizeMax := 0;
                           fh_frameType := 1; fh_headerSize := ZSTD_SKIPPABLEHEADERSIZE;
                           fh_dictID := magic - ZSTD_MAGIC_SKIPPABLE_START; fh_checksumFlag := 0 |})
          else FH_err)
       else get_frame_header s)).
    { cbv zeta. destruct (le_field s 0 4 =? ZSTD_MAGICNUMBER) eqn:E; [reflexivity|].
      unfold get_frame_header at 1. rewrite H5f. rewrite E. reflexivity. }
    assert (Hne: le_field s 0 4 <> ZSTD_MAGICNUMBER)
      by (intro E; rewrite E, Z.eqb_refl in H1; apply H1; reflexivity).
    cbv zeta in Hgfh. rewrite (proj2 (Z.eqb_neq _ _) Hne) in Hgfh. cbn [negb] in Hgfh.
    forward_call (sh, offset_val off base, s, 0).
    1: (apply win_read; auto; lia).
    forward_if (PROP (is_skippable_magic (le_field s 0 4) = false)
      LOCAL (temp _t'8 (Vint (Int.repr (le_field s 0 4))); temp _minInputSize (Vlong (Int64.repr ZSTD_FRAMEHEADERSIZE_PREFIX));
     temp _ip (offset_val off base); lvar _hbuf (tarray tuchar 4) v_hbuf;
     gvars gv; temp _zfhPtr zfh; temp _src (offset_val off base);
     temp _srcSize (Vlong (Int64.repr (Zlength s))); temp _format (Vint (Int.repr 0))) SEP (data_at shz t_fh (fh_val fh0) zfh; data_at_ Tsh (tarray tuchar 4) v_hbuf; zstd_globals gv;
     data_at sh (tarray tuchar (Zlength s)) (zbytes s) (offset_val off base);
     win_rest sh N c off (Zlength s) base)).
    { rewrite and_mask_repr in H2 by auto.
      apply repr_inj32 in H2; [| apply land_mask_range; auto | unfold ZSTD_MAGIC_SKIPPABLE_START; lia].
      assert (Hsk: is_skippable_magic (le_field s 0 4) = true)
        by (unfold is_skippable_magic; rewrite H2; apply Z.eqb_refl).
      rewrite Hsk in Hgfh.
      forward_if (PROP (Zlength s >= 8)
        LOCAL (temp _t'8 (Vint (Int.repr (le_field s 0 4))); temp _minInputSize (Vlong (Int64.repr ZSTD_FRAMEHEADERSIZE_PREFIX));
     temp _ip (offset_val off base); lvar _hbuf (tarray tuchar 4) v_hbuf;
     gvars gv; temp _zfhPtr zfh; temp _src (offset_val off base);
     temp _srcSize (Vlong (Int64.repr (Zlength s))); temp _format (Vint (Int.repr 0))) SEP (data_at shz t_fh (fh_val fh0) zfh; data_at_ Tsh (tarray tuchar 4) v_hbuf; zstd_globals gv;
     data_at sh (tarray tuchar (Zlength s)) (zbytes s) (offset_val off base);
     win_rest sh N c off (Zlength s) base)).
      { forward. Exists 8 (fh_val fh0). entailer!.
        2: (rewrite (win_take_all sh (Zlength c) c off s base Hw Hfc); cancel).
        rewrite !Int64.unsigned_repr in H3 by rep_lia.
        rewrite fh_post_m0; unfold fh_post; rewrite H5f. rewrite Hgfh. unfold ZSTD_SKIPPABLEHEADERSIZE.
        replace (Zlength s <? 8) with true by (symmetry; apply Z.ltb_lt; lia). split; reflexivity. }
      { forward. entailer!. rewrite !Int64.unsigned_repr in H3 by rep_lia. lia. }
      Intros. sep_apply (data_at_data_at_ shz t_fh (fh_val fh0) zfh).
      sep_apply (data_at__memory_block shz t_fh zfh). Intros.
      forward_call (shz, zfh, 0, sizeof t_fh).
      sep_apply (memset_fh shz zfh ltac:(auto) H0).
      forward.
      forward_call (sh, offset_val off base, s, 0).
      1: (apply win_read; auto; lia).
      forward. forward.
      forward_call (sh, offset_val off base, s, 4).
      1: (apply win_read; auto; lia).
      forward.
      pose proof (fh_le_field_range s 4 4 Hb ltac:(lia)) as Hf4. change (2 ^ (8 * 4)) with (2 ^ 32) in Hf4.
      rewrite Int.unsigned_repr by rep_lia.
      forward.
      match goal with |- context [data_at shz t_fh ?v zfh] => Exists 0 v end.
      entailer!.
      2: (rewrite (win_take_all sh (Zlength c) c off s base Hw Hfc); cancel).
      rewrite fh_post_m0; unfold fh_post; rewrite H5f. rewrite Hgfh. unfold ZSTD_SKIPPABLEHEADERSIZE.
      replace (Zlength s <? 8) with false by (symmetry; apply Z.ltb_ge; lia). split; reflexivity. }
    { forward. entailer!. rewrite and_mask_repr in H2 by auto. unfold is_skippable_magic.
      apply Z.eqb_neq. intro E. apply H2. rewrite E. reflexivity. }
    Intros. match goal with Hs: is_skippable_magic _ = false |- _ => rewrite Hs in Hgfh end.
    match goal with |- semax _ ?P _ _ => forward_loop P break: (PROP (False) LOCAL () SEP ()) end;
      [apply andp_left2, derives_refl | | Intros; contradiction].
    once_skip. once_skip. once_skip. once_skip. forward.
    Exists (Int64.unsigned (Int64.repr (-10))) (fh_val fh0). rewrite Int64.repr_unsigned. entailer!.
    2: (rewrite (win_take_all sh (Zlength c) c off s base Hw Hfc); cancel).
    rewrite fh_post_m0; unfold fh_post; rewrite H5f. rewrite Hgfh. dec_err_c.
    unfold fh_err_code_m; rewrite (fh_err_code_magic s) by first [exact Hne | apply Z.ltb_ge in H5f; lia]; reflexivity. }
  { forward. entailer!. destruct Hf as [-> | ->]; [right | left; reflexivity]. change (0 =? 1) with false in *. cbv iota in *.
    destruct (Z.eqb_spec (le_field s 0 4) ZSTD_MAGICNUMBER); auto.
    exfalso; apply Int.one_not_zero; auto. }
  Intros.
  match goal with Hx: f = 1 \/ _ |- _ => rename Hx into Hfm end.
  assert (Hgfh := gfh_m_main (fmt_mg f) s ltac:(rewrite Hml; lia)
    ltac:(intro E; destruct Hfm as [-> | ?]; [discriminate | auto])).
  assert (Hcode := fh_code_fsrc (fmt_mg f) s ltac:(rewrite Hml; lia)
    ltac:(intro E; destruct Hfm as [-> | ?]; [discriminate | auto])).
  sep_apply (derives_refl' _ _ (eq_sym (win_take_all sh N c off s base Hw Hfc))).
  forward_call (gv, sh, base, N, c, off, s, f).
  Intros fhs.
  match goal with Hx: match frame_header_size_m _ _ with _ => _ end |- _ =>
    rewrite fhs_m in Hx by (rewrite Hml; lia); cbv iota beta in Hx; subst fhs end.
  pose proof (fsrc_len (fmt_mg f) s) as Ht_len.
  pose proof (fsrc_byte (fmt_mg f) s) as Ht_byte.
  pose proof (fsrc_le (fmt_mg f) s) as Ht_le.
  pose proof (fsrc_ok (fmt_mg f) s Hb) as Ht_ok.
  clear Hfm.
  remember (fsrc (fmt_mg f) s) as t eqn:Et. clear Et.
  remember (fsh (fmt_mg f)) as d eqn:Ed. clear Ed.
  pose proof (byte_at_range t 4 Ht_ok) as Hbr.
  set (b := byte_at t 4) in *.
  pose proof (fhd_header_size_range b) as Hfr.
  rewrite (win_take_all sh N c off s base Hw Hfc).
  forward_if (PROP (Zlength t >= fhd_header_size b)
    LOCAL (temp _fhsize (Vlong (Int64.repr (fhd_header_size b - d))); temp _minInputSize (Vlong (Int64.repr (5 - d)));
     temp _ip (offset_val off base); lvar _hbuf (tarray tuchar 4) v_hbuf;
     gvars gv; temp _zfhPtr zfh; temp _src (offset_val off base);
     temp _srcSize (Vlong (Int64.repr (Zlength s))); temp _format (Vint (Int.repr f))) SEP (data_at shz t_fh (fh_val fh0) zfh; data_at_ Tsh (tarray tuchar 4) v_hbuf; zstd_globals gv;
     data_at sh (tarray tuchar (Zlength s)) (zbytes s) (offset_val off base);
     win_rest sh N c off (Zlength s) base)).
  { forward. Exists (fhd_header_size b - d) (fh_val fh0). entailer!.
    2: (rewrite (win_take_all sh (Zlength c) c off s base Hw Hfc); cancel).
    unfold fh_post_m. rewrite H5f, Hgfh. unfold gfh_main. fold b.
    replace (Zlength t <? fhd_header_size b) with true by (symmetry; apply Z.ltb_lt; lia). split; reflexivity. }
  { forward. entailer!. }
  Intros.
  forward.
  assert (Hz4: Znth (5 - d - 1) s = b)
    by (rewrite Znth_byte_at by lia; replace (5 - d - 1) with (4 - d) by lia; apply Ht_byte; lia).
  forward.
  1: (rewrite Hz4; entailer!; simpl; rep_lia).
  rewrite Hz4.
  forward. forward. forward. forward. forward. forward. forward. forward. forward.
  rewrite (zero_ext8 b Hbr).
  pose proof (shiftr_byte_range b 2 Hbr ltac:(lia)). pose proof (shiftr_byte_range b 5 Hbr ltac:(lia)).
  pose proof (shiftr_byte_range b 6 Hbr ltac:(lia)).
  rewrite (shr_byte b 2), (shr_byte b 5), (shr_byte b 6) by lia.
  rewrite !and_small by rep_lia.
  assert (Hfcs0: Int64.sub (Int64.repr 0) (Int64.repr (Int.signed (Int.repr 1))) = Int64.repr ZSTD_CONTENTSIZE_UNKNOWN)
    by (unfold Int64.sub; rewrite Int.signed_repr by rep_lia; rewrite !Int64.unsigned_repr by rep_lia;
        apply Int64.eqm_samerepr; exists (-1); reflexivity).
  rewrite Hfcs0. change (Int.signed (Int.repr 0)) with 0.
  set (dic := Z.land b 3). set (cf := Z.land (Z.shiftr b 2) 1). set (ss := Z.land (Z.shiftr b 5) 1).
  set (fid := Z.shiftr b 6).
  assert (Hdic: 0 <= dic <= 3) by (subst dic; rewrite land3; pose proof (Z.mod_pos_bound b 4); lia).
  assert (Hcf: 0 <= cf <= 1) by (subst cf; rewrite land1; pose proof (Z.mod_pos_bound (Z.shiftr b 2) 2); lia).
  assert (Hss: 0 <= ss <= 1) by (subst ss; rewrite land1; pose proof (Z.mod_pos_bound (Z.shiftr b 5) 2); lia).
  assert (Hfid: 0 <= fid <= 3) by (subst fid; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 6) with 64;
    split; [apply Z.div_pos; lia | assert (b / 64 < 4) by (apply Z.div_lt_upper_bound; lia); lia]).
  match goal with |- context [data_at shz t_fh ?v zfh] => set (v1 := v) end.
  assert (Hfhs: Zlength t >= fhd_header_size b) by auto.
  unfold gfh_main in Hgfh. fold b in Hgfh. cbv zeta in Hgfh.
  replace (Zlength t <? fhd_header_size b) with false in Hgfh by (symmetry; apply Z.ltb_ge; lia).
  fold dic cf ss fid in Hgfh.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_loop (PROPx P (LOCALx Q (SEPx R))) break: (PROPx ((Z.land b 8 = 0) :: P) (LOCALx Q (SEPx R))) end.
  { apply andp_left2, derives_refl. }
  { forward_if.
    { match goal with Hx: Int.and _ _ <> _ |- _ => rename Hx into Hr end.
      rewrite and_small in Hr by rep_lia.
      assert (Hr8: Z.land b 8 <> 0) by (intro E; apply Hr; rewrite E; reflexivity).
      once_skip. once_skip. once_skip. once_skip. forward.
      Exists (Int64.unsigned (Int64.repr (-14))) v1. rewrite Int64.repr_unsigned. entailer!.
      2: (rewrite (win_take_all sh (Zlength c) c off s base Hw Hfc); cancel).
      unfold fh_post_m. rewrite H5f, Hgfh, (proj2 (Z.eqb_neq _ _) Hr8). dec_err_c.
      rewrite Hcode, (proj2 (Z.eqb_neq _ _) Hr8). reflexivity. }
    { forward. entailer!. match goal with Hx: Int.and _ _ = _ |- _ => rename Hx into Hr end.
      rewrite and_small in Hr by rep_lia.
      apply repr_inj32 in Hr; [auto | | lia].
      pose proof (land_range (byte_at t 4) 8 8 ltac:(lia) ltac:(lia) ltac:(lia)). lia. } }
  Intros. match goal with Hx: Z.land b 8 = 0 |- _ => rewrite Hx, Z.eqb_refl in Hgfh end. cbn [negb] in Hgfh.
  set (dsz := nth (Z.to_nat dic) [0; 1; 2; 4] 0) in *.
  set (fsz := nth (Z.to_nat fid) [0; 2; 4; 8] 0).
  assert (Hhs: fhd_header_size b = 5 + (1 - ss) + dsz + fsz + (if andb (ss =? 1) (fid =? 0) then 1 else 0))
    by reflexivity.
  assert (Hdsz: dsz = 0 /\ dic = 0 \/ dsz = 1 /\ dic = 1 \/ dsz = 2 /\ dic = 2 \/ dsz = 4 /\ dic = 3)
    by (subst dsz; assert (dic = 0 \/ dic = 1 \/ dic = 2 \/ dic = 3) as [E|[E|[E|E]]] by lia; rewrite E; auto).
  assert (Hfsz: fsz = 0 /\ fid = 0 \/ fsz = 2 /\ fid = 1 \/ fsz = 4 /\ fid = 2 \/ fsz = 8 /\ fid = 3)
    by (subst fsz; assert (fid = 0 \/ fid = 1 \/ fid = 2 \/ fid = 3) as [E|[E|[E|E]]] by lia; rewrite E; auto).
  assert (He: 0 <= (if andb (ss =? 1) (fid =? 0) then 1 else 0) <= 1) by (clear Hgfh; destruct (andb _ _); lia).
  forward_if (PROP (ss = 0 -> Z.shiftr (byte_at t 5) 3 + ZSTD_WINDOWLOG_ABSOLUTEMIN <= ZSTD_WINDOWLOG_MAX)
    LOCAL (temp _windowSize (Vlong (Int64.repr (if ss =? 0 then wsz (byte_at t 5) else 0)));
           temp _pos (Vlong (Int64.repr (6 - ss - d))); temp _frameContentSize (Vlong (Int64.repr ZSTD_CONTENTSIZE_UNKNOWN));
     temp _dictID (Vint (Int.repr 0)); temp _fcsID (Vint (Int.repr fid));
     temp _singleSegment (Vint (Int.repr ss)); temp _checksumFlag (Vint (Int.repr cf));
     temp _dictIDSizeCode (Vint (Int.repr dic));
     temp _ip (offset_val off base); lvar _hbuf (tarray tuchar 4) v_hbuf; gvars gv; temp _zfhPtr zfh)
    SEP (data_at shz t_fh v1 zfh; data_at_ Tsh (tarray tuchar 4) v_hbuf; zstd_globals gv;
     data_at sh (tarray tuchar (Zlength s)) (zbytes s) (offset_val off base);
     win_rest sh N c off (Zlength s) base)).
  { match goal with Hx: Int.repr ss = Int.zero |- _ => rename Hx into Hsz end.
    assert (Hs0': ss = 0) by (change Int.zero with (Int.repr 0) in Hsz; apply repr_inj32 in Hsz; lia).
    forward. forward.
    assert (H5': 0 <= 5 - d < Zlength s) by lia.
    assert (Hz5: Znth (5 - d) s = byte_at t 5) by (rewrite Znth_byte_at by lia; apply Ht_byte; lia).
    pose proof (byte_at_range t 5 Ht_ok) as Hb5.
    forward.
    1: (rewrite Hz5; entailer!; simpl; rep_lia).
    rewrite Hz5.
    forward. rewrite (zero_ext8 _ Hb5).
    pose proof (shiftr_byte_range (byte_at t 5) 3 Hb5 ltac:(lia)) as Hw3.
    forward.
    1: (entailer!; rewrite (shr_byte _ 3 Hb5 ltac:(lia)), Int.signed_repr by rep_lia; rep_lia).
    rewrite (shr_byte _ 3 Hb5 ltac:(lia)), add_repr.
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_loop (PROPx P (LOCALx Q (SEPx R)))
        break: (PROPx ((Z.shiftr (byte_at t 5) 3 + 10 <= 31) :: P) (LOCALx Q (SEPx R))) end.
    { apply andp_left2, derives_refl. }
    { match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
        forward_if (PROPx P (LOCALx (temp _t'13 (Vint (Int.repr 31)) :: Q) (SEPx R))) end.
      { discriminate. }
      { forward. entailer!. }
      forward_if.
      { once_skip. once_skip. once_skip. once_skip. forward.
        Exists (Int64.unsigned (Int64.repr (-16))) v1. rewrite Int64.repr_unsigned. entailer!.
        2: (rewrite (win_take_all sh (Zlength c) c off s base Hw Hfc); cancel).
        unfold fh_post_m. rewrite H5f, Hgfh, Hs0', Z.eqb_refl. unfold ZSTD_WINDOWLOG_ABSOLUTEMIN, ZSTD_WINDOWLOG_MAX.
        replace (Z.shiftr (byte_at t 5) 3 + 10 >? 31) with true by (symmetry; apply Z.gtb_lt; lia).
        dec_err_c.
        rewrite Hcode. match goal with Hx: Z.land _ 8 = 0 |- _ => rewrite Hx end. reflexivity. }
      { forward. entailer!. } }
    Intros.
    forward. 1: (entailer!; change (Int.unsigned Int64.iwordsize') with 64; lia).
    forward.
    entailer!.
    rewrite Hs0', Z.eqb_refl. split; [| do 2 f_equal; lia].
    rewrite wsz_eq by (auto; lia). reflexivity. }
  { forward. entailer!.
    assert (ss <> 0) by (intro E; match goal with Hx: Int.repr ss <> _ |- _ => apply Hx end; rewrite E; reflexivity).
    assert (ss = 1) by lia.
    split3; [lia | rewrite (proj2 (Z.eqb_neq ss 0)) by lia; auto | do 2 f_equal; lia]. }
  Intros.
  forward_if (PROP ()
    LOCAL (temp _dictID (Vint (Int.repr (le_field t (6 - ss) dsz))); temp _pos (Vlong (Int64.repr (6 - ss + dsz - d)));
     temp _windowSize (Vlong (Int64.repr (if ss =? 0 then wsz (byte_at t 5) else 0)));
     temp _frameContentSize (Vlong (Int64.repr ZSTD_CONTENTSIZE_UNKNOWN));
     temp _fcsID (Vint (Int.repr fid)); temp _singleSegment (Vint (Int.repr ss));
     temp _checksumFlag (Vint (Int.repr cf));
     temp _ip (offset_val off base); lvar _hbuf (tarray tuchar 4) v_hbuf; gvars gv; temp _zfhPtr zfh)
    SEP (data_at shz t_fh v1 zfh; data_at_ Tsh (tarray tuchar 4) v_hbuf; zstd_globals gv;
     data_at sh (tarray tuchar (Zlength s)) (zbytes s) (offset_val off base);
     win_rest sh N c off (Zlength s) base)).
  { assert (Hd0: dsz = 0) by lia. forward. entailer!. rewrite Hd0. split; [reflexivity | do 2 f_equal; lia]. }
  { assert (Hd1: dsz = 1) by lia.
    assert (Hp: 0 <= 6 - ss - d < Zlength s) by lia.
    assert (Hzp: 0 <= Znth (6 - ss - d) s < 256)
      by (pose proof (proj1 (Forall_Znth _ _) Hb (6 - ss - d) ltac:(lia)) as X; exact X).
    forward. 1: (entailer!; try (simpl; rep_lia)).
    forward. forward. entailer!. rewrite Hd1, <- Ht_le, le_field1 by lia.
    split; [reflexivity | do 2 f_equal; lia]. }
  { assert (Hd2: dsz = 2) by lia.
    apply -> seq_assoc. apply -> seq_assoc. eapply semax_seq'.
    { clear Hgfh. forward_call (sh, offset_val off base, s, 6 - ss - d).
      1: (apply win_read; auto; lia).
      apply andp_left2, derives_refl. }
    abbreviate_semax.
    forward. forward. forward. entailer!. rewrite Hd2, <- Ht_le by lia.
    split; [reflexivity | do 2 f_equal; lia]. }
  { assert (Hd3: dsz = 4) by lia.
    apply -> seq_assoc. apply -> seq_assoc. eapply semax_seq'.
    { clear Hgfh. forward_call (sh, offset_val off base, s, 6 - ss - d).
      1: (apply win_read; auto; lia).
      apply andp_left2, derives_refl. }
    abbreviate_semax.
    forward. forward. forward. entailer!. rewrite Hd3, <- Ht_le by lia.
    split; [reflexivity | do 2 f_equal; lia]. }
  { exfalso. rewrite !Int.unsigned_repr in NE, NE0, NE1, NE2 by rep_lia. lia. }
  match goal with Hx: ss = 0 -> _ |- _ => rename Hx into Hwl end.
  assert (Hpf: 6 - ss + dsz + fsz + (if andb (ss =? 1) (fid =? 0) then 1 else 0) <= Zlength t) by lia.
  forward_if (PROP ()
    LOCAL (temp _frameContentSize (Vlong (Int64.repr (if fid =? 0 then (if ss =? 1 then byte_at t (6 - ss + dsz) else ZSTD_CONTENTSIZE_UNKNOWN)
        else if fid =? 1 then le_field t (6 - ss + dsz) 2 + 256
        else if fid =? 2 then le_field t (6 - ss + dsz) 4
        else le_field t (6 - ss + dsz) 8))); temp _dictID (Vint (Int.repr (le_field t (6 - ss) dsz)));
     temp _windowSize (Vlong (Int64.repr (if ss =? 0 then wsz (byte_at t 5) else 0)));
     temp _singleSegment (Vint (Int.repr ss)); temp _checksumFlag (Vint (Int.repr cf));
     temp _ip (offset_val off base); lvar _hbuf (tarray tuchar 4) v_hbuf; gvars gv; temp _zfhPtr zfh)
    SEP (data_at shz t_fh v1 zfh; data_at_ Tsh (tarray tuchar 4) v_hbuf; zstd_globals gv;
     data_at sh (tarray tuchar (Zlength s)) (zbytes s) (offset_val off base);
     win_rest sh N c off (Zlength s) base)).
  { rename E into Hf0.
    forward_if (PROP ()
      LOCAL (temp _frameContentSize (Vlong (Int64.repr
               (if ss =? 1 then byte_at t (6 - ss + dsz) else ZSTD_CONTENTSIZE_UNKNOWN)));
             temp _pos (Vlong (Int64.repr (6 - ss + dsz - d))); temp _dictID (Vint (Int.repr (le_field t (6 - ss) dsz)));
     temp _windowSize (Vlong (Int64.repr (if ss =? 0 then wsz (byte_at t 5) else 0)));
     temp _singleSegment (Vint (Int.repr ss)); temp _checksumFlag (Vint (Int.repr cf));
     temp _ip (offset_val off base); lvar _hbuf (tarray tuchar 4) v_hbuf; gvars gv; temp _zfhPtr zfh)
      SEP (data_at shz t_fh v1 zfh; data_at_ Tsh (tarray tuchar 4) v_hbuf; zstd_globals gv;
     data_at sh (tarray tuchar (Zlength s)) (zbytes s) (offset_val off base);
     win_rest sh N c off (Zlength s) base)).
    { assert (Hs1: ss = 1) by (destruct (Z.eq_dec ss 0) as [E0|E0]; [rewrite E0 in *; contradiction | lia]).
      assert (Hp: 0 <= 6 - ss + dsz - d < Zlength s) by (rewrite Hs1, Hf0 in Hpf; simpl in Hpf; lia).
      assert (Hzp: Znth (6 - ss + dsz - d) s = byte_at t (6 - ss + dsz))
        by (rewrite Znth_byte_at by lia; apply Ht_byte; lia).
      pose proof (byte_at_range t (6 - ss + dsz) Ht_ok) as Hbp.
      forward. 1: (rewrite Hzp; entailer!; try (simpl; rep_lia)).
      rewrite Hzp. forward. entailer!. rewrite Hs1. reflexivity. }
    { forward. entailer!.
      match goal with Hx: Int.repr ss = Int.zero |- _ =>
        change Int.zero with (Int.repr 0) in Hx; apply repr_inj32 in Hx; [rewrite Hx; reflexivity | lia | lia] end. }
    forward. entailer!. rewrite Hf0. reflexivity. }
  { rename E into Hf1.
    pose proof (fh_le_field_range t (6 - ss + dsz) 2 Ht_ok ltac:(lia)) as Hr1.
    apply -> seq_assoc. apply -> seq_assoc. eapply semax_seq'.
    { clear Hgfh. forward_call (sh, offset_val off base, s, 6 - ss + dsz - d).
      1: (apply win_read; auto; lia).
      apply andp_left2, derives_refl. }
    abbreviate_semax.
    rewrite (Ht_le (6 - ss + dsz)) by lia.
    forward.
    forward. entailer!. rewrite Hf1. simpl. reflexivity. }
  { rename E into Hf2.
    pose proof (fh_le_field_range t (6 - ss + dsz) 4 Ht_ok ltac:(lia)) as Hr2.
    apply -> seq_assoc. apply -> seq_assoc. eapply semax_seq'.
    { clear Hgfh. forward_call (sh, offset_val off base, s, 6 - ss + dsz - d).
      1: (apply win_read; auto; lia).
      apply andp_left2, derives_refl. }
    abbreviate_semax.
    rewrite (Ht_le (6 - ss + dsz)) by lia.
    forward.
    forward. entailer!. rewrite Hf2. simpl. reflexivity. }
  { rename E into Hf3.
    pose proof (fh_le_field_range t (6 - ss + dsz) 8 Ht_ok ltac:(lia)) as Hr3.
    apply -> seq_assoc. apply -> seq_assoc. eapply semax_seq'.
    { clear Hgfh. forward_call (sh, offset_val off base, s, 6 - ss + dsz - d).
      1: (apply win_read; auto; lia).
      apply andp_left2, derives_refl. }
    abbreviate_semax.
    rewrite (Ht_le (6 - ss + dsz)) by lia.
    forward.
    forward. entailer!. rewrite Hf3. simpl. reflexivity. }
  { exfalso. rewrite !Int.unsigned_repr in * by rep_lia. lia. }
  set (fcsv := (if fid =? 0 then (if ss =? 1 then byte_at t (6 - ss + dsz) else ZSTD_CONTENTSIZE_UNKNOWN)
        else if fid =? 1 then le_field t (6 - ss + dsz) 2 + 256
        else if fid =? 2 then le_field t (6 - ss + dsz) 4
        else le_field t (6 - ss + dsz) 8)).
  set (wsv := if ss =? 1 then fcsv else wsz (byte_at t 5)).
  forward_if (PROP ()
    LOCAL (temp _windowSize (Vlong (Int64.repr wsv)); temp _frameContentSize (Vlong (Int64.repr fcsv));
     temp _dictID (Vint (Int.repr (le_field t (6 - ss) dsz)));
     temp _checksumFlag (Vint (Int.repr cf));
     temp _ip (offset_val off base); lvar _hbuf (tarray tuchar 4) v_hbuf; gvars gv; temp _zfhPtr zfh)
    SEP (data_at shz t_fh v1 zfh; data_at_ Tsh (tarray tuchar 4) v_hbuf; zstd_globals gv;
     data_at sh (tarray tuchar (Zlength s)) (zbytes s) (offset_val off base);
     win_rest sh N c off (Zlength s) base)).
  { forward. entailer!.
    assert (Hs1: ss = 1) by (destruct (Z.eq_dec ss 0) as [E0|E0]; [rewrite E0 in *; contradiction | lia]).
    unfold wsv. rewrite Hs1. reflexivity. }
  { forward. entailer!.
    match goal with Hx: Int.repr ss = Int.zero |- _ =>
      change Int.zero with (Int.repr 0) in Hx; apply repr_inj32 in Hx; [| lia | lia] end.
    unfold wsv. match goal with Hx: ss = 0 |- _ => rewrite Hx end. reflexivity. }
  forward. forward. forward.
  assert (Hfcr: 0 <= fcsv <= Int64.max_unsigned).
  { pose proof (fh_le_field_range t (6 - ss + dsz) 2 Ht_ok ltac:(lia)) as Q2.
    pose proof (fh_le_field_range t (6 - ss + dsz) 4 Ht_ok ltac:(lia)) as Q4.
    pose proof (fh_le_field_range t (6 - ss + dsz) 8 Ht_ok ltac:(lia)) as Q8.
    pose proof (byte_at_range t (6 - ss + dsz) Ht_ok) as Q1.
    clear - Q2 Q4 Q8 Q1. unfold fcsv, ZSTD_CONTENTSIZE_UNKNOWN.
    simpl in Q2, Q4, Q8.
    destruct (fid =? 0); [destruct (ss =? 1) | destruct (fid =? 1); [| destruct (fid =? 2)]]; rep_lia. }
  assert (Hwsr: 0 <= wsv <= Int64.max_unsigned).
  { unfold wsv. destruct (ss =? 1) eqn:Es; [auto|].
    apply Z.eqb_neq in Es. assert (Es0: ss = 0) by lia.
    pose proof (wsz_range (byte_at t 5) (byte_at_range t 5 Ht_ok)
      ltac:(apply Hwl in Es0; unfold ZSTD_WINDOWLOG_ABSOLUTEMIN, ZSTD_WINDOWLOG_MAX in Es0; lia)).
    rep_lia. }
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _t'19 (Vlong (Int64.repr (Z.min wsv 131072))) :: Q) (SEPx R))) end.
  { forward. entailer!.
    match goal with Hx: Int64.ltu _ _ = true |- _ =>
      change (Int.signed (Int.shl (Int.repr 1) (Int.repr 17))) with 131072 in Hx;
      apply ltu_inv64 in Hx; rewrite !Int64.unsigned_repr in Hx by rep_lia end.
    rewrite Z.min_l by lia. reflexivity. }
  { forward. entailer!.
    match goal with Hx: Int64.ltu _ _ = false |- _ =>
      change (Int.signed (Int.shl (Int.repr 1) (Int.repr 17))) with 131072 in Hx |- *;
      apply ltu_false_inv64 in Hx; rewrite !Int64.unsigned_repr in Hx by rep_lia end.
    rewrite Z.min_r by lia. reflexivity. }
  forward. forward. forward.
  match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx (data_at shz t_fh ?v zfh :: _)))) _ _ =>
    assert (Hpost: fh_post_m (fmt_mg f) s 0 v0 v) end.
  { unfold fh_post_m. rewrite H5f, Hgfh.
    replace (andb (ss =? 0) (Z.shiftr (byte_at t 5) 3 + ZSTD_WINDOWLOG_ABSOLUTEMIN >? ZSTD_WINDOWLOG_MAX))
      with false.
    2: { destruct (Z.eq_dec ss 0) as [E|E].
         - specialize (Hwl E). rewrite E. simpl. symmetry. rewrite Z.gtb_ltb. apply Z.ltb_ge. lia.
         - rewrite (proj2 (Z.eqb_neq _ _) E). reflexivity. }
    split; [reflexivity|].
    replace (5 + (1 - ss) + dsz) with (6 - ss + dsz) by lia.
    replace (5 + (1 - ss)) with (6 - ss) by lia.
    unfold fh_val, fh_hsub. cbn [fh_contentSize fh_windowSize fh_blockSizeMax fh_frameType fh_headerSize fh_dictID fh_checksumFlag].
    f_equal. f_equal. f_equal. 2: f_equal. 2: f_equal. 2: f_equal. 2: f_equal. 2: f_equal.
    - rewrite Int64.Z_mod_modulus_eq, Z.mod_small by (pose proof (Z.le_min_l wsv 131072); rep_lia).
      reflexivity.
    - unfold v1. simpl. rewrite Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia. reflexivity. }
  forward.
  match goal with |- context [data_at shz t_fh ?v zfh] => Exists 0 v end.
  entailer!.
  rewrite (win_take_all sh (Zlength c) c off s base Hw Hfc). cancel.
Qed.
