(* Subtree H: shared lemmas on input windows (DecIface.win_ok) and the model. *)
Require Export Zstd.proof.dec.H.HSpecs.
Local Open Scope logic.

Lemma arr_split3: forall sh n i k (l: list val) p,
  0 <= i -> 0 <= k -> i + k <= n -> Zlength l = n ->
  field_compatible (tarray tuchar n) [] p ->
  data_at sh (tarray tuchar n) l p =
  (data_at sh (tarray tuchar i) (sublist 0 i l) p *
   data_at sh (tarray tuchar k) (sublist i (i + k) l) (offset_val i p) *
   data_at sh (tarray tuchar (n - (i + k))) (sublist (i + k) n l) (offset_val (i + k) p)).
Proof.
  intros. rewrite (split3_data_at_Tarray_tuchar sh n i (i + k)) by lia.
  change (Tarray tuchar n noattr) with (tarray tuchar n). rewrite !arr_field_address0 by (auto; lia).
  replace (i + k - i) with k by lia. simpl sizeof. rewrite !Z.mul_1_l. reflexivity.
Qed.

(* an API buffer is a window of itself *)
Lemma win_ok_full: forall sh s, src_spec_pre sh s -> win_ok sh (Zlength s) (zbytes s) 0 (Zlength s) s.
Proof.
  intros sh s [H1 [H2 H3]]. unfold win_ok. pose proof (Zlength_nonneg s).
  rewrite Zlength_map. repeat split; auto; try lia.
  rewrite sublist_same by (rewrite ?Zlength_map; lia). auto.
Qed.

(* the rest of a window after its first k bytes *)
Lemma win_ok_skip: forall sh N c off s k, win_ok sh N c off (Zlength s) s -> 0 <= k <= Zlength s ->
  win_ok sh N c (off + k) (Zlength s - k) (sublist k (Zlength s) s).
Proof.
  intros sh N c off s k [H1 [H2 [H3 [H4 [H5 [H6 [H7 H8]]]]]]] Hk. unfold win_ok.
  repeat split; auto; try lia.
  - list_solve.
  - unfold bytes_ok in *. apply Forall_sublist; auto.
  - replace (off + k + (Zlength s - k)) with (off + Zlength s) by lia.
    rewrite <- sublist_map, <- H8. list_solve.
Qed.

(* the window's bytes as an array of their own, between the two other parts of the array *)
Lemma win_split: forall sh N c off s base,
  win_ok sh N c off (Zlength s) s -> field_compatible (tarray tuchar N) [] base ->
  data_at sh (tarray tuchar N) c base =
  (data_at sh (tarray tuchar off) (sublist 0 off c) base *
   data_at sh (tarray tuchar (Zlength s)) (zbytes s) (offset_val off base) *
   data_at sh (tarray tuchar (N - (off + Zlength s))) (sublist (off + Zlength s) N c)
     (offset_val (off + Zlength s) base)).
Proof.
  intros sh N c off s base [H1 [H2 [H3 [H4 [H5 [H6 [H7 H8]]]]]]] Hfc. pose proof (Zlength_nonneg s).
  rewrite (arr_split3 sh N off (Zlength s) c base) by (auto; lia). rewrite H8. reflexivity.
Qed.

(* ZSTD_findFrameCompressedSize is the first component of ZSTD_findFrameSizeInfo *)
Lemma frame_compressed_size_info: forall s,
  frame_compressed_size s = option_map fst (frame_size_info s).
Proof.
  intros s. unfold frame_compressed_size, frame_size_info.
  destruct (andb _ _); [destruct (skippable_frame_size s); reflexivity |].
  destruct (get_frame_header s) as [| |h]; try reflexivity.
  destruct (blocks_size _ _) as [[k nb]|]; [|reflexivity].
  destruct (fh_checksumFlag h =? 1); [destruct (_ <? 4)|]; reflexivity.
Qed.

(* dec_err (StreamModel): an error code other than the two noForwardProgress ones *)
Lemma dec_err_is_error: forall r, dec_err r -> is_error_code r = true.
Proof. intros r [H _]. exact H. Qed.

Lemma dec_err_neg: forall e, 0 < e < 120 -> e <> 80 -> e <> 82 ->
  dec_err (Int64.unsigned (Int64.repr (- e))).
Proof.
  intros e He H80 H82. unfold dec_err, is_error_code, ZSTD_error_noForwardProgress_destFull,
    ZSTD_error_noForwardProgress_inputEmpty.
  rewrite Int64.unsigned_repr_eq. change Int64.modulus with (2 ^ 64).
  replace (- e mod 2 ^ 64) with (2 ^ 64 - e) by (apply Z.mod_unique_pos with (-1); lia).
  split; [apply Z.ltb_lt; lia | split; lia].
Qed.
