(* Bodies of group util: MEM_* reads and writes (except MEM_write64), swaps, MEM_32bits/64bits/isLittleEndian. *)
Require Import Zstd.proof.zstd.Gprog.
Require Import Zstd.proof.zstd.PickLemmas.


Lemma arr_split3: forall sh n i k (l: list val) p,
  0 <= i -> 0 <= k -> i + k <= n -> Zlength l = n ->
  field_compatible (tarray tuchar n) [] p ->
  data_at sh (tarray tuchar n) l p =
  (data_at sh (tarray tuchar i) (sublist 0 i l) p *
   data_at sh (tarray tuchar k) (sublist i (i + k) l) (offset_val i p) *
   data_at sh (tarray tuchar (n - (i + k))) (sublist (i + k) n l) (offset_val (i + k) p))%logic.
Proof.
  intros. rewrite (split3_data_at_Tarray_tuchar sh n i (i + k)) by lia.
  change (Tarray tuchar n noattr) with (tarray tuchar n). rewrite !arr_field_address0 by (auto; lia).
  replace (i + k - i) with k by lia. simpl sizeof. rewrite !Z.mul_1_l. reflexivity.
Qed.

Lemma bytes_ok_range: forall l, bytes_ok l -> Forall (fun b => 0 <= b <= Byte.max_unsigned) l.
Proof.
  intros l H. eapply Forall_impl; [|exact H]. intros a Ha. unfold is_byte in Ha. rep_lia.
Qed.

Lemma le_field_sublist: forall bs i k, 0 <= i -> 0 <= k ->
  le_field bs i k = le_value (sublist i (i + k) bs).
Proof.
  intros. unfold le_field, slice, sublist. f_equal.
  rewrite skipn_firstn_comm. f_equal. lia.
Qed.

Lemma mem_written_split: forall sh c i k v p,
  0 <= i -> 0 <= k -> i + k <= Zlength c ->
  field_compatible (tarray tuchar (Zlength c)) [] p ->
  data_at sh (tarray tuchar (Zlength c)) (mem_written c i k v) p =
  (data_at sh (tarray tuchar i) (sublist 0 i c) p *
   data_at sh (tarray tuchar k) (zbytes (le_bytes (Z.to_nat k) v)) (offset_val i p) *
   data_at sh (tarray tuchar (Zlength c - (i + k))) (sublist (i + k) (Zlength c) c)
     (offset_val (i + k) p))%logic.
Proof.
  intros.
  assert (Zlength (zbytes (le_bytes (Z.to_nat k) v)) = k)
    by (rewrite Zlength_map, Zlength_le_bytes; lia).
  assert (Zlength (mem_written c i k v) = Zlength c)
    by (unfold mem_written; list_solve).
  rewrite (arr_split3 sh (Zlength c) i k (mem_written c i k v) p) by (auto; lia).
  unfold mem_written.
  f_equal; [f_equal|]; f_equal; list_solve.
Qed.

Lemma body_MEM_32bits: semax_body Vprog Gprog f_MEM_32bits MEM_32bits_spec.
Proof. start_function. forward. Qed.

Lemma body_MEM_64bits: semax_body Vprog Gprog f_MEM_64bits MEM_64bits_spec.
Proof. start_function. forward. Qed.

Lemma body_MEM_isLittleEndian: semax_body Vprog Gprog f_MEM_isLittleEndian MEM_isLittleEndian_spec.
Proof. start_function. forward. Qed.

Lemma body_MEM_swap32_fallback: semax_body Vprog Gprog f_MEM_swap32_fallback MEM_swap32_fallback_spec.
Proof. start_function. forward. EExists. entailer!. Qed.

Lemma body_MEM_swap32: semax_body Vprog Gprog f_MEM_swap32 MEM_swap32_spec.
Proof. start_function. forward_call v. Intros r. forward. EExists. entailer!. Qed.

Lemma body_MEM_swap64_fallback: semax_body Vprog Gprog f_MEM_swap64_fallback MEM_swap64_fallback_spec.
Proof. start_function. forward. EExists. entailer!. Qed.

Lemma body_MEM_swap64: semax_body Vprog Gprog f_MEM_swap64 MEM_swap64_spec.
Proof. start_function. forward_call v. Intros r. forward. EExists. entailer!. Qed.

Lemma body_MEM_read16: semax_body Vprog Gprog f_MEM_read16 MEM_read16_spec.
Proof.
  start_function. destruct H as (Hsh & Hi & Hik & Hok).
  assert_PROP (field_compatible (tarray tuchar (Zlength bs)) [] p) as FC by entailer!.
  assert_PROP (field_compatible tushort [] v_val) as FCv by entailer!.
  rewrite (arr_split3 sh (Zlength bs) i 2 (zbytes bs) p) by (auto; list_solve).
  rewrite (data_at__tushort_bytes Tsh v_val FCv).
  rewrite !sublist_map. Intros.
  forward_call (sh, Tsh, offset_val i p, v_val, existT (fun t => reptype t) (tarray tuchar 2) (zbytes (sublist i (i + 2) bs))).
  { memcpy_side. }
  simpl projT1; simpl projT2.
  rewrite (bytes2_tushort Tsh (sublist i (i + 2) bs) v_val) by (auto using bytes_ok_range; list_solve).
  pose proof (le_value_range (sublist i (i + 2) bs) (bytes_ok_range _ Hok)) as R.
  rewrite Zlength_sublist in R by list_solve. replace (8 * (i + 2 - i)) with 16 in R by lia.
  change (2^16) with 65536 in R.
  forward.
  { entailer!. lia. }
  forward.
  rewrite (arr_split3 sh (Zlength bs) i 2 (zbytes bs) p) by (auto; list_solve).
  rewrite !sublist_map. rewrite le_field_sublist by lia.
  entailer!.
Qed.

Lemma body_MEM_read32: semax_body Vprog Gprog f_MEM_read32 MEM_read32_spec.
Proof.
  start_function. destruct H as (Hsh & Hi & Hik & Hok).
  assert_PROP (field_compatible (tarray tuchar (Zlength bs)) [] p) as FC by entailer!.
  assert_PROP (field_compatible tuint [] v_val) as FCv by entailer!.
  rewrite (arr_split3 sh (Zlength bs) i 4 (zbytes bs) p) by (auto; list_solve).
  rewrite (data_at__tuint_bytes Tsh v_val FCv).
  rewrite !sublist_map. Intros.
  forward_call (sh, Tsh, offset_val i p, v_val, existT (fun t => reptype t) (tarray tuchar 4) (zbytes (sublist i (i + 4) bs))).
  { memcpy_side. }
  simpl projT1; simpl projT2.
  rewrite (bytes4_tuint Tsh (sublist i (i + 4) bs) v_val) by (auto using bytes_ok_range; list_solve).
  forward.
  forward.
  rewrite (arr_split3 sh (Zlength bs) i 4 (zbytes bs) p) by (auto; list_solve).
  rewrite !sublist_map. rewrite le_field_sublist by lia.
  entailer!.
Qed.

Lemma body_MEM_read64: semax_body Vprog Gprog f_MEM_read64 MEM_read64_spec.
Proof.
  start_function. destruct H as (Hsh & Hi & Hik & Hok).
  assert_PROP (field_compatible (tarray tuchar (Zlength bs)) [] p) as FC by entailer!.
  assert_PROP (field_compatible tulong [] v_val) as FCv by entailer!.
  rewrite (arr_split3 sh (Zlength bs) i 8 (zbytes bs) p) by (auto; list_solve).
  rewrite (data_at__tulong_bytes Tsh v_val FCv).
  rewrite !sublist_map. Intros.
  forward_call (sh, Tsh, offset_val i p, v_val, existT (fun t => reptype t) (tarray tuchar 8) (zbytes (sublist i (i + 8) bs))).
  { memcpy_side. }
  simpl projT1; simpl projT2.
  sep_apply (bytes8_tulong Tsh (sublist i (i + 8) bs) v_val); auto using bytes_ok_range; try list_solve.
  forward.
  forward.
  rewrite (arr_split3 sh (Zlength bs) i 8 (zbytes bs) p) by (auto; list_solve).
  rewrite !sublist_map. rewrite le_field_sublist by lia.
  entailer!.
Qed.

Lemma body_MEM_write16: semax_body Vprog Gprog f_MEM_write16 MEM_write16_spec.
Proof.
  start_function. destruct H as (Hsh & Hi & Hik).
  assert_PROP (field_compatible (tarray tuchar (Zlength c)) [] p) as FC by entailer!.
  forward.
  assert_PROP (field_compatible tushort [] v_value) as FCv by entailer!.
  rewrite zero_ext_inrange by (rewrite Int.unsigned_repr by rep_lia; simpl; lia).
  rewrite (tushort_bytes2 Tsh v v_value FCv H0).
  rewrite (arr_split3 sh (Zlength c) i 2 c p) by (auto; list_solve). Intros.
  sep_apply (data_at_data_at_ sh (tarray tuchar 2) (sublist i (i + 2) c) (offset_val i p)).
  forward_call (Tsh, sh, v_value, offset_val i p, existT (fun t => reptype t) (tarray tuchar 2) (zbytes (le_bytes 2 v))).
  { memcpy_side. }
  simpl projT1; simpl projT2.
  rewrite (mem_written_split sh c i 2 v p) by (auto; lia).
  entailer!.
  rewrite (data_at__tushort_bytes Tsh v_value FCv). apply data_at_data_at_.
Qed.

Lemma body_MEM_write32: semax_body Vprog Gprog f_MEM_write32 MEM_write32_spec.
Proof.
  start_function. destruct H as (Hsh & Hi & Hik).
  assert_PROP (field_compatible (tarray tuchar (Zlength c)) [] p) as FC by entailer!.
  forward.
  assert_PROP (field_compatible tuint [] v_value) as FCv by entailer!.
  rewrite (tuint_bytes4 Tsh v v_value FCv).
  rewrite (arr_split3 sh (Zlength c) i 4 c p) by (auto; list_solve). Intros.
  sep_apply (data_at_data_at_ sh (tarray tuchar 4) (sublist i (i + 4) c) (offset_val i p)).
  forward_call (Tsh, sh, v_value, offset_val i p, existT (fun t => reptype t) (tarray tuchar 4) (zbytes (le_bytes 4 v))).
  { memcpy_side. }
  simpl projT1; simpl projT2.
  rewrite (mem_written_split sh c i 4 v p) by (auto; lia).
  entailer!.
  rewrite (data_at__tuint_bytes Tsh v_value FCv). apply data_at_data_at_.
Qed.

Lemma body_MEM_readLE16: semax_body Vprog Gprog f_MEM_readLE16 MEM_readLE16_spec.
Proof.
  start_function.
  forward_call tt.
  forward_if.
  - forward_call (sh, p, bs, i). forward.
  - discriminate.
Qed.

Lemma body_MEM_readLE24: semax_body Vprog Gprog f_MEM_readLE24 MEM_readLE24_spec.
Proof.
  start_function. pose proof H as (Hsh & Hi & Hik & Hok).
  forward_call (sh, p, bs, i).
  { unfold mem_read_pre. split; [auto|split; [auto|split; [lia|]]].
    unfold bytes_ok in *. replace (sublist i (i + 2) bs) with (sublist 0 2 (sublist i (i + 3) bs)) by list_solve.
    apply Forall_sublist; auto. }
  assert_PROP (field_compatible (tarray tuchar (Zlength bs)) [] p) as FC by entailer!.
  assert_PROP (force_val (sem_add_ptr_int tuchar Signed (offset_val i p) (Vint (Int.repr 2))) =
               field_address (tarray tuchar (Zlength bs)) [ArraySubsc (i + 2)] p) as E.
  { entailer!. rewrite arr_field_address by (auto; lia).
    destruct p; try contradiction. simpl. f_equal.
    f_equal. f_equal. lia. }
  assert (S3: sublist i (i + 3) bs = [Znth i bs; Znth (i + 1) bs; Znth (i + 2) bs]) by list_solve.
  assert (S2: sublist i (i + 2) bs = [Znth i bs; Znth (i + 1) bs]) by list_solve.
  rewrite S3 in Hok. unfold bytes_ok, is_byte in Hok.
  inversion Hok as [|? ? B0 Hok1]; subst. inversion Hok1 as [|? ? B1 Hok2]; subst.
  inversion Hok2 as [|? ? B2 _]; subst.
  forward.
  { entailer!. rep_lia. }
  forward.
  entailer!.
  rewrite !le_field_sublist by lia. rewrite S3, S2. cbn [le_value].
  rewrite Int.shl_mul_two_p.
  change (two_p (Int.unsigned (Int.repr 16))) with 65536.
  rewrite mul_repr, add_repr. f_equal. f_equal. lia.
Qed.

Lemma body_MEM_readLE32: semax_body Vprog Gprog f_MEM_readLE32 MEM_readLE32_spec.
Proof.
  start_function.
  forward_call tt.
  forward_if.
  - forward_call (sh, p, bs, i). forward.
  - discriminate.
Qed.

Lemma body_MEM_writeLE32: semax_body Vprog Gprog f_MEM_writeLE32 MEM_writeLE32_spec.
Proof.
  start_function.
  forward_call tt.
  forward_if.
  - forward_call (sh, p, c, i, v). entailer!.
  - discriminate.
Qed.

Lemma body_MEM_readLE64: semax_body Vprog Gprog f_MEM_readLE64 MEM_readLE64_spec.
Proof.
  start_function.
  forward_call tt.
  forward_if.
  - forward_call (sh, p, bs, i). forward.
  - discriminate.
Qed.

Lemma body_MEM_readLEST: semax_body Vprog Gprog f_MEM_readLEST MEM_readLEST_spec.
Proof.
  start_function.
  forward_call tt.
  forward_if.
  - contradiction.
  - forward_call (sh, p, bs, i). forward.
Qed.

Lemma bodies_util_mem :
  semax_body Vprog Gprog f_MEM_32bits MEM_32bits_spec /\
  semax_body Vprog Gprog f_MEM_64bits MEM_64bits_spec /\
  semax_body Vprog Gprog f_MEM_isLittleEndian MEM_isLittleEndian_spec /\
  semax_body Vprog Gprog f_MEM_read16 MEM_read16_spec /\
  semax_body Vprog Gprog f_MEM_read32 MEM_read32_spec /\
  semax_body Vprog Gprog f_MEM_read64 MEM_read64_spec /\
  semax_body Vprog Gprog f_MEM_write16 MEM_write16_spec /\
  semax_body Vprog Gprog f_MEM_write32 MEM_write32_spec /\
  semax_body Vprog Gprog f_MEM_swap32_fallback MEM_swap32_fallback_spec /\
  semax_body Vprog Gprog f_MEM_swap32 MEM_swap32_spec /\
  semax_body Vprog Gprog f_MEM_swap64_fallback MEM_swap64_fallback_spec /\
  semax_body Vprog Gprog f_MEM_swap64 MEM_swap64_spec /\
  semax_body Vprog Gprog f_MEM_readLE16 MEM_readLE16_spec /\
  semax_body Vprog Gprog f_MEM_readLE24 MEM_readLE24_spec /\
  semax_body Vprog Gprog f_MEM_readLE32 MEM_readLE32_spec /\
  semax_body Vprog Gprog f_MEM_writeLE32 MEM_writeLE32_spec /\
  semax_body Vprog Gprog f_MEM_readLE64 MEM_readLE64_spec /\
  semax_body Vprog Gprog f_MEM_readLEST MEM_readLEST_spec.
Proof.
  exact (conj body_MEM_32bits (conj body_MEM_64bits (conj body_MEM_isLittleEndian (conj body_MEM_read16 (conj body_MEM_read32 (conj body_MEM_read64 (conj body_MEM_write16 (conj body_MEM_write32 (conj body_MEM_swap32_fallback (conj body_MEM_swap32 (conj body_MEM_swap64_fallback (conj body_MEM_swap64 (conj body_MEM_readLE16 (conj body_MEM_readLE24 (conj body_MEM_readLE32 (conj body_MEM_writeLE32 (conj body_MEM_readLE64 (body_MEM_readLEST)))))))))))))))))).
Qed.
