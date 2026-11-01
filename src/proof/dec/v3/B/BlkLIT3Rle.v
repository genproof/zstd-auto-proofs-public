(* ZSTD_decodeLiteralsBlock, the arm set_rle of its switch (one byte repeated litSize times), and the default arm
   after it; exactly as model/ExBlock.v (BlkLIT3Exact.lx_rle). *)
Require Export Zstd.proof.dec.v3.B.BlkLIT3Exact.
Local Open Scope logic.


(* ---------- set_rle (case 1) ---------- *)

(* the statement of case 1, and the default case after it *)
Definition lit_c1 : statement :=
  match lit_sw with LScons _ _ (LScons _ _ (LScons _ _ (LScons _ c _))) => c | _ => Sskip end.
Definition lit_cd : statement :=
  match lit_sw with LScons _ _ (LScons _ _ (LScons _ _ (LScons _ _ (LScons _ c _)))) => c | _ => Sskip end.

Lemma lit_sw1 : seq_of_labeled_statement (select_switch 1 lit_sw) = Ssequence lit_c1 (Ssequence lit_cd Sskip).
Proof. reflexivity. Qed.

Lemma lit_dl_rle (oh: option huf_table) (s: list Z) (bsm: Z) :
  2 <= Zlength s -> Z.land (byte_at s 0) 3 = 1 ->
  decode_literals oh s bsm =
    if andb (rle_lhl s =? 1) (Zlength s <? 3) then None else
    if andb (rle_lhl s =? 3) (Zlength s <? 4) then None else
    if rle_ls s >? bsm then None else
    Some (repeat (byte_at s (rle_lh s)) (Z.to_nat (rle_ls s)), rle_lh s + 1, oh).
Proof.
  intros Hn Hk. unfold decode_literals. rewrite (proj2 (Z.ltb_ge _ _) Hn), Hk. simpl.
  unfold rle_lh, rle_ls. fold (rle_lhl s).
  destruct (rle_lhl s =? 1); [reflexivity |]. destruct (rle_lhl s =? 3); reflexivity.
Qed.

Lemma lit_lhl (b: Z) : 0 <= b < 256 ->
  Int.and (Int.shr (Int.repr b) (Int.repr 2)) (Int.repr 3) = Int.repr (Z.land (Z.shiftr b 2) 3).
Proof.
  intros Hb. unfold Int.and, Int.shr.
  assert (E: 0 <= Z.shiftr b 2 < 256)
    by (rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 2) with 4; split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  rewrite (Int.signed_repr b), (Int.unsigned_repr 2) by rep_lia.
  rewrite (Int.unsigned_repr (Z.shiftr b 2)), (Int.unsigned_repr 3) by rep_lia. reflexivity.
Qed.

Lemma lit_shiftr_le (x k: Z) : 0 <= x -> 0 <= k -> 0 <= Z.shiftr x k <= x.
Proof.
  intros Hx Hk. rewrite Z.shiftr_div_pow2 by lia.
  assert (H: 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  split; [apply Z.div_pos; lia |]. apply Z.div_le_upper_bound; [lia |].
  assert (1 <= 2 ^ k) by lia. nia.
Qed.

Lemma lit_shr_s (x k: Z) : 0 <= x <= Int.max_signed -> 0 <= k < 32 ->
  Int.signed (Int.shr (Int.repr x) (Int.repr k)) = Z.shiftr x k.
Proof.
  intros Hx Hk. pose proof (lit_shiftr_le x k ltac:(lia) ltac:(lia)).
  unfold Int.shr. rewrite (Int.signed_repr x), (Int.unsigned_repr k) by rep_lia.
  apply Int.signed_repr. rep_lia.
Qed.

Lemma lit_shru_u (x k: Z) : 0 <= x <= Int.max_unsigned -> 0 <= k < 32 ->
  Int.unsigned (Int.shru (Int.repr x) (Int.repr k)) = Z.shiftr x k.
Proof.
  intros Hx Hk. pose proof (lit_shiftr_le x k ltac:(lia) ltac:(lia)).
  unfold Int.shru. rewrite (Int.unsigned_repr x), (Int.unsigned_repr k) by rep_lia.
  apply Int.unsigned_repr. rep_lia.
Qed.

Lemma lit_le_range (s: list Z) (k: nat) : bytes_ok s -> 0 <= le_value (firstn k s) < 2 ^ (8 * Z.of_nat k).
Proof.
  revert k. induction s as [| a s IH]; intros k Hb.
  - rewrite firstn_nil. simpl. split; [lia | apply Z.pow_pos_nonneg; lia].
  - destruct k as [| k]; [simpl; lia |].
    inversion Hb as [| ? ? Ha Hs]; subst. unfold is_byte in Ha.
    specialize (IH k Hs). cbn [firstn le_value].
    rewrite Nat2Z.inj_succ, Z.mul_succ_r, Z.pow_add_r by lia. change (2 ^ 8) with 256. nia.
Qed.

Lemma lit_le2 (s: list Z) : bytes_ok s -> 0 <= le_field s 0 2 < 2 ^ 16.
Proof. intros Hb. apply (lit_le_range s 2 Hb). Qed.

Lemma lit_le3 (s: list Z) : bytes_ok s -> 0 <= le_field s 0 3 < 2 ^ 24.
Proof. intros Hb. apply (lit_le_range s 3 Hb). Qed.

(* the input array around the window s at off *)
Lemma lit_win_split (sh: share) (c: list val) (b: val) (off: Z) (s: list Z) :
  0 <= off -> off + Zlength s <= Zlength c -> sublist off (off + Zlength s) c = zbytes s ->
  field_compatible (tarray tuchar (Zlength c)) [] b ->
  data_at sh (tarray tuchar (Zlength c)) c b =
  data_at sh (tarray tuchar off) (sublist 0 off c) b *
  data_at sh (tarray tuchar (Zlength s)) (zbytes s) (offset_val off b) *
  data_at sh (tarray tuchar (Zlength c - (off + Zlength s))) (sublist (off + Zlength s) (Zlength c) c)
    (offset_val (off + Zlength s) b).
Proof.
  intros Ho Hn Hw Hf. pose proof (Zlength_nonneg s).
  rewrite (split3_data_at_Tarray_tuchar sh (Zlength c) off (off + Zlength s) c b) by lia.
  replace (off + Zlength s - off) with (Zlength s) by lia. rewrite Hw.
  rewrite !field_address0_offset.
  - simpl. rewrite !Z.add_0_l, !Z.mul_1_l. reflexivity.
  - apply field_compatible0_cons. split; [simpl; lia | exact Hf].
  - apply field_compatible0_cons. split; [simpl; lia | exact Hf].
Qed.

(* dst == NULL is defined: dst is weakly valid (in the output array, or the witness when cap = 0) *)
Local Transparent denote_tc_test_eq.
Lemma lit_tc_null (q: val) (P: mpred) :
  isptr q -> (P |-- weak_valid_pointer q) -> P |-- denote_tc_test_eq q (Vlong (Int64.repr 0)).
Proof.
  intros Hq H. destruct q; try contradiction. unfold denote_tc_test_eq; simpl.
  apply andp_right; [apply prop_right; reflexivity | exact H].
Qed.
Local Opaque denote_tc_test_eq.

Lemma lit_dat_wvp (sh: share) (oc: list val) (ob: val) (d: Z) :
  readable_share sh -> 0 <= d < Zlength oc ->
  data_at sh (tarray tuchar (Zlength oc)) oc ob |-- weak_valid_pointer (offset_val d ob).
Proof.
  intros Hsh Hd. eapply derives_trans; [apply data_at_memory_block |].
  eapply derives_trans; [apply (memory_block_valid_pointer sh _ ob d) | apply valid_pointer_weak].
  - simpl sizeof. rewrite Z.max_r by lia. lia.
  - apply readable_nonidentity; auto.
Qed.

Ltac lit_wvp_pick H :=
  first [ exact H
        | apply sepcon_weak_valid_pointer2; lit_wvp_pick H
        | apply sepcon_weak_valid_pointer1; lit_wvp_pick H ].

(* litExtraBuffer: its first k cells as a memory block, and back *)
Lemma lit_extra_split (p: val) (k: Z) :
  0 <= k <= LITEXTRA_N ->
  field_at_ Ews t_dctx (DOT _litExtraBuffer) p |--
  !! field_compatible (tarray tuchar LITEXTRA_N) [] (lit_extra p) &&
  (memory_block Ews k (lit_extra p) *
   data_at Ews (tarray tuchar (LITEXTRA_N - k)) (Zrepeat Vundef (LITEXTRA_N - k)) (offset_val k (lit_extra p))).
Proof.
  intros Hk. rewrite field_at__data_at_. fold (lit_extra p).
  change (nested_field_type t_dctx (DOT _litExtraBuffer)) with (tarray tuchar LITEXTRA_N).
  assert_PROP (field_compatible (tarray tuchar LITEXTRA_N) [] (lit_extra p)) as Hf by entailer!.
  apply andp_right; [apply prop_right; exact Hf |].
  change (data_at_ Ews (tarray tuchar LITEXTRA_N) (lit_extra p))
    with (data_at Ews (tarray tuchar LITEXTRA_N) (Zrepeat Vundef LITEXTRA_N) (lit_extra p)).
  assert (HN: Zlength (Zrepeat Vundef LITEXTRA_N) = LITEXTRA_N)
    by (apply Zlength_Zrepeat; unfold LITEXTRA_N, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH; lia).
  assert (Hpe: isptr (offset_val LITEXTRA_N (lit_extra p)))
    by (destruct Hf as [Hp _]; destruct (lit_extra p); try contradiction; exact I).
  rewrite (lit_arr_split3 Ews LITEXTRA_N (Zrepeat Vundef LITEXTRA_N) (lit_extra p) k LITEXTRA_N Hk
             (Z.le_refl _) HN Hf).
  rewrite !sublist_Zrepeat by lia.
  replace (k - 0) with k by lia. replace (LITEXTRA_N - LITEXTRA_N) with 0 by lia.
  sep_apply (data_at_memory_block Ews (tarray tuchar k) (Zrepeat Vundef k) (lit_extra p)).
  simpl sizeof. rewrite Z.max_r by lia. rewrite Z.mul_1_l.
  rewrite (data_at_zero_array_eq Ews tuchar (Zrepeat Vundef 0)) by (first [reflexivity | exact Hpe]).
  cancel.
Qed.

Lemma lit_extra_join (p: val) (k: Z) (x: list val) :
  0 <= k <= LITEXTRA_N -> Zlength x = k -> field_compatible (tarray tuchar LITEXTRA_N) [] (lit_extra p) ->
  data_at Ews (tarray tuchar k) x (lit_extra p) *
  data_at Ews (tarray tuchar (LITEXTRA_N - k)) (Zrepeat Vundef (LITEXTRA_N - k)) (offset_val k (lit_extra p))
  |-- field_at Ews t_dctx (DOT _litExtraBuffer) (x ++ Zrepeat Vundef (LITEXTRA_N - k)) p.
Proof.
  intros Hk Hx Hf. rewrite field_at_data_at. fold (lit_extra p).
  change (nested_field_type t_dctx (DOT _litExtraBuffer)) with (tarray tuchar LITEXTRA_N).
  assert (HN: Zlength (x ++ Zrepeat Vundef (LITEXTRA_N - k)) = LITEXTRA_N)
    by (rewrite Zlength_app, Zlength_Zrepeat by lia; lia).
  assert (Hp: isptr (lit_extra p)) by (destruct Hf as [Hp _]; exact Hp).
  assert (H0: 0 <= 0 <= k) by lia.
  rewrite (lit_arr_split3 Ews LITEXTRA_N (x ++ Zrepeat Vundef (LITEXTRA_N - k)) (lit_extra p) 0 k H0
             ltac:(lia) HN Hf).
  replace (sublist 0 k (x ++ Zrepeat Vundef (LITEXTRA_N - k))) with x by list_solve.
  replace (sublist k LITEXTRA_N (x ++ Zrepeat Vundef (LITEXTRA_N - k))) with (Zrepeat Vundef (LITEXTRA_N - k))
    by list_solve.
  replace (k - 0) with k by lia. rewrite isptr_offset_val_zero by exact Hp.
  rewrite (data_at_zero_array_eq Ews tuchar (sublist 0 0 (x ++ Zrepeat Vundef (LITEXTRA_N - k))))
    by (first [reflexivity | exact Hp]).
  cancel.
Qed.

Lemma lit_loc_range (streaming cap bsm n: Z) : 0 <= alloc_loc streaming cap bsm n <= 2.
Proof.
  unfold alloc_loc, LOC_IN_DST, LOC_NOT_IN_DST, LOC_SPLIT.
  destruct (andb _ _); [lia |]. destruct (n <=? LITBUFFEREXTRASIZE); lia.
Qed.

(* the literals' bytes *)
Lemma lit_rep_bytes (v n: Z) : zbytes (repeat v (Z.to_nat n)) = Zrepeat (Vint (Int.repr v)) n.
Proof. apply map_repeat. Qed.

Lemma lit_lhl_range (s: list Z) : 0 <= rle_lhl s <= 3.
Proof.
  unfold rle_lhl. set (x := Z.shiftr (byte_at s 0) 2).
  change (Z.land x 3) with (Z.land x (Z.ones 2)). rewrite Z.land_ones by lia.
  pose proof (Z.mod_pos_bound x (2 ^ 2) ltac:(reflexivity)).
  change (2 ^ 2) with 4 in *. lia.
Qed.

(* litExtraBuffer holding bytes l: its first k cells as a memory block, the rest kept *)
Lemma lit_xb_split (p: val) (l: list val) (k: Z) :
  0 <= k <= LITEXTRA_N ->
  field_at Ews t_dctx (DOT _litExtraBuffer) l p |--
  !! (field_compatible (tarray tuchar LITEXTRA_N) [] (lit_extra p) /\ Zlength l = LITEXTRA_N) &&
  (memory_block Ews k (lit_extra p) *
   data_at Ews (tarray tuchar (LITEXTRA_N - k)) (sublist k LITEXTRA_N l) (offset_val k (lit_extra p))).
Proof.
  intros Hk. rewrite field_at_data_at. fold (lit_extra p).
  change (nested_field_type t_dctx (DOT _litExtraBuffer)) with (tarray tuchar LITEXTRA_N).
  assert_PROP (field_compatible (tarray tuchar LITEXTRA_N) [] (lit_extra p)) as Hf by entailer!.
  assert_PROP (Zlength l = LITEXTRA_N) as HN.
  { entailer!; unfold LITEXTRA_N, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *; list_solve. }
  apply andp_right; [apply prop_right; split; [exact Hf | exact HN] |].
  assert (Hpe: isptr (offset_val LITEXTRA_N (lit_extra p)))
    by (destruct Hf as [Hp _]; destruct (lit_extra p); try contradiction; exact I).
  rewrite (lit_arr_split3 Ews LITEXTRA_N l (lit_extra p) k LITEXTRA_N Hk (Z.le_refl _) HN Hf).
  replace (k - 0) with k by lia. replace (LITEXTRA_N - LITEXTRA_N) with 0 by lia.
  sep_apply (data_at_memory_block Ews (tarray tuchar k) (sublist 0 k l) (lit_extra p)).
  simpl sizeof. rewrite Z.max_r by lia. rewrite Z.mul_1_l.
  rewrite (data_at_zero_array_eq Ews tuchar (sublist LITEXTRA_N LITEXTRA_N l))
    by (first [reflexivity | exact Hpe | list_solve]).
  cancel.
Qed.

Lemma lit_xb_join (p: val) (k: Z) (x rest: list val) :
  0 <= k <= LITEXTRA_N -> Zlength x = k -> Zlength rest = LITEXTRA_N - k ->
  field_compatible (tarray tuchar LITEXTRA_N) [] (lit_extra p) ->
  data_at Ews (tarray tuchar k) x (lit_extra p) *
  data_at Ews (tarray tuchar (LITEXTRA_N - k)) rest (offset_val k (lit_extra p))
  |-- field_at Ews t_dctx (DOT _litExtraBuffer) (x ++ rest) p.
Proof.
  intros Hk Hx Hr Hf. rewrite field_at_data_at. fold (lit_extra p).
  change (nested_field_type t_dctx (DOT _litExtraBuffer)) with (tarray tuchar LITEXTRA_N).
  assert (HN: Zlength (x ++ rest) = LITEXTRA_N) by (rewrite Zlength_app; lia).
  assert (Hp: isptr (lit_extra p)) by (destruct Hf as [Hp _]; exact Hp).
  assert (H0: 0 <= 0 <= k) by lia.
  rewrite (lit_arr_split3 Ews LITEXTRA_N (x ++ rest) (lit_extra p) 0 k H0 ltac:(lia) HN Hf).
  replace (sublist 0 k (x ++ rest)) with x by list_solve.
  replace (sublist k LITEXTRA_N (x ++ rest)) with rest by list_solve.
  replace (k - 0) with k by lia. rewrite isptr_offset_val_zero by exact Hp.
  rewrite (data_at_zero_array_eq Ews tuchar (sublist 0 0 (x ++ rest)))
    by (first [reflexivity | exact Hp | list_solve]).
  cancel.
Qed.

Lemma lit_xb_fold (p: val) (l: list val) :
  byte_cells l -> field_at Ews t_dctx (DOT _litExtraBuffer) l p |-- lit_extra_bytes p.
Proof. intros H. unfold lit_extra_bytes. Exists l. entailer!. Qed.

(* the output array after memset of v over n cells from k, as the exact lemmas state it (cwr) *)
Lemma rle_cwr (c: list val) (k v n N: Z) :
  Zlength c = N -> 0 <= n ->
  cwr c k (zbytes (repeat v (Z.to_nat n))) = sublist 0 k c ++ Zrepeat (Vint (Int.repr v)) n ++ sublist (k + n) N c.
Proof. intros Hc Hn. unfold cwr. rewrite lit_rep_bytes, Zlength_Zrepeat by lia. subst N. reflexivity. Qed.

(* litExtraBuffer after memset of v over its first k cells *)
Lemma rle_xb (v k: Z) (lxb: list Z) :
  0 <= v < 256 -> 0 <= k <= LITEXTRA_N -> Zlength lxb = LITEXTRA_N -> bytes_ok lxb ->
  Zlength (repeat v (Z.to_nat k) ++ sublist k LITEXTRA_N lxb) = LITEXTRA_N /\
  bytes_ok (repeat v (Z.to_nat k) ++ sublist k LITEXTRA_N lxb) /\
  sublist 0 k (repeat v (Z.to_nat k) ++ sublist k LITEXTRA_N lxb) = repeat v (Z.to_nat k) /\
  zbytes (repeat v (Z.to_nat k) ++ sublist k LITEXTRA_N lxb) =
    Zrepeat (Vint (Int.repr v)) k ++ sublist k LITEXTRA_N (zbytes lxb).
Proof.
  intros Hv Hk Hl Hb. assert (Hr: Zlength (repeat v (Z.to_nat k)) = k) by (rewrite Zlength_repeat; lia).
  split; [rewrite Zlength_app, Zlength_sublist by lia; lia |].
  split; [apply Forall_app; split; [apply Forall_repeat; unfold is_byte; lia | apply Forall_sublist; exact Hb] |].
  split; [rewrite sublist_app1 by lia; apply sublist_same; lia |].
  rewrite map_app, lit_rep_bytes, sublist_map. reflexivity.
Qed.

(* set_rle (case 1) *)
Lemma seg_rle : lit_seg 1 1 (fun _ => True).
Proof.
  unfold lit_seg. intros Espec gv p fs ox oh x2 lxb bsm streaming W o i R HY Hk _ HR.
  apply semax_post with (R' := switch_ret_assert (overridePost FF (lit_R gv p fs ox oh x2 lxb bsm streaming W o i))).
  1-3: destruct R; unfold lit_R; simpl; intros; apply andp_left2; normalize.
  { intros vl. destruct R as [Rn Rb Rc Rr]. cbn [RA_return] in HR |- *. subst Rr.
    unfold switch_ret_assert, overridePost. destruct (lit_R gv p fs ox oh x2 lxb bsm streaming W o i). apply andp_left2. cbn [tycontext.RA_return]. apply derives_refl. }
  clear R HR.
  assert_PROP (Zlength lxb = LITEXTRA_N /\ bytes_ok lxb) as Hlx.
  { unfold lit_S, lit_L, lit_scratch_x, lit_extra_at. Intros. apply prop_right. auto. }
  destruct Hlx as [Hlxb Hlxbb].
  assert (LXH: lx_hyps o i bsm streaming lxb).
  { destruct HY as (A1 & A2 & A3 & A4 & A5 & _). exact (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 Hlxb))))). }
  destruct o as [osh ob oN oc d cap]; destruct i as [ish ib iN ic ioff s].
  unfold lit_hyps, outarr_ok, inwin_ok, win_ok in HY.
  cbn [oa_sh oa_base oa_N oa_c oa_d oa_cap iw_sh iw_base iw_N iw_c iw_off iw_s] in *.
  destruct HY as ((Hosh & HoN & HoN32 & Hd & Hcap & Hdc) & (Hish & Hioff & Hin & HiN32 & HiN & _ & Hbytes & Hwin) &
    Hstr & Hbsm0 & Hsb & Hfp & Hfd & Hcold & Hwv & Hhuf & Hs2).
  subst iN oN.
  assert (Hbsm: 0 <= bsm <= 131072) by (unfold ZSTD_BLOCKSIZE_MAX in Hbsm0; lia).
  unfold lit_R, lit_post.
  unfold lit_L, lit_S. change (Int.unsigned (Int.repr 1)) with 1. rewrite lit_sw1.
  apply semax_seq with (Q := FF); [| apply semax_ff].
  cbv [lit_c1 lit_sw f_ZSTD_decodeLiteralsBlock fn_body].
  cbn [oa_sh oa_base oa_N oa_c oa_d oa_cap iw_sh iw_base iw_N iw_c iw_off iw_s].
  abbreviate_semax.
  assert_PROP (force_val (sem_add_ptr_int tuchar Signed (offset_val ioff ib) (Vint (Int.repr 0))) =
               field_address (tarray tuchar (Zlength ic)) [ArraySubsc ioff] ib) as FA0.
  { entailer!. rewrite lit_fa by (auto; lia). reflexivity. }
  assert (B0: @Znth val Vundef ioff ic = Vint (Int.repr (byte_at s 0))).
  { rewrite <- (Z.add_0_r ioff) at 1. apply lit_win_byte; auto; lia. }
  pose proof (lit_byte_range s 0 Hbytes) as R0.
  forward.
  { entailer!. rewrite B0. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
  rewrite B0.
  forward.
  forward_if (temp _t'36 (Vlong (Int64.repr (Z.min bsm cap)))).
  { forward. entailer!. rewrite Z.min_l by lia. reflexivity. }
  { forward. entailer!. rewrite Z.min_r by lia. reflexivity. }
  forward.
  rewrite lit_lhl by lia. fold (rle_lhl s).
  pose proof (lit_lhl_range s) as Hl.
  forward_if (PROP ((rle_lhl s = 1 -> 3 <= Zlength s); (rle_lhl s = 3 -> 4 <= Zlength s); 0 <= rle_ls s < 2 ^ 20)
    LOCAL (temp _lhSize__2 (Vlong (Int64.repr (rle_lh s))); temp _litSize__2 (Vlong (Int64.repr (rle_ls s)));
      temp _expectedWriteSize__2 (Vlong (Int64.repr (Z.min bsm cap)));
      temp _blockSizeMax (Vlong (Int64.repr bsm)); temp _istart (offset_val ioff ib);
      gvars gv; temp _dctx p; temp _srcSize (Vlong (Int64.repr (Zlength s)));
      temp _dst (offset_val d ob); temp _dstCapacity (Vlong (Int64.repr cap));
      temp _streaming (Vint (Int.repr streaming)))
    SEP (frame_fields p fs; zstd_globals gv; pws_pred W; cfg_lit p; tabs_huf gv p ox oh x2; dent_of dent_def gv ox;
      field_at_ Ews t_dctx (DOT _workspace) p; lit_scratch_x p lxb;
      data_at osh (tarray tuchar (Zlength oc)) oc ob; data_at ish (tarray tuchar (Zlength ic)) ic ib)).
  - (* 0 *) abbreviate_semax. forward. forward.
    { entailer!. rewrite B0. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    rewrite B0. forward. forward. entailer!.
    unfold rle_lh, rle_ls. rewrite E. simpl. rewrite lit_shr_s by rep_lia.
    pose proof (lit_shiftr_le (byte_at s 0) 3 ltac:(lia) ltac:(lia)). split; [lia | auto].
  - (* 2 *) abbreviate_semax. forward. forward.
    { entailer!. rewrite B0. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    rewrite B0. forward. forward. entailer!.
    unfold rle_lh, rle_ls. rewrite E. simpl. rewrite lit_shr_s by rep_lia.
    pose proof (lit_shiftr_le (byte_at s 0) 3 ltac:(lia) ltac:(lia)). split; [lia | auto].
  - (* 1 *) abbreviate_semax. forward.
    lit_check (3 <= Zlength s).
    { entailer!. }
    { forward_if.
      - lit_errpath. lit_err 20 oc oh x2 lxb.
        rewrite lit_dl_rle by auto. rewrite E. rewrite !Int64.unsigned_repr in H by rep_lia.
        rewrite (proj2 (Z.ltb_lt (Zlength s) 3)) by lia. simpl. auto.
        cbn [iw_s oa_cap]. rewrite xl_rle by auto. rewrite E. rewrite !Int64.unsigned_repr in H by rep_lia.
        rewrite (proj2 (Z.ltb_lt (Zlength s) 3)) by lia. reflexivity.
      - forward. entailer!. rewrite !Int64.unsigned_repr in H by rep_lia. lia. }
    Intros.
    assert_PROP (field_compatible (tarray tuchar (Zlength ic)) [] ib) as FCi by entailer!.
    rewrite (lit_win_split ish ic ib ioff s) by auto. Intros.
    forward_call (ish, offset_val ioff ib, s, 0).
    { split; [exact Hish | split; [lia | split; [lia |]]]. apply Forall_sublist. exact Hbytes. }
    pose proof (lit_le2 s Hbytes) as L2.
    forward. forward. entailer!.
    2: rewrite (lit_win_split ish ic ib ioff s) by auto; cancel.
    unfold rle_lh, rle_ls. rewrite E. simpl. rewrite lit_shr_s by rep_lia.
    pose proof (lit_shiftr_le (le_field s 0 2) 4 ltac:(lia) ltac:(lia)). split; [lia | auto].
  - (* 3 *) abbreviate_semax. forward.
    lit_check (4 <= Zlength s).
    { entailer!. }
    { forward_if.
      - lit_errpath. lit_err 20 oc oh x2 lxb.
        rewrite lit_dl_rle by auto. rewrite E. rewrite !Int64.unsigned_repr in H by rep_lia.
        rewrite (proj2 (Z.ltb_lt (Zlength s) 4)) by lia. simpl. auto.
        cbn [iw_s oa_cap]. rewrite xl_rle by auto. rewrite E. rewrite !Int64.unsigned_repr in H by rep_lia.
        rewrite (proj2 (Z.ltb_lt (Zlength s) 4)) by lia. reflexivity.
      - forward. entailer!. rewrite !Int64.unsigned_repr in H by rep_lia. lia. }
    Intros.
    assert_PROP (field_compatible (tarray tuchar (Zlength ic)) [] ib) as FCi by entailer!.
    rewrite (lit_win_split ish ic ib ioff s) by auto. Intros.
    forward_call (ish, offset_val ioff ib, s, 0).
    { split; [exact Hish | split; [lia | split; [lia |]]]. apply Forall_sublist. exact Hbytes. }
    pose proof (lit_le3 s Hbytes) as L3.
    forward. forward. entailer!.
    2: rewrite (lit_win_split ish ic ib ioff s) by auto; cancel.
    pose proof L3 as L3'. change (2 ^ 24) with 16777216 in L3'.
    unfold rle_lh, rle_ls. rewrite E. simpl. rewrite lit_shru_u by rep_lia.
    rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
    assert (Q1: le_field s 0 3 / 16 < 1048576) by (apply Z.div_lt_upper_bound; lia).
    assert (Q2: 0 <= le_field s 0 3 / 16) by (apply Z.div_pos; lia).
    split; [change (2 ^ 20) with 1048576; lia | auto].
  - (* default: impossible *) exfalso.
    repeat match goal with H: Int.unsigned _ <> Int.unsigned _ |- _ => rewrite !Int.unsigned_repr in H by rep_lia end.
    lia.
  - Intros.
    match goal with H: rle_lhl s = 1 -> _ |- _ => rename H into Hl1 end.
    match goal with H: rle_lhl s = 3 -> _ |- _ => rename H into Hl3 end.
    match goal with H: 0 <= rle_ls s < _ |- _ => rename H into Hls end.
    change (2 ^ 20) with 1048576 in Hls.
    (* litSize > 0 && dst == NULL *)
    assert_PROP (field_compatible (tarray tuchar (Zlength oc)) [] ob) as FCo by entailer!.
    assert (Hob: isptr ob) by (destruct FCo; auto).
    lit_check True.
    { entailer!. }
    { forward_if (temp _t'39 (Vint (Int.repr 0))).
      - forward.
        + entailer!. apply lit_tc_null; [destruct ob; try contradiction; exact I |].
          destruct (Z.eq_dec cap 0) as [Hc0 | Hc0].
          * specialize (Hwv Hc0). lit_wvp_pick Hwv.
          * assert (Hv: data_at osh (tarray tuchar (Zlength oc)) oc ob |-- weak_valid_pointer (offset_val d ob))
              by (apply lit_dat_wvp; [auto | lia]).
            lit_wvp_pick Hv.
        + entailer!. destruct ob; try contradiction. reflexivity.
      - forward. entailer!.
      - forward_if; [contradiction | forward; entailer!]. }
    Intros.
    (* litSize > blockSizeMax *)
    lit_check (rle_ls s <= bsm).
    { entailer!. }
    { forward_if.
      - lit_errpath. lit_err 20 oc oh x2 lxb.
        rewrite lit_dl_rle by auto. try rewrite !Int64.unsigned_repr in H by rep_lia.
        rewrite (proj2 (Z.gtb_lt (rle_ls s) bsm)) by lia.
        destruct (andb _ _); [auto |]. destruct (andb _ _); auto.
        cbn [iw_s oa_cap]. rewrite xl_rle by auto. try rewrite !Int64.unsigned_repr in H by rep_lia.
        rewrite (proj2 (Z.gtb_lt (rle_ls s) bsm)) by lia.
        destruct (andb _ _); [reflexivity |]. destruct (andb _ _); reflexivity.
      - forward. entailer!; try (rewrite !Int64.unsigned_repr in H by rep_lia); lia. }
    Intros.
    (* expectedWriteSize < litSize *)
    lit_check (rle_ls s <= Z.min bsm cap).
    { entailer!. }
    { forward_if.
      - lit_errpath. lit_err 70 oc oh x2 lxb.
        rewrite lit_dl_rle by auto. try rewrite !Int64.unsigned_repr in H by rep_lia.
        rewrite Z.gtb_ltb, (proj2 (Z.ltb_ge bsm (rle_ls s))) by lia.
        destruct (andb _ _); [auto |]. destruct (andb _ _); [auto |].
        right. rewrite Zlength_repeat by lia. rewrite Z.min_comm. lia.
        cbn [iw_s oa_cap]. rewrite xl_rle by auto. try rewrite !Int64.unsigned_repr in H by rep_lia.
        rewrite Z.gtb_ltb, (proj2 (Z.ltb_ge bsm (rle_ls s))) by lia.
        rewrite (proj2 (Z.ltb_lt (Z.min bsm cap) (rle_ls s))) by lia.
        destruct (andb _ _); [reflexivity |]. destruct (andb _ _); reflexivity.
      - forward. entailer!; try (rewrite !Int64.unsigned_repr in H by rep_lia); lia. }
    Intros.
    unfold lit_scratch_x, lit_extra_at. Intros.
    set (xl := zbytes lxb) in *.
    assert (XB: byte_cells xl) by (apply litc_bc_zbytes; exact Hlxbb).
    forward_call (p, fs, bsm, ob, d, cap, rle_ls s, streaming, 1, osh, oc).
    destruct (lit_alloc_out oc streaming cap bsm (rle_ls s) d 1 ltac:(lia) ltac:(lia) ltac:(lia))
      as (AL & AU & AUs & AB & AD & AS1 & AS2 & AE).
    pose proof (lx_rle (option_map (xhuf_of x2) oh) lxb _ _ bsm streaming LXH Hs2 Hk
                  ltac:(cbn; intros [E1 E2]; specialize (Hl1 E1); lia)
                  ltac:(cbn; intros [E1 E2]; specialize (Hl3 E1); lia) ltac:(cbn; lia) ltac:(cbn; lia)) as LXE.
    cbn [oa_c oa_cap oa_d iw_s iw_off] in LXE.
    set (oc1 := alloc_out oc streaming cap bsm (rle_ls s) d (Z.min bsm cap) 1) in *. clearbody oc1.
    assert_PROP (field_compatible t_dctx (DOT _litBuffer) p) as FCp by entailer!.
    assert (Hlh: 1 <= rle_lh s < Zlength s).
    { unfold rle_lh. destruct (rle_lhl s =? 1) eqn:E1; [apply Z.eqb_eq in E1; specialize (Hl1 E1); lia |].
      destruct (rle_lhl s =? 3) eqn:E3; [apply Z.eqb_eq in E3; specialize (Hl3 E3); lia | lia]. }
    assert (BL: @Znth val Vundef (ioff + rle_lh s) ic = Vint (Int.repr (byte_at s (rle_lh s))))
      by (apply lit_win_byte; auto; lia).
    pose proof (lit_byte_range s (rle_lh s) Hbytes) as RL.
    assert_PROP (field_compatible (tarray tuchar (Zlength ic)) [] ib) as FCi by entailer!.
    assert (Hib: isptr (offset_val ioff ib)) by (destruct FCi as [Hp _]; destruct ib; try contradiction; exact I).
    assert (FAL: force_val (sem_add_ptr_long tuchar (offset_val ioff ib) (Vlong (Int64.repr (rle_lh s)))) =
                 field_address (tarray tuchar (Zlength ic)) [ArraySubsc (ioff + rle_lh s)] ib).
    { rewrite lit_fa by (auto; lia). rewrite lit_add_l by auto. rewrite offset_offset_val. reflexivity. }
    assert (DL: decode_literals oh s bsm = Some (repeat (byte_at s (rle_lh s)) (Z.to_nat (rle_ls s)), rle_lh s + 1, oh)).
    { rewrite lit_dl_rle by auto.
      assert (A1: andb (rle_lhl s =? 1) (Zlength s <? 3) = false).
      { destruct (rle_lhl s =? 1) eqn:E1; [| reflexivity]. apply Z.eqb_eq in E1. specialize (Hl1 E1).
        simpl. apply Z.ltb_ge. lia. }
      assert (A3: andb (rle_lhl s =? 3) (Zlength s <? 4) = false).
      { destruct (rle_lhl s =? 3) eqn:E3; [| reflexivity]. apply Z.eqb_eq in E3. specialize (Hl3 E3).
        simpl. apply Z.ltb_ge. lia. }
      rewrite A1, A3, Z.gtb_ltb, (proj2 (Z.ltb_ge bsm (rle_ls s))) by lia. reflexivity. }
    assert (Herr: is_error_code (rle_lh s + 1) = false) by (unfold is_error_code; apply Z.ltb_ge; lia).
    assert (ZL: Zlength (repeat (byte_at s (rle_lh s)) (Z.to_nat (rle_ls s))) = rle_ls s)
      by (apply Zlength_repeat; lia).
    assert (BO: bytes_ok (repeat (byte_at s (rle_lh s)) (Z.to_nat (rle_ls s))))
      by (apply Forall_repeat; unfold is_byte; lia).
    set (n := rle_ls s) in *. set (v := byte_at s (rle_lh s)) in *. set (ews := Z.min bsm cap) in *.
    assert (Hews: 0 <= ews <= bsm /\ ews <= cap) by (subst ews; lia).
    forward.
    apply semax_if_seq. forward_if.
    + (* split *)
      assert (HL: alloc_loc streaming cap bsm n = LOC_SPLIT).
      { pose proof (lit_loc_range streaming cap bsm n).
        match goal with H: Int.repr (alloc_loc _ _ _ _) = _ |- _ => apply repr_inj_unsigned in H end;
          [assumption | rep_lia | rep_lia]. }
      assert (Hn: LITBUFFEREXTRASIZE < n).
      { unfold alloc_loc in HL. destruct (andb _ _); [discriminate |].
        destruct (n <=? LITBUFFEREXTRASIZE) eqn:E; [discriminate | apply Z.leb_gt in E; exact E]. }
      unfold LITBUFFEREXTRASIZE in Hn.
      unfold alloc_buf; rewrite HL; simpl fst; simpl snd.
      unfold LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH.
      forward_if (temp _t'40 (Vint (Int.repr 65536))).
      { forward. entailer!. }
      { discriminate. }
      forward_if (temp _t'41 (Vint (Int.repr 65536))).
      { discriminate. }
      { forward_if (temp _t'41 (Vint (Int.repr 65536))).
        - forward. forward. entailer!.
        - discriminate. }
      forward. forward.
      { entailer!. rewrite BL. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
      rewrite BL.
      sep_apply (lit_out_split_n osh (Zlength oc) oc1 ob (d + ews - n + 65536 - 32) (n - 65536) AL); try lia; auto.
      forward_call (osh, offset_val (d + ews - n + 65536 - 32) ob, v, n - 65536).
      { cancel. }
      forward_if (temp _t'42 (Vint (Int.repr 65536))).
      { forward. entailer!. }
      { discriminate. }
      forward_if (temp _t'43 (Vint (Int.repr 65536))).
      { discriminate. }
      { forward_if (temp _t'43 (Vint (Int.repr 65536))).
        - forward. forward. entailer!.
        - discriminate. }
      forward.
      { entailer!. rewrite BL. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
      rewrite BL.
      pose (K := 65536). assert (HK: 65536 <= K <= 65536) by (subst K; lia). clearbody K.
      sep_apply (lit_xb_split p xl K ltac:(unfold LITEXTRA_N, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH; lia)).
      Intros.
      match goal with H: field_compatible (tarray tuchar LITEXTRA_N) [] (lit_extra p) |- _ =>
        rename H into FCx end.
      match goal with H: Zlength xl = LITEXTRA_N |- _ => rename H into XL end.
      forward_call (Ews, lit_extra p, v, K).
      { apply prop_right. replace K with 65536 by lia. simpl. rewrite lit_extra_eq by auto. reflexivity. }
      set (lb := d + ews - n + 65536 - 32).
      assert (J1: Zlength (Zrepeat (Vint (Int.repr v)) (n - 65536)) = n - 65536)
        by (rewrite Zlength_Zrepeat; lia).
      assert (J2: Zlength (Zrepeat (Vint (Int.repr v)) K) = K) by (rewrite Zlength_Zrepeat; lia).
      assert (J3: 0 <= K <= LITEXTRA_N) by (unfold LITEXTRA_N, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH; lia).
      sep_apply (lit_out_join_n osh (Zlength oc) oc1 ob lb (n - 65536) _ AL ltac:(subst lb; lia) J1 ltac:(subst lb; lia) FCo).
      assert (J4: Zlength (sublist K LITEXTRA_N xl) = LITEXTRA_N - K) by (rewrite Zlength_sublist by lia; lia).
      sep_apply (lit_xb_join p K _ _ J3 J2 J4 FCx).
      forward. forward. forward. forward.
      set (n := rle_ls s) in *.
      pose proof (proj2 (proj2 LXE) HL) as XE. clear LXE.
      change LITBUFFEREXTRASIZE with 65536 in XE. change WILDCOPY_OVERLENGTH with 32 in XE.
      replace (d + ews - n + 65536 - 32) with lb in XE by (unfold lb; lia).
      rewrite (rle_cwr oc1 lb v (n - 65536) (Zlength oc) AL ltac:(lia)) in XE.
      Exists (rle_lh s + 1) (sublist 0 lb oc1 ++ Zrepeat (Vint (Int.repr v)) (n - 65536) ++
                               sublist (lb + (n - 65536)) (Zlength oc) oc1)
        (LSplit lb) (repeat v (Z.to_nat n)) oh x2 (repeat v (Z.to_nat 65536) ++ sublist 65536 LITEXTRA_N lxb).
      rewrite Herr. apply andp_right.
      * apply prop_right.
        assert (Hlb: d <= lb /\ lb + (n - 65536) + 32 <= d + cap /\ lb + (n - 65536) <= d + Z.min cap bsm)
          by (assert (Ecm: Z.min cap bsm = ews) by (unfold ews; apply Z.min_comm); unfold lb; lia).
        assert (ZX: zbytes (sublist 0 (n - LITBUFFEREXTRASIZE) (repeat v (Z.to_nat n))) =
                    Zrepeat (Vint (Int.repr v)) (n - 65536)).
        { change (repeat v (Z.to_nat n)) with (Zrepeat v n). unfold LITBUFFEREXTRASIZE.
          rewrite sublist_Zrepeat by lia. rewrite map_Zrepeat. f_equal. lia. }
        split; [rep_lia |]. split; [list_solve |].
        split; [apply lit_unch_after; auto; lia |].
        split; [intros Hs1; apply lit_unch_after; auto; lia |].
        split; [| split; [rewrite DL; left; reflexivity | split; [discriminate |
          split; [intros BCO _; rewrite <- AL; apply lit_bc_mid_r; [auto | exact RL] |
          split; [intros _; apply lit_dk_after; auto; try lia; apply lit_bv_rep; exact RL | split; [intros _; exact XE | reflexivity]]]]]].
        intros _. unfold lits_ok, lits_at, lit_slack_def; cbn [oa_d oa_cap iw_s iw_c iw_N].
        rewrite ZL, DL. unfold LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *.
        split; [lia |]. split; [split; [exact BO | split; [unfold ZSTD_BLOCKSIZE_MAX; lia |]] |].
        { split; [lia | split; [lia | split; [lia |]]]. rewrite ZX. list_solve. }
        split; [lia |]. split; [exact I |]. split; [destruct oh; auto |]. split; [auto |].
        split; [unfold lit_pos; try rewrite ZL; try unfold lb; try unfold ews;
                unfold LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *; first [exact I | lia] |].
        replace (sublist (lb + (n - 65536)) (lb + (n - 65536) + 32) _)
          with (sublist (d + ews - 32) (d + ews) oc1).
        { apply AS2; auto. }
        replace (lb + (n - 65536)) with (d + ews - 32) by (unfold lb; lia).
        replace (d + ews - 32 + 32) with (d + ews) by lia.
        list_solve.
      * unfold litfields. rewrite ZL. simpl loc_code.
        replace (lb + (n - LITBUFFEREXTRASIZE)) with (d + ews - 32) by (unfold lb, LITBUFFEREXTRASIZE; lia).
        replace K with 65536 in * by lia.
        destruct (rle_xb v 65536 lxb RL ltac:(unfold LITEXTRA_N, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH; lia)
                    Hlxb Hlxbb) as (X1 & X2 & X3 & X4).
        unfold lit_extra_at. rewrite X4. subst xl.
        rewrite (prop_true_andp (Zlength _ = LITEXTRA_N /\ bytes_ok _)) by (split; [exact X1 | exact X2]).
        unfold LITBUFFEREXTRASIZE. rewrite X3.
        rewrite (prop_true_andp (repeat v (Z.to_nat 65536) = _))
          by (change (repeat v (Z.to_nat n)) with (Zrepeat v n); rewrite sublist_Zrepeat by lia; unfold Zrepeat; f_equal; f_equal; lia).
        cancel.
    + (* not split *)
      assert (HL2: alloc_loc streaming cap bsm n <> LOC_SPLIT).
      { intros E. match goal with H: Int.repr (alloc_loc _ _ _ _) <> _ |- _ => apply H; rewrite E; reflexivity end. }
      assert (Hcases: (alloc_loc streaming cap bsm n = LOC_IN_DST /\ streaming = 0 /\ bsm + 32 + n + 32 < cap) \/
                      (alloc_loc streaming cap bsm n = LOC_NOT_IN_DST /\ n <= 65536)).
      { unfold alloc_loc in *. destruct (andb (streaming =? 0) _) eqn:EA.
        - left. apply andb_prop in EA. destruct EA as [E1 E2]. apply Z.eqb_eq in E1. apply Z.ltb_lt in E2.
          unfold WILDCOPY_OVERLENGTH in E2. auto.
        - right. destruct (n <=? LITBUFFEREXTRASIZE) eqn:E; [| contradiction].
          apply Z.leb_le in E. unfold LITBUFFEREXTRASIZE in E. auto. }
      destruct Hcases as [(HL & Hs0 & Hc) | (HL & Hn)].
      * (* in dst *)
        specialize (AS1 HL).
        unfold alloc_buf; rewrite HL; simpl fst; simpl snd. unfold WILDCOPY_OVERLENGTH in *.
        forward. forward.
        { entailer!. rewrite BL. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
        rewrite BL.
        set (lb := d + bsm + 32).
        sep_apply (lit_out_split_n osh (Zlength oc) oc1 ob lb n AL ltac:(unfold lb; lia) ltac:(lia) ltac:(unfold lb; lia) FCo).
        forward_call (osh, offset_val lb ob, v, n).
        { cancel. }
        assert (J1: Zlength (Zrepeat (Vint (Int.repr v)) n) = n) by (rewrite Zlength_Zrepeat; lia).
        sep_apply (lit_out_join_n osh (Zlength oc) oc1 ob lb n _ AL ltac:(unfold lb; lia) J1 ltac:(unfold lb; lia) FCo).
        forward. forward. forward. forward.
        set (n := rle_ls s) in *.
        pose proof (proj1 LXE HL) as XE. clear LXE.
        change WILDCOPY_OVERLENGTH with 32 in XE. change (d + bsm + 32) with lb in XE.
        rewrite (rle_cwr oc1 lb v n (Zlength oc) AL ltac:(lia)) in XE.
        Exists (rle_lh s + 1) (sublist 0 lb oc1 ++ Zrepeat (Vint (Int.repr v)) n ++ sublist (lb + n) (Zlength oc) oc1)
          (LDst lb) (repeat v (Z.to_nat n)) oh x2 lxb.
        rewrite Herr. apply andp_right.
        -- apply prop_right.
           assert (Ecm: Z.min cap bsm = ews) by (unfold ews; apply Z.min_comm).
           assert (Hlb: d <= lb /\ lb + n + 32 <= d + cap) by (unfold lb; lia).
           split; [rep_lia |]. split; [list_solve |].
           split; [apply lit_unch_after; auto; lia |].
           split; [intros Hs1; lia |].
           split; [| split; [rewrite DL; left; reflexivity | split; [discriminate |
             split; [intros BCO _; rewrite <- AL; apply lit_bc_mid_r; [auto | exact RL] |
             split; [intros _; apply lit_dk_after; auto; try lia; apply lit_bv_rep; exact RL | split; [intros _; exact XE | reflexivity]]]]]].
           intros _. unfold lits_ok, lits_at, lit_slack_def; cbn [oa_d oa_cap iw_s iw_c iw_N].
           rewrite ZL, DL.
           split; [lia |]. split; [split; [exact BO | split; [unfold ZSTD_BLOCKSIZE_MAX; lia |]] |].
           { unfold WILDCOPY_OVERLENGTH. split; [lia | split; [lia |]]. rewrite lit_rep_bytes. list_solve. }
           split; [lia |]. split; [auto |]. split; [destruct oh; auto |]. split; [auto |].
           split; [unfold lit_pos; try rewrite ZL; try unfold lb; try unfold ews;
                   unfold LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *; first [exact I | lia] |].
           unfold WILDCOPY_OVERLENGTH.
           replace (sublist (lb + n) (lb + n + 32) _) with (sublist (lb + n) (lb + n + 32) oc1) by list_solve.
           exact AS1.
        -- unfold litfields, lit_extra_at. rewrite ZL. simpl loc_code. subst xl.
           rewrite (prop_true_andp (Zlength lxb = LITEXTRA_N /\ bytes_ok lxb)) by auto. cancel.
      * (* litExtraBuffer *)
        assert (E1: oc1 = oc) by (apply AE; left; exact HL). subst oc1.
        unfold alloc_buf; rewrite HL; simpl fst; simpl snd.
        rewrite (lit_extra_eq p FCp).
        forward. forward.
        { entailer!. rewrite BL. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
        rewrite BL. rewrite <- (lit_extra_eq p FCp).
        assert (J3: 0 <= n <= LITEXTRA_N) by (unfold LITEXTRA_N, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH; lia).
        sep_apply (lit_xb_split p xl n J3). Intros.
        match goal with H: field_compatible (tarray tuchar LITEXTRA_N) [] (lit_extra p) |- _ =>
          rename H into FCx end.
        match goal with H: Zlength xl = LITEXTRA_N |- _ => rename H into XL end.
        assert (J4: Zlength (sublist n LITEXTRA_N xl) = LITEXTRA_N - n) by (rewrite Zlength_sublist by lia; lia).
        forward_call (Ews, lit_extra p, v, n).
        assert (J2: Zlength (Zrepeat (Vint (Int.repr v)) n) = n) by (rewrite Zlength_Zrepeat; lia).
        sep_apply (lit_xb_join p n _ _ J3 J2 J4 FCx).
        rewrite (lit_extra_eq p FCp).
        forward. forward. forward. forward.
        rewrite <- (lit_extra_eq p FCp).
        set (n := rle_ls s) in *.
        pose proof (proj1 (proj2 LXE) HL) as XE. clear LXE.
        Exists (rle_lh s + 1) oc LExtra (repeat v (Z.to_nat n)) oh x2 (repeat v (Z.to_nat n) ++ sublist n LITEXTRA_N lxb).
        rewrite Herr. apply andp_right.
        -- apply prop_right.
           split; [rep_lia |]. split; [reflexivity |].
           split; [apply lit_unch |]. split; [intros _; apply lit_unch |].
           split; [| split; [rewrite DL; left; reflexivity | split; [discriminate |
             split; [intros BCO _; exact BCO | split; [intros _ j _ Hj; exact Hj | split; [intros _; exact XE | reflexivity]]]]]].
           intros _. unfold lits_ok, lits_at, lit_slack_def; cbn [oa_d oa_cap iw_s iw_c iw_N].
           rewrite ZL, DL. unfold LITBUFFEREXTRASIZE.
           split; [lia |]. split; [split; [exact BO | split; [unfold ZSTD_BLOCKSIZE_MAX; lia | lia]] |].
           split; [lia |]. split; [exact I |]. split; [destruct oh; auto |]. split; [auto |].
           split; exact I.
        -- destruct (rle_xb v n lxb RL J3 Hlxb Hlxbb) as (X1 & X2 & X3 & X4).
           unfold litfields, lit_extra_at. rewrite ZL. simpl loc_code. rewrite X4. subst xl.
           rewrite (prop_true_andp (Zlength _ = LITEXTRA_N /\ bytes_ok _)) by (split; [exact X1 | exact X2]).
           rewrite (prop_true_andp (sublist 0 n _ = _)) by exact X3.
           rewrite !(lit_extra_eq p FCp), ?offset_offset_val. cancel.
Qed.
