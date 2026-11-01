(* API v3, subtree B, group BLK, sub-group LIT, the common part: ZSTD_allocateLiteralsBuffer (spec and body),
   ZSTD_blockSizeMax's body, and the frame of ZSTD_decodeLiteralsBlock's proof (BSpecs3.ZSTD_decodeLiteralsBlock_spec3:
   its pre- and postcondition as lit_S / lit_post, the statement lit_seg of one arm of its switch).  The arms are
   proved in BlkLIT3Raw.v (set_basic), BlkLIT3Rle.v (set_rle) and BlkLIT3Comp.v (set_compressed / set_repeat), the
   exact outcome of each arm against model/ExBlock.v in BlkLIT3Exact.v, the function in BlkLIT3.v.  The literals
   decoder writes only defined bytes (input bytes, the RLE byte, Huffman output, the zeroed slack), so every copy
   reads defined bytes. *)
Require Export Zstd.proof.dec.v3.B.BSpecs3.
Require Export Zstd.proof.model.ExHuf Zstd.proof.model.ExBlock.
Local Open Scope logic.

(* ===================== ZSTD_allocateLiteralsBuffer ===================== *)

(* where ZSTD_allocateLiteralsBuffer puts n literals (litBufferLocation) *)
Definition alloc_loc (streaming cap bsm n: Z) : Z :=
  if andb (streaming =? 0) (bsm + WILDCOPY_OVERLENGTH + n + WILDCOPY_OVERLENGTH <? cap) then LOC_IN_DST
  else if n <=? LITBUFFEREXTRASIZE then LOC_NOT_IN_DST else LOC_SPLIT.

(* litBuffer and litBufferEnd it sets (ob: the output array's base, dst = ob + d, ews = min(bsm, cap)) *)
Definition alloc_buf (p ob: val) (streaming cap bsm n d ews split: Z) : val * val :=
  if alloc_loc streaming cap bsm n =? LOC_IN_DST then
    (offset_val (d + bsm + WILDCOPY_OVERLENGTH) ob, offset_val (d + bsm + WILDCOPY_OVERLENGTH + n) ob)
  else if alloc_loc streaming cap bsm n =? LOC_NOT_IN_DST then
    (lit_extra p, offset_val n (lit_extra p))
  else if split =? 1 then
    (offset_val (d + ews - n + LITBUFFEREXTRASIZE - WILDCOPY_OVERLENGTH) ob,
     offset_val (d + ews - WILDCOPY_OVERLENGTH) ob)
  else (offset_val (d + ews - n) ob, offset_val (d + ews) ob).

(* where it zeroes the WILDCOPY_OVERLENGTH bytes after litBufferEnd (patch item 19): after the literals in dst
   (in_dst), and after the part of a split buffer in dst when it is split at once (splitImmediately, raw and RLE
   literals); the sequence executors over-read these cells *)
Definition alloc_slack (streaming cap bsm n d ews split: Z) : option Z :=
  if alloc_loc streaming cap bsm n =? LOC_IN_DST then Some (d + bsm + WILDCOPY_OVERLENGTH + n)
  else if alloc_loc streaming cap bsm n =? LOC_NOT_IN_DST then None
  else if split =? 1 then Some (d + ews - WILDCOPY_OVERLENGTH)
  else None.

(* the output array afterwards *)
Definition alloc_out (oc: list val) (streaming cap bsm n d ews split: Z) : list val :=
  match alloc_slack streaming cap bsm n d ews split with
  | Some k => sublist 0 k oc ++ Zrepeat (Vint (Int.repr 0)) WILDCOPY_OVERLENGTH ++
              sublist (k + WILDCOPY_OVERLENGTH) (Zlength oc) oc
  | None => oc
  end.

(* ZSTD_allocateLiteralsBuffer(dctx, dst, dstCapacity, litSize, streaming, expectedWriteSize,
   splitImmediately): sets litBuffer, litBufferEnd, litBufferLocation (alloc_loc, alloc_buf) and zeroes the
   slack after litBufferEnd in the output array oc (alloc_out). *)
Definition ZSTD_allocateLiteralsBuffer_spec : ident * funspec :=
  DECLARE _ZSTD_allocateLiteralsBuffer
  WITH p: val, fs: fstate, bsm: Z, ob: val, d: Z, cap: Z, n: Z, streaming: Z, split: Z, osh: share, oc: list val
  PRE [ tptr t_dctx, tptr tvoid, tulong, tulong, tint, tulong, tuint ]
    PROP (0 <= bsm <= ZSTD_BLOCKSIZE_MAX; fp_blockSizeMax (fs_fParams fs) = Vint (Int.repr bsm);
          fs_isFrameDecompression fs = Vint (Int.repr 1);
          0 <= cap <= Int64.max_unsigned; 0 <= n <= Z.min bsm cap;
          streaming = 0 \/ streaming = 1; split = 0 \/ split = 1; isptr ob;
          writable_share osh; 0 <= d; d + cap <= Zlength oc)
    PARAMS (p; offset_val d ob; Vlong (Int64.repr cap); Vlong (Int64.repr n); Vint (Int.repr streaming);
            Vlong (Int64.repr (Z.min bsm cap)); Vint (Int.repr split))
    SEP (frame_fields p fs; field_at_ Ews t_dctx (DOT _litBuffer) p;
         field_at_ Ews t_dctx (DOT _litBufferEnd) p; field_at_ Ews t_dctx (DOT _litBufferLocation) p;
         data_at osh (tarray tuchar (Zlength oc)) oc ob)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (frame_fields p fs;
         field_at Ews t_dctx (DOT _litBuffer) (fst (alloc_buf p ob streaming cap bsm n d (Z.min bsm cap) split)) p;
         field_at Ews t_dctx (DOT _litBufferEnd) (snd (alloc_buf p ob streaming cap bsm n d (Z.min bsm cap) split)) p;
         field_at Ews t_dctx (DOT _litBufferLocation) (Vint (Int.repr (alloc_loc streaming cap bsm n))) p;
         data_at osh (tarray tuchar (Zlength oc)) (alloc_out oc streaming cap bsm n d (Z.min bsm cap) split) ob).

(* ===================== the group ===================== *)

Definition LIT_S : funspecs :=
  [ ZSTD_blockSizeMax_spec; ZSTD_allocateLiteralsBuffer_spec; ZSTD_decodeLiteralsBlock_spec3 ].
Definition LIT_G : funspecs := (G_BLK ++ LIT_imports) ++ LIT_S.


(* ===================== small facts ===================== *)

Lemma lit_cmpu_gt (a b: Z) :
  0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int64.cmpu Cgt (Int64.repr a) (Int64.repr b) = (b <? a).
Proof.
  intros Ha Hb. simpl. unfold Int64.ltu. rewrite !Int64.unsigned_repr by lia.
  destruct (zlt b a); symmetry; [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Qed.

Lemma lit_cmpu_le (a b: Z) :
  0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int64.cmpu Cle (Int64.repr a) (Int64.repr b) = (a <=? b).
Proof.
  intros Ha Hb. simpl. unfold Int64.ltu. rewrite !Int64.unsigned_repr by lia.
  destruct (zlt b a); simpl; symmetry; [apply Z.leb_gt | apply Z.leb_le]; lia.
Qed.

Lemma lit_cmpu_lt (a b: Z) :
  0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int64.cmpu Clt (Int64.repr a) (Int64.repr b) = (a <? b).
Proof.
  intros Ha Hb. simpl. unfold Int64.ltu. rewrite !Int64.unsigned_repr by lia.
  destruct (zlt a b); symmetry; [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Qed.

(* pointer + / - a size_t or an int on a byte pointer *)
Lemma lit_add_l (q: val) (b: Z) :
  isptr q -> force_val (sem_add_ptr_long tuchar q (Vlong (Int64.repr b))) = offset_val b q.
Proof.
  intros Hq. destruct q; try contradiction. simpl. f_equal.
  rewrite Ptrofs.mul_commut, Ptrofs.mul_one. unfold Ptrofs.of_int64. f_equal.
  apply Ptrofs.eqm_samerepr. rewrite Int64.unsigned_repr_eq. unfold Ptrofs.eqm. apply Zbits.eqmod_sym.
  change Ptrofs.modulus with Int64.modulus. apply Zbits.eqmod_mod. reflexivity.
Qed.

Lemma lit_of64 (b: Z) : Ptrofs.of_int64 (Int64.repr b) = Ptrofs.repr b.
Proof.
  unfold Ptrofs.of_int64.
  apply Ptrofs.eqm_samerepr. rewrite Int64.unsigned_repr_eq. unfold Ptrofs.eqm. apply Zbits.eqmod_sym.
  change Ptrofs.modulus with Int64.modulus. apply Zbits.eqmod_mod. reflexivity.
Qed.

(* pointer - size_t, pointer - int *)
Lemma lit_sub_l (q: val) (b: Z) :
  isptr q -> force_val (sem_sub_pl tuchar q (Vlong (Int64.repr b))) = offset_val (- b) q.
Proof.
  intros Hq. destruct q; try contradiction. simpl. f_equal.
  rewrite Ptrofs.mul_commut, Ptrofs.mul_one, lit_of64, Ptrofs.sub_add_opp, Ptrofs.neg_repr. reflexivity.
Qed.

Lemma lit_sub_i (q: val) (b: Z) :
  isptr q -> Int.min_signed <= b <= Int.max_signed ->
  force_val (sem_sub_pi tuchar Signed q (Vint (Int.repr b))) = offset_val (- b) q.
Proof.
  intros Hq Hb. destruct q; try contradiction. simpl. f_equal.
  rewrite Ptrofs.mul_commut, Ptrofs.mul_one. unfold Ptrofs.of_ints.
  rewrite Int.signed_repr by lia. rewrite Ptrofs.sub_add_opp, Ptrofs.neg_repr. reflexivity.
Qed.

Lemma lit_add_i (q: val) (b: Z) :
  isptr q -> Int.min_signed <= b <= Int.max_signed ->
  force_val (sem_add_ptr_int tuchar Signed q (Vint (Int.repr b))) = offset_val b q.
Proof.
  intros Hq Hb. destruct q; try contradiction. simpl. f_equal.
  rewrite Ptrofs.mul_commut, Ptrofs.mul_one. unfold Ptrofs.of_ints.
  rewrite Int.signed_repr by lia. reflexivity.
Qed.

(* the context struct from one of its fields *)
Lemma lit_fc (f g: ident) (p: val) :
  field_compatible t_dctx (DOT f) p -> in_members g (co_members (get_co _ZSTD_DCtx_s)) ->
  field_compatible t_dctx (DOT g) p.
Proof.
  intros H Hg. apply field_compatible_cons in H. destruct H as [_ H].
  apply field_compatible_cons. split; [exact Hg | exact H].
Qed.

Lemma lit_extra_eq (p: val) :
  field_compatible t_dctx (DOT _litBuffer) p -> lit_extra p = offset_val 30380 p.
Proof.
  intros H. unfold lit_extra. rewrite field_address_offset; [reflexivity |].
  apply (lit_fc _litBuffer); [exact H | apply compute_in_members_true_iff; reflexivity].
Qed.

(* the lifted entailment `forward` leaves at the end of a branch *)
Ltac lit_fin :=
  unfold PROPx, LOCALx, SEPx, local, lift1; simpl; normalize;
  try (apply andp_right; [apply prop_right | cancel]; simpl in *; unfold_lift in *; simpl in *; tauto).

(* ---------- the Huffman part after an error ---------- *)

Lemma lit_mb_join (sh: share) (n m: Z) (q: val) :
  0 <= n -> 0 <= m ->
  memory_block sh n q * memory_block sh m (offset_val n q) |-- memory_block sh (n + m) q.
Proof.
  intros Hn Hm. destruct q as [| | | | | b i]; try (unfold memory_block at 1; rewrite FF_sepcon; apply FF_left).
  pose proof (Ptrofs.unsigned_range i) as Ri.
  unfold memory_block at 1. Intros. simpl offset_val.
  assert (E: Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr n)) = Ptrofs.unsigned i + n).
  { rewrite Ptrofs.add_unsigned, (Ptrofs.unsigned_repr n) by rep_lia. apply Ptrofs.unsigned_repr. rep_lia. }
  unfold memory_block at 1. rewrite E. Intros.
  replace (Vptr b i) with (Vptr b (Ptrofs.repr (Ptrofs.unsigned i))) by (rewrite Ptrofs.repr_unsigned; auto).
  rewrite (memory_block_split sh b (Ptrofs.unsigned i) n m) by lia.
  unfold memory_block at 1 2. rewrite !Ptrofs.unsigned_repr by rep_lia. entailer!.
Qed.

Lemma lit_hufhdr_mb (sh: share) (q: val) :
  hufhdr_at sh q |-- memory_block sh (4 + HUF_CELLBYTES) q.
Proof.
  unfold hufhdr_at. Intros ty lg res.
  sep_apply (data_at_memory_block sh t_dtdesc). simpl sizeof.
  sep_apply (lit_mb_join sh 4 HUF_CELLBYTES q); try (unfold HUF_CELLBYTES; lia); cancel.
Qed.

Lemma lit_hufdt_mb (sh: share) (ht: huf_table) (q: val) :
  hufdt_at sh ht q |-- memory_block sh (4 + HUF_CELLBYTES) q.
Proof.
  unfold hufdt_at, hufdt_x_at. Intros x2 L res.
  match goal with H: huf_ok _ |- _ => destruct H as [Hl _] end.
  unfold HUF_TABLELOG_MAX in *.
  assert (HL2: 0 < 2 ^ L <= 4096).
  { split; [apply Z.pow_pos_nonneg; lia |]. change 4096 with (2 ^ 12). apply Z.pow_le_mono_r; lia. }
  sep_apply (data_at_memory_block sh t_dtdesc). simpl sizeof.
  destruct x2.
  - Intros c2. sep_apply data_at_memory_block. simpl sizeof. rewrite Z.max_r by lia.
    rewrite <- (offset_offset_val q 4 (4 * 2 ^ L)).
    sep_apply (lit_mb_join sh (4 * 2 ^ L) (HUF_CELLBYTES - 4 * 2 ^ L) (offset_val 4 q));
      try (unfold HUF_CELLBYTES; lia).
    replace (4 * 2 ^ L + (HUF_CELLBYTES - 4 * 2 ^ L)) with HUF_CELLBYTES by lia.
    sep_apply (lit_mb_join sh 4 HUF_CELLBYTES q); try (unfold HUF_CELLBYTES; lia); cancel.
  - sep_apply data_at_memory_block. simpl sizeof. rewrite Z.max_r by lia.
    rewrite <- (offset_offset_val q 4 (2 * 2 ^ L)).
    sep_apply (lit_mb_join sh (2 * 2 ^ L) (HUF_CELLBYTES - 2 * 2 ^ L) (offset_val 4 q));
      try (unfold HUF_CELLBYTES; lia).
    replace (2 * 2 ^ L + (HUF_CELLBYTES - 2 * 2 ^ L)) with HUF_CELLBYTES by lia.
    sep_apply (lit_mb_join sh 4 HUF_CELLBYTES q); try (unfold HUF_CELLBYTES; lia); cancel.
Qed.

Lemma lit_hufdtx_mb (x2: bool) (sh: share) (ht: huf_table) (q: val) :
  hufdt_x_at x2 sh ht q |-- memory_block sh (4 + HUF_CELLBYTES) q.
Proof. eapply derives_trans; [| apply lit_hufdt_mb]. unfold hufdt_at. Exists x2. apply derives_refl. Qed.

Lemma lit_huf_junk (gv: globals) (p: val) (ox: option ddx) (oh: option huf_table) (x2: bool) :
  tabs_huf gv p ox oh x2 |-- huf_junk p.
Proof.
  unfold tabs_huf, huf_junk. Intros hp.
  destruct oh as [ht |].
  - Intros w. destruct w; Intros.
    + sep_apply lit_hufdtx_mb. cancel.
    + sep_apply lit_hufhdr_mb. cancel.
  - Intros. sep_apply lit_hufhdr_mb. cancel.
Qed.

(* ===================== ZSTD_blockSizeMax ===================== *)

Lemma body_blockSizeMax : body_ok LIT_G ZSTD_blockSizeMax_spec.
Proof.
  exists f_ZSTD_blockSizeMax; split; [reflexivity | split; [reflexivity |]].
  start_function.
  unfold frame_fields. Intros. rewrite H1. forward.
  destruct (fs_fParams fs) as (f1 & f2 & f3 & f4) eqn:EF.
  unfold fp_blockSizeMax in H0; simpl in H0. subst f3.
  forward_if (temp _t'1 (Vint (Int.repr bsm))).
  { forward. forward. entailer!. }
  { discriminate. }
  forward. forward. rewrite <- EF, <- H1. entailer!.
  - unfold ZSTD_BLOCKSIZE_MAX in H. rewrite Int.unsigned_repr by rep_lia. reflexivity.
  - unfold frame_fields. cancel.
Qed.

(* a byte array in three pieces [0, lo), [lo, hi), [hi, N) *)
Lemma lit_arr_split3 (sh: share) (N: Z) (c: list val) (b: val) (lo hi: Z) :
  0 <= lo <= hi -> hi <= N -> Zlength c = N -> field_compatible (tarray tuchar N) [] b ->
  data_at sh (tarray tuchar N) c b =
  data_at sh (tarray tuchar lo) (sublist 0 lo c) b *
  data_at sh (tarray tuchar (hi - lo)) (sublist lo hi c) (offset_val lo b) *
  data_at sh (tarray tuchar (N - hi)) (sublist hi N c) (offset_val hi b).
Proof.
  intros Hl Hh Hc Hf.
  rewrite (split3_data_at_Tarray_tuchar sh N lo hi c b) by lia.
  rewrite !field_address0_offset.
  - simpl. rewrite !Z.add_0_l, !Z.mul_1_l. reflexivity.
  - apply field_compatible0_cons. split; [simpl; lia | exact Hf].
  - apply field_compatible0_cons. split; [simpl; lia | exact Hf].
Qed.

(* the m cells at lo of the output array, as a memory block *)
Lemma lit_out_split (sh: share) (c: list val) (b: val) (lo m: Z) :
  0 <= lo -> 0 <= m -> lo + m <= Zlength c -> field_compatible (tarray tuchar (Zlength c)) [] b ->
  data_at sh (tarray tuchar (Zlength c)) c b |--
  data_at sh (tarray tuchar lo) (sublist 0 lo c) b * memory_block sh m (offset_val lo b) *
  data_at sh (tarray tuchar (Zlength c - (lo + m))) (sublist (lo + m) (Zlength c) c) (offset_val (lo + m) b).
Proof.
  intros Hl Hm Hc Hf. rewrite (lit_arr_split3 sh (Zlength c) c b lo (lo + m)) by (auto; lia).
  replace (lo + m - lo) with m by lia.
  sep_apply (data_at_memory_block sh (tarray tuchar m) (sublist lo (lo + m) c) (offset_val lo b)).
  simpl sizeof. rewrite Z.max_r by lia. rewrite Z.mul_1_l. cancel.
Qed.

Lemma lit_out_join (sh: share) (c: list val) (b: val) (lo m: Z) (x: list val) :
  0 <= lo -> Zlength x = m -> lo + m <= Zlength c -> field_compatible (tarray tuchar (Zlength c)) [] b ->
  data_at sh (tarray tuchar lo) (sublist 0 lo c) b * data_at sh (tarray tuchar m) x (offset_val lo b) *
  data_at sh (tarray tuchar (Zlength c - (lo + m))) (sublist (lo + m) (Zlength c) c) (offset_val (lo + m) b)
  |-- data_at sh (tarray tuchar (Zlength c)) (sublist 0 lo c ++ x ++ sublist (lo + m) (Zlength c) c) b.
Proof.
  intros Hl Hx Hc Hf. pose proof (Zlength_nonneg x).
  rewrite (lit_arr_split3 sh (Zlength c) (sublist 0 lo c ++ x ++ sublist (lo + m) (Zlength c) c) b lo (lo + m))
    by (auto; try lia; list_solve).
  replace (lo + m - lo) with m by lia.
  replace (sublist 0 lo (sublist 0 lo c ++ x ++ sublist (lo + m) (Zlength c) c)) with (sublist 0 lo c) by list_solve.
  replace (sublist lo (lo + m) (sublist 0 lo c ++ x ++ sublist (lo + m) (Zlength c) c)) with x by list_solve.
  replace (sublist (lo + m) (Zlength c) (sublist 0 lo c ++ x ++ sublist (lo + m) (Zlength c) c))
    with (sublist (lo + m) (Zlength c) c) by list_solve.
  cancel.
Qed.

(* the same, for an array c of length N (the output array after ZSTD_allocateLiteralsBuffer) *)
Lemma lit_out_split_n (sh: share) (N: Z) (c: list val) (b: val) (lo m: Z) :
  Zlength c = N -> 0 <= lo -> 0 <= m -> lo + m <= N -> field_compatible (tarray tuchar N) [] b ->
  data_at sh (tarray tuchar N) c b |--
  data_at sh (tarray tuchar lo) (sublist 0 lo c) b * memory_block sh m (offset_val lo b) *
  data_at sh (tarray tuchar (N - (lo + m))) (sublist (lo + m) N c) (offset_val (lo + m) b).
Proof. intros <-. apply lit_out_split. Qed.

Lemma lit_out_join_n (sh: share) (N: Z) (c: list val) (b: val) (lo m: Z) (x: list val) :
  Zlength c = N -> 0 <= lo -> Zlength x = m -> lo + m <= N -> field_compatible (tarray tuchar N) [] b ->
  data_at sh (tarray tuchar lo) (sublist 0 lo c) b * data_at sh (tarray tuchar m) x (offset_val lo b) *
  data_at sh (tarray tuchar (N - (lo + m))) (sublist (lo + m) N c) (offset_val (lo + m) b)
  |-- data_at sh (tarray tuchar N) (sublist 0 lo c ++ x ++ sublist (lo + m) N c) b.
Proof. intros <-. apply lit_out_join. Qed.

Lemma body_allocate : body_ok LIT_G ZSTD_allocateLiteralsBuffer_spec.
Proof.
  exists f_ZSTD_allocateLiteralsBuffer; split; [reflexivity | split; [reflexivity |]].
  start_function.
  forward_call (p, fs, bsm).
  forward_if (temp _t'8 (Vint (Int.repr (if alloc_loc streaming cap bsm n =? LOC_IN_DST then 1 else 0)))).
  - forward. entailer!.
    unfold ZSTD_BLOCKSIZE_MAX in *. rewrite lit_cmpu_gt by rep_lia.
    unfold alloc_loc, WILDCOPY_OVERLENGTH. simpl.
    destruct (bsm + 32 + n + 32 <? cap); [reflexivity |].
    destruct (n <=? LITBUFFEREXTRASIZE); reflexivity.
  - forward. entailer!.
    unfold alloc_loc. destruct H4 as [-> | ->]; [contradiction |]. simpl.
    destruct (n <=? LITBUFFEREXTRASIZE); reflexivity.
  - assert (Hb: 0 <= bsm <= 131072) by (unfold ZSTD_BLOCKSIZE_MAX in H; lia).
    assert (Hd: isptr (offset_val d ob)) by (destruct ob; try contradiction; exact I).
    assert_PROP (field_compatible (tarray tuchar (Zlength oc)) [] ob) as FCo by entailer!.
    forward_if.
    + forward. forward. forward. forward.
      assert (HL: alloc_loc streaming cap bsm n = LOC_IN_DST).
      { destruct (alloc_loc streaming cap bsm n =? LOC_IN_DST) eqn:E; [apply Z.eqb_eq; auto | contradiction]. }
      rewrite lit_add_l by auto. rewrite lit_add_i by (auto; rep_lia). rewrite lit_add_l by auto.
      rewrite !offset_offset_val.
      forward.
      assert (Hroom: streaming = 0 /\ bsm + 32 + n + 32 < cap).
      { unfold alloc_loc in HL. destruct (andb (streaming =? 0) _) eqn:E.
        - apply andb_prop in E. destruct E as [E1 E2]. apply Z.eqb_eq in E1. apply Z.ltb_lt in E2.
          unfold WILDCOPY_OVERLENGTH in E2. lia.
        - destruct (n <=? LITBUFFEREXTRASIZE); discriminate. }
      replace (d + (bsm + 32) + n) with (d + bsm + 32 + n) by lia.
      sep_apply (lit_out_split osh oc ob (d + bsm + 32 + n) 32); try lia; auto.
      forward_call (osh, offset_val (d + bsm + 32 + n) ob, 0, 32).
      { cancel. }
      sep_apply (lit_out_join osh oc ob (d + bsm + 32 + n) 32 (Zrepeat (Vint (Int.repr 0)) 32)); try lia; auto.
      unfold alloc_buf, alloc_out, alloc_slack; rewrite HL, Z.eqb_refl; cbn [fst snd].
      unfold WILDCOPY_OVERLENGTH, LOC_IN_DST.
      replace (d + bsm + 32) with (d + (bsm + 32)) by lia. entailer!.
    + assert (HL: alloc_loc streaming cap bsm n <> LOC_IN_DST).
      { intros E. rewrite E in H9. discriminate. }
      forward_if (temp _t'6 (Vint (Int.repr 65536))).
      { forward. entailer!. }
      { discriminate. }
      forward_if (temp _t'7 (Vint (Int.repr 65536))).
      { discriminate. }
      { forward_if (temp _t'7 (Vint (Int.repr 65536))).
        - forward. forward. entailer!.
        - discriminate. }
      assert (Hn: 0 <= n <= 131072) by (pose proof (Z.le_min_l bsm cap); lia).
      forward_if.
      * (* in litExtraBuffer *)
        rewrite !Int64.unsigned_repr in H10 by rep_lia.
        assert (HL2: alloc_loc streaming cap bsm n = LOC_NOT_IN_DST).
        { unfold alloc_loc in *. destruct (andb _ _); [contradiction |].
          destruct (n <=? LITBUFFEREXTRASIZE) eqn:E; [reflexivity |].
          apply Z.leb_gt in E. unfold LITBUFFEREXTRASIZE in E. lia. }
        forward. forward. forward. forward.
        assert_PROP (field_compatible t_dctx (DOT _litBuffer) p) as FC by entailer!.
        unfold alloc_buf, alloc_out, alloc_slack; rewrite HL2; simpl.
        rewrite lit_extra_eq by auto.
        rewrite lit_add_l by (destruct FC as [Hp _]; destruct p; try contradiction; exact I).
        rewrite offset_offset_val. unfold LOC_NOT_IN_DST. entailer!.
        unfold PROPx, LOCALx, SEPx, local, lift1; simpl; normalize.
      * (* split *)
        rewrite !Int64.unsigned_repr in H10 by rep_lia.
        assert (HL2: alloc_loc streaming cap bsm n = LOC_SPLIT).
        { unfold alloc_loc in *. destruct (andb _ _); [contradiction |].
          destruct (n <=? LITBUFFEREXTRASIZE) eqn:E; [| reflexivity].
          apply Z.leb_le in E. unfold LITBUFFEREXTRASIZE in E. lia. }
        assert (He: 0 <= Z.min bsm cap <= 131072) by (pose proof (Z.le_min_l bsm cap); lia).
        forward_if (PROP ()
          LOCAL (temp _dctx p)
          SEP (frame_fields p fs;
               field_at Ews t_dctx (DOT _litBuffer) (fst (alloc_buf p ob streaming cap bsm n d (Z.min bsm cap) split)) p;
               field_at Ews t_dctx (DOT _litBufferEnd) (snd (alloc_buf p ob streaming cap bsm n d (Z.min bsm cap) split)) p;
               field_at_ Ews t_dctx (DOT _litBufferLocation) p;
               data_at osh (tarray tuchar (Zlength oc)) (alloc_out oc streaming cap bsm n d (Z.min bsm cap) split) ob)).
        -- assert (Hs: split = 1) by (destruct H5 as [-> | ->]; [contradiction | reflexivity]). subst split.
           assert (Hob: forall k, isptr (offset_val k ob)) by (intros; destruct ob; try contradiction; exact I).
           forward_if (temp _t'2 (Vint (Int.repr 65536))).
           { forward. entailer!. }
           { discriminate. }
           forward_if (temp _t'3 (Vint (Int.repr 65536))).
           { discriminate. }
           { forward_if (temp _t'3 (Vint (Int.repr 65536))).
             - forward. forward. entailer!.
             - discriminate. }
           forward. { entailer!. destruct ob; try contradiction. split; exact I. }
           rewrite lit_add_l by auto. rewrite lit_sub_l by auto. rewrite lit_add_i by (auto; rep_lia).
           rewrite lit_sub_i by (auto; rep_lia). rewrite !offset_offset_val.
           forward_if (temp _t'4 (Vint (Int.repr 65536))).
           { forward. entailer!. }
           { discriminate. }
           forward_if (temp _t'5 (Vint (Int.repr 65536))).
           { discriminate. }
           { forward_if (temp _t'5 (Vint (Int.repr 65536))).
             - forward. forward. entailer!.
             - discriminate. }
           forward. forward.
           rewrite lit_add_l by auto. rewrite lit_sub_i by (auto; rep_lia). rewrite !offset_offset_val.
           match goal with |- context [field_at Ews t_dctx (DOT _litBufferEnd) (offset_val ?k ob) p] =>
             replace k with (d + Z.min bsm cap - 32) by lia end.
           match goal with |- context [field_at Ews t_dctx (DOT _litBuffer) (offset_val ?k ob) p] =>
             replace k with (d + Z.min bsm cap - n + 65536 - 32) by lia end.
           forward.
           sep_apply (lit_out_split osh oc ob (d + Z.min bsm cap - 32) 32); try lia; auto.
           forward_call (osh, offset_val (d + Z.min bsm cap - 32) ob, 0, 32).
           { cancel. }
           sep_apply (lit_out_join osh oc ob (d + Z.min bsm cap - 32) 32 (Zrepeat (Vint (Int.repr 0)) 32)); try lia; auto.
           unfold alloc_buf, alloc_out, alloc_slack; rewrite HL2; cbn [fst snd Z.eqb LOC_SPLIT LOC_IN_DST LOC_NOT_IN_DST].
           unfold LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH.
           replace (d + Z.min bsm cap - n + 65536 - 32 + (n - 65536)) with (d + Z.min bsm cap - 32) by lia.
           entailer!.
        -- assert (Hs: split = 0) by (destruct H5 as [-> | ->]; [reflexivity | discriminate]). subst split.
           forward.
           rewrite lit_add_l by auto. rewrite lit_sub_l by (destruct ob; try contradiction; exact I).
           rewrite offset_offset_val.
           forward. rewrite lit_add_l by auto. rewrite offset_offset_val.
           replace (d + (Z.min bsm cap + - n)) with (d + Z.min bsm cap - n) by lia.
           unfold alloc_buf, alloc_out, alloc_slack; rewrite HL2; simpl. entailer!. lit_fin.
        -- forward. rewrite HL2. unfold LOC_SPLIT. entailer!.
Qed.

Lemma lit_tabs_fold (gv: globals) (p: val) (ox: option ddx) (oh: option huf_table) (x2: bool) (hp: val) :
  field_at Ews t_dctx (DOT _HUFptr) hp p *
  field_at Ews t_dctx (DOT _litEntropy) (Vint (Int.repr (match oh with Some _ => 1 | None => 0 end))) p *
  match oh with
  | None => !! (hp = ctx_huf p) && hufhdr_at Ews (ctx_huf p)
  | Some ht =>
      EX w: bool,
      if w then !! (hp = ctx_huf p) && hufdt_x_at x2 Ews ht (ctx_huf p)
      else !! (ox_huf ox = Some ht /\ hp = dd_huf (ox_q ox)) && hufhdr_at Ews (ctx_huf p)
  end |-- tabs_huf gv p ox oh x2.
Proof. unfold tabs_huf. Exists hp. cancel. Qed.

(* ---------- error returns ---------- *)

Lemma lit_err_true (e: Z) : 1 <= e <= 119 -> is_error_code (err_code e) = true.
Proof. intros H. unfold is_error_code, err_code. apply Z.ltb_lt. lia. Qed.

Lemma lit_err_val (e: Z) :
  1 <= e <= 119 -> Vlong (Int64.repr (- e)) = Vlong (Int64.repr (err_code e)) /\ 0 <= err_code e <= Int64.max_unsigned.
Proof.
  intros H. split; [| unfold err_code; rep_lia].
  f_equal. apply Int64.eqm_samerepr. exists (-1). unfold err_code. change Int64.modulus with (2 ^ 64). lia.
Qed.

(* bytes in, bytes out *)
Lemma litc_bc_zbytes (l: list Z) : bytes_ok l -> byte_cells (zbytes l).
Proof.
  intros H. unfold byte_cells. induction H as [| b l Hb _ IH]; constructor; auto.
  exists b. unfold is_byte in Hb. split; [lia | reflexivity].
Qed.

(* litExtraBuffer exactly, forgotten to bytes (the scratch of an error return) *)
Lemma lit_scratch_x_weak (p: val) (lxb: list Z) : lit_scratch_x p lxb |-- lit_scratch p.
Proof.
  unfold lit_scratch_x, lit_scratch, lit_extra_at, lit_extra_bytes. Intros. Exists (zbytes lxb).
  entailer!. apply litc_bc_zbytes. assumption.
Qed.

(* an error return is exact when the model's literals section fails *)
Lemma lx_err (hx: option xhuf) (lxb: list Z) (o: outarr) (i: inwin) (bsm streaming r: Z) (oc': list val)
    (l: litloc) (lits: list Z) (hx': option xhuf) (lxb': list Z) :
  is_error_code r = true -> xb_lits hx (iw_s i) bsm (Z.min bsm (oa_cap o)) (streaming =? 1) = None ->
  lits_exact hx lxb o i bsm streaming r oc' l lits hx' lxb'.
Proof. intros He Hx rb mem _ _ _. cbv zeta. rewrite Hx. exact He. Qed.

Lemma lit_unch (oc: list val) (lo hi: Z) : unchanged_outside oc oc lo hi.
Proof. intros k _ _. reflexivity. Qed.

Lemma lit_dl_short (oh: option huf_table) (s: list Z) (bsm: Z) :
  Zlength s < 2 -> decode_literals oh s bsm = None.
Proof. intros H. unfold decode_literals. rewrite (proj2 (Z.ltb_lt _ _) H). reflexivity. Qed.

(* a byte of the input window *)
Lemma lit_win_byte (ic: list val) (ioff: Z) (s: list Z) (k: Z) :
  sublist ioff (ioff + Zlength s) ic = zbytes s -> 0 <= ioff -> ioff + Zlength s <= Zlength ic ->
  0 <= k < Zlength s -> Znth (ioff + k) ic = Vint (Int.repr (byte_at s k)).
Proof.
  intros Hw Ho Hn Hk.
  assert (E: Znth k (sublist ioff (ioff + Zlength s) ic) = Znth (k + ioff) ic)
    by (apply Znth_sublist; lia).
  rewrite Hw, Znth_map in E by lia. rewrite Z.add_comm, <- E.
  unfold byte_at. f_equal. f_equal. rewrite <- nth_Znth by lia. reflexivity.
Qed.

Lemma lit_byte_range (s: list Z) (k: Z) : bytes_ok s -> 0 <= byte_at s k < 256.
Proof.
  intros Hb. unfold byte_at.
  destruct (lt_dec (Z.to_nat k) (length s)) as [Hl | Hl].
  - apply (Forall_nth is_byte s) with (d := 0) (i := Z.to_nat k) in Hl; [exact Hl | exact Hb].
  - rewrite nth_overflow by lia. lia.
Qed.

(* the address of a cell of a byte array *)
Lemma lit_fa (N k: Z) (b: val) :
  field_compatible (tarray tuchar N) [] b -> 0 <= k < N ->
  field_address (tarray tuchar N) [ArraySubsc k] b = offset_val k b.
Proof.
  intros H Hk. rewrite field_address_offset; [simpl; f_equal; lia |].
  apply field_compatible_cons; split; [simpl; lia | exact H].
Qed.

Lemma lit_dec_err (e: Z) : 1 <= e <= 119 -> e <> 80 -> e <> 82 -> dec_err (err_code e).
Proof.
  intros H H1 H2. unfold dec_err, is_error_code, err_code,
    ZSTD_error_noForwardProgress_destFull, ZSTD_error_noForwardProgress_inputEmpty.
  split; [apply Z.ltb_lt; lia | lia].
Qed.

(* the last conjunct of the post, `is_error_code r = true -> dec_err r`: peel it off a goal A /\ (.. -> dec_err r) *)
Ltac lit_dec_close :=
  first [ apply lit_dec_err; lia
        | match goal with H: is_error_code ?r = true |- dec_err ?r =>
            unfold is_error_code in H; apply Z.ltb_lt in H; rep_lia end
        | match goal with H: is_error_code ?r = false, H': is_error_code ?r = true |- _ =>
            rewrite H in H'; discriminate end
        | match goal with H: _ = true |- dec_err ?r => discriminate H end ].
Ltac lit_decfix :=
  match goal with
  | |- ?A /\ (_ = true -> dec_err _) =>
      let H := fresh "HA" in cut A; [intros H; split; [exact H | intros ?; lit_dec_close] |]
  | |- _ = true -> dec_err _ => intros ?; lit_dec_close
  end.

(* the postcondition of an error return e (oc: the output array, unchanged; x2, lxb: the precondition's table
   type and litExtraBuffer).  It leaves the goals about the models: decode_literals' outcome, and that the exact
   model fails (`xb_lits .. = None`, lx_err). *)
Ltac lit_err e oc oh x2 lxb :=
  Exists (err_code e) oc LExtra (@nil Z) oh x2 lxb;
  rewrite (lit_err_true e) by lia;
  destruct (lit_err_val e) as [?LEV ?LER]; [lia |];
  entailer!;
  [ repeat split; auto; try apply lit_unch; try (intros; discriminate);
    try (intros _; apply lit_dec_err; lia);
    try (let BC := fresh "BC" in intros BC _; exact BC);
    try (intros _; apply lx_err; [apply lit_err_true; lia |])
  | sep_apply lit_scratch_x_weak;
    first [ sep_apply lit_huf_junk; cancel
          | unfold huf_junk; sep_apply lit_hufhdr_mb; cancel
          | unfold huf_junk; sep_apply lit_hufdtx_mb; cancel
          | unfold huf_junk; sep_apply lit_hufdt_mb; cancel ] ].

(* ---------- tactics for zstd's macro loops (as body_dict_load) ---------- *)

Ltac lit_body :=
  solve [ forward; entailer!
        | match goal with |- semax _ ?Q _ _ => forward_if Q end;
          [ contradiction | forward; entailer! | forward; entailer! ]
        | match goal with |- semax _ ?Q _ _ => forward_if Q end;
          [ contradiction | forward; entailer! ] ].

(* for(;;break) { skip / if(0) ... } *)
Ltac lit_skiploop :=
  repeat match goal with |- semax _ _ (Ssequence (Ssequence _ _) _) _ => apply -> seq_assoc end;
  match goal with
  | |- semax _ ?P (Ssequence (Sloop _ Sbreak) _) _ =>
      forward_loop P break: P; [ entailer! | lit_body | ]
  | |- semax _ ?P (Sloop _ Sbreak) _ =>
      forward_loop P break: P; [ entailer! | lit_body | ]
  end.

(* the error path of RETURN_ERROR_IF: four macro loops, then the return *)
Ltac lit_errpath := do 4 lit_skiploop; forward.

(* RETURN_ERROR_IF(cond, ...): the loop around it; after it, C holds *)
Ltac lit_check C :=
  repeat match goal with |- semax _ _ (Ssequence (Ssequence _ _) _) _ => apply -> seq_assoc end;
  match goal with |- semax _ (PROPx ?Ps (LOCALx ?Qs (SEPx ?Rs))) (Ssequence (Sloop _ Sbreak) _) _ =>
    forward_loop (PROPx Ps (LOCALx Qs (SEPx Rs)))
      break: (PROPx (C :: Ps) (LOCALx Qs (SEPx Rs))) end.

(* ===================== ZSTD_decodeLiteralsBlock: the switch on the literals type ===================== *)

(* the cases of `switch (litEncType)` (code.v) *)
Definition lit_sw : labeled_statements :=
  match fn_body f_ZSTD_decodeLiteralsBlock with
  | Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Sswitch _ ls))))) => ls
  | _ => LSnil
  end.

Definition lit_Delta : tycontext := func_tycontext f_ZSTD_decodeLiteralsBlock Vprog LIT_G nil.

(* the precondition's facts, and the block body has at least 2 bytes (the first check) *)
Definition lit_hyps (fs: fstate) (oh: option huf_table) (bsm streaming: Z) (W: list ptr_witness)
    (o: outarr) (i: inwin) : Prop :=
  outarr_ok o /\ inwin_ok i /\ (streaming = 0 \/ streaming = 1) /\ 0 <= bsm <= ZSTD_BLOCKSIZE_MAX /\
  Zlength (iw_s i) <= bsm /\ fp_blockSizeMax (fs_fParams fs) = Vint (Int.repr bsm) /\
  fs_isFrameDecompression fs = Vint (Int.repr 1) /\
  (fs_ddictIsCold fs = Vint (Int.repr 0) \/ fs_ddictIsCold fs = Vint (Int.repr 1)) /\
  (oa_cap o = 0 -> (pws_pred W |-- weak_valid_pointer (offset_val (oa_d o) (oa_base o)))) /\
  match oh with Some ht => huf_ok ht | None => True end /\
  2 <= Zlength (iw_s i).

(* the state at the switch: litEncType = k *)
Definition lit_L (gv: globals) (p: val) (bsm streaming: Z) (o: outarr) (i: inwin) (k: Z) : list localdef :=
  [temp _blockSizeMax (Vlong (Int64.repr bsm)); temp _litEncType (Vint (Int.repr k));
   temp _istart (offset_val (iw_off i) (iw_base i)); gvars gv; temp _dctx p;
   temp _srcSize (Vlong (Int64.repr (Zlength (iw_s i))));
   temp _dst (offset_val (oa_d o) (oa_base o)); temp _dstCapacity (Vlong (Int64.repr (oa_cap o)));
   temp _streaming (Vint (Int.repr streaming))].

Definition lit_S (gv: globals) (p: val) (fs: fstate) (ox: option ddx) (oh: option huf_table) (x2: bool)
    (lxb: list Z) (W: list ptr_witness) (o: outarr) (i: inwin) : list mpred :=
  [frame_fields p fs; zstd_globals gv; pws_pred W; cfg_lit p; tabs_huf gv p ox oh x2; dent_of dent_def gv ox;
   field_at_ Ews t_dctx (DOT _workspace) p; lit_scratch_x p lxb;
   data_at (oa_sh o) (tarray tuchar (oa_N o)) (oa_c o) (oa_base o);
   data_at (iw_sh i) (tarray tuchar (iw_N i)) (iw_c i) (iw_base i)].

(* the function's postcondition (ZSTD_decodeLiteralsBlock_spec3) *)
Definition lit_post (gv: globals) (p: val) (fs: fstate) (ox: option ddx) (oh: option huf_table) (x2: bool)
    (lxb: list Z) (bsm streaming: Z) (W: list ptr_witness) (o: outarr) (i: inwin) : environ -> mpred :=
  (EX r: Z, EX oc': list val, EX l: litloc, EX lits: list Z, EX oh': option huf_table, EX x2': bool,
   EX lxb': list Z,
    PROP (0 <= r <= Int64.max_unsigned; Zlength oc' = oa_N o;
          unchanged_outside (oa_c o) oc' (oa_d o) (oa_d o + oa_cap o);
          streaming = 1 -> unchanged_outside (oa_c o) oc' (oa_d o) (oa_d o + Z.min (oa_cap o) bsm);
          is_error_code r = false -> lits_ok oh o i bsm streaming r oc' l lits oh';
          match decode_literals oh (iw_s i) bsm with
          | Some (lits0, _, _) => is_error_code r = false \/ Z.min (oa_cap o) bsm < Zlength lits0
          | None => True
          end;
          is_error_code r = true -> dec_err r;
          byte_cells (oa_c o) -> byte_cells (iw_c i) -> byte_cells oc';
          is_error_code r = false -> forall j, 0 <= j < oa_N o -> is_byte_val (Znth j (oa_c o)) -> is_byte_val (Znth j oc');
          ox = None ->
          lits_exact (option_map (xhuf_of x2) oh) lxb o i bsm streaming r oc' l lits
            (option_map (xhuf_of x2') oh') lxb')
    RETURN (Vlong (Int64.repr r))
    SEP (zstd_globals gv; pws_pred W; cfg_lit p; frame_fields p fs; dent_of dent_def gv ox;
         field_at_ Ews t_dctx (DOT _workspace) p;
         data_at (oa_sh o) (tarray tuchar (oa_N o)) oc' (oa_base o);
         data_at (iw_sh i) (tarray tuchar (iw_N i)) (iw_c i) (iw_base i);
         if is_error_code r then huf_junk p * lit_scratch p
         else tabs_huf gv p ox oh' x2' * litfields p (oa_base o) (iw_base i) l lits lxb'))%assert.

Definition lit_R (gv: globals) (p: val) (fs: fstate) (ox: option ddx) (oh: option huf_table) (x2: bool)
    (lxb: list Z) (bsm streaming: Z) (W: list ptr_witness) (o: outarr) (i: inwin) : ret_assert :=
  frame_ret_assert (function_body_ret_assert tulong (lit_post gv p fs ox oh x2 lxb bsm streaming W o i))
    (stackframe_of f_ZSTD_decodeLiteralsBlock).

(* the switch from the case-k label on (fall-through included), litEncType = e *)
Definition lit_seg (k e: Z) (extra: option huf_table -> Prop) : Prop :=
  forall (Espec: OracleKind) (gv: globals) (p: val) (fs: fstate) (ox: option ddx) (oh: option huf_table)
    (x2: bool) (lxb: list Z) (bsm streaming: Z) (W: list ptr_witness) (o: outarr) (i: inwin) (R: ret_assert),
    lit_hyps fs oh bsm streaming W o i -> Z.land (byte_at (iw_s i) 0) 3 = e -> extra oh ->
    RA_return R = RA_return (lit_R gv p fs ox oh x2 lxb bsm streaming W o i) ->
    semax lit_Delta (PROPx [] (LOCALx (lit_L gv p bsm streaming o i e) (SEPx (lit_S gv p fs ox oh x2 lxb W o i))))
      (seq_of_labeled_statement (select_switch (Int.unsigned (Int.repr k)) lit_sw)) (switch_ret_assert R).

(* ---------- set_basic helpers ---------- *)

(* the raw literals header: (lhSize, litSize) *)
Definition lit_rawhdr (s: list Z) : Z * Z :=
  let b0 := byte_at s 0 in
  let lhl := Z.land (Z.shiftr b0 2) 3 in
  if lhl =? 1 then (2, Z.shiftr (le_field s 0 2) 4)
  else if lhl =? 3 then (3, Z.shiftr (le_field s 0 3) 4)
  else (1, Z.shiftr b0 3).

Lemma lit_dl_raw (oh: option huf_table) (s: list Z) (bsm lh ls: Z) :
  Z.land (byte_at s 0) 3 = 0 -> 2 <= Zlength s ->
  (Z.land (Z.shiftr (byte_at s 0) 2) 3 = 3 -> 3 <= Zlength s) -> lit_rawhdr s = (lh, ls) ->
  decode_literals oh s bsm =
  if ls >? bsm then None else if lh + ls >? Zlength s then None else Some (slice s lh ls, lh + ls, oh).
Proof.
  intros Ht H2 H3 Hh. unfold lit_rawhdr in Hh. unfold decode_literals.
  rewrite (proj2 (Z.ltb_ge _ _) H2), Ht. simpl.
  destruct (Z.land (Z.shiftr (byte_at s 0) 2) 3 =? 1) eqn:E1.
  - inversion Hh; subst. apply Z.eqb_eq in E1. rewrite E1. reflexivity.
  - destruct (Z.land (Z.shiftr (byte_at s 0) 2) 3 =? 3) eqn:E3.
    + inversion Hh; subst. apply Z.eqb_eq in E3. specialize (H3 E3).
      rewrite (proj2 (Z.ltb_ge _ _) H3). reflexivity.
    + inversion Hh; subst. reflexivity.
Qed.

Lemma lit_dl_raw3 (oh: option huf_table) (s: list Z) (bsm: Z) :
  Z.land (byte_at s 0) 3 = 0 -> Z.land (Z.shiftr (byte_at s 0) 2) 3 = 3 -> Zlength s < 3 ->
  decode_literals oh s bsm = None.
Proof.
  intros Ht H3 Hn. unfold decode_literals. rewrite Ht, H3. simpl.
  destruct (Zlength s <? 2); [reflexivity |]. rewrite (proj2 (Z.ltb_lt _ _) Hn). reflexivity.
Qed.

Lemma lit_le_value_range (l: list Z) : bytes_ok l -> 0 <= le_value l < 2 ^ (8 * Zlength l).
Proof.
  induction l as [|b l IH]; intros Hl.
  - simpl. rewrite ?Zlength_nil. simpl. lia.
  - inversion Hl as [|? ? Hb Hl']; subst. specialize (IH Hl'). unfold is_byte in Hb.
    simpl le_value. rewrite Zlength_cons.
    replace (8 * Z.succ (Zlength l))%Z with (8 + 8 * Zlength l)%Z by lia.
    rewrite Z.pow_add_r by (pose proof (Zlength_nonneg l); lia). change (2^8) with 256. nia.
Qed.

Lemma lit_slice (s: list Z) (i k: Z) :
  0 <= i -> 0 <= k -> i + k <= Zlength s -> slice s i k = sublist i (i + k) s.
Proof.
  intros Hi Hk Hn. unfold slice, sublist. rewrite skipn_firstn_comm. f_equal. lia.
Qed.

Lemma lit_le_field (s: list Z) (k: Z) :
  bytes_ok s -> 0 <= k <= Zlength s -> 0 <= le_field s 0 k < 2 ^ (8 * k).
Proof.
  intros Hb Hk. unfold le_field. rewrite lit_slice by lia. rewrite Z.add_0_l.
  assert (Hs: bytes_ok (sublist 0 k s)) by (unfold bytes_ok in *; apply Forall_sublist; exact Hb).
  pose proof (lit_le_value_range _ Hs) as L. rewrite Zlength_sublist in L by lia.
  replace (k - 0) with k in L by lia. exact L.
Qed.

Lemma lit_shr (v k: Z) :
  0 <= v <= Int.max_signed -> 0 <= k < 32 -> Int.shr (Int.repr v) (Int.repr k) = Int.repr (Z.shiftr v k).
Proof.
  intros Hv Hk. unfold Int.shr. rewrite Int.signed_repr by rep_lia. rewrite Int.unsigned_repr by rep_lia.
  reflexivity.
Qed.

Lemma lit_shru (v k: Z) :
  0 <= v <= Int.max_unsigned -> 0 <= k < 32 -> Int.shru (Int.repr v) (Int.repr k) = Int.repr (Z.shiftr v k).
Proof.
  intros Hv Hk. unfold Int.shru. rewrite !Int.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma lit_shiftr_range (v k: Z) : 0 <= v -> 0 <= k -> 0 <= Z.shiftr v k <= v.
Proof.
  intros Hv Hk. rewrite Z.shiftr_div_pow2 by lia. split.
  - apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia].
  - apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia |].
    assert (1 <= 2 ^ k) by (apply Z.pow_le_mono_r with (a := 2) in Hk; [simpl in Hk; lia | lia]). nia.
Qed.

Lemma lit_shiftr_lt (v k m: Z) : 0 <= v < 2 ^ (m + k) -> 0 <= k -> 0 <= m -> Z.shiftr v k < 2 ^ m.
Proof.
  intros Hv Hk Hm. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia |].
  rewrite <- Z.pow_add_r by lia. replace (k + m) with (m + k) by lia. lia.
Qed.

(* the header's sizes *)
Lemma lit_rawhdr_range (s: list Z) (lh ls: Z) :
  bytes_ok s -> 2 <= Zlength s -> (Z.land (Z.shiftr (byte_at s 0) 2) 3 = 3 -> 3 <= Zlength s) ->
  lit_rawhdr s = (lh, ls) -> 1 <= lh <= 3 /\ lh <= Zlength s /\ 0 <= ls < 2 ^ 20.
Proof.
  intros Hb H2 H3 Hh. unfold lit_rawhdr in Hh.
  pose proof (lit_byte_range s 0 Hb) as R0.
  destruct (Z.land (Z.shiftr (byte_at s 0) 2) 3 =? 1) eqn:E1.
  - inversion Hh; subst. pose proof (lit_le_field s 2 Hb ltac:(lia)) as L.
    split; [lia | split; [lia |]]. split; [apply Z.shiftr_nonneg; lia |].
    apply lit_shiftr_lt; lia.
  - destruct (Z.land (Z.shiftr (byte_at s 0) 2) 3 =? 3) eqn:E3.
    + inversion Hh; subst. apply Z.eqb_eq in E3. specialize (H3 E3).
      pose proof (lit_le_field s 3 Hb ltac:(lia)) as L.
      split; [lia | split; [lia |]]. split; [apply Z.shiftr_nonneg; lia |].
      apply lit_shiftr_lt; lia.
    + inversion Hh; subst. split; [lia | split; [lia |]].
      pose proof (lit_shiftr_range (byte_at s 0) 3 ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma lit_band3 (b: Z) : 0 <= b < 256 -> Int.and (Int.repr b) (Int.repr 3) = Int.repr (Z.land b 3).
Proof.
  intros Hb. unfold Int.and. rewrite !Int.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma lit_band3_range (b: Z) : 0 <= Z.land b 3 <= 3.
Proof.
  change (Z.land b 3) with (Z.land b (Z.ones 2)). rewrite Z.land_ones by lia.
  assert (H4: 0 < 2 ^ 2) by reflexivity. pose proof (Z.mod_pos_bound b (2 ^ 2) H4).
  change (2 ^ 2) with 4 in *. lia.
Qed.

(* dst is (weakly) valid: in the output array, or by the caller's witness when the array is empty *)
Lemma lit_dst_wvp (W: list ptr_witness) (osh: share) (oc: list val) (ob: val) (d cap: Z) :
  writable_share osh -> 0 <= d -> 0 <= cap -> d + cap <= Zlength oc ->
  (cap = 0 -> pws_pred W |-- weak_valid_pointer (offset_val d ob)) ->
  pws_pred W * data_at osh (tarray tuchar (Zlength oc)) oc ob * TT |-- weak_valid_pointer (offset_val d ob).
Proof.
  intros Hw Hd Hc Hn Hweak. apply sepcon_weak_valid_pointer1.
  destruct (Z.eq_dec (Zlength oc) 0) as [E | NE].
  - apply sepcon_weak_valid_pointer1. apply Hweak. lia.
  - apply sepcon_weak_valid_pointer2. eapply derives_trans; [apply data_at_memory_block |].
    apply memory_block_weak_valid_pointer; [| | auto].
    + rewrite sizeof_tarray_tuchar by (pose proof (Zlength_nonneg oc); lia). lia.
    + rewrite sizeof_tarray_tuchar by (pose proof (Zlength_nonneg oc); lia). pose proof (Zlength_nonneg oc). lia.
Qed.

Local Transparent denote_tc_test_eq.
Lemma lit_test_eq_null (q: val) (P: mpred) :
  isptr q -> (P |-- weak_valid_pointer q) -> P |-- denote_tc_test_eq q (Vlong (Int64.repr 0)).
Proof.
  intros Hq H. destruct q; try contradiction. unfold denote_tc_test_eq. simpl.
  apply andp_right; [apply prop_right; reflexivity | exact H].
Qed.
Local Opaque denote_tc_test_eq.

Lemma lit_slice_len (s: list Z) (i k: Z) :
  0 <= i -> 0 <= k -> i + k <= Zlength s -> Zlength (slice s i k) = k.
Proof. intros. rewrite lit_slice by lia. rewrite Zlength_sublist by lia. lia. Qed.

Lemma lit_not_err (r: Z) : 0 <= r < 2 ^ 32 -> is_error_code r = false.
Proof. intros H. unfold is_error_code. apply Z.ltb_ge. lia. Qed.

(* the literals in the input window *)
Lemma lit_win_sub (ic: list val) (ioff lh ls: Z) (s: list Z) :
  sublist ioff (ioff + Zlength s) ic = zbytes s -> 0 <= ioff -> ioff + Zlength s <= Zlength ic ->
  0 <= lh -> 0 <= ls -> lh + ls <= Zlength s ->
  sublist (ioff + lh) (ioff + lh + ls) ic = zbytes (slice s lh ls).
Proof.
  intros Hw Ho Hi Hlh Hls Hn. rewrite lit_slice by lia. rewrite <- sublist_map, <- Hw.
  rewrite sublist_sublist by lia. f_equal; lia.
Qed.

Lemma lit_bytes_slice (s: list Z) (i k: Z) :
  bytes_ok s -> 0 <= i -> 0 <= k -> i + k <= Zlength s -> bytes_ok (slice s i k).
Proof. intros. rewrite lit_slice by lia. unfold bytes_ok in *. apply Forall_sublist. auto. Qed.

(* where ZSTD_allocateLiteralsBuffer put them *)
Lemma lit_alloc_cases (streaming cap bsm n: Z) :
  (alloc_loc streaming cap bsm n = LOC_IN_DST /\ streaming = 0 /\ bsm + 32 + n + 32 < cap) \/
  (alloc_loc streaming cap bsm n = LOC_NOT_IN_DST /\ n <= 65536) \/
  (alloc_loc streaming cap bsm n = LOC_SPLIT /\ 65536 < n).
Proof.
  unfold alloc_loc, WILDCOPY_OVERLENGTH, LITBUFFEREXTRASIZE.
  destruct (streaming =? 0) eqn:E1; destruct (bsm + 32 + n + 32 <? cap) eqn:E2; simpl;
    try (left; apply Z.eqb_eq in E1; apply Z.ltb_lt in E2; auto; fail);
    (destruct (n <=? 65536) eqn:E3; [right; left; apply Z.leb_le in E3; auto
                                    | right; right; apply Z.leb_gt in E3; auto]).
Qed.

(* litExtraBuffer as a byte array *)
Lemma lit_xb_eq (v: list val) (p: val) :
  field_at Ews t_dctx (DOT _litExtraBuffer) v p = data_at Ews (tarray tuchar LITEXTRA_N) v (lit_extra p).
Proof. rewrite field_at_data_at. reflexivity. Qed.

Lemma lit_xb_eq_ (p: val) :
  field_at_ Ews t_dctx (DOT _litExtraBuffer) p = data_at_ Ews (tarray tuchar LITEXTRA_N) (lit_extra p).
Proof. unfold field_at_, data_at_. rewrite field_at_data_at. reflexivity. Qed.

Lemma lit_xb_fc (p: val) :
  field_compatible t_dctx (DOT _litExtraBuffer) p -> field_compatible (tarray tuchar LITEXTRA_N) [] (lit_extra p).
Proof.
  intros H. unfold lit_extra. rewrite field_address_offset by auto.
  apply (field_compatible_nested_field _ _ _ H).
Qed.

(* a byte array: the first k cells, any contents after them *)
Lemma lit_arr_split_ (sh: share) (N k: Z) (q: val) :
  0 <= k <= N -> field_compatible (tarray tuchar N) [] q ->
  data_at_ sh (tarray tuchar N) q = (data_at_ sh (tarray tuchar k) q * data_at_ sh (tarray tuchar (N - k)) (offset_val k q))%logic.
Proof.
  intros Hk FC. unfold tarray. rewrite (split2_data_at__Tarray_tuchar sh N k q) by (auto; destruct FC; auto).
  change (Tarray tuchar N noattr) with (tarray tuchar N). rewrite arr_field_address0 by (auto; lia).
  simpl sizeof. rewrite Z.mul_1_l. reflexivity.
Qed.

Lemma lit_arr_join (sh: share) (N k: Z) (v: list val) (q: val) :
  Zlength v = k -> 0 <= k <= N -> field_compatible (tarray tuchar N) [] q ->
  data_at sh (tarray tuchar k) v q * data_at_ sh (tarray tuchar (N - k)) (offset_val k q)
  |-- data_at sh (tarray tuchar N) (v ++ Zrepeat Vundef (N - k)) q.
Proof.
  intros Hv Hk FC. rewrite (split2_data_at_Tarray_app k N sh tuchar v (Zrepeat Vundef (N - k)) q)
    by (auto; rewrite Zlength_Zrepeat; lia).
  rewrite arr_field_address0 by (auto; lia). simpl sizeof. rewrite Z.mul_1_l.
  unfold data_at_. apply derives_refl.
Qed.

(* a byte array as three pieces *)
Lemma lit_split3 (sh: share) (n i k: Z) (l: list val) (q: val) :
  0 <= i -> 0 <= k -> i + k <= n -> Zlength l = n ->
  field_compatible (tarray tuchar n) [] q ->
  data_at sh (tarray tuchar n) l q =
  (data_at sh (tarray tuchar i) (sublist 0 i l) q *
   data_at sh (tarray tuchar k) (sublist i (i + k) l) (offset_val i q) *
   data_at sh (tarray tuchar (n - (i + k))) (sublist (i + k) n l) (offset_val (i + k) q))%logic.
Proof.
  intros. rewrite (split3_data_at_Tarray_tuchar sh n i (i + k)) by lia.
  change (Tarray tuchar n noattr) with (tarray tuchar n). rewrite !arr_field_address0 by (auto; lia).
  replace (i + k - i) with k by lia. simpl sizeof. rewrite !Z.mul_1_l. reflexivity.
Qed.

(* a piece of a byte array replaced *)
Lemma lit_join3 (sh: share) (N i k: Z) (c v: list val) (q: val) :
  0 <= i -> 0 <= k -> i + k <= N -> Zlength c = N -> Zlength v = k ->
  field_compatible (tarray tuchar N) [] q ->
  data_at sh (tarray tuchar i) (sublist 0 i c) q *
  data_at sh (tarray tuchar k) v (offset_val i q) *
  data_at sh (tarray tuchar (N - (i + k))) (sublist (i + k) N c) (offset_val (i + k) q)
  |-- data_at sh (tarray tuchar N) (sublist 0 i c ++ v ++ sublist (i + k) N c) q.
Proof.
  intros. rewrite (lit_split3 sh N i k (sublist 0 i c ++ v ++ sublist (i + k) N c) q) by (auto; list_solve).
  replace (sublist 0 i (sublist 0 i c ++ v ++ sublist (i + k) N c)) with (sublist 0 i c) by list_solve.
  replace (sublist i (i + k) (sublist 0 i c ++ v ++ sublist (i + k) N c)) with v by list_solve.
  replace (sublist (i + k) N (sublist 0 i c ++ v ++ sublist (i + k) N c)) with (sublist (i + k) N c)
    by list_solve.
  apply derives_refl.
Qed.

Lemma lit_join3_same (sh: share) (N i k: Z) (c: list val) (q: val) :
  0 <= i -> 0 <= k -> i + k <= N -> Zlength c = N ->
  field_compatible (tarray tuchar N) [] q ->
  data_at sh (tarray tuchar i) (sublist 0 i c) q *
  data_at sh (tarray tuchar k) (sublist i (i + k) c) (offset_val i q) *
  data_at sh (tarray tuchar (N - (i + k))) (sublist (i + k) N c) (offset_val (i + k) q)
  |-- data_at sh (tarray tuchar N) c q.
Proof. intros. rewrite (lit_split3 sh N i k c q) by auto. apply derives_refl. Qed.

Lemma lit_unch_mid (oc v: list val) (lo hi i k: Z) :
  lo <= i -> i + k <= hi -> 0 <= i -> 0 <= k -> i + k <= Zlength oc -> Zlength v = k ->
  unchanged_outside oc (sublist 0 i oc ++ v ++ sublist (i + k) (Zlength oc) oc) lo hi.
Proof.
  intros. intros j Hj Hn. destruct (Z_lt_ge_dec j i).
  - rewrite app_Znth1 by list_solve. rewrite Znth_sublist by lia. f_equal; lia.
  - rewrite app_Znth2 by list_solve. rewrite app_Znth2 by list_solve.
    rewrite Znth_sublist by list_solve. f_equal. list_solve.
Qed.

(* set_basic (raw literals, case 0) *)
(* pieces of the literals in the input window *)
Lemma lit_win_sub2 (ic: list val) (ioff lh ls a b: Z) (s: list Z) :
  sublist ioff (ioff + Zlength s) ic = zbytes s -> 0 <= ioff -> ioff + Zlength s <= Zlength ic ->
  0 <= lh -> 0 <= ls -> lh + ls <= Zlength s -> 0 <= a <= b -> b <= ls ->
  sublist (ioff + lh + a) (ioff + lh + b) ic = zbytes (sublist a b (slice s lh ls)).
Proof.
  intros Hw Ho Hi Hlh Hls Hn Hab Hb. rewrite <- sublist_map, <- (lit_win_sub ic ioff lh ls s) by auto.
  rewrite sublist_sublist by lia. f_equal; lia.
Qed.

(* litExtraBuffer with byte contents xl: take its first k cells for a copy, give them back *)
Lemma lit_xb_take (k: Z) (xl: list val) (p: val) :
  0 <= k <= LITEXTRA_N -> Zlength xl = LITEXTRA_N -> field_compatible t_dctx (DOT _litExtraBuffer) p ->
  field_at Ews t_dctx (DOT _litExtraBuffer) xl p
  |-- data_at_ Ews (tarray tuchar k) (lit_extra p) *
      data_at Ews (tarray tuchar (LITEXTRA_N - k)) (sublist k LITEXTRA_N xl) (offset_val k (lit_extra p)).
Proof.
  intros Hk Hl FC. rewrite lit_xb_eq. pose proof (lit_xb_fc p FC) as FC'.
  unfold tarray. rewrite (split2_data_at_Tarray_tuchar Ews LITEXTRA_N k xl (lit_extra p)) by auto.
  change (Tarray tuchar LITEXTRA_N noattr) with (tarray tuchar LITEXTRA_N).
  rewrite arr_field_address0 by (auto; lia). simpl sizeof. rewrite Z.mul_1_l.
  cancel; try apply data_at_data_at_.
Qed.

Lemma lit_xb_give (k: Z) (v xl: list val) (p: val) :
  Zlength v = k -> 0 <= k <= LITEXTRA_N -> Zlength xl = LITEXTRA_N ->
  field_compatible t_dctx (DOT _litExtraBuffer) p ->
  data_at Ews (tarray tuchar k) v (lit_extra p) *
  data_at Ews (tarray tuchar (LITEXTRA_N - k)) (sublist k LITEXTRA_N xl) (offset_val k (lit_extra p))
  |-- field_at Ews t_dctx (DOT _litExtraBuffer) (v ++ sublist k LITEXTRA_N xl) p.
Proof.
  intros Hv Hk Hl FC. rewrite lit_xb_eq. pose proof (lit_xb_fc p FC) as FC'.
  rewrite (split2_data_at_Tarray_app k LITEXTRA_N Ews tuchar v (sublist k LITEXTRA_N xl) (lit_extra p))
    by (first [exact Hv | rewrite Zlength_sublist by lia; lia | list_solve]).
  rewrite arr_field_address0 by (auto; lia). simpl sizeof. rewrite Z.mul_1_l.
  apply derives_refl.
Qed.

Lemma lit_bc_sub (l: list val) (i j: Z) : byte_cells l -> byte_cells (sublist i j l).
Proof. unfold byte_cells. apply Forall_sublist. Qed.

Lemma lit_bc_mid (oc ic: list val) (i a b j n: Z) :
  byte_cells oc -> byte_cells ic -> byte_cells (sublist 0 i oc ++ sublist a b ic ++ sublist j n oc).
Proof.
  intros Ho Hi. unfold byte_cells in *. apply Forall_app; split; [apply Forall_sublist; auto |].
  apply Forall_app; split; apply Forall_sublist; auto.
Qed.

Lemma lit_unch_mid_r (oc x: list val) (lb m lo hi: Z) :
  0 <= lb -> lb + m <= Zlength oc -> lo <= lb -> lb + m <= hi -> Zlength x = m ->
  unchanged_outside oc (sublist 0 lb oc ++ x ++ sublist (lb + m) (Zlength oc) oc) lo hi.
Proof.
  intros H1 H2 H3 H4 H5 k Hk Hn. pose proof (Zlength_nonneg x).
  destruct (Z_lt_le_dec k lb).
  - rewrite app_Znth1 by list_solve. list_solve.
  - rewrite app_Znth2 by list_solve. rewrite app_Znth2 by list_solve. list_solve.
Qed.

Lemma lit_bc_sub_r (l: list val) (a b: Z) : byte_cells l -> byte_cells (sublist a b l).
Proof. intros H. unfold byte_cells in *. apply Forall_sublist. exact H. Qed.

Lemma lit_bc_rep (v k: Z) : 0 <= v < 256 -> byte_cells (Zrepeat (Vint (Int.repr v)) k).
Proof.
  intros H. unfold byte_cells, Zrepeat. apply Forall_repeat. exists v. split; [lia | reflexivity].
Qed.

Lemma lit_bc_mid_r (oc: list val) (a b k v: Z) : byte_cells oc -> 0 <= v < 256 ->
  byte_cells (sublist 0 a oc ++ Zrepeat (Vint (Int.repr v)) k ++ sublist b (Zlength oc) oc).
Proof.
  intros H Hv. unfold byte_cells. apply Forall_app. split; [apply (lit_bc_sub_r oc 0 a H) |].
  apply Forall_app. split; [apply (lit_bc_rep v k Hv) | apply (lit_bc_sub_r oc b (Zlength oc) H)].
Qed.

(* a defined cell of oc stays defined in oc' (the post's last conjunct: every write is a defined byte) *)
Definition lit_dk (oc oc': list val) : Prop :=
  forall j, 0 <= j < Zlength oc -> is_byte_val (Znth j oc) -> is_byte_val (Znth j oc').

Lemma lit_dk_refl (oc: list val) : lit_dk oc oc.
Proof. intros j _ H. exact H. Qed.

Lemma lit_dk_trans (oc oc1 oc2: list val) :
  Zlength oc1 = Zlength oc -> lit_dk oc oc1 -> lit_dk oc1 oc2 -> lit_dk oc oc2.
Proof. intros HL D1 D2 j Hj H. apply D2; [lia | apply D1; auto]. Qed.

(* oc' differs from oc only in [lo, hi), where it holds defined bytes *)
Lemma lit_dk_unch (oc oc': list val) (lo hi: Z) :
  0 <= lo <= hi -> hi <= Zlength oc -> Zlength oc' = Zlength oc -> unchanged_outside oc oc' lo hi ->
  Forall is_byte_val (sublist lo hi oc') -> lit_dk oc oc'.
Proof.
  intros Hl Hh HL U F j Hj H.
  destruct (Z_lt_le_dec j lo) as [J | J]; [rewrite U by (auto; lia); exact H |].
  destruct (Z_lt_le_dec j hi) as [J2 | J2]; [| rewrite U by (auto; lia); exact H].
  rewrite Forall_forall in F. replace (Znth j oc') with (Znth (j - lo) (sublist lo hi oc')) by list_solve.
  apply F. apply Znth_In. list_solve.
Qed.

(* the m cells at k replaced by defined bytes v *)
Lemma lit_dk_mid (oc v: list val) (k m: Z) :
  0 <= k -> k + m <= Zlength oc -> Zlength v = m -> Forall is_byte_val v ->
  lit_dk oc (sublist 0 k oc ++ v ++ sublist (k + m) (Zlength oc) oc).
Proof.
  intros Hk Hn Hv F. pose proof (Zlength_nonneg v).
  apply (lit_dk_unch _ _ k (k + m)); try lia.
  - list_solve.
  - apply lit_unch_mid_r; auto; lia.
  - replace (sublist k (k + m) (sublist 0 k oc ++ v ++ sublist (k + m) (Zlength oc) oc)) with v
      by list_solve. exact F.
Qed.

Lemma lit_bv_rep (v k: Z) : 0 <= v < 256 -> Forall is_byte_val (Zrepeat (Vint (Int.repr v)) k).
Proof. intros H. apply Forall_repeat. exists v. split; [lia | reflexivity]. Qed.

Lemma lit_bv_zbytes (l: list Z) : bytes_ok l -> Forall is_byte_val (zbytes l).
Proof. intros H. induction H; simpl; constructor; auto. exists x. unfold is_byte in H. split; [lia | reflexivity]. Qed.

(* what ZSTD_allocateLiteralsBuffer does to the output array *)
Lemma lit_alloc_out (oc: list val) (streaming cap bsm n d split: Z) :
  0 <= d -> d + cap <= Zlength oc -> 0 <= n <= Z.min bsm cap ->
  Zlength (alloc_out oc streaming cap bsm n d (Z.min bsm cap) split) = Zlength oc /\
  unchanged_outside oc (alloc_out oc streaming cap bsm n d (Z.min bsm cap) split) d (d + cap) /\
  (streaming = 1 ->
     unchanged_outside oc (alloc_out oc streaming cap bsm n d (Z.min bsm cap) split) d (d + Z.min cap bsm)) /\
  (byte_cells oc -> byte_cells (alloc_out oc streaming cap bsm n d (Z.min bsm cap) split)) /\
  lit_dk oc (alloc_out oc streaming cap bsm n d (Z.min bsm cap) split) /\
  (alloc_loc streaming cap bsm n = LOC_IN_DST ->
     Forall is_byte_val (sublist (d + bsm + WILDCOPY_OVERLENGTH + n)
                          (d + bsm + WILDCOPY_OVERLENGTH + n + WILDCOPY_OVERLENGTH)
                          (alloc_out oc streaming cap bsm n d (Z.min bsm cap) split))) /\
  (alloc_loc streaming cap bsm n = LOC_SPLIT -> split = 1 ->
     Forall is_byte_val (sublist (d + Z.min bsm cap - WILDCOPY_OVERLENGTH) (d + Z.min bsm cap)
                          (alloc_out oc streaming cap bsm n d (Z.min bsm cap) split))) /\
  (alloc_loc streaming cap bsm n = LOC_NOT_IN_DST \/ (alloc_loc streaming cap bsm n = LOC_SPLIT /\ split <> 1) ->
     alloc_out oc streaming cap bsm n d (Z.min bsm cap) split = oc).
Proof.
  intros Hd Hc Hn.
  assert (Z32: Zlength (Zrepeat (Vint (Int.repr 0)) WILDCOPY_OVERLENGTH) = WILDCOPY_OVERLENGTH)
    by (rewrite Zlength_Zrepeat; unfold WILDCOPY_OVERLENGTH; lia).
  assert (B32: Forall is_byte_val (Zrepeat (Vint (Int.repr 0)) WILDCOPY_OVERLENGTH)) by (apply lit_bv_rep; lia).
  destruct (lit_alloc_cases streaming cap bsm n) as [(HL & Hs & Hr) | [(HL & Hs) | (HL & Hs)]];
    unfold alloc_out, alloc_slack; rewrite HL; unfold LOC_IN_DST, LOC_NOT_IN_DST, LOC_SPLIT in *;
    cbn [Z.eqb Pos.eqb].
  - set (k := d + bsm + WILDCOPY_OVERLENGTH + n). set (z := Zrepeat (Vint (Int.repr 0)) WILDCOPY_OVERLENGTH) in *.
    unfold WILDCOPY_OVERLENGTH in *.
    assert (Hk: d <= k /\ k + 32 < d + cap) by (unfold k; lia).
    split; [list_solve |]. split; [apply lit_unch_mid_r; auto; lia |].
    split; [intros; lia |]. split; [intros BC; apply lit_bc_mid_r; auto; lia |].
    split; [apply lit_dk_mid; auto; lia |].
    split; [intros _; replace (sublist k (k + 32) _) with z by list_solve; exact B32 |].
    split; [intros; lia |]. intros [E | [E _]]; lia.
  - repeat split; auto using lit_unch, lit_dk_refl; intros; lia.
  - destruct (split =? 1) eqn:Es.
    + apply Z.eqb_eq in Es. subst split.
      set (k := d + Z.min bsm cap - WILDCOPY_OVERLENGTH).
      set (z := Zrepeat (Vint (Int.repr 0)) WILDCOPY_OVERLENGTH) in *.
      unfold WILDCOPY_OVERLENGTH in *.
      assert (Hk: d <= k /\ k + 32 <= d + Z.min bsm cap) by (unfold k; lia).
      split; [list_solve |]. split; [apply lit_unch_mid_r; auto; lia |].
      split; [intros _; apply lit_unch_mid_r; auto; try lia; rewrite Z.min_comm; lia |].
      split; [intros BC; apply lit_bc_mid_r; auto; lia |].
      split; [apply lit_dk_mid; auto; lia |].
      split; [intros; lia |].
      split; [intros _ _; replace (d + Z.min bsm cap) with (k + 32) by (unfold k; lia);
              replace (sublist k (k + 32) _) with z by list_solve; exact B32 |].
      intros [E | [_ E]]; lia.
    + apply Z.eqb_neq in Es.
      repeat split; auto using lit_unch, lit_dk_refl; intros; lia.
Qed.

Lemma lit_unch_mono (oc oc1: list val) (a b a' b': Z) :
  a' <= a -> b <= b' -> unchanged_outside oc oc1 a b -> unchanged_outside oc oc1 a' b'.
Proof. intros H1 H2 U k Hk Hn. apply U; auto; lia. Qed.

Lemma lit_unch_trans (oc oc1 oc2: list val) (a b: Z) :
  Zlength oc1 = Zlength oc ->
  unchanged_outside oc oc1 a b -> unchanged_outside oc1 oc2 a b -> unchanged_outside oc oc2 a b.
Proof. intros HL U1 U2 k Hk Hn. rewrite U2 by (auto; lia). apply U1; auto. Qed.

(* the input window holds defined bytes (what the raw-literals memcpy copies) *)
Lemma lit_win_bv (ic: list val) (ioff a b: Z) (s: list Z) :
  sublist ioff (ioff + Zlength s) ic = zbytes s -> bytes_ok s -> 0 <= ioff -> ioff + Zlength s <= Zlength ic ->
  ioff <= a <= b -> b <= ioff + Zlength s -> Forall byte_val (sublist a b ic).
Proof.
  intros Hw Hb Ho Hn Ha Hb2.
  replace (sublist a b ic) with (sublist (a - ioff) (b - ioff) (sublist ioff (ioff + Zlength s) ic))
    by (rewrite sublist_sublist by lia; f_equal; lia).
  rewrite Hw. apply Forall_sublist. apply byte_val_zbytes. exact Hb.
Qed.

(* a piece of the array after ZSTD_allocateLiteralsBuffer (oc1, from oc) replaced: the post's facts about oc *)
Lemma lit_unch_after (oc oc1 v: list val) (i k lo hi: Z) :
  Zlength oc1 = Zlength oc -> unchanged_outside oc oc1 lo hi -> lo <= i -> i + k <= hi -> 0 <= i ->
  i + k <= Zlength oc -> Zlength v = k ->
  unchanged_outside oc (sublist 0 i oc1 ++ v ++ sublist (i + k) (Zlength oc) oc1) lo hi.
Proof.
  intros HL U Hl Hh Hi Hn Hv. pose proof (Zlength_nonneg v).
  apply (lit_unch_trans oc oc1); auto. rewrite <- HL.
  apply lit_unch_mid_r; auto; lia.
Qed.

Lemma lit_dk_after (oc oc1 v: list val) (i k: Z) :
  Zlength oc1 = Zlength oc -> lit_dk oc oc1 -> 0 <= i -> i + k <= Zlength oc -> Zlength v = k ->
  Forall is_byte_val v -> lit_dk oc (sublist 0 i oc1 ++ v ++ sublist (i + k) (Zlength oc) oc1).
Proof.
  intros HL D Hi Hn Hv F. apply (lit_dk_trans oc oc1); auto. rewrite <- HL.
  apply lit_dk_mid; auto; lia.
Qed.


(* ---------- the literals headers (pure) ---------- *)

(* set_rle's header: lhlCode, lhSize, litSize *)
Definition rle_lhl (s: list Z) : Z := Z.land (Z.shiftr (byte_at s 0) 2) 3.
Definition rle_lh (s: list Z) : Z := if rle_lhl s =? 1 then 2 else if rle_lhl s =? 3 then 3 else 1.
Definition rle_ls (s: list Z) : Z :=
  if rle_lhl s =? 1 then Z.shiftr (le_field s 0 2) 4
  else if rle_lhl s =? 3 then Z.shiftr (le_field s 0 3) 4 else Z.shiftr (byte_at s 0) 3.

(* set_compressed / set_repeat's header: (lhSize, litSize, litCSize, singleStream) *)
Definition lit_hdr (s: list Z) : Z * Z * Z * bool :=
  let lhl := Z.land (Z.shiftr (byte_at s 0) 2) 3 in
  let lhc := le_field s 0 4 in
  if lhl =? 2 then (4, Z.land (Z.shiftr lhc 4) 16383, Z.shiftr lhc 18, false)
  else if lhl =? 3 then (5, Z.land (Z.shiftr lhc 4) 262143, Z.shiftr lhc 22 + byte_at s 4 * 1024, false)
  else (3, Z.land (Z.shiftr lhc 4) 1023, Z.land (Z.shiftr lhc 14) 1023, lhl =? 0).

(* the array c with the cells v stored from index k on (a memcpy / memset / memmove into an array) *)
Definition cwr (c: list val) (k: Z) (v: list val) : list val :=
  sublist 0 k c ++ v ++ sublist (k + Zlength v) (Zlength c) c.
