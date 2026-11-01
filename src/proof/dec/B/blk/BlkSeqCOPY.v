(* Sub-group COPY of SEQ (BlkGroups.ids_SEQ): the five byte/struct copy helpers used by the sequence
   executors and loops, their funspecs (COPY_exports, on the forward-copy model listcopy) and the proofs of
   their bodies (COPY_ok).

     ZSTD_wildcopy, ZSTD_seqCopy, ZSTD_overlapCopy8, ZSTD_safecopy, ZSTD_safecopyDstBeforeSrc

   ZSTD_copy4/8/16, memcpy, memmove are already in G_BLK (Spec_util, LibcSpec).  memcpy and memmove are the
   byte loops of QuickProof's libc.c, so every byte these helpers copy must be a defined byte: the
   preconditions say which source cells are defined (copy_src_def and its variants). *)
Require Export Zstd.proof.dec.B.blk.BlkSeqXMem.
Local Open Scope logic.

(* WILDCOPY_VECLEN (the 16-byte copy unit); WILDCOPY_OVERLENGTH = 32 is in DecRep. *)
Definition WILDCOPY_VECLEN : Z := 16.

(* The two overlap tags (ZSTD_overlap_e): ZSTD_no_overlap = 0, ZSTD_overlap_src_before_dst = 1. *)
Definition OV_NO_OVERLAP : Z := 0.
Definition OV_SRC_BEFORE_DST : Z := 1.

(* ------------------------------------------------------------------ *)
(* The forward, left-to-right byte copy of n bytes within one array: write c[di+j] := (current c)[si+j]
   for j = 0..n-1 in order, so a write at di+j may be read back at si+j' for j' > j when the ranges
   overlap (si < di).  This is what ZSTD_wildcopy / ZSTD_safecopy / ZSTD_overlapCopy8 produce; the LZ
   match copy (Block.lz_copy) is the instance si = di - offset (proved in EXEC). *)
Fixpoint listcopy (c: list val) (si di: Z) (n: nat) : list val :=
  match n with
  | O => c
  | S m => listcopy (upd_Znth di c (Znth si c)) (si + 1) (di + 1) m
  end.

Lemma listcopy_Zlength (c: list val) (si di: Z) (n: nat) :
  0 <= di -> di + Z.of_nat n <= Zlength c -> Zlength (listcopy c si di n) = Zlength c.
Proof.
  revert c si di. induction n as [|m IH]; intros c si di Hdi Hn; simpl; [reflexivity|].
  rewrite Nat2Z.inj_succ in Hn.
  assert (Hu: Zlength (upd_Znth di c (Znth si c)) = Zlength c) by (apply Zlength_upd_Znth).
  rewrite IH; [ exact Hu | lia | rewrite Hu; lia ].
Qed.

(* The bytes outside [di, di+n) are unchanged by listcopy. *)
Lemma listcopy_outside (c: list val) (si di: Z) (n: nat) (k: Z) :
  0 <= di -> di + Z.of_nat n <= Zlength c -> 0 <= k < Zlength c -> ~ (di <= k < di + Z.of_nat n) ->
  Znth k (listcopy c si di n) = Znth k c.
Proof.
  revert c si di. induction n as [|m IH]; intros c si di Hdi Hn Hk Hout; simpl; [reflexivity|].
  rewrite Nat2Z.inj_succ in Hn.
  assert (Hu: Zlength (upd_Znth di c (Znth si c)) = Zlength c) by (apply Zlength_upd_Znth).
  rewrite IH.
  - rewrite upd_Znth_diff; [reflexivity | lia | lia | lia].
  - lia.
  - rewrite Hu; lia.
  - rewrite Hu; lia.
  - lia.
Qed.


(* ---------- listcopy algebra (helpers for the five bodies) ---------- *)
Lemma listcopy_add (c: list val) (si di: Z) (a b: nat) :
  listcopy c si di (a + b) = listcopy (listcopy c si di a) (si + Z.of_nat a) (di + Z.of_nat a) b.
Proof.
  revert c si di. induction a as [|a IH]; intros c si di; simpl.
  - rewrite !Z.add_0_r. reflexivity.
  - rewrite IH. f_equal; lia.
Qed.

Lemma listcopy_snoc (c: list val) (si di: Z) (k: nat) :
  listcopy c si di (S k) =
  upd_Znth (di + Z.of_nat k) (listcopy c si di k) (Znth (si + Z.of_nat k) (listcopy c si di k)).
Proof.
  replace (S k) with (k + 1)%nat by lia. rewrite listcopy_add. reflexivity.
Qed.

(* a copy whose source and destination ranges are disjoint is a block replacement *)
Lemma listcopy_disj (l: list val) (s d m: Z) :
  0 <= m -> 0 <= s -> s + m <= Zlength l -> 0 <= d -> d + m <= Zlength l -> (s + m <= d \/ d + m <= s) ->
  listcopy l s d (Z.to_nat m) = sublist 0 d l ++ sublist s (s + m) l ++ sublist (d + m) (Zlength l) l.
Proof.
  intros Hm Hs Hsm Hd Hdm Hdisj.
  rewrite <- (Z2Nat.id m) in Hsm, Hdm, Hdisj |- * by lia.
  set (k := Z.to_nat m) in *. clearbody k. rewrite Nat2Z.id. clear Hm.
  induction k as [|k IH].
  - simpl. autorewrite with sublist. reflexivity.
  - rewrite listcopy_snoc, IH by lia. rewrite Nat2Z.inj_succ in *.
    assert (HL: Zlength (sublist 0 d l ++ sublist s (s + Z.of_nat k) l ++
                         sublist (d + Z.of_nat k) (Zlength l) l) = Zlength l) by list_solve.
    apply Znth_eq_ext. { rewrite Zlength_upd_Znth. list_solve. }
    intros i Hi. rewrite Zlength_upd_Znth, HL in Hi.
    destruct (Z.eq_dec i (d + Z.of_nat k)) as [->|Hne].
    + rewrite upd_Znth_same by list_solve. list_solve.
    + rewrite upd_Znth_diff by list_solve. list_solve.
Qed.

(* listcopy beyond n only changes positions >= di + n *)
Lemma listcopy_prefix (c: list val) (si di: Z) (n E: Z) :
  0 <= di -> 0 <= n <= E -> di + E <= Zlength c ->
  sublist 0 (di + n) (listcopy c si di (Z.to_nat E)) = sublist 0 (di + n) (listcopy c si di (Z.to_nat n)).
Proof.
  intros. replace (Z.to_nat E) with (Z.to_nat n + Z.to_nat (E - n))%nat by lia.
  rewrite listcopy_add. rewrite !Z2Nat.id by lia.
  assert (HL: Zlength (listcopy c si di (Z.to_nat n)) = Zlength c) by (apply listcopy_Zlength; lia).
  apply Znth_eq_ext. { rewrite !Zlength_sublist; try lia; rewrite ?listcopy_Zlength; try lia; rewrite ?Z2Nat.id; lia. }
  intros i Hi. rewrite Zlength_sublist in Hi; [| lia | rewrite listcopy_Zlength; rewrite ?Z2Nat.id; lia].
  rewrite !Znth_sublist by (try lia; rewrite ?listcopy_Zlength; rewrite ?Z2Nat.id; lia).
  rewrite Z.add_0_r. apply listcopy_outside; rewrite ?HL, ?Z2Nat.id; lia.
Qed.

Lemma listcopy_suffix (c: list val) (si di: Z) (E k: Z) :
  0 <= di -> 0 <= E -> di + E <= Zlength c -> 0 <= k < Zlength c -> ~ (di <= k < di + E) ->
  Znth k (listcopy c si di (Z.to_nat E)) = Znth k c.
Proof. intros. apply listcopy_outside; rewrite ?Z2Nat.id; lia. Qed.

Lemma Zlength_listcopy (c: list val) (si di E: Z) :
  0 <= di -> 0 <= E -> di + E <= Zlength c -> Zlength (listcopy c si di (Z.to_nat E)) = Zlength c.
Proof. intros. apply listcopy_Zlength; rewrite ?Z2Nat.id; lia. Qed.


(* ---------- splitting a byte array into two separately held pieces (for ZSTD_copy4/8/16) ---------- *)
Lemma tuchar_join (sh: share) (p: val) (N: Z) (a b: list val) :
  field_compatible (tarray tuchar N) [] p -> Zlength a + Zlength b = N ->
  data_at sh (tarray tuchar (Zlength a)) a p *
  data_at sh (tarray tuchar (Zlength b)) b (offset_val (Zlength a) p) =
  data_at sh (tarray tuchar N) (a ++ b) p.
Proof.
  intros Hfc HN.
  rewrite (split2_data_at_Tarray_tuchar sh N (Zlength a) (a ++ b)) by list_solve.
  change (Tarray tuchar N noattr) with (tarray tuchar N).
  rewrite arr_field_address0 by (auto; list_solve).
  replace (N - Zlength a) with (Zlength b) by lia.
  replace (sublist 0 (Zlength a) (a ++ b)) with a by list_solve.
  replace (sublist (Zlength a) N (a ++ b)) with b by list_solve.
  simpl sizeof. rewrite Z.mul_1_l. reflexivity.
Qed.

Lemma tuchar_split (sh: share) (p: val) (l: list val) (d: Z) :
  field_compatible (tarray tuchar (Zlength l)) [] p -> 0 <= d <= Zlength l ->
  data_at sh (tarray tuchar (Zlength l)) l p =
  data_at sh (tarray tuchar (Zlength (sublist 0 d l))) (sublist 0 d l) p *
  data_at sh (tarray tuchar (Zlength (sublist d (Zlength l) l))) (sublist d (Zlength l) l) (offset_val d p).
Proof.
  intros Hfc Hd.
  replace (offset_val d p) with (offset_val (Zlength (sublist 0 d l)) p) by (f_equal; list_solve).
  rewrite (tuchar_join sh p (Zlength l)) by (auto; list_solve).
  rewrite sublist_rejoin, sublist_same by lia. reflexivity.
Qed.


(* a chunk copy inside one array, source before destination: split at d, copy, rejoin *)
Lemma within_copy_sb (sh: share) (p: val) (l: list val) (s d m: Z) :
  field_compatible (tarray tuchar (Zlength l)) [] p ->
  0 <= m -> 0 <= s -> s + m <= d -> d + m <= Zlength l ->
  data_at sh (tarray tuchar (Zlength (sublist 0 d l))) (sublist 0 d l) p *
  data_at sh (tarray tuchar (Zlength (sublist d (Zlength l) l)))
    (copied (sublist 0 d l) (sublist d (Zlength l) l) s 0 m) (offset_val d p) =
  data_at sh (tarray tuchar (Zlength l)) (listcopy l s d (Z.to_nat m)) p.
Proof.
  intros Hfc Hm Hs Hsd Hdl.
  replace (offset_val d p) with (offset_val (Zlength (sublist 0 d l)) p) by (f_equal; list_solve).
  replace (Zlength (sublist d (Zlength l) l))
    with (Zlength (copied (sublist 0 d l) (sublist d (Zlength l) l) s 0 m))
    by (unfold copied; list_solve).
  rewrite (tuchar_join sh p (Zlength l)) by (auto; unfold copied; list_solve).
  rewrite listcopy_disj by lia. unfold copied. f_equal. list_solve.
Qed.

(* destination before source: split at s *)
Lemma within_copy_ds (sh: share) (p: val) (l: list val) (s d m: Z) :
  field_compatible (tarray tuchar (Zlength l)) [] p ->
  0 <= m -> 0 <= d -> d + m <= s -> s + m <= Zlength l ->
  data_at sh (tarray tuchar (Zlength (sublist s (Zlength l) l))) (sublist s (Zlength l) l) (offset_val s p) *
  data_at sh (tarray tuchar (Zlength (sublist 0 s l)))
    (copied (sublist s (Zlength l) l) (sublist 0 s l) 0 d m) p =
  data_at sh (tarray tuchar (Zlength l)) (listcopy l s d (Z.to_nat m)) p.
Proof.
  intros Hfc Hm Hd Hds Hsl.
  rewrite sepcon_comm.
  replace (offset_val s p) with (offset_val (Zlength (copied (sublist s (Zlength l) l) (sublist 0 s l) 0 d m)) p)
    by (f_equal; unfold copied; list_solve).
  replace (Zlength (sublist 0 s l))
    with (Zlength (copied (sublist s (Zlength l) l) (sublist 0 s l) 0 d m))
    by (unfold copied; list_solve).
  rewrite (tuchar_join sh p (Zlength l)) by (auto; unfold copied; list_solve).
  rewrite listcopy_disj by lia. unfold copied. f_equal. list_solve.
Qed.


(* the same, as entailments on an array of declared length N (for sep_apply) *)
Lemma tuchar_split_N (sh: share) (p: val) (N: Z) (l: list val) (d: Z) :
  Zlength l = N -> field_compatible (tarray tuchar N) [] p -> 0 <= d <= N ->
  data_at sh (tarray tuchar N) l p |--
  data_at sh (tarray tuchar (Zlength (sublist 0 d l))) (sublist 0 d l) p *
  data_at sh (tarray tuchar (Zlength (sublist d (Zlength l) l))) (sublist d (Zlength l) l) (offset_val d p).
Proof. intros <- Hfc Hd. rewrite (tuchar_split sh p l d) by auto. apply derives_refl. Qed.

Lemma within_copy_sb_N (sh: share) (p: val) (N: Z) (l: list val) (s d m: Z) :
  Zlength l = N -> field_compatible (tarray tuchar N) [] p ->
  0 <= m -> 0 <= s -> s + m <= d -> d + m <= N ->
  data_at sh (tarray tuchar (Zlength (sublist 0 d l))) (sublist 0 d l) p *
  data_at sh (tarray tuchar (Zlength (sublist d (Zlength l) l)))
    (copied (sublist 0 d l) (sublist d (Zlength l) l) s 0 m) (offset_val d p) |--
  data_at sh (tarray tuchar N) (listcopy l s d (Z.to_nat m)) p.
Proof. intros <- Hfc. intros. rewrite within_copy_sb by auto. apply derives_refl. Qed.

Lemma within_copy_ds_N (sh: share) (p: val) (N: Z) (l: list val) (s d m: Z) :
  Zlength l = N -> field_compatible (tarray tuchar N) [] p ->
  0 <= m -> 0 <= d -> d + m <= s -> s + m <= N ->
  data_at sh (tarray tuchar (Zlength (sublist s (Zlength l) l))) (sublist s (Zlength l) l) (offset_val s p) *
  data_at sh (tarray tuchar (Zlength (sublist 0 s l)))
    (copied (sublist s (Zlength l) l) (sublist 0 s l) 0 d m) p |--
  data_at sh (tarray tuchar N) (listcopy l s d (Z.to_nat m)) p.
Proof. intros <- Hfc. intros. rewrite within_copy_ds by auto. apply derives_refl. Qed.


Lemma listcopy_step (c: list val) (si di k m: Z) :
  0 <= k -> 0 <= m ->
  listcopy (listcopy c si di (Z.to_nat k)) (si + k) (di + k) (Z.to_nat m) = listcopy c si di (Z.to_nat (k + m)).
Proof.
  intros. replace (Z.to_nat (k + m)) with (Z.to_nat k + Z.to_nat m)%nat by lia.
  rewrite listcopy_add, Z2Nat.id by lia. reflexivity.
Qed.

(* one chunk of a forward copy inside one array, as the separately held pieces ZSTD_copy4/8/16 see *)
Lemma within_step_sb (sh: share) (p: val) (c: list val) (si di k m: Z) :
  field_compatible (tarray tuchar (Zlength c)) [] p ->
  0 <= k -> 0 <= m -> 0 <= di -> 0 <= si + k -> si + m <= di -> di + k + m <= Zlength c ->
  data_at sh (tarray tuchar (Zlength (sublist 0 (di + k) (listcopy c si di (Z.to_nat k))))) (sublist 0 (di + k) (listcopy c si di (Z.to_nat k))) p *
  data_at sh (tarray tuchar (Zlength (sublist (di + k) (Zlength (listcopy c si di (Z.to_nat k))) (listcopy c si di (Z.to_nat k)))))
    (copied (sublist 0 (di + k) (listcopy c si di (Z.to_nat k))) (sublist (di + k) (Zlength (listcopy c si di (Z.to_nat k))) (listcopy c si di (Z.to_nat k))) (si + k) 0 m) (offset_val (di + k) p) |--
  data_at sh (tarray tuchar (Zlength c)) (listcopy c si di (Z.to_nat (k + m))) p.
Proof.
  intros Hfc **.
  sep_apply (within_copy_sb_N sh p (Zlength c) (listcopy c si di (Z.to_nat k)) (si + k) (di + k) m);
    try (apply Zlength_listcopy); try lia; auto.
  rewrite listcopy_step by lia. apply derives_refl.
Qed.

Lemma within_step_ds (sh: share) (p: val) (c: list val) (si di k m: Z) :
  field_compatible (tarray tuchar (Zlength c)) [] p ->
  0 <= k -> 0 <= m -> 0 <= di -> di + m <= si -> si + k + m <= Zlength c -> di + k + m <= Zlength c ->
  data_at sh (tarray tuchar (Zlength (sublist (si + k) (Zlength (listcopy c si di (Z.to_nat k))) (listcopy c si di (Z.to_nat k))))) (sublist (si + k) (Zlength (listcopy c si di (Z.to_nat k))) (listcopy c si di (Z.to_nat k)))
    (offset_val (si + k) p) *
  data_at sh (tarray tuchar (Zlength (sublist 0 (si + k) (listcopy c si di (Z.to_nat k)))))
    (copied (sublist (si + k) (Zlength (listcopy c si di (Z.to_nat k))) (listcopy c si di (Z.to_nat k))) (sublist 0 (si + k) (listcopy c si di (Z.to_nat k))) 0 (di + k) m) p |--
  data_at sh (tarray tuchar (Zlength c)) (listcopy c si di (Z.to_nat (k + m))) p.
Proof.
  intros Hfc **.
  sep_apply (within_copy_ds_N sh p (Zlength c) (listcopy c si di (Z.to_nat k)) (si + k) (di + k) m);
    try (apply Zlength_listcopy); try lia; auto.
  rewrite listcopy_step by lia. apply derives_refl.
Qed.

(* the disjoint copy: after k bytes the destination is the source's prefix, the rest original *)
Lemma disj_step (cs cd: list val) (k m: Z) :
  0 <= k -> 0 <= m -> k + m <= Zlength cs -> k + m <= Zlength cd ->
  copied cs (sublist 0 k cs ++ sublist k (Zlength cd) cd) k k m =
  sublist 0 (k + m) cs ++ sublist (k + m) (Zlength cd) cd.
Proof. intros. unfold copied. list_solve. Qed.


(* ---------- pointer comparisons inside one byte array (as body6_xxh_oneshot's eo_cmp / eo_test_order) ---------- *)
Lemma cp_cmp (n: Z) (p: val) (i j: Z) :
  field_compatible (tarray tuchar n) [] p -> 0 <= i <= n -> 0 <= j <= n ->
  sem_cmp_pp Clt (offset_val i p) (offset_val j p) = Some (Vint (if zlt i j then Int.one else Int.zero)).
Proof.
  intros FC Hi Hj. destruct FC as [Pp [_ [Hs _]]]. destruct p; try contradiction.
  simpl in Hs. rewrite Z.max_r in Hs by lia. pose proof (Ptrofs.unsigned_range i0).
  unfold sem_cmp_pp. simpl.
  rewrite if_true by auto. simpl. f_equal. unfold Ptrofs.ltu, Ptrofs.add.
  rewrite (Ptrofs.unsigned_repr i), (Ptrofs.unsigned_repr j) by rep_lia.
  rewrite !Ptrofs.unsigned_repr by rep_lia.
  destruct (zlt (Ptrofs.unsigned i0 + i) (Ptrofs.unsigned i0 + j)), (zlt i j); try reflexivity; lia.
Qed.

Lemma cp_test_order (sh: share) (n: Z) (c: list val) (p: val) (i j: Z) (R: mpred) :
  readable_share sh -> field_compatible (tarray tuchar n) [] p ->
  0 <= i <= n -> 0 <= j <= n -> 0 < n ->
  data_at sh (tarray tuchar n) c p * R |-- denote_tc_test_order (offset_val i p) (offset_val j p).
Proof.
  intros SH FC Hi Hj Hn.
  assert (Wi: data_at sh (tarray tuchar n) c p * R |-- weak_valid_pointer (offset_val i p)).
  { apply sepcon_weak_valid_pointer1. eapply derives_trans; [apply data_at_memory_block|].
    apply memory_block_weak_valid_pointer; [ | | auto]; rewrite sizeof_tarray_tuchar by lia; lia. }
  assert (Wj: data_at sh (tarray tuchar n) c p * R |-- weak_valid_pointer (offset_val j p)).
  { apply sepcon_weak_valid_pointer1. eapply derives_trans; [apply data_at_memory_block|].
    apply memory_block_weak_valid_pointer; [ | | auto]; rewrite sizeof_tarray_tuchar by lia; lia. }
  destruct FC as [Pp _]. destruct p; try contradiction.
  unfold denote_tc_test_order. simpl offset_val in *. unfold test_order_ptrs.
  simpl sameblock. destruct (peq b b); [|congruence]. simpl. apply andp_right; auto.
Qed.

Lemma cp_repr_eqm (x y: Z) : x mod 2^64 = y mod 2^64 -> Int64.repr x = Int64.repr y.
Proof.
  intros. apply Int64.eqm_samerepr. unfold Int64.eqm. change Int64.modulus with (2^64).
  apply Zbits.eqmod_trans with (x mod 2^64); [apply Zbits.eqmod_mod; lia |].
  rewrite H. apply Zbits.eqmod_sym, Zbits.eqmod_mod; lia.
Qed.

Lemma cp_sub_pp (p: val) (a c: Z) : isptr p ->
  force_val (sem_sub_pp tuchar (offset_val a p) (offset_val c p)) = Vlong (Int64.repr (a - c)).
Proof.
  intros. destruct p; try contradiction. unfold sem_sub_pp. simpl. rewrite if_true by auto. simpl.
  rewrite (Ptrofs.add_commut i (Ptrofs.repr a)), (Ptrofs.add_commut i (Ptrofs.repr c)).
  rewrite Ptrofs.sub_shifted. change (Ptrofs.repr 1) with Ptrofs.one. rewrite Ptrofs.divs_one by reflexivity.
  unfold Vptrofs. simpl. f_equal. unfold Ptrofs.to_int64. apply cp_repr_eqm.
  unfold Ptrofs.sub. rewrite !Ptrofs.unsigned_repr_eq. change Ptrofs.modulus with (2^64).
  rewrite Zmod_mod. rewrite <- Zminus_mod. reflexivity.
Qed.

Lemma cp_sameblock (p: val) (a b: Z) : isptr p -> is_true (sameblock (offset_val a p) (offset_val b p)).
Proof. intros. destruct p; try contradiction. simpl. unfold sameblock. destruct (peq b0 b0); [reflexivity | congruence]. Qed.

(* (ptr_a - ptr_b < k), as the Clight of `(BYTE* )dst - (const BYTE* )src < k` evaluates it *)
Lemma cp_diff_lt (p: val) (a b k: Z) :
  isptr p -> Int64.min_signed <= a - b <= Int64.max_signed -> 0 <= k <= Int.max_signed ->
  force_val (sem_cast tint tbool
    (eval_binop Olt tlong tint
       (eval_binop Osub (tptr tuchar) (tptr tuchar)
          (eval_cast (tptr tvoid) (tptr tuchar) (offset_val a p))
          (eval_cast (tptr tvoid) (tptr tuchar) (offset_val b p))) (Vint (Int.repr k)))) =
  Vint (if zlt (a - b) k then Int.one else Int.zero).
Proof.
  intros Hp Hab Hk. destruct p; try contradiction.
  unfold eval_binop. simpl eval_cast.
  replace (force_val2 (sem_binary_operation' Osub (tptr tuchar) (tptr tuchar))
             (Vptr b0 (Ptrofs.add i (Ptrofs.repr a))) (Vptr b0 (Ptrofs.add i (Ptrofs.repr b))))
    with (Vlong (Int64.repr (a - b))) by (rewrite <- (cp_sub_pp (Vptr b0 i) a b I); reflexivity).
  simpl. unfold Int64.lt. rewrite Int64.signed_repr by lia.
  rewrite ?Int.signed_repr by rep_lia. rewrite ?Int64.signed_repr by rep_lia.
  destruct (zlt (a - b) k); reflexivity.
Qed.


(* ---------- the disjoint wild copy: destination after k bytes ---------- *)
Definition dj (cs cd: list val) (k: Z) : list val := sublist 0 k cs ++ sublist k (Zlength cd) cd.

Lemma Zlength_dj (cs cd: list val) (k: Z) :
  0 <= k <= Zlength cs -> k <= Zlength cd -> Zlength (dj cs cd k) = Zlength cd.
Proof. intros. unfold dj. list_solve. Qed.

Lemma dj_0 (cs cd: list val) : dj cs cd 0 = cd.
Proof. unfold dj. list_solve. Qed.

Lemma dj_step (cs cd: list val) (k m: Z) :
  0 <= k -> 0 <= m -> k + m <= Zlength cs -> k + m <= Zlength cd ->
  copied cs (dj cs cd k) k k m = dj cs cd (k + m).
Proof. intros. unfold copied, dj. list_solve. Qed.

Lemma tuchar_retype (sh: share) (N: Z) (l: list val) (p: val) :
  Zlength l = N -> data_at sh (tarray tuchar N) l p |-- data_at sh (tarray tuchar (Zlength l)) l p.
Proof. intros <-. apply derives_refl. Qed.

Lemma dj_post (cs cd: list val) (n E: Z) :
  0 <= n <= E -> E <= n + 32 -> n + 32 <= Zlength cs -> n + 32 <= Zlength cd ->
  sublist 0 n cs ++ sublist n (n + 32) (dj cs cd E) ++ sublist (n + 32) (Zlength cd) cd = dj cs cd E.
Proof. intros. unfold dj. list_solve. Qed.


(* ---------- the forward overlap copy as a periodic extension (for ZSTD_overlapCopy8) ---------- *)
Lemma listcopy_period (c: list val) (si di n j: Z) :
  0 <= si < di -> 0 <= n -> di + n <= Zlength c -> 0 <= j < n ->
  Znth (di + j) (listcopy c si di (Z.to_nat n)) = Znth (si + j mod (di - si)) c.
Proof.
  intros Hs Hn HN Hj. rewrite <- (Z2Nat.id n) in HN, Hj by lia.
  set (k := Z.to_nat n) in *. clearbody k. clear Hn. revert j Hj.
  induction k as [|k IH]; intros j Hj; [simpl in Hj; lia |].
  rewrite Nat2Z.inj_succ in *.
  assert (HL: Zlength (listcopy c si di k) = Zlength c) by (apply listcopy_Zlength; lia).
  rewrite listcopy_snoc.
  destruct (Z.eq_dec j (Z.of_nat k)) as [-> | Hne].
  - rewrite upd_Znth_same by lia.
    destruct (Z_lt_le_dec (si + Z.of_nat k) di) as [L | L].
    + rewrite listcopy_outside by lia. rewrite Z.mod_small by lia. reflexivity.
    + replace (si + Z.of_nat k) with (di + (Z.of_nat k - (di - si))) by lia.
      rewrite IH by lia. f_equal. f_equal.
      replace (Z.of_nat k) with ((Z.of_nat k - (di - si)) + 1 * (di - si)) at 2 by lia.
      rewrite Z_mod_plus_full. reflexivity.
  - rewrite upd_Znth_diff by lia. apply IH; lia.
Qed.

Lemma listcopy_bytes (c: list val) (si di n x: Z) :
  0 <= si < di -> 0 <= n -> di + n <= Zlength c -> Forall is_byte_val (sublist si di c) ->
  si <= x < di + n -> is_byte_val (Znth x (listcopy c si di (Z.to_nat n))).
Proof.
  intros Hs Hn HN HB Hx.
  assert (Hd: forall y, si <= y < di -> is_byte_val (Znth y c)).
  { intros y Hy. rewrite Forall_forall in HB. apply HB.
    replace (Znth y c) with (Znth (y - si) (sublist si di c)) by (rewrite Znth_sublist by lia; f_equal; lia).
    apply Znth_In. rewrite Zlength_sublist by lia. lia. }
  destruct (Z_lt_le_dec x di) as [L | L].
  - rewrite listcopy_outside by (rewrite ?Z2Nat.id; lia). apply Hd. lia.
  - replace x with (di + (x - di)) by lia. rewrite listcopy_period by lia.
    apply Hd. pose proof (Z.mod_pos_bound (x - di) (di - si)). lia.
Qed.

(* ---------- the bytes a copy reads are defined ----------
   memcpy and memmove are libc.c's byte loops (QuickProof v0.1.0-beta.1), and ZSTD_copy4/8/16 are memcpy: each
   copy needs the cells it reads to be defined bytes (Spec_util.copy_pre, LibcSpec.mm_ok).  These lemmas carry
   that fact through a forward copy. *)
Lemma Forall_sublist_pt (P: val -> Prop) (l: list val) (a b: Z) :
  0 <= a <= b -> b <= Zlength l -> (forall x, a <= x < b -> P (Znth x l)) -> Forall P (sublist a b l).
Proof.
  intros Hab Hb H. apply Forall_forall. intros v Hv.
  apply In_Znth in Hv. destruct Hv as [i [Hi Ev]]. rewrite Zlength_sublist in Hi by lia.
  subst v. rewrite Znth_sublist by lia. apply H. lia.
Qed.

Lemma Forall_sub_range (P: val -> Prop) (l: list val) (a b a' b': Z) :
  0 <= a <= a' -> a' <= b' <= b -> b <= Zlength l -> Forall P (sublist a b l) -> Forall P (sublist a' b' l).
Proof.
  intros Ha Hb HN HF. apply Forall_sublist_pt; try lia. intros x Hx.
  rewrite Forall_forall in HF. apply HF.
  replace (Znth x l) with (Znth (x - a) (sublist a b l)) by (rewrite Znth_sublist by lia; f_equal; lia).
  apply Znth_In. rewrite Zlength_sublist by lia. lia.
Qed.

Lemma Forall_sublist_pt_inv (l: list val) (a b x: Z) :
  0 <= a -> b <= Zlength l -> Forall is_byte_val (sublist a b l) -> a <= x < b -> is_byte_val (Znth x l).
Proof.
  intros Ha Hb HF Hx. rewrite Forall_forall in HF. apply HF.
  replace (Znth x l) with (Znth (x - a) (sublist a b l)) by (rewrite Znth_sublist by lia; f_equal; lia).
  apply Znth_In. rewrite Zlength_sublist by lia. lia.
Qed.

(* DecIface.is_byte_val and LibcSpec.byte_val are the same predicate *)
Lemma fa_bv (l: list val) : Forall is_byte_val l -> Forall byte_val l.
Proof. exact (fun H => H). Qed.

(* A forward copy from si < di whose source cells [si, b) (b <= di) are defined bytes: after k bytes, the cell x
   is defined when it is an original cell below b, or a copy (x >= di) of one; the copy at x is the cell
   si + (x - di) mod (di - si), which is below b when b = di or x - di < b - si. *)
Lemma lc_read_gap (c: list val) (si di k b x: Z) :
  0 <= si < di -> 0 <= k -> di + k <= Zlength c -> si <= b <= di -> Forall is_byte_val (sublist si b c) ->
  si <= x < di + k -> (x < b \/ (di <= x /\ (b = di \/ x - di < b - si))) ->
  is_byte_val (Znth x (listcopy c si di (Z.to_nat k))).
Proof.
  intros Hs Hk HN Hb HB Hx Hr.
  destruct (Z_lt_le_dec x di) as [L | L].
  - rewrite listcopy_outside by (rewrite ?Z2Nat.id; lia).
    apply (Forall_sublist_pt_inv c si b); auto; lia.
  - replace x with (di + (x - di)) by lia. rewrite listcopy_period by lia.
    pose proof (Z.mod_pos_bound (x - di) (di - si) ltac:(lia)).
    pose proof (Z.mod_le (x - di) (di - si) ltac:(lia) ltac:(lia)).
    apply (Forall_sublist_pt_inv c si b); auto; lia.
Qed.

(* the source of a ZSTD_copyN inside one array, held as the prefix [0, d) or as the suffix from a *)
Lemma fa_sub_prefix (L: list val) (a b d: Z) :
  0 <= a <= b -> b <= d -> d <= Zlength L -> Forall is_byte_val (sublist a b L) ->
  Forall byte_val (sublist a b (sublist 0 d L)).
Proof.
  intros. replace (sublist a b (sublist 0 d L)) with (sublist a b L) by list_solve. apply fa_bv; assumption.
Qed.

Lemma fa_sub_suffix (L: list val) (a m e: Z) :
  0 <= a -> 0 <= m -> a + m <= e -> e <= Zlength L -> Forall is_byte_val (sublist a (a + m) L) ->
  Forall byte_val (sublist 0 m (sublist a e L)).
Proof.
  intros. replace (sublist 0 m (sublist a e L)) with (sublist a (a + m) L) by list_solve. apply fa_bv; assumption.
Qed.

(* a range of defined bytes from a larger one in the context *)
Ltac fa_range :=
  match goal with
  | Hb: Forall is_byte_val (sublist ?a ?b ?l) |- Forall is_byte_val (sublist _ _ ?l) =>
      apply (Forall_sub_range _ l a b); [lia | lia | lia | exact Hb]
  end.

(* the second half of ZSTD_overlapCopy8 (offset < 8): ZSTD_copy4 from si + d, with d = dec32[offset] *)
Lemma oc8_listcopy (c: list val) (si di d: Z) :
  0 <= si < di -> di - si < 8 -> 0 <= d <= di - si -> (d - 4) mod (di - si) = 0 -> di + 8 <= Zlength c ->
  listcopy (listcopy c si di (Z.to_nat 4)) (si + d) (di + 4) (Z.to_nat 4) = listcopy c si di (Z.to_nat 8).
Proof.
  intros Hs Ho Hd Hm HN.
  set (o := di - si) in *.
  assert (HL4: Zlength (listcopy c si di (Z.to_nat 4)) = Zlength c) by (apply Zlength_listcopy; lia).
  rewrite listcopy_disj by lia. rewrite HL4.
  apply Znth_eq_ext.
  { rewrite Zlength_listcopy by lia. list_solve. }
  intros i Hi. rewrite !Zlength_app, !Zlength_sublist in Hi by lia.
  destruct (Z_lt_le_dec i (di + 4)) as [L1 | L1].
  - rewrite Znth_app1 by (rewrite Zlength_sublist by lia; lia).
    rewrite Znth_sublist by lia. rewrite Z.add_0_r.
    destruct (Z_lt_le_dec i di) as [L2 | L2].
    + rewrite !listcopy_outside by (rewrite ?Z2Nat.id; lia). reflexivity.
    + replace i with (di + (i - di)) by lia. rewrite !listcopy_period by lia. reflexivity.
  - rewrite Znth_app2 by (rewrite Zlength_sublist by lia; lia). rewrite Zlength_sublist by lia.
    destruct (Z_lt_le_dec i (di + 8)) as [L2 | L2].
    + rewrite Znth_app1 by (rewrite Zlength_sublist by lia; lia).
      rewrite Znth_sublist by lia.
      assert (E8: Znth i (listcopy c si di (Z.to_nat 8)) = Znth (si + (i - di) mod o) c)
        by (replace i with (di + (i - di)) at 1 by lia; apply listcopy_period; lia).
      rewrite E8. clear E8.
      set (j := i - (di + 4)).
      match goal with |- Znth ?x _ = _ => replace x with (si + d + j) by (subst j; lia) end.
      replace (i - di) with (4 + j) by (subst j; lia).
      assert (Hjm: (d + j) mod o = (4 + j) mod o).
      { replace (d + j) with ((4 + j) + (d - 4)) by lia.
        rewrite Zplus_mod, Hm, Z.add_0_r, Zmod_mod. reflexivity. }
      destruct (Z_lt_le_dec (si + d + j) di) as [L3 | L3].
      * rewrite listcopy_outside by (rewrite ?Z2Nat.id; lia).
        rewrite <- Hjm. rewrite Z.mod_small by lia. f_equal. lia.
      * replace (si + d + j) with (di + (d + j - o)) by (subst o; lia).
        rewrite listcopy_period by lia. f_equal. f_equal.
        rewrite <- Hjm. fold o.
        replace (d + j) with ((d + j - o) + 1 * o) at 2 by lia. rewrite Z_mod_plus_full. reflexivity.
    + rewrite Znth_app2 by (rewrite Zlength_sublist by lia; lia). rewrite Zlength_sublist by lia.
      rewrite Znth_sublist by lia.
      rewrite listcopy_outside by (rewrite ?Z2Nat.id; lia).
      rewrite listcopy_outside by (rewrite ?Z2Nat.id; lia). f_equal. lia.
Qed.



(* ---------- helpers for the byte loops of ZSTD_safecopy / ZSTD_safecopyDstBeforeSrc ---------- *)

(* dst before src: a forward copy reads only original bytes *)
Lemma listcopy_dbs (c: list val) (si di n j: Z) :
  0 <= di <= si -> 0 <= n -> si + n <= Zlength c -> 0 <= j < n ->
  Znth (di + j) (listcopy c si di (Z.to_nat n)) = Znth (si + j) c.
Proof.
  intros Hd Hn HN Hj. rewrite <- (Z2Nat.id n) in HN, Hj by lia.
  set (q := Z.to_nat n) in *. clearbody q. clear Hn. revert j Hj.
  induction q as [|q IH]; intros j Hj; [simpl in Hj; lia |].
  rewrite Nat2Z.inj_succ in *. rewrite listcopy_snoc.
  assert (HL: Zlength (listcopy c si di q) = Zlength c) by (apply listcopy_Zlength; lia).
  destruct (Z.eq_dec j (Z.of_nat q)) as [-> | Hne].
  - rewrite upd_Znth_same by lia. apply listcopy_outside; lia.
  - rewrite upd_Znth_diff by lia. apply IH; lia.
Qed.

(* the forward copy with src before dst, position by position *)
Lemma lc_char (c: list val) (s d n x: Z) :
  0 <= s < d -> 0 <= n -> d + n <= Zlength c -> 0 <= x < Zlength c ->
  Znth x (listcopy c s d (Z.to_nat n)) =
  if andb (d <=? x) (x <? d + n) then Znth (s + (x - s) mod (d - s)) c else Znth x c.
Proof.
  intros Hs Hn HN Hx.
  destruct (andb (d <=? x) (x <? d + n)) eqn:E.
  - apply andb_true_iff in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    replace x with (d + (x - d)) at 1 by lia. rewrite listcopy_period by lia. f_equal. f_equal.
    replace (x - s) with ((x - d) + 1 * (d - s)) by lia. rewrite Z_mod_plus_full. reflexivity.
  - apply andb_false_iff in E. apply listcopy_outside; rewrite ?Z2Nat.id; try lia.
Qed.

Lemma lc_extend_sb (c: list val) (s d E a m: Z) :
  0 <= s < d -> 0 <= a <= E -> 0 <= m -> d + E <= Zlength c -> d + a + m <= Zlength c ->
  listcopy (listcopy c s d (Z.to_nat E)) (s + a) (d + a) (Z.to_nat m) = listcopy c s d (Z.to_nat (Z.max E (a + m))).
Proof.
  intros Hs Ha Hm HE Hm2.
  assert (HL: Zlength (listcopy c s d (Z.to_nat E)) = Zlength c) by (apply Zlength_listcopy; lia).
  apply Znth_eq_ext.
  { rewrite !Zlength_listcopy; try lia; rewrite ?HL; lia. }
  intros x Hx. rewrite Zlength_listcopy in Hx by (rewrite ?HL; lia). rewrite HL in Hx.
  rewrite (lc_char (listcopy c s d (Z.to_nat E)) (s + a) (d + a) m x) by (rewrite ?HL; lia).
  rewrite (lc_char c s d (Z.max E (a + m)) x) by lia.
  replace (d + a - (s + a)) with (d - s) by lia.
  destruct (andb (d + a <=? x) (x <? d + a + m)) eqn:E1.
  - apply andb_true_iff in E1. destruct E1 as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    replace (andb (d <=? x) (x <? d + Z.max E (a + m))) with true
      by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    set (y := s + a + (x - (s + a)) mod (d - s)).
    assert (Hy: s + a <= y < d + a) by (subst y; pose proof (Z.mod_pos_bound (x - (s + a)) (d - s)); lia).
    rewrite (lc_char c s d E y) by lia.
    assert (Hm1: (y - s) mod (d - s) = (x - s) mod (d - s)).
    { subst y. replace (s + a + (x - (s + a)) mod (d - s) - s) with (a + (x - (s + a)) mod (d - s)) by lia.
      rewrite Zplus_mod_idemp_r. f_equal. lia. }
    destruct (andb (d <=? y) (y <? d + E)) eqn:E3.
    + rewrite Hm1. reflexivity.
    + rewrite <- Hm1. rewrite Z.mod_small; [f_equal; lia |].
      apply andb_false_iff in E3. destruct E3 as [E3 | E3]; [apply Z.leb_gt in E3 | apply Z.ltb_ge in E3]; lia.
  - rewrite (lc_char c s d E x) by lia.
    apply andb_false_iff in E1.
    destruct (andb (d <=? x) (x <? d + E)) eqn:E2; destruct (andb (d <=? x) (x <? d + Z.max E (a + m))) eqn:E3;
      try reflexivity;
      apply andb_true_iff in E2 || apply andb_true_iff in E3;
      apply andb_false_iff in E2 || apply andb_false_iff in E3; exfalso;
      repeat match goal with
      | H: _ /\ _ |- _ => destruct H
      | H: _ \/ _ |- _ => destruct H
      | H: (_ <=? _) = true |- _ => apply Z.leb_le in H
      | H: (_ <=? _) = false |- _ => apply Z.leb_gt in H
      | H: (_ <? _) = true |- _ => apply Z.ltb_lt in H
      | H: (_ <? _) = false |- _ => apply Z.ltb_ge in H
      end; lia.
Qed.

Lemma lc_bytes_sb (c: list val) (s d k n x: Z) :
  0 <= s < d -> 0 <= k -> d + k <= Zlength c -> s + n <= Zlength c ->
  Forall is_byte_val (sublist s (s + n) c) -> s <= x < s + n ->
  is_byte_val (Znth x (listcopy c s d (Z.to_nat k))).
Proof.
  intros Hs Hk HN Hn HB Hx.
  assert (Hc: forall y, s <= y < s + n -> is_byte_val (Znth y c)).
  { intros y Hy. rewrite Forall_forall in HB. apply HB.
    replace (Znth y c) with (Znth (y - s) (sublist s (s + n) c)) by (rewrite Znth_sublist by lia; f_equal; lia).
    apply Znth_In. rewrite Zlength_sublist by lia. lia. }
  rewrite lc_char by lia.
  destruct (andb (d <=? x) (x <? d + k)) eqn:E; [| apply Hc; lia].
  apply andb_true_iff in E. destruct E as [E1 _]. apply Z.leb_le in E1.
  apply Hc. pose proof (Z.mod_pos_bound (x - s) (d - s)). lia.
Qed.

(* dst before src at distance >= 32: the leftover byte loop after a wild copy of E bytes *)
Lemma lc_extend_dbs (c: list val) (s d E a m: Z) :
  0 <= d -> d + 32 <= s -> 0 <= a <= E -> E <= a + 31 -> 0 <= m ->
  s + a + m <= Zlength c -> s + E <= Zlength c ->
  let F := listcopy (listcopy c s d (Z.to_nat E)) (s + a) (d + a) (Z.to_nat m) in
  Zlength F = Zlength c /\
  (forall j, 0 <= j < a + m -> Znth (d + j) F = Znth (s + j) c) /\
  (forall x, 0 <= x < Zlength c -> ~ (d <= x < d + Z.max E (a + m)) -> Znth x F = Znth x c).
Proof.
  intros Hd Hds Ha HE Hm Ham HsE F. subst F.
  assert (HL: Zlength (listcopy c s d (Z.to_nat E)) = Zlength c) by (apply Zlength_listcopy; lia).
  split; [rewrite Zlength_listcopy; rewrite ?HL; lia |]. split.
  - intros j Hj. destruct (Z_lt_le_dec j a) as [L | L].
    + rewrite listcopy_outside by (rewrite ?HL, ?Z2Nat.id; lia).
      apply listcopy_dbs; lia.
    + replace (d + j) with (d + a + (j - a)) by lia.
      rewrite listcopy_dbs by (rewrite ?HL; lia).
      rewrite listcopy_outside by (rewrite ?Z2Nat.id; lia). f_equal. lia.
  - intros x Hx Hout.
    rewrite listcopy_outside by (rewrite ?HL, ?Z2Nat.id; lia).
    apply listcopy_outside; rewrite ?Z2Nat.id; lia.
Qed.

(* after ZSTD_overlapCopy8 the copy goes on at distance K (a multiple of the offset): the same forward copy *)
Lemma lc_reoff (c: list val) (si di a K m: Z) :
  0 <= si < di -> 0 <= a -> K mod (di - si) = 0 -> di - si <= K <= a + (di - si) -> 0 <= m ->
  di + a + m <= Zlength c ->
  listcopy (listcopy c si di (Z.to_nat a)) (di + a - K) (di + a) (Z.to_nat m) = listcopy c si di (Z.to_nat (a + m)).
Proof.
  intros Hs Ha HK HK2 Hm HN.
  set (D := di - si) in *.
  assert (HL: Zlength (listcopy c si di (Z.to_nat a)) = Zlength c) by (apply Zlength_listcopy; lia).
  assert (Hq: (K = (K / D) * D)%Z) by (rewrite (Z.div_mod K D) at 1 by lia; rewrite HK; lia).
  assert (HqP: 0 < K / D) by (apply Z.div_str_pos; lia).
  apply Znth_eq_ext.
  { rewrite !Zlength_listcopy; try lia; rewrite ?HL; lia. }
  intros x Hx. rewrite Zlength_listcopy in Hx by (rewrite ?HL; lia). rewrite HL in Hx.
  rewrite (lc_char (listcopy c si di (Z.to_nat a)) (di + a - K) (di + a) m x) by (rewrite ?HL; lia).
  rewrite (lc_char c si di (a + m) x) by lia.
  replace (di + a - (di + a - K)) with K by lia.
  destruct (andb (di + a <=? x) (x <? di + a + m)) eqn:E1.
  - apply andb_true_iff in E1. destruct E1 as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    replace (andb (di <=? x) (x <? di + (a + m))) with true
      by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    set (u := x - (di + a - K)).
    set (y := di + a - K + u mod K).
    assert (Hy: di + a - K <= y < di + a) by (subst y; pose proof (Z.mod_pos_bound u K); lia).
    rewrite (lc_char c si di a y) by lia.
    assert (Hm1: (y - si) mod D = (x - si) mod D).
    { subst y. replace (di + a - K + u mod K - si) with ((di + a - K - si) + u mod K) by lia.
      assert (Hmm: (u mod K) mod D = u mod D)
        by (clearbody u; rewrite Hq; apply Zaux.Zmod_mod_mult; lia).
      rewrite <- Zplus_mod_idemp_r. rewrite Hmm.
      rewrite Zplus_mod_idemp_r. f_equal. subst u. lia. }
    destruct (andb (di <=? y) (y <? di + a)) eqn:E3.
    + fold D. rewrite Hm1. reflexivity.
    + fold D. rewrite <- Hm1. rewrite Z.mod_small; [f_equal; lia |].
      apply andb_false_iff in E3. destruct E3 as [E3 | E3]; [apply Z.leb_gt in E3 | apply Z.ltb_ge in E3]; lia.
  - rewrite (lc_char c si di a x) by lia.
    apply andb_false_iff in E1.
    destruct (andb (di <=? x) (x <? di + a)) eqn:E2; destruct (andb (di <=? x) (x <? di + (a + m))) eqn:E3;
      try reflexivity;
      apply andb_true_iff in E2 || apply andb_true_iff in E3;
      apply andb_false_iff in E2 || apply andb_false_iff in E3; exfalso;
      repeat match goal with
      | H: _ /\ _ |- _ => destruct H
      | H: _ \/ _ |- _ => destruct H
      | H: (_ <=? _) = true |- _ => apply Z.leb_le in H
      | H: (_ <=? _) = false |- _ => apply Z.leb_gt in H
      | H: (_ <? _) = true |- _ => apply Z.ltb_lt in H
      | H: (_ <? _) = false |- _ => apply Z.ltb_ge in H
      end; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* seq_t = {litLength; matchLength; offset} as a reptype of ___gp_seq_t. *)
Definition t_seq : type := Tstruct ___gp_seq_t noattr.
Definition seqrep (ll ml off: Z) : reptype t_seq :=
  (Vlong (Int64.repr ll), (Vlong (Int64.repr ml), Vlong (Int64.repr off))).

(* ZSTD_seqCopy(dst, src): copy the three fields. *)
Definition ZSTD_seqCopy_spec : ident * funspec :=
  DECLARE _ZSTD_seqCopy
  WITH shs: share, ps: val, ll: Z, ml: Z, off: Z, shd: share, pd: val
  PRE [ tptr t_seq, tptr t_seq ]
    PROP (readable_share shs; writable_share shd;
          0 <= ll <= Int64.max_unsigned; 0 <= ml <= Int64.max_unsigned; 0 <= off <= Int64.max_unsigned)
    PARAMS (pd; ps) SEP (data_at shs t_seq (seqrep ll ml off) ps; data_at_ shd t_seq pd)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at shs t_seq (seqrep ll ml off) ps; data_at shd t_seq (seqrep ll ml off) pd).

(* ------------------------------------------------------------------ *)
(* ZSTD_wildcopy / ZSTD_safecopy argument shapes.  Both calls occur in two situations:
   - within: source and destination are two ranges [si,si+n) and [di,di+n) of ONE byte array (the output
     array for a match, or the output array for literals that live in it); the overlap tag applies.
   - disjoint: source and destination are two SEPARATE arrays (literals in the input window or
     litExtraBuffer, copied to the output); ovtype = ZSTD_no_overlap.
   In both cases the function may over-READ up to WILDCOPY_OVERLENGTH past the source and over-WRITE up to
   WILDCOPY_OVERLENGTH past dst+n (the caller owns that slack); the written bytes [di,di+n) are listcopy
   (within) / the source bytes (disjoint); the slack [.,.+32) becomes unspecified. *)

(* the post array of a within copy: [0,di+n) from listcopy, [di+n,di+n+32) unspecified, the rest original *)
Definition wc_within_post (c: list val) (si di n: Z) (g: list val) : list val :=
  sublist 0 (di + n) (listcopy c si di (Z.to_nat n)) ++ g ++ sublist (di + n + WILDCOPY_OVERLENGTH) (Zlength c) c.

(* The number of bytes the C actually writes (and reads): the 8-byte loop (overlap tag with dst-src < 16)
   writes max(1, ceil(n/8)) chunks of 8; the 16-byte path writes 16, then pairs of 16 until >= n.  The
   result is exactly the forward copy of that many bytes (chunks never overlap their own source). *)
Definition wc_ext (short: bool) (n: Z) : Z :=
  if short then 8 * Z.max 1 ((n + 7) / 8)
  else if n <=? WILDCOPY_VECLEN then WILDCOPY_VECLEN
  else WILDCOPY_VECLEN + 32 * ((n - WILDCOPY_VECLEN + 31) / 32).

(* The cells a forward copy of n bytes from si to di inside one array reads before it has written them, with the
   over-read of the wild copies (up to 31 bytes past n): they must be defined bytes, since memcpy and memmove are
   libc.c's byte loops (QuickProof v0.1.0-beta.1; LibcSpec.memcpy_bytes_spec, memmove_spec).  When the source is
   before the destination, the cells from di on are written before they are read. *)
Definition copy_src_def (c: list val) (si di n: Z) : Prop :=
  Forall is_byte_val
    (sublist si (if si <? di then Z.min di (si + n + WILDCOPY_OVERLENGTH) else si + n + WILDCOPY_OVERLENGTH) c).

Definition ZSTD_wildcopy_spec : ident * funspec :=
  DECLARE _ZSTD_wildcopy
  WITH gv: globals, within: bool,
       sh: share, p: val, c: list val, si: Z, di: Z,
       shs: share, ps: val, cs: list val, shd: share, pd: val, cd: list val,
       n: Z, ov: Z
  PRE [ tptr tvoid, tptr tvoid, tulong, tint ]
    PROP (0 <= n; ov = OV_NO_OVERLAP \/ ov = OV_SRC_BEFORE_DST;
          (* within: one array c, [si,si+n) -> [di,di+n); overlap needs si + VECLEN <= di (dst-src >= 16)
             for the 16-byte path, or dst-src >= 8 handled by the 8-byte path; a match has si < di. *)
          within = true ->
            writable_share sh /\ 0 <= si /\ 0 <= di /\ Zlength c <= Ptrofs.max_signed /\
            di + n + WILDCOPY_OVERLENGTH <= Zlength c /\ si + n + WILDCOPY_OVERLENGTH <= Zlength c /\
            (ov = OV_SRC_BEFORE_DST -> si + 8 <= di) /\
            (ov = OV_NO_OVERLAP -> si + WILDCOPY_VECLEN <= di \/ di + WILDCOPY_VECLEN <= si);
          (* disjoint: two arrays; ovtype = no_overlap. *)
          within = false ->
            readable_share shs /\ writable_share shd /\ ov = OV_NO_OVERLAP /\
            n + WILDCOPY_OVERLENGTH <= Zlength cs /\ n + WILDCOPY_OVERLENGTH <= Zlength cd;
          (* the bytes read are defined (copy_src_def) *)
          within = true -> copy_src_def c si di n;
          within = false -> Forall is_byte_val (sublist 0 (n + WILDCOPY_OVERLENGTH) cs))
    PARAMS ((if within then field_address (tarray tuchar (Zlength c)) (SUB di) p else pd);
            (if within then field_address (tarray tuchar (Zlength c)) (SUB si) p else ps);
            Vlong (Int64.repr n); Vint (Int.repr ov))
    GLOBALS (gv)
    SEP (zstd_globals gv;
         if within then data_at sh (tarray tuchar (Zlength c)) c p
         else data_at shs (tarray tuchar (Zlength cs)) cs ps * data_at shd (tarray tuchar (Zlength cd)) cd pd)
  POST [ tvoid ]
    EX g: list val,
    PROP (Zlength g = WILDCOPY_OVERLENGTH;
          (* the slack holds what the C really wrote there *)
          if within then
            g = sublist (di + n) (di + n + WILDCOPY_OVERLENGTH)
                  (listcopy c si di (Z.to_nat (wc_ext (andb (ov =? OV_SRC_BEFORE_DST) (di - si <? WILDCOPY_VECLEN)) n)))
          else
            g = sublist n (n + WILDCOPY_OVERLENGTH)
                  (sublist 0 (wc_ext false n) cs ++ sublist (wc_ext false n) (Zlength cd) cd);
          (* exactly ZSTD_wildcopy's stores (BlkSeqXMem.lwild, the model's xm_wild) *)
          if within then wc_within_post c si di n g = lwild c di LW si n (ov =? OV_SRC_BEFORE_DST)
          else sublist 0 n cs ++ g ++ sublist (n + WILDCOPY_OVERLENGTH) (Zlength cd) cd = lwild cd 0 (LS cs) 0 n false)
    RETURN ()
    SEP (zstd_globals gv;
         if within then data_at sh (tarray tuchar (Zlength c)) (wc_within_post c si di n g) p
         else data_at shs (tarray tuchar (Zlength cs)) cs ps *
              data_at shd (tarray tuchar (Zlength cd))
                (sublist 0 n cs ++ g ++ sublist (n + WILDCOPY_OVERLENGTH) (Zlength cd) cd) pd).

(* ZSTD_overlapCopy8(&op, &ip, offset): copies 8 bytes from *ip to *op where *ip <= *op (one array),
   spreading a short offset to >= 8, then advances *op by 8 and *ip by 8 - (dec64[offset]-8 ...).  The
   dec32/dec64 tables are in zstd_globals.  The 8 written bytes are the forward overlap copy; the pointer
   update is the C's (op advances 8; ip advances to op's new position minus 8).  Stated on one array c
   with the source at si = di - offset (a match), 1 <= offset. *)
(* the distance op - ip after ZSTD_overlapCopy8: offset + dec64[offset] - dec32[offset] for offset < 8
   (a multiple of offset, >= 8), else offset *)
Definition oc8_off (offset: Z) : Z :=
  match offset with 1 => 8 | 2 => 8 | 3 => 9 | 4 => 8 | 5 => 10 | 6 => 12 | 7 => 14 | _ => offset end.

Definition ZSTD_overlapCopy8_spec : ident * funspec :=
  DECLARE _ZSTD_overlapCopy8
  WITH gv: globals, sh: share, p: val, c: list val, pop: val, pip: val, di: Z, offset: Z
  PRE [ tptr (tptr tuchar), tptr (tptr tuchar), tulong ]
    PROP (writable_share sh; 1 <= offset; 0 <= di - offset; di + 8 <= Zlength c;
          (* the bytes read before they are written: defined (offset < 8: the offset cells it spreads; else the
             8 bytes ZSTD_copy8 reads) *)
          Forall is_byte_val (sublist (di - offset) (di - offset + Z.min offset 8) c))
    PARAMS (pop; pip; Vlong (Int64.repr offset)) GLOBALS (gv)
    SEP (zstd_globals gv;
         data_at Tsh (tptr tuchar) (field_address (tarray tuchar (Zlength c)) (SUB di) p) pop;
         data_at Tsh (tptr tuchar) (field_address (tarray tuchar (Zlength c)) (SUB (di - offset)) p) pip;
         data_at sh (tarray tuchar (Zlength c)) c p)
  POST [ tvoid ]
    PROP ((* exactly ZSTD_overlapCopy8's stores and pointers (BlkSeqXMem.lov8, the model's xm_ov8) *)
          lov8 c di (di - offset) offset =
            pair (pair (listcopy c (di - offset) di 8) (di + 8)%Z) (di + 8 - oc8_off offset)%Z)
    RETURN ()
    SEP (zstd_globals gv;
         data_at Tsh (tptr tuchar) (field_address0 (tarray tuchar (Zlength c)) (SUB (di + 8)) p) pop;
         data_at Tsh (tptr tuchar) (field_address0 (tarray tuchar (Zlength c)) (SUB (di + 8 - oc8_off offset)) p) pip;
         data_at sh (tarray tuchar (Zlength c)) (listcopy c (di - offset) di 8) p).

(* ZSTD_safecopy(op, oend_w, ip, length, ovtype): like wildcopy, but the wild part stops at oend_w
   (oend_w = oend - 32 may lie before the array; op may pass it; the leftovers are copied byte by byte, by
   one-byte ZSTD_memmove in the patched code).
   The destination op = p + di is in the output array c (oend_w = p + dw); the source is
   - within (within = true): ip = p + si in the same array: a match (ov = overlap, si < di; it reads only
     below the write bound) or literals that live in the output array after oend (ov = no_overlap, entirely
     after everything the call writes);
   - disjoint (within = false): ip = ps, the start of a separate array cs (literals in the input window or in
     litExtraBuffer; ov = no_overlap), read up to 32 bytes past n.
   Writes [di, di+n) = the forward copy (within) / the n source bytes (disjoint); nothing outside
   [di, min(di+n+32, max(di+n, dw+32))); if every readable cell is a byte (DecRep.byte_cells), so is every
   cell after the call (bytes in, bytes out). *)
Definition ZSTD_safecopy_spec : ident * funspec :=
  DECLARE _ZSTD_safecopy
  WITH gv: globals, within: bool, sh: share, p: val, c: list val, dw: Z, si: Z, di: Z,
       shs: share, ps: val, cs: list val, n: Z, ov: Z
  PRE [ tptr tuchar, tptr tuchar, tptr tuchar, tulong, tint ]
    PROP (writable_share sh; 0 <= n; ov = OV_NO_OVERLAP \/ ov = OV_SRC_BEFORE_DST;
          0 <= di; di < Zlength c; di + n <= Zlength c;
          (* the array's offsets are ptrdiff_t values, and oend_w - oend (a ptrdiff_t the C compares with 0)
             does not wrap below -2^63; dw - op then does not wrap either *)
          Zlength c <= Ptrofs.max_signed /\ di + n - dw <= 2 ^ 63;
          (* oend_w = oend - 32 may lie before the array (output buffer < 32 bytes) *)
          - WILDCOPY_OVERLENGTH <= dw;
          (* the wild part writes up to 31 bytes past its end, so up to oend_w + 32 *)
          Z.max (di + n) (dw + WILDCOPY_OVERLENGTH) <= Zlength c;
          within = true ->
            0 <= si /\
            (ov = OV_SRC_BEFORE_DST -> si < di) /\
            (ov = OV_NO_OVERLAP ->
               si + n + WILDCOPY_OVERLENGTH <= Zlength c /\
               (si + WILDCOPY_VECLEN <= di \/ Z.max (di + n) (dw + WILDCOPY_OVERLENGTH) <= si));
          within = false ->
            readable_share shs /\ ov = OV_NO_OVERLAP /\ n + WILDCOPY_OVERLENGTH <= Zlength cs;
          (* the bytes read are defined (copy_src_def) *)
          within = true -> copy_src_def c si di n;
          within = false -> Forall is_byte_val (sublist 0 (n + WILDCOPY_OVERLENGTH) cs))
    PARAMS (field_address (tarray tuchar (Zlength c)) (SUB di) p;
            offset_val dw p;
            (if within then field_address (tarray tuchar (Zlength c)) (SUB si) p else ps);
            Vlong (Int64.repr n); Vint (Int.repr ov))
    GLOBALS (gv)
    SEP (zstd_globals gv; data_at sh (tarray tuchar (Zlength c)) c p;
         if within then emp else data_at shs (tarray tuchar (Zlength cs)) cs ps)
  POST [ tvoid ]
    EX cd': list val,
    PROP (Zlength cd' = Zlength c;
          sublist di (di + n) cd' =
            (if within then sublist di (di + n) (listcopy c si di (Z.to_nat n)) else sublist 0 n cs);
          forall k, 0 <= k < Zlength c ->
            ~ (di <= k < Z.min (di + n + WILDCOPY_OVERLENGTH) (Z.max (di + n) (dw + WILDCOPY_OVERLENGTH))) ->
            Znth k cd' = Znth k c;
          (* every cell written, slack included, is a copy of a readable cell: bytes in, bytes out *)
          (if within then byte_cells c else byte_cells c /\ byte_cells cs) -> byte_cells cd';
          (* cell by cell: each cell is unchanged or a defined byte (it copies only defined bytes) *)
          forall q, 0 <= q < Zlength c -> Znth q cd' = Znth q c \/ is_byte_val (Znth q cd');
          (* exactly ZSTD_safecopy's stores, the cells past oend_w included (BlkSeqXMem.lsafecopy, the model's
             xm_safecopy) *)
          cd' = lsafecopy c di dw (if within then LW else LS cs) (if within then si else 0) n
                  (ov =? OV_SRC_BEFORE_DST))
    RETURN ()
    SEP (zstd_globals gv; data_at sh (tarray tuchar (Zlength c)) cd' p;
         if within then emp else data_at shs (tarray tuchar (Zlength cs)) cs ps).

(* ZSTD_safecopyDstBeforeSrc(op, ip, length): one array c, op = p + di, ip = p + si, in any relative position
   (the split-literal loops call it with dst before the literals, or after them).  diff = di - si > -8 or
   n < 8: a forward byte copy (one-byte ZSTD_memmove in the patched code); else, if n >= 32 and
   diff < -16, a wild copy of n - 32 bytes (ending before op + n) then the byte loop.  So it touches only
   [di, di+n) and [si, si+n); the result is the forward copy (listcopy) unless 16 < si - di < 32 and
   n >= 32 (the wild part then over-writes source bytes the byte loop reads later); the written bytes are
   always source bytes, so bytes stay bytes.  The pointers are field_address0 (di = N or si = N allowed when
   n = 0, e.g. an empty literal run at the end of the output) and the array is nonempty (the C compares
   op < oend, which needs weakly valid pointers). *)
Definition ZSTD_safecopyDstBeforeSrc_spec : ident * funspec :=
  DECLARE _ZSTD_safecopyDstBeforeSrc
  WITH gv: globals, sh: share, p: val, c: list val, si: Z, di: Z, n: Z
  PRE [ tptr tuchar, tptr tuchar, tulong ]
    PROP (writable_share sh; 0 <= n; 0 <= si; 0 <= di; 0 < Zlength c; Zlength c <= Ptrofs.max_signed;
          di + n <= Zlength c; si + n <= Zlength c;
          (* the source bytes are defined *)
          Forall is_byte_val (sublist si (si + n) c))
    PARAMS (field_address0 (tarray tuchar (Zlength c)) (SUB di) p;
            field_address0 (tarray tuchar (Zlength c)) (SUB si) p;
            Vlong (Int64.repr n))
    GLOBALS (gv)
    SEP (zstd_globals gv; data_at sh (tarray tuchar (Zlength c)) c p)
  POST [ tvoid ]
    EX cd': list val,
    PROP (Zlength cd' = Zlength c;
          (* exact forward copy unless the wild part clobbers the source *)
          (n < WILDCOPY_OVERLENGTH \/ si - di <= WILDCOPY_VECLEN \/ WILDCOPY_OVERLENGTH <= si - di ->
             sublist di (di + n) cd' = sublist di (di + n) (listcopy c si di (Z.to_nat n)));
          (* the written bytes are source bytes *)
          Forall is_byte_val (sublist si (si + n) c) -> Forall is_byte_val (sublist di (di + n) cd');
          forall k, 0 <= k < Zlength c -> ~ (di <= k < di + n) -> Znth k cd' = Znth k c;
          (* exactly its stores, the case where the wild part overwrites its source included (BlkSeqXMem.lsdbs,
             the model's xm_sdbs) *)
          cd' = lsdbs c di si n)
    RETURN ()
    SEP (zstd_globals gv; data_at sh (tarray tuchar (Zlength c)) cd' p).

(* ---------- helpers about the wild copy's extent ---------- *)
Lemma wc_post_listcopy (c: list val) (si di n E: Z) :
  0 <= di -> 0 <= n <= E -> E <= n + 32 -> di + n + 32 <= Zlength c ->
  wc_within_post c si di n (sublist (di + n) (di + n + 32) (listcopy c si di (Z.to_nat E))) =
  listcopy c si di (Z.to_nat E).
Proof.
  intros Hdi Hn HE Hc. unfold wc_within_post. unfold WILDCOPY_OVERLENGTH.
  assert (HL: Zlength (listcopy c si di (Z.to_nat E)) = Zlength c) by (apply Zlength_listcopy; lia).
  rewrite <- (listcopy_prefix c si di n E) by lia.
  replace (sublist (di + n + 32) (Zlength c) c)
    with (sublist (di + n + 32) (Zlength c) (listcopy c si di (Z.to_nat E))).
  - rewrite <- HL. rewrite !sublist_rejoin by lia. rewrite sublist_same by lia. reflexivity.
  - apply Znth_eq_ext. { list_solve. }
    intros i Hi. rewrite Zlength_sublist in Hi by lia.
    rewrite !Znth_sublist by lia. apply listcopy_suffix; lia.
Qed.

Lemma wc_ext_short_exit (j n: Z) :
  (0 <= j -> 0 <= n -> (j = 0 \/ 8 * j < n) -> n <= 8 * (j + 1) -> wc_ext true n = 8 * (j + 1))%Z.
Proof.
  intros Hj Hn Hlt Hle. unfold wc_ext. f_equal.
  destruct Hlt as [-> | Hlt].
  - assert ((n + 7) / 8 < 2) by (apply Z.div_lt_upper_bound; lia).
    assert (0 <= (n + 7) / 8) by (apply Z.div_pos; lia). lia.
  - assert ((n + 7) / 8 = j + 1) by (symmetry; apply Z.div_unique with (r := n + 7 - 8 * (j + 1)); lia). lia.
Qed.

Lemma wc_ext_long_exit (j n: Z) :
  (0 <= j -> WILDCOPY_VECLEN + 32 * j < n -> n <= WILDCOPY_VECLEN + 32 * (j + 1) ->
  wc_ext false n = WILDCOPY_VECLEN + 32 * (j + 1))%Z.
Proof.
  unfold WILDCOPY_VECLEN. intros Hj Hlt Hle. unfold wc_ext, WILDCOPY_VECLEN.
  destruct (n <=? 16) eqn:E; [lia |].
  assert ((n - 16 + 31) / 32 = j + 1) by (symmetry; apply Z.div_unique with (r := n - 16 + 31 - 32 * (j + 1)); lia). lia.
Qed.

Lemma wc_ext_bounds (b: bool) (n: Z) : 0 <= n -> n <= wc_ext b n <= n + 31.
Proof.
  intros Hn. unfold wc_ext, WILDCOPY_VECLEN. destruct b.
  - assert (0 <= (n + 7) / 8) by (apply Z.div_pos; lia).
    assert (8 * ((n + 7) / 8) <= n + 7) by (apply Z.mul_div_le; lia).
    assert (n + 7 < 8 * ((n + 7) / 8) + 8) by (pose proof (Z.mod_pos_bound (n + 7) 8); rewrite (Z.div_mod (n + 7) 8) at 1 by lia; lia).
    destruct (Z.max_spec 1 ((n + 7) / 8)) as [[? ->] | [? ->]]; lia.
  - destruct (n <=? 16) eqn:E; [lia |].
    assert (32 * ((n - 16 + 31) / 32) <= n - 16 + 31) by (apply Z.mul_div_le; lia).
    assert (n - 16 + 31 < 32 * ((n - 16 + 31) / 32) + 32)
      by (pose proof (Z.mod_pos_bound (n - 16 + 31) 32); rewrite (Z.div_mod (n - 16 + 31) 32) at 1 by lia; lia).
    lia.
Qed.

Lemma wc_ext_le16 (n: Z) : n <= WILDCOPY_VECLEN -> wc_ext false n = WILDCOPY_VECLEN.
Proof. intros. unfold wc_ext. destruct (n <=? WILDCOPY_VECLEN) eqn:E; [reflexivity | lia]. Qed.

(* A cell x that a copy from si to di reads after writing k bytes is defined under copy_src_def: x is a source
   cell (si <= x < si + n + 32); when si < di it lies below di + k (an original cell below di, or a copy of one),
   and when di <= si it lies at or after di + k (not yet overwritten). *)
Lemma csd_read (c: list val) (si di n k x: Z) :
  copy_src_def c si di n -> 0 <= si -> 0 <= di -> 0 <= k -> di + k <= Zlength c ->
  (si < di \/ si + n + 32 <= Zlength c) ->
  si <= x < si + n + 32 -> (si < di -> x < di + k) -> (di <= si -> di + k <= x) ->
  is_byte_val (Znth x (listcopy c si di (Z.to_nat k))).
Proof.
  unfold copy_src_def, WILDCOPY_OVERLENGTH. intros HB Hsi Hdi Hk HN Hl Hx H1 H2.
  destruct (Z_lt_le_dec si di) as [L | L].
  - rewrite (proj2 (Z.ltb_lt si di) L) in HB.
    apply (lc_read_gap c si di k (Z.min di (si + n + 32))); auto; lia.
  - rewrite (proj2 (Z.ltb_ge si di) L) in HB.
    rewrite listcopy_outside by (rewrite ?Z2Nat.id; lia).
    apply (Forall_sublist_pt_inv c si (si + n + 32)); auto; lia.
Qed.

(* a shorter copy reads fewer cells *)
Lemma csd_mono (c: list val) (si di n m: Z) :
  copy_src_def c si di n -> 0 <= si -> 0 <= m <= n ->
  (si < di /\ di <= Zlength c \/ si + n + 32 <= Zlength c) -> copy_src_def c si di m.
Proof.
  unfold copy_src_def, WILDCOPY_OVERLENGTH. intros HB Hsi Hm Hl.
  destruct (Z_lt_le_dec si di) as [L | L].
  - rewrite (proj2 (Z.ltb_lt si di) L) in HB |- *.
    apply (Forall_sub_range _ c si (Z.min di (si + n + 32))); auto; lia.
  - rewrite (proj2 (Z.ltb_ge si di) L) in HB |- *.
    apply (Forall_sub_range _ c si (si + n + 32)); auto; lia.
Qed.

(* ================= sub-group COPY ================= *)
(* ---------- the exact stores (BlkSeqXMem's mirrors) as forward copies ---------- *)
Lemma lfwd_LW (k: nat) (c: list val) (d i: Z) : lfwd k c d LW i = listcopy c i d k.
Proof. revert c d i. induction k as [|k IH]; intros c d i; simpl; [reflexivity | apply IH]. Qed.

Lemma lfwd_LS (k: nat) (c cs: list val) (d i: Z) :
  0 <= d -> d + Z.of_nat k <= Zlength c -> 0 <= i -> i + Z.of_nat k <= Zlength cs ->
  lfwd k c d (LS cs) i = sublist 0 d c ++ sublist i (i + Z.of_nat k) cs ++ sublist (d + Z.of_nat k) (Zlength c) c.
Proof.
  revert c d i. induction k as [|k IH]; intros c d i Hd Hdk Hi Hik; simpl.
  - rewrite !Z.add_0_r. list_solve.
  - rewrite Nat2Z.inj_succ in *. rewrite IH by (rewrite ?Zlength_upd_Znth; lia).
    rewrite Zlength_upd_Znth. list_solve.
Qed.

Lemma lrdn_sub (k: nat) (c L: list val) (s: lsrc) (i: Z) :
  L = match s with LW => c | LS cs => cs end -> 0 <= i -> i + Z.of_nat k <= Zlength L ->
  lrdn k c s i = sublist i (i + Z.of_nat k) L.
Proof.
  intros HL. revert i. induction k as [|k IH]; intros i Hi Hik; simpl.
  - rewrite Z.add_0_r, sublist_nil. reflexivity.
  - rewrite Nat2Z.inj_succ in *. rewrite IH by lia.
    assert (lrd c s i = Znth i L) by (subst L; destruct s; reflexivity).
    rewrite H, Zpos_P_of_succ_nat. list_solve.
Qed.

Lemma lwrn_sub (vs c: list val) (d: Z) :
  0 <= d -> d + Zlength vs <= Zlength c ->
  lwrn vs c d = sublist 0 d c ++ vs ++ sublist (d + Zlength vs) (Zlength c) c.
Proof.
  revert c d. induction vs as [|v vs IH]; intros c d Hd Hdv; simpl.
  - rewrite Z.add_0_r. list_solve.
  - rewrite Zlength_cons in Hdv. rewrite IH by (rewrite ?Zlength_upd_Znth; lia).
    rewrite Zlength_upd_Znth, Zlength_cons. list_solve.
Qed.

(* a move whose source and destination ranges in the output array are disjoint is the forward copy *)
Lemma lmove_LW (m: Z) (c: list val) (d i: Z) :
  0 <= m -> 0 <= i -> i + m <= Zlength c -> 0 <= d -> d + m <= Zlength c -> (i + m <= d \/ d + m <= i) ->
  lmove (Z.to_nat m) c d LW i = listcopy c i d (Z.to_nat m).
Proof.
  intros. unfold lmove. rewrite (lrdn_sub _ c c) by (try rewrite Z2Nat.id; auto; lia).
  rewrite Z2Nat.id by lia. rewrite lwrn_sub by list_solve. rewrite listcopy_disj by lia.
  f_equal. f_equal. f_equal. list_solve.
Qed.

Lemma lchunks16_LW (k: nat) (c: list val) (d i: Z) :
  0 <= i -> i + (16 * Z.of_nat k)%Z <= Zlength c -> 0 <= d -> d + (16 * Z.of_nat k)%Z <= Zlength c ->
  (i + 16 <= d \/ d + 16 <= i) ->
  lchunks16 k c d LW i = listcopy c i d (Z.to_nat ((16 * Z.of_nat k)%Z)).
Proof.
  revert c d i. induction k as [|k IH]; intros c d i Hi Hik Hd Hdk Hdir; simpl lchunks16.
  - reflexivity.
  - rewrite Nat2Z.inj_succ in *. change 16%nat with (Z.to_nat 16).
    rewrite lmove_LW by lia.
    assert (HL: Zlength (listcopy c i d (Z.to_nat 16)) = Zlength c) by (apply Zlength_listcopy; lia).
    rewrite IH by (rewrite ?HL; lia).
    rewrite listcopy_step by lia. f_equal. f_equal. lia.
Qed.

Lemma lchunks16_LS (k: nat) (c cs: list val) (d i: Z) :
  0 <= i -> i + (16 * Z.of_nat k)%Z <= Zlength cs -> 0 <= d -> d + (16 * Z.of_nat k)%Z <= Zlength c ->
  lchunks16 k c d (LS cs) i =
  sublist 0 d c ++ sublist i (i + (16 * Z.of_nat k)%Z) cs ++ sublist (d + (16 * Z.of_nat k)%Z) (Zlength c) c.
Proof.
  revert c d i. induction k as [|k IH]; intros c d i Hi Hik Hd Hdk; simpl lchunks16.
  - rewrite !Z.mul_0_r, !Z.add_0_r. list_solve.
  - rewrite Nat2Z.inj_succ in *. unfold lmove.
    rewrite (lrdn_sub _ c cs) by (auto; simpl; lia).
    change (Z.of_nat 16) with 16. rewrite lwrn_sub by list_solve.
    rewrite IH by list_solve. list_solve.
Qed.

(* the number of 16-byte chunks of the long path, times 16, is wc_ext false *)
Lemma lwild_nch (n: Z) : 0 <= n ->
  (16 * Z.of_nat (Z.to_nat (if n <=? 16 then 1 else 1 + 2 * ((n - 16 + 31) / 32))) = wc_ext false n)%Z.
Proof.
  intros Hn. unfold wc_ext, WILDCOPY_VECLEN. destruct (n <=? 16) eqn:E; [reflexivity |].
  assert (0 <= (n - 16 + 31) / 32) by (apply Z.div_pos; lia).
  rewrite Z2Nat.id by lia. lia.
Qed.

(* ZSTD_wildcopy inside one array: the 8-byte loop (overlap, dst - src < 16) *)
Lemma lwild_8 (c: list val) (si di n: Z) :
  di - si < 16 -> lwild c di LW si n true = listcopy c si di (Z.to_nat (wc_ext true n)).
Proof.
  intros H. unfold lwild. rewrite (proj2 (Z.ltb_lt _ _) H). simpl andb. cbv iota.
  rewrite lfwd_LW. reflexivity.
Qed.

(* ... and the 16-byte path: source and destination at least 16 bytes apart *)
Lemma lwild_16 (c: list val) (si di n: Z) (b: bool) :
  0 <= si -> 0 <= di -> 0 <= n -> di + n + 32 <= Zlength c -> si + n + 32 <= Zlength c ->
  (si + 16 <= di \/ (b = false /\ di + 16 <= si)) ->
  lwild c di LW si n b = listcopy c si di (Z.to_nat (wc_ext false n)).
Proof.
  intros Hs Hd Hn Hdn Hsn Hdir. pose proof (wc_ext_bounds false n Hn) as HE.
  unfold lwild.
  replace (andb b (di - si <? 16)) with false
    by (destruct Hdir as [H | [-> H]]; [rewrite (proj2 (Z.ltb_ge _ _)) by lia; destruct b |]; reflexivity).
  rewrite lchunks16_LW; rewrite ?lwild_nch; auto; try lia.
Qed.

(* the disjoint wild copy: the source's first wc_ext false n bytes spliced in *)
Lemma lwild_LS (c cs: list val) (d i n: Z) :
  0 <= n -> 0 <= i -> i + n + 32 <= Zlength cs -> 0 <= d -> d + n + 32 <= Zlength c ->
  lwild c d (LS cs) i n false =
  sublist 0 d c ++ sublist i (i + wc_ext false n) cs ++ sublist (d + wc_ext false n) (Zlength c) c.
Proof.
  intros. pose proof (wc_ext_bounds false n ltac:(lia)) as HE.
  unfold lwild. simpl andb. cbv iota.
  rewrite lchunks16_LS; rewrite ?lwild_nch; auto; lia.
Qed.

Lemma lwild_LS_shift (c cs: list val) (d n: Z) :
  0 <= n -> n + 32 <= Zlength cs -> 0 <= d -> d + n + 32 <= Zlength c ->
  sublist 0 d c ++ lwild (sublist d (Zlength c) c) 0 (LS cs) 0 n false = lwild c d (LS cs) 0 n false.
Proof.
  intros. pose proof (wc_ext_bounds false n ltac:(lia)) as HE.
  rewrite !lwild_LS by (try rewrite Zlength_sublist; lia). list_solve.
Qed.

(* ---------- ZSTD_safecopy's outcome, case by case, as BlkSeqXMem.lsafecopy ---------- *)
Lemma lsc_w_short (c: list val) (si di dw n: Z) (b: bool) :
  n < 8 -> listcopy c si di (Z.to_nat n) = lsafecopy c di dw LW si n b.
Proof. intros. unfold lsafecopy. rewrite (proj2 (Z.ltb_lt n 8)) by lia. rewrite lfwd_LW. reflexivity. Qed.

(* after the optional ZSTD_overlapCopy8 (c', di', si'), the rest of lsafecopy *)
Lemma lsc_w_rest (c c': list val) (si di dw n ov si' di': Z) :
  8 <= n ->
  (if ov =? OV_SRC_BEFORE_DST then lov8 c di si (di - si) else (c, di, si)) = (c', di', si') ->
  lsafecopy c di dw LW si n (ov =? OV_SRC_BEFORE_DST) =
  if dw - (di + n) >=? 0 then lwild c' di' LW si' (di + n - di') (ov =? OV_SRC_BEFORE_DST)
  else if dw - di' >=? 0 then
    lfwd (Z.to_nat (di + n - dw)) (lwild c' di' LW si' (dw - di') (ov =? OV_SRC_BEFORE_DST)) dw LW (si' + (dw - di'))
  else lfwd (Z.to_nat (di + n - di')) c' di' LW si'.
Proof.
  intros Hn Hx. unfold lsafecopy. rewrite (proj2 (Z.ltb_ge n 8)) by lia.
  destruct (ov =? OV_SRC_BEFORE_DST).
  - assert (Hd: di' = di + 8) by (unfold lov8 in Hx; destruct (_ <? 8); inversion Hx; lia).
    rewrite Hx. cbv beta iota zeta. subst di'.
    destruct (dw - (di + n) >=? 0); [f_equal; lia |].
    destruct (dw - (di + 8) >=? 0); cbv beta iota zeta; [reflexivity | f_equal; f_equal; lia].
  - injection Hx as <- <- <-. cbv beta iota zeta.
    destruct (dw - (di + n) >=? 0); [f_equal; lia |].
    destruct (dw - di >=? 0); cbv beta iota zeta; [reflexivity | f_equal; f_equal; lia].
Qed.

Lemma lsc_w_wild (c c': list val) (si di dw n ov si' di' E: Z) :
  8 <= n -> dw - (di + n) >= 0 ->
  (if ov =? OV_SRC_BEFORE_DST then lov8 c di si (di - si) else (c, di, si)) = (c', di', si') ->
  wc_within_post c' si' di' (di + n - di') (sublist (di + n) (di + n + 32) (listcopy c' si' di' (Z.to_nat E))) =
    lwild c' di' LW si' (di + n - di') (ov =? OV_SRC_BEFORE_DST) ->
  0 <= di' -> di' <= di + n -> di + n - di' <= E -> E <= di + n - di' + 32 -> di + n + 32 <= Zlength c' ->
  listcopy c' si' di' (Z.to_nat E) = lsafecopy c di dw LW si n (ov =? OV_SRC_BEFORE_DST).
Proof.
  intros Hn Hdw Hx Hw **. rewrite (lsc_w_rest c c' si di dw n ov si' di') by auto.
  rewrite (proj2 (Z.geb_le _ _)) by lia. rewrite <- Hw.
  pose proof (wc_post_listcopy c' si' di' (di + n - di') E) as W.
  replace (di' + (di + n - di')) with (di + n) in W by lia. symmetry. apply W; lia.
Qed.

Lemma lsc_w_tail (c c': list val) (si di dw n ov si' di' E0 a: Z) :
  8 <= n -> dw < di + n ->
  (if ov =? OV_SRC_BEFORE_DST then lov8 c di si (di - si) else (c, di, si)) = (c', di', si') ->
  (a, listcopy c' si' di' (Z.to_nat E0)) =
    (if dw - di' >=? 0 then (dw - di', lwild c' di' LW si' (dw - di') (ov =? OV_SRC_BEFORE_DST)) else (0, c')) ->
  listcopy (listcopy c' si' di' (Z.to_nat E0)) (si' + a) (di' + a) (Z.to_nat (di + n - di' - a)) =
  lsafecopy c di dw LW si n (ov =? OV_SRC_BEFORE_DST).
Proof.
  intros Hn Hdw Hx HaE.
  assert (HE: listcopy c' si' di' (Z.to_nat E0) =
    (if dw - di' >=? 0 then lwild c' di' LW si' (dw - di') (ov =? OV_SRC_BEFORE_DST) else c'))
    by (destruct (dw - di' >=? 0); injection HaE; intros; assumption).
  assert (Ha: a = (if dw - di' >=? 0 then dw - di' else 0))
    by (destruct (dw - di' >=? 0); injection HaE; intros; assumption).
  clear HaE. rewrite (lsc_w_rest c c' si di dw n ov si' di') by auto.
  rewrite Z.geb_leb, (proj2 (Z.leb_gt _ _)) by lia. rewrite HE, Ha.
  destruct (dw - di' >=? 0); rewrite lfwd_LW; f_equal; f_equal; lia.
Qed.

Lemma lsc_d_short (c cs: list val) (di dw n: Z) :
  0 <= di -> 0 <= n < 8 -> di + n <= Zlength c -> n <= Zlength cs ->
  sublist 0 di c ++ sublist 0 n cs ++ sublist (di + n) (Zlength c) c = lsafecopy c di dw (LS cs) 0 n false.
Proof.
  intros. unfold lsafecopy. rewrite (proj2 (Z.ltb_lt n 8)) by lia.
  rewrite lfwd_LS by (rewrite ?Z2Nat.id; lia). rewrite !Z2Nat.id by lia. reflexivity.
Qed.

Lemma lsc_d_wild (c cs g: list val) (di dw n: Z) :
  0 <= di -> 8 <= n -> dw - (di + n) >= 0 -> n + 32 <= Zlength cs -> di + n + 32 <= Zlength c ->
  sublist 0 n cs ++ g ++ sublist (n + 32) (Zlength (sublist di (Zlength c) c)) (sublist di (Zlength c) c) =
    lwild (sublist di (Zlength c) c) 0 (LS cs) 0 n false ->
  sublist 0 di c ++ (sublist 0 n cs ++ g ++ sublist (n + 32) (Zlength (sublist di (Zlength c) c)) (sublist di (Zlength c) c)) =
  lsafecopy c di dw (LS cs) 0 n false.
Proof.
  intros Hd Hn Hdw Hcs Hc Hw. rewrite Hw, lwild_LS_shift by lia.
  unfold lsafecopy. rewrite (proj2 (Z.ltb_ge n 8)) by lia. cbv beta iota zeta.
  rewrite (proj2 (Z.geb_le _ _)) by lia. reflexivity.
Qed.

Lemma lsc_d_tail (c cs c1: list val) (di dw n a: Z) :
  0 <= di -> 8 <= n -> dw < di + n -> -32 <= dw -> n + 32 <= Zlength cs -> di + n <= Zlength c ->
  dw + 32 <= Zlength c ->
  (a, c1) = (if dw - di >=? 0 then (dw - di, lwild c di (LS cs) 0 (dw - di) false) else (0, c)) ->
  sublist 0 (di + a) c1 ++ sublist a (a + (n - a)) cs ++ sublist (di + a + (n - a)) (Zlength c1) c1 =
  lsafecopy c di dw (LS cs) 0 n false.
Proof.
  intros Hd Hn Hdw Hdw' Hcs Hc Hc' HaE.
  assert (Hc1: c1 = (if dw - di >=? 0 then lwild c di (LS cs) 0 (dw - di) false else c))
    by (destruct (dw - di >=? 0); injection HaE; intros; assumption).
  assert (Ha: a = (if dw - di >=? 0 then dw - di else 0))
    by (destruct (dw - di >=? 0); injection HaE; intros; assumption).
  clear HaE.
  assert (HL: Zlength c1 = Zlength c).
  { rewrite Hc1. destruct (dw - di >=? 0) eqn:E; [| reflexivity]. apply Z.geb_le in E.
    pose proof (wc_ext_bounds false (dw - di) ltac:(lia)).
    rewrite lwild_LS by lia. list_solve. }
  unfold lsafecopy. rewrite (proj2 (Z.ltb_ge n 8)) by lia. cbv beta iota zeta.
  rewrite Z.geb_leb, (proj2 (Z.leb_gt _ _)) by lia.
  destruct (dw - di >=? 0) eqn:E; subst a c1.
  - apply Z.geb_le in E. cbv beta iota zeta.
    rewrite lfwd_LS by (rewrite ?HL, ?Z2Nat.id; lia). rewrite Z2Nat.id by lia.
    f_equal; [f_equal; lia |]. f_equal; [f_equal; lia |]. f_equal; lia.
  - rewrite lfwd_LS by (rewrite ?Z2Nat.id; lia). rewrite Z2Nat.id by lia. rewrite !Z.add_0_r, Z.sub_0_r.
    f_equal. f_equal; [f_equal; lia |]. f_equal; lia.
Qed.

(* ---------- ZSTD_safecopyDstBeforeSrc's outcome as BlkSeqXMem.lsdbs ---------- *)
Lemma lsdbs_short (c: list val) (si di n: Z) :
  n < 8 \/ -8 < di - si -> listcopy c si di (Z.to_nat n) = lsdbs c di si n.
Proof.
  intros H. unfold lsdbs.
  replace ((n <? 8) || (di - si >? -8))%bool with true
    by (destruct H; [rewrite (proj2 (Z.ltb_lt _ _)) by lia | rewrite (proj2 (Z.gtb_lt _ _)) by lia;
                     rewrite orb_true_r]; reflexivity).
  rewrite lfwd_LW. reflexivity.
Qed.

Lemma lsdbs_tail (c: list val) (si di n E0 a: Z) :
  8 <= n -> di - si <= -8 ->
  (a, listcopy c si di (Z.to_nat E0)) =
    (if andb (n >=? 32) (di - si <? -16) then (n - 32, lwild c di LW si (n - 32) false) else (0, c)) ->
  listcopy (listcopy c si di (Z.to_nat E0)) (si + a) (di + a) (Z.to_nat (n - a)) = lsdbs c di si n.
Proof.
  intros Hn Hd HaE.
  assert (HE: listcopy c si di (Z.to_nat E0) =
    (if andb (n >=? 32) (di - si <? -16) then lwild c di LW si (n - 32) false else c))
    by (destruct (andb (n >=? 32) (di - si <? -16)); injection HaE; intros; assumption).
  assert (Ha: a = (if andb (n >=? 32) (di - si <? -16) then n - 32 else 0))
    by (destruct (andb (n >=? 32) (di - si <? -16)); injection HaE; intros; assumption).
  clear HaE. unfold lsdbs.
  rewrite (proj2 (Z.ltb_ge n 8)) by lia.
  replace (di - si >? -8) with false by (rewrite Z.gtb_ltb; symmetry; apply Z.ltb_ge; lia).
  simpl orb. cbv beta iota zeta. rewrite HE, Ha.
  destruct (andb (n >=? 32) (di - si <? -16)); rewrite lfwd_LW; f_equal; try lia; apply f_equal; lia.
Qed.

Definition COPY_ids : list ident :=
  [ _ZSTD_wildcopy; _ZSTD_seqCopy; _ZSTD_overlapCopy8; _ZSTD_safecopy; _ZSTD_safecopyDstBeforeSrc ].
Definition COPY_exports : funspecs :=
  [ ZSTD_wildcopy_spec; ZSTD_seqCopy_spec; ZSTD_overlapCopy8_spec; ZSTD_safecopy_spec;
    ZSTD_safecopyDstBeforeSrc_spec ].
Definition COPY_imports : funspecs := [].
Definition COPY_obligation : Prop := subtree_ok COPY_ids COPY_exports (G_BLK ++ COPY_imports).

Lemma body_ZSTD_seqCopy : semax_body Vprog (G_BLK ++ COPY_exports) f_ZSTD_seqCopy ZSTD_seqCopy_spec.
Proof.
  start_function.
  unfold seqrep.
  forward. forward. forward. forward. forward. forward.
  entailer!.
Qed.

Ltac simp_ptr :=
  simpl force_val; rewrite ?sem_add_pl_ptr_special by auto; simpl force_val;
  rewrite ?sem_add_pi' by (auto; rep_lia);
  rewrite ?offset_offset_val; simpl sizeof; rewrite ?Z.mul_1_l.

Lemma fc_tuchar_bound (N: Z) (p: val) :
  field_compatible (tarray tuchar N) [] p -> isptr p /\ N < Ptrofs.modulus.
Proof.
  intros [Hp [_ [Hsz _]]]. destruct p; try contradiction. split; [exact I |].
  simpl in Hsz. pose proof (Ptrofs.unsigned_range i). rewrite Z.mul_1_l in Hsz. lia.
Qed.

(* the source cell x of a copy inside one array is defined: from copy_src_def (the wild copies), or from defined
   source cells [si, b) before the destination (ZSTD_overlapCopy8) *)
Ltac lc_read :=
  match goal with
  | Hc: copy_src_def ?c ?si ?di ?n |- is_byte_val (Znth _ (listcopy ?c ?si ?di (Z.to_nat _))) =>
      apply (csd_read c si di n); [exact Hc | lia ..]
  | Hb: Forall is_byte_val (sublist ?si ?b ?c) |- is_byte_val (Znth _ (listcopy ?c ?si ?di (Z.to_nat _))) =>
      apply (lc_read_gap c si di _ b); [lia | lia | lia | lia | exact Hb | lia | lia]
  end.

(* the last conjunct of copy_pre for a copy inside one array: the m source bytes are defined *)
Ltac wc_bytes :=
  first [ apply fa_sub_prefix | rewrite ?Z.add_0_l; apply fa_sub_suffix ];
  [ (rewrite ?Zlength_listcopy by lia; lia) .. | ];
  apply Forall_sublist_pt; [lia | rewrite ?Zlength_listcopy by lia; lia | ];
  let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; lc_read.

(* call ZSTD_copy4/8/16 (m bytes) at op = di + k, ip = si + k inside the array c, whose first di + k bytes
   are already the forward copy of k bytes *)
Ltac wc_side := try solve [lia | auto | apply Zlength_listcopy; lia].

Ltac wc_call k m :=
  match goal with |- context [data_at ?sh (tarray tuchar (Zlength ?c)) (listcopy ?c ?si ?di (Z.to_nat k)) ?p] =>
  first
  [ assert (si + m <= di) by lia;
    sep_apply (tuchar_split_N sh p (Zlength c) (listcopy c si di (Z.to_nat k)) (di + k)); wc_side; Intros;
    forward_call (sh, p, sublist 0 (di + k) (listcopy c si di (Z.to_nat k)), si + k, sh, offset_val (di + k) p,
                  sublist (di + k) (Zlength (listcopy c si di (Z.to_nat k))) (listcopy c si di (Z.to_nat k)), 0);
    [ unfold copy_pre; rewrite ?Zlength_listcopy by lia;
      rewrite !Zlength_sublist by (rewrite ?Zlength_listcopy; lia);
      split; [apply writable_readable; assumption |]; split; [assumption |];
      repeat (split; [lia |]); wc_bytes | ];
    sep_apply (within_step_sb sh p c si di k m); wc_side
  | assert (di + m <= si) by lia;
    sep_apply (tuchar_split_N sh p (Zlength c) (listcopy c si di (Z.to_nat k)) (si + k)); wc_side; Intros;
    forward_call (sh, offset_val (si + k) p,
                  sublist (si + k) (Zlength (listcopy c si di (Z.to_nat k))) (listcopy c si di (Z.to_nat k)), 0,
                  sh, p, sublist 0 (si + k) (listcopy c si di (Z.to_nat k)), di + k);
    [ unfold copy_pre; rewrite ?Zlength_listcopy by lia;
      rewrite !Zlength_sublist by (rewrite ?Zlength_listcopy; lia);
      split; [apply writable_readable; assumption |]; split; [assumption |];
      repeat (split; [lia |]); wc_bytes | ];
    sep_apply (within_step_ds sh p c si di k m); wc_side ]
  end.

(* the wild copy's state inside one array after k bytes *)
Local Notation wc_state sh p c si di oe k gv :=
  (PROP () LOCAL (temp _ip (offset_val (si + k) p); temp _op (offset_val (di + k) p);
                 temp _oend (offset_val oe p); gvars gv)
  SEP (data_at sh (tarray tuchar (Zlength c)) (listcopy c si di (Z.to_nat k)) p; zstd_globals gv))%assert.

(* one COPY8 / COPY16 macro: do { ZSTD_copyM(op, ip); op += m; ip += m; } while (0) *)
Ltac wc_once sh p c si di oe gv k m :=
  forward_loop (wc_state sh p c si di oe k gv)
    continue: (wc_state sh p c si di oe (k + m) gv) break: (wc_state sh p c si di oe (k + m) gv);
  [ entailer!
  | wc_call k m; forward; forward; simp_ptr; entailer!;
    repeat match goal with |- _ /\ _ => split end; try (f_equal; lia)
  | forward; entailer!
  | ].

(* close a within wild copy whose array is the forward copy of E = wc_ext .. n bytes *)
(* a typed_true/typed_false hypothesis on op < oend inside one array: keep the consistent case *)
Ltac cmp_simpl :=
  match goal with
  | Hfc: field_compatible (tarray tuchar ?N) [] ?p,
    H: context [sem_cmp_pp Clt (offset_val _ ?p) (offset_val _ ?p)] |- _ =>
      rewrite (cp_cmp N) in H by (auto; lia);
      match type of H with context [zlt ?x ?y] =>
        destruct (zlt x y); [ try solve [inv H] | try solve [inv H] ] end
  end.

Ltac if_absurd :=
  first [ contradiction | discriminate
        | match goal with H: Int.one = Int.zero |- _ => exfalso; apply Int.one_not_zero; exact H end ].

Ltac unfold_post :=
  repeat match goal with P := @abbreviate ret_assert _ |- _ => unfold abbreviate in P; subst P end;
  simpl_ret_assert.

(* the new exact PROP of a within wild copy: lwild is the forward copy of wc_ext bytes *)
Ltac wc_exact :=
  first [ rewrite lwild_8 by lia
        | rewrite lwild_16 by first [lia | left; lia | right; split; [reflexivity | lia]] ];
  reflexivity.

Ltac wc_ret_within :=
  unfold_post; unfold OV_SRC_BEFORE_DST, OV_NO_OVERLAP;
  change (1 =? 1) with true; change (0 =? 1) with false; rewrite ?andb_true_l, ?andb_false_l;
  repeat match goal with
  | H: ?x < ?y |- context [?x <? ?y] => rewrite (proj2 (Z.ltb_lt x y) H)
  | H: ?y <= ?x |- context [?x <? ?y] => rewrite (proj2 (Z.ltb_ge x y) H)
  end;
  match goal with |- context [data_at ?sh (tarray tuchar (Zlength ?c)) (listcopy ?c ?si ?di (Z.to_nat (wc_ext ?b ?n))) ?p] =>
    pose proof (wc_ext_bounds b n ltac:(lia));
    Exists (sublist (di + n) (di + n + 32) (listcopy c si di (Z.to_nat (wc_ext b n))));
    entailer!;
    repeat match goal with |- _ /\ _ => split end;
    first
      [ solve [rewrite Zlength_sublist; try lia; rewrite Zlength_listcopy; lia]
      | solve [rewrite wc_post_listcopy by lia; apply derives_refl]
      | solve [rewrite wc_post_listcopy by lia; wc_exact] ]
  end.

(* the disjoint wild copy's state after k bytes *)
Local Notation dj_state shs ps cs shd pd cd oe k gv :=
  (PROP () LOCAL (temp _ip (offset_val k ps); temp _op (offset_val k pd);
                 temp _oend (offset_val oe pd); gvars gv)
  SEP (data_at shd (tarray tuchar (Zlength cd)) (dj cs cd k) pd;
       data_at shs (tarray tuchar (Zlength cs)) cs ps; zstd_globals gv))%assert.

Ltac dj_call k m :=
  match goal with |- context [data_at ?shd (tarray tuchar (Zlength ?cd)) (dj ?cs ?cd k) ?pd] =>
  match goal with |- context [data_at ?shs (tarray tuchar (Zlength cs)) cs ?ps] =>
    sep_apply (tuchar_retype shd (Zlength cd) (dj cs cd k) pd); [apply Zlength_dj; lia |];
    forward_call (shs, ps, cs, k, shd, pd, dj cs cd k, k);
    [ unfold copy_pre; rewrite Zlength_dj by lia; split; [assumption |]; split; [assumption |];
      repeat (split; [lia |]); apply fa_bv; fa_range | ];
    rewrite dj_step by lia; rewrite Zlength_dj by lia
  end end.

Ltac dj_once shs ps cs shd pd cd oe gv k m :=
  forward_loop (dj_state shs ps cs shd pd cd oe k gv)
    continue: (dj_state shs ps cs shd pd cd oe (k + m) gv) break: (dj_state shs ps cs shd pd cd oe (k + m) gv);
  [ entailer!
  | dj_call k m; forward; forward; simp_ptr; entailer!;
    repeat match goal with |- _ /\ _ => split end; try (f_equal; lia)
  | forward; entailer!
  | ].

Ltac dj_ret :=
  unfold_post;
  match goal with |- context [data_at ?shd (tarray tuchar (Zlength ?cd)) (dj ?cs ?cd (wc_ext ?b ?n)) ?pd] =>
    pose proof (wc_ext_bounds b n ltac:(lia));
    Exists (sublist n (n + 32) (dj cs cd (wc_ext b n)));
    unfold OV_NO_OVERLAP in *; entailer!;
    repeat match goal with |- _ /\ _ => split end;
    first
      [ solve [rewrite Zlength_sublist; try lia; rewrite Zlength_dj; lia]
      | solve [rewrite (dj_post cs cd n (wc_ext b n)) by lia; unfold dj; cancel]
      | solve [rewrite (dj_post cs cd n (wc_ext b n)) by lia; unfold dj; rewrite lwild_LS by lia; list_solve] ]
  end.

Lemma body_ZSTD_wildcopy : semax_body Vprog (G_BLK ++ COPY_exports) f_ZSTD_wildcopy ZSTD_wildcopy_spec.
Proof.
  start_function. destruct within.
  - destruct H1 as [Hsh [Hsi [Hdi [Hcs [Hdn [Hsn [Hov1 Hov0]]]]]]]; [reflexivity|]. clear H2.
    assert (Hcsd := H3 eq_refl). clear H3 H4.
    assert_PROP (field_compatible (tarray tuchar (Zlength c)) [] p) as Hfc by entailer!.
    destruct (fc_tuchar_bound _ _ Hfc) as [Hp Hcm].
    unfold WILDCOPY_OVERLENGTH, WILDCOPY_VECLEN in *.
    assert (Hn64: 0 <= n <= Int64.max_unsigned)
      by (assert (Ptrofs.modulus = Int64.modulus) by reflexivity; unfold Int64.max_unsigned; lia).
    rewrite !arr_field_address by (auto; lia). simpl sizeof. rewrite !Z.mul_1_l.
    forward. forward. forward. simp_ptr.
    destruct H0 as [-> | ->].
    + (* ZSTD_no_overlap: the 16-byte path *)
      specialize (Hov0 eq_refl). clear Hov1.
      forward_if (temp _t'1 (Vint (Int.repr 0))).
      { discriminate. }
      { forward. entailer!. }
      forward_if. { contradiction. }
      replace_SEP 1 (data_at sh (tarray tuchar (Zlength c)) (listcopy c si di (Z.to_nat 0)) p).
      { entailer!. }
      change (listcopy c si di 0) with (listcopy c si di (Z.to_nat 0)).
      destruct Hov0 as [Hdir | Hdir].
      * wc_call 0 16.
        forward_if.
        { rewrite !Int64.unsigned_repr in * by rep_lia.
          replace (Z.to_nat (0 + 16)) with (Z.to_nat (wc_ext false n))
            by (rewrite wc_ext_le16 by (unfold WILDCOPY_VECLEN; lia); reflexivity).
          forward. wc_ret_within. }
        forward. forward. simp_ptr.
        rewrite !Int64.unsigned_repr in * by rep_lia.
        forward_loop (EX j: Z, PROP (0 <= j; 16 + 32 * j < n)
           LOCAL (temp _ip (offset_val (si + (16 + 32 * j)) p); temp _op (offset_val (di + (16 + 32 * j)) p);
                  temp _oend (offset_val (di + n) p); gvars gv)
           SEP (data_at sh (tarray tuchar (Zlength c)) (listcopy c si di (Z.to_nat (16 + 32 * j))) p;
                zstd_globals gv))%assert
          continue: (EX j: Z, PROP (0 <= j; 16 + 32 * j < n)
           LOCAL (temp _ip (offset_val (si + (16 + 32 * j + 32)) p); temp _op (offset_val (di + (16 + 32 * j + 32)) p);
                  temp _oend (offset_val (di + n) p); gvars gv)
           SEP (data_at sh (tarray tuchar (Zlength c)) (listcopy c si di (Z.to_nat (16 + 32 * j + 32))) p;
                zstd_globals gv))%assert
          break: (PROP () LOCAL ()
           SEP (data_at sh (tarray tuchar (Zlength c)) (listcopy c si di (Z.to_nat (wc_ext false n))) p;
                zstd_globals gv))%assert.
        { Exists 0. entailer!. }
        { Intros j. wc_once sh p c si di (di + n) gv (16 + 32 * j) 16.
          wc_once sh p c si di (di + n) gv (16 + 32 * j + 16) 16.
          Exists j. replace (16 + 32 * j + 16 + 16) with (16 + 32 * j + 32) by lia. entailer!. }
        { Intros j. forward_if.
          - apply cp_test_order; auto; try lia; apply writable_readable; auto.
          - cmp_simpl.
            forward. Exists (j + 1). replace (16 + 32 * (j + 1)) with (16 + 32 * j + 32) by lia. entailer!.
          - cmp_simpl.
            forward. rewrite (wc_ext_long_exit j n) by (unfold WILDCOPY_VECLEN; lia).
            unfold WILDCOPY_VECLEN. replace (16 + 32 * (j + 1)) with (16 + 32 * j + 32) by lia.
            entailer!. }
        wc_ret_within.
      * wc_call 0 16.
        forward_if.
        { rewrite !Int64.unsigned_repr in * by rep_lia.
          replace (Z.to_nat (0 + 16)) with (Z.to_nat (wc_ext false n))
            by (rewrite wc_ext_le16 by (unfold WILDCOPY_VECLEN; lia); reflexivity).
          forward. wc_ret_within. }
        forward. forward. simp_ptr.
        rewrite !Int64.unsigned_repr in * by rep_lia.
        forward_loop (EX j: Z, PROP (0 <= j; 16 + 32 * j < n)
           LOCAL (temp _ip (offset_val (si + (16 + 32 * j)) p); temp _op (offset_val (di + (16 + 32 * j)) p);
                  temp _oend (offset_val (di + n) p); gvars gv)
           SEP (data_at sh (tarray tuchar (Zlength c)) (listcopy c si di (Z.to_nat (16 + 32 * j))) p;
                zstd_globals gv))%assert
          continue: (EX j: Z, PROP (0 <= j; 16 + 32 * j < n)
           LOCAL (temp _ip (offset_val (si + (16 + 32 * j + 32)) p); temp _op (offset_val (di + (16 + 32 * j + 32)) p);
                  temp _oend (offset_val (di + n) p); gvars gv)
           SEP (data_at sh (tarray tuchar (Zlength c)) (listcopy c si di (Z.to_nat (16 + 32 * j + 32))) p;
                zstd_globals gv))%assert
          break: (PROP () LOCAL ()
           SEP (data_at sh (tarray tuchar (Zlength c)) (listcopy c si di (Z.to_nat (wc_ext false n))) p;
                zstd_globals gv))%assert.
        { Exists 0. entailer!. }
        { Intros j. wc_once sh p c si di (di + n) gv (16 + 32 * j) 16.
          wc_once sh p c si di (di + n) gv (16 + 32 * j + 16) 16.
          Exists j. replace (16 + 32 * j + 16 + 16) with (16 + 32 * j + 32) by lia. entailer!. }
        { Intros j. forward_if.
          - apply cp_test_order; auto; try lia; apply writable_readable; auto.
          - cmp_simpl.
            forward. Exists (j + 1). replace (16 + 32 * (j + 1)) with (16 + 32 * j + 32) by lia. entailer!.
          - cmp_simpl.
            forward. rewrite (wc_ext_long_exit j n) by (unfold WILDCOPY_VECLEN; lia).
            unfold WILDCOPY_VECLEN. replace (16 + 32 * (j + 1)) with (16 + 32 * j + 32) by lia.
            entailer!. }
        wc_ret_within.
    + (* ZSTD_overlap_src_before_dst *)
      specialize (Hov1 eq_refl). clear Hov0.
      forward_if (temp _t'1 (Vint (if zlt (di - si) 16 then Int.one else Int.zero))).
      { forward.
        - entailer!. apply prop_right, cp_sameblock; auto.
        - assert (Ptrofs.max_signed = Int64.max_signed) by reflexivity.
          rewrite cp_diff_lt by (auto; rep_lia).
          entailer!. }
      { contradiction. }
      replace_SEP 1 (data_at sh (tarray tuchar (Zlength c)) (listcopy c si di (Z.to_nat 0)) p).
      { entailer!. }
      change (listcopy c si di 0) with (listcopy c si di (Z.to_nat 0)).
      destruct (zlt (di - si) 16) as [Hlt | Hge].
      * (* the 8-byte loop *)
        forward_if. 2: { if_absurd. }
        forward_loop (EX j: Z, PROP (0 <= j; j = 0 \/ 8 * j < n)
           LOCAL (temp _ip (offset_val (si + 8 * j) p); temp _op (offset_val (di + 8 * j) p);
                  temp _oend (offset_val (di + n) p); gvars gv)
           SEP (data_at sh (tarray tuchar (Zlength c)) (listcopy c si di (Z.to_nat (8 * j))) p;
                zstd_globals gv))%assert
          continue: (EX j: Z, PROP (0 <= j; j = 0 \/ 8 * j < n)
           LOCAL (temp _ip (offset_val (si + (8 * j + 8)) p); temp _op (offset_val (di + (8 * j + 8)) p);
                  temp _oend (offset_val (di + n) p); gvars gv)
           SEP (data_at sh (tarray tuchar (Zlength c)) (listcopy c si di (Z.to_nat (8 * j + 8))) p;
                zstd_globals gv))%assert
          break: (PROP () LOCAL ()
           SEP (data_at sh (tarray tuchar (Zlength c)) (listcopy c si di (Z.to_nat (wc_ext true n))) p;
                zstd_globals gv))%assert.
        { Exists 0. entailer!. }
        { Intros j. wc_once sh p c si di (di + n) gv (8 * j)%Z 8. Exists j. entailer!. }
        { Intros j. forward_if.
          - apply cp_test_order; auto; try lia; apply writable_readable; auto.
          - cmp_simpl.
            forward. Exists (j + 1). replace (8 * (j + 1))%Z with (8 * j + 8)%Z by lia. entailer!.
          - cmp_simpl.
            forward. rewrite (wc_ext_short_exit j n) by lia.
            replace (8 * (j + 1))%Z with (8 * j + 8)%Z by lia.
            entailer!. }
        wc_ret_within.
      * assert (Hdir: si + 16 <= di) by lia.
        forward_if. { contradiction. }
        assert (Hge': 16 <= di - si) by lia.
        wc_call 0 16.
        forward_if.
        { rewrite !Int64.unsigned_repr in * by rep_lia.
          replace (Z.to_nat (0 + 16)) with (Z.to_nat (wc_ext false n))
            by (rewrite wc_ext_le16 by (unfold WILDCOPY_VECLEN; lia); reflexivity).
          forward. wc_ret_within. }
        forward. forward. simp_ptr.
        rewrite !Int64.unsigned_repr in * by rep_lia.
        forward_loop (EX j: Z, PROP (0 <= j; 16 + 32 * j < n)
           LOCAL (temp _ip (offset_val (si + (16 + 32 * j)) p); temp _op (offset_val (di + (16 + 32 * j)) p);
                  temp _oend (offset_val (di + n) p); gvars gv)
           SEP (data_at sh (tarray tuchar (Zlength c)) (listcopy c si di (Z.to_nat (16 + 32 * j))) p;
                zstd_globals gv))%assert
          continue: (EX j: Z, PROP (0 <= j; 16 + 32 * j < n)
           LOCAL (temp _ip (offset_val (si + (16 + 32 * j + 32)) p); temp _op (offset_val (di + (16 + 32 * j + 32)) p);
                  temp _oend (offset_val (di + n) p); gvars gv)
           SEP (data_at sh (tarray tuchar (Zlength c)) (listcopy c si di (Z.to_nat (16 + 32 * j + 32))) p;
                zstd_globals gv))%assert
          break: (PROP () LOCAL ()
           SEP (data_at sh (tarray tuchar (Zlength c)) (listcopy c si di (Z.to_nat (wc_ext false n))) p;
                zstd_globals gv))%assert.
        { Exists 0. entailer!. }
        { Intros j. wc_once sh p c si di (di + n) gv (16 + 32 * j) 16.
          wc_once sh p c si di (di + n) gv (16 + 32 * j + 16) 16.
          Exists j. replace (16 + 32 * j + 16 + 16) with (16 + 32 * j + 32) by lia. entailer!. }
        { Intros j. forward_if.
          - apply cp_test_order; auto; try lia; apply writable_readable; auto.
          - cmp_simpl.
            forward. Exists (j + 1). replace (16 + 32 * (j + 1)) with (16 + 32 * j + 32) by lia. entailer!.
          - cmp_simpl.
            forward. rewrite (wc_ext_long_exit j n) by (unfold WILDCOPY_VECLEN; lia).
            unfold WILDCOPY_VECLEN. replace (16 + 32 * (j + 1)) with (16 + 32 * j + 32) by lia.
            entailer!. }
        wc_ret_within.
  - destruct H2 as [Hshs [Hshd [-> [Hcs Hcd]]]]; [reflexivity|]. clear H1 H0.
    assert (Hcsb := H4 eq_refl). clear H3 H4.
    assert_PROP (field_compatible (tarray tuchar (Zlength cs)) [] ps /\
                 field_compatible (tarray tuchar (Zlength cd)) [] pd) as Hfsd by entailer!.
    destruct Hfsd as [Hfs Hfd].
    destruct (fc_tuchar_bound _ _ Hfs) as [Hps Hcsm].
    destruct (fc_tuchar_bound _ _ Hfd) as [Hpd Hcdm].
    unfold WILDCOPY_OVERLENGTH, WILDCOPY_VECLEN in *.
    assert (Hn64: 0 <= n <= Int64.max_unsigned)
      by (assert (Ptrofs.modulus = Int64.modulus) by reflexivity; unfold Int64.max_unsigned; lia).
    Intros.
    forward. forward. forward. simp_ptr.
    forward_if (temp _t'1 (Vint (Int.repr 0))).
    { if_absurd. }
    { forward. entailer!. }
    forward_if. { if_absurd. }
    replace_SEP 2 (data_at shd (tarray tuchar (Zlength cd)) (dj cs cd 0) pd).
    { rewrite dj_0. entailer!. }
    dj_call 0 16.
    forward_if.
    { rewrite !Int64.unsigned_repr in * by rep_lia.
      replace (0 + 16) with (wc_ext false n) by (rewrite wc_ext_le16 by (unfold WILDCOPY_VECLEN; lia); reflexivity).
      forward. dj_ret. }
    forward. forward. simp_ptr.
    rewrite !Int64.unsigned_repr in * by rep_lia.
    forward_loop (EX j: Z, PROP (0 <= j; 16 + 32 * j < n)
       LOCAL (temp _ip (offset_val (16 + 32 * j) ps); temp _op (offset_val (16 + 32 * j) pd);
              temp _oend (offset_val n pd); gvars gv)
       SEP (data_at shd (tarray tuchar (Zlength cd)) (dj cs cd (16 + 32 * j)) pd;
            data_at shs (tarray tuchar (Zlength cs)) cs ps; zstd_globals gv))%assert
      continue: (EX j: Z, PROP (0 <= j; 16 + 32 * j < n)
       LOCAL (temp _ip (offset_val (16 + 32 * j + 32) ps); temp _op (offset_val (16 + 32 * j + 32) pd);
              temp _oend (offset_val n pd); gvars gv)
       SEP (data_at shd (tarray tuchar (Zlength cd)) (dj cs cd (16 + 32 * j + 32)) pd;
            data_at shs (tarray tuchar (Zlength cs)) cs ps; zstd_globals gv))%assert
      break: (PROP () LOCAL ()
       SEP (data_at shd (tarray tuchar (Zlength cd)) (dj cs cd (wc_ext false n)) pd;
            data_at shs (tarray tuchar (Zlength cs)) cs ps; zstd_globals gv))%assert.
    { Exists 0. entailer!. }
    { Intros j. dj_once shs ps cs shd pd cd n gv (16 + 32 * j) 16.
      dj_once shs ps cs shd pd cd n gv (16 + 32 * j + 16) 16.
      Exists j. replace (16 + 32 * j + 16 + 16) with (16 + 32 * j + 32) by lia. entailer!. }
    { Intros j. forward_if.
      - rewrite sepcon_assoc. apply cp_test_order; auto; try lia; apply writable_readable; auto.
      - cmp_simpl.
        forward. Exists (j + 1). replace (16 + 32 * (j + 1)) with (16 + 32 * j + 32) by lia. entailer!.
      - cmp_simpl.
        forward. rewrite (wc_ext_long_exit j n) by (unfold WILDCOPY_VECLEN; lia).
        unfold WILDCOPY_VECLEN. replace (16 + 32 * (j + 1)) with (16 + 32 * j + 32) by lia.
        entailer!. }
    dj_ret.
Qed.

Definition zg_rest_dec (gv: globals) : mpred := (
  data_at Ews tint g_debuglevel_val (gv _g_debuglevel) *
  data_at Ers (tarray tuint 32) DeBruijnBytePos_val (gv _DeBruijnBytePos) *
  data_at Ers (tarray tuint 32) DeBruijnClz_val (gv _DeBruijnClz) *
  data_at Ers tulong zeroFilled_val (gv _zeroFilled) *
  data_at Ers (Tstruct ___gp_ZSTD_customMem noattr) ZSTD_defaultCMem_val (gv _ZSTD_defaultCMem) *
  data_at Ers (tarray tuint 3) repStartValue_val (gv _repStartValue) *
  data_at Ers (tarray tulong 4) ZSTD_fcs_fieldSize_val (gv _ZSTD_fcs_fieldSize) *
  data_at Ers (tarray tulong 4) ZSTD_did_fieldSize_val (gv _ZSTD_did_fieldSize) *
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
  eb_res gv)%logic.

Lemma zg_dec gv : zstd_globals gv =
  (data_at Ers (tarray tuint 8) dec32table_val (gv _dec32table) *
   data_at Ers (tarray tint 8) dec64table_val (gv _dec64table) * zg_rest_dec gv)%logic.
Proof. unfold zstd_globals, zg_rest_dec. apply pred_ext; cancel. Qed.

Lemma oc8_off_ge8 (o: Z) : 8 <= o -> oc8_off o = o.
Proof.
  intros H. unfold oc8_off. destruct o as [|q|q]; try lia.
  destruct q as [q|q|]; try reflexivity; try lia;
  destruct q as [q|q|]; try reflexivity; try lia;
  destruct q as [q|q|]; try reflexivity; try lia.
Qed.

(* the distance after ZSTD_overlapCopy8 is a multiple of the offset, at least 8 (and at most offset + 7) *)
Lemma oc8_off_facts (o: Z) : 1 <= o -> 8 <= oc8_off o <= o + 7 /\ o <= oc8_off o /\ oc8_off o mod o = 0.
Proof.
  intros H. destruct (Z_lt_le_dec o 8) as [L | L].
  - assert (o = 1 \/ o = 2 \/ o = 3 \/ o = 4 \/ o = 5 \/ o = 6 \/ o = 7) as E by lia.
    destruct E as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]; (split; [simpl; lia | split; [simpl; lia | reflexivity]]).
  - rewrite oc8_off_ge8 by lia. split; [lia | split; [lia | apply Z_mod_same_full]].
Qed.

Lemma fa_add_tuchar (N: Z) (p: val) (i k: Z) :
  field_compatible (tarray tuchar N) [] p -> 0 <= i + k < N -> 0 <= k <= 8 ->
  force_val (sem_add_ptr_int tuchar Signed (offset_val i p) (Vint (Int.repr k))) =
  field_address (tarray tuchar N) (SUB (i + k)) p.
Proof.
  intros Hfc Hik Hk. destruct (fc_tuchar_bound _ _ Hfc) as [Hp _].
  rewrite sem_add_pi' by (auto; rep_lia). rewrite arr_field_address by auto.
  simpl sizeof. rewrite !Z.mul_1_l, offset_offset_val. f_equal; lia.
Qed.

Lemma byte_tc_val (v: val) : is_byte_val v -> tc_val tuchar v.
Proof. intros (z & Hz & ->). simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. Qed.

Lemma byte_cast_id (v: val) : is_byte_val v -> force_val (sem_cast_i2i I8 Unsigned v) = v.
Proof.
  intros (z & Hz & ->). simpl. f_equal. apply Int.same_bits_eq. intros i Hi.
  rewrite Int.bits_zero_ext by lia. rewrite Int.testbit_repr by auto.
  destruct (zlt i 8); [reflexivity |].
  symmetry. apply (Zbits.Ztestbit_above 8); [| lia]. change (two_power_nat 8) with 256. lia.
Qed.

Lemma byte_is_int (v: val) : is_byte_val v -> is_int I8 Unsigned v.
Proof. intros (z & Hz & ->). simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. Qed.

Lemma byte_at_eq (l: list val) (x y: Z) : is_byte_val (Znth x l) -> x = y -> is_byte_val (Znth y l).
Proof. intros H <-. exact H. Qed.

(* one byte of a forward copy: c'[di+k] := c'[si+k] *)
Lemma byte_step (c: list val) (si di k: Z) :
  0 <= k -> is_byte_val (Znth (si + k) (listcopy c si di (Z.to_nat k))) ->
  upd_Znth (di + k) (listcopy c si di (Z.to_nat k))
    (force_val (sem_cast_i2i I8 Unsigned (Znth (si + k) (listcopy c si di (Z.to_nat k))))) =
  listcopy c si di (Z.to_nat (k + 1)).
Proof.
  intros Hk Hb. rewrite byte_cast_id by auto.
  replace (Z.to_nat (k + 1)) with (S (Z.to_nat k)) by lia.
  rewrite listcopy_snoc, Z2Nat.id by lia. reflexivity.
Qed.

Lemma byte_step_gen (c: list val) (si di k: Z) (A B: Z) (L1 L2: list val) (m: nat) :
  0 <= k -> is_byte_val (Znth (si + k) (listcopy c si di (Z.to_nat k))) ->
  A = di + k -> B = si + k -> L1 = listcopy c si di (Z.to_nat k) -> L2 = listcopy c si di (Z.to_nat k) ->
  m = Z.to_nat (k + 1) ->
  upd_Znth A L1 (force_val (sem_cast_i2i I8 Unsigned (Znth B L2))) = listcopy c si di m.
Proof. intros Hk Hb -> -> -> -> ->. apply byte_step; auto. Qed.

Lemma byte_step_nocast (c: list val) (si di k: Z) (A B: Z) (L1 L2: list val) (m: nat) :
  0 <= k -> A = di + k -> B = si + k -> L1 = listcopy c si di (Z.to_nat k) -> L2 = listcopy c si di (Z.to_nat k) ->
  m = Z.to_nat (k + 1) ->
  upd_Znth A L1 (Znth B L2) = listcopy c si di m.
Proof.
  intros Hk -> -> -> -> ->. replace (Z.to_nat (k + 1)) with (S (Z.to_nat k)) by lia.
  rewrite listcopy_snoc, Z2Nat.id by lia. reflexivity.
Qed.

(* the byte assignment op[k] = ip[k] inside the array c (op at di, ip at si); state: the forward copy of k bytes *)
Ltac oc_byte sh p c si di k :=
  forward; forward;
  assert (force_val (sem_add_ptr_int tuchar Signed (offset_val si p) (Vint (Int.repr k))) =
          field_address (tarray tuchar (Zlength c)) (SUB (si + k)) p) by (apply fa_add_tuchar; auto; lia);
  assert (is_byte_val (Znth (si + k) (listcopy c si di (Z.to_nat k)))) by (apply listcopy_bytes; auto; lia);
  forward;
  [ match goal with |- semax _ _ _ _ => idtac | _ =>
      entailer!; first [ apply byte_tc_val | apply byte_is_int ]; eapply byte_at_eq; [eassumption | lia] end .. ];
  assert (force_val (sem_add_ptr_int tuchar Signed (offset_val di p) (Vint (Int.repr k))) =
          field_address (tarray tuchar (Zlength c)) (SUB (di + k)) p) by (apply fa_add_tuchar; auto; lia);
  forward;
  replace_SEP 5 (data_at sh (tarray tuchar (Zlength c)) (listcopy c si di (Z.to_nat (k + 1))) p);
  [ entailer!; try (unfold data_at; apply derives_refl'; f_equal;
    first [ apply (byte_step_gen c si di k); [lia | assumption | lia | lia | reflexivity | reflexivity | reflexivity]
          | apply (byte_step_nocast c si di k); [lia | lia | lia | reflexivity | reflexivity | reflexivity] ])
  | ].


Lemma cp_sub_pi (p: val) (a k: Z) : isptr p -> Int.min_signed <= k <= Int.max_signed ->
  force_val (sem_sub_pi tuchar Signed (offset_val a p) (Vint (Int.repr k))) =
  offset_val (a - k) p.
Proof.
  intros. destruct p; try contradiction. unfold sem_sub_pi. simpl. f_equal.
  rewrite Ptrofs.mul_commut, Ptrofs.mul_one.
  rewrite <- (Ptrofs.repr_unsigned i). rewrite !ptrofs_add_repr.
  unfold Ptrofs.of_ints. rewrite Int.signed_repr by lia.
  rewrite ptrofs_sub_repr. f_equal. lia.
Qed.

Local Opaque listcopy.

(* one-byte ZSTD_memmove inside the array: one step of the forward copy *)
Lemma mm_result_step (c: list val) (si di k: Z) :
  0 <= di -> 0 <= k -> di + k + 1 <= Zlength c -> 0 <= si + k -> si + k + 1 <= Zlength c ->
  mm_result (listcopy c si di (Z.to_nat k)) (Zlength c) (si + k) (di + k) 1 = listcopy c si di (Z.to_nat (k + 1)).
Proof.
  intros. replace (Z.to_nat (k + 1)) with (S (Z.to_nat k)) by lia.
  rewrite listcopy_snoc, Z2Nat.id by lia.
  assert (HL: Zlength (listcopy c si di (Z.to_nat k)) = Zlength c) by (apply Zlength_listcopy; lia).
  unfold mm_result. rewrite (sublist_one (si + k)) by lia.
  rewrite upd_Znth_unfold by lia. rewrite HL. reflexivity.
Qed.

Lemma mm_post_within (sh: share) (p: val) (N: Z) (c: list val) (si di n: Z) :
  mm_post (mm_within sh p N c si di n) = data_at sh (tarray tuchar N) (mm_result c N si di n) p.
Proof. reflexivity. Qed.

Lemma add_off_tuchar (p: val) (i k: Z) : isptr p -> 0 <= k <= 8 ->
  force_val (sem_add_ptr_int tuchar Signed (offset_val i p) (Vint (Int.repr k))) = offset_val (i + k) p.
Proof.
  intros Hp Hk. rewrite sem_add_pi' by (auto; rep_lia). simpl sizeof.
  rewrite offset_offset_val. f_equal; lia.
Qed.

(* the byte move ZSTD_memmove( *op + k, *ip + k, 1) inside the array c (op at di, ip at si) *)
Ltac oc_mm sh p c si di k :=
  forward; forward;
  assert (force_val (sem_add_ptr_int tuchar Signed (offset_val si p) (Vint (Int.repr k))) =
          offset_val (si + k) p) by (apply add_off_tuchar; auto; lia);
  assert (force_val (sem_add_ptr_int tuchar Signed (offset_val di p) (Vint (Int.repr k))) =
          offset_val (di + k) p) by (apply add_off_tuchar; auto; lia);
  forward_call (mm_within sh p (Zlength c) (listcopy c si di (Z.to_nat k)) (si + k) (di + k) 1);
  [ unfold mm_ok; rewrite Zlength_listcopy by lia; split; [auto |]; repeat (split; [rep_lia |]);
    apply fa_bv, Forall_sublist_pt; [lia | rewrite Zlength_listcopy by lia; lia |];
    let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; lc_read
  | rewrite mm_post_within, (mm_result_step c si di k) by lia ].

(* ZSTD_overlapCopy8's stores: the forward copy of 8 bytes; ip ends oc8_off before op *)
Lemma lov8_exact (c: list val) (di off: Z) :
  1 <= off -> 0 <= di - off -> di + 8 <= Zlength c ->
  lov8 c di (di - off) off = (listcopy c (di - off) di 8, di + 8, di + 8 - oc8_off off).
Proof.
  intros Ho Hd HN. unfold lov8.
  destruct (off <? 8) eqn:E.
  - apply Z.ltb_lt in E. rewrite !lfwd_LW.
    assert (Hx: 0 <= Zstd.proof.model.ExBlock.xdec32 off <= off /\ (Zstd.proof.model.ExBlock.xdec32 off - 4) mod off = 0 /\
                oc8_off off = off - Zstd.proof.model.ExBlock.xdec32 off + Zstd.proof.model.ExBlock.xdec64 off).
    { assert (off = 1 \/ off = 2 \/ off = 3 \/ off = 4 \/ off = 5 \/ off = 6 \/ off = 7) as F by lia.
      destruct F as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]; cbv; repeat split; congruence. }
    destruct Hx as [Hx1 [Hx2 Hx3]].
    change 8%nat with (Z.to_nat 8). change 4%nat with (Z.to_nat 4).
    rewrite (oc8_listcopy c (di - off) di (Zstd.proof.model.ExBlock.xdec32 off))
      by (try lia; replace (di - (di - off)) with off by lia; exact Hx2).
    rewrite Hx3. f_equal. lia.
  - apply Z.ltb_ge in E. rewrite lfwd_LW, oc8_off_ge8 by lia. f_equal. lia.
Qed.

Lemma body_ZSTD_overlapCopy8 :
  semax_body Vprog (G_BLK ++ COPY_exports) f_ZSTD_overlapCopy8 ZSTD_overlapCopy8_spec.
Proof.
  start_function. rename H2 into Hdef.
  (* the exact PROP is pure: lov8 is the forward copy (lov8_exact) *)
  pose proof (lov8_exact c di offset ltac:(lia) ltac:(lia) ltac:(lia)) as Hlov8.
  assert_PROP (field_compatible (tarray tuchar (Zlength c)) [] p) as Hfc by entailer!.
  destruct (fc_tuchar_bound _ _ Hfc) as [Hp Hcm].
  rewrite !arr_field_address by (auto; lia).
  simpl sizeof. rewrite !Z.mul_1_l.
  rewrite zg_dec. Intros.
  forward_if (PROP () LOCAL (temp _op pop; temp _ip pip; gvars gv)
    SEP (data_at Ers (tarray tuint 8) dec32table_val (gv _dec32table);
         data_at Ers (tarray tint 8) dec64table_val (gv _dec64table); zg_rest_dec gv;
         data_at Tsh (tptr tuchar) (offset_val di p) pop;
         data_at Tsh (tptr tuchar) (offset_val (di - oc8_off offset) p) pip;
         data_at sh (tarray tuchar (Zlength c)) (listcopy c (di - offset) di (Z.to_nat 8)) p)).
  - assert (Ptrofs.modulus = Int64.modulus) by reflexivity.
    rewrite !Int64.unsigned_repr in H2 by rep_lia.
    (* offset < 8: the offset cells before di are defined *)
    assert (Hdo: Forall is_byte_val (sublist (di - offset) di c))
      by (rewrite Z.min_l in Hdef by lia; replace (di - offset + offset) with di in Hdef by lia; exact Hdef).
    clear Hdef.
    assert (offset = 1 \/ offset = 2 \/ offset = 3 \/ offset = 4 \/ offset = 5 \/ offset = 6 \/ offset = 7)
      as Ho by lia.
    destruct Ho as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]].
    + forward.
      replace_SEP 5 (data_at sh (tarray tuchar (Zlength c)) (listcopy c (di - 1) di (Z.to_nat 0)) p).
      { entailer!. }
      oc_mm sh p c (di - 1) di 0.
      oc_mm sh p c (di - 1) di 1.
      oc_mm sh p c (di - 1) di 2.
      oc_mm sh p c (di - 1) di 3.
      forward. forward.
      match goal with |- context [@Znth val ?d 1 dec32table_val] =>
        change (@Znth val d 1 dec32table_val) with (Vint (Int.repr 1)) end.
      match goal with |- context [@Znth val ?d 1 dec64table_val] =>
        change (@Znth val d 1 dec64table_val) with (Vint (Int.repr 8)) end.
      forward. simp_ptr. forward. forward.
      change (Z.to_nat (3 + 1)) with (Z.to_nat 4).
      sep_apply (tuchar_split_N sh p (Zlength c) (listcopy c (di - 1) di (Z.to_nat 4)) (di + 4)); wc_side.
      Intros.
      forward_call (sh, p, sublist 0 (di + 4) (listcopy c (di - 1) di (Z.to_nat 4)), di - 1 + 1, sh, offset_val (di + 4) p,
                    sublist (di + 4) (Zlength (listcopy c (di - 1) di (Z.to_nat 4))) (listcopy c (di - 1) di (Z.to_nat 4)), 0).
      { unfold copy_pre; rewrite ?Zlength_listcopy by lia;
        rewrite !Zlength_sublist by (rewrite ?Zlength_listcopy; lia);
        split; [apply writable_readable; assumption |]; split; [assumption |];
        repeat (split; [lia |]); wc_bytes. }
      sep_apply (within_copy_sb_N sh p (Zlength c) (listcopy c (di - 1) di (Z.to_nat 4)) (di - 1 + 1) (di + 4) 4); wc_side.
      rewrite (oc8_listcopy c (di - 1) di 1)
        by (try lia; match goal with |- _ mod ?y = 0 => replace y with 1 by lia; reflexivity end).
      forward. forward. rewrite cp_sub_pi by (auto; rep_lia).
      change (oc8_off 1) with 8.
      replace (di - 1 + 1 - 8) with (di - 8) by lia.
      entailer!.
    + forward.
      replace_SEP 5 (data_at sh (tarray tuchar (Zlength c)) (listcopy c (di - 2) di (Z.to_nat 0)) p).
      { entailer!. }
      oc_mm sh p c (di - 2) di 0.
      oc_mm sh p c (di - 2) di 1.
      oc_mm sh p c (di - 2) di 2.
      oc_mm sh p c (di - 2) di 3.
      forward. forward.
      match goal with |- context [@Znth val ?d 2 dec32table_val] =>
        change (@Znth val d 2 dec32table_val) with (Vint (Int.repr 2)) end.
      match goal with |- context [@Znth val ?d 2 dec64table_val] =>
        change (@Znth val d 2 dec64table_val) with (Vint (Int.repr 8)) end.
      forward. simp_ptr. forward. forward.
      change (Z.to_nat (3 + 1)) with (Z.to_nat 4).
      sep_apply (tuchar_split_N sh p (Zlength c) (listcopy c (di - 2) di (Z.to_nat 4)) (di + 4)); wc_side.
      Intros.
      forward_call (sh, p, sublist 0 (di + 4) (listcopy c (di - 2) di (Z.to_nat 4)), di - 2 + 2, sh, offset_val (di + 4) p,
                    sublist (di + 4) (Zlength (listcopy c (di - 2) di (Z.to_nat 4))) (listcopy c (di - 2) di (Z.to_nat 4)), 0).
      { unfold copy_pre; rewrite ?Zlength_listcopy by lia;
        rewrite !Zlength_sublist by (rewrite ?Zlength_listcopy; lia);
        split; [apply writable_readable; assumption |]; split; [assumption |];
        repeat (split; [lia |]); wc_bytes. }
      sep_apply (within_copy_sb_N sh p (Zlength c) (listcopy c (di - 2) di (Z.to_nat 4)) (di - 2 + 2) (di + 4) 4); wc_side.
      rewrite (oc8_listcopy c (di - 2) di 2)
        by (try lia; match goal with |- _ mod ?y = 0 => replace y with 2 by lia; reflexivity end).
      forward. forward. rewrite cp_sub_pi by (auto; rep_lia).
      change (oc8_off 2) with 8.
      replace (di - 2 + 2 - 8) with (di - 8) by lia.
      entailer!.
    + forward.
      replace_SEP 5 (data_at sh (tarray tuchar (Zlength c)) (listcopy c (di - 3) di (Z.to_nat 0)) p).
      { entailer!. }
      oc_mm sh p c (di - 3) di 0.
      oc_mm sh p c (di - 3) di 1.
      oc_mm sh p c (di - 3) di 2.
      oc_mm sh p c (di - 3) di 3.
      forward. forward.
      match goal with |- context [@Znth val ?d 3 dec32table_val] =>
        change (@Znth val d 3 dec32table_val) with (Vint (Int.repr 1)) end.
      match goal with |- context [@Znth val ?d 3 dec64table_val] =>
        change (@Znth val d 3 dec64table_val) with (Vint (Int.repr 7)) end.
      forward. simp_ptr. forward. forward.
      change (Z.to_nat (3 + 1)) with (Z.to_nat 4).
      sep_apply (tuchar_split_N sh p (Zlength c) (listcopy c (di - 3) di (Z.to_nat 4)) (di + 4)); wc_side.
      Intros.
      forward_call (sh, p, sublist 0 (di + 4) (listcopy c (di - 3) di (Z.to_nat 4)), di - 3 + 1, sh, offset_val (di + 4) p,
                    sublist (di + 4) (Zlength (listcopy c (di - 3) di (Z.to_nat 4))) (listcopy c (di - 3) di (Z.to_nat 4)), 0).
      { unfold copy_pre; rewrite ?Zlength_listcopy by lia;
        rewrite !Zlength_sublist by (rewrite ?Zlength_listcopy; lia);
        split; [apply writable_readable; assumption |]; split; [assumption |];
        repeat (split; [lia |]); wc_bytes. }
      sep_apply (within_copy_sb_N sh p (Zlength c) (listcopy c (di - 3) di (Z.to_nat 4)) (di - 3 + 1) (di + 4) 4); wc_side.
      rewrite (oc8_listcopy c (di - 3) di 1)
        by (try lia; match goal with |- _ mod ?y = 0 => replace y with 3 by lia; reflexivity end).
      forward. forward. rewrite cp_sub_pi by (auto; rep_lia).
      change (oc8_off 3) with 9.
      replace (di - 3 + 1 - 7) with (di - 9) by lia.
      entailer!.
    + forward.
      replace_SEP 5 (data_at sh (tarray tuchar (Zlength c)) (listcopy c (di - 4) di (Z.to_nat 0)) p).
      { entailer!. }
      oc_mm sh p c (di - 4) di 0.
      oc_mm sh p c (di - 4) di 1.
      oc_mm sh p c (di - 4) di 2.
      oc_mm sh p c (di - 4) di 3.
      forward. forward.
      match goal with |- context [@Znth val ?d 4 dec32table_val] =>
        change (@Znth val d 4 dec32table_val) with (Vint (Int.repr 4)) end.
      match goal with |- context [@Znth val ?d 4 dec64table_val] =>
        change (@Znth val d 4 dec64table_val) with (Vint (Int.repr 8)) end.
      forward. simp_ptr. forward. forward.
      change (Z.to_nat (3 + 1)) with (Z.to_nat 4).
      sep_apply (tuchar_split_N sh p (Zlength c) (listcopy c (di - 4) di (Z.to_nat 4)) (di + 4)); wc_side.
      Intros.
      forward_call (sh, p, sublist 0 (di + 4) (listcopy c (di - 4) di (Z.to_nat 4)), di - 4 + 4, sh, offset_val (di + 4) p,
                    sublist (di + 4) (Zlength (listcopy c (di - 4) di (Z.to_nat 4))) (listcopy c (di - 4) di (Z.to_nat 4)), 0).
      { unfold copy_pre; rewrite ?Zlength_listcopy by lia;
        rewrite !Zlength_sublist by (rewrite ?Zlength_listcopy; lia);
        split; [apply writable_readable; assumption |]; split; [assumption |];
        repeat (split; [lia |]); wc_bytes. }
      sep_apply (within_copy_sb_N sh p (Zlength c) (listcopy c (di - 4) di (Z.to_nat 4)) (di - 4 + 4) (di + 4) 4); wc_side.
      rewrite (oc8_listcopy c (di - 4) di 4)
        by (try lia; match goal with |- _ mod ?y = 0 => replace y with 4 by lia; reflexivity end).
      forward. forward. rewrite cp_sub_pi by (auto; rep_lia).
      change (oc8_off 4) with 8.
      replace (di - 4 + 4 - 8) with (di - 8) by lia.
      entailer!.
    + forward.
      replace_SEP 5 (data_at sh (tarray tuchar (Zlength c)) (listcopy c (di - 5) di (Z.to_nat 0)) p).
      { entailer!. }
      oc_mm sh p c (di - 5) di 0.
      oc_mm sh p c (di - 5) di 1.
      oc_mm sh p c (di - 5) di 2.
      oc_mm sh p c (di - 5) di 3.
      forward. forward.
      match goal with |- context [@Znth val ?d 5 dec32table_val] =>
        change (@Znth val d 5 dec32table_val) with (Vint (Int.repr 4)) end.
      match goal with |- context [@Znth val ?d 5 dec64table_val] =>
        change (@Znth val d 5 dec64table_val) with (Vint (Int.repr 9)) end.
      forward. simp_ptr. forward. forward.
      change (Z.to_nat (3 + 1)) with (Z.to_nat 4).
      sep_apply (tuchar_split_N sh p (Zlength c) (listcopy c (di - 5) di (Z.to_nat 4)) (di + 4)); wc_side.
      Intros.
      forward_call (sh, p, sublist 0 (di + 4) (listcopy c (di - 5) di (Z.to_nat 4)), di - 5 + 4, sh, offset_val (di + 4) p,
                    sublist (di + 4) (Zlength (listcopy c (di - 5) di (Z.to_nat 4))) (listcopy c (di - 5) di (Z.to_nat 4)), 0).
      { unfold copy_pre; rewrite ?Zlength_listcopy by lia;
        rewrite !Zlength_sublist by (rewrite ?Zlength_listcopy; lia);
        split; [apply writable_readable; assumption |]; split; [assumption |];
        repeat (split; [lia |]); wc_bytes. }
      sep_apply (within_copy_sb_N sh p (Zlength c) (listcopy c (di - 5) di (Z.to_nat 4)) (di - 5 + 4) (di + 4) 4); wc_side.
      rewrite (oc8_listcopy c (di - 5) di 4)
        by (try lia; match goal with |- _ mod ?y = 0 => replace y with 5 by lia; reflexivity end).
      forward. forward. rewrite cp_sub_pi by (auto; rep_lia).
      change (oc8_off 5) with 10.
      replace (di - 5 + 4 - 9) with (di - 10) by lia.
      entailer!.
    + forward.
      replace_SEP 5 (data_at sh (tarray tuchar (Zlength c)) (listcopy c (di - 6) di (Z.to_nat 0)) p).
      { entailer!. }
      oc_mm sh p c (di - 6) di 0.
      oc_mm sh p c (di - 6) di 1.
      oc_mm sh p c (di - 6) di 2.
      oc_mm sh p c (di - 6) di 3.
      forward. forward.
      match goal with |- context [@Znth val ?d 6 dec32table_val] =>
        change (@Znth val d 6 dec32table_val) with (Vint (Int.repr 4)) end.
      match goal with |- context [@Znth val ?d 6 dec64table_val] =>
        change (@Znth val d 6 dec64table_val) with (Vint (Int.repr 10)) end.
      forward. simp_ptr. forward. forward.
      change (Z.to_nat (3 + 1)) with (Z.to_nat 4).
      sep_apply (tuchar_split_N sh p (Zlength c) (listcopy c (di - 6) di (Z.to_nat 4)) (di + 4)); wc_side.
      Intros.
      forward_call (sh, p, sublist 0 (di + 4) (listcopy c (di - 6) di (Z.to_nat 4)), di - 6 + 4, sh, offset_val (di + 4) p,
                    sublist (di + 4) (Zlength (listcopy c (di - 6) di (Z.to_nat 4))) (listcopy c (di - 6) di (Z.to_nat 4)), 0).
      { unfold copy_pre; rewrite ?Zlength_listcopy by lia;
        rewrite !Zlength_sublist by (rewrite ?Zlength_listcopy; lia);
        split; [apply writable_readable; assumption |]; split; [assumption |];
        repeat (split; [lia |]); wc_bytes. }
      sep_apply (within_copy_sb_N sh p (Zlength c) (listcopy c (di - 6) di (Z.to_nat 4)) (di - 6 + 4) (di + 4) 4); wc_side.
      rewrite (oc8_listcopy c (di - 6) di 4)
        by (try lia; match goal with |- _ mod ?y = 0 => replace y with 6 by lia; reflexivity end).
      forward. forward. rewrite cp_sub_pi by (auto; rep_lia).
      change (oc8_off 6) with 12.
      replace (di - 6 + 4 - 10) with (di - 12) by lia.
      entailer!.
    + forward.
      replace_SEP 5 (data_at sh (tarray tuchar (Zlength c)) (listcopy c (di - 7) di (Z.to_nat 0)) p).
      { entailer!. }
      oc_mm sh p c (di - 7) di 0.
      oc_mm sh p c (di - 7) di 1.
      oc_mm sh p c (di - 7) di 2.
      oc_mm sh p c (di - 7) di 3.
      forward. forward.
      match goal with |- context [@Znth val ?d 7 dec32table_val] =>
        change (@Znth val d 7 dec32table_val) with (Vint (Int.repr 4)) end.
      match goal with |- context [@Znth val ?d 7 dec64table_val] =>
        change (@Znth val d 7 dec64table_val) with (Vint (Int.repr 11)) end.
      forward. simp_ptr. forward. forward.
      change (Z.to_nat (3 + 1)) with (Z.to_nat 4).
      sep_apply (tuchar_split_N sh p (Zlength c) (listcopy c (di - 7) di (Z.to_nat 4)) (di + 4)); wc_side.
      Intros.
      forward_call (sh, p, sublist 0 (di + 4) (listcopy c (di - 7) di (Z.to_nat 4)), di - 7 + 4, sh, offset_val (di + 4) p,
                    sublist (di + 4) (Zlength (listcopy c (di - 7) di (Z.to_nat 4))) (listcopy c (di - 7) di (Z.to_nat 4)), 0).
      { unfold copy_pre; rewrite ?Zlength_listcopy by lia;
        rewrite !Zlength_sublist by (rewrite ?Zlength_listcopy; lia);
        split; [apply writable_readable; assumption |]; split; [assumption |];
        repeat (split; [lia |]); wc_bytes. }
      sep_apply (within_copy_sb_N sh p (Zlength c) (listcopy c (di - 7) di (Z.to_nat 4)) (di - 7 + 4) (di + 4) 4); wc_side.
      rewrite (oc8_listcopy c (di - 7) di 4)
        by (try lia; match goal with |- _ mod ?y = 0 => replace y with 7 by lia; reflexivity end).
      forward. forward. rewrite cp_sub_pi by (auto; rep_lia).
      change (oc8_off 7) with 14.
      replace (di - 7 + 4 - 11) with (di - 14) by lia.
      entailer!.
  - assert (Ptrofs.modulus = Int64.modulus) by reflexivity.
    rewrite !Int64.unsigned_repr in H2 by rep_lia.
    (* offset >= 8: the 8 cells ZSTD_copy8 reads are defined *)
    assert (Hdo: Forall is_byte_val (sublist (di - offset) (di - offset + 8) c))
      by (rewrite Z.min_r in Hdef by lia; exact Hdef).
    clear Hdef.
    forward. forward.
    replace_SEP 5 (data_at sh (tarray tuchar (Zlength c)) (listcopy c (di - offset) di (Z.to_nat 0)) p).
    { entailer!. }
    change (listcopy c (di - offset) di 0) with (listcopy c (di - offset) di (Z.to_nat 0)).
    wc_call 0 8.
    rewrite oc8_off_ge8 by lia. entailer!.
  - forward. forward. forward. forward. simp_ptr.
    rewrite zg_dec. rewrite !arr_field_address0 by (auto; pose proof (oc8_off_facts offset H); lia).
    simpl sizeof. rewrite !Z.mul_1_l.
    replace (di - oc8_off offset + 8) with (di + 8 - oc8_off offset) by lia.
    entailer!.
Qed.

Lemma lc_prefix_nth (c: list val) (si di k n x: Z) :
  0 <= di -> 0 <= k <= n -> di + n <= Zlength c -> 0 <= x < di + k ->
  Znth x (listcopy c si di (Z.to_nat k)) = Znth x (listcopy c si di (Z.to_nat n)).
Proof.
  intros. replace (Z.to_nat n) with (Z.to_nat k + Z.to_nat (n - k))%nat by lia.
  rewrite listcopy_add, Z2Nat.id by lia.
  assert (Zlength (listcopy c si di (Z.to_nat k)) = Zlength c) by (apply Zlength_listcopy; lia).
  symmetry. apply listcopy_outside; rewrite ?Z2Nat.id; lia.
Qed.

(* the end of ZSTD_safecopy: after the (optional) ZSTD_overlapCopy8 the copy goes on from (si', di') over
   c'; a wild copy of E0 bytes and then the byte loop from a; the result is the forward copy of n bytes from
   (si, di) on [di, di + n), and c elsewhere outside [di, max(di + n, dw + 32)) *)
Lemma sc_final (c c': list val) (si di n si' di' E0 a dw: Z) :
  Zlength c' = Zlength c -> 0 <= di -> di <= di' <= di + n -> di + n <= Zlength c ->
  0 <= si' -> (si' < di' \/ di' + 32 <= si') -> (si' < di' \/ si' + (di + n - di') + 32 <= Zlength c) ->
  (forall m, 0 <= m <= di + n - di' ->
     listcopy c' si' di' (Z.to_nat m) = listcopy c si di (Z.to_nat (di' - di + m))) ->
  0 <= a <= E0 -> E0 <= a + 31 -> a <= di + n - di' -> di' + E0 <= Zlength c ->
  di' + E0 <= Z.max (di + n) (dw + 32) ->
  let F := listcopy (listcopy c' si' di' (Z.to_nat E0)) (si' + a) (di' + a) (Z.to_nat (di + n - di' - a)) in
  Zlength F = Zlength c /\
  sublist di (di + n) F = sublist di (di + n) (listcopy c si di (Z.to_nat n)) /\
  (forall k, 0 <= k < Zlength c -> ~ (di <= k < Z.max (di + n) (dw + 32)) -> Znth k F = Znth k c).
Proof.
  intros HZ Hdi Hd HN Hsi Hdir Hsrc Htr Ha HE0 Han HEN HEw F.
  set (n' := di + n - di') in *.
  assert (Hn': n' = di + n - di') by reflexivity. clearbody n'.
  assert (Hc0: c' = listcopy c si di (Z.to_nat (di' - di))).
  { rewrite <- (Z.add_0_r (di' - di)). rewrite <- Htr by lia. reflexivity. }
  assert (Hcn: listcopy c' si' di' (Z.to_nat n') = listcopy c si di (Z.to_nat n)).
  { rewrite Htr by lia. f_equal. f_equal. subst n'. lia. }
  assert (HL0: Zlength (listcopy c' si' di' (Z.to_nat E0)) = Zlength c) by (rewrite Zlength_listcopy; lia).
  assert (HF: Zlength F = Zlength c) by (subst F; rewrite Zlength_listcopy; rewrite ?HL0; lia).
  (* P1, P2 *)
  assert (P: (forall j, 0 <= j < n' -> Znth (di' + j) F = Znth (di' + j) (listcopy c' si' di' (Z.to_nat n'))) /\
             (forall x, 0 <= x < Zlength c -> ~ (di' <= x < di' + Z.max E0 n') -> Znth x F = Znth x c')).
  { destruct Hdir as [Hsb | Hdbs].
    - assert (EF: F = listcopy c' si' di' (Z.to_nat (Z.max E0 (a + (n' - a))))).
      { subst F. apply lc_extend_sb; lia. }
      replace (a + (n' - a)) with n' in EF by lia.
      split.
      + intros j Hj. rewrite EF. symmetry. apply lc_prefix_nth; rewrite ?HZ; lia.
      + intros x Hx Hout. rewrite EF. apply listcopy_outside; rewrite ?Z2Nat.id, ?HZ; lia.
    - destruct Hsrc as [Hsrc | Hsrc]; [lia |].
      destruct (lc_extend_dbs c' si' di' E0 a (n' - a)) as [_ [P1 P2]]; try lia.
      fold F in P1, P2. replace (a + (n' - a)) with n' in P1, P2 by lia.
      split.
      + intros j Hj. rewrite P1 by lia. symmetry. apply listcopy_dbs; lia.
      + intros x Hx Hout. rewrite HZ in P2. apply P2; auto. }
  destruct P as [P1 P2].
  split; [exact HF | split].
  - apply Znth_eq_ext. { rewrite !Zlength_sublist; rewrite ?HF, ?Zlength_listcopy; lia. }
    intros i Hi. rewrite Zlength_sublist in Hi by (rewrite ?HF; lia).
    rewrite !Znth_sublist by lia.
    destruct (Z_lt_le_dec (i + di) di') as [L | L].
    + rewrite P2 by lia. rewrite Hc0. apply lc_prefix_nth; lia.
    + replace (i + di) with (di' + (i + di - di')) by lia.
      rewrite P1 by lia. rewrite Hcn. reflexivity.
  - intros k Hk Hout. rewrite P2 by lia. rewrite Hc0. apply listcopy_outside; rewrite ?Z2Nat.id; lia.
Qed.

(* the byte loop reads bytes *)
Lemma sc_read_byte (c': list val) (si' di' n' E0 a j: Z) :
  0 <= si' -> 0 <= di' -> (si' < di' \/ di' + 32 <= si') -> (si' < di' \/ si' + n' + 32 <= Zlength c') ->
  Forall is_byte_val (sublist si' (si' + n') c') -> si' + n' <= Zlength c' ->
  0 <= a <= E0 -> E0 <= a + 31 -> di' + E0 <= Zlength c' -> di' + n' <= Zlength c' -> 0 <= j -> a + j < n' ->
  is_byte_val (Znth (si' + a + j) (listcopy (listcopy c' si' di' (Z.to_nat E0)) (si' + a) (di' + a) (Z.to_nat j))).
Proof.
  intros Hsi Hdi Hdir Hsrc HB Hsn Ha HE HEN HnN Hj Haj.
  assert (Hc: forall y, si' <= y < si' + n' -> is_byte_val (Znth y c')).
  { intros y Hy. rewrite Forall_forall in HB. apply HB.
    replace (Znth y c') with (Znth (y - si') (sublist si' (si' + n') c')) by (rewrite Znth_sublist by lia; f_equal; lia).
    apply Znth_In. rewrite Zlength_sublist by lia. lia. }
  destruct Hdir as [Hsb | Hdbs].
  - rewrite lc_extend_sb by lia. apply (lc_bytes_sb c' si' di' _ n'); auto; lia.
  - destruct Hsrc as [? | Hsrc]; [lia |].
    assert (HL0: Zlength (listcopy c' si' di' (Z.to_nat E0)) = Zlength c') by (rewrite Zlength_listcopy; lia).
    rewrite listcopy_outside by (rewrite ?HL0, ?Z2Nat.id; lia).
    rewrite listcopy_outside by (rewrite ?Z2Nat.id; lia). apply Hc; lia.
Qed.

Lemma sc_read_byte0 (c': list val) (si' di' n' j: Z) :
  0 <= si' -> 0 <= di' -> (si' < di' \/ di' + 32 <= si') -> (si' < di' \/ si' + n' + 32 <= Zlength c') ->
  Forall is_byte_val (sublist si' (si' + n') c') -> si' + n' <= Zlength c' -> di' + n' <= Zlength c' ->
  0 <= j < n' -> is_byte_val (Znth (si' + j) (listcopy c' si' di' (Z.to_nat j))).
Proof.
  intros. pose proof (sc_read_byte c' si' di' n' 0 0 j) as X.
  rewrite !Z.add_0_r in X. apply X; auto; lia.
Qed.

Lemma listcopy_zero (c: list val) (s d: Z) : listcopy c s d (Z.to_nat 0) = c.
Proof. reflexivity. Qed.

Lemma cp_eval_sub (p: val) (a b: Z) : isptr p ->
  eval_binop Osub (tptr tuchar) (tptr tuchar) (offset_val a p) (offset_val b p) = Vlong (Int64.repr (a - b)).
Proof.
  intros Hp. rewrite <- (cp_sub_pp p a b Hp). destruct p; try contradiction. reflexivity.
Qed.

Lemma cp_ge0_val (p: val) (a b: Z) : isptr p -> Int64.min_signed <= a - b <= Int64.max_signed ->
  match both_long (fun n1 n2 : int64 => Some (bool2val (negb (Int64.lt n1 n2))))
      sem_cast_pointer (sem_cast_i2l Signed)
      (force_val (sem_sub_pp tuchar (offset_val a p) (offset_val b p))) (Vint (Int.repr 0)) with
  | Some v' => v' | None => Vundef end = Vint (if zle b a then Int.one else Int.zero).
Proof.
  intros Hp Hab. rewrite cp_sub_pp by auto. simpl. unfold Int64.lt.
  rewrite Int64.signed_repr by lia. rewrite ?Int.signed_repr by rep_lia.
  change (Int64.signed (Int64.repr 0)) with 0.
  destruct (zlt (a - b) 0), (zle b a); try lia; reflexivity.
Qed.

Lemma cp_test_order_TT (sh: share) (n: Z) (c0: list val) (p: val) (i j: Z) (P: mpred) :
  readable_share sh -> field_compatible (tarray tuchar n) [] p -> 0 <= i <= n -> 0 <= j <= n -> 0 < n ->
  (P |-- data_at sh (tarray tuchar n) c0 p * TT) -> P |-- denote_tc_test_order (offset_val i p) (offset_val j p).
Proof. intros. eapply derives_trans; [eassumption | apply cp_test_order; auto]. Qed.

(* ---------- helpers for ZSTD_safecopy (its byte loops are one-byte ZSTD_memmove) ---------- *)
Lemma mm1_upd (L: list val) (N s d: Z) :
  Zlength L = N -> 0 <= s < N -> 0 <= d < N ->
  mm_result L N s d 1 = upd_Znth d L (Znth s L).
Proof. intros. unfold mm_result. list_solve. Qed.

(* one cell of a byte array, held separately *)
Lemma tuchar_cell (sh: share) (p: val) (l: list val) (k: Z) (v: val) :
  field_compatible (tarray tuchar (Zlength l)) [] p -> 0 <= k < Zlength l ->
  data_at sh (tarray tuchar (Zlength l)) (upd_Znth k l v) p =
  data_at sh (tarray tuchar k) (sublist 0 k l) p *
  data_at sh (tarray tuchar 1) [v] (offset_val k p) *
  data_at sh (tarray tuchar (Zlength l - (k + 1))) (sublist (k + 1) (Zlength l) l) (offset_val (k + 1) p).
Proof.
  intros Hfc Hk.
  rewrite (split3_data_at_Tarray_tuchar sh (Zlength l) k (k + 1) (upd_Znth k l v) p) by list_solve.
  change (Tarray tuchar (Zlength l) noattr) with (tarray tuchar (Zlength l)).
  rewrite !arr_field_address0 by (auto; lia). simpl sizeof. rewrite !Z.mul_1_l.
  replace (k + 1 - k) with 1 by lia.
  replace (sublist 0 k (upd_Znth k l v)) with (sublist 0 k l) by list_solve.
  replace (sublist k (k + 1) (upd_Znth k l v)) with [v] by list_solve.
  replace (sublist (k + 1) (Zlength l) (upd_Znth k l v)) with (sublist (k + 1) (Zlength l) l) by list_solve.
  replace (Zlength l - (k + 1)) with (Zlength l - (k + 1)) by lia.
  reflexivity.
Qed.

Lemma tuchar_cell_split (sh: share) (p: val) (N: Z) (l: list val) (k: Z) :
  Zlength l = N -> field_compatible (tarray tuchar N) [] p -> 0 <= k < N ->
  data_at sh (tarray tuchar N) l p |--
  data_at sh (tarray tuchar k) (sublist 0 k l) p *
  data_at sh (tarray tuchar 1) [Znth k l] (offset_val k p) *
  data_at sh (tarray tuchar (Zlength l - (k + 1))) (sublist (k + 1) (Zlength l) l) (offset_val (k + 1) p).
Proof.
  intros <- Hfc Hk. rewrite <- tuchar_cell by auto.
  replace (upd_Znth k l (Znth k l)) with l by list_solve. apply derives_refl.
Qed.

Lemma tuchar_cell_join (sh: share) (p: val) (N: Z) (l: list val) (k: Z) (v: val) :
  Zlength l = N -> field_compatible (tarray tuchar N) [] p -> 0 <= k < N ->
  data_at sh (tarray tuchar k) (sublist 0 k l) p *
  data_at sh (tarray tuchar 1) [v] (offset_val k p) *
  data_at sh (tarray tuchar (Zlength l - (k + 1))) (sublist (k + 1) (Zlength l) l) (offset_val (k + 1) p) |--
  data_at sh (tarray tuchar N) (upd_Znth k l v) p.
Proof. intros <- Hfc Hk. rewrite <- tuchar_cell by auto. apply derives_refl. Qed.

(* sc_final with the write bound min (di + n + 32) (max (di + n) (dw + 32)), and a source after the
   destination at any distance beyond everything written *)
Lemma sc_final2 (c c': list val) (si di n si' di' E0 a dw: Z) :
  Zlength c' = Zlength c -> 0 <= di -> di <= di' <= di + n -> di + n <= Zlength c -> 0 <= si' ->
  (si' < di' \/ (di' + E0 <= si' /\ di' + (di + n - di') <= si' /\
                 si' + E0 <= Zlength c /\ si' + (di + n - di') <= Zlength c)) ->
  (forall m, 0 <= m <= di + n - di' ->
     listcopy c' si' di' (Z.to_nat m) = listcopy c si di (Z.to_nat (di' - di + m))) ->
  0 <= a <= E0 -> E0 <= a + 31 -> a <= di + n - di' -> di' + E0 <= Zlength c ->
  di' + E0 <= di + n + 32 -> di' + E0 <= Z.max (di + n) (dw + 32) ->
  let F := listcopy (listcopy c' si' di' (Z.to_nat E0)) (si' + a) (di' + a) (Z.to_nat (di + n - di' - a)) in
  Zlength F = Zlength c /\
  sublist di (di + n) F = sublist di (di + n) (listcopy c si di (Z.to_nat n)) /\
  (forall k, 0 <= k < Zlength c -> ~ (di <= k < Z.min (di + n + 32) (Z.max (di + n) (dw + 32))) ->
     Znth k F = Znth k c).
Proof.
  intros HZ Hdi Hd HN Hsi Hdir Htr Ha HE0 Han HEN HE32 HEw F.
  set (n' := di + n - di') in *.
  assert (Hn': n' = di + n - di') by reflexivity. clearbody n'.
  assert (Hc0: c' = listcopy c si di (Z.to_nat (di' - di))).
  { rewrite <- (Z.add_0_r (di' - di)). rewrite <- Htr by lia. reflexivity. }
  assert (Hcn: listcopy c' si' di' (Z.to_nat n') = listcopy c si di (Z.to_nat n)).
  { rewrite Htr by lia. f_equal. f_equal. subst n'. lia. }
  assert (HL0: Zlength (listcopy c' si' di' (Z.to_nat E0)) = Zlength c) by (rewrite Zlength_listcopy; lia).
  assert (HF: Zlength F = Zlength c) by (subst F; rewrite Zlength_listcopy; rewrite ?HL0; lia).
  assert (P: (forall j, 0 <= j < n' -> Znth (di' + j) F = Znth (di' + j) (listcopy c' si' di' (Z.to_nat n'))) /\
             (forall x, 0 <= x < Zlength c -> ~ (di' <= x < di' + Z.max E0 n') -> Znth x F = Znth x c')).
  { destruct Hdir as [Hsb | [Hd1 [Hd2 [Hd3 Hd4]]]].
    - assert (EF: F = listcopy c' si' di' (Z.to_nat (Z.max E0 (a + (n' - a))))).
      { subst F. apply lc_extend_sb; lia. }
      replace (a + (n' - a)) with n' in EF by lia.
      split.
      + intros j Hj. rewrite EF. symmetry. apply lc_prefix_nth; rewrite ?HZ; lia.
      + intros x Hx Hout. rewrite EF. apply listcopy_outside; rewrite ?Z2Nat.id, ?HZ; lia.
    - split.
      + intros j Hj. rewrite listcopy_dbs by lia. subst F.
        destruct (Z_lt_le_dec j a) as [L | L].
        * rewrite listcopy_outside by (rewrite ?HL0, ?Z2Nat.id; lia).
          apply listcopy_dbs; lia.
        * replace (di' + j) with (di' + a + (j - a)) by lia.
          rewrite listcopy_dbs by (rewrite ?HL0; lia).
          rewrite listcopy_outside by (rewrite ?Z2Nat.id; lia). f_equal. lia.
      + intros x Hx Hout. subst F.
        rewrite listcopy_outside by (rewrite ?HL0, ?Z2Nat.id; lia).
        apply listcopy_outside; rewrite ?Z2Nat.id; lia. }
  destruct P as [P1 P2].
  split; [exact HF | split].
  - apply Znth_eq_ext. { rewrite !Zlength_sublist; rewrite ?HF, ?Zlength_listcopy; lia. }
    intros i Hi. rewrite Zlength_sublist in Hi by (rewrite ?HF; lia).
    rewrite !Znth_sublist by lia.
    destruct (Z_lt_le_dec (i + di) di') as [L | L].
    + rewrite P2 by lia. rewrite Hc0. apply lc_prefix_nth; lia.
    + replace (i + di) with (di' + (i + di - di')) by lia.
      rewrite P1 by lia. rewrite Hcn. reflexivity.
  - intros k Hk Hout. rewrite P2 by lia. rewrite Hc0. apply listcopy_outside; rewrite ?Z2Nat.id; lia.
Qed.

Lemma tuchar_join_at (sh: share) (p: val) (N: Z) (a b: list val) (da db d: Z) :
  field_compatible (tarray tuchar N) [] p -> Zlength a = da -> da = d -> Zlength b = db -> da + db = N ->
  data_at sh (tarray tuchar da) a p * data_at sh (tarray tuchar db) b (offset_val d p) |--
  data_at sh (tarray tuchar N) (a ++ b) p.
Proof. intros Hfc <- <- <- HN. rewrite (tuchar_join sh p N a b Hfc HN). apply derives_refl. Qed.

(* the disjoint byte loop: after j bytes from cs[a..] to c1[d..] *)
Lemma dj_loop_step (c1 cs: list val) (d a j: Z) :
  0 <= d -> 0 <= a -> 0 <= j -> d + j < Zlength c1 -> a + j < Zlength cs ->
  upd_Znth (d + j) (sublist 0 d c1 ++ sublist a (a + j) cs ++ sublist (d + j) (Zlength c1) c1) (Znth (a + j) cs) =
  sublist 0 d c1 ++ sublist a (a + (j + 1)) cs ++ sublist (d + (j + 1)) (Zlength c1) c1.
Proof. intros. list_solve. Qed.

Lemma dj_loop_len (c1 cs: list val) (d a j: Z) :
  0 <= d -> 0 <= a -> 0 <= j -> d + j <= Zlength c1 -> a + j <= Zlength cs ->
  Zlength (sublist 0 d c1 ++ sublist a (a + j) cs ++ sublist (d + j) (Zlength c1) c1) = Zlength c1.
Proof. intros. list_solve. Qed.

Lemma dj_loop_0 (c1 cs: list val) (d a: Z) :
  0 <= d <= Zlength c1 -> 0 <= a <= Zlength cs ->
  sublist 0 d c1 ++ sublist a (a + 0) cs ++ sublist (d + 0) (Zlength c1) c1 = c1.
Proof. intros. list_solve. Qed.

Lemma sc_dj_final (c c1 cs: list val) (di n a B: Z) :
  Zlength c1 = Zlength c -> 0 <= di -> 0 <= a <= n -> di + n <= Zlength c -> n <= Zlength cs ->
  sublist di (di + a) c1 = sublist 0 a cs ->
  (forall k, 0 <= k < Zlength c -> ~ (di <= k < B) -> Znth k c1 = Znth k c) -> di + n <= B ->
  let F := sublist 0 (di + a) c1 ++ sublist a (a + (n - a)) cs ++ sublist (di + a + (n - a)) (Zlength c1) c1 in
  Zlength F = Zlength c /\ sublist di (di + n) F = sublist 0 n cs /\
  (forall k, 0 <= k < Zlength c -> ~ (di <= k < B) -> Znth k F = Znth k c).
Proof.
  intros HL Hdi Ha Hn Hcs Hpre Hfr HB F. subst F.
  replace (a + (n - a)) with n by lia. replace (di + a + (n - a)) with (di + n) by lia.
  split; [list_solve |]. split.
  - replace (sublist 0 n cs) with (sublist 0 a cs ++ sublist a n cs) by (rewrite sublist_rejoin; auto; lia).
    rewrite <- Hpre. list_solve.
  - intros k Hk Hout. rewrite <- Hfr by lia.
    destruct (Z_lt_le_dec k di); list_solve.
Qed.

(* bytes in, bytes out: every cell of a forward copy / of sublists of byte arrays is a byte *)
Lemma bc_app (a b: list val) : byte_cells a -> byte_cells b -> byte_cells (a ++ b).
Proof. unfold byte_cells. intros. apply Forall_app; auto. Qed.

Lemma bc_sublist (l: list val) (i j: Z) : byte_cells l -> byte_cells (sublist i j l).
Proof. unfold byte_cells. apply Forall_sublist. Qed.

Lemma bc_listcopy (c: list val) (s d: Z) (k: nat) :
  byte_cells c -> 0 <= s -> s + Z.of_nat k <= Zlength c -> 0 <= d -> d + Z.of_nat k <= Zlength c ->
  byte_cells (listcopy c s d k).
Proof.
  intros Hb Hs Hsk Hd Hdk. induction k as [|k IH]; [exact Hb |].
  rewrite listcopy_snoc.
  assert (HL: Zlength (listcopy c s d k) = Zlength c) by (apply listcopy_Zlength; lia).
  assert (IH': byte_cells (listcopy c s d k)) by (apply IH; lia).
  unfold byte_cells in *. apply Forall_upd_Znth; auto.
  apply (proj1 (Forall_Znth _ _) IH'). lia.
Qed.

Lemma bc_listcopy_Z (c: list val) (s d E: Z) :
  byte_cells c -> 0 <= s -> 0 <= d -> 0 <= E -> s + E <= Zlength c -> d + E <= Zlength c ->
  byte_cells (listcopy c s d (Z.to_nat E)).
Proof. intros. apply bc_listcopy; [assumption | ..]; rewrite ?Z2Nat.id; lia. Qed.

Lemma bc_listcopy2 (c: list val) (s d E a m: Z) :
  byte_cells c -> 0 <= s -> 0 <= d -> 0 <= E -> 0 <= a -> 0 <= m -> s + E <= Zlength c -> d + E <= Zlength c ->
  s + a + m <= Zlength c -> d + a + m <= Zlength c ->
  byte_cells (listcopy (listcopy c s d (Z.to_nat E)) (s + a) (d + a) (Z.to_nat m)).
Proof.
  intros. assert (Zlength (listcopy c s d (Z.to_nat E)) = Zlength c) by (apply Zlength_listcopy; lia).
  apply bc_listcopy_Z; try lia. apply bc_listcopy_Z; auto; lia.
Qed.

Ltac bc := repeat first [ assumption | apply bc_app | apply bc_sublist ].

(* cell by cell (ZSTD_safecopy's last postcondition): each cell of c' is the cell of c at the same place, or a
   defined byte *)
Definition kept_or_byte (c c': list val) : Prop :=
  forall q, 0 <= q < Zlength c -> Znth q c' = Znth q c \/ is_byte_val (Znth q c').

Lemma kob_unfold (c c': list val) : kept_or_byte c c' ->
  forall q, 0 <= q < Zlength c -> Znth q c' = Znth q c \/ is_byte_val (Znth q c').
Proof. exact (fun H => H). Qed.

Lemma kob_refl (c: list val) : kept_or_byte c c.
Proof. intros q _. left. reflexivity. Qed.

Lemma kob_trans (c c1 c2: list val) :
  Zlength c1 = Zlength c -> kept_or_byte c c1 -> kept_or_byte c1 c2 -> kept_or_byte c c2.
Proof.
  intros HL H1 H2 q Hq. destruct (H2 q ltac:(lia)) as [E | B]; [| right; exact B].
  rewrite E. destruct (H1 q Hq) as [E' | B']; [left; exact E' | right; exact B'].
Qed.

(* a forward copy whose every read is a defined byte writes defined bytes *)
Lemma kob_listcopy (c: list val) (si di k: Z) :
  0 <= di -> 0 <= k -> di + k <= Zlength c ->
  (forall j, 0 <= j < k -> is_byte_val (Znth (si + j) (listcopy c si di (Z.to_nat j)))) ->
  kept_or_byte c (listcopy c si di (Z.to_nat k)).
Proof.
  intros Hdi Hk HN Hr. rewrite <- (Z2Nat.id k) in HN, Hr by lia.
  set (m := Z.to_nat k) in *. clearbody m. clear Hk.
  induction m as [|m IH].
  - apply kob_refl.
  - rewrite Nat2Z.inj_succ in HN, Hr. rewrite listcopy_snoc.
    assert (HL: Zlength (listcopy c si di m) = Zlength c) by (apply listcopy_Zlength; lia).
    intros q Hq. destruct (Z.eq_dec q (di + Z.of_nat m)) as [-> | Hne].
    + right. rewrite upd_Znth_same by lia.
      specialize (Hr (Z.of_nat m) ltac:(lia)). rewrite Nat2Z.id in Hr. exact Hr.
    + rewrite upd_Znth_diff by lia.
      exact (IH ltac:(lia) (fun j Hj => Hr j ltac:(lia)) q Hq).
Qed.

(* a copy of up to n + 32 bytes under copy_src_def: every read is defined *)
Lemma csd_kob (c: list val) (si di n E: Z) :
  copy_src_def c si di n -> 0 <= si -> 0 <= di -> 0 <= E <= n + 32 -> di + E <= Zlength c ->
  (si < di \/ si + n + 32 <= Zlength c) -> kept_or_byte c (listcopy c si di (Z.to_nat E)).
Proof.
  intros HB Hsi Hdi HE HN Hl. apply kob_listcopy; try lia.
  intros j Hj. apply (csd_read c si di n); auto; lia.
Qed.

(* the cells [d, e) replaced by the defined bytes [a, b) of another array *)
Lemma kob_splice (c cs: list val) (d a b e: Z) :
  0 <= d -> 0 <= a <= b -> e = d + (b - a) -> e <= Zlength c -> b <= Zlength cs ->
  Forall is_byte_val (sublist a b cs) ->
  kept_or_byte c (sublist 0 d c ++ sublist a b cs ++ sublist e (Zlength c) c).
Proof.
  intros Hd Hab He HeN Hb HB q Hq. subst e.
  destruct (Z_lt_le_dec q d) as [L1 | L1]; [left; list_solve |].
  destruct (Z_lt_le_dec q (d + (b - a))) as [L2 | L2].
  - right.
    replace (Znth q (sublist 0 d c ++ sublist a b cs ++ sublist (d + (b - a)) (Zlength c) c))
      with (Znth (a + (q - d)) cs) by list_solve.
    apply (Forall_sublist_pt_inv cs a b); auto; lia.
  - left. list_solve.
Qed.

(* the disjoint wild copy of n bytes into c from di: the first E (<= n + 31) cells are source bytes, the rest of
   the 32-cell slack is unchanged *)
Lemma kob_dj_wc (c cs: list val) (di n E: Z) :
  0 <= di -> 0 <= n <= E -> E <= n + 31 -> n + 32 <= Zlength cs -> di + n + 32 <= Zlength c ->
  Forall is_byte_val (sublist 0 (n + 32) cs) ->
  kept_or_byte c (sublist 0 di c ++ (sublist 0 n cs ++
     sublist n (n + 32) (sublist 0 E cs ++ sublist E (Zlength (sublist di (Zlength c) c)) (sublist di (Zlength c) c)) ++
     sublist (n + 32) (Zlength (sublist di (Zlength c) c)) (sublist di (Zlength c) c))).
Proof.
  intros Hdi Hn HE Hcs Hc HB.
  replace (sublist 0 n cs ++
     sublist n (n + 32) (sublist 0 E cs ++ sublist E (Zlength (sublist di (Zlength c) c)) (sublist di (Zlength c) c)) ++
     sublist (n + 32) (Zlength (sublist di (Zlength c) c)) (sublist di (Zlength c) c))
    with (sublist 0 E cs ++ sublist E (Zlength (sublist di (Zlength c) c)) (sublist di (Zlength c) c))
    by list_solve.
  intros q Hq.
  destruct (Z_lt_le_dec q di) as [L1 | L1]; [left; list_solve |].
  destruct (Z_lt_le_dec q (di + E)) as [L2 | L2].
  - right.
    replace (Znth q (sublist 0 di c ++
               (sublist 0 E cs ++ sublist E (Zlength (sublist di (Zlength c) c)) (sublist di (Zlength c) c))))
      with (Znth (q - di) cs) by list_solve.
    apply (Forall_sublist_pt_inv cs 0 (n + 32)); auto; lia.
  - left. list_solve.
Qed.

(* ZSTD_safecopy with overlap: what ZSTD_overlapCopy8 reads (min offset 8 cells from si) is defined *)
Lemma csd_oc8 (c: list val) (si di n: Z) :
  copy_src_def c si di n -> 0 <= si < di -> 8 <= n -> di <= Zlength c ->
  Forall is_byte_val (sublist si (si + Z.min (di - si) 8) c).
Proof.
  unfold copy_src_def, WILDCOPY_OVERLENGTH. intros HB Hs Hn HN.
  rewrite (proj2 (Z.ltb_lt si di)) in HB by lia.
  apply (Forall_sub_range _ c si (Z.min di (si + n + 32))); auto; lia.
Qed.

(* after ZSTD_overlapCopy8 the copy goes on from di + 8 - oc8_off (di - si) to di + 8 over the forward copy of 8
   bytes: the cells it reads are defined (original source cells, or copies of them) *)
Lemma oc8_csd (c: list val) (si di n: Z) :
  copy_src_def c si di n -> 0 <= si < di -> 8 <= n -> di + 8 <= Zlength c ->
  copy_src_def (listcopy c si di (Z.to_nat 8)) (di + 8 - oc8_off (di - si)) (di + 8) (n - 8).
Proof.
  intros HB Hs Hn HN.
  destruct (oc8_off_facts (di - si) ltac:(lia)) as [HK1 [HK2 _]].
  assert (HL: Zlength (listcopy c si di (Z.to_nat 8)) = Zlength c) by (apply Zlength_listcopy; lia).
  unfold copy_src_def at 1. unfold WILDCOPY_OVERLENGTH.
  rewrite (proj2 (Z.ltb_lt (di + 8 - oc8_off (di - si)) (di + 8))) by lia.
  apply Forall_sublist_pt; [lia | rewrite HL; lia |]. intros x Hx.
  apply (csd_read c si di n); auto; lia.
Qed.

(* the leftover byte loop of ZSTD_safecopy reads defined cells: after a wild copy of E0 bytes and j more bytes
   from a, the cell si + a + j (a + j < n) *)
Lemma sc_read_def (c: list val) (si di n E0 a j: Z) :
  copy_src_def c si di n -> 0 <= si -> 0 <= di -> 0 <= a <= E0 -> 0 <= j -> a + j < n ->
  di + E0 <= Zlength c -> di + n <= Zlength c ->
  (si < di \/ (di + E0 <= si /\ di + n <= si /\ si + n + 32 <= Zlength c)) ->
  is_byte_val (Znth (si + a + j) (listcopy (listcopy c si di (Z.to_nat E0)) (si + a) (di + a) (Z.to_nat j))).
Proof.
  intros HB Hsi Hdi Ha Hj Haj HE HN Hdir.
  assert (HL0: Zlength (listcopy c si di (Z.to_nat E0)) = Zlength c) by (apply Zlength_listcopy; lia).
  destruct Hdir as [Hsb | (Hd1 & Hd2 & Hd3)].
  - rewrite lc_extend_sb by lia. apply (csd_read c si di n); auto; lia.
  - rewrite listcopy_outside by (rewrite ?HL0, ?Z2Nat.id; lia).
    apply (csd_read c si di n); auto; lia.
Qed.

Lemma body_ZSTD_safecopy :
  semax_body Vprog (G_BLK ++ COPY_exports) f_ZSTD_safecopy ZSTD_safecopy_spec.
Proof.
  start_function.
  destruct H4 as [H4 Hwrap]. change (2 ^ 63) with 9223372036854775808 in Hwrap.
  assert_PROP (field_compatible (tarray tuchar (Zlength c)) [] p) as Hfc by entailer!.
  destruct (fc_tuchar_bound _ _ Hfc) as [Hp Hcm].
  unfold WILDCOPY_OVERLENGTH, WILDCOPY_VECLEN in *.
  assert (Hn64: 0 <= n <= Int64.max_unsigned)
      by (assert (Ptrofs.modulus = Int64.modulus) by reflexivity; unfold Int64.max_unsigned; lia).
  destruct within.
  - (* within: the source in the output array *)
    destruct H7 as [Hsi [Hov1 Hov0]]; [reflexivity |]. clear H8.
    assert (Hcsd := H9 eq_refl). clear H9 H10.
    assert (Hsn: si + n <= Zlength c)
      by (destruct H0 as [-> | ->]; [destruct (Hov0 eq_refl); lia | specialize (Hov1 eq_refl); lia]).
    assert (Hcsl: si < di \/ si + n + 32 <= Zlength c)
      by (destruct H0 as [-> | ->]; [destruct (Hov0 eq_refl); lia | specialize (Hov1 eq_refl); lia]).
    rewrite !arr_field_address by (auto; lia). simpl sizeof. rewrite !Z.mul_1_l.
    forward. forward. forward. forward. simp_ptr.
    forward_if (PROP (8 <= n)
      LOCAL (temp _oend (offset_val (di + n) p); lvar _ip (tptr tuchar) v_ip; lvar _op (tptr tuchar) v_op;
             gvars gv; temp _oend_w (offset_val dw p); temp _length (Vlong (Int64.repr n));
             temp _ovtype (Vint (Int.repr ov)))
      SEP (data_at Tsh (tptr tuchar) (offset_val si p) v_ip;
           data_at Tsh (tptr tuchar) (offset_val di p) v_op; zstd_globals gv;
           data_at sh (tarray tuchar (Zlength c)) c p)).
    + (* short copies: the byte loop *)
      rewrite Int64.unsigned_repr in * by rep_lia.
      change (Int64.unsigned (Int64.repr 8)) with 8 in *.
      replace_SEP 3 (data_at sh (tarray tuchar (Zlength c)) (listcopy c si di (Z.to_nat 0)) p).
      { entailer!. }
      replace (offset_val si p) with (offset_val (si + 0) p) by (f_equal; lia).
      replace (offset_val di p) with (offset_val (di + 0) p) by (f_equal; lia).
      forward_loop (EX j: Z, PROP (0 <= j <= n)
        LOCAL (temp _oend (offset_val (di + n) p); lvar _ip (tptr tuchar) v_ip; lvar _op (tptr tuchar) v_op; gvars gv)
        SEP (data_at Tsh (tptr tuchar) (offset_val (si + j) p) v_ip;
             data_at Tsh (tptr tuchar) (offset_val (di + j) p) v_op; zstd_globals gv;
             data_at sh (tarray tuchar (Zlength c)) (listcopy c si di (Z.to_nat j)) p))%assert
      break: (PROP () LOCAL (lvar _ip (tptr tuchar) v_ip; lvar _op (tptr tuchar) v_op; gvars gv)
        SEP (data_at Tsh (tptr tuchar) (offset_val (si + n) p) v_ip;
             data_at Tsh (tptr tuchar) (offset_val (di + n) p) v_op; zstd_globals gv;
             data_at sh (tarray tuchar (Zlength c)) (listcopy c si di (Z.to_nat n)) p))%assert.
      { Exists 0. entailer!; apply derives_refl. }
      { Intros j. forward. forward_if.
        - apply (cp_test_order_TT sh (Zlength c) (listcopy c si di (Z.to_nat j)));
            [apply writable_readable; auto | auto | lia | lia | lia | cancel].
        - cmp_simpl. forward. forward.
          forward_call (mm_within sh p (Zlength c) (listcopy c si di (Z.to_nat j)) (si + j) (di + j) 1).
          { simpl. rewrite Zlength_listcopy by lia. split; [exact SH |]. repeat (split; [rep_lia |]).
            apply fa_bv, Forall_sublist_pt; [lia | rewrite Zlength_listcopy by lia; lia |].
            intros x Hx. apply (csd_read c si di n); auto; lia. }
          simpl mm_post. rewrite mm1_upd by (rewrite ?Zlength_listcopy; lia).
          rewrite (byte_step_nocast c si di j (di + j) (si + j) _ _ (Z.to_nat (j + 1))) by (try reflexivity; lia).
          forward. forward. forward. forward. simp_ptr.
          Exists (j + 1). replace (si + (j + 1)) with (si + j + 1) by lia.
          replace (di + (j + 1)) with (di + j + 1) by lia. entailer!.
        - cmp_simpl. forward. assert (j = n) by lia. subst j. entailer!. }
      assert (Hkq := kob_unfold _ _ (csd_kob c si di n n Hcsd ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hcsl)).
      pose proof (lsc_w_short c si di dw n (ov =? OV_SRC_BEFORE_DST) ltac:(lia)) as Hex.
      forward. Exists (listcopy c si di (Z.to_nat n)). entailer!.
      split; [intros k Hk Hout; apply listcopy_outside; rewrite ?Z2Nat.id; lia |].
      intros; apply bc_listcopy_Z; auto; lia.
    + rewrite Int64.unsigned_repr in * by rep_lia.
      change (Int64.unsigned (Int64.repr 8)) with 8 in *.
      forward. entailer!.
    + Intros.
      forward_if (EX c': list val, EX si': Z, EX di': Z,
        PROP (Zlength c' = Zlength c; di <= di' <= di + 8; di' <= di + n; 0 <= si';
              ov = OV_SRC_BEFORE_DST -> si' + 8 <= di';
              ov = OV_NO_OVERLAP -> si' = si /\ di' = di;
              forall m, 0 <= m <= di + n - di' ->
                listcopy c' si' di' (Z.to_nat m) = listcopy c si di (Z.to_nat (di' - di + m));
              byte_cells c -> byte_cells c';
              copy_src_def c' si' di' (di + n - di'); kept_or_byte c c';
              (* the array and pointers as BlkSeqXMem.lsafecopy has them after its overlapCopy8 step *)
              (if ov =? OV_SRC_BEFORE_DST then lov8 c di si (di - si) else (c, di, si)) = (c', di', si'))
        LOCAL (temp _oend (offset_val (di + n) p); lvar _ip (tptr tuchar) v_ip; lvar _op (tptr tuchar) v_op;
               gvars gv; temp _oend_w (offset_val dw p); temp _length (Vlong (Int64.repr (di + n - di')));
               temp _ovtype (Vint (Int.repr ov)))
        SEP (data_at Tsh (tptr tuchar) (offset_val si' p) v_ip;
             data_at Tsh (tptr tuchar) (offset_val di' p) v_op; zstd_globals gv;
             data_at sh (tarray tuchar (Zlength c)) c' p))%assert.
      * (* ZSTD_overlap_src_before_dst: ZSTD_overlapCopy8 first *)
        destruct H0 as [-> | ->].
        { exfalso. unfold OV_NO_OVERLAP in *. match goal with H: Int.repr 0 = Int.repr 1 |- _ =>
            apply (f_equal Int.unsigned) in H; rewrite !Int.unsigned_repr in H by rep_lia; lia end. }
        specialize (Hov1 eq_refl).
        forward. forward.
        assert (Hfd: offset_val di p = field_address (tarray tuchar (Zlength c)) (SUB di) p)
          by (rewrite arr_field_address by (auto; lia); simpl sizeof; f_equal; lia).
        assert (Hfs: offset_val si p = field_address (tarray tuchar (Zlength c)) (SUB (di - (di - si))) p)
          by (rewrite arr_field_address by (auto; lia); simpl sizeof; f_equal; lia).
        replace_SEP 0 (data_at Tsh (tptr tuchar) (field_address (tarray tuchar (Zlength c)) (SUB (di - (di - si))) p) v_ip).
        { entailer!; try (rewrite <- Hfs; apply derives_refl). }
        replace_SEP 1 (data_at Tsh (tptr tuchar) (field_address (tarray tuchar (Zlength c)) (SUB di) p) v_op).
        { entailer!; try (rewrite <- Hfd; apply derives_refl). }
        forward_call (gv, sh, p, c, v_op, v_ip, di, di - si).
        { apply prop_right, cp_sameblock; auto. }
        { entailer!. rewrite cp_sub_pp by auto. destruct v_op, v_ip; try contradiction; reflexivity. }
        { replace (di - (di - si)) with si by lia. apply (csd_oc8 c si di n); auto; lia. }
        match goal with H: lov8 _ _ _ _ = _ |- _ => rename H into Hlov8 end.
        replace (di - (di - si)) with si in Hlov8 by lia.
        pose proof (oc8_off_facts (di - si) ltac:(lia)) as [HK1 [HK3 HK2]].
        rewrite !arr_field_address0 by (auto; lia). simpl sizeof. rewrite !Z.mul_1_l.
        replace (di - (di - si)) with si by lia.
        forward.
        assert (Hx8: (if OV_SRC_BEFORE_DST =? OV_SRC_BEFORE_DST then lov8 c di si (di - si) else (c, di, si)) =
                     (listcopy c si di (Z.to_nat 8), di + 8, di + 8 - oc8_off (di - si))) by exact Hlov8.
        Exists (listcopy c si di (Z.to_nat 8)) (di + 8 - oc8_off (di - si)) (di + 8).
        entailer!.
        split; [unfold OV_SRC_BEFORE_DST, OV_NO_OVERLAP; intros; lia |].
        split; [intros m Hm; replace (di + 8 - di + m) with (8 + m) by lia; apply lc_reoff; lia |].
        split; [intros; apply bc_listcopy_Z; auto; lia |].
        split; [replace (di + n - (di + 8)) with (n - 8) by lia; apply oc8_csd; auto; lia |].
        split; [apply (csd_kob c si di n); auto; lia | do 2 f_equal; lia].
      * assert (Hx0: (if ov =? OV_SRC_BEFORE_DST then lov8 c di si (di - si) else (c, di, si)) = (c, di, si)).
        { destruct H0 as [-> | ->]; [reflexivity |]. exfalso. unfold OV_SRC_BEFORE_DST in *.
          match goal with H: Int.repr 1 <> Int.repr 1 |- _ => apply H; reflexivity end. }
        forward. Exists c si di. entailer!.
        split; [intros m Hm; do 2 f_equal; lia |].
        split; [replace (di + n - di) with n by lia; exact Hcsd |].
        split; [apply kob_refl | do 2 f_equal; lia].
      * Intros c' si' di'.
        match goal with H: byte_cells c -> byte_cells c' |- _ => rename H into Hbc' end.
        match goal with H: copy_src_def c' _ _ _ |- _ => rename H into Hcsd' end.
        match goal with H: kept_or_byte c c' |- _ => rename H into Hkob' end.
        match goal with H: (if _ then lov8 _ _ _ _ else _) = _ |- _ => rename H into Hxov end.
        assert (Hdwm: dw + 32 <= Zlength c) by lia.
        assert (Hdir: si' < di' \/ (ov = OV_NO_OVERLAP /\ si' = si /\ di' = di /\ di + n <= si /\
                                    dw + 32 <= si /\ si + n + 32 <= Zlength c)).
        { destruct H0 as [Ho | Ho].
          - destruct (H13 Ho) as [-> ->]. destruct (Hov0 Ho) as [Hs1 [Hs2 | Hs2]]; [left; lia | right; repeat split; auto; lia].
          - left. specialize (H12 Ho). lia. }
        assert (Hwov: ov = OV_NO_OVERLAP -> di' <= dw -> si' + 16 <= di' \/ di' + 16 <= si').
        { intros Ho Hd. destruct (H13 Ho) as [-> ->]. destruct (Hov0 Ho) as [Hs1 [Hs2 | Hs2]]; lia. }
        assert (Hsrc: forall m, 0 <= m <= di + n - di' -> di' + m <= dw -> si' + m + 32 <= Zlength c).
        { intros m Hm Hd. destruct H0 as [Ho | Ho].
          - destruct (H13 Ho) as [-> ->]. destruct (Hov0 Ho). lia.
          - specialize (H12 Ho). lia. }
        assert (Hms: Ptrofs.max_signed = 9223372036854775807) by reflexivity.
        assert (Hms64: Int64.max_signed = 9223372036854775807) by reflexivity.
        assert (Hmn64: Int64.min_signed = -9223372036854775808) by reflexivity.
        forward_if (PROP (dw < di + n)
          LOCAL (temp _oend (offset_val (di + n) p); lvar _ip (tptr tuchar) v_ip; lvar _op (tptr tuchar) v_op;
                 gvars gv; temp _oend_w (offset_val dw p); temp _length (Vlong (Int64.repr (di + n - di')));
                 temp _ovtype (Vint (Int.repr ov)))
          SEP (data_at Tsh (tptr tuchar) (offset_val si' p) v_ip;
               data_at Tsh (tptr tuchar) (offset_val di' p) v_op; zstd_globals gv;
               data_at sh (tarray tuchar (Zlength c)) c' p)).
        -- apply prop_right, cp_sameblock; auto.
        -- match goal with H: typed_true _ _ |- _ => rewrite cp_ge0_val in H by (auto; lia);
             destruct (zle (di + n) dw) as [Hle | Hgt]; [| inv H] end.
           forward. forward.
           assert (Hfd': offset_val di' p = field_address (tarray tuchar (Zlength c')) (SUB di') p)
             by (rewrite arr_field_address by (rewrite ?H8; auto; lia); simpl sizeof; f_equal; lia).
           assert (Hfs': offset_val si' p = field_address (tarray tuchar (Zlength c')) (SUB si') p)
             by (rewrite arr_field_address by (rewrite ?H8; auto; lia); simpl sizeof; f_equal; lia).
           rewrite <- H8.
           forward_call (gv, true, sh, p, c', si', di', Tsh, nullval, @nil val, Tsh, nullval, @nil val,
                         di + n - di', ov).
           { rewrite H8. pose proof (Hsrc (di + n - di') ltac:(lia) ltac:(lia)).
             split; [auto |]. split; [lia |]. split; [lia |]. split; [lia |]. split; [lia |].
             split; [lia |]. split; [auto | intros Hov; apply Hwov; auto; lia]. }
           Intros g. match goal with H: g = _ |- _ => subst g end.
           match goal with H: wc_within_post _ _ _ _ _ = lwild _ _ _ _ _ _ |- _ => rename H into Hw end.
           set (b := ((ov =? OV_SRC_BEFORE_DST) && (di' - si' <? 16))%bool) in *.
           pose proof (wc_ext_bounds b (di + n - di') ltac:(lia)) as HE.
           replace (di' + (di + n - di')) with (di + n) in Hw by lia.
           pose proof (lsc_w_wild c c' si di dw n ov si' di' (wc_ext b (di + n - di')) ltac:(lia) ltac:(lia) Hxov Hw
                         ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hex.
           rewrite wc_post_listcopy by (rewrite ?H8; lia).
           forward.
           destruct (sc_final2 c c' si di n si' di' (wc_ext b (di + n - di')) (di + n - di') dw)
             as [F1 [F2 F3]]; auto; try lia.
           replace (di + n - di' - (di + n - di')) with 0 in F1, F2, F3 by lia.
           rewrite listcopy_zero in F1, F2, F3.
           assert (Hbx: byte_cells c -> byte_cells (listcopy c' si' di' (Z.to_nat (wc_ext b (di + n - di')))))
             by (intros Hb; apply bc_listcopy_Z; auto; lia).
           assert (Hkq := kob_unfold _ _ (kob_trans c c' _ H8 Hkob'
             (csd_kob c' si' di' (di + n - di') (wc_ext b (di + n - di')) Hcsd'
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)))).
           Exists (listcopy c' si' di' (Z.to_nat (wc_ext b (di + n - di')))).
           rewrite H8. entailer!.
        -- match goal with H: typed_false _ _ |- _ => rewrite cp_ge0_val in H by (auto; lia);
             destruct (zle (di + n) dw) as [Hle | Hgt]; [inv H |] end.
           forward. entailer!.
        -- Intros.
           forward.
           forward_if (EX E0: Z, EX a: Z,
             PROP (0 <= a <= E0; E0 <= a + 31; a <= di + n - di'; di' + E0 <= Zlength c;
                   di' + E0 <= Z.max (di + n) (dw + 32); di' + E0 <= di + n + 32;
                   si' < di' \/ (di' + E0 <= si' /\ di' + (di + n - di') <= si' /\
                                 si' + E0 <= Zlength c /\ si' + (di + n - di') <= Zlength c);
                   (* the wild part as BlkSeqXMem.lwild *)
                   (a, listcopy c' si' di' (Z.to_nat E0)) =
                     (if dw - di' >=? 0 then (dw - di', lwild c' di' LW si' (dw - di') (ov =? OV_SRC_BEFORE_DST))
                      else (0, c')))
             LOCAL (temp _oend (offset_val (di + n) p); lvar _ip (tptr tuchar) v_ip; lvar _op (tptr tuchar) v_op;
                    gvars gv)
             SEP (data_at Tsh (tptr tuchar) (offset_val (si' + a) p) v_ip;
                  data_at Tsh (tptr tuchar) (offset_val (di' + a) p) v_op; zstd_globals gv;
                  data_at sh (tarray tuchar (Zlength c)) (listcopy c' si' di' (Z.to_nat E0)) p))%assert.
           { apply prop_right, cp_sameblock; auto. }
           { match goal with H: typed_true _ _ |- _ => rewrite cp_ge0_val in H by (auto; lia);
               destruct (zle di' dw) as [Hle | Hgt]; [| inv H] end.
             forward. forward. forward.
             assert (Hfd': offset_val di' p = field_address (tarray tuchar (Zlength c')) (SUB di') p)
               by (rewrite arr_field_address by (rewrite ?H8; auto; lia); simpl sizeof; f_equal; lia).
             assert (Hfs': offset_val si' p = field_address (tarray tuchar (Zlength c')) (SUB si') p)
               by (rewrite arr_field_address by (rewrite ?H8; auto; lia); simpl sizeof; f_equal; lia).
             rewrite <- H8.
             forward_call (gv, true, sh, p, c', si', di', Tsh, nullval, @nil val, Tsh, nullval, @nil val,
                           dw - di', ov).
             { apply prop_right, cp_sameblock; auto. }
             { entailer!. rewrite cp_sub_pp by auto. rewrite <- Hfd', <- Hfs'. reflexivity. }
             { rewrite H8. pose proof (Hsrc (dw - di') ltac:(lia) ltac:(lia)).
               split; intros _.
               - split; [auto |]. split; [lia |]. split; [lia |]. split; [lia |]. split; [lia |].
                 split; [lia |]. split; [auto | intros Hov; apply Hwov; auto; lia].
               - apply (csd_mono c' si' di' (di + n - di')); auto; lia. }
             Intros g. match goal with H: g = _ |- _ => subst g end.
             match goal with H: wc_within_post _ _ _ _ _ = lwild _ _ _ _ _ _ |- _ => rename H into Hw end.
             set (b := ((ov =? OV_SRC_BEFORE_DST) && (di' - si' <? 16))%bool) in *.
             pose proof (wc_ext_bounds b (dw - di') ltac:(lia)) as HE.
             rewrite wc_post_listcopy by (rewrite ?H8; lia).
             unfold WILDCOPY_OVERLENGTH in Hw. rewrite wc_post_listcopy in Hw by (rewrite ?H8; lia).
             assert (HE0: (dw - di', listcopy c' si' di' (Z.to_nat (wc_ext b (dw - di')))) =
                     (if dw - di' >=? 0 then (dw - di', lwild c' di' LW si' (dw - di') (ov =? OV_SRC_BEFORE_DST))
                      else (0, c')))
               by (rewrite (proj2 (Z.geb_le _ _)) by lia; rewrite Hw; reflexivity).
             forward. forward. forward.
             1: (entailer!; apply prop_right, cp_sameblock; auto).
             rewrite cp_sub_pp by auto. simp_ptr.
             forward. forward. forward.
             1: (entailer!; apply prop_right, cp_sameblock; auto).
             rewrite cp_sub_pp by auto. simp_ptr.
             Exists (wc_ext b (dw - di')) (dw - di'). rewrite H8. entailer!. }
           { match goal with H: typed_false _ _ |- _ => rewrite cp_ge0_val in H by (auto; lia);
               destruct (zle di' dw) as [Hle | Hgt]; [inv H |] end.
             assert (HE0: (0, listcopy c' si' di' (Z.to_nat 0)) =
                     (if dw - di' >=? 0 then (dw - di', lwild c' di' LW si' (dw - di') (ov =? OV_SRC_BEFORE_DST))
                      else (0, c')))
               by (rewrite Z.geb_leb, (proj2 (Z.leb_gt _ _)) by lia; reflexivity).
             forward. Exists 0 0. rewrite !Z.add_0_r. entailer!. }
           Intros E0 a.
           match goal with H: (a, listcopy c' si' di' (Z.to_nat E0)) = _ |- _ => rename H into HE0' end.
           forward_loop (EX j: Z, PROP (0 <= j <= (di + n - di' - a))
             LOCAL (temp _oend (offset_val (di + n) p); lvar _ip (tptr tuchar) v_ip; lvar _op (tptr tuchar) v_op; gvars gv)
             SEP (data_at Tsh (tptr tuchar) (offset_val ((si' + a) + j) p) v_ip;
                  data_at Tsh (tptr tuchar) (offset_val ((di' + a) + j) p) v_op; zstd_globals gv;
                  data_at sh (tarray tuchar (Zlength c))
                    (listcopy (listcopy c' si' di' (Z.to_nat E0)) (si' + a) (di' + a) (Z.to_nat j)) p))%assert
           break: (PROP () LOCAL (lvar _ip (tptr tuchar) v_ip; lvar _op (tptr tuchar) v_op; gvars gv)
             SEP (data_at Tsh (tptr tuchar) (offset_val ((si' + a) + (di + n - di' - a)) p) v_ip;
                  data_at Tsh (tptr tuchar) (offset_val ((di' + a) + (di + n - di' - a)) p) v_op; zstd_globals gv;
                  data_at sh (tarray tuchar (Zlength c))
                    (listcopy (listcopy c' si' di' (Z.to_nat E0)) (si' + a) (di' + a) (Z.to_nat (di + n - di' - a))) p))%assert.
           { Exists 0. entailer!; apply derives_refl. }
           { Intros j. forward. forward_if.
             - apply (cp_test_order_TT sh (Zlength c)
                 (listcopy (listcopy c' si' di' (Z.to_nat E0)) (si' + a) (di' + a) (Z.to_nat j)));
                 [apply writable_readable; auto | auto | lia | lia | lia | cancel].
             - cmp_simpl. forward. forward.
               assert (HL0: Zlength (listcopy c' si' di' (Z.to_nat E0)) = Zlength c)
                 by (rewrite Zlength_listcopy; lia).
               assert (HLj: Zlength (listcopy (listcopy c' si' di' (Z.to_nat E0)) (si' + a) (di' + a) (Z.to_nat j)) = Zlength c)
                 by (rewrite Zlength_listcopy; rewrite ?HL0; lia).
               forward_call (mm_within sh p (Zlength c)
                 (listcopy (listcopy c' si' di' (Z.to_nat E0)) (si' + a) (di' + a) (Z.to_nat j)) (si' + a + j) (di' + a + j) 1).
               { simpl. split; [exact SH |]. repeat (split; [rep_lia |]).
                 apply fa_bv, Forall_sublist_pt; [lia | rewrite HLj; lia |].
                 intros x Hx. replace x with (si' + a + j) by lia.
                 apply (sc_read_def c' si' di' (di + n - di') E0 a j); auto; lia. }
               simpl mm_post. rewrite mm1_upd by lia.
               rewrite (byte_step_nocast (listcopy c' si' di' (Z.to_nat E0)) (si' + a) (di' + a) j
                          (di' + a + j) (si' + a + j) _ _ (Z.to_nat (j + 1))) by (try reflexivity; lia).
               forward. forward. forward. forward. simp_ptr.
               Exists (j + 1). replace ((si' + a) + (j + 1)) with ((si' + a) + j + 1) by lia.
               replace ((di' + a) + (j + 1)) with ((di' + a) + j + 1) by lia. entailer!.
             - cmp_simpl. forward. assert (j = (di + n - di' - a)) by lia. subst j. entailer!. }
           destruct (sc_final2 c c' si di n si' di' E0 a dw) as [F1 [F2 F3]]; auto; try lia.
           assert (Hbx: byte_cells c ->
             byte_cells (listcopy (listcopy c' si' di' (Z.to_nat E0)) (si' + a) (di' + a) (Z.to_nat (di + n - di' - a))))
             by (intros Hb; apply bc_listcopy2; auto; lia).
           assert (Hkq: kept_or_byte c
             (listcopy (listcopy c' si' di' (Z.to_nat E0)) (si' + a) (di' + a) (Z.to_nat (di + n - di' - a)))).
           { assert (HL0: Zlength (listcopy c' si' di' (Z.to_nat E0)) = Zlength c') by (apply Zlength_listcopy; lia).
             apply (kob_trans c c'); [lia | exact Hkob' |].
             apply (kob_trans c' (listcopy c' si' di' (Z.to_nat E0)));
               [lia | apply (csd_kob c' si' di' (di + n - di')); auto; lia |].
             apply kob_listcopy; [lia | lia | lia |]. intros j Hj.
             apply (sc_read_def c' si' di' (di + n - di') E0 a j); auto; lia. }
           pose proof (kob_unfold _ _ Hkq) as Hkq'.
           pose proof (lsc_w_tail c c' si di dw n ov si' di' E0 a ltac:(lia) ltac:(lia) Hxov HE0') as Hex.
           Exists (listcopy (listcopy c' si' di' (Z.to_nat E0)) (si' + a) (di' + a) (Z.to_nat (di + n - di' - a))).
           entailer!.
  - (* disjoint: the source is a separate array *)
    destruct H8 as [Hshs [Hov Hcs]]; [reflexivity |]. clear H7. subst ov.
    assert (Hcsb := H10 eq_refl). clear H9 H10.
    assert_PROP (field_compatible (tarray tuchar (Zlength cs)) [] ps) as Hfcs by entailer!.
    destruct (fc_tuchar_bound _ _ Hfcs) as [Hps Hcsm].
    rewrite !arr_field_address by (auto; lia). simpl sizeof. rewrite !Z.mul_1_l.
    forward. forward. forward. forward. simp_ptr.
    forward_if (PROP (8 <= n)
      LOCAL (temp _oend (offset_val (di + n) p); lvar _ip (tptr tuchar) v_ip; lvar _op (tptr tuchar) v_op;
             gvars gv; temp _oend_w (offset_val dw p); temp _length (Vlong (Int64.repr n));
             temp _ovtype (Vint (Int.repr OV_NO_OVERLAP)))
      SEP (data_at Tsh (tptr tuchar) ps v_ip;
           data_at Tsh (tptr tuchar) (offset_val di p) v_op; zstd_globals gv;
           data_at sh (tarray tuchar (Zlength c)) c p; data_at shs (tarray tuchar (Zlength cs)) cs ps)).
    + (* short copies: the byte loop *)
      rewrite Int64.unsigned_repr in * by rep_lia.
      change (Int64.unsigned (Int64.repr 8)) with 8 in *.
      forward_loop (EX j: Z, PROP (0 <= j <= n)
        LOCAL (temp _oend (offset_val (di + n) p); lvar _ip (tptr tuchar) v_ip; lvar _op (tptr tuchar) v_op; gvars gv)
        SEP (data_at Tsh (tptr tuchar) (offset_val j ps) v_ip;
             data_at Tsh (tptr tuchar) (offset_val (di + j) p) v_op; zstd_globals gv;
             data_at sh (tarray tuchar (Zlength c)) (sublist 0 di c ++ sublist 0 j cs ++ sublist (di + j) (Zlength c) c) p;
             data_at shs (tarray tuchar (Zlength cs)) cs ps))%assert
      break: (PROP () LOCAL (lvar _ip (tptr tuchar) v_ip; lvar _op (tptr tuchar) v_op; gvars gv)
        SEP (data_at Tsh (tptr tuchar) (offset_val n ps) v_ip;
             data_at Tsh (tptr tuchar) (offset_val (di + n) p) v_op; zstd_globals gv;
             data_at sh (tarray tuchar (Zlength c)) (sublist 0 di c ++ sublist 0 n cs ++ sublist (di + n) (Zlength c) c) p;
             data_at shs (tarray tuchar (Zlength cs)) cs ps))%assert.
      { Exists 0. replace (sublist 0 di c ++ sublist 0 0 cs ++ sublist (di + 0) (Zlength c) c) with c by list_solve.
        rewrite isptr_offset_val_zero by auto. rewrite Z.add_0_r. entailer!. }
      { Intros j. forward. forward_if.
        - apply (cp_test_order_TT sh (Zlength c) (sublist 0 di c ++ sublist 0 j cs ++ sublist (di + j) (Zlength c) c));
            [apply writable_readable; auto | auto | lia | lia | lia | cancel].
        - cmp_simpl. forward. forward.
          assert (HLj: Zlength (sublist 0 di c ++ sublist 0 j cs ++ sublist (di + j) (Zlength c) c) = Zlength c)
            by list_solve.
          sep_apply (tuchar_cell_split sh p (Zlength c) (sublist 0 di c ++ sublist 0 j cs ++ sublist (di + j) (Zlength c) c) (di + j)); try solve [auto | lia].
          sep_apply (tuchar_cell_split shs ps (Zlength cs) cs j); try solve [auto | lia].
          forward_call (mm_disjoint shs sh (offset_val j ps) (offset_val (di + j) p) 1 [Znth j cs]).
          { simpl mm_pre. cancel. }
          { simpl. split; [auto |]. split; [auto |]. split; [reflexivity |]. split; [rep_lia |].
            apply Forall_cons; [| constructor]. apply (Forall_sublist_pt_inv cs 0 (n + 32)); auto; lia. }
          simpl mm_post.
          sep_apply (tuchar_cell_join shs ps (Zlength cs) cs j (Znth j cs)); try solve [auto | lia].
          sep_apply (tuchar_cell_join sh p (Zlength c) (sublist 0 di c ++ sublist 0 j cs ++ sublist (di + j) (Zlength c) c) (di + j) (Znth j cs)); try solve [auto | lia].
          replace (upd_Znth j cs (Znth j cs)) with cs by list_solve.
          replace (upd_Znth (di + j) (sublist 0 di c ++ sublist 0 j cs ++ sublist (di + j) (Zlength c) c) (Znth j cs))
            with (sublist 0 di c ++ sublist 0 (j + 1) cs ++ sublist (di + (j + 1)) (Zlength c) c) by list_solve.
          forward. forward. forward. forward. simp_ptr.
          Exists (j + 1). replace (di + (j + 1)) with (di + j + 1) by lia. entailer!.
        - cmp_simpl. forward. assert (j = n) by lia. subst j. entailer!. }
      assert (Hbx: byte_cells c /\ byte_cells cs -> byte_cells (sublist 0 di c ++ sublist 0 n cs ++ sublist (di + n) (Zlength c) c))
        by (intros [? ?]; bc).
      assert (Hkq: kept_or_byte c (sublist 0 di c ++ sublist 0 n cs ++ sublist (di + n) (Zlength c) c))
        by (apply (kob_splice c cs di 0 n (di + n)); try lia; fa_range).
      pose proof (kob_unfold _ _ Hkq) as Hkq'.
      pose proof (lsc_d_short c cs di dw n ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hex.
      forward. Exists (sublist 0 di c ++ sublist 0 n cs ++ sublist (di + n) (Zlength c) c). entailer!.
      split; [list_solve |].
      intros k Hk Hout. assert (k < di \/ di + n <= k) as [Hl | Hl] by lia; list_solve.
    + rewrite Int64.unsigned_repr in * by rep_lia.
      change (Int64.unsigned (Int64.repr 8)) with 8 in *.
      forward. entailer!.
    + Intros.
      forward_if (PROP ()
        LOCAL (temp _oend (offset_val (di + n) p); lvar _ip (tptr tuchar) v_ip; lvar _op (tptr tuchar) v_op;
               gvars gv; temp _oend_w (offset_val dw p); temp _length (Vlong (Int64.repr n));
               temp _ovtype (Vint (Int.repr OV_NO_OVERLAP)))
        SEP (data_at Tsh (tptr tuchar) ps v_ip;
             data_at Tsh (tptr tuchar) (offset_val di p) v_op; zstd_globals gv;
             data_at sh (tarray tuchar (Zlength c)) c p; data_at shs (tarray tuchar (Zlength cs)) cs ps)).
      { exfalso. unfold OV_NO_OVERLAP in *. match goal with H: Int.repr 0 = Int.repr 1 |- _ =>
          apply (f_equal Int.unsigned) in H; rewrite !Int.unsigned_repr in H by rep_lia; lia end. }
      { forward. entailer!. }
      assert (Hdwm: dw + 32 <= Zlength c) by lia.
      assert (Hms: Ptrofs.max_signed = 9223372036854775807) by reflexivity.
      assert (Hms64: Int64.max_signed = 9223372036854775807) by reflexivity.
      assert (Hmn64: Int64.min_signed = -9223372036854775808) by reflexivity.
      forward_if (PROP (dw < di + n)
        LOCAL (temp _oend (offset_val (di + n) p); lvar _ip (tptr tuchar) v_ip; lvar _op (tptr tuchar) v_op;
               gvars gv; temp _oend_w (offset_val dw p); temp _length (Vlong (Int64.repr n));
               temp _ovtype (Vint (Int.repr OV_NO_OVERLAP)))
        SEP (data_at Tsh (tptr tuchar) ps v_ip;
             data_at Tsh (tptr tuchar) (offset_val di p) v_op; zstd_globals gv;
             data_at sh (tarray tuchar (Zlength c)) c p; data_at shs (tarray tuchar (Zlength cs)) cs ps)).
      * apply prop_right, cp_sameblock; auto.
      * match goal with H: typed_true _ _ |- _ => rewrite cp_ge0_val in H by (auto; lia);
          destruct (zle (di + n) dw) as [Hle | Hgt]; [| inv H] end.
        forward. forward.
        sep_apply (tuchar_split_N sh p (Zlength c) c di); try solve [auto | lia].
        forward_call (gv, false, sh, p, c, si, di, shs, ps, cs, sh, offset_val di p, sublist di (Zlength c) c,
                      n, OV_NO_OVERLAP).
        { cancel. }
        { split; [auto |]. split; [auto |]. split; [reflexivity |]. split; [lia |]. list_solve. }
        Intros g. match goal with H: g = _ |- _ =>
          assert (Hbg: byte_cells c -> byte_cells cs -> byte_cells g) by (intros; rewrite H; bc);
          assert (Hkq: kept_or_byte c (sublist 0 di c ++
            (sublist 0 n cs ++ g ++ sublist (n + 32) (Zlength (sublist di (Zlength c) c)) (sublist di (Zlength c) c))))
            by (rewrite H; pose proof (wc_ext_bounds false n ltac:(lia)); apply kob_dj_wc; try lia; fa_range);
          clear H end.
        pose proof (kob_unfold _ _ Hkq) as Hkq'.
        match goal with Hw: _ = lwild _ _ _ _ _ _ |- _ =>
          pose proof (lsc_d_wild c cs g di dw n ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hw) as Hex end.
        sep_apply (tuchar_join_at sh p (Zlength c) (sublist 0 di c)
          (sublist 0 n cs ++ g ++ sublist (n + 32) (Zlength (sublist di (Zlength c) c)) (sublist di (Zlength c) c))
          (Zlength (sublist 0 di c)) (Zlength (sublist di (Zlength c) c)) di); try solve [auto | list_solve].
        forward.
        Exists (sublist 0 di c ++
          (sublist 0 n cs ++ g ++ sublist (n + 32) (Zlength (sublist di (Zlength c) c)) (sublist di (Zlength c) c))).
        entailer!.
        split; [list_solve |]. split.
        { intros k Hk Hout. assert (k < di \/ di + n + 32 <= k) as [Hl | Hl] by lia; list_solve. }
        intros [? ?]. specialize (Hbg ltac:(auto) ltac:(auto)). bc.
      * match goal with H: typed_false _ _ |- _ => rewrite cp_ge0_val in H by (auto; lia);
          destruct (zle (di + n) dw) as [Hle | Hgt]; [inv H |] end.
        forward. entailer!.
      * Intros.
        forward.
        forward_if (EX a: Z, EX c1: list val,
          PROP (0 <= a <= n; Zlength c1 = Zlength c; sublist di (di + a) c1 = sublist 0 a cs;
                forall k, 0 <= k < Zlength c -> ~ (di <= k < Z.min (di + n + 32) (Z.max (di + n) (dw + 32))) ->
                  Znth k c1 = Znth k c;
                byte_cells c -> byte_cells cs -> byte_cells c1; kept_or_byte c c1;
                (* the wild part as BlkSeqXMem.lwild *)
                (a, c1) = (if dw - di >=? 0 then (dw - di, lwild c di (LS cs) 0 (dw - di) false) else (0, c)))
          LOCAL (temp _oend (offset_val (di + n) p); lvar _ip (tptr tuchar) v_ip; lvar _op (tptr tuchar) v_op;
                 gvars gv)
          SEP (data_at Tsh (tptr tuchar) (offset_val a ps) v_ip;
               data_at Tsh (tptr tuchar) (offset_val (di + a) p) v_op; zstd_globals gv;
               data_at sh (tarray tuchar (Zlength c)) c1 p; data_at shs (tarray tuchar (Zlength cs)) cs ps))%assert.
        { apply prop_right, cp_sameblock; auto. }
        { match goal with H: typed_true _ _ |- _ => rewrite cp_ge0_val in H by (auto; lia);
            destruct (zle di dw) as [Hle | Hgt]; [| inv H] end.
          forward. forward. forward.
          sep_apply (tuchar_split_N sh p (Zlength c) c di); try solve [auto | lia].
          forward_call (gv, false, sh, p, c, si, di, shs, ps, cs, sh, offset_val di p, sublist di (Zlength c) c,
                        dw - di, OV_NO_OVERLAP).
          { apply prop_right, cp_sameblock; auto. }
          { entailer!. rewrite cp_sub_pp by auto. reflexivity. }
          { cancel. }
          { split; intros _.
            - split; [auto |]. split; [auto |]. split; [reflexivity |]. split; [lia |]. list_solve.
            - fa_range. }
          Intros g. match goal with H: g = _ |- _ =>
            assert (Hbg: byte_cells c -> byte_cells cs -> byte_cells g) by (intros; rewrite H; bc);
            assert (Hkg: kept_or_byte c (sublist 0 di c ++ (sublist 0 (dw - di) cs ++ g ++
                      sublist (dw - di + 32) (Zlength (sublist di (Zlength c) c)) (sublist di (Zlength c) c))))
              by (rewrite H; pose proof (wc_ext_bounds false (dw - di) ltac:(lia)); apply kob_dj_wc; try lia; fa_range);
            clear H end.
          sep_apply (tuchar_join_at sh p (Zlength c) (sublist 0 di c)
            (sublist 0 (dw - di) cs ++ g ++ sublist (dw - di + 32) (Zlength (sublist di (Zlength c) c)) (sublist di (Zlength c) c))
            (Zlength (sublist 0 di c)) (Zlength (sublist di (Zlength c) c)) di); try solve [auto | list_solve].
          forward. forward. forward.
          1: (entailer!; apply prop_right, cp_sameblock; auto).
          rewrite cp_sub_pp by auto. simp_ptr.
          forward. forward. forward.
          1: (entailer!; apply prop_right, cp_sameblock; auto).
          rewrite cp_sub_pp by auto. simp_ptr.
          match goal with Hw: _ = lwild _ _ _ _ _ _ |- _ => unfold WILDCOPY_OVERLENGTH in Hw;
            assert (Hc1: (dw - di, sublist 0 di c ++ (sublist 0 (dw - di) cs ++ g ++
                      sublist (dw - di + 32) (Zlength (sublist di (Zlength c) c)) (sublist di (Zlength c) c))) =
                    (if dw - di >=? 0 then (dw - di, lwild c di (LS cs) 0 (dw - di) false) else (0, c)))
              by (rewrite (proj2 (Z.geb_le _ _)) by lia; rewrite Hw, lwild_LS_shift by lia; reflexivity) end.
          Exists (dw - di) (sublist 0 di c ++
            (sublist 0 (dw - di) cs ++ g ++ sublist (dw - di + 32) (Zlength (sublist di (Zlength c) c)) (sublist di (Zlength c) c))).
          entailer!.
          split; [list_solve |]. split.
          { intros k Hk Hout. assert (k < di \/ dw + 32 <= k) as [Hl | Hl] by lia; list_solve. }
          intros. specialize (Hbg ltac:(auto) ltac:(auto)). bc. }
        { match goal with H: typed_false _ _ |- _ => rewrite cp_ge0_val in H by (auto; lia);
            destruct (zle di dw) as [Hle | Hgt]; [inv H |] end.
          pose proof (kob_refl c) as Hk0.
          assert (Hc1: (0, c) = (if dw - di >=? 0 then (dw - di, lwild c di (LS cs) 0 (dw - di) false) else (0, c)))
            by (rewrite Z.geb_leb, (proj2 (Z.leb_gt _ _)) by lia; reflexivity).
          forward. Exists 0 c. rewrite isptr_offset_val_zero by auto. rewrite Z.add_0_r. entailer!.
          list_solve. }
        Intros a c1.
        match goal with H: byte_cells c -> byte_cells cs -> byte_cells c1 |- _ => rename H into Hbc1 end.
        match goal with H: (a, c1) = _ |- _ => rename H into Hc1' end.
        forward_loop (EX j: Z, PROP (0 <= j <= n - a)
          LOCAL (temp _oend (offset_val (di + n) p); lvar _ip (tptr tuchar) v_ip; lvar _op (tptr tuchar) v_op; gvars gv)
          SEP (data_at Tsh (tptr tuchar) (offset_val (a + j) ps) v_ip;
               data_at Tsh (tptr tuchar) (offset_val (di + a + j) p) v_op; zstd_globals gv;
               data_at sh (tarray tuchar (Zlength c)) (sublist 0 (di + a) c1 ++ sublist a (a + j) cs ++ sublist (di + a + j) (Zlength c1) c1) p;
               data_at shs (tarray tuchar (Zlength cs)) cs ps))%assert
        break: (PROP () LOCAL (lvar _ip (tptr tuchar) v_ip; lvar _op (tptr tuchar) v_op; gvars gv)
          SEP (data_at Tsh (tptr tuchar) (offset_val (a + (n - a)) ps) v_ip;
               data_at Tsh (tptr tuchar) (offset_val (di + a + (n - a)) p) v_op; zstd_globals gv;
               data_at sh (tarray tuchar (Zlength c))
                 (sublist 0 (di + a) c1 ++ sublist a (a + (n - a)) cs ++ sublist (di + a + (n - a)) (Zlength c1) c1) p;
               data_at shs (tarray tuchar (Zlength cs)) cs ps))%assert.
        { Exists 0. rewrite dj_loop_0 by lia. rewrite !Z.add_0_r. entailer!. }
        { Intros j. forward. forward_if.
          - apply (cp_test_order_TT sh (Zlength c) (sublist 0 (di + a) c1 ++ sublist a (a + j) cs ++ sublist (di + a + j) (Zlength c1) c1));
              [apply writable_readable; auto | auto | lia | lia | lia | cancel].
          - cmp_simpl. forward. forward.
            assert (HLj: Zlength (sublist 0 (di + a) c1 ++ sublist a (a + j) cs ++ sublist (di + a + j) (Zlength c1) c1) = Zlength c) by (rewrite dj_loop_len; lia).
            sep_apply (tuchar_cell_split sh p (Zlength c) (sublist 0 (di + a) c1 ++ sublist a (a + j) cs ++ sublist (di + a + j) (Zlength c1) c1) (di + a + j)); try solve [auto | lia].
            sep_apply (tuchar_cell_split shs ps (Zlength cs) cs (a + j)); try solve [auto | lia].
            forward_call (mm_disjoint shs sh (offset_val (a + j) ps) (offset_val (di + a + j) p) 1 [Znth (a + j) cs]).
            { simpl mm_pre. cancel. }
            { simpl. split; [auto |]. split; [auto |]. split; [reflexivity |]. split; [rep_lia |].
            apply Forall_cons; [| constructor]. apply (Forall_sublist_pt_inv cs 0 (n + 32)); auto; lia. }
            simpl mm_post.
            sep_apply (tuchar_cell_join shs ps (Zlength cs) cs (a + j) (Znth (a + j) cs)); try solve [auto | lia].
            sep_apply (tuchar_cell_join sh p (Zlength c) (sublist 0 (di + a) c1 ++ sublist a (a + j) cs ++ sublist (di + a + j) (Zlength c1) c1) (di + a + j) (Znth (a + j) cs)); try solve [auto | lia].
            replace (upd_Znth (a + j) cs (Znth (a + j) cs)) with cs by list_solve.
            rewrite dj_loop_step by lia.
            forward. forward. forward. forward. simp_ptr.
            Exists (j + 1). replace (a + (j + 1)) with (a + j + 1) by lia.
            replace (di + a + (j + 1)) with (di + a + j + 1) by lia. entailer!.
          - cmp_simpl. forward. assert (j = n - a) by lia. subst j. entailer!. }
        destruct (sc_dj_final c c1 cs di n a (Z.min (di + n + 32) (Z.max (di + n) (dw + 32)))) as [F1 [F2 F3]];
          auto; try lia.
        assert (Hbx: byte_cells c /\ byte_cells cs ->
          byte_cells (sublist 0 (di + a) c1 ++ sublist a (a + (n - a)) cs ++ sublist (di + a + (n - a)) (Zlength c1) c1))
          by (intros [? ?]; specialize (Hbc1 ltac:(auto) ltac:(auto)); bc).
        assert (Hkq: kept_or_byte c
          (sublist 0 (di + a) c1 ++ sublist a (a + (n - a)) cs ++ sublist (di + a + (n - a)) (Zlength c1) c1)).
        { apply (kob_trans c c1); [lia | assumption |].
          apply (kob_splice c1 cs (di + a) a (a + (n - a)) (di + a + (n - a))); try lia. fa_range. }
        pose proof (kob_unfold _ _ Hkq) as Hkq'.
        pose proof (lsc_d_tail c cs c1 di dw n a ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                      ltac:(lia) Hc1') as Hex.
        Exists (sublist 0 (di + a) c1 ++ sublist a (a + (n - a)) cs ++ sublist (di + a + (n - a)) (Zlength c1) c1).
        entailer!.
Qed.

(* ---------- helpers for ZSTD_safecopyDstBeforeSrc ---------- *)
Lemma cp_sub_pp' (p: val) (a b: Z) : isptr p ->
  force_val (sem_binary_operation' Osub (tptr tuchar) (tptr tuchar) (offset_val a p) (offset_val b p)) =
  Vlong (Int64.repr (a - b)).
Proof. intros. apply cp_sub_pp; auto. Qed.

Lemma dbs_bytes (c: list val) (s d k n x: Z) :
  0 <= d <= s -> 0 <= k <= n -> s + n <= Zlength c -> d + k <= Zlength c ->
  Forall is_byte_val (sublist s (s + n) c) -> (d <= x < d + k \/ s <= x < s + n) ->
  is_byte_val (Znth x (listcopy c s d (Z.to_nat k))).
Proof.
  intros Hd Hk Hsn Hdk HB Hx.
  assert (Hc: forall y, s <= y < s + n -> is_byte_val (Znth y c)).
  { intros y Hy. rewrite Forall_forall in HB. apply HB.
    replace (Znth y c) with (Znth (y - s) (sublist s (s + n) c)) by (rewrite Znth_sublist by lia; f_equal; lia).
    apply Znth_In. rewrite Zlength_sublist by lia. lia. }
  destruct (Z_lt_le_dec x (d + k)) as [L | L]; [destruct (Z_lt_le_dec x d) as [L2 | L2] |].
  - rewrite listcopy_outside by (rewrite ?Z2Nat.id; lia). apply Hc; lia.
  - replace x with (d + (x - d)) by lia. rewrite listcopy_dbs by lia. apply Hc; lia.
  - rewrite listcopy_outside by (rewrite ?Z2Nat.id; lia). apply Hc; lia.
Qed.

Lemma dbs_final (c: list val) (si di n E0 a: Z) :
  0 <= di <= si -> 0 <= a <= E0 -> E0 <= n -> a <= n -> si + n <= Zlength c -> di + n <= Zlength c ->
  Forall is_byte_val (sublist si (si + n) c) ->
  let F := listcopy (listcopy c si di (Z.to_nat E0)) (si + a) (di + a) (Z.to_nat (n - a)) in
  Zlength F = Zlength c /\
  Forall is_byte_val (sublist di (di + n) F) /\
  (forall k, 0 <= k < Zlength c -> ~ (di <= k < di + n) -> Znth k F = Znth k c) /\
  (forall j, 0 <= j < n - a -> is_byte_val (Znth (si + a + j)
                 (listcopy (listcopy c si di (Z.to_nat E0)) (si + a) (di + a) (Z.to_nat j)))).
Proof.
  intros Hd Ha HE Han Hsn Hdn HB F. subst F.
  set (l := listcopy c si di (Z.to_nat E0)).
  assert (HL: Zlength l = Zlength c) by (apply Zlength_listcopy; lia).
  assert (Hl: forall x, (di <= x < di + E0 \/ si <= x < si + n) -> is_byte_val (Znth x l))
    by (intros; apply (dbs_bytes c si di E0 n); auto; lia).
  assert (HBl: Forall is_byte_val (sublist (si + a) (si + a + (n - a)) l)).
  { apply Forall_sublist_pt; try lia. intros x Hx. apply Hl. lia. }
  split; [rewrite Zlength_listcopy; rewrite ?HL; lia |].
  split; [| split].
  - apply Forall_sublist_pt; [lia | rewrite Zlength_listcopy; rewrite ?HL; lia |].
    intros x Hx. destruct (Z_lt_le_dec x (di + a)) as [L | L].
    + rewrite listcopy_outside by (rewrite ?HL, ?Z2Nat.id; lia). apply Hl; lia.
    + apply (dbs_bytes l (si + a) (di + a) (n - a) (n - a)); rewrite ?HL; auto; lia.
  - intros k Hk Hout.
    rewrite listcopy_outside by (rewrite ?HL, ?Z2Nat.id; lia).
    apply listcopy_outside; rewrite ?Z2Nat.id; lia.
  - intros j Hj. rewrite listcopy_outside by (rewrite ?HL, ?Z2Nat.id; lia). apply Hl; lia.
Qed.


Lemma cp_eval_sub_pi (p: val) (a k: Z) : isptr p -> Int.min_signed <= k <= Int.max_signed ->
  eval_binop Osub (tptr tuchar) tint (offset_val a p) (Vint (Int.repr k)) = offset_val (a - k) p.
Proof. intros. rewrite <- (cp_sub_pi p a k) by auto. destruct p; try contradiction. reflexivity. Qed.

Lemma cp_add_pl (p: val) (a k: Z) : isptr p ->
  force_val (sem_binary_operation' Oadd (tptr tuchar) tlong (offset_val a p) (Vlong (Int64.repr k))) =
  offset_val (a + k) p.
Proof.
  intros Hp. destruct p; try contradiction.
  assert (E: force_val (sem_add_ptr_long tuchar (offset_val a (Vptr b i)) (Vlong (Int64.repr k))) =
             offset_val (a + k) (Vptr b i)).
  { rewrite sem_add_pl_ptr_special by (auto; exact I). simpl force_val. simpl.
    rewrite Ptrofs.add_assoc, ptrofs_add_repr. replace (a + 1 * k)%Z with (a + k)%Z by lia. reflexivity. }
  exact E.
Qed.

Lemma dbs_exact (c: list val) (si di n E0 a: Z) :
  0 <= di -> di + 32 <= si -> 0 <= a <= E0 -> E0 <= a + 31 -> a <= n -> si + n <= Zlength c ->
  si + E0 <= Zlength c -> di + n <= Zlength c ->
  sublist di (di + n) (listcopy (listcopy c si di (Z.to_nat E0)) (si + a) (di + a) (Z.to_nat (n - a))) =
  sublist di (di + n) (listcopy c si di (Z.to_nat n)).
Proof.
  intros. destruct (lc_extend_dbs c si di E0 a (n - a)) as [F1 [F2 _]]; try lia.
  apply Znth_eq_ext. { rewrite !Zlength_sublist; rewrite ?F1, ?Zlength_listcopy; lia. }
  intros i Hi. rewrite Zlength_sublist in Hi by (rewrite ?F1; lia).
  rewrite !Znth_sublist by lia. replace (i + di) with (di + i) by lia.
  rewrite F2 by lia. symmetry. apply listcopy_dbs; lia.
Qed.

Lemma cp_ge_val (p: val) (a b k: Z) : isptr p -> Int64.min_signed <= a - b <= Int64.max_signed ->
  0 <= k <= Int.max_signed ->
  match both_long (fun n1 n2 : int64 => Some (bool2val (negb (Int64.lt n1 n2))))
      sem_cast_pointer (sem_cast_i2l Signed)
      (force_val (sem_sub_pp tuchar (offset_val a p) (offset_val b p))) (Vint (Int.repr k)) with
  | Some v' => v' | None => Vundef end = Vint (if zle k (a - b) then Int.one else Int.zero).
Proof.
  intros Hp Hab Hk. rewrite cp_sub_pp by auto. simpl. unfold Int64.lt.
  rewrite Int64.signed_repr by lia. rewrite ?Int.signed_repr by rep_lia.
  rewrite Int64.signed_repr by rep_lia.
  destruct (zlt (a - b) k), (zle k (a - b)); try lia; reflexivity.
Qed.

Lemma dbs_Forall_pt_inv (l: list val) (a b x: Z) :
  0 <= a -> b <= Zlength l -> Forall is_byte_val (sublist a b l) -> a <= x < b -> is_byte_val (Znth x l).
Proof.
  intros Ha Hb HF Hx. rewrite Forall_forall in HF. apply HF.
  replace (Znth x l) with (Znth (x - a) (sublist a b l)) by (rewrite Znth_sublist by lia; f_equal; lia).
  apply Znth_In. rewrite Zlength_sublist by lia. lia.
Qed.

Lemma dbs_sub_pp' (p: val) (a b: Z) : isptr p ->
  force_val (sem_binary_operation' Osub (tptr tuchar) (tptr tuchar) (offset_val a p) (offset_val b p)) =
  Vlong (Int64.repr (a - b)).
Proof. intros. apply cp_sub_pp; auto. Qed.

(* one-byte memmove inside the array = one step of the forward copy *)
Lemma dbs_mm_step (c: list val) (si di j N: Z) :
  0 <= j -> 0 <= si -> 0 <= di -> si + j + 1 <= N -> di + j + 1 <= N -> Zlength c = N ->
  mm_result (listcopy c si di (Z.to_nat j)) N (si + j) (di + j) 1 = listcopy c si di (Z.to_nat (j + 1)).
Proof.
  intros Hj Hs Hd Hsn Hdn HN.
  rewrite Z2Nat.inj_add by lia. change (Z.to_nat 1) with 1%nat.
  rewrite Nat.add_1_r, listcopy_snoc, Z2Nat.id by lia.
  assert (HL: Zlength (listcopy c si di (Z.to_nat j)) = N) by (rewrite Zlength_listcopy; lia).
  set (L := listcopy c si di (Z.to_nat j)) in *.
  unfold mm_result. rewrite upd_Znth_unfold by lia. rewrite (sublist_len_1 (si + j)) by lia.
  rewrite HL. reflexivity.
Qed.

(* the forward copy in any relative position: the written bytes are source bytes *)
Lemma lc_bytes_any (c: list val) (s d n: Z) :
  0 <= s -> 0 <= d -> 0 <= n -> s + n <= Zlength c -> d + n <= Zlength c ->
  Forall is_byte_val (sublist s (s + n) c) ->
  Forall is_byte_val (sublist d (d + n) (listcopy c s d (Z.to_nat n))).
Proof.
  intros Hs Hd Hn Hsn Hdn HB.
  apply Forall_sublist_pt; [lia | rewrite Zlength_listcopy; lia |].
  intros x Hx. destruct (Z_le_gt_dec d s) as [L | L].
  - apply (dbs_bytes c s d n n); auto; lia.
  - rewrite lc_char by lia.
    replace (andb (d <=? x) (x <? d + n)) with true
      by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    apply (dbs_Forall_pt_inv c s (s + n)); auto; try lia.
    pose proof (Z.mod_pos_bound (x - s) (d - s)).
    split; [lia |].
    destruct (Z_lt_le_dec (d - s) n) as [L2 | L2]; [lia |].
    replace (x - s) with ((x - d) + 1 * (d - s)) by lia. rewrite Z_mod_plus_full.
    rewrite Z.mod_small by lia. lia.
Qed.

Lemma body_ZSTD_safecopyDstBeforeSrc :
  semax_body Vprog (G_BLK ++ COPY_exports) f_ZSTD_safecopyDstBeforeSrc ZSTD_safecopyDstBeforeSrc_spec.
Proof.
  start_function. rename H6 into Hsdef.
  assert_PROP (field_compatible (tarray tuchar (Zlength c)) [] p) as Hfc by entailer!.
  destruct (fc_tuchar_bound _ _ Hfc) as [Hp Hcm].
  unfold WILDCOPY_OVERLENGTH, WILDCOPY_VECLEN in *.
  assert (Hn64: 0 <= n <= Int64.max_unsigned)
      by (assert (Ptrofs.modulus = Int64.modulus) by reflexivity; unfold Int64.max_unsigned; lia).
  assert (Hms: Ptrofs.max_signed = 9223372036854775807) by reflexivity.
  assert (Hms64: Int64.max_signed = 9223372036854775807) by reflexivity.
  assert (Hmn64: Int64.min_signed = -9223372036854775808) by reflexivity.
  rewrite !arr_field_address0 by (auto; lia). simpl sizeof. rewrite !Z.mul_1_l.
  forward.
  { entailer!. apply prop_right, cp_sameblock; auto. }
  rewrite dbs_sub_pp' by auto.
  forward. simp_ptr.
  forward_if (temp _t'1 (Vint (if zlt n 8 then Int.one else if zlt (-8) (di - si) then Int.one else Int.zero))).
  { forward. entailer!. rewrite Int64.unsigned_repr in * by rep_lia.
    destruct (zlt n 8); [reflexivity | change (Int64.unsigned (Int64.repr 8)) with 8 in *; lia]. }
  { forward. entailer!. rewrite Int64.unsigned_repr in * by rep_lia.
    change (Int64.unsigned (Int64.repr 8)) with 8 in *.
    destruct (zlt n 8); [lia |]. simpl. unfold Int64.lt.
    rewrite !Int64.signed_repr by lia.
    destruct (zlt (-8) (di - si)), (zlt (- (8)) (di - si)); try lia; reflexivity. }
  forward_if (PROP (8 <= n; 8 <= si - di)
      LOCAL (temp _oend (offset_val (di + n) p); temp _diff (Vlong (Int64.repr (di - si)));
             temp _op (offset_val di p); temp _ip (offset_val si p); temp _length (Vlong (Int64.repr n));
             gvars gv)
      SEP (zstd_globals gv; data_at sh (tarray tuchar (Zlength c)) c p)).
  - (* short, close or dst after src: the byte loop *)
    assert (Hsh: n < 8 \/ -8 < di - si).
    { match goal with H: (if zlt n 8 then _ else _) <> Int.zero |- _ => revert H end.
      destruct (zlt n 8); [intros; left; lia |].
      destruct (zlt (-8) (di - si)); [intros; right; lia | intros X; exfalso; apply X; reflexivity]. }
    replace_SEP 1 (data_at sh (tarray tuchar (Zlength c)) (listcopy c si di (Z.to_nat 0)) p).
    { entailer!. }
    forward_while (EX j: Z, PROP (0 <= j <= n)
      LOCAL (temp _op (offset_val (di + j) p); temp _ip (offset_val (si + j) p);
             temp _oend (offset_val (di + n) p); gvars gv)
      SEP (zstd_globals gv; data_at sh (tarray tuchar (Zlength c)) (listcopy c si di (Z.to_nat j)) p))%assert.
    { Exists 0. entailer!; try (repeat match goal with |- _ /\ _ => split end; f_equal; lia). }
    { entailer!. apply (cp_test_order_TT sh (Zlength c) (listcopy c si di (Z.to_nat j)));
        [apply writable_readable; auto | auto | lia | lia | lia | cancel]. }
    { cmp_simpl.
      forward_call (mm_within sh p (Zlength c) (listcopy c si di (Z.to_nat j)) (si + j) (di + j) 1).
      { unfold mm_ok. rewrite Zlength_listcopy by lia. split; [auto |]. repeat (split; [rep_lia |]).
        apply fa_bv, Forall_sublist_pt; [lia | rewrite Zlength_listcopy by lia; lia |]. intros x Hx.
        destruct (Z_le_gt_dec di si); [apply (dbs_bytes c si di j n) | apply (lc_bytes_sb c si di j n)]; auto; lia. }
      unfold mm_post.
      forward. forward.
      Exists (j + 1). entailer!.
      { split; f_equal; lia. }
      rewrite dbs_mm_step by (rewrite ?Zlength_listcopy; lia). cancel. }
    cmp_simpl. assert (j = n) by lia. subst j.
    pose proof (lsdbs_short c si di n Hsh) as Hex.
    forward.
    Exists (listcopy c si di (Z.to_nat n)). entailer!.
    split.
    + intros. apply lc_bytes_any; auto.
    + intros k Hk Hout. apply listcopy_outside; rewrite ?Z2Nat.id; lia.
  - forward. entailer!.
    match goal with H: (if zlt n 8 then _ else _) = Int.zero |- _ => revert H end.
    destruct (zlt n 8); [intros X; contradiction (Int.one_not_zero X) |].
    destruct (zlt (-8) (di - si)); [intros X; contradiction (Int.one_not_zero X) | intros; lia].
  - Intros.
    forward_if (temp _t'2 (Vint (if zle 32 n then (if zlt (di - si) (-16) then Int.one else Int.zero) else Int.zero))).
    { apply prop_right, cp_sameblock; auto. }
    { match goal with H: context [sem_sub_pp] |- _ => rewrite (cp_ge_val p (di + n) di 32) in H by (auto; rep_lia);
        destruct (zle 32 (di + n - di)) as [Hle | Hgt]; [| inv H] end.
      forward. entailer!.
      destruct (zle 32 n); [| lia]. simpl. unfold Int64.lt.
      rewrite ?Int64.signed_repr by lia.
      destruct (zlt (di - si) (-16)); reflexivity. }
    { match goal with H: context [sem_sub_pp] |- _ => rewrite (cp_ge_val p (di + n) di 32) in H by (auto; rep_lia);
        destruct (zle 32 (di + n - di)) as [Hle | Hgt]; [inv H |] end.
      forward. entailer!. destruct (zle 32 n); [lia | reflexivity]. }
    forward_if (EX E0: Z, EX a: Z,
      PROP (0 <= a <= E0; E0 <= n; a <= n; (E0 = 0 /\ a = 0) \/ (a = n - 32 /\ E0 <= a + 31 /\ di + 16 < si);
            (* the wild part as BlkSeqXMem.lwild *)
            (a, listcopy c si di (Z.to_nat E0)) =
              (if andb (n >=? 32) (di - si <? -16) then (n - 32, lwild c di LW si (n - 32) false) else (0, c)))
      LOCAL (temp _oend (offset_val (di + n) p); temp _op (offset_val (di + a) p); temp _ip (offset_val (si + a) p);
             gvars gv)
      SEP (zstd_globals gv; data_at sh (tarray tuchar (Zlength c)) (listcopy c si di (Z.to_nat E0)) p))%assert.
    { match goal with H: (if zle 32 n then _ else _) <> Int.zero |- _ =>
        destruct (zle 32 n) as [Hn32 | Hn32]; [| exfalso; apply H; reflexivity];
        destruct (zlt (di - si) (-16)) as [Hd16 | Hd16]; [| exfalso; apply H; reflexivity] end.
      assert (Hfd: offset_val di p = field_address (tarray tuchar (Zlength c)) (SUB di) p)
        by (rewrite arr_field_address by (auto; lia); simpl sizeof; f_equal; lia).
      assert (Hfs: offset_val si p = field_address (tarray tuchar (Zlength c)) (SUB si) p)
        by (rewrite arr_field_address by (auto; lia); simpl sizeof; f_equal; lia).
      forward_call (gv, true, sh, p, c, si, di, Tsh, nullval, @nil val, Tsh, nullval, @nil val, n - 32, 0).
      { rewrite cp_sub_pi by (auto; rep_lia). destruct p; try contradiction; exact I. }
      { rewrite cp_sub_pi by (auto; rep_lia). apply prop_right, cp_sameblock; auto. }
      { entailer!. rewrite cp_sub_pi by (auto; rep_lia). rewrite cp_sub_pp by auto.
        rewrite <- Hfd, <- Hfs. simpl. replace (di + n - 32 - di) with (n - 32) by lia. reflexivity. }
      { split; intros _.
        - split; [auto |]. split; [lia |]. split; [lia |]. split; [lia |]. split; [lia |]. split; [lia |].
          unfold OV_SRC_BEFORE_DST, OV_NO_OVERLAP. split; intros X; lia.
        - (* dst before src: the wild copy reads the n - 32 + 32 = n source bytes *)
          unfold copy_src_def, WILDCOPY_OVERLENGTH. rewrite (proj2 (Z.ltb_ge si di)) by lia.
          replace (si + (n - 32) + 32) with (si + n) by lia. exact Hsdef. }
      Intros g. match goal with H: g = _ |- _ => subst g end.
      match goal with H: wc_within_post _ _ _ _ _ = lwild _ _ _ _ _ _ |- _ => rename H into Hw end.
      set (b := ((0 =? OV_SRC_BEFORE_DST) && (di - si <? 16))%bool) in *.
      pose proof (wc_ext_bounds b (n - 32) ltac:(lia)) as HE.
      rewrite wc_post_listcopy by lia.
      unfold WILDCOPY_OVERLENGTH in Hw. rewrite wc_post_listcopy in Hw by lia.
      assert (HE0: (n - 32, listcopy c si di (Z.to_nat (wc_ext b (n - 32)))) =
                   (if andb (n >=? 32) (di - si <? -16) then (n - 32, lwild c di LW si (n - 32) false) else (0, c)))
        by (rewrite (proj2 (Z.geb_le n 32)), (proj2 (Z.ltb_lt (di - si) (-16))) by lia; rewrite Hw; reflexivity).
      forward.
      { entailer!. all: rewrite ?cp_sub_pi by (auto; rep_lia).
        all: first [ apply prop_right, cp_sameblock; auto | apply cp_sameblock; auto
                   | destruct p; try contradiction; exact I ]. }
      rewrite cp_eval_sub_pi by (auto; rep_lia). rewrite cp_eval_sub by auto. rewrite cp_add_pl by auto.
      forward.
      { entailer!. all: rewrite ?cp_sub_pi by (auto; rep_lia).
        all: first [ apply prop_right, cp_sameblock; auto | apply cp_sameblock; auto
                   | destruct p; try contradiction; exact I ]. }
      rewrite cp_eval_sub_pi by (auto; rep_lia). rewrite cp_eval_sub by auto. rewrite cp_add_pl by auto.
      Exists (wc_ext b (n - 32)) (n - 32).
      replace (si + (di + n - 32 - di)) with (si + (n - 32)) by lia.
      replace (di + (di + n - 32 - di)) with (di + (n - 32)) by lia.
      entailer!. }
    { assert (Hb: andb (n >=? 32) (di - si <? -16) = false).
      { match goal with H: (if zle 32 n then _ else _) = Int.zero |- _ => revert H end.
        destruct (zle 32 n), (zlt (di - si) (-16)); intros X;
          [contradiction (Int.one_not_zero X) | apply andb_false_iff ..].
        - right. apply Z.ltb_ge. lia.
        - left. rewrite Z.geb_leb. apply Z.leb_gt. lia.
        - left. rewrite Z.geb_leb. apply Z.leb_gt. lia. }
      assert (HE0: (0, listcopy c si di (Z.to_nat 0)) =
                   (if andb (n >=? 32) (di - si <? -16) then (n - 32, lwild c di LW si (n - 32) false) else (0, c)))
        by (rewrite Hb; reflexivity).
      forward. Exists 0 0. rewrite !Z.add_0_r. entailer!. }
    Intros E0 a.
    match goal with H: (a, listcopy c si di (Z.to_nat E0)) = _ |- _ => rename H into HE0' end.
    assert (HL0: Zlength (listcopy c si di (Z.to_nat E0)) = Zlength c) by (apply Zlength_listcopy; lia).
    forward_while (EX j: Z, PROP (0 <= j <= (n - a))
      LOCAL (temp _op (offset_val ((di + a) + j) p); temp _ip (offset_val ((si + a) + j) p);
             temp _oend (offset_val (di + n) p); gvars gv)
      SEP (zstd_globals gv; data_at sh (tarray tuchar (Zlength c)) (listcopy (listcopy c si di (Z.to_nat E0)) (si + a) (di + a) (Z.to_nat j)) p))%assert.
    { Exists 0. entailer!; try (repeat match goal with |- _ /\ _ => split end; f_equal; lia). }
    { entailer!. apply (cp_test_order_TT sh (Zlength c) (listcopy (listcopy c si di (Z.to_nat E0)) (si + a) (di + a) (Z.to_nat j)));
        [apply writable_readable; auto | auto | lia | lia | lia | cancel]. }
    { cmp_simpl.
      forward_call (mm_within sh p (Zlength c) (listcopy (listcopy c si di (Z.to_nat E0)) (si + a) (di + a) (Z.to_nat j)) (si + a + j) (di + a + j) 1).
      { unfold mm_ok. rewrite Zlength_listcopy by (rewrite ?HL0; lia). rewrite HL0.
        split; [auto |]. repeat (split; [rep_lia |]).
        apply fa_bv, Forall_sublist_pt; [lia | rewrite Zlength_listcopy by (rewrite ?HL0; lia); rewrite HL0; lia |].
        intros x Hx. replace x with (si + a + j) by lia.
        assert (F4 := proj2 (proj2 (proj2 (dbs_final c si di n E0 a ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                        ltac:(lia) ltac:(lia) Hsdef)))).
        apply F4; lia. }
      unfold mm_post.
      forward. forward.
      Exists (j + 1). entailer!.
      { split; f_equal; lia. }
      rewrite dbs_mm_step by (rewrite ?Zlength_listcopy, ?HL0; lia). cancel. }
    cmp_simpl. assert (j = (n - a)) by lia. subst j.
    pose proof (lsdbs_tail c si di n E0 a ltac:(lia) ltac:(lia) HE0') as Hex.
    forward.
    Exists (listcopy (listcopy c si di (Z.to_nat E0)) (si + a) (di + a) (Z.to_nat (n - a))).
    entailer!.
    split; [| split].
    + intros Hx. match goal with H: (E0 = 0 /\ a = 0) \/ _ |- _ => destruct H as [[-> ->] | [Ha [HE Hd]]] end.
      * rewrite !Z.add_0_r, Z.sub_0_r, listcopy_zero. reflexivity.
      * apply dbs_exact; lia.
    + intros HB. destruct (dbs_final c si di n E0 a) as [_ [F2 _]]; auto; lia.
    + intros k Hk Hout.
      rewrite listcopy_outside by (rewrite ?HL0, ?Z2Nat.id; lia).
      apply listcopy_outside; rewrite ?Z2Nat.id; lia.
Qed.

(* ================= the three bodies whose byte copies are one-byte ZSTD_memmove ================= *)
Lemma COPY_mm_bodies :
  Forall (body_ok (G_BLK ++ COPY_exports))
    [ ZSTD_overlapCopy8_spec; ZSTD_safecopy_spec; ZSTD_safecopyDstBeforeSrc_spec ].
Proof.
  repeat constructor.
  - exists f_ZSTD_overlapCopy8. split; [reflexivity | split; [reflexivity | apply body_ZSTD_overlapCopy8]].
  - exists f_ZSTD_safecopy. split; [reflexivity | split; [reflexivity | apply body_ZSTD_safecopy]].
  - exists f_ZSTD_safecopyDstBeforeSrc.
    split; [reflexivity | split; [reflexivity | apply body_ZSTD_safecopyDstBeforeSrc]].
Qed.

Lemma COPY_ok : COPY_obligation.
Proof.
  unfold COPY_obligation, subtree_ok, COPY_imports. rewrite app_nil_r.
  exists COPY_exports. split; [reflexivity | split; [apply incl_refl | ]].
  repeat constructor.
  - exists f_ZSTD_wildcopy. split; [reflexivity | split; [reflexivity | apply body_ZSTD_wildcopy]].
  - exists f_ZSTD_seqCopy. split; [reflexivity | split; [reflexivity | apply body_ZSTD_seqCopy]].
  - exact (Forall_inv COPY_mm_bodies).
  - exact (Forall_inv (Forall_inv_tail COPY_mm_bodies)).
  - exact (Forall_inv (Forall_inv_tail (Forall_inv_tail COPY_mm_bodies))).
Qed.
