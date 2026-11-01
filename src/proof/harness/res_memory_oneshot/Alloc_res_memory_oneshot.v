(* The counting allocator of harness/res_memory_oneshot.c (count_alloc, count_free) as an allocator a context
   may be given (CMem.cm_alloc_spec, cm_free_spec): its state CM o B h is the struct count at o (main's local,
   share Tsh) with now = h bytes given out and peak <= B; a block CB o p n carries its size n in the size_t just
   before p, in a block of 8 + n bytes from malloc.  The harness reads peak <= B at the end (count_peak). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Export Zstd.proof.top.HarnessDefs.
Require Zstd.contracts.res_memory_oneshot.
Require Export Zstd.harness.res_memory_oneshot.code.
Require Export Zstd.proof.zstd.CMem.
Require Import Zstd.proof.harness.CountAllocKit.
Local Open Scope logic.

#[export] Instance CompSpecs : compspecs := Zstd.contracts.res_memory_oneshot.Harness.CS.

Definition t_count : type := Tstruct _count noattr.

(* now = h (modulo 2^64) and peak <= B.  While B fits in a size_t, h <= peak: no sum of sizes wraps (h + n <= B at each
   allocation).  A bound beyond 2^64 - 1 (CM_mono lets a context raise it to any value) says nothing more.  The trailing
   TT absorbs the memory managers (mem_mgr) the two functions create for each call to malloc and free: their
   specifications carry none, and VST's logic does not let a function drop one. *)
Definition count_CM (o: val) (B h: Z) : mpred :=
  EX peak: Z, !! (0 <= h /\ 0 <= peak <= Int64.max_unsigned /\ peak <= B /\ (B <= Int64.max_unsigned -> h <= peak)) &&
  (data_at Tsh t_count (Vlong (Int64.repr h), Vlong (Int64.repr peak)) o * TT).

Definition count_CB (o p: val) (n: Z) : mpred :=
  !! (0 <= n <= Ptrofs.max_unsigned - 8) &&
  (data_at Ews tulong (Vlong (Int64.repr n)) (offset_val (-8) p) *
   malloc_token Ews (tarray tuchar (8 + n)) (offset_val (-8) p)).

Lemma count_CM_mono : forall o B B' h, B <= B' -> count_CM o B h |-- count_CM o B' h.
Proof.
  intros. unfold count_CM. Intros peak. Exists peak. entailer!.
Qed.

#[export] Instance count_cm : cmem_preds := {| CM := count_CM; CB := count_CB; CM_mono := count_CM_mono |}.

(* the harness's functions' context: malloc and free of the environment *)
Definition Vprog : varspecs := QPvarspecs Zstd.contracts.res_memory_oneshot.whole_prog.
Definition G_alloc : funspecs := [(_quickproof_malloc, malloc_spec'); (_quickproof_free, free_spec')].

Lemma body_count_alloc : semax_body Vprog G_alloc f_count_alloc (_count_alloc, cm_alloc_spec).
Proof.
  start_function.
  apply semax_gvars_intro; intro gv. sep_apply (create_mem_mgr gv).
  change (CM o B h) with (count_CM o B h). unfold count_CM. Intros peak.
  forward.
  forward_if (EX q: val, 
    PROP (q <> nullval -> 8 + n <= Int64.max_signed)
    LOCAL (temp _t'1 q; temp _count__1 o; gvars gv; temp _opaque o; temp _size (Vlong (Int64.repr n)))
    SEP (mem_mgr gv;
         if eq_dec q nullval then emp
         else malloc_token Ews (tarray tuchar (8 + n)) q * data_at_ Ews (tarray tuchar (8 + n)) q;
         data_at Tsh t_count (Vlong (Int64.repr h), Vlong (Int64.repr peak)) o; TT))%assert.
  - assert (Hn: n <= 9223372036854775799).
    { apply ltu_false_inv64 in H5. rewrite Int64.unsigned_repr in H5 by rep_lia.
      change (Int64.unsigned (Int64.sub (Int64.repr 9223372036854775807) (Int64.repr 8)))
        with 9223372036854775799 in H5. lia. }
    forward_call (tarray tuchar (8 + n), gv).
    { simpl. rep_lia. }
    Intros vret. forward. Exists vret. entailer!.
  - forward. Exists nullval. entailer!.
  - Intros q. forward.
    destruct (eq_dec q nullval) as [Hq | Hq].
    + subst q. forward_if.
      * forward. Exists nullval. rewrite if_true by auto. change (CM o B h) with (count_CM o B h).
        unfold count_CM. Exists peak. entailer!.
      * contradiction.
    + forward_if.
      * subst q. contradiction.
      * Intros. specialize (H5 Hq).
        assert_PROP (malloc_compatible (8 + n) q).
        { go_lower. sep_apply (malloc_token_local_facts Ews (tarray tuchar (8 + n)) q). simpl sizeof.
          rewrite Z.max_r by lia. Intros. apply prop_right. rewrite Z.mul_1_l in *. auto. }
        destruct q as [| | | | | b ofs]; try contradiction. destruct H7 as [Hal Hsz].
        sep_apply (data_at__memory_block_cancel Ews (tarray tuchar (8 + n)) (Vptr b ofs)).
        simpl sizeof. rewrite Z.mul_1_l, Z.max_r by lia.
        rewrite memory_block_split8 by lia.
        rewrite (memory_block_data_at_ Ews tulong (Vptr b ofs)).
        2: { apply malloc_compatible_field_compatible; auto. split; auto. simpl. lia. }
        Intros.
        assert_PROP (Vptr b (Ptrofs.add ofs (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_ints (Int.repr 0)))) =
                     field_address tulong [] (Vptr b ofs)).
        { entailer!. rewrite field_compatible_field_address by auto. simpl. normalize. }
        forward. forward. forward.
        rewrite add64_repr. forward. forward.
        set (now := (h + n) mod Int64.modulus).
        assert (Hnow: Int64.unsigned (Int64.repr (h + n)) = now) by (apply Int64.unsigned_repr_eq).
        forward_if (PROP ()
          LOCAL (temp _block (Vptr b ofs); temp _count__1 o; gvars gv; temp _size (Vlong (Int64.repr n)))
          SEP (field_at Ews tulong [] (Vlong (Int64.repr n)) (Vptr b ofs);
               memory_block Ews n (offset_val 8 (Vptr b ofs));
               mem_mgr gv; malloc_token Ews (tarray tuchar (8 + n)) (Vptr b ofs);
               data_at Tsh t_count (Vlong (Int64.repr (h + n)), Vlong (Int64.repr (Z.max peak now))) o; TT)).
        { forward. forward. entailer!.
          apply Int64.ltu_inv in H8. rewrite Int64.unsigned_repr in H8 by lia. rewrite Hnow in H8.
          rewrite Z.max_r by lia. rewrite <- Hnow, Int64.repr_unsigned. cancel. }
        { forward. entailer!.
          apply ltu_false_inv64 in H8. rewrite Int64.unsigned_repr in H8 by lia. rewrite Hnow in H8.
          rewrite Z.max_l by lia. cancel. }
        forward. Exists (offset_val 8 (Vptr b ofs)). rewrite if_false by (simpl; discriminate).
        change (CM o B (h + n)) with (count_CM o B (h + n)).
        change (CB o (offset_val 8 (Vptr b ofs)) n) with (count_CB o (offset_val 8 (Vptr b ofs)) n).
        unfold count_CM, count_CB. Exists (Z.max peak ((h + n) mod Int64.modulus)).
        replace (offset_val (-8) (offset_val 8 (Vptr b ofs))) with (Vptr b ofs).
        2: { simpl. f_equal. rewrite Ptrofs.add_assoc. rewrite <- (Ptrofs.add_zero ofs) at 1. f_equal.
             rewrite ptrofs_add_repr. reflexivity. }
        entailer!. split; [right |].
        { simpl. unfold Ptrofs.add. rewrite (Ptrofs.unsigned_repr 8) by rep_lia.
          rewrite Ptrofs.unsigned_repr by rep_lia. split; [| lia].
          apply Z.divide_add_r; auto. apply Z.divide_refl. }
        pose proof (Z.mod_pos_bound (h + n) Int64.modulus ltac:(rep_lia)).
        destruct (Z_le_gt_dec B Int64.max_unsigned).
        { rewrite Z.mod_small by rep_lia. lia. }
        split; [| intros; lia]. change Int64.max_unsigned with (Int64.modulus - 1) in *. lia.
Qed.

Lemma body_count_free : semax_body Vprog G_alloc f_count_free (_count_free, cm_free_spec).
Proof.
  start_function.
  apply semax_gvars_intro; intro gv. sep_apply (create_mem_mgr gv).
  change (CM o B h) with (count_CM o B h). change (CB o p n) with (count_CB o p n).
  unfold count_CM, count_CB. Intros peak.
  assert_PROP (isptr (offset_val (-8) p)) by entailer!.
  assert (Hp: p = offset_val 8 (offset_val (-8) p)).
  { destruct p; try contradiction. simpl. f_equal. rewrite Ptrofs.add_assoc, ptrofs_add_repr.
    rewrite Ptrofs.add_zero. reflexivity. }
  forget (offset_val (-8) p) as q. subst p. destruct q as [| | | | | b ofs]; try contradiction.
  forward. forward.
  assert (Ptrofs.sub (Ptrofs.add ofs (Ptrofs.repr 8))
            (Ptrofs.mul (Ptrofs.repr (Ctypes.sizeof tulong)) (ptrofs_of_int Signed (Int.repr 1))) = ofs) as ->.
  { replace (Ptrofs.mul (Ptrofs.repr (Ctypes.sizeof tulong)) (ptrofs_of_int Signed (Int.repr 1)))
      with (Ptrofs.repr 8) by reflexivity.
    rewrite Ptrofs.sub_add_opp, Ptrofs.add_assoc, Ptrofs.add_neg_zero, Ptrofs.add_zero. reflexivity. }
  assert_PROP (malloc_compatible (8 + n) (Vptr b ofs)).
  { go_lower. sep_apply (malloc_token_local_facts Ews (tarray tuchar (8 + n)) (Vptr b ofs)). simpl sizeof.
    rewrite Z.mul_1_l, Z.max_r by lia. Intros. apply prop_right. auto. }
  destruct H6 as [Hal Hsz].
  forward_if.
  { apply test_eq_null_weak; [exact I |].
    sep_apply (data_at_memory_block Ews tulong (Vlong (Int64.repr n)) (Vptr b ofs)).
    apply sepcon_weak_valid_pointer1.
    apply (memory_block_weak_valid_pointer Ews (sizeof tulong) (Vptr b ofs) 8); simpl; auto; lia. }
  { simpl in H6. discriminate. }
  forward.
  assert_PROP (Vptr b (Ptrofs.add ofs (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_ints (Int.repr 0)))) =
               field_address tulong [] (Vptr b ofs)).
  { entailer!. rewrite field_compatible_field_address by auto. simpl. normalize. }
  forward. forward. rewrite sub64_repr.
  sep_apply (data_at_memory_block Ews tulong (Vlong (Int64.repr n)) (Vptr b ofs)). simpl sizeof.
  sep_apply (derives_refl' _ _ (eq_sym (memory_block_split8 Ews b ofs n ltac:(lia) Hsz))).
  replace (memory_block Ews (8 + n) (Vptr b ofs))
    with (memory_block Ews (sizeof (tarray tuchar (8 + n))) (Vptr b ofs)) by (f_equal; simpl; lia).
  rewrite (memory_block_data_at_ Ews (tarray tuchar (8 + n)) (Vptr b ofs)).
  2: { apply malloc_compatible_field_compatible; auto.
       simpl. rewrite Z.max_r by lia. split; auto. lia. }
  forward_call (tarray tuchar (8 + n), Vptr b ofs, gv).
  { rewrite if_false by discriminate. cancel. }
  forward. change (CM o B (h - n)) with (count_CM o B (h - n)). unfold count_CM. Exists peak.
  entailer!.
Qed.

(* the state main sets up: count.now = count.peak = 0 *)
Lemma count_CM_init : forall o B, 0 <= B ->
  data_at Tsh t_count (Vlong (Int64.repr 0), Vlong (Int64.repr 0)) o |-- count_CM o B 0.
Proof.
  intros. unfold count_CM. Exists 0. entailer!.
Qed.

(* what the harness's check reads *)
Lemma count_peak : forall o B h, count_CM o B h |--
  EX peak: Z, !! (peak <= B) && (data_at Tsh t_count (Vlong (Int64.repr h), Vlong (Int64.repr peak)) o * TT).
Proof.
  intros. unfold count_CM. Intros peak. Exists peak. entailer!.
Qed.

Lemma alloc_res_memory_oneshot_ok :
  semax_body Vprog G_alloc f_count_alloc (_count_alloc, cm_alloc_spec) /\
  semax_body Vprog G_alloc f_count_free (_count_free, cm_free_spec).
Proof. split; [apply body_count_alloc | apply body_count_free]. Qed.
