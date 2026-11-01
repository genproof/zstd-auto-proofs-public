(* The proof obligations of the libc unit, proved by the body lemmas. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require Import Zstd.libc.code.
Require Import Zstd.proof.libc.LibcBodies.
Require Import Zstd.proof.libc.LibcOk.

Lemma body_memset : semax_body Vprog Gprog f_memset memset_spec.
Proof.
  start_function.
  rewrite memory_block_data_at__tarray_tuchar_eq by rep_lia.
  forward.
  forward_for_simple_bound n
    (EX i: Z,
     PROP () LOCAL (temp _p p; temp _s p; temp _c (Vint (Int.repr b)); temp _n (Vlong (Int64.repr n)))
     SEP (data_at sh (tarray tuchar n) (Zrepeat (Vint (Int.repr b)) i ++ Zrepeat Vundef (n - i)) p)).
  - entailer!. change (Zrepeat (Vint (Int.repr b)) 0) with (@nil val). rewrite app_nil_l. cancel.
  - forward.
    entailer!.
    assert (Int.zero_ext 8 (Int.repr b) = Int.repr b) as Hz
      by (apply zero_ext_inrange; rewrite Int.unsigned_repr by rep_lia; simpl; rep_lia).
    rewrite !Hz. apply derives_refl'. f_equal. list_solve.
  - forward. entailer!.
    apply derives_refl'. f_equal. list_solve.
Qed.

Lemma tc_val_tuchar_Znth: forall (bs: list val) i, Forall (tc_val tuchar) bs -> 0 <= i < Zlength bs ->
  exists x, Znth i bs = Vint x /\ Int.unsigned x <= Byte.max_unsigned.
Proof.
  intros. eapply Forall_Znth in H; [| exact H0].
  destruct (Znth i bs); try contradiction. exists i0. simpl in H. split; auto.
Qed.

Lemma data_at_tuchar_len: forall {cs: compspecs} sh n v p, 0 <= n ->
  data_at sh (tarray tuchar n) v p |-- !! (n <= Int64.max_unsigned).
Proof.
  intros. assert_PROP (isptr p) by entailer!. destruct p; try contradiction.
  sep_apply data_at_strict_range. Intros. apply prop_right.
  pose proof (Ptrofs.unsigned_range i). simpl sizeof in H1. rewrite Z.max_r in H1 by lia. rep_lia.
Qed.

Lemma body_memcmp : semax_body Vprog Gprog f_memcmp memcmp_spec.
Proof.
  start_function.
  forward. forward.
  assert_PROP (n <= Int64.max_unsigned) by (sep_apply data_at_tuchar_len; [rep_lia | entailer!]).
  forward_for_simple_bound n
    (EX i: Z,
     PROP () LOCAL (temp _a p1; temp _b p2; temp _n (Vlong (Int64.repr n)))
     SEP (data_at sh1 (tarray tuchar n) bs1 p1; data_at sh2 (tarray tuchar n) bs2 p2)).
  - entailer!.
  - cbv beta. forward.
    { entailer!. eapply Forall_Znth in H1; [exact H1 | lia]. }
    forward.
    { entailer!. eapply Forall_Znth in H2; [exact H2 | lia]. }
    forward_if.
    + forward. 
      forward.
      forward.
      all: revert H6 H7; destruct (Znth i bs2); intros; try contradiction;
        destruct (Znth i bs1); try contradiction; simpl in H6, H7; simpl.
      all: entailer!.
      { rewrite !Int.signed_eq_unsigned by rep_lia. rep_lia. }
      { match goal with |- context [Vint (Int.sub ?a ?b)] => Exists (Int.sub a b) end. entailer!. }
    + forward. entailer!.
  - forward. Exists Int.zero. entailer!.
Qed.

Lemma exists_bool: forall b: bool, {c: bool | c = b}.
Proof. intros; exists b; auto. Qed.

Lemma body_calloc : semax_body Vprog Gprog f_calloc calloc_spec.
Proof.
  start_function.
  destruct (exists_bool (negb (Z.eqb size 0) && (Int64.max_unsigned / size <? nmemb))) as [ovf Hovf].
  forward_if (temp _t'1 (Val.of_bool ovf)).
  - forward. entailer!.
    assert (size <> 0) by (intro; subst; contradiction).
    rewrite (proj2 (Z.eqb_neq _ _) H2). rewrite andb_true_l.
    unfold Int64.divu, Int64.cmpu. rewrite Int64.ltu_not.
    change (Int64.unsigned (Int64.repr (-1))) with Int64.max_unsigned.
    rewrite !Int64.unsigned_repr by rep_lia.
    assert (0 <= Int64.max_unsigned / size <= Int64.max_unsigned)
      by (split; [apply Z.div_pos; rep_lia | apply Z.div_le_upper_bound; rep_lia]).
    unfold Int64.ltu. rewrite !Int64.unsigned_repr by rep_lia.
    unfold Int64.eq. rewrite !Int64.unsigned_repr by rep_lia.
    destruct (zlt nmemb (Int64.max_unsigned / size)); destruct (zeq nmemb (Int64.max_unsigned / size));
      destruct (Int64.max_unsigned / size <? nmemb) eqn:E;
      try (apply Z.ltb_lt in E || apply Z.ltb_ge in E); try lia; reflexivity.
  - forward. entailer!.
    apply (f_equal Int64.unsigned) in H1. rewrite Int64.unsigned_repr in H1 by rep_lia.
    rewrite H1. reflexivity.
  - forward_if.
    + forward. Exists nullval. entailer!.
    + destruct ovf; [inv H1|]. symmetry in Hovf. apply andb_false_iff in Hovf.
      assert (Htot: 0 <= nmemb * size <= Int64.max_unsigned).
      { split; [apply Z.mul_nonneg_nonneg; lia|].
        destruct (Z.eq_dec size 0) as [Hz|Hnz]; [subst; rep_lia|].
        destruct Hovf as [Hz|Hlt].
        - apply negb_false_iff, Z.eqb_eq in Hz. lia.
        - apply Z.ltb_ge in Hlt.
          pose proof (Z.mul_div_le Int64.max_unsigned size ltac:(lia)).
          pose proof (Z.mul_le_mono_nonneg_r nmemb (Int64.max_unsigned / size) size ltac:(lia) Hlt). lia. }
      forward.
      replace (Int64.mul (Int64.repr nmemb) (Int64.repr size)) with (Int64.repr (nmemb * size))
        by (unfold Int64.mul; rewrite !Int64.unsigned_repr by rep_lia; auto).
      forward_call (tarray tuchar (nmemb * size), gv).
      { rewrite sizeof_tarray_tuchar by lia. rep_lia. }
      Intros p.
      forward_if (PROP () LOCAL (temp _p p)
        SEP (mem_mgr gv; if eq_dec p nullval then emp
             else malloc_token Ews (tarray tuchar (nmemb * size)) p *
                  data_at Ews (tarray tuchar (nmemb * size)) (Zrepeat (Vint Int.zero) (nmemb * size)) p)).
      * destruct (eq_dec p nullval); [subst; entailer! | entailer!].
      * rewrite if_false by auto. Intros.
        forward_for_simple_bound (nmemb * size)
          (EX i: Z, PROP () LOCAL (temp _p p; temp _total (Vlong (Int64.repr (nmemb * size))))
           SEP (mem_mgr gv; malloc_token Ews (tarray tuchar (nmemb * size)) p;
                data_at Ews (tarray tuchar (nmemb * size))
                  (Zrepeat (Vint Int.zero) i ++ Zrepeat Vundef (nmemb * size - i)) p)).
        { entailer!. change (Zrepeat (Vint Int.zero) 0) with (@nil val). rewrite app_nil_l. cancel. }
        { forward. entailer!. apply derives_refl'. f_equal. list_solve. }
        rewrite if_false by auto. entailer!. apply derives_refl'. f_equal. list_solve.
      * forward. subst. rewrite if_true by auto. entailer!.
      * forward. Exists p. entailer!.
Qed.

Lemma addr_norm: forall b ofs si i, 0 <= i <= Int64.max_unsigned ->
  Vptr b (Ptrofs.add (Ptrofs.add ofs (Ptrofs.repr si))
                     (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_int64 (Int64.repr i)))) =
  offset_val (si + i) (Vptr b ofs).
Proof.
  intros. simpl offset_val. f_equal.
  rewrite Ptrofs.mul_commut, Ptrofs.mul_one. unfold Ptrofs.of_int64.
  rewrite Int64.unsigned_repr by lia. rewrite Ptrofs.add_assoc. f_equal.
  apply ptrofs_add_repr.
Qed.

Lemma offset_val_inj: forall b ofs x y,
  0 <= x -> 0 <= y -> Ptrofs.unsigned ofs + x < Ptrofs.modulus -> Ptrofs.unsigned ofs + y < Ptrofs.modulus ->
  offset_val x (Vptr b ofs) = offset_val y (Vptr b ofs) -> x = y.
Proof.
  intros. unfold offset_val in H3. injection H3 as H5.
  pose proof (Ptrofs.unsigned_range ofs).
  rewrite !Ptrofs.Z_mod_modulus_eq, !Ptrofs.unsigned_repr in H5 by rep_lia.
  rewrite !Z.mod_small in H5 by lia. lia.
Qed.

Lemma tuchar_valid_ptr: forall {cs: compspecs} sh N c p k, sepalg.nonidentity sh -> 0 <= k < N ->
  data_at sh (tarray tuchar N) c p |-- valid_pointer (offset_val k p).
Proof.
  intros. sep_apply data_at_memory_block. apply memory_block_valid_pointer; auto.
  rewrite sizeof_tarray_tuchar by lia. lia.
Qed.

Lemma fa_tuchar: forall {cs: compspecs} N p k, field_compatible (tarray tuchar N) nil p -> 0 <= k < N ->
  field_address (tarray tuchar N) (SUB k) p = offset_val k p.
Proof.
  intros. rewrite field_address_offset by auto with field_compatible. simpl. f_equal. lia.
Qed.

Lemma addr_norm_sub1: forall b ofs si j, 1 <= j <= Int64.max_unsigned ->
  Vptr b (Ptrofs.add (Ptrofs.add ofs (Ptrofs.repr si))
     (Ptrofs.mul (Ptrofs.repr 1)
        (Ptrofs.of_int64 (Int64.sub (Int64.repr j) (Int64.repr (Int.signed (Int.repr 1))))))) =
  offset_val (si + (j - 1)) (Vptr b ofs).
Proof.
  intros. change (Int.signed (Int.repr 1)) with 1. rewrite sub64_repr. apply addr_norm. lia.
Qed.


(* Byte arrays mean the same at any two compspecs (no composite type involved). *)
Definition libc_cce (cs1 cs2: compspecs) : change_composite_env cs1 cs2 :=
  {| coeq := cs_preserve_env cs1 cs2;
     coeq_consistent := cs_preserve_env_consistent cs1 cs2 _ eq_refl;
     coeq_complete := cs_preserve_completeness cs1 cs2 _ eq_refl |}.

Lemma data_at_tuchar_cs: forall (cs1 cs2: compspecs) sh n (v: list val) p,
  @data_at cs1 sh (tarray tuchar n) v p = @data_at cs2 sh (tarray tuchar n) v p.
Proof.
  intros. apply equal_f.
  exact (@data_at_change_composite _ _ (libc_cce cs1 cs2) sh (tarray tuchar n) v v (JMeq_refl v) eq_refl).
Qed.

Lemma data_at__tuchar_cs: forall (cs1 cs2: compspecs) sh n p,
  @data_at_ cs1 sh (tarray tuchar n) p = @data_at_ cs2 sh (tarray tuchar n) p.
Proof. intros. rewrite (@data_at__change_composite _ _ (libc_cce cs1 cs2)); auto. Qed.

Lemma malloc_token_tuchar_cs: forall (cs1 cs2: compspecs) sh n p,
  @malloc_token cs1 sh (tarray tuchar n) p = @malloc_token cs2 sh (tarray tuchar n) p.
Proof. intros. rewrite (@malloc_token_change_composite _ _ (libc_cce cs1 cs2)); auto. Qed.




Lemma sub_memset_proof: funspec_sub (snd memset_spec) (snd memset_spec_Zstd).
Proof.
  apply NDsubsume_subsume; [split; reflexivity|].
  split; [split; reflexivity|].
  intros [[[sh p] b] n] [g args]. simpl.
  Exists (sh, p, b, n) (@emp mpred _ _). rewrite emp_sepcon. simpl.
  rewrite (data_at_tuchar_cs Zstd.units.Zstd.CS CompSpecs).
  apply andp_right; [apply andp_left2; auto|].
  apply prop_right; intros rho'; rewrite emp_sepcon; apply andp_left2; auto.
Qed.

Lemma sub_calloc_proof: funspec_sub (snd calloc_spec) (snd calloc_spec_Zstd).
Proof.
  apply NDsubsume_subsume; [split; reflexivity|].
  split; [split; reflexivity|].
  intros [[nmemb size] gv] [g args]. simpl.
  Exists (nmemb, size, gv) (@emp mpred _ _). rewrite emp_sepcon. simpl.
  apply andp_right; [apply andp_left2; auto|].
  apply prop_right; intros rho'; rewrite emp_sepcon; apply andp_left2.
  apply exp_derives; intros p.
  rewrite (data_at_tuchar_cs Zstd.units.Zstd.CS CompSpecs),
          (malloc_token_tuchar_cs Zstd.units.Zstd.CS CompSpecs). auto.
Qed.

(* memcpy and memmove: libc.c's byte loops (port to QuickProof v0.1.0-beta.1; docs/port-beta/README.md) *)

(* A defined byte (byte_val) is an unsigned char value: the byte loops' loads type-check. *)
Lemma byte_val_is_int: forall v, byte_val v -> is_int I8 Unsigned v.
Proof. intros v [z [Hz ->]]. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. Qed.

Lemma byte_val_Znth_is_int: forall (l: list val) i, Forall byte_val l -> 0 <= i < Zlength l ->
  is_int I8 Unsigned (Znth i l).
Proof. intros. apply byte_val_is_int. eapply Forall_Znth in H; eauto. Qed.

Lemma body_memcpy : semax_body Vprog Gprog f_memcpy memcpy_bytes_spec.
Proof.
  start_function.
  set (n := Zlength l).
  assert (0 <= n) by (subst n; apply Zlength_nonneg).
  forward. forward.
  forward_loop
    (EX i: Z,
      PROP (0 <= i <= n)
      LOCAL (temp _i (Vlong (Int64.repr i)); temp _d dst; temp _s src; temp _dest dst;
             temp _n (Vlong (Int64.repr n)))
      SEP (data_at shs (tarray tuchar n) l src;
           data_at shd (tarray tuchar n) (sublist 0 i l ++ Zrepeat Vundef (n - i)) dst))
    break: (PROP ()
      LOCAL (temp _dest dst)
      SEP (data_at shs (tarray tuchar n) l src;
           data_at shd (tarray tuchar n) l dst)).
  - forward. Exists 0. entailer!. simpl app. apply derives_refl.
  - Intros i.
    forward_if.
    + forward.
      { entailer!. apply byte_val_Znth_is_int; auto; lia. }
      forward.
      forward.
      Exists (i+1). entailer!.
      apply derives_refl'. f_equal. list_solve.
    + forward. entailer!.
      assert (i = Zlength l) by lia. subst i.
      rewrite sublist_same, Z.sub_diag by lia. simpl. rewrite app_nil_r. apply derives_refl.
  - forward.
Qed.

(* Two memory blocks whose shares overlap cannot overlap (data_at_conflict_glb for memory blocks). *)
Lemma memory_block_conflict_glb (sh1 sh2: share) (n1 n2: Z) (p1 p2: val) :
  sepalg.nonidentity (Share.glb sh1 sh2) ->
  address_conflict.pointer_range_overlap p1 n1 p2 n2 ->
  memory_block sh1 n1 p1 * memory_block sh2 n2 p2 |-- FF.
Proof.
  intros.
  pose (sh := Share.glb sh1 sh2).
  assert (sepalg.join sh (Share.glb sh1 (Share.comp sh)) sh1). {
    hnf. rewrite (Share.glb_commute sh1), <- Share.glb_assoc, Share.comp2.
    rewrite Share.glb_commute, Share.glb_bot.
    split; auto.
    rewrite Share.distrib2, Share.comp1.
    rewrite Share.glb_commute, Share.glb_top.
    unfold sh. rewrite Share.lub_commute, Share.lub_absorb. auto. }
  assert (sepalg.join sh (Share.glb sh2 (Share.comp sh)) sh2). {
    hnf. rewrite (Share.glb_commute sh2), <- Share.glb_assoc, Share.comp2.
    rewrite Share.glb_commute, Share.glb_bot.
    split; auto.
    rewrite Share.distrib2, Share.comp1.
    rewrite Share.glb_commute, Share.glb_top.
    unfold sh. rewrite Share.glb_commute.
    rewrite Share.lub_commute, Share.lub_absorb. auto. }
  rewrite <- (memory_block_share_join _ _ _ _ _ H1).
  rewrite <- (memory_block_share_join _ _ _ _ _ H2).
  assert (Hu: sepalg.nonunit sh) by (apply VST.msl.sepalg.nonidentity_nonunit; auto).
  eapply derives_trans with
    ((memory_block sh n1 p1 * memory_block sh n2 p2) *
     (memory_block (Share.glb sh1 (Share.comp sh)) n1 p1 *
      memory_block (Share.glb sh2 (Share.comp sh)) n2 p2))%logic.
  { cancel. }
  eapply derives_trans.
  { apply sepcon_derives; [| apply derives_refl].
    constructor. apply (VST.veric.mapsto_memory_block.memory_block_overlap sh p1 n1 p2 n2 Hu H0). }
  change predicates_hered.FF with (@FF mpred Nveric).
  rewrite FF_sepcon. auto.
Qed.

(* A readable and a writable byte array of length n cannot start i bytes apart, 0 < i < n. *)
Lemma uchar_arrays_overlap (shs shd: share) (n i: Z) (l1 l2: list val) (s: val) :
  readable_share shs -> writable_share shd -> 0 < i < n ->
  data_at shs (tarray tuchar n) l1 s * data_at shd (tarray tuchar n) l2 (offset_val i s) |-- FF.
Proof.
  intros.
  assert_PROP (field_compatible (tarray tuchar n) [] s) by entailer!.
  destruct s; try solve [destruct H2; contradiction].
  sep_apply (data_at_memory_block shs). sep_apply (data_at_memory_block shd).
  apply memory_block_conflict_glb.
  - apply nonempty_writable_glb; auto.
  - destruct H2 as (_ & _ & Hsz & _). unfold size_compatible in Hsz.
    simpl sizeof in *. rewrite Z.max_r in * by lia.
    pose proof (Ptrofs.unsigned_range i0).
    assert (Hu: Ptrofs.unsigned (Ptrofs.add i0 (Ptrofs.repr i)) = Ptrofs.unsigned i0 + i).
    { rewrite Ptrofs.add_unsigned, (Ptrofs.unsigned_repr i), Ptrofs.unsigned_repr; rep_lia. }
    exists (b, Ptrofs.unsigned (Ptrofs.add i0 (Ptrofs.repr i))), (b, Ptrofs.unsigned i0).
    split; [reflexivity | split; [reflexivity |]].
    exists (b, Ptrofs.unsigned (Ptrofs.add i0 (Ptrofs.repr i))). simpl. lia.
Qed.

Lemma uchar_array_valid_pointer (sh: share) (n i: Z) (l: list val) (p: val) :
  readable_share sh -> 0 <= i < n ->
  data_at sh (tarray tuchar n) l p |-- valid_pointer (offset_val i p).
Proof.
  intros. eapply derives_trans; [apply data_at_memory_block |].
  simpl sizeof. rewrite Z.max_r by lia.
  apply memory_block_valid_pointer; [lia | apply readable_nonidentity; auto].
Qed.


(* memmove within one array c: the contents during the backward loop (the last n - i bytes moved) and
   during the forward loop (the first i bytes moved). *)
Lemma mm_back_Znth: forall (c: list val) N si di n i,
  Zlength c = N -> 0 <= si -> si < di -> di + n <= N -> si + n <= N -> 0 < i <= n ->
  Znth (si + (i - 1)) (sublist 0 (di + i) c ++ sublist (si + i) (si + n) c ++ sublist (di + n) N c) =
  Znth (i - 1) (sublist si (si + n) c).
Proof. intros. list_solve. Qed.

Lemma mm_back_step: forall (c: list val) N si di n i,
  Zlength c = N -> 0 <= si -> si < di -> di + n <= N -> si + n <= N -> 0 < i <= n ->
  upd_Znth (di + (i - 1)) (sublist 0 (di + i) c ++ sublist (si + i) (si + n) c ++ sublist (di + n) N c)
    (Znth (si + (i - 1)) (sublist 0 (di + i) c ++ sublist (si + i) (si + n) c ++ sublist (di + n) N c)) =
  sublist 0 (di + (i - 1)) c ++ sublist (si + (i - 1)) (si + n) c ++ sublist (di + n) N c.
Proof. intros. list_solve. Qed.

Lemma mm_fwd_Znth: forall (c: list val) N si di n i,
  Zlength c = N -> 0 <= si -> 0 <= di -> di + n <= N -> si + n <= N -> (di <= si \/ si + n <= di) -> 0 <= i < n ->
  Znth (si + i) (sublist 0 di c ++ sublist si (si + i) c ++ sublist (di + i) N c) =
  Znth i (sublist si (si + n) c).
Proof. intros. destruct H5; list_solve. Qed.

Lemma mm_fwd_step: forall (c: list val) N si di n i,
  Zlength c = N -> 0 <= si -> 0 <= di -> di + n <= N -> si + n <= N -> (di <= si \/ si + n <= di) -> 0 <= i < n ->
  upd_Znth (di + i) (sublist 0 di c ++ sublist si (si + i) c ++ sublist (di + i) N c)
    (Znth (si + i) (sublist 0 di c ++ sublist si (si + i) c ++ sublist (di + i) N c)) =
  sublist 0 di c ++ sublist si (si + (i + 1)) c ++ sublist (di + (i + 1)) N c.
Proof. intros. destruct H5; list_solve. Qed.

Lemma mm_back_is_int: forall (c: list val) N si di n i,
  Zlength c = N -> 0 <= si -> si < di -> di + n <= N -> si + n <= N -> 0 < i <= n ->
  Forall byte_val (sublist si (si + n) c) ->
  is_int I8 Unsigned
    (Znth (si + (i - 1)) (sublist 0 (di + i) c ++ sublist (si + i) (si + n) c ++ sublist (di + n) N c)).
Proof.
  intros. rewrite mm_back_Znth by lia. apply byte_val_Znth_is_int; auto. rewrite Zlength_sublist; lia.
Qed.

Lemma mm_fwd_is_int: forall (c: list val) N si di n i,
  Zlength c = N -> 0 <= si -> 0 <= di -> di + n <= N -> si + n <= N -> (di <= si \/ si + n <= di) -> 0 <= i < n ->
  Forall byte_val (sublist si (si + n) c) ->
  is_int I8 Unsigned (Znth (si + i) (sublist 0 di c ++ sublist si (si + i) c ++ sublist (di + i) N c)).
Proof.
  intros. rewrite mm_fwd_Znth with (n := n) by lia. apply byte_val_Znth_is_int; auto. rewrite Zlength_sublist; lia.
Qed.

Lemma body_memmove : semax_body Vprog Gprog f_memmove memmove_spec.
Proof.
  start_function.
  destruct a as [shs shd s d n bs | sh p N c si di n]; simpl in H |- *.
  - destruct H as (SHs & SHd & Hlen & Hn & Hbs). Intros.
    assert (0 <= n) by (subst n; apply Zlength_nonneg).
    forward. forward. forward.
    forward_loop
      (EX i: Z,
        PROP (1 <= i <= Z.max 1 n)
        LOCAL (temp _i (Vlong (Int64.repr i)); temp _backwards (Vint (Int.repr 0));
               temp _d d; temp _s s; temp _dest d; temp _n (Vlong (Int64.repr n)))
        SEP (data_at shs (tarray tuchar n) bs s; data_at_ shd (tarray tuchar n) d))
      break: (PROP ()
        LOCAL (temp _backwards (Vint (Int.repr 0));
               temp _d d; temp _s s; temp _dest d; temp _n (Vlong (Int64.repr n)))
        SEP (data_at shs (tarray tuchar n) bs s; data_at_ shd (tarray tuchar n) d)).
    + forward. Exists 1. entailer!.
    + Intros i.
      forward_if.
      * forward_if.
        -- apply denote_tc_test_eq_split.
           ++ apply sepcon_valid_pointer1. apply uchar_array_valid_pointer; auto; lia.
           ++ apply sepcon_valid_pointer2. auto with valid_pointer.
        -- (* s + i == d: the two buffers would overlap *)
           eapply semax_pre; [| apply semax_ff]. go_lower.
           assert_PROP (isptr s) by entailer!. destruct s; try contradiction. subst d. simpl.
           rewrite data_at__eq, Ptrofs.mul_commut, Ptrofs.mul_one. unfold Ptrofs.of_int64.
           rewrite Int64.unsigned_repr by rep_lia.
           change (Vptr b (Ptrofs.add i0 (Ptrofs.repr i))) with (offset_val i (Vptr b i0)).
           apply uchar_arrays_overlap; auto. lia.
        -- forward. Exists (i+1). entailer!.
      * forward. entailer!.
    + forward_if
        (PROP ()
         LOCAL (temp _dest d)
         SEP (data_at shs (tarray tuchar n) bs s;
              data_at shd (tarray tuchar n) bs d)).
      * (* backwards = 0 *) contradiction.
      * forward_loop
          (EX i: Z,
            PROP (0 <= i <= n)
            LOCAL (temp _i__2 (Vlong (Int64.repr i)); temp _d d; temp _s s; temp _dest d;
                   temp _n (Vlong (Int64.repr n)))
            SEP (data_at shs (tarray tuchar n) bs s;
                 data_at shd (tarray tuchar n)
                   (sublist 0 i bs ++ Zrepeat Vundef (n - i)) d))
          break: (PROP ()
            LOCAL (temp _dest d)
            SEP (data_at shs (tarray tuchar n) bs s;
                 data_at shd (tarray tuchar n) bs d)).
        -- forward. Exists 0. entailer!. simpl app. apply derives_refl.
        -- Intros i.
           forward_if.
           ++ forward.
              { entailer!. apply byte_val_Znth_is_int; auto; lia. }
              forward.
              forward.
              Exists (i+1). entailer!.
              apply derives_refl'. f_equal. list_solve.
           ++ forward. entailer!.
              assert (i = Zlength bs) by lia. subst i.
              rewrite sublist_same, Z.sub_diag by lia. simpl. rewrite app_nil_r. apply derives_refl.
      * forward.
  - destruct H as (SH & Hlen & Hn0 & Hsi & Hsin & Hdi & Hdin & Hn & Hbs).
    assert_PROP (isptr p) by entailer!. destruct p as [| | | | | b ofs]; try contradiction.
    assert_PROP (Ptrofs.unsigned ofs + N < Ptrofs.modulus).
    { sep_apply data_at_strict_range. simpl sizeof. rewrite Z.max_r by lia. entailer!. }
    set (q := Vptr b ofs).
    set (ov := andb (si <? di) (di <? si + n)).
    forward. forward. forward.
    forward_loop
      (EX i: Z,
        PROP (1 <= i <= Z.max 1 n; forall j: Z, (1 <= j < i -> si + j <> di)%Z)
        LOCAL (temp _i (Vlong (Int64.repr i)); temp _backwards (Vint (Int.repr 0));
               temp _d (offset_val di q); temp _s (offset_val si q); temp _dest (offset_val di q);
               temp _n (Vlong (Int64.repr n)))
        SEP (data_at sh (tarray tuchar N) c q))
      break: (PROP ()
        LOCAL (temp _backwards (Vint (Int.repr (if ov then 1 else 0)));
               temp _d (offset_val di q); temp _s (offset_val si q); temp _dest (offset_val di q);
               temp _n (Vlong (Int64.repr n)))
        SEP (data_at sh (tarray tuchar N) c q)).
    + forward. Exists 1. entailer!.
    + Intros i.
      forward_if.
      * forward_if.
        -- rewrite addr_norm by rep_lia. apply denote_tc_test_eq_split.
           ++ apply (tuchar_valid_ptr sh (Zlength c) c q (si+i));
                [apply readable_nonidentity, writable_readable; auto | lia].
           ++ apply (tuchar_valid_ptr sh (Zlength c) c q di);
                [apply readable_nonidentity, writable_readable; auto | lia].
        -- assert (Heq: si + i = di).
           { rewrite addr_norm in H4 by rep_lia. apply (offset_val_inj b ofs); try lia. exact H4. }
           assert (Hov: ov = true) by (unfold ov; apply andb_true_intro; split; apply Z.ltb_lt; lia).
           forward. forward. rewrite Hov. entailer!.
        -- assert (Hne: si + i <> di).
           { intro Heq. apply H4. rewrite addr_norm by rep_lia. rewrite Heq. reflexivity. }
           assert (H2': forall j, 1 <= j < i+1 -> si + j <> di)
             by (intros j Hj; destruct (Z.eq_dec j i); [subst; auto | apply H2; lia]).
           forward. Exists (i+1). entailer!.
      * assert (Hov: ov = false).
        { unfold ov. destruct (si <? di) eqn:E1, (di <? si + n) eqn:E2; simpl; auto.
          apply Z.ltb_lt in E1, E2. exfalso. apply (H2 (di - si)); lia. }
        forward. rewrite Hov. entailer!.
    + forward_if
        (PROP () LOCAL (temp _dest (offset_val di q))
         SEP (data_at sh (tarray tuchar N) (mm_result c N si di n) q)).
      * destruct ov eqn:Eov; [| contradiction].
        unfold ov in Eov. apply andb_true_iff in Eov. destruct Eov as [E1 E2].
        apply Z.ltb_lt in E1, E2.
        forward_loop
          (EX i: Z,
            PROP (0 <= i <= n)
            LOCAL (temp _i__1 (Vlong (Int64.repr i)); temp _d (offset_val di q); temp _s (offset_val si q);
                   temp _dest (offset_val di q); temp _n (Vlong (Int64.repr n)))
            SEP (data_at sh (tarray tuchar N)
                   (sublist 0 (di + i) c ++ sublist (si + i) (si + n) c ++ sublist (di + n) N c) q))
          break: (PROP () LOCAL (temp _dest (offset_val di q))
            SEP (data_at sh (tarray tuchar N) (mm_result c N si di n) q)).
        -- forward. Exists n. entailer!. apply derives_refl'. f_equal. list_solve.
        -- Intros i. forward_if.
           ++ match goal with Hc: Int64.unsigned (Int64.repr 0) < Int64.unsigned (Int64.repr i) |- _ =>
                rewrite !Int64.unsigned_repr in Hc by rep_lia end.
              assert_PROP (Vptr b (Ptrofs.add (Ptrofs.add ofs (Ptrofs.repr si)) (Ptrofs.mul (Ptrofs.repr 1)
                 (Ptrofs.of_int64 (Int64.sub (Int64.repr i) (Int64.repr (Int.signed (Int.repr 1)))))))
                 = field_address (tarray tuchar N) (SUB (si + (i - 1))) q) as Hfs.
              { entailer!. rewrite addr_norm by rep_lia. rewrite fa_tuchar; auto; lia. }
              assert_PROP (Vptr b (Ptrofs.add (Ptrofs.add ofs (Ptrofs.repr di)) (Ptrofs.mul (Ptrofs.repr 1)
                 (Ptrofs.of_int64 (Int64.sub (Int64.repr i) (Int64.repr (Int.signed (Int.repr 1)))))))
                 = field_address (tarray tuchar N) (SUB (di + (i - 1))) q) as Hfd.
              { entailer!. rewrite addr_norm by rep_lia. rewrite fa_tuchar; auto; lia. }
              forward.
              { entailer!. apply (mm_back_is_int c (Zlength c) si di n i); auto; lia. }
              forward.
              forward.
              Exists (i - 1). entailer!.
              unfold data_at. apply derives_refl'. f_equal. apply mm_back_step; lia.
           ++ match goal with Hc: Int64.unsigned (Int64.repr 0) >= Int64.unsigned (Int64.repr i) |- _ =>
                rewrite !Int64.unsigned_repr in Hc by rep_lia end.
              forward. entailer!.
              assert (i = 0) by lia. subst i. rewrite !Z.add_0_r. unfold mm_result. apply derives_refl.
      * destruct ov eqn:Eov.
        { exfalso. apply Int.one_not_zero. assumption. }
        assert (Hdis: di <= si \/ si + n <= di).
        { unfold ov in Eov. destruct (Z.le_gt_cases di si); [left; auto | right].
          destruct (Z.le_gt_cases (si + n) di); auto.
          assert (E1: (si <? di) = true) by (apply Z.ltb_lt; lia).
          assert (E2: (di <? si + n) = true) by (apply Z.ltb_lt; lia).
          rewrite E1, E2 in Eov. discriminate. }
        forward_loop
          (EX i: Z,
            PROP (0 <= i <= n)
            LOCAL (temp _i__2 (Vlong (Int64.repr i)); temp _d (offset_val di q); temp _s (offset_val si q);
                   temp _dest (offset_val di q); temp _n (Vlong (Int64.repr n)))
            SEP (data_at sh (tarray tuchar N)
                   (sublist 0 di c ++ sublist si (si + i) c ++ sublist (di + i) N c) q))
          break: (PROP () LOCAL (temp _dest (offset_val di q))
            SEP (data_at sh (tarray tuchar N) (mm_result c N si di n) q)).
        -- forward. Exists 0. entailer!. apply derives_refl'. f_equal. list_solve.
        -- Intros i. forward_if.
           ++ assert_PROP (Vptr b (Ptrofs.add (Ptrofs.add ofs (Ptrofs.repr si)) (Ptrofs.mul (Ptrofs.repr 1)
                 (Ptrofs.of_int64 (Int64.repr i))))
                 = field_address (tarray tuchar N) (SUB (si + i)) q) as Hfs.
              { entailer!. rewrite addr_norm by rep_lia. rewrite fa_tuchar; auto; lia. }
              assert_PROP (Vptr b (Ptrofs.add (Ptrofs.add ofs (Ptrofs.repr di)) (Ptrofs.mul (Ptrofs.repr 1)
                 (Ptrofs.of_int64 (Int64.repr i))))
                 = field_address (tarray tuchar N) (SUB (di + i)) q) as Hfd.
              { entailer!. rewrite addr_norm by rep_lia. rewrite fa_tuchar; auto; lia. }
              forward.
              { entailer!. apply (mm_fwd_is_int c (Zlength c) si di n i); auto; lia. }
              forward.
              forward.
              Exists (i + 1). entailer!.
              unfold data_at. apply derives_refl'. f_equal. apply (mm_fwd_step c (Zlength c) si di n i); lia.
           ++ forward. entailer!.
              assert (i = n) by lia. subst i. unfold mm_result. apply derives_refl.
      * forward.
Qed.

Lemma sub_memcpy_cs (cs: compspecs) : funspec_sub (snd (@memcpy_bytes_spec CompSpecs)) (snd (@memcpy_bytes_spec cs)).
Proof.
  apply NDsubsume_subsume; [split; reflexivity|].
  split; [split; reflexivity|].
  intros x gargs. destruct x as [[[[shs shd] src] dst] l]. destruct gargs as [g args]. simpl.
  Exists (shs, shd, src, dst, l) (@emp mpred _ _). rewrite emp_sepcon. simpl.
  rewrite (data_at_tuchar_cs cs CompSpecs), (data_at__tuchar_cs cs CompSpecs).
  apply andp_right; [apply andp_left2; auto|].
  apply prop_right; intros rho'; rewrite emp_sepcon; apply andp_left2.
  rewrite !(data_at_tuchar_cs cs CompSpecs). auto.
Qed.

Lemma sub_memcpy_proof (cs: compspecs) : funspec_sub (snd (@memcpy_bytes_spec CompSpecs)) (snd (@memcpy_spec cs)).
Proof. eapply funspec_sub_trans; [apply sub_memcpy_cs | apply memcpy_sub_typed]. Qed.

Lemma sub_memmove_proof (cs: compspecs) : funspec_sub (snd (@memmove_spec CompSpecs)) (snd (@memmove_spec cs)).
Proof.
  apply NDsubsume_subsume; [split; reflexivity|].
  split; [split; reflexivity|].
  intros a gargs. destruct gargs as [g args]. simpl.
  Exists a (@emp mpred _ _). rewrite emp_sepcon. simpl.
  assert (EP: @mm_pre cs a = @mm_pre CompSpecs a)
    by (destruct a; simpl; rewrite ?(data_at_tuchar_cs cs CompSpecs), ?(data_at__tuchar_cs cs CompSpecs); reflexivity).
  assert (EQ: @mm_post cs a = @mm_post CompSpecs a)
    by (destruct a; simpl; rewrite ?(data_at_tuchar_cs cs CompSpecs), ?(data_at__tuchar_cs cs CompSpecs); reflexivity).
  rewrite EP.
  apply andp_right; [apply andp_left2; auto|].
  apply prop_right; intros rho'. rewrite emp_sepcon. apply andp_left2. rewrite EQ. auto.
Qed.

Lemma libc_bodies : LibcBodies.
Proof.
  constructor.
  - exact body_memset.
  - exact body_memcmp.
  - exact body_calloc.
  - exact body_memcpy.
  - exact body_memmove.
  - exact sub_memset_proof.
  - exact sub_calloc_proof.
  - exact sub_memcpy_proof.
  - exact sub_memmove_proof.
Qed.
