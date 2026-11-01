(* Specifications of quickproof/libc/libc.c (memset, memcmp, calloc, memcpy, memmove).
   Stated for any compspecs: the decoder unit imports them at its own compspecs, the libc unit proves
   them at its own (the assembly relates the two with funspec_sub).  The decoder relies
   on them, so a change must keep every caller's proof working.
   Only cs-independent types appear (tarray tuchar n). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require Zstd.libc.code.

Definition _memset : ident := Zstd.libc.code._memset.
Definition _memcmp : ident := Zstd.libc.code._memcmp.
Definition _calloc : ident := Zstd.libc.code._calloc.
Definition _memcpy : ident := Zstd.libc.code._memcpy.
Definition _memmove : ident := Zstd.libc.code._memmove.

(* A defined byte: the only value that libc.c's memcpy and memmove, byte loops through unsigned char, can copy.
   (Before QuickProof v0.1.0-beta.1 the proof ran on a framework branch where memcpy and memmove were functions of
   the environment that copied any bytes, even never-written ones; docs/port-beta/README.md.) *)
Definition byte_val (v: val) : Prop := exists z, 0 <= z < 256 /\ v = Vint (Int.repr z).

(* The arguments of a memmove call, as the decoder's proofs state them:
   - mm_disjoint shs shd s d n bs: two separate ranges: s holds the n bytes bs, d is n writable bytes;
   - mm_within sh p N c si di n: ONE byte array p of N cells with contents c; the source is p + si, the
     destination p + di, both ranges of n bytes inside the array; they may overlap. *)
Inductive memmove_args : Type :=
| mm_disjoint (shs shd: share) (s d: val) (n: Z) (bs: list val)
| mm_within (sh: share) (p: val) (N: Z) (c: list val) (si di n: Z).

Definition mm_src (a: memmove_args) : val :=
  match a with mm_disjoint _ _ s _ _ _ => s | mm_within _ p _ _ si _ _ => offset_val si p end.
Definition mm_dst (a: memmove_args) : val :=
  match a with mm_disjoint _ _ _ d _ _ => d | mm_within _ p _ _ _ di _ => offset_val di p end.
Definition mm_len (a: memmove_args) : Z :=
  match a with mm_disjoint _ _ _ _ n _ => n | mm_within _ _ _ _ _ _ n => n end.
(* the shape, and: the moved bytes are defined *)
Definition mm_ok (a: memmove_args) : Prop :=
  match a with
  | mm_disjoint shs shd s d n bs =>
      readable_share shs /\ writable_share shd /\ Zlength bs = n /\ n <= Int64.max_unsigned /\
      Forall byte_val bs
  | mm_within sh p N c si di n =>
      writable_share sh /\ Zlength c = N /\ 0 <= n /\ 0 <= si /\ si + n <= N /\ 0 <= di /\ di + n <= N /\
      n <= Int64.max_unsigned /\ Forall byte_val (sublist si (si + n) c)
  end.

(* The array after the move: the bytes [di, di+n) replaced by the bytes [si, si+n) of the original. *)
Definition mm_result (c: list val) (N si di n: Z) : list val :=
  (sublist 0 di c ++ sublist si (si + n) c ++ sublist (di + n) N c)%list.

Section Specs.
Context {CS: compspecs}.

(* memset(p, b, n) with a byte value 0 <= b <= 255 (as the int argument) on n writable bytes.
   To zero a typed object t: memory_block from data_at_ (data_at__memory_block), then
   memset_zero_data_at below turns the n = sizeof t zero bytes into data_at sh t (zero_val t) p. *)
Definition memset_spec :=
  DECLARE _memset
  WITH sh: share, p: val, b: Z, n: Z
  PRE  [ tptr tvoid, tint, tulong ]
       PROP (writable_share sh; 0 <= b <= Byte.max_unsigned; 0 <= n <= Int64.max_unsigned)
       PARAMS (p; Vint (Int.repr b); Vlong (Int64.repr n))
       SEP (memory_block sh n p)
  POST [ tptr tvoid ]
       PROP () RETURN (p)
       SEP (data_at sh (tarray tuchar n) (Zrepeat (Vint (Int.repr b)) n) p).

(* memcmp(s1, s2, n) on two readable ranges of n defined bytes; returns some int. *)
Definition memcmp_spec :=
  DECLARE _memcmp
  WITH sh1: share, sh2: share, p1: val, p2: val, n: Z, bs1: list val, bs2: list val
  PRE  [ tptr tvoid, tptr tvoid, tulong ]
       PROP (readable_share sh1; readable_share sh2; Zlength bs1 = n; Zlength bs2 = n;
             Forall (tc_val tuchar) bs1; Forall (tc_val tuchar) bs2)
       PARAMS (p1; p2; Vlong (Int64.repr n))
       SEP (data_at sh1 (tarray tuchar n) bs1 p1; data_at sh2 (tarray tuchar n) bs2 p2)
  POST [ tint ] EX r: int,
       PROP () RETURN (Vint r)
       SEP (data_at sh1 (tarray tuchar n) bs1 p1; data_at sh2 (tarray tuchar n) bs2 p2).

(* calloc(nmemb, size): NULL, or nmemb*size zero bytes with their malloc_token (type tarray tuchar). *)
Definition calloc_spec :=
  DECLARE _calloc
  WITH nmemb: Z, size: Z, gv: globals
  PRE  [ tulong, tulong ]
       PROP (0 <= nmemb <= Int64.max_unsigned; 0 <= size <= Int64.max_unsigned)
       PARAMS (Vlong (Int64.repr nmemb); Vlong (Int64.repr size)) GLOBALS (gv)
       SEP (mem_mgr gv)
  POST [ tptr tvoid ] EX p: val,
       PROP () RETURN (p)
       SEP (mem_mgr gv;
            if eq_dec p nullval then emp
            else malloc_token Ews (tarray tuchar (nmemb * size)) p *
                 data_at Ews (tarray tuchar (nmemb * size)) (Zrepeat (Vint Int.zero) (nmemb * size)) p).

(* memcpy(dst, src, n) as libc.c implements it: a forward byte loop through unsigned char, so n defined bytes;
   the two SEP conjuncts make the ranges disjoint. *)
Definition memcpy_bytes_spec :=
  DECLARE _memcpy
  WITH shs: share, shd: share, src: val, dst: val, l: list val
  PRE  [ tptr tvoid, tptr tvoid, tulong ]
       PROP (readable_share shs; writable_share shd; Zlength l <= Int64.max_unsigned; Forall byte_val l)
       PARAMS (dst; src; Vlong (Int64.repr (Zlength l)))
       SEP (data_at shs (tarray tuchar (Zlength l)) l src; data_at_ shd (tarray tuchar (Zlength l)) dst)
  POST [ tptr tvoid ]
       PROP () RETURN (dst)
       SEP (data_at shs (tarray tuchar (Zlength l)) l src; data_at shd (tarray tuchar (Zlength l)) l dst).

(* An object of type t with value v whose sizeof t bytes are the defined bytes l, in both directions (the second
   needs t's alignment at the address). *)
Definition obj_bytes (t: type) (v: reptype t) (l: list val) : Prop :=
  Zlength l = sizeof t /\ Forall byte_val l /\
  (forall sh p, readable_share sh -> data_at sh t v p |-- data_at sh (tarray tuchar (sizeof t)) l p) /\
  (forall sh p, readable_share sh -> field_compatible t nil p ->
     data_at sh (tarray tuchar (sizeof t)) l p |-- data_at sh t v p).
Definition memcpy_ok (t: type) (v: reptype t) : Prop := exists l, obj_bytes t v l.

(* memcpy as the callers state it: the n = sizeof t bytes of an object of type t (instantiate tv := existT _ t v)
   whose bytes are defined (memcpy_ok); afterwards dst holds the same value.  Derived from memcpy_bytes_spec
   (memcpy_sub_typed below). *)
Definition memcpy_spec :=
  DECLARE _memcpy
  WITH shs: share, shd: share, src: val, dst: val, tv: {t: type & reptype t}
  PRE  [ tptr tvoid, tptr tvoid, tulong ]
       PROP (readable_share shs; writable_share shd; 0 <= sizeof (projT1 tv) <= Int64.max_unsigned;
             memcpy_ok (projT1 tv) (projT2 tv))
       PARAMS (dst; src; Vlong (Int64.repr (sizeof (projT1 tv))))
       SEP (data_at shs (projT1 tv) (projT2 tv) src; data_at_ shd (projT1 tv) dst)
  POST [ tptr tvoid ]
       PROP () RETURN (dst)
       SEP (data_at shs (projT1 tv) (projT2 tv) src; data_at shd (projT1 tv) (projT2 tv) dst).

Definition mm_pre (a: memmove_args) : mpred :=
  match a with
  | mm_disjoint shs shd s d n bs =>
      sepcon (data_at shs (tarray tuchar n) bs s) (data_at_ shd (tarray tuchar n) d)
  | mm_within sh p N c si di n => data_at sh (tarray tuchar N) c p
  end.
Definition mm_post (a: memmove_args) : mpred :=
  match a with
  | mm_disjoint shs shd s d n bs =>
      sepcon (data_at shs (tarray tuchar n) bs s) (data_at shd (tarray tuchar n) bs d)
  | mm_within sh p N c si di n => data_at sh (tarray tuchar N) (mm_result c N si di n) p
  end.

(* memmove(dst, src, n) as libc.c implements it: the n defined bytes at src end up at dst, also when the ranges
   overlap (backwards when dst starts inside the source range after its first byte). *)
Definition memmove_spec :=
  DECLARE _memmove
  WITH a: memmove_args
  PRE  [ tptr tvoid, tptr tvoid, tulong ]
       PROP (mm_ok a)
       PARAMS (mm_dst a; mm_src a; Vlong (Int64.repr (mm_len a)))
       SEP (mm_pre a)
  POST [ tptr tvoid ]
       PROP () RETURN (mm_dst a) SEP (mm_post a).

(* n zero bytes are mapsto_zeros n. *)
Lemma data_at_strict_range: forall sh t v b ofs,
  data_at sh t v (Vptr b ofs) |-- !! (Ptrofs.unsigned ofs + sizeof t < Ptrofs.modulus).
Proof.
  intros. sep_apply (data_at_data_at_ sh t v). rewrite data_at__memory_block.
  apply andp_left2. eapply derives_trans; [apply memory_block_local_facts|].
  apply prop_derives. unfold size_compatible'. tauto.
Qed.

Lemma byte_zero_mapsto_zeros: forall sh b ofs, readable_share sh ->
  data_at sh tuchar (Vint Int.zero) (Vptr b ofs) |-- mapsto_zeros 1 sh (Vptr b ofs).
Proof.
  intros.
  assert_PROP (Ptrofs.unsigned ofs + 1 < Ptrofs.modulus) by (sep_apply data_at_strict_range; entailer!).
  assert_PROP (field_compatible tuchar nil (Vptr b ofs)) by entailer!.
  rewrite <- (mapsto_data_at' sh tuchar (Vint Int.zero)) by auto.
  unfold mapsto, mapsto_zeros. simpl. rewrite if_true by auto.
  apply orp_left.
  - normalize. rewrite prop_true_andp by (pose proof (Ptrofs.unsigned_range ofs); lia).
    change (?A |-- predicates_sl.sepcon ?A predicates_sl.emp) with (A |-- sepcon A emp).
    rewrite sepcon_emp; auto.
  - normalize. discriminate.
Qed.

Lemma zero_bytes_mapsto_zeros: forall sh n p, readable_share sh -> 0 <= n ->
  data_at sh (tarray tuchar n) (Zrepeat (Vint Int.zero) n) p |-- mapsto_zeros n sh p.
Proof.
  intros sh n p Hsh Hn.
  assert_PROP (isptr p) by entailer!. destruct p; try contradiction. clear H.
  revert i. pattern n; apply natlike_ind; [ | | exact Hn]; clear n Hn.
  - intros ofs. change (Zrepeat (Vint Int.zero) 0) with (@nil val).
    rewrite data_at_tuchar_zero_array_eq by exact I. rewrite aggregate_pred.mapsto_zeros_zero. entailer!.
  - intros k Hk IH ofs.
    assert_PROP (Ptrofs.unsigned ofs + Z.succ k < Ptrofs.modulus)
      by (sep_apply data_at_strict_range; entailer!; simpl in *; rewrite Z.max_r in * by lia; lia).
    assert_PROP (field_compatible (tarray tuchar (Z.succ k)) nil (Vptr b ofs)) by entailer!.
    rewrite (split2_data_at_Tarray_tuchar sh (Z.succ k) 1) by (try rewrite Zlength_Zrepeat; lia).
    rewrite field_address0_offset by auto with field_compatible.
    autorewrite with sublist.
    replace (Z.succ k - 1) with k by lia.
    change (Zrepeat (Vint Int.zero) 1) with [Vint Int.zero].
    change (Tarray tuchar 1 noattr) with (tarray tuchar 1). rewrite data_at_tuchar_singleton_array_eq.
    simpl nested_field_offset.
    pose proof (Ptrofs.unsigned_range ofs).
    rewrite <- (Ptrofs.repr_unsigned ofs) at 3. replace (Z.succ k) with (1 + k) by lia.
    rewrite aggregate_pred.mapsto_zeros_split by lia. rewrite Ptrofs.repr_unsigned.
    apply sepcon_derives; [apply byte_zero_mapsto_zeros; auto |].
    simpl offset_val. unfold Ptrofs.add. rewrite (Ptrofs.unsigned_repr 1) by rep_lia.
    rewrite Z.add_comm. apply IH.
Qed.

(* memset(p, 0, sizeof t) zeroes a typed object: the zero bytes are data_at sh t (zero_val t). *)
Lemma memset_zero_data_at: forall sh t p,
  readable_share sh ->
  complete_legal_cosu_type t = true ->
  fully_nonvolatile (rank_type cenv_cs t) t = true ->
  field_compatible t nil p ->
  data_at sh (tarray tuchar (sizeof t)) (Zrepeat (Vint Int.zero) (sizeof t)) p |--
  data_at sh t (zero_val t) p.
Proof.
  intros. eapply derives_trans; [apply zero_bytes_mapsto_zeros; auto; pose proof (sizeof_pos t); lia |].
  apply mapsto_zero_data_at_zero; auto.
Qed.

End Specs.
