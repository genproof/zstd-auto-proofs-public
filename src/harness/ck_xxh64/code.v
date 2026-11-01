From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Module Info.
  Definition version := "3.15".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "x86".
  Definition model := "64".
  Definition abi := "standard".
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "harness/ck_xxh64.c".
  Definition normalized := true.
End Info.

Definition _ZSTD_XXH64 : ident := $"ZSTD_XXH64".
Definition ___builtin_ais_annot : ident := $"__builtin_ais_annot".
Definition ___builtin_annot : ident := $"__builtin_annot".
Definition ___builtin_annot_intval : ident := $"__builtin_annot_intval".
Definition ___builtin_bswap : ident := $"__builtin_bswap".
Definition ___builtin_bswap16 : ident := $"__builtin_bswap16".
Definition ___builtin_bswap32 : ident := $"__builtin_bswap32".
Definition ___builtin_bswap64 : ident := $"__builtin_bswap64".
Definition ___builtin_clz : ident := $"__builtin_clz".
Definition ___builtin_clzl : ident := $"__builtin_clzl".
Definition ___builtin_clzll : ident := $"__builtin_clzll".
Definition ___builtin_ctz : ident := $"__builtin_ctz".
Definition ___builtin_ctzl : ident := $"__builtin_ctzl".
Definition ___builtin_ctzll : ident := $"__builtin_ctzll".
Definition ___builtin_debug : ident := $"__builtin_debug".
Definition ___builtin_expect : ident := $"__builtin_expect".
Definition ___builtin_fabs : ident := $"__builtin_fabs".
Definition ___builtin_fabsf : ident := $"__builtin_fabsf".
Definition ___builtin_fmadd : ident := $"__builtin_fmadd".
Definition ___builtin_fmax : ident := $"__builtin_fmax".
Definition ___builtin_fmin : ident := $"__builtin_fmin".
Definition ___builtin_fmsub : ident := $"__builtin_fmsub".
Definition ___builtin_fnmadd : ident := $"__builtin_fnmadd".
Definition ___builtin_fnmsub : ident := $"__builtin_fnmsub".
Definition ___builtin_fsqrt : ident := $"__builtin_fsqrt".
Definition ___builtin_membar : ident := $"__builtin_membar".
Definition ___builtin_memcpy_aligned : ident := $"__builtin_memcpy_aligned".
Definition ___builtin_read16_reversed : ident := $"__builtin_read16_reversed".
Definition ___builtin_read32_reversed : ident := $"__builtin_read32_reversed".
Definition ___builtin_sel : ident := $"__builtin_sel".
Definition ___builtin_sqrt : ident := $"__builtin_sqrt".
Definition ___builtin_unreachable : ident := $"__builtin_unreachable".
Definition ___builtin_va_arg : ident := $"__builtin_va_arg".
Definition ___builtin_va_copy : ident := $"__builtin_va_copy".
Definition ___builtin_va_end : ident := $"__builtin_va_end".
Definition ___builtin_va_start : ident := $"__builtin_va_start".
Definition ___builtin_write16_reversed : ident := $"__builtin_write16_reversed".
Definition ___builtin_write32_reversed : ident := $"__builtin_write32_reversed".
Definition ___compcert_i64_dtos : ident := $"__compcert_i64_dtos".
Definition ___compcert_i64_dtou : ident := $"__compcert_i64_dtou".
Definition ___compcert_i64_sar : ident := $"__compcert_i64_sar".
Definition ___compcert_i64_sdiv : ident := $"__compcert_i64_sdiv".
Definition ___compcert_i64_shl : ident := $"__compcert_i64_shl".
Definition ___compcert_i64_shr : ident := $"__compcert_i64_shr".
Definition ___compcert_i64_smod : ident := $"__compcert_i64_smod".
Definition ___compcert_i64_smulh : ident := $"__compcert_i64_smulh".
Definition ___compcert_i64_stod : ident := $"__compcert_i64_stod".
Definition ___compcert_i64_stof : ident := $"__compcert_i64_stof".
Definition ___compcert_i64_udiv : ident := $"__compcert_i64_udiv".
Definition ___compcert_i64_umod : ident := $"__compcert_i64_umod".
Definition ___compcert_i64_umulh : ident := $"__compcert_i64_umulh".
Definition ___compcert_i64_utod : ident := $"__compcert_i64_utod".
Definition ___compcert_i64_utof : ident := $"__compcert_i64_utof".
Definition ___compcert_va_composite : ident := $"__compcert_va_composite".
Definition ___compcert_va_float64 : ident := $"__compcert_va_float64".
Definition ___compcert_va_int32 : ident := $"__compcert_va_int32".
Definition ___compcert_va_int64 : ident := $"__compcert_va_int64".
Definition _acc : ident := $"acc".
Definition _acc1 : ident := $"acc1".
Definition _acc2 : ident := $"acc2".
Definition _acc3 : ident := $"acc3".
Definition _acc4 : ident := $"acc4".
Definition _accn : ident := $"accn".
Definition _any_bytes : ident := $"any_bytes".
Definition _bytes : ident := $"bytes".
Definition _data : ident := $"data".
Definition _gp_assert : ident := $"gp_assert".
Definition _i : ident := $"i".
Definition _lane : ident := $"lane".
Definition _le : ident := $"le".
Definition _left : ident := $"left".
Definition _len : ident := $"len".
Definition _main : ident := $"main".
Definition _max : ident := $"max".
Definition _merge : ident := $"merge".
Definition _n : ident := $"n".
Definition _nondet_bytes : ident := $"nondet_bytes".
Definition _nondet_size : ident := $"nondet_size".
Definition _p : ident := $"p".
Definition _quickproof_malloc : ident := $"quickproof_malloc".
Definition _r : ident := $"r".
Definition _rotl : ident := $"rotl".
Definition _round64 : ident := $"round64".
Definition _seed : ident := $"seed".
Definition _size : ident := $"size".
Definition _upto : ident := $"upto".
Definition _value : ident := $"value".
Definition _x : ident := $"x".
Definition _xxh64 : ident := $"xxh64".
Definition _t'1 : ident := 128%positive.
Definition _t'10 : ident := 137%positive.
Definition _t'11 : ident := 138%positive.
Definition _t'12 : ident := 139%positive.
Definition _t'13 : ident := 140%positive.
Definition _t'14 : ident := 141%positive.
Definition _t'15 : ident := 142%positive.
Definition _t'16 : ident := 143%positive.
Definition _t'17 : ident := 144%positive.
Definition _t'18 : ident := 145%positive.
Definition _t'19 : ident := 146%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'20 : ident := 147%positive.
Definition _t'21 : ident := 148%positive.
Definition _t'22 : ident := 149%positive.
Definition _t'23 : ident := 150%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

Definition f_upto := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_max, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_value, tulong) :: (_t'2, tulong) :: (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1) (Evar _nondet_size (Tfunction nil tulong cc_default))
      nil)
    (Sset _value (Etempvar _t'1 tulong)))
  (Ssequence
    (Sifthenelse (Ebinop Olt (Etempvar _value tulong) (Etempvar _max tulong)
                   tint)
      (Sset _t'2 (Ecast (Etempvar _value tulong) tulong))
      (Sset _t'2 (Ecast (Etempvar _max tulong) tulong)))
    (Sreturn (Some (Etempvar _t'2 tulong)))))
|}.

Definition f_any_bytes := {|
  fn_return := (tptr tuchar);
  fn_callconv := cc_default;
  fn_params := ((_n, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_bytes, (tptr tuchar)) :: (_t'2, tint) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _quickproof_malloc (Tfunction (tulong :: nil) (tptr tvoid)
                                 cc_default)) ((Etempvar _n tulong) :: nil))
    (Sset _bytes (Etempvar _t'1 (tptr tvoid))))
  (Ssequence
    (Ssequence
      (Sifthenelse (Ebinop One (Etempvar _bytes (tptr tuchar))
                     (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                     tint)
        (Sset _t'2
          (Ecast
            (Ebinop One (Etempvar _n tulong) (Econst_int (Int.repr 0) tint)
              tint) tbool))
        (Sset _t'2 (Econst_int (Int.repr 0) tint)))
      (Sifthenelse (Etempvar _t'2 tint)
        (Scall None
          (Evar _nondet_bytes (Tfunction ((tptr tuchar) :: tulong :: nil)
                                tvoid cc_default))
          ((Etempvar _bytes (tptr tuchar)) :: (Etempvar _n tulong) :: nil))
        Sskip))
    (Sreturn (Some (Etempvar _bytes (tptr tuchar))))))
|}.

Definition f_rotl := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_x, tulong) :: (_r, tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop Oor
                 (Ebinop Oshl (Etempvar _x tulong) (Etempvar _r tint) tulong)
                 (Ebinop Oshr (Etempvar _x tulong)
                   (Ebinop Osub (Econst_int (Int.repr 64) tint)
                     (Etempvar _r tint) tint) tulong) tulong)))
|}.

Definition f_le := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr tuchar)) :: (_size, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_value, tulong) :: (_i, tint) :: (_t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Sset _value (Ecast (Econst_int (Int.repr 0) tint) tulong))
  (Ssequence
    (Ssequence
      (Sset _i
        (Ebinop Osub (Etempvar _size tint) (Econst_int (Int.repr 1) tint)
          tint))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Oge (Etempvar _i tint)
                         (Econst_int (Int.repr 0) tint) tint)
            Sskip
            Sbreak)
          (Ssequence
            (Sset _t'1
              (Ederef
                (Ebinop Oadd (Etempvar _p (tptr tuchar)) (Etempvar _i tint)
                  (tptr tuchar)) tuchar))
            (Sset _value
              (Ebinop Oor
                (Ebinop Oshl (Etempvar _value tulong)
                  (Econst_int (Int.repr 8) tint) tulong)
                (Etempvar _t'1 tuchar) tulong))))
        (Sset _i
          (Ebinop Osub (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
            tint))))
    (Sreturn (Some (Etempvar _value tulong)))))
|}.

Definition f_round64 := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_acc, tulong) :: (_lane, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1)
    (Evar _rotl (Tfunction (tulong :: tint :: nil) tulong cc_default))
    ((Ebinop Oadd (Etempvar _acc tulong)
       (Ebinop Omul (Etempvar _lane tulong)
         (Econst_long (Int64.repr (-4417276706812531889)) tulong) tulong)
       tulong) :: (Econst_int (Int.repr 31) tint) :: nil))
  (Sreturn (Some (Ebinop Omul (Etempvar _t'1 tulong)
                   (Econst_long (Int64.repr (-7046029288634856825)) tulong)
                   tulong))))
|}.

Definition f_merge := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_acc, tulong) :: (_accn, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1)
    (Evar _round64 (Tfunction (tulong :: tulong :: nil) tulong cc_default))
    ((Econst_int (Int.repr 0) tint) :: (Etempvar _accn tulong) :: nil))
  (Sreturn (Some (Ebinop Oadd
                   (Ebinop Omul
                     (Ebinop Oxor (Etempvar _acc tulong)
                       (Etempvar _t'1 tulong) tulong)
                     (Econst_long (Int64.repr (-7046029288634856825)) tulong)
                     tulong)
                   (Econst_long (Int64.repr (-8796714831421723037)) tulong)
                   tulong))))
|}.

Definition f_xxh64 := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr tuchar)) :: (_len, tulong) :: (_seed, tulong) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_acc, tulong) :: (_left, tulong) :: (_acc1, tulong) ::
               (_acc2, tulong) :: (_acc3, tulong) :: (_acc4, tulong) ::
               (_t'22, tulong) :: (_t'21, tulong) :: (_t'20, tulong) ::
               (_t'19, tulong) :: (_t'18, tulong) :: (_t'17, tulong) ::
               (_t'16, tulong) :: (_t'15, tulong) :: (_t'14, tulong) ::
               (_t'13, tulong) :: (_t'12, tulong) :: (_t'11, tulong) ::
               (_t'10, tulong) :: (_t'9, tulong) :: (_t'8, tulong) ::
               (_t'7, tulong) :: (_t'6, tulong) :: (_t'5, tulong) ::
               (_t'4, tulong) :: (_t'3, tulong) :: (_t'2, tulong) ::
               (_t'1, tulong) :: (_t'23, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Sset _acc
    (Ebinop Oadd (Etempvar _seed tulong)
      (Econst_long (Int64.repr 2870177450012600261) tulong) tulong))
  (Ssequence
    (Sset _left (Etempvar _len tulong))
    (Ssequence
      (Sifthenelse (Ebinop Oge (Etempvar _len tulong)
                     (Econst_int (Int.repr 32) tint) tint)
        (Ssequence
          (Sset _acc1
            (Ebinop Oadd
              (Ebinop Oadd (Etempvar _seed tulong)
                (Econst_long (Int64.repr (-7046029288634856825)) tulong)
                tulong)
              (Econst_long (Int64.repr (-4417276706812531889)) tulong)
              tulong))
          (Ssequence
            (Sset _acc2
              (Ebinop Oadd (Etempvar _seed tulong)
                (Econst_long (Int64.repr (-4417276706812531889)) tulong)
                tulong))
            (Ssequence
              (Sset _acc3 (Etempvar _seed tulong))
              (Ssequence
                (Sset _acc4
                  (Ebinop Osub (Etempvar _seed tulong)
                    (Econst_long (Int64.repr (-7046029288634856825)) tulong)
                    tulong))
                (Ssequence
                  (Sloop
                    (Ssequence
                      (Sifthenelse (Ebinop Oge (Etempvar _left tulong)
                                     (Econst_int (Int.repr 32) tint) tint)
                        Sskip
                        Sbreak)
                      (Ssequence
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'1)
                              (Evar _le (Tfunction
                                          ((tptr tuchar) :: tint :: nil)
                                          tulong cc_default))
                              ((Etempvar _p (tptr tuchar)) ::
                               (Econst_int (Int.repr 8) tint) :: nil))
                            (Scall (Some _t'2)
                              (Evar _round64 (Tfunction
                                               (tulong :: tulong :: nil)
                                               tulong cc_default))
                              ((Etempvar _acc1 tulong) ::
                               (Etempvar _t'1 tulong) :: nil)))
                          (Sset _acc1 (Etempvar _t'2 tulong)))
                        (Ssequence
                          (Ssequence
                            (Ssequence
                              (Scall (Some _t'3)
                                (Evar _le (Tfunction
                                            ((tptr tuchar) :: tint :: nil)
                                            tulong cc_default))
                                ((Ebinop Oadd (Etempvar _p (tptr tuchar))
                                   (Econst_int (Int.repr 8) tint)
                                   (tptr tuchar)) ::
                                 (Econst_int (Int.repr 8) tint) :: nil))
                              (Scall (Some _t'4)
                                (Evar _round64 (Tfunction
                                                 (tulong :: tulong :: nil)
                                                 tulong cc_default))
                                ((Etempvar _acc2 tulong) ::
                                 (Etempvar _t'3 tulong) :: nil)))
                            (Sset _acc2 (Etempvar _t'4 tulong)))
                          (Ssequence
                            (Ssequence
                              (Ssequence
                                (Scall (Some _t'5)
                                  (Evar _le (Tfunction
                                              ((tptr tuchar) :: tint :: nil)
                                              tulong cc_default))
                                  ((Ebinop Oadd (Etempvar _p (tptr tuchar))
                                     (Econst_int (Int.repr 16) tint)
                                     (tptr tuchar)) ::
                                   (Econst_int (Int.repr 8) tint) :: nil))
                                (Scall (Some _t'6)
                                  (Evar _round64 (Tfunction
                                                   (tulong :: tulong :: nil)
                                                   tulong cc_default))
                                  ((Etempvar _acc3 tulong) ::
                                   (Etempvar _t'5 tulong) :: nil)))
                              (Sset _acc3 (Etempvar _t'6 tulong)))
                            (Ssequence
                              (Ssequence
                                (Scall (Some _t'7)
                                  (Evar _le (Tfunction
                                              ((tptr tuchar) :: tint :: nil)
                                              tulong cc_default))
                                  ((Ebinop Oadd (Etempvar _p (tptr tuchar))
                                     (Econst_int (Int.repr 24) tint)
                                     (tptr tuchar)) ::
                                   (Econst_int (Int.repr 8) tint) :: nil))
                                (Scall (Some _t'8)
                                  (Evar _round64 (Tfunction
                                                   (tulong :: tulong :: nil)
                                                   tulong cc_default))
                                  ((Etempvar _acc4 tulong) ::
                                   (Etempvar _t'7 tulong) :: nil)))
                              (Sset _acc4 (Etempvar _t'8 tulong)))))))
                    (Ssequence
                      (Sset _left
                        (Ebinop Osub (Etempvar _left tulong)
                          (Econst_int (Int.repr 32) tint) tulong))
                      (Sset _p
                        (Ebinop Oadd (Etempvar _p (tptr tuchar))
                          (Econst_int (Int.repr 32) tint) (tptr tuchar)))))
                  (Ssequence
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'9)
                              (Evar _rotl (Tfunction (tulong :: tint :: nil)
                                            tulong cc_default))
                              ((Etempvar _acc1 tulong) ::
                               (Econst_int (Int.repr 1) tint) :: nil))
                            (Scall (Some _t'10)
                              (Evar _rotl (Tfunction (tulong :: tint :: nil)
                                            tulong cc_default))
                              ((Etempvar _acc2 tulong) ::
                               (Econst_int (Int.repr 7) tint) :: nil)))
                          (Scall (Some _t'11)
                            (Evar _rotl (Tfunction (tulong :: tint :: nil)
                                          tulong cc_default))
                            ((Etempvar _acc3 tulong) ::
                             (Econst_int (Int.repr 12) tint) :: nil)))
                        (Scall (Some _t'12)
                          (Evar _rotl (Tfunction (tulong :: tint :: nil)
                                        tulong cc_default))
                          ((Etempvar _acc4 tulong) ::
                           (Econst_int (Int.repr 18) tint) :: nil)))
                      (Sset _acc
                        (Ebinop Oadd
                          (Ebinop Oadd
                            (Ebinop Oadd (Etempvar _t'9 tulong)
                              (Etempvar _t'10 tulong) tulong)
                            (Etempvar _t'11 tulong) tulong)
                          (Etempvar _t'12 tulong) tulong)))
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'13)
                              (Evar _merge (Tfunction
                                             (tulong :: tulong :: nil) tulong
                                             cc_default))
                              ((Etempvar _acc tulong) ::
                               (Etempvar _acc1 tulong) :: nil))
                            (Scall (Some _t'14)
                              (Evar _merge (Tfunction
                                             (tulong :: tulong :: nil) tulong
                                             cc_default))
                              ((Etempvar _t'13 tulong) ::
                               (Etempvar _acc2 tulong) :: nil)))
                          (Scall (Some _t'15)
                            (Evar _merge (Tfunction (tulong :: tulong :: nil)
                                           tulong cc_default))
                            ((Etempvar _t'14 tulong) ::
                             (Etempvar _acc3 tulong) :: nil)))
                        (Scall (Some _t'16)
                          (Evar _merge (Tfunction (tulong :: tulong :: nil)
                                         tulong cc_default))
                          ((Etempvar _t'15 tulong) ::
                           (Etempvar _acc4 tulong) :: nil)))
                      (Sset _acc (Etempvar _t'16 tulong)))))))))
        Sskip)
      (Ssequence
        (Sset _acc
          (Ebinop Oadd (Etempvar _acc tulong) (Etempvar _len tulong) tulong))
        (Ssequence
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Oge (Etempvar _left tulong)
                             (Econst_int (Int.repr 8) tint) tint)
                Sskip
                Sbreak)
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'17)
                      (Evar _le (Tfunction ((tptr tuchar) :: tint :: nil)
                                  tulong cc_default))
                      ((Etempvar _p (tptr tuchar)) ::
                       (Econst_int (Int.repr 8) tint) :: nil))
                    (Scall (Some _t'18)
                      (Evar _round64 (Tfunction (tulong :: tulong :: nil)
                                       tulong cc_default))
                      ((Econst_int (Int.repr 0) tint) ::
                       (Etempvar _t'17 tulong) :: nil)))
                  (Scall (Some _t'19)
                    (Evar _rotl (Tfunction (tulong :: tint :: nil) tulong
                                  cc_default))
                    ((Ebinop Oxor (Etempvar _acc tulong)
                       (Etempvar _t'18 tulong) tulong) ::
                     (Econst_int (Int.repr 27) tint) :: nil)))
                (Sset _acc
                  (Ebinop Oadd
                    (Ebinop Omul (Etempvar _t'19 tulong)
                      (Econst_long (Int64.repr (-7046029288634856825)) tulong)
                      tulong)
                    (Econst_long (Int64.repr (-8796714831421723037)) tulong)
                    tulong))))
            (Ssequence
              (Sset _left
                (Ebinop Osub (Etempvar _left tulong)
                  (Econst_int (Int.repr 8) tint) tulong))
              (Sset _p
                (Ebinop Oadd (Etempvar _p (tptr tuchar))
                  (Econst_int (Int.repr 8) tint) (tptr tuchar)))))
          (Ssequence
            (Sifthenelse (Ebinop Oge (Etempvar _left tulong)
                           (Econst_int (Int.repr 4) tint) tint)
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'20)
                      (Evar _le (Tfunction ((tptr tuchar) :: tint :: nil)
                                  tulong cc_default))
                      ((Etempvar _p (tptr tuchar)) ::
                       (Econst_int (Int.repr 4) tint) :: nil))
                    (Scall (Some _t'21)
                      (Evar _rotl (Tfunction (tulong :: tint :: nil) tulong
                                    cc_default))
                      ((Ebinop Oxor (Etempvar _acc tulong)
                         (Ebinop Omul (Etempvar _t'20 tulong)
                           (Econst_long (Int64.repr (-7046029288634856825)) tulong)
                           tulong) tulong) ::
                       (Econst_int (Int.repr 23) tint) :: nil)))
                  (Sset _acc
                    (Ebinop Oadd
                      (Ebinop Omul (Etempvar _t'21 tulong)
                        (Econst_long (Int64.repr (-4417276706812531889)) tulong)
                        tulong)
                      (Econst_long (Int64.repr 1609587929392839161) tulong)
                      tulong)))
                (Ssequence
                  (Sset _left
                    (Ebinop Osub (Etempvar _left tulong)
                      (Econst_int (Int.repr 4) tint) tulong))
                  (Sset _p
                    (Ebinop Oadd (Etempvar _p (tptr tuchar))
                      (Econst_int (Int.repr 4) tint) (tptr tuchar)))))
              Sskip)
            (Ssequence
              (Sloop
                (Ssequence
                  (Sifthenelse (Ebinop Oge (Etempvar _left tulong)
                                 (Econst_int (Int.repr 1) tint) tint)
                    Sskip
                    Sbreak)
                  (Ssequence
                    (Ssequence
                      (Sset _t'23
                        (Ederef (Etempvar _p (tptr tuchar)) tuchar))
                      (Scall (Some _t'22)
                        (Evar _rotl (Tfunction (tulong :: tint :: nil) tulong
                                      cc_default))
                        ((Ebinop Oxor (Etempvar _acc tulong)
                           (Ebinop Omul (Etempvar _t'23 tuchar)
                             (Econst_long (Int64.repr 2870177450012600261) tulong)
                             tulong) tulong) ::
                         (Econst_int (Int.repr 11) tint) :: nil)))
                    (Sset _acc
                      (Ebinop Omul (Etempvar _t'22 tulong)
                        (Econst_long (Int64.repr (-7046029288634856825)) tulong)
                        tulong))))
                (Ssequence
                  (Sset _left
                    (Ebinop Osub (Etempvar _left tulong)
                      (Econst_int (Int.repr 1) tint) tulong))
                  (Sset _p
                    (Ebinop Oadd (Etempvar _p (tptr tuchar))
                      (Econst_int (Int.repr 1) tint) (tptr tuchar)))))
              (Ssequence
                (Sset _acc
                  (Ebinop Omul
                    (Ebinop Oxor (Etempvar _acc tulong)
                      (Ebinop Oshr (Etempvar _acc tulong)
                        (Econst_int (Int.repr 33) tint) tulong) tulong)
                    (Econst_long (Int64.repr (-4417276706812531889)) tulong)
                    tulong))
                (Ssequence
                  (Sset _acc
                    (Ebinop Omul
                      (Ebinop Oxor (Etempvar _acc tulong)
                        (Ebinop Oshr (Etempvar _acc tulong)
                          (Econst_int (Int.repr 29) tint) tulong) tulong)
                      (Econst_long (Int64.repr 1609587929392839161) tulong)
                      tulong))
                  (Sreturn (Some (Ebinop Oxor (Etempvar _acc tulong)
                                   (Ebinop Oshr (Etempvar _acc tulong)
                                     (Econst_int (Int.repr 32) tint) tulong)
                                   tulong))))))))))))
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := ((_seed, tulong) :: nil);
  fn_temps := ((_len, tulong) :: (_data, (tptr tuchar)) :: (_t'4, tulong) ::
               (_t'3, tulong) :: (_t'2, (tptr tuchar)) :: (_t'1, tulong) ::
               (_t'6, tulong) :: (_t'5, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _upto (Tfunction (tulong :: nil) tulong cc_default))
        ((Econst_long (Int64.repr 9223372036854775807) tlong) :: nil))
      (Sset _len (Etempvar _t'1 tulong)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _any_bytes (Tfunction (tulong :: nil) (tptr tuchar)
                             cc_default)) ((Etempvar _len tulong) :: nil))
        (Sset _data (Etempvar _t'2 (tptr tuchar))))
      (Ssequence
        (Scall None
          (Evar _nondet_bytes (Tfunction ((tptr tuchar) :: tulong :: nil)
                                tvoid cc_default))
          ((Ecast (Eaddrof (Evar _seed tulong) (tptr tulong)) (tptr tuchar)) ::
           (Esizeof tulong tulong) :: nil))
        (Ssequence
          (Sifthenelse (Ebinop Oeq (Etempvar _data (tptr tuchar))
                         (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                         tint)
            (Sreturn (Some (Econst_int (Int.repr 0) tint)))
            Sskip)
          (Ssequence
            (Ssequence
              (Ssequence
                (Ssequence
                  (Sset _t'6 (Evar _seed tulong))
                  (Scall (Some _t'3)
                    (Evar _ZSTD_XXH64 (Tfunction
                                        ((tptr tvoid) :: tulong :: tulong ::
                                         nil) tulong cc_default))
                    ((Etempvar _data (tptr tuchar)) ::
                     (Etempvar _len tulong) :: (Etempvar _t'6 tulong) :: nil)))
                (Ssequence
                  (Sset _t'5 (Evar _seed tulong))
                  (Scall (Some _t'4)
                    (Evar _xxh64 (Tfunction
                                   ((tptr tuchar) :: tulong :: tulong :: nil)
                                   tulong cc_default))
                    ((Etempvar _data (tptr tuchar)) ::
                     (Etempvar _len tulong) :: (Etempvar _t'5 tulong) :: nil))))
              (Scall None
                (Evar _gp_assert (Tfunction (tint :: nil) tvoid cc_default))
                ((Ebinop Oeq (Etempvar _t'3 tulong) (Etempvar _t'4 tulong)
                   tint) :: nil)))
            (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition composites : list composite_definition :=
nil.

Definition global_definitions : list (ident * globdef fundef type) :=
((___compcert_va_int32,
   Gfun(External (EF_runtime "__compcert_va_int32"
                   (mksignature (AST.Xptr :: nil) AST.Xint cc_default))
     ((tptr tvoid) :: nil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_runtime "__compcert_va_int64"
                   (mksignature (AST.Xptr :: nil) AST.Xlong cc_default))
     ((tptr tvoid) :: nil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_runtime "__compcert_va_float64"
                   (mksignature (AST.Xptr :: nil) AST.Xfloat cc_default))
     ((tptr tvoid) :: nil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_runtime "__compcert_va_composite"
                   (mksignature (AST.Xptr :: AST.Xlong :: nil) AST.Xptr
                     cc_default)) ((tptr tvoid) :: tulong :: nil)
     (tptr tvoid) cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Xfloat :: nil) AST.Xlong cc_default))
     (tdouble :: nil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Xfloat :: nil) AST.Xlong cc_default))
     (tdouble :: nil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Xlong :: nil) AST.Xfloat cc_default))
     (tlong :: nil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Xlong :: nil) AST.Xfloat cc_default))
     (tulong :: nil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Xlong :: nil) AST.Xsingle cc_default))
     (tlong :: nil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Xlong :: nil) AST.Xsingle cc_default))
     (tulong :: nil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tlong :: tint :: nil) tlong cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tulong :: tint :: nil) tulong cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tlong :: tint :: nil) tlong cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___builtin_ais_annot,
   Gfun(External (EF_builtin "__builtin_ais_annot"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     ((tptr tschar) :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Xlong :: nil) AST.Xlong cc_default))
     (tulong :: nil) tulong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Xint16unsigned :: nil)
                     AST.Xint16unsigned cc_default)) (tushort :: nil) tushort
     cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fabsf,
   Gfun(External (EF_builtin "__builtin_fabsf"
                   (mksignature (AST.Xsingle :: nil) AST.Xsingle cc_default))
     (tfloat :: nil) tfloat cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_sqrt,
   Gfun(External (EF_builtin "__builtin_sqrt"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Xptr :: AST.Xptr :: AST.Xlong :: AST.Xlong :: nil)
                     AST.Xvoid cc_default))
     ((tptr tvoid) :: (tptr tvoid) :: tulong :: tulong :: nil) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Xbool :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (tbool :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     ((tptr tschar) :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xint
                     cc_default)) ((tptr tschar) :: tint :: nil) tint
     cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Xvoid cc_default)) nil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr tvoid) :: nil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xvoid
                     cc_default)) ((tptr tvoid) :: tuint :: nil) tvoid
     cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xvoid
                     cc_default)) ((tptr tvoid) :: (tptr tvoid) :: nil) tvoid
     cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr tvoid) :: nil) tvoid cc_default)) ::
 (___builtin_unreachable,
   Gfun(External (EF_builtin "__builtin_unreachable"
                   (mksignature nil AST.Xvoid cc_default)) nil tvoid
     cc_default)) ::
 (___builtin_expect,
   Gfun(External (EF_builtin "__builtin_expect"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Xfloat :: AST.Xfloat :: nil) AST.Xfloat
                     cc_default)) (tdouble :: tdouble :: nil) tdouble
     cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Xfloat :: AST.Xfloat :: nil) AST.Xfloat
                     cc_default)) (tdouble :: tdouble :: nil) tdouble
     cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Xptr :: nil) AST.Xint16unsigned
                     cc_default)) ((tptr tushort) :: nil) tushort
     cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Xptr :: nil) AST.Xint cc_default))
     ((tptr tuint) :: nil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Xptr :: AST.Xint16unsigned :: nil)
                     AST.Xvoid cc_default))
     ((tptr tushort) :: tushort :: nil) tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xvoid
                     cc_default)) ((tptr tuint) :: tuint :: nil) tvoid
     cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Xint :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (tint :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_quickproof_malloc,
   Gfun(External (EF_external "quickproof_malloc"
                   (mksignature (AST.Xlong :: nil) AST.Xptr cc_default))
     (tulong :: nil) (tptr tvoid) cc_default)) ::
 (_nondet_size,
   Gfun(External (EF_external "nondet_size"
                   (mksignature nil AST.Xlong cc_default)) nil tulong
     cc_default)) ::
 (_nondet_bytes,
   Gfun(External (EF_external "nondet_bytes"
                   (mksignature (AST.Xptr :: AST.Xlong :: nil) AST.Xvoid
                     cc_default)) ((tptr tuchar) :: tulong :: nil) tvoid
     cc_default)) ::
 (_gp_assert,
   Gfun(External (EF_external "gp_assert"
                   (mksignature (AST.Xint :: nil) AST.Xvoid cc_default))
     (tint :: nil) tvoid cc_default)) ::
 (_ZSTD_XXH64,
   Gfun(External (EF_external "ZSTD_XXH64"
                   (mksignature (AST.Xptr :: AST.Xlong :: AST.Xlong :: nil)
                     AST.Xlong cc_default))
     ((tptr tvoid) :: tulong :: tulong :: nil) tulong cc_default)) ::
 (_upto, Gfun(Internal f_upto)) ::
 (_any_bytes, Gfun(Internal f_any_bytes)) ::
 (_rotl, Gfun(Internal f_rotl)) :: (_le, Gfun(Internal f_le)) ::
 (_round64, Gfun(Internal f_round64)) :: (_merge, Gfun(Internal f_merge)) ::
 (_xxh64, Gfun(Internal f_xxh64)) :: (_main, Gfun(Internal f_main)) :: nil).

Definition public_idents : list ident :=
(_main :: _ZSTD_XXH64 :: _gp_assert :: _nondet_bytes :: _nondet_size ::
 _quickproof_malloc :: ___builtin_debug :: ___builtin_write32_reversed ::
 ___builtin_write16_reversed :: ___builtin_read32_reversed ::
 ___builtin_read16_reversed :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_fmin ::
 ___builtin_fmax :: ___builtin_expect :: ___builtin_unreachable ::
 ___builtin_va_end :: ___builtin_va_copy :: ___builtin_va_arg ::
 ___builtin_va_start :: ___builtin_membar :: ___builtin_annot_intval ::
 ___builtin_annot :: ___builtin_sel :: ___builtin_memcpy_aligned ::
 ___builtin_sqrt :: ___builtin_fsqrt :: ___builtin_fabsf ::
 ___builtin_fabs :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
 ___builtin_bswap16 :: ___builtin_bswap32 :: ___builtin_bswap ::
 ___builtin_bswap64 :: ___builtin_ais_annot :: ___compcert_i64_umulh ::
 ___compcert_i64_smulh :: ___compcert_i64_sar :: ___compcert_i64_shr ::
 ___compcert_i64_shl :: ___compcert_i64_umod :: ___compcert_i64_smod ::
 ___compcert_i64_udiv :: ___compcert_i64_sdiv :: ___compcert_i64_utof ::
 ___compcert_i64_stof :: ___compcert_i64_utod :: ___compcert_i64_stod ::
 ___compcert_i64_dtou :: ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


