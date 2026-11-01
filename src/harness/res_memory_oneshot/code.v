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
  Definition source_file := "harness/res_memory_oneshot.c".
  Definition normalized := true.
End Info.

Definition _ZSTD_DCtx_s : ident := $"ZSTD_DCtx_s".
Definition _ZSTD_createDCtx_advancedP : ident := $"ZSTD_createDCtx_advancedP".
Definition _ZSTD_decompressDCtx : ident := $"ZSTD_decompressDCtx".
Definition _ZSTD_estimateDCtxSize : ident := $"ZSTD_estimateDCtxSize".
Definition _ZSTD_freeDCtx : ident := $"ZSTD_freeDCtx".
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
Definition ___gp_ZSTD_customMem : ident := $"__gp_ZSTD_customMem".
Definition _address : ident := $"address".
Definition _any_bytes : ident := $"any_bytes".
Definition _block : ident := $"block".
Definition _bytes : ident := $"bytes".
Definition _cap : ident := $"cap".
Definition _count : ident := $"count".
Definition _count__1 : ident := $"count__1".
Definition _count_alloc : ident := $"count_alloc".
Definition _count_free : ident := $"count_free".
Definition _customAlloc : ident := $"customAlloc".
Definition _customFree : ident := $"customFree".
Definition _dctx : ident := $"dctx".
Definition _dst : ident := $"dst".
Definition _gp_assert : ident := $"gp_assert".
Definition _main : ident := $"main".
Definition _max : ident := $"max".
Definition _mem : ident := $"mem".
Definition _n : ident := $"n".
Definition _nondet_bytes : ident := $"nondet_bytes".
Definition _nondet_size : ident := $"nondet_size".
Definition _nondet_u8 : ident := $"nondet_u8".
Definition _now : ident := $"now".
Definition _opaque : ident := $"opaque".
Definition _peak : ident := $"peak".
Definition _quickproof_free : ident := $"quickproof_free".
Definition _quickproof_malloc : ident := $"quickproof_malloc".
Definition _size : ident := $"size".
Definition _src : ident := $"src".
Definition _upto : ident := $"upto".
Definition _value : ident := $"value".
Definition _t'1 : ident := 128%positive.
Definition _t'10 : ident := 137%positive.
Definition _t'2 : ident := 129%positive.
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

Definition f_count_alloc := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_opaque, (tptr tvoid)) :: (_size, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_count__1, (tptr (Tstruct _count noattr))) ::
               (_block, (tptr tulong)) :: (_t'2, (tptr tvoid)) ::
               (_t'1, (tptr tvoid)) :: (_t'6, tulong) :: (_t'5, tulong) ::
               (_t'4, tulong) :: (_t'3, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sset _count__1 (Etempvar _opaque (tptr tvoid)))
  (Ssequence
    (Ssequence
      (Sifthenelse (Ebinop Ole (Etempvar _size tulong)
                     (Ebinop Osub
                       (Econst_long (Int64.repr 9223372036854775807) tlong)
                       (Esizeof tulong tulong) tulong) tint)
        (Ssequence
          (Scall (Some _t'2)
            (Evar _quickproof_malloc (Tfunction (tulong :: nil) (tptr tvoid)
                                       cc_default))
            ((Ebinop Oadd (Esizeof tulong tulong) (Etempvar _size tulong)
               tulong) :: nil))
          (Sset _t'1 (Ecast (Etempvar _t'2 (tptr tvoid)) (tptr tvoid))))
        (Sset _t'1
          (Ecast (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
            (tptr tvoid))))
      (Sset _block (Etempvar _t'1 (tptr tvoid))))
    (Ssequence
      (Sifthenelse (Ebinop Oeq (Etempvar _block (tptr tulong))
                     (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                     tint)
        (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
        Sskip)
      (Ssequence
        (Sassign
          (Ederef
            (Ebinop Oadd (Etempvar _block (tptr tulong))
              (Econst_int (Int.repr 0) tint) (tptr tulong)) tulong)
          (Etempvar _size tulong))
        (Ssequence
          (Ssequence
            (Sset _t'6
              (Efield
                (Ederef (Etempvar _count__1 (tptr (Tstruct _count noattr)))
                  (Tstruct _count noattr)) _now tulong))
            (Sassign
              (Efield
                (Ederef (Etempvar _count__1 (tptr (Tstruct _count noattr)))
                  (Tstruct _count noattr)) _now tulong)
              (Ebinop Oadd (Etempvar _t'6 tulong) (Etempvar _size tulong)
                tulong)))
          (Ssequence
            (Ssequence
              (Sset _t'3
                (Efield
                  (Ederef (Etempvar _count__1 (tptr (Tstruct _count noattr)))
                    (Tstruct _count noattr)) _now tulong))
              (Ssequence
                (Sset _t'4
                  (Efield
                    (Ederef
                      (Etempvar _count__1 (tptr (Tstruct _count noattr)))
                      (Tstruct _count noattr)) _peak tulong))
                (Sifthenelse (Ebinop Ogt (Etempvar _t'3 tulong)
                               (Etempvar _t'4 tulong) tint)
                  (Ssequence
                    (Sset _t'5
                      (Efield
                        (Ederef
                          (Etempvar _count__1 (tptr (Tstruct _count noattr)))
                          (Tstruct _count noattr)) _now tulong))
                    (Sassign
                      (Efield
                        (Ederef
                          (Etempvar _count__1 (tptr (Tstruct _count noattr)))
                          (Tstruct _count noattr)) _peak tulong)
                      (Etempvar _t'5 tulong)))
                  Sskip)))
            (Sreturn (Some (Ebinop Oadd (Etempvar _block (tptr tulong))
                             (Econst_int (Int.repr 1) tint) (tptr tulong))))))))))
|}.

Definition f_count_free := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_opaque, (tptr tvoid)) :: (_address, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_count__1, (tptr (Tstruct _count noattr))) ::
               (_block, (tptr tulong)) :: (_t'2, tulong) :: (_t'1, tulong) ::
               nil);
  fn_body :=
(Ssequence
  (Sset _count__1 (Etempvar _opaque (tptr tvoid)))
  (Ssequence
    (Sset _block
      (Ebinop Osub (Ecast (Etempvar _address (tptr tvoid)) (tptr tulong))
        (Econst_int (Int.repr 1) tint) (tptr tulong)))
    (Ssequence
      (Sifthenelse (Ebinop Oeq (Etempvar _address (tptr tvoid))
                     (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                     tint)
        (Sreturn None)
        Sskip)
      (Ssequence
        (Ssequence
          (Sset _t'1
            (Efield
              (Ederef (Etempvar _count__1 (tptr (Tstruct _count noattr)))
                (Tstruct _count noattr)) _now tulong))
          (Ssequence
            (Sset _t'2
              (Ederef
                (Ebinop Oadd (Etempvar _block (tptr tulong))
                  (Econst_int (Int.repr 0) tint) (tptr tulong)) tulong))
            (Sassign
              (Efield
                (Ederef (Etempvar _count__1 (tptr (Tstruct _count noattr)))
                  (Tstruct _count noattr)) _now tulong)
              (Ebinop Osub (Etempvar _t'1 tulong) (Etempvar _t'2 tulong)
                tulong))))
        (Scall None
          (Evar _quickproof_free (Tfunction ((tptr tvoid) :: nil) tvoid
                                   cc_default))
          ((Etempvar _block (tptr tulong)) :: nil))))))
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := ((_count__1, (Tstruct _count noattr)) ::
              (_mem, (Tstruct ___gp_ZSTD_customMem noattr)) :: nil);
  fn_temps := ((_dctx, (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
               (_n, tulong) :: (_cap, tulong) :: (_src, (tptr tuchar)) ::
               (_dst, (tptr tuchar)) :: (_t'9, tulong) :: (_t'8, tint) ::
               (_t'7, (tptr tvoid)) :: (_t'6, (tptr tuchar)) ::
               (_t'5, tulong) :: (_t'4, tulong) :: (_t'3, tuchar) ::
               (_t'2, (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
               (_t'1, tulong) :: (_t'10, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'1 (Ecast (Econst_int (Int.repr 0) tint) tulong))
        (Sassign
          (Efield (Evar _count__1 (Tstruct _count noattr)) _peak tulong)
          (Etempvar _t'1 tulong)))
      (Sassign (Efield (Evar _count__1 (Tstruct _count noattr)) _now tulong)
        (Etempvar _t'1 tulong)))
    (Ssequence
      (Sassign
        (Efield (Evar _mem (Tstruct ___gp_ZSTD_customMem noattr))
          _customAlloc
          (tptr (Tfunction ((tptr tvoid) :: tulong :: nil) (tptr tvoid)
                  cc_default)))
        (Evar _count_alloc (Tfunction ((tptr tvoid) :: tulong :: nil)
                             (tptr tvoid) cc_default)))
      (Ssequence
        (Sassign
          (Efield (Evar _mem (Tstruct ___gp_ZSTD_customMem noattr))
            _customFree
            (tptr (Tfunction ((tptr tvoid) :: (tptr tvoid) :: nil) tvoid
                    cc_default)))
          (Evar _count_free (Tfunction ((tptr tvoid) :: (tptr tvoid) :: nil)
                              tvoid cc_default)))
        (Ssequence
          (Sassign
            (Efield (Evar _mem (Tstruct ___gp_ZSTD_customMem noattr)) _opaque
              (tptr tvoid))
            (Eaddrof (Evar _count__1 (Tstruct _count noattr))
              (tptr (Tstruct _count noattr))))
          (Ssequence
            (Ssequence
              (Scall (Some _t'2)
                (Evar _ZSTD_createDCtx_advancedP (Tfunction
                                                   ((tptr (Tstruct ___gp_ZSTD_customMem noattr)) ::
                                                    nil)
                                                   (tptr (Tstruct _ZSTD_DCtx_s noattr))
                                                   cc_default))
                ((Eaddrof (Evar _mem (Tstruct ___gp_ZSTD_customMem noattr))
                   (tptr (Tstruct ___gp_ZSTD_customMem noattr))) :: nil))
              (Sset _dctx
                (Etempvar _t'2 (tptr (Tstruct _ZSTD_DCtx_s noattr)))))
            (Ssequence
              (Sifthenelse (Ebinop Oeq
                             (Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                             (Ecast (Econst_int (Int.repr 0) tint)
                               (tptr tvoid)) tint)
                (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                Sskip)
              (Ssequence
                (Sloop
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'4)
                        (Evar _upto (Tfunction (tulong :: nil) tulong
                                      cc_default))
                        ((Econst_long (Int64.repr 9223372036854775807) tlong) ::
                         nil))
                      (Sset _n (Etempvar _t'4 tulong)))
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'5)
                          (Evar _upto (Tfunction (tulong :: nil) tulong
                                        cc_default))
                          ((Econst_long (Int64.repr 9223372036854775807) tlong) ::
                           nil))
                        (Sset _cap (Etempvar _t'5 tulong)))
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'6)
                            (Evar _any_bytes (Tfunction (tulong :: nil)
                                               (tptr tuchar) cc_default))
                            ((Etempvar _n tulong) :: nil))
                          (Sset _src (Etempvar _t'6 (tptr tuchar))))
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'7)
                              (Evar _quickproof_malloc (Tfunction
                                                         (tulong :: nil)
                                                         (tptr tvoid)
                                                         cc_default))
                              ((Etempvar _cap tulong) :: nil))
                            (Sset _dst (Etempvar _t'7 (tptr tvoid))))
                          (Ssequence
                            (Ssequence
                              (Sifthenelse (Ebinop Oeq
                                             (Etempvar _src (tptr tuchar))
                                             (Ecast
                                               (Econst_int (Int.repr 0) tint)
                                               (tptr tvoid)) tint)
                                (Sset _t'8 (Econst_int (Int.repr 1) tint))
                                (Sset _t'8
                                  (Ecast
                                    (Ebinop Oeq (Etempvar _dst (tptr tuchar))
                                      (Ecast (Econst_int (Int.repr 0) tint)
                                        (tptr tvoid)) tint) tbool)))
                              (Sifthenelse (Etempvar _t'8 tint)
                                (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                                Sskip))
                            (Ssequence
                              (Scall None
                                (Evar _ZSTD_decompressDCtx (Tfunction
                                                             ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
                                                              (tptr tvoid) ::
                                                              tulong ::
                                                              (tptr tvoid) ::
                                                              tulong :: nil)
                                                             tulong
                                                             cc_default))
                                ((Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
                                 (Etempvar _dst (tptr tuchar)) ::
                                 (Etempvar _cap tulong) ::
                                 (Etempvar _src (tptr tuchar)) ::
                                 (Etempvar _n tulong) :: nil))
                              (Ssequence
                                (Scall None
                                  (Evar _quickproof_free (Tfunction
                                                           ((tptr tvoid) ::
                                                            nil) tvoid
                                                           cc_default))
                                  ((Etempvar _src (tptr tuchar)) :: nil))
                                (Scall None
                                  (Evar _quickproof_free (Tfunction
                                                           ((tptr tvoid) ::
                                                            nil) tvoid
                                                           cc_default))
                                  ((Etempvar _dst (tptr tuchar)) :: nil)))))))))
                  (Ssequence
                    (Scall (Some _t'3)
                      (Evar _nondet_u8 (Tfunction nil tuchar cc_default))
                      nil)
                    (Sifthenelse (Ebinop One (Etempvar _t'3 tuchar)
                                   (Econst_int (Int.repr 0) tint) tint)
                      Sskip
                      Sbreak)))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'9)
                      (Evar _ZSTD_estimateDCtxSize (Tfunction nil tulong
                                                     cc_default)) nil)
                    (Ssequence
                      (Sset _t'10
                        (Efield (Evar _count__1 (Tstruct _count noattr))
                          _peak tulong))
                      (Scall None
                        (Evar _gp_assert (Tfunction (tint :: nil) tvoid
                                           cc_default))
                        ((Ebinop Ole (Etempvar _t'10 tulong)
                           (Etempvar _t'9 tulong) tint) :: nil))))
                  (Ssequence
                    (Scall None
                      (Evar _ZSTD_freeDCtx (Tfunction
                                             ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
                                              nil) tulong cc_default))
                      ((Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
                       nil))
                    (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition composites : list composite_definition :=
(Composite ___gp_ZSTD_customMem Struct
   (Member_plain _customAlloc
      (tptr (Tfunction ((tptr tvoid) :: tulong :: nil) (tptr tvoid)
              cc_default)) ::
    Member_plain _customFree
      (tptr (Tfunction ((tptr tvoid) :: (tptr tvoid) :: nil) tvoid
              cc_default)) :: Member_plain _opaque (tptr tvoid) :: nil)
   noattr ::
 Composite _count Struct
   (Member_plain _now tulong :: Member_plain _peak tulong :: nil)
   noattr :: nil).

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
 (_quickproof_free,
   Gfun(External (EF_external "quickproof_free"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr tvoid) :: nil) tvoid cc_default)) ::
 (_nondet_u8,
   Gfun(External (EF_external "nondet_u8"
                   (mksignature nil AST.Xint8unsigned cc_default)) nil tuchar
     cc_default)) ::
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
 (_ZSTD_freeDCtx,
   Gfun(External (EF_external "ZSTD_freeDCtx"
                   (mksignature (AST.Xptr :: nil) AST.Xlong cc_default))
     ((tptr (Tstruct _ZSTD_DCtx_s noattr)) :: nil) tulong cc_default)) ::
 (_ZSTD_decompressDCtx,
   Gfun(External (EF_external "ZSTD_decompressDCtx"
                   (mksignature
                     (AST.Xptr :: AST.Xptr :: AST.Xlong :: AST.Xptr ::
                      AST.Xlong :: nil) AST.Xlong cc_default))
     ((tptr (Tstruct _ZSTD_DCtx_s noattr)) :: (tptr tvoid) :: tulong ::
      (tptr tvoid) :: tulong :: nil) tulong cc_default)) ::
 (_ZSTD_estimateDCtxSize,
   Gfun(External (EF_external "ZSTD_estimateDCtxSize"
                   (mksignature nil AST.Xlong cc_default)) nil tulong
     cc_default)) :: (_upto, Gfun(Internal f_upto)) ::
 (_any_bytes, Gfun(Internal f_any_bytes)) ::
 (_ZSTD_createDCtx_advancedP,
   Gfun(External (EF_external "ZSTD_createDCtx_advancedP"
                   (mksignature (AST.Xptr :: nil) AST.Xptr cc_default))
     ((tptr (Tstruct ___gp_ZSTD_customMem noattr)) :: nil)
     (tptr (Tstruct _ZSTD_DCtx_s noattr)) cc_default)) ::
 (_count_alloc, Gfun(Internal f_count_alloc)) ::
 (_count_free, Gfun(Internal f_count_free)) ::
 (_main, Gfun(Internal f_main)) :: nil).

Definition public_idents : list ident :=
(_main :: _ZSTD_createDCtx_advancedP :: _ZSTD_estimateDCtxSize ::
 _ZSTD_decompressDCtx :: _ZSTD_freeDCtx :: _gp_assert :: _nondet_bytes ::
 _nondet_size :: _nondet_u8 :: _quickproof_free :: _quickproof_malloc ::
 ___builtin_debug :: ___builtin_write32_reversed ::
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


