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
  Definition source_file := "harness/x_any_params.c".
  Definition normalized := true.
End Info.

Definition _ZSTD_DCtx_refDDict : ident := $"ZSTD_DCtx_refDDict".
Definition _ZSTD_DCtx_reset : ident := $"ZSTD_DCtx_reset".
Definition _ZSTD_DCtx_s : ident := $"ZSTD_DCtx_s".
Definition _ZSTD_DCtx_setMaxWindowSize : ident := $"ZSTD_DCtx_setMaxWindowSize".
Definition _ZSTD_DCtx_setParameter : ident := $"ZSTD_DCtx_setParameter".
Definition _ZSTD_DDict_s : ident := $"ZSTD_DDict_s".
Definition _ZSTD_createDCtx : ident := $"ZSTD_createDCtx".
Definition _ZSTD_createDDict : ident := $"ZSTD_createDDict".
Definition _ZSTD_decompressDCtx : ident := $"ZSTD_decompressDCtx".
Definition _ZSTD_decompressStream : ident := $"ZSTD_decompressStream".
Definition _ZSTD_freeDCtx : ident := $"ZSTD_freeDCtx".
Definition _ZSTD_freeDDict : ident := $"ZSTD_freeDDict".
Definition _ZSTD_inBuffer_s : ident := $"ZSTD_inBuffer_s".
Definition _ZSTD_isError : ident := $"ZSTD_isError".
Definition _ZSTD_outBuffer_s : ident := $"ZSTD_outBuffer_s".
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
Definition _ap_params : ident := $"ap_params".
Definition _calls : ident := $"calls".
Definition _cap : ident := $"cap".
Definition _d : ident := $"d".
Definition _dbuf : ident := $"dbuf".
Definition _dctx : ident := $"dctx".
Definition _dd : ident := $"dd".
Definition _dn : ident := $"dn".
Definition _dst : ident := $"dst".
Definition _got : ident := $"got".
Definition _gp_assert : ident := $"gp_assert".
Definition _gp_assume : ident := $"gp_assume".
Definition _i : ident := $"i".
Definition _ib : ident := $"ib".
Definition _ilen : ident := $"ilen".
Definition _in : ident := $"in".
Definition _ipos : ident := $"ipos".
Definition _main : ident := $"main".
Definition _n : ident := $"n".
Definition _nondet_bytes : ident := $"nondet_bytes".
Definition _nondet_size : ident := $"nondet_size".
Definition _nondet_u32 : ident := $"nondet_u32".
Definition _ob : ident := $"ob".
Definition _olen : ident := $"olen".
Definition _out : ident := $"out".
Definition _pos : ident := $"pos".
Definition _quickproof_free : ident := $"quickproof_free".
Definition _quickproof_malloc : ident := $"quickproof_malloc".
Definition _r : ident := $"r".
Definition _size : ident := $"size".
Definition _src : ident := $"src".
Definition _which : ident := $"which".
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
Definition _t'24 : ident := 151%positive.
Definition _t'25 : ident := 152%positive.
Definition _t'26 : ident := 153%positive.
Definition _t'27 : ident := 154%positive.
Definition _t'28 : ident := 155%positive.
Definition _t'29 : ident := 156%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'30 : ident := 157%positive.
Definition _t'31 : ident := 158%positive.
Definition _t'32 : ident := 159%positive.
Definition _t'33 : ident := 160%positive.
Definition _t'34 : ident := 161%positive.
Definition _t'35 : ident := 162%positive.
Definition _t'36 : ident := 163%positive.
Definition _t'37 : ident := 164%positive.
Definition _t'38 : ident := 165%positive.
Definition _t'39 : ident := 166%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'40 : ident := 167%positive.
Definition _t'41 : ident := 168%positive.
Definition _t'42 : ident := 169%positive.
Definition _t'43 : ident := 170%positive.
Definition _t'44 : ident := 171%positive.
Definition _t'45 : ident := 172%positive.
Definition _t'46 : ident := 173%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

Definition v_ap_params := {|
  gvar_info := (tarray tint 5);
  gvar_init := (Init_int32 (Int.repr 100) :: Init_int32 (Int.repr 1000) ::
                Init_int32 (Int.repr 1002) :: Init_int32 (Int.repr 1003) ::
                Init_int32 (Int.repr 1005) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := ((_dd, (tarray (tptr (Tstruct _ZSTD_DDict_s noattr)) 2)) ::
              (_dbuf, (tarray (tptr tuchar) 2)) ::
              (_in, (Tstruct _ZSTD_inBuffer_s noattr)) ::
              (_out, (Tstruct _ZSTD_outBuffer_s noattr)) :: nil);
  fn_temps := ((_n, tulong) :: (_cap, tulong) :: (_r, tulong) ::
               (_ipos, tulong) :: (_got, tulong) :: (_src, (tptr tuchar)) ::
               (_dst, (tptr tuchar)) :: (_i, tuint) :: (_calls, tuint) ::
               (_dctx, (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
               (_which, tuint) :: (_dn, tulong) :: (_d, (tptr tuchar)) ::
               (_ilen, tulong) :: (_olen, tulong) :: (_ib, (tptr tuchar)) ::
               (_ob, (tptr tuchar)) :: (_t'30, tuint) :: (_t'29, tint) ::
               (_t'28, tint) :: (_t'27, tuint) :: (_t'26, tulong) ::
               (_t'25, tint) :: (_t'24, (tptr tvoid)) ::
               (_t'23, (tptr tvoid)) :: (_t'22, tulong) :: (_t'21, tuint) ::
               (_t'20, tuint) :: (_t'19, tint) :: (_t'18, tint) ::
               (_t'17, tuint) :: (_t'16, tulong) :: (_t'15, (tptr tvoid)) ::
               (_t'14, tulong) ::
               (_t'13, (tptr (Tstruct _ZSTD_DDict_s noattr))) ::
               (_t'12, (tptr tvoid)) :: (_t'11, tulong) :: (_t'10, tuint) ::
               (_t'9, tint) :: (_t'8, tuint) :: (_t'7, tuint) ::
               (_t'6, tuint) :: (_t'5, tuint) ::
               (_t'4, (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
               (_t'3, tulong) :: (_t'2, (tptr tvoid)) :: (_t'1, tulong) ::
               (_t'46, tint) :: (_t'45, (tptr tuchar)) ::
               (_t'44, (tptr (Tstruct _ZSTD_DDict_s noattr))) ::
               (_t'43, (tptr (Tstruct _ZSTD_DDict_s noattr))) ::
               (_t'42, (tptr (Tstruct _ZSTD_DDict_s noattr))) ::
               (_t'41, tuchar) :: (_t'40, tulong) :: (_t'39, tulong) ::
               (_t'38, tulong) :: (_t'37, tulong) :: (_t'36, tulong) ::
               (_t'35, tulong) :: (_t'34, tulong) :: (_t'33, tulong) ::
               (_t'32, (tptr (Tstruct _ZSTD_DDict_s noattr))) ::
               (_t'31, (tptr tuchar)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _nondet_size (Tfunction nil tulong cc_default)) nil)
      (Sset _n (Etempvar _t'1 tulong)))
    (Ssequence
      (Sset _ipos (Ecast (Econst_int (Int.repr 0) tint) tulong))
      (Ssequence
        (Sset _got (Ecast (Econst_int (Int.repr 0) tint) tulong))
        (Ssequence
          (Sset _dst (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
          (Ssequence
            (Scall None
              (Evar _gp_assume (Tfunction (tint :: nil) tvoid cc_default))
              ((Ebinop Ole (Etempvar _n tulong)
                 (Econst_int (Int.repr 4096) tint) tint) :: nil))
            (Ssequence
              (Ssequence
                (Scall (Some _t'2)
                  (Evar _quickproof_malloc (Tfunction (tulong :: nil)
                                             (tptr tvoid) cc_default))
                  ((Etempvar _n tulong) :: nil))
                (Sset _src (Etempvar _t'2 (tptr tvoid))))
              (Ssequence
                (Sifthenelse (Ebinop Oeq (Etempvar _src (tptr tuchar))
                               (Ecast (Econst_int (Int.repr 0) tint)
                                 (tptr tvoid)) tint)
                  (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                  Sskip)
                (Ssequence
                  (Scall None
                    (Evar _nondet_bytes (Tfunction
                                          ((tptr tuchar) :: tulong :: nil)
                                          tvoid cc_default))
                    ((Etempvar _src (tptr tuchar)) :: (Etempvar _n tulong) ::
                     nil))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'3)
                        (Evar _nondet_size (Tfunction nil tulong cc_default))
                        nil)
                      (Sset _cap (Etempvar _t'3 tulong)))
                    (Ssequence
                      (Scall None
                        (Evar _gp_assume (Tfunction (tint :: nil) tvoid
                                           cc_default))
                        ((Ebinop Ole (Etempvar _cap tulong)
                           (Econst_int (Int.repr 65536) tint) tint) :: nil))
                      (Ssequence
                        (Ssequence
                          (Sset _i (Econst_int (Int.repr 0) tint))
                          (Sloop
                            (Ssequence
                              (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                                             (Econst_int (Int.repr 2) tint)
                                             tint)
                                Sskip
                                Sbreak)
                              (Ssequence
                                (Sassign
                                  (Ederef
                                    (Ebinop Oadd
                                      (Evar _dd (tarray (tptr (Tstruct _ZSTD_DDict_s noattr)) 2))
                                      (Etempvar _i tuint)
                                      (tptr (tptr (Tstruct _ZSTD_DDict_s noattr))))
                                    (tptr (Tstruct _ZSTD_DDict_s noattr)))
                                  (Ecast (Econst_int (Int.repr 0) tint)
                                    (tptr tvoid)))
                                (Sassign
                                  (Ederef
                                    (Ebinop Oadd
                                      (Evar _dbuf (tarray (tptr tuchar) 2))
                                      (Etempvar _i tuint)
                                      (tptr (tptr tuchar))) (tptr tuchar))
                                  (Ecast (Econst_int (Int.repr 0) tint)
                                    (tptr tvoid)))))
                            (Sset _i
                              (Ebinop Oadd (Etempvar _i tuint)
                                (Econst_int (Int.repr 1) tint) tuint))))
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'4)
                              (Evar _ZSTD_createDCtx (Tfunction nil
                                                       (tptr (Tstruct _ZSTD_DCtx_s noattr))
                                                       cc_default)) nil)
                            (Sset _dctx
                              (Etempvar _t'4 (tptr (Tstruct _ZSTD_DCtx_s noattr)))))
                          (Ssequence
                            (Sifthenelse (Ebinop Oeq
                                           (Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                           (Ecast
                                             (Econst_int (Int.repr 0) tint)
                                             (tptr tvoid)) tint)
                              (Ssequence
                                (Scall None
                                  (Evar _quickproof_free (Tfunction
                                                           ((tptr tvoid) ::
                                                            nil) tvoid
                                                           cc_default))
                                  ((Etempvar _src (tptr tuchar)) :: nil))
                                (Sreturn (Some (Econst_int (Int.repr 0) tint))))
                              Sskip)
                            (Ssequence
                              (Ssequence
                                (Sset _i (Econst_int (Int.repr 0) tint))
                                (Sloop
                                  (Ssequence
                                    (Sifthenelse (Ebinop Olt
                                                   (Etempvar _i tuint)
                                                   (Econst_int (Int.repr 8) tint)
                                                   tint)
                                      Sskip
                                      Sbreak)
                                    (Ssequence
                                      (Ssequence
                                        (Scall (Some _t'5)
                                          (Evar _nondet_u32 (Tfunction nil
                                                              tuint
                                                              cc_default))
                                          nil)
                                        (Sset _which
                                          (Ebinop Omod (Etempvar _t'5 tuint)
                                            (Econst_int (Int.repr 7) tint)
                                            tuint)))
                                      (Sifthenelse (Ebinop Olt
                                                     (Etempvar _which tuint)
                                                     (Econst_int (Int.repr 5) tint)
                                                     tint)
                                        (Ssequence
                                          (Scall (Some _t'6)
                                            (Evar _nondet_u32 (Tfunction nil
                                                                tuint
                                                                cc_default))
                                            nil)
                                          (Ssequence
                                            (Sset _t'46
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Evar _ap_params (tarray tint 5))
                                                  (Etempvar _which tuint)
                                                  (tptr tint)) tint))
                                            (Scall None
                                              (Evar _ZSTD_DCtx_setParameter 
                                              (Tfunction
                                                ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
                                                 tint :: tint :: nil) tulong
                                                cc_default))
                                              ((Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
                                               (Etempvar _t'46 tint) ::
                                               (Ecast (Etempvar _t'6 tuint)
                                                 tint) :: nil))))
                                        (Sifthenelse (Ebinop Oeq
                                                       (Etempvar _which tuint)
                                                       (Econst_int (Int.repr 5) tint)
                                                       tint)
                                          (Ssequence
                                            (Ssequence
                                              (Ssequence
                                                (Scall (Some _t'7)
                                                  (Evar _nondet_u32 (Tfunction
                                                                    nil tuint
                                                                    cc_default))
                                                  nil)
                                                (Scall (Some _t'8)
                                                  (Evar _nondet_u32 (Tfunction
                                                                    nil tuint
                                                                    cc_default))
                                                  nil))
                                              (Sifthenelse (Ebinop Omod
                                                             (Etempvar _t'8 tuint)
                                                             (Econst_int (Int.repr 2) tint)
                                                             tuint)
                                                (Sset _t'9
                                                  (Ecast
                                                    (Econst_int (Int.repr 0) tint)
                                                    tint))
                                                (Sset _t'9
                                                  (Ecast
                                                    (Econst_int (Int.repr 8) tint)
                                                    tint))))
                                            (Scall None
                                              (Evar _ZSTD_DCtx_setMaxWindowSize 
                                              (Tfunction
                                                ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
                                                 tulong :: nil) tulong
                                                cc_default))
                                              ((Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
                                               (Ebinop Oshl
                                                 (Ecast (Etempvar _t'7 tuint)
                                                   tulong)
                                                 (Etempvar _t'9 tint) tulong) ::
                                               nil)))
                                          (Ssequence
                                            (Sset _t'42
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Evar _dd (tarray (tptr (Tstruct _ZSTD_DDict_s noattr)) 2))
                                                  (Ebinop Omod
                                                    (Etempvar _i tuint)
                                                    (Econst_int (Int.repr 2) tint)
                                                    tuint)
                                                  (tptr (tptr (Tstruct _ZSTD_DDict_s noattr))))
                                                (tptr (Tstruct _ZSTD_DDict_s noattr))))
                                            (Sifthenelse (Ebinop Oeq
                                                           (Etempvar _t'42 (tptr (Tstruct _ZSTD_DDict_s noattr)))
                                                           (Ecast
                                                             (Econst_int (Int.repr 0) tint)
                                                             (tptr tvoid))
                                                           tint)
                                              (Ssequence
                                                (Ssequence
                                                  (Scall (Some _t'10)
                                                    (Evar _nondet_u32 
                                                    (Tfunction nil tuint
                                                      cc_default)) nil)
                                                  (Sset _dn
                                                    (Ecast
                                                      (Ebinop Omod
                                                        (Etempvar _t'10 tuint)
                                                        (Ebinop Oadd
                                                          (Econst_int (Int.repr 512) tint)
                                                          (Econst_int (Int.repr 1) tint)
                                                          tint) tuint)
                                                      tulong)))
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _t'45
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _dbuf (tarray (tptr tuchar) 2))
                                                          (Ebinop Omod
                                                            (Etempvar _i tuint)
                                                            (Econst_int (Int.repr 2) tint)
                                                            tuint)
                                                          (tptr (tptr tuchar)))
                                                        (tptr tuchar)))
                                                    (Scall None
                                                      (Evar _quickproof_free 
                                                      (Tfunction
                                                        ((tptr tvoid) :: nil)
                                                        tvoid cc_default))
                                                      ((Etempvar _t'45 (tptr tuchar)) ::
                                                       nil)))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sifthenelse 
                                                          (Ebinop Ogt
                                                            (Etempvar _dn tulong)
                                                            (Econst_int (Int.repr 0) tint)
                                                            tint)
                                                          (Sset _t'11
                                                            (Ecast
                                                              (Etempvar _dn tulong)
                                                              tulong))
                                                          (Sset _t'11
                                                            (Ecast
                                                              (Econst_int (Int.repr 1) tint)
                                                              tulong)))
                                                        (Scall (Some _t'12)
                                                          (Evar _quickproof_malloc 
                                                          (Tfunction
                                                            (tulong :: nil)
                                                            (tptr tvoid)
                                                            cc_default))
                                                          ((Etempvar _t'11 tulong) ::
                                                           nil)))
                                                      (Sset _d
                                                        (Etempvar _t'12 (tptr tvoid))))
                                                    (Ssequence
                                                      (Sassign
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _dbuf (tarray (tptr tuchar) 2))
                                                            (Ebinop Omod
                                                              (Etempvar _i tuint)
                                                              (Econst_int (Int.repr 2) tint)
                                                              tuint)
                                                            (tptr (tptr tuchar)))
                                                          (tptr tuchar))
                                                        (Etempvar _d (tptr tuchar)))
                                                      (Sifthenelse (Ebinop One
                                                                    (Etempvar _d (tptr tuchar))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                        (Ssequence
                                                          (Scall None
                                                            (Evar _nondet_bytes 
                                                            (Tfunction
                                                              ((tptr tuchar) ::
                                                               tulong :: nil)
                                                              tvoid
                                                              cc_default))
                                                            ((Etempvar _d (tptr tuchar)) ::
                                                             (Etempvar _dn tulong) ::
                                                             nil))
                                                          (Ssequence
                                                            (Ssequence
                                                              (Scall (Some _t'13)
                                                                (Evar _ZSTD_createDDict 
                                                                (Tfunction
                                                                  ((tptr tvoid) ::
                                                                   tulong ::
                                                                   nil)
                                                                  (tptr (Tstruct _ZSTD_DDict_s noattr))
                                                                  cc_default))
                                                                ((Etempvar _d (tptr tuchar)) ::
                                                                 (Etempvar _dn tulong) ::
                                                                 nil))
                                                              (Sassign
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Evar _dd (tarray (tptr (Tstruct _ZSTD_DDict_s noattr)) 2))
                                                                    (Ebinop Omod
                                                                    (Etempvar _i tuint)
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tuint)
                                                                    (tptr (tptr (Tstruct _ZSTD_DDict_s noattr))))
                                                                  (tptr (Tstruct _ZSTD_DDict_s noattr)))
                                                                (Etempvar _t'13 (tptr (Tstruct _ZSTD_DDict_s noattr)))))
                                                            (Ssequence
                                                              (Sset _t'43
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Evar _dd (tarray (tptr (Tstruct _ZSTD_DDict_s noattr)) 2))
                                                                    (Ebinop Omod
                                                                    (Etempvar _i tuint)
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tuint)
                                                                    (tptr (tptr (Tstruct _ZSTD_DDict_s noattr))))
                                                                  (tptr (Tstruct _ZSTD_DDict_s noattr))))
                                                              (Sifthenelse 
                                                                (Ebinop One
                                                                  (Etempvar _t'43 (tptr (Tstruct _ZSTD_DDict_s noattr)))
                                                                  (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                  tint)
                                                                (Ssequence
                                                                  (Sset _t'44
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _dd (tarray (tptr (Tstruct _ZSTD_DDict_s noattr)) 2))
                                                                    (Ebinop Omod
                                                                    (Etempvar _i tuint)
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tuint)
                                                                    (tptr (tptr (Tstruct _ZSTD_DDict_s noattr))))
                                                                    (tptr (Tstruct _ZSTD_DDict_s noattr))))
                                                                  (Scall None
                                                                    (Evar _ZSTD_DCtx_refDDict 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
                                                                    (tptr (Tstruct _ZSTD_DDict_s noattr)) ::
                                                                    nil)
                                                                    tulong
                                                                    cc_default))
                                                                    ((Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
                                                                    (Etempvar _t'44 (tptr (Tstruct _ZSTD_DDict_s noattr))) ::
                                                                    nil)))
                                                                Sskip))))
                                                        Sskip)))))
                                              Sskip))))))
                                  (Sset _i
                                    (Ebinop Oadd (Etempvar _i tuint)
                                      (Econst_int (Int.repr 1) tint) tuint))))
                              (Ssequence
                                (Ssequence
                                  (Scall (Some _t'30)
                                    (Evar _nondet_u32 (Tfunction nil tuint
                                                        cc_default)) nil)
                                  (Sifthenelse (Ebinop Omod
                                                 (Etempvar _t'30 tuint)
                                                 (Econst_int (Int.repr 2) tint)
                                                 tuint)
                                    (Ssequence
                                      (Ssequence
                                        (Ssequence
                                          (Sifthenelse (Ebinop Ogt
                                                         (Etempvar _cap tulong)
                                                         (Econst_int (Int.repr 0) tint)
                                                         tint)
                                            (Sset _t'14
                                              (Ecast (Etempvar _cap tulong)
                                                tulong))
                                            (Sset _t'14
                                              (Ecast
                                                (Econst_int (Int.repr 1) tint)
                                                tulong)))
                                          (Scall (Some _t'15)
                                            (Evar _quickproof_malloc 
                                            (Tfunction (tulong :: nil)
                                              (tptr tvoid) cc_default))
                                            ((Etempvar _t'14 tulong) :: nil)))
                                        (Sset _dst
                                          (Etempvar _t'15 (tptr tvoid))))
                                      (Sifthenelse (Ebinop One
                                                     (Etempvar _dst (tptr tuchar))
                                                     (Ecast
                                                       (Econst_int (Int.repr 0) tint)
                                                       (tptr tvoid)) tint)
                                        (Ssequence
                                          (Ssequence
                                            (Scall (Some _t'16)
                                              (Evar _ZSTD_decompressDCtx 
                                              (Tfunction
                                                ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
                                                 (tptr tvoid) :: tulong ::
                                                 (tptr tvoid) :: tulong ::
                                                 nil) tulong cc_default))
                                              ((Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
                                               (Etempvar _dst (tptr tuchar)) ::
                                               (Etempvar _cap tulong) ::
                                               (Etempvar _src (tptr tuchar)) ::
                                               (Etempvar _n tulong) :: nil))
                                            (Sset _r (Etempvar _t'16 tulong)))
                                          (Ssequence
                                            (Ssequence
                                              (Scall (Some _t'17)
                                                (Evar _ZSTD_isError (Tfunction
                                                                    (tulong ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                ((Etempvar _r tulong) :: nil))
                                              (Sifthenelse (Etempvar _t'17 tuint)
                                                (Sset _t'18
                                                  (Econst_int (Int.repr 1) tint))
                                                (Sset _t'18
                                                  (Ecast
                                                    (Ebinop Ole
                                                      (Etempvar _r tulong)
                                                      (Etempvar _cap tulong)
                                                      tint) tbool))))
                                            (Scall None
                                              (Evar _gp_assert (Tfunction
                                                                 (tint ::
                                                                  nil) tvoid
                                                                 cc_default))
                                              ((Etempvar _t'18 tint) :: nil))))
                                        Sskip))
                                    (Ssequence
                                      (Sset _calls
                                        (Econst_int (Int.repr 0) tint))
                                      (Sloop
                                        (Ssequence
                                          (Ssequence
                                            (Sifthenelse (Ebinop Olt
                                                           (Etempvar _calls tuint)
                                                           (Econst_int (Int.repr 512) tint)
                                                           tint)
                                              (Sset _t'19
                                                (Ecast
                                                  (Ebinop Ole
                                                    (Etempvar _got tulong)
                                                    (Etempvar _cap tulong)
                                                    tint) tbool))
                                              (Sset _t'19
                                                (Econst_int (Int.repr 0) tint)))
                                            (Sifthenelse (Etempvar _t'19 tint)
                                              Sskip
                                              Sbreak))
                                          (Ssequence
                                            (Ssequence
                                              (Scall (Some _t'20)
                                                (Evar _nondet_u32 (Tfunction
                                                                    nil tuint
                                                                    cc_default))
                                                nil)
                                              (Sset _ilen
                                                (Ecast
                                                  (Ebinop Omod
                                                    (Etempvar _t'20 tuint)
                                                    (Ebinop Oadd
                                                      (Econst_int (Int.repr 256) tint)
                                                      (Econst_int (Int.repr 1) tint)
                                                      tint) tuint) tulong)))
                                            (Ssequence
                                              (Ssequence
                                                (Scall (Some _t'21)
                                                  (Evar _nondet_u32 (Tfunction
                                                                    nil tuint
                                                                    cc_default))
                                                  nil)
                                                (Sset _olen
                                                  (Ecast
                                                    (Ebinop Oadd
                                                      (Ebinop Omod
                                                        (Etempvar _t'21 tuint)
                                                        (Econst_int (Int.repr 256) tint)
                                                        tuint)
                                                      (Econst_int (Int.repr 1) tint)
                                                      tuint) tulong)))
                                              (Ssequence
                                                (Sifthenelse (Ebinop Ogt
                                                               (Etempvar _ilen tulong)
                                                               (Ebinop Osub
                                                                 (Etempvar _n tulong)
                                                                 (Etempvar _ipos tulong)
                                                                 tulong)
                                                               tint)
                                                  (Sset _ilen
                                                    (Ebinop Osub
                                                      (Etempvar _n tulong)
                                                      (Etempvar _ipos tulong)
                                                      tulong))
                                                  Sskip)
                                                (Ssequence
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sifthenelse (Ebinop Ogt
                                                                    (Etempvar _ilen tulong)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                        (Sset _t'22
                                                          (Ecast
                                                            (Etempvar _ilen tulong)
                                                            tulong))
                                                        (Sset _t'22
                                                          (Ecast
                                                            (Econst_int (Int.repr 1) tint)
                                                            tulong)))
                                                      (Scall (Some _t'23)
                                                        (Evar _quickproof_malloc 
                                                        (Tfunction
                                                          (tulong :: nil)
                                                          (tptr tvoid)
                                                          cc_default))
                                                        ((Etempvar _t'22 tulong) ::
                                                         nil)))
                                                    (Sset _ib
                                                      (Etempvar _t'23 (tptr tvoid))))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Scall (Some _t'24)
                                                        (Evar _quickproof_malloc 
                                                        (Tfunction
                                                          (tulong :: nil)
                                                          (tptr tvoid)
                                                          cc_default))
                                                        ((Etempvar _olen tulong) ::
                                                         nil))
                                                      (Sset _ob
                                                        (Etempvar _t'24 (tptr tvoid))))
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sifthenelse 
                                                          (Ebinop Oeq
                                                            (Etempvar _ib (tptr tuchar))
                                                            (Ecast
                                                              (Econst_int (Int.repr 0) tint)
                                                              (tptr tvoid))
                                                            tint)
                                                          (Sset _t'25
                                                            (Econst_int (Int.repr 1) tint))
                                                          (Sset _t'25
                                                            (Ecast
                                                              (Ebinop Oeq
                                                                (Etempvar _ob (tptr tuchar))
                                                                (Ecast
                                                                  (Econst_int (Int.repr 0) tint)
                                                                  (tptr tvoid))
                                                                tint) tbool)))
                                                        (Sifthenelse (Etempvar _t'25 tint)
                                                          (Ssequence
                                                            (Scall None
                                                              (Evar _quickproof_free 
                                                              (Tfunction
                                                                ((tptr tvoid) ::
                                                                 nil) tvoid
                                                                cc_default))
                                                              ((Etempvar _ib (tptr tuchar)) ::
                                                               nil))
                                                            (Ssequence
                                                              (Scall None
                                                                (Evar _quickproof_free 
                                                                (Tfunction
                                                                  ((tptr tvoid) ::
                                                                   nil) tvoid
                                                                  cc_default))
                                                                ((Etempvar _ob (tptr tuchar)) ::
                                                                 nil))
                                                              Sbreak))
                                                          Sskip))
                                                      (Ssequence
                                                        (Ssequence
                                                          (Sset _i
                                                            (Econst_int (Int.repr 0) tint))
                                                          (Sloop
                                                            (Ssequence
                                                              (Sifthenelse 
                                                                (Ebinop Olt
                                                                  (Etempvar _i tuint)
                                                                  (Etempvar _ilen tulong)
                                                                  tint)
                                                                Sskip
                                                                Sbreak)
                                                              (Ssequence
                                                                (Sset _t'41
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _src (tptr tuchar))
                                                                    (Ebinop Oadd
                                                                    (Etempvar _ipos tulong)
                                                                    (Etempvar _i tuint)
                                                                    tulong)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                (Sassign
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _ib (tptr tuchar))
                                                                    (Etempvar _i tuint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                  (Etempvar _t'41 tuchar))))
                                                            (Sset _i
                                                              (Ebinop Oadd
                                                                (Etempvar _i tuint)
                                                                (Econst_int (Int.repr 1) tint)
                                                                tuint))))
                                                        (Ssequence
                                                          (Sassign
                                                            (Efield
                                                              (Evar _in (Tstruct _ZSTD_inBuffer_s noattr))
                                                              _src
                                                              (tptr tvoid))
                                                            (Etempvar _ib (tptr tuchar)))
                                                          (Ssequence
                                                            (Sassign
                                                              (Efield
                                                                (Evar _in (Tstruct _ZSTD_inBuffer_s noattr))
                                                                _size tulong)
                                                              (Etempvar _ilen tulong))
                                                            (Ssequence
                                                              (Sassign
                                                                (Efield
                                                                  (Evar _in (Tstruct _ZSTD_inBuffer_s noattr))
                                                                  _pos
                                                                  tulong)
                                                                (Econst_int (Int.repr 0) tint))
                                                              (Ssequence
                                                                (Sassign
                                                                  (Efield
                                                                    (Evar _out (Tstruct _ZSTD_outBuffer_s noattr))
                                                                    _dst
                                                                    (tptr tvoid))
                                                                  (Etempvar _ob (tptr tuchar)))
                                                                (Ssequence
                                                                  (Sassign
                                                                    (Efield
                                                                    (Evar _out (Tstruct _ZSTD_outBuffer_s noattr))
                                                                    _size
                                                                    tulong)
                                                                    (Etempvar _olen tulong))
                                                                  (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _out (Tstruct _ZSTD_outBuffer_s noattr))
                                                                    _pos
                                                                    tulong)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'26)
                                                                    (Evar _ZSTD_decompressStream 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
                                                                    (tptr (Tstruct _ZSTD_outBuffer_s noattr)) ::
                                                                    (tptr (Tstruct _ZSTD_inBuffer_s noattr)) ::
                                                                    nil)
                                                                    tulong
                                                                    cc_default))
                                                                    ((Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
                                                                    (Eaddrof
                                                                    (Evar _out (Tstruct _ZSTD_outBuffer_s noattr))
                                                                    (tptr (Tstruct _ZSTD_outBuffer_s noattr))) ::
                                                                    (Eaddrof
                                                                    (Evar _in (Tstruct _ZSTD_inBuffer_s noattr))
                                                                    (tptr (Tstruct _ZSTD_inBuffer_s noattr))) ::
                                                                    nil))
                                                                    (Sset _r
                                                                    (Etempvar _t'26 tulong)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'39
                                                                    (Efield
                                                                    (Evar _in (Tstruct _ZSTD_inBuffer_s noattr))
                                                                    _pos
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _t'40
                                                                    (Efield
                                                                    (Evar _in (Tstruct _ZSTD_inBuffer_s noattr))
                                                                    _size
                                                                    tulong))
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Ebinop Ole
                                                                    (Etempvar _t'39 tulong)
                                                                    (Etempvar _t'40 tulong)
                                                                    tint) ::
                                                                    nil))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'37
                                                                    (Efield
                                                                    (Evar _out (Tstruct _ZSTD_outBuffer_s noattr))
                                                                    _pos
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _t'38
                                                                    (Efield
                                                                    (Evar _out (Tstruct _ZSTD_outBuffer_s noattr))
                                                                    _size
                                                                    tulong))
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Ebinop Ole
                                                                    (Etempvar _t'37 tulong)
                                                                    (Etempvar _t'38 tulong)
                                                                    tint) ::
                                                                    nil))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'36
                                                                    (Efield
                                                                    (Evar _in (Tstruct _ZSTD_inBuffer_s noattr))
                                                                    _pos
                                                                    tulong))
                                                                    (Sset _ipos
                                                                    (Ebinop Oadd
                                                                    (Etempvar _ipos tulong)
                                                                    (Etempvar _t'36 tulong)
                                                                    tulong)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'35
                                                                    (Efield
                                                                    (Evar _out (Tstruct _ZSTD_outBuffer_s noattr))
                                                                    _pos
                                                                    tulong))
                                                                    (Sset _got
                                                                    (Ebinop Oadd
                                                                    (Etempvar _got tulong)
                                                                    (Etempvar _t'35 tulong)
                                                                    tulong)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _quickproof_free 
                                                                    (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _ib (tptr tuchar)) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _quickproof_free 
                                                                    (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _ob (tptr tuchar)) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'27)
                                                                    (Evar _ZSTD_isError 
                                                                    (Tfunction
                                                                    (tulong ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                    ((Etempvar _r tulong) ::
                                                                    nil))
                                                                    (Sifthenelse (Etempvar _t'27 tuint)
                                                                    (Scall None
                                                                    (Evar _ZSTD_DCtx_reset 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
                                                                    tint ::
                                                                    nil)
                                                                    tulong
                                                                    cc_default))
                                                                    ((Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
                                                                    (Econst_int (Int.repr 1) tint) ::
                                                                    nil))
                                                                    Sskip))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _ipos tulong)
                                                                    (Etempvar _n tulong)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _t'34
                                                                    (Efield
                                                                    (Evar _in (Tstruct _ZSTD_inBuffer_s noattr))
                                                                    _pos
                                                                    tulong))
                                                                    (Sset _t'28
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'34 tulong)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    tbool)))
                                                                    (Sset _t'28
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                    (Sifthenelse (Etempvar _t'28 tint)
                                                                    (Ssequence
                                                                    (Sset _t'33
                                                                    (Efield
                                                                    (Evar _out (Tstruct _ZSTD_outBuffer_s noattr))
                                                                    _pos
                                                                    tulong))
                                                                    (Sset _t'29
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'33 tulong)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    tbool)))
                                                                    (Sset _t'29
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse (Etempvar _t'29 tint)
                                                                    Sbreak
                                                                    Sskip))))))))))))))))))))))))
                                        (Sset _calls
                                          (Ebinop Oadd
                                            (Etempvar _calls tuint)
                                            (Econst_int (Int.repr 1) tint)
                                            tuint))))))
                                (Ssequence
                                  (Scall None
                                    (Evar _ZSTD_freeDCtx (Tfunction
                                                           ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
                                                            nil) tulong
                                                           cc_default))
                                    ((Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
                                     nil))
                                  (Ssequence
                                    (Ssequence
                                      (Sset _i
                                        (Econst_int (Int.repr 0) tint))
                                      (Sloop
                                        (Ssequence
                                          (Sifthenelse (Ebinop Olt
                                                         (Etempvar _i tuint)
                                                         (Econst_int (Int.repr 2) tint)
                                                         tint)
                                            Sskip
                                            Sbreak)
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'32
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Evar _dd (tarray (tptr (Tstruct _ZSTD_DDict_s noattr)) 2))
                                                    (Etempvar _i tuint)
                                                    (tptr (tptr (Tstruct _ZSTD_DDict_s noattr))))
                                                  (tptr (Tstruct _ZSTD_DDict_s noattr))))
                                              (Scall None
                                                (Evar _ZSTD_freeDDict 
                                                (Tfunction
                                                  ((tptr (Tstruct _ZSTD_DDict_s noattr)) ::
                                                   nil) tulong cc_default))
                                                ((Etempvar _t'32 (tptr (Tstruct _ZSTD_DDict_s noattr))) ::
                                                 nil)))
                                            (Ssequence
                                              (Sset _t'31
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Evar _dbuf (tarray (tptr tuchar) 2))
                                                    (Etempvar _i tuint)
                                                    (tptr (tptr tuchar)))
                                                  (tptr tuchar)))
                                              (Scall None
                                                (Evar _quickproof_free 
                                                (Tfunction
                                                  ((tptr tvoid) :: nil) tvoid
                                                  cc_default))
                                                ((Etempvar _t'31 (tptr tuchar)) ::
                                                 nil)))))
                                        (Sset _i
                                          (Ebinop Oadd (Etempvar _i tuint)
                                            (Econst_int (Int.repr 1) tint)
                                            tuint))))
                                    (Ssequence
                                      (Scall None
                                        (Evar _quickproof_free (Tfunction
                                                                 ((tptr tvoid) ::
                                                                  nil) tvoid
                                                                 cc_default))
                                        ((Etempvar _dst (tptr tuchar)) ::
                                         nil))
                                      (Ssequence
                                        (Scall None
                                          (Evar _quickproof_free (Tfunction
                                                                   ((tptr tvoid) ::
                                                                    nil)
                                                                   tvoid
                                                                   cc_default))
                                          ((Etempvar _src (tptr tuchar)) ::
                                           nil))
                                        (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))))))))))))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition composites : list composite_definition :=
(Composite _ZSTD_inBuffer_s Struct
   (Member_plain _src (tptr tvoid) :: Member_plain _size tulong ::
    Member_plain _pos tulong :: nil)
   noattr ::
 Composite _ZSTD_outBuffer_s Struct
   (Member_plain _dst (tptr tvoid) :: Member_plain _size tulong ::
    Member_plain _pos tulong :: nil)
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
 (_nondet_u32,
   Gfun(External (EF_external "nondet_u32"
                   (mksignature nil AST.Xint cc_default)) nil tuint
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
 (_gp_assume,
   Gfun(External (EF_external "gp_assume"
                   (mksignature (AST.Xint :: nil) AST.Xvoid cc_default))
     (tint :: nil) tvoid cc_default)) ::
 (_ZSTD_isError,
   Gfun(External (EF_external "ZSTD_isError"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tuint cc_default)) ::
 (_ZSTD_createDCtx,
   Gfun(External (EF_external "ZSTD_createDCtx"
                   (mksignature nil AST.Xptr cc_default)) nil
     (tptr (Tstruct _ZSTD_DCtx_s noattr)) cc_default)) ::
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
 (_ZSTD_DCtx_setParameter,
   Gfun(External (EF_external "ZSTD_DCtx_setParameter"
                   (mksignature (AST.Xptr :: AST.Xint :: AST.Xint :: nil)
                     AST.Xlong cc_default))
     ((tptr (Tstruct _ZSTD_DCtx_s noattr)) :: tint :: tint :: nil) tulong
     cc_default)) ::
 (_ZSTD_DCtx_reset,
   Gfun(External (EF_external "ZSTD_DCtx_reset"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xlong
                     cc_default))
     ((tptr (Tstruct _ZSTD_DCtx_s noattr)) :: tint :: nil) tulong
     cc_default)) ::
 (_ZSTD_decompressStream,
   Gfun(External (EF_external "ZSTD_decompressStream"
                   (mksignature (AST.Xptr :: AST.Xptr :: AST.Xptr :: nil)
                     AST.Xlong cc_default))
     ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
      (tptr (Tstruct _ZSTD_outBuffer_s noattr)) ::
      (tptr (Tstruct _ZSTD_inBuffer_s noattr)) :: nil) tulong cc_default)) ::
 (_ZSTD_createDDict,
   Gfun(External (EF_external "ZSTD_createDDict"
                   (mksignature (AST.Xptr :: AST.Xlong :: nil) AST.Xptr
                     cc_default)) ((tptr tvoid) :: tulong :: nil)
     (tptr (Tstruct _ZSTD_DDict_s noattr)) cc_default)) ::
 (_ZSTD_freeDDict,
   Gfun(External (EF_external "ZSTD_freeDDict"
                   (mksignature (AST.Xptr :: nil) AST.Xlong cc_default))
     ((tptr (Tstruct _ZSTD_DDict_s noattr)) :: nil) tulong cc_default)) ::
 (_ZSTD_DCtx_refDDict,
   Gfun(External (EF_external "ZSTD_DCtx_refDDict"
                   (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xlong
                     cc_default))
     ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
      (tptr (Tstruct _ZSTD_DDict_s noattr)) :: nil) tulong cc_default)) ::
 (_ZSTD_DCtx_setMaxWindowSize,
   Gfun(External (EF_external "ZSTD_DCtx_setMaxWindowSize"
                   (mksignature (AST.Xptr :: AST.Xlong :: nil) AST.Xlong
                     cc_default))
     ((tptr (Tstruct _ZSTD_DCtx_s noattr)) :: tulong :: nil) tulong
     cc_default)) :: (_ap_params, Gvar v_ap_params) ::
 (_main, Gfun(Internal f_main)) :: nil).

Definition public_idents : list ident :=
(_main :: _ZSTD_DCtx_setMaxWindowSize :: _ZSTD_DCtx_refDDict ::
 _ZSTD_freeDDict :: _ZSTD_createDDict :: _ZSTD_decompressStream ::
 _ZSTD_DCtx_reset :: _ZSTD_DCtx_setParameter :: _ZSTD_decompressDCtx ::
 _ZSTD_freeDCtx :: _ZSTD_createDCtx :: _ZSTD_isError :: _gp_assume ::
 _gp_assert :: _nondet_bytes :: _nondet_size :: _nondet_u32 ::
 _quickproof_free :: _quickproof_malloc :: ___builtin_debug ::
 ___builtin_write32_reversed :: ___builtin_write16_reversed ::
 ___builtin_read32_reversed :: ___builtin_read16_reversed ::
 ___builtin_fnmsub :: ___builtin_fnmadd :: ___builtin_fmsub ::
 ___builtin_fmadd :: ___builtin_fmin :: ___builtin_fmax ::
 ___builtin_expect :: ___builtin_unreachable :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_sel :: ___builtin_memcpy_aligned :: ___builtin_sqrt ::
 ___builtin_fsqrt :: ___builtin_fabsf :: ___builtin_fabs ::
 ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll ::
 ___builtin_clzl :: ___builtin_clz :: ___builtin_bswap16 ::
 ___builtin_bswap32 :: ___builtin_bswap :: ___builtin_bswap64 ::
 ___builtin_ais_annot :: ___compcert_i64_umulh :: ___compcert_i64_smulh ::
 ___compcert_i64_sar :: ___compcert_i64_shr :: ___compcert_i64_shl ::
 ___compcert_i64_umod :: ___compcert_i64_smod :: ___compcert_i64_udiv ::
 ___compcert_i64_sdiv :: ___compcert_i64_utof :: ___compcert_i64_stof ::
 ___compcert_i64_utod :: ___compcert_i64_stod :: ___compcert_i64_dtou ::
 ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


