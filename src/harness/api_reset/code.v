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
  Definition source_file := "harness/api_reset.c".
  Definition normalized := true.
End Info.

Definition _ZSTD_DCtx_loadDictionary : ident := $"ZSTD_DCtx_loadDictionary".
Definition _ZSTD_DCtx_reset : ident := $"ZSTD_DCtx_reset".
Definition _ZSTD_DCtx_s : ident := $"ZSTD_DCtx_s".
Definition _ZSTD_DCtx_setParameter : ident := $"ZSTD_DCtx_setParameter".
Definition _ZSTD_createDCtx : ident := $"ZSTD_createDCtx".
Definition _ZSTD_decompressDCtx : ident := $"ZSTD_decompressDCtx".
Definition _ZSTD_decompressStream : ident := $"ZSTD_decompressStream".
Definition _ZSTD_getErrorCode : ident := $"ZSTD_getErrorCode".
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
Definition _a : ident := $"a".
Definition _any_bytes : ident := $"any_bytes".
Definition _b : ident := $"b".
Definition _bytes : ident := $"bytes".
Definition _bytes_eq : ident := $"bytes_eq".
Definition _cap : ident := $"cap".
Definition _dst : ident := $"dst".
Definition _expected : ident := $"expected".
Definition _fresh : ident := $"fresh".
Definition _gp_assert : ident := $"gp_assert".
Definition _i : ident := $"i".
Definition _in : ident := $"in".
Definition _in2 : ident := $"in2".
Definition _main : ident := $"main".
Definition _max : ident := $"max".
Definition _n : ident := $"n".
Definition _nondet_bytes : ident := $"nondet_bytes".
Definition _nondet_size : ident := $"nondet_size".
Definition _nondet_u32 : ident := $"nondet_u32".
Definition _nondet_u8 : ident := $"nondet_u8".
Definition _other : ident := $"other".
Definition _out : ident := $"out".
Definition _out2 : ident := $"out2".
Definition _out_of_memory : ident := $"out_of_memory".
Definition _pos : ident := $"pos".
Definition _quickproof_free : ident := $"quickproof_free".
Definition _quickproof_malloc : ident := $"quickproof_malloc".
Definition _result : ident := $"result".
Definition _size : ident := $"size".
Definition _src : ident := $"src".
Definition _upto : ident := $"upto".
Definition _used : ident := $"used".
Definition _value : ident := $"value".
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
Definition _t'47 : ident := 174%positive.
Definition _t'48 : ident := 175%positive.
Definition _t'49 : ident := 176%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'50 : ident := 177%positive.
Definition _t'51 : ident := 178%positive.
Definition _t'52 : ident := 179%positive.
Definition _t'53 : ident := 180%positive.
Definition _t'54 : ident := 181%positive.
Definition _t'55 : ident := 182%positive.
Definition _t'56 : ident := 183%positive.
Definition _t'57 : ident := 184%positive.
Definition _t'58 : ident := 185%positive.
Definition _t'59 : ident := 186%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'60 : ident := 187%positive.
Definition _t'61 : ident := 188%positive.
Definition _t'62 : ident := 189%positive.
Definition _t'63 : ident := 190%positive.
Definition _t'64 : ident := 191%positive.
Definition _t'65 : ident := 192%positive.
Definition _t'66 : ident := 193%positive.
Definition _t'67 : ident := 194%positive.
Definition _t'68 : ident := 195%positive.
Definition _t'69 : ident := 196%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'70 : ident := 197%positive.
Definition _t'71 : ident := 198%positive.
Definition _t'72 : ident := 199%positive.
Definition _t'73 : ident := 200%positive.
Definition _t'74 : ident := 201%positive.
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

Definition f_bytes_eq := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_a, (tptr tuchar)) :: (_b, (tptr tuchar)) :: (_n, tulong) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_i, tulong) :: (_t'2, tuchar) :: (_t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tulong) (Etempvar _n tulong)
                       tint)
          Sskip
          Sbreak)
        (Ssequence
          (Sset _t'1
            (Ederef
              (Ebinop Oadd (Etempvar _a (tptr tuchar)) (Etempvar _i tulong)
                (tptr tuchar)) tuchar))
          (Ssequence
            (Sset _t'2
              (Ederef
                (Ebinop Oadd (Etempvar _b (tptr tuchar)) (Etempvar _i tulong)
                  (tptr tuchar)) tuchar))
            (Sifthenelse (Ebinop One (Etempvar _t'1 tuchar)
                           (Etempvar _t'2 tuchar) tint)
              (Sreturn (Some (Econst_int (Int.repr 0) tint)))
              Sskip))))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tulong) (Econst_int (Int.repr 1) tint)
          tulong))))
  (Sreturn (Some (Econst_int (Int.repr 1) tint))))
|}.

Definition f_out_of_memory := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_result, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1)
    (Evar _ZSTD_getErrorCode (Tfunction (tulong :: nil) tint cc_default))
    ((Etempvar _result tulong) :: nil))
  (Sreturn (Some (Ebinop Oeq (Etempvar _t'1 tint)
                   (Econst_int (Int.repr 64) tint) tint))))
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := ((_in, (Tstruct _ZSTD_inBuffer_s noattr)) ::
              (_in2, (Tstruct _ZSTD_inBuffer_s noattr)) ::
              (_out, (Tstruct _ZSTD_outBuffer_s noattr)) ::
              (_out2, (Tstruct _ZSTD_outBuffer_s noattr)) :: nil);
  fn_temps := ((_used, (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
               (_fresh, (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
               (_n, tulong) :: (_cap, tulong) :: (_result, tulong) ::
               (_expected, tulong) :: (_src, (tptr tuchar)) ::
               (_dst, (tptr tuchar)) :: (_other, (tptr tuchar)) ::
               (_t'61, tint) :: (_t'60, tint) :: (_t'59, tint) ::
               (_t'58, tint) :: (_t'57, tuint) :: (_t'56, tuint) ::
               (_t'55, tuint) :: (_t'54, tint) :: (_t'53, tint) ::
               (_t'52, tint) :: (_t'51, tulong) :: (_t'50, tulong) ::
               (_t'49, tulong) :: (_t'48, tulong) :: (_t'47, tulong) ::
               (_t'46, tulong) :: (_t'45, tuchar) :: (_t'44, tint) ::
               (_t'43, tuint) :: (_t'42, tulong) :: (_t'41, tulong) ::
               (_t'40, (tptr tvoid)) :: (_t'39, tuchar) :: (_t'38, tint) ::
               (_t'37, tint) :: (_t'36, tuint) :: (_t'35, tuint) ::
               (_t'34, tuint) :: (_t'33, tint) :: (_t'32, tint) ::
               (_t'31, tint) :: (_t'30, tulong) :: (_t'29, tulong) ::
               (_t'28, tint) :: (_t'27, tint) :: (_t'26, (tptr tvoid)) ::
               (_t'25, (tptr tvoid)) :: (_t'24, tulong) ::
               (_t'23, (tptr tuchar)) :: (_t'22, tulong) :: (_t'21, tuint) ::
               (_t'20, tulong) :: (_t'19, tuint) :: (_t'18, tuchar) ::
               (_t'17, tuchar) :: (_t'16, tulong) :: (_t'15, tulong) ::
               (_t'14, tuchar) :: (_t'13, tint) :: (_t'12, tuint) ::
               (_t'11, tulong) :: (_t'10, tulong) :: (_t'9, tint) ::
               (_t'8, (tptr tvoid)) :: (_t'7, tulong) ::
               (_t'6, (tptr tuchar)) :: (_t'5, tulong) :: (_t'4, tuchar) ::
               (_t'3, tint) ::
               (_t'2, (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
               (_t'1, (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
               (_t'74, tulong) :: (_t'73, tulong) :: (_t'72, tulong) ::
               (_t'71, tulong) :: (_t'70, tulong) :: (_t'69, tulong) ::
               (_t'68, tulong) :: (_t'67, tulong) :: (_t'66, tulong) ::
               (_t'65, tulong) :: (_t'64, tulong) :: (_t'63, tulong) ::
               (_t'62, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _ZSTD_createDCtx (Tfunction nil
                                 (tptr (Tstruct _ZSTD_DCtx_s noattr))
                                 cc_default)) nil)
      (Sset _used (Etempvar _t'1 (tptr (Tstruct _ZSTD_DCtx_s noattr)))))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _ZSTD_createDCtx (Tfunction nil
                                   (tptr (Tstruct _ZSTD_DCtx_s noattr))
                                   cc_default)) nil)
        (Sset _fresh (Etempvar _t'2 (tptr (Tstruct _ZSTD_DCtx_s noattr)))))
      (Ssequence
        (Ssequence
          (Sifthenelse (Ebinop Oeq
                         (Etempvar _used (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                         (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                         tint)
            (Sset _t'3 (Econst_int (Int.repr 1) tint))
            (Sset _t'3
              (Ecast
                (Ebinop Oeq
                  (Etempvar _fresh (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                  (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
                tbool)))
          (Sifthenelse (Etempvar _t'3 tint)
            (Sreturn (Some (Econst_int (Int.repr 0) tint)))
            Sskip))
        (Ssequence
          (Sloop
            (Ssequence
              (Ssequence
                (Scall (Some _t'5)
                  (Evar _upto (Tfunction (tulong :: nil) tulong cc_default))
                  ((Econst_long (Int64.repr 9223372036854775807) tlong) ::
                   nil))
                (Sset _n (Etempvar _t'5 tulong)))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'6)
                    (Evar _any_bytes (Tfunction (tulong :: nil) (tptr tuchar)
                                       cc_default))
                    ((Etempvar _n tulong) :: nil))
                  (Sset _src (Etempvar _t'6 (tptr tuchar))))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'7)
                      (Evar _upto (Tfunction (tulong :: nil) tulong
                                    cc_default))
                      ((Econst_long (Int64.repr 9223372036854775807) tlong) ::
                       nil))
                    (Sset _cap (Etempvar _t'7 tulong)))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'8)
                        (Evar _quickproof_malloc (Tfunction (tulong :: nil)
                                                   (tptr tvoid) cc_default))
                        ((Etempvar _cap tulong) :: nil))
                      (Sset _dst (Etempvar _t'8 (tptr tvoid))))
                    (Ssequence
                      (Ssequence
                        (Sifthenelse (Ebinop Oeq
                                       (Etempvar _src (tptr tuchar))
                                       (Ecast (Econst_int (Int.repr 0) tint)
                                         (tptr tvoid)) tint)
                          (Sset _t'9 (Econst_int (Int.repr 1) tint))
                          (Sset _t'9
                            (Ecast
                              (Ebinop Oeq (Etempvar _dst (tptr tuchar))
                                (Ecast (Econst_int (Int.repr 0) tint)
                                  (tptr tvoid)) tint) tbool)))
                        (Sifthenelse (Etempvar _t'9 tint)
                          (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                          Sskip))
                      (Ssequence
                        (Sassign
                          (Efield
                            (Evar _in (Tstruct _ZSTD_inBuffer_s noattr)) _src
                            (tptr tvoid)) (Etempvar _src (tptr tuchar)))
                        (Ssequence
                          (Ssequence
                            (Ssequence
                              (Sset _t'10
                                (Ecast (Econst_int (Int.repr 0) tint) tulong))
                              (Sassign
                                (Efield
                                  (Evar _in (Tstruct _ZSTD_inBuffer_s noattr))
                                  _pos tulong) (Etempvar _t'10 tulong)))
                            (Sassign
                              (Efield
                                (Evar _in (Tstruct _ZSTD_inBuffer_s noattr))
                                _size tulong) (Etempvar _t'10 tulong)))
                          (Ssequence
                            (Sassign
                              (Efield
                                (Evar _out (Tstruct _ZSTD_outBuffer_s noattr))
                                _dst (tptr tvoid))
                              (Etempvar _dst (tptr tuchar)))
                            (Ssequence
                              (Sassign
                                (Efield
                                  (Evar _out (Tstruct _ZSTD_outBuffer_s noattr))
                                  _pos tulong)
                                (Econst_int (Int.repr 0) tint))
                              (Ssequence
                                (Ssequence
                                  (Scall (Some _t'17)
                                    (Evar _nondet_u8 (Tfunction nil tuchar
                                                       cc_default)) nil)
                                  (Sifthenelse (Ebinop Oand
                                                 (Etempvar _t'17 tuchar)
                                                 (Econst_int (Int.repr 1) tint)
                                                 tint)
                                    (Scall None
                                      (Evar _ZSTD_decompressDCtx (Tfunction
                                                                   ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
                                                                    (tptr tvoid) ::
                                                                    tulong ::
                                                                    (tptr tvoid) ::
                                                                    tulong ::
                                                                    nil)
                                                                   tulong
                                                                   cc_default))
                                      ((Etempvar _used (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
                                       (Etempvar _dst (tptr tuchar)) ::
                                       (Etempvar _cap tulong) ::
                                       (Etempvar _src (tptr tuchar)) ::
                                       (Etempvar _n tulong) :: nil))
                                    (Sloop
                                      (Ssequence
                                        (Ssequence
                                          (Ssequence
                                            (Sset _t'74
                                              (Efield
                                                (Evar _in (Tstruct _ZSTD_inBuffer_s noattr))
                                                _size tulong))
                                            (Scall (Some _t'15)
                                              (Evar _upto (Tfunction
                                                            (tulong :: nil)
                                                            tulong
                                                            cc_default))
                                              ((Ebinop Osub
                                                 (Etempvar _n tulong)
                                                 (Etempvar _t'74 tulong)
                                                 tulong) :: nil)))
                                          (Ssequence
                                            (Sset _t'73
                                              (Efield
                                                (Evar _in (Tstruct _ZSTD_inBuffer_s noattr))
                                                _size tulong))
                                            (Sassign
                                              (Efield
                                                (Evar _in (Tstruct _ZSTD_inBuffer_s noattr))
                                                _size tulong)
                                              (Ebinop Oadd
                                                (Etempvar _t'73 tulong)
                                                (Etempvar _t'15 tulong)
                                                tulong))))
                                        (Ssequence
                                          (Ssequence
                                            (Sset _t'72
                                              (Efield
                                                (Evar _out (Tstruct _ZSTD_outBuffer_s noattr))
                                                _pos tulong))
                                            (Scall (Some _t'16)
                                              (Evar _upto (Tfunction
                                                            (tulong :: nil)
                                                            tulong
                                                            cc_default))
                                              ((Ebinop Osub
                                                 (Etempvar _cap tulong)
                                                 (Etempvar _t'72 tulong)
                                                 tulong) :: nil)))
                                          (Ssequence
                                            (Sset _t'71
                                              (Efield
                                                (Evar _out (Tstruct _ZSTD_outBuffer_s noattr))
                                                _pos tulong))
                                            (Sassign
                                              (Efield
                                                (Evar _out (Tstruct _ZSTD_outBuffer_s noattr))
                                                _size tulong)
                                              (Ebinop Oadd
                                                (Etempvar _t'71 tulong)
                                                (Etempvar _t'16 tulong)
                                                tulong)))))
                                      (Ssequence
                                        (Ssequence
                                          (Ssequence
                                            (Scall (Some _t'11)
                                              (Evar _ZSTD_decompressStream 
                                              (Tfunction
                                                ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
                                                 (tptr (Tstruct _ZSTD_outBuffer_s noattr)) ::
                                                 (tptr (Tstruct _ZSTD_inBuffer_s noattr)) ::
                                                 nil) tulong cc_default))
                                              ((Etempvar _used (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
                                               (Eaddrof
                                                 (Evar _out (Tstruct _ZSTD_outBuffer_s noattr))
                                                 (tptr (Tstruct _ZSTD_outBuffer_s noattr))) ::
                                               (Eaddrof
                                                 (Evar _in (Tstruct _ZSTD_inBuffer_s noattr))
                                                 (tptr (Tstruct _ZSTD_inBuffer_s noattr))) ::
                                               nil))
                                            (Scall (Some _t'12)
                                              (Evar _ZSTD_isError (Tfunction
                                                                    (tulong ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                              ((Etempvar _t'11 tulong) ::
                                               nil)))
                                          (Sifthenelse (Eunop Onotbool
                                                         (Etempvar _t'12 tuint)
                                                         tint)
                                            (Ssequence
                                              (Scall (Some _t'14)
                                                (Evar _nondet_u8 (Tfunction
                                                                   nil tuchar
                                                                   cc_default))
                                                nil)
                                              (Sset _t'13
                                                (Ecast
                                                  (Ebinop One
                                                    (Etempvar _t'14 tuchar)
                                                    (Econst_int (Int.repr 0) tint)
                                                    tint) tbool)))
                                            (Sset _t'13
                                              (Econst_int (Int.repr 0) tint))))
                                        (Sifthenelse (Etempvar _t'13 tint)
                                          Sskip
                                          Sbreak)))))
                                (Ssequence
                                  (Scall None
                                    (Evar _ZSTD_DCtx_reset (Tfunction
                                                             ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
                                                              tint :: nil)
                                                             tulong
                                                             cc_default))
                                    ((Etempvar _used (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
                                     (Econst_int (Int.repr 1) tint) :: nil))
                                  (Ssequence
                                    (Ssequence
                                      (Scall (Some _t'18)
                                        (Evar _nondet_u8 (Tfunction nil
                                                           tuchar cc_default))
                                        nil)
                                      (Sifthenelse (Ebinop Oand
                                                     (Etempvar _t'18 tuchar)
                                                     (Econst_int (Int.repr 1) tint)
                                                     tint)
                                        (Scall None
                                          (Evar _ZSTD_DCtx_loadDictionary 
                                          (Tfunction
                                            ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
                                             (tptr tvoid) :: tulong :: nil)
                                            tulong cc_default))
                                          ((Etempvar _used (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
                                           (Etempvar _src (tptr tuchar)) ::
                                           (Etempvar _n tulong) :: nil))
                                        Sskip))
                                    (Ssequence
                                      (Ssequence
                                        (Scall (Some _t'19)
                                          (Evar _nondet_u32 (Tfunction nil
                                                              tuint
                                                              cc_default))
                                          nil)
                                        (Scall None
                                          (Evar _ZSTD_DCtx_setParameter 
                                          (Tfunction
                                            ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
                                             tint :: tint :: nil) tulong
                                            cc_default))
                                          ((Etempvar _used (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
                                           (Econst_int (Int.repr 100) tint) ::
                                           (Ecast (Etempvar _t'19 tuint)
                                             tint) :: nil)))
                                      (Ssequence
                                        (Scall None
                                          (Evar _quickproof_free (Tfunction
                                                                   ((tptr tvoid) ::
                                                                    nil)
                                                                   tvoid
                                                                   cc_default))
                                          ((Etempvar _src (tptr tuchar)) ::
                                           nil))
                                        (Scall None
                                          (Evar _quickproof_free (Tfunction
                                                                   ((tptr tvoid) ::
                                                                    nil)
                                                                   tvoid
                                                                   cc_default))
                                          ((Etempvar _dst (tptr tuchar)) ::
                                           nil))))))))))))))))
            (Ssequence
              (Scall (Some _t'4)
                (Evar _nondet_u8 (Tfunction nil tuchar cc_default)) nil)
              (Sifthenelse (Ebinop One (Etempvar _t'4 tuchar)
                             (Econst_int (Int.repr 0) tint) tint)
                Sskip
                Sbreak)))
          (Ssequence
            (Ssequence
              (Ssequence
                (Scall (Some _t'20)
                  (Evar _ZSTD_DCtx_reset (Tfunction
                                           ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
                                            tint :: nil) tulong cc_default))
                  ((Etempvar _used (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
                   (Econst_int (Int.repr 3) tint) :: nil))
                (Scall (Some _t'21)
                  (Evar _ZSTD_isError (Tfunction (tulong :: nil) tuint
                                        cc_default))
                  ((Etempvar _t'20 tulong) :: nil)))
              (Sifthenelse (Etempvar _t'21 tuint)
                (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                Sskip))
            (Ssequence
              (Ssequence
                (Scall (Some _t'22)
                  (Evar _upto (Tfunction (tulong :: nil) tulong cc_default))
                  ((Econst_long (Int64.repr 9223372036854775807) tlong) ::
                   nil))
                (Sset _n (Etempvar _t'22 tulong)))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'23)
                    (Evar _any_bytes (Tfunction (tulong :: nil) (tptr tuchar)
                                       cc_default))
                    ((Etempvar _n tulong) :: nil))
                  (Sset _src (Etempvar _t'23 (tptr tuchar))))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'24)
                      (Evar _upto (Tfunction (tulong :: nil) tulong
                                    cc_default))
                      ((Econst_long (Int64.repr 9223372036854775807) tlong) ::
                       nil))
                    (Sset _cap (Etempvar _t'24 tulong)))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'25)
                        (Evar _quickproof_malloc (Tfunction (tulong :: nil)
                                                   (tptr tvoid) cc_default))
                        ((Etempvar _cap tulong) :: nil))
                      (Sset _dst (Etempvar _t'25 (tptr tvoid))))
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'26)
                          (Evar _quickproof_malloc (Tfunction (tulong :: nil)
                                                     (tptr tvoid) cc_default))
                          ((Etempvar _cap tulong) :: nil))
                        (Sset _other (Etempvar _t'26 (tptr tvoid))))
                      (Ssequence
                        (Ssequence
                          (Ssequence
                            (Sifthenelse (Ebinop Oeq
                                           (Etempvar _src (tptr tuchar))
                                           (Ecast
                                             (Econst_int (Int.repr 0) tint)
                                             (tptr tvoid)) tint)
                              (Sset _t'27 (Econst_int (Int.repr 1) tint))
                              (Sset _t'27
                                (Ecast
                                  (Ebinop Oeq (Etempvar _dst (tptr tuchar))
                                    (Ecast (Econst_int (Int.repr 0) tint)
                                      (tptr tvoid)) tint) tbool)))
                            (Sifthenelse (Etempvar _t'27 tint)
                              (Sset _t'28 (Econst_int (Int.repr 1) tint))
                              (Sset _t'28
                                (Ecast
                                  (Ebinop Oeq (Etempvar _other (tptr tuchar))
                                    (Ecast (Econst_int (Int.repr 0) tint)
                                      (tptr tvoid)) tint) tbool))))
                          (Sifthenelse (Etempvar _t'28 tint)
                            (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                            Sskip))
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'39)
                              (Evar _nondet_u8 (Tfunction nil tuchar
                                                 cc_default)) nil)
                            (Sifthenelse (Ebinop Oand (Etempvar _t'39 tuchar)
                                           (Econst_int (Int.repr 1) tint)
                                           tint)
                              (Ssequence
                                (Ssequence
                                  (Scall (Some _t'29)
                                    (Evar _ZSTD_decompressDCtx (Tfunction
                                                                 ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
                                                                  (tptr tvoid) ::
                                                                  tulong ::
                                                                  (tptr tvoid) ::
                                                                  tulong ::
                                                                  nil) tulong
                                                                 cc_default))
                                    ((Etempvar _used (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
                                     (Etempvar _dst (tptr tuchar)) ::
                                     (Etempvar _cap tulong) ::
                                     (Etempvar _src (tptr tuchar)) ::
                                     (Etempvar _n tulong) :: nil))
                                  (Sset _result (Etempvar _t'29 tulong)))
                                (Ssequence
                                  (Ssequence
                                    (Scall (Some _t'30)
                                      (Evar _ZSTD_decompressDCtx (Tfunction
                                                                   ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
                                                                    (tptr tvoid) ::
                                                                    tulong ::
                                                                    (tptr tvoid) ::
                                                                    tulong ::
                                                                    nil)
                                                                   tulong
                                                                   cc_default))
                                      ((Etempvar _fresh (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
                                       (Etempvar _other (tptr tuchar)) ::
                                       (Etempvar _cap tulong) ::
                                       (Etempvar _src (tptr tuchar)) ::
                                       (Etempvar _n tulong) :: nil))
                                    (Sset _expected (Etempvar _t'30 tulong)))
                                  (Ssequence
                                    (Ssequence
                                      (Ssequence
                                        (Scall (Some _t'31)
                                          (Evar _out_of_memory (Tfunction
                                                                 (tulong ::
                                                                  nil) tint
                                                                 cc_default))
                                          ((Etempvar _result tulong) :: nil))
                                        (Sifthenelse (Etempvar _t'31 tint)
                                          (Sset _t'32
                                            (Econst_int (Int.repr 1) tint))
                                          (Ssequence
                                            (Scall (Some _t'33)
                                              (Evar _out_of_memory (Tfunction
                                                                    (tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                              ((Etempvar _expected tulong) ::
                                               nil))
                                            (Sset _t'32
                                              (Ecast (Etempvar _t'33 tint)
                                                tbool)))))
                                      (Sifthenelse (Etempvar _t'32 tint)
                                        (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                                        Sskip))
                                    (Ssequence
                                      (Ssequence
                                        (Ssequence
                                          (Scall (Some _t'34)
                                            (Evar _ZSTD_isError (Tfunction
                                                                  (tulong ::
                                                                   nil) tuint
                                                                  cc_default))
                                            ((Etempvar _result tulong) ::
                                             nil))
                                          (Sifthenelse (Etempvar _t'34 tuint)
                                            (Ssequence
                                              (Scall (Some _t'36)
                                                (Evar _ZSTD_isError (Tfunction
                                                                    (tulong ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                ((Etempvar _expected tulong) ::
                                                 nil))
                                              (Sset _t'35
                                                (Ecast (Etempvar _t'36 tuint)
                                                  tuint)))
                                            (Sifthenelse (Ebinop Oeq
                                                           (Etempvar _result tulong)
                                                           (Etempvar _expected tulong)
                                                           tint)
                                              (Ssequence
                                                (Ssequence
                                                  (Scall (Some _t'38)
                                                    (Evar _bytes_eq (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                    ((Etempvar _dst (tptr tuchar)) ::
                                                     (Etempvar _other (tptr tuchar)) ::
                                                     (Etempvar _result tulong) ::
                                                     nil))
                                                  (Sset _t'37
                                                    (Ecast
                                                      (Etempvar _t'38 tint)
                                                      tbool)))
                                                (Sset _t'35
                                                  (Ecast
                                                    (Etempvar _t'37 tint)
                                                    tuint)))
                                              (Sset _t'35
                                                (Ecast
                                                  (Econst_int (Int.repr 0) tint)
                                                  tuint)))))
                                        (Scall None
                                          (Evar _gp_assert (Tfunction
                                                             (tint :: nil)
                                                             tvoid
                                                             cc_default))
                                          ((Etempvar _t'35 tuint) :: nil)))
                                      (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))
                              Sskip))
                          (Ssequence
                            (Ssequence
                              (Ssequence
                                (Sset _t'40
                                  (Ecast (Etempvar _src (tptr tuchar))
                                    (tptr tvoid)))
                                (Sassign
                                  (Efield
                                    (Evar _in2 (Tstruct _ZSTD_inBuffer_s noattr))
                                    _src (tptr tvoid))
                                  (Etempvar _t'40 (tptr tvoid))))
                              (Sassign
                                (Efield
                                  (Evar _in (Tstruct _ZSTD_inBuffer_s noattr))
                                  _src (tptr tvoid))
                                (Etempvar _t'40 (tptr tvoid))))
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Sset _t'41
                                    (Ecast (Econst_int (Int.repr 0) tint)
                                      tulong))
                                  (Sassign
                                    (Efield
                                      (Evar _in2 (Tstruct _ZSTD_inBuffer_s noattr))
                                      _pos tulong) (Etempvar _t'41 tulong)))
                                (Sassign
                                  (Efield
                                    (Evar _in (Tstruct _ZSTD_inBuffer_s noattr))
                                    _pos tulong) (Etempvar _t'41 tulong)))
                              (Ssequence
                                (Sassign
                                  (Efield
                                    (Evar _out (Tstruct _ZSTD_outBuffer_s noattr))
                                    _dst (tptr tvoid))
                                  (Etempvar _dst (tptr tuchar)))
                                (Ssequence
                                  (Sassign
                                    (Efield
                                      (Evar _out2 (Tstruct _ZSTD_outBuffer_s noattr))
                                      _dst (tptr tvoid))
                                    (Etempvar _other (tptr tuchar)))
                                  (Ssequence
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'42
                                          (Ecast
                                            (Econst_int (Int.repr 0) tint)
                                            tulong))
                                        (Sassign
                                          (Efield
                                            (Evar _out2 (Tstruct _ZSTD_outBuffer_s noattr))
                                            _pos tulong)
                                          (Etempvar _t'42 tulong)))
                                      (Sassign
                                        (Efield
                                          (Evar _out (Tstruct _ZSTD_outBuffer_s noattr))
                                          _pos tulong)
                                        (Etempvar _t'42 tulong)))
                                    (Ssequence
                                      (Sloop
                                        (Ssequence
                                          (Ssequence
                                            (Ssequence
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'70
                                                    (Efield
                                                      (Evar _in (Tstruct _ZSTD_inBuffer_s noattr))
                                                      _pos tulong))
                                                  (Scall (Some _t'46)
                                                    (Evar _upto (Tfunction
                                                                  (tulong ::
                                                                   nil)
                                                                  tulong
                                                                  cc_default))
                                                    ((Ebinop Osub
                                                       (Etempvar _n tulong)
                                                       (Etempvar _t'70 tulong)
                                                       tulong) :: nil)))
                                                (Ssequence
                                                  (Sset _t'69
                                                    (Efield
                                                      (Evar _in (Tstruct _ZSTD_inBuffer_s noattr))
                                                      _pos tulong))
                                                  (Sset _t'47
                                                    (Ecast
                                                      (Ebinop Oadd
                                                        (Etempvar _t'69 tulong)
                                                        (Etempvar _t'46 tulong)
                                                        tulong) tulong))))
                                              (Sassign
                                                (Efield
                                                  (Evar _in2 (Tstruct _ZSTD_inBuffer_s noattr))
                                                  _size tulong)
                                                (Etempvar _t'47 tulong)))
                                            (Sassign
                                              (Efield
                                                (Evar _in (Tstruct _ZSTD_inBuffer_s noattr))
                                                _size tulong)
                                              (Etempvar _t'47 tulong)))
                                          (Ssequence
                                            (Ssequence
                                              (Ssequence
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _t'68
                                                      (Efield
                                                        (Evar _out (Tstruct _ZSTD_outBuffer_s noattr))
                                                        _pos tulong))
                                                    (Scall (Some _t'48)
                                                      (Evar _upto (Tfunction
                                                                    (tulong ::
                                                                    nil)
                                                                    tulong
                                                                    cc_default))
                                                      ((Ebinop Osub
                                                         (Etempvar _cap tulong)
                                                         (Etempvar _t'68 tulong)
                                                         tulong) :: nil)))
                                                  (Ssequence
                                                    (Sset _t'67
                                                      (Efield
                                                        (Evar _out (Tstruct _ZSTD_outBuffer_s noattr))
                                                        _pos tulong))
                                                    (Sset _t'49
                                                      (Ecast
                                                        (Ebinop Oadd
                                                          (Etempvar _t'67 tulong)
                                                          (Etempvar _t'48 tulong)
                                                          tulong) tulong))))
                                                (Sassign
                                                  (Efield
                                                    (Evar _out2 (Tstruct _ZSTD_outBuffer_s noattr))
                                                    _size tulong)
                                                  (Etempvar _t'49 tulong)))
                                              (Sassign
                                                (Efield
                                                  (Evar _out (Tstruct _ZSTD_outBuffer_s noattr))
                                                  _size tulong)
                                                (Etempvar _t'49 tulong)))
                                            (Ssequence
                                              (Ssequence
                                                (Scall (Some _t'50)
                                                  (Evar _ZSTD_decompressStream 
                                                  (Tfunction
                                                    ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
                                                     (tptr (Tstruct _ZSTD_outBuffer_s noattr)) ::
                                                     (tptr (Tstruct _ZSTD_inBuffer_s noattr)) ::
                                                     nil) tulong cc_default))
                                                  ((Etempvar _used (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
                                                   (Eaddrof
                                                     (Evar _out (Tstruct _ZSTD_outBuffer_s noattr))
                                                     (tptr (Tstruct _ZSTD_outBuffer_s noattr))) ::
                                                   (Eaddrof
                                                     (Evar _in (Tstruct _ZSTD_inBuffer_s noattr))
                                                     (tptr (Tstruct _ZSTD_inBuffer_s noattr))) ::
                                                   nil))
                                                (Sset _result
                                                  (Etempvar _t'50 tulong)))
                                              (Ssequence
                                                (Ssequence
                                                  (Scall (Some _t'51)
                                                    (Evar _ZSTD_decompressStream 
                                                    (Tfunction
                                                      ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
                                                       (tptr (Tstruct _ZSTD_outBuffer_s noattr)) ::
                                                       (tptr (Tstruct _ZSTD_inBuffer_s noattr)) ::
                                                       nil) tulong
                                                      cc_default))
                                                    ((Etempvar _fresh (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
                                                     (Eaddrof
                                                       (Evar _out2 (Tstruct _ZSTD_outBuffer_s noattr))
                                                       (tptr (Tstruct _ZSTD_outBuffer_s noattr))) ::
                                                     (Eaddrof
                                                       (Evar _in2 (Tstruct _ZSTD_inBuffer_s noattr))
                                                       (tptr (Tstruct _ZSTD_inBuffer_s noattr))) ::
                                                     nil))
                                                  (Sset _expected
                                                    (Etempvar _t'51 tulong)))
                                                (Ssequence
                                                  (Ssequence
                                                    (Ssequence
                                                      (Scall (Some _t'52)
                                                        (Evar _out_of_memory 
                                                        (Tfunction
                                                          (tulong :: nil)
                                                          tint cc_default))
                                                        ((Etempvar _result tulong) ::
                                                         nil))
                                                      (Sifthenelse (Etempvar _t'52 tint)
                                                        (Sset _t'53
                                                          (Econst_int (Int.repr 1) tint))
                                                        (Ssequence
                                                          (Scall (Some _t'54)
                                                            (Evar _out_of_memory 
                                                            (Tfunction
                                                              (tulong :: nil)
                                                              tint
                                                              cc_default))
                                                            ((Etempvar _expected tulong) ::
                                                             nil))
                                                          (Sset _t'53
                                                            (Ecast
                                                              (Etempvar _t'54 tint)
                                                              tbool)))))
                                                    (Sifthenelse (Etempvar _t'53 tint)
                                                      (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                                                      Sskip))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Scall (Some _t'55)
                                                        (Evar _ZSTD_isError 
                                                        (Tfunction
                                                          (tulong :: nil)
                                                          tuint cc_default))
                                                        ((Etempvar _result tulong) ::
                                                         nil))
                                                      (Sifthenelse (Etempvar _t'55 tuint)
                                                        (Ssequence
                                                          (Scall (Some _t'57)
                                                            (Evar _ZSTD_isError 
                                                            (Tfunction
                                                              (tulong :: nil)
                                                              tuint
                                                              cc_default))
                                                            ((Etempvar _expected tulong) ::
                                                             nil))
                                                          (Sset _t'56
                                                            (Ecast
                                                              (Etempvar _t'57 tuint)
                                                              tuint)))
                                                        (Ssequence
                                                          (Ssequence
                                                            (Sifthenelse 
                                                              (Ebinop Oeq
                                                                (Etempvar _result tulong)
                                                                (Etempvar _expected tulong)
                                                                tint)
                                                              (Ssequence
                                                                (Sset _t'65
                                                                  (Efield
                                                                    (Evar _in (Tstruct _ZSTD_inBuffer_s noattr))
                                                                    _pos
                                                                    tulong))
                                                                (Ssequence
                                                                  (Sset _t'66
                                                                    (Efield
                                                                    (Evar _in2 (Tstruct _ZSTD_inBuffer_s noattr))
                                                                    _pos
                                                                    tulong))
                                                                  (Sset _t'58
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'65 tulong)
                                                                    (Etempvar _t'66 tulong)
                                                                    tint)
                                                                    tbool))))
                                                              (Sset _t'58
                                                                (Econst_int (Int.repr 0) tint)))
                                                            (Sifthenelse (Etempvar _t'58 tint)
                                                              (Ssequence
                                                                (Sset _t'63
                                                                  (Efield
                                                                    (Evar _out (Tstruct _ZSTD_outBuffer_s noattr))
                                                                    _pos
                                                                    tulong))
                                                                (Ssequence
                                                                  (Sset _t'64
                                                                    (Efield
                                                                    (Evar _out2 (Tstruct _ZSTD_outBuffer_s noattr))
                                                                    _pos
                                                                    tulong))
                                                                  (Sset _t'59
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'63 tulong)
                                                                    (Etempvar _t'64 tulong)
                                                                    tint)
                                                                    tbool))))
                                                              (Sset _t'59
                                                                (Econst_int (Int.repr 0) tint))))
                                                          (Sifthenelse (Etempvar _t'59 tint)
                                                            (Ssequence
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Sset _t'62
                                                                    (Efield
                                                                    (Evar _out (Tstruct _ZSTD_outBuffer_s noattr))
                                                                    _pos
                                                                    tulong))
                                                                  (Scall (Some _t'61)
                                                                    (Evar _bytes_eq 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Etempvar _dst (tptr tuchar)) ::
                                                                    (Etempvar _other (tptr tuchar)) ::
                                                                    (Etempvar _t'62 tulong) ::
                                                                    nil)))
                                                                (Sset _t'60
                                                                  (Ecast
                                                                    (Etempvar _t'61 tint)
                                                                    tbool)))
                                                              (Sset _t'56
                                                                (Ecast
                                                                  (Etempvar _t'60 tint)
                                                                  tuint)))
                                                            (Sset _t'56
                                                              (Ecast
                                                                (Econst_int (Int.repr 0) tint)
                                                                tuint))))))
                                                    (Scall None
                                                      (Evar _gp_assert 
                                                      (Tfunction
                                                        (tint :: nil) tvoid
                                                        cc_default))
                                                      ((Etempvar _t'56 tuint) ::
                                                       nil))))))))
                                        (Ssequence
                                          (Ssequence
                                            (Scall (Some _t'43)
                                              (Evar _ZSTD_isError (Tfunction
                                                                    (tulong ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                              ((Etempvar _result tulong) ::
                                               nil))
                                            (Sifthenelse (Eunop Onotbool
                                                           (Etempvar _t'43 tuint)
                                                           tint)
                                              (Ssequence
                                                (Scall (Some _t'45)
                                                  (Evar _nondet_u8 (Tfunction
                                                                    nil
                                                                    tuchar
                                                                    cc_default))
                                                  nil)
                                                (Sset _t'44
                                                  (Ecast
                                                    (Ebinop One
                                                      (Etempvar _t'45 tuchar)
                                                      (Econst_int (Int.repr 0) tint)
                                                      tint) tbool)))
                                              (Sset _t'44
                                                (Econst_int (Int.repr 0) tint))))
                                          (Sifthenelse (Etempvar _t'44 tint)
                                            Sskip
                                            Sbreak)))
                                      (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))))))))))))))
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
 (_nondet_u8,
   Gfun(External (EF_external "nondet_u8"
                   (mksignature nil AST.Xint8unsigned cc_default)) nil tuchar
     cc_default)) ::
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
 (_ZSTD_isError,
   Gfun(External (EF_external "ZSTD_isError"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tuint cc_default)) ::
 (_ZSTD_getErrorCode,
   Gfun(External (EF_external "ZSTD_getErrorCode"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (_ZSTD_createDCtx,
   Gfun(External (EF_external "ZSTD_createDCtx"
                   (mksignature nil AST.Xptr cc_default)) nil
     (tptr (Tstruct _ZSTD_DCtx_s noattr)) cc_default)) ::
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
 (_ZSTD_DCtx_loadDictionary,
   Gfun(External (EF_external "ZSTD_DCtx_loadDictionary"
                   (mksignature (AST.Xptr :: AST.Xptr :: AST.Xlong :: nil)
                     AST.Xlong cc_default))
     ((tptr (Tstruct _ZSTD_DCtx_s noattr)) :: (tptr tvoid) :: tulong :: nil)
     tulong cc_default)) :: (_upto, Gfun(Internal f_upto)) ::
 (_any_bytes, Gfun(Internal f_any_bytes)) ::
 (_bytes_eq, Gfun(Internal f_bytes_eq)) ::
 (_out_of_memory, Gfun(Internal f_out_of_memory)) ::
 (_main, Gfun(Internal f_main)) :: nil).

Definition public_idents : list ident :=
(_main :: _ZSTD_DCtx_loadDictionary :: _ZSTD_decompressStream ::
 _ZSTD_DCtx_reset :: _ZSTD_DCtx_setParameter :: _ZSTD_decompressDCtx ::
 _ZSTD_createDCtx :: _ZSTD_getErrorCode :: _ZSTD_isError :: _gp_assert ::
 _nondet_bytes :: _nondet_size :: _nondet_u32 :: _nondet_u8 ::
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


