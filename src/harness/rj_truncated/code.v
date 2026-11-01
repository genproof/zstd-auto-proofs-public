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
  Definition source_file := "harness/rj_truncated.c".
  Definition normalized := true.
End Info.

Definition _ZSTD_DCtx_s : ident := $"ZSTD_DCtx_s".
Definition _ZSTD_XXH64 : ident := $"ZSTD_XXH64".
Definition _ZSTD_createDStream : ident := $"ZSTD_createDStream".
Definition _ZSTD_decompress : ident := $"ZSTD_decompress".
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
Definition _any_bytes : ident := $"any_bytes".
Definition _at : ident := $"at".
Definition _base : ident := $"base".
Definition _bytes : ident := $"bytes".
Definition _cap : ident := $"cap".
Definition _completed : ident := $"completed".
Definition _copy : ident := $"copy".
Definition _copy_of : ident := $"copy_of".
Definition _cut : ident := $"cut".
Definition _data : ident := $"data".
Definition _dict_id : ident := $"dict_id".
Definition _did_flag : ident := $"did_flag".
Definition _did_size : ident := $"did_size".
Definition _done : ident := $"done".
Definition _dst : ident := $"dst".
Definition _f : ident := $"f".
Definition _fcs : ident := $"fcs".
Definition _fcs_flag : ident := $"fcs_flag".
Definition _fcs_size : ident := $"fcs_size".
Definition _frame : ident := $"frame".
Definition _gp_assert : ident := $"gp_assert".
Definition _gp_assume : ident := $"gp_assume".
Definition _i : ident := $"i".
Definition _in : ident := $"in".
Definition _last : ident := $"last".
Definition _left : ident := $"left".
Definition _len : ident := $"len".
Definition _main : ident := $"main".
Definition _max : ident := $"max".
Definition _max_block : ident := $"max_block".
Definition _max_window : ident := $"max_window".
Definition _most : ident := $"most".
Definition _n : ident := $"n".
Definition _new_frame : ident := $"new_frame".
Definition _nondet_bytes : ident := $"nondet_bytes".
Definition _nondet_size : ident := $"nondet_size".
Definition _nondet_u8 : ident := $"nondet_u8".
Definition _out : ident := $"out".
Definition _out_of_memory : ident := $"out_of_memory".
Definition _p : ident := $"p".
Definition _part : ident := $"part".
Definition _pos : ident := $"pos".
Definition _put_le : ident := $"put_le".
Definition _quickproof_free : ident := $"quickproof_free".
Definition _quickproof_malloc : ident := $"quickproof_malloc".
Definition _read : ident := $"read".
Definition _result : ident := $"result".
Definition _rle : ident := $"rle".
Definition _single : ident := $"single".
Definition _size : ident := $"size".
Definition _source : ident := $"source".
Definition _src : ident := $"src".
Definition _stream_all : ident := $"stream_all".
Definition _upto : ident := $"upto".
Definition _value : ident := $"value".
Definition _wd : ident := $"wd".
Definition _window : ident := $"window".
Definition _written : ident := $"written".
Definition _wrote : ident := $"wrote".
Definition _zds : ident := $"zds".
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

Definition f_copy_of := {|
  fn_return := (tptr tuchar);
  fn_callconv := cc_default;
  fn_params := ((_source, (tptr tuchar)) :: (_n, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_copy, (tptr tuchar)) :: (_i, tulong) :: (_t'2, tint) ::
               (_t'1, (tptr tvoid)) :: (_t'3, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _quickproof_malloc (Tfunction (tulong :: nil) (tptr tvoid)
                                 cc_default)) ((Etempvar _n tulong) :: nil))
    (Sset _copy (Etempvar _t'1 (tptr tvoid))))
  (Ssequence
    (Ssequence
      (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
      (Sloop
        (Ssequence
          (Ssequence
            (Sifthenelse (Ebinop One (Etempvar _copy (tptr tuchar))
                           (Ecast (Econst_int (Int.repr 0) tint)
                             (tptr tvoid)) tint)
              (Sset _t'2
                (Ecast
                  (Ebinop Olt (Etempvar _i tulong) (Etempvar _n tulong) tint)
                  tbool))
              (Sset _t'2 (Econst_int (Int.repr 0) tint)))
            (Sifthenelse (Etempvar _t'2 tint) Sskip Sbreak))
          (Ssequence
            (Sset _t'3
              (Ederef
                (Ebinop Oadd (Etempvar _source (tptr tuchar))
                  (Etempvar _i tulong) (tptr tuchar)) tuchar))
            (Sassign
              (Ederef
                (Ebinop Oadd (Etempvar _copy (tptr tuchar))
                  (Etempvar _i tulong) (tptr tuchar)) tuchar)
              (Etempvar _t'3 tuchar))))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tulong) (Econst_int (Int.repr 1) tint)
            tulong))))
    (Sreturn (Some (Etempvar _copy (tptr tuchar))))))
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

Definition f_put_le := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr tuchar)) :: (_value, tulong) :: (_size, tulong) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_i, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
  (Sloop
    (Ssequence
      (Sifthenelse (Ebinop Olt (Etempvar _i tulong) (Etempvar _size tulong)
                     tint)
        Sskip
        Sbreak)
      (Sassign
        (Ederef
          (Ebinop Oadd (Etempvar _p (tptr tuchar)) (Etempvar _i tulong)
            (tptr tuchar)) tuchar)
        (Ecast
          (Ebinop Oshr (Etempvar _value tulong)
            (Ebinop Omul (Econst_int (Int.repr 8) tint) (Etempvar _i tulong)
              tulong) tulong) tuchar)))
    (Sset _i
      (Ebinop Oadd (Etempvar _i tulong) (Econst_int (Int.repr 1) tint)
        tulong))))
|}.

Definition f_new_frame := {|
  fn_return := (tptr tuchar);
  fn_callconv := cc_default;
  fn_params := ((_data, (tptr tuchar)) :: (_n, tulong) :: (_fcs, tulong) ::
                (_max_window, tulong) :: (_dict_id, tuint) ::
                (_len, (tptr tulong)) :: nil);
  fn_vars := nil;
  fn_temps := ((_f, (tptr tuchar)) :: (_fcs_flag, tuint) ::
               (_did_flag, tuint) :: (_single, tuint) ::
               (_fcs_size, tuint) :: (_did_size, tuint) :: (_wd, tuchar) ::
               (_base, tulong) :: (_window, tulong) :: (_at, tulong) ::
               (_done, tulong) :: (_max_block, tulong) :: (_last, tint) ::
               (_left, tulong) :: (_most, tulong) :: (_size, tulong) ::
               (_rle, tuint) :: (_i, tulong) :: (_frame, (tptr tuchar)) ::
               (_t'35, (tptr tuchar)) :: (_t'34, tulong) ::
               (_t'33, tuchar) :: (_t'32, tint) :: (_t'31, tulong) ::
               (_t'30, tulong) :: (_t'29, tuchar) :: (_t'28, tint) ::
               (_t'27, tint) :: (_t'26, tuchar) :: (_t'25, tulong) ::
               (_t'24, tulong) :: (_t'23, tulong) :: (_t'22, tulong) ::
               (_t'21, tulong) :: (_t'20, tulong) :: (_t'19, tint) ::
               (_t'18, tuchar) :: (_t'17, tulong) :: (_t'16, tuchar) ::
               (_t'15, tuint) :: (_t'14, tuint) :: (_t'13, tint) ::
               (_t'12, tint) :: (_t'11, tint) :: (_t'10, tint) ::
               (_t'9, tint) :: (_t'8, tint) :: (_t'7, tint) ::
               (_t'6, tint) :: (_t'5, tuchar) :: (_t'4, tuchar) ::
               (_t'3, tuchar) :: (_t'2, (tptr tvoid)) ::
               (_t'1, (tptr tvoid)) :: (_t'39, tuchar) :: (_t'38, tuchar) ::
               (_t'37, tuchar) :: (_t'36, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sifthenelse (Ebinop Ole (Etempvar _n tulong)
                   (Ebinop Odiv
                     (Ebinop Osub
                       (Econst_long (Int64.repr 9223372036854775807) tlong)
                       (Econst_int (Int.repr 26) tint) tlong)
                     (Econst_int (Int.repr 4) tint) tlong) tint)
      (Ssequence
        (Scall (Some _t'2)
          (Evar _quickproof_malloc (Tfunction (tulong :: nil) (tptr tvoid)
                                     cc_default))
          ((Ebinop Oadd (Econst_int (Int.repr 26) tint)
             (Ebinop Omul (Econst_int (Int.repr 4) tint) (Etempvar _n tulong)
               tulong) tulong) :: nil))
        (Sset _t'1 (Ecast (Etempvar _t'2 (tptr tvoid)) (tptr tvoid))))
      (Sset _t'1
        (Ecast (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
          (tptr tvoid))))
    (Sset _f (Etempvar _t'1 (tptr tvoid))))
  (Ssequence
    (Ssequence
      (Scall (Some _t'3) (Evar _nondet_u8 (Tfunction nil tuchar cc_default))
        nil)
      (Sset _fcs_flag
        (Ebinop Oand (Etempvar _t'3 tuchar) (Econst_int (Int.repr 3) tint)
          tint)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'4)
          (Evar _nondet_u8 (Tfunction nil tuchar cc_default)) nil)
        (Sset _did_flag
          (Ebinop Oand (Etempvar _t'4 tuchar) (Econst_int (Int.repr 3) tint)
            tint)))
      (Ssequence
        (Ssequence
          (Ssequence
            (Scall (Some _t'5)
              (Evar _nondet_u8 (Tfunction nil tuchar cc_default)) nil)
            (Sifthenelse (Ebinop Oand (Etempvar _t'5 tuchar)
                           (Econst_int (Int.repr 1) tint) tint)
              (Sset _t'6
                (Ecast
                  (Ebinop Ole (Etempvar _fcs tulong)
                    (Etempvar _max_window tulong) tint) tbool))
              (Sset _t'6 (Econst_int (Int.repr 0) tint))))
          (Sset _single (Etempvar _t'6 tint)))
        (Ssequence
          (Ssequence
            (Ssequence
              (Ssequence
                (Ssequence
                  (Sifthenelse (Ebinop Oeq (Etempvar _fcs_flag tuint)
                                 (Econst_int (Int.repr 0) tint) tint)
                    (Sset _t'7 (Ecast (Etempvar _single tuint) tbool))
                    (Sset _t'7 (Econst_int (Int.repr 0) tint)))
                  (Sifthenelse (Etempvar _t'7 tint)
                    (Sset _t'8
                      (Ecast
                        (Ebinop Ogt (Etempvar _fcs tulong)
                          (Econst_int (Int.repr 255) tint) tint) tbool))
                    (Sset _t'8 (Econst_int (Int.repr 0) tint))))
                (Sifthenelse (Etempvar _t'8 tint)
                  (Sset _t'9 (Econst_int (Int.repr 1) tint))
                  (Sifthenelse (Ebinop Oeq (Etempvar _fcs_flag tuint)
                                 (Econst_int (Int.repr 1) tint) tint)
                    (Sifthenelse (Ebinop Olt (Etempvar _fcs tulong)
                                   (Econst_int (Int.repr 256) tint) tint)
                      (Ssequence
                        (Sset _t'9
                          (Ecast (Econst_int (Int.repr 1) tint) tbool))
                        (Sset _t'9 (Ecast (Etempvar _t'9 tint) tbool)))
                      (Ssequence
                        (Ssequence
                          (Sset _t'9
                            (Ecast
                              (Ebinop Ogt (Etempvar _fcs tulong)
                                (Econst_int (Int.repr 65791) tint) tint)
                              tbool))
                          (Sset _t'9 (Ecast (Etempvar _t'9 tint) tbool)))
                        (Sset _t'9 (Ecast (Etempvar _t'9 tint) tbool))))
                    (Sset _t'9 (Ecast (Econst_int (Int.repr 0) tint) tbool)))))
              (Sifthenelse (Etempvar _t'9 tint)
                (Sset _t'10 (Econst_int (Int.repr 1) tint))
                (Sifthenelse (Ebinop Oeq (Etempvar _fcs_flag tuint)
                               (Econst_int (Int.repr 2) tint) tint)
                  (Ssequence
                    (Sset _t'10
                      (Ecast
                        (Ebinop Ogt (Etempvar _fcs tulong)
                          (Econst_int (Int.repr (-1)) tuint) tint) tbool))
                    (Sset _t'10 (Ecast (Etempvar _t'10 tint) tbool)))
                  (Sset _t'10 (Ecast (Econst_int (Int.repr 0) tint) tbool)))))
            (Sifthenelse (Etempvar _t'10 tint)
              (Sset _fcs_flag (Econst_int (Int.repr 3) tint))
              Sskip))
          (Ssequence
            (Ssequence
              (Ssequence
                (Ssequence
                  (Sifthenelse (Ebinop Oeq (Etempvar _did_flag tuint)
                                 (Econst_int (Int.repr 0) tint) tint)
                    (Sset _t'11
                      (Ecast
                        (Ebinop One (Etempvar _dict_id tuint)
                          (Econst_int (Int.repr 0) tint) tint) tbool))
                    (Sset _t'11 (Econst_int (Int.repr 0) tint)))
                  (Sifthenelse (Etempvar _t'11 tint)
                    (Sset _t'12 (Econst_int (Int.repr 1) tint))
                    (Sifthenelse (Ebinop Oeq (Etempvar _did_flag tuint)
                                   (Econst_int (Int.repr 1) tint) tint)
                      (Ssequence
                        (Sset _t'12
                          (Ecast
                            (Ebinop Ogt (Etempvar _dict_id tuint)
                              (Econst_int (Int.repr 255) tint) tint) tbool))
                        (Sset _t'12 (Ecast (Etempvar _t'12 tint) tbool)))
                      (Sset _t'12
                        (Ecast (Econst_int (Int.repr 0) tint) tbool)))))
                (Sifthenelse (Etempvar _t'12 tint)
                  (Sset _t'13 (Econst_int (Int.repr 1) tint))
                  (Sifthenelse (Ebinop Oeq (Etempvar _did_flag tuint)
                                 (Econst_int (Int.repr 2) tint) tint)
                    (Ssequence
                      (Sset _t'13
                        (Ecast
                          (Ebinop Ogt (Etempvar _dict_id tuint)
                            (Econst_int (Int.repr 65535) tint) tint) tbool))
                      (Sset _t'13 (Ecast (Etempvar _t'13 tint) tbool)))
                    (Sset _t'13 (Ecast (Econst_int (Int.repr 0) tint) tbool)))))
              (Sifthenelse (Etempvar _t'13 tint)
                (Sset _did_flag (Econst_int (Int.repr 3) tint))
                Sskip))
            (Ssequence
              (Ssequence
                (Sifthenelse (Ebinop Oeq (Etempvar _fcs_flag tuint)
                               (Econst_int (Int.repr 0) tint) tint)
                  (Sset _t'14 (Ecast (Etempvar _single tuint) tuint))
                  (Sset _t'14
                    (Ecast
                      (Ebinop Oshl (Econst_int (Int.repr 2) tuint)
                        (Ebinop Osub (Etempvar _fcs_flag tuint)
                          (Econst_int (Int.repr 1) tint) tuint) tuint) tuint)))
                (Sset _fcs_size (Etempvar _t'14 tuint)))
              (Ssequence
                (Ssequence
                  (Sifthenelse (Ebinop Oeq (Etempvar _did_flag tuint)
                                 (Econst_int (Int.repr 3) tint) tint)
                    (Sset _t'15 (Ecast (Econst_int (Int.repr 4) tint) tuint))
                    (Sset _t'15 (Ecast (Etempvar _did_flag tuint) tuint)))
                  (Sset _did_size (Etempvar _t'15 tuint)))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'16)
                      (Evar _nondet_u8 (Tfunction nil tuchar cc_default))
                      nil)
                    (Sset _wd (Ecast (Etempvar _t'16 tuchar) tuchar)))
                  (Ssequence
                    (Sset _base
                      (Ebinop Oshl
                        (Ecast (Econst_int (Int.repr 1) tint) tulong)
                        (Ebinop Oadd (Econst_int (Int.repr 10) tint)
                          (Ebinop Oshr (Etempvar _wd tuchar)
                            (Econst_int (Int.repr 3) tint) tint) tint)
                        tulong))
                    (Ssequence
                      (Ssequence
                        (Sifthenelse (Etempvar _single tuint)
                          (Sset _t'17 (Ecast (Etempvar _fcs tulong) tulong))
                          (Sset _t'17
                            (Ecast
                              (Ebinop Oadd (Etempvar _base tulong)
                                (Ebinop Omul
                                  (Ebinop Odiv (Etempvar _base tulong)
                                    (Econst_int (Int.repr 8) tint) tulong)
                                  (Ebinop Oand (Etempvar _wd tuchar)
                                    (Econst_int (Int.repr 7) tint) tint)
                                  tulong) tulong) tulong)))
                        (Sset _window (Etempvar _t'17 tulong)))
                      (Ssequence
                        (Scall None
                          (Evar _gp_assume (Tfunction (tint :: nil) tvoid
                                             cc_default))
                          ((Ebinop Ole (Etempvar _window tulong)
                             (Etempvar _max_window tulong) tint) :: nil))
                        (Ssequence
                          (Sifthenelse (Ebinop Oeq
                                         (Etempvar _f (tptr tuchar))
                                         (Ecast
                                           (Econst_int (Int.repr 0) tint)
                                           (tptr tvoid)) tint)
                            (Sreturn (Some (Ecast
                                             (Econst_int (Int.repr 0) tint)
                                             (tptr tvoid))))
                            Sskip)
                          (Ssequence
                            (Scall None
                              (Evar _put_le (Tfunction
                                              ((tptr tuchar) :: tulong ::
                                               tulong :: nil) tvoid
                                              cc_default))
                              ((Etempvar _f (tptr tuchar)) ::
                               (Econst_int (Int.repr (-47205080)) tuint) ::
                               (Econst_int (Int.repr 4) tint) :: nil))
                            (Ssequence
                              (Ssequence
                                (Scall (Some _t'18)
                                  (Evar _nondet_u8 (Tfunction nil tuchar
                                                     cc_default)) nil)
                                (Sassign
                                  (Ederef
                                    (Ebinop Oadd (Etempvar _f (tptr tuchar))
                                      (Econst_int (Int.repr 4) tint)
                                      (tptr tuchar)) tuchar)
                                  (Ecast
                                    (Ebinop Oor
                                      (Ebinop Oor
                                        (Ebinop Oor
                                          (Ebinop Oshl
                                            (Etempvar _fcs_flag tuint)
                                            (Econst_int (Int.repr 6) tint)
                                            tuint)
                                          (Ebinop Oshl
                                            (Etempvar _single tuint)
                                            (Econst_int (Int.repr 5) tint)
                                            tuint) tuint)
                                        (Ebinop Oand (Etempvar _t'18 tuchar)
                                          (Econst_int (Int.repr 20) tint)
                                          tint) tuint)
                                      (Etempvar _did_flag tuint) tuint)
                                    tuchar)))
                              (Ssequence
                                (Sassign
                                  (Ederef
                                    (Ebinop Oadd (Etempvar _f (tptr tuchar))
                                      (Econst_int (Int.repr 5) tint)
                                      (tptr tuchar)) tuchar)
                                  (Etempvar _wd tuchar))
                                (Ssequence
                                  (Ssequence
                                    (Sifthenelse (Etempvar _single tuint)
                                      (Sset _t'19
                                        (Ecast (Econst_int (Int.repr 5) tint)
                                          tint))
                                      (Sset _t'19
                                        (Ecast (Econst_int (Int.repr 6) tint)
                                          tint)))
                                    (Sset _at
                                      (Ecast (Etempvar _t'19 tint) tulong)))
                                  (Ssequence
                                    (Sset _done
                                      (Ecast (Econst_int (Int.repr 0) tint)
                                        tulong))
                                    (Ssequence
                                      (Ssequence
                                        (Sifthenelse (Ebinop Olt
                                                       (Etempvar _window tulong)
                                                       (Econst_int (Int.repr 131072) tint)
                                                       tint)
                                          (Sset _t'20
                                            (Ecast
                                              (Ecast
                                                (Etempvar _window tulong)
                                                tulong) tulong))
                                          (Sset _t'20
                                            (Ecast
                                              (Econst_int (Int.repr 131072) tint)
                                              tulong)))
                                        (Sset _max_block
                                          (Etempvar _t'20 tulong)))
                                      (Ssequence
                                        (Scall None
                                          (Evar _put_le (Tfunction
                                                          ((tptr tuchar) ::
                                                           tulong ::
                                                           tulong :: nil)
                                                          tvoid cc_default))
                                          ((Ebinop Oadd
                                             (Etempvar _f (tptr tuchar))
                                             (Etempvar _at tulong)
                                             (tptr tuchar)) ::
                                           (Etempvar _dict_id tuint) ::
                                           (Etempvar _did_size tuint) :: nil))
                                        (Ssequence
                                          (Ssequence
                                            (Sifthenelse (Ebinop Oeq
                                                           (Etempvar _fcs_flag tuint)
                                                           (Econst_int (Int.repr 1) tint)
                                                           tint)
                                              (Sset _t'21
                                                (Ecast
                                                  (Ebinop Osub
                                                    (Etempvar _fcs tulong)
                                                    (Econst_int (Int.repr 256) tint)
                                                    tulong) tulong))
                                              (Sset _t'21
                                                (Ecast (Etempvar _fcs tulong)
                                                  tulong)))
                                            (Scall None
                                              (Evar _put_le (Tfunction
                                                              ((tptr tuchar) ::
                                                               tulong ::
                                                               tulong :: nil)
                                                              tvoid
                                                              cc_default))
                                              ((Ebinop Oadd
                                                 (Ebinop Oadd
                                                   (Etempvar _f (tptr tuchar))
                                                   (Etempvar _at tulong)
                                                   (tptr tuchar))
                                                 (Etempvar _did_size tuint)
                                                 (tptr tuchar)) ::
                                               (Etempvar _t'21 tulong) ::
                                               (Etempvar _fcs_size tuint) ::
                                               nil)))
                                          (Ssequence
                                            (Sset _at
                                              (Ebinop Oadd
                                                (Etempvar _at tulong)
                                                (Ebinop Oadd
                                                  (Etempvar _did_size tuint)
                                                  (Etempvar _fcs_size tuint)
                                                  tuint) tulong))
                                            (Ssequence
                                              (Ssequence
                                                (Sset _last
                                                  (Econst_int (Int.repr 0) tint))
                                                (Swhile
                                                  (Eunop Onotbool
                                                    (Etempvar _last tint)
                                                    tint)
                                                  (Ssequence
                                                    (Sset _left
                                                      (Ebinop Osub
                                                        (Etempvar _n tulong)
                                                        (Etempvar _done tulong)
                                                        tulong))
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sifthenelse 
                                                          (Ebinop Olt
                                                            (Etempvar _left tulong)
                                                            (Etempvar _max_block tulong)
                                                            tint)
                                                          (Sset _t'22
                                                            (Ecast
                                                              (Etempvar _left tulong)
                                                              tulong))
                                                          (Sset _t'22
                                                            (Ecast
                                                              (Etempvar _max_block tulong)
                                                              tulong)))
                                                        (Sset _most
                                                          (Etempvar _t'22 tulong)))
                                                      (Ssequence
                                                        (Ssequence
                                                          (Sifthenelse 
                                                            (Ebinop Oeq
                                                              (Etempvar _left tulong)
                                                              (Econst_int (Int.repr 0) tint)
                                                              tint)
                                                            (Sset _t'23
                                                              (Ecast
                                                                (Econst_int (Int.repr 0) tint)
                                                                tulong))
                                                            (Ssequence
                                                              (Ssequence
                                                                (Sifthenelse 
                                                                  (Ebinop Oeq
                                                                    (Etempvar _most tulong)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                  (Sset _t'24
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tulong))
                                                                  (Sset _t'24
                                                                    (Ecast
                                                                    (Ebinop Osub
                                                                    (Etempvar _most tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong)
                                                                    tulong)))
                                                                (Scall (Some _t'25)
                                                                  (Evar _upto 
                                                                  (Tfunction
                                                                    (tulong ::
                                                                    nil)
                                                                    tulong
                                                                    cc_default))
                                                                  ((Etempvar _t'24 tulong) ::
                                                                   nil)))
                                                              (Sset _t'23
                                                                (Ecast
                                                                  (Ebinop Oadd
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (Etempvar _t'25 tulong)
                                                                    tulong)
                                                                  tulong))))
                                                          (Sset _size
                                                            (Etempvar _t'23 tulong)))
                                                        (Ssequence
                                                          (Ssequence
                                                            (Ssequence
                                                              (Scall (Some _t'26)
                                                                (Evar _nondet_u8 
                                                                (Tfunction
                                                                  nil tuchar
                                                                  cc_default))
                                                                nil)
                                                              (Sifthenelse 
                                                                (Ebinop Oand
                                                                  (Etempvar _t'26 tuchar)
                                                                  (Econst_int (Int.repr 1) tint)
                                                                  tint)
                                                                (Sset _t'27
                                                                  (Ecast
                                                                    (Ebinop Ogt
                                                                    (Etempvar _max_block tulong)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    tbool))
                                                                (Sset _t'27
                                                                  (Econst_int (Int.repr 0) tint))))
                                                            (Sset _rle
                                                              (Etempvar _t'27 tint)))
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sifthenelse 
                                                                (Ebinop Oeq
                                                                  (Ebinop Oadd
                                                                    (Etempvar _done tulong)
                                                                    (Etempvar _size tulong)
                                                                    tulong)
                                                                  (Etempvar _n tulong)
                                                                  tint)
                                                                (Sifthenelse 
                                                                  (Ebinop Oeq
                                                                    (Etempvar _size tulong)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                  (Sset _t'28
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tbool))
                                                                  (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'29)
                                                                    (Evar _nondet_u8 
                                                                    (Tfunction
                                                                    nil
                                                                    tuchar
                                                                    cc_default))
                                                                    nil)
                                                                    (Sset _t'28
                                                                    (Ecast
                                                                    (Ebinop Oand
                                                                    (Etempvar _t'29 tuchar)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    tbool)))
                                                                    (Sset _t'28
                                                                    (Ecast
                                                                    (Etempvar _t'28 tint)
                                                                    tbool))))
                                                                (Sset _t'28
                                                                  (Econst_int (Int.repr 0) tint)))
                                                              (Sset _last
                                                                (Etempvar _t'28 tint)))
                                                            (Ssequence
                                                              (Scall None
                                                                (Evar _put_le 
                                                                (Tfunction
                                                                  ((tptr tuchar) ::
                                                                   tulong ::
                                                                   tulong ::
                                                                   nil) tvoid
                                                                  cc_default))
                                                                ((Ebinop Oadd
                                                                   (Etempvar _f (tptr tuchar))
                                                                   (Etempvar _at tulong)
                                                                   (tptr tuchar)) ::
                                                                 (Ebinop Oor
                                                                   (Ebinop Oor
                                                                    (Ecast
                                                                    (Etempvar _last tint)
                                                                    tulong)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _rle tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)
                                                                    tulong)
                                                                   (Ebinop Oshl
                                                                    (Etempvar _size tulong)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tulong)
                                                                   tulong) ::
                                                                 (Econst_int (Int.repr 3) tint) ::
                                                                 nil))
                                                              (Ssequence
                                                                (Sset _at
                                                                  (Ebinop Oadd
                                                                    (Etempvar _at tulong)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tulong))
                                                                (Ssequence
                                                                  (Ssequence
                                                                    (Sset _i
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tulong))
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _i tulong)
                                                                    (Etempvar _size tulong)
                                                                    tint)
                                                                    Sskip
                                                                    Sbreak)
                                                                    (Sifthenelse (Etempvar _rle tuint)
                                                                    (Ssequence
                                                                    (Sset _t'39
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _data (tptr tuchar))
                                                                    (Etempvar _done tulong)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _data (tptr tuchar))
                                                                    (Ebinop Oadd
                                                                    (Etempvar _done tulong)
                                                                    (Etempvar _i tulong)
                                                                    tulong)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Etempvar _t'39 tuchar)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'30
                                                                    (Etempvar _at tulong))
                                                                    (Sset _at
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'30 tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong)))
                                                                    (Ssequence
                                                                    (Sset _t'38
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _data (tptr tuchar))
                                                                    (Ebinop Oadd
                                                                    (Etempvar _done tulong)
                                                                    (Etempvar _i tulong)
                                                                    tulong)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _f (tptr tuchar))
                                                                    (Etempvar _t'30 tulong)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Etempvar _t'38 tuchar))))))
                                                                    (Sset _i
                                                                    (Ebinop Oadd
                                                                    (Etempvar _i tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong))))
                                                                  (Ssequence
                                                                    (Sifthenelse (Etempvar _rle tuint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'31
                                                                    (Etempvar _at tulong))
                                                                    (Sset _at
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'31 tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong)))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _size tulong)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'33)
                                                                    (Evar _nondet_u8 
                                                                    (Tfunction
                                                                    nil
                                                                    tuchar
                                                                    cc_default))
                                                                    nil)
                                                                    (Sset _t'32
                                                                    (Ecast
                                                                    (Etempvar _t'33 tuchar)
                                                                    tint)))
                                                                    (Ssequence
                                                                    (Sset _t'37
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _data (tptr tuchar))
                                                                    (Etempvar _done tulong)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Sset _t'32
                                                                    (Ecast
                                                                    (Etempvar _t'37 tuchar)
                                                                    tint)))))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _f (tptr tuchar))
                                                                    (Etempvar _t'31 tulong)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Etempvar _t'32 tint)))
                                                                    Sskip)
                                                                    (Sset _done
                                                                    (Ebinop Oadd
                                                                    (Etempvar _done tulong)
                                                                    (Etempvar _size tulong)
                                                                    tulong)))))))))))))
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'36
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Etempvar _f (tptr tuchar))
                                                        (Econst_int (Int.repr 4) tint)
                                                        (tptr tuchar))
                                                      tuchar))
                                                  (Sifthenelse (Ebinop Oand
                                                                 (Etempvar _t'36 tuchar)
                                                                 (Econst_int (Int.repr 4) tint)
                                                                 tint)
                                                    (Ssequence
                                                      (Ssequence
                                                        (Scall (Some _t'34)
                                                          (Evar _ZSTD_XXH64 
                                                          (Tfunction
                                                            ((tptr tvoid) ::
                                                             tulong ::
                                                             tulong :: nil)
                                                            tulong
                                                            cc_default))
                                                          ((Etempvar _data (tptr tuchar)) ::
                                                           (Etempvar _n tulong) ::
                                                           (Econst_int (Int.repr 0) tint) ::
                                                           nil))
                                                        (Scall None
                                                          (Evar _put_le 
                                                          (Tfunction
                                                            ((tptr tuchar) ::
                                                             tulong ::
                                                             tulong :: nil)
                                                            tvoid cc_default))
                                                          ((Ebinop Oadd
                                                             (Etempvar _f (tptr tuchar))
                                                             (Etempvar _at tulong)
                                                             (tptr tuchar)) ::
                                                           (Etempvar _t'34 tulong) ::
                                                           (Econst_int (Int.repr 4) tint) ::
                                                           nil)))
                                                      (Sset _at
                                                        (Ebinop Oadd
                                                          (Etempvar _at tulong)
                                                          (Econst_int (Int.repr 4) tint)
                                                          tulong)))
                                                    Sskip))
                                                (Ssequence
                                                  (Sassign
                                                    (Ederef
                                                      (Etempvar _len (tptr tulong))
                                                      tulong)
                                                    (Etempvar _at tulong))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Scall (Some _t'35)
                                                        (Evar _copy_of 
                                                        (Tfunction
                                                          ((tptr tuchar) ::
                                                           tulong :: nil)
                                                          (tptr tuchar)
                                                          cc_default))
                                                        ((Etempvar _f (tptr tuchar)) ::
                                                         (Etempvar _at tulong) ::
                                                         nil))
                                                      (Sset _frame
                                                        (Etempvar _t'35 (tptr tuchar))))
                                                    (Ssequence
                                                      (Scall None
                                                        (Evar _quickproof_free 
                                                        (Tfunction
                                                          ((tptr tvoid) ::
                                                           nil) tvoid
                                                          cc_default))
                                                        ((Etempvar _f (tptr tuchar)) ::
                                                         nil))
                                                      (Sreturn (Some (Etempvar _frame (tptr tuchar)))))))))))))))))))))))))))))))
|}.

Definition f_stream_all := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_zds, (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
                (_src, (tptr tuchar)) :: (_len, tulong) ::
                (_dst, (tptr tuchar)) :: (_cap, tulong) ::
                (_written, (tptr tulong)) :: (_completed, (tptr tulong)) ::
                nil);
  fn_vars := ((_in, (Tstruct _ZSTD_inBuffer_s noattr)) ::
              (_out, (Tstruct _ZSTD_outBuffer_s noattr)) :: nil);
  fn_temps := ((_result, tulong) :: (_read, tulong) :: (_wrote, tulong) ::
               (_t'7, tulong) :: (_t'6, tulong) :: (_t'5, tulong) ::
               (_t'4, tulong) :: (_t'3, tulong) :: (_t'2, tint) ::
               (_t'1, tuint) :: (_t'18, tulong) :: (_t'17, tulong) ::
               (_t'16, tulong) :: (_t'15, tulong) :: (_t'14, tulong) ::
               (_t'13, tulong) :: (_t'12, tulong) :: (_t'11, tulong) ::
               (_t'10, tulong) :: (_t'9, tulong) :: (_t'8, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sassign
    (Efield (Evar _in (Tstruct _ZSTD_inBuffer_s noattr)) _src (tptr tvoid))
    (Etempvar _src (tptr tuchar)))
  (Ssequence
    (Sassign
      (Efield (Evar _in (Tstruct _ZSTD_inBuffer_s noattr)) _pos tulong)
      (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Sassign
        (Efield (Evar _out (Tstruct _ZSTD_outBuffer_s noattr)) _dst
          (tptr tvoid)) (Etempvar _dst (tptr tuchar)))
      (Ssequence
        (Sassign
          (Efield (Evar _out (Tstruct _ZSTD_outBuffer_s noattr)) _pos tulong)
          (Econst_int (Int.repr 0) tint))
        (Ssequence
          (Sassign (Ederef (Etempvar _completed (tptr tulong)) tulong)
            (Econst_int (Int.repr 0) tint))
          (Ssequence
            (Sloop
              (Ssequence
                (Sset _read
                  (Efield (Evar _in (Tstruct _ZSTD_inBuffer_s noattr)) _pos
                    tulong))
                (Ssequence
                  (Sset _wrote
                    (Efield (Evar _out (Tstruct _ZSTD_outBuffer_s noattr))
                      _pos tulong))
                  (Ssequence
                    (Ssequence
                      (Ssequence
                        (Sset _t'16
                          (Efield
                            (Evar _in (Tstruct _ZSTD_inBuffer_s noattr)) _pos
                            tulong))
                        (Sifthenelse (Ebinop Oeq (Etempvar _t'16 tulong)
                                       (Etempvar _len tulong) tint)
                          (Sset _t'3 (Ecast (Etempvar _len tulong) tulong))
                          (Ssequence
                            (Ssequence
                              (Sset _t'18
                                (Efield
                                  (Evar _in (Tstruct _ZSTD_inBuffer_s noattr))
                                  _pos tulong))
                              (Scall (Some _t'4)
                                (Evar _upto (Tfunction (tulong :: nil) tulong
                                              cc_default))
                                ((Ebinop Osub
                                   (Ebinop Osub (Etempvar _len tulong)
                                     (Etempvar _t'18 tulong) tulong)
                                   (Econst_int (Int.repr 1) tint) tulong) ::
                                 nil)))
                            (Ssequence
                              (Sset _t'17
                                (Efield
                                  (Evar _in (Tstruct _ZSTD_inBuffer_s noattr))
                                  _pos tulong))
                              (Sset _t'3
                                (Ecast
                                  (Ebinop Oadd
                                    (Ebinop Oadd (Etempvar _t'17 tulong)
                                      (Econst_int (Int.repr 1) tint) tulong)
                                    (Etempvar _t'4 tulong) tulong) tulong))))))
                      (Sassign
                        (Efield (Evar _in (Tstruct _ZSTD_inBuffer_s noattr))
                          _size tulong) (Etempvar _t'3 tulong)))
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Sset _t'13
                            (Efield
                              (Evar _out (Tstruct _ZSTD_outBuffer_s noattr))
                              _pos tulong))
                          (Sifthenelse (Ebinop Oeq (Etempvar _t'13 tulong)
                                         (Etempvar _cap tulong) tint)
                            (Sset _t'5 (Ecast (Etempvar _cap tulong) tulong))
                            (Ssequence
                              (Ssequence
                                (Sset _t'15
                                  (Efield
                                    (Evar _out (Tstruct _ZSTD_outBuffer_s noattr))
                                    _pos tulong))
                                (Scall (Some _t'6)
                                  (Evar _upto (Tfunction (tulong :: nil)
                                                tulong cc_default))
                                  ((Ebinop Osub
                                     (Ebinop Osub (Etempvar _cap tulong)
                                       (Etempvar _t'15 tulong) tulong)
                                     (Econst_int (Int.repr 1) tint) tulong) ::
                                   nil)))
                              (Ssequence
                                (Sset _t'14
                                  (Efield
                                    (Evar _out (Tstruct _ZSTD_outBuffer_s noattr))
                                    _pos tulong))
                                (Sset _t'5
                                  (Ecast
                                    (Ebinop Oadd
                                      (Ebinop Oadd (Etempvar _t'14 tulong)
                                        (Econst_int (Int.repr 1) tint)
                                        tulong) (Etempvar _t'6 tulong)
                                      tulong) tulong))))))
                        (Sassign
                          (Efield
                            (Evar _out (Tstruct _ZSTD_outBuffer_s noattr))
                            _size tulong) (Etempvar _t'5 tulong)))
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'7)
                            (Evar _ZSTD_decompressStream (Tfunction
                                                           ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
                                                            (tptr (Tstruct _ZSTD_outBuffer_s noattr)) ::
                                                            (tptr (Tstruct _ZSTD_inBuffer_s noattr)) ::
                                                            nil) tulong
                                                           cc_default))
                            ((Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
                             (Eaddrof
                               (Evar _out (Tstruct _ZSTD_outBuffer_s noattr))
                               (tptr (Tstruct _ZSTD_outBuffer_s noattr))) ::
                             (Eaddrof
                               (Evar _in (Tstruct _ZSTD_inBuffer_s noattr))
                               (tptr (Tstruct _ZSTD_inBuffer_s noattr))) ::
                             nil))
                          (Sset _result (Etempvar _t'7 tulong)))
                        (Ssequence
                          (Sset _t'12
                            (Ederef (Etempvar _completed (tptr tulong))
                              tulong))
                          (Sassign
                            (Ederef (Etempvar _completed (tptr tulong))
                              tulong)
                            (Ebinop Oadd (Etempvar _t'12 tulong)
                              (Ebinop Oeq (Etempvar _result tulong)
                                (Econst_int (Int.repr 0) tint) tint) tulong))))))))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'1)
                    (Evar _ZSTD_isError (Tfunction (tulong :: nil) tuint
                                          cc_default))
                    ((Etempvar _result tulong) :: nil))
                  (Sifthenelse (Eunop Onotbool (Etempvar _t'1 tuint) tint)
                    (Sifthenelse (Ebinop Oeq (Etempvar _result tulong)
                                   (Econst_int (Int.repr 0) tint) tint)
                      (Ssequence
                        (Ssequence
                          (Sset _t'11
                            (Efield
                              (Evar _in (Tstruct _ZSTD_inBuffer_s noattr))
                              _pos tulong))
                          (Sset _t'2
                            (Ecast
                              (Ebinop Olt (Etempvar _t'11 tulong)
                                (Etempvar _len tulong) tint) tint)))
                        (Sset _t'2 (Ecast (Etempvar _t'2 tint) tbool)))
                      (Ssequence
                        (Sset _t'9
                          (Efield
                            (Evar _in (Tstruct _ZSTD_inBuffer_s noattr)) _pos
                            tulong))
                        (Sifthenelse (Ebinop One (Etempvar _t'9 tulong)
                                       (Etempvar _read tulong) tint)
                          (Ssequence
                            (Sset _t'2
                              (Ecast (Econst_int (Int.repr 1) tint) tint))
                            (Sset _t'2 (Ecast (Etempvar _t'2 tint) tbool)))
                          (Ssequence
                            (Ssequence
                              (Ssequence
                                (Sset _t'10
                                  (Efield
                                    (Evar _out (Tstruct _ZSTD_outBuffer_s noattr))
                                    _pos tulong))
                                (Sset _t'2
                                  (Ecast
                                    (Ebinop One (Etempvar _t'10 tulong)
                                      (Etempvar _wrote tulong) tint) tbool)))
                              (Sset _t'2 (Ecast (Etempvar _t'2 tint) tint)))
                            (Sset _t'2 (Ecast (Etempvar _t'2 tint) tbool))))))
                    (Sset _t'2 (Econst_int (Int.repr 0) tint))))
                (Sifthenelse (Etempvar _t'2 tint) Sskip Sbreak)))
            (Ssequence
              (Ssequence
                (Sset _t'8
                  (Efield (Evar _out (Tstruct _ZSTD_outBuffer_s noattr)) _pos
                    tulong))
                (Sassign (Ederef (Etempvar _written (tptr tulong)) tulong)
                  (Etempvar _t'8 tulong)))
              (Sreturn (Some (Etempvar _result tulong))))))))))
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := ((_len, tulong) :: (_written, tulong) :: (_completed, tulong) ::
              nil);
  fn_temps := ((_n, tulong) :: (_data, (tptr tuchar)) ::
               (_frame, (tptr tuchar)) :: (_cut, tulong) :: (_cap, tulong) ::
               (_part, (tptr tuchar)) :: (_dst, (tptr tuchar)) ::
               (_zds, (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
               (_result, tulong) :: (_last, tulong) :: (_t'18, tint) ::
               (_t'17, tuint) :: (_t'16, tint) :: (_t'15, tint) ::
               (_t'14, tint) :: (_t'13, tulong) :: (_t'12, tulong) ::
               (_t'11, tint) :: (_t'10, tint) ::
               (_t'9, (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
               (_t'8, (tptr tvoid)) :: (_t'7, (tptr tuchar)) ::
               (_t'6, tulong) :: (_t'5, tulong) :: (_t'4, (tptr tuchar)) ::
               (_t'3, (tptr tvoid)) :: (_t'2, (tptr tuchar)) ::
               (_t'1, tulong) :: (_t'20, tulong) :: (_t'19, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _upto (Tfunction (tulong :: nil) tulong cc_default))
        ((Econst_long (Int64.repr 9223372036854775807) tlong) :: nil))
      (Sset _n (Etempvar _t'1 tulong)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _any_bytes (Tfunction (tulong :: nil) (tptr tuchar)
                             cc_default)) ((Etempvar _n tulong) :: nil))
        (Sset _data (Etempvar _t'2 (tptr tuchar))))
      (Ssequence
        (Ssequence
          (Sifthenelse (Ebinop Oeq (Etempvar _data (tptr tuchar))
                         (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                         tint)
            (Sset _t'3
              (Ecast (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                (tptr tvoid)))
            (Ssequence
              (Scall (Some _t'4)
                (Evar _new_frame (Tfunction
                                   ((tptr tuchar) :: tulong :: tulong ::
                                    tulong :: tuint :: (tptr tulong) :: nil)
                                   (tptr tuchar) cc_default))
                ((Etempvar _data (tptr tuchar)) :: (Etempvar _n tulong) ::
                 (Etempvar _n tulong) ::
                 (Ebinop Oshl (Ecast (Econst_int (Int.repr 1) tint) tulong)
                   (Econst_int (Int.repr 27) tint) tulong) ::
                 (Econst_int (Int.repr 0) tint) ::
                 (Eaddrof (Evar _len tulong) (tptr tulong)) :: nil))
              (Sset _t'3 (Ecast (Etempvar _t'4 (tptr tuchar)) (tptr tvoid)))))
          (Sset _frame (Etempvar _t'3 (tptr tvoid))))
        (Ssequence
          (Sifthenelse (Ebinop Oeq (Etempvar _frame (tptr tuchar))
                         (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                         tint)
            (Sreturn (Some (Econst_int (Int.repr 0) tint)))
            Sskip)
          (Ssequence
            (Ssequence
              (Ssequence
                (Sset _t'20 (Evar _len tulong))
                (Scall (Some _t'5)
                  (Evar _upto (Tfunction (tulong :: nil) tulong cc_default))
                  ((Ebinop Osub (Etempvar _t'20 tulong)
                     (Econst_int (Int.repr 2) tint) tulong) :: nil)))
              (Sset _cut
                (Ebinop Oadd (Econst_int (Int.repr 1) tint)
                  (Etempvar _t'5 tulong) tulong)))
            (Ssequence
              (Ssequence
                (Scall (Some _t'6)
                  (Evar _upto (Tfunction (tulong :: nil) tulong cc_default))
                  ((Econst_long (Int64.repr 9223372036854775807) tlong) ::
                   nil))
                (Sset _cap (Etempvar _t'6 tulong)))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'7)
                    (Evar _copy_of (Tfunction
                                     ((tptr tuchar) :: tulong :: nil)
                                     (tptr tuchar) cc_default))
                    ((Etempvar _frame (tptr tuchar)) ::
                     (Etempvar _cut tulong) :: nil))
                  (Sset _part (Etempvar _t'7 (tptr tuchar))))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'8)
                      (Evar _quickproof_malloc (Tfunction (tulong :: nil)
                                                 (tptr tvoid) cc_default))
                      ((Etempvar _cap tulong) :: nil))
                    (Sset _dst (Etempvar _t'8 (tptr tvoid))))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'9)
                        (Evar _ZSTD_createDStream (Tfunction nil
                                                    (tptr (Tstruct _ZSTD_DCtx_s noattr))
                                                    cc_default)) nil)
                      (Sset _zds
                        (Etempvar _t'9 (tptr (Tstruct _ZSTD_DCtx_s noattr)))))
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Sifthenelse (Ebinop Oeq
                                         (Etempvar _part (tptr tuchar))
                                         (Ecast
                                           (Econst_int (Int.repr 0) tint)
                                           (tptr tvoid)) tint)
                            (Sset _t'10 (Econst_int (Int.repr 1) tint))
                            (Sset _t'10
                              (Ecast
                                (Ebinop Oeq (Etempvar _dst (tptr tuchar))
                                  (Ecast (Econst_int (Int.repr 0) tint)
                                    (tptr tvoid)) tint) tbool)))
                          (Sifthenelse (Etempvar _t'10 tint)
                            (Sset _t'11 (Econst_int (Int.repr 1) tint))
                            (Sset _t'11
                              (Ecast
                                (Ebinop Oeq
                                  (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                  (Ecast (Econst_int (Int.repr 0) tint)
                                    (tptr tvoid)) tint) tbool))))
                        (Sifthenelse (Etempvar _t'11 tint)
                          (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                          Sskip))
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'12)
                            (Evar _ZSTD_decompress (Tfunction
                                                     ((tptr tvoid) ::
                                                      tulong ::
                                                      (tptr tvoid) ::
                                                      tulong :: nil) tulong
                                                     cc_default))
                            ((Etempvar _dst (tptr tuchar)) ::
                             (Etempvar _cap tulong) ::
                             (Etempvar _part (tptr tuchar)) ::
                             (Etempvar _cut tulong) :: nil))
                          (Sset _result (Etempvar _t'12 tulong)))
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'13)
                              (Evar _stream_all (Tfunction
                                                  ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
                                                   (tptr tuchar) :: tulong ::
                                                   (tptr tuchar) :: tulong ::
                                                   (tptr tulong) ::
                                                   (tptr tulong) :: nil)
                                                  tulong cc_default))
                              ((Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
                               (Etempvar _part (tptr tuchar)) ::
                               (Etempvar _cut tulong) ::
                               (Etempvar _dst (tptr tuchar)) ::
                               (Etempvar _cap tulong) ::
                               (Eaddrof (Evar _written tulong) (tptr tulong)) ::
                               (Eaddrof (Evar _completed tulong)
                                 (tptr tulong)) :: nil))
                            (Sset _last (Etempvar _t'13 tulong)))
                          (Ssequence
                            (Ssequence
                              (Ssequence
                                (Scall (Some _t'14)
                                  (Evar _out_of_memory (Tfunction
                                                         (tulong :: nil) tint
                                                         cc_default))
                                  ((Etempvar _result tulong) :: nil))
                                (Sifthenelse (Etempvar _t'14 tint)
                                  (Sset _t'15 (Econst_int (Int.repr 1) tint))
                                  (Ssequence
                                    (Scall (Some _t'16)
                                      (Evar _out_of_memory (Tfunction
                                                             (tulong :: nil)
                                                             tint cc_default))
                                      ((Etempvar _last tulong) :: nil))
                                    (Sset _t'15
                                      (Ecast (Etempvar _t'16 tint) tbool)))))
                              (Sifthenelse (Etempvar _t'15 tint)
                                (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                                Sskip))
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Scall (Some _t'17)
                                    (Evar _ZSTD_isError (Tfunction
                                                          (tulong :: nil)
                                                          tuint cc_default))
                                    ((Etempvar _result tulong) :: nil))
                                  (Sifthenelse (Etempvar _t'17 tuint)
                                    (Ssequence
                                      (Sset _t'19 (Evar _completed tulong))
                                      (Sset _t'18
                                        (Ecast
                                          (Ebinop Oeq (Etempvar _t'19 tulong)
                                            (Econst_int (Int.repr 0) tint)
                                            tint) tbool)))
                                    (Sset _t'18
                                      (Econst_int (Int.repr 0) tint))))
                                (Scall None
                                  (Evar _gp_assert (Tfunction (tint :: nil)
                                                     tvoid cc_default))
                                  ((Etempvar _t'18 tint) :: nil)))
                              (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))))))))))
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
 (_ZSTD_decompress,
   Gfun(External (EF_external "ZSTD_decompress"
                   (mksignature
                     (AST.Xptr :: AST.Xlong :: AST.Xptr :: AST.Xlong :: nil)
                     AST.Xlong cc_default))
     ((tptr tvoid) :: tulong :: (tptr tvoid) :: tulong :: nil) tulong
     cc_default)) ::
 (_ZSTD_isError,
   Gfun(External (EF_external "ZSTD_isError"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tuint cc_default)) ::
 (_ZSTD_getErrorCode,
   Gfun(External (EF_external "ZSTD_getErrorCode"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (_ZSTD_createDStream,
   Gfun(External (EF_external "ZSTD_createDStream"
                   (mksignature nil AST.Xptr cc_default)) nil
     (tptr (Tstruct _ZSTD_DCtx_s noattr)) cc_default)) ::
 (_ZSTD_decompressStream,
   Gfun(External (EF_external "ZSTD_decompressStream"
                   (mksignature (AST.Xptr :: AST.Xptr :: AST.Xptr :: nil)
                     AST.Xlong cc_default))
     ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
      (tptr (Tstruct _ZSTD_outBuffer_s noattr)) ::
      (tptr (Tstruct _ZSTD_inBuffer_s noattr)) :: nil) tulong cc_default)) ::
 (_ZSTD_XXH64,
   Gfun(External (EF_external "ZSTD_XXH64"
                   (mksignature (AST.Xptr :: AST.Xlong :: AST.Xlong :: nil)
                     AST.Xlong cc_default))
     ((tptr tvoid) :: tulong :: tulong :: nil) tulong cc_default)) ::
 (_upto, Gfun(Internal f_upto)) ::
 (_any_bytes, Gfun(Internal f_any_bytes)) ::
 (_copy_of, Gfun(Internal f_copy_of)) ::
 (_out_of_memory, Gfun(Internal f_out_of_memory)) ::
 (_put_le, Gfun(Internal f_put_le)) ::
 (_new_frame, Gfun(Internal f_new_frame)) ::
 (_stream_all, Gfun(Internal f_stream_all)) ::
 (_main, Gfun(Internal f_main)) :: nil).

Definition public_idents : list ident :=
(_main :: _ZSTD_XXH64 :: _ZSTD_decompressStream :: _ZSTD_createDStream ::
 _ZSTD_getErrorCode :: _ZSTD_isError :: _ZSTD_decompress :: _gp_assume ::
 _gp_assert :: _nondet_bytes :: _nondet_size :: _nondet_u8 ::
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


