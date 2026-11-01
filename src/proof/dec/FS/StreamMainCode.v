(* GENERATED from src/zstd/code.v (f_ZSTD_decompressStream cut in pieces); regenerated on 2026-10-24 for F9;
   do not edit. *)
From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Require Import Zstd.zstd.code.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Definition ds_case_init : statement :=
(Ssequence
                                        (Sloop Sskip Sbreak)
                                        (Ssequence
                                          (Sassign
                                            (Efield
                                              (Ederef
                                                (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                (Tstruct _ZSTD_DCtx_s noattr))
                                              _streamStage tint)
                                            (Econst_int (Int.repr 1) tint))
                                          (Ssequence
                                            (Ssequence
                                              (Ssequence
                                                (Ssequence
                                                  (Ssequence
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sset _t'9
                                                          (Ecast
                                                            (Econst_int (Int.repr 0) tint)
                                                            tulong))
                                                        (Sassign
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                              (Tstruct _ZSTD_DCtx_s noattr))
                                                            _outEnd tulong)
                                                          (Etempvar _t'9 tulong)))
                                                      (Sset _t'10
                                                        (Ecast
                                                          (Etempvar _t'9 tulong)
                                                          tulong)))
                                                    (Sassign
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                          (Tstruct _ZSTD_DCtx_s noattr))
                                                        _outStart tulong)
                                                      (Etempvar _t'10 tulong)))
                                                  (Sset _t'11
                                                    (Ecast
                                                      (Etempvar _t'10 tulong)
                                                      tulong)))
                                                (Sassign
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                      (Tstruct _ZSTD_DCtx_s noattr))
                                                    _inPos tulong)
                                                  (Etempvar _t'11 tulong)))
                                              (Sassign
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                  _lhSize tulong)
                                                (Etempvar _t'11 tulong)))
                                            (Ssequence
                                              (Sassign
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                  _hostageByte tuint)
                                                (Econst_int (Int.repr 0) tint))
                                              (Scall None
                                                (Evar _ZSTD_outBuffer_copy 
                                                (Tfunction
                                                  ((tptr (Tstruct _ZSTD_outBuffer_s noattr)) ::
                                                   (tptr (Tstruct _ZSTD_outBuffer_s noattr)) ::
                                                   nil) tvoid cc_default))
                                                ((Eaddrof
                                                   (Efield
                                                     (Ederef
                                                       (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                       (Tstruct _ZSTD_DCtx_s noattr))
                                                     _expectedOutBuffer
                                                     (Tstruct _ZSTD_outBuffer_s noattr))
                                                   (tptr (Tstruct _ZSTD_outBuffer_s noattr))) ::
                                                 (Etempvar _output (tptr (Tstruct _ZSTD_outBuffer_s noattr))) ::
                                                 nil)))))).

Definition ds_case_loadHeader : statement :=
(Ssequence
                                          (Sloop Sskip Sbreak)
                                          (Ssequence
                                            (Ssequence
                                              (Ssequence
                                                (Sset _t'165
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                      (Tstruct _ZSTD_DCtx_s noattr))
                                                    _lhSize tulong))
                                                (Ssequence
                                                  (Sset _t'166
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                        (Tstruct _ZSTD_DCtx_s noattr))
                                                      _format tint))
                                                  (Scall (Some _t'12)
                                                    (Evar _ZSTD_getFrameHeader_advanced 
                                                    (Tfunction
                                                      ((tptr (Tstruct ___gp_ZSTD_FrameHeader noattr)) ::
                                                       (tptr tvoid) ::
                                                       tulong :: tint :: nil)
                                                      tulong cc_default))
                                                    ((Eaddrof
                                                       (Efield
                                                         (Ederef
                                                           (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                           (Tstruct _ZSTD_DCtx_s noattr))
                                                         _fParams
                                                         (Tstruct ___gp_ZSTD_FrameHeader noattr))
                                                       (tptr (Tstruct ___gp_ZSTD_FrameHeader noattr))) ::
                                                     (Efield
                                                       (Ederef
                                                         (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                         (Tstruct _ZSTD_DCtx_s noattr))
                                                       _headerBuffer
                                                       (tarray tuchar 18)) ::
                                                     (Etempvar _t'165 tulong) ::
                                                     (Etempvar _t'166 tint) ::
                                                     nil))))
                                              (Sset _hSize
                                                (Etempvar _t'12 tulong)))
                                            (Ssequence
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'163
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                        (Tstruct _ZSTD_DCtx_s noattr))
                                                      _refMultipleDDicts
                                                      tint))
                                                  (Sifthenelse (Etempvar _t'163 tint)
                                                    (Ssequence
                                                      (Sset _t'164
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                            (Tstruct _ZSTD_DCtx_s noattr))
                                                          _ddictSet
                                                          (tptr (Tstruct ___gp_ZSTD_DDictHashSet noattr))))
                                                      (Sset _t'13
                                                        (Ecast
                                                          (Etempvar _t'164 (tptr (Tstruct ___gp_ZSTD_DDictHashSet noattr)))
                                                          tbool)))
                                                    (Sset _t'13
                                                      (Econst_int (Int.repr 0) tint))))
                                                (Sifthenelse (Etempvar _t'13 tint)
                                                  (Scall None
                                                    (Evar _ZSTD_DCtx_selectFrameDDict 
                                                    (Tfunction
                                                      ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
                                                       nil) tvoid cc_default))
                                                    ((Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
                                                     nil))
                                                  Sskip))
                                              (Ssequence
                                                (Ssequence
                                                  (Scall (Some _t'14)
                                                    (Evar _ZSTD_isError 
                                                    (Tfunction
                                                      (tulong :: nil) tuint
                                                      cc_default))
                                                    ((Etempvar _hSize tulong) ::
                                                     nil))
                                                  (Sifthenelse (Etempvar _t'14 tuint)
                                                    (Sreturn (Some (Etempvar _hSize tulong)))
                                                    Sskip))
                                                (Ssequence
                                                  (Sifthenelse (Ebinop One
                                                                 (Etempvar _hSize tulong)
                                                                 (Econst_int (Int.repr 0) tint)
                                                                 tint)
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sset _t'162
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                              (Tstruct _ZSTD_DCtx_s noattr))
                                                            _lhSize tulong))
                                                        (Sset _toLoad
                                                          (Ebinop Osub
                                                            (Etempvar _hSize tulong)
                                                            (Etempvar _t'162 tulong)
                                                            tulong)))
                                                      (Ssequence
                                                        (Sset _remainingInput
                                                          (Ecast
                                                            (Ebinop Osub
                                                              (Etempvar _iend (tptr tschar))
                                                              (Etempvar _ip (tptr tschar))
                                                              tlong) tulong))
                                                        (Ssequence
                                                          (Sifthenelse 
                                                            (Ebinop Ogt
                                                              (Etempvar _toLoad tulong)
                                                              (Etempvar _remainingInput tulong)
                                                              tint)
                                                            (Ssequence
                                                              (Sifthenelse 
                                                                (Ebinop Ogt
                                                                  (Etempvar _remainingInput tulong)
                                                                  (Econst_int (Int.repr 0) tint)
                                                                  tint)
                                                                (Ssequence
                                                                  (Ssequence
                                                                    (Sset _t'161
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _lhSize
                                                                    tulong))
                                                                    (Scall None
                                                                    (Evar _memcpy 
                                                                    (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    (tptr tvoid) ::
                                                                    tulong ::
                                                                    nil)
                                                                    (tptr tvoid)
                                                                    cc_default))
                                                                    ((Ebinop Oadd
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _headerBuffer
                                                                    (tarray tuchar 18))
                                                                    (Etempvar _t'161 tulong)
                                                                    (tptr tuchar)) ::
                                                                    (Etempvar _ip (tptr tschar)) ::
                                                                    (Etempvar _remainingInput tulong) ::
                                                                    nil)))
                                                                  (Ssequence
                                                                    (Sset _t'160
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _lhSize
                                                                    tulong))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _lhSize
                                                                    tulong)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'160 tulong)
                                                                    (Etempvar _remainingInput tulong)
                                                                    tulong))))
                                                                Sskip)
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Sset _t'159
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _input (tptr (Tstruct _ZSTD_inBuffer_s noattr)))
                                                                    (Tstruct _ZSTD_inBuffer_s noattr))
                                                                    _size
                                                                    tulong))
                                                                  (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _input (tptr (Tstruct _ZSTD_inBuffer_s noattr)))
                                                                    (Tstruct _ZSTD_inBuffer_s noattr))
                                                                    _pos
                                                                    tulong)
                                                                    (Etempvar _t'159 tulong)))
                                                                (Ssequence
                                                                  (Sloop
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'157
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _lhSize
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _t'158
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _format
                                                                    tint))
                                                                    (Scall (Some _t'15)
                                                                    (Evar _ZSTD_getFrameHeader_advanced 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct ___gp_ZSTD_FrameHeader noattr)) ::
                                                                    (tptr tvoid) ::
                                                                    tulong ::
                                                                    tint ::
                                                                    nil)
                                                                    tulong
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _fParams
                                                                    (Tstruct ___gp_ZSTD_FrameHeader noattr))
                                                                    (tptr (Tstruct ___gp_ZSTD_FrameHeader noattr))) ::
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _headerBuffer
                                                                    (tarray tuchar 18)) ::
                                                                    (Etempvar _t'157 tulong) ::
                                                                    (Etempvar _t'158 tint) ::
                                                                    nil))))
                                                                    (Sset _err_code__1
                                                                    (Etempvar _t'15 tulong)))
                                                                    (Ssequence
                                                                    (Scall (Some _t'16)
                                                                    (Evar _ERR_isError 
                                                                    (Tfunction
                                                                    (tulong ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                    ((Etempvar _err_code__1 tulong) ::
                                                                    nil))
                                                                    (Sifthenelse (Etempvar _t'16 tuint)
                                                                    (Ssequence
                                                                    (Sloop
                                                                    Sskip
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Sifthenelse (Econst_int (Int.repr 0) tint)
                                                                    (Scall None
                                                                    (Evar __force_has_format_string 
                                                                    (Tfunction
                                                                    ((tptr tschar) ::
                                                                    nil)
                                                                    tvoid
                                                                    {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                                                                    ((Evar ___stringlit_zstd_67 (tarray tschar 35)) ::
                                                                    nil))
                                                                    Sskip)
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Sloop
                                                                    Sskip
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Sloop
                                                                    Sskip
                                                                    Sbreak)
                                                                    (Sreturn (Some (Etempvar _err_code__1 tulong)))))))
                                                                    Sskip)))
                                                                    Sbreak)
                                                                  (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'154
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _format
                                                                    tint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'154 tint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _t'155
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _lhSize
                                                                    tulong))
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _t'155 tulong)
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tint)
                                                                    (Sset _t'18
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tbool))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'156
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _lhSize
                                                                    tulong))
                                                                    (Scall (Some _t'19)
                                                                    (Evar _ZSTD_isSkippableFrame 
                                                                    (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    tulong ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _headerBuffer
                                                                    (tarray tuchar 18)) ::
                                                                    (Etempvar _t'156 tulong) ::
                                                                    nil)))
                                                                    (Sset _t'18
                                                                    (Ecast
                                                                    (Etempvar _t'19 tuint)
                                                                    tbool)))
                                                                    (Sset _t'18
                                                                    (Ecast
                                                                    (Etempvar _t'18 tint)
                                                                    tbool)))))
                                                                    (Sset _t'18
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse (Etempvar _t'18 tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'153
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _lhSize
                                                                    tulong))
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _t'153 tulong)
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tint)
                                                                    (Sset _t'17
                                                                    (Ecast
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Sset _t'17
                                                                    (Ecast
                                                                    (Etempvar _hSize tulong)
                                                                    tulong))))
                                                                    (Ssequence
                                                                    (Sset _t'152
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _lhSize
                                                                    tulong))
                                                                    (Sreturn (Some 
                                                                    (Ebinop Osub
                                                                    (Etempvar _t'17 tulong)
                                                                    (Etempvar _t'152 tulong)
                                                                    tulong)))))
                                                                    Sskip))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'151
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _format
                                                                    tint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'151 tint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Sset _t'20
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 6) tint)
                                                                    tint))
                                                                    (Sset _t'20
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint))))
                                                                    (Sifthenelse 
                                                                    (Ebinop Ogt
                                                                    (Ecast
                                                                    (Etempvar _t'20 tint)
                                                                    tulong)
                                                                    (Etempvar _hSize tulong)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'150
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _format
                                                                    tint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'150 tint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Sset _t'22
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 6) tint)
                                                                    tint))
                                                                    (Sset _t'22
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint))))
                                                                    (Sset _t'21
                                                                    (Ecast
                                                                    (Ecast
                                                                    (Etempvar _t'22 tint)
                                                                    tulong)
                                                                    tulong)))
                                                                    (Sset _t'21
                                                                    (Ecast
                                                                    (Etempvar _hSize tulong)
                                                                    tulong))))
                                                                    (Ssequence
                                                                    (Sset _t'148
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _lhSize
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _t'149
                                                                    (Evar _ZSTD_blockHeaderSize tulong))
                                                                    (Sreturn (Some 
                                                                    (Ebinop Oadd
                                                                    (Ebinop Osub
                                                                    (Etempvar _t'21 tulong)
                                                                    (Etempvar _t'148 tulong)
                                                                    tulong)
                                                                    (Etempvar _t'149 tulong)
                                                                    tulong))))))))))
                                                            Sskip)
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _t'147
                                                                (Efield
                                                                  (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                  _lhSize
                                                                  tulong))
                                                              (Scall None
                                                                (Evar _memcpy 
                                                                (Tfunction
                                                                  ((tptr tvoid) ::
                                                                   (tptr tvoid) ::
                                                                   tulong ::
                                                                   nil)
                                                                  (tptr tvoid)
                                                                  cc_default))
                                                                ((Ebinop Oadd
                                                                   (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _headerBuffer
                                                                    (tarray tuchar 18))
                                                                   (Etempvar _t'147 tulong)
                                                                   (tptr tuchar)) ::
                                                                 (Etempvar _ip (tptr tschar)) ::
                                                                 (Etempvar _toLoad tulong) ::
                                                                 nil)))
                                                            (Ssequence
                                                              (Sassign
                                                                (Efield
                                                                  (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                  _lhSize
                                                                  tulong)
                                                                (Etempvar _hSize tulong))
                                                              (Ssequence
                                                                (Sset _ip
                                                                  (Ebinop Oadd
                                                                    (Etempvar _ip (tptr tschar))
                                                                    (Etempvar _toLoad tulong)
                                                                    (tptr tschar)))
                                                                Sbreak))))))
                                                    Sskip)
                                                  (Ssequence
                                                    (Ssequence
                                                      (Ssequence
                                                        (Ssequence
                                                          (Ssequence
                                                            (Sset _t'145
                                                              (Efield
                                                                (Efield
                                                                  (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                  _fParams
                                                                  (Tstruct ___gp_ZSTD_FrameHeader noattr))
                                                                _frameContentSize
                                                                tulong))
                                                            (Sifthenelse 
                                                              (Ebinop One
                                                                (Etempvar _t'145 tulong)
                                                                (Ebinop Osub
                                                                  (Econst_long (Int64.repr 0) tulong)
                                                                  (Econst_int (Int.repr 1) tint)
                                                                  tulong)
                                                                tint)
                                                              (Ssequence
                                                                (Sset _t'146
                                                                  (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _fParams
                                                                    (Tstruct ___gp_ZSTD_FrameHeader noattr))
                                                                    _frameType
                                                                    tint))
                                                                (Sset _t'28
                                                                  (Ecast
                                                                    (Ebinop One
                                                                    (Etempvar _t'146 tint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    tbool)))
                                                              (Sset _t'28
                                                                (Econst_int (Int.repr 0) tint))))
                                                          (Sifthenelse (Etempvar _t'28 tint)
                                                            (Ssequence
                                                              (Sset _t'143
                                                                (Evar _op (tptr tschar)))
                                                              (Ssequence
                                                                (Sset _t'144
                                                                  (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _fParams
                                                                    (Tstruct ___gp_ZSTD_FrameHeader noattr))
                                                                    _frameContentSize
                                                                    tulong))
                                                                (Sset _t'29
                                                                  (Ecast
                                                                    (Ebinop Oge
                                                                    (Ecast
                                                                    (Ecast
                                                                    (Ebinop Osub
                                                                    (Etempvar _oend (tptr tschar))
                                                                    (Etempvar _t'143 (tptr tschar))
                                                                    tlong)
                                                                    tulong)
                                                                    tulong)
                                                                    (Etempvar _t'144 tulong)
                                                                    tint)
                                                                    tbool))))
                                                            (Sset _t'29
                                                              (Econst_int (Int.repr 0) tint))))
                                                        (Sifthenelse (Etempvar _t'29 tint)
                                                          (Ssequence
                                                            (Sset _t'142
                                                              (Efield
                                                                (Ederef
                                                                  (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                  (Tstruct _ZSTD_DCtx_s noattr))
                                                                _lhSize
                                                                tulong))
                                                            (Sset _t'30
                                                              (Ecast
                                                                (Ebinop Oeq
                                                                  (Etempvar _t'142 tulong)
                                                                  (Ecast
                                                                    (Ebinop Osub
                                                                    (Etempvar _ip (tptr tschar))
                                                                    (Etempvar _istart (tptr tschar))
                                                                    tlong)
                                                                    tulong)
                                                                  tint)
                                                                tbool)))
                                                          (Sset _t'30
                                                            (Econst_int (Int.repr 0) tint))))
                                                      (Sifthenelse (Etempvar _t'30 tint)
                                                        (Ssequence
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _t'141
                                                                (Efield
                                                                  (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                  _format
                                                                  tint))
                                                              (Scall (Some _t'23)
                                                                (Evar _ZSTD_findFrameCompressedSize_advanced 
                                                                (Tfunction
                                                                  ((tptr tvoid) ::
                                                                   tulong ::
                                                                   tint ::
                                                                   nil)
                                                                  tulong
                                                                  cc_default))
                                                                ((Etempvar _istart (tptr tschar)) ::
                                                                 (Ecast
                                                                   (Ebinop Osub
                                                                    (Etempvar _iend (tptr tschar))
                                                                    (Etempvar _istart (tptr tschar))
                                                                    tlong)
                                                                   tulong) ::
                                                                 (Etempvar _t'141 tint) ::
                                                                 nil)))
                                                            (Sset _cSize
                                                              (Etempvar _t'23 tulong)))
                                                          (Sifthenelse 
                                                            (Ebinop Ole
                                                              (Etempvar _cSize tulong)
                                                              (Ecast
                                                                (Ebinop Osub
                                                                  (Etempvar _iend (tptr tschar))
                                                                  (Etempvar _istart (tptr tschar))
                                                                  tlong)
                                                                tulong) tint)
                                                            (Ssequence
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Scall (Some _t'24)
                                                                    (Evar _ZSTD_getDDict 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
                                                                    nil)
                                                                    (tptr (Tstruct _ZSTD_DDict_s noattr))
                                                                    cc_default))
                                                                    ((Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
                                                                    nil))
                                                                  (Ssequence
                                                                    (Sset _t'139
                                                                    (Evar _op (tptr tschar)))
                                                                    (Ssequence
                                                                    (Sset _t'140
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _fParams
                                                                    (Tstruct ___gp_ZSTD_FrameHeader noattr))
                                                                    _frameContentSize
                                                                    tulong))
                                                                    (Scall (Some _t'25)
                                                                    (Evar _ZSTD_decompress_usingDDict 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
                                                                    (tptr tvoid) ::
                                                                    tulong ::
                                                                    (tptr tvoid) ::
                                                                    tulong ::
                                                                    (tptr (Tstruct _ZSTD_DDict_s noattr)) ::
                                                                    nil)
                                                                    tulong
                                                                    cc_default))
                                                                    ((Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
                                                                    (Etempvar _t'139 (tptr tschar)) ::
                                                                    (Ecast
                                                                    (Etempvar _t'140 tulong)
                                                                    tulong) ::
                                                                    (Etempvar _istart (tptr tschar)) ::
                                                                    (Etempvar _cSize tulong) ::
                                                                    (Etempvar _t'24 (tptr (Tstruct _ZSTD_DDict_s noattr))) ::
                                                                    nil)))))
                                                                (Sset _decompressedSize
                                                                  (Etempvar _t'25 tulong)))
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Scall (Some _t'26)
                                                                    (Evar _ZSTD_isError 
                                                                    (Tfunction
                                                                    (tulong ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                    ((Etempvar _decompressedSize tulong) ::
                                                                    nil))
                                                                  (Sifthenelse (Etempvar _t'26 tuint)
                                                                    (Sreturn (Some (Etempvar _decompressedSize tulong)))
                                                                    Sskip))
                                                                (Ssequence
                                                                  (Sloop
                                                                    Sskip
                                                                    Sbreak)
                                                                  (Ssequence
                                                                    (Sset _ip
                                                                    (Ebinop Oadd
                                                                    (Etempvar _istart (tptr tschar))
                                                                    (Etempvar _cSize tulong)
                                                                    (tptr tschar)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'136
                                                                    (Evar _op (tptr tschar)))
                                                                    (Sifthenelse (Etempvar _t'136 (tptr tschar))
                                                                    (Ssequence
                                                                    (Sset _t'138
                                                                    (Evar _op (tptr tschar)))
                                                                    (Sset _t'27
                                                                    (Ecast
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'138 (tptr tschar))
                                                                    (Etempvar _decompressedSize tulong)
                                                                    (tptr tschar))
                                                                    (tptr tschar))))
                                                                    (Ssequence
                                                                    (Sset _t'137
                                                                    (Evar _op (tptr tschar)))
                                                                    (Sset _t'27
                                                                    (Ecast
                                                                    (Etempvar _t'137 (tptr tschar))
                                                                    (tptr tschar))))))
                                                                    (Sassign
                                                                    (Evar _op (tptr tschar))
                                                                    (Etempvar _t'27 (tptr tschar))))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _expected
                                                                    tulong)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _streamStage
                                                                    tint)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sset _someMoreWork
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    Sbreak))))))))
                                                            Sskip))
                                                        Sskip))
                                                    (Ssequence
                                                      (Ssequence
                                                        (Ssequence
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _t'134
                                                                (Efield
                                                                  (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                  _outBufferMode
                                                                  tint))
                                                              (Sifthenelse 
                                                                (Ebinop Oeq
                                                                  (Etempvar _t'134 tint)
                                                                  (Econst_int (Int.repr 1) tint)
                                                                  tint)
                                                                (Ssequence
                                                                  (Sset _t'135
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _fParams
                                                                    (Tstruct ___gp_ZSTD_FrameHeader noattr))
                                                                    _frameType
                                                                    tint))
                                                                  (Sset _t'31
                                                                    (Ecast
                                                                    (Ebinop One
                                                                    (Etempvar _t'135 tint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    tbool)))
                                                                (Sset _t'31
                                                                  (Econst_int (Int.repr 0) tint))))
                                                            (Sifthenelse (Etempvar _t'31 tint)
                                                              (Ssequence
                                                                (Sset _t'133
                                                                  (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _fParams
                                                                    (Tstruct ___gp_ZSTD_FrameHeader noattr))
                                                                    _frameContentSize
                                                                    tulong))
                                                                (Sset _t'32
                                                                  (Ecast
                                                                    (Ebinop One
                                                                    (Etempvar _t'133 tulong)
                                                                    (Ebinop Osub
                                                                    (Econst_long (Int64.repr 0) tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong)
                                                                    tint)
                                                                    tbool)))
                                                              (Sset _t'32
                                                                (Econst_int (Int.repr 0) tint))))
                                                          (Sifthenelse (Etempvar _t'32 tint)
                                                            (Ssequence
                                                              (Sset _t'131
                                                                (Evar _op (tptr tschar)))
                                                              (Ssequence
                                                                (Sset _t'132
                                                                  (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _fParams
                                                                    (Tstruct ___gp_ZSTD_FrameHeader noattr))
                                                                    _frameContentSize
                                                                    tulong))
                                                                (Sset _t'33
                                                                  (Ecast
                                                                    (Ebinop Olt
                                                                    (Ecast
                                                                    (Ecast
                                                                    (Ebinop Osub
                                                                    (Etempvar _oend (tptr tschar))
                                                                    (Etempvar _t'131 (tptr tschar))
                                                                    tlong)
                                                                    tulong)
                                                                    tulong)
                                                                    (Etempvar _t'132 tulong)
                                                                    tint)
                                                                    tbool))))
                                                            (Sset _t'33
                                                              (Econst_int (Int.repr 0) tint))))
                                                        (Sifthenelse (Etempvar _t'33 tint)
                                                          (Sloop
                                                            (Ssequence
                                                              (Sloop
                                                                Sskip
                                                                Sbreak)
                                                              (Ssequence
                                                                (Sloop
                                                                  (Sifthenelse (Econst_int (Int.repr 0) tint)
                                                                    (Scall None
                                                                    (Evar __force_has_format_string 
                                                                    (Tfunction
                                                                    ((tptr tschar) ::
                                                                    nil)
                                                                    tvoid
                                                                    {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                                                                    ((Evar ___stringlit_zstd_68 (tarray tschar 55)) ::
                                                                    nil))
                                                                    Sskip)
                                                                  Sbreak)
                                                                (Ssequence
                                                                  (Sloop
                                                                    Sskip
                                                                    Sbreak)
                                                                  (Ssequence
                                                                    (Sloop
                                                                    Sskip
                                                                    Sbreak)
                                                                    (Sreturn (Some 
                                                                    (Ecast
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 70) tint)
                                                                    tint)
                                                                    tulong)))))))
                                                            Sbreak)
                                                          Sskip))
                                                      (Ssequence
                                                        (Sloop Sskip Sbreak)
                                                        (Ssequence
                                                          (Sloop
                                                            (Ssequence
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Scall (Some _t'34)
                                                                    (Evar _ZSTD_getDDict 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
                                                                    nil)
                                                                    (tptr (Tstruct _ZSTD_DDict_s noattr))
                                                                    cc_default))
                                                                    ((Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
                                                                    nil))
                                                                  (Scall (Some _t'35)
                                                                    (Evar _ZSTD_decompressBegin_usingDDict 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
                                                                    (tptr (Tstruct _ZSTD_DDict_s noattr)) ::
                                                                    nil)
                                                                    tulong
                                                                    cc_default))
                                                                    ((Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
                                                                    (Etempvar _t'34 (tptr (Tstruct _ZSTD_DDict_s noattr))) ::
                                                                    nil)))
                                                                (Sset _err_code__2
                                                                  (Etempvar _t'35 tulong)))
                                                              (Ssequence
                                                                (Scall (Some _t'36)
                                                                  (Evar _ERR_isError 
                                                                  (Tfunction
                                                                    (tulong ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                  ((Etempvar _err_code__2 tulong) ::
                                                                   nil))
                                                                (Sifthenelse (Etempvar _t'36 tuint)
                                                                  (Ssequence
                                                                    (Sloop
                                                                    Sskip
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Sifthenelse (Econst_int (Int.repr 0) tint)
                                                                    (Scall None
                                                                    (Evar __force_has_format_string 
                                                                    (Tfunction
                                                                    ((tptr tschar) ::
                                                                    nil)
                                                                    tvoid
                                                                    {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                                                                    ((Evar ___stringlit_zstd_37 (tarray tschar 1)) ::
                                                                    nil))
                                                                    Sskip)
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Sloop
                                                                    Sskip
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Sloop
                                                                    Sskip
                                                                    Sbreak)
                                                                    (Sreturn (Some (Etempvar _err_code__2 tulong)))))))
                                                                  Sskip)))
                                                            Sbreak)
                                                          (Ssequence
                                                            (Ssequence
                                                              (Ssequence
                                                                (Sset _t'130
                                                                  (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _format
                                                                    tint))
                                                                (Sifthenelse 
                                                                  (Ebinop Oeq
                                                                    (Etempvar _t'130 tint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                  (Ssequence
                                                                    (Scall (Some _t'41)
                                                                    (Evar _MEM_readLE32 
                                                                    (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _headerBuffer
                                                                    (tarray tuchar 18)) ::
                                                                    nil))
                                                                    (Sset _t'40
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Ebinop Oand
                                                                    (Etempvar _t'41 tuint)
                                                                    (Econst_int (Int.repr (-16)) tuint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 407710288) tint)
                                                                    tint)
                                                                    tbool)))
                                                                  (Sset _t'40
                                                                    (Econst_int (Int.repr 0) tint))))
                                                              (Sifthenelse (Etempvar _t'40 tint)
                                                                (Ssequence
                                                                  (Ssequence
                                                                    (Scall (Some _t'37)
                                                                    (Evar _MEM_readLE32 
                                                                    (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                    ((Ebinop Oadd
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _headerBuffer
                                                                    (tarray tuchar 18))
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    (tptr tuchar)) ::
                                                                    nil))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _expected
                                                                    tulong)
                                                                    (Etempvar _t'37 tuint)))
                                                                  (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _stage
                                                                    tint)
                                                                    (Econst_int (Int.repr 7) tint)))
                                                                (Ssequence
                                                                  (Sloop
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'129
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _lhSize
                                                                    tulong))
                                                                    (Scall (Some _t'38)
                                                                    (Evar _ZSTD_decodeFrameHeader 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
                                                                    (tptr tvoid) ::
                                                                    tulong ::
                                                                    nil)
                                                                    tulong
                                                                    cc_default))
                                                                    ((Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _headerBuffer
                                                                    (tarray tuchar 18)) ::
                                                                    (Etempvar _t'129 tulong) ::
                                                                    nil)))
                                                                    (Sset _err_code__3
                                                                    (Etempvar _t'38 tulong)))
                                                                    (Ssequence
                                                                    (Scall (Some _t'39)
                                                                    (Evar _ERR_isError 
                                                                    (Tfunction
                                                                    (tulong ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                    ((Etempvar _err_code__3 tulong) ::
                                                                    nil))
                                                                    (Sifthenelse (Etempvar _t'39 tuint)
                                                                    (Ssequence
                                                                    (Sloop
                                                                    Sskip
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Sifthenelse (Econst_int (Int.repr 0) tint)
                                                                    (Scall None
                                                                    (Evar __force_has_format_string 
                                                                    (Tfunction
                                                                    ((tptr tschar) ::
                                                                    nil)
                                                                    tvoid
                                                                    {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                                                                    ((Evar ___stringlit_zstd_37 (tarray tschar 1)) ::
                                                                    nil))
                                                                    Sskip)
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Sloop
                                                                    Sskip
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Sloop
                                                                    Sskip
                                                                    Sbreak)
                                                                    (Sreturn (Some (Etempvar _err_code__3 tulong)))))))
                                                                    Sskip)))
                                                                    Sbreak)
                                                                  (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'128
                                                                    (Evar _ZSTD_blockHeaderSize tulong))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _expected
                                                                    tulong)
                                                                    (Etempvar _t'128 tulong)))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _stage
                                                                    tint)
                                                                    (Econst_int (Int.repr 2) tint))))))
                                                            (Ssequence
                                                              (Sloop
                                                                Sskip
                                                                Sbreak)
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Ssequence
                                                                    (Sset _t'126
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _fParams
                                                                    (Tstruct ___gp_ZSTD_FrameHeader noattr))
                                                                    _windowSize
                                                                    tulong))
                                                                    (Sifthenelse 
                                                                    (Ebinop Ogt
                                                                    (Etempvar _t'126 tulong)
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tuint)
                                                                    (Econst_int (Int.repr 10) tint)
                                                                    tuint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _t'127
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _fParams
                                                                    (Tstruct ___gp_ZSTD_FrameHeader noattr))
                                                                    _windowSize
                                                                    tulong))
                                                                    (Sset _t'42
                                                                    (Ecast
                                                                    (Etempvar _t'127 tulong)
                                                                    tulong)))
                                                                    (Sset _t'42
                                                                    (Ecast
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tuint)
                                                                    (Econst_int (Int.repr 10) tint)
                                                                    tuint)
                                                                    tulong))))
                                                                  (Sassign
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _fParams
                                                                    (Tstruct ___gp_ZSTD_FrameHeader noattr))
                                                                    _windowSize
                                                                    tulong)
                                                                    (Etempvar _t'42 tulong)))
                                                                (Ssequence
                                                                  (Sloop
                                                                    (Ssequence
                                                                    (Sset _t'124
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _fParams
                                                                    (Tstruct ___gp_ZSTD_FrameHeader noattr))
                                                                    _windowSize
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _t'125
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _maxWindowSize
                                                                    tulong))
                                                                    (Sifthenelse 
                                                                    (Ebinop Ogt
                                                                    (Etempvar _t'124 tulong)
                                                                    (Etempvar _t'125 tulong)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sloop
                                                                    Sskip
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Sifthenelse (Econst_int (Int.repr 0) tint)
                                                                    (Scall None
                                                                    (Evar __force_has_format_string 
                                                                    (Tfunction
                                                                    ((tptr tschar) ::
                                                                    nil)
                                                                    tvoid
                                                                    {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                                                                    ((Evar ___stringlit_zstd_37 (tarray tschar 1)) ::
                                                                    nil))
                                                                    Sskip)
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Sloop
                                                                    Sskip
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Sloop
                                                                    Sskip
                                                                    Sbreak)
                                                                    (Sreturn (Some 
                                                                    (Ecast
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 16) tint)
                                                                    tint)
                                                                    tulong)))))))
                                                                    Sskip)))
                                                                    Sbreak)
                                                                  (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'119
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _maxBlockSizeParam
                                                                    tint))
                                                                    (Sifthenelse 
                                                                    (Ebinop One
                                                                    (Etempvar _t'119 tint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'120
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _fParams
                                                                    (Tstruct ___gp_ZSTD_FrameHeader noattr))
                                                                    _blockSizeMax
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'121
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _maxBlockSizeParam
                                                                    tint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _t'120 tuint)
                                                                    (Ecast
                                                                    (Etempvar _t'121 tint)
                                                                    tuint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _t'123
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _fParams
                                                                    (Tstruct ___gp_ZSTD_FrameHeader noattr))
                                                                    _blockSizeMax
                                                                    tuint))
                                                                    (Sset _t'43
                                                                    (Ecast
                                                                    (Etempvar _t'123 tuint)
                                                                    tuint)))
                                                                    (Ssequence
                                                                    (Sset _t'122
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _maxBlockSizeParam
                                                                    tint))
                                                                    (Sset _t'43
                                                                    (Ecast
                                                                    (Ecast
                                                                    (Etempvar _t'122 tint)
                                                                    tuint)
                                                                    tuint))))))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _fParams
                                                                    (Tstruct ___gp_ZSTD_FrameHeader noattr))
                                                                    _blockSizeMax
                                                                    tuint)
                                                                    (Etempvar _t'43 tuint)))
                                                                    Sskip))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'117
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _fParams
                                                                    (Tstruct ___gp_ZSTD_FrameHeader noattr))
                                                                    _blockSizeMax
                                                                    tuint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Ogt
                                                                    (Etempvar _t'117 tuint)
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _t'118
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _fParams
                                                                    (Tstruct ___gp_ZSTD_FrameHeader noattr))
                                                                    _blockSizeMax
                                                                    tuint))
                                                                    (Sset _t'44
                                                                    (Ecast
                                                                    (Etempvar _t'118 tuint)
                                                                    tuint)))
                                                                    (Sset _t'44
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tuint))))
                                                                    (Sset _neededInBuffSize
                                                                    (Ecast
                                                                    (Etempvar _t'44 tuint)
                                                                    tulong)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'113
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _outBufferMode
                                                                    tint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'113 tint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'114
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _fParams
                                                                    (Tstruct ___gp_ZSTD_FrameHeader noattr))
                                                                    _windowSize
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _t'115
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _fParams
                                                                    (Tstruct ___gp_ZSTD_FrameHeader noattr))
                                                                    _frameContentSize
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _t'116
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _fParams
                                                                    (Tstruct ___gp_ZSTD_FrameHeader noattr))
                                                                    _blockSizeMax
                                                                    tuint))
                                                                    (Scall (Some _t'46)
                                                                    (Evar _ZSTD_decodingBufferSize_internal 
                                                                    (Tfunction
                                                                    (tulong ::
                                                                    tulong ::
                                                                    tulong ::
                                                                    nil)
                                                                    tulong
                                                                    cc_default))
                                                                    ((Etempvar _t'114 tulong) ::
                                                                    (Etempvar _t'115 tulong) ::
                                                                    (Etempvar _t'116 tuint) ::
                                                                    nil)))))
                                                                    (Sset _t'45
                                                                    (Ecast
                                                                    (Etempvar _t'46 tulong)
                                                                    tulong)))
                                                                    (Sset _t'45
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tulong))))
                                                                    (Sset _neededOutBuffSize
                                                                    (Etempvar _t'45 tulong)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _ZSTD_DCtx_updateOversizedDuration 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
                                                                    tulong ::
                                                                    tulong ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
                                                                    (Etempvar _neededInBuffSize tulong) ::
                                                                    (Etempvar _neededOutBuffSize tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'111
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _inBuffSize
                                                                    tulong))
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _t'111 tulong)
                                                                    (Etempvar _neededInBuffSize tulong)
                                                                    tint)
                                                                    (Sset _t'47
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    (Ssequence
                                                                    (Sset _t'112
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _outBuffSize
                                                                    tulong))
                                                                    (Sset _t'47
                                                                    (Ecast
                                                                    (Ebinop Olt
                                                                    (Etempvar _t'112 tulong)
                                                                    (Etempvar _neededOutBuffSize tulong)
                                                                    tint)
                                                                    tbool)))))
                                                                    (Sset _tooSmall
                                                                    (Etempvar _t'47 tint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'48)
                                                                    (Evar _ZSTD_DCtx_isOversizedTooLong 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
                                                                    nil))
                                                                    (Sset _tooLarge
                                                                    (Etempvar _t'48 tint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sifthenelse (Etempvar _tooSmall tint)
                                                                    (Sset _t'50
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    (Sset _t'50
                                                                    (Ecast
                                                                    (Etempvar _tooLarge tint)
                                                                    tbool)))
                                                                    (Sifthenelse (Etempvar _t'50 tint)
                                                                    (Ssequence
                                                                    (Sset _bufferSize
                                                                    (Ebinop Oadd
                                                                    (Etempvar _neededInBuffSize tulong)
                                                                    (Etempvar _neededOutBuffSize tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sloop
                                                                    Sskip
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Sloop
                                                                    Sskip
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'107
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _staticSize
                                                                    tulong))
                                                                    (Sifthenelse (Etempvar _t'107 tulong)
                                                                    (Ssequence
                                                                    (Sloop
                                                                    Sskip
                                                                    Sbreak)
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Sset _t'110
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _staticSize
                                                                    tulong))
                                                                    (Sifthenelse 
                                                                    (Ebinop Ogt
                                                                    (Etempvar _bufferSize tulong)
                                                                    (Ebinop Osub
                                                                    (Etempvar _t'110 tulong)
                                                                    (Esizeof (Tstruct _ZSTD_DCtx_s noattr) tulong)
                                                                    tulong)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sloop
                                                                    Sskip
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Sifthenelse (Econst_int (Int.repr 0) tint)
                                                                    (Scall None
                                                                    (Evar __force_has_format_string 
                                                                    (Tfunction
                                                                    ((tptr tschar) ::
                                                                    nil)
                                                                    tvoid
                                                                    {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                                                                    ((Evar ___stringlit_zstd_37 (tarray tschar 1)) ::
                                                                    nil))
                                                                    Sskip)
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Sloop
                                                                    Sskip
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Sloop
                                                                    Sskip
                                                                    Sbreak)
                                                                    (Sreturn (Some 
                                                                    (Ecast
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 64) tint)
                                                                    tint)
                                                                    tulong)))))))
                                                                    Sskip))
                                                                    Sbreak))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'109
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _inBuff
                                                                    (tptr tschar)))
                                                                    (Scall None
                                                                    (Evar _ZSTD_customFreeP 
                                                                    (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    (tptr (Tstruct ___gp_ZSTD_customMem noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _t'109 (tptr tschar)) ::
                                                                    (Eaddrof
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _customMem
                                                                    (Tstruct ___gp_ZSTD_customMem noattr))
                                                                    (tptr (Tstruct ___gp_ZSTD_customMem noattr))) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _inBuffSize
                                                                    tulong)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _outBuffSize
                                                                    tulong)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'49)
                                                                    (Evar _ZSTD_customCallocP 
                                                                    (Tfunction
                                                                    (tulong ::
                                                                    (tptr (Tstruct ___gp_ZSTD_customMem noattr)) ::
                                                                    nil)
                                                                    (tptr tvoid)
                                                                    cc_default))
                                                                    ((Etempvar _bufferSize tulong) ::
                                                                    (Eaddrof
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _customMem
                                                                    (Tstruct ___gp_ZSTD_customMem noattr))
                                                                    (tptr (Tstruct ___gp_ZSTD_customMem noattr))) ::
                                                                    nil))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _inBuff
                                                                    (tptr tschar))
                                                                    (Ecast
                                                                    (Etempvar _t'49 (tptr tvoid))
                                                                    (tptr tschar))))
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Sset _t'108
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _inBuff
                                                                    (tptr tschar)))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'108 (tptr tschar))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sloop
                                                                    Sskip
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Sifthenelse (Econst_int (Int.repr 0) tint)
                                                                    (Scall None
                                                                    (Evar __force_has_format_string 
                                                                    (Tfunction
                                                                    ((tptr tschar) ::
                                                                    nil)
                                                                    tvoid
                                                                    {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                                                                    ((Evar ___stringlit_zstd_37 (tarray tschar 1)) ::
                                                                    nil))
                                                                    Sskip)
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Sloop
                                                                    Sskip
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Sloop
                                                                    Sskip
                                                                    Sbreak)
                                                                    (Sreturn (Some 
                                                                    (Ecast
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 64) tint)
                                                                    tint)
                                                                    tulong)))))))
                                                                    Sskip))
                                                                    Sbreak)))))))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _inBuffSize
                                                                    tulong)
                                                                    (Etempvar _neededInBuffSize tulong))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'105
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _inBuff
                                                                    (tptr tschar)))
                                                                    (Ssequence
                                                                    (Sset _t'106
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _inBuffSize
                                                                    tulong))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _outBuff
                                                                    (tptr tschar))
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'105 (tptr tschar))
                                                                    (Etempvar _t'106 tulong)
                                                                    (tptr tschar)))))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _outBuffSize
                                                                    tulong)
                                                                    (Etempvar _neededOutBuffSize tulong))))))))
                                                                    Sskip))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _streamStage
                                                                    tint)
                                                                    (Econst_int (Int.repr 2) tint)))))))))))))))))))))).

Definition ds_case_read : statement :=
(Ssequence
                                            (Sloop Sskip Sbreak)
                                            (Ssequence
                                              (Ssequence
                                                (Scall (Some _t'51)
                                                  (Evar _ZSTD_nextSrcSizeToDecompressWithInputSize 
                                                  (Tfunction
                                                    ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
                                                     tulong :: nil) tulong
                                                    cc_default))
                                                  ((Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
                                                   (Ecast
                                                     (Ebinop Osub
                                                       (Etempvar _iend (tptr tschar))
                                                       (Etempvar _ip (tptr tschar))
                                                       tlong) tulong) :: nil))
                                                (Sset _neededInSize
                                                  (Etempvar _t'51 tulong)))
                                              (Ssequence
                                                (Sloop Sskip Sbreak)
                                                (Ssequence
                                                  (Sifthenelse (Ebinop Oeq
                                                                 (Etempvar _neededInSize tulong)
                                                                 (Econst_int (Int.repr 0) tint)
                                                                 tint)
                                                    (Ssequence
                                                      (Sassign
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                            (Tstruct _ZSTD_DCtx_s noattr))
                                                          _streamStage tint)
                                                        (Econst_int (Int.repr 0) tint))
                                                      (Ssequence
                                                        (Sset _someMoreWork
                                                          (Econst_int (Int.repr 0) tint))
                                                        Sbreak))
                                                    Sskip)
                                                  (Ssequence
                                                    (Sifthenelse (Ebinop Oge
                                                                   (Ecast
                                                                    (Ebinop Osub
                                                                    (Etempvar _iend (tptr tschar))
                                                                    (Etempvar _ip (tptr tschar))
                                                                    tlong)
                                                                    tulong)
                                                                   (Etempvar _neededInSize tulong)
                                                                   tint)
                                                      (Ssequence
                                                        (Sloop
                                                          (Ssequence
                                                            (Ssequence
                                                              (Scall (Some _t'52)
                                                                (Evar _ZSTD_decompressContinueStream 
                                                                (Tfunction
                                                                  ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
                                                                   (tptr (tptr tschar)) ::
                                                                   (tptr tschar) ::
                                                                   (tptr tvoid) ::
                                                                   tulong ::
                                                                   nil)
                                                                  tulong
                                                                  cc_default))
                                                                ((Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
                                                                 (Eaddrof
                                                                   (Evar _op (tptr tschar))
                                                                   (tptr (tptr tschar))) ::
                                                                 (Etempvar _oend (tptr tschar)) ::
                                                                 (Etempvar _ip (tptr tschar)) ::
                                                                 (Etempvar _neededInSize tulong) ::
                                                                 nil))
                                                              (Sset _err_code__4
                                                                (Etempvar _t'52 tulong)))
                                                            (Ssequence
                                                              (Scall (Some _t'53)
                                                                (Evar _ERR_isError 
                                                                (Tfunction
                                                                  (tulong ::
                                                                   nil) tuint
                                                                  cc_default))
                                                                ((Etempvar _err_code__4 tulong) ::
                                                                 nil))
                                                              (Sifthenelse (Etempvar _t'53 tuint)
                                                                (Ssequence
                                                                  (Sloop
                                                                    Sskip
                                                                    Sbreak)
                                                                  (Ssequence
                                                                    (Sloop
                                                                    (Sifthenelse (Econst_int (Int.repr 0) tint)
                                                                    (Scall None
                                                                    (Evar __force_has_format_string 
                                                                    (Tfunction
                                                                    ((tptr tschar) ::
                                                                    nil)
                                                                    tvoid
                                                                    {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                                                                    ((Evar ___stringlit_zstd_37 (tarray tschar 1)) ::
                                                                    nil))
                                                                    Sskip)
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Sloop
                                                                    Sskip
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Sloop
                                                                    Sskip
                                                                    Sbreak)
                                                                    (Sreturn (Some (Etempvar _err_code__4 tulong)))))))
                                                                Sskip)))
                                                          Sbreak)
                                                        (Ssequence
                                                          (Sset _ip
                                                            (Ebinop Oadd
                                                              (Etempvar _ip (tptr tschar))
                                                              (Etempvar _neededInSize tulong)
                                                              (tptr tschar)))
                                                          Sbreak))
                                                      Sskip)
                                                    (Ssequence
                                                      (Sifthenelse (Ebinop Oeq
                                                                    (Etempvar _ip (tptr tschar))
                                                                    (Etempvar _iend (tptr tschar))
                                                                    tint)
                                                        (Ssequence
                                                          (Sset _someMoreWork
                                                            (Econst_int (Int.repr 0) tint))
                                                          Sbreak)
                                                        Sskip)
                                                      (Sassign
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                            (Tstruct _ZSTD_DCtx_s noattr))
                                                          _streamStage tint)
                                                        (Econst_int (Int.repr 3) tint)))))))).

Definition ds_case_load : statement :=
(Ssequence
                                              (Ssequence
                                                (Scall (Some _t'54)
                                                  (Evar _ZSTD_nextSrcSizeToDecompress 
                                                  (Tfunction
                                                    ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
                                                     nil) tulong cc_default))
                                                  ((Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
                                                   nil))
                                                (Sset _neededInSize__1
                                                  (Etempvar _t'54 tulong)))
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'104
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                        (Tstruct _ZSTD_DCtx_s noattr))
                                                      _inPos tulong))
                                                  (Sset _toLoad__1
                                                    (Ebinop Osub
                                                      (Etempvar _neededInSize__1 tulong)
                                                      (Etempvar _t'104 tulong)
                                                      tulong)))
                                                (Ssequence
                                                  (Ssequence
                                                    (Scall (Some _t'55)
                                                      (Evar _ZSTD_isSkipFrame 
                                                      (Tfunction
                                                        ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
                                                         nil) tint
                                                        cc_default))
                                                      ((Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
                                                       nil))
                                                    (Sset _isSkipFrame
                                                      (Etempvar _t'55 tint)))
                                                  (Ssequence
                                                    (Sifthenelse (Etempvar _isSkipFrame tint)
                                                      (Ssequence
                                                        (Sifthenelse 
                                                          (Ebinop Olt
                                                            (Etempvar _toLoad__1 tulong)
                                                            (Ecast
                                                              (Ebinop Osub
                                                                (Etempvar _iend (tptr tschar))
                                                                (Etempvar _ip (tptr tschar))
                                                                tlong)
                                                              tulong) tint)
                                                          (Sset _t'56
                                                            (Ecast
                                                              (Etempvar _toLoad__1 tulong)
                                                              tulong))
                                                          (Sset _t'56
                                                            (Ecast
                                                              (Ecast
                                                                (Ebinop Osub
                                                                  (Etempvar _iend (tptr tschar))
                                                                  (Etempvar _ip (tptr tschar))
                                                                  tlong)
                                                                tulong)
                                                              tulong)))
                                                        (Sset _loadedSize
                                                          (Etempvar _t'56 tulong)))
                                                      (Ssequence
                                                        (Sloop
                                                          (Ssequence
                                                            (Sset _t'102
                                                              (Efield
                                                                (Ederef
                                                                  (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                  (Tstruct _ZSTD_DCtx_s noattr))
                                                                _inBuffSize
                                                                tulong))
                                                            (Ssequence
                                                              (Sset _t'103
                                                                (Efield
                                                                  (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                  _inPos
                                                                  tulong))
                                                              (Sifthenelse 
                                                                (Ebinop Ogt
                                                                  (Etempvar _toLoad__1 tulong)
                                                                  (Ebinop Osub
                                                                    (Etempvar _t'102 tulong)
                                                                    (Etempvar _t'103 tulong)
                                                                    tulong)
                                                                  tint)
                                                                (Ssequence
                                                                  (Sloop
                                                                    Sskip
                                                                    Sbreak)
                                                                  (Ssequence
                                                                    (Sloop
                                                                    (Sifthenelse (Econst_int (Int.repr 0) tint)
                                                                    (Scall None
                                                                    (Evar __force_has_format_string 
                                                                    (Tfunction
                                                                    ((tptr tschar) ::
                                                                    nil)
                                                                    tvoid
                                                                    {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                                                                    ((Evar ___stringlit_zstd_66 (tarray tschar 20)) ::
                                                                    nil))
                                                                    Sskip)
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Sloop
                                                                    Sskip
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Sloop
                                                                    Sskip
                                                                    Sbreak)
                                                                    (Sreturn (Some 
                                                                    (Ecast
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 20) tint)
                                                                    tint)
                                                                    tulong)))))))
                                                                Sskip)))
                                                          Sbreak)
                                                        (Ssequence
                                                          (Ssequence
                                                            (Sset _t'100
                                                              (Efield
                                                                (Ederef
                                                                  (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                  (Tstruct _ZSTD_DCtx_s noattr))
                                                                _inBuff
                                                                (tptr tschar)))
                                                            (Ssequence
                                                              (Sset _t'101
                                                                (Efield
                                                                  (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                  _inPos
                                                                  tulong))
                                                              (Scall (Some _t'57)
                                                                (Evar _ZSTD_limitCopy 
                                                                (Tfunction
                                                                  ((tptr tvoid) ::
                                                                   tulong ::
                                                                   (tptr tvoid) ::
                                                                   tulong ::
                                                                   nil)
                                                                  tulong
                                                                  cc_default))
                                                                ((Ebinop Oadd
                                                                   (Etempvar _t'100 (tptr tschar))
                                                                   (Etempvar _t'101 tulong)
                                                                   (tptr tschar)) ::
                                                                 (Etempvar _toLoad__1 tulong) ::
                                                                 (Etempvar _ip (tptr tschar)) ::
                                                                 (Ecast
                                                                   (Ebinop Osub
                                                                    (Etempvar _iend (tptr tschar))
                                                                    (Etempvar _ip (tptr tschar))
                                                                    tlong)
                                                                   tulong) ::
                                                                 nil))))
                                                          (Sset _loadedSize
                                                            (Etempvar _t'57 tulong)))))
                                                    (Ssequence
                                                      (Sifthenelse (Ebinop One
                                                                    (Etempvar _loadedSize tulong)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                        (Ssequence
                                                          (Sset _ip
                                                            (Ebinop Oadd
                                                              (Etempvar _ip (tptr tschar))
                                                              (Etempvar _loadedSize tulong)
                                                              (tptr tschar)))
                                                          (Ssequence
                                                            (Sset _t'99
                                                              (Efield
                                                                (Ederef
                                                                  (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                  (Tstruct _ZSTD_DCtx_s noattr))
                                                                _inPos
                                                                tulong))
                                                            (Sassign
                                                              (Efield
                                                                (Ederef
                                                                  (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                  (Tstruct _ZSTD_DCtx_s noattr))
                                                                _inPos
                                                                tulong)
                                                              (Ebinop Oadd
                                                                (Etempvar _t'99 tulong)
                                                                (Etempvar _loadedSize tulong)
                                                                tulong))))
                                                        Sskip)
                                                      (Ssequence
                                                        (Sifthenelse 
                                                          (Ebinop Olt
                                                            (Etempvar _loadedSize tulong)
                                                            (Etempvar _toLoad__1 tulong)
                                                            tint)
                                                          (Ssequence
                                                            (Sset _someMoreWork
                                                              (Econst_int (Int.repr 0) tint))
                                                            Sbreak)
                                                          Sskip)
                                                        (Ssequence
                                                          (Sassign
                                                            (Efield
                                                              (Ederef
                                                                (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                (Tstruct _ZSTD_DCtx_s noattr))
                                                              _inPos tulong)
                                                            (Econst_int (Int.repr 0) tint))
                                                          (Ssequence
                                                            (Sloop
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Ssequence
                                                                    (Sset _t'98
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _inBuff
                                                                    (tptr tschar)))
                                                                    (Scall (Some _t'58)
                                                                    (Evar _ZSTD_decompressContinueStream 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
                                                                    (tptr (tptr tschar)) ::
                                                                    (tptr tschar) ::
                                                                    (tptr tvoid) ::
                                                                    tulong ::
                                                                    nil)
                                                                    tulong
                                                                    cc_default))
                                                                    ((Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
                                                                    (Eaddrof
                                                                    (Evar _op (tptr tschar))
                                                                    (tptr (tptr tschar))) ::
                                                                    (Etempvar _oend (tptr tschar)) ::
                                                                    (Etempvar _t'98 (tptr tschar)) ::
                                                                    (Etempvar _neededInSize__1 tulong) ::
                                                                    nil)))
                                                                  (Sset _err_code__5
                                                                    (Etempvar _t'58 tulong)))
                                                                (Ssequence
                                                                  (Scall (Some _t'59)
                                                                    (Evar _ERR_isError 
                                                                    (Tfunction
                                                                    (tulong ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                    ((Etempvar _err_code__5 tulong) ::
                                                                    nil))
                                                                  (Sifthenelse (Etempvar _t'59 tuint)
                                                                    (Ssequence
                                                                    (Sloop
                                                                    Sskip
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Sifthenelse (Econst_int (Int.repr 0) tint)
                                                                    (Scall None
                                                                    (Evar __force_has_format_string 
                                                                    (Tfunction
                                                                    ((tptr tschar) ::
                                                                    nil)
                                                                    tvoid
                                                                    {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                                                                    ((Evar ___stringlit_zstd_37 (tarray tschar 1)) ::
                                                                    nil))
                                                                    Sskip)
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Sloop
                                                                    Sskip
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Sloop
                                                                    Sskip
                                                                    Sbreak)
                                                                    (Sreturn (Some (Etempvar _err_code__5 tulong)))))))
                                                                    Sskip)))
                                                              Sbreak)
                                                            Sbreak)))))))).

Definition ds_case_flush : statement :=
(Ssequence
                                                (Ssequence
                                                  (Sset _t'96
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                        (Tstruct _ZSTD_DCtx_s noattr))
                                                      _outEnd tulong))
                                                  (Ssequence
                                                    (Sset _t'97
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                          (Tstruct _ZSTD_DCtx_s noattr))
                                                        _outStart tulong))
                                                    (Sset _toFlushSize
                                                      (Ebinop Osub
                                                        (Etempvar _t'96 tulong)
                                                        (Etempvar _t'97 tulong)
                                                        tulong))))
                                                (Ssequence
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sset _t'92
                                                        (Evar _op (tptr tschar)))
                                                      (Ssequence
                                                        (Sset _t'93
                                                          (Evar _op (tptr tschar)))
                                                        (Ssequence
                                                          (Sset _t'94
                                                            (Efield
                                                              (Ederef
                                                                (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                (Tstruct _ZSTD_DCtx_s noattr))
                                                              _outBuff
                                                              (tptr tschar)))
                                                          (Ssequence
                                                            (Sset _t'95
                                                              (Efield
                                                                (Ederef
                                                                  (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                  (Tstruct _ZSTD_DCtx_s noattr))
                                                                _outStart
                                                                tulong))
                                                            (Scall (Some _t'60)
                                                              (Evar _ZSTD_limitCopy 
                                                              (Tfunction
                                                                ((tptr tvoid) ::
                                                                 tulong ::
                                                                 (tptr tvoid) ::
                                                                 tulong ::
                                                                 nil) tulong
                                                                cc_default))
                                                              ((Etempvar _t'92 (tptr tschar)) ::
                                                               (Ecast
                                                                 (Ebinop Osub
                                                                   (Etempvar _oend (tptr tschar))
                                                                   (Etempvar _t'93 (tptr tschar))
                                                                   tlong)
                                                                 tulong) ::
                                                               (Ebinop Oadd
                                                                 (Etempvar _t'94 (tptr tschar))
                                                                 (Etempvar _t'95 tulong)
                                                                 (tptr tschar)) ::
                                                               (Etempvar _toFlushSize tulong) ::
                                                               nil))))))
                                                    (Sset _flushedSize
                                                      (Etempvar _t'60 tulong)))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sset _t'89
                                                          (Evar _op (tptr tschar)))
                                                        (Sifthenelse (Etempvar _t'89 (tptr tschar))
                                                          (Ssequence
                                                            (Sset _t'91
                                                              (Evar _op (tptr tschar)))
                                                            (Sset _t'61
                                                              (Ecast
                                                                (Ebinop Oadd
                                                                  (Etempvar _t'91 (tptr tschar))
                                                                  (Etempvar _flushedSize tulong)
                                                                  (tptr tschar))
                                                                (tptr tschar))))
                                                          (Ssequence
                                                            (Sset _t'90
                                                              (Evar _op (tptr tschar)))
                                                            (Sset _t'61
                                                              (Ecast
                                                                (Etempvar _t'90 (tptr tschar))
                                                                (tptr tschar))))))
                                                      (Sassign
                                                        (Evar _op (tptr tschar))
                                                        (Etempvar _t'61 (tptr tschar))))
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sset _t'88
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                              (Tstruct _ZSTD_DCtx_s noattr))
                                                            _outStart tulong))
                                                        (Sassign
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                              (Tstruct _ZSTD_DCtx_s noattr))
                                                            _outStart tulong)
                                                          (Ebinop Oadd
                                                            (Etempvar _t'88 tulong)
                                                            (Etempvar _flushedSize tulong)
                                                            tulong)))
                                                      (Ssequence
                                                        (Sifthenelse 
                                                          (Ebinop Oeq
                                                            (Etempvar _flushedSize tulong)
                                                            (Etempvar _toFlushSize tulong)
                                                            tint)
                                                          (Ssequence
                                                            (Sassign
                                                              (Efield
                                                                (Ederef
                                                                  (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                  (Tstruct _ZSTD_DCtx_s noattr))
                                                                _streamStage
                                                                tint)
                                                              (Econst_int (Int.repr 2) tint))
                                                            (Ssequence
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Sset _t'83
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _outBuffSize
                                                                    tulong))
                                                                  (Ssequence
                                                                    (Sset _t'84
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _fParams
                                                                    (Tstruct ___gp_ZSTD_FrameHeader noattr))
                                                                    _frameContentSize
                                                                    tulong))
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _t'83 tulong)
                                                                    (Etempvar _t'84 tulong)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _t'85
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _outStart
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _t'86
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _fParams
                                                                    (Tstruct ___gp_ZSTD_FrameHeader noattr))
                                                                    _blockSizeMax
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'87
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _outBuffSize
                                                                    tulong))
                                                                    (Sset _t'63
                                                                    (Ecast
                                                                    (Ebinop Ogt
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'85 tulong)
                                                                    (Etempvar _t'86 tuint)
                                                                    tulong)
                                                                    (Etempvar _t'87 tulong)
                                                                    tint)
                                                                    tbool)))))
                                                                    (Sset _t'63
                                                                    (Econst_int (Int.repr 0) tint)))))
                                                                (Sifthenelse (Etempvar _t'63 tint)
                                                                  (Ssequence
                                                                    (Sloop
                                                                    Sskip
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'62
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tulong))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _outEnd
                                                                    tulong)
                                                                    (Etempvar _t'62 tulong)))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _outStart
                                                                    tulong)
                                                                    (Etempvar _t'62 tulong))))
                                                                  Sskip))
                                                              Sbreak))
                                                          Sskip)
                                                        (Ssequence
                                                          (Sset _someMoreWork
                                                            (Econst_int (Int.repr 0) tint))
                                                          Sbreak)))))).

Definition ds_case_default : statement :=
(Sloop
                                                  (Ssequence
                                                    (Sloop Sskip Sbreak)
                                                    (Ssequence
                                                      (Sloop
                                                        (Sifthenelse (Econst_int (Int.repr 0) tint)
                                                          (Scall None
                                                            (Evar __force_has_format_string 
                                                            (Tfunction
                                                              ((tptr tschar) ::
                                                               nil) tvoid
                                                              {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                                                            ((Evar ___stringlit_zstd_56 (tarray tschar 20)) ::
                                                             nil))
                                                          Sskip)
                                                        Sbreak)
                                                      (Ssequence
                                                        (Sloop Sskip Sbreak)
                                                        (Ssequence
                                                          (Sloop
                                                            Sskip
                                                            Sbreak)
                                                          (Sreturn (Some 
                                                            (Ecast
                                                              (Eunop Oneg
                                                                (Econst_int (Int.repr 1) tint)
                                                                tint) tulong)))))))
                                                  Sbreak).

Definition ds_switch_ls : labeled_statements :=
  (LScons (Some 0) ds_case_init (LScons (Some 1) ds_case_loadHeader (LScons (Some 2) ds_case_read (LScons (Some 3) ds_case_load (LScons (Some 4) ds_case_flush (LScons None ds_case_default LSnil)))))).

Definition ds_loop : statement :=
(Swhile
                                (Etempvar _someMoreWork tuint)
                                (Ssequence
                                  (Sset _t'82
                                    (Efield
                                      (Ederef
                                        (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                        (Tstruct _ZSTD_DCtx_s noattr))
                                      _streamStage tint))
                                  (Sswitch (Etempvar _t'82 tint)
                                    ds_switch_ls))).

Definition ds_epilogue : statement :=
(Ssequence
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _input (tptr (Tstruct _ZSTD_inBuffer_s noattr)))
                                      (Tstruct _ZSTD_inBuffer_s noattr)) _pos
                                    tulong)
                                  (Ecast
                                    (Ebinop Osub (Etempvar _ip (tptr tschar))
                                      (Etempvar _src (tptr tschar)) tlong)
                                    tulong))
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'81 (Evar _op (tptr tschar)))
                                    (Sassign
                                      (Efield
                                        (Ederef
                                          (Etempvar _output (tptr (Tstruct _ZSTD_outBuffer_s noattr)))
                                          (Tstruct _ZSTD_outBuffer_s noattr))
                                        _pos tulong)
                                      (Ecast
                                        (Ebinop Osub
                                          (Etempvar _t'81 (tptr tschar))
                                          (Etempvar _dst (tptr tschar))
                                          tlong) tulong)))
                                  (Ssequence
                                    (Scall None
                                      (Evar _ZSTD_outBuffer_copy (Tfunction
                                                                   ((tptr (Tstruct _ZSTD_outBuffer_s noattr)) ::
                                                                    (tptr (Tstruct _ZSTD_outBuffer_s noattr)) ::
                                                                    nil)
                                                                   tvoid
                                                                   cc_default))
                                      ((Eaddrof
                                         (Efield
                                           (Ederef
                                             (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                             (Tstruct _ZSTD_DCtx_s noattr))
                                           _expectedOutBuffer
                                           (Tstruct _ZSTD_outBuffer_s noattr))
                                         (tptr (Tstruct _ZSTD_outBuffer_s noattr))) ::
                                       (Etempvar _output (tptr (Tstruct _ZSTD_outBuffer_s noattr))) ::
                                       nil))
                                    (Ssequence
                                      (Ssequence
                                        (Sifthenelse (Ebinop Oeq
                                                       (Etempvar _ip (tptr tschar))
                                                       (Etempvar _istart (tptr tschar))
                                                       tint)
                                          (Ssequence
                                            (Sset _t'80
                                              (Evar _op (tptr tschar)))
                                            (Sset _t'64
                                              (Ecast
                                                (Ebinop Oeq
                                                  (Etempvar _t'80 (tptr tschar))
                                                  (Etempvar _ostart (tptr tschar))
                                                  tint) tbool)))
                                          (Sset _t'64
                                            (Econst_int (Int.repr 0) tint)))
                                        (Sifthenelse (Etempvar _t'64 tint)
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'79
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                  _noForwardProgress tint))
                                              (Sassign
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                  _noForwardProgress tint)
                                                (Ebinop Oadd
                                                  (Etempvar _t'79 tint)
                                                  (Econst_int (Int.repr 1) tint)
                                                  tint)))
                                            (Ssequence
                                              (Sset _t'77
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                  _noForwardProgress tint))
                                              (Sifthenelse (Ebinop Oge
                                                             (Etempvar _t'77 tint)
                                                             (Econst_int (Int.repr 16) tint)
                                                             tint)
                                                (Ssequence
                                                  (Sloop
                                                    (Ssequence
                                                      (Sset _t'78
                                                        (Evar _op (tptr tschar)))
                                                      (Sifthenelse (Ebinop Oeq
                                                                    (Etempvar _t'78 (tptr tschar))
                                                                    (Etempvar _oend (tptr tschar))
                                                                    tint)
                                                        (Ssequence
                                                          (Sloop
                                                            Sskip
                                                            Sbreak)
                                                          (Ssequence
                                                            (Sloop
                                                              (Sifthenelse (Econst_int (Int.repr 0) tint)
                                                                (Scall None
                                                                  (Evar __force_has_format_string 
                                                                  (Tfunction
                                                                    ((tptr tschar) ::
                                                                    nil)
                                                                    tvoid
                                                                    {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                                                                  ((Evar ___stringlit_zstd_37 (tarray tschar 1)) ::
                                                                   nil))
                                                                Sskip)
                                                              Sbreak)
                                                            (Ssequence
                                                              (Sloop
                                                                Sskip
                                                                Sbreak)
                                                              (Ssequence
                                                                (Sloop
                                                                  Sskip
                                                                  Sbreak)
                                                                (Sreturn (Some 
                                                                  (Ecast
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 80) tint)
                                                                    tint)
                                                                    tulong)))))))
                                                        Sskip))
                                                    Sbreak)
                                                  (Sloop
                                                    (Sifthenelse (Ebinop Oeq
                                                                   (Etempvar _ip (tptr tschar))
                                                                   (Etempvar _iend (tptr tschar))
                                                                   tint)
                                                      (Ssequence
                                                        (Sloop Sskip Sbreak)
                                                        (Ssequence
                                                          (Sloop
                                                            (Sifthenelse (Econst_int (Int.repr 0) tint)
                                                              (Scall None
                                                                (Evar __force_has_format_string 
                                                                (Tfunction
                                                                  ((tptr tschar) ::
                                                                   nil) tvoid
                                                                  {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                                                                ((Evar ___stringlit_zstd_37 (tarray tschar 1)) ::
                                                                 nil))
                                                              Sskip)
                                                            Sbreak)
                                                          (Ssequence
                                                            (Sloop
                                                              Sskip
                                                              Sbreak)
                                                            (Ssequence
                                                              (Sloop
                                                                Sskip
                                                                Sbreak)
                                                              (Sreturn (Some 
                                                                (Ecast
                                                                  (Eunop Oneg
                                                                    (Econst_int (Int.repr 82) tint)
                                                                    tint)
                                                                  tulong)))))))
                                                      Sskip)
                                                    Sbreak))
                                                Sskip)))
                                          (Sassign
                                            (Efield
                                              (Ederef
                                                (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                (Tstruct _ZSTD_DCtx_s noattr))
                                              _noForwardProgress tint)
                                            (Econst_int (Int.repr 0) tint))))
                                      (Ssequence
                                        (Ssequence
                                          (Scall (Some _t'65)
                                            (Evar _ZSTD_nextSrcSizeToDecompress 
                                            (Tfunction
                                              ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
                                               nil) tulong cc_default))
                                            ((Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
                                             nil))
                                          (Sset _nextSrcSizeHint
                                            (Etempvar _t'65 tulong)))
                                        (Ssequence
                                          (Sifthenelse (Eunop Onotbool
                                                         (Etempvar _nextSrcSizeHint tulong)
                                                         tint)
                                            (Ssequence
                                              (Ssequence
                                                (Sset _t'71
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                      (Tstruct _ZSTD_DCtx_s noattr))
                                                    _outEnd tulong))
                                                (Ssequence
                                                  (Sset _t'72
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                        (Tstruct _ZSTD_DCtx_s noattr))
                                                      _outStart tulong))
                                                  (Sifthenelse (Ebinop Oeq
                                                                 (Etempvar _t'71 tulong)
                                                                 (Etempvar _t'72 tulong)
                                                                 tint)
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sset _t'73
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                              (Tstruct _ZSTD_DCtx_s noattr))
                                                            _hostageByte
                                                            tuint))
                                                        (Sifthenelse (Etempvar _t'73 tuint)
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _t'75
                                                                (Efield
                                                                  (Ederef
                                                                    (Etempvar _input (tptr (Tstruct _ZSTD_inBuffer_s noattr)))
                                                                    (Tstruct _ZSTD_inBuffer_s noattr))
                                                                  _pos
                                                                  tulong))
                                                              (Ssequence
                                                                (Sset _t'76
                                                                  (Efield
                                                                    (Ederef
                                                                    (Etempvar _input (tptr (Tstruct _ZSTD_inBuffer_s noattr)))
                                                                    (Tstruct _ZSTD_inBuffer_s noattr))
                                                                    _size
                                                                    tulong))
                                                                (Sifthenelse 
                                                                  (Ebinop Oge
                                                                    (Etempvar _t'75 tulong)
                                                                    (Etempvar _t'76 tulong)
                                                                    tint)
                                                                  (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _streamStage
                                                                    tint)
                                                                    (Econst_int (Int.repr 2) tint))
                                                                    (Sreturn (Some (Econst_int (Int.repr 1) tint))))
                                                                  Sskip)))
                                                            (Ssequence
                                                              (Sset _t'74
                                                                (Efield
                                                                  (Ederef
                                                                    (Etempvar _input (tptr (Tstruct _ZSTD_inBuffer_s noattr)))
                                                                    (Tstruct _ZSTD_inBuffer_s noattr))
                                                                  _pos
                                                                  tulong))
                                                              (Sassign
                                                                (Efield
                                                                  (Ederef
                                                                    (Etempvar _input (tptr (Tstruct _ZSTD_inBuffer_s noattr)))
                                                                    (Tstruct _ZSTD_inBuffer_s noattr))
                                                                  _pos
                                                                  tulong)
                                                                (Ebinop Oadd
                                                                  (Etempvar _t'74 tulong)
                                                                  (Econst_int (Int.repr 1) tint)
                                                                  tulong))))
                                                          Sskip))
                                                      (Sreturn (Some (Econst_int (Int.repr 0) tint))))
                                                    Sskip)))
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'69
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                        (Tstruct _ZSTD_DCtx_s noattr))
                                                      _hostageByte tuint))
                                                  (Sifthenelse (Eunop Onotbool
                                                                 (Etempvar _t'69 tuint)
                                                                 tint)
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sset _t'70
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _input (tptr (Tstruct _ZSTD_inBuffer_s noattr)))
                                                              (Tstruct _ZSTD_inBuffer_s noattr))
                                                            _pos tulong))
                                                        (Sassign
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _input (tptr (Tstruct _ZSTD_inBuffer_s noattr)))
                                                              (Tstruct _ZSTD_inBuffer_s noattr))
                                                            _pos tulong)
                                                          (Ebinop Osub
                                                            (Etempvar _t'70 tulong)
                                                            (Econst_int (Int.repr 1) tint)
                                                            tulong)))
                                                      (Sassign
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                            (Tstruct _ZSTD_DCtx_s noattr))
                                                          _hostageByte tuint)
                                                        (Econst_int (Int.repr 1) tint)))
                                                    Sskip))
                                                (Sreturn (Some (Econst_int (Int.repr 1) tint)))))
                                            Sskip)
                                          (Ssequence
                                            (Ssequence
                                              (Scall (Some _t'66)
                                                (Evar _ZSTD_nextInputType 
                                                (Tfunction
                                                  ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
                                                   nil) tint cc_default))
                                                ((Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
                                                 nil))
                                              (Ssequence
                                                (Sset _t'68
                                                  (Evar _ZSTD_blockHeaderSize tulong))
                                                (Sset _nextSrcSizeHint
                                                  (Ebinop Oadd
                                                    (Etempvar _nextSrcSizeHint tulong)
                                                    (Ebinop Omul
                                                      (Etempvar _t'68 tulong)
                                                      (Ebinop Oeq
                                                        (Etempvar _t'66 tint)
                                                        (Econst_int (Int.repr 2) tint)
                                                        tint) tulong) tulong))))
                                            (Ssequence
                                              (Ssequence
                                                (Sset _t'67
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                      (Tstruct _ZSTD_DCtx_s noattr))
                                                    _inPos tulong))
                                                (Sset _nextSrcSizeHint
                                                  (Ebinop Osub
                                                    (Etempvar _nextSrcSizeHint tulong)
                                                    (Etempvar _t'67 tulong)
                                                    tulong)))
                                              (Sreturn (Some (Etempvar _nextSrcSizeHint tulong))))))))))).

Definition ds_prologue (REST: statement) : statement :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'185
        (Efield
          (Ederef (Etempvar _input (tptr (Tstruct _ZSTD_inBuffer_s noattr)))
            (Tstruct _ZSTD_inBuffer_s noattr)) _src (tptr tvoid)))
      (Sifthenelse (Ebinop One (Etempvar _t'185 (tptr tvoid))
                     (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                     tint)
        (Ssequence
          (Sset _t'186
            (Efield
              (Ederef
                (Etempvar _input (tptr (Tstruct _ZSTD_inBuffer_s noattr)))
                (Tstruct _ZSTD_inBuffer_s noattr)) _src (tptr tvoid)))
          (Sset _t'1
            (Ecast (Ecast (Etempvar _t'186 (tptr tvoid)) (tptr tschar))
              (tptr tschar))))
        (Sset _t'1
          (Ecast
            (Ecast (Evar _ZSTD_emptyBuffer (tarray tuchar 1)) (tptr tschar))
            (tptr tschar)))))
    (Sset _src (Etempvar _t'1 (tptr tschar))))
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'183
          (Efield
            (Ederef
              (Etempvar _input (tptr (Tstruct _ZSTD_inBuffer_s noattr)))
              (Tstruct _ZSTD_inBuffer_s noattr)) _pos tulong))
        (Sifthenelse (Ebinop One (Etempvar _t'183 tulong)
                       (Econst_int (Int.repr 0) tint) tint)
          (Ssequence
            (Sset _t'184
              (Efield
                (Ederef
                  (Etempvar _input (tptr (Tstruct _ZSTD_inBuffer_s noattr)))
                  (Tstruct _ZSTD_inBuffer_s noattr)) _pos tulong))
            (Sset _t'2
              (Ecast
                (Ebinop Oadd (Etempvar _src (tptr tschar))
                  (Etempvar _t'184 tulong) (tptr tschar)) (tptr tschar))))
          (Sset _t'2 (Ecast (Etempvar _src (tptr tschar)) (tptr tschar)))))
      (Sset _istart (Etempvar _t'2 (tptr tschar))))
    (Ssequence
      (Ssequence
        (Ssequence
          (Sset _t'181
            (Efield
              (Ederef
                (Etempvar _input (tptr (Tstruct _ZSTD_inBuffer_s noattr)))
                (Tstruct _ZSTD_inBuffer_s noattr)) _size tulong))
          (Sifthenelse (Ebinop One (Etempvar _t'181 tulong)
                         (Econst_int (Int.repr 0) tint) tint)
            (Ssequence
              (Sset _t'182
                (Efield
                  (Ederef
                    (Etempvar _input (tptr (Tstruct _ZSTD_inBuffer_s noattr)))
                    (Tstruct _ZSTD_inBuffer_s noattr)) _size tulong))
              (Sset _t'3
                (Ecast
                  (Ebinop Oadd (Etempvar _src (tptr tschar))
                    (Etempvar _t'182 tulong) (tptr tschar)) (tptr tschar))))
            (Sset _t'3 (Ecast (Etempvar _src (tptr tschar)) (tptr tschar)))))
        (Sset _iend (Etempvar _t'3 (tptr tschar))))
      (Ssequence
        (Sset _ip (Etempvar _istart (tptr tschar)))
        (Ssequence
          (Ssequence
            (Ssequence
              (Sset _t'179
                (Efield
                  (Ederef
                    (Etempvar _output (tptr (Tstruct _ZSTD_outBuffer_s noattr)))
                    (Tstruct _ZSTD_outBuffer_s noattr)) _dst (tptr tvoid)))
              (Sifthenelse (Ebinop One (Etempvar _t'179 (tptr tvoid))
                             (Ecast (Econst_int (Int.repr 0) tint)
                               (tptr tvoid)) tint)
                (Ssequence
                  (Sset _t'180
                    (Efield
                      (Ederef
                        (Etempvar _output (tptr (Tstruct _ZSTD_outBuffer_s noattr)))
                        (Tstruct _ZSTD_outBuffer_s noattr)) _dst
                      (tptr tvoid)))
                  (Sset _t'4
                    (Ecast
                      (Ecast (Etempvar _t'180 (tptr tvoid)) (tptr tschar))
                      (tptr tschar))))
                (Sset _t'4
                  (Ecast
                    (Ecast (Evar _ZSTD_emptyBuffer (tarray tuchar 1))
                      (tptr tschar)) (tptr tschar)))))
            (Sset _dst (Etempvar _t'4 (tptr tschar))))
          (Ssequence
            (Ssequence
              (Ssequence
                (Sset _t'177
                  (Efield
                    (Ederef
                      (Etempvar _output (tptr (Tstruct _ZSTD_outBuffer_s noattr)))
                      (Tstruct _ZSTD_outBuffer_s noattr)) _pos tulong))
                (Sifthenelse (Ebinop One (Etempvar _t'177 tulong)
                               (Econst_int (Int.repr 0) tint) tint)
                  (Ssequence
                    (Sset _t'178
                      (Efield
                        (Ederef
                          (Etempvar _output (tptr (Tstruct _ZSTD_outBuffer_s noattr)))
                          (Tstruct _ZSTD_outBuffer_s noattr)) _pos tulong))
                    (Sset _t'5
                      (Ecast
                        (Ebinop Oadd (Etempvar _dst (tptr tschar))
                          (Etempvar _t'178 tulong) (tptr tschar))
                        (tptr tschar))))
                  (Sset _t'5
                    (Ecast (Etempvar _dst (tptr tschar)) (tptr tschar)))))
              (Sset _ostart (Etempvar _t'5 (tptr tschar))))
            (Ssequence
              (Ssequence
                (Ssequence
                  (Sset _t'175
                    (Efield
                      (Ederef
                        (Etempvar _output (tptr (Tstruct _ZSTD_outBuffer_s noattr)))
                        (Tstruct _ZSTD_outBuffer_s noattr)) _size tulong))
                  (Sifthenelse (Ebinop One (Etempvar _t'175 tulong)
                                 (Econst_int (Int.repr 0) tint) tint)
                    (Ssequence
                      (Sset _t'176
                        (Efield
                          (Ederef
                            (Etempvar _output (tptr (Tstruct _ZSTD_outBuffer_s noattr)))
                            (Tstruct _ZSTD_outBuffer_s noattr)) _size tulong))
                      (Sset _t'6
                        (Ecast
                          (Ebinop Oadd (Etempvar _dst (tptr tschar))
                            (Etempvar _t'176 tulong) (tptr tschar))
                          (tptr tschar))))
                    (Sset _t'6
                      (Ecast (Etempvar _dst (tptr tschar)) (tptr tschar)))))
                (Sset _oend (Etempvar _t'6 (tptr tschar))))
              (Ssequence
                (Sassign (Evar _op (tptr tschar))
                  (Etempvar _ostart (tptr tschar)))
                (Ssequence
                  (Sset _someMoreWork (Econst_int (Int.repr 1) tint))
                  (Ssequence
                    (Sloop Sskip Sbreak)
                    (Ssequence
                      (Sloop
                        (Ssequence
                          (Sset _t'171
                            (Efield
                              (Ederef
                                (Etempvar _input (tptr (Tstruct _ZSTD_inBuffer_s noattr)))
                                (Tstruct _ZSTD_inBuffer_s noattr)) _pos
                              tulong))
                          (Ssequence
                            (Sset _t'172
                              (Efield
                                (Ederef
                                  (Etempvar _input (tptr (Tstruct _ZSTD_inBuffer_s noattr)))
                                  (Tstruct _ZSTD_inBuffer_s noattr)) _size
                                tulong))
                            (Sifthenelse (Ebinop Ogt (Etempvar _t'171 tulong)
                                           (Etempvar _t'172 tulong) tint)
                              (Ssequence
                                (Sloop Sskip Sbreak)
                                (Ssequence
                                  (Sloop
                                    (Sifthenelse (Econst_int (Int.repr 0) tint)
                                      (Ssequence
                                        (Sset _t'173
                                          (Efield
                                            (Ederef
                                              (Etempvar _input (tptr (Tstruct _ZSTD_inBuffer_s noattr)))
                                              (Tstruct _ZSTD_inBuffer_s noattr))
                                            _pos tulong))
                                        (Ssequence
                                          (Sset _t'174
                                            (Efield
                                              (Ederef
                                                (Etempvar _input (tptr (Tstruct _ZSTD_inBuffer_s noattr)))
                                                (Tstruct _ZSTD_inBuffer_s noattr))
                                              _size tulong))
                                          (Scall None
                                            (Evar __force_has_format_string 
                                            (Tfunction ((tptr tschar) :: nil)
                                              tvoid
                                              {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                                            ((Evar ___stringlit_zstd_64 (tarray tschar 37)) ::
                                             (Ecast (Etempvar _t'173 tulong)
                                               tuint) ::
                                             (Ecast (Etempvar _t'174 tulong)
                                               tuint) :: nil))))
                                      Sskip)
                                    Sbreak)
                                  (Ssequence
                                    (Sloop Sskip Sbreak)
                                    (Ssequence
                                      (Sloop Sskip Sbreak)
                                      (Sreturn (Some (Ecast
                                                       (Eunop Oneg
                                                         (Econst_int (Int.repr 72) tint)
                                                         tint) tulong)))))))
                              Sskip)))
                        Sbreak)
                      (Ssequence
                        (Sloop
                          (Ssequence
                            (Sset _t'167
                              (Efield
                                (Ederef
                                  (Etempvar _output (tptr (Tstruct _ZSTD_outBuffer_s noattr)))
                                  (Tstruct _ZSTD_outBuffer_s noattr)) _pos
                                tulong))
                            (Ssequence
                              (Sset _t'168
                                (Efield
                                  (Ederef
                                    (Etempvar _output (tptr (Tstruct _ZSTD_outBuffer_s noattr)))
                                    (Tstruct _ZSTD_outBuffer_s noattr)) _size
                                  tulong))
                              (Sifthenelse (Ebinop Ogt
                                             (Etempvar _t'167 tulong)
                                             (Etempvar _t'168 tulong) tint)
                                (Ssequence
                                  (Sloop Sskip Sbreak)
                                  (Ssequence
                                    (Sloop
                                      (Sifthenelse (Econst_int (Int.repr 0) tint)
                                        (Ssequence
                                          (Sset _t'169
                                            (Efield
                                              (Ederef
                                                (Etempvar _output (tptr (Tstruct _ZSTD_outBuffer_s noattr)))
                                                (Tstruct _ZSTD_outBuffer_s noattr))
                                              _pos tulong))
                                          (Ssequence
                                            (Sset _t'170
                                              (Efield
                                                (Ederef
                                                  (Etempvar _output (tptr (Tstruct _ZSTD_outBuffer_s noattr)))
                                                  (Tstruct _ZSTD_outBuffer_s noattr))
                                                _size tulong))
                                            (Scall None
                                              (Evar __force_has_format_string 
                                              (Tfunction
                                                ((tptr tschar) :: nil) tvoid
                                                {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                                              ((Evar ___stringlit_zstd_65 (tarray tschar 38)) ::
                                               (Ecast
                                                 (Etempvar _t'169 tulong)
                                                 tuint) ::
                                               (Ecast
                                                 (Etempvar _t'170 tulong)
                                                 tuint) :: nil))))
                                        Sskip)
                                      Sbreak)
                                    (Ssequence
                                      (Sloop Sskip Sbreak)
                                      (Ssequence
                                        (Sloop Sskip Sbreak)
                                        (Sreturn (Some (Ecast
                                                         (Eunop Oneg
                                                           (Econst_int (Int.repr 70) tint)
                                                           tint) tulong)))))))
                                Sskip)))
                          Sbreak)
                        (Ssequence
                          (Sloop Sskip Sbreak)
                          (Ssequence
                            (Sloop
                              (Ssequence
                                (Ssequence
                                  (Scall (Some _t'7)
                                    (Evar _ZSTD_checkOutBuffer (Tfunction
                                                                 ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
                                                                  (tptr (Tstruct _ZSTD_outBuffer_s noattr)) ::
                                                                  nil) tulong
                                                                 cc_default))
                                    ((Etempvar _zds (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
                                     (Etempvar _output (tptr (Tstruct _ZSTD_outBuffer_s noattr))) ::
                                     nil))
                                  (Sset _err_code (Etempvar _t'7 tulong)))
                                (Ssequence
                                  (Scall (Some _t'8)
                                    (Evar _ERR_isError (Tfunction
                                                         (tulong :: nil)
                                                         tuint cc_default))
                                    ((Etempvar _err_code tulong) :: nil))
                                  (Sifthenelse (Etempvar _t'8 tuint)
                                    (Ssequence
                                      (Sloop Sskip Sbreak)
                                      (Ssequence
                                        (Sloop
                                          (Sifthenelse (Econst_int (Int.repr 0) tint)
                                            (Scall None
                                              (Evar __force_has_format_string 
                                              (Tfunction
                                                ((tptr tschar) :: nil) tvoid
                                                {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                                              ((Evar ___stringlit_zstd_37 (tarray tschar 1)) ::
                                               nil))
                                            Sskip)
                                          Sbreak)
                                        (Ssequence
                                          (Sloop Sskip Sbreak)
                                          (Ssequence
                                            (Sloop Sskip Sbreak)
                                            (Sreturn (Some (Etempvar _err_code tulong)))))))
                                    Sskip)))
                              Sbreak)
                            REST)))))))))))))).

Lemma ds_body_eq : fn_body f_ZSTD_decompressStream = ds_prologue (Ssequence ds_loop ds_epilogue).
Proof.
  reflexivity.
Qed.
