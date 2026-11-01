(* GENERATED from src/zstd/code.v (f_ZSTD_decompressSequencesLong_body cut in pieces) by a script that is
   not part of this repository; do not edit.  lg_body_eq: the body is the composition of the pieces. *)
From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Require Import Zstd.zstd.code.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Definition lg_epi : statement :=
(Ssequence
                    (Ssequence
                      (Sset _t'32
                        (Efield
                          (Ederef
                            (Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                            (Tstruct _ZSTD_DCtx_s noattr)) _litBufferLocation
                          tint))
                      (Sifthenelse (Ebinop Oeq (Etempvar _t'32 tint)
                                     (Econst_int (Int.repr 2) tint) tint)
                        (Ssequence
                          (Ssequence
                            (Sset _t'34 (Evar _litPtr (tptr tuchar)))
                            (Sset _lastLLSize
                              (Ecast
                                (Ebinop Osub
                                  (Etempvar _litBufferEnd (tptr tuchar))
                                  (Etempvar _t'34 (tptr tuchar)) tlong)
                                tulong)))
                          (Ssequence
                            (Sloop
                              (Sifthenelse (Ebinop Ogt
                                             (Etempvar _lastLLSize tulong)
                                             (Ecast
                                               (Ebinop Osub
                                                 (Etempvar _oend (tptr tuchar))
                                                 (Etempvar _op (tptr tuchar))
                                                 tlong) tulong) tint)
                                (Ssequence
                                  (Sloop Sskip Sbreak)
                                  (Ssequence
                                    (Sloop
                                      (Sifthenelse (Econst_int (Int.repr 0) tint)
                                        (Scall None
                                          (Evar __force_has_format_string 
                                          (Tfunction ((tptr tschar) :: nil)
                                            tvoid
                                            {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                                          ((Evar ___stringlit_zstd_37 (tarray tschar 1)) ::
                                           nil))
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
                                Sskip)
                              Sbreak)
                            (Ssequence
                              (Sifthenelse (Ebinop One
                                             (Etempvar _op (tptr tuchar))
                                             (Ecast
                                               (Econst_int (Int.repr 0) tint)
                                               (tptr tvoid)) tint)
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'33 (Evar _litPtr (tptr tuchar)))
                                    (Scall None
                                      (Evar _memmove (Tfunction
                                                       ((tptr tvoid) ::
                                                        (tptr tvoid) ::
                                                        tulong :: nil)
                                                       (tptr tvoid)
                                                       cc_default))
                                      ((Etempvar _op (tptr tuchar)) ::
                                       (Etempvar _t'33 (tptr tuchar)) ::
                                       (Etempvar _lastLLSize tulong) :: nil)))
                                  (Sset _op
                                    (Ebinop Oadd (Etempvar _op (tptr tuchar))
                                      (Etempvar _lastLLSize tulong)
                                      (tptr tuchar))))
                                Sskip)
                              (Ssequence
                                (Sassign (Evar _litPtr (tptr tuchar))
                                  (Efield
                                    (Ederef
                                      (Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                      (Tstruct _ZSTD_DCtx_s noattr))
                                    _litExtraBuffer (tarray tuchar 65568)))
                                (Ssequence
                                  (Ssequence
                                    (Sifthenelse (Ebinop Olt
                                                   (Ebinop Oshl
                                                     (Econst_int (Int.repr 1) tint)
                                                     (Econst_int (Int.repr 16) tint)
                                                     tint)
                                                   (Ebinop Oshl
                                                     (Econst_int (Int.repr 128) tint)
                                                     (Econst_int (Int.repr 10) tint)
                                                     tint) tint)
                                      (Sset _t'28
                                        (Ecast
                                          (Ebinop Oshl
                                            (Econst_int (Int.repr 1) tint)
                                            (Econst_int (Int.repr 16) tint)
                                            tint) tint))
                                      (Sset _t'28
                                        (Ecast
                                          (Ebinop Oshl
                                            (Econst_int (Int.repr 128) tint)
                                            (Econst_int (Int.repr 10) tint)
                                            tint) tint)))
                                    (Sifthenelse (Ebinop Ogt
                                                   (Econst_int (Int.repr 64) tint)
                                                   (Etempvar _t'28 tint)
                                                   tint)
                                      (Sset _t'29
                                        (Ecast
                                          (Econst_int (Int.repr 64) tint)
                                          tint))
                                      (Sifthenelse (Ebinop Olt
                                                     (Ebinop Oshl
                                                       (Econst_int (Int.repr 1) tint)
                                                       (Econst_int (Int.repr 16) tint)
                                                       tint)
                                                     (Ebinop Oshl
                                                       (Econst_int (Int.repr 128) tint)
                                                       (Econst_int (Int.repr 10) tint)
                                                       tint) tint)
                                        (Ssequence
                                          (Sset _t'29
                                            (Ecast
                                              (Ebinop Oshl
                                                (Econst_int (Int.repr 1) tint)
                                                (Econst_int (Int.repr 16) tint)
                                                tint) tint))
                                          (Sset _t'29
                                            (Ecast (Etempvar _t'29 tint)
                                              tint)))
                                        (Ssequence
                                          (Sset _t'29
                                            (Ecast
                                              (Ebinop Oshl
                                                (Econst_int (Int.repr 128) tint)
                                                (Econst_int (Int.repr 10) tint)
                                                tint) tint))
                                          (Sset _t'29
                                            (Ecast (Etempvar _t'29 tint)
                                              tint))))))
                                  (Sset _litBufferEnd
                                    (Ebinop Oadd
                                      (Efield
                                        (Ederef
                                          (Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                          (Tstruct _ZSTD_DCtx_s noattr))
                                        _litExtraBuffer
                                        (tarray tuchar 65568))
                                      (Etempvar _t'29 tint) (tptr tuchar))))))))
                        Sskip))
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Sset _t'31 (Evar _litPtr (tptr tuchar)))
                          (Sset _lastLLSize__1
                            (Ecast
                              (Ebinop Osub
                                (Etempvar _litBufferEnd (tptr tuchar))
                                (Etempvar _t'31 (tptr tuchar)) tlong) tulong)))
                        (Ssequence
                          (Sloop
                            (Sifthenelse (Ebinop Ogt
                                           (Etempvar _lastLLSize__1 tulong)
                                           (Ecast
                                             (Ebinop Osub
                                               (Etempvar _oend (tptr tuchar))
                                               (Etempvar _op (tptr tuchar))
                                               tlong) tulong) tint)
                              (Ssequence
                                (Sloop Sskip Sbreak)
                                (Ssequence
                                  (Sloop
                                    (Sifthenelse (Econst_int (Int.repr 0) tint)
                                      (Scall None
                                        (Evar __force_has_format_string 
                                        (Tfunction ((tptr tschar) :: nil)
                                          tvoid
                                          {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                                        ((Evar ___stringlit_zstd_37 (tarray tschar 1)) ::
                                         nil))
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
                              Sskip)
                            Sbreak)
                          (Sifthenelse (Ebinop One
                                         (Etempvar _op (tptr tuchar))
                                         (Ecast
                                           (Econst_int (Int.repr 0) tint)
                                           (tptr tvoid)) tint)
                            (Ssequence
                              (Ssequence
                                (Sset _t'30 (Evar _litPtr (tptr tuchar)))
                                (Scall None
                                  (Evar _memmove (Tfunction
                                                   ((tptr tvoid) ::
                                                    (tptr tvoid) :: tulong ::
                                                    nil) (tptr tvoid)
                                                   cc_default))
                                  ((Etempvar _op (tptr tuchar)) ::
                                   (Etempvar _t'30 (tptr tuchar)) ::
                                   (Etempvar _lastLLSize__1 tulong) :: nil)))
                              (Sset _op
                                (Ebinop Oadd (Etempvar _op (tptr tuchar))
                                  (Etempvar _lastLLSize__1 tulong)
                                  (tptr tuchar))))
                            Sskip)))
                      (Sreturn (Some (Ecast
                                       (Ebinop Osub
                                         (Etempvar _op (tptr tuchar))
                                         (Etempvar _ostart (tptr tuchar))
                                         tlong) tulong))))).

Definition lg_reps : statement :=
(Ssequence
                                                (Sset _i__1
                                                  (Econst_int (Int.repr 0) tint))
                                                (Sloop
                                                  (Ssequence
                                                    (Sifthenelse (Ebinop Olt
                                                                   (Etempvar _i__1 tuint)
                                                                   (Econst_int (Int.repr 3) tint)
                                                                   tint)
                                                      Sskip
                                                      Sbreak)
                                                    (Ssequence
                                                      (Sset _t'35
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Efield
                                                              (Evar _seqState (Tstruct ___gp_seqState_t noattr))
                                                              _prevOffset
                                                              (tarray tulong 3))
                                                            (Etempvar _i__1 tuint)
                                                            (tptr tulong))
                                                          tulong))
                                                      (Sassign
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Efield
                                                              (Efield
                                                                (Ederef
                                                                  (Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                  (Tstruct _ZSTD_DCtx_s noattr))
                                                                _entropy
                                                                (Tstruct ___gp_ZSTD_entropyDTables_t noattr))
                                                              _rep
                                                              (tarray tuint 3))
                                                            (Etempvar _i__1 tuint)
                                                            (tptr tuint))
                                                          tuint)
                                                        (Ecast
                                                          (Etempvar _t'35 tulong)
                                                          tuint))))
                                                  (Sset _i__1
                                                    (Ebinop Oadd
                                                      (Etempvar _i__1 tuint)
                                                      (Econst_int (Int.repr 1) tint)
                                                      tuint)))).

Definition lg_fin_x2 : statement :=
(Ssequence
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _t'36
                                                                (Efield
                                                                  (Ederef
                                                                    (Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                  _litBufferLocation
                                                                  tint))
                                                              (Sifthenelse 
                                                                (Ebinop Oeq
                                                                  (Etempvar _t'36 tint)
                                                                  (Econst_int (Int.repr 2) tint)
                                                                  tint)
                                                                (Ssequence
                                                                  (Ssequence
                                                                    (Sset _t'37
                                                                    (Evar _litPtr (tptr tuchar)))
                                                                    (Ssequence
                                                                    (Sset _t'38
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _sequence__2 (tptr (Tstruct ___gp_seq_t noattr)))
                                                                    (Tstruct ___gp_seq_t noattr))
                                                                    _litLength
                                                                    tulong))
                                                                    (Scall (Some _t'24)
                                                                    (Evar _ZSTD_execSequenceSplitLitBuffer 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    (tptr (Tstruct ___gp_seq_t noattr)) ::
                                                                    (tptr (tptr tuchar)) ::
                                                                    (tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    nil)
                                                                    tulong
                                                                    cc_default))
                                                                    ((Etempvar _op (tptr tuchar)) ::
                                                                    (Etempvar _oend (tptr tuchar)) ::
                                                                    (Ebinop Osub
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'37 (tptr tuchar))
                                                                    (Etempvar _t'38 tulong)
                                                                    (tptr tuchar))
                                                                    (Econst_int (Int.repr 32) tint)
                                                                    (tptr tuchar)) ::
                                                                    (Etempvar _sequence__2 (tptr (Tstruct ___gp_seq_t noattr))) ::
                                                                    (Eaddrof
                                                                    (Evar _litPtr (tptr tuchar))
                                                                    (tptr (tptr tuchar))) ::
                                                                    (Etempvar _litBufferEnd (tptr tuchar)) ::
                                                                    (Etempvar _prefixStart (tptr tuchar)) ::
                                                                    (Etempvar _dictStart (tptr tuchar)) ::
                                                                    (Etempvar _dictEnd (tptr tuchar)) ::
                                                                    nil))))
                                                                  (Sset _t'23
                                                                    (Ecast
                                                                    (Etempvar _t'24 tulong)
                                                                    tulong)))
                                                                (Ssequence
                                                                  (Scall (Some _t'25)
                                                                    (Evar _ZSTD_execSequence 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    (tptr (Tstruct ___gp_seq_t noattr)) ::
                                                                    (tptr (tptr tuchar)) ::
                                                                    (tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    nil)
                                                                    tulong
                                                                    cc_default))
                                                                    ((Etempvar _op (tptr tuchar)) ::
                                                                    (Etempvar _oend (tptr tuchar)) ::
                                                                    (Etempvar _sequence__2 (tptr (Tstruct ___gp_seq_t noattr))) ::
                                                                    (Eaddrof
                                                                    (Evar _litPtr (tptr tuchar))
                                                                    (tptr (tptr tuchar))) ::
                                                                    (Etempvar _litBufferEnd (tptr tuchar)) ::
                                                                    (Etempvar _prefixStart (tptr tuchar)) ::
                                                                    (Etempvar _dictStart (tptr tuchar)) ::
                                                                    (Etempvar _dictEnd (tptr tuchar)) ::
                                                                    nil))
                                                                  (Sset _t'23
                                                                    (Ecast
                                                                    (Etempvar _t'25 tulong)
                                                                    tulong)))))
                                                            (Sset _oneSeqSize__3
                                                              (Etempvar _t'23 tulong)))
                                                          (Ssequence
                                                            (Ssequence
                                                              (Scall (Some _t'26)
                                                                (Evar _ZSTD_isError 
                                                                (Tfunction
                                                                  (tulong ::
                                                                   nil) tuint
                                                                  cc_default))
                                                                ((Etempvar _oneSeqSize__3 tulong) ::
                                                                 nil))
                                                              (Sifthenelse (Etempvar _t'26 tuint)
                                                                (Sreturn (Some (Etempvar _oneSeqSize__3 tulong)))
                                                                Sskip))
                                                            (Sset _op
                                                              (Ebinop Oadd
                                                                (Etempvar _op (tptr tuchar))
                                                                (Etempvar _oneSeqSize__3 tulong)
                                                                (tptr tuchar))))).

Definition lg_fin_x1 : statement :=
(Ssequence
                                                          (Ssequence
                                                            (Sset _t'41
                                                              (Efield
                                                                (Ederef
                                                                  (Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                  (Tstruct _ZSTD_DCtx_s noattr))
                                                                _litBufferEnd
                                                                (tptr tuchar)))
                                                            (Ssequence
                                                              (Sset _t'42
                                                                (Evar _litPtr (tptr tuchar)))
                                                              (Sset _leftoverLit__1
                                                                (Ecast
                                                                  (Ebinop Osub
                                                                    (Etempvar _t'41 (tptr tuchar))
                                                                    (Etempvar _t'42 (tptr tuchar))
                                                                    tlong)
                                                                  tulong))))
                                                          (Ssequence
                                                            (Sifthenelse (Etempvar _leftoverLit__1 tulong)
                                                              (Ssequence
                                                                (Sloop
                                                                  (Sifthenelse 
                                                                    (Ebinop Ogt
                                                                    (Etempvar _leftoverLit__1 tulong)
                                                                    (Ecast
                                                                    (Ebinop Osub
                                                                    (Etempvar _oend (tptr tuchar))
                                                                    (Etempvar _op (tptr tuchar))
                                                                    tlong)
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
                                                                    ((Evar ___stringlit_zstd_81 (tarray tschar 40)) ::
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
                                                                    Sskip)
                                                                  Sbreak)
                                                                (Ssequence
                                                                  (Ssequence
                                                                    (Sset _t'40
                                                                    (Evar _litPtr (tptr tuchar)))
                                                                    (Scall None
                                                                    (Evar _ZSTD_safecopyDstBeforeSrc 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _op (tptr tuchar)) ::
                                                                    (Etempvar _t'40 (tptr tuchar)) ::
                                                                    (Etempvar _leftoverLit__1 tulong) ::
                                                                    nil)))
                                                                  (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'39
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _sequence__2 (tptr (Tstruct ___gp_seq_t noattr)))
                                                                    (Tstruct ___gp_seq_t noattr))
                                                                    _litLength
                                                                    tulong))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _sequence__2 (tptr (Tstruct ___gp_seq_t noattr)))
                                                                    (Tstruct ___gp_seq_t noattr))
                                                                    _litLength
                                                                    tulong)
                                                                    (Ebinop Osub
                                                                    (Etempvar _t'39 tulong)
                                                                    (Etempvar _leftoverLit__1 tulong)
                                                                    tulong)))
                                                                    (Sset _op
                                                                    (Ebinop Oadd
                                                                    (Etempvar _op (tptr tuchar))
                                                                    (Etempvar _leftoverLit__1 tulong)
                                                                    (tptr tuchar))))))
                                                              Sskip)
                                                            (Ssequence
                                                              (Sassign
                                                                (Evar _litPtr (tptr tuchar))
                                                                (Efield
                                                                  (Ederef
                                                                    (Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                  _litExtraBuffer
                                                                  (tarray tuchar 65568)))
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (Econst_int (Int.repr 16) tint)
                                                                    tint)
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 128) tint)
                                                                    (Econst_int (Int.repr 10) tint)
                                                                    tint)
                                                                    tint)
                                                                    (Sset _t'19
                                                                    (Ecast
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (Econst_int (Int.repr 16) tint)
                                                                    tint)
                                                                    tint))
                                                                    (Sset _t'19
                                                                    (Ecast
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 128) tint)
                                                                    (Econst_int (Int.repr 10) tint)
                                                                    tint)
                                                                    tint)))
                                                                    (Sifthenelse 
                                                                    (Ebinop Ogt
                                                                    (Econst_int (Int.repr 64) tint)
                                                                    (Etempvar _t'19 tint)
                                                                    tint)
                                                                    (Sset _t'20
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 64) tint)
                                                                    tint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (Econst_int (Int.repr 16) tint)
                                                                    tint)
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 128) tint)
                                                                    (Econst_int (Int.repr 10) tint)
                                                                    tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _t'20
                                                                    (Ecast
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (Econst_int (Int.repr 16) tint)
                                                                    tint)
                                                                    tint))
                                                                    (Sset _t'20
                                                                    (Ecast
                                                                    (Etempvar _t'20 tint)
                                                                    tint)))
                                                                    (Ssequence
                                                                    (Sset _t'20
                                                                    (Ecast
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 128) tint)
                                                                    (Econst_int (Int.repr 10) tint)
                                                                    tint)
                                                                    tint))
                                                                    (Sset _t'20
                                                                    (Ecast
                                                                    (Etempvar _t'20 tint)
                                                                    tint))))))
                                                                  (Sset _litBufferEnd
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _litExtraBuffer
                                                                    (tarray tuchar 65568))
                                                                    (Etempvar _t'20 tint)
                                                                    (tptr tuchar))))
                                                                (Ssequence
                                                                  (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                    _litBufferLocation
                                                                    tint)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                  (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'21)
                                                                    (Evar _ZSTD_execSequence 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    (tptr (Tstruct ___gp_seq_t noattr)) ::
                                                                    (tptr (tptr tuchar)) ::
                                                                    (tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    nil)
                                                                    tulong
                                                                    cc_default))
                                                                    ((Etempvar _op (tptr tuchar)) ::
                                                                    (Etempvar _oend (tptr tuchar)) ::
                                                                    (Etempvar _sequence__2 (tptr (Tstruct ___gp_seq_t noattr))) ::
                                                                    (Eaddrof
                                                                    (Evar _litPtr (tptr tuchar))
                                                                    (tptr (tptr tuchar))) ::
                                                                    (Etempvar _litBufferEnd (tptr tuchar)) ::
                                                                    (Etempvar _prefixStart (tptr tuchar)) ::
                                                                    (Etempvar _dictStart (tptr tuchar)) ::
                                                                    (Etempvar _dictEnd (tptr tuchar)) ::
                                                                    nil))
                                                                    (Sset _oneSeqSize__2
                                                                    (Etempvar _t'21 tulong)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'22)
                                                                    (Evar _ZSTD_isError 
                                                                    (Tfunction
                                                                    (tulong ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                    ((Etempvar _oneSeqSize__2 tulong) ::
                                                                    nil))
                                                                    (Sifthenelse (Etempvar _t'22 tuint)
                                                                    (Sreturn (Some (Etempvar _oneSeqSize__2 tulong)))
                                                                    Sskip))
                                                                    (Sset _op
                                                                    (Ebinop Oadd
                                                                    (Etempvar _op (tptr tuchar))
                                                                    (Etempvar _oneSeqSize__2 tulong)
                                                                    (tptr tuchar)))))))))).

Definition lg_fin_chk : statement :=
(Ssequence
                                                        (Sset _t'43
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                              (Tstruct _ZSTD_DCtx_s noattr))
                                                            _litBufferLocation
                                                            tint))
                                                        (Sifthenelse 
                                                          (Ebinop Oeq
                                                            (Etempvar _t'43 tint)
                                                            (Econst_int (Int.repr 2) tint)
                                                            tint)
                                                          (Ssequence
                                                            (Sset _t'44
                                                              (Efield
                                                                (Ederef
                                                                  (Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                  (Tstruct _ZSTD_DCtx_s noattr))
                                                                _litBufferEnd
                                                                (tptr tuchar)))
                                                            (Ssequence
                                                              (Sset _t'45
                                                                (Evar _litPtr (tptr tuchar)))
                                                              (Ssequence
                                                                (Sset _t'46
                                                                  (Efield
                                                                    (Ederef
                                                                    (Etempvar _sequence__2 (tptr (Tstruct ___gp_seq_t noattr)))
                                                                    (Tstruct ___gp_seq_t noattr))
                                                                    _litLength
                                                                    tulong))
                                                                (Sset _t'27
                                                                  (Ecast
                                                                    (Ebinop Olt
                                                                    (Ecast
                                                                    (Ebinop Osub
                                                                    (Etempvar _t'44 (tptr tuchar))
                                                                    (Etempvar _t'45 (tptr tuchar))
                                                                    tlong)
                                                                    tulong)
                                                                    (Etempvar _t'46 tulong)
                                                                    tint)
                                                                    tbool)))))
                                                          (Sset _t'27
                                                            (Econst_int (Int.repr 0) tint)))).

Definition lg_fin_pre : statement :=
(Sset _sequence__2
                                                      (Ebinop Oadd
                                                        (Evar _sequences (tarray (Tstruct ___gp_seq_t noattr) 8))
                                                        (Ebinop Oand
                                                          (Etempvar _seqNb tint)
                                                          (Ebinop Osub
                                                            (Econst_int (Int.repr 8) tint)
                                                            (Econst_int (Int.repr 1) tint)
                                                            tint) tint)
                                                        (tptr (Tstruct ___gp_seq_t noattr)))).

Definition lg_end : statement :=
(Sloop
                                            (Ssequence
                                              (Scall (Some _t'18)
                                                (Evar _BIT_endOfDStream 
                                                (Tfunction
                                                  ((tptr (Tstruct ___gp_BIT_DStream_t noattr)) ::
                                                   nil) tuint cc_default))
                                                ((Eaddrof
                                                   (Efield
                                                     (Evar _seqState (Tstruct ___gp_seqState_t noattr))
                                                     _DStream
                                                     (Tstruct ___gp_BIT_DStream_t noattr))
                                                   (tptr (Tstruct ___gp_BIT_DStream_t noattr))) ::
                                                 nil))
                                              (Sifthenelse (Eunop Onotbool
                                                             (Etempvar _t'18 tuint)
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
                                                      (Sloop Sskip Sbreak)
                                                      (Ssequence
                                                        (Sloop Sskip Sbreak)
                                                        (Sreturn (Some 
                                                          (Ecast
                                                            (Eunop Oneg
                                                              (Econst_int (Int.repr 20) tint)
                                                              tint) tulong)))))))
                                                Sskip))
                                            Sbreak).

Definition lg_main_x2 : statement :=
(Ssequence
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sset _t'47
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                              (Tstruct _ZSTD_DCtx_s noattr))
                                                            _litBufferLocation
                                                            tint))
                                                        (Sifthenelse 
                                                          (Ebinop Oeq
                                                            (Etempvar _t'47 tint)
                                                            (Econst_int (Int.repr 2) tint)
                                                            tint)
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _t'48
                                                                (Evar _litPtr (tptr tuchar)))
                                                              (Ssequence
                                                                (Sset _t'49
                                                                  (Efield
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _sequences (tarray (Tstruct ___gp_seq_t noattr) 8))
                                                                    (Ebinop Oand
                                                                    (Ebinop Osub
                                                                    (Etempvar _seqNb tint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tint)
                                                                    (Ebinop Osub
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    tint)
                                                                    (tptr (Tstruct ___gp_seq_t noattr)))
                                                                    (Tstruct ___gp_seq_t noattr))
                                                                    _litLength
                                                                    tulong))
                                                                (Scall (Some _t'13)
                                                                  (Evar _ZSTD_execSequenceSplitLitBuffer 
                                                                  (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    (tptr (Tstruct ___gp_seq_t noattr)) ::
                                                                    (tptr (tptr tuchar)) ::
                                                                    (tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    nil)
                                                                    tulong
                                                                    cc_default))
                                                                  ((Etempvar _op (tptr tuchar)) ::
                                                                   (Etempvar _oend (tptr tuchar)) ::
                                                                   (Ebinop Osub
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'48 (tptr tuchar))
                                                                    (Etempvar _t'49 tulong)
                                                                    (tptr tuchar))
                                                                    (Econst_int (Int.repr 32) tint)
                                                                    (tptr tuchar)) ::
                                                                   (Ebinop Oadd
                                                                    (Evar _sequences (tarray (Tstruct ___gp_seq_t noattr) 8))
                                                                    (Ebinop Oand
                                                                    (Ebinop Osub
                                                                    (Etempvar _seqNb tint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tint)
                                                                    (Ebinop Osub
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    tint)
                                                                    (tptr (Tstruct ___gp_seq_t noattr))) ::
                                                                   (Eaddrof
                                                                    (Evar _litPtr (tptr tuchar))
                                                                    (tptr (tptr tuchar))) ::
                                                                   (Etempvar _litBufferEnd (tptr tuchar)) ::
                                                                   (Etempvar _prefixStart (tptr tuchar)) ::
                                                                   (Etempvar _dictStart (tptr tuchar)) ::
                                                                   (Etempvar _dictEnd (tptr tuchar)) ::
                                                                   nil))))
                                                            (Sset _t'12
                                                              (Ecast
                                                                (Etempvar _t'13 tulong)
                                                                tulong)))
                                                          (Ssequence
                                                            (Scall (Some _t'14)
                                                              (Evar _ZSTD_execSequence 
                                                              (Tfunction
                                                                ((tptr tuchar) ::
                                                                 (tptr tuchar) ::
                                                                 (tptr (Tstruct ___gp_seq_t noattr)) ::
                                                                 (tptr (tptr tuchar)) ::
                                                                 (tptr tuchar) ::
                                                                 (tptr tuchar) ::
                                                                 (tptr tuchar) ::
                                                                 (tptr tuchar) ::
                                                                 nil) tulong
                                                                cc_default))
                                                              ((Etempvar _op (tptr tuchar)) ::
                                                               (Etempvar _oend (tptr tuchar)) ::
                                                               (Ebinop Oadd
                                                                 (Evar _sequences (tarray (Tstruct ___gp_seq_t noattr) 8))
                                                                 (Ebinop Oand
                                                                   (Ebinop Osub
                                                                    (Etempvar _seqNb tint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tint)
                                                                   (Ebinop Osub
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                   tint)
                                                                 (tptr (Tstruct ___gp_seq_t noattr))) ::
                                                               (Eaddrof
                                                                 (Evar _litPtr (tptr tuchar))
                                                                 (tptr (tptr tuchar))) ::
                                                               (Etempvar _litBufferEnd (tptr tuchar)) ::
                                                               (Etempvar _prefixStart (tptr tuchar)) ::
                                                               (Etempvar _dictStart (tptr tuchar)) ::
                                                               (Etempvar _dictEnd (tptr tuchar)) ::
                                                               nil))
                                                            (Sset _t'12
                                                              (Ecast
                                                                (Etempvar _t'14 tulong)
                                                                tulong)))))
                                                      (Sset _oneSeqSize__1
                                                        (Etempvar _t'12 tulong)))
                                                    (Ssequence
                                                      (Ssequence
                                                        (Scall (Some _t'15)
                                                          (Evar _ZSTD_isError 
                                                          (Tfunction
                                                            (tulong :: nil)
                                                            tuint cc_default))
                                                          ((Etempvar _oneSeqSize__1 tulong) ::
                                                           nil))
                                                        (Sifthenelse (Etempvar _t'15 tuint)
                                                          (Sreturn (Some (Etempvar _oneSeqSize__1 tulong)))
                                                          Sskip))
                                                      (Ssequence
                                                        (Ssequence
                                                          (Scall (Some _t'16)
                                                            (Evar _ZSTD_prefetchMatch 
                                                            (Tfunction
                                                              (tulong ::
                                                               (tptr (Tstruct ___gp_seq_t noattr)) ::
                                                               (tptr tuchar) ::
                                                               (tptr tuchar) ::
                                                               nil) tulong
                                                              cc_default))
                                                            ((Etempvar _prefetchPos tulong) ::
                                                             (Eaddrof
                                                               (Evar _sequence__1 (Tstruct ___gp_seq_t noattr))
                                                               (tptr (Tstruct ___gp_seq_t noattr))) ::
                                                             (Etempvar _prefixStart (tptr tuchar)) ::
                                                             (Etempvar _dictEnd (tptr tuchar)) ::
                                                             nil))
                                                          (Sset _prefetchPos
                                                            (Etempvar _t'16 tulong)))
                                                        (Ssequence
                                                          (Scall None
                                                            (Evar _ZSTD_seqCopy 
                                                            (Tfunction
                                                              ((tptr (Tstruct ___gp_seq_t noattr)) ::
                                                               (tptr (Tstruct ___gp_seq_t noattr)) ::
                                                               nil) tvoid
                                                              cc_default))
                                                            ((Ebinop Oadd
                                                               (Evar _sequences (tarray (Tstruct ___gp_seq_t noattr) 8))
                                                               (Ebinop Oand
                                                                 (Etempvar _seqNb tint)
                                                                 (Ebinop Osub
                                                                   (Econst_int (Int.repr 8) tint)
                                                                   (Econst_int (Int.repr 1) tint)
                                                                   tint)
                                                                 tint)
                                                               (tptr (Tstruct ___gp_seq_t noattr))) ::
                                                             (Eaddrof
                                                               (Evar _sequence__1 (Tstruct ___gp_seq_t noattr))
                                                               (tptr (Tstruct ___gp_seq_t noattr))) ::
                                                             nil))
                                                          (Sset _op
                                                            (Ebinop Oadd
                                                              (Etempvar _op (tptr tuchar))
                                                              (Etempvar _oneSeqSize__1 tulong)
                                                              (tptr tuchar))))))).

Definition lg_main_x1 : statement :=
(Ssequence
                                                    (Ssequence
                                                      (Sset _t'52
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                            (Tstruct _ZSTD_DCtx_s noattr))
                                                          _litBufferEnd
                                                          (tptr tuchar)))
                                                      (Ssequence
                                                        (Sset _t'53
                                                          (Evar _litPtr (tptr tuchar)))
                                                        (Sset _leftoverLit
                                                          (Ecast
                                                            (Ebinop Osub
                                                              (Etempvar _t'52 (tptr tuchar))
                                                              (Etempvar _t'53 (tptr tuchar))
                                                              tlong) tulong))))
                                                    (Ssequence
                                                      (Sifthenelse (Etempvar _leftoverLit tulong)
                                                        (Ssequence
                                                          (Sloop
                                                            (Sifthenelse 
                                                              (Ebinop Ogt
                                                                (Etempvar _leftoverLit tulong)
                                                                (Ecast
                                                                  (Ebinop Osub
                                                                    (Etempvar _oend (tptr tuchar))
                                                                    (Etempvar _op (tptr tuchar))
                                                                    tlong)
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
                                                                    ((Evar ___stringlit_zstd_81 (tarray tschar 40)) ::
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
                                                              Sskip)
                                                            Sbreak)
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _t'51
                                                                (Evar _litPtr (tptr tuchar)))
                                                              (Scall None
                                                                (Evar _ZSTD_safecopyDstBeforeSrc 
                                                                (Tfunction
                                                                  ((tptr tuchar) ::
                                                                   (tptr tuchar) ::
                                                                   tulong ::
                                                                   nil) tvoid
                                                                  cc_default))
                                                                ((Etempvar _op (tptr tuchar)) ::
                                                                 (Etempvar _t'51 (tptr tuchar)) ::
                                                                 (Etempvar _leftoverLit tulong) ::
                                                                 nil)))
                                                            (Ssequence
                                                              (Ssequence
                                                                (Sset _t'50
                                                                  (Efield
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _sequences (tarray (Tstruct ___gp_seq_t noattr) 8))
                                                                    (Ebinop Oand
                                                                    (Ebinop Osub
                                                                    (Etempvar _seqNb tint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tint)
                                                                    (Ebinop Osub
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    tint)
                                                                    (tptr (Tstruct ___gp_seq_t noattr)))
                                                                    (Tstruct ___gp_seq_t noattr))
                                                                    _litLength
                                                                    tulong))
                                                                (Sassign
                                                                  (Efield
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _sequences (tarray (Tstruct ___gp_seq_t noattr) 8))
                                                                    (Ebinop Oand
                                                                    (Ebinop Osub
                                                                    (Etempvar _seqNb tint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tint)
                                                                    (Ebinop Osub
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    tint)
                                                                    (tptr (Tstruct ___gp_seq_t noattr)))
                                                                    (Tstruct ___gp_seq_t noattr))
                                                                    _litLength
                                                                    tulong)
                                                                  (Ebinop Osub
                                                                    (Etempvar _t'50 tulong)
                                                                    (Etempvar _leftoverLit tulong)
                                                                    tulong)))
                                                              (Sset _op
                                                                (Ebinop Oadd
                                                                  (Etempvar _op (tptr tuchar))
                                                                  (Etempvar _leftoverLit tulong)
                                                                  (tptr tuchar))))))
                                                        Sskip)
                                                      (Ssequence
                                                        (Sassign
                                                          (Evar _litPtr (tptr tuchar))
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                              (Tstruct _ZSTD_DCtx_s noattr))
                                                            _litExtraBuffer
                                                            (tarray tuchar 65568)))
                                                        (Ssequence
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sifthenelse 
                                                                (Ebinop Olt
                                                                  (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (Econst_int (Int.repr 16) tint)
                                                                    tint)
                                                                  (Ebinop Oshl
                                                                    (Econst_int (Int.repr 128) tint)
                                                                    (Econst_int (Int.repr 10) tint)
                                                                    tint)
                                                                  tint)
                                                                (Sset _t'7
                                                                  (Ecast
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (Econst_int (Int.repr 16) tint)
                                                                    tint)
                                                                    tint))
                                                                (Sset _t'7
                                                                  (Ecast
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 128) tint)
                                                                    (Econst_int (Int.repr 10) tint)
                                                                    tint)
                                                                    tint)))
                                                              (Sifthenelse 
                                                                (Ebinop Ogt
                                                                  (Econst_int (Int.repr 64) tint)
                                                                  (Etempvar _t'7 tint)
                                                                  tint)
                                                                (Sset _t'8
                                                                  (Ecast
                                                                    (Econst_int (Int.repr 64) tint)
                                                                    tint))
                                                                (Sifthenelse 
                                                                  (Ebinop Olt
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (Econst_int (Int.repr 16) tint)
                                                                    tint)
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 128) tint)
                                                                    (Econst_int (Int.repr 10) tint)
                                                                    tint)
                                                                    tint)
                                                                  (Ssequence
                                                                    (Sset _t'8
                                                                    (Ecast
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (Econst_int (Int.repr 16) tint)
                                                                    tint)
                                                                    tint))
                                                                    (Sset _t'8
                                                                    (Ecast
                                                                    (Etempvar _t'8 tint)
                                                                    tint)))
                                                                  (Ssequence
                                                                    (Sset _t'8
                                                                    (Ecast
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 128) tint)
                                                                    (Econst_int (Int.repr 10) tint)
                                                                    tint)
                                                                    tint))
                                                                    (Sset _t'8
                                                                    (Ecast
                                                                    (Etempvar _t'8 tint)
                                                                    tint))))))
                                                            (Sset _litBufferEnd
                                                              (Ebinop Oadd
                                                                (Efield
                                                                  (Ederef
                                                                    (Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                    (Tstruct _ZSTD_DCtx_s noattr))
                                                                  _litExtraBuffer
                                                                  (tarray tuchar 65568))
                                                                (Etempvar _t'8 tint)
                                                                (tptr tuchar))))
                                                          (Ssequence
                                                            (Sassign
                                                              (Efield
                                                                (Ederef
                                                                  (Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                                  (Tstruct _ZSTD_DCtx_s noattr))
                                                                _litBufferLocation
                                                                tint)
                                                              (Econst_int (Int.repr 0) tint))
                                                            (Ssequence
                                                              (Ssequence
                                                                (Scall (Some _t'9)
                                                                  (Evar _ZSTD_execSequence 
                                                                  (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    (tptr (Tstruct ___gp_seq_t noattr)) ::
                                                                    (tptr (tptr tuchar)) ::
                                                                    (tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    nil)
                                                                    tulong
                                                                    cc_default))
                                                                  ((Etempvar _op (tptr tuchar)) ::
                                                                   (Etempvar _oend (tptr tuchar)) ::
                                                                   (Ebinop Oadd
                                                                    (Evar _sequences (tarray (Tstruct ___gp_seq_t noattr) 8))
                                                                    (Ebinop Oand
                                                                    (Ebinop Osub
                                                                    (Etempvar _seqNb tint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tint)
                                                                    (Ebinop Osub
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    tint)
                                                                    (tptr (Tstruct ___gp_seq_t noattr))) ::
                                                                   (Eaddrof
                                                                    (Evar _litPtr (tptr tuchar))
                                                                    (tptr (tptr tuchar))) ::
                                                                   (Etempvar _litBufferEnd (tptr tuchar)) ::
                                                                   (Etempvar _prefixStart (tptr tuchar)) ::
                                                                   (Etempvar _dictStart (tptr tuchar)) ::
                                                                   (Etempvar _dictEnd (tptr tuchar)) ::
                                                                   nil))
                                                                (Sset _oneSeqSize
                                                                  (Etempvar _t'9 tulong)))
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Scall (Some _t'10)
                                                                    (Evar _ZSTD_isError 
                                                                    (Tfunction
                                                                    (tulong ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                    ((Etempvar _oneSeqSize tulong) ::
                                                                    nil))
                                                                  (Sifthenelse (Etempvar _t'10 tuint)
                                                                    (Sreturn (Some (Etempvar _oneSeqSize tulong)))
                                                                    Sskip))
                                                                (Ssequence
                                                                  (Ssequence
                                                                    (Scall (Some _t'11)
                                                                    (Evar _ZSTD_prefetchMatch 
                                                                    (Tfunction
                                                                    (tulong ::
                                                                    (tptr (Tstruct ___gp_seq_t noattr)) ::
                                                                    (tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    nil)
                                                                    tulong
                                                                    cc_default))
                                                                    ((Etempvar _prefetchPos tulong) ::
                                                                    (Eaddrof
                                                                    (Evar _sequence__1 (Tstruct ___gp_seq_t noattr))
                                                                    (tptr (Tstruct ___gp_seq_t noattr))) ::
                                                                    (Etempvar _prefixStart (tptr tuchar)) ::
                                                                    (Etempvar _dictEnd (tptr tuchar)) ::
                                                                    nil))
                                                                    (Sset _prefetchPos
                                                                    (Etempvar _t'11 tulong)))
                                                                  (Ssequence
                                                                    (Scall None
                                                                    (Evar _ZSTD_seqCopy 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct ___gp_seq_t noattr)) ::
                                                                    (tptr (Tstruct ___gp_seq_t noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Ebinop Oadd
                                                                    (Evar _sequences (tarray (Tstruct ___gp_seq_t noattr) 8))
                                                                    (Ebinop Oand
                                                                    (Etempvar _seqNb tint)
                                                                    (Ebinop Osub
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    tint)
                                                                    (tptr (Tstruct ___gp_seq_t noattr))) ::
                                                                    (Eaddrof
                                                                    (Evar _sequence__1 (Tstruct ___gp_seq_t noattr))
                                                                    (tptr (Tstruct ___gp_seq_t noattr))) ::
                                                                    nil))
                                                                    (Sset _op
                                                                    (Ebinop Oadd
                                                                    (Etempvar _op (tptr tuchar))
                                                                    (Etempvar _oneSeqSize tulong)
                                                                    (tptr tuchar)))))))))))).

Definition lg_main_chk : statement :=
(Ssequence
                                                  (Sset _t'54
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                        (Tstruct _ZSTD_DCtx_s noattr))
                                                      _litBufferLocation
                                                      tint))
                                                  (Sifthenelse (Ebinop Oeq
                                                                 (Etempvar _t'54 tint)
                                                                 (Econst_int (Int.repr 2) tint)
                                                                 tint)
                                                    (Ssequence
                                                      (Sset _t'55
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                            (Tstruct _ZSTD_DCtx_s noattr))
                                                          _litBufferEnd
                                                          (tptr tuchar)))
                                                      (Ssequence
                                                        (Sset _t'56
                                                          (Evar _litPtr (tptr tuchar)))
                                                        (Ssequence
                                                          (Sset _t'57
                                                            (Efield
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _sequences (tarray (Tstruct ___gp_seq_t noattr) 8))
                                                                  (Ebinop Oand
                                                                    (Ebinop Osub
                                                                    (Etempvar _seqNb tint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tint)
                                                                    (Ebinop Osub
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    tint)
                                                                  (tptr (Tstruct ___gp_seq_t noattr)))
                                                                (Tstruct ___gp_seq_t noattr))
                                                              _litLength
                                                              tulong))
                                                          (Sset _t'17
                                                            (Ecast
                                                              (Ebinop Olt
                                                                (Ecast
                                                                  (Ebinop Osub
                                                                    (Etempvar _t'55 (tptr tuchar))
                                                                    (Etempvar _t'56 (tptr tuchar))
                                                                    tlong)
                                                                  tulong)
                                                                (Etempvar _t'57 tulong)
                                                                tint) tbool)))))
                                                    (Sset _t'17
                                                      (Econst_int (Int.repr 0) tint)))).

Definition lg_main_dec : statement :=
(Scall None
                                                (Evar _ZSTD_decodeSequence 
                                                (Tfunction
                                                  ((tptr (Tstruct ___gp_seq_t noattr)) ::
                                                   (tptr (Tstruct ___gp_seqState_t noattr)) ::
                                                   tint :: tint :: nil) tvoid
                                                  cc_default))
                                                ((Eaddrof
                                                   (Evar _sequence__1 (Tstruct ___gp_seq_t noattr))
                                                   (tptr (Tstruct ___gp_seq_t noattr))) ::
                                                 (Eaddrof
                                                   (Evar _seqState (Tstruct ___gp_seqState_t noattr))
                                                   (tptr (Tstruct ___gp_seqState_t noattr))) ::
                                                 (Etempvar _isLongOffset tint) ::
                                                 (Ebinop Oeq
                                                   (Etempvar _seqNb tint)
                                                   (Ebinop Osub
                                                     (Etempvar _nbSeq tint)
                                                     (Econst_int (Int.repr 1) tint)
                                                     tint) tint) :: nil)).

Definition lg_adv_body : statement :=
(Ssequence
                                              (Scall None
                                                (Evar _ZSTD_decodeSequence 
                                                (Tfunction
                                                  ((tptr (Tstruct ___gp_seq_t noattr)) ::
                                                   (tptr (Tstruct ___gp_seqState_t noattr)) ::
                                                   tint :: tint :: nil) tvoid
                                                  cc_default))
                                                ((Eaddrof
                                                   (Evar _sequence (Tstruct ___gp_seq_t noattr))
                                                   (tptr (Tstruct ___gp_seq_t noattr))) ::
                                                 (Eaddrof
                                                   (Evar _seqState (Tstruct ___gp_seqState_t noattr))
                                                   (tptr (Tstruct ___gp_seqState_t noattr))) ::
                                                 (Etempvar _isLongOffset tint) ::
                                                 (Ebinop Oeq
                                                   (Etempvar _seqNb tint)
                                                   (Ebinop Osub
                                                     (Etempvar _nbSeq tint)
                                                     (Econst_int (Int.repr 1) tint)
                                                     tint) tint) :: nil))
                                              (Ssequence
                                                (Ssequence
                                                  (Scall (Some _t'6)
                                                    (Evar _ZSTD_prefetchMatch 
                                                    (Tfunction
                                                      (tulong ::
                                                       (tptr (Tstruct ___gp_seq_t noattr)) ::
                                                       (tptr tuchar) ::
                                                       (tptr tuchar) :: nil)
                                                      tulong cc_default))
                                                    ((Etempvar _prefetchPos tulong) ::
                                                     (Eaddrof
                                                       (Evar _sequence (Tstruct ___gp_seq_t noattr))
                                                       (tptr (Tstruct ___gp_seq_t noattr))) ::
                                                     (Etempvar _prefixStart (tptr tuchar)) ::
                                                     (Etempvar _dictEnd (tptr tuchar)) ::
                                                     nil))
                                                  (Sset _prefetchPos
                                                    (Etempvar _t'6 tulong)))
                                                (Scall None
                                                  (Evar _ZSTD_seqCopy 
                                                  (Tfunction
                                                    ((tptr (Tstruct ___gp_seq_t noattr)) ::
                                                     (tptr (Tstruct ___gp_seq_t noattr)) ::
                                                     nil) tvoid cc_default))
                                                  ((Ebinop Oadd
                                                     (Evar _sequences (tarray (Tstruct ___gp_seq_t noattr) 8))
                                                     (Etempvar _seqNb tint)
                                                     (tptr (Tstruct ___gp_seq_t noattr))) ::
                                                   (Eaddrof
                                                     (Evar _sequence (Tstruct ___gp_seq_t noattr))
                                                     (tptr (Tstruct ___gp_seq_t noattr))) ::
                                                   nil)))).

Definition lg_init (REST: statement) : statement :=
(Ssequence
                      (Ssequence
                        (Sifthenelse (Ebinop Olt (Etempvar _nbSeq tint)
                                       (Econst_int (Int.repr 8) tint) tint)
                          (Sset _t'3 (Ecast (Etempvar _nbSeq tint) tint))
                          (Sset _t'3
                            (Ecast (Econst_int (Int.repr 8) tint) tint)))
                        (Sset _seqAdvance (Etempvar _t'3 tint)))
                      (Ssequence
                        (Sset _prefetchPos
                          (Ecast
                            (Ebinop Osub (Etempvar _op (tptr tuchar))
                              (Etempvar _prefixStart (tptr tuchar)) tlong)
                            tulong))
                        (Ssequence
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                (Tstruct _ZSTD_DCtx_s noattr)) _fseEntropy
                              tuint) (Econst_int (Int.repr 1) tint))
                          (Ssequence
                            (Ssequence
                              (Sset _i (Econst_int (Int.repr 0) tint))
                              (Sloop
                                (Ssequence
                                  (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                                 (Econst_int (Int.repr 3) tint)
                                                 tint)
                                    Sskip
                                    Sbreak)
                                  (Ssequence
                                    (Sset _t'61
                                      (Ederef
                                        (Ebinop Oadd
                                          (Efield
                                            (Efield
                                              (Ederef
                                                (Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                (Tstruct _ZSTD_DCtx_s noattr))
                                              _entropy
                                              (Tstruct ___gp_ZSTD_entropyDTables_t noattr))
                                            _rep (tarray tuint 3))
                                          (Etempvar _i tint) (tptr tuint))
                                        tuint))
                                    (Sassign
                                      (Ederef
                                        (Ebinop Oadd
                                          (Efield
                                            (Evar _seqState (Tstruct ___gp_seqState_t noattr))
                                            _prevOffset (tarray tulong 3))
                                          (Etempvar _i tint) (tptr tulong))
                                        tulong) (Etempvar _t'61 tuint))))
                                (Sset _i
                                  (Ebinop Oadd (Etempvar _i tint)
                                    (Econst_int (Int.repr 1) tint) tint))))
                            (Ssequence
                              (Sloop
                                (Ssequence
                                  (Ssequence
                                    (Scall (Some _t'4)
                                      (Evar _BIT_initDStream (Tfunction
                                                               ((tptr (Tstruct ___gp_BIT_DStream_t noattr)) ::
                                                                (tptr tvoid) ::
                                                                tulong ::
                                                                nil) tulong
                                                               cc_default))
                                      ((Eaddrof
                                         (Efield
                                           (Evar _seqState (Tstruct ___gp_seqState_t noattr))
                                           _DStream
                                           (Tstruct ___gp_BIT_DStream_t noattr))
                                         (tptr (Tstruct ___gp_BIT_DStream_t noattr))) ::
                                       (Etempvar _seqStart (tptr tvoid)) ::
                                       (Etempvar _seqSize tulong) :: nil))
                                    (Scall (Some _t'5)
                                      (Evar _ERR_isError (Tfunction
                                                           (tulong :: nil)
                                                           tuint cc_default))
                                      ((Etempvar _t'4 tulong) :: nil)))
                                  (Sifthenelse (Etempvar _t'5 tuint)
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
                                            (Sreturn (Some (Ecast
                                                             (Eunop Oneg
                                                               (Econst_int (Int.repr 20) tint)
                                                               tint) tulong)))))))
                                    Sskip))
                                Sbreak)
                              (Ssequence
                                (Ssequence
                                  (Sset _t'60
                                    (Efield
                                      (Ederef
                                        (Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                        (Tstruct _ZSTD_DCtx_s noattr))
                                      _LLTptr
                                      (tptr (Tstruct ___gp_ZSTD_seqSymbol noattr))))
                                  (Scall None
                                    (Evar _ZSTD_initFseState (Tfunction
                                                               ((tptr (Tstruct ___gp_ZSTD_fseState noattr)) ::
                                                                (tptr (Tstruct ___gp_BIT_DStream_t noattr)) ::
                                                                (tptr (Tstruct ___gp_ZSTD_seqSymbol noattr)) ::
                                                                nil) tvoid
                                                               cc_default))
                                    ((Eaddrof
                                       (Efield
                                         (Evar _seqState (Tstruct ___gp_seqState_t noattr))
                                         _stateLL
                                         (Tstruct ___gp_ZSTD_fseState noattr))
                                       (tptr (Tstruct ___gp_ZSTD_fseState noattr))) ::
                                     (Eaddrof
                                       (Efield
                                         (Evar _seqState (Tstruct ___gp_seqState_t noattr))
                                         _DStream
                                         (Tstruct ___gp_BIT_DStream_t noattr))
                                       (tptr (Tstruct ___gp_BIT_DStream_t noattr))) ::
                                     (Etempvar _t'60 (tptr (Tstruct ___gp_ZSTD_seqSymbol noattr))) ::
                                     nil)))
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'59
                                      (Efield
                                        (Ederef
                                          (Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                          (Tstruct _ZSTD_DCtx_s noattr))
                                        _OFTptr
                                        (tptr (Tstruct ___gp_ZSTD_seqSymbol noattr))))
                                    (Scall None
                                      (Evar _ZSTD_initFseState (Tfunction
                                                                 ((tptr (Tstruct ___gp_ZSTD_fseState noattr)) ::
                                                                  (tptr (Tstruct ___gp_BIT_DStream_t noattr)) ::
                                                                  (tptr (Tstruct ___gp_ZSTD_seqSymbol noattr)) ::
                                                                  nil) tvoid
                                                                 cc_default))
                                      ((Eaddrof
                                         (Efield
                                           (Evar _seqState (Tstruct ___gp_seqState_t noattr))
                                           _stateOffb
                                           (Tstruct ___gp_ZSTD_fseState noattr))
                                         (tptr (Tstruct ___gp_ZSTD_fseState noattr))) ::
                                       (Eaddrof
                                         (Efield
                                           (Evar _seqState (Tstruct ___gp_seqState_t noattr))
                                           _DStream
                                           (Tstruct ___gp_BIT_DStream_t noattr))
                                         (tptr (Tstruct ___gp_BIT_DStream_t noattr))) ::
                                       (Etempvar _t'59 (tptr (Tstruct ___gp_ZSTD_seqSymbol noattr))) ::
                                       nil)))
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'58
                                        (Efield
                                          (Ederef
                                            (Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                            (Tstruct _ZSTD_DCtx_s noattr))
                                          _MLTptr
                                          (tptr (Tstruct ___gp_ZSTD_seqSymbol noattr))))
                                      (Scall None
                                        (Evar _ZSTD_initFseState (Tfunction
                                                                   ((tptr (Tstruct ___gp_ZSTD_fseState noattr)) ::
                                                                    (tptr (Tstruct ___gp_BIT_DStream_t noattr)) ::
                                                                    (tptr (Tstruct ___gp_ZSTD_seqSymbol noattr)) ::
                                                                    nil)
                                                                   tvoid
                                                                   cc_default))
                                        ((Eaddrof
                                           (Efield
                                             (Evar _seqState (Tstruct ___gp_seqState_t noattr))
                                             _stateML
                                             (Tstruct ___gp_ZSTD_fseState noattr))
                                           (tptr (Tstruct ___gp_ZSTD_fseState noattr))) ::
                                         (Eaddrof
                                           (Efield
                                             (Evar _seqState (Tstruct ___gp_seqState_t noattr))
                                             _DStream
                                             (Tstruct ___gp_BIT_DStream_t noattr))
                                           (tptr (Tstruct ___gp_BIT_DStream_t noattr))) ::
                                         (Etempvar _t'58 (tptr (Tstruct ___gp_ZSTD_seqSymbol noattr))) ::
                                         nil)))
                                    REST)))))))).

Definition lg_pro (REST: statement) : statement :=
(Ssequence
  (Sset _ostart (Ecast (Etempvar _dst (tptr tvoid)) (tptr tuchar)))
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'66
          (Efield
            (Ederef (Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr)))
              (Tstruct _ZSTD_DCtx_s noattr)) _litBufferLocation tint))
        (Sifthenelse (Ebinop Oeq (Etempvar _t'66 tint)
                       (Econst_int (Int.repr 1) tint) tint)
          (Ssequence
            (Sset _t'67
              (Efield
                (Ederef (Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                  (Tstruct _ZSTD_DCtx_s noattr)) _litBuffer (tptr tuchar)))
            (Sset _t'1 (Ecast (Etempvar _t'67 (tptr tuchar)) (tptr tuchar))))
          (Ssequence
            (Scall (Some _t'2)
              (Evar _ZSTD_maybeNullPtrAdd (Tfunction
                                            ((tptr tvoid) :: tlong :: nil)
                                            (tptr tvoid) cc_default))
              ((Etempvar _ostart (tptr tuchar)) ::
               (Ecast (Etempvar _maxDstSize tulong) tlong) :: nil))
            (Sset _t'1
              (Ecast (Ecast (Etempvar _t'2 (tptr tvoid)) (tptr tuchar))
                (tptr tuchar))))))
      (Sset _oend (Etempvar _t'1 (tptr tuchar))))
    (Ssequence
      (Sset _op (Etempvar _ostart (tptr tuchar)))
      (Ssequence
        (Ssequence
          (Sset _t'65
            (Efield
              (Ederef (Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                (Tstruct _ZSTD_DCtx_s noattr)) _litPtr (tptr tuchar)))
          (Sassign (Evar _litPtr (tptr tuchar))
            (Etempvar _t'65 (tptr tuchar))))
        (Ssequence
          (Sset _litBufferEnd
            (Efield
              (Ederef (Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                (Tstruct _ZSTD_DCtx_s noattr)) _litBufferEnd (tptr tuchar)))
          (Ssequence
            (Ssequence
              (Sset _t'64
                (Efield
                  (Ederef
                    (Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                    (Tstruct _ZSTD_DCtx_s noattr)) _prefixStart (tptr tvoid)))
              (Sset _prefixStart
                (Ecast (Etempvar _t'64 (tptr tvoid)) (tptr tuchar))))
            (Ssequence
              (Ssequence
                (Sset _t'63
                  (Efield
                    (Ederef
                      (Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                      (Tstruct _ZSTD_DCtx_s noattr)) _virtualStart
                    (tptr tvoid)))
                (Sset _dictStart
                  (Ecast (Etempvar _t'63 (tptr tvoid)) (tptr tuchar))))
              (Ssequence
                (Ssequence
                  (Sset _t'62
                    (Efield
                      (Ederef
                        (Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                        (Tstruct _ZSTD_DCtx_s noattr)) _dictEnd (tptr tvoid)))
                  (Sset _dictEnd
                    (Ecast (Etempvar _t'62 (tptr tvoid)) (tptr tuchar))))
                REST)))))))).

Lemma lg_body_eq : fn_body f_ZSTD_decompressSequencesLong_body =
  (lg_pro (Ssequence (Sifthenelse (Etempvar _nbSeq tint) (lg_init (Ssequence (Ssequence (Sset _seqNb (Econst_int (Int.repr 0) tint)) (Sloop (Ssequence (Sifthenelse (Ebinop Olt (Etempvar _seqNb tint) (Etempvar _seqAdvance tint) tint) Sskip Sbreak) lg_adv_body) (Sset _seqNb (Ebinop Oadd (Etempvar _seqNb tint) (Econst_int (Int.repr 1) tint) tint)))) (Ssequence (Sloop (Ssequence (Sifthenelse (Ebinop Olt (Etempvar _seqNb tint) (Etempvar _nbSeq tint) tint) Sskip Sbreak) (Ssequence lg_main_dec (Ssequence lg_main_chk (Sifthenelse (Etempvar _t'17 tint) lg_main_x1 lg_main_x2)))) (Sset _seqNb (Ebinop Oadd (Etempvar _seqNb tint) (Econst_int (Int.repr 1) tint) tint))) (Ssequence lg_end (Ssequence (Sset _seqNb (Ebinop Osub (Etempvar _seqNb tint) (Etempvar _seqAdvance tint) tint)) (Ssequence (Sloop (Ssequence (Sifthenelse (Ebinop Olt (Etempvar _seqNb tint) (Etempvar _nbSeq tint) tint) Sskip Sbreak) (Ssequence lg_fin_pre (Ssequence lg_fin_chk (Sifthenelse (Etempvar _t'27 tint) lg_fin_x1 lg_fin_x2)))) (Sset _seqNb (Ebinop Oadd (Etempvar _seqNb tint) (Econst_int (Int.repr 1) tint) tint))) lg_reps)))))) Sskip) lg_epi)).
Proof. reflexivity. Qed.
