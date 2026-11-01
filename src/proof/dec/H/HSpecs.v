(* Subtree H of the decoder: the specifications of the 24 functions of ids_H, in
   that order.  22 are fixed elsewhere (H_exports: DecIface.v; H_api: Spec_api6.v); the two internal
   ones are here: ZSTD_errorFrameSizeInfo and ZSTD_findFrameSizeInfo (out-pointer to a
   ZSTD_frameSizeInfo {nbBlocks; compressedSize; decompressedBound}, exact against Info.frame_size_info).
   Every body of H is proved against H_G = Gprog ++ H_specs (files body_H_*.v). *)
Require Export Zstd.proof.dec.DecSubtrees.
Local Open Scope logic.

Definition t_fsi : type := Tstruct ___gp_ZSTD_frameSizeInfo noattr.

(* the struct after ZSTD_errorFrameSizeInfo(fsi, ret): nbBlocks kept *)
Definition ZSTD_errorFrameSizeInfo_spec : ident * funspec :=
  DECLARE _ZSTD_errorFrameSizeInfo
  WITH sh: share, p: val, nb: val, cs: val, db: val, ret: Z
  PRE [ tptr t_fsi, tulong ]
    PROP (writable_share sh; 0 <= ret <= Int64.max_unsigned)
    PARAMS (p; Vlong (Int64.repr ret))
    SEP (data_at sh t_fsi (nb, (cs, db)) p)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh t_fsi (nb, (Vlong (Int64.repr ret), Vlong (Int64.repr ZSTD_CONTENTSIZE_ERROR))) p).

(* ZSTD_findFrameSizeInfo(fsi, src, srcSize, ZSTD_f_zstd1) on the window s: compressedSize and
   decompressedBound as frame_size_info s says; on None, compressedSize is an error code
   (decompressedBound: anything; zstd leaves 0 for a bad skippable frame). *)
Definition ZSTD_findFrameSizeInfo_spec : ident * funspec :=
  DECLARE _ZSTD_findFrameSizeInfo
  WITH gv: globals, shf: share, pf: val, sh: share, base: val, N: Z, c: list val, off: Z, s: list Z
  PRE [ tptr t_fsi, tptr tvoid, tulong, tint ]
    PROP (writable_share shf; win_ok sh N c off (Zlength s) s)
    PARAMS (pf; offset_val off base; Vlong (Int64.repr (Zlength s)); Vint (Int.repr 0)) GLOBALS (gv)
    SEP (zstd_globals gv; data_at_ shf t_fsi pf; data_at sh (tarray tuchar N) c base)
  POST [ tvoid ]
    EX nb: val, EX cs: Z, EX db: Z,
    PROP (0 <= cs <= Int64.max_unsigned; 0 <= db <= Int64.max_unsigned;
          match frame_size_info s with
          | Some (k, b) => cs = k /\ db = b
          | None => is_error_code cs = true
          end)
    RETURN ()
    SEP (zstd_globals gv; data_at shf t_fsi (nb, (Vlong (Int64.repr cs), Vlong (Int64.repr db))) pf;
         data_at sh (tarray tuchar N) c base).

Definition H_specs : funspecs :=
  [ ZSTD_customMallocP_spec;
    ZSTD_customCallocP_spec;
    ZSTD_customFreeP_spec;
    ZSTD_customMem_copy_spec;
    ZSTD_startingInputLength_spec;
    ZSTD_isFrame_spec;
    ZSTD_isSkippableFrame_spec;
    ZSTD_frameHeaderSize_internal_spec;
    ZSTD_frameHeaderSize_spec;
    ZSTD_getFrameHeader_advanced_spec;
    ZSTD_getFrameHeader_spec;
    ZSTD_getFrameContentSize_spec;
    readSkippableFrameSize_spec;
    ZSTD_readSkippableFrame_spec;
    ZSTD_findDecompressedSize_spec;
    ZSTD_errorFrameSizeInfo_spec;
    ZSTD_findFrameSizeInfo_spec;
    ZSTD_findFrameCompressedSize_advanced_spec;
    ZSTD_findFrameCompressedSize_spec;
    ZSTD_decompressBound_spec;
    ZSTD_getDictID_fromDict_spec;
    ZSTD_getDictID_fromFrame_spec;
    ZSTD_DStreamOutSize_spec;
    ZSTD_getcBlockSize_spec ].

Definition H_G : funspecs := Gprog ++ H_specs.
