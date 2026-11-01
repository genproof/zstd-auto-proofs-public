(* Subtree H of the decoder, API v3: the specifications of the 25
   functions of ids_H3, in that order.  As v2's HSpecs.H_specs, with the format argument f in {0, 1} for
   startingInputLength, frameHeaderSize_internal, getFrameHeader_advanced, findFrameCompressedSize_advanced
   (DecIface3 H_exports3) and the internal findFrameSizeInfo (spec3 below), plus ZSTD_getDecompressedSize
   (Spec_api6).  Every body of H is proved against H3_G = Gprog ++ H3_specs. *)
Require Export Zstd.proof.dec.v3.DecSubtrees3.
Require Export Zstd.proof.dec.H.HSpecs.
Local Open Scope logic.

(* ZSTD_findFrameSizeInfo(fsi, src, n, format): Info.frame_size_info for zstd1; magicless: no skippable frames,
   the header of get_frame_header_m true *)
Definition frame_size_info_m (mg: bool) (s: list Z) : option (Z * Z) :=
  if negb mg then frame_size_info s else
  match get_frame_header_m true s with
  | FH_ok h =>
      let rest := skipn (Z.to_nat (fh_headerSize h)) s in
      match blocks_size (length rest) rest with
      | None => None
      | Some (k, nb) =>
          let sz := fh_headerSize h + k in
          let bound := if fh_contentSize h =? ZSTD_CONTENTSIZE_UNKNOWN then (nb * fh_blockSizeMax h) mod 2 ^ 64
                       else fh_contentSize h in
          if fh_checksumFlag h =? 1 then
            (if Zlength s - sz <? 4 then None else Some (sz + 4, bound))
          else Some (sz, bound)
      end
  | _ => None
  end.

Lemma frame_size_info_zstd1 (s: list Z) : frame_size_info_m false s = frame_size_info s.
Proof. reflexivity. Qed.

Lemma frame_compressed_size_info_m (mg: bool) (s: list Z) :
  frame_compressed_size_m mg s = option_map fst (frame_size_info_m mg s).
Proof.
  destruct mg.
  - unfold frame_compressed_size_m, frame_size_info_m. simpl negb. cbv iota.
    destruct (get_frame_header_m true s) as [h| |]; try reflexivity.
    destruct (blocks_size _ _) as [[k nb]|]; [| reflexivity].
    destruct (fh_checksumFlag h =? 1); [| reflexivity].
    destruct (Zlength s - _ <? 4); reflexivity.
  - unfold frame_compressed_size_m, frame_size_info_m. simpl negb. cbv iota.
    unfold frame_compressed_size, frame_size_info.
    destruct (andb _ _); [destruct (skippable_frame_size s); reflexivity |].
    destruct (get_frame_header s) as [h| |]; try reflexivity.
    destruct (blocks_size _ _) as [[k nb]|]; [| reflexivity].
    destruct (fh_checksumFlag h =? 1); [| reflexivity].
    destruct (Zlength s - _ <? 4); reflexivity.
Qed.

Definition ZSTD_findFrameSizeInfo_spec3 : ident * funspec :=
  DECLARE _ZSTD_findFrameSizeInfo
  WITH gv: globals, shf: share, pf: val, sh: share, base: val, N: Z, c: list val, off: Z, s: list Z, f: Z
  PRE [ tptr t_fsi, tptr tvoid, tulong, tint ]
    PROP (writable_share shf; win_ok sh N c off (Zlength s) s; f = 0 \/ f = 1)
    PARAMS (pf; offset_val off base; Vlong (Int64.repr (Zlength s)); Vint (Int.repr f)) GLOBALS (gv)
    SEP (zstd_globals gv; data_at_ shf t_fsi pf; data_at sh (tarray tuchar N) c base)
  POST [ tvoid ]
    EX nb: val, EX cs: Z, EX db: Z,
    PROP (0 <= cs <= Int64.max_unsigned; 0 <= db <= Int64.max_unsigned;
          match frame_size_info_m (fmt_mg f) s with
          | Some (k, b) => cs = k /\ db = b
          | None => is_error_code cs = true
          end)
    RETURN ()
    SEP (zstd_globals gv; data_at shf t_fsi (nb, (Vlong (Int64.repr cs), Vlong (Int64.repr db))) pf;
         data_at sh (tarray tuchar N) c base).

(* v2's H_specs with the v3 entries *)
Definition H3_core : funspecs :=
  [ ZSTD_customMallocP_spec;
    ZSTD_customCallocP_spec;
    ZSTD_customFreeP_spec;
    ZSTD_customMem_copy_spec;
    ZSTD_startingInputLength_spec3;
    ZSTD_isFrame_spec;
    ZSTD_isSkippableFrame_spec;
    ZSTD_frameHeaderSize_internal_spec3;
    ZSTD_frameHeaderSize_spec;
    ZSTD_getFrameHeader_advanced_spec3;
    ZSTD_getFrameHeader_spec;
    ZSTD_getFrameContentSize_spec;
    readSkippableFrameSize_spec;
    ZSTD_readSkippableFrame_spec;
    ZSTD_findDecompressedSize_spec;
    ZSTD_errorFrameSizeInfo_spec;
    ZSTD_findFrameSizeInfo_spec3;
    ZSTD_findFrameCompressedSize_advanced_spec3;
    ZSTD_findFrameCompressedSize_spec;
    ZSTD_decompressBound_spec;
    ZSTD_getDictID_fromDict_spec;
    ZSTD_getDictID_fromFrame_spec;
    ZSTD_DStreamOutSize_spec;
    ZSTD_getcBlockSize_spec ].

Definition H3_specs : funspecs := H3_core ++ [ ZSTD_getDecompressedSize_aspec ].

Definition H3_G : funspecs := Gprog ++ H3_specs.

Lemma H3_names : map fst H3_specs = ids_H3.
Proof. reflexivity. Qed.
