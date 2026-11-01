(* The frame-inspection models of model/Info.v and model/Frame.v under ZSTD_d_format (API v3).
   Plain Coq.
   - frame_header_size_m mg: ZSTD_frameHeaderSize_internal(src, n, format);
   - frame_compressed_size_m mg: ZSTD_findFrameCompressedSize_advanced(src, n, format) (no skippable
     frames in the magicless format; the header is get_frame_header_m's).
   With mg = false they are the zstd1 functions (lemmas *_zstd1, by computation). *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Info Zstd.proof.model.Params.
Local Open Scope bool_scope.

Definition frame_header_size_m (mg: bool) (s: list Z) : option Z :=
  if negb mg then frame_header_size s else
  if Zlength s <? 1 then None else Some (fhd_header_size (byte_at s 0) - 4).

Definition frame_compressed_size_m (mg: bool) (s: list Z) : option Z :=
  if negb mg then frame_compressed_size s else
  match get_frame_header_m true s with
  | FH_ok h =>
      let rest := skipn (Z.to_nat (fh_headerSize h)) s in
      match blocks_size (length rest) rest with
      | None => None
      | Some (k, _) =>
          let sz := fh_headerSize h + k in
          if fh_checksumFlag h =? 1 then
            (if Zlength s - sz <? 4 then None else Some (sz + 4))
          else Some sz
      end
  | _ => None
  end.

Lemma frame_header_size_zstd1 (s: list Z) : frame_header_size_m false s = frame_header_size s.
Proof. reflexivity. Qed.

Lemma frame_compressed_size_zstd1 (s: list Z) : frame_compressed_size_m false s = frame_compressed_size s.
Proof. reflexivity. Qed.

Lemma get_frame_header_zstd1 (s: list Z) : get_frame_header_m false s = get_frame_header s.
Proof. reflexivity. Qed.

Lemma starting_len_zstd1 : starting_len false = ZSTD_FRAMEHEADERSIZE_PREFIX.
Proof. reflexivity. Qed.

Example frame_compressed_size_m_abc :
  frame_compressed_size_m true [32; 3; 25; 0; 0; 97; 98; 99] = Some 8 /\
  frame_compressed_size_m false [40; 181; 47; 253; 32; 3; 25; 0; 0; 97; 98; 99] = Some 12 /\
  frame_header_size_m true [32; 3; 25; 0; 0; 97; 98; 99] = Some 2.
Proof. vm_compute. auto. Qed.
