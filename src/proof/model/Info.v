(* The format model: the frame-inspection functions of zstd.h that Frame.v does not cover, exact on ANY
   bytes (lib/decompress/zstd_decompress.c).  Plain Coq, no VST.  An error result is `None` (which error
   code is not specified). *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame.
Local Open Scope bool_scope.

(* ZSTD_frameHeaderSize (= ZSTD_frameHeaderSize_internal, format zstd1) *)
Definition frame_header_size (s: list Z) : option Z :=
  if Zlength s <? ZSTD_FRAMEHEADERSIZE_PREFIX then None else Some (fhd_header_size (byte_at s 4)).

(* ZSTD_isFrame, ZSTD_isSkippableFrame *)
Definition is_frame (s: list Z) : Z :=
  if Zlength s <? 4 then 0 else
  let m := le_field s 0 4 in
  if (m =? ZSTD_MAGICNUMBER) || is_skippable_magic m then 1 else 0.

Definition is_skippable_frame (s: list Z) : Z :=
  if Zlength s <? 4 then 0 else if is_skippable_magic (le_field s 0 4) then 1 else 0.

(* ZSTD_readSkippableFrame(dst, cap, &variant, s): Some (user data, magic variant), or None (an error) *)
Definition read_skippable (s: list Z) (cap: Z) : option (list Z * Z) :=
  if Zlength s <? ZSTD_SKIPPABLEHEADERSIZE then None else
  let m := le_field s 0 4 in
  if negb (is_skippable_magic m) then None else
  match skippable_frame_size s with
  | None => None
  | Some k =>
      if k - ZSTD_SKIPPABLEHEADERSIZE >? cap then None else
      Some (slice s ZSTD_SKIPPABLEHEADERSIZE (k - ZSTD_SKIPPABLEHEADERSIZE), m - ZSTD_MAGIC_SKIPPABLE_START)
  end.

(* ZSTD_getDictID_fromFrame *)
Definition dict_id_from_frame (s: list Z) : Z :=
  match get_frame_header s with
  | FH_ok h => if fh_frameType h =? 1 then 0 else fh_dictID h
  | _ => 0
  end.

(* ZSTD_findFrameSizeInfo: the frame's size and its decompressed bound, or None (an error) *)
Definition frame_size_info (s: list Z) : option (Z * Z) :=
  if (Zlength s >=? ZSTD_SKIPPABLEHEADERSIZE) && is_skippable_magic (le_field s 0 4) then
    match skippable_frame_size s with Some k => Some (k, 0) | None => None end
  else
  match get_frame_header s with
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

(* ZSTD_decompressBound *)
Fixpoint bound_loop (fuel: nat) (s: list Z) (acc: Z) : Z :=
  match fuel with
  | O => ZSTD_CONTENTSIZE_ERROR
  | S f =>
      if Zlength s =? 0 then acc else
      match frame_size_info s with
      | None => ZSTD_CONTENTSIZE_ERROR
      | Some (k, b) =>
          if b =? ZSTD_CONTENTSIZE_ERROR then ZSTD_CONTENTSIZE_ERROR
          else bound_loop f (skipn (Z.to_nat k) s) ((acc + b) mod 2 ^ 64)
      end
  end.

Definition decompress_bound (s: list Z) : Z := bound_loop (S (length s)) s 0.

(* frame_compressed_size of Frame.v is the first component of frame_size_info *)
Example info_empty_frame :
  frame_size_info [40; 181; 47; 253; 32; 0; 1; 0; 0] = Some (9, 0) /\
  decompress_bound [40; 181; 47; 253; 32; 0; 1; 0; 0] = 0 /\
  frame_header_size [40; 181; 47; 253; 32; 0; 1; 0; 0] = Some 6.
Proof. vm_compute. auto. Qed.
