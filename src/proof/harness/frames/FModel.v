(* The frame writer of harness/frames.h in plain Coq: what new_frame and new_skippable write, as a function of
   the choices the harness makes (its nondet_* values).  Plain Coq, no VST.  The specifications of
   FSpecs.v say: new_frame returns nf_bytes d fcs did c and leaves nf_data d c in its data array, for some
   choices c with nf_ok (Zlength d) fcs max_window did c; new_skippable returns sk_bytes k u.  FFacts.v
   states what zstd's format model (model/Frame.v, model/Series.v) makes of these bytes.

   Byte strings are `list Z` (model/Bytes.v). *)
Require Export Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Xxh64.
Local Open Scope bool_scope.

Definition zb (b: bool) : Z := if b then 1 else 0.

(* ---------- the frame header ---------- *)

(* The header's choices, after new_frame's corrections: Frame_Content_Size_flag (0..3), Single_Segment_flag,
   the descriptor's bits 4 (Unused_bit) and 2 (Content_Checksum_flag) as written (0, 4, 16 or 20),
   Dictionary_ID_flag (0..3), the Window_Descriptor byte (written only without Single_Segment). *)
Record nf_header := {
  nh_fcs_flag : Z;
  nh_single : bool;
  nh_bits : Z;
  nh_did_flag : Z;
  nh_wd : Z }.

(* FCS_Field_Size and DID_Field_Size (RFC 8878 3.1.1.1.1) *)
Definition nh_fcs_size (h: nf_header) : Z :=
  if nh_fcs_flag h =? 0 then zb (nh_single h) else 2 ^ nh_fcs_flag h.
Definition nh_did_size (h: nf_header) : Z :=
  if nh_did_flag h =? 3 then 4 else nh_did_flag h.

Definition nh_checksum (h: nf_header) : bool := Z.testbit (nh_bits h) 2.

(* Window_Size: fcs with Single_Segment, else from the Window_Descriptor (Exponent bits 7-3, Mantissa 2-0);
   Block_Maximum_Size = min(Window_Size, 128 KiB) *)
Definition nh_window (fcs: Z) (h: nf_header) : Z :=
  if nh_single h then fcs
  else 2 ^ (10 + nh_wd h / 8) + 2 ^ (10 + nh_wd h / 8) / 8 * (nh_wd h mod 8).
Definition nh_max_block (fcs: Z) (h: nf_header) : Z := Z.min (nh_window fcs h) 131072.

(* Frame_Header_Descriptor *)
Definition nh_fhd (h: nf_header) : Z :=
  nh_fcs_flag h * 64 + zb (nh_single h) * 32 + nh_bits h + nh_did_flag h.

(* the Frame_Content_Size field's value (fcs - 256 in the 2-byte form) *)
Definition nh_fcs_value (fcs: Z) (h: nf_header) : Z := if nh_fcs_flag h =? 1 then fcs - 256 else fcs.

(* Magic_Number, Frame_Header_Descriptor, [Window_Descriptor], [Dictionary_ID], [Frame_Content_Size] *)
Definition nh_bytes (fcs did: Z) (h: nf_header) : list Z :=
  le_bytes 4 ZSTD_MAGICNUMBER ++ [nh_fhd h] ++ (if nh_single h then [] else [nh_wd h]) ++
  le_bytes (Z.to_nat (nh_did_size h)) did ++ le_bytes (Z.to_nat (nh_fcs_size h)) (nh_fcs_value fcs h).

(* the choices new_frame can make for content size fcs, window limit maxw, dictionary ID did *)
Definition nh_ok (fcs maxw did: Z) (h: nf_header) : Prop :=
  0 <= nh_fcs_flag h <= 3 /\
  (nh_fcs_flag h = 0 -> nh_single h = true -> fcs <= 255) /\
  (nh_fcs_flag h = 1 -> 256 <= fcs <= 65791) /\
  (nh_fcs_flag h = 2 -> fcs <= 4294967295) /\
  (nh_single h = true -> fcs <= maxw) /\
  In (nh_bits h) [0; 4; 16; 20] /\
  0 <= nh_did_flag h <= 3 /\
  (nh_did_flag h = 0 -> did = 0) /\
  (nh_did_flag h = 1 -> did <= 255) /\
  (nh_did_flag h = 2 -> did <= 65535) /\
  0 <= nh_wd h <= 255 /\
  nh_window fcs h <= maxw.

(* ---------- the blocks ---------- *)

(* One block: its Block_Size, Raw (false) or RLE (true), and the byte of an empty RLE block (any byte; an RLE
   block of size > 0 repeats the first byte of its part of the data). *)
Record nf_block := { nb_size : Z; nb_rle : bool; nb_byte : Z }.

(* The cut of n bytes of data, from offset done, into the blocks bl, under Block_Maximum_Size mb: each
   block takes 1 to min(rest, mb) bytes (1 when mb = 0) while data is left, 0 when none is; an RLE block
   only when mb > 0; the last block ends the data; only the last one may be empty. *)
Fixpoint nf_blocks_ok (mb n done: Z) (bl: list nf_block) : Prop :=
  match bl with
  | [] => False
  | b :: bl' =>
      (done = n -> nb_size b = 0) /\
      (done < n -> 1 <= nb_size b <= Z.max 1 (Z.min (n - done) mb)) /\
      (nb_rle b = true -> 0 < mb) /\
      0 <= nb_byte b < 256 /\
      match bl' with
      | [] => done + nb_size b = n
      | _ => 0 < nb_size b /\ nf_blocks_ok mb n (done + nb_size b) bl'
      end
  end.

Definition is_nil {A} (l: list A) : bool := match l with [] => true | _ => false end.

(* the Block_Header: Last_Block, Block_Type (0 Raw, 1 RLE), Block_Size *)
Definition nb_header (last: bool) (b: nf_block) : list Z :=
  le_bytes 3 (zb last + 2 * zb (nb_rle b) + 8 * nb_size b).

(* the bytes of the blocks bl over data d from offset done *)
Fixpoint nf_blocks_bytes (d: list Z) (done: Z) (bl: list nf_block) : list Z :=
  match bl with
  | [] => []
  | b :: bl' =>
      nb_header (is_nil bl') b ++
      (if nb_rle b then [if nb_size b =? 0 then nb_byte b else byte_at d done]
       else slice d done (nb_size b)) ++
      nf_blocks_bytes d (done + nb_size b) bl'
  end.

(* the data after the blocks bl: an RLE block makes its part one byte repeated *)
Fixpoint nf_content (d: list Z) (done: Z) (bl: list nf_block) : list Z :=
  match bl with
  | [] => []
  | b :: bl' =>
      (if nb_rle b then repeat (byte_at d done) (Z.to_nat (nb_size b)) else slice d done (nb_size b)) ++
      nf_content d (done + nb_size b) bl'
  end.

(* ---------- the frame ---------- *)

Record nf_choice := { nc_hdr : nf_header; nc_blocks : list nf_block }.

Definition nf_ok (n fcs maxw did: Z) (c: nf_choice) : Prop :=
  nh_ok fcs maxw did (nc_hdr c) /\ nf_blocks_ok (nh_max_block fcs (nc_hdr c)) n 0 (nc_blocks c).

(* the data new_frame leaves in its array *)
Definition nf_data (d: list Z) (c: nf_choice) : list Z := nf_content d 0 (nc_blocks c).

(* Content_Checksum: the low 4 bytes of XXH64(data, seed 0), little-endian *)
Definition nf_checksum (d: list Z) (c: nf_choice) : list Z :=
  if nh_checksum (nc_hdr c) then le_bytes 4 (xxh64 (nf_data d c) 0) else [].

(* the frame new_frame returns *)
Definition nf_bytes (d: list Z) (fcs did: Z) (c: nf_choice) : list Z :=
  nh_bytes fcs did (nc_hdr c) ++ nf_blocks_bytes d 0 (nc_blocks c) ++ nf_checksum d c.

(* ---------- skippable frames ---------- *)

(* new_skippable: Magic_Number 0x184D2A50 + k (k < 16), Frame_Size = |u|, User_Data u *)
Definition sk_bytes (k: Z) (u: list Z) : list Z :=
  le_bytes 4 (ZSTD_MAGIC_SKIPPABLE_START + k) ++ le_bytes 4 (Zlength u) ++ u.
