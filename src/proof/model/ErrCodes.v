(* The error codes of one-shot decoding.  Plain Coq.

   Two facts of ZSTD_decompress / ZSTD_decompressDCtx are stated against the format model here:
   - a series whose walk ends at a Zstandard frame refused by its Content_Checksum (Params.walk_m's tail TDetCk)
     is refused with ZSTD_error_checksum_wrong when the output has room for everything zstd decodes before it
     compares the checksum: the contents of the frames before, and the refused frame's own content
     (series_ck_m);
   - a series the model decodes (SOk c) whose Zstandard frames have only Raw and RLE blocks is refused with
     ZSTD_error_dstSize_tooSmall when the output is smaller than c (series_rr_m).  The decoder reports the same
     code for compressed blocks, but the block specifications do not carry it (block_ok gives only an error).
   The relations follow Params.walk_m step by step (skippable frames, the dictionary selection), without fuel. *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Block Zstd.proof.model.Series.
Require Import Zstd.proof.model.StreamModel Zstd.proof.model.Params.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

(* zstd_errors.h *)
Definition ZSTD_error_checksum_wrong : Z := 22.

(* ---------- one frame ---------- *)

(* The content of the Zstandard frame at the start of s, as decode_frame_m decodes its blocks: what zstd has
   written when it reaches the frame's Content_Checksum (None: the header does not parse or the model does not
   decode the blocks) *)
Definition frame_out_m (md: dmode) (dm: dict_model) (s: list Z) : option (list Z) :=
  match get_frame_header_m (md_magicless md) s with
  | FH_ok h =>
      let rest := skipn (Z.to_nat (fh_headerSize h)) s in
      match (if md_dwin md then decode_blocks_w else decode_blocks)
              (length rest) (dm_state dm) (dm_content dm) rest nil (Z.min (fh_blockSizeMax h) (md_bmax md))
              (fh_windowSize h) with
      | Some (out, _) => Some out
      | None => None
      end
  | _ => None
  end.

(* The blocks from the block header at the start of t up to the last block are Raw (0) or RLE (1) blocks *)
Inductive blocks_rr : list Z -> Prop :=
  | brr_last: forall t c,
      cblock_size t = Some c -> bp_type (block_props_of t) < 2 -> bp_last (block_props_of t) = 1 ->
      blocks_rr t
  | brr_more: forall t c,
      cblock_size t = Some c -> bp_type (block_props_of t) < 2 -> bp_last (block_props_of t) <> 1 ->
      blocks_rr (skipn (Z.to_nat (ZSTD_blockHeaderSize + c)) t) -> blocks_rr t.

(* The Zstandard frame at the start of s has only Raw and RLE blocks *)
Definition frame_rr_m (md: dmode) (s: list Z) : Prop :=
  exists h, get_frame_header_m (md_magicless md) s = FH_ok h /\
    blocks_rr (skipn (Z.to_nat (fh_headerSize h)) s).

(* ---------- series ---------- *)

(* the current dictionary after a skippable frame at the start of s (walk_m: with md_dwin, the frame's magic
   variant selects a dictionary) *)
Definition skip_dict (md: dmode) (sel: Z -> option dict_model) (cur: option dict_model) (s: list Z)
    : option dict_model :=
  if md_dwin md then match sel (Z.land (le_field s 0 4) 15) with Some d => Some d | None => cur end else cur.

(* series_ck_m md sel cur wlim s c: walk_m on s from the current dictionary cur ends at a Zstandard frame
   refused by its Content_Checksum (FDetCk), after Zstandard frames it decodes and skippable frames; c is the
   contents of the frames before it followed by its own content (frame_out_m) *)
Inductive series_ck_m (md: dmode) (sel: Z -> option dict_model) (wlim: Z)
    : option dict_model -> list Z -> list Z -> Prop :=
  | sck_skip: forall cur s k c,
      starting_len (md_magicless md) <= Zlength s ->
      negb (md_magicless md) && is_skippable_magic (le_field s 0 4) = true ->
      skippable_frame_size s = Some k ->
      series_ck_m md sel wlim (skip_dict md sel cur s) (skipn (Z.to_nat k) s) c ->
      series_ck_m md sel wlim cur s c
  | sck_frame: forall cur s d c0 k c,
      starting_len (md_magicless md) <= Zlength s ->
      negb (md_magicless md) && is_skippable_magic (le_field s 0 4) = false ->
      frame_dict (md_magicless md) sel cur s = Some d ->
      decode_frame_m md d wlim s = FOk c0 k ->
      series_ck_m md sel wlim (Some d) (skipn (Z.to_nat k) s) c ->
      series_ck_m md sel wlim cur s (c0 ++ c)
  | sck_last: forall cur s d c,
      starting_len (md_magicless md) <= Zlength s ->
      negb (md_magicless md) && is_skippable_magic (le_field s 0 4) = false ->
      frame_dict (md_magicless md) sel cur s = Some d ->
      decode_frame_m md d wlim s = FDetCk ->
      frame_out_m md d s = Some c ->
      series_ck_m md sel wlim cur s c.

(* series_rr_m md sel cur wlim s c: walk_m decodes all of s to c (decode_series_m = SOk c), and every Zstandard
   frame of s has only Raw and RLE blocks *)
Inductive series_rr_m (md: dmode) (sel: Z -> option dict_model) (wlim: Z)
    : option dict_model -> list Z -> list Z -> Prop :=
  | srr_nil: forall cur, series_rr_m md sel wlim cur nil nil
  | srr_skip: forall cur s k c,
      starting_len (md_magicless md) <= Zlength s ->
      negb (md_magicless md) && is_skippable_magic (le_field s 0 4) = true ->
      skippable_frame_size s = Some k ->
      series_rr_m md sel wlim (skip_dict md sel cur s) (skipn (Z.to_nat k) s) c ->
      series_rr_m md sel wlim cur s c
  | srr_frame: forall cur s d c0 k c,
      starting_len (md_magicless md) <= Zlength s ->
      negb (md_magicless md) && is_skippable_magic (le_field s 0 4) = false ->
      frame_dict (md_magicless md) sel cur s = Some d ->
      decode_frame_m md d wlim s = FOk c0 k ->
      frame_rr_m md s ->
      series_rr_m md sel wlim (Some d) (skipn (Z.to_nat k) s) c ->
      series_rr_m md sel wlim cur s (c0 ++ c).

(* ---------- sanity checks ---------- *)

(* Series.decode_raw_abc's frame: one raw block "abc", decoded to "abc" *)
Example rr_raw_abc :
  series_rr_m md_dflt sel_none no_wlim (Some no_dict) [40; 181; 47; 253; 32; 3; 25; 0; 0; 97; 98; 99] [97; 98; 99].
Proof.
  rewrite <- (app_nil_r [97; 98; 99]).
  eapply srr_frame; [vm_compute; discriminate | reflexivity | reflexivity | vm_compute; reflexivity | | ].
  - eexists. split; [vm_compute; reflexivity |]. apply (brr_last _ 3); vm_compute; reflexivity.
  - vm_compute. apply srr_nil.
Qed.

(* the same frame with a Content_Checksum (FHD 0x24) of 0: refused by its checksum, after "abc" *)
Example ck_raw_abc :
  series_ck_m md_dflt sel_none no_wlim (Some no_dict) [40; 181; 47; 253; 36; 3; 25; 0; 0; 97; 98; 99; 0; 0; 0; 0]
    [97; 98; 99].
Proof. eapply sck_last; [vm_compute; discriminate | reflexivity | reflexivity | vm_compute | vm_compute]; reflexivity. Qed.
