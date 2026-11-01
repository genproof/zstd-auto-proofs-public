(* What the writer (harness/writer.h) guarantees about the data it writes, in terms of the format model:
   the facts the harness mains need.  Plain Coq.  The writer's specifications
   (w_series, w_dict) state these facts of the series / dictionary they leave in memory.

   A series: its bytes, its content, and per frame the fields of winfo_t. *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Info Zstd.proof.model.Block Zstd.proof.model.Series.
Local Open Scope bool_scope.

Record winfo := {
  wi_skippable : bool; wi_variant : Z;
  wi_start : Z; wi_size : Z; wi_cstart : Z; wi_csize : Z;
  wi_fcs_present : bool; wi_fcs : Z;
  wi_did_size : Z; wi_did : Z;
  wi_single : bool; wi_window : Z; wi_window_log : Z;
  wi_checksum : bool; wi_blocks : Z; wi_skip_n : Z; wi_hsize : Z; wi_uses_dict : bool }.

Record wseries := { ws_bytes : list Z; ws_content : list Z; ws_frames : list winfo }.

(* a Zstandard frame whose window is beyond zstd's range (zlimits.h within_oneshot) *)
Definition wi_big (f: winfo) : bool :=
  negb (wi_skippable f) && negb (wi_single f) && (wi_window_log f >? ZSTD_WINDOWLOG_MAX).

(* rejected at its header by a decoder with window limit wl *)
Definition wi_rejected (wl: Z) (f: winfo) : bool :=
  negb (wi_skippable f) && (wi_big f || (wi_window f >? wl)).

Definition wi_end (f: winfo) : Z := wi_start f + wi_size f.

(* the content of frame f *)
Definition wi_content (ws: wseries) (f: winfo) : list Z :=
  slice (ws_content ws) (wi_cstart f) (wi_csize f).

(* the frame's bytes *)
Definition wi_bytes (ws: wseries) (f: winfo) : list Z :=
  slice (ws_bytes ws) (wi_start f) (wi_size f).

(* ---------- the corruptions of harness/detect.c ---------- *)

(* xor the 4 bytes at position pos with the little-endian bytes of x *)
Definition xor4 (b: list Z) (pos x: Z) : list Z :=
  map (fun i => let v := byte_at b (Z.of_nat i) in
                if (pos <=? Z.of_nat i) && (Z.of_nat i <? pos + 4)
                then Z.lxor v (Z.land (Z.shiftr x (8 * (Z.of_nat i - pos))) 255) else v)
      (seq 0 (length b)).

(* set bit 3 of the byte at position pos *)
Definition set_bit3 (b: list Z) (pos: Z) : list Z :=
  map (fun i => let v := byte_at b (Z.of_nat i) in if Z.of_nat i =? pos then Z.lor v 8 else v)
      (seq 0 (length b)).

(* ---------- the facts ---------- *)

(* the frames tile the bytes and the content, in order *)
Fixpoint tiles (fs: list winfo) (off coff: Z) (n cn: Z) : Prop :=
  match fs with
  | nil => off = n /\ coff = cn
  | f :: fs' => wi_start f = off /\ wi_cstart f = coff /\ 0 < wi_size f /\ 0 <= wi_csize f /\
                (wi_skippable f = true -> wi_csize f = 0) /\
                tiles fs' (off + wi_size f) (coff + wi_csize f) n cn
  end.

(* the header ZSTD_getFrameHeader reports for a frame (Frame.frame_header) *)
Definition wi_header (f: winfo) : frame_header :=
  if wi_skippable f then
    {| fh_contentSize := wi_skip_n f; fh_windowSize := 0; fh_blockSizeMax := 0; fh_frameType := 1;
       fh_headerSize := ZSTD_SKIPPABLEHEADERSIZE; fh_dictID := wi_variant f; fh_checksumFlag := 0 |}
  else
    {| fh_contentSize := if wi_fcs_present f then wi_fcs f else ZSTD_CONTENTSIZE_UNKNOWN;
       fh_windowSize := wi_window f; fh_blockSizeMax := Z.min (wi_window f) ZSTD_BLOCKSIZE_MAX;
       fh_frameType := 0; fh_headerSize := wi_hsize f; fh_dictID := wi_did f;
       fh_checksumFlag := if wi_checksum f then 1 else 0 |}.

(* The facts of one frame f of the series ws written for the dictionary dm. *)
Definition frame_facts (dm: dict_model) (ws: wseries) (f: winfo) : Prop :=
  let s := skipn (Z.to_nat (wi_start f)) (ws_bytes ws) in
  let fb := wi_bytes ws f in
  (* inspection, on the series' bytes from the frame's start *)
  is_frame s = 1 /\
  is_skippable_frame s = (if wi_skippable f then 1 else 0) /\
  frame_compressed_size s = (if wi_big f then None else Some (wi_size f)) /\
  get_frame_header s = (if wi_big f then FH_err else FH_ok (wi_header f)) /\
  frame_content_size s = (if wi_skippable f then 0 else if wi_big f then ZSTD_CONTENTSIZE_ERROR
                          else if wi_fcs_present f then wi_fcs f else ZSTD_CONTENTSIZE_UNKNOWN) /\
  dict_id_from_frame s = (if wi_skippable f || wi_big f then 0 else wi_did f) /\
  (wi_skippable f = false -> frame_header_size s = Some (wi_hsize f)) /\
  (wi_skippable f = true ->
     wi_size f = ZSTD_SKIPPABLEHEADERSIZE + wi_skip_n f /\
     Zlength fb >= ZSTD_SKIPPABLEHEADERSIZE /\ is_skippable_magic (le_field fb 0 4) = true /\
     (forall t, skippable_frame_size (fb ++ t) = Some (wi_size f)) /\
     (forall cap, read_skippable s cap =
        if cap >=? wi_skip_n f then Some (slice fb ZSTD_SKIPPABLEHEADERSIZE (wi_skip_n f), wi_variant f)
        else None)) /\
  (* decoding, the frame followed by anything *)
  (wi_skippable f = false ->
     (forall wl t, decode_frame dm wl (fb ++ t) =
        if wi_rejected wl f then FDetHdr else FOk (wi_content ws f) (wi_size f)) /\
     (forall wl t, decode_frame dm wl (set_bit3 fb 4 ++ t) = FDetHdr) /\
     (wi_checksum f = true -> forall wl t x, 0 < x < 2 ^ 32 -> wi_rejected wl f = false ->
        decode_frame dm wl (xor4 fb (wi_size f - 4) x ++ t) = FDetCk)).

(* ZSTD_findDecompressedSize and ZSTD_decompressBound of the series *)
Fixpoint expected_fds (fs: list winfo) (acc: Z) : Z :=
  match fs with
  | nil => acc
  | f :: fs' =>
      if wi_skippable f then expected_fds fs' acc
      else if wi_big f then ZSTD_CONTENTSIZE_ERROR
      else if negb (wi_fcs_present f) then ZSTD_CONTENTSIZE_UNKNOWN
      else expected_fds fs' (acc + wi_fcs f)
  end.

Fixpoint expected_bound (fs: list winfo) (acc: Z) : Z :=
  match fs with
  | nil => acc
  | f :: fs' =>
      if wi_skippable f then expected_bound fs' acc
      else if wi_big f then ZSTD_CONTENTSIZE_ERROR
      else expected_bound fs' (acc + (if wi_fcs_present f then wi_fcs f
                                      else wi_blocks f * Z.min (wi_window f) ZSTD_BLOCKSIZE_MAX))
  end.

Definition series_facts (dm: dict_model) (ws: wseries) : Prop :=
  bytes_ok (ws_bytes ws) /\ bytes_ok (ws_content ws) /\
  Zlength (ws_bytes ws) <= 2 ^ 19 /\ Zlength (ws_content ws) <= 2 ^ 18 /\
  (1 <= length (ws_frames ws) <= 4)%nat /\
  tiles (ws_frames ws) 0 0 (Zlength (ws_bytes ws)) (Zlength (ws_content ws)) /\
  Forall (frame_facts dm ws) (ws_frames ws) /\
  Forall (fun f => wi_skippable f = false -> wi_fcs_present f = true -> wi_fcs f = wi_csize f)
         (ws_frames ws) /\
  find_decompressed_size (ws_bytes ws) = expected_fds (ws_frames ws) 0 /\
  decompress_bound (ws_bytes ws) = expected_bound (ws_frames ws) 0.

(* ---------- dictionaries (w_dict) ---------- *)

Record wdict := { wd_bytes : list Z; wd_formatted : bool; wd_id : Z; wd_content : list Z }.

(* the dictionary model frames are written for *)
Definition wd_model (d: wdict) : dict_model :=
  match dict_auto (wd_bytes d) with Some dm => dm | None => no_dict end.

Definition dict_facts (d: wdict) : Prop :=
  bytes_ok (wd_bytes d) /\ 8 <= Zlength (wd_bytes d) <= 2 ^ 12 + 2048 /\
  dict_auto (wd_bytes d) <> None /\
  dm_content (wd_model d) = wd_content d /\ dm_id (wd_model d) = wd_id d /\
  dict_id_of (wd_bytes d) = wd_id d /\
  (wd_formatted d = false -> wd_model d = dict_raw (wd_bytes d) /\ wd_id d = 0).
