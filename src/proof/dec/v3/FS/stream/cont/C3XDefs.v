(* ZSTD_decompressContinue exactly (S3Specs.cont_exact): the model's call cut where the C cuts it.  The body runs
   ZSTD_checkContinuity first, then the switch on the stage; the proof of each case states the model's outcome from
   the state after checkContinuity (cont_exact1 below), and the body's proof assembles cont_exact from it
   (d_continue_body: the sanity check, then d_continuity, then d_body).  The block stages decode the block first
   (d_bres: ZSTD_copyRawBlock / ZSTD_setRleBlock / ZSTD_decompressBlock_internal), then check its size and update
   the frame state (d_body). *)
Require Import Zstd.proof.dec.v3.FS.stream.S3Specs.
Require Import Zstd.proof.dec.v3.FS.stream.cont.C3XModel.
Require Import Zstd.proof.model.ExStream.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

(* the block of a block stage, decoded at dst with capacity cap from the unit src of n bytes: the block decoder's
   new state, the ring's cells, the block's size and the input still expected of it (a raw block in pieces) *)
Definition d_bres (fh: frame_header) (d: dstate XS) (mem: list Z) (dst cap: Z) (src: list Z) (n: Z)
    : option (XS * list Z * Z * Z) :=
  let bsm := fh_blockSizeMax fh in
  if d_btype XS d =? 2 then
    let '(ps, ds, de) := d_hist XS d dst in
    match Exact.xblock (d_ent XS d) mem ps dst ds de src bsm cap true with
    | Some (e, mem', sz) => Some (e, mem', sz, 0)
    | None => None
    end
  else if d_btype XS d =? 0 then
    (if n >? cap then None else Some (d_ent XS d, mem_write mem dst src, n, d_expected XS d - n))
  else if d_btype XS d =? 1 then
    (if d_rle XS d >? cap then None
     else Some (d_ent XS d, mem_write mem dst (repeat (byte_at src 0) (Z.to_nat (d_rle XS d))), d_rle XS d, 0))
  else None.

(* ZSTD_decompressContinue after the sanity check and ZSTD_checkContinuity (ExStream.d_continue's body) *)
Definition d_body (fh: frame_header) (d: dstate XS) (mem: list Z) (dst cap: Z) (src: list Z) (n: Z)
    : option (dstate XS * list Z * Z) :=
  let bsm := fh_blockSizeMax fh in
  if d_stage XS d =? DS_decodeBlockHeader then
    match cblock_size src with
    | None => None
    | Some c =>
        if c >? bsm then None else
        let bp := block_props_of src in
        let d1 := mkD XS (d_stage XS d) c (bp_type bp) (bp_origSize bp) (d_out XS d) (d_check XS d) (d_ent XS d)
                      (d_prev XS d) (d_pfx XS d) (d_ds XS d) (d_de XS d) in
        if c >? 0 then
          Some (d_goto XS d1 (if bp_last bp =? 1 then DS_decompressLastBlock else DS_decompressBlock) c, mem, 0)
        else if bp_last bp =? 1 then
          match d_end_frame XS fh d1 with Some d2 => Some (d2, mem, 0) | None => None end
        else Some (d_goto XS d1 DS_decodeBlockHeader ZSTD_blockHeaderSize, mem, 0)
    end
  else if (d_stage XS d =? DS_decompressBlock) || (d_stage XS d =? DS_decompressLastBlock) then
    match d_bres fh d mem dst cap src n with
    | None => None
    | Some (e, mem', sz, ex) =>
        if sz >? bsm then None else
        let d1 := mkD XS (d_stage XS d) ex (d_btype XS d) (d_rle XS d) (d_out XS d ++ slice mem' dst sz) (d_check XS d) e
                      (Some (dst + sz)) (d_pfx XS d) (d_ds XS d) (d_de XS d) in
        if ex >? 0 then Some (d1, mem', sz)
        else if d_stage XS d =? DS_decompressLastBlock then
          match d_end_frame XS fh d1 with Some d2 => Some (d2, mem', sz) | None => None end
        else Some (d_goto XS d1 DS_decodeBlockHeader ZSTD_blockHeaderSize, mem', sz)
    end
  else if d_stage XS d =? DS_checkChecksum then
    if d_check XS d && negb (le_field src 0 4 =? xxh64 (d_out XS d) 0 mod 2 ^ 32) then None
    else Some (d_goto XS d DS_getFrameHeaderSize 0, mem, 0)
  else if d_stage XS d =? DS_skipFrame then
    Some (d_goto XS d DS_getFrameHeaderSize 0, mem, 0)
  else None.

Lemma d_continue_body fh d0 mem dst cap src n :
  d_continue XS Exact.xblock fh d0 mem dst cap src n =
  if negb (n =? d_next_in XS d0 n) then None else d_body fh (d_continuity XS d0 dst cap) mem dst cap src n.
Proof. reflexivity. Qed.

(* the exact claim on an outcome *)
Definition cx_match (res: option (dstate XS * list Z * Z)) (fh: frame_header) (ob: val) (r: Z) (oc': list val)
    (fs': fstate) (tabs': option tstate) : Prop :=
  match res with
  | None => is_error_code r = true
  | Some (d', mem', r0) =>
      r = r0 /\ oc' = zbytes mem' /\ exists ts', tabs' = Some ts' /\ drel fh d' ob fs' ts'
  end.

(* the room-less compressed block reads no extDict (cont_exact's premise) *)
Definition noext0 (d: dstate XS) (cap: Z) : Prop :=
  (d_stage XS d = DS_decompressBlock \/ d_stage XS d = DS_decompressLastBlock) ->
  d_btype XS d = 2 -> cap = 0 -> d_de XS d = None.

(* the exact claim of a case of the switch, from the frame fields fs1 after ZSTD_checkContinuity *)
Definition cont_exact1 (fs1: fstate) (ts: tstate) (o: outarr) (u: list Z) (n r: Z) (oc': list val)
    (fs': fstate) (tabs': option tstate) : Prop :=
  forall fh d mem, drel fh d (oa_base o) fs1 ts -> oa_c o = zbytes mem -> bytes_ok mem -> noext0 d (oa_cap o) ->
    cx_match (d_body fh d mem (oa_d o) (oa_cap o) u n) fh (oa_base o) r oc' fs' tabs'.

(* the block's part of it (the block stages): what the decoders return, before the size check; a success fits the
   room, keeps the ring's length and bytes, and leaves a well-formed Huffman table *)
Definition bres_exact (fs1: fstate) (ts: tstate) (o: outarr) (u: list Z) (n r: Z) (oc': list val)
    (tso: option tstate) (e': Z) : Prop :=
  forall fh d mem, drel fh d (oa_base o) fs1 ts -> oa_c o = zbytes mem -> bytes_ok mem -> noext0 d (oa_cap o) ->
    match d_bres fh d mem (oa_d o) (oa_cap o) u n with
    | None => is_error_code r = true
    | Some (e, mem', sz, ex) =>
        r = sz /\ 0 <= sz <= oa_cap o /\ oc' = zbytes mem' /\ Zlength mem' = Zlength mem /\ bytes_ok mem' /\
        e' = ex /\ ExBlockBytes.xh_good (ExBlock.x_huf ExHuf.xhuf e) /\
        exists ts2, tso = Some ts2 /\ ts_x ts2 = e
    end.
