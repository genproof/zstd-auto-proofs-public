(* w_frame (harness/writer.h) in plain Coq: what one Zstandard
   frame written by w_frame is made of.  The VST body of w_frame (the WB_frame templates) shows that it
   writes hp_bytes p ++ bb ++ b ++ hp_ck_bytes p c for parameters p (hp_ok) and blocks (wblocks_pre,
   wblock_ok); WF_Frame.wf_zframe_ok turns that into WModel.zframe_ok. *)
Require Export Zstd.proof.harness.writer.model.WModel.
Local Open Scope bool_scope.

Definition zb (b: bool) : Z := if b then 1 else 0.

(* ---------- the header ---------- *)

(* w_frame's choices: content size n, single segment, checksum, Frame_Content_Size form (fcsflag),
   window exponent e and mantissa m (0 / 0 for a single segment), Dictionary_ID form (didflag) and the
   Dictionary_ID written (fi->did) *)
Record hparams := { hp_n : Z; hp_single : bool; hp_ck : bool; hp_fcs : Z; hp_e : Z; hp_m : Z;
                    hp_didf : Z; hp_did : Z }.

Definition hp_ok (dm: dict_model) (p: hparams) : Prop :=
  0 <= hp_n p <= 2 ^ 18 /\
  0 <= hp_fcs p <= 3 /\
  (hp_single p = true -> hp_fcs p = 0 -> hp_n p <= 255) /\
  (hp_fcs p = 1 -> 256 <= hp_n p <= 65791) /\
  0 <= hp_e p <= 31 /\ 0 <= hp_m p <= 7 /\
  0 <= hp_didf p <= 3 /\
  (hp_didf p = 0 -> hp_did p = 0) /\
  (hp_didf p = 1 -> hp_did p <= 255) /\
  (hp_didf p = 2 -> hp_did p <= 65535) /\
  0 <= hp_did p < 2 ^ 32 /\
  (hp_did p = 0 \/ hp_did p = dm_id dm).

(* fi->did_size *)
Definition hp_did_size (p: hparams) : Z := nth (Z.to_nat (hp_didf p)) [0; 1; 2; 4] 0.

(* the Frame_Header_Descriptor: (fcsflag << 6) | (single << 5) | (checksum << 2) | didflag *)
Definition hp_fhd (p: hparams) : Z :=
  Z.lor (Z.lor (Z.lor (Z.shiftl (hp_fcs p) 6) (Z.shiftl (zb (hp_single p)) 5)) (Z.shiftl (zb (hp_ck p)) 2))
        (hp_didf p).

(* the Window_Descriptor: (e << 3) | m *)
Definition hp_wbyte (p: hparams) : Z := Z.lor (Z.shiftl (hp_e p) 3) (hp_m p).

(* window (fi->window), fi->window_log, Block_Maximum_Size (bmax) *)
Definition hp_window (p: hparams) : Z :=
  if hp_single p then hp_n p else 2 ^ (10 + hp_e p) + 2 ^ (10 + hp_e p) / 8 * hp_m p.
Definition hp_window_log (p: hparams) : Z := if hp_single p then 0 else 10 + hp_e p.
Definition hp_bsm (p: hparams) : Z := Z.min (hp_window p) (2 ^ 17).

(* the Frame_Content_Size field *)
Definition hp_fcs_bytes (p: hparams) : list Z :=
  if hp_fcs p =? 0 then (if hp_single p then le_bytes 1 (hp_n p) else [])
  else if hp_fcs p =? 1 then le_bytes 2 (hp_n p - 256)
  else if hp_fcs p =? 2 then le_bytes 4 (hp_n p)
  else le_bytes 8 (hp_n p).

(* the frame header (hdr[0 .. h.n)) *)
Definition hp_bytes (p: hparams) : list Z :=
  le_bytes 4 ZSTD_MAGICNUMBER ++ [hp_fhd p] ++ (if hp_single p then [] else [hp_wbyte p]) ++
  le_bytes (Z.to_nat (hp_did_size p)) (hp_did p) ++ hp_fcs_bytes p.

(* the Content_Checksum of the content c (if any) *)
Definition hp_ck_bytes (p: hparams) (c: list Z) : list Z :=
  if hp_ck p then le_bytes 4 (Z.land (Xxh64.xxh64 c 0) 4294967295) else [].

(* the frame record w_frame leaves: f0's fields that w_frame does not write (skippable, variant, start,
   size, cstart, csize, skip_n), nb blocks, ud = (d != NULL) *)
Definition hp_info (f0: winfo) (p: hparams) (nb: Z) (ud: bool) : winfo :=
  {| wi_skippable := wi_skippable f0; wi_variant := wi_variant f0;
     wi_start := wi_start f0; wi_size := wi_size f0; wi_cstart := wi_cstart f0; wi_csize := wi_csize f0;
     wi_fcs_present := hp_single p || negb (hp_fcs p =? 0); wi_fcs := hp_n p;
     wi_did_size := hp_did_size p; wi_did := hp_did p;
     wi_single := hp_single p; wi_window := hp_window p; wi_window_log := hp_window_log p;
     wi_checksum := hp_ck p; wi_blocks := nb; wi_skip_n := wi_skip_n f0;
     wi_hsize := Zlength (hp_bytes p); wi_uses_dict := ud |}.

(* ---------- the blocks ---------- *)

(* the block header's value: last | (type << 1) | (bsize << 3) *)
Definition blk_hv (last: bool) (ty bsize: Z) : Z :=
  Z.lor (Z.lor (zb last) (Z.shiftl ty 1)) (Z.shiftl bsize 3).

(* one block b (header and body) written by w_frame's loop, after the frame's content out, with the
   decoder state st before it (st' after it), adding the content c; bsm = Block_Maximum_Size, wsize =
   Window_Size, hist = the dictionary's content *)
Definition wblock_ok (bsm wsize: Z) (hist: list Z) (st: dstate) (out: list Z) (last: bool)
    (b: list Z) (st': dstate) (c: list Z) : Prop :=
  exists ty bsize body,
    b = le_bytes 3 (blk_hv last ty bsize) ++ body /\ bytes_ok body /\ bytes_ok c /\ 0 <= bsize <= bsm /\
    ((ty = 0 /\ body = c /\ bsize = Zlength c /\ st' = st) \/                    (* Raw_Block *)
     (ty = 1 /\ 1 <= bsm /\ (exists x, body = [x] /\ c = repeat x (Z.to_nat bsize)) /\ st' = st) \/  (* RLE_Block *)
     (ty = 2 /\ bsize = Zlength body /\                                           (* Compressed_Block *)
      decode_block st hist out body bsm wsize = Some (st', c))).

(* the blocks bb written before the current one: nb blocks, none last, from the state st0 and no
   output, to the state st and the output out *)
Inductive wblocks_pre (bsm wsize: Z) (hist: list Z) (st0: dstate) : list Z -> dstate -> list Z -> Z -> Prop :=
| wbp_nil : wblocks_pre bsm wsize hist st0 [] st0 [] 0
| wbp_snoc : forall bb st out nb b st' c,
    wblocks_pre bsm wsize hist st0 bb st out nb ->
    wblock_ok bsm wsize hist st out false b st' c ->
    wblocks_pre bsm wsize hist st0 (bb ++ b) st' (out ++ c) (nb + 1).
