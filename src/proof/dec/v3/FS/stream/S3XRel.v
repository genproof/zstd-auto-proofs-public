(* The exact relation of the stream (FSRep3.srel3's sr_ex for the streaming part, Spec_api6.dc_ex): the concrete
   streaming fields, frame fields and tables of a context are the image of model/ExStream.v's state after the calls
   since the reset (ExStreamFacts.zs_run_x, model/Exact.v's instance), on the fields zstd still reads.

   - drel: ZSTD_decompressContinue's state (ExStream.dstate) against the frame fields and the tables;
   - zrel: the stream state (ExStream.zstate) against the streaming fields, stage by stage: at a call boundary in
     zdss_init zstd rewrites lhSize, inPos, outStart, outEnd and the hostage byte before reading them and begins the
     frame state again, so only the buffers, oversizedDuration, noForwardProgress and litExtraBuffer are pinned
     there;
   - zrel_end: what the code after the loop reads (in zdss_init too);
   - xrel3: the relation itself; a clean context is the image of no call (xrel3_clean). *)
Require Export Zstd.proof.dec.v3.FS.FSOblig3.
Require Import Zstd.proof.model.ExCall Zstd.proof.model.ExStream Zstd.proof.model.ExStreamFacts.
Require Zstd.proof.model.ExHuf Zstd.proof.model.ExBlock Zstd.proof.model.ExBlockBytes Zstd.proof.model.Exact.
Local Open Scope logic.

Notation XS := Exact.xstate.

(* a ring offset as a pointer into outBuff (None: NULL) *)
Definition ring_ptr (ob: val) (o: option Z) : val :=
  match o with Some x => offset_val x ob | None => nullval end.

(* virtualStart: dictEnd - (prefixStart - virtualStart) is the extDict's start d_ds (ExStream.d_continuity) *)
Definition vstart_of (ob: val) (d: ExStream.dstate XS) : val :=
  match d_pfx XS d with
  | None => nullval
  | Some ps =>
      match d_ds XS d, d_de XS d with
      | Some a, Some b => offset_val (ps - (b - a)) ob
      | _, _ => offset_val ps ob
      end
  end.

(* ZSTD_decompressContinue's state d of the frame with header fh, ring offsets in outBuff ob: the frame fields fs
   and the tables' state ts (the entropy state, litExtraBuffer included, is the model's) *)
Definition drel (fh: frame_header) (d: ExStream.dstate XS) (ob: val) (fs: fstate) (ts: tstate) : Prop :=
  fs_fParams fs = fh_val fh /\
  (* the header's fields as zstd stores them (U64 content size, block size): the model compares them unbounded *)
  0 <= fh_contentSize fh <= Int64.max_unsigned /\ 0 <= fh_blockSizeMax fh <= Int.max_unsigned /\
  0 <= fh_checksumFlag fh <= Int.max_unsigned /\
  (* the values zstd stores in bounded fields, and the ring offsets of its pointers *)
  0 <= d_stage XS d <= DS_skipFrame /\ 0 <= d_expected XS d <= Int64.max_unsigned /\ 0 <= d_btype XS d <= 3 /\
  0 <= d_rle XS d <= Int64.max_unsigned /\
  (forall x, d_prev XS d = Some x \/ d_pfx XS d = Some x \/ d_ds XS d = Some x \/ d_de XS d = Some x ->
     0 <= x <= Ptrofs.max_unsigned) /\
  (* the Huffman table's cells are in range: a compressed block then leaves bytes (ExBlockBytes.xblock_bytes) *)
  ExBlockBytes.xh_good (ExBlock.x_huf ExHuf.xhuf (d_ent XS d)) /\
  ts_x ts = d_ent XS d /\
  fs_isFrameDecompression fs = Vint (Int.repr 1) /\
  fs_stage fs = Vint (Int.repr (d_stage XS d)) /\ fs_expected fs = vlong (d_expected XS d) /\
  (d_stage XS d = DS_decompressBlock \/ d_stage XS d = DS_decompressLastBlock ->
     fs_bType fs = Vint (Int.repr (d_btype XS d)) /\ fs_rleSize fs = vlong (d_rle XS d)) /\
  (DS_decodeBlockHeader <= d_stage XS d <= DS_checkChecksum ->
     fs_decodedSize fs = vlong (Zlength (d_out XS d)) /\ bytes_ok (d_out XS d) /\
     fs_validateChecksum fs = Vint (Int.repr (if d_check XS d then 1 else 0)) /\
     (d_check XS d = true -> fs_xxh fs = Some (d_out XS d)) /\
     fs_previousDstEnd fs = ring_ptr ob (d_prev XS d) /\ fs_prefixStart fs = ring_ptr ob (d_pfx XS d) /\
     fs_dictEnd fs = ring_ptr ob (d_de XS d) /\ fs_virtualStart fs = vstart_of ob d /\
     fs_gpDictCopy fs = Vint (Int.repr 0)).

(* the stream state z against the streaming fields s (FSRep3.sf_strip of the context's), frame fields and tables *)
Definition zrel (z: zstate_x) (s: sfields) (fs: fstate) (t: tabs3) : Prop :=
  let d := zs_dc XS z in
  (* every stage: the buffers, oversizedDuration, noForwardProgress, the ring's cells, litExtraBuffer *)
  sf_stage s = zs_stage XS z /\ 0 <= zs_stage XS z <= 4 /\
  sf_inSize s = zs_inbs XS z /\ sf_outSize s = zs_outbs XS z /\ sf_over s = zs_over XS z /\
  sf_nfp s = zs_nfp XS z /\
  Zlength (zs_mem XS z) = zs_outbs XS z /\ bytes_ok (zs_mem XS z) /\
  sublist (zs_inbs XS z) (zs_inbs XS z + zs_outbs XS z) (sf_ring s) = zbytes (zs_mem XS z) /\
  tabs_lxb t = ExBlock.x_lxb ExHuf.xhuf (d_ent XS d) /\
  (* zdss_loadHeader: the header bytes so far, the rest of the frame state not yet begun *)
  (zs_stage XS z = ZDSS_loadHeader ->
     sf_lhSize s = vlong (Zlength (zs_hbuf XS z)) /\ Zlength (zs_hbuf XS z) <= 18 /\ bytes_ok (zs_hbuf XS z) /\
     sublist 0 (Zlength (zs_hbuf XS z)) (sf_hbuf s) = zbytes (zs_hbuf XS z) /\
     sf_inPos s = vlong 0 /\ zs_inpos XS z = 0 /\ sf_outStart s = vlong 0 /\ sf_outEnd s = vlong 0 /\
     zs_ostart XS z = 0 /\ zs_oend XS z = 0 /\ sf_hostage s = Vint (Int.repr 0) /\ zs_host XS z = 0) /\
  (* zdss_read, zdss_load, zdss_flush: a frame in progress *)
  (ZDSS_read <= zs_stage XS z ->
     sf_inPos s = vlong (zs_inpos XS z) /\ sf_outStart s = vlong (zs_ostart XS z) /\
     sf_outEnd s = vlong (zs_oend XS z) /\ 0 <= zs_ostart XS z <= zs_oend XS z /\ zs_oend XS z <= zs_outbs XS z /\
     sf_hostage s = Vint (Int.repr (zs_host XS z)) /\ (zs_host XS z = 0 \/ zs_host XS z = 1) /\
     (exists ts, t = TInit None ts /\ drel (zs_fp XS z) d (sf_outBuff s) fs ts) /\
     (zs_stage XS z = ZDSS_load -> d_stage XS d <> DS_skipFrame ->
        Zlength (zs_ibuf XS z) = zs_inpos XS z /\ bytes_ok (zs_ibuf XS z) /\
        sublist 0 (zs_inpos XS z) (sf_ring s) = zbytes (zs_ibuf XS z))).

(* at the loop's exit and between the loop and the epilogue: what the epilogue reads, in zdss_init too *)
Definition zrel_end (z: zstate_x) (s: sfields) (fs: fstate) (t: tabs3) : Prop :=
  let d := zs_dc XS z in
  zrel z s fs t /\
  (* in zdss_loadHeader zstd's expected and stage are not read (the shortcut sets expected, ZSTD_decompressBegin both),
     and a context reset with the parameters keeps them; the stage is read only when expected is not 0 *)
  (zs_stage XS z <> ZDSS_loadHeader ->
     fs_expected fs = vlong (d_expected XS d) /\ (d_expected XS d <> 0 -> fs_stage fs = Vint (Int.repr (d_stage XS d)))) /\
  (* a frame done with the hostage byte held: the epilogue may go back to zdss_read, so the frame state is kept *)
  (zs_stage XS z = ZDSS_init -> zs_host XS z = 1 -> exists ts, t = TInit None ts /\ drel (zs_fp XS z) d (sf_outBuff s) fs ts) /\
  sf_inPos s = vlong (zs_inpos XS z) /\ sf_outStart s = vlong (zs_ostart XS z) /\
  sf_outEnd s = vlong (zs_oend XS z) /\ sf_hostage s = Vint (Int.repr (zs_host XS z)) /\
  (zs_host XS z = 0 \/ zs_host XS z = 1).

(* the exact relation: the calls h since the reset lead the model to a state z the fields represent *)
Definition xrel3 (h: list zcall) (s: sfields) (fs: fstate) (t: tabs3) : Prop :=
  exists z, zs_run_x h = Some z /\ zinv_x z /\ zrel z s fs t.

(* litExtraBuffer zeroed is the model's initial one (compared without computing the 65568 cells) *)
Lemma lxb_zero_init : lxb_zero = ExBlock.x_lxb ExHuf.xhuf (ExBlock.xst_init ExHuf.xhuf).
Proof. unfold lxb_zero, ExBlock.xst_init; cbn [ExBlock.x_lxb]. f_equal. Qed.

(* a clean context (a new one, or one reset with the parameters) is the image of no call *)
Lemma xrel3_clean (s: sfields) (fs: fstate) :
  sf_stage s = 0 -> sf_inSize s = 0 -> sf_outSize s = 0 -> sf_over s = 0 -> sf_nfp s = 0 ->
  xrel3 nil (sf_strip s) fs (TUninit lxb_zero).
Proof.
  intros E1 E2 E3 E4 E5. exists (zstate_init XS (ExBlock.xst_init ExHuf.xhuf)).
  split; [exact zs_run_x_nil |]. split; [exact zinv_x_init |].
  unfold zrel.
  cbn [sf_strip sf_stage sf_inSize sf_outSize sf_over sf_nfp sf_ring zs_stage zs_inbs zs_outbs zs_over zs_nfp
       zs_mem zs_dc zstate_init tabs_lxb d_ent].
  rewrite E1, E2, E3, E4, E5.
  split; [reflexivity |]. split; [unfold ZDSS_init; lia |]. split; [reflexivity |]. split; [reflexivity |].
  split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |]. split; [constructor |].
  split; [rewrite sublist_nil; reflexivity |]. split; [exact lxb_zero_init |].
  split; intros H; unfold ZDSS_init, ZDSS_loadHeader, ZDSS_read in H; lia.
Qed.
