(* FS3 streaming: the model facts the decompressStream segments use, as statements (MF3), so that the
   segment proofs assume them (MF3 -> ...) while the model part proves them (MF3_ok).  The statements
   are fixed: both sides rely on them.  v2's StreamModelStmts (src/proof/dec/FS/) generalised to the streaming mode sm
   (format, ignored checksums, block size cap, dictionary selection, window limit) and the current
   dictionary cd; the v2 proofs (src/proof/dec/FS/StreamModelFacts.v) are the template.

   R1 (API v3.3): the stream's model has the dictionary window rule (sm_md = dmode_w ..: dec_block true =
   decode_block_w); zstd's blocks are described by B with Block.v's lenient decode_block behind the history H it
   still reaches (the dictionary content, or nil after a ring wrap, when the output exceeds the window: zhist_ok);
   the streaming shortcut's one-shot claims are lenient (md_len).  P_dict_wrap (v3.0's gap) is gone. *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Block Zstd.proof.model.Xxh64 Zstd.proof.model.Info Zstd.proof.model.Series Zstd.proof.model.StreamModel Zstd.proof.model.Params Zstd.proof.model.ParamsH.
Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Export Zstd.proof.dec.v3.FS.stream.S3ModelDefs.
Require Import Zstd.proof.model.Refuse.
Import ListNotations.
Local Open Scope Z_scope.

Definition sm_series (sm: smode) (cd: option dict_model) (wl: Z) (s: list Z) : list frec * Series.tail :=
  series_frames_m (sm_md sm) (sm_sel sm) cd wl s.

Definition sm_curafter (sm: smode) (cd: option dict_model) (s: list Z) : option dict_model :=
  series_cur (sm_md sm) (sm_sel sm) cd no_wlim s.

(* the effective Block_Maximum_Size of a header under the mode *)
Definition sm_bsm (sm: smode) (h: frame_header) : Z := Z.min (fh_blockSizeMax h) (md_bmax (sm_md sm)).

Definition P_frames_done_app : Prop :=
  forall sm cd dsin recs fb fp, bytes_ok dsin -> bytes_ok fb ->
  sm_series sm (sm_cur sm) no_wlim dsin = (recs, TEnd) -> sm_curafter sm (sm_cur sm) dsin = cd ->
  cur_rel (sm_md sm) (sm_sel sm) cd fb fp -> fp_complete fp = true ->
  exists recs', sm_series sm (sm_cur sm) no_wlim (dsin ++ fb) = (recs', TEnd) /\
    flat_map fr_content recs' = flat_map fr_content recs ++ fp_content fp /\
    length recs' = S (length recs) /\
    sm_curafter sm (sm_cur sm) (dsin ++ fb) = next_cd sm fp cd.

Definition P_dead_of_fdead : Prop :=
  forall sm cd dsin recs x, bytes_ok dsin ->
  sm_series sm (sm_cur sm) no_wlim dsin = (recs, TEnd) -> sm_curafter sm (sm_cur sm) dsin = cd ->
  fdead sm cd x -> dead sm (dsin ++ x).

Definition P_bad_of_fbad : Prop :=
  forall sm cd dsin recs x s, bytes_ok dsin ->
  sm_series sm (sm_cur sm) no_wlim dsin = (recs, TEnd) -> sm_curafter sm (sm_cur sm) dsin = cd ->
  fbad sm cd x -> is_prefix (dsin ++ x) s ->
  snd (sm_series sm (sm_cur sm) (sm_wl sm) s) <> TEnd.

Definition P_dead_app : Prop :=
  forall sm x y, dead sm x -> dead sm (x ++ y).

Definition P_fdead_app : Prop :=
  forall sm cd x y, fdead sm cd x -> fdead sm cd (x ++ y).

Definition P_fbad_app : Prop :=
  forall sm cd x y, fbad sm cd x -> fbad sm cd (x ++ y).

Definition P_hdr_err_bad : Prop :=
  forall sm cd x, bytes_ok x -> x <> nil -> get_frame_header_m (sm_mg sm) x = FH_err -> fbad sm cd x.

Definition P_hdr_skip : Prop :=
  forall sm cd x h, bytes_ok x -> sm_mg sm = false ->
  get_frame_header x = FH_ok h -> fh_frameType h = 1 -> Zlength x = fh_headerSize h ->
  Zlength x = ZSTD_SKIPPABLEHEADERSIZE /\ fh_contentSize h = le_field x 4 4 /\
  is_skippable_magic (le_field x 0 4) = true /\
  cur_rel (sm_md sm) (sm_sel sm) cd x (FP_skip x 0).

(* a magicless header is never skippable *)
Definition P_hdr_magicless : Prop :=
  forall x h, get_frame_header_m true x = FH_ok h -> fh_frameType h = 0.

Definition P_hdr_zstd : Prop :=
  forall sm cd x h, bytes_ok x ->
  get_frame_header_m (sm_mg sm) x = FH_ok h -> fh_frameType h = 0 -> Zlength x = fh_headerSize h ->
  (frame_dict (sm_mg sm) (sm_sel sm) cd x = None -> fdead sm cd x) /\
  (forall dm, frame_dict (sm_mg sm) (sm_sel sm) cd x = Some dm ->
     fh_dictID h <> 0 -> fh_dictID h <> dm_id dm -> fdead sm cd x) /\
  (ZSTD_WINDOWSIZE_ABSMIN <= sm_wl sm -> Z.max (fh_windowSize h) ZSTD_WINDOWSIZE_ABSMIN > sm_wl sm ->
     fbad sm cd x) /\
  (forall dm, frame_dict (sm_mg sm) (sm_sel sm) cd x = Some dm -> (fh_dictID h = 0 \/ fh_dictID h = dm_id dm) ->
     cur_rel (sm_md sm) (sm_sel sm) cd x (FP_zstd x (z_start h dm (sm_bsm sm h) (md_ignore (sm_md sm))))).

Definition P_hdr_more_size : Prop :=
  forall mg x k, get_frame_header_m mg x = FH_more k -> Zlength x < k.

Definition P_hdr_more_ext : Prop :=
  forall mg x y k, bytes_ok (x ++ y) ->
  get_frame_header_m mg x = FH_more k -> Zlength (x ++ y) <= k ->
  match get_frame_header_m mg (x ++ y) with
  | FH_ok h => fh_headerSize h = Zlength (x ++ y)
  | FH_more k' => Zlength (x ++ y) < k'
  | FH_err => True
  end.

Definition P_skip_more : Prop :=
  forall md sel cd fb hdr got u,
  cur_rel md sel cd fb (FP_skip hdr got) -> got + Zlength u <= le_field hdr 4 4 ->
  cur_rel md sel cd (fb ++ u) (FP_skip hdr (got + Zlength u)).

Definition P_zunit_partial : Prop :=
  forall md sel cd fb hdr z g,
  cur_rel md sel cd fb (FP_zstd hdr z) -> zp_got z = nil ->
  match zp_ph z with
  | ZP_bhdr => Zlength g < ZSTD_blockHeaderSize
  | ZP_body bh => bp_type (block_props_of bh) <> 0 /\ exists c, cblock_size bh = Some c /\ Zlength g < c
  | ZP_ck => Zlength g < 4
  | ZP_end => False
  end ->
  cur_rel md sel cd (fb ++ g) (FP_zstd hdr (zp_set_got z g)).

(* the history zstd's block decoder was given: the frame's dictionary content, or nothing once the frame's
   output exceeds the window (after a ring wrap; the dictionary window rule then forbids it in the model too) *)
Definition zhist_ok (sm: smode) (z: zprog) (H: list Z) : Prop :=
  H = zp_hist z \/ (H = nil /\ md_dwin (sm_md sm) = true /\ fh_windowSize (zp_h z) < Zlength (zp_out z)).

Definition P_zunit_step : Prop :=
  forall sm cd fb hdr z H u cnt ts', bytes_ok fb -> dm_ok (zp_dm z) -> zhist_ok sm z H ->
  (forall bh c, zp_ph (zstep z u cnt ts') = ZP_body bh -> cblock_size bh = Some c -> c <= zp_bsm z) ->
  cur_rel (sm_md sm) (sm_sel sm) cd fb (FP_zstd hdr z) ->
  (match zp_ph z with
   | ZP_body bh => bp_type (block_props_of bh) = 0 \/ zp_got z = nil
   | _ => zp_got z = nil
   end) ->
  unit_ok (FP_zstd hdr z) (Zlength u) -> bytes_ok u ->
  cnt_safe z u cnt ts' -> cnt_ok z H u cnt ts' -> cont_checks z u cnt ->
  (cur_rel (sm_md sm) (sm_sel sm) cd (fb ++ u) (FP_zstd hdr (zstep z u cnt ts')) /\
   cnt_model_some (md_dwin (sm_md sm)) z u) \/
  fdead sm cd (fb ++ u).

Definition P_zunit_err : Prop :=
  forall sm cd fb hdr z H u cap, bytes_ok fb -> 0 < zp_bsm z -> zhist_ok sm z H ->
  cur_rel (sm_md sm) (sm_sel sm) cd fb (FP_zstd hdr z) ->
  (match zp_ph z with
   | ZP_body bh => bp_type (block_props_of bh) = 0 \/ zp_got z = nil
   | _ => zp_got z = nil
   end) ->
  unit_ok (FP_zstd hdr z) (Zlength u) -> bytes_ok u ->
  cont_err (FP_zstd hdr z) H u cap -> cap_room z cap ->
  fbad sm cd (fb ++ u).

Definition P_cur_complete : Prop :=
  forall sm cd fb fp, bytes_ok fb ->
  cur_rel (sm_md sm) (sm_sel sm) cd fb fp -> fp_complete fp = true ->
  exists rec, sm_series sm cd no_wlim fb = ([rec], TEnd) /\ fr_content rec = fp_content fp /\
              fr_start rec = 0 /\ fr_size rec = Zlength fb /\ sm_curafter sm cd fb = next_cd sm fp cd.

(* the streaming shortcut: one Zstandard frame x decoded in one shot (ZSTD_decompress_usingDDict) with the
   dictionary dm the frame selects; its claims are lenient (md_len: Block.v's blocks); the stream's model is
   strict (dictionary window rule): where the strict one decides, the lenient one agrees *)
Definition shortcut_frame (sm: smode) (cd: option dict_model) (x: list Z) (dm: dict_model) : Prop :=
  frame_compressed_size_m (sm_mg sm) x = Some (Zlength x) /\
  (exists h, get_frame_header_m (sm_mg sm) x = FH_ok h /\ fh_frameType h = 0) /\
  frame_dict (sm_mg sm) (sm_sel sm) cd x = Some dm.

Definition P_shortcut_ok : Prop :=
  forall sm cd x dm c, bytes_ok x -> shortcut_frame sm cd x dm ->
  decode_series_m (md_len (sm_md sm)) sel_none (Some dm) no_wlim x = SOk c ->
  (exists rec, sm_series sm cd no_wlim x = ([rec], TEnd) /\ fr_content rec = c /\
               fr_start rec = 0 /\ fr_size rec = Zlength x /\ sm_curafter sm cd x = Some dm) \/
  fdead sm cd x.

(* zstd decoded the frame in one shot (oneshot_ok's SUnk branch: the frame is then not refused) *)
Definition P_shortcut_unk : Prop :=
  forall sm cd x dm, bytes_ok x -> shortcut_frame sm cd x dm ->
  decode_series_m (md_len (sm_md sm)) sel_none (Some dm) no_wlim x = SUnk ->
  ~ series_refused_m (md_len (sm_md sm)) sel_none (Some dm) no_wlim x -> fdead sm cd x.

Definition P_shortcut_det : Prop :=
  forall sm cd x dm, bytes_ok x -> shortcut_frame sm cd x dm ->
  decode_series_m (md_len (sm_md sm)) sel_none (Some dm) no_wlim x = SDet -> fbad sm cd x.

Definition P_shortcut_capacity : Prop :=
  forall sm cd x dm s, bytes_ok x -> shortcut_frame sm cd x dm -> is_prefix x s ->
  snd (sm_series sm cd (sm_wl sm) s) = TEnd ->
  exists c, decode_series_m (md_len (sm_md sm)) sel_none (Some dm) no_wlim x = SOk c /\
    (forall h, get_frame_header_m (sm_mg sm) x = FH_ok h ->
       fh_contentSize h <> ZSTD_CONTENTSIZE_UNKNOWN -> Zlength c = fh_contentSize h).

(* one frame decoded with a selection is decoded with the dictionary its header selects (the shortcut's
   one-shot claim with the DDict set: Spec_api6.oneshot_sel) *)
Definition P_shortcut_sel : Prop :=
  forall md sel cur x dm,
  frame_compressed_size_m (md_magicless md) x = Some (Zlength x) ->
  (exists h, get_frame_header_m (md_magicless md) x = FH_ok h /\ fh_frameType h = 0) ->
  frame_dict (md_magicless md) sel cur x = Some dm ->
  decode_series_m md sel cur no_wlim x = decode_series_m md sel_none (Some dm) no_wlim x.

(* the same for the refusal (oneshot_sel's SUnk branch with the DDict set gives oneshot_ok's) *)
Definition P_shortcut_sel_ref : Prop :=
  forall md sel cur x dm,
  frame_compressed_size_m (md_magicless md) x = Some (Zlength x) ->
  (exists h, get_frame_header_m (md_magicless md) x = FH_ok h /\ fh_frameType h = 0) ->
  frame_dict (md_magicless md) sel cur x = Some dm ->
  series_refused_m md sel_none (Some dm) no_wlim x -> series_refused_m md sel cur no_wlim x.

Definition MF3 : Prop :=
  P_frames_done_app /\
  P_dead_of_fdead /\
  P_bad_of_fbad /\
  P_dead_app /\
  P_fdead_app /\
  P_fbad_app /\
  P_hdr_err_bad /\
  P_hdr_skip /\
  P_hdr_magicless /\
  P_hdr_zstd /\
  P_hdr_more_size /\
  P_hdr_more_ext /\
  P_skip_more /\
  P_zunit_partial /\
  P_zunit_step /\
  P_zunit_err /\
  P_cur_complete /\
  P_shortcut_ok /\
  P_shortcut_unk /\
  P_shortcut_det /\
  P_shortcut_capacity /\
  P_shortcut_sel /\
  P_shortcut_sel_ref.

Lemma mf_frames_done_app : MF3 -> P_frames_done_app.
Proof. intros M; unfold MF3 in M; tauto. Qed.
Lemma mf_dead_of_fdead : MF3 -> P_dead_of_fdead.
Proof. intros M; unfold MF3 in M; tauto. Qed.
Lemma mf_bad_of_fbad : MF3 -> P_bad_of_fbad.
Proof. intros M; unfold MF3 in M; tauto. Qed.
Lemma mf_dead_app : MF3 -> P_dead_app.
Proof. intros M; unfold MF3 in M; tauto. Qed.
Lemma mf_fdead_app : MF3 -> P_fdead_app.
Proof. intros M; unfold MF3 in M; tauto. Qed.
Lemma mf_fbad_app : MF3 -> P_fbad_app.
Proof. intros M; unfold MF3 in M; tauto. Qed.
Lemma mf_hdr_err_bad : MF3 -> P_hdr_err_bad.
Proof. intros M; unfold MF3 in M; tauto. Qed.
Lemma mf_hdr_skip : MF3 -> P_hdr_skip.
Proof. intros M; unfold MF3 in M; tauto. Qed.
Lemma mf_hdr_magicless : MF3 -> P_hdr_magicless.
Proof. intros M; unfold MF3 in M; tauto. Qed.
Lemma mf_hdr_zstd : MF3 -> P_hdr_zstd.
Proof. intros M; unfold MF3 in M; tauto. Qed.
Lemma mf_hdr_more_size : MF3 -> P_hdr_more_size.
Proof. intros M; unfold MF3 in M; tauto. Qed.
Lemma mf_hdr_more_ext : MF3 -> P_hdr_more_ext.
Proof. intros M; unfold MF3 in M; tauto. Qed.
Lemma mf_skip_more : MF3 -> P_skip_more.
Proof. intros M; unfold MF3 in M; tauto. Qed.
Lemma mf_zunit_partial : MF3 -> P_zunit_partial.
Proof. intros M; unfold MF3 in M; tauto. Qed.
Lemma mf_zunit_step : MF3 -> P_zunit_step.
Proof. intros M; unfold MF3 in M; tauto. Qed.
Lemma mf_zunit_err : MF3 -> P_zunit_err.
Proof. intros M; unfold MF3 in M; tauto. Qed.
Lemma mf_cur_complete : MF3 -> P_cur_complete.
Proof. intros M; unfold MF3 in M; tauto. Qed.
Lemma mf_shortcut_ok : MF3 -> P_shortcut_ok.
Proof. intros M; unfold MF3 in M; tauto. Qed.
Lemma mf_shortcut_unk : MF3 -> P_shortcut_unk.
Proof. intros M; unfold MF3 in M; tauto. Qed.
Lemma mf_shortcut_det : MF3 -> P_shortcut_det.
Proof. intros M; unfold MF3 in M; tauto. Qed.
Lemma mf_shortcut_capacity : MF3 -> P_shortcut_capacity.
Proof. intros M; unfold MF3 in M; tauto. Qed.
Lemma mf_shortcut_sel : MF3 -> P_shortcut_sel.
Proof. intros M; unfold MF3 in M; tauto. Qed.
Lemma mf_shortcut_sel_ref : MF3 -> P_shortcut_sel_ref.
Proof. intros M; unfold MF3 in M; tauto. Qed.
