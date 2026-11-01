(* The decoder's API as the harnesses see it.  FIXED: the harness proofs, the
   assembly and the decoder all use exactly these specifications.

   The specifications are parameterized by two abstract predicates chosen by the decoder's proof:
     DC gv p st : a decompression context (ZSTD_DCtx = ZSTD_DStream) at p in the abstract state st;
     DD gv q d  : a digested dictionary (ZSTD_DDict) at q made from the bytes dd_bytes d.
   The results are stated against the format model (src/proof/model/):
   - one-shot decoding (`oneshot_ok`): a success fits; on a series the model decodes to c, a success is
     exactly c and an error is a too small capacity or memory; a series the model says zstd certainly
     rejects (SDet) gives an error, and so does a series it certainly refuses (model/Refuse.v: a reserved block,
     a frame cut before its end, a wrong Frame_Content_Size); the error codes of a checksum refusal and of a too
     small capacity (ZSTD_decompress, ZSTD_decompressDCtx: Spec_codes.oneshot_codes);
   - streaming (`stream_post`): positions, delivered bytes and the claims of StreamModel.stream_claims; a return
     of 0 on a refused series ends a frame before the refused one (Refuse.stream_zero_ref);
     progress (`stream_progress`): when a call may read and write nothing (model/StreamProgress.v);
   - the inspection functions: exactly the functions of model/Frame.v and model/Info.v, on ANY bytes. *)
Require Export Zstd.proof.zstd.Gprog.
Require Export Zstd.proof.model.Frame Zstd.proof.model.Info Zstd.proof.model.Block Zstd.proof.model.Series Zstd.proof.model.StreamModel Zstd.proof.model.Params.
Require Export Zstd.proof.model.Refuse.
Require Export Zstd.proof.model.StreamProgress.
Require Export Zstd.proof.zstd.Spec_codes.
Require Export Zstd.proof.zstd.CMem.
Require Export Zstd.proof.model.Exact.

Definition t_dctx : type := Tstruct _ZSTD_DCtx_s noattr.
Definition t_ddict : type := Tstruct _ZSTD_DDict_s noattr.
Definition t_inBuffer : type := Tstruct _ZSTD_inBuffer_s noattr.
Definition t_outBuffer : type := Tstruct _ZSTD_outBuffer_s noattr.
Definition t_fh : type := Tstruct ___gp_ZSTD_FrameHeader noattr.

(* a byte buffer that may be NULL when it is empty (fix F9: ZSTD_decompressStream and ZSTD_decompressMultiFrame take a
   non-NULL base, ZSTD_emptyBuffer, for an empty buffer passed as NULL) *)
Definition mbuf (sh: share) (n: Z) (c: list val) (p: val) : mpred :=
  if eq_dec p nullval then !! (n = 0 /\ c = []) && emp else data_at sh (tarray tuchar n) c p.

Definition ZSTD_d_stableOutBuffer : Z := 1001.
Definition ZSTD_reset_session_only : Z := 1.
Definition ZSTD_reset_parameters : Z := 2.
Definition ZSTD_reset_session_and_parameters : Z := 3.

(* the decoding parameters (ZSTD_dParameter) *)
Definition ZSTD_d_windowLogMax : Z := 100.
Definition ZSTD_d_format : Z := 1000.
Definition ZSTD_d_forceIgnoreChecksum : Z := 1002.
Definition ZSTD_d_refMultipleDDicts : Z := 1003.
Definition ZSTD_d_maxBlockSize : Z := 1005.

(* ---------- abstract states ---------- *)

(* where the bytes of a context's dictionary are: the caller's memory at p (by reference), the context's
   own copy, or a ZSTD_DDict q (whose bytes are the caller's at p when it was made by reference) *)
(* a ZSTD_DDict: its bytes, and the caller's pointer when it refers to the caller's memory (made by
   reference, or a copy of 0 bytes, which zstd does not copy).  v3.1: also two facts only the decoder
   interprets, fixed when the DDict is made (createDDict's post gives them existentially): where its content
   is (dd_buf: zstd's copy, or the caller's memory) and what zstd's entropy loading gave (dd_ld); they pin
   the concrete DDict a context keeps pointers into across calls.  Callers only carry them along. *)
Record ddict_st := { dd_bytes : list Z; dd_ref : option val; dd_buf : val; dd_ld : option (dstate * Z) }.

Inductive dsrc := DSRef (p: val) | DSOwn | DSDDict (q: val) (dd: ddict_st).

(* a dictionary referenced by a context: raw content or not, used once (refPrefix) or sticky *)
Record dictref := { dr_src : dsrc; dr_raw : bool; dr_once : bool; dr_bytes : list Z }.

(* a stream since its last reset: the bytes zstd has READ (ss_in) and delivered (ss_out), zstd's count of
   calls in a row without progress, whether the last call failed, the output buffer of the last call when
   ZSTD_d_stableOutBuffer is set, and ss_ahead (0 or 1): how many bytes of ss_in are beyond the caller's
   input positions (zstd's "hostage byte": it reads the last byte of a frame, reports in.pos one less
   until the frame's output is flushed, then counts it without reading it again); ss_calls: the calls since
   the reset (the bytes each could read, its output room), whose history fixes zstd's buffers and ring
   (model/Exact.v, zs_call) *)
Record sstate := { ss_in : list Z; ss_out : list Z; ss_stall : Z; ss_err : bool; ss_obuf : option (val * Z);
                   ss_ahead : Z; ss_calls : list zcall }.

(* the decoding parameters of a context, as zstd stores them (v3): format (0 ZSTD_f_zstd1, 1 magicless),
   forceIgnoreChecksum (0/1), maxBlockSizeParam (0: none, else 1024..ZSTD_BLOCKSIZE_MAX), maxWindowSize
   (2^10..2^31; default 2^27 + 1), refMultipleDDicts (0/1) *)
Record dparams := { dp_fmt : Z; dp_ignore : Z; dp_bmax : Z; dp_wmax : Z; dp_multi : Z }.

Definition dp_wmax_dflt : Z := 2 ^ 27 + 1.
Definition dparams_dflt : dparams :=
  {| dp_fmt := 0; dp_ignore := 0; dp_bmax := 0; dp_wmax := dp_wmax_dflt; dp_multi := 0 |}.

(* the model's view of the parameters (model/Params.v) *)
Definition dmode_of (p: dparams) : dmode :=
  {| md_magicless := dp_fmt p =? 1; md_ignore := dp_ignore p =? 1;
     md_bmax := if dp_bmax p =? 0 then ZSTD_BLOCKSIZE_MAX else dp_bmax p; md_dwin := false |}.


(* a frame of the buffer-less API (ZSTD_decompressBegin*, ZSTD_decompressContinue): the dictionary it was
   begun with; its stage in the model (None: not described, after a call the model does not cover or that
   failed); zstd's dctx->expected (what ZSTD_nextSrcSizeToDecompress returns, also in an undescribed stage);
   and where the frame's output so far is (buffer, start, end), once a call has delivered into it: zstd
   reads it back as history, and the next call's dst must continue it *)
Record blabs := { ba_dict : option dictref; ba_st : option blst; ba_expect : Z; ba_out : option (val * Z * Z * Z) }.

(* dc_last: the dictionary of the context's last decoding with one (zstd keeps a pointer to its end, dictEnd).
   Since ZSTD_decompressBegin_usingDDict no longer compares dictEnd with the next DDict's end (patch: ddictIsCold
   = 1), no specification requires anything of it: contexts may change dictionaries after any use.
   v3: dc_par, the parameters; dc_set, the DDicts of zstd's DDict set (ZSTD_d_refMultipleDDicts: every
   ZSTD_DCtx_refDDict while it is on adds its DDict, replacing one of the same dictionary ID), in the order
   added; dc_bl, the buffer-less frame (None: none begun).
   dc_mem: the context's own allocator (CMem.cmem, given to ZSTD_createDCtx_advancedP; None: the default
   allocator), with the law's bound on the bytes it gives out; streaming raises the bound to the estimate of the
   window limit (set_ss, CMem.cm_raise).
   dc_ex: the stream is exactly what its calls since the reset (ss_calls) do to a clean context (a new one, or one
   reset with the parameters: no stream buffers, oversizedDuration 0, litExtraBuffer zeroed).  A session reset, a
   one-shot decoding or the buffer-less API leave buffers and literal slack behind that later streaming can read
   (patch item 17), so they clear it (set_ex). *)
Record dctx_st := { dc_dict : option dictref; dc_stable : bool; dc_ss : sstate; dc_last : option dictref;
                    dc_par : dparams; dc_set : list (val * ddict_st); dc_bl : option blabs;
                    dc_mem : option cmem; dc_ex : bool }.

Definition ss_init : sstate :=
  {| ss_in := nil; ss_out := nil; ss_stall := 0; ss_err := false; ss_obuf := None; ss_ahead := 0;
     ss_calls := nil |}.
Definition dctx_init : dctx_st :=
  {| dc_dict := None; dc_stable := false; dc_ss := ss_init; dc_last := None;
     dc_par := dparams_dflt; dc_set := nil; dc_bl := None; dc_mem := None; dc_ex := true |}.

Definition set_dict (st: dctx_st) (d: option dictref) : dctx_st :=
  {| dc_dict := d; dc_stable := dc_stable st; dc_ss := dc_ss st; dc_last := dc_last st;
     dc_par := dc_par st; dc_set := dc_set st; dc_bl := dc_bl st; dc_mem := dc_mem st;
     dc_ex := dc_ex st |}.
Definition set_ss (st: dctx_st) (ss: sstate) : dctx_st :=
  {| dc_dict := dc_dict st; dc_stable := dc_stable st; dc_ss := ss; dc_last := dc_last st;
     dc_par := dc_par st; dc_set := dc_set st; dc_bl := dc_bl st;
     dc_mem := cm_raise (dc_mem st) (dp_wmax (dc_par st)); dc_ex := dc_ex st |}.
Definition set_stable (st: dctx_st) (b: bool) : dctx_st :=
  {| dc_dict := dc_dict st; dc_stable := b; dc_ss := dc_ss st; dc_last := dc_last st;
     dc_par := dc_par st; dc_set := dc_set st; dc_bl := dc_bl st; dc_mem := dc_mem st;
     dc_ex := dc_ex st |}.
Definition set_last (st: dctx_st) (l: option dictref) : dctx_st :=
  {| dc_dict := dc_dict st; dc_stable := dc_stable st; dc_ss := dc_ss st; dc_last := l;
     dc_par := dc_par st; dc_set := dc_set st; dc_bl := dc_bl st; dc_mem := dc_mem st;
     dc_ex := dc_ex st |}.
Definition set_par (st: dctx_st) (p: dparams) : dctx_st :=
  {| dc_dict := dc_dict st; dc_stable := dc_stable st; dc_ss := dc_ss st; dc_last := dc_last st;
     dc_par := p; dc_set := dc_set st; dc_bl := dc_bl st; dc_mem := dc_mem st;
     dc_ex := dc_ex st |}.
Definition set_set (st: dctx_st) (l: list (val * ddict_st)) : dctx_st :=
  {| dc_dict := dc_dict st; dc_stable := dc_stable st; dc_ss := dc_ss st; dc_last := dc_last st;
     dc_par := dc_par st; dc_set := l; dc_bl := dc_bl st; dc_mem := dc_mem st;
     dc_ex := dc_ex st |}.
Definition set_ex (st: dctx_st) (b: bool) : dctx_st :=
  {| dc_dict := dc_dict st; dc_stable := dc_stable st; dc_ss := dc_ss st; dc_last := dc_last st;
     dc_par := dc_par st; dc_set := dc_set st; dc_bl := dc_bl st; dc_mem := dc_mem st; dc_ex := b |}.
Definition set_bl (st: dctx_st) (b: option blabs) : dctx_st :=
  {| dc_dict := dc_dict st; dc_stable := dc_stable st; dc_ss := dc_ss st; dc_last := dc_last st;
     dc_par := dc_par st; dc_set := dc_set st; dc_bl := b; dc_mem := dc_mem st;
     dc_ex := dc_ex st |}.

(* a new context with its own allocator m *)
Definition dctx_init_m (m: cmem) : dctx_st :=
  {| dc_dict := None; dc_stable := false; dc_ss := ss_init; dc_last := None;
     dc_par := dparams_dflt; dc_set := nil; dc_bl := None; dc_mem := Some m; dc_ex := true |}.

(* ZSTD_DCtx_reset's parameter half (ZSTD_reset_parameters, and ZSTD_reset_session_and_parameters after its session
   half): no dictionary (ZSTD_clearDict), zstd's default parameters and buffered output, no buffer-less frame.  F8's
   effects (the stream's buffers freed, the literal buffer cleared) are inside the context's representation.  zstd
   keeps its DDict set, which it does not consult while ZSTD_d_refMultipleDDicts is off (the default): with an empty
   set, a context reset with both halves is a new one (reset_both_init). *)
Definition reset_par (st: dctx_st) : dctx_st :=
  {| dc_dict := None; dc_stable := false; dc_ss := dc_ss st; dc_last := None; dc_par := dparams_dflt;
     dc_set := dc_set st; dc_bl := None; dc_mem := dc_mem st; dc_ex := true |}.

Lemma reset_both_init (st: dctx_st) : dc_set st = nil -> dc_mem st = None -> reset_par (set_ss st ss_init) = dctx_init.
Proof. intros E M. unfold reset_par, set_ss, dctx_init; simpl. rewrite E, M. reflexivity. Qed.

(* a new stream in a context that has streamed before: zstd's streamStage is zdss_init again (a setter between two
   frames, or one-shot decoding, code fix F10), so the next ZSTD_decompressStream begins a new frame, as after a
   session reset; no claim of the earlier stream carries on.  zstd keeps its count of calls without progress
   (noForwardProgress), so the state claims no stall count: the next call without progress may fail *)
Definition ss_restart : sstate :=
  {| ss_in := nil; ss_out := nil; ss_stall := ZSTD_NO_FORWARD_PROGRESS_MAX - 1; ss_err := false; ss_obuf := None;
     ss_ahead := 0; ss_calls := nil |}.

(* ... unless the stream failed: a failed stream stays failed (its count of calls without progress may have passed
   the limit), it needs a session reset before the next stream call *)
Definition ss_next (ss: sstate) : sstate := if ss_err ss then ss else ss_restart.

(* the result of a function zstd refuses while a frame is being streamed (RETURN_ERROR_IF(streamStage !=
   zdss_init, stage_wrong)), on a context in any state: before any stream (dc_ss = ss_init) its effect res; after
   one, either the refusal (an error, nothing changed) or, between two frames, res on the context with a new
   stream (ss_next: ss_restart, or the failed stream kept).  Between two frames zstd keeps the stream's buffers,
   its ring cells, oversizedDuration and noForwardProgress (and, after a setter, litExtraBuffer), so the context
   is no longer the image of its calls since the reset on a clean one: the restart clears dc_ex, also after
   reset_par (which sets it) *)
Definition after_stage (res: dctx_st -> Z -> dctx_st -> Prop) (st: dctx_st) (r: Z) (st': dctx_st) : Prop :=
  (dc_ss st = ss_init /\ res st r st') \/
  (dc_ss st <> ss_init /\ ((is_error_code r = true /\ st' = st) \/
                           exists st1, res (set_ss st (ss_next (dc_ss st))) r st1 /\ st' = set_ex st1 false)).

Lemma after_stage_init (res: dctx_st -> Z -> dctx_st -> Prop) (st: dctx_st) (r: Z) (st': dctx_st) :
  dc_ss st = ss_init -> after_stage res st r st' -> res st r st'.
Proof. intros E [[_ H] | [H _]]; [exact H | contradiction]. Qed.

(* ZSTD_DCtx_reset(d, dir): the session half (ZSTD_reset_session_only: a new stream, nothing else changed), the
   parameter half (ZSTD_reset_parameters, refused while a frame is being streamed), or both (never refused: the
   session half first ends any stream) *)
Definition reset_post (dir: Z) (st: dctx_st) (r: Z) (st': dctx_st) : Prop :=
  if dir =? ZSTD_reset_session_only then r = 0 /\ st' = set_ex (set_ss st ss_init) false
  else if dir =? ZSTD_reset_parameters then after_stage (fun st0 r0 st1 => r0 = 0 /\ st1 = reset_par st0) st r st'
  else r = 0 /\ st' = reset_par (set_ss st ss_init).

Lemma reset_post_session (st: dctx_st) (r: Z) (st': dctx_st) :
  reset_post ZSTD_reset_session_only st r st' -> r = 0 /\ st' = set_ex (set_ss st ss_init) false.
Proof. exact (fun H => H). Qed.

Lemma reset_post_both (st: dctx_st) (r: Z) (st': dctx_st) :
  reset_post ZSTD_reset_session_and_parameters st r st' -> r = 0 /\ st' = reset_par (set_ss st ss_init).
Proof. exact (fun H => H). Qed.

(* after a one-shot decompression: a dictionary used once is dropped *)
Definition after_use (st: dctx_st) : dctx_st :=
  match dc_dict st with Some d => if dr_once d then set_dict st None else st | None => st end.


(* the dictionary of a context that references the DDict q made from dd *)
Definition ddict_ref (q: val) (dd: ddict_st) : dictref :=
  {| dr_src := DSDDict q dd; dr_raw := false; dr_once := false; dr_bytes := dd_bytes dd |}.

(* the former condition of a decoding with the dictionary d on the context's last one (none or d, and d not a
   DDict copied by zstd); no specification requires it any more.  After a decoding, dc_last is the old one or the
   new one *)
Definition last_ok (st: dctx_st) (d: dictref) : Prop :=
  dc_last st = None \/
  (dc_last st = Some d /\ match dr_src d with DSDDict _ dd => dd_ref dd <> None | _ => True end).

(* the mark streaming leaves in dc_last (zstd's dictEnd may then point into the stream's buffer) *)
Definition stream_mark : dictref := {| dr_src := DSOwn; dr_raw := true; dr_once := true; dr_bytes := nil |}.
Definition after_decode (st st': dctx_st) (l: option dictref) : Prop :=
  st' = set_ex st false \/ st' = set_last (set_ex st false) l.

(* the dictionary a context decodes with (None: no claim, a corrupted formatted dictionary) *)
Definition dictref_model (d: option dictref) : option dict_model :=
  match d with
  | None => Some no_dict
  | Some d => if dr_raw d then Some (dict_raw (dr_bytes d)) else dict_auto (dr_bytes d)
  end.

(* ---------- the DDict set (ZSTD_d_refMultipleDDicts) ---------- *)

(* the ID zstd gives a DDict made in ZSTD_dct_auto mode (ZSTD_getDictID_fromDDict) *)
Definition dd_id (dd: ddict_st) : Z := dict_id_of (dd_bytes dd).

(* a ZSTD_DCtx_refDDict while the parameter is on: the DDict replaces the one of the same ID, or joins *)
Definition set_add (l: list (val * ddict_st)) (q: val) (dd: ddict_st) : list (val * ddict_st) :=
  if existsb (fun e => dd_id (snd e) =? dd_id dd) l
  then map (fun e => if dd_id (snd e) =? dd_id dd then (q, dd) else e) l
  else l ++ (q, dd) :: nil.

Fixpoint ids_distinct (l: list Z) : bool :=
  match l with nil => true | x :: r => (negb (existsb (Z.eqb x) r) && ids_distinct r)%bool end.

(* the set is described when its DDicts are ones the model loads, with distinct non-zero IDs: zstd's lookup by
   a frame's Dictionary_ID then finds exactly the DDict of that ID (a DDict of ID 0 ends a probe early) *)
Definition set_clean (l: list (val * ddict_st)) : bool :=
  (ids_distinct (map (fun e => dd_id (snd e)) l) &&
   forallb (fun e => negb (dd_id (snd e) =? 0) &&
                     match dict_auto (dd_bytes (snd e)) with Some _ => true | None => false end) l)%bool.

Definition set_sel (l: list (val * ddict_st)) (id: Z) : option dict_model :=
  if id =? 0 then None else
  match find (fun e => dd_id (snd e) =? id) l with
  | Some e => dict_auto (dd_bytes (snd e))
  | None => None
  end.

(* the dictionaries a decoding uses (model/Params.v: the selection, and the dictionary before the first frame).
   No set: the context's dictionary.  A set: zstd may have switched its current DDict at an earlier frame, so
   the current one is not described; frames are described when the parameter is on, the set clean and a
   dictionary configured (zstd only selects while it has a current DDict); otherwise nothing is. *)
Definition st_sel (st: dctx_st) : (Z -> option dict_model) * option dict_model :=
  match dc_set st with
  | nil => (sel_none, dictref_model (dc_dict st))
  | _ :: _ =>
      match dc_dict st with
      | None => (sel_none, None)
      | Some dr =>
          (* v3.4: zstd selects only with a current DDict: none for a dictionary of 0 bytes loaded into the
             context (or by reference) *)
          if ((dp_multi (dc_par st) =? 1) && set_clean (dc_set st) &&
              match dr_src dr with DSDDict _ _ => true | _ => negb (Nat.eqb (length (dr_bytes dr)) 0) end)%bool
          then (set_sel (dc_set st), None)
          else (sel_none, None)
      end
  end.

(* one-shot decoding with the set: ZSTD_decompressMultiFrame begins each frame with the DDict of its
   Dictionary_ID found in the set (fix F4), else the current one: the streaming selection
   (st_sel).  oneshot_dm is v3's (kept for the proofs that use it with an empty set) *)
Definition oneshot_dm (st: dctx_st) (dm: option dict_model) : option dict_model :=
  match dc_set st with nil => dm | _ :: _ => None end.

(* bytes of a dictionary in the format zstd recognises (magic number) *)
Definition dict_formatted (b: list Z) : bool :=
  ((8 <=? Zlength b) && (le_field b 0 4 =? ZSTD_MAGIC_DICTIONARY))%bool.

(* ---------- contexts after any use (res_free) ---------- *)

(* a context's own allocator after a call that may allocate through it (a dictionary loaded by copy, the DDict
   set): the same functions and opaque pointer, the ghost bound raised (the decoder chooses how far) *)
Definition cm_raised (om om': option cmem) : Prop :=
  match om, om' with
  | None, None => True
  | Some m, Some m' => cm_alloc m' = cm_alloc m /\ cm_free m' = cm_free m /\ cm_opaque m' = cm_opaque m /\
                       cm_bound m <= cm_bound m'
  | _, _ => False
  end.

Definition set_mem (st: dctx_st) (om: option cmem) : dctx_st :=
  {| dc_dict := dc_dict st; dc_stable := dc_stable st; dc_ss := dc_ss st; dc_last := dc_last st;
     dc_par := dc_par st; dc_set := dc_set st; dc_bl := dc_bl st; dc_mem := om;
     dc_ex := dc_ex st |}.

(* ZSTD_decompressDCtx on a context in any streaming state: before any stream, the state is the one-shot's; after
   one, a new stream begins (F10: ZSTD_decompressMultiFrame sets streamStage = zdss_init), a failed one stays failed
   (ss_next) *)
Definition oneshot_after (st: dctx_st) (st': dctx_st) : Prop :=
  (dc_ss st = ss_init /\ after_decode (after_use st) st' (dc_dict st)) \/
  (dc_ss st <> ss_init /\ after_decode (after_use (set_ss st (ss_next (dc_ss st)))) st' (dc_dict st)).

Lemma oneshot_after_init (st st': dctx_st) :
  dc_ss st = ss_init -> oneshot_after st st' -> after_decode (after_use st) st' (dc_dict st).
Proof. intros E [[_ H] | [H _]]; [exact H | contradiction]. Qed.

(* cells holding bytes *)
Definition cells_bytes (l: list val) : Prop := exists bs, l = zbytes bs /\ bytes_ok bs.

Section Api.
Variable DC : globals -> val -> dctx_st -> mpred.
Variable DD : globals -> val -> ddict_st -> mpred.
(* the law's allocator predicates (CMem); laws without contexts of their own allocator take CMem.cmem_none *)
Context {CMI: cmem_preds}.

(* v3.2: with the DDict pointer's validity (callers test it against NULL after lending it) *)
Definition ddict_res (gv: globals) (sh: share) (q: val) (d: ddict_st) : mpred :=
  sepcon (andp (DD gv q d) (valid_pointer q))
  (match dd_ref d with
   | Some p => data_at sh (tarray tuchar (Zlength (dd_bytes d))) (zbytes (dd_bytes d)) p
   | None => emp
   end).

(* the caller's n bytes b at p, or NULL for no bytes (ZSTD_createDDict(NULL, 0)) *)
Definition bytes_at (sh: share) (b: list Z) (p: val) : mpred :=
  if eq_dec p nullval then emp else data_at sh (tarray tuchar (Zlength b)) (zbytes b) p.

Lemma bytes_at_ptr (sh: share) (b: list Z) (p: val) :
  isptr p -> bytes_at sh b p = data_at sh (tarray tuchar (Zlength b)) (zbytes b) p.
Proof. intros Hp. unfold bytes_at. destruct (eq_dec p nullval) as [E|E]; [subst; contradiction | reflexivity]. Qed.

Lemma bytes_at_null (sh: share) (b: list Z) : bytes_at sh b nullval = emp.
Proof. unfold bytes_at. destruct (eq_dec nullval nullval); [reflexivity | contradiction]. Qed.

(* the memory of the dictionary in use, which the caller holds (any readable share sh) *)
Definition dict_res (gv: globals) (sh: share) (d: option dictref) : mpred :=
  match d with
  | None => emp
  | Some d =>
      match dr_src d with
      | DSRef p => data_at sh (tarray tuchar (Zlength (dr_bytes d))) (zbytes (dr_bytes d)) p
      | DSOwn => emp
      | DSDDict q dd => ddict_res gv sh q dd
      end
  end.

(* Buffer witnesses: the code compares the pointers of the caller's buffers (with NULL, with the ends of
   other buffers), which needs their start and end to be weakly valid; a buffer of 0 bytes cannot show it
   by itself.  ws are resources the caller lends for the call (Spec_xxh.ptr_witness: [] when every buffer
   is non-empty; e.g. the malloc_token of an empty block, or a slack byte next to the buffer), returned
   unchanged.  (A WITH of type mpred is a universe inconsistency in VST, hence first-order witnesses.) *)
(* pws_pred ws (Spec_xxh): the witnesses' resources *)

Definition buf_ok (ws: list ptr_witness) (sh: share) (n: Z) (p: val) : Prop :=
  sepcon (pws_pred ws) (data_at_ sh (tarray tuchar n) p) |--
    andp (weak_valid_pointer p) (weak_valid_pointer (offset_val n p)).

(* ... and of the caller's memory of a dictionary used by reference: zstd compares dst with the dictionary's
   end, defined only in ONE object (the laws' [dst | 1 | dict] layout: the dictionary at or after dst's
   end), or, for 0 bytes, between two strictly valid pointers (a copied DDict of 0 bytes refers to the
   caller's pointer) *)
Definition dict_ptr_ok (W: list ptr_witness) (sh: share) (n: Z) (p: val) (shd: share) (cap: Z) (dst: val) : Prop :=
  (sameblock dst p = true /\
   match dst, p with Vptr _ o1, Vptr _ o2 => Ptrofs.unsigned o1 + cap <= Ptrofs.unsigned o2 | _, _ => False end /\
   buf_ok W sh n p) \/
  (n = 0 /\ (pws_pred W |-- valid_pointer p) /\
   (sepcon (pws_pred W) (data_at_ shd (tarray tuchar cap) dst) |-- valid_pointer dst)).

(* the caller's dictionary for ZSTD_decompress_usingDict: as dict_ptr_ok, or before dst in the same object with any
   gap [dict | gap | dst].  With no gap (and a non-empty dictionary), zstd finds dst contiguous with the dictionary
   and decodes with the dictionary as the prefix of dst's output: the two are then one array of the same share
   (of at most 2^63 - 1 bytes) *)
Definition dict_ptr_ok_any (W: list ptr_witness) (sh: share) (n: Z) (p: val) (shd: share) (cap: Z) (dst: val) : Prop :=
  dict_ptr_ok W sh n p shd cap dst \/
  (sameblock dst p = true /\
   match dst, p with
   | Vptr _ o1, Vptr _ o2 =>
       Ptrofs.unsigned o2 + n <= Ptrofs.unsigned o1 /\
       (0 < n -> Ptrofs.unsigned o2 + n = Ptrofs.unsigned o1 -> sh = shd /\ n + cap <= 2 ^ 63 - 1)
   | _, _ => False
   end /\
   buf_ok W sh n p).

Definition dict_buf_ok (W: list ptr_witness) (sh: share) (d: option dictref) (shd: share) (cap: Z) (dst: val) : Prop :=
  match d with
  | Some d => match dr_src d with
              | DSRef p => dict_ptr_ok W sh (Zlength (dr_bytes d)) p shd cap dst
              | DSDDict _ dd =>
                  match dd_ref dd with Some p => dict_ptr_ok W sh (Zlength (dd_bytes dd)) p shd cap dst | None => True end
              | _ => True
              end
  | None => True
  end.

(* the DDicts of the set other than the context's current one (whose memory dict_res holds) *)
Definition cur_ddict (d: option dictref) : option val :=
  match d with Some r => match dr_src r with DSDDict q _ => Some q | _ => None end | None => None end.

Definition set_res (gv: globals) (sh: share) (l: list (val * ddict_st)) (cur: option dictref) : mpred :=
  fold_right sepcon emp
    (map (fun e => match cur_ddict cur with
                   | Some q => if Val.eq (fst e) q then emp else ddict_res gv sh (fst e) (snd e)
                   | None => ddict_res gv sh (fst e) (snd e)
                   end) l).

(* the dictionaries a stream may use: zstd's own copies (a DDict made by copy, or loaded into the context by
   copy), or a DDict of 0 bytes at a strictly valid caller pointer (zstd compares it with its stream buffer),
   used for every frame (not a prefix used once); no buffer-less frame begun *)
Definition sddict_ok (W: list ptr_witness) (dd: ddict_st) : Prop :=
  match dd_ref dd with None => True | Some p => dd_bytes dd = nil /\ (pws_pred W |-- valid_pointer p) end.

Definition stream_dict_ok (W: list ptr_witness) (st: dctx_st) : Prop :=
  match dc_dict st with
  | None => True
  | Some d => dr_once d = false /\
      match dr_src d with
      | DSOwn => True
      | DSDDict _ dd => sddict_ok W dd
      | DSRef _ => False
      end
  end /\ Forall (fun e => sddict_ok W (snd e)) (dc_set st) /\ dc_bl st = None.

Definition ddict_buf_ok (W: list ptr_witness) (sh: share) (dd: ddict_st) (shd: share) (cap: Z) (dst: val) : Prop :=
  match dd_ref dd with Some p => dict_ptr_ok W sh (Zlength (dd_bytes dd)) p shd cap dst | None => True end.

(* ---------- one-shot decoding ---------- *)

(* v3: under the parameters' model md (model/Params.v); oneshot_ok2 is the v2 form (oneshot_ok_dflt) *)
Definition oneshot_ok (md: dmode) (odm: option dict_model) (s: list Z) (cap r: Z) (out: list val) : Prop :=
  (is_error_code r = false -> r <= cap) /\
  match odm with
  | None => True
  | Some dm =>
      match decode_series_m md sel_none (Some dm) no_wlim s with
      | SOk c => (is_error_code r = false -> r = Zlength c /\ sublist 0 r out = zbytes c) /\
                 (is_error_code r = true -> cap < Zlength c \/ r = err_code ZSTD_error_memory_allocation)
      | SDet => is_error_code r = true
      | SUnk => series_refused_m md sel_none (Some dm) no_wlim s -> is_error_code r = true
      end
  end.

(* with the selection of the DDict set: frames through sel, the current dictionary cur (None: not known) *)
Definition oneshot_sel (md: dmode) (sel: Z -> option dict_model) (cur: option dict_model) (s: list Z) (cap r: Z)
    (out: list val) : Prop :=
  (is_error_code r = false -> r <= cap) /\
  match decode_series_m md sel cur no_wlim s with
  | SOk c => (is_error_code r = false -> r = Zlength c /\ sublist 0 r out = zbytes c) /\
             (is_error_code r = true -> cap < Zlength c \/ r = err_code ZSTD_error_memory_allocation)
  | SDet => is_error_code r = true
  | SUnk => series_refused_m md sel cur no_wlim s -> is_error_code r = true
  end.

(* ZSTD_decompressDCtx's claims: without a set, the context's dictionary; with one, the selection *)
Definition oneshot_dctx (st: dctx_st) (s: list Z) (cap r: Z) (out: list val) : Prop :=
  match dc_set st with
  | nil => oneshot_ok (dmode_of (dc_par st)) (dictref_model (dc_dict st)) s cap r out
  | _ :: _ => oneshot_sel (dmode_of (dc_par st)) (fst (st_sel st)) (snd (st_sel st)) s cap r out
  end.

Definition oneshot_ok2 (odm: option dict_model) (s: list Z) (cap r: Z) (out: list val) : Prop :=
  (is_error_code r = false -> r <= cap) /\
  match odm with
  | None => True
  | Some dm =>
      match decode_series dm no_wlim s with
      | SOk c => (is_error_code r = false -> r = Zlength c /\ sublist 0 r out = zbytes c) /\
                 (is_error_code r = true -> cap < Zlength c \/ r = err_code ZSTD_error_memory_allocation)
      | SDet => is_error_code r = true
      | SUnk => True
      end
  end.

Definition ZSTD_decompress_spec : ident * funspec :=
  DECLARE _ZSTD_decompress
  WITH W: list ptr_witness, gv: globals, shd: share, dst: val, cap: Z, shs: share, src: val, s: list Z
  PRE [ tptr tvoid, tulong, tptr tvoid, tulong ]
    PROP (buf_ok W shd cap dst; buf_ok W shs (Zlength s) src; writable_share shd; readable_share shs; 0 <= cap <= 2 ^ 63 - 1; Zlength s <= 2 ^ 63 - 1; bytes_ok s)
    PARAMS (dst; Vlong (Int64.repr cap); src; Vlong (Int64.repr (Zlength s)))
    GLOBALS (gv)
    SEP (pws_pred W; mem_mgr gv; zstd_globals gv;
         mbuf shd cap (Zrepeat Vundef cap) dst;
         data_at shs (tarray tuchar (Zlength s)) (zbytes s) src)
  POST [ tulong ]
    EX r: Z, EX out: list val,
    PROP (0 <= r <= Int64.max_unsigned; Zlength out = cap; oneshot_ok md_dflt (Some no_dict) s cap r out;
          oneshot_codes md_dflt sel_none (Some no_dict) s cap r)
    RETURN (Vlong (Int64.repr r))
    SEP (pws_pred W; mem_mgr gv; zstd_globals gv;
         mbuf shd cap out dst;
         data_at shs (tarray tuchar (Zlength s)) (zbytes s) src).

(* ZSTD_decompressDCtx: with the context's dictionary (sticky, or once) *)
(* the configuration of a new context: no dictionary, default parameters, no DDict set, buffered output, and a
   stream that only its calls since the context was new (or reset with the parameters) have shaped *)
Definition fresh_cfg (st: dctx_st) : Prop :=
  dc_dict st = None /\ dc_par st = dparams_dflt /\ dc_set st = nil /\ dc_stable st = false /\ dc_ex st = true.

(* ZSTD_decompressDCtx from that configuration: exactly model/Exact.v's os_res, up to a memory-allocation error *)
Definition oneshot_exact (st: dctx_st) (s: list Z) (cap r: Z) (out: list val) : Prop :=
  fresh_cfg st -> r = err_code ZSTD_error_memory_allocation \/
  match os_res s cap with
  | None => is_error_code r = true
  | Some c => r = Zlength c /\ sublist 0 r out = zbytes c
  end.

Definition ZSTD_decompressDCtx_spec : ident * funspec :=
  DECLARE _ZSTD_decompressDCtx
  WITH W: list ptr_witness, gv: globals, d: val, st: dctx_st, shk: share,
       shd: share, dst: val, cap: Z, shs: share, src: val, s: list Z
  PRE [ tptr t_dctx, tptr tvoid, tulong, tptr tvoid, tulong ]
    PROP (buf_ok W shd cap dst; buf_ok W shs (Zlength s) src; dict_buf_ok W shk (dc_dict st) shd cap dst;
          Forall (fun e => ddict_buf_ok W shk (snd e) shd cap dst) (dc_set st); writable_share shd; readable_share shs; readable_share shk; dc_bl st = None;
          0 <= cap <= 2 ^ 63 - 1; Zlength s <= 2 ^ 63 - 1; bytes_ok s)
    PARAMS (d; dst; Vlong (Int64.repr cap); src; Vlong (Int64.repr (Zlength s)))
    GLOBALS (gv)
    SEP (pws_pred W; mem_mgr gv; zstd_globals gv; DC gv d st; dict_res gv shk (dc_dict st);
         set_res gv shk (dc_set st) (dc_dict st);
         mbuf shd cap (Zrepeat Vundef cap) dst;
         data_at shs (tarray tuchar (Zlength s)) (zbytes s) src)
  POST [ tulong ]
    EX r: Z, EX out: list val, EX st': dctx_st,
    PROP (0 <= r <= Int64.max_unsigned; Zlength out = cap;
          oneshot_dctx st s cap r out;
          oneshot_after st st';
          (* the error codes, for a context without a DDict set *)
          dc_set st = nil -> oneshot_codes (dmode_of (dc_par st)) sel_none (dictref_model (dc_dict st)) s cap r;
          (* the exact result from the configuration of a new context *)
          oneshot_exact st s cap r out)
    RETURN (Vlong (Int64.repr r))
    SEP (pws_pred W; mem_mgr gv; zstd_globals gv; DC gv d st'; dict_res gv shk (dc_dict st);
         set_res gv shk (dc_set st) (dc_dict st);
         mbuf shd cap out dst;
         data_at shs (tarray tuchar (Zlength s)) (zbytes s) src).

(* ZSTD_decompress_usingDict: the dictionary b at pk (ZSTD_dct_auto); the context's own is not used *)
Definition ZSTD_decompress_usingDict_spec : ident * funspec :=
  DECLARE _ZSTD_decompress_usingDict
  WITH W: list ptr_witness, gv: globals, d: val, st: dctx_st,
       shd: share, dst: val, cap: Z, shs: share, src: val, s: list Z, shk: share, pk: val, b: list Z
  PRE [ tptr t_dctx, tptr tvoid, tulong, tptr tvoid, tulong, tptr tvoid, tulong ]
    PROP (buf_ok W shd cap dst; buf_ok W shs (Zlength s) src; dict_ptr_ok_any W shk (Zlength b) pk shd cap dst; writable_share shd; readable_share shs; readable_share shk; dc_ss st = ss_init; dc_bl st = None; dc_set st = nil;
          0 <= cap <= 2 ^ 63 - 1; Zlength s <= 2 ^ 63 - 1; bytes_ok s; Zlength b <= 2 ^ 63 - 1; bytes_ok b)
    PARAMS (d; dst; Vlong (Int64.repr cap); src; Vlong (Int64.repr (Zlength s));
            pk; Vlong (Int64.repr (Zlength b)))
    GLOBALS (gv)
    SEP (pws_pred W; mem_mgr gv; zstd_globals gv; DC gv d st;
         data_at shk (tarray tuchar (Zlength b)) (zbytes b) pk;
         data_at_ shd (tarray tuchar cap) dst;
         data_at shs (tarray tuchar (Zlength s)) (zbytes s) src)
  POST [ tulong ]
    EX r: Z, EX out: list val, EX st': dctx_st,
    PROP (0 <= r <= Int64.max_unsigned; Zlength out = cap;
          oneshot_ok (dmode_of (dc_par st)) (dict_auto b) s cap r out;
          after_decode st st' (if Zlength b =? 0 then None
            else Some {| dr_src := DSRef pk; dr_raw := false; dr_once := false; dr_bytes := b |}))
    RETURN (Vlong (Int64.repr r))
    SEP (pws_pred W; mem_mgr gv; zstd_globals gv; DC gv d st';
         data_at shk (tarray tuchar (Zlength b)) (zbytes b) pk;
         data_at shd (tarray tuchar cap) out dst;
         data_at shs (tarray tuchar (Zlength s)) (zbytes s) src).

Definition ZSTD_decompress_usingDDict_spec : ident * funspec :=
  DECLARE _ZSTD_decompress_usingDDict
  WITH W: list ptr_witness, gv: globals, d: val, st: dctx_st,
       shd: share, dst: val, cap: Z, shs: share, src: val, s: list Z, shk: share, q: val, dd: ddict_st
  PRE [ tptr t_dctx, tptr tvoid, tulong, tptr tvoid, tulong, tptr t_ddict ]
    PROP (buf_ok W shd cap dst; buf_ok W shs (Zlength s) src; ddict_buf_ok W shk dd shd cap dst; writable_share shd; readable_share shs; readable_share shk; dc_ss st = ss_init; dc_bl st = None; dc_set st = nil;
          0 <= cap <= 2 ^ 63 - 1; Zlength s <= 2 ^ 63 - 1; bytes_ok s)
    PARAMS (d; dst; Vlong (Int64.repr cap); src; Vlong (Int64.repr (Zlength s)); q)
    GLOBALS (gv)
    SEP (pws_pred W; mem_mgr gv; zstd_globals gv; DC gv d st; ddict_res gv shk q dd;
         data_at_ shd (tarray tuchar cap) dst;
         data_at shs (tarray tuchar (Zlength s)) (zbytes s) src)
  POST [ tulong ]
    EX r: Z, EX out: list val, EX st': dctx_st,
    PROP (0 <= r <= Int64.max_unsigned; Zlength out = cap;
          oneshot_ok (dmode_of (dc_par st)) (dict_auto (dd_bytes dd)) s cap r out;
          after_decode st st' (Some (ddict_ref q dd)))
    RETURN (Vlong (Int64.repr r))
    SEP (pws_pred W; mem_mgr gv; zstd_globals gv; DC gv d st'; ddict_res gv shk q dd;
         data_at shd (tarray tuchar cap) out dst;
         data_at shs (tarray tuchar (Zlength s)) (zbytes s) src).

(* ---------- contexts ---------- *)

Definition ZSTD_createDCtx_spec : ident * funspec :=
  DECLARE _ZSTD_createDCtx
  WITH gv: globals
  PRE [ ]
    PROP () PARAMS () GLOBALS (gv)
    SEP (mem_mgr gv; zstd_globals gv)
  POST [ tptr t_dctx ]
    EX p: val,
    PROP (is_pointer_or_null p)
    RETURN (p)
    SEP (mem_mgr gv; zstd_globals gv; if eq_dec p nullval then emp else (DC gv p dctx_init && valid_pointer p)).

Definition ZSTD_createDStream_spec : ident * funspec :=
  DECLARE _ZSTD_createDStream
  WITH gv: globals
  PRE [ ]
    PROP () PARAMS () GLOBALS (gv)
    SEP (mem_mgr gv; zstd_globals gv)
  POST [ tptr t_dctx ]
    EX p: val,
    PROP (is_pointer_or_null p)
    RETURN (p)
    SEP (mem_mgr gv; zstd_globals gv; if eq_dec p nullval then emp else (DC gv p dctx_init && valid_pointer p)).

(* ZSTD_createDCtx_advancedP(&mem) (patch/lawhooks.py) with a context's own allocator m: the two functions and the
   opaque pointer at pm, nothing given out yet, room for the context (zstd allocates it zeroed through
   customAlloc); NULL (allocation failed) gives everything back *)
Definition ZSTD_createDCtx_advancedP_spec : ident * funspec :=
  DECLARE _ZSTD_createDCtx_advancedP
  WITH gv: globals, shm: share, pm: val, m: cmem
  PRE [ tptr (Tstruct ___gp_ZSTD_customMem noattr) ]
    PROP (readable_share shm; dctx_size <= cm_bound m; is_pointer_or_null (cm_opaque m))
    PARAMS (pm) GLOBALS (gv)
    SEP (mem_mgr gv; zstd_globals gv; data_at shm (Tstruct ___gp_ZSTD_customMem noattr) (cmem_val m) pm;
         cm_funs m; CM (cm_opaque m) (cm_bound m) 0)
  POST [ tptr t_dctx ]
    EX p: val,
    PROP (is_pointer_or_null p)
    RETURN (p)
    SEP (mem_mgr gv; zstd_globals gv; data_at shm (Tstruct ___gp_ZSTD_customMem noattr) (cmem_val m) pm;
         if eq_dec p nullval then (cm_funs m * CM (cm_opaque m) (cm_bound m) 0)%logic
         else DC gv p (dctx_init_m m) && valid_pointer p).

(* what freeing a context gives back besides its memory: the state of its own allocator, with nothing given out *)
Definition cm_back (ost: option dctx_st) : mpred :=
  match ost with
  | Some st => match dc_mem st with Some m => (cm_funs m * CM (cm_opaque m) (cm_bound m) 0)%logic | None => emp end
  | None => emp
  end.

(* free: NULL (ost = None) or a context in any state *)
Definition ZSTD_freeDCtx_spec : ident * funspec :=
  DECLARE _ZSTD_freeDCtx
  WITH gv: globals, p: val, ost: option dctx_st
  PRE [ tptr t_dctx ]
    PROP (match ost with None => p = nullval | Some _ => True end)
    PARAMS (p) GLOBALS (gv)
    SEP (mem_mgr gv; zstd_globals gv; match ost with None => emp | Some st => DC gv p st end)
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr 0)) SEP (mem_mgr gv; zstd_globals gv; cm_back ost).

Definition ZSTD_freeDStream_spec : ident * funspec :=
  DECLARE _ZSTD_freeDStream
  WITH gv: globals, p: val, ost: option dctx_st
  PRE [ tptr t_dctx ]
    PROP (match ost with None => p = nullval | Some _ => True end)
    PARAMS (p) GLOBALS (gv)
    SEP (mem_mgr gv; zstd_globals gv; match ost with None => emp | Some st => DC gv p st end)
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr 0)) SEP (mem_mgr gv; zstd_globals gv; cm_back ost).

(* ZSTD_DCtx_reset(d, dir), any of the three directives (reset_post) *)
Definition ZSTD_DCtx_reset_spec : ident * funspec :=
  DECLARE _ZSTD_DCtx_reset
  WITH gv: globals, d: val, st: dctx_st, dir: Z
  PRE [ tptr t_dctx, tint ]
    PROP (dir = ZSTD_reset_session_only \/ dir = ZSTD_reset_parameters \/ dir = ZSTD_reset_session_and_parameters)
    PARAMS (d; Vint (Int.repr dir)) GLOBALS (gv)
    SEP (mem_mgr gv; zstd_globals gv; DC gv d st)
  POST [ tulong ]
    EX r: Z, EX st': dctx_st,
    PROP (0 <= r <= Int64.max_unsigned; reset_post dir st r st')
    RETURN (Vlong (Int64.repr r))
    SEP (mem_mgr gv; zstd_globals gv; DC gv d st').

(* ZSTD_initDStream: a new stream without dictionary; returns the first input size hint
   (ZSTD_startingInputLength of the context's format) *)
Definition ZSTD_initDStream_spec : ident * funspec :=
  DECLARE _ZSTD_initDStream
  WITH gv: globals, d: val, st: dctx_st
  PRE [ tptr t_dctx ]
    PROP () PARAMS (d) GLOBALS (gv)
    SEP (mem_mgr gv; zstd_globals gv; DC gv d st)
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr (starting_len (dp_fmt (dc_par st) =? 1))))
    SEP (mem_mgr gv; zstd_globals gv; DC gv d (set_ex (set_ss (set_dict st None) ss_init) false)).

(* ZSTD_DCtx_setParameter(d, k, v) for the parameters the laws use, ANY int v: the new parameters, or None
   (zstd returns an error and changes nothing: a value out of the parameter's bounds) *)
Definition param_set (p: dparams) (k v: Z) : option dparams :=
  if k =? ZSTD_d_windowLogMax then
    let v' := if v =? 0 then 27 else v in
    if ((10 <=? v') && (v' <=? 31))%bool
    then Some {| dp_fmt := dp_fmt p; dp_ignore := dp_ignore p; dp_bmax := dp_bmax p; dp_wmax := 2 ^ v';
                 dp_multi := dp_multi p |}
    else None
  else if k =? ZSTD_d_format then
    if ((0 <=? v) && (v <=? 1))%bool
    then Some {| dp_fmt := v; dp_ignore := dp_ignore p; dp_bmax := dp_bmax p; dp_wmax := dp_wmax p;
                 dp_multi := dp_multi p |}
    else None
  else if k =? ZSTD_d_forceIgnoreChecksum then
    if ((0 <=? v) && (v <=? 1))%bool
    then Some {| dp_fmt := dp_fmt p; dp_ignore := v; dp_bmax := dp_bmax p; dp_wmax := dp_wmax p;
                 dp_multi := dp_multi p |}
    else None
  else if k =? ZSTD_d_refMultipleDDicts then
    if ((0 <=? v) && (v <=? 1))%bool
    then Some {| dp_fmt := dp_fmt p; dp_ignore := dp_ignore p; dp_bmax := dp_bmax p; dp_wmax := dp_wmax p;
                 dp_multi := v |}
    else None
  else if k =? ZSTD_d_maxBlockSize then
    if ((v =? 0) || ((1024 <=? v) && (v <=? ZSTD_BLOCKSIZE_MAX)))%bool
    then Some {| dp_fmt := dp_fmt p; dp_ignore := dp_ignore p; dp_bmax := v; dp_wmax := dp_wmax p;
                 dp_multi := dp_multi p |}
    else None
  else None.

(* ZSTD_DCtx_setParameter(d, k, v) before a stream starts: ZSTD_d_stableOutBuffer (v = 0 or 1, else an
   error) or one of param_set's parameters *)
Definition setpar_res (k v: Z) (st: dctx_st) (r: Z) (st': dctx_st) : Prop :=
  if k =? ZSTD_d_stableOutBuffer then
    (if ((0 <=? v) && (v <=? 1))%bool then r = 0 /\ st' = set_stable st (v =? 1)
     else is_error_code r = true /\ st' = st)
  else match param_set (dc_par st) k v with
       | Some p' => r = 0 /\ st' = set_par st p'
       | None => is_error_code r = true /\ st' = st
       end.

(* ... and after any use (after_stage: refused while a frame is being streamed) *)
Definition ZSTD_DCtx_setParameter_spec : ident * funspec :=
  DECLARE _ZSTD_DCtx_setParameter
  WITH gv: globals, d: val, st: dctx_st, k: Z, v: Z
  PRE [ tptr t_dctx, tint, tint ]
    PROP (In k [ZSTD_d_windowLogMax; ZSTD_d_format; ZSTD_d_stableOutBuffer; ZSTD_d_forceIgnoreChecksum;
                ZSTD_d_refMultipleDDicts; ZSTD_d_maxBlockSize];
          Int.min_signed <= v <= Int.max_signed; dc_bl st = None)
    PARAMS (d; Vint (Int.repr k); Vint (Int.repr v)) GLOBALS (gv)
    SEP (mem_mgr gv; zstd_globals gv; DC gv d st)
  POST [ tulong ]
    EX r: Z, EX st': dctx_st,
    PROP (0 <= r <= Int64.max_unsigned; after_stage (setpar_res k v) st r st')
    RETURN (Vlong (Int64.repr r))
    SEP (mem_mgr gv; zstd_globals gv; DC gv d st').

(* ZSTD_DCtx_setFormat(d, f): ZSTD_DCtx_setParameter(d, ZSTD_d_format, f) *)
Definition ZSTD_DCtx_setFormat_aspec : ident * funspec :=
  DECLARE _ZSTD_DCtx_setFormat
  WITH gv: globals, d: val, st: dctx_st, v: Z
  PRE [ tptr t_dctx, tint ]
    PROP (Int.min_signed <= v <= Int.max_signed; dc_ss st = ss_init; dc_bl st = None)
    PARAMS (d; Vint (Int.repr v)) GLOBALS (gv)
    SEP (mem_mgr gv; zstd_globals gv; DC gv d st)
  POST [ tulong ]
    EX r: Z, EX st': dctx_st,
    PROP (0 <= r <= Int64.max_unsigned;
          match param_set (dc_par st) ZSTD_d_format v with
          | Some p' => r = 0 /\ st' = set_par st p'
          | None => is_error_code r = true /\ st' = st
          end)
    RETURN (Vlong (Int64.repr r))
    SEP (mem_mgr gv; zstd_globals gv; DC gv d st').

(* ZSTD_DCtx_setMaxWindowSize(d, m): within [2^10, 2^31] (the bounds of ZSTD_d_windowLogMax), else an error *)
Definition ZSTD_DCtx_setMaxWindowSize_aspec : ident * funspec :=
  DECLARE _ZSTD_DCtx_setMaxWindowSize
  WITH gv: globals, d: val, st: dctx_st, m: Z
  PRE [ tptr t_dctx, tulong ]
    PROP (0 <= m <= Int64.max_unsigned; dc_ss st = ss_init; dc_bl st = None)
    PARAMS (d; Vlong (Int64.repr m)) GLOBALS (gv)
    SEP (mem_mgr gv; zstd_globals gv; DC gv d st)
  POST [ tulong ]
    EX r: Z, EX st': dctx_st,
    PROP (0 <= r <= Int64.max_unsigned;
          if ((2 ^ 10 <=? m) && (m <=? 2 ^ 31))%bool
          then r = 0 /\ st' = set_par st {| dp_fmt := dp_fmt (dc_par st); dp_ignore := dp_ignore (dc_par st);
                                            dp_bmax := dp_bmax (dc_par st); dp_wmax := m;
                                            dp_multi := dp_multi (dc_par st) |}
          else is_error_code r = true /\ st' = st)
    RETURN (Vlong (Int64.repr r))
    SEP (mem_mgr gv; zstd_globals gv; DC gv d st').

(* ZSTD_resetDStream: ZSTD_DCtx_reset(d, ZSTD_reset_session_only); returns ZSTD_startingInputLength *)
Definition ZSTD_resetDStream_aspec : ident * funspec :=
  DECLARE _ZSTD_resetDStream
  WITH gv: globals, d: val, st: dctx_st
  PRE [ tptr t_dctx ]
    PROP () PARAMS (d) GLOBALS (gv)
    SEP (mem_mgr gv; zstd_globals gv; DC gv d st)
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr (starting_len (dp_fmt (dc_par st) =? 1))))
    SEP (mem_mgr gv; zstd_globals gv; DC gv d (set_ex (set_ss st ss_init) false)).

Definition ZSTD_DStreamOutSize_spec : ident * funspec :=
  DECLARE _ZSTD_DStreamOutSize
  WITH u: unit
  PRE [ ]
    PROP () PARAMS () SEP ()
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr ZSTD_BLOCKSIZE_MAX)) SEP ().

(* ---------- dictionaries ---------- *)

(* by copy; the bytes may be NULL for none (ZSTD_createDDict(NULL, 0): a DDict without content, which refers to
   nothing of the caller's) *)
Definition ZSTD_createDDict_spec : ident * funspec :=
  DECLARE _ZSTD_createDDict
  WITH W: list ptr_witness, gv: globals, sh: share, p: val, b: list Z
  PRE [ tptr tvoid, tulong ]
    PROP (is_pointer_or_null p; p = nullval -> b = nil; p <> nullval -> buf_ok W sh (Zlength b) p;
          readable_share sh; Zlength b <= 2 ^ 63 - 1; bytes_ok b)
    PARAMS (p; Vlong (Int64.repr (Zlength b))) GLOBALS (gv)
    SEP (pws_pred W; mem_mgr gv; zstd_globals gv; bytes_at sh b p)
  POST [ tptr t_ddict ]
    EX q: val, EX dd: ddict_st,
    PROP (is_pointer_or_null q; dd_bytes dd = b;
          dd_ref dd = (if eq_dec p nullval then None else if Zlength b =? 0 then Some p else None))
    RETURN (q)
    SEP (pws_pred W; mem_mgr gv; zstd_globals gv; bytes_at sh b p;
         if eq_dec q nullval then emp else (DD gv q dd && valid_pointer q)).

Definition ZSTD_createDDict_byReference_spec : ident * funspec :=
  DECLARE _ZSTD_createDDict_byReference
  WITH W: list ptr_witness, gv: globals, sh: share, p: val, b: list Z
  PRE [ tptr tvoid, tulong ]
    PROP (buf_ok W sh (Zlength b) p; readable_share sh; Zlength b <= 2 ^ 63 - 1; bytes_ok b)
    PARAMS (p; Vlong (Int64.repr (Zlength b))) GLOBALS (gv)
    SEP (pws_pred W; mem_mgr gv; zstd_globals gv; data_at sh (tarray tuchar (Zlength b)) (zbytes b) p)
  POST [ tptr t_ddict ]
    EX q: val, EX dd: ddict_st,
    PROP (is_pointer_or_null q; dd_bytes dd = b; dd_ref dd = Some p)
    RETURN (q)
    SEP (pws_pred W; mem_mgr gv; zstd_globals gv; data_at sh (tarray tuchar (Zlength b)) (zbytes b) p;
         if eq_dec q nullval then emp else (DD gv q dd && valid_pointer q)).

Definition ZSTD_freeDDict_spec : ident * funspec :=
  DECLARE _ZSTD_freeDDict
  WITH gv: globals, q: val, odd: option ddict_st
  PRE [ tptr t_ddict ]
    PROP (match odd with None => q = nullval | Some _ => True end)
    PARAMS (q) GLOBALS (gv)
    SEP (mem_mgr gv; zstd_globals gv; match odd with None => emp | Some dd => DD gv q dd end)
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr 0)) SEP (mem_mgr gv; zstd_globals gv).

Definition ZSTD_getDictID_fromDDict_spec : ident * funspec :=
  DECLARE _ZSTD_getDictID_fromDDict
  WITH gv: globals, q: val, dd: ddict_st
  PRE [ tptr t_ddict ]
    PROP () PARAMS (q) GLOBALS (gv)
    SEP (DD gv q dd)
  POST [ tuint ]
    PROP () RETURN (Vint (Int.repr (dict_id_of (dd_bytes dd)))) SEP (DD gv q dd && valid_pointer q).

Definition ZSTD_getDictID_fromDict_spec : ident * funspec :=
  DECLARE _ZSTD_getDictID_fromDict
  WITH sh: share, p: val, b: list Z
  PRE [ tptr tvoid, tulong ]
    PROP (readable_share sh; Zlength b <= 2 ^ 30; bytes_ok b)
    PARAMS (p; Vlong (Int64.repr (Zlength b)))
    SEP (data_at sh (tarray tuchar (Zlength b)) (zbytes b) p)
  POST [ tuint ]
    PROP () RETURN (Vint (Int.repr (dict_id_of b)))
    SEP (data_at sh (tarray tuchar (Zlength b)) (zbytes b) p).

(* load a dictionary into a context (sticky): by reference (the caller keeps b at p), or by copy.  The functions
   that attach a dictionary to a context (they allocate a ZSTD_DDict or the DDict set through the context's
   allocator) are specified for contexts with the default allocator: dc_mem st = None *)
Definition load_result (st st': dctx_st) (r: Z) (dr: dictref) : Prop :=
  (r = 0 /\ st' = set_dict st (Some dr)) \/
  (is_error_code r = true /\ st' = set_dict st None /\
   ((dr_raw dr = false /\ dict_auto (dr_bytes dr) = None) \/ r = err_code ZSTD_error_memory_allocation)).

Definition ZSTD_DCtx_loadDictionary_byReference_spec : ident * funspec :=
  DECLARE _ZSTD_DCtx_loadDictionary_byReference
  WITH W: list ptr_witness, gv: globals, d: val, st: dctx_st, sh: share, p: val, b: list Z
  PRE [ tptr t_dctx, tptr tvoid, tulong ]
    PROP (buf_ok W sh (Zlength b) p; readable_share sh; dc_ss st = ss_init; dc_bl st = None; Zlength b <= 2 ^ 63 - 1; bytes_ok b;
          dc_mem st = None)
    PARAMS (d; p; Vlong (Int64.repr (Zlength b))) GLOBALS (gv)
    SEP (pws_pred W; mem_mgr gv; zstd_globals gv; DC gv d st; data_at sh (tarray tuchar (Zlength b)) (zbytes b) p)
  POST [ tulong ]
    EX r: Z, EX st': dctx_st,
    PROP (0 <= r <= Int64.max_unsigned;
          load_result st st' r {| dr_src := DSRef p; dr_raw := false; dr_once := false; dr_bytes := b |})
    RETURN (Vlong (Int64.repr r))
    SEP (pws_pred W; mem_mgr gv; zstd_globals gv; DC gv d st'; data_at sh (tarray tuchar (Zlength b)) (zbytes b) p).

(* by copy, after any use (after_stage), into a context with any allocator (its own allocates the copy: cm_raised) *)
Definition ZSTD_DCtx_loadDictionary_spec : ident * funspec :=
  DECLARE _ZSTD_DCtx_loadDictionary
  WITH W: list ptr_witness, gv: globals, d: val, st: dctx_st, sh: share, p: val, b: list Z
  PRE [ tptr t_dctx, tptr tvoid, tulong ]
    PROP (buf_ok W sh (Zlength b) p; readable_share sh; dc_bl st = None; Zlength b <= 2 ^ 63 - 1; bytes_ok b)
    PARAMS (d; p; Vlong (Int64.repr (Zlength b))) GLOBALS (gv)
    SEP (pws_pred W; mem_mgr gv; zstd_globals gv; DC gv d st; data_at sh (tarray tuchar (Zlength b)) (zbytes b) p)
  POST [ tulong ]
    EX r: Z, EX st': dctx_st,
    PROP (0 <= r <= Int64.max_unsigned;
          after_stage (fun st0 r0 st1 => exists om, cm_raised (dc_mem st0) om /\
            load_result (set_mem st0 om) st1 r0 {| dr_src := DSOwn; dr_raw := false; dr_once := false; dr_bytes := b |})
            st r st')
    RETURN (Vlong (Int64.repr r))
    SEP (pws_pred W; mem_mgr gv; zstd_globals gv; DC gv d st'; data_at sh (tarray tuchar (Zlength b)) (zbytes b) p).

(* ZSTD_DCtx_refPrefix: raw content, by reference, for the next decompression only *)
Definition ZSTD_DCtx_refPrefix_spec : ident * funspec :=
  DECLARE _ZSTD_DCtx_refPrefix
  WITH W: list ptr_witness, gv: globals, d: val, st: dctx_st, sh: share, p: val, b: list Z
  PRE [ tptr t_dctx, tptr tvoid, tulong ]
    PROP (buf_ok W sh (Zlength b) p; readable_share sh; dc_ss st = ss_init; dc_bl st = None; Zlength b <= 2 ^ 63 - 1; bytes_ok b;
          dc_mem st = None)
    PARAMS (d; p; Vlong (Int64.repr (Zlength b))) GLOBALS (gv)
    SEP (pws_pred W; mem_mgr gv; zstd_globals gv; DC gv d st; data_at sh (tarray tuchar (Zlength b)) (zbytes b) p)
  POST [ tulong ]
    EX r: Z, EX st': dctx_st,
    PROP (0 <= r <= Int64.max_unsigned;
          load_result st st' r {| dr_src := DSRef p; dr_raw := true; dr_once := true; dr_bytes := b |})
    RETURN (Vlong (Int64.repr r))
    SEP (pws_pred W; mem_mgr gv; zstd_globals gv; DC gv d st'; data_at sh (tarray tuchar (Zlength b)) (zbytes b) p).

(* ZSTD_DCtx_refDDict: the context references the DDict q (made from dd); with ZSTD_d_refMultipleDDicts on,
   q also joins the context's DDict set (set_add), which may fail for memory (the DDict is then referenced,
   the set unchanged) *)
Definition refddict_result (st st': dctx_st) (r: Z) (q: val) (dd: ddict_st) : Prop :=
  (r = 0 /\ st' = set_set (set_dict st (Some (ddict_ref q dd)))
                          (if dp_multi (dc_par st) =? 1 then set_add (dc_set st) q dd else dc_set st)) \/
  (dp_multi (dc_par st) = 1 /\ is_error_code r = true /\ st' = set_dict st (Some (ddict_ref q dd))).

(* v3.1: zstd reads the dictionary IDs of the set's DDicts (dict_res/set_res, as decoding); the set stays
   small (its table size is computed in size_t); q stays valid for the caller's NULL tests *)
Definition ZSTD_DCtx_refDDict_spec : ident * funspec :=
  DECLARE _ZSTD_DCtx_refDDict
  WITH gv: globals, d: val, st: dctx_st, q: val, dd: ddict_st, shk: share
  PRE [ tptr t_dctx, tptr t_ddict ]
    PROP (is_pointer_or_null q; dc_bl st = None; readable_share shk;
          Zlength (dc_set st) < 2 ^ 20)
    PARAMS (d; q) GLOBALS (gv)
    SEP (mem_mgr gv; zstd_globals gv; DC gv d st; if eq_dec q nullval then emp else DD gv q dd;
         dict_res gv shk (dc_dict st); set_res gv shk (dc_set st) (dc_dict st))
  POST [ tulong ]
    EX r: Z, EX st': dctx_st,
    PROP (0 <= r <= Int64.max_unsigned;
          after_stage (fun st0 r0 st1 =>
            if eq_dec q nullval then r0 = 0 /\ st1 = set_dict st0 None
            else exists om, cm_raised (dc_mem st0) om /\ refddict_result (set_mem st0 om) st1 r0 q dd) st r st')
    RETURN (Vlong (Int64.repr r))
    SEP (mem_mgr gv; zstd_globals gv; if eq_dec q nullval then emp else (DD gv q dd && valid_pointer q); DC gv d st';
         dict_res gv shk (dc_dict st); set_res gv shk (dc_set st) (dc_dict st)).

(* ZSTD_DCtx_loadDictionary_advanced(d, p, n, m, t): m = ZSTD_dlm_byCopy 0 / byRef 1, t = ZSTD_dct_auto 0 /
   rawContent 1 / fullDict 2 (fullDict refuses bytes without the magic number) *)
Definition load_result_adv (st st': dctx_st) (r t: Z) (dr: dictref) : Prop :=
  (r = 0 /\ st' = set_dict st (Some dr) /\
   (t = 2 -> dr_bytes dr <> nil -> dict_formatted (dr_bytes dr) = true)) \/
  (is_error_code r = true /\ st' = set_dict st None /\
   ((dr_raw dr = false /\ dict_auto (dr_bytes dr) = None) \/ (t = 2 /\ dict_formatted (dr_bytes dr) = false) \/
    r = err_code ZSTD_error_memory_allocation)).

Definition ZSTD_DCtx_loadDictionary_advanced_aspec : ident * funspec :=
  DECLARE _ZSTD_DCtx_loadDictionary_advanced
  WITH W: list ptr_witness, gv: globals, d: val, st: dctx_st, sh: share, p: val, b: list Z, m: Z, t: Z
  PRE [ tptr t_dctx, tptr tvoid, tulong, tint, tint ]
    PROP (buf_ok W sh (Zlength b) p; readable_share sh; dc_ss st = ss_init; dc_bl st = None; Zlength b <= 2 ^ 63 - 1; bytes_ok b;
          m = 0 \/ m = 1; t = 0 \/ t = 1 \/ t = 2;
          dc_mem st = None)
    PARAMS (d; p; Vlong (Int64.repr (Zlength b)); Vint (Int.repr m); Vint (Int.repr t)) GLOBALS (gv)
    SEP (pws_pred W; mem_mgr gv; zstd_globals gv; DC gv d st; data_at sh (tarray tuchar (Zlength b)) (zbytes b) p)
  POST [ tulong ]
    EX r: Z, EX st': dctx_st,
    PROP (0 <= r <= Int64.max_unsigned;
          load_result_adv st st' r t {| dr_src := if m =? 1 then DSRef p else DSOwn; dr_raw := t =? 1;
                                        dr_once := false; dr_bytes := b |})
    RETURN (Vlong (Int64.repr r))
    SEP (pws_pred W; mem_mgr gv; zstd_globals gv; DC gv d st'; data_at sh (tarray tuchar (Zlength b)) (zbytes b) p).

(* ZSTD_DCtx_refPrefix_advanced(d, p, n, t): by reference, content type t, for the next decompression only *)
Definition ZSTD_DCtx_refPrefix_advanced_aspec : ident * funspec :=
  DECLARE _ZSTD_DCtx_refPrefix_advanced
  WITH W: list ptr_witness, gv: globals, d: val, st: dctx_st, sh: share, p: val, b: list Z, t: Z
  PRE [ tptr t_dctx, tptr tvoid, tulong, tint ]
    PROP (buf_ok W sh (Zlength b) p; readable_share sh; dc_ss st = ss_init; dc_bl st = None; Zlength b <= 2 ^ 63 - 1; bytes_ok b;
          t = 0 \/ t = 1 \/ t = 2;
          dc_mem st = None)
    PARAMS (d; p; Vlong (Int64.repr (Zlength b)); Vint (Int.repr t)) GLOBALS (gv)
    SEP (pws_pred W; mem_mgr gv; zstd_globals gv; DC gv d st; data_at sh (tarray tuchar (Zlength b)) (zbytes b) p)
  POST [ tulong ]
    EX r: Z, EX st': dctx_st,
    PROP (0 <= r <= Int64.max_unsigned;
          load_result_adv st st' r t {| dr_src := DSRef p; dr_raw := t =? 1; dr_once := true; dr_bytes := b |})
    RETURN (Vlong (Int64.repr r))
    SEP (pws_pred W; mem_mgr gv; zstd_globals gv; DC gv d st'; data_at sh (tarray tuchar (Zlength b)) (zbytes b) p).

(* ZSTD_initDStream_usingDict(d, p, n): ZSTD_DCtx_reset(session only) + ZSTD_DCtx_loadDictionary (by copy);
   returns ZSTD_startingInputLength on success *)
Definition ZSTD_initDStream_usingDict_aspec : ident * funspec :=
  DECLARE _ZSTD_initDStream_usingDict
  WITH W: list ptr_witness, gv: globals, d: val, st: dctx_st, sh: share, p: val, b: list Z
  PRE [ tptr t_dctx, tptr tvoid, tulong ]
    PROP (buf_ok W sh (Zlength b) p; readable_share sh; dc_bl st = None; Zlength b <= 2 ^ 63 - 1; bytes_ok b;
          dc_mem st = None)
    PARAMS (d; p; Vlong (Int64.repr (Zlength b))) GLOBALS (gv)
    SEP (pws_pred W; mem_mgr gv; zstd_globals gv; DC gv d st; data_at sh (tarray tuchar (Zlength b)) (zbytes b) p)
  POST [ tulong ]
    EX r: Z, EX st': dctx_st,
    PROP (0 <= r <= Int64.max_unsigned;
          (r = starting_len (dp_fmt (dc_par st) =? 1) /\
           st' = set_dict (set_ex (set_ss st ss_init) false) (Some {| dr_src := DSOwn; dr_raw := false; dr_once := false; dr_bytes := b |})) \/
          (is_error_code r = true /\ st' = set_dict (set_ex (set_ss st ss_init) false) None /\
           (dict_auto b = None \/ r = err_code ZSTD_error_memory_allocation)))
    RETURN (Vlong (Int64.repr r))
    SEP (pws_pred W; mem_mgr gv; zstd_globals gv; DC gv d st'; data_at sh (tarray tuchar (Zlength b)) (zbytes b) p).

(* ZSTD_initDStream_usingDDict(d, q): ZSTD_DCtx_reset(session only) + ZSTD_DCtx_refDDict(d, q) *)
Definition ZSTD_initDStream_usingDDict_aspec : ident * funspec :=
  DECLARE _ZSTD_initDStream_usingDDict
  WITH gv: globals, d: val, st: dctx_st, q: val, dd: ddict_st, shk: share
  PRE [ tptr t_dctx, tptr t_ddict ]
    PROP (isptr q; dc_bl st = None; readable_share shk; Zlength (dc_set st) < 2 ^ 20;
          dc_mem st = None)
    PARAMS (d; q) GLOBALS (gv)
    SEP (mem_mgr gv; zstd_globals gv; DC gv d st; DD gv q dd;
         dict_res gv shk (dc_dict st); set_res gv shk (dc_set st) (dc_dict st))
  POST [ tulong ]
    EX r: Z, EX st': dctx_st, EX r0: Z,
    PROP (0 <= r <= Int64.max_unsigned; refddict_result (set_ex (set_ss st ss_init) false) st' r0 q dd;
          if is_error_code r0 then r = r0 else r = starting_len (dp_fmt (dc_par st) =? 1))
    RETURN (Vlong (Int64.repr r))
    SEP (mem_mgr gv; zstd_globals gv; (DD gv q dd && valid_pointer q); DC gv d st';
         dict_res gv shk (dc_dict st); set_res gv shk (dc_set st) (dc_dict st)).

(* ---------- streaming ---------- *)

(* One call: the caller's input bytes ibs[ipos..ipos') consumed (in.pos), output bytes dl delivered at
   oc'[opos..opos') (the cells are the bytes dl in stable mode, and in buffered mode while the bytes read
   can still begin a series the model decodes: on garbage, zstd's ring buffer may hand out cells it never
   wrote).  The bytes zstd read: ibs[ipos + a .. ipos' + a') with a, a' the read-ahead before and
   after the call (a hostage byte already read is skipped); the claims are on all bytes read, and errors
   on every series that also extends the unread rest of the chunk. *)
Definition stream_post (st st': dctx_st) (r: Z) (ob: val) (osz opos opos': Z) (oc oc': list val)
    (ibs: list Z) (isz ipos ipos': Z) : Prop :=
  let ss := dc_ss st in
  exists dl stall' a',
    let sin' := ss_in ss ++ sublist (ipos + ss_ahead ss) (ipos' + a') ibs in
    opos <= opos' <= osz /\ ipos <= ipos' <= isz /\ Zlength oc' = osz /\
    sublist 0 opos oc' = sublist 0 opos oc /\
    Zlength dl = opos' - opos /\
    (dc_stable st = true \/ stream_alive_m (dmode_w (dmode_of (dc_par st))) (fst (st_sel st)) (snd (st_sel st)) sin' ->
       sublist opos opos' oc' = zbytes dl /\ bytes_ok dl) /\
    0 <= a' <= 1 /\ ipos + ss_ahead ss <= ipos' + a' /\
    (ipos' + a' <= isz \/ ipos' + a' = ipos + ss_ahead ss) /\ (a' = 1 -> is_error_code r = false -> r = 1) /\
    st' = set_last
            (set_ss st {| ss_in := sin'; ss_out := ss_out ss ++ dl;
                          ss_stall := stall'; ss_err := is_error_code r;
                          ss_obuf := if dc_stable st then Some (ob, osz) else None; ss_ahead := a';
                          ss_calls := ss_calls ss ++ [(sublist ipos isz ibs, osz - opos)] |})
            (Some stream_mark) /\
    (is_error_code r = false -> (ipos' <> ipos \/ opos' <> opos) -> stall' = 0) /\
    (is_error_code r = false -> ipos' = ipos -> opos' = opos -> 0 <= stall' <= ss_stall ss + 1) /\
    (dc_stable st = false -> ipos = isz -> opos' - opos <= ZSTD_BLOCKSIZE_MAX) /\
    stall_ok r (ss_stall ss) ipos ipos' isz opos opos' osz /\
    stream_claims_m (dmode_w (dmode_of (dc_par st))) (fst (st_sel st)) (snd (st_sel st)) (dp_wmax (dc_par st))
      (sublist 0 (Zlength (ss_in ss) - ss_ahead ss) (ss_in ss)) (ss_out ss) sin' (sin' ++ sublist (ipos' + a') isz ibs) (ss_out ss ++ dl) a'
      (if dc_stable st then Some osz else None) r /\
    stream_zero_ref (dmode_w (dmode_of (dc_par st))) (fst (st_sel st)) (snd (st_sel st)) sin' (ss_out ss ++ dl) r.

(* the progress claim of one call (model/StreamProgress.v), on the bytes read before the call and delivered
   (ss_in includes a hostage byte), the bytes read after it then the unread rest of the call's input, and the
   stall count after it *)
Definition stream_progress (st st': dctx_st) (r osz opos opos' isz ipos ipos': Z) (ibs: list Z) : Prop :=
  stream_progress_m (dmode_w (dmode_of (dc_par st))) (fst (st_sel st)) (snd (st_sel st)) (dp_wmax (dc_par st))
    (ss_in (dc_ss st)) (ss_out (dc_ss st)) (ss_in (dc_ss st') ++ sublist (ipos' + ss_ahead (dc_ss st')) isz ibs)
    (ss_stall (dc_ss st')) r ipos ipos' isz opos opos' osz.

(* a return of 0 releases the hostage byte (the clause of stream_post with a' = 1 gives r = 1) *)
Lemma stream_hostage_zero: forall (a' r: Z),
  (a' = 1 -> is_error_code r = false -> r = 1) -> 0 <= a' <= 1 -> r = 0 -> a' = 0.
Proof.
  intros a' r H Ha Hr. subst r. destruct (Z.eq_dec a' 1) as [E|E].
  - specialize (H E eq_refl). discriminate.
  - lia.
Qed.

(* in buffered mode a call that returns no error leaves the output cells after the position it returns as they
   were: the flush copies exactly the bytes it delivers, and the single-pass shortcut decodes into exactly the
   frame's content size (fix F7) *)
Definition stream_untouched (st: dctx_st) (r osz opos': Z) (oc oc': list val) : Prop :=
  dc_stable st = false -> is_error_code r = false -> sublist opos' osz oc' = sublist opos' osz oc.

(* the stream after a call that returned r, consumed k of the bytes inp it could read, delivered dl, with zstd's
   noForwardProgress stall and hostage byte a after it *)
Definition ss_after (ss: sstate) (inp: list Z) (room r k: Z) (dl: list Z) (stall a: Z) : sstate :=
  {| ss_in := ss_in ss ++ sublist (ss_ahead ss) (k + a) inp; ss_out := ss_out ss ++ dl; ss_stall := stall;
     ss_err := is_error_code r; ss_obuf := None; ss_ahead := a; ss_calls := ss_calls ss ++ [(inp, room)] |}.

(* ZSTD_decompressStream from the configuration of a new context: exactly model/Exact.v's zs_call on the calls
   since the reset, up to a memory-allocation error.  The stall count of the next state is not zs_call's (zstd's
   noForwardProgress): a call that only releases the hostage byte after calls without progress moves in.pos but
   counts as one more call without progress, while stream_post's ss_stall is 0 after any call that moves *)
Definition stream_exact (st st': dctx_st) (r osz opos opos': Z) (oc': list val) (ibs: list Z) (isz ipos ipos': Z)
    : Prop :=
  fresh_cfg st -> r = err_code ZSTD_error_memory_allocation \/
  let inp := sublist ipos isz ibs in
  let room := osz - opos in
  match zs_call (ss_calls (dc_ss st)) (inp, room) with
  | None => is_error_code r = true
  | Some (r0, k, dl, _, a) =>
      r = r0 /\ ipos' = ipos + k /\ opos' = opos + Zlength dl /\ sublist opos opos' oc' = zbytes dl /\
      exists stall', st' = set_last (set_ss st (ss_after (dc_ss st) inp room r0 k dl stall' a)) (Some stream_mark)
  end.

Definition ZSTD_decompressStream_spec : ident * funspec :=
  DECLARE _ZSTD_decompressStream
  WITH W: list ptr_witness, gv: globals, d: val, st: dctx_st, outp: val, inp: val, sho: share, shi: share,
       shob: share, ob: val, osz: Z, opos: Z, oc: list val,
       shb: share, ib: val, isz: Z, ipos: Z, ibs: list Z
  PRE [ tptr t_dctx, tptr t_outBuffer, tptr t_inBuffer ]
    PROP (buf_ok W shob osz ob; buf_ok W shb isz ib;
          dc_stable st = true -> match ss_obuf (dc_ss st) with Some (ob', osz') => ob' = ob /\ osz' = osz | None => True end;
          dc_stable st = true -> opos = Zlength (ss_out (dc_ss st)) /\ sublist 0 opos oc = zbytes (ss_out (dc_ss st));
          writable_share sho; writable_share shi; writable_share shob; readable_share shb;
          stream_dict_ok W st; ss_err (dc_ss st) = false;
          0 <= opos <= osz; osz <= 2 ^ 63 - 1; Zlength oc = osz;
          0 <= ipos <= isz; isz <= 2 ^ 63 - 1; Zlength ibs = isz; bytes_ok ibs)
    PARAMS (d; outp; inp) GLOBALS (gv)
    SEP (pws_pred W; mem_mgr gv; zstd_globals gv; DC gv d st;
         dict_res gv Ews (dc_dict st); set_res gv Ews (dc_set st) (dc_dict st);
         data_at sho t_outBuffer (ob, (Vlong (Int64.repr osz), Vlong (Int64.repr opos))) outp;
         data_at shi t_inBuffer (ib, (Vlong (Int64.repr isz), Vlong (Int64.repr ipos))) inp;
         mbuf shob osz oc ob;
         mbuf shb isz (zbytes ibs) ib)
  POST [ tulong ]
    EX r: Z, EX opos': Z, EX ipos': Z, EX oc': list val, EX st': dctx_st,
    PROP (0 <= r <= Int64.max_unsigned;
          stream_post st st' r ob osz opos opos' oc oc' ibs isz ipos ipos';
          stream_progress st st' r osz opos opos' isz ipos ipos' ibs;
          stream_untouched st r osz opos' oc oc';
          (* the exact call from the configuration of a new context *)
          stream_exact st st' r osz opos opos' oc' ibs isz ipos ipos')
    RETURN (Vlong (Int64.repr r))
    SEP (pws_pred W; mem_mgr gv; zstd_globals gv; (DC gv d st' && valid_pointer d);
         dict_res gv Ews (dc_dict st); set_res gv Ews (dc_set st) (dc_dict st);
         data_at sho t_outBuffer (ob, (Vlong (Int64.repr osz), Vlong (Int64.repr opos'))) outp;
         data_at shi t_inBuffer (ib, (Vlong (Int64.repr isz), Vlong (Int64.repr ipos'))) inp;
         mbuf shob osz oc' ob;
         mbuf shb isz (zbytes ibs) ib).

(* what a buffered stream's error means on a series the model decodes (stream_claims_m's error clause with stall_ok):
   with fewer than ZSTD_NO_FORWARD_PROGRESS_MAX - 1 calls without progress before, only memory *)
Lemma stream_error_memory : forall st st' r ob osz opos opos' oc oc' ibs isz ipos ipos' s,
  stream_post st st' r ob osz opos opos' oc oc' ibs isz ipos ipos' ->
  dc_stable st = false -> ss_stall (dc_ss st) + 1 < ZSTD_NO_FORWARD_PROGRESS_MAX ->
  bytes_ok s -> is_prefix (ss_in (dc_ss st') ++ sublist (ipos' + ss_ahead (dc_ss st')) isz ibs) s ->
  snd (series_frames_m (dmode_w (dmode_of (dc_par st))) (fst (st_sel st)) (snd (st_sel st)) (dp_wmax (dc_par st)) s)
    = TEnd ->
  is_error_code r = true -> r = 2 ^ 64 - ZSTD_error_memory_allocation.
Proof.
  intros st st' r ob osz opos opos' oc oc' ibs isz ipos ipos' s Hp Hstab Hst Hb Hpre Ht Herr.
  destruct Hp as (dl & stall' & a' & Hp). cbv zeta in Hp.
  destruct Hp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hst' & _ & _ & _ & Hstall & Hcl & _).
  rewrite Hst' in Hpre. cbn [set_last set_ss dc_ss ss_in ss_ahead] in Hpre.
  assert (Hpl: forall p q (x: list Z), is_prefix (p ++ q) x -> is_prefix p x).
  { unfold is_prefix. intros p q x H.
    replace (firstn (length p) x) with (firstn (length p) (firstn (length (p ++ q)) x))
      by (rewrite firstn_firstn, length_app, Nat.min_l by lia; reflexivity).
    rewrite H, firstn_app, Nat.sub_diag, firstn_O, app_nil_r, firstn_all. reflexivity. }
  destruct (Hcl s Hb (Hpl _ _ _ Hpre)) as (_ & _ & _ & He). cbv zeta in He.
  destruct (He Hpre Ht Herr (2 ^ 64 - r) ltac:(lia)) as [E|[E|[E|(o & Eo & _)]]].
  - lia.
  - exfalso. assert (Er: r = 2 ^ 64 - ZSTD_error_noForwardProgress_destFull) by lia.
    destruct (Hstall (or_introl Er)) as (H1 & _). lia.
  - exfalso. assert (Er: r = 2 ^ 64 - ZSTD_error_noForwardProgress_inputEmpty) by lia.
    destruct (Hstall (or_intror Er)) as (H1 & _). lia.
  - rewrite Hstab in Eo. discriminate.
Qed.

(* ---------- frame inspection (no context): exact on any bytes ---------- *)

Definition src_spec_pre (sh: share) (s: list Z) : Prop := readable_share sh /\ Zlength s <= 2 ^ 63 - 1 /\ bytes_ok s.

Definition ZSTD_findFrameCompressedSize_spec : ident * funspec :=
  DECLARE _ZSTD_findFrameCompressedSize
  WITH gv: globals, sh: share, src: val, s: list Z
  PRE [ tptr tvoid, tulong ]
    PROP (src_spec_pre sh s) PARAMS (src; Vlong (Int64.repr (Zlength s))) GLOBALS (gv)
    SEP (zstd_globals gv; data_at sh (tarray tuchar (Zlength s)) (zbytes s) src)
  POST [ tulong ]
    EX r: Z,
    PROP (0 <= r <= Int64.max_unsigned;
          match frame_compressed_size s with Some k => r = k | None => is_error_code r = true end)
    RETURN (Vlong (Int64.repr r))
    SEP (zstd_globals gv; data_at sh (tarray tuchar (Zlength s)) (zbytes s) src).

Definition ZSTD_getFrameContentSize_spec : ident * funspec :=
  DECLARE _ZSTD_getFrameContentSize
  WITH gv: globals, sh: share, src: val, s: list Z
  PRE [ tptr tvoid, tulong ]
    PROP (src_spec_pre sh s) PARAMS (src; Vlong (Int64.repr (Zlength s))) GLOBALS (gv)
    SEP (zstd_globals gv; data_at sh (tarray tuchar (Zlength s)) (zbytes s) src)
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr (frame_content_size s)))
    SEP (zstd_globals gv; data_at sh (tarray tuchar (Zlength s)) (zbytes s) src).

Definition ZSTD_findDecompressedSize_spec : ident * funspec :=
  DECLARE _ZSTD_findDecompressedSize
  WITH gv: globals, sh: share, src: val, s: list Z
  PRE [ tptr tvoid, tulong ]
    PROP (src_spec_pre sh s) PARAMS (src; Vlong (Int64.repr (Zlength s))) GLOBALS (gv)
    SEP (zstd_globals gv; data_at sh (tarray tuchar (Zlength s)) (zbytes s) src)
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr (find_decompressed_size s)))
    SEP (zstd_globals gv; data_at sh (tarray tuchar (Zlength s)) (zbytes s) src).

Definition ZSTD_decompressBound_spec : ident * funspec :=
  DECLARE _ZSTD_decompressBound
  WITH gv: globals, sh: share, src: val, s: list Z
  PRE [ tptr tvoid, tulong ]
    PROP (src_spec_pre sh s) PARAMS (src; Vlong (Int64.repr (Zlength s))) GLOBALS (gv)
    SEP (zstd_globals gv; data_at sh (tarray tuchar (Zlength s)) (zbytes s) src)
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr (decompress_bound s)))
    SEP (zstd_globals gv; data_at sh (tarray tuchar (Zlength s)) (zbytes s) src).

Definition ZSTD_frameHeaderSize_spec : ident * funspec :=
  DECLARE _ZSTD_frameHeaderSize
  WITH gv: globals, sh: share, src: val, s: list Z
  PRE [ tptr tvoid, tulong ]
    PROP (src_spec_pre sh s) PARAMS (src; Vlong (Int64.repr (Zlength s))) GLOBALS (gv)
    SEP (zstd_globals gv; data_at sh (tarray tuchar (Zlength s)) (zbytes s) src)
  POST [ tulong ]
    EX r: Z,
    PROP (0 <= r <= Int64.max_unsigned;
          match frame_header_size s with Some k => r = k | None => is_error_code r = true end)
    RETURN (Vlong (Int64.repr r))
    SEP (zstd_globals gv; data_at sh (tarray tuchar (Zlength s)) (zbytes s) src).

Definition ZSTD_getDictID_fromFrame_spec : ident * funspec :=
  DECLARE _ZSTD_getDictID_fromFrame
  WITH gv: globals, sh: share, src: val, s: list Z
  PRE [ tptr tvoid, tulong ]
    PROP (src_spec_pre sh s) PARAMS (src; Vlong (Int64.repr (Zlength s))) GLOBALS (gv)
    SEP (zstd_globals gv; data_at sh (tarray tuchar (Zlength s)) (zbytes s) src)
  POST [ tuint ]
    PROP () RETURN (Vint (Int.repr (dict_id_from_frame s)))
    SEP (zstd_globals gv; data_at sh (tarray tuchar (Zlength s)) (zbytes s) src).

Definition ZSTD_isFrame_spec : ident * funspec :=
  DECLARE _ZSTD_isFrame
  WITH sh: share, src: val, s: list Z
  PRE [ tptr tvoid, tulong ]
    PROP (src_spec_pre sh s) PARAMS (src; Vlong (Int64.repr (Zlength s)))
    SEP (data_at sh (tarray tuchar (Zlength s)) (zbytes s) src)
  POST [ tuint ]
    PROP () RETURN (Vint (Int.repr (is_frame s)))
    SEP (data_at sh (tarray tuchar (Zlength s)) (zbytes s) src).

Definition ZSTD_isSkippableFrame_spec : ident * funspec :=
  DECLARE _ZSTD_isSkippableFrame
  WITH sh: share, src: val, s: list Z
  PRE [ tptr tvoid, tulong ]
    PROP (src_spec_pre sh s) PARAMS (src; Vlong (Int64.repr (Zlength s)))
    SEP (data_at sh (tarray tuchar (Zlength s)) (zbytes s) src)
  POST [ tuint ]
    PROP () RETURN (Vint (Int.repr (is_skippable_frame s)))
    SEP (data_at sh (tarray tuchar (Zlength s)) (zbytes s) src).

(* the ZSTD_FrameHeader struct of a parsed header (reserved fields 0: zstd clears the struct) *)
Definition fh_val (h: frame_header) : reptype t_fh :=
  (Vlong (Int64.repr (fh_contentSize h)),
   (Vlong (Int64.repr (fh_windowSize h)),
    (Vint (Int.repr (fh_blockSizeMax h)),
     (Vint (Int.repr (fh_frameType h)),
      (Vint (Int.repr (fh_headerSize h)),
       (Vint (Int.repr (fh_dictID h)),
        (Vint (Int.repr (fh_checksumFlag h)),
         (Vint (Int.repr 0), Vint (Int.repr 0))))))))).

(* the dictID field of a ZSTD_FrameHeader struct (v3.4: after a header error zstd leaves the struct untouched
   (a prefix error, before clearing it) or cleared: its dictID is the caller's or 0) *)
Definition fp_dictID (f: reptype t_fh) : val := fst (snd (snd (snd (snd (snd f))))).

(* the all-zero header (zstd clears the struct once it has 5 bytes, before asking for more) *)
Definition fh_zero : frame_header :=
  {| fh_contentSize := 0; fh_windowSize := 0; fh_blockSizeMax := 0; fh_frameType := 0; fh_headerSize := 0;
     fh_dictID := 0; fh_checksumFlag := 0 |}.

(* v0: the struct before the call (untouched when fewer than 5 bytes are given) *)
Definition fh_post (s: list Z) (r: Z) (v0 v: reptype t_fh) : Prop :=
  match get_frame_header s with
  | FH_ok h => r = 0 /\ v = fh_val h
  | FH_more k => r = k /\ v = (if Zlength s <? 5 then v0 else fh_val fh_zero)
  | FH_err => dec_err r /\ r = fh_err_code_m false s /\ (v = v0 \/ fp_dictID v = Vint (Int.repr 0))
  end.

Definition ZSTD_getFrameHeader_spec : ident * funspec :=
  DECLARE _ZSTD_getFrameHeader
  WITH gv: globals, shz: share, pz: val, v0: reptype t_fh, sh: share, src: val, s: list Z
  PRE [ tptr t_fh, tptr tvoid, tulong ]
    PROP (writable_share shz; src_spec_pre sh s)
    PARAMS (pz; src; Vlong (Int64.repr (Zlength s))) GLOBALS (gv)
    SEP (zstd_globals gv; data_at shz t_fh v0 pz; data_at sh (tarray tuchar (Zlength s)) (zbytes s) src)
  POST [ tulong ]
    EX r: Z, EX v: reptype t_fh,
    PROP (0 <= r <= Int64.max_unsigned; fh_post s r v0 v)
    RETURN (Vlong (Int64.repr r))
    SEP (zstd_globals gv; data_at shz t_fh v pz; data_at sh (tarray tuchar (Zlength s)) (zbytes s) src).

Definition ZSTD_readSkippableFrame_spec : ident * funspec :=
  DECLARE _ZSTD_readSkippableFrame
  WITH shd: share, dst: val, cap: Z, shv: share, pv: val, sh: share, src: val, s: list Z
  PRE [ tptr tvoid, tulong, tptr tuint, tptr tvoid, tulong ]
    PROP (writable_share shd; writable_share shv; 0 <= cap <= 2 ^ 30; src_spec_pre sh s)
    PARAMS (dst; Vlong (Int64.repr cap); pv; src; Vlong (Int64.repr (Zlength s)))
    SEP (data_at_ shd (tarray tuchar cap) dst; data_at_ shv tuint pv;
         data_at sh (tarray tuchar (Zlength s)) (zbytes s) src)
  POST [ tulong ]
    EX r: Z, EX out: list val, EX vv: val,
    PROP (0 <= r <= Int64.max_unsigned; Zlength out = cap;
          match read_skippable s cap with
          | Some (u, var) => r = Zlength u /\ sublist 0 r out = zbytes u /\ vv = Vint (Int.repr var)
          | None => is_error_code r = true
          end)
    RETURN (Vlong (Int64.repr r))
    SEP (data_at shd (tarray tuchar cap) out dst; data_at shv tuint vv pv;
         data_at sh (tarray tuchar (Zlength s)) (zbytes s) src).

(* ZSTD_getDecompressedSize: ZSTD_getFrameContentSize with "unknown" and "error" blended to 0 *)
Definition ZSTD_getDecompressedSize_aspec : ident * funspec :=
  DECLARE _ZSTD_getDecompressedSize
  WITH gv: globals, sh: share, src: val, s: list Z
  PRE [ tptr tvoid, tulong ]
    PROP (src_spec_pre sh s) PARAMS (src; Vlong (Int64.repr (Zlength s))) GLOBALS (gv)
    SEP (zstd_globals gv; data_at sh (tarray tuchar (Zlength s)) (zbytes s) src)
  POST [ tulong ]
    PROP ()
    RETURN (Vlong (Int64.repr (if frame_content_size s >=? ZSTD_CONTENTSIZE_ERROR then 0 else frame_content_size s)))
    SEP (zstd_globals gv; data_at sh (tarray tuchar (Zlength s)) (zbytes s) src).

(* ZSTD_getFrameHeader_advanced(zfh, src, n, format), format 0 (zstd1) or 1 (magicless): fh_post with the
   magicless reading of model/Params.v (the struct untouched below ZSTD_startingInputLength bytes) *)
Definition fh_post_m (mg: bool) (s: list Z) (r: Z) (v0 v: reptype t_fh) : Prop :=
  match get_frame_header_m mg s with
  | FH_ok h => r = 0 /\ v = fh_val h
  | FH_more k => r = k /\ v = (if Zlength s <? starting_len mg then v0 else fh_val fh_zero)
  | FH_err => dec_err r /\ r = fh_err_code_m mg s /\ (v = v0 \/ fp_dictID v = Vint (Int.repr 0))
  end.

Definition ZSTD_getFrameHeader_advanced_aspec : ident * funspec :=
  DECLARE _ZSTD_getFrameHeader_advanced
  WITH gv: globals, shz: share, pz: val, v0: reptype t_fh, sh: share, src: val, s: list Z, fmt: Z
  PRE [ tptr t_fh, tptr tvoid, tulong, tint ]
    PROP (writable_share shz; src_spec_pre sh s; fmt = 0 \/ fmt = 1)
    PARAMS (pz; src; Vlong (Int64.repr (Zlength s)); Vint (Int.repr fmt)) GLOBALS (gv)
    SEP (zstd_globals gv; data_at shz t_fh v0 pz; data_at sh (tarray tuchar (Zlength s)) (zbytes s) src)
  POST [ tulong ]
    EX r: Z, EX v: reptype t_fh,
    PROP (0 <= r <= Int64.max_unsigned; fh_post_m (fmt =? 1) s r v0 v)
    RETURN (Vlong (Int64.repr r))
    SEP (zstd_globals gv; data_at shz t_fh v pz; data_at sh (tarray tuchar (Zlength s)) (zbytes s) src).

(* ---------- the buffer-less API (v3) ---------- *)

(* the frame state after ZSTD_decompressBegin* with the dictionary od *)
Definition bl_begin (st: dctx_st) (od: option dictref) : blabs :=
  let md := dmode_of (dc_par st) in
  {| ba_dict := od;
     ba_st := match dictref_model od with Some dm => Some (bl_init md dm) | None => None end;
     ba_expect := starting_len (md_magicless md); ba_out := None |}.

Definition ZSTD_decompressBegin_aspec : ident * funspec :=
  DECLARE _ZSTD_decompressBegin
  WITH gv: globals, d: val, st: dctx_st
  PRE [ tptr t_dctx ]
    PROP (dc_set st = nil; dc_ss st = ss_init) PARAMS (d) GLOBALS (gv)
    SEP (zstd_globals gv; DC gv d st)
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr 0))
    SEP (zstd_globals gv; DC gv d (set_ex (set_bl st (Some (bl_begin st None))) false)).

(* with the caller's dictionary b at p, by reference (ZSTD_dct_auto); none when b is empty; an error only when
   zstd cannot load b's entropy tables (dictionary_corrupted), and then no frame is begun *)
Definition ZSTD_decompressBegin_usingDict_aspec : ident * funspec :=
  DECLARE _ZSTD_decompressBegin_usingDict
  WITH W: list ptr_witness, gv: globals, d: val, st: dctx_st, sh: share, p: val, b: list Z
  PRE [ tptr t_dctx, tptr tvoid, tulong ]
    PROP (dc_set st = nil; dc_ss st = ss_init; buf_ok W sh (Zlength b) p; readable_share sh;
          Zlength b <= 2 ^ 63 - 1; bytes_ok b)
    PARAMS (d; p; Vlong (Int64.repr (Zlength b))) GLOBALS (gv)
    SEP (pws_pred W; zstd_globals gv; DC gv d st; data_at sh (tarray tuchar (Zlength b)) (zbytes b) p)
  POST [ tulong ]
    EX r: Z, EX st': dctx_st,
    PROP (0 <= r <= Int64.max_unsigned;
          (r = 0 /\ st' = set_ex (set_bl st (Some (bl_begin st
             (if Zlength b =? 0 then None
              else Some {| dr_src := DSRef p; dr_raw := false; dr_once := false; dr_bytes := b |})))) false) \/
          (is_error_code r = true /\ dict_auto b = None /\ st' = set_ex (set_bl st None) false))
    RETURN (Vlong (Int64.repr r))
    SEP (pws_pred W; zstd_globals gv; DC gv d st'; data_at sh (tarray tuchar (Zlength b)) (zbytes b) p).

(* with the DDict q (NULL: none) *)
Definition ZSTD_decompressBegin_usingDDict_aspec : ident * funspec :=
  DECLARE _ZSTD_decompressBegin_usingDDict
  WITH gv: globals, d: val, st: dctx_st, q: val, odd: option ddict_st
  PRE [ tptr t_dctx, tptr t_ddict ]
    PROP (dc_set st = nil; dc_ss st = ss_init; match odd with None => q = nullval | Some _ => isptr q end)
    PARAMS (d; q) GLOBALS (gv)
    SEP (zstd_globals gv; DC gv d st; match odd with None => emp | Some dd => DD gv q dd end)
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr 0))
    SEP (zstd_globals gv;
         DC gv d (set_ex (set_bl st (Some (bl_begin st (match odd with Some dd => Some (ddict_ref q dd) | None => None end)))) false);
         match odd with None => emp | Some dd => (DD gv q dd && valid_pointer q) end).

Definition ZSTD_nextSrcSizeToDecompress_aspec : ident * funspec :=
  DECLARE _ZSTD_nextSrcSizeToDecompress
  WITH gv: globals, d: val, st: dctx_st, ba: blabs
  PRE [ tptr t_dctx ]
    PROP (dc_bl st = Some ba) PARAMS (d) GLOBALS (gv)
    SEP (DC gv d st)
  POST [ tulong ]
    PROP (0 <= ba_expect ba <= Int64.max_unsigned) RETURN (Vlong (Int64.repr (ba_expect ba)))
    SEP (DC gv d st).

(* ZSTD_nextInputType: one of the 6 ZSTD_nextInputType_e values, the model's in a described stage *)
Definition ZSTD_nextInputType_aspec : ident * funspec :=
  DECLARE _ZSTD_nextInputType
  WITH gv: globals, d: val, st: dctx_st, ba: blabs
  PRE [ tptr t_dctx ]
    PROP (dc_bl st = Some ba) PARAMS (d) GLOBALS (gv)
    SEP (DC gv d st)
  POST [ tint ]
    EX r: Z,
    PROP (0 <= r <= 5; forall b, ba_st ba = Some b -> r = bl_input_type b) RETURN (Vint (Int.repr r))
    SEP (DC gv d st).

(* the history a call needs: the frame's output so far right before dst (the call continues it, in the same
   buffer of the same size osz: v3.1), as the model says in a described stage, else bytes *)
Definition bl_hist_ok (ba: blabs) (ob: val) (osz opos: Z) (oc: list val) : Prop :=
  match ba_out ba with
  | Some (ob', osz', fs, pe) =>
      ob' = ob /\ osz' = osz /\ pe = opos /\ 0 <= fs <= opos /\
      match ba_st ba with
      | Some b => sublist fs opos oc = zbytes (bs_out b)
      | None => cells_bytes (sublist fs opos oc)
      end
  | None => match ba_st ba with Some b => bs_out b = nil | None => True end
  end.

Definition bl_start (ba: blabs) (opos: Z) : Z :=
  match ba_out ba with Some (_, _, fs, _) => fs | None => opos end.

(* in a described stage with the size zstd asks for: the model's step (model/Params.v bl_step) *)
Definition bl_claim (md: dmode) (ba ba': blabs) (c: list Z) (r opos osz: Z) (oc': list val) : Prop :=
  match ba_st ba, dictref_model (ba_dict ba) with
  | Some b, Some dm =>
      Zlength c = bs_expect b ->
      match bl_step md dm b c with
      | BLOk b' out =>
          (is_error_code r = false ->
             r = Zlength out /\ sublist opos (opos + r) oc' = zbytes out /\ ba_st ba' = Some b') /\
          (is_error_code r = true -> osz - opos < Zlength out)
      | BLErr => is_error_code r = true
      | BLUnk => True
      end
  | _, _ => True
  end.

(* ZSTD_decompressContinue(d, ob + opos, osz - opos, src, n): the output buffer ob of osz cells, the call
   writing at opos; after an error no frame is begun (the caller begins a new one) *)
Definition ZSTD_decompressContinue_aspec : ident * funspec :=
  DECLARE _ZSTD_decompressContinue
  WITH W: list ptr_witness, gv: globals, d: val, st: dctx_st, ba: blabs, shk: share,
       shd: share, ob: val, osz: Z, opos: Z, oc: list val, shs: share, src: val, c: list Z
  PRE [ tptr t_dctx, tptr tvoid, tulong, tptr tvoid, tulong ]
    PROP (dc_bl st = Some ba; ba_expect ba <> 0; bl_hist_ok ba ob osz opos oc; dc_set st = nil;
          buf_ok W shd osz ob; buf_ok W shs (Zlength c) src;
          dict_buf_ok W shk (ba_dict ba) shd (osz - opos) (offset_val opos ob);
          writable_share shd; readable_share shs; readable_share shk;
          0 <= opos <= osz; osz <= 2 ^ 30; Zlength oc = osz; Zlength c <= 2 ^ 30; bytes_ok c)
    PARAMS (d; offset_val opos ob; Vlong (Int64.repr (osz - opos)); src; Vlong (Int64.repr (Zlength c)))
    GLOBALS (gv)
    SEP (pws_pred W; zstd_globals gv; DC gv d st; dict_res gv shk (ba_dict ba);
         data_at shd (tarray tuchar osz) oc ob; data_at shs (tarray tuchar (Zlength c)) (zbytes c) src)
  POST [ tulong ]
    EX r: Z, EX oc': list val, EX ba': blabs,
    PROP (0 <= r <= Int64.max_unsigned; Zlength oc' = osz; sublist 0 opos oc' = sublist 0 opos oc;
          (is_error_code r = false ->
             r <= osz - opos /\ cells_bytes (sublist opos (opos + r) oc') /\ ba_dict ba' = ba_dict ba /\
             ba_out ba' = Some (pair (pair (pair ob osz) (bl_start ba opos)) (opos + r)%Z) /\
             bl_hist_ok ba' ob osz (opos + r) oc' /\
             (forall b', ba_st ba' = Some b' -> ba_expect ba' = bs_expect b'));
          bl_claim (dmode_of (dc_par st)) ba ba' c r opos osz oc')
    RETURN (Vlong (Int64.repr r))
    SEP (pws_pred W; zstd_globals gv; DC gv d (set_ex (set_bl st (if is_error_code r then None else Some ba')) false);
         dict_res gv shk (ba_dict ba);
         data_at shd (tarray tuchar osz) oc' ob; data_at shs (tarray tuchar (Zlength c)) (zbytes c) src).

(* ---------- the API ---------- *)

(* a law reads its allocator's state between two calls on a context with its own allocator: the context's
   predicate holds the state (some h bytes given out) and takes it back *)
Definition dc_cm_ok : Prop :=
  forall gv p st m, dc_mem st = Some m ->
    DC gv p st |-- EX h: Z, CM (cm_opaque m) (cm_bound m) h * (CM (cm_opaque m) (cm_bound m) h -* DC gv p st).

Definition Specs_api : funspecs :=
  [ ZSTD_isError_spec; ZSTD_getErrorCode_spec;
    ZSTD_decompress_spec; ZSTD_decompressDCtx_spec; ZSTD_decompress_usingDict_spec;
    ZSTD_decompress_usingDDict_spec;
    ZSTD_createDCtx_spec; ZSTD_createDStream_spec; ZSTD_freeDCtx_spec; ZSTD_freeDStream_spec;
    ZSTD_DCtx_reset_spec; ZSTD_initDStream_spec; ZSTD_DCtx_setParameter_spec; ZSTD_DStreamOutSize_spec;
    ZSTD_createDDict_spec; ZSTD_createDDict_byReference_spec; ZSTD_freeDDict_spec;
    ZSTD_getDictID_fromDDict_spec; ZSTD_getDictID_fromDict_spec;
    ZSTD_DCtx_loadDictionary_byReference_spec; ZSTD_DCtx_loadDictionary_spec;
    ZSTD_DCtx_refPrefix_spec; ZSTD_DCtx_refDDict_spec;
    ZSTD_decompressStream_spec;
    ZSTD_findFrameCompressedSize_spec; ZSTD_getFrameContentSize_spec; ZSTD_findDecompressedSize_spec;
    ZSTD_decompressBound_spec; ZSTD_frameHeaderSize_spec; ZSTD_getDictID_fromFrame_spec;
    ZSTD_isFrame_spec; ZSTD_isSkippableFrame_spec; ZSTD_getFrameHeader_spec; ZSTD_readSkippableFrame_spec;
    (* v3 *)
    ZSTD_DCtx_setFormat_aspec; ZSTD_DCtx_setMaxWindowSize_aspec; ZSTD_resetDStream_aspec;
    ZSTD_DCtx_loadDictionary_advanced_aspec; ZSTD_DCtx_refPrefix_advanced_aspec;
    ZSTD_initDStream_usingDict_aspec; ZSTD_initDStream_usingDDict_aspec;
    ZSTD_getDecompressedSize_aspec; ZSTD_getFrameHeader_advanced_aspec;
    ZSTD_decompressBegin_aspec; ZSTD_decompressBegin_usingDict_aspec; ZSTD_decompressBegin_usingDDict_aspec;
    ZSTD_nextSrcSizeToDecompress_aspec; ZSTD_nextInputType_aspec; ZSTD_decompressContinue_aspec;
    (* contexts with their own allocator (the res_ laws) *)
    ZSTD_createDCtx_advancedP_spec; ZSTD_estimateDCtxSize_spec; ZSTD_estimateDStreamSize_spec ].

End Api.
