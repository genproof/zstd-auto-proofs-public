(* The decoder's shared representations, fixed for the whole decoder: the subtrees H (headers), B (blocks,
   entropy tables, dictionary entropy) and FS (frames, streaming, contexts, dictionary API) all use these.

   - the frame fields of a ZSTD_DCtx (record fstate, frame_fields): concrete;
   - the "tables" fields of a ZSTD_DCtx (entropy tables, table pointers, literal buffers, workspace):
     owned by B through an abstract predicate TABS (tabs_pred), uninitialised = tables_uninit;
   - a ZSTD_DDict (ddict_rep): its struct fields are concrete, its `entropy` field is owned by B through
     an abstract predicate DENT (dent_pred);
   - the two configuration fields B reads (format, disableHufAsm): cfg_b.
   Every field of struct ZSTD_DCtx_s other than these groups is FS's business. *)
Require Export Zstd.proof.zstd.Spec_api6.
Require Import Zstd.proof.model.ExHuf Zstd.proof.model.ExBlock.
Local Open Scope logic.

Definition t_seqSymbol : type := Tstruct ___gp_ZSTD_seqSymbol noattr.
Definition t_entropy : type := Tstruct ___gp_ZSTD_entropyDTables_t noattr.
Definition t_cmem : type := Tstruct ___gp_ZSTD_customMem noattr.
Definition t_bp : type := Tstruct ___gp_blockProperties_t noattr.

(* the allocator { NULL, NULL, NULL } (the only one the API uses) *)
Definition cmem_null : reptype t_cmem := (nullval, (nullval, nullval)).

Definition WILDCOPY_OVERLENGTH : Z := 32.
Definition ZSTD_HUFFDTABLE_CAPACITY_LOG : Z := 12.

(* ZSTD_dictUses_e *)
Definition ZSTD_use_indefinitely : Z := -1.
Definition ZSTD_dont_use : Z := 0.
Definition ZSTD_use_once : Z := 1.

(* ---------- frame fields ---------- *)

Record fstate := {
  fs_previousDstEnd : val;
  fs_gpDictCopy : val;
  fs_prefixStart : val;
  fs_virtualStart : val;
  fs_dictEnd : val;
  fs_expected : val;
  fs_fParams : reptype t_fh;
  fs_processedCSize : val;
  fs_decodedSize : val;
  fs_bType : val;
  fs_stage : val;
  fs_xxh : option (list Z);      (* None: any contents; Some l: xxh64_state Ews 0 l *)
  fs_headerSize : val;
  fs_validateChecksum : val;
  fs_rleSize : val;
  fs_isFrameDecompression : val;
  fs_dictID : val;
  fs_ddictIsCold : val
}.

Definition xxh_field (p: val) (x: option (list Z)) : mpred :=
  match x with
  | None => field_at_ Ews t_dctx (DOT _xxhState) p
  | Some l => xxh64_state Ews 0 l (field_address t_dctx (DOT _xxhState) p)
  end.

Definition frame_fields (p: val) (fs: fstate) : mpred :=
  field_at Ews t_dctx (DOT _previousDstEnd) (fs_previousDstEnd fs) p *
  field_at Ews t_dctx (DOT _gpDictCopy) (fs_gpDictCopy fs) p *
  field_at Ews t_dctx (DOT _prefixStart) (fs_prefixStart fs) p *
  field_at Ews t_dctx (DOT _virtualStart) (fs_virtualStart fs) p *
  field_at Ews t_dctx (DOT _dictEnd) (fs_dictEnd fs) p *
  field_at Ews t_dctx (DOT _expected) (fs_expected fs) p *
  field_at Ews t_dctx (DOT _fParams) (fs_fParams fs) p *
  field_at Ews t_dctx (DOT _processedCSize) (fs_processedCSize fs) p *
  field_at Ews t_dctx (DOT _decodedSize) (fs_decodedSize fs) p *
  field_at Ews t_dctx (DOT _bType) (fs_bType fs) p *
  field_at Ews t_dctx (DOT _stage) (fs_stage fs) p *
  xxh_field p (fs_xxh fs) *
  field_at Ews t_dctx (DOT _headerSize) (fs_headerSize fs) p *
  field_at Ews t_dctx (DOT _validateChecksum) (fs_validateChecksum fs) p *
  field_at Ews t_dctx (DOT _rleSize) (fs_rleSize fs) p *
  field_at Ews t_dctx (DOT _isFrameDecompression) (fs_isFrameDecompression fs) p *
  field_at Ews t_dctx (DOT _dictID) (fs_dictID fs) p *
  field_at Ews t_dctx (DOT _ddictIsCold) (fs_ddictIsCold fs) p.

(* the fields of fParams (ZSTD_FrameHeader): frameContentSize, windowSize, blockSizeMax, frameType,
   headerSize, dictID, checksumFlag, _reserved1, _reserved2 *)
Definition fp_blockSizeMax (f: reptype t_fh) : val := fst (snd (snd f)).
Definition fp_windowSize (f: reptype t_fh) : val := fst (snd f).

(* ---------- the two configuration fields B reads ---------- *)

Definition cfg_b (p: val) : mpred :=
  field_at Ews t_dctx (DOT _format) (Vint (Int.repr 0)) p *
  field_at Ews t_dctx (DOT _disableHufAsm) (Vint (Int.repr 0)) p.

(* ---------- the tables group (owned by B) ---------- *)

(* every cell is a defined byte (contract patch item 17: the context and the stream buffers are calloc'd,
   and zstd only ever writes bytes into them; zstd's literal copies over-read up to 32 cells past the
   literals) *)
Definition byte_cells (l: list val) : Prop :=
  Forall (fun v => exists z, 0 <= z < 256 /\ v = Vint (Int.repr z)) l.

(* litExtraBuffer always holds bytes (zeroed at creation) *)
Definition lit_extra_bytes (p: val) : mpred :=
  EX l: list val, !! byte_cells l && field_at Ews t_dctx (DOT _litExtraBuffer) l p.

(* the cells of litExtraBuffer: ZSTD_LITBUFFEREXTRASIZE (65536) + WILDCOPY_OVERLENGTH *)
Definition LITEXTRA_N : Z := 65536 + WILDCOPY_OVERLENGTH.

(* litExtraBuffer holding the bytes lxb (all its LITEXTRA_N cells; model/ExBlock.v's x_lxb) *)
Definition lit_extra_at (p: val) (lxb: list Z) : mpred :=
  !! (Zlength lxb = LITEXTRA_N /\ bytes_ok lxb) && field_at Ews t_dctx (DOT _litExtraBuffer) (zbytes lxb) p.

Lemma lit_extra_at_bytes (p: val) (lxb: list Z) : lit_extra_at p lxb |-- lit_extra_bytes p.
Proof.
  unfold lit_extra_at, lit_extra_bytes. Intros. Exists (zbytes lxb). entailer!.
  unfold byte_cells. rewrite Forall_map. eapply Forall_impl; [|eassumption].
  intros z Hz. exists z. split; [exact Hz | reflexivity].
Qed.

Lemma lit_extra_bytes_at (p: val) : lit_extra_bytes p |-- EX lxb: list Z, lit_extra_at p lxb.
Proof.
  unfold lit_extra_bytes, lit_extra_at. Intros l.
  assert (Hl: exists lxb, l = zbytes lxb /\ bytes_ok lxb).
  { clear -H. induction H as [|v l [z [Hz ->]] _ [lxb [-> Hb]]].
    - exists nil. split; [reflexivity | constructor].
    - exists (z :: lxb). split; [reflexivity | constructor; [exact Hz | exact Hb]]. }
  destruct Hl as [lxb [-> Hb]]. Exists lxb.
  sep_apply (field_at_local_facts Ews t_dctx (DOT _litExtraBuffer) (zbytes lxb) p). Intros.
  entailer!. clear - H2. destruct H2 as [H2 _]. unfold LITEXTRA_N, WILDCOPY_OVERLENGTH.
  change (Zlength (zbytes lxb) = 65568) in H2. rewrite Zlength_map in H2. lia.
Qed.

(* the tables group before ZSTD_decompressBegin: every field anything, except litExtraBuffer, which holds the
   bytes lxb (zstd's literal copies can carry its stale cells into the output: model/ExBlock.v's x_lxb) *)
Definition tables_uninit (p: val) (lxb: list Z) : mpred :=
  field_at_ Ews t_dctx (DOT _LLTptr) p *
  field_at_ Ews t_dctx (DOT _MLTptr) p *
  field_at_ Ews t_dctx (DOT _OFTptr) p *
  field_at_ Ews t_dctx (DOT _HUFptr) p *
  field_at_ Ews t_dctx (DOT _entropy) p *
  field_at_ Ews t_dctx (DOT _workspace) p *
  field_at_ Ews t_dctx (DOT _litEntropy) p *
  field_at_ Ews t_dctx (DOT _fseEntropy) p *
  field_at_ Ews t_dctx (DOT _litPtr) p *
  field_at_ Ews t_dctx (DOT _litSize) p *
  field_at_ Ews t_dctx (DOT _litBuffer) p *
  field_at_ Ews t_dctx (DOT _litBufferEnd) p *
  field_at_ Ews t_dctx (DOT _litBufferLocation) p *
  lit_extra_at p lxb.

(* ---------- digested dictionaries ---------- *)

Definition is_formatted (b: list Z) : bool :=
  (8 <=? Zlength b) && (le_field b 0 4 =? ZSTD_MAGIC_DICTIONARY).

(* ---------- zstd's dictionary loading vs the model (C-result form) ----------
   zstd may accept entropy descriptions the model rejects, so ZSTD_loadDEntropy's
   result ores is related to Series.load_dentropy by ld_rel only: equal where the model loads.  The
   dictionary as zstd loads it is dict_auto_c b ores / ddict_ent_c b raw ores; with ores = load_dentropy b
   these are dict_auto / ddict_ent, and ld_rel gives the same on every dictionary the model accepts
   (ld_rel_auto_some / ld_rel_auto_none). *)
Definition ld_rel (b: list Z) (ores: option (dstate * Z)) : Prop :=
  forall x, load_dentropy b = Some x -> ores = Some x.

Definition dict_auto_c (b: list Z) (ores: option (dstate * Z)) : option dict_model :=
  if Zlength b <? 8 then Some (dict_raw b) else
  if negb (le_field b 0 4 =? ZSTD_MAGIC_DICTIONARY) then Some (dict_raw b) else
  match ores with
  | None => None
  | Some (st, esize) =>
      Some {| dm_content := skipn (Z.to_nat esize) b; dm_id := le_field b 4 4; dm_state := st |}
  end.

Definition ddict_ent_c (b: list Z) (raw: bool) (ores: option (dstate * Z)) : option dstate :=
  if raw then None
  else if is_formatted b then
    match ores with Some (st, _) => Some st | None => None end
  else None.

Lemma dict_auto_c_exact (b: list Z) : dict_auto_c b (load_dentropy b) = dict_auto b.
Proof. reflexivity. Qed.

Lemma ld_rel_exact (b: list Z) : ld_rel b (load_dentropy b).
Proof. intros x H; exact H. Qed.

Lemma ld_rel_auto_some (b: list Z) (ores: option (dstate * Z)) (dm: dict_model) :
  ld_rel b ores -> dict_auto b = Some dm -> dict_auto_c b ores = Some dm.
Proof.
  intros HL HA. unfold dict_auto in HA; unfold dict_auto_c.
  destruct (Zlength b <? 8); [exact HA|].
  destruct (negb (le_field b 0 4 =? ZSTD_MAGIC_DICTIONARY)); [exact HA|].
  destruct (load_dentropy b) as [x|] eqn:E; [|discriminate].
  rewrite (HL x E). exact HA.
Qed.

Lemma ld_rel_auto_none (b: list Z) (ores: option (dstate * Z)) :
  ld_rel b ores -> dict_auto_c b ores = None -> dict_auto b = None.
Proof.
  intros HL HA. unfold dict_auto_c in HA; unfold dict_auto.
  destruct (Zlength b <? 8); [discriminate|].
  destruct (negb (le_field b 0 4 =? ZSTD_MAGIC_DICTIONARY)); [discriminate|].
  destruct (load_dentropy b) as [x|] eqn:E; [|reflexivity].
  rewrite (HL x E) in HA. destruct x; discriminate.
Qed.

(* A ZSTD_DDict at q: made from the bytes b, by reference to the caller's p (dx_ref = Some p) or by
   copy (None), as raw content (refPrefix: ZSTD_dct_rawContent) or in ZSTD_dct_auto mode; dx_ld: what
   ZSTD_loadDEntropy gives on b (ld_rel; irrelevant for raw content); dx_mem: the allocator that made it, which
   zstd keeps in the DDict's cMem and frees it through (None: the default one; a context's own allocator for the
   DDict a context makes, CMem.cmem) *)
Record ddx := { dx_q : val; dx_bytes : list Z; dx_ref : option val; dx_raw : bool;
                dx_ld : option (dstate * Z); dx_mem : option cmem }.

(* the entropy state a DDict holds (entropyPresent): the tables of a formatted dictionary *)
Definition ddict_ent (b: list Z) (raw: bool) : option dstate :=
  if raw then None
  else if is_formatted b then
    match load_dentropy b with Some (st, _) => Some st | None => None end
  else None.

(* the entropy state a DDict holds as zstd loaded it *)
Definition ddx_ent (x: ddx) : option dstate := ddict_ent_c (dx_bytes x) (dx_raw x) (dx_ld x).

Lemma ddict_ent_c_exact (b: list Z) (raw: bool) : ddict_ent_c b raw (load_dentropy b) = ddict_ent b raw.
Proof. reflexivity. Qed.

(* the dictionary model of a DDict, as zstd loaded it (= dictref_model where the model loads) *)
Definition ddx_model (x: ddx) : option dict_model :=
  if dx_raw x then Some (dict_raw (dx_bytes x)) else dict_auto_c (dx_bytes x) (dx_ld x).

Lemma ddx_model_some (x: ddx) (dm: dict_model) :
  ld_rel (dx_bytes x) (dx_ld x) ->
  (if dx_raw x then Some (dict_raw (dx_bytes x)) else dict_auto (dx_bytes x)) = Some dm ->
  ddx_model x = Some dm.
Proof.
  intros HL H. unfold ddx_model. destruct (dx_raw x); [exact H|]. exact (ld_rel_auto_some _ _ _ HL H).
Qed.

(* the bytes zstd uses as the history in front of a frame decoded with this DDict (dictContent): the
   whole dictionary (header included) *)

(* B's predicate for the `entropy` field of a DDict q: the tables of oe (None: no entropy) *)
Definition dent_pred : Type := globals -> val -> option dstate -> mpred.

Definition DENT_OK (DENT: dent_pred) : Prop :=
  forall gv q oe, DENT gv q oe |-- field_at_ Ews (Tstruct _ZSTD_DDict_s noattr) (DOT _entropy) q.

(* a DDict that owns a copy of its bytes (dictBuffer <> NULL); a "copy" of 0 bytes keeps the caller's
   pointer instead, so it is described with dx_ref = Some p, as Spec_api6 does *)
Definition ddx_copied (x: ddx) : bool :=
  match dx_ref x with Some _ => false | None => true end.

(* the struct fields of a DDict other than `entropy`; dictContent = buf: the copy, or the caller's p; cMem: its
   allocator.  buf is a pointer, except for the DDict ZSTD_createDDict(NULL, 0) makes: no content at all
   (dictBuffer = dictContent = NULL, dictSize = 0), described by dx_ref = Some nullval *)
Definition ddict_struct (x: ddx) (buf: val) : mpred :=
  let q := dx_q x in let b := dx_bytes x in
  let t := Tstruct _ZSTD_DDict_s noattr in
  !! (isptr q /\ Zlength b <= 2 ^ 63 - 1 /\ bytes_ok b /\
      ld_rel b (dx_ld x) /\ (dx_raw x = true \/ dict_auto_c b (dx_ld x) <> None) /\
      (isptr buf \/ (buf = nullval /\ dx_ref x = Some nullval /\ b = nil)) /\ (ddx_copied x = true -> 0 < Zlength b) /\
      (match dx_ref x with Some p => buf = p | None => True end) /\ cmem_ok (dx_mem x)) &&
  (field_at Ews t (DOT _dictBuffer) (if ddx_copied x then buf else nullval) q *
   field_at Ews t (DOT _dictContent) buf q *
   field_at Ews t (DOT _dictSize) (Vlong (Int64.repr (Zlength b))) q *
   field_at Ews t (DOT _dictID) (Vint (Int.repr (if dx_raw x then 0 else dict_id_of b))) q *
   field_at Ews t (DOT _entropyPresent)
     (Vint (Int.repr (match ddx_ent x with Some _ => 1 | None => 0 end))) q *
   field_at Ews t (DOT _cMem) (cmem_v (dx_mem x)) q).

(* the content pointer fact of ddict_struct, for a copy *)
Lemma ddx_buf_copied (x: ddx) (buf: val) :
  ddx_copied x = true -> (isptr buf \/ (buf = nullval /\ dx_ref x = Some nullval /\ dx_bytes x = nil)) ->
  isptr buf.
Proof. unfold ddx_copied. intros Hc [H | (_ & H & _)]; [exact H | rewrite H in Hc; discriminate]. Qed.

(* the content of a DDict is at a pointer unless it is the DDict without content *)
Lemma ddict_struct_isptr (x: ddx) (buf: val) :
  dx_ref x <> Some nullval -> ddict_struct x buf |-- !! isptr buf.
Proof.
  intros Hr. unfold ddict_struct. Intros. apply prop_right.
  match goal with H: isptr buf \/ _ |- _ => destruct H as [H | (_ & H & _)]; [exact H | contradiction] end.
Qed.

Lemma ddict_struct_copied_isptr (x: ddx) (buf: val) :
  ddx_copied x = true -> ddict_struct x buf |-- !! isptr buf.
Proof.
  intros Hc. apply ddict_struct_isptr. unfold ddx_copied in Hc. destruct (dx_ref x); [discriminate | congruence].
Qed.

Section DMem.
Context {CMI: cmem_preds}.

(* the memory a DDict owns besides its fields: the struct's allocation token, the copy (both of its allocator) *)
Definition ddict_mem (x: ddx) (buf: val) : mpred :=
  blk_tok (dx_mem x) (Tstruct _ZSTD_DDict_s noattr) (dx_q x) *
  (if ddx_copied x
   then blk_tok (dx_mem x) (tarray tuchar (Zlength (dx_bytes x))) buf *
        data_at Ews (tarray tuchar (Zlength (dx_bytes x))) (zbytes (dx_bytes x)) buf
   else emp).

Definition ddict_rep (DENT: dent_pred) (gv: globals) (x: ddx) : mpred :=
  EX buf: val,
  ddict_struct x buf * DENT gv (dx_q x) (ddx_ent x) * ddict_mem x buf.

End DMem.

(* the bytes a DDict holds from a context's own allocator (none from the default one): the struct and the copy *)
Definition ddx_held (x: ddx) : Z :=
  match dx_mem x with
  | None => 0
  | Some _ => sizeof (Tstruct _ZSTD_DDict_s noattr) + (if ddx_copied x then Zlength (dx_bytes x) else 0)
  end.

(* ---------- the tables of a context (owned by B) ---------- *)

(* The state the tables group of a context holds: the entropy state ts_d (model/Block.v: Huffman table,
   sequence tables, repeat offsets), the type of the context's own Huffman table (ts_x2: X2 cells, else X1;
   irrelevant without a table or with a DDict's) and litExtraBuffer's bytes ts_lxb.  ts_x is the same state
   as model/ExBlock.v's exact block model sees it (the Huffman table as the cells zstd built, ExHuf.xhuf_of). *)
Record tstate := mk_tstate { ts_d : dstate; ts_x2 : bool; ts_lxb : list Z }.
Coercion ts_d : tstate >-> dstate.

Definition ts_x (t: tstate) : xst xhuf :=
  {| x_huf := option_map (xhuf_of (ts_x2 t)) (st_huf t); x_seq := st_seq t; x_rep := st_rep t;
     x_lxb := ts_lxb t |}.

(* after ZSTD_decompressBegin without a dictionary, litExtraBuffer holding lxb (xst_begin) *)
Definition tstate_begin (lxb: list Z) : tstate := mk_tstate dstate_init false lxb.

(* ... on a new context, litExtraBuffer all zeros (xst_init) *)
Definition tstate_init : tstate := tstate_begin (x_lxb xhuf (xst_init xhuf)).

Lemma ts_x_begin (st: xst xhuf) : ts_x (tstate_begin (x_lxb xhuf st)) = xst_begin xhuf st.
Proof. reflexivity. Qed.

Lemma ts_x_init : ts_x tstate_init = xst_init xhuf.
Proof. reflexivity. Qed.

(* TABS gv p ox ts: the tables group of the context p holds the state ts.  Tables may live in the DDict ox
   (whose entropy, DENT gv q (ddx_ent x), the caller then holds), in the context, or (predefined) in
   zstd_globals. *)
Definition tabs_pred : Type := globals -> val -> option ddx -> tstate -> mpred.

Definition TABS_OK (TABS: tabs_pred) : Prop :=
  forall gv p ox ts, TABS gv p ox ts |-- tables_uninit p (ts_lxb ts).

(* the DDict entropy a context's tables may point to *)
Definition dent_of (DENT: dent_pred) (gv: globals) (ox: option ddx) : mpred :=
  match ox with
  | None => emp
  | Some x => DENT gv (dx_q x) (ddx_ent x)
  end.
