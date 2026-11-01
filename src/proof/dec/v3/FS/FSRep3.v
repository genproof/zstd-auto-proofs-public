(* Subtree FS of the decoder, API v3: the representation of a ZSTD_DCtx, fixed: every
   FS3 part uses these definitions.

   v2's FSRep, as FSRepC (still in force: dgroup, sgroup, ddict_rep_at, ...) fixed the parameter fields to
   zstd's defaults.  v3 keeps v2's groups and adds:
   - fgroup3: the frame group with the parameters as they are (Spec_api6.dparams: format, forceIgnoreChecksum,
     maxBlockSizeParam, refMultipleDDicts) and the DDict set pointer, and tables that may point into a DDict
     (tabs3 = TUninit lxb: uninitialised, litExtraBuffer holding the bytes lxb; TInit ox ts: B's TABS gv p ox ts);
   - cgroup3: maxWindowSize as set;
   - hset_rep am sp l hb: zstd's DDict hash set at sp (NULL: none) holding exactly the DDicts of the abstract set l,
     allocated through the context's allocator am (hb bytes of it)
     (Spec_api6.dc_set), with the linear-probing invariant hs_inv;
   - DC3_of SR BR: the abstract state related by base_rel3 (parameters, set, dictionary, which after a frame's
     selection may be any DDict of the set), SR for a running stream (chosen by the streaming part), BR for a
     buffer-less frame (chosen by the buffer-less part; it sees only the frame fields, tables and headerBuffer,
     which the other functions do not change), and SR's exact relation sr_ex for a context with dc_ex (the stream
     is the image of its calls since the reset on a clean context; it sees only the calls, the streaming fields
     without the allocator, the frame fields and the tables). *)
Require Export Zstd.proof.dec.v3.FS.FSRepC.
Require Export Zstd.proof.dec.v3.DecSubtrees3.
Local Open Scope logic.

(* ---------- parameters ---------- *)

(* the values zstd's setters can store *)
Definition par_ok (pr: dparams) : Prop :=
  (dp_fmt pr = 0 \/ dp_fmt pr = 1) /\ (dp_ignore pr = 0 \/ dp_ignore pr = 1) /\
  (dp_bmax pr = 0 \/ 1024 <= dp_bmax pr <= ZSTD_BLOCKSIZE_MAX) /\
  2 ^ 10 <= dp_wmax pr <= 2 ^ 31 /\ (dp_multi pr = 0 \/ dp_multi pr = 1).

Lemma par_ok_dflt : par_ok dparams_dflt.
Proof. unfold par_ok, dparams_dflt, dp_wmax_dflt; simpl. repeat split; try lia; auto. Qed.

(* ---------- the DDict hash set ---------- *)

Definition t_hset : type := Tstruct ___gp_ZSTD_DDictHashSet noattr.

(* ZSTD_DDictHashSet_getIndex: XXH64 of the dictID's 4 bytes (seed 0), masked by the table size n (a power of 2) *)
Definition hs_home (id n: Z) : Z := Z.land (xxh64 (le_bytes 4 id) 0) (n - 1).

(* the slot reached after t probes from h *)
Definition hs_slot (h t n: Z) : Z := (h + t) mod n.

(* the DDicts of the set sit at slots of tbl (one each), every other slot is NULL, and each DDict is reached by
   linear probing from its home slot through non-NULL slots; IDs distinct (zstd replaces a DDict of the same ID);
   the table never full; its size a power of 2 between 64 and max(64, 8 * count) *)
Definition hs_inv (l: list (val * ddict_st)) (tbl: list val) : Prop :=
  let n := Zlength tbl in
  (exists k, 6 <= k /\ n = 2 ^ k) /\ n <= Z.max 64 (8 * Zlength l) /\ Zlength l < n /\
  NoDup (map fst l) /\ ids_distinct (map (fun e => dd_id (snd e)) l) = true /\
  Forall (fun e => isptr (fst e)) l /\
  Permutation (filter (fun v => negb (veqb v nullval)) tbl) (map fst l) /\
  Forall (fun v => v = nullval \/ isptr v) tbl /\
  (forall j e, 0 <= j < n -> In e l -> Znth j tbl = fst e ->
     forall t, 0 <= t < (j - hs_home (dd_id (snd e)) n) mod n ->
       Znth (hs_slot (hs_home (dd_id (snd e)) n) t n) tbl <> nullval).

(* the bytes the set's blocks (struct, table of n pointers) hold from a context's own allocator (none from the
   default one) *)
Definition set_bytes (am: option cmem) (n: Z) : Z :=
  match am with None => 0 | Some _ => sizeof t_hset + 8 * n end.

Section HSet.
Context {CMI: cmem_preds}.

(* the table: calloc'd bytes through the context's allocator am (the allocation's token is the byte array's), used
   as a pointer array *)
Definition hs_table (am: option cmem) (tp: val) (tbl: list val) : mpred :=
  !! field_compatible (tarray (tptr t_ddict) (Zlength tbl)) nil tp &&
  (blk_tok am (tarray tuchar (8 * Zlength tbl)) tp *
   data_at Ews (tarray (tptr t_ddict) (Zlength tbl)) tbl tp).

(* zstd's DDict set at sp holding the DDicts l, allocated through the context's allocator am, holding hb bytes of it
   (set_bytes): none (NULL) for an empty set, else the struct and its table *)
Definition hset_rep (am: option cmem) (sp: val) (l: list (val * ddict_st)) (hb: Z) : mpred :=
  if eq_dec sp nullval then !! (l = nil /\ hb = 0) && emp
  else EX tp: val, EX tbl: list val,
       !! (hs_inv l tbl /\ l <> nil /\ hb = set_bytes am (Zlength tbl)) &&
       (blk_tok am t_hset sp *
        data_at Ews t_hset (tp, (Vlong (Int64.repr (Zlength tbl)), Vlong (Int64.repr (Zlength l)))) sp *
        hs_table am tp tbl).

End HSet.

(* the DDict lookup of a described set (non-zero distinct IDs): the DDict of that ID *)
Definition set_find (l: list (val * ddict_st)) (id: Z) : val :=
  match find (fun e => dd_id (snd e) =? id) l with Some e => fst e | None => nullval end.

(* ---------- the context ---------- *)

(* the tables: TUninit lxb uninitialised, litExtraBuffer holding the bytes lxb (the exact stream reads them back as
   slack, patch item 17); TInit ox ts B's TABS gv p ox ts (ox: the DDict they point into; ts: DecRep.tstate, the
   entropy state, the Huffman table's type and litExtraBuffer's bytes) *)
Inductive tabs3 : Type := TUninit (lxb: list Z) | TInit (ox: option ddx) (ts: tstate).

(* litExtraBuffer's bytes, whatever the tables' state *)
Definition tabs_lxb (t: tabs3) : list Z := match t with TUninit lxb => lxb | TInit _ ts => ts_lxb ts end.

(* litExtraBuffer zeroed: a new (calloc'd) context, or after ZSTD_DCtx_reset with the parameters (F8) *)
Definition lxb_zero : list Z := repeat 0 (Z.to_nat LITEXTRA_N).

Section Rep3.
Context {CMI: cmem_preds}.
Variable DENT : dent_pred.
Variable TABS : tabs_pred.

Definition tabs_rep (gv: globals) (p: val) (t: tabs3) : mpred :=
  match t with TUninit lxb => tables_uninit p lxb | TInit ox ts => TABS gv p ox ts end.

(* the frame group: format and the literal config (cfg_fmt, cfg_lit), the 18 frame fields, the tables, the
   parameters frame decoding reads, the DDict set pointer *)
Definition fgroup3 (gv: globals) (p: val) (fs: fstate) (t: tabs3) (pr: dparams) (sp: val) : mpred :=
  !! (cold01 fs /\ par_ok pr) &&
  (cfg_fmt p (dp_fmt pr) * cfg_lit p * frame_fields p fs * tabs_rep gv p t *
   field_at Ews t_dctx (DOT _forceIgnoreChecksum) (Vint (Int.repr (dp_ignore pr))) p *
   field_at Ews t_dctx (DOT _maxBlockSizeParam) (Vint (Int.repr (dp_bmax pr))) p *
   field_at Ews t_dctx (DOT _refMultipleDDicts) (Vint (Int.repr (dp_multi pr))) p *
   field_at Ews t_dctx (DOT _ddictSet) sp p).

(* the frame group without the tables (what ZSTD_decodeFrameHeader touches besides the selection) *)
Definition fcore3 (p: val) (fs: fstate) (pr: dparams) (sp: val) : mpred :=
  !! (par_ok pr) &&
  (cfg_fmt p (dp_fmt pr) * cfg_lit p * frame_fields p fs *
   field_at Ews t_dctx (DOT _forceIgnoreChecksum) (Vint (Int.repr (dp_ignore pr))) p *
   field_at Ews t_dctx (DOT _maxBlockSizeParam) (Vint (Int.repr (dp_bmax pr))) p *
   field_at Ews t_dctx (DOT _refMultipleDDicts) (Vint (Int.repr (dp_multi pr))) p *
   field_at Ews t_dctx (DOT _ddictSet) sp p).

(* the context's configuration (its customMem field is in the streaming group: FSRepC.mgroup) *)
Definition cgroup3 (p: val) (stable: bool) (wmax: Z) : mpred :=
  field_at Ews t_dctx (DOT _staticSize) (Vlong (Int64.repr 0)) p *
  field_at Ews t_dctx (DOT _maxWindowSize) (Vlong (Int64.repr wmax)) p *
  field_at Ews t_dctx (DOT _outBufferMode) (Vint (Int.repr (if stable then 1 else 0))) p.

(* the concrete state *)
Record cst3 := {
  c3_fs : fstate; c3_tabs : tabs3; c3_stable : bool; c3_dict : dfields; c3_s : sfields;
  c3_par : dparams; c3_sp : val; c3_set : list (val * ddict_st) }.

(* the context; its own allocator's other blocks (sf_held) are the local DDict's and the DDict set's *)
Definition ctx_body3 (gv: globals) (p: val) (k: cst3) : mpred :=
  fgroup3 gv p (c3_fs k) (c3_tabs k) (c3_par k) (c3_sp k) * cgroup3 p (c3_stable k) (dp_wmax (c3_par k)) *
  dgroup DENT gv p (c3_dict k) * sgroup p (c3_s k) *
  hset_rep (sf_mem (c3_s k)) (c3_sp k) (c3_set k) (sf_held (c3_s k) - local_held (c3_dict k)).

Definition ctx_rep3 (gv: globals) (p: val) (k: cst3) : mpred :=
  dctx_token p * dctx_pad p * ctx_body3 gv p k.

(* the caller's pointer of a DDict's content, as DecRep.ddx has it: Spec_api6's dd_ref, except for the DDict without
   content (ZSTD_createDDict(NULL, 0): no caller's memory, dd_ref = None and no bytes), whose content pointer is
   NULL (dx_ref = Some nullval).  Every other DDict with dd_ref = None is a copy of at least one byte. *)
Definition dd_xref (dd: ddict_st) : option val :=
  match dd_ref dd, dd_bytes dd with
  | None, nil => Some nullval
  | r, _ => r
  end.

(* the ddx a ZSTD_DDict state describes (API v3.1: dd_buf and dd_ld pin zstd's buffer and entropy-load result) *)
Definition dd_x (q: val) (dd: ddict_st) : ddx :=
  {| dx_q := q; dx_bytes := dd_bytes dd; dx_ref := dd_xref dd; dx_raw := false; dx_ld := dd_ld dd; dx_mem := None |}.

Lemma dd_xref_some (dd: ddict_st) (p: val) : dd_ref dd = Some p -> dd_xref dd = Some p.
Proof. intros E. unfold dd_xref. rewrite E. destruct (dd_bytes dd); reflexivity. Qed.

Lemma dd_xref_copy (dd: ddict_st) : dd_ref dd = None -> dd_bytes dd <> nil -> dd_xref dd = None.
Proof. intros E N. unfold dd_xref. rewrite E. destruct (dd_bytes dd); [contradiction | reflexivity]. Qed.

Lemma dd_xref_empty (dd: ddict_st) : dd_ref dd = None -> dd_bytes dd = nil -> dd_xref dd = Some nullval.
Proof. intros E N. unfold dd_xref. rewrite E, N. reflexivity. Qed.

(* the three kinds: by reference to the caller's p, a copy, or no content *)
Lemma dd_xref_cases (dd: ddict_st) :
  (exists p, dd_ref dd = Some p /\ dd_xref dd = Some p) \/
  (dd_ref dd = None /\ dd_bytes dd <> nil /\ dd_xref dd = None) \/
  (dd_ref dd = None /\ dd_bytes dd = nil /\ dd_xref dd = Some nullval).
Proof.
  unfold dd_xref. destruct (dd_ref dd) as [p|]; [left; exists p; destruct (dd_bytes dd); auto |].
  right. destruct (dd_bytes dd) as [|z l]; [right; auto | left; split; [auto | split; [discriminate | auto]]].
Qed.

(* Spec_api6's DD: a DDict made in ZSTD_dct_auto mode (by the caller, with the default allocator), its content at
   dd_buf, zstd's load result dd_ld *)
Definition DD3_of (gv: globals) (q: val) (dd: ddict_st) : mpred :=
  ddict_rep_at DENT gv (dd_x q dd) (dd_buf dd).

(* the DDicts of a set, all of them *)
Definition set_dds (gv: globals) (l: list (val * ddict_st)) : mpred :=
  fold_right sepcon emp (map (fun e => DD3_of gv (fst e) (snd e)) l).

End Rep3.

(* updates of the concrete state *)
Definition c3_with_fs (k: cst3) (fs: fstate) (t: tabs3) : cst3 :=
  {| c3_fs := fs; c3_tabs := t; c3_stable := c3_stable k; c3_dict := c3_dict k; c3_s := c3_s k;
     c3_par := c3_par k; c3_sp := c3_sp k; c3_set := c3_set k |}.
Definition c3_with_dict (k: cst3) (d: dfields) : cst3 :=
  {| c3_fs := c3_fs k; c3_tabs := c3_tabs k; c3_stable := c3_stable k; c3_dict := d; c3_s := c3_s k;
     c3_par := c3_par k; c3_sp := c3_sp k; c3_set := c3_set k |}.
Definition c3_with_s (k: cst3) (s: sfields) : cst3 :=
  {| c3_fs := c3_fs k; c3_tabs := c3_tabs k; c3_stable := c3_stable k; c3_dict := c3_dict k; c3_s := s;
     c3_par := c3_par k; c3_sp := c3_sp k; c3_set := c3_set k |}.
Definition c3_with_stable (k: cst3) (b: bool) : cst3 :=
  {| c3_fs := c3_fs k; c3_tabs := c3_tabs k; c3_stable := b; c3_dict := c3_dict k; c3_s := c3_s k;
     c3_par := c3_par k; c3_sp := c3_sp k; c3_set := c3_set k |}.
Definition c3_with_par (k: cst3) (pr: dparams) : cst3 :=
  {| c3_fs := c3_fs k; c3_tabs := c3_tabs k; c3_stable := c3_stable k; c3_dict := c3_dict k; c3_s := c3_s k;
     c3_par := pr; c3_sp := c3_sp k; c3_set := c3_set k |}.
Definition c3_with_set (k: cst3) (sp: val) (l: list (val * ddict_st)) : cst3 :=
  {| c3_fs := c3_fs k; c3_tabs := c3_tabs k; c3_stable := c3_stable k; c3_dict := c3_dict k; c3_s := c3_s k;
     c3_par := c3_par k; c3_sp := sp; c3_set := l |}.

(* ---------- the abstract state ---------- *)

(* the dictionary fields after zstd selected a frame's DDict from the set (ZSTD_DCtx_selectFrameDDict): the local
   DDict freed, the set's DDict referenced indefinitely *)
Definition dict_switched (l: list (val * ddict_st)) (d: dfields) : Prop :=
  df_local d = nullval /\ df_uses d = -1 /\ df_lx d = None /\ In (df_ddict d) (map fst l).

(* the dictionary fields of a context whose dictionary is od (Spec_api6.dc_dict, API v3.1's dsrc): no
   dictionary (none in use: NULL, or a local DDict left after a used-once prefix), a DDict of the caller, zstd's
   copy (raw content allowed: ZSTD_DCtx_loadDictionary_advanced), or the caller's bytes by reference *)
Definition dict_rel3_of (od: option dictref) (d: dfields) : Prop :=
  match od with
  | None => df_uses d = 0 /\ (df_ddict d = nullval \/ df_ddict d = df_local d)
  | Some dr =>
      let b := dr_bytes dr in
      match dr_src dr with
      | DSDDict q dd =>
          dr_raw dr = false /\ dr_once dr = false /\ isptr q /\ df_local d = nullval /\ df_ddict d = q /\ df_uses d = -1 /\
          dr_bytes dr = dd_bytes dd
      | DSOwn =>
          dr_once dr = false /\
          if Zlength b =? 0 then d = df_none
          else exists buf ld am, isptr (df_local d) /\ df_ddict d = df_local d /\ df_uses d = -1 /\
                 df_lx d = Some ({| dx_q := df_local d; dx_bytes := b; dx_ref := None; dx_raw := dr_raw dr; dx_ld := ld;
                                    dx_mem := am |}, buf)
      | DSRef pk =>
          if Zlength b =? 0 then
            df_local d = nullval /\ df_ddict d = nullval /\ df_uses d = (if dr_once dr then 1 else 0)
          else isptr (df_local d) /\ df_ddict d = df_local d /\ df_uses d = (if dr_once dr then 1 else -1) /\
               exists ld am, df_lx d = Some ({| dx_q := df_local d; dx_bytes := b; dx_ref := Some pk; dx_raw := dr_raw dr;
                                               dx_ld := ld; dx_mem := am |}, pk)
      end
  end.

(* ... or, with a set, a DDict selected from it *)
Definition dict_rel3 (st: dctx_st) (d: dfields) : Prop :=
  dict_rel3_of (dc_dict st) d \/ (dc_set st <> nil /\ dict_switched (dc_set st) d).

(* the context's DDict, when also in the set, is the set's entry (both come from one ZSTD_DCtx_refDDict) *)
Definition set_cur_ok (st: dctx_st) : Prop :=
  forall dr q dd dd', dc_dict st = Some dr -> dr_src dr = DSDDict q dd -> In (q, dd') (dc_set st) -> dd' = dd.

(* fp_dictID (the dictID field of a reptype t_fh) is Spec_api6's (API v3.4) *)
(* fParams' dictID is a 32-bit value: zstd's streaming selection probes it before a header is complete *)
Definition fp_ok (f: reptype t_fh) : Prop :=
  exists id, fp_dictID f = Vint (Int.repr id) /\ 0 <= id <= Int.max_unsigned.

(* room for a stream next to the dictionaries: a context's own allocator has given out nothing but the context and
   the stream buffer, or its bound leaves room for the largest stream buffers besides (Spec_api6.cm_raised: a call
   that allocates a DDict or the set raises the bound so); nothing besides for the default one *)
Definition mem_room (s: sfields) : Prop :=
  match sf_mem s with
  | None => sf_held s = 0
  | Some m => sf_held s = 0 \/ sf_held s + dstream_size (2 ^ 31) <= cm_bound m
  end.

(* the local DDict of a context's own allocator is a live one (zstd made it by copy) of that allocator (with the
   bound of its time: CMem.cm_same); the default allocator's are of the default one (a leftover's too:
   DecIface.ddict_failed) *)
Definition local_mem (am: option cmem) (d: dfields) : Prop :=
  df_local d <> nullval ->
  (am <> None -> df_lx d <> None) /\ (forall x buf, df_lx d = Some (x, buf) -> cm_same (dx_mem x) am).

(* the context's allocator (FSRepC.sf_mem) is the abstract one (Spec_api6.dc_mem, with its bound); besides the
   context and the stream buffer it has given out the local DDict's and the set's blocks (ctx_body3: sf_held) *)
Definition mem_rel3 (st: dctx_st) (k: cst3) : Prop :=
  sf_mem (c3_s k) = dc_mem st /\ mem_room (c3_s k) /\ local_mem (sf_mem (c3_s k)) (c3_dict k).

(* the streaming fields a stream state needs: unless the stream failed (no stream call before a session reset),
   zstd's count of calls without progress stays within its limit (its increment must not overflow); a context before
   any stream is at zdss_init with no such call *)
Definition stage_rel3 (ss: sstate) (s: sfields) : Prop :=
  (ss_err ss = false -> 0 <= sf_nfp s <= ZSTD_NO_FORWARD_PROGRESS_MAX) /\
  (ss = ss_init -> sf_stage s = 0 /\ sf_nfp s = 0).

Definition base_rel3 (st: dctx_st) (k: cst3) : Prop :=
  c3_stable k = dc_stable st /\ c3_par k = dc_par st /\ c3_set k = dc_set st /\
  dict_rel3 st (c3_dict k) /\ set_cur_ok st /\ fp_ok (fs_fParams (c3_fs k)) /\
  stage_rel3 (dc_ss st) (c3_s k) /\
  (dc_bl st <> None -> dc_ss st = ss_init /\ fs_isFrameDecompression (c3_fs k) = Vint (Int.repr 1)) /\
  mem_rel3 st k.

Lemma base_rel3_mem (st: dctx_st) (k: cst3) : base_rel3 st k -> mem_rel3 st k.
Proof. intros (_ & _ & _ & _ & _ & _ & _ & _ & Hm). exact Hm. Qed.

(* the concrete state with the allocator's bound raised as set_ss raises the abstract one *)
Definition c3_raise (k: cst3) (w: Z) : cst3 := c3_with_s k (sf_with_mem (c3_s k) (cm_raise (sf_mem (c3_s k)) w)).

Lemma mem_rel3_raise (st: dctx_st) (k: cst3) (ss: sstate) :
  mem_rel3 st k -> mem_rel3 (set_ss st ss) (c3_raise k (dp_wmax (dc_par st))).
Proof.
  intros (Hm & Hh & Hn). unfold mem_rel3, mem_room, local_mem, c3_raise, set_ss in *; simpl in *. rewrite Hm in *.
  split; [reflexivity | split].
  - destruct (dc_mem st) as [m|]; simpl; [| exact Hh]. destruct Hh as [Hh | Hh]; [left; exact Hh | right; lia].
  - intros E. destruct (Hn E) as [Hn1 Hn2]. split.
    + intros E'. apply Hn1. intros E''. apply E'. rewrite E''. reflexivity.
    + intros x buf Hx. exact (cm_same_trans _ _ _ (Hn2 x buf Hx) (cm_same_raise _ _)).
Qed.

(* mem_rel3 for a state built from st by setters other than set_ss, the concrete state keeping its allocator, its
   local DDict and set pointer (tactic: the goal mem_rel3 st' k' after simpl) *)
Ltac dc_mem_tac :=
  match goal with H: mem_rel3 _ _ |- mem_rel3 _ _ => unfold mem_rel3 in *; simpl in *; exact H end.

(* the streaming fields without the allocator and its other blocks (what the exact relation sees) *)
Definition sf_strip (s: sfields) : sfields :=
  {| sf_stage := sf_stage s; sf_inBuff := sf_inBuff s; sf_inSize := sf_inSize s; sf_inPos := sf_inPos s;
     sf_outBuff := sf_outBuff s; sf_outSize := sf_outSize s; sf_outStart := sf_outStart s; sf_outEnd := sf_outEnd s;
     sf_lhSize := sf_lhSize s; sf_hostage := sf_hostage s; sf_nfp := sf_nfp s; sf_expOut := sf_expOut s;
     sf_hbuf := sf_hbuf s; sf_over := sf_over s; sf_ring := sf_ring s; sf_mem := None; sf_held := 0 |}.

(* the streaming part's relations (it sees the program's globals: in stable mode, an output buffer passed as NULL
   has the base ZSTD_emptyBuffer):
   - sr_run: a relation between a running stream (dc_ss not ss_init, no error) and the concrete state, unless the
     stream is a new one at zdss_init (Spec_api6.ss_restart: after a setter between frames or a one-shot);
   - sr_ex: Spec_api6.dc_ex's meaning, a relation between the calls since the last reset (ss_calls) and the
     streaming fields (sf_strip), frame fields and tables: they are the image of what the calls do to a clean
     context (model/Exact.v's zs_call);
   - sr_ex_clean: a clean context (zdss_init, no buffers, oversizedDuration and noForwardProgress 0, litExtraBuffer
     zeroed) is the image of no call. *)
Record srel3 : Type := {
  sr_run :> globals -> dctx_st -> cst3 -> Prop;
  sr_ex : list zcall -> sfields -> fstate -> tabs3 -> Prop;
  sr_ex_clean : forall s fs, sf_stage s = 0 -> sf_inSize s = 0 -> sf_outSize s = 0 -> sf_over s = 0 ->
                  sf_nfp s = 0 -> sr_ex nil (sf_strip s) fs (TUninit lxb_zero) }.

(* dc_ex in the concrete state: unless the stream failed, a context with dc_ex is the image of its calls since the
   reset, at a stream's start (dc_ss = ss_init, any configuration: the next call is in zdss_init, the configuration is
   read from there on) or within the configuration of a new context (Spec_api6.fresh_cfg: a configuration change
   needs dc_ss = ss_init or restarts the stream, which clears dc_ex) *)
Definition ex_on3 (SR: srel3) (st: dctx_st) (k: cst3) : Prop :=
  dc_ex st = true -> ss_err (dc_ss st) = false ->
  (dc_ss st = ss_init \/
   (dc_dict st = None /\ dc_par st = dparams_dflt /\ dc_set st = nil /\ dc_stable st = false)) ->
  sr_ex SR (ss_calls (dc_ss st)) (sf_strip (c3_s k)) (c3_fs k) (c3_tabs k).

(* kept by any change of the context that keeps the stream, dc_ex (or clears it), the streaming fields up to the
   allocator, the frame fields and the tables, and (within a stream) the configuration *)
Lemma ex_on3_keep (SR: srel3) (st st': dctx_st) (k k': cst3) :
  ex_on3 SR st k -> dc_ss st' = dc_ss st -> (dc_ex st' = true -> dc_ex st = true) ->
  sf_strip (c3_s k') = sf_strip (c3_s k) -> c3_fs k' = c3_fs k -> c3_tabs k' = c3_tabs k ->
  (dc_ss st = ss_init \/ (dc_dict st' = dc_dict st /\ dc_par st' = dc_par st /\ dc_set st' = dc_set st /\
                          dc_stable st' = dc_stable st)) ->
  ex_on3 SR st' k'.
Proof.
  intros H Ess Eex Es Efs Et Ecf E1 E2 E3. unfold ex_on3 in *. rewrite Ess, Es, Efs, Et. rewrite Ess in E2, E3.
  apply H; [exact (Eex E1) | exact E2 |].
  destruct E3 as [E3 | (D & P & S & B)]; [left; exact E3 |].
  destruct Ecf as [Ei | (D' & P' & S' & B')]; [left; exact Ei |].
  right. rewrite <- D', <- P', <- S', <- B'. auto.
Qed.

(* vacuous without dc_ex, or after a failed call *)
Lemma ex_on3_noex (SR: srel3) (st: dctx_st) (k: cst3) : dc_ex st = false -> ex_on3 SR st k.
Proof. unfold ex_on3. intros E H. congruence. Qed.

Lemma ex_on3_err (SR: srel3) (st: dctx_st) (k: cst3) : ss_err (dc_ss st) = true -> ex_on3 SR st k.
Proof. unfold ex_on3. intros E _ H. congruence. Qed.

(* a relation between a buffer-less frame and the context's parameters (those of the Begin, since every setter
   ends the frame), the frame fields, tables and headerBuffer: the buffer-less part's *)
Definition blrel : Type := dparams -> blabs -> fstate -> tabs3 -> list val -> Prop.

Section DC3.
Context {CMI: cmem_preds}.

Definition DC3_of (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR: blrel)
    (gv: globals) (p: val) (st: dctx_st) : mpred :=
  EX k: cst3,
  !! (base_rel3 st k /\
      (dc_ss st <> ss_init -> ss_err (dc_ss st) = false ->
         SR gv st k \/ (dc_ss st = ss_restart /\ sf_stage (c3_s k) = 0)) /\
      (forall ba, dc_bl st = Some ba -> BR (c3_par k) ba (c3_fs k) (c3_tabs k) (sf_hbuf (c3_s k))) /\
      ex_on3 SR st k) &&
  ctx_rep3 DENT TABS gv p k.

(* the streaming group with its allocator's bound raised (CM_mono) *)
Lemma sgroup_raise (p: val) (s: sfields) (w: Z) :
  sgroup p s |-- sgroup p (sf_with_mem s (cm_raise (sf_mem s) w)).
Proof.
  unfold sgroup, ring_rep, mgroup, sf_given, sf_with_mem; simpl.
  rewrite !blk_tok_raise, cmem_v_raise, cmem_ok_raise.
  Intros. apply andp_right; [apply prop_right; tauto |]. cancel. apply cm_have_raise.
Qed.

(* the set's representation does not see the bound *)
Lemma hset_rep_raise (am: option cmem) (w: Z) (sp: val) (l: list (val * ddict_st)) (hb: Z) :
  hset_rep (cm_raise am w) sp l hb = hset_rep am sp l hb.
Proof.
  assert (Eb: forall n, set_bytes (cm_raise am w) n = set_bytes am n) by (destruct am; reflexivity).
  unfold hset_rep, hs_table. rewrite !blk_tok_raise.
  destruct (eq_dec sp nullval); [reflexivity |]. f_equal; extensionality tp; f_equal; extensionality tbl.
  rewrite Eb, !blk_tok_raise. reflexivity.
Qed.

Lemma ctx_rep3_raise (DENT: dent_pred) (TABS: tabs_pred) (gv: globals) (p: val) (k: cst3) (w: Z) :
  ctx_rep3 DENT TABS gv p k |-- ctx_rep3 DENT TABS gv p (c3_raise k w).
Proof.
  unfold ctx_rep3, ctx_body3, c3_raise, c3_with_s; simpl.
  rewrite hset_rep_raise.
  sep_apply (sgroup_raise p (c3_s k) w). cancel.
Qed.

End DC3.
