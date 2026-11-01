(* API v3, subtree B, group DICT: ZSTD_decompressBegin_usingDDict after the
   contract's VST-layer change (ddictIsCold = 1, no dictEnd comparison), any format (v2: B/dict/body_dict_ddict.v,
   which no longer compiles against the new code.v). *)
Require Export Zstd.proof.dec.v3.B.BSpecs3.
Local Open Scope logic.

(* do { c } while (0), as Clight's Sloop c Sbreak (recipes of H's body_H_skip.v) *)
Ltac reassoc3 := repeat match goal with
  |- semax _ _ (Ssequence (Ssequence _ _) _) _ => apply -> seq_assoc end.
Ltac once_loop3 Q := reassoc3;
  match goal with |- semax _ ?P (Ssequence (Sloop _ Sbreak) _) _ =>
    forward_loop P break: Q; [apply andp_left2, derives_refl | | ] end.
Ltac skip_loop3 :=
  match goal with |- semax _ ?P _ _ => forward_loop P break: P end; try solve [entailer!]; try solve [forward; entailer!].

Lemma ddict3_begin_tabs_init (gv: globals) (p: val) (ox: option ddx) (lxb: list Z) :
  begin_tabs p lxb |-- tabs_def gv p ox (tstate_begin lxb).
Proof.
  unfold begin_tabs, tabs_def, tabs_huf, tabs_seq, tstate_begin, dstate_init; simpl.
  Exists (ctx_huf p). entailer!.
  unfold dstate_ok, rep_ok, seqs_ok; simpl; repeat split; lia.
Qed.

Ltac fs_proj3 := cbn [fs_previousDstEnd fs_gpDictCopy fs_prefixStart fs_virtualStart fs_dictEnd fs_expected
  fs_fParams fs_processedCSize fs_decodedSize fs_bType fs_stage fs_xxh fs_headerSize fs_validateChecksum
  fs_rleSize fs_isFrameDecompression fs_dictID fs_ddictIsCold].

(* `if (ddict)`: the DDict's struct gives a valid pointer *)
Ltac ddict_tc3 x :=
  apply denote_tc_test_eq_split; [| apply valid_pointer_null]; unfold ddict_struct; Intros;
  assert (Hv: forall v, field_at Ews (Tstruct _ZSTD_DDict_s noattr) (DOT _dictBuffer) v (dx_q x)
                        |-- valid_pointer (dx_q x))
    by (intros; apply field_at_valid_ptr0; [auto | simpl; lia | reflexivity]);
  auto 50 with valid_pointer.

(* the body for an allocator class: the DDict's memory is of its allocator; B uses only its copy's bytes *)
Section DD3.
Context {CMI: cmem_preds}.

(* a DDict's memory: its allocation tokens and its copy's bytes (DictSpecs.ddict_copy, what
   ZSTD_copyDDictParameters needs) *)
Lemma ddict_mem_split (x: ddx) (buf: val) :
  ddict_mem x buf =
  (blk_tok (dx_mem x) (Tstruct _ZSTD_DDict_s noattr) (dx_q x) *
   (if ddx_copied x then blk_tok (dx_mem x) (tarray tuchar (Zlength (dx_bytes x))) buf else emp)) *
  ddict_copy x buf.
Proof.
  unfold ddict_mem, ddict_copy. destruct (ddx_copied x).
  - rewrite !sepcon_assoc. reflexivity.
  - rewrite !sepcon_emp. reflexivity.
Qed.

Lemma DICT3_ddict_ok : body_ok DICT3_G (ZSTD_decompressBegin_usingDDict_spec3 dent_def tabs_def).
Proof.
  exists f_ZSTD_decompressBegin_usingDDict; split; [reflexivity | split; [reflexivity |]].
  start_function.
  destruct ox as [x|].
  - assert_PROP (isptr (dx_q x)) as Hq by (unfold ddict_struct; entailer!).
    flatten_sepcon_in_SEP. flatten_sepcon_in_SEP.
    skip_loop3.
    forward_if (PROP ()
                LOCAL (temp _dctx p; temp _ddict (dx_q x); gvars gv)
                SEP (zstd_globals gv; pws_pred W; cfg_fmt p f; cfg_lit p;
                     frame_fields p (fs_set_cold fs (Vint (Int.repr 1))); tables_uninit p lxb;
                     ddict_struct x buf; dent_def gv (dx_q x) (ddx_ent x); ddict_mem x buf)).
    { ddict_tc3 x. }
    + unfold frame_fields. Intros. forward. skip_loop3.
      unfold frame_fields, fs_set_cold. fs_proj3. entailer!.
    + destruct x as [q b r raw]; simpl in *; subst q; contradiction.
    + once_loop3 (PROP () LOCAL (temp _dctx p; temp _ddict (dx_q x); gvars gv)
                 SEP (zstd_globals gv; pws_pred W; cfg_fmt p f; cfg_lit p;
                      frame_fields p (fs_begin3 (fs_set_cold fs (Vint (Int.repr 1))) f);
                      begin_tabs p lxb; ddict_struct x buf;
                      dent_def gv (dx_q x) (ddx_ent x); ddict_mem x buf)).
      { forward_call (gv, p, fs_set_cold fs (Vint (Int.repr 1)), f, lxb). forward_call 0.
        forward_if; [contradiction | forward; entailer! ]. }
      forward_if (PROP () LOCAL (temp _dctx p; temp _ddict (dx_q x); gvars gv)
                  SEP (zstd_globals gv; pws_pred W; cfg_fmt p f; cfg_lit p;
                       frame_fields p
                         (fs_set_dictEnd
                            (fs_with_dict (fs_begin3 (fs_set_cold fs (Vint (Int.repr 1))) f) buf (ddx_end x buf)
                               (if ddx_copied x then 1 else 0)
                               (if dx_raw x then 0 else dict_id_of (dx_bytes x)))
                            (ddx_end x buf));
                       tabs_def gv p (Some x) (mk_tstate (ddx_state x) false lxb); ddict_struct x buf;
                       dent_def gv (dx_q x) (ddx_ent x); ddict_mem x buf)).
      { ddict_tc3 x. }
      { rewrite ddict_mem_split. repeat flatten_sepcon_in_SEP.
        forward_call (gv, p, fs_begin3 (fs_set_cold fs (Vint (Int.repr 1))) f, x, buf, lxb).
        rewrite ddict_mem_split. entailer!. }
      { destruct x as [q b r raw]; simpl in *; subst q; contradiction. }
      forward. Exists (Vint (Int.repr 1)). entailer!. apply derives_refl.
  - simpl. skip_loop3.
    forward_if (PROP () LOCAL (temp _dctx p; temp _ddict nullval; gvars gv)
                SEP (zstd_globals gv; pws_pred W; cfg_fmt p f; cfg_lit p; frame_fields p fs; tables_uninit p lxb)).
    { inversion H0. }
    { forward. entailer!. }
    once_loop3 (PROP () LOCAL (temp _dctx p; temp _ddict nullval; gvars gv)
               SEP (zstd_globals gv; pws_pred W; cfg_fmt p f; cfg_lit p; frame_fields p (fs_begin3 fs f); begin_tabs p lxb)).
    { forward_call (gv, p, fs, f, lxb). forward_call 0.
      forward_if; [contradiction | forward; entailer! ]. }
    forward_if (PROP () LOCAL (temp _dctx p; temp _ddict nullval; gvars gv)
                SEP (zstd_globals gv; pws_pred W; cfg_fmt p f; cfg_lit p; frame_fields p (fs_begin3 fs f); begin_tabs p lxb)).
    { inversion H0. }
    { forward. entailer!. }
    forward. Exists (fs_ddictIsCold fs). entailer!. apply ddict3_begin_tabs_init.
Qed.

End DD3.
