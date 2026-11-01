(* ZSTD_decompress_insertDictionary's error branch also keeps dctx->fParams (the error path
   writes only dictID), as DecIface3.ZSTD_decompressBegin_usingDict_spec3 now requires; group DICT's context
   with that specification.  The rest of BSpecs3 is unchanged. *)
Require Export Zstd.proof.dec.v3.B.BSpecs3.
Local Open Scope logic.

(* BSpecs3.ZSTD_decompress_insertDictionary_spec3 with fs_fParams fs' = fs_fParams fs in the error branch *)
Definition ZSTD_decompress_insertDictionary_spec34 : ident * funspec :=
  DECLARE _ZSTD_decompress_insertDictionary
  WITH gv: globals, p: val, fs: fstate, shk: share, dk: val, b: list Z, f: Z, lxb: list Z
  PRE [ tptr t_dctx, tptr tvoid, tulong ]
    PROP (readable_share shk; 0 < Zlength b <= 2 ^ 63 - 1; bytes_ok b)
    PARAMS (p; dk; Vlong (Int64.repr (Zlength b))) GLOBALS (gv)
    SEP (zstd_globals gv; frame_fields p (fs_begin3 fs f); begin_tabs p lxb;
         data_at shk (tarray tuchar (Zlength b)) (zbytes b) dk)
  POST [ tulong ]
    EX r: Z, EX ores: option (dstate * Z),
    PROP (0 <= r <= Int64.max_unsigned; ld_rel b ores)
    RETURN (Vlong (Int64.repr r))
    SEP (zstd_globals gv;
         match dict_auto_c b ores with
         | None => !! (is_error_code r = true) &&
             EX fs': fstate, !! (fs_dictEnd fs' = nullval /\ fs_ddictIsCold fs' = fs_ddictIsCold fs /\
                                 fs_fParams fs' = fs_fParams fs) &&
               frame_fields p fs' * tables_uninit p lxb
         | Some dm =>
             !! (r = 0) &&
             frame_fields p (fs_with_dict (fs_begin3 fs f) (offset_val (Zlength b - Zlength (dm_content dm)) dk)
                               (offset_val (Zlength b) dk) 0 (dm_id dm)) *
             EX x2: bool, tabs_def gv p None (mk_tstate (dm_state dm) x2 lxb)
         end;
         data_at shk (tarray tuchar (Zlength b)) (zbytes b) dk).

Section DICT34.
Context {CMI: cmem_preds}.

(* one specification per function of ids_DICT, in that order (BSpecs3.DICT3_specs with the spec above) *)
Definition DICT34_specs : funspecs :=
  [ ZSTD_DDict_dictContent_spec; ZSTD_DDict_dictSize_spec; ZSTD_copyDDictParameters_spec;
    ZSTD_loadEntropy_intoDDict_spec3; ZSTD_initDDict_internal_spec3 dent_def; ZSTD_refDictContent_spec;
    ZSTD_loadDEntropy_spec; ZSTD_decompress_insertDictionary_spec34; ZSTD_decompressBegin_spec3s;
    ZSTD_decompressBegin_usingDict_spec3 tabs_def; ZSTD_decompressBegin_usingDDict_spec3 dent_def tabs_def ].

Definition DICT34_G : funspecs := (G_B03 ++ ENT_exports ++ HUF_exports) ++ DICT34_specs.

Lemma DICT34_specs_ids : map fst DICT34_specs = ids_DICT.
Proof. reflexivity. Qed.

End DICT34.

Lemma ins34_sub3 :
  funspec_sub (snd ZSTD_decompress_insertDictionary_spec34) (snd ZSTD_decompress_insertDictionary_spec3).
Proof.
  apply NDsubsume_subsume; [split; reflexivity|].
  split; [split; reflexivity|].
  intros x [g args]. simpl.
  Exists x (@emp mpred _ _). rewrite emp_sepcon. destruct x as [[[[[[[gv p] fs] shk] dk] b] f] lxb]. simpl.
  apply andp_right.
  - apply andp_left2. apply derives_refl.
  - apply prop_right; intros rho'. rewrite emp_sepcon. apply andp_left2.
    apply exp_derives; intros r. apply exp_derives; intros ores.
    unfold PROPx, LOCALx, SEPx; simpl. apply andp_derives; [auto |]. apply andp_derives; [auto |].
    apply sepcon_derives; [auto |]. apply sepcon_derives; [| auto].
    destruct (dict_auto_c b ores); [auto |].
    apply andp_derives; [auto |]. apply exp_derives; intros fs'.
    first [ apply andp_derives; [apply prop_derives; tauto | apply derives_refl]
          | apply sepcon_derives; [apply andp_derives; [apply prop_derives; tauto | apply derives_refl] | apply derives_refl] ].
Qed.
