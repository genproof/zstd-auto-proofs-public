(* Group ENT: the dispatching wrappers (bmi2 = 0, DYNAMIC_BMI2 = 0). *)
Require Import Zstd.proof.dec.B.ent.EntSpecs.
Local Open Scope logic.

Lemma body_w_ncount_default :
  semax_body Vprog (G_B0 ++ [FSE_readNCount_body_spec])
    f_FSE_readNCount_body_default FSE_readNCount_body_default_spec.
Proof.
  start_function.
  forward_call (gv, shn, pn, nn, shm, pm, sht, pt, maxsv, sh, base, N, c, off, s).
  Intros vret. destruct vret as [[r nc] res]. simpl fst in *; simpl snd in *.
  match goal with h: res = x_ncount _ _ |- _ => subst res end.
  forward. Exists r nc (x_ncount s maxsv). entailer!.
Qed.

Lemma body_w_ncount_bmi2 :
  semax_body Vprog (G_B0 ++ [FSE_readNCount_body_default_spec])
    f_FSE_readNCount_bmi2 FSE_readNCount_bmi2_spec.
Proof.
  start_function.
  forward_if (PROP () LOCAL (temp _normalizedCounter pn; temp _maxSVPtr pm; temp _tableLogPtr pt;
      temp _headerBuffer (offset_val off base); temp _hbSize (Vlong (Int64.repr (Zlength s))); gvars gv)
    SEP (zstd_globals gv; data_at_ shn (tarray tshort nn) pn; data_at shm tuint (Vint (Int.repr maxsv)) pm;
         data_at_ sht tuint pt; data_at sh (tarray tuchar N) c base)).
  { exfalso; congruence. }
  { forward. entailer!. }
  forward_call (gv, shn, pn, nn, shm, pm, sht, pt, maxsv, sh, base, N, c, off, s).
  Intros vret. destruct vret as [[r nc] res]. simpl fst in *; simpl snd in *.
  match goal with h: res = x_ncount _ _ |- _ => subst res end.
  forward. Exists r nc (x_ncount s maxsv). entailer!.
Qed.

Lemma body_w_wksp_default :
  semax_body Vprog (G_B0 ++ [FSE_decompress_wksp_body_spec])
    f_FSE_decompress_wksp_body_default FSE_decompress_wksp_body_default_spec.
Proof.
  start_function.
  forward_call (gv, shw, pw, oc, sh, base, N, c, off, s, shk, pk, nk).
  Intros vret. destruct vret as [[r oc'] res]. simpl fst in *; simpl snd in *.
  match goal with h: res = x_ncount _ _ |- _ => subst res end.
  forward. Exists r oc' (x_ncount s 255). entailer!.
Qed.

Lemma body_w_wksp_bmi2 :
  semax_body Vprog (G_B0 ++ [FSE_decompress_wksp_body_default_spec])
    f_FSE_decompress_wksp_bmi2 FSE_decompress_wksp_bmi2_spec.
Proof.
  start_function.
  forward_if (PROP () LOCAL (temp _dst pw; temp _dstCapacity (Vlong (Int64.repr 255));
      temp _cSrc (offset_val off base); temp _cSrcSize (Vlong (Int64.repr (Zlength s)));
      temp _maxLog (Vint (Int.repr 6)); temp _workSpace pk; temp _wkspSize (Vlong (Int64.repr (4 * nk))); gvars gv)
    SEP (zstd_globals gv; data_at shw (tarray tuchar 256) oc pw; data_at sh (tarray tuchar N) c base;
         data_at_ shk (tarray tuint nk) pk)).
  { exfalso; congruence. }
  { forward. entailer!. }
  forward_call (gv, shw, pw, oc, sh, base, N, c, off, s, shk, pk, nk).
  Intros vret. destruct vret as [[r oc'] res]. simpl fst in *; simpl snd in *.
  match goal with h: res = x_ncount _ _ |- _ => subst res end.
  forward. Exists r oc' (x_ncount s 255). entailer!.
Qed.

Lemma body_w_readstats_default :
  semax_body Vprog (G_B0 ++ [HUF_readStats_body_spec])
    f_HUF_readStats_body_default HUF_readStats_body_default_spec.
Proof.
  start_function.
  forward_call (gv, shw, pw, shr, pr, shs, ps, sht, pt, sh, base, N, c, off, s, shk, pk, nk).
  Intros vret. destruct vret as [[r wc] res]. simpl fst in *; simpl snd in *.
  forward. Exists r wc res. entailer!.
Qed.

Lemma body_w_buildfse_default :
  semax_body Vprog (G_B0 ++ [ZSTD_buildFSETable_body_spec])
    f_ZSTD_buildFSETable_body_default ZSTD_buildFSETable_body_default_spec.
Proof.
  start_function.
  (* gv (sk_gbase k) must be a concrete global for entailer: case on the kind *)
  destruct k; match goal with H: ncount_ok _ _ (sk_max ?K) |- _ =>
    forward_call (gv, K, shd, dt, shn, pn, nc, norm, log, shw, pw, nw) end; entailer!.
Qed.

Lemma body_w_buildfse :
  semax_body Vprog (G_B0 ++ [ZSTD_buildFSETable_body_default_spec])
    f_ZSTD_buildFSETable ZSTD_buildFSETable_spec.
Proof.
  start_function.
  (* gv (sk_gbase k) must be a concrete global for entailer: case on the kind *)
  destruct k; (forward_if; [exfalso; congruence | ]); match goal with H: ncount_ok _ _ (sk_max ?K) |- _ =>
    forward_call (gv, K, shd, dt, shn, pn, nc, norm, log, shw, pw, nw) end; entailer!.
Qed.

Lemma body_ent_wrappers :
  semax_body Vprog (G_B0 ++ [FSE_readNCount_body_spec])
    f_FSE_readNCount_body_default FSE_readNCount_body_default_spec /\
  semax_body Vprog (G_B0 ++ [FSE_readNCount_body_default_spec])
    f_FSE_readNCount_bmi2 FSE_readNCount_bmi2_spec /\
  semax_body Vprog (G_B0 ++ [FSE_decompress_wksp_body_spec])
    f_FSE_decompress_wksp_body_default FSE_decompress_wksp_body_default_spec /\
  semax_body Vprog (G_B0 ++ [FSE_decompress_wksp_body_default_spec])
    f_FSE_decompress_wksp_bmi2 FSE_decompress_wksp_bmi2_spec /\
  semax_body Vprog (G_B0 ++ [HUF_readStats_body_spec])
    f_HUF_readStats_body_default HUF_readStats_body_default_spec /\
  semax_body Vprog (G_B0 ++ [ZSTD_buildFSETable_body_spec])
    f_ZSTD_buildFSETable_body_default ZSTD_buildFSETable_body_default_spec /\
  semax_body Vprog (G_B0 ++ [ZSTD_buildFSETable_body_default_spec])
    f_ZSTD_buildFSETable ZSTD_buildFSETable_spec.
Proof.
  split; [exact body_w_ncount_default|]. split; [exact body_w_ncount_bmi2|].
  split; [exact body_w_wksp_default|]. split; [exact body_w_wksp_bmi2|].
  split; [exact body_w_readstats_default|]. split; [exact body_w_buildfse_default|].
  exact body_w_buildfse.
Qed.
