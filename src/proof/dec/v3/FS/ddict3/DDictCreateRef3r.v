(* FS3 ddict3: ZSTD_createDDict_byReference (port of v2 body_FS_ddict.v; DD3_of pinned by dd_buf/dd_ld) *)
Require Import Zstd.proof.dec.v3.FS.FSOblig3.
Require Import Zstd.proof.dec.v3.FS.ddict3.DDictLayout3 Zstd.proof.dec.v3.FS.ddict3.DDictLift3.
Local Open Scope logic.

Section CM_DDictCreateRef3r_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Definition G_createDDict_byReference_r (DENT: dent_pred) : funspecs := [ZSTD_createDDict_advancedP_spec3 DENT].

Lemma body_createDDict_byReference_small_r (DENT: dent_pred) : body_ok (G_createDDict_byReference_r DENT) (ZSTD_createDDict_byReference_spec (DD3x DENT)).
Proof.
  exists f_ZSTD_createDDict_byReference; split; [reflexivity | split; [reflexivity | ]].
  unfold G_createDDict_byReference_r.
  start_function.
  forward. forward. forward.
  assert_PROP (isptr p) as Hp by entailer!.
  rewrite <- (bytes_at_ptr sh b p Hp).
  forward_call (W, gv, sh, p, b, 1, 0, Tsh, v_allocator, @None cmem, 0).
  { unfold cm_have. cancel. }
  Intros q.
  rewrite (bytes_at_ptr sh b p Hp).
  forward.
  destruct (eq_dec q nullval) as [Hq|Hq].
  { Exists q {| dd_bytes := b; dd_ref := Some p; dd_buf := nullval; dd_ld := None |}.
    destruct (eq_dec q nullval); [ | contradiction]. unfold cm_have. entailer!. }
  Intros buf ores. Intros.
  rewrite ddx_of3_none.
  Exists q {| dd_bytes := b; dd_ref := Some p; dd_buf := buf; dd_ld := ores |}.
  destruct (eq_dec q nullval); [contradiction | ].
  unfold cm_have.
  sep_apply (ddict_rep_at_props DENT gv (ddx_of q p b 1 0 ores) buf). Intros. simpl in *.
  entailer!.
  apply andp_right.
  - unfold DD3x, DD3_of, dd_x, ddx_of. simpl. entailer!.
  - apply (ddict_rep_at_valid DENT gv (ddx_of q p b 1 0 ores) buf).
Qed.

Lemma body_createDDict_byReference_r : FS3_body (fun DENT TABS SR BR => ZSTD_createDDict_byReference_spec (DD3x DENT)).
Proof.
  intros DENT TABS SR BR HD HT. apply (ddict3_lift (G_createDDict_byReference_r DENT)); [unfold G_createDDict_byReference_r; ddict3_in | apply body_createDDict_byReference_small_r].
Qed.

End CM_DDictCreateRef3r_1.
