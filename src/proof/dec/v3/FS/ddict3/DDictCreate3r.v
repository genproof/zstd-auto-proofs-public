(* FS3 ddict3: ZSTD_createDDict (port of v2 body_FS_ddict.v; DD3_of pinned by dd_buf/dd_ld) *)
Require Import Zstd.proof.dec.v3.FS.FSOblig3.
Require Import Zstd.proof.dec.v3.FS.ddict3.DDictLayout3 Zstd.proof.dec.v3.FS.ddict3.DDictLift3.
Local Open Scope logic.

Section CM_DDictCreate3r_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Definition G_createDDict_r (DENT: dent_pred) : funspecs := [ZSTD_createDDict_advancedP_spec3 DENT].

(* the DDict ZSTD_createDDict describes (Spec_api6: no caller's pointer for NULL) is the one
   ZSTD_initDDict_internal made by copy in auto mode: for NULL (no bytes) the DDict without content *)
Lemma createDDict_dd_x (q p buf: val) (b: list Z) (ores: option (dstate * Z)) :
  (p = nullval -> b = nil) ->
  dd_x q {| dd_bytes := b; dd_ref := (if eq_dec p nullval then None else if Zlength b =? 0 then Some p else None);
            dd_buf := buf; dd_ld := ores |} = ddx_of q p b 0 0 ores.
Proof.
  intros Hn. unfold dd_x, ddx_of, dd_xref. cbn [dd_bytes dd_ref dd_ld]. f_equal.
  destruct (eq_dec p nullval) as [E|E].
  - rewrite (Hn E), E. reflexivity.
  - destruct (Zlength b =? 0) eqn:Z; [reflexivity |].
    destruct b; [discriminate | reflexivity].
Qed.

Lemma body_createDDict_small_r (DENT: dent_pred) : body_ok (G_createDDict_r DENT) (ZSTD_createDDict_spec (DD3x DENT)).
Proof.
  exists f_ZSTD_createDDict; split; [reflexivity | split; [reflexivity | ]].
  unfold G_createDDict_r.
  start_function.
  forward. forward. forward.
  forward_call (W, gv, sh, p, b, 0, 0, Tsh, v_allocator, @None cmem, 0).
  { unfold cm_have. cancel. }
  Intros q.
  forward.
  set (r := if eq_dec p nullval then None else if Zlength b =? 0 then Some p else None).
  destruct (eq_dec q nullval) as [Hq|Hq].
  { Exists q {| dd_bytes := b; dd_ref := r; dd_buf := nullval; dd_ld := None |}.
    destruct (eq_dec q nullval); [ | contradiction].
    unfold cm_have. entailer!. }
  Intros buf ores. Intros.
  rewrite ddx_of3_none.
  Exists q {| dd_bytes := b; dd_ref := r; dd_buf := buf; dd_ld := ores |}.
  destruct (eq_dec q nullval); [contradiction | ].
  unfold cm_have.
  sep_apply (ddict_rep_at_props DENT gv (ddx_of q p b 0 0 ores) buf). Intros. simpl in *.
  entailer!.
  apply andp_right.
  - unfold DD3x, DD3_of. subst r. rewrite createDDict_dd_x by assumption. simpl. entailer!.
  - apply (ddict_rep_at_valid DENT gv (ddx_of q p b 0 0 ores) buf).
Qed.

Lemma body_createDDict_r : FS3_body (fun DENT TABS SR BR => ZSTD_createDDict_spec (DD3x DENT)).
Proof.
  intros DENT TABS SR BR HD HT. apply (ddict3_lift (G_createDDict_r DENT)); [unfold G_createDDict_r; ddict3_in | apply body_createDDict_small_r].
Qed.

End CM_DDictCreate3r_1.
