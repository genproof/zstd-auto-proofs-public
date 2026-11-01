(* FS3 ddict3: ZSTD_createDDict_advancedP (port of v2 body_FS_ddict.v) *)
Require Import Zstd.proof.dec.v3.FS.FSOblig3.
Require Import Zstd.proof.dec.v3.FS.ddict3.DDictLayout3 Zstd.proof.dec.v3.FS.ddict3.DDictLift3.
Local Open Scope logic.

Section CM_DDictAdv3_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Definition G_createDDict_advancedP (DENT: dent_pred) : funspecs := [ZSTD_customMallocP_cm_spec; ZSTD_customMem_copy_cm_spec; ZSTD_initDDict_internal_spec3 DENT; ZSTD_isError_spec; ZSTD_freeDDict_int_spec].

Lemma body_createDDict_advancedP_small (DENT: dent_pred) : body_ok (G_createDDict_advancedP DENT) (ZSTD_createDDict_advancedP_spec3 DENT).
Proof.
  exists f_ZSTD_createDDict_advancedP; split; [reflexivity | split; [reflexivity | ]].
  unfold G_createDDict_advancedP.
  start_function.
  match goal with H: cmem_ok am |- _ => rename H into Hok end.
  match goal with H: cm_room am h _ |- _ => rename H into Hroom end.
  (* the test of customAlloc and customFree: both NULL (the default allocator) or both functions *)
  assert (Hcm: exists ca cf co: val, cmem_v am = (ca, (cf, co)) /\ is_pointer_or_null ca /\ is_pointer_or_null cf)
    by (destruct am as [m|]; [exists (cm_alloc m), (cm_free m), (cm_opaque m); split; [reflexivity | destruct Hok as (? & ? & ?); split; assumption]
                             | exists nullval, nullval, nullval; split; [reflexivity | split; simpl; auto]]).
  destruct Hcm as (ca & cf & co & Ecm & Hca & Hcf).
  rewrite Ecm.
  assert_PROP (am <> None -> isptr ca /\ isptr cf) as Hpt.
  { destruct am as [m|]; [| entailer!; congruence].
    unfold cmem_v, cmem_val in Ecm. inversion Ecm; subst.
    sep_apply (dd_cm_have_ptrs m h). entailer!. }
  forward. forward.
  forward_if.
  { destruct am as [m|].
    2: inversion Ecm; subst. 2: entailer!. 2: apply denote_tc_test_eq_split; apply valid_pointer_null.
    unfold cmem_v, cmem_val in Ecm. inversion Ecm; subst.
    apply andp_right; apply denote_tc_test_eq_split; try (apply valid_pointer_zero64; reflexivity);
      (apply (derives_trans _ (cm_have (Some m) h * TT)); [cancel | apply sepcon_valid_pointer1;
       eapply derives_trans; [apply (dd_cm_have_valid m h)
                             | first [apply andp_left1; apply derives_refl | apply andp_left2; apply derives_refl]]]). }
  { exfalso. destruct am as [m|]; [destruct (Hpt ltac:(discriminate)) as [Ha Hf]; destruct ca; try contradiction;
                           destruct cf; try contradiction | inversion Ecm; subst]; simpl in *;
      match goal with H: typed_true _ _ |- _ => inv H end. }
  rewrite <- Ecm.
  assert (Hb0: 0 <= Zlength b) by apply Zlength_nonneg.
  forward_call (gv, Tstruct _ZSTD_DDict_s noattr, shm, pm, am, h).
  { destruct am as [m|]; [ | exact I]. unfold cm_room in *.
    change (sizeof t_ddict) with 27352 in Hroom. simpl. lia. }
  Intros q.
  destruct (eq_dec q nullval) as [Hq|Hq].
  { subst q. forward_if; [ | contradiction]. forward. Exists nullval. entailer!. rewrite if_true by auto. cancel. }
  Intros.
  forward_if; [contradiction | ].
  assert_PROP (field_compatible (Tstruct _ZSTD_DDict_s noattr) [] q) as Hfc by entailer!.
  assert (field_compatible (Tstruct _ZSTD_DDict_s noattr) (DOT _cMem) q).
  { apply field_compatible_cons. simpl. split; [ | exact Hfc]. right; right; right; right; right; right; left; reflexivity. }
  sep_apply (ddict_split3 q).
  forward_call (Ews, field_address (Tstruct _ZSTD_DDict_s noattr) (DOT _cMem) q, shm, pm, am).
  { cancel. }
  sep_apply (ddict_fresh3_fold am q).
  forward_call (gv, q, W, sh, pk, b, method, ctype, am, h + sizeof (Tstruct _ZSTD_DDict_s noattr)).
  { destruct am as [m|]; [ | exact I]. unfold cm_room in *.
    change (sizeof t_ddict) with 27352 in Hroom. simpl. lia. }
  Intros vr. destruct vr as [r ores]. simpl fst in *; simpl snd in *.
  forward_call r.
  forward_if.
  - destruct (Z.eq_dec r 0) as [Hr|Hr].
    { subst r. exfalso. match goal with H: (if is_error_code 0 then 1 else 0) <> 0 |- _ => apply H; reflexivity end. }
    Intros nb.
    sep_apply (ddict_failed3_nb am q (Zlength b) nb). Intros.
    forward_call (gv, q, am, h + sizeof (Tstruct _ZSTD_DDict_s noattr) + nb, nb).
    { rewrite if_false by auto. unfold ddict_any3. Exists (Zlength b). cancel. }
    { destruct am as [m|]; [ | congruence].
      match goal with Hn: Some m <> None -> 0 <= nb |- _ => specialize (Hn ltac:(discriminate)) end.
      split; [lia | ]. unfold cm_room in Hroom.
      change (sizeof t_ddict) with 27352 in *. simpl. lia. }
    forward. Exists nullval. rewrite if_false by auto.
    replace (h + sizeof (Tstruct _ZSTD_DDict_s noattr) + nb - (sizeof t_ddict + nb)) with h by (simpl; lia).
    entailer!. rewrite if_true by auto. cancel.
  - destruct (Z.eq_dec r 0) as [Hr|Hr].
    2: { exfalso. match goal with H: (r = 0 /\ _) \/ _ |- _ => destruct H as [[? _] | [He _]]; [contradiction | ] end.
         match goal with H: Int.repr (if is_error_code r then 1 else 0) = Int.zero |- _ => rewrite He in H; discriminate end. }
    subst r. destruct (Z.eq_dec 0 0) as [_|?]; [|contradiction]. Intros buf.
    assert (Hfmt: ctype = 2 -> dict_formatted b = true).
    { match goal with H: (0 = 0 /\ _) \/ _ |- _ => destruct H as [[_ Hf] | [He _]]; [exact Hf | discriminate] end. }
    forward. Exists q. destruct (eq_dec q nullval); [contradiction|]. Exists buf ores.
    unfold ddict_rep_at, ddict_mem. entailer!.
    change (dx_q (ddx_of3 am q pk b method ctype ores)) with q.
    change (dx_mem (ddx_of3 am q pk b method ctype ores)) with am.
    change (dx_bytes (ddx_of3 am q pk b method ctype ores)) with b.
    destruct am as [m|]; [ | unfold cm_have; cancel].
    replace (h + sizeof (Tstruct _ZSTD_DDict_s noattr) +
             (if ddx_copied (ddx_of3 (Some m) q pk b method ctype ores) then Zlength b else 0))
      with (h + ddx_held (ddx_of3 (Some m) q pk b method ctype ores)) by (unfold ddx_held; simpl; lia).
    cancel.
Qed.

Lemma body_createDDict_advancedP : FS3_body (fun DENT TABS SR BR => ZSTD_createDDict_advancedP_spec3 DENT).
Proof.
  intros DENT TABS SR BR HD HT. apply (ddict3_lift (G_createDDict_advancedP DENT)); [unfold G_createDDict_advancedP; ddict3_in | apply body_createDDict_advancedP_small].
Qed.

End CM_DDictAdv3_1.
