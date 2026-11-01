(* FS3 ddict3: ZSTD_freeDDict (port of v2 body_FS_ddict.v) *)
Require Import Zstd.proof.dec.v3.FS.FSOblig3.
Require Import Zstd.proof.dec.v3.FS.ddict3.DDictLayout3 Zstd.proof.dec.v3.FS.ddict3.DDictLift3.
Local Open Scope logic.

Section CM_DDictFree3_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Definition G_freeDDict (DENT: dent_pred) : funspecs := [ZSTD_customMem_copy_cm_spec; ZSTD_customFreeP_cm_spec].

Lemma body_freeDDict_small (DENT: dent_pred) : body_ok (G_freeDDict DENT) (ZSTD_freeDDict_int_spec).
Proof.
  exists f_ZSTD_freeDDict; split; [reflexivity | split; [reflexivity | ]].
  unfold G_freeDDict.
  start_function.
  rename H0 into Hroom.
  destruct (eq_dec q nullval) as [Hq | Hq].
  { subst q. forward_if; [forward; entailer! | contradiction]. }
  forward_if.
  { entailer!. apply denote_tc_test_eq_split; [ | auto with valid_pointer].
    sep_apply (ddict_any3_valid am q nb). entailer!. }
  { contradiction. }
  unfold ddict_any3, ddict_failed3. Intros n db.
  match goal with Hn: nb = _, Hp: db <> nullval -> _ |- _ => rename Hn into Hnb; rename Hp into Hpos end.
  assert (Hsz: db <> nullval -> am <> None -> sizeof (tarray tuchar n) = n /\ 0 < n).
  { intros Hdb Ham. specialize (Hpos Hdb Ham). simpl. rewrite Z.max_r by lia. lia. }
  assert (Hroom': am <> None -> 0 <= nb /\ sizeof t_ddict + nb <= h) by (apply Hroom; exact Hq).
  change (sizeof t_ddict) with 27352 in Hroom'.
  assert_PROP (field_compatible (Tstruct _ZSTD_DDict_s noattr) (DOT _cMem) q) by entailer!.
  rewrite (field_at_data_at Ews (Tstruct _ZSTD_DDict_s noattr) (DOT _cMem)).
  forward_call (Tsh, v_cMem, Ews, field_address (Tstruct _ZSTD_DDict_s noattr) (DOT _cMem) q, am).
  sep_apply (failed_buf_ptr3 am n db). Intros.
  forward.
  forward_call (gv, tarray tuchar n, db, Tsh, v_cMem, am, h).
  { split.
    - intros Hdb. destruct am as [m|]; [ | exact I]. destruct (Hsz Hdb ltac:(discriminate)) as [Es ?].
      unfold cm_held. rewrite Es.
      rewrite if_false in Hnb by exact Hdb. destruct Hroom' as [? ?]; [discriminate | ]. lia.
    - intros Hdb Ham. destruct (Hsz Hdb Ham) as [Es ?]. rewrite Es. lia. }
  sep_apply (field_at_field_at_ Ews (Tstruct _ZSTD_DDict_s noattr) (DOT _dictBuffer) db q).
  sep_apply (data_at_data_at_ Ews t_cmem (cmem_v am)
               (field_address (Tstruct _ZSTD_DDict_s noattr) (DOT _cMem) q)).
  sep_apply (ddict_merge3 q).
  (* the allocator's count after the first free: h - nb (with the default allocator the count is not used) *)
  assert (Hh: am <> None -> (if eq_dec db nullval then h else h - sizeof (tarray tuchar n)) = h - nb).
  { intros Ham. destruct (eq_dec db nullval) as [E|E]; [lia | ]. destruct (Hsz E Ham) as [Es ?]. rewrite Es. lia. }
  forward_call (gv, Tstruct _ZSTD_DDict_s noattr, q, Tsh, v_cMem, am,
                (if eq_dec db nullval then h else h - sizeof (tarray tuchar n))).
  { rewrite if_false by auto. cancel. }
  { destruct am as [m|]; [ | exact I]. unfold cm_held. rewrite Hh by discriminate.
    destruct Hroom' as [? ?]; [discriminate | ]. change (sizeof (Tstruct _ZSTD_DDict_s noattr)) with 27352. lia. }
  forward.
  rewrite if_false by auto.
  sep_apply (data_at_data_at_ Tsh t_cmem3 (cmem_v am) v_cMem).
  destruct am as [m|]; [ | unfold cm_have; cancel].
  rewrite Hh by discriminate.
  match goal with |- context [cm_have _ (h - ?x - sizeof (Tstruct _ZSTD_DDict_s noattr))] =>
    replace (h - x - sizeof (Tstruct _ZSTD_DDict_s noattr)) with (h - (sizeof t_ddict + x))
      by (change (sizeof t_ddict) with (sizeof (Tstruct _ZSTD_DDict_s noattr)); lia) end.
  cancel.
Qed.

Lemma body_freeDDict : FS3_body (fun DENT TABS SR BR => ZSTD_freeDDict_int_spec).
Proof.
  intros DENT TABS SR BR HD HT. apply (ddict3_lift (G_freeDDict DENT)); [unfold G_freeDDict; ddict3_in | apply body_freeDDict_small].
Qed.

End CM_DDictFree3_1.
