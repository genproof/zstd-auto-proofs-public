(* FS3 ddict3: ZSTD_getDictID_fromDDict, internal spec on ddid (port of v2 body_FS_ddict.v) *)
Require Import Zstd.proof.dec.v3.FS.FSOblig3.
Require Import Zstd.proof.dec.v3.FS.ddict3.DDictLayout3 Zstd.proof.dec.v3.FS.ddict3.DDictLift3.
Local Open Scope logic.

Section CM_DDictID3r_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Definition G_getDictID_fromDDict_r : funspecs := @nil (ident * funspec).

Lemma body_getDictID_fromDDict_int_small : body_ok G_getDictID_fromDDict_r ZSTD_getDictID_fromDDict_int_spec.
Proof.
  exists f_ZSTD_getDictID_fromDDict; split; [reflexivity | split; [reflexivity | ]].
  unfold G_getDictID_fromDDict_r.
  start_function.
  destruct (eq_dec q nullval) as [Hq|Hq].
  { forward_if.
    { forward. }
    { exfalso. apply H. exact Hq. } }
  unfold ddid. Intros.
  forward_if.
  { entailer!. apply denote_tc_test_eq_split; [ | auto with valid_pointer].
    sep_apply (field_at_valid_ptr0 Ews (Tstruct _ZSTD_DDict_s noattr) (DOT _dictBuffer)); auto.
    entailer!. }
  { exfalso. apply Hq. exact H0. }
  forward. forward.
  unfold ddid. entailer!.
Qed.

Lemma body_getDictID_fromDDict_int : FS3_body (fun DENT TABS SR BR => ZSTD_getDictID_fromDDict_int_spec).
Proof.
  intros DENT TABS SR BR HD HT. apply (ddict3_lift G_getDictID_fromDDict_r); [unfold G_getDictID_fromDDict_r; ddict3_in | apply body_getDictID_fromDDict_int_small].
Qed.

End CM_DDictID3r_1.
