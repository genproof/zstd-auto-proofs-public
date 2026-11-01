(* FS3 ddict3: ZSTD_getDictID_fromDDict's internal spec (on ddid) implies the API one (on DD3_of):
   DD3_of splits into the dictBuffer/dictID fields (ddid, id = dict_id_of b < 2^32 since bytes_ok) and the rest *)
Require Import Zstd.proof.dec.v3.FS.FSOblig3.
Require Import Zstd.proof.dec.v3.FS.ddict3.DDictLayout3.
Local Open Scope logic.

Section CM_DDictIDSub3r_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma le_value_range_r: forall l, bytes_ok l -> 0 <= le_value l < 256 ^ Zlength l.
Proof.
  induction l as [| b l IH]; intros Hb; simpl; [lia |].
  inversion Hb as [| ? ? Hb1 Hb2]; subst. specialize (IH Hb2). unfold is_byte in Hb1.
  rewrite Zlength_cons, Z.pow_succ_r by (apply Zlength_nonneg). nia.
Qed.

Lemma le_field_4_range_r: forall l i, bytes_ok l -> 0 <= le_field l i 4 <= Int.max_unsigned.
Proof.
  intros. unfold le_field, slice.
  assert (Hok: bytes_ok (firstn (Z.to_nat 4) (skipn (Z.to_nat i) l))).
  { unfold bytes_ok in *. apply Forall_firstn, Forall_skipn. auto. }
  pose proof (le_value_range_r _ Hok).
  assert (Zlength (firstn (Z.to_nat 4) (skipn (Z.to_nat i) l)) <= 4).
  { rewrite Zlength_correct, firstn_length. lia. }
  assert (256 ^ Zlength (firstn (Z.to_nat 4) (skipn (Z.to_nat i) l)) <= 256 ^ 4)
    by (apply Z.pow_le_mono_r; [lia | auto]).
  rep_lia.
Qed.

Lemma dict_id_of_range_r: forall b, bytes_ok b -> 0 <= dict_id_of b <= Int.max_unsigned.
Proof.
  intros. unfold dict_id_of. destruct (Zlength b <? 8); [rep_lia |].
  destruct (negb _); [rep_lia | apply le_field_4_range_r; auto].
Qed.

(* DD3_of without the dictBuffer and dictID fields *)
Definition dd3_rest (DENT: dent_pred) (gv: globals) (q: val) (dd: ddict_st) : mpred :=
  let x := dd_x q dd in let buf := dd_buf dd in let b := dd_bytes dd in
  let t := Tstruct _ZSTD_DDict_s noattr in
  !! (isptr q /\ Zlength b <= 2 ^ 63 - 1 /\ bytes_ok b /\
      ld_rel b (dx_ld x) /\ (dx_raw x = true \/ dict_auto_c b (dx_ld x) <> None) /\
      (isptr buf \/ (buf = nullval /\ dx_ref x = Some nullval /\ b = nil)) /\ (ddx_copied x = true -> 0 < Zlength b) /\
      (match dx_ref x with Some p => buf = p | None => True end)) &&
  (field_at Ews t (DOT _dictContent) buf q *
   field_at Ews t (DOT _dictSize) (Vlong (Int64.repr (Zlength b))) q *
   field_at Ews t (DOT _entropyPresent)
     (Vint (Int.repr (match ddx_ent x with Some _ => 1 | None => 0 end))) q *
   field_at Ews t (DOT _cMem) cmem_null q *
   DENT gv q (ddx_ent x) * ddict_mem x buf * ddict_pad q).

Lemma ddb_copied (q: val) (dd: ddict_st) : ddb dd = (if ddx_copied (dd_x q dd) then dd_buf dd else nullval).
Proof. unfold ddb, ddx_copied, dd_x; simpl. destruct (dd_xref dd); reflexivity. Qed.

Lemma dd3_split (DENT: dent_pred) gv q dd :
  DD3_of DENT gv q dd |-- !! isptr q && (ddid q (dict_id_of (dd_bytes dd)) (ddb dd) * dd3_rest DENT gv q dd).
Proof.
  unfold DD3_of, ddict_rep_at, ddict_struct, ddid, dd3_rest. rewrite (ddb_copied q dd).
  simpl dx_q; simpl dx_bytes; simpl dx_raw. Intros.
  pose proof (dict_id_of_range_r _ H0).
  entailer!.
Qed.

Lemma dd3_merge (DENT: dent_pred) gv q dd :
  ddid q (dict_id_of (dd_bytes dd)) (ddb dd) * dd3_rest DENT gv q dd |-- DD3_of DENT gv q dd.
Proof.
  unfold DD3_of, ddict_rep_at, ddict_struct, ddid, dd3_rest. rewrite (ddb_copied q dd).
  simpl dx_q; simpl dx_bytes; simpl dx_raw. Intros.
  entailer!.
Qed.

Lemma getDictID_fromDDict_sub3 : FS3_sub (fun DENT TABS SR BR => ZSTD_getDictID_fromDDict_int_spec)
          (fun DENT TABS SR BR => ZSTD_getDictID_fromDDict_spec (DD3x DENT)).
Proof.
  intros DENT TABS SR BR HD HT.
  apply NDsubsume_subsume; [split; reflexivity|].
  split; [split; reflexivity|].
  intros [[gv q] dd] [g args]. simpl.
  unfold PROPx, LOCALx, SEPx, PARAMSx, GLOBALSx; simpl. normalize.
  unfold LOCALx at 1, argsassert2assert at 1; simpl.
  unfold local, lift1; simpl. Intros.
  unfold DD3x. sep_apply (dd3_split DENT gv q dd). Intros.
  Exists (q, dict_id_of (dd_bytes dd), ddb dd) (dd3_rest DENT gv q dd). simpl.
  rewrite if_false by (intro E; subst q; contradiction).
  apply andp_right.
  { unfold LOCALx, argsassert2assert; simpl. entailer!. }
  apply prop_right. intros rho'.
  rewrite if_false by (intro E; subst q; contradiction).
  unfold liftx, lift; simpl. normalize.
  sep_apply (dd3_merge DENT gv q dd).
  apply andp_right; [apply derives_refl | ].
  unfold DD3_of. apply (ddict_rep_at_valid DENT gv (dd_x q dd) (dd_buf dd)).
Qed.

End CM_DDictIDSub3r_1.
