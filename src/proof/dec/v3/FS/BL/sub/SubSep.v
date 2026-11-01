(* FS3-bl SUB: the dictionary's memory (Spec_api6.dict_res) split into the tables' DDict entropy and the
   dictionary bytes (BLDefs.bd_res); the context part in SubCtx.v. *)
Require Export Zstd.proof.dec.v3.FS.BL.sub.SubCtx2.
Local Open Scope logic.

Section CM_SubSep_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* ---------- the dictionary ---------- *)

(* the share of the dictionary's bytes as BLDefs.bd_res sees them: the caller's, or Ews for a DDict's copy *)
Definition bd_sh (shk: share) (odr: option dictref) : share :=
  match odr with
  | Some dr => match dr_src dr with DSDDict _ dd => match dd_ref dd with Some _ => shk | None => Ews end | _ => shk end
  | None => shk
  end.

Lemma bd_sh_readable shk odr : readable_share shk -> readable_share (bd_sh shk odr).
Proof.
  intros H. destruct odr as [dr|]; simpl; auto. destruct (dr_src dr); auto. destruct (dd_ref dd); auto;
  try (apply writable_readable_share, writable_Ews).
Qed.

(* the DDict's memory besides its entropy and its bytes *)
Definition dict_rest (odr: option dictref) : mpred :=
  match odr with
  | Some dr =>
      match dr_src dr with
      | DSDDict q dd =>
          ddict_struct (dd_x q dd) (dd_buf dd) * ddict_pad q * malloc_token Ews (Tstruct _ZSTD_DDict_s noattr) q *
          (if ddx_copied (dd_x q dd)
           then malloc_token Ews (tarray tuchar (Zlength (dd_bytes dd))) (dd_buf dd) else emp)
      | _ => emp
      end
  | None => emp
  end.

(* a DDict by reference: its content is the caller's pointer (NULL for the DDict without content) *)
Definition dict_ref_buf (odr: option dictref) : Prop :=
  match odr with
  | Some dr =>
      match dr_src dr with
      | DSDDict q dd => match dd_xref dd with Some p => dd_buf dd = p | None => True end
      | _ => True
      end
  | None => True
  end.

Lemma dict_rest_buf odr : dict_rest odr |-- !! dict_ref_buf odr.
Proof.
  destruct odr as [dr|]; simpl; [| entailer!]. destruct (dr_src dr) as [| |q dd]; [entailer! | entailer! |].
  unfold ddict_struct; simpl. entailer!.
Qed.

Lemma bd_buf_conv W shk odr od shd cap dst :
  bd_rel odr od -> dict_ref_buf odr -> dict_buf_ok W shk odr shd cap dst -> bd_buf_ok W (bd_sh shk odr) od shd cap dst.
Proof.
  destruct odr as [dr|], od as [d|]; simpl; try tauto.
  intros [Hb Hs] Hr Hok. destruct (dr_src dr) as [p| |q dd]; try contradiction.
  - destruct Hs as (_ & He & _). intros _ _. rewrite Hb, He. exact Hok.
  - destruct Hs as (He & Hbd & _ & Hg). rewrite Hb, Hbd, He.
    destruct (dd_xref_cases dd) as [(p & Er & Ex) | [(Er & _ & Ex) | (Er & _ & Ex)]];
      rewrite Er in Hok |- *; rewrite Ex in Hr, Hg.
    + intros _ _. rewrite Hr. exact Hok.
    + intros E; rewrite Hg in E; discriminate.
    + intros _ Hp. rewrite Hr in Hp. contradiction.
Qed.

(* the caller's bytes (by reference, or of a DDict by reference) are at a pointer: Spec_api6.dict_res holds them
   (the struct alone, ddict_struct, also admits the DDict without content at NULL) *)
Definition dict_ref_ptr (odr: option dictref) : Prop :=
  match odr with
  | Some dr =>
      match dr_src dr with
      | DSRef p => isptr p
      | DSDDict _ dd => forall p, dd_ref dd = Some p -> isptr p
      | DSOwn => True
      end
  | None => True
  end.

Section Dict.
Variable DENT : dent_pred.

Lemma dict_res_ref_ptr gv shk odr : dict_res (DD3x DENT) gv shk odr |-- !! dict_ref_ptr odr.
Proof.
  destruct odr as [dr|]; simpl; [| entailer!]. destruct (dr_src dr) as [| |q dd]; [entailer! | entailer! |].
  unfold ddict_res. destruct (dd_ref dd) as [p|].
  - assert_PROP (isptr p) as Hp by entailer!. apply prop_right. intros p0 E. inversion E; subst p0. exact Hp.
  - apply prop_right. intros p0 E. discriminate E.
Qed.

Lemma dict_split gv shk odr od :
  bd_rel odr od ->
  dict_res (DD3x DENT) gv shk odr |-- dent_of DENT gv (bd_oxo od) * bd_res (bd_sh shk odr) od * dict_rest odr.
Proof.
  intros Hrel. destruct odr as [dr|], od as [d|]; simpl in *; try contradiction.
  2: { simpl. cancel. }
  destruct Hrel as [Hb Hs]. unfold dict_res, bd_oxo, bd_res.
  destruct (dr_src dr) as [p| |q dd]; try contradiction.
  - destruct Hs as (_ & He & Hox). rewrite Hox, He, Hb. simpl.
    assert_PROP (isptr p) as Hp by entailer!. rewrite bytes_at_ptr by exact Hp. cancel.
  - destruct Hs as (He & Hbd & Hox & _). rewrite Hox, He, Hb, Hbd. unfold ddict_res, DD3x, DD3_of.
    eapply derives_trans; [apply sepcon_derives; [apply andp_left1; apply derives_refl | apply derives_refl] |].
    unfold ddict_rep_at, ddict_mem, ddx_copied; simpl.
    assert_PROP ((isptr (dd_buf dd) \/ (dd_buf dd = nullval /\ dd_xref dd = Some nullval /\ dd_bytes dd = nil)) /\
                 match dd_xref dd with Some p => dd_buf dd = p | None => True end) as Hr.
    { unfold ddict_struct; simpl. entailer!. }
    destruct Hr as [Hp Hr].
    destruct (dd_xref_cases dd) as [(p & Er & Ex) | [(Er & _ & Ex) | (Er & _ & Ex)]]; rewrite Er; rewrite Ex in Hr |- *.
    + subst p. assert_PROP (isptr (dd_buf dd)) as Hp' by entailer!. rewrite bytes_at_ptr by exact Hp'. cancel.
    + destruct Hp as [Hp | (_ & E & _)]; [| rewrite Ex in E; discriminate E].
      rewrite bytes_at_ptr by exact Hp. cancel.
    + rewrite Hr, bytes_at_null. cancel.
Qed.

Lemma dict_join gv shk odr od :
  bd_rel odr od -> dict_ref_ptr odr ->
  dent_of DENT gv (bd_oxo od) * bd_res (bd_sh shk odr) od * dict_rest odr |-- dict_res (DD3x DENT) gv shk odr.
Proof.
  intros Hrel Hptr. destruct odr as [dr|], od as [d|]; simpl in *; try contradiction.
  2: { simpl. cancel. }
  destruct Hrel as [Hb Hs]. unfold dict_res, bd_oxo, bd_res, dict_rest.
  destruct (dr_src dr) as [p| |q dd]; try contradiction.
  - destruct Hs as (_ & He & Hox). rewrite Hox, He, Hb. simpl. rewrite bytes_at_ptr by exact Hptr. cancel.
  - destruct Hs as (He & Hbd & Hox & _). rewrite Hox, He, Hb, Hbd. unfold ddict_res, DD3x, DD3_of.
    assert (Hv: ddict_struct (dd_x q dd) (dd_buf dd) |-- valid_pointer q).
    { unfold ddict_struct; simpl. Intros.
      sep_apply (field_at_valid_ptr0 Ews (Tstruct _ZSTD_DDict_s noattr) (DOT _dictBuffer)); auto.
      repeat apply sepcon_valid_pointer1; apply derives_refl. }
    assert_PROP ((isptr (dd_buf dd) \/ (dd_buf dd = nullval /\ dd_xref dd = Some nullval /\ dd_bytes dd = nil)) /\
                 match dd_xref dd with Some p => dd_buf dd = p | None => True end) as Hr.
    { unfold ddict_struct; simpl. entailer!. }
    destruct Hr as [Hp Hr].
    unfold ddict_rep_at, ddict_mem, ddx_copied; simpl.
    destruct (dd_xref_cases dd) as [(p & Er & Ex) | [(Er & _ & Ex) | (Er & _ & Ex)]]; rewrite Er; rewrite Ex in Hr |- *.
    + pose proof (Hptr p Er) as Hpp. subst p. rewrite bytes_at_ptr by exact Hpp.
      eapply derives_trans; [| apply sepcon_derives; [apply andp_right; [apply derives_refl |] | apply derives_refl]].
      * unfold dent_of. cancel.
      * do 3 apply sepcon_valid_pointer1. exact Hv.
    + destruct Hp as [Hp | (_ & E & _)]; [| rewrite Ex in E; discriminate E].
      rewrite bytes_at_ptr by exact Hp.
      eapply derives_trans; [| apply sepcon_derives; [apply andp_right; [apply derives_refl |] | apply derives_refl]].
      * unfold dent_of. cancel.
      * do 3 apply sepcon_valid_pointer1. exact Hv.
    + rewrite Hr, bytes_at_null. rewrite Hr in Hv.
      eapply derives_trans; [| apply sepcon_derives; [apply andp_right; [apply derives_refl |] | apply derives_refl]].
      * unfold dent_of. cancel.
      * do 3 apply sepcon_valid_pointer1. exact Hv.
Qed.

End Dict.

End CM_SubSep_1.
