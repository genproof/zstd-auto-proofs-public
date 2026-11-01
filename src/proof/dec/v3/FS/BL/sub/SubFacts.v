(* FS3-bl SUB: pure facts relating the API's buffer-less frame (Spec_api6.blabs, with the buffer size) and the
   body's view (BLDefs.blabs), the model step without the cap and Params.bl_step (equal since API v3.1). *)
Require Export Zstd.proof.dec.v3.FS.BL.BLDefs.
Local Open Scope logic.

Section CM_SubFacts_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* the API's frame from the body's view and the buffer size *)
Definition bl_glob (ba: blabs) (osz: Z) : Spec_api6.blabs :=
  {| Spec_api6.ba_dict := ba_dict ba; Spec_api6.ba_st := ba_st ba; Spec_api6.ba_expect := ba_expect ba;
     Spec_api6.ba_out := match ba_out ba with Some (ob, f0, pe) => Some (ob, osz, f0, pe) | None => None end |}.

Lemma bl_loc_glob (ba: blabs) (osz: Z) : bl_loc (bl_glob ba osz) = ba.
Proof. destruct ba as [? ? ? [[[? ?] ?]|]]; reflexivity. Qed.

Lemma bl_hist_loc (ba: Spec_api6.blabs) ob osz opos oc :
  Spec_api6.bl_hist_ok ba ob osz opos oc ->
  bl_hist_ok (bl_loc ba) ob opos oc /\ (forall o, bl_osz ba = Some o -> o = osz).
Proof.
  unfold Spec_api6.bl_hist_ok, bl_hist_ok, bl_loc, bl_osz. simpl.
  destruct (Spec_api6.ba_out ba) as [[[[ob' o] f] pe]|]; simpl.
  - intros (E1 & E2 & E3 & E4 & E5). split; [auto | intros o' Ho; inversion Ho; subst; auto].
  - intros H. split; [exact H | intros o Ho; discriminate].
Qed.

Lemma bl_start_loc (ba: Spec_api6.blabs) opos : bl_start (bl_loc ba) opos = Spec_api6.bl_start ba opos.
Proof. unfold bl_start, Spec_api6.bl_start, bl_loc; simpl. destruct (Spec_api6.ba_out ba) as [[[[? ?] ?] ?]|]; reflexivity. Qed.

Lemma bl_hist_glob (ba: blabs) ob osz opos oc :
  bl_hist_ok ba ob opos oc -> Spec_api6.bl_hist_ok (bl_glob ba osz) ob osz opos oc.
Proof.
  unfold Spec_api6.bl_hist_ok, bl_hist_ok, bl_glob. simpl.
  destruct (ba_out ba) as [[[ob' f] pe]|]; simpl; [| auto].
  intros (E1 & E2 & E3 & E4). auto.
Qed.

Lemma bl_out_glob (ba: blabs) ob osz s e :
  ba_out ba = Some (ob, s, e) -> Spec_api6.ba_out (bl_glob ba osz) = Some (ob, osz, s, e).
Proof. intros E. unfold bl_glob; simpl. rewrite E. reflexivity. Qed.

Lemma bl_osz_glob (ba: blabs) osz o : bl_osz (bl_glob ba osz) = Some o -> o = osz.
Proof. unfold bl_osz, bl_glob; simpl. destruct (ba_out ba) as [[[? ?] ?]|]; intros H; inversion H; auto. Qed.

Lemma bl_step_nc_eq md dm b c : bl_step_nc md dm b c = bl_step md dm b c.
Proof.
  unfold bl_step_nc. destruct (bs_stage b) eqn:E; try reflexivity.
  unfold bl_step. rewrite E.
  destruct (get_frame_header_m (md_magicless md) (bs_hbuf b ++ c)) as [h| |]; try reflexivity.
  destruct h; reflexivity.
Qed.

Lemma bl_claim_glob md (ba: Spec_api6.blabs) (ba': blabs) c r opos osz oc' :
  bl_claim_nc md (bl_loc ba) ba' c r opos osz oc' -> bl_claim md ba (bl_glob ba' osz) c r opos osz oc'.
Proof.
  unfold bl_claim_nc, bl_claim, bl_loc, bl_glob; simpl.
  destruct (Spec_api6.ba_st ba) as [b|]; [| auto].
  destruct (dictref_model (Spec_api6.ba_dict ba)) as [dm|]; [| auto].
  intros H Hc. specialize (H Hc). rewrite bl_step_nc_eq in H. exact H.
Qed.

End CM_SubFacts_1.
