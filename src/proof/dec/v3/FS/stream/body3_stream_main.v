(* FS3 streaming: the body of ZSTD_decompressStream from its pieces (template v2 body_stream_main.v). *)
Require Import Zstd.proof.dec.v3.FS.stream.S3Main Zstd.proof.dec.v3.FS.stream.main3.ds_loop3.
Require Import Zstd.proof.zstd.NullBufOk.
Local Open Scope logic.

Section CM_body3_stream_main_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* the stream's dictionary facts survive a witness more *)
Lemma sddict_ok_cons : forall w W dd, sddict_ok W dd -> sddict_ok (w :: W) dd.
Proof.
intros w W dd H. unfold sddict_ok in *. destruct (dd_ref dd); auto. destruct H as [A B]. split; [exact A |].
rewrite pws_pred_cons. apply sepcon_valid_pointer2. exact B.
Qed.

Lemma stream_dict_ok_cons : forall w W st, stream_dict_ok W st -> stream_dict_ok (w :: W) st.
Proof.
intros w W st (H1 & H2 & H3). split; [| split; [| exact H3]].
- destruct (dc_dict st) as [dr |]; auto. destruct H1 as [A B]. split; [exact A |].
  destruct (dr_src dr); auto. apply sddict_ok_cons; exact B.
- eapply Forall_impl; [| exact H2]. intros e He. apply sddict_ok_cons; exact He.
Qed.

(* The body (against its full specification, stream_exact included) works on the bases of the buffers (F9: ZSTD_emptyBuffer for an empty buffer passed as NULL), with a part of
   ZSTD_emptyBuffer lent by zstd_globals as the witness of that base (S3Main.dsa); the specification's mbuf at the
   caller's pointers is the array at the base, and back. *)
Lemma body3_stream_main_of_segs :
  seg_prologue_x -> (forall k, 0 <= k <= 4 -> seg_case_x k) -> seg_epilogue_x ->
  stream_body3 (fun DENT TABS BR => ZSTD_decompressStream_spec (DC3x DENT TABS SR3 BR) (DD3x DENT)).
Proof.
intros Hpro Hcase Hepi DENT TABS BR HD HT.
exists f_ZSTD_decompressStream; split; [reflexivity | split; [reflexivity | ]].
start_function.
unfold MORE_COMMANDS, abbreviate.
match goal with |- semax _ _ (Ssequence ?a ?b) _ =>
  change (Ssequence a b) with (ds_prologue (Ssequence ds_loop ds_epilogue)) end.
assert_PROP (ob = nullval -> osz = 0 /\ oc = []) as Hon.
{ sep_apply (mbuf_local_facts shob osz oc ob ltac:(lia)). entailer!. all: tauto. }
assert_PROP (ib = nullval -> isz = 0 /\ zbytes ibs = []) as Hin.
{ sep_apply (mbuf_local_facts shb isz (zbytes ibs) ib ltac:(lia)). entailer!. all: tauto. }
replace_SEP 3 (EX sh: share, !! readable_share sh && (zstd_globals gv * pw_pred (eb_wit gv sh)))
  by (entailer!; apply zstd_globals_lend).
Intros shw. Intros. match goal with Hr: readable_share shw |- _ => rename Hr into Hrw end.
sep_apply (mbuf_base gv shw shob osz oc ob).
sep_apply (mbuf_base gv shw shb isz (zbytes ibs) ib).
pose (A := {| a_W := eb_wit gv shw :: W; a_gv := gv; a_d := d; a_st := st; a_outp := outp; a_inp := inp; a_sho := sho;
              a_shi := shi; a_shob := shob; a_obf := ob; a_osz := osz; a_opos := opos; a_oc := oc;
              a_shb := shb; a_ibf := ib; a_isz := isz; a_ipos := ipos; a_ibs := ibs; a_vop := v_op |}).
assert_PROP (field_compatible (tarray tuchar osz) [] (nbase gv ob)) as Hfco by entailer!.
assert_PROP (cmem_ok (dc_mem st)) as Hmem.
{ unfold DC3x, DC3_of. Intros k. match goal with Hb: base_rel3 st k |- _ =>
    destruct (base_rel3_mem st k Hb) as (Em & _) end.
  rewrite <- Em. unfold ctx_rep3, ctx_body3, sgroup, mgroup. Intros. entailer!. }
assert (Hon0: ob = nullval -> osz = 0) by (intros E; apply (Hon E)).
assert (Hin0: ib = nullval -> isz = 0) by (intros E; apply (Hin E)).
assert (HA: dsa_ok A).
{ unfold dsa_ok; simpl. unfold a_ob, a_ib; simpl.
  match goal with Hb: buf_ok W shob _ ob |- _ => pose proof (buf_ok_base gv shw W shob osz ob Hrw Hon0 Hb) as Hbo end.
  match goal with Hb: buf_ok W shb _ ib |- _ => pose proof (buf_ok_base gv shw W shb isz ib Hrw Hin0 Hb) as Hbi end.
  match goal with Hd: stream_dict_ok W st |- _ => pose proof (stream_dict_ok_cons (eb_wit gv shw) W st Hd) as Hsd end.
  assert (F6: osz = 0 -> (pws_pred (eb_wit gv shw :: W) |-- weak_valid_pointer (nbase gv ob))).
  { intros E.
    assert (Hb0: buf_ok (eb_wit gv shw :: W) shob 0 (nbase gv ob)) by (rewrite <- E; exact Hbo).
    assert (Hp: isptr (nbase gv ob)) by (destruct Hfco as [Hp _]; exact Hp).
    eapply derives_trans; [| eapply derives_trans; [exact Hb0 | apply andp_left1, derives_refl]].
    rewrite (data_at__tuchar_zero_array_eq shob (nbase gv ob) Hp), sepcon_emp. apply derives_refl. }
  repeat match goal with Hx: dc_stable st = true -> _ /\ _ |- _ =>
    let H1 := fresh in let H2 := fresh in
    assert (H1: dc_stable st = true -> opos = Zlength (ss_out (dc_ss st))) by (intro E; apply (proj1 (Hx E)));
    assert (H2: dc_stable st = true -> sublist 0 opos oc = zbytes (ss_out (dc_ss st))) by (intro E; apply (proj2 (Hx E)));
    clear Hx end.
  tauto. }
apply (semax_post (ds_R_x DENT TABS BR A)).
- unfold ds_R_x; simpl; intros; apply andp_left2; normalize; apply FF_left.
- unfold ds_R_x; simpl; intros; apply andp_left2; normalize; apply FF_left.
- unfold ds_R_x; simpl; intros; apply andp_left2; normalize; apply FF_left.
- (* the return: give back the lent part of ZSTD_emptyBuffer, the arrays at the bases are mbuf *)
  intros vl rho. unfold ds_R_x, ds_post_x. simpl. apply andp_left2. apply sepcon_derives; [| apply derives_refl].
  destruct vl as [v |]; simpl bind_ret; [| apply derives_refl].
  apply andp_derives; [apply derives_refl |]. unfold liftx; simpl.
  unfold a_ob, a_ib. unfold A; cbn [a_W a_gv a_d a_st a_outp a_inp a_sho a_shi a_shob a_obf a_osz a_opos a_oc a_shb a_ibf a_isz a_ipos a_ibs a_vop].
  unfold lift; simpl. generalize (env_set (globals_only rho) ret_temp v); intro rho'.
  Intros r opos' ipos' oc' st'. Exists r opos' ipos' oc' st'.
  unfold PROPx, LOCALx, SEPx; simpl. rewrite pws_pred_cons. entailer!.
  apply andp_derives; [apply derives_refl |].
  sep_apply (base_mbuf gv shob (Zlength oc) oc' ob Hon0). sep_apply (base_mbuf gv shb (Zlength ibs) (zbytes ibs) ib Hin0).
  sep_apply (zstd_globals_return gv shw). cancel.
- eapply semax_pre; [| apply (ds_after_pro Espec DENT TABS BR A Hpro Hcase Hepi HD HT HA)].
  unfold a_ob, a_ib. unfold A; cbn [a_W a_gv a_d a_st a_outp a_inp a_sho a_shi a_shob a_obf a_osz a_opos a_oc a_shb a_ibf a_isz a_ipos a_ibs a_vop].
  rewrite pws_pred_cons. unfold eb_wit, pw_pred at 1. entailer!.
Qed.

End CM_body3_stream_main_1.
