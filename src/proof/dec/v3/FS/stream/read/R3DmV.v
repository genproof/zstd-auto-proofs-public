(* FS3 streaming, case zdss_load (a copy of load/L3DmV.v): the byte content of the context's dictionaries (dicts_bytes) from the
   dictionary memory a stream holds (dd_all: dgroup, dict_res, set_res; dict_rel3_of's dr_bytes = dd_bytes). *)
Require Import Zstd.proof.dec.v3.FS.stream.read.R3Borrow Zstd.proof.dec.v3.FS.stream.read.R3Dm.
Local Open Scope logic.

Section CM_R3DmV_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma prop_forall_derives : forall (P: mpred) (A: Type) (Q: A -> Prop),
  (forall a, P |-- !! Q a) -> P |-- !! (forall a, Q a).
Proof. intros P A Q H. rewrite prop_forall. apply allp_right. exact H. Qed.

Section DmV.
Variable DENT : dent_pred.

Lemma dd_all_caller_bytes : forall gv p st d W q dd, dd_caller st q dd -> stream_dict_ok W st -> set_cur_ok st ->
  dd_all DENT gv p st d |-- !! bytes_ok (dd_bytes dd).
Proof.
intros gv p st d W q dd Hc Hs Hcur.
eapply derives_trans; [apply (dd_borrow_caller DENT gv p st d W q dd Hc Hs Hcur)|].
apply andp_left1. apply prop_derives. intros Hf. unfold dd_facts in Hf. cbn [dx_bytes dd_x] in Hf. tauto.
Qed.

Lemma dd_all_local_bytes : forall gv p st d x buf,
  df_local d = dx_q x -> df_lx d = Some (x, buf) -> dx_q x <> nullval -> ddx_copied x = true ->
  dd_all DENT gv p st d |-- !! bytes_ok (dx_bytes x).
Proof.
intros gv p st d x buf Hl Hx Hn Hc.
eapply derives_trans; [apply (dd_borrow_local DENT gv p st d nil x buf Hl Hx Hn Hc)|].
apply andp_left1. apply prop_derives. intros Hf. unfold dd_facts in Hf. tauto.
Qed.

Lemma dd_all_bytes : forall gv p st d W, dict_rel3 st d -> set_cur_ok st -> stream_dict_ok W st ->
  dd_all DENT gv p st d |-- !! dicts_bytes st.
Proof.
intros gv p st d W Hr Hcur Hsd. unfold dicts_bytes. rewrite prop_and. apply andp_right.
- apply prop_forall_derives. intros Hn.
  apply prop_forall_derives. intros dr.
  apply prop_forall_derives. intros Hd.
  destruct Hr as [Hr|(Hne&_)]; [|contradiction].
  unfold dict_rel3_of in Hr. rewrite Hd in Hr.
  destruct (dr_src dr) as [pk| |q dd] eqn:Hs.
  + exfalso. unfold stream_dict_ok in Hsd. rewrite Hd, Hs in Hsd. tauto.
  + destruct Hr as (_ & Hr). destruct (Zlength (dr_bytes dr) =? 0) eqn:Hz.
    * apply prop_right. apply Z.eqb_eq in Hz. apply Zlength_nil_inv in Hz. rewrite Hz. constructor.
    * destruct Hr as (buf & ld & am & Hp & _ & _ & Hlx).
      apply (dd_all_local_bytes gv p st d {| dx_q := df_local d; dx_bytes := dr_bytes dr; dx_ref := None;
                                           dx_raw := dr_raw dr; dx_ld := ld; dx_mem := am |} buf); [reflexivity|exact Hlx| |reflexivity].
      cbn [dx_q]. intros E. rewrite E in Hp. exact Hp.
  + destruct Hr as (_&_&_&_&_&_&Hb). rewrite Hb. apply (dd_all_caller_bytes gv p st d W q dd); auto.
    right. exists dr. split; assumption.
- apply prop_forall_derives. intros q. apply prop_forall_derives. intros dd.
  apply prop_forall_derives. intros Hin.
  apply (dd_all_caller_bytes gv p st d W q dd); auto. left; exact Hin.
Qed.

(* the same, keeping the resources (for sep_apply in a VST proof) *)
Lemma dd_all_bytes_keep : forall gv p st d W, dict_rel3 st d -> set_cur_ok st -> stream_dict_ok W st ->
  dgroup DENT gv p d * dict_res (DD3x DENT) gv Ews (dc_dict st) * set_res (DD3x DENT) gv Ews (dc_set st) (dc_dict st)
  |-- !! dicts_bytes st &&
      (dgroup DENT gv p d * dict_res (DD3x DENT) gv Ews (dc_dict st) * set_res (DD3x DENT) gv Ews (dc_set st) (dc_dict st)).
Proof.
intros. apply andp_right; [apply (dd_all_bytes gv p st d W); auto|apply derives_refl].
Qed.

End DmV.

End CM_R3DmV_1.
