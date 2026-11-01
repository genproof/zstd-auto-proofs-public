(* FS3 load3: the internal specifications of ZSTD_DCtx_loadDictionary_advanced / ZSTD_DCtx_refPrefix_advanced imply
   the API ones *)
Require Import Zstd.proof.dec.v3.FS.FSOblig3.
Require Import Zstd.proof.dec.v3.FS.load3.Load3Post.
Local Open Scope logic.

Section CM_Load3Sub_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* the API's dictionary after ZSTD_DCtx_loadDictionary_advanced(m, t) and ZSTD_DCtx_refPrefix_advanced(t) *)
Definition dr_adv (pk: val) (b: list Z) (m t: Z) : dictref :=
  {| dr_src := if m =? 1 then DSRef pk else DSOwn; dr_raw := t =? 1; dr_once := false; dr_bytes := b |}.
Definition dr_pre (pk: val) (b: list Z) (t: Z) : dictref :=
  {| dr_src := DSRef pk; dr_raw := t =? 1; dr_once := true; dr_bytes := b |}.

Definition fmt_ok (t: Z) (b: list Z) : Prop := t = 2 -> b <> nil -> dict_formatted b = true.

Lemma Zlength_nil_iff {A} (b: list A) : Zlength b = 0 -> b = nil.
Proof. intros H. destruct b; auto. rewrite Zlength_cons in H. pose proof (Zlength_nonneg b). lia. Qed.

Lemma load_res3_adv pk b m t r d' :
  (m = 0 \/ m = 1) -> load_res3 None pk b m t r d' ->
  (r = 0 /\ dict_rel3_of (Some (dr_adv pk b m t)) d' /\ fmt_ok t b) \/
  (r = err_code ZSTD_error_memory_allocation /\ d' = df_none).
Proof.
  intros Hm HL. unfold load_res3 in HL. unfold dict_rel3_of, dr_adv, fmt_ok; simpl.
  destruct (Zlength b =? 0) eqn:E.
  - destruct HL as [-> ->]. left. split; [reflexivity |].
    apply Z.eqb_eq in E. split; [| intros _ Hn; exfalso; apply Hn; apply Zlength_nil_iff; auto].
    destruct Hm as [-> | ->]; simpl; rewrite ?E; simpl; auto.
  - destruct HL as [[-> [Hf [q [buf [ores [Hq [Hbuf ->]]]]]]] | [-> ->]]; [left | right; auto].
    split; [reflexivity |]. split; [| intros Ht _; auto].
    destruct Hm as [-> | ->]; simpl.
    + rewrite ?E. split; auto. exists buf, ores, None. split; auto. split; auto. split; auto.
      unfold ddx_of3. simpl. rewrite ?E. reflexivity.
    + rewrite ?E. rewrite <- Hbuf by auto. split; auto. split; auto. split; auto.
      exists ores, None. unfold ddx_of3. simpl. reflexivity.
Qed.

Lemma load_res3_pre pk b t r d' :
  (exists d0, load_res3 None pk b 1 t r d0 /\ d' = (if r =? 0 then df_set_uses d0 1 else d0)) ->
  (r = 0 /\ dict_rel3_of (Some (dr_pre pk b t)) d' /\ fmt_ok t b) \/
  (r = err_code ZSTD_error_memory_allocation /\ d' = df_none).
Proof.
  intros [d0 [HL ->]]. unfold load_res3 in HL. unfold dict_rel3_of, dr_pre, fmt_ok; simpl.
  destruct (Zlength b =? 0) eqn:E.
  - destruct HL as [-> ->]. left. split; [reflexivity |].
    apply Z.eqb_eq in E. split; [| intros _ Hn; exfalso; apply Hn; apply Zlength_nil_iff; auto].
    rewrite ?E; simpl; auto.
  - destruct HL as [[-> [Hf [q [buf [ores [Hq [Hbuf ->]]]]]]] | [-> ->]]; [left | right; auto].
    split; [reflexivity |]. split; [| intros Ht _; auto].
    simpl. rewrite <- Hbuf by auto. split; auto. split; auto. split; auto.
    exists ores, None. unfold ddx_of3. simpl. reflexivity.
Qed.

Lemma load_result_adv_of st r t dr :
  (r = 0 /\ fmt_ok t (dr_bytes dr)) \/ r = err_code ZSTD_error_memory_allocation ->
  load_result_adv st (if r =? 0 then set_dict st (Some dr) else set_dict st None) r t dr.
Proof.
  intros [[-> Hf] | ->].
  - left. split; [reflexivity |]. split; [reflexivity | exact Hf].
  - right. split; [reflexivity |]. split; [reflexivity |]. right; right; reflexivity.
Qed.

Lemma refPrefix_advanced_sub3 :
  FS3_sub (fun DENT TABS SR BR => ZSTD_DCtx_refPrefix_advanced_spec3 DENT TABS)
          (fun DENT TABS SR BR => ZSTD_DCtx_refPrefix_advanced_aspec (DC3x DENT TABS SR BR)).
Proof.
  intros DENT TABS SR BR HD HT.
  apply NDsubsume_subsume; [split; reflexivity|].
  split; [split; reflexivity|].
  intros [[[[[[[W gv] d] st] sh] p] b] t] [g args]. simpl.
  unfold PROPx, LOCALx, SEPx, PARAMSx, GLOBALSx; simpl. normalize.
  unfold DC3x, DC3_of.
  unfold LOCALx at 1, argsassert2assert at 1; simpl.
  Intros k.
  match goal with Hx: base_rel3 st k |- _ => rename Hx into Hb end.
  match goal with Hx: dc_ss st = ss_init |- _ => rename Hx into Hss end.
  match goal with Hx: forall ba, dc_bl st = Some ba -> _ |- _ => rename Hx into Hbr end.
  match goal with Hx: ex_on3 SR st k |- _ => rename Hx into Hex end.
  match goal with Hx: dc_bl st = None |- _ => rename Hx into Hbl end.
  assert (Hstage: sf_stage (c3_s k) = 0)
    by (destruct Hb as (_ & _ & _ & _ & _ & _ & [_ Hs] & _); exact (proj1 (Hs Hss))).
  assert (Hsm: sf_mem (c3_s k) = None) by (destruct (base_rel3_mem _ _ Hb) as [E _]; rewrite E; assumption).
  assert (Hlm: local_mem (sf_mem (c3_s k)) (c3_dict k)) by (destruct (base_rel3_mem _ _ Hb) as [_ [_ E]]; exact E).
  Exists (W, gv, d, k, sh, p, b, t) (emp: mpred).
  simpl. rewrite emp_sepcon.
  apply andp_right.
  { unfold LOCALx, argsassert2assert; simpl. unfold local, lift1; simpl. entailer!. }
  apply prop_right. intros rho'. rewrite emp_sepcon.
  Intros r d'.
  match goal with Hx: exists d0, load_res3 _ _ _ _ _ _ _ /\ _ |- _ =>
    pose proof (load_res3_pre _ _ _ _ _ Hx) as Hr;
    assert (Hlm': local_mem None d')
      by (destruct Hx as [d0 [Hd0 ->]]; pose proof (load_res3_local _ _ _ _ _ _ _ Hd0) as Hl0;
          destruct (r =? 0); exact Hl0) end.
  assert (Hr': (r = 0 /\ dict_rel3_of (Some (dr_pre p b t)) d') \/ (r = err_code ZSTD_error_memory_allocation /\ d' = df_none))
    by (destruct Hr as [[? [? _]] | ?]; auto).
  assert (Hr01: (r = 0 /\ fmt_ok t b) \/ r = err_code ZSTD_error_memory_allocation) by (destruct Hr as [[? [_ ?]] | [? _]]; auto).
  destruct (load3_rel_r SR gv BR st k r d' (dr_pre p b t) Hb ltac:(assumption) Hss Hbl I Hlm' Hr' Hex) as [Hrange Hrel].
  pose proof (load_result_adv_of st r t (dr_pre p b t) Hr01) as Hres.
  Exists r (if r =? 0 then set_dict st (Some (dr_pre p b t)) else set_dict st None).
  unfold local, lift1; simpl. normalize.
  Exists (c3_with_dict k d').
  entailer!.
Qed.

Lemma loadDictionary_advanced_sub3 :
  FS3_sub (fun DENT TABS SR BR => ZSTD_DCtx_loadDictionary_advanced_spec3 DENT TABS)
          (fun DENT TABS SR BR => ZSTD_DCtx_loadDictionary_advanced_aspec (DC3x DENT TABS SR BR)).
Proof.
  intros DENT TABS SR BR HD HT.
  apply NDsubsume_subsume; [split; reflexivity|].
  split; [split; reflexivity|].
  intros [[[[[[[[W gv] d] st] sh] p] b] m] t] [g args]. simpl.
  unfold PROPx, LOCALx, SEPx, PARAMSx, GLOBALSx; simpl. normalize.
  unfold DC3x, DC3_of.
  unfold LOCALx at 1, argsassert2assert at 1; simpl.
  Intros k.
  match goal with Hx: base_rel3 st k |- _ => rename Hx into Hb end.
  match goal with Hx: dc_ss st = ss_init |- _ => rename Hx into Hss end.
  match goal with Hx: forall ba, dc_bl st = Some ba -> _ |- _ => rename Hx into Hbr end.
  match goal with Hx: ex_on3 SR st k |- _ => rename Hx into Hex end.
  match goal with Hx: dc_bl st = None |- _ => rename Hx into Hbl end.
  assert (Hstage: sf_stage (c3_s k) = 0)
    by (destruct Hb as (_ & _ & _ & _ & _ & _ & [_ Hs] & _); exact (proj1 (Hs Hss))).
  assert (Hsm: sf_mem (c3_s k) = None) by (destruct (base_rel3_mem _ _ Hb) as [E _]; rewrite E; assumption).
  assert (Hlm: local_mem (sf_mem (c3_s k)) (c3_dict k)) by (destruct (base_rel3_mem _ _ Hb) as [_ [_ E]]; exact E).
  match goal with Hx: m = 0 \/ m = 1 |- _ => rename Hx into Hm end.
  assert (Hroom: sf_stage (c3_s k) = 0 -> cm_room (sf_mem (c3_s k)) (sf_given (c3_s k)) (sizeof t_ddict + Zlength b))
    by (intros _; rewrite Hsm; exact I).
  Exists (W, gv, d, k, sh, p, b, m, t) (emp: mpred).
  simpl. rewrite emp_sepcon.
  apply andp_right.
  { unfold LOCALx, argsassert2assert; simpl. unfold local, lift1; simpl. entailer!. }
  apply prop_right. intros rho'. rewrite emp_sepcon.
  Intros r k'.
  rewrite Hsm in Hlm.
  match goal with Hx: load_int_res _ _ _ _ _ _ _ |- _ =>
    destruct (load_int_res_none _ _ _ _ _ _ _ Hstage Hsm Hlm Hx) as [d' [Hd' ->]] end.
  pose proof (load_res3_adv _ _ _ _ _ _ Hm Hd') as Hr.
  pose proof (load_res3_local _ _ _ _ _ _ _ Hd') as Hlm'.
  assert (Hr': (r = 0 /\ dict_rel3_of (Some (dr_adv p b m t)) d') \/ (r = err_code ZSTD_error_memory_allocation /\ d' = df_none))
    by (destruct Hr as [[? [? _]] | ?]; auto).
  assert (Hr01: (r = 0 /\ fmt_ok t b) \/ r = err_code ZSTD_error_memory_allocation) by (destruct Hr as [[? [_ ?]] | [? _]]; auto).
  assert (Hnd: not_ddict (dr_adv p b m t)) by (unfold not_ddict, dr_adv; simpl; destruct (m =? 1); exact I).
  destruct (load3_rel_r SR gv BR st k r d' (dr_adv p b m t) Hb ltac:(assumption) Hss Hbl Hnd Hlm' Hr' Hex) as [Hrange Hrel].
  pose proof (load_result_adv_of st r t (dr_adv p b m t) Hr01) as Hres.
  Exists r (if r =? 0 then set_dict st (Some (dr_adv p b m t)) else set_dict st None).
  unfold local, lift1; simpl. normalize.
  Exists (c3_with_dict k d').
  entailer!.
Qed.

End CM_Load3Sub_1.
