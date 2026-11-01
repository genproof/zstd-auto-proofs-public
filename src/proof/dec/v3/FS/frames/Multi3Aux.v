(* FS3 one-shot frames, ZSTD_decompressMultiFrame: small facts on fix F4's probe and the frame
   header for the body. *)
Require Export Zstd.proof.dec.v3.FS.frames.Multi3Probe.
Require Import Zstd.proof.dec.v3.FS.frames.Frames3Model.
Local Open Scope logic.

Section CM_Multi3Aux_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma gfh_more_pos: forall mg s k, bytes_ok s -> get_frame_header_m mg s = FH_more k -> 0 < k.
Proof.
  intros mg s k Hb H. destruct mg; unfold get_frame_header_m in H; cbn [negb] in H.
  - destruct (Zlength s <? 1); [inversion H; lia|].
    destruct (get_frame_header (magic_bytes ++ s)) as [|k'|h] eqn:E; try discriminate. inversion H; subst.
    unfold get_frame_header in E.
    pose proof (f3m_bytes_ok s Hb) as Hb'.
    pose proof (fh_hs_range _ (fh_byte_at_bound _ 4 Hb')).
    repeat match type of E with context [if ?c then _ else _] => destruct c end; try discriminate;
      inversion E; subst; unfold ZSTD_SKIPPABLEHEADERSIZE in *; try lia.
    match goal with |- 0 < fhd_header_size ?b - 4 => change b with (byte_at (magic_bytes ++ s) 4); lia end.
  - unfold get_frame_header in H. pose proof (fh_hs_range _ (fh_byte_at_bound s 4 Hb)).
    repeat match type of H with context [if ?c then _ else _] => destruct c end; try discriminate;
      inversion H; subst; unfold ZSTD_SKIPPABLEHEADERSIZE in *; lia.
Qed.

(* ZSTD_getFrameHeader_advanced returned 0: a header *)
Lemma fh_post_zero: forall mg s r v0 v, bytes_ok s -> fh_post_m mg s r v0 v -> r = 0 ->
  exists h, get_frame_header_m mg s = FH_ok h /\ v = fh_val h.
Proof.
  intros mg s r v0 v Hb H Hr. unfold fh_post_m in H.
  destruct (get_frame_header_m mg s) as [|k|h] eqn:E.
  - destruct H as [[He _] _]. subst r. unfold is_error_code in He. discriminate.
  - destruct H as [-> _]. pose proof (gfh_more_pos _ _ _ Hb E). lia.
  - destruct H as [_ ->]. eauto.
Qed.

Lemma fh_post_nz: forall mg s r v0 v, fh_post_m mg s r v0 v -> r <> 0 ->
  forall h, get_frame_header_m mg s <> FH_ok h.
Proof.
  intros mg s r v0 v H Hr h E. unfold fh_post_m in H. rewrite E in H. destruct H; contradiction.
Qed.

Lemma veqb_true: forall a b, veqb a b = true -> a = b.
Proof. intros. unfold veqb in H. destruct (Val.eq a b); auto; discriminate. Qed.

Lemma veqb_refl: forall a, veqb a a = true.
Proof. intros. unfold veqb. destruct (Val.eq a a); auto. Qed.

Lemma find_fst_some: forall (l: list (val * ddict_st)) q, In q (map fst l) ->
  exists e, find (fun e => veqb (fst e) q) l = Some e /\ fst e = q /\ In e l.
Proof.
  induction l as [|e l IH]; intros q H; simpl in H; [contradiction|]. simpl.
  destruct (veqb (fst e) q) eqn:E.
  - exists e. split; [auto | split; [apply veqb_true; auto | left; auto]].
  - destruct H as [H | H]; [subst; rewrite veqb_refl in E; discriminate|].
    destruct (IH q H) as (e' & H1 & H2 & H3). exists e'. auto.
Qed.

(* the frame's dictionary for a DDict variable: a DDict whose pointer is the variable *)
Lemma mf_dict_ddict: forall pr sp a l shk qv, darg_ddict a <> nullval -> qv_ok pr sp a l qv ->
  exists x buf sh, mf_dict a l shk qv = DA_ddict x buf sh /\ dx_q x = qv.
Proof.
  intros pr sp a l shk qv Hn Hq. unfold mf_dict.
  destruct (veqb qv (darg_ddict a)) eqn:E.
  - apply veqb_true in E. subst qv. destruct a as [| sh pk b | x buf sh]; simpl in Hn; try congruence.
    eauto.
  - destruct Hq as [Hq | (_ & _ & Hq)]; [subst; rewrite veqb_refl in E; discriminate|].
    destruct (find_fst_some l qv Hq) as (e & -> & _ & _). eauto.
Qed.

Lemma mf_probe_off: forall pr sp a l tbl qv sfr,
  andb (sel_on pr sp) (negb (veqb (darg_ddict a) nullval)) = false -> mf_probe pr sp a l tbl qv sfr = qv.
Proof. intros. unfold mf_probe. rewrite H. reflexivity. Qed.

Lemma mf_probe_nohdr: forall pr sp a l tbl qv sfr,
  (forall h, get_frame_header_m (dp_fmt pr =? 1) sfr <> FH_ok h) -> mf_probe pr sp a l tbl qv sfr = qv.
Proof.
  intros. unfold mf_probe. destruct (andb _ _); auto.
  destruct (get_frame_header_m _ sfr) eqn:E; auto. exfalso. eapply H; eauto.
Qed.

Lemma mf_probe_hit: forall pr sp a l tbl qv sfr h,
  sel_on pr sp = true -> darg_ddict a <> nullval -> get_frame_header_m (dp_fmt pr =? 1) sfr = FH_ok h ->
  mf_probe pr sp a l tbl qv sfr =
    (if eq_dec (hs_probe l tbl (fh_dictID h)) nullval then qv else hs_probe l tbl (fh_dictID h)).
Proof.
  intros. unfold mf_probe. rewrite H, H1.
  replace (veqb (darg_ddict a) nullval) with false; [reflexivity|].
  unfold veqb. destruct (Val.eq _ _); congruence.
Qed.

Lemma mf_probe_ok: forall pr sp a l tbl qv sfr,
  (sel_on pr sp = true -> hs_inv l tbl) -> qv_ok pr sp a l qv -> qv_ok pr sp a l (mf_probe pr sp a l tbl qv sfr).
Proof.
  intros pr sp a l tbl qv sfr Hh Hq. unfold mf_probe.
  destruct (sel_on pr sp) eqn:Hs; cbn [andb]; auto.
  destruct (veqb (darg_ddict a) nullval) eqn:Hn; cbn [negb]; auto.
  destruct (get_frame_header_m _ sfr); auto.
  destruct (eq_dec (hs_probe l tbl (fh_dictID h)) nullval) as [E|E]; auto.
  right. split; [auto | split].
  - intro N. rewrite N in Hn. rewrite veqb_refl in Hn. discriminate.
  - apply hs_probe_in; auto.
Qed.

Lemma mf_probe_pp: forall pr sp a l tbl qv sfr h,
  get_frame_header_m (dp_fmt pr =? 1) sfr = FH_ok h -> sel_on pr sp = true -> darg_ddict a <> nullval ->
  hs_probe l tbl (fh_dictID h) = nullval \/ hs_probe l tbl (fh_dictID h) = mf_probe pr sp a l tbl qv sfr.
Proof.
  intros. rewrite (mf_probe_hit pr sp a l tbl qv sfr h) by auto.
  destruct (eq_dec (hs_probe l tbl (fh_dictID h)) nullval); auto.
Qed.

Lemma mf_probe_loc: forall pr sp a l tbl qv sfr (d: dfields),
  (sel_on pr sp = true -> hs_inv l tbl) ->
  (sel_on pr sp = true -> darg_local d a = true -> ~ In (darg_ddict a) (map fst l)) ->
  darg_local d a = true -> mf_probe pr sp a l tbl qv sfr = darg_ddict a -> qv = darg_ddict a.
Proof.
  intros pr sp a l tbl qv sfr d Hh Hg Hl E. unfold mf_probe in E.
  destruct (sel_on pr sp) eqn:Hs; cbn [andb] in E; auto.
  destruct (negb _); auto.
  destruct (get_frame_header_m _ sfr); auto.
  destruct (eq_dec (hs_probe l tbl (fh_dictID h)) nullval) as [N|N]; auto.
  exfalso. apply (Hg eq_refl Hl). rewrite <- E. apply hs_probe_in; auto.
Qed.

Lemma set_ids_valid: forall l q, In q (map fst l) -> set_ids l |-- valid_pointer q.
Proof.
  induction l as [|e l IH]; intros q H; simpl in H; [contradiction|]. unfold set_ids. simpl.
  destruct H as [<- | H].
  - apply sepcon_valid_pointer1. apply ddid_valid.
  - apply sepcon_valid_pointer2. apply IH; auto.
Qed.

End CM_Multi3Aux_1.
