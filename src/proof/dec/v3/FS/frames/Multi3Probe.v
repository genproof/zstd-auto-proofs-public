(* FS3 one-shot frames, ZSTD_decompressMultiFrame: the resources of fix F4's probe *)
Require Export Zstd.proof.dec.v3.FS.frames.Multi3Res.
Local Open Scope logic.

Section CM_Multi3Probe_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* ---------- the probe ---------- *)

Section Probe.
Variable DENT : dent_pred.

(* a DDict's resources other than what ZSTD_DDictHashSet reads (ddid) *)
Definition dd_rest (gv: globals) (x: ddx) (buf: val) : mpred :=
  let q := dx_q x in let b := dx_bytes x in
  let t := Tstruct _ZSTD_DDict_s noattr in
  !! (isptr q /\ Zlength b <= 2 ^ 63 - 1 /\ bytes_ok b /\
      ld_rel b (dx_ld x) /\ (dx_raw x = true \/ dict_auto_c b (dx_ld x) <> None) /\
      (isptr buf \/ (buf = nullval /\ dx_ref x = Some nullval /\ b = nil)) /\ (ddx_copied x = true -> 0 < Zlength b) /\
      (match dx_ref x with Some p => buf = p | None => True end) /\ cmem_ok (dx_mem x)) &&
  (field_at Ews t (DOT _dictContent) buf q *
   field_at Ews t (DOT _dictSize) (Vlong (Int64.repr (Zlength b))) q *
   field_at Ews t (DOT _entropyPresent)
     (Vint (Int.repr (match ddx_ent x with Some _ => 1 | None => 0 end))) q *
   field_at Ews t (DOT _cMem) (cmem_v (dx_mem x)) q) *
  DENT gv (dx_q x) (ddx_ent x) * ddict_mem x buf * ddict_pad (dx_q x).

Lemma ddrep_split (gv: globals) (x: ddx) (buf: val) :
  dx_raw x = false ->
  ddict_rep_at DENT gv x buf =
  ddid (dx_q x) (dict_id_of (dx_bytes x)) (if ddx_copied x then buf else nullval) * dd_rest gv x buf.
Proof.
  intros HR. unfold ddict_rep_at, ddict_struct, dd_rest, ddid. rewrite HR.
  apply pred_ext.
  - Intros. pose proof (dict_id_of_range (dx_bytes x) ltac:(tauto)). entailer!.
  - Intros. entailer!.
Qed.

Definition ddres_rest (gv: globals) (sh: share) (q: val) (dd: ddict_st) : mpred :=
  dd_rest gv (dd_x q dd) (dd_buf dd) *
  match dd_ref dd with
  | Some p => data_at sh (tarray tuchar (Zlength (dd_bytes dd))) (zbytes (dd_bytes dd)) p
  | None => emp
  end.

Lemma ddb_x (q: val) (dd: ddict_st) :
  (if ddx_copied (dd_x q dd) then dd_buf dd else nullval) = ddb dd.
Proof. unfold ddx_copied, dd_x, ddb; simpl. destruct (dd_xref dd); reflexivity. Qed.

Lemma ddid_valid (q: val) (id: Z) (db: val) : ddid q id db |-- valid_pointer q.
Proof.
  unfold ddid. apply andp_left2. apply sepcon_valid_pointer1.
  apply field_at_valid_ptr0; auto; reflexivity.
Qed.

Lemma ddres_split (gv: globals) (sh: share) (q: val) (dd: ddict_st) :
  ddict_res (DD3_of DENT) gv sh q dd = ddid q (dd_id dd) (ddb dd) * ddres_rest gv sh q dd.
Proof.
  unfold ddict_res, ddres_rest, DD3_of.
  rewrite (ddrep_split gv (dd_x q dd) (dd_buf dd)) by reflexivity.
  rewrite ddb_x. change (dx_q (dd_x q dd)) with q. change (dict_id_of (dx_bytes (dd_x q dd))) with (dd_id dd).
  apply pred_ext.
  - rewrite <- sepcon_assoc. apply sepcon_derives; [apply andp_left1 | ]; auto.
  - rewrite <- sepcon_assoc. apply sepcon_derives; auto. apply andp_right; auto.
    apply sepcon_valid_pointer1, ddid_valid.
Qed.

(* folds *)
Lemma fold_sep_map2 {A} (f g: A -> mpred) (l: list A) :
  fold_right sepcon emp (map (fun e => f e * g e) l) =
  fold_right sepcon emp (map f l) * fold_right sepcon emp (map g l).
Proof.
  induction l; simpl. { rewrite emp_sepcon; auto. }
  rewrite IHl. apply pred_ext; cancel.
Qed.

Lemma fold_sep_ext {A} (f g: A -> mpred) (l: list A) :
  (forall e, In e l -> f e = g e) ->
  fold_right sepcon emp (map f l) = fold_right sepcon emp (map g l).
Proof. intros H. f_equal. apply map_ext_in. auto. Qed.

Definition ddid_e (e: val * ddict_st) : mpred := ddid (fst e) (dd_id (snd e)) (ddb (snd e)).

Definition ids_but (l: list (val * ddict_st)) (q0: val) : mpred :=
  fold_right sepcon emp (map (fun e => if Val.eq (fst e) q0 then emp else ddid_e e) l).

Definition rest_but (gv: globals) (shk: share) (l: list (val * ddict_st)) (q0: val) : mpred :=
  fold_right sepcon emp (map (fun e => if Val.eq (fst e) q0 then emp else ddres_rest gv shk (fst e) (snd e)) l).

Lemma set_full_split (gv: globals) (shk: share) (l: list (val * ddict_st)) (q0: val) :
  set_full DENT gv shk l q0 = ids_but l q0 * rest_but gv shk l q0.
Proof.
  unfold set_full, ids_but, rest_but. rewrite <- fold_sep_map2. apply fold_sep_ext.
  intros e _. destruct (Val.eq (fst e) q0). { rewrite emp_sepcon; auto. }
  rewrite ddres_split. reflexivity.
Qed.

Lemma ids_but_out (l: list (val * ddict_st)) (q0: val) :
  ~ In q0 (map fst l) -> ids_but l q0 = set_ids l.
Proof.
  intros H. unfold ids_but, set_ids. apply fold_sep_ext. intros e He.
  destruct (Val.eq (fst e) q0); [| reflexivity].
  exfalso; apply H. subst. apply in_map; auto.
Qed.

Lemma ids_but_in (l: list (val * ddict_st)) (q0: val) (dd0: ddict_st) :
  NoDup (map fst l) -> In (q0, dd0) l -> ids_but l q0 * ddid_e (q0, dd0) = set_ids l.
Proof.
  induction l as [| e l IH]; intros ND Hin; [destruct Hin |].
  simpl in ND. inversion ND; subst.
  unfold ids_but, set_ids in *; simpl.
  destruct (Val.eq (fst e) q0).
  - assert (e = (q0, dd0)).
    { destruct Hin as [-> | Hin]; auto. exfalso. apply H1. rewrite e0. change q0 with (fst (q0, dd0)).
      apply in_map; auto. }
    subst e. rewrite emp_sepcon, sepcon_comm. f_equal.
    apply (ids_but_out l q0). exact H1.
  - destruct Hin as [-> | Hin]; [simpl in n; contradiction |].
    rewrite sepcon_assoc. rewrite IH; auto.
Qed.

Lemma hset_tbl_inv (am: option cmem) (sp: val) (l: list (val * ddict_st)) (tbl: list val) :
  hset_tbl am sp l tbl = !! (hs_inv l tbl) && hset_tbl am sp l tbl.
Proof.
  apply pred_ext; [| apply andp_left2; auto].
  unfold hset_tbl. Intros tp. Exists tp. entailer!.
Qed.

End Probe.

(* the set's table and IDs, for ZSTD_DDictHashSet_getDDict, from MultiFrame's selection resources *)
Lemma mf_probe_split: forall DENT gv p pr sp d l tbl shk a W shd cap dst dcur am hb,
  sel_on pr sp = true -> msel_ok W d l a shk shd cap dst ->
  (darg_local d a = true -> ~ In (darg_ddict a) (map fst l)) ->
  dc_ok pr sp l d dcur ->
  exists MK0: mpred,
    (msel_res DENT gv p pr sp dcur l tbl shk a am hb * darg_res3 DENT gv pr sp d a |--
       hset_tbl am sp l tbl * set_ids l * MK0) /\
    (hset_tbl am sp l tbl * set_ids l * MK0 |--
       msel_res DENT gv p pr sp dcur l tbl shk a am hb * darg_res3 DENT gv pr sp d a).
Proof.
  intros DENT gv p pr sp d l tbl shk a W shd cap dst dcur am hb Hon Hok Hloc _.
  unfold msel_res. rewrite Hon. rewrite set_full_split.
  destruct (in_dec Val.eq (darg_ddict a) (map fst l)) as [Hin0 | Hout].
  2: { rewrite ids_but_out by auto.
       exists (mem_mgr gv * dgroup DENT gv p dcur * cm_have am (hb + local_held dcur) *
               rest_but DENT gv shk l (darg_ddict a) * darg_res3 DENT gv pr sp d a).
       split; cancel. }
  assert (Hlf: darg_local d a = false).
  { destruct (darg_local d a) eqn:E; auto. exfalso; apply (Hloc eq_refl Hin0). }
  pose proof Hin0 as Hin. apply in_map_iff in Hin as [[q1 dd0] [Hq1 Hin]]. simpl in Hq1. subst q1.
  destruct a as [| sh pk b | x buf sh].
  1, 2: exists FF; split;
    [ rewrite (hset_tbl_inv am sp l tbl) at 1; Intros; exfalso;
      match goal with H: hs_inv _ _ |- _ => destruct H as (_&_&_&_&_&Hp&_) end;
      rewrite Forall_forall in Hp; specialize (Hp _ Hin); simpl in Hp; contradiction
    | rewrite sepcon_FF; apply FF_left ].
  simpl darg_ddict in *.
  destruct Hok as (_&_&_&Hent&_). destruct (Hent x buf sh dd0 eq_refl Hin) as [Hx Hb].
  remember (dx_q x) as q0 eqn:Hq0. subst x buf. clear Hq0.
  unfold darg_res3. rewrite Hon, Hlf. simpl andb. cbv iota. unfold darg_res.
  rewrite ddrep_split by reflexivity. rewrite ddb_x.
  change (dict_id_of (dx_bytes (dd_x q0 dd0))) with (dd_id dd0). change (dx_q (dd_x q0 dd0)) with q0.
  exists (mem_mgr gv * dgroup DENT gv p dcur * cm_have am (hb + local_held dcur) * rest_but DENT gv shk l q0 *
          dd_rest DENT gv (dd_x q0 dd0) (dd_buf dd0) *
          (if ddx_copied (dd_x q0 dd0) then emp else bytes_at sh (dx_bytes (dd_x q0 dd0)) (dd_buf dd0))).
  split.
  - rewrite (hset_tbl_inv am sp l tbl) at 1. Intros.
    match goal with H: hs_inv _ _ |- _ => destruct H as (_&_&_&Hnd&_) end.
    rewrite <- (ids_but_in l q0 dd0) by auto. unfold ddid_e; cbn [fst snd]. cancel.
  - rewrite (hset_tbl_inv am sp l tbl) at 1. Intros.
    match goal with H: hs_inv _ _ |- _ => destruct H as (_&_&_&Hnd&_) end.
    rewrite <- (ids_but_in l q0 dd0) by auto. unfold ddid_e; cbn [fst snd]. cancel.
Qed.

Lemma mf_hs: forall DENT gv p pr sp dcur l tbl shk a am hb,
  msel_res DENT gv p pr sp dcur l tbl shk a am hb |-- !! (sel_on pr sp = true -> hs_inv l tbl).
Proof.
  intros. unfold msel_res. destruct (sel_on pr sp).
  - rewrite (hset_tbl_inv am sp l tbl). Intros. apply prop_right; auto.
  - apply prop_right; discriminate.
Qed.


(* both lemmas above *)
Lemma mf_probe_all : True.
Proof. pose proof mf_probe_split. pose proof mf_hs. exact I. Qed.

End CM_Multi3Probe_1.
