(* FS3 streaming, G2: the dictionary after a successful shortcut with the DDict set (pure facts).
   Copies of G4's set lemmas (LH3G4_dict.v) and the selection case analysis. *)
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3Stmts.
Local Open Scope Z_scope.

Section CM_LH3G2Sel_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma g2s_clean_ids : forall l, set_clean l = true -> Forall (fun e => dd_id (snd e) <> 0) l.
Proof.
intros l Hc. unfold set_clean in Hc. apply andb_prop in Hc. destruct Hc as [_ Hc].
rewrite forallb_forall in Hc. apply Forall_forall. intros e He. specialize (Hc e He).
apply andb_prop in Hc. destruct Hc as [Hc _]. apply negb_true_iff in Hc. apply Z.eqb_neq in Hc. exact Hc.
Qed.

Lemma g2s_clean_auto : forall l e, set_clean l = true -> In e l -> dict_auto (dd_bytes (snd e)) <> None.
Proof.
intros l e Hc He. unfold set_clean in Hc. apply andb_prop in Hc. destruct Hc as [_ Hc].
rewrite forallb_forall in Hc. specialize (Hc e He).
apply andb_prop in Hc. destruct Hc as [_ Hc]. destruct (dict_auto _); congruence.
Qed.

Lemma g2s_find0 : forall l, Forall (fun e => dd_id (snd e) <> 0) l -> set_find l 0 = nullval.
Proof.
intros l Hl. unfold set_find. destruct (find (fun e => dd_id (snd e) =? 0) l) eqn:E; auto.
apply find_some in E. destruct E as [Hin Heq]. apply Z.eqb_eq in Heq.
rewrite Forall_forall in Hl. exfalso. exact (Hl _ Hin Heq).
Qed.

Lemma g2s_find_miss : forall l id, set_clean l = true -> set_sel l id = None -> set_find l id = nullval.
Proof.
intros l id Hc Hs. destruct (Z.eq_dec id 0) as [->|Hn]; [ apply g2s_find0, g2s_clean_ids; auto | ].
unfold set_sel in Hs. rewrite (proj2 (Z.eqb_neq _ _) Hn) in Hs.
unfold set_find. destruct (find (fun e => dd_id (snd e) =? id) l) as [e|] eqn:E; auto.
apply find_some in E. destruct E as [Hin _]. exfalso. exact (g2s_clean_auto l e Hc Hin Hs).
Qed.

Lemma g2s_find_hit : forall l id dq, set_sel l id = Some dq ->
  id <> 0 /\ exists e, In e l /\ dd_id (snd e) = id /\ set_find l id = fst e /\ dict_auto (dd_bytes (snd e)) = Some dq.
Proof.
intros l id dq Hs. unfold set_sel in Hs. destruct (Z.eqb_spec id 0) as [_|Hn]; [ discriminate | ].
split; [ exact Hn | ]. unfold set_find.
destruct (find (fun e => dd_id (snd e) =? id) l) as [e|] eqn:E; [ | discriminate ].
apply find_some in E. destruct E as [Hin Heq]. apply Z.eqb_eq in Heq.
exists e. auto.
Qed.

Lemma g2s_repr_inj : forall a b, 0 <= a <= Int.max_unsigned -> 0 <= b <= Int.max_unsigned ->
  Vint (Int.repr a) = Vint (Int.repr b) -> a = b.
Proof.
intros a b Ha Hb E. apply Vint_inj in E. apply (f_equal Int.unsigned) in E.
rewrite !Int.unsigned_repr in E by lia. exact E.
Qed.

Lemma g2s_st_sel : forall st, dc_set st <> nil ->
  st_sel st = (sel_none, None) \/
  (st_sel st = (set_sel (dc_set st), None) /\ dp_multi (dc_par st) = 1 /\ set_clean (dc_set st) = true /\
   exists dr, dc_dict st = Some dr /\
     (match dr_src dr with DSDDict _ _ => true | _ => negb (Nat.eqb (length (dr_bytes dr)) 0) end) = true).
Proof.
intros st Hne. unfold st_sel. destruct (dc_set st) as [|e0 l0]; [ contradiction | ].
destruct (dc_dict st) as [dr|]; [ | left; reflexivity ].
destruct ((dp_multi (dc_par st) =? 1) && set_clean (e0 :: l0) &&
          match dr_src dr with DSDDict _ _ => true | _ => negb (Nat.eqb (length (dr_bytes dr)) 0) end)%bool eqn:E;
  [ | left; reflexivity ].
apply andb_prop in E. destruct E as [E E3]. apply andb_prop in E. destruct E as [E1 E2]. apply Z.eqb_eq in E1.
right. split; [ reflexivity | ]. split; [ exact E1 | ]. split; [ exact E2 | ]. exists dr. auto.
Qed.

Lemma g2s_st_sel_nil : forall st, dc_set st = nil -> st_sel st = (sel_none, dictref_model (dc_dict st)).
Proof. intros st H. unfold st_sel. rewrite H. reflexivity. Qed.

Lemma g2s_getddict_m1 : forall d, df_uses d = -1 -> getddict_res d = (df_ddict d, d).
Proof. intros d Hu. unfold getddict_res. rewrite Hu. reflexivity. Qed.

Lemma g2s_sel_on_t : forall k st, base_call st k -> dc_set st <> nil -> (c3_set k <> nil -> c3_sp k <> nullval) ->
  dp_multi (dc_par st) = 1 -> sel_on (c3_par k) (c3_sp k) = true.
Proof.
intros k st (_ & Hpar & Hset & _) Hne Hsp Hm. unfold sel_on. rewrite Hpar, Hm. cbn.
assert (c3_sp k <> nullval) by (apply Hsp; rewrite Hset; auto).
unfold veqb. destruct (Val.eq (c3_sp k) _) as [E|E]; [ contradiction | reflexivity ].
Qed.

Lemma g2s_ptr_nn : forall q, isptr q -> q <> nullval.
Proof. intros q H E. subst q. exact H. Qed.

Lemma g2s_mem_ptr : forall l tbl q, hs_inv l tbl -> In q (map fst l) -> isptr q.
Proof.
intros l tbl q (_ & _ & _ & _ & _ & Hp & _) Hin. apply list_in_map_inv in Hin. destruct Hin as [e [-> He]].
rewrite Forall_forall in Hp. apply Hp; auto.
Qed.

Lemma g2s_probe : hs_probe_ok -> forall l tbl id, hs_inv l tbl -> set_clean l = true ->
  0 <= id <= Int.max_unsigned -> hs_probe l tbl id = set_find l id.
Proof. intros HP l tbl id Hi Hc Hr. destruct (HP l tbl id Hi Hr) as [_ H]. apply H, g2s_clean_ids, Hc. Qed.

(* the context's dictionary with bytes (or a switched member): a current DDict *)
Lemma g2s_ddict_nn : forall st d tbl dr, dict_rel3 st d -> hs_inv (dc_set st) tbl -> dc_dict st = Some dr ->
  (match dr_src dr with DSDDict _ _ => true | _ => negb (Nat.eqb (length (dr_bytes dr)) 0) end) = true ->
  df_ddict d <> nullval.
Proof.
intros st d tbl dr Hd Hi E Hne. destruct Hd as [Hd|(_ & Hsw)].
- rewrite E in Hd. cbn in Hd.
  assert (Hz: dr_src dr <> DSOwn /\ (forall p, dr_src dr <> DSRef p) \/ (Zlength (dr_bytes dr) =? 0) = false).
  { destruct (dr_src dr) eqn:Es; [right|right|left; split; [discriminate|intros; discriminate]].
    all: apply Z.eqb_neq; intro Z0; apply Zlength_nil_inv in Z0; rewrite Z0 in Hne; cbn in Hne; discriminate. }
  destruct (dr_src dr) eqn:Es.
  + destruct Hz as [(_ & Hz)|Hz]; [exfalso; eapply Hz; reflexivity|].
    rewrite Hz in Hd. destruct Hd as (Hp & Hdd & _). rewrite Hdd. apply g2s_ptr_nn; auto.
  + destruct Hz as [(Hz & _)|Hz]; [congruence|].
    destruct Hd as (_ & Hd). rewrite Hz in Hd. destruct Hd as (buf & ld & am & Hp & Hdd & _).
    rewrite Hdd; apply g2s_ptr_nn; auto.
  + destruct Hd as (_ & _ & Hp & _ & Hdd & _). rewrite Hdd; apply g2s_ptr_nn; auto.
- destruct Hsw as (_ & _ & _ & Hin). apply g2s_ptr_nn. eapply g2s_mem_ptr; eauto.
Qed.

(* the frame's dictionary (the model's, frame_dict) is the one zstd decodes it with (lh_fdm), and the context after
   the shortcut describes it (cur_dict_ok) *)
Lemma g2s_sel : hs_probe_ok -> forall a k hb x h tbl d1 did1 cd dm d' fs' k',
  base_call (a_st a) k -> (c3_set k <> nil -> c3_sp k <> nullval) ->
  get_frame_header_m (lh_mg k) hb = FH_ok h -> get_frame_header_m (lh_mg k) x = FH_ok h -> fh_frameType h = 0 ->
  frame_compressed_size_m (lh_mg k) x = Some (Zlength x) ->
  0 <= fh_dictID h <= Int.max_unsigned ->
  lhA_sel k hb 0 (fh_val h) tbl d1 did1 ->
  cur_dict_ok (a_st a) k cd ->
  (fst (st_sel (a_st a)) = sel_none -> snd (st_sel (a_st a)) = None -> cd = None) ->
  frame_dict (lh_mg k) (fst (st_sel (a_st a))) cd hb = Some dm ->
  lhB_sw (k_A k (fh_val h) d1 did1) tbl x d' -> lhB_sel_fp (k_A k (fh_val h) d1 did1) tbl x fs' d' ->
  c3_dict k' = d' -> fs_fParams (c3_fs k') = fs_fParams fs' ->
  lh_fdm a (k_A k (fh_val h) d1 did1) x dm /\ cur_dict_ok (a_st a) k' (Some dm).
Proof.
intros HP a k hb x h tbl d1 did1 cd dm d' fs' k' Hb Hsp G Gx Ht Hfcs Hidr HA Hcd Hcdn Hfd HD HSF Hk'd Hk'f.
assert (Hb' := Hb). destruct Hb' as (Hstab & Hpar & Hset & Hdr & Hsco & Hfp).
unfold frame_dict in Hfd. rewrite G in Hfd.
assert (Hcase: dc_set (a_st a) = nil \/ dc_set (a_st a) <> nil)
  by (destruct (dc_set (a_st a)); [left|right]; congruence).
destruct Hcase as [Hnil|Hnn].
{ rewrite (g2s_st_sel_nil _ Hnil) in Hfd. cbn [fst sel_none] in Hfd. subst cd.
  destruct (Hcd dm eq_refl) as [(_ & Hdm)|(Hn & _)]; [|contradiction].
  split; [left; auto|]. intros dm' E. injection E as <-. left; auto. }
destruct (g2s_st_sel _ Hnn) as [Es|(Es & Hm & Hcl & dr0 & Edr & Hsrc)].
{ rewrite Es in Hcdn, Hfd. cbn [fst snd sel_none] in Hcdn, Hfd. rewrite (Hcdn eq_refl eq_refl) in Hfd. discriminate. }
rewrite Es in Hfd. cbn [fst] in Hfd.
assert (Hon: sel_on (c3_par k) (c3_sp k) = true) by (apply (g2s_sel_on_t k (a_st a)); auto).
destruct HA as (_ & _ & id & Hidv & Hsb). unfold sel_by in Hsb. rewrite Hon in Hsb.
destruct Hsb as (Hinv & Hid & Hd1 & _).
assert (Eid: id = fh_dictID h).
{ specialize (Hidv Hon). cbn [fp_dictID fh_val fst snd] in Hidv.
  apply g2s_repr_inj; auto. }
subst id. rewrite Hset in Hinv, Hd1.
set (l := dc_set (a_st a)) in *.
assert (Hk1: c3_dict (k_A k (fh_val h) d1 did1) = d1 /\ c3_par (k_A k (fh_val h) d1 did1) = c3_par k /\
             c3_sp (k_A k (fh_val h) d1 did1) = c3_sp k /\ c3_set (k_A k (fh_val h) d1 did1) = c3_set k /\
             lh_mg (k_A k (fh_val h) d1 did1) = lh_mg k) by (repeat split).
destruct Hk1 as (Ek1d & Ek1p & Ek1s & Ek1l & Ek1m).
unfold lhB_sw in HD. unfold lhB_sel_fp in HSF.
rewrite Ek1d, Ek1p, Ek1s, Ek1l, Ek1m in HD, HSF. rewrite Hset in HD, HSF. fold l in HD, HSF.
assert (Hpr: forall id, 0 <= id <= Int.max_unsigned -> hs_probe l tbl id = set_find l id)
  by (intros; apply g2s_probe; auto).
destruct (set_sel l (fh_dictID h)) as [dq|] eqn:Ess.
- (* a member of the frame's ID *)
  injection Hfd as <-.
  destruct (g2s_find_hit _ _ _ Ess) as (_ & e & Hin & _ & Hfind & Hda).
  assert (Hep: isptr (fst e)) by (apply (g2s_mem_ptr l tbl); auto; apply in_map; auto).
  assert (Hen: fst e <> nullval) by (apply g2s_ptr_nn; auto).
  assert (Hdk: df_ddict (c3_dict k) <> nullval) by (eapply g2s_ddict_nn; eauto; rewrite <- Hset; exact Hinv).
  assert (Ed1: d1 = switch_fields (fst e)).
  { rewrite Hd1. unfold sel_dict, sel_r.
    destruct (eq_dec (df_ddict (c3_dict k)) nullval) as [E|_]; [contradiction|].
    rewrite Hpr, Hfind by auto. destruct (eq_dec (fst e) nullval); [contradiction|reflexivity]. }
  assert (Ed': d' = switch_fields (fst e)).
  { destruct HD as [HD|(_ & q & Hq & HD & Hqp)].
    - rewrite HD, Ed1, g2s_getddict_m1 by reflexivity. reflexivity.
    - rewrite HD, (Hqp h Gx), Hpr, Hfind by auto. reflexivity. }
  split.
  + right. split; [exact Hnn|]. split; [rewrite Ek1p, Ek1s; exact Hon|]. split; [exact Hcl|].
    split; [rewrite Ek1d, Ed1, g2s_getddict_m1 by reflexivity; exact Hen|].
    exists h, (fst e), (snd e). split; [rewrite Ek1m; exact Gx|]. split; [exact Ht|]. split; [rewrite Ek1m; exact Hfcs|].
    split.
    * fold l. rewrite Hfind. destruct (eq_dec (fst e) nullval); [contradiction|reflexivity].
    * split; [destruct e; exact Hin|exact Hda].
  + intros dm' E. injection E as <-. right. split; [exact Hnn|].
    rewrite Hk'd, Ed'. split; [reflexivity|]. split.
    { exists (snd e). split; [destruct e; exact Hin|exact Hda]. }
    destruct HSF as (id' & Hfp' & Hid' & Hpb).
    { exact Hon. }
    { rewrite Ed1, g2s_getddict_m1 by reflexivity. exact Hen. }
    { exists h; auto. }
    exists id'. rewrite Hk'f. split; [exact Hfp'|]. split; [exact Hid'|].
    rewrite <- Hpr by auto. rewrite Ed' in Hpb. exact Hpb.
- (* no member: the current DDict *)
  subst cd. destruct (Hcd dm eq_refl) as [(Hn & _)|(_ & Hu & (dd & Hin & Hda) & _)]; [contradiction|].
  try fold l in Hin.
  assert (Hfind: set_find l (fh_dictID h) = nullval) by (apply g2s_find_miss; auto).
  assert (Hkp: isptr (df_ddict (c3_dict k))) by (apply (g2s_mem_ptr l tbl); auto; apply (in_map fst) in Hin; exact Hin).
  assert (Hkn: df_ddict (c3_dict k) <> nullval) by (apply g2s_ptr_nn; auto).
  assert (Ed1: d1 = c3_dict k).
  { rewrite Hd1. unfold sel_dict, sel_r.
    destruct (eq_dec (df_ddict (c3_dict k)) nullval) as [E|_]; [contradiction|].
    rewrite Hpr, Hfind by auto. destruct (eq_dec nullval nullval); [reflexivity|congruence]. }
  assert (Ed': d' = c3_dict k).
  { destruct HD as [HD|(_ & q & Hq & HD & Hqp)].
    - rewrite HD, Ed1, g2s_getddict_m1 by exact Hu. reflexivity.
    - exfalso. rewrite (Hqp h Gx), Hpr, Hfind in Hq by auto.
      apply (g2s_mem_ptr l tbl) in Hq; auto. }
  split.
  + right. split; [exact Hnn|]. split; [rewrite Ek1p, Ek1s; exact Hon|]. split; [exact Hcl|].
    split; [rewrite Ek1d, Ed1, g2s_getddict_m1 by exact Hu; exact Hkn|].
    exists h, (df_ddict (c3_dict k)), dd. split; [rewrite Ek1m; exact Gx|]. split; [exact Ht|].
    split; [rewrite Ek1m; exact Hfcs|]. split.
    * fold l. rewrite Hfind, Ek1d, Ed1. destruct (eq_dec nullval nullval); [reflexivity|congruence].
    * split; [exact Hin|exact Hda].
  + intros dm' E. injection E as <-. right. split; [exact Hnn|].
    rewrite Hk'd, Ed'. split; [exact Hu|]. split.
    { exists dd. split; [exact Hin|exact Hda]. }
    destruct HSF as (id' & Hfp' & Hid' & Hpb).
    { exact Hon. }
    { rewrite Ed1, g2s_getddict_m1 by exact Hu. exact Hkn. }
    { exists h; auto. }
    exists id'. rewrite Hk'f. split; [exact Hfp'|]. split; [exact Hid'|].
    rewrite <- Hpr by auto. rewrite Ed' in Hpb. exact Hpb.
Qed.

(* the selection's dictionary fields are a context dictionary (copy of G4's g4_dict_rel1) *)
Lemma g2s_dict_rel1 : hs_probe_ok -> forall st k hb kk v tbl d1 did1,
  base_call st k -> lhA_sel k hb kk v tbl d1 did1 -> dict_rel3 st d1.
Proof.
intros Hpr st k hb kk v tbl d1 did1 Hb Hsel.
destruct Hb as (_ & _ & Hset & Hdr & _).
destruct Hsel as (_ & _ & id & _ & Hsb). unfold sel_by in Hsb.
destruct (sel_on (c3_par k) (c3_sp k)).
- destruct Hsb as (Hinv & Hidr & Hd1 & _). subst d1. unfold sel_dict.
  destruct (eq_dec (sel_r (c3_dict k) (c3_set k) tbl id) nullval) as [E|E]; [ exact Hdr | ].
  right. unfold sel_r in *.
  destruct (eq_dec (df_ddict (c3_dict k)) nullval); [ contradiction | ].
  destruct (Hpr _ _ _ Hinv Hidr) as [[Hn | Hin] _]; [ contradiction | ].
  rewrite Hset in Hin. split.
  + intro Hnil. rewrite Hnil in Hin. contradiction.
  + unfold dict_switched, switch_fields. cbn. rewrite Hset. auto.
- destruct Hsb as [Hd1 _]. subst d1. exact Hdr.
Qed.

(* ZSTD_getDDict keeps the context's dictionary (copy of G4's g4_dict_rel2) *)
Lemma g2s_dict_rel2 : forall W st d, stream_dict_ok W st -> dict_rel3 st d -> dict_rel3 st (snd (getddict_res d)).
Proof.
intros W st d Hsd Hd. unfold getddict_res.
destruct (Z.eqb_spec (df_uses d) 0) as [U0|U0]; cbn [snd].
- destruct Hd as [Hd | (_ & _ & Hu & _ & _)]; [ | lia ].
  left. destruct (dc_dict st) as [dr|] eqn:Ed; cbn in Hd |- *; [ | split; [reflexivity | left; reflexivity] ].
  unfold stream_dict_ok in Hsd. rewrite Ed in Hsd. destruct Hsd as ((Ho & Hs) & _).
  destruct (dr_src dr) as [pk | | q pref]; [ contradiction | | ].
  + destruct Hd as (Ho' & Hz). split; [ exact Ho' | ].
    destruct (Zlength (dr_bytes dr) =? 0); [ auto | ].
    destruct Hz as (buf & ld & am & _ & _ & Hu & _). lia.
  + destruct Hd as (_ & _ & _ & _ & _ & Hu & _). lia.
- destruct (Z.eqb_spec (df_uses d) 1) as [U1|U1]; cbn [snd]; [ | exact Hd ].
  exfalso. destruct Hd as [Hd | (_ & _ & Hu & _ & _)]; [ | lia ].
  destruct (dc_dict st) as [dr|] eqn:Ed; cbn in Hd; [ | lia ].
  unfold stream_dict_ok in Hsd. rewrite Ed in Hsd. destruct Hsd as ((Ho & Hs) & _).
  destruct (dr_src dr) as [pk | | q pref]; [ contradiction | | ].
  + destruct Hd as (Ho' & Hz). destruct (Zlength (dr_bytes dr) =? 0).
    * subst d. cbn in U1. lia.
    * destruct Hz as (buf & ld & am & _ & _ & Hu & _). lia.
  + destruct Hd as (_ & _ & _ & _ & _ & Hu & _). lia.
Qed.

(* the dictionary fields after the shortcut are a context dictionary *)
Lemma g2s_dict_rel_brk : hs_probe_ok -> forall W st k hb v tbl d1 did1 d',
  base_call st k -> stream_dict_ok W st -> lhA_sel k hb 0 v tbl d1 did1 -> lhB_dict (k_A k v d1 did1) d' ->
  dict_rel3 st d'.
Proof.
intros HP W st k hb v tbl d1 did1 d' Hb Hsd HA HD.
destruct HD as [HD|(_ & q & Hq & HD)]; subst d'.
- apply (g2s_dict_rel2 W); auto. cbn [k_A c3_with_dict c3_dict]. eapply g2s_dict_rel1; eauto.
- destruct Hb as (_ & _ & Hset & _). cbn [k_A k_redict c3_with_s c3_with_dict c3_with_fs c3_set] in Hq. rewrite Hset in Hq.
  right. split.
  + intro Hn. rewrite Hn in Hq. contradiction.
  + unfold dict_switched, switch_fields. cbn. auto.
Qed.

End CM_LH3G2Sel_1.
