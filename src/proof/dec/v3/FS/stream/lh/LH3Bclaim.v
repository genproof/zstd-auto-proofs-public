(* FS3 streaming, case zdss_loadHeader, piece B: the shortcut's one-shot claim with the selection on:
   usingDDict_int_spec3's oneshot_sel under the probe's selection gives oneshot_ok with the dictionary of lh_fdm
   (P_shortcut_sel).  The probe's selection on a clean set is set_sel (copied from the one-shot part,
   oneshot3/O3ModelPsel.v). *)
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3Stmts Zstd.proof.dec.v3.FS.stream.lh.LH3Gfh.

Section CM_LH3Bclaim_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma bc_psel_find_ptr (l: list (val * ddict_st)) (e: val * ddict_st) :
  NoDup (map fst l) -> In e l -> find (fun e' => veqb (fst e') (fst e)) l = Some e.
Proof.
  induction l as [|a r IH]; simpl; intros HN HI; [contradiction|].
  inversion HN as [|x y Hnin HN' Hxy]; subst.
  destruct HI as [<-|HI].
  - unfold veqb. destruct (Val.eq (fst a) (fst a)); [reflexivity|congruence].
  - unfold veqb at 1. destruct (Val.eq (fst a) (fst e)) as [E|E].
    + exfalso. apply Hnin. rewrite E. apply in_map. exact HI.
    + apply IH; assumption.
Qed.

Lemma bc_psel_set_sel (l: list (val * ddict_st)) (tbl: list val) :
  hs_probe_ok -> hs_inv l tbl -> set_clean l = true ->
  Forall (fun e => ld_rel (dd_bytes (snd e)) (dd_ld (snd e))) l ->
  forall id, 0 <= id <= Int.max_unsigned -> psel l tbl id = set_sel l id.
Proof.
  intros Hp Hinv Hc Hld id Hid.
  unfold set_clean in Hc. apply andb_prop in Hc. destruct Hc as [_ Hc].
  rewrite forallb_forall in Hc.
  assert (Hnz: Forall (fun e => dd_id (snd e) <> 0) l).
  { rewrite Forall_forall. intros e He. specialize (Hc e He).
    apply andb_prop in Hc. destruct Hc as [Hc _]. apply negb_true_iff in Hc. apply Z.eqb_neq in Hc. exact Hc. }
  destruct (Hp l tbl id Hinv Hid) as [_ Heq]. specialize (Heq Hnz).
  destruct Hinv as (_ & _ & _ & HND & _ & Hptr & _).
  unfold psel, set_sel. rewrite Heq. unfold set_find.
  destruct (id =? 0) eqn:Hz.
  - apply Z.eqb_eq in Hz. subst id.
    destruct (find (fun e => dd_id (snd e) =? 0) l) eqn:Hf.
    + exfalso. apply find_some in Hf. destruct Hf as [Hin Hf]. apply Z.eqb_eq in Hf.
      rewrite Forall_forall in Hnz. exact (Hnz _ Hin Hf).
    + destruct (eq_dec nullval nullval); [reflexivity|congruence].
  - destruct (find (fun e => dd_id (snd e) =? id) l) as [e|] eqn:Hf.
    + apply find_some in Hf. destruct Hf as [Hin _].
      rewrite Forall_forall in Hptr. specialize (Hptr e Hin).
      destruct (eq_dec (fst e) nullval) as [E|E].
      { rewrite E in Hptr. contradiction. }
      rewrite (bc_psel_find_ptr l e HND Hin).
      specialize (Hc e Hin). apply andb_prop in Hc. destruct Hc as [_ Hc].
      destruct (dict_auto (dd_bytes (snd e))) as [dm|] eqn:Ha; [|discriminate].
      rewrite Forall_forall in Hld.
      unfold ddx_model, dd_x; simpl.
      exact (ld_rel_auto_some _ _ _ (Hld e Hin) Ha).
    + destruct (eq_dec nullval nullval); [reflexivity|congruence].
Qed.

Lemma bc_nodup_in (l: list (val * ddict_st)) (q: val) (a b: ddict_st) :
  NoDup (map fst l) -> In (q, a) l -> In (q, b) l -> a = b.
Proof.
  induction l as [|e r IH]; simpl; intros HN Ha Hb; [contradiction|].
  inversion HN as [|x y Hnin HN' Hxy]; subst.
  destruct Ha as [Ea|Ha]; destruct Hb as [Eb|Hb].
  - subst e. inversion Eb. reflexivity.
  - subst e. exfalso. apply Hnin. apply in_map_iff. exists (q, b); auto.
  - subst e. exfalso. apply Hnin. apply in_map_iff. exists (q, a); auto.
  - apply IH; auto.
Qed.

(* getDDict's DDict, when the fields after it have one *)
Lemma bc_getddict (d: dfields) :
  df_ddict (snd (getddict_res d)) <> nullval -> fst (getddict_res d) = df_ddict d /\ df_ddict d <> nullval.
Proof.
  unfold getddict_res. destruct (df_uses d =? 0); [simpl; congruence|].
  destruct (df_uses d =? 1); simpl; auto.
Qed.

Lemma lhB_claim_sel : P_shortcut_sel -> P_shortcut_sel_ref -> hs_probe_ok ->
  forall (l: list (val * ddict_st)) (tbl: list val) (pr: dparams) (d1: dfields) (ad: darg) (x: list Z)
         (cap r: Z) (out: list val) (h: frame_header) (q: val) (dd: ddict_st) (dm: dict_model),
  hs_inv l tbl -> set_clean l = true -> Forall (fun e => ld_rel (dd_bytes (snd e)) (dd_ld (snd e))) l ->
  darg_ddict ad = fst (getddict_res d1) -> df_ddict (snd (getddict_res d1)) <> nullval ->
  (forall dd dm, In (darg_ddict ad, dd) l -> dict_auto (dd_bytes dd) = Some dm -> darg_model ad = Some dm) ->
  bytes_ok x ->
  get_frame_header_m (dp_fmt pr =? 1) x = FH_ok h -> fh_frameType h = 0 ->
  frame_compressed_size_m (dp_fmt pr =? 1) x = Some (Zlength x) ->
  q = (if eq_dec (set_find l (fh_dictID h)) nullval then df_ddict d1 else set_find l (fh_dictID h)) ->
  In (q, dd) l -> dict_auto (dd_bytes dd) = Some dm ->
  (darg_ddict ad <> nullval -> oneshot_sel (dmode_of pr) (psel l tbl) (darg_model ad) x cap r out) ->
  oneshot_ok (dmode_of pr) (Some dm) x cap r out.
Proof.
  intros Psel Pref Hprobe l tbl pr d1 ad x cap r out h q dd dm Hinv Hcl Hld Had Hd2 Hmod Hbx Hh Ht Hfc Hq Hin Hdm Hos.
  destruct (bc_getddict d1 Hd2) as [Eg Hnn].
  assert (Hadn: darg_ddict ad <> nullval) by (rewrite Had, Eg; exact Hnn).
  specialize (Hos Hadn).
  assert (Hid: 0 <= fh_dictID h <= Int.max_unsigned).
  { destruct (gfh3_ok _ _ _ Hh Hbx) as (_&_&_&_&_&_&_&_&_&Hd&_). exact Hd. }
  assert (Hps := bc_psel_set_sel l tbl Hprobe Hinv Hcl Hld (fh_dictID h) Hid).
  pose proof Hinv as (_ & _ & _ & HND & _ & Hptr & _).
  assert (Hfd: frame_dict (dp_fmt pr =? 1) (psel l tbl) (darg_model ad) x = Some dm).
  { unfold frame_dict. rewrite Hh, Hps. unfold set_sel. unfold set_find in Hq.
    destruct (find (fun e => dd_id (snd e) =? fh_dictID h) l) as [e|] eqn:Hf.
    - apply find_some in Hf. destruct Hf as [Hine Hfe]. apply Z.eqb_eq in Hfe.
      assert (Hpe: isptr (fst e)) by (rewrite Forall_forall in Hptr; exact (Hptr e Hine)).
      destruct (eq_dec (fst e) nullval) as [E|E]; [rewrite E in Hpe; contradiction|].
      subst q. destruct e as [qe de]. simpl in *.
      assert (de = dd) by exact (bc_nodup_in l qe de dd HND Hine Hin). subst de.
      destruct (fh_dictID h =? 0) eqn:Hz.
      + exfalso. apply Z.eqb_eq in Hz. unfold set_clean in Hcl. apply andb_prop in Hcl. destruct Hcl as [_ Hcl].
        rewrite forallb_forall in Hcl. specialize (Hcl _ Hine). simpl in Hcl.
        rewrite Hfe, Hz in Hcl. discriminate.
      + rewrite Hdm. reflexivity.
    - destruct (eq_dec nullval nullval) as [_|E]; [|congruence].
      subst q. rewrite <- Eg, <- Had in Hin.
      destruct (fh_dictID h =? 0); apply (Hmod dd dm Hin Hdm). }
  assert (Hdec := Psel (dmode_of pr) (psel l tbl) (darg_model ad) x dm Hfc (ex_intro _ h (conj Hh Ht)) Hfd).
  unfold oneshot_sel in Hos. unfold oneshot_ok. rewrite <- Hdec.
  destruct Hos as [Hcap Hm]. split; [exact Hcap|].
  destruct (decode_series_m (dmode_of pr) (psel l tbl) (darg_model ad) no_wlim x); auto.
  (* a refusal with the frame's own dictionary is one with the selection *)
  intros Href. apply Hm.
  exact (Pref (dmode_of pr) (psel l tbl) (darg_model ad) x dm Hfc (ex_intro _ h (conj Hh Ht)) Hfd Href).
Qed.

(* the claim of lhB_facts from usingDDict_int_spec3's, the selection on or off *)
Lemma lhB_claim : MF3 -> hs_probe_ok ->
  forall (a: dsa) (k1: cst3) (tbl: list val) (ad: darg) (x: list Z) (cap r: Z) (out: list val),
  c3_set k1 = dc_set (a_st a) ->
  (sel_on (c3_par k1) (c3_sp k1) = true -> c3_set k1 <> nil /\ hs_inv (c3_set k1) tbl) ->
  darg_ddict ad = fst (getddict_res (c3_dict k1)) ->
  (sel_on (c3_par k1) (c3_sp k1) = false -> dc_set (a_st a) = nil ->
     forall dm, dictref_model (dc_dict (a_st a)) = Some dm -> darg_model ad = Some dm) ->
  (sel_on (c3_par k1) (c3_sp k1) = true ->
     Forall (fun e => ld_rel (dd_bytes (snd e)) (dd_ld (snd e))) (c3_set k1) /\
     (forall dd dm, In (darg_ddict ad, dd) (c3_set k1) -> dict_auto (dd_bytes dd) = Some dm ->
        darg_model ad = Some dm)) ->
  bytes_ok x ->
  (sel_on (c3_par k1) (c3_sp k1) = false \/ darg_ddict ad = nullval ->
     oneshot_ok (dmode_of (c3_par k1)) (darg_model ad) x cap r out) ->
  (sel_on (c3_par k1) (c3_sp k1) = true -> darg_ddict ad <> nullval ->
     oneshot_sel (dmode_of (c3_par k1)) (psel (c3_set k1) tbl) (darg_model ad) x cap r out) ->
  forall dm, lh_fdm a k1 x dm -> oneshot_ok (dmode_of (c3_par k1)) (Some dm) x cap r out.
Proof.
  intros MFh Hprobe a k1 tbl ad x cap r out Hset Hsel Hdq Hmod Hmods Hbx H1 H2 dm Hfdm.
  destruct Hfdm as [[Hn Hdm] | (Hn & Hon & Hcl & Hd2 & h & q & dd & Hh & Ht & Hfc & Hq & Hin & Hdm)].
  - destruct (sel_on (c3_par k1) (c3_sp k1)) eqn:Es.
    + destruct (Hsel eq_refl) as [Hne _]. rewrite Hset in Hne. contradiction.
    + rewrite <- (Hmod eq_refl Hn dm Hdm). apply H1. left; reflexivity.
  - destruct (Hsel Hon) as [_ Hinv]. destruct (Hmods Hon) as [Hld Hm].
    rewrite <- Hset in Hcl, Hq, Hin.
    exact (lhB_claim_sel (mf_shortcut_sel MFh) (mf_shortcut_sel_ref MFh) Hprobe (c3_set k1) tbl (c3_par k1) (c3_dict k1) ad x cap r out
             h q dd dm Hinv Hcl Hld Hdq Hd2 Hm Hbx Hh Ht Hfc Hq Hin Hdm (H2 Hon)).
Qed.

End CM_LH3Bclaim_1.
