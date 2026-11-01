(* FS3 one-shot: shared helpers, ZSTD_decompress_usingDDict (internal) and ZSTD_decompress_usingDict *)
Require Import Zstd.proof.dec.v3.FS.FSOblig3.
Local Open Scope logic.

Section CM_O3Base_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma hset_rep_nil (am: option cmem) (sp: val) (hb: Z) :
  hset_rep am sp nil hb = !! (sp = nullval /\ hb = 0) && emp.
Proof.
  unfold hset_rep. destruct (eq_dec sp nullval) as [E | E].
  - apply pred_ext; Intros; entailer!.
  - apply pred_ext; [Intros tp tbl; tauto | Intros; tauto].
Qed.

Lemma sel_on_null (pr: dparams) : sel_on pr nullval = false.
Proof.
  unfold sel_on, veqb. destruct (Val.eq nullval nullval) as [_ | E]; [ | congruence].
  simpl. apply andb_false_r.
Qed.

(* the concrete state after a one-shot decoding outside a stream and a buffer-less frame *)
Lemma base_rel3_with_fs (st: dctx_st) (k: cst3) (fs: fstate) (t: tabs3) :
  base_rel3 st k -> dc_bl st = None -> fp_ok (fs_fParams fs) -> base_rel3 st (c3_with_fs k fs t).
Proof.
  intros (H1 & H2 & H3 & H4 & H5 & Hf & H6 & H7 & Hm) Hb Hfp.
  unfold base_rel3, mem_rel3 in *; simpl.
  split3; auto. split; auto. split; auto. split; auto. split; [exact Hfp |]. split; [exact H6 |].
  split; [intros E; contradiction | exact Hm].
Qed.

(* the memory error is a valid result of any one-shot decoding *)
Lemma oneshot_ok_mem3 md odm s cap out :
  oneshot_ok md odm s cap (err_code ZSTD_error_memory_allocation) out.
Proof.
  assert (He: is_error_code (err_code ZSTD_error_memory_allocation) = true) by reflexivity.
  unfold oneshot_ok. split; [rewrite He; discriminate | ].
  destruct odm as [dm | ]; auto.
  destruct (decode_series_m md sel_none (Some dm) no_wlim s); auto.
  split; [rewrite He; discriminate | intros _; right; reflexivity].
Qed.

Lemma msel_res_off DENT gv p pr sp d l tbl shk a am hb :
  sel_on pr sp = false -> msel_res DENT gv p pr sp d l tbl shk a am hb = emp.
Proof. intros H. unfold msel_res. rewrite H. reflexivity. Qed.

Lemma darg_res3_off DENT gv pr sp d a :
  sel_on pr sp = false -> darg_res3 DENT gv pr sp d a = darg_res DENT gv a.
Proof. intros H. unfold darg_res3. rewrite H. reflexivity. Qed.

(* the streaming fields with streamStage = zdss_init: what ZSTD_decompressMultiFrame leaves (code fix F10) *)
Definition sf_end_stage (s: sfields) : sfields :=
  {| sf_stage := 0; sf_inBuff := sf_inBuff s; sf_inSize := sf_inSize s; sf_inPos := sf_inPos s;
     sf_outBuff := sf_outBuff s; sf_outSize := sf_outSize s; sf_outStart := sf_outStart s;
     sf_outEnd := sf_outEnd s; sf_lhSize := sf_lhSize s; sf_hostage := sf_hostage s; sf_nfp := sf_nfp s;
     sf_expOut := sf_expOut s; sf_hbuf := sf_hbuf s; sf_over := sf_over s; sf_ring := sf_ring s; sf_mem := sf_mem s; sf_held := sf_held s |}.

Lemma sf_end_stage_init (s: sfields) : sf_stage s = 0 -> sf_end_stage s = s.
Proof. destruct s; simpl; intros ->; reflexivity. Qed.

(* the one-shot functions take streamStage out of the streaming fields and give it back as zdss_init *)
Lemma sgroup_take_stage (p: val) (s: sfields) :
  sgroup p s |-- field_at_ Ews t_dctx (DOT _streamStage) p *
    (field_at Ews t_dctx (DOT _streamStage) (Vint (Int.repr 0)) p -* sgroup p (sf_end_stage s)).
Proof.
  unfold sgroup. Intros. rewrite !sepcon_assoc.
  apply sepcon_derives.
  - cancel.
  - rewrite <- wand_sepcon_adjoint. unfold sf_end_stage, sf_given; simpl. entailer!.
Qed.

Section Oneshot.
Variable DENT : dent_pred.
Variable TABS : tabs_pred.
Variable SR : srel3.
Variable BR : blrel.

Lemma body_usingDDict_int3 :
  body_ok (FS3_G DENT TABS SR BR) (ZSTD_decompress_usingDDict_int_spec3 DENT TABS).
Proof.
  exists f_ZSTD_decompress_usingDDict; split; [reflexivity | split; [reflexivity | ]].
  start_function.
  forward_call (W, gv, p, fs, tabs, pr, sp, d, l, tbl, shk, shd, dst, cap, shs, src, s, a, am, hb).
  { destruct a; simpl in *; try contradiction; entailer!. }
  Intros vret. destruct vret as [[[[r out] fs'] d'] lxb']. simpl fst in *; simpl snd in *.
  forward.
  Exists r out fs' d' lxb'. entailer!.
Qed.

End Oneshot.

(* ---------- the internal specifications imply the API ones ---------- *)

(* a live DDict can be freed: its allocator's blocks, the struct and the copy (if any) *)
Lemma ddict_rep_at_any3 DENT : DENT_OK DENT -> forall gv x buf,
  ddict_rep_at DENT gv x buf |--
  ddict_any3 (dx_mem x) (dx_q x) (if ddx_copied x then Zlength (dx_bytes x) else 0).
Proof.
  intros HDENT gv x buf.
  unfold ddict_rep_at, ddict_any3, ddict_failed3, ddict_struct, ddict_mem.
  Intros.
  sep_apply (HDENT gv (dx_q x) (ddx_ent x)).
  Exists (Zlength (dx_bytes x)) (if ddx_copied x then buf else nullval).
  destruct (ddx_copied x) eqn:Hc.
  - match goal with H: isptr buf \/ _ |- _ => apply (ddx_buf_copied x buf Hc) in H end.
    rewrite if_false by (intro Heq; subst buf; contradiction).
    entailer!. destruct (eq_dec buf nullval); [subst; contradiction | cancel].
  - rewrite if_true by auto. entailer!.
Qed.

Lemma freeDDict_sub3 DENT : DENT_OK DENT ->
  funspec_sub (snd ZSTD_freeDDict_int_spec) (snd (ZSTD_freeDDict_spec (DD3x DENT))).
Proof.
  intros HD.
  apply NDsubsume_subsume; [split; reflexivity|].
  split; [split; reflexivity|].
  intros [[gv q] odd] [g args]. simpl.
  set (nb := match odd with Some dd => if ddx_copied (dd_x q dd) then Zlength (dd_bytes dd) else 0 | None => 0 end).
  Exists (gv, q, @None cmem, 0, nb) (@emp mpred _ _). rewrite emp_sepcon. simpl.
  apply andp_right; [apply andp_left2 | apply prop_right; intros rho'; rewrite emp_sepcon; apply andp_left2; auto].
  2: { unfold PROPx, LOCALx, SEPx; simpl. rewrite !sepcon_emp. auto. }
  unfold PROPx, LOCALx, SEPx, PARAMSx, GLOBALSx; simpl. normalize.
  unfold LOCALx, argsassert2assert; simpl. apply andp_right.
  { apply prop_right. split; auto. split; auto. split; auto. intros _ E. exfalso; apply E; reflexivity. }
  apply andp_derives; [auto|].
  apply sepcon_derives; auto. apply sepcon_derives; auto.
  destruct odd as [dd|].
  2:{ subst q. rewrite if_true by auto. auto. }
  unfold DD3x, DD3_of.
  assert_PROP (isptr (dx_q (dd_x q dd))). { unfold ddict_rep_at, ddict_struct. entailer!. }
  rewrite if_false by (simpl in *; destruct q; simpl in *; try contradiction; discriminate).
  sep_apply (ddict_rep_at_any3 DENT HD gv (dd_x q dd) (dd_buf dd)). simpl. subst nb. auto.
Qed.

(* zstd's loading of a dictionary (C-result form) gives the model's claims where the model loads *)
Lemma oneshot_ok_c3 (md: dmode) (b: list Z) ores s cap r out :
  ld_rel b ores -> oneshot_ok md (dict_auto_c b ores) s cap r out -> oneshot_ok md (dict_auto b) s cap r out.
Proof.
  intros HL [H1 H2]. split; auto.
  destruct (dict_auto b) as [dm|] eqn:E; auto.
  rewrite (ld_rel_auto_some _ _ _ HL E) in H2. exact H2.
Qed.

(* an API DDict dd (DD3x) as the dictionary argument DA_ddict (dd_x q dd) (dd_buf dd) sh: the caller's part of its
   memory, the bytes of a DDict by reference; none for a copy or for the DDict without content (dd_xref) *)
Lemma dd_darg_bytes (sh: share) (q: val) (dd: ddict_st) :
  (match dd_ref dd with Some p => isptr p | None => True end) ->
  (match dx_ref (dd_x q dd) with Some p => dd_buf dd = p | None => True end) ->
  (match dd_ref dd with
   | Some p => data_at sh (tarray tuchar (Zlength (dd_bytes dd))) (zbytes (dd_bytes dd)) p
   | None => emp end) =
  (if ddx_copied (dd_x q dd) then emp else bytes_at sh (dx_bytes (dd_x q dd)) (dd_buf dd)).
Proof.
  intros Hrp Hbuf. unfold ddx_copied in *. cbn [dx_ref dx_bytes dd_x] in *.
  destruct (dd_xref_cases dd) as [(p & Hr & Hx) | [(Hr & _ & Hx) | (Hr & Hnb & Hx)]];
    rewrite Hx in *; rewrite Hr in *.
  - rewrite Hbuf, bytes_at_ptr by exact Hrp. reflexivity.
  - reflexivity.
  - rewrite Hbuf, Hnb, bytes_at_null. reflexivity.
Qed.

(* ... and its conditions on the caller's bytes (darg_ok3) from the API's (ddict_buf_ok) *)
Lemma dd_darg_ok3 (W: list ptr_witness) (sh shd: share) (cap: Z) (dst q: val) (dd: ddict_st) :
  (forall p0, dd_ref dd = Some p0 -> readable_share sh /\ dict_ptr_ok W sh (Zlength (dd_bytes dd)) p0 shd cap dst) ->
  (match dx_ref (dd_x q dd) with Some p => dd_buf dd = p | None => True end) ->
  darg_ok3 W (DA_ddict (dd_x q dd) (dd_buf dd) sh) shd cap dst.
Proof.
  intros Hptr Hbuf. simpl. unfold ddx_copied. cbn [dx_ref dx_bytes dd_x] in *. intros Hc Hn.
  destruct (dd_xref_cases dd) as [(p & Hr & Hx) | [(Hr & _ & Hx) | (Hr & _ & Hx)]];
    rewrite Hx in *; [ | discriminate | exfalso; exact (Hn Hbuf)].
  rewrite Hbuf. destruct (Hptr p Hr). split; [assumption | left; assumption].
Qed.

End CM_O3Base_1.
