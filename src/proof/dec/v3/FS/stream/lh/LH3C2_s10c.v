(* FS3 streaming, case zdss_loadHeader, piece C, segment s10: the call
   ZSTD_decodeFrameHeader(zds, zds->headerBuffer, zds->lhSize) on its resources. 
   2026-10-24: the temps renamed after F9. *)
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3C2_s10_g.
Local Open Scope logic.

Section CM_LH3C2_s10c_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma c10_sel_fold_on (DENT: dent_pred) gv p pr sp d l tbl xq am hm : sel_on pr sp = true ->
  mem_mgr gv * dgroup DENT gv p d * cm_have am (hm + local_held d) * hset_tbl am sp l tbl * set_ids l * opt_token xq |--
  sel_res DENT gv p pr sp d l tbl xq am hm.
Proof. intros H. rewrite (c10_sel_on DENT gv p pr sp d l tbl xq am hm H). apply derives_refl. Qed.

Lemma c10_hset_fold (am: option cmem) (sp: val) l hbs tbl : sp <> nullval -> l <> nil ->
  hbs = set_bytes am (Zlength tbl) -> hset_tbl am sp l tbl |-- hset_t am sp l hbs tbl.
Proof. intros H1 H2 H3. rewrite (c10_hset_on am sp l hbs tbl H1). entailer!. Qed.

Lemma c10_dfh_off md d l tbl fs did pcs s r fs' d' :
  dfh_post3 md false d l tbl fs did pcs s r fs' d' -> d' = d.
Proof.
unfold dfh_post3. destruct (get_frame_header_m _ _); try (intros (_ & -> & _); reflexivity).
intros [-> _]. unfold sel_dict. rewrite if_true by auto. reflexivity.
Qed.

(* after the call: the selection's dictionary fields d', with the allocator's count of the local DDict of d'
   (am: the context's allocator, hm: its bytes besides the local DDict, hbs: the set's) *)
Definition c10_Cpost (DENT: dent_pred) (a: dsa) (w1: lw) (c: list val) (hb: list Z) (fs: fstate) (pr: dparams)
    (sp: val) (d: dfields) (l: list (val * ddict_st)) (tbl: list val) (did: Z) (am: option cmem) (hm hbs: Z)
    (TR DR SR FR: mpred) : environ -> mpred :=
  @exp (environ -> mpred) _ Z (fun r => @exp (environ -> mpred) _ fstate (fun fs' =>
  @exp (environ -> mpred) _ dfields (fun d' =>
  PROPx [0 <= r <= Int64.max_unsigned; dfh_post3 (dmode_of pr) (sel_on pr sp) d l tbl fs did 0 hb r fs' d']
  (LOCALx (temp _t'38 (Vlong (Int64.repr r)) :: ds_LI_L a w1)
  (SEPx [field_at Ews t_dctx (DOT _lhSize) (vlong (Zlength hb)) (a_d a);
         field_at Ews t_dctx (DOT _headerBuffer) c (a_d a);
         fcore3 (a_d a) fs' pr sp; TR; zstd_globals (a_gv a); mem_mgr (a_gv a);
         dgroup DENT (a_gv a) (a_d a) d'; hset_t am sp l hbs tbl; cm_have am (hm + local_held d'); DR; SR; FR]))))).

Lemma c10_Lc_core : forall (Espec: OracleKind) DENT TABS BR (a: dsa) (w1: lw) (v38: val) (c: list val)
    (hb: list Z) (fs: fstate) (pr: dparams) (sp: val) (d: dfields) (l: list (val * ddict_st)) (tbl: list val)
    (xq: option (val * val)) (did: Z) (am: option cmem) (hm hbs: Z) (TR DR SR FR: mpred) (P: list Prop)
    (R: ret_assert),
  Zlength c = 18 -> Zlength hb <= 18 -> sublist 0 (Zlength hb) c = zbytes hb -> bytes_ok hb ->
  fs_dictID fs = Vint (Int.repr did) -> 0 <= did <= Int.max_unsigned -> fs_processedCSize fs = Vlong (Int64.repr 0) ->
  sel_mem pr sp d am hm ->
  (sel_on pr sp = true ->
     cur_ok d l xq /\ (DR * SR |-- set_ids l * opt_token xq * (set_ids l * opt_token xq -* DR * SR))) ->
  semax (ds_Delta DENT TABS BR)
    (PROPx P (LOCALx (temp _t'40 v38 :: ds_LI_L a w1)
      (SEPx [field_at Ews t_dctx (DOT _lhSize) (vlong (Zlength hb)) (a_d a);
             field_at Ews t_dctx (DOT _headerBuffer) c (a_d a);
             fcore3 (a_d a) fs pr sp; TR; zstd_globals (a_gv a); mem_mgr (a_gv a);
             dgroup DENT (a_gv a) (a_d a) d; hset_t am sp l hbs tbl; cm_have am (hm + local_held d);
             DR; SR; FR]))) c10_call
    (overridePost (c10_Cpost DENT a w1 c hb fs pr sp d l tbl did am hm hbs TR DR SR FR) R).
Proof.
intros Espec DENT TABS BR a w1 v38 c hb fs pr sp d l tbl xq did am hm hbs TR DR SR FR P R
  Hc Hhb18 Hsub Hbok Hdid Hdidr Hpcs Hmem Hlend.
apply c10_props_pre; intros _.
destruct R as [Rn Rb Rc Rr]. cbv beta iota delta [overridePost]. unfold c10_Cpost.
pose proof (Zlength_nonneg hb) as Hhb0.
unfold ds_Delta. simplify_func_tycontext. unfold c10_call, ds_LI_L. abbreviate_semax.
forward.
assert_PROP (field_compatible t_dctx (DOT _headerBuffer) (a_d a)) as Hfc by entailer!.
rewrite <- c10_hb_eq.
assert (Hw: win_ok Ews 18 c 0 (Zlength hb) hb).
{ unfold win_ok. rewrite Z.add_0_l. repeat split; auto; try lia; auto with share. }
destruct (sel_on pr sp) eqn:Hon.
- destruct (Hlend eq_refl) as [Hcur Hle].
  rewrite (c10_hset_on am sp l hbs tbl (c10_sel_on_t pr sp Hon)). Intros.
  sep_apply Hle.
  sep_apply (c10_sel_fold_on DENT (a_gv a) (a_d a) pr sp d l tbl xq am hm Hon).
  forward_call (a_gv a, a_d a, fs, did, 0, pr, sp, d, l, tbl, xq, Ews,
                field_address t_dctx (DOT _headerBuffer) (a_d a), 18, c, 0, hb, am, hm).
  { entailer!. unfold field_address. rewrite if_true by auto. reflexivity. }
  Intros vret. destruct vret as [[r fs'] d']. cbn [fst snd] in *.
  rewrite Hon in *.
  rewrite (c10_sel_on DENT (a_gv a) (a_d a) pr sp d' l tbl xq am hm Hon). Intros.
  sep_apply (wand_frame_elim (set_ids l * opt_token xq) (DR * SR)).
  match goal with Hl: l <> [] /\ _ |- _ => destruct Hl as [Hl Hbs] | Hl: l <> [] |- _ => idtac end.
  match goal with Hl: l <> [] |- _ =>
    match goal with Hbs: hbs = _ |- _ => sep_apply (c10_hset_fold am sp l hbs tbl (c10_sel_on_t pr sp Hon) Hl Hbs) end end.
  Exists r fs' d'. rewrite c10_hb_eq. entailer!.
- sep_apply (c10_sel_off_intro DENT (a_gv a) (a_d a) pr sp d l tbl xq am hm (mem_mgr (a_gv a)) Hon).
  forward_call (a_gv a, a_d a, fs, did, 0, pr, sp, d, l, tbl, xq, Ews,
                field_address t_dctx (DOT _headerBuffer) (a_d a), 18, c, 0, hb, am, hm).
  { entailer!. unfold field_address. rewrite if_true by auto. reflexivity. }
  { cancel. }
  Intros vret. destruct vret as [[r fs'] d']. cbn [fst snd] in *.
  rewrite Hon in *.
  sep_apply (c10_sel_off_elim DENT (a_gv a) (a_d a) pr sp d' l tbl xq am hm (mem_mgr (a_gv a)) Hon).
  match goal with Hd: dfh_post3 _ false _ _ _ _ _ _ _ _ _ _ |- _ => pose proof (c10_dfh_off _ _ _ _ _ _ _ _ _ _ _ Hd) as Ed end.
  subst d'.
  Exists r fs' d. rewrite c10_hb_eq. entailer!.
Qed.

End CM_LH3C2_s10c_1.
