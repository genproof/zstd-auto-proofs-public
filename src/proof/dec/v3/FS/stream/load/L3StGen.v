(* FS3 streaming: generic facts of a unit decoded in stable mode into the caller's buffer at op
   (the stable ring after a unit, the history zstd sees, c_core at zdss_read, the model after a unit), shared by
   the zdss_load and zdss_read cases; ported from v2 StreamSeg_load.v (lines 796-1316). *)
Require Export Zstd.proof.dec.v3.FS.stream.S3RetStmts Zstd.proof.dec.v3.FS.stream.S3ModelStmts.
Local Open Scope logic.

Section CM_L3StGen_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Definition oa_stable (sh: share) (ob: val) (osz: Z) (fp: fprog) (oc: list val) (opc: Z) : outarr :=
  {| oa_sh := sh; oa_base := ob; oa_N := osz; oa_c := oc; oa_d := opc;
     oa_cap := if is_skip fp then 0 else osz - opc |}.

(* the frame's DDict content is bounded (ddict_struct: at most 2^63-1 bytes; R3Borrow.dd_facts) *)
Definition dd_small (dd: option (ddx * val)) : Prop :=
  forall x buf, dd = Some (x, buf) -> Zlength (dx_bytes x) <= 2 ^ 63 - 1.

(* ---------- zstep ---------- *)

Lemma zstep_h : forall z u cnt ts', zp_h (zstep z u cnt ts') = zp_h z.
Proof.
intros z u cnt ts'. unfold zstep. destruct (zp_ph z); try reflexivity.
- destruct (cblock_size u); [destruct (_ =? 0)|]; reflexivity.
- destruct (_ =? 0); [destruct (match cblock_size bh with Some c => _ | None => false end)|]; reflexivity.
Qed.

Lemma zstep_bsm : forall z u cnt ts', zp_bsm (zstep z u cnt ts') = zp_bsm z.
Proof.
intros z u cnt ts'. unfold zstep. destruct (zp_ph z); try reflexivity.
- destruct (cblock_size u); [destruct (_ =? 0)|]; reflexivity.
- destruct (_ =? 0); [destruct (match cblock_size bh with Some c => _ | None => false end)|]; reflexivity.
Qed.

Lemma zstep_dm : forall z u cnt ts', zp_dm (zstep z u cnt ts') = zp_dm z.
Proof.
intros z u cnt ts'. unfold zstep. destruct (zp_ph z); try reflexivity.
- destruct (cblock_size u); [destruct (_ =? 0)|]; reflexivity.
- destruct (_ =? 0); [destruct (match cblock_size bh with Some c => _ | None => false end)|]; reflexivity.
Qed.

Lemma zstep_out : forall z u cnt ts', cnt_safe z u cnt ts' -> zp_out (zstep z u cnt ts') = zp_out z ++ cnt.
Proof.
intros z u cnt ts'. unfold cnt_safe, zstep. destruct (zp_ph z) as [|bh| |]; intros H.
- destruct H as [-> _]. rewrite app_nil_r. destruct (cblock_size u); [destruct (_ =? 0)|]; reflexivity.
- destruct (bp_type (block_props_of bh) =? 0).
  + destruct H as [-> _]. destruct (match cblock_size bh with Some c => _ | None => false end); reflexivity.
  + reflexivity.
- destruct H as [-> _]. rewrite app_nil_r. reflexivity.
- destruct H as [-> _]. rewrite app_nil_r. reflexivity.
Qed.

(* the unit leaves no loaded bytes (all units but the checksum) *)
Lemma zstep_loaded : forall hdr z u cnt ts' n, unit_ok (FP_zstd hdr z) n -> zp_ph z <> ZP_ck ->
  fp_rawbody (FP_zstd hdr (zstep z u cnt ts')) = true \/ fp_loaded (FP_zstd hdr (zstep z u cnt ts')) = nil.
Proof.
intros hdr z u cnt ts' n Hu Hck. unfold unit_ok in Hu. unfold fp_rawbody, fp_loaded, zstep.
destruct (zp_ph z) as [|bh| |] eqn:Ep.
- destruct Hu as [Hg _]. destruct (cblock_size u); [destruct (_ =? 0)|]; simpl; auto.
- destruct (bp_type (block_props_of bh) =? 0) eqn:E0.
  + destruct (match cblock_size bh with Some c => _ | None => false end); simpl; auto.
  + simpl; auto.
- congruence.
- contradiction.
Qed.

Lemma zstep_ck_complete : forall hdr z u cnt ts', zp_ph z = ZP_ck ->
  fp_complete (FP_zstd hdr (zstep z u cnt ts')) = true.
Proof. intros hdr z u cnt ts' Hp. unfold zstep, fp_complete. rewrite Hp. reflexivity. Qed.

(* ---------- lists ---------- *)

Lemma sublist_app_tail : forall {A} (l c: list A) ps, 0 <= ps <= Zlength l ->
  sublist ps (Zlength l + Zlength c) (l ++ c) = sublist ps (Zlength l) l ++ c.
Proof.
intros A l c ps H. pose proof (Zlength_nonneg c).
rewrite (sublist_split ps (Zlength l) (Zlength l + Zlength c)) by (rewrite ?Zlength_app; lia).
rewrite sublist_app1 by lia. rewrite sublist_app2 by lia.
rewrite Z.sub_diag. replace (Zlength l + Zlength c - Zlength l) with (Zlength c) by lia.
rewrite (sublist_same 0 (Zlength c)); auto.
Qed.

Lemma unch_sublist : forall (oc oc': list val) lo hi i j, unchanged_outside oc oc' lo hi ->
  Zlength oc' = Zlength oc -> 0 <= i <= j -> j <= lo -> j <= Zlength oc -> sublist i j oc' = sublist i j oc.
Proof.
intros oc oc' lo hi i j Hu Hl Hij Hj Hjo.
apply Znth_eq_ext; [rewrite !Zlength_sublist; lia|].
intros x Hx. rewrite Zlength_sublist in Hx by lia. rewrite !Znth_sublist by lia. apply Hu; lia.
Qed.

Lemma sublist_len_bound : forall {A} (l: list A) lo hi, 0 <= lo <= hi -> lo <= Zlength l ->
  Zlength (sublist lo hi l) = hi - lo -> hi <= Zlength l.
Proof.
intros A l lo hi H Hlo Hz. destruct (Z_le_gt_dec hi (Zlength l)); auto. exfalso.
rewrite Zlength_correct in g, Hlo. unfold sublist in Hz. rewrite firstn_all2 in Hz by lia.
rewrite Zlength_correct in Hz. rewrite skipn_length in Hz. lia.
Qed.

(* ---------- the stable ring ---------- *)

(* the stable layout rule of c_ring *)
Definition sring (ob: val) (osz: Z) (sout out: list Z) (l: hlay) : Prop :=
  match l with
  | HL_none => out = nil
  | HL_dict _ _ _ => out = nil
  | HL_stuck base pe _ => base = ob /\ out = nil /\ pe = Zlength sout /\ pe = osz
  | HL_seg base ps pe e =>
      base = ob /\ (match e with ExtIn _ _ => False | _ => True end) /\
      pe = Zlength sout /\ ps = pe - Zlength out /\ sublist ps pe sout = out
  end.

Lemma sring_move : forall ob osz sout out l opc,
  sring ob osz sout out l -> Zlength sout = opc -> opc <= osz ->
  sring ob osz sout out (lmove l ob opc (osz - opc)).
Proof.
intros ob osz sout out l opc H Hl Ho. unfold lmove.
destruct (osz - opc <=? 0) eqn:E; [exact H|]. apply Z.leb_gt in E.
destruct l as [|eb ec gp|b pe od|b ps pe e]; simpl in H |- *.
- subst out. rewrite sublist_nil. repeat split; auto; rewrite ?Zlength_nil; lia.
- subst out. rewrite sublist_nil. repeat split; auto; rewrite ?Zlength_nil; lia.
- lia.
- destruct H as (->&He&->&->&Hs). rewrite (proj2 (Z.eqb_eq _ _) Hl). simpl. auto.
Qed.

Lemma sring_write : forall ob osz sout out l opc cnt,
  sring ob osz sout out l -> Zlength sout = opc -> opc + Zlength cnt <= osz ->
  (forall b ps pe e, l = HL_seg b ps pe e -> 0 <= ps) ->
  sring ob osz (sout ++ cnt) (out ++ cnt) (lwrite (lmove l ob opc (osz - opc)) ob opc (Zlength cnt)).
Proof.
intros ob osz sout out l opc cnt H Hl Ho Hps. pose proof (Zlength_nonneg cnt).
unfold lmove. destruct (osz - opc <=? 0) eqn:E.
- apply Z.leb_le in E. assert (Hc: cnt = nil) by (apply Zlength_nil_inv; lia). subst cnt.
  rewrite !app_nil_r. rewrite Zlength_nil in *.
  destruct l as [|eb ec gp|b pe od|b ps pe e]; simpl in H |- *; rewrite ?Z.add_0_r.
  + subst out. repeat split; auto; lia.
  + subst out. repeat split; auto; lia.
  + destruct H as (->&->&->&->). repeat split; auto; lia.
  + destruct H as (->&He&->&Hps'&Hs). rewrite <- Hl. auto 6.
- apply Z.leb_gt in E.
  destruct l as [|eb ec gp|b pe od|b ps pe e]; simpl in H |- *.
  + subst out. simpl. rewrite Zlength_app. repeat split; auto; try lia.
    rewrite <- Hl. pose proof (Zlength_nonneg sout). rewrite sublist_app2 by lia. rewrite Z.sub_diag.
    replace (Zlength sout + Zlength cnt - Zlength sout) with (Zlength cnt) by lia.
    apply sublist_same; lia.
  + subst out. simpl. rewrite Zlength_app. repeat split; auto; try lia.
    rewrite <- Hl. pose proof (Zlength_nonneg sout). rewrite sublist_app2 by lia. rewrite Z.sub_diag.
    replace (Zlength sout + Zlength cnt - Zlength sout) with (Zlength cnt) by lia.
    apply sublist_same; lia.
  + lia.
  + destruct H as (->&He&->&->&Hs). rewrite (proj2 (Z.eqb_eq _ _) Hl). simpl.
    specialize (Hps _ _ _ _ eq_refl).
    rewrite !Zlength_app. repeat split; auto; try lia.
    rewrite <- Hl. rewrite sublist_app_tail by (pose proof (Zlength_nonneg out); lia).
    rewrite Hs. reflexivity.
Qed.

(* the stable ring after a unit of a Zstandard frame written at opc = |sout| *)
Lemma c_ring_stable_zunit : forall sh ob osz oc sout s hdr z z' l cnt opc fs,
  c_ring true (Some (ob, osz)) sout s (FP_zstd hdr z) nil l -> lay_fields fs l ->
  Zlength sout = opc -> opc + Zlength cnt <= osz ->
  zp_bsm z' = zp_bsm z -> zp_out z' = zp_out z ++ cnt ->
  (match zp_ph z with ZP_body _ => True | _ => cnt = nil end) ->
  c_ring true (Some (ob, osz)) (sout ++ cnt) s (FP_zstd hdr z') nil
    (lnext (FP_zstd hdr z) l (oa_stable sh ob osz (FP_zstd hdr z) oc opc) (Zlength cnt)).
Proof.
intros sh ob osz oc sout s hdr z z' l cnt opc fs Hr Hlf Hl Ho Hh Hout Hc.
destruct Hr as (Hi1&Hi2&Hi3&ostart&oend&Hos&Hoe&Hoo&Hst).
destruct Hst as (Ho0&Ho1&_&ob'&osz'&Hob&Hly). inversion Hob; subst ob' osz'.
assert (Hps: forall b ps pe e, l = HL_seg b ps pe e -> 0 <= ps)
  by (intros; subst l; destruct Hlf as (_&_&?&_); lia).
pose proof (Zlength_nonneg cnt).
split; [auto|]. split; [auto|]. split; [cbn [fp_bsm] in *; rewrite Hh; auto|].
exists ostart, oend. do 3 (split; [auto|]). do 3 (split; [auto|]). exists ob, osz. split; [auto|].
refine (_ : sring ob osz (sout ++ cnt) (fp_content (FP_zstd hdr z')) _).
change (sring ob osz sout (fp_content (FP_zstd hdr z)) l) in Hly.
cbn [fp_content] in *. rewrite Hout.
unfold lnext, oa_stable; cbn [oa_base oa_d oa_cap is_skip].
destruct (zp_ph z).
- subst cnt. rewrite !app_nil_r. apply sring_move; auto. rewrite Zlength_nil in Ho; lia.
- apply sring_write; auto.
- subst cnt. rewrite !app_nil_r. apply sring_move; auto. rewrite Zlength_nil in Ho; lia.
- subst cnt. rewrite !app_nil_r. apply sring_move; auto. rewrite Zlength_nil in Ho; lia.
Qed.

(* c_ring (stable) only reads the stream fields inBuff, inSize, outStart, outEnd, and of the progress its
   Block_Maximum_Size and content *)
Lemma c_ring_stable_eq : forall obuf sout s s' fp fp' pend l,
  c_ring true obuf sout s fp pend l ->
  sf_inBuff s' = sf_inBuff s -> sf_inSize s' = sf_inSize s -> sf_outStart s' = sf_outStart s ->
  sf_outEnd s' = sf_outEnd s -> fp_bsm fp' = fp_bsm fp -> fp_content fp' = fp_content fp ->
  c_ring true obuf sout s' fp' pend l.
Proof.
intros obuf sout s s' fp fp' pend l H H1 H2 H3 H4 H5 H6. unfold c_ring in *.
rewrite H1, H2, H3, H4, H5, H6. exact H.
Qed.

(* c_core at zdss_read, stable mode, from the frame fields and the ring of the new view (generic: any unit
   that leaves the stream at zdss_read with nothing pending and no hostage byte) *)
Lemma c_core_read_stable : forall obuf sout k sv,
  sf_stage (c3_s k) = zdss_read -> sf_hostage (c3_s k) = Vint (Int.repr 0) -> sv_ahead sv = nil ->
  sv_pend sv = nil ->
  sf_inSize (c3_s k) + sf_outSize (c3_s k) <= 2 ^ 32 ->
  sf_inPos (c3_s k) = vlong 0 -> sf_outStart (c3_s k) = sf_outEnd (c3_s k) ->
  c_frame (c3_fs k) (c3_tabs k) (sv_fp sv) (sv_lay sv) (sv_dd sv) ->
  c_ring true obuf sout (c3_s k) (sv_fp sv) nil (sv_lay sv) ->
  (fp_rawbody (sv_fp sv) = true \/ fp_loaded (sv_fp sv) = nil \/ fp_complete (sv_fp sv) = true) ->
  (match sv_fp sv with FP_skip _ got => got = 0 \/ fp_complete (sv_fp sv) = true | _ => True end) ->
  c_core true obuf sout k sv.
Proof.
intros obuf sout k sv Hs Hh Ha Hp Hsz Hip Hoo Hcf Hr Hraw Hsk.
unfold c_core. rewrite Hp.
split; [right; left; auto|].
split; [destruct Hcf as (_&Hc&_); exact Hc|].
split; [exact Hsz|].
rewrite Hs. unfold zdss_read, zdss_init, zdss_loadHeader, zdss_load, zdss_flush. simpl.
split; [left; reflexivity|]. split; [exact Hcf|]. split; [exact Hr|].
split; [intros _; discriminate|]. split; [intros; discriminate|].
split; [intros _; split; [exact Hip|]; split; [tauto|exact Hsk]|].
intros _; auto.
Qed.

(* ---------- the history zstd sees in stable mode ---------- *)

(* a DDict's model content is a suffix of its bytes *)
Lemma ddx_model_suffix : forall x dm, ddx_model x = Some dm -> exists pre, dx_bytes x = pre ++ dm_content dm.
Proof.
intros x dm H. unfold ddx_model in H. destruct (dx_raw x).
- inversion H; subst. exists nil. reflexivity.
- unfold dict_auto_c in H.
  destruct (Zlength (dx_bytes x) <? 8); [inversion H; subst; exists nil; reflexivity|].
  destruct (negb (le_field (dx_bytes x) 0 4 =? ZSTD_MAGIC_DICTIONARY)); [inversion H; subst; exists nil; reflexivity|].
  destruct (dx_ld x) as [[st esize]|]; [|discriminate].
  inversion H; subst. cbn [dm_content]. exists (firstn (Z.to_nat esize) (dx_bytes x)).
  symmetry. apply firstn_skipn.
Qed.

Lemma byte_at_Znth : forall l i, 0 <= i -> byte_at l i = Znth i l.
Proof.
intros l i Hi. unfold byte_at, Znth. destruct (Z_lt_dec i 0); [lia|reflexivity].
Qed.

(* the stable segment: the frame output at [ps, opc) of the delivered bytes; the extDict is nothing (no
   history) or the DDict content (bytes b ending with the history) *)
Definition ext_hist (e: ext_seg) (hist: list Z) : Prop :=
  match e with
  | ExtNone => hist = nil
  | ExtIn _ _ => False
  | ExtSep sh _ en ec e1 elen =>
      readable_share sh /\ en = Zlength ec /\
      exists pre b, ec = zbytes b /\ b = pre ++ hist /\ e1 = Zlength ec /\ elen = Zlength ec
  end.

Lemma hv_stable : forall oc sout out opc ps e hist ws,
  sublist 0 opc oc = zbytes sout -> Zlength sout = opc -> ps = opc - Zlength out ->
  sublist ps opc sout = out -> 0 <= ps -> ext_hist e hist ->
  hist_view oc opc ps e hist out ws.
Proof.
intros oc sout out opc ps e hist ws Hoc Hl Hps Hout Hps0 He.
unfold hist_view. intros k Hk.
assert (Hlo: Zlength (hist ++ out) = Zlength hist + Zlength out) by apply Zlength_app.
pose proof (Zlength_nonneg hist). pose proof (Zlength_nonneg out).
assert (Hk2: k <= Zlength hist + Zlength out) by lia.
assert (Hoc_len: Zlength (sublist 0 opc oc) = opc) by (rewrite Hoc, Zlength_map; lia).
assert (Hocl: opc <= Zlength oc).
{ pose proof (Zlength_nonneg oc). apply (sublist_len_bound oc 0 opc); [lia|lia|rewrite Hoc_len; lia]. }
assert (Hin: forall k, 1 <= k <= Zlength out ->
          Znth (opc - k) oc = Vint (Int.repr (byte_at (hist ++ out) (Zlength (hist ++ out) - k)))).
{ intros k' Hk'.
  replace (Znth (opc - k') oc) with (Znth (opc - k') (sublist 0 opc oc))
    by (rewrite Znth_sublist by lia; f_equal; lia).
  rewrite Hoc. rewrite Znth_map by lia. f_equal. f_equal.
  rewrite byte_at_Znth by lia. rewrite Hlo. rewrite Znth_app2 by lia.
  replace (Zlength hist + Zlength out - k' - Zlength hist) with (Zlength out - k') by lia.
  assert (Hz: forall i, 0 <= i < Zlength out -> Znth i out = Znth (i + ps) sout)
    by (intros i Hi; rewrite <- Hout at 1; rewrite Znth_sublist; [reflexivity | lia | lia]).
  rewrite Hz by lia. f_equal. lia. }
unfold chist.
destruct e as [|e1 elen|sh eb en ec e1 elen]; cbn [ext_hist ext_len] in He |- *.
- subst hist. rewrite Zlength_nil in *.
  split; [lia|]. rewrite (proj2 (Z.leb_le k (opc - ps))) by lia. apply Hin. lia.
- contradiction.
- destruct He as (_ & _ & pre & b & -> & -> & -> & ->).
  pose proof (Zlength_nonneg pre).
  assert (Hlb: Zlength (zbytes (pre ++ hist)) = Zlength pre + Zlength hist)
    by (rewrite Zlength_map, Zlength_app; lia).
  rewrite Hlb.
  split; [lia|].
  destruct (k <=? opc - ps) eqn:Ek.
  + apply Z.leb_le in Ek. apply Hin. lia.
  + apply Z.leb_gt in Ek. rewrite Znth_map by (rewrite Zlength_app; lia).
    f_equal. f_equal. rewrite byte_at_Znth by lia. rewrite Hlo.
    rewrite (Znth_app1 _ _ hist out) by lia. rewrite (Znth_app2 _ _ pre hist) by lia. f_equal. lia.
Qed.

(* the layout facts and the history of a compressed block at op (after checkContinuity's move) *)
Lemma hp_seg : forall oc sout out opc ps e hist ws osz bsm,
  sublist 0 opc oc = zbytes sout -> Zlength sout = opc -> ps = opc - Zlength out ->
  sublist ps opc sout = out -> 0 <= ps -> ext_hist e hist -> ext_len e <= 2 ^ 63 - 1 ->
  layout_ok_seg ps e osz /\ hist_view oc opc ps e hist out ws /\ ext_clear opc ps (osz - opc) bsm e hist out ws.
Proof.
intros oc sout out opc ps e hist ws osz bsm Hoc Hl Hps Hout Hps0 He Hel.
split; [|split; [eapply hv_stable; eauto|]].
- unfold layout_ok_seg. destruct e as [|e1 elen|sh eb en ec e1 elen]; cbn [ext_hist ext_len] in He, Hel |- *.
  + split; [lia|]. split; [lia|]. exact I.
  + contradiction.
  + destruct He as (Hsh & -> & pre & b & Hb & _ & -> & ->).
    pose proof (Zlength_nonneg ec). split; [lia|]. split; [lia|]. repeat split; auto; lia.
- unfold ext_clear. destruct e; cbn [ext_hist] in He; auto. contradiction.
Qed.

Lemma ext_hist_none : forall z, dd_model None (zp_dm z) -> ext_hist ExtNone (zp_hist z).
Proof. intros z H. cbn [dd_model] in H. unfold zp_hist. rewrite H. reflexivity. Qed.

Lemma ext_hist_dd : forall dd z eb ec gp, dd_model dd (zp_dm z) -> dd_pre dd (eb, ec, gp) -> dd_small dd ->
  ext_hist (ExtSep Ews eb (Zlength ec) ec (Zlength ec) (Zlength ec)) (zp_hist z) /\ Zlength ec <= 2 ^ 63 - 1.
Proof.
intros dd z eb ec gp Hm Hp Hs. destruct Hp as (x & -> & -> & _).
cbn [dd_model] in Hm. destruct (ddx_model_suffix _ _ Hm) as [pre Hpre].
split.
- cbn [ext_hist]. split; [apply writable_readable; apply writable_Ews|]. split; [reflexivity|].
  exists pre, (dx_bytes x). split; [reflexivity|]. split; [exact Hpre|]. split; reflexivity.
- rewrite Zlength_map. exact (Hs x eb eq_refl).
Qed.

(* stable mode: the history zstd needs for a compressed block at op, and what it reaches (the dictionary
   content: no ring wrap) *)
Lemma hist_pre_stable : forall sh ob osz oc sout s fs tabs hdr z l dd opc,
  c_ring true (Some (ob, osz)) sout s (FP_zstd hdr z) nil l -> c_frame fs tabs (FP_zstd hdr z) l dd ->
  dd_small dd -> sublist 0 opc oc = zbytes sout -> Zlength sout = opc -> opc <= osz ->
  hist_pre (FP_zstd hdr z) l (oa_stable sh ob osz (FP_zstd hdr z) oc opc) /\
  lay_H z l (oa_stable sh ob osz (FP_zstd hdr z) oc opc) = zp_hist z.
Proof.
intros sh ob osz oc sout s fs tabs hdr z l dd opc Hr Hcf Hdd Hoc Hl Ho.
destruct Hr as (_&_&_&os&oe&_&_&_&Hst). destruct Hst as (_&_&_&ob'&osz'&Hob&Hly).
inversion Hob; subst ob' osz'. clear Hob.
change (sring ob osz sout (zp_out z) l) in Hly.
unfold c_frame in Hcf. cbv zeta in Hcf.
destruct Hcf as (_&_&_&Hlf&Hld&_&_&_&_&Hws&_&_&_&Hdm&_).
pose proof (Zlength_nonneg sout).
unfold hist_pre, lay_H, oa_stable. cbn [oa_base oa_d oa_cap oa_N oa_c is_skip].
destruct l as [|eb ec gp|b pe od|b ps pe e]; cbn [sring] in Hly; cbn [lay_dd] in Hld; cbn [lay_fields] in Hlf;
  unfold lmove; destruct (osz - opc <=? 0) eqn:E;
  try (apply Z.leb_le in E; split; [destruct (zp_ph z); auto; intros _ Hc; lia|]);
  try (apply Z.leb_gt in E).
- reflexivity.
- apply (dd_nodict_model _ _ Hld) in Hdm. split; [|reflexivity]. destruct (zp_ph z); auto. intros _ _.
  split; [reflexivity|]. split; [reflexivity|].
  apply (hp_seg oc sout (zp_out z)); auto; try lia.
  + rewrite Hly, Zlength_nil. lia.
  + rewrite Hly. apply sublist_nil.
  + apply ext_hist_none. exact Hdm.
  + cbn. lia.
- reflexivity.
- destruct (ext_hist_dd _ _ _ _ _ Hdm Hld Hdd) as [Heh Hec].
  split; [|reflexivity]. destruct (zp_ph z); auto. intros _ _.
  split; [reflexivity|]. split; [reflexivity|]. unfold ext_of_dict. cbn [hist_for].
  apply (hp_seg oc sout (zp_out z)); auto; try lia.
  + rewrite Hly, Zlength_nil. lia.
  + rewrite Hly. apply sublist_nil.
- reflexivity.
- destruct Hly as (_ & _ & Hx1 & Hx2). lia.
- destruct Hly as (-> & Hne & -> & -> & Hs). destruct e; [reflexivity|contradiction|reflexivity].
- destruct Hly as (-> & Hne & -> & -> & Hs). rewrite (proj2 (Z.eqb_eq _ _) Hl).
  destruct Hlf as (_ & _ & Hps & _).
  assert (Heh: ext_hist e (hist_for e z) /\ ext_len e <= 2 ^ 63 - 1).
  { destruct e as [|e1 elen|sh' eb en ec e1 elen].
    - split; [apply ext_hist_none; exact (dd_nodict_model _ _ Hld Hdm)|]. cbn. lia.
    - contradiction.
    - destruct Hld as (-> & -> & -> & -> & gp & Hdp).
      destruct (ext_hist_dd _ _ _ _ _ Hdm Hdp Hdd) as [Heh Hec]. split; [exact Heh|]. cbn [ext_len]. lia. }
  destruct Heh as [Heh Hel].
  split; [|destruct e; [reflexivity|contradiction|reflexivity]].
  destruct (zp_ph z); auto. intros _ _.
  split; [reflexivity|]. split; [exact Hl|].
  apply (hp_seg oc sout (zp_out z)); auto; try lia. rewrite <- Hl. exact Hs.
Qed.

(* ---------- the model after a unit ---------- *)

Lemma c_frame_body : forall fs tabs hdr z l dd bh, c_frame fs tabs (FP_zstd hdr z) l dd -> zp_ph z = ZP_body bh ->
  exists c, cblock_size bh = Some c /\ 0 < c <= zp_bsm z /\ Zlength (zp_got z) < c.
Proof.
intros fs tabs hdr z l dd bh H Ep. destruct H as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&Hx&_).
rewrite Ep in Hx. destruct Hx as (_&_&c&Hc&Hb&Hg&_). eauto.
Qed.

(* the unit's bytes loaded before this call belong to the current frame's bytes *)
Lemma cur_rel_unget : forall md sel cd fb hdr z, cur_rel md sel cd fb (FP_zstd hdr z) ->
  match zp_ph z with ZP_body bh => bp_type (block_props_of bh) <> 0 | ZP_end => False | _ => True end ->
  exists fb0, fb = fb0 ++ zp_got z /\ cur_rel md sel cd fb0 (FP_zstd hdr (zp_set_got z nil)).
Proof.
intros md sel cd fb hdr z Hc Hph. unfold cur_rel in *. cbv zeta in *.
cbn [zp_set_got zp_with zp_h zp_dm zp_bsm zp_ign zp_bl zp_ts zp_out zp_ph zp_got] in *.
destruct Hc as (H1&H2&H3&H4&H5&H6&H7&outc&last&Hb&Hfb&Hp).
destruct (zp_ph z) as [|bh| |] eqn:Ep; try contradiction.
- exists (hdr ++ zp_bl z ++ nil). split; [rewrite Hfb, app_nil_r, app_assoc; reflexivity|].
  repeat (split; [assumption|]). exists outc, last. split; [exact Hb|]. split; [reflexivity|].
  destruct Hp as (A&B&_). split; [exact A|]. split; [exact B|]. rewrite Zlength_nil. unfold ZSTD_blockHeaderSize. lia.
- exists (hdr ++ zp_bl z ++ (bh ++ nil)). split; [rewrite Hfb, !app_nil_r, !app_assoc; reflexivity|].
  repeat (split; [assumption|]). exists outc, last. split; [exact Hb|]. split; [reflexivity|].
  destruct Hp as (A&B&c&Hc1&Hc2&Hc3&Hc4). split; [exact A|]. split; [exact B|].
  exists c. split; [exact Hc1|]. split; [exact Hc2|]. split; [rewrite Zlength_nil; lia|].
  rewrite Hc4. destruct (bp_type (block_props_of bh) =? 0) eqn:Eb; [apply Z.eqb_eq in Eb; contradiction|].
  reflexivity.
- exists (hdr ++ zp_bl z ++ nil). split; [rewrite Hfb, app_nil_r, app_assoc; reflexivity|].
  repeat (split; [assumption|]). exists outc, last. split; [exact Hb|]. split; [reflexivity|].
  destruct Hp as (A&B&C&D&_). split; [exact A|]. split; [exact B|]. split; [exact C|]. split; [exact D|].
  rewrite Zlength_nil; lia.
Qed.

(* the model after a unit of a Zstandard frame (generic: sin, sout are the bytes read / delivered before) *)
Lemma model_zunit3 : MF3 -> forall sm cd sin sout hdr z H u cnt ts' fs' tabs' l' dd',
  bytes_ok sin -> bytes_ok u -> dm_ok (zp_dm z) -> zhist_ok sm z H ->
  m_rel_cd sm sin sout (FP_zstd hdr z) nil cd ->
  (match zp_ph z with
   | ZP_body bh => bp_type (block_props_of bh) = 0 \/ zp_got z = nil
   | _ => zp_got z = nil
   end) ->
  unit_ok (FP_zstd hdr z) (Zlength u) -> cnt_safe z u cnt ts' -> cnt_ok z H u cnt ts' -> cont_checks z u cnt ->
  c_frame fs' tabs' (FP_zstd hdr (zstep z u cnt ts')) l' dd' ->
  dead sm (sin ++ u) \/ m_rel_cd sm (sin ++ u) (sout ++ cnt) (FP_zstd hdr (zstep z u cnt ts')) nil cd.
Proof.
intros M sm cd sin sout hdr z H u cnt ts' fs' tabs' l' dd' Hbs Hbu Hdm Hzh Hm Hgot Hun Hsafe Hok Hchk Hcf'.
destruct Hm as (dsin&fb&recs&Hsin&Hser&Hcd&Hcur&Hout). subst sin.
apply Forall_app in Hbs. destruct Hbs as [Hbd Hbf].
assert (Hbc: forall bh c, zp_ph (zstep z u cnt ts') = ZP_body bh -> cblock_size bh = Some c -> c <= zp_bsm z).
{ intros bh c E Ec. destruct (c_frame_body _ _ _ _ _ _ _ Hcf' E) as (c'&Ec'&Hc'&_).
  rewrite zstep_bsm in Hc'. rewrite Ec in Ec'. injection Ec' as <-. lia. }
destruct (mf_zunit_step M sm cd fb hdr z H u cnt ts' Hbf Hdm Hzh Hbc Hcur Hgot Hun Hbu Hsafe Hok Hchk) as [[Hc _]|Hfd].
- right. exists dsin, (fb ++ u), recs. split; [rewrite app_assoc; reflexivity|]. split; [exact Hser|].
  split; [exact Hcd|]. split; [exact Hc|].
  cbn [fp_content] in *. rewrite (zstep_out _ _ _ _ Hsafe). rewrite app_nil_r in *. rewrite Hout, app_assoc.
  reflexivity.
- left. rewrite <- app_assoc. exact (mf_dead_of_fdead M sm cd dsin recs (fb ++ u) Hbd Hser Hcd Hfd).
Qed.

(* ---------- the context's dictionary facts across a unit ---------- *)

Lemma cur_dict_ok_eq : forall st k k' cd, cur_dict_ok st k cd -> c3_dict k' = c3_dict k ->
  fs_fParams (c3_fs k') = fs_fParams (c3_fs k) -> cur_dict_ok st k' cd.
Proof. intros st k k' cd H E1 E2. unfold cur_dict_ok in *. rewrite E1, E2. exact H. Qed.

Lemma c_frame_fparams_z : forall fs tabs hdr z l dd fs' tabs' z' l' dd',
  c_frame fs tabs (FP_zstd hdr z) l dd -> c_frame fs' tabs' (FP_zstd hdr z') l' dd' ->
  zp_h z' = zp_h z -> zp_bsm z' = zp_bsm z -> fs_fParams fs' = fs_fParams fs.
Proof.
intros fs tabs hdr z l dd fs' tabs' z' l' dd' H H' Eh Eb.
destruct H as (_&_&_&_&_&_&Hp&_). destruct H' as (_&_&_&_&_&_&Hp'&_).
rewrite Hp, Hp', Eh, Eb. reflexivity.
Qed.

Lemma c_frame_fparams_s : forall fs tabs hdr g l dd fs' tabs' g' l' dd',
  c_frame fs tabs (FP_skip hdr g) l dd -> c_frame fs' tabs' (FP_skip hdr g') l' dd' ->
  fs_fParams fs' = fs_fParams fs.
Proof.
intros fs tabs hdr g l dd fs' tabs' g' l' dd' H H'.
destruct H as (_&_&_&_&_&_&_&(h&Hh&_&Hp)&_). destruct H' as (_&_&_&_&_&_&_&(h'&Hh'&_&Hp')&_).
rewrite Hh in Hh'. inversion Hh'; subst h'. rewrite Hp, Hp'. reflexivity.
Qed.

End CM_L3StGen_1.
