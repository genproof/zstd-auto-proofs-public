(* FS3 streaming (a copy of read/R3RingNew.v): the stream buffer (buffered mode) after a unit of a Zstandard frame
   written at outStart: the ring relation and the history of the new state (v2 StreamSeg_read.v ring_new /
   hist_new / hist_after_write, with the dictionary extDict and a history H in front of the frame). *)
Require Export Zstd.proof.dec.v3.FS.stream.load.L3BfRing.
Local Open Scope logic.

Section CM_L3BfRingNew_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* the history zstd sees at d, then cnt written at d with the cells outside [d, hi) unchanged and an in-array
   extDict beyond hi: the history at d + |cnt| *)
Lemma hist_after_write3 : forall (oc oc': list val) d ps e (H content cnt: list Z) ws hi,
  Zlength oc' = Zlength oc -> 0 <= ps <= d -> 0 <= ext_len e ->
  hist_view oc d ps e H content ws ->
  (forall k, d - ps < k -> k <= Zlength H + Zlength content -> k <= ws + Zlength H ->
     match e with ExtIn e1 _ => e1 - (k - (d - ps)) >= hi | _ => True end) ->
  unchanged_outside oc oc' d hi ->
  sublist d (d + Zlength cnt) oc' = zbytes cnt ->
  hist_view oc' (d + Zlength cnt) ps e H (content ++ cnt) ws.
Proof.
intros oc oc' d ps e H content cnt ws hi Hlen Hps He0 Hv Hext Hun Hsub.
assert (Hc0 := Zlength_nonneg cnt). assert (Hn0 := Zlength_nonneg content). assert (HH0 := Zlength_nonneg H).
assert (Hdl: 0 < Zlength cnt -> d + Zlength cnt <= Zlength oc').
{ intros. apply (f_equal (@Zlength val)) in Hsub. rewrite Zlength_map, Zlength_sublist2 in Hsub. lia. }
unfold hist_view in *. intros k Hk. rewrite app_assoc, Zlength_app in Hk |- *. rewrite Zlength_app in *.
destruct (Z_le_gt_dec k (Zlength cnt)) as [Hkc|Hkc].
- specialize (Hdl ltac:(lia)). split; [lia|]. unfold chist.
  rewrite (proj2 (Z.leb_le k (d + Zlength cnt - ps))) by lia.
  replace (Znth (d + Zlength cnt - k) oc') with (Znth (Zlength cnt - k) (sublist d (d + Zlength cnt) oc'))
    by (rewrite Znth_sublist by lia; f_equal; lia).
  rewrite Hsub. erewrite Znth_map by lia. f_equal. f_equal.
  rewrite byte_at_app_r by (rewrite ?Zlength_app; lia). rewrite Zlength_app.
  unfold byte_at, Znth. destruct (Z_lt_dec (Zlength cnt - k) 0); [lia|]. f_equal. f_equal. lia.
- set (k' := k - Zlength cnt).
  destruct (Hv k') as [Hb Hval]; [unfold k'; rewrite ?Zlength_app; lia|].
  split; [unfold k' in Hb; lia|].
  assert (Hbyte: byte_at ((H ++ content) ++ cnt) (Zlength H + Zlength content + Zlength cnt - k) =
                 byte_at (H ++ content) (Zlength (H ++ content) - k')).
  { unfold byte_at, k'. rewrite app_nth1 by (rewrite <- ZtoNat_Zlength, ?Zlength_app; lia).
    rewrite Zlength_app. f_equal. f_equal. lia. }
  rewrite Hbyte. rewrite Zlength_app. rewrite <- Hval. unfold chist in Hval |- *.
  destruct (Z_le_gt_dec k (d + Zlength cnt - ps)) as [Hin|Hout].
  + rewrite (proj2 (Z.leb_le k (d + Zlength cnt - ps))) by lia.
    rewrite (proj2 (Z.leb_le k' (d - ps))) by (unfold k'; lia).
    rewrite (proj2 (Z.leb_le k' (d - ps))) in Hval by (unfold k'; lia).
    replace (d + Zlength cnt - k) with (d - k') by (unfold k'; lia).
    destruct (Z_lt_dec (d - k') (Zlength oc)) as [Hi|Hi].
    * destruct (Z_lt_dec (d - k') 0) as [Hn|Hn]; [rewrite Znth_underflow in Hval by lia; discriminate|].
      apply Hun; unfold k'; lia.
    * rewrite Znth_overflow in Hval by lia. discriminate.
  + rewrite (proj2 (Z.leb_gt k (d + Zlength cnt - ps))) by lia.
    rewrite (proj2 (Z.leb_gt k' (d - ps))) by (unfold k'; lia).
    rewrite (proj2 (Z.leb_gt k' (d - ps))) in Hval by (unfold k'; lia).
    replace (k - (d + Zlength cnt - ps)) with (k' - (d - ps)) by (unfold k'; lia).
    destruct e as [|e1 elen|sh eb en ec e1 elen]; auto.
    specialize (Hext k' ltac:(unfold k'; lia) ltac:(unfold k'; lia) ltac:(unfold k'; lia)).
    destruct (Z_lt_dec (e1 - (k' - (d - ps))) (Zlength oc)) as [Hi|Hi].
    * destruct (Z_lt_dec (e1 - (k' - (d - ps))) 0) as [Hn|Hn].
      { rewrite Znth_underflow in Hval by lia. discriminate. }
      apply Hun; lia.
    * rewrite Znth_overflow in Hval by lia. discriminate.
Qed.

(* the shape of the extDict of the ring's segment *)
Lemma seg_shape : forall obuf sout s hdr z b ps pe e dd W,
  c_ring false obuf sout s (FP_zstd hdr z) nil (HL_seg b ps pe e) ->
  lay_dd (HL_seg b ps pe e) dd -> dd_bf W dd ->
  ext_shape e (sf_outSize s) (fh_windowSize (zp_h z)) (zp_bsm z) (zp_out z).
Proof.
intros obuf sout s hdr z b ps pe e dd W Hr Hld Hdf.
destruct Hr as (_&_&_&os&oe&_&_&_&Hr). cbv beta iota zeta in Hr.
destruct Hr as (_&_&_&_&Hl). destruct Hl as (_&_&_&_&Hroom&_). cbn [lay_room fp_content fp_ws fp_bsm] in Hroom.
destruct e as [|e1 elen|sh eb en ec e1 elen]; [left; reflexivity| |].
- destruct Hroom as (->&_&Hr1&Hr2). right; left. exists e1. auto.
- cbn [lay_dd] in Hld. destruct Hld as (-> & -> & -> & -> & gp & x & Edd & -> & _ & Hbx & _).
  rewrite Edd in Hdf. destruct Hdf as (_&Hlen&_).
  right; right. exists eb, (dx_bytes x). split; [reflexivity|auto].
Qed.

Lemma ring_new3 : forall obuf sout s hdr z z' l dd W ostart rr (oc': list val) cnt stage' (body: bool),
  c_ring false obuf sout s (FP_zstd hdr z) nil l ->
  lay_dd l dd -> dd_model dd (zp_dm z) -> dd_bf W dd -> lay_cbound (FP_zstd hdr z) l ->
  sf_outStart s = vlong ostart -> sf_outEnd s = vlong ostart -> 0 <= ostart <= sf_outSize s ->
  sf_outSize s <= 2 ^ 32 ->
  0 <= fh_windowSize (zp_h z) -> fh_blockSizeMax (zp_h z) = Z.min (fh_windowSize (zp_h z)) ZSTD_BLOCKSIZE_MAX ->
  0 <= zp_bsm z <= fh_blockSizeMax (zp_h z) ->
  zp_h z' = zp_h z -> zp_bsm z' = zp_bsm z -> zp_out z' = zp_out z ++ cnt ->
  Zlength (sf_ring s) = sf_inSize s + sf_outSize s -> Zlength oc' = sf_outSize s ->
  rr = Zlength cnt -> Zlength cnt <= zp_bsm z -> ostart + rr <= sf_outSize s ->
  sublist ostart (ostart + rr) oc' = zbytes cnt ->
  (body = false -> rr = 0) ->
  byte_cells oc' ->
  c_ring false obuf sout (sf_cont s stage' (vlong (ostart + rr)) (sublist 0 (sf_inSize s) (sf_ring s) ++ oc'))
    (FP_zstd hdr z') cnt
    (if body then lwrite (lmove l (sf_outBuff s) ostart (sf_outSize s - ostart)) (sf_outBuff s) ostart rr
     else lmove l (sf_outBuff s) ostart (sf_outSize s - ostart)) /\
  lay_cbound (FP_zstd hdr z')
    (if body then lwrite (lmove l (sf_outBuff s) ostart (sf_outSize s - ostart)) (sf_outBuff s) ostart rr
     else lmove l (sf_outBuff s) ostart (sf_outSize s - ostart)).
Proof.
intros obuf sout s hdr z z' l dd W ostart rr oc' cnt stage' body Hr Hld Hdm Hdf Hcb Hos Hoe Hor HN Hws Hbsm Hb0
  Hzh Hzb Hzo Hlr Hlo Hrr Hcl Hend Hsub Hbody Hbc.
pose proof Hr as Hr0. assert (Hc0 := Zlength_nonneg cnt).
destruct Hr as (Hib&Hipt&Hisz&os&oe&Hos'&Hoe'&Hoo&Hr). cbv beta iota zeta in Hr.
destruct Hr as (Hoeb&_&_&Hrn&Hl).
assert (oe = ostart) by (rewrite Hoe in Hoe'; apply vlong_eq_range in Hoe'; lia). subst oe.
assert (os = ostart) by (rewrite Hos in Hos'; apply vlong_eq_range in Hos'; lia). subst os.
assert (HI: 0 <= sf_inSize s) by (cbn [fp_bsm] in Hisz; lia).
unfold c_ring, lay_cbound. cbn [sf_cont sf_inBuff sf_inSize sf_outStart sf_outEnd sf_outSize sf_ring sf_outBuff
  fp_bsm fp_content fp_fcs fp_ws]. cbn [fp_bsm fp_content fp_fcs fp_ws] in Hisz, Hl, Hrn.
rewrite Hzh, Hzo, Hzb.
fold (ring_cells s) in Hl.
assert (Hcells: sublist (sf_inSize s) (sf_inSize s + sf_outSize s) (sublist 0 (sf_inSize s) (sf_ring s) ++ oc') = oc')
  by (apply ring_out_cells; lia).
assert (Hcells': forall j, 0 <= j <= sf_outSize s -> hist_def oc' j 0 ExtNone).
{ intros j Hj. apply (hist_def_bytes3 _ _ _ (sf_outSize s) 0 0 nil); auto; try lia. left; reflexivity. }
destruct (Z_lt_ge_dec 0 (sf_outSize s - ostart)) as [Hcap|Hcap].
- destruct (moved3 _ _ _ _ _ _ _ _ ostart Hr0 Hld Hdm Hdf Hcb Hos Hoe Hor HN Hws Hbsm Hb0 Hcap)
    as (eM&El1&Hsh&Hfc&Hrm&Hob&_).
  rewrite El1.
  assert (El2: (if body then lwrite (HL_seg (sf_outBuff s) 0 ostart eM) (sf_outBuff s) ostart rr
                else HL_seg (sf_outBuff s) 0 ostart eM) = HL_seg (sf_outBuff s) 0 (ostart + rr) eM).
  { destruct body; cbn [lwrite]; [reflexivity|]. rewrite (Hbody eq_refl), Z.add_0_r. reflexivity. }
  rewrite El2.
  split.
  + split; [exact Hib|]. split; [exact Hipt|]. split; [exact Hisz|].
    exists ostart, (ostart + rr). split; [exact Hos|]. split; [reflexivity|]. split; [lia|].
    cbv beta iota zeta. rewrite Hcells.
    split; [lia|]. split; [exact Hsub|]. split; [lia|]. split; [exact Hrn|].
    split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [rewrite Zlength_app; lia|].
    split.
    { cbn [lay_room]. destruct Hsh as [->|[(e1&->&He1)|(eb&b&->&_)]]; auto.
      rewrite Zlength_app. repeat split; lia. }
    split; [apply (hist_def_bytes3 _ _ _ (sf_outSize s) (fh_windowSize (zp_h z)) (zp_bsm z) (zp_out z)); auto; lia|].
    split; [exists (zp_out z); reflexivity|].
    split; [left; reflexivity|].
    split; [intros Hx; destruct (Hfc Hx) as [Hx1 Hx2]; split; [exact Hx1|rewrite Zlength_app; lia]|].
    intros Hx; rewrite Hx in Hrm; lia.
  + intros b' ps' pe' e' E. inversion E; subst. rewrite Zlength_app. lia.
- assert (Hr0z: rr = 0) by lia. assert (cnt = nil) by (apply Zlength_nil_inv; lia). subst cnt rr.
  rewrite ?Zlength_nil, ?Z.add_0_r, ?app_nil_r in *. rewrite ?Zlength_nil, ?Z.add_0_r, ?app_nil_r.
  assert (El1: lmove l (sf_outBuff s) ostart (sf_outSize s - ostart) = l)
    by (unfold lmove; rewrite (proj2 (Z.leb_le _ 0)) by lia; reflexivity).
  rewrite El1.
  destruct l as [|eb ec gp|b pe od|b ps pe e].
  + destruct Hl as (Hc&->&_). assert (HN0: sf_outSize s = 0) by lia.
    destruct body; cbn [lwrite]; (split; [|intros ? ? ? ? E; discriminate E]);
    (split; [exact Hib|]); (split; [exact Hipt|]); (split; [exact Hisz|]);
    exists 0, 0; (split; [exact Hos|]); (split; [reflexivity|]); (split; [lia|]); cbv beta iota zeta;
    rewrite Hcells, ?sublist_nil; repeat split; auto; try lia; rewrite ?Zlength_nil; lia.
  + destruct Hl as (Hc&->&_). assert (HN0: sf_outSize s = 0) by lia.
    destruct body; cbn [lwrite]; (split; [|intros ? ? ? ? E; discriminate E]);
    (split; [exact Hib|]); (split; [exact Hipt|]); (split; [exact Hisz|]);
    exists 0, 0; (split; [exact Hos|]); (split; [reflexivity|]); (split; [lia|]); cbv beta iota zeta;
    rewrite Hcells, ?sublist_nil; repeat split; auto; try lia; rewrite ?Zlength_nil; lia.
  + destruct Hl as (->&Hc&->&->&_&HN0).
    destruct body; cbn [lwrite]; (split; [|intros ? ? ? ? E; discriminate E]);
    (split; [exact Hib|]); (split; [exact Hipt|]); (split; [exact Hisz|]);
    exists 0, 0; (split; [exact Hos|]); (split; [reflexivity|]); (split; [lia|]); cbv beta iota zeta;
    rewrite Hcells, ?sublist_nil; repeat split; auto; try lia; rewrite ?Zlength_nil; lia.
  + pose proof (seg_shape _ _ _ _ _ _ _ _ _ _ _ Hr0 Hld Hdf) as Hsh.
    destruct Hl as (->&->&Hpe&Hpc&Hroom&Hhd&_&Hw&Hfc&Hrm). specialize (Hrm eq_refl).
    assert (Hpe2: pe = ostart).
    { destruct Hw as [Hw|(Ho0&_&_&Hlt1&Hlt2)]; [lia|].
      exfalso. unfold ring_needed, ZSTD_WINDOWSIZE_ABSMIN, WILDCOPY_OVERLENGTH, ZSTD_BLOCKSIZE_MAX in *. lia. }
    subst pe.
    assert (El2: (if body then lwrite (HL_seg (sf_outBuff s) 0 ostart e) (sf_outBuff s) ostart 0
                  else HL_seg (sf_outBuff s) 0 ostart e) = HL_seg (sf_outBuff s) 0 ostart e)
      by (destruct body; cbn [lwrite]; rewrite ?Z.add_0_r; reflexivity).
    rewrite El2.
    split; [|exact Hcb].
    split; [exact Hib|]. split; [exact Hipt|]. split; [exact Hisz|].
    exists ostart, ostart. split; [exact Hos|]. split; [reflexivity|]. split; [lia|].
    cbv beta iota zeta. rewrite Hcells, sublist_nil.
    split; [lia|]. split; [reflexivity|]. split; [rewrite ?Zlength_nil; lia|]. split; [exact Hrn|].
    split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [exact Hpc|].
    split; [exact Hroom|].
    split; [apply (hist_def_bytes3 _ _ _ (sf_outSize s) (fh_windowSize (zp_h z)) (zp_bsm z) (zp_out z)); auto; lia|].
    split; [exists (zp_out z); rewrite app_nil_r; reflexivity|].
    split; [left; reflexivity|].
    split; [exact Hfc|].
    intros _; exact Hrm.
Qed.

Lemma hist_for_dm : forall e z z', zp_dm z' = zp_dm z -> hist_for e z' = hist_for e z.
Proof. intros e z z' H. destruct e; cbn [hist_for]; unfold zp_hist; rewrite ?H; reflexivity. Qed.

(* the history of the new state (hist_ok) after a unit written at outStart *)
Lemma hist_new3 : forall obuf sout s hdr z z' l dd W ostart rr (oc': list val) cnt (body: bool),
  c_ring false obuf sout s (FP_zstd hdr z) nil l ->
  lay_dd l dd -> dd_model dd (zp_dm z) -> dd_bf W dd -> lay_cbound (FP_zstd hdr z) l ->
  sf_outStart s = vlong ostart -> sf_outEnd s = vlong ostart -> 0 <= ostart <= sf_outSize s ->
  sf_outSize s <= 2 ^ 32 ->
  0 <= fh_windowSize (zp_h z) -> fh_blockSizeMax (zp_h z) = Z.min (fh_windowSize (zp_h z)) ZSTD_BLOCKSIZE_MAX ->
  0 <= zp_bsm z <= fh_blockSizeMax (zp_h z) ->
  zp_dm z' = zp_dm z ->
  Zlength (sf_ring s) = sf_inSize s + sf_outSize s -> 0 <= sf_inSize s -> Zlength oc' = sf_outSize s ->
  rr = Zlength cnt -> sublist ostart (ostart + rr) oc' = zbytes cnt -> (body = false -> rr = 0) ->
  unchanged_outside (ring_cells s) oc' ostart
    (ostart + Z.min (sf_outSize s - ostart) (zp_bsm z + WILDCOPY_OVERLENGTH)) ->
  old_hist (ring_cells s) l z ->
  match (if body then lwrite (lmove l (sf_outBuff s) ostart (sf_outSize s - ostart)) (sf_outBuff s) ostart rr
         else lmove l (sf_outBuff s) ostart (sf_outSize s - ostart)) with
  | HL_seg _ ps pe e => hist_view oc' pe ps e (hist_for e z') (zp_out z ++ cnt) (fh_windowSize (zp_h z))
  | _ => True end.
Proof.
intros obuf sout s hdr z z' l dd W ostart rr oc' cnt body Hr Hld Hdm Hdf Hcb Hos Hoe Hor HN Hws Hbsm Hb0 Hzd
  Hlr HI Hlo Hrr Hsub Hbody Hun Hold.
assert (Hc0 := Zlength_nonneg cnt).
assert (Hlc: Zlength oc' = Zlength (ring_cells s)) by (unfold ring_cells; rewrite Zlength_sublist by lia; lia).
destruct (Z_lt_ge_dec 0 (sf_outSize s - ostart)) as [Hcap|Hcap].
- destruct (moved3 _ _ _ _ _ _ _ _ ostart Hr Hld Hdm Hdf Hcb Hos Hoe Hor HN Hws Hbsm Hb0 Hcap)
    as (eM&El1&Hsh&_&_&_&Hhf&Hmv).
  specialize (Hmv Hold). rewrite El1.
  assert (G: hist_view oc' (ostart + Zlength cnt) 0 eM (hist_for eM z) (zp_out z ++ cnt) (fh_windowSize (zp_h z))).
  { apply (hist_after_write3 (ring_cells s) oc' ostart 0 eM (hist_for eM z) (zp_out z) cnt _
             (ostart + Z.min (sf_outSize s - ostart) (zp_bsm z + WILDCOPY_OVERLENGTH))); auto; try lia.
    - destruct Hsh as [->|[(e1&->&He1)|(eb&b&->&_)]]; cbn [ext_len]; rewrite ?Zlength_map;
        unfold WILDCOPY_OVERLENGTH in *; first [lia | apply Zlength_nonneg].
    - intros kk Hk1 Hk2 Hk3. destruct Hsh as [->|[(e1&->&He1)|(eb&b&->&_)]]; auto.
      cbn [hist_for] in Hk2, Hk3. rewrite Zlength_nil in Hk2, Hk3. unfold WILDCOPY_OVERLENGTH in *. lia.
    - rewrite <- Hrr. exact Hsub. }
  destruct body; cbn [lwrite]; rewrite (hist_for_dm _ z z' Hzd).
  + rewrite Hrr. exact G.
  + rewrite (Hbody eq_refl) in Hrr. assert (cnt = nil) by (apply Zlength_nil_inv; lia). subst cnt.
    rewrite Zlength_nil, Z.add_0_r in G. exact G.
- assert (rr = 0).
  { subst rr. destruct (Z.eq_dec (Zlength cnt) 0); auto.
    apply (f_equal (@Zlength val)) in Hsub. rewrite Zlength_map, Zlength_sublist2 in Hsub. lia. }
  assert (cnt = nil) by (apply Zlength_nil_inv; lia). subst cnt rr.
  assert (El1: lmove l (sf_outBuff s) ostart (sf_outSize s - ostart) = l)
    by (unfold lmove; rewrite (proj2 (Z.leb_le _ 0)) by lia; reflexivity).
  rewrite El1.
  destruct l as [| | |b ps pe e]; [destruct body; exact I ..|].
  pose proof (seg_shape _ _ _ _ _ _ _ _ _ _ _ Hr Hld Hdf) as Hsh.
  rewrite ?Zlength_nil in *.
  destruct Hr as (_&_&_&os&oe&Hos'&Hoe'&Hoo&Hr). cbv beta iota zeta in Hr.
  destruct Hr as (Hoeb&_&_&Hrn&Hl).
  assert (oe = ostart) by (rewrite Hoe in Hoe'; apply vlong_eq_range in Hoe'; lia). subst oe.
  assert (os = ostart) by (rewrite Hos in Hos'; apply vlong_eq_range in Hos'; lia). subst os.
  destruct Hl as (->&->&Hpe&_&_&_&_&Hw&_).
  assert (Hpe2: pe = ostart).
  { destruct Hw as [Hw|(Ho0&_&_&Hlt1&Hlt2)]; [lia|].
    exfalso. cbn [fp_fcs fp_bsm] in *. unfold ring_needed, ZSTD_WINDOWSIZE_ABSMIN, WILDCOPY_OVERLENGTH, ZSTD_BLOCKSIZE_MAX in *. lia. }
  subst pe. cbn [old_hist] in Hold.
  assert (G: hist_view oc' (ostart + Zlength (@nil Z)) 0 e (hist_for e z) (zp_out z ++ nil) (fh_windowSize (zp_h z))).
  { apply (hist_after_write3 (ring_cells s) oc' ostart 0 e (hist_for e z) (zp_out z) nil _
             (ostart + Z.min (sf_outSize s - ostart) (zp_bsm z + WILDCOPY_OVERLENGTH))); auto; try lia.
    - destruct Hsh as [->|[(e1&->&He1)|(eb&b&->&_)]]; cbn [ext_len]; rewrite ?Zlength_map;
        unfold WILDCOPY_OVERLENGTH in *; first [lia | apply Zlength_nonneg].
    - intros kk Hk1 Hk2 Hk3. destruct Hsh as [->|[(e1&->&He1)|(eb&b&->&_)]]; auto.
      cbn [hist_for] in Hk2, Hk3. rewrite Zlength_nil in Hk2, Hk3. unfold WILDCOPY_OVERLENGTH in *. lia.
    }
  rewrite Zlength_nil, Z.add_0_r in G.
  destruct body; cbn [lwrite]; rewrite (hist_for_dm _ z z' Hzd); rewrite ?Z.add_0_r; exact G.
Qed.

End CM_L3BfRingNew_1.
