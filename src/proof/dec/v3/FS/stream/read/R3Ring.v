(* FS3 streaming, case zdss_read: the stream buffer (buffered mode) around a unit decoded at
   outStart: checkContinuity's move, the history zstd sees (v2 StreamSeg_read.v moved / unmoved / hist_pre_ok /
   buf_cap_room / read_cont_hist_buf, with v3's dictionary extDict ExtSep and lay_room's e1 <= |out|). *)
Require Export Zstd.proof.dec.v3.FS.stream.read.R3Pre.
Local Open Scope logic.

Section CM_R3Ring_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Definition ring_cells (s: sfields) : list val := sublist (sf_inSize s) (sf_inSize s + sf_outSize s) (sf_ring s).

(* the extDict after checkContinuity at outStart *)
Definition ext_shape (eM: ext_seg) (N ws bsm: Z) (out: list Z) : Prop :=
  eM = ExtNone \/
  (exists e1, eM = ExtIn e1 e1 /\ ws + bsm + WILDCOPY_OVERLENGTH <= e1 <= N /\ e1 <= Zlength out) \/
  (exists eb b, eM = ExtSep Ews eb (Zlength (zbytes b)) (zbytes b) (Zlength (zbytes b)) (Zlength (zbytes b)) /\
     bytes_ok b /\ Zlength b <= 2 ^ 63 - 1).

(* the ring history before the unit (hist_ok of the read stage) *)
Definition old_hist (ocells: list val) (l: hlay) (z: zprog) : Prop :=
  match l with
  | HL_seg _ ps pe e => hist_view ocells pe ps e (hist_for e z) (zp_out z) (fh_windowSize (zp_h z))
  | _ => True
  end.

Lemma vlong_eq_range : forall x y, 0 <= x <= 2 ^ 32 -> 0 <= y <= 2 ^ 32 -> vlong x = vlong y -> x = y.
Proof. intros. apply lcp_vlong_inj; auto; rep_lia. Qed.

Lemma byte_at_app_r : forall (H out: list Z) j, Zlength H <= j ->
  byte_at (H ++ out) j = byte_at out (j - Zlength H).
Proof.
intros H out j Hj. unfold byte_at. rewrite app_nth2 by (rewrite <- ZtoNat_Zlength; lia).
f_equal. rewrite <- ZtoNat_Zlength. pose proof (Zlength_nonneg H). rewrite <- Z2Nat.inj_sub by lia. reflexivity.
Qed.

(* the history after a wrap (the old segment as the extDict, the dictionary out of reach) *)
Lemma hist_view_wrap : forall ocells pe e H out ws,
  hist_view ocells pe 0 e H out ws -> ws < pe ->
  hist_view ocells 0 0 (ExtIn pe pe) nil out ws.
Proof.
intros ocells pe e H out ws Hv Hw. unfold hist_view in *. intros k Hk. simpl app in Hk |- *.
pose proof (Zlength_nonneg H).
destruct (Hv k) as [_ Hc]; [rewrite Zlength_app; rewrite Zlength_nil in Hk; lia|].
cbn [ext_len]. rewrite Zlength_nil in Hk. split; [lia|].
unfold chist in *. rewrite (proj2 (Z.leb_gt k (0 - 0))) by lia.
rewrite (proj2 (Z.leb_le k (pe - 0))) in Hc by lia.
replace (pe - (k - (0 - 0))) with (pe - k) by lia. rewrite Hc. f_equal. f_equal.
rewrite Zlength_app, byte_at_app_r by lia. f_equal. lia.
Qed.

Lemma moved3 : forall obuf sout s hdr z l dd W ostart,
  c_ring false obuf sout s (FP_zstd hdr z) nil l ->
  lay_dd l dd -> dd_model dd (zp_dm z) -> dd_facts W dd -> lay_cbound (FP_zstd hdr z) l ->
  sf_outStart s = vlong ostart -> sf_outEnd s = vlong ostart -> 0 <= ostart <= sf_outSize s ->
  sf_outSize s <= 2 ^ 32 ->
  0 <= fh_windowSize (zp_h z) -> fh_blockSizeMax (zp_h z) = Z.min (fh_windowSize (zp_h z)) ZSTD_BLOCKSIZE_MAX ->
  0 <= zp_bsm z <= fh_blockSizeMax (zp_h z) ->
  0 < sf_outSize s - ostart ->
  exists eM, lmove l (sf_outBuff s) ostart (sf_outSize s - ostart) = HL_seg (sf_outBuff s) 0 ostart eM /\
    ext_shape eM (sf_outSize s) (fh_windowSize (zp_h z)) (zp_bsm z) (zp_out z) /\
    (fh_contentSize (zp_h z) <= sf_outSize s ->
       (match eM with ExtIn _ _ => False | _ => True end) /\ ostart = Zlength (zp_out z)) /\
    (ostart + zp_bsm z <= sf_outSize s \/ fh_contentSize (zp_h z) <= sf_outSize s) /\
    ostart <= Zlength (zp_out z) /\
    (hist_for eM z = zp_hist z \/ (hist_for eM z = nil /\ fh_windowSize (zp_h z) < Zlength (zp_out z))) /\
    (old_hist (ring_cells s) l z ->
       hist_view (ring_cells s) ostart 0 eM (hist_for eM z) (zp_out z) (fh_windowSize (zp_h z))).
Proof.
intros obuf sout s hdr z l dd W ostart Hr Hld Hdm Hdf Hcb Hos Hoe Hor HN Hws Hbsm Hb0 Hcap.
destruct Hr as (_&_&_&os&oe&Hos'&Hoe'&Hoo&Hr). cbv beta iota zeta in Hr.
destruct Hr as (Hoeb&_&_&Hrn&Hl).
assert (oe = ostart) by (rewrite Hoe in Hoe'; apply vlong_eq_range in Hoe'; lia). subst oe.
assert (os = ostart) by (rewrite Hos in Hos'; apply vlong_eq_range in Hos'; lia). subst os.
cbn [fp_content fp_fcs fp_ws fp_bsm] in Hl.
set (h := zp_h z) in *. set (N := sf_outSize s) in *. set (bsm := zp_bsm z) in *.
assert (Hbig: N < fh_contentSize h -> fh_windowSize h + 2 * bsm + 2 * WILDCOPY_OVERLENGTH <= N)
  by (intros; apply ring_big; auto; lia).
unfold WILDCOPY_OVERLENGTH in *.
assert (Hroom0: N < fh_contentSize h -> bsm <= N) by (intros Hf; specialize (Hbig Hf); lia).
unfold lmove. rewrite (proj2 (Z.leb_gt (N - ostart) 0)) by lia.
destruct l as [|eb ec gp|b pe od|b ps pe e].
- destruct Hl as (Hc&->&_). cbn [lay_dd] in Hld. apply (dd_nodict_model _ _ Hld) in Hdm.
  exists ExtNone. split; [reflexivity|]. split; [left; reflexivity|].
  split; [intros; split; [exact I|rewrite Hc; reflexivity]|].
  split; [destruct (Z_lt_ge_dec N (fh_contentSize h)); [left; specialize (Hroom0 l); lia|right; lia]|].
  split; [rewrite Hc, Zlength_nil; lia|].
  split; [left; reflexivity|].
  intros _. unfold hist_view. cbn [hist_for]. unfold zp_hist. rewrite Hdm, Hc. intros kk Hk. rewrite Zlength_nil in Hk. lia.
- destruct Hl as (Hc&->&_). cbn [lay_dd] in Hld. destruct Hld as (x & Edd & -> & _ & Hbx & _).
  rewrite Edd in Hdm, Hdf. cbn [dd_model] in Hdm. destruct Hdf as (_&Hlen&_).
  exists (ext_of_dict eb (zbytes (dx_bytes x))). split; [reflexivity|].
  split; [right; right; exists eb, (dx_bytes x); split; [reflexivity|auto]|].
  split; [intros; split; [exact I|rewrite Hc; reflexivity]|].
  split; [destruct (Z_lt_ge_dec N (fh_contentSize h)); [left; specialize (Hroom0 l); lia|right; lia]|].
  split; [rewrite Hc, Zlength_nil; lia|].
  split; [left; reflexivity|].
  intros _. rewrite Hc. cbn [hist_for]. unfold zp_hist. apply hist_view_fresh_dict; auto.
- destruct Hl as (_&_&_&_&_&HN0). lia.
- destruct Hl as (->&->&Hpe&Hpc&Hroom&Hhd&_&Hw&Hfc&Hrm). specialize (Hrm eq_refl).
  cbn [lay_room] in Hroom. unfold WILDCOPY_OVERLENGTH in *.
  specialize (Hcb _ _ _ _ eq_refl). cbn [fp_content] in Hcb.
  destruct Hw as [<-|(->&_&_&Hlt1&Hlt2)].
  + rewrite Z.eqb_refl. exists e. split; [reflexivity|].
    split.
    { destruct e as [|e1 elen|sh eb en ec e1 elen]; [left; reflexivity| |].
      - destruct Hroom as (->&_&Hr1&Hr2). right; left. exists e1. split; [reflexivity|]. unfold WILDCOPY_OVERLENGTH. lia.
      - cbn [lay_dd] in Hld. destruct Hld as (-> & -> & -> & -> & gp & x & Edd & -> & _ & Hbx & _).
        rewrite Edd in Hdf. destruct Hdf as (_&Hlen&_).
        right; right. exists eb, (dx_bytes x). split; [reflexivity|auto]. }
    split; [exact Hfc|]. split; [exact Hrm|]. split; [exact Hcb|].
    split.
    { destruct e as [|e1 elen|sh eb en ec e1 elen]; cbn [hist_for]; [left; reflexivity| |left; reflexivity].
      right. split; [reflexivity|]. destruct Hroom as (_&_&Hr1&Hr2). lia. }
    intros Hv. exact Hv.
  + assert (Hpe0: pe <> 0) by (intro; subst pe; specialize (Hbig Hlt1); lia).
    rewrite (proj2 (Z.eqb_neq pe 0)) by auto.
    specialize (Hbig Hlt1).
    exists (ExtIn pe (pe - 0)). split; [reflexivity|].
    split; [right; left; exists pe; rewrite Z.sub_0_r; split; [reflexivity|]; unfold WILDCOPY_OVERLENGTH; lia|].
    split; [intros; lia|]. split; [left; lia|]. split; [lia|].
    split; [right; split; [reflexivity|lia]|].
    intros Hv. cbn [old_hist] in Hv. cbn [hist_for]. rewrite Z.sub_0_r.
    apply (hist_view_wrap _ _ e (hist_for e z)); auto. lia.
Qed.

(* what zstd needs of the history for a compressed block at outStart *)
Lemma hist_pre_buf3 : forall obuf sout s hdr z l dd W ostart,
  c_ring false obuf sout s (FP_zstd hdr z) nil l ->
  lay_dd l dd -> dd_model dd (zp_dm z) -> dd_facts W dd -> lay_cbound (FP_zstd hdr z) l ->
  sf_outStart s = vlong ostart -> sf_outEnd s = vlong ostart -> 0 <= ostart <= sf_outSize s ->
  sf_outSize s <= 2 ^ 32 ->
  0 <= fh_windowSize (zp_h z) -> fh_blockSizeMax (zp_h z) = Z.min (fh_windowSize (zp_h z)) ZSTD_BLOCKSIZE_MAX ->
  0 <= zp_bsm z <= fh_blockSizeMax (zp_h z) ->
  old_hist (ring_cells s) l z ->
  hist_pre (FP_zstd hdr z) l (oa_ring s (FP_zstd hdr z) ostart).
Proof.
intros obuf sout s hdr z l dd W ostart Hr Hld Hdm Hdf Hcb Hos Hoe Hor HN Hws Hbsm Hb0 Hold.
unfold hist_pre. cbn [oa_base oa_d oa_cap oa_N oa_c oa_ring is_skip].
destruct (zp_ph z); auto. intros _ Hcap.
destruct (moved3 _ _ _ _ _ _ _ _ ostart Hr Hld Hdm Hdf Hcb Hos Hoe Hor HN Hws Hbsm Hb0 Hcap)
  as (eM&El1&Hsh&_&_&_&Hhf&Hmv).
rewrite El1. split; [reflexivity|]. split; [reflexivity|].
unfold WILDCOPY_OVERLENGTH in *.
split.
{ unfold layout_ok_seg. destruct Hsh as [->|[(e1&->&He1)|(eb&b&->&_&Hl)]]; cbn [ext_len];
  unfold WILDCOPY_OVERLENGTH in *;
  repeat match goal with |- _ /\ _ => split end; rewrite ?Zlength_map;
  first [apply writable_readable, writable_Ews | apply Zlength_nonneg | lia | auto]. }
split; [exact (Hmv Hold)|].
unfold ext_clear. destruct Hsh as [->|[(e1&->&He1)|(eb&b&->&_)]]; auto.
intros kk Hk. cbn [hist_for] in Hk. simpl app in Hk. rewrite Zlength_nil in Hk. unfold WILDCOPY_OVERLENGTH in *. lia.
Qed.

(* the history zstd's block decoder gets (StreamSpecs lay_H) is the model's, or nothing after a wrap *)
Lemma zhist_buf3 : forall obuf sout s hdr z l dd W ostart sm,
  c_ring false obuf sout s (FP_zstd hdr z) nil l ->
  lay_dd l dd -> dd_model dd (zp_dm z) -> dd_facts W dd -> lay_cbound (FP_zstd hdr z) l ->
  sf_outStart s = vlong ostart -> sf_outEnd s = vlong ostart -> 0 <= ostart <= sf_outSize s ->
  sf_outSize s <= 2 ^ 32 ->
  0 <= fh_windowSize (zp_h z) -> fh_blockSizeMax (zp_h z) = Z.min (fh_windowSize (zp_h z)) ZSTD_BLOCKSIZE_MAX ->
  0 <= zp_bsm z <= fh_blockSizeMax (zp_h z) -> md_dwin (sm_md sm) = true ->
  zhist_ok sm z (lay_H z l (oa_ring s (FP_zstd hdr z) ostart)).
Proof.
intros obuf sout s hdr z l dd W ostart sm Hr Hld Hdm Hdf Hcb Hos Hoe Hor HN Hws Hbsm Hb0 Hdw.
unfold lay_H, zhist_ok. cbn [oa_base oa_d oa_cap oa_N oa_c oa_ring is_skip].
destruct (Z_lt_ge_dec 0 (sf_outSize s - ostart)) as [Hcap|Hcap].
- destruct (moved3 _ _ _ _ _ _ _ _ ostart Hr Hld Hdm Hdf Hcb Hos Hoe Hor HN Hws Hbsm Hb0 Hcap)
    as (eM&El1&_&_&_&_&Hhf&_).
  rewrite El1. destruct Hhf as [E|(E&Hw)]; rewrite E; [left; reflexivity|right; auto].
- unfold lmove. rewrite (proj2 (Z.leb_le _ 0)) by lia.
  destruct l as [| | |b ps pe e]; try (left; reflexivity).
  destruct e as [|e1 elen|]; cbn [hist_for]; try (left; reflexivity).
  right. split; [reflexivity|]. split; [exact Hdw|].
  destruct Hr as (_&_&_&os&oe&_&_&_&Hr). cbv beta iota zeta in Hr.
  destruct Hr as (_&_&_&_&_&_&_&_&Hroom&_). cbn [lay_room fp_content fp_ws fp_bsm] in Hroom.
  destruct Hroom as (_&_&Hr1&Hr2). unfold WILDCOPY_OVERLENGTH in Hr1. lia.
Qed.

(* the ring has room for the unit's content at outStart *)
Lemma buf_cap_room3 : forall obuf sout s hdr z l ostart,
  c_ring false obuf sout s (FP_zstd hdr z) nil l ->
  sf_outStart s = vlong ostart -> sf_outEnd s = vlong ostart -> 0 <= ostart <= sf_outSize s ->
  sf_outSize s <= 2 ^ 32 ->
  0 <= fh_windowSize (zp_h z) -> fh_blockSizeMax (zp_h z) = Z.min (fh_windowSize (zp_h z)) ZSTD_BLOCKSIZE_MAX ->
  0 <= zp_bsm z <= fh_blockSizeMax (zp_h z) ->
  cap_room z (sf_outSize s - ostart).
Proof.
intros obuf sout s hdr z l ostart Hr Hs He Ho Hsz Hws Hbsm Hb0.
assert (Hrn: forall n, n <= 2 ^ 32 -> n >= ring_needed (zp_h z) (zp_bsm z) ->
  zp_bsm z <= n \/ fh_contentSize (zp_h z) <= n).
{ intros n Hn Hge. unfold ring_needed in Hge.
  unfold ZSTD_WINDOWSIZE_ABSMIN, WILDCOPY_OVERLENGTH, ZSTD_BLOCKSIZE_MAX in *. lia. }
assert (Hunk: forall x, x <= 2 ^ 32 -> x <> ZSTD_CONTENTSIZE_UNKNOWN)
  by (intros x Hx; unfold ZSTD_CONTENTSIZE_UNKNOWN; lia).
unfold c_ring in Hr. simpl in Hr.
destruct Hr as [_ [_ [_ [os [oe [Hos [Hoe [Hle Hr]]]]]]]].
destruct Hr as [Hoe2 [_ [_ [Hneed Hl]]]].
rewrite Hs in Hos. rewrite He in Hoe.
apply vlong_eq_range in Hos; [|lia|lia]. apply vlong_eq_range in Hoe; [|lia|lia]. subst os oe.
unfold cap_room.
destruct l as [|eb ec gp|base pe od|base ps pe e].
- destruct Hl as [Hc [H0 _]]. simpl in Hc. rewrite Hc, Zlength_nil. subst ostart.
  destruct (Hrn (sf_outSize s)) as [?|?]; [lia|lia|left; lia|right; split; [apply Hunk|]; lia].
- destruct Hl as [Hc [H0 _]]. simpl in Hc. rewrite Hc, Zlength_nil. subst ostart.
  destruct (Hrn (sf_outSize s)) as [?|?]; [lia|lia|left; lia|right; split; [apply Hunk|]; lia].
- destruct Hl as [_ [Hc [_ [H0 [_ Hz]]]]]. simpl in Hc. rewrite Hc, Zlength_nil. subst ostart.
  destruct (Hrn (sf_outSize s)) as [?|?]; [lia|lia|left; lia|right; split; [apply Hunk|]; lia].
- destruct Hl as [_ [_ [_ [_ [_ [_ [_ [Hend [Hnw Hroom]]]]]]]]]. simpl in Hend, Hnw, Hroom.
  destruct (Hroom eq_refl) as [?|Hf]; [left; lia|].
  destruct (Hnw Hf) as [_ Hpe].
  right. split; [apply Hunk; lia|].
  destruct Hend as [Hend|Hend]; [|lia]. lia.
Qed.

(* the output array of ZSTD_decompressContinueStream, buffered mode *)
Lemma read_pre_buf3 : forall a k sv ipc opc oc1 dl ostart,
  call_inv a k sv ipc opc oc1 dl -> sf_stage (c3_s k) = zdss_read -> dc_stable (a_st a) = false ->
  sf_outStart (c3_s k) = vlong ostart -> 0 <= ostart <= sf_outSize (c3_s k) ->
  Zlength (sf_ring (c3_s k)) = sf_inSize (c3_s k) + sf_outSize (c3_s k) -> 0 <= sf_inSize (c3_s k) ->
  0 <= sf_outSize (c3_s k) ->
  let o := oa_ring (c3_s k) (sv_fp sv) ostart in
  outarr_ok o /\ lay_at (sv_lay sv) o.
Proof.
intros a k sv ipc opc oc1 dl ostart Hi Hs Hst Hos Hor Hlr HnI HnO o.
destruct Hi as (H1&H2&H3&H4&H5&H6&H7&H8&H9&H10&H11&H12&Hcore&_).
rewrite Hst in Hcore.
destruct Hcore as (_&_&Hsz&Hcs). rewrite Hs in Hcs. simpl in Hcs.
destruct Hcs as (_&Hcf&Hring&_).
assert (Hlf: lay_fields (c3_fs k) (sv_lay sv)).
{ destruct (sv_fp sv); unfold c_frame in Hcf; try tauto; destruct Hcf as (_&_&_&Hlf&_); exact Hlf. }
destruct Hring as (_&_&_&os&oe&Hos'&Hoe&Hoo&Hr).
assert (Hwb: 0 <= fp_ws (sv_fp sv) /\ 0 <= fp_bsm (sv_fp sv)).
{ destruct (sv_fp sv); unfold c_frame in Hcf; simpl; try lia; try tauto. }
destruct Hr as (Hoeb&_&_&_&Hl).
rewrite Hos in Hos'. apply vlong_eq_range in Hos'; [|lia|lia]. subst os.
unfold o, oa_ring. clear o. split.
- unfold outarr_ok; simpl. split; [auto|]. rewrite Zlength_sublist by lia.
  repeat split; try lia; destruct (is_skip (sv_fp sv)); lia.
- destruct (sv_lay sv) as [|eb ec gp|b pe od|b ps pe e] eqn:El; simpl; auto.
  + destruct Hl as (->&_&->&->&->&Hz). repeat split; auto. rewrite Hz. destruct (is_skip (sv_fp sv)); lia.
  + destruct Hl as (->&->&Hpe&Hpc&Hroom&_). simpl in Hroom.
    split; [auto|]. split; [|split; [lia|split; [lia|]]].
    { destruct Hlf as (_&_&Hlf&_). lia. }
    destruct e; auto. destruct Hroom as (->&_&He1&_). unfold WILDCOPY_OVERLENGTH in He1. lia.
Qed.

(* the history cells (segment [0, d) of an array of bytes, the extDict) are bytes *)
Lemma hist_def_bytes3 : forall oc d e N ws bsm out, byte_cells oc -> 0 <= d <= Zlength oc -> Zlength oc = N ->
  0 <= ws -> 0 <= bsm -> ext_shape e N ws bsm out -> hist_def oc d 0 e.
Proof.
intros oc d e N ws bsm out Hb Hd HN Hws Hbsm Hsh k Hk. unfold chist. destruct (k <=? d - 0) eqn:E.
- apply Z.leb_le in E. apply byte_cells_Znth; auto; lia.
- apply Z.leb_gt in E. unfold WILDCOPY_OVERLENGTH in Hsh.
  destruct Hsh as [->|[(e1&->&He1)|(eb&b&->&Hbo&Hl)]]; cbn [ext_len] in Hk; try lia.
  + apply byte_cells_Znth; auto; lia.
  + rewrite Zlength_map in Hk. apply zbytes_byte; auto; rewrite ?Zlength_map; lia.
Qed.

Lemma read_cont_hist_buf3 : forall obuf sout s hdr z l dd W ostart,
  c_ring false obuf sout s (FP_zstd hdr z) nil l ->
  lay_dd l dd -> dd_model dd (zp_dm z) -> dd_facts W dd -> lay_cbound (FP_zstd hdr z) l ->
  sf_outStart s = vlong ostart -> sf_outEnd s = vlong ostart -> 0 <= ostart <= sf_outSize s ->
  sf_outSize s <= 2 ^ 32 ->
  0 <= fh_windowSize (zp_h z) -> fh_blockSizeMax (zp_h z) = Z.min (fh_windowSize (zp_h z)) ZSTD_BLOCKSIZE_MAX ->
  0 <= zp_bsm z <= fh_blockSizeMax (zp_h z) ->
  Zlength (sf_ring s) = sf_inSize s + sf_outSize s -> 0 <= sf_inSize s -> byte_cells (sf_ring s) ->
  cont_hist (FP_zstd hdr z) l (oa_ring s (FP_zstd hdr z) ostart).
Proof.
intros obuf sout s hdr z l dd W ostart Hr Hld Hdm Hdf Hcb Hos Hoe Hor HN Hws Hbsm Hb0 Hlr HI Hby.
unfold cont_hist. destruct (zp_ph z) eqn:Ep; auto. intros _ Hcap.
cbn [oa_cap oa_base oa_d oa_c oa_ring is_skip] in *.
destruct (moved3 _ _ _ _ _ _ _ _ ostart Hr Hld Hdm Hdf Hcb Hos Hoe Hor HN Hws Hbsm Hb0 Hcap)
  as (eM&El1&Hsh&_).
rewrite El1. split.
- apply (hist_def_bytes3 _ _ _ (sf_outSize s) (fh_windowSize (zp_h z)) (zp_bsm z) (zp_out z));
    auto; try lia; try (rewrite Zlength_sublist by lia; lia).
  apply byte_cells_sublist; exact Hby.
- right. apply byte_cells_sublist; exact Hby.
Qed.

End CM_R3Ring_1.
