(* FS3 streaming, case zdss_load: the stream buffer (buffered mode) at outStart, the history zstd
   sees and the room for the unit (copied from read/R3Ring.v, R3Pre.v, R3Base.v; the DDict fact used
   is dd_small, from ld_dd). *)
Require Export Zstd.proof.dec.v3.FS.stream.load.L3StFacts.
Local Open Scope logic.

Section CM_L3ErRing_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Definition oa_ring (s: sfields) (fp: fprog) (ostart: Z) : outarr :=
  {| oa_sh := Ews; oa_base := sf_outBuff s; oa_N := sf_outSize s;
     oa_c := sublist (sf_inSize s) (sf_inSize s + sf_outSize s) (sf_ring s); oa_d := ostart;
     oa_cap := if is_skip fp then 0 else sf_outSize s - ostart |}.

Lemma er_vlong_inj : forall x y, 0 <= x <= Int64.max_unsigned -> 0 <= y <= Int64.max_unsigned ->
  vlong x = vlong y -> x = y.
Proof.
intros x y Hx Hy H. unfold vlong in H. inversion H as [H1].
rewrite <- (Int64.unsigned_repr x), <- (Int64.unsigned_repr y) by rep_lia. congruence.
Qed.

Lemma ring_big : forall h bsm N, N >= ring_needed h bsm -> N < fh_contentSize h -> 0 <= fh_windowSize h ->
  0 <= bsm <= Z.min (fh_windowSize h) ZSTD_BLOCKSIZE_MAX ->
  fh_windowSize h + 2 * bsm + 2 * WILDCOPY_OVERLENGTH <= N.
Proof.
intros h bsm N Hr Hf Hw Hb. unfold ring_needed in Hr. unfold ZSTD_WINDOWSIZE_ABSMIN, ZSTD_BLOCKSIZE_MAX in *.
lia.
Qed.

Lemma Zlength_suffix : forall (pre h: list Z), Zlength h <= Zlength (pre ++ h).
Proof. intros. rewrite Zlength_app. pose proof (Zlength_nonneg pre). lia. Qed.

Lemma byte_at_suffix : forall (pre h: list Z) j, 0 <= j < Zlength h ->
  Znth (Zlength pre + j) (pre ++ h) = byte_at h j.
Proof.
intros pre h j Hj. rewrite Znth_app2 by (pose proof (Zlength_nonneg pre); lia).
replace (Zlength pre + j - Zlength pre) with j by lia.
unfold byte_at, Znth. destruct (Z_lt_dec j 0); [lia|reflexivity].
Qed.

(* the history right after the DDict content became the extDict (a frame's first segment) *)
Lemma hist_view_fresh_dict : forall oc d x eb dm ws, ddx_model x = Some dm ->
  hist_view oc d d (ext_of_dict eb (zbytes (dx_bytes x))) (dm_content dm) nil ws.
Proof.
intros oc d x eb dm ws Hm. destruct (ddx_model_suffix x dm Hm) as [pre Hb].
unfold hist_view, ext_of_dict. rewrite app_nil_r. intros k Hk.
assert (Hl: Zlength (dm_content dm) <= Zlength (dx_bytes x)) by (rewrite Hb; apply Zlength_suffix).
cbn [ext_len]. rewrite Zlength_map. split; [lia|].
unfold chist. rewrite (proj2 (Z.leb_gt k (d - d))) by lia.
erewrite Znth_map by (rewrite ?Zlength_map in *; lia).
rewrite Hb. rewrite Zlength_app.
replace (Zlength pre + Zlength (dm_content dm) - (k - (d - d))) with (Zlength pre + (Zlength (dm_content dm) - k)) by lia.
rewrite byte_at_suffix by lia. reflexivity.
Qed.

(* the facts of c_frame a Zstandard frame's continue call uses *)
Lemma c_frame_zstd_facts : forall fs tabs hdr z l dd, c_frame fs tabs (FP_zstd hdr z) l dd ->
  lay_fields fs l /\ lay_dd l dd /\ dd_model dd (zp_dm z) /\ 0 <= zp_bsm z <= fh_blockSizeMax (zp_h z) /\
  fh_blockSizeMax (zp_h z) = Z.min (fh_windowSize (zp_h z)) ZSTD_BLOCKSIZE_MAX /\ 0 <= fh_windowSize (zp_h z) /\
  bytes_ok (zp_out z).
Proof.
intros fs tabs hdr z l dd H. unfold c_frame in H.
destruct H as (_&_&_&Hlf&Hld&_&_&Hb&Hbe&Hw&_&_&_&Hdm&_&_&_&_&_&Hbo&_). auto 10.
Qed.

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
Proof. intros. apply er_vlong_inj; auto; rep_lia. Qed.

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

Lemma moved3 : forall obuf sout s hdr z l dd ostart,
  c_ring false obuf sout s (FP_zstd hdr z) nil l ->
  lay_dd l dd -> dd_model dd (zp_dm z) -> dd_small dd -> lay_cbound (FP_zstd hdr z) l ->
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
intros obuf sout s hdr z l dd ostart Hr Hld Hdm Hdf Hcb Hos Hoe Hor HN Hws Hbsm Hb0 Hcap.
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
  rewrite Edd in Hdm, Hdf. cbn [dd_model] in Hdm. pose proof (Hdf _ _ eq_refl) as Hlen.
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
        rewrite Edd in Hdf. pose proof (Hdf _ _ eq_refl) as Hlen.
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
Lemma hist_pre_buf3 : forall obuf sout s hdr z l dd ostart,
  c_ring false obuf sout s (FP_zstd hdr z) nil l ->
  lay_dd l dd -> dd_model dd (zp_dm z) -> dd_small dd -> lay_cbound (FP_zstd hdr z) l ->
  sf_outStart s = vlong ostart -> sf_outEnd s = vlong ostart -> 0 <= ostart <= sf_outSize s ->
  sf_outSize s <= 2 ^ 32 ->
  0 <= fh_windowSize (zp_h z) -> fh_blockSizeMax (zp_h z) = Z.min (fh_windowSize (zp_h z)) ZSTD_BLOCKSIZE_MAX ->
  0 <= zp_bsm z <= fh_blockSizeMax (zp_h z) ->
  old_hist (ring_cells s) l z ->
  hist_pre (FP_zstd hdr z) l (oa_ring s (FP_zstd hdr z) ostart).
Proof.
intros obuf sout s hdr z l dd ostart Hr Hld Hdm Hdf Hcb Hos Hoe Hor HN Hws Hbsm Hb0 Hold.
unfold hist_pre. cbn [oa_base oa_d oa_cap oa_N oa_c oa_ring is_skip].
destruct (zp_ph z); auto. intros _ Hcap.
destruct (moved3 _ _ _ _ _ _ _ ostart Hr Hld Hdm Hdf Hcb Hos Hoe Hor HN Hws Hbsm Hb0 Hcap)
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
Lemma zhist_buf3 : forall obuf sout s hdr z l dd ostart sm,
  c_ring false obuf sout s (FP_zstd hdr z) nil l ->
  lay_dd l dd -> dd_model dd (zp_dm z) -> dd_small dd -> lay_cbound (FP_zstd hdr z) l ->
  sf_outStart s = vlong ostart -> sf_outEnd s = vlong ostart -> 0 <= ostart <= sf_outSize s ->
  sf_outSize s <= 2 ^ 32 ->
  0 <= fh_windowSize (zp_h z) -> fh_blockSizeMax (zp_h z) = Z.min (fh_windowSize (zp_h z)) ZSTD_BLOCKSIZE_MAX ->
  0 <= zp_bsm z <= fh_blockSizeMax (zp_h z) -> md_dwin (sm_md sm) = true ->
  zhist_ok sm z (lay_H z l (oa_ring s (FP_zstd hdr z) ostart)).
Proof.
intros obuf sout s hdr z l dd ostart sm Hr Hld Hdm Hdf Hcb Hos Hoe Hor HN Hws Hbsm Hb0 Hdw.
unfold lay_H, zhist_ok. cbn [oa_base oa_d oa_cap oa_N oa_c oa_ring is_skip].
destruct (Z_lt_ge_dec 0 (sf_outSize s - ostart)) as [Hcap|Hcap].
- destruct (moved3 _ _ _ _ _ _ _ ostart Hr Hld Hdm Hdf Hcb Hos Hoe Hor HN Hws Hbsm Hb0 Hcap)
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

End CM_L3ErRing_1.
