(* FS3 streaming: the block case's pieces for the body of ZSTD_decompressContinue (port of v2
   body_stream_continue.v). *)
Require Import Zstd.proof.dec.v3.FS.stream.S3Specs.
Require Import Zstd.proof.dec.v3.FS.stream.cont.C3Base.
Require Import Zstd.proof.zstd.XxhLemmas.

Section CM_C3Mid_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* ---------- after the block decoder (the inner switch on bType) ---------- *)

Definition blk_sep (DENT: dent_pred) (TABS: tabs_pred) gv p (f: Z) (dd: option (ddx * val)) (l: hlay) (fs1: fstate)
    (pcs n bt st: Z) (W: list ptr_witness) (o: outarr)
    (i: inwin) (v_bp: val) (oc': list val) (tso: option tstate) (cold: val) (e': Z) : list mpred :=
  [data_at (oa_sh o) (tarray tuchar (oa_N o)) oc' (oa_base o); pws_pred W;
   field_at Ews t_dctx (DOT _previousDstEnd) (fs_previousDstEnd fs1) p;
   field_at Ews t_dctx (DOT _gpDictCopy) (fs_gpDictCopy fs1) p;
   field_at Ews t_dctx (DOT _prefixStart) (fs_prefixStart fs1) p;
   field_at Ews t_dctx (DOT _virtualStart) (fs_virtualStart fs1) p;
   field_at Ews t_dctx (DOT _dictEnd) (fs_dictEnd fs1) p;
   field_at Ews t_dctx (DOT _expected) (Vlong (Int64.repr e')) p;
   field_at Ews t_dctx (DOT _fParams) (fs_fParams fs1) p;
   field_at Ews t_dctx (DOT _processedCSize) (Vlong (Int64.add (Int64.repr pcs) (Int64.repr n))) p;
   field_at Ews t_dctx (DOT _decodedSize) (fs_decodedSize fs1) p;
   field_at Ews t_dctx (DOT _bType) (Vint (Int.repr bt)) p;
   field_at Ews t_dctx (DOT _stage) (Vint (Int.repr st)) p;
   xxh_field p (fs_xxh fs1);
   field_at Ews t_dctx (DOT _headerSize) (fs_headerSize fs1) p;
   field_at Ews t_dctx (DOT _validateChecksum) (fs_validateChecksum fs1) p;
   field_at Ews t_dctx (DOT _rleSize) (fs_rleSize fs1) p;
   field_at Ews t_dctx (DOT _isFrameDecompression) (fs_isFrameDecompression fs1) p;
   field_at Ews t_dctx (DOT _dictID) (fs_dictID fs1) p;
   field_at Ews t_dctx (DOT _ddictIsCold) cold p;
   data_at_ Tsh (Tstruct ___gp_blockProperties_t noattr) v_bp;
   zstd_globals gv; cfg_fmt p f; cfg_lit p;
   match tso with Some ts' => TABS gv p (dd_ox dd) ts' | None => EX lxb: list Z, tables_uninit p lxb end;
   dent_of DENT gv (dd_ox dd); lay_res l;
   data_at (iw_sh i) (tarray tuchar (iw_N i)) (iw_c i) (iw_base i)].

(* ---------- error codes of the callees ---------- *)

(* the callees' errors are not the noForwardProgress codes (80, 82): their posts give dec_err *)
Definition nfp_free (r: Z) : Prop :=
  r <> err_code ZSTD_error_noForwardProgress_destFull /\ r <> err_code ZSTD_error_noForwardProgress_inputEmpty.

Lemma dec_nfp r : dec_err r -> nfp_free r.
Proof. intros (_ & A & B). split; [exact A | exact B]. Qed.

(* the history pointers zstd loads, for a block written at the end of the segment *)
Lemma hpo_seg fs o ps ex :
  lay_fields fs (HL_seg (oa_base o) ps (oa_d o) ex) -> layout_ok_seg ps ex (oa_N o) -> hist_ptrs_ok fs o ex.
Proof.
  intros (_ & Hb & Hps & _ & Hpre & Hvirt & He) (_ & Hel & Hm). unfold hist_ptrs_ok, dictend_ok.
  rewrite Hpre, Hvirt. destruct (oa_base o); try contradiction.
  split; [exact I |]. split; [exact I |].
  destruct ex as [ | e1 elen | sh eb en ec e1 elen]; cbn in He, Hm, Hel |- *.
  - left; exact He.
  - right; left. exists e1. split; [lia | exact (proj1 He)].
  - right; right. split; [exact (proj1 He) | lia].
Qed.

(* copyRawBlock / setRleBlock fail with dstSize_tooSmall *)
Lemma tooSmall_dec r : r = err_code ZSTD_error_dstSize_tooSmall -> dec_err r.
Proof.
  intros ->. unfold dec_err, err_code, ZSTD_error_dstSize_tooSmall, ZSTD_error_noForwardProgress_destFull,
    ZSTD_error_noForwardProgress_inputEmpty.
  split; [reflexivity | lia].
Qed.

Definition blk_mid (hdr: list Z) (z: zprog) (bh: list Z) (c: Z) (l: hlay) (o: outarr) (u: list Z) (r: Z)
    (oc': list val) (tso: option tstate) (cold: val) (e': Z) (fs1: fstate) : Prop :=
  let fp := FP_zstd hdr z in let h := zp_h z in let bsm := zp_bsm z in
  0 <= r <= Int64.max_unsigned /\ Zlength oc' = oa_N o /\
  unchanged_outside (oa_c o) oc' (oa_d o) (oa_d o + oa_cap o) /\ win_bytes (oa_c o) oc' /\
  (cold = fs_ddictIsCold fs1 \/ cold = Vint (Int.repr 0)) /\
  0 <= e' <= Int64.max_unsigned /\
  (is_error_code r = true ->
     (hist_pre fp l o -> cont_err fp (lay_H z l o) u (oa_cap o)) /\
     r <> err_code ZSTD_error_noForwardProgress_destFull /\ r <> err_code ZSTD_error_noForwardProgress_inputEmpty) /\
  (is_error_code r = false ->
     r <= oa_cap o /\
     (r > bsm -> hist_pre fp l o -> cont_err fp (lay_H z l o) u (oa_cap o)) /\
     (r <= bsm ->
        exists cnt (ts': tstate), tso = Some ts' /\ Zlength cnt = r /\ bytes_ok cnt /\
          sublist (oa_d o) (oa_d o + r) oc' = zbytes cnt /\
          cnt_safe z u cnt ts' /\ (hist_pre fp l o -> cnt_ok z (lay_H z l o) u cnt ts') /\
          unchanged_outside (oa_c o) oc' (oa_d o) (oa_d o + Z.min (oa_cap o) (bsm + WILDCOPY_OVERLENGTH)) /\
          (e' = 0 -> bp_last (block_props_of bh) = 1 -> fcs_bad h (zp_out z ++ cnt) -> hist_pre fp l o ->
           cont_err fp (lay_H z l o) u (oa_cap o)) /\
          (if bp_type (block_props_of bh) =? 0 then e' = c - Zlength (zp_got z ++ u) else e' = 0))).

(* ---------- the written window [d, d + cap) of the output array ---------- *)

Definition mid_o (o: outarr) : outarr :=
  {| oa_sh := oa_sh o; oa_base := offset_val (oa_d o) (oa_base o); oa_N := oa_cap o;
     oa_c := sublist (oa_d o) (oa_d o + oa_cap o) (oa_c o); oa_d := 0; oa_cap := oa_cap o |}.

Definition side_W (o: outarr) : list ptr_witness :=
  [pw_bytes (oa_sh o) (oa_d o) (sublist 0 (oa_d o) (oa_c o)) (oa_base o);
   pw_bytes (oa_sh o) (oa_N o - (oa_d o + oa_cap o)) (sublist (oa_d o + oa_cap o) (oa_N o) (oa_c o))
     (offset_val (oa_d o + oa_cap o) (oa_base o))].

(* cap = 0 (the empty window mid_o o, no move): the extDict zstd's pointers describe (dictEnd weakly valid):
   the DDict content (HL_dict, a stuck layout with a dictionary, a segment's ExtSep), an empty separate
   array at dictEnd after a ring wrap (ExtIn), none otherwise *)
Definition ext0 (l: hlay) (o: outarr) : ext_seg :=
  match l with
  | HL_dict eb ec _ => ext_of_dict eb ec
  | HL_stuck _ _ (Some (eb, ec, _)) => ext_of_dict eb ec
  | HL_seg _ _ _ (ExtIn e1 _) => ExtSep Ews (offset_val e1 (oa_base o)) 0 [] 0 0
  | HL_seg _ _ _ e => e
  | _ => ExtNone
  end.

Lemma ext0_res l o : isptr (oa_base o) -> ext_res (ext0 l o) = lay_res l.
Proof.
  intros Hb. destruct l as [ | eb ec gp | b pe [[[eb ec] gp] |] | b ps pe [ | e1 elen | sh eb en ec e1 elen]]; try reflexivity.
  cbn. apply data_at_zero_array_eq; auto; try (destruct (oa_base o); try contradiction; exact I).
Qed.

(* cap = 0: the history of the empty window is ext0's extDict, the DDict content (defined bytes) or empty *)
Lemma hist_def_ext0 l o dd : dd_gap -> lay_dd l dd -> hist_def [] 0 0 (ext0 l o).
Proof.
  intros Hdg Ld k Hk. unfold chist.
  replace (k <=? 0 - 0) with false by (symmetry; apply Z.leb_gt; lia).
  assert (Hd: forall ec, byte_cells ec -> 1 <= k <= Zlength ec -> is_byte_val (Znth (Zlength ec - (k - (0 - 0))) ec)).
  { intros ec Hb Hk'. apply (proj1 (Forall_Znth _ _) Hb). lia. }
  destruct l as [ | eb ec gp | b pe [[[eb ec] gp] |] | b ps pe [ | e1 elen | sh eb en ec e1 elen]];
    cbn [ext0 ext_of_dict ext_len lay_dd] in Hk, Ld |- *; try lia.
  - apply Hd; [exact (proj1 (Hdg _ _ _ _ Ld)) | lia].
  - apply Hd; [exact (proj1 (Hdg _ _ _ _ Ld)) | lia].
  - destruct Ld as (-> & -> & -> & -> & gp & Hdd). apply Hd; [exact (proj1 (Hdg _ _ _ _ Hdd)) | lia].
Qed.

Lemma hpo_zero fs l dd o :
  lay_fields fs (lmove l (oa_base o) (oa_d o) (oa_cap o)) -> lay_dd l dd -> lay_at l o -> oa_cap o = 0 ->
  hist_ptrs_ok fs (mid_o o) (ext0 l o).
Proof.
  intros Lf Ld Hl Hc. unfold lmove in Lf. rewrite Hc in Lf. cbn in Lf.
  unfold hist_ptrs_ok, dictend_ok.
  assert (Hpn: forall v, isptr v -> is_pointer_or_null v) by (intros v Hv; destruct v; try contradiction; exact I).
  destruct l as [ | eb ec gp | b pe [[[eb ec] gp] |] | b ps pe e]; cbn in Lf, Hl, Ld.
  - destruct Lf as ((_ & -> & -> & ->) & _).
    split; [apply mapsto_memory_block.is_pointer_or_null_nullval |].
    split; [apply mapsto_memory_block.is_pointer_or_null_nullval |]. left; reflexivity.
  - destruct Lf as ((Hp & _ & -> & -> & ->) & _). split; [auto |]. split; [auto |].
    right; right. cbn. split; [auto | pose proof (Zlength_nonneg ec); lia].
  - destruct Lf as (_ & _ & _ & (Hp & _ & -> & -> & ->)). split; [auto |]. split; [auto |].
    right; right. cbn. split; [auto | pose proof (Zlength_nonneg ec); lia].
  - destruct Lf as (_ & _ & _ & (_ & -> & -> & ->)).
    split; [apply mapsto_memory_block.is_pointer_or_null_nullval |].
    split; [apply mapsto_memory_block.is_pointer_or_null_nullval |]. left; reflexivity.
  - destruct Lf as (_ & Hb & _ & _ & -> & -> & He). destruct Hl as (-> & _).
    destruct (oa_base o) eqn:Eb; try contradiction.
    split; [exact I |]. split; [exact I |].
    destruct e as [ | e1 elen | sh eb en ec e1 elen]; cbn in He |- *.
    + left; exact He.
    + right; right. split; [| lia]. rewrite Eb. rewrite (proj1 He). cbn. f_equal.
      rewrite Ptrofs.add_assoc, Ptrofs.add_zero. reflexivity.
    + destruct Ld as (-> & -> & -> & -> & _). right; right. split; [exact (proj1 He) | pose proof (Zlength_nonneg ec); lia].
Qed.

Lemma mid_ok o : outarr_ok o -> outarr_ok (mid_o o).
Proof.
  intros (Hs & Hc & HN & Hd & Hcap & Hdc). unfold mid_o, outarr_ok; cbn.
  split; [auto |]. split; [rewrite Zlength_sublist; lia |]. repeat split; lia.
Qed.

Lemma out_split o :
  outarr_ok o -> field_compatible (tarray tuchar (oa_N o)) [] (oa_base o) ->
  data_at (oa_sh o) (tarray tuchar (oa_N o)) (oa_c o) (oa_base o) =
  (pws_pred (side_W o) *
   data_at (oa_sh (mid_o o)) (tarray tuchar (oa_N (mid_o o))) (oa_c (mid_o o)) (offset_val (oa_d o) (oa_base o)))%logic.
Proof.
  intros (Hs & Hc & HN & Hd & Hcap & Hdc) Fc. unfold side_W, mid_o, pws_pred; cbn.
  unfold tarray. rewrite (split3_data_at_Tarray_tuchar (oa_sh o) (oa_N o) (oa_d o) (oa_d o + oa_cap o)) by lia.
  rewrite !fa0_sub by (auto; lia). replace (oa_d o + oa_cap o - oa_d o) with (oa_cap o) by lia.
  rewrite sepcon_emp. apply pred_ext; cancel.
Qed.

Lemma out_join o (bs: list Z) :
  outarr_ok o -> field_compatible (tarray tuchar (oa_N o)) [] (oa_base o) -> Zlength bs <= oa_cap o ->
  pws_pred (side_W o) *
  data_at (oa_sh o) (tarray tuchar (oa_cap o)) (put_bytes (oa_c (mid_o o)) 0 bs) (offset_val (oa_d o) (oa_base o))
  |-- data_at (oa_sh o) (tarray tuchar (oa_N o)) (put_bytes (oa_c o) (oa_d o) bs) (oa_base o).
Proof.
  intros Ho Fc Hb. pose proof Ho as (Hs & Hc & HN & Hd & Hcap & Hdc). pose proof (Zlength_nonneg bs).
  assert (Hz: Zlength (zbytes bs) = Zlength bs) by apply Zlength_map.
  assert (Lp: Zlength (put_bytes (oa_c o) (oa_d o) bs) = oa_N o)
    by (unfold put_bytes; rewrite !Zlength_app, Hz, !Zlength_sublist by lia; lia).
  assert (Fc': field_compatible (tarray tuchar (oa_N o)) [] (oa_base o)) by auto.
  set (o2 := {| oa_sh := oa_sh o; oa_base := oa_base o; oa_N := oa_N o;
      oa_c := put_bytes (oa_c o) (oa_d o) bs; oa_d := oa_d o; oa_cap := oa_cap o |}).
  change (data_at (oa_sh o) (tarray tuchar (oa_N o)) (put_bytes (oa_c o) (oa_d o) bs) (oa_base o))
    with (data_at (oa_sh o2) (tarray tuchar (oa_N o2)) (oa_c o2) (oa_base o2)).
  rewrite (out_split o2) by (subst o2; first [assumption | split; [exact Hs |]; split; [exact Lp |]; cbn; repeat split; lia]).
  subst o2.
  unfold side_W, mid_o, pws_pred; cbn [map fold_right oa_sh oa_base oa_N oa_c oa_d oa_cap pw_pred].
  rewrite !sepcon_emp. unfold put_bytes.
  apply sepcon_derives; [apply sepcon_derives |]; apply derives_refl'; f_equal; list_solve.
Qed.

Lemma mid_wvp o W :
  outarr_ok o -> field_compatible (tarray tuchar (oa_N o)) [] (oa_base o) -> oa_cap o = 0 ->
  (oa_N o = 0 -> (pws_pred W |-- weak_valid_pointer (oa_base o))) ->
  pws_pred (W ++ side_W o) |-- weak_valid_pointer (offset_val (oa_d o) (oa_base o)).
Proof.
  intros (Hs & Hc & HN & Hd & Hcap & Hdc) Fc H0 HW. rewrite pws_app.
  assert (Hni: sepalg.nonidentity (oa_sh o)) by (apply readable_nonidentity, writable_readable; auto).
  destruct (zlt 0 (oa_d o)).
  - apply sepcon_weak_valid_pointer2. unfold side_W, pws_pred; simpl. apply sepcon_weak_valid_pointer1.
    apply arr_wvp; auto; lia.
  - destruct (zlt 0 (oa_N o)).
    + apply sepcon_weak_valid_pointer2. unfold side_W, pws_pred; simpl. apply sepcon_weak_valid_pointer2.
      apply sepcon_weak_valid_pointer1. rewrite H0, Z.add_0_r.
      destruct (fc_arr _ _ Fc ltac:(lia)) as (bb & ofs & -> & _).
      rewrite <- (isptr_offset_val_zero (offset_val (oa_d o) (Vptr bb ofs))) at 2 by exact I.
      apply arr_wvp; auto; lia.
    + apply sepcon_weak_valid_pointer1.
      replace (oa_d o) with 0 by lia. rewrite isptr_offset_val_zero by (destruct Fc; auto).
      apply HW; lia.
Qed.

(* cap = 0: any point of the output array is weakly valid through W and the two sides *)
Lemma mid_wvp_at o W k :
  outarr_ok o -> field_compatible (tarray tuchar (oa_N o)) [] (oa_base o) -> oa_cap o = 0 -> 0 <= k <= oa_N o ->
  (oa_N o = 0 -> (pws_pred W |-- weak_valid_pointer (oa_base o))) ->
  pws_pred (W ++ side_W o) |-- weak_valid_pointer (offset_val k (oa_base o)).
Proof.
  intros (Hs & Hc & HN & Hd & Hcap & Hdc) Fc H0 Hk HW. rewrite pws_app.
  assert (Hni: sepalg.nonidentity (oa_sh o)) by (apply readable_nonidentity, writable_readable; auto).
  destruct (zlt 0 (oa_d o)); [destruct (zle k (oa_d o)) |].
  - apply sepcon_weak_valid_pointer2. unfold side_W, pws_pred; simpl. apply sepcon_weak_valid_pointer1.
    apply arr_wvp; auto; lia.
  - apply sepcon_weak_valid_pointer2. unfold side_W, pws_pred; simpl. apply sepcon_weak_valid_pointer2.
    apply sepcon_weak_valid_pointer1. rewrite H0, Z.add_0_r.
    destruct (fc_arr _ _ Fc ltac:(lia)) as (bb & ofs & -> & _).
    replace (offset_val k (Vptr bb ofs)) with (offset_val (k - oa_d o) (offset_val (oa_d o) (Vptr bb ofs)))
      by (rewrite offset_offset_val; f_equal; lia).
    apply arr_wvp; auto; lia.
  - destruct (zlt 0 (oa_N o)).
    + apply sepcon_weak_valid_pointer2. unfold side_W, pws_pred; simpl. apply sepcon_weak_valid_pointer2.
      apply sepcon_weak_valid_pointer1. rewrite H0, Z.add_0_r.
      destruct (fc_arr _ _ Fc ltac:(lia)) as (bb & ofs & -> & _).
      replace (offset_val k (Vptr bb ofs)) with (offset_val (k - oa_d o) (offset_val (oa_d o) (Vptr bb ofs)))
        by (rewrite offset_offset_val; f_equal; lia).
      apply arr_wvp; auto; lia.
    + apply sepcon_weak_valid_pointer1.
      replace k with 0 by lia. rewrite isptr_offset_val_zero by (destruct Fc; auto).
      apply HW; lia.
Qed.

(* a separate extDict's array is at a pointer (from its data_at) *)
Definition ext_ptr (e: ext_seg) : Prop := match e with ExtSep _ eb _ _ _ _ => isptr eb | _ => True end.

Lemma ext_res_ptr e : ext_res e |-- !! ext_ptr e.
Proof.
  destruct e; cbn; try (apply prop_right; exact I).
  entailer!.
Qed.

(* cap = 0: the extDict ext0's end (dictEnd) is weakly valid when it is empty *)
Lemma ext0_ok_zero fs l dd o W :
  lay_fields fs (lmove l (oa_base o) (oa_d o) (oa_cap o)) -> lay_dd l dd -> lay_at l o -> lay_wit W l -> dd_gap ->
  ext_ptr (ext0 l o) ->
  oa_cap o = 0 -> outarr_ok o -> field_compatible (tarray tuchar (oa_N o)) [] (oa_base o) ->
  (oa_N o = 0 -> (pws_pred W |-- weak_valid_pointer (oa_base o))) ->
  ext0_ok (W ++ side_W o) fs (ext0 l o).
Proof.
  intros Lf Ld Hl Hw Hg Hep Hc Ho Fc HW. unfold lmove in Lf. rewrite Hc in Lf. cbn in Lf.
  assert (Hpre: forall eb ec gp, isptr eb -> pre_ok W (eb, ec, gp) -> dd_pre dd (eb, ec, gp) -> Zlength ec = 0 ->
            pws_pred (W ++ side_W o) |-- weak_valid_pointer (offset_val (Zlength ec) eb)).
  { intros eb ec gp Hpe (_ & Hp) Hd E0. destruct (Hg dd eb ec gp Hd) as (_ & Hne & _).
    destruct Hp as [-> | (-> & -> & Hv)]; [specialize (Hne eq_refl); lia |].
    rewrite pws_app. apply sepcon_weak_valid_pointer1. rewrite Zlength_nil.
    rewrite isptr_offset_val_zero by exact Hpe.
    eapply derives_trans; [exact Hv | apply valid_pointer_weak]. }
  destruct l as [ | eb ec gp | b pe [[[eb ec] gp] |] | b ps pe e]; cbn; auto.
  - intros E0. destruct Lf as ((Hpe & _ & _ & _ & ->) & _). apply (Hpre eb ec gp); auto.
  - intros E0. destruct Lf as (_ & _ & _ & (Hpe & _ & _ & _ & ->)). apply (Hpre eb ec gp); auto.
  - destruct e as [ | e1 elen | sh eb en ec e1 elen]; cbn; auto.
    + intros _.
      destruct Lf as (_ & _ & _ & _ & _ & _ & He). cbn in He. rewrite (proj1 He).
      destruct Hl as (-> & _ & _ & _ & Hel & HeN).
      apply mid_wvp_at; auto. lia.
    + intros E0. destruct Lf as (_ & _ & _ & _ & _ & _ & He). rewrite (proj1 He).
      destruct Ld as (_ & Hen & He1 & _). destruct Hw as (_ & Hv). specialize (Hv E0).
      rewrite He1, E0, pws_app. apply sepcon_weak_valid_pointer1. cbn in Hep.
      rewrite isptr_offset_val_zero by exact Hep.
      eapply derives_trans; [exact Hv | apply valid_pointer_weak].
Qed.

(* cap > 0: the extDict of the moved layout (ExtSep: the DDict content, from HL_dict or a segment) *)
Lemma ext0_ok_seg W fs l dd o ps ex :
  lmove l (oa_base o) (oa_d o) (oa_cap o) = HL_seg (oa_base o) ps (oa_d o) ex -> 0 < oa_cap o ->
  lay_fields fs (HL_seg (oa_base o) ps (oa_d o) ex) -> lay_dd l dd -> lay_wit W l -> dd_gap -> ext_ptr ex ->
  ext0_ok W fs ex.
Proof.
  intros El Hc0 Lf Ld Hw Hg Hep. unfold lmove in El.
  replace (oa_cap o <=? 0) with false in El by (symmetry; apply Z.leb_gt; lia).
  destruct ex as [ | e1 elen | sh eb en ec e1 elen]; cbn; auto. intros E0.
  destruct Lf as (_ & _ & _ & _ & _ & _ & He). rewrite (proj1 He).
  assert (Hwv: forall v, isptr v -> (pws_pred W |-- valid_pointer v) -> pws_pred W |-- weak_valid_pointer (offset_val 0 v)).
  { intros v Hpv Hv. rewrite isptr_offset_val_zero by exact Hpv. eapply derives_trans; [exact Hv | apply valid_pointer_weak]. }
  cbn in Hep.
  destruct l as [ | eb' ec' gp | b pe od | b ps' pe e]; cbn in El; try discriminate.
  - unfold ext_of_dict in El. injection El as E1 E2 E3 E4 E5 E6 E7. subst.
    destruct Hw as (_ & Hp). edestruct Hg as (_ & Hne & _); [exact Ld |].
    destruct Hp as [-> | (-> & Hnil & Hv)]; [specialize (Hne eq_refl); lia |]. subst. cbn in *. apply Hwv; auto.
  - destruct (pe =? oa_d o); [| discriminate]. inv El.
    destruct Ld as (_ & Hen & He1 & _). destruct Hw as (_ & Hv). rewrite He1. apply Hwv; auto.
Qed.

(* R6: a compressed block's output is bytes: B's post for an extDict clear of the block, or the whole
   output array bytes (the calloc'd ring) *)
Lemma bc_sub_bytes (oc': list val) d r :
  byte_cells oc' -> exists cnt, sublist d (d + r) oc' = zbytes cnt /\ bytes_ok cnt.
Proof.
  intros Hb. assert (Hs: byte_cells (sublist d (d + r) oc')) by (apply Forall_sublist; exact Hb).
  induction (sublist d (d + r) oc') as [ | v l IH].
  - exists nil. split; [reflexivity | constructor].
  - inv Hs. destruct H1 as (x & Hx & ->). destruct (IH H2) as (cnt & E & B).
    exists (x :: cnt). split; [simpl; rewrite E; reflexivity | constructor; [unfold is_byte; lia | exact B]].
Qed.

Lemma comp_hist_bytes (oc oc': list val) (d cap ps: Z) (e: ext_seg) (r bsm: Z) :
  hist_def oc d ps e /\ (ext_clean d cap e \/ byte_cells oc) -> win_bytes oc oc' ->
  (hist_def oc d ps e -> (ext_clean d cap e \/ (r <= bsm /\ ext_far d cap bsm e)) ->
   exists cnt, sublist d (d + r) oc' = zbytes cnt /\ bytes_ok cnt) ->
  exists cnt, sublist d (d + r) oc' = zbytes cnt /\ bytes_ok cnt.
Proof.
  intros [Hh [Hc | Hb]] Hw Hk; [apply Hk; auto | apply bc_sub_bytes, Hw, Hb].
Qed.

Lemma out_unsplit o :
  outarr_ok o -> field_compatible (tarray tuchar (oa_N o)) [] (oa_base o) ->
  pws_pred (side_W o) * data_at (oa_sh o) (tarray tuchar (oa_cap o)) (oa_c (mid_o o)) (offset_val (oa_d o) (oa_base o))
  |-- data_at (oa_sh o) (tarray tuchar (oa_N o)) (oa_c o) (oa_base o).
Proof. intros. rewrite (out_split o) by auto. apply derives_refl. Qed.

Lemma pws_app_fold W1 W2 : pws_pred W1 * pws_pred W2 |-- pws_pred (W1 ++ W2).
Proof. rewrite pws_app. apply derives_refl. Qed.

Lemma pws_app_unfold W1 W2 : pws_pred (W1 ++ W2) |-- pws_pred W1 * pws_pred W2.
Proof. rewrite pws_app. apply derives_refl. Qed.

Lemma put_bytes_len (oc: list val) d (bs: list Z) :
  0 <= d -> d + Zlength bs <= Zlength oc -> Zlength (put_bytes oc d bs) = Zlength oc.
Proof.
  intros. unfold put_bytes. pose proof (Zlength_nonneg bs).
  rewrite !Zlength_app, Zlength_map, !Zlength_sublist by lia. lia.
Qed.

Lemma sublist_put_bytes (oc: list val) d (bs: list Z) :
  0 <= d -> d + Zlength bs <= Zlength oc -> sublist d (d + Zlength bs) (put_bytes oc d bs) = zbytes bs.
Proof. intros. unfold put_bytes. pose proof (Zlength_nonneg bs). list_solve. Qed.

Lemma unchanged_put_bytes (oc: list val) d (bs: list Z) lo hi :
  0 <= d -> d + Zlength bs <= Zlength oc -> lo <= d -> d + Zlength bs <= hi ->
  unchanged_outside oc (put_bytes oc d bs) lo hi.
Proof.
  intros Hd Hb Hl Hh j Hj Hn. unfold put_bytes. pose proof (Zlength_nonneg bs).
  assert (Hz: Zlength (zbytes bs) = Zlength bs) by apply Zlength_map.
  destruct (zlt j d).
  - rewrite app_Znth1 by (rewrite Zlength_sublist; lia). rewrite Znth_sublist by lia. f_equal; lia.
  - rewrite app_Znth2 by (rewrite Zlength_sublist; lia). rewrite Zlength_sublist by lia.
    rewrite app_Znth2 by (rewrite Hz; lia). rewrite Hz, Znth_sublist by lia. f_equal; lia.
Qed.

Lemma win_bytes_put (oc: list val) d (bs: list Z) :
  0 <= d -> d + Zlength bs <= Zlength oc -> bytes_ok bs -> win_bytes oc (put_bytes oc d bs).
Proof.
  intros Hd Hb Bb Hc. pose proof (Zlength_nonneg bs). unfold put_bytes, byte_cells in *.
  apply Forall_app; split; [apply Forall_sublist; auto |].
  apply Forall_app; split; [| apply Forall_sublist; auto].
  apply Forall_map. eapply Forall_impl; [| exact Bb].
  intros x Hx. unfold is_byte in Hx. exists x. split; [lia | reflexivity].
Qed.

Lemma is_error_le k : 0 <= k <= ZSTD_BLOCKSIZE_MAX -> is_error_code k = false.
Proof. intros. apply is_error_small. unfold ZSTD_BLOCKSIZE_MAX in *. lia. Qed.

Lemma blk_mid_raw hdr z bh c l o u fs1 (ts: tstate) :
  zp_ph z = ZP_body bh -> bp_type (block_props_of bh) = 0 -> cblock_size bh = Some c ->
  1 <= Zlength u <= c - Zlength (zp_got z) -> 0 < c <= zp_bsm z ->
  zp_bsm z <= ZSTD_BLOCKSIZE_MAX ->
  Zlength u <= oa_cap o -> bytes_ok u -> outarr_ok o -> ts_d ts = zp_ts z ->
  blk_mid hdr z bh c l o u (Zlength u) (put_bytes (oa_c o) (oa_d o) u) (Some ts) (fs_ddictIsCold fs1)
    (c - Zlength (zp_got z) - Zlength u) fs1.
Proof.
  intros Ez Et Ec Hn Hc Hb Hcap Bu (Hs & HcN & HN & Hd & Hc0 & Hdc) Ets.
  pose proof (Zlength_nonneg (zp_got z)). unfold ZSTD_BLOCKSIZE_MAX in Hb.
  assert (Hne: is_error_code (Zlength u) = false) by (apply is_error_small; lia).
  split; [rep_lia |]. split; [rewrite put_bytes_len; lia |].
  split; [apply unchanged_put_bytes; lia |]. split; [apply win_bytes_put; auto; lia |].
  split; [left; auto |]. split; [rep_lia |].
  split; [rewrite Hne; discriminate |]. intros _. split; [lia |]. split; [lia |]. intros _.
  exists u, ts. split; [auto |]. split; [auto |]. split; [auto |].
  split; [apply sublist_put_bytes; lia |].
  split; [unfold cnt_safe; rewrite Ez, Et; simpl; auto |].
  split; [intros _; unfold cnt_ok; rewrite Ez, Et; simpl; auto |].
  split; [apply unchanged_put_bytes; try lia; unfold WILDCOPY_OVERLENGTH; lia |].
  split.
  - intros E0 Hl Hf _. cbn [cont_err]. rewrite Ez, Et. simpl. right. split.
    + rewrite Ec, Zlength_app. f_equal. lia.
    + auto.
  - rewrite Et. simpl. rewrite Zlength_app. lia.
Qed.

Lemma zbytes_inj (a b: list Z) : bytes_ok a -> bytes_ok b -> zbytes a = zbytes b -> a = b.
Proof.
  revert b. induction a as [ | x a IH]; intros [ | y b] Ha Hb E; simpl in E; try discriminate; auto.
  assert (Hx: Vint (Int.repr x) = Vint (Int.repr y)) by congruence.
  assert (Ht: zbytes a = zbytes b) by congruence.
  inv Ha. inv Hb. f_equal; [| apply IH; auto].
  unfold is_byte in *.
  apply (f_equal (fun v => match v with Vint i => Int.unsigned i | _ => 0 end)) in Hx. simpl in Hx.
  rewrite !Int.unsigned_repr in Hx by rep_lia. auto.
Qed.

Lemma decode_block_len ts hist out b bsm ws ts2 c2 :
  decode_block ts hist out b bsm ws = Some (ts2, c2) -> Zlength c2 <= bsm.
Proof.
  unfold decode_block. intros H.
  repeat match type of H with
  | context [match ?x with _ => _ end] => destruct x eqn:?; try discriminate
  end.
  inv H. match goal with Hb: (?x >? bsm) = false |- _ => destruct (Z.gtb_spec x bsm); [discriminate | lia] end.
Qed.

Lemma blk_mid_err hdr z bh c l o u r tso cold e' fs1 :
  0 <= r <= Int64.max_unsigned -> is_error_code r = true -> outarr_ok o ->
  (hist_pre (FP_zstd hdr z) l o -> cont_err (FP_zstd hdr z) (lay_H z l o) u (oa_cap o)) ->
  r <> err_code ZSTD_error_noForwardProgress_destFull -> r <> err_code ZSTD_error_noForwardProgress_inputEmpty ->
  (cold = fs_ddictIsCold fs1 \/ cold = Vint (Int.repr 0)) -> 0 <= e' <= Int64.max_unsigned ->
  blk_mid hdr z bh c l o u r (oa_c o) tso cold e' fs1.
Proof.
  intros Hr Er (Hs & HcN & _) He N1 N2 Hc Hee.
  split; [auto |]. split; [auto |]. split; [intros j _ _; auto |]. split; [intros X; exact X |].
  split; [auto |]. split; [auto |].
  split; [auto |]. rewrite Er. discriminate.
Qed.

Lemma blk_mid_rle hdr z bh c l o u fs1 (ts: tstate) :
  zp_ph z = ZP_body bh -> bp_type (block_props_of bh) = 1 ->
  bp_origSize (block_props_of bh) <= oa_cap o -> 0 <= bp_origSize (block_props_of bh) ->
  zp_bsm z <= ZSTD_BLOCKSIZE_MAX -> bytes_ok u -> 1 <= Zlength u -> outarr_ok o -> ts_d ts = zp_ts z ->
  blk_mid hdr z bh c l o u (bp_origSize (block_props_of bh))
    (put_bytes (oa_c o) (oa_d o) (Zrepeat (Znth 0 u) (bp_origSize (block_props_of bh))))
    (Some ts) (fs_ddictIsCold fs1) 0 fs1.
Proof.
  intros Ez Et Hcap Hos Hb Bu Lu Ho Ets. pose proof Ho as (Hs & HcN & HN & Hd & Hc0 & Hdc).
  set (k := bp_origSize (block_props_of bh)) in *. unfold ZSTD_BLOCKSIZE_MAX in Hb.
  assert (Lr: Zlength (Zrepeat (Znth 0 u) k) = k) by (rewrite Zlength_Zrepeat; lia).
  assert (Hne: is_error_code k = false) by (unfold is_error_code; apply Z.ltb_ge; rep_lia).
  assert (Bz: bytes_ok (Zrepeat (Znth 0 u) k)).
  { unfold bytes_ok, Zrepeat. apply Forall_forall. intros x Hx. apply repeat_spec in Hx. subst.
    unfold bytes_ok in Bu. apply Forall_Znth; auto; lia. }
  assert (Hbyte: Znth 0 u = byte_at u 0).
  { unfold byte_at. destruct u; [rewrite Zlength_nil in Lu; lia | reflexivity]. }
  split; [rep_lia |]. split; [rewrite put_bytes_len; lia |].
  split; [apply unchanged_put_bytes; lia |]. split; [apply win_bytes_put; auto; lia |].
  split; [left; auto |]. split; [rep_lia |].
  split; [rewrite Hne; discriminate |]. intros _. split; [lia |].
  split; [intros Hk _; cbn [cont_err]; rewrite Ez, Et; simpl; right; left; exact Hk |]. intros Hk.
  exists (Zrepeat (Znth 0 u) k), ts. split; [auto |]. split; [auto |]. split; [auto |].
  split; [replace (oa_d o + k) with (oa_d o + Zlength (Zrepeat (Znth 0 u) k)) by (rewrite Lr; auto);
          apply sublist_put_bytes; lia |].
  split; [unfold cnt_safe; rewrite Ez, Et; simpl; rewrite Hbyte; auto |].
  split; [intros _; unfold cnt_ok; rewrite Ez, Et; simpl; rewrite Hbyte; auto |].
  split; [apply unchanged_put_bytes; try lia; unfold WILDCOPY_OVERLENGTH; lia |].
  split.
  - intros _ Hl Hf _. cbn [cont_err]. rewrite Ez, Et. simpl. right. right. split; auto.
  - rewrite Et. reflexivity.
Qed.

Lemma zbytes_mod (a b: list Z) : zbytes a = zbytes b ->
  map (fun x => x mod 2 ^ 32) a = map (fun x => x mod 2 ^ 32) b.
Proof.
  revert b. induction a as [ | x a IH]; intros [ | y b] E; simpl in E; try discriminate; auto.
  assert (Hx: Int.repr x = Int.repr y) by congruence.
  assert (Ht: zbytes a = zbytes b) by congruence.
  simpl. f_equal; [| apply IH; auto].
  apply (f_equal Int.unsigned) in Hx. rewrite !Int.unsigned_repr_eq in Hx. exact Hx.
Qed.

Lemma blk_mid_comp hdr z bh c l o u r oc' tso cold fs1 :
  zp_ph z = ZP_body bh -> bp_type (block_props_of bh) = 2 -> outarr_ok o ->
  0 <= r <= Int64.max_unsigned -> Zlength oc' = oa_N o ->
  unchanged_outside (oa_c o) oc' (oa_d o) (oa_d o + oa_cap o) -> win_bytes (oa_c o) oc' ->
  (is_error_code r = false ->
     r <= oa_cap o /\ cold = Vint (Int.repr 0) /\ tso <> None /\
     (r <= zp_bsm z -> exists cnt, sublist (oa_d o) (oa_d o + r) oc' = zbytes cnt /\ bytes_ok cnt) /\
     (r <= zp_bsm z ->
      unchanged_outside (oa_c o) oc' (oa_d o)
        (oa_d o + Z.min (oa_cap o) (zp_bsm z + WILDCOPY_OVERLENGTH)))) ->
  (cold = fs_ddictIsCold fs1 \/ cold = Vint (Int.repr 0)) ->
  zp_bsm z <= ZSTD_BLOCKSIZE_MAX ->
  (is_error_code r = true -> nfp_free r) ->
  (hist_pre (FP_zstd hdr z) l o ->
   block_ok (zp_ts z) (lay_H z l o) (zp_out z) u (zp_bsm z) (fh_windowSize (zp_h z)) 1
     (oa_c o) oc' (oa_d o) (oa_cap o) r (option_map ts_d tso)) ->
  blk_mid hdr z bh c l o u r oc' tso cold 0 fs1.
Proof.
  intros Ez Et Ho Hr HN Hun Hwb Hok Hc Hbsm N12 Hbk. pose proof Ho as (Hs & HcN & HN' & Hd & Hc0 & Hdc).
  unfold block_ok in Hbk.
  split; [auto |]. split; [auto |]. split; [auto |]. split; [exact Hwb |]. split; [auto |]. split; [rep_lia |].
  split.
  - intros Er. split; [| apply N12; exact Er]. intros Hp. specialize (Hbk Hp). cbn [cont_err]. rewrite Ez, Et. simpl.
    destruct (decode_block _ _ _ _ _ _) as [[ts2 c2] |]; auto.
    destruct Hbk as [(Er' & _) | (_ & Hl)]; [congruence | left; lia].
  - intros Er. destruct (Hok Er) as (Hrc & Hcold & Hts & Hcnt & Hwin).
    split; [auto |]. split.
    + intros Hb Hp. specialize (Hbk Hp). cbn [cont_err]. rewrite Ez, Et. simpl.
      destruct (decode_block _ _ _ _ _ _) as [[ts2 c2] |] eqn:Ed; auto.
      apply decode_block_len in Ed.
      destruct Hbk as [(_ & Er2 & _) | ((Er2 & _) & _)]; [lia | congruence].
    + intros Hb. destruct (Hcnt Hb) as (cnt & Hsub & Bc). pose proof (Hwin Hb) as Hunw.
      assert (Lc: Zlength cnt = r).
      { apply (f_equal (@Zlength val)) in Hsub. rewrite Zlength_sublist in Hsub by lia.
        rewrite Zlength_map in Hsub. lia. }
      destruct tso as [ts' |]; [| contradiction]. cbn [option_map] in Hbk.
      exists cnt, ts'. split; [auto |]. split; [auto |]. split; [auto |]. split; [auto |].
      split; [unfold cnt_safe; rewrite Ez, Et; simpl; split; [auto | lia] |].
      split; [| split; [exact Hunw | split]].
      * intros Hp. specialize (Hbk Hp). unfold cnt_ok; rewrite Ez, Et; simpl.
        split; [auto |]. split; [lia |].
        destruct (decode_block _ _ _ _ _ _) as [[ts2 c2] |] eqn:Ed; auto.
        destruct Hbk as [(_ & Er2 & Hsub2 & _ & Ets & Hun2) | ((Er2 & _) & _)]; [| congruence].
        injection Ets as Ets. subst ts2. split; [| auto].
        apply zbytes_mod. rewrite <- Hsub, <- Hsub2. repeat f_equal; lia.
      * intros _ Hl Hf Hp. specialize (Hbk Hp). cbn [cont_err]. rewrite Ez, Et. simpl.
        destruct (decode_block _ _ _ _ _ _) as [[ts2 c2] |] eqn:Ed; auto.
        destruct Hbk as [(_ & Er2 & Hsub2 & _ & Ets & Hun2) | ((Er2 & _) & _)]; [| congruence].
        right. split; [auto |]. unfold fcs_bad in *. rewrite Zlength_app in *. lia.
      * rewrite Et. reflexivity.
Qed.

Lemma blk_mid_comp0 hdr z bh c l o u r oc'' tso cold fs1 :
  zp_ph z = ZP_body bh -> bp_type (block_props_of bh) = 2 -> outarr_ok o -> oa_cap o = 0 ->
  0 <= r <= Int64.max_unsigned ->
  (is_error_code r = false ->
     r <= 0 /\ cold = Vint (Int.repr 0) /\ tso <> None) ->
  (cold = fs_ddictIsCold fs1 \/ cold = Vint (Int.repr 0)) ->
  zp_bsm z <= ZSTD_BLOCKSIZE_MAX ->
  (is_error_code r = true -> nfp_free r) ->
  block_ok (zp_ts z) (lay_H z l o) (zp_out z) u (zp_bsm z) (fh_windowSize (zp_h z)) 1
    nil oc'' 0 0 r (option_map ts_d tso) ->
  blk_mid hdr z bh c l o u r (oa_c o) tso cold 0 fs1.
Proof.
  intros Ez Et Ho Hc0 Hr Hok Hc Hbsm N12 Hbk. pose proof Ho as (Hs & HcN & HN' & Hd & Hcap & Hdc).
  assert (Hwb0: win_bytes (oa_c o) (oa_c o)) by (intros X; exact X).
  apply blk_mid_comp; auto.
  - intros j _ _; auto.
  - intros Er. destruct (Hok Er) as (Hr0 & Hcold & Hts). split; [lia |]. split; [auto |]. split; [auto |].
    split; [intros _; exists nil; split; [| constructor]; replace r with 0 by lia; rewrite sublist_nil'; auto; lia |].
    intros _ j _ _; reflexivity.
  - intros _. unfold block_ok in *. rewrite Hc0.
    destruct (decode_block _ _ _ _ _ _) as [[ts2 c2] |]; auto.
    destruct Hbk as [(Er & Lr & Hsub & Bc2 & Ets & _) | (Er & Hl)]; [left | right; auto].
    assert (r = 0).
    { destruct (Hok Er) as (Hr0 & _). lia. }
    rewrite H in *. destruct c2; [| rewrite Zlength_cons in Lr; pose proof (Zlength_nonneg c2); lia].
    split; [auto |]. split; [auto |]. split; [rewrite sublist_nil'; auto; lia |]. split; [auto |]. split; [auto |].
    intros _ j _ _. auto.
Qed.

Lemma frame_fields_fold_pc p fs v :
  field_at Ews t_dctx (DOT _previousDstEnd) (fs_previousDstEnd fs) p *
  field_at Ews t_dctx (DOT _gpDictCopy) (fs_gpDictCopy fs) p *
  field_at Ews t_dctx (DOT _prefixStart) (fs_prefixStart fs) p *
  field_at Ews t_dctx (DOT _virtualStart) (fs_virtualStart fs) p *
  field_at Ews t_dctx (DOT _dictEnd) (fs_dictEnd fs) p *
  field_at Ews t_dctx (DOT _expected) (fs_expected fs) p *
  field_at Ews t_dctx (DOT _fParams) (fs_fParams fs) p *
  field_at Ews t_dctx (DOT _processedCSize) v p *
  field_at Ews t_dctx (DOT _decodedSize) (fs_decodedSize fs) p *
  field_at Ews t_dctx (DOT _bType) (fs_bType fs) p *
  field_at Ews t_dctx (DOT _stage) (fs_stage fs) p *
  xxh_field p (fs_xxh fs) *
  field_at Ews t_dctx (DOT _headerSize) (fs_headerSize fs) p *
  field_at Ews t_dctx (DOT _validateChecksum) (fs_validateChecksum fs) p *
  field_at Ews t_dctx (DOT _rleSize) (fs_rleSize fs) p *
  field_at Ews t_dctx (DOT _isFrameDecompression) (fs_isFrameDecompression fs) p *
  field_at Ews t_dctx (DOT _dictID) (fs_dictID fs) p *
  field_at Ews t_dctx (DOT _ddictIsCold) (fs_ddictIsCold fs) p |-- frame_fields p (fsu_processedCSize fs v).
Proof. unfold frame_fields, fsu_processedCSize. simpl. cancel. Qed.

(* the block finished or not, the tail's post: the frame fields after it *)
Definition fs_after (fs1: fstate) (pe: val) (pc: val) (out_len r: Z) (bt: Z) (x: option (list Z)) (cold: val)
    (e2 st2: val) : fstate :=
  {| fs_previousDstEnd := pe; fs_gpDictCopy := Vint (Int.repr 0);
     fs_prefixStart := fs_prefixStart fs1; fs_virtualStart := fs_virtualStart fs1;
     fs_dictEnd := fs_dictEnd fs1; fs_expected := e2; fs_fParams := fs_fParams fs1;
     fs_processedCSize := pc; fs_decodedSize := Vlong (Int64.repr (out_len + r));
     fs_bType := Vint (Int.repr bt); fs_stage := st2; fs_xxh := x;
     fs_headerSize := fs_headerSize fs1; fs_validateChecksum := fs_validateChecksum fs1;
     fs_rleSize := fs_rleSize fs1; fs_isFrameDecompression := fs_isFrameDecompression fs1;
     fs_dictID := fs_dictID fs1; fs_ddictIsCold := cold |}.

Lemma cont_res_after fs1 hdr z bh l dd o u oc' cnt (ts': tstate) c cold pcs e2 st2 (tabs1: tabs3) :
  stuck_gap ->
  c_frame fs1 tabs1 (FP_zstd hdr z) (lmove l (oa_base o) (oa_d o) (oa_cap o)) dd ->
  zp_ph z = ZP_body bh -> cblock_size bh = Some c -> unit_ok (FP_zstd hdr z) (Zlength u) -> bytes_ok u ->
  lay_at l o -> isptr (oa_base o) -> 0 <= oa_d o ->
  0 <= Zlength cnt <= Int64.max_unsigned -> Zlength oc' = oa_N o ->
  unchanged_outside (oa_c o) oc' (oa_d o) (oa_d o + oa_cap o) -> is_error_code (Zlength cnt) = false ->
  sublist (oa_d o) (oa_d o + Zlength cnt) oc' = zbytes cnt -> cnt_safe z u cnt ts' ->
  (hist_pre (FP_zstd hdr z) l o -> cnt_ok z (lay_H z l o) u cnt ts') ->
  unchanged_outside (oa_c o) oc' (oa_d o)
    (oa_d o + Z.min (oa_cap o) (zp_bsm z + WILDCOPY_OVERLENGTH)) ->
  win_bytes (oa_c o) oc' ->
  cont_checks z u cnt ->
  bytes_ok cnt ->
  Zlength cnt <= zp_bsm z ->
  (cold = fs_ddictIsCold fs1 \/ cold = Vint (Int.repr 0)) ->
  phase_fields (fs_after fs1 (offset_val (oa_d o + Zlength cnt) (oa_base o)) (Vlong (Int64.repr pcs))
     (Zlength (zp_out z)) (Zlength cnt) (bp_type (block_props_of bh))
     (if fcheck z then Some (zp_out z ++ cnt) else fs_xxh fs1) cold e2 st2)
     (zstep z u cnt ts') ->
  cont_res (FP_zstd hdr z) l dd o u (Zlength cnt) oc'
    (fs_after fs1 (offset_val (oa_d o + Zlength cnt) (oa_base o)) (Vlong (Int64.repr pcs))
     (Zlength (zp_out z)) (Zlength cnt) (bp_type (block_props_of bh))
     (if fcheck z then Some (zp_out z ++ cnt) else fs_xxh fs1) cold e2 st2) (Some ts').
Proof.
  intros Hg Hc Ez Ec Hu Bu Hl Hp Hd Hr HN Hun Er Hs Hsafe Hcnt Hun2 Hby Hck Bc Lb Hcold Ph.
  pose proof Hc as (I1 & I2 & I3 & Lf & Ld & _).
  eapply cont_res_blk; eauto.
  - unfold lnext. rewrite Ez. eapply lay_lwrite; eauto; try reflexivity; try lia.
    apply lmove_at; auto.
  - unfold lnext. rewrite Ez. apply lay_dd_lwrite; auto.
  - unfold fs_after; cbn. destruct Hcold as [-> | ->]; auto.
  - unfold fs_after; cbn. eauto.
  - unfold fs_after; cbn. rewrite Zlength_app. reflexivity.
  - intros Hf. unfold fs_after; cbn. rewrite Hf. reflexivity.
Qed.

Lemma frame_fields_fold p fs :
  field_at Ews t_dctx (DOT _previousDstEnd) (fs_previousDstEnd fs) p *
  field_at Ews t_dctx (DOT _gpDictCopy) (fs_gpDictCopy fs) p *
  field_at Ews t_dctx (DOT _prefixStart) (fs_prefixStart fs) p *
  field_at Ews t_dctx (DOT _virtualStart) (fs_virtualStart fs) p *
  field_at Ews t_dctx (DOT _dictEnd) (fs_dictEnd fs) p *
  field_at Ews t_dctx (DOT _expected) (fs_expected fs) p *
  field_at Ews t_dctx (DOT _fParams) (fs_fParams fs) p *
  field_at Ews t_dctx (DOT _processedCSize) (fs_processedCSize fs) p *
  field_at Ews t_dctx (DOT _decodedSize) (fs_decodedSize fs) p *
  field_at Ews t_dctx (DOT _bType) (fs_bType fs) p *
  field_at Ews t_dctx (DOT _stage) (fs_stage fs) p *
  xxh_field p (fs_xxh fs) *
  field_at Ews t_dctx (DOT _headerSize) (fs_headerSize fs) p *
  field_at Ews t_dctx (DOT _validateChecksum) (fs_validateChecksum fs) p *
  field_at Ews t_dctx (DOT _rleSize) (fs_rleSize fs) p *
  field_at Ews t_dctx (DOT _isFrameDecompression) (fs_isFrameDecompression fs) p *
  field_at Ews t_dctx (DOT _dictID) (fs_dictID fs) p *
  field_at Ews t_dctx (DOT _ddictIsCold) (fs_ddictIsCold fs) p |-- frame_fields p fs.
Proof. unfold frame_fields. cancel. Qed.

Lemma nfp_ne k : k <> 80 -> k <> 82 ->
  2 ^ 64 - k <> err_code ZSTD_error_noForwardProgress_destFull /\
  2 ^ 64 - k <> err_code ZSTD_error_noForwardProgress_inputEmpty.
Proof. unfold err_code, ZSTD_error_noForwardProgress_destFull, ZSTD_error_noForwardProgress_inputEmpty. lia. Qed.

Definition fcs_t15 (f a: Z) : Z := if f =? 2 ^ 64 - 1 then 0 else if a mod 2 ^ 64 =? f then 0 else 1.

Lemma fcs_then a f : 0 <= f < 2 ^ 64 -> Int64.repr f <> Int64.repr (- (1)) ->
  Vint (Int.repr (fcs_t15 f a)) = bool2val (Int64.cmpu Cne (Int64.repr a) (Int64.repr f)).
Proof.
  intros Hf Hn. unfold fcs_t15.
  assert (Hne: f <> 2 ^ 64 - 1).
  { intros ->. apply Hn. apply Int64.eqm_samerepr. exists 1. reflexivity. }
  rewrite (proj2 (Z.eqb_neq _ _) Hne). unfold Int64.cmpu, Int64.eq. rewrite !Int64.unsigned_repr_eq.
  change Int64.modulus with (2 ^ 64). rewrite (Z.mod_small f) by lia.
  destruct (zeq (a mod 2 ^ 64) f), (Z.eqb_spec (a mod 2 ^ 64) f); simpl; auto; congruence.
Qed.

Lemma fcs_else a f : 0 <= f < 2 ^ 64 -> Int64.repr f = Int64.repr (- (1)) -> fcs_t15 f a = 0.
Proof.
  intros Hf He. unfold fcs_t15. apply (f_equal Int64.unsigned) in He.
  rewrite Int64.unsigned_repr in He by (unfold Int64.max_unsigned; simpl; lia).
  rewrite He. reflexivity.
Qed.

Lemma fcs_ok_of a f : fcs_t15 f a = 0 -> f = 2 ^ 64 - 1 \/ a mod 2 ^ 64 = f.
Proof.
  unfold fcs_t15. destruct (Z.eqb_spec f (2 ^ 64 - 1)); [auto |].
  destruct (Z.eqb_spec (a mod 2 ^ 64) f); [auto | discriminate].
Qed.

Lemma fcs_bad_of a f : 0 <= f < 2 ^ 64 -> fcs_t15 f a <> 0 -> f <> 2 ^ 64 - 1 /\ a <> f.
Proof.
  unfold fcs_t15. intros Hf. destruct (Z.eqb_spec f (2 ^ 64 - 1)); [congruence |].
  destruct (Z.eqb_spec (a mod 2 ^ 64) f); [congruence |]. intros _. split; auto.
  intros <-. apply n0. apply Z.mod_small. lia.
Qed.

Lemma repr_neg64 k : Int64.repr (- k) = Int64.repr (2 ^ 64 - k).
Proof. apply Int64.eqm_samerepr. exists (-1). simpl. lia. Qed.

End CM_C3Mid_1.

Ltac fif_set id v :=
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp id v :: Q) (SEPx R))) end.

Ltac repl_item R a b :=
  lazymatch R with
  | a :: ?t => constr:(b :: t)
  | ?x :: ?t => let t' := repl_item t a b in constr:(x :: t')
  end.

Ltac fif_prop X :=
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx (X :: P) (LOCALx Q (SEPx R))) end.

Ltac head_dw0 c :=
  lazymatch c with Sloop _ Sbreak => idtac | Ssequence ?a _ => head_dw0 a end.

(* do { DEBUGLOG } while (0) *)
Ltac dw0 :=
  match goal with |- semax _ ?P ?c _ => head_dw0 c;
    first [ forward_loop P break: P; [entailer! | forward; entailer! | ]
          | forward_loop P break: P;
            [entailer! | forward_if P; [exfalso; lia | forward; entailer! | forward; entailer!] | ] ] end.

Section CM_C3Mid_2.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.

(* ---------- the block case (stages decompressLastBlock = 4, decompressBlock = 3: the same code) ---------- *)

Definition blk_cmd : statement :=
  ltac:(let b := eval cbv [f_ZSTD_decompressContinue fn_body] in (fn_body f_ZSTD_decompressContinue) in
        lazymatch b with context [LScons (Some 4) Sskip (LScons (Some 3) ?s3 ?rest)] =>
          let c := eval cbv [seq_of_labeled_statement] in (seq_of_labeled_statement (LScons (Some 3) s3 rest)) in
          exact c end).

(* what follows the switch on the block type *)
Definition blk_tail : statement :=
  ltac:(let c := eval cbv [blk_cmd] in blk_cmd in
        lazymatch c with Ssequence (Ssequence _ (Ssequence _ ?t)) ?b => exact (Ssequence t b) end).

Definition blk_pre (DENT: dent_pred) (TABS: tabs_pred) gv p (f: Z) (dd: option (ddx * val)) (l: hlay)
    (fs1: fstate) ts fp W (o: outarr) src (i: inwin) (n: Z) v_bp (pcs st: Z) : environ -> mpred :=
  PROP ( )
  LOCAL (temp _t'20 (Vint (Int.repr st)); temp _t'59 (Vlong (Int64.repr pcs));
         lvar _bp (Tstruct ___gp_blockProperties_t noattr) v_bp; gvars gv; temp _dctx p;
         temp _dst (offset_val (oa_d o) (oa_base o)); temp _dstCapacity (Vlong (Int64.repr (oa_cap o)));
         temp _src src; temp _srcSize (Vlong (Int64.repr n)))
  SEP (data_at (oa_sh o) (tarray tuchar (oa_N o)) (oa_c o) (oa_base o); pws_pred W;
       field_at Ews t_dctx (DOT _previousDstEnd) (fs_previousDstEnd fs1) p;
       field_at Ews t_dctx (DOT _gpDictCopy) (fs_gpDictCopy fs1) p;
       field_at Ews t_dctx (DOT _prefixStart) (fs_prefixStart fs1) p;
       field_at Ews t_dctx (DOT _virtualStart) (fs_virtualStart fs1) p;
       field_at Ews t_dctx (DOT _dictEnd) (fs_dictEnd fs1) p;
       field_at Ews t_dctx (DOT _expected) (fs_expected fs1) p;
       field_at Ews t_dctx (DOT _fParams) (fs_fParams fs1) p;
       field_at Ews t_dctx (DOT _processedCSize) (Vlong (Int64.add (Int64.repr pcs) (Int64.repr n))) p;
       field_at Ews t_dctx (DOT _decodedSize) (fs_decodedSize fs1) p;
       field_at Ews t_dctx (DOT _bType) (fs_bType fs1) p;
       field_at Ews t_dctx (DOT _stage) (Vint (Int.repr st)) p;
       xxh_field p (fs_xxh fs1);
       field_at Ews t_dctx (DOT _headerSize) (fs_headerSize fs1) p;
       field_at Ews t_dctx (DOT _validateChecksum) (fs_validateChecksum fs1) p;
       field_at Ews t_dctx (DOT _rleSize) (fs_rleSize fs1) p;
       field_at Ews t_dctx (DOT _isFrameDecompression) (fs_isFrameDecompression fs1) p;
       field_at Ews t_dctx (DOT _dictID) (fs_dictID fs1) p;
       field_at Ews t_dctx (DOT _ddictIsCold) (fs_ddictIsCold fs1) p;
       data_at_ Tsh (Tstruct ___gp_blockProperties_t noattr) v_bp;
       zstd_globals gv; cfg_fmt p f; cfg_lit p; TABS gv p (dd_ox dd) ts; dent_of DENT gv (dd_ox dd); lay_res l;
       in_res fp i).

(* the return of a case of the switch; XP: the exact claim of the case (C3XDefs.cont_exact1) *)
Definition dcc_R (DENT: dent_pred) (TABS: tabs_pred) gv p (f: Z) fp l (dd: option (ddx * val)) W (o: outarr)
    (i: inwin) (cold0: val) (fpar0: reptype t_fh) (XP: Z -> list val -> fstate -> option tstate -> Prop)
    : ret_assert :=
  frame_ret_assert
    (function_body_ret_assert tulong
      (EX r: Z, EX oc': list val, EX fs': fstate, EX tabs': option tstate,
       PROP (cont_res fp l dd o (iw_s i) r oc' fs' tabs';
             fs_ddictIsCold fs' = cold0 \/ fs_ddictIsCold fs' = Vint (Int.repr 0);
             is_error_code r = true -> fs_fParams fs' = fpar0;
             XP r oc' fs' tabs')
       RETURN (Vlong (Int64.repr r))
       SEP (zstd_globals gv; pws_pred W; cfg_fmt p f; cfg_lit p; frame_fields p fs';
            match tabs' with Some ts' => TABS gv p (dd_ox dd) ts' | None => EX lxb: list Z, tables_uninit p lxb end;
            dent_of DENT gv (dd_ox dd); lay_res l;
            data_at (oa_sh o) (tarray tuchar (oa_N o)) oc' (oa_base o); in_res fp i))%assert)
    (stackframe_of f_ZSTD_decompressContinue).

(* the exact claim moved to the front of a return's pure part (entailer! then leaves it first) *)
Lemma conj_rot5 (A B C X E: Prop) : (A /\ B /\ C /\ X /\ E) = (X /\ A /\ B /\ C /\ E).
Proof. apply prop_ext. tauto. Qed.

Lemma stage_if st x : (st = 3 \/ st = 4) -> (x = 1 <-> st = 4) -> (if x =? 1 then 4 else 3) = st.
Proof.
  intros Hs Hl. destruct (Z.eqb_spec x 1) as [E | E]; [symmetry; apply Hl; auto |].
  destruct Hs as [-> | ->]; [reflexivity | exfalso; apply E, Hl; reflexivity].
Qed.

End CM_C3Mid_2.

Ltac st_contra := exfalso; first
  [ lia
  | match goal with Hx: Int.repr ?a = Int.repr ?b |- _ =>
      apply (f_equal Int.unsigned) in Hx; rewrite !Int.unsigned_repr in Hx by rep_lia; lia end
  | match goal with Hx: Int.eq ?a ?b = true |- _ =>
      apply Int.same_if_eq in Hx; apply (f_equal Int.unsigned) in Hx;
      rewrite !Int.unsigned_repr in Hx by rep_lia; lia end
  | match goal with Hx: Int.eq ?a ?b = false |- _ => vm_compute in Hx; discriminate end
  | match goal with Hx: ?a <> ?a |- _ => apply Hx; reflexivity end ].

Section CM_C3Mid_3.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.

(* the part after the switch on the block type (a separate lemma: one Qed stays below the time limit) *)

(* the block header stage *)
Definition bhdr_cmd : statement :=
  ltac:(let b := eval cbv [f_ZSTD_decompressContinue fn_body] in (fn_body f_ZSTD_decompressContinue) in
        lazymatch b with context [LScons (Some 2) ?s2 ?rest] =>
          let c := eval cbv [seq_of_labeled_statement] in (seq_of_labeled_statement (LScons (Some 2) s2 rest)) in
          exact c end).

(* the history a compressed block is decoded behind is bytes *)
Lemma lay_H_bytes z l dd o :
  dd_gap -> lay_dd (lmove l (oa_base o) (oa_d o) (oa_cap o)) dd -> dd_model dd (zp_dm z) -> bytes_ok (lay_H z l o).
Proof.
  intros Hg Ld Dm. unfold lay_H, zp_hist.
  assert (Hn: dd_nodict dd -> bytes_ok (dm_content (zp_dm z))).
  { intros Hnd. rewrite (dd_nodict_model _ _ Hnd Dm). constructor. }
  destruct (lmove l (oa_base o) (oa_d o) (oa_cap o)) as [ | eb ec gp | b pe [[[eb ec] gp] |] | b ps pe e];
    cbn in Ld.
  - apply Hn, Ld.
  - destruct (Hg dd eb ec gp Ld) as (_ & _ & Hb). apply Hb, Dm.
  - destruct (Hg dd eb ec gp Ld) as (_ & _ & Hb). apply Hb, Dm.
  - apply Hn, Ld.
  - destruct e as [ | e1 elen | sh eb en ec e1 elen]; cbn.
    + apply Hn, Ld.
    + constructor.
    + destruct Ld as (_ & _ & _ & _ & gp & Hd). destruct (Hg dd eb ec gp Hd) as (_ & _ & Hb). apply Hb, Dm.
Qed.

End CM_C3Mid_3.
