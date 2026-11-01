(* valid_dict_api main, mode 0: helpers copied from VDA3M12Lemmas.v (M12_ renamed M0L_): buffer
   witnesses of the [dst | 1 | dict] layout, compspecs conversion of byte arrays, sr by fields, and one-shot
   decoding facts. *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.harness.valid_dict_api.WTopSpecs_valid_dict_api.
Require Import Zstd.proof.harness.valid_dict_api.VDA3Defs.
Require Import Zstd.proof.harness.writer.SeriesLemmas.
Require Import Zstd.proof.zstd.ApiBridge Zstd.proof.model.ParamsDflt.

Local Notation ZCS := Zstd.proof.zstd.Base.CompSpecs.
Local Notation HCS := Zstd.proof.harness.valid_dict_api.HOK_valid_dict_api.CompSpecs.

(* ---------- the model ---------- *)

Lemma M0L_err64 : is_error_code (err_code ZSTD_error_memory_allocation) = true /\
  error_of (err_code ZSTD_error_memory_allocation) = ZSTD_error_memory_allocation /\
  0 <= err_code ZSTD_error_memory_allocation <= Int64.max_unsigned.
Proof. vm_compute. repeat split; congruence. Qed.

Lemma M0L_ok_prefix_all wl fs : all_ok wl fs = true -> ok_prefix wl fs = fs.
Proof.
  induction fs as [|f fs IH]; simpl; auto.
  intros H. apply andb_prop in H as [H1 H2].
  destruct (wi_rejected wl f); simpl in H1; [discriminate|]. rewrite IH; auto.
Qed.

Lemma M0L_decode dm ws : series_facts dm ws -> wseries_wf ws ->
  decode_series dm no_wlim (ws_bytes ws) =
    if within_oneshot_b (ws_frames ws) then SOk (ws_content ws) else SDet.
Proof.
  intros Hf Hw. unfold decode_series. rewrite (series_frames_written dm ws no_wlim Hf).
  rewrite (within_oneshot_all_ok ws Hw).
  destruct (all_ok no_wlim (ws_frames ws)) eqn:E; [|reflexivity].
  rewrite M0L_ok_prefix_all by auto. rewrite (written_content dm ws Hf). reflexivity.
Qed.

Lemma M0L_check dm ws cap r out :
  series_facts dm ws -> wseries_wf ws ->
  oneshot_ok md_dflt (Some dm) (ws_bytes ws) cap r out ->
  (is_error_code r = false -> r = Zlength (ws_content ws) /\ sublist 0 r out = zbytes (ws_content ws)) /\
  (is_error_code r = true -> Zlength (ws_content ws) <= cap -> within_oneshot_b (ws_frames ws) = true ->
   r = err_code ZSTD_error_memory_allocation).
Proof.
  intros Hf Hw Ho. apply oneshot_ok_dflt in Ho. destruct Ho as [_ H].
  rewrite (M0L_decode dm ws Hf Hw) in H.
  destruct (within_oneshot_b (ws_frames ws)) eqn:E.
  - destruct H as [H1 H2]. split; auto.
    intros He Hc _. destruct (H2 He) as [Hlt|Hm]; [lia | exact Hm].
  - split; intros He; [rewrite H in He; discriminate | intros _ Hx; discriminate].
Qed.

(* the dictionary ZSTD_DCtx_loadDictionary_advanced(dctx, p, |b|, mm, t) leaves *)
Definition dr12 (mm t: Z) (p: val) (b: list Z) : dictref :=
  {| dr_src := if mm =? 1 then DSRef p else DSOwn; dr_raw := t =? 1; dr_once := false; dr_bytes := b |}.

Lemma M0L_model_auto wd : dict_facts wd -> dict_auto (wd_bytes wd) = Some (wd_model wd).
Proof.
  intros (_ & _ & Ha & _). unfold wd_model. destruct (dict_auto (wd_bytes wd)); [reflexivity | contradiction].
Qed.

Lemma M0L_model m mm t p wd : (m = 1 \/ m = 2) -> dict_facts wd -> (m = 1 -> wd_formatted wd = false) ->
  (m = 2 -> t = 1) -> dictref_model (Some (dr12 mm t p (wd_bytes wd))) = Some (vda_dm m wd).
Proof.
  intros Hm Hd Hf Ht. unfold dictref_model, dr12, vda_dm. cbn [dr_raw dr_bytes].
  destruct Hm as [-> | ->].
  - change (1 =? 2) with false. cbv iota.
    pose proof Hd as (_ & _ & _ & _ & _ & _ & Hr). destruct (Hr (Hf eq_refl)) as [Hw _].
    destruct (t =? 1); [rewrite Hw; reflexivity | apply M0L_model_auto; auto].
  - rewrite (Ht eq_refl). reflexivity.
Qed.

Lemma M0L_dd_res DD gv : dd_res DD gv (Zrepeat nullval 3) = emp.
Proof.
  unfold dd_res. simpl. rewrite !sepcon_emp. reflexivity.
Qed.

(* ---------- byte arrays at any two compspecs ---------- *)

Definition VB_cce (cs1 cs2: compspecs) : change_composite_env cs1 cs2 :=
  {| coeq := cs_preserve_env cs1 cs2;
     coeq_consistent := cs_preserve_env_consistent cs1 cs2 _ eq_refl;
     coeq_complete := cs_preserve_completeness cs1 cs2 _ eq_refl |}.

Lemma VB_cs (cs1 cs2: compspecs) sh n (v: list val) p :
  @data_at cs1 sh (tarray tuchar n) v p = @data_at cs2 sh (tarray tuchar n) v p.
Proof.
  pose proof (@data_at_change_composite cs1 cs2 (VB_cce cs1 cs2) sh (tarray tuchar n) v v
    (JMeq_refl _) ltac:(reflexivity)) as E. rewrite E; reflexivity.
Qed.

Lemma VB_cs_ (cs1 cs2: compspecs) sh n p :
  @data_at_ cs1 sh (tarray tuchar n) p = @data_at_ cs2 sh (tarray tuchar n) p.
Proof.
  pose proof (@data_at__change_composite cs1 cs2 (VB_cce cs1 cs2) sh (tarray tuchar n)
    ltac:(reflexivity)) as E. rewrite E; reflexivity.
Qed.

Lemma VB_split_bytes_ {cs: compspecs} sh m k p : 0 <= k <= m -> field_compatible (tarray tuchar m) [] p ->
  data_at_ sh (tarray tuchar m) p =
  (data_at_ sh (tarray tuchar k) p * data_at_ sh (tarray tuchar (m - k)) (offset_val k p))%logic.
Proof.
  intros Hk Hf. unfold tarray. rewrite (split2_data_at__Tarray_tuchar sh m k p Hk) by auto with field_compatible.
  rewrite field_address0_offset by auto with field_compatible. simpl. rewrite Z.mul_1_l, Z.add_0_l. reflexivity.
Qed.

(* ---------- the buffer witnesses: the slack of src's block and the gap byte between dst and dict ---------- *)

Definition VB_slack (src: val) (n: Z) : ptr_witness :=
  pw_bytes Ews (Z.max 1 n - n) (Zrepeat Vundef (Z.max 1 n - n)) (offset_val n src).
Definition VB_gap (buf: val) (cap: Z) : ptr_witness := pw_bytes Ews 1 [Vundef] (offset_val cap buf).
Definition VB_W (src: val) (n: Z) (buf: val) (cap: Z) : list ptr_witness := [VB_slack src n; VB_gap buf cap].

Lemma VB_pws src n buf cap : pws_pred (VB_W src n buf cap) =
  (@data_at_ ZCS Ews (tarray tuchar (Z.max 1 n - n)) (offset_val n src) *
   @data_at_ ZCS Ews (tarray tuchar 1) (offset_val cap buf))%logic.
Proof. unfold pws_pred, VB_W, map, fold_right. rewrite sepcon_emp. reflexivity. Qed.

Lemma VB_wvp_at {cs: compspecs} sh k p i q : readable_share sh -> 0 <= i <= k -> 0 < k -> q = offset_val i p ->
  data_at_ sh (tarray tuchar k) p |-- weak_valid_pointer q.
Proof.
  intros Hsh Hi Hk ->. eapply derives_trans; [apply data_at__memory_block_cancel|].
  simpl sizeof. rewrite Z.mul_1_l, Z.max_r by lia.
  apply memory_block_weak_valid_pointer; try lia. apply readable_nonidentity; auto.
Qed.

Lemma VB_ptr_eq b o i j : i = j -> offset_val i (Vptr b o) = offset_val j (Vptr b o).
Proof. intros ->; reflexivity. Qed.

Lemma VB_off_off b o i j : offset_val j (offset_val i (Vptr b o)) = offset_val (i + j) (Vptr b o).
Proof. rewrite offset_offset_val. reflexivity. Qed.

Lemma VB_off0 b o : Vptr b o = offset_val 0 (Vptr b o).
Proof. simpl. rewrite Ptrofs.add_zero. reflexivity. Qed.

Ltac VB_ptr_eq_tac :=
  first [ reflexivity
        | rewrite ?VB_off_off; apply VB_ptr_eq; lia
        | match goal with |- Vptr ?b ?o = _ => rewrite (VB_off0 b o) at 1 end; rewrite ?VB_off_off; apply VB_ptr_eq; lia ].

Ltac VB_piece k i :=
  eapply (VB_wvp_at _ k _ i); [auto | lia | lia | VB_ptr_eq_tac].

Lemma VB_buf_ok_src src n buf cap : isptr src -> 0 <= n -> buf_ok (VB_W src n buf cap) Ews n src.
Proof.
  intros Hp Hn. destruct src; try contradiction. unfold buf_ok. rewrite VB_pws.
  destruct (zlt 0 n).
  - apply andp_right; apply sepcon_weak_valid_pointer2.
    + VB_piece n 0.
    + VB_piece n n.
  - apply andp_right; apply sepcon_weak_valid_pointer1, sepcon_weak_valid_pointer1.
    + VB_piece (Z.max 1 n - n) 0.
    + VB_piece (Z.max 1 n - n) 0.
Qed.

Lemma VB_buf_ok_dst src n buf cap : isptr buf -> 0 <= cap -> buf_ok (VB_W src n buf cap) Ews cap buf.
Proof.
  intros Hp Hc. destruct buf; try contradiction. unfold buf_ok. rewrite VB_pws.
  destruct (zlt 0 cap).
  - apply andp_right; apply sepcon_weak_valid_pointer2.
    + VB_piece cap 0.
    + VB_piece cap cap.
  - apply andp_right; apply sepcon_weak_valid_pointer1, sepcon_weak_valid_pointer2.
    + VB_piece 1 0.
    + VB_piece 1 0.
Qed.

Lemma VB_buf_ok_dict src n buf cap dn : isptr buf -> 0 <= cap -> 0 <= dn ->
  buf_ok (VB_W src n buf cap) Ews dn (offset_val (cap + 1) buf).
Proof.
  intros Hp Hc Hd. destruct buf; try contradiction. unfold buf_ok. rewrite VB_pws.
  apply andp_right.
  - apply sepcon_weak_valid_pointer1, sepcon_weak_valid_pointer2. VB_piece 1 1.
  - destruct (zlt 0 dn).
    + apply sepcon_weak_valid_pointer2. VB_piece dn dn.
    + apply sepcon_weak_valid_pointer1, sepcon_weak_valid_pointer2. VB_piece 1 1.
Qed.

Lemma VB_sameblock_off buf k : isptr buf -> sameblock buf (offset_val k buf) = true.
Proof. intros Hp. destruct buf; try contradiction. simpl. unfold sameblock. apply peq_true. Qed.

Lemma VB_dict_ptr_ok src n buf cap dn : isptr buf -> 0 <= cap -> 0 <= dn ->
  field_compatible (tarray tuchar (cap + 1 + dn)) [] buf ->
  dict_ptr_ok (VB_W src n buf cap) Ews dn (offset_val (cap + 1) buf) Ews cap buf.
Proof.
  intros Hp Hc Hd Hf. left. split; [apply VB_sameblock_off; auto | split; [| apply VB_buf_ok_dict; auto]].
  destruct buf as [| | | | | b o]; try contradiction.
  destruct Hf as (_ & _ & Hsz & _). simpl in Hsz. rewrite Z.max_r in Hsz by lia.
  simpl. rewrite Ptrofs.add_unsigned. rewrite (Ptrofs.unsigned_repr (cap + 1)) by rep_lia.
  rewrite Ptrofs.unsigned_repr by rep_lia. lia.
Qed.

Lemma M0L_dict_buf_ok src n buf cap mm t b : isptr buf -> 0 <= cap ->
  field_compatible (tarray tuchar (cap + 1 + Zlength b)) [] buf ->
  dict_buf_ok (VB_W src n buf cap) Ews (Some (dr12 mm t (offset_val (cap + 1) buf) b)) Ews cap buf.
Proof.
  intros Hp Hc Hf. unfold dict_buf_ok, dr12. cbn [dr_src dr_bytes].
  destruct (mm =? 1); [| exact I]. apply VB_dict_ptr_ok; auto. apply Zlength_nonneg.
Qed.

Lemma VB_split3_ {cs: compspecs} sh c d p : 0 <= c -> 0 <= d ->
  field_compatible (tarray tuchar (c + 1 + d)) [] p ->
  data_at_ sh (tarray tuchar (c + 1 + d)) p =
  (data_at_ sh (tarray tuchar c) p * data_at_ sh (tarray tuchar 1) (offset_val c p) *
   data_at_ sh (tarray tuchar d) (offset_val (c + 1) p))%logic.
Proof.
  intros Hc Hd Hf.
  rewrite (VB_split_bytes_ sh (c + 1 + d) (c + 1) p) by (auto; lia).
  replace (c + 1 + d - (c + 1)) with d by lia.
  rewrite (VB_split_bytes_ sh (c + 1) c p).
  - replace (c + 1 - c) with 1 by lia. reflexivity.
  - lia.
  - eapply field_compatible_array_smaller0; [exact Hf | lia].
Qed.

Lemma VB_Zrepeat {cs: compspecs} sh c p :
  data_at_ sh (tarray tuchar c) p = data_at sh (tarray tuchar c) (Zrepeat Vundef c) p.
Proof. unfold data_at_, field_at_, data_at. reflexivity. Qed.

(* src from exact_copy: n bytes, then the slack (Vundef) of its max(1, n) block *)
Lemma VB_src_split src bs :
  field_compatible (tarray tuchar (Z.max 1 (Zlength bs))) [] src ->
  @data_at HCS Ews (tarray tuchar (Z.max 1 (Zlength bs))) (zbytes bs ++ Zrepeat Vundef (Z.max 1 (Zlength bs) - Zlength bs)) src
  = (@data_at ZCS Ews (tarray tuchar (Zlength bs)) (zbytes bs) src *
     @data_at_ ZCS Ews (tarray tuchar (Z.max 1 (Zlength bs) - Zlength bs)) (offset_val (Zlength bs) src))%logic.
Proof.
  intros Hf. pose proof (Zlength_nonneg bs).
  rewrite (VB_cs HCS ZCS).
  rewrite (split2_data_at_Tarray_app (Zlength bs) (Z.max 1 (Zlength bs)) Ews tuchar).
  - rewrite VB_Zrepeat. f_equal. f_equal.
    assert (Hf': @field_compatible ZCS (tarray tuchar (Z.max 1 (Zlength bs))) [] src).
    { apply (@field_compatible_change_composite HCS ZCS (VB_cce HCS ZCS)); [reflexivity | exact Hf]. }
    rewrite field_address0_offset by auto with field_compatible.
    simpl. f_equal. lia.
  - exact (Zlength_map _ _ _ _).
  - rewrite Zlength_Zrepeat; lia.
Qed.

(* VDA_A's buffers, converted to the decoder's compspecs and the witnesses folded *)
Lemma M0L_bufs src buf ws wd cap : 0 <= cap ->
  field_compatible (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws)))) [] src ->
  field_compatible (tarray tuchar (cap + 1 + Zlength (wd_bytes wd))) [] buf ->
  @data_at HCS Ews (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws))))
    (zbytes (ws_bytes ws) ++ Zrepeat Vundef (Z.max 1 (Zlength (ws_bytes ws)) - Zlength (ws_bytes ws))) src *
  @data_at_ HCS Ews (tarray tuchar (cap + 1)) buf *
  @data_at HCS Ews (tarray tuchar (Zlength (wd_bytes wd))) (zbytes (wd_bytes wd)) (offset_val (cap + 1) buf)
  |-- pws_pred (VB_W src (Zlength (ws_bytes ws)) buf cap) *
      @data_at ZCS Ews (tarray tuchar (Zlength (ws_bytes ws))) (zbytes (ws_bytes ws)) src *
      @data_at_ ZCS Ews (tarray tuchar cap) buf *
      @data_at ZCS Ews (tarray tuchar (Zlength (wd_bytes wd))) (zbytes (wd_bytes wd)) (offset_val (cap + 1) buf).
Proof.
  intros Hc Hfs Hfb. pose proof (Zlength_nonneg (wd_bytes wd)).
  rewrite (VB_src_split src (ws_bytes ws) Hfs).
  rewrite (VB_split_bytes_ Ews (cap + 1) cap buf) by first [lia | eapply field_compatible_array_smaller0; [exact Hfb | lia]].
  replace (cap + 1 - cap) with 1 by lia.
  rewrite VB_pws, !(VB_cs_ HCS ZCS), (VB_cs HCS ZCS). cancel.
Qed.

(* everything back for free(src) and free(buf) *)
Lemma VB_final_merge src n buf cap dn out v vs :
  0 <= n -> 0 <= cap -> 0 <= dn ->
  field_compatible (tarray tuchar (Z.max 1 n)) [] src ->
  field_compatible (tarray tuchar (cap + 1 + dn)) [] buf ->
  pws_pred (VB_W src n buf cap) * @data_at ZCS Ews (tarray tuchar cap) out buf *
  @data_at ZCS Ews (tarray tuchar dn) v (offset_val (cap + 1) buf) *
  @data_at ZCS Ews (tarray tuchar n) vs src
  |-- @data_at_ HCS Ews (tarray tuchar (Z.max 1 n)) src * @data_at_ HCS Ews (tarray tuchar (cap + 1 + dn)) buf.
Proof.
  intros Hn Hc Hd Hfs Hfb.
  rewrite (VB_split_bytes_ Ews (Z.max 1 n) n src) by (auto; lia).
  rewrite (VB_split3_ Ews cap dn buf) by auto.
  rewrite VB_pws, !(VB_cs_ HCS ZCS).
  sep_apply (data_at_data_at_ Ews (tarray tuchar cap) out buf).
  sep_apply (data_at_data_at_ Ews (tarray tuchar dn) v (offset_val (cap + 1) buf)).
  sep_apply (data_at_data_at_ Ews (tarray tuchar n) vs src).
  cancel.
Qed.

(* ---------- sr by fields ---------- *)

Lemma VB_bytes_split sh (bs: list Z) p : Zlength bs <= 2 ^ 19 ->
  @field_at HCS sh t_wseries (DOT _bytes) (zbytes bs ++ Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength bs)) p =
  (@data_at HCS sh (tarray tuchar (Zlength bs)) (zbytes bs) (@field_address HCS t_wseries (DOT _bytes) p) *
   @data_at HCS sh (tarray tuchar (2 ^ 19 - Zlength bs)) (Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength bs))
     (@field_address0 HCS (tarray tuchar (2 ^ 19)) (SUB (Zlength bs)) (@field_address HCS t_wseries (DOT _bytes) p)))%logic.
Proof.
  intros Hn. rewrite field_at_data_at.
  change (@nested_field_type HCS t_wseries (DOT _bytes)) with (tarray tuchar (2 ^ 19)).
  apply split2_data_at_Tarray_app.
  - rewrite Zlength_map. reflexivity.
  - rewrite Zlength_Zrepeat; [reflexivity|]. pose proof (Zlength_nonneg bs). lia.
Qed.

Definition VB_sr_rest (ws: wseries) (p: val) : mpred :=
  (@data_at HCS Ews (tarray tuchar (Zlength (ws_bytes ws))) (zbytes (ws_bytes ws)) (@field_address HCS t_wseries (DOT _bytes) p) *
   @data_at HCS Ews (tarray tuchar (2 ^ 19 - Zlength (ws_bytes ws))) (Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength (ws_bytes ws)))
     (@field_address0 HCS (tarray tuchar (2 ^ 19)) (SUB (Zlength (ws_bytes ws))) (@field_address HCS t_wseries (DOT _bytes) p)) *
   @field_at HCS Ews t_wseries (DOT _f)
     (map winfo_val (ws_frames ws) ++ Zrepeat (winfo_val winfo0) (4 - Zlength (ws_frames ws))) p *
   @field_at HCS Ews t_wseries (DOT _nframes) (vu (Zlength (ws_frames ws))) p *
   spacer Ews 786932 786936 p)%logic.

Definition VB_Rn (ws: wseries) (p: val) : mpred :=
  @field_at HCS Ews t_wseries (DOT _n) (vl (Zlength (ws_bytes ws))) p.
Definition VB_Rc (ws: wseries) (p: val) : mpred :=
  @field_at HCS Ews t_wseries (DOT _content)
     (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws))) p.
Definition VB_Rcn (ws: wseries) (p: val) : mpred :=
  @field_at HCS Ews t_wseries (DOT _content_n) (vl (Zlength (ws_content ws))) p.

Lemma VB_ws_fold ws p : Zlength (ws_bytes ws) <= 2 ^ 19 ->
  VB_sr_rest ws p * VB_Rn ws p * VB_Rc ws p * VB_Rcn ws p |-- @data_at HCS Ews t_wseries (wseries_val ws) p.
Proof.
  intros Hn. unfold VB_sr_rest, VB_Rn, VB_Rc, VB_Rcn. rewrite <- VB_bytes_split by exact Hn.
  unfold_data_at (@data_at HCS _ _ _ p). cbn [fst snd wseries_val]. cancel.
Qed.

Lemma VB_ws_unfold ws p : Zlength (ws_bytes ws) <= 2 ^ 19 ->
  @data_at HCS Ews t_wseries (wseries_val ws) p |-- VB_sr_rest ws p * VB_Rn ws p * VB_Rc ws p * VB_Rcn ws p.
Proof.
  intros Hn. unfold VB_sr_rest, VB_Rn, VB_Rc, VB_Rcn. unfold_data_at (@data_at HCS _ _ _ p). cbn [fst snd wseries_val].
  rewrite (VB_bytes_split Ews (ws_bytes ws) p Hn). cancel.
Qed.

(* the bytes delivered and the content, at index i *)
Lemma VB_out_at (c: list Z) r out i : sublist 0 r out = zbytes c -> r = Zlength c -> 0 <= i < r ->
  Znth i out = Vint (Int.repr (Znth i c)).
Proof.
  intros Hs Hr Hi. replace (Znth i out) with (Znth (i + 0) out) by (rewrite Z.add_0_r; reflexivity).
  rewrite <- (Znth_sublist 0 i r out) by lia. rewrite Hs. rewrite Znth_map by lia. reflexivity.
Qed.

Lemma VI_content_split ws p : Zlength (ws_content ws) <= 2 ^ 18 -> @field_compatible HCS t_wseries (DOT _content) p ->
  VB_Rc ws p =
  (@data_at HCS Ews (tarray tuchar (Zlength (ws_content ws))) (zbytes (ws_content ws)) (@field_address HCS t_wseries (DOT _content) p) *
   @data_at HCS Ews (tarray tuchar (262144 - Zlength (ws_content ws))) (Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws)))
     (@field_address0 HCS (tarray tuchar 262144) (SUB (Zlength (ws_content ws))) (@field_address HCS t_wseries (DOT _content) p)))%logic.
Proof.
  intros Hn Hfc. unfold VB_Rc. rewrite field_at_data_at.
  change (@nested_field_type HCS t_wseries (DOT _content)) with (tarray tuchar 262144).
  apply split2_data_at_Tarray_app; rewrite ?Zlength_map, ?Zlength_Zrepeat; rep_lia.
Qed.

Lemma VB_dict_val buf cap : isptr buf -> 0 <= cap <= Int64.max_unsigned - 1 ->
  force_val (sem_binary_operation' Oadd (tptr tuchar) tint
     (eval_binop Oadd (tptr tuchar) tulong buf (Vlong (Int64.repr cap))) (Vint (Int.repr 1)))
  = offset_val (cap + 1) buf.
Proof.
  intros Hp Hc. destruct buf; try contradiction. simpl.
  rewrite !(Ptrofs.mul_commut (Ptrofs.repr 1)), !Ptrofs.mul_one.
  rewrite Ptrofs.add_assoc.
  replace (Ptrofs.of_int64 (Int64.repr cap)) with (Ptrofs.repr cap)
    by (unfold Ptrofs.of_int64; rewrite Int64.unsigned_repr by rep_lia; reflexivity).
  rewrite ptrofs_add_repr. reflexivity.
Qed.
