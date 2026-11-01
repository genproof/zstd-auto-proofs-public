(* valid_dict_api main: mode 3 (ZSTD_dct_fullDict refused on raw content) and mode 4
   (ZSTD_DCtx_refPrefix_advanced and one-shot decoding of one frame) (VDA3Defs.VDA_mode_ok). *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.harness.valid_dict_api.WTopSpecs_valid_dict_api.
Require Import Zstd.proof.harness.valid_dict_api.VDA3Defs.
Require Import Zstd.proof.harness.writer.SeriesLemmas.
Require Import Zstd.proof.zstd.ApiBridge.
Require Import Zstd.proof.zstd.NullBuf.

Local Notation ZCS := Zstd.proof.zstd.Base.CompSpecs.
Local Notation HCS := Zstd.proof.harness.valid_dict_api.HOK_valid_dict_api.CompSpecs.

(* ---------- model facts ---------- *)

Lemma M34_dentropy_huf b st e : load_dentropy b = Some (st, e) -> st_huf st <> None.
Proof.
  unfold load_dentropy. intros H.
  repeat match type of H with
  | context [if ?c then _ else _] => destruct c
  | context [match ?x with _ => _ end] => destruct x as [[[? ?] ?]|] || destruct x as [[? ?]|] || destruct x
  end; try discriminate.
  inv H. cbn. discriminate.
Qed.

(* a raw-content dictionary of the writer does not start with the magic number *)
Lemma M34_not_formatted wd : dict_facts wd -> wd_formatted wd = false -> dict_formatted (wd_bytes wd) = false.
Proof.
  intros (_ & Hl & Ha & _ & _ & _ & Hr) Hf. destruct (Hr Hf) as [Hm _].
  unfold dict_formatted. destruct (8 <=? Zlength (wd_bytes wd)) eqn:E1; [| reflexivity].
  destruct (le_field (wd_bytes wd) 0 4 =? ZSTD_MAGIC_DICTIONARY) eqn:E2; [| reflexivity].
  exfalso. unfold wd_model in Hm. unfold dict_auto in Ha, Hm.
  rewrite (proj2 (Z.ltb_ge _ _)) in Ha, Hm by lia. rewrite E2 in Ha, Hm. cbn [negb] in Ha, Hm.
  destruct (load_dentropy (wd_bytes wd)) as [[st e]|] eqn:E3; [| contradiction].
  apply M34_dentropy_huf in E3. apply (f_equal dm_state) in Hm. cbn in Hm. subst st. cbn in E3. congruence.
Qed.

(* ---------- after WMain3_valid_dict.v (valid_dict's main on API v3): the one-shot decoding's model, buffer witnesses, sr's fields ---------- *)

Lemma M34v_ok_prefix_all wl fs : all_ok wl fs = true -> ok_prefix wl fs = fs.
Proof.
  induction fs as [|f fs IH]; simpl; auto.
  intros H. apply andb_prop in H as [H1 H2].
  destruct (wi_rejected wl f); simpl in H1; [discriminate|]. rewrite IH; auto.
Qed.

Lemma M34v_decode dm ws : series_facts dm ws -> wseries_wf ws ->
  decode_series dm no_wlim (ws_bytes ws) =
    if within_oneshot_b (ws_frames ws) then SOk (ws_content ws) else SDet.
Proof.
  intros Hf Hw. unfold decode_series. rewrite (series_frames_written dm ws no_wlim Hf).
  rewrite (within_oneshot_all_ok ws Hw).
  destruct (all_ok no_wlim (ws_frames ws)) eqn:E; [|reflexivity].
  rewrite M34v_ok_prefix_all by auto. rewrite (written_content dm ws Hf). reflexivity.
Qed.

Lemma M34v_check dm ws cap r out :
  series_facts dm ws -> wseries_wf ws ->
  oneshot_ok md_dflt (Some dm) (ws_bytes ws) cap r out ->
  (is_error_code r = false -> r = Zlength (ws_content ws) /\ sublist 0 r out = zbytes (ws_content ws)) /\
  (is_error_code r = true -> Zlength (ws_content ws) <= cap -> within_oneshot_b (ws_frames ws) = true ->
   r = err_code ZSTD_error_memory_allocation).
Proof.
  intros Hf Hw Ho. apply oneshot_ok_dflt in Ho. destruct Ho as [_ H]. rewrite (M34v_decode dm ws Hf Hw) in H.
  destruct (within_oneshot_b (ws_frames ws)) eqn:E.
  - destruct H as [H1 H2]. split; auto.
    intros He Hc _. destruct (H2 He) as [Hlt|Hm]; [lia | exact Hm].
  - split; intros He; [rewrite H in He; discriminate | intros _ Hx; discriminate].
Qed.

Lemma M34_err64 : is_error_code (err_code ZSTD_error_memory_allocation) = true /\
  error_of (err_code ZSTD_error_memory_allocation) = ZSTD_error_memory_allocation /\
  0 <= err_code ZSTD_error_memory_allocation <= Int64.max_unsigned.
Proof. vm_compute. repeat split; congruence. Qed.
Definition M34B_cce (cs1 cs2: compspecs) : change_composite_env cs1 cs2 :=
  {| coeq := cs_preserve_env cs1 cs2;
     coeq_consistent := cs_preserve_env_consistent cs1 cs2 _ eq_refl;
     coeq_complete := cs_preserve_completeness cs1 cs2 _ eq_refl |}.

Lemma M34B_cs (cs1 cs2: compspecs) sh n (v: list val) p :
  @data_at cs1 sh (tarray tuchar n) v p = @data_at cs2 sh (tarray tuchar n) v p.
Proof.
  pose proof (@data_at_change_composite cs1 cs2 (M34B_cce cs1 cs2) sh (tarray tuchar n) v v
    (JMeq_refl _) ltac:(reflexivity)) as E. rewrite E; reflexivity.
Qed.

Lemma M34B_cs_ (cs1 cs2: compspecs) sh n p :
  @data_at_ cs1 sh (tarray tuchar n) p = @data_at_ cs2 sh (tarray tuchar n) p.
Proof.
  pose proof (@data_at__change_composite cs1 cs2 (M34B_cce cs1 cs2) sh (tarray tuchar n)
    ltac:(reflexivity)) as E. rewrite E; reflexivity.
Qed.

Lemma M34B_split_bytes_ {cs: compspecs} sh m k p : 0 <= k <= m -> field_compatible (tarray tuchar m) [] p ->
  data_at_ sh (tarray tuchar m) p =
  (data_at_ sh (tarray tuchar k) p * data_at_ sh (tarray tuchar (m - k)) (offset_val k p))%logic.
Proof.
  intros Hk Hf. unfold tarray. rewrite (split2_data_at__Tarray_tuchar sh m k p Hk) by auto with field_compatible.
  rewrite field_address0_offset by auto with field_compatible. simpl. rewrite Z.mul_1_l, Z.add_0_l. reflexivity.
Qed.

(* the slack of src's block and the gap byte between dst and dict *)
Definition M34B_slack (src: val) (n: Z) : ptr_witness :=
  pw_bytes Ews (Z.max 1 n - n) (Zrepeat Vundef (Z.max 1 n - n)) (offset_val n src).
Definition M34B_gap (buf: val) (cap: Z) : ptr_witness := pw_bytes Ews 1 [Vundef] (offset_val cap buf).
Definition M34B_W (src: val) (n: Z) (buf: val) (cap: Z) : list ptr_witness := [M34B_slack src n; M34B_gap buf cap].

Lemma M34B_pws src n buf cap : pws_pred (M34B_W src n buf cap) =
  (@data_at_ ZCS Ews (tarray tuchar (Z.max 1 n - n)) (offset_val n src) *
   @data_at_ ZCS Ews (tarray tuchar 1) (offset_val cap buf))%logic.
Proof. unfold pws_pred, M34B_W, map, fold_right. rewrite sepcon_emp. reflexivity. Qed.

Lemma M34B_wvp_at {cs: compspecs} sh k p i q : readable_share sh -> 0 <= i <= k -> 0 < k -> q = offset_val i p ->
  data_at_ sh (tarray tuchar k) p |-- weak_valid_pointer q.
Proof.
  intros Hsh Hi Hk ->. eapply derives_trans; [apply data_at__memory_block_cancel|].
  simpl sizeof. rewrite Z.mul_1_l, Z.max_r by lia.
  apply memory_block_weak_valid_pointer; try lia. apply readable_nonidentity; auto.
Qed.

Lemma M34B_ptr_eq b o i j : i = j -> offset_val i (Vptr b o) = offset_val j (Vptr b o).
Proof. intros ->; reflexivity. Qed.

Lemma M34B_off_off b o i j : offset_val j (offset_val i (Vptr b o)) = offset_val (i + j) (Vptr b o).
Proof. rewrite offset_offset_val. reflexivity. Qed.

Lemma M34B_off0 b o : Vptr b o = offset_val 0 (Vptr b o).
Proof. simpl. rewrite Ptrofs.add_zero. reflexivity. Qed.

Ltac M34B_ptr_eq_tac :=
  first [ reflexivity
        | rewrite ?M34B_off_off; apply M34B_ptr_eq; lia
        | match goal with |- Vptr ?b ?o = _ => rewrite (M34B_off0 b o) at 1 end; rewrite ?M34B_off_off; apply M34B_ptr_eq; lia ].

Ltac M34B_piece k i :=
  eapply (M34B_wvp_at _ k _ i); [auto | lia | lia | M34B_ptr_eq_tac].

Lemma M34B_buf_ok_src src n buf cap : isptr src -> 0 <= n -> buf_ok (M34B_W src n buf cap) Ews n src.
Proof.
  intros Hp Hn. destruct src; try contradiction. unfold buf_ok. rewrite M34B_pws.
  destruct (zlt 0 n).
  - apply andp_right; apply sepcon_weak_valid_pointer2.
    + M34B_piece n 0.
    + M34B_piece n n.
  - apply andp_right; apply sepcon_weak_valid_pointer1, sepcon_weak_valid_pointer1.
    + M34B_piece (Z.max 1 n - n) 0.
    + M34B_piece (Z.max 1 n - n) 0.
Qed.

Lemma M34B_buf_ok_dst src n buf cap : isptr buf -> 0 <= cap -> buf_ok (M34B_W src n buf cap) Ews cap buf.
Proof.
  intros Hp Hc. destruct buf; try contradiction. unfold buf_ok. rewrite M34B_pws.
  destruct (zlt 0 cap).
  - apply andp_right; apply sepcon_weak_valid_pointer2.
    + M34B_piece cap 0.
    + M34B_piece cap cap.
  - apply andp_right; apply sepcon_weak_valid_pointer1, sepcon_weak_valid_pointer2.
    + M34B_piece 1 0.
    + M34B_piece 1 0.
Qed.

Lemma M34B_buf_ok_dict src n buf cap dn : isptr buf -> 0 <= cap -> 0 <= dn ->
  buf_ok (M34B_W src n buf cap) Ews dn (offset_val (cap + 1) buf).
Proof.
  intros Hp Hc Hd. destruct buf; try contradiction. unfold buf_ok. rewrite M34B_pws.
  apply andp_right.
  - apply sepcon_weak_valid_pointer1, sepcon_weak_valid_pointer2. M34B_piece 1 1.
  - destruct (zlt 0 dn).
    + apply sepcon_weak_valid_pointer2. M34B_piece dn dn.
    + apply sepcon_weak_valid_pointer1, sepcon_weak_valid_pointer2. M34B_piece 1 1.
Qed.

Lemma M34B_sameblock_off buf k : isptr buf -> sameblock buf (offset_val k buf) = true.
Proof. intros Hp. destruct buf; try contradiction. simpl. unfold sameblock. apply peq_true. Qed.

Lemma M34B_dict_ptr_ok src n buf cap dn : isptr buf -> 0 <= cap -> 0 <= dn ->
  field_compatible (tarray tuchar (cap + 1 + dn)) [] buf ->
  dict_ptr_ok (M34B_W src n buf cap) Ews dn (offset_val (cap + 1) buf) Ews cap buf.
Proof.
  intros Hp Hc Hd Hf. left. split; [apply M34B_sameblock_off; auto | split; [| apply M34B_buf_ok_dict; auto]].
  destruct buf as [| | | | | b o]; try contradiction.
  destruct Hf as (_ & _ & Hsz & _). simpl in Hsz. rewrite Z.max_r in Hsz by lia.
  simpl. rewrite Ptrofs.add_unsigned. rewrite (Ptrofs.unsigned_repr (cap + 1)) by rep_lia.
  rewrite Ptrofs.unsigned_repr by rep_lia. lia.
Qed.

(* a buffer of n > 0 bytes needs no witness *)
Lemma M34B_buf_ok_nil n p : 0 < n -> buf_ok [] Ews n p.
Proof.
  intros Hn. unfold buf_ok, pws_pred. simpl. rewrite emp_sepcon.
  destruct (isptr_dec p) as [Hp|Hp].
  - destruct p; try contradiction. apply andp_right.
    + M34B_piece n 0.
    + M34B_piece n n.
  - rewrite data_at__isptr. normalize.
Qed.

Lemma M34B_split3_ {cs: compspecs} sh c d p : 0 <= c -> 0 <= d ->
  field_compatible (tarray tuchar (c + 1 + d)) [] p ->
  data_at_ sh (tarray tuchar (c + 1 + d)) p =
  (data_at_ sh (tarray tuchar c) p * data_at_ sh (tarray tuchar 1) (offset_val c p) *
   data_at_ sh (tarray tuchar d) (offset_val (c + 1) p))%logic.
Proof.
  intros Hc Hd Hf.
  rewrite (M34B_split_bytes_ sh (c + 1 + d) (c + 1) p) by (auto; lia).
  replace (c + 1 + d - (c + 1)) with d by lia.
  rewrite (M34B_split_bytes_ sh (c + 1) c p).
  - replace (c + 1 - c) with 1 by lia. reflexivity.
  - lia.
  - eapply field_compatible_array_smaller0; [exact Hf | lia].
Qed.

Lemma M34B_Zrepeat {cs: compspecs} sh c p :
  data_at_ sh (tarray tuchar c) p = data_at sh (tarray tuchar c) (Zrepeat Vundef c) p.
Proof. unfold data_at_, field_at_, data_at. reflexivity. Qed.

Lemma M34B_bytes_ok l : Forall (fun b => 0 <= b <= Byte.max_unsigned) l -> bytes_ok l.
Proof. unfold bytes_ok, is_byte. apply Forall_impl. intros x Hx. rep_lia. Qed.

(* src from exact_copy: n bytes, then the slack (Vundef) of its max(1, n) block *)
Lemma M34B_src_split src bs : 
  field_compatible (tarray tuchar (Z.max 1 (Zlength bs))) [] src ->
  @data_at HCS Ews (tarray tuchar (Z.max 1 (Zlength bs))) (zbytes bs ++ Zrepeat Vundef (Z.max 1 (Zlength bs) - Zlength bs)) src
  = (@data_at ZCS Ews (tarray tuchar (Zlength bs)) (zbytes bs) src *
     @data_at_ ZCS Ews (tarray tuchar (Z.max 1 (Zlength bs) - Zlength bs)) (offset_val (Zlength bs) src))%logic.
Proof.
  intros Hf. pose proof (Zlength_nonneg bs).
  rewrite (M34B_cs HCS ZCS).
  rewrite (split2_data_at_Tarray_app (Zlength bs) (Z.max 1 (Zlength bs)) Ews tuchar).
  - rewrite M34B_Zrepeat. f_equal. f_equal.
    assert (Hf': @field_compatible ZCS (tarray tuchar (Z.max 1 (Zlength bs))) [] src).
    { apply (@field_compatible_change_composite HCS ZCS (M34B_cce HCS ZCS)); [reflexivity | exact Hf]. }
    rewrite field_address0_offset by auto with field_compatible.
    simpl. f_equal. lia.
  - exact (Zlength_map _ _ _ _).
  - rewrite Zlength_Zrepeat; lia.
Qed.

Lemma M34B_wit_fold src n buf cap :
  @data_at_ ZCS Ews (tarray tuchar (Z.max 1 n - n)) (offset_val n src) *
  @data_at_ ZCS Ews (tarray tuchar 1) (offset_val cap buf) |-- pws_pred (M34B_W src n buf cap).
Proof. rewrite M34B_pws. auto. Qed.

Lemma M34B_wit_unfold src n buf cap :
  pws_pred (M34B_W src n buf cap) |--
  @data_at_ ZCS Ews (tarray tuchar (Z.max 1 n - n)) (offset_val n src) *
  @data_at_ ZCS Ews (tarray tuchar 1) (offset_val cap buf).
Proof. rewrite M34B_pws. auto. Qed.

(* everything back for free(src) and free(buf) *)
Lemma M34B_final_merge src n buf cap dn out v vs :
  0 <= n -> 0 <= cap -> 0 <= dn ->
  field_compatible (tarray tuchar (Z.max 1 n)) [] src ->
  field_compatible (tarray tuchar (cap + 1 + dn)) [] buf ->
  pws_pred (M34B_W src n buf cap) * @data_at ZCS Ews (tarray tuchar cap) out buf *
  @data_at ZCS Ews (tarray tuchar dn) v (offset_val (cap + 1) buf) *
  @data_at ZCS Ews (tarray tuchar n) vs src
  |-- @data_at_ HCS Ews (tarray tuchar (Z.max 1 n)) src * @data_at_ HCS Ews (tarray tuchar (cap + 1 + dn)) buf.
Proof.
  intros Hn Hc Hd Hfs Hfb.
  rewrite (M34B_split_bytes_ Ews (Z.max 1 n) n src) by (auto; lia).
  rewrite (M34B_split3_ Ews cap dn buf) by auto.
  rewrite M34B_pws, !(M34B_cs_ HCS ZCS).
  sep_apply (data_at_data_at_ Ews (tarray tuchar cap) out buf).
  sep_apply (data_at_data_at_ Ews (tarray tuchar dn) v (offset_val (cap + 1) buf)).
  sep_apply (data_at_data_at_ Ews (tarray tuchar n) vs src).
  cancel.
Qed.

Lemma M34B_dict_val buf cap : isptr buf -> 0 <= cap <= Int64.max_unsigned - 1 ->
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

(* sr's bytes: the series' bytes for exact_copy, and the zeros after them *)
Lemma M34B_bytes_split sh (bs: list Z) p : Zlength bs <= 2 ^ 19 ->
  field_at sh t_wseries (DOT _bytes) (zbytes bs ++ Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength bs)) p =
  (data_at sh (tarray tuchar (Zlength bs)) (zbytes bs) (field_address t_wseries (DOT _bytes) p) *
   data_at sh (tarray tuchar (2 ^ 19 - Zlength bs)) (Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength bs))
     (field_address0 (tarray tuchar (2 ^ 19)) (SUB (Zlength bs)) (field_address t_wseries (DOT _bytes) p)))%logic.
Proof.
  intros Hn. rewrite field_at_data_at.
  change (nested_field_type t_wseries (DOT _bytes)) with (tarray tuchar (2 ^ 19)).
  apply split2_data_at_Tarray_app.
  - rewrite Zlength_map. reflexivity.
  - rewrite Zlength_Zrepeat; [reflexivity|]. pose proof (Zlength_nonneg bs). lia.
Qed.

(* sr whole (within_oneshot) and by fields *)
Definition M34B_sr_rest (ws: wseries) (p: val) : mpred :=
  (@data_at HCS Ews (tarray tuchar (Zlength (ws_bytes ws))) (zbytes (ws_bytes ws)) (@field_address HCS t_wseries (DOT _bytes) p) *
   @data_at HCS Ews (tarray tuchar (2 ^ 19 - Zlength (ws_bytes ws))) (Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength (ws_bytes ws)))
     (@field_address0 HCS (tarray tuchar (2 ^ 19)) (SUB (Zlength (ws_bytes ws))) (@field_address HCS t_wseries (DOT _bytes) p)) *
   @field_at HCS Ews t_wseries (DOT _f)
     (map winfo_val (ws_frames ws) ++ Zrepeat (winfo_val winfo0) (4 - Zlength (ws_frames ws))) p *
   @field_at HCS Ews t_wseries (DOT _nframes) (vu (Zlength (ws_frames ws))) p *
   spacer Ews 786932 786936 p)%logic.

Lemma M34B_ws_fold ws p : Zlength (ws_bytes ws) <= 2 ^ 19 ->
  (M34B_sr_rest ws p *
   @field_at HCS Ews t_wseries (DOT _n) (vl (Zlength (ws_bytes ws))) p *
   @field_at HCS Ews t_wseries (DOT _content)
     (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws))) p *
   @field_at HCS Ews t_wseries (DOT _content_n) (vl (Zlength (ws_content ws))) p) |--
  @data_at HCS Ews t_wseries (wseries_val ws) p.
Proof.
  intros Hn. unfold M34B_sr_rest. rewrite <- M34B_bytes_split by exact Hn.
  unfold_data_at (data_at _ _ _ p). cbn [fst snd wseries_val]. cancel.
Qed.

Lemma M34B_ws_unfold ws p : Zlength (ws_bytes ws) <= 2 ^ 19 ->
  @data_at HCS Ews t_wseries (wseries_val ws) p |--
  (M34B_sr_rest ws p *
   @field_at HCS Ews t_wseries (DOT _n) (vl (Zlength (ws_bytes ws))) p *
   @field_at HCS Ews t_wseries (DOT _content)
     (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws))) p *
   @field_at HCS Ews t_wseries (DOT _content_n) (vl (Zlength (ws_content ws))) p).
Proof.
  intros Hn. unfold M34B_sr_rest. unfold_data_at (data_at _ _ _ p). cbn [fst snd wseries_val].
  rewrite (M34B_bytes_split Ews (ws_bytes ws) p Hn). cancel.
Qed.

(* the bytes delivered and the content, at index i *)
Lemma M34B_out_at (c: list Z) r out i : sublist 0 r out = zbytes c -> r = Zlength c -> 0 <= i < r ->
  Znth i out = Vint (Int.repr (Znth i c)).
Proof.
  intros Hs Hr Hi. replace (Znth i out) with (Znth (i + 0) out) by (rewrite Z.add_0_r; reflexivity).
  rewrite <- (Znth_sublist 0 i r out) by lia. rewrite Hs. rewrite Znth_map by lia. reflexivity.
Qed.

Lemma M34B_content_at (c: list Z) k i : 0 <= i < Zlength c -> 
  Znth i (zbytes c ++ Zrepeat (Vint Int.zero) k) = Vint (Int.repr (Znth i c)).
Proof.
  intros Hi. rewrite app_Znth1 by (rewrite Zlength_map; lia). rewrite Znth_map by lia. reflexivity.
Qed.

(* the dictionary copy: dict[0..i) written *)
Lemma M34B_copy_step (b: list Z) i n : 0 <= i < n -> Zlength b = n ->
  upd_Znth i (zbytes (sublist 0 i b) ++ Zrepeat Vundef (n - i)) (Vint (Int.repr (Znth i b))) =
  zbytes (sublist 0 (i + 1) b) ++ Zrepeat Vundef (n - (i + 1)).
Proof.
  intros Hi Hn.
  rewrite upd_Znth_app2 by (rewrite Zlength_map, Zlength_sublist, Zlength_Zrepeat; lia).
  rewrite Zlength_map, Zlength_sublist by lia. replace (i - (i - 0)) with 0 by lia.
  replace (n - i) with (1 + (n - (i + 1))) by lia.
  rewrite <- Zrepeat_app by lia. rewrite upd_Znth_app1 by (rewrite Zlength_Zrepeat; lia).
  change (Zrepeat Vundef 1) with [Vundef]. rewrite upd_Znth0.
  rewrite (sublist_split 0 i (i + 1) b) by lia. rewrite map_app, <- app_assoc.
  rewrite sublist_len_1 by lia. reflexivity.
Qed.

Lemma M34B_rest_fold ws p :
  (@data_at HCS Ews (tarray tuchar (Zlength (ws_bytes ws))) (zbytes (ws_bytes ws)) (@field_address HCS t_wseries (DOT _bytes) p) *
   @data_at HCS Ews (tarray tuchar (2 ^ 19 - Zlength (ws_bytes ws))) (Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength (ws_bytes ws)))
     (@field_address0 HCS (tarray tuchar (2 ^ 19)) (SUB (Zlength (ws_bytes ws))) (@field_address HCS t_wseries (DOT _bytes) p)) *
   @field_at HCS Ews t_wseries (DOT _f)
     (map winfo_val (ws_frames ws) ++ Zrepeat (winfo_val winfo0) (4 - Zlength (ws_frames ws))) p *
   @field_at HCS Ews t_wseries (DOT _nframes) (vu (Zlength (ws_frames ws))) p *
   spacer Ews 786932 786936 p)%logic |-- M34B_sr_rest ws p.
Proof. unfold M34B_sr_rest. apply derives_refl. Qed.

(* wd: the fields main reads (bytes, n, formatted); the rest is dropped *)
Lemma M34I_content_split ws p : Zlength (ws_content ws) <= 2 ^ 18 -> field_compatible t_wseries (DOT _content) p ->
  field_at Ews t_wseries (DOT _content) (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws))) p =
  (data_at Ews (tarray tuchar (Zlength (ws_content ws))) (zbytes (ws_content ws)) (field_address t_wseries (DOT _content) p) *
   data_at Ews (tarray tuchar (262144 - Zlength (ws_content ws))) (Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws)))
     (field_address0 (tarray tuchar 262144) (SUB (Zlength (ws_content ws))) (field_address t_wseries (DOT _content) p)))%logic.
Proof.
  intros Hn Hfc. rewrite field_at_data_at.
  change (nested_field_type t_wseries (DOT _content)) with (tarray tuchar 262144).
  apply split2_data_at_Tarray_app; rewrite ?Zlength_map, ?Zlength_Zrepeat; rep_lia.
Qed.

Lemma M34I_content_fold ws p : Zlength (ws_content ws) <= 2 ^ 18 -> field_compatible t_wseries (DOT _content) p ->
  data_at Ews (tarray tuchar (Zlength (ws_content ws))) (zbytes (ws_content ws)) (field_address t_wseries (DOT _content) p) *
  data_at Ews (tarray tuchar (262144 - Zlength (ws_content ws))) (Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws)))
     (field_address0 (tarray tuchar 262144) (SUB (Zlength (ws_content ws))) (field_address t_wseries (DOT _content) p))
  |-- field_at Ews t_wseries (DOT _content) (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws))) p.
Proof. intros Hn Hfc. rewrite (M34I_content_split ws p Hn Hfc). apply derives_refl. Qed.

Lemma M34I_ltu64 x y : 0 <= x <= Int64.max_unsigned -> 0 <= y <= Int64.max_unsigned ->
  Int64.ltu (Int64.repr x) (Int64.repr y) = (x <? y).
Proof.
  intros Hx Hy. unfold Int64.ltu. rewrite !Int64.unsigned_repr by lia.
  destruct (zlt x y); destruct (Z.ltb_spec x y); lia || reflexivity.
Qed.





Section M34.
Variable DC : globals -> val -> dctx_st -> mpred.
Variable DD : globals -> val -> ddict_st -> mpred.
Variable WG : globals -> mpred.
Variable WDS : wdict -> reptype t_wstate -> Prop.

Lemma M34_load_err st st' r dr : load_result_adv st st' r 2 dr -> dr_bytes dr <> nil ->
  dict_formatted (dr_bytes dr) = false -> is_error_code r = true.
Proof. intros [[_ [_ H]] | [E _]] Hn Hf; [rewrite H in Hf by auto; discriminate | exact E]. Qed.

Lemma M34_nonnil (b: list Z) : 0 < Zlength b -> b <> nil.
Proof. intros H E. subst b. rewrite Zlength_nil in H. lia. Qed.

Lemma M34_facts mode nd which wds wd ws cap : vda_facts mode nd which wds wd ws cap ->
  dict_facts wd /\ wdict_wf wd.
Proof.
  intros (_ & _ & _ & _ & _ & Hn & Hf & Hw & _). apply nth_error_In in Hn.
  rewrite Forall_forall in Hf, Hw. auto.
Qed.

(* ---------- byte arrays (after the VB lemmas of WMain3_valid_dict.v) ---------- *)

Definition M34_cce (cs1 cs2: compspecs) : change_composite_env cs1 cs2 :=
  {| coeq := cs_preserve_env cs1 cs2;
     coeq_consistent := cs_preserve_env_consistent cs1 cs2 _ eq_refl;
     coeq_complete := cs_preserve_completeness cs1 cs2 _ eq_refl |}.

Lemma M34_cs (cs1 cs2: compspecs) sh n (v: list val) p :
  @data_at cs1 sh (tarray tuchar n) v p = @data_at cs2 sh (tarray tuchar n) v p.
Proof.
  pose proof (@data_at_change_composite cs1 cs2 (M34_cce cs1 cs2) sh (tarray tuchar n) v v
    (JMeq_refl _) ltac:(reflexivity)) as E. rewrite E; reflexivity.
Qed.

Lemma M34_cs_ (cs1 cs2: compspecs) sh n p :
  @data_at_ cs1 sh (tarray tuchar n) p = @data_at_ cs2 sh (tarray tuchar n) p.
Proof.
  pose proof (@data_at__change_composite cs1 cs2 (M34_cce cs1 cs2) sh (tarray tuchar n)
    ltac:(reflexivity)) as E. rewrite E; reflexivity.
Qed.

Lemma M34_split_bytes_ {cs: compspecs} sh m k p : 0 <= k <= m -> field_compatible (tarray tuchar m) [] p ->
  data_at_ sh (tarray tuchar m) p =
  (data_at_ sh (tarray tuchar k) p * data_at_ sh (tarray tuchar (m - k)) (offset_val k p))%logic.
Proof.
  intros Hk Hf. unfold tarray. rewrite (split2_data_at__Tarray_tuchar sh m k p Hk) by auto with field_compatible.
  rewrite field_address0_offset by auto with field_compatible. simpl. rewrite Z.mul_1_l, Z.add_0_l. reflexivity.
Qed.

(* a buffer of n > 0 bytes needs no witness *)
Lemma M34_wvp_at {cs: compspecs} sh k p i q : readable_share sh -> 0 <= i <= k -> 0 < k -> q = offset_val i p ->
  data_at_ sh (tarray tuchar k) p |-- weak_valid_pointer q.
Proof.
  intros Hsh Hi Hk ->. eapply derives_trans; [apply data_at__memory_block_cancel|].
  simpl sizeof. rewrite Z.mul_1_l, Z.max_r by lia.
  apply memory_block_weak_valid_pointer; try lia. apply readable_nonidentity; auto.
Qed.

Lemma M34_buf_ok_nil n p : 0 < n -> buf_ok [] Ews n p.
Proof.
  intros Hn. unfold buf_ok, pws_pred. simpl. rewrite emp_sepcon.
  destruct (isptr_dec p) as [Hp|Hp].
  - destruct p; try contradiction. apply andp_right.
    + eapply (M34_wvp_at _ n _ 0); [auto | lia | lia |]. simpl. rewrite Ptrofs.add_zero. reflexivity.
    + eapply (M34_wvp_at _ n _ n); [auto | lia | lia | reflexivity].
  - rewrite data_at__isptr. normalize.
Qed.

(* buf back in one piece: [dst | gap] and the dictionary *)
Lemma M34_merge_buf buf cap dn v : 0 <= cap -> 0 <= dn ->
  field_compatible (tarray tuchar (cap + 1 + dn)) [] buf ->
  @data_at_ HCS Ews (tarray tuchar (cap + 1)) buf * @data_at ZCS Ews (tarray tuchar dn) v (offset_val (cap + 1) buf)
  |-- @data_at_ HCS Ews (tarray tuchar (cap + 1 + dn)) buf.
Proof.
  intros Hc Hd Hf. rewrite (M34_split_bytes_ Ews (cap + 1 + dn) (cap + 1) buf) by (auto; lia).
  replace (cap + 1 + dn - (cap + 1)) with dn by lia. rewrite (M34_cs ZCS HCS).
  sep_apply (@data_at_data_at_ HCS Ews (tarray tuchar dn) v (offset_val (cap + 1) buf)). cancel.
Qed.

Lemma M34_dd_res gv : dd_res DD gv (Zrepeat nullval 3) = emp.
Proof. unfold dd_res. simpl. rewrite !sepcon_emp. reflexivity. Qed.

Lemma M34_ddv_ok : Forall is_pointer_or_null (Zrepeat nullval 3).
Proof. repeat constructor. Qed.

(* mode 3, after the load (or refPrefix) with ZSTD_dct_fullDict: the error, fail = 1, no decoding *)
Ltac M34_side :=
  match goal with
  | |- buf_ok _ _ _ _ => apply M34_buf_ok_nil; lia
  | |- _ |-- _ => change (pws_pred []) with (@emp mpred _ _); cancel
  end.

Ltac M34_tail3 :=
  let vret := fresh "vret" in
  Intros vret; destruct vret as [?r ?st']; cbn [fst snd] in *; change (pws_pred []) with (@emp mpred _ _);
  try (match goal with |- semax _ _ (Ssequence (Sset _ _) _) _ => forward end);
  match goal with HL: load_result_adv _ ?st1 ?r1 _ _ |- _ =>
  match goal with Hdl: 8 <= Zlength (wd_bytes ?wd) <= _, Hnf: dict_formatted (wd_bytes ?wd) = false |- _ =>
    let Er := fresh "Er" in
    assert (Er: is_error_code r1 = true)
      by (eapply M34_load_err; [exact HL | cbn; apply M34_nonnil; lia | exact Hnf]);
  forward_call r1;
  forward_call (Int.repr (if is_error_code r1 then 1 else 0));
  [ match goal with Hx: Int.repr _ = Int.zero |- _ => rewrite Er in Hx; apply repr_inj_unsigned in Hx; rep_lia end | ];
  forward;
  forward_if;
  [ exfalso; match goal with Hx: Int.repr 1 = Int.zero |- _ => apply repr_inj_unsigned in Hx; rep_lia end | ];
  forward; Exists st1 (Zrepeat nullval 3); unfold VDA_E; rewrite M34_dd_res; entailer!;
  [ apply M34_ddv_ok | ];
  match goal with |- context [@data_at_ _ _ (tarray tuchar (?c + 1)) ?b] =>
  match goal with |- context [@data_at _ _ (tarray tuchar ?n) ?v (offset_val (c + 1) b)] =>
    sep_apply (M34_merge_buf b c n v); [lia | lia | cancel] end end
  end end.

Lemma vda_mode3 : VDA_mode_ok DC DD WG WDS 3.
Proof.
  intros Espec gv v_dd nd which wds wd ws cap src buf dctx.
  unfold VDA_Delta. simplify_func_tycontext.
  unfold VDA_A, VDA_setup_s, VDA_dec_s. Intros.
  destruct (M34_facts _ _ _ _ _ _ _ H) as [Hdf Hdw].
  destruct H as (Hm & Hnd & Hnd' & Hw & Hw0 & Hnth & Hfs & Hws & H0m & Hraw & H2m & Hsf & Hwf & H0f & H4m & H56 & Hcap & Hdwin).
  assert (Hnf: dict_formatted (wd_bytes wd) = false) by (apply M34_not_formatted; [auto | apply Hraw; auto]).
  pose proof Hdf as (Hbok & Hdl & _).
  rewrite (M34_cs HCS ZCS Ews (Zlength (wd_bytes wd))).
  apply semax_if_seq. forward_if; [lia|]. repeat apply -> seq_assoc. apply semax_if_seq. forward_if; [lia|].
  forward. apply semax_if_seq. forward_if. 1: (exfalso; revert H3; simpl; intros; discriminate).
  apply semax_if_seq. forward_if; [| lia].
  forward_call 2. Intros c.
  apply semax_if_seq. forward_if.
  - forward_call 2. Intros c2.
    apply semax_if_seq. forward_if.
    + forward.
      forward_call ([] : list ptr_witness, gv, dctx, dctx_init, Ews, offset_val (cap + 1) buf, wd_bytes wd, 1, 2).
      all: try M34_side. M34_tail3.
    + forward.
      forward_call ([] : list ptr_witness, gv, dctx, dctx_init, Ews, offset_val (cap + 1) buf, wd_bytes wd, 0, 2).
      all: try M34_side. M34_tail3.
  - forward_call ([] : list ptr_witness, gv, dctx, dctx_init, Ews, offset_val (cap + 1) buf, wd_bytes wd, 2).
    all: try M34_side. M34_tail3.
Qed.

(* mode 4: the prefix (raw content either way) *)
Definition M34_drp (p: val) (t: Z) (b: list Z) : dictref :=
  {| dr_src := DSRef p; dr_raw := t =? 1; dr_once := true; dr_bytes := b |}.

Lemma M34_pref st st' r t p wd : load_result_adv st st' r t (M34_drp p t (wd_bytes wd)) ->
  (is_error_code r = false -> st' = set_dict st (Some (M34_drp p t (wd_bytes wd)))) /\
  (is_error_code r = true -> st' = set_dict st None).
Proof.
  intros [[-> [-> _]] | [E [-> _]]]; split; intros Er; auto.
  - vm_compute in Er. discriminate.
  - congruence.
Qed.

Lemma M34_model p t wd : t = 0 \/ t = 1 -> dict_facts wd -> wd_formatted wd = false ->
  dictref_model (Some (M34_drp p t (wd_bytes wd))) = Some (wd_model wd).
Proof.
  intros Ht Hf Hr. destruct Ht as [-> | ->]; cbn.
  - destruct Hf as (_ & _ & Ha & _). unfold wd_model. destruct (dict_auto (wd_bytes wd)); [reflexivity | contradiction].
  - destruct Hf as (_ & _ & _ & _ & _ & _ & H). destruct (H Hr) as [-> _]. reflexivity.
Qed.

Lemma M34_dres_fold gv p t b :
  @data_at ZCS Ews (tarray tuchar (Zlength b)) (zbytes b) p |--
  dict_res DD gv Ews (dc_dict (set_dict dctx_init (Some (M34_drp p t b)))) *
  set_res DD gv Ews (dc_set (set_dict dctx_init (Some (M34_drp p t b)))) (dc_dict (set_dict dctx_init (Some (M34_drp p t b)))).
Proof. unfold dict_res, set_res. simpl. rewrite sepcon_emp. apply derives_refl. Qed.

Lemma M34_dres_unfold gv p t b :
  dict_res DD gv Ews (dc_dict (set_dict dctx_init (Some (M34_drp p t b)))) *
  set_res DD gv Ews (dc_set (set_dict dctx_init (Some (M34_drp p t b)))) (dc_dict (set_dict dctx_init (Some (M34_drp p t b))))
  |-- @data_at ZCS Ews (tarray tuchar (Zlength b)) (zbytes b) p.
Proof. unfold dict_res, set_res. simpl. rewrite sepcon_emp. apply derives_refl. Qed.

Lemma M34_os4 p t wd s cap r out : t = 0 \/ t = 1 -> dict_facts wd -> wd_formatted wd = false ->
  oneshot_dctx (set_dict dctx_init (Some (M34_drp p t (wd_bytes wd)))) s cap r out ->
  oneshot_ok md_dflt (Some (wd_model wd)) s cap r out.
Proof. intros Ht Hf Hr Ho. rewrite <- (M34_model p t wd Ht Hf Hr). exact Ho. Qed.

(* the decoding: the then-branch of `if (!fail)` *)
Definition M34_dec_s : statement := ltac:(
  let x := eval cbv [VDA_dec_s] in VDA_dec_s in lazymatch x with Sifthenelse _ ?s _ => exact s end).

(* the end of the decoding: src and buf back in one piece each, sr dropped *)
Ltac M34_fin :=
  match goal with |- context [pws_pred (M34B_W ?s ?n ?b ?c)] =>
  match goal with |- context [@data_at _ _ (tarray tuchar c) ?o b] =>
  match goal with |- context [@data_at _ _ (tarray tuchar ?dn) ?v (offset_val (c + 1) b)] =>
  match goal with |- context [@data_at _ _ (tarray tuchar n) ?vs s] =>
    sep_apply (M34B_final_merge s n b c dn o v vs) end end end end;
  [ try apply Zlength_nonneg; lia .. | cancel ].

Lemma M34_dec4 (Espec: OracleKind) gv v_dd wd ws cap src buf dctx t
  (Hsf: series_facts (wd_model wd) ws) (Hwf: wseries_wf ws) (Hdf: dict_facts wd) (Hrw: wd_formatted wd = false)
  (Ht: t = 0 \/ t = 1) (Hcap: 0 <= cap <= Zlength (ws_content ws) + 16)
  (Psrc: isptr src) (Pbuf: isptr buf) (Pdctx: isptr dctx)
  (H0: field_compatible (tarray tuchar (cap + 1 + Zlength (wd_bytes wd))) [] buf)
  (H1: field_compatible (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws)))) [] src) :
  @semax HCS Espec (VDA_Delta DC DD WG WDS)
    (PROP ()
     LOCAL (temp _mode (Vint (Int.repr 4)); temp _cap (Vlong (Int64.repr cap)); temp _src src; temp _buf buf;
            temp _dst buf; temp _dctx dctx; lvar _dd t_ddp v_dd; gvars gv)
     SEP (mem_mgr gv; zstd_globals gv; DC gv dctx (set_dict dctx_init (Some (M34_drp (offset_val (cap + 1) buf) t (wd_bytes wd))));
          @data_at HCS Ews t_wseries (wseries_val ws) (gv _x_valid_dict_api__sr);
          @malloc_token HCS Ews (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws)))) src;
          @data_at HCS Ews (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws))))
            (zbytes (ws_bytes ws) ++ Zrepeat Vundef (Z.max 1 (Zlength (ws_bytes ws)) - Zlength (ws_bytes ws))) src;
          @malloc_token HCS Ews (tarray tuchar (cap + 1 + Zlength (wd_bytes wd))) buf;
          @data_at_ HCS Ews (tarray tuchar (cap + 1)) buf;
          @data_at ZCS Ews (tarray tuchar (Zlength (wd_bytes wd))) (zbytes (wd_bytes wd)) (offset_val (cap + 1) buf);
          @data_at HCS Tsh t_ddp (Zrepeat nullval 3) v_dd; TT))
    M34_dec_s
    (normal_ret_assert (EX st: dctx_st, EX ddv: list val,
       VDA_E DC DD gv v_dd (Zlength (ws_bytes ws)) cap (Zlength (wd_bytes wd)) src buf dctx st ddv)).
Proof.
  unfold VDA_Delta, M34_dec_s. simplify_func_tycontext.
  pose proof Hsf as (Hbs & Hcs & Hnb & Hnc & Hnf & _).
  pose proof Hdf as (Hbok & Hdl & _).
  apply semax_if_seq. forward_if; [lia|]. forward. forward_if. 1: discriminate.
  apply semax_if_seq. forward_if; [lia|]. forward. forward_if. 1: lia.
  sep_apply (M34B_ws_unfold ws (gv _x_valid_dict_api__sr) Hnb). Intros.
  forward.
  rewrite (M34B_src_split src (ws_bytes ws) H1).
  assert (Hfb1: field_compatible (tarray tuchar (cap + 1)) [] buf)
    by (eapply field_compatible_array_smaller0; [exact H0 | lia]).
  rewrite (M34_split_bytes_ (cs := HCS) Ews (cap + 1) cap buf) by (auto; lia).
  replace (cap + 1 - cap) with 1 by lia.
  rewrite (M34_cs_ HCS ZCS Ews cap buf), (M34_cs_ HCS ZCS Ews 1 (offset_val cap buf)).
  sep_apply (M34B_wit_fold src (Zlength (ws_bytes ws)) buf cap).
  sep_apply (M34_dres_fold gv (offset_val (cap + 1) buf) t (wd_bytes wd)).
  forward_call (M34B_W src (Zlength (ws_bytes ws)) buf cap, gv, dctx,
                set_dict dctx_init (Some (M34_drp (offset_val (cap + 1) buf) t (wd_bytes wd))),
                Ews, Ews, buf, cap, Ews, src, ws_bytes ws).
  1: (sep_apply (data_at__mbuf Ews cap buf); cancel).
  1: { split; [apply M34B_buf_ok_dst; [auto | lia] | split; [apply M34B_buf_ok_src; [auto | rep_lia] |]].
       cbn. apply M34B_dict_ptr_ok; auto; lia. }
  Intros vret. destruct vret as [[r out] st']. cbn [fst snd] in *. rewrite mbuf_isptr by auto.
  sep_apply (M34_dres_unfold gv (offset_val (cap + 1) buf) t (wd_bytes wd)).
  match goal with Ho: oneshot_dctx _ _ _ _ _ |- _ =>
    pose proof (M34_os4 _ _ _ _ _ _ _ Ht Hdf Hrw Ho) as Hos end.
  pose proof (M34v_check (wd_model wd) ws cap r out Hsf Hwf Hos) as [Hck1 Hck2].
  forward.
  forward_call r.
  forward_if.
  - (* success: the content *)
    assert (He: is_error_code r = false).
    { destruct (is_error_code r) eqn:E; [exfalso | reflexivity].
      match goal with Hx: Int.repr 1 = Int.zero |- _ => apply repr_inj_unsigned in Hx; rep_lia end. }
    destruct (Hck1 He) as [Er Esub].
    assert (Hrc: r <= cap) by (apply (proj1 Hos); auto).
    forward.
    forward_call (Int.one).
    { entailer!. rewrite Int64.eq_true. reflexivity. }
    match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
      forward;
      forward_loop (EX j: Z, PROPx ((0 <= j <= r) :: P) (LOCALx (temp _j (Vlong (Int64.repr j)) :: L) (SEPx R)))
        break: (PROPx P (LOCALx L (SEPx R))) end.
    + Exists 0. entailer!.
    + Intros j.
      forward_if.
      2: { forward. entailer!. }
      assert (Hi1: Znth j out = Vint (Int.repr (Znth j (ws_content ws)))) by (apply (M34B_out_at (ws_content ws) r out j); auto; lia).
      assert (Hbyte: 0 <= Znth j (ws_content ws) <= Byte.max_unsigned).
      { pose proof (proj1 (Forall_Znth _ _) Hcs j ltac:(lia)) as Hz. unfold is_byte in Hz. rep_lia. }
      rewrite (M34_cs ZCS HCS Ews cap out buf).
      forward.
      1: { entailer!.
           all: try (replace (@Znth val Vundef j out) with (Vint (Int.repr (Znth j (ws_content ws)))) by (rewrite <- Hi1; reflexivity);
                     simpl; rewrite Int.unsigned_repr by rep_lia; rep_lia).
           all: lia. }
      assert_PROP (field_compatible t_wseries (DOT _content) (gv _x_valid_dict_api__sr)) as Hfcc by entailer!.
      rewrite (M34I_content_split ws (gv _x_valid_dict_api__sr) Hnc Hfcc). Intros.
      assert_PROP (force_val (sem_add_ptr_long tuchar (offset_val 524296 (gv _x_valid_dict_api__sr)) (Vlong (Int64.repr j))) =
        field_address (tarray tuchar (Zlength (ws_content ws))) (SUB j) (field_address t_wseries (DOT _content) (gv _x_valid_dict_api__sr))) as Ea.
      { entailer!. rewrite (field_address_offset t_wseries) by auto.
        rewrite arr_field_address by (auto; try lia; rewrite field_address_offset in *; auto).
        simpl; rewrite offset_offset_val; f_equal; lia. }
      forward.
      1: { entailer!. apply Hbyte. }
      sep_apply (M34I_content_fold ws (gv _x_valid_dict_api__sr) Hnc Hfcc).
      forward_call (Int.one).
      { entailer!. replace (@Znth val Vundef j out) with (Vint (Int.repr (Znth j (ws_content ws)))) by (rewrite <- Hi1; reflexivity).
        simpl. rewrite Int.eq_true. reflexivity. }
      forward.
      Exists (j + 1). rewrite (M34_cs HCS ZCS Ews cap out buf).
      entailer!.
    + Exists st' (Zrepeat nullval 3). unfold VDA_E. rewrite M34_dd_res. entailer!.
      1: apply M34_ddv_ok.
      M34_fin.
  - (* an error: memory_allocation when the capacity holds the content and the frames are within range *)
    assert (He: is_error_code r = true).
    { destruct (is_error_code r) eqn:E; [reflexivity | exfalso].
      match goal with Hx: Int.repr 0 <> Int.zero |- _ => apply Hx; reflexivity end. }
    forward.
    match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp _x_valid_dict_api__t'51
        (Vint (Int.repr (if andb (Zlength (ws_content ws) <=? cap) (within_oneshot_b (ws_frames ws)) then 1 else 0))) :: L)
        (SEPx R))) end.
    + (* within_oneshot *)
      sep_apply (M34B_ws_fold ws (gv _x_valid_dict_api__sr) Hnb).
      forward_call (Ews, gv _x_valid_dict_api__sr, ws).
      forward.
      sep_apply (M34B_ws_unfold ws (gv _x_valid_dict_api__sr) Hnb). Intros.
      entailer!.
      rewrite (proj2 (Z.leb_le _ _)) by lia. destruct (within_oneshot_b _); reflexivity.
    + forward. entailer!. rewrite (proj2 (Z.leb_gt _ _)) by lia. reflexivity.
    + forward_if.
      * assert (Hw: Zlength (ws_content ws) <= cap /\ within_oneshot_b (ws_frames ws) = true).
        { match goal with H: Int.repr (if (?b1 && ?b2)%bool then 1 else 0) <> Int.zero |- _ =>
            destruct (b1 && b2)%bool eqn:Eb; [|contradiction H; reflexivity] end.
          apply andb_prop in Eb as [E1 E2]. apply Z.leb_le in E1. auto. }
        destruct Hw as [Hw1 Hw2].
        assert (Erm: error_of r = ZSTD_error_memory_allocation).
        { rewrite (Hck2 He Hw1 Hw2). apply M34_err64. }
        forward_call r.
        forward_call (Int.one).
        { entailer!. rewrite Erm. reflexivity. }
        Exists st' (Zrepeat nullval 3). unfold VDA_E. rewrite M34_dd_res. entailer!.
        1: apply M34_ddv_ok.
        M34_fin.
      * forward. Exists st' (Zrepeat nullval 3). unfold VDA_E. rewrite M34_dd_res. entailer!.
        1: apply M34_ddv_ok.
        M34_fin.
Qed.

Lemma vda_mode4 : VDA_mode_ok DC DD WG WDS 4.
Proof.
  intros Espec gv v_dd nd which wds wd ws cap src buf dctx.
  assert (Hdec := M34_dec4 Espec gv v_dd wd ws cap src buf dctx).
  unfold VDA_Delta. simplify_func_tycontext.
  unfold VDA_A, VDA_setup_s, VDA_dec_s. Intros.
  destruct (M34_facts _ _ _ _ _ _ _ H) as [Hdf Hdw].
  destruct H as (Hm & Hnd & Hnd' & Hw & Hw0 & Hnth & Hfs & Hws & H0m & Hraw & H2m & Hsf & Hwf & H0f & H4m & H56 & Hcap & Hdwin).
  assert (Hsf4: series_facts (wd_model wd) ws) by exact Hsf.
  assert (Hrw: wd_formatted wd = false) by (apply Hraw; auto).
  pose proof Hdf as (Hbok & Hdl & _).
  rewrite (M34_cs HCS ZCS Ews (Zlength (wd_bytes wd))).
  apply semax_if_seq. forward_if; [lia|]. repeat apply -> seq_assoc. apply semax_if_seq. forward_if; [lia|].
  forward. apply semax_if_seq. forward_if. 1: (exfalso; revert H3; simpl; intros; discriminate).
  apply semax_if_seq. forward_if; [lia |].
  apply semax_if_seq. forward_if; [| lia].
  forward_call 2. Intros c.
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
    forward_if (EX t: Z, PROPx ((t = 0 \/ t = 1) :: P) (LOCALx (temp _x_valid_dict_api__t'37 (Vint (Int.repr t)) :: L) (SEPx R))) end.
  1: (forward; Exists 1; entailer!).
  1: (forward; Exists 0; entailer!).
  Intros t.
  forward_call ([] : list ptr_witness, gv, dctx, dctx_init, Ews, offset_val (cap + 1) buf, wd_bytes wd, t).
  all: try M34_side.
  Intros vret. destruct vret as [r st']. cbn [fst snd] in *. change (pws_pred []) with (@emp mpred _ _).
  match goal with HL: load_result_adv _ _ _ _ _ |- _ =>
    destruct (M34_pref _ _ _ _ _ wd HL) as [Hok Herr] end.
  forward_call r.
  forward.
  forward_if.
  - (* the prefix is set: decoding *)
    assert (Er: is_error_code r = false).
    { destruct (is_error_code r) eqn:E; [| reflexivity]. exfalso.
      match goal with Hx: Int.repr 1 = Int.zero |- _ => apply repr_inj_unsigned in Hx; rep_lia end. }
    rewrite (Hok Er).
    eapply semax_pre; [| apply (Hdec t); auto].
    entailer!.
  - (* an error: nothing decoded *)
    assert (Er: is_error_code r = true).
    { destruct (is_error_code r) eqn:E; [reflexivity |]. exfalso.
      match goal with Hx: Int.repr 0 <> Int.zero |- _ => apply Hx; reflexivity end. }
    forward. Exists st' (Zrepeat nullval 3). unfold VDA_E. rewrite M34_dd_res. entailer!.
    + apply M34_ddv_ok.
    + sep_apply (M34_merge_buf buf cap (Zlength (wd_bytes wd)) (zbytes (wd_bytes wd))); [lia | lia | cancel].
Qed.
End M34.

Lemma vda_mode34_ok DC DD WG WDS : VDA_mode_ok DC DD WG WDS 3 /\ VDA_mode_ok DC DD WG WDS 4.
Proof. split; [exact (vda_mode3 DC DD WG WDS) | exact (vda_mode4 DC DD WG WDS)]. Qed.
