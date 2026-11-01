(* valid_bufferless: helpers of the main (buffers and their witnesses, compspecs, main's precondition, sr field by
   field), after src/proof/harness/valid_dict/WMain_valid_dict.v (same layout: src of max(1,n) bytes, buf = [dst | 1 byte
   | dict]). *)
Require Import VST.floyd.proofauto.
Require Export Zstd.proof.harness.valid_bufferless.WTopSpecs_valid_bufferless.
Require Zstd.proof.top.MainPre6.

Local Notation ZCS := Zstd.proof.zstd.Base.CompSpecs.
Local Notation HCS := Zstd.proof.harness.valid_bufferless.HOK_valid_bufferless.CompSpecs.

Definition VLB_cce (cs1 cs2: compspecs) : change_composite_env cs1 cs2 :=
  {| coeq := cs_preserve_env cs1 cs2;
     coeq_consistent := cs_preserve_env_consistent cs1 cs2 _ eq_refl;
     coeq_complete := cs_preserve_completeness cs1 cs2 _ eq_refl |}.

Lemma VLB_cs (cs1 cs2: compspecs) sh n (v: list val) p :
  @data_at cs1 sh (tarray tuchar n) v p = @data_at cs2 sh (tarray tuchar n) v p.
Proof.
  pose proof (@data_at_change_composite cs1 cs2 (VLB_cce cs1 cs2) sh (tarray tuchar n) v v
    (JMeq_refl _) ltac:(reflexivity)) as E. rewrite E; reflexivity.
Qed.

Lemma VLB_cs_ (cs1 cs2: compspecs) sh n p :
  @data_at_ cs1 sh (tarray tuchar n) p = @data_at_ cs2 sh (tarray tuchar n) p.
Proof.
  pose proof (@data_at__change_composite cs1 cs2 (VLB_cce cs1 cs2) sh (tarray tuchar n)
    ltac:(reflexivity)) as E. rewrite E; reflexivity.
Qed.

Lemma VLB_split_bytes_ {cs: compspecs} sh m k p : 0 <= k <= m -> field_compatible (tarray tuchar m) [] p ->
  data_at_ sh (tarray tuchar m) p =
  (data_at_ sh (tarray tuchar k) p * data_at_ sh (tarray tuchar (m - k)) (offset_val k p))%logic.
Proof.
  intros Hk Hf. unfold tarray. rewrite (split2_data_at__Tarray_tuchar sh m k p Hk) by auto with field_compatible.
  rewrite field_address0_offset by auto with field_compatible. simpl. rewrite Z.mul_1_l, Z.add_0_l. reflexivity.
Qed.

(* the slack of src's block and the gap byte between dst and dict *)
Definition VLB_slack (src: val) (n: Z) : ptr_witness :=
  pw_bytes Ews (Z.max 1 n - n) (Zrepeat Vundef (Z.max 1 n - n)) (offset_val n src).
Definition VLB_gap (buf: val) (cap: Z) : ptr_witness := pw_bytes Ews 1 [Vundef] (offset_val cap buf).
Definition VLB_W (src: val) (n: Z) (buf: val) (cap: Z) : list ptr_witness := [VLB_slack src n; VLB_gap buf cap].

Lemma VLB_pws src n buf cap : pws_pred (VLB_W src n buf cap) =
  (@data_at_ ZCS Ews (tarray tuchar (Z.max 1 n - n)) (offset_val n src) *
   @data_at_ ZCS Ews (tarray tuchar 1) (offset_val cap buf))%logic.
Proof. unfold pws_pred, VLB_W, map, fold_right. rewrite sepcon_emp. reflexivity. Qed.

Lemma VLB_wvp_at {cs: compspecs} sh k p i q : readable_share sh -> 0 <= i <= k -> 0 < k -> q = offset_val i p ->
  data_at_ sh (tarray tuchar k) p |-- weak_valid_pointer q.
Proof.
  intros Hsh Hi Hk ->. eapply derives_trans; [apply data_at__memory_block_cancel|].
  simpl sizeof. rewrite Z.mul_1_l, Z.max_r by lia.
  apply memory_block_weak_valid_pointer; try lia. apply readable_nonidentity; auto.
Qed.

Lemma VLB_ptr_eq b o i j : i = j -> offset_val i (Vptr b o) = offset_val j (Vptr b o).
Proof. intros ->; reflexivity. Qed.

Lemma VLB_off_off b o i j : offset_val j (offset_val i (Vptr b o)) = offset_val (i + j) (Vptr b o).
Proof. rewrite offset_offset_val. reflexivity. Qed.

Lemma VLB_off0 b o : Vptr b o = offset_val 0 (Vptr b o).
Proof. simpl. rewrite Ptrofs.add_zero. reflexivity. Qed.

Ltac VLB_ptr_eq_tac :=
  first [ reflexivity
        | rewrite ?VLB_off_off; apply VLB_ptr_eq; lia
        | match goal with |- Vptr ?b ?o = _ => rewrite (VLB_off0 b o) at 1 end; rewrite ?VLB_off_off; apply VLB_ptr_eq; lia ].

Ltac VLB_piece k i :=
  eapply (VLB_wvp_at _ k _ i); [auto | lia | lia | VLB_ptr_eq_tac].

Lemma VLB_buf_ok_src src n buf cap : isptr src -> 0 <= n -> buf_ok (VLB_W src n buf cap) Ews n src.
Proof.
  intros Hp Hn. destruct src; try contradiction. unfold buf_ok. rewrite VLB_pws.
  destruct (zlt 0 n).
  - apply andp_right; apply sepcon_weak_valid_pointer2.
    + VLB_piece n 0.
    + VLB_piece n n.
  - apply andp_right; apply sepcon_weak_valid_pointer1, sepcon_weak_valid_pointer1.
    + VLB_piece (Z.max 1 n - n) 0.
    + VLB_piece (Z.max 1 n - n) 0.
Qed.

Lemma VLB_buf_ok_dst src n buf cap : isptr buf -> 0 <= cap -> buf_ok (VLB_W src n buf cap) Ews cap buf.
Proof.
  intros Hp Hc. destruct buf; try contradiction. unfold buf_ok. rewrite VLB_pws.
  destruct (zlt 0 cap).
  - apply andp_right; apply sepcon_weak_valid_pointer2.
    + VLB_piece cap 0.
    + VLB_piece cap cap.
  - apply andp_right; apply sepcon_weak_valid_pointer1, sepcon_weak_valid_pointer2.
    + VLB_piece 1 0.
    + VLB_piece 1 0.
Qed.

Lemma VLB_buf_ok_dict src n buf cap dn : isptr buf -> 0 <= cap -> 0 <= dn ->
  buf_ok (VLB_W src n buf cap) Ews dn (offset_val (cap + 1) buf).
Proof.
  intros Hp Hc Hd. destruct buf; try contradiction. unfold buf_ok. rewrite VLB_pws.
  apply andp_right.
  - apply sepcon_weak_valid_pointer1, sepcon_weak_valid_pointer2. VLB_piece 1 1.
  - destruct (zlt 0 dn).
    + apply sepcon_weak_valid_pointer2. VLB_piece dn dn.
    + apply sepcon_weak_valid_pointer1, sepcon_weak_valid_pointer2. VLB_piece 1 1.
Qed.

Lemma VLB_sameblock_off buf k : isptr buf -> sameblock buf (offset_val k buf) = true.
Proof. intros Hp. destruct buf; try contradiction. simpl. unfold sameblock. apply peq_true. Qed.

Lemma VLB_dict_ptr_ok src n buf cap dn : isptr buf -> 0 <= cap -> 0 <= dn ->
  field_compatible (tarray tuchar (cap + 1 + dn)) [] buf ->
  dict_ptr_ok (VLB_W src n buf cap) Ews dn (offset_val (cap + 1) buf) Ews cap buf.
Proof.
  intros Hp Hc Hd Hf. left. split; [apply VLB_sameblock_off; auto | split; [| apply VLB_buf_ok_dict; auto]].
  destruct buf as [| | | | | b o]; try contradiction.
  destruct Hf as (_ & _ & Hsz & _). simpl in Hsz. rewrite Z.max_r in Hsz by lia.
  simpl. rewrite Ptrofs.add_unsigned. rewrite (Ptrofs.unsigned_repr (cap + 1)) by rep_lia.
  rewrite Ptrofs.unsigned_repr by rep_lia. lia.
Qed.

(* a buffer of n > 0 bytes needs no witness *)
Lemma VLB_buf_ok_nil n p : 0 < n -> buf_ok [] Ews n p.
Proof.
  intros Hn. unfold buf_ok, pws_pred. simpl. rewrite emp_sepcon.
  destruct (isptr_dec p) as [Hp|Hp].
  - destruct p; try contradiction. apply andp_right.
    + VLB_piece n 0.
    + VLB_piece n n.
  - rewrite data_at__isptr. normalize.
Qed.

Lemma VLB_split3_ {cs: compspecs} sh c d p : 0 <= c -> 0 <= d ->
  field_compatible (tarray tuchar (c + 1 + d)) [] p ->
  data_at_ sh (tarray tuchar (c + 1 + d)) p =
  (data_at_ sh (tarray tuchar c) p * data_at_ sh (tarray tuchar 1) (offset_val c p) *
   data_at_ sh (tarray tuchar d) (offset_val (c + 1) p))%logic.
Proof.
  intros Hc Hd Hf.
  rewrite (VLB_split_bytes_ sh (c + 1 + d) (c + 1) p) by (auto; lia).
  replace (c + 1 + d - (c + 1)) with d by lia.
  rewrite (VLB_split_bytes_ sh (c + 1) c p).
  - replace (c + 1 - c) with 1 by lia. reflexivity.
  - lia.
  - eapply field_compatible_array_smaller0; [exact Hf | lia].
Qed.

Lemma VLB_Zrepeat {cs: compspecs} sh c p :
  data_at_ sh (tarray tuchar c) p = data_at sh (tarray tuchar c) (Zrepeat Vundef c) p.
Proof. unfold data_at_, field_at_, data_at. reflexivity. Qed.

Lemma VLB_bytes_ok l : Forall (fun b => 0 <= b <= Byte.max_unsigned) l -> bytes_ok l.
Proof. unfold bytes_ok, is_byte. apply Forall_impl. intros x Hx. rep_lia. Qed.

(* src from exact_copy: n bytes, then the slack (Vundef) of its max(1, n) block *)
Lemma VLB_src_split src bs : 
  field_compatible (tarray tuchar (Z.max 1 (Zlength bs))) [] src ->
  @data_at HCS Ews (tarray tuchar (Z.max 1 (Zlength bs))) (zbytes bs ++ Zrepeat Vundef (Z.max 1 (Zlength bs) - Zlength bs)) src
  = (@data_at ZCS Ews (tarray tuchar (Zlength bs)) (zbytes bs) src *
     @data_at_ ZCS Ews (tarray tuchar (Z.max 1 (Zlength bs) - Zlength bs)) (offset_val (Zlength bs) src))%logic.
Proof.
  intros Hf. pose proof (Zlength_nonneg bs).
  rewrite (VLB_cs HCS ZCS).
  rewrite (split2_data_at_Tarray_app (Zlength bs) (Z.max 1 (Zlength bs)) Ews tuchar).
  - rewrite VLB_Zrepeat. f_equal. f_equal.
    assert (Hf': @field_compatible ZCS (tarray tuchar (Z.max 1 (Zlength bs))) [] src).
    { apply (@field_compatible_change_composite HCS ZCS (VLB_cce HCS ZCS)); [reflexivity | exact Hf]. }
    rewrite field_address0_offset by auto with field_compatible.
    simpl. f_equal. lia.
  - exact (Zlength_map _ _ _ _).
  - rewrite Zlength_Zrepeat; lia.
Qed.

Lemma VLB_wit_fold src n buf cap :
  @data_at_ ZCS Ews (tarray tuchar (Z.max 1 n - n)) (offset_val n src) *
  @data_at_ ZCS Ews (tarray tuchar 1) (offset_val cap buf) |-- pws_pred (VLB_W src n buf cap).
Proof. rewrite VLB_pws. auto. Qed.

Lemma VLB_wit_unfold src n buf cap :
  pws_pred (VLB_W src n buf cap) |--
  @data_at_ ZCS Ews (tarray tuchar (Z.max 1 n - n)) (offset_val n src) *
  @data_at_ ZCS Ews (tarray tuchar 1) (offset_val cap buf).
Proof. rewrite VLB_pws. auto. Qed.

(* everything back for free(src) and free(buf) *)
Lemma VLB_final_merge src n buf cap dn out v vs :
  0 <= n -> 0 <= cap -> 0 <= dn ->
  field_compatible (tarray tuchar (Z.max 1 n)) [] src ->
  field_compatible (tarray tuchar (cap + 1 + dn)) [] buf ->
  pws_pred (VLB_W src n buf cap) * @data_at ZCS Ews (tarray tuchar cap) out buf *
  @data_at ZCS Ews (tarray tuchar dn) v (offset_val (cap + 1) buf) *
  @data_at ZCS Ews (tarray tuchar n) vs src
  |-- @data_at_ HCS Ews (tarray tuchar (Z.max 1 n)) src * @data_at_ HCS Ews (tarray tuchar (cap + 1 + dn)) buf.
Proof.
  intros Hn Hc Hd Hfs Hfb.
  rewrite (VLB_split_bytes_ Ews (Z.max 1 n) n src) by (auto; lia).
  rewrite (VLB_split3_ Ews cap dn buf) by auto.
  rewrite VLB_pws, !(VLB_cs_ HCS ZCS).
  sep_apply (data_at_data_at_ Ews (tarray tuchar cap) out buf).
  sep_apply (data_at_data_at_ Ews (tarray tuchar dn) v (offset_val (cap + 1) buf)).
  sep_apply (data_at_data_at_ Ews (tarray tuchar n) vs src).
  cancel.
Qed.

Lemma VLB_dict_val buf cap : isptr buf -> 0 <= cap <= Int64.max_unsigned - 1 ->
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
Lemma VLB_bytes_split sh (bs: list Z) p : Zlength bs <= 2 ^ 19 ->
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
Definition VLB_sr_rest (ws: wseries) (p: val) : mpred :=
  (@data_at HCS Ews (tarray tuchar (Zlength (ws_bytes ws))) (zbytes (ws_bytes ws)) (@field_address HCS t_wseries (DOT _bytes) p) *
   @data_at HCS Ews (tarray tuchar (2 ^ 19 - Zlength (ws_bytes ws))) (Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength (ws_bytes ws)))
     (@field_address0 HCS (tarray tuchar (2 ^ 19)) (SUB (Zlength (ws_bytes ws))) (@field_address HCS t_wseries (DOT _bytes) p)) *
   @field_at HCS Ews t_wseries (DOT _f)
     (map winfo_val (ws_frames ws) ++ Zrepeat (winfo_val winfo0) (4 - Zlength (ws_frames ws))) p *
   @field_at HCS Ews t_wseries (DOT _nframes) (vu (Zlength (ws_frames ws))) p *
   spacer Ews 786932 786936 p)%logic.

Lemma VLB_ws_fold ws p : Zlength (ws_bytes ws) <= 2 ^ 19 ->
  (VLB_sr_rest ws p *
   @field_at HCS Ews t_wseries (DOT _n) (vl (Zlength (ws_bytes ws))) p *
   @field_at HCS Ews t_wseries (DOT _content)
     (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws))) p *
   @field_at HCS Ews t_wseries (DOT _content_n) (vl (Zlength (ws_content ws))) p) |--
  @data_at HCS Ews t_wseries (wseries_val ws) p.
Proof.
  intros Hn. unfold VLB_sr_rest. rewrite <- VLB_bytes_split by exact Hn.
  unfold_data_at (data_at _ _ _ p). cbn [fst snd wseries_val]. cancel.
Qed.

Lemma VLB_ws_unfold ws p : Zlength (ws_bytes ws) <= 2 ^ 19 ->
  @data_at HCS Ews t_wseries (wseries_val ws) p |--
  (VLB_sr_rest ws p *
   @field_at HCS Ews t_wseries (DOT _n) (vl (Zlength (ws_bytes ws))) p *
   @field_at HCS Ews t_wseries (DOT _content)
     (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws))) p *
   @field_at HCS Ews t_wseries (DOT _content_n) (vl (Zlength (ws_content ws))) p).
Proof.
  intros Hn. unfold VLB_sr_rest. unfold_data_at (data_at _ _ _ p). cbn [fst snd wseries_val].
  rewrite (VLB_bytes_split Ews (ws_bytes ws) p Hn). cancel.
Qed.

(* the bytes delivered and the content, at index i *)
Lemma VLB_out_at (c: list Z) r out i : sublist 0 r out = zbytes c -> r = Zlength c -> 0 <= i < r ->
  Znth i out = Vint (Int.repr (Znth i c)).
Proof.
  intros Hs Hr Hi. replace (Znth i out) with (Znth (i + 0) out) by (rewrite Z.add_0_r; reflexivity).
  rewrite <- (Znth_sublist 0 i r out) by lia. rewrite Hs. rewrite Znth_map by lia. reflexivity.
Qed.

Lemma VLB_content_at (c: list Z) k i : 0 <= i < Zlength c -> 
  Znth i (zbytes c ++ Zrepeat (Vint Int.zero) k) = Vint (Int.repr (Znth i c)).
Proof.
  intros Hi. rewrite app_Znth1 by (rewrite Zlength_map; lia). rewrite Znth_map by lia. reflexivity.
Qed.

(* the dictionary copy: dict[0..i) written *)
Lemma VLB_copy_step (b: list Z) i n : 0 <= i < n -> Zlength b = n ->
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

Lemma VLB_rest_fold ws p :
  (@data_at HCS Ews (tarray tuchar (Zlength (ws_bytes ws))) (zbytes (ws_bytes ws)) (@field_address HCS t_wseries (DOT _bytes) p) *
   @data_at HCS Ews (tarray tuchar (2 ^ 19 - Zlength (ws_bytes ws))) (Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength (ws_bytes ws)))
     (@field_address0 HCS (tarray tuchar (2 ^ 19)) (SUB (Zlength (ws_bytes ws))) (@field_address HCS t_wseries (DOT _bytes) p)) *
   @field_at HCS Ews t_wseries (DOT _f)
     (map winfo_val (ws_frames ws) ++ Zrepeat (winfo_val winfo0) (4 - Zlength (ws_frames ws))) p *
   @field_at HCS Ews t_wseries (DOT _nframes) (vu (Zlength (ws_frames ws))) p *
   spacer Ews 786932 786936 p)%logic |-- VLB_sr_rest ws p.
Proof. unfold VLB_sr_rest. apply derives_refl. Qed.

(* wd: the fields main reads (bytes, n, formatted); the rest is dropped *)
Lemma VLB_wd_take wd p stv :
  @data_at HCS Ews t_wdict (wdict_val wd p stv) p |--
  @field_at HCS Ews t_wdict (DOT _bytes) (zbytes (wd_bytes wd) ++ Zrepeat (Vint Int.zero) (6144 - Zlength (wd_bytes wd))) p *
  @field_at HCS Ews t_wdict (DOT _n) (vl (Zlength (wd_bytes wd))) p *
  @field_at HCS Ews t_wdict (DOT _formatted) (vb (wd_formatted wd)) p * TT.
Proof. unfold_data_at (data_at _ _ _ p). cbn [fst snd wdict_val]. cancel. Qed.


Lemma VLI_content_split ws p : Zlength (ws_content ws) <= 2 ^ 18 -> field_compatible t_wseries (DOT _content) p ->
  field_at Ews t_wseries (DOT _content) (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws))) p =
  (data_at Ews (tarray tuchar (Zlength (ws_content ws))) (zbytes (ws_content ws)) (field_address t_wseries (DOT _content) p) *
   data_at Ews (tarray tuchar (262144 - Zlength (ws_content ws))) (Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws)))
     (field_address0 (tarray tuchar 262144) (SUB (Zlength (ws_content ws))) (field_address t_wseries (DOT _content) p)))%logic.
Proof.
  intros Hn Hfc. rewrite field_at_data_at.
  change (nested_field_type t_wseries (DOT _content)) with (tarray tuchar 262144).
  apply split2_data_at_Tarray_app; rewrite ?Zlength_map, ?Zlength_Zrepeat; rep_lia.
Qed.

Lemma VLI_content_fold ws p : Zlength (ws_content ws) <= 2 ^ 18 -> field_compatible t_wseries (DOT _content) p ->
  data_at Ews (tarray tuchar (Zlength (ws_content ws))) (zbytes (ws_content ws)) (field_address t_wseries (DOT _content) p) *
  data_at Ews (tarray tuchar (262144 - Zlength (ws_content ws))) (Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws)))
     (field_address0 (tarray tuchar 262144) (SUB (Zlength (ws_content ws))) (field_address t_wseries (DOT _content) p))
  |-- field_at Ews t_wseries (DOT _content) (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws))) p.
Proof. intros Hn Hfc. rewrite (VLI_content_split ws p Hn Hfc). apply derives_refl. Qed.

Lemma VLI_ltu64 x y : 0 <= x <= Int64.max_unsigned -> 0 <= y <= Int64.max_unsigned ->
  Int64.ltu (Int64.repr x) (Int64.repr y) = (x <? y).
Proof.
  intros Hx Hy. unfold Int64.ltu. rewrite !Int64.unsigned_repr by lia.
  destruct (zlt x y); destruct (Z.ltb_spec x y); lia || reflexivity.
Qed.


(* ---------- main's precondition: the decoder's tables, the writer's statics, sr and wd ---------- *)

Lemma VLD_filter_filter {A: Type} (f g: A -> bool) l :
  filter f (filter g l) = filter (fun x => andb (g x) (f x)) l.
Proof.
  induction l as [|a l IH]; simpl; auto.
  destruct (g a); simpl; [destruct (f a); simpl; rewrite IH; auto | exact IH].
Qed.

Lemma VLD_wvar_not_zstd : forallb (fun i => negb (id_in_list i MainPre6.zstd_var_ids)) wvar_ids = true.
Proof. vm_compute. reflexivity. Qed.

Lemma VLD_wvardefs :
  filter (fun ig => id_in_list (fst ig) wvar_ids)
    (filter (fun ig => negb (id_in_list (fst ig) MainPre6.zstd_var_ids)) (Vardefs Zstd.contracts.x_valid_bufferless.whole_prog))
  = wvardefs.
Proof.
  rewrite VLD_filter_filter. unfold wvardefs. apply filter_ext. intros [i g]; cbn [fst].
  destruct (id_in_list i wvar_ids) eqn:E; [|apply andb_false_r].
  rewrite andb_true_r.
  pose proof VLD_wvar_not_zstd as H. rewrite forallb_forall in H.
  apply id_in_list_true in E. exact (H i E).
Qed.

Lemma VLD_InitGPred_in x l gv : In x l -> InitGPred l gv |-- globs2pred gv x * TT.
Proof.
  intros Hin. apply in_split in Hin as [l1 [l2 ->]].
  rewrite InitGPred_middleD. rewrite sepcon_assoc. apply sepcon_derives; [apply derives_refl | apply TT_right].
Qed.

Local Notation VLD_rest :=
  (filter (fun ig : ident * globdef (fundef function) type => negb (id_in_list (fst ig) wvar_ids))
    (filter (fun ig : ident * globdef (fundef function) type => negb (id_in_list (fst ig) MainPre6.zstd_var_ids))
       (Vardefs Zstd.contracts.x_valid_bufferless.whole_prog))).

Lemma VLD_sr_in : In (_x_valid_bufferless__sr, Gvar v_x_valid_bufferless__sr) VLD_rest.
Proof.
  rewrite !filter_In. split; [split|].
  - unfold Vardefs. apply filter_In. split; [|reflexivity].
    apply Maps.PTree.elements_correct. vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.

Lemma VLD_wd_in :
  In (_vb_wd, Gvar v_vb_wd)
    (filter (fun x : ident * globdef (fundef function) type => negb (Pos.eqb (fst x) _x_valid_bufferless__sr)) VLD_rest).
Proof.
  rewrite filter_In. split; [|vm_compute; reflexivity].
  rewrite !filter_In. split; [split|].
  - unfold Vardefs. apply filter_In. split; [|reflexivity].
    apply Maps.PTree.elements_correct. vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.

Lemma VLD_sr_only :
  filter (fun x : ident * globdef (fundef function) type => Pos.eqb (fst x) _x_valid_bufferless__sr) VLD_rest = [(_x_valid_bufferless__sr, Gvar v_x_valid_bufferless__sr)].
Proof. vm_compute. reflexivity. Qed.

Lemma VLD_sr_zero gv :
  globs2pred gv (_x_valid_bufferless__sr, Gvar v_x_valid_bufferless__sr) |-- data_at Ews t_wseries (zero_val t_wseries) (gv _x_valid_bufferless__sr).
Proof.
  unfold globs2pred. apply derives_extract_prop; intros Hh.
  unfold globvar2pred. simpl. rewrite sepcon_emp.
  change 786936 with (@sizeof HCS t_wseries).
  apply mapsto_zero_data_at_zero.
  - auto.
  - reflexivity.
  - reflexivity.
  - destruct Hh as [b ->]. repeat split; auto.
    hnf. rewrite Ptrofs.unsigned_zero. apply la_env_cs_sound; vm_compute; reflexivity.
Qed.

Lemma VLD_wd_zero gv :
  globs2pred gv (_vb_wd, Gvar v_vb_wd) |-- data_at Ews t_wdict (zero_val t_wdict) (gv _vb_wd).
Proof.
  unfold globs2pred. apply derives_extract_prop; intros Hh.
  unfold globvar2pred. simpl. rewrite sepcon_emp.
  change 13984 with (@sizeof HCS t_wdict).
  apply mapsto_zero_data_at_zero.
  - auto.
  - reflexivity.
  - reflexivity.
  - destruct Hh as [b ->]. repeat split; auto.
    hnf. rewrite Ptrofs.unsigned_zero. apply la_env_cs_sound; vm_compute; reflexivity.
Qed.

Lemma VLD_rest_zero gv :
  InitGPred VLD_rest gv |--
  data_at Ews t_wseries (zero_val t_wseries) (gv _x_valid_bufferless__sr) *
  (data_at Ews t_wdict (zero_val t_wdict) (gv _vb_wd) * TT).
Proof.
  rewrite (MainPre6.MP_InitGPred_filter (fun x : ident * globdef (fundef function) type => Pos.eqb (fst x) _x_valid_bufferless__sr)).
  rewrite VLD_sr_only. rewrite InitGPred_consD, InitGPred_nilD, sepcon_emp.
  apply sepcon_derives; [apply VLD_sr_zero|].
  eapply derives_trans; [apply VLD_InitGPred_in, VLD_wd_in|].
  apply sepcon_derives; [apply VLD_wd_zero | apply derives_refl].
Qed.

Lemma VLD_pre (WG: globals -> mpred) (HWG: forall gv, InitGPred wvardefs gv |-- WG gv) gv :
  globals_ok gv ->
  InitGPred (Vardefs Zstd.contracts.x_valid_bufferless.whole_prog) gv |--
  zstd_globals gv * (WG gv * (data_at Ews t_wseries (zero_val t_wseries) (gv _x_valid_bufferless__sr) *
                              (data_at Ews t_wdict (zero_val t_wdict) (gv _vb_wd) * TT))).
Proof.
  intros Hgv. eapply derives_trans.
  - apply (MainPre6.main_pre_fact6 Zstd.contracts.x_valid_bufferless.whole_prog); [|exact Hgv].
    unfold MainPre6.all_progs. do 16 right; left; reflexivity.
  - apply sepcon_derives; [apply derives_refl|].
    rewrite (MainPre6.MP_InitGPred_filter (fun ig => id_in_list (fst ig) wvar_ids)).
    rewrite VLD_wvardefs. apply sepcon_derives; [apply HWG|].
    exact (VLD_rest_zero gv).
Qed.

(* ---------- compspecs: the API's (decoder) and main's (this unit) ---------- *)

Definition VLD_cce (cs1 cs2: compspecs) : change_composite_env cs1 cs2 :=
  {| coeq := cs_preserve_env cs1 cs2;
     coeq_consistent := cs_preserve_env_consistent cs1 cs2 _ eq_refl;
     coeq_complete := cs_preserve_completeness cs1 cs2 _ eq_refl |}.

Lemma VLD_arr: forall sh n (v: list val) p,
  @data_at ZCS sh (tarray tuchar n) v p = @data_at HCS sh (tarray tuchar n) v p.
Proof.
  intros. pose proof (@data_at_change_composite ZCS HCS (VLD_cce ZCS HCS) sh (tarray tuchar n) v v
    (JMeq_refl _) ltac:(reflexivity)) as E. rewrite E; reflexivity.
Qed.

Lemma VLD_arr_: forall sh n p,
  @data_at_ ZCS sh (tarray tuchar n) p = @data_at_ HCS sh (tarray tuchar n) p.
Proof.
  intros. pose proof (@data_at__change_composite ZCS HCS (VLD_cce ZCS HCS) sh (tarray tuchar n)
    ltac:(reflexivity)) as E. rewrite E; reflexivity.
Qed.

Lemma VLD_Externals : Externals = [nondet_u32_spec; gp_assert_spec; gp_assume_spec].
Proof.
  unfold Externals, present, env_harness, filter.
  repeat match goal with |- context [id_in_list ?i ?l] =>
    let b := eval lazy in (id_in_list i l) in change (id_in_list i l) with b end.
  reflexivity.
Qed.

Lemma VLD_tyc_g_isSome: forall (V: varspecs) G i, In i (map fst V) ->
  isSome (Maps.PTree.get i (make_tycontext_g V G)).
Proof.
  intros. unfold make_tycontext_g. induction G as [|[j f] G IH]; simpl.
  - induction V as [|[k t] V IHV]; simpl in *; [contradiction|].
    rewrite Maps.PTree.gsspec. destruct (peq i k); simpl; auto.
    apply IHV. destruct H; [congruence|auto].
  - rewrite Maps.PTree.gsspec. destruct (peq i j); simpl; auto.
Qed.

(* ---------- sr field by field (a load from the whole struct overflows the stack) ---------- *)

(* ---------- sr field by field (a load from the whole struct overflows the stack) ---------- *)

Lemma VLD_sr_nframes ws : snd (snd (snd (snd (snd (wseries_val ws))))) = vu (Zlength (ws_frames ws)).
Proof. reflexivity. Qed.

Lemma VLD_sr_f ws : fst (snd (snd (snd (snd (wseries_val ws))))) =
  map winfo_val (ws_frames ws) ++ Zrepeat (winfo_val winfo0) (4 - Zlength (ws_frames ws)).
Proof. reflexivity. Qed.

Lemma VLD_sr_content_n ws : fst (snd (snd (snd (wseries_val ws)))) = vl (Zlength (ws_content ws)).
Proof. reflexivity. Qed.

Lemma VLD_sr_content ws : fst (snd (snd (wseries_val ws))) =
  zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws)).
Proof. reflexivity. Qed.

Lemma VLD_sr_bytes ws : fst (wseries_val ws) =
  zbytes (ws_bytes ws) ++ Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength (ws_bytes ws)).
Proof. reflexivity. Qed.

Lemma VLD_bytes_split ws p : field_compatible t_wseries (DOT _bytes) p -> Zlength (ws_bytes ws) <= 2 ^ 19 ->
  field_at Ews t_wseries (DOT _bytes) (fst (wseries_val ws)) p =
  (data_at Ews (tarray tuchar (Zlength (ws_bytes ws))) (zbytes (ws_bytes ws)) p *
   data_at Ews (tarray tuchar (2 ^ 19 - Zlength (ws_bytes ws))) (Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength (ws_bytes ws)))
     (offset_val (Zlength (ws_bytes ws)) p))%logic.
Proof.
  intros Hf Hl. rewrite field_at_data_at. rewrite VLD_sr_bytes.
  rewrite field_address_offset by auto. simpl nested_field_offset. rewrite isptr_offset_val_zero by auto with field_compatible.
  change (nested_field_type t_wseries (DOT _bytes)) with (tarray tuchar 524288).
  assert (Hz: Zlength (zbytes (ws_bytes ws)) = Zlength (ws_bytes ws)) by (unfold zbytes; apply Zlength_map).
  pose proof (Zlength_nonneg (ws_bytes ws)).
  rewrite (split2_data_at_Tarray_app (Zlength (ws_bytes ws)) 524288 Ews tuchar (zbytes (ws_bytes ws))
             (Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength (ws_bytes ws)))); auto.
  - assert (Hf': field_compatible (tarray tuchar 524288) [] p).
    { pose proof (field_compatible_nested_field _ _ _ Hf) as X.
      change (nested_field_type t_wseries (DOT _bytes)) with (tarray tuchar 524288) in X.
      change (nested_field_offset t_wseries (DOT _bytes)) with 0 in X.
      rewrite isptr_offset_val_zero in X by auto with field_compatible. exact X. }
    rewrite field_address0_offset by auto with field_compatible.
    simpl nested_field_offset. rewrite Z.mul_1_l, Z.add_0_l. reflexivity.
  - rewrite Zlength_Zrepeat by lia. lia.
Qed.

Lemma VLD_sr_n ws : fst (snd (wseries_val ws)) = vl (Zlength (ws_bytes ws)).
Proof. reflexivity. Qed.

Ltac VL_kill :=
  match goal with
  | H: false = true |- _ => discriminate H
  | H: true = false |- _ => discriminate H
  | H: ?x <> ?x |- _ => exfalso; exact (H eq_refl)
  | H: Int.repr ?x = Int.repr ?y |- _ =>
      exfalso; apply repr_inj_unsigned in H; [lia | rep_lia | rep_lia]
  | H: typed_true _ _ |- _ => inv H
  | H: typed_false _ _ |- _ => inv H
  end.

Ltac VL_ifs := repeat apply -> seq_assoc; apply semax_if_seq; forward_if; try solve [VL_kill | exfalso; lia].

