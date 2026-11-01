(* MainOK of the unit detect: the main of detect adapted to API v3 from its v2 proof. *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.harness.detect.WTopSpecs_detect.
Require Import Zstd.proof.harness.detect.DetectModel.
Require Import Zstd.proof.zstd.ApiBridge Zstd.proof.model.ParamsDflt.
Require Zstd.proof.top.MainPre6.

Local Notation ZCS := Zstd.proof.zstd.Base.CompSpecs.
Local Notation HCS := Zstd.proof.harness.detect.HOK_detect.CompSpecs.

(* ---------- main's precondition: the decoder's tables, the writer's statics, sr ---------- *)

Lemma WD_filter_filter {A: Type} (f g: A -> bool) l :
  filter f (filter g l) = filter (fun x => andb (g x) (f x)) l.
Proof.
  induction l as [|a l IH]; simpl; auto.
  destruct (g a); simpl; [destruct (f a); simpl; rewrite IH; auto | exact IH].
Qed.

Lemma WD_wvar_not_zstd : forallb (fun i => negb (id_in_list i MainPre6.zstd_var_ids)) wvar_ids = true.
Proof. vm_compute. reflexivity. Qed.

Lemma WD_wvardefs :
  filter (fun ig => id_in_list (fst ig) wvar_ids)
    (filter (fun ig => negb (id_in_list (fst ig) MainPre6.zstd_var_ids)) (Vardefs Zstd.contracts.x_detect.whole_prog))
  = wvardefs.
Proof.
  rewrite WD_filter_filter. unfold wvardefs. apply filter_ext. intros [i g]; cbn [fst].
  destruct (id_in_list i wvar_ids) eqn:E; [|apply andb_false_r].
  rewrite andb_true_r.
  pose proof WD_wvar_not_zstd as H. rewrite forallb_forall in H.
  apply id_in_list_true in E. exact (H i E).
Qed.

Lemma WD_InitGPred_in x l gv : In x l -> InitGPred l gv |-- globs2pred gv x * TT.
Proof.
  intros Hin. apply in_split in Hin as [l1 [l2 ->]].
  rewrite InitGPred_middleD. rewrite sepcon_assoc. apply sepcon_derives; [apply derives_refl | apply TT_right].
Qed.

Lemma WD_sr_in :
  In (_x_detect__sr, Gvar v_x_detect__sr)
    (filter (fun ig => negb (id_in_list (fst ig) wvar_ids))
      (filter (fun ig => negb (id_in_list (fst ig) MainPre6.zstd_var_ids)) (Vardefs Zstd.contracts.x_detect.whole_prog))).
Proof.
  rewrite !filter_In. split; [split|].
  - unfold Vardefs. apply filter_In. split; [|reflexivity].
    apply Maps.PTree.elements_correct. vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.

Lemma WD_sr_zero gv :
  globs2pred gv (_x_detect__sr, Gvar v_x_detect__sr) |-- data_at Ews t_wseries (zero_val t_wseries) (gv _x_detect__sr).
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

Lemma WD_pre (WG: globals -> mpred) (HWG: forall gv, InitGPred wvardefs gv |-- WG gv) gv :
  globals_ok gv ->
  InitGPred (Vardefs Zstd.contracts.x_detect.whole_prog) gv |--
  zstd_globals gv * (WG gv * (data_at Ews t_wseries (zero_val t_wseries) (gv _x_detect__sr) * TT)).
Proof.
  intros Hgv. eapply derives_trans.
  - apply (MainPre6.main_pre_fact6 Zstd.contracts.x_detect.whole_prog); [|exact Hgv].
    unfold MainPre6.all_progs. do 6 right; left; reflexivity.
  - apply sepcon_derives; [apply derives_refl|].
    rewrite (MainPre6.MP_InitGPred_filter (fun ig => id_in_list (fst ig) wvar_ids)).
    rewrite WD_wvardefs. apply sepcon_derives; [apply HWG|].
    eapply derives_trans; [apply WD_InitGPred_in, WD_sr_in|].
    apply sepcon_derives; [apply WD_sr_zero | apply derives_refl].
Qed.

(* ---------- compspecs: the API's (decoder) and main's (this unit) ---------- *)

Definition WD_cce (cs1 cs2: compspecs) : change_composite_env cs1 cs2 :=
  {| coeq := cs_preserve_env cs1 cs2;
     coeq_consistent := cs_preserve_env_consistent cs1 cs2 _ eq_refl;
     coeq_complete := cs_preserve_completeness cs1 cs2 _ eq_refl |}.

Local Notation tout := (Tstruct _ZSTD_outBuffer_s noattr).
Local Notation tin := (Tstruct _ZSTD_inBuffer_s noattr).

Lemma WD_arr: forall sh n (v: list val) p,
  @data_at ZCS sh (tarray tuchar n) v p = @data_at HCS sh (tarray tuchar n) v p.
Proof.
  intros. pose proof (@data_at_change_composite ZCS HCS (WD_cce ZCS HCS) sh (tarray tuchar n) v v
    (JMeq_refl _) ltac:(reflexivity)) as E. rewrite E; reflexivity.
Qed.

Lemma WD_arr_: forall sh n p,
  @data_at_ ZCS sh (tarray tuchar n) p = @data_at_ HCS sh (tarray tuchar n) p.
Proof.
  intros. pose proof (@data_at__change_composite ZCS HCS (WD_cce ZCS HCS) sh (tarray tuchar n)
    ltac:(reflexivity)) as E. rewrite E; reflexivity.
Qed.

Lemma WD_out: forall sh (a b c: val) p,
  @data_at ZCS sh t_outBuffer (a, (b, c)) p = @data_at HCS sh tout (a, (b, c)) p.
Proof.
  intros. pose proof (@data_at_change_composite ZCS HCS (WD_cce ZCS HCS) sh tout (a, (b, c)) (a, (b, c))
    (JMeq_refl _) ltac:(vm_compute; reflexivity)) as E. exact (f_equal (fun f => f p) E).
Qed.

Lemma WD_in: forall sh (a b c: val) p,
  @data_at ZCS sh t_inBuffer (a, (b, c)) p = @data_at HCS sh tin (a, (b, c)) p.
Proof.
  intros. pose proof (@data_at_change_composite ZCS HCS (WD_cce ZCS HCS) sh tin (a, (b, c)) (a, (b, c))
    (JMeq_refl _) ltac:(vm_compute; reflexivity)) as E. exact (f_equal (fun f => f p) E).
Qed.

Lemma WD_Externals : Externals = [nondet_u32_spec; gp_assert_spec; gp_assume_spec].
Proof.
  unfold Externals, present, env_harness, filter.
  repeat match goal with |- context [id_in_list ?i ?l] =>
    let b := eval lazy in (id_in_list i l) in change (id_in_list i l) with b end.
  reflexivity.
Qed.

Lemma WD_tyc_g_isSome: forall (V: varspecs) G i, In i (map fst V) ->
  isSome (Maps.PTree.get i (make_tycontext_g V G)).
Proof.
  intros. unfold make_tycontext_g. induction G as [|[j f] G IH]; simpl.
  - induction V as [|[k t] V IHV]; simpl in *; [contradiction|].
    rewrite Maps.PTree.gsspec. destruct (peq i k); simpl; auto.
    apply IHV. destruct H; [congruence|auto].
  - rewrite Maps.PTree.gsspec. destruct (peq i j); simpl; auto.
Qed.

(* sr field by field (unfold_data_at on an abstract value: fast; on wseries_val: minutes) *)
Lemma WD_sr_split sh (v: reptype t_wseries) p :
  data_at sh t_wseries v p =
  (field_at sh t_wseries (DOT _bytes) (fst v) p * field_at sh t_wseries (DOT _n) (fst (snd v)) p *
   field_at sh t_wseries (DOT _content) (fst (snd (snd v))) p *
   field_at sh t_wseries (DOT _content_n) (fst (snd (snd (snd v)))) p *
   field_at sh t_wseries (DOT _f) (fst (snd (snd (snd (snd v))))) p *
   field_at sh t_wseries (DOT _nframes) (snd (snd (snd (snd (snd v))))) p *
   spacer sh 786932 786936 p)%logic.
Proof.
  unfold_data_at (data_at _ _ _ p).
  rewrite !sepcon_assoc. reflexivity.
Qed.

(* one byte of sr.bytes as its own cell (VST's array-element load on the whole 2^19-byte field overflows
   the stack) *)
Lemma WD_bytes_split sh (VB: list val) i p : 0 <= i < 524288 -> Zlength VB = 524288 ->
  field_at sh t_wseries (DOT _bytes) VB p =
  (array_at sh t_wseries (DOT _bytes) 0 i (sublist 0 i VB) p *
   field_at sh t_wseries (DOT _bytes SUB i) (Znth i VB) p *
   array_at sh t_wseries (DOT _bytes) (i + 1) 524288 (sublist (i + 1) 524288 VB) p)%logic.
Proof.
  intros Hi Hl.
  erewrite field_at_Tarray; [ | auto with field_compatible | reflexivity | lia | apply JMeq_refl].
  2: { split; [exact I | left; reflexivity]. }
  erewrite (split3_array_at sh t_wseries (DOT _bytes) 0 i 524288); [| lia | exact Hl | rewrite Z.sub_0_r; apply JMeq_refl].
  rewrite !Z.sub_0_r. reflexivity.
Qed.

Lemma WD_bytes_join sh (VB: list val) i v p : 0 <= i < 524288 -> Zlength VB = 524288 ->
  (array_at sh t_wseries (DOT _bytes) 0 i (sublist 0 i VB) p *
   field_at sh t_wseries (DOT _bytes SUB i) v p *
   array_at sh t_wseries (DOT _bytes) (i + 1) 524288 (sublist (i + 1) 524288 VB) p)%logic
  |-- field_at sh t_wseries (DOT _bytes) (upd_Znth i VB v) p.
Proof.
  intros Hi Hl.
  rewrite (WD_bytes_split sh (upd_Znth i VB v) i p) by (try rewrite Zlength_upd_Znth; lia).
  rewrite upd_Znth_same by lia.
  rewrite sublist_upd_Znth_l by lia. rewrite sublist_upd_Znth_r by lia.
  apply derives_refl.
Qed.

Lemma WD_byte_tc b : 0 <= b <= Byte.max_unsigned -> tc_val tuchar (Vint (Int.repr b)).
Proof. intros. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. Qed.

(* ---------- byte arithmetic of the corruption ---------- *)
Lemma WD_log2_byte a : 0 <= a < 256 -> Z.log2 a < 8.
Proof.
  intros. destruct (Z.eq_dec a 0) as [->|]; [simpl; lia|].
  apply Z.log2_lt_pow2; lia.
Qed.

Lemma WD_byte_of_log2 a : 0 <= a -> Z.log2 a < 8 -> a < 256.
Proof.
  intros. destruct (Z.eq_dec a 0) as [->|]; [lia|].
  change 256 with (2 ^ 8). apply Z.log2_lt_pow2; lia.
Qed.

Lemma WD_lxor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lxor a b < 256.
Proof.
  intros. assert (0 <= Z.lxor a b) by (apply Z.lxor_nonneg; lia).
  split; [lia|]. apply WD_byte_of_log2; [lia|].
  eapply Z.le_lt_trans; [apply Z.log2_lxor; lia|].
  apply Z.max_lub_lt; apply WD_log2_byte; lia.
Qed.

Lemma WD_lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
  intros. assert (0 <= Z.lor a b) by (apply Z.lor_nonneg; lia).
  split; [lia|]. apply WD_byte_of_log2; [lia|].
  rewrite Z.log2_lor by lia.
  apply Z.max_lub_lt; apply WD_log2_byte; lia.
Qed.

Lemma WD_zext8 c : 0 <= c < 256 -> Int.zero_ext 8 (Int.repr c) = Int.repr c.
Proof.
  intros. unfold Int.zero_ext. rewrite Int.unsigned_repr by rep_lia.
  rewrite Zbits.Zzero_ext_mod by lia. rewrite Z.mod_small; [reflexivity|].
  change (two_p 8) with 256. lia.
Qed.

Lemma WD_xor_byte b x i : 0 <= b <= Byte.max_unsigned -> 0 <= x <= Int.max_unsigned -> 0 <= i < 4 ->
  Int.zero_ext 8 (Int.xor (Int.repr b) (Int.zero_ext 8 (Int.and (Int.shru (Int.repr x)
    (Int.mul (Int.repr 8) (Int.repr i))) (Int.repr 255)))) =
  Int.repr (Z.lxor b (Z.land (Z.shiftr x (8 * i)) 255)).
Proof.
  intros Hb Hx Hi.
  assert (Hs: 0 <= Z.shiftr x (8 * i) <= x).
  { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia]|].
    apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia|].
    assert (1 <= 2 ^ (8 * i)) by (apply Z.pow_le_mono_r with (a := 2) (b := 0) (c := 8 * i) ; lia). nia. }
  assert (Hl: 0 <= Z.land (Z.shiftr x (8 * i)) 255 < 256).
  { change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
    apply Z.mod_pos_bound. lia. }
  rewrite mul_repr. unfold Int.shru. rewrite !Int.unsigned_repr by rep_lia.
  unfold Int.and. rewrite !Int.unsigned_repr by rep_lia.
  rewrite WD_zext8 by lia.
  unfold Int.xor. rewrite !Int.unsigned_repr by rep_lia.
  apply WD_zext8. apply WD_lxor_byte; rep_lia.
Qed.

Lemma WD_or_byte b : 0 <= b <= Byte.max_unsigned ->
  Int.zero_ext 8 (Int.or (Int.repr b) (Int.repr 8)) = Int.repr (Z.lor b 8).
Proof.
  intros Hb. unfold Int.or. rewrite !Int.unsigned_repr by rep_lia.
  apply WD_zext8. apply WD_lor_byte; rep_lia.
Qed.

Lemma WD_bytes_prefix sh (A: list Z) p : Zlength A <= 524288 ->
  field_at sh t_wseries (DOT _bytes) (zbytes A ++ Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength A)) p |--
  (data_at sh (tarray tuchar (Zlength A)) (zbytes A) (field_address t_wseries (DOT _bytes) p) * TT)%logic.
Proof.
  intros HA.
  rewrite field_at_data_at.
  change (nested_field_type t_wseries (DOT _bytes)) with (tarray tuchar 524288).
  rewrite (split2_data_at_Tarray_app (Zlength A) 524288) by (rewrite ?Zlength_map, ?Zlength_Zrepeat; lia).
  cancel.
Qed.

(* the witnesses lent to ZSTD_decompressStream: the unused byte of ib = malloc(1) when ilen = 0 *)
Definition WD_W (il: Z) (ib: val) : list ptr_witness :=
  if zeq il 0 then [pw_bytes Ews 1 [Vundef] ib] else [].

Lemma WD_buf_ok_pos W n p : 0 < n -> buf_ok W Ews n p.
Proof.
  intros Hn. unfold buf_ok. rewrite data_at__memory_block. rewrite sepcon_andp_prop.
  apply derives_extract_prop; intros FC.
  replace (sizeof (tarray tuchar n)) with n by (simpl; lia).
  assert (Hp: isptr p) by (destruct FC; auto).
  apply andp_right; apply sepcon_weak_valid_pointer2.
  - eapply derives_trans; [apply (memory_block_weak_valid_pointer Ews n p 0); auto; try lia |].
    rewrite isptr_offset_val_zero by auto. apply derives_refl.
  - apply memory_block_weak_valid_pointer; auto; lia.
Qed.

Lemma WD_buf_ok_zero p c : buf_ok [pw_bytes Ews 1 c p] Ews 0 p.
Proof.
  unfold buf_ok, pws_pred. simpl map. simpl fold_right. cbn [pw_pred]. rewrite sepcon_emp.
  assert_PROP (isptr p) by (saturate_local; apply prop_right; match goal with H: field_compatible _ _ p |- _ => destruct H as [? _]; auto end).
  rewrite isptr_offset_val_zero by auto.
  apply andp_right; apply sepcon_weak_valid_pointer1;
    (eapply derives_trans; [apply data_at_valid_ptr; auto; simpl; lia | apply valid_pointer_weak]).
Qed.

Lemma WD_ib_split ib il m A : Zlength A = il -> (0 < il /\ m = il) \/ (il = 0 /\ m = 1) ->
  @data_at ZCS Ews (tarray tuchar m) (A ++ Zrepeat Vundef (m - il)) ib |--
  !!(buf_ok (WD_W il ib) Ews il ib) && (@data_at ZCS Ews (tarray tuchar il) A ib * pws_pred (WD_W il ib)).
Proof.
  intros HA [[Hil ->] | [-> ->]].
  - unfold WD_W. destruct (zeq il 0); [lia|]. rewrite Z.sub_diag.
    change (Zrepeat Vundef 0) with (@nil val). rewrite app_nil_r.
    unfold pws_pred; simpl. rewrite sepcon_emp.
    apply andp_right; [apply prop_right; apply WD_buf_ok_pos; lia | apply derives_refl].
  - apply Zlength_nil_inv in HA. subst A. unfold WD_W. rewrite if_true by auto.
    apply andp_right; [apply prop_right; apply WD_buf_ok_zero|].
    unfold pws_pred; simpl. rewrite sepcon_emp.
    assert_PROP (isptr ib) by (saturate_local; apply prop_right; match goal with H: field_compatible _ _ ib |- _ => destruct H as [? _]; auto end).
    change (Zrepeat Vundef (1 - 0)) with [Vundef]. change (Zrepeat Vundef 1) with [Vundef].
    rewrite <- (emp_sepcon (@data_at ZCS Ews (tarray tuchar 1) [Vundef] ib)) at 1.
    apply sepcon_derives; [apply data_at_zero_array; auto | apply derives_refl].
Qed.

Lemma WD_ib_join ib il m A : (0 < il /\ m = il) \/ (il = 0 /\ m = 1) ->
  @data_at ZCS Ews (tarray tuchar il) A ib * pws_pred (WD_W il ib) |-- @data_at_ ZCS Ews (tarray tuchar m) ib.
Proof.
  intros [[Hil ->] | [-> ->]].
  - unfold WD_W. destruct (zeq il 0); [lia|]. unfold pws_pred; simpl. rewrite sepcon_emp.
    apply data_at_data_at_.
  - unfold WD_W. rewrite if_true by auto. unfold pws_pred; simpl. rewrite sepcon_emp.
    assert_PROP (A = []) by (entailer!; apply Zlength_nil_inv; auto). subst A.
    sep_apply (@data_at_zero_array_inv ZCS Ews tuchar (@nil val) ib); auto.
    rewrite emp_sepcon. apply data_at_data_at_.
Qed.

Lemma WD_dst_split cap m dst : (0 < cap /\ m = cap) \/ (cap = 0 /\ m = 1) ->
  @data_at_ ZCS Ews (tarray tuchar m) dst |--
  !!(buf_ok (WD_W cap dst) Ews cap dst) &&
  (@data_at_ ZCS Ews (tarray tuchar cap) dst * pws_pred (WD_W cap dst)).
Proof.
  intros Hm.
  assert (Hc: 0 <= cap) by lia.
  change (@data_at_ ZCS Ews (tarray tuchar m) dst) with (@data_at ZCS Ews (tarray tuchar m) (Zrepeat Vundef m) dst).
  change (@data_at_ ZCS Ews (tarray tuchar cap) dst) with (@data_at ZCS Ews (tarray tuchar cap) (Zrepeat Vundef cap) dst).
  replace (Zrepeat Vundef m) with (Zrepeat Vundef cap ++ Zrepeat Vundef (m - cap))
    by (rewrite Zrepeat_app by lia; f_equal; lia).
  apply WD_ib_split; [apply Zlength_Zrepeat; lia | exact Hm].
Qed.

Lemma WD_ltu_Z x y : 0 <= x <= Int64.max_unsigned -> 0 <= y <= Int64.max_unsigned ->
  Int64.ltu (Int64.repr x) (Int64.repr y) = (x <? y).
Proof.
  intros. unfold Int64.ltu. rewrite !Int64.unsigned_repr by lia.
  destruct (zlt x y); symmetry; [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Qed.

Lemma WD_repr1_neq0: Int.repr 1 <> Int.zero.
Proof. intro H; inv H. Qed.

(* the copy src split around the chunk [a, a+l) *)
Lemma WD_src_split sh (bs: list Z) a l p : 0 <= a -> 0 <= l -> a + l <= Zlength bs ->
  field_compatible (tarray tuchar (Zlength bs)) [] p ->
  data_at sh (tarray tuchar (Zlength bs)) (zbytes bs) p =
  (data_at sh (tarray tuchar a) (zbytes (sublist 0 a bs)) p *
   data_at sh (tarray tuchar l) (zbytes (sublist a (a + l) bs)) (offset_val a p) *
   data_at sh (tarray tuchar (Zlength bs - (a + l))) (zbytes (sublist (a + l) (Zlength bs) bs))
     (offset_val (a + l) p))%logic.
Proof.
  intros Ha Hl Hal Hfc.
  unfold tarray.
  rewrite (split3_data_at_Tarray_tuchar sh (Zlength bs) a (a + l)) by (rewrite ?Zlength_map; lia).
  rewrite !field_address0_offset.
  2, 3: destruct Hfc as (?&?&?&?&?); repeat split; auto; simpl; lia.
  simpl nested_field_offset. rewrite !Z.mul_1_l, !Z.add_0_l.
  rewrite !sublist_map. replace (a + l - a) with l by lia. reflexivity.
Qed.

Lemma WD_if_data_at_ sh t q (v: reptype t) :
  (if eq_dec q nullval then emp else (malloc_token sh t q * data_at sh t v q))%logic |--
  (if eq_dec q nullval then emp else (malloc_token sh t q * data_at_ sh t q))%logic.
Proof. destruct (eq_dec q nullval); [apply derives_refl | cancel]. Qed.

Lemma WD_vp (P R: mpred) p : (P && valid_pointer p) * R |-- valid_pointer p.
Proof. apply sepcon_valid_pointer1. apply andp_left2. apply derives_refl. Qed.

Lemma WD_prefix (s: list Z) m : 0 <= m <= Zlength s -> is_prefix (sublist 0 m s) s.
Proof.
  intros Hm. unfold is_prefix. rewrite sublist_firstn.
  rewrite firstn_length_le by (rewrite <- ZtoNat_Zlength; lia). reflexivity.
Qed.

Lemma WD_sin (s: list Z) ipos il ip : 0 <= ipos -> 0 <= ip <= il -> ipos + il <= Zlength s ->
  sublist 0 ipos s ++ sublist 0 ip (sublist ipos (ipos + il) s) = sublist 0 (ipos + ip) s.
Proof.
  intros. rewrite sublist_sublist by lia. rewrite ?Z.add_0_r, ?Z.add_0_l.
  rewrite sublist_rejoin by lia. f_equal; lia.
Qed.

Lemma WD_zero_le {sin0 sout0: list Z} {a1: Z} sin sall sout ocap s st :
  stream_claims sin0 sout0 sin sall sout a1 ocap 0 -> bytes_ok s -> is_prefix sin s ->
  snd (series_frames no_dict no_wlim s) <> TUnk ->
  Forall (fun fr => fr_end fr <= st) (fst (series_frames no_dict no_wlim s)) ->
  Zlength sin <= st.
Proof.
  intros Hc Hb Hp Ht Hf.
  destruct (Hc s Hb Hp) as (_ & Hz & _).
  destruct (Hz eq_refl Ht) as (n & Hn & Hl & _).
  rewrite Hl. rewrite Forall_forall in Hf. apply Hf.
  apply nth_In. lia.
Qed.

(* the bytes zstd has read after a call: up to the caller's new position plus the hostage byte *)
Lemma WD_sin2 (s: list Z) ipos ah ilen q : 0 <= ipos -> 0 <= ah -> ipos + ah <= Zlength s -> 0 <= ilen ->
  ipos + ilen <= Zlength s -> ah <= q -> (q <= ilen \/ q = ah) ->
  sublist 0 (ipos + ah) s ++ sublist (0 + ah) q (sublist ipos (ipos + ilen) s) = sublist 0 (ipos + q) s.
Proof.
  intros. rewrite Z.add_0_l. destruct H5 as [Hq | ->].
  - rewrite sublist_sublist by lia. replace (ah + ipos) with (ipos + ah) by lia.
    replace (q + ipos) with (ipos + q) by lia. rewrite sublist_rejoin by lia. reflexivity.
  - rewrite sublist_nil, app_nil_r. reflexivity.
Qed.

(* DM_detect's frame facts on any window limit (stream_claims' zero clause uses no_wlim) *)
Lemma WD_detect_frames ws k s' wl :
  series_facts no_dict ws -> wseries_wf ws -> (k < length (ws_frames ws))%nat ->
  wi_skippable (nth k (ws_frames ws) winfo0) = false ->
  ((exists x, wi_checksum (nth k (ws_frames ws) winfo0) = true /\ 0 < x < 2 ^ 32 /\
     s' = xorn (ws_bytes ws)
            (wi_start (nth k (ws_frames ws) winfo0) + wi_size (nth k (ws_frames ws) winfo0) - 4) x 4) \/
   s' = set_bit3 (ws_bytes ws) (wi_start (nth k (ws_frames ws) winfo0) + 4)) ->
  snd (series_frames no_dict wl s') <> TUnk /\
  Forall (fun fr => fr_end fr <= wi_start (nth k (ws_frames ws) winfo0))
         (fst (series_frames no_dict wl s')).
Proof.
  intros Hsf Hwf Hk Hsk Hs'.
  destruct (DM_corrupt_frames ws k s' wl Hsf Hwf Hk Hsk Hs') as (r2 & Hr2 & E2).
  split.
  - rewrite E2. simpl. destruct (all_ok wl (firstn k (ws_frames ws))); [destruct Hr2 as [->| ->]|]; simpl; congruence.
  - rewrite E2. simpl. rewrite Forall_map, Forall_forall. intros g Hg.
    apply ok_prefix_In in Hg. apply (In_nth _ _ winfo0) in Hg. destruct Hg as (j & Hj & <-).
    rewrite firstn_length in Hj. rewrite nth_firstn. destruct (Nat.ltb_spec j k); [|lia].
    unfold fr_end. simpl. pose proof Hsf as (_ & _ & _ & _ & _ & Ht & _).
    eapply tiles_order; eauto.
Qed.

Lemma WD_src_join sh (bs: list Z) a l p : 0 <= a -> 0 <= l -> a + l <= Zlength bs ->
  field_compatible (tarray tuchar (Zlength bs)) [] p ->
  (data_at sh (tarray tuchar a) (zbytes (sublist 0 a bs)) p *
   data_at sh (tarray tuchar l) (zbytes (sublist a (a + l) bs)) (offset_val a p) *
   data_at sh (tarray tuchar (Zlength bs - (a + l))) (zbytes (sublist (a + l) (Zlength bs) bs))
     (offset_val (a + l) p))%logic
  |-- data_at sh (tarray tuchar (Zlength bs)) (zbytes bs) p.
Proof. intros. rewrite (WD_src_split sh bs a l p) by auto. apply derives_refl. Qed.

Ltac WD_drop_vp :=
  match goal with |- context [andp (?D ?g ?d ?s) (valid_pointer ?d)] =>
    sep_apply (andp_left1 (D g d s) (valid_pointer d) (D g d s) (derives_refl _)) end.

Ltac WD_tc_null_test p :=
  apply denote_tc_test_eq_split; [|apply valid_pointer_null];
  destruct (eq_dec p nullval); [subst; apply valid_pointer_null|];
  rewrite ?(if_false (p = nullval)) by auto;
  match goal with |- context [malloc_token ?sh ?t p] =>
    destruct (zlt 0 (sizeof t));
    [ apply derives_trans with (data_at_ sh t p * TT)%logic; [cancel|];
      apply sepcon_valid_pointer1; apply data_at__valid_ptr; [auto | lia]
    | apply derives_trans with (malloc_token sh t p * TT)%logic; [cancel|];
      apply sepcon_valid_pointer1; apply malloc_token_valid_pointer; lia ]
  end.

Lemma WD_Znth_map_nth {A B} {IB: Inhabitant B} (g: A -> B) (l: list A) d k :
  0 <= k < Zlength l -> Znth k (map g l) = g (nth (Z.to_nat k) l d).
Proof.
  intros Hk. unfold Znth. rewrite if_false by lia.
  rewrite nth_indep with (d' := g d) by (rewrite map_length, <- ZtoNat_Zlength; lia).
  apply map_nth.
Qed.

(* a field of sr.f[k] after a load: Znth k of the frame table is winfo_val f (EF), whatever instance *)
Ltac WD_fix f :=
  repeat match goal with |- context [@Znth ?A ?I ?k ?l] =>
    replace (@Znth A I k l) with (winfo_val f : A) end;
  cbn [winfo_val].

(* the type-checking side goal of such a load *)
Ltac WD_fix_tc f :=
  WD_fix f; entailer!;
  repeat match goal with |- context [@Znth ?A ?I ?k ?l] =>
    replace (@Znth A I k l) with (winfo_val f : A) end;
  unfold winfo_val; simpl; unfold vb, vu, vl;
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; simpl; auto.

(* the bytes of sr after the corruption of frame f *)
Definition WD_corrupt (ws: wseries) (f: winfo) (s': list Z) : Prop :=
  (exists x, wi_checksum f = true /\ 0 < x < 2 ^ 32 /\
             s' = xorn (ws_bytes ws) (wi_start f + wi_size f - 4) x 4) \/
  s' = set_bit3 (ws_bytes ws) (wi_start f + 4).

(* ---------- API v3 at the default parameters (ApiBridge) ---------- *)

Lemma WD_res (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred) gv d st :
  dc_dict st = None -> dc_set st = nil ->
  DC gv d st |-- DC gv d st * dict_res DD gv Ews (dc_dict st) * set_res DD gv Ews (dc_set st) (dc_dict st).
Proof.
  intros Hd Hs. rewrite Hd, Hs. unfold dict_res. rewrite set_res_nil, !sepcon_emp. apply derives_refl.
Qed.

Lemma WD_res_drop (DD: globals -> val -> ddict_st -> mpred) gv st :
  dc_dict st = None -> dc_set st = nil ->
  dict_res DD gv Ews (dc_dict st) * set_res DD gv Ews (dc_set st) (dc_dict st) |-- emp.
Proof.
  intros Hd Hs. rewrite Hd, Hs. unfold dict_res. rewrite set_res_nil, sepcon_emp. apply derives_refl.
Qed.

Lemma WD_sdict_ok W st : dc_dict st = None -> dc_set st = nil -> dc_bl st = None -> stream_dict_ok W st.
Proof. intros Hd Hs Hb. unfold stream_dict_ok. rewrite Hd, Hs, Hb. auto. Qed.

(* ParamsW.params_w without a dictionary (hist = []), proved here: the strict and lenient models agree *)
Lemma WD_exec_seqs_w_nil wsize rep lits out seqs :
  exec_seqs_w wsize rep nil lits out seqs = exec_seqs wsize rep nil lits out seqs.
Proof.
  revert rep lits out. induction seqs as [|sq rest IH]; intros rep lits out; simpl; auto.
  destruct (sq_ll sq >? Zlength lits); auto.
  destruct (resolve_offset rep (sq_ll sq) (sq_ov sq)) as [[offset rep']|]; auto.
  rewrite Zlength_nil, !Z.add_0_l.
  destruct (offset >? Zlength (out ++ firstn (Z.to_nat (sq_ll sq)) lits)) eqn:E1; auto.
  cbn [andb negb]. rewrite andb_true_r, Z.add_0_r.
  destruct (offset >? wsize); auto.
Qed.

Lemma WD_decode_block_w_nil st out b bsm wsize :
  decode_block_w st nil out b bsm wsize = decode_block st nil out b bsm wsize.
Proof.
  unfold decode_block_w, decode_block.
  destruct (Zlength b >? bsm); auto.
  destruct (decode_literals (st_huf st) b bsm) as [[[lits lused] huf]|]; auto.
  destruct (decode_seq_header (st_seq st) (skipn (Z.to_nat lused) b)) as [[[nbSeq tabs] hused]|]; auto.
  match goal with |- match ?x with _ => _ end = _ => destruct x as [seqs|] end; auto.
  rewrite WD_exec_seqs_w_nil. reflexivity.
Qed.

Lemma WD_decode_blocks_w_nil fuel st s out bsm wsize :
  decode_blocks_w fuel st nil s out bsm wsize = decode_blocks fuel st nil s out bsm wsize.
Proof.
  revert st s out. induction fuel as [|f IH]; intros st s out; simpl; auto.
  destruct (cblock_size s) as [c|]; auto.
  rewrite WD_decode_block_w_nil.
  destruct (c >? Zlength s - ZSTD_blockHeaderSize); auto.
  match goal with |- match ?r with _ => _ end = match ?r with _ => _ end => destruct r as [[st' out']|] end; auto.
  rewrite IH. reflexivity.
Qed.

Lemma WD_decode_frame_m_w_nodict md wl s :
  decode_frame_m (dmode_w md) no_dict wl s = decode_frame_m md no_dict wl s.
Proof.
  unfold decode_frame_m. cbn [md_magicless md_ignore md_bmax md_dwin dmode_w].
  destruct (md_dwin md); [reflexivity|].
  change (dm_content no_dict) with (@nil Z).
  destruct (get_frame_header_m (md_magicless md) s); try reflexivity.
  rewrite WD_decode_blocks_w_nil. reflexivity.
Qed.

Lemma WD_frame_dict_nodict mg s : frame_dict mg sel_none (Some no_dict) s = Some no_dict.
Proof. unfold frame_dict. destruct (get_frame_header_m mg s); reflexivity. Qed.

Lemma WD_walk_m_w_nodict fuel md wl s off :
  walk_m fuel (dmode_w md) sel_none (Some no_dict) wl s off = walk_m fuel md sel_none (Some no_dict) wl s off.
Proof.
  revert s off. induction fuel as [|f IH]; intros s off; simpl; auto.
  rewrite !WD_frame_dict_nodict, WD_decode_frame_m_w_nodict.
  destruct (md_dwin md);
  destruct (skippable_frame_size s) as [k|]; destruct (decode_frame_m md no_dict wl s) as [c k'| | |];
    rewrite ?IH; reflexivity.
Qed.

Lemma WD_series_frames_m_w_nodict md wl s :
  series_frames_m (dmode_w md) sel_none (Some no_dict) wl s = series_frames_m md sel_none (Some no_dict) wl s.
Proof. apply WD_walk_m_w_nodict. Qed.

Lemma WD_stream_claims_v3_dflt (st: dctx_st) (sin0 sout0 sin sall sout: list Z) (a1: Z) (ocap: option Z) (r: Z) :
  dc_par st = dparams_dflt -> dc_set st = nil -> dc_dict st = None ->
  stream_claims_m (dmode_w (dmode_of (dc_par st))) (fst (st_sel st)) (snd (st_sel st)) (dp_wmax (dc_par st))
     sin0 sout0 sin sall sout a1 ocap r -> stream_claims sin0 sout0 sin sall sout a1 ocap r.
Proof.
  intros Hp Hs Hd. rewrite (st_sel_nil st Hs), Hd, Hp, dmode_of_dflt. simpl fst. simpl snd.
  change (dp_wmax dparams_dflt) with stream_wlim.
  rewrite <- stream_claims_m_dflt. unfold stream_claims_m.
  intros H s0 Hb Hpre; specialize (H s0 Hb Hpre);
  rewrite ?WD_series_frames_m_w_nodict in *; exact H.
Qed.

Lemma WD_claims st sin0 sout0 sin sall sout a1 ocap r :
  dc_par st = dparams_dflt -> dc_set st = nil -> dc_dict st = None ->
  stream_claims_m (dmode_w (dmode_of (dc_par st))) (fst (st_sel st)) (snd (st_sel st)) (dp_wmax (dc_par st))
    sin0 sout0 sin sall sout a1 ocap r ->
  stream_claims sin0 sout0 sin sall sout a1 ocap r.
Proof. apply WD_stream_claims_v3_dflt. Qed.

Theorem main_ok3_detect : MainOK.
Proof.
intros DC DD WG WDS HWG.
unfold G0. rewrite WD_Externals.
unfold main_spec, QPmain_spec_ext', NDmk_funspec.
split3; [reflexivity | reflexivity |].
intros Espec DTL gv.
simpl fn_body; simpl fn_params; simpl fn_return.
change (map fst []) with (@nil ident).
eapply (main_pre_InitGpred
          (sepcon (zstd_globals gv) (sepcon (WG gv) (sepcon (data_at Ews t_wseries (zero_val t_wseries) (gv _x_detect__sr)) TT)))
          _ _ _ Zstd.contracts.x_detect.whole_prog).
4: idtac.
- intros. apply WD_pre; auto.
- reflexivity.
- apply Forall_forall; intros [i g] Hin; simpl fst.
  apply WD_tyc_g_isSome. unfold Vprog, QPvarspecs. rewrite map_map.
  apply in_map_iff. exists (i, g); auto.
- process_stackframe_of.
  repeat rewrite <- data_at__offset_zero.
  try simple apply start_function_aux1.
  match goal with |- semax ?D ?P ?c (frame_ret_assert (function_body_ret_assert ?t _) ?F) =>
    apply (semax_post (frame_ret_assert (function_body_ret_assert t (PROP () LOCAL () (SEP (TT)))) F))
  end.
  1,2,3: intros; simpl; normalize.
  1: intros [v|]; simpl; unfold bind_ret; simpl; normalize;
       intros x; apply andp_left2; apply sepcon_derives; [unfold_lift; apply TT_right | auto].
  abbreviate_semax.
  sep_apply (create_mem_mgr gv).
  forward_call 2.
  Intros kind.
  forward_call (gv, Ews, gv _x_detect__sr, nullval, @None (wdict * share)).
  { unfold wdict_arg. entailer!. }
  Intros ws.
  unfold wdict_arg, wdict_model in *.
  Intros.
  rewrite WD_sr_split.
  unfold wseries_val. cbn [fst snd].
  Intros. forward.
  assert (Hnf: 1 <= Zlength (ws_frames ws) <= 4) by (destruct H0 as (_&_&_&_&Hn&_); rewrite Zlength_correct; lia).
  forward_call (Zlength (ws_frames ws)).
  Intros k. forward.
  assert (Hk: (Z.to_nat k < length (ws_frames ws))%nat) by (rewrite Zlength_correct in *; lia).
  pose proof (DM_frame_bounds _ _ _ H0 Hk) as (Hst & Hsz & Hend & H9).
  set (f := nth (Z.to_nat k) (ws_frames ws) winfo0) in *.
  assert (EF: Znth k (map winfo_val (ws_frames ws) ++ Zrepeat (winfo_val winfo0) (4 - Zlength (ws_frames ws)))
              = winfo_val f).
  { rewrite app_Znth1 by (rewrite Zlength_map; lia). apply WD_Znth_map_nth; lia. }
  forward.
  { WD_fix_tc f. }
  WD_fix f.
  forward_call (if wi_skippable f then Int.zero else Int.one).
  { unfold vb. entailer!. destruct (wi_skippable f); reflexivity. }
  assert (Hns: wi_skippable f = false) by (destruct (wi_skippable f); auto; contradiction).
  specialize (H9 Hns).
  match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
    let Q := eval cbv [replace_nth] in (fun s': list Z => replace_nth 1 R
      (field_at Ews t_wseries (DOT _bytes)
         (zbytes s' ++ Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength (ws_bytes ws))) (gv _x_detect__sr))) in
    let Post := eval cbv beta in (EX s': list Z,
      PROP (WD_corrupt ws f s')
      LOCAL (temp _k (Vint (Int.repr k)); lvar _out tout v_out; lvar _in tin v_in; gvars gv)
      (SEPx (Q s'))) in
    forward_if Post
  end.
  { forward_call Int.max_unsigned.
    { entailer!. simpl. do 2 f_equal. apply Int.eqm_samerepr. exists (-1). reflexivity. }
    Intros r.
    forward.
    forward.
    { WD_fix_tc f. }
    WD_fix f.
    forward_call (Int.repr (if wi_checksum f then 1 else 0)).
    assert (Hck: wi_checksum f = true) by (destruct (wi_checksum f); auto; contradiction).
    rewrite add_repr.
    set (pos := wi_start f + wi_size f - 4).
    match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
      let Q := eval cbv [replace_nth] in (fun j: Z => replace_nth 1 R
        (field_at Ews t_wseries (DOT _bytes)
           (zbytes (xorn (ws_bytes ws) pos (1 + r) j) ++ Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength (ws_bytes ws)))
           (gv _x_detect__sr))) in
      let Inv := eval cbv beta in (EX j: Z,
        PROP ()
        LOCAL (temp _x (Vint (Int.repr (1 + r))); temp _k (Vint (Int.repr k));
               lvar _out tout v_out; lvar _in tin v_in; gvars gv)
        (SEPx (Q j))) in
      forward_for_simple_bound 4 Inv
    end.
    { entailer!. rewrite xorn_0. cancel. }
    { forward. { WD_fix_tc f. } WD_fix f.
      forward. { WD_fix_tc f. } WD_fix f.
      forward. { WD_fix_tc f. } WD_fix f.
      forward. { WD_fix_tc f. } WD_fix f.
      unfold vl.
      assert (HB: Zlength (ws_bytes ws) <= 2 ^ 19) by (destruct H0 as (_&_&HBn&_); exact HBn).
      assert (HBb: bytes_ok (ws_bytes ws)) by (destruct H0 as (HBb&_); exact HBb).
      remember (zbytes (xorn (ws_bytes ws) pos (1 + r) i) ++
                Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength (ws_bytes ws))) as VB eqn:EVB.
      assert (HVB: Zlength VB = 524288)
        by (subst VB; rewrite Zlength_app, Zlength_map, xorn_Zlength, Zlength_Zrepeat by lia; lia).
      rewrite (WD_bytes_split Ews VB (pos + i) (gv _x_detect__sr)) by (unfold pos; lia).
      Intros.
      assert (EZ: Znth (pos + i) VB = Vint (Int.repr (Znth (pos + i) (ws_bytes ws)))).
      { subst VB. rewrite app_Znth1 by (rewrite Zlength_map, xorn_Zlength; unfold pos; lia).
        rewrite Znth_map by (rewrite xorn_Zlength; unfold pos; lia).
        rewrite xorn_Znth_out by (unfold pos; lia). reflexivity. }
      assert (Hb: 0 <= Znth (pos + i) (ws_bytes ws) <= Byte.max_unsigned).
      { pose proof (proj1 (Forall_Znth _ _) HBb (pos + i)) as Hx. unfold is_byte in Hx.
        assert (0 <= pos + i < Zlength (ws_bytes ws)) by (unfold pos; lia). specialize (Hx H8). rep_lia. }
      forward.
      { rewrite EZ. entailer!. rep_lia. }
      rewrite EZ.
      forward.
      { entailer!. change (Int.unsigned Int.iwordsize) with 32. lia. }
      rewrite WD_xor_byte by rep_lia.
      sep_apply (WD_bytes_join Ews VB (pos + i)
        (Vint (Int.repr (Z.lxor (Znth (pos + i) (ws_bytes ws)) (Z.land (Z.shiftr (1 + r) (8 * i)) 255))))
        (gv _x_detect__sr) ltac:(unfold pos; lia) HVB).
      match goal with |- context [upd_Znth (pos + i) VB ?v] =>
        replace (upd_Znth (pos + i) VB v) with
          (zbytes (xorn (ws_bytes ws) pos (1 + r) (i + 1)) ++
           Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength (ws_bytes ws))) end.
      2: { subst VB. rewrite upd_Znth_app1 by (rewrite Zlength_map, xorn_Zlength; unfold pos; lia).
           rewrite (xorn_step _ _ _ i) by (unfold pos; lia).
           rewrite <- upd_Znth_map. reflexivity. }
      unfold vl. entailer!. }
    Exists (xorn (ws_bytes ws) pos (1 + r) 4). entailer!.
    left. exists (1 + r). split; [exact Hck | split; [rep_lia | reflexivity]]. }
  { forward. { WD_fix_tc f. } WD_fix f.
    forward. { WD_fix_tc f. } WD_fix f.
    assert (HB: Zlength (ws_bytes ws) <= 2 ^ 19) by (destruct H0 as (_&_&HBn&_); exact HBn).
    assert (HBb: bytes_ok (ws_bytes ws)) by (destruct H0 as (HBb&_); exact HBb).
    remember (zbytes (ws_bytes ws) ++ Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength (ws_bytes ws))) as VB eqn:EVB.
    assert (HVB: Zlength VB = 524288)
      by (subst VB; rewrite Zlength_app, Zlength_map, Zlength_Zrepeat by lia; lia).
    rewrite (WD_bytes_split Ews VB (wi_start f + 4) (gv _x_detect__sr)) by lia.
    Intros.
    assert (EZ: Znth (wi_start f + 4) VB = Vint (Int.repr (Znth (wi_start f + 4) (ws_bytes ws)))).
    { subst VB. rewrite app_Znth1 by (rewrite Zlength_map; lia).
      rewrite Znth_map by lia. reflexivity. }
    assert (Hb: 0 <= Znth (wi_start f + 4) (ws_bytes ws) <= Byte.max_unsigned).
    { pose proof (proj1 (Forall_Znth _ _) HBb (wi_start f + 4)) as Hx. unfold is_byte in Hx.
      assert (0 <= wi_start f + 4 < Zlength (ws_bytes ws)) by lia. specialize (Hx H5). rep_lia. }
    forward.
    { rewrite EZ. entailer!. rep_lia. }
    rewrite EZ.
    forward.
    rewrite WD_or_byte by rep_lia.
    sep_apply (WD_bytes_join Ews VB (wi_start f + 4)
      (Vint (Int.repr (Z.lor (Znth (wi_start f + 4) (ws_bytes ws)) 8)))
      (gv _x_detect__sr) ltac:(lia) HVB).
    Exists (set_bit3 (ws_bytes ws) (wi_start f + 4)).
    match goal with |- context [upd_Znth (wi_start f + 4) VB ?v] =>
      replace (upd_Znth (wi_start f + 4) VB v) with
        (zbytes (set_bit3 (ws_bytes ws) (wi_start f + 4)) ++
         Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength (ws_bytes ws))) end.
    2: { subst VB. rewrite upd_Znth_app1 by (rewrite Zlength_map; lia).
         rewrite set_bit3_upd by lia.
         rewrite <- upd_Znth_map. reflexivity. }
    unfold vl. entailer!. right. reflexivity. }
  Intros s'.
  match goal with H: WD_corrupt _ _ _ |- _ => rename H into Hcor end.
  assert (Hlen: Zlength s' = Zlength (ws_bytes ws) /\ bytes_ok s').
  { assert (HBb: bytes_ok (ws_bytes ws)) by (destruct H0 as (HBb&_); exact HBb).
    destruct Hcor as [(x & _ & Hx & ->) | ->].
    - split; [apply xorn_Zlength | apply xorn_bytes; auto; lia].
    - split; [apply set_bit3_Zlength | apply set_bit3_bytes; auto]. }
  destruct Hlen as [Hlen Hs'b].
  destruct (DM_detect ws (Z.to_nat k) s' H0 H1 Hk Hns Hcor) as (Hdec & _ & _).
  destruct (WD_detect_frames ws (Z.to_nat k) s' no_wlim H0 H1 Hk Hns Hcor) as (Htl & Hfr).
  assert (HB: Zlength (ws_bytes ws) <= 2 ^ 19) by (destruct H0 as (_&_&HBn&_); exact HBn).
  assert (HC: Zlength (ws_content ws) <= 2 ^ 18) by (destruct H0 as (_&_&_&HCn&_); exact HCn).
  forward. { WD_fix_tc f. } WD_fix f.
  forward. { WD_fix_tc f. } WD_fix f.
  forward.
  forward.
  rewrite <- Hlen.
  sep_apply (WD_bytes_prefix Ews s' (gv _x_detect__sr) ltac:(lia)).
  forward_call (gv, Ews, field_address t_wseries (DOT _bytes) (gv _x_detect__sr), s').
  { entailer!. unfold field_address in *.
    destruct (field_compatible_dec t_wseries (DOT _bytes) (gv _x_detect__sr)) as [Hfc|Hfc]; [| destruct H4; contradiction].
    reflexivity. }
  { cancel. }
  Intros src.
  assert (Hn9: 9 <= Zlength s') by lia.
  rewrite Z.max_r by lia. rewrite Z.sub_diag. change (Zrepeat Vundef 0) with (@nil val). rewrite app_nil_r.
  forward.
  destruct (eq_dec src nullval) as [Hsrc|Hsrc].
  { subst src. forward_if; [forward; entailer! | exfalso; auto]. }
  Intros.
  forward_if; [contradiction|].
  freeze [1; 4; 5; 7; 9; 10; 11; 15] FR.
  forward_call 2.
  Intros c.
  match goal with |- semax _ ?P _ _ => forward_if P end.
  { forward.
    forward_call (0, Zlength (ws_content ws) + 16).
    Intros cap. forward.
    match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp _x_detect__t'6 (Vlong (Int64.repr (Z.max 1 cap))) :: L) (SEPx R))) end.
    { forward. entailer!.
      repeat match goal with H: context [Int64.unsigned (Int64.repr _)] |- _ => rewrite !Int64.unsigned_repr in H by rep_lia end.
      rewrite Z.max_r by lia. reflexivity. }
    { forward. entailer!.
      repeat match goal with H: context [Int64.unsigned (Int64.repr _)] |- _ => rewrite !Int64.unsigned_repr in H by rep_lia end.
      replace cap with 0 by lia. reflexivity. }
    forward_call (tarray tuchar (Z.max 1 cap), gv).
    { simpl. rewrite Z.max_r by lia. rep_lia. }
    Intros dst. forward.
    destruct (eq_dec dst nullval) as [Hdst|Hdst].
    { subst dst. forward_if; [discriminate | forward; entailer!]. }
    Intros.
    forward_if; [| contradiction].
    {
      forward.
      assert (Hm: (0 < cap /\ Z.max 1 cap = cap) \/ (cap = 0 /\ Z.max 1 cap = 1)) by lia.
      rewrite <- WD_arr_.
      sep_apply (WD_dst_split cap (Z.max 1 cap) dst Hm).
      Intros.
      rewrite <- WD_arr.
      forward_call (WD_W cap dst, gv, Ews, dst, cap, Ews, src, s').
      { unfold mbuf; rewrite if_false by auto. cancel. }
      { apply WD_buf_ok_pos; lia. }
      Intros vr. destruct vr as [r out]. cbn [fst snd] in *.
      unfold mbuf; rewrite if_false by auto.
      match goal with H: oneshot_ok _ _ _ _ _ _ |- _ => apply oneshot_ok_dflt in H; destruct H as [_ Hok] end.
      rewrite Hdec in Hok.
      forward.
      forward_call r.
      rewrite Hok.
      forward_call (Int.repr 1).
      sep_apply (WD_ib_join dst cap (Z.max 1 cap) out Hm).
      rewrite WD_arr_. rewrite WD_arr.
      forward_call (tarray tuchar (Z.max 1 cap), dst, gv).
      { rewrite if_false by auto. cancel. }
      entailer!. } }
  { match goal with |- semax _ (PROPx _ (LOCALx ?L0 (SEPx ?R0))) _ _ =>
      forward_call gv;
      Intros ds;
      forward; forward;
      destruct (eq_dec ds nullval) as [Hds|Hds];
      [ subst ds;
        forward_loop (PROPx [] (LOCALx (temp _ds nullval :: L0) (SEPx (emp :: R0))))
          break: (PROPx [] (LOCALx (temp _ds nullval :: L0) (SEPx (emp :: R0))))
      | idtac ]
    end.
    { entailer!. }
    { match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
        forward_if (PROPx P (LOCALx (temp _x_detect__t'11 (Vint Int.zero) :: L) (SEPx R))) end;
        [discriminate | forward; entailer! |].
      forward_if; [lia | forward; entailer!]. }
    { forward_call (gv, nullval, @None dctx_st). entailer!. }
    assert_PROP (field_compatible (tarray tuchar (Zlength s')) [] src) as Hfcs by entailer!.
    set (E := wi_start f + wi_size f).
    forward_loop
      (EX calls: Z, EX ipos: Z, EX st: dctx_st,
       PROP (0 <= calls <= 4096; 0 <= ipos <= Zlength s'; dc_dict st = None; dc_stable st = false; dc_par st = dparams_dflt; dc_set st = nil; dc_bl st = None; dc_mem st = None;
             ss_err (dc_ss st) = false; 0 <= ss_ahead (dc_ss st) <= 1; ipos + ss_ahead (dc_ss st) <= Zlength s';
             ss_in (dc_ss st) = sublist 0 (ipos + ss_ahead (dc_ss st)) s')
       LOCAL (temp _calls (Vlong (Int64.repr calls)); temp _ipos (Vlong (Int64.repr ipos)); temp _ds ds;
              temp _x_detect__t'19 (Vint (Int.repr c)); temp _src src; temp _x_detect__t'4 src;
              temp _x_detect__t'25 (vl (Zlength s'));
              temp _end (Vlong (Int64.add (Int64.repr (wi_start f)) (Int64.repr (wi_size f))));
              temp _x_detect__t'27 (vl (wi_size f)); temp _x_detect__t'26 (vl (wi_start f));
              temp _k (Vint (Int.repr k)); lvar _out tout v_out; lvar _in tin v_in; gvars gv)
       SEP (mem_mgr gv; zstd_globals gv; (DC gv ds st && valid_pointer ds); FRZL FR;
            malloc_token Ews (tarray tuchar (Zlength s')) src;
            data_at Ews (tarray tuchar (Zlength s')) (zbytes s') src;
            field_at Ews t_wseries (DOT _n) (vl (Zlength s')) (gv _x_detect__sr);
            field_at Ews t_wseries (DOT _content_n) (vl (Zlength (ws_content ws))) (gv _x_detect__sr);
            data_at_ Tsh tout v_out; data_at_ Tsh tin v_in; has_ext tt))%assert
    continue:
      (EX calls: Z, EX ipos: Z, EX st: dctx_st,
       PROP (0 <= calls < 4096; 0 <= ipos <= Zlength s'; dc_dict st = None; dc_stable st = false; dc_par st = dparams_dflt; dc_set st = nil; dc_bl st = None; dc_mem st = None;
             ss_err (dc_ss st) = false; 0 <= ss_ahead (dc_ss st) <= 1; ipos + ss_ahead (dc_ss st) <= Zlength s';
             ss_in (dc_ss st) = sublist 0 (ipos + ss_ahead (dc_ss st)) s')
       LOCAL (temp _calls (Vlong (Int64.repr calls)); temp _ipos (Vlong (Int64.repr ipos)); temp _ds ds;
              temp _x_detect__t'19 (Vint (Int.repr c)); temp _src src; temp _x_detect__t'4 src;
              temp _x_detect__t'25 (vl (Zlength s'));
              temp _end (Vlong (Int64.add (Int64.repr (wi_start f)) (Int64.repr (wi_size f))));
              temp _x_detect__t'27 (vl (wi_size f)); temp _x_detect__t'26 (vl (wi_start f));
              temp _k (Vint (Int.repr k)); lvar _out tout v_out; lvar _in tin v_in; gvars gv)
       SEP (mem_mgr gv; zstd_globals gv; (DC gv ds st && valid_pointer ds); FRZL FR;
            malloc_token Ews (tarray tuchar (Zlength s')) src;
            data_at Ews (tarray tuchar (Zlength s')) (zbytes s') src;
            field_at Ews t_wseries (DOT _n) (vl (Zlength s')) (gv _x_detect__sr);
            field_at Ews t_wseries (DOT _content_n) (vl (Zlength (ws_content ws))) (gv _x_detect__sr);
            data_at_ Tsh tout v_out; data_at_ Tsh tin v_in; has_ext tt))%assert
    break:
      (EX st: dctx_st,
       PROP (dc_mem st = None)
       LOCAL (temp _ds ds;
              temp _x_detect__t'19 (Vint (Int.repr c)); temp _src src; temp _x_detect__t'4 src;
              temp _x_detect__t'25 (vl (Zlength s'));
              temp _end (Vlong (Int64.add (Int64.repr (wi_start f)) (Int64.repr (wi_size f))));
              temp _x_detect__t'27 (vl (wi_size f)); temp _x_detect__t'26 (vl (wi_start f));
              temp _k (Vint (Int.repr k)); lvar _out tout v_out; lvar _in tin v_in; gvars gv)
       SEP (mem_mgr gv; zstd_globals gv; DC gv ds st; FRZL FR;
            malloc_token Ews (tarray tuchar (Zlength s')) src;
            data_at Ews (tarray tuchar (Zlength s')) (zbytes s') src;
            field_at Ews t_wseries (DOT _n) (vl (Zlength s')) (gv _x_detect__sr);
            field_at Ews t_wseries (DOT _content_n) (vl (Zlength (ws_content ws))) (gv _x_detect__sr);
            data_at_ Tsh tout v_out; data_at_ Tsh tin v_in; has_ext tt))%assert.
    { entailer!. Exists 0 0 dctx_init. entailer!. simpl. lia. }
    2: { Intros calls ipos st. forward. Exists (calls + 1) ipos st. entailer!. }
    2: { Intros st. forward_call (gv, ds, Some st).
         match goal with H: dc_mem st = None |- _ => unfold cm_back; rewrite H end. entailer!. }
    Intros calls ipos st.
    match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp _x_detect__t'11 (Vint (if calls <? 4096 then Int.one else Int.zero)) :: L) (SEPx R))) end.
    { forward. entailer!. rewrite WD_ltu_Z by rep_lia. destruct (calls <? 4096); reflexivity. }
    { contradiction. }
    forward_if.
    2: { forward. WD_drop_vp. Exists st. entailer!. }
    assert (Hc4: calls < 4096) by (destruct (calls <? 4096) eqn:Ec; [apply Z.ltb_lt in Ec; lia | contradiction]).
    forward.
    forward_call (0, Zlength s' - ipos).
    Intros ilen. forward.
    forward.
    forward_call (1, Zlength (ws_content ws) + 1).
    Intros olen. forward.
    rewrite (WD_src_split Ews s' ipos ilen src) by (auto; lia).
    Intros.
    set (bs1 := sublist ipos (ipos + ilen) s').
    assert (Hl1: Zlength bs1 = ilen) by (unfold bs1; rewrite Zlength_sublist by lia; lia).
    rewrite <- Hl1.
    forward_call (gv, Ews, offset_val ipos src, bs1).
    { unfold bs1. apply Forall_sublist. exact Hs'b. }
    Intros ib. rewrite Hl1.
    forward_call (tarray tuchar olen, gv).
    { simpl. rewrite Z.max_r by lia. rep_lia. }
    Intros ob.
    assert (Ebs1: bs1 = sublist ipos (ipos + ilen) s') by reflexivity. clearbody bs1.
    match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp _x_detect__t'16 (Vint (Int.repr
          (if eq_dec ib nullval then 1 else if eq_dec ob nullval then 1 else 0))) :: L) (SEPx R)))
    end.
    { WD_tc_null_test ib. }
    { forward. destruct (eq_dec ib nullval); [|contradiction]. entailer!. }
    { forward.
      { entailer!; WD_tc_null_test ob. }
      destruct (eq_dec ib nullval); [contradiction|].
      destruct (eq_dec ob nullval); entailer!;
        try reflexivity; destruct ob; try contradiction; reflexivity. }
    match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
      forward_if (PROPx ((ib <> nullval) :: (ob <> nullval) :: P) (LOCALx L (SEPx R)))
    end.
    { destruct (eq_dec ib nullval) as [Hib|Hib]; Intros.
      - subst ib. forward_call (tarray tuchar (Z.max 1 ilen), nullval, gv).
        { destruct (eq_dec nullval nullval); [|congruence]. cancel. }
        forward_call (tarray tuchar olen, ob, gv).
        subst bs1.
        sep_apply (WD_src_join Ews s' ipos ilen src ltac:(lia) ltac:(lia) ltac:(lia) Hfcs).
        forward. WD_drop_vp. Exists st. entailer!.
      - sep_apply (data_at_data_at_ Ews (tarray tuchar (Z.max 1 ilen))
          (zbytes bs1 ++ Zrepeat Vundef (Z.max 1 ilen - ilen)) ib).
        forward_call (tarray tuchar (Z.max 1 ilen), ib, gv).
        { destruct (eq_dec ib nullval); [contradiction|]. cancel. }
        forward_call (tarray tuchar olen, ob, gv).
        subst bs1.
        sep_apply (WD_src_join Ews s' ipos ilen src ltac:(lia) ltac:(lia) ltac:(lia) Hfcs).
        forward. WD_drop_vp. Exists st. entailer!. }
    { forward. entailer!.
      match goal with H: Int.repr _ = Int.zero |- _ => rename H into Ht16 end.
      destruct (EqDec_val ib nullval); [inv Ht16|]. destruct (EqDec_val ob nullval); [inv Ht16|]. auto. }
    Intros.
    rewrite !if_false by auto. Intros.
    do 6 forward.
    assert (Hm: (0 < ilen /\ Z.max 1 ilen = ilen) \/ (ilen = 0 /\ Z.max 1 ilen = 1)) by lia.
    rewrite <- !WD_arr.
    sep_apply (WD_ib_split ib ilen (Z.max 1 ilen) (zbytes bs1) ltac:(rewrite Zlength_map; lia) Hm).
    Intros.
    rewrite <- WD_arr_.
    change (@data_at_ ZCS Ews (tarray tuchar olen) ob) with (@data_at ZCS Ews (tarray tuchar olen) (Zrepeat Vundef olen) ob).
    change (Int.signed (Int.repr 0)) with 0.
    rewrite <- WD_in, <- WD_out.
    WD_drop_vp.
    match goal with H: dc_dict st = None |- _ => rename H into Hstd end.
    match goal with H: dc_set st = nil |- _ => rename H into Hsts end.
    match goal with H: dc_bl st = None |- _ => rename H into Hstb end.
    match goal with H: dc_par st = dparams_dflt |- _ => rename H into Hstp end.
    match goal with H: dc_mem st = None |- _ => rename H into Hstm end.
    sep_apply (WD_res DC DD gv ds st Hstd Hsts).
    do 2 try flatten_sepcon_in_SEP.
    forward_call (WD_W ilen ib, gv, ds, st, v_out, v_in, Tsh, Tsh, Ews, ob, olen, 0, Zrepeat Vundef olen, Ews, ib, ilen, 0, bs1).
    { unfold mbuf; rewrite !if_false by auto. cancel. }
    { split; [apply WD_buf_ok_pos; lia|]. split; [apply WD_sdict_ok; auto|]. split; [apply Zlength_Zrepeat; lia|].
      rewrite Ebs1. apply Forall_sublist. exact Hs'b. }
    Intros vr. destruct vr as [[[[r opos'] ip'] oc'] st']. cbn [fst snd] in *.
    unfold mbuf; rewrite !if_false by auto.
    match goal with H: stream_post _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      destruct H as (dl & stall' & a' & Hop & Hip & Hoc & _ & _ & _ & Ha' & Hge & Hor & Hra & Hst' & _ & _ & _ & _ & Hcl & _) end.
    apply (WD_claims st) in Hcl; auto.
    assert (Hstm': dc_mem st' = None) by (rewrite Hst'; cbn; rewrite Hstm; reflexivity).
    sep_apply (WD_res_drop DD gv st Hstd Hsts).
    rewrite WD_in, WD_out.
    forward. forward.
    sep_apply (WD_ib_join ib ilen (Z.max 1 ilen) (zbytes bs1) Hm). rewrite WD_arr_.
    forward_call (tarray tuchar (Z.max 1 ilen), ib, gv).
    { rewrite if_false by auto. cancel. }
    rewrite !WD_arr.
    sep_apply (data_at_data_at_ Ews (tarray tuchar olen) oc' ob).
    forward_call (tarray tuchar olen, ob, gv).
    { rewrite if_false by auto. cancel. }
    subst bs1.
    sep_apply (WD_src_join Ews s' ipos ilen src ltac:(lia) ltac:(lia) ltac:(lia) Hfcs).
    forward_call r.
    forward_if.
    { forward. WD_drop_vp. Exists st'.
      sep_apply (data_at_data_at_ Tsh tout (ob, (Vlong (Int64.repr olen), Vlong (Int64.repr opos'))) v_out).
      sep_apply (data_at_data_at_ Tsh tin (ib, (Vlong (Int64.repr ilen), Vlong (Int64.repr ip'))) v_in).
      entailer!. }
    assert (Herr: is_error_code r = false).
    { match goal with H: Int.repr (if is_error_code r then 1 else 0) = Int.zero |- _ => revert H end.
      destruct (is_error_code r); [intro X; inv X | auto]. }
    assert (Hsin: ss_in (dc_ss st) ++ sublist (0 + ss_ahead (dc_ss st)) (ip' + a') (sublist ipos (ipos + ilen) s')
                  = sublist 0 (ipos + (ip' + a')) s')
      by (match goal with H: ss_in (dc_ss st) = _ |- _ => rewrite H end; apply WD_sin2; lia).
    rewrite !add64_repr.
    sep_apply (data_at_data_at_ Tsh tout (ob, (Vlong (Int64.repr olen), Vlong (Int64.repr opos'))) v_out).
    sep_apply (data_at_data_at_ Tsh tin (ib, (Vlong (Int64.repr ilen), Vlong (Int64.repr ip'))) v_in).
    forward_if.
    { assert (Hr0: r = 0).
      { match goal with H: Int64.repr r = _ |- _ =>
          apply (f_equal Int64.unsigned) in H; rewrite Int64.unsigned_repr in H by rep_lia; exact H end. }
      subst r. assert (a' = 0) by exact (stream_hostage_zero a' 0 Hra Ha' eq_refl). subst a'.
      assert (Hlt: ipos + ip' < E).
      { assert (Hz := WD_zero_le _ _ _ _ s' (wi_start f) Hcl Hs'b
          ltac:(rewrite Hsin; apply WD_prefix; lia) Htl Hfr).
        rewrite Hsin, Zlength_sublist in Hz by lia. unfold E; lia. }
      forward_call Int.one.
      { entailer!. rewrite WD_ltu_Z by (unfold E in *; rep_lia).
        unfold E in Hlt. rewrite (proj2 (Z.ltb_lt _ _) Hlt). reflexivity. }
      Exists calls (ipos + ip') st'. entailer!. rewrite ?Z.add_0_l, ?Z.add_0_r in Hsin. simpl. rewrite Hsin.
      split; [lia|reflexivity]. }
    { forward. Exists calls (ipos + ip') st'. entailer!. rewrite ?Z.add_0_l in Hsin. simpl. rewrite Hsin.
      split; [lia | f_equal; lia]. } }
  forward_call (tarray tuchar (Zlength s'), src, gv).
  { rewrite if_false by auto. sep_apply (data_at_data_at_ Ews (tarray tuchar (Zlength s')) (zbytes s') src). cancel. }
  forward.
  cancel.
Qed.
