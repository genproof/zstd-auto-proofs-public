(* vd_stream (harness/valid_dict_api.c): small VST and list facts for its proof (from valid_stream's v2 main,
   WMain_valid_stream.v), at the compspecs of valid_dict_api. *)
Require Import VST.floyd.proofauto.
Require Export Zstd.proof.harness.valid_dict_api.VDSModel.
Require Export Zstd.proof.harness.valid_dict_api.VDSMem.

Local Notation ZCS := Zstd.proof.zstd.Base.CompSpecs.
Local Notation HCS := Zstd.proof.harness.valid_dict_api.HOK_valid_dict_api.CompSpecs.
Local Notation tout := (Tstruct _ZSTD_outBuffer_s noattr).
Local Notation tin := (Tstruct _ZSTD_inBuffer_s noattr).

Definition VD_cce (cs1 cs2: compspecs) : change_composite_env cs1 cs2 :=
  {| coeq := cs_preserve_env cs1 cs2;
     coeq_consistent := cs_preserve_env_consistent cs1 cs2 _ eq_refl;
     coeq_complete := cs_preserve_completeness cs1 cs2 _ eq_refl |}.

Lemma VD_arr: forall sh n (v: list val) p,
  @data_at ZCS sh (tarray tuchar n) v p = @data_at HCS sh (tarray tuchar n) v p.
Proof.
  intros. pose proof (@data_at_change_composite ZCS HCS (VD_cce ZCS HCS) sh (tarray tuchar n) v v
    (JMeq_refl _) ltac:(reflexivity)) as E. rewrite E; reflexivity.
Qed.

Lemma VD_arr_: forall sh n p,
  @data_at_ ZCS sh (tarray tuchar n) p = @data_at_ HCS sh (tarray tuchar n) p.
Proof.
  intros. pose proof (@data_at__change_composite ZCS HCS (VD_cce ZCS HCS) sh (tarray tuchar n)
    ltac:(reflexivity)) as E. rewrite E; reflexivity.
Qed.

Lemma VD_out: forall sh (a b c: val) p,
  @data_at ZCS sh t_outBuffer (a, (b, c)) p = @data_at HCS sh tout (a, (b, c)) p.
Proof.
  intros. pose proof (@data_at_change_composite ZCS HCS (VD_cce ZCS HCS) sh tout (a, (b, c)) (a, (b, c))
    (JMeq_refl _) ltac:(vm_compute; reflexivity)) as E. exact (f_equal (fun f => f p) E).
Qed.

Lemma VD_in: forall sh (a b c: val) p,
  @data_at ZCS sh t_inBuffer (a, (b, c)) p = @data_at HCS sh tin (a, (b, c)) p.
Proof.
  intros. pose proof (@data_at_change_composite ZCS HCS (VD_cce ZCS HCS) sh tin (a, (b, c)) (a, (b, c))
    (JMeq_refl _) ltac:(vm_compute; reflexivity)) as E. exact (f_equal (fun f => f p) E).
Qed.

Lemma VD_ltu_Z x y : 0 <= x <= Int64.max_unsigned -> 0 <= y <= Int64.max_unsigned ->
  Int64.ltu (Int64.repr x) (Int64.repr y) = (x <? y).
Proof.
  intros. unfold Int64.ltu. rewrite !Int64.unsigned_repr by lia.
  destruct (zlt x y); symmetry; [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Qed.

Lemma VD_ltu64_false: forall a b, 0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned -> a <= b ->
  Int64.ltu (Int64.repr b) (Int64.repr a) = false.
Proof.
  intros. unfold Int64.ltu. rewrite !Int64.unsigned_repr by lia.
  destruct (zlt b a); [lia | reflexivity].
Qed.

Lemma VD_repr1_neq0: Int.repr 1 <> Int.zero.
Proof. intro H; inv H. Qed.

Lemma VD_free_prep {cs: compspecs} sh t v p :
  (if eq_dec p nullval then emp else malloc_token sh t p * data_at sh t v p) |--
  (if eq_dec p nullval then emp else malloc_token sh t p * data_at_ sh t p).
Proof. destruct (eq_dec p nullval); [auto|]. apply sepcon_derives; [auto | apply data_at_data_at_]. Qed.

(* ---------- pointer witnesses ---------- *)

Lemma VD_pws_app: forall A B, pws_pred (A ++ B) = (pws_pred A * pws_pred B)%logic.
Proof.
  intros. unfold pws_pred. rewrite map_app. induction A as [| w A IH]; simpl.
  - rewrite emp_sepcon. auto.
  - rewrite IH, sepcon_assoc. auto.
Qed.

Lemma VD_pws_join W X : pws_pred W * pws_pred X |-- pws_pred (W ++ X).
Proof. rewrite VD_pws_app. apply derives_refl. Qed.

Lemma VD_pws_split W X : pws_pred (W ++ X) |-- pws_pred W * pws_pred X.
Proof. rewrite VD_pws_app. apply derives_refl. Qed.

(* the witnesses lent to ZSTD_decompressStream for the input chunk: the unused byte of ib = malloc(1) when ilen = 0 *)
Definition VD_W (il: Z) (ib: val) : list ptr_witness :=
  if zeq il 0 then [pw_bytes Ews 1 [Vundef] ib] else [].

Lemma VD_buf_ok_pos W n p : 0 < n -> buf_ok W Ews n p.
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

Lemma VD_buf_ok_zero p c : buf_ok [pw_bytes Ews 1 c p] Ews 0 p.
Proof.
  unfold buf_ok, pws_pred. simpl map. simpl fold_right. cbn [pw_pred]. rewrite sepcon_emp.
  assert_PROP (isptr p) by (saturate_local; apply prop_right; match goal with H: field_compatible _ _ p |- _ => destruct H as [? _]; auto end).
  rewrite isptr_offset_val_zero by auto.
  apply andp_right; apply sepcon_weak_valid_pointer1;
    (eapply derives_trans; [apply data_at_valid_ptr; auto; simpl; lia | apply valid_pointer_weak]).
Qed.

Lemma VD_buf_ok_app W X sh n p : buf_ok X sh n p -> buf_ok (W ++ X) sh n p.
Proof.
  unfold buf_ok. intros H. rewrite VD_pws_app, sepcon_assoc.
  apply andp_right; apply sepcon_weak_valid_pointer2;
    (eapply derives_trans; [exact H|]); [apply andp_left1 | apply andp_left2]; auto.
Qed.

Lemma VD_sddict_app W X dd : sddict_ok W dd -> sddict_ok (W ++ X) dd.
Proof.
  unfold sddict_ok. destruct (dd_ref dd); auto. intros [H1 H2]. split; auto.
  rewrite VD_pws_app. apply sepcon_valid_pointer1. exact H2.
Qed.

Lemma VD_sdo_app W X st : stream_dict_ok W st -> stream_dict_ok (W ++ X) st.
Proof.
  unfold stream_dict_ok. intros (H1 & H2 & H3). split; [|split; [|exact H3]].
  - destruct (dc_dict st) as [d|]; auto. destruct H1 as [H1a H1b]. split; auto.
    destruct (dr_src d); auto. apply VD_sddict_app; auto.
  - eapply Forall_impl; [|exact H2]. intros e. apply VD_sddict_app.
Qed.

Lemma VD_sdo_eq W a b : dc_dict a = dc_dict b -> dc_set a = dc_set b -> dc_bl a = dc_bl b ->
  stream_dict_ok W a -> stream_dict_ok W b.
Proof. unfold stream_dict_ok. intros -> -> ->. auto. Qed.

Lemma VD_ib_split ib il m A : Zlength A = il -> (0 < il /\ m = il) \/ (il = 0 /\ m = 1) ->
  @data_at ZCS Ews (tarray tuchar m) (A ++ Zrepeat Vundef (m - il)) ib |--
  !!(buf_ok (VD_W il ib) Ews il ib) && (@data_at ZCS Ews (tarray tuchar il) A ib * pws_pred (VD_W il ib)).
Proof.
  intros HA [[Hil ->] | [-> ->]].
  - unfold VD_W. destruct (zeq il 0); [lia|]. rewrite Z.sub_diag.
    change (Zrepeat Vundef 0) with (@nil val). rewrite app_nil_r.
    unfold pws_pred; simpl. rewrite sepcon_emp.
    apply andp_right; [apply prop_right; apply VD_buf_ok_pos; lia | apply derives_refl].
  - apply Zlength_nil_inv in HA. subst A. unfold VD_W. rewrite if_true by auto.
    apply andp_right; [apply prop_right; apply VD_buf_ok_zero|].
    unfold pws_pred; simpl. rewrite sepcon_emp.
    assert_PROP (isptr ib) by (saturate_local; apply prop_right; match goal with H: field_compatible _ _ ib |- _ => destruct H as [? _]; auto end).
    change (Zrepeat Vundef (1 - 0)) with [Vundef]. change (Zrepeat Vundef 1) with [Vundef].
    rewrite <- (emp_sepcon (@data_at ZCS Ews (tarray tuchar 1) [Vundef] ib)) at 1.
    apply sepcon_derives; [apply data_at_zero_array; auto | apply derives_refl].
Qed.

Lemma VD_ib_join ib il m A : (0 < il /\ m = il) \/ (il = 0 /\ m = 1) ->
  @data_at ZCS Ews (tarray tuchar il) A ib * pws_pred (VD_W il ib) |-- @data_at_ ZCS Ews (tarray tuchar m) ib.
Proof.
  intros [[Hil ->] | [-> ->]].
  - unfold VD_W. destruct (zeq il 0); [lia|]. unfold pws_pred; simpl. rewrite sepcon_emp.
    apply data_at_data_at_.
  - unfold VD_W. rewrite if_true by auto. unfold pws_pred; simpl. rewrite sepcon_emp.
    assert_PROP (A = []) by (entailer!; apply Zlength_nil_inv; auto). subst A.
    sep_apply (@data_at_zero_array_inv ZCS Ews tuchar (@nil val) ib); auto.
    rewrite emp_sepcon. apply data_at_data_at_.
Qed.

(* ---------- the stream's state ---------- *)

(* the caller's view of the stream's read bytes: zstd has read ss_ahead (0 or 1) bytes beyond the caller's ipos *)
Definition VD_in_ok (ss: sstate) (ipos: Z) (bs: list Z) : Prop :=
  0 <= ss_ahead ss <= 1 /\ ipos + ss_ahead ss <= Zlength bs /\ ss_in ss = sublist 0 (ipos + ss_ahead ss) bs.

(* stream_post (API v3), unpacked, in buffered mode, with the hostage byte released by a 0 return *)
Lemma VD_post st st' r ob osz opos opos' oc oc' ibs isz ipos ipos' :
  dc_stable st = false ->
  stream_post st st' r ob osz opos opos' oc oc' ibs isz ipos ipos' ->
  exists dl stall' a',
    opos <= opos' <= osz /\ ipos <= ipos' <= isz /\ Zlength oc' = osz /\
    sublist 0 opos oc' = sublist 0 opos oc /\
    Zlength dl = opos' - opos /\
    (stream_alive_m (dmode_w (dmode_of (dc_par st))) (fst (st_sel st)) (snd (st_sel st))
        (ss_in (dc_ss st) ++ sublist (ipos + ss_ahead (dc_ss st)) (ipos' + a') ibs) ->
       sublist opos opos' oc' = zbytes dl /\ bytes_ok dl) /\
    0 <= a' <= 1 /\ ipos + ss_ahead (dc_ss st) <= ipos' + a' /\
    (ipos' + a' <= isz \/ ipos' + a' = ipos + ss_ahead (dc_ss st)) /\ (r = 0 -> a' = 0) /\
    st' = set_last
            (set_ss st {| ss_in := ss_in (dc_ss st) ++ sublist (ipos + ss_ahead (dc_ss st)) (ipos' + a') ibs;
                          ss_out := ss_out (dc_ss st) ++ dl;
                          ss_stall := stall'; ss_err := is_error_code r;
                          ss_obuf := None; ss_ahead := a';
                          ss_calls := ss_calls (dc_ss st) ++ [(sublist ipos isz ibs, osz - opos)] |})
            (Some stream_mark) /\
    (is_error_code r = false -> (ipos' <> ipos \/ opos' <> opos) -> stall' = 0) /\
    (is_error_code r = false -> ipos' = ipos -> opos' = opos -> 0 <= stall' <= ss_stall (dc_ss st) + 1) /\
    stall_ok r (ss_stall (dc_ss st)) ipos ipos' isz opos opos' osz /\
    stream_claims_m (dmode_w (dmode_of (dc_par st))) (fst (st_sel st)) (snd (st_sel st)) (dp_wmax (dc_par st))
      (sublist 0 (Zlength (ss_in (dc_ss st)) - ss_ahead (dc_ss st)) (ss_in (dc_ss st))) (ss_out (dc_ss st))
      (ss_in (dc_ss st) ++ sublist (ipos + ss_ahead (dc_ss st)) (ipos' + a') ibs)
      ((ss_in (dc_ss st) ++ sublist (ipos + ss_ahead (dc_ss st)) (ipos' + a') ibs) ++ sublist (ipos' + a') isz ibs)
      (ss_out (dc_ss st) ++ dl) a' None r.
Proof.
  intros Hs H. destruct H as (dl & stall' & a' & H). cbv zeta in H. rewrite Hs in H.
  destruct H as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & Hh & A10 & A11 & A12 & _ & A13 & A14 & _).
  exists dl, stall', a'.
  do 5 (split; [assumption|]). split; [intros X; apply A6; right; exact X|].
  do 3 (split; [assumption|]). split; [exact (stream_hostage_zero a' r Hh A7)|].
  repeat (split; [assumption|]). exact A14.
Qed.

(* the bytes the caller saw consumed before the call *)
Lemma VD_sin0 (l: list Z) ipos a : 0 <= ipos -> 0 <= a -> ipos + a <= Zlength l ->
  sublist 0 (Zlength (sublist 0 (ipos + a) l) - a) (sublist 0 (ipos + a) l) = sublist 0 ipos l.
Proof.
  intros. rewrite Zlength_sublist by lia. rewrite sublist_sublist by lia. f_equal; lia.
Qed.
