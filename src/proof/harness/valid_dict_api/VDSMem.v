(* vd_stream (harness/valid_dict_api.c) and the static sr (a wseries_t of 786936 bytes, at any readable share):
   its fields one by one, the byte sr.content[k] it reads, and the bytes of src it lends to exact_copy.  Never
   let VST compute on the whole struct. *)
Require Import VST.floyd.proofauto.
Require Export Zstd.proof.harness.valid_dict_api.WTopSpecs_valid_dict_api.

Local Notation HCS := Zstd.proof.harness.valid_dict_api.HOK_valid_dict_api.CompSpecs.

Definition VD_Rb (sh: share) (v: list val) (p: val) : mpred := @field_at HCS sh t_wseries (DOT _bytes) v p.
Definition VD_Rn (sh: share) (v: val) (p: val) : mpred := @field_at HCS sh t_wseries (DOT _n) v p.
Definition VD_Rc (sh: share) (v: list val) (p: val) : mpred := @field_at HCS sh t_wseries (DOT _content) v p.
Definition VD_Rcn (sh: share) (v: val) (p: val) : mpred := @field_at HCS sh t_wseries (DOT _content_n) v p.
Definition VD_Rf (sh: share) (v: list (reptype t_winfo)) (p: val) : mpred := @field_at HCS sh t_wseries (DOT _f) v p.
Definition VD_Rnf (sh: share) (v: val) (p: val) : mpred := @field_at HCS sh t_wseries (DOT _nframes) v p.

Definition VD_bv (ws: wseries) : list val := zbytes (ws_bytes ws) ++ Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength (ws_bytes ws)).
Definition VD_cv (ws: wseries) : list val := zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws)).
Definition VD_fv (ws: wseries) : list (reptype t_winfo) :=
  map winfo_val (ws_frames ws) ++ Zrepeat (winfo_val winfo0) (4 - Zlength (ws_frames ws)).

Lemma VD_sr_unfold sh ws p :
  @data_at HCS sh t_wseries (wseries_val ws) p |--
  VD_Rb sh (VD_bv ws) p * VD_Rn sh (vl (Zlength (ws_bytes ws))) p * VD_Rc sh (VD_cv ws) p *
  VD_Rcn sh (vl (Zlength (ws_content ws))) p * VD_Rf sh (VD_fv ws) p *
  VD_Rnf sh (vu (Zlength (ws_frames ws))) p * spacer sh 786932 786936 p.
Proof.
  unfold VD_Rb, VD_Rn, VD_Rc, VD_Rcn, VD_Rf, VD_Rnf, VD_bv, VD_cv, VD_fv.
  unfold_data_at (@data_at HCS sh t_wseries _ _). unfold wseries_val; cbn [fst snd].
  cancel.
Qed.

Lemma VD_sr_fold sh ws p :
  VD_Rb sh (VD_bv ws) p * VD_Rn sh (vl (Zlength (ws_bytes ws))) p * VD_Rc sh (VD_cv ws) p *
  VD_Rcn sh (vl (Zlength (ws_content ws))) p * VD_Rf sh (VD_fv ws) p *
  VD_Rnf sh (vu (Zlength (ws_frames ws))) p * spacer sh 786932 786936 p |--
  @data_at HCS sh t_wseries (wseries_val ws) p.
Proof.
  unfold VD_Rb, VD_Rn, VD_Rc, VD_Rcn, VD_Rf, VD_Rnf, VD_bv, VD_cv, VD_fv.
  unfold_data_at (@data_at HCS sh t_wseries _ _). unfold wseries_val; cbn [fst snd].
  cancel.
Qed.

Lemma VD_borrow (P Q R: mpred) : P |-- Q * R -> Q * R |-- P -> P |-- R * (R -* P).
Proof.
  intros H1 H2. eapply derives_trans; [exact H1|].
  rewrite (sepcon_comm Q R). apply sepcon_derives; [apply derives_refl|].
  apply wand_sepcon_adjoint. exact H2.
Qed.

Lemma VD_content_split sh (V: list val) p k :
  0 <= k < 2 ^ 18 -> Zlength V = 2 ^ 18 ->
  field_compatible (cs := HCS) t_wseries (DOT _content) p ->
  @field_at HCS sh t_wseries (DOT _content) V p =
  (@data_at HCS sh (Tarray tuchar k noattr) (sublist 0 k V) (offset_val 524296 p) *
  @data_at HCS sh tuchar (Znth k V) (offset_val (524296 + k) p) *
  @data_at HCS sh (Tarray tuchar (262144 - (k + 1)) noattr) (sublist (k + 1) 262144 V)
    (offset_val (524296 + (k + 1)) p))%logic.
Proof.
  intros Hk HV FC.
  rewrite field_at_data_at.
  assert (FC1 := field_compatible_app nil t_wseries (DOT _content) p FC).
  assert (FA: field_address t_wseries (DOT _content) p = offset_val 524296 p).
  { unfold field_address. rewrite if_true by auto. reflexivity. }
  rewrite FA in *.
  change (nested_field_type t_wseries (DOT _content)) with (Tarray tuchar 262144 noattr) in *.
  rewrite (split3_data_at_Tarray_tuchar sh 262144 k (k + 1) V) by lia.
  rewrite !field_address0_offset by auto with field_compatible.
  simpl nested_field_type. simpl nested_field_offset. rewrite !offset_offset_val.
  replace (524296 + (0 + 1 * k)) with (524296 + k) by lia.
  replace (524296 + (0 + 1 * (k + 1))) with (524296 + (k + 1)) by lia.
  replace (k + 1 - k) with 1 by lia.
  rewrite sublist_len_1 by lia.
  rewrite (data_at_singleton_array_eq sh tuchar (Znth k V) [Znth k V]) by reflexivity.
  reflexivity.
Qed.

(* sr.content[k], lent out of its field *)
Lemma VD_content_borrow sh (V: list val) p k :
  0 <= k < 2 ^ 18 -> Zlength V = 2 ^ 18 ->
  VD_Rc sh V p |--
  @data_at HCS sh tuchar (Znth k V) (offset_val (524296 + k) p) *
  (@data_at HCS sh tuchar (Znth k V) (offset_val (524296 + k) p) -* VD_Rc sh V p).
Proof.
  intros Hk HV. unfold VD_Rc.
  eapply derives_trans; [rewrite field_at_compatible'; apply derives_refl|].
  apply derives_extract_prop; intro FC.
  rewrite (VD_content_split sh V p k Hk HV FC).
  apply VD_borrow with
    (Q := (@data_at HCS sh (Tarray tuchar k noattr) (sublist 0 k V) (offset_val 524296 p) *
          @data_at HCS sh (Tarray tuchar (262144 - (k + 1)) noattr) (sublist (k + 1) 262144 V)
            (offset_val (524296 + (k + 1)) p))%logic);
    cancel.
Qed.

(* the bytes [ipos, ipos + ilen) of src, lent to exact_copy(src + ipos, ilen) *)
Lemma VD_src_borrow sh (B: list Z) p ipos ilen :
  0 <= ipos -> 0 <= ilen -> ipos + ilen <= Zlength B ->
  @data_at HCS sh (tarray tuchar (Zlength B)) (zbytes B) p |--
  @data_at HCS sh (tarray tuchar ilen) (zbytes (sublist ipos (ipos + ilen) B)) (offset_val ipos p) *
  (@data_at HCS sh (tarray tuchar ilen) (zbytes (sublist ipos (ipos + ilen) B)) (offset_val ipos p) -*
   @data_at HCS sh (tarray tuchar (Zlength B)) (zbytes B) p).
Proof.
  intros H0 H1 H2.
  assert_PROP (@field_compatible HCS (tarray tuchar (Zlength B)) nil p) by entailer!.
  set (L := zbytes B).
  assert (HL: Zlength L = Zlength B) by (subst L; list_solve).
  assert (HB: sublist ipos (ipos + ilen) L = zbytes (sublist ipos (ipos + ilen) B)) by (subst L; list_solve).
  unfold tarray. rewrite (split3_data_at_Tarray_tuchar sh (Zlength B) ipos (ipos + ilen) L) by lia.
  rewrite HB. replace (ipos + ilen - ipos) with ilen by lia.
  rewrite field_address0_offset by auto with field_compatible.
  replace (offset_val (nested_field_offset (Tarray tuchar (Zlength B) noattr) (SUB ipos)) p)
    with (offset_val ipos p) by (simpl nested_field_offset; f_equal; lia).
  match goal with |- sepcon (sepcon ?A ?B) ?C |-- _ =>
    apply derives_trans with (sepcon B (sepcon A C));
    [cancel | apply sepcon_derives; [apply derives_refl | rewrite <- wand_sepcon_adjoint; cancel]] end.
Qed.
