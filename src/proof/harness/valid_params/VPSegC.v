(* valid_params main, segment C (see the header of VPMain.v). *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.harness.valid_params.VPMain.
Require Import Zstd.proof.harness.valid_params.VPMem2 Zstd.proof.harness.valid_params.VPMem3.

Local Notation HCS := Zstd.proof.harness.valid_params.HOK_valid_params.CompSpecs.
Local Notation ZCS := Zstd.proof.zstd.Base.CompSpecs.
Local Notation tout := (Tstruct _ZSTD_outBuffer_s noattr).
Local Notation tin := (Tstruct _ZSTD_inBuffer_s noattr).

Definition VPC_s15 : statement := ltac:(
  let s := eval cbv [VP_drop VP_body0] in (VP_drop 15 VP_body0) in
  lazymatch s with Ssequence ?x _ => exact x end).

Lemma VPC_rest15 : VP_rest 15 = Ssequence (Ssequence VPC_s15 (VP_drop 16 VP_body0)) VP_ret.
Proof. reflexivity. Qed.

(* the header's size: 5..19 bytes (magicless: 4 fewer) *)
Lemma VPC_fhd_le : forall x, fhd_header_size x <= 19.
Proof.
  intros x. unfold fhd_header_size.
  assert (Hs : 0 <= Z.land (Z.shiftr x 5) 1 <= 1).
  { assert (Z.land (Z.shiftr x 5) 1 = Z.shiftr x 5 mod 2) as ->
      by (change 1 with (Z.ones 1); rewrite Z.land_ones by lia; reflexivity).
    pose proof (Z.mod_pos_bound (Z.shiftr x 5) 2). lia. }
  assert (H1 : forall n, nth n [0; 1; 2; 4] 0 <= 4) by (intros [|[|[|[|n]]]]; simpl; try lia; destruct n; lia).
  assert (H2 : forall n, nth n [0; 2; 4; 8] 0 <= 8) by (intros [|[|[|[|n]]]]; simpl; try lia; destruct n; lia).
  specialize (H1 (Z.to_nat (Z.land x 3))). specialize (H2 (Z.to_nat (Z.shiftr x 6))).
  destruct (Z.land (Z.shiftr x 5) 1 =? 1) eqn:E; [apply Z.eqb_eq in E | apply Z.eqb_neq in E];
    destruct (Z.shiftr x 6 =? 0); simpl andb; lia.
Qed.

Lemma VPC_gfh_hs : forall s h, get_frame_header s = FH_ok h -> 5 <= fh_headerSize h <= 19.
Proof.
  intros s h H. split; [eapply vpm_gfh_hs; eauto|]. unfold get_frame_header in H.
  repeat match type of H with
  | context [if ?c then _ else _] => destruct c
  end; try discriminate; inversion H; subst; simpl;
  try (unfold ZSTD_SKIPPABLEHEADERSIZE; lia); apply VPC_fhd_le.
Qed.

Lemma VPC_hsize s f : wi_skippable f = false ->
  get_frame_header_m true s = FH_ok (fh_unshift (wi_header f)) -> 5 <= wi_hsize f <= 19.
Proof.
  intros Hsk H. unfold get_frame_header_m in H. cbn [negb] in H.
  destruct (Zlength s <? 1); [discriminate|].
  destruct (get_frame_header (magic_bytes ++ s)) as [| |h0] eqn:E; try discriminate.
  assert (H2: fh_headerSize (fh_unshift h0) = fh_headerSize (fh_unshift (wi_header f))) by congruence.
  unfold fh_unshift, wi_header in H2. rewrite Hsk in H2. cbn in H2.
  apply VPC_gfh_hs in E. lia.
Qed.

(* sr.f[0] (sr.f is at offset 786448 of wseries_t), lent to main's f = &sr.f[0] *)
Lemma VPC_f_split (x: reptype t_winfo) (L: list (reptype t_winfo)) p :
  Zlength L = 3 -> field_compatible (cs := HCS) t_wseries (DOT _f) p ->
  @field_at HCS Ews t_wseries (DOT _f) (x :: L) p =
  (@data_at HCS Ews t_winfo x (offset_val 786448 p) *
   @data_at HCS Ews (tarray t_winfo 3) L (offset_val 786568 p))%logic.
Proof.
  intros HL FC.
  rewrite field_at_data_at.
  assert (FC1 := field_compatible_app nil t_wseries (DOT _f) p FC).
  assert (FA: field_address t_wseries (DOT _f) p = offset_val 786448 p).
  { unfold field_address. rewrite if_true by auto. reflexivity. }
  rewrite FA in *.
  change (nested_field_type t_wseries (DOT _f)) with (tarray t_winfo 4) in *.
  change (x :: L) with ([x] ++ L).
  rewrite (split2_data_at_Tarray_app 1 4 Ews t_winfo [x] L) by (try rewrite HL; reflexivity).
  rewrite field_address0_offset by auto with field_compatible.
  simpl nested_field_offset. rewrite offset_offset_val.
  rewrite (data_at_singleton_array_eq Ews t_winfo x [x]) by reflexivity.
  reflexivity.
Qed.

Lemma VPC_f_borrow (x: reptype t_winfo) (L: list (reptype t_winfo)) p :
  Zlength L = 3 ->
  VP_Rf (x :: L) p |--
  @data_at HCS Ews t_winfo x (offset_val 786448 p) *
  (@data_at HCS Ews t_winfo x (offset_val 786448 p) -* VP_Rf (x :: L) p).
Proof.
  intros HL. unfold VP_Rf.
  eapply derives_trans; [rewrite field_at_compatible'; apply derives_refl|].
  apply derives_extract_prop; intro FC.
  rewrite (VPC_f_split x L p HL FC).
  apply VPC_borrow with (Q := @data_at HCS Ews (tarray t_winfo 3) L (offset_val 786568 p)); cancel.
Qed.

Lemma VPC_faddr q : isptr q ->
  force_val (sem_binary_operation' Oadd (tarray t_winfo 4) tint (eval_field t_wseries _f q) (Vint (Int.repr 0))) =
  offset_val 786448 q.
Proof. destruct q; try contradiction. intros _. simpl. rewrite Ptrofs.mul_zero, Ptrofs.add_zero. reflexivity. Qed.

(* the API specs are at the decoder's compspecs (ZCS), main at the harness's (HCS) *)
Definition VPC_cce (cs1 cs2: compspecs) : change_composite_env cs1 cs2 :=
  {| coeq := cs_preserve_env cs1 cs2;
     coeq_consistent := cs_preserve_env_consistent cs1 cs2 _ eq_refl;
     coeq_complete := cs_preserve_completeness cs1 cs2 _ eq_refl |}.

Lemma VPC_arr sh n (v: list val) p :
  @data_at ZCS sh (tarray tuchar n) v p = @data_at HCS sh (tarray tuchar n) v p.
Proof.
  pose proof (@data_at_change_composite ZCS HCS (VPC_cce ZCS HCS) sh (tarray tuchar n) v v
    (JMeq_refl _) ltac:(reflexivity)) as E. rewrite E; reflexivity.
Qed.

Lemma VPC_fh_ sh p : @data_at_ ZCS sh t_fh p = @data_at_ HCS sh t_fh p.
Proof.
  pose proof (@data_at__change_composite ZCS HCS (VPC_cce ZCS HCS) sh t_fh
    ltac:(vm_compute; reflexivity)) as E. exact (f_equal (fun g => g p) E).
Qed.

Lemma VPC_fh sh (h: frame_header) p : @data_at ZCS sh t_fh (fh_val h) p = @data_at HCS sh t_fh (fh_val h) p.
Proof.
  pose proof (@data_at_change_composite ZCS HCS (VPC_cce ZCS HCS) sh t_fh (fh_val h) (fh_val h)
    (JMeq_refl _) ltac:(vm_compute; reflexivity)) as E. exact (f_equal (fun g => g p) E).
Qed.

(* the end of s15: zfh back to data_at_, sr.f[0] back into sr.f *)
Ltac vpc_close :=
  first [ match goal with |- context [@data_at ZCS Tsh t_fh ?v ?vz] =>
            sep_apply (@data_at_data_at_ ZCS Tsh t_fh v vz) end; rewrite VPC_fh_
        | match goal with |- context [@data_at HCS Tsh t_fh ?v ?vz] =>
            sep_apply (@data_at_data_at_ HCS Tsh t_fh v vz) end ];
  match goal with |- context [(@data_at HCS Ews t_winfo ?x ?q -* VP_Rf ?L ?p)%logic] =>
    sep_apply (modus_ponens_wand (@data_at HCS Ews t_winfo x q) (VP_Rf L p)) end;
  match goal with Hfs: ws_frames ?ws = [?f] |- context [VP_Rf [winfo_val ?f; ?a; ?b; ?c]] =>
    replace [winfo_val f; a; b; c]
      with (map winfo_val (ws_frames ws) ++ Zrepeat (winfo_val winfo0) (4 - Zlength (ws_frames ws)))
      by (rewrite Hfs; reflexivity);
    match goal with |- context [ws_ck ws ?b'] => change (ws_frames (ws_ck ws b')) with (ws_frames ws) end
  end;
  entailer!.

Section Seg.
Context {Espec: OracleKind}.
Variable DC : globals -> val -> dctx_st -> mpred.
Variable DD : globals -> val -> ddict_st -> mpred.
Variable WG : globals -> mpred.
Variable WDS : wdict -> reptype t_wstate -> Prop.
Local Notation Delta := (VP_Delta DC DD WG WDS).

(* C: s15 *)
Lemma VP_segC (gv: globals) (vz vi vo: val) (mode: Z) (ws: wseries) (b': list Z) (p: dparams) (wlim: Z)
    (src dctx: val) :
  semax Delta (VP_SB DC WG gv vz vi vo mode ws b' p wlim src dctx) (VP_rest 16) VP_RR ->
  semax Delta (VP_SB DC WG gv vz vi vo mode ws b' p wlim src dctx) (VP_rest 15) VP_RR.
Proof.
  intros Hk. rewrite VPC_rest15. apply seq_assoc. fold (VP_rest 16).
  eapply semax_seq'; [| exact Hk]. clear Hk. unfold VPC_s15.
  unfold VP_SB at 1. Intros.
  sep_apply (VP_sr_unfold7w (ws_ck ws b') (gv _x_valid_params__sr)). Intros.
  unfold VP_Delta. simplify_func_tycontext.
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx L (SEPx R))) end.
  3: { unfold VP_SB. sep_apply (VP_sr_fold7w (ws_ck ws b') (gv _x_valid_params__sr)). entailer!. }
  2: { forward. entailer!. }
  match goal with H: VP_SB_facts _ _ _ _ _ |- _ => destruct H as (HA & HD & Hbs & Hm3) end.
  assert (mode = 3) by (destruct HA as [Hmd _];
    apply (f_equal Int.unsigned) in H0; rewrite !Int.unsigned_repr in H0 by rep_lia; lia).
  subst mode.
  destruct (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HA))))) eq_refl) as (f & Hfs & Hsk).
  specialize (Hm3 eq_refl f Hfs).
  change (ws_frames (ws_ck ws b')) with (ws_frames ws).
  forward.
  assert_PROP (isptr (gv _x_valid_params__sr)) by (unfold VP_Rn; entailer!).
  rewrite VPC_faddr by auto.
  replace (map winfo_val (ws_frames ws) ++ Zrepeat (winfo_val winfo0) (4 - Zlength (ws_frames ws)))
    with (winfo_val f :: [winfo_val winfo0; winfo_val winfo0; winfo_val winfo0]) by (rewrite Hfs; reflexivity).
  sep_apply (VPC_f_borrow (winfo_val f) [winfo_val winfo0; winfo_val winfo0; winfo_val winfo0]
    (gv _x_valid_params__sr) eq_refl). Intros.
  forward.
  unfold winfo_val at 1. cbv beta iota zeta.
  assert (Hwf1: winfo_wf f) by (destruct HA as (_ & _ & (Hw1 & _ & _) & _); rewrite Hfs in Hw1; inversion Hw1; auto).
  pose proof Hwf1 as (Hu1 & Hu2 & Hu3 & Hu4 & Hu5 & Hu6 & Hu7 & Hu8 & Hu9 & Hu10 & Hu11 & Hu12 & Hu13).
  unfold u32, u64 in *.
  match goal with |- semax _ (PROPx ?P (LOCALx (_ :: ?L) (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _x_valid_params__t'32 (Vint (Int.repr (if wi_big f then 1 else 0))) :: L)
      (SEPx R))) end.
  { match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp _x_valid_params__t'33 (Vint (Int.repr 31)) :: L) (SEPx R))) end.
    { exfalso. discriminate. }
    { forward. entailer!. }
    forward. unfold winfo_val at 1. cbv beta iota zeta.
    forward. entailer!.
    assert (Hs1: wi_single f = false).
    { destruct (wi_single f); [discriminate|reflexivity]. }
    unfold wi_big; rewrite Hsk, Hs1; cbn [negb andb]; change ZSTD_WINDOWLOG_MAX with 31; unfold bool2val.
    rewrite Z.gtb_ltb; destruct (zlt 31 (wi_window_log f)) as [L|L];
      [rewrite (proj2 (Z.ltb_lt 31 (wi_window_log f)) L) | rewrite (proj2 (Z.ltb_ge 31 (wi_window_log f))) by lia];
      reflexivity. }
  { forward. entailer!.
    destruct (wi_single f) eqn:Es; [|contradiction H1; reflexivity].
    unfold wi_big; rewrite Hsk, Es; reflexivity. }
  forward.
  assert (Hsrc: src_spec_pre Ews (vp_src 3 b')).
  { destruct HD as (_ & _ & _ & _ & _ & Hbok & _ & Hlb & _). cbn [ws_bytes ws_ck] in Hbok, Hlb.
    unfold vp_src, vp_base; simpl Z.eqb; cbv iota.
    split; [auto|]. split; [pose proof (sublist_max_length 4 (Zlength b') b'); lia|].
    unfold bytes_ok in *. apply Forall_sublist. auto. }
  rewrite <- VPC_fh_, <- VPC_arr.
  change (@data_at_ ZCS Tsh t_fh vz) with (@data_at ZCS Tsh t_fh (@default_val ZCS t_fh) vz).
  forward_call (gv, Tsh, vz, @default_val ZCS t_fh, Ews, src, vp_src 3 b', 1).
  Intros vret. destruct vret as [r v]. cbn [fst snd] in *.
  rewrite VPC_arr.
  match goal with H: fh_post_m _ _ _ _ _ |- _ => rename H into Hpost end.
  change (1 =? 1) with true in Hpost. unfold fh_post_m in Hpost. rewrite Hm3 in Hpost.
  destruct (wi_big f) eqn:Eb.
  - (* beyond zstd's range: an error *)
    destruct Hpost as [[Herr _] _].
    assert (Hr0: r <> 0) by (intro; subst r; discriminate Herr).
    match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp _x_valid_params__t'35 (Vint Int.one) :: L) (SEPx R))) end.
    { match goal with H: Int64.repr r = _ |- _ => apply (f_equal Int64.unsigned) in H;
        try change (Int64.unsigned Int64.zero) with 0 in H; rewrite !Int64.unsigned_repr in H by rep_lia end.
      lia. }
    { forward_if.
      { apply seq_assoc. forward_call r. forward. forward. entailer!. rewrite Herr. reflexivity. }
      { exfalso. discriminate. } }
    forward_call Int.one.
    forward_if.
    { match goal with H: Int64.repr r = _ |- _ => apply (f_equal Int64.unsigned) in H;
        try change (Int64.unsigned Int64.zero) with 0 in H; rewrite !Int64.unsigned_repr in H by rep_lia end.
      lia. }
    forward.
    vpc_close.
  - (* within range: the header *)
    destruct Hpost as [-> ->].
    pose proof (VPC_hsize _ _ Hsk Hm3) as Hhs.
    rewrite VPC_fh.
    assert (Hh: fh_val (fh_unshift (wi_header f)) =
      (Vlong (Int64.repr (if wi_fcs_present f then wi_fcs f else ZSTD_CONTENTSIZE_UNKNOWN)),
       (Vlong (Int64.repr (wi_window f)),
        (Vint (Int.repr (Z.min (wi_window f) ZSTD_BLOCKSIZE_MAX)),
         (Vint (Int.repr 0),
          (Vint (Int.repr (wi_hsize f - 4)),
           (Vint (Int.repr (wi_did f)),
            (Vint (Int.repr (if wi_checksum f then 1 else 0)),
             (Vint (Int.repr 0), Vint (Int.repr 0)))))))))).
    { unfold wi_header. rewrite Hsk. reflexivity. }
    rewrite Hh.
    match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp _x_valid_params__t'35 (Vint Int.one) :: L) (SEPx R))) end.
    { forward. entailer!. }
    { exfalso. auto. }
    forward_call Int.one.
    forward_if.
    2: { exfalso. auto. }
    forward.
    forward_call Int.one.
    forward. unfold winfo_val at 1. cbv beta iota zeta.
    match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp _x_valid_params__t'37 (Vlong (Int64.repr
        (if wi_fcs_present f then wi_fcs f else ZSTD_CONTENTSIZE_UNKNOWN))) :: L) (SEPx R))) end.
    { forward. unfold winfo_val at 1. cbv beta iota zeta. forward. entailer!.
      destruct (wi_fcs_present f); [reflexivity|]. contradiction H3'; reflexivity. }
    { forward. entailer!.
      destruct (wi_fcs_present f); [discriminate|].
      unfold ZSTD_CONTENTSIZE_UNKNOWN. f_equal. apply Int64.eqm_samerepr. exists 1. reflexivity. }
    forward. forward_call Int.one.
    { entailer!. simpl. rewrite Int64.eq_true. reflexivity. }
    forward. forward. unfold winfo_val at 1. cbv beta iota zeta.
    forward_call Int.one.
    { entailer!. simpl. rewrite Int64.eq_true. reflexivity. }
    forward. forward. unfold winfo_val at 1. cbv beta iota zeta.
    forward_call Int.one.
    { entailer!. simpl. rewrite Int64.eq_true. reflexivity. }
    forward. forward. unfold winfo_val at 1. cbv beta iota zeta.
    forward_call Int.one.
    { entailer!. simpl. rewrite Int.eq_true. reflexivity. }
    forward. forward. unfold winfo_val at 1. cbv beta iota zeta.
    forward_call Int.one.
    { entailer!. simpl. rewrite Int.eq_true. reflexivity. }
    vpc_close.
Qed.

End Seg.
