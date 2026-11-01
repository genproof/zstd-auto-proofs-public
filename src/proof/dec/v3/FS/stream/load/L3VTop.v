(* FS3 streaming, case zdss_load: the case up to the computation of loadedSize (nextSrcSize,
   isSkipFrame, limitCopy into inBuff); the rest (ld_rest) is P_ld_rest.  Port of v2 StreamSeg_load.seg_load_ok. *)
Require Import Zstd.proof.dec.v3.FS.stream.load.L3Stmts Zstd.proof.dec.v3.FS.stream.load.L3Dsub.
Require Import Zstd.proof.dec.v3.FS.stream.load.L3Ex.
Local Open Scope logic.

Section CM_L3VTop_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* the rest of the case, from ld_join (it never falls through: break or return), with the exact claim of the loop
   state at the case's start *)
Definition P_ld_rest : Prop :=
  forall (Espec: OracleKind) DENT TABS BR a k0 sv ipc opc oc dl E L R,
  DENT_OK DENT -> TABS_OK TABS -> dsa_ok a -> start_ok a ->
  call_inv a k0 sv ipc opc oc dl -> (dc_stable (a_st a) = false -> sublist opc (a_osz a) oc = sublist opc (a_osz a) (a_oc a)) ->
  sf_stage (c3_s k0) = zdss_load ->
  fs_expected (c3_fs k0) = vlong E -> 0 <= E < 2 ^ 32 ->
  L = Z.min (E - fp_inpos (sv_fp sv)) (a_isz a - ipc) ->
  Zlength (sf_ring (c3_s k0)) = sf_inSize (c3_s k0) + sf_outSize (c3_s k0) ->
  ex_call a (ld_w0 k0 sv ipc opc oc dl) ->
  RA_normal R = ds_inv_x DENT TABS a -> RA_return R = RA_return (ds_R_x DENT TABS BR a) ->
  semax (ds_Delta DENT TABS BR) (ld_join DENT TABS a
       (k_load k0 (fp_inpos (sv_fp sv))
          (ring_load (sv_fp sv) (sf_ring (c3_s k0)) (fp_inpos (sv_fp sv)) (a_ibs a) ipc L))
       sv ipc opc oc dl E L)
    ld_rest (overridePost FF (switch_ret_assert R)).

(* the case's statements before ld_rest *)
Definition ld_A : statement := match ds_case_load with Ssequence s _ => s | _ => Sskip end.
Definition ld_B : statement := match ds_case_load with Ssequence _ (Ssequence s _) => s | _ => Sskip end.
Definition ld_C : statement := match ds_case_load with Ssequence _ (Ssequence _ (Ssequence s _)) => s | _ => Sskip end.
Definition ld_D : statement :=
  match ds_case_load with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence s _))) => s | _ => Sskip end.
Lemma ld_case_eq : ds_case_load = Ssequence ld_A (Ssequence ld_B (Ssequence ld_C (Ssequence ld_D ld_rest))).
Proof. reflexivity. Qed.

Definition ld_Gs : funspecs := [ZSTD_nextSrcSizeToDecompress_spec; ZSTD_isSkipFrame_spec; ZSTD_limitCopy_spec].

Lemma ld_ring_len : forall DENT TABS a w, isptr (sf_inBuff (c3_s (w_k w))) ->
  PROPx [] (LOCALx (ds_LI_L a w) (SEPx (ds_LI_S DENT TABS a w))) |--
  !! (Zlength (sf_ring (c3_s (w_k w))) = sf_inSize (c3_s (w_k w)) + sf_outSize (c3_s (w_k w))).
Proof.
intros DENT TABS a w Hib.
unfold ds_LI_S, ctx_rep3, ctx_body3, sgroup, sf_given, ring_rep.
rewrite if_false by (intro Hn; rewrite Hn in Hib; contradiction).
Intros. go_lowerx. entailer!.
Qed.

Lemma byte_cells_sublist : forall (l: list val) lo hi, byte_cells l -> byte_cells (sublist lo hi l).
Proof. intros. apply Forall_sublist. exact H. Qed.

Lemma byte_cells_app : forall (l1 l2: list val), byte_cells l1 -> byte_cells l2 -> byte_cells (l1 ++ l2).
Proof. intros. apply Forall_app. auto. Qed.

Lemma byte_cells_zbytes : forall (l: list Z), bytes_ok l -> byte_cells (zbytes l).
Proof.
intros l H. unfold byte_cells. apply Forall_map. eapply Forall_impl; [|exact H].
intros b Hb. exists b. unfold is_byte in Hb. auto.
Qed.

Lemma byte_cells_ring_load : forall fp ring P ibs ipc L, byte_cells ring -> bytes_ok ibs ->
  byte_cells (ring_load fp ring P ibs ipc L).
Proof.
intros fp ring P ibs ipc L Hr Hb. unfold ring_load. destruct (is_skip fp); [exact Hr|].
unfold copy_cells. apply byte_cells_app; [apply byte_cells_sublist; exact Hr|].
apply byte_cells_app; apply byte_cells_sublist; [apply byte_cells_zbytes; exact Hb|exact Hr].
Qed.


Lemma ld_pre_ok : forall (Espec: OracleKind) DENT TABS a w E R,
  dsa_ok a -> call_inv a (w_k w) (w_sv w) (w_ipc w) (w_opc w) (w_oc w) (w_dl w) -> w_smw w = 1 ->
  sf_stage (c3_s (w_k w)) = zdss_load -> fs_expected (c3_fs (w_k w)) = vlong E -> 0 <= E < 2 ^ 32 ->
  semax (ld_DeltaG ld_Gs) (PROPx [] (LOCALx (ds_LI_L a w) (SEPx (ds_LI_S DENT TABS a w))))
    (Ssequence (Ssequence (Ssequence ld_A ld_B) ld_C) ld_D)
    (overridePost (ld_join DENT TABS a
       (k_load (w_k w) (fp_inpos (sv_fp (w_sv w)))
          (ring_load (sv_fp (w_sv w)) (sf_ring (c3_s (w_k w))) (fp_inpos (sv_fp (w_sv w))) (a_ibs a) (w_ipc w)
             (Z.min (E - fp_inpos (sv_fp (w_sv w))) (a_isz a - w_ipc w))))
       (w_sv w) (w_ipc w) (w_opc w) (w_oc w) (w_dl w) E
       (Z.min (E - fp_inpos (sv_fp (w_sv w))) (a_isz a - w_ipc w))) R).
Proof.
intros Espec DENT TABS a w E0 R Ha Hinv Hsmw Hstage HE0 HE00.
apply ld_unsplit4.
destruct R as [Rn Rb Rc Rr].
unfold ld_DeltaG, ld_Gs.
destruct w as [smw k sv ipc opc oc dl]; cbn [w_k w_sv w_ipc w_opc w_oc w_dl w_smw] in *. subst smw.
destruct k as [fs tabs stable dict s par sp set]; cbn [c3_fs c3_tabs c3_stable c3_dict c3_s c3_par c3_sp c3_set] in *.
pose proof Hinv as Hinv0.
destruct Hinv as (Hipc & Hopc & Hloc & Hpre & Hldl & Hdl & Hbdl & Hbase & Hbin & Hnfp1 & Hnfp2 & Hnfp3 & Hcore &
                  Hdd & Hstout & Hahead & Hbsm & Hmodel & Hlh & Hsah & Hexp & HTT).
unfold ds_LI_L, ds_LI_S, ctx_rep3, ctx_body3, fgroup3, sgroup, sf_given, frame_fields;
  cbn [w_k w_sv w_ipc w_opc w_oc w_dl w_smw c3_fs c3_tabs c3_stable c3_dict c3_s c3_par c3_sp c3_set].
Intros.
match goal with H: byte_cells (sf_ring s) |- _ => rename H into Hbyc end.
match goal with H: sf_inBuff s <> nullval -> _ |- _ => rename H into H6 end.
pose proof Ha as Ha'.
destruct Ha' as (Hbo & Hbi & Hstb & Hwo & Hwi & Hwob & Hrb & Hdict & Herr & Hopos & Hosz & Hloc0 & Hipos & Hisz & Hlibs & Hbibs & Hstbuf & Hwit).
destruct (load_facts _ _ _ _ _ Hcore Hstage) as (E & fst & HE & HP & HPE & HE32 & Hfst & Hfst7 & Hskip & HEin & [ts Hts] & Hib).
cbn [c3_fs c3_tabs c3_s] in HE, HP, Hfst, HEin, Hts, Hib. rewrite HE in HE0. apply vlong_eq in HE0; [|rep_lia|rep_lia]. subst E0.
rewrite HE, HP, Hfst. subst tabs.
assert_PROP (Zlength (sf_ring s) = sf_inSize s + sf_outSize s) as Hrl0
  by (unfold ring_rep; rewrite if_false by (intro Hn; rewrite Hn in Hib; contradiction); entailer!).
unfold ld_A, ld_B, ld_C, ld_D, ds_case_load.
forward_call (a_d a, E).
forward. forward.
forward_call (a_d a, fst).
assert_PROP (isptr (a_ib a)) as Hibp by entailer!.
set (P := fp_inpos (sv_fp sv)) in *.
set (L := Z.min (E - P) (a_isz a - ipc)).
assert (Hsub: Int64.sub (Int64.repr E) (Int64.repr P) = Int64.repr (E - P))
  by (unfold Int64.sub; rewrite !Int64.unsigned_repr by rep_lia; reflexivity).
rewrite Hsub.
set (k0 := {| c3_fs := fs; c3_tabs := TInit (dd_ox (sv_dd sv)) ts; c3_stable := stable; c3_dict := dict; c3_s := s;
              c3_par := par; c3_sp := sp; c3_set := set |}).
set (ring1 := ring_load (sv_fp sv) (sf_ring s) P (a_ibs a) ipc L).
forward_if (ld_join DENT TABS a (k_load k0 P ring1) sv ipc opc oc dl E L).
- (* a skippable frame *)
  assert (Hsk: is_skip (sv_fp sv) = true).
  { apply Hskip. destruct (fst =? ds_skipFrame) eqn:Hf; [lia|]. contradiction. }
  assert (Hr1: ring1 = sf_ring s) by (unfold ring1, ring_load; rewrite Hsk; reflexivity).
  fif_temp _t'56 (vlong L).
  { sbk. }
  { match goal with H: typed_true _ _ |- _ => cond64 H end.
    forward. entailer!. unfold L; rewrite Z.min_l by lia; auto. }
  { match goal with H: typed_false _ _ |- _ => cond64 H end.
    forward. { sbk. }
    entailer!. unfold L; rewrite Z.min_r by lia. rewrite sub_pp_off by (auto; rep_lia). reflexivity. }
  forward.
  unfold ld_join, ds_LI_L, ds_LI_S, k_load, k0, ctx_rep3, ctx_body3, fgroup3, sgroup, sf_given, frame_fields.
  cbn [w_k w_sv w_ipc w_opc w_oc w_dl w_smw c3_fs c3_tabs c3_stable c3_dict c3_s c3_par c3_sp c3_set c3_with_s s_load
       sf_stage sf_inBuff sf_inSize sf_inPos sf_outBuff sf_outSize sf_outStart sf_outEnd sf_lhSize
       sf_hostage sf_nfp sf_expOut sf_hbuf sf_over sf_ring sf_mem sf_held sf_given].
  rewrite Hr1, HE, Hfst. entailer!.
- (* a Zstandard frame: load into inBuff *)
  assert (Hsk: is_skip (sv_fp sv) = false).
  { destruct (is_skip (sv_fp sv)) eqn:Hk; auto. exfalso.
    assert (fst = ds_skipFrame) by (apply Hskip; reflexivity). subst fst.
    first [ match goal with H: (if _ then 1 else 0) = 0 |- _ => rewrite Z.eqb_refl in H; discriminate end
          | match goal with H: Int.repr (if _ then 1 else 0) = Int.zero |- _ =>
              rewrite Z.eqb_refl in H; apply (f_equal Int.unsigned) in H;
              rewrite Int.unsigned_repr in H by rep_lia; discriminate end
          | fail 0 "skipfalse" ]. }
  specialize (HEin Hsk).
  assert (Hr1: ring1 = copy_cells (sf_ring s) P (zbytes (a_ibs a)) ipc L)
    by (unfold ring1, ring_load; rewrite Hsk; reflexivity).
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre break: Pre end.
  { entailer!. }
  { forward. forward. forward_if.
    { exfalso. cond64h. lia. }
    { forward. entailer!. } }
  forward. forward.
  unfold ring_rep. rewrite if_false by (intro Hn; rewrite Hn in Hib; contradiction).
  Intros.
  match goal with H: Zlength (sf_ring s) = _ |- _ => rename H into Hrl end.
  assert (Hlz: Zlength (zbytes (a_ibs a)) = a_isz a) by list_solve.
  sep_apply (tarray_len Ews _ (sf_ring s) (sf_inBuff s) Hrl).
  sep_apply (tarray_len (a_shb a) _ (zbytes (a_ibs a)) (a_ib a) Hlz).
  forward_call (Ews, sf_inBuff s, sf_ring s, P, E - P, a_shb a, a_ib a, zbytes (a_ibs a), ipc, a_isz a - ipc).
  { sbk. }
  { entailer!.
    rewrite sub_pp_off by (auto; rep_lia). simpl. destruct (sf_inBuff s); try contradiction. simpl.
    change (Ptrofs.repr 1) with Ptrofs.one. rewrite Ptrofs.mul_commut, Ptrofs.mul_one.
    unfold Ptrofs.of_int64. rewrite Int64.unsigned_repr by rep_lia. reflexivity. }
  (* the copied input bytes are defined *)
  all: try (apply byte_cells_sublist, byte_cells_zbytes; exact Hbibs).
  forward.
  unfold ld_join, ds_LI_L, ds_LI_S, k_load, k0, ctx_rep3, ctx_body3, fgroup3, sgroup, sf_given, frame_fields, ring_rep.
  cbn [w_k w_sv w_ipc w_opc w_oc w_dl w_smw c3_fs c3_tabs c3_stable c3_dict c3_s c3_par c3_sp c3_set c3_with_s s_load
       sf_stage sf_inBuff sf_inSize sf_inPos sf_outBuff sf_outSize sf_outStart sf_outEnd sf_lhSize
       sf_hostage sf_nfp sf_expOut sf_hbuf sf_over sf_ring sf_mem sf_held sf_given].
  rewrite if_false by (intro Hn; rewrite Hn in Hib; contradiction).
  rewrite Hr1, HE, Hfst.
  assert (Hlc: Zlength (copy_cells (sf_ring s) P (zbytes (a_ibs a)) ipc L) = sf_inSize s + sf_outSize s)
    by (rewrite Zlength_copy_cells; unfold L; lia).
  sep_apply (tarray_len' (a_shb a) (a_isz a) (zbytes (a_ibs a)) (a_ib a) Hlz).
  assert (Hbyc1: byte_cells (copy_cells (sf_ring s) P (zbytes (a_ibs a)) ipc L))
    by (rewrite <- Hr1; unfold ring1; apply byte_cells_ring_load; [exact Hbyc|exact Hbibs]).
  rewrite Hrl. entailer!.
Qed.


Lemma seg_load_top : P_ld_rest -> seg_case_x 3.
Proof.
intros Hrest Espec DENT TABS BR a w R HD HT Ha Hinv Hsmw Hext Hstage HRn HRr Hstart Hentry Hun Hx.
assert (Hx0: ex_call a (ld_w0 (w_k w) (w_sv w) (w_ipc w) (w_opc w) (w_oc w) (w_dl w)))
  by (destruct w; cbn in Hsmw |- *; subst; exact Hx).
pose proof Hinv as Hinv0.
destruct Hinv0 as (_&_&_&_&_&_&_&_&_&_&_&_&Hcore&_).
destruct (load_facts _ _ _ _ _ Hcore Hstage) as (E & fst & HE & HP & HPE & HE32 & _ & _ & _ & _ & _ & Hib).
assert_PROP (Zlength (sf_ring (c3_s (w_k w))) = sf_inSize (c3_s (w_k w)) + sf_outSize (c3_s (w_k w))) as Hrl0.
{ apply andp_left2. apply ld_ring_len. exact Hib. }
unfold ds_tail. simpl seq_of_labeled_statement.
rewrite ld_case_eq.
eapply semax_seq; [|apply semax_ff].
eapply ld_split4.
{ apply (ld_Delta_lift DENT TABS BR ld_Gs); [intros sp Hsp; unfold ld_Gs in Hsp; simpl in Hsp;
    repeat (destruct Hsp as [<-|Hsp]; [ld_in_tac|]); destruct Hsp|].
  apply (ld_pre_ok Espec DENT TABS a w E); auto; lia. }
apply (Hrest Espec DENT TABS BR a (w_k w) (w_sv w) (w_ipc w) (w_opc w) (w_oc w) (w_dl w) E _ R HD HT Ha Hstart Hinv Hun
         Hstage HE ltac:(lia) eq_refl Hrl0 Hx0 HRn HRr).
Qed.

End CM_L3VTop_1.
