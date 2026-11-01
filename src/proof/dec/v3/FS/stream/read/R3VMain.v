(* FS3 streaming, case zdss_read: the case from its label (v2 StreamSeg_read.v seg_read_ok). *)
Require Import Zstd.proof.dec.v3.FS.stream.read.R3Step Zstd.proof.dec.v3.FS.stream.read.R3Dsub Zstd.proof.dec.v3.FS.stream.read.R3VSt Zstd.proof.dec.v3.FS.stream.read.R3VBf Zstd.proof.dec.v3.FS.stream.read.R3Inv.
Require Import Zstd.proof.dec.v3.FS.stream.read.R3X.
Local Open Scope logic.

Section CM_R3VMain_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* a buffered ring's segment holds frame output only *)
Lemma c_ring_cbound : forall obuf sout s fp pend l, c_ring false obuf sout s fp pend l -> lay_cbound fp l.
Proof.
intros obuf sout s fp pend l H b ps pe e ->.
destruct H as (_&_&_&os&oe&_&_&_&H). cbv beta iota zeta in H.
destruct H as (_&_&_&_&H). destruct H as (_&_&_&Hpc&_). exact Hpc.
Qed.

(* iend - ip on char pointers, for input buffers up to PTRDIFF_MAX ([sub_pp_tschar] is stated for offsets up
   to 2^30) *)
Lemma sub_pp_tschar63 : forall p i j, isptr p -> 0 <= j <= i -> i <= 2 ^ 63 - 1 ->
  force_val (sem_sub_pp tschar (offset_val i p) (offset_val j p)) = Vlong (Int64.repr (i - j)).
Proof.
intros p i j Hp Hj Hi. destruct p; try contradiction.
unfold sem_sub_pp; simpl. rewrite if_true by auto. simpl. f_equal.
rewrite !(Ptrofs.add_commut i0), Ptrofs.sub_shifted. rewrite Ptrofs.divs_one by reflexivity.
unfold Vptrofs, Ptrofs.sub. rewrite !Ptrofs.unsigned_repr by rep_lia. simpl.
unfold Ptrofs.to_int64. rewrite Ptrofs.unsigned_repr by rep_lia. reflexivity.
Qed.

(* the state falling into case zdss_load (with the exact claim of the iteration it continues) *)
Definition load_pre (DENT: dent_pred) (TABS: tabs_pred) (a: dsa) : environ -> mpred :=
  EX w': lw,
  PROPx [call_inv a (w_k w') (w_sv w') (w_ipc w') (w_opc w') (w_oc w') (w_dl w'); w_smw w' = 1;
         sf_stage (c3_s (w_k w')) = 3; untouched_ok a w'; ex_call a w']
  (LOCALx (ds_LI_L a w') (SEPx (ds_LI_S DENT TABS a w'))).

Ltac proj_simpl := cbn [a_W a_gv a_d a_st a_outp a_inp a_sho a_shi a_shob a_obf a_osz a_opos a_oc a_shb a_ibf
  a_isz a_ipos a_ibs a_vop w_smw w_k w_sv w_ipc w_opc w_oc w_dl].

(* case zdss_read, then case zdss_load: the relational claims as before, the exact claim (ex_call) rebuilt at each
   exit from the model's st_read (R3X) *)
Lemma seg_read_gen : MF3 -> RET3x -> seg_case_x 3 -> seg_case_x 2.
Proof.
intros M RT Hseg3 Espec DENT TABS BR a w R HD HT Ha Hinv Hsmw Hle Hstage HRn HRr Hstart Hentry Hun Hxa.
unfold ds_tail. simpl seq_of_labeled_statement.
eapply semax_seq with (Q := load_pre DENT TABS a).
2: { unfold load_pre. Intros w'.
      match goal with H: sf_stage (c3_s (w_k w')) = 3 |- _ => rename H into Hs3 end.
      apply Hseg3; auto.
      all: first [ (unfold loop_extra; intros _ Hx; rewrite Hs3 in Hx; unfold zdss_loadHeader in Hx; lia)
                 | (unfold entry_ok; intros _ Hx; rewrite Hs3 in Hx; unfold zdss_init in Hx; lia) ]. }
apply (rd_Delta_lift DENT TABS BR [ZSTD_decompressContinueStream_spec3 DENT TABS; ERR_isError_spec;
            ZSTD_nextSrcSizeToDecompressWithInputSize_spec]);
  [apply Forall_cons; [apply rd_in_cs|]; apply Forall_cons; [apply rd_in_err|];
   apply Forall_cons; [apply rd_in_nss|]; apply Forall_nil|].
fold (rd_Delta2 DENT TABS).
destruct a as [W gv d st outp inp sho shi shob obf osz opos oc shb ibf isz ipos ibs vop].
destruct w as [smw k sv ipc opc oc1 dl]. simpl in *. subst smw.
pose proof Hinv as Hinv'.
destruct Hinv' as (Hip & Hop & Hloc & Hpre & Hdl & Hdlc & Hdlb & Hbase & Hbin & Hnfp1 & Hnfp2 & Hnfp3 &
                   Hcore & Hddok & Hstout & Hahead & Hblk & Hmodel & Hlh & Hsin & Hexp0 & HT0).
simpl in *.
pose proof Hcore as Hcore'. unfold c_core in Hcore'. destruct Hcore' as (Hhost & Hcold & Hsz & Hcs).
rewrite Hstage in Hcs. simpl in Hcs.
destruct Hcs as (_ & Hcf & Hring & Hstfl & _ & Hnld & Hrd).
destruct Hnld as (Hinpos & Hraw & Hsk); [unfold zdss_read, zdss_load; lia|].
destruct Hrd as (Hpend & Hoso); [reflexivity|].
destruct (read_ns _ _ _ _ _ Hcf Hsk Hraw) as (fstage & e & Hfst & Hfe & Hfstr & Her & Hbt & Hcpl & Hns).
pose proof (rx_hd_of _ (Build_lw 1 k sv ipc opc oc1 dl) fstage e Ha Hinv Hstage Hfst Hfstr Hfe Her) as Hhd.
destruct R as [Rn Rb Rc Rr]. cbn [RA_normal RA_return] in HRn, HRr.
unfold ds_case_read. apply semax_dowhile0.
match goal with |- semax _ _ _ ?P =>
  let P' := eval cbv beta iota delta [overridePost switch_ret_assert] in P in change P with P' end.
unfold rd_Delta2, rd_Delta. abbreviate_semax.
pose proof Ha as Ha'.
destruct Ha' as (Hbufo & Hbufi & Hstbuf & Hwso & Hwsi & Hwsob & Hrsb & Hdict & Herr & Hopos & Hosz & Hloc0 &
                 Hipos & Hisz & Hlibs & Hbibs & Hstout0 & Hw0 & Hopst & _).
cbn [a_W a_gv a_d a_st a_outp a_inp a_sho a_shi a_shob a_obf a_osz a_opos a_oc a_shb a_ibf
  a_isz a_ipos a_ibs a_vop] in *.
(* the bases the code computes with (the caller's pointers, or ZSTD_emptyBuffer for NULL) *)
set (ob := a_ob _) in *. set (ib := a_ib _) in *.
unfold ds_LI_S, ds_LI_L, ctx_rep3, ctx_body3, fgroup3, sgroup. rewrite frame_fields_split. proj_simpl.
fold ob ib. Intros.
assert_PROP (isptr ib) as Pib by entailer!.
forward_call (d, fstage, fs_bType (c3_fs k), e, isz - ipc).
{ entailer!. destruct ib; try contradiction. simpl. clear. destruct (peq b b); [reflexivity | congruence]. }
{ entailer!. destruct ib; try contradiction. simpl. clear - Hip Hisz Hipos.
  unfold sem_sub_pp; simpl. rewrite if_true by auto. simpl. f_equal. f_equal.
  rewrite !(Ptrofs.add_commut i), Ptrofs.sub_shifted. rewrite Ptrofs.divs_one by reflexivity.
  unfold Vptrofs, Ptrofs.sub. rewrite !Ptrofs.unsigned_repr by rep_lia. simpl.
  unfold Ptrofs.to_int64. rewrite Ptrofs.unsigned_repr by rep_lia. reflexivity. }
all: try (match goal with |- semax _ _ _ _ => fail 1 | _ => idtac end;
  first [ rep_lia
        | intros; match goal with H: _ = ds_decompressBlock \/ _ |- _ => destruct (Hbt H) as (b&->&?) end;
          exists b; split; auto; rep_lia ]).
change (match fs_bType (c3_fs k) with Vint b => Int.signed b | _ => 0 end) with (bt_of (fs_bType (c3_fs k))).
set (ns := next_size fstage (bt_of (fs_bType (c3_fs k))) e (isz - ipc)).
unfold MORE_COMMANDS, abbreviate. apply semax_dowhile0. abbreviate_semax.
forward_if.
{ (* end of frame *)
  assert (Hc: fp_complete (sv_fp sv) = true).
  { destruct (fp_complete (sv_fp sv)) eqn:Ec; auto. exfalso.
    destruct (Hns eq_refl (isz - ipc) ltac:(lia)) as [Hr _].
    change (next_size fstage (bt_of (fs_bType (c3_fs k))) e (isz - ipc)) with ns in Hr.
    match goal with H: Int64.repr ns = Int64.zero |- _ => apply (f_equal Int64.unsigned) in H;
      rewrite Int64.unsigned_repr in H by rep_lia; rewrite Int64.unsigned_zero in H end. lia. }
  assert (Hns00: ns = 0).
  { unfold ns, next_size. destruct (Hcpl Hc) as [Hs0 ->]. destruct Hs0 as [-> | ->]; reflexivity. }
  pose proof (rx_end _ (Build_lw 1 k sv ipc opc oc1 dl) fstage e Hxa eq_refl Hhd Hns00) as Hxc.
  forward. forward. forward.
  rewrite HRn. unfold ds_inv_x.
  Exists {| w_smw := 0; w_k := k_stage k zdss_init; w_sv := sv; w_ipc := ipc; w_opc := opc; w_oc := oc1;
            w_dl := dl |}.
  unfold ds_LI_Px, ds_LI_L, ds_LI_S, ctx_rep3, ctx_body3, fgroup3, sgroup, frame_fields, frame_rest, sf_given.
  proj_simpl.
  cbn [k_stage c3_with_s sf_set_stage c3_s c3_fs c3_tabs c3_stable c3_dict c3_par c3_sp c3_set sf_stage sf_inBuff
       sf_inSize sf_inPos sf_outBuff sf_outSize sf_outStart sf_outEnd sf_lhSize sf_hostage sf_nfp sf_expOut sf_hbuf
       sf_over sf_ring sf_mem sf_held].
  rewrite <- Hfst, <- Hfe.
  entailer!.
  repeat match goal with |- _ /\ _ => split end.
  all: first [ exact Hxc
             | apply (read_end_inv' _ _ _ _ _ _ _ Hinv Hstage Hc)
             | (unfold loop_extra; cbn; intros Hx; discriminate)
             | entry_tac
             | (apply (read_end_exit _ _ _ _ _ _ _ Hinv Hstage Hc); rewrite Hfe; destruct (Hcpl Hc) as [_ ->];
                reflexivity)
             | (unfold zdss_init; rep_lia) | exact Hun ]. }
assert (Hnc: fp_complete (sv_fp sv) = false).
{ destruct (fp_complete (sv_fp sv)) eqn:Ec; auto. destruct (Hcpl eq_refl) as [Hs0 He0].
  exfalso. match goal with H: Int64.repr ns <> _ |- _ => apply H end.
  unfold ns. rewrite He0. destruct Hs0 as [-> | ->]; reflexivity. }
destruct (Hns Hnc (isz - ipc) ltac:(lia)) as (Hns1 & Hns2 & Hns3).
change (next_size fstage (bt_of (fs_bType (c3_fs k))) e (isz - ipc)) with ns in Hns1, Hns2, Hns3.
forward_if.
{ entailer!. destruct ib; try contradiction. simpl. clear. destruct (peq b b); [reflexivity | congruence]. }
{ (* decode directly from the input *)
  assert (Hge: ns <= isz - ipc).
  { match goal with H: typed_true tint _ |- _ =>
      rewrite sub_pp_tschar63 in H by (auto; lia); simpl in H; unfold typed_true in H; simpl in H end.
    destruct (Int64.ltu (Int64.repr (isz - ipc)) (Int64.repr ns)) eqn:El; [discriminate|].
    unfold Int64.ltu in El. rewrite !Int64.unsigned_repr in El by rep_lia.
    destruct (zlt (isz - ipc) ns); [discriminate|lia]. }
  pose proof (Hns2 Hge) as Hunit.
  eapply semax_pre with (P' := PROPx [] (LOCALx (temp _neededInSize (Vlong (Int64.repr ns)) ::
      ds_LI_L {| a_W := W; a_gv := gv; a_d := d; a_st := st; a_outp := outp; a_inp := inp; a_sho := sho;
                 a_shi := shi; a_shob := shob; a_obf := obf; a_osz := osz; a_opos := opos; a_oc := oc; a_shb := shb;
                 a_ibf := ibf; a_isz := isz; a_ipos := ipos; a_ibs := ibs; a_vop := vop |}
              (Build_lw 1 k sv ipc opc oc1 dl))
    (SEPx (ds_LI_S DENT TABS {| a_W := W; a_gv := gv; a_d := d; a_st := st; a_outp := outp; a_inp := inp; a_sho := sho;
                 a_shi := shi; a_shob := shob; a_obf := obf; a_osz := osz; a_opos := opos; a_oc := oc; a_shb := shb;
                 a_ibf := ibf; a_isz := isz; a_ipos := ipos; a_ibs := ibs; a_vop := vop |}
              (Build_lw 1 k sv ipc opc oc1 dl))))).
  { unfold ds_LI_S, ds_LI_L, ctx_rep3, ctx_body3, fgroup3, sgroup. rewrite frame_fields_split. proj_simpl.
    rewrite Hfst, Hfe. entailer!. }
  unfold abbreviate in POSTCONDITION; subst POSTCONDITION.
  unfold MORE_COMMANDS, abbreviate.
  eapply semax_seq with (Q := FF); [| apply semax_ff].
  unfold abbreviate in Delta; subst Delta.
  fold (rd_Delta [ZSTD_decompressContinueStream_spec3 DENT TABS; ERR_isError_spec;
                  ZSTD_nextSrcSizeToDecompressWithInputSize_spec]).
  fold (rd_Delta2 DENT TABS).
  destruct (dc_stable st) eqn:Est.
  - apply (rd_direct_st3 Espec DENT TABS BR _ (Build_lw 1 k sv ipc opc oc1 dl) _ ns M RT HT Ha Hstart Hinv
             eq_refl Hstage Hnc Hunit ltac:(lia) ltac:(simpl; lia) Est); [exact HRn | exact HRr].
  - assert (Hcb: lay_cbound (sv_fp sv) (sv_lay sv))
      by (eapply c_ring_cbound; rewrite ?Est in Hring; exact Hring).
    apply (rd_direct_bf3 Espec DENT TABS BR _ (Build_lw 1 k sv ipc opc oc1 dl) _ ns fstage e M RT HT Ha Hstart Hinv
             Hun eq_refl Hstage Hnc Hunit ltac:(lia) ltac:(simpl; lia) Est Hcb Hxa Hhd eq_refl);
      [exact HRn | exact HRr].
}
forward_if.
{ entailer!. apply tc_test_eq_same; auto;
  (eapply derives_trans; [| apply (wvp_buf W shb (Zlength ibs) (zbytes ibs) ib TT); auto; lia]; cancel). }
{ (* no more input *)
  assert (Hie: ipc = isz).
  { match goal with H: offset_val ipc ib = offset_val isz ib |- _ => rename H into Hpe end.
    destruct ib; try contradiction. unfold offset_val in Hpe.
    assert (E: Ptrofs.add i (Ptrofs.repr ipc) = Ptrofs.add i (Ptrofs.repr isz)) by congruence.
    apply (f_equal (fun x => Ptrofs.sub x i)) in E.
    rewrite !Ptrofs.sub_add_l, Ptrofs.sub_idem, !Ptrofs.add_zero_l in E.
    apply (f_equal Ptrofs.unsigned) in E. rewrite !Ptrofs.unsigned_repr in E by rep_lia. exact E. }
  assert (Hnz: ns <> 0).
  { intros E. match goal with H: Int64.repr ns <> _ |- _ => apply H end. rewrite E. reflexivity. }
  pose proof (rx_noin _ (Build_lw 1 k sv ipc opc oc1 dl) fstage e Hxa eq_refl Hhd Hnz Hie) as Hxc.
  forward. forward.
  rewrite HRn. unfold ds_inv_x.
  Exists {| w_smw := 0; w_k := k; w_sv := sv; w_ipc := ipc; w_opc := opc; w_oc := oc1; w_dl := dl |}.
  unfold ds_LI_Px, ds_LI_L, ds_LI_S, ctx_rep3, ctx_body3, fgroup3, sgroup, frame_fields, frame_rest. proj_simpl.
  rewrite <- Hfst, <- Hfe.
  entailer!. repeat match goal with |- _ /\ _ => split end.
  all: first [ exact Hxc | (unfold loop_extra; cbn; intros Hx; discriminate) | entry_tac
             | (apply read_noin_exit; auto) | exact Hun ]. }
assert (Hlt: isz - ipc < ns).
{ match goal with H: typed_false tint _ |- _ =>
    rewrite sub_pp_tschar63 in H by (auto; lia); simpl in H; unfold typed_false in H; simpl in H end.
  destruct (Int64.ltu (Int64.repr (isz - ipc)) (Int64.repr ns)) eqn:El; [|discriminate].
  apply Int64.ltu_inv in El. rewrite !Int64.unsigned_repr in El by rep_lia. lia. }
assert (Hne: ipc <> isz) by (intro; subst; congruence).
pose proof (rx_fall _ (Build_lw 1 k sv ipc opc oc1 dl) fstage e Hxa eq_refl Hhd Hlt Hne) as Hxc.
forward.
unfold load_pre.
Exists {| w_smw := 1; w_k := k_stage k zdss_load; w_sv := sv; w_ipc := ipc; w_opc := opc; w_oc := oc1;
          w_dl := dl |}.
unfold ds_LI_P, ds_LI_L, ds_LI_S, ctx_rep3, ctx_body3, fgroup3, sgroup, frame_fields, frame_rest, sf_given.
proj_simpl.
cbn [k_stage c3_with_s sf_set_stage c3_s c3_fs c3_tabs c3_stable c3_dict c3_par c3_sp c3_set sf_stage sf_inBuff
     sf_inSize sf_inPos sf_outBuff sf_outSize sf_outStart sf_outEnd sf_lhSize sf_hostage sf_nfp sf_expOut sf_hbuf
     sf_over sf_ring sf_mem sf_held].
rewrite <- Hfst, <- Hfe.
entailer!.
all: repeat match goal with |- _ /\ _ => split end.
all: first [ exact Hun | exact Hxc | (apply (read_load_inv _ _ _ _ _ _ _ Hinv Hstage Hnc); apply Hns3; lia) ].
Qed.

End CM_R3VMain_1.
