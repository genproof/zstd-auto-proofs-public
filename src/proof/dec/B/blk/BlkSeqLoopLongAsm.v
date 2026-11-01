(* The long loop's assembly: ZSTD_decompressSequencesLong_body against seqs_spec (fun _ => True) from the
   segment statements of BlkSeqLoopLongDefs (long_body_of_segs); BlkSeqLoopLong.v instantiates them with the
   segments' proofs. *)
Require Export Zstd.proof.dec.B.blk.BlkSeqLoopCommon.
Require Import Zstd.proof.dec.B.blk.BlkSeqLoopLongDefs Zstd.proof.dec.B.blk.BlkSeqLoopLongXD.
Local Open Scope logic.

(* la_pend from seqs_spec's PRE: hist_ptrs_ok, lit_pos, ext0_ok (dictend_ok_split) *)
Lemma la_pend_of (a: la) :
  hist_ptrs_ok (a_fs a) (a_o a) (a_x a) -> lit_pos (a_l a) (a_d a) (a_cap a) (a_bsm a) (a_n a) ->
  ext0_ok (a_W a) (a_fs a) (a_x a) -> la_pend a.
Proof.
  intros (Hps & Hvs & Hde) Hlp He0. split.
  - split; [exact Hps|]. split; [exact Hvs|].
    destruct (dictend_ok_split (a_W a) (a_fs a) (a_o a) (a_x a) Hde He0) as [Hne|Hw]; [left; exact Hne | right; exact Hw].
  - unfold lit_pos in Hlp. destruct (a_l a); auto; unfold LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *; lia.
Qed.

Lemma fr_app (l1 l2: list Prop) : fold_right and True (l1 ++ l2) = (fold_right and True l1 /\ fold_right and True l2).
Proof.
  induction l1 as [|P l1 IH]; simpl.
  - apply prop_ext; tauto.
  - rewrite IH. apply prop_ext; tauto.
Qed.

Lemma propx_LIP (a: la) (x: lfx) (w: lst) (l: list Prop) Q R :
  PROPx (LI_P a x w ++ l) (LOCALx Q (SEPx R)) = PROPx (LIP a x w :: l) (LOCALx Q (SEPx R)).
Proof. unfold PROPx, LIP. rewrite fr_app. reflexivity. Qed.

Lemma lip_bounds (a: la) (x: lfx) (w: lst) :
  LIP a x w -> 0 <= w_ie w <= w_id w /\ w_id w <= a_nb a /\ w_id w - w_ie w <= 8.
Proof. unfold LIP, LI_P. simpl. tauto. Qed.

Lemma adv_bounds (a: la) : 0 < a_nb a -> 1 <= a_adv a <= 8 /\ a_adv a <= a_nb a.
Proof. unfold a_adv. lia. Qed.

Lemma lip_pre (a: la) (x: lfx) (w: lst) (P: list Prop) Q R :
  LIP a x w -> PROPx P (LOCALx Q (SEPx R)) |-- PROPx (LI_P a x w) (LOCALx Q (SEPx R)).
Proof.
  intros H. unfold PROPx. apply andp_derives; [| apply derives_refl]. intros rho. simpl. apply prop_derives. intros _. exact H.
Qed.

Lemma prop_pre (P1 P2: list Prop) Q R :
  fold_right and True P2 -> PROPx P1 (LOCALx Q (SEPx R)) |-- PROPx P2 (LOCALx Q (SEPx R)).
Proof.
  intros H. unfold PROPx. apply andp_derives; [| apply derives_refl]. intros rho. simpl. apply prop_derives. intros _. exact H.
Qed.

Lemma lg_drop_props (P: list Prop) Q R : PROPx P (LOCALx Q (SEPx R)) |-- PROPx [] (LOCALx Q (SEPx R)).
Proof. apply prop_pre. exact I. Qed.

Lemma zbytes_byte_vals (l: list Z) : bytes_ok l -> Forall is_byte_val (zbytes l).
Proof.
  intros H. induction H as [|b l Hb Hl IH]; simpl; constructor; auto.
  exists b. split; [exact Hb | reflexivity].
Qed.

(* nbSeq = 0: the epilogue's precondition with nothing executed *)
Lemma xi_nb0 (a: la) (xc: list val) :
  la_ok a -> la_dok a -> xc_ok (a_l a) (a_lits a) xc -> xc = zbytes (a_lxb a) -> xl_lxb_ok a -> a_nb a = 0 ->
  fold_right and True (XI_P a xc 0 0 false (oa_c (a_o a)) (a_rep a)).
Proof.
  intros Ha Hdok Hxc Hxz Hlxb Hnb. pose proof (ex_def0 a Ha Hdok) as Hd0.
  pose proof (xl_aft_nb0 a (xl_ctx_of a Ha Hlxb) Hnb) as Haft.
  destruct Ha as (Ho & _ & Hl & _ & _ & _ & _ & _ & Hrep & _).
  destruct Ho as (_ & HN & _ & Hd & Hcap & _).
  destruct Hl as (Hbo & Hn & Hloc).
  unfold XI_P. cbn [fold_right].
  assert (Hsub0: sublist (a_d a) (a_d a + 0) (oa_c (a_o a)) = []) by (rewrite Z.add_0_r; apply sublist_nil).
  assert (Hlit: lit_intact a 0 false (oa_c (a_o a))).
  { unfold lit_intact. destruct (a_l a); auto. intros _. rewrite Z.add_0_r. apply Hloc. }
  split; [exact Hxc|]. split.
  { unfold ex_safe, a_E. split; [lia|]. split.
    { destruct (a_l a); unfold a_d, a_cap in *; lia. }
    split; [unfold a_n; pose proof (Zlength_nonneg (a_lits a)); lia|].
    split; [destruct (a_l a); auto; unfold a_n; lia|].
    split; [exact HN|]. split; [intros k _ _; reflexivity | intros Hb _ _; exact Hb]. }
  split.
  { exact Hd0. }
  split; [exact Hrep|]. split; [|exact (conj Hxz (conj Hlxb (conj Haft I)))].
  unfold XM, DMg. rewrite Hnb. cbn. intros seqs Hs. injection Hs as <-.
  split; [reflexivity|]. split; [reflexivity|].
  intros out' lits' rep2 He _ _ _. cbn in He. injection He as <- <- <-.
  split; [reflexivity|]. exists []. split; [reflexivity|]. split; [rewrite Hsub0; reflexivity|].
  split; [rewrite app_nil_r; reflexivity|]. split; [unfold a_n; rewrite ZtoNat_Zlength, firstn_all; reflexivity|]. exact Hlit.
Qed.

Lemma long_body_of_segs :
  TABS_INTRO -> TABS_ELIM -> TABS_BORROW -> DSTEP -> SEG_PRO -> SEG_INIT -> SEG_ADV -> SEG_MAIN ->
  SEG_END -> SEG_FIN -> SEG_REPS -> SEG_EPI ->
  GLOBALS_obligation ->
  semax_body Vprog LOOP_GB f_ZSTD_decompressSequencesLong_body (_ZSTD_decompressSequencesLong_body, seqs_spec (fun _ => True)).
Proof.
intros TI TE TB DS SPRO SINIT SADV SMAIN SEND SFIN SREPS SEPI HG.
start_function.
pose (a := mk_la gv p fs ox os fe rep l lits lxb nbSeq bsm W o i h v_litPtr v_sequences v_seqState v_sequence v_sequence__1).
assert (Ha: la_ok a) by (unfold la_ok; simpl; tauto).
assert (Hp: la_pend a) by (apply la_pend_of; assumption).
assert (Hdok: la_dok a) by (split; assumption).
match goal with |- semax _ _ ?c _ =>
  replace c with (fn_body f_ZSTD_decompressSequencesLong_body) by reflexivity end.
rewrite lg_body_eq.
change Delta with lg_Delta.
change POSTCONDITION with (lg_R a).
eapply semax_pre; [| apply (SPRO Espec a); [exact Ha | exact Hp | ]].
{ apply andp_left2. unfold L_pre, S_pre. apply derives_refl. }
intros xc Hxc Hxz Hlxb.
assert (Hnbr: 0 <= a_nb a <= LONGNBSEQ + 65535) by exact H5.
assert (H6a: a_nb a > 0 -> a_os a <> None) by (intro Hg; exact (proj1 (H6 Hg))).
assert (H0a: inwin_ok (a_i a)) by exact H0.
unfold LONGNBSEQ in Hnbr. clearbody a. clear H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14.
apply semax_seq with (EX K: Z, EX j: Z, EX sw: bool, EX c: list val, EX rep': Z * Z * Z,
                        XI a xc K j sw c (if a_nb a =? 0 then a_fe a else 1) rep').
2: { Intros K j sw c rep'. apply SEPI; auto. }
unfold L_ex, L_base, XI_S. cbn [app].
eapply semax_pre; [apply andp_left2, now_later|].
apply (semax_ifthenelse_PQR' _ (Vint (Int.repr (a_nb a)))); [reflexivity | entailer! | entailer! | | ].
2: {
  (* nbSeq = 0: straight to the epilogue *)
  Intros. match goal with H: typed_false _ _ |- _ => rename H into Hf | H: Int.repr _ = Int.zero |- _ => rename H into Hf end.
  assert (Hnb: a_nb a = 0).
  { simpl in Hf. apply (f_equal Int.unsigned) in Hf.
    rewrite Int.unsigned_repr in Hf by rep_lia. exact Hf. }
  unfold lg_Delta. abbreviate_semax. forward.
  unfold lg_R; cbn [RA_normal].
  Exists 0 0 false (oa_c (a_o a)) (a_rep a). rewrite Hnb. cbn [Z.eqb].
  unfold XI. eapply derives_trans; [| apply (prop_pre []), (xi_nb0 a xc Ha Hdok Hxc Hxz Hlxb Hnb)].
  unfold L_ex, L_base, XI_S. cbn [app]. entailer!. }
(* nbSeq > 0 *)
Intros. match goal with H: typed_true _ _ |- _ => rename H into Ht | H: Int.repr _ <> Int.zero |- _ => rename H into Ht end.
assert (Hnb: 0 < a_nb a).
{ simpl in Ht. destruct (Z.eq_dec (a_nb a) 0) as [E|E]; [|lia]. rewrite E in Ht. contradiction. }
destruct (a_os a) as [t|] eqn:Et; [| exfalso; exact (H6a ltac:(lia) eq_refl)].
sep_apply (TI (a_gv a) (a_p a) (a_ox a) t (a_fe a)). Intros tp.
destruct (inwin_bits (a_i a) H0a) as (sh1 & sh2 & Ri & Hr1 & Hr2 & Hiw).
pose (x := mk_lfx t tp sh1 sh2 Ri xc).
assert (Hx: lfx_ok a x) by (unfold lfx_ok; simpl x_t; simpl x_sh1; simpl x_sh2; simpl x_Ri; simpl x_xc; tauto).
assert (Hxx: lfx_x a x) by (split; [exact Hxz | exact Hlxb]).
eapply semax_pre; [| eapply (SINIT TE TB Espec a x); [exact HG | exact Ha | exact Hp | exact Hdok | exact Hx | exact Hxx | exact Hnb | reflexivity | ]].
{ rewrite Hiw. unfold S_init, S_fix, L_ex, L_base. cbn [app]. subst x. cbn [x_t x_tp x_sh1 x_sh2 x_Ri x_xc]. entailer!. }
intros w Hw Hadv Hid0.
apply seq_assoc1. unfold lg_Delta. abbreviate_semax. forward. change Delta with lg_Delta.
(* the prepare loop *)
forward_loop (EX w': lst, PROP (LIP a x w'; adv_ph a w'; w_id w' <= a_adv a)
                          (LOCALx (LI_L a w' (w_id w')) (SEPx (LI_S a x w'))))
  continue: (EX w': lst, PROP (LIP a x w'; adv_ph a w'; 1 <= w_id w' <= a_adv a)
                          (LOCALx (LI_L a w' (w_id w' - 1)) (SEPx (LI_S a x w'))))
  break: (EX w': lst, PROP (LIP a x w'; adv_ph a w'; w_id w' = a_adv a)
                          (LOCALx (LI_L a w' (a_adv a)) (SEPx (LI_S a x w')))).
{ Exists w. unfold LI_L, L_seq, L_ex, L_base. cbn [app]. rewrite Hid0.
  pose proof Hadv as (_ & HK & _ & Hsw & _). rewrite HK, Hsw. entailer!.
  all: try exact Hadv; try (unfold a_adv; lia). }
{ Intros w'.
  match goal with H: LIP a x w' |- _ => rename H into Hw' end.
  match goal with H: adv_ph a w' |- _ => rename H into Hadv' end.
  match goal with H: w_id w' <= a_adv a |- _ => rename H into Hle end.
  unfold LI_L, L_seq, L_ex, L_base. cbn [app].
  forward_if.
  2: { forward. Exists w'. unfold LI_L, L_seq, L_ex, L_base. cbn [app].
       pose proof (lip_bounds _ _ _ Hw'). pose proof (adv_bounds a Hnb).
       match goal with H: Int.signed _ >= Int.signed _ |- _ => rewrite !Int.signed_repr in H by rep_lia end.
       assert (E: w_id w' = a_adv a) by lia. rewrite E. entailer!. }
  pose proof (lip_bounds _ _ _ Hw'). pose proof (adv_bounds a Hnb).
  match goal with H: Int.signed _ < Int.signed _ |- _ => rewrite !Int.signed_repr in H by rep_lia end.
  eapply semax_pre; [| eapply semax_post; [ | | | | apply (SADV TB DS Espec a x w' HG Ha Hp Hx Hxx Hw' Hadv' ltac:(lia))]].
  { eapply derives_trans; [| apply (lip_pre _ _ _ []), Hw']. unfold LI_L, L_seq, L_ex, L_base. cbn [app].
    entailer!. }
  all: unfold POSTCONDITION, abbreviate; cbn [RA_normal RA_break RA_continue RA_return normal_ret_assert loop1_ret_assert].
  { Intros w''. rewrite propx_LIP. Intros.
    match goal with H: w_id w'' = _ |- _ => rename H into Hid'' end.
    Exists w''. replace (w_id w'' - 1) with (w_id w') by lia.
    apply andp_left2. apply prop_pre. cbn [fold_right]. refine (conj _ (conj _ (conj _ I))); [assumption | assumption | lia]. }
  all: intros; apply andp_left2; apply FF_left. }
{ (* seqNb++ *)
  Intros w'. pose proof (adv_bounds a Hnb). unfold LI_L, L_seq, L_ex, L_base. cbn [app]. forward.
  all: try solve [entailer!].
  Exists w'. unfold LI_L, L_seq, L_ex, L_base. cbn [app].
  replace (w_id w' - 1 + 1) with (w_id w') by lia. entailer!.
  do 2 f_equal; lia. }
(* after the prepare loop *)
Intros w1.
match goal with H: LIP a x w1 |- _ => rename H into Hw1 end.
match goal with H: adv_ph a w1 |- _ => rename H into Hadv1 end.
match goal with H: w_id w1 = a_adv a |- _ => rename H into Hid1 end.
pose proof (adv_bounds a Hnb) as Hab.
(* the main loop *)
forward_loop (EX w': lst, PROP (LIP a x w'; main_ph a w'; a_adv a <= w_id w' <= a_nb a)
                          (LOCALx (LI_L a w' (w_id w')) (SEPx (LI_S a x w'))))
  continue: (EX w': lst, PROP (LIP a x w'; main_ph a w'; a_adv a + 1 <= w_id w' <= a_nb a)
                          (LOCALx (LI_L a w' (w_id w' - 1)) (SEPx (LI_S a x w'))))
  break: (EX w': lst, PROP (LIP a x w'; main_ph a w'; w_id w' = a_nb a)
                          (LOCALx (LI_L a w' (a_nb a)) (SEPx (LI_S a x w')))).
{ Exists w1. unfold LI_L, L_seq, L_ex, L_base. cbn [app]. rewrite Hid1. entailer!.
  all: unfold main_ph; pose proof Hadv1 as (? & _); lia. }
{ Intros w'.
  match goal with H: LIP a x w' |- _ => rename H into Hw' end.
  match goal with H: main_ph a w' |- _ => rename H into Hm' end.
  match goal with H: a_adv a <= w_id w' <= a_nb a |- _ => rename H into Hle end.
  pose proof (lip_bounds _ _ _ Hw').
  unfold LI_L, L_seq, L_ex, L_base. cbn [app].
  forward_if.
  2: { forward. Exists w'. unfold LI_L, L_seq, L_ex, L_base. cbn [app].
       try match goal with H: Int.signed _ >= Int.signed _ |- _ => rewrite !Int.signed_repr in H by rep_lia end.
       assert (E: w_id w' = a_nb a) by lia. rewrite E. entailer!. }
  try match goal with H: Int.signed _ < Int.signed _ |- _ => rewrite !Int.signed_repr in H by rep_lia end.
  eapply semax_pre; [| eapply semax_post; [ | | | |
    eapply (SMAIN TE TB DS Espec a x w'
      (Build_ret_assert
         (EX w'': lst, PROPx (LI_P a x w'' ++ [main_ph a w''; w_id w'' = w_id w' + 1])
                         (LOCALx (LI_L a w'' (w_id w')) (SEPx (LI_S a x w''))))
         FF FF (RA_return (lg_R a))));
      [exact HG | exact Ha | exact Hp | exact Hx | exact Hxx | exact Hw' | exact Hm' | lia | reflexivity | reflexivity]]].
  { eapply derives_trans; [| apply (lip_pre _ _ _ []), Hw']. unfold LI, LI_L, L_seq, L_ex, L_base. cbn [app].
    entailer!. }
  all: unfold POSTCONDITION, abbreviate; cbn [RA_normal RA_break RA_continue RA_return normal_ret_assert loop1_ret_assert overridePost].
  { Intros w''. rewrite propx_LIP. Intros.
    match goal with H: w_id w'' = _ |- _ => rename H into Hid'' end.
    Exists w''. replace (w_id w'' - 1) with (w_id w') by lia.
    apply andp_left2. apply prop_pre. cbn [fold_right]. refine (conj _ (conj _ (conj _ I))); [assumption | assumption | lia]. }
  1, 2: apply andp_left2; apply FF_left.
  intros; apply andp_left2; apply derives_refl. }
{ (* seqNb++ *)
  Intros w'. unfold LI_L, L_seq, L_ex, L_base. cbn [app]. forward.
  all: try solve [entailer!].
  Exists w'. unfold LI_L, L_seq, L_ex, L_base. cbn [app].
  replace (w_id w' - 1 + 1) with (w_id w') by lia. entailer!.
  do 2 f_equal; lia. }
(* after the main loop *)
Intros w2.
match goal with H: LIP a x w2 |- _ => rename H into Hw2 end.
match goal with H: main_ph a w2 |- _ => rename H into Hm2 end.
match goal with H: w_id w2 = a_nb a |- _ => rename H into Hid2 end.
pose proof (lip_bounds _ _ _ Hw2) as Hb2.
(* BIT_endOfDStream *)
apply semax_seq with (PROPx (LI_P a x w2 ++ [w_pos w2 = 0]) (LOCALx (LI_L a w2 (a_nb a)) (SEPx (LI_S a x w2)))).
{ eapply semax_pre; [| eapply semax_post; [ | | | | apply (SEND TE Espec a x w2 HG Ha Hp Hx Hxx Hw2 Hm2 Hid2 Hnb)]].
  { eapply derives_trans; [| apply (lip_pre _ _ _ []), Hw2]. unfold LI, LI_L, L_seq, L_ex, L_base. cbn [app].
    entailer!. }
  all: unfold POSTCONDITION, abbreviate; cbn [RA_normal RA_break RA_continue RA_return overridePost lg_R frame_ret_assert function_body_ret_assert].
  all: intros; apply andp_left2; apply derives_refl. }
(* seqNb -= seqAdvance *)
rewrite propx_LIP. Intros. match goal with H: w_pos w2 = 0 |- _ => rename H into Hpos2 end.
unfold LI_L, L_seq, L_ex, L_base. cbn [app].
abbreviate_semax. forward.
all: try solve [entailer!].
(* the queue loop *)
forward_loop (EX w': lst, PROP (LIP a x w'; fin_ph a w'; a_nb a - a_adv a <= w_ie w' <= a_nb a)
                          (LOCALx (LI_L a w' (w_ie w')) (SEPx (LI_S a x w'))))
  continue: (EX w': lst, PROP (LIP a x w'; fin_ph a w'; a_nb a - a_adv a + 1 <= w_ie w' <= a_nb a)
                          (LOCALx (LI_L a w' (w_ie w' - 1)) (SEPx (LI_S a x w'))))
  break: (EX w': lst, PROP (LIP a x w'; fin_ph a w'; w_ie w' = a_nb a)
                          (LOCALx (LI_L a w' (a_nb a)) (SEPx (LI_S a x w')))).
{ Exists w2. unfold LI_L, L_seq, L_ex, L_base. cbn [app].
  assert (Eie: w_ie w2 = a_nb a - a_adv a) by (unfold main_ph in Hm2; lia).
  rewrite Eie. entailer!.
  all: try (unfold fin_ph; split; lia).
  all: try lia. }
{ Intros w'.
  match goal with H: LIP a x w' |- _ => rename H into Hw' end.
  match goal with H: fin_ph a w' |- _ => rename H into Hf' end.
  match goal with H: a_nb a - a_adv a <= w_ie w' <= a_nb a |- _ => rename H into Hle end.
  pose proof (lip_bounds _ _ _ Hw').
  unfold LI_L, L_seq, L_ex, L_base. cbn [app].
  forward_if.
  2: { forward. Exists w'. unfold LI_L, L_seq, L_ex, L_base. cbn [app].
       try match goal with H: Int.signed _ >= Int.signed _ |- _ => rewrite !Int.signed_repr in H by rep_lia end.
       assert (E: w_ie w' = a_nb a) by lia. rewrite E. entailer!. }
  try match goal with H: Int.signed _ < Int.signed _ |- _ => rewrite !Int.signed_repr in H by rep_lia end.
  eapply semax_pre; [| eapply semax_post; [ | | | |
    eapply (SFIN TE Espec a x w'
      (Build_ret_assert
         (EX w'': lst, PROPx (LI_P a x w'' ++ [fin_ph a w''; w_ie w'' = w_ie w' + 1])
                         (LOCALx (LI_L a w'' (w_ie w')) (SEPx (LI_S a x w''))))
         FF FF (RA_return (lg_R a))));
      [exact HG | exact Ha | exact Hp | exact Hx | exact Hxx | exact Hw' | exact Hf' | lia | reflexivity | reflexivity]]].
  { eapply derives_trans; [| apply (lip_pre _ _ _ []), Hw']. unfold LI, LI_L, L_seq, L_ex, L_base. cbn [app].
    entailer!. }
  all: unfold POSTCONDITION, abbreviate; cbn [RA_normal RA_break RA_continue RA_return normal_ret_assert loop1_ret_assert overridePost].
  { Intros w''. rewrite propx_LIP. Intros.
    match goal with H: w_ie w'' = _ |- _ => rename H into Hie'' end.
    Exists w''. replace (w_ie w'' - 1) with (w_ie w') by lia.
    apply andp_left2. apply prop_pre. cbn [fold_right]. refine (conj _ (conj _ (conj _ I))); [assumption | assumption | lia]. }
  1, 2: apply andp_left2; apply FF_left.
  intros; apply andp_left2; apply derives_refl. }
{ (* seqNb++ *)
  Intros w'. unfold LI_L, L_seq, L_ex, L_base. cbn [app]. forward.
  all: try solve [entailer!].
  Exists w'. unfold LI_L, L_seq, L_ex, L_base. cbn [app].
  replace (w_ie w' - 1 + 1) with (w_ie w') by lia. entailer!.
  do 2 f_equal; lia. }
(* save the repeat offsets *)
Intros w3.
match goal with H: LIP a x w3 |- _ => rename H into Hw3 end.
match goal with H: fin_ph a w3 |- _ => rename H into Hf3 end.
match goal with H: w_ie w3 = a_nb a |- _ => rename H into Hie3 end.
eapply semax_pre; [| eapply semax_post; [ | | | | apply (SREPS TE Espec a x w3 HG Ha Hp Hx Hxx Hw3 Hf3 Hie3 Hnb)]].
{ eapply derives_trans; [| apply (lip_pre _ _ _ []), Hw3]. unfold LI, LI_L, L_seq, L_ex, L_base. cbn [app].
  entailer!. }
all: unfold POSTCONDITION, abbreviate; cbn [RA_normal RA_break RA_continue RA_return normal_ret_assert overridePost].
{ Exists (w_K w3) (w_j w3) (w_sw w3) (w_c w3) (rep_trunc (w_drep w3)).
  replace (a_nb a =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  apply andp_left2; apply derives_refl. }
1, 2: apply andp_left2; apply FF_left.
intros; apply andp_left2; apply FF_left.
Qed.

