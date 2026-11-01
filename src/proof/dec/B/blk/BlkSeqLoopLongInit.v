(* The long loop (ZSTD_decompressSequencesLong_body, cut in segments by BlkSeqLoopLongDefs): lg_init (sequence
   state, BIT_initDStream, the three initFseState); the exact model: its error return fails on every choice
   (BlkSeqLoopLongXD.xl_init_err), its success starts the invariant xl_inv (xl_init). *)
Require Import Zstd.proof.dec.B.blk.BlkSeqLoopLongDefs Zstd.proof.dec.B.blk.BlkSeqLoopLongXD.
Local Open Scope logic.

Lemma li_repr_eqm: forall x y, x mod 2^64 = y mod 2^64 -> Int64.repr x = Int64.repr y.
Proof.
  intros x y H. apply Int64.eqm_samerepr. unfold Int64.eqm. change Int64.modulus with (2^64).
  apply Zbits.eqmod_trans with (x mod 2^64); [apply Zbits.eqmod_mod; lia|].
  rewrite H. apply Zbits.eqmod_sym, Zbits.eqmod_mod; lia.
Qed.

(* op - prefixStart, inside one object *)
Lemma li_sub_pp: forall p a c, isptr p ->
  force_val (sem_binary_operation' Osub (tptr tuchar) (tptr tuchar) (offset_val a p) (offset_val c p)) =
  Vlong (Int64.repr (a - c)).
Proof.
  intros. destruct p; try contradiction. unfold sem_binary_operation', sem_sub, sem_sub_pp. simpl. rewrite if_true by auto. simpl.
  rewrite (Ptrofs.add_commut i (Ptrofs.repr a)), (Ptrofs.add_commut i (Ptrofs.repr c)).
  rewrite Ptrofs.sub_shifted. change (Ptrofs.repr 1) with Ptrofs.one. rewrite Ptrofs.divs_one by reflexivity.
  unfold Vptrofs. simpl. f_equal. unfold Ptrofs.to_int64. apply li_repr_eqm.
  unfold Ptrofs.sub. rewrite !Ptrofs.unsigned_repr_eq. change Ptrofs.modulus with (2^64).
  rewrite Zmod_mod. rewrite <- Zminus_mod. reflexivity.
Qed.

(* the seqState_t local, split into its fields *)
Lemma li_ss_split (v: val) :
  data_at_ Tsh t_seqstate v =
  data_at_ Tsh t_bitd (field_address t_seqstate (DOT _DStream) v) *
  data_at_ Tsh t_fsestate (field_address t_seqstate (DOT _stateLL) v) *
  data_at_ Tsh t_fsestate (field_address t_seqstate (DOT _stateOffb) v) *
  data_at_ Tsh t_fsestate (field_address t_seqstate (DOT _stateML) v) *
  field_at_ Tsh t_seqstate (DOT _prevOffset) v.
Proof.
  unfold t_seqstate. unfold_data_at (data_at_ Tsh (Tstruct ___gp_seqState_t noattr) v).
  rewrite !field_at_data_at. rewrite <- !sepcon_assoc. unfold field_at_. rewrite field_at_data_at. reflexivity.
Qed.

(* TABS_BORROW on the unfolded tabs_seq_tp at fseEntropy 1 *)
Lemma li_borrow (HTB: TABS_BORROW) (HG: GLOBALS_obligation) (gv: globals) (p: val) (ox: option ddx)
    (t1 t2 t3: fse_table) (p1 p2 p3: val) :
  field_at Ews t_dctx (DOT _fseEntropy) (Vint (Int.repr 1)) p *
  seq_where_tp gv p ox KLL t1 p1 * seq_where_tp gv p ox KOF t2 p2 * seq_where_tp gv p ox KML t3 p3 *
  dent_of dent_def gv ox * zstd_globals gv |--
  EX sht: (share * share * share)%type, EX fm: (Z * Z * Z)%type, EX R: mpred,
    !! (seqtabs_sh_ok sht /\
        forall fe': Z,
          field_at Ews t_dctx (DOT _fseEntropy) (Vint (Int.repr fe')) p * seq_ptrs p (p1, p2, p3) *
          seqtabs_at sht (t1, t2, t3) fm (p1, p2, p3) * R
          |-- tabs_seq_tp gv p ox (t1, t2, t3) fe' (p1, p2, p3) * dent_of dent_def gv ox * zstd_globals gv) &&
    (field_at Ews t_dctx (DOT _fseEntropy) (Vint (Int.repr 1)) p * seq_ptrs p (p1, p2, p3) *
     seqtabs_at sht (t1, t2, t3) fm (p1, p2, p3) * R).
Proof. exact (HTB HG gv p ox (t1, t2, t3) 1 (p1, p2, p3)). Qed.

Lemma li_tab_isptr (sh: share) (k: seqkind) (t: fse_table) (fm: Z) (p: val) :
  seqtab_at_fm sh k t fm p |-- !! isptr p.
Proof.
  unfold seqtab_at_fm. Intros. rewrite (data_at_isptr sh t_seqhdr). Intros. apply prop_right. auto.
Qed.

(* the stream as its own bit source (offset 0) *)
Lemma li_bsrc (s: list Z) (st: val) : isptr st -> bit_src_ok s st st s 0.
Proof.
  intros Hp. unfold bit_src_ok. rewrite isptr_offset_val_zero by exact Hp.
  pose proof (Zlength_nonneg s). split; [reflexivity|]. split; [lia|]. split; [lia|].
  rewrite Z.add_0_l. apply sublist_same; lia.
Qed.

(* bits consumed after BIT_initDStream: at most 64 *)
Lemma li_bcons0 (s: list Z) :
  bytes_ok s -> bs_wf s = true -> 0 <= bcons (bs_total s) (8 * Z.max 0 (Zlength s - 8)) <= 64.
Proof.
  intros Hb Hwf. destruct (lim_init s Hb Hwf) as (H0 & H8 & H64 & Hr).
  assert (Ht: 0 <= bs_total s).
  { unfold bs_wf in Hwf. apply andb_prop in Hwf as [Hz _]. apply negb_true_iff, Z.eqb_neq in Hz.
    unfold bs_total. rewrite <- Zlength_correct. pose proof (Zlength_nonneg s).
    pose proof (Z.log2_nonneg (last s 0)). unfold highbit. lia. }
  unfold bcons. destruct Hr as [Hr | Hr]; lia.
Qed.

(* one read of nb bits and a reload consume at most nb more bits *)
Lemma li_bcons_step (pos lo nb: Z) :
  0 <= lo -> pos - nb <= lo + 64 ->
  bcons (pos - nb) (snd (bs_reload (pos - nb) lo)) <= bcons pos lo + nb.
Proof.
  intros H0 H1. pose proof (bs_reload_lo (pos - nb) lo H0 H1). unfold bcons. lia.
Qed.

Lemma li_rep_inv (sh: share) (gv: globals) (s: list Z) (st: val) (pos lo: Z) (p: val) :
  BIT_DStream_rep sh gv s st pos lo p |-- !! (0 <= lo /\ lo mod 8 = 0 /\ pos <= lo + 64).
Proof.
  unfold BIT_DStream_rep, bit_inv. Intros ptr lim. apply prop_right. tauto.
Qed.

(* decode_seqs k returns k sequences *)
Lemma li_decode_len (tLL tOF tML: fse_table) (V: list Z) (k: nat) :
  forall a b c pos l p, decode_seqs tLL tOF tML V k a b c pos = Some (l, p) -> length l = k.
Proof.
  induction k as [|k IH]; intros a b c pos l p H; cbn [decode_seqs] in H.
  - injection H as <- _. reflexivity.
  - repeat match type of H with
      | match ?x with None => _ | Some _ => _ end = _ =>
          destruct x as [[? ?]|] eqn:?; [cbv beta iota in H | discriminate]
      end.
    destruct k as [|k'].
    + injection H as <- _. reflexivity.
    + repeat match type of H with
        | match ?x with None => _ | Some _ => _ end = _ =>
            destruct x as [[? ?]|] eqn:?; [cbv beta iota in H | discriminate]
        | match ?x with Some _ => _ | None => _ end = _ =>
            destruct x as [[? ?]|] eqn:?; [cbv beta iota in H | discriminate]
        end.
      injection H as <- _. cbn [length]. f_equal. eapply IH. eassumption.
Qed.

Lemma li_zbytes_byte (l: list Z) : bytes_ok l -> Forall is_byte_val (zbytes l).
Proof.
  intros H. induction H as [|b l Hb Hl IH]; constructor; auto. exists b. split; [exact Hb | reflexivity].
Qed.

(* the executor's state at the start *)
Lemma li_ex_safe (a: la) :
  outarr_ok (a_o a) -> lits_at (a_l a) (oa_c (a_o a)) (oa_d (a_o a)) (oa_cap (a_o a)) (a_i a) (a_lits a) ->
  0 < oa_cap (a_o a) -> ex_safe a 0 0 false (oa_c (a_o a)).
Proof.
  intros (Hw & Hlen & HN & Hd & Hc & Hdc) (Hb & Hnr & Hl) Hcap.
  pose proof (Zlength_nonneg (a_lits a)).
  unfold ex_safe, a_E, a_n, a_d, a_cap in *.
  destruct (a_l a) as [off| |lb|lb]; cbv beta iota in *;
    (split; [lia|]); (split; [lia|]); (split; [lia|]);
    (split; [first [reflexivity | lia] |]); (split; [lia|]); (split; [intros ? ? ?; reflexivity|]);
    intros Hcb _ _; exact Hcb.
Qed.

(* no well-formed stream: the model fails *)
Lemma li_model_none (t: fse_table * fse_table * fse_table) (s: list Z) (nb: Z) (rep: Z * Z * Z)
    (hist out lits: list Z) (w: Z) :
  bs_wf s = false -> nb <> 0 -> seqs_model (Some t) s nb rep hist out lits w = None.
Proof.
  intros Hwf Hnb. destruct t as [[tLL tOF] tML]. unfold seqs_model.
  rewrite (proj2 (Z.eqb_neq nb 0) Hnb). unfold decode_seq_stream.
  assert (Hok: bs_okb s = false).
  { unfold bs_wf in Hwf. unfold bs_okb.
    apply andb_false_iff in Hwf as [Hz | Hl].
    - apply negb_false_iff, Z.eqb_eq in Hz. rewrite Zlength_correct in Hz.
      assert (length s = 0%nat) as -> by lia. rewrite andb_false_r. reflexivity.
    - rewrite Hl, andb_false_r. reflexivity. }
  rewrite Hok. reflexivity.
Qed.

(* TABS_ELIM on the unfolded tabs_seq_tp *)
Lemma li_elim (HTE: TABS_ELIM) (gv: globals) (p: val) (ox: option ddx) (t1 t2 t3: fse_table) (p1 p2 p3: val)
    (fe: Z) :
  field_at Ews t_dctx (DOT _fseEntropy) (Vint (Int.repr fe)) p *
  seq_where_tp gv p ox KLL t1 p1 * seq_where_tp gv p ox KOF t2 p2 * seq_where_tp gv p ox KML t3 p3 |--
  tabs_seq gv p ox (Some (t1, t2, t3)) fe.
Proof. exact (HTE gv p ox (t1, t2, t3) fe (p1, p2, p3)). Qed.

Lemma lit_extra_bytes_intro (p: val) (xc: list val) :
  byte_cells xc -> field_at Ews t_dctx (DOT _litExtraBuffer) xc p |-- lit_extra_bytes p.
Proof. intros Hx. unfold lit_extra_bytes. Exists xc. entailer!. Qed.

(* the literal fields back as scratch *)
Lemma li_lit_scratch (a: la) (xc: list val) (sw: bool) :
  byte_cells xc -> lit_now a xc sw |-- lit_scratch (a_p a).
Proof.
  intros Hx. unfold lit_now, lit_fix, lit_scratch. rewrite <- litextra_data_at.
  sep_apply (lit_extra_bytes_intro (a_p a) xc Hx).
  destruct (a_l a);
    try sep_apply (field_at_field_at_ Ews t_dctx (DOT _litPtr));
    try sep_apply (field_at_field_at_ Ews t_dctx (DOT _litSize));
    try sep_apply (field_at_field_at_ Ews t_dctx (DOT _litBuffer));
    try sep_apply (field_at_field_at_ Ews t_dctx (DOT _litBufferEnd));
    try sep_apply (field_at_field_at_ Ews t_dctx (DOT _litBufferLocation));
    try sep_apply (field_at_field_at_ Ews t_dctx (DOT _litExtraBuffer));
    cancel.
Qed.

(* the literal fields back as scratch, litExtraBuffer still holding lxb (la_post's lit_scratch_x) *)
Lemma li_lit_scratch_x (a: la) (sw: bool) :
  Zlength (a_lxb a) = LITEXTRA_N /\ bytes_ok (a_lxb a) ->
  lit_now a (zbytes (a_lxb a)) sw |-- lit_scratch_x (a_p a) (a_lxb a).
Proof.
  intros Hx. unfold lit_now, lit_fix, lit_scratch_x, lit_extra_at. rewrite <- litextra_data_at.
  destruct (a_l a);
    try sep_apply (field_at_field_at_ Ews t_dctx (DOT _litPtr));
    try sep_apply (field_at_field_at_ Ews t_dctx (DOT _litSize));
    try sep_apply (field_at_field_at_ Ews t_dctx (DOT _litBuffer));
    try sep_apply (field_at_field_at_ Ews t_dctx (DOT _litBufferEnd));
    try sep_apply (field_at_field_at_ Ews t_dctx (DOT _litBufferLocation));
    entailer!; apply Hx.
Qed.

(* do { } while (0) with an empty body *)
Ltac li_dw0 :=
  match goal with |- semax _ ?P _ _ =>
    forward_loop P break: P; [apply ENTAIL_refl | forward; apply ENTAIL_refl | ]
  end.

(* do { if (0) ...; } while (0) *)
Ltac li_dw0if :=
  match goal with |- semax _ ?P _ _ =>
    forward_loop P break: P;
    [ apply ENTAIL_refl
    | forward_if P;
      [ exfalso; match goal with H: Int.repr 0 <> Int.zero |- _ => apply H; reflexivity end
      | forward; try apply ENTAIL_refl
      | forward; try apply ENTAIL_refl ]
    | ]
  end.

Lemma lg_init_ok : SEG_INIT.
Proof.
  intros HTE HTB Espec a x REST R HG Hla Hpend Hdok Hlfx Hlfxx Hnb HR HK.
  unfold lg_Delta.
  destruct R as [Rn Rb Rc Rr].
  assert (HR': Rr = RA_return (lg_R a)) by exact HR. clear HR. rename HR' into HR.
  pose proof Hla as (Hoa & Hiw & Hlits & Hbsm & Hn & Hnbr & Hnb' & Hso & Hrep & Hfe & Hc0 & Hlay).
  destruct (Hnb' ltac:(lia)) as [_ Hcap].
  specialize (Hlay Hcap).
  pose proof Hlfx as (Hos & Hsh1 & Hsh2 & Heq & Hxc).
  unfold lg_init, S_init, S_fix, L_ex, L_base. cbn [app].
  pose proof (ex_def0 a Hla Hdok) as Hdef0.
  pose proof (xl_ctx_of a Hla (proj2 Hlfxx)) as Hxctx.
  clear Hla Hnb'.
  assert (Hnbr8: a_nb a <= Int.max_signed) by (unfold LONGNBSEQ in Hnbr; rep_lia).
  forward_if (temp _t'3 (Vint (Int.repr (a_adv a)))).
  { forward. entailer!. unfold a_adv. f_equal. f_equal. lia. }
  { forward. entailer!. unfold a_adv. f_equal. f_equal. lia. }
  forward.
  destruct Hlay as (Hps & Hpfx & Hvs & Hel & Hx).
  rewrite Hpfx.
  assert_PROP (isptr (a_ob a)) as Hob by entailer!.
  forward.
  { entailer!. unfold a_ob in *. destruct (oa_base (a_o a)); try contradiction. apply prop_right. cbn. destruct (peq b b); [reflexivity|congruence]. }
  unfold a_ob at 1. rewrite (li_sub_pp _ _ _ Hob). simpl force_val.
  destruct x as [t tp sh1 sh2 Ri xc]; cbn [x_t x_tp x_sh1 x_sh2 x_Ri x_xc] in *.
  destruct t as [[tLL tOF] tML], tp as [[pLL pOF] pML].
  unfold tabs_seq_tp at 1. Intros.
  forward.
  rewrite (li_ss_split (a_vss a)). Intros.
  destruct (a_rep a) as [[r1 r2] r3] eqn:Erep.
  pose proof Hrep as (Hr1 & Hr2 & Hr3).
  match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?S))) _ _ =>
    match S with context C [field_at_ Tsh t_seqstate (DOT _prevOffset) (a_vss a)] =>
      let Inv := constr:(fun k: Z => ltac:(
         let S' := context C [field_at Tsh t_seqstate (DOT _prevOffset)
             (map (fun r => Vlong (Int64.repr r)) (sublist 0 k [r1; r2; r3]) ++ Zrepeat Vundef (3 - k)) (a_vss a)] in
         exact (PROPx [] (LOCALx Q (SEPx S'))))) in
      forward_for_simple_bound 3 (EX k: Z, Inv k)%assert
    end end.
  - entailer!. unfold field_at_. apply derives_refl.
  - assert (Hz: forall d, @Znth val d i (rep_vals (r1, r2, r3)) = Vint (Int.repr (Znth i [r1; r2; r3]))).
    { intros d. assert (i = 0 \/ i = 1 \/ i = 2) as [ -> | [ -> | -> ] ] by lia; reflexivity. }
    forward.
    { rewrite Hz. entailer!. }
    forward.
    assert (Hz2: forall d, @Znth val d i [Vint (Int.repr r1); Vint (Int.repr r2); Vint (Int.repr r3)] =
                           Vint (Int.repr (Znth i [r1; r2; r3]))) by exact Hz.
    rewrite ?Hz, ?Hz2.
    assert (Hl: upd_Znth i
       (map (fun r : Z => Vlong (Int64.repr r)) (sublist 0 i [r1; r2; r3]) ++ Zrepeat Vundef (3 - i))
       (force_val (sem_cast_i2l Unsigned (Vint (Int.repr (Znth i [r1; r2; r3]))))) =
       map (fun r : Z => Vlong (Int64.repr r)) (sublist 0 (i + 1) [r1; r2; r3]) ++
       Zrepeat Vundef (3 - (i + 1))).
    { assert (i = 0 \/ i = 1 \/ i = 2) as [ -> | [ -> | -> ] ] by lia; cbn;
        rewrite Int.unsigned_repr by rep_lia; reflexivity. }
    rewrite Hl. entailer!.
  - change (map (fun r : Z => Vlong (Int64.repr r)) (sublist 0 3 [r1; r2; r3]) ++ Zrepeat Vundef (3 - 3))
      with (rep64_vals (r1, r2, r3)).
    pose proof Hiw as (Hiw1 & Hiw2 & Hiw3 & Hiw4 & Hiw5 & Hiw6 & Hiw7 & Hiw8).
    assert (Hsub: sublist 0 (0 + Zlength (iw_s (a_i a))) (iw_s (a_i a)) = iw_s (a_i a))
      by (rewrite Z.add_0_l; apply sublist_same; lia).
    assert_PROP (isptr (a_start a)) as Hst by (unfold bit_src; entailer!).
    destruct (bs_wf (iw_s (a_i a))) eqn:Ewf.
    + match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?S))) _ _ =>
        match S with context C [data_at_ Tsh t_bitd (field_address t_seqstate (DOT _DStream) (a_vss a))] =>
          let S' := context C [BIT_DStream_rep Tsh (a_gv a) (iw_s (a_i a)) (a_start a) (bs_total (iw_s (a_i a)))
                  (8 * Z.max 0 (Zlength (iw_s (a_i a)) - 8)) (field_address t_seqstate (DOT _DStream) (a_vss a))] in
          forward_loop (PROPx [] (LOCALx Q (SEPx S))) continue: (PROPx [] (LOCALx Q (SEPx S')))
            break: (PROPx [] (LOCALx Q (SEPx S')))
        end end.
      * entailer!.
      * forward_call (Tsh, field_address t_seqstate (DOT _DStream) (a_vss a), sh2, a_start a, iw_s (a_i a), 0,
          Zlength (iw_s (a_i a)), a_gv a).
        { rewrite isptr_offset_val_zero by exact Hst. entailer!.
          unfold field_address. rewrite if_true by auto with field_compatible. reflexivity. }
        rewrite Hsub, Ewf. Intros r. subst r.
        assert (Hn32: 0 <= Zlength (iw_s (a_i a)) <= 2 ^ 63 - 1) by (pose proof (Zlength_nonneg (iw_s (a_i a))); lia).
        forward_call (Zlength (iw_s (a_i a))).
        assert (Hne: is_error_code (Zlength (iw_s (a_i a))) = false)
          by (unfold is_error_code; apply Z.ltb_ge; lia).
        rewrite Hne.
        forward_if.
        { exfalso. match goal with H: Int.repr 0 <> Int.zero |- _ => apply H; reflexivity end. }
        { forward. rewrite isptr_offset_val_zero by exact Hst. entailer!. }
      * forward. entailer!.
      * pose proof (lim_init _ Hiw7 Ewf) as Hli0.
        pose proof Hso as Hso'. rewrite Hos in Hso'. destruct Hso' as (HfLL & HfOF & HfML).
        sep_apply (li_borrow HTB HG (a_gv a) (a_p a) (a_ox a) tLL tOF tML pLL pOF pML).
        Intros sht fm Rt.
        match goal with H: seqtabs_sh_ok _ |- _ => rename H into Hsht end.
        match goal with H: forall fe': Z, _ |-- tabs_seq_tp _ _ _ _ _ _ * _ * _ |- _ => rename H into Hgive end.
        destruct sht as [[shLL shOF] shML], fm as [[fLL fOF] fML].
        destruct Hsht as (HsLL & HsOF & HsML).
        unfold seq_ptrs, seqtabs_at. Intros.
        assert_PROP (isptr pLL) as HpLL by (sep_apply (li_tab_isptr shLL KLL tLL fLL pLL); entailer!).
        assert_PROP (isptr pOF) as HpOF by (sep_apply (li_tab_isptr shOF KOF tOF fOF pOF); entailer!).
        assert_PROP (isptr pML) as HpML by (sep_apply (li_tab_isptr shML KML tML fML pML); entailer!).
        pose proof (li_bcons0 _ Hiw7 Ewf) as Hb0.
        pose proof HfLL as (HlLL & _). pose proof HfOF as (HlOF & _). pose proof HfML as (HlML & _).
        cbn [sk_maxlog] in HlLL, HlOF, HlML. unfold LLFSELog, OffFSELog, MLFSELog in *.
        forward.
        forward_call (Tsh, field_address t_seqstate (DOT _stateLL) (a_vss a), Tsh,
          field_address t_seqstate (DOT _DStream) (a_vss a), a_gv a, iw_s (a_i a), a_start a,
          bs_total (iw_s (a_i a)), (8 * Z.max 0 (Zlength (iw_s (a_i a)) - 8))%Z, sh2, a_start a, iw_s (a_i a), 0,
          shLL, KLL, tLL, fLL, pLL).
        { entailer!. unfold field_address. rewrite !if_true by auto with field_compatible. reflexivity. }
        { pose proof (li_bsrc (iw_s (a_i a)) _ Hst) as Hbs. unfold bit_src_ok in Hbs. destruct Hbs as (? & ? & ? & ?). repeat split; auto; rep_lia. }
        Intros v1.
        match goal with |- context [BIT_DStream_rep Tsh _ _ _ ?pos ?lo _] =>
          assert_PROP (0 <= lo /\ lo mod 8 = 0 /\ pos <= lo + 64) as Hi1 by (sep_apply li_rep_inv; entailer!);
          pose proof (li_bcons_step (bs_total (iw_s (a_i a))) (8 * Z.max 0 (Zlength (iw_s (a_i a)) - 8)) (ft_log tLL)
            ltac:(lia) ltac:(unfold bcons in Hb0; lia)) as Hb1;
          forward;
          forward_call (Tsh, field_address t_seqstate (DOT _stateOffb) (a_vss a), Tsh,
            field_address t_seqstate (DOT _DStream) (a_vss a), a_gv a, iw_s (a_i a), a_start a,
            pos, lo, sh2, a_start a, iw_s (a_i a), 0, shOF, KOF, tOF, fOF, pOF)
        end.
        { entailer!. unfold field_address. rewrite !if_true by auto with field_compatible. reflexivity. }
        { pose proof (li_bsrc (iw_s (a_i a)) _ Hst) as Hbs. unfold bit_src_ok in Hbs. destruct Hbs as (? & ? & ? & ?). repeat split; auto; rep_lia. }
        Intros v2.
        match goal with |- context [BIT_DStream_rep Tsh _ _ _ ?pos ?lo _] =>
          assert_PROP (0 <= lo /\ lo mod 8 = 0 /\ pos <= lo + 64) as Hi2 by (sep_apply li_rep_inv; entailer!)
        end.
        pose proof (li_bcons_step (bs_total (iw_s (a_i a)) - ft_log tLL)
            (snd (bs_reload (bs_total (iw_s (a_i a)) - ft_log tLL) (8 * Z.max 0 (Zlength (iw_s (a_i a)) - 8))))
            (ft_log tOF) ltac:(lia) ltac:(lia)) as Hb2.
        match goal with |- context [BIT_DStream_rep Tsh _ _ _ ?pos ?lo _] =>
          forward;
          forward_call (Tsh, field_address t_seqstate (DOT _stateML) (a_vss a), Tsh,
            field_address t_seqstate (DOT _DStream) (a_vss a), a_gv a, iw_s (a_i a), a_start a,
            pos, lo, sh2, a_start a, iw_s (a_i a), 0, shML, KML, tML, fML, pML)
        end.
        { entailer!. unfold field_address. rewrite !if_true by auto with field_compatible. reflexivity. }
        { pose proof (li_bsrc (iw_s (a_i a)) _ Hst) as Hbs. unfold bit_src_ok in Hbs. destruct Hbs as (? & ? & ? & ?). repeat split; auto; rep_lia. }
        Intros v3.
        match goal with |- context [BIT_DStream_rep Tsh _ _ _ ?pos ?lo _] =>
          assert_PROP (0 <= lo /\ lo mod 8 = 0 /\ pos <= lo + 64) as Hi3 by (sep_apply li_rep_inv; entailer!)
        end.
        unfold seq_ptrs, seqtabs_at in Hgive. sep_apply (Hgive 1). clear Hgive.
        match goal with |- context [BIT_DStream_rep Tsh _ _ _ ?pos ?lo _] =>
          eapply semax_pre; [| apply (HK {| w_id := 0; w_ie := 0; w_pos := pos; w_lo := lo; w_st := (v1, v2, v3);
             w_drep := (r1, r2, r3); w_ring := repeat None 8; w_q := []; w_K := 0; w_j := 0; w_sw := false;
             w_c := oa_c (a_o a); w_pp := a_d a - a_ps a |}) ]
        end.
        -- clear HK. unfold LI_S, S_fix, L_ex, L_base.
           cbn [app w_pos w_lo w_st w_drep w_ring w_K w_j w_sw w_c w_pp x_t x_tp x_sh1 x_sh2 x_Ri x_xc].
           rewrite Erep, Hpfx, !Z.add_0_r. unfold seqstate_at.
           change (ring_vals (repeat None 8)) with (default_val (tarray t_seq 8)).
           fold (data_at_ Tsh (tarray t_seq 8) (a_vsqs a)). rewrite !(field_at_data_at Tsh t_seqstate). entailer!.
        -- clear HK.
           pose proof (li_bcons_step (bs_total (iw_s (a_i a)) - ft_log tLL - ft_log tOF)
              (snd (bs_reload (bs_total (iw_s (a_i a)) - ft_log tLL - ft_log tOF)
                 (snd (bs_reload (bs_total (iw_s (a_i a)) - ft_log tLL) (8 * Z.max 0 (Zlength (iw_s (a_i a)) - 8))))))
              (ft_log tML) ltac:(lia) ltac:(lia)) as Hb3.
           unfold LIP, LI_P.
           cbn [fold_right w_id w_ie w_pos w_lo w_st w_drep w_ring w_q w_K w_j w_sw w_c w_pp x_t x_tp].
           split; [lia|]. split; [lia|]. split; [lia|]. split; [reflexivity|].
           split. { split; [reflexivity|]. intros k Hk. cbn in Hk. lia. }
           split. { constructor. }
           split. { unfold dec_safe, states_ok, rep_c_ok, rc1. split; [lia|]. split; [lia|]. lia. }
           split. { pose proof Hoa as (_ & _ & HN & _ & _ & Hdc). unfold a_d. lia. }
           split; [apply li_ex_safe; auto|].
           split; [exact Hdef0|].
           split; [|split; [|exact I]].
           2: { rewrite <- Erep. exact (xl_init a tLL tOF tML v1 v2 v3 Hxctx Hos ltac:(lia) Ewf H0 H2 H4). }
           intros seqs HDM. unfold DM in HDM. cbv beta iota in HDM.
           pose proof (loop_init_model tLL tOF tML (iw_s (a_i a)) (a_nb a) seqs v1 v2 v3 Hiw7 Ewf HfLL HfOF HfML
             H0 H2 H4 HDM) as [Hrdy Hdec].
           assert (Hlen: Zlength seqs = a_nb a).
           { rewrite Zlength_correct, (li_decode_len _ _ _ _ _ _ _ _ _ _ _ Hdec), Z2Nat.id by lia. reflexivity. }
           split; [exact Hlen|].
           split.
           { unfold dec_model. cbv beta iota. split; [| split].
             - intros _. rewrite Z.sub_0_r, sublist_same by lia. split; [exact Hdec | exact Hrdy].
             - intros; lia.
             - rewrite sublist_nil, Erep. reflexivity. }
           split. { rewrite sublist_nil. reflexivity. }
           unfold ex_model. rewrite sublist_nil. cbn [sum_llml sum_ll fold_right rep_chain].
           split; [reflexivity|]. split; [reflexivity|].
           intros out' lits' rep2 (Hex & Hcnt & Hhv & Hec) Hcap'.
           split. { rewrite Erep; exact Hrep. }
           exists []. split; [reflexivity|]. split. { rewrite Z.add_0_r, sublist_nil. reflexivity. }
           split.
           { rewrite app_nil_r, (sublist_same 0 (a_n a) (a_lits a)) by (unfold a_n; lia).
             rewrite (sublist_same 0 (a_nb a) seqs) by lia. exact Hex. }
           unfold lit_intact. destruct Hlits as (_ & _ & Hl). destruct (a_l a); auto.
           intros _. rewrite Z.add_0_r. unfold a_n. apply Hl.
        -- unfold adv_ph. cbn. auto.
        -- reflexivity.
    + clear HK.
      match goal with |- semax _ ?Pre _ _ =>
        forward_loop Pre continue: (PROP (False) LOCAL () SEP ()) break: (PROP (False) LOCAL () SEP ()) end.
      * entailer!.
      * forward_call (Tsh, field_address t_seqstate (DOT _DStream) (a_vss a), sh2, a_start a, iw_s (a_i a), 0,
          Zlength (iw_s (a_i a)), a_gv a).
        { rewrite isptr_offset_val_zero by exact Hst. entailer!.
          unfold field_address. rewrite if_true by auto with field_compatible. reflexivity. }
        rewrite Hsub, Ewf. Intros r.
        match goal with H: is_error_code r = true |- _ => rename H into Hre end.
        forward_call r.
        rewrite Hre.
        forward_if.
        { li_dw0. li_dw0if. li_dw0. li_dw0.
          subst Rr. apply semax_post with (R' := lg_R a).
          1-3: unfold lg_R, frame_ret_assert, function_body_ret_assert; simpl RA_normal; simpl RA_break;
               simpl RA_continue; unfold bind_ret; apply andp_left2; intro rho; simpl; normalize; try contradiction.
          1: intros vl; apply andp_left2; apply derives_refl.
          clear Hlfx Hx Hc0 Hvs Hiw8 Hpend.
          unfold lg_R, la_post. forward.
          assert (Hmn: seqs_model (a_os a) (iw_s (a_i a)) (a_nb a) (a_rep a) (hc_hist (a_h a)) (hc_out (a_h a))
                         (a_lits a) (hc_wsize (a_h a)) = None)
            by (rewrite Hos; apply li_model_none; [exact Ewf | lia]).
          Exists (2 ^ 64 - 20) (oa_c (a_o a)) (r1, r2, r3).
          rewrite Hmn, (proj2 (Z.eqb_neq (a_nb a) 0) ltac:(lia)), Hos.
          sep_apply (li_elim HTE (a_gv a) (a_p a) (a_ox a) tLL tOF tML pLL pOF pML 1).
          destruct Hlfxx as [Exc Hxl]. cbn [x_xc] in Exc. subst xc.
          sep_apply (li_lit_scratch_x a false ltac:(destruct Hxl as (? & ? & _); split; assumption)).
          pose proof (xl_init_err a (tLL, tOF, tML) Hxctx Hos ltac:(lia) Ewf) as Hxn.
          change (data_at_ Tsh (Tstruct ___gp_seqState_t noattr) (a_vss a)) with (data_at_ Tsh t_seqstate (a_vss a)).
          rewrite Heq, (li_ss_split (a_vss a)).
          unfold a_ob, a_x in *.
          entailer!.
          repeat match goal with
            | |- _ /\ _ => split
            | |- Zlength _ = _ => pose proof Hoa as (_ & Hl & _); exact Hl
            | |- is_error_code _ = false -> _ => intros Hf; discriminate Hf
            | |- is_error_code _ = true -> dec_err _ =>
                intros _; exact (fs_dec_err 20 ltac:(lia) ltac:(lia) ltac:(lia))
            | |- byte_cells _ -> _ => intros Hcb _ _; exact Hcb
            | |- seqs_exact _ _ _ _ _ _ _ _ _ _ _ _ => rewrite <- Hos; apply xl_exact_none; [reflexivity | exact Hxn]
            | |- Vlong _ = Vlong _ => f_equal; apply li_repr_eqm; reflexivity
            end. }
        { exfalso. match goal with H: Int.repr 1 = Int.zero |- _ => discriminate H end. }
Qed.
