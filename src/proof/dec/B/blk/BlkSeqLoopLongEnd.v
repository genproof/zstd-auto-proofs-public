(* LOOP / long loop: BIT_endOfDStream check; saving the repeat offsets. *)
Require Import Zstd.proof.dec.B.blk.BlkSeqLoopLongDefs Zstd.proof.dec.B.blk.BlkSeqLoopLongXD.
Local Open Scope logic.

(* the literal fields back to scratch, litExtraBuffer still holding lxb *)
Lemma lge_lit_release_x (a: la) (xc: list val) (sw: bool) :
  xc = zbytes (a_lxb a) -> xl_lxb_ok a -> lit_now a xc sw |-- lit_scratch_x (a_p a) (a_lxb a).
Proof.
  intros -> (Hn & Hb & _). unfold lit_now, lit_fix, lit_scratch_x, lit_extra_at.
  rewrite <- litextra_data_at. destruct (a_l a); entailer!.
Qed.

(* the seqState_t local back to data_at_ (as BlkSeqLoopShort.sh_end_ok_ss) *)
Lemma lge_ss_split (v: val) :
  data_at_ Tsh (Tstruct ___gp_seqState_t noattr) v =
  data_at_ Tsh t_bitd (field_address t_seqstate (DOT _DStream) v) *
  data_at_ Tsh t_fsestate (field_address t_seqstate (DOT _stateLL) v) *
  data_at_ Tsh t_fsestate (field_address t_seqstate (DOT _stateOffb) v) *
  data_at_ Tsh t_fsestate (field_address t_seqstate (DOT _stateML) v) *
  field_at_ Tsh t_seqstate (DOT _prevOffset) v.
Proof.
  unfold_data_at (data_at_ Tsh (Tstruct ___gp_seqState_t noattr) v).
  rewrite !field_at_data_at. rewrite <- !sepcon_assoc. unfold field_at_. rewrite field_at_data_at. reflexivity.
Qed.

Lemma lge_ss (gv: globals) (s: list Z) (start: val) (pos lo sLL sOF sML: Z) (pLL pOF pML: val) (r: Z * Z * Z)
    (v: val) :
  BIT_DStream_rep Tsh gv s start pos lo (field_address t_seqstate (DOT _DStream) v) *
  field_at Tsh t_seqstate (DOT _stateLL) (fse_val sLL pLL) v *
  field_at Tsh t_seqstate (DOT _stateOffb) (fse_val sOF pOF) v *
  field_at Tsh t_seqstate (DOT _stateML) (fse_val sML pML) v *
  field_at Tsh t_seqstate (DOT _prevOffset) (rep64_vals r) v
  |-- data_at_ Tsh (Tstruct ___gp_seqState_t noattr) v.
Proof.
  rewrite lge_ss_split. unfold BIT_DStream_rep. Intros ptr lim.
  sep_apply (field_at_field_at_ Tsh t_seqstate (DOT _prevOffset) (rep64_vals r) v).
  rewrite !field_at_data_at.
  sep_apply (data_at_data_at_ Tsh t_bitd
    (Vlong (Int64.repr (bit_C s lo)), (Vint (Int.repr (lo + 64 - pos)), (ptr, (start, lim))))
    (field_address t_seqstate (DOT _DStream) v)).
  sep_apply (data_at_data_at_ Tsh t_fsestate (fse_val sLL pLL) (field_address t_seqstate (DOT _stateLL) v)).
  sep_apply (data_at_data_at_ Tsh t_fsestate (fse_val sOF pOF) (field_address t_seqstate (DOT _stateOffb) v)).
  sep_apply (data_at_data_at_ Tsh t_fsestate (fse_val sML pML) (field_address t_seqstate (DOT _stateML) v)).
  cancel.
Qed.

(* oend <= dst + capacity *)
Lemma lge_E_le (a: la) : la_ok a -> a_E a <= a_d a + a_cap a.
Proof.
  intros (_ & _ & Hlits & _). unfold a_E, a_d, a_cap.
  destruct Hlits as (_ & Hn & Hl). destruct (a_l a); try lia.
  destruct Hl as (? & ? & _). unfold WILDCOPY_OVERLENGTH in *. lia.
Qed.

Lemma lge_unch (a: la) (K j: Z) (sw: bool) (c: list val) :
  la_ok a -> ex_safe a K j sw c ->
  unchanged_outside (oa_c (a_o a)) c (oa_d (a_o a)) (oa_d (a_o a) + oa_cap (a_o a)).
Proof.
  intros Hla (HK & HKE & _ & _ & _ & Hu). pose proof (lge_E_le a Hla) as HE.
  unfold a_d, a_cap in *. intros k Hk Hn. apply Hu; [exact Hk|]. intros Hk'. apply Hn. lia.
Qed.

(* the model decodes when seqs_model is defined *)
Lemma lge_DM (a: la) (t: fse_table * fse_table * fse_table) (rep: Z * Z * Z) (hist out lits: list Z)
    (wsize: Z) (r: list Z * (Z * Z * Z)) :
  a_os a = Some t -> 0 < a_nb a ->
  seqs_model (a_os a) (iw_s (a_i a)) (a_nb a) rep hist out lits wsize = Some r ->
  exists seqs, DM a t seqs /\ exec_seqs wsize rep hist lits out seqs <> None.
Proof.
  intros Hos Hnb Hm. unfold seqs_model in Hm. rewrite Hos in Hm.
  replace (a_nb a =? 0) with false in Hm by (symmetry; apply Z.eqb_neq; lia).
  destruct t as [[tLL tOF] tML].
  destruct (decode_seq_stream tLL tOF tML (iw_s (a_i a)) (a_nb a)) as [seqs|] eqn:Hd; [|discriminate].
  exists seqs. split; [exact Hd|].
  destruct (exec_seqs wsize rep hist lits out seqs); [discriminate|discriminate].
Qed.

Lemma lg_end_ok : SEG_END.
Proof.
  intros HTE Espec a x w HG Hla Hpd Hlx Hlxx HLI Hph Hid Hnb.
  unfold lg_end, lg_R.
  forward_loop (LI a x w (a_nb a))
    break: (PROPx (LI_P a x w ++ [w_pos w = 0]) (LOCALx (LI_L a w (a_nb a)) (SEPx (LI_S a x w)))).
  - apply ENTAIL_refl.
  - unfold LI at 1. unfold LI_P, LI_L, LI_S, S_fix, L_seq, L_ex, L_base.
    destruct (x_tp x) as [[pLL pOF] pML] eqn:Etp.
    destruct (w_st w) as [[sLL sOF] sML] eqn:Est.
    unfold seqstate_at. Intros. cbv [app]. repeat flatten_sepcon_in_SEP.
    assert (Hlx' := Hlx). destruct Hlx' as (Hos & Hsh1 & Hsh2 & Heq & Hxc).
    assert_PROP (isptr (a_start a)) as Hsp.
    { unfold bit_src. entailer!. }
    assert_PROP (field_compatible t_seqstate (DOT _DStream) (a_vss a)) as HFC.
    { entailer!. }
    forward_call (Tsh, field_address t_seqstate (DOT _DStream) (a_vss a), a_gv a, iw_s (a_i a),
                  a_start a, w_pos w, w_lo w, x_sh2 x, a_start a, iw_s (a_i a), 0).
    { entailer!. simpl. rewrite field_compatible_field_address by auto. reflexivity. }
    { unfold bit_src_ok. rewrite isptr_offset_val_zero by auto.
      split; [reflexivity|]. split; [lia|]. rewrite Z.add_0_l, sublist_same by lia. split; [lia|reflexivity]. }
    forward_if (w_lo w = 0 /\ w_pos w = 0).
    + apply dec_skipbreak_seq. unfold MORE_COMMANDS, abbreviate.
      match goal with |- semax _ ?P _ _ => forward_loop P break: P end.
      * apply ENTAIL_refl.
      * forward_if True. { contradiction. } { forward. entailer!. }
        forward. Intros. apply ENTAIL_refl.
      * apply dec_skipbreak_seq. apply dec_skipbreak_seq.
        unfold la_post in POSTCONDITION. forward.
        Exists (Int64.unsigned (Int64.repr (-20))) (w_c w) (a_rep a).
        rewrite Int64.repr_unsigned.
        sep_apply (lge_ss (a_gv a) (iw_s (a_i a)) (a_start a) (w_pos w) (w_lo w) sLL sOF sML pLL pOF pML
                     (w_drep w) (a_vss a)).
        sep_apply (lge_lit_release_x a (x_xc x) (w_sw w) (proj1 Hlxx) (proj2 Hlxx)).
        sep_apply (derives_refl' _ _ (eq_sym Heq)).
        sep_apply (HTE (a_gv a) (a_p a) (a_ox a) (x_t x) 1 (pLL, pOF, pML)).
        sep_apply (data_at_data_at_ Tsh (tptr tuchar)
                     (offset_val (lit_li a (w_sw w) (w_j w)) (lit_base a (w_sw w))) (a_vlp a)).
        sep_apply (data_at_data_at_ Tsh (tarray t_seq 8) (ring_vals (w_ring w)) (a_vsqs a)).
        rewrite <- Hos. replace (a_nb a =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
        apply andp_right; [apply prop_right | unfold a_x, a_ob; cancel].
        assert (Hla' := Hla). destruct Hla' as (_ & _ & _ & _ & _ & _ & _ & _ & Hrep & _).
        split; [apply Int64.unsigned_range_2|].
        split; [destruct H7 as (_ & _ & _ & _ & HN & _); exact HN|]. split; [exact Hrep|].
        split; [exact (lge_unch a _ _ _ _ Hla H7)|].
        assert (HE: is_error_code (Int64.unsigned (Int64.repr (-20))) = true) by reflexivity.
        rewrite HE. split; [discriminate|]. split; [|split; [|split; [|split; [|reflexivity]]]].
        2: { intros _. unfold dec_err. rewrite HE. split; [reflexivity|]. cbv. split; discriminate. }
        2: { destruct H7 as (_ & _ & _ & _ & _ & _ & Hb). exact Hb. }
        2: { apply (xl_exact_none a _ _ _ HE).
             apply (xl_end a (x_t x) (w_K w) (w_c w) (w_drep w) (w_j w) (w_sw w) (w_pos w) (w_lo w)
                      (sLL, sOF, sML) (w_q w)); [rewrite <- Hid; exact H10|].
             intros [Hl Hp]. rewrite Hl, Hp in H11. simpl in H11.
             apply (f_equal Int.unsigned) in H11. rewrite Int.unsigned_repr, Int.unsigned_zero in H11 by rep_lia.
             discriminate. }
        intros _.
        destruct (seqs_model (a_os a) (iw_s (a_i a)) (a_nb a) (a_rep a) (hc_hist (a_h a)) (hc_out (a_h a))
                    (a_lits a) (hc_wsize (a_h a))) as [r|] eqn:Esm; [|exact I].
        exfalso. destruct (lge_DM a (x_t x) _ _ _ _ _ r Hos Hnb Esm) as (seqs & Hdm & _).
        destruct (H9 seqs Hdm) as (_ & (_ & Hend & _) & _).
        destruct (Hend Hid) as [Hp Hl]. rewrite Hp, Hl in H11. simpl in H11.
        apply (f_equal Int.unsigned) in H11. rewrite Int.unsigned_repr, Int.unsigned_zero in H11 by rep_lia.
        discriminate.
    + assert (Hlp: w_lo w = 0 /\ w_pos w = 0).
      { destruct ((w_lo w =? 0) && (w_pos w =? 0))%bool eqn:E;
          [rewrite andb_true_iff, !Z.eqb_eq in E; exact E | contradiction H11; reflexivity]. }
      forward. entailer!.
    + forward. unfold LI, LI_P, LI_L, LI_S, S_fix, L_seq, L_ex, L_base, seqstate_at. rewrite Etp, Est.
      cbv [app]. entailer!.
Qed.

(* ===================== REPS ===================== *)

(* the U32 truncation of a decoder repeat offset is never 0 *)
Lemma lge_rc1_trunc (k v: Z) : 0 <= k <= 2 ^ 32 - 2 -> rc1 k v -> 1 <= v mod 2 ^ 32 < 2 ^ 32.
Proof.
  intros Hk [Hv|Hv].
  - rewrite Z.mod_small by lia. lia.
  - unfold SIZE_MAX in Hv.
    replace v with ((2 ^ 32 - 1 - (2 ^ 64 - 1 - v)) + (2 ^ 32 - 1) * 2 ^ 32) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma lge_rep_trunc_ok (k: Z) (r: Z * Z * Z) : 0 <= k <= 2 ^ 32 - 2 -> rep_c_ok k r -> rep_ok (rep_trunc r).
Proof.
  destruct r as [[r1 r2] r3]. intros Hk (H1 & H2 & H3). unfold rep_trunc, rep_ok.
  repeat split; first [apply (lge_rc1_trunc k); assumption | apply (lge_rc1_trunc k r1); assumption |
                       apply (lge_rc1_trunc k r2); assumption | apply (lge_rc1_trunc k r3); assumption].
Qed.

Lemma lge_rep_trunc_id (r: Z * Z * Z) : rep_ok r -> rep_trunc r = r.
Proof.
  destruct r as [[r1 r2] r3]. intros (H1 & H2 & H3). unfold rep_trunc. rewrite !Z.mod_small by lia. reflexivity.
Qed.

Lemma lge_sum_llml_full (l: list sequence) : sublist 0 (Zlength l) l = l.
Proof. apply sublist_same; lia. Qed.

(* the model when all sequences are decoded and executed *)
Lemma lge_XM (a: la) (t: fse_table * fse_table * fse_table) (id ie pos lo: Z) (st drep: Z * Z * Z)
    (q: list (Z * Z * Z)) (K j: Z) (sw: bool) (c: list val) :
  la_ok a -> a_os a = Some t -> 0 < a_nb a -> id = a_nb a -> ie = a_nb a ->
  (forall seqs, DM a t seqs ->
     Zlength seqs = a_nb a /\ dec_model a t seqs id pos lo st drep /\
     q = q_of (rep_chain (a_rep a) (sublist 0 ie seqs)) (sublist ie id seqs) /\
     ex_model a seqs ie K j sw c) ->
  XM a K j sw c (rep_trunc drep).
Proof.
  intros Hla Hos Hnb Hid Hie HM seqs Hg.
  assert (Hcap: 0 < oa_cap (a_o a)).
  { destruct Hla as (_ & _ & _ & _ & _ & _ & Hc & _). apply Hc. lia. }
  assert (Hdm: DM a t seqs).
  { unfold DMg in Hg. rewrite Hos in Hg.
    replace (a_nb a =? 0) with false in Hg by (symmetry; apply Z.eqb_neq; lia).
    destruct t as [[tLL tOF] tML]. exact Hg. }
  destruct (HM seqs Hdm) as (Hlen & (_ & _ & Hdrep) & _ & (HK & Hj & Hex)).
  subst id ie.
  rewrite <- Hlen, lge_sum_llml_full in HK, Hj, Hdrep.
  split; [exact HK|]. split; [exact Hj|].
  intros out' lits' rep2 He Hcnt Hhv Hcc.
  assert (Hhv': hist_view (oa_c (a_o a)) (oa_d (a_o a)) (hc_ps (a_h a)) (hc_ext (a_h a)) (hc_hist (a_h a))
                  (hc_out (a_h a)) (hc_wsize (a_h a)) /\
                ext_clear (oa_d (a_o a)) (hc_ps (a_h a)) (oa_cap (a_o a)) (a_bsm a) (hc_ext (a_h a))
                  (hc_hist (a_h a)) (hc_out (a_h a)) (hc_wsize (a_h a))).
  { destruct Hhv as [Hhv|Hhv]; [lia|exact Hhv]. }
  assert (HEM: EM a seqs out' lits' rep2).
  { unfold EM. split; [exact He|]. split; [exact Hcnt|]. exact Hhv'. }
  destruct (Hex out' lits' rep2 HEM Hcc) as (Hrok & blk & Hb & Hsub & Hexe & Hint).
  rewrite <- Hlen, lge_sum_llml_full in Hrok, Hexe.
  rewrite sublist_nil in Hexe. simpl in Hexe. injection Hexe as Ho Hl Hr.
  split.
  - rewrite Hdrep, lge_rep_trunc_id by exact Hrok. exact Hr.
  - exists blk. split; [exact Hb|]. split; [exact Hsub|]. split; [congruence|]. split; [congruence|exact Hint].
Qed.

(* one step of the copy of the three offsets *)
Lemma lge_upd3 (A B: list val) (i: Z) (v: val) :
  Zlength A = 3 -> Zlength B = 3 -> 0 <= i < 3 -> Znth i A = v ->
  upd_Znth i (sublist 0 i A ++ sublist i 3 B) v = sublist 0 (i + 1) A ++ sublist (i + 1) 3 B.
Proof.
  intros HA HB Hi Hv.
  destruct A as [|a0 [|a1 [|a2 [|a3 A]]]];
    try (exfalso; rewrite ?Zlength_cons, ?Zlength_nil in HA; try pose proof (Zlength_nonneg A); lia).
  destruct B as [|b0 [|b1 [|b2 [|b3 B]]]];
    try (exfalso; rewrite ?Zlength_cons, ?Zlength_nil in HB; try pose proof (Zlength_nonneg B); lia).
  assert (i = 0 \/ i = 1 \/ i = 2) as [-> | [-> | ->]] by lia; subst v; reflexivity.
Qed.

(* the U32 cast of a size_t is its truncation *)
Lemma lge_cast32 (z: Z) : Int.repr (Int64.unsigned (Int64.repr z)) = Int.repr (z mod 2 ^ 32).
Proof.
  rewrite Int64.unsigned_repr_eq. apply Int.eqm_samerepr. unfold Int.eqm, Zbits.eqmod.
  exists (z / 2 ^ 32 - 2 ^ 32 * (z / 2 ^ 64)).
  change Int64.modulus with (2 ^ 64). change Int.modulus with (2 ^ 32).
  rewrite (Z.mod_eq z (2 ^ 64)), (Z.mod_eq z (2 ^ 32)) by lia. lia.
Qed.

Lemma lg_reps_ok : SEG_REPS.
Proof.
  intros HTE Espec a x w HG Hla Hpd Hlx Hlxx HLI Hph Hie Hnb.
  unfold lg_reps, LI, LI_P, LI_L, LI_S, S_fix, L_seq, L_ex, L_base.
  destruct (x_tp x) as [[pLL pOF] pML] eqn:Etp.
  destruct (w_st w) as [[sLL sOF] sML] eqn:Est.
  unfold seqstate_at. Intros. cbv [app]. repeat flatten_sepcon_in_SEP.
  assert (Hlx' := Hlx). destruct Hlx' as (Hos & Hsh1 & Hsh2 & Heq & Hxc).
  unfold fin_ph in Hph. destruct Hph as [Hph Hp0].
  assert (HXM: XM a (w_K w) (w_j w) (w_sw w) (w_c w) (rep_trunc (w_drep w))).
  { rewrite <- Est in H9. exact (lge_XM a (x_t x) _ _ _ _ _ _ _ _ _ _ _ Hla Hos Hnb Hph Hie H9). }
  (* the exact model: the queue is empty (ie = id = nbSeq), the stream consumed *)
  assert (HXA: xl_aft a (w_K w) (w_c w) (rep_trunc (w_drep w)) (w_j w) (w_sw w)).
  { assert (Hq: w_q w = nil) by (apply Zlength_nil_inv; lia).
    rewrite Hph, Hp0, Hq in H10. exact (xl_reps a _ _ _ _ _ _ _ _ H10). }
  destruct Hlxx as [Hxz Hxb].
  assert (Hrt: rep_ok (rep_trunc (w_drep w))).
  { destruct H5 as (_ & Hrc & _). destruct Hla as (_ & _ & _ & _ & _ & Hnbr & _).
    apply (lge_rep_trunc_ok (w_id w)); [unfold LONGNBSEQ in Hnbr; lia | exact Hrc]. }
  destruct (w_drep w) as [[c1 c2] c3] eqn:Ed.
  freeze [0;1;2;3;4;5;7;8;9;10;11;12;13;14;15;17;18;19;20] FR.
  forward_for_simple_bound 3 (EX k: Z,
    PROP ()
    LOCAL (temp _seqAdvance (Vint (Int.repr (a_adv a)));
     temp _seqNb (Vint (Int.repr (a_nb a)));
     temp _prefetchPos (Vlong (Int64.repr (w_pp w)));
     temp _op (offset_val (a_d a + w_K w) (a_ob a));
     temp _litBufferEnd (offset_val (lit_lim a (w_sw w)) (lit_base a (w_sw w)));
     lvar _sequence__1 t_seq (a_vs1 a); lvar _sequence t_seq (a_vs a);
     lvar _seqState t_seqstate (a_vss a);
     lvar _sequences (tarray t_seq 8) (a_vsqs a);
     lvar _litPtr (tptr tuchar) (a_vlp a); gvars (a_gv a);
     temp _dctx (a_p a);
     temp _dst (offset_val (oa_d (a_o a)) (oa_base (a_o a)));
     temp _maxDstSize (Vlong (Int64.repr (oa_cap (a_o a))));
     temp _seqStart (a_start a);
     temp _seqSize (Vlong (Int64.repr (Zlength (iw_s (a_i a)))));
     temp _nbSeq (Vint (Int.repr (a_nb a)));
     temp _isLongOffset (Vint (Int.repr 0));
     temp _ostart (offset_val (oa_d (a_o a)) (oa_base (a_o a)));
     temp _oend (offset_val (a_E a) (oa_base (a_o a)));
     temp _prefixStart (fs_prefixStart (a_fs a));
     temp _dictStart (fs_virtualStart (a_fs a));
     temp _dictEnd (fs_dictEnd (a_fs a)))
    SEP (FRZL FR; field_at Tsh t_seqstate (DOT _prevOffset) (rep64_vals (c1, c2, c3)) (a_vss a);
         field_at Ews t_dctx (DOT _entropy DOT _rep)
           (sublist 0 k (rep_vals (rep_trunc (c1, c2, c3))) ++ sublist k 3 (rep_vals (a_rep a))) (a_p a)))%assert.
  - entailer!. rewrite sublist_nil, app_nil_l, sublist_same; [apply derives_refl | reflexivity |].
    destruct (a_rep a) as [[? ?] ?]; reflexivity.
  - assert (Hz: forall d, @Znth val d i (rep64_vals (c1, c2, c3)) = Vlong (Int64.repr (Znth i [c1; c2; c3]))).
    { intros d. assert (i = 0 \/ i = 1 \/ i = 2) as [ -> | [ -> | -> ] ] by lia; reflexivity. }
    forward.
    { entailer!. rewrite Hz. exact I. }
    rewrite !Hz.
    forward.
    rewrite Int64.Z_mod_modulus_eq, <- Int64.unsigned_repr_eq, lge_cast32.
    rewrite (lge_upd3 _ _ i); [entailer! | reflexivity | destruct (a_rep a) as [[? ?] ?]; reflexivity | lia |].
    assert (i = 0 \/ i = 1 \/ i = 2) as [ -> | [ -> | -> ] ] by lia; reflexivity.
  - thaw FR.
    rewrite (sublist_same 0 3) by reflexivity. rewrite sublist_nil, app_nil_r.
    unfold XI, XI_P, XI_S, L_ex, L_base. cbv [app].
    sep_apply (lge_ss (a_gv a) (iw_s (a_i a)) (a_start a) (w_pos w) (w_lo w) sLL sOF sML pLL pOF pML
                 (c1, c2, c3) (a_vss a)).
    sep_apply (derives_refl' _ _ (eq_sym Heq)).
    sep_apply (HTE (a_gv a) (a_p a) (a_ox a) (x_t x) 1 (pLL, pOF, pML)). rewrite <- Hos.
    sep_apply (data_at_data_at_ Tsh (tarray t_seq 8) (ring_vals (w_ring w)) (a_vsqs a)).
    unfold t_seqstate. entailer!.
Qed.

Lemma lg_endreps_ok : SEG_END /\ SEG_REPS.
Proof.
  split; [exact lg_end_ok | exact lg_reps_ok].
Qed.
