(* LOOP / long loop, part MAIN: the invariant's plumbing (pure). *)
Require Import Zstd.proof.dec.B.blk.BlkSeqLoopLongMainDefs.
Local Open Scope logic.

(* ---------- the model's offset values are in [1, 2^32) ---------- *)

Lemma lmi_sym_OF (t: fse_table) (s: Z) : fse_ok KOF t -> 0 <= fe_sym (fse_cell t s) <= 31.
Proof.
  intros (_ & _ & HF). unfold fse_cell.
  destruct (nth_in_or_default (Z.to_nat s) (ft_cells t) {| fe_sym := 0; fe_nb := 0; fe_base := 0 |}) as [Hin|Hd].
  - rewrite Forall_forall in HF. apply HF in Hin. cbn [sk_max] in Hin. unfold MaxOff in Hin. lia.
  - rewrite Hd. cbn [fe_sym]. lia.
Qed.

Lemma lmi_peek_range (s: list Z) (pos nb: Z) : 0 <= nb -> 0 <= pos - nb -> 0 <= bs_peek_s s pos nb < 2 ^ nb.
Proof.
  intros H1 H2. unfold bs_peek_s.
  replace (pos <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (pos - nb >=? 0) with true by (symmetry; apply Z.geb_le; lia).
  apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
Qed.

Lemma lmi_rd (V: list Z) (pos nb e p: Z) : rd V pos nb = Some (e, p) -> 0 <= pos - nb /\ e = bs_peek_s V pos nb.
Proof.
  unfold rd. destruct (pos - nb <? 0) eqn:E; [discriminate|]. apply Z.ltb_ge in E.
  intros H. injection H as <- _. auto.
Qed.

Lemma lmi_dseqs_ov (tLL tOF tML: fse_table) (V: list Z) (k: nat) :
  fse_ok KOF tOF -> forall sLL sOF sML pos l p,
  decode_seqs tLL tOF tML V k sLL sOF sML pos = Some (l, p) ->
  Forall (fun sq => 1 <= sq_ov sq < 2 ^ 32) l.
Proof.
  intros Hok. induction k as [|k IH]; intros sLL sOF sML pos l p H; cbn [decode_seqs] in H.
  - injection H as <- _. constructor.
  - pose proof (lmi_sym_OF tOF sOF Hok) as Hs.
    destruct (rd V pos (fe_sym (fse_cell tOF sOF))) as [[eOF p1]|] eqn:R1; [|discriminate].
    apply lmi_rd in R1. destruct R1 as [R1 ->].
    assert (Hov: 1 <= 2 ^ fe_sym (fse_cell tOF sOF) + bs_peek_s V pos (fe_sym (fse_cell tOF sOF)) < 2 ^ 32).
    { pose proof (lmi_peek_range V pos (fe_sym (fse_cell tOF sOF)) ltac:(lia) ltac:(lia)).
      assert (1 <= 2 ^ fe_sym (fse_cell tOF sOF)) by (change 1 with (2 ^ 0); apply Z.pow_le_mono_r; lia).
      assert (2 ^ fe_sym (fse_cell tOF sOF) <= 2 ^ 31) by (apply Z.pow_le_mono_r; lia).
      lia. }
    destruct (rd V p1 _) as [[eML p2]|]; [|discriminate].
    destruct (rd V p2 _) as [[eLL p3]|]; [|discriminate].
    destruct k as [|k].
    + injection H as <- _. constructor; [exact Hov|constructor].
    + destruct (rd V p3 _) as [[uLL p4]|]; [|discriminate].
      destruct (rd V p4 _) as [[uML p5]|]; [|discriminate].
      destruct (rd V p5 _) as [[uOF p6]|]; [|discriminate].
      destruct (decode_seqs tLL tOF tML V (S k) _ _ _ p6) as [[l' p']|] eqn:Hr; [|discriminate].
      injection H as <- _. constructor; [exact Hov|]. eapply IH. exact Hr.
Qed.

Lemma lmi_ov (a: la) (x: lfx) (seqs: list sequence) (i: Z) :
  la_ok a -> lfx_ok a x -> DM a (x_t x) seqs -> 0 <= i < Zlength seqs -> 1 <= sq_ov (Znth i seqs) < 2 ^ 32.
Proof.
  intros Hla Hlfx HD Hi.
  destruct Hla as (_ & _ & _ & _ & _ & _ & _ & Hsok & _).
  destruct Hlfx as (Hos & _).
  rewrite Hos in Hsok. unfold DM in HD. destruct (x_t x) as [[tLL tOF] tML].
  destruct Hsok as (_ & HOF & _).
  unfold decode_seq_stream in HD.
  destruct (negb (bs_okb (iw_s (a_i a)))); [discriminate|].
  destruct (rd _ _ (ft_log tLL)) as [[sLL p1]|]; [|discriminate].
  destruct (rd _ p1 (ft_log tOF)) as [[sOF p2]|]; [|discriminate].
  destruct (rd _ p2 (ft_log tML)) as [[sML p3]|]; [|discriminate].
  destruct (decode_seqs _ _ _ _ _ _ _ _ p3) as [[l p]|] eqn:Hd; [|discriminate].
  destruct p; try discriminate. injection HD as ->.
  pose proof (lmi_dseqs_ov _ _ _ _ _ HOF _ _ _ _ _ _ Hd) as HF.
  rewrite Forall_forall in HF. apply HF. apply Znth_In. exact Hi.
Qed.

(* ---------- the queue and the ring ---------- *)

Lemma lmi_rep_chain_app (r: Z * Z * Z) (l: list sequence) (sq: sequence) :
  rep_chain r (l ++ [sq]) = snd (c_offset (rep_chain r l) (sq_ll sq) (sq_ov sq)).
Proof. revert r. induction l as [|s l IH]; intros r; cbn [app rep_chain]; [reflexivity|apply IH]. Qed.

Lemma lmi_peel (seqs: list sequence) (lo hi: Z) :
  0 <= lo < hi -> hi <= Zlength seqs -> sublist lo hi seqs = Znth lo seqs :: sublist (lo + 1) hi seqs.
Proof.
  intros H1 H2. rewrite (sublist_split lo (lo + 1) hi) by lia. rewrite sublist_len_1 by lia. reflexivity.
Qed.

Lemma lmi_ring (ie: Z) (ring: list (option (Z * Z * Z))) (e0: Z * Z * Z) (qt: list (Z * Z * Z)) (e: Z * Z * Z) :
  Zlength qt = 7 -> ring_ok ie ring (e0 :: qt) ->
  ring_ok (ie + 1) (upd_Znth ((ie + 8) mod 8) ring (Some e)) (qt ++ [e]).
Proof.
  intros Hq [Hl Hk]. pose proof (Z.mod_pos_bound (ie + 8) 8 ltac:(lia)).
  split; [rewrite upd_Znth_Zlength; lia|].
  intros k Hk'. rewrite Zlength_app, Zlength_cons, Zlength_nil in Hk'.
  destruct (Z.eq_dec k 7) as [->|Hne].
  - replace (ie + 1 + 7) with (ie + 8) by lia. rewrite upd_Znth_same by lia.
    rewrite Znth_app2 by lia. replace (7 - Zlength qt) with 0 by lia. reflexivity.
  - pose proof (Z.mod_pos_bound (ie + 1 + k) 8 ltac:(lia)).
    assert ((ie + 1 + k) mod 8 <> (ie + 8) mod 8).
    { pose proof (Z.div_mod (ie + 1 + k) 8 ltac:(lia)). pose proof (Z.div_mod (ie + 8) 8 ltac:(lia)). lia. }
    rewrite upd_Znth_diff by lia.
    rewrite Znth_app1 by lia.
    specialize (Hk (k + 1) ltac:(rewrite Zlength_cons; lia)).
    replace (ie + (k + 1)) with (ie + 1 + k) in Hk by lia. rewrite Hk.
    rewrite Znth_pos_cons by lia. replace (k + 1 - 1) with k by lia. reflexivity.
Qed.

Lemma lg_main_inv_ok : P_INV.
Proof.
  intros a x w dd Hla Hpend Hlfx Hlx HMD.
  destruct w as [id ie pos lo st drep ring q K j sw c pp].
  unfold MD_P, LI_P in HMD; cbn [app fold_right w_id w_ie w_pos w_lo w_st w_drep w_ring w_q w_K w_j w_sw w_c w_pp] in HMD.
  destruct HMD as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & _ & Hph & Hid & Hds & Hqs & Hmd & Hxl & _).
  unfold main_ph, a_adv in Hph; cbn [w_id w_ie] in Hph.
  assert (Hnb: 8 <= a_nb a) by (destruct (Z.min_spec (a_nb a) 8); lia).
  rewrite Z.min_r in Hph by lia.
  destruct q as [|e0 qt]; [rewrite Zlength_nil in H4; lia|]. rewrite Zlength_cons in H4.
  cbn [w_id w_ie w_pos w_lo w_st w_drep w_ring w_q w_K w_j w_sw w_c w_pp].
  rewrite Znth_0_cons.
  assert (Hid8: id = ie + 8) by lia. subst id. clear Hph H3.
  assert (Hqt: Zlength qt = 7) by lia. clear H4.
  unfold q_safe in H6. rewrite Forall_cons_iff in H6. destruct H6 as [He0 Hqts].
  assert (Hm8: (ie + 8) mod 8 = ie mod 8).
  { replace (ie + 8) with (ie + 1 * 8) by lia. apply Z_mod_plus_full. }
  split; [|split; [|split; [|split; [|split; [|split]]]]].
  - destruct e0 as [[ll ml] off]. destruct He0 as (Hll & Hml & Hoff).
    unfold XP. split; [lia|]. split; [exact H9|]. split; [exact H10|].
    split; [exact Hll|]. split; [exact Hml|]. split; [exact Hoff|].
    intros seqs HD. destruct (H11 seqs HD) as (Hz & _ & Hq & Hex).
    rewrite (lmi_peel seqs ie (ie + 8)) in Hq by lia. cbn [q_of] in Hq.
    injection Hq as Ell Eml Eoff _.
    split; [exact Hz|]. split; [apply (lmi_ov a x seqs ie Hla Hlfx HD); lia|].
    split; [exact Ell|]. split; [exact Eml|]. split; [|exact Hex].
    rewrite Eoff. rewrite <- Ell. reflexivity.
  - symmetry; exact Hm8.
  - destruct H5 as [_ Hk]. specialize (Hk 0 ltac:(rewrite Zlength_cons; lia)).
    rewrite Z.add_0_r, Znth_0_cons in Hk. rewrite Hm8. exact Hk.
  - apply xl_ctx_of; [exact Hla | exact (proj2 Hlx)].
  - destruct H9 as (Hs1 & Hs2 & Hs3 & Hs4 & Hs5 & _). unfold xl_pos. auto.
  - cbn [tl]. exact Hxl.
  - intros K' j' sw' c' (Hs' & Hd' & Hm') Hxl'.
    unfold LIP, LI_P, w_next.
    cbn [fold_right tl w_id w_ie w_pos w_lo w_st w_drep w_ring w_q w_K w_j w_sw w_c w_pp].
    pose proof Hqs as Hqs0. unfold q_safe in Hqs. rewrite Forall_cons_iff in Hqs. destruct Hqs as [Hdd _].
    unfold d_e in Hdd. destruct Hdd as (Hll & Hml & _).
    split; [lia|]. split; [lia|]. split; [lia|].
    split; [rewrite Zlength_app, Zlength_cons, Zlength_nil; lia|].
    split; [apply (lmi_ring ie ring e0 qt); auto|].
    split; [unfold q_safe; rewrite Forall_app; split; [exact Hqts|exact Hqs0]|].
    split; [exact Hds|].
    split; [unfold LL_VMAX, ML_VMAX in *; lia|].
    split; [exact Hs'|]. split; [exact Hd'|]. split; [|split; [exact Hxl'|exact I]].
    intros seqs HD. destruct (H11 seqs HD) as (Hz & _ & _ & _). destruct (Hmd seqs HD) as (Hdm & Hq).
    split; [exact Hz|]. split; [exact Hdm|]. split; [|exact (Hm' seqs HD)].
    rewrite (lmi_peel seqs ie (ie + 8 + 1)) in Hq by lia. cbn [q_of app] in Hq.
    injection Hq as _ Hq. rewrite Hq.
    rewrite (sublist_split 0 ie (ie + 1)) by lia. rewrite sublist_len_1 by lia.
    rewrite lmi_rep_chain_app. reflexivity.
Qed.
