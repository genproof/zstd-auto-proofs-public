(* w_compressed_block, segment B, statements 16..23 (the codes and extra bits of a sequence, nseq++,
   rem -= ll + ml) in the unit valid_dict: segB_codes of WBlkBDefs_valid_dict.
   Template: WB_blkB_codes. *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.harness.valid_dict.WBlkBDefs_valid_dict.
Require Import Zstd.proof.harness.writer.WBlkBC_SibGen Zstd.proof.harness.writer.WBlkBC_SibCodes.
Local Open Scope logic.

(* ---------- one cell of a 2-D array ---------- *)

Definition blkBC_is {A} (x y: A) : Prop := x = y.

Lemma blkBC_add64 : forall a,
  Int64.add (Int64.repr a) (Int64.repr (Int.signed (Int.repr 1))) = Int64.repr (a + 1).
Proof.
  intros. unfold Int64.add. apply Int64.eqm_samerepr. apply Int64.eqm_add.
  - apply Int64.eqm_sym, Int64.eqm_unsigned_repr.
  - rewrite Int.signed_repr by rep_lia. rewrite Int64.unsigned_repr by rep_lia. apply Int64.eqm_refl.
Qed.

Lemma blkBC_rem : forall a b c,
  Int64.sub (Int64.repr a) (Int64.add (Int64.repr b) (Int64.repr c)) = Int64.repr (a - (b + c)).
Proof.
  intros.
  assert (E: Int64.add (Int64.repr b) (Int64.repr c) = Int64.repr (b + c)).
  { unfold Int64.add. apply Int64.eqm_samerepr. apply Int64.eqm_add; apply Int64.eqm_sym, Int64.eqm_unsigned_repr. }
  rewrite E. unfold Int64.sub. apply Int64.eqm_samerepr.
  apply Int64.eqm_sub; apply Int64.eqm_sym, Int64.eqm_unsigned_repr.
Qed.

Lemma blkBC_Znth_indep {A} (d1 d2: Inhabitant A) i (l: list A) :
  0 <= i < Zlength l -> @Znth A d1 i l = @Znth A d2 i l.
Proof.
  intros H. unfold Znth. destruct (Z_lt_dec i 0); [lia |]. apply nth_indep.
  rewrite Zlength_correct in H. lia.
Qed.

(* JMeq between two Znth of the same list (other Inhabitant instance, index i - 0) *)
Ltac blkBC_jmeq Hl Hr :=
  match goal with |- JMeq ?a ?b =>
    let E := fresh "E" in
    assert (E: a = b) by
      (rewrite ?Z.sub_0_r; apply blkBC_Znth_indep;
       match goal with |- 0 <= _ < @Zlength ?A ?l =>
         let HL := fresh in
         first [pose proof (Hl: @Zlength A l = _) as HL | pose proof (Hr: @Zlength A l = _) as HL]; lia end);
    rewrite E; apply JMeq_refl
  end.

(* the 2-D array rows at p without its cell [ty][n] *)
Definition blkBC_hole {cs: compspecs} (sh: share) (T: type) (N m: Z) (rows: list (list (reptype T)))
    (ty n: Z) (p: val) : mpred :=
  array_at sh (tarray (tarray T N) m) [] 0 ty (sublist 0 ty rows) p *
  array_at sh (tarray (tarray T N) m) [ArraySubsc ty] 0 n (sublist 0 n (Znth ty rows)) p *
  array_at sh (tarray (tarray T N) m) [ArraySubsc ty] (n + 1) N (sublist (n + 1) N (Znth ty rows)) p *
  array_at sh (tarray (tarray T N) m) [] (ty + 1) m (sublist (ty + 1) m rows) p.

Lemma blkBC_cell {cs: compspecs} : forall sh T N m (rows: list (list (reptype T))) ty n p,
  0 <= ty < m -> 0 <= n < N -> Zlength rows = m -> Zlength (Znth ty rows) = N ->
  data_at sh (tarray (tarray T N) m) rows p =
  blkBC_hole sh T N m rows ty n p *
  field_at sh (tarray (tarray T N) m) [ArraySubsc n; ArraySubsc ty] (Znth n (Znth ty rows)) p.
Proof.
  intros sh T N m rows ty n p Hty Hn Hl Hr.
  unfold data_at, blkBC_hole.
  erewrite field_at_Tarray; [| constructor | reflexivity | lia | apply JMeq_refl].
  rewrite (split3_array_at sh (tarray (tarray T N) m) [] 0 ty m rows (Znth ty rows));
    [| lia | rewrite Z.sub_0_r; exact Hl | blkBC_jmeq Hl Hr].
  erewrite (field_at_Tarray sh (tarray (tarray T N) m) [ArraySubsc ty]);
    [| split; [constructor | simpl; lia] | reflexivity | lia | apply JMeq_refl].
  rewrite (split3_array_at sh (tarray (tarray T N) m) [ArraySubsc ty] 0 n N (Znth ty rows)
             (Znth n (Znth ty rows)));
    [| lia | rewrite Z.sub_0_r; exact Hr | blkBC_jmeq Hl Hr].
  rewrite !Z.sub_0_r. apply pred_ext; cancel.
Qed.

Lemma blkBC_uncell {cs: compspecs} : forall sh T N m (rows: list (list (reptype T))) ty n p (v: reptype T),
  0 <= ty < m -> 0 <= n < N -> Zlength rows = m -> Zlength (Znth ty rows) = N ->
  blkBC_hole sh T N m rows ty n p *
  field_at sh (tarray (tarray T N) m) [ArraySubsc n; ArraySubsc ty] v p =
  data_at sh (tarray (tarray T N) m) (upd_Znth ty rows (upd_Znth n (Znth ty rows) v)) p.
Proof.
  intros sh T N m rows ty n p v Hty Hn Hl Hr.
  assert (Hr': 0 <= n < Zlength (Znth ty rows))
    by (split; [lia | eapply Z.lt_le_trans; [apply Hn | apply Z.eq_le_incl; symmetry; exact Hr]]).
  rewrite (blkBC_cell sh T N m (upd_Znth ty rows (upd_Znth n (Znth ty rows) v)) ty n p);
    [| lia | lia | rewrite Zlength_upd_Znth; lia | rewrite upd_Znth_same, Zlength_upd_Znth by lia; exact Hr].
  rewrite upd_Znth_same by lia. rewrite upd_Znth_same by exact Hr'.
  unfold blkBC_hole.
  rewrite upd_Znth_same by lia.
  rewrite (sublist_upd_Znth_l _ ty 0 ty) by lia.
  rewrite (sublist_upd_Znth_l _ n 0 n); [| lia | split; [lia | exact (proj2 Hr')]].
  rewrite (sublist_upd_Znth_r _ n (n + 1) N); [| lia | split; [lia | apply Z.eq_le_incl; symmetry; exact Hr]].
  rewrite (sublist_upd_Znth_r _ ty (ty + 1) m) by lia.
  reflexivity.
Qed.

(* ---------- w_code / w_extra after one more sequence ---------- *)

Definition blkBC_set (rows: list (list val)) (ty n: Z) (v: val) : list (list val) :=
  upd_Znth ty rows (upd_Znth n (Znth ty rows) v).

Definition blkBC_rows (f: Z -> sequence -> Z) (seqs: list sequence) : list (list val) :=
  map (fun ty => map (fun sq => vu (f ty sq)) seqs ++ Zrepeat Vundef (65536 - Zlength seqs)) [0; 1; 2].

Lemma blkBC_code_rows : forall seqs, code_rows seqs = blkBC_rows sq_code seqs.
Proof. reflexivity. Qed.

Lemma blkBC_extra_rows : forall seqs, extra_rows seqs = blkBC_rows sq_extra seqs.
Proof. reflexivity. Qed.

Lemma blkBC_Zrepeat_cons : forall (x: val) k, 0 < k -> Zrepeat x k = x :: Zrepeat x (k - 1).
Proof.
  intros. unfold Zrepeat. replace (Z.to_nat k) with (S (Z.to_nat (k - 1))) by lia. reflexivity.
Qed.

Lemma blkBC_row_snoc : forall (g: sequence -> val) seqs sq, Zlength seqs < 65536 ->
  map g (seqs ++ [sq]) ++ Zrepeat Vundef (65536 - Zlength (seqs ++ [sq])) =
  upd_Znth (Zlength seqs) (map g seqs ++ Zrepeat Vundef (65536 - Zlength seqs)) (g sq).
Proof.
  intros g seqs sq H.
  rewrite upd_Znth_app2 by (rewrite Zlength_map, Zlength_Zrepeat; lia).
  rewrite Zlength_map, Z.sub_diag.
  rewrite (blkBC_Zrepeat_cons Vundef (65536 - Zlength seqs)) by lia.
  rewrite upd_Znth0. rewrite map_app, <- app_assoc. simpl. f_equal. f_equal. f_equal.
  rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.

Lemma blkBC_rows_len : forall f seqs, Zlength (blkBC_rows f seqs) = 3.
Proof. reflexivity. Qed.

Lemma blkBC_rows_row : forall f seqs ty, 0 <= ty < 3 -> Zlength seqs <= 65536 ->
  Zlength (Znth ty (blkBC_rows f seqs)) = 65536.
Proof.
  intros f seqs ty Hty H. unfold blkBC_rows.
  rewrite Znth_map by (assert (Zlength [0; 1; 2] = 3) by reflexivity; lia).
  rewrite Zlength_app, Zlength_map, Zlength_Zrepeat; lia.
Qed.

Lemma blkBC_set_len : forall rows ty n v, Zlength (blkBC_set rows ty n v) = Zlength rows.
Proof. intros. unfold blkBC_set. apply Zlength_upd_Znth. Qed.

Lemma blkBC_set_row : forall rows ty n v k, 0 <= ty < Zlength rows -> 0 <= k < Zlength rows ->
  Zlength (Znth k (blkBC_set rows ty n v)) = Zlength (Znth k rows).
Proof.
  intros. unfold blkBC_set. destruct (Z.eq_dec k ty) as [-> | Hne].
  - rewrite upd_Znth_same by lia. apply Zlength_upd_Znth.
  - rewrite upd_Znth_diff by lia. reflexivity.
Qed.

Lemma blkBC_rows_snoc : forall f seqs sq, Zlength seqs < 65536 ->
  blkBC_rows f (seqs ++ [sq]) =
  blkBC_set (blkBC_set (blkBC_set (blkBC_rows f seqs) 0 (Zlength seqs) (vu (f 0 sq)))
     2 (Zlength seqs) (vu (f 2 sq))) 1 (Zlength seqs) (vu (f 1 sq)).
Proof.
  intros f seqs sq H. unfold blkBC_rows. cbn [map].
  rewrite !(blkBC_row_snoc (fun sq => vu (f _ sq))) by assumption.
  reflexivity.
Qed.

Lemma blkBC_zext : forall c, 0 <= c < 256 -> Int.zero_ext 8 (Int.repr c) = Int.repr c.
Proof.
  intros. apply zero_ext_inrange. rewrite Int.unsigned_repr by rep_lia. simpl. lia.
Qed.

Lemma blkBC_tab : forall l c, 0 <= c < Zlength l -> Znth c (uints l) = vu (zn l c).
Proof.
  intros. unfold uints. rewrite Znth_map by lia. unfold Znth, zn.
  destruct (Z_lt_dec c 0); [lia | reflexivity].
Qed.

Lemma blkBC_LL_base_len : Zlength LL_base_tab = 36.
Proof. reflexivity. Qed.
Lemma blkBC_ML_base_len : Zlength ML_base_tab = 53.
Proof. reflexivity. Qed.

Lemma blkBC_sub64 : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 32 ->
  Int.repr (Int64.Z_mod_modulus (Int64.Z_mod_modulus a - Int64.Z_mod_modulus (Int.unsigned (Int.repr b)))) =
  Int.repr (a - b).
Proof.
  intros a b Ha Hb.
  rewrite Int.unsigned_repr by rep_lia.
  rewrite !Int64.Z_mod_modulus_eq.
  rewrite (Z.mod_small a) by (change Int64.modulus with (2 ^ 64); lia).
  rewrite (Z.mod_small b) by (change Int64.modulus with (2 ^ 64); lia).
  apply Int.eqm_samerepr. unfold Int.eqm.
  apply Zbits.eqmod_divides with Int64.modulus.
  - apply Zbits.eqmod_sym, Zbits.eqmod_mod. reflexivity.
  - exists (2 ^ 32). reflexivity.
Qed.

Lemma blkBC_sub64' : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  Int.repr (Int64.Z_mod_modulus (Int64.Z_mod_modulus a - Int64.Z_mod_modulus b)) = Int.repr (a - b).
Proof.
  intros a b Ha Hb.
  rewrite !Int64.Z_mod_modulus_eq.
  rewrite (Z.mod_small a) by (change Int64.modulus with (2 ^ 64); lia).
  rewrite (Z.mod_small b) by (change Int64.modulus with (2 ^ 64); lia).
  apply Int.eqm_samerepr. unfold Int.eqm.
  apply Zbits.eqmod_divides with Int64.modulus.
  - apply Zbits.eqmod_sym, Zbits.eqmod_mod. reflexivity.
  - exists (2 ^ 32). reflexivity.
Qed.

Lemma blkBC_ov : forall a c, 0 <= a < 2 ^ 64 -> 0 <= c <= 31 ->
  Int.repr (Int64.Z_mod_modulus (Int64.Z_mod_modulus a -
    Int64.Z_mod_modulus (Z.shiftl 1 (Int64.Z_mod_modulus (Int.unsigned (Int.repr c)))))) =
  Int.repr (a - 2 ^ c).
Proof.
  intros a c Ha Hc.
  rewrite Int.unsigned_repr by rep_lia.
  rewrite (Int64.Z_mod_modulus_eq c), (Z.mod_small c) by (change Int64.modulus with (2 ^ 64); lia).
  rewrite Z.shiftl_1_l.
  apply blkBC_sub64'; [assumption |].
  split; [lia |]. apply Z.pow_lt_mono_r; lia.
Qed.

Lemma blkBC_LLb : forall c, 0 <= c < 36 -> 0 <= zn LL_base_tab c <= 65536.
Proof.
  intros c Hc. unfold zn.
  assert (HF: Forall (fun x => 0 <= x <= 65536) LL_base_tab) by (repeat constructor; lia).
  rewrite Forall_forall in HF. apply HF. apply nth_In.
  pose proof blkBC_LL_base_len as E. rewrite Zlength_correct in E. lia.
Qed.

Lemma blkBC_MLb : forall c, 0 <= c < 53 -> 0 <= zn ML_base_tab c <= 65539.
Proof.
  intros c Hc. unfold zn.
  assert (HF: Forall (fun x => 0 <= x <= 65539) ML_base_tab) by (repeat constructor; lia).
  rewrite Forall_forall in HF. apply HF. apply nth_In.
  pose proof blkBC_ML_base_len as E. rewrite Zlength_correct in E. lia.
Qed.

Lemma blkBC_Gc : forall gv,
  data_at Ers (tarray tuint 36) (uints LL_base_tab) (gv _x_valid_dict__W_LL_base) *
  (data_at Ers (tarray tuchar 36) (uints LL_bits_tab) (gv _x_valid_dict__W_LL_bits) *
   (data_at Ers (tarray tuint 53) (uints ML_base_tab) (gv _x_valid_dict__W_ML_base) *
    data_at Ers (tarray tuchar 53) (uints ML_bits_tab) (gv _x_valid_dict__W_ML_bits))) = G_codes gv.
Proof. intros. unfold G_codes. rewrite !sepcon_assoc. reflexivity. Qed.

(* blk_fixed with G_codes (the code tables) taken out *)
Definition blkBC_rest (gv: globals) : mpred :=
  G_lit gv * G_pre gv *
  data_at_ Ews (tarray (tarray tushort 65536) 3) (gv _x_valid_dict__w_st) *
  data_at_ Ews (tarray tuchar 53) (gv _x_valid_dict__need__2) *
  (EX v: list (reptype t_fse), !! Forall fse_def v &&
     data_at Ews (tarray t_fse 3) v (gv _x_valid_dict__ntab)) *
  data_at Ers (tarray tuint 3) (uints [35; 31; 52]) (gv _x_valid_dict__maxsym__1) *
  data_at Ers (tarray tuint 3) (uints [9; 8; 9]) (gv _x_valid_dict__maxlog__1) *
  data_at Ers (tarray tuint 3) (uints [2; 1; 0]) (gv _x_valid_dict__upd).

Lemma blkBC_fixed : forall gv, blk_fixed gv = G_codes gv * blkBC_rest gv.
Proof.
  intros. unfold blk_fixed, blkBC_rest.
  generalize (G_codes gv) (G_lit gv) (G_pre gv)
    (data_at_ Ews (tarray (tarray tushort 65536) 3) (gv _x_valid_dict__w_st))
    (data_at_ Ews (tarray tuchar 53) (gv _x_valid_dict__need__2))
    (EX v: list (reptype t_fse), !! Forall fse_def v && data_at Ews (tarray t_fse 3) v (gv _x_valid_dict__ntab))
    (data_at Ers (tarray tuint 3) (uints [35; 31; 52]) (gv _x_valid_dict__maxsym__1))
    (data_at Ers (tarray tuint 3) (uints [9; 8; 9]) (gv _x_valid_dict__maxlog__1))
    (data_at Ers (tarray tuint 3) (uints [2; 1; 0]) (gv _x_valid_dict__upd)).
  intros. apply pred_ext; cancel.
Qed.

Lemma segB_codes_ok : segB_codes.
Proof.
  unfold segB_codes. blkB_start.
  unfold blk_it, blk_env_ok, blk_locals, blk_bsm, hp_val in *.
  destruct E as [gv osh bsh o p cap bs tl ssh stp stv S hsh hnp hist out htl t window
                 vblk vmode vopts vvalid vforms vopts1 vbt]; blk_env_simpl.
  destruct H as (Hosh & Hbsh & Hssh & Hhsh & Hwt & Hrep & Hbh & Hbo & Hlh & Hlo & Hwin & Ht & Hhs & Hhl).
  Intros stv1 htl1 nhv.
  set (sq := {| sq_ll := ll; sq_ml := ml; sq_ov := ov |}).
  set (T := blk_tail _ cont L off ml) in *.
  assert (HT: Zlength T = ml) by (unfold T, blk_tail; rewrite lz_tail_len; lia).
  assert (Hgen: gen_ok window (wt_rep S) hist out (lits ++ L) (seqs ++ [sq]) (cont ++ L ++ T)
                  (c_rep_upd rep ll ov off))
    by (unfold T, blk_tail; cbn [be_hist be_out]; apply gen_step with (rep := rep); auto; lia).
  assert (HTb: bytes_ok T).
  { unfold T, blk_tail; cbn [be_hist be_out].
    assert (Hc: bytes_ok (out ++ cont ++ L)) by (apply Forall_app; split; [| apply Forall_app]; auto).
    pose proof (lz_copy_bytes hist (out ++ cont ++ L) off (Z.to_nat ml) Hbh Hc) as Hb.
    rewrite lz_copy_app in Hb. apply Forall_app in Hb. tauto. }
  clearbody T.
  freeze [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 14] FR.
  rewrite blkBC_fixed. flatten_sepcon_in_SEP.
  freeze [0; 4] FR2.
  forward_call (gv, ll).
  assert (Ht17: t <= 2 ^ 17) by (pose proof (Z.le_min_r window (2 ^ 17)); lia).
  assert (Hsq: seq_ok sq) by (unfold sq, seq_ok; cbn; pose proof (Zlength_nonneg cont); lia).
  assert (Hc0: 0 <= ll_code_of ll <= 35) by exact (proj1 (sq_code_facts 0 sq Hsq ltac:(lia))).
  remember (ll_code_of ll) as c0 eqn:Hc0e.
  set (n := Zlength seqs) in *.
  assert (Hn: 0 <= n < 65536) by (unfold n; pose proof (Zlength_nonneg seqs); lia).
  rewrite blkBC_code_rows, blkBC_extra_rows.
  set (CR := blkBC_rows sq_code seqs).
  set (ER := blkBC_rows sq_extra seqs).
  assert (HCRl: Zlength CR = 3) by apply blkBC_rows_len.
  assert (HCR0: Zlength (Znth 0 CR) = 65536) by (apply blkBC_rows_row; lia).
  assert (HCR1: Zlength (Znth 1 CR) = 65536) by (apply blkBC_rows_row; lia).
  assert (HCR2: Zlength (Znth 2 CR) = 65536) by (apply blkBC_rows_row; lia).
  assert (HCRe: blkBC_is CR (blkBC_rows sq_code seqs)) by reflexivity.
  clearbody CR.
  change (vl n) with (Vlong (Int64.repr n)).
  rewrite (blkBC_cell Ews tuchar 65536 3 CR 0 n) by first [exact HCR0 | exact HCRl | lia].
  Intros.
  forward.
  rewrite !blkBC_zext by lia.
  freeze [1; 2; 4] FX.
  forward.
  { entailer!; rep_lia. }
  unfold G_codes. Intros.
  remember (uints LL_base_tab) as TB0 eqn:HTB0.
  forward.
  { rewrite HTB0, blkBC_tab by (rewrite blkBC_LL_base_len; lia). entailer!. }
  rewrite HTB0, blkBC_tab by (rewrite blkBC_LL_base_len; lia).
  thaw FX.
  sep_apply (derives_refl' _ _ (blkBC_uncell Ews tuchar 65536 3 CR 0 n (gv _x_valid_dict__w_code) (vu c0)
    ltac:(lia) ltac:(lia) HCRl HCR0)).
  change (upd_Znth 0 CR (upd_Znth n (Znth 0 CR) (vu c0))) with (blkBC_set CR 0 n (vu c0)).
  assert (HERl: Zlength ER = 3) by apply blkBC_rows_len.
  assert (HER0: Zlength (Znth 0 ER) = 65536) by (apply blkBC_rows_row; lia).
  assert (HER1: Zlength (Znth 1 ER) = 65536) by (apply blkBC_rows_row; lia).
  assert (HER2: Zlength (Znth 2 ER) = 65536) by (apply blkBC_rows_row; lia).
  assert (HERe: blkBC_is ER (blkBC_rows sq_extra seqs)) by reflexivity.
  clearbody ER.
  rewrite (blkBC_cell Ews tuint 65536 3 ER 0 n) by first [exact HER0 | exact HERl | lia].
  Intros.
  forward.
  rewrite blkBC_sub64 by (pose proof (blkBC_LLb c0 ltac:(lia)); rep_lia).
  sep_apply (derives_refl' _ _ (blkBC_uncell Ews tuint 65536 3 ER 0 n (gv _x_valid_dict__w_extra)
    (vu (ll - zn LL_base_tab c0)) ltac:(lia) ltac:(lia) HERl HER0)).
  change (upd_Znth 0 ER (upd_Znth n (Znth 0 ER) (vu (ll - zn LL_base_tab c0))))
    with (blkBC_set ER 0 n (vu (ll - zn LL_base_tab c0))).
  (* the match length *)
  gather_SEP 3 4 5 6. rewrite blkBC_Gc.
  forward_call (gv, ml).
  assert (Hc2: 0 <= ml_code_of ml <= 52) by exact (proj1 (sq_code_facts 2 sq Hsq ltac:(lia))).
  remember (ml_code_of ml) as c2 eqn:Hc2e.
  set (CR1 := blkBC_set CR 0 n (vu c0)).
  assert (HCR1l: Zlength CR1 = 3) by (unfold CR1; rewrite blkBC_set_len; exact HCRl).
  assert (HCR12: Zlength (Znth 2 CR1) = 65536) by (unfold CR1; rewrite blkBC_set_row by lia; exact HCR2).
  assert (HCR11: Zlength (Znth 1 CR1) = 65536) by (unfold CR1; rewrite blkBC_set_row by lia; exact HCR1).
  assert (HCR1e: blkBC_is CR1 (blkBC_set CR 0 n (vu c0))) by reflexivity.
  clearbody CR1.
  set (ER1 := blkBC_set ER 0 n (vu (ll - zn LL_base_tab c0))).
  assert (HER1l: Zlength ER1 = 3) by (unfold ER1; rewrite blkBC_set_len; exact HERl).
  assert (HER12: Zlength (Znth 2 ER1) = 65536) by (unfold ER1; rewrite blkBC_set_row by lia; exact HER2).
  assert (HER11: Zlength (Znth 1 ER1) = 65536) by (unfold ER1; rewrite blkBC_set_row by lia; exact HER1).
  assert (HER1e: blkBC_is ER1 (blkBC_set ER 0 n (vu (ll - zn LL_base_tab c0)))) by reflexivity.
  clearbody ER1.
  rewrite (blkBC_cell Ews tuchar 65536 3 CR1 2 n) by first [exact HCR12 | exact HCR1l | lia].
  Intros.
  forward.
  rewrite !blkBC_zext by lia.
  freeze [1; 2; 4] FX.
  forward.
  { entailer!; rep_lia. }
  unfold G_codes. Intros.
  remember (uints ML_base_tab) as TB2 eqn:HTB2.
  forward.
  { rewrite HTB2, blkBC_tab by (rewrite blkBC_ML_base_len; lia). entailer!. }
  rewrite HTB2, blkBC_tab by (rewrite blkBC_ML_base_len; lia).
  thaw FX.
  sep_apply (derives_refl' _ _ (blkBC_uncell Ews tuchar 65536 3 CR1 2 n (gv _x_valid_dict__w_code) (vu c2)
    ltac:(lia) ltac:(lia) HCR1l HCR12)).
  change (upd_Znth 2 CR1 (upd_Znth n (Znth 2 CR1) (vu c2))) with (blkBC_set CR1 2 n (vu c2)).
  rewrite (blkBC_cell Ews tuint 65536 3 ER1 2 n) by first [exact HER12 | exact HER1l | lia].
  Intros.
  forward.
  rewrite blkBC_sub64 by (pose proof (blkBC_MLb c2 ltac:(lia)); rep_lia).
  sep_apply (derives_refl' _ _ (blkBC_uncell Ews tuint 65536 3 ER1 2 n (gv _x_valid_dict__w_extra)
    (vu (ml - zn ML_base_tab c2)) ltac:(lia) ltac:(lia) HER1l HER12)).
  change (upd_Znth 2 ER1 (upd_Znth n (Znth 2 ER1) (vu (ml - zn ML_base_tab c2))))
    with (blkBC_set ER1 2 n (vu (ml - zn ML_base_tab c2))).
  (* the offset *)
  gather_SEP 3 4 5 6. rewrite blkBC_Gc.
  forward_call ov.
  assert (Hc1: 0 <= Z.log2 ov <= 31) by exact (proj1 (sq_code_facts 1 sq Hsq ltac:(lia))).
  remember (Z.log2 ov) as c1 eqn:Hc1e.
  set (CR2 := blkBC_set CR1 2 n (vu c2)).
  assert (HCR2l: Zlength CR2 = 3) by (unfold CR2; rewrite blkBC_set_len; exact HCR1l).
  assert (HCR21: Zlength (Znth 1 CR2) = 65536) by (unfold CR2; rewrite blkBC_set_row by lia; exact HCR11).
  assert (HCR2e: blkBC_is CR2 (blkBC_set CR1 2 n (vu c2))) by reflexivity.
  clearbody CR2.
  set (ER2 := blkBC_set ER1 2 n (vu (ml - zn ML_base_tab c2))).
  assert (HER2l: Zlength ER2 = 3) by (unfold ER2; rewrite blkBC_set_len; exact HER1l).
  assert (HER21: Zlength (Znth 1 ER2) = 65536) by (unfold ER2; rewrite blkBC_set_row by lia; exact HER11).
  assert (HER2e: blkBC_is ER2 (blkBC_set ER1 2 n (vu (ml - zn ML_base_tab c2)))) by reflexivity.
  clearbody ER2.
  rewrite (blkBC_cell Ews tuchar 65536 3 CR2 1 n) by first [exact HCR21 | exact HCR2l | lia].
  Intros.
  forward.
  rewrite !blkBC_zext by lia.
  freeze [0; 1; 2; 4] FX.
  forward.
  { entailer!; rep_lia. }
  thaw FX.
  sep_apply (derives_refl' _ _ (blkBC_uncell Ews tuchar 65536 3 CR2 1 n (gv _x_valid_dict__w_code) (vu c1)
    ltac:(lia) ltac:(lia) HCR2l HCR21)).
  change (upd_Znth 1 CR2 (upd_Znth n (Znth 1 CR2) (vu c1))) with (blkBC_set CR2 1 n (vu c1)).
  rewrite (blkBC_cell Ews tuint 65536 3 ER2 1 n) by first [exact HER21 | exact HER2l | lia].
  Intros.
  freeze [0; 1; 4] FX.
  forward.
  { entailer!. change (Int.unsigned Int64.iwordsize') with 64. lia. }
  rewrite blkBC_ov by rep_lia.
  thaw FX.
  sep_apply (derives_refl' _ _ (blkBC_uncell Ews tuint 65536 3 ER2 1 n (gv _x_valid_dict__w_extra)
    (vu (ov - 2 ^ c1)) ltac:(lia) ltac:(lia) HER2l HER21)).
  change (upd_Znth 1 ER2 (upd_Znth n (Znth 1 ER2) (vu (ov - 2 ^ c1))))
    with (blkBC_set ER2 1 n (vu (ov - 2 ^ c1))).
  forward.
  forward.
  (* the loop invariant *)
  assert (HCRf: blkBC_set CR2 1 n (vu c1) = code_rows (seqs ++ [sq])).
  { unfold blkBC_is in *. rewrite HCR2e, HCR1e, HCRe.
    change (code_rows (seqs ++ [sq])) with (blkBC_rows sq_code (seqs ++ [sq])).
    rewrite blkBC_rows_snoc by lia.
    subst c0 c1 c2. reflexivity. }
  assert (HERf: blkBC_set ER2 1 n (vu (ov - 2 ^ c1)) = extra_rows (seqs ++ [sq])).
  { unfold blkBC_is in *. rewrite HER2e, HER1e, HERe.
    change (extra_rows (seqs ++ [sq])) with (blkBC_rows sq_extra (seqs ++ [sq])).
    rewrite blkBC_rows_snoc by lia.
    subst c0 c1 c2. reflexivity. }
  rewrite HCRf, HERf.
  rewrite blkBC_add64, blkBC_rem.
  thaw FR2. thaw FR.
  unfold blkB_inv, blk_gen.
  Exists (seqs ++ [sq]) (lits ++ L) (cont ++ L ++ T) (c_rep_upd rep ll ov off).
  Exists stv1 htl1 nhv.
  rewrite blkBC_fixed.
  cbn [be_gv be_osh be_bsh be_o be_p be_cap be_bs be_tl be_ssh be_stp be_stv be_S be_hsh be_hnp be_hist
       be_out be_htl be_t be_window be_vblk be_vmode be_vopts be_vvalid be_vforms be_vopts1 be_vb].
  unfold blk_bsm, blk_locals, hp_val. blk_env_simpl.
  replace (Zlength (seqs ++ [sq])) with (n + 1)
    by (unfold n; rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  replace (Zlength (lits ++ L)) with (Zlength lits + Zlength L) by (rewrite Zlength_app; lia).
  replace (t - Zlength (cont ++ L ++ T)) with (t - Zlength cont - (ll + ml)) by (rewrite !Zlength_app; lia).
  replace (Zlength hist + Zlength out + Zlength (cont ++ L ++ T))
    with (Zlength hist + Zlength out + Zlength cont + Zlength L + ml) by (rewrite !Zlength_app; lia).
  set (Xe := data_at Ews (tarray (tarray tuint 65536) 3) (extra_rows (seqs ++ [sq])) (gv _x_valid_dict__w_extra)).
  set (Xc := data_at Ews (tarray (tarray tuchar 65536) 3) (code_rows (seqs ++ [sq])) (gv _x_valid_dict__w_code)).
  set (Xb := out_rep Tsh Ews vblk (gv _x_valid_dict__blk_buf) 135168 [] (Zrepeat Vundef 135168)).
  set (Xh := data_at Ews (tarray tuchar HIST_SIZE) (zbytes (hist ++ out ++ cont ++ L ++ T) ++ htl1)
               (gv _x_valid_dict__w_hist)).
  set (Xl := data_at Ews (tarray tuchar 131072)
               (zbytes (lits ++ L) ++ Zrepeat Vundef (131072 - (Zlength lits + Zlength L)))
               (gv _x_valid_dict__w_lit)).
  clearbody Xe Xc Xb Xh Xl.
  entailer!.
  split; [apply Forall_app; split; [assumption | constructor; [assumption | constructor]] |].
  split; [apply Forall_app; split; assumption |].
  split; [apply Forall_app; split; [assumption | apply Forall_app; split; assumption] |].
  rewrite !Zlength_app. lia.
Qed.
