(* Group ENT: body of FSE_decompress_usingDTable_generic. *)
Require Import Zstd.proof.dec.B.ent.EntSpecs.
Local Open Scope logic.

(* ---------- pure facts ---------- *)
Local Open Scope Z_scope.

Lemma ent_mod_mul_r a b c : 0 < b -> 0 < c -> a mod (b * c) = a mod b + b * ((a / b) mod c).
Proof.
  intros Hb Hc. symmetry. apply Z.mod_unique with (q := a / b / c).
  - left. pose proof (Z.mod_pos_bound a b Hb). pose proof (Z.mod_pos_bound (a / b) c Hc). nia.
  - pose proof (Z.div_mod a b ltac:(lia)). pose proof (Z.div_mod (a / b) c ltac:(lia)). nia.
Qed.

Lemma ent_low_div a lo nb : 0 <= lo -> 0 <= nb -> (a mod 2 ^ (lo + nb)) / 2 ^ lo = (a / 2 ^ lo) mod 2 ^ nb.
Proof.
  intros. rewrite Z.pow_add_r by lia. rewrite ent_mod_mul_r by lia.
  rewrite Z.mul_comm, Z.div_add by lia. rewrite Z.div_small. lia.
  apply Z.mod_pos_bound; lia.
Qed.

Lemma ent_mod_mod a x y : 0 <= y <= x -> (a mod 2 ^ x) mod 2 ^ y = a mod 2 ^ y.
Proof.
  intros. replace x with (y + (x - y)) by lia. rewrite Z.pow_add_r by lia.
  rewrite ent_mod_mul_r by lia. rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_mod; lia.
Qed.

Lemma le_value_split m l : bytes_ok l ->
  le_value l = le_value (firstn m l) + 2 ^ (8 * Z.of_nat m) * le_value (skipn m l) /\
  0 <= le_value (firstn m l) < 2 ^ (8 * Z.of_nat m).
Proof.
  revert l; induction m as [|m IH]; intros l Hl.
  - simpl. split; lia.
  - destruct l as [|b l']; cbn [firstn skipn le_value].
    + split; [lia|]. split; [lia|]. apply Z.pow_pos_nonneg; lia.
    + inversion Hl; subst. destruct (IH l' H2) as [E B]. unfold is_byte in H1.
      rewrite Nat2Z.inj_succ. replace (8 * Z.succ (Z.of_nat m)) with (8 + 8 * Z.of_nat m) by lia.
      rewrite Z.pow_add_r by lia.
      change (2 ^ 8) with 256. rewrite E. split; nia.
Qed.

Lemma le_value_nonneg l : bytes_ok l -> 0 <= le_value l.
Proof.
  intros Hl. destruct (le_value_split (length l) l Hl) as [E B].
  rewrite firstn_all in B. lia.
Qed.

Lemma le_value_firstn m l : bytes_ok l -> le_value (firstn m l) = le_value l mod 2 ^ (8 * Z.of_nat m).
Proof.
  intros Hl. destruct (le_value_split m l Hl) as [E B]. apply Z.mod_unique with (q := le_value (skipn m l)).
  left; lia. lia.
Qed.

Lemma le_value_skipn m l : bytes_ok l -> le_value (skipn m l) = le_value l / 2 ^ (8 * Z.of_nat m).
Proof.
  intros Hl. destruct (le_value_split m l Hl) as [E B]. apply Z.div_unique with (r := le_value (firstn m l)).
  left; lia. lia.
Qed.

Lemma bytes_ok_skipn m l : bytes_ok l -> bytes_ok (skipn m l).
Proof.
  revert l; induction m; intros l Hl; simpl; auto. destruct l; auto. inversion Hl; auto.
Qed.

(* the model's fast peek is the bitstream's peek (reads of at most 12 bits, inside the stream) *)
Lemma bs_peek_s_eq s pos nb : bytes_ok s -> 0 <= nb <= 12 -> nb <= pos ->
  bs_peek_s s pos nb = bs_peek (bs_value s) pos nb.
Proof.
  intros Hs Hnb Hp. unfold bs_peek_s, bs_peek, bs_value, slice.
  destruct (pos <? 0) eqn:E0; [lia|]. destruct (pos - nb >=? 0) eqn:E1; [|lia].
  set (lo := pos - nb).
  rewrite le_value_firstn by (apply bytes_ok_skipn; auto).
  rewrite le_value_skipn by auto.
  rewrite (Z2Nat.id 5) by lia. rewrite (Z2Nat.id (lo / 8)) by (apply Z.div_pos; unfold lo; lia).
  set (V := le_value s). pose proof (Z.mod_pos_bound lo 8 ltac:(lia)) as Hr.
  assert (Hlo: lo = 8 * (lo / 8) + lo mod 8) by (apply Z.div_mod; lia).
  assert (Hl8: 0 <= lo / 8) by (apply Z.div_pos; lia).
  assert (R: (V mod 2 ^ pos) * 2 ^ nb / 2 ^ pos = (V / 2 ^ lo) mod 2 ^ nb).
  { rewrite <- (ent_low_div V lo nb) by lia. replace (lo + nb) with pos by (unfold lo; lia).
    replace (2 ^ pos) with (2 ^ lo * 2 ^ nb) at 2 by (rewrite <- Z.pow_add_r by lia; f_equal; unfold lo; lia).
    rewrite Z.div_mul_cancel_r; auto; apply Z.pow_nonzero; lia. }
  assert (L: ((V / 2 ^ (8 * (lo / 8))) mod 2 ^ (8 * 5) / 2 ^ (lo mod 8)) mod 2 ^ nb = (V / 2 ^ lo) mod 2 ^ nb).
  { replace (8 * 5) with (lo mod 8 + (40 - lo mod 8)) by lia. rewrite ent_low_div by lia.
    rewrite ent_mod_mod by lia.
    rewrite Z.div_div by (try apply Z.pow_nonzero; try apply Z.pow_pos_nonneg; lia).
    rewrite <- Z.pow_add_r by lia. rewrite <- Hlo. reflexivity. }
  rewrite L, R. reflexivity.
Qed.

(* ---------- BIT_reloadDStream ---------- *)

Lemma reload_ok pos lo : 0 <= lo -> lo mod 8 = 0 -> lo <= pos ->
  fst (bs_reload pos lo) <> BIT_overflow /\
  0 <= snd (bs_reload pos lo) <= pos /\
  (fst (bs_reload pos lo) = BIT_unfinished -> 57 <= pos - snd (bs_reload pos lo)) /\
  (fst (bs_reload pos lo) <> BIT_unfinished -> snd (bs_reload pos lo) = 0) /\
  (snd (bs_reload pos lo) = 0 \/ 57 <= pos - snd (bs_reload pos lo)).
Proof.
  intros H0 H8 Hp. unfold bs_reload, BIT_overflow, BIT_unfinished, BIT_endOfBuffer, BIT_completed.
  destruct (pos <? lo) eqn:E; [lia|].
  assert (Hd: lo = 8 * (lo / 8)) by (pose proof (Z.div_mod lo 8 ltac:(lia)); lia).
  set (k := lo / 8) in *. set (nb := (lo + 64 - pos) / 8).
  assert (Hnb: lo + 64 - pos - 7 <= 8 * nb <= lo + 64 - pos)
    by (pose proof (Z.div_mod (lo + 64 - pos) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (lo + 64 - pos) 8 ltac:(lia)); unfold nb; lia).
  destruct (8 <=? k) eqn:E8; simpl.
  - assert (nb <= 8) by (unfold nb; apply Z.div_le_upper_bound; lia). lia.
  - destruct (k =? 0) eqn:Ek; simpl.
    + destruct (0 <? pos); simpl; lia.
    + destruct (k <? nb) eqn:Ekn; simpl; lia.
Qed.

Lemma reload_range pos lo : 0 <= fst (bs_reload pos lo) <= 3.
Proof.
  unfold bs_reload, BIT_overflow, BIT_unfinished, BIT_endOfBuffer, BIT_completed.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; simpl; lia.
Qed.

Lemma reload_overflow pos lo : pos < lo -> fst (bs_reload pos lo) = BIT_overflow /\ snd (bs_reload pos lo) = lo.
Proof. intros. unfold bs_reload. destruct (pos <? lo) eqn:E; [auto|lia]. Qed.

(* ---------- the model loop ---------- *)

Definition ent_fin (o: option (list Z)) : option (list Z) :=
  match o with Some ws => if Zlength ws >? 255 then None else Some ws | None => None end.

Lemma fse2_loop_len f t V pos s1 s2 acc ws :
  fse2_loop f t V pos s1 s2 acc = Some ws -> Zlength acc + 2 <= Zlength ws.
Proof.
  revert pos s1 s2 acc; induction f as [|f IH]; intros pos s1 s2 acc H; cbn [fse2_loop] in H; [discriminate|].
  destruct (_ <? 0).
  - inversion H; subst. rewrite !Zlength_app, !Zlength_cons, !Zlength_nil. lia.
  - destruct (_ <? 0).
    + inversion H; subst. rewrite !Zlength_app, !Zlength_cons, !Zlength_nil. lia.
    + apply IH in H. rewrite !Zlength_app, !Zlength_cons, !Zlength_nil in H. lia.
Qed.

Lemma fse2_step f t V pos s1 s2 acc :
  0 <= pos - fe_nb (fse_cell t s1) ->
  0 <= pos - fe_nb (fse_cell t s1) - fe_nb (fse_cell t s2) ->
  fse2_loop (S f) t V pos s1 s2 acc =
  fse2_loop f t V (pos - fe_nb (fse_cell t s1) - fe_nb (fse_cell t s2))
    (fe_base (fse_cell t s1) + bs_peek_s V pos (fe_nb (fse_cell t s1)))
    (fe_base (fse_cell t s2) + bs_peek_s V (pos - fe_nb (fse_cell t s1)) (fe_nb (fse_cell t s2)))
    ((acc ++ [fe_sym (fse_cell t s1)]) ++ [fe_sym (fse_cell t s2)]).
Proof.
  intros H1 H2. cbn [fse2_loop].
  destruct (pos - fe_nb (fse_cell t s1) <? 0) eqn:E1; [lia|].
  destruct (pos - fe_nb (fse_cell t s1) - fe_nb (fse_cell t s2) <? 0) eqn:E2; [lia|].
  rewrite !Z.sub_add. reflexivity.
Qed.

Lemma fse2_stop1 f t V pos s1 s2 acc :
  pos - fe_nb (fse_cell t s1) < 0 ->
  fse2_loop (S f) t V pos s1 s2 acc = Some ((acc ++ [fe_sym (fse_cell t s1)]) ++ [fe_sym (fse_cell t s2)]).
Proof. intros H1. cbn [fse2_loop]. destruct (_ <? 0) eqn:E1; [reflexivity|lia]. Qed.

Lemma fse2_stop2 f t V pos s1 s2 acc :
  0 <= pos - fe_nb (fse_cell t s1) ->
  pos - fe_nb (fse_cell t s1) - fe_nb (fse_cell t s2) < 0 ->
  fse2_loop (S f) t V pos s1 s2 acc =
  Some (((acc ++ [fe_sym (fse_cell t s1)]) ++ [fe_sym (fse_cell t s2)]) ++
        [fe_sym (fse_cell t (fe_base (fse_cell t s1) + bs_peek_s V pos (fe_nb (fse_cell t s1))))]).
Proof.
  intros H1 H2. cbn [fse2_loop].
  destruct (pos - fe_nb (fse_cell t s1) <? 0) eqn:E1; [lia|].
  destruct (pos - fe_nb (fse_cell t s1) - fe_nb (fse_cell t s2) <? 0) eqn:E2; [|lia].
  rewrite !Z.sub_add. reflexivity.
Qed.


Local Open Scope logic.

(* ---------- separation-logic facts ---------- *)

Lemma win_split sh N c off s base :
  field_compatible (tarray tuchar N) [] base -> win_ok sh N c off (Zlength s) s ->
  data_at sh (tarray tuchar N) c base =
  data_at sh (tarray tuchar off) (sublist 0 off c) base *
  bit_src sh (offset_val off base) s *
  data_at sh (tarray tuchar (N - (off + Zlength s))) (sublist (off + Zlength s) N c)
    (offset_val (off + Zlength s) base).
Proof.
  intros Hfc (Hsh & Hoff & Hn & HN & Hc & _ & Hbytes & Hwin). pose proof (Zlength_nonneg s).
  unfold tarray. rewrite (split3_data_at_Tarray_tuchar sh N off (off + Zlength s) c base) by lia.
  rewrite !field_address0_offset by auto with field_compatible.
  simpl nested_field_offset. rewrite !Z.add_0_l, !Z.mul_1_l.
  unfold bit_src. rewrite Hwin. replace (off + Zlength s - off) with (Zlength s) by lia.
  reflexivity.
Qed.

Lemma rep_bit_inv sh gv s start pos lo p :
  BIT_DStream_rep sh gv s start pos lo p |-- !! bit_inv s pos lo.
Proof. unfold BIT_DStream_rep. Intros ptr lim. entailer!. Qed.

Lemma rep_data_at_ sh gv s start pos lo p :
  BIT_DStream_rep sh gv s start pos lo p |-- data_at_ sh t_bitd p.
Proof. unfold BIT_DStream_rep. Intros ptr lim. unfold t_bitd. cancel. Qed.

Lemma bs_okb_wf s : bytes_ok s -> bs_okb s = bs_wf s.
Proof.
  intros Hs. unfold bs_okb, bs_wf.
  replace (forallb (fun b => andb (0 <=? b) (b <? 256)) s) with true.
  2:{ symmetry. apply forallb_forall. intros x Hx. unfold bytes_ok in Hs. rewrite Forall_forall in Hs. apply Hs in Hx.
      unfold is_byte in Hx. lia. }
  rewrite Zlength_correct. simpl. destruct (length s); reflexivity.
Qed.


(* ---------- the model's start ---------- *)
Local Open Scope Z_scope.

Lemma bs_total_lo s : bs_wf s = true -> bytes_ok s ->
  0 <= bs_total s /\ (8 * Z.max 0 (Zlength s - 8) = 0 \/ 56 <= bs_total s - 8 * Z.max 0 (Zlength s - 8)).
Proof.
  intros Hwf Hs. unfold bs_total, highbit. rewrite <- Zlength_correct.
  pose proof (Z.log2_nonneg (last s 0)).
  unfold bs_wf in Hwf. apply andb_prop in Hwf. destruct Hwf as [Hz _].
  pose proof (Zlength_nonneg s). destruct (Zlength s =? 0) eqn:E; [discriminate|]. apply Z.eqb_neq in E.
  split; [lia|]. destruct (Z.max_spec 0 (Zlength s - 8)) as [[? ->]|[? ->]]; lia.
Qed.

Lemma wdec_nowf t s : bs_wf s = false -> bytes_ok s -> fse_weights_dec t s = None.
Proof. intros Hwf Hs. unfold fse_weights_dec. rewrite bs_okb_wf, Hwf by auto. reflexivity. Qed.

Lemma wdec_short t s : bs_wf s = true -> bytes_ok s -> bs_total s - 2 * ft_log t < 0 -> fse_weights_dec t s = None.
Proof.
  intros Hwf Hs Hl. unfold fse_weights_dec. rewrite bs_okb_wf, Hwf by auto. cbv beta iota zeta delta [negb].
  destruct (bs_total s - 2 * ft_log t <? 0) eqn:E; [reflexivity|lia].
Qed.

Lemma wdec_start t s : bs_wf s = true -> bytes_ok s -> 0 <= bs_total s - 2 * ft_log t ->
  fse_weights_dec t s =
  ent_fin (fse2_loop 256 t s (bs_total s - 2 * ft_log t) (bs_peek_s s (bs_total s) (ft_log t))
             (bs_peek_s s (bs_total s - ft_log t) (ft_log t)) nil).
Proof.
  intros Hwf Hs Hl. unfold fse_weights_dec. rewrite bs_okb_wf, Hwf by auto. cbv beta iota zeta delta [negb].
  destruct (bs_total s - 2 * ft_log t <? 0) eqn:E; [lia|]. unfold ent_fin. reflexivity.
Qed.

Lemma len4 (k: Z) : k mod 4 = 0 -> k < 252 -> 0 <= k ->
  (k + 1 + 1 + 1 + 1) mod 4 = 0 /\ 4 <= k + 1 + 1 + 1 + 1 <= 252.
Proof.
  intros H1 H2 H3. pose proof (Z.div_mod k 4 ltac:(lia)). rewrite H1 in H.
  replace (k + 1 + 1 + 1 + 1) with ((k / 4 + 1) * 4) by lia. rewrite Z_mod_mult. lia.
Qed.

Lemma is_error_small n : 0 <= n <= 2 ^ 63 - 1 -> is_error_code n = false.
Proof. intros. unfold is_error_code. apply Z.ltb_ge. lia. Qed.

Local Open Scope logic.

Lemma neg_code_repr k : 0 < k < 2 ^ 63 -> Vlong (Int64.repr (- k)) = Vlong (Int64.repr (2 ^ 64 - k)).
Proof.
  intros. f_equal. apply Int64.eqm_samerepr. unfold Int64.eqm, Zbits.eqmod. exists (-1).
  change Int64.modulus with (2 ^ 64). lia.
Qed.

Lemma ent_ptr_ltu pw k j : field_compatible (Tarray tuchar 256 noattr) [] pw -> 0 <= k <= 256 -> 0 <= j <= 256 ->
  exists b i, pw = Vptr b i /\ offset_val k pw = Vptr b (Ptrofs.add i (Ptrofs.repr k)) /\
    offset_val j pw = Vptr b (Ptrofs.add i (Ptrofs.repr j)) /\
    Ptrofs.ltu (Ptrofs.add i (Ptrofs.repr k)) (Ptrofs.add i (Ptrofs.repr j)) = (k <? j)%Z.
Proof.
  intros Hfc Hk Hj. destruct Hfc as (Hp & _ & Hsz & _). destruct pw; try contradiction.
  exists b, i. split; [auto|]. split; [auto|]. split; [auto|].
  unfold size_compatible in Hsz. simpl sizeof in Hsz. pose proof (Ptrofs.unsigned_range i).
  unfold Ptrofs.ltu. rewrite !Ptrofs.add_unsigned, !Ptrofs.unsigned_repr by (rewrite ?Ptrofs.unsigned_repr; rep_lia).
  destruct (zlt _ _); destruct (k <? j)%Z eqn:E; auto; lia.
Qed.

Lemma ent_cmp_lt pw k j : field_compatible (Tarray tuchar 256 noattr) [] pw -> 0 <= k <= 256 -> 0 <= j <= 256 ->
  sem_cmp_pp Clt (offset_val k pw) (offset_val j pw) = Some (bool2val (k <? j)%Z).
Proof.
  intros Hfc Hk Hj. destruct (ent_ptr_ltu pw k j Hfc Hk Hj) as (b & i & -> & E1 & E2 & E3).
  rewrite E1, E2. unfold sem_cmp_pp. simpl. destruct (eq_block b b); [|congruence]. simpl.
  unfold Ptrofs.cmpu. rewrite E3. reflexivity.
Qed.

Lemma ent_cmp_gt pw k j : field_compatible (Tarray tuchar 256 noattr) [] pw -> 0 <= k <= 256 -> 0 <= j <= 256 ->
  sem_cmp_pp Cgt (offset_val k pw) (offset_val j pw) = Some (bool2val (j <? k)%Z).
Proof.
  intros Hfc Hk Hj. destruct (ent_ptr_ltu pw j k Hfc Hj Hk) as (b & i & -> & E1 & E2 & E3).
  rewrite E1, E2. unfold sem_cmp_pp. simpl. destruct (eq_block b b); [|congruence]. simpl.
  unfold Ptrofs.cmpu. rewrite E3. reflexivity.
Qed.

Lemma out_test_order shw pw l k j R : writable_share shw -> 0 <= k <= 256 -> 0 <= j <= 256 ->
  data_at shw (tarray tuchar 256) l pw * R |-- denote_tc_test_order (offset_val k pw) (offset_val j pw).
Proof.
  intros Hsh Hk Hj. assert_PROP (isptr pw) as Hp by entailer!.
  rewrite isptr_denote_tc_test_order by (destruct pw; try contradiction; exact I).
  unfold test_order_ptrs. destruct pw; try contradiction. simpl. unfold sameblock.
  destruct (peq b b); [|congruence]. simpl.
  apply andp_right; apply sepcon_weak_valid_pointer1;
    (eapply derives_trans; [apply data_at_memory_block|]); simpl sizeof;
    change (Vptr b (Ptrofs.add i (Ptrofs.repr ?x))) with (offset_val x (Vptr b i));
    apply memory_block_weak_valid_pointer; auto; try lia; apply writable_nonidentity; auto.
Qed.

Lemma out_split shw pw (l: list val) k : Zlength l = 256 -> 0 <= k <= 256 ->
  field_compatible (tarray tuchar 256) [] pw ->
  data_at shw (tarray tuchar 256) l pw =
  data_at shw (tarray tuchar k) (sublist 0 k l) pw *
  data_at shw (tarray tuchar (256 - k)) (sublist k 256 l) (offset_val k pw).
Proof.
  intros Hl Hk Hfc. unfold tarray. rewrite (split2_data_at_Tarray_tuchar shw 256 k l pw) by lia.
  rewrite field_address0_offset by auto with field_compatible. simpl nested_field_offset.
  rewrite Z.add_0_l, Z.mul_1_l. reflexivity.
Qed.

Lemma cell_P (P: fse_entry -> Prop) t st : Zlength (ft_cells t) = 2 ^ ft_log t -> Forall P (ft_cells t) ->
  0 <= st < 2 ^ ft_log t -> P (fse_cell t st).
Proof.
  intros Hl HP Hs. unfold fse_cell. rewrite Forall_forall in HP. apply HP. apply nth_In.
  rewrite Zlength_correct in Hl. lia.
Qed.

Lemma ze8 y : 0 <= y < 256 -> Int.zero_ext 8 (Int.repr y) = Int.repr y.
Proof.
  intros. rewrite <- (Int.repr_unsigned (Int.zero_ext 8 (Int.repr y))).
  rewrite Int.zero_ext_mod by (cbn; lia). rewrite Int.unsigned_repr by rep_lia.
  rewrite Z.mod_small; [reflexivity|]. change (two_p 8) with 256. lia.
Qed.

Lemma upd4_eq (acc: list Z) (oc: list val) y1 y2 y3 y4 : Zlength oc = 256 -> Zlength acc + 4 <= 256 ->
  upd_Znth 3 (upd_Znth 2 (upd_Znth 1 (upd_Znth 0 (sublist (Zlength acc) 256 oc) (Vint (Int.repr y1)))
     (Vint (Int.repr y2))) (Vint (Int.repr y3))) (Vint (Int.repr y4))
  = sublist (Zlength acc) 256 (zbytes ((((acc ++ [y1]) ++ [y2]) ++ [y3]) ++ [y4]) ++
      sublist (Zlength ((((acc ++ [y1]) ++ [y2]) ++ [y3]) ++ [y4])) 256 oc).
Proof. intros. list_solve. Qed.

Lemma pre_eq (acc acc2: list Z) (oc: list val) : Zlength oc = 256 -> Zlength (acc ++ acc2) <= 256 ->
  sublist 0 (Zlength acc) (zbytes (acc ++ acc2) ++ sublist (Zlength (acc ++ acc2)) 256 oc) = zbytes acc.
Proof. intros. list_solve. Qed.

Lemma sub2 p : isptr p -> force_val (sem_sub_pi tuchar Signed (offset_val 255 p) (Vint (Int.repr 2))) = offset_val 253 p.
Proof.
  intros Hp. destruct p; try contradiction. simpl. f_equal.
  rewrite Ptrofs.sub_add_opp, Ptrofs.add_assoc. f_equal. apply Ptrofs.same_if_eq; vm_compute; reflexivity.
Qed.

Lemma out3 shw pw (l: list val) k : Zlength l = 256 -> 0 <= k < 256 ->
  field_compatible (tarray tuchar 256) [] pw ->
  data_at shw (tarray tuchar 256) l pw =
  data_at shw (tarray tuchar k) (sublist 0 k l) pw *
  data_at shw tuchar (Znth k l) (offset_val k pw) *
  data_at shw (tarray tuchar (256 - (k + 1))) (sublist (k + 1) 256 l) (offset_val (k + 1) pw).
Proof.
  intros Hl Hk Hfc. unfold tarray. rewrite (split3_data_at_Tarray_tuchar shw 256 k (k + 1) l pw) by lia.
  rewrite !field_address0_offset by auto with field_compatible. simpl nested_field_offset.
  rewrite !Z.add_0_l, !Z.mul_1_l. replace (k + 1 - k) with 1 by lia.
  rewrite (sublist_one k (k + 1) l) by lia. change (Tarray tuchar 1 noattr) with (tarray tuchar 1).
  rewrite (data_at_singleton_array_eq shw tuchar (Znth k l) [Znth k l]) by reflexivity.
  reflexivity.
Qed.

Lemma fin_none f t V pos s1 s2 acc : 254 <= Zlength acc -> ent_fin (fse2_loop f t V pos s1 s2 acc) = None.
Proof.
  intros. destruct (fse2_loop f t V pos s1 s2 acc) as [ws|] eqn:E; [|reflexivity].
  apply fse2_loop_len in E. unfold ent_fin. destruct (Zlength ws >? 255) eqn:G; [reflexivity|lia].
Qed.

Lemma fin_some ws : Zlength ws <= 255 -> ent_fin (Some ws) = Some ws.
Proof. intros. unfold ent_fin. destruct (Zlength ws >? 255) eqn:G; [lia|reflexivity]. Qed.

Definition gt_val (k: Z) (pw: val) : val := force_val (sem_cmp_pp Cgt (offset_val k pw) (offset_val 253 pw)).

Lemma gt_cond k pw : field_compatible (Tarray tuchar 256 noattr) [] pw -> 0 <= k <= 256 ->
  (typed_true tint (gt_val k pw) -> 253 < k) /\ (typed_false tint (gt_val k pw) -> k <= 253).
Proof.
  intros Hfc Hk. unfold gt_val. rewrite ent_cmp_gt by (auto; lia). simpl force_val.
  destruct (253 <? k)%Z eqn:E; unfold typed_true, typed_false; simpl; split; intros Ht; try discriminate; lia.
Qed.

Lemma out_split1 shw pw (acc: list Z) (oc: list val) : Zlength oc = 256 -> Zlength acc < 256 ->
  field_compatible (tarray tuchar 256) [] pw ->
  data_at shw (tarray tuchar 256) (zbytes acc ++ sublist (Zlength acc) 256 oc) pw |--
  data_at shw (tarray tuchar (Zlength acc)) (zbytes acc) pw *
  data_at shw tuchar (Znth (Zlength acc) oc) (offset_val (Zlength acc) pw) *
  data_at shw (tarray tuchar (256 - (Zlength acc + 1))) (sublist (Zlength acc + 1) 256 oc)
    (offset_val (Zlength acc + 1) pw).
Proof.
  intros Ho Ha Hfc. pose proof (Zlength_nonneg acc).
  rewrite (out3 shw pw _ (Zlength acc)) by (auto; list_solve).
  replace (sublist 0 (Zlength acc) (zbytes acc ++ sublist (Zlength acc) 256 oc)) with (zbytes acc) by list_solve.
  replace (Znth (Zlength acc) (zbytes acc ++ sublist (Zlength acc) 256 oc)) with (Znth (Zlength acc) oc) by list_solve.
  replace (sublist (Zlength acc + 1) 256 (zbytes acc ++ sublist (Zlength acc) 256 oc))
    with (sublist (Zlength acc + 1) 256 oc) by list_solve.
  apply derives_refl.
Qed.

Lemma out_merge1 shw pw (acc: list Z) (oc: list val) y : Zlength oc = 256 -> Zlength acc < 256 ->
  field_compatible (tarray tuchar 256) [] pw ->
  data_at shw (tarray tuchar (Zlength acc)) (zbytes acc) pw *
  data_at shw tuchar (Vint (Int.repr y)) (offset_val (Zlength acc) pw) *
  data_at shw (tarray tuchar (256 - (Zlength acc + 1))) (sublist (Zlength acc + 1) 256 oc)
    (offset_val (Zlength acc + 1) pw) |--
  data_at shw (tarray tuchar 256) (zbytes (acc ++ [y]) ++ sublist (Zlength (acc ++ [y])) 256 oc) pw.
Proof.
  intros Ho Ha Hfc. pose proof (Zlength_nonneg acc).
  rewrite (out3 shw pw _ (Zlength acc)) by (auto; list_solve).
  replace (sublist 0 (Zlength acc) (zbytes (acc ++ [y]) ++ sublist (Zlength (acc ++ [y])) 256 oc))
    with (zbytes acc) by list_solve.
  replace (Znth (Zlength acc) (zbytes (acc ++ [y]) ++ sublist (Zlength (acc ++ [y])) 256 oc))
    with (Vint (Int.repr y)) by list_solve.
  replace (sublist (Zlength acc + 1) 256 (zbytes (acc ++ [y]) ++ sublist (Zlength (acc ++ [y])) 256 oc))
    with (sublist (Zlength acc + 1) 256 oc) by list_solve.
  apply derives_refl.
Qed.

Ltac static_if := repeat apply -> seq_assoc;
  match goal with |- semax _ ?Pre (Ssequence (Sifthenelse _ _ _) _) _ =>
    forward_if Pre; [discriminate | forward; entailer! | ] end.

Ltac out_tc shw pw := match goal with |- _ |-- denote_tc_test_order (offset_val ?k _) (offset_val ?j _) =>
  match goal with |- context [data_at shw (tarray tuchar 256) ?l pw] =>
    apply derives_trans with (data_at shw (tarray tuchar 256) l pw * TT); [cancel | apply out_test_order; auto; lia]
  end end.

Definition fast_cond_val (st k: Z) (pw: val) : val :=
  match sem_and tint tint (bool2val (Int.eq (Int.repr st) (Int.repr 0)))
          (force_val (sem_cmp_pp Clt (offset_val k pw) (offset_val 252 pw))) with
  | Some v' => v' | None => Vundef end.

Lemma fast_cond st k pw : field_compatible (Tarray tuchar 256 noattr) [] pw -> 0 <= st <= 3 -> 0 <= k <= 252 ->
  (typed_true tint (fast_cond_val st k pw) -> st = 0 /\ k < 252) /\
  (typed_false tint (fast_cond_val st k pw) -> st <> 0 \/ 252 <= k).
Proof.
  intros Hfc Hst Hk. unfold fast_cond_val. rewrite ent_cmp_lt by (auto; lia). simpl force_val.
  assert (st = 0 \/ st = 1 \/ st = 2 \/ st = 3) as Hc by lia.
  destruct (k <? 252)%Z eqn:E; destruct Hc as [ -> | [ -> | [ -> | -> ]]];
    unfold typed_true, typed_false; simpl; split; intros Ht; try discriminate; lia.
Qed.

Ltac dw0 := repeat apply -> seq_assoc; match goal with
  | |- semax _ ?Pre (Ssequence (Sloop _ Sbreak) _) _ => forward_loop Pre break: Pre; [entailer! | .. ]
  | |- semax _ ?Pre (Sloop _ Sbreak) _ => forward_loop Pre break: Pre; [entailer! | .. ]
  end.

(* The loop bodies below accumulate many arithmetic hypotheses (disjunctions, Z.max, div and mod) on which lia,
   list_solve and entailer! case-split; once a step no longer needs them, they are cleared to keep every sentence
   fast. This one drops the readings of the bit container (r = bs_peek ...) once restated as bs_peek_s. *)
Ltac ent_clear_peeks := repeat match goal with Hx: _ -> _ = bs_peek _ _ _ |- _ => clear Hx end.

Lemma body_ent_generic :
  semax_body Vprog (G_B0 ++ [FSE_initDState_spec; FSE_decodeSymbol_spec; FSE_decodeSymbolFast_spec])
    f_FSE_decompress_usingDTable_generic FSE_decompress_usingDTable_generic_spec.
Proof.
  start_function.
  assert_PROP (isptr pw /\ field_compatible (tarray tuchar N) [] base) as Hpf by entailer!.
  destruct Hpf as [Hpw Hfc].
  assert_PROP (fse_dt_ok t /\ (fm = 0 \/ fm = 1)) as Hdf by (unfold fsedt_at; entailer!).
  destruct Hdf as [Hdt Hfm].
  rewrite (win_split sh N c off s base) by auto.
  pose proof H0 as Hw. destruct Hw as (Hsh & Hoff & Hn & HN & Hc & _ & Hbytes & Hwin).
  pose proof (Zlength_nonneg s) as Hsn.
  Intros.
  forward. forward. forward. forward.
  assert (Eom: force_val (sem_binary_operation' Osub (tptr tuchar) tint (force_val (sem_binary_operation' Oadd (tptr tuchar) tulong pw (Vlong (Int64.repr 255)))) (Vint (Int.repr 3))) = offset_val 252 pw /\ force_val (sem_binary_operation' Oadd (tptr tuchar) tulong pw (Vlong (Int64.repr 255))) = offset_val 255 pw).
  { destruct pw; try contradiction. simpl. split; f_equal; try (rewrite Ptrofs.sub_add_opp, Ptrofs.add_assoc; f_equal);
      try (apply Ptrofs.same_if_eq; vm_compute; reflexivity). }
  destruct Eom as [Eol Eom]. rewrite Eol, Eom. clear Eol Eom.
  assert (Hsub: sublist 0 (0 + Zlength s) s = s) by (rewrite Z.add_0_l; apply sublist_same; lia).
  assert (Hob: isptr (offset_val off base)) by (destruct Hfc as [Hb _]; destruct base; try contradiction; exact I).
  destruct (bs_wf s) eqn:Hwf.
  2: { match goal with |- semax _ ?Pre _ _ => forward_loop Pre break: (@FF (environ -> mpred) _) end.
       { entailer!. }
       { forward_call (Tsh, v_bitD, sh, offset_val off base, s, 0, Zlength s, gv).
         Intros r. rewrite Hsub, Hwf in *.
         unfold POSTCONDITION, abbreviate.
         match goal with |- semax _ ?Pre _ (loop_nocontinue_ret_assert _ (overridePost ?Q _)) =>
           forward_loop Pre break: Q end.
         { entailer!. }
         assert (Hr: 0 <= r <= Int64.max_unsigned) by assumption.
         forward_call r.
         match goal with Hx: is_error_code r = true |- _ => rewrite Hx end.
         forward_if.
         { forward. Exists r oc.
           rewrite (win_split sh (Zlength c) c off s base) by auto.
           rewrite (wdec_nowf t s Hwf Hbytes).
           entailer!. }
         { match goal with Hx: Int.repr 1 = Int.zero |- _ => discriminate Hx end. } } }
  forward_loop (PROP () LOCAL (temp _olimit (offset_val 252 pw); temp _omax (offset_val 255 pw);
   temp _op pw; temp _ostart pw;
   lvar _state2 (Tstruct ___gp_FSE_DState_t noattr) v_state2;
   lvar _state1 (Tstruct ___gp_FSE_DState_t noattr) v_state1;
   lvar _bitD (Tstruct ___gp_BIT_DStream_t noattr) v_bitD;
   gvars gv; temp _dst pw; temp _maxDstSize (Vlong (Int64.repr 255));
   temp _cSrc (offset_val off base);
   temp _cSrcSize (Vlong (Int64.repr (Zlength s)));
   temp _dt dt; temp _fast (Vint (Int.repr fm)))
   SEP (data_at_ Tsh (Tstruct ___gp_FSE_DState_t noattr) v_state2;
   data_at_ Tsh (Tstruct ___gp_FSE_DState_t noattr) v_state1;
   data_at_ Tsh (Tstruct ___gp_BIT_DStream_t noattr) v_bitD;
   zstd_globals gv; data_at shw (tarray tuchar 256) oc pw;
   data_at sh (tarray tuchar off) (sublist 0 off c) base;
   bit_src sh (offset_val off base) s;
   data_at sh (tarray tuchar (N - (off + Zlength s)))
     (sublist (off + Zlength s) N c) (offset_val (off + Zlength s) base);
   fsedt_at sht t fm dt))
  break: (PROP () LOCAL (temp _olimit (offset_val 252 pw); temp _omax (offset_val 255 pw);
   temp _op pw; temp _ostart pw;
   lvar _state2 (Tstruct ___gp_FSE_DState_t noattr) v_state2;
   lvar _state1 (Tstruct ___gp_FSE_DState_t noattr) v_state1;
   lvar _bitD (Tstruct ___gp_BIT_DStream_t noattr) v_bitD;
   gvars gv; temp _dst pw; temp _maxDstSize (Vlong (Int64.repr 255));
   temp _cSrc (offset_val off base);
   temp _cSrcSize (Vlong (Int64.repr (Zlength s)));
   temp _dt dt; temp _fast (Vint (Int.repr fm)))
   SEP (data_at_ Tsh (Tstruct ___gp_FSE_DState_t noattr) v_state2;
   data_at_ Tsh (Tstruct ___gp_FSE_DState_t noattr) v_state1;
   BIT_DStream_rep Tsh gv s (offset_val off base) (bs_total s) (8 * Z.max 0 (Zlength s - 8)) v_bitD;
   zstd_globals gv; data_at shw (tarray tuchar 256) oc pw;
   data_at sh (tarray tuchar off) (sublist 0 off c) base;
   bit_src sh (offset_val off base) s;
   data_at sh (tarray tuchar (N - (off + Zlength s)))
     (sublist (off + Zlength s) N c) (offset_val (off + Zlength s) base);
   fsedt_at sht t fm dt)).
  { entailer!. }
  forward_call (Tsh, v_bitD, sh, offset_val off base, s, 0, Zlength s, gv).
  { Intros r. rewrite Hsub, Hwf in *. rewrite isptr_offset_val_zero by auto. subst r.
    unfold POSTCONDITION, abbreviate.
    match goal with |- semax _ ?Pre _ (loop_nocontinue_ret_assert _ (overridePost ?Q _)) => forward_loop Pre break: Q end.
    { entailer!. }
    forward_call (Zlength s).
    rewrite is_error_small by lia.
    forward_if.
    { contradiction. }
    forward. entailer!.
    forward. entailer!. }
  pose proof (bs_total_lo s Hwf Hbytes) as HT.
  set (T := bs_total s) in *. set (lo0 := (8 * Z.max 0 (Zlength s - 8))%Z) in *.
  destruct Hdt as (Hlog & Hcells & Hcf).
  assert_PROP (bit_inv s T lo0) as Hinv0 by (sep_apply rep_bit_inv; entailer!).
  forward_call (Tsh, v_state1, Tsh, v_bitD, gv, s, offset_val off base, T, lo0, sht, dt, t, fm,
                sh, offset_val off base, s, 0).
  { clear - Hob Hsub Hsn Hinv0 HT Hlog. unfold bit_src_ok, bit_inv in *.
    rewrite isptr_offset_val_zero by auto. try rewrite Hsub. repeat split; auto; rep_lia. }
  Intros st1.
  set (lo1 := snd (bs_reload (T - ft_log t) lo0)) in *.
  assert_PROP (bit_inv s (T - ft_log t) lo1) as Hinv1 by (sep_apply rep_bit_inv; entailer!).
  assert (Hlo1: lo1 <= Z.max 0 (T - ft_log t)).
  { destruct (Z_lt_le_dec (T - ft_log t) lo0).
    - destruct (reload_overflow (T - ft_log t) lo0) as [_ E]; [lia|]. unfold lo1; rewrite E. lia.
    - unfold bit_inv in Hinv0.
      pose proof (reload_ok (T - ft_log t) lo0 ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & Hb & _). unfold lo1. lia. }
  forward_call (Tsh, v_state2, Tsh, v_bitD, gv, s, offset_val off base, T - ft_log t, lo1, sht, dt, t, fm,
                sh, offset_val off base, s, 0).
  { clear - Hob Hsub Hsn Hinv1 HT Hlog Hlo1. unfold bit_src_ok, bit_inv in *.
    rewrite isptr_offset_val_zero by auto. try rewrite Hsub. repeat split; auto; rep_lia. }
  Intros st2.
  set (pos2 := T - ft_log t - ft_log t) in *.
  set (lo2 := snd (bs_reload pos2 lo1)) in *.
  assert_PROP (bit_inv s pos2 lo2) as Hinv2 by (sep_apply rep_bit_inv; entailer!).
  assert (Hgood: 0 <= pos2 ->
     st1 = bs_peek_s s T (ft_log t) /\ st2 = bs_peek_s s (T - ft_log t) (ft_log t) /\ lo2 <= pos2).
  { intros Hp. unfold bit_inv in Hinv0, Hinv1.
    pose proof (reload_ok (T - ft_log t) lo0 ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & _ & _ & _ & R1).
    fold lo1 in R1.
    pose proof (reload_ok pos2 lo1 ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & R2 & _).
    split; [|split; [|unfold lo2; lia]].
    - rewrite H3 by lia. symmetry. apply bs_peek_s_eq; auto; lia.
    - rewrite H5 by lia. symmetry. apply bs_peek_s_eq; auto; lia. }
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx (?A :: _ :: ?R)))) _ _ =>
    forward_loop (PROPx P (LOCALx Q (SEPx (A :: BIT_DStream_rep Tsh gv s (offset_val off base) pos2 lo2 v_bitD :: R))))
    break: (PROPx ((0 <= pos2) :: P) (LOCALx Q (SEPx (A ::
               BIT_DStream_rep Tsh gv s (offset_val off base) pos2 (snd (bs_reload pos2 lo2)) v_bitD :: R))))
  end.
  { entailer!. }
  { forward_call (Tsh, v_bitD, gv, s, offset_val off base, pos2, lo2, sh, offset_val off base, s, 0).
    { clear - Hob Hsub Hsn. unfold bit_src_ok.
      rewrite isptr_offset_val_zero by auto. try rewrite Hsub. repeat split; auto; rep_lia. }
    pose proof (reload_range pos2 lo2) as Hrr.
    forward_if.
    { match goal with H: fst (bs_reload pos2 lo2) = _ |- _ => rename H into E3 end.
      assert (Hp: pos2 < 0).
      { destruct (Z_lt_le_dec pos2 0); auto. destruct (Hgood l) as (_ & _ & Hl2). unfold bit_inv in Hinv2.
        pose proof (reload_ok pos2 lo2 ltac:(lia) ltac:(lia) Hl2) as (R & _). contradiction. }
      dw0. { forward. entailer!. }
      dw0. { match goal with |- semax _ ?Pre _ _ => forward_if Pre end. { contradiction. } { forward. entailer!. }
             forward. entailer!. }
      dw0. { forward. entailer!. }
      dw0. { forward. entailer!. }
      forward.
      Exists (2 ^ 64 - 20) oc.
      rewrite (win_split sh (Zlength c) c off s base) by auto.
      sep_apply rep_data_at_. unfold t_bitd.
      rewrite (wdec_short t s Hwf Hbytes) by (unfold pos2, T in Hp; lia).
      rewrite neg_code_repr by lia.
      entailer!. }
    forward. entailer!.
    destruct (Z_lt_le_dec pos2 0); auto.
    destruct (reload_overflow pos2 lo2) as [E _]; [unfold bit_inv in Hinv2; lia|]. contradiction. }
  Intros.
  destruct (Hgood H6) as (Est1 & Est2 & Hl2).
  pose proof (wdec_start t s Hwf Hbytes) as Hstart. fold T in Hstart.
  rewrite <- Est1, <- Est2 in Hstart. replace (T - 2 * ft_log t) with pos2 in Hstart by (unfold pos2; lia).
  specialize (Hstart H6).
  pose (LOCS := fun k : Z =>
   [temp _olimit (offset_val 252 pw); temp _omax (offset_val 255 pw);
   temp _op (offset_val k pw); temp _ostart pw;
   lvar _state2 (Tstruct ___gp_FSE_DState_t noattr) v_state2;
   lvar _state1 (Tstruct ___gp_FSE_DState_t noattr) v_state1;
   lvar _bitD (Tstruct ___gp_BIT_DStream_t noattr) v_bitD;
   gvars gv; temp _dst pw; temp _maxDstSize (Vlong (Int64.repr 255));
   temp _cSrc (offset_val off base);
   temp _cSrcSize (Vlong (Int64.repr (Zlength s)));
   temp _dt dt; temp _fast (Vint (Int.repr fm))]).
  pose (SEPS := fun (st1 st2 pos lo: Z) (acc: list Z) =>
   [data_at Tsh t_dstate (Vlong (Int64.repr st1), offset_val 4 dt) v_state1;
    data_at Tsh t_dstate (Vlong (Int64.repr st2), offset_val 4 dt) v_state2;
    BIT_DStream_rep Tsh gv s (offset_val off base) pos lo v_bitD;
    fsedt_at sht t fm dt; bit_src sh (offset_val off base) s; zstd_globals gv;
    data_at shw (tarray tuchar 256) (zbytes acc ++ sublist (Zlength acc) 256 oc) pw;
    data_at sh (tarray tuchar off) (sublist 0 off c) base;
    data_at sh (tarray tuchar (N - (off + Zlength s))) (sublist (off + Zlength s) N c)
      (offset_val (off + Zlength s) base)]).
  clear Hgood H3 H5 Est1 Est2.
  forward_loop (EX f: nat, EX pos: Z, EX lo: Z, EX st1: Z, EX st2: Z, EX acc: list Z,
     PROPx [0 <= lo <= pos; Zlength acc = 512 - 2 * Z.of_nat f; Zlength acc mod 4 = 0; Zlength acc <= 252;
            fse_weights_dec t s = ent_fin (fse2_loop f t s pos st1 st2 acc);
            0 <= st1 < 2 ^ ft_log t; 0 <= st2 < 2 ^ ft_log t]
     (LOCALx (LOCS (Zlength acc)) (SEPx (SEPS st1 st2 pos lo acc))))
   continue: (EX f: nat, EX pos: Z, EX lo: Z, EX st1: Z, EX st2: Z, EX acc: list Z,
     PROPx [0 <= lo <= pos; Zlength acc = 512 - 2 * Z.of_nat f; Zlength acc mod 4 = 0; 4 <= Zlength acc <= 252;
            fse_weights_dec t s = ent_fin (fse2_loop f t s pos st1 st2 acc);
            0 <= st1 < 2 ^ ft_log t; 0 <= st2 < 2 ^ ft_log t]
     (LOCALx (LOCS (Zlength acc - 4)) (SEPx (SEPS st1 st2 pos lo acc))))
   break: (EX f: nat, EX pos: Z, EX lo: Z, EX st1: Z, EX st2: Z, EX acc: list Z,
     PROPx [0 <= lo <= pos; lo = 0 \/ 57 <= pos - lo; Zlength acc = 512 - 2 * Z.of_nat f; Zlength acc <= 254;
            fse_weights_dec t s = ent_fin (fse2_loop f t s pos st1 st2 acc);
            0 <= st1 < 2 ^ ft_log t; 0 <= st2 < 2 ^ ft_log t]
     (LOCALx (LOCS (Zlength acc)) (SEPx (SEPS st1 st2 pos lo acc)))).
  { Exists 256%nat pos2 (snd (bs_reload pos2 lo2)) st1 st2 (@nil Z).
    unfold LOCS, SEPS. rewrite Zlength_nil, (sublist_same 0 256 oc) by lia. simpl app.
    unfold bit_inv in Hinv2.
    pose proof (reload_ok pos2 lo2 ltac:(lia) ltac:(lia) Hl2) as (_ & Hb & _).
    rewrite isptr_offset_val_zero by auto.
    entailer!. }
  { Intros f pos lo st1' st2' acc. unfold LOCS, SEPS.
    clear HT Hinv0 Hinv1 Hlo1 Hinv2 Hl2 Hstart.
    assert_PROP (bit_inv s pos lo) as Hinv by (sep_apply rep_bit_inv; entailer!).
    forward_call (Tsh, v_bitD, gv, s, offset_val off base, pos, lo, sh, offset_val off base, s, 0).
    { clear - Hob Hsub Hsn. unfold bit_src_ok. rewrite isptr_offset_val_zero by auto. try rewrite Hsub. repeat split; auto; rep_lia. }
    pose proof (reload_range pos lo) as Hrr.
    unfold bit_inv in Hinv.
    pose proof (reload_ok pos lo ltac:(lia) ltac:(lia) ltac:(lia)) as (Rno & Rb & Run & Rnu & Ror).
    assert_PROP (field_compatible (Tarray tuchar 256 noattr) [] pw) as Hfpw by entailer!.
    pose proof (Zlength_nonneg acc) as Hacc0.
    pose proof (fast_cond (fst (bs_reload pos lo)) (Zlength acc) pw Hfpw Hrr ltac:(lia)) as [Ctrue Cfalse].
    clear Hinv.
    forward_if.
    { entailer!. out_tc shw pw. }
    { apply Ctrue in H12. destruct H12 as [Hst Hk].
      specialize (Run Hst). clear Ctrue Cfalse Rnu Ror.
      destruct Hfm as [Efm|Efm].
      {
      set (lo' := snd (bs_reload pos lo)) in *.
      assert_PROP (bit_inv s pos lo') as Hinv' by (sep_apply rep_bit_inv; entailer!).
      assert_PROP (field_compatible (tarray tuchar 256) [] pw) as Hfpw' by entailer!.
      rewrite (out_split shw pw _ (Zlength acc)) by (auto; try list_solve).
      replace (sublist 0 (Zlength acc) (zbytes acc ++ sublist (Zlength acc) 256 oc)) with (zbytes acc) by list_solve.
      replace (sublist (Zlength acc) 256 (zbytes acc ++ sublist (Zlength acc) 256 oc))
        with (sublist (Zlength acc) 256 oc) by list_solve.
      Intros.
      pose proof (cell_P _ t st1' Hcells Hcf H10) as (Cs1 & Cn1 & Cb1 & Cbb1).
      repeat apply -> seq_assoc. apply semax_if_seq. forward_if.
      1: { rewrite Efm in *; exfalso; match goal with Hx: ?a <> ?a |- _ => apply Hx; reflexivity end. }
      forward_call (Tsh, v_state1, st1', sht, dt, t, fm, Tsh, v_bitD, gv, s, offset_val off base, pos, lo').
      Intros r1.
      forward.
      assert (E1: r1 = bs_peek_s s pos (fe_nb (fse_cell t st1'))).
      { match goal with Hx: _ -> r1 = _ |- _ => rewrite Hx by lia end. symmetry; apply bs_peek_s_eq; auto; lia. }
      ent_clear_peeks.
      static_if.
      pose proof (cell_P _ t st2' Hcells Hcf H11) as (Cs2 & Cn2 & Cb2 & Cbb2).
      repeat apply -> seq_assoc. apply semax_if_seq. forward_if.
      1: { rewrite Efm in *; exfalso; match goal with Hx: ?a <> ?a |- _ => apply Hx; reflexivity end. }
      forward_call (Tsh, v_state2, st2', sht, dt, t, fm, Tsh, v_bitD, gv, s, offset_val off base,
                    pos - fe_nb (fse_cell t st1'), lo').
      Intros r2.
      forward.
      assert (E2: r2 = bs_peek_s s (pos - fe_nb (fse_cell t st1')) (fe_nb (fse_cell t st2'))).
      { match goal with Hx: _ -> r2 = _ |- _ => rewrite Hx by lia end. symmetry; apply bs_peek_s_eq; auto; lia. }
      ent_clear_peeks.
      static_if.
      assert (H10': 0 <= fe_base (fse_cell t st1') + r1 < 2 ^ ft_log t).
      { match goal with Hx: 0 <= r1 < _ |- _ => idtac end. lia. }
      pose proof (cell_P _ t _ Hcells Hcf H10') as (Cs3 & Cn3 & Cb3 & Cbb3).
      repeat apply -> seq_assoc. apply semax_if_seq. forward_if.
      1: { rewrite Efm in *; exfalso; match goal with Hx: ?a <> ?a |- _ => apply Hx; reflexivity end. }
      forward_call (Tsh, v_state1, fe_base (fse_cell t st1') + r1, sht, dt, t, fm, Tsh, v_bitD, gv, s, offset_val off base,
                    pos - fe_nb (fse_cell t st1') - fe_nb (fse_cell t st2'), lo').
      Intros r3.
      forward.
      assert (E3: r3 = bs_peek_s s (pos - fe_nb (fse_cell t st1') - fe_nb (fse_cell t st2'))
                         (fe_nb (fse_cell t (fe_base (fse_cell t st1') + r1)))).
      { match goal with Hx: _ -> r3 = _ |- _ => rewrite Hx by lia end. symmetry; apply bs_peek_s_eq; auto; lia. }
      ent_clear_peeks.
      static_if.
      assert (H11': 0 <= fe_base (fse_cell t st2') + r2 < 2 ^ ft_log t) by lia.
      pose proof (cell_P _ t _ Hcells Hcf H11') as (Cs4 & Cn4 & Cb4 & Cbb4).
      apply semax_if_seq. forward_if.
      1: { rewrite Efm in *; exfalso; match goal with Hx: ?a <> ?a |- _ => apply Hx; reflexivity end. }
      forward_call (Tsh, v_state2, fe_base (fse_cell t st2') + r2, sht, dt, t, fm, Tsh, v_bitD, gv, s, offset_val off base,
                    pos - fe_nb (fse_cell t st1') - fe_nb (fse_cell t st2')
                        - fe_nb (fse_cell t (fe_base (fse_cell t st1') + r1)), lo').
      Intros r4.
      forward.
      assert (E4: r4 = bs_peek_s s (pos - fe_nb (fse_cell t st1') - fe_nb (fse_cell t st2')
                                       - fe_nb (fse_cell t (fe_base (fse_cell t st1') + r1)))
                         (fe_nb (fse_cell t (fe_base (fse_cell t st2') + r2)))).
      { match goal with Hx: _ -> r4 = _ |- _ => rewrite Hx by lia end. symmetry; apply bs_peek_s_eq; auto; lia. }
      ent_clear_peeks.
      destruct f as [|[|f'']]; [lia|lia|].
      rewrite fse2_step in H9 by lia. rewrite <- E1, <- E2 in H9.
      rewrite fse2_step in H9 by lia. rewrite <- E3, <- E4 in H9.
      rewrite !ze8 by auto.
      Exists f'' (pos - fe_nb (fse_cell t st1') - fe_nb (fse_cell t st2')
                        - fe_nb (fse_cell t (fe_base (fse_cell t st1') + r1))
                        - fe_nb (fse_cell t (fe_base (fse_cell t st2') + r2))) lo'
        (fe_base (fse_cell t (fe_base (fse_cell t st1') + r1)) + r3)
        (fe_base (fse_cell t (fe_base (fse_cell t st2') + r2)) + r4)
        ((((acc ++ [fe_sym (fse_cell t st1')]) ++ [fe_sym (fse_cell t st2')]) ++
           [fe_sym (fse_cell t (fe_base (fse_cell t st1') + r1))]) ++
           [fe_sym (fse_cell t (fe_base (fse_cell t st2') + r2))]).
      unfold LOCS, SEPS.
      rewrite (out_split shw pw _ (Zlength acc)) by (auto; list_solve).
      match goal with |- context [sublist 0 (Zlength acc) ?L] =>
        replace (sublist 0 (Zlength acc) L) with (zbytes acc) by list_solve end.
      rewrite <- upd4_eq by list_solve.
      entailer!.
      rewrite !Zlength_app, !Zlength_cons, !Zlength_nil.
      destruct (len4 (Zlength acc) H7 Hk Hacc0) as [L1 L2].
      split; [lia|]. split; [exact L1|]. split; [exact L2|]. f_equal. lia.  }
      {
      set (lo' := snd (bs_reload pos lo)) in *.
      assert_PROP (bit_inv s pos lo') as Hinv' by (sep_apply rep_bit_inv; entailer!).
      assert_PROP (field_compatible (tarray tuchar 256) [] pw) as Hfpw' by entailer!.
      rewrite (out_split shw pw _ (Zlength acc)) by (auto; try list_solve).
      replace (sublist 0 (Zlength acc) (zbytes acc ++ sublist (Zlength acc) 256 oc)) with (zbytes acc) by list_solve.
      replace (sublist (Zlength acc) 256 (zbytes acc ++ sublist (Zlength acc) 256 oc))
        with (sublist (Zlength acc) 256 oc) by list_solve.
      Intros.
      pose proof (cell_P _ t st1' Hcells Hcf H10) as (Cs1 & Cn1 & Cb1 & Cbb1).
      pose proof (cell_P _ t st1' Hcells (H1 Efm) H10) as Cf1. simpl in Cf1.
      repeat apply -> seq_assoc. apply semax_if_seq. forward_if.
      2: { rewrite Efm in *; discriminate. }
      forward_call (Tsh, v_state1, st1', sht, dt, t, fm, Tsh, v_bitD, gv, s, offset_val off base, pos, lo').
      Intros r1.
      forward.
      assert (E1: r1 = bs_peek_s s pos (fe_nb (fse_cell t st1'))).
      { match goal with Hx: _ -> r1 = _ |- _ => rewrite Hx by lia end. symmetry; apply bs_peek_s_eq; auto; lia. }
      ent_clear_peeks.
      static_if.
      pose proof (cell_P _ t st2' Hcells Hcf H11) as (Cs2 & Cn2 & Cb2 & Cbb2).
      pose proof (cell_P _ t st2' Hcells (H1 Efm) H11) as Cf2. simpl in Cf2.
      repeat apply -> seq_assoc. apply semax_if_seq. forward_if.
      2: { rewrite Efm in *; discriminate. }
      forward_call (Tsh, v_state2, st2', sht, dt, t, fm, Tsh, v_bitD, gv, s, offset_val off base,
                    pos - fe_nb (fse_cell t st1'), lo').
      Intros r2.
      forward.
      assert (E2: r2 = bs_peek_s s (pos - fe_nb (fse_cell t st1')) (fe_nb (fse_cell t st2'))).
      { match goal with Hx: _ -> r2 = _ |- _ => rewrite Hx by lia end. symmetry; apply bs_peek_s_eq; auto; lia. }
      ent_clear_peeks.
      static_if.
      assert (H10': 0 <= fe_base (fse_cell t st1') + r1 < 2 ^ ft_log t).
      { match goal with Hx: 0 <= r1 < _ |- _ => idtac end. lia. }
      pose proof (cell_P _ t _ Hcells Hcf H10') as (Cs3 & Cn3 & Cb3 & Cbb3).
      pose proof (cell_P _ t _ Hcells (H1 Efm) H10') as Cf3. simpl in Cf3.
      repeat apply -> seq_assoc. apply semax_if_seq. forward_if.
      2: { rewrite Efm in *; discriminate. }
      forward_call (Tsh, v_state1, fe_base (fse_cell t st1') + r1, sht, dt, t, fm, Tsh, v_bitD, gv, s, offset_val off base,
                    pos - fe_nb (fse_cell t st1') - fe_nb (fse_cell t st2'), lo').
      Intros r3.
      forward.
      assert (E3: r3 = bs_peek_s s (pos - fe_nb (fse_cell t st1') - fe_nb (fse_cell t st2'))
                         (fe_nb (fse_cell t (fe_base (fse_cell t st1') + r1)))).
      { match goal with Hx: _ -> r3 = _ |- _ => rewrite Hx by lia end. symmetry; apply bs_peek_s_eq; auto; lia. }
      ent_clear_peeks.
      static_if.
      assert (H11': 0 <= fe_base (fse_cell t st2') + r2 < 2 ^ ft_log t) by lia.
      pose proof (cell_P _ t _ Hcells Hcf H11') as (Cs4 & Cn4 & Cb4 & Cbb4).
      pose proof (cell_P _ t _ Hcells (H1 Efm) H11') as Cf4. simpl in Cf4.
      apply semax_if_seq. forward_if.
      2: { rewrite Efm in *; discriminate. }
      forward_call (Tsh, v_state2, fe_base (fse_cell t st2') + r2, sht, dt, t, fm, Tsh, v_bitD, gv, s, offset_val off base,
                    pos - fe_nb (fse_cell t st1') - fe_nb (fse_cell t st2')
                        - fe_nb (fse_cell t (fe_base (fse_cell t st1') + r1)), lo').
      Intros r4.
      forward.
      assert (E4: r4 = bs_peek_s s (pos - fe_nb (fse_cell t st1') - fe_nb (fse_cell t st2')
                                       - fe_nb (fse_cell t (fe_base (fse_cell t st1') + r1)))
                         (fe_nb (fse_cell t (fe_base (fse_cell t st2') + r2)))).
      { match goal with Hx: _ -> r4 = _ |- _ => rewrite Hx by lia end. symmetry; apply bs_peek_s_eq; auto; lia. }
      ent_clear_peeks.
      destruct f as [|[|f'']]; [lia|lia|].
      rewrite fse2_step in H9 by lia. rewrite <- E1, <- E2 in H9.
      rewrite fse2_step in H9 by lia. rewrite <- E3, <- E4 in H9.
      rewrite !ze8 by auto.
      Exists f'' (pos - fe_nb (fse_cell t st1') - fe_nb (fse_cell t st2')
                        - fe_nb (fse_cell t (fe_base (fse_cell t st1') + r1))
                        - fe_nb (fse_cell t (fe_base (fse_cell t st2') + r2))) lo'
        (fe_base (fse_cell t (fe_base (fse_cell t st1') + r1)) + r3)
        (fe_base (fse_cell t (fe_base (fse_cell t st2') + r2)) + r4)
        ((((acc ++ [fe_sym (fse_cell t st1')]) ++ [fe_sym (fse_cell t st2')]) ++
           [fe_sym (fse_cell t (fe_base (fse_cell t st1') + r1))]) ++
           [fe_sym (fse_cell t (fe_base (fse_cell t st2') + r2))]).
      unfold LOCS, SEPS.
      rewrite (out_split shw pw _ (Zlength acc)) by (auto; list_solve).
      match goal with |- context [sublist 0 (Zlength acc) ?L] =>
        replace (sublist 0 (Zlength acc) L) with (zbytes acc) by list_solve end.
      rewrite <- upd4_eq by list_solve.
      entailer!.
      rewrite !Zlength_app, !Zlength_cons, !Zlength_nil.
      destruct (len4 (Zlength acc) H7 Hk Hacc0) as [L1 L2].
      split; [lia|]. split; [exact L1|]. split; [exact L2|]. f_equal. lia.  } }
    { forward. Exists f pos (snd (bs_reload pos lo)) st1' st2' acc. unfold LOCS, SEPS. entailer!. } }
  { Intros f pos lo st1' st2' acc. unfold LOCS, SEPS. forward.
    Exists f pos lo st1' st2' acc. unfold LOCS, SEPS. entailer!. f_equal; lia. }
  forward_loop (EX f: nat, EX pos: Z, EX lo: Z, EX st1: Z, EX st2: Z, EX acc: list Z,
     PROPx [0 <= lo <= pos; lo = 0 \/ 57 <= pos - lo; Zlength acc = 512 - 2 * Z.of_nat f; Zlength acc <= 254;
            fse_weights_dec t s = ent_fin (fse2_loop f t s pos st1 st2 acc);
            0 <= st1 < 2 ^ ft_log t; 0 <= st2 < 2 ^ ft_log t]
     (LOCALx (LOCS (Zlength acc)) (SEPx (SEPS st1 st2 pos lo acc))))
   break: (EX ws: list Z, EX st1: Z, EX st2: Z, EX pos: Z, EX lo: Z,
     PROPx [fse_weights_dec t s = Some ws; Zlength ws <= 255]
     (LOCALx (LOCS (Zlength ws)) (SEPx (SEPS st1 st2 pos lo ws)))).
  { apply ENTAIL_refl. }
  { Intros f pos lo st1' st2' acc. unfold LOCS, SEPS.
    assert_PROP (bit_inv s pos lo) as Hinv by (sep_apply rep_bit_inv; entailer!). unfold bit_inv in Hinv.
    assert_PROP (field_compatible (tarray tuchar 256) [] pw) as Hfpw by entailer!.
    pose proof (Zlength_nonneg acc) as Hacc0.
    assert (Add1: forall k, force_val (sem_binary_operation' Oadd (tptr tuchar) tint (offset_val k pw) (Vint (Int.repr 1)))
                            = offset_val (k + 1) pw).
    { clear - Hpw. intros k. destruct pw; try contradiction. simpl. f_equal. rewrite Ptrofs.add_assoc. f_equal.
      replace (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_ints (Int.repr 1))) with (Ptrofs.repr 1)
        by (apply Ptrofs.same_if_eq; vm_compute; reflexivity).
      apply ptrofs_add_repr. }
    destruct Hfm as [Efm|Efm].
    {
    clear Hstart HT Hinv0 Hinv1 Hlo1 Hinv2 Hl2.
    match goal with Hx: 0 <= lo <= pos |- _ => rename Hx into Tlo end.
    match goal with Hx: lo = 0 \/ _ |- _ => rename Hx into Tlo2 end.
    match goal with Hx: Zlength acc = 512 - _ |- _ => rename Hx into Tf end.
    match goal with Hx: Zlength acc <= 254 |- _ => rename Hx into Tk end.
    match goal with Hx: fse_weights_dec t s = _ |- _ => rename Hx into Tm end.
    match goal with Hx: 0 <= st1' < _ |- _ => rename Hx into Ts1 end.
    match goal with Hx: 0 <= st2' < _ |- _ => rename Hx into Ts2 end.
    forward_if.
    { rewrite sub2 by auto. entailer!. out_tc shw pw. }
    { match goal with Hx: typed_true _ _ |- _ => rewrite sub2 in Hx by auto;
        apply (proj1 (gt_cond (Zlength acc) pw Hfpw ltac:(lia))) in Hx end.
      forward.
      assert (Hnone: fse_weights_dec t s = None) by (rewrite Tm; apply fin_none; lia).
      Exists (2 ^ 64 - 70) (zbytes acc ++ sublist (Zlength acc) 256 oc).
      first [rewrite (win_split sh (Zlength c) c off s base) by auto | rewrite (win_split sh N c off s base) by auto].
      sep_apply rep_data_at_. unfold t_bitd. rewrite Hnone. rewrite neg_code_repr by lia.
      entailer!. }
    match goal with Hx: typed_false _ _ |- _ => rewrite sub2 in Hx by auto;
      apply (proj2 (gt_cond (Zlength acc) pw Hfpw ltac:(lia))) in Hx end.
    assert (Tk2: Zlength acc <= 252) by lia.
    destruct f as [|f']; [lia|].
    sep_apply (out_split1 shw pw acc oc H ltac:(lia) Hfpw). Intros.
    forward. forward.
    pose proof (cell_P _ t st1' Hcells Hcf Ts1) as (Cs1 & Cn1 & Cb1 & Cbb1).
    repeat apply -> seq_assoc. apply semax_if_seq. forward_if.
    1: { rewrite Efm in *; exfalso; match goal with Hx: ?a <> ?a |- _ => apply Hx; reflexivity end. }
    forward_call (Tsh, v_state1, st1', sht, dt, t, fm, Tsh, v_bitD, gv, s, offset_val off base, pos, lo).
    Intros r1.
    forward.
    rewrite ze8 by auto.
    sep_apply (out_merge1 shw pw acc oc (fe_sym (fse_cell t st1')) H ltac:(lia) Hfpw).
    forward_call (Tsh, v_bitD, gv, s, offset_val off base, pos - fe_nb (fse_cell t st1'), lo, sh, offset_val off base, s, 0).
    { clear - Hob Hsub Hsn. unfold bit_src_ok. rewrite isptr_offset_val_zero by auto. try rewrite Hsub. repeat split; auto; rep_lia. }
    rewrite Add1. replace (Zlength acc + 1) with (Zlength (acc ++ [fe_sym (fse_cell t st1')])) by list_solve.
    set (p1 := pos - fe_nb (fse_cell t st1')) in *.
    pose proof (cell_P _ t st2' Hcells Hcf Ts2) as (Cs2 & Cn2 & Cb2 & Cbb2).
    destruct (Z_lt_le_dec p1 lo) as [Hov|Hnov].
    { (* reload overflow: state2's symbol, then stop *)
      destruct (reload_overflow p1 lo Hov) as [Ov1 Ov2].
      assert (Hlo0: lo = 0) by (destruct Tlo2; [auto | unfold p1 in Hov; lia]).
      clear Tlo2 Hinv.
      forward_if.
      2: { exfalso. match goal with Hx: Int.repr (fst (bs_reload _ _)) <> _ |- _ => apply Hx; rewrite Ov1; reflexivity end. }
      rewrite Ov2.
      sep_apply (out_split1 shw pw (acc ++ [fe_sym (fse_cell t st1')]) oc H ltac:(list_solve) Hfpw). Intros.
      forward. forward.
      repeat apply -> seq_assoc. apply semax_if_seq. forward_if.
      1: { rewrite Efm in *; exfalso; match goal with Hx: ?a <> ?a |- _ => apply Hx; reflexivity end. }
      forward_call (Tsh, v_state2, st2', sht, dt, t, fm, Tsh, v_bitD, gv, s, offset_val off base, p1, lo).
      Intros r2.
      forward.
      rewrite ze8 by auto.
      sep_apply (out_merge1 shw pw (acc ++ [fe_sym (fse_cell t st1')]) oc (fe_sym (fse_cell t st2')) H ltac:(list_solve) Hfpw).
      forward.
      rewrite fse2_stop1 in Tm by (unfold p1 in Hov; lia).
      rewrite fin_some in Tm by list_solve.
      Exists ((acc ++ [fe_sym (fse_cell t st1')]) ++ [fe_sym (fse_cell t st2')])
        (fe_base (fse_cell t st1') + r1) (fe_base (fse_cell t st2') + r2) (p1 - fe_nb (fse_cell t st2')) lo.
      unfold LOCS, SEPS. rewrite Add1.
      entailer!.
      split; [list_solve | f_equal; list_solve]. }
    { (* no overflow after state1's symbol *)
      assert (Hp1: 0 <= p1) by lia.
      unfold bit_inv in Hinv.
      pose proof (reload_ok p1 lo ltac:(lia) ltac:(lia) Hnov) as (Rno & Rb & Run & Rnu & Ror).
      pose proof (reload_range p1 lo) as Rrr.
      set (lo1' := snd (bs_reload p1 lo)) in *.
      assert (E1: r1 = bs_peek_s s pos (fe_nb (fse_cell t st1'))).
      { match goal with Hx: _ -> r1 = _ |- _ => rewrite Hx by lia end. symmetry; apply bs_peek_s_eq; auto; lia. }
      ent_clear_peeks.
      assert (Hl1: Zlength (acc ++ [fe_sym (fse_cell t st1')]) = Zlength acc + 1) by list_solve.
      forward_if.
      { exfalso. match goal with Hx: fst (bs_reload _ _) = _ |- _ => apply Rno; exact Hx end. }
      forward_if.
      { rewrite sub2 by auto. entailer!. out_tc shw pw. }
      { match goal with Hx: typed_true _ _ |- _ => rewrite sub2 in Hx by auto;
          apply (proj1 (gt_cond (Zlength (acc ++ [fe_sym (fse_cell t st1')])) pw Hfpw ltac:(lia))) in Hx end.
        lia. }
      sep_apply (out_split1 shw pw (acc ++ [fe_sym (fse_cell t st1')]) oc H ltac:(list_solve) Hfpw). Intros.
      forward. forward.
      repeat apply -> seq_assoc. apply semax_if_seq. forward_if.
      1: { rewrite Efm in *; exfalso; match goal with Hx: ?a <> ?a |- _ => apply Hx; reflexivity end. }
      forward_call (Tsh, v_state2, st2', sht, dt, t, fm, Tsh, v_bitD, gv, s, offset_val off base, p1, lo1').
      Intros r2.
      forward.
      rewrite ze8 by auto.
      sep_apply (out_merge1 shw pw (acc ++ [fe_sym (fse_cell t st1')]) oc (fe_sym (fse_cell t st2')) H ltac:(list_solve) Hfpw).
      rewrite Add1.
      replace (Zlength (acc ++ [fe_sym (fse_cell t st1')]) + 1)
        with (Zlength ((acc ++ [fe_sym (fse_cell t st1')]) ++ [fe_sym (fse_cell t st2')])) by list_solve.
      assert_PROP (bit_inv s (p1 - fe_nb (fse_cell t st2')) lo1') as Hinv1' by (sep_apply rep_bit_inv; entailer!).
      unfold bit_inv in Hinv1'.
      forward_call (Tsh, v_bitD, gv, s, offset_val off base, p1 - fe_nb (fse_cell t st2'), lo1', sh, offset_val off base, s, 0).
      { clear - Hob Hsub Hsn. unfold bit_src_ok. rewrite isptr_offset_val_zero by auto. try rewrite Hsub. repeat split; auto; rep_lia. }
      set (p2 := p1 - fe_nb (fse_cell t st2')) in *.
      assert (Tn1: 0 <= fe_base (fse_cell t st1') + r1 < 2 ^ ft_log t) by lia.
      pose proof (cell_P _ t _ Hcells Hcf Tn1) as (Cs3 & Cn3 & Cb3 & Cbb3).
      assert (Tn2: 0 <= fe_base (fse_cell t st2') + r2 < 2 ^ ft_log t) by lia.
      destruct (Z_lt_le_dec p2 lo1') as [Hov2|Hnov2].
      { (* overflow after state2's symbol: state1's symbol, then stop *)
        destruct (reload_overflow p2 lo1' Hov2) as [Ov1 Ov2].
        assert (Tlo1: lo1' = 0) by (destruct Ror; [auto | unfold p2 in Hov2; lia]).
        clear Hinv Hinv1' Ror Rnu Tlo2.
        forward_if.
        2: { exfalso. match goal with Hx: Int.repr (fst (bs_reload _ _)) <> _ |- _ => apply Hx; rewrite Ov1; reflexivity end. }
        rewrite Ov2.
        sep_apply (out_split1 shw pw ((acc ++ [fe_sym (fse_cell t st1')]) ++ [fe_sym (fse_cell t st2')]) oc H
                     ltac:(list_solve) Hfpw). Intros.
        forward. forward.
        repeat apply -> seq_assoc. apply semax_if_seq. forward_if.
        1: { rewrite Efm in *; exfalso; match goal with Hx: ?a <> ?a |- _ => apply Hx; reflexivity end. }
        forward_call (Tsh, v_state1, fe_base (fse_cell t st1') + r1, sht, dt, t, fm, Tsh, v_bitD, gv, s,
                      offset_val off base, p2, lo1').
        Intros r3.
        forward.
        rewrite ze8 by auto.
        sep_apply (out_merge1 shw pw ((acc ++ [fe_sym (fse_cell t st1')]) ++ [fe_sym (fse_cell t st2')]) oc
                     (fe_sym (fse_cell t (fe_base (fse_cell t st1') + r1))) H ltac:(list_solve) Hfpw).
        forward.
        rewrite fse2_stop2 in Tm by (unfold p2, p1 in *; lia).
        rewrite <- E1 in Tm.
        rewrite fin_some in Tm by list_solve.
        Exists (((acc ++ [fe_sym (fse_cell t st1')]) ++ [fe_sym (fse_cell t st2')]) ++
                  [fe_sym (fse_cell t (fe_base (fse_cell t st1') + r1))])
          (fe_base (fse_cell t (fe_base (fse_cell t st1') + r1)) + r3) (fe_base (fse_cell t st2') + r2)
          (p2 - fe_nb (fse_cell t (fe_base (fse_cell t st1') + r1))) lo1'.
        unfold LOCS, SEPS. rewrite Add1.
        entailer!.
        split; [list_solve | f_equal; list_solve]. }
      { (* no overflow: next iteration *)
        pose proof (reload_ok p2 lo1' ltac:(lia) ltac:(lia) Hnov2) as (Rno2 & Rb2 & Run2 & Rnu2 & Ror2).
        pose proof (reload_range p2 lo1') as Rrr2.
        clear Hinv Hinv1' Ror Rnu Rnu2 Tlo2.
        forward_if.
        { exfalso. match goal with Hx: fst (bs_reload _ _) = _ |- _ => apply Rno2; exact Hx end. }
        assert (E2: r2 = bs_peek_s s p1 (fe_nb (fse_cell t st2'))).
        { match goal with Hx: _ -> r2 = _ |- _ => rewrite Hx by lia end. symmetry; apply bs_peek_s_eq; auto; lia. }
        ent_clear_peeks.
        rewrite fse2_step in Tm by (unfold p1 in *; lia).
        change (pos - fe_nb (fse_cell t st1')) with p1 in Tm.
        change (p1 - fe_nb (fse_cell t st2')) with p2 in Tm.
        rewrite <- E1, <- E2 in Tm.
        forward.
        Exists f' p2 (snd (bs_reload p2 lo1')) (fe_base (fse_cell t st1') + r1) (fe_base (fse_cell t st2') + r2)
          ((acc ++ [fe_sym (fse_cell t st1')]) ++ [fe_sym (fse_cell t st2')]).
        unfold LOCS, SEPS.
        entailer!.
        rewrite !Zlength_app, !Zlength_cons, !Zlength_nil. split; lia. } } }
    {
    clear Hstart HT Hinv0 Hinv1 Hlo1 Hinv2 Hl2.
    match goal with Hx: 0 <= lo <= pos |- _ => rename Hx into Tlo end.
    match goal with Hx: lo = 0 \/ _ |- _ => rename Hx into Tlo2 end.
    match goal with Hx: Zlength acc = 512 - _ |- _ => rename Hx into Tf end.
    match goal with Hx: Zlength acc <= 254 |- _ => rename Hx into Tk end.
    match goal with Hx: fse_weights_dec t s = _ |- _ => rename Hx into Tm end.
    match goal with Hx: 0 <= st1' < _ |- _ => rename Hx into Ts1 end.
    match goal with Hx: 0 <= st2' < _ |- _ => rename Hx into Ts2 end.
    forward_if.
    { rewrite sub2 by auto. entailer!. out_tc shw pw. }
    { match goal with Hx: typed_true _ _ |- _ => rewrite sub2 in Hx by auto;
        apply (proj1 (gt_cond (Zlength acc) pw Hfpw ltac:(lia))) in Hx end.
      forward.
      assert (Hnone: fse_weights_dec t s = None) by (rewrite Tm; apply fin_none; lia).
      Exists (2 ^ 64 - 70) (zbytes acc ++ sublist (Zlength acc) 256 oc).
      first [rewrite (win_split sh (Zlength c) c off s base) by auto | rewrite (win_split sh N c off s base) by auto].
      sep_apply rep_data_at_. unfold t_bitd. rewrite Hnone. rewrite neg_code_repr by lia.
      entailer!. }
    match goal with Hx: typed_false _ _ |- _ => rewrite sub2 in Hx by auto;
      apply (proj2 (gt_cond (Zlength acc) pw Hfpw ltac:(lia))) in Hx end.
    assert (Tk2: Zlength acc <= 252) by lia.
    destruct f as [|f']; [lia|].
    sep_apply (out_split1 shw pw acc oc H ltac:(lia) Hfpw). Intros.
    forward. forward.
    pose proof (cell_P _ t st1' Hcells Hcf Ts1) as (Cs1 & Cn1 & Cb1 & Cbb1).
    pose proof (cell_P _ t st1' Hcells (H1 Efm) Ts1) as Cf1. simpl in Cf1.
    repeat apply -> seq_assoc. apply semax_if_seq. forward_if.
    2: { rewrite Efm in *; discriminate. }
    forward_call (Tsh, v_state1, st1', sht, dt, t, fm, Tsh, v_bitD, gv, s, offset_val off base, pos, lo).
    Intros r1.
    forward.
    rewrite ze8 by auto.
    sep_apply (out_merge1 shw pw acc oc (fe_sym (fse_cell t st1')) H ltac:(lia) Hfpw).
    forward_call (Tsh, v_bitD, gv, s, offset_val off base, pos - fe_nb (fse_cell t st1'), lo, sh, offset_val off base, s, 0).
    { clear - Hob Hsub Hsn. unfold bit_src_ok. rewrite isptr_offset_val_zero by auto. try rewrite Hsub. repeat split; auto; rep_lia. }
    rewrite Add1. replace (Zlength acc + 1) with (Zlength (acc ++ [fe_sym (fse_cell t st1')])) by list_solve.
    set (p1 := pos - fe_nb (fse_cell t st1')) in *.
    pose proof (cell_P _ t st2' Hcells Hcf Ts2) as (Cs2 & Cn2 & Cb2 & Cbb2).
    pose proof (cell_P _ t st2' Hcells (H1 Efm) Ts2) as Cf2. simpl in Cf2.
    destruct (Z_lt_le_dec p1 lo) as [Hov|Hnov].
    { (* reload overflow: state2's symbol, then stop *)
      destruct (reload_overflow p1 lo Hov) as [Ov1 Ov2].
      assert (Hlo0: lo = 0) by (destruct Tlo2; [auto | unfold p1 in Hov; lia]).
      clear Tlo2 Hinv.
      forward_if.
      2: { exfalso. match goal with Hx: Int.repr (fst (bs_reload _ _)) <> _ |- _ => apply Hx; rewrite Ov1; reflexivity end. }
      rewrite Ov2.
      sep_apply (out_split1 shw pw (acc ++ [fe_sym (fse_cell t st1')]) oc H ltac:(list_solve) Hfpw). Intros.
      forward. forward.
      repeat apply -> seq_assoc. apply semax_if_seq. forward_if.
      2: { rewrite Efm in *; discriminate. }
      forward_call (Tsh, v_state2, st2', sht, dt, t, fm, Tsh, v_bitD, gv, s, offset_val off base, p1, lo).
      Intros r2.
      forward.
      rewrite ze8 by auto.
      sep_apply (out_merge1 shw pw (acc ++ [fe_sym (fse_cell t st1')]) oc (fe_sym (fse_cell t st2')) H ltac:(list_solve) Hfpw).
      forward.
      rewrite fse2_stop1 in Tm by (unfold p1 in Hov; lia).
      rewrite fin_some in Tm by list_solve.
      Exists ((acc ++ [fe_sym (fse_cell t st1')]) ++ [fe_sym (fse_cell t st2')])
        (fe_base (fse_cell t st1') + r1) (fe_base (fse_cell t st2') + r2) (p1 - fe_nb (fse_cell t st2')) lo.
      unfold LOCS, SEPS. rewrite Add1.
      entailer!.
      split; [list_solve | f_equal; list_solve]. }
    { (* no overflow after state1's symbol *)
      assert (Hp1: 0 <= p1) by lia.
      unfold bit_inv in Hinv.
      pose proof (reload_ok p1 lo ltac:(lia) ltac:(lia) Hnov) as (Rno & Rb & Run & Rnu & Ror).
      pose proof (reload_range p1 lo) as Rrr.
      set (lo1' := snd (bs_reload p1 lo)) in *.
      assert (E1: r1 = bs_peek_s s pos (fe_nb (fse_cell t st1'))).
      { match goal with Hx: _ -> r1 = _ |- _ => rewrite Hx by lia end. symmetry; apply bs_peek_s_eq; auto; lia. }
      ent_clear_peeks.
      assert (Hl1: Zlength (acc ++ [fe_sym (fse_cell t st1')]) = Zlength acc + 1) by list_solve.
      forward_if.
      { exfalso. match goal with Hx: fst (bs_reload _ _) = _ |- _ => apply Rno; exact Hx end. }
      forward_if.
      { rewrite sub2 by auto. entailer!. out_tc shw pw. }
      { match goal with Hx: typed_true _ _ |- _ => rewrite sub2 in Hx by auto;
          apply (proj1 (gt_cond (Zlength (acc ++ [fe_sym (fse_cell t st1')])) pw Hfpw ltac:(lia))) in Hx end.
        lia. }
      sep_apply (out_split1 shw pw (acc ++ [fe_sym (fse_cell t st1')]) oc H ltac:(list_solve) Hfpw). Intros.
      forward. forward.
      repeat apply -> seq_assoc. apply semax_if_seq. forward_if.
      2: { rewrite Efm in *; discriminate. }
      forward_call (Tsh, v_state2, st2', sht, dt, t, fm, Tsh, v_bitD, gv, s, offset_val off base, p1, lo1').
      Intros r2.
      forward.
      rewrite ze8 by auto.
      sep_apply (out_merge1 shw pw (acc ++ [fe_sym (fse_cell t st1')]) oc (fe_sym (fse_cell t st2')) H ltac:(list_solve) Hfpw).
      rewrite Add1.
      replace (Zlength (acc ++ [fe_sym (fse_cell t st1')]) + 1)
        with (Zlength ((acc ++ [fe_sym (fse_cell t st1')]) ++ [fe_sym (fse_cell t st2')])) by list_solve.
      assert_PROP (bit_inv s (p1 - fe_nb (fse_cell t st2')) lo1') as Hinv1' by (sep_apply rep_bit_inv; entailer!).
      unfold bit_inv in Hinv1'.
      forward_call (Tsh, v_bitD, gv, s, offset_val off base, p1 - fe_nb (fse_cell t st2'), lo1', sh, offset_val off base, s, 0).
      { clear - Hob Hsub Hsn. unfold bit_src_ok. rewrite isptr_offset_val_zero by auto. try rewrite Hsub. repeat split; auto; rep_lia. }
      set (p2 := p1 - fe_nb (fse_cell t st2')) in *.
      assert (Tn1: 0 <= fe_base (fse_cell t st1') + r1 < 2 ^ ft_log t) by lia.
      pose proof (cell_P _ t _ Hcells Hcf Tn1) as (Cs3 & Cn3 & Cb3 & Cbb3).
      pose proof (cell_P _ t _ Hcells (H1 Efm) Tn1) as Cf3. simpl in Cf3.
      assert (Tn2: 0 <= fe_base (fse_cell t st2') + r2 < 2 ^ ft_log t) by lia.
      destruct (Z_lt_le_dec p2 lo1') as [Hov2|Hnov2].
      { (* overflow after state2's symbol: state1's symbol, then stop *)
        destruct (reload_overflow p2 lo1' Hov2) as [Ov1 Ov2].
        assert (Tlo1: lo1' = 0) by (destruct Ror; [auto | unfold p2 in Hov2; lia]).
        clear Hinv Hinv1' Ror Rnu Tlo2.
        forward_if.
        2: { exfalso. match goal with Hx: Int.repr (fst (bs_reload _ _)) <> _ |- _ => apply Hx; rewrite Ov1; reflexivity end. }
        rewrite Ov2.
        sep_apply (out_split1 shw pw ((acc ++ [fe_sym (fse_cell t st1')]) ++ [fe_sym (fse_cell t st2')]) oc H
                     ltac:(list_solve) Hfpw). Intros.
        forward. forward.
        repeat apply -> seq_assoc. apply semax_if_seq. forward_if.
        2: { rewrite Efm in *; discriminate. }
        forward_call (Tsh, v_state1, fe_base (fse_cell t st1') + r1, sht, dt, t, fm, Tsh, v_bitD, gv, s,
                      offset_val off base, p2, lo1').
        Intros r3.
        forward.
        rewrite ze8 by auto.
        sep_apply (out_merge1 shw pw ((acc ++ [fe_sym (fse_cell t st1')]) ++ [fe_sym (fse_cell t st2')]) oc
                     (fe_sym (fse_cell t (fe_base (fse_cell t st1') + r1))) H ltac:(list_solve) Hfpw).
        forward.
        rewrite fse2_stop2 in Tm by (unfold p2, p1 in *; lia).
        rewrite <- E1 in Tm.
        rewrite fin_some in Tm by list_solve.
        Exists (((acc ++ [fe_sym (fse_cell t st1')]) ++ [fe_sym (fse_cell t st2')]) ++
                  [fe_sym (fse_cell t (fe_base (fse_cell t st1') + r1))])
          (fe_base (fse_cell t (fe_base (fse_cell t st1') + r1)) + r3) (fe_base (fse_cell t st2') + r2)
          (p2 - fe_nb (fse_cell t (fe_base (fse_cell t st1') + r1))) lo1'.
        unfold LOCS, SEPS. rewrite Add1.
        entailer!.
        split; [list_solve | f_equal; list_solve]. }
      { (* no overflow: next iteration *)
        pose proof (reload_ok p2 lo1' ltac:(lia) ltac:(lia) Hnov2) as (Rno2 & Rb2 & Run2 & Rnu2 & Ror2).
        pose proof (reload_range p2 lo1') as Rrr2.
        clear Hinv Hinv1' Ror Rnu Rnu2 Tlo2.
        forward_if.
        { exfalso. match goal with Hx: fst (bs_reload _ _) = _ |- _ => apply Rno2; exact Hx end. }
        assert (E2: r2 = bs_peek_s s p1 (fe_nb (fse_cell t st2'))).
        { match goal with Hx: _ -> r2 = _ |- _ => rewrite Hx by lia end. symmetry; apply bs_peek_s_eq; [exact Hbytes | clear - Cn2 Hlog; lia | clear - Hnov2 Rb; unfold p2 in Hnov2; lia]. }
        ent_clear_peeks.
        rewrite fse2_step in Tm by (unfold p1 in *; lia).
        change (pos - fe_nb (fse_cell t st1')) with p1 in Tm.
        change (p1 - fe_nb (fse_cell t st2')) with p2 in Tm.
        rewrite <- E1, <- E2 in Tm.
        forward.
        Exists f' p2 (snd (bs_reload p2 lo1')) (fe_base (fse_cell t st1') + r1) (fe_base (fse_cell t st2') + r2)
          ((acc ++ [fe_sym (fse_cell t st1')]) ++ [fe_sym (fse_cell t st2')]).
        unfold LOCS, SEPS.
        entailer!.
        rewrite !Zlength_app, !Zlength_cons, !Zlength_nil. split; lia. } } }
    }
  Intros ws st1f st2f posf lof. unfold LOCS, SEPS.
  assert_PROP (field_compatible (tarray tuchar 256) [] pw) as Hfc2 by entailer!.
  assert (Esub: forall k, 0 <= k <= 256 -> force_val (sem_sub_pp tuchar (offset_val k pw) pw) = Vlong (Int64.repr k)).
  { clear - Hfc2. intros k Hk. destruct Hfc2 as (Hp & _ & Hsz & _). destruct pw; try contradiction.
    unfold sem_sub_pp. simpl. destruct (eq_block b b); [|congruence]. simpl.
    rewrite Ptrofs.sub_add_l, Ptrofs.sub_idem, Ptrofs.add_zero_l.
    unfold Ptrofs.divs. rewrite !Ptrofs.signed_repr by rep_lia. rewrite Z.quot_1_r.
    unfold Vptrofs. simpl. unfold Ptrofs.to_int64. rewrite Ptrofs.unsigned_repr by rep_lia. reflexivity. }
  forward.
  { entailer!. destruct pw; try contradiction. simpl. unfold sameblock. destruct (peq b b); [reflexivity|congruence]. }
  match goal with Hx: fse_weights_dec t s = Some ws |- _ => rewrite Hx end.
  Exists (Zlength ws) (zbytes ws ++ sublist (Zlength ws) 256 oc).
  first [rewrite (win_split sh (Zlength c) c off s base) by auto | rewrite (win_split sh N c off s base) by auto].
  sep_apply rep_data_at_. unfold t_bitd. rewrite Esub by list_solve.
  entailer!.
  list_solve.
Qed.
