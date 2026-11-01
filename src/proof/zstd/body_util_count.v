(* Bodies of group util: software bit counting over the De Bruijn tables. *)
Require Import Zstd.proof.zstd.Gprog.

(* ---------- arithmetic: lowest set bit ---------- *)

Lemma odd_factor v : 0 < v -> exists k j, 0 <= k /\ 0 <= j /\ v = 2 ^ k * (2 * j + 1).
Proof.
  intros Hv. assert (H0: 0 <= v) by lia. revert Hv. pattern v. apply Z_lt_induction; [|exact H0].
  clear. intros v IH Hv.
  destruct (Z.even v) eqn:E.
  - apply Z.even_spec in E. destruct E as [m Em].
    destruct (IH m) as (k & j & Hk & Hj & Ev); [lia|lia|].
    exists (k + 1), j. split; [lia|split; [lia|]].
    rewrite Z.pow_add_r by lia. rewrite Em, Ev. ring.
  - assert (O: Z.odd v = true) by (rewrite <- Z.negb_even, E; reflexivity).
    apply Z.odd_spec in O. destruct O as [m Em].
    exists 0, m. split; [lia|split; [lia|]]. rewrite Em. simpl. ring.
Qed.

Lemma land_odd_neg j : Z.land (2 * j + 1) (- (2 * j + 1)) = 1.
Proof.
  apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec.
  replace (- (2 * j + 1)) with (2 * (- j - 1) + 1) by ring.
  destruct (Z.eq_dec n 0) as [->|Hn0].
  - rewrite !Z.testbit_odd_0. reflexivity.
  - replace n with (Z.succ (n - 1)) by lia.
    rewrite !Z.testbit_odd_succ by lia.
    replace (- j - 1) with (Z.lnot j) by (unfold Z.lnot; lia).
    rewrite Z.lnot_spec by lia.
    rewrite (Z.bits_above_log2 1) by (simpl; lia).
    destruct (Z.testbit j (n - 1)); reflexivity.
Qed.

Lemma land_neg_factor k j : 0 <= k ->
  Z.land (2 ^ k * (2 * j + 1)) (- (2 ^ k * (2 * j + 1))) = 2 ^ k.
Proof.
  intros Hk.
  replace (- (2 ^ k * (2 * j + 1))) with (- (2 * j + 1) * 2 ^ k) by ring.
  rewrite (Z.mul_comm (2 ^ k)).
  rewrite <- !Z.shiftl_mul_pow2 by lia.
  rewrite <- Z.shiftl_land, land_odd_neg.
  rewrite Z.shiftl_mul_pow2 by lia. ring.
Qed.

Lemma ctz_factor k j : 0 <= k -> ctz (2 ^ k * (2 * j + 1)) = k.
Proof.
  intros Hk. unfold ctz. rewrite land_neg_factor by lia. apply Z.log2_pow2; lia.
Qed.

Lemma ctz_0 : ctz 0 = 0.
Proof. reflexivity. Qed.

Lemma int_and_neg w : 0 <= w <= Int.max_unsigned ->
  Int.and (Int.repr w) (Int.sub (Int.repr 0) (Int.repr w)) = Int.repr (Z.land w (- w)).
Proof.
  intros Hr.
  apply Int.same_bits_eq. intros i Hi.
  rewrite Int.bits_and by lia. unfold Int.sub.
  rewrite !Int.testbit_repr by lia.
  rewrite Z.land_spec. f_equal.
  rewrite !Int.unsigned_repr by rep_lia.
  reflexivity.
Qed.

Lemma pow_lt_32 k x : 0 <= k -> 0 < x -> 2 ^ k * x <= Int.max_unsigned -> k < 32.
Proof.
  intros Hk Hx Hr. destruct (Z_lt_le_dec k 32) as [|Hk32]; auto. exfalso.
  assert (2 ^ 32 <= 2 ^ k) by (apply Z.pow_le_mono_r; lia).
  assert (Int.max_unsigned = 2 ^ 32 - 1) by reflexivity. nia.
Qed.

Lemma ctz_table k : 0 <= k < 32 ->
  let i := Int.unsigned (Int.shru (Int.mul (Int.repr (2 ^ k)) (Int.repr 125613361)) (Int.repr 27)) in
  0 <= i < 32 /\ Znth i DeBruijnBytePos_val = Vint (Int.repr k).
Proof.
  intros Hk. assert (Hn: exists n, k = Z.of_nat n /\ (n < 32)%nat) by (exists (Z.to_nat k); lia).
  destruct Hn as (n & -> & Hn). clear Hk.
  do 32 (destruct n as [|n]; [vm_compute; split; [split; congruence | reflexivity] |]). lia.
Qed.

Lemma ctz_ok v : 0 <= v <= Int.max_unsigned ->
  let i := Int.unsigned (Int.shru (Int.mul (Int.and (Int.repr v) (Int.sub (Int.repr 0) (Int.repr v)))
             (Int.repr 125613361)) (Int.repr 27)) in
  0 <= i < 32 /\ Znth i DeBruijnBytePos_val = Vint (Int.repr (ctz v)).
Proof.
  intros Hv. rewrite int_and_neg by lia.
  destruct (Z.eq_dec v 0) as [->|Hv0].
  { vm_compute; split; [split; congruence | reflexivity]. }
  destruct (odd_factor v) as (k & j & Hk & Hj & Ev); [lia|].
  rewrite Ev in *. rewrite land_neg_factor, ctz_factor by lia.
  apply ctz_table. split; [lia|]. apply (pow_lt_32 k (2 * j + 1)); lia.
Qed.

(* ---------- arithmetic: the smear of countLeadingZeros ---------- *)

Definition zsmear (x c: Z) : Z := Z.lor x (Z.shiftr x c).
Definition ismear (x: int) (c: Z) : int := Int.or x (Int.shru x (Int.repr c)).

Lemma zsmear_step x k c : 0 < x -> Z.log2 x = k -> 0 <= c ->
  (forall i, k - c < i <= k -> 0 <= i -> Z.testbit x i = true) ->
  0 < zsmear x c /\ Z.log2 (zsmear x c) = k /\
  (forall i, k - 2 * c < i <= k -> 0 <= i -> Z.testbit (zsmear x c) i = true).
Proof.
  intros Hx Hk Hc Hb. unfold zsmear. pose proof (Z.log2_nonneg x).
  assert (0 <= Z.shiftr x c) by (apply Z.shiftr_nonneg; lia).
  assert (Hl: Z.log2 (Z.lor x (Z.shiftr x c)) = k).
  { rewrite Z.log2_lor by lia. rewrite Z.log2_shiftr by lia. lia. }
  split; [|split; [exact Hl|]].
  - assert (0 <= Z.lor x (Z.shiftr x c)) by (apply Z.lor_nonneg; lia).
    assert (Z.lor x (Z.shiftr x c) <> 0). { intro E. apply Z.lor_eq_0_iff in E. lia. }
    lia.
  - intros i Hi Hi0. rewrite Z.lor_spec.
    destruct (Z_lt_dec (k - c) i).
    + rewrite Hb by lia. reflexivity.
    + rewrite Z.shiftr_spec by lia. rewrite (Hb (i + c)) by lia. apply orb_true_r.
Qed.

Lemma smear_ones x k : 0 < x -> Z.log2 x = k ->
  (forall i, 0 <= i <= k -> Z.testbit x i = true) -> x = Z.ones (k + 1).
Proof.
  intros Hx Hk Hb. pose proof (Z.log2_nonneg x).
  apply Z.bits_inj'. intros n Hn. rewrite Z.testbit_ones_nonneg by lia.
  destruct (Z_le_gt_dec n k).
  - rewrite Hb by lia. symmetry. apply Z.ltb_lt; lia.
  - rewrite Z.bits_above_log2 by lia. symmetry. apply Z.ltb_ge; lia.
Qed.

Lemma ismear_repr x c : 0 < x -> Z.log2 x < 32 -> 0 <= c < 32 ->
  ismear (Int.repr x) c = Int.repr (zsmear x c).
Proof.
  intros Hx Hk Hc. unfold ismear, Int.or, Int.shru, zsmear.
  assert (x < 2 ^ 32) by (apply Z.log2_lt_pow2; lia).
  assert (Int.max_unsigned = 2 ^ 32 - 1) by reflexivity.
  assert (0 <= Z.shiftr x c <= x).
  { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|].
    apply Z.div_le_upper_bound; [lia|]. assert (0 < 2 ^ c) by (apply Z.pow_pos_nonneg; lia). nia. }
  rewrite (Int.unsigned_repr x) by lia. rewrite (Int.unsigned_repr c) by lia.
  rewrite (Int.unsigned_repr (Z.shiftr x c)) by lia. reflexivity.
Qed.

Definition ismear5 (x: int) : int := ismear (ismear (ismear (ismear (ismear x 1) 2) 4) 8) 16.

Lemma clz_core v : 0 < v <= Int.max_unsigned ->
  ismear5 (Int.repr v) = Int.repr (Z.ones (Z.log2 v + 1)).
Proof.
  intros Hv. unfold ismear5. set (k := Z.log2 v).
  assert (Hk: k < 32).
  { apply Z.log2_lt_pow2; [lia|]. assert (Int.max_unsigned = 2 ^ 32 - 1) by reflexivity. lia. }
  pose proof (Z.log2_nonneg v).
  destruct (zsmear_step v k 1) as (P1 & L1 & B1); try lia.
  { intros i Hi _. replace i with k by lia. apply Z.bit_log2; lia. }
  rewrite ismear_repr by lia.
  destruct (zsmear_step _ k 2 P1 L1) as (P2 & L2 & B2); [lia | intros; apply B1; lia |].
  rewrite ismear_repr by lia.
  destruct (zsmear_step _ k 4 P2 L2) as (P3 & L3 & B3); [lia | intros; apply B2; lia |].
  rewrite ismear_repr by lia.
  destruct (zsmear_step _ k 8 P3 L3) as (P4 & L4 & B4); [lia | intros; apply B3; lia |].
  rewrite ismear_repr by lia.
  destruct (zsmear_step _ k 16 P4 L4) as (P5 & L5 & B5); [lia | intros; apply B4; lia |].
  rewrite ismear_repr by lia.
  f_equal. apply smear_ones; auto. intros; apply B5; lia.
Qed.

Lemma clz_table k : 0 <= k < 32 ->
  let i := Int.unsigned (Int.shru (Int.mul (Int.repr (Z.ones (k + 1))) (Int.repr 130329821)) (Int.repr 27)) in
  0 <= i < 32 /\ Znth i DeBruijnClz_val = Vint (Int.repr k).
Proof.
  intros Hk. assert (Hn: exists n, k = Z.of_nat n /\ (n < 32)%nat) by (exists (Z.to_nat k); lia).
  destruct Hn as (n & -> & Hn). clear Hk.
  do 32 (destruct n as [|n]; [vm_compute; split; [split; congruence | reflexivity] |]). lia.
Qed.

Lemma clz_ok v : 0 <= v <= Int.max_unsigned ->
  let i := Int.unsigned (Int.shru (Int.mul (ismear5 (Int.repr v)) (Int.repr 130329821)) (Int.repr 27)) in
  0 <= i < 32 /\ Znth i DeBruijnClz_val = Vint (Int.repr (Z.log2 v)).
Proof.
  intros Hv. destruct (Z.eq_dec v 0) as [->|Hv0].
  { vm_compute; split; [split; congruence | reflexivity]. }
  rewrite clz_core by lia. apply clz_table.
  split; [apply Z.log2_nonneg|].
  apply Z.log2_lt_pow2; [lia|]. assert (Int.max_unsigned = 2 ^ 32 - 1) by reflexivity. lia.
Qed.

(* ---------- arithmetic: ctz of a 64-bit value from its two words ---------- *)

Lemma ctz_bits x : 0 < x ->
  Z.testbit x (ctz x) = true /\ (forall i, 0 <= i < ctz x -> Z.testbit x i = false) /\ 0 <= ctz x.
Proof.
  intros Hx. destruct (odd_factor x Hx) as (k & j & Hk & Hj & ->). rewrite ctz_factor by lia.
  rewrite (Z.mul_comm (2 ^ k)), <- Z.shiftl_mul_pow2 by lia.
  split; [|split; [|lia]].
  - rewrite Z.shiftl_spec by lia. replace (k - k) with 0 by lia. apply Z.testbit_odd_0.
  - intros i Hi. rewrite Z.shiftl_spec by lia. apply Z.testbit_neg_r; lia.
Qed.

Lemma ctz_char x k : 0 < x -> 0 <= k -> Z.testbit x k = true ->
  (forall i, 0 <= i < k -> Z.testbit x i = false) -> ctz x = k.
Proof.
  intros Hx Hk Hb Hl. destruct (ctz_bits x Hx) as (B & L & N).
  destruct (Z.lt_total (ctz x) k) as [C|[C|C]]; auto.
  - rewrite Hl in B by lia. discriminate.
  - rewrite L in Hb by lia. discriminate.
Qed.

Lemma ctz_lo v : 0 <= v -> v mod 2 ^ 32 <> 0 -> ctz v = ctz (v mod 2 ^ 32).
Proof.
  intros Hv Hm. assert (P: 0 < v mod 2 ^ 32) by (pose proof (Z.mod_pos_bound v (2 ^ 32)); lia).
  destruct (ctz_bits _ P) as (B & L & N).
  assert (K: ctz (v mod 2 ^ 32) < 32).
  { destruct (Z_lt_le_dec (ctz (v mod 2 ^ 32)) 32) as [|C]; auto.
    rewrite Z.mod_pow2_bits_high in B by lia. discriminate. }
  assert (v <> 0) by (intro E; subst; apply Hm; reflexivity).
  apply ctz_char; [lia | lia | |].
  - rewrite <- (Z.mod_pow2_bits_low v 32) by lia. exact B.
  - intros i Hi. rewrite <- (Z.mod_pow2_bits_low v 32) by lia. apply L; lia.
Qed.

Lemma ctz_hi v : 0 < v -> v mod 2 ^ 32 = 0 -> ctz v = 32 + ctz (v / 2 ^ 32).
Proof.
  intros Hv Hm.
  assert (Ev: v = Z.shiftl (v / 2 ^ 32) 32).
  { rewrite Z.shiftl_mul_pow2 by lia. pose proof (Z_div_mod_eq_full v (2 ^ 32)). lia. }
  set (h := v / 2 ^ 32) in *.
  assert (P: 0 < h).
  { assert (0 <= h) by (apply Z.div_pos; lia).
    destruct (Z.eq_dec h 0) as [E|]; [|lia]. rewrite E in Ev. simpl in Ev. lia. }
  destruct (ctz_bits _ P) as (B & L & N).
  apply ctz_char; [lia | lia | |].
  - rewrite Ev, Z.shiftl_spec by lia. replace (32 + ctz h - 32) with (ctz h) by lia. exact B.
  - intros i Hi. rewrite Ev, Z.shiftl_spec by lia. destruct (Z_lt_le_dec i 32).
    + apply Z.testbit_neg_r; lia.
    + apply L; lia.
Qed.

(* ---------- the De Bruijn tables out of zstd_globals ---------- *)

Definition zg_rest_pos (gv: globals) : mpred := (
  data_at Ews tint g_debuglevel_val (gv _g_debuglevel) *
  data_at Ers (tarray tuint 32) DeBruijnClz_val (gv _DeBruijnClz) *
  data_at Ers tulong zeroFilled_val (gv _zeroFilled) *
  data_at Ers (Tstruct ___gp_ZSTD_customMem noattr) ZSTD_defaultCMem_val (gv _ZSTD_defaultCMem) *
  data_at Ers (tarray tuint 3) repStartValue_val (gv _repStartValue) *
  data_at Ers (tarray tulong 4) ZSTD_fcs_fieldSize_val (gv _ZSTD_fcs_fieldSize) *
  data_at Ers (tarray tulong 4) ZSTD_did_fieldSize_val (gv _ZSTD_did_fieldSize) *
  data_at Ers tulong ZSTD_blockHeaderSize_val (gv _ZSTD_blockHeaderSize) *
  data_at Ers (tarray tuchar 36) LL_bits_val (gv _LL_bits) *
  data_at Ers (tarray tuchar 53) ML_bits_val (gv _ML_bits) *
  data_at Ers (tarray (tarray (Tstruct ___gp_algo_time_t noattr) 2) 16) algoTime_val (gv _algoTime) *
  data_at Ers (tarray tuint 36) LL_base_val (gv _LL_base) *
  data_at Ers (tarray tuint 32) OF_base_val (gv _OF_base) *
  data_at Ers (tarray tuchar 32) OF_bits_val (gv _OF_bits) *
  data_at Ers (tarray tuint 53) ML_base_val (gv _ML_base) *
  data_at Ers (tarray (Tstruct ___gp_ZSTD_seqSymbol noattr) 65) LL_defaultDTable_val (gv _LL_defaultDTable) *
  data_at Ers (tarray (Tstruct ___gp_ZSTD_seqSymbol noattr) 33) OF_defaultDTable_val (gv _OF_defaultDTable) *
  data_at Ers (tarray (Tstruct ___gp_ZSTD_seqSymbol noattr) 65) ML_defaultDTable_val (gv _ML_defaultDTable) *
  data_at Ers (tarray tuint 8) dec32table_val (gv _dec32table) *
  data_at Ers (tarray tint 8) dec64table_val (gv _dec64table) *
  eb_res gv)%logic.

Lemma zg_pos gv : zstd_globals gv =
  (data_at Ers (tarray tuint 32) DeBruijnBytePos_val (gv _DeBruijnBytePos) * zg_rest_pos gv)%logic.
Proof. unfold zstd_globals, zg_rest_pos. apply pred_ext; cancel. Qed.

Definition zg_rest_clz (gv: globals) : mpred := (
  data_at Ews tint g_debuglevel_val (gv _g_debuglevel) *
  data_at Ers (tarray tuint 32) DeBruijnBytePos_val (gv _DeBruijnBytePos) *
  data_at Ers tulong zeroFilled_val (gv _zeroFilled) *
  data_at Ers (Tstruct ___gp_ZSTD_customMem noattr) ZSTD_defaultCMem_val (gv _ZSTD_defaultCMem) *
  data_at Ers (tarray tuint 3) repStartValue_val (gv _repStartValue) *
  data_at Ers (tarray tulong 4) ZSTD_fcs_fieldSize_val (gv _ZSTD_fcs_fieldSize) *
  data_at Ers (tarray tulong 4) ZSTD_did_fieldSize_val (gv _ZSTD_did_fieldSize) *
  data_at Ers tulong ZSTD_blockHeaderSize_val (gv _ZSTD_blockHeaderSize) *
  data_at Ers (tarray tuchar 36) LL_bits_val (gv _LL_bits) *
  data_at Ers (tarray tuchar 53) ML_bits_val (gv _ML_bits) *
  data_at Ers (tarray (tarray (Tstruct ___gp_algo_time_t noattr) 2) 16) algoTime_val (gv _algoTime) *
  data_at Ers (tarray tuint 36) LL_base_val (gv _LL_base) *
  data_at Ers (tarray tuint 32) OF_base_val (gv _OF_base) *
  data_at Ers (tarray tuchar 32) OF_bits_val (gv _OF_bits) *
  data_at Ers (tarray tuint 53) ML_base_val (gv _ML_base) *
  data_at Ers (tarray (Tstruct ___gp_ZSTD_seqSymbol noattr) 65) LL_defaultDTable_val (gv _LL_defaultDTable) *
  data_at Ers (tarray (Tstruct ___gp_ZSTD_seqSymbol noattr) 33) OF_defaultDTable_val (gv _OF_defaultDTable) *
  data_at Ers (tarray (Tstruct ___gp_ZSTD_seqSymbol noattr) 65) ML_defaultDTable_val (gv _ML_defaultDTable) *
  data_at Ers (tarray tuint 8) dec32table_val (gv _dec32table) *
  data_at Ers (tarray tint 8) dec64table_val (gv _dec64table) *
  eb_res gv)%logic.

Lemma zg_clz gv : zstd_globals gv =
  (data_at Ers (tarray tuint 32) DeBruijnClz_val (gv _DeBruijnClz) * zg_rest_clz gv)%logic.
Proof. unfold zstd_globals, zg_rest_clz. apply pred_ext; cancel. Qed.

(* VST's [forward] hangs on a load from a constant table at a computed index (its entailer simplifies
   the symbolic index against the concrete table): this is its load_tac with the last two side conditions
   (the loaded value's type check, the address's type check) left to the caller. *)
Ltac load_table_tac :=
  match goal with
  | |- semax _ (|> (PROPx _ (LOCALx ?Q (SEPx _)))) (Sset _ _) _ =>
    let T1 := fresh "T1" in evar (T1: Maps.PTree.t val);
    let T2 := fresh "T2" in evar (T2: Maps.PTree.t (type * val));
    let G := fresh "GV" in evar (G: option globals);
    let L := fresh "LOCAL2PTREE" in
    assert (L: local2ptree Q = (T1, T2, nil, G)) by (subst T1 T2 G; prove_local2ptree);
    eapply semax_PTree_field_load_no_hint;
    [ exact L | reflexivity | reflexivity | reflexivity | reflexivity | solve_msubst_eval_LR
    | solve_msubst_efield_denote | econstructor | solve_field_address_gen | search_field_at_in_SEP | auto
    | solve_load_rule_evaluation | solve_legal_nested_field_in_entailment | idtac | idtac ];
    clear L T1 T2 G
  end.

Lemma body_ctz32_fallback :
  semax_body Vprog Gprog f_ZSTD_countTrailingZeros32_fallback ZSTD_countTrailingZeros32_fallback_spec.
Proof.
  start_function.
  rewrite zg_pos. Intros. destruct (ctz_ok v) as [Hi Hz]; [lia|].
  forget (Int.repr v) as y.
  eapply semax_seq'.
  { hoist_later_in_pre; load_table_tac.
    2: entailer!.
    forget (Int.unsigned (Int.shru (Int.mul (Int.and y (Int.sub (Int.repr 0) y)) (Int.repr 125613361)) (Int.repr 27))) as i.
    change (@Znth val Vundef i DeBruijnBytePos_val) with (@Znth val Inhabitant_val i DeBruijnBytePos_val).
    rewrite Hz. entailer!. }
  abbreviate_semax.
  forget (Int.unsigned (Int.shru (Int.mul (Int.and y (Int.sub (Int.repr 0) y)) (Int.repr 125613361)) (Int.repr 27))) as i.
  change (@Znth val Vundef i DeBruijnBytePos_val) with (@Znth val Inhabitant_val i DeBruijnBytePos_val).
  rewrite Hz. simpl remove_localdef_temp.
  forward. entailer!. rewrite zg_pos. cancel.
Qed.


Lemma body_clz32_fallback :
  semax_body Vprog Gprog f_ZSTD_countLeadingZeros32_fallback ZSTD_countLeadingZeros32_fallback_spec.
Proof.
  start_function.
  rewrite zg_clz. Intros. do 5 forward. destruct (clz_ok v) as [Hi Hz]; [lia|].
  change (Int.or (Int.or (Int.or (Int.or (Int.or (Int.repr v) (Int.shru (Int.repr v) (Int.repr 1))) _) _) _) _) with (ismear5 (Int.repr v)).
  forget (ismear5 (Int.repr v)) as x.
  eapply semax_seq'.
  { hoist_later_in_pre; load_table_tac.
    2: entailer!.
    forget (Int.unsigned (Int.shru (Int.mul x (Int.repr 130329821)) (Int.repr 27))) as i.
    change (@Znth val Vundef i DeBruijnClz_val) with (@Znth val Inhabitant_val i DeBruijnClz_val).
    rewrite Hz. entailer!. }
  abbreviate_semax.
  forget (Int.unsigned (Int.shru (Int.mul x (Int.repr 130329821)) (Int.repr 27))) as i.
  change (@Znth val Vundef i DeBruijnClz_val) with (@Znth val Inhabitant_val i DeBruijnClz_val).
  rewrite Hz. simpl remove_localdef_temp.
  forward. entailer!. rewrite zg_clz. cancel.
Qed.

Lemma body_ctz32 :
  semax_body Vprog Gprog f_ZSTD_countTrailingZeros32 ZSTD_countTrailingZeros32_spec.
Proof.
  start_function.
  forward_call (v, gv).
  forward.
Qed.

Lemma body_clz32 :
  semax_body Vprog Gprog f_ZSTD_countLeadingZeros32 ZSTD_countLeadingZeros32_spec.
Proof.
  start_function.
  forward_call (v, gv).
  forward.
Qed.

Lemma body_highbit32 :
  semax_body Vprog Gprog f_ZSTD_highbit32 ZSTD_highbit32_spec.
Proof.
  start_function.
  forward_call (v, gv).
  forward.
  entailer!. unfold highbit. do 2 f_equal. lia.
Qed.

Lemma body_ctz64 :
  semax_body Vprog Gprog f_ZSTD_countTrailingZeros64 ZSTD_countTrailingZeros64_spec.
Proof.
  start_function.
  forward. forward.
  set (lo := v mod 2 ^ 32). set (hi := v / 2 ^ 32).
  assert (Rlo: 0 <= lo < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
  assert (Rhi: 0 <= hi < 2 ^ 32).
  { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
    assert (Int64.max_unsigned = 2 ^ 64 - 1) by reflexivity. lia. }
  assert (Elo: Int.repr (Int64.unsigned (Int64.repr v)) = Int.repr lo).
  { rewrite Int64.unsigned_repr by lia. rewrite <- (Int.repr_unsigned (Int.repr v)), Int.unsigned_repr_eq.
    reflexivity. }
  assert (Ehi: Int64.unsigned (Int64.shru (Int64.repr v) (Int64.repr (Int.unsigned (Int.repr 32)))) = hi).
  { unfold Int64.shru. rewrite Int.unsigned_repr by rep_lia.
    rewrite (Int64.unsigned_repr v), (Int64.unsigned_repr 32) by rep_lia. rewrite Z.shiftr_div_pow2 by lia.
    apply Int64.unsigned_repr. assert (Int64.max_unsigned = 2 ^ 64 - 1) by reflexivity. lia. }
  rewrite Elo, Ehi.
  forward_if.
  - assert (E0: lo = 0) by assumption.
    forward_call (hi, gv).
    forward. entailer!. do 2 f_equal.
    destruct (Z.eqb_spec v 0) as [->|Hv0].
    + reflexivity.
    + rewrite (ctz_hi v) by (lia || exact E0). reflexivity.
  - assert (N0: lo <> 0) by assumption.
    forward_call (lo, gv).
    forward. entailer!.
    destruct (Z.eqb_spec v 0) as [->|Hv0].
    + exfalso. apply N0. reflexivity.
    + rewrite (ctz_lo v) by lia. reflexivity.
Qed.

Lemma bodies_util_count :
  semax_body Vprog Gprog f_ZSTD_countTrailingZeros32_fallback ZSTD_countTrailingZeros32_fallback_spec /\
  semax_body Vprog Gprog f_ZSTD_countTrailingZeros32 ZSTD_countTrailingZeros32_spec /\
  semax_body Vprog Gprog f_ZSTD_countLeadingZeros32_fallback ZSTD_countLeadingZeros32_fallback_spec /\
  semax_body Vprog Gprog f_ZSTD_countLeadingZeros32 ZSTD_countLeadingZeros32_spec /\
  semax_body Vprog Gprog f_ZSTD_countTrailingZeros64 ZSTD_countTrailingZeros64_spec /\
  semax_body Vprog Gprog f_ZSTD_highbit32 ZSTD_highbit32_spec.
Proof.
  exact (conj body_ctz32_fallback (conj body_ctz32 (conj body_clz32_fallback (conj body_clz32
    (conj body_ctz64 body_highbit32))))).
Qed.
