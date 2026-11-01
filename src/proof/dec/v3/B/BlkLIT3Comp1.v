(* ZSTD_decodeLiteralsBlock, the arms set_compressed (a Huffman tree description, then one or four streams) and
   set_repeat (the previous table, after the litEntropy check), part 1: the model facts of the header, the frame of
   the Huffman part (its pre- and postcondition lit_K / lit_J, the facts after the call lit_hfacts, exact against
   model/ExBlock.v), the facts the Huffman decoders' specifications give.  The arm is proved in BlkLIT3Comp2.v (the
   Huffman call), BlkLIT3Comp3.v (the split layout's copy to litExtraBuffer and move by 65536 - 32), BlkLIT3Comp4.v
   (the literal fields and the result), BlkLIT3Comp.v (the header, seg_comp). *)
Require Export Zstd.proof.dec.v3.B.BlkLIT3Exact.
Local Open Scope logic.

(* ---------- speed: loads and zstd's macro loops ---------- *)

(* VST's solve_load_rule_evaluation (floyd/simpl_reptype.v), run by every `forward` over a load, with `lazy` in place
   of its `cbv` (same reduction flags, hence the same normal form).  `cbv` evaluates the whole composite environment of
   zstd's structs, proofs included, at each load; `lazy` only the part the field's type needs.  Only the left side of
   the JMeq goal (and its type) is reduced: `lazy` on the whole goal would also reduce the instance of the evar on the
   right and unfold the local definitions (`set`) of the caller in the loaded value.  The files of this arm install it
   with `Local Ltac solve_load_rule_evaluation ::= lit_slre.` *)
Ltac lit_slre :=
  eapply JMeq_trans;
  [ clear;
    repeat
    match goal with
    | A : _ |- _ => clear A
    | A := _ |- _ => clear A
    end;
    match goal with
    | |- JMeq (@proj_reptype _ _ ?gfs _) _ =>
      remember_indexes gfs
    end;
    match goal with
    | |- JMeq (@proj_reptype ?cs ?t ?gfs ?v) _ =>
        let opaque_v := fresh "opaque_v" in
              remember v as opaque_v;
              change @proj_reptype with @proj_reptype';
              match goal with |- @JMeq ?A ?L ?B ?Y =>
                let A' := eval lazy - [ sublist.Znth Int.repr JMeq myfst mysnd] in A in
                let L' := eval lazy - [ sublist.Znth Int.repr JMeq myfst mysnd] in L in
                change_no_check (@JMeq A' L' B Y) end;
              change @myfst with @fst;
              change @mysnd with @snd;
              subst opaque_v;
              repeat match goal with
                     | |- context [@fst ?a ?b (?c,?d)] =>
                              let u := eval hnf in (@fst a b (c,d)) in
                                 change_no_check (@fst a b (c,d)) with c
                     | |- context [@snd ?a ?b (?c,?d)] =>
                               let u := eval hnf in (@snd a b (c,d)) in
                                  change_no_check (@snd a b (c,d)) with d
                    end
        end;
        subst; apply JMeq_refl
  | canon_load_result; apply JMeq_refl ].

(* The do-nothing macro loops `for(;;break) {}` and `for(;;break) { if (0) ... }` before a statement c behave as
   c alone.  These two rules step over them without going through forward_loop and entailer!, which on this
   function's large preconditions cost tens of seconds per loop. *)
Lemma lit_loop_skip {cs: compspecs} (Espec: OracleKind) (Delta: tycontext) (P: environ -> mpred) (c: statement)
    (R: ret_assert) :
  semax Delta P c R -> semax Delta P (Ssequence (Sloop Sskip Sbreak) c) R.
Proof.
  intros H. eapply semax_seq'; [| exact H].
  apply semax_loop with (Q' := P).
  - eapply semax_post; [| | | | apply semax_skip]; intros; apply andp_left2;
      first [apply derives_refl | apply FF_left | intros ?; apply FF_left].
  - exact (semax_break Delta (loop2_ret_assert P (normal_ret_assert P))).
Qed.

Lemma lit_loop_if0 {cs: compspecs} (Espec: OracleKind) (Delta: tycontext) (P: environ -> mpred) (X c: statement)
    (R: ret_assert) :
  semax Delta P c R ->
  semax Delta P (Ssequence (Sloop (Sifthenelse (Econst_int (Int.repr 0) tint) X Sskip) Sbreak) c) R.
Proof.
  intros H. eapply semax_seq'; [| exact H].
  apply semax_loop with (Q' := P).
  - eapply semax_pre; [| apply semax_ifthenelse; [reflexivity | |]].
    { apply andp_left2. eapply derives_trans; [| apply now_later]. apply andp_right; [| apply derives_refl].
      intro rho. unfold tc_expr. simpl. apply TT_right. }
    + eapply semax_pre with (P' := FF); [| apply semax_ff].
      apply andp_left2, andp_left2. intro rho. unfold local, lift1. unfold_lift. simpl.
      apply prop_left. intros Hf. inversion Hf.
    + eapply semax_pre with (P' := P); [apply andp_left2, andp_left1, derives_refl |].
      eapply semax_post; [| | | | apply semax_skip]; intros; apply andp_left2;
        first [apply derives_refl | apply FF_left | intros ?; apply FF_left].
  - exact (semax_break Delta (loop2_ret_assert P (normal_ret_assert P))).
Qed.

(* one macro loop: by the two rules above when it is followed by a statement, else as lit_skiploop *)
Ltac lit_skip1 :=
  repeat match goal with |- semax _ _ (Ssequence (Ssequence _ _) _) _ => apply -> seq_assoc end;
  first [ apply lit_loop_skip | apply lit_loop_if0 | lit_skiploop ].

(* lit_errpath with lit_skip1 *)
Ltac lit_errp := do 4 lit_skip1; forward.

(* the side conditions of semax_post, as rules: no unfolding of the function's postcondition *)
Lemma lit_ovr_FF (R: ret_assert) (P: environ -> mpred) : RA_normal (overridePost FF R) |-- P.
Proof. destruct R; apply FF_left. Qed.

Lemma lit_R_brk (P P' F: environ -> mpred) :
  RA_break (overridePost FF (switch_ret_assert (frame_ret_assert (function_body_ret_assert tulong P) F))) |--
  RA_break (overridePost FF (switch_ret_assert (frame_ret_assert (function_body_ret_assert tulong P') F))).
Proof. intro rho. simpl. apply derives_refl. Qed.

Lemma lit_R_cnt (P P' F: environ -> mpred) :
  RA_continue (overridePost FF (switch_ret_assert (frame_ret_assert (function_body_ret_assert tulong P) F))) |--
  RA_continue (overridePost FF (switch_ret_assert (frame_ret_assert (function_body_ret_assert tulong P') F))).
Proof. intro rho. simpl. apply derives_refl. Qed.

(* ---------- the header ---------- *)

Lemma lit_dl_lt5 (oh: option huf_table) (s: list Z) (bsm e: Z) :
  Zlength s < 5 -> Z.land (byte_at s 0) 3 = e -> (e = 2 \/ e = 3) -> decode_literals oh s bsm = None.
Proof.
  intros H Ht He. unfold decode_literals. cbv zeta. rewrite Ht, (proj2 (Z.ltb_lt _ _) H).
  destruct (Zlength s <? 2); [reflexivity |].
  destruct He as [-> | ->]; [reflexivity | destruct oh; reflexivity].
Qed.

(* ---------- model facts of set_compressed / set_repeat ---------- *)
Local Open Scope Z_scope.

Lemma litc_le_value_range (l: list Z) : bytes_ok l -> 0 <= le_value l < 2 ^ (8 * Zlength l).
Proof.
  induction l as [| b l IH]; intros Hb.
  - simpl. lia.
  - inversion Hb as [| ? ? Hb0 Hl]; subst. specialize (IH Hl). unfold is_byte in Hb0.
    rewrite Zlength_cons. simpl le_value.
    replace (8 * Z.succ (Zlength l)) with (8 + 8 * Zlength l) by lia.
    rewrite Z.pow_add_r by (pose proof (Zlength_nonneg l); lia). change (2 ^ 8) with 256. nia.
Qed.

Lemma lit_lhc_range (s: list Z) : bytes_ok s -> 4 <= Zlength s -> 0 <= le_field s 0 4 < 2 ^ 32.
Proof.
  intros Hb Hn. unfold le_field, slice. simpl skipn.
  assert (Hl: Zlength (firstn 4 s) = 4).
  { rewrite Zlength_correct, firstn_length. rewrite Zlength_correct in Hn. lia. }
  pose proof (litc_le_value_range (firstn 4 s)) as H. rewrite Hl in H. apply H.
  unfold bytes_ok in *. apply Forall_firstn. exact Hb.
Qed.

Lemma lit_syms_len (t: huf_table) (V: list Z) (k: nat) (pos: Z) (l: list Z) (q: Z) :
  huf_decode_syms t V k pos = Some (l, q) -> length l = k.
Proof.
  revert pos l q. induction k as [| k IH]; intros pos l q H; simpl in H.
  - inversion H; reflexivity.
  - destruct (nth _ _ _) as [sy nb].
    destruct (pos - nb <? 0); [discriminate |].
    destruct (huf_decode_syms t V k (pos - nb)) as [[l' q'] |] eqn:E; [| discriminate].
    inversion H; subst. simpl. f_equal. eapply IH; eauto.
Qed.

Lemma lit_stream_len (t: huf_table) (s: list Z) (k: Z) (l: list Z) :
  0 <= k -> huf_decode_stream t s k = Some l -> Zlength l = k.
Proof.
  intros Hk H. unfold huf_decode_stream in H.
  destruct (negb (bs_okb s)); [discriminate |].
  destruct (huf_decode_syms t s (Z.to_nat k) (bs_total s)) as [[l' q] |] eqn:E; [| discriminate].
  destruct q; try discriminate. inversion H; subst.
  apply lit_syms_len in E. rewrite Zlength_correct, E. lia.
Qed.

Lemma lit_4s_len (t: huf_table) (b: list Z) (k: Z) (l: list Z) :
  0 <= k -> huf_decode_4streams t b k = Some l -> Zlength l = k.
Proof.
  intros Hk H. unfold huf_decode_4streams in H.
  destruct (Z.of_nat (length b) <? 10); [discriminate |].
  destruct (_ <? 1); [discriminate |].
  destruct (k - 3 * ((k + 3) / 4) <? 0) eqn:E3; [discriminate |]. apply Z.ltb_ge in E3.
  assert (Hs: 0 <= (k + 3) / 4) by (apply Z.div_pos; lia).
  repeat match type of H with context [huf_decode_stream ?a ?b ?c] =>
    let E := fresh "E" in destruct (huf_decode_stream a b c) eqn:E end; inversion H; subst.
  repeat match goal with E: huf_decode_stream _ _ _ = Some _ |- _ => apply lit_stream_len in E; [| lia] end.
  rewrite !Zlength_app. lia.
Qed.

Lemma lit_lits_len (four: bool) (cb: list Z) (n: Z) (t: huf_table) (l: list Z) :
  0 <= n -> huf_lits four cb n = Some (t, l) -> Zlength l = n.
Proof.
  intros Hn H. unfold huf_lits in H.
  destruct (huf_parse_desc cb) as [[t0 h] |]; [| discriminate].
  destruct (h >=? Zlength cb); [discriminate |].
  destruct four;
    [destruct (huf_decode_4streams _ _ _) eqn:E | destruct (huf_decode_stream _ _ _) eqn:E];
    try discriminate; inversion H; subst;
    [eapply lit_4s_len | eapply lit_stream_len]; eauto.
Qed.

Lemma lit_with_len (four: bool) (t: huf_table) (cb: list Z) (n: Z) (l: list Z) :
  0 <= n -> huf_lits_with four t cb n = Some l -> Zlength l = n.
Proof.
  intros Hn H. unfold huf_lits_with in H.
  destruct four; [eapply lit_4s_len | eapply lit_stream_len]; eauto.
Qed.

(* the literals header of a compressed section: lhSize, litSize, litCSize, singleStream *)

(* what the Huffman call computes, by the model: the literals and the table *)
Definition lit_model (e: Z) (oh: option huf_table) (four: bool) (cb: list Z) (n: Z) : option (list Z * huf_table) :=
  if e =? 2 then match huf_lits four cb n with Some (t, l) => Some (l, t) | None => None end
  else match oh with
       | Some t => match huf_lits_with four t cb n with Some l => Some (l, t) | None => None end
       | None => None
       end.


Lemma lit_dl_comp (oh: option huf_table) (s: list Z) (bsm e lh n cs: Z) (single: bool) :
  5 <= Zlength s -> Z.land (byte_at s 0) 3 = e -> (e = 2 \/ e = 3) -> (e = 3 -> oh <> None) ->
  lit_hdr s = (lh, n, cs, single) -> 0 <= lh -> 0 <= cs ->
  decode_literals oh s bsm =
  if n >? bsm then None else if andb (negb single) (n <? 6) then None else if cs + lh >? Zlength s then None else
  match lit_model e oh (negb single) (sublist lh (lh + cs) s) n with
  | Some (l, t) => Some (l, lh + cs, Some t)
  | None => None
  end.
Proof.
  intros H5 Ht He Hx Hh Hlh Hcs.
  assert (Hcb: slice s lh cs = sublist lh (lh + cs) s).
  { unfold slice, sublist. rewrite firstn_skipn_comm. f_equal. f_equal. rewrite <- Z2Nat.inj_add; f_equal; lia. }
  unfold decode_literals. cbv zeta. rewrite Ht.
  replace (Zlength s <? 2) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (Zlength s <? 5) with false by (symmetry; apply Z.ltb_ge; lia).
  unfold lit_hdr in Hh. cbv zeta in Hh.
  rewrite Hh. cbv beta iota. rewrite Hcb. unfold MIN_LITERALS_FOR_4_STREAMS.
  destruct (n >? bsm); [destruct He as [-> | ->]; [reflexivity | destruct oh; reflexivity] |].
  destruct (andb (negb single) (n <? 6)); [destruct He as [-> | ->]; [reflexivity | destruct oh; reflexivity] |].
  destruct (cs + lh >? Zlength s) eqn:E3; [destruct He as [-> | ->]; [reflexivity | destruct oh; reflexivity] |].
  rewrite Z.gtb_ltb, Z.ltb_ge in E3.
  assert (Hlcb: Zlength (sublist lh (lh + cs) s) = cs) by (rewrite Zlength_sublist by lia; lia).
  unfold lit_model, huf_lits, huf_lits_with.
  destruct He as [-> | ->].
  - cbn [Z.eqb Pos.eqb andb]. rewrite Hlcb.
    destruct (huf_parse_desc _) as [[t h] |]; [| reflexivity].
    destruct (h >=? cs); [reflexivity |].
    destruct single; cbn [negb];
      [destruct (huf_decode_stream _ _ _) | destruct (huf_decode_4streams _ _ _)]; reflexivity.
  - destruct oh as [t |]; [| exfalso; apply Hx; auto].
    cbn [Z.eqb Pos.eqb andb skipn Z.to_nat].
    destruct single; cbn [negb];
      [destruct (huf_decode_stream _ _ _) | destruct (huf_decode_4streams _ _ _)]; reflexivity.
Qed.

Local Open Scope Z_scope.
Lemma litc_lhl (b: Z) : 0 <= b < 256 ->
  Int.and (Int.shr (Int.repr b) (Int.repr 2)) (Int.repr 3) = Int.repr (Z.land (Z.shiftr b 2) 3).
Proof.
  intros Hb. unfold Int.and, Int.shr. rewrite (Int.signed_repr b) by rep_lia.
  rewrite (Int.unsigned_repr 2) by rep_lia. rewrite (Int.unsigned_repr 3) by rep_lia.
  assert (0 <= Z.shiftr b 2 < 256).
  { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 2) with 4. split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia. }
  rewrite Int.unsigned_repr by rep_lia. reflexivity.
Qed.


Lemma litc_shiftr_le (x k: Z) : 0 <= x -> 0 <= k -> 0 <= Z.shiftr x k <= x.
Proof.
  intros Hx Hk. rewrite Z.shiftr_div_pow2 by lia.
  assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; nia].
Qed.

Lemma lit_fld (x k m j: Z) : 0 <= x < 2 ^ 32 -> 0 <= k < 32 -> m = Z.ones j -> 0 <= j <= 31 ->
  Int.unsigned (Int.and (Int.shru (Int.repr x) (Int.repr k)) (Int.repr m)) = Z.land (Z.shiftr x k) m.
Proof.
  intros Hx Hk Hm Hj. unfold Int.and, Int.shru.
  rewrite (Int.unsigned_repr x) by rep_lia. rewrite (Int.unsigned_repr k) by rep_lia.
  assert (0 <= Z.shiftr x k <= x) by (apply litc_shiftr_le; lia).
  assert (Hp: 0 < 2 ^ j <= 2 ^ 31).
  { split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]. }
  assert (Hm2: 0 <= m < 2 ^ 31) by (subst m; rewrite Z.ones_equiv; lia).
  rewrite (Int.unsigned_repr (Z.shiftr x k)) by rep_lia. rewrite (Int.unsigned_repr m) by rep_lia.
  apply Int.unsigned_repr. subst m. rewrite Z.land_ones by lia.
  pose proof (Z.mod_pos_bound (Z.shiftr x k) (2 ^ j) ltac:(lia)). rep_lia.
Qed.

Lemma litc_shru (x k: Z) : 0 <= x < 2 ^ 32 -> 0 <= k < 32 ->
  Int.unsigned (Int.shru (Int.repr x) (Int.repr k)) = Z.shiftr x k.
Proof.
  intros Hx Hk. unfold Int.shru.
  rewrite (Int.unsigned_repr x) by rep_lia. rewrite (Int.unsigned_repr k) by rep_lia.
  apply Int.unsigned_repr. pose proof (litc_shiftr_le x k ltac:(lia) ltac:(lia)). rep_lia.
Qed.

Lemma lit_cs3 (x b: Z) : 0 <= x < 2 ^ 32 -> 0 <= b < 256 ->
  Int64.add (Int64.repr x) (Int64.shl (Int64.repr b) (Int64.repr 10)) = Int64.repr (x + b * 1024).
Proof.
  intros Hx Hb. unfold Int64.shl.
  rewrite (Int64.unsigned_repr b) by rep_lia. rewrite (Int64.unsigned_repr 10) by rep_lia.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 10) with 1024.
  rewrite Int64.add_unsigned, (Int64.unsigned_repr x), (Int64.unsigned_repr (b * 1024)) by rep_lia.
  reflexivity.
Qed.

Lemma lit_land_ones (x j: Z) : 0 <= j -> 0 <= Z.land x (Z.ones j) < 2 ^ j.
Proof.
  intros Hj. rewrite Z.land_ones by lia. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
Qed.

Lemma litc_shiftr_lt (x k m: Z) : 0 <= k -> 0 <= m -> 0 <= x < 2 ^ (k + m) -> Z.shiftr x k < 2 ^ m.
Proof.
  intros Hk Hm Hx. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_lt_upper_bound.
  - apply Z.pow_pos_nonneg; lia.
  - rewrite <- Z.pow_add_r by lia. lia.
Qed.

Lemma lit_tup4 {A B C D: Type} (a a': A) (b b': B) (c c': C) (x x': D) :
  (a, b, c, x) = (a', b', c', x') -> a = a' /\ b = b' /\ c = c' /\ x = x'.
Proof. intros H. inversion H. auto. Qed.

Lemma lit_hdr_range (s: list Z) (lh n cs: Z) (single: bool) :
  bytes_ok s -> 5 <= Zlength s -> lit_hdr s = (lh, n, cs, single) ->
  3 <= lh <= 5 /\ 0 <= n <= 262143 /\ 0 <= cs < 2 ^ 18 /\ (single = true -> lh = 3).
Proof.
  intros Hb H5 Hh.
  pose proof (lit_lhc_range s Hb ltac:(lia)) as Hc.
  pose proof (lit_byte_range s 4 Hb) as B4.
  pose proof (litc_shiftr_le (le_field s 0 4) 4 ltac:(lia) ltac:(lia)).
  unfold lit_hdr in Hh. cbv zeta in Hh.
  destruct (_ =? 2); [| destruct (_ =? 3)]; apply lit_tup4 in Hh; destruct Hh as (<- & <- & <- & <-).
  - pose proof (lit_land_ones (Z.shiftr (le_field s 0 4) 4) 14 ltac:(lia)).
    pose proof (litc_shiftr_lt (le_field s 0 4) 18 14 ltac:(lia) ltac:(lia) ltac:(simpl; lia)).
    pose proof (litc_shiftr_le (le_field s 0 4) 18 ltac:(lia) ltac:(lia)).
    change (Z.ones 14) with 16383 in *. change (2 ^ 14) with 16384 in *. repeat split; try lia; discriminate.
  - pose proof (lit_land_ones (Z.shiftr (le_field s 0 4) 4) 18 ltac:(lia)).
    pose proof (litc_shiftr_lt (le_field s 0 4) 22 10 ltac:(lia) ltac:(lia) ltac:(simpl; lia)).
    pose proof (litc_shiftr_le (le_field s 0 4) 22 ltac:(lia) ltac:(lia)).
    change (Z.ones 18) with 262143 in *. change (2 ^ 18) with 262144 in *. change (2 ^ 10) with 1024 in *.
    repeat split; try lia; discriminate.
  - pose proof (lit_land_ones (Z.shiftr (le_field s 0 4) 4) 10 ltac:(lia)).
    pose proof (lit_land_ones (Z.shiftr (le_field s 0 4) 14) 10 ltac:(lia)).
    change (Z.ones 10) with 1023 in *. change (2 ^ 10) with 1024 in *. change (2 ^ 18) with 262144.
    repeat split; try lia.
Qed.

Local Open Scope logic.

(* a byte array as three consecutive pieces [0,a), [a,b), [b,N) *)
Lemma litc_split3 (sh: share) (N a b: Z) (c: list val) (q: val) :
  0 <= a <= b -> b <= N -> Zlength c = N -> field_compatible (tarray tuchar N) [] q ->
  data_at sh (tarray tuchar N) c q =
  data_at sh (tarray tuchar a) (sublist 0 a c) q * data_at sh (tarray tuchar (b - a)) (sublist a b c) (offset_val a q) *
  data_at sh (tarray tuchar (N - b)) (sublist b N c) (offset_val b q).
Proof.
  intros Hab HbN Hc FC. unfold tarray.
  rewrite (split3_data_at_Tarray_tuchar sh N a b c q) by (auto; lia).
  rewrite !field_address0_offset.
  - simpl. rewrite !Z.mul_1_l. reflexivity.
  - apply field_compatible0_cons. split; [simpl; lia | auto with field_compatible].
  - apply field_compatible0_cons. split; [simpl; lia | auto with field_compatible].
Qed.

(* the input window as its own array (MEM_readLE32 wants the bytes as zbytes) *)
Lemma litc_win_split (sh: share) (ic: list val) (ib: val) (ioff: Z) (s: list Z) :
  0 <= ioff -> ioff + Zlength s <= Zlength ic -> sublist ioff (ioff + Zlength s) ic = zbytes s ->
  field_compatible (tarray tuchar (Zlength ic)) [] ib ->
  data_at sh (tarray tuchar (Zlength ic)) ic ib =
  data_at sh (tarray tuchar ioff) (sublist 0 ioff ic) ib *
  data_at sh (tarray tuchar (Zlength s)) (zbytes s) (offset_val ioff ib) *
  data_at sh (tarray tuchar (Zlength ic - (ioff + Zlength s))) (sublist (ioff + Zlength s) (Zlength ic) ic)
    (offset_val (ioff + Zlength s) ib).
Proof.
  intros H0 H1 Hw FC. pose proof (Zlength_nonneg s). rewrite (litc_split3 sh (Zlength ic) ioff (ioff + Zlength s) ic ib) by (auto; lia).
  rewrite Hw. replace (ioff + Zlength s - ioff) with (Zlength s) by lia. reflexivity.
Qed.

Lemma lit_win_join (sh: share) (ic: list val) (ib: val) (ioff: Z) (s: list Z) :
  0 <= ioff -> ioff + Zlength s <= Zlength ic -> sublist ioff (ioff + Zlength s) ic = zbytes s ->
  field_compatible (tarray tuchar (Zlength ic)) [] ib ->
  data_at sh (tarray tuchar ioff) (sublist 0 ioff ic) ib *
  data_at sh (tarray tuchar (Zlength s)) (zbytes s) (offset_val ioff ib) *
  data_at sh (tarray tuchar (Zlength ic - (ioff + Zlength s))) (sublist (ioff + Zlength s) (Zlength ic) ic)
    (offset_val (ioff + Zlength s) ib) |--
  data_at sh (tarray tuchar (Zlength ic)) ic ib.
Proof. intros. rewrite (litc_win_split sh ic ib ioff s) by auto. apply derives_refl. Qed.

Lemma lit_land3c (b: Z) : 0 <= Z.land b 3 <= 3.
Proof.
  change (Z.land b 3) with (Z.land b (Z.ones 2)). rewrite Z.land_ones by lia.
  assert (H4: 0 < 2 ^ 2) by reflexivity. pose proof (Z.mod_pos_bound b (2 ^ 2) H4).
  change (2 ^ 2) with 4 in *. lia.
Qed.

Transparent denote_tc_test_eq.
Lemma litc_tc_null (P: mpred) (b: block) (i: ptrofs) :
  P |-- weak_valid_pointer (Vptr b i) -> P |-- denote_tc_test_eq (Vptr b i) (Vlong (Int64.repr 0)).
Proof. intros H. unfold denote_tc_test_eq; simpl. apply andp_right; [apply prop_right; reflexivity | exact H]. Qed.
Opaque denote_tc_test_eq.

(* a cell of a byte array is a valid pointer *)
Lemma lit_arr_wvp (sh: share) (c: list val) (q: val) (k: Z) :
  readable_share sh -> 0 <= k < Zlength c ->
  data_at sh (tarray tuchar (Zlength c)) c q |-- weak_valid_pointer (offset_val k q).
Proof.
  intros Hsh Hk. assert_PROP (field_compatible (tarray tuchar (Zlength c)) [] q) as FC by entailer!.
  rewrite (litc_split3 sh (Zlength c) k (k + 1) c q) by (auto; lia).
  apply sepcon_weak_valid_pointer1, sepcon_weak_valid_pointer2.
  apply valid_pointer_weak', data_at_valid_ptr; [apply readable_nonidentity; auto | simpl; lia].
Qed.

Lemma lit_model_len (e: Z) (oh: option huf_table) (four: bool) (cb: list Z) (n: Z) (l: list Z) (t: huf_table) :
  0 <= n -> lit_model e oh four cb n = Some (l, t) -> Zlength l = n.
Proof.
  intros Hn H. unfold lit_model in H. destruct (e =? 2).
  - destruct (huf_lits four cb n) as [[t0 l0] |] eqn:E; inversion H; subst. eapply lit_lits_len; eauto.
  - destruct oh as [t0 |]; [| discriminate].
    destruct (huf_lits_with four t0 cb n) as [l0 |] eqn:E; inversion H; subst. eapply lit_with_len; eauto.
Qed.

Lemma lit_ltu_add (a b c: Z) : 0 <= a <= 2 ^ 40 -> 0 <= b <= 2 ^ 40 -> 0 <= c <= 2 ^ 40 ->
  Int64.ltu (Int64.repr a) (Int64.add (Int64.repr b) (Int64.repr c)) = (a <? b + c).
Proof.
  intros Ha Hb Hc. unfold Int64.ltu. rewrite Int64.add_unsigned.
  rewrite (Int64.unsigned_repr b), (Int64.unsigned_repr c), (Int64.unsigned_repr (b + c)), (Int64.unsigned_repr a)
    by rep_lia.
  destruct (zlt a (b + c)); symmetry; [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Qed.

Ltac lit_false := exfalso; first [lia | match goal with H: ?a <> ?a |- _ => apply H; reflexivity end
  | match goal with H: Int.repr _ = Int.zero |- _ => apply (f_equal Int.unsigned) in H; vm_compute in H; discriminate end].

Lemma lit_cfg_fold (p: val) :
  field_at Ews t_dctx (DOT _disableHufAsm) (Vint (Int.repr 0)) p |-- cfg_lit p.
Proof. unfold cfg_lit. cancel. Qed.

(* ---------- exactness: pure facts ---------- *)
Local Open Scope Z_scope.

(* byte lists are determined by their cells *)
Lemma lit_zbytes_inj (a b: list Z) : bytes_ok a -> bytes_ok b -> zbytes a = zbytes b -> a = b.
Proof.
  intros Ha. revert b. induction Ha as [| x a Hx Ha IH]; intros b Hb E; destruct b as [| y b]; try discriminate.
  - reflexivity.
  - inversion Hb as [| ? ? Hy Hb']; subst. unfold is_byte in Hx, Hy.
    pose proof (f_equal (fun c => match c with Vint i :: _ => Int.unsigned i | _ => 0 end) E) as E1.
    pose proof (f_equal (@tl val) E) as E2. cbn [map] in E1. simpl in E2.
    rewrite !Int.unsigned_repr in E1 by rep_lia. subst y.
    f_equal. apply IH; auto.
Qed.

(* an array that differs from oc only in [k, k + n), where it holds v, is oc with v stored at k *)
Lemma lit_cwr_of (oc oc1 v: list val) (k n: Z) :
  Zlength oc1 = Zlength oc -> unchanged_outside oc oc1 k (k + n) -> sublist k (k + n) oc1 = v -> Zlength v = n ->
  0 <= k -> 0 <= n -> k + n <= Zlength oc -> oc1 = cwr oc k v.
Proof.
  intros HL U Hs Hv Hk Hn Hkn. unfold cwr. rewrite Hv. subst v.
  apply Znth_eq_ext; [list_solve |]. intros j Hj.
  destruct (Z_lt_le_dec j k) as [J1 | J1]; [| destruct (Z_lt_le_dec j (k + n)) as [J2 | J2]].
  - rewrite app_Znth1 by list_solve. rewrite Znth_sublist by lia. rewrite U by lia. f_equal; lia.
  - rewrite app_Znth2 by list_solve. rewrite app_Znth1 by list_solve.
    rewrite !Zlength_sublist by lia. rewrite Znth_sublist by lia. f_equal; lia.
  - rewrite app_Znth2 by list_solve. rewrite app_Znth2 by list_solve.
    rewrite !Zlength_sublist by lia. rewrite Znth_sublist by lia. rewrite U by lia. f_equal; lia.
Qed.

(* memmove within one array is a store of the source cells *)
Lemma lit_mm_cwr (c: list val) (si di len: Z) :
  0 <= len -> 0 <= si -> si + len <= Zlength c -> 0 <= di -> di + len <= Zlength c ->
  mm_result c (Zlength c) si di len = cwr c di (sublist si (si + len) c).
Proof. intros. unfold mm_result, cwr. rewrite Zlength_sublist by lia. f_equal. f_equal. f_equal. lia. Qed.

(* the literals xh_dctx decodes are bytes *)
Lemma lit_dctx_bytes (x2 single: bool) (cb: list Z) (n: Z) (l: list Z) (t: xhuf) (ht: huf_table) (h: Z) :
  huf_ok ht -> x_readstats cb = Some (ht, h) -> xh_dctx x2 single cb n = Some (l, t) -> bytes_ok l.
Proof.
  intros Ht Hr Hd. unfold xh_dctx, x_huf_read in Hd. rewrite Hr in Hd.
  destruct (Zlength cb <=? h); [discriminate |].
  destruct (x_huf_decode _ _ _ _) as [l0 |] eqn:E; [| discriminate].
  inversion Hd; subst. eapply xl_dec_bytes; eauto.
Qed.

(* the table type after the arm: the one the call builds (set_compressed), else the one used (set_repeat) *)
Definition lit_x2' (e: Z) (x2 single: bool) (n: Z) (cb: list Z) : bool :=
  if e =? 2 then huf_dctx_x2 (negb single) n cb else x2.

(* the model's Huffman part (ExHuf.x_lits_huf) against the call's result r, its literals l and table ht *)
Definition lit_xfacts (e: Z) (ox: option ddx) (oh: option huf_table) (x2 single: bool) (cb: list Z) (n r: Z)
    (l: list Z) (ht: huf_table) : Prop :=
  ox = None ->
  match x_lits_huf (option_map (xhuf_of x2) oh) e single cb n with
  | None => is_error_code r = true
  | Some (l0, t0) => r = n /\ l = l0 /\ t0 = xhuf_of (lit_x2' e x2 single n cb) ht
  end.

(* the output array and litExtraBuffer at the end of the arm (success), from the array oc after
   ZSTD_allocateLiteralsBuffer and litExtraBuffer lxb before: as BlkLIT3Exact.lx_huf states them *)
Definition lit_oc2 (streaming cap bsm n d: Z) (oc: list val) (l: list Z) : list val :=
  if alloc_loc streaming cap bsm n =? LOC_IN_DST then cwr oc (d + bsm + WILDCOPY_OVERLENGTH) (zbytes l)
  else if alloc_loc streaming cap bsm n =? LOC_NOT_IN_DST then oc
  else cwr (cwr oc (d + Z.min bsm cap - n) (zbytes l))
           (d + Z.min bsm cap - n + LITBUFFEREXTRASIZE - WILDCOPY_OVERLENGTH)
           (zbytes (sublist 0 (n - LITBUFFEREXTRASIZE) l)).

Definition lit_lxb2 (streaming cap bsm n: Z) (lxb l: list Z) : list Z :=
  if alloc_loc streaming cap bsm n =? LOC_IN_DST then lxb
  else if alloc_loc streaming cap bsm n =? LOC_NOT_IN_DST then l ++ sublist n LITEXTRA_N lxb
  else sublist (n - LITBUFFEREXTRASIZE) n l ++ sublist LITBUFFEREXTRASIZE LITEXTRA_N lxb.

Local Open Scope logic.

(* ---------- the state after the Huffman call (the join of its four variants) ---------- *)

(* where the Huffman call writes the n literals in the output array (in_dst, split) *)
Definition lit_hd (streaming cap bsm n d: Z) : Z :=
  if alloc_loc streaming cap bsm n =? LOC_IN_DST then d + bsm + WILDCOPY_OVERLENGTH else d + Z.min bsm cap - n.

(* the Huffman part after the call (e: litEncType, r: its result, ht: the table on success, xt: its type) *)
Definition lit_hpart (gv: globals) (p: val) (ox: option ddx) (e r: Z) (ht: huf_table) (xt: bool) : mpred :=
  if is_error_code r then huf_junk p
  else if e =? 2 then
    field_at_ Ews t_dctx (DOT _HUFptr) p * field_at_ Ews t_dctx (DOT _litEntropy) p * hufdt_x_at xt Ews ht (ctx_huf p)
  else tabs_huf gv p ox (Some ht) xt.

(* the facts after the call: the output array oc1 (from oc) and litExtraBuffer ex1 (from lxb); on success the n
   literals l at the litBuffer; the model's literals and table when it decodes cb (old model: lit_model, exact
   model: lit_xfacts) *)
Definition lit_hfacts (e: Z) (ox: option ddx) (oh: option huf_table) (x2 single: bool) (cb: list Z)
    (streaming cap bsm n d: Z) (oc oc1: list val) (lxb: list Z) (ex1: list val) (r: Z) (l: list Z) (ht: huf_table)
    : Prop :=
  let hd := lit_hd streaming cap bsm n d in
  0 <= r <= Int64.max_unsigned /\ Zlength oc1 = Zlength oc /\ Zlength ex1 = LITEXTRA_N /\
  byte_cells ex1 /\ (byte_cells oc -> byte_cells oc1) /\
  (if alloc_loc streaming cap bsm n =? LOC_NOT_IN_DST then oc1 = oc
   else unchanged_outside oc oc1 hd (hd + n)) /\
  (is_error_code r = false ->
     r = n /\ bytes_ok l /\ Zlength l = n /\ huf_ok ht /\
     (if alloc_loc streaming cap bsm n =? LOC_NOT_IN_DST then sublist 0 n ex1 = zbytes l
      else sublist hd (hd + n) oc1 = zbytes l)) /\
  (e = 3 -> oh = Some ht) /\
  match lit_model e oh (negb single) cb n with
  | Some (l0, t0) => r = n /\ l = l0 /\ ht = t0
  | None => True
  end /\
  (is_error_code r = false ->
     ex1 = zbytes (if alloc_loc streaming cap bsm n =? LOC_NOT_IN_DST then l ++ sublist n LITEXTRA_N lxb else lxb)) /\
  lit_xfacts e ox oh x2 single cb n r l ht.

Fixpoint lit_drop (k: nat) (c: statement) : statement :=
  match k with O => c | S k' => match c with Ssequence _ c2 => lit_drop k' c2 | _ => Sskip end end.

Definition lit_c2 : statement := match lit_sw with LScons _ _ (LScons _ c _) => c | _ => Sskip end.
Definition lit_r2 : statement := match lit_sw with LScons _ _ (LScons _ _ r) => seq_of_labeled_statement r | _ => Sskip end.

Lemma lit_sw2 : seq_of_labeled_statement (select_switch 2 lit_sw) = Ssequence lit_c2 lit_r2.
Proof. reflexivity. Qed.

(* the locals during the Huffman part *)
Definition lit_KL (gv: globals) (p: val) (bsm streaming e: Z) (ob: val) (d cap: Z) (ib: val) (ioff: Z) (s: list Z)
    (lh n cs: Z) (single: bool) : list localdef :=
  [temp _litCSize (Vlong (Int64.repr cs)); temp _litSize (Vlong (Int64.repr n));
   temp _lhSize (Vlong (Int64.repr lh)); temp _singleStream (Vint (Int.repr (if single then 1 else 0)));
   temp _flags (Vint (Int.repr 0)); temp _expectedWriteSize (Vlong (Int64.repr (Z.min bsm cap)));
   temp _blockSizeMax (Vlong (Int64.repr bsm)); temp _litEncType (Vint (Int.repr e));
   temp _istart (offset_val ioff ib); gvars gv; temp _dctx p; temp _srcSize (Vlong (Int64.repr (Zlength s)));
   temp _dst (offset_val d ob); temp _dstCapacity (Vlong (Int64.repr cap)); temp _streaming (Vint (Int.repr streaming))].

(* the literal fields after ZSTD_allocateLiteralsBuffer *)
Definition lit_KF (p ob: val) (streaming cap bsm n d: Z) : list mpred :=
  [field_at Ews t_dctx (DOT _litBuffer) (fst (alloc_buf p ob streaming cap bsm n d (Z.min bsm cap) 0)) p;
   field_at Ews t_dctx (DOT _litBufferEnd) (snd (alloc_buf p ob streaming cap bsm n d (Z.min bsm cap) 0)) p;
   field_at Ews t_dctx (DOT _litBufferLocation) (Vint (Int.repr (alloc_loc streaming cap bsm n))) p;
   field_at_ Ews t_dctx (DOT _litPtr) p; field_at_ Ews t_dctx (DOT _litSize) p].

(* the facts the prologue establishes (besides lit_hyps): the header, its checks *)
Definition lit_kfacts (oh: option huf_table) (bsm cap e: Z) (s: list Z) (lh n cs: Z) (single: bool) : Prop :=
  (e = 2 \/ e = 3) /\ Z.land (byte_at s 0) 3 = e /\ (e = 3 -> oh <> None) /\ 5 <= Zlength s /\
  lit_hdr s = (lh, n, cs, single) /\ 3 <= lh <= 5 /\ 0 <= cs < 262144 /\ (single = true -> lh = 3) /\
  n <= Z.min bsm cap /\ (single = false -> 6 <= n) /\ cs + lh <= Zlength s.

(* before the Huffman call *)
Definition lit_K (gv: globals) (p: val) (fs: fstate) (ox: option ddx) (oh: option huf_table) (x2: bool) (lxb: list Z)
    (bsm streaming: Z) (W: list ptr_witness) (o: outarr) (i: inwin) (e lh n cs: Z) (single: bool)
    : environ -> mpred :=
  PROPx [] (LOCALx (lit_KL gv p bsm streaming e (oa_base o) (oa_d o) (oa_cap o) (iw_base i) (iw_off i) (iw_s i) lh n cs single)
  (SEPx ([frame_fields p fs; zstd_globals gv; pws_pred W; cfg_lit p; tabs_huf gv p ox oh x2; dent_of dent_def gv ox;
          field_at_ Ews t_dctx (DOT _workspace) p; lit_extra_at p lxb;
          data_at (oa_sh o) (tarray tuchar (oa_N o)) (oa_c o) (oa_base o);
          data_at (iw_sh i) (tarray tuchar (iw_N i)) (iw_c i) (iw_base i)] ++
         lit_KF p (oa_base o) streaming (oa_cap o) bsm n (oa_d o)))).

(* after the Huffman call *)
Definition lit_J (gv: globals) (p: val) (fs: fstate) (ox: option ddx) (oh: option huf_table) (x2: bool) (lxb: list Z)
    (bsm streaming: Z) (W: list ptr_witness) (o: outarr) (i: inwin) (e lh n cs: Z) (single: bool)
    : environ -> mpred :=
  (EX r: Z, EX oc1: list val, EX ex1: list val, EX l: list Z, EX ht: huf_table,
  PROPx [lit_hfacts e ox oh x2 single (sublist lh (lh + cs) (iw_s i)) streaming (oa_cap o) bsm n (oa_d o) (oa_c o)
           oc1 lxb ex1 r l ht]
  (LOCALx (temp _hufSuccess (Vlong (Int64.repr r)) ::
           lit_KL gv p bsm streaming e (oa_base o) (oa_d o) (oa_cap o) (iw_base i) (iw_off i) (iw_s i) lh n cs single)
  (SEPx ([frame_fields p fs; zstd_globals gv; pws_pred W; cfg_lit p;
          lit_hpart gv p ox e r ht (lit_x2' e x2 single n (sublist lh (lh + cs) (iw_s i))); dent_of dent_def gv ox;
          field_at_ Ews t_dctx (DOT _workspace) p; field_at Ews t_dctx (DOT _litExtraBuffer) ex1 p;
          data_at (oa_sh o) (tarray tuchar (oa_N o)) oc1 (oa_base o);
          data_at (iw_sh i) (tarray tuchar (iw_N i)) (iw_c i) (iw_base i)] ++
         lit_KF p (oa_base o) streaming (oa_cap o) bsm n (oa_d o)))))%assert.

(* the Huffman call (the four variants) and the rest of the segment *)
Definition lit_huf : statement := match lit_drop 14 lit_c2 with Ssequence c _ => c | _ => Sskip end.
Definition lit_tail : statement := lit_drop 15 lit_c2.

(* ---------- the Huffman call: the tables ---------- *)

Lemma lit_hufdtx_hdr (x2: bool) (sh: share) (ht: huf_table) (q: val) :
  hufdt_x_at x2 sh ht q |-- hufhdr_at sh q.
Proof.
  unfold hufdt_x_at, hufhdr_at. Intros L res.
  match goal with H: huf_ok _ |- _ => destruct H as [Hl _] end.
  unfold HUF_TABLELOG_MAX in *.
  assert (HL2: 0 < 2 ^ L <= 4096).
  { split; [apply Z.pow_pos_nonneg; lia |]. change 4096 with (2 ^ 12). apply Z.pow_le_mono_r; lia. }
  assert (HL0: 0 <= L) by (destruct (Z_lt_le_dec L 0) as [E | E]; [rewrite Z.pow_neg_r in HL2 by lia; lia | lia]).
  Exists (Vint (Int.repr (if x2 then 1 else 0))) (Vint (Int.repr L)) res.
  rewrite prop_true_andp
    by (split; [auto | split; [exists (if x2 then 1 else 0); split; [destruct x2; lia | reflexivity] |
                               split; [exists L; split; [lia | reflexivity] | auto]]]).
  cancel.
  destruct x2.
  - Intros c2. sep_apply data_at_memory_block. simpl sizeof. rewrite Z.max_r by lia.
    rewrite <- (offset_offset_val q 4 (4 * 2 ^ L)).
    sep_apply (lit_mb_join sh (4 * 2 ^ L) (HUF_CELLBYTES - 4 * 2 ^ L) (offset_val 4 q));
      try (unfold HUF_CELLBYTES; lia).
    replace (4 * 2 ^ L + (HUF_CELLBYTES - 4 * 2 ^ L)) with HUF_CELLBYTES by lia. cancel.
  - sep_apply data_at_memory_block. simpl sizeof. rewrite Z.max_r by lia.
    rewrite <- (offset_offset_val q 4 (2 * 2 ^ L)).
    sep_apply (lit_mb_join sh (2 * 2 ^ L) (HUF_CELLBYTES - 2 * 2 ^ L) (offset_val 4 q));
      try (unfold HUF_CELLBYTES; lia).
    replace (2 * 2 ^ L + (HUF_CELLBYTES - 2 * 2 ^ L)) with HUF_CELLBYTES by lia. cancel.
Qed.

Lemma lit_hufdtx_ptr (x2: bool) (sh: share) (ht: huf_table) (q: val) :
  hufdt_x_at x2 sh ht q |-- !! isptr q.
Proof. unfold hufdt_x_at. Intros L res. entailer!. Qed.

Lemma lit_hufdtx_ok (x2: bool) (sh: share) (ht: huf_table) (q: val) :
  hufdt_x_at x2 sh ht q |-- !! huf_ok ht.
Proof. unfold hufdt_x_at. Intros L res. apply prop_right. auto. Qed.

(* set_compressed: the context's table is to be built *)
Lemma lit_tab2 (gv: globals) (p: val) (ox: option ddx) (oh: option huf_table) (x2: bool) :
  tabs_huf gv p ox oh x2 |--
  field_at_ Ews t_dctx (DOT _HUFptr) p * field_at_ Ews t_dctx (DOT _litEntropy) p * hufhdr_at Ews (ctx_huf p).
Proof.
  unfold tabs_huf. Intros hp.
  destruct oh as [ht |].
  - Intros w. destruct w; Intros.
    + sep_apply lit_hufdtx_hdr. cancel.
    + cancel.
  - Intros. cancel.
Qed.

(* set_repeat: the table HUFptr points to (the context's, of type x2, or the DDict's: then ox <> None), and the
   way back *)
Lemma lit_tab3 (gv: globals) (p: val) (ox: option ddx) (ht: huf_table) (x2: bool) :
  tabs_huf gv p ox (Some ht) x2 * dent_of dent_def gv ox |--
  EX hp: val, EX xh: bool, !! (ox = None -> xh = x2) &&
    (field_at Ews t_dctx (DOT _HUFptr) hp p * hufdt_x_at xh Ews ht hp *
     ((field_at Ews t_dctx (DOT _HUFptr) hp p * hufdt_x_at xh Ews ht hp) -*
      (tabs_huf gv p ox (Some ht) x2 * dent_of dent_def gv ox))).
Proof.
  unfold tabs_huf. Intros hp w. Exists hp.
  destruct w; Intros.
  - subst hp. Exists x2. rewrite prop_true_andp by auto. cancel.
    apply -> wand_sepcon_adjoint. Exists (ctx_huf p) true. entailer!.
  - match goal with H: ox_huf ox = Some ht |- _ => rename H into Hox end. subst hp.
    destruct ox as [x |]; [| discriminate].
    unfold ox_huf, ox_ent in Hox. simpl ox_q. unfold dent_of, dent_def.
    destruct (ddx_ent x) as [st |] eqn:Est; [| discriminate].
    rewrite Hox. destruct (st_seq st) as [[[a b] c] |]; [| rewrite sepcon_FF; apply FF_left].
    Intros. unfold hufdt_at. Intros xh. Exists xh. rewrite prop_true_andp by discriminate.
    cancel. apply -> wand_sepcon_adjoint. Exists (dd_huf (dx_q x)) xh false.
    unfold ox_huf, ox_ent. rewrite Est, Hox. simpl ox_q. entailer!.
Qed.

(* HUFptr points to a table when there is one (the prefetch reads and casts it) *)
Lemma lit_hp_some (gv: globals) (p: val) (ox: option ddx) (ht: huf_table) (x2: bool) (hp: val) :
  (EX w: bool, if w then !! (hp = ctx_huf p) && hufdt_x_at x2 Ews ht (ctx_huf p)
               else !! (ox_huf ox = Some ht /\ hp = dd_huf (ox_q ox)) && hufhdr_at Ews (ctx_huf p)) *
  dent_of dent_def gv ox |-- !! is_pointer_or_null hp.
Proof.
  Intros w. destruct w; Intros.
  - subst hp. unfold hufdt_x_at. Intros L res.
    assert_PROP (isptr (ctx_huf p)) as Hq by entailer!.
    apply prop_right. destruct (ctx_huf p); try contradiction; exact I.
  - match goal with H: ox_huf ox = Some ht |- _ => rename H into Hox end. subst hp.
    destruct ox as [x |]; [| discriminate].
    unfold ox_huf, ox_ent in Hox. simpl ox_q. unfold dent_of, dent_def.
    destruct (ddx_ent x) as [st |] eqn:Est; [| discriminate].
    rewrite Hox. destruct (st_seq st) as [[[a b] c] |]; [| rewrite sepcon_FF; apply FF_left].
    Intros. unfold hufdt_at, hufdt_x_at. Intros x2' L res.
    assert_PROP (isptr (dd_huf (dx_q x))) as Hq by entailer!.
    apply prop_right. destruct (dd_huf (dx_q x)); try contradiction; exact I.
Qed.

Lemma lit_hp_frame (gv: globals) (p: val) (ox: option ddx) (ht: huf_table) (x2: bool) (hp: val) :
  (EX w: bool, if w then !! (hp = ctx_huf p) && hufdt_x_at x2 Ews ht (ctx_huf p)
               else !! (ox_huf ox = Some ht /\ hp = dd_huf (ox_q ox)) && hufhdr_at Ews (ctx_huf p)) *
  dent_of dent_def gv ox * TT |-- !! is_pointer_or_null hp.
Proof.
  apply derives_trans with (!! is_pointer_or_null hp * TT).
  - apply sepcon_derives; [apply lit_hp_some | apply derives_refl].
  - rewrite prop_sepcon. apply derives_extract_prop; intros Hq; apply prop_right; exact Hq.
Qed.

Lemma lit_wk (p: val) :
  field_at_ Ews t_dctx (DOT _workspace) p = data_at_ Ews (tarray tuint 640) (field_address t_dctx (DOT _workspace) p).
Proof. unfold field_at_. rewrite field_at_data_at. reflexivity. Qed.

Lemma lit_syms_bytes (t: huf_table) (V: list Z) (k: nat) (pos: Z) (l: list Z) (q: Z) :
  huf_ok t -> huf_decode_syms t V k pos = Some (l, q) -> bytes_ok l.
Proof.
  intros Ht. revert pos l q. induction k as [| k IH]; intros pos l q H; simpl in H.
  - inversion H; subst. constructor.
  - destruct (nth _ (huf_cells t) (0, 0)) as [sy nb] eqn:En.
    destruct (pos - nb <? 0); [discriminate |].
    destruct (huf_decode_syms t V k (pos - nb)) as [[l' q'] |] eqn:E; [| discriminate].
    inversion H; subst. constructor; [| eapply IH; eauto].
    destruct Ht as (_ & _ & Hc). unfold is_byte.
    destruct (lt_dec (Z.to_nat (bs_peek_s V pos (ht_log t))) (length (huf_cells t))) as [Hl | Hl].
    + pose proof (proj1 (Forall_nth _ _) Hc _ (0, 0) Hl) as Hn. rewrite En in Hn. simpl in Hn. lia.
    + rewrite nth_overflow in En by lia. inversion En. lia.
Qed.

Lemma lit_stream_bytes (t: huf_table) (s: list Z) (k: Z) (l: list Z) :
  huf_ok t -> huf_decode_stream t s k = Some l -> bytes_ok l.
Proof.
  intros Ht H. unfold huf_decode_stream in H.
  destruct (negb (bs_okb s)); [discriminate |].
  destruct (huf_decode_syms t s (Z.to_nat k) (bs_total s)) as [[l' q] |] eqn:E; [| discriminate].
  destruct q; try discriminate. inversion H; subst. eapply lit_syms_bytes; eauto.
Qed.

Lemma lit_with_bytes (four: bool) (t: huf_table) (cb: list Z) (n: Z) (l: list Z) :
  huf_ok t -> huf_lits_with four t cb n = Some l -> bytes_ok l.
Proof.
  intros Ht H. unfold huf_lits_with in H. destruct four; [| eapply lit_stream_bytes; eauto].
  unfold huf_decode_4streams in H.
  destruct (Z.of_nat (length cb) <? 10); [discriminate |].
  destruct (_ <? 1); [discriminate |].
  destruct (_ <? 0); [discriminate |].
  repeat match type of H with context [huf_decode_stream ?a ?b ?c] =>
    let E := fresh "E" in destruct (huf_decode_stream a b c) eqn:E end; inversion H; subst.
  repeat match goal with E: huf_decode_stream _ _ _ = Some _ |- _ => apply lit_stream_bytes in E; [| exact Ht] end.
  unfold bytes_ok in *. rewrite !Forall_app. auto.
Qed.

Lemma lit_lits_bytes (four: bool) (cb: list Z) (n: Z) (t: huf_table) (l: list Z) :
  huf_ok t -> huf_lits four cb n = Some (t, l) -> bytes_ok l.
Proof.
  intros Ht H. unfold huf_lits in H.
  destruct (huf_parse_desc cb) as [[t0 h] |]; [| discriminate].
  destruct (h >=? Zlength cb); [discriminate |].
  change (if four then huf_decode_4streams t0 (skipn (Z.to_nat h) cb) n
          else huf_decode_stream t0 (skipn (Z.to_nat h) cb) n)
    with (huf_lits_with four t0 (skipn (Z.to_nat h) cb) n) in H.
  destruct (huf_lits_with four t0 _ n) as [l0 |] eqn:E; [| discriminate].
  inversion H; subst. eapply lit_with_bytes; eauto.
Qed.

(* the facts after the call, for a destination dc at dd *)
Definition lit_gfacts (e: Z) (ox: option ddx) (oh: option huf_table) (x2 single: bool) (cb: list Z) (n dd: Z)
    (dc dc1: list val) (r: Z) (l: list Z) (ht: huf_table) : Prop :=
  0 <= r <= Int64.max_unsigned /\ out_after dc dc1 dd n /\ (byte_cells dc -> byte_cells dc1) /\
  (is_error_code r = false ->
     r = n /\ bytes_ok l /\ Zlength l = n /\ huf_ok ht /\ sublist dd (dd + n) dc1 = zbytes l) /\
  (e = 3 -> oh = Some ht) /\
  match lit_model e oh (negb single) cb n with
  | Some (l0, t0) => r = n /\ l = l0 /\ ht = t0
  | None => True
  end /\
  lit_xfacts e ox oh x2 single cb n r l ht.

Lemma lit_small_ok (n: Z) : 0 <= n <= 131072 -> is_error_code n = false.
Proof. intros H. unfold is_error_code. apply Z.ltb_ge. lia. Qed.

Lemma lit_out_len (dc dc1: list val) (dd n: Z) (l: list Z) :
  out_after dc dc1 dd n -> 0 <= dd -> 0 <= n -> dd + n <= Zlength dc ->
  sublist dd (dd + n) dc1 = zbytes l -> Zlength l = n.
Proof.
  intros [Hl _] H0 Hn Hd E. apply (f_equal (@Zlength val)) in E.
  rewrite Zlength_map, Zlength_sublist in E by lia. lia.
Qed.

(* set_repeat: the facts from huf_using_spec's post (xh: the type of the table used, the context's x2 when there
   is no DDict) *)
Lemma lit_gf3 (ox: option ddx) (oh: option huf_table) (x2 xh single: bool) (ht: huf_table) (cb: list Z) (n dd: Z)
    (dc dc1: list val) (r: Z) :
  0 <= dd -> 0 <= n <= 131072 -> dd + n <= Zlength dc -> huf_ok ht -> oh = Some ht -> (ox = None -> xh = x2) ->
  0 <= r <= Int64.max_unsigned -> out_after dc dc1 dd n -> (byte_cells dc -> byte_cells dc1) ->
  match huf_lits_with (negb single) ht cb n with
  | Some l => r = n /\ sublist dd (dd + n) dc1 = zbytes l
  | None => True
  end ->
  match x_huf_decode (xhuf_of xh ht) single cb n with
  | None => is_error_code r = true
  | Some l => r = n /\ sublist dd (dd + n) dc1 = zbytes l
  end ->
  exists l, lit_gfacts 3 ox oh x2 single cb n dd dc dc1 r l ht.
Proof.
  intros Hd Hn Hdn Ht Hoh Hxh Hr Ho Hbc Hm Hx.
  unfold lit_gfacts, lit_model, lit_xfacts, lit_x2'. cbn [Z.eqb Pos.eqb]. rewrite Hoh. cbn [option_map].
  destruct (x_huf_decode (xhuf_of xh ht) single cb n) as [l0 |] eqn:XD.
  - destruct Hx as [Hr0 Hsub]. exists l0.
    assert (Hb0: bytes_ok l0) by (eapply xl_dec_bytes; eauto).
    split; [exact Hr |]. split; [exact Ho |]. split; [exact Hbc |].
    split; [intros _; split; [exact Hr0 |]; split; [exact Hb0 |];
            split; [eapply lit_out_len; eauto; lia |]; split; [exact Ht | exact Hsub] |].
    split; [intros _; reflexivity |].
    split.
    + destruct (huf_lits_with (negb single) ht cb n) as [l1 |] eqn:E; [| exact I].
      destruct Hm as [_ Hsub1]. split; [exact Hr0 |]. split; [| reflexivity].
      apply lit_zbytes_inj; [exact Hb0 | eapply lit_with_bytes; eauto | congruence].
    + intros Hox. rewrite (xl_huf3 (xhuf_of x2 ht)). rewrite <- (Hxh Hox), XD. auto.
  - exists nil.
    split; [exact Hr |]. split; [exact Ho |]. split; [exact Hbc |].
    split; [intros Er; rewrite Hx in Er; discriminate |].
    split; [intros _; reflexivity |].
    split.
    + destruct (huf_lits_with (negb single) ht cb n) as [l1 |] eqn:E; [| exact I].
      destruct Hm as [Hr0 _]. subst r. rewrite lit_small_ok in Hx by lia. discriminate.
    + intros Hox. rewrite (xl_huf3 (xhuf_of x2 ht)). rewrite <- (Hxh Hox), XD. exact Hx.
Qed.

(* set_compressed, success: the table ht of huf_built (the exact clause's error case is `false = true` once
   is_error_code r = false is substituted) *)
Lemma lit_gf2 (ox: option ddx) (oh: option huf_table) (x2 single: bool) (ht: huf_table) (cb: list Z) (n dd: Z)
    (dc dc1: list val) (r: Z) :
  0 <= dd -> 0 <= n <= 131072 -> dd + n <= Zlength dc -> huf_ok ht -> is_error_code r = false ->
  (single = false -> 6 <= n) ->
  0 <= r <= Int64.max_unsigned -> out_after dc dc1 dd n -> (byte_cells dc -> byte_cells dc1) ->
  match huf_lits (negb single) cb n with
  | Some (t, l) => r = n /\ sublist dd (dd + n) dc1 = zbytes l
  | None => True
  end ->
  match option_map fst (huf_lits (negb single) cb n) with Some t => ht = t | None => True end ->
  match xh_dctx (huf_dctx_x2 (negb single) n cb) (negb (negb single)) cb n with
  | None => false = true
  | Some (l, _) => r = n /\ sublist dd (dd + n) dc1 = zbytes l
  end ->
  (exists h, x_readstats cb = Some (ht, h)) ->
  exists l, lit_gfacts 2 ox oh x2 single cb n dd dc dc1 r l ht.
Proof.
  intros Hd Hn Hdn Ht Er Hs6 Hr Ho Hbc Hm Hh Hx [h HR].
  unfold lit_gfacts, lit_model, lit_xfacts, lit_x2'. cbn [Z.eqb Pos.eqb].
  rewrite (xl_huf2 (option_map (xhuf_of x2) oh) single cb n Hs6).
  destruct (xh_dctx (huf_dctx_x2 (negb single) n cb) (negb (negb single)) cb n) as [[l0 t0] |] eqn:XD;
    [| discriminate Hx].
  destruct Hx as [Hr0 Hsub]. exists l0.
  assert (Hb0: bytes_ok l0) by (eapply lit_dctx_bytes; eauto).
  split; [exact Hr |]. split; [exact Ho |]. split; [exact Hbc |].
  split; [intros _; split; [exact Hr0 |]; split; [exact Hb0 |];
          split; [eapply lit_out_len; eauto; lia |]; split; [exact Ht | exact Hsub] |].
  split; [discriminate |].
  split.
  - destruct (huf_lits (negb single) cb n) as [[t1 l1] |] eqn:E; [| exact I].
    destruct Hm as [_ Hsub1]. simpl in Hh. subst t1. split; [exact Hr0 |]. split; [| reflexivity].
    apply lit_zbytes_inj; [exact Hb0 | eapply lit_lits_bytes; eauto | congruence].
  - intros _. split; [exact Hr0 |]. split; [reflexivity |]. eapply xl_dctx_tab; eauto.
Qed.

(* set_compressed, error *)
Lemma lit_gf2e (ox: option ddx) (oh: option huf_table) (x2 single: bool) (ht: huf_table) (cb: list Z) (n dd: Z)
    (dc dc1: list val) (r: Z) :
  0 <= n <= 131072 -> is_error_code r = true -> (single = false -> 6 <= n) ->
  0 <= r <= Int64.max_unsigned -> out_after dc dc1 dd n -> (byte_cells dc -> byte_cells dc1) ->
  match huf_lits (negb single) cb n with
  | Some (t, l) => r = n /\ sublist dd (dd + n) dc1 = zbytes l
  | None => True
  end ->
  match xh_dctx (huf_dctx_x2 (negb single) n cb) (negb (negb single)) cb n with
  | None => is_error_code r = true
  | Some (l, _) => r = n /\ sublist dd (dd + n) dc1 = zbytes l
  end ->
  lit_gfacts 2 ox oh x2 single cb n dd dc dc1 r nil ht.
Proof.
  intros Hn Er Hs6 Hr Ho Hbc Hm Hx.
  unfold lit_gfacts, lit_model, lit_xfacts. cbn [Z.eqb Pos.eqb].
  split; [exact Hr |]. split; [exact Ho |]. split; [exact Hbc |]. split; [rewrite Er; discriminate |].
  split; [discriminate |].
  split.
  - destruct (huf_lits (negb single) cb n) as [[t0 l0] |] eqn:E; [| exact I].
    destruct Hm as [Hr0 _]. subst r. rewrite lit_small_ok in Er by lia. discriminate.
  - intros _. rewrite (xl_huf2 (option_map (xhuf_of x2) oh) single cb n Hs6).
    destruct (xh_dctx _ _ cb n) as [[l0 t0] |]; [| exact Er].
    destruct Hx as [Hr0 _]. subst r. rewrite lit_small_ok in Er by lia. discriminate.
Qed.

Lemma lit_ctx_huf_eq (p: val) :
  field_compatible t_dctx (DOT _litBuffer) p -> ctx_huf p = offset_val 10296 p.
Proof.
  intros H. unfold ctx_huf. rewrite field_address_offset; [reflexivity |].
  apply field_compatible_cons. split; [apply compute_in_members_true_iff; reflexivity |].
  apply (lit_fc _litBuffer); [exact H | apply compute_in_members_true_iff; reflexivity].
Qed.

Lemma lit_wk_eq (p: val) :
  field_compatible t_dctx (DOT _litBuffer) p -> field_address t_dctx (DOT _workspace) p = offset_val 27324 p.
Proof.
  intros H. rewrite field_address_offset; [reflexivity |].
  apply (lit_fc _litBuffer); [exact H | apply compute_in_members_true_iff; reflexivity].
Qed.
