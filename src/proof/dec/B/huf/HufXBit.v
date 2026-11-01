(* The bridge between the BIT_DStream_t state of zstd/Spec_bits.v and the bit container of the exact
   Huffman model (model/ExHuf.v), for the exact specifications of the Huffman decoders (the HufX1D and HufX2D files).

   Spec_bits describes a reader of the stream bytes s by (pos, lo): bitContainer = bit_C s lo,
   bitsConsumed = lo + 64 - pos, ptr = start + lo / 8, or &zeroFilled once BIT_reloadDStream has seen an
   overflow (pos < lo).  ExHuf's xbit keeps the container, bitsConsumed and ptr themselves (ptr None =
   &zeroFilled).  xb_rel s pos lo d: d is that state.  Each BIT operation the decoders use moves both
   descriptions alike (xb_init_eq, xb_look_rel, xb_skip_rel, xb_reload_rel, xb_reload_fast_of,
   xb_end_rel), so the decoders' bodies can follow ExHuf's functions step by step.

   The decoders use Spec_bits.v's BIT_lookBitsFast_spec, whose last PROP is the value the C computes on every
   state (also outside the container: HUF_decodeLastSymbolX2 at bitsConsumed = 64 emits a byte from it). *)
Require Export Zstd.proof.dec.B.huf.HufGroups.
Require Export Zstd.proof.model.ExHuf.
Require Import Zstd.proof.zstd.body_bits_init Zstd.proof.zstd.body_bits_reload.
Local Open Scope logic.

Local Open Scope Z_scope.

(* ---------- the two descriptions of a reader ---------- *)

(* the state (pos, lo) with ptr at the window *)
Definition xb_of (s: list Z) (pos lo: Z) : xbit :=
  {| xb_c := bit_C s lo; xb_bc := lo + 64 - pos; xb_ptr := Some (lo / 8) |}.

(* d is the C state of the reader (pos, lo): ptr at the window, or &zeroFilled after an overflow *)
Definition xb_rel (s: list Z) (pos lo: Z) (d: xbit) : Prop :=
  xb_c d = bit_C s lo /\ xb_bc d = lo + 64 - pos /\
  (xb_ptr d = Some (lo / 8) \/ (pos < lo /\ xb_ptr d = None)).

Lemma xb_rel_of (s: list Z) (pos lo: Z) : xb_rel s pos lo (xb_of s pos lo).
Proof. unfold xb_rel, xb_of. simpl. auto. Qed.

(* with ptr at the window, the state is xb_of *)
Lemma xb_rel_some (s: list Z) (pos lo: Z) (d: xbit) :
  xb_rel s pos lo d -> xb_ptr d <> None -> d = xb_of s pos lo.
Proof.
  intros (Hc & Hb & [Hp | [_ Hp]]) Hn; [|contradiction].
  destruct d as [c b p]. unfold xb_of. simpl in *. subst. reflexivity.
Qed.

(* ---------- the operations ---------- *)

(* MEM_readLEST at start + k, inside the stream: the container of the window 8 k *)
Lemma xb_rd64_bitC (s: list Z) (k: Z) :
  bytes_ok s -> 0 <= k -> k + 8 <= Zlength s -> xb_rd64 s k = bit_C s (8 * k).
Proof.
  intros Hs Hk _. rewrite br_bit_C_field by (auto; try lia; rewrite Z.mul_comm, Z_mod_mult; reflexivity).
  rewrite (Z.mul_comm 8 k), Z.div_mul by lia. reflexivity.
Qed.

(* BIT_initDStream *)
Lemma xb_init_eq (s: list Z) :
  bytes_ok s ->
  xb_init s = if bs_wf s then Some (xb_of s (bs_total s) (8 * Z.max 0 (Zlength s - 8))) else None.
Proof.
  intros Hs. unfold xb_init. set (n := Zlength s).
  destruct (n <? 1) eqn:E1.
  { apply Z.ltb_lt in E1. destruct s; [reflexivity|]. unfold n in E1. rewrite Zlength_cons in E1.
    pose proof (Zlength_nonneg s). lia. }
  apply Z.ltb_ge in E1.
  assert (Hb: byte_at s (n - 1) = Znth (n - 1) s).
  { unfold byte_at, Znth. rewrite if_false by lia. reflexivity. }
  rewrite Hb, (bi_bs_wf s E1). fold n.
  destruct (Znth (n - 1) s =? 0) eqn:E2; [reflexivity|]. cbn [negb].
  rewrite (bi_bs_total s E1). fold n. unfold xb_of.
  destruct (8 <=? n) eqn:E3.
  - apply Z.leb_le in E3. rewrite Z.max_r by lia.
    rewrite xb_rd64_bitC by (auto; lia).
    replace (8 * (n - 8) / 8) with (n - 8) by (rewrite Z.mul_comm, Z.div_mul; lia).
    do 2 f_equal. lia.
  - apply Z.leb_gt in E3. rewrite Z.max_l by lia. rewrite Z.mul_0_r.
    rewrite bi_bitC_small by (auto; lia). do 2 f_equal. lia.
Qed.

(* BIT_lookBitsFast: the value of xb_look_fast *)
Lemma xb_look_rel (s: list Z) (pos lo: Z) (d: xbit) (nb: Z) :
  xb_rel s pos lo d -> 1 <= nb <= 64 ->
  xb_look_fast d nb = Z.shiftr ((Z.shiftl (bit_C s lo) ((lo + 64 - pos) mod 64)) mod 2 ^ 64) (64 - nb).
Proof.
  intros (Hc & Hb & _) Hnb. unfold xb_look_fast. rewrite Hc, Hb.
  destruct (Z.eq_dec nb 64) as [->|Hne]; [reflexivity|].
  rewrite (Z.mod_small (64 - nb)) by lia. reflexivity.
Qed.

(* BIT_skipBits, when bitsConsumed does not wrap *)
Lemma xb_skip_rel (s: list Z) (pos lo: Z) (d: xbit) (nb: Z) :
  xb_rel s pos lo d -> 0 <= nb -> 0 <= lo + 64 - (pos - nb) <= Int.max_unsigned ->
  xb_rel s (pos - nb) lo (xb_skip d nb).
Proof.
  intros (Hc & Hb & Hp) Hnb Hr. unfold xb_rel, xb_skip. cbn [xb_c xb_bc xb_ptr].
  rewrite Hb, Z.mod_small by (unfold Int.max_unsigned in Hr; simpl in Hr; lia).
  split; [exact Hc|]. split; [lia|]. destruct Hp as [Hp | [Hlt Hp]]; [left; exact Hp | right; split; [lia | exact Hp]].
Qed.

(* the full reload BIT_reloadDStream_internal from the window lo >= 64, when bitsConsumed <= 64 *)
Lemma xb_internal_of (s: list Z) (pos lo: Z) :
  bit_inv s pos lo -> lo <= pos -> 8 <= lo / 8 ->
  xb_reload_internal s (xb_of s pos lo) (lo / 8) = (XB_unfinished, xb_of s pos (lo - 8 * ((lo + 64 - pos) / 8))).
Proof.
  intros (Hs & Hn & Hlo & Hlo8 & Hlos & Hpl & Hbc) Hle H8.
  unfold xb_reload_internal, xb_of. cbn [xb_bc xb_c xb_ptr].
  pose proof (Z.div_mod lo 8 ltac:(lia)) as Elo.
  assert (Hq: 0 <= (lo + 64 - pos) / 8 <= 8).
  { split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]. }
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  rewrite Z.max_r in Hlos by lia.
  rewrite xb_rd64_bitC by (auto; lia).
  assert (E1: 8 * (lo / 8 - (lo + 64 - pos) / 8) = lo - 8 * ((lo + 64 - pos) / 8)) by lia.
  assert (E2: (lo - 8 * ((lo + 64 - pos) / 8)) / 8 = lo / 8 - (lo + 64 - pos) / 8).
  { rewrite <- E1, Z.mul_comm, Z.div_mul; lia. }
  assert (E3: Z.land (lo + 64 - pos) 7 = lo - 8 * ((lo + 64 - pos) / 8) + 64 - pos).
  { change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
    pose proof (Z.div_mod (lo + 64 - pos) 8 ltac:(lia)). lia. }
  rewrite E1, E2, E3. reflexivity.
Qed.

(* BIT_reloadDStream *)
Lemma xb_reload_rel (s: list Z) (pos lo: Z) (d: xbit) :
  bit_inv s pos lo -> xb_rel s pos lo d ->
  fst (xb_reload s d) = fst (bs_reload pos lo) /\
  xb_rel s pos (snd (bs_reload pos lo)) (snd (xb_reload s d)).
Proof.
  intros Hinv Hr. pose proof Hinv as (Hs & Hn & Hlo & Hlo8 & Hlos & Hpl & Hbc).
  pose proof Hr as (Hc & Hb & Hp).
  unfold xb_reload, bs_reload. rewrite Hb.
  destruct (64 <? lo + 64 - pos) eqn:E1.
  { apply Z.ltb_lt in E1. rewrite (proj2 (Z.ltb_lt pos lo)) by lia. cbn [fst snd].
    split; [reflexivity|]. unfold xb_rel. cbn [xb_c xb_bc xb_ptr]. split; [exact Hc|]. split; [reflexivity|].
    right. split; [lia | reflexivity]. }
  apply Z.ltb_ge in E1. rewrite (proj2 (Z.ltb_ge pos lo)) by lia.
  destruct Hp as [Hp | [Hlt _]]; [|lia]. rewrite Hp.
  assert (Hd: d = xb_of s pos lo) by (apply (xb_rel_some s pos lo d Hr); rewrite Hp; discriminate).
  destruct (8 <=? lo / 8) eqn:E2.
  { apply Z.leb_le in E2. rewrite Hd, xb_internal_of by (auto; lia). simpl. split; [reflexivity | apply xb_rel_of]. }
  apply Z.leb_gt in E2.
  pose proof (Z.div_mod lo 8 ltac:(lia)) as Elo.
  destruct (lo / 8 =? 0) eqn:E3.
  { apply Z.eqb_eq in E3. assert (lo = 0) by lia. subst lo. cbn [fst snd]. split; [|exact Hr].
    unfold XB_endOfBuffer, XB_completed, BIT_endOfBuffer, BIT_completed.
    destruct (0 + 64 - pos <? 64) eqn:E4, (0 <? pos) eqn:E5; try reflexivity;
      apply Z.ltb_lt in E4 || apply Z.ltb_ge in E4; apply Z.ltb_lt in E5 || apply Z.ltb_ge in E5; lia. }
  apply Z.eqb_neq in E3.
  assert (Hq: 0 <= (lo + 64 - pos) / 8 <= 8).
  { split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]. }
  assert (Hk: lo / 8 + 8 <= Zlength s).
  { destruct (Z.max_spec 0 (Zlength s - 8)) as [[_ M] | [_ M]]; rewrite M in Hlos; lia. }
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  destruct (lo / 8 <? (lo + 64 - pos) / 8) eqn:E4; cbn [fst snd].
  - split; [reflexivity|]. unfold xb_rel. cbn [xb_c xb_bc xb_ptr].
    rewrite Z.sub_diag, xb_rd64_bitC by (auto; lia). rewrite Z.mul_0_r.
    split; [reflexivity|]. split; [lia|]. left. reflexivity.
  - split; [reflexivity|]. unfold xb_rel. cbn [xb_c xb_bc xb_ptr].
    apply Z.ltb_ge in E4.
    rewrite xb_rd64_bitC by (auto; lia).
    assert (E5: (lo - 8 * ((lo + 64 - pos) / 8)) / 8 = lo / 8 - (lo + 64 - pos) / 8).
    { replace (lo - 8 * ((lo + 64 - pos) / 8)) with ((lo / 8 - (lo + 64 - pos) / 8) * 8) by lia.
      rewrite Z.div_mul; lia. }
    rewrite E5. split; [f_equal; lia|]. split; [lia|]. left. reflexivity.
Qed.

(* BIT_reloadDStreamFast, on the window-pointer state of the 4-stream loops (BIT_DStream_rep_np) *)
Lemma xb_reload_fast_of (s: list Z) (pos lo: Z) :
  bit_inv s pos lo -> lo <= pos \/ lo < 64 ->
  xb_reload_fast s (xb_of s pos lo) = (fst (bs_reload_fast pos lo), xb_of s pos (snd (bs_reload_fast pos lo))).
Proof.
  intros Hinv Hor. unfold xb_reload_fast, bs_reload_fast. cbn [xb_ptr xb_of].
  destruct (lo / 8 <? 8) eqn:E; [reflexivity|]. apply Z.ltb_ge in E.
  pose proof Hinv as (_ & _ & Hlo & Hlo8 & _).
  pose proof (Z.div_mod lo 8 ltac:(lia)).
  rewrite xb_internal_of by (auto; lia). reflexivity.
Qed.

(* BIT_endOfDStream *)
Lemma xb_end_rel (s: list Z) (pos lo: Z) (d: xbit) :
  bit_inv s pos lo -> xb_rel s pos lo d -> xb_end d = andb (lo =? 0) (pos =? 0).
Proof.
  intros (_ & _ & Hlo & Hlo8 & _) (_ & Hb & Hp). unfold xb_end. rewrite Hb.
  pose proof (Z.div_mod lo 8 ltac:(lia)).
  destruct Hp as [Hp | [Hlt Hp]]; rewrite Hp.
  - destruct (Z.eqb_spec (lo / 8) 0), (Z.eqb_spec lo 0); try lia; simpl; try reflexivity.
  - destruct (Z.eqb_spec lo 0); [|reflexivity]. destruct (Z.eqb_spec pos 0); [lia | reflexivity].
Qed.

(* ---------- the tables ---------- *)

(* the model's X1 cell of v is the C's cell (BRep.x1_cells) *)
Lemma xh_cells_x1_nth (ht: huf_table) (L v: Z) :
  0 <= v < 2 ^ L ->
  nth (Z.to_nat v) (xh_cells_x1 ht L) (0, 0, 0) = (fst (hsym ht L v), snd (hsym ht L v), 1).
Proof.
  intros Hv. unfold xh_cells_x1.
  assert (Hlen: (Z.to_nat v < length (seq 0 (Z.to_nat (2 ^ L))))%nat) by (rewrite length_seq; lia).
  set (f := fun n : nat => let '(s, nb) := hsym ht L (Z.of_nat n) in (s, nb, 1)).
  rewrite (nth_indep _ _ (f O)) by (rewrite length_map; exact Hlen).
  rewrite map_nth, seq_nth by (rewrite length_seq in Hlen; exact Hlen).
  unfold f. rewrite Nat.add_0_l, Z2Nat.id by lia.
  destruct (hsym ht L v); reflexivity.
Qed.

(* the model's X2 cell of v, as the fields of the C's cell (BRep.hufdt_x_at: c2 = map x2v (xh_cells_x2 ht L)) *)
Lemma xh_cells_x2_Znth (ht: huf_table) (L v: Z) :
  0 <= v < 2 ^ L ->
  Znth v (map x2v (xh_cells_x2 ht L)) = x2v (nth (Z.to_nat v) (xh_cells_x2 ht L) (0, 0, 0)).
Proof.
  intros Hv.
  assert (Hlen: Zlength (xh_cells_x2 ht L) = 2 ^ L).
  { unfold xh_cells_x2. rewrite Zlength_map, Zlength_correct, length_seq. lia. }
  rewrite Znth_map by lia. f_equal. unfold Znth. rewrite if_false by lia. reflexivity.
Qed.
