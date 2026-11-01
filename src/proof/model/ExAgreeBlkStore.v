(* The literals' placement and stores (ExBlock.x_lits_store, ZSTD_allocateLiteralsBuffer and the stores of
   ZSTD_decodeLiteralsBlock) of a block decoded one-shot (no dictionary, not streaming) after the frame's output
   out establish the sequence loop's invariant ex_inv, when the block's content (|lits| + M) fits the expected
   write size MIN(bsm, room).  Plain Coq. *)
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Import ListNotations.
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Bitstream Zstd.proof.model.BitsFast Zstd.proof.model.Fse.
Require Import Zstd.proof.model.NCount Zstd.proof.model.Huffman Zstd.proof.model.Block.
Require Import Zstd.proof.model.ExHuf Zstd.proof.model.ExCSeq Zstd.proof.model.ExBlock.
Require Import Zstd.proof.model.ExAgreeDefs Zstd.proof.model.ExAgreeBlkDefs.
Local Open Scope Z_scope.

Local Open Scope bool_scope.

(* ---------- lists ---------- *)

Lemma nth_upd_eq : forall {A} (l: list A) i x d, (i < length l)%nat -> nth i (upd l i x) d = x.
Proof.
  induction l as [|y l IH]; intros i x d H; simpl in H; [lia|].
  destruct i; simpl; [reflexivity|]. apply IH. lia.
Qed.

Lemma nth_upd_neq : forall {A} (l: list A) i n x d, n <> i -> nth n (upd l i x) d = nth n l d.
Proof.
  induction l as [|y l IH]; intros i n x d H; simpl; [reflexivity|].
  destruct i, n; simpl; try reflexivity; [lia|]. apply IH. lia.
Qed.

Lemma length_upd : forall {A} (l: list A) i x, length (upd l i x) = length l.
Proof. induction l as [|y l IH]; intros i x; simpl; [reflexivity|]. destruct i; simpl; auto. Qed.

Lemma Zlen_nonneg : forall {A} (l: list A), 0 <= Zlength l.
Proof. intros. rewrite Zlength_correct. lia. Qed.

Lemma Zlength_upd : forall {A} (l: list A) i x, Zlength (upd l i x) = Zlength l.
Proof. intros. rewrite !Zlength_correct, length_upd. reflexivity. Qed.

Lemma byte_at_firstn : forall (l: list Z) n j, 0 <= j < Z.of_nat n -> byte_at (firstn n l) j = byte_at l j.
Proof.
  intros l n j H. unfold byte_at. rewrite nth_firstn.
  destruct (Nat.ltb_spec (Z.to_nat j) n); [reflexivity|lia].
Qed.

Lemma byte_at_skipn : forall (l: list Z) n j, 0 <= j -> byte_at (skipn n l) j = byte_at l (Z.of_nat n + j).
Proof.
  intros l n j H. unfold byte_at. rewrite nth_skipn. f_equal. lia.
Qed.

Lemma byte_at_repeat : forall v n j, 0 <= j < Z.of_nat n -> byte_at (repeat v n) j = v.
Proof. intros v n j H. unfold byte_at. apply nth_repeat_lt. lia. Qed.

(* ---------- the memory's cells after stores ---------- *)

Definition xreg_eqb (a b: xreg) : bool :=
  match a, b with R_dst, R_dst | R_lxb, R_lxb | R_src, R_src => true | _, _ => false end.

Lemma xreg_eqb_neq : forall a b, a <> b -> xreg_eqb a b = false.
Proof. intros [] [] H; simpl; congruence. Qed.

(* a cell is defined in R_lxb exactly within the buffer, in R_src within the block *)
Lemma rd_lxb : forall src m p, 0 <= p < Zlength (xm_lxb m) -> xm_rd src m R_lxb p = Some (byte_at (xm_lxb m) p).
Proof.
  intros src m p H. unfold xm_rd. destruct (Z.ltb_spec p 0); [lia|]. destruct (Z.ltb_spec p (Zlength (xm_lxb m))); [reflexivity|lia].
Qed.

Lemma rd_src : forall src m p, 0 <= p < Zlength src -> xm_rd src m R_src p = Some (byte_at src p).
Proof.
  intros src m p H. unfold xm_rd. destruct (Z.ltb_spec p 0); [lia|]. destruct (Z.ltb_spec p (Zlength src)); [reflexivity|lia].
Qed.

Lemma rd_init : forall src out lxb p, 0 <= p < Zlength out ->
  xm_rd src {| xm_dst := map Some out; xm_lxb := lxb |} R_dst p = Some (byte_at out p).
Proof.
  intros src out lxb p H. unfold xm_rd. destruct (Z.ltb_spec p 0); [lia|]. simpl.
  rewrite Zlength_correct in H.
  rewrite (nth_indep _ None (Some 0)) by (rewrite length_map; lia).
  rewrite map_nth. reflexivity.
Qed.

(* one store: the cell i of region r changes, nothing else *)
Lemma wr_rd : forall m r i v m', xm_wr m r i v = Some m' -> forall src r' p,
  xm_rd src m' r' p = if xreg_eqb r r' && (p =? i) then Some v else xm_rd src m r' p.
Proof.
  intros m r i v m' H src r' p. unfold xm_wr in H.
  destruct (Z.ltb_spec i 0) as [Hi|Hi]; [discriminate|].
  destruct r.
  - inversion H; subst; clear H.
    destruct r'; simpl; [|reflexivity|reflexivity].
    unfold xm_rd. simpl.
    destruct (Z.eqb_spec p i) as [->|Hne].
    + destruct (Z.ltb_spec i 0); [lia|].
      destruct (Z.ltb_spec i (Zlength (xm_dst m))).
      * apply nth_upd_eq. rewrite Zlength_correct in *. lia.
      * rewrite app_nth2 by (rewrite Zlength_correct in *; lia).
        rewrite app_nth2 by (rewrite repeat_length, Zlength_correct in *; lia).
        rewrite repeat_length. rewrite Zlength_correct in *.
        replace (Z.to_nat i - length (xm_dst m) - Z.to_nat (i - Z.of_nat (length (xm_dst m))))%nat with O by lia.
        reflexivity.
    + destruct (Z.ltb_spec p 0); [reflexivity|].
      destruct (Z.ltb_spec i (Zlength (xm_dst m))).
      * apply nth_upd_neq. lia.
      * rewrite Zlength_correct in *.
        destruct (Nat.ltb_spec (Z.to_nat p) (length (xm_dst m))).
        -- rewrite app_nth1 by lia. reflexivity.
        -- rewrite app_nth2 by lia. rewrite (nth_overflow (xm_dst m)) by lia.
           destruct (Nat.ltb_spec (Z.to_nat p - length (xm_dst m)) (Z.to_nat (i - Z.of_nat (length (xm_dst m))))).
           ++ rewrite app_nth1 by (rewrite repeat_length; lia). apply nth_repeat.
           ++ rewrite app_nth2 by (rewrite repeat_length; lia). rewrite repeat_length.
              destruct (Z.to_nat p - length (xm_dst m) - Z.to_nat (i - Z.of_nat (length (xm_dst m))))%nat eqn:E; [lia|].
              simpl. destruct n; reflexivity.
  - destruct (Z.ltb_spec i (Zlength (xm_lxb m))) as [Hl|Hl]; [|discriminate].
    inversion H; subst; clear H.
    destruct r'; simpl; [reflexivity| |reflexivity].
    unfold xm_rd. cbn [xm_lxb]. rewrite Zlength_upd.
    destruct (Z.eqb_spec p i) as [->|Hne].
    + destruct (Z.ltb_spec i 0); [lia|]. destruct (Z.ltb_spec i (Zlength (xm_lxb m))); [|lia].
      unfold byte_at. rewrite nth_upd_eq; [reflexivity|]. rewrite Zlength_correct in *. lia.
    + destruct (Z.ltb_spec p 0); [reflexivity|]. destruct (p <? Zlength (xm_lxb m)); [|reflexivity].
      unfold byte_at. rewrite nth_upd_neq; [reflexivity|]. lia.
  - discriminate.
Qed.

Lemma wr_lxb_len : forall m r i v m', xm_wr m r i v = Some m' -> Zlength (xm_lxb m') = Zlength (xm_lxb m).
Proof.
  intros m r i v m' H. unfold xm_wr in H. destruct (i <? 0); [discriminate|].
  destruct r; [inversion H; reflexivity| |discriminate].
  destruct (i <? Zlength (xm_lxb m)); [|discriminate]. inversion H; subst. cbn [xm_lxb].
  apply Zlength_upd.
Qed.

(* where a run of stores may go: dst at any index >= 0, litExtraBuffer within its length *)
Definition wr_ok (m: xmem) (r: xreg) (i n: Z) : Prop :=
  0 <= i /\ r <> R_src /\ (r = R_lxb -> i + n <= Zlength (xm_lxb m)).

Lemma wrn_spec : forall vs m r i, wr_ok m r i (Zlength vs) ->
  exists m', xm_wrn vs m r i = Some m' /\ Zlength (xm_lxb m') = Zlength (xm_lxb m) /\
  forall src r' p, xm_rd src m' r' p =
    if xreg_eqb r r' && ((i <=? p) && (p <? i + Zlength vs)) then Some (byte_at vs (p - i)) else xm_rd src m r' p.
Proof.
  induction vs as [|v vs IH]; intros m r i Hok.
  - exists m. split; [reflexivity|]. split; [reflexivity|]. intros src r' p.
    rewrite Zlength_nil. destruct (xreg_eqb r r'); simpl; [|reflexivity].
    destruct (Z.leb_spec i p); destruct (Z.ltb_spec p (i + 0)); simpl; try reflexivity; lia.
  - destruct Hok as [Hi [Hs Hl]]. rewrite Zlength_cons in Hl.
    assert (Hw: exists m1, xm_wr m r i v = Some m1).
    { unfold xm_wr. destruct (Z.ltb_spec i 0); [lia|].
      destruct r; [eauto| |congruence].
      destruct (Z.ltb_spec i (Zlength (xm_lxb m))); [eauto|]. specialize (Hl eq_refl). pose proof (Zlen_nonneg vs). lia. }
    destruct Hw as [m1 Hw].
    pose proof (wr_rd _ _ _ _ _ Hw) as Hr1. pose proof (wr_lxb_len _ _ _ _ _ Hw) as Hl1.
    destruct (IH m1 r (i + 1)) as [m' [Hm' [Hl' Hr']]].
    { split; [lia|]. split; [exact Hs|]. intros ->. rewrite Hl1. specialize (Hl eq_refl). lia. }
    exists m'. simpl. rewrite Hw. split; [exact Hm'|]. split; [congruence|].
    intros src r' p. rewrite Hr', Hr1. rewrite Zlength_cons.
    destruct (xreg_eqb r r'); simpl; [|reflexivity].
    destruct (Z.eqb_spec p i) as [->|Hne].
    + destruct (Z.leb_spec (i + 1) i); [lia|]. simpl.
      destruct (Z.leb_spec i i); [|lia]. destruct (Z.ltb_spec i (i + Z.succ (Zlength vs))); [|pose proof (Zlen_nonneg vs); lia].
      simpl. replace (i - i) with 0 by lia. reflexivity.
    + destruct (Z.leb_spec (i + 1) p); destruct (Z.ltb_spec p (i + 1 + Zlength vs));
      destruct (Z.leb_spec i p); destruct (Z.ltb_spec p (i + Z.succ (Zlength vs))); simpl; try lia; try reflexivity.
      unfold byte_at. replace (Z.to_nat (p - i)) with (S (Z.to_nat (p - (i + 1)))) by lia. reflexivity.
Qed.

(* reading k defined cells *)
Lemma rdn_eq : forall src l m r s, (forall j, 0 <= j < Zlength l -> xm_rd src m r (s + j) = Some (byte_at l j)) ->
  xm_rdn src (length l) m r s = Some l.
Proof.
  induction l as [|v l IH]; intros m r s H; [reflexivity|].
  simpl. rewrite (IH m r (s + 1)).
  - specialize (H 0). rewrite Z.add_0_r in H. rewrite H by (rewrite Zlength_cons; pose proof (Zlen_nonneg l); lia).
    reflexivity.
  - intros j Hj. specialize (H (j + 1)). rewrite Zlength_cons in H.
    replace (s + 1 + j) with (s + (j + 1)) by lia. rewrite H by lia.
    unfold byte_at. replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia. reflexivity.
Qed.

Lemma move_eq : forall src l m rd d rs s, (forall j, 0 <= j < Zlength l -> xm_rd src m rs (s + j) = Some (byte_at l j)) ->
  xm_move src (length l) m rd d rs s = xm_wrn l m rd d.
Proof. intros. unfold xm_move. rewrite rdn_eq by assumption. reflexivity. Qed.

(* a forward copy between two regions is the stores of the bytes it reads *)
Lemma fwd_eq : forall src l m rd d rs s, rd <> rs ->
  (forall j, 0 <= j < Zlength l -> xm_rd src m rs (s + j) = Some (byte_at l j)) ->
  xm_fwd src (length l) m rd d rs s = xm_wrn l m rd d.
Proof.
  induction l as [|v l IH]; intros m rd d rs s Hne H; [reflexivity|].
  simpl. pose proof (H 0) as H0. rewrite Z.add_0_r in H0. rewrite H0 by (rewrite Zlength_cons; pose proof (Zlen_nonneg l); lia).
  unfold byte_at at 1. simpl.
  destruct (xm_wr m rd d v) as [m1|] eqn:Hw; [|reflexivity].
  apply IH; [exact Hne|]. intros j Hj.
  rewrite (wr_rd _ _ _ _ _ Hw). rewrite xreg_eqb_neq by exact Hne. simpl.
  specialize (H (j + 1)). rewrite Zlength_cons in H.
  replace (s + 1 + j) with (s + (j + 1)) by lia. rewrite H by lia.
  unfold byte_at. replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia. reflexivity.
Qed.

(* ---------- the literals section as Block.decode_literals reads it ---------- *)

Lemma Forall_firstn' : forall {A} (P: A -> Prop) n l, Forall P l -> Forall P (firstn n l).
Proof. induction n; intros [|x l] H; simpl; auto. inversion H; subst. constructor; auto. Qed.

Lemma Forall_skipn' : forall {A} (P: A -> Prop) n l, Forall P l -> Forall P (skipn n l).
Proof. induction n; intros [|x l] H; simpl; auto. inversion H; subst. auto. Qed.

Lemma le_value_nn : forall l, Forall (fun x => 0 <= x) l -> 0 <= le_value l.
Proof. induction l as [|x l IH]; intros H; cbn [le_value]; [lia|]. inversion H; subst. specialize (IH H3). lia. Qed.

Lemma le_field_nn : forall l i k, bytes_ok l -> 0 <= le_field l i k.
Proof.
  intros l i k H. unfold le_field, slice. apply le_value_nn. apply Forall_firstn', Forall_skipn'.
  eapply Forall_impl; [|exact H]. intros x Hx. unfold is_byte in Hx. lia.
Qed.

Lemma byte_at_nn : forall l i, bytes_ok l -> 0 <= byte_at l i.
Proof.
  intros l i H. unfold byte_at. destruct (nth_in_or_default (Z.to_nat i) l 0) as [Hin|Hd]; [|rewrite Hd; lia].
  unfold bytes_ok in H. rewrite Forall_forall in H. specialize (H _ Hin). unfold is_byte in H. lia.
Qed.

Lemma Zlength_slice : forall (l: list Z) i k, 0 <= i -> 0 <= k -> i + k <= Zlength l -> Zlength (slice l i k) = k.
Proof.
  intros l i k Hi Hk H. unfold slice. rewrite Zlength_correct in *. rewrite firstn_length, skipn_length. lia.
Qed.

Lemma byte_at_slice : forall (l: list Z) i k j, 0 <= i -> 0 <= j < k -> byte_at (slice l i k) j = byte_at l (i + j).
Proof.
  intros l i k j Hi Hj. unfold slice. rewrite byte_at_firstn by lia. rewrite byte_at_skipn by lia. f_equal. lia.
Qed.

(* raw literals: the lits = Zlength lits bytes of the block before lused *)
Lemma dl_raw : forall h body bsm lits lused huf, bytes_ok body ->
  decode_literals h body bsm = Some (lits, lused, huf) -> Z.land (byte_at body 0) 3 = 0 ->
  0 <= lused - Zlength lits /\ lused <= Zlength body /\
  forall k, 0 <= k < Zlength lits -> byte_at lits k = byte_at body (lused - Zlength lits + k).
Proof.
  intros h body bsm lits lused huf Hb H Hty. unfold decode_literals in H.
  destruct (Zlength body <? 2); [discriminate|]. rewrite Hty in H. cbn [Z.eqb Pos.eqb] in H.
  pose proof (byte_at_nn body 0 Hb) as H0.
  assert (Hlh: exists lh litSize, 1 <= lh /\ 0 <= litSize /\
    (if Z.land (Z.shiftr (byte_at body 0) 2) 3 =? 1 then (2, Z.shiftr (le_field body 0 2) 4)
     else if Z.land (Z.shiftr (byte_at body 0) 2) 3 =? 3 then (3, Z.shiftr (le_field body 0 3) 4)
     else (1, Z.shiftr (byte_at body 0) 3)) = (lh, litSize)).
  { destruct (_ =? 1); [|destruct (_ =? 3)]; do 2 eexists; (split; [|split; [|reflexivity]]); try lia;
      apply Z.shiftr_nonneg; try apply le_field_nn; auto. }
  destruct Hlh as [lh [litSize [Hlh1 [Hls Heq]]]]. rewrite Heq in H.
  destruct (_ && _); [discriminate|]. destruct (litSize >? bsm); [discriminate|].
  destruct (Z.gtb_spec (lh + litSize) (Zlength body)); [discriminate|].
  inversion H; subst; clear H. rewrite Zlength_slice by lia.
  split; [lia|]. split; [lia|]. intros k Hk. rewrite byte_at_slice by lia. f_equal. lia.
Qed.

(* RLE literals: Zlength lits copies of the byte before lused *)
Lemma dl_rle : forall h body bsm lits lused huf,
  decode_literals h body bsm = Some (lits, lused, huf) -> Z.land (byte_at body 0) 3 = 1 ->
  lits = repeat (byte_at body (lused - 1)) (Z.to_nat (Zlength lits)).
Proof.
  intros h body bsm lits lused huf H Hty. unfold decode_literals in H.
  destruct (Zlength body <? 2); [discriminate|]. rewrite Hty in H. cbn [Z.eqb Pos.eqb] in H.
  destruct (if _ =? 1 then _ else _) as [lh litSize].
  destruct (_ && _); [discriminate|]. destruct (_ && _); [discriminate|]. destruct (litSize >? bsm); [discriminate|].
  inversion H; subst; clear H. rewrite Zlength_correct, repeat_length, Nat2Z.id.
  replace (lh + 1 - 1) with lh by lia. reflexivity.
Qed.

Lemma Zlength_repeat : forall {A} (v: A) k, Zlength (repeat v k) = Z.of_nat k.
Proof. intros. rewrite Zlength_correct, repeat_length. reflexivity. Qed.

(* ZSTD_allocateLiteralsBuffer's three choices, one-shot *)
Lemma alloc_cases : forall room n bsm,
  (x_alloc_loc room n bsm false = XL_in_dst /\ room > bsm + 32 + n + 32) \/
  (x_alloc_loc room n bsm false = XL_extra /\ room <= bsm + 32 + n + 32 /\ n <= 65536) \/
  (x_alloc_loc room n bsm false = XL_split /\ room <= bsm + 32 + n + 32 /\ n > 65536).
Proof.
  intros room n bsm. unfold x_alloc_loc, XWILDCOPY, XLITEXTRA. cbn [negb andb].
  destruct (Z.gtb_spec room (bsm + 32 + n + 32)); [left; split; [reflexivity|lia]|right].
  destruct (Z.leb_spec n 65536); [left; split; [reflexivity|lia] | right; split; [reflexivity|lia]].
Qed.

(* the cells of a memory after its stores, expanded store by store *)
Ltac rd_expand :=
  repeat match goal with
  | H: forall (src: list Z) (r': xreg) (p: Z), xm_rd src ?m' r' p = _ |- context [xm_rd _ ?m' _ _] => rewrite H
  end; cbn [xreg_eqb andb].

Ltac zcase :=
  repeat (match goal with
  | |- context [Z.leb ?a ?b] => destruct (Z.leb_spec a b)
  | |- context [Z.ltb ?a ?b] => destruct (Z.ltb_spec a b)
  end; cbn [andb]).

(* the literals split into their first D and their last |lits| - D *)
Lemma split_lits : forall (lits: list Z) D, 0 <= D <= Zlength lits ->
  exists Ld Lx, lits = Ld ++ Lx /\ length Ld = Z.to_nat D /\ length Lx = Z.to_nat (Zlength lits - D) /\
    Zlength Ld = D /\ Zlength Lx = Zlength lits - D /\
    (forall j, 0 <= j < D -> byte_at Ld j = byte_at lits j) /\
    (forall j, 0 <= j -> byte_at Lx j = byte_at lits (D + j)).
Proof.
  intros lits D HD. exists (firstn (Z.to_nat D) lits), (skipn (Z.to_nat D) lits).
  rewrite Zlength_correct in HD.
  split; [symmetry; apply firstn_skipn|].
  split; [rewrite firstn_length; lia|]. split; [rewrite skipn_length, Zlength_correct; lia|].
  split; [rewrite Zlength_correct, firstn_length; lia|]. split; [rewrite !Zlength_correct, skipn_length; lia|].
  split; [intros j Hj; apply byte_at_firstn; lia|].
  intros j Hj. rewrite byte_at_skipn by lia. f_equal. lia.
Qed.

(* raw literals read in place from the block *)
Lemma inplace_inv : forall e m out lits M lused n body room bsm op0,
  xe_src e = body -> xe_ps e = 0 -> xe_vs e = 0 -> op0 = Zlength out -> n = Zlength lits ->
  dst_has m 0 out -> 0 <= M -> xe_oend e = op0 + room -> n + M <= Z.min bsm room ->
  0 <= lused - n -> lused + 32 <= Zlength body ->
  (forall k, 0 <= k < n -> byte_at lits k = byte_at body (lused - n + k)) ->
  ex_inv e {| xmm := m; xop := op0; xlr := R_src; xli := lused - n; xlim := lused - n + n; xsp := false |} out lits M.
Proof.
  intros e m out lits M lused n body room bsm op0 Hsrc Hps Hvs Hop0 Hn Hd HM Hoe Hfit Hlh Hin Hbyte.
  pose proof (Zlen_nonneg lits).
  unfold ex_inv, lit_inv, XWILDCOPY, XLITEXTRA; cbn [xmm xop xlr xli xlim xsp].
  split; [exact Hps|]. split; [exact Hvs|]. split; [exact Hop0|]. split; [exact Hd|]. split; [exact HM|].
  split; [rewrite Hoe; lia|]. split; [lia|]. split.
  - intros k Hk. rewrite Hsrc, rd_src by lia. f_equal. symmetry. apply Hbyte. lia.
  - split; [lia|]. split; [|intros Hc; discriminate Hc].
    intros k Hk. rewrite Hsrc, rd_src by lia. eauto.
Qed.

Lemma x_lits_store_agree : forall (h: option huf_table) (body: list Z) (bsm room: Z) (out lits: list Z)
    (lused: Z) (huf: option huf_table) (lxb: list Z) (M: Z) (e: xenv),
  bytes_ok body -> Zlength body <= bsm -> 0 <= room ->
  decode_literals h body bsm = Some (lits, lused, huf) ->
  Zlength lxb = XLITEXTRA + XWILDCOPY -> 0 <= M -> Zlength lits + M <= Z.min bsm room ->
  xe_src e = body -> xe_ps e = 0 -> xe_vs e = 0 ->
  xe_oend e = match x_litloc body lused (Zlength lits) bsm room false with
              | XL_in_dst => Zlength out + bsm + XWILDCOPY
              | _ => Zlength out + room
              end ->
  exists m lr li lim sp,
    x_lits_store body lits lused {| xm_dst := map Some out; xm_lxb := lxb |} (Zlength out) (Z.min bsm room)
      bsm room false = Some (m, lr, li, lim, sp) /\
    ex_inv e {| xmm := m; xop := Zlength out; xlr := lr; xli := li; xlim := lim; xsp := sp |} out lits M /\
    Zlength (xm_lxb m) = XLITEXTRA + XWILDCOPY.
Proof.
  (* by cases on the section's type (raw, read in place or copied; RLE; Huffman) and on the placement
     (after the block's room, litExtraBuffer, split); every store is at or above op0, so the frame's output
     stays, and each region's cells are read off store by store (wrn_spec, fwd_eq, move_eq) *)
  intros h body bsm room out lits lused huf lxb M e Hb Hbs Hroom Hdl Hlxb HM Hfit Hsrc Hps Hvs Hoend.
  unfold x_lits_store, x_litloc in *. cbv zeta.
  pose proof (Zlen_nonneg lits) as Hn0. pose proof (Zlen_nonneg out) as Hop00.
  remember (Zlength lits) as n eqn:Hn. remember (Zlength out) as op0 eqn:Hop0.
  assert (Hnl: n = Z.of_nat (length lits)) by (rewrite Hn; apply Zlength_correct).
  set (m0 := {| xm_dst := map Some out; xm_lxb := lxb |}).
  assert (Hm0: forall src p, 0 <= p < op0 -> xm_rd src m0 R_dst p = Some (byte_at out p))
    by (intros; apply rd_init; lia).
  assert (Hty: 0 <= Z.land (byte_at body 0) 3) by (apply Z.land_nonneg; lia).
  unfold x_split_L0 in *. unfold XWILDCOPY, XLITEXTRA in *.
  assert (Hlxn: Zlength (xm_lxb m0) = 65568) by (cbn [xm_lxb m0]; lia).
  (* the type of the literals section: the booleans x_lits_store tests *)
  assert (Hcase:
    (Z.land (byte_at body 0) 3 = 0 /\ (Z.land (byte_at body 0) 3 =? 0) = true /\ (Z.land (byte_at body 0) 3 <=? 1) = true) \/
    (Z.land (byte_at body 0) 3 = 1 /\ (Z.land (byte_at body 0) 3 =? 0) = false /\ (Z.land (byte_at body 0) 3 =? 1) = true /\
       (Z.land (byte_at body 0) 3 <=? 1) = true) \/
    ((Z.land (byte_at body 0) 3 =? 0) = false /\ (Z.land (byte_at body 0) 3 =? 1) = false /\
       (Z.land (byte_at body 0) 3 <=? 1) = false)).
  { destruct (Z.eqb_spec (Z.land (byte_at body 0) 3) 0) as [E|E]; [left; split; [exact E|]; rewrite E; auto|right].
    destruct (Z.eqb_spec (Z.land (byte_at body 0) 3) 1) as [E1|E1]; [left; split; [exact E1|]; rewrite E1; auto|right].
    split; [reflexivity|]. split; [reflexivity|]. apply Z.leb_gt. lia. }
  destruct Hcase as [[Ht [E0 Es]]|[[Ht [E0 [E1 Es]]]|[E0 [E1 Es]]]].
  (* ---------- raw ---------- *)
  - destruct (dl_raw h body bsm lits lused huf Hb Hdl Ht) as [Hlh [Hlu Hbyte]].
    rewrite <- Hn in Hlh, Hbyte.
    rewrite E0 in Hoend |- *. cbn [andb] in Hoend.
    destruct (Z.leb_spec (lused + 32) (Zlength body)) as [Hin|Hin].
    + (* read in place *)
      destruct (alloc_cases room n bsm) as [[Hloc Hc]|[[Hloc Hc]|[Hloc Hc]]]; rewrite Hloc in *; cbv iota beta in *;
        try rewrite Es; cbv iota beta.
      * destruct (wrn_spec (repeat 0 32) m0 R_dst (op0 + bsm + 32 + n)) as [m1 [Ew1 [Hl1 Hr1]]].
        { unfold wr_ok. split; [lia|]. split; [discriminate|]. intros Hc'; discriminate Hc'. }
        rewrite Zlength_repeat in Hr1. change (Z.of_nat 32) with 32 in Hr1.
        rewrite Ew1. do 5 eexists. split; [reflexivity|]. split; [|rewrite Hl1; exact Hlxn].
        apply (inplace_inv e m1 out lits M lused n body room bsm op0); auto.
        unfold dst_has, reg_has. intros k Hk. rewrite Z.add_0_l. rd_expand. zcase; try lia. apply Hm0. lia.
      * do 5 eexists. split; [reflexivity|]. split; [|exact Hlxn].
        apply (inplace_inv e m0 out lits M lused n body room bsm op0); auto.
        unfold dst_has, reg_has. intros k Hk. rewrite Z.add_0_l. apply Hm0. lia.
      * destruct (wrn_spec (repeat 0 32) m0 R_dst (op0 + Z.min bsm room - 32)) as [m1 [Ew1 [Hl1 Hr1]]].
        { unfold wr_ok. split; [lia|]. split; [discriminate|]. intros Hc'; discriminate Hc'. }
        rewrite Zlength_repeat in Hr1. change (Z.of_nat 32) with 32 in Hr1.
        rewrite Ew1. do 5 eexists. split; [reflexivity|]. split; [|rewrite Hl1; exact Hlxn].
        apply (inplace_inv e m1 out lits M lused n body room bsm op0); auto.
        unfold dst_has, reg_has. intros k Hk. rewrite Z.add_0_l. rd_expand. zcase; try lia. apply Hm0. lia.
    + (* copied *)
      destruct (alloc_cases room n bsm) as [[Hloc Hc]|[[Hloc Hc]|[Hloc Hc]]]; rewrite Hloc in *; cbv iota beta in *;
        try rewrite Es; cbv iota beta; cbn [xl_is_split]; cbv iota beta.
      * destruct (wrn_spec (repeat 0 32) m0 R_dst (op0 + bsm + 32 + n)) as [m1 [Ew1 [Hl1 Hr1]]].
        { unfold wr_ok. split; [lia|]. split; [discriminate|]. intros Hc'; discriminate Hc'. }
        rewrite Zlength_repeat in Hr1. change (Z.of_nat 32) with 32 in Hr1.
        rewrite Ew1. replace (Z.to_nat n) with (length lits) by lia.
        rewrite (fwd_eq body lits m1 R_dst (op0 + bsm + 32) R_src (lused - n)).
        2: discriminate.
        2: { intros j Hj. rewrite rd_src by lia. f_equal. symmetry. apply Hbyte. lia. }
        destruct (wrn_spec lits m1 R_dst (op0 + bsm + 32)) as [m2 [Ew2 [Hl2 Hr2]]].
        { unfold wr_ok. split; [lia|]. split; [discriminate|]. intros Hc'; discriminate Hc'. }
        rewrite <- Hn in Hr2. rewrite Ew2.
        do 5 eexists. split; [reflexivity|]. split; [|rewrite Hl2, Hl1; exact Hlxn].
        unfold ex_inv, lit_inv, XWILDCOPY, XLITEXTRA; cbn [xmm xop xlr xli xlim xsp].
        split; [exact Hps|]. split; [exact Hvs|]. split; [exact Hop0|].
        split. { unfold dst_has, reg_has. intros k Hk. rewrite Z.add_0_l. rd_expand. zcase; try lia. apply Hm0. lia. }
        split; [exact HM|]. split; [rewrite Hoend; lia|]. split; [lia|].
        split. { intros k Hk. rd_expand. zcase; try lia. f_equal. f_equal. lia. }
        split; [lia|]. split; [|intros _; rewrite Hoend; lia].
        intros k Hk. rd_expand. zcase; try lia. eexists; reflexivity.
      * replace (Z.to_nat n) with (length lits) by lia.
        rewrite (fwd_eq body lits m0 R_lxb 0 R_src (lused - n)).
        2: discriminate.
        2: { intros j Hj. rewrite rd_src by lia. f_equal. symmetry. apply Hbyte. lia. }
        destruct (wrn_spec lits m0 R_lxb 0) as [m1 [Ew1 [Hl1 Hr1]]].
        { unfold wr_ok. split; [lia|]. split; [discriminate|]. intros _. lia. }
        rewrite <- Hn in Hr1. rewrite Ew1.
        do 5 eexists. split; [reflexivity|]. split; [|rewrite Hl1; exact Hlxn].
        unfold ex_inv, lit_inv, XWILDCOPY, XLITEXTRA; cbn [xmm xop xlr xli xlim xsp].
        split; [exact Hps|]. split; [exact Hvs|]. split; [exact Hop0|].
        split. { unfold dst_has, reg_has. intros k Hk. rewrite Z.add_0_l. rd_expand. apply Hm0. lia. }
        split; [exact HM|]. split; [rewrite Hoend; lia|]. split; [lia|].
        split. { intros k Hk. rd_expand. zcase; try lia. f_equal. f_equal. lia. }
        split; [lia|]. split; [|intros Hc'; discriminate Hc'].
        intros k Hk. rd_expand. zcase; try lia. eexists. apply rd_lxb. lia.
      * destruct (wrn_spec (repeat 0 32) m0 R_dst (op0 + Z.min bsm room - 32)) as [m1 [Ew1 [Hl1 Hr1]]].
        { unfold wr_ok. split; [lia|]. split; [discriminate|]. intros Hc'; discriminate Hc'. }
        rewrite Zlength_repeat in Hr1. change (Z.of_nat 32) with 32 in Hr1.
        rewrite Ew1.
        destruct (split_lits lits (n - 65536)) as [Ld [Lx [Happ [HLd [HLx [HLdz [HLxz [HLdb HLxb]]]]]]]]; [lia|].
        rewrite <- Hn in HLx, HLxz.
        replace (Z.to_nat (n - 65536)) with (length Ld) by lia.
        rewrite (fwd_eq body Ld m1 R_dst (op0 + (Z.min bsm room - n + 65536 - 32)) R_src (lused - n)).
        2: discriminate.
        2: { intros j Hj. rewrite rd_src by lia. f_equal. rewrite HLdb by lia. symmetry. apply Hbyte. lia. }
        destruct (wrn_spec Ld m1 R_dst (op0 + (Z.min bsm room - n + 65536 - 32))) as [m2 [Ew2 [Hl2 Hr2]]].
        { unfold wr_ok. split; [lia|]. split; [discriminate|]. intros Hc'; discriminate Hc'. }
        rewrite Ew2.
        replace (Z.to_nat 65536) with (length Lx) by lia.
        rewrite (fwd_eq body Lx m2 R_lxb 0 R_src (lused - n + (n - 65536))).
        2: discriminate.
        2: { intros j Hj. rewrite rd_src by lia. f_equal. rewrite HLxb by lia. rewrite Hbyte by lia. f_equal. lia. }
        destruct (wrn_spec Lx m2 R_lxb 0) as [m3 [Ew3 [Hl3 Hr3]]].
        { unfold wr_ok. split; [lia|]. split; [discriminate|]. intros _. rewrite Hl2, Hl1. lia. }
        rewrite Ew3.
        do 5 eexists. split; [reflexivity|]. split; [|rewrite Hl3, Hl2, Hl1; exact Hlxn].
        unfold ex_inv, lit_inv, XWILDCOPY, XLITEXTRA; cbn [xmm xop xlr xli xlim xsp].
        split; [exact Hps|]. split; [exact Hvs|]. split; [exact Hop0|].
        split. { unfold dst_has, reg_has. intros k Hk. rewrite Z.add_0_l. rd_expand. zcase; try lia. apply Hm0. lia. }
        split; [exact HM|]. split; [rewrite Hoend; lia|].
        exists Ld, Lx. split; [exact Happ|]. split; [lia|].
        split. { unfold dst_has, reg_has. intros k Hk. rd_expand. zcase; try lia. f_equal. f_equal. lia. }
        split; [lia|].
        split. { intros k Hk. rd_expand. zcase; try lia. eexists; reflexivity. }
        split. { intros k Hk. rd_expand. zcase; try lia. f_equal. f_equal. lia. }
        split; [rewrite Hl3, Hl2, Hl1; exact Hlxn|]. lia.
  (* ---------- RLE ---------- *)
  - assert (Hlv: forall k, 0 <= k < n -> byte_at lits k = byte_at body (lused - 1)).
    { intros k Hk. rewrite (dl_rle h body bsm lits lused huf Hdl Ht). apply byte_at_repeat. lia. }
    assert (Hrl: repeat (byte_at body (lused - 1)) (Z.to_nat n) = lits).
    { rewrite Hn. symmetry. exact (dl_rle h body bsm lits lused huf Hdl Ht). }
    rewrite E0 in Hoend |- *. cbn [andb] in Hoend. rewrite E1.
    destruct (alloc_cases room n bsm) as [[Hloc Hc]|[[Hloc Hc]|[Hloc Hc]]]; rewrite Hloc in *; cbv iota beta in *;
      try rewrite Es; cbv iota beta; cbn [xl_is_split]; cbv iota beta.
    + destruct (wrn_spec (repeat 0 32) m0 R_dst (op0 + bsm + 32 + n)) as [m1 [Ew1 [Hl1 Hr1]]].
      { unfold wr_ok. split; [lia|]. split; [discriminate|]. intros Hc'; discriminate Hc'. }
      rewrite Zlength_repeat in Hr1. change (Z.of_nat 32) with 32 in Hr1.
      rewrite Ew1, Hrl.
      destruct (wrn_spec lits m1 R_dst (op0 + bsm + 32)) as [m2 [Ew2 [Hl2 Hr2]]].
      { unfold wr_ok. split; [lia|]. split; [discriminate|]. intros Hc'; discriminate Hc'. }
      rewrite <- Hn in Hr2. rewrite Ew2.
      do 5 eexists. split; [reflexivity|]. split; [|rewrite Hl2, Hl1; exact Hlxn].
      unfold ex_inv, lit_inv, XWILDCOPY, XLITEXTRA; cbn [xmm xop xlr xli xlim xsp].
      split; [exact Hps|]. split; [exact Hvs|]. split; [exact Hop0|].
      split. { unfold dst_has, reg_has. intros k Hk. rewrite Z.add_0_l. rd_expand. zcase; try lia. apply Hm0. lia. }
      split; [exact HM|]. split; [rewrite Hoend; lia|]. split; [lia|].
      split. { intros k Hk. rd_expand. zcase; try lia. f_equal. f_equal. lia. }
      split; [lia|]. split; [|intros _; rewrite Hoend; lia].
      intros k Hk. rd_expand. zcase; try lia. eexists; reflexivity.
    + rewrite Hrl.
      destruct (wrn_spec lits m0 R_lxb 0) as [m1 [Ew1 [Hl1 Hr1]]].
      { unfold wr_ok. split; [lia|]. split; [discriminate|]. intros _. lia. }
      rewrite <- Hn in Hr1. rewrite Ew1.
      do 5 eexists. split; [reflexivity|]. split; [|rewrite Hl1; exact Hlxn].
      unfold ex_inv, lit_inv, XWILDCOPY, XLITEXTRA; cbn [xmm xop xlr xli xlim xsp].
      split; [exact Hps|]. split; [exact Hvs|]. split; [exact Hop0|].
      split. { unfold dst_has, reg_has. intros k Hk. rewrite Z.add_0_l. rd_expand. apply Hm0. lia. }
      split; [exact HM|]. split; [rewrite Hoend; lia|]. split; [lia|].
      split. { intros k Hk. rd_expand. zcase; try lia. f_equal. f_equal. lia. }
      split; [lia|]. split; [|intros Hc'; discriminate Hc'].
      intros k Hk. rd_expand. zcase; try lia. eexists. apply rd_lxb. lia.
    + destruct (wrn_spec (repeat 0 32) m0 R_dst (op0 + Z.min bsm room - 32)) as [m1 [Ew1 [Hl1 Hr1]]].
      { unfold wr_ok. split; [lia|]. split; [discriminate|]. intros Hc'; discriminate Hc'. }
      rewrite Zlength_repeat in Hr1. change (Z.of_nat 32) with 32 in Hr1.
      rewrite Ew1.
      destruct (split_lits lits (n - 65536)) as [Ld [Lx [Happ [HLd [HLx [HLdz [HLxz [HLdb HLxb]]]]]]]]; [lia|].
      rewrite <- Hn in HLx, HLxz.
      destruct (wrn_spec (repeat (byte_at body (lused - 1)) (Z.to_nat (n - 65536))) m1 R_dst
                  (op0 + (Z.min bsm room - n + 65536 - 32))) as [m2 [Ew2 [Hl2 Hr2]]].
      { unfold wr_ok. split; [lia|]. split; [discriminate|]. intros Hc'; discriminate Hc'. }
      rewrite Zlength_repeat, Z2Nat.id in Hr2 by lia.
      rewrite Ew2.
      destruct (wrn_spec (repeat (byte_at body (lused - 1)) (Z.to_nat 65536)) m2 R_lxb 0) as [m3 [Ew3 [Hl3 Hr3]]].
      { unfold wr_ok. split; [lia|]. split; [discriminate|]. intros _. rewrite Hl2, Hl1, Zlength_repeat. lia. }
      rewrite Zlength_repeat, Z2Nat.id in Hr3 by lia.
      rewrite Ew3.
      do 5 eexists. split; [reflexivity|]. split; [|rewrite Hl3, Hl2, Hl1; exact Hlxn].
      unfold ex_inv, lit_inv, XWILDCOPY, XLITEXTRA; cbn [xmm xop xlr xli xlim xsp].
      split; [exact Hps|]. split; [exact Hvs|]. split; [exact Hop0|].
      split. { unfold dst_has, reg_has. intros k Hk. rewrite Z.add_0_l. rd_expand. zcase; try lia. apply Hm0. lia. }
      split; [exact HM|]. split; [rewrite Hoend; lia|].
      exists Ld, Lx. split; [exact Happ|]. split; [lia|].
      split. { unfold dst_has, reg_has. intros k Hk. rd_expand. zcase; try lia.
               rewrite byte_at_repeat by lia. rewrite HLdb, Hlv by lia. reflexivity. }
      split; [lia|].
      split. { intros k Hk. rd_expand. zcase; try lia. eexists; reflexivity. }
      split. { intros k Hk. rd_expand. zcase; try lia.
               rewrite byte_at_repeat by lia. rewrite HLxb, Hlv by lia. reflexivity. }
      split; [rewrite Hl3, Hl2, Hl1; exact Hlxn|]. lia.
  (* ---------- Huffman (compressed or treeless) ---------- *)
  - rewrite E0 in Hoend |- *. cbn [andb] in Hoend. rewrite E1.
    destruct (alloc_cases room n bsm) as [[Hloc Hc]|[[Hloc Hc]|[Hloc Hc]]]; rewrite Hloc in *; cbv iota beta in *;
      try rewrite Es; cbv iota beta; cbn [xl_is_split]; cbv iota beta.
    + destruct (wrn_spec (repeat 0 32) m0 R_dst (op0 + bsm + 32 + n)) as [m1 [Ew1 [Hl1 Hr1]]].
      { unfold wr_ok. split; [lia|]. split; [discriminate|]. intros Hc'; discriminate Hc'. }
      rewrite Zlength_repeat in Hr1. change (Z.of_nat 32) with 32 in Hr1.
      rewrite Ew1.
      destruct (wrn_spec lits m1 R_dst (op0 + bsm + 32)) as [m2 [Ew2 [Hl2 Hr2]]].
      { unfold wr_ok. split; [lia|]. split; [discriminate|]. intros Hc'; discriminate Hc'. }
      rewrite <- Hn in Hr2. rewrite Ew2.
      do 5 eexists. split; [reflexivity|]. split; [|rewrite Hl2, Hl1; exact Hlxn].
      unfold ex_inv, lit_inv, XWILDCOPY, XLITEXTRA; cbn [xmm xop xlr xli xlim xsp].
      split; [exact Hps|]. split; [exact Hvs|]. split; [exact Hop0|].
      split. { unfold dst_has, reg_has. intros k Hk. rewrite Z.add_0_l. rd_expand. zcase; try lia. apply Hm0. lia. }
      split; [exact HM|]. split; [rewrite Hoend; lia|]. split; [lia|].
      split. { intros k Hk. rd_expand. zcase; try lia. f_equal. f_equal. lia. }
      split; [lia|]. split; [|intros _; rewrite Hoend; lia].
      intros k Hk. rd_expand. zcase; try lia. eexists; reflexivity.
    + destruct (wrn_spec lits m0 R_lxb 0) as [m1 [Ew1 [Hl1 Hr1]]].
      { unfold wr_ok. split; [lia|]. split; [discriminate|]. intros _. lia. }
      rewrite <- Hn in Hr1. rewrite Ew1.
      do 5 eexists. split; [reflexivity|]. split; [|rewrite Hl1; exact Hlxn].
      unfold ex_inv, lit_inv, XWILDCOPY, XLITEXTRA; cbn [xmm xop xlr xli xlim xsp].
      split; [exact Hps|]. split; [exact Hvs|]. split; [exact Hop0|].
      split. { unfold dst_has, reg_has. intros k Hk. rewrite Z.add_0_l. rd_expand. apply Hm0. lia. }
      split; [exact HM|]. split; [rewrite Hoend; lia|]. split; [lia|].
      split. { intros k Hk. rd_expand. zcase; try lia. f_equal. f_equal. lia. }
      split; [lia|]. split; [|intros Hc'; discriminate Hc'].
      intros k Hk. rd_expand. zcase; try lia. eexists. apply rd_lxb. lia.
    + destruct (split_lits lits (n - 65536)) as [Ld [Lx [Happ [HLd [HLx [HLdz [HLxz [HLdb HLxb]]]]]]]]; [lia|].
      rewrite <- Hn in HLx, HLxz.
      destruct (wrn_spec lits m0 R_dst (op0 + Z.min bsm room - n)) as [m1 [Ew1 [Hl1 Hr1]]].
      { unfold wr_ok. split; [lia|]. split; [discriminate|]. intros Hc'; discriminate Hc'. }
      rewrite <- Hn in Hr1. rewrite Ew1.
      replace (Z.to_nat 65536) with (length Lx) by lia.
      rewrite (fwd_eq body Lx m1 R_lxb 0 R_dst (op0 + Z.min bsm room - 65536)).
      2: discriminate.
      2: { intros j Hj. rd_expand. zcase; try lia. f_equal. rewrite HLxb by lia. f_equal. lia. }
      destruct (wrn_spec Lx m1 R_lxb 0) as [m2 [Ew2 [Hl2 Hr2]]].
      { unfold wr_ok. split; [lia|]. split; [discriminate|]. intros _. rewrite Hl1. lia. }
      rewrite Ew2.
      replace (Z.to_nat (n - 65536)) with (length Ld) by lia.
      rewrite (move_eq body Ld m2 R_dst (op0 + Z.min bsm room - n + 65536 - 32) R_dst (op0 + Z.min bsm room - n)).
      2: { intros j Hj. rd_expand. zcase; try lia. f_equal. rewrite HLdb by lia. f_equal. lia. }
      destruct (wrn_spec Ld m2 R_dst (op0 + Z.min bsm room - n + 65536 - 32)) as [m3 [Ew3 [Hl3 Hr3]]].
      { unfold wr_ok. split; [lia|]. split; [discriminate|]. intros Hc'; discriminate Hc'. }
      rewrite Ew3.
      do 5 eexists. split; [reflexivity|]. split; [|rewrite Hl3, Hl2, Hl1; exact Hlxn].
      unfold ex_inv, lit_inv, XWILDCOPY, XLITEXTRA; cbn [xmm xop xlr xli xlim xsp].
      split; [exact Hps|]. split; [exact Hvs|]. split; [exact Hop0|].
      split. { unfold dst_has, reg_has. intros k Hk. rewrite Z.add_0_l. rd_expand. zcase; try lia. apply Hm0. lia. }
      split; [exact HM|]. split; [rewrite Hoend; lia|].
      exists Ld, Lx. split; [exact Happ|]. split; [lia|].
      split. { unfold dst_has, reg_has. intros k Hk. rd_expand. zcase; try lia. f_equal. f_equal. lia. }
      split; [lia|].
      split. { intros k Hk. rd_expand. zcase; try lia. eexists; reflexivity. }
      split. { intros k Hk. rd_expand. zcase; try lia. f_equal. f_equal. lia. }
      split; [rewrite Hl3, Hl2, Hl1; exact Hlxn|]. lia.
Qed.
