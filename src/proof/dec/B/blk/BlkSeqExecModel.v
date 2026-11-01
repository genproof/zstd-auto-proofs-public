(* CORE of SEQ: the bytes one ZSTD_execSequence* writes, at the level of the
   C arrays (exec_c, what EXEC's specs promise), and their relation to the model's exec_seqs step
   (Block.lz_copy), which LOOP uses.

   One sequence at op = k of the output array c (prefix from ps, extDict e = DecIface.ext_seg):
   1. the ll literal values Lv go to [k, k+ll);
   2. the match of ml bytes at offset off behind x = k + ll:
      - off <= x - ps: inside the array, the forward (overlapping) copy listcopy c1 (x - off) x ml;
      - else it starts dl = off - (x - ps) bytes before the end e1 of the extDict: min(ml, dl) bytes come
        from the extDict (memmove: [e1 - dl, ..) of the extDict array, the output array itself for ExtIn),
        the rest is the forward copy from prefixStart (ps) to x + dl. *)
Require Export Zstd.proof.dec.B.blk.BlkSeqCOPY.
Require Import Coq.micromega.Lia.
Local Open Scope Z_scope.

(* the array holding the extDict (the output array for ExtNone / ExtIn), and its end *)
Definition ext_src (c: list val) (e: ext_seg) : list val :=
  match e with ExtSep _ _ _ ec _ _ => ec | _ => c end.
Definition ext_end (e: ext_seg) : Z :=
  match e with ExtNone => 0 | ExtIn e1 _ => e1 | ExtSep _ _ _ _ e1 _ => e1 end.

(* replace [i, i + |v|) of c by v *)
Definition put (c: list val) (i: Z) (v: list val) : list val :=
  sublist 0 i c ++ v ++ sublist (i + Zlength v) (Zlength c) c.

Definition exec_c (c: list val) (k: Z) (Lv: list val) (ml off ps: Z) (e: ext_seg) : list val :=
  let x := k + Zlength Lv in
  let c1 := put c k Lv in
  if off <=? x - ps then listcopy c1 (x - off) x (Z.to_nat ml)
  else
    let dl := off - (x - ps) in
    let l1 := Z.min ml dl in
    let c2 := put c1 x (sublist (ext_end e - dl) (ext_end e - dl + l1) (ext_src c1 e)) in
    listcopy c2 ps (x + l1) (Z.to_nat (ml - l1)).

(* ---------- helpers for exec_c_lz ---------- *)

Lemma ecl_Zlength_put (c: list val) (i: Z) (v: list val) :
  0 <= i -> i + Zlength v <= Zlength c -> Zlength (put c i v) = Zlength c.
Proof.
  intros H1 H2. pose proof (Zlength_nonneg v). unfold put. rewrite !Zlength_app, !Zlength_sublist; lia.
Qed.

Lemma ecl_Znth_put_in (c: list val) (i: Z) (v: list val) (p: Z) :
  0 <= i <= p -> p < i + Zlength v -> i + Zlength v <= Zlength c ->
  Znth p (put c i v) = Znth (p - i) v.
Proof.
  intros H1 H2 H3. pose proof (Zlength_nonneg v). unfold put.
  rewrite Znth_app2 by (rewrite Zlength_sublist; lia).
  rewrite Zlength_sublist by lia.
  rewrite Znth_app1 by lia. f_equal; lia.
Qed.

Lemma ecl_Znth_put_out (c: list val) (i: Z) (v: list val) (p: Z) :
  0 <= i -> i + Zlength v <= Zlength c -> 0 <= p < Zlength c -> ~ (i <= p < i + Zlength v) ->
  Znth p (put c i v) = Znth p c.
Proof.
  intros H1 H2 H3 H4. pose proof (Zlength_nonneg v). unfold put.
  destruct (Z_lt_le_dec p i).
  - rewrite Znth_app1 by (rewrite Zlength_sublist; lia).
    rewrite Znth_sublist by lia. f_equal; lia.
  - rewrite Znth_app2 by (rewrite Zlength_sublist; lia).
    rewrite Zlength_sublist by lia.
    rewrite Znth_app2 by lia.
    rewrite Znth_sublist by (try rewrite Zlength_sublist; lia). f_equal; lia.
Qed.

(* listcopy reproduces any sequence f obeying the copy recurrence f (di + j) = f (si + j), once the array
   agrees with f on [lo, di) (lo <= si < di) *)
Lemma ecl_listcopy_agree (f: Z -> val) (a: list val) (si di lo: Z) (n: nat) :
  0 <= lo <= si -> si < di -> di + Z.of_nat n <= Zlength a ->
  (forall p, lo <= p < di -> Znth p a = f p) ->
  (forall j, 0 <= j < Z.of_nat n -> f (di + j) = f (si + j)) ->
  forall p, lo <= p < di + Z.of_nat n -> Znth p (listcopy a si di n) = f p.
Proof.
  revert a si di. induction n as [|m IH]; intros a si di Hlo Hsd Hn Ha Hf p Hp.
  - simpl. apply Ha. lia.
  - simpl. rewrite Nat2Z.inj_succ in *.
    assert (Hu: Zlength (upd_Znth di a (Znth si a)) = Zlength a) by apply Zlength_upd_Znth.
    apply IH; try lia.
    + intros q Hq. destruct (Z.eq_dec q di) as [->|Hne].
      * rewrite upd_Znth_same by lia. rewrite Ha by lia.
        specialize (Hf 0 ltac:(lia)). rewrite !Z.add_0_r in Hf. auto.
      * rewrite upd_Znth_diff by lia. apply Ha. lia.
    + intros j Hj. specialize (Hf (j + 1) ltac:(lia)).
      replace (di + 1 + j) with (di + (j + 1)) by lia.
      replace (si + 1 + j) with (si + (j + 1)) by lia. auto.
Qed.

Lemma ecl_byte_at_Znth (l: list Z) (i: Z) : 0 <= i -> byte_at l i = Znth i l.
Proof.
  intros H. unfold byte_at, Znth. destruct (Z_lt_dec i 0); [lia|]. reflexivity.
Qed.

Lemma ecl_byte_at_app_l (P Q: list Z) (i: Z) :
  0 <= i < Zlength P -> byte_at (P ++ Q) i = byte_at P i.
Proof.
  intros H. unfold byte_at. rewrite app_nth1; [reflexivity|].
  rewrite Zlength_correct in H. lia.
Qed.

Lemma ecl_byte_at_app_r (P Q: list Z) (i: Z) :
  0 <= i -> byte_at (P ++ Q) (Zlength P + i) = byte_at Q i.
Proof.
  intros H. unfold byte_at. rewrite app_nth2; rewrite Zlength_correct.
  - f_equal. lia.
  - lia.
Qed.

(* the copy recurrence of the model: a byte lz_copy produces equals the byte off before it *)
Lemma ecl_lz_rec (hist O: list Z) (off: Z) (ml: nat) (j: Z) :
  1 <= off <= Zlength hist + Zlength O -> 0 <= j < Z.of_nat ml ->
  byte_at (hist ++ lz_copy hist O off ml) (Zlength hist + Zlength O + j) =
  byte_at (hist ++ lz_copy hist O off ml) (Zlength hist + Zlength O + j - off).
Proof.
  intros Hoff Hj. pose proof (Zlength_nonneg O). pose proof (Zlength_nonneg hist).
  rewrite <- Z.add_assoc, ecl_byte_at_app_r by lia.
  pose proof (lz_copy_nth hist O off ml (Z.to_nat j) ltac:(lia)) as Hn.
  rewrite Z2Nat.id in Hn by lia. rewrite Hn.
  replace ml with (Z.to_nat j + (ml - Z.to_nat j))%nat by lia.
  rewrite lz_copy_add.
  destruct (lz_copy_app hist (lz_copy hist O off (Z.to_nat j)) off (ml - Z.to_nat j)) as [tl [Htl _]].
  rewrite Htl, app_assoc, (ecl_byte_at_app_l (hist ++ lz_copy hist O off (Z.to_nat j)) tl); [f_equal; lia|].
  rewrite Zlength_app, lz_copy_length, Z2Nat.id by lia. lia.
Qed.

Lemma ecl_skipn_app (A: Type) (P Q: list A) : skipn (length P) (P ++ Q) = Q.
Proof. induction P; simpl; auto. Qed.

(* exec_c_lz with 0 <= ext_len e (layout_ok), without which the offset check can fail *)
Lemma exec_c_lz_gen (c: list val) (d k ps B: Z) (e: ext_seg) (hist out blk L: list Z) (wsize ml off: Z) :
  0 <= ps <= d -> k = d + Zlength blk -> 0 <= ml -> k + Zlength L + ml <= B -> B <= Zlength c ->
  bytes_ok L -> sublist d k c = zbytes blk ->
  hist_view c d ps e hist out wsize ->
  (match e with
   | ExtNone => True
   | ExtIn e1 elen =>
       e1 <= Zlength c /\ 0 <= e1 - elen /\
       (forall k', d - ps < k' <= Z.min (Zlength (hist ++ out)) (wsize + Zlength hist) ->
          e1 - (k' - (d - ps)) >= B)
   | ExtSep _ _ en ec e1 elen => Zlength ec = en /\ e1 <= en /\ 0 <= e1 - elen
   end) ->
  0 <= ext_len e ->
  1 <= off -> off <= Zlength hist + Zlength (out ++ blk ++ L) -> off <= wsize + Zlength hist ->
  off <= k + Zlength L - ps + ext_len e /\
  sublist k (k + Zlength L + ml) (exec_c c k (zbytes L) ml off ps e) =
    zbytes (skipn (length (out ++ blk)) (lz_copy hist (out ++ blk ++ L) off (Z.to_nat ml))).
Proof.
  intros Hps Hk Hml HB HBc HL Hblk Hhv Hext Hel Hoff1 Hoff2 Hoff3.
  subst k.
  pose proof (Zlength_nonneg hist) as Hh0. pose proof (Zlength_nonneg out) as Ho0.
  pose proof (Zlength_nonneg blk) as Hb0. pose proof (Zlength_nonneg L) as HL0.
  set (O := out ++ blk ++ L) in *.
  assert (HO: Zlength O = Zlength out + Zlength blk + Zlength L) by (unfold O; rewrite !Zlength_app; lia).
  assert (Hho: Zlength (hist ++ out) = Zlength hist + Zlength out) by (rewrite Zlength_app; lia).
  destruct (lz_copy_app hist O off (Z.to_nat ml)) as [tl [Htl Htll]].
  assert (Htl0: Zlength tl = ml) by (rewrite Zlength_correct, Htll; lia).
  set (M := hist ++ lz_copy hist O off (Z.to_nat ml)).
  set (N0 := Zlength hist + Zlength out - d).
  set (f := fun p => Vint (Int.repr (byte_at M (p + N0)))).
  set (x := d + Zlength blk + Zlength L).
  set (W := Z.min (Zlength (hist ++ out)) (wsize + Zlength hist)).
  assert (HW: off - (x - d) <= W).
  { unfold W. apply Z.min_glb; unfold x in *; lia. }
  assert (HW0: 0 <= W) by (unfold x in *; lia).
  (* the model's bytes *)
  assert (HMeq: M = (hist ++ out) ++ (blk ++ (L ++ tl))).
  { unfold M. rewrite Htl. unfold O. rewrite <- !app_assoc. reflexivity. }
  assert (HM_ho: forall i, 0 <= i < Zlength (hist ++ out) -> byte_at M i = byte_at (hist ++ out) i).
  { intros i Hi. rewrite HMeq, ecl_byte_at_app_l by lia. reflexivity. }
  assert (HM_blk: forall i, 0 <= i < Zlength blk ->
            byte_at M (Zlength hist + Zlength out + i) = Znth i blk).
  { intros i Hi. rewrite HMeq, <- Hho, ecl_byte_at_app_r, ecl_byte_at_app_l, ecl_byte_at_Znth by lia.
    reflexivity. }
  assert (HM_tl: forall i, 0 <= i ->
            byte_at M (Zlength hist + Zlength out + Zlength blk + i) = Znth i (L ++ tl)).
  { intros i Hi. rewrite HMeq, <- Hho, <- Z.add_assoc, ecl_byte_at_app_r by lia.
    rewrite ecl_byte_at_app_r, ecl_byte_at_Znth by lia. reflexivity. }
  assert (Hrec: forall j, 0 <= j < ml -> f (x + j) = f (x - off + j)).
  { intros j Hj. unfold f. do 2 f_equal.
    pose proof (ecl_lz_rec hist O off (Z.to_nat ml) j ltac:(lia) ltac:(lia)) as R.
    fold M in R.
    replace (x + j + N0) with (Zlength hist + Zlength O + j) by (unfold x, N0; lia).
    replace (x - off + j + N0) with (Zlength hist + Zlength O + j - off) by (unfold x, N0; lia).
    exact R. }
  (* the array before the sequence *)
  assert (Hc_hist: forall p, ps <= p < d -> d - p <= W -> Znth p c = f p).
  { intros p Hp HpW. destruct (Hhv (d - p) ltac:(fold W; lia)) as [_ Hch].
    unfold chist in Hch.
    destruct (d - p <=? d - ps) eqn:E; [|apply Z.leb_gt in E; lia].
    replace (d - (d - p)) with p in Hch by lia. rewrite Hch. unfold f. do 2 f_equal.
    rewrite HM_ho by (unfold W in *; lia). f_equal. unfold N0. lia. }
  assert (Hc_blk: forall p, d <= p < d + Zlength blk -> Znth p c = f p).
  { intros p Hp.
    assert (E: Znth (p - d) (sublist d (d + Zlength blk) c) = Znth p c).
    { rewrite Znth_sublist by lia. f_equal. lia. }
    rewrite <- E, Hblk, Znth_map by lia. unfold f. do 2 f_equal.
    replace (p + N0) with (Zlength hist + Zlength out + (p - d)) by (unfold N0; lia).
    rewrite HM_blk by lia. reflexivity. }
  set (c1 := put c (d + Zlength blk) (zbytes L)).
  assert (Hzl: Zlength (zbytes L) = Zlength L) by apply Zlength_map.
  assert (Hc1l: Zlength c1 = Zlength c) by (unfold c1; apply ecl_Zlength_put; unfold x in *; lia).
  assert (Hc1: forall p, ps <= p < x -> d - p <= W -> Znth p c1 = f p).
  { intros p Hp HpW. destruct (Z_lt_le_dec p (d + Zlength blk)).
    - unfold c1. rewrite ecl_Znth_put_out by (unfold x in *; lia).
      destruct (Z_lt_le_dec p d); [apply Hc_hist | apply Hc_blk]; lia.
    - unfold c1. rewrite ecl_Znth_put_in by (unfold x in *; lia).
      rewrite Znth_map by (unfold x in *; lia). unfold f. do 2 f_equal.
      replace (p + N0) with (Zlength hist + Zlength out + Zlength blk + (p - (d + Zlength blk)))
        by (unfold N0; lia).
      rewrite HM_tl by lia. rewrite Znth_app1 by (unfold x in *; lia). reflexivity. }
  (* the final step: the written range is the model's *)
  assert (Hfin: forall fin, Zlength fin = Zlength c ->
            (forall p, d + Zlength blk <= p < x + ml -> Znth p fin = f p) ->
            sublist (d + Zlength blk) (d + Zlength blk + Zlength L + ml) fin = zbytes (L ++ tl)).
  { intros fin Hfl Hfp. apply Znth_eq_ext.
    - rewrite Zlength_sublist, Zlength_map, Zlength_app by (unfold x in *; lia). lia.
    - intros i Hi. rewrite Zlength_sublist in Hi by (unfold x in *; lia).
      rewrite Znth_sublist by lia. rewrite Hfp by (unfold x; lia).
      rewrite Znth_map by (rewrite Zlength_app; lia). unfold f. do 2 f_equal.
      replace (i + (d + Zlength blk) + N0) with (Zlength hist + Zlength out + Zlength blk + i)
        by (unfold N0; lia).
      apply HM_tl. lia. }
  assert (Hrhs: skipn (length (out ++ blk)) (lz_copy hist O off (Z.to_nat ml)) = L ++ tl).
  { rewrite Htl. unfold O. replace ((out ++ blk ++ L) ++ tl) with ((out ++ blk) ++ (L ++ tl))
      by (rewrite <- !app_assoc; reflexivity). apply ecl_skipn_app. }
  rewrite Hrhs.
  unfold exec_c. cbv zeta. rewrite Hzl. fold c1. fold x.
  destruct (off <=? x - ps) eqn:Hc.
  - (* the match lies in the array *)
    apply Z.leb_le in Hc. split; [lia|].
    apply Hfin.
    + rewrite listcopy_Zlength; [lia | unfold x in *; lia | rewrite Z2Nat.id; lia].
    + intros p Hp. destruct (Z_lt_le_dec p x).
      * rewrite listcopy_outside by (rewrite ?Z2Nat.id; unfold x in *; lia).
        apply Hc1; lia.
      * apply (ecl_listcopy_agree f c1 (x - off) x (x - off)); try (rewrite ?Z2Nat.id; lia).
        -- intros q Hq. apply Hc1; lia.
        -- intros j Hj. rewrite Z2Nat.id in Hj by lia. apply Hrec. lia.
  - (* the match starts in the extDict *)
    apply Z.leb_gt in Hc.
    set (k0 := off - (x - d)).
    destruct (Hhv k0 ltac:(fold W; unfold k0; lia)) as [Hk0 _].
    split; [unfold k0 in Hk0; unfold x in *; lia|].
    set (dl := off - (x - ps)).
    set (l1 := Z.min ml dl).
    assert (Hdl: dl <= ext_len e) by (unfold dl, k0 in *; lia).
    assert (Hl1: 0 <= l1 <= ml /\ l1 <= dl) by (unfold l1, dl; lia).
    assert (Hes: 0 <= ext_end e - dl /\ ext_end e <= Zlength (ext_src c1 e)).
    { destruct e as [|e1 elen|sh eb en ec e1 elen]; simpl in *.
      - lia.
      - lia.
      - lia. }
    assert (Hext_byte: forall j, 0 <= j < l1 -> Znth (ext_end e - dl + j) (ext_src c1 e) = f (x + j)).
    { intros j Hj.
      destruct (Hhv (k0 - j) ltac:(fold W; unfold k0, dl in *; lia)) as [_ Hch].
      assert (Hv: f (x + j) = Vint (Int.repr (byte_at (hist ++ out) (Zlength (hist ++ out) - (k0 - j))))).
      { rewrite Hrec by lia. unfold f. do 2 f_equal.
        rewrite <- HM_ho by (unfold k0, dl in *; lia). f_equal. unfold k0, N0. lia. }
      rewrite Hv, <- Hch. unfold chist.
      destruct (k0 - j <=? d - ps) eqn:E; [apply Z.leb_le in E; unfold k0, dl in *; lia|].
      replace (k0 - j - (d - ps)) with (dl - j) by (unfold k0, dl; lia).
      destruct e as [|e1 elen|sh eb en ec e1 elen]; simpl in *.
      - lia.
      - destruct Hext as (He1 & Hel1 & Hfar).
        specialize (Hfar (k0 - j) ltac:(fold W; unfold k0, dl in *; lia)).
        replace (k0 - j - (d - ps)) with (dl - j) in Hfar by (unfold k0, dl; lia).
        unfold c1. rewrite ecl_Znth_put_out by (unfold x in *; lia). f_equal. lia.
      - f_equal. lia. }
    set (S := sublist (ext_end e - dl) (ext_end e - dl + l1) (ext_src c1 e)).
    assert (HS: Zlength S = l1) by (unfold S; rewrite Zlength_sublist; lia).
    set (c2 := put c1 x S).
    assert (Hc2l: Zlength c2 = Zlength c) by (unfold c2; rewrite ecl_Zlength_put; unfold x in *; lia).
    assert (Hc2: forall p, ps <= p < x + l1 -> Znth p c2 = f p).
    { intros p Hp. unfold c2. destruct (Z_lt_le_dec p x).
      - rewrite ecl_Znth_put_out by (unfold x in *; lia). apply Hc1; [lia|]. unfold k0 in HW; lia.
      - rewrite ecl_Znth_put_in by (unfold x in *; lia). unfold S.
        rewrite Znth_sublist by lia.
        replace (p - x + (ext_end e - dl)) with (ext_end e - dl + (p - x)) by lia.
        rewrite Hext_byte by lia. f_equal. lia. }
    apply Hfin.
    + rewrite listcopy_Zlength; [lia | unfold x in *; lia | rewrite Z2Nat.id; lia].
    + intros p Hp. destruct (Z_lt_le_dec p (x + l1)).
      * rewrite listcopy_outside by (rewrite ?Z2Nat.id; unfold x in *; lia).
        apply Hc2; unfold x in *; lia.
      * assert (El1: l1 = dl) by (unfold l1 in *; lia).
        apply (ecl_listcopy_agree f c2 ps (x + l1) ps); try (rewrite ?Z2Nat.id; unfold dl in *; lia).
        -- intros q Hq. apply Hc2; lia.
        -- intros j Hj. rewrite Z2Nat.id in Hj by lia.
           replace (x + l1 + j) with (x + (l1 + j)) by lia. rewrite Hrec by lia.
           f_equal. unfold dl in *; lia.
Qed.

(* One exec_seqs step, seen in the arrays.  The output array c holds, at the block start d, the history
   the model sees (hist_view: dictionary content hist, frame output out) and the block's bytes so far blk
   in [d, k); the literals L go next.  When the model accepts the offset (Block.exec_seqs: off <= |hist| +
   |out ++ blk ++ L| and off <= wsize + |hist|), the C does not reject it (off <= x - ps + elen) and
   writes exactly the model's bytes, as long as what it reads of an extDict in the output array (ExtIn)
   lies beyond B, the end of what this sequence writes. *)
Lemma exec_c_lz (c: list val) (d k ps B: Z) (e: ext_seg) (hist out blk L: list Z) (wsize ml off: Z) :
  0 <= ps <= d -> k = d + Zlength blk -> 0 <= ml -> k + Zlength L + ml <= B -> B <= Zlength c ->
  bytes_ok L -> sublist d k c = zbytes blk ->
  hist_view c d ps e hist out wsize ->
  (match e with
   | ExtNone => True
   | ExtIn e1 elen =>
       e1 <= Zlength c /\ 0 <= e1 - elen /\
       (forall k', d - ps < k' <= Z.min (Zlength (hist ++ out)) (wsize + Zlength hist) ->
          e1 - (k' - (d - ps)) >= B)
   | ExtSep _ _ en ec e1 elen => Zlength ec = en /\ e1 <= en /\ 0 <= e1 - elen
   end) ->
  0 <= ext_len e ->
  1 <= off -> off <= Zlength hist + Zlength (out ++ blk ++ L) -> off <= wsize + Zlength hist ->
  off <= k + Zlength L - ps + ext_len e /\
  sublist k (k + Zlength L + ml) (exec_c c k (zbytes L) ml off ps e) =
    zbytes (skipn (length (out ++ blk)) (lz_copy hist (out ++ blk ++ L) off (Z.to_nat ml))).
Proof.
  exact (exec_c_lz_gen c d k ps B e hist out blk L wsize ml off).
Qed.
