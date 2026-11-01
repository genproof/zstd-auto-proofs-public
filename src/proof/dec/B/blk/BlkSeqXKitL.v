(* The model's stores (model/ExBlock.v) on a region of cells are the C's stores on the arrays
   (BlkSeqXMem): when the model's function succeeds on a region m whose written cells are the output
   array's (BlkIface.dst_rel c rb m), the array after the C's stores (the list function of BlkSeqXMem
   that mirrors it) still holds every written cell of the model's new region.  The model reads only
   written cells (it fails otherwise), the same cells the C reads, and stores the same values at the
   same places; R_src is the block's body in the input array from bo, R_lxb litExtraBuffer's array
   (src_rel).  The hypotheses bound the stores inside the output array.  Plain Coq. *)
Require Export Zstd.proof.dec.B.blk.BlkSeqXMem.
Require Import Zstd.proof.model.ExBlock.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

(* ---------- one read, one store ---------- *)

Lemma xk_nth_upd_eq {A} (l: list A) (i: nat) (x d: A) : (i < length l)%nat -> nth i (upd l i x) d = x.
Proof.
  revert i; induction l as [|y l IH]; intros i H; simpl in H; [lia|].
  destruct i; simpl; [reflexivity|]. apply IH. lia.
Qed.

Lemma xk_nth_upd_neq {A} (l: list A) (i n: nat) (x d: A) : n <> i -> nth n (upd l i x) d = nth n l d.
Proof.
  revert i n; induction l as [|y l IH]; intros i n H; simpl; [reflexivity|].
  destruct i, n; simpl; try reflexivity; [lia|]. apply IH. lia.
Qed.

(* a store of the model in its destination region: the cell d changes, the others keep their contents
   (the region grows with never-written cells) *)
Lemma xk_wr_dst (m m': xmem) (d v: Z) :
  xm_wr m R_dst d v = Some m' ->
  0 <= d /\ xm_lxb m' = xm_lxb m /\
  forall j, 0 <= j -> nth (Z.to_nat j) (xm_dst m') None = if j =? d then Some v else nth (Z.to_nat j) (xm_dst m) None.
Proof.
  unfold xm_wr. destruct (Z.ltb_spec d 0) as [Hd|Hd]; [discriminate|].
  intros H; inversion H; subst; clear H. split; [lia|]. split; [reflexivity|].
  intros j Hj. cbn [xm_dst]. rewrite Zlength_correct.
  destruct (Z.eqb_spec j d) as [->|Hne].
  - destruct (Z.ltb_spec d (Z.of_nat (length (xm_dst m)))).
    + apply xk_nth_upd_eq. lia.
    + rewrite app_nth2 by lia. rewrite app_nth2 by (rewrite repeat_length; lia).
      rewrite repeat_length.
      replace (Z.to_nat d - length (xm_dst m) - Z.to_nat (d - Z.of_nat (length (xm_dst m))))%nat with O by lia.
      reflexivity.
  - destruct (Z.ltb_spec d (Z.of_nat (length (xm_dst m)))).
    + apply xk_nth_upd_neq. lia.
    + destruct (Nat.ltb_spec (Z.to_nat j) (length (xm_dst m))).
      * rewrite app_nth1 by lia. reflexivity.
      * rewrite app_nth2 by lia. rewrite (nth_overflow (xm_dst m)) by lia.
        destruct (Nat.ltb_spec (Z.to_nat j - length (xm_dst m)) (Z.to_nat (d - Z.of_nat (length (xm_dst m))))).
        -- rewrite app_nth1 by (rewrite repeat_length; lia). apply nth_repeat.
        -- rewrite app_nth2 by (rewrite repeat_length; lia). rewrite repeat_length.
           destruct (Z.to_nat j - length (xm_dst m) - Z.to_nat (d - Z.of_nat (length (xm_dst m))))%nat eqn:E; [lia|].
           simpl. destruct n; reflexivity.
Qed.

(* a cell of the array holding a byte is inside the array *)
Lemma xk_znth_in (c: list val) (i: Z) (z: int) : Znth i c = Vint z -> 0 <= i < Zlength c.
Proof.
  intros H. destruct (Z_le_gt_dec 0 i); [|rewrite Znth_underflow in H by lia; discriminate].
  destruct (Z_lt_ge_dec i (Zlength c)); [lia|]. rewrite Znth_overflow in H by lia. discriminate.
Qed.

(* the C's store of the same byte at the same place keeps the written cells *)
Lemma xk_store (c: list val) (rb: Z) (m m': xmem) (d v: Z) :
  xm_wr m R_dst d v = Some m' -> dst_rel c rb (xm_dst m) -> 0 <= rb -> rb + d < Zlength c ->
  0 <= d /\ xm_lxb m' = xm_lxb m /\ dst_rel (upd_Znth (rb + d) c (Vint (Int.repr v))) rb (xm_dst m').
Proof.
  intros Hw Hr Hrb Hc. destruct (xk_wr_dst _ _ _ _ Hw) as (Hd & Hl & Hn).
  split; [exact Hd|]. split; [exact Hl|].
  intros j z Hj Hz. rewrite Hn in Hz by exact Hj.
  destruct (Z.eqb_spec j d) as [->|Hne].
  - inversion Hz; subst. apply upd_Znth_same. lia.
  - pose proof (Hr j z Hj Hz) as Hc0. rewrite upd_Znth_diff' by lia. exact Hc0.
Qed.

Lemma xk_byte_at_znth (l: list Z) (i: Z) : 0 <= i -> byte_at l i = Znth i l.
Proof. intros H. unfold byte_at, Znth. destruct (Z_lt_dec i 0); [lia|]. reflexivity. Qed.

(* the model's read of a defined cell is the C's read at the same place *)
Lemma xk_read (src: list Z) (m: xmem) (rs: xreg) (s v: Z) (c ci cl: list val) (rb bo: Z) :
  xm_rd src m rs s = Some v -> dst_rel c rb (xm_dst m) -> src_rel src (xm_lxb m) ci bo cl ->
  lrd c (reg_l rs ci cl) (reg_o rs rb bo + s) = Vint (Int.repr v).
Proof.
  intros Hrd Hr (Hbo & Hci & Hsub & Hcl). unfold xm_rd in Hrd.
  destruct (Z.ltb_spec s 0) as [Hs|Hs]; [discriminate|].
  destruct rs; cbn [reg_l reg_o lrd].
  - apply Hr; assumption.
  - destruct (Z.ltb_spec s (Zlength (xm_lxb m))); [|discriminate]. inversion Hrd; subst v.
    subst cl. rewrite Z.add_0_l, Znth_map by lia. rewrite xk_byte_at_znth by lia. reflexivity.
  - destruct (Z.ltb_spec s (Zlength src)); [|discriminate]. inversion Hrd; subst v.
    replace (bo + s) with (s + bo) by lia. rewrite <- (Znth_sublist bo s (bo + Zlength src)) by lia.
    rewrite Hsub, Znth_map by lia. rewrite xk_byte_at_znth by lia. reflexivity.
Qed.

(* for a copy within the output array the other arrays play no role: any arrays will do *)
Lemma xk_src_rel_any (src lxb: list Z) : src_rel src lxb (zbytes src) 0 (zbytes lxb).
Proof.
  unfold src_rel. rewrite Zlength_map. split; [lia|]. split; [lia|]. split; [|reflexivity].
  rewrite Z.add_0_l, <- (Zlength_map _ _ (fun b : Z => Vint (Int.repr b))). apply sublist_same; reflexivity.
Qed.

(* ---------- the lengths of the arrays ---------- *)

Lemma lfwd_len (k: nat) (c: list val) (d: Z) (s: lsrc) (i: Z) : Zlength (lfwd k c d s i) = Zlength c.
Proof. revert c d i; induction k; intros; simpl; [reflexivity|]. rewrite IHk. apply Zlength_upd_Znth. Qed.

Lemma lwrn_len (vs c: list val) (d: Z) : Zlength (lwrn vs c d) = Zlength c.
Proof. revert c d; induction vs; intros; simpl; [reflexivity|]. rewrite IHvs. apply Zlength_upd_Znth. Qed.

Lemma lmove_len (k: nat) (c: list val) (d: Z) (s: lsrc) (i: Z) : Zlength (lmove k c d s i) = Zlength c.
Proof. apply lwrn_len. Qed.

Lemma lchunks16_len (k: nat) (c: list val) (d: Z) (s: lsrc) (i: Z) : Zlength (lchunks16 k c d s i) = Zlength c.
Proof. revert c d i; induction k; intros; simpl; [reflexivity|]. rewrite IHk. apply lmove_len. Qed.

Lemma lwild_len (c: list val) (d: Z) (s: lsrc) (i len: Z) (b: bool) : Zlength (lwild c d s i len b) = Zlength c.
Proof. unfold lwild. destruct (b && (d - i <? 16))%bool; [apply lfwd_len | apply lchunks16_len]. Qed.

Lemma lov8_len (c: list val) (op ip off: Z) : Zlength (fst (fst (lov8 c op ip off))) = Zlength c.
Proof. unfold lov8. destruct (off <? 8); cbn [fst]; rewrite !lfwd_len; reflexivity. Qed.

(* k bytes forward (memcpy, the one-byte loops) *)
Lemma xm_fwd_l (src: list Z) (k: nat) (m m': xmem) (d: Z) (rs: xreg) (s: Z) (c ci cl: list val) (rb bo: Z) :
  xm_fwd src k m R_dst d rs s = Some m' ->
  dst_rel c rb (xm_dst m) -> src_rel src (xm_lxb m) ci bo cl -> 0 <= rb -> rb + d + Z.of_nat k <= Zlength c ->
  xm_lxb m' = xm_lxb m /\
  dst_rel (lfwd k c (rb + d) (reg_l rs ci cl) (reg_o rs rb bo + s)) rb (xm_dst m').
Proof.
  revert m c d s. induction k as [|k IH]; intros m c d s H Hr Hs Hrb Hb.
  - cbn in H. inversion H; subst. split; [reflexivity|exact Hr].
  - cbn [xm_fwd] in H.
    destruct (xm_rd src m rs s) as [v|] eqn:Er; [|discriminate].
    destruct (xm_wr m R_dst d v) as [m1|] eqn:Ew; [|discriminate].
    pose proof (xk_read _ _ _ _ _ _ _ _ _ _ Er Hr Hs) as Hv.
    destruct (xk_store c rb m m1 d v Ew Hr Hrb ltac:(lia)) as (Hd & Hl & Hr1).
    cbn [lfwd]. rewrite Hv.
    replace (rb + d + 1) with (rb + (d + 1)) by lia.
    replace (reg_o rs rb bo + s + 1) with (reg_o rs rb bo + (s + 1)) by lia.
    destruct (IH m1 _ (d + 1) (s + 1) H Hr1) as [Hl' Hr']; [rewrite Hl; exact Hs | exact Hrb | |].
    + rewrite Zlength_upd_Znth. lia.
    + split; [congruence|exact Hr'].
Qed.

(* k reads, all before the stores (the first half of a move) *)
Lemma xk_rdn (src: list Z) (k: nat) (m: xmem) (rs: xreg) (s: Z) (vs: list Z) (c ci cl: list val) (rb bo: Z) :
  xm_rdn src k m rs s = Some vs -> dst_rel c rb (xm_dst m) -> src_rel src (xm_lxb m) ci bo cl ->
  lrdn k c (reg_l rs ci cl) (reg_o rs rb bo + s) = zbytes vs /\ Zlength vs = Z.of_nat k.
Proof.
  revert s vs. induction k as [|k IH]; intros s vs H Hr Hs.
  - cbn in H. inversion H; subst. split; reflexivity.
  - cbn [xm_rdn] in H.
    destruct (xm_rd src m rs s) as [v|] eqn:Er; [|discriminate].
    destruct (xm_rdn src k m rs (s + 1)) as [vs1|] eqn:Ers; [|discriminate].
    inversion H; subst vs; clear H.
    destruct (IH (s + 1) vs1 Ers Hr Hs) as [Hl Hn].
    cbn [lrdn map]. rewrite (xk_read _ _ _ _ _ _ _ _ _ _ Er Hr Hs).
    replace (reg_o rs rb bo + s + 1) with (reg_o rs rb bo + (s + 1)) by lia. rewrite Hl.
    split; [reflexivity|]. rewrite Zlength_cons, Hn. lia.
Qed.

(* the stores of the values read (the second half of a move) *)
Lemma xk_wrn (vs: list Z) (m m': xmem) (d: Z) (c: list val) (rb: Z) :
  xm_wrn vs m R_dst d = Some m' -> dst_rel c rb (xm_dst m) -> 0 <= rb -> rb + d + Zlength vs <= Zlength c ->
  xm_lxb m' = xm_lxb m /\ dst_rel (lwrn (zbytes vs) c (rb + d)) rb (xm_dst m').
Proof.
  revert m c d. induction vs as [|v vs IH]; intros m c d H Hr Hrb Hb.
  - cbn in H. inversion H; subst. split; [reflexivity|exact Hr].
  - cbn [xm_wrn] in H. rewrite Zlength_cons in Hb.
    destruct (xm_wr m R_dst d v) as [m1|] eqn:Ew; [|discriminate].
    destruct (xk_store c rb m m1 d v Ew Hr Hrb ltac:(pose proof (Zlength_nonneg vs); lia)) as (Hd & Hl & Hr1).
    cbn [map lwrn]. replace (rb + d + 1) with (rb + (d + 1)) by lia.
    destruct (IH m1 _ (d + 1) H Hr1 Hrb) as [Hl' Hr'].
    + rewrite Zlength_upd_Znth. lia.
    + split; [congruence|exact Hr'].
Qed.

(* k bytes moved (memmove) *)
Lemma xm_move_l (src: list Z) (k: nat) (m m': xmem) (d: Z) (rs: xreg) (s: Z) (c ci cl: list val) (rb bo: Z) :
  xm_move src k m R_dst d rs s = Some m' ->
  dst_rel c rb (xm_dst m) -> src_rel src (xm_lxb m) ci bo cl -> 0 <= rb -> rb + d + Z.of_nat k <= Zlength c ->
  xm_lxb m' = xm_lxb m /\
  dst_rel (lmove k c (rb + d) (reg_l rs ci cl) (reg_o rs rb bo + s)) rb (xm_dst m').
Proof.
  intros H Hr Hs Hrb Hb. unfold xm_move in H. unfold lmove.
  destruct (xm_rdn src k m rs s) as [vs|] eqn:Ers; [|discriminate].
  destruct (xk_rdn _ _ _ _ _ _ _ _ _ _ _ Ers Hr Hs) as [Hl Hn]. rewrite Hl.
  apply (xk_wrn vs m m' d c rb H Hr Hrb). lia.
Qed.

Lemma lsafecopy_len (c: list val) (op w: Z) (s: lsrc) (ip len: Z) (b: bool) :
  Zlength (lsafecopy c op w s ip len b) = Zlength c.
Proof.
  unfold lsafecopy. destruct (len <? 8); [apply lfwd_len|].
  assert (H1: Zlength (fst (fst (if b then lov8 c op ip (op - ip) else (c, op, ip)))) = Zlength c)
    by (destruct b; [apply lov8_len|reflexivity]).
  destruct (if b then lov8 c op ip (op - ip) else (c, op, ip)) as [[c1 op1] ip1]. cbn [fst] in H1.
  destruct (w - (op + len) >=? 0); [rewrite lwild_len; exact H1|].
  destruct (w - op1 >=? 0); rewrite lfwd_len; [rewrite lwild_len|]; exact H1.
Qed.

Lemma lsdbs_len (c: list val) (op ip len: Z) : Zlength (lsdbs c op ip len) = Zlength c.
Proof.
  unfold lsdbs. cbv zeta. destruct ((len <? 8) || (op - ip >? -8)); [apply lfwd_len|].
  destruct ((len >=? 32) && (op - ip <? -16)); rewrite lfwd_len; [apply lwild_len|reflexivity].
Qed.

(* the facts a Z comparison of the model gives, as linear arithmetic *)
Ltac xk_zb E :=
  try rewrite Z.gtb_ltb in E; try rewrite Z.geb_leb in E;
  first [ apply Z.ltb_lt in E | apply Z.ltb_ge in E | apply Z.leb_le in E | apply Z.leb_gt in E ].

(* ---------- the composite copies ---------- *)

(* k ZSTD_copy16 at stride 16 *)
Lemma xk_chunks (src: list Z) (k: nat) (m m': xmem) (d: Z) (rs: xreg) (s: Z) (c ci cl: list val) (rb bo: Z) :
  xm_chunks16 src k m d rs s = Some m' ->
  dst_rel c rb (xm_dst m) -> src_rel src (xm_lxb m) ci bo cl -> 0 <= rb -> rb + d + 16 * Z.of_nat k <= Zlength c ->
  xm_lxb m' = xm_lxb m /\
  dst_rel (lchunks16 k c (rb + d) (reg_l rs ci cl) (reg_o rs rb bo + s)) rb (xm_dst m').
Proof.
  revert m c d s. induction k as [|k IH]; intros m c d s H Hr Hs Hrb Hb.
  - cbn in H. inversion H; subst. split; [reflexivity|exact Hr].
  - cbn [xm_chunks16] in H.
    destruct (xm_move src 16 m R_dst d rs s) as [m1|] eqn:E; [|discriminate].
    destruct (xm_move_l src 16 m m1 d rs s c ci cl rb bo E Hr Hs Hrb ltac:(cbn; lia)) as [Hl1 Hr1].
    cbn [lchunks16]. replace (rb + d + 16) with (rb + (d + 16)) by lia.
    replace (reg_o rs rb bo + s + 16) with (reg_o rs rb bo + (s + 16)) by lia.
    destruct (IH m1 _ (d + 16) (s + 16) H Hr1) as [Hl' Hr']; [rewrite Hl1; exact Hs | exact Hrb | |].
    + rewrite lmove_len. lia.
    + split; [congruence|exact Hr'].
Qed.

(* ZSTD_wildcopy: it stores at most max(16, len + 31) bytes from d *)
Lemma xk_wild (src: list Z) (m m': xmem) (d: Z) (rs: xreg) (s len: Z) (b: bool) (c ci cl: list val) (rb bo: Z) :
  xm_wild src m d rs s len b = Some m' ->
  dst_rel c rb (xm_dst m) -> src_rel src (xm_lxb m) ci bo cl -> 0 <= rb ->
  rb + d + Z.max 16 (len + 31) <= Zlength c -> (b = true -> rs = R_dst) ->
  xm_lxb m' = xm_lxb m /\
  dst_rel (lwild c (rb + d) (reg_l rs ci cl) (reg_o rs rb bo + s) len b) rb (xm_dst m').
Proof.
  intros H Hr Hs Hrb Hb Hsb. unfold xm_wild in H. unfold lwild.
  replace (b && (rb + d - (reg_o rs rb bo + s) <? 16)) with (b && (d - s <? 16)).
  2: { destruct b; [|reflexivity]. rewrite (Hsb eq_refl). cbn [reg_o andb].
       replace (rb + d - (rb + s)) with (d - s) by lia. reflexivity. }
  destruct (b && (d - s <? 16)).
  - apply (xm_fwd_l _ _ _ _ _ _ _ _ _ _ _ _ H Hr Hs Hrb).
    pose proof (Z.mul_div_le (len + 7) 8 ltac:(lia)). rewrite Z2Nat.id by lia. lia.
  - apply (xk_chunks _ _ _ _ _ _ _ _ _ _ _ _ H Hr Hs Hrb).
    destruct (Z.leb_spec len 16); [cbn; lia|].
    pose proof (Z.mul_div_le (len - 16 + 31) 32 ltac:(lia)).
    pose proof (Z.div_pos (len - 16 + 31) 32 ltac:(lia) ltac:(lia)). rewrite Z2Nat.id by lia. lia.
Qed.

(* the copies within the output array (source R_dst) *)
Lemma xk_fwd_dst (src: list Z) (k: nat) (m m': xmem) (d s: Z) (c: list val) (rb: Z) :
  xm_fwd src k m R_dst d R_dst s = Some m' -> dst_rel c rb (xm_dst m) -> 0 <= rb -> rb + d + Z.of_nat k <= Zlength c ->
  xm_lxb m' = xm_lxb m /\ dst_rel (lfwd k c (rb + d) LW (rb + s)) rb (xm_dst m').
Proof.
  intros H Hr Hrb Hb.
  exact (xm_fwd_l src k m m' d R_dst s c (zbytes src) (zbytes (xm_lxb m)) rb 0 H Hr (xk_src_rel_any _ _) Hrb Hb).
Qed.

Lemma xk_move_dst (src: list Z) (k: nat) (m m': xmem) (d s: Z) (c: list val) (rb: Z) :
  xm_move src k m R_dst d R_dst s = Some m' -> dst_rel c rb (xm_dst m) -> 0 <= rb -> rb + d + Z.of_nat k <= Zlength c ->
  xm_lxb m' = xm_lxb m /\ dst_rel (lmove k c (rb + d) LW (rb + s)) rb (xm_dst m').
Proof.
  intros H Hr Hrb Hb.
  exact (xm_move_l src k m m' d R_dst s c (zbytes src) (zbytes (xm_lxb m)) rb 0 H Hr (xk_src_rel_any _ _) Hrb Hb).
Qed.

Lemma xk_wild_dst (src: list Z) (m m': xmem) (d s len: Z) (b: bool) (c: list val) (rb: Z) :
  xm_wild src m d R_dst s len b = Some m' -> dst_rel c rb (xm_dst m) -> 0 <= rb ->
  rb + d + Z.max 16 (len + 31) <= Zlength c ->
  xm_lxb m' = xm_lxb m /\ dst_rel (lwild c (rb + d) LW (rb + s) len b) rb (xm_dst m').
Proof.
  intros H Hr Hrb Hb.
  exact (xk_wild src m m' d R_dst s len b c (zbytes src) (zbytes (xm_lxb m)) rb 0 H Hr (xk_src_rel_any _ _) Hrb Hb
    (fun _ => eq_refl)).
Qed.

(* a byte loop of a signed length (none when it is not positive) *)
Lemma xk_fwd_z (src: list Z) (len: Z) (m m': xmem) (d s: Z) (c: list val) (rb: Z) :
  xm_fwd src (Z.to_nat len) m R_dst d R_dst s = Some m' -> dst_rel c rb (xm_dst m) -> 0 <= rb ->
  (0 < len -> rb + d + len <= Zlength c) ->
  xm_lxb m' = xm_lxb m /\ dst_rel (lfwd (Z.to_nat len) c (rb + d) LW (rb + s)) rb (xm_dst m').
Proof.
  intros H Hr Hrb Hb. destruct (Z_le_gt_dec len 0).
  - rewrite (Z_to_nat_neg len) in * by lia. cbn in H |- *. inversion H; subst. split; [reflexivity|exact Hr].
  - apply (xk_fwd_dst _ _ _ _ _ _ _ _ H Hr Hrb). rewrite Z2Nat.id by lia. lia.
Qed.

(* ZSTD_overlapCopy8: 8 bytes from op *)
Lemma xk_ov8 (src: list Z) (m m': xmem) (op ip off op' ip': Z) (c: list val) (rb: Z) :
  xm_ov8 src m op ip off = Some (m', op', ip') -> dst_rel c rb (xm_dst m) -> 0 <= rb -> rb + op + 8 <= Zlength c ->
  exists c', lov8 c (rb + op) (rb + ip) off = (c', rb + op', rb + ip') /\ dst_rel c' rb (xm_dst m') /\
    Zlength c' = Zlength c /\ xm_lxb m' = xm_lxb m /\ op' = op + 8.
Proof.
  intros H Hr Hrb Hb. unfold xm_ov8 in H. unfold lov8.
  destruct (off <? 8).
  - destruct (xm_fwd src 4 m R_dst op R_dst ip) as [m1|] eqn:E1; [|discriminate].
    destruct (xm_fwd src 4 m1 R_dst (op + 4) R_dst (ip + xdec32 off)) as [m2|] eqn:E2; [|discriminate].
    inversion H; subst; clear H.
    destruct (xm_fwd_l src 4 m m1 op R_dst ip c (zbytes src) (zbytes (xm_lxb m)) rb 0 E1 Hr
      (xk_src_rel_any _ _) Hrb ltac:(cbn; lia)) as [Hl1 Hr1]. cbn [reg_l reg_o] in Hr1.
    destruct (xm_fwd_l src 4 m1 m' (op + 4) R_dst (ip + xdec32 off) _ (zbytes src) (zbytes (xm_lxb m1)) rb 0 E2 Hr1
      (xk_src_rel_any _ _) Hrb ltac:(rewrite lfwd_len; cbn; lia)) as [Hl2 Hr2]. cbn [reg_l reg_o] in Hr2.
    eexists. split; [|split; [exact Hr2|split; [rewrite !lfwd_len; reflexivity|split; [congruence|reflexivity]]]].
    replace (rb + op + 4) with (rb + (op + 4)) by lia.
    replace (rb + ip + xdec32 off) with (rb + (ip + xdec32 off)) by lia.
    f_equal; [f_equal|]; lia.
  - destruct (xm_fwd src 8 m R_dst op R_dst ip) as [m1|] eqn:E1; [|discriminate].
    inversion H; subst; clear H.
    destruct (xm_fwd_l src 8 m m' op R_dst ip c (zbytes src) (zbytes (xm_lxb m)) rb 0 E1 Hr
      (xk_src_rel_any _ _) Hrb ltac:(cbn; lia)) as [Hl1 Hr1]. cbn [reg_l reg_o] in Hr1.
    eexists. split; [|split; [exact Hr1|split; [rewrite !lfwd_len; reflexivity|split; [congruence|reflexivity]]]].
    f_equal; [f_equal|]; lia.
Qed.

(* the first step of ZSTD_safecopy: ZSTD_overlapCopy8 when the source is before the output *)
Lemma xk_safecopy_pre (src: list Z) (m m1: xmem) (op rs_ip op1 ip1: Z) (rs: xreg) (b: bool)
    (c ci cl: list val) (rb bo: Z) :
  (if b then xm_ov8 src m op rs_ip (op - rs_ip) else Some (m, op, rs_ip)) = Some (m1, op1, ip1) ->
  dst_rel c rb (xm_dst m) -> 0 <= rb -> rb + op + 8 <= Zlength c -> (b = true -> rs = R_dst) ->
  exists c1,
    (if b then lov8 c (rb + op) (reg_o rs rb bo + rs_ip) (rb + op - (reg_o rs rb bo + rs_ip))
     else (c, rb + op, reg_o rs rb bo + rs_ip)) = (c1, rb + op1, reg_o rs rb bo + ip1) /\
    dst_rel c1 rb (xm_dst m1) /\ Zlength c1 = Zlength c /\ xm_lxb m1 = xm_lxb m /\
    op1 = (if b then op + 8 else op).
Proof.
  intros H Hr Hrb Hb Hsb. destruct b.
  - rewrite (Hsb eq_refl). cbn [reg_o]. replace (rb + op - (rb + rs_ip)) with (op - rs_ip) by lia.
    exact (xk_ov8 _ _ _ _ _ _ _ _ _ _ H Hr Hrb Hb).
  - inversion H; subst. exists c. split; [reflexivity|]. split; [exact Hr|]. repeat split.
Qed.

(* ZSTD_safecopy: it stores below op + len and below oend_w + 31 *)
Lemma xk_safecopy (src: list Z) (m m': xmem) (op w: Z) (rs: xreg) (ip len: Z) (b: bool)
    (c ci cl: list val) (rb bo: Z) :
  xm_safecopy src m op w rs ip len b = Some m' ->
  dst_rel c rb (xm_dst m) -> src_rel src (xm_lxb m) ci bo cl -> 0 <= rb ->
  rb + op + len <= Zlength c -> rb + w + 31 <= Zlength c -> (b = true -> rs = R_dst) ->
  xm_lxb m' = xm_lxb m /\
  dst_rel (lsafecopy c (rb + op) (rb + w) (reg_l rs ci cl) (reg_o rs rb bo + ip) len b) rb (xm_dst m').
Proof.
  intros H Hr Hs Hrb Hb Hw Hsb. unfold xm_safecopy in H. unfold lsafecopy.
  destruct (Z.ltb_spec len 8).
  - destruct (Z_le_gt_dec len 0).
    + rewrite (Z_to_nat_neg len) in * by lia. cbn in H |- *. inversion H; subst. split; [reflexivity|exact Hr].
    + apply (xm_fwd_l _ _ _ _ _ _ _ _ _ _ _ _ H Hr Hs Hrb). rewrite Z2Nat.id by lia. lia.
  - destruct (if b then xm_ov8 src m op ip (op - ip) else Some (m, op, ip)) as [[[m1 op1] ip1]|] eqn:Epre;
      [|discriminate].
    destruct (xk_safecopy_pre src m m1 op ip op1 ip1 rs b c ci cl rb bo Epre Hr Hrb ltac:(lia) Hsb)
      as (c1 & Hc1 & Hr1 & Hlen1 & Hl1 & Hop1).
    assert (Hs1: src_rel src (xm_lxb m1) ci bo cl) by (rewrite Hl1; exact Hs).
    assert (Hop1': op <= op1 <= op + 8) by (destruct b; lia).
    rewrite Hc1.
    replace (rb + w - (rb + op + len)) with (w - (op + len)) by lia.
    replace (rb + w - (rb + op1)) with (w - op1) by lia.
    destruct (w - (op + len) >=? 0) eqn:E1.
    + rewrite Z.geb_leb in E1. apply Z.leb_le in E1.
      destruct (xk_wild _ _ _ _ _ _ _ _ _ _ _ _ _ H Hr1 Hs1 Hrb) as [Hl Hr']; [destruct b; lia|exact Hsb|].
      split; [congruence|exact Hr'].
    + rewrite Z.geb_leb in E1. apply Z.leb_gt in E1.
      destruct (w - op1 >=? 0) eqn:E2.
      * rewrite Z.geb_leb in E2. apply Z.leb_le in E2.
        destruct (xm_wild src m1 op1 rs ip1 (w - op1) b) as [m2|] eqn:Ew; [|discriminate].
        destruct (xk_wild _ _ _ _ _ _ _ _ _ _ _ _ _ Ew Hr1 Hs1 Hrb) as [Hl2 Hr2]; [lia|exact Hsb|].
        replace (rb + op + len - (rb + w)) with (op + len - w) by lia.
        replace (reg_o rs rb bo + ip1 + (w - op1)) with (reg_o rs rb bo + (ip1 + (w - op1))) by lia.
        destruct (xm_fwd_l _ _ _ _ _ _ _ _ ci cl rb bo H Hr2) as [Hl3 Hr3];
          [rewrite Hl2; exact Hs1 | exact Hrb | rewrite lwild_len, Z2Nat.id by lia; lia |].
        split; [congruence|exact Hr3].
      * replace (rb + op + len - (rb + op1)) with (op + len - op1) by lia.
        destruct (xm_fwd_l _ _ _ _ _ _ _ _ _ _ _ _ H Hr1 Hs1 Hrb) as [Hl3 Hr3];
          [rewrite Z2Nat.id by lia; lia |].
        split; [congruence|exact Hr3].
Qed.

(* ZSTD_safecopyDstBeforeSrc (it stores only in [op, op + len)) *)
Lemma xm_sdbs_l (src: list Z) (m m': xmem) (op ip len: Z) (c: list val) (rb: Z) :
  xm_sdbs src m op ip len = Some m' ->
  dst_rel c rb (xm_dst m) -> 0 <= rb -> rb + op + len <= Zlength c ->
  xm_lxb m' = xm_lxb m /\ dst_rel (lsdbs c (rb + op) (rb + ip) len) rb (xm_dst m').
Proof.
  intros H Hr Hrb Hb. unfold xm_sdbs in H. unfold lsdbs. cbv zeta in H |- *.
  replace (rb + op - (rb + ip)) with (op - ip) by lia.
  destruct ((len <? 8) || (op - ip >? -8)) eqn:E1.
  - apply (xk_fwd_z _ _ _ _ _ _ _ _ H Hr Hrb). lia.
  - destruct ((len >=? 32) && (op - ip <? -16)) eqn:E2.
    + apply andb_true_iff in E2 as [E2 _]. rewrite Z.geb_leb in E2. apply Z.leb_le in E2.
      destruct (xm_wild src m op R_dst ip (len - 32) false) as [m1|] eqn:Ew; [|discriminate].
      destruct (xk_wild_dst _ _ _ _ _ _ _ _ _ Ew Hr Hrb) as [Hl1 Hr1]; [lia|].
      replace (rb + op + len - (rb + op + len - 32)) with (op + len - (op + len - 32)) by lia.
      replace (rb + op + len - 32) with (rb + (op + len - 32)) by lia.
      replace (rb + ip + len - 32) with (rb + (ip + len - 32)) by lia.
      destruct (xk_fwd_z _ _ _ _ _ _ _ _ H Hr1 Hrb) as [Hl2 Hr2]; [rewrite lwild_len; lia|].
      split; [congruence|exact Hr2].
    + replace (rb + op + len - (rb + op)) with (op + len - op) by lia.
      apply (xk_fwd_z _ _ _ _ _ _ _ _ H Hr Hrb). lia.
Qed.

(* the match within the prefix: ZSTD_safecopy (slow path: below op + ml and oend_w + 31), or
   ZSTD_overlapCopy8 / ZSTD_wildcopy (fast path: below op + max(16, ml + 31)) *)
Lemma xk_prefix (e: xenv) (m m': xmem) (op mt ml off: Z) (wo: option Z) (c: list val) (rb: Z) :
  xm_prefix e m op mt ml off wo = Some m' -> dst_rel c rb (xm_dst m) -> 0 <= rb ->
  match wo with
  | Some w => rb + op + ml <= Zlength c /\ rb + w + 31 <= Zlength c
  | None => rb + op + Z.max 16 (ml + 31) <= Zlength c
  end ->
  xm_lxb m' = xm_lxb m /\ dst_rel (lprefix c (rb + op) (rb + mt) ml off (option_map (Z.add rb) wo)) rb (xm_dst m').
Proof.
  intros H Hr Hrb Hb. unfold xm_prefix in H. unfold lprefix. destruct wo as [w|]; cbn [option_map].
  - destruct Hb as [Hb1 Hb2].
    exact (xk_safecopy (xe_src e) m m' op w R_dst mt ml true c (zbytes (xe_src e)) (zbytes (xm_lxb m)) rb 0
      H Hr (xk_src_rel_any _ _) Hrb Hb1 Hb2 (fun _ => eq_refl)).
  - destruct (off >=? 16).
    + exact (xk_wild_dst _ _ _ _ _ _ _ _ _ H Hr Hrb Hb).
    + destruct (xm_ov8 (xe_src e) m op mt off) as [[[m1 op1] mt1]|] eqn:E; [|discriminate].
      destruct (xk_ov8 _ _ _ _ _ _ _ _ _ _ E Hr Hrb ltac:(lia)) as (c1 & Hc1 & Hr1 & Hlen1 & Hl1 & Hop1).
      rewrite Hc1. destruct (ml >? 8) eqn:E8.
      * xk_zb E8.
        destruct (xk_wild_dst _ _ _ _ _ _ _ _ _ H Hr1 Hrb) as [Hl2 Hr2]; [lia|].
        split; [congruence|exact Hr2].
      * inversion H; subst. split; [exact Hl1|exact Hr1].
Qed.

(* the match of a sequence at oLitEnd: from the extDict (a move), then within the prefix *)
Lemma xk_match (e: xenv) (m m': xmem) (oLitEnd ml off: Z) (wo: option Z) (c: list val) (rb: Z) :
  xm_match e m oLitEnd ml off wo = Some m' -> dst_rel c rb (xm_dst m) -> 0 <= rb -> 0 <= ml ->
  match wo with
  | Some w => rb + oLitEnd + ml <= Zlength c /\ rb + w + 31 <= Zlength c
  | None => rb + oLitEnd + ml + 31 <= Zlength c
  end ->
  xm_lxb m' = xm_lxb m /\
  dst_rel (lmatch (rb + xe_ps e) (rb + xe_vs e) (rb + xe_de e) c (rb + oLitEnd) ml off (option_map (Z.add rb) wo))
    rb (xm_dst m').
Proof.
  intros H Hr Hrb Hml Hb. unfold xm_match in H. unfold lmatch. cbv zeta in H |- *.
  assert (Hb0: rb + oLitEnd + ml <= Zlength c) by (destruct wo as [w|]; lia).
  replace (rb + oLitEnd - (rb + xe_ps e)) with (oLitEnd - xe_ps e) by lia.
  replace (rb + xe_de e + (rb + oLitEnd - off - (rb + xe_ps e)))
    with (rb + (xe_de e + (oLitEnd - off - xe_ps e))) by lia.
  replace (rb + xe_de e - (rb + (xe_de e + (oLitEnd - off - xe_ps e))))
    with (xe_de e - (xe_de e + (oLitEnd - off - xe_ps e))) by lia.
  destruct (off >? oLitEnd - xe_ps e) eqn:E1.
  - xk_zb E1. destruct (off >? oLitEnd - xe_vs e); [discriminate|].
    destruct (xe_de e - (xe_de e + (oLitEnd - off - xe_ps e)) >=? ml) eqn:E2.
    + apply (xk_move_dst _ _ _ _ _ _ _ _ H Hr Hrb). rewrite Z2Nat.id by lia. exact Hb0.
    + xk_zb E2.
      destruct (xm_move (xe_src e) (Z.to_nat (xe_de e - (xe_de e + (oLitEnd - off - xe_ps e)))) m R_dst oLitEnd
        R_dst (xe_de e + (oLitEnd - off - xe_ps e))) as [m1|] eqn:Em; [|discriminate].
      destruct (xk_move_dst _ _ _ _ _ _ _ _ Em Hr Hrb) as [Hl1 Hr1]; [rewrite Z2Nat.id by lia; lia|].
      replace (rb + oLitEnd + (xe_de e - (xe_de e + (oLitEnd - off - xe_ps e))))
        with (rb + (oLitEnd + (xe_de e - (xe_de e + (oLitEnd - off - xe_ps e))))) by lia.
      destruct (xk_prefix _ _ _ _ _ _ _ _ _ _ H Hr1 Hrb) as [Hl2 Hr2].
      { rewrite lmove_len. destruct wo as [w|]; lia. }
      split; [congruence|exact Hr2].
  - replace (rb + oLitEnd - off) with (rb + (oLitEnd - off)) by lia.
    apply (xk_prefix _ _ _ _ _ _ _ _ _ _ H Hr Hrb). destruct wo as [w|]; lia.
Qed.

(* ZSTD_execSequence / ZSTD_execSequenceEnd: every store is before the output end oend (for the lengths of a
   decoded sequence, ll and ml nonnegative: with a negative length the fast path's first ZSTD_copy16 could
   start past oend) *)
Lemma x_exec_l (e: xenv) (m m': xmem) (op: Z) (lr: xreg) (li llim ll ml off op' li': Z)
    (c ci cl: list val) (rb bo: Z) :
  x_exec e m op lr li llim ll ml off = Some (m', op', li') ->
  dst_rel c rb (xm_dst m) -> src_rel (xe_src e) (xm_lxb m) ci bo cl ->
  0 <= ll -> 0 <= ml -> 0 <= rb -> rb + xe_oend e <= Zlength c ->
  xm_lxb m' = xm_lxb m /\
  dst_rel (lexec (rb + xe_ps e) (rb + xe_vs e) (rb + xe_de e) (rb + xe_oend e) c (rb + op)
             (reg_l lr ci cl) (reg_o lr rb bo + li) (reg_o lr rb bo + llim) ll ml off) rb (xm_dst m').
Proof.
  intros H Hr Hs Hll Hml Hrb Hb. unfold x_exec in H. unfold lexec. cbv zeta in H |- *.
  unfold WILDCOPY_OVERLENGTH, XWILDCOPY in *.
  replace (reg_o lr rb bo + llim - (reg_o lr rb bo + li)) with (llim - li) by lia.
  replace (rb + xe_oend e - 32 - (rb + op)) with (xe_oend e - 32 - op) by lia.
  replace (rb + xe_oend e - 32) with (rb + (xe_oend e - 32)) by lia.
  replace (rb + op + ll) with (rb + (op + ll)) by lia.
  destruct ((llim - li <? ll) || (xe_oend e - 32 - op <? ll + ml)) eqn:E.
  - destruct (ll + ml >? xe_oend e - op) eqn:E1; [discriminate|]. xk_zb E1.
    destruct (ll >? llim - li); [discriminate|].
    destruct (xm_safecopy (xe_src e) m op (xe_oend e - 32) lr li ll false) as [m1|] eqn:Es; [|discriminate].
    destruct (xm_match e m1 (op + ll) ml off (Some (xe_oend e - 32))) as [m2|] eqn:Em; [|discriminate].
    inversion H; subst m2; clear H.
    destruct (xk_safecopy _ _ _ _ _ _ _ _ _ _ _ _ _ _ Es Hr Hs Hrb) as [Hl1 Hr1];
      [lia | lia | discriminate |].
    change (Some (rb + (xe_oend e - 32))) with (option_map (Z.add rb) (Some (xe_oend e - 32))).
    destruct (xk_match _ _ _ _ _ _ _ _ _ Em Hr1 Hrb Hml) as [Hl2 Hr2].
    { rewrite lsafecopy_len. lia. }
    split; [congruence|exact Hr2].
  - apply orb_false_iff in E as [E1 E2]. xk_zb E1. xk_zb E2.
    destruct (xm_move (xe_src e) 16 m R_dst op lr li) as [m1|] eqn:Em1; [|discriminate].
    destruct (xm_move_l _ _ _ _ _ _ _ _ _ _ _ _ Em1 Hr Hs Hrb) as [Hl1 Hr1]; [cbn; lia|].
    assert (Hs1: src_rel (xe_src e) (xm_lxb m1) ci bo cl) by (rewrite Hl1; exact Hs).
    destruct (if ll >? 16 then xm_wild (xe_src e) m1 (op + 16) lr (li + 16) (ll - 16) false else Some m1)
      as [m2|] eqn:Ew; [|discriminate].
    destruct (xm_match e m2 (op + ll) ml off None) as [m3|] eqn:Em; [|discriminate].
    inversion H; subst m3; clear H.
    assert (Hw: xm_lxb m2 = xm_lxb m1 /\
      dst_rel (if ll >? 16
               then lwild (lmove 16 c (rb + op) (reg_l lr ci cl) (reg_o lr rb bo + li))
                      (rb + op + 16) (reg_l lr ci cl) (reg_o lr rb bo + li + 16) (ll - 16) false
               else lmove 16 c (rb + op) (reg_l lr ci cl) (reg_o lr rb bo + li)) rb (xm_dst m2)).
    { destruct (ll >? 16) eqn:E16.
      - xk_zb E16. replace (rb + op + 16) with (rb + (op + 16)) by lia.
        replace (reg_o lr rb bo + li + 16) with (reg_o lr rb bo + (li + 16)) by lia.
        apply (xk_wild _ _ _ _ _ _ _ _ _ _ _ _ _ Ew Hr1 Hs1 Hrb); [rewrite lmove_len; lia | discriminate].
      - inversion Ew; subst m2. split; [reflexivity|exact Hr1]. }
    destruct Hw as [Hl2 Hr2].
    change None with (option_map (Z.add rb) None).
    destruct (xk_match _ _ _ _ _ _ _ _ _ Em Hr2 Hrb Hml) as [Hl3 Hr3].
    { destruct (ll >? 16); [rewrite lwild_len|]; rewrite lmove_len; lia. }
    split; [congruence|exact Hr3].
Qed.

(* ZSTD_execSequenceSplitLitBuffer / ZSTD_execSequenceEndSplitLitBuffer: the literals' part in dst ends 32
   bytes before oend (every store is then before oend; ll and ml nonnegative as above) *)
Lemma x_exec_split_l (e: xenv) (m m': xmem) (op li llim ll ml off op' li': Z) (c: list val) (rb: Z) :
  x_exec_split e m op li llim ll ml off = Some (m', op', li') ->
  dst_rel c rb (xm_dst m) -> 0 <= ll -> 0 <= ml -> 0 <= rb -> rb + xe_oend e <= Zlength c ->
  llim + WILDCOPY_OVERLENGTH <= xe_oend e ->
  xm_lxb m' = xm_lxb m /\
  dst_rel (lexec_split (rb + xe_ps e) (rb + xe_vs e) (rb + xe_de e) (rb + xe_oend e) c (rb + op)
             (rb + li) (rb + llim) ll ml off) rb (xm_dst m').
Proof.
  intros H Hr Hll Hml Hrb Hb Hlim. unfold x_exec_split in H. unfold lexec_split. cbv zeta in H |- *.
  unfold WILDCOPY_OVERLENGTH, XWILDCOPY in *.
  replace (rb + llim - (rb + li)) with (llim - li) by lia.
  replace (rb + li + ll - 32 - (rb + op)) with (li + ll - 32 - op) by lia.
  replace (rb + li + ll - 32) with (rb + (li + ll - 32)) by lia.
  replace (rb + op + ll) with (rb + (op + ll)) by lia.
  destruct ((llim - li <? ll) || (li + ll - 32 - op <? ll + ml)) eqn:E.
  - destruct (ll + ml >? xe_oend e - op) eqn:E1; [discriminate|]. xk_zb E1.
    destruct (ll >? llim - li) eqn:E2; [discriminate|]. xk_zb E2.
    destruct ((op >? li) && (op <? li + ll)); [discriminate|].
    destruct (xm_sdbs (xe_src e) m op li ll) as [m1|] eqn:Es; [|discriminate].
    destruct (xm_match e m1 (op + ll) ml off (Some (li + ll - 32))) as [m2|] eqn:Em; [|discriminate].
    inversion H; subst m2; clear H.
    destruct (xm_sdbs_l _ _ _ _ _ _ _ _ Es Hr Hrb) as [Hl1 Hr1]; [lia|].
    change (Some (rb + (li + ll - 32))) with (option_map (Z.add rb) (Some (li + ll - 32))).
    destruct (xk_match _ _ _ _ _ _ _ _ _ Em Hr1 Hrb Hml) as [Hl2 Hr2].
    { rewrite lsdbs_len. lia. }
    split; [congruence|exact Hr2].
  - apply orb_false_iff in E as [E1 E2]. xk_zb E1. xk_zb E2.
    destruct (xm_move (xe_src e) 16 m R_dst op R_dst li) as [m1|] eqn:Em1; [|discriminate].
    destruct (xk_move_dst _ _ _ _ _ _ _ _ Em1 Hr Hrb) as [Hl1 Hr1]; [cbn; lia|].
    destruct (if ll >? 16 then xm_wild (xe_src e) m1 (op + 16) R_dst (li + 16) (ll - 16) false else Some m1)
      as [m2|] eqn:Ew; [|discriminate].
    destruct (xm_match e m2 (op + ll) ml off None) as [m3|] eqn:Em; [|discriminate].
    inversion H; subst m3; clear H.
    assert (Hw: xm_lxb m2 = xm_lxb m1 /\
      dst_rel (if ll >? 16
               then lwild (lmove 16 c (rb + op) LW (rb + li)) (rb + op + 16) LW (rb + li + 16) (ll - 16) false
               else lmove 16 c (rb + op) LW (rb + li)) rb (xm_dst m2)).
    { destruct (ll >? 16) eqn:E16.
      - xk_zb E16. replace (rb + op + 16) with (rb + (op + 16)) by lia.
        replace (rb + li + 16) with (rb + (li + 16)) by lia.
        apply (xk_wild_dst _ _ _ _ _ _ _ _ _ Ew Hr1 Hrb). rewrite lmove_len. lia.
      - inversion Ew; subst m2. split; [reflexivity|exact Hr1]. }
    destruct Hw as [Hl2 Hr2].
    change None with (option_map (Z.add rb) None).
    destruct (xk_match _ _ _ _ _ _ _ _ _ Em Hr2 Hrb Hml) as [Hl3 Hr3].
    { destruct (ll >? 16); [rewrite lwild_len|]; rewrite lmove_len; lia. }
    split; [congruence|exact Hr3].
Qed.
