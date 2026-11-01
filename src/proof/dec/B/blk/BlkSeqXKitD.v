(* The model's stores (model/ExBlock.v) never read an unwritten cell when the cells zstd reads are written:
   the history [prefixStart, op) and the extDict [dictStart, dictEnd) (xh_ok), the literals with the 32
   cells after them (xl_ok).  Then the model's executors fail exactly on the C's error conditions
   (capacity, literals, offset; split: the output caught up with the literals), and on success they write
   [op, op + ll + ml) and keep every written cell written.  Plain Coq. *)
Require Export Zstd.proof.dec.B.blk.BlkSeqXMem.
Require Import Zstd.proof.model.ExBlock.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

(* the history the matches read is written (virtualStart = prefixStart - (dictEnd - dictStart)) *)
Definition xh_ok (e: xenv) (m: xmem) (op: Z) : Prop :=
  0 <= xe_ps e <= op /\ xe_vs e <= xe_ps e /\ 0 <= xe_de e - (xe_ps e - xe_vs e) /\
  xwr_rng m (xe_ps e) op /\ xwr_rng m (xe_de e - (xe_ps e - xe_vs e)) (xe_de e).

(* the literals [li, lim) with the 32 cells after them are readable *)
Definition xl_ok (e: xenv) (m: xmem) (lr: xreg) (li lim: Z) : Prop :=
  0 <= li <= lim /\
  match lr with
  | R_dst => xwr_rng m li (lim + WILDCOPY_OVERLENGTH)
  | R_src => lim + WILDCOPY_OVERLENGTH <= Zlength (xe_src e)
  | R_lxb => lim + WILDCOPY_OVERLENGTH <= Zlength (xm_lxb m)
  end.

(* the C's error conditions (BlkSeqEXEC.exec_err / exec_split_err in the model's coordinates) *)
Definition xexec_err (e: xenv) (op li llim ll ml off: Z) : bool :=
  (xe_oend e - op <? ll + ml) || (llim - li <? ll) || (op + ll - xe_vs e <? off).
Definition xsplit_err (e: xenv) (op li ll ml off: Z) : bool :=
  (xe_oend e - op <? ll + ml) || ((li <? op) && (op <? li + ll)) || (op + ll - xe_vs e <? off).

(* ---------- the cells: one store, one read ---------- *)

Lemma xkd_nth_upd : forall {A} (l: list A) i n x d,
  nth n (Fse.upd l i x) d = if Nat.eqb n i then (if Nat.ltb i (length l) then x else nth n l d) else nth n l d.
Proof.
  induction l as [|y l IH]; intros i n x d; cbn [Fse.upd length].
  - destruct (Nat.eqb n i); cbn; reflexivity.
  - destruct i, n; cbn [nth Nat.eqb Nat.ltb Fse.upd]; try reflexivity. apply IH.
Qed.

Lemma xm_le_refl : forall m, xm_le m m.
Proof. intros m. split; auto. Qed.

Lemma xm_le_trans : forall m1 m2 m3, xm_le m1 m2 -> xm_le m2 m3 -> xm_le m1 m3.
Proof. intros m1 m2 m3 [A1 B1] [A2 B2]. split; [auto|congruence]. Qed.

Lemma xwr_rng_le : forall m m' a b, xm_le m m' -> xwr_rng m a b -> xwr_rng m' a b.
Proof. intros m m' a b [H _] R j Hj. apply H, R, Hj. Qed.

Lemma xwr_rng_sub : forall m a b a' b', a <= a' -> b' <= b -> xwr_rng m a b -> xwr_rng m a' b'.
Proof. intros m a b a' b' H1 H2 R j Hj. apply R. lia. Qed.

Lemma xwr_rng_app : forall m a b c, xwr_rng m a b -> xwr_rng m b c -> xwr_rng m a c.
Proof. intros m a b c R1 R2 j Hj. destruct (Z.ltb_spec j b); [apply R1|apply R2]; lia. Qed.

(* a store to dst at a nonnegative index succeeds, writes its cell and keeps the others *)
Lemma xkd_wr : forall m i v, 0 <= i ->
  exists m', xm_wr m R_dst i v = Some m' /\ xm_le m m' /\ xwr m' i.
Proof.
  intros m i v Hi. unfold xm_wr. destruct (Z.ltb_spec i 0) as [H|_]; [lia|].
  eexists; split; [reflexivity|]. unfold xm_le, xwr; cbn [xm_dst xm_lxb].
  destruct (Z.ltb_spec i (Zlength (xm_dst m))) as [Hl|Hl]; rewrite Zlength_correct in *.
  - split; [split; [|reflexivity]|].
    + intros j [Hj Hn]. split; [lia|]. rewrite xkd_nth_upd.
      destruct (Nat.eqb_spec (Z.to_nat j) (Z.to_nat i)); [|exact Hn].
      destruct (Nat.ltb_spec (Z.to_nat i) (length (xm_dst m))); [discriminate|exact Hn].
    + split; [lia|]. rewrite xkd_nth_upd, Nat.eqb_refl.
      destruct (Nat.ltb_spec (Z.to_nat i) (length (xm_dst m))); [discriminate|lia].
  - split; [split; [|reflexivity]|].
    + intros j [Hj Hn]. split; [lia|].
      destruct (Nat.ltb_spec (Z.to_nat j) (length (xm_dst m))).
      * rewrite app_nth1 by lia. exact Hn.
      * rewrite nth_overflow in Hn by lia. congruence.
    + split; [lia|]. rewrite app_nth2 by lia. rewrite app_nth2 by (rewrite repeat_length; lia).
      rewrite repeat_length.
      replace (Z.to_nat i - length (xm_dst m) - Z.to_nat (i - Z.of_nat (length (xm_dst m))))%nat with O by lia.
      cbn [nth]. discriminate.
Qed.

(* a readable cell: written in dst, within the buffer in litExtraBuffer and the block *)
Definition xrd (src: list Z) (m: xmem) (r: xreg) (j: Z) : Prop :=
  match r with
  | R_dst => xwr m j
  | R_src => 0 <= j < Zlength src
  | R_lxb => 0 <= j < Zlength (xm_lxb m)
  end.
Definition xrd_rng (src: list Z) (m: xmem) (r: xreg) (a b: Z) : Prop := forall j, a <= j < b -> xrd src m r j.

Lemma xrd_le : forall src m m' r j, xm_le m m' -> xrd src m r j -> xrd src m' r j.
Proof. intros src m m' r j [H1 H2] H. destruct r; cbn in *; [auto| rewrite H2; auto | auto]. Qed.

Lemma xrd_rng_le : forall src m m' r a b, xm_le m m' -> xrd_rng src m r a b -> xrd_rng src m' r a b.
Proof. intros src m m' r a b H R j Hj. eapply xrd_le; [exact H|]. apply R, Hj. Qed.

Lemma xrd_rng_sub : forall src m r a b a' b', a <= a' -> b' <= b -> xrd_rng src m r a b -> xrd_rng src m r a' b'.
Proof. intros src m r a b a' b' H1 H2 R j Hj. apply R. lia. Qed.

Lemma xrd_some : forall src m r j, xrd src m r j -> exists v, xm_rd src m r j = Some v.
Proof.
  intros src m r j H. unfold xm_rd. destruct r; cbn in H.
  - destruct H as [Hj Hn]. destruct (Z.ltb_spec j 0); [lia|].
    destruct (nth (Z.to_nat j) (xm_dst m) None) as [v|]; [eauto|congruence].
  - destruct (Z.ltb_spec j 0); [lia|]. destruct (Z.ltb_spec j (Zlength (xm_lxb m))); [eauto|lia].
  - destruct (Z.ltb_spec j 0); [lia|]. destruct (Z.ltb_spec j (Zlength src)); [eauto|lia].
Qed.

(* ---------- runs of stores ---------- *)

(* k bytes forward succeed when each byte is readable when it is read: readable from the start, or a cell
   of dst stored by the run itself (d <= s + i < d + i) *)
Lemma xkd_fwd : forall src rs k m d s, 0 <= d ->
  (forall i, 0 <= i < Z.of_nat k -> xrd src m rs (s + i) \/ (rs = R_dst /\ d <= s + i < d + i)) ->
  exists m', xm_fwd src k m R_dst d rs s = Some m' /\ xm_le m m' /\ xwr_rng m' d (d + Z.of_nat k).
Proof.
  intros src rs. induction k as [|k IH]; intros m d s Hd H.
  - exists m. split; [reflexivity|]. split; [apply xm_le_refl|]. intros j Hj; lia.
  - destruct (H 0 ltac:(lia)) as [H0|[_ H0]]; [|lia].
    rewrite Z.add_0_r in H0. destruct (xrd_some _ _ _ _ H0) as [v Hv].
    destruct (xkd_wr m d v Hd) as [m1 [Hw [Hle1 Hd1]]].
    destruct (IH m1 (d + 1) (s + 1)) as [m' [Hf [Hle Hr]]]; [lia| |].
    + intros i Hi. destruct (H (i + 1) ltac:(lia)) as [Hc|[Er Hc]].
      * left. replace (s + 1 + i) with (s + (i + 1)) by lia. eapply xrd_le; eauto.
      * destruct (Z.eq_dec (s + (i + 1)) d) as [E|E].
        -- left. subst rs. cbn. replace (s + 1 + i) with d by lia. exact Hd1.
        -- right. split; [exact Er|lia].
    + exists m'. split; [cbn [xm_fwd]; rewrite Hv, Hw; exact Hf|].
      split; [eapply xm_le_trans; eauto|].
      intros j Hj. destruct (Z.eq_dec j d) as [->|E]; [apply (proj1 Hle); exact Hd1|apply Hr; lia].
Qed.

(* the source readable from the start *)
Lemma xkd_fwd_rd : forall src rs k m d s, 0 <= d -> xrd_rng src m rs s (s + Z.of_nat k) ->
  exists m', xm_fwd src k m R_dst d rs s = Some m' /\ xm_le m m' /\ xwr_rng m' d (d + Z.of_nat k).
Proof. intros src rs k m d s Hd R. apply xkd_fwd; [exact Hd|]. intros i Hi. left. apply R. lia. Qed.

(* the source in dst before the destination, [s, d) written *)
Lemma xkd_fwd_back : forall src k m d s, 0 <= s -> 1 <= d - s -> xwr_rng m s d ->
  exists m', xm_fwd src k m R_dst d R_dst s = Some m' /\ xm_le m m' /\ xwr_rng m' d (d + Z.of_nat k).
Proof.
  intros src k m d s Hs Hd R. apply xkd_fwd; [lia|]. intros i Hi.
  destruct (Z.ltb_spec (s + i) d); [left; apply R; lia|right; split; [reflexivity|lia]].
Qed.

Lemma xkd_rdn : forall src r k m s, xrd_rng src m r s (s + Z.of_nat k) ->
  exists vs, xm_rdn src k m r s = Some vs /\ length vs = k.
Proof.
  intros src r. induction k as [|k IH]; intros m s R; [exists nil; split; reflexivity|].
  destruct (xrd_some src m r s (R s ltac:(lia))) as [v Hv].
  destruct (IH m (s + 1)) as [vs [Hvs Hl]]; [intros j Hj; apply R; lia|].
  exists (v :: vs). split; [cbn [xm_rdn]; rewrite Hv, Hvs; reflexivity|cbn; congruence].
Qed.

Lemma xkd_wrn : forall vs m d, 0 <= d ->
  exists m', xm_wrn vs m R_dst d = Some m' /\ xm_le m m' /\ xwr_rng m' d (d + Z.of_nat (length vs)).
Proof.
  induction vs as [|v vs IH]; intros m d Hd.
  - exists m. split; [reflexivity|]. split; [apply xm_le_refl|]. intros j Hj; cbn in Hj; lia.
  - destruct (xkd_wr m d v Hd) as [m1 [Hw [Hle1 Hd1]]].
    destruct (IH m1 (d + 1)) as [m' [Hf [Hle Hr]]]; [lia|].
    exists m'. split; [cbn [xm_wrn]; rewrite Hw; exact Hf|].
    split; [eapply xm_le_trans; eauto|].
    intros j Hj. cbn [length] in Hj. destruct (Z.eq_dec j d) as [->|E]; [apply (proj1 Hle); exact Hd1|apply Hr; lia].
Qed.

Lemma xkd_move : forall src rs k m d s, 0 <= d -> xrd_rng src m rs s (s + Z.of_nat k) ->
  exists m', xm_move src k m R_dst d rs s = Some m' /\ xm_le m m' /\ xwr_rng m' d (d + Z.of_nat k).
Proof.
  intros src rs k m d s Hd R. destruct (xkd_rdn src rs k m s R) as [vs [Hvs Hl]].
  destruct (xkd_wrn vs m d Hd) as [m' [Hw [Hle Hr]]]. rewrite Hl in Hr.
  exists m'. unfold xm_move. rewrite Hvs. auto.
Qed.

Lemma xkd_chunks_rd : forall src rs k m d s, 0 <= d -> xrd_rng src m rs s (s + 16 * Z.of_nat k) ->
  exists m', xm_chunks16 src k m d rs s = Some m' /\ xm_le m m' /\ xwr_rng m' d (d + 16 * Z.of_nat k).
Proof.
  intros src rs. induction k as [|k IH]; intros m d s Hd R.
  - exists m. split; [reflexivity|]. split; [apply xm_le_refl|]. intros j Hj; lia.
  - destruct (xkd_move src rs 16 m d s Hd) as [m1 [Hm [Hle1 Hr1]]]; [intros j Hj; apply R; lia|].
    destruct (IH m1 (d + 16) (s + 16)) as [m' [Hf [Hle Hr]]]; [lia| |].
    + eapply xrd_rng_le; [exact Hle1|]. intros j Hj; apply R; lia.
    + exists m'. split; [cbn [xm_chunks16]; rewrite Hm; exact Hf|].
      split; [eapply xm_le_trans; eauto|].
      intros j Hj. destruct (Z.ltb_spec j (d + 16)); [apply (proj1 Hle), Hr1; cbn; lia|apply Hr; lia].
Qed.

(* chunks of a match at distance >= 16: each reads cells written before it *)
Lemma xkd_chunks_back : forall src k m d s, 0 <= s -> 16 <= d - s -> xwr_rng m s d ->
  exists m', xm_chunks16 src k m d R_dst s = Some m' /\ xm_le m m' /\ xwr_rng m' d (d + 16 * Z.of_nat k).
Proof.
  intros src. induction k as [|k IH]; intros m d s Hs Hd R.
  - exists m. split; [reflexivity|]. split; [apply xm_le_refl|]. intros j Hj; lia.
  - destruct (xkd_move src R_dst 16 m d s) as [m1 [Hm [Hle1 Hr1]]]; [lia|intros j Hj; apply R; cbn in Hj; lia|].
    destruct (IH m1 (d + 16) (s + 16)) as [m' [Hf [Hle Hr]]]; [lia|lia| |].
    + intros j Hj. destruct (Z.ltb_spec j d); [apply (proj1 Hle1), R; lia|apply Hr1; cbn; lia].
    + exists m'. split; [cbn [xm_chunks16]; rewrite Hm; exact Hf|].
      split; [eapply xm_le_trans; eauto|].
      intros j Hj. destruct (Z.ltb_spec j (d + 16)); [apply (proj1 Hle), Hr1; cbn; lia|apply Hr; lia].
Qed.

(* the number of ZSTD_copy16 of a wildcopy covers len and reads at most len + 31 bytes *)
Lemma xkd_nch : forall len, 0 <= len ->
  let nch := if len <=? 16 then 1 else 1 + 2 * ((len - 16 + 31) / 32) in
  0 <= nch /\ len <= 16 * nch <= len + 31.
Proof.
  intros len H. cbv zeta. destruct (Z.leb_spec len 16); [lia|].
  pose proof (Z.div_mod (len - 16 + 31) 32 ltac:(lia)). pose proof (Z.mod_pos_bound (len - 16 + 31) 32 ltac:(lia)).
  lia.
Qed.

(* the COPY8 loop of a short-offset wildcopy covers len *)
Lemma xkd_n8 : forall len, len <= 8 * Z.max 1 ((len + 7) / 8).
Proof.
  intros len. pose proof (Z.div_mod (len + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (len + 7) 8 ltac:(lia)).
  lia.
Qed.

Lemma xkd_wild_rd : forall src rs m d s len, 0 <= d -> 0 <= len -> xrd_rng src m rs s (s + len + 31) ->
  exists m', xm_wild src m d rs s len false = Some m' /\ xm_le m m' /\ xwr_rng m' d (d + len).
Proof.
  intros src rs m d s len Hd Hl R. unfold xm_wild. cbn [andb].
  destruct (xkd_nch len Hl) as [H0 H1].
  destruct (xkd_chunks_rd src rs (Z.to_nat (if len <=? 16 then 1 else 1 + 2 * ((len - 16 + 31) / 32))) m d s Hd)
    as [m' [Hc [Hle Hr]]]; [rewrite Z2Nat.id by lia; eapply xrd_rng_sub; [| |exact R]; lia|].
  rewrite Z2Nat.id in Hr by lia. exists m'. split; [exact Hc|]. split; [exact Hle|]. eapply xwr_rng_sub; [| |exact Hr]; lia.
Qed.

(* a wildcopy of a match: source before destination in dst, [s, d) written; at distance >= 16 when
   ZSTD_no_overlap *)
Lemma xkd_wild_back : forall src m d s len (b: bool), 0 <= s -> (if b then 1 else 16) <= d - s ->
  xwr_rng m s d -> 0 <= len ->
  exists m', xm_wild src m d R_dst s len b = Some m' /\ xm_le m m' /\ xwr_rng m' d (d + len).
Proof.
  intros src m d s len b Hs Hb R Hl. unfold xm_wild.
  destruct (xkd_nch len Hl) as [H0 H1].
  destruct (b && (d - s <? 16)) eqn:E.
  - destruct (xkd_fwd_back src (Z.to_nat (8 * Z.max 1 ((len + 7) / 8))) m d s Hs) as [m' [Hf [Hle Hr]]];
      [destruct b; lia|exact R|].
    pose proof (xkd_n8 len). rewrite Z2Nat.id in Hr by lia. exists m'. split; [exact Hf|]. split; [exact Hle|]. eapply xwr_rng_sub; [| |exact Hr]; lia.
  - assert (16 <= d - s) by (destruct b; cbn in E; [apply Z.ltb_ge in E|]; lia).
    destruct (xkd_chunks_back src (Z.to_nat (if len <=? 16 then 1 else 1 + 2 * ((len - 16 + 31) / 32))) m d s)
      as [m' [Hc [Hle Hr]]]; [lia|lia|exact R|].
    rewrite Z2Nat.id in Hr by lia. exists m'. split; [exact Hc|]. split; [exact Hle|]. eapply xwr_rng_sub; [| |exact Hr]; lia.
Qed.

(* ---------- zstd's copies ---------- *)

(* ZSTD_overlapCopy8 for offsets below 8 leaves the source at distance off - dec32 + dec64 >= 8, not
   before where it started *)
Lemma xkd_dec : forall off, 1 <= off < 8 ->
  0 <= xdec32 off <= 4 /\ 8 <= off - xdec32 off + xdec64 off /\ xdec64 off - xdec32 off <= 8.
Proof.
  intros off H.
  assert (off = 1 \/ off = 2 \/ off = 3 \/ off = 4 \/ off = 5 \/ off = 6 \/ off = 7) as E by lia.
  unfold xdec32, xdec64.
  destruct E as [->|[->|[->|[->|[->|[->| ->]]]]]]; cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add nth]; lia.
Qed.

(* ZSTD_overlapCopy8 of a match at distance off, [ip, op) written: 8 bytes stored, the new source at
   distance >= 8 with the cells between it and the new op written *)
Lemma xkd_ov8 : forall src m op ip off, 0 <= ip -> 1 <= off -> op - ip = off -> xwr_rng m ip op ->
  exists m' ip1, xm_ov8 src m op ip off = Some (m', op + 8, ip1) /\ xm_le m m' /\ ip <= ip1 /\
    8 <= op + 8 - ip1 /\ xwr_rng m' ip1 (op + 8).
Proof.
  intros src m op ip off Hip Hoff Hd R. unfold xm_ov8.
  destruct (Z.ltb_spec off 8) as [Hlt|Hge].
  - destruct (xkd_dec off) as [D1 [D2 D3]]; [lia|].
    destruct (xkd_fwd_back src 4 m op ip) as [m1 [F1 [L1 R1]]]; [lia|lia|exact R|].
    rewrite F1. cbv zeta.
    destruct (xkd_fwd_back src 4 m1 (op + 4) (ip + xdec32 off)) as [m2 [F2 [L2 R2]]]; [lia|lia| |].
    + intros j Hj. destruct (Z.ltb_spec j op); [apply (proj1 L1), R; lia|apply R1; lia].
    + rewrite F2. eexists _, _. split; [reflexivity|]. split; [eapply xm_le_trans; eauto|].
      split; [lia|]. split; [lia|].
      intros j Hj. destruct (Z.ltb_spec j op); [apply (proj1 L2), (proj1 L1), R; lia|].
      destruct (Z.ltb_spec j (op + 4)); [apply (proj1 L2), R1; lia|apply R2; lia].
  - destruct (xkd_fwd_back src 8 m op ip) as [m1 [F1 [L1 R1]]]; [lia|lia|exact R|].
    rewrite F1. eexists _, _. split; [reflexivity|]. split; [exact L1|]. split; [lia|]. split; [lia|].
    intros j Hj. destruct (Z.ltb_spec j op); [apply (proj1 L1), R; lia|apply R1; lia].
Qed.

(* ZSTD_safecopy of literals (ZSTD_no_overlap): reads at most len + 31 bytes of its source *)
Lemma xkd_sc_rd : forall src m op w rs ip len, 0 <= op -> 0 <= len -> xrd_rng src m rs ip (ip + len + 31) ->
  exists m', xm_safecopy src m op w rs ip len false = Some m' /\ xm_le m m' /\ xwr_rng m' op (op + len).
Proof.
  intros src m op w rs ip len Hop Hl R. unfold xm_safecopy. cbv zeta.
  destruct (Z.ltb_spec len 8).
  - destruct (xkd_fwd_rd src rs (Z.to_nat len) m op ip Hop) as [m' [F [L W]]];
      [rewrite Z2Nat.id by lia; eapply xrd_rng_sub; [| |exact R]; lia|].
    rewrite Z2Nat.id in W by lia. eauto.
  - cbv beta iota. destruct (Z.geb_spec (w - (op + len)) 0).
    + apply xkd_wild_rd; [lia|lia|exact R].
    + destruct (Z.geb_spec (w - op) 0).
      * destruct (xkd_wild_rd src rs m op ip (w - op)) as [m1 [Wd [L1 W1]]];
          [lia|lia|eapply xrd_rng_sub; [| |exact R]; lia|].
        cbv beta iota. rewrite Wd.
        destruct (xkd_fwd_rd src rs (Z.to_nat (op + len - w)) m1 w (ip + (w - op))) as [m' [F [L W]]];
          [lia|rewrite Z2Nat.id by lia; eapply xrd_rng_le; [exact L1|]; eapply xrd_rng_sub; [| |exact R]; lia|].
        rewrite F. exists m'. split; [reflexivity|]. split; [eapply xm_le_trans; eauto|].
        rewrite Z2Nat.id in W by lia. intros j Hj.
        destruct (Z.ltb_spec j w); [apply (proj1 L), W1; lia|apply W; lia].
      * cbv beta iota.
        destruct (xkd_fwd_rd src rs (Z.to_nat (op + len - op)) m op ip Hop) as [m' [F [L W]]];
          [rewrite Z2Nat.id by lia; eapply xrd_rng_sub; [| |exact R]; lia|].
        rewrite Z2Nat.id in W by lia. exists m'. split; [exact F|]. split; [exact L|].
        eapply xwr_rng_sub; [| |exact W]; lia.
Qed.

(* ZSTD_safecopy of a match (ZSTD_overlap_src_before_dst), [ip, op) written *)
Lemma xkd_sc_back : forall src m op w ip len, 0 <= ip -> 1 <= op - ip -> xwr_rng m ip op -> 0 <= len ->
  exists m', xm_safecopy src m op w R_dst ip len true = Some m' /\ xm_le m m' /\ xwr_rng m' op (op + len).
Proof.
  intros src m op w ip len Hip Hd R Hl. unfold xm_safecopy. cbv zeta.
  destruct (Z.ltb_spec len 8).
  - destruct (xkd_fwd_back src (Z.to_nat len) m op ip Hip Hd R) as [m' [F [L W]]].
    rewrite Z2Nat.id in W by lia. eauto.
  - destruct (xkd_ov8 src m op ip (op - ip)) as [m1 [ip1 [O [L1 [Hi1 [Hd1 W1]]]]]]; [lia|lia|lia|exact R|].
    rewrite O. cbv beta iota.
    destruct (Z.geb_spec (w - (op + len)) 0).
    + destruct (xkd_wild_back src m1 (op + 8) ip1 (len - 8) true) as [m' [Wd [L W]]]; [lia|lia|exact W1|lia|].
      exists m'. split; [exact Wd|]. split; [eapply xm_le_trans; eauto|].
      intros j Hj. destruct (Z.ltb_spec j (op + 8)); [apply (proj1 L), W1; lia|apply W; lia].
    + destruct (Z.geb_spec (w - (op + 8)) 0).
      * destruct (xkd_wild_back src m1 (op + 8) ip1 (w - (op + 8)) true) as [m2 [Wd [L2 W2]]];
          [lia|lia|exact W1|lia|].
        cbv beta iota. rewrite Wd.
        destruct (xkd_fwd_back src (Z.to_nat (op + len - w)) m2 w (ip1 + (w - (op + 8)))) as [m' [F [L W]]];
          [lia|lia| |].
        { intros j Hj. destruct (Z.ltb_spec j (op + 8)); [apply (proj1 L2), W1; lia|apply W2; lia]. }
        rewrite F. exists m'. split; [reflexivity|].
        split; [eapply xm_le_trans; [exact L1|]; eapply xm_le_trans; eauto|].
        rewrite Z2Nat.id in W by lia. intros j Hj.
        destruct (Z.ltb_spec j (op + 8)); [apply (proj1 L), (proj1 L2), W1; lia|].
        destruct (Z.ltb_spec j w); [apply (proj1 L), W2; lia|apply W; lia].
      * cbv beta iota.
        destruct (xkd_fwd_back src (Z.to_nat (op + len - (op + 8))) m1 (op + 8) ip1) as [m' [F [L W]]];
          [lia|lia|exact W1|].
        rewrite F. exists m'. split; [reflexivity|]. split; [eapply xm_le_trans; eauto|].
        rewrite Z2Nat.id in W by lia. intros j Hj.
        destruct (Z.ltb_spec j (op + 8)); [apply (proj1 L), W1; lia|apply W; lia].
Qed.

(* the prefix part of a match at distance off, [mt, op) written *)
Lemma xkd_prefix : forall e m op mt ml off wo, 0 <= mt -> 1 <= off -> op - mt = off -> xwr_rng m mt op ->
  0 <= ml ->
  exists m', xm_prefix e m op mt ml off wo = Some m' /\ xm_le m m' /\ xwr_rng m' op (op + ml).
Proof.
  intros e m op mt ml off wo Hmt Hoff Hd R Hml. unfold xm_prefix. destruct wo as [w|].
  - apply xkd_sc_back; [lia|lia|exact R|lia].
  - destruct (Z.geb_spec off 16).
    + apply (xkd_wild_back _ _ _ _ _ false); [lia|lia|exact R|lia].
    + destruct (xkd_ov8 (xe_src e) m op mt off) as [m1 [ip1 [O [L1 [Hi1 [Hd1 W1]]]]]]; [lia|lia|lia|exact R|].
      rewrite O. destruct (Z.gtb_spec ml 8).
      * destruct (xkd_wild_back (xe_src e) m1 (op + 8) ip1 (ml - 8) true) as [m' [Wd [L W]]];
          [lia|lia|exact W1|lia|].
        exists m'. split; [exact Wd|]. split; [eapply xm_le_trans; eauto|].
        intros j Hj. destruct (Z.ltb_spec j (op + 8)); [apply (proj1 L), W1; lia|apply W; lia].
      * exists m1. split; [reflexivity|]. split; [exact L1|]. eapply xwr_rng_sub; [| |exact W1]; lia.
Qed.

(* the match at oLitEnd, the history written: it fails exactly on an offset beyond virtualStart *)
Lemma xkd_match : forall e m oLitEnd ml off wo,
  0 <= xe_ps e <= oLitEnd -> xe_vs e <= xe_ps e -> 0 <= xe_de e - (xe_ps e - xe_vs e) ->
  xwr_rng m (xe_ps e) oLitEnd -> xwr_rng m (xe_de e - (xe_ps e - xe_vs e)) (xe_de e) -> 1 <= ml -> 1 <= off ->
  match xm_match e m oLitEnd ml off wo with
  | None => oLitEnd - xe_vs e < off
  | Some m' => off <= oLitEnd - xe_vs e /\ xm_le m m' /\ xwr_rng m' oLitEnd (oLitEnd + ml)
  end.
Proof.
  intros e m oLitEnd ml off wo Hps Hvs Hde Rh Rd Hml Hoff. unfold xm_match. cbv zeta.
  destruct (Z.gtb_spec off (oLitEnd - xe_ps e)).
  - destruct (Z.gtb_spec off (oLitEnd - xe_vs e)); [lia|].
    destruct (Z.geb_spec (xe_de e - (xe_de e + (oLitEnd - off - xe_ps e))) ml).
    + destruct (xkd_move (xe_src e) R_dst (Z.to_nat ml) m oLitEnd (xe_de e + (oLitEnd - off - xe_ps e)))
        as [m' [Mv [L W]]]; [lia|rewrite Z2Nat.id by lia; intros j Hj; apply Rd; lia|].
      rewrite Mv. rewrite Z2Nat.id in W by lia. split; [lia|]. split; [exact L|exact W].
    + destruct (xkd_move (xe_src e) R_dst (Z.to_nat (xe_de e - (xe_de e + (oLitEnd - off - xe_ps e)))) m oLitEnd
        (xe_de e + (oLitEnd - off - xe_ps e))) as [m1 [Mv [L1 W1]]];
        [lia|rewrite Z2Nat.id by lia; intros j Hj; apply Rd; lia|].
      rewrite Mv. rewrite Z2Nat.id in W1 by lia.
      destruct (xkd_prefix e m1 (oLitEnd + (xe_de e - (xe_de e + (oLitEnd - off - xe_ps e)))) (xe_ps e)
        (ml - (xe_de e - (xe_de e + (oLitEnd - off - xe_ps e)))) off wo) as [m' [P [L W]]];
        [lia|lia|lia| |lia|].
      { intros j Hj. destruct (Z.ltb_spec j oLitEnd); [apply (proj1 L1), Rh; lia|apply W1; lia]. }
      rewrite P. split; [lia|]. split; [eapply xm_le_trans; eauto|].
      intros j Hj. destruct (Z.ltb_spec j (oLitEnd + (xe_de e - (xe_de e + (oLitEnd - off - xe_ps e))))).
      * apply (proj1 L), W1; lia.
      * apply W; lia.
  - destruct (xkd_prefix e m oLitEnd (oLitEnd - off) ml off wo) as [m' [P [L W]]];
      [lia|lia|lia|eapply xwr_rng_sub; [| |exact Rh]; lia|lia|].
    rewrite P. split; [lia|]. split; [exact L|exact W].
Qed.

(* k bytes forward: the source cells read before being overwritten are written *)
Lemma xm_fwd_def (src: list Z) (k: nat) (m: xmem) (d: Z) (rs: xreg) (s: Z) :
  0 <= d -> 0 <= s ->
  match rs with
  | R_dst => xwr_rng m s (if s <? d then Z.min d (s + Z.of_nat k) else s + Z.of_nat k)
  | R_src => s + Z.of_nat k <= Zlength src
  | R_lxb => s + Z.of_nat k <= Zlength (xm_lxb m)
  end ->
  exists m', xm_fwd src k m R_dst d rs s = Some m' /\ xm_le m m' /\ xwr_rng m' d (d + Z.of_nat k).
Proof.
  intros Hd Hs Hr. apply xkd_fwd; [exact Hd|]. intros i Hi. destruct rs; cbn in Hr |- *.
  - destruct (Z.ltb_spec s d).
    + destruct (Z.ltb_spec (s + i) d); [left; apply Hr; lia|right; split; [reflexivity|lia]].
    + left. apply Hr; lia.
  - left. lia.
  - left. lia.
Qed.

(* k bytes moved *)
Lemma xm_move_def (src: list Z) (k: nat) (m: xmem) (d: Z) (rs: xreg) (s: Z) :
  0 <= d -> 0 <= s ->
  match rs with
  | R_dst => xwr_rng m s (s + Z.of_nat k)
  | R_src => s + Z.of_nat k <= Zlength src
  | R_lxb => s + Z.of_nat k <= Zlength (xm_lxb m)
  end ->
  exists m', xm_move src k m R_dst d rs s = Some m' /\ xm_le m m' /\ xwr_rng m' d (d + Z.of_nat k).
Proof.
  intros Hd Hs Hr. apply xkd_move; [exact Hd|]. intros j Hj. destruct rs; cbn in Hr |- *; [apply Hr| |]; lia.
Qed.

(* ZSTD_safecopyDstBeforeSrc, source in the region *)
Lemma xm_sdbs_def (src: list Z) (m: xmem) (op ip len: Z) :
  0 <= op -> 0 <= ip -> 0 <= len -> xwr_rng m ip (ip + len) ->
  exists m', xm_sdbs src m op ip len = Some m' /\ xm_le m m' /\ xwr_rng m' op (op + len).
Proof.
  intros Hop Hip Hl R. unfold xm_sdbs. cbv zeta.
  destruct ((len <? 8) || (op - ip >? -8)) eqn:E.
  - destruct (xkd_fwd_rd src R_dst (Z.to_nat len) m op ip Hop) as [m' [F [L W]]];
      [rewrite Z2Nat.id by lia; exact R|].
    rewrite Z2Nat.id in W by lia. eauto.
  - destruct ((len >=? 32) && (op - ip <? -16)) eqn:E2.
    + apply andb_true_iff in E2. destruct E2 as [E2 E3]. apply Z.geb_le in E2.
      destruct (xkd_wild_rd src R_dst m op ip (len - 32)) as [m1 [Wd [L1 W1]]];
        [lia|lia|eapply xrd_rng_sub; [| |exact R]; lia|].
      cbv beta iota. rewrite Wd.
      destruct (xkd_fwd_rd src R_dst (Z.to_nat (op + len - (op + len - 32))) m1 (op + len - 32) (ip + len - 32))
        as [m' [F [L W]]];
        [lia|rewrite Z2Nat.id by lia; eapply xrd_rng_le; [exact L1|]; eapply xrd_rng_sub; [| |exact R]; lia|].
      rewrite F. exists m'. split; [reflexivity|]. split; [eapply xm_le_trans; eauto|].
      rewrite Z2Nat.id in W by lia. intros j Hj.
      destruct (Z.ltb_spec j (op + len - 32)); [apply (proj1 L), W1; lia|apply W; lia].
    + cbv beta iota.
      destruct (xkd_fwd_rd src R_dst (Z.to_nat (op + len - op)) m op ip Hop) as [m' [F [L W]]];
        [rewrite Z2Nat.id by lia; eapply xrd_rng_sub; [| |exact R]; lia|].
      rewrite Z2Nat.id in W by lia. exists m'. split; [exact F|]. split; [exact L|].
      eapply xwr_rng_sub; [| |exact W]; lia.
Qed.

(* the literals' cells are readable *)
Lemma xkd_xl : forall e m lr li llim, xl_ok e m lr li llim -> xrd_rng (xe_src e) m lr li (llim + 32).
Proof.
  intros e m lr li llim [H0 H]. unfold WILDCOPY_OVERLENGTH in H.
  intros j Hj. destruct lr; cbn in H |- *; [apply H| |]; lia.
Qed.

(* an executor after its literals [op, op + ll) are stored: the match decides; err is the C's error
   condition, reduced to the offset check *)
Lemma xkd_tail : forall e m m1 op li ll ml off wo (err: bool),
  xh_ok e m op -> 0 <= ll -> 1 <= ml -> 1 <= off -> xm_le m m1 -> xwr_rng m1 op (op + ll) ->
  err = (op + ll - xe_vs e <? off) ->
  match (match xm_match e m1 (op + ll) ml off wo with
         | Some m' => Some (m', op + ll + ml, li + ll) | None => None end) with
  | None => err = true
  | Some (m', op', li') => err = false /\ op' = op + ll + ml /\ li' = li + ll /\ xm_le m m' /\ xwr_rng m' op op'
  end.
Proof.
  intros e m m1 op li ll ml off wo err [Hps [Hvs [Hde [Rh Rd]]]] Hll Hml Hoff L1 W1 Herr.
  pose proof (xkd_match e m1 (op + ll) ml off wo) as M.
  destruct (xm_match e m1 (op + ll) ml off wo) as [m'|].
  - destruct M as [Ho [L W]]; [lia|lia|lia| |eapply xwr_rng_le; eauto|lia|lia|].
    { intros j Hj. destruct (Z.ltb_spec j op); [apply (proj1 L1), Rh; lia|apply W1; lia]. }
    subst err. split; [apply Z.ltb_ge; lia|]. split; [reflexivity|]. split; [reflexivity|].
    split; [eapply xm_le_trans; eauto|].
    intros j Hj. destruct (Z.ltb_spec j (op + ll)); [apply (proj1 L), W1; lia|apply W; lia].
  - assert (op + ll - xe_vs e < off) as Ho.
    { apply M; [lia|lia|lia| |eapply xwr_rng_le; eauto|lia|lia].
      intros j Hj. destruct (Z.ltb_spec j op); [apply (proj1 L1), Rh; lia|apply W1; lia]. }
    subst err. apply Z.ltb_lt. exact Ho.
Qed.

(* ZSTD_execSequence / ZSTD_execSequenceEnd *)
Lemma x_exec_def (e: xenv) (m: xmem) (op: Z) (lr: xreg) (li llim ll ml off: Z) :
  xh_ok e m op -> xl_ok e m lr li llim -> 0 <= ll -> 1 <= ml -> 1 <= off ->
  match x_exec e m op lr li llim ll ml off with
  | None => xexec_err e op li llim ll ml off = true
  | Some (m', op', li') =>
      xexec_err e op li llim ll ml off = false /\ op' = op + ll + ml /\ li' = li + ll /\
      xm_le m m' /\ xwr_rng m' op op'
  end.
Proof.
  intros Hh Hl Hll Hml Hoff. pose proof (xkd_xl e m lr li llim Hl) as R. destruct Hl as [Hli _].
  pose proof Hh as [Hps _].
  unfold x_exec, XWILDCOPY. cbv zeta.
  destruct ((llim - li <? ll) || (xe_oend e - 32 - op <? ll + ml)) eqn:Eslow.
  - destruct (Z.gtb_spec (ll + ml) (xe_oend e - op)).
    { unfold xexec_err. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
    destruct (Z.gtb_spec ll (llim - li)).
    { unfold xexec_err. rewrite (proj2 (Z.ltb_lt (llim - li) ll)) by lia. rewrite orb_true_r. reflexivity. }
    destruct (xkd_sc_rd (xe_src e) m op (xe_oend e - 32) lr li ll) as [m1 [Sc [L1 W1]]];
      [lia|lia|eapply xrd_rng_sub; [| |exact R]; lia|].
    rewrite Sc. apply xkd_tail; [exact Hh|lia|lia|lia|exact L1|exact W1|].
    unfold xexec_err. rewrite (proj2 (Z.ltb_ge (xe_oend e - op) (ll + ml))) by lia.
    rewrite (proj2 (Z.ltb_ge (llim - li) ll)) by lia. reflexivity.
  - apply orb_false_iff in Eslow. destruct Eslow as [E1 E2]. apply Z.ltb_ge in E1, E2.
    destruct (xkd_move (xe_src e) lr 16 m op li) as [m1 [Mv [L1 W1]]];
      [lia|eapply xrd_rng_sub; [| |exact R]; lia|].
    rewrite Mv.
    assert (Herr: xexec_err e op li llim ll ml off = (op + ll - xe_vs e <? off)).
    { unfold xexec_err. rewrite (proj2 (Z.ltb_ge (xe_oend e - op) (ll + ml))) by lia.
      rewrite (proj2 (Z.ltb_ge (llim - li) ll)) by lia. reflexivity. }
    destruct (Z.gtb_spec ll 16).
    + destruct (xkd_wild_rd (xe_src e) lr m1 (op + 16) (li + 16) (ll - 16)) as [m2 [Wd [L2 W2]]];
        [lia|lia|eapply xrd_rng_le; [exact L1|]; eapply xrd_rng_sub; [| |exact R]; lia|].
      rewrite Wd. apply xkd_tail; [exact Hh|lia|lia|lia|eapply xm_le_trans; eauto| |exact Herr].
      intros j Hj. destruct (Z.ltb_spec j (op + 16)); [apply (proj1 L2), W1; lia|apply W2; lia].
    + apply xkd_tail; [exact Hh|lia|lia|lia|exact L1| |exact Herr].
      eapply xwr_rng_sub; [| |exact W1]; lia.
Qed.

(* ZSTD_execSequenceSplitLitBuffer / ZSTD_execSequenceEndSplitLitBuffer: the loop has checked
   li + ll <= llim; the literals' part in dst ends 32 bytes before oend *)
Lemma x_exec_split_def (e: xenv) (m: xmem) (op li llim ll ml off: Z) :
  xh_ok e m op -> xl_ok e m R_dst li llim -> li + ll <= llim -> llim + WILDCOPY_OVERLENGTH <= xe_oend e ->
  0 <= ll -> 1 <= ml -> 1 <= off ->
  match x_exec_split e m op li llim ll ml off with
  | None => xsplit_err e op li ll ml off = true
  | Some (m', op', li') =>
      xsplit_err e op li ll ml off = false /\ op' = op + ll + ml /\ li' = li + ll /\
      xm_le m m' /\ xwr_rng m' op op'
  end.
Proof.
  intros Hh Hl Hlim Hoe Hll Hml Hoff. pose proof (xkd_xl e m R_dst li llim Hl) as R. destruct Hl as [Hli Hl].
  cbn in R. pose proof Hh as [Hps _].
  unfold WILDCOPY_OVERLENGTH in Hoe. unfold x_exec_split, XWILDCOPY. cbv zeta.
  destruct ((llim - li <? ll) || (li + ll - 32 - op <? ll + ml)) eqn:Eslow.
  - destruct (Z.gtb_spec (ll + ml) (xe_oend e - op)).
    { unfold xsplit_err. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
    destruct (Z.gtb_spec ll (llim - li)); [lia|].
    destruct ((op >? li) && (op <? li + ll)) eqn:Ein.
    { unfold xsplit_err. apply andb_true_iff in Ein. destruct Ein as [E1 E2]. apply Z.gtb_lt in E1.
      rewrite (proj2 (Z.ltb_lt li op)) by lia. rewrite E2. cbn [andb]. rewrite orb_true_r. reflexivity. }
    destruct (xm_sdbs_def (xe_src e) m op li ll) as [m1 [Sd [L1 W1]]];
      [lia|lia|lia|intros j Hj; apply R; lia|].
    rewrite Sd. apply xkd_tail; [exact Hh|lia|lia|lia|exact L1|exact W1|].
    unfold xsplit_err. rewrite (proj2 (Z.ltb_ge (xe_oend e - op) (ll + ml))) by lia.
    replace ((li <? op) && (op <? li + ll)) with false; [reflexivity|].
    rewrite <- Ein. f_equal. destruct (Z.ltb_spec li op), (Z.gtb_spec op li); reflexivity || lia.
  - apply orb_false_iff in Eslow. destruct Eslow as [E1 E2]. apply Z.ltb_ge in E1, E2.
    destruct (xkd_move (xe_src e) R_dst 16 m op li) as [m1 [Mv [L1 W1]]];
      [lia|intros j Hj; apply R; lia|].
    rewrite Mv.
    assert (Herr: xsplit_err e op li ll ml off = (op + ll - xe_vs e <? off)).
    { unfold xsplit_err. rewrite (proj2 (Z.ltb_ge (xe_oend e - op) (ll + ml))) by lia.
      rewrite (proj2 (Z.ltb_ge li op)) by lia. reflexivity. }
    destruct (Z.gtb_spec ll 16).
    + destruct (xkd_wild_rd (xe_src e) R_dst m1 (op + 16) (li + 16) (ll - 16)) as [m2 [Wd [L2 W2]]];
        [lia|lia|eapply xrd_rng_le; [exact L1|]; intros j Hj; apply R; lia|].
      rewrite Wd. apply xkd_tail; [exact Hh|lia|lia|lia|eapply xm_le_trans; eauto| |exact Herr].
      intros j Hj. destruct (Z.ltb_spec j (op + 16)); [apply (proj1 L2), W1; lia|apply W2; lia].
    + apply xkd_tail; [exact Hh|lia|lia|lia|exact L1| |exact Herr].
      eapply xwr_rng_sub; [| |exact W1]; lia.
Qed.
