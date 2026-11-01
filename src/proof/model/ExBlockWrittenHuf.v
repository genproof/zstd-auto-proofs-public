(* The exact Huffman literals decoding (ExHuf.x_lits_huf) returns at most litSize literals.  Every loop of
   HUF_decodeStreamX1/X2 runs only while the bytes left exceed what its body emits, its last steps emit at
   most what is left, and the 4-stream decoders check (or bound by olimit) each segment.

   The block model needs it where the literals of a split literal buffer are decoded at dst + ews - |lits|
   (ExBlock.x_lits_store): with |lits| <= litSize <= ews, they lie at or after the block's start.  Plain
   Coq. *)
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Require Import Zstd.proof.model.Bytes Zstd.proof.model.ExHuf.
Local Open Scope Z_scope.

Local Ltac xw_split :=
  repeat match goal with
  | H: context [match ?e with pair _ _ => _ end] |- _ => let E := fresh "E" in destruct e eqn:E
  | |- context [match ?e with pair _ _ => _ end] => let E := fresh "E" in destruct e eqn:E
  end.

Local Lemma xw_zlen_app (a b: list Z) : Zlength (a ++ b) = Zlength a + Zlength b.
Proof. rewrite !Zlength_correct, app_length. lia. Qed.

Local Lemma xw_zlen_nn (a: list Z) : 0 <= Zlength a.
Proof. rewrite Zlength_correct. lia. Qed.

(* ---------- X1 ---------- *)

(* k symbols without reload are k bytes *)
Lemma xh_x1_n_len (t: xhuf) (k: nat) : forall d l d',
  xh_x1_n t d k = (l, d') -> Zlength l = Z.of_nat k.
Proof.
  induction k as [|k IH]; simpl; intros d l d' H.
  - inversion H; reflexivity.
  - xw_split. inversion H; subst. rewrite Zlength_cons. apply IH in E0. lia.
Qed.

(* The 4-symbol loop: what it emits plus what is left is what it started with, and it never goes below
   zero (it runs only while more than 3 are left). *)
Lemma xh_x1_loop4_inv (s: list Z) (t: xhuf) (fuel: nat) : forall d rem acc a d' r,
  0 <= rem -> xh_x1_loop4 fuel s t d rem acc = (a, d', r) ->
  Zlength a + r = Zlength acc + rem /\ 0 <= r.
Proof.
  induction fuel as [|f IH]; cbn [xh_x1_loop4 xh_x2_loopr xh_x2_loop1]; intros d rem acc a d' r Hr H.
  - inversion H; subst; lia.
  - xw_split. destruct (andb _ _) eqn:C.
    + apply Bool.andb_true_iff in C as [_ C]. apply Z.ltb_lt in C.
      xw_split. apply xh_x1_n_len in E0. simpl in E0.
      apply IH in H; [|lia]. rewrite xw_zlen_app in H. lia.
    + inversion H; subst; lia.
Qed.

(* HUF_decodeStreamX1 emits at most max 0 rem bytes *)
Lemma xh_x1_stream_len (t: xhuf) (s: list Z) (d: xbit) (rem: Z) :
  Zlength (fst (xh_x1_stream t s d rem)) <= Z.max 0 rem.
Proof.
  unfold xh_x1_stream. destruct (3 <? rem) eqn:C.
  - apply Z.ltb_lt in C. xw_split. simpl.
    apply xh_x1_loop4_inv in E; [|lia].
    match goal with H: xh_x1_n _ _ _ = _ |- _ => apply xh_x1_n_len in H; rewrite xw_zlen_app, H end.
    rewrite Z2Nat.id by lia. simpl in E. lia.
  - xw_split. simpl.
    match goal with H: (_, _, _) = (_, _, _) |- _ => inversion H; subst end.
    match goal with H: xh_x1_n _ _ _ = _ |- _ => apply xh_x1_n_len in H; rewrite xw_zlen_app, H end.
    simpl. lia.
Qed.

(* ---------- X2 ---------- *)

(* one decode emits at most 2 bytes *)
Lemma xh_x2_sym_len (t: xhuf) (d: xbit) : Zlength (fst (xh_x2_sym t d)) <= 2.
Proof.
  unfold xh_x2_sym. xw_split. simpl. rewrite Zlength_correct, firstn_length. simpl. lia.
Qed.

(* k decodes without reload emit at most 2k bytes *)
Lemma xh_x2_n_len (t: xhuf) (k: nat) : forall d l d',
  xh_x2_n t d k = (l, d') -> Zlength l <= 2 * Z.of_nat k.
Proof.
  induction k as [|k IH]; simpl; intros d l d' H.
  - inversion H; subst; reflexivity.
  - xw_split. inversion H; subst. rewrite xw_zlen_app.
    pose proof (xh_x2_sym_len t d) as S. rewrite E in S. simpl in S. apply IH in E0. lia.
Qed.

(* A loop of HUF_decodeStreamX2 with reloads, whose test guarantees room for its k decodes: it keeps
   what it emitted plus what is left constant and never goes below zero. *)
Lemma xh_x2_loopr_inv (s: list Z) (t: xhuf) (k: nat) (cond: Z -> bool)
    (Hc: forall r, cond r = true -> 2 * Z.of_nat k <= r) (fuel: nat) : forall d rem acc a d' r,
  0 <= rem -> xh_x2_loopr fuel s t k cond d rem acc = (a, d', r) ->
  Zlength a + r = Zlength acc + rem /\ 0 <= r.
Proof.
  induction fuel as [|f IH]; cbn [xh_x1_loop4 xh_x2_loopr xh_x2_loop1]; intros d rem acc a d' r Hr H.
  - inversion H; subst; lia.
  - xw_split. destruct (andb _ _) eqn:C.
    + apply Bool.andb_true_iff in C as [_ C]. apply Hc in C.
      xw_split. pose proof (xw_zlen_nn l). apply xh_x2_n_len in E0.
      apply IH in H; [|lia]. rewrite xw_zlen_app in H. lia.
    + inversion H; subst; lia.
Qed.

(* the same for the loop without reload (one decode while at least 2 are left) *)
Lemma xh_x2_loop1_inv (t: xhuf) (fuel: nat) : forall d rem acc a d' r,
  0 <= rem -> xh_x2_loop1 fuel t d rem acc = (a, d', r) ->
  Zlength a + r = Zlength acc + rem /\ 0 <= r.
Proof.
  induction fuel as [|f IH]; cbn [xh_x1_loop4 xh_x2_loopr xh_x2_loop1]; intros d rem acc a d' r Hr H.
  - inversion H; subst; lia.
  - destruct (2 <=? rem) eqn:C.
    + apply Z.leb_le in C. xw_split. pose proof (xw_zlen_nn l).
      pose proof (xh_x2_sym_len t d) as S. rewrite E in S. simpl in S.
      apply IH in H; [|lia]. rewrite xw_zlen_app in H. lia.
    + inversion H; subst; lia.
Qed.

(* HUF_decodeStreamX2 emits at most max 0 rem bytes *)
Lemma xh_x2_stream_len (t: xhuf) (s: list Z) (d: xbit) (rem: Z) :
  Zlength (fst (xh_x2_stream t s d rem)) <= Z.max 0 rem.
Proof.
  unfold xh_x2_stream.
  set (fuel := (Z.to_nat rem + 1)%nat).
  assert (S1: forall a d1 r1,
    (if 8 <=? rem then
       if xh_log t <=? 11 then xh_x2_loopr fuel s t 5 (fun r => 9 <? r) d rem nil
       else xh_x2_loopr fuel s t 4 (fun r => 7 <? r) d rem nil
     else let '(_, d) := xb_reload s d in (nil, d, rem)) = (a, d1, r1) ->
    Zlength a + r1 = rem /\ (0 <= r1 \/ Zlength a = 0)).
  { intros a d1 r1 H. destruct (8 <=? rem) eqn:C8.
    - apply Z.leb_le in C8. destruct (xh_log t <=? 11).
      + apply xh_x2_loopr_inv in H; [simpl in H; lia| |lia].
        intros r Hr. apply Z.ltb_lt in Hr. simpl. lia.
      + apply xh_x2_loopr_inv in H; [simpl in H; lia| |lia].
        intros r Hr. apply Z.ltb_lt in Hr. simpl. lia.
    - xw_split. inversion H; subst. split; [reflexivity|right; reflexivity]. }
  destruct (if 8 <=? rem then _ else _) as [[a d1] r1] eqn:E1 in |- *.
  apply S1 in E1. clear S1.
  assert (S2: forall b d2 r2,
    (if 2 <=? r1 then
       let '(b1, d, rem) := xh_x2_loopr fuel s t 1 (fun r => 2 <=? r) d1 r1 nil in
       let '(b2, d, rem) := xh_x2_loop1 fuel t d rem nil in (b1 ++ b2, d, rem)
     else (nil, d1, r1)) = (b, d2, r2) ->
    Zlength b + r2 = r1 /\ (0 <= r2 \/ (Zlength b = 0 /\ r2 = r1))).
  { intros b d2 r2 H. destruct (2 <=? r1) eqn:C2.
    - apply Z.leb_le in C2. xw_split. inversion H; subst.
      apply xh_x2_loopr_inv in E; [| |lia].
      2:{ intros r Hr. apply Z.leb_le in Hr. simpl. lia. }
      match goal with H: xh_x2_loop1 _ _ _ _ _ = _ |- _ => apply xh_x2_loop1_inv in H; [|lia] end.
      rewrite xw_zlen_app. simpl in *. lia.
    - inversion H; subst. rewrite Zlength_nil. lia. }
  destruct (if 2 <=? r1 then _ else _) as [[b d2] r2] eqn:E2 in |- *.
  apply S2 in E2. clear S2.
  destruct (if 0 <? r2 then xh_x2_last t d2 else (nil, d2)) as [c d3] eqn:E3.
  assert (Zlength c <= Z.max 0 r2).
  { destruct (0 <? r2) eqn:C3.
    - apply Z.ltb_lt in C3. unfold xh_x2_last in E3. xw_split. inversion E3; subst. rewrite Zlength_cons, Zlength_nil. lia.
    - inversion E3; subst. rewrite Zlength_nil. lia. }
  simpl. rewrite !xw_zlen_app. pose proof (xw_zlen_nn a). pose proof (xw_zlen_nn b). lia.
Qed.

(* ---------- one stream, four streams ---------- *)

Local Lemma xh_1stream_len (fin: list Z -> xbit -> Z -> list Z * xbit)
    (Hf: forall s d r, Zlength (fst (fin s d r)) <= Z.max 0 r) (src: list Z) (n: Z) (l: list Z) :
  xh_1stream fin src n = Some l -> Zlength l <= Z.max 0 n.
Proof.
  unfold xh_1stream. destruct (xb_init src) as [d|]; [|discriminate].
  pose proof (Hf src d n) as B. destruct (fin src d n) as [l' d']. simpl in B.
  destruct (xb_end d'); [|discriminate]. intros H; inversion H; subst; exact B.
Qed.

(* The main loop of the 4-stream decoders keeps the fourth stream's output within its segment: it runs
   only while |o4| < lim4 and each body adds at most B bytes, with lim4 + B <= M + 1. *)
Lemma xh_loop4s_o4 (dec4: xbit -> list Z * xbit) (B lim4 M: Z)
    (HB: forall d, Zlength (fst (dec4 d)) <= B) (Hl: lim4 + B <= M + 1) (s1 s2 s3 s4: list Z)
    (fuel: nat) : forall d1 d2 d3 d4 o1 o2 o3 o4 ds p1 p2 p3 p4,
  Zlength o4 <= M ->
  xh_loop4s fuel dec4 lim4 s1 s2 s3 s4 d1 d2 d3 d4 o1 o2 o3 o4 = (ds, (p1, p2, p3, p4)) ->
  Zlength p4 <= M.
Proof.
  induction fuel as [|f IH]; simpl; intros d1 d2 d3 d4 o1 o2 o3 o4 ds p1 p2 p3 p4 Ho H.
  - inversion H; subst; exact Ho.
  - destruct (Zlength o4 <? lim4) eqn:C; simpl in H; [|inversion H; subst; exact Ho].
    apply Z.ltb_lt in C. xw_split.
    pose proof (HB d4) as B4. rewrite E2 in B4. simpl in B4.
    destruct (andb _ _).
    + eapply IH; [|exact H]. rewrite xw_zlen_app. lia.
    + inversion H; subst. rewrite xw_zlen_app. lia.
Qed.

(* the 4-stream decoders emit at most max 0 n bytes *)
Lemma xh_4streams_len (dec4: xbit -> list Z * xbit) (slack: Z) (fin: list Z -> xbit -> Z -> list Z * xbit)
    (HB: forall d, Zlength (fst (dec4 d)) <= slack + 1)
    (Hf: forall s d r, Zlength (fst (fin s d r)) <= Z.max 0 r) (src: list Z) (n: Z) (l: list Z) :
  xh_4streams dec4 slack fin src n = Some l -> Zlength l <= Z.max 0 n.
Proof.
  unfold xh_4streams.
  destruct (Zlength src <? 10); [discriminate|].
  destruct (n <? 6) eqn:C6; [discriminate|]. apply Z.ltb_ge in C6.
  destruct (xh_split4 src) as [[[[s1 s2] s3] s4]|]; [|discriminate].
  set (seg := (n + 3) / 4).
  destruct (n <? 3 * seg) eqn:Cs; [discriminate|]. apply Z.ltb_ge in Cs.
  destruct (xb_init s1) as [d1|]; [|discriminate].
  destruct (xb_init s2) as [d2|]; [|discriminate].
  destruct (xb_init s3) as [d3|]; [|discriminate].
  destruct (xb_init s4) as [d4|]; [|discriminate].
  assert (Hseg: 0 <= seg) by (unfold seg; apply Z.div_pos; lia).
  destruct (if 8 <=? n - 3 * seg then _ else _) as [[[[e1 e2] e3] e4] [[[o1 o2] o3] o4]] eqn:EL.
  assert (H4: Zlength o4 <= n - 3 * seg).
  { destruct (8 <=? n - 3 * seg).
    - eapply xh_loop4s_o4; [exact HB| |rewrite Zlength_nil; lia|exact EL]. lia.
    - inversion EL; subst. rewrite Zlength_nil. lia. }
  destruct (seg <? Zlength o1) eqn:C1; [discriminate|]. apply Z.ltb_ge in C1.
  destruct (seg <? Zlength o2) eqn:C2; [discriminate|]. apply Z.ltb_ge in C2.
  destruct (seg <? Zlength o3) eqn:C3; [discriminate|]. apply Z.ltb_ge in C3.
  pose proof (Hf s1 e1 (seg - Zlength o1)) as T1. destruct (fin s1 e1 _) as [t1 f1]. cbn [fst] in T1.
  pose proof (Hf s2 e2 (seg - Zlength o2)) as T2. destruct (fin s2 e2 _) as [t2 f2]. cbn [fst] in T2.
  pose proof (Hf s3 e3 (seg - Zlength o3)) as T3. destruct (fin s3 e3 _) as [t3 f3]. cbn [fst] in T3.
  pose proof (Hf s4 e4 (n - 3 * seg - Zlength o4)) as T4. destruct (fin s4 e4 _) as [t4 f4]. cbn [fst] in T4.
  destruct (andb _ _); [|discriminate]. intros H; inversion H; subst.
  rewrite !xw_zlen_app. lia.
Qed.

(* the decoding of litSize symbols emits at most max 0 litSize bytes *)
Lemma x_huf_decode_len (t: xhuf) (single: bool) (streams: list Z) (litSize: Z) (l: list Z) :
  x_huf_decode t single streams litSize = Some l -> Zlength l <= Z.max 0 litSize.
Proof.
  unfold x_huf_decode. destruct (xh_x2 t), single.
  - apply xh_1stream_len. apply xh_x2_stream_len.
  - apply xh_4streams_len; [|apply xh_x2_stream_len].
    intros d. destruct (xh_x2_n t d 4) as [a d'] eqn:E. apply xh_x2_n_len in E. simpl in *. lia.
  - apply xh_1stream_len. apply xh_x1_stream_len.
  - apply xh_4streams_len; [|apply xh_x1_stream_len].
    intros d. destruct (xh_x1_n t d 4) as [a d'] eqn:E. apply xh_x1_n_len in E. simpl in *. lia.
Qed.

Lemma x_lits_huf_len : forall (hprev: option xhuf) (ty: Z) (single: bool) (cb: list Z) (litSize: Z)
    (l: list Z) (t: xhuf),
  x_lits_huf hprev ty single cb litSize = Some (l, t) -> Zlength l <= Z.max 0 litSize.
Proof.
  intros hprev ty single cb litSize l t. unfold x_lits_huf, xh_dctx.
  destruct (ty =? 2).
  - assert (D: forall x2 single', match x_huf_read x2 cb with
        | None => None
        | Some (t, h) =>
            if Zlength cb <=? h then None else
            match x_huf_decode t single' (skipn (Z.to_nat h) cb) litSize with
            | Some l => Some (l, t)
            | None => None
            end
        end = Some (l, t) -> Zlength l <= Z.max 0 litSize).
    { intros x2 single' H. destruct (x_huf_read x2 cb) as [[t' h]|]; [|discriminate].
      destruct (Zlength cb <=? h); [discriminate|].
      destruct (x_huf_decode t' single' _ litSize) eqn:E; [|discriminate].
      inversion H; subst. eapply x_huf_decode_len; exact E. }
    destruct single; [apply D|].
    destruct (litSize =? 0); [discriminate|]. destruct (Zlength cb =? 0); [discriminate|]. apply D.
  - destruct (ty =? 3); [|discriminate]. destruct hprev as [t'|]; [|discriminate].
    destruct (x_huf_decode t' single cb litSize) eqn:E; [|discriminate].
    intros H; inversion H; subst. eapply x_huf_decode_len; exact E.
Qed.
