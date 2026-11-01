(* CORE of SEQ: the plain-Coq side of the FSE sequence machine
   (ZSTD_decodeSequence) shared by DEC (the bodies) and LOOP (the loop invariants).

   - dseq_one: one step of Block.decode_seqs (the sequence, the next states, the position); `last` = no
     state update (C: isLastSeq);
   - c_offset: the C offset resolution of ZSTD_decodeSequence on size_t prevOffset (total; an invalid
     repeat gives (size_t)-1), = Block.resolve_offset whenever the model resolves the offset;
   - bs_ready: the bit container holds enough bits for one whole ZSTD_decodeSequence (64-bit: <= 56 bits
     read between reloads), or the stream is at its last container (lo = 0). *)
Require Export Zstd.proof.dec.B.blk.BlkSeqCOPY.
Require Import Coq.micromega.Lia.
Require Export Zstd.proof.model.ExCSeq.
Local Open Scope Z_scope.

(* ---------- one decode step ----------
   dseq_one (one step of Block.decode_seqs), SIZE_MAX and c_offset (the C offset resolution) are plain Coq in
   model/ExCSeq.v, exported by this file, which the exact block model shares. *)

(* decode_seqs unfolded by one step *)
Lemma decode_seqs_S (tLL tOF tML: fse_table) (V: list Z) (k: nat) (sLL sOF sML pos: Z) :
  decode_seqs tLL tOF tML V (S k) sLL sOF sML pos =
  match dseq_one tLL tOF tML V (Nat.eqb k 0) sLL sOF sML pos with
  | None => None
  | Some (sq, (a, b, c), p) =>
      match k with
      | O => Some ([sq], p)
      | _ => match decode_seqs tLL tOF tML V k a b c p with
             | Some (l, p') => Some (sq :: l, p')
             | None => None
             end
      end
  end.
Proof.
  simpl decode_seqs at 1. unfold dseq_one.
  destruct (rd V pos _) as [[eOF p1]|]; [|reflexivity].
  destruct (rd V p1 _) as [[eML p2]|]; [|reflexivity].
  destruct (rd V p2 _) as [[eLL p3]|]; [|reflexivity].
  destruct k as [|k']; [reflexivity|]. simpl Nat.eqb. cbv iota.
  destruct (rd V p3 _) as [[uLL p4]|]; [|reflexivity].
  destruct (rd V p4 _) as [[uML p5]|]; [|reflexivity].
  destruct (rd V p5 _) as [[uOF p6]|]; reflexivity.
Qed.

(* ---------- the C offset resolution ---------- *)
(* repeat offsets as size_t values: never 0 *)
Definition rep64_ok (rep: Z * Z * Z) : Prop :=
  let '(r1, r2, r3) := rep in 1 <= r1 <= SIZE_MAX /\ 1 <= r2 <= SIZE_MAX /\ 1 <= r3 <= SIZE_MAX.

Lemma c_offset_ok (rep: Z * Z * Z) (ll ov: Z) :
  rep64_ok rep -> 1 <= ov < 2 ^ 32 ->
  1 <= fst (c_offset rep ll ov) <= SIZE_MAX /\ rep64_ok (snd (c_offset rep ll ov)).
Proof.
  destruct rep as [[r1 r2] r3]. unfold rep64_ok, c_offset, SIZE_MAX. intros (H1 & H2 & H3) Hov.
  destruct (ov >? 3) eqn:E; [apply Z.gtb_lt in E; simpl; lia|].
  destruct ((if ll =? 0 then ov + 1 else ov) =? 1); [simpl; lia|].
  destruct ((if ll =? 0 then ov + 1 else ov) =? 2); [simpl; lia|].
  destruct ((if ll =? 0 then ov + 1 else ov) =? 3); [simpl; lia|].
  cbv [fst snd]. destruct ((r1 - 1) mod 2 ^ 64 =? 0) eqn:E0; [lia|].
  apply Z.eqb_neq in E0. pose proof (Z.mod_pos_bound (r1 - 1) (2 ^ 64) ltac:(lia)). lia.
Qed.

(* the model's offset resolution is the C's when it succeeds *)
Lemma c_offset_resolve (rep: Z * Z * Z) (ll ov off: Z) (rep': Z * Z * Z) :
  rep64_ok rep -> resolve_offset rep ll ov = Some (off, rep') -> c_offset rep ll ov = (off, rep').
Proof.
  destruct rep as [[r1 r2] r3]. unfold rep64_ok, resolve_offset, c_offset, SIZE_MAX. intros (H1 & H2 & H3) H.
  destruct (ov >? 3); [inversion H; reflexivity|].
  destruct ((if ll =? 0 then ov + 1 else ov) =? 1); [inversion H; reflexivity|].
  destruct ((if ll =? 0 then ov + 1 else ov) =? 2); [inversion H; reflexivity|].
  destruct ((if ll =? 0 then ov + 1 else ov) =? 3); [inversion H; reflexivity|].
  destruct (r1 - 1 <=? 0) eqn:E; [discriminate|]. apply Z.leb_gt in E. inversion H; subst.
  rewrite Z.mod_small by lia. destruct (r1 - 1 =? 0) eqn:E2; [apply Z.eqb_eq in E2; lia|]. reflexivity.
Qed.

(* ... and an offset the model rejects becomes (size_t)-1 in C *)
Lemma c_offset_none (rep: Z * Z * Z) (ll ov: Z) :
  rep64_ok rep -> resolve_offset rep ll ov = None -> fst (c_offset rep ll ov) = SIZE_MAX.
Proof.
  destruct rep as [[r1 r2] r3]. unfold rep64_ok, resolve_offset, c_offset, SIZE_MAX. intros (H1 & H2 & H3) H.
  destruct (ov >? 3); [discriminate|].
  destruct ((if ll =? 0 then ov + 1 else ov) =? 1); [discriminate|].
  destruct ((if ll =? 0 then ov + 1 else ov) =? 2); [discriminate|].
  destruct ((if ll =? 0 then ov + 1 else ov) =? 3); [discriminate|].
  destruct (r1 - 1 <=? 0) eqn:E; [|discriminate]. apply Z.leb_le in E.
  replace (r1 - 1) with 0 by lia. reflexivity.
Qed.

(* ---------- the bit container ---------- *)
(* bitsConsumed of the C state (pos, lo) *)
Definition bcons (pos lo: Z) : Z := lo + 64 - pos.

(* enough bits for a whole ZSTD_decodeSequence (<= 56 between reloads), or the last container *)
Definition bs_ready (pos lo: Z) : Prop := lo = 0 \/ lo + 56 <= pos.

(* a reload from a non-overflowed state makes the container ready *)
Lemma bs_reload_ready (pos lo: Z) :
  0 <= lo -> lo mod 8 = 0 -> lo <= pos -> bs_ready pos (snd (bs_reload pos lo)).
Proof.
  intros H0 H8 H. unfold bs_ready, bs_reload.
  destruct (pos <? lo) eqn:E; [apply Z.ltb_lt in E; lia|].
  assert (Hk: 8 * (lo / 8) = lo) by (pose proof (Z.div_mod lo 8 ltac:(lia)); lia).
  assert (Hnb: 8 * ((lo + 64 - pos) / 8) <= lo + 64 - pos /\ lo + 64 - pos < 8 * ((lo + 64 - pos) / 8) + 8).
  { pose proof (Z.div_mod (lo + 64 - pos) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (lo + 64 - pos) 8 ltac:(lia)). lia. }
  destruct (8 <=? lo / 8) eqn:E1; [cbn [snd]; right; lia|].
  destruct (lo / 8 =? 0) eqn:E2; [apply Z.eqb_eq in E2; cbn [snd]; left; lia|].
  destruct (lo / 8 <? (lo + 64 - pos) / 8) eqn:E3; [cbn [snd]; left; reflexivity|].
  cbn [snd]; right; lia.
Qed.

(* reloads never move the window up *)
Lemma bs_reload_lo (pos lo: Z) : 0 <= lo -> pos <= lo + 64 -> 0 <= snd (bs_reload pos lo) <= lo.
Proof.
  intros H0 H1. unfold bs_reload.
  assert (Hnb: 0 <= (lo + 64 - pos) / 8) by (apply Z.div_pos; lia).
  assert (Hle: 8 * ((lo + 64 - pos) / 8) <= lo + 64 - pos) by (apply Z.mul_div_le; lia).
  destruct (pos <? lo) eqn:E; [cbn [snd]; lia|].
  apply Z.ltb_ge in E.
  destruct (8 <=? lo / 8) eqn:E1.
  - apply Z.leb_le in E1. cbn [snd].
    assert (8 * 8 <= 8 * (lo / 8)) by lia. pose proof (Z.mul_div_le lo 8 ltac:(lia)).
    assert ((lo + 64 - pos) / 8 <= 8) by (apply Z.div_le_upper_bound; lia). lia.
  - destruct (lo / 8 =? 0); [cbn [snd]; lia|].
    destruct (lo / 8 <? (lo + 64 - pos) / 8) eqn:E3; [cbn [snd]; lia|].
    apply Z.ltb_ge in E3. cbn [snd]. pose proof (Z.mul_div_le lo 8 ltac:(lia)). lia.
Qed.

(* the state right after BIT_initDStream is ready *)
Lemma bs_init_ready (s: list Z) :
  bs_wf s = true -> bytes_ok s ->
  bs_ready (bs_total s) (8 * Z.max 0 (Zlength s - 8)).
Proof.
  intros Hwf Hb. unfold bs_ready, bs_total.
  rewrite Zlength_correct.
  destruct (Z.max_spec 0 (Z.of_nat (length s) - 8)) as [[Hm Hmx]|[Hm Hmx]]; rewrite Hmx.
  - right. assert (0 <= highbit (last s 0)).
    { unfold highbit. first [apply Z.log2_nonneg | destruct (last s 0 >? 0); [apply Z.log2_nonneg | lia]]. }
    lia.
  - left; lia.
Qed.

