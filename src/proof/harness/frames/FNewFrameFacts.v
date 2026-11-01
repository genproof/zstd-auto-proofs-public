(* The frame model (FModel.v) as new_frame builds it, one block at a time: the body of new_frame
   (FBodyNewFrame.v) appends a block per iteration of its loop, and decides only then whether that block is
   the last one.  These facts restate the block lists of FModel.v for lists built from the front (bl ++ [b]),
   with the Last_Block flag of the final block left open while the loop runs.  Plain Coq. *)
Require Import Zstd.proof.harness.frames.FModel.
Local Open Scope bool_scope.

(* the bytes a block writes after its Block_Header: one byte for RLE (the byte of an empty block, else the
   first byte of its part of d), its part of d for Raw *)
Definition nb_payload (d: list Z) (done: Z) (b: nf_block) : list Z :=
  if nb_rle b then [if nb_size b =? 0 then nb_byte b else byte_at d done]
  else slice d done (nb_size b).

(* what a block leaves in the data: its part of d, or for RLE its first byte repeated *)
Definition nb_content (d: list Z) (done: Z) (b: nf_block) : list Z :=
  if nb_rle b then repeat (byte_at d done) (Z.to_nat (nb_size b)) else slice d done (nb_size b).

(* the data the blocks bl take *)
Fixpoint nfb_size (bl: list nf_block) : Z :=
  match bl with [] => 0 | b :: bl' => nb_size b + nfb_size bl' end.

(* the bytes of the blocks bl; closed = false: no block is marked last (the loop is still running),
   closed = true: the final block is marked last (nf_blocks_bytes) *)
Fixpoint nfb_bytes (closed: bool) (d: list Z) (done: Z) (bl: list nf_block) : list Z :=
  match bl with
  | [] => []
  | b :: bl' => nb_header (closed && is_nil bl') b ++ nb_payload d done b ++
                nfb_bytes closed d (done + nb_size b) bl'
  end.

(* one block at offset done, under Block_Maximum_Size mb, for n bytes of data (the conditions of
   nf_blocks_ok on a single block) *)
Definition blk_ok (mb n done: Z) (b: nf_block) : Prop :=
  (done = n -> nb_size b = 0) /\
  (done < n -> 1 <= nb_size b <= Z.max 1 (Z.min (n - done) mb)) /\
  (nb_rle b = true -> 0 < mb) /\
  0 <= nb_byte b < 256.

(* blocks none of which is the last one: each one valid and not empty *)
Fixpoint nfb_open_ok (mb n done: Z) (bl: list nf_block) : Prop :=
  match bl with
  | [] => True
  | b :: bl' => blk_ok mb n done b /\ 0 < nb_size b /\ nfb_open_ok mb n (done + nb_size b) bl'
  end.

(* ---------- list helpers ---------- *)

(* a list with a block appended is not empty *)
Lemma nf_snoc_cons : forall (bl: list nf_block) b, exists x y, bl ++ [b] = x :: y.
Proof. intros [|x bl] b; eexists; eexists; reflexivity. Qed.

Lemma nf_is_nil_snoc : forall (bl: list nf_block) b, is_nil (bl ++ [b]) = false.
Proof. intros [|x bl] b; reflexivity. Qed.

Lemma nf_Zlength_le_bytes : forall k v, Zlength (le_bytes k v) = Z.of_nat k.
Proof.
  induction k; intros v; cbn [le_bytes]; [reflexivity|].
  rewrite Zlength_cons, IHk. lia.
Qed.

Lemma nf_Zlength_app : forall (l1 l2: list Z), Zlength (l1 ++ l2) = Zlength l1 + Zlength l2.
Proof. intros. rewrite !Zlength_correct, app_length. lia. Qed.

Lemma nf_Zlength_slice : forall d i k, 0 <= i -> 0 <= k -> i + k <= Zlength d -> Zlength (slice d i k) = k.
Proof.
  intros d i k Hi Hk H. unfold slice. rewrite Zlength_correct in *.
  rewrite firstn_length, skipn_length. lia.
Qed.

Lemma nf_bytes_ok_slice : forall d i k, bytes_ok d -> bytes_ok (slice d i k).
Proof.
  intros d i k H. unfold slice, bytes_ok in *.
  rewrite <- (firstn_skipn (Z.to_nat i) d) in H. apply Forall_app in H. destruct H as [_ H].
  rewrite <- (firstn_skipn (Z.to_nat k) (skipn (Z.to_nat i) d)) in H. apply Forall_app in H. tauto.
Qed.

(* the byte read at any position of a byte string is a byte (0 out of range) *)
Lemma nf_byte_at_ok : forall d i, bytes_ok d -> is_byte (byte_at d i).
Proof.
  intros d i H. unfold byte_at, bytes_ok in *.
  destruct (Nat.lt_ge_cases (Z.to_nat i) (length d)) as [Hl|Hl].
  - rewrite Forall_forall in H. apply H, nth_In, Hl.
  - rewrite nth_overflow by exact Hl. unfold is_byte. lia.
Qed.

(* ---------- the blocks, built from the front ---------- *)

Lemma nfb_bytes_closed : forall d done bl, nfb_bytes true d done bl = nf_blocks_bytes d done bl.
Proof.
  intros d done bl. revert done. induction bl as [|b bl IH]; intros done; [reflexivity|].
  cbn [nfb_bytes nf_blocks_bytes andb]. unfold nb_payload. rewrite IH. reflexivity.
Qed.

Lemma nfb_size_snoc : forall bl b, nfb_size (bl ++ [b]) = nfb_size bl + nb_size b.
Proof.
  induction bl as [|a bl IH]; intros b; cbn [app nfb_size]; [lia|]. rewrite IH. lia.
Qed.

(* appending a block, marked last (closed = true) or not *)
Lemma nfb_bytes_snoc : forall closed d done bl b,
  nfb_bytes closed d done (bl ++ [b]) =
  nfb_bytes false d done bl ++ nb_header closed b ++ nb_payload d (done + nfb_size bl) b.
Proof.
  intros closed d done bl. revert done. induction bl as [|a bl IH]; intros done b.
  - cbn [app nfb_bytes nfb_size is_nil]. rewrite Bool.andb_true_r, Z.add_0_r, !app_nil_r. reflexivity.
  - cbn [app nfb_bytes nfb_size]. rewrite nf_is_nil_snoc, Bool.andb_false_r, IH.
    rewrite !app_assoc, Z.add_assoc. reflexivity.
Qed.

Lemma nf_content_snoc : forall d done bl b,
  nf_content d done (bl ++ [b]) = nf_content d done bl ++ nb_content d (done + nfb_size bl) b.
Proof.
  intros d done bl. revert done. induction bl as [|a bl IH]; intros done b.
  - cbn [app nf_content nfb_size]. rewrite Z.add_0_r, !app_nil_r. reflexivity.
  - cbn [app nf_content nfb_size]. rewrite IH, !app_assoc, Z.add_assoc. reflexivity.
Qed.

Lemma nfb_open_snoc : forall mb n done bl b,
  nfb_open_ok mb n done bl -> blk_ok mb n (done + nfb_size bl) b -> 0 < nb_size b ->
  nfb_open_ok mb n done (bl ++ [b]).
Proof.
  intros mb n done bl. revert done. induction bl as [|a bl IH]; intros done b H Hb Hs.
  - cbn [app nfb_open_ok]. cbn [nfb_size] in Hb. rewrite Z.add_0_r in Hb. auto.
  - cbn [app nfb_open_ok] in *. cbn [nfb_size] in Hb. destruct H as (Ha & Hsa & H).
    split; [exact Ha|]. split; [exact Hsa|]. apply IH; auto. rewrite Z.add_assoc in Hb. exact Hb.
Qed.

(* the last block, ending the data, closes the list *)
Lemma nfb_close : forall mb n done bl b,
  nfb_open_ok mb n done bl -> blk_ok mb n (done + nfb_size bl) b -> done + nfb_size bl + nb_size b = n ->
  nf_blocks_ok mb n done (bl ++ [b]).
Proof.
  intros mb n done bl. revert done. induction bl as [|a bl IH]; intros done b H Hb He.
  - cbn [nfb_size] in *. rewrite Z.add_0_r in *. cbn [app nf_blocks_ok].
    unfold blk_ok in Hb. tauto.
  - cbn [nfb_size] in *. destruct H as ((H1 & H2 & H3 & H4) & Hsa & H).
    rewrite Z.add_assoc in Hb, He.
    pose proof (IH (done + nb_size a) b H Hb He) as IH'.
    cbn [app]. destruct (nf_snoc_cons bl b) as (x & y & E). rewrite E in *.
    exact (conj H1 (conj H2 (conj H3 (conj H4 (conj Hsa IH'))))).
Qed.

(* blocks that are not last stay inside the data *)
Lemma nfb_open_bound : forall mb n done bl,
  nfb_open_ok mb n done bl -> 0 <= done <= n -> 0 <= nfb_size bl /\ done + nfb_size bl <= n.
Proof.
  intros mb n done bl. revert done. induction bl as [|a bl IH]; intros done H Hd.
  - cbn [nfb_size]. lia.
  - cbn [nfb_size nfb_open_ok] in *. destruct H as ((H1 & H2 & H3 & H4) & Hsa & H).
    assert (done < n) by (destruct (Z.eq_dec done n); [specialize (H1 e); lia | lia]).
    specialize (H2 H0).
    assert (done + nb_size a <= n) by lia.
    destruct (IH (done + nb_size a) H) as [IH1 IH2]; lia.
Qed.

(* a closed list takes all the data *)
Lemma nf_blocks_ok_size : forall mb n done bl, nf_blocks_ok mb n done bl -> done + nfb_size bl = n.
Proof.
  intros mb n done bl. revert done. induction bl as [|a bl IH]; intros done H; [destruct H|].
  cbn [nf_blocks_ok nfb_size] in *. destruct H as (_ & _ & _ & _ & H).
  destruct bl as [|b bl'].
  - cbn [nfb_size]. lia.
  - destruct H as [_ H]. specialize (IH _ H). lia.
Qed.

(* ---------- sizes and bytes of one block ---------- *)

Lemma nb_header_length : forall last b, Zlength (nb_header last b) = 3.
Proof.
  intros. unfold nb_header. rewrite nf_Zlength_le_bytes. reflexivity.
Qed.

Lemma nb_payload_length : forall d done b, 0 <= done -> 0 <= nb_size b -> done + nb_size b <= Zlength d ->
  Zlength (nb_payload d done b) = if nb_rle b then 1 else nb_size b.
Proof.
  intros d done b H0 H1 H2. unfold nb_payload. destruct (nb_rle b); [reflexivity|].
  apply nf_Zlength_slice; auto.
Qed.

Lemma nb_content_length : forall d done b, 0 <= done -> 0 <= nb_size b -> done + nb_size b <= Zlength d ->
  Zlength (nb_content d done b) = nb_size b.
Proof.
  intros d done b H0 H1 H2. unfold nb_content. destruct (nb_rle b).
  - rewrite Zlength_correct, repeat_length. lia.
  - apply nf_Zlength_slice; auto.
Qed.

Lemma le_bytes_ok : forall k v, bytes_ok (le_bytes k v).
Proof.
  induction k; intros v; cbn [le_bytes]; constructor; [|apply IHk].
  unfold is_byte. apply Z.mod_pos_bound. lia.
Qed.

Lemma nb_header_ok : forall last b, bytes_ok (nb_header last b).
Proof.
  intros. apply le_bytes_ok.
Qed.

Lemma nb_payload_ok : forall d done b, bytes_ok d -> 0 <= nb_byte b < 256 -> bytes_ok (nb_payload d done b).
Proof.
  intros d done b Hd Hb. unfold nb_payload. destruct (nb_rle b).
  - constructor; [|constructor]. destruct (nb_size b =? 0); [exact Hb|]. apply nf_byte_at_ok, Hd.
  - apply nf_bytes_ok_slice, Hd.
Qed.

Lemma nb_content_ok : forall d done b, bytes_ok d -> bytes_ok (nb_content d done b).
Proof.
  intros d done b Hd. unfold nb_content. destruct (nb_rle b).
  - unfold bytes_ok. rewrite Forall_forall. intros x Hx. apply repeat_spec in Hx. subst x.
    apply nf_byte_at_ok, Hd.
  - apply nf_bytes_ok_slice, Hd.
Qed.

(* ---------- the header ---------- *)

Lemma nh_bytes_length : forall fcs maxw did h, nh_ok fcs maxw did h ->
  Zlength (nh_bytes fcs did h) = 5 + (if nh_single h then 0 else 1) + nh_did_size h + nh_fcs_size h.
Proof.
  intros fcs maxw did h (Hf & _ & _ & _ & _ & _ & Hd & _).
  unfold nh_bytes. rewrite !nf_Zlength_app, !nf_Zlength_le_bytes.
  assert (0 <= nh_did_size h) by (unfold nh_did_size; destruct (nh_did_flag h =? 3); lia).
  assert (0 <= nh_fcs_size h).
  { unfold nh_fcs_size, zb. destruct (nh_fcs_flag h =? 0); [destruct (nh_single h); lia|].
    apply Z.pow_nonneg. lia. }
  rewrite !Z2Nat.id by assumption.
  destruct (nh_single h); cbn [Zlength Zlength_aux]; lia.
Qed.

Lemma nh_bytes_ok : forall fcs maxw did h, nh_ok fcs maxw did h -> bytes_ok (nh_bytes fcs did h).
Proof.
  intros fcs maxw did h (Hf & _ & _ & _ & _ & Hb & Hd & _ & _ & _ & Hw & _).
  unfold nh_bytes, bytes_ok.
  apply Forall_app; split; [apply le_bytes_ok|].
  apply Forall_app; split.
  { constructor; [|constructor]. unfold is_byte, nh_fhd, zb.
    destruct Hb as [E|[E|[E|[E|[]]]]]; rewrite <- E; destruct (nh_single h); lia. }
  apply Forall_app; split.
  { destruct (nh_single h); [constructor | constructor; [unfold is_byte; lia | constructor]]. }
  apply Forall_app; split; apply le_bytes_ok.
Qed.

(* all the facts above, for the record of what this file proves *)
Lemma nf_new_frame_facts :
  (forall d done bl, nfb_bytes true d done bl = nf_blocks_bytes d done bl) /\
  (forall bl b, nfb_size (bl ++ [b]) = nfb_size bl + nb_size b) /\
  (forall closed d done bl b,
  nfb_bytes closed d done (bl ++ [b]) =
  nfb_bytes false d done bl ++ nb_header closed b ++ nb_payload d (done + nfb_size bl) b) /\
  (forall d done bl b,
  nf_content d done (bl ++ [b]) = nf_content d done bl ++ nb_content d (done + nfb_size bl) b) /\
  (forall mb n done bl b,
  nfb_open_ok mb n done bl -> blk_ok mb n (done + nfb_size bl) b -> 0 < nb_size b ->
  nfb_open_ok mb n done (bl ++ [b])) /\
  (forall mb n done bl b,
  nfb_open_ok mb n done bl -> blk_ok mb n (done + nfb_size bl) b -> done + nfb_size bl + nb_size b = n ->
  nf_blocks_ok mb n done (bl ++ [b])) /\
  (forall mb n done bl,
  nfb_open_ok mb n done bl -> 0 <= done <= n -> 0 <= nfb_size bl /\ done + nfb_size bl <= n) /\
  (forall mb n done bl, nf_blocks_ok mb n done bl -> done + nfb_size bl = n) /\
  (forall last b, Zlength (nb_header last b) = 3) /\
  (forall d done b, 0 <= done -> 0 <= nb_size b -> done + nb_size b <= Zlength d ->
  Zlength (nb_payload d done b) = if nb_rle b then 1 else nb_size b) /\
  (forall d done b, 0 <= done -> 0 <= nb_size b -> done + nb_size b <= Zlength d ->
  Zlength (nb_content d done b) = nb_size b) /\
  (forall k v, bytes_ok (le_bytes k v)) /\
  (forall last b, bytes_ok (nb_header last b)) /\
  (forall d done b, bytes_ok d -> 0 <= nb_byte b < 256 -> bytes_ok (nb_payload d done b)) /\
  (forall d done b, bytes_ok d -> bytes_ok (nb_content d done b)) /\
  (forall fcs maxw did h, nh_ok fcs maxw did h ->
  Zlength (nh_bytes fcs did h) = 5 + (if nh_single h then 0 else 1) + nh_did_size h + nh_fcs_size h) /\
  (forall fcs maxw did h, nh_ok fcs maxw did h -> bytes_ok (nh_bytes fcs did h)).
Proof.
  exact (conj nfb_bytes_closed (conj nfb_size_snoc (conj nfb_bytes_snoc (conj nf_content_snoc (conj nfb_open_snoc (conj nfb_close (conj nfb_open_bound (conj nf_blocks_ok_size (conj nb_header_length (conj nb_payload_length (conj nb_content_length (conj le_bytes_ok (conj nb_header_ok (conj nb_payload_ok (conj nb_content_ok (conj nh_bytes_length (nh_bytes_ok))))))))))))))))).
Qed.
