(* A block the exact model decodes (Exact.xblock) from bytes leaves bytes: the destination cells it returns, the
   state's litExtraBuffer, and a Huffman table whose cells hold byte symbols (X1) or two-byte sequences (X2).

   The decoder's proofs need it to identify the model's content with the bytes the C wrote: block_exact (DecIface)
   gives the output array's cells as zbytes of the model's written cells, and zbytes is injective only on bytes.
   The Huffman condition is a property of the tables zstd builds (ExHuf.xhuf_of on a parsed description: at most
   256 symbols), kept from block to block; ZSTD_decompressBegin starts without a table.  Plain Coq. *)
Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.ExHuf Zstd.proof.model.ExBlock.
Require Import Zstd.proof.model.Exact Zstd.proof.model.ExFrameFacts Zstd.proof.model.ExBlockBytesKit.
Require Import Coq.micromega.Lia.
Local Open Scope Z_scope.

(* the cells of a Huffman table hold what its decoder emits as bytes: an X1 cell's symbol is a byte, an X2 cell's
   sequence is a U16 (its low and high bytes are the symbols) *)
Definition xh_good (o: option xhuf) : Prop :=
  match o with
  | None => True
  | Some t => Forall (fun c : Z * Z * Z => let '(sq, _, _) := c in 0 <= sq < (if xh_x2 t then 65536 else 256))
                (xh_cells t)
  end.

(* a compressed block decoded from bytes (the history mem, the body, litExtraBuffer, a good Huffman table) leaves
   bytes in every written destination cell and in litExtraBuffer, and a good Huffman table *)
Lemma xblock_bytes (st st': xstate) (mem m': list Z) (ps op ds de: Z) (body: list Z) (bsm cap: Z) (str: bool)
    (n: Z) :
  bytes_ok mem -> bytes_ok body -> bytes_ok (x_lxb xhuf st) -> xh_good (x_huf xhuf st) ->
  xblock st mem ps op ds de body bsm cap str = Some (st', m', n) ->
  bytes_ok m' /\ bytes_ok (x_lxb xhuf st') /\ xh_good (x_huf xhuf st').
Proof.
  intros Hm Hb Hl Hh H.
  assert (Hh': forall t, x_huf xhuf st = Some t -> xt_good t).
  { intros t Et. rewrite Et in Hh. exact Hh. }
  unfold xblock, x_block in H. cbv zeta in H.
  destruct (Zlength body >? bsm); [discriminate|].
  destruct (x_lits xhuf x_lits_huf (x_huf xhuf st) body bsm (Z.min bsm cap) str) as [[[lits lused] huf]|] eqn:El;
    [|discriminate].
  destruct (lits_b _ _ _ _ _ _ _ _ Hb Hh' El) as [Hlits Hhuf].
  destruct (x_seq_header ncount_c (x_seq xhuf st) (skipn (Z.to_nat lused) body)) as [[[nbSeq tabs] hused]|];
    [|discriminate].
  destruct ((nbSeq >? 0) && (cap =? 0))%bool; [discriminate|].
  destruct (x_lits_store body lits lused {| xm_dst := map Some mem; xm_lxb := x_lxb xhuf st |} op
              (Z.min bsm cap) bsm cap str) as [[[[[m lr] li] lim] sp]|] eqn:Es; [|discriminate].
  apply lits_store_mb in Es; [|exact Hb|exact Hlits|apply mb_init; assumption].
  assert (Hg: xh_good huf) by (destruct huf as [t|]; [apply Hhuf; reflexivity|exact I]).
  match type of H with (match ?r with _ => _ end = _) =>
    assert (Hr: forall m1 op1 rep1, r = Some (m1, op1, rep1) -> mb m1);
    [|destruct r as [[[m1 op1] rep1]|]; [specialize (Hr _ _ _ eq_refl)|discriminate]] end.
  { intros m1 op1 rep1 E. destruct (nbSeq =? 0).
    - match type of E with (match x_last ?e ?s with _ => _ end = _) =>
        destruct (x_last e s) as [[m2 op2]|] eqn:Ex; [|discriminate] end.
      injection E as <- _ _. eapply last_mb in Ex; [exact Ex|assumption..].
    - destruct tabs as [t|]; [|discriminate]. eapply seqs_mb in E; [exact E|assumption..]. }
  injection H as <- <- _. destruct Hr as [Hd Hx].
  split; [apply mb_written, Hd|]. split; [exact Hx|exact Hg].
Qed.

Lemma xbb_slice (l: list Z) (i k: Z) : bytes_ok l -> bytes_ok (slice l i k).
Proof.
  intros H. unfold slice, bytes_ok in *. generalize (Z.to_nat k) as a. generalize (Z.to_nat i) as b.
  induction l as [|x l IH]; intros b a; [destruct b, a; constructor|].
  inversion H as [|? ? Hx Hl]; subst. destruct b as [|b]; cbn [skipn].
  - destruct a as [|a]; [constructor|]. cbn. constructor; [exact Hx|].
    specialize (IH Hl O a). exact IH.
  - apply IH. exact Hl.
Qed.

(* one step of ZSTD_decompressFrame's block loop (ExFrameFacts.xb_one) on bytes: its content is bytes and the
   state after it is good again *)
Lemma xb_one_bytes (st st': xstate) (t out cn: list Z) (cap bsm n: Z) (l: bool) :
  bytes_ok t -> bytes_ok out -> bytes_ok (x_lxb xhuf st) -> xh_good (x_huf xhuf st) ->
  xb_one xstate xblock st t out cap bsm = Some (st', cn, n, l) ->
  bytes_ok cn /\ bytes_ok (x_lxb xhuf st') /\ xh_good (x_huf xhuf st').
Proof.
  intros Ht Ho Hl Hh H. unfold xb_one in H.
  destruct (cblock_size t) as [c|]; [|discriminate].
  destruct (c >? Zlength t - ZSTD_blockHeaderSize); [discriminate|]. cbv zeta in H.
  destruct (bp_type (block_props_of t) =? 2).
  - destruct (xblock st out 0 (Zlength out) 0 0 (slice t ZSTD_blockHeaderSize c) bsm (cap - Zlength out) false)
      as [[[st2 mem2] d]|] eqn:E; [|discriminate].
    injection H as <- <- _ _.
    destruct (xblock_bytes st st2 out mem2 0 (Zlength out) 0 0 (slice t ZSTD_blockHeaderSize c) bsm
                (cap - Zlength out) false d Ho (xbb_slice _ _ _ Ht) Hl Hh E) as (Hm & Hl2 & Hh2).
    split; [apply xbb_slice, Hm | auto].
  - destruct (bp_type (block_props_of t) =? 0).
    + destruct (c >? cap - Zlength out); [discriminate|].
      injection H as <- <- _ _. split; [apply xbb_slice, Ht | auto].
    + destruct (bp_origSize (block_props_of t) >? cap - Zlength out); [discriminate|].
      injection H as <- <- _ _. split; [|auto].
      unfold bytes_ok. apply Forall_forall. intros x Hx. apply repeat_spec in Hx. subst x.
      unfold byte_at. pose proof (xbb_slice t ZSTD_blockHeaderSize c Ht) as Hs. unfold bytes_ok in Hs.
      remember (slice t ZSTD_blockHeaderSize c) as b eqn:Eb. clear Eb.
      destruct b as [|x b]; [cbn; unfold is_byte; lia|]. cbn. inversion Hs; assumption.
Qed.

(* the Huffman table alone: a block decoded from a body of bytes keeps a good table (the literals section keeps the
   previous table or builds one from a description), whatever the memory holds *)
Lemma xblock_good (st st': xstate) (mem m': list Z) (ps op ds de: Z) (body: list Z) (bsm cap: Z) (str: bool)
    (n: Z) :
  bytes_ok body -> xh_good (x_huf xhuf st) ->
  xblock st mem ps op ds de body bsm cap str = Some (st', m', n) -> xh_good (x_huf xhuf st').
Proof.
  intros Hb Hh H.
  assert (Hh': forall t, x_huf xhuf st = Some t -> xt_good t).
  { intros t Et. rewrite Et in Hh. exact Hh. }
  unfold xblock, x_block in H. cbv zeta in H.
  destruct (Zlength body >? bsm); [discriminate|].
  destruct (x_lits xhuf x_lits_huf (x_huf xhuf st) body bsm (Z.min bsm cap) str) as [[[lits lused] huf]|] eqn:El;
    [|discriminate].
  destruct (lits_b _ _ _ _ _ _ _ _ Hb Hh' El) as [_ Hhuf].
  assert (Hg: xh_good huf) by (destruct huf as [t|]; [apply Hhuf; reflexivity|exact I]).
  destruct (x_seq_header ncount_c (x_seq xhuf st) (skipn (Z.to_nat lused) body)) as [[[nbSeq tabs] hused]|];
    [|discriminate].
  destruct ((nbSeq >? 0) && (cap =? 0))%bool; [discriminate|].
  destruct (x_lits_store _ _ _ _ _ _ _ _ _) as [[[[[m lr] li] lim] sp]|]; [|discriminate].
  match type of H with (match ?r with _ => _ end = _) => destruct r as [[[m1 op1] rep1]|]; [|discriminate] end.
  injection H as <- _ _. exact Hg.
Qed.

(* ... and so does one step of the block loop *)
Lemma xb_one_good (st st': xstate) (t out cn: list Z) (cap bsm n: Z) (l: bool) :
  bytes_ok t -> xh_good (x_huf xhuf st) ->
  xb_one xstate xblock st t out cap bsm = Some (st', cn, n, l) -> xh_good (x_huf xhuf st').
Proof.
  intros Ht Hh H. unfold xb_one in H.
  destruct (cblock_size t) as [c|]; [|discriminate].
  destruct (c >? Zlength t - ZSTD_blockHeaderSize); [discriminate|]. cbv zeta in H.
  destruct (bp_type (block_props_of t) =? 2).
  - destruct (xblock st out 0 (Zlength out) 0 0 (slice t ZSTD_blockHeaderSize c) bsm (cap - Zlength out) false)
      as [[[st2 mem2] d]|] eqn:E; [|discriminate].
    injection H as <- _ _ _. exact (xblock_good _ _ _ _ _ _ _ _ _ _ _ _ _ (xbb_slice _ _ _ Ht) Hh E).
  - destruct (bp_type (block_props_of t) =? 0).
    + destruct (c >? cap - Zlength out); [discriminate|]. injection H as <- _ _ _. exact Hh.
    + destruct (bp_origSize (block_props_of t) >? cap - Zlength out); [discriminate|].
      injection H as <- _ _ _. exact Hh.
Qed.
