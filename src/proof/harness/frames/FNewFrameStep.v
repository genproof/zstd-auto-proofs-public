(* One iteration of new_frame's block loop (harness/frames.h), in the model: the blocks bl written so far
   (none of them last), with the facts the loop keeps about them, and one more block b, valid at offset
   nfb_size bl, marked last or not (lst).  The facts then hold for bl ++ [b]: the block list (closed when
   lst), the data taken, the content left in the data array, the bytes written, and the room they take in
   new_frame's buffer of 26 + 4 n bytes (hb: the frame header before the blocks).  Plain Coq. *)
Require Import Zstd.proof.harness.frames.FModel Zstd.proof.harness.frames.FNewFrameFacts.

Lemma nf_step : forall (d hb: list Z) mb bl b (lst: bool),
  bytes_ok d ->
  nfb_open_ok mb (Zlength d) 0 bl ->
  0 <= nfb_size bl <= Zlength d ->
  Zlength (nf_content d 0 bl) = nfb_size bl ->
  bytes_ok (nf_content d 0 bl) ->
  bytes_ok (nfb_bytes false d 0 bl) ->
  Zlength hb + Zlength (nfb_bytes false d 0 bl) <= 18 + 4 * nfb_size bl ->
  blk_ok mb (Zlength d) (nfb_size bl) b ->
  (lst = true -> nfb_size bl + nb_size b = Zlength d) ->
  (lst = false -> 0 < nb_size b) ->
  (if lst then nf_blocks_ok mb (Zlength d) 0 (bl ++ [b]) else nfb_open_ok mb (Zlength d) 0 (bl ++ [b])) /\
  0 <= nfb_size (bl ++ [b]) <= Zlength d /\
  Zlength (nf_content d 0 (bl ++ [b])) = nfb_size (bl ++ [b]) /\
  bytes_ok (nf_content d 0 (bl ++ [b])) /\
  bytes_ok (nfb_bytes lst d 0 (bl ++ [b])) /\
  Zlength hb + Zlength (nfb_bytes lst d 0 (bl ++ [b])) <= (if lst then 22 else 18) + 4 * nfb_size (bl ++ [b]).
Proof.
  intros d hb mb bl b lst Hd Hopen Hsz Hcl Hco Hby Hroom Hb Hlast Hne.
  (* the block stays inside the data: it is empty at the end of the data, else at most n - done long *)
  assert (Hs: 0 <= nb_size b /\ nfb_size bl + nb_size b <= Zlength d).
  { destruct Hb as (Hb1 & Hb2 & _).
    destruct (Z.eq_dec (nfb_size bl) (Zlength d)) as [E|E];
      [specialize (Hb1 E) | specialize (Hb2 ltac:(lia))]; lia. }
  assert (Hbyte: 0 <= nb_byte b < 256) by apply Hb.
  rewrite nfb_size_snoc, nf_content_snoc, nfb_bytes_snoc, !Z.add_0_l.
  unfold bytes_ok in *.
  split; [|split; [lia|split; [|split; [|split]]]].
  - destruct lst.
    + apply nfb_close; [exact Hopen | rewrite Z.add_0_l; exact Hb | rewrite Z.add_0_l; auto].
    + apply nfb_open_snoc; [exact Hopen | rewrite Z.add_0_l; exact Hb | auto].
  - rewrite nf_Zlength_app, Hcl, nb_content_length by lia. reflexivity.
  - apply Forall_app. split; [exact Hco | apply nb_content_ok, Hd].
  - apply Forall_app. split; [exact Hby|].
    apply Forall_app. split; [apply nb_header_ok | apply nb_payload_ok; assumption].
  - (* a block adds its 3-byte header and a payload of at most max 1 size bytes *)
    rewrite !nf_Zlength_app, nb_header_length, nb_payload_length by lia.
    destruct lst, (nb_rle b);
      [| | specialize (Hne eq_refl) | specialize (Hne eq_refl)]; lia.
Qed.
