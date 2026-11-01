(* FS3 streaming, G2: the content the model decodes with a dictionary of bytes is bytes.  Plain Coq. *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Block Zstd.proof.model.Series Zstd.proof.model.Params Zstd.proof.model.ParamsW Zstd.proof.dec.FS.StreamModelFacts.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

(* a dictionary model whose content is bytes and whose Huffman table has at most 256 symbols *)
Definition g2_dm_ok (dm: dict_model) : Prop := bytes_ok (dm_content dm) /\ huf_ok (st_huf (dm_state dm)).

Lemma g2_decode_block_bytes : forall st hist out b bsm ws st' c, bytes_ok hist -> bytes_ok out -> bytes_ok b ->
  st_ok st -> decode_block st hist out b bsm ws = Some (st', c) -> bytes_ok c /\ st_ok st'.
Proof.
  intros st hist out b bsm ws st' c Hh Ho Hb Hs H. unfold decode_block in H.
  destruct (_ >? _); [discriminate|].
  destruct (decode_literals _ _ _) as [[[lits lused] huf]|] eqn:L; [|discriminate].
  destruct (decode_literals_bytes _ _ _ _ _ _ Hb Hs L) as [Hl Hh'].
  destruct (decode_seq_header _ _) as [[[nbSeq tabs] hused]|]; [|discriminate].
  match type of H with context [match ?e with Some _ => _ | None => None end] =>
    destruct e as [seqs|]; [|discriminate] end.
  destruct (exec_seqs _ _ _ _ _ _) as [[[out' lits'] rep']|] eqn:X; [|discriminate].
  destruct (_ >? _); [discriminate|]. inversion H; subst.
  destruct (exec_seqs_bytes _ _ _ _ _ _ _ _ _ Hh Hl Ho X).
  split; [|unfold st_ok; simpl; auto].
  apply bytes_ok_skipn. apply bytes_ok_app; auto.
Qed.

Lemma g2_db_bytes : forall f st hist s out bsm ws o k, bytes_ok hist -> bytes_ok s -> bytes_ok out -> st_ok st ->
  decode_blocks f st hist s out bsm ws = Some (o, k) -> bytes_ok o.
Proof.
  induction f; intros st hist s out bsm ws o k Hh Hs Ho Hst H; [discriminate|].
  cbn [decode_blocks] in H.
  destruct (cblock_size s) as [c|]; [|discriminate].
  destruct (_ >? _); [discriminate|]. cbv zeta in H.
  assert (Hbody: bytes_ok (slice s ZSTD_blockHeaderSize c)) by (apply bytes_ok_slice; auto).
  match type of H with context [match ?r with None => None | Some _ => _ end] =>
    destruct r as [[st' out']|] eqn:Er; [|discriminate] end.
  assert (Hr: bytes_ok out' /\ st_ok st').
  { destruct (bp_type _ =? 0); [|destruct (bp_type _ =? 1)].
    - destruct (_ >? _); [discriminate|]. inversion Er; subst.
      split; auto. apply bytes_ok_app. split; auto.
    - destruct (_ || _); [discriminate|]. inversion Er; subst.
      split; auto. apply bytes_ok_app. split; auto. apply bytes_ok_repeat, is_byte_byte_at; auto.
    - destruct (decode_block _ _ _ _ _ _) as [[st2 c2]|] eqn:D; [|discriminate]. inversion Er; subst.
      destruct (g2_decode_block_bytes _ _ _ _ _ _ _ _ Hh Ho Hbody Hst D).
      split; auto. apply bytes_ok_app; auto. }
  destruct Hr as [Ho' Hst'].
  destruct (bp_last _ =? 1); [inversion H; subst; auto|].
  destruct (decode_blocks f st' hist _ out' bsm ws) as [[o2 k2]|] eqn:E2; [|discriminate].
  inversion H; subst. eapply IHf; [| | | |exact E2]; auto. apply bytes_ok_skipn; auto.
Qed.

Lemma g2_frame_bytes : forall md dm wl s c k, g2_dm_ok dm -> bytes_ok s ->
  decode_frame_m md dm wl s = FOk c k -> bytes_ok c.
Proof.
  intros md dm wl s c k [Hc Hh] Hs H. unfold decode_frame_m in H. cbv zeta in H.
  repeat match type of H with
  | context [if ?b then _ else _] => destruct b; [discriminate|]
  end.
  destruct (get_frame_header_m _ _) as [| |h]; try discriminate.
  repeat match type of H with
  | context [if ?b then _ else _] => destruct b; [discriminate|]
  end.
  match type of H with context [match ?e with Some _ => _ | None => FUnk end] =>
    destruct e as [[o kb]|] eqn:DB; [|discriminate] end.
  destruct (md_dwin md); [apply decode_blocks_w_lenient in DB|].
  all: assert (bytes_ok o).
  all: try (eapply g2_db_bytes; [exact Hc| | |exact Hh|exact DB]; [apply bytes_ok_skipn; auto|constructor]).
  all: destruct (_ && _); [discriminate|].
  all: destruct (fh_checksumFlag h =? 1); [destruct (_ <? 4); [discriminate|]; destruct (_ && _); [discriminate|]|];
  inversion H; subst; auto.
Qed.

Lemma g2_frame_dict : forall mg dm s, frame_dict mg sel_none (Some dm) s = Some dm.
Proof. intros. unfold frame_dict, sel_none. destruct (get_frame_header_m mg s); reflexivity. Qed.

Lemma g2_walk_bytes : forall f md dm wl s off l t, bytes_ok s -> g2_dm_ok dm ->
  walk_m f md sel_none (Some dm) wl s off = (l, t) -> bytes_ok (flat_map fr_content l).
Proof.
  induction f; intros md dm wl s off l t Hs Hd H.
  - cbn in H. inversion H; subst. constructor.
  - cbn [walk_m] in H. cbv zeta in H.
    destruct (Zlength s <? _); [inversion H; subst; constructor|].
    destruct (negb _ && _).
    + destruct (skippable_frame_size s) as [k|]; [|inversion H; subst; constructor].
      assert (Ec: (if md_dwin md then match sel_none (Z.land (le_field s 0 4) 15) with Some d => Some d | None => Some dm end
                   else Some dm) = Some dm) by (destruct (md_dwin md); reflexivity).
      rewrite Ec in H.
      destruct (walk_m f md sel_none (Some dm) wl (skipn (Z.to_nat k) s) (off + k)) as [l' t'] eqn:E2.
      inversion H; subst. cbn [flat_map fr_content app].
      eapply IHf; [|exact Hd|exact E2]. apply bytes_ok_skipn; auto.
    + rewrite g2_frame_dict in H.
      destruct (decode_frame_m md dm wl s) as [c k| | |] eqn:D; try (inversion H; subst; constructor).
      destruct (walk_m f md sel_none (Some dm) wl (skipn (Z.to_nat k) s) (off + k)) as [l' t'] eqn:E2.
      inversion H; subst. cbn [flat_map fr_content].
      apply bytes_ok_app. split.
      * eapply g2_frame_bytes; eauto.
      * eapply IHf; [|exact Hd|exact E2]. apply bytes_ok_skipn; auto.
Qed.

(* (1) a dictionary in ZSTD_dct_auto mode made of bytes is g2_dm_ok; (2) every frame content of a series read
   with such a dictionary (no selection) is bytes *)
Lemma g2_bytes_facts :
  (forall b dm, bytes_ok b -> dict_auto b = Some dm -> g2_dm_ok dm) /\
  (forall md dm wl x l t, bytes_ok x -> g2_dm_ok dm ->
     series_frames_m md sel_none (Some dm) wl x = (l, t) -> bytes_ok (flat_map fr_content l)).
Proof.
  split.
  - intros b dm Hb H. unfold dict_auto in H.
    destruct (Zlength b <? 8); [inversion H; subst; split; simpl; auto|].
    destruct (negb _); [inversion H; subst; split; simpl; auto|].
    destruct (load_dentropy b) as [[st es]|] eqn:L; [|discriminate].
    inversion H; subst. clear H. unfold load_dentropy in L.
    destruct (Zlength b <=? 8); [discriminate|].
    destruct (Huffman.huf_parse_desc (skipn 8 b)) as [[ht hs]|] eqn:P; [|discriminate].
    repeat match type of L with
    | context [match ?e with _ => _ end] => let E := fresh "E" in destruct e eqn:E; try discriminate
    | context [if ?c then _ else _] => let E := fresh "E" in destruct c eqn:E; try discriminate
    end.
    inversion L; subst. split; simpl.
    + apply bytes_ok_skipn; auto.
    + eapply huf_parse_len; [|exact P]. apply bytes_ok_skipn; auto.
  - intros md dm wl x l t Hx Hd H. unfold series_frames_m in H. eapply g2_walk_bytes; eauto.
Qed.
