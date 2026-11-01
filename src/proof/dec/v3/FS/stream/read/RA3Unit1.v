(* FS3 streaming model facts (a copy of modelw/MW3Unit1.v): a Zstandard frame whose current block fails, and the model's
   block content is bytes (ported from v2 src/proof/dec/FS/StreamModelFacts.v). *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Block Zstd.proof.model.Xxh64 Zstd.proof.model.Info Zstd.proof.model.Series Zstd.proof.model.StreamModel Zstd.proof.model.Params Zstd.proof.model.ParamsH Zstd.proof.model.Huffman.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Require Import Zstd.proof.model.ParamsW Zstd.proof.dec.v3.FS.stream.S3ModelDefs Zstd.proof.dec.v3.FS.stream.read.RA3Base Zstd.proof.dec.v3.FS.stream.read.RA3Frame Zstd.proof.dec.v3.FS.stream.read.RA3FrameM Zstd.proof.dec.v3.FS.stream.read.RA3Walk.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

(* ---------- series that do not end ---------- *)

Lemma series_not_end3 : forall md sel cd w s dm, s <> nil ->
  negb (md_magicless md) && is_skippable_magic (le_field s 0 4) = false ->
  frame_dict (md_magicless md) sel cd s = Some dm ->
  (forall c k, decode_frame_m md dm w s <> FOk c k) ->
  snd (series_frames_m md sel cd w s) <> TEnd.
Proof.
  intros md sel cd w s dm Hs Hk Hf Hd. unfold series_frames_m. rewrite walk_S.
  destruct (wfirst md sel cd w s) as [[[[k c] sk] cur']|t] eqn:E.
  - unfold wfirst in E. destruct (Zlength s <? _); [discriminate|]. rewrite Hk, Hf in E.
    destruct (decode_frame_m md dm w s) eqn:D; try discriminate. exfalso; eapply Hd; eauto.
  - simpl. intro. subst t. apply wfirst_end in E. auto.
Qed.

Lemma series_unk3 : forall md sel cd w s dm, s <> nil ->
  negb (md_magicless md) && is_skippable_magic (le_field s 0 4) = false ->
  frame_dict (md_magicless md) sel cd s = Some dm ->
  decode_frame_m md dm w s = FUnk -> snd (series_frames_m md sel cd w s) = TUnk.
Proof.
  intros md sel cd w s dm Hs Hk Hf Hd. unfold series_frames_m. rewrite walk_S.
  unfold wfirst. destruct (Zlength s <? _).
  - destruct (Zlength s =? 0) eqn:E; auto. apply Z.eqb_eq in E. rewrite Zlength_correct in E.
    destruct s; [congruence|simpl in E; lia].
  - rewrite Hk, Hf, Hd. auto.
Qed.

(* ---------- a Zstandard frame whose current block fails in the model ---------- *)

Definition blk_fails (h: frame_header) (res: option (dstate * list Z * Z * bool)) : Prop :=
  match res with
  | None => True
  | Some (_, out2, _, last) =>
      (last = true /\ ~ fcs_ok h out2) \/
      (fh_contentSize h <> ZSTD_CONTENTSIZE_UNKNOWN /\ fh_contentSize h < Zlength out2)
  end.

Lemma fcs_bad_cond : forall h out, ~ fcs_ok h out ->
  (negb (fh_contentSize h =? ZSTD_CONTENTSIZE_UNKNOWN) && negb (Zlength out =? fh_contentSize h)) = true.
Proof.
  unfold fcs_ok; intros.
  destruct (fh_contentSize h =? ZSTD_CONTENTSIZE_UNKNOWN) eqn:E1; [apply Z.eqb_eq in E1; tauto|].
  destruct (Zlength out =? fh_contentSize h) eqn:E2; [apply Z.eqb_eq in E2; tauto|]. auto.
Qed.

Lemma fcs_ok_cond : forall h out, fcs_ok h out ->
  (negb (fh_contentSize h =? ZSTD_CONTENTSIZE_UNKNOWN) && negb (Zlength out =? fh_contentSize h)) = false.
Proof.
  unfold fcs_ok; intros h out [E|E]; rewrite E, Z.eqb_refl; auto. apply Bool.andb_false_r.
Qed.

Lemma cblock_none_res : forall dw st hist s out bsm ws, cblock_size s = None -> block_res dw st hist s out bsm ws = None.
Proof. intros. unfold block_res. rewrite H. auto. Qed.

Lemma zstd_unk_core3 : forall md dm hdr h bl ts outc rest,
  get_frame_header_m (md_magicless md) hdr = FH_ok h -> Zlength hdr = fh_headerSize h -> fh_frameType h = 0 ->
  (fh_dictID h = 0 \/ fh_dictID h = dm_id dm) -> bytes_ok hdr ->
  blocks_pre (md_dwin md) (dm_content dm) (Z.min (fh_blockSizeMax h) (md_bmax md)) (fh_windowSize h) (dm_state dm) bl ts outc false ->
  3 <= Zlength rest ->
  (forall r, blk_fails h (block_res (md_dwin md) ts (dm_content dm) (rest ++ r) outc
                            (Z.min (fh_blockSizeMax h) (md_bmax md)) (fh_windowSize h))) ->
  forall w r, decode_frame_m md dm w (hdr ++ bl ++ rest ++ r) = if fh_windowSize h >? w then FDetHdr else FUnk.
Proof.
  intros md dm hdr h bl ts outc rest G Hl Ht Hd Hb Hbp H3 Hr w r.
  pose proof (Zlength_nonneg r). pose proof (Zlength_nonneg bl).
  destruct (dfm_cur md dm w hdr h bl ts outc (rest ++ r) G Hl Ht Hd Hb Hbp) as [fuel [Hf E]];
    [rewrite !Zlength_app; lia|].
  rewrite E. destruct (fh_windowSize h >? w); auto.
  destruct fuel as [|fuel].
  { rewrite length_app in Hf. rewrite Zlength_correct in H3. lia. }
  rewrite db_S_eq. specialize (Hr r).
  destruct (block_res _ ts _ (rest ++ r) outc _ _) as [[[[st2 out2] k] last]|]; [|reflexivity].
  simpl in Hr. destruct last.
  - simpl. unfold df_fin. destruct Hr as [[_ Hr]|[Hu Hlt]].
    + rewrite fcs_bad_cond by auto. auto.
    + rewrite fcs_bad_cond; auto. unfold fcs_ok. lia.
  - destruct Hr as [[Hr _]|[Hu Hlt]]; [discriminate|].
    unfold oshift. destruct (dblocks _ fuel st2 _ _ out2 _ _) as [[o k2]|] eqn:D; [|reflexivity].
    destruct (db_out _ _ _ _ _ _ _ _ _ _ D) as [d ->]. unfold df_fin.
    rewrite fcs_bad_cond; auto. unfold fcs_ok. rewrite Zlength_app. pose proof (Zlength_nonneg d). lia.
Qed.

Lemma hdr_skip_false3 : forall mg hdr h r, get_frame_header_m mg hdr = FH_ok h -> fh_frameType h = 0 ->
  negb mg && is_skippable_magic (le_field (hdr ++ r) 0 4) = false.
Proof.
  intros. destruct mg; [reflexivity|].
  destruct (gfhm_info _ _ _ H) as [[_ [Ht _]]|[_ [H5 [Hm _]]]]; [congruence|].
  cbn [starting_len] in H5. unfold ZSTD_FRAMEHEADERSIZE_PREFIX in H5.
  rewrite le_field_app, Hm by lia. reflexivity.
Qed.

Lemma app_ne_nil_l : forall (a b: list Z), a <> nil -> a ++ b <> nil.
Proof. intros. destruct a; [congruence|discriminate]. Qed.

Lemma hdr_ne_nil3 : forall mg hdr h, get_frame_header_m mg hdr = FH_ok h -> hdr <> nil.
Proof.
  intros. apply gfhm_len in H. pose proof (starting_len_pos mg). intro E. subst.
  change (Zlength (@nil Z)) with 0 in H. lia.
Qed.

Section Dead.
Variable sm : smode.
Variable cd : option dict_model.
Variable hdr : list Z.
Variable h : frame_header.
Variable dm : dict_model.
Hypothesis G : get_frame_header_m (md_magicless (sm_md sm)) hdr = FH_ok h.
Hypothesis Hl : Zlength hdr = fh_headerSize h.
Hypothesis Ht : fh_frameType h = 0.
Hypothesis Hfd : frame_dict (md_magicless (sm_md sm)) (sm_sel sm) cd hdr = Some dm.
Hypothesis Hd : fh_dictID h = 0 \/ fh_dictID h = dm_id dm.
Hypothesis Hb : bytes_ok hdr.

Lemma fd_ext3 : forall r, frame_dict (md_magicless (sm_md sm)) (sm_sel sm) cd (hdr ++ r) = Some dm.
Proof. intros. rewrite (frame_dict_ext _ _ _ _ r h G (bytes_ok_byte_at _ _ Hb)). auto. Qed.

Lemma fbad_zstd3 : forall bl ts outc rest,
  blocks_pre (md_dwin (sm_md sm)) (dm_content dm) (Z.min (fh_blockSizeMax h) (md_bmax (sm_md sm))) (fh_windowSize h) (dm_state dm) bl ts outc false ->
  3 <= Zlength rest ->
  (forall r, blk_fails h (block_res (md_dwin (sm_md sm)) ts (dm_content dm) (rest ++ r) outc
                            (Z.min (fh_blockSizeMax h) (md_bmax (sm_md sm))) (fh_windowSize h))) ->
  fbad sm cd (hdr ++ bl ++ rest).
Proof.
  intros bl ts outc rest Hbp H3 Hr s Hp.
  apply is_prefix_ex in Hp. destruct Hp as [r ->]. rewrite <- !app_assoc.
  eapply series_not_end3.
  - apply app_ne_nil_l. eapply hdr_ne_nil3; eauto.
  - eapply hdr_skip_false3; eauto.
  - apply fd_ext3.
  - intros c k. rewrite (zstd_unk_core3 (sm_md sm) dm hdr h bl ts outc rest G Hl Ht Hd Hb Hbp H3 Hr).
    destruct (_ >? _); discriminate.
Qed.

(* a frame that fails at its checksum (or anywhere after its blocks, by the decoder's result) *)
Lemma fbad_zstd3_last : forall bl ts outc t,
  blocks_pre (md_dwin (sm_md sm)) (dm_content dm) (Z.min (fh_blockSizeMax h) (md_bmax (sm_md sm))) (fh_windowSize h) (dm_state dm) bl ts outc true ->
  (forall r c k, df_fin (sm_md sm) h (hdr ++ bl ++ t ++ r) (Some (outc, Zlength bl)) <> FOk c k) ->
  fbad sm cd (hdr ++ bl ++ t).
Proof.
  intros bl ts outc t Hbp Hr s Hp.
  apply is_prefix_ex in Hp. destruct Hp as [r ->]. rewrite <- !app_assoc.
  eapply series_not_end3.
  - apply app_ne_nil_l. eapply hdr_ne_nil3; eauto.
  - eapply hdr_skip_false3; eauto.
  - apply fd_ext3.
  - intros c k. rewrite (dfm_cur_last (sm_md sm) dm _ hdr h bl ts outc (t ++ r) G Hl Ht Hd Hb Hbp).
    destruct (_ >? _); [discriminate|]. apply Hr.
Qed.

End Dead.

(* ---------- one block, unfolded ---------- *)

Definition blk_body (dw: bool) (st: dstate) (hist: list Z) (bp: block_props) (body out: list Z) (c bsm ws: Z)
    : option (dstate * list Z) :=
  if bp_type bp =? 0 then (if c >? bsm then None else Some (st, out ++ body))
  else if bp_type bp =? 1 then
    (if (bp_origSize bp >? bsm) || (c >? bsm) then None
     else Some (st, out ++ repeat (byte_at body 0) (Z.to_nat (bp_origSize bp))))
  else match dec_block dw st hist out body bsm ws with
       | Some (st', content) => Some (st', out ++ content)
       | None => None
       end.

Lemma br_eq : forall dw st hist s out bsm ws c, cblock_size s = Some c -> c <= Zlength s - 3 ->
  block_res dw st hist s out bsm ws =
  match blk_body dw st hist (block_props_of s) (slice s 3 c) out c bsm ws with
  | None => None
  | Some (st', out') => Some (st', out', 3 + c, bp_last (block_props_of s) =? 1)
  end.
Proof.
  intros. unfold block_res. rewrite H. unfold ZSTD_blockHeaderSize.
  replace (c >? Zlength s - 3) with false by (symmetry; apply Zgtb_le; lia). reflexivity.
Qed.

Lemma slice_hdr : forall bh t k, Zlength bh = 3 -> slice (bh ++ t) 3 k = firstn (Z.to_nat k) t.
Proof.
  intros. unfold slice. rewrite skipn_app. rewrite Zlength_correct in H.
  replace (Z.to_nat 3) with (length bh) by lia. rewrite skipn_all, Nat.sub_diag. auto.
Qed.

Lemma cblock_types : forall s c, cblock_size s = Some c ->
  (bp_type (block_props_of s) = 1 /\ c = 1) \/
  (bp_type (block_props_of s) <> 1 /\ bp_type (block_props_of s) <> 3 /\ c = bp_origSize (block_props_of s)).
Proof.
  unfold cblock_size; intros. destruct (Zlength s <? ZSTD_blockHeaderSize); [discriminate|].
  destruct (bp_type _ =? 1) eqn:E1; [left; apply Z.eqb_eq in E1; inversion H; auto|].
  destruct (bp_type _ =? 3) eqn:E3; [discriminate|]. right. apply Z.eqb_neq in E1, E3. inversion H; auto.
Qed.

Lemma decode_block_len : forall st hist out b bsm ws st' c,
  decode_block st hist out b bsm ws = Some (st', c) -> Zlength c <= bsm.
Proof.
  unfold decode_block; intros.
  repeat match type of H with
  | context [if ?b then _ else _] => let E := fresh "E" in destruct b eqn:E; try discriminate
  | context [match ?e with _ => _ end] => let E := fresh "E" in destruct e eqn:E; try discriminate
  end.
  all: inversion H; subst; apply Zgtb_le; auto.
Qed.

Lemma decode_block_big : forall st hist out b bsm ws, Zlength b > bsm -> decode_block st hist out b bsm ws = None.
Proof.
  unfold decode_block; intros. replace (Zlength b >? bsm) with true by (symmetry; apply Zgtb_gt; auto). auto.
Qed.

Lemma decode_block_nil : forall st hist out bsm ws, decode_block st hist out nil bsm ws = None.
Proof.
  intros. unfold decode_block. destruct (Zlength [] >? bsm); reflexivity.
Qed.

(* the stream's block decoder (dw: dictionary window rule) decodes less than Block.v's, the same where it does *)
Lemma dec_block_lenient : forall dw st hist out b bsm ws x,
  dec_block dw st hist out b bsm ws = Some x -> decode_block st hist out b bsm ws = Some x.
Proof. intros [|] st hist out b bsm ws x H; [exact (pw_decode_block_w _ _ _ _ _ _ _ H)|exact H]. Qed.

Lemma dec_block_len : forall dw st hist out b bsm ws st' c,
  dec_block dw st hist out b bsm ws = Some (st', c) -> Zlength c <= bsm.
Proof. intros. eapply decode_block_len. apply dec_block_lenient in H. exact H. Qed.

Lemma dec_block_big : forall dw st hist out b bsm ws, Zlength b > bsm -> dec_block dw st hist out b bsm ws = None.
Proof.
  intros [|] st hist out b bsm ws H; unfold dec_block; [|apply decode_block_big; auto].
  unfold decode_block_w. replace (Zlength b >? bsm) with true by (symmetry; apply Zgtb_gt; auto). auto.
Qed.

Lemma dec_block_nil : forall dw st hist out bsm ws, dec_block dw st hist out nil bsm ws = None.
Proof.
  intros [|] st hist out bsm ws; unfold dec_block; [|apply decode_block_nil].
  unfold decode_block_w. destruct (Zlength [] >? bsm); reflexivity.
Qed.

(* ---------- the model's content is bytes (for cnt_ok's comparison mod 2^32) ---------- *)

Definition huf_ok (o: option Huffman.huf_table) : Prop :=
  match o with None => True | Some t => (length (Huffman.ht_weights t) <= 256)%nat end.

Definition st_ok (st: dstate) : Prop := huf_ok (st_huf st).

Lemma bytes_ok_repeat : forall x n, is_byte x -> bytes_ok (repeat x n).
Proof. unfold bytes_ok. induction n; simpl; auto. Qed.

Lemma is_byte_byte_at : forall l i, bytes_ok l -> is_byte (byte_at l i).
Proof. intros. apply bytes_ok_byte_at. auto. Qed.

Lemma bytes_ok_slice : forall l i k, bytes_ok l -> bytes_ok (slice l i k).
Proof. intros. unfold slice. apply bytes_ok_firstn, bytes_ok_skipn. auto. Qed.

Lemma huf_cells_range : forall t a b, In (a, b) (Huffman.huf_cells t) ->
  0 <= a < Z.of_nat (length (Huffman.ht_weights t)).
Proof.
  intros t a b H. unfold Huffman.huf_cells in H.
  apply in_flat_map in H. destruct H as [w [_ H]].
  apply in_flat_map in H. destruct H as [s [Hs H]].
  apply in_seq in Hs.
  destruct (_ =? w); [|contradiction].
  apply repeat_spec in H. inversion H; subst. lia.
Qed.

Lemma huf_syms_range : forall t V k pos l p, Huffman.huf_decode_syms t V k pos = Some (l, p) ->
  Forall (fun x => 0 <= x < Z.of_nat (length (Huffman.ht_weights t)) \/ x = 0) l.
Proof.
  induction k; intros; simpl in H. { inversion H; subst; constructor. }
  destruct (nth _ (Huffman.huf_cells t) (0, 0)) as [s nb] eqn:E.
  destruct (pos - nb <? 0); [discriminate|].
  destruct (Huffman.huf_decode_syms t V k (pos - nb)) as [[l' p']|] eqn:E2; [|discriminate].
  inversion H; subst. constructor; eauto.
  match type of E with nth ?i _ _ = _ => destruct (lt_dec i (length (Huffman.huf_cells t))) end.
  - left. eapply huf_cells_range. rewrite <- E. apply nth_In. auto.
  - right. rewrite nth_overflow in E by lia. inversion E; auto.
Qed.

Lemma range_bytes : forall t l, (length (Huffman.ht_weights t) <= 256)%nat ->
  Forall (fun x => 0 <= x < Z.of_nat (length (Huffman.ht_weights t)) \/ x = 0) l -> bytes_ok l.
Proof.
  intros. unfold bytes_ok. eapply Forall_impl; [|eauto]. intros a [Ha|Ha]; unfold is_byte; lia.
Qed.

Lemma huf_stream_bytes : forall t s k l, (length (Huffman.ht_weights t) <= 256)%nat ->
  Huffman.huf_decode_stream t s k = Some l -> bytes_ok l.
Proof.
  unfold Huffman.huf_decode_stream; intros.
  destruct (negb _); [discriminate|].
  destruct (Huffman.huf_decode_syms _ _ _ _) as [[l' p]|] eqn:E; [|discriminate].
  destruct p; try discriminate. inversion H0; subst.
  eapply range_bytes; eauto. eapply huf_syms_range; eauto.
Qed.

Lemma huf_4streams_bytes : forall t s k l, (length (Huffman.ht_weights t) <= 256)%nat ->
  Huffman.huf_decode_4streams t s k = Some l -> bytes_ok l.
Proof.
  unfold Huffman.huf_decode_4streams; intros.
  repeat match type of H0 with context [if ?b then _ else _] => destruct b; [discriminate|] end.
  repeat match type of H0 with
  | context [match Huffman.huf_decode_stream ?a ?b ?c with _ => _ end] =>
      let E := fresh "E" in destruct (Huffman.huf_decode_stream a b c) eqn:E; [|discriminate]
  end.
  inversion H0; subst.
  repeat (apply bytes_ok_app; split); eapply huf_stream_bytes; eauto.
Qed.

Lemma huf_desc_len : forall b ws size, bytes_ok b -> Huffman.huf_desc_weights b = Some (ws, size) ->
  (length ws <= 255)%nat.
Proof.
  unfold Huffman.huf_desc_weights; intros.
  destruct (Zlength b <? 1); [discriminate|].
  pose proof (bytes_ok_byte_at b 0 H).
  destruct (byte_at b 0 >=? 128) eqn:E.
  - destruct (Zlength b <? _); [discriminate|]. inversion H0; subst.
    unfold Huffman.huf_direct_weights. rewrite length_map, length_seq. lia.
  - destruct (Zlength b <? _); [discriminate|].
    destruct (Huffman.huf_fse_weights _) as [ws'|] eqn:F; [|discriminate]. inversion H0; subst.
    unfold Huffman.huf_fse_weights in F.
    repeat match type of F with
    | context [match ?e with _ => _ end] => let E := fresh "E" in destruct e eqn:E; try discriminate
    | context [if ?b then _ else _] => let E := fresh "E" in destruct b eqn:E; try discriminate
    end.
    all: inversion F; subst; apply Zgtb_le in E5 || idtac; rewrite Zlength_correct in *; lia.
Qed.

Lemma huf_parse_len : forall b t size, bytes_ok b -> Huffman.huf_parse_desc b = Some (t, size) ->
  (length (Huffman.ht_weights t) <= 256)%nat.
Proof.
  unfold Huffman.huf_parse_desc; intros.
  destruct (Huffman.huf_desc_weights b) as [[ws sz]|] eqn:E; [|discriminate].
  pose proof (huf_desc_len _ _ _ H E).
  repeat match type of H0 with context [if ?c then _ else _] => destruct c; [discriminate|] end.
  inversion H0; subst. simpl. rewrite length_app. simpl. lia.
Qed.

Lemma decode_literals_bytes : forall hprev b bsm lits used huf, bytes_ok b -> huf_ok hprev ->
  decode_literals hprev b bsm = Some (lits, used, huf) -> bytes_ok lits /\ huf_ok huf.
Proof.
  intros hprev b bsm lits used huf Hb Hh H. unfold decode_literals in H.
  repeat match type of H with
  | context [match ?e with _ => _ end] => let E := fresh "E" in destruct e eqn:E; try discriminate
  | context [if ?c then _ else _] => let E := fresh "E" in destruct c eqn:E; try discriminate
  end.
  all: inversion H; subst; clear H.
  all: try (split; [apply bytes_ok_slice; auto | auto]).
  all: try (split; [apply bytes_ok_repeat, is_byte_byte_at; auto | auto]).
  all: match goal with
       | E10: (if _ then _ else _) = Some (?h, ?z2), E12: (if ?b0 then _ else _) = Some ?ll |- _ =>
         assert (Hh': (length (Huffman.ht_weights h) <= 256)%nat);
         [ destruct (Z.land (byte_at b 0) 3 =? 2);
           [ destruct (Huffman.huf_parse_desc _) as [[t hs]|] eqn:P; [|discriminate];
             destruct (_ >=? _); [discriminate|]; inversion E10; subst;
             eapply huf_parse_len; [|exact P]; apply bytes_ok_slice; auto
           | destruct hprev; [|discriminate]; inversion E10; subst; exact Hh ]
         | split; [destruct b0; [eapply huf_stream_bytes | eapply huf_4streams_bytes]; eauto | simpl; auto] ]
       end.
Qed.

Lemma lz_copy_bytes : forall hist out offset ml, bytes_ok hist -> bytes_ok out ->
  bytes_ok (lz_copy hist out offset ml).
Proof.
  intros hist out offset ml. revert out. induction ml; intros; simpl; auto.
  apply IHml; auto. apply bytes_ok_app. split; auto.
  constructor; [|constructor]. apply is_byte_byte_at. apply bytes_ok_app; auto.
Qed.

Lemma exec_seqs_bytes : forall wsize seqs rep hist lits out out' lits' rep',
  bytes_ok hist -> bytes_ok lits -> bytes_ok out ->
  exec_seqs wsize rep hist lits out seqs = Some (out', lits', rep') -> bytes_ok out' /\ bytes_ok lits'.
Proof.
  intros wsize seqs. induction seqs; intros; simpl in H2.
  - inversion H2; subst. auto.
  - destruct (_ >? _); [discriminate|].
    destruct (resolve_offset _ _ _) as [[offset rep2]|]; [|discriminate].
    destruct (_ >? _); [discriminate|]. destruct (_ >? _); [discriminate|].
    eapply IHseqs; [| | |exact H2]; auto.
    + apply bytes_ok_skipn; auto.
    + apply lz_copy_bytes; auto. apply bytes_ok_app. split; auto. apply bytes_ok_firstn; auto.
Qed.

Lemma decode_block_bytes : forall st hist out b bsm ws st' c, bytes_ok hist -> bytes_ok out -> bytes_ok b ->
  st_ok st -> decode_block st hist out b bsm ws = Some (st', c) -> bytes_ok c /\ st_ok st'.
Proof.
  intros st hist out b bsm ws st' c Hh Ho Hb Hs H. unfold decode_block in H.
  destruct (_ >? _); [discriminate|].
  destruct (decode_literals _ _ _) as [[[lits lused] huf]|] eqn:L; [|discriminate].
  destruct (decode_literals_bytes _ _ _ _ _ _ Hb Hs L) as [Hl Hhf].
  destruct (decode_seq_header _ _) as [[[nbSeq tabs] hused]|]; [|discriminate].
  match type of H with context [match ?e with Some _ => _ | None => None end] =>
    destruct e as [seqs|]; [|discriminate] end.
  destruct (exec_seqs _ _ _ _ _ _) as [[[out' lits'] rep']|] eqn:X; [|discriminate].
  destruct (_ >? _); [discriminate|]. inversion H; subst.
  destruct (exec_seqs_bytes _ _ _ _ _ _ _ _ _ Hh Hl Ho X).
  split; [|unfold st_ok; simpl; auto].
  apply bytes_ok_skipn. apply bytes_ok_app; auto.
Qed.

Lemma dec_block_bytes : forall dw st hist out b bsm ws st' c, bytes_ok hist -> bytes_ok out -> bytes_ok b ->
  st_ok st -> dec_block dw st hist out b bsm ws = Some (st', c) -> bytes_ok c /\ st_ok st'.
Proof. intros. apply dec_block_lenient in H3. exact (decode_block_bytes _ _ _ _ _ _ _ _ H H0 H1 H2 H3). Qed.

Lemma block_res_bytes : forall dw st hist s out bsm ws st' out' k last, bytes_ok hist -> bytes_ok s -> bytes_ok out ->
  st_ok st -> block_res dw st hist s out bsm ws = Some (st', out', k, last) -> bytes_ok out' /\ st_ok st'.
Proof.
  intros. unfold block_res in H3.
  destruct (cblock_size s); [|discriminate]. destruct (_ >? _); [discriminate|]. cbv zeta in H3.
  destruct (bp_type _ =? 0); [|destruct (bp_type _ =? 1)].
  - destruct (_ >? _); [discriminate|]. inversion H3; subst.
    split; auto. apply bytes_ok_app. split; auto. apply bytes_ok_slice; auto.
  - destruct (_ || _); [discriminate|]. inversion H3; subst.
    split; auto. apply bytes_ok_app. split; auto. apply bytes_ok_repeat, is_byte_byte_at, bytes_ok_slice; auto.
  - destruct (dec_block _ _ _ _ _ _ _) as [[st2 c2]|] eqn:D; [|discriminate]. inversion H3; subst.
    destruct (dec_block_bytes _ _ _ _ _ _ _ _ _ H H1 (bytes_ok_slice _ _ _ H0) H2 D).
    split; auto. apply bytes_ok_app; auto.
Qed.

Lemma bp_bytes : forall dw hist bsm ws ts0 bl ts out last, blocks_pre dw hist bsm ws ts0 bl ts out last ->
  bytes_ok hist -> st_ok ts0 -> bytes_ok bl -> bytes_ok out /\ st_ok ts.
Proof.
  induction 1; intros Hh Hs0 Hbl.
  - split; [constructor|auto].
  - apply bytes_ok_app in Hbl. destruct Hbl as [H1 H2]. destruct (IHblocks_pre Hh Hs0 H1).
    exact (block_res_bytes _ _ _ _ _ _ _ _ _ _ _ Hh H2 H3 H4 H0).
Qed.

Lemma map_mod_bytes : forall l, bytes_ok l -> map (fun b => b mod 2 ^ 32) l = l.
Proof.
  induction l; intros; cbn [map]; auto. inversion H; subst. unfold is_byte in H2.
  rewrite IHl by auto. rewrite Z.mod_small by lia. auto.
Qed.

Lemma fcs_ok_dec : forall h out, fcs_ok h out \/ ~ fcs_ok h out.
Proof.
  unfold fcs_ok; intros.
  destruct (Z.eq_dec (fh_contentSize h) ZSTD_CONTENTSIZE_UNKNOWN); [tauto|].
  destruct (Z.eq_dec (Zlength out) (fh_contentSize h)); tauto.
Qed.

Lemma gfh_ck : forall s h, get_frame_header s = FH_ok h -> fh_checksumFlag h = 0 \/ fh_checksumFlag h = 1.
Proof.
  intros s h H. pose proof (gfh_len _ _ H) as Hn.
  unfold get_frame_header in H. cbv zeta in H.
  replace (Zlength s <? 5) with false in H by (symmetry; apply Z.ltb_ge; lia).
  destruct (negb (le_field s 0 4 =? ZSTD_MAGICNUMBER)).
  { destruct (is_skippable_magic _); [|discriminate].
    destruct (Zlength s <? ZSTD_SKIPPABLEHEADERSIZE); [discriminate|]. inversion H; subst. auto. }
  destruct (Zlength s <? _); [discriminate|]. destruct (negb _); [discriminate|].
  destruct (_ && _); [discriminate|]. inversion H; subst. simpl. apply land1_cases.
Qed.

Lemma gfhm_ck : forall mg s h, get_frame_header_m mg s = FH_ok h -> fh_checksumFlag h = 0 \/ fh_checksumFlag h = 1.
Proof.
  intros [|] s h H.
  - destruct (gfhm_true _ _ H) as [h' [G [-> _]]]. cbn [fh_unshift fh_checksumFlag]. eapply gfh_ck; eauto.
  - eapply gfh_ck; eauto.
Qed.
