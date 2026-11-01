(* The format model: series of frames zstd certainly refuses, where decode_frame_m answers FUnk (no claim).  Plain
   Coq, an addition to model/Params.v (nothing there changes).

   A Zstandard frame is certainly refused (frame_refused_m) when
   - its header is cut: the bytes end before the header's last byte (ZSTD_decompressFrame: srcSize_wrong;
     streaming waits for the rest of the header and never ends the frame); or
   - its header is complete and accepted (FH_ok, a Zstandard frame, Window_Size within wlim, a Dictionary_ID of 0
     or the dictionary's) and the walk over its blocks, as zstd makes it, reaches
     . a block header past the end of the bytes, or a block's content past the end (srcSize_wrong; streaming
       waits for it),
     . a block header of Block_Type 3 (ZSTD_getcBlockSize: corruption_detected), or
     . after the last block: a Frame_Content_Size other than the content's size (the check at the end of
       ZSTD_decompressFrame, ZSTD_decompressContinue's at the last block and fix F6 for an empty last block:
       corruption_detected), or a Content_Checksum cut short (checksum_wrong; streaming waits for it).
   The walk goes through Raw and RLE blocks of any size: ZSTD_decompressFrame copies them without comparing their
   size with Block_Maximum_Size, and streaming refuses a larger one at its header (corruption_detected), which
   refuses the frame as well.  It goes through compressed blocks the model decodes (Block.decode_block, with the
   dictionary window rule when md_dwin, as decode_frame_m), and stops (no claim) at one it does not.

   A series is certainly refused (series_refused_m) when the walk of Params.walk_m over it (frames the model
   decodes, skippable frames) ends at a refused Zstandard frame, or at a non-empty rest shorter than a frame's
   first bytes (ZSTD_startingInputLength: ZSTD_decompressMultiFrame's "input not entirely consumed").  Its frames
   before the refused one are those of series_frames_m and its tail is TUnk (series_refused_tunk).

   The specifications use it with no_wlim: ZSTD_decompress* return an error on a refused series
   (Spec_api6.oneshot_ok, oneshot_sel), and ZSTD_decompressStream returns 0 on one only at the end of a frame
   before the refused one (stream_zero_ref). *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Block Zstd.proof.model.Series.
Require Import Zstd.proof.model.StreamModel Zstd.proof.model.Params.
Local Open Scope bool_scope.

(* ---------- the blocks of a refused frame ---------- *)

(* the block decoder of the model: with the dictionary window rule (dw = md_dwin) or Block.v's *)
Definition rdec_block (dw: bool) : dstate -> list Z -> list Z -> list Z -> Z -> Z -> option (dstate * list Z) :=
  if dw then decode_block_w else decode_block.

(* the block at the start of s (c = cblock_size s, its content in s) decoded as zstd decodes it when it accepts it,
   after the frame's output out: Raw and RLE blocks of any size, compressed blocks as the model decodes them *)
Definition rblock (dw: bool) (st: dstate) (hist s out: list Z) (c bsm wsize: Z) : option (dstate * list Z) :=
  let bp := block_props_of s in
  let body := slice s ZSTD_blockHeaderSize c in
  if bp_type bp =? 0 then Some (st, out ++ body)
  else if bp_type bp =? 1 then Some (st, out ++ repeat (byte_at body 0) (Z.to_nat (bp_origSize bp)))
  else match rdec_block dw st hist out body bsm wsize with
       | Some (st', content) => Some (st', out ++ content)
       | None => None
       end.

(* the end of a frame zstd refuses, after its last block: the frame's content out and the bytes after the last
   block *)
Definition frame_end_refused (h: frame_header) (out after: list Z) : Prop :=
  (fh_contentSize h <> ZSTD_CONTENTSIZE_UNKNOWN /\ Zlength out mod 2 ^ 64 <> fh_contentSize h) \/
  (fh_checksumFlag h = 1 /\ Zlength after < 4).

(* the blocks from s on (at a block header), after the frame's output out, end refused *)
Fixpoint blocks_refused (dw: bool) (fuel: nat) (h: frame_header) (st: dstate) (hist s out: list Z) (bsm: Z) : Prop :=
  match fuel with
  | O => False
  | S f =>
      if Zlength s <? ZSTD_blockHeaderSize then True else
      if bp_type (block_props_of s) =? 3 then True else
      match cblock_size s with
      | None => False
      | Some c =>
          if c >? Zlength s - ZSTD_blockHeaderSize then True else
          match rblock dw st hist s out c bsm (fh_windowSize h) with
          | None => False
          | Some (st', out') =>
              let after := skipn (Z.to_nat (ZSTD_blockHeaderSize + c)) s in
              if bp_last (block_props_of s) =? 1 then frame_end_refused h out' after
              else blocks_refused dw f h st' hist after out' bsm
          end
      end
  end.

(* ---------- frames ---------- *)

(* the Zstandard frame at the start of s (not a skippable one; at least ZSTD_startingInputLength bytes), decoded
   with the dictionary dm under the mode md and the window limit wlim, is certainly refused *)
Definition frame_refused_m (md: dmode) (dm: dict_model) (wlim: Z) (s: list Z) : Prop :=
  let mg := md_magicless md in
  if Zlength s <? header_size_m mg s then True else
  match get_frame_header_m mg s with
  | FH_ok h =>
      fh_windowSize h <= wlim /\ fh_frameType h = 0 /\ (fh_dictID h = 0 \/ fh_dictID h = dm_id dm) /\
      let rest := skipn (Z.to_nat (fh_headerSize h)) s in
      blocks_refused (md_dwin md) (S (length rest)) h (dm_state dm) (dm_content dm) rest nil
        (Z.min (fh_blockSizeMax h) (md_bmax md))
  | _ => False
  end.

(* ---------- series ---------- *)

(* the walk of Params.walk_m ends at a refused frame, or at a non-empty rest shorter than a frame's start *)
Fixpoint walk_refused (fuel: nat) (md: dmode) (sel: Z -> option dict_model) (cur: option dict_model) (wlim: Z)
    (s: list Z) : Prop :=
  match fuel with
  | O => False
  | S f =>
      let mg := md_magicless md in
      if Zlength s <? starting_len mg then Zlength s <> 0 else
      if negb mg && is_skippable_magic (le_field s 0 4) then
        match skippable_frame_size s with
        | None => False
        | Some k =>
            let cur' := if md_dwin md
                        then match sel (Z.land (le_field s 0 4) 15) with Some d => Some d | None => cur end
                        else cur in
            walk_refused f md sel cur' wlim (skipn (Z.to_nat k) s)
        end
      else
        match frame_dict mg sel cur s with
        | None => False
        | Some d =>
            match decode_frame_m md d wlim s with
            | FOk _ k => walk_refused f md sel (Some d) wlim (skipn (Z.to_nat k) s)
            | FUnk => frame_refused_m md d wlim s
            | _ => False
            end
        end
  end.

Definition series_refused_m (md: dmode) (sel: Z -> option dict_model) (cur: option dict_model) (wlim: Z)
    (s: list Z) : Prop :=
  walk_refused (S (length s)) md sel cur wlim s.

(* ---------- what streaming promises on a refused series ---------- *)

(* ZSTD_decompressStream returning 0 (a frame completely decoded and flushed) after reading sin and delivering sout,
   on any byte series s it may be the beginning of that ends refused: sin ends one of the frames of s before the
   refused one, and sout is the content of the frames up to it (Params.stream_claims_m's zero clause, for these
   series).  A single refused frame has no frame before it: no call returns 0 on it. *)
Definition stream_zero_ref (md: dmode) (sel: Z -> option dict_model) (dm: option dict_model) (sin sout: list Z)
    (r: Z) : Prop :=
  forall s, bytes_ok s -> is_prefix sin s -> series_refused_m md sel dm no_wlim s -> r = 0 ->
    let fl0 := fst (series_frames_m md sel dm no_wlim s) in
    exists n, (1 <= n <= length fl0)%nat /\
      Zlength sin = fr_end (nth (n - 1) fl0 fr_dflt) /\
      sout = flat_map fr_content (firstn n fl0).

(* ---------- facts ---------- *)

(* ---------- helpers: bytes and fields ---------- *)

Lemma rf_ok_skipn: forall (l: list Z) n, bytes_ok l -> bytes_ok (skipn n l).
Proof.
  unfold bytes_ok. induction l as [|a l IH]; intros [|n] H; simpl; auto.
  inversion H; subst; auto.
Qed.

Lemma rf_ok_firstn: forall (l: list Z) n, bytes_ok l -> bytes_ok (firstn n l).
Proof.
  unfold bytes_ok. induction l as [|a l IH]; intros [|n] H; simpl; auto.
  inversion H; subst; constructor; auto.
Qed.

Lemma rf_zlength_skipn: forall (l: list Z) n, 0 <= n <= Zlength l ->
  Zlength (skipn (Z.to_nat n) l) = Zlength l - n.
Proof.
  intros l n H. rewrite !Zlength_correct in *. rewrite skipn_length.
  rewrite Nat2Z.inj_sub, Z2Nat.id; [lia|lia|].
  apply Nat2Z.inj_le. rewrite Z2Nat.id; lia.
Qed.

Lemma rf_le_value_range: forall l, bytes_ok l -> 0 <= le_value l < 2 ^ (8 * Zlength l).
Proof.
  induction l as [|a l IH]; intros H; [simpl; lia|].
  inversion H as [|? ? Ha Hl]; subst. specialize (IH Hl). unfold is_byte in Ha.
  rewrite Zlength_cons. assert (0 <= Zlength l) by (rewrite Zlength_correct; lia).
  replace (8 * Z.succ (Zlength l)) with (8 + 8 * Zlength l) by lia.
  rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256. cbn [le_value]. nia.
Qed.

Lemma rf_le_field_range: forall s i k, bytes_ok s -> 0 <= k -> 0 <= le_field s i k < 2 ^ (8 * k).
Proof.
  intros s i k Hb Hk. unfold le_field, slice.
  assert (Ho: bytes_ok (firstn (Z.to_nat k) (skipn (Z.to_nat i) s))) by (apply rf_ok_firstn, rf_ok_skipn; auto).
  pose proof (rf_le_value_range _ Ho) as R.
  assert (Zlength (firstn (Z.to_nat k) (skipn (Z.to_nat i) s)) <= k).
  { rewrite Zlength_correct. pose proof (firstn_le_length (Z.to_nat k) (skipn (Z.to_nat i) s)).
    apply Nat2Z.inj_le in H. rewrite Z2Nat.id in H; lia. }
  split; [lia|]. eapply Z.lt_le_trans; [apply R|]. apply Z.pow_le_mono_r; lia.
Qed.

Lemma rf_byte_at_range: forall s i, bytes_ok s -> 0 <= byte_at s i < 256.
Proof.
  intros s i. unfold byte_at. generalize (Z.to_nat i). unfold bytes_ok.
  induction s as [|a s IH]; intros [|n] H; simpl; try lia; inversion H; subst; auto.
Qed.

Lemma rf_land1: forall x, Z.land x 1 = 0 \/ Z.land x 1 = 1.
Proof.
  intros x. pose proof (Z.land_ones x 1 ltac:(lia)) as E. change (Z.ones 1) with 1 in E.
  rewrite E. pose proof (Z.mod_pos_bound x (2 ^ 1) ltac:(lia)). change (2 ^ 1) with 2 in *. lia.
Qed.

Lemma rf_fhd_hs: forall b, 5 <= fhd_header_size b.
Proof.
  intros b. unfold fhd_header_size.
  assert (N: forall n, 0 <= nth n [0; 1; 2; 4] 0) by (intros [|[|[|[|[|n]]]]]; simpl; lia).
  assert (N': forall n, 0 <= nth n [0; 2; 4; 8] 0) by (intros [|[|[|[|[|n]]]]]; simpl; lia).
  pose proof (N (Z.to_nat (Z.land b 3))). pose proof (N' (Z.to_nat (Z.shiftr b 6))).
  destruct (_ && _); destruct (rf_land1 (Z.shiftr b 5)) as [-> | ->]; lia.
Qed.

(* ---------- helpers: the frame header ---------- *)

(* what a Zstandard frame header (zstd1) get_frame_header accepts says about its bytes: the checks of
   decode_frame_m before get_frame_header_m pass, and Frame_Content_Size fits in 64 bits *)
Lemma rf_gfh: forall s h, bytes_ok s -> get_frame_header s = FH_ok h -> fh_frameType h = 0 ->
  le_field s 0 4 = ZSTD_MAGICNUMBER /\ fh_headerSize h = fhd_header_size (byte_at s 4) /\
  fh_headerSize h <= Zlength s /\ Z.land (byte_at s 4) 8 = 0 /\
  negb (Z.land (Z.shiftr (byte_at s 4) 5) 1 =? 1) &&
    (Z.shiftr (byte_at s 5) 3 + ZSTD_WINDOWLOG_ABSOLUTEMIN >? ZSTD_WINDOWLOG_MAX) = false /\
  fh_contentSize h < 2 ^ 64.
Proof.
  intros s h Hb G Ht. unfold get_frame_header in G.
  destruct (Zlength s <? 5).
  { repeat match type of G with context [if ?c then _ else _] => destruct c end; discriminate. }
  destruct (Z.eqb_spec (le_field s 0 4) ZSTD_MAGICNUMBER) as [M|M]; cbn [negb] in G.
  2:{ destruct (is_skippable_magic (le_field s 0 4)); [|discriminate].
      destruct (Zlength s <? ZSTD_SKIPPABLEHEADERSIZE); [discriminate|].
      injection G as <-. discriminate. }
  destruct (Z.ltb_spec (Zlength s) (fhd_header_size (byte_at s 4))); [discriminate|].
  destruct (Z.eqb_spec (Z.land (byte_at s 4) 8) 0) as [R|R]; cbn [negb] in G; [|discriminate].
  destruct (rf_land1 (Z.shiftr (byte_at s 4) 5)) as [S1|S1]; rewrite S1 in G |- *; cbn [Z.eqb negb andb] in G |- *.
  - destruct (Z.shiftr (byte_at s 5) 3 + ZSTD_WINDOWLOG_ABSOLUTEMIN >? ZSTD_WINDOWLOG_MAX); [discriminate|].
    injection G as <-. cbn [fh_headerSize fh_contentSize].
    repeat split; auto.
    repeat match goal with |- context [if ?c then _ else _] => destruct c end;
      try (unfold ZSTD_CONTENTSIZE_UNKNOWN; lia);
      match goal with |- le_field ?s ?p ?k + _ < _ => pose proof (rf_le_field_range s p k Hb ltac:(lia))
                    | |- le_field ?s ?p ?k < _ => pose proof (rf_le_field_range s p k Hb ltac:(lia))
                    | |- byte_at ?s ?p < _ => pose proof (rf_byte_at_range s p Hb) end;
      cbn in *; lia.
  - injection G as <-. cbn [fh_headerSize fh_contentSize].
    repeat split; auto.
    repeat match goal with |- context [if ?c then _ else _] => destruct c end;
      try (unfold ZSTD_CONTENTSIZE_UNKNOWN; lia);
      match goal with |- le_field ?s ?p ?k + _ < _ => pose proof (rf_le_field_range s p k Hb ltac:(lia))
                    | |- le_field ?s ?p ?k < _ => pose proof (rf_le_field_range s p k Hb ltac:(lia))
                    | |- byte_at ?s ?p < _ => pose proof (rf_byte_at_range s p Hb) end;
      cbn in *; lia.
Qed.

(* ---------- helpers: the blocks ---------- *)

(* one step of the block decoder decode_frame_m runs (with or without the dictionary window rule) *)
Lemma rf_dec_step: forall (dw: bool) g st hist s out bsm ws,
  (if dw then decode_blocks_w else decode_blocks) (S g) st hist s out bsm ws =
  match cblock_size s with
  | None => None
  | Some c =>
      if c >? Zlength s - ZSTD_blockHeaderSize then None else
      let bp := block_props_of s in
      let body := slice s ZSTD_blockHeaderSize c in
      let res :=
        if bp_type bp =? 0 then
          (if c >? bsm then None else Some (st, out ++ body))
        else if bp_type bp =? 1 then
          (if (bp_origSize bp >? bsm) || (c >? bsm) then None
           else Some (st, out ++ repeat (byte_at body 0) (Z.to_nat (bp_origSize bp))))
        else
          match rdec_block dw st hist out body bsm ws with
          | Some (st', content) => Some (st', out ++ content)
          | None => None
          end in
      match res with
      | None => None
      | Some (st', out') =>
          if bp_last bp =? 1 then Some (out', ZSTD_blockHeaderSize + c)
          else match (if dw then decode_blocks_w else decode_blocks)
                       g st' hist (skipn (Z.to_nat (ZSTD_blockHeaderSize + c)) s) out' bsm ws with
               | Some (o, k) => Some (o, ZSTD_blockHeaderSize + c + k)
               | None => None
               end
      end
  end.
Proof. intros [|]; reflexivity. Qed.

(* the decoder of decode_frame_m, with any fuel, on blocks blocks_refused calls refused: no result, or a result
   whose end (content size, checksum length) decode_frame_m refuses *)
Lemma rf_blocks: forall (dw: bool) h hist bsm f g st s out, bytes_ok s -> blocks_refused dw f h st hist s out bsm ->
  match (if dw then decode_blocks_w else decode_blocks) g st hist s out bsm (fh_windowSize h) with
  | None => True
  | Some (o, k) =>
      (fh_contentSize h <> ZSTD_CONTENTSIZE_UNKNOWN /\ Zlength o mod 2 ^ 64 <> fh_contentSize h) \/
      (fh_checksumFlag h = 1 /\ Zlength s - k < 4)
  end.
Proof.
  intros dw h hist bsm f. induction f as [|f IH]; intros g st s out Hb H; [contradiction|].
  destruct g as [|g]; [destruct dw; exact I|].
  rewrite rf_dec_step. cbn [blocks_refused] in H. unfold cblock_size in *. cbv zeta in *.
  destruct (Z.ltb_spec (Zlength s) ZSTD_blockHeaderSize); [exact I|].
  destruct (Z.eqb_spec (bp_type (block_props_of s)) 3) as [T3|T3].
  { rewrite T3. exact I. }
  set (c := if bp_type (block_props_of s) =? 1 then 1 else bp_origSize (block_props_of s)).
  assert (Ec: (if bp_type (block_props_of s) =? 1 then Some 1 else Some (bp_origSize (block_props_of s)))
              = Some c) by (subst c; destruct (bp_type (block_props_of s) =? 1); reflexivity).
  rewrite Ec in H |- *.
  assert (Hc0: 0 <= c).
  { subst c. destruct (_ =? 1); [lia|]. unfold block_props_of. cbn [bp_origSize].
    pose proof (rf_le_field_range s 0 3 Hb ltac:(lia)). apply Z.shiftr_nonneg. lia. }
  destruct (Z.gtb_spec c (Zlength s - ZSTD_blockHeaderSize)); [exact I|].
  unfold rblock, rdec_block in H.
  set (body := slice s ZSTD_blockHeaderSize c) in *.
  assert (Ha: Zlength (skipn (Z.to_nat (ZSTD_blockHeaderSize + c)) s) = Zlength s - (ZSTD_blockHeaderSize + c))
    by (apply rf_zlength_skipn; unfold ZSTD_blockHeaderSize in *; lia).
  assert (Hba: bytes_ok (skipn (Z.to_nat (ZSTD_blockHeaderSize + c)) s)) by (apply rf_ok_skipn; auto).
  (* the step's result: none, or the one of rblock *)
  match goal with |- match match ?r with _ => _ end with _ => _ end => destruct r as [[st' out']|] eqn:R end;
    [|exact I].
  match type of H with context [match ?r with Some _ => _ | None => False end] =>
    replace r with (Some (st', out')) in H end.
  2:{ revert R. unfold rdec_block.
      destruct (bp_type (block_props_of s) =? 0); [destruct (c >? bsm); [discriminate|]; auto|].
      destruct (bp_type (block_props_of s) =? 1); [destruct (_ || _); [discriminate|]; auto|].
      intros E; symmetry; exact E. }
  destruct (bp_last (block_props_of s) =? 1).
  - unfold frame_end_refused in H. rewrite Ha in H. unfold ZSTD_blockHeaderSize in *.
    destruct H as [H|[HK1 HK2]]; [left; exact H | right; split; [exact HK1 | lia]].
  - specialize (IH g st' _ out' Hba H).
    destruct ((if dw then decode_blocks_w else decode_blocks) g st' hist _ out' bsm (fh_windowSize h))
      as [[o k]|]; [|exact I].
    rewrite Ha in IH. destruct IH as [IH|[HK1 HK2]]; [left; exact IH | right; split; [exact HK1 | lia]].
Qed.

(* a magicless header is read behind the zstd magic number (get_frame_header_m) *)
Lemma rf_magic: magic_bytes = [40; 181; 47; 253].
Proof. reflexivity. Qed.

Lemma rf_magic_byte4: forall s, byte_at (magic_bytes ++ s) 4 = byte_at s 0.
Proof. intros. rewrite rf_magic. reflexivity. Qed.

Lemma rf_magic_byte5: forall s, byte_at (magic_bytes ++ s) 5 = byte_at s 1.
Proof. intros. rewrite rf_magic. reflexivity. Qed.

Lemma rf_magic_len: forall s, Zlength (magic_bytes ++ s) = Zlength s + 4.
Proof. intros. rewrite rf_magic, !Zlength_correct, app_length. simpl length. lia. Qed.

Lemma rf_magic_ok: forall s, bytes_ok s -> bytes_ok (magic_bytes ++ s).
Proof.
  intros. unfold bytes_ok. apply Forall_app. split; [|exact H].
  rewrite rf_magic. repeat constructor; unfold is_byte; lia.
Qed.

(* decode_frame_m after an accepted Zstandard frame header h whose blocks blocks_refused calls refused *)
Lemma rf_tail: forall md dm s h, bytes_ok s -> 0 <= fh_headerSize h <= Zlength s -> fh_contentSize h < 2 ^ 64 ->
  fh_frameType h = 0 -> (fh_dictID h = 0 \/ fh_dictID h = dm_id dm) ->
  blocks_refused (md_dwin md) (S (length (skipn (Z.to_nat (fh_headerSize h)) s))) h (dm_state dm) (dm_content dm)
    (skipn (Z.to_nat (fh_headerSize h)) s) nil (Z.min (fh_blockSizeMax h) (md_bmax md)) ->
  (if negb (fh_frameType h =? 0) then FUnk else
   if negb (fh_dictID h =? 0) && negb (fh_dictID h =? dm_id dm) then FUnk else
   let hs := fh_headerSize h in
   let rest := skipn (Z.to_nat hs) s in
   let bsm := Z.min (fh_blockSizeMax h) (md_bmax md) in
   match (if md_dwin md then decode_blocks_w else decode_blocks)
           (length rest) (dm_state dm) (dm_content dm) rest nil bsm (fh_windowSize h) with
   | None => FUnk
   | Some (out, k) =>
       if negb (fh_contentSize h =? ZSTD_CONTENTSIZE_UNKNOWN) && negb (Zlength out =? fh_contentSize h)
       then FUnk else
       if fh_checksumFlag h =? 1 then
         (if Zlength s - hs - k <? 4 then FUnk
          else if negb (md_ignore md) && negb (le_field s (hs + k) 4 =? Zstd.proof.model.Xxh64.xxh64 out 0 mod 2 ^ 32) then FDetCk
          else FOk out (hs + k + 4))
       else FOk out (hs + k)
   end) = FUnk.
Proof.
  intros md dm s h Hb Hhs Hfcs Ht Hd Hr. rewrite Ht. cbn [Z.eqb negb Pos.eqb].
  assert (D: negb (fh_dictID h =? 0) && negb (fh_dictID h =? dm_id dm) = false)
    by (destruct Hd as [-> | ->]; rewrite Z.eqb_refl; [reflexivity | destruct (negb (_ =? 0)); reflexivity]).
  rewrite D. cbv zeta.
  pose proof (rf_blocks (md_dwin md) h (dm_content dm) _ _
                (length (skipn (Z.to_nat (fh_headerSize h)) s)) (dm_state dm) _ nil (rf_ok_skipn _ _ Hb) Hr) as B.
  destruct ((if md_dwin md then decode_blocks_w else decode_blocks) _ _ _ _ _ _ _) as [[o k]|]; [|reflexivity].
  rewrite rf_zlength_skipn in B by lia.
  destruct B as [[B1 B2]|[B1 B2]].
  - destruct (Z.eqb_spec (Zlength o) (fh_contentSize h)) as [E|E].
    + exfalso. apply B2. rewrite <- E. apply Z.mod_small.
      assert (0 <= Zlength o) by (rewrite Zlength_correct; lia). lia.
    + apply Z.eqb_neq in B1. rewrite B1. reflexivity.
  - rewrite B1. destruct (negb (fh_contentSize h =? ZSTD_CONTENTSIZE_UNKNOWN) && _); [reflexivity|]. cbn [Z.eqb Pos.eqb].
    destruct (Z.ltb_spec (Zlength s - fh_headerSize h - k) 4); [reflexivity|lia].
Qed.

(* a refused frame is one decode_frame_m answers FUnk for *)
Lemma frame_refused_funk: forall md dm wlim s,
  bytes_ok s -> starting_len (md_magicless md) <= Zlength s ->
  (md_magicless md = true \/ le_field s 0 4 = ZSTD_MAGICNUMBER \/ Zlength s < header_size_m (md_magicless md) s) ->
  frame_refused_m md dm wlim s -> decode_frame_m md dm wlim s = FUnk.
Proof.
  intros md dm wlim s Hb Hst _ Hr. unfold frame_refused_m, decode_frame_m in *. cbv zeta in *.
  destruct (md_magicless md) eqn:Mg; cbn [negb andb starting_len header_size_m] in *.
  - (* magicless: the header is read behind a magic number *)
    change (4 - 4) with 0. change (5 - 4) with 1.
    destruct (Z.ltb_spec (Zlength s) (fhd_header_size (byte_at s 0) - 4)) as [Hc|Hc].
    + destruct (Zlength s <? _); [reflexivity|].
      destruct (Z.ltb_spec (Zlength s) (fhd_header_size (byte_at s 0) - 4 + ZSTD_blockHeaderSize));
        [reflexivity | unfold ZSTD_blockHeaderSize in *; lia].
    + destruct (get_frame_header_m true s) as [| |h] eqn:G; try contradiction.
      destruct Hr as (Hw & Ht & Hd & Hbl).
      assert (G' := G). unfold get_frame_header_m in G'. cbn [negb] in G'.
      destruct (Zlength s <? 1); [discriminate|].
      destruct (get_frame_header (magic_bytes ++ s)) as [| |h'] eqn:G''; try discriminate.
      injection G' as <-.
      destruct (rf_gfh _ _ (rf_magic_ok s Hb) G'' Ht) as (_ & Hhs & Hhl & R & W & Hfcs).
      rewrite rf_magic_byte4 in Hhs, R, W. rewrite rf_magic_byte5 in W. rewrite rf_magic_len in Hhl.
      pose proof (rf_fhd_hs (byte_at s 0)).
      destruct (Zlength s <? _); [reflexivity|].
      destruct (Zlength s <? _); [reflexivity|].
      rewrite R, W. cbn [Z.eqb negb].
      destruct (Z.gtb_spec (fh_windowSize (fh_unshift h')) wlim); [lia|].
      apply rf_tail; auto; cbn [fh_unshift fh_headerSize fh_contentSize]; lia.
  - (* zstd1 *)
    change (4 - 0) with 4. change (5 - 0) with 5.
    destruct (Z.ltb_spec (Zlength s) (fhd_header_size (byte_at s 4))) as [Hc|Hc].
    + destruct (Zlength s <? _); [reflexivity|].
      destruct (negb (le_field s 0 4 =? ZSTD_MAGICNUMBER)); [reflexivity|].
      destruct (Z.ltb_spec (Zlength s) (fhd_header_size (byte_at s 4) - 0 + ZSTD_blockHeaderSize));
        [reflexivity | unfold ZSTD_blockHeaderSize in *; lia].
    + destruct (get_frame_header_m false s) as [| |h] eqn:G; try contradiction.
      destruct Hr as (Hw & Ht & Hd & Hbl).
      assert (G' := G). cbn [get_frame_header_m negb] in G'.
      destruct (rf_gfh _ _ Hb G' Ht) as (M & Hhs & Hhl & R & W & Hfcs).
      pose proof (rf_fhd_hs (byte_at s 4)).
      destruct (Zlength s <? _); [reflexivity|].
      rewrite M, Z.eqb_refl. cbn [negb].
      destruct (Zlength s <? _); [reflexivity|].
      rewrite R, W. cbn [Z.eqb negb].
      destruct (Z.gtb_spec (fh_windowSize h) wlim); [lia|].
      apply rf_tail; auto; lia.
Qed.

(* walk_refused follows walk_m's branches and ends where walk_m answers TUnk *)
Lemma rf_walk: forall fuel md sel cur wlim s off,
  walk_refused fuel md sel cur wlim s -> snd (walk_m fuel md sel cur wlim s off) = TUnk.
Proof.
  induction fuel as [|f IH]; intros md sel cur wlim s off H; [contradiction|].
  cbn [walk_refused] in H. cbn [walk_m]. cbv zeta in H |- *.
  destruct (Zlength s <? starting_len (md_magicless md)).
  { cbn [snd]. destruct (Z.eqb_spec (Zlength s) 0); [contradiction | reflexivity]. }
  destruct (negb (md_magicless md) && is_skippable_magic (le_field s 0 4)).
  - destruct (skippable_frame_size s) as [k|]; [|contradiction].
    specialize (IH _ _ _ _ _ (off + k) H).
    match goal with |- context [walk_m f ?a ?b ?c ?d ?e ?g] => destruct (walk_m f a b c d e g) as [l t] eqn:E end.
    exact IH.
  - destruct (frame_dict (md_magicless md) sel cur s) as [d|]; [|contradiction].
    destruct (decode_frame_m md d wlim s) as [c k| | |]; try contradiction; [|reflexivity].
    specialize (IH _ _ _ _ _ (off + k) H).
    match goal with |- context [walk_m f ?a ?b ?c ?d ?e ?g] => destruct (walk_m f a b c d e g) as [l t] eqn:E end.
    exact IH.
Qed.

(* a refused series ends TUnk *)
Lemma series_refused_tunk: forall md sel cur wlim s,
  bytes_ok s -> series_refused_m md sel cur wlim s -> snd (series_frames_m md sel cur wlim s) = TUnk.
Proof. intros md sel cur wlim s _ H. apply rf_walk. exact H. Qed.

(* ---------- sanity checks ---------- *)

(* the frame "abc" of Series.v (a single-segment frame, Frame_Content_Size 3, one raw last block) *)
Definition ex_abc : list Z := [40; 181; 47; 253; 32; 3; 25; 0; 0; 97; 98; 99].

(* some cuts of it: in the magic number, the header, the block header, the block's content *)
Definition ex_cuts : list (list Z) := map (fun n => firstn n ex_abc) [1; 4; 5; 6; 7; 8; 9; 10; 11]%nat.

Definition ex_refused : list (list Z) :=
  ex_cuts ++
  [(* the block made Reserved (Block_Type 3: header byte 25 | 6 = 31) *)
   [40; 181; 47; 253; 32; 3; 31; 0; 0; 97; 98; 99];
   (* a declared size of 4 for 3 bytes *)
   [40; 181; 47; 253; 32; 4; 25; 0; 0; 97; 98; 99];
   (* a declared size of 0 (Window_Size 0) for a raw block of 1 byte, larger than Block_Maximum_Size 0 *)
   [40; 181; 47; 253; 32; 0; 9; 0; 0; 97];
   (* a checksum flag (FHD 0x24) with 2 of the 4 checksum bytes *)
   [40; 181; 47; 253; 36; 3; 25; 0; 0; 97; 98; 99; 1; 2]].

(* a compressed last block (Block_Type 2, size 3: 3 << 3 | 2 << 1 | 1 = 29) of bytes the model does not decode *)
Definition ex_garbage : list Z := [40; 181; 47; 253; 32; 3; 29; 0; 0; 255; 255; 255].

Example refused_examples_series :
  decode_series_m md_dflt sel_none (Some no_dict) no_wlim ex_abc = SOk [97; 98; 99] /\
  map (decode_series_m md_dflt sel_none (Some no_dict) no_wlim) ex_refused = repeat SUnk 13 /\
  decode_series_m md_dflt sel_none (Some no_dict) no_wlim ex_garbage = SUnk.
Proof. vm_compute. auto. Qed.

Example refused_examples :
  ~ series_refused_m md_dflt sel_none (Some no_dict) no_wlim ex_abc /\
  Forall (series_refused_m md_dflt sel_none (Some no_dict) no_wlim) ex_refused /\
  ~ series_refused_m md_dflt sel_none (Some no_dict) no_wlim ex_garbage.
Proof.
  split; [| split].
  - vm_compute. tauto.
  - unfold ex_refused, ex_cuts. simpl map. simpl app.
    repeat apply Forall_cons; try apply Forall_nil; vm_compute;
      first [lia | tauto | (repeat split; try discriminate; try lia;
                            first [left; split; intro; discriminate | right; split; reflexivity])].
  - vm_compute. tauto.
Qed.
