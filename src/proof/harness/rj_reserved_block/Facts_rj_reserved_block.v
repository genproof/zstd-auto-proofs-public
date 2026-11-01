(* Model facts of the law rj_reserved_block (harness/rj_reserved_block.c), plain Coq.

   The harness takes a frame F = nf_bytes d fcs did c of new_frame (frames kit, FModel.v), walks its block
   headers from the first one (the offset it computes from the Frame_Header_Descriptor F[4]) over any number of
   blocks, never past the last one, and sets Block_Type 3 (Reserved) in the header it stops at: F[at] |= 6.
   - blk_off fcs did c i: the offset in F of the header of the i-th block (i < the number of blocks);
   - rb_first: the harness's first offset is blk_off .. 0;
   - rb_hdr_in, rb_last, rb_next: the three header bytes are in F, the Last_Block bit tells whether the block is
     the last, and the harness's step goes from the i-th header to the next one;
   - rb_refused: F with the i-th block made Reserved is a series zstd certainly refuses (model/Refuse.v), and
     the model's walk over it finds no complete frame (no frame comes before the refused one): the one-shot
     specification then promises an error, the streaming specification no 0 return. *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Block Zstd.proof.model.Series.
Require Import Zstd.proof.model.StreamModel Zstd.proof.model.Params Zstd.proof.model.Refuse.
Require Export Zstd.proof.harness.frames.FModel.
Require Import Coq.ZArith.ZArith Coq.Lists.List.
Import ListNotations.
Local Open Scope Z_scope.

(* the bytes of the blocks bl in a frame: a header of 3 bytes, then the Block_Size bytes of a Raw block or the
   one byte of an RLE block *)
Fixpoint blocks_len (bl: list nf_block) : Z :=
  match bl with
  | [] => 0
  | b :: bl' => 3 + (if nb_rle b then 1 else nb_size b) + blocks_len bl'
  end.

(* the offset of the i-th block header in nf_bytes d fcs did c *)
Definition blk_off (fcs did: Z) (c: nf_choice) (i: nat) : Z :=
  Zlength (nh_bytes fcs did (nc_hdr c)) + blocks_len (firstn i (nc_blocks c)).

(* s with its byte at k replaced by v *)
Definition set_byte (s: list Z) (k v: Z) : list Z :=
  firstn (Z.to_nat k) s ++ v :: skipn (Z.to_nat k + 1) s.

(* the frame with the header of its i-th block made Reserved, as the harness writes it *)
Definition reserved_at (F: list Z) (k: Z) : list Z := set_byte F k (Z.lor (byte_at F k) 6).

(* the frames of new_frame the facts are about *)
Definition rb_frame (d: list Z) (fcs maxw did: Z) (c: nf_choice) : Prop :=
  nf_ok (Zlength d) fcs maxw did c /\ bytes_ok d /\ 0 <= fcs < 2 ^ 64 /\ 0 <= did < 2 ^ 32 /\ maxw < 2 ^ 32.

(* ---------- helpers ---------- *)

Require Import Zstd.proof.harness.frames.FFacts.

(* the bytes before position k, then from k on *)
Lemma rb_byte_at_skipn : forall (F: list Z) o j, 0 <= o -> 0 <= j ->
  byte_at F (o + j) = byte_at (skipn (Z.to_nat o) F) j.
Proof.
  intros F o j Ho Hj. unfold byte_at. rewrite nth_skipn, Z2Nat.inj_add by lia. reflexivity.
Qed.

Lemma rb_skipn_add : forall (A R: list Z) k, 0 <= k ->
  skipn (Z.to_nat (Zlength A + k)) (A ++ R) = skipn (Z.to_nat k) R.
Proof.
  intros A R k Hk. rewrite Z2Nat.inj_add by (pose proof (ff_Zlength_nonneg A); lia).
  rewrite Zlength_correct, Nat2Z.id, skipn_app, skipn_all2 by lia.
  replace (length A + Z.to_nat k - length A)%nat with (Z.to_nat k) by lia. reflexivity.
Qed.

(* the harness's write past a prefix A is a write in the rest *)
Lemma rb_reserved_at_app : forall (A R: list Z) k, 0 <= k ->
  reserved_at (A ++ R) (Zlength A + k) = A ++ reserved_at R k.
Proof.
  intros A R k Hk. unfold reserved_at, set_byte, byte_at.
  pose proof (ff_Zlength_nonneg A) as HA.
  rewrite Z2Nat.inj_add by lia. rewrite Zlength_correct, Nat2Z.id.
  rewrite firstn_app, firstn_all2 by lia. replace (length A + Z.to_nat k - length A)%nat with (Z.to_nat k) by lia.
  rewrite app_nth2 by lia. replace (length A + Z.to_nat k - length A)%nat with (Z.to_nat k) by lia.
  rewrite skipn_app, skipn_all2 by lia.
  replace (length A + Z.to_nat k + 1 - length A)%nat with (Z.to_nat k + 1)%nat by lia.
  rewrite <- !app_assoc. reflexivity.
Qed.

(* a value below 2^k or'ed with a multiple of 2^k is their sum *)
Lemma rb_lor_small : forall a s k, 0 <= k -> 0 <= a < 2 ^ k -> 0 <= s -> Z.lor a (s * 2 ^ k) = a + s * 2 ^ k.
Proof.
  intros a s k Hk Ha Hs.
  assert (L: Z.land a (s * 2 ^ k) = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i k).
    - rewrite Z.mul_pow2_bits_low by lia. apply Bool.andb_false_r.
    - destruct (Z.eq_dec a 0); [subst; rewrite Z.bits_0; reflexivity |].
      rewrite (Z.bits_above_log2 a i); [reflexivity | lia |].
      assert (Z.log2 a < k) by (apply Z.log2_lt_pow2; lia). lia. }
  rewrite <- Z.lxor_lor by exact L. rewrite Z.add_nocarry_lxor by exact L. reflexivity.
Qed.

(* Last_Block and Block_Type depend only on the header's first byte; Block_Size as the harness computes it *)
Lemma rb_props_bytes : forall y0 y1 y2 t,
  bp_last (block_props_of (y0 :: y1 :: y2 :: t)) = Z.land y0 1 /\
  bp_type (block_props_of (y0 :: y1 :: y2 :: t)) = Z.land (Z.shiftr y0 1) 3 /\
  (0 <= y0 < 256 -> 0 <= y1 < 256 -> 0 <= y2 < 256 ->
   bp_origSize (block_props_of (y0 :: y1 :: y2 :: t)) =
   Z.shiftr (Z.lor (Z.lor y0 (Z.shiftl y1 8)) (Z.shiftl y2 16)) 3).
Proof.
  intros y0 y1 y2 t. set (q := y1 + 256 * (y2 + 256 * 0)).
  assert (E: le_field (y0 :: y1 :: y2 :: t) 0 3 = y0 + 256 * q) by reflexivity.
  unfold block_props_of. rewrite E. cbn [bp_last bp_type bp_origSize].
  split; [| split].
  - change 1 with (Z.ones 1). rewrite !Z.land_ones by lia.
    replace (y0 + 256 * q) with (y0 + (128 * q) * 2 ^ 1) by lia. apply Z.mod_add. lia.
  - change 3 with (Z.ones 2). rewrite !Z.land_ones, !Z.shiftr_div_pow2 by lia.
    replace (y0 + 256 * q) with (y0 + (128 * q) * 2 ^ 1) by lia. rewrite Z.div_add by lia.
    replace (y0 / 2 ^ 1 + 128 * q) with (y0 / 2 ^ 1 + (32 * q) * 2 ^ 2) by lia. apply Z.mod_add. lia.
  - intros H0 H1 H2. f_equal. rewrite !Z.shiftl_mul_pow2 by lia.
    rewrite (rb_lor_small y0 y1 8) by (change (2 ^ 8) with 256; lia).
    rewrite (rb_lor_small _ y2 16) by (change (2 ^ 8) with 256; change (2 ^ 16) with 65536; lia).
    unfold q. change (2 ^ 8) with 256. change (2 ^ 16) with 65536. lia.
Qed.

(* the byte the harness writes: Block_Type 3, still a byte *)
Lemma rb_lor6_type : forall x, Z.land (Z.shiftr (Z.lor x 6) 1) 3 = 3.
Proof.
  intros x. apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec, Z.shiftr_spec, Z.lor_spec by lia.
  destruct (Z.lt_ge_cases n 2) as [Hl | Hl].
  - assert (n = 0 \/ n = 1) as [-> | ->] by lia; cbn; rewrite Bool.orb_true_r; reflexivity.
  - rewrite (Z.bits_above_log2 3 n) by (cbn; lia). apply Bool.andb_false_r.
Qed.

Lemma rb_lor6_byte : forall x, is_byte x -> is_byte (Z.lor x 6).
Proof.
  intros x Hx. unfold is_byte in *. split; [apply Z.lor_nonneg; lia |].
  destruct (Z.eq_dec (Z.lor x 6) 0) as [E | E]; [lia |].
  assert (0 <= Z.lor x 6) by (apply Z.lor_nonneg; lia).
  change 256 with (2 ^ 8). apply Z.log2_lt_pow2; [lia |].
  rewrite Z.log2_lor by lia.
  destruct (Z.eq_dec x 0) as [-> | Ex]; [cbn; lia |].
  assert (Z.log2 x < 8) by (apply Z.log2_lt_pow2; cbn; lia). cbn [Z.log2 Pos.size]. lia.
Qed.

(* the blocks of a cut are at most 128 KiB each *)
Lemma rb_sizes : forall mb n bl done, 0 <= done <= n -> mb <= 131072 -> nf_blocks_ok mb n done bl ->
  Forall (fun b => 0 <= nb_size b <= 131072) bl.
Proof.
  intros mb n bl. induction bl as [| b bl IH]; intros done Hd Hmb H; [destruct H |].
  pose proof (ff_block_bound _ _ _ _ _ Hd Hmb H) as Hs. constructor; [lia |].
  destruct H as (_ & _ & _ & _ & Hr). destruct bl as [| b' bl']; [constructor |].
  destruct Hr as (_ & Hr). eapply IH; [| exact Hmb | exact Hr]. lia.
Qed.

Lemma rb_blocks_len_nonneg : forall bl, Forall (fun b => 0 <= nb_size b <= 131072) bl -> 0 <= blocks_len bl.
Proof.
  induction bl as [| b bl IH]; intros H; cbn [blocks_len]; [lia |]. inversion H; subst.
  specialize (IH ltac:(assumption)). destruct (nb_rle b); lia.
Qed.

Lemma rb_firstn_nonneg : forall bl i, Forall (fun b => 0 <= nb_size b <= 131072) bl ->
  0 <= blocks_len (firstn i bl).
Proof.
  intros bl i H. apply rb_blocks_len_nonneg. rewrite <- (firstn_skipn i bl) in H.
  apply Forall_app in H. apply H.
Qed.

Lemma rb_firstn_lt : forall bl i, Forall (fun b => 0 <= nb_size b <= 131072) bl -> (i < length bl)%nat ->
  blocks_len (firstn i bl) + 3 <= blocks_len bl.
Proof.
  induction bl as [| b bl IH]; intros i H Hi; [cbn in Hi; lia |]. inversion H; subst.
  pose proof (rb_blocks_len_nonneg bl ltac:(assumption)).
  destruct i as [| i]; cbn [firstn blocks_len].
  - destruct (nb_rle b); lia.
  - cbn [length] in Hi. specialize (IH i ltac:(assumption) ltac:(lia)). destruct (nb_rle b); lia.
Qed.

Lemma rb_firstn_S : forall bl i b0, (i < length bl)%nat ->
  blocks_len (firstn (S i) bl) =
  blocks_len (firstn i bl) + 3 + (if nb_rle (nth i bl b0) then 1 else nb_size (nth i bl b0)).
Proof.
  induction bl as [| b bl IH]; intros i b0 Hi; [cbn in Hi; lia |].
  destruct i as [| i].
  - cbn [firstn blocks_len nth]. destruct (nb_rle b); lia.
  - change (firstn (S (S i)) (b :: bl)) with (b :: firstn (S i) bl).
    change (firstn (S i) (b :: bl)) with (b :: firstn i bl).
    change (nth (S i) (b :: bl) b0) with (nth i bl b0). cbn [blocks_len].
    cbn [length] in Hi. rewrite (IH i b0) by lia. lia.
Qed.

Lemma rb_blocks_bytes_Zlength : forall d mb bl done, 0 <= done <= Zlength d ->
  nf_blocks_ok mb (Zlength d) done bl -> Zlength (nf_blocks_bytes d done bl) = blocks_len bl.
Proof.
  intros d mb bl. induction bl as [| b bl IH]; intros done Hd H; [destruct H |].
  pose proof (ff_block_size _ _ _ _ _ Hd H) as Hs.
  cbn [nf_blocks_bytes blocks_len]. rewrite !ff_Zlength_app.
  assert (Hh3: Zlength (nb_header (is_nil bl) b) = 3) by (unfold nb_header; rewrite ff_le_bytes_Zlength; reflexivity).
  assert (Hr: Zlength (nf_blocks_bytes d (done + nb_size b) bl) = blocks_len bl).
  { destruct H as (_ & _ & _ & _ & Hr). destruct bl as [| b' bl']; [reflexivity |].
    destruct Hr as (_ & Hr). apply IH; [lia | exact Hr]. }
  rewrite Hh3, Hr. destruct (nb_rle b); [rewrite Zlength_cons, Zlength_nil; lia |].
  rewrite ff_slice_length by lia. lia.
Qed.

(* the i-th block header of the blocks, followed by anything *)
Lemma rb_blocks_at : forall d mb bl done i t b0, 0 <= done <= Zlength d -> mb <= 131072 ->
  nf_blocks_ok mb (Zlength d) done bl -> (i < length bl)%nat ->
  exists t', skipn (Z.to_nat (blocks_len (firstn i bl))) (nf_blocks_bytes d done bl ++ t) =
             nb_header (Nat.eqb (S i) (length bl)) (nth i bl b0) ++ t'.
Proof.
  intros d mb bl. induction bl as [| b bl IH]; intros done i t b0 Hd Hmb H Hi; [destruct H |].
  pose proof (ff_block_size _ _ _ _ _ Hd H) as Hs.
  set (body := if nb_rle b then [if nb_size b =? 0 then nb_byte b else byte_at d done]
               else slice d done (nb_size b)).
  assert (Hbody: Zlength body = if nb_rle b then 1 else nb_size b).
  { unfold body. destruct (nb_rle b); [reflexivity | apply ff_slice_length; lia]. }
  assert (Hh3: Zlength (nb_header (is_nil bl) b) = 3) by (unfold nb_header; rewrite ff_le_bytes_Zlength; reflexivity).
  cbn [nf_blocks_bytes]. fold body. destruct i as [| i].
  - cbn [firstn blocks_len nth Z.to_nat skipn length]. rewrite <- !app_assoc.
    eexists. f_equal. f_equal. destruct bl; reflexivity.
  - cbn [length] in Hi. destruct H as (_ & _ & _ & _ & Hr). destruct bl as [| b' bl']; [cbn in Hi; lia |].
    destruct Hr as (_ & Hr).
    set (bl := b' :: bl') in *.
    assert (Hf: Forall (fun b => 0 <= nb_size b <= 131072) bl) by (eapply rb_sizes; [| exact Hmb | exact Hr]; lia).
    pose proof (rb_firstn_nonneg bl i Hf) as Hk.
    cbn [firstn blocks_len nth length].
    replace (3 + (if nb_rle b then 1 else nb_size b) + blocks_len (firstn i bl))
      with (Zlength (nb_header (is_nil bl) b ++ body) + blocks_len (firstn i bl))
      by (rewrite ff_Zlength_app, Hh3, Hbody; lia).
    rewrite <- !app_assoc, app_assoc, rb_skipn_add by exact Hk.
    destruct (IH (done + nb_size b) i t b0 ltac:(lia) Hmb Hr ltac:(lia)) as [t' E].
    exists t'. rewrite E. reflexivity.
Qed.

(* the walk of a refused frame's blocks (model/Refuse.v) over the blocks with the i-th made Reserved: the blocks
   before it are Raw or RLE and not the last, the i-th has Block_Type 3 *)
Lemma rb_walk : forall dw h st hist bsm d mb bl done i out fuel t,
  0 <= done <= Zlength d -> mb <= 131072 -> nf_blocks_ok mb (Zlength d) done bl -> (i < length bl)%nat ->
  (length (nf_blocks_bytes d done bl) <= fuel)%nat ->
  blocks_refused dw fuel h st hist (reserved_at (nf_blocks_bytes d done bl ++ t) (blocks_len (firstn i bl))) out bsm.
Proof.
  intros dw h st hist bsm d mb bl. induction bl as [| b bl IH]; intros done i out fuel t Hd Hmb H Hi Hf;
    [destruct H |].
  pose proof (ff_block_bound _ _ _ _ _ Hd Hmb H) as Hs.
  set (body := if nb_rle b then [if nb_size b =? 0 then nb_byte b else byte_at d done]
               else slice d done (nb_size b)).
  assert (Hbody: Zlength body = if nb_rle b then 1 else nb_size b).
  { unfold body. destruct (nb_rle b); [reflexivity | apply ff_slice_length; lia]. }
  assert (Hh3: Zlength (nb_header (is_nil bl) b) = 3) by (unfold nb_header; rewrite ff_le_bytes_Zlength; reflexivity).
  cbn [nf_blocks_bytes] in *. fold body in Hf |- *.
  set (rest := nf_blocks_bytes d (done + nb_size b) bl) in *.
  rewrite !length_app in Hf. destruct fuel as [| f]; [rewrite Zlength_correct in Hh3; lia |].
  destruct i as [| i].
  - (* the Reserved block *)
    cbn [firstn blocks_len]. rewrite <- !app_assoc.
    unfold nb_header. cbn [le_bytes app].
    unfold reserved_at, set_byte, byte_at. cbn [Z.to_nat firstn skipn nth app Nat.add].
    cbn [blocks_refused]. unfold ZSTD_blockHeaderSize.
    rewrite (proj2 (Z.ltb_ge _ 3)) by (rewrite !Zlength_cons; pose proof (ff_Zlength_nonneg (body ++ rest ++ t)); lia).
    destruct (rb_props_bytes (Z.lor ((zb (is_nil bl) + 2 * zb (nb_rle b) + 8 * nb_size b) mod 256) 6)
                ((zb (is_nil bl) + 2 * zb (nb_rle b) + 8 * nb_size b) / 256 mod 256)
                ((zb (is_nil bl) + 2 * zb (nb_rle b) + 8 * nb_size b) / 256 / 256 mod 256)
                (body ++ rest ++ t)) as (_ & Ht & _).
    rewrite Ht, rb_lor6_type. reflexivity.
  - (* a Raw or RLE block before it *)
    cbn [length] in Hi. destruct H as (_ & _ & _ & _ & Hr). destruct bl as [| b' bl']; [cbn in Hi; lia |].
    destruct Hr as (Hpos & Hr). set (bl := b' :: bl') in *.
    assert (Hfa: Forall (fun b => 0 <= nb_size b <= 131072) bl) by (eapply rb_sizes; [| exact Hmb | exact Hr]; lia).
    pose proof (rb_firstn_nonneg bl i Hfa) as Hk.
    cbn [firstn blocks_len].
    replace (3 + (if nb_rle b then 1 else nb_size b) + blocks_len (firstn i bl))
      with (Zlength (nb_header (is_nil bl) b ++ body) + blocks_len (firstn i bl))
      by (rewrite ff_Zlength_app, Hh3, Hbody; lia).
    rewrite <- !app_assoc, (app_assoc (nb_header _ _) body), rb_reserved_at_app by exact Hk.
    rewrite <- app_assoc.
    set (R := reserved_at (rest ++ t) (blocks_len (firstn i bl))).
    pose proof (ff_Zlength_nonneg R). pose proof (ff_Zlength_nonneg body).
    cbn [blocks_refused]. unfold cblock_size. rewrite ff_block_props by lia. cbn [bp_type bp_last bp_origSize].
    rewrite !ff_Zlength_app, Hh3. unfold ZSTD_blockHeaderSize.
    rewrite (proj2 (Z.ltb_ge _ 3)) by lia.
    assert (Hc: (if zb (nb_rle b) =? 1 then Some 1 else if zb (nb_rle b) =? 3 then None else Some (nb_size b))
                = Some (Zlength body)) by (rewrite Hbody; destruct (nb_rle b); reflexivity).
    assert (H3: zb (nb_rle b) =? 3 = false) by (destruct (nb_rle b); reflexivity).
    rewrite Hc, H3. rewrite Z.gtb_ltb, (proj2 (Z.ltb_ge _ _)) by lia.
    unfold rblock. rewrite ff_block_props by lia. cbn [bp_type bp_last bp_origSize].
    assert (Hrb: exists out', (if zb (nb_rle b) =? 0 then Some (st, out ++ slice (nb_header (is_nil bl) b ++ body ++ R) 3 (Zlength body))
              else if zb (nb_rle b) =? 1 then Some (st, out ++ repeat (byte_at (slice (nb_header (is_nil bl) b ++ body ++ R) 3 (Zlength body)) 0) (Z.to_nat (nb_size b)))
              else match rdec_block dw st hist out (slice (nb_header (is_nil bl) b ++ body ++ R) 3 (Zlength body)) bsm (fh_windowSize h) with
                   | Some (st', content) => Some (st', out ++ content) | None => None end) = Some (st, out'))
      by (destruct (nb_rle b); eexists; reflexivity).
    destruct Hrb as [out' Hrb]. unfold ZSTD_blockHeaderSize. rewrite Hrb.
    cbn [is_nil bl zb]. change (0 =? 1) with false. cbv iota.
    rewrite ff_skipn_mid by (unfold nb_header; rewrite ff_le_bytes_Zlength; reflexivity).
    apply IH; [lia | exact Hmb | exact Hr | lia |]. rewrite Zlength_correct in Hh3. fold rest. lia.
Qed.


(* the frame with the harness's write: the header, then the blocks and the checksum with the write *)
Lemma rb_reserved_frame : forall d fcs maxw did c i, rb_frame d fcs maxw did c ->
  reserved_at (nf_bytes d fcs did c) (blk_off fcs did c i) =
  nh_bytes fcs did (nc_hdr c) ++
  reserved_at (nf_blocks_bytes d 0 (nc_blocks c) ++ nf_checksum d c) (blocks_len (firstn i (nc_blocks c))).
Proof.
  intros d fcs maxw did c i (Hok & _). destruct Hok as [_ Hb].
  pose proof (ff_Zlength_nonneg d).
  assert (Hmb: nh_max_block fcs (nc_hdr c) <= 131072) by apply Z.le_min_r.
  pose proof (rb_firstn_nonneg (nc_blocks c) i (rb_sizes _ (Zlength d) _ 0 ltac:(lia) Hmb Hb)) as Hk.
  unfold blk_off, nf_bytes. apply rb_reserved_at_app. exact Hk.
Qed.

(* the i-th block header is at blk_off .. i in the frame *)
Lemma rb_hdr : forall d fcs maxw did c i b0, rb_frame d fcs maxw did c -> (i < length (nc_blocks c))%nat ->
  0 <= blk_off fcs did c i /\ 0 <= nb_size (nth i (nc_blocks c) b0) <= 131072 /\
  exists t', skipn (Z.to_nat (blk_off fcs did c i)) (nf_bytes d fcs did c) =
             nb_header (Nat.eqb (S i) (length (nc_blocks c))) (nth i (nc_blocks c) b0) ++ t'.
Proof.
  intros d fcs maxw did c i b0 (Hok & _) Hi. destruct Hok as [_ Hb].
  pose proof (ff_Zlength_nonneg d).
  assert (Hmb: nh_max_block fcs (nc_hdr c) <= 131072) by apply Z.le_min_r.
  pose proof (rb_sizes _ (Zlength d) _ 0 ltac:(lia) Hmb Hb) as Hf.
  pose proof (rb_firstn_nonneg (nc_blocks c) i Hf) as Hk.
  pose proof (ff_Zlength_nonneg (nh_bytes fcs did (nc_hdr c))).
  split; [unfold blk_off; lia |]. split; [apply Forall_nth; auto |].
  unfold blk_off, nf_bytes. rewrite rb_skipn_add by exact Hk.
  eapply rb_blocks_at; eauto. lia.
Qed.

(* the three bytes of a block header new_frame writes, as the harness reads them *)
Lemma rb_hdr_bytes : forall last b t, 0 <= nb_size b < 2 ^ 21 ->
  exists y0 y1 y2, nb_header last b ++ t = y0 :: y1 :: y2 :: t /\
    Z.land y0 1 = zb last /\ Z.land (Z.shiftr y0 1) 3 = zb (nb_rle b) /\
    Z.shiftr (Z.lor (Z.lor y0 (Z.shiftl y1 8)) (Z.shiftl y2 16)) 3 = nb_size b.
Proof.
  intros last b t Hs. pose proof (ff_block_props last b t Hs) as Hp.
  assert (Hok: bytes_ok (nb_header last b)) by apply ff_le_bytes_ok.
  assert (E: exists y0 y1 y2, nb_header last b = [y0; y1; y2]) by (unfold nb_header; cbn [le_bytes]; eauto).
  destruct E as (y0 & y1 & y2 & E). rewrite E in Hp, Hok |- *. exists y0, y1, y2.
  inversion Hok as [| ? ? H0 Hok1]; subst. inversion Hok1 as [| ? ? H1 Hok2]; subst.
  inversion Hok2 as [| ? ? H2 _]; subst. unfold is_byte in *.
  change ([y0; y1; y2] ++ t) with (y0 :: y1 :: y2 :: t) in Hp |- *.
  destruct (rb_props_bytes y0 y1 y2 t) as (HL & HT & HS). rewrite Hp in HL, HT, HS. cbn in HL, HT, HS.
  split; [reflexivity |]. split; [auto |]. split; [auto |]. symmetry. auto.
Qed.

Lemma rb_set_len : forall (F: list Z) o, 0 <= o < Zlength F -> Zlength (reserved_at F o) = Zlength F.
Proof.
  intros F o Ho. unfold reserved_at, set_byte. rewrite Zlength_correct in *.
  rewrite length_app, length_firstn. cbn [length]. rewrite length_skipn.
  assert (Z.of_nat (Z.to_nat o) = o) by (apply Z2Nat.id; lia).
  assert (Z.to_nat o < length F)%nat by lia. rewrite Nat.min_l, Zlength_correct by lia. lia.
Qed.

Lemma rb_set_ok : forall F o, bytes_ok F -> 0 <= o < Zlength F -> bytes_ok (reserved_at F o).
Proof.
  intros F o HF Ho. unfold reserved_at, set_byte, bytes_ok in *.
  pose proof HF as HF'. rewrite <- (firstn_skipn (Z.to_nat o) F) in HF'.
  apply Forall_app in HF'. destruct HF' as [H1 _].
  pose proof HF as HF''. rewrite <- (firstn_skipn (Z.to_nat o + 1) F) in HF''.
  apply Forall_app in HF''. destruct HF'' as [_ H2].
  apply Forall_app. split; [exact H1 |]. constructor; [| exact H2].
  apply rb_lor6_byte. apply ff_byte_at_ok. exact HF.
Qed.

(* the harness's first offset: 5 + !single + (fhd & 3) + ((fhd & 3) == 3) + (fcs_flag == 0 ? single : 1 << fcs_flag)
   with fhd = F[4], single = fhd >> 5 & 1, fcs_flag = fhd >> 6 *)
Lemma rb_first : forall d fcs maxw did c, rb_frame d fcs maxw did c ->
  let F := nf_bytes d fcs did c in
  let fhd := byte_at F 4 in
  let single := Z.land (Z.shiftr fhd 5) 1 in
  let fcs_flag := Z.shiftr fhd 6 in
  4 < Zlength F /\
  5 + (1 - single) + Z.land fhd 3 + (if Z.land fhd 3 =? 3 then 1 else 0) +
    (if fcs_flag =? 0 then single else 2 ^ fcs_flag) = blk_off fcs did c 0.
Proof.
  intros d fcs maxw did c Hr. cbv zeta. destruct Hr as (Hok & Hd & Hfcs & Hdid & Hmw).
  pose proof (nf_bytes_length _ _ _ _ _ Hok) as HL. pose proof Hok as [Hh Hb].
  split; [lia |].
  unfold nf_bytes. destruct (ff_nh_read fcs maxw did (nc_hdr c) (nf_blocks_bytes d 0 (nc_blocks c) ++ nf_checksum d c)
                             Hh Hfcs Hdid) as (_ & H4 & _).
  rewrite H4. pose proof Hh as (Hf03 & _ & _ & _ & _ & Hbits & Hd03 & _).
  destruct (ff_fhd_facts _ Hf03 Hbits Hd03) as (_ & Hd3 & Hs5 & Hf6 & _).
  rewrite Hd3, Hs5, Hf6. unfold blk_off. cbn [firstn blocks_len]. rewrite (ff_nh_bytes_Zlength _ _ _ _ Hh).
  unfold nh_did_size, nh_fcs_size.
  destruct (ff_flag_cases _ Hf03) as [E | [E | [E | E]]]; rewrite E;
  destruct (ff_flag_cases _ Hd03) as [E' | [E' | [E' | E']]]; rewrite E';
  destruct (nh_single (nc_hdr c)); cbn; lia.
Qed.

(* the three bytes of every block header are in the frame *)
Lemma rb_hdr_in : forall d fcs maxw did c i, rb_frame d fcs maxw did c -> (i < length (nc_blocks c))%nat ->
  0 <= blk_off fcs did c i /\ blk_off fcs did c i + 3 <= Zlength (nf_bytes d fcs did c).
Proof.
  intros d fcs maxw did c i Hr Hi. destruct (rb_hdr d fcs maxw did c i (nth i (nc_blocks c) {| nb_size := 0; nb_rle := false; nb_byte := 0 |}) Hr Hi) as (Ho & _).
  split; [exact Ho |].
  destruct Hr as (Hok & _). pose proof Hok as [_ Hb].
  pose proof (ff_Zlength_nonneg d).
  assert (Hmb: nh_max_block fcs (nc_hdr c) <= 131072) by apply Z.le_min_r.
  pose proof (rb_sizes _ (Zlength d) _ 0 ltac:(lia) Hmb Hb) as Hf.
  pose proof (rb_firstn_lt _ i Hf Hi).
  pose proof (rb_blocks_bytes_Zlength d _ _ 0 ltac:(lia) Hb).
  unfold blk_off, nf_bytes. rewrite !ff_Zlength_app.
  pose proof (ff_Zlength_nonneg (nf_checksum d c)). lia.
Qed.

(* Last_Block (bit 0 of the header's first byte): set exactly in the last block's header *)
Lemma rb_last : forall d fcs maxw did c i, rb_frame d fcs maxw did c -> (i < length (nc_blocks c))%nat ->
  Z.land (byte_at (nf_bytes d fcs did c) (blk_off fcs did c i)) 1 =
  (if Nat.eqb (S i) (length (nc_blocks c)) then 1 else 0).
Proof.
  intros d fcs maxw did c i Hr Hi.
  set (b0 := {| nb_size := 0; nb_rle := false; nb_byte := 0 |}).
  destruct (rb_hdr d fcs maxw did c i b0 Hr Hi) as (Ho & Hs & t' & E).
  rewrite <- (Z.add_0_r (blk_off fcs did c i)), rb_byte_at_skipn, E by lia.
  destruct (rb_hdr_bytes (Nat.eqb (S i) (length (nc_blocks c))) (nth i (nc_blocks c) b0) t')
    as (y0 & y1 & y2 & E' & HL & _); [change (2 ^ 21) with 2097152; lia |].
  rewrite E'. change (byte_at (y0 :: y1 :: y2 :: t') 0) with y0. rewrite HL.
  destruct (Nat.eqb (S i) (length (nc_blocks c))); reflexivity.
Qed.

(* the harness's step from a header that is not the last one: at += 3 + (Block_Type == 1 ? 1 : Block_Size), with
   Block_Type = b0 >> 1 & 3 and Block_Size = (b0 | b1 << 8 | b2 << 16) >> 3 *)
Lemma rb_next : forall d fcs maxw did c i, rb_frame d fcs maxw did c -> (S i < length (nc_blocks c))%nat ->
  let F := nf_bytes d fcs did c in
  let o := blk_off fcs did c i in
  let b0 := byte_at F o in
  let b1 := byte_at F (o + 1) in
  let b2 := byte_at F (o + 2) in
  blk_off fcs did c (S i) =
  o + 3 + (if Z.land (Z.shiftr b0 1) 3 =? 1 then 1
           else Z.shiftr (Z.lor (Z.lor b0 (Z.shiftl b1 8)) (Z.shiftl b2 16)) 3).
Proof.
  intros d fcs maxw did c i Hr Hi. cbv zeta.
  set (b0 := {| nb_size := 0; nb_rle := false; nb_byte := 0 |}).
  destruct (rb_hdr d fcs maxw did c i b0 Hr ltac:(lia)) as (Ho & Hs & t' & E).
  destruct (rb_hdr_bytes (Nat.eqb (S i) (length (nc_blocks c))) (nth i (nc_blocks c) b0) t')
    as (y0 & y1 & y2 & E' & _ & HT & HS); [change (2 ^ 21) with 2097152; lia |].
  assert (Bj: forall j, 0 <= j -> byte_at (nf_bytes d fcs did c) (blk_off fcs did c i + j) =
                                  byte_at (y0 :: y1 :: y2 :: t') j)
    by (intros j Hj; rewrite rb_byte_at_skipn, E, E' by lia; reflexivity).
  pose proof (Bj 0 ltac:(lia)) as B0. rewrite Z.add_0_r in B0.
  rewrite B0, (Bj 1), (Bj 2) by lia.
  change (byte_at (y0 :: y1 :: y2 :: t') 0) with y0. change (byte_at (y0 :: y1 :: y2 :: t') 1) with y1.
  change (byte_at (y0 :: y1 :: y2 :: t') 2) with y2.
  rewrite HT, HS. unfold blk_off. rewrite (rb_firstn_S _ i b0) by lia.
  destruct (nb_rle (nth i (nc_blocks c) b0)); cbn; lia.
Qed.

(* the frame with the i-th block made Reserved is a Zstandard frame zstd certainly refuses, with any dictionary:
   its header is accepted, the blocks before the i-th are Raw or RLE, the i-th has Block_Type 3 *)
Lemma rb_frame_refused : forall d fcs maxw did c i md dm, rb_frame d fcs maxw did c ->
  (i < length (nc_blocks c))%nat ->
  fcs = Zlength d -> did = 0 -> md_magicless md = false ->
  frame_refused_m md dm no_wlim (reserved_at (nf_bytes d fcs did c) (blk_off fcs did c i)).
Proof.
  intros d fcs maxw did c i md dm Hr Hi Hfd Hdid0 Hmg.
  rewrite (rb_reserved_frame d fcs maxw did c i Hr).
  destruct Hr as (Hok & Hd & Hfcs & Hdid & Hmw). pose proof Hok as [Hh Hb].
  pose proof (ff_Zlength_nonneg d) as Hn.
  assert (Hmb: nh_max_block fcs (nc_hdr c) <= 131072) by apply Z.le_min_r.
  pose proof (rb_sizes _ (Zlength d) _ 0 ltac:(lia) Hmb Hb) as Hf.
  pose proof (rb_firstn_lt _ i Hf Hi) as Hlt. pose proof (rb_firstn_nonneg _ i Hf) as Hk.
  pose proof (rb_blocks_bytes_Zlength d _ _ 0 ltac:(lia) Hb) as HB.
  pose proof (ff_Zlength_nonneg (nf_checksum d c)) as HK.
  set (X := reserved_at (nf_blocks_bytes d 0 (nc_blocks c) ++ nf_checksum d c) (blocks_len (firstn i (nc_blocks c)))).
  assert (HX: Zlength X = Zlength (nf_blocks_bytes d 0 (nc_blocks c) ++ nf_checksum d c))
    by (apply rb_set_len; rewrite ff_Zlength_app; lia).
  destruct (ff_nh_read fcs maxw did (nc_hdr c) X Hh Hfcs Hdid) as (_ & H4 & _).
  pose proof Hh as (Hf03 & _ & _ & _ & _ & Hbits & Hd03 & _).
  destruct (ff_fhd_facts _ Hf03 Hbits Hd03) as (_ & _ & _ & _ & _ & _ & _ & Hhs).
  pose proof (ff_nh_bytes_Zlength _ _ _ _ Hh) as Hlen.
  unfold frame_refused_m. rewrite Hmg. unfold header_size_m. rewrite H4, Hhs, <- Hlen.
  rewrite ff_Zlength_app. pose proof (ff_Zlength_nonneg X). rewrite (proj2 (Z.ltb_ge _ _)) by lia.
  change (get_frame_header_m false (nh_bytes fcs did (nc_hdr c) ++ X))
    with (get_frame_header (nh_bytes fcs did (nc_hdr c) ++ X)).
  rewrite (ff_get_frame_header fcs maxw) by (auto; eapply nf_wlog_ok; eauto).
  cbn [nf_header_of fh_windowSize fh_frameType fh_dictID fh_headerSize fh_blockSizeMax].
  split.
  { destruct Hh as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hw). unfold no_wlim.
    change (2 ^ 32) with 4294967296 in Hmw. change (2 ^ 64) with 18446744073709551616. lia. }
  split; [reflexivity |]. split; [left; exact Hdid0 |].
  rewrite ff_skipn_app by reflexivity.
  unfold X. apply rb_walk with (mb := nh_max_block fcs (nc_hdr c)); auto; try lia.
  fold X. rewrite ff_Zlength_app, !Zlength_correct in HX. lia.
Qed.

(* the frame with the i-th block made Reserved: refused, and no complete frame in the model's walk over it, for
   any mode with the magic number and any dictionaries (the frame names none: did = 0) *)
Lemma rb_refused : forall d fcs maxw did c i md sel cur, rb_frame d fcs maxw did c ->
  (i < length (nc_blocks c))%nat ->
  fcs = Zlength d -> did = 0 -> md_magicless md = false -> cur <> None ->
  let F' := reserved_at (nf_bytes d fcs did c) (blk_off fcs did c i) in
  series_refused_m md sel cur no_wlim F' /\ fst (series_frames_m md sel cur no_wlim F') = nil.
Proof.
  intros d fcs maxw did c i md sel cur Hr Hi Hfd Hdid0 Hmg Hcur. cbv zeta.
  pose proof (fun dm => rb_frame_refused d fcs maxw did c i md dm Hr Hi Hfd Hdid0 Hmg) as Hfr.
  pose proof (rb_hdr_in d fcs maxw did c i Hr Hi) as Hin.
  pose proof Hr as (Hok & Hd & Hfcs & Hdid & Hmw). pose proof Hok as [Hh Hb].
  assert (Hok': bytes_ok (reserved_at (nf_bytes d fcs did c) (blk_off fcs did c i)))
    by (apply rb_set_ok; [eapply nf_bytes_ok; eauto | lia]).
  assert (HL: Zlength (reserved_at (nf_bytes d fcs did c) (blk_off fcs did c i)) = Zlength (nf_bytes d fcs did c))
    by (apply rb_set_len; lia).
  pose proof (nf_bytes_length _ _ _ _ _ Hok) as HL9.
  rewrite (rb_reserved_frame d fcs maxw did c i Hr) in *.
  set (X := reserved_at (nf_blocks_bytes d 0 (nc_blocks c) ++ nf_checksum d c) (blocks_len (firstn i (nc_blocks c))))
    in *.
  set (s := nh_bytes fcs did (nc_hdr c) ++ X) in *.
  destruct (ff_nh_read fcs maxw did (nc_hdr c) X Hh Hfcs Hdid) as (Hm & _).
  fold s in Hm.
  assert (Hdict: exists dd, frame_dict false sel cur s = Some dd).
  { unfold frame_dict. change (get_frame_header_m false s) with (get_frame_header s). unfold s.
    rewrite (ff_get_frame_header fcs maxw) by (auto; eapply nf_wlog_ok; eauto).
    destruct (sel _) as [dd |]; [eauto |]. destruct cur as [dd |]; [eauto | congruence]. }
  destruct Hdict as [dd Hdict].
  assert (Hfunk: decode_frame_m md dd no_wlim s = FUnk).
  { apply frame_refused_funk; auto; rewrite Hmg; unfold starting_len, ZSTD_FRAMEHEADERSIZE_PREFIX; lia. }
  assert (Hst: (Zlength s <? starting_len false) = false)
    by (apply Z.ltb_ge; unfold starting_len, ZSTD_FRAMEHEADERSIZE_PREFIX; lia).
  split.
  - unfold series_refused_m. cbn [walk_refused]. rewrite Hmg, Hst, Hm.
    change (is_skippable_magic ZSTD_MAGICNUMBER) with false. cbn [negb andb].
    rewrite Hdict, Hfunk. apply Hfr.
  - unfold series_frames_m. cbn [walk_m]. rewrite Hmg, Hst, Hm.
    change (is_skippable_magic ZSTD_MAGICNUMBER) with false. cbn [negb andb].
    rewrite Hdict, Hfunk. reflexivity.
Qed.

(* one-shot: ZSTD_decompress's model (default mode, no dictionary) answers SUnk on a refused series, so its
   specification's refusal clause applies *)
Lemma rb_series_unk : forall s,
  bytes_ok s -> series_refused_m md_dflt sel_none (Some no_dict) no_wlim s ->
  decode_series_m md_dflt sel_none (Some no_dict) no_wlim s = SUnk.
Proof.
  intros s Hs Hr. pose proof (series_refused_tunk _ _ _ _ _ Hs Hr) as T.
  unfold decode_series_m. destruct (series_frames_m md_dflt sel_none (Some no_dict) no_wlim s) as [l t].
  cbn in T. subst t. reflexivity.
Qed.

(* the harness's write keeps the length and the bytes *)
Lemma reserved_at_length : forall F o, 0 <= o < Zlength F -> Zlength (reserved_at F o) = Zlength F.
Proof.
  exact rb_set_len.
Qed.

Lemma reserved_at_ok : forall F o, bytes_ok F -> 0 <= o < Zlength F -> bytes_ok (reserved_at F o).
Proof.
  exact rb_set_ok.
Qed.
