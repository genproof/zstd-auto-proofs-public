(* Frames of the writer of harness/frames.h (FModel.v) that zstd certainly refuses, in the sense of the format
   model's model/Refuse.v (series_refused_m): the decoder's specifications promise an error for such a series
   (ZSTD_decompress) and no 0 return of ZSTD_decompressStream.  Plain Coq.  These are the facts the laws
   rj_truncated, rj_reserved_block and rj_content_size need from the writer:

   - nf_refused_truncated: every part of a frame F = nf_bytes d |d| 0 c that stops before its end (1 <= k < |F|
     bytes of it) is refused;
   - nf_refused_reserved: F with the Block_Type of any one of its blocks made 3 (Reserved) is refused;
     nf_reserved_at_harness: the byte rj_reserved_block.c changes is the header of one of the blocks;
   - nf_refused_content_size: a frame whose Frame_Content_Size field declares a size other than its content's
     (and not ZSTD_CONTENTSIZE_UNKNOWN, which zstd reads as "no size") is refused.

   All three hold for any decoding mode with the magic number (Raw and RLE blocks of any size are decoded the
   same way under every mode), any dictionary selection, any current dictionary. *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Block Zstd.proof.model.Series.
Require Import Zstd.proof.model.Params Zstd.proof.model.Refuse.
Require Import Zstd.proof.harness.frames.FModel Zstd.proof.harness.frames.FFacts.
Local Open Scope bool_scope.

(* ---------- the reserved block: what rj_reserved_block.c changes ---------- *)

(* the offset of the header of block i (from 0) after the frame's header: the earlier blocks take 3 bytes of
   header and 1 (RLE) or Block_Size (Raw) bytes each *)
Fixpoint nb_off (bl: list nf_block) (i: nat) : Z :=
  match i, bl with
  | S i', b :: bl' => 3 + (if nb_rle b then 1 else nb_size b) + nb_off bl' i'
  | _, _ => 0
  end.

(* the offset of the header of block i in the frame nf_bytes d fcs did c *)
Definition nf_block_off (fcs did: Z) (c: nf_choice) (i: nat) : Z :=
  Zlength (nh_bytes fcs did (nc_hdr c)) + nb_off (nc_blocks c) i.

(* the bytes l with Z.lor 6 on the byte at off: a Block_Header there gets Block_Type 3 (bits 1-2) *)
Definition nf_reserve (l: list Z) (off: Z) : list Z :=
  firstn (Z.to_nat off) l ++ Z.lor (byte_at l off) 6 :: skipn (S (Z.to_nat off)) l.

(* what rj_reserved_block.c computes on the frame F: the first Block_Header follows Magic_Number,
   Frame_Header_Descriptor, Window_Descriptor (none with Single_Segment_flag), Dictionary_ID and
   Frame_Content_Size *)
Definition rb_first (F: list Z) : Z :=
  let fhd := byte_at F 4 in
  let single := Z.land (Z.shiftr fhd 5) 1 in
  let fcs_flag := Z.shiftr fhd 6 in
  5 + (1 - single) + Z.land fhd 3 + (if Z.land fhd 3 =? 3 then 1 else 0) +
  (if fcs_flag =? 0 then single else Z.shiftl 1 fcs_flag).

(* then its loop: while skip > 0 and the block at pos is not the last, skip it (3 + 1 for RLE, 3 + Block_Size
   otherwise) and decrement skip *)
Fixpoint rb_skip (F: list Z) (skip: nat) (pos: Z) : Z :=
  match skip with
  | O => pos
  | S k =>
      if Z.land (byte_at F pos) 1 =? 0 then
        rb_skip F k (pos + 3 +
          (if Z.land (Z.shiftr (byte_at F pos) 1) 3 =? 1 then 1
           else Z.shiftr (Z.lor (Z.lor (byte_at F pos) (Z.shiftl (byte_at F (pos + 1)) 8))
                                (Z.shiftl (byte_at F (pos + 2)) 16)) 3))
      else pos
  end.

(* ---------- sanity checks on concrete frames ---------- *)

(* "abcdef": Frame_Content_Size_flag 0 with Single_Segment (a 1-byte size), Content_Checksum, then a Raw block
   of 2, an RLE block of 3 ("ccc": data "abcdef" becomes "abcccf"), a Raw last block of 1 *)
Definition ex_d : list Z := [97; 98; 99; 100; 101; 102].
Definition ex_c : nf_choice :=
  {| nc_hdr := {| nh_fcs_flag := 0; nh_single := true; nh_bits := 4; nh_did_flag := 0; nh_wd := 0 |};
     nc_blocks := [{| nb_size := 2; nb_rle := false; nb_byte := 0 |};
                   {| nb_size := 3; nb_rle := true; nb_byte := 0 |};
                   {| nb_size := 1; nb_rle := false; nb_byte := 0 |}] |}.
Definition ex_F : list Z := nf_bytes ex_d 6 0 ex_c.
(* the same with a window descriptor, Frame_Content_Size_flag 1 (2 bytes, 300 - 256) declaring 300 *)
Definition ex_c2 : nf_choice :=
  {| nc_hdr := {| nh_fcs_flag := 1; nh_single := false; nh_bits := 0; nh_did_flag := 0; nh_wd := 0 |};
     nc_blocks := nc_blocks ex_c |}.
Definition ex_F2 : list Z := nf_bytes ex_d 300 0 ex_c2.
(* declared size 0 with Single_Segment: Window_Size 0, Raw blocks of 1 byte *)
Definition ex_c3 : nf_choice :=
  {| nc_hdr := {| nh_fcs_flag := 0; nh_single := true; nh_bits := 0; nh_did_flag := 0; nh_wd := 0 |};
     nc_blocks := [{| nb_size := 1; nb_rle := false; nb_byte := 0 |};
                   {| nb_size := 1; nb_rle := false; nb_byte := 0 |}] |}.
Definition ex_F3 : list Z := nf_bytes [7; 8] 0 0 ex_c3.

Definition ex_dec (s: list Z) : sres := decode_series_m md_dflt sel_none (Some no_dict) no_wlim s.
Definition ex_cut (k: nat) : sres := ex_dec (firstn k ex_F).
Definition ex_skip (i: nat) : Z := rb_skip ex_F i (rb_first ex_F).
Definition ex_res (i: nat) : sres := ex_dec (nf_reserve ex_F (nf_block_off 6 0 ex_c i)).

Example ex_frames :
  ex_dec ex_F = SOk [97; 98; 99; 99; 99; 102] /\
  map ex_cut (seq 1 (length ex_F - 1)) = repeat SUnk (length ex_F - 1) /\
  map ex_skip [0; 1; 2; 3; 200]%nat = map (nf_block_off 6 0 ex_c) [0; 1; 2; 2; 2]%nat /\
  map ex_res [0; 1; 2]%nat = [SUnk; SUnk; SUnk] /\
  ex_dec ex_F2 = SUnk /\ ex_dec ex_F3 = SUnk.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* ---------- helpers: lists, bits ---------- *)

Lemma fr_bytes_ok_firstn : forall l n, bytes_ok l -> bytes_ok (firstn n l).
Proof.
  intros l n H. unfold bytes_ok in *. rewrite <- (firstn_skipn n l) in H. apply Forall_app in H. tauto.
Qed.

Lemma fr_firstn_app_ge : forall (a b: list Z) k, Zlength a <= k ->
  firstn (Z.to_nat k) (a ++ b) = a ++ firstn (Z.to_nat (k - Zlength a)) b.
Proof.
  intros a b k Hk. rewrite firstn_app, firstn_all2 by (rewrite Zlength_correct in Hk; lia).
  f_equal. f_equal. rewrite Zlength_correct in *. lia.
Qed.

Lemma fr_Zlength_firstn : forall (l: list Z) k, 0 <= k <= Zlength l -> Zlength (firstn (Z.to_nat k) l) = k.
Proof.
  intros l k Hk. rewrite Zlength_correct, firstn_length_le by (rewrite Zlength_correct in Hk; lia). lia.
Qed.

Lemma fr_le_field_firstn : forall (l: list Z) j i k, 0 <= i -> 0 <= k -> i + k <= j ->
  le_field (firstn (Z.to_nat j) l) i k = le_field l i k.
Proof.
  intros l j i k Hi Hk Hj. unfold le_field, slice. f_equal.
  rewrite skipn_firstn_comm, firstn_firstn. f_equal. lia.
Qed.

Lemma fr_byte_at_firstn : forall (l: list Z) j i, 0 <= i < j -> byte_at (firstn (Z.to_nat j) l) i = byte_at l i.
Proof.
  intros l j i Hi. unfold byte_at. rewrite nth_firstn.
  destruct (Nat.ltb_spec (Z.to_nat i) (Z.to_nat j)); [reflexivity | lia].
Qed.

Lemma fr_block_props_firstn : forall (l: list Z) j, 3 <= j ->
  block_props_of (firstn (Z.to_nat j) l) = block_props_of l.
Proof. intros. unfold block_props_of. rewrite fr_le_field_firstn by lia. reflexivity. Qed.

(* Block_Type 3 after the Z.lor 6 of the header's first byte *)
Definition fr_lor6_ok (a: Z) : bool :=
  ((Z.lor a 6 / 2) mod 4 =? 3) && (0 <=? Z.lor a 6) && (Z.lor a 6 <? 256).

Lemma fr_lor6 : forall a, 0 <= a < 256 -> (Z.lor a 6 / 2) mod 4 = 3 /\ 0 <= Z.lor a 6 < 256.
Proof.
  intros a Ha.
  assert (H: forallb fr_lor6_ok (map Z.of_nat (seq 0 256)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. specialize (H a).
  assert (Hin: In a (map Z.of_nat (seq 0 256))).
  { apply in_map_iff. exists (Z.to_nat a). split; [lia | apply in_seq; lia]. }
  specialize (H Hin). unfold fr_lor6_ok in H.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.eqb_eq in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3. lia.
Qed.

Lemma fr_type3 : forall a x, 0 <= a < 256 -> Z.land (Z.shiftr (Z.lor a 6 + 256 * x) 1) 3 = 3.
Proof.
  intros a x Ha. destruct (fr_lor6 a Ha) as [H1 _].
  change 3 with (Z.ones 2) at 1. rewrite Z.land_ones by lia. rewrite Z.shiftr_div_pow2 by lia.
  change (2 ^ 1) with 2. change (2 ^ 2) with 4.
  replace (Z.lor a 6 + 256 * x) with (Z.lor a 6 + (128 * x) * 2) by lia. rewrite Z.div_add by lia.
  replace (Z.lor a 6 / 2 + 128 * x) with (Z.lor a 6 / 2 + (32 * x) * 4) by lia. rewrite Z.mod_add by lia.
  exact H1.
Qed.

Lemma fr_reserve_ok : forall l off, bytes_ok l -> bytes_ok (nf_reserve l off).
Proof.
  intros l off H. unfold nf_reserve. apply ff_bytes_ok_app; [apply fr_bytes_ok_firstn; auto |].
  constructor.
  - apply fr_lor6. apply ff_byte_at_ok. auto.
  - unfold bytes_ok in *. rewrite <- (firstn_skipn (S (Z.to_nat off)) l) in H. apply Forall_app in H. tauto.
Qed.

Lemma fr_reserve_app : forall (a l: list Z) off, 0 <= off ->
  nf_reserve (a ++ l) (Zlength a + off) = a ++ nf_reserve l off.
Proof.
  intros a l off Hoff. unfold nf_reserve, byte_at.
  replace (Z.to_nat (Zlength a + off)) with (length a + Z.to_nat off)%nat by (rewrite Zlength_correct; lia).
  rewrite firstn_app_2, app_nth2_plus, <- app_assoc. f_equal. f_equal. f_equal.
  replace (S (length a + Z.to_nat off)) with (length a + S (Z.to_nat off))%nat by lia.
  rewrite skipn_app, skipn_all2 by lia. rewrite app_nil_l. f_equal. lia.
Qed.

Lemma fr_Zlength_reserve : forall l off, 0 <= off < Zlength l -> Zlength (nf_reserve l off) = Zlength l.
Proof.
  intros l off H. unfold nf_reserve. rewrite ff_Zlength_app, Zlength_cons, !Zlength_correct, firstn_length_le,
    length_skipn by (rewrite Zlength_correct in H; lia). rewrite Zlength_correct in H. lia.
Qed.

(* ---------- the block walk of Refuse.blocks_refused over the writer's blocks ---------- *)

(* a block's bytes after its header, and its part of the content *)
Definition nb_body (d: list Z) (done: Z) (b: nf_block) : list Z :=
  if nb_rle b then [if nb_size b =? 0 then nb_byte b else byte_at d done] else slice d done (nb_size b).
Definition nb_chunk (d: list Z) (done: Z) (b: nf_block) : list Z :=
  if nb_rle b then repeat (byte_at d done) (Z.to_nat (nb_size b)) else slice d done (nb_size b).

Lemma fr_blocks_bytes_cons : forall d done b bl,
  nf_blocks_bytes d done (b :: bl) =
  nb_header (is_nil bl) b ++ nb_body d done b ++ nf_blocks_bytes d (done + nb_size b) bl.
Proof. reflexivity. Qed.

Lemma fr_content_cons : forall d done b bl,
  nf_content d done (b :: bl) = nb_chunk d done b ++ nf_content d (done + nb_size b) bl.
Proof. reflexivity. Qed.

Lemma fr_header_Zlength : forall last b, Zlength (nb_header last b) = 3.
Proof. intros. unfold nb_header. rewrite ff_le_bytes_Zlength. reflexivity. Qed.

Lemma fr_body_Zlength : forall d done b, 0 <= done -> 0 <= nb_size b -> done + nb_size b <= Zlength d ->
  Zlength (nb_body d done b) = if nb_rle b then 1 else nb_size b.
Proof. intros. unfold nb_body. destruct (nb_rle b); [reflexivity | apply ff_slice_length; lia]. Qed.

(* one block of the walk: a Raw or RLE block goes through, with its part of the content *)
Lemma fr_step : forall dw f h st hist d done b last t out bsm,
  0 <= done -> 0 <= nb_size b < 2 ^ 21 -> done + nb_size b <= Zlength d ->
  blocks_refused dw (S f) h st hist (nb_header last b ++ nb_body d done b ++ t) out bsm =
  (if last then frame_end_refused h (out ++ nb_chunk d done b) t
   else blocks_refused dw f h st hist t (out ++ nb_chunk d done b) bsm).
Proof.
  intros dw f h st hist d done b last t out bsm Hd Hs Hn.
  pose proof (fr_body_Zlength d done b Hd ltac:(lia) Hn) as Hb.
  pose proof (fr_header_Zlength last b) as Hh.
  pose proof (ff_Zlength_nonneg t) as Ht.
  cbn [blocks_refused]. unfold cblock_size, rblock. rewrite ff_block_props by lia.
  cbn [bp_type bp_last bp_origSize]. rewrite !ff_Zlength_app, Hh, Hb. unfold ZSTD_blockHeaderSize.
  rewrite (proj2 (Z.ltb_ge _ 3)) by (destruct (nb_rle b); lia).
  unfold nb_chunk. destruct (nb_rle b) eqn:Er; cbn [zb Z.eqb Pos.eqb]; cbv iota beta.
  - rewrite Z.gtb_ltb, (proj2 (Z.ltb_ge _ _)) by lia.
    rewrite ff_slice_mid by (rewrite ?Hh, ?Hb; reflexivity).
    rewrite ff_skipn_mid by (rewrite Hh, Hb; reflexivity).
    unfold nb_body. rewrite Er.
    change (byte_at [if nb_size b =? 0 then nb_byte b else byte_at d done] 0)
      with (if nb_size b =? 0 then nb_byte b else byte_at d done).
    rewrite ff_repeat_rle. destruct last; reflexivity.
  - rewrite Z.gtb_ltb, (proj2 (Z.ltb_ge _ _)) by lia.
    rewrite ff_slice_mid by (rewrite ?Hh, ?Hb; reflexivity).
    rewrite ff_skipn_mid by (rewrite Hh, Hb; reflexivity).
    unfold nb_body. rewrite Er.
    destruct last; reflexivity.
Qed.

(* the whole walk: after the last block, the end of the frame decides *)
Lemma fr_blocks_end : forall dw d mb h st hist bsm bl done out t fuel,
  0 <= done <= Zlength d -> mb <= 131072 -> nf_blocks_ok mb (Zlength d) done bl ->
  (length (nf_blocks_bytes d done bl) <= fuel)%nat ->
  frame_end_refused h (out ++ nf_content d done bl) t ->
  blocks_refused dw fuel h st hist (nf_blocks_bytes d done bl ++ t) out bsm.
Proof.
  intros dw d mb h st hist bsm bl. induction bl as [| b bl IH]; intros done out t fuel Hd Hmb H Hf Hend;
    [destruct H |].
  pose proof (ff_block_bound _ _ _ _ _ Hd Hmb H) as Hs.
  rewrite fr_blocks_bytes_cons in *. rewrite fr_content_cons in Hend. rewrite !length_app in Hf.
  pose proof (fr_header_Zlength (is_nil bl) b) as Hh. rewrite Zlength_correct in Hh.
  destruct fuel as [| f]; [lia |]. rewrite <- !app_assoc, fr_step by lia.
  destruct H as (_ & _ & _ & _ & Hr). destruct bl as [| b' bl'].
  - cbn [is_nil nf_blocks_bytes nf_content] in *. rewrite app_nil_r in Hend. exact Hend.
  - cbn [is_nil]. destruct Hr as (_ & Hr). apply IH; [lia | lia | exact Hr | lia |].
    rewrite <- app_assoc. exact Hend.
Qed.

(* a cut of the blocks and the checksum after them: the walk reaches the end of the bytes inside a block, or
   after the last block with less than the 4 bytes of the checksum *)
Lemma fr_blocks_cut : forall dw d mb h st hist bsm K bl done out j fuel,
  0 <= done <= Zlength d -> mb <= 131072 -> nf_blocks_ok mb (Zlength d) done bl ->
  (K = [] \/ (fh_checksumFlag h = 1 /\ Zlength K = 4)) ->
  0 <= j < Zlength (nf_blocks_bytes d done bl) + Zlength K -> (Z.to_nat j < fuel)%nat ->
  blocks_refused dw fuel h st hist (firstn (Z.to_nat j) (nf_blocks_bytes d done bl ++ K)) out bsm.
Proof.
  intros dw d mb h st hist bsm K bl. induction bl as [| b bl IH]; intros done out j fuel Hd Hmb H HK Hj Hf;
    [destruct H |].
  pose proof (ff_block_bound _ _ _ _ _ Hd Hmb H) as Hs.
  pose proof (fr_header_Zlength (is_nil bl) b) as Hh.
  pose proof (fr_body_Zlength d done b ltac:(lia) ltac:(lia) ltac:(lia)) as Hb.
  set (c := if nb_rle b then 1 else nb_size b) in Hb.
  assert (Hc: 0 <= c) by (unfold c; destruct (nb_rle b); lia).
  rewrite fr_blocks_bytes_cons in *. rewrite <- !app_assoc.
  set (R := nf_blocks_bytes d (done + nb_size b) bl) in *.
  pose proof (ff_Zlength_nonneg R). pose proof (ff_Zlength_nonneg K).
  rewrite !ff_Zlength_app, Hh, Hb in Hj.
  destruct fuel as [| f]; [lia |].
  destruct (Z_lt_le_dec j 3) as [Lj | Lj].
  { cbn [blocks_refused]. rewrite fr_Zlength_firstn by (rewrite !ff_Zlength_app, Hh, Hb; lia).
    unfold ZSTD_blockHeaderSize. rewrite (proj2 (Z.ltb_lt _ _)) by lia. exact I. }
  destruct (Z_lt_le_dec j (3 + c)) as [Lc | Lc].
  { cbn [blocks_refused]. rewrite fr_Zlength_firstn by (rewrite !ff_Zlength_app, Hh, Hb; lia).
    unfold cblock_size. rewrite fr_Zlength_firstn by (rewrite !ff_Zlength_app, Hh, Hb; lia).
    unfold ZSTD_blockHeaderSize. rewrite (proj2 (Z.ltb_ge _ 3)) by lia.
    rewrite !fr_block_props_firstn by lia. rewrite ff_block_props by lia. cbn [bp_type bp_origSize].
    unfold c in *. destruct (nb_rle b); cbn [zb Z.eqb Pos.eqb]; cbv iota;
      rewrite Z.gtb_ltb, (proj2 (Z.ltb_lt _ _)) by lia; exact I. }
  rewrite app_assoc, fr_firstn_app_ge by (rewrite ff_Zlength_app, Hh, Hb; lia). rewrite <- app_assoc.
  rewrite fr_step by lia. rewrite ff_Zlength_app, Hh, Hb.
  destruct H as (_ & _ & _ & _ & Hr). destruct bl as [| b' bl'].
  - cbn [is_nil]. unfold R in *. cbn [nf_blocks_bytes] in *. rewrite app_nil_l.
    rewrite Zlength_nil in Hj. right.
    destruct HK as [-> | [Hck HK]]; [rewrite Zlength_nil in Hj; lia |].
    split; [exact Hck |]. rewrite fr_Zlength_firstn; lia.
  - cbn [is_nil]. destruct Hr as (_ & Hr). unfold R in *. apply IH; auto; lia.
Qed.

Lemma fr_off_nonneg : forall mb n bl done i, 0 <= done <= n -> nf_blocks_ok mb n done bl -> 0 <= nb_off bl i.
Proof.
  intros mb n bl. induction bl as [| b bl IH]; intros done i Hd H; [destruct i; simpl; lia |].
  destruct i as [| i]; [simpl; lia |]. cbn [nb_off].
  pose proof (ff_block_size _ _ _ _ _ Hd H) as Hs.
  destruct H as (_ & _ & _ & _ & Hr). destruct bl as [| b' bl'].
  - destruct i; cbn [nb_off]; destruct (nb_rle b); lia.
  - destruct Hr as (_ & Hr). specialize (IH (done + nb_size b) i ltac:(lia) Hr). destruct (nb_rle b); lia.
Qed.

(* the walk with the header of block i made Reserved: it goes through the blocks before it and stops there *)
Lemma fr_blocks_reserved : forall dw d mb h st hist bsm bl done out t i fuel,
  0 <= done <= Zlength d -> mb <= 131072 -> nf_blocks_ok mb (Zlength d) done bl ->
  (i < length bl)%nat -> (length (nf_blocks_bytes d done bl) <= fuel)%nat ->
  blocks_refused dw fuel h st hist (nf_reserve (nf_blocks_bytes d done bl ++ t) (nb_off bl i)) out bsm.
Proof.
  intros dw d mb h st hist bsm bl. induction bl as [| b bl IH]; intros done out t i fuel Hd Hmb H Hi Hf;
    [destruct H |].
  pose proof (ff_block_bound _ _ _ _ _ Hd Hmb H) as Hs.
  pose proof (fr_header_Zlength (is_nil bl) b) as Hh.
  pose proof (fr_body_Zlength d done b ltac:(lia) ltac:(lia) ltac:(lia)) as Hb.
  rewrite fr_blocks_bytes_cons in *. rewrite length_app in Hf. rewrite Zlength_correct in Hh.
  destruct fuel as [| f]; [lia |].
  destruct i as [| i].
  - (* this block: Block_Type 3 *)
    cbn [nb_off]. unfold nf_reserve. change (Z.to_nat 0) with O. cbn [firstn skipn app].
    unfold nb_header. set (v := zb (is_nil bl) + 2 * zb (nb_rle b) + 8 * nb_size b).
    cbn [le_bytes app]. unfold byte_at. cbn [nth Z.to_nat].
    cbn [blocks_refused]. rewrite Zlength_cons, !Zlength_cons.
    pose proof (ff_Zlength_nonneg ((nb_body d done b ++ nf_blocks_bytes d (done + nb_size b) bl) ++ t)).
    unfold ZSTD_blockHeaderSize. rewrite (proj2 (Z.ltb_ge _ 3)) by lia.
    unfold block_props_of, le_field, slice. cbn [Z.to_nat skipn firstn le_value bp_type].
    change (Pos.to_nat 3) with 3%nat. cbn [firstn le_value].
    rewrite fr_type3 by (apply Z.mod_pos_bound; lia). exact I.
  - (* an earlier block: it goes through *)
    assert (Hil: bl <> []) by (intros ->; cbn in Hi; lia).
    destruct H as (_ & _ & _ & _ & Hr). destruct bl as [| b' bl']; [congruence |]. destruct Hr as (Hpos & Hr).
    change (nb_off (b :: b' :: bl') (S i)) with (3 + (if nb_rle b then 1 else nb_size b) + nb_off (b' :: bl') i).
    rewrite <- !app_assoc.
    pose proof (fr_off_nonneg mb (Zlength d) (b' :: bl') (done + nb_size b) i ltac:(lia) Hr) as Ho.
    replace (3 + (if nb_rle b then 1 else nb_size b) + nb_off (b' :: bl') i)
      with (Zlength (nb_header (is_nil (b' :: bl')) b ++ nb_body d done b) + nb_off (b' :: bl') i)
      by (rewrite ff_Zlength_app, Zlength_correct, Hh, Hb; lia).
    rewrite (app_assoc (nb_header _ b) (nb_body d done b)), fr_reserve_app by exact Ho.
    rewrite <- app_assoc, fr_step by lia. cbn [is_nil].
    rewrite length_app in Hf. cbn [length] in Hi. apply IH; cbn [length]; auto; lia.
Qed.

(* ---------- the frame, the series ---------- *)

(* a series that starts as a Zstandard frame every dictionary refuses is refused (Params.walk_m takes the
   current dictionary or the one sel gives for the Dictionary_ID: the refusal holds for each) *)
Lemma fr_series_frame : forall md sel dm s,
  md_magicless md = false -> bytes_ok s -> 5 <= Zlength s -> le_field s 0 4 = ZSTD_MAGICNUMBER ->
  (forall d', frame_refused_m md d' no_wlim s) ->
  series_refused_m md sel (Some dm) no_wlim s.
Proof.
  intros md sel dm s Hmg Hs H5 Hm Hr. unfold series_refused_m. cbn [walk_refused]. rewrite Hmg.
  unfold starting_len, ZSTD_FRAMEHEADERSIZE_PREFIX. rewrite (proj2 (Z.ltb_ge _ 5)) by lia.
  rewrite Hm. change (negb false && is_skippable_magic ZSTD_MAGICNUMBER) with false. cbv iota.
  assert (Hd: exists d', frame_dict false sel (Some dm) s = Some d').
  { unfold frame_dict. destruct (get_frame_header_m false s) as [| k | h0]; eauto.
    destruct (sel (fh_dictID h0)); eauto. }
  destruct Hd as [d' Hd]. rewrite Hd.
  rewrite frame_refused_funk; auto.
  rewrite Hmg. unfold starting_len, ZSTD_FRAMEHEADERSIZE_PREFIX. lia.
Qed.

(* a cut inside the frame's header: zstd waits for the rest of it *)
Lemma fr_frame_short : forall md d' wlim s,
  md_magicless md = false -> Zlength s < fhd_header_size (byte_at s 4) -> frame_refused_m md d' wlim s.
Proof.
  intros md d' wlim s Hmg H. unfold frame_refused_m, header_size_m. rewrite Hmg.
  rewrite (proj2 (Z.ltb_lt _ _)) by exact H. exact I.
Qed.

(* the writer's header (with no Dictionary_ID or 0) followed by blocks the walk refuses *)
Lemma fr_frame_blocks : forall md d' fcs maxw h X,
  md_magicless md = false -> nh_ok fcs maxw 0 h -> 0 <= fcs < 2 ^ 64 -> maxw < 2 ^ 32 ->
  blocks_refused (md_dwin md) (S (length X)) (nf_header_of fcs 0 h) (dm_state d') (dm_content d') X nil
    (Z.min (nh_max_block fcs h) (md_bmax md)) ->
  frame_refused_m md d' no_wlim (nh_bytes fcs 0 h ++ X).
Proof.
  intros md d' fcs maxw h X Hmg Hh Hfcs Hmw HX.
  pose proof (nf_wlog_ok _ _ _ _ Hh Hmw) as Hw.
  destruct (ff_nh_read fcs maxw 0 h X Hh Hfcs ltac:(lia)) as (_ & H4 & _).
  pose proof Hh as (Hf03 & _ & _ & _ & _ & Hbits & Hd03 & _).
  destruct (ff_fhd_facts h Hf03 Hbits Hd03) as (_ & _ & _ & _ & _ & _ & _ & Hhs).
  pose proof (ff_nh_bytes_Zlength _ _ _ _ Hh) as Hlen.
  pose proof (ff_Zlength_nonneg X).
  unfold frame_refused_m, header_size_m. rewrite Hmg. rewrite H4, Hhs, <- Hlen, ff_Zlength_app.
  rewrite (proj2 (Z.ltb_ge _ _)) by lia.
  change (get_frame_header_m false (nh_bytes fcs 0 h ++ X)) with (get_frame_header (nh_bytes fcs 0 h ++ X)).
  rewrite (ff_get_frame_header fcs maxw 0 h X Hh Hfcs ltac:(lia) Hw).
  cbn [nf_header_of fh_windowSize fh_frameType fh_dictID fh_headerSize fh_blockSizeMax].
  destruct Hh as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwin).
  split; [unfold no_wlim; lia |]. split; [reflexivity |]. split; [left; reflexivity |].
  rewrite ff_skipn_app by reflexivity. exact HX.
Qed.

Lemma fr_length_reserve : forall (l: list Z) off, (length l <= length (nf_reserve l off))%nat.
Proof. intros. unfold nf_reserve. rewrite length_app. cbn [length]. rewrite length_firstn, length_skipn. lia. Qed.

(* the writer's frame: its header is at least 5 bytes, starts with the magic number *)
Lemma fr_header_facts : forall fcs maxw h t, nh_ok fcs maxw 0 h -> 0 <= fcs < 2 ^ 64 ->
  5 <= Zlength (nh_bytes fcs 0 h) /\ le_field (nh_bytes fcs 0 h ++ t) 0 4 = ZSTD_MAGICNUMBER /\
  byte_at (nh_bytes fcs 0 h ++ t) 4 = nh_fhd h /\
  fhd_header_size (nh_fhd h) = Zlength (nh_bytes fcs 0 h).
Proof.
  intros fcs maxw h t Hh Hfcs.
  destruct (ff_nh_read fcs maxw 0 h t Hh Hfcs ltac:(lia)) as (Hm & H4 & _).
  pose proof Hh as (Hf03 & _ & _ & _ & _ & Hbits & Hd03 & _).
  destruct (ff_fhd_facts h Hf03 Hbits Hd03) as (_ & _ & _ & _ & _ & _ & _ & Hhs).
  pose proof (ff_nh_bytes_Zlength _ _ _ _ Hh) as Hlen.
  pose proof (ff_field_sizes _ _ _ _ Hh) as Hs. pose proof (ff_fcs_size_single _ _ _ _ Hh) as Hz.
  repeat split; auto; lia.
Qed.

(* ---------- the three refusals ---------- *)

(* rj_content_size: a Frame_Content_Size field declaring fcs, other than the content's size |d| *)
Theorem nf_refused_content_size : forall md sel dm d fcs maxw c,
  md_magicless md = false -> bytes_ok d -> nf_ok (Zlength d) fcs maxw 0 c -> maxw < 2 ^ 32 ->
  0 <= fcs < ZSTD_CONTENTSIZE_UNKNOWN -> Zlength d < 2 ^ 64 -> fcs <> Zlength d ->
  (nh_fcs_flag (nc_hdr c) <> 0 \/ nh_single (nc_hdr c) = true) ->
  series_refused_m md sel (Some dm) no_wlim (nf_bytes d fcs 0 c).
Proof.
  intros md sel dm d fcs maxw c Hmg Hd Hok Hmw Hfcs Hn Hne Hfield.
  unfold ZSTD_CONTENTSIZE_UNKNOWN in Hfcs.
  pose proof (nf_bytes_ok _ _ _ _ _ Hok Hd) as HF.
  pose proof (nf_data_length _ _ _ _ _ Hok) as Hdl.
  destruct Hok as [Hh Hb].
  destruct (fr_header_facts fcs maxw (nc_hdr c) (nf_blocks_bytes d 0 (nc_blocks c) ++ nf_checksum d c) Hh
              ltac:(lia)) as (H5 & Hm & _).
  unfold nf_bytes in *. apply fr_series_frame; auto.
  { rewrite ff_Zlength_app. pose proof (ff_Zlength_nonneg (nf_blocks_bytes d 0 (nc_blocks c) ++ nf_checksum d c)).
    lia. }
  intros d'. apply (fr_frame_blocks md d' fcs maxw); auto; [lia |].
  pose proof (ff_Zlength_nonneg d).
  apply fr_blocks_end with (mb := nh_max_block fcs (nc_hdr c)); [lia | apply Z.le_min_r | exact Hb
                                                                 | rewrite length_app; lia |].
  left. cbn [nf_header_of fh_contentSize].
  assert (E: (nh_fcs_flag (nc_hdr c) =? 0) && negb (nh_single (nc_hdr c)) = false).
  { destruct Hfield as [E | E]; [rewrite (proj2 (Z.eqb_neq _ _) E); reflexivity
                                | rewrite E, Bool.andb_false_r; reflexivity]. }
  rewrite E. unfold ZSTD_CONTENTSIZE_UNKNOWN. split; [lia |].
  rewrite app_nil_l. change (nf_content d 0 (nc_blocks c)) with (nf_data d c). rewrite Hdl.
  pose proof (ff_Zlength_nonneg d). rewrite Z.mod_small by lia. lia.
Qed.

(* rj_truncated: the first k bytes of the frame, 0 < k < |F| *)
Theorem nf_refused_truncated : forall md sel dm d maxw c k,
  md_magicless md = false -> bytes_ok d -> nf_ok (Zlength d) (Zlength d) maxw 0 c -> maxw < 2 ^ 32 ->
  Zlength d < 2 ^ 64 -> 0 < k < Zlength (nf_bytes d (Zlength d) 0 c) ->
  series_refused_m md sel (Some dm) no_wlim (firstn (Z.to_nat k) (nf_bytes d (Zlength d) 0 c)).
Proof.
  intros md sel dm d maxw c k Hmg Hd Hok Hmw Hn Hk.
  pose proof (ff_Zlength_nonneg d) as Hn0.
  pose proof (nf_bytes_ok _ _ _ _ _ Hok Hd) as HF.
  set (F := nf_bytes d (Zlength d) 0 c) in *.
  assert (HkF: Zlength (firstn (Z.to_nat k) F) = k) by (apply fr_Zlength_firstn; lia).
  destruct (Z_lt_le_dec k 5) as [L5 | L5].
  { unfold series_refused_m. cbn [walk_refused]. rewrite Hmg, HkF. unfold starting_len, ZSTD_FRAMEHEADERSIZE_PREFIX.
    rewrite (proj2 (Z.ltb_lt _ _)) by lia. lia. }
  destruct Hok as [Hh Hb].
  set (H := nh_bytes (Zlength d) 0 (nc_hdr c)).
  set (BK := nf_blocks_bytes d 0 (nc_blocks c) ++ nf_checksum d c).
  assert (EF: F = H ++ BK) by reflexivity.
  destruct (fr_header_facts (Zlength d) maxw (nc_hdr c) BK Hh ltac:(lia)) as (H5 & Hm & H4 & Hhs).
  fold H in H5, Hm, H4, Hhs. rewrite <- EF in Hm, H4.
  apply fr_series_frame; auto.
  { apply fr_bytes_ok_firstn. exact HF. }
  { lia. }
  { rewrite fr_le_field_firstn by lia. exact Hm. }
  intros d'. destruct (Z_lt_le_dec k (Zlength H)) as [LH | LH].
  { apply fr_frame_short; auto. rewrite fr_byte_at_firstn by lia. rewrite H4, Hhs. lia. }
  rewrite EF, fr_firstn_app_ge by exact LH.
  apply (fr_frame_blocks md d' (Zlength d) maxw); auto.
  assert (HBK: Zlength F = Zlength H + Zlength BK) by (rewrite EF; apply ff_Zlength_app).
  unfold BK in *. rewrite ff_Zlength_app in HBK.
  apply fr_blocks_cut with (mb := nh_max_block (Zlength d) (nc_hdr c)); [lia | apply Z.le_min_r | exact Hb | | lia |].
  - unfold nf_checksum. destruct (nh_checksum (nc_hdr c)) eqn:E; [right | left; reflexivity].
    cbn [nf_header_of fh_checksumFlag]. rewrite E. split; [reflexivity |]. apply ff_le_bytes_Zlength.
  - rewrite firstn_length_le; [lia |]. rewrite <- ff_Zlength_app, (Zlength_correct (_ ++ _)) in HBK. lia.
Qed.

(* rj_reserved_block: the header of block i made Reserved (Block_Type 3) *)
Theorem nf_refused_reserved : forall md sel dm d fcs maxw c i,
  md_magicless md = false -> bytes_ok d -> nf_ok (Zlength d) fcs maxw 0 c -> maxw < 2 ^ 32 ->
  0 <= fcs < 2 ^ 64 -> (i < length (nc_blocks c))%nat ->
  series_refused_m md sel (Some dm) no_wlim (nf_reserve (nf_bytes d fcs 0 c) (nf_block_off fcs 0 c i)).
Proof.
  intros md sel dm d fcs maxw c i Hmg Hd Hok Hmw Hfcs Hi.
  pose proof (fr_reserve_ok _ (nf_block_off fcs 0 c i) (nf_bytes_ok _ _ _ _ _ Hok Hd)) as HF.
  pose proof (ff_Zlength_nonneg d) as Hn0.
  destruct Hok as [Hh Hb].
  pose proof (fr_off_nonneg _ (Zlength d) (nc_blocks c) 0 i ltac:(lia) Hb) as Ho.
  unfold nf_bytes, nf_block_off in *. rewrite fr_reserve_app in * by exact Ho.
  set (X := nf_reserve (nf_blocks_bytes d 0 (nc_blocks c) ++ nf_checksum d c) (nb_off (nc_blocks c) i)) in *.
  destruct (fr_header_facts fcs maxw (nc_hdr c) X Hh Hfcs) as (H5 & Hm & _).
  apply fr_series_frame; auto.
  { rewrite ff_Zlength_app. pose proof (ff_Zlength_nonneg X). lia. }
  intros d'. apply (fr_frame_blocks md d' fcs maxw); auto.
  apply fr_blocks_reserved with (mb := nh_max_block fcs (nc_hdr c)); [lia | apply Z.le_min_r | exact Hb | exact Hi |].
  unfold X. pose proof (fr_length_reserve (nf_blocks_bytes d 0 (nc_blocks c) ++ nf_checksum d c)
                          (nb_off (nc_blocks c) i)).
  rewrite length_app in H. lia.
Qed.

(* ---------- the byte rj_reserved_block.c changes ---------- *)

Lemma fr_lor_shiftl : forall a b k, 0 <= k -> 0 <= a < 2 ^ k -> 0 <= b -> Z.lor a (Z.shiftl b k) = a + b * 2 ^ k.
Proof.
  intros a b k Hk Ha Hb. rewrite Z.shiftl_mul_pow2 by lia.
  assert (Hp: 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  apply Z.bits_inj'. intros n Hn. rewrite Z.lor_spec. destruct (Z.lt_ge_cases n k) as [L | L].
  - rewrite Z.mul_pow2_bits_low by lia. rewrite Bool.orb_false_r.
    rewrite <- (Z.mod_pow2_bits_low (a + b * 2 ^ k) k n) by lia.
    rewrite Z.mod_add, Z.mod_small by lia. reflexivity.
  - rewrite <- (Z.mod_small a (2 ^ k)) at 1 by lia. rewrite Z.mod_pow2_bits_high by lia. cbn [orb].
    rewrite Z.mul_pow2_bits by lia.
    replace n with ((n - k) + k) at 2 by lia. rewrite <- Z.div_pow2_bits by lia.
    rewrite Z.div_add, Z.div_small by lia. reflexivity.
Qed.

Lemma fr_land_mod256_1 : forall v, Z.land (v mod 256) 1 = Z.land v 1.
Proof.
  intros v. apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec. destruct (Z.lt_ge_cases n 1).
  - change 256 with (2 ^ 8). rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - replace (Z.testbit 1 n) with false; [rewrite !Bool.andb_false_r; reflexivity |].
    symmetry. change 1 with (Z.ones 1) at 1. apply Z.ones_spec_high. lia.
Qed.

Lemma fr_land_mod256_type : forall v, Z.land (Z.shiftr (v mod 256) 1) 3 = Z.land (Z.shiftr v 1) 3.
Proof.
  intros v. apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec, !Z.shiftr_spec by lia.
  destruct (Z.lt_ge_cases n 2).
  - change 256 with (2 ^ 8). rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - replace (Z.testbit 3 n) with false; [rewrite !Bool.andb_false_r; reflexivity |].
    symmetry. change 3 with (Z.ones 2). apply Z.ones_spec_high. lia.
Qed.

(* the C reading of a Block_Header written by new_frame: Last_Block, Block_Type, Block_Size *)
Lemma fr_header_read : forall last rle s, 0 <= s < 2 ^ 21 ->
  let v := zb last + 2 * zb rle + 8 * s in
  Z.land (v mod 256) 1 = zb last /\
  Z.land (Z.shiftr (v mod 256) 1) 3 = zb rle /\
  Z.shiftr (Z.lor (Z.lor (v mod 256) (Z.shiftl ((v / 256) mod 256) 8)) (Z.shiftl ((v / 256 / 256) mod 256) 16)) 3
    = s.
Proof.
  intros last rle s Hs v.
  assert (Hl: 0 <= zb last <= 1) by (destruct last; simpl; lia).
  assert (Hr: 0 <= zb rle <= 1) by (destruct rle; simpl; lia).
  split; [| split].
  - rewrite fr_land_mod256_1. change (Z.land v 1) with (Z.land v (Z.ones 1)). rewrite Z.land_ones by lia.
    change (2 ^ 1) with 2. unfold v.
    replace (zb last + 2 * zb rle + 8 * s) with (zb last + (zb rle + 4 * s) * 2) by lia.
    rewrite Z.mod_add, Z.mod_small by lia. reflexivity.
  - rewrite fr_land_mod256_type. change 3 with (Z.ones 2). rewrite Z.land_ones by lia.
    rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2. change (2 ^ 2) with 4. unfold v.
    replace (zb last + 2 * zb rle + 8 * s) with (zb last + (zb rle + 4 * s) * 2) by lia.
    rewrite Z.div_add, (Z.div_small (zb last)) by lia.
    replace (0 + (zb rle + 4 * s)) with (zb rle + s * 4) by lia.
    rewrite Z.mod_add, Z.mod_small by lia. reflexivity.
  - assert (Hv: 0 <= v < 2 ^ 24) by (unfold v; change (2 ^ 21) with 2097152 in Hs; change (2 ^ 24) with 16777216; lia).
    pose proof (ff_le_value_le_bytes 3 v) as Hle. cbn [le_bytes le_value] in Hle.
    change (2 ^ (8 * Z.of_nat 3)) with (2 ^ 24) in Hle. rewrite (Z.mod_small v (2 ^ 24)) in Hle by exact Hv.
    assert (H0: 0 <= v mod 256 < 256) by (apply Z.mod_pos_bound; lia).
    assert (H1: 0 <= (v / 256) mod 256 < 256) by (apply Z.mod_pos_bound; lia).
    assert (H2: 0 <= (v / 256 / 256) mod 256 < 256) by (apply Z.mod_pos_bound; lia).
    rewrite (fr_lor_shiftl _ _ 8) by (change (2 ^ 8) with 256; lia).
    rewrite (fr_lor_shiftl _ _ 16) by (change (2 ^ 16) with 65536; change (2 ^ 8) with 256; lia).
    change (2 ^ 8) with 256. change (2 ^ 16) with 65536.
    replace (v mod 256 + (v / 256) mod 256 * 256 + (v / 256 / 256) mod 256 * 65536) with v by lia.
    rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. unfold v.
    replace (zb last + 2 * zb rle + 8 * s) with ((zb last + 2 * zb rle) + s * 8) by lia.
    rewrite Z.div_add, Z.div_small by lia. lia.
Qed.

Lemma fr_byte_at_mid : forall (p r: list Z) v,
  byte_at (p ++ le_bytes 3 v ++ r) (Zlength p) = v mod 256 /\
  byte_at (p ++ le_bytes 3 v ++ r) (Zlength p + 1) = (v / 256) mod 256 /\
  byte_at (p ++ le_bytes 3 v ++ r) (Zlength p + 2) = (v / 256 / 256) mod 256.
Proof.
  intros p r v. unfold byte_at. rewrite Zlength_correct.
  replace (Z.to_nat (Z.of_nat (length p) + 1)) with (length p + 1)%nat by lia.
  replace (Z.to_nat (Z.of_nat (length p) + 2)) with (length p + 2)%nat by lia.
  rewrite Nat2Z.id, <- (Nat.add_0_r (length p)) at 1.
  rewrite !app_nth2_plus. split; [| split]; reflexivity.
Qed.

(* the loop over the blocks: it stops at the last block or after skip blocks *)
Lemma fr_rb_skip : forall d mb bl done p t skip, 0 <= done <= Zlength d -> mb <= 131072 ->
  nf_blocks_ok mb (Zlength d) done bl ->
  rb_skip (p ++ nf_blocks_bytes d done bl ++ t) skip (Zlength p) =
  Zlength p + nb_off bl (Nat.min skip (length bl - 1)).
Proof.
  intros d mb bl. induction bl as [| b bl IH]; intros done p t skip Hd Hmb H; [destruct H |].
  pose proof (ff_block_bound _ _ _ _ _ Hd Hmb H) as Hs.
  destruct skip as [| k]; [cbn [rb_skip Nat.min nb_off]; lia |].
  pose proof (fr_body_Zlength d done b ltac:(lia) ltac:(lia) ltac:(lia)) as Hb.
  pose proof (fr_header_Zlength (is_nil bl) b) as Hh.
  rewrite fr_blocks_bytes_cons, <- !app_assoc. cbn [rb_skip].
  unfold nb_header.
  set (R := nb_body d done b ++ nf_blocks_bytes d (done + nb_size b) bl ++ t).
  destruct (fr_byte_at_mid p R (zb (is_nil bl) + 2 * zb (nb_rle b) + 8 * nb_size b)) as (B0 & B1 & B2).
  rewrite B0, B1, B2.
  destruct (fr_header_read (is_nil bl) (nb_rle b) (nb_size b) ltac:(lia)) as (E1 & E2 & E3).
  rewrite E1, E2, E3.
  destruct H as (_ & _ & _ & _ & Hr). destruct bl as [| b' bl'].
  - cbn [is_nil zb Z.eqb Pos.eqb]. cbv iota. cbn [length Nat.sub Nat.min nb_off]. lia.
  - cbn [is_nil zb Z.eqb Pos.eqb]. cbv iota. destruct Hr as (_ & Hr).
    change (le_bytes 3 (0 + 2 * zb (nb_rle b) + 8 * nb_size b)) with (nb_header false b).
    unfold R. rewrite !app_assoc, <- (app_assoc p), <- (app_assoc (p ++ _)).
    replace (Zlength p + 3 + (if zb (nb_rle b) =? 1 then 1 else nb_size b))
      with (Zlength ((p ++ nb_header false b) ++ nb_body d done b))
      by (rewrite !ff_Zlength_app, fr_header_Zlength, Hb; destruct (nb_rle b); reflexivity || lia).
    rewrite <- (app_assoc p (nb_header false b) (nb_body d done b)), (IH (done + nb_size b)) by (auto; lia).
    replace (length (b :: b' :: bl') - 1)%nat with (S (length (b' :: bl') - 1)) by (cbn; lia).
    cbn [Nat.min]. change (nb_off (b :: b' :: bl') (S (Nat.min k (length (b' :: bl') - 1))))
      with (3 + (if nb_rle b then 1 else nb_size b) + nb_off (b' :: bl') (Nat.min k (length (b' :: bl') - 1))).
    rewrite !ff_Zlength_app, fr_header_Zlength, Hb. lia.
Qed.

(* rj_reserved_block.c's offset, for any skip, is the header of block min(skip, last) of the frame *)
Theorem nf_reserved_at_harness : forall d fcs maxw did c skip,
  nf_ok (Zlength d) fcs maxw did c -> 0 <= fcs < 2 ^ 64 -> 0 <= did < 2 ^ 32 ->
  rb_skip (nf_bytes d fcs did c) skip (rb_first (nf_bytes d fcs did c)) =
  nf_block_off fcs did c (Nat.min skip (length (nc_blocks c) - 1)).
Proof.
  intros d fcs maxw did c skip [Hh Hb] Hfcs Hdid.
  pose proof (ff_Zlength_nonneg d) as Hn0.
  set (H := nh_bytes fcs did (nc_hdr c)).
  change (nf_bytes d fcs did c) with (H ++ nf_blocks_bytes d 0 (nc_blocks c) ++ nf_checksum d c).
  assert (Ef: rb_first (H ++ nf_blocks_bytes d 0 (nc_blocks c) ++ nf_checksum d c) = Zlength H).
  { destruct (ff_nh_read fcs maxw did (nc_hdr c) (nf_blocks_bytes d 0 (nc_blocks c) ++ nf_checksum d c) Hh Hfcs Hdid)
      as (_ & H4 & _).
    pose proof Hh as (Hf03 & _ & _ & _ & _ & Hbits & Hd03 & _).
    destruct (ff_fhd_facts _ Hf03 Hbits Hd03) as (_ & Hd3 & Hs5 & Hf6 & _).
    unfold rb_first. fold H in H4. rewrite H4, Hd3, Hs5, Hf6.
    unfold H. rewrite (ff_nh_bytes_Zlength _ _ _ _ Hh). unfold nh_did_size, nh_fcs_size.
    destruct (ff_flag_cases _ Hf03) as [E | [E | [E | E]]]; rewrite E;
    destruct (ff_flag_cases _ Hd03) as [E' | [E' | [E' | E']]]; rewrite E';
    destruct (nh_single (nc_hdr c)); reflexivity. }
  rewrite Ef. unfold nf_block_off. fold H.
  apply (fr_rb_skip d (nh_max_block fcs (nc_hdr c))); [lia | apply Z.le_min_r | exact Hb].
Qed.
