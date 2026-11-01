(* valid_bufferless: the buffer-less model (model/Params.v bl_step) on the frames the writer writes (plain Coq).
   A frame f of a written series ws, begun with the dictionary model dm it was written for, fed exactly the
   bytes zstd asks for. *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Block Zstd.proof.model.Series.
Require Import Zstd.proof.model.StreamModel Zstd.proof.model.Params Zstd.proof.model.ParamsDflt.
Require Export Zstd.proof.harness.writer.SeriesLemmas.
Local Open Scope bool_scope.

(* b is the state after feeding the first i bytes of the frame's bytes fb from bl_init, in the pieces zstd
   asked for, every step succeeding (each piece non-empty: the harness never calls ZSTD_decompressContinue when
   zstd asks for 0 bytes) *)
Definition vbl_reach (dm: dict_model) (fb: list Z) (i: Z) (b: blst) : Prop :=
  0 <= i <= Zlength fb /\
  exists pieces, bl_run md_dflt dm (bl_init md_dflt dm) pieces = Some b /\ concat pieces = slice fb 0 i /\
    Forall (fun c => c <> nil) pieces.

(* ---------- helpers of vbl_frame ---------- *)

Lemma vbf_skipn_len (l: list Z) (i: Z) : 0 <= i <= Zlength l -> Zlength (skipn (Z.to_nat i) l) = Zlength l - i.
Proof. intros H. rewrite !Zlength_correct, length_skipn in *. lia. Qed.

Lemma vbf_firstn_len (l: list Z) (i: Z) : 0 <= i <= Zlength l -> Zlength (firstn (Z.to_nat i) l) = i.
Proof. intros H. rewrite !Zlength_correct, length_firstn in *. lia. Qed.

Lemma vbf_skipn_skipn (l: list Z) (i j: Z) : 0 <= i -> 0 <= j ->
  skipn (Z.to_nat j) (skipn (Z.to_nat i) l) = skipn (Z.to_nat (i + j)) l.
Proof. intros Hi Hj. rewrite skipn_skipn. f_equal. lia. Qed.

Lemma vbf_slice_skipn (l: list Z) (i j k: Z) : 0 <= i -> 0 <= j ->
  slice (skipn (Z.to_nat i) l) j k = slice l (i + j) k.
Proof. intros Hi Hj. unfold slice. rewrite vbf_skipn_skipn by lia. reflexivity. Qed.

Lemma vbf_le_field_firstn (l: list Z) (m p k: Z) : 0 <= p -> 0 <= k -> p + k <= m ->
  le_field (firstn (Z.to_nat m) l) p k = le_field l p k.
Proof.
  intros Hp Hk H. unfold le_field. f_equal. apply (sl_firstn_agree _ _ (Z.to_nat m)); [|lia].
  rewrite firstn_firstn. f_equal. lia.
Qed.

Lemma vbf_byte_at_firstn (l: list Z) (m p: Z) : 0 <= p < m -> byte_at (firstn (Z.to_nat m) l) p = byte_at l p.
Proof.
  intros H. apply (sl_byte_at_agree _ _ (Z.to_nat m)); [|lia|lia].
  rewrite firstn_firstn. f_equal. lia.
Qed.

Lemma vbf_le_value_nonneg (l: list Z) : bytes_ok l -> 0 <= le_value l.
Proof. unfold bytes_ok. intros H. induction H as [|x l Hx _ IH]; cbn [le_value]; [lia|]. unfold is_byte in Hx. lia. Qed.

Lemma vbf_bytes_skipn (l: list Z) (n: nat) : bytes_ok l -> bytes_ok (skipn n l).
Proof. revert l. induction n as [|n IH]; intros [|x l] H; simpl; auto. inversion H; auto. Qed.

Lemma vbf_bytes_firstn (l: list Z) (n: nat) : bytes_ok l -> bytes_ok (firstn n l).
Proof. revert l. induction n as [|n IH]; intros [|x l] H; simpl; try apply Forall_nil. inversion H; subst. constructor; [assumption|apply IH; assumption]. Qed.

Lemma vbf_le_field_nonneg (l: list Z) (p k: Z) : bytes_ok l -> 0 <= le_field l p k.
Proof. intros H. apply vbf_le_value_nonneg. unfold slice. apply vbf_bytes_firstn, vbf_bytes_skipn, H. Qed.

Lemma vbf_byte_at_range (l: list Z) (p: Z) : bytes_ok l -> 0 <= byte_at l p < 256.
Proof.
  intros H. unfold byte_at. destruct (Nat.lt_ge_cases (Z.to_nat p) (length l)) as [Hl|Hl].
  - eapply Forall_forall in H; [exact H|]. apply nth_In, Hl.
  - rewrite nth_overflow by exact Hl. lia.
Qed.

(* running steps that keep an invariant P over exactly-asked, nonempty pieces *)
Lemma vbf_run_inv (dm: dict_model) (fb: list Z) (P: Z -> blst -> Prop) :
  (forall i b, P i b -> bs_expect b <> 0 -> 0 <= i /\ 0 < bs_expect b /\
     forall b' out, bl_step md_dflt dm b (slice fb i (bs_expect b)) = BLOk b' out -> P (i + bs_expect b) b') ->
  forall pieces i0 b0 b rest, P i0 b0 -> 0 <= i0 -> bl_run md_dflt dm b0 pieces = Some b ->
    Forall (fun c => c <> []) pieces -> skipn (Z.to_nat i0) fb = concat pieces ++ rest ->
    P (i0 + Zlength (concat pieces)) b.
Proof.
  intros HP pieces. induction pieces as [|c cs IH]; intros i0 b0 b rest H0 Hi0 Hr Hne Hs.
  - simpl in Hr. inversion Hr; subst. simpl. rewrite Z.add_0_r. exact H0.
  - simpl in Hr. inversion Hne as [|? ? Hc Hcs]; subst.
    destruct (Zlength c =? bs_expect b0) eqn:Ee; [|discriminate]. apply Z.eqb_eq in Ee. simpl in Hr.
    assert (Hz: bs_expect b0 <> 0).
    { destruct c as [|x c]; [congruence|]. rewrite Zlength_correct in Ee. simpl length in Ee. lia. }
    destruct (HP _ _ H0 Hz) as (_ & Hpos & Hst).
    simpl in Hs. rewrite <- app_assoc in Hs.
    assert (Hsl: slice fb i0 (bs_expect b0) = c).
    { unfold slice. rewrite Hs, <- Ee, Zlength_correct, Nat2Z.id, firstn_app, firstn_all, Nat.sub_diag.
      simpl. apply app_nil_r. }
    destruct (bl_step md_dflt dm b0 c) as [b1 o| |] eqn:Estep; try discriminate.
    rewrite <- Hsl in Estep. specialize (Hst _ _ Estep).
    simpl. assert (Hl: Zlength (c ++ concat cs) = Zlength c + Zlength (concat cs))
      by (rewrite !Zlength_correct, length_app; lia).
    rewrite Hl, Z.add_assoc, Ee. apply (IH _ b1 b rest Hst); auto; try lia.
    rewrite <- vbf_skipn_skipn by lia. rewrite Hs, <- Ee, Zlength_correct, Nat2Z.id, skipn_app, skipn_all,
      Nat.sub_diag. reflexivity.
Qed.

(* the header ZSTD_getFrameHeader reads from the header's bytes alone *)
Lemma vbf_gfh_firstn (s: list Z) (m: Z) :
  le_field s 0 4 = ZSTD_MAGICNUMBER -> 0 <= byte_at s 4 < 256 ->
  fhd_header_size (byte_at s 4) <= m <= Zlength s ->
  get_frame_header (firstn (Z.to_nat m) s) = get_frame_header s.
Proof.
  intros Hmag Hb Hm.
  pose proof (sl_fhd_bits _ Hb) as (Hd & Hsg & Hfc).
  pose proof (sl_fhd_header_size_ge6 _ Hb) as H6.
  set (s' := firstn (Z.to_nat m) s).
  assert (Hz : Zlength s' = m) by (apply vbf_firstn_len; lia).
  assert (E0 : le_field s' 0 4 = le_field s 0 4) by (apply vbf_le_field_firstn; lia).
  assert (E4 : byte_at s' 4 = byte_at s 4) by (apply vbf_byte_at_firstn; lia).
  assert (E5 : byte_at s' 5 = byte_at s 5) by (apply vbf_byte_at_firstn; lia).
  unfold get_frame_header. rewrite Hz, E0, E4, E5, Hmag.
  assert (m <? 5 = false) as -> by (apply Z.ltb_ge; lia).
  assert (Zlength s <? 5 = false) as -> by (apply Z.ltb_ge; lia).
  change (negb (ZSTD_MAGICNUMBER =? ZSTD_MAGICNUMBER)) with false. cbv iota zeta beta.
  set (fhd := byte_at s 4) in *.
  assert (m <? fhd_header_size fhd = false) as -> by (apply Z.ltb_ge; lia).
  assert (Zlength s <? fhd_header_size fhd = false) as -> by (apply Z.ltb_ge; lia).
  assert (Hm' : fhd_header_size fhd <= m) by lia. clear Hm.
  unfold fhd_header_size in Hm'.
  destruct Hd as [Hd | [Hd | [Hd | Hd]]], Hsg as [Hsg | Hsg], Hfc as [Hfc | [Hfc | [Hfc | Hfc]]];
    cbv zeta in Hm'; rewrite ?Hd, ?Hsg, ?Hfc in Hm' |- *; simpl in Hm';
    cbn -[le_field byte_at Zlength Z.pow]; cbv [Pos.to_nat Pos.iter_op Nat.add]; unfold s';
    repeat (rewrite vbf_le_field_firstn by lia);
    repeat (rewrite vbf_byte_at_firstn by lia);
    reflexivity.
Qed.

Lemma vbf_skipn_len' (l: list Z) (i: Z) : 0 <= i -> Zlength (skipn (Z.to_nat i) l) = Z.max 0 (Zlength l - i).
Proof. intros H. rewrite !Zlength_correct, length_skipn. lia. Qed.

Lemma vbf_gfh_hs (s: list Z) (h: frame_header) :
  le_field s 0 4 = ZSTD_MAGICNUMBER -> 5 <= Zlength s -> get_frame_header s = FH_ok h ->
  fh_headerSize h = fhd_header_size (byte_at s 4) /\ fh_frameType h = 0.
Proof.
  intros Hm H5 H. unfold get_frame_header in H. rewrite Hm in H.
  assert (Zlength s <? 5 = false) as E by (apply Z.ltb_ge; lia). rewrite E in H.
  change (negb (ZSTD_MAGICNUMBER =? ZSTD_MAGICNUMBER)) with false in H. cbv zeta iota beta in H.
  repeat match type of H with
  | context [if ?c then _ else _] => destruct c
  end; try discriminate; inversion H; subst; simpl; auto.
Qed.

(* the facts of a Zstandard frame fb that decodes alone to C, taking n bytes *)
Definition vbf_zfacts (dm: dict_model) (fb C: list Z) (n: Z) (h: frame_header) (k: Z) : Prop :=
  bytes_ok fb /\ Zlength fb = n /\ le_field fb 0 4 = ZSTD_MAGICNUMBER /\ get_frame_header fb = FH_ok h /\
  fh_headerSize h = fhd_header_size (byte_at fb 4) /\ fh_blockSizeMax h <= ZSTD_BLOCKSIZE_MAX /\
  (negb (fh_dictID h =? 0) && negb (fh_dictID h =? dm_id dm)) = false /\
  decode_blocks (length (skipn (Z.to_nat (fh_headerSize h)) fb)) (dm_state dm) (dm_content dm)
     (skipn (Z.to_nat (fh_headerSize h)) fb) nil (fh_blockSizeMax h) (fh_windowSize h) = Some (C, k) /\
  (negb (fh_contentSize h =? ZSTD_CONTENTSIZE_UNKNOWN) && negb (Zlength C =? fh_contentSize h)) = false /\
  (if fh_checksumFlag h =? 1
   then n = fh_headerSize h + k + 4 /\
        le_field fb (fh_headerSize h + k) 4 = Zstd.proof.model.Xxh64.xxh64 C 0 mod 2 ^ 32
   else n = fh_headerSize h + k).

Lemma vbf_zfacts_of (dm: dict_model) (wl: Z) (fb C: list Z) (n: Z) :
  bytes_ok fb -> Zlength fb = n -> decode_frame dm wl fb = FOk C n -> exists h k, vbf_zfacts dm fb C n h k.
Proof.
  intros Hb Hl H. unfold decode_frame in H.
  destruct (Zlength fb <? ZSTD_FRAMEHEADERSIZE_MIN + ZSTD_blockHeaderSize) eqn:E1; [discriminate|].
  destruct (negb (le_field fb 0 4 =? ZSTD_MAGICNUMBER)) eqn:E2; [discriminate|].
  apply Z.ltb_ge in E1. apply Bool.negb_false_iff, Z.eqb_eq in E2.
  cbv zeta in H.
  destruct (Zlength fb <? fhd_header_size (byte_at fb 4) + ZSTD_blockHeaderSize) eqn:E3; [discriminate|].
  destruct (negb (Z.land (byte_at fb 4) 8 =? 0)); [discriminate|].
  match type of H with (if ?c then _ else _) = _ => destruct c end; [discriminate|].
  destruct (get_frame_header fb) as [| |h] eqn:Eg; try discriminate.
  destruct (fh_windowSize h >? wl); [discriminate|].
  destruct (negb (fh_frameType h =? 0)); [discriminate|].
  destruct (negb (fh_dictID h =? 0) && negb (fh_dictID h =? dm_id dm)) eqn:Ed; [discriminate|].
  destruct (decode_blocks _ _ _ _ _ _ _) as [[o k]|] eqn:Edb; [|discriminate].
  destruct (negb (fh_contentSize h =? ZSTD_CONTENTSIZE_UNKNOWN) && negb (Zlength o =? fh_contentSize h)) eqn:Ef;
    [discriminate|].
  pose proof (vbf_gfh_hs fb h E2 ltac:(unfold ZSTD_FRAMEHEADERSIZE_MIN, ZSTD_blockHeaderSize in E1; lia) Eg)
    as [Hhs _].
  exists h, k.
  destruct (fh_checksumFlag h =? 1) eqn:Ec.
  - destruct (Zlength fb - fh_headerSize h - k <? 4); [discriminate|].
    destruct (negb (le_field fb (fh_headerSize h + k) 4 =? _)) eqn:Ex; [discriminate|].
    inversion H; subst. apply Bool.negb_false_iff, Z.eqb_eq in Ex.
    repeat split; auto. apply (pd_fh_bmax _ _ Eg). rewrite Ec. auto.
  - inversion H; subst. repeat split; auto. apply (pd_fh_bmax _ _ Eg). rewrite Ec. auto.
Qed.

(* ---------- blocks ---------- *)

Lemma vbf_gtb_false (a b: Z) : (a >? b) = false -> a <= b.
Proof. rewrite Z.gtb_ltb. intros H. apply Z.ltb_ge in H. exact H. Qed.

Lemma vbf_db_ext (fuel: nat) : forall ds hist s out bsm wsz o k,
  decode_blocks fuel ds hist s out bsm wsz = Some (o, k) -> exists suf, o = out ++ suf.
Proof.
  induction fuel as [|fuel IH]; intros ds hist s out bsm wsz o k H; [discriminate|].
  cbn [decode_blocks] in H.
  destruct (cblock_size s) as [c|]; [|discriminate].
  destruct (c >? Zlength s - ZSTD_blockHeaderSize); [discriminate|].
  match type of H with context [match ?r with Some _ => _ | None => None end] =>
    lazymatch r with decode_blocks _ _ _ _ _ _ _ => fail | _ => destruct r as [[st' o']|] eqn:Er end end;
    [|discriminate].
  assert (Ho': exists suf, o' = out ++ suf).
  { repeat match type of Er with
    | context [if ?c then _ else _] => destruct c
    | context [match ?x with Some _ => _ | None => _ end] => destruct x as [[? ?]|]
    end; try discriminate; inversion Er; subst; eexists; reflexivity. }
  destruct Ho' as [suf Hs]. subst o'.
  destruct (bp_last (block_props_of s) =? 1).
  - inversion H; subst. eexists; reflexivity.
  - destruct (decode_blocks fuel _ _ _ _ _ _) as [[o2 k2]|] eqn:Ed; [|discriminate]. inversion H; subst.
    destruct (IH _ _ _ _ _ _ _ _ Ed) as [suf2 ->]. exists (suf ++ suf2). apply app_assoc_reverse.
Qed.

Lemma vbf_decode_block_nil (ds: dstate) (hist out: list Z) (bsm wsz: Z) : decode_block ds hist out [] bsm wsz = None.
Proof. unfold decode_block. destruct (Zlength [] >? bsm); reflexivity. Qed.

Lemma vbf_decode_block_len (ds ds': dstate) (hist out body content: list Z) (bsm wsz: Z) :
  decode_block ds hist out body bsm wsz = Some (ds', content) -> Zlength content <= bsm.
Proof.
  unfold decode_block. intros H.
  repeat match type of H with
  | context [if ?c then _ else _] => destruct c eqn:?
  | context [match ?x with Some _ => _ | None => _ end] => destruct x as [[[? ?] ?]|]
  | context [match ?x with Some _ => _ | None => _ end] => destruct x as [[? ?]|]
  | context [match ?x with Some _ => _ | None => _ end] => destruct x
  | context [match ?x with Some _ => _ | None => _ end] => destruct x as [[[? ?] ?]|]
  | context [match ?x with (_, _) => _ end] => destruct x
  end; try discriminate.
  all: inversion H; subst; lia.
Qed.

(* the content of a block body, as bl_step computes it from the block type and RLE size *)
Definition vbf_blk (ty rle: Z) (ds: dstate) (hist out body: list Z) (bsm wsz: Z) : option (dstate * list Z) :=
  if ty =? 0 then Some (ds, body) else if ty =? 1 then Some (ds, repeat (byte_at body 0) (Z.to_nat rle))
  else if ty =? 2 then decode_block ds hist out body bsm wsz else None.

Lemma vbf_step_blk (md: dmode) (dm: dict_model) (b: blst) (c: list Z) (ds': dstate) (content: list Z) :
  (bs_stage b = BBlk \/ bs_stage b = BLastBlk) ->
  vbf_blk (bs_btype b) (bs_rle b) (bs_ds b) (dm_content dm) (bs_out b) c (fh_blockSizeMax (bs_hdr b))
    (fh_windowSize (bs_hdr b)) = Some (ds', content) ->
  bl_step md dm b c = bl_block_done b ds' content.
Proof.
  intros Hst H. unfold bl_step. unfold vbf_blk in H.
  destruct Hst as [E|E]; rewrite E;
  (destruct (bs_btype b =? 0); [inversion H; reflexivity|]);
  (destruct (bs_btype b =? 1); [inversion H; reflexivity|]);
  (destruct (bs_btype b =? 2); [rewrite H; reflexivity|discriminate]).
Qed.

Lemma vbf_db_step (fuel: nat) (ds: dstate) (hist s out: list Z) (bsm wsz: Z) (C: list Z) (k' cs: Z) :
  bytes_ok s -> decode_blocks (S fuel) ds hist s out bsm wsz = Some (C, k') -> cblock_size s = Some cs ->
  0 <= cs /\ cs <= Zlength s - 3 /\ cs <= bsm /\ (cs = 0 -> bp_type (block_props_of s) = 0) /\
  exists ds' content,
    vbf_blk (bp_type (block_props_of s)) (bp_origSize (block_props_of s)) ds hist out (slice s 3 cs) bsm wsz
      = Some (ds', content) /\
    Zlength content <= bsm /\
    (if bp_last (block_props_of s) =? 1 then C = out ++ content /\ k' = 3 + cs
     else exists k'', decode_blocks fuel ds' hist (skipn (Z.to_nat (3 + cs)) s) (out ++ content) bsm wsz
                        = Some (C, k'') /\ k' = 3 + cs + k'').
Proof.
  intros Hb H Hcs. cbn [decode_blocks] in H. rewrite Hcs in H.
  destruct (cs >? Zlength s - ZSTD_blockHeaderSize) eqn:E1; [discriminate|].
  apply vbf_gtb_false in E1. unfold ZSTD_blockHeaderSize in E1.
  set (bp := block_props_of s) in *.
  assert (Hnn: 0 <= bp_origSize bp).
  { unfold bp, block_props_of. simpl. apply Z.shiftr_nonneg. apply vbf_le_field_nonneg, Hb. }
  assert (Hcs0: 0 <= cs).
  { unfold cblock_size in Hcs. fold bp in Hcs.
    destruct (Zlength s <? ZSTD_blockHeaderSize); [discriminate|].
    destruct (bp_type bp =? 1); [injection Hcs as <-; lia|].
    destruct (bp_type bp =? 3); [discriminate|]. injection Hcs as <-; exact Hnn. }
  assert (Hbody: Zlength (slice s 3 cs) = cs).
  { unfold slice. rewrite Zlength_correct, length_firstn, length_skipn.
    rewrite Zlength_correct in E1. lia. }
  assert (Htype1: bp_type bp = 1 -> cs = 1).
  { intros T. unfold cblock_size in Hcs. fold bp in Hcs. rewrite T in Hcs.
    destruct (Zlength s <? ZSTD_blockHeaderSize); [discriminate|]. injection Hcs as <-; auto. }
  match type of H with context [match ?r with Some _ => _ | None => None end] =>
    lazymatch r with decode_blocks _ _ _ _ _ _ _ => fail | _ => destruct r as [[st' o']|] eqn:Er end end;
    [|discriminate].
  assert (Hres: cs <= bsm /\ (cs = 0 -> bp_type bp = 0) /\ exists content,
            vbf_blk (bp_type bp) (bp_origSize bp) ds hist out (slice s 3 cs) bsm wsz = Some (st', content) /\
            Zlength content <= bsm /\ o' = out ++ content).
  { unfold vbf_blk.
    destruct (bp_type bp =? 0) eqn:T0.
    - destruct (cs >? bsm) eqn:E2; [discriminate|]. apply vbf_gtb_false in E2. inversion Er; subst.
      split; [lia|]. split; [intros _; apply Z.eqb_eq; exact T0|].
      eexists; split; [reflexivity|]. split; [lia|reflexivity].
    - destruct (bp_type bp =? 1) eqn:T1.
      + destruct ((bp_origSize bp >? bsm) || (cs >? bsm)) eqn:E2; [discriminate|].
        apply Bool.orb_false_iff in E2. destruct E2 as [E2 E3]. apply vbf_gtb_false in E2, E3.
        inversion Er; subst. split; [lia|]. split.
        { intros ->. apply Z.eqb_eq in T1. specialize (Htype1 T1). lia. }
        eexists; split; [reflexivity|]. split; [|reflexivity].
        rewrite Zlength_correct, repeat_length. lia.
      + destruct (decode_block ds hist out (slice s ZSTD_blockHeaderSize cs) bsm wsz) as [[ds2 content]|] eqn:Edb;
          [|discriminate].
        change ZSTD_blockHeaderSize with 3 in Edb. inversion Er; subst.
        assert (Hcne: cs <> 0).
        { intros ->. unfold slice in Edb. simpl in Edb. rewrite vbf_decode_block_nil in Edb. discriminate. }
        assert (Hle: cs <= bsm).
        { unfold decode_block in Edb. rewrite Hbody in Edb. destruct (cs >? bsm) eqn:E3; [discriminate|].
          apply vbf_gtb_false in E3. exact E3. }
        split; [exact Hle|]. split; [intros; lia|].
        assert (Hty: bp_type bp = 2).
        { assert (Z.land (Z.shiftr (le_field s 0 3) 1) 3 = Z.shiftr (le_field s 0 3) 1 mod 4) as Em
            by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; reflexivity).
          pose proof (Z.mod_pos_bound (Z.shiftr (le_field s 0 3) 1) 4 ltac:(lia)).
          change (bp_type bp) with (Z.land (Z.shiftr (le_field s 0 3) 1) 3) in T0, T1 |- *.
          unfold cblock_size in Hcs. fold bp in Hcs.
          change (bp_type bp) with (Z.land (Z.shiftr (le_field s 0 3) 1) 3) in Hcs.
          destruct (Zlength s <? ZSTD_blockHeaderSize); [discriminate|].
          rewrite T1 in Hcs. destruct (Z.land (Z.shiftr (le_field s 0 3) 1) 3 =? 3) eqn:T3; [discriminate|].
          apply Z.eqb_neq in T0, T1, T3. lia. }
        rewrite Hty. cbn. exists content. split; [exact Edb|]. split; [|reflexivity].
        apply (vbf_decode_block_len _ _ _ _ _ _ _ _ Edb). }
  destruct Hres as (Hle & H0 & content & Hv & Hcl & ->).
  split; [lia|]. split; [lia|]. split; [exact Hle|]. split; [exact H0|].
  exists st', content. split; [exact Hv|]. split; [exact Hcl|].
  destruct (bp_last bp =? 1).
  - inversion H; subst. unfold ZSTD_blockHeaderSize. auto.
  - destruct (decode_blocks fuel _ _ _ _ _ _) as [[o2 k2]|] eqn:Ed; [|discriminate]. inversion H; subst.
    exists k2. unfold ZSTD_blockHeaderSize in Ed |- *. auto.
Qed.

Lemma vbf_hdr3 (s: list Z) : 3 <= Zlength s ->
  block_props_of (firstn 3 s) = block_props_of s /\ cblock_size (firstn 3 s) = cblock_size s.
Proof.
  intros H.
  assert (E: block_props_of (firstn 3 s) = block_props_of s).
  { unfold block_props_of. change (firstn 3 s) with (firstn (Z.to_nat 3) s).
    rewrite vbf_le_field_firstn by lia. reflexivity. }
  split; [exact E|]. unfold cblock_size. rewrite E.
  change (firstn 3 s) with (firstn (Z.to_nat 3) s). rewrite vbf_firstn_len by lia.
  destruct (Zlength s <? ZSTD_blockHeaderSize) eqn:E1; [apply Z.ltb_lt in E1; unfold ZSTD_blockHeaderSize in E1; lia|].
  reflexivity.
Qed.

Lemma vbf_firstn_add (l: list Z) (a b: nat) : firstn (a + b) l = firstn a l ++ firstn b (skipn a l).
Proof.
  revert l. induction a as [|a IH]; intros l; [reflexivity|].
  destruct l as [|x l]; simpl; [destruct b; reflexivity|]. f_equal. apply IH.
Qed.

Lemma vbf_db_len3 (fuel: nat) (ds: dstate) (hist s out: list Z) (bsm wsz: Z) (r: list Z * Z) :
  decode_blocks fuel ds hist s out bsm wsz = Some r -> 3 <= Zlength s.
Proof.
  intros H. destruct fuel as [|fuel]; [discriminate|]. cbn [decode_blocks] in H.
  unfold cblock_size in H. destruct (Zlength s <? ZSTD_blockHeaderSize) eqn:E; [discriminate|].
  apply Z.ltb_ge in E. exact E.
Qed.

Lemma vbf_db_k (fuel: nat) : forall ds hist s out bsm wsz o k, bytes_ok s ->
  decode_blocks fuel ds hist s out bsm wsz = Some (o, k) -> 3 <= k <= Zlength s.
Proof.
  induction fuel as [|fuel IH]; intros ds hist s out bsm wsz o k Hb H; [discriminate|].
  pose proof (vbf_db_len3 _ _ _ _ _ _ _ _ H) as H3.
  destruct (cblock_size s) as [cs|] eqn:Ecs.
  2:{ cbn [decode_blocks] in H. rewrite Ecs in H. discriminate. }
  destruct (vbf_db_step fuel ds hist s out bsm wsz o k cs Hb H Ecs) as (Hc0 & Hcl & _ & _ & ds' & content & _ & _ & Hk).
  destruct (bp_last (block_props_of s) =? 1).
  - destruct Hk as [_ ->]. lia.
  - destruct Hk as (k'' & Hd & ->).
    pose proof (IH _ _ _ _ _ _ _ _ (vbf_bytes_skipn _ _ Hb) Hd) as Hk''.
    rewrite vbf_skipn_len' in Hk'' by lia. lia.
Qed.

(* ---------- a Zstandard frame: the states the buffer-less steps reach ---------- *)

Definition vbf_zinv (dm: dict_model) (fb C: list Z) (n: Z) (h: frame_header) (k: Z) (i: Z) (b: blst) : Prop :=
  (i = 0 /\ b = bl_init md_dflt dm) \/
  (i = 5 /\ bs_stage b = BHdrRest /\ bs_expect b = fh_headerSize h - 5 /\ bs_hbuf b = firstn 5 fb /\
   bs_out b = [] /\ bs_ds b = dm_state dm) \/
  (exists fuel k', bs_stage b = BBlkHdr /\ bs_expect b = 3 /\ bs_hdr b = h /\ fh_headerSize h <= i /\
     i + k' = fh_headerSize h + k /\
     decode_blocks fuel (bs_ds b) (dm_content dm) (skipn (Z.to_nat i) fb) (bs_out b) (fh_blockSizeMax h)
       (fh_windowSize h) = Some (C, k')) \/
  (exists fuel k', bs_hdr b = h /\ fh_headerSize h + 3 <= i /\ i - 3 + k' = fh_headerSize h + k /\
     cblock_size (skipn (Z.to_nat (i - 3)) fb) = Some (bs_expect b) /\ 0 < bs_expect b /\
     bs_btype b = bp_type (block_props_of (skipn (Z.to_nat (i - 3)) fb)) /\
     bs_rle b = bp_origSize (block_props_of (skipn (Z.to_nat (i - 3)) fb)) /\
     bs_stage b = (if bp_last (block_props_of (skipn (Z.to_nat (i - 3)) fb)) =? 1 then BLastBlk else BBlk) /\
     decode_blocks (S fuel) (bs_ds b) (dm_content dm) (skipn (Z.to_nat (i - 3)) fb) (bs_out b)
       (fh_blockSizeMax h) (fh_windowSize h) = Some (C, k')) \/
  (fh_checksumFlag h = 1 /\ i = fh_headerSize h + k /\ bs_stage b = BCk /\ bs_expect b = 4 /\ bs_out b = C /\
   bs_hdr b = h) \/
  (i = n /\ bs_expect b = 0 /\ bs_out b = C).

Lemma vbf_zend (dm: dict_model) (fb C: list Z) (n: Z) (h: frame_header) (k i: Z) (b0 b1: blst) (stg: blstage) (e: Z) :
  vbf_zfacts dm fb C n h k -> bs_hdr b0 = h -> bs_out b1 = C -> bs_hdr b1 = h -> i = fh_headerSize h + k ->
  bl_frame_end b0 = (stg, e) -> vbf_zinv dm fb C n h k i (bl_set b1 stg e).
Proof.
  intros (Hb & Hl & Hmag & Hg & Hhs & Hbm & Hdid & Hdb & Hfcs & Hck) H0 H1 H1h Hi He.
  unfold bl_frame_end in He. rewrite H0 in He. unfold vbf_zinv.
  destruct (fh_checksumFlag h =? 1) eqn:Ec; injection He as <- <-.
  - do 4 right. left. apply Z.eqb_eq in Ec. cbn. repeat split; auto.
  - do 5 right. cbn. repeat split; auto; lia.
Qed.

Lemma vbf_zstep (dm: dict_model) (fb C: list Z) (n: Z) (h: frame_header) (k i: Z) (b: blst) :
  vbf_zfacts dm fb C n h k -> vbf_zinv dm fb C n h k i b -> bs_expect b <> 0 ->
  0 <= i /\ 0 < bs_expect b /\ i + bs_expect b <= n /\
  exists b' out, bl_step md_dflt dm b (slice fb i (bs_expect b)) = BLOk b' out /\
                 vbf_zinv dm fb C n h k (i + bs_expect b) b'.
Proof.
  intros Hz Hinv Hne. pose proof Hz as (Hb & Hl & Hmag & Hg & Hhs & Hbm & Hdid & Hdb & Hfcs & Hck).
  pose proof (vbf_byte_at_range fb 4 Hb) as Hb4. pose proof (sl_fhd_header_size_ge6 _ Hb4) as H6.
  rewrite <- Hhs in H6.
  pose proof (vbf_db_len3 _ _ _ _ _ _ _ _ Hdb) as Hhs3. rewrite vbf_skipn_len' in Hhs3 by lia.
  pose proof (vbf_db_k _ _ _ _ _ _ _ _ _ (vbf_bytes_skipn _ _ Hb) Hdb) as Hk.
  rewrite vbf_skipn_len' in Hk by lia.
  unfold vbf_zinv in Hinv.
  destruct Hinv as [(-> & ->) | [(-> & Hst & He & Hhb & Ho & Hds) | [(fuel & k' & Hst & He & Hh & Hi & Hik & Hd) |
                   [(fuel & k' & Hh & Hi & Hik & Hcs & Hpos & Hty & Hrle & Hst & Hd) |
                   [(Hc & -> & Hst & He & Ho & Hh) | (-> & He & Ho)]]]]].
  - (* the first 5 bytes *)
    cbn [bl_init bs_expect md_magicless md_dflt starting_len]. unfold ZSTD_FRAMEHEADERSIZE_PREFIX.
    split; [lia|]. split; [lia|]. split; [lia|].
    assert (Hc5: slice fb 0 5 = firstn (Z.to_nat 5) fb) by reflexivity.
    assert (Hm5: le_field (slice fb 0 5) 0 4 = ZSTD_MAGICNUMBER) by (rewrite Hc5, vbf_le_field_firstn by lia; exact Hmag).
    eexists _, nil. split.
    + unfold bl_step. cbn [bl_init bs_stage md_magicless md_dflt negb]. rewrite Hm5. reflexivity.
    + unfold vbf_zinv. right. left. cbn [bs_stage bs_expect bs_hbuf bs_out bs_ds bl_init md_magicless md_dflt].
      unfold header_size_m. rewrite Hc5, vbf_byte_at_firstn, vbf_firstn_len by lia. rewrite Hhs.
      repeat split; reflexivity.
  - (* the rest of the header *)
    rewrite He. split; [lia|]. split; [lia|]. split; [lia|].
    assert (Hcat: bs_hbuf b ++ slice fb 5 (fh_headerSize h - 5) = firstn (Z.to_nat (fh_headerSize h)) fb).
    { rewrite Hhb. unfold slice. replace (Z.to_nat (fh_headerSize h)) with (5 + Z.to_nat (fh_headerSize h - 5))%nat
        by lia. rewrite vbf_firstn_add. reflexivity. }
    assert (Hg': get_frame_header (firstn (Z.to_nat (fh_headerSize h)) fb) = FH_ok h)
      by (rewrite vbf_gfh_firstn; auto; lia).
    eexists _, nil. split.
    + unfold bl_step. rewrite Hst. cbn [md_magicless md_dflt]. unfold get_frame_header_m. cbn [negb].
      rewrite Hcat, Hg', Hdid. reflexivity.
    + unfold vbf_zinv. do 2 right. left.
      exists (length (skipn (Z.to_nat (fh_headerSize h)) fb)), k.
      cbn [bs_stage bs_expect bs_hbuf bs_out bs_ds bs_hdr].
      replace (5 + (fh_headerSize h - 5)) with (fh_headerSize h) by lia.
      repeat split; try lia.
      * destruct h; reflexivity.
      * rewrite Ho, Hds. exact Hdb.
  - (* a block header *)
    rewrite He.
    set (s := skipn (Z.to_nat i) fb) in Hd.
    assert (Hsb: bytes_ok s) by (apply vbf_bytes_skipn, Hb).
    pose proof (vbf_db_len3 _ _ _ _ _ _ _ _ Hd) as Hs3.
    assert (Hsl: Zlength s = Z.max 0 (Zlength fb - i)) by (apply vbf_skipn_len'; lia).
    split; [lia|]. split; [lia|]. split; [lia|].
    destruct fuel as [|fuel]; [discriminate|].
    destruct (cblock_size s) as [cs|] eqn:Ecs.
    2:{ cbn [decode_blocks] in Hd. rewrite Ecs in Hd. discriminate. }
    destruct (vbf_db_step fuel _ _ _ _ _ _ _ _ cs Hsb Hd Ecs)
      as (Hc0 & Hcl & Hcb & Hc00 & ds' & content & Hv & Hcont & Hnext).
    assert (Hc3: slice fb i 3 = firstn 3 s) by reflexivity.
    destruct (vbf_hdr3 s Hs3) as [Hbp Hcbs].
    unfold bl_step. rewrite Hst, Hc3, Hcbs, Ecs, Hbp, Hh.
    assert (E1: (cs >? fh_blockSizeMax h) = false) by (rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
    rewrite E1.
    destruct (cs =? 0) eqn:Ez.
    + apply Z.eqb_eq in Ez. subst cs. specialize (Hc00 eq_refl).
      unfold vbf_blk in Hv. rewrite Hc00 in Hv. cbn in Hv. injection Hv as <- <-.
      assert (Hnil: slice s 3 0 = []) by reflexivity.
      rewrite ?Hnil, !app_nil_r in Hnext.
      destruct (bp_last (block_props_of s) =? 1) eqn:El.
      * destruct Hnext as [HC Hk'].
        destruct (bl_frame_end b) as [stg e] eqn:Efe.
        (* F6: the content size check of the empty last block passes, the frame's content being C *)
        assert (Hf6: negb (fh_contentSize h =? ZSTD_CONTENTSIZE_UNKNOWN) &&
                     negb (Zlength (bs_out b) =? fh_contentSize h) = false)
          by (first [rewrite <- HC | rewrite HC]; exact Hfcs).
        rewrite Hf6.
        eexists _, nil. split; [reflexivity|].
        apply (vbf_zend dm fb C n h k _ b); [exact Hz|exact Hh|cbn; first [reflexivity|symmetry; exact HC]|cbn; first [reflexivity|exact Hh]|lia|exact Efe].
      * destruct Hnext as (k'' & Hd'' & Hk').
        eexists _, nil. split; [reflexivity|].
        unfold vbf_zinv. do 2 right. left. exists fuel, k''. cbn [bl_set bs_stage bs_expect bs_hdr bs_ds bs_out].
        unfold ZSTD_blockHeaderSize.
        split; [reflexivity|]. split; [reflexivity|]. split; [first [reflexivity|exact Hh]|]. split; [lia|]. split; [lia|].
        replace (skipn (Z.to_nat (i + 3)) fb) with (skipn (Z.to_nat (3 + 0)) s)
          by (unfold s; rewrite vbf_skipn_skipn by lia; f_equal; f_equal; lia).
        exact Hd''.
    + apply Z.eqb_neq in Ez.
      eexists _, nil. split; [reflexivity|].
      unfold vbf_zinv. do 3 right. left. exists fuel, k'.
      cbn [bl_set bs_stage bs_expect bs_hdr bs_ds bs_out bs_btype bs_rle].
      replace (i + 3 - 3) with i by lia. fold s.
      split; [first [reflexivity|exact Hh]|]. split; [lia|]. split; [lia|]. split; [exact Ecs|]. split; [lia|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. exact Hd.
  - (* a block body *)
    set (s := skipn (Z.to_nat (i - 3)) fb) in *.
    assert (Hsb: bytes_ok s) by (apply vbf_bytes_skipn, Hb).
    set (cs := bs_expect b) in *.
    destruct (vbf_db_step fuel _ _ _ _ _ _ _ _ cs Hsb Hd Hcs)
      as (Hc0 & Hcl & Hcb & _ & ds' & content & Hv & Hcont & Hnext).
    assert (Hsl: Zlength s = Z.max 0 (Zlength fb - (i - 3))) by (apply vbf_skipn_len'; lia).
    split; [lia|]. split; [lia|]. split; [lia|].
    assert (Hc: slice fb i cs = slice s 3 cs) by (unfold s; rewrite vbf_slice_skipn by lia; f_equal; lia).
    rewrite Hc.
    assert (Hstep: bl_step md_dflt dm b (slice s 3 cs) = bl_block_done b ds' content).
    { apply vbf_step_blk.
      - rewrite Hst. destruct (bp_last (block_props_of s) =? 1); auto.
      - rewrite Hty, Hrle, Hh. exact Hv. }
    rewrite Hstep. unfold bl_block_done. rewrite Hh.
    assert ((Zlength content >? fh_blockSizeMax h) = false) as -> by (rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
    rewrite Hst. destruct (bp_last (block_props_of s) =? 1) eqn:El.
    + destruct Hnext as [HC Hk']. rewrite <- HC, Hfcs.
      destruct (bl_frame_end b) as [stg e] eqn:Efe.
      eexists _, _. split; [reflexivity|].
      apply (vbf_zend dm fb C n h k _ b); [exact Hz|exact Hh|cbn; first [reflexivity|symmetry; exact HC]|cbn; first [reflexivity|exact Hh]|lia|exact Efe].
    + destruct Hnext as (k'' & Hd'' & Hk').
      eexists _, _. split; [reflexivity|].
      unfold vbf_zinv. do 2 right. left. exists fuel, k''. cbn [bl_set bs_stage bs_expect bs_hdr bs_ds bs_out].
      unfold ZSTD_blockHeaderSize.
      split; [reflexivity|]. split; [reflexivity|]. split; [first [reflexivity|exact Hh]|]. split; [lia|]. split; [lia|].
      replace (skipn (Z.to_nat (i + cs)) fb) with (skipn (Z.to_nat (3 + cs)) s)
        by (unfold s; rewrite vbf_skipn_skipn by lia; f_equal; f_equal; lia).
      exact Hd''.
  - (* the checksum *)
    rewrite He.
    assert (Hck2: n = fh_headerSize h + k + 4 /\
                  le_field fb (fh_headerSize h + k) 4 = Zstd.proof.model.Xxh64.xxh64 C 0 mod 2 ^ 32)
      by (rewrite Hc in Hck; exact Hck).
    destruct Hck2 as [Hn Hx].
    split; [lia|]. split; [lia|]. split; [lia|].
    assert (Hlf: le_field (slice fb (fh_headerSize h + k) 4) 0 4 = le_field fb (fh_headerSize h + k) 4).
    { unfold le_field. f_equal. unfold slice at 1. change (Z.to_nat 0) with 0%nat. cbn [skipn].
      unfold slice. rewrite firstn_firstn. reflexivity. }
    eexists _, nil. split.
    + unfold bl_step. rewrite Hst, Hh, Hc, Hlf, Hx, Ho. rewrite !Z.eqb_refl. reflexivity.
    + unfold vbf_zinv. do 5 right. cbn [bl_set bs_expect bs_out]. split; [lia|]. split; [reflexivity|exact Ho].
  - lia.
Qed.

Lemma vbf_zclaims (dm: dict_model) (fb C: list Z) (n: Z) (h: frame_header) (k i: Z) (b: blst) :
  vbf_zfacts dm fb C n h k -> vbf_zinv dm fb C n h k i b ->
  (exists suf, C = bs_out b ++ suf) /\ (bs_expect b = 0 -> i = n /\ bs_out b = C).
Proof.
  intros Hz Hinv. pose proof Hz as (Hb & Hl & Hmag & Hg & Hhs & Hbm & Hdid & Hdb & Hfcs & Hck).
  pose proof (vbf_byte_at_range fb 4 Hb) as Hb4. pose proof (sl_fhd_header_size_ge6 _ Hb4) as H6.
  rewrite <- Hhs in H6.
  destruct Hinv as [(-> & ->) | [(-> & Hst & He & Hhb & Ho & Hds) | [(fuel & k' & Hst & He & Hh & Hi & Hik & Hd) |
                   [(fuel & k' & Hh & Hi & Hik & Hcs & Hpos & Hty & Hrle & Hst & Hd) |
                   [(Hc & -> & Hst & He & Ho & Hh) | (-> & He & Ho)]]]]].
  - split; [exists C; reflexivity|]. cbn. unfold ZSTD_FRAMEHEADERSIZE_PREFIX. lia.
  - rewrite Ho. split; [exists C; reflexivity|]. lia.
  - destruct (vbf_db_ext _ _ _ _ _ _ _ _ _ Hd) as [suf Hs]. split; [exists suf; exact Hs|]. lia.
  - destruct (vbf_db_ext _ _ _ _ _ _ _ _ _ Hd) as [suf Hs]. split; [exists suf; exact Hs|]. lia.
  - rewrite Ho. split; [exists []; rewrite app_nil_r; reflexivity|]. lia.
  - rewrite Ho. split; [exists []; rewrite app_nil_r; reflexivity|]. auto.
Qed.

(* ---------- a skippable frame ---------- *)

Definition vbf_sinv (dm: dict_model) (fb: list Z) (n: Z) (i: Z) (b: blst) : Prop :=
  (i = 0 /\ b = bl_init md_dflt dm) \/
  (i = 5 /\ bs_stage b = BSkipHdr /\ bs_expect b = 3 /\ bs_hbuf b = firstn 5 fb /\ bs_out b = []) \/
  (i = 8 /\ bs_stage b = BSkip /\ bs_expect b = n - 8 /\ bs_out b = []) \/
  (i = n /\ bs_expect b = 0 /\ bs_out b = []).

Lemma vbf_sstep (dm: dict_model) (fb: list Z) (n i: Z) (b: blst) :
  bytes_ok fb -> Zlength fb = n -> is_skippable_magic (le_field fb 0 4) = true -> le_field fb 4 4 + 8 = n ->
  vbf_sinv dm fb n i b -> bs_expect b <> 0 ->
  0 <= i /\ 0 < bs_expect b /\ i + bs_expect b <= n /\
  exists b', bl_step md_dflt dm b (slice fb i (bs_expect b)) = BLOk b' nil /\ vbf_sinv dm fb n (i + bs_expect b) b'.
Proof.
  intros Hb Hl Hm Hn Hinv Hne. pose proof (vbf_le_field_nonneg fb 4 4 Hb) as Hsz.
  destruct Hinv as [(-> & ->) | [(-> & Hst & He & Hhb & Ho) | [(-> & Hst & He & Ho) | (-> & He & Ho)]]].
  - cbn [bl_init bs_expect md_magicless md_dflt starting_len]. unfold ZSTD_FRAMEHEADERSIZE_PREFIX.
    split; [lia|]. split; [lia|]. split; [lia|].
    assert (Hc5: slice fb 0 5 = firstn (Z.to_nat 5) fb) by reflexivity.
    assert (Hm5: le_field (slice fb 0 5) 0 4 = le_field fb 0 4) by (rewrite Hc5, vbf_le_field_firstn by lia; reflexivity).
    eexists. split.
    + unfold bl_step. cbn [bl_init bs_stage md_magicless md_dflt negb andb]. rewrite Hm5, Hm. reflexivity.
    + unfold vbf_sinv. right. left. cbn [bs_stage bs_expect bs_hbuf bs_out bl_init].
      rewrite Hc5, vbf_firstn_len by lia. unfold ZSTD_SKIPPABLEHEADERSIZE. repeat split; reflexivity.
  - rewrite He. split; [lia|]. split; [lia|]. split; [lia|].
    assert (Hcat: bs_hbuf b ++ slice fb 5 3 = firstn (Z.to_nat 8) fb).
    { rewrite Hhb. unfold slice. change (Z.to_nat 8) with (5 + Z.to_nat 3)%nat. rewrite vbf_firstn_add. reflexivity. }
    eexists. split.
    + unfold bl_step. rewrite Hst. reflexivity.
    + unfold vbf_sinv. do 2 right. left. cbn [bs_stage bs_expect bs_hbuf bs_out].
      rewrite Hcat, vbf_le_field_firstn by lia. repeat split; auto; lia.
  - rewrite He. split; [lia|]. split; [lia|]. split; [lia|].
    eexists. split.
    + unfold bl_step. rewrite Hst. reflexivity.
    + unfold vbf_sinv. do 3 right. cbn [bl_set bs_expect bs_out]. repeat split; auto; lia.
  - lia.
Qed.

(* ---------- a frame beyond zstd's window range ---------- *)

Definition vbf_binv (dm: dict_model) (fb: list Z) (hs: Z) (i: Z) (b: blst) : Prop :=
  (i = 0 /\ b = bl_init md_dflt dm) \/
  (i = 5 /\ bs_stage b = BHdrRest /\ bs_expect b = hs - 5 /\ bs_hbuf b = firstn 5 fb /\ bs_out b = []).

Lemma vbf_bstep (dm: dict_model) (fb: list Z) (n hs i: Z) (b: blst) :
  bytes_ok fb -> Zlength fb = n -> le_field fb 0 4 = ZSTD_MAGICNUMBER -> hs = fhd_header_size (byte_at fb 4) ->
  hs + 3 <= n -> get_frame_header (firstn (Z.to_nat hs) fb) = FH_err ->
  vbf_binv dm fb hs i b -> bs_expect b <> 0 ->
  0 <= i /\ 0 < bs_expect b /\ i + bs_expect b <= n /\
  ((exists b', bl_step md_dflt dm b (slice fb i (bs_expect b)) = BLOk b' nil /\ vbf_binv dm fb hs (i + bs_expect b) b') \/
   bl_step md_dflt dm b (slice fb i (bs_expect b)) = BLErr).
Proof.
  intros Hb Hl Hmag Hhs Hn Herr Hinv Hne.
  pose proof (vbf_byte_at_range fb 4 Hb) as Hb4. pose proof (sl_fhd_header_size_ge6 _ Hb4) as H6.
  rewrite <- Hhs in H6.
  destruct Hinv as [(-> & ->) | (-> & Hst & He & Hhb & Ho)].
  - cbn [bl_init bs_expect md_magicless md_dflt starting_len]. unfold ZSTD_FRAMEHEADERSIZE_PREFIX.
    split; [lia|]. split; [lia|]. split; [lia|]. left.
    assert (Hc5: slice fb 0 5 = firstn (Z.to_nat 5) fb) by reflexivity.
    assert (Hm5: le_field (slice fb 0 5) 0 4 = ZSTD_MAGICNUMBER) by (rewrite Hc5, vbf_le_field_firstn by lia; exact Hmag).
    eexists. split.
    + unfold bl_step. cbn [bl_init bs_stage md_magicless md_dflt negb]. rewrite Hm5. reflexivity.
    + unfold vbf_binv. right. cbn [bs_stage bs_expect bs_hbuf bs_out bl_init md_magicless md_dflt].
      unfold header_size_m. rewrite Hc5, vbf_byte_at_firstn, vbf_firstn_len by lia. rewrite <- Hhs.
      repeat split; reflexivity.
  - rewrite He. split; [lia|]. split; [lia|]. split; [lia|]. right.
    assert (Hcat: bs_hbuf b ++ slice fb 5 (hs - 5) = firstn (Z.to_nat hs) fb).
    { rewrite Hhb. unfold slice. replace (Z.to_nat hs) with (5 + Z.to_nat (hs - 5))%nat by lia.
      rewrite vbf_firstn_add. reflexivity. }
    unfold bl_step. rewrite Hst. cbn [md_magicless md_dflt]. unfold get_frame_header_m. cbn [negb].
    rewrite Hcat, Herr. reflexivity.
Qed.

Lemma vbf_prefix (C out suf: list Z) : C = out ++ suf -> Zlength out <= Zlength C /\ out = slice C 0 (Zlength out).
Proof.
  intros ->. split.
  - rewrite !Zlength_correct, length_app. lia.
  - unfold slice. change (Z.to_nat 0) with 0%nat. cbn [skipn].
    rewrite Zlength_correct, Nat2Z.id, firstn_app, firstn_all, Nat.sub_diag. simpl. rewrite app_nil_r. reflexivity.
Qed.

Lemma vbf_tiles_cs (fs: list winfo) : forall off coff n cn, tiles fs off coff n cn ->
  Forall (fun f => 0 <= wi_csize f /\ (wi_skippable f = true -> wi_csize f = 0)) fs.
Proof.
  induction fs as [|f fs IH]; simpl; intros off coff n cn H; constructor.
  - tauto.
  - destruct H as (_ & _ & _ & _ & _ & H). eapply IH. exact H.
Qed.

Lemma vbf_dethdr_len (dm: dict_model) (wl: Z) (s: list Z) :
  decode_frame dm wl s = FDetHdr -> fhd_header_size (byte_at s 4) + 3 <= Zlength s.
Proof.
  intros H. unfold decode_frame in H.
  destruct (Zlength s <? ZSTD_FRAMEHEADERSIZE_MIN + ZSTD_blockHeaderSize); [discriminate|].
  destruct (negb (le_field s 0 4 =? ZSTD_MAGICNUMBER)); [discriminate|].
  cbv zeta in H.
  destruct (Zlength s <? fhd_header_size (byte_at s 4) + ZSTD_blockHeaderSize) eqn:E; [discriminate|].
  apply Z.ltb_ge in E. exact E.
Qed.

(* ---------- the frame ---------- *)

(* vbl_frame, for the states reached over nonempty pieces (zstd is never called with bs_expect = 0) *)
Lemma vbf_frame (dm: dict_model) (ws: wseries) (k: nat) (i: Z) (b: blst) (pieces: list (list Z)) :
  series_facts dm ws -> (k < length (ws_frames ws))%nat ->
  let f := nth k (ws_frames ws) winfo0 in
  0 <= i <= Zlength (wi_bytes ws f) ->
  bl_run md_dflt dm (bl_init md_dflt dm) pieces = Some b -> Forall (fun c => c <> []) pieces ->
  concat pieces = slice (wi_bytes ws f) 0 i ->
  (Zlength (bs_out b) <= wi_csize f /\ bs_out b = slice (wi_content ws f) 0 (Zlength (bs_out b))) /\
  (bs_expect b = 0 -> i = wi_size f /\ bs_out b = wi_content ws f) /\
  (bs_expect b <> 0 ->
     0 < bs_expect b /\ i + bs_expect b <= wi_size f /\
     ((exists b' out, bl_step md_dflt dm b (slice (wi_bytes ws f) i (bs_expect b)) = BLOk b' out /\
                      (wi_skippable f = true -> out = nil)) \/
      (wi_big f = true /\ bl_step md_dflt dm b (slice (wi_bytes ws f) i (bs_expect b)) = BLErr))).
Proof.
  intros Hs Hk f Hi Hr Hne Hcat.
  destruct Hs as (Hbytes & Hcont & _ & _ & _ & Htiles & Hfacts & _).
  assert (Hff: frame_facts dm ws f) by (apply Forall_nth; auto).
  pose proof (sl_tiles_bounds _ _ _ _ _ Htiles) as (_ & _ & Hbd).
  assert (Hbf: 0 <= wi_start f /\ 0 < wi_size f /\ wi_end f <= Zlength (ws_bytes ws) /\ 0 <= wi_cstart f /\
               wi_cstart f + wi_csize f <= Zlength (ws_content ws))
    by (apply (proj1 (Forall_nth _ _) Hbd); auto).
  assert (Hcf: 0 <= wi_csize f /\ (wi_skippable f = true -> wi_csize f = 0))
    by (apply (proj1 (Forall_nth _ _) (vbf_tiles_cs _ _ _ _ _ Htiles)); auto).
  destruct Hbf as (Hst0 & Hsz0 & Hend & Hcs0 & Hcend). unfold wi_end in Hend.
  destruct Hcf as (Hcsz & Hskc).
  set (fb := wi_bytes ws f) in *. set (C := wi_content ws f) in *. set (n := wi_size f) in *.
  set (s := skipn (Z.to_nat (wi_start f)) (ws_bytes ws)) in *.
  assert (Hfbs: fb = firstn (Z.to_nat n) s) by reflexivity.
  assert (Hsl: Zlength s = Zlength (ws_bytes ws) - wi_start f) by (apply vbf_skipn_len; lia).
  assert (Hl: Zlength fb = n) by (rewrite Hfbs; apply vbf_firstn_len; lia).
  assert (Hlc: Zlength C = wi_csize f).
  { unfold C, wi_content, slice. rewrite vbf_firstn_len; [reflexivity|].
    rewrite vbf_skipn_len by lia. lia. }
  assert (Hb: bytes_ok fb) by (rewrite Hfbs; apply vbf_bytes_firstn, vbf_bytes_skipn, Hbytes).
  (* the run from the frame's start *)
  assert (Hrest: skipn (Z.to_nat 0) fb = concat pieces ++ skipn (Z.to_nat i) fb).
  { rewrite Hcat. unfold slice. change (Z.to_nat 0) with 0%nat. cbn [skipn]. symmetry. apply firstn_skipn. }
  assert (Hci: Zlength (concat pieces) = i).
  { rewrite Hcat. unfold slice. change (Z.to_nat 0) with 0%nat. cbn [skipn]. apply vbf_firstn_len. lia. }
  unfold frame_facts in Hff. fold s fb in Hff.
  destruct Hff as (_ & _ & _ & Hgfh & _ & _ & _ & Hskip & Hzst).
  destruct (wi_skippable f) eqn:Esk.
  - (* skippable *)
    destruct (Hskip eq_refl) as (_ & H8 & Hm & Hsfs & _).
    specialize (Hsfs []). rewrite app_nil_r in Hsfs.
    assert (Hn8: le_field fb 4 4 + 8 = n).
    { unfold skippable_frame_size in Hsfs.
      destruct (Zlength fb <? ZSTD_SKIPPABLEHEADERSIZE); [discriminate|].
      destruct (le_field fb 4 4 + ZSTD_SKIPPABLEHEADERSIZE >? Zlength fb); [discriminate|].
      injection Hsfs as E. unfold n. unfold ZSTD_SKIPPABLEHEADERSIZE in E. lia. }
    assert (HC: C = []).
    { apply Zlength_nil_inv. rewrite Hlc. apply Hskc. reflexivity. }
    assert (HP: vbf_sinv dm fb n i b).
    { replace i with (0 + Zlength (concat pieces)) by lia.
      apply (vbf_run_inv dm fb (vbf_sinv dm fb n)) with (b0 := bl_init md_dflt dm) (rest := skipn (Z.to_nat i) fb);
        auto; try lia.
      - intros i0 b0 H0 He0. destruct (vbf_sstep dm fb n i0 b0 Hb Hl Hm Hn8 H0 He0) as (A & B & _ & b1 & E1 & P1).
        split; [exact A|]. split; [exact B|]. intros b' out E. rewrite E1 in E. injection E as <- _. exact P1.
      - left. auto. }
    assert (Hout: bs_out b = []).
    { destruct HP as [(_ & ->) | [(_ & _ & _ & _ & Ho) | [(_ & _ & _ & Ho) | (_ & _ & Ho)]]]; auto. }
    rewrite Hout, HC. split; [split; [cbn; lia|reflexivity]|]. split.
    + intros He. split; [|reflexivity].
      destruct HP as [(_ & ->) | [(_ & _ & He' & _ & _) | [(-> & _ & He' & _) | (-> & _ & _)]]]; cbn in He; unfold ZSTD_FRAMEHEADERSIZE_PREFIX in *; lia.
    + intros He. destruct (vbf_sstep dm fb n i b Hb Hl Hm Hn8 HP He) as (A & B & C' & b1 & E1 & _).
      split; [exact B|]. split; [exact C'|]. left. exists b1, nil. split; [exact E1|auto].
  - specialize (Hzst eq_refl). destruct Hzst as (Hdec & _ & _).
    destruct (wi_big f) eqn:Ebig.
    + (* beyond zstd's window range *)
      assert (Hrej: forall wl, wi_rejected wl f = true) by (intros wl; unfold wi_rejected; rewrite Esk, Ebig; reflexivity).
      pose proof (Hdec 0 []) as Hd0. rewrite Hrej, app_nil_r in Hd0.
      pose proof (sl_decode_frame_not_unk dm 0 fb ltac:(rewrite Hd0; discriminate)) as [H9 Hmag].
      pose proof (vbf_dethdr_len _ _ _ Hd0) as Hhs3.
      set (hs := fhd_header_size (byte_at fb 4)) in *.
      pose proof (vbf_byte_at_range fb 4 Hb) as Hb4. pose proof (sl_fhd_header_size_ge6 _ Hb4) as H6.
      fold hs in H6.
      assert (Herr: get_frame_header (firstn (Z.to_nat hs) fb) = FH_err).
      { rewrite Hfbs, firstn_firstn. replace (Nat.min (Z.to_nat hs) (Z.to_nat n)) with (Z.to_nat hs) by lia.
        assert (Ems: le_field s 0 4 = ZSTD_MAGICNUMBER)
          by (rewrite <- Hmag, Hfbs, vbf_le_field_firstn by lia; reflexivity).
        assert (Ebs: byte_at s 4 = byte_at fb 4) by (rewrite Hfbs, vbf_byte_at_firstn by lia; reflexivity).
        rewrite vbf_gfh_firstn; [rewrite Hgfh; reflexivity|exact Ems|rewrite Ebs; exact Hb4|].
        rewrite Ebs. fold hs. lia. }
      assert (HP: vbf_binv dm fb hs i b).
      { replace i with (0 + Zlength (concat pieces)) by lia.
        apply (vbf_run_inv dm fb (vbf_binv dm fb hs)) with (b0 := bl_init md_dflt dm) (rest := skipn (Z.to_nat i) fb);
          auto; try lia.
        - intros i0 b0 H0 He0.
          destruct (vbf_bstep dm fb n hs i0 b0 Hb Hl Hmag eq_refl ltac:(lia) Herr H0 He0) as (A & B & _ & D).
          split; [exact A|]. split; [exact B|]. intros b' out E.
          destruct D as [(b1 & E1 & P1) | E1]; rewrite E1 in E; [injection E as <- _; exact P1|discriminate].
        - left. auto. }
      assert (Hout: bs_out b = []) by (destruct HP as [(_ & ->) | (_ & _ & _ & _ & Ho)]; auto).
      rewrite Hout. split.
      { split; [cbn; lia|]. reflexivity. }
      split.
      * intros He. exfalso.
        destruct HP as [(_ & ->) | (_ & _ & He' & _ & _)]; cbn in He; unfold ZSTD_FRAMEHEADERSIZE_PREFIX in He; lia.
      * intros He. destruct (vbf_bstep dm fb n hs i b Hb Hl Hmag eq_refl ltac:(lia) Herr HP He) as (A & B & C' & D).
        split; [exact B|]. split; [exact C'|].
        destruct D as [(b1 & E1 & _) | E1]; [left; exists b1, nil; split; [exact E1|discriminate]|right; auto].
    + (* a Zstandard frame zstd decodes *)
      pose proof (Hdec (wi_window f) []) as Hd0.
      assert (Hrej: wi_rejected (wi_window f) f = false)
        by (unfold wi_rejected; rewrite Esk, Ebig, Z.gtb_ltb, Z.ltb_irrefl; reflexivity).
      rewrite Hrej, app_nil_r in Hd0. fold C n in Hd0.
      destruct (vbf_zfacts_of dm _ fb C n Hb Hl Hd0) as (h & kk & Hz).
      assert (HP: vbf_zinv dm fb C n h kk i b).
      { replace i with (0 + Zlength (concat pieces)) by lia.
        apply (vbf_run_inv dm fb (vbf_zinv dm fb C n h kk)) with (b0 := bl_init md_dflt dm)
          (rest := skipn (Z.to_nat i) fb); auto; try lia.
        - intros i0 b0 H0 He0. destruct (vbf_zstep dm fb C n h kk i0 b0 Hz H0 He0) as (A & B & _ & b1 & o1 & E1 & P1).
          split; [exact A|]. split; [exact B|]. intros b' out E. rewrite E1 in E. injection E as <- _. exact P1.
        - left. auto. }
      destruct (vbf_zclaims dm fb C n h kk i b Hz HP) as [(suf & Hsuf) Hzend].
      split; [rewrite <- Hlc; apply (vbf_prefix C _ suf Hsuf)|]. split; [exact Hzend|].
      intros He. destruct (vbf_zstep dm fb C n h kk i b Hz HP He) as (A & B & C' & b1 & o1 & E1 & _).
      split; [exact B|]. split; [exact C'|]. left. exists b1, o1. split; [exact E1|discriminate].
Qed.

(* END helpers *)

(* THE MODEL FACT: in a reached state of a written frame, what has been delivered is the start of the frame's
   content; zstd asks for nothing more (bs_expect = 0) exactly at the frame's end, with all of its content
   delivered; otherwise it asks for bytes within the frame, and the step on them succeeds (delivering nothing
   in a skippable frame), or fails at the header of a frame beyond zstd's window range *)
Lemma vbl_frame (dm: dict_model) (ws: wseries) (k: nat) (i: Z) (b: blst) :
  series_facts dm ws -> wseries_wf ws -> (k < length (ws_frames ws))%nat ->
  let f := nth k (ws_frames ws) winfo0 in
  vbl_reach dm (wi_bytes ws f) i b ->
  (Zlength (bs_out b) <= wi_csize f /\ bs_out b = slice (wi_content ws f) 0 (Zlength (bs_out b))) /\
  (bs_expect b = 0 -> i = wi_size f /\ bs_out b = wi_content ws f) /\
  (bs_expect b <> 0 ->
     0 < bs_expect b /\ i + bs_expect b <= wi_size f /\
     ((exists b' out, bl_step md_dflt dm b (slice (wi_bytes ws f) i (bs_expect b)) = BLOk b' out /\
                      (wi_skippable f = true -> out = nil)) \/
      (wi_big f = true /\ bl_step md_dflt dm b (slice (wi_bytes ws f) i (bs_expect b)) = BLErr))).
Proof.
  intros Hs Hw Hk f (Hi & pieces & Hr & Hcat & Hne).
  exact (vbf_frame dm ws k i b pieces Hs Hk Hi Hr Hne Hcat).
Qed.

(* what a reached state has delivered is the start of the frame's content *)
Lemma vbl_reach_out (dm: dict_model) (ws: wseries) (k: nat) (i: Z) (b: blst) :
  series_facts dm ws -> wseries_wf ws -> (k < length (ws_frames ws))%nat ->
  let f := nth k (ws_frames ws) winfo0 in
  vbl_reach dm (wi_bytes ws f) i b ->
  Zlength (bs_out b) <= wi_csize f /\ bs_out b = slice (wi_content ws f) 0 (Zlength (bs_out b)).
Proof. intros Hs Hw Hk f Hr. apply (vbl_frame dm ws k i b Hs Hw Hk Hr). Qed.

(* zstd asks for nothing more exactly at the frame's end, with all of its content delivered *)
Lemma vbl_end (dm: dict_model) (ws: wseries) (k: nat) (i: Z) (b: blst) :
  series_facts dm ws -> wseries_wf ws -> (k < length (ws_frames ws))%nat ->
  let f := nth k (ws_frames ws) winfo0 in
  vbl_reach dm (wi_bytes ws f) i b -> bs_expect b = 0 ->
  i = wi_size f /\ bs_out b = wi_content ws f.
Proof. intros Hs Hw Hk f Hr. apply (vbl_frame dm ws k i b Hs Hw Hk Hr). Qed.

(* otherwise it asks for bytes of the frame, and the step succeeds (delivering nothing in a skippable frame),
   or fails at the header of a frame beyond zstd's window range *)
Lemma vbl_step (dm: dict_model) (ws: wseries) (k: nat) (i: Z) (b: blst) :
  series_facts dm ws -> wseries_wf ws -> (k < length (ws_frames ws))%nat ->
  let f := nth k (ws_frames ws) winfo0 in
  vbl_reach dm (wi_bytes ws f) i b -> bs_expect b <> 0 ->
  0 < bs_expect b /\ i + bs_expect b <= wi_size f /\
  ((exists b' out, bl_step md_dflt dm b (slice (wi_bytes ws f) i (bs_expect b)) = BLOk b' out /\
                   (wi_skippable f = true -> out = nil)) \/
   (wi_big f = true /\ bl_step md_dflt dm b (slice (wi_bytes ws f) i (bs_expect b)) = BLErr)).
Proof. intros Hs Hw Hk f Hr. apply (vbl_frame dm ws k i b Hs Hw Hk Hr). Qed.

(* ---------- the frames: bounds, tiling, reaching ---------- *)

Lemma vbl_tiles_at : forall fs off coff n cn, tiles fs off coff n cn -> forall k, (k < length fs)%nat ->
  let f := nth k fs winfo0 in
  off <= wi_start f /\ coff <= wi_cstart f /\ 0 < wi_size f /\ 0 <= wi_csize f /\
  (wi_skippable f = true -> wi_csize f = 0) /\
  wi_start f + wi_size f <= n /\ wi_cstart f + wi_csize f <= cn /\
  ((S k < length fs)%nat -> wi_start (nth (S k) fs winfo0) = wi_start f + wi_size f /\
                            wi_cstart (nth (S k) fs winfo0) = wi_cstart f + wi_csize f).
Proof.
  induction fs as [|g fs IH]; simpl; intros off coff n cn H k Hk; [lia|].
  destruct H as (H1 & H2 & H3 & H4 & H5 & H6). destruct k as [|k].
  - simpl. pose proof (sl_tiles_bounds _ _ _ _ _ H6) as (B1 & B2 & _).
    repeat split; try lia; auto.
    + destruct fs as [|g' fs]; simpl in *; [lia|]. destruct H6 as (-> & _); lia.
    + destruct fs as [|g' fs]; simpl in *; [lia|]. destruct H6 as (_ & -> & _); lia.
  - assert (Hk': (k < length fs)%nat) by lia.
    destruct (IH _ _ _ _ H6 k Hk') as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    simpl. repeat split; try lia; auto.
    all: try (intros Hs; apply A8; lia).
Qed.

Lemma vbl_frame_bounds (dm: dict_model) (ws: wseries) (k: nat) :
  series_facts dm ws -> wseries_wf ws -> (k < length (ws_frames ws))%nat ->
  let f := nth k (ws_frames ws) winfo0 in
  0 <= wi_start f /\ 0 < wi_size f /\ wi_start f + wi_size f <= Zlength (ws_bytes ws) /\
  0 <= wi_cstart f /\ 0 <= wi_csize f /\ wi_cstart f + wi_csize f <= Zlength (ws_content ws) /\
  Zlength (wi_bytes ws f) = wi_size f /\ Zlength (wi_content ws f) = wi_csize f /\
  (wi_skippable f = true -> wi_csize f = 0).
Proof.
  intros (_ & _ & _ & _ & _ & Ht & _) _ Hk f.
  destruct (vbl_tiles_at _ _ _ _ _ Ht k Hk) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _).
  fold f in A1, A2, A3, A4, A5, A6, A7.
  unfold wi_bytes, wi_content, slice. rewrite !Zlength_correct in *.
  rewrite !length_firstn, !length_skipn. repeat split; auto; lia.
Qed.

Lemma vbl_tiles_first (dm: dict_model) (ws: wseries) :
  series_facts dm ws -> wseries_wf ws ->
  wi_start (nth 0 (ws_frames ws) winfo0) = 0 /\ wi_cstart (nth 0 (ws_frames ws) winfo0) = 0.
Proof.
  intros (_ & _ & _ & _ & Hn & Ht & _) _.
  destruct (ws_frames ws) as [|g fs]; simpl in *; [lia|]. destruct Ht as (-> & -> & _). auto.
Qed.

Lemma vbl_tiles_next (dm: dict_model) (ws: wseries) (k: nat) :
  series_facts dm ws -> wseries_wf ws -> (S k < length (ws_frames ws))%nat ->
  let f := nth k (ws_frames ws) winfo0 in
  let g := nth (S k) (ws_frames ws) winfo0 in
  wi_start g = wi_start f + wi_size f /\ wi_cstart g = wi_cstart f + wi_csize f.
Proof.
  intros (_ & _ & _ & _ & _ & Ht & _) _ Hk f g.
  destruct (vbl_tiles_at _ _ _ _ _ Ht k ltac:(lia)) as (_ & _ & _ & _ & _ & _ & _ & A). apply A, Hk.
Qed.

(* the start of a frame *)
Lemma vbl_init (dm: dict_model) (fb: list Z) : vbl_reach dm fb 0 (bl_init md_dflt dm).
Proof.
  split; [rewrite Zlength_correct; lia|]. exists nil. split; [reflexivity | split; [reflexivity | constructor]].
Qed.

Lemma vbl_run_app (dm: dict_model) (b b1 b': blst) (ps: list (list Z)) (c out: list Z) :
  bl_run md_dflt dm b ps = Some b1 -> Zlength c = bs_expect b1 -> bl_step md_dflt dm b1 c = BLOk b' out ->
  bl_run md_dflt dm b (ps ++ c :: nil) = Some b'.
Proof.
  revert b. induction ps as [|p ps IH]; simpl; intros b H Hc Hs.
  - inversion H; subst. rewrite Hc, Z.eqb_refl. simpl. rewrite Hs. reflexivity.
  - destruct (negb (Zlength p =? bs_expect b)); [discriminate|].
    destruct (bl_step md_dflt dm b p); try discriminate. apply IH; auto.
Qed.

(* a successful step on the asked bytes reaches the next state *)
Lemma vbl_reach_step (dm: dict_model) (fb: list Z) (i: Z) (b b': blst) (out: list Z) :
  vbl_reach dm fb i b -> 0 < bs_expect b -> i + bs_expect b <= Zlength fb ->
  bl_step md_dflt dm b (slice fb i (bs_expect b)) = BLOk b' out ->
  vbl_reach dm fb (i + bs_expect b) b'.
Proof.
  intros (Hi & ps & Hr & Hc & Hne) He Hle Hs. split; [lia|].
  assert (Hlen: Zlength (slice fb i (bs_expect b)) = bs_expect b).
  { unfold slice. rewrite Zlength_correct, length_firstn, length_skipn.
    rewrite Zlength_correct in Hle. lia. }
  exists (ps ++ slice fb i (bs_expect b) :: nil). split; [| split].
  - eapply vbl_run_app; eauto.
  - rewrite concat_app, Hc. simpl. rewrite app_nil_r. unfold slice. rewrite !skipn_O.
    rewrite Z2Nat.inj_add by lia. rewrite Zlength_correct in Hle.
    rewrite <- (firstn_skipn (Z.to_nat i) fb) at 3.
    rewrite firstn_app, length_firstn. replace (Z.to_nat i + Z.to_nat (bs_expect b) - Nat.min (Z.to_nat i) (length fb))%nat with (Z.to_nat (bs_expect b)) by lia.
    rewrite firstn_firstn. f_equal. f_equal. lia.
  - apply Forall_app. split; [exact Hne |]. constructor; [| constructor].
    intros E. rewrite E in Hlen. rewrite Zlength_nil in Hlen. lia.
Qed.
