(* Facts about the exact frame and series models (model/ExFrame.v: x_blocks, x_frame, x_series_loop), for any
   block model, as the decoder's proofs of ZSTD_decompressFrame and ZSTD_decompressMultiFrame use them: one step of
   each loop at a time (xb_one: one block as ZSTD_decompressFrame's loop body handles it), the fuel (the length of
   the input is always enough), the bounds of what a frame takes, and the independence of the outcome from a
   relation on the decoding states that the block model respects (instantiated in ExOneshot.v with "the same
   state up to litExtraBuffer's contents").  Plain Coq. *)
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Xxh64 Zstd.proof.model.ExFrame.
Require Import Zstd.proof.dec.FS.FramesHdr.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

Section Facts.

Variable xst : Type.
Variable xst_begin : xst -> xst.
Variable x_block : xst -> list Z -> Z -> Z -> Z -> Z -> list Z -> Z -> Z -> bool -> option (xst * list Z * Z).

Local Notation XB := (x_blocks xst x_block).
Local Notation XF := (x_frame xst xst_begin x_block).
Local Notation XS := (x_series_loop xst xst_begin x_block).

(* ---------- one block ---------- *)

(* One iteration of ZSTD_decompressFrame's block loop on the bytes t at a block header, after the frame's output
   out, with the frame's capacity cap and Block_Maximum_Size bsm: the state after the block, its content, the
   bytes it takes (header included) and whether it is the last one.  None: the C returns an error. *)
Definition xb_one (st: xst) (t out: list Z) (cap bsm: Z) : option (xst * list Z * Z * bool) :=
  match cblock_size t with
  | None => None
  | Some c =>
      if c >? Zlength t - ZSTD_blockHeaderSize then None else
      let bp := block_props_of t in
      let body := slice t ZSTD_blockHeaderSize c in
      let room := cap - Zlength out in
      let res :=
        if bp_type bp =? 2 then
          match x_block st out 0 (Zlength out) 0 0 body bsm room false with
          | Some (st', mem, d) => Some (st', slice mem (Zlength out) d)
          | None => None
          end
        else if bp_type bp =? 0 then (if c >? room then None else Some (st, body))
        else (if bp_origSize bp >? room then None
              else Some (st, repeat (byte_at body 0) (Z.to_nat (bp_origSize bp)))) in
      match res with
      | None => None
      | Some (st', content) => Some (st', content, ZSTD_blockHeaderSize + c, bp_last bp =? 1)
      end
  end.

Lemma x_blocks_S (f: nat) (st: xst) (t out: list Z) (cap bsm: Z) :
  XB (S f) st t out cap bsm =
  match xb_one st t out cap bsm with
  | None => None
  | Some (st', cn, n, true) => Some (out ++ cn, n, st')
  | Some (st', cn, n, false) =>
      match XB f st' (skipn (Z.to_nat n) t) (out ++ cn) cap bsm with
      | Some (o, k, st'') => Some (o, n + k, st'')
      | None => None
      end
  end.
Proof.
  cbn [x_blocks]. unfold xb_one.
  destruct (cblock_size t) as [c|]; [|reflexivity].
  destruct (c >? Zlength t - ZSTD_blockHeaderSize); [reflexivity|]. cbv zeta.
  destruct (bp_type (block_props_of t) =? 2).
  - destruct (x_block _ _ _ _ _ _ _ _ _ _) as [[[st' mem] d]|]; [|reflexivity].
    destruct (bp_last (block_props_of t) =? 1); reflexivity.
  - destruct (bp_type (block_props_of t) =? 0).
    + destruct (c >? cap - Zlength out); [reflexivity|]. destruct (bp_last (block_props_of t) =? 1); reflexivity.
    + destruct (bp_origSize (block_props_of t) >? cap - Zlength out); [reflexivity|].
      destruct (bp_last (block_props_of t) =? 1); reflexivity.
Qed.

(* the block takes its header and its body, inside t *)
Lemma xb_one_bounds (st st': xst) (t out cn: list Z) (cap bsm n: Z) (l: bool) :
  bytes_ok t -> xb_one st t out cap bsm = Some (st', cn, n, l) ->
  ZSTD_blockHeaderSize <= n <= Zlength t /\
  exists c, cblock_size t = Some c /\ n = ZSTD_blockHeaderSize + c /\ l = (bp_last (block_props_of t) =? 1).
Proof.
  intros Hb H. unfold xb_one in H.
  destruct (cblock_size t) as [c|] eqn:Ec; [|discriminate].
  pose proof (fh_cblock_size_nonneg t c Hb Ec) as Hc.
  destruct (Z.gtb_spec c (Zlength t - ZSTD_blockHeaderSize)) as [_|Hle]; [discriminate|].
  remember (ZSTD_blockHeaderSize + c) as n0 eqn:En0. cbv zeta in H.
  destruct (if bp_type (block_props_of t) =? 2 then _ else _) as [[st1 cn1]|]; [|discriminate].
  injection H as E1 E2 E3 E4; subst. split; [unfold ZSTD_blockHeaderSize in *; lia|]. exists c. auto.
Qed.

(* ---------- the blocks of a frame: fuel ---------- *)

Lemma Zlength_skipn_nat (t: list Z) (n: Z) : 0 <= n <= Zlength t ->
  length (skipn (Z.to_nat n) t) = (length t - Z.to_nat n)%nat.
Proof. intros. rewrite skipn_length. reflexivity. Qed.

(* any fuel at least the length of the bytes gives the same result *)
Lemma x_blocks_fuel (f g: nat) (st: xst) (t out: list Z) (cap bsm: Z) :
  bytes_ok t -> (length t <= f)%nat -> (length t <= g)%nat -> XB f st t out cap bsm = XB g st t out cap bsm.
Proof.
  revert g st t out. induction f as [|f IH]; intros g st t out Hb Hf Hg.
  - destruct t; [|cbn in Hf; lia].
    destruct g as [|g]; [reflexivity|]. rewrite x_blocks_S. unfold xb_one. reflexivity.
  - destruct g as [|g].
    + destruct t; [|cbn in Hg; lia]. rewrite x_blocks_S. unfold xb_one. reflexivity.
    + rewrite !x_blocks_S. destruct (xb_one st t out cap bsm) as [[[[st' cn] n] l]|] eqn:E; [|reflexivity].
      destruct l; [reflexivity|].
      destruct (xb_one_bounds st st' t out cn cap bsm n false Hb E) as [Hn _].
      rewrite (IH g st' (skipn (Z.to_nat n) t) (out ++ cn)); [reflexivity| | |].
      * apply fh_Forall_skipn. exact Hb.
      * rewrite skipn_length. rewrite Zlength_correct in Hn. unfold ZSTD_blockHeaderSize in Hn. lia.
      * rewrite skipn_length. rewrite Zlength_correct in Hn. unfold ZSTD_blockHeaderSize in Hn. lia.
Qed.

(* the blocks with the length of the bytes as fuel *)
Definition xbs (st: xst) (t out: list Z) (cap bsm: Z) : option (list Z * Z * xst) :=
  XB (length t) st t out cap bsm.

(* the result after the first n bytes, shifted by n *)
Definition xb_shift (n: Z) (r: option (list Z * Z * xst)) : option (list Z * Z * xst) :=
  match r with Some (o, k, st') => Some (o, n + k, st') | None => None end.

Lemma xb_shift_0 (r: option (list Z * Z * xst)) : xb_shift 0 r = r.
Proof. destruct r as [[[o k] st']|]; reflexivity. Qed.

Lemma xb_shift_shift (a b: Z) (r: option (list Z * Z * xst)) : xb_shift a (xb_shift b r) = xb_shift (a + b) r.
Proof. destruct r as [[[o k] st']|]; cbn; [rewrite Z.add_assoc|]; reflexivity. Qed.

Lemma xbs_err (st: xst) (t out: list Z) (cap bsm: Z) :
  xb_one st t out cap bsm = None -> xbs st t out cap bsm = None.
Proof.
  intros E. unfold xbs. destruct t as [|x t].
  - reflexivity.
  - cbn [length]. rewrite x_blocks_S, E. reflexivity.
Qed.

Lemma xbs_last (st st': xst) (t out cn: list Z) (cap bsm n: Z) :
  xb_one st t out cap bsm = Some (st', cn, n, true) -> xbs st t out cap bsm = Some (out ++ cn, n, st').
Proof.
  intros E. unfold xbs. destruct t as [|x t].
  - unfold xb_one in E. discriminate.
  - cbn [length]. rewrite x_blocks_S, E. reflexivity.
Qed.

Lemma xbs_next (st st': xst) (t out cn: list Z) (cap bsm n: Z) :
  bytes_ok t -> xb_one st t out cap bsm = Some (st', cn, n, false) ->
  xbs st t out cap bsm = xb_shift n (xbs st' (skipn (Z.to_nat n) t) (out ++ cn) cap bsm).
Proof.
  intros Hb E. destruct (xb_one_bounds st st' t out cn cap bsm n false Hb E) as [Hn _].
  unfold xbs. destruct t as [|x t'].
  - unfold xb_one in E. discriminate.
  - cbn [length]. rewrite x_blocks_S, E. unfold xb_shift.
    rewrite (x_blocks_fuel (length t') (length (skipn (Z.to_nat n) (x :: t'))) st'
      (skipn (Z.to_nat n) (x :: t')) (out ++ cn)).
    + reflexivity.
    + apply fh_Forall_skipn. exact Hb.
    + rewrite skipn_length. rewrite Zlength_correct in Hn. cbn [length] in *.
      unfold ZSTD_blockHeaderSize in Hn. lia.
    + lia.
Qed.

(* a successful walk takes at least one block header, inside t, and appends to out *)
Lemma x_blocks_bounds (f: nat) (st st': xst) (t out o: list Z) (cap bsm k: Z) :
  bytes_ok t -> XB f st t out cap bsm = Some (o, k, st') ->
  ZSTD_blockHeaderSize <= k <= Zlength t /\ exists cn, o = out ++ cn.
Proof.
  revert st t out k. induction f as [|f IH]; intros st t out k Hb H; [discriminate|].
  rewrite x_blocks_S in H.
  destruct (xb_one st t out cap bsm) as [[[[st1 cn] n] l]|] eqn:E; [|discriminate].
  destruct (xb_one_bounds st st1 t out cn cap bsm n l Hb E) as [Hn _].
  destruct l.
  - inversion H; subst. split; [lia|]. exists cn. reflexivity.
  - destruct (XB f st1 (skipn (Z.to_nat n) t) (out ++ cn) cap bsm) as [[[o1 k1] st2]|] eqn:E1; [|discriminate].
    inversion H; subst.
    destruct (IH st1 (skipn (Z.to_nat n) t) (out ++ cn) k1 (fh_Forall_skipn _ _ _ Hb) E1) as [Hk [cn' Ho]].
    rewrite fh_Zlength_skipn in Hk by (unfold ZSTD_blockHeaderSize in *; lia).
    split; [unfold ZSTD_blockHeaderSize in *; lia|]. exists (cn ++ cn'). rewrite Ho, app_assoc. reflexivity.
Qed.

(* ---------- one frame ---------- *)

(* the end of a frame after its blocks (ZSTD_decompressFrame 1050-1066): the content size check, the checksum *)
Definition x_fend (h: frame_header) (s: list Z) (hs: Z) (out: list Z) (k: Z) (st': xst) : option (list Z * Z * xst) :=
  if negb (fh_contentSize h =? ZSTD_CONTENTSIZE_UNKNOWN) && negb (Zlength out =? fh_contentSize h)
  then None else
  if fh_checksumFlag h =? 1 then
    (if Zlength s - hs - k <? 4 then None
     else if negb (le_field s (hs + k) 4 =? xxh64 out 0 mod 2 ^ 32) then None
     else Some (out, hs + k + 4, st'))
  else Some (out, hs + k, st').

(* the checks before the blocks, each an error of the C (ZSTD_decompressFrame 971-984) *)
Lemma x_frame_short (st: xst) (s: list Z) (cap: Z) :
  Zlength s < ZSTD_FRAMEHEADERSIZE_MIN + ZSTD_blockHeaderSize -> XF st s cap = None.
Proof. intros H. unfold x_frame. destruct (Z.ltb_spec (Zlength s) (ZSTD_FRAMEHEADERSIZE_MIN + ZSTD_blockHeaderSize)); [reflexivity|lia]. Qed.

Lemma x_frame_short_hs (st: xst) (s: list Z) (cap: Z) :
  Zlength s < fhd_header_size (byte_at s 4) + ZSTD_blockHeaderSize -> XF st s cap = None.
Proof.
  intros H. unfold x_frame. destruct (Zlength s <? _); [reflexivity|]. cbv zeta.
  destruct (Z.ltb_spec (Zlength s) (fhd_header_size (byte_at s 4) + ZSTD_blockHeaderSize)); [reflexivity|lia].
Qed.

(* with the sizes checked: the header ZSTD_decodeFrameHeader decodes, then the blocks and the end *)
Lemma x_frame_eq (st: xst) (s: list Z) (cap: Z) :
  ZSTD_FRAMEHEADERSIZE_MIN + ZSTD_blockHeaderSize <= Zlength s ->
  fhd_header_size (byte_at s 4) + ZSTD_blockHeaderSize <= Zlength s ->
  XF st s cap =
  let hs := fhd_header_size (byte_at s 4) in
  match get_frame_header (slice s 0 hs) with
  | FH_ok h =>
      if negb (fh_dictID h =? 0) then None else
      let rest := skipn (Z.to_nat hs) s in
      match XB (length rest) (xst_begin st) rest nil cap (fh_blockSizeMax h) with
      | None => None
      | Some (out, k, st') => x_fend h s hs out k st'
      end
  | _ => None
  end.
Proof.
  intros H1 H2. unfold x_frame.
  destruct (Z.ltb_spec (Zlength s) (ZSTD_FRAMEHEADERSIZE_MIN + ZSTD_blockHeaderSize)); [lia|].
  destruct (Z.ltb_spec (Zlength s) (fhd_header_size (byte_at s 4) + ZSTD_blockHeaderSize)); [lia|].
  reflexivity.
Qed.

Lemma fhd_header_size_bounds (fhd: Z) : 5 <= fhd_header_size fhd <= 19.
Proof.
  unfold fhd_header_size.
  assert (Hs: 0 <= Z.land (Z.shiftr fhd 5) 1 <= 1).
  { replace (Z.land (Z.shiftr fhd 5) 1) with (Z.shiftr fhd 5 mod 2)
      by (rewrite <- (Z.land_ones _ 1) by lia; reflexivity).
    pose proof (Z.mod_pos_bound (Z.shiftr fhd 5) 2). lia. }
  assert (Hd: forall n, 0 <= nth n [0; 1; 2; 4] 0 <= 4) by (intros [|[|[|[|n]]]]; cbn; try lia; destruct n; cbn; lia).
  assert (Hf: forall n, 0 <= nth n [0; 2; 4; 8] 0 <= 8) by (intros [|[|[|[|n]]]]; cbn; try lia; destruct n; cbn; lia).
  specialize (Hd (Z.to_nat (Z.land fhd 3))). specialize (Hf (Z.to_nat (Z.shiftr fhd 6))).
  destruct ((Z.land (Z.shiftr fhd 5) 1 =? 1) && (Z.shiftr fhd 6 =? 0)); lia.
Qed.

(* a frame takes at least its header and a block header, inside s *)
Lemma x_frame_bounds (st st': xst) (s c: list Z) (cap k: Z) :
  bytes_ok s -> XF st s cap = Some (c, k, st') -> 8 <= k <= Zlength s.
Proof.
  intros Hb H.
  destruct (Z.ltb_spec (Zlength s) (ZSTD_FRAMEHEADERSIZE_MIN + ZSTD_blockHeaderSize)) as [Hl|Hl].
  { rewrite x_frame_short in H by exact Hl. discriminate. }
  destruct (Z.ltb_spec (Zlength s) (fhd_header_size (byte_at s 4) + ZSTD_blockHeaderSize)) as [Hl2|Hl2].
  { rewrite x_frame_short_hs in H by exact Hl2. discriminate. }
  rewrite x_frame_eq in H by lia. cbv zeta in H.
  pose proof (fhd_header_size_bounds (byte_at s 4)) as Hhs.
  set (hs := fhd_header_size (byte_at s 4)) in *.
  destruct (get_frame_header (slice s 0 hs)) as [| |h]; try discriminate.
  destruct (negb (fh_dictID h =? 0)); [discriminate|].
  destruct (XB _ _ _ _ _ _) as [[[out kb] st1]|] eqn:E; [|discriminate].
  destruct (x_blocks_bounds _ _ _ _ _ _ _ _ _ (fh_Forall_skipn _ _ _ Hb) E) as [Hk _].
  rewrite fh_Zlength_skipn in Hk by (unfold ZSTD_blockHeaderSize in *; lia).
  unfold x_fend in H.
  destruct (negb _ && negb _); [discriminate|].
  destruct (fh_checksumFlag h =? 1).
  - destruct (Z.ltb_spec (Zlength s - hs - kb) 4); [discriminate|].
    destruct (negb _); [discriminate|]. inversion H; subst. unfold ZSTD_blockHeaderSize in *. lia.
  - inversion H; subst. unfold ZSTD_blockHeaderSize in *. lia.
Qed.

(* ---------- the series ---------- *)

Lemma x_series_loop_S (f: nat) (st: xst) (s: list Z) (cap: Z) (out: list Z) :
  XS (S f) st s cap out =
  if Zlength s <? ZSTD_FRAMEHEADERSIZE_PREFIX then (if Zlength s =? 0 then Some out else None) else
  if is_skippable_magic (le_field s 0 4) then
    match skippable_frame_size s with
    | None => None
    | Some k => XS f st (skipn (Z.to_nat k) s) cap out
    end
  else
    match XF st s (cap - Zlength out) with
    | None => None
    | Some (c, k, st') => XS f st' (skipn (Z.to_nat k) s) cap (out ++ c)
    end.
Proof. reflexivity. Qed.

Lemma skippable_frame_size_bounds (s: list Z) (k: Z) :
  bytes_ok s -> skippable_frame_size s = Some k -> ZSTD_SKIPPABLEHEADERSIZE <= k <= Zlength s.
Proof.
  intros Hb H. unfold skippable_frame_size in H.
  destruct (Zlength s <? ZSTD_SKIPPABLEHEADERSIZE); [discriminate|].
  destruct (Z.gtb_spec (le_field s 4 4 + ZSTD_SKIPPABLEHEADERSIZE) (Zlength s)); [discriminate|].
  inversion H; subst. pose proof (fh_le_field_bound s 4 4 Hb ltac:(lia)). lia.
Qed.

(* any fuel beyond the length of the bytes gives the same result *)
Lemma x_series_loop_fuel (f g: nat) (st: xst) (s: list Z) (cap: Z) (out: list Z) :
  bytes_ok s -> (length s < f)%nat -> (length s < g)%nat -> XS f st s cap out = XS g st s cap out.
Proof.
  revert g st s out. induction f as [|f IH]; intros g st s out Hb Hf Hg; [lia|].
  destruct g as [|g]; [lia|]. rewrite !x_series_loop_S.
  destruct (Zlength s <? ZSTD_FRAMEHEADERSIZE_PREFIX); [reflexivity|].
  destruct (is_skippable_magic (le_field s 0 4)).
  - destruct (skippable_frame_size s) as [k|] eqn:E; [|reflexivity].
    pose proof (skippable_frame_size_bounds s k Hb E) as Hk. unfold ZSTD_SKIPPABLEHEADERSIZE in Hk.
    apply IH; [apply fh_Forall_skipn; exact Hb| |];
      rewrite skipn_length; rewrite Zlength_correct in Hk; lia.
  - destruct (XF st s (cap - Zlength out)) as [[[c k] st']|] eqn:E; [|reflexivity].
    pose proof (x_frame_bounds st st' s c _ k Hb E) as Hk.
    apply IH; [apply fh_Forall_skipn; exact Hb| |];
      rewrite skipn_length; rewrite Zlength_correct in Hk; lia.
Qed.

(* ---------- independence from a relation on the states ---------- *)

Section Rel.
(* Rb relates states at a block (the block model respects it), Rs states between frames (ZSTD_decompressBegin
   makes Rb of it) *)
Variable Rb Rs : xst -> xst -> Prop.
Hypothesis begin_R : forall a b, Rs a b -> Rb (xst_begin a) (xst_begin b).
Hypothesis Rb_Rs : forall a b, Rb a b -> Rs a b.
Hypothesis block_R : forall a b mem body bsm cap, Rb a b -> bytes_ok body ->
  match x_block a mem 0 (Zlength mem) 0 0 body bsm cap false, x_block b mem 0 (Zlength mem) 0 0 body bsm cap false with
  | None, None => True
  | Some (a', m1, n1), Some (b', m2, n2) =>
      n1 = n2 /\ Rb a' b' /\ slice m1 (Zlength mem) n1 = slice m2 (Zlength mem) n2
  | _, _ => False
  end.

Lemma xb_one_R (a b: xst) (t out: list Z) (cap bsm: Z) :
  Rb a b -> bytes_ok t ->
  match xb_one a t out cap bsm, xb_one b t out cap bsm with
  | None, None => True
  | Some (a', c1, n1, l1), Some (b', c2, n2, l2) => c1 = c2 /\ n1 = n2 /\ l1 = l2 /\ Rb a' b'
  | _, _ => False
  end.
Proof.
  intros R Hb. unfold xb_one.
  destruct (cblock_size t) as [c|]; [|exact I].
  destruct (c >? Zlength t - ZSTD_blockHeaderSize); [exact I|]. cbv zeta.
  destruct (bp_type (block_props_of t) =? 2).
  - pose proof (block_R a b out (slice t ZSTD_blockHeaderSize c) bsm (cap - Zlength out) R
      (fh_Forall_firstn _ _ _ (fh_Forall_skipn _ _ _ Hb))) as HB.
    destruct (x_block a _ _ _ _ _ _ _ _ _) as [[[a' m1] n1]|];
      destruct (x_block b _ _ _ _ _ _ _ _ _) as [[[b' m2] n2]|]; try contradiction; [|exact I].
    destruct HB as (-> & HR & Hc). rewrite Hc. auto.
  - destruct (bp_type (block_props_of t) =? 0).
    + destruct (c >? cap - Zlength out); [exact I|]. auto.
    + destruct (bp_origSize (block_props_of t) >? cap - Zlength out); [exact I|]. auto.
Qed.

Lemma x_blocks_R (f: nat) (a b: xst) (t out: list Z) (cap bsm: Z) :
  Rb a b -> bytes_ok t ->
  match XB f a t out cap bsm, XB f b t out cap bsm with
  | None, None => True
  | Some (o1, k1, a'), Some (o2, k2, b') => o1 = o2 /\ k1 = k2 /\ Rb a' b'
  | _, _ => False
  end.
Proof.
  revert a b t out. induction f as [|f IH]; intros a b t out R Hb; [exact I|].
  rewrite !x_blocks_S. pose proof (xb_one_R a b t out cap bsm R Hb) as H1.
  destruct (xb_one a t out cap bsm) as [[[[a' c1] n1] l1]|];
    destruct (xb_one b t out cap bsm) as [[[[b' c2] n2] l2]|]; try contradiction; [|exact I].
  destruct H1 as (<- & <- & <- & HR).
  destruct l1; [auto|].
  specialize (IH a' b' (skipn (Z.to_nat n1) t) (out ++ c1) HR (fh_Forall_skipn _ _ _ Hb)).
  destruct (XB f a' _ _ cap bsm) as [[[o1 k1] a'']|];
    destruct (XB f b' _ _ cap bsm) as [[[o2 k2] b'']|]; try contradiction; [|exact I].
  destruct IH as (<- & <- & HR'). auto.
Qed.

Lemma x_frame_R (a b: xst) (s: list Z) (cap: Z) :
  Rs a b -> bytes_ok s ->
  match XF a s cap, XF b s cap with
  | None, None => True
  | Some (c1, k1, a'), Some (c2, k2, b') => c1 = c2 /\ k1 = k2 /\ Rs a' b'
  | _, _ => False
  end.
Proof.
  intros R Hb. unfold x_frame.
  destruct (Zlength s <? _); [exact I|]. cbv zeta. destruct (Zlength s <? _); [exact I|].
  destruct (get_frame_header _) as [| |h]; try exact I.
  destruct (negb (fh_dictID h =? 0)); [exact I|].
  pose proof (x_blocks_R (length (skipn (Z.to_nat (fhd_header_size (byte_at s 4))) s)) (xst_begin a) (xst_begin b)
    (skipn (Z.to_nat (fhd_header_size (byte_at s 4))) s) nil cap (fh_blockSizeMax h) (begin_R a b R)
    (fh_Forall_skipn _ _ _ Hb)) as HB.
  destruct (XB _ (xst_begin a) _ _ _ _) as [[[o1 k1] a']|];
    destruct (XB _ (xst_begin b) _ _ _ _) as [[[o2 k2] b']|]; try contradiction; [|exact I].
  destruct HB as (<- & <- & HR). apply Rb_Rs in HR.
  destruct (negb _ && negb _); [exact I|].
  destruct (fh_checksumFlag h =? 1); [|auto].
  destruct (Zlength s - _ - k1 <? 4); [exact I|]. destruct (negb _); [exact I|]. auto.
Qed.

Lemma x_series_loop_R (f: nat) (a b: xst) (s: list Z) (cap: Z) (out: list Z) :
  Rs a b -> bytes_ok s -> XS f a s cap out = XS f b s cap out.
Proof.
  revert a b s out. induction f as [|f IH]; intros a b s out R Hb; [reflexivity|].
  rewrite !x_series_loop_S.
  destruct (Zlength s <? _); [reflexivity|].
  destruct (is_skippable_magic _).
  - destruct (skippable_frame_size s); [apply IH; [exact R|apply fh_Forall_skipn; exact Hb]|reflexivity].
  - pose proof (x_frame_R a b s (cap - Zlength out) R Hb) as HF.
    destruct (XF a s _) as [[[c1 k1] a']|]; destruct (XF b s _) as [[[c2 k2] b']|]; try contradiction; [|reflexivity].
    destruct HF as (<- & <- & HR). apply IH; [exact HR|apply fh_Forall_skipn; exact Hb].
Qed.

End Rel.

End Facts.
