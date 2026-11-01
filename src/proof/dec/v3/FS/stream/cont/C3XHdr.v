(* ZSTD_decompressContinue exactly: the exits of the stages that decode no block (block header, checksum, skippable
   content), as plain lemmas the body's proof applies at each return (cont_exact1 with the frame fields it returns). *)
Require Import Zstd.proof.dec.v3.FS.stream.S3Specs.
Require Import Zstd.proof.dec.v3.FS.stream.cont.C3Base.
Require Import Zstd.proof.dec.v3.FS.stream.cont.C3XDefs.
Require Import Zstd.proof.dec.v3.FS.stream.cont.C3XKit.
Require Import Zstd.proof.model.ExStream.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

(* the frame fields a stage change keeps (all drel reads but the stage, expected, bType and rleSize) *)
Definition fs_keep (fs fs': fstate) : Prop :=
  fs_fParams fs' = fs_fParams fs /\ fs_isFrameDecompression fs' = fs_isFrameDecompression fs /\
  fs_decodedSize fs' = fs_decodedSize fs /\ fs_validateChecksum fs' = fs_validateChecksum fs /\
  fs_xxh fs' = fs_xxh fs /\ fs_previousDstEnd fs' = fs_previousDstEnd fs /\
  fs_prefixStart fs' = fs_prefixStart fs /\ fs_virtualStart fs' = fs_virtualStart fs /\
  fs_dictEnd fs' = fs_dictEnd fs /\ fs_gpDictCopy fs' = fs_gpDictCopy fs.

(* a stage change on both sides *)
Lemma drel_goto fh d ob fs ts d' fs' :
  drel fh d ob fs ts -> fs_keep fs fs' ->
  d_out XS d' = d_out XS d -> d_check XS d' = d_check XS d -> d_ent XS d' = d_ent XS d ->
  d_prev XS d' = d_prev XS d -> d_pfx XS d' = d_pfx XS d -> d_ds XS d' = d_ds XS d -> d_de XS d' = d_de XS d ->
  0 <= d_stage XS d' <= DS_skipFrame -> 0 <= d_expected XS d' <= Int64.max_unsigned -> 0 <= d_btype XS d' <= 3 ->
  0 <= d_rle XS d' <= Int64.max_unsigned ->
  (DS_decodeBlockHeader <= d_stage XS d' <= DS_checkChecksum -> DS_decodeBlockHeader <= d_stage XS d <= DS_checkChecksum) ->
  fs_stage fs' = Vint (Int.repr (d_stage XS d')) -> fs_expected fs' = vlong (d_expected XS d') ->
  (d_stage XS d' = DS_decompressBlock \/ d_stage XS d' = DS_decompressLastBlock ->
     fs_bType fs' = Vint (Int.repr (d_btype XS d')) /\ fs_rleSize fs' = vlong (d_rle XS d')) ->
  drel fh d' ob fs' ts.
Proof.
  intros H (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10) S1 S2 S3 S4 S5 S6 S7 R1 R2 R3 R4 Hst E1 E2 E3.
  drel_d H.
  assert (Ev: vstart_of ob d' = vstart_of ob d) by (unfold vstart_of; rewrite S5, S6, S7; reflexivity).
  unfold drel. rewrite K1, K2, K3, K4, K5, K6, K7, K8, K9, K10, S1, S2, S3, S4, S5, S6, S7, Ev.
  split; [exact Ep |]. split; [exact Rc |]. split; [exact Rb |]. split; [exact Rk |].
  split; [exact R1 |]. split; [exact R2 |]. split; [exact R3 |]. split; [exact R4 |].
  split; [exact Roff |]. split; [exact Rxh |]. split; [exact Rts |]. split; [exact Rfd |].
  split; [exact E1 |]. split; [exact E2 |]. split; [exact E3 |].
  intros Hs. exact (Hptr (Hst Hs)).
Qed.

(* the end of a frame, on the content length zstd counts (decodedSize, modulo 2^64) *)
Lemma end_frame_eq fh d h L :
  fh_contentSize fh = fh_contentSize h -> fh_checksumFlag fh = fh_checksumFlag h ->
  Zlength (d_out XS d) mod 2 ^ 64 = L mod 2 ^ 64 ->
  d_end_frame XS fh d =
  if negb (fh_contentSize h =? ZSTD_CONTENTSIZE_UNKNOWN) && negb (L mod 2 ^ 64 =? fh_contentSize h) then None
  else if fh_checksumFlag h =? 1 then Some (d_goto XS d DS_checkChecksum 4)
  else Some (d_goto XS d DS_getFrameHeaderSize 0).
Proof. intros E1 E2 E3. unfold d_end_frame. rewrite E1, E2, E3. reflexivity. Qed.

Lemma vlong_mod a b : vlong a = Vlong (Int64.repr b) -> a mod 2 ^ 64 = b mod 2 ^ 64.
Proof.
  unfold vlong. intros E. assert (E': Int64.repr a = Int64.repr b) by congruence.
  apply (f_equal Int64.unsigned) in E'. rewrite !Int64.unsigned_repr_eq in E'. exact E'.
Qed.

(* ---------- decodeBlockHeader ---------- *)

Section Bhdr.
Variables (fs1: fstate) (ts: tstate) (o: outarr) (u: list Z) (n: Z) (h: frame_header) (bsm: Z).
Hypothesis Hst: fs_stage fs1 = Vint (Int.repr 2).
Hypothesis Hfp: fs_fParams fs1 = fh_val (fh_adj h bsm).
Hypothesis Hcs: 0 <= fh_contentSize h <= Int64.max_unsigned.
Hypothesis Hbsm: 0 <= bsm <= ZSTD_BLOCKSIZE_MAX.
Hypothesis Hck: fh_checksumFlag h = 0 \/ fh_checksumFlag h = 1.

Lemma bhdr_body fh d mem :
  drel fh d (oa_base o) fs1 ts ->
  d_stage XS d = 2 /\ fh_contentSize fh = fh_contentSize h /\ fh_blockSizeMax fh = bsm /\
  fh_checksumFlag fh = fh_checksumFlag h /\
  d_body fh d mem (oa_d o) (oa_cap o) u n =
    match cblock_size u with
    | None => None
    | Some c =>
        if c >? bsm then None else
        let bp := block_props_of u in
        let d1 := mkD XS 2 c (bp_type bp) (bp_origSize bp) (d_out XS d) (d_check XS d) (d_ent XS d)
                      (d_prev XS d) (d_pfx XS d) (d_ds XS d) (d_de XS d) in
        if c >? 0 then
          Some (d_goto XS d1 (if bp_last bp =? 1 then DS_decompressLastBlock else DS_decompressBlock) c, mem, 0)
        else if bp_last bp =? 1 then
          match d_end_frame XS fh d1 with Some d2 => Some (d2, mem, 0) | None => None end
        else Some (d_goto XS d1 DS_decodeBlockHeader ZSTD_blockHeaderSize, mem, 0)
    end.
Proof.
  intros Hd. assert (Ds: d_stage XS d = 2) by (apply (drel_stage _ _ _ _ _ _ Hd Hst); lia).
  destruct (drel_fh _ _ _ _ _ _ _ Hd Hfp Hcs ltac:(unfold ZSTD_BLOCKSIZE_MAX in Hbsm; rep_lia)
              ltac:(destruct Hck as [-> | ->]; rep_lia)) as (F1 & F2 & F3).
  split; [exact Ds |]. split; [exact F1 |]. split; [exact F2 |]. split; [exact F3 |].
  unfold d_body. rewrite Ds, F2. reflexivity.
Qed.

(* getcBlockSize failed *)
Lemma cx_bhdr_bad r oc' fs' tabs' :
  cblock_size u = None -> is_error_code r = true -> cont_exact1 fs1 ts o u n r oc' fs' tabs'.
Proof using All.
  intros Ec Er fh d mem Hd _ _ _. destruct (bhdr_body fh d mem Hd) as (_ & _ & _ & _ & ->).
  rewrite Ec. exact Er.
Qed.

(* the block size exceeds Block_Maximum_Size *)
Lemma cx_bhdr_big r oc' fs' tabs' c :
  cblock_size u = Some c -> bsm < c -> is_error_code r = true -> cont_exact1 fs1 ts o u n r oc' fs' tabs'.
Proof using All.
  intros Ec Hc Er fh d mem Hd _ _ _. destruct (bhdr_body fh d mem Hd) as (_ & _ & _ & _ & ->).
  rewrite Ec. replace (c >? bsm) with true by lia. exact Er.
Qed.

(* the stage and size of the next block, or after an empty block *)
Lemma cx_bhdr_ok c st' e' fs' :
  cblock_size u = Some c -> c <= bsm -> bytes_ok u -> fs_keep fs1 fs' ->
  fs_bType fs' = Vint (Int.repr (Z.land (Z.shiftr (le_field u 0 3) 1) 3)) ->
  fs_rleSize fs' = Vlong (Int64.repr (Int.unsigned (Int.repr (Z.shiftr (le_field u 0 3) 3)))) ->
  fs_stage fs' = Vint (Int.repr st') -> fs_expected fs' = Vlong (Int64.repr e') ->
  (* what the C returned to, as the model's stage: *)
  (0 < c -> st' = (if bp_last (block_props_of u) =? 1 then 4 else 3) /\ e' = c) ->
  (c = 0 -> bp_last (block_props_of u) <> 1 -> st' = 2 /\ e' = 3) ->
  (c = 0 -> bp_last (block_props_of u) = 1 ->
     (fh_contentSize h = ZSTD_CONTENTSIZE_UNKNOWN \/
      exists L, fs_decodedSize fs1 = Vlong (Int64.repr L) /\ L mod 2 ^ 64 = fh_contentSize h) /\
     (if fh_checksumFlag h =? 1 then st' = 5 /\ e' = 4 else st' = 0 /\ e' = 0)) ->
  cont_exact1 fs1 ts o u n 0 (oa_c o) fs' (Some ts).
Proof using All.
  intros Ec Hcb Bu K Fbt Frl Fst Fex Hgo Hnl Hlast fh d mem Hd Hm _ _.
  destruct (bhdr_body fh d mem Hd) as (Ds & F1 & F2 & F3 & ->).
  pose proof (cblock_size_range u c Bu Ec) as Hcr.
  assert (Hos: 0 <= Z.shiftr (le_field u 0 3) 3 < 2 ^ 21).
  { pose proof (lef_range u 0 3 Bu ltac:(lia)). rewrite Z.shiftr_div_pow2 by lia.
    split; [apply Z.div_pos; lia |]. apply Z.div_lt_upper_bound; [lia |].
    change (2 ^ 3 * 2 ^ 21) with (2 ^ (8 * 3)). lia. }
  pose proof (bp_type_range u) as Hbt. pose proof (bp_last01 u) as Hl01.
  rewrite Ec. replace (c >? bsm) with false by lia. cbv zeta.
  pose proof Hd as Hd0. drel_d Hd0.
  assert (G: forall st2 e2, 0 <= st2 <= 7 -> 0 <= e2 <= Int64.max_unsigned -> st' = st2 -> e' = e2 ->
             drel fh (d_goto XS (mkD XS 2 c (bp_type (block_props_of u)) (bp_origSize (block_props_of u))
                      (d_out XS d) (d_check XS d) (d_ent XS d) (d_prev XS d) (d_pfx XS d) (d_ds XS d) (d_de XS d)) st2 e2)
               (oa_base o) fs' ts).
  { intros st2 e2 Hs2 He2 -> ->.
    apply (drel_goto fh d (oa_base o) fs1 ts); try exact Hd; try exact K; try reflexivity.
    all: cbn [d_stage d_expected d_btype d_rle d_goto].
    - unfold DS_skipFrame; lia.
    - lia.
    - exact Hbt.
    - unfold block_props_of in *; cbn [bp_origSize] in *; rep_lia.
    - intros _. rewrite Ds. unfold DS_decodeBlockHeader, DS_checkChecksum; lia.
    - exact Fst.
    - rewrite Fex. reflexivity.
    - intros _. rewrite Fbt, Frl. split; [reflexivity |]. unfold vlong, block_props_of; cbn [bp_origSize].
      rewrite Int.unsigned_repr by rep_lia. reflexivity. }
  destruct (Z.gtb_spec c 0) as [Hc0 | Hc0]; cbv beta iota.
  - destruct (Hgo Hc0) as [E1 E2]. cbn [cx_match].
    split; [reflexivity |]. split; [exact Hm |]. exists ts. split; [reflexivity |].
    apply G.
    + destruct (_ =? 1); unfold DS_decompressLastBlock, DS_decompressBlock; lia.
    + rep_lia.
    + rewrite E1. destruct (_ =? 1); reflexivity.
    + exact E2.
  - assert (c = 0) as -> by lia.
    destruct (Z.eqb_spec (bp_last (block_props_of u)) 1) as [El | El]; cbv beta iota.
    + destruct (Hlast eq_refl El) as [Hcs' Hfin].
      assert (HE: exists L, Zlength (d_out XS d) mod 2 ^ 64 = L mod 2 ^ 64 /\
                    (fh_contentSize h = ZSTD_CONTENTSIZE_UNKNOWN \/ L mod 2 ^ 64 = fh_contentSize h)).
      { destruct Hcs' as [Hu | (L & EL & HL)]; [exists (Zlength (d_out XS d)); auto |].
        exists L. split; [| auto].
        destruct (Hptr ltac:(rewrite Ds; unfold DS_decodeBlockHeader, DS_checkChecksum; lia)) as (Dd & _).
        rewrite Dd in EL. apply vlong_mod, EL. }
      destruct HE as (L & HL1 & HL2).
      match goal with |- context [d_end_frame XS fh ?D] => rewrite (end_frame_eq fh D h L F1 F3 HL1) end.
      replace (negb (fh_contentSize h =? ZSTD_CONTENTSIZE_UNKNOWN) && negb (L mod 2 ^ 64 =? fh_contentSize h))
        with false by (destruct HL2 as [-> | ->]; rewrite Z.eqb_refl; [reflexivity | cbn [negb]; destruct (negb _); reflexivity]).
      cbv beta iota.
      destruct (fh_checksumFlag h =? 1); destruct Hfin as [E1 E2]; cbn [cx_match];
        (split; [reflexivity |]; split; [exact Hm |]; exists ts; split; [reflexivity |];
         apply G; [unfold DS_checkChecksum, DS_getFrameHeaderSize; lia | rep_lia | exact E1 | exact E2]).
    + destruct (Hnl eq_refl El) as [E1 E2]. cbn [cx_match].
      split; [reflexivity |]. split; [exact Hm |]. exists ts. split; [reflexivity |].
      apply G; [unfold DS_decodeBlockHeader; lia | unfold ZSTD_blockHeaderSize; rep_lia | exact E1 | exact E2].
Qed.

(* the empty last block whose content size disagrees *)
Lemma cx_bhdr_fcs r oc' fs' tabs' L :
  cblock_size u = Some 0 -> bp_last (block_props_of u) = 1 ->
  fs_decodedSize fs1 = Vlong (Int64.repr L) ->
  fh_contentSize h <> ZSTD_CONTENTSIZE_UNKNOWN -> L mod 2 ^ 64 <> fh_contentSize h ->
  is_error_code r = true -> cont_exact1 fs1 ts o u n r oc' fs' tabs'.
Proof using All.
  intros Ec El EL Hu HL Er fh d mem Hd _ _ _.
  destruct (bhdr_body fh d mem Hd) as (Ds & F1 & F2 & F3 & ->).
  rewrite Ec. replace (0 >? bsm) with false by (unfold ZSTD_BLOCKSIZE_MAX in Hbsm; lia). cbv zeta.
  replace (0 >? 0) with false by reflexivity. rewrite El. cbv beta iota. cbn [Z.eqb Pos.eqb]. cbv beta iota.
  pose proof Hd as Hd0. drel_d Hd0.
  destruct (Hptr ltac:(rewrite Ds; unfold DS_decodeBlockHeader, DS_checkChecksum; lia)) as (Dd & _).
  rewrite Dd in EL.
  match goal with |- context [d_end_frame XS fh ?D] => rewrite (end_frame_eq fh D h L F1 F3 (vlong_mod _ _ EL)) end.
  replace (fh_contentSize h =? ZSTD_CONTENTSIZE_UNKNOWN) with false by (symmetry; apply Z.eqb_neq; exact Hu).
  replace (L mod 2 ^ 64 =? fh_contentSize h) with false by (symmetry; apply Z.eqb_neq; exact HL).
  exact Er.
Qed.

End Bhdr.

(* ---------- checkChecksum ---------- *)

Lemma ck_body (fs1: fstate) (ts: tstate) (o: outarr) (u: list Z) (n: Z) (fh: frame_header) (d: dstate XS)
    (mem: list Z) (v: bool) (out: list Z) :
  drel fh d (oa_base o) fs1 ts -> fs_stage fs1 = Vint (Int.repr 5) ->
  fs_validateChecksum fs1 = Vint (Int.repr (if v then 1 else 0)) -> (v = true -> fs_xxh fs1 = Some out) ->
  d_check XS d = v /\ (v = true -> d_out XS d = out) /\
  d_body fh d mem (oa_d o) (oa_cap o) u n =
    if v && negb (le_field u 0 4 =? xxh64 out 0 mod 2 ^ 32) then None
    else Some (d_goto XS d DS_getFrameHeaderSize 0, mem, 0).
Proof.
  intros Hd Es Ev Ex. assert (Ds: d_stage XS d = 5) by (apply (drel_stage _ _ _ _ _ _ Hd Es); lia).
  pose proof Hd as Hd0. drel_d Hd0.
  destruct (Hptr ltac:(rewrite Ds; unfold DS_decodeBlockHeader, DS_checkChecksum; lia)) as (_ & _ & Vc & Xx & _).
  assert (Ec: d_check XS d = v).
  { rewrite Ev in Vc. destruct v, (d_check XS d); auto; apply vint_small_inj in Vc; rep_lia. }
  assert (Eo: v = true -> d_out XS d = out).
  { intros Hv. pose proof Ec as Ec1. rewrite Hv in Ec1, Ex. rewrite (Xx Ec1) in Ex. specialize (Ex eq_refl). congruence. }
  split; [exact Ec |]. split; [exact Eo |].
  unfold d_body. rewrite Ds. cbn [Z.eqb Pos.eqb orb]. unfold DS_decodeBlockHeader, DS_decompressBlock,
    DS_decompressLastBlock, DS_checkChecksum. cbn [Z.eqb Pos.eqb orb]. rewrite Ec.
  destruct v; [rewrite (Eo eq_refl) |]; reflexivity.
Qed.

Lemma cx_ck_bad (fs1: fstate) (ts: tstate) (o: outarr) (u: list Z) (n r: Z) (oc': list val) (fs': fstate)
    (tabs': option tstate) (out: list Z) :
  fs_stage fs1 = Vint (Int.repr 5) -> fs_validateChecksum fs1 = Vint (Int.repr 1) -> fs_xxh fs1 = Some out ->
  le_field u 0 4 <> xxh64 out 0 mod 2 ^ 32 -> is_error_code r = true -> cont_exact1 fs1 ts o u n r oc' fs' tabs'.
Proof.
  intros Es Ev Ex Hne Er fh d mem Hd _ _ _.
  destruct (ck_body fs1 ts o u n fh d mem true out Hd Es Ev (fun _ => Ex)) as (_ & _ & ->).
  replace (le_field u 0 4 =? xxh64 out 0 mod 2 ^ 32) with false by (symmetry; apply Z.eqb_neq; exact Hne).
  exact Er.
Qed.

Lemma cx_ck_ok (fs1: fstate) (ts: tstate) (o: outarr) (u: list Z) (n: Z) (fs': fstate) (v: bool) (out: list Z) :
  fs_stage fs1 = Vint (Int.repr 5) -> fs_validateChecksum fs1 = Vint (Int.repr (if v then 1 else 0)) ->
  (v = true -> fs_xxh fs1 = Some out) -> (v = true -> le_field u 0 4 = xxh64 out 0 mod 2 ^ 32) ->
  fs_keep fs1 fs' -> fs_stage fs' = Vint (Int.repr 0) -> fs_expected fs' = Vlong (Int64.repr 0) ->
  cont_exact1 fs1 ts o u n 0 (oa_c o) fs' (Some ts).
Proof.
  intros Es Ev Ex Hok K Fs Fe fh d mem Hd Hm _ _.
  destruct (ck_body fs1 ts o u n fh d mem v out Hd Es Ev Ex) as (_ & _ & ->).
  assert (Ds: d_stage XS d = 5) by (apply (drel_stage _ _ _ _ _ _ Hd Es); lia).
  replace (v && negb (le_field u 0 4 =? xxh64 out 0 mod 2 ^ 32)) with false
    by (destruct v; auto; rewrite (Hok eq_refl), Z.eqb_refl; reflexivity).
  split; [reflexivity |]. split; [exact Hm |]. exists ts. split; [reflexivity |].
  pose proof Hd as Hd0. drel_d Hd0.
  apply (drel_goto fh d (oa_base o) fs1 ts); auto; cbn; try reflexivity; try lia.
  - unfold DS_getFrameHeaderSize, DS_skipFrame; lia.
  - unfold DS_decodeBlockHeader, DS_getFrameHeaderSize; lia.
  - unfold DS_getFrameHeaderSize, DS_decompressBlock, DS_decompressLastBlock; lia.
Qed.

(* ---------- skipFrame ---------- *)

Lemma cx_skip (fs1: fstate) (ts: tstate) (o: outarr) (u: list Z) (n: Z) (fs': fstate) :
  fs_stage fs1 = Vint (Int.repr 7) -> fs_keep fs1 fs' -> fs_stage fs' = Vint (Int.repr 0) ->
  fs_expected fs' = Vlong (Int64.repr 0) -> cont_exact1 fs1 ts o u n 0 (oa_c o) fs' (Some ts).
Proof.
  intros Es K Fs Fe fh d mem Hd Hm _ _.
  assert (Ds: d_stage XS d = 7) by (apply (drel_stage _ _ _ _ _ _ Hd Es); lia).
  unfold d_body. rewrite Ds. cbn - [d_goto].
  split; [reflexivity |]. split; [exact Hm |]. exists ts. split; [reflexivity |].
  pose proof Hd as Hd0. drel_d Hd0.
  apply (drel_goto fh d (oa_base o) fs1 ts); auto; cbn; try reflexivity; try lia.
  - unfold DS_getFrameHeaderSize, DS_skipFrame; lia.
  - unfold DS_decodeBlockHeader, DS_getFrameHeaderSize; lia.
  - unfold DS_getFrameHeaderSize, DS_decompressBlock, DS_decompressLastBlock; lia.
Qed.
