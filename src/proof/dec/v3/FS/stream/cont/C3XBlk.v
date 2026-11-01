(* ZSTD_decompressContinue exactly: the block stages.  What follows the block decoders (the size check against
   Block_Maximum_Size, decodedSize, the checksum's state, previousDstEnd, the end of the block or of the frame) as plain
   lemmas the body's proof applies at each return, from the block decoders' exact outcome (C3XDefs.bres_exact). *)
Require Import Zstd.proof.dec.v3.FS.stream.S3Specs.
Require Import Zstd.proof.dec.v3.FS.stream.cont.C3Base.
Require Import Zstd.proof.dec.v3.FS.stream.cont.C3XDefs.
Require Import Zstd.proof.dec.v3.FS.stream.cont.C3XKit.
Require Import Zstd.proof.dec.v3.FS.stream.cont.C3XHdr.
Require Import Zstd.proof.model.ExStream.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

Lemma slice_sublist (l: list Z) i k : 0 <= i -> 0 <= k -> slice l i k = sublist i (i + k) l.
Proof. intros Hi Hk. unfold slice, sublist. rewrite skipn_firstn_comm. f_equal. lia. Qed.

Lemma zbytes_slice (mem: list Z) i k :
  0 <= i -> 0 <= k -> i + k <= Zlength mem -> zbytes (slice mem i k) = sublist i (i + k) (zbytes mem).
Proof. intros. rewrite slice_sublist by lia. rewrite sublist_map. reflexivity. Qed.

Lemma slice_len (mem: list Z) i k : 0 <= i -> 0 <= k -> i + k <= Zlength mem -> Zlength (slice mem i k) = k.
Proof. intros. rewrite slice_sublist by lia. rewrite Zlength_sublist by lia. lia. Qed.

Lemma slice_bytes (mem: list Z) i k : bytes_ok mem -> bytes_ok (slice mem i k).
Proof. intros Hb. unfold slice. apply Forall_firstn, Forall_skipn, Hb. Qed.

(* the frame state after a block of sz bytes written at dst, on both sides *)
Lemma drel_blk fh d ob fs1 ts e mem' dst sz st2 e2 ts' fs' L :
  drel fh d ob fs1 ts -> (d_stage XS d = 3 \/ d_stage XS d = 4) -> ts_x ts' = e ->
  ExBlockBytes.xh_good (ExBlock.x_huf ExHuf.xhuf e) ->
  bytes_ok (slice mem' dst sz) -> Zlength (slice mem' dst sz) = sz -> 0 <= dst -> 0 <= sz ->
  dst + sz <= Ptrofs.max_unsigned ->
  fs_decodedSize fs1 = Vlong (Int64.repr L) ->
  fs_fParams fs' = fs_fParams fs1 -> fs_isFrameDecompression fs' = fs_isFrameDecompression fs1 ->
  fs_stage fs' = Vint (Int.repr st2) -> fs_expected fs' = vlong e2 ->
  fs_bType fs' = fs_bType fs1 -> fs_rleSize fs' = fs_rleSize fs1 ->
  fs_decodedSize fs' = Vlong (Int64.repr (L + sz)) ->
  fs_validateChecksum fs' = fs_validateChecksum fs1 ->
  (d_check XS d = true -> fs_xxh fs' = Some (d_out XS d ++ slice mem' dst sz)) ->
  fs_previousDstEnd fs' = offset_val (dst + sz) ob -> fs_prefixStart fs' = fs_prefixStart fs1 ->
  fs_virtualStart fs' = fs_virtualStart fs1 -> fs_dictEnd fs' = fs_dictEnd fs1 ->
  fs_gpDictCopy fs' = Vint (Int.repr 0) ->
  0 <= st2 <= DS_skipFrame -> 0 <= e2 <= Int64.max_unsigned ->
  drel fh (mkD XS st2 e2 (d_btype XS d) (d_rle XS d) (d_out XS d ++ slice mem' dst sz) (d_check XS d) e
             (Some (dst + sz)) (d_pfx XS d) (d_ds XS d) (d_de XS d)) ob fs' ts'.
Proof.
  intros H Hs Ets Hxh Bs Ls Hd Hz Hm EL F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 F14 R1 R2.
  pose proof H as H0. drel_d H0.
  destruct (Hptr ltac:(unfold DS_decodeBlockHeader, DS_checkChecksum; lia))
    as (Dd & Bo & Vc & Xx & Ppe & Pps & Pde & Pvs & Pgp).
  destruct (Hblk ltac:(unfold DS_decompressBlock, DS_decompressLastBlock; lia)) as [Bt Br].
  unfold drel; cbn [d_stage d_expected d_btype d_rle d_out d_check d_ent d_prev d_pfx d_ds d_de].
  rewrite F1, F2, F3, F4, F5, F6, F7, F8, F10, F11, F12, F13, F14.
  split; [exact Ep |]. split; [exact Rc |]. split; [exact Rb |]. split; [exact Rk |].
  split; [exact R1 |]. split; [exact R2 |]. split; [exact Rbt |]. split; [exact Rrl |].
  split.
  { intros x [E | [E | [E | E]]]; [inversion E; subst; lia | apply Roff; auto .. ]. }
  split; [exact Hxh |]. split; [exact Ets |]. split; [exact Rfd |]. split; [reflexivity |]. split; [reflexivity |].
  split; [intros _; split; [exact Bt | exact Br] |].
  intros _. split.
  { rewrite Dd in EL. unfold vlong in *. rewrite Zlength_app, Ls.
    assert (E': Int64.repr (Zlength (d_out XS d)) = Int64.repr L) by congruence.
    rewrite <- !add64_repr, E'. reflexivity. }
  split; [apply Forall_app; split; [exact Bo | exact Bs] |].
  split; [exact Vc |]. split; [exact F9 |].
  split; [reflexivity |]. split; [exact Pps |]. split; [exact Pde |].
  split; [rewrite Pvs; reflexivity |]. reflexivity.
Qed.

Lemma is_error_63 k : 0 <= k <= 2 ^ 63 -> is_error_code k = false.
Proof. intros. unfold is_error_code. apply Z.ltb_ge. lia. Qed.

Lemma zb_inj (a b: list Z) : bytes_ok a -> bytes_ok b -> zbytes a = zbytes b -> a = b.
Proof.
  revert b. induction a as [ | x a IH]; intros [ | y b] Ha Hb E; simpl in E; try discriminate; auto.
  assert (Hx: Int.repr x = Int.repr y) by congruence. assert (Ht: zbytes a = zbytes b) by congruence.
  inv Ha. inv Hb. f_equal; [| apply IH; auto].
  apply (f_equal Int.unsigned) in Hx. unfold is_byte in *. rewrite !Int.unsigned_repr in Hx by rep_lia. exact Hx.
Qed.

(* ---------- after the block decoders ---------- *)

Section Tail.
Variables (fs1: fstate) (ts: tstate) (o: outarr) (u: list Z) (n: Z) (h: frame_header) (bsm st: Z).
Hypothesis Hst: fs_stage fs1 = Vint (Int.repr st).
Hypothesis Hst34: st = 3 \/ st = 4.
Hypothesis Hfp: fs_fParams fs1 = fh_val (fh_adj h bsm).
Hypothesis Hcs: 0 <= fh_contentSize h <= Int64.max_unsigned.
Hypothesis Hbsm: 0 <= bsm <= ZSTD_BLOCKSIZE_MAX.
Hypothesis Hck: fh_checksumFlag h = 0 \/ fh_checksumFlag h = 1.
Hypothesis Ho: 0 <= oa_d o /\ 0 <= oa_cap o /\ oa_d o + oa_cap o <= oa_N o /\ oa_N o <= 2 ^ 63 - 1 /\
               Zlength (oa_c o) = oa_N o.

Lemma blk_body fh d mem :
  drel fh d (oa_base o) fs1 ts ->
  d_stage XS d = st /\ fh_contentSize fh = fh_contentSize h /\ fh_blockSizeMax fh = bsm /\
  fh_checksumFlag fh = fh_checksumFlag h /\
  d_body fh d mem (oa_d o) (oa_cap o) u n =
    match d_bres fh d mem (oa_d o) (oa_cap o) u n with
    | None => None
    | Some (e, mem', sz, ex) =>
        if sz >? bsm then None else
        let d1 := mkD XS st ex (d_btype XS d) (d_rle XS d) (d_out XS d ++ slice mem' (oa_d o) sz) (d_check XS d) e
                      (Some (oa_d o + sz)) (d_pfx XS d) (d_ds XS d) (d_de XS d) in
        if ex >? 0 then Some (d1, mem', sz)
        else if st =? 4 then
          match d_end_frame XS fh d1 with Some d2 => Some (d2, mem', sz) | None => None end
        else Some (d_goto XS d1 DS_decodeBlockHeader ZSTD_blockHeaderSize, mem', sz)
    end.
Proof.
  intros Hd. assert (Ds: d_stage XS d = st) by (apply (drel_stage _ _ _ _ _ _ Hd Hst); lia).
  destruct (drel_fh _ _ _ _ _ _ _ Hd Hfp Hcs ltac:(unfold ZSTD_BLOCKSIZE_MAX in Hbsm; rep_lia)
              ltac:(destruct Hck as [-> | ->]; rep_lia)) as (F1 & F2 & F3).
  split; [exact Ds |]. split; [exact F1 |]. split; [exact F2 |]. split; [exact F3 |].
  unfold d_body. rewrite Ds, F2. destruct Hst34 as [-> | ->]; reflexivity.
Qed.

(* the block decoder failed *)
Lemma cx_tail_err r oc' tso e' r2 oc2 fs2 tabs2 :
  bres_exact fs1 ts o u n r oc' tso e' -> is_error_code r = true -> r2 = r ->
  cont_exact1 fs1 ts o u n r2 oc2 fs2 tabs2.
Proof using All.
  intros Hb Er -> fh d mem Hd Hm Hbm Hne. destruct (blk_body fh d mem Hd) as (_ & _ & _ & _ & ->).
  specialize (Hb fh d mem Hd Hm Hbm Hne).
  destruct (d_bres fh d mem (oa_d o) (oa_cap o) u n) as [[[[e mem'] sz] ex] |]; [| exact Er].
  destruct Hb as (-> & Hsz & _). rewrite is_error_63 in Er by lia. discriminate.
Qed.

(* the block exceeds Block_Maximum_Size *)
Lemma cx_tail_big r oc' tso e' r2 oc2 fs2 tabs2 :
  bres_exact fs1 ts o u n r oc' tso e' -> bsm < r -> is_error_code r2 = true ->
  cont_exact1 fs1 ts o u n r2 oc2 fs2 tabs2.
Proof using All.
  intros Hb Hr Er fh d mem Hd Hm Hbm Hne. destruct (blk_body fh d mem Hd) as (_ & _ & _ & _ & ->).
  specialize (Hb fh d mem Hd Hm Hbm Hne).
  destruct (d_bres fh d mem (oa_d o) (oa_cap o) u n) as [[[[e mem'] sz] ex] |]; [| exact Er].
  destruct Hb as (Er0 & _). subst r. replace (sz >? bsm) with true by lia. exact Er.
Qed.

(* the block's content and the frame state after it *)
Lemma blk_content (fh: frame_header) (d: dstate XS) (mem: list Z) (r: Z) (oc': list val) (ts': tstate) (e': Z)
    (cnt: list Z) (e: XS) (mem': list Z) (sz ex: Z) :
  drel fh d (oa_base o) fs1 ts -> oa_c o = zbytes mem ->
  (r = sz /\ 0 <= sz <= oa_cap o /\ oc' = zbytes mem' /\ Zlength mem' = Zlength mem /\ bytes_ok mem' /\
   e' = ex /\ ExBlockBytes.xh_good (ExBlock.x_huf ExHuf.xhuf e) /\
   exists ts2, Some ts' = Some ts2 /\ ts_x ts2 = e) ->
  Zlength cnt = r -> bytes_ok cnt -> sublist (oa_d o) (oa_d o + r) oc' = zbytes cnt ->
  r = sz /\ oc' = zbytes mem' /\ e' = ex /\ ts_x ts' = e /\ ExBlockBytes.xh_good (ExBlock.x_huf ExHuf.xhuf e) /\
  slice mem' (oa_d o) sz = cnt /\ Zlength (slice mem' (oa_d o) sz) = sz /\ 0 <= sz <= oa_cap o.
Proof.
  intros Hd Hm (-> & Hsz & -> & Lm & Bm & -> & Hxh & ts2 & Et & Ex) Lc Bc Hsub.
  injection Et as <-.
  assert (LN: Zlength mem = oa_N o) by (rewrite <- (proj2 (proj2 (proj2 (proj2 Ho)))), Hm, Zlength_map; reflexivity).
  destruct Ho as (H1 & H2 & H3 & H4 & H5).
  assert (Es: slice mem' (oa_d o) sz = cnt).
  { apply zb_inj; [apply slice_bytes, Bm | exact Bc |]. rewrite zbytes_slice by lia. exact Hsub. }
  repeat split; auto; try lia. rewrite slice_len by lia. reflexivity.
Qed.

Lemma cx_tail_ok r oc' ts' e' cnt out (v: bool) fs' st2 e2 :
  bres_exact fs1 ts o u n r oc' (Some ts') e' -> is_error_code r = false -> r <= bsm -> 0 <= e' <= Int64.max_unsigned ->
  Zlength cnt = r -> bytes_ok cnt -> sublist (oa_d o) (oa_d o + r) oc' = zbytes cnt ->
  fs_decodedSize fs1 = Vlong (Int64.repr (Zlength out)) ->
  fs_validateChecksum fs1 = Vint (Int.repr (if v then 1 else 0)) -> (v = true -> fs_xxh fs1 = Some out) ->
  fs_fParams fs' = fs_fParams fs1 -> fs_isFrameDecompression fs' = fs_isFrameDecompression fs1 ->
  fs_stage fs' = Vint (Int.repr st2) -> fs_expected fs' = Vlong (Int64.repr e2) ->
  fs_bType fs' = fs_bType fs1 -> fs_rleSize fs' = fs_rleSize fs1 ->
  fs_decodedSize fs' = Vlong (Int64.repr (Zlength out + r)) ->
  fs_validateChecksum fs' = fs_validateChecksum fs1 ->
  fs_xxh fs' = (if v then Some (out ++ cnt) else fs_xxh fs1) ->
  fs_previousDstEnd fs' = offset_val (oa_d o + r) (oa_base o) -> fs_prefixStart fs' = fs_prefixStart fs1 ->
  fs_virtualStart fs' = fs_virtualStart fs1 -> fs_dictEnd fs' = fs_dictEnd fs1 ->
  fs_gpDictCopy fs' = Vint (Int.repr 0) ->
  (0 < e' -> st2 = st /\ e2 = e') ->
  (e' = 0 -> st = 3 -> st2 = 2 /\ e2 = 3) ->
  (e' = 0 -> st = 4 ->
     (fh_contentSize h = ZSTD_CONTENTSIZE_UNKNOWN \/ (Zlength out + r) mod 2 ^ 64 = fh_contentSize h) /\
     (if fh_checksumFlag h =? 1 then st2 = 5 /\ e2 = 4 else st2 = 0 /\ e2 = 0)) ->
  cont_exact1 fs1 ts o u n r oc' fs' (Some ts').
Proof using All.
  intros Hb Er Hrb He' Lc Bc Hsub Ed Ev Ex F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 F14 Hgo Hb3 Hb4
    fh d mem Hd Hm Hbm Hne.
  destruct (blk_body fh d mem Hd) as (Ds & G1 & G2 & G3 & ->).
  specialize (Hb fh d mem Hd Hm Hbm Hne).
  destruct (d_bres fh d mem (oa_d o) (oa_cap o) u n) as [[[[e mem'] sz] ex] |] eqn:Eb.
  2: { rewrite Er in Hb. discriminate. }
  destruct (blk_content fh d mem r oc' ts' e' cnt e mem' sz ex Hd Hm Hb Lc Bc Hsub)
    as (-> & -> & -> & Ets & Hxh & Esl & Lsl & Hsz).
  replace (sz >? bsm) with false by lia. cbv zeta.
  pose proof Hd as Hd0. drel_d Hd0.
  destruct (Hptr ltac:(rewrite Ds; unfold DS_decodeBlockHeader, DS_checkChecksum; lia))
    as (Dd & Bo & Vc & Xx & _).
  assert (Ec: d_check XS d = v).
  { rewrite Ev in Vc. destruct v, (d_check XS d); auto; apply vint_small_inj in Vc; rep_lia. }
  assert (Eo: v = true -> d_out XS d = out).
  { intros Hv. pose proof Ec as Ec1. rewrite Hv in Ec1, Ex. rewrite (Xx Ec1) in Ex. specialize (Ex eq_refl). congruence. }
  destruct Ho as (H1 & H2 & H3 & H4 & H5).
  assert (G: forall st3 e3, 0 <= st3 <= 7 -> 0 <= e3 <= Int64.max_unsigned -> st2 = st3 -> e2 = e3 ->
             drel fh (mkD XS st3 e3 (d_btype XS d) (d_rle XS d) (d_out XS d ++ slice mem' (oa_d o) sz)
                        (d_check XS d) e (Some (oa_d o + sz)) (d_pfx XS d) (d_ds XS d) (d_de XS d))
               (oa_base o) fs' ts').
  { intros st3 e3 R1 R2 -> ->.
    apply (drel_blk fh d (oa_base o) fs1 ts e mem' (oa_d o) sz st3 e3 ts' fs' (Zlength out)); auto; try rep_lia.
    all: first [ apply slice_bytes; destruct Hb as (_ & _ & _ & _ & Bm & _); exact Bm
               | unfold DS_skipFrame; lia
               | intros Hc; rewrite F9; rewrite <- Ec, Hc; rewrite (Eo ltac:(rewrite <- Ec; exact Hc)), Esl; reflexivity ]. }
  assert (Hlen: Zlength (d_out XS d ++ slice mem' (oa_d o) sz) mod 2 ^ 64 = (Zlength out + sz) mod 2 ^ 64).
  { rewrite Zlength_app, Lsl. rewrite Dd in Ed. apply vlong_mod in Ed.
    rewrite Zplus_mod, Ed, <- Zplus_mod. reflexivity. }
  destruct (Z.gtb_spec ex 0) as [Hx | Hx]; cbv beta iota.
  - destruct (Hgo Hx) as [-> ->]. cbn [cx_match]. split; [reflexivity |]. split; [reflexivity |].
    exists ts'. split; [reflexivity |]. apply G; auto; try (destruct Hst34 as [-> | ->]; lia); rep_lia.
  - assert (ex = 0) as -> by lia.
    destruct Hst34 as [-> | ->]; cbn [Z.eqb Pos.eqb]; cbv beta iota.
    + destruct (Hb3 eq_refl eq_refl) as [-> ->]. cbn [cx_match]. split; [reflexivity |]. split; [reflexivity |].
      exists ts'. split; [reflexivity |]. unfold d_goto. cbn [d_btype d_rle d_out d_check d_ent d_prev d_pfx d_ds d_de].
      apply G; auto; unfold DS_decodeBlockHeader, ZSTD_blockHeaderSize; rep_lia.
    + destruct (Hb4 eq_refl eq_refl) as [Hcs' Hfin].
      match goal with |- context [d_end_frame XS fh ?D] =>
        rewrite (end_frame_eq fh D h (Zlength out + sz) G1 G3 Hlen) end.
      replace (negb (fh_contentSize h =? ZSTD_CONTENTSIZE_UNKNOWN) &&
               negb ((Zlength out + sz) mod 2 ^ 64 =? fh_contentSize h)) with false
        by (destruct Hcs' as [-> | ->]; rewrite Z.eqb_refl; [reflexivity | cbn [negb]; destruct (negb _); reflexivity]).
      cbv beta iota.
      destruct (fh_checksumFlag h =? 1); destruct Hfin as [-> ->]; cbn [cx_match];
        (split; [reflexivity |]; split; [reflexivity |]; exists ts'; split; [reflexivity |];
         unfold d_goto; cbn [d_btype d_rle d_out d_check d_ent d_prev d_pfx d_ds d_de];
         apply G; auto; unfold DS_checkChecksum, DS_getFrameHeaderSize; rep_lia).
Qed.

(* the last block whose frame's content size disagrees *)
Lemma cx_tail_fcs (r: Z) (oc': list val) (ts': tstate) (e': Z) (out: list Z) (r2: Z) (oc2: list val) (fs2: fstate)
    (tabs2: option tstate) :
  bres_exact fs1 ts o u n r oc' (Some ts') e' -> is_error_code r = false -> r <= bsm -> e' = 0 -> st = 4 ->
  fs_decodedSize fs1 = Vlong (Int64.repr (Zlength out)) ->
  fh_contentSize h <> ZSTD_CONTENTSIZE_UNKNOWN -> (Zlength out + r) mod 2 ^ 64 <> fh_contentSize h ->
  is_error_code r2 = true -> cont_exact1 fs1 ts o u n r2 oc2 fs2 tabs2.
Proof using All.
  intros Hb Er Hrb He0 Hs4 Ed Hu Hne2 Er2 fh d mem Hd Hm Hbm Hne.
  destruct (blk_body fh d mem Hd) as (Ds & G1 & G2 & G3 & ->). rewrite Hs4.
  specialize (Hb fh d mem Hd Hm Hbm Hne).
  destruct (d_bres fh d mem (oa_d o) (oa_cap o) u n) as [[[[e mem'] sz] ex] |] eqn:Eb; [| exact Er2].
  destruct Hb as (-> & Hsz & _ & Lm & _ & Ex0 & _). assert (ex = 0) as -> by lia.
  replace (sz >? bsm) with false by lia. cbv zeta. cbn [Z.gtb Z.compare]. cbv beta iota.
  cbn [Z.eqb Pos.eqb]. cbv beta iota.
  pose proof Hd as Hd0. drel_d Hd0.
  destruct (Hptr ltac:(rewrite Ds, Hs4; unfold DS_decodeBlockHeader, DS_checkChecksum; lia)) as (Dd & _).
  destruct Ho as (H1 & H2 & H3 & H4 & H5).
  assert (LN: Zlength mem = oa_N o) by (rewrite <- H5, Hm, Zlength_map; reflexivity).
  assert (Hlen: Zlength (d_out XS d ++ slice mem' (oa_d o) sz) mod 2 ^ 64 = (Zlength out + sz) mod 2 ^ 64).
  { rewrite Zlength_app, slice_len by lia. rewrite Dd in Ed. apply vlong_mod in Ed.
    rewrite Zplus_mod, Ed, <- Zplus_mod. reflexivity. }
  match goal with |- context [d_end_frame XS fh ?D] =>
    rewrite (end_frame_eq fh D h (Zlength out + sz) G1 G3 Hlen) end.
  replace (fh_contentSize h =? ZSTD_CONTENTSIZE_UNKNOWN) with false by (symmetry; apply Z.eqb_neq; exact Hu).
  replace ((Zlength out + sz) mod 2 ^ 64 =? fh_contentSize h) with false by (symmetry; apply Z.eqb_neq; exact Hne2).
  exact Er2.
Qed.

End Tail.
