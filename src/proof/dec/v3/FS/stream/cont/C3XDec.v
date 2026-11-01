(* ZSTD_decompressContinue exactly: the block decoders of the block stages (ZSTD_copyRawBlock, ZSTD_setRleBlock,
   ZSTD_decompressBlock_internal) against the model's (C3XDefs.d_bres).  The compressed block: DecIface.block_exact at
   the whole ring (region base 0), its history being the model's d_hist (an empty extDict anywhere, C3XModel.xblock_noext);
   without room, at the empty window, whose outcome is the model's at the ring (C3XModel.xblock_cap0). *)
Require Import Zstd.proof.dec.v3.FS.stream.S3Specs.
Require Import Zstd.proof.dec.v3.FS.stream.cont.C3Base.
Require Import Zstd.proof.dec.v3.FS.stream.cont.C3XModel.
Require Import Zstd.proof.dec.v3.FS.stream.cont.C3XDefs.
Require Import Zstd.proof.dec.v3.FS.stream.cont.C3XKit.
Require Import Zstd.proof.dec.v3.FS.stream.cont.C3XBlk.
Require Import Zstd.proof.model.ExStream Zstd.proof.model.ExBlockWritten Zstd.proof.model.ExBlockBytes.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

Lemma mem_write_zbytes (mem bs: list Z) d :
  0 <= d -> d + Zlength bs <= Zlength mem ->
  put_bytes (zbytes mem) d bs = zbytes (mem_write mem d bs).
Proof.
  intros Hd Hl. unfold put_bytes, mem_write. rewrite Zlength_map, !map_app.
  f_equal.
  - rewrite sublist_map. f_equal.
  - f_equal. rewrite sublist_map. f_equal. unfold sublist. rewrite firstn_same by (rewrite Zlength_correct; lia).
    reflexivity.
Qed.

Lemma mem_write_len (mem bs: list Z) d :
  0 <= d -> d + Zlength bs <= Zlength mem -> Zlength (mem_write mem d bs) = Zlength mem.
Proof.
  intros Hd Hl. unfold mem_write. rewrite !Zlength_app.
  rewrite !Zlength_correct, firstn_length, skipn_length. rewrite !Zlength_correct in Hl. lia.
Qed.

Lemma mem_write_bytes (mem bs: list Z) d : bytes_ok mem -> bytes_ok bs -> bytes_ok (mem_write mem d bs).
Proof.
  intros Hm Hb. unfold mem_write. apply Forall_app; split; [apply Forall_firstn, Hm |].
  apply Forall_app; split; [exact Hb | apply Forall_skipn, Hm].
Qed.

Section Dec.
Variables (fs1: fstate) (ts: tstate) (o: outarr) (u: list Z) (n: Z) (st bt: Z).
Hypothesis Hst: fs_stage fs1 = Vint (Int.repr st).
Hypothesis Hst34: st = 3 \/ st = 4.
Hypothesis Hbt: fs_bType fs1 = Vint (Int.repr bt).
Hypothesis Hbt3: 0 <= bt <= 3.
Hypothesis Ho: 0 <= oa_d o /\ 0 <= oa_cap o /\ oa_d o + oa_cap o <= oa_N o /\ oa_N o <= 2 ^ 63 - 1 /\
               Zlength (oa_c o) = oa_N o.

Lemma bres_fields fh d :
  drel fh d (oa_base o) fs1 ts -> d_stage XS d = st /\ d_btype XS d = bt.
Proof.
  intros Hd. assert (Ds: d_stage XS d = st) by (apply (drel_stage _ _ _ _ _ _ Hd Hst); lia).
  split; [exact Ds |]. pose proof Hd as Hd0. drel_d Hd0.
  destruct (Hblk ltac:(rewrite Ds; unfold DS_decompressBlock, DS_decompressLastBlock; lia)) as [Bt _].
  rewrite Hbt in Bt. apply vint_small_inj in Bt; rep_lia.
Qed.

Lemma memlen mem : oa_c o = zbytes mem -> Zlength mem = oa_N o.
Proof. intros Hm. destruct Ho as (_ & _ & _ & _ & H5). rewrite <- H5, Hm, Zlength_map. reflexivity. Qed.

(* ZSTD_copyRawBlock: the piece of a raw block *)
Lemma bres_raw r oc' tso e' E :
  bt = 0 -> fs_expected fs1 = Vlong (Int64.repr E) -> 0 <= E <= Int64.max_unsigned ->
  Zlength u = n -> bytes_ok u ->
  (if n >? oa_cap o then is_error_code r = true
   else r = n /\ oc' = put_bytes (oa_c o) (oa_d o) u /\ tso = Some ts /\ e' = E - n) ->
  bres_exact fs1 ts o u n r oc' tso e'.
Proof using All.
  intros B0 Ee He Lu Bu Hc fh d mem Hd Hm Hbm Hne.
  destruct (bres_fields fh d Hd) as [Ds Db]. pose proof (memlen mem Hm) as LN.
  pose proof (drel_expected _ _ _ _ _ _ Hd Ee He) as De.
  pose proof Hd as Hd0. drel_d Hd0.
  unfold d_bres. rewrite Db, B0. cbn [Z.eqb]. cbv beta iota.
  destruct (n >? oa_cap o) eqn:Eg; [exact Hc |].
  destruct Hc as (-> & -> & -> & ->). destruct Ho as (H1 & H2 & H3 & H4 & H5).
  assert (Hn: n <= oa_cap o) by (rewrite Z.gtb_ltb, Z.ltb_ge in Eg; lia). pose proof (Zlength_nonneg u).
  split; [reflexivity |]. split; [lia |].
  split; [rewrite Hm; apply mem_write_zbytes; lia |].
  split; [apply mem_write_len; lia |]. split; [apply mem_write_bytes; auto |].
  split; [rewrite De; reflexivity |]. split; [exact Rxh |]. exists ts. split; [reflexivity | exact Rts].
Qed.

(* ZSTD_setRleBlock *)
Lemma bres_rle r oc' tso e' R :
  bt = 1 -> fs_rleSize fs1 = Vlong (Int64.repr R) -> 0 <= R <= Int64.max_unsigned ->
  1 <= Zlength u -> bytes_ok u ->
  (if R >? oa_cap o then is_error_code r = true
   else r = R /\ oc' = put_bytes (oa_c o) (oa_d o) (Zrepeat (Znth 0 u) R) /\ tso = Some ts /\ e' = 0) ->
  bres_exact fs1 ts o u n r oc' tso e'.
Proof using All.
  intros B1 Er HR Lu Bu Hc fh d mem Hd Hm Hbm Hne.
  destruct (bres_fields fh d Hd) as [Ds Db]. pose proof (memlen mem Hm) as LN.
  pose proof Hd as Hd0. drel_d Hd0.
  destruct (Hblk ltac:(rewrite Ds; unfold DS_decompressBlock, DS_decompressLastBlock; lia)) as [_ Br].
  rewrite Er in Br. unfold vlong in Br. apply vlong_inj in Br; auto. subst R.
  unfold d_bres. rewrite Db, B1. cbn [Z.eqb]. cbv beta iota.
  destruct (d_rle XS d >? oa_cap o) eqn:Eg; [exact Hc |].
  destruct Hc as (-> & -> & -> & ->). destruct Ho as (H1 & H2 & H3 & H4 & H5).
  assert (Hr: d_rle XS d <= oa_cap o) by (rewrite Z.gtb_ltb, Z.ltb_ge in Eg; lia).
  assert (Eb: Zrepeat (Znth 0 u) (d_rle XS d) = repeat (byte_at u 0) (Z.to_nat (d_rle XS d))).
  { unfold Zrepeat, byte_at. f_equal. }
  assert (Lr: Zlength (repeat (byte_at u 0) (Z.to_nat (d_rle XS d))) = d_rle XS d)
    by (rewrite Zlength_correct, repeat_length; lia).
  assert (Bb: bytes_ok (repeat (byte_at u 0) (Z.to_nat (d_rle XS d)))).
  { apply Forall_forall. intros x Hx. apply repeat_spec in Hx. subst x. unfold byte_at.
    destruct u as [ | a u']; [rewrite Zlength_nil in Lu; lia |]. inv Bu. exact H6. }
  split; [reflexivity |]. split; [lia |].
  split; [rewrite Hm, Eb; apply mem_write_zbytes; lia |].
  split; [apply mem_write_len; lia |]. split; [apply mem_write_bytes; auto |].
  split; [reflexivity |]. split; [exact Rxh |]. exists ts. split; [reflexivity | exact Rts].
Qed.

End Dec.

Lemma off_mod b ofs x y : offset_val x (Vptr b ofs) = offset_val y (Vptr b ofs) ->
  x mod Ptrofs.modulus = y mod Ptrofs.modulus.
Proof.
  intros E. simpl in E. assert (E1: Ptrofs.add ofs (Ptrofs.repr x) = Ptrofs.add ofs (Ptrofs.repr y)) by congruence.
  assert (E2: Ptrofs.repr x = Ptrofs.repr y).
  { rewrite <- (Ptrofs.add_zero_l (Ptrofs.repr x)), <- (Ptrofs.add_zero_l (Ptrofs.repr y)).
    rewrite <- (Ptrofs.add_neg_zero ofs), (Ptrofs.add_commut ofs (Ptrofs.neg ofs)), !Ptrofs.add_assoc, E1.
    reflexivity. }
  apply (f_equal Ptrofs.unsigned) in E2. rewrite !Ptrofs.unsigned_repr_eq in E2. exact E2.
Qed.

Lemma zlen_sublist_le {A} (l: list A) k : Zlength (sublist 0 k l) <= Zlength l.
Proof.
  unfold sublist. rewrite skipn_0, !Zlength_correct, firstn_length. lia.
Qed.

(* the region a compressed block returns over the whole ring is the ring *)
Lemma region_whole (mem mem2: list Z) (oc': list val) :
  Zlength mem <= Zlength mem2 -> Zlength oc' = Zlength mem ->
  sublist 0 (Zlength mem2) oc' = zbytes mem2 -> oc' = zbytes mem2 /\ Zlength mem2 = Zlength mem.
Proof.
  intros Hge Hl E. pose proof (zlen_sublist_le oc' (Zlength mem2)) as Hle.
  rewrite E, Zlength_map in Hle. assert (Eq: Zlength mem2 = Zlength mem) by lia.
  split; [| exact Eq]. rewrite <- E, Eq, <- Hl. symmetry. apply sublist_same; reflexivity.
Qed.

Lemma cong_eq x y M : 0 < M -> (x - y) mod M = 0 -> 0 <= x < M -> 0 <= y < M -> x = y.
Proof.
  intros HM E Hx Hy. apply Z.mod_divide in E; [| lia]. destruct E as [k Hk].
  destruct (Z.lt_trichotomy k 0) as [Hk0 | [Hk0 | Hk0]].
  - assert (k * M <= - M) by nia. lia.
  - subst k. lia.
  - assert (M <= k * M) by nia. lia.
Qed.

Section Comp.
Variables (fs1: fstate) (ts: tstate) (o: outarr) (u: list Z) (n: Z) (st: Z) (h: frame_header) (bsm: Z).
Hypothesis Hst: fs_stage fs1 = Vint (Int.repr st).
Hypothesis Hst34: st = 3 \/ st = 4.
Hypothesis Hbt: fs_bType fs1 = Vint (Int.repr 2).
Hypothesis Ho: 0 <= oa_d o /\ 0 <= oa_cap o /\ oa_d o + oa_cap o <= oa_N o /\ oa_N o <= 2 ^ 63 - 1 /\
               Zlength (oa_c o) = oa_N o.
Hypothesis Hfp: fs_fParams fs1 = fh_val (fh_adj h bsm).
Hypothesis Hcs: 0 <= fh_contentSize h <= Int64.max_unsigned.
Hypothesis Hbsm: 0 <= bsm <= ZSTD_BLOCKSIZE_MAX.
Hypothesis Hck: fh_checksumFlag h = 0 \/ fh_checksumFlag h = 1.
Hypothesis Bu: bytes_ok u.
Hypothesis Bl: bytes_ok (ts_lxb ts).

Lemma comp_fields fh d mem :
  drel fh d (oa_base o) fs1 ts -> oa_c o = zbytes mem ->
  d_stage XS d = st /\ d_btype XS d = 2 /\ fh_blockSizeMax fh = bsm /\ d_ent XS d = ts_x ts /\
  Zlength mem = oa_N o /\ ExBlockBytes.xh_good (ExBlock.x_huf ExHuf.xhuf (ts_x ts)) /\
  d_bres fh d mem (oa_d o) (oa_cap o) u n =
    let '(ps, ds, de) := d_hist XS d (oa_d o) in
    match Exact.xblock (ts_x ts) mem ps (oa_d o) ds de u bsm (oa_cap o) true with
    | Some (e, mem', sz) => Some (e, mem', sz, 0)
    | None => None
    end.
Proof.
  intros Hd Hm.
  destruct (bres_fields fs1 ts o st 2 Hst Hst34 Hbt ltac:(lia) fh d Hd) as [Ds Db].
  destruct (drel_fh _ _ _ _ _ _ _ Hd Hfp Hcs ltac:(unfold ZSTD_BLOCKSIZE_MAX in Hbsm; rep_lia)
              ltac:(destruct Hck as [-> | ->]; rep_lia)) as (_ & F2 & _).
  pose proof Hd as Hd0. drel_d Hd0.
  split; [exact Ds |]. split; [exact Db |]. split; [exact F2 |]. split; [symmetry; exact Rts |].
  split; [apply (memlen o Ho mem Hm) |]. split; [rewrite Rts; exact Rxh |].
  unfold d_bres. rewrite Db, F2, <- Rts. reflexivity.
Qed.

Lemma bytes_of_comp (st0 st2: XS) mem mem2 ps op ds de cap sz :
  bytes_ok mem -> ExBlock.x_lxb ExHuf.xhuf st0 = ts_lxb ts -> ExBlockBytes.xh_good (ExBlock.x_huf ExHuf.xhuf st0) ->
  Exact.xblock st0 mem ps op ds de u bsm cap true = Some (st2, mem2, sz) ->
  bytes_ok mem2 /\ ExBlockBytes.xh_good (ExBlock.x_huf ExHuf.xhuf st2).
Proof.
  intros Bm El Hx E. destruct (xblock_bytes st0 st2 mem mem2 ps op ds de u bsm cap true sz Bm Bu
                                 ltac:(rewrite El; exact Bl) Hx E) as (B1 & _ & B3).
  split; [exact B1 | exact B3].
Qed.

(* with room: the ring is the region, the history is the model's *)
Lemma bres_comp r oc' tso (i: inwin) (hh: hctx) b ofs ps ex :
  0 < oa_cap o -> oa_base o = Vptr b ofs ->
  lay_fields fs1 (HL_seg (oa_base o) ps (oa_d o) ex) -> layout_ok_seg ps ex (oa_N o) -> ps <= oa_d o ->
  (match ex with ExtSep _ _ _ _ _ _ => False | _ => True end) ->
  iw_s i = u -> hc_ext hh = ex -> hc_ps hh = ps ->
  block_exact ts o i hh bsm 1 r oc' tso -> Zlength oc' = oa_N o ->
  bres_exact fs1 ts o u n r oc' tso 0.
Proof using All.
  intros Hc0 Eb Lf Lok Hpsd Hex Eu Eh Ep Hbe Loc fh d mem Hd Hm Hbm Hne.
  destruct (comp_fields fh d mem Hd Hm) as (Ds & Db & F2 & Ent & LN & Hxh & ->).
  pose proof Hd as Hd0. drel_d Hd0.
  destruct (Hptr ltac:(rewrite Ds; unfold DS_decodeBlockHeader, DS_checkChecksum; destruct Hst34; lia))
    as (_ & _ & _ & _ & _ & Pps & Pde & Pvs & _).
  destruct Ho as (H1 & H2 & H3 & H4 & H5).
  destruct Lf as (_ & _ & Hps & _ & Pps' & Pvs' & Hde). rewrite Eb in *.
  destruct Lok as (Lps & Lel & Lm).
  assert (Epfx: d_pfx XS d = Some ps).
  { apply (ring_ptr_off b ofs); [intros x Ex; apply Roff; right; left; exact Ex | rep_lia |].
    rewrite <- Pps, Pps'. reflexivity. }
  (* the model's history and the C's region: the same, up to the place of an empty extDict *)
  assert (Hreg: exists a c, hc_region hh 0 = Some (ps, a, c) /\ 0 <= a /\ a <= c <= oa_N o /\
            (let '(p', ds', de') := d_hist XS d (oa_d o) in
             Exact.xblock (ts_x ts) mem p' (oa_d o) ds' de' u bsm (oa_cap o) true) =
            Exact.xblock (ts_x ts) mem ps (oa_d o) a c u bsm (oa_cap o) true).
  { unfold hc_region. rewrite Eh, Ep. unfold d_hist. rewrite Epfx.
    destruct ex as [ | e1 elen | sh eb en ec e1 elen]; [| | contradiction].
    - assert (Ede: d_de XS d = None) by (apply (ring_ptr_null b ofs); rewrite <- Pde; exact Hde).
      exists ps, ps. rewrite !Z.sub_0_r. split; [reflexivity |]. split; [lia |]. split; [lia |].
      rewrite Ede. destruct (d_ds XS d); apply xblock_noext.
    - destruct Hde as [Hde He1]. cbn [ext_len] in Lel, Pvs'.
      assert (Ede: d_de XS d = Some e1).
      { apply (ring_ptr_off b ofs); [intros x Ex; apply Roff; right; right; right; exact Ex | rep_lia |].
        rewrite <- Pde, Hde. reflexivity. }
      exists (e1 - elen), e1. rewrite !Z.sub_0_r. split; [reflexivity |]. split; [lia |]. split; [lia |].
      rewrite Ede. unfold vstart_of in Pvs. rewrite Epfx, Ede in Pvs.
      destruct (d_ds XS d) as [a |] eqn:Eds.
      + assert (Ha: 0 <= a <= Ptrofs.max_unsigned) by (apply Roff; right; right; left; reflexivity).
        rewrite Pvs' in Pvs. apply off_mod in Pvs.
        assert (Ea: a = e1 - elen).
        { assert (PM: Ptrofs.modulus = 2 ^ 64) by reflexivity. assert (PX: Ptrofs.max_unsigned = 2 ^ 64 - 1) by reflexivity.
          rewrite PM in Pvs. rewrite PX in Ha.
          apply (cong_eq _ _ (2 ^ 64)); [lia | | lia | lia].
          replace (a - (e1 - elen)) with ((ps - (e1 - a)) - (ps - elen)) by lia.
          rewrite Zminus_mod, Pvs, Z.sub_diag. reflexivity. }
        subst a. reflexivity.
      + rewrite Pvs' in Pvs. apply off_mod in Pvs.
        assert (E0: elen = 0).
        { assert (PM: Ptrofs.modulus = 2 ^ 64) by reflexivity. rewrite PM in Pvs.
          apply (cong_eq _ _ (2 ^ 64)); [lia | | lia | lia].
          replace (elen - 0) with (ps - (ps - elen)) by lia.
          rewrite Zminus_mod, Pvs, Z.sub_diag. reflexivity. }
        subst elen. rewrite Z.sub_0_r. apply xblock_noext. }
  destruct Hreg as (a & c & Hrg & Ha & Hac & HX).
  specialize (Hbe 0 mem ps a c ltac:(lia) ltac:(lia)
                ltac:(rewrite Z.add_0_l, Hm; apply sublist_same; [reflexivity | rewrite Zlength_map; reflexivity])
                Hrg ltac:(lia) Ha ltac:(intros j [Hj | Hj]; lia)).
  rewrite Z.sub_0_r, Eu in Hbe.
  fold Exact.xblock in Hbe.
  change (1 =? 1) with true in Hbe.
  destruct (d_hist XS d (oa_d o)) as [[p' ds'] de']. rewrite HX.
  destruct (Exact.xblock (ts_x ts) mem ps (oa_d o) a c u bsm (oa_cap o) true) as [[[st2 mem2] sz] |] eqn:Ex;
    [| exact Hbe].
  destruct Hbe as (-> & Hsub & Hts).
  destruct (xblock_written_cap (ts_x ts) st2 mem mem2 ps (oa_d o) a c u bsm (oa_cap o) true sz ltac:(lia) Ex) as (Hsz & _).
  pose proof (xblock_len_ge (ts_x ts) st2 mem mem2 ps (oa_d o) a c u bsm (oa_cap o) true sz ltac:(lia) Ex) as Hge.
  destruct (region_whole mem mem2 oc' Hge ltac:(lia) Hsub) as [Eoc Lm2].
  destruct (bytes_of_comp (ts_x ts) st2 mem mem2 ps (oa_d o) a c (oa_cap o) sz Hbm eq_refl Hxh Ex) as [Bm2 Hx2].
  split; [reflexivity |]. split; [exact Hsz |]. split; [exact Eoc |]. split; [exact Lm2 |].
  split; [exact Bm2 |]. split; [reflexivity |]. split; [exact Hx2 | exact Hts].
Qed.

(* without room: the C decodes into the empty window o0 at dst (no history read); an extDict in the ring is excluded
   by cont_exact's premise (noext0) *)
Lemma bres_comp0 r oc0 tso (i: inwin) (hh: hctx) (o0: outarr) b ofs :
  oa_cap o = 0 -> oa_base o = Vptr b ofs ->
  (hc_ext hh = ExtNone \/
   exists e1, fs_dictEnd fs1 = offset_val e1 (Vptr b ofs) /\ 0 <= e1 <= Ptrofs.max_unsigned) ->
  hc_ps hh = 0 -> oa_d o0 = 0 -> oa_cap o0 = 0 -> 0 <= oa_N o0 ->
  iw_s i = u -> block_exact ts o0 i hh bsm 1 r oc0 tso ->
  bres_exact fs1 ts o u n r (oa_c o) tso 0.
Proof using All.
  intros Hc0 Eb Hext Ep Ed0 Ec0 HN0 Eu Hbe fh d mem Hd Hm Hbm Hne.
  destruct (comp_fields fh d mem Hd Hm) as (Ds & Db & F2 & Ent & LN & Hxh & ->).
  destruct Hext as [Hext | (e1 & Hde & He1)].
  2: { exfalso. pose proof Hd as Hd0. drel_d Hd0. rewrite Eb in *.
       destruct (Hptr ltac:(rewrite Ds; unfold DS_decodeBlockHeader, DS_checkChecksum; destruct Hst34; lia))
         as (_ & _ & _ & _ & _ & _ & Pde & _).
       assert (Ede: d_de XS d = Some e1).
       { apply (ring_ptr_off b ofs); [intros x Ex; apply Roff; right; right; right; exact Ex | exact He1 |].
         rewrite <- Pde, Hde. reflexivity. }
       rewrite (Hne ltac:(rewrite Ds; unfold DS_decompressBlock, DS_decompressLastBlock; destruct Hst34; lia) Db Hc0)
         in Ede. discriminate. }
  assert (Hrg: hc_region hh 0 = Some (0, 0, 0)) by (unfold hc_region; rewrite Hext, Ep; reflexivity).
  specialize (Hbe 0 [] 0 0 0 ltac:(lia) ltac:(rewrite Zlength_nil; lia) ltac:(reflexivity) Hrg ltac:(lia) ltac:(lia)
                ltac:(intros j [Hj | Hj]; rewrite ?Ed0 in Hj; lia)).
  rewrite Ed0, Ec0, Eu in Hbe. fold Exact.xblock in Hbe. change (1 =? 1) with true in Hbe. change (0 - 0) with 0 in Hbe.
  rewrite Hc0.
  destruct (d_hist XS d (oa_d o)) as [[p' ds'] de'].
  pose proof (xblock_cap0 (ts_x ts) mem p' (oa_d o) ds' de' [] 0 0 0 0 u bsm true ltac:(lia)) as HC.
  destruct (Exact.xblock (ts_x ts) mem p' (oa_d o) ds' de' u bsm 0 true) as [[[a m1] n1] |] eqn:E1;
    destruct (Exact.xblock (ts_x ts) [] 0 0 0 0 u bsm 0 true) as [[[a2 m2] n2] |];
    try contradiction; [| exact Hbe].
  destruct HC as (<- & -> & -> & -> & ->). destruct Hbe as (-> & _ & Hts).
  destruct (bytes_of_comp (ts_x ts) a mem mem p' (oa_d o) ds' de' 0 0 Hbm eq_refl Hxh E1) as [_ Hx2].
  split; [reflexivity |]. split; [lia |]. split; [exact Hm |]. split; [reflexivity |].
  split; [exact Hbm |]. split; [reflexivity |]. split; [exact Hx2 | exact Hts].
Qed.

End Comp.
