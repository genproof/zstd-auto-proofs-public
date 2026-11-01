(* FS3 streaming, case zdss_flush: the exact claim (S3Main.ex_call) after the flush, plain Coq on the model's
   iteration ExStream.st_flush.  The C (zstd_decompress.c 2377-2398) copies min(room, outEnd - outStart) bytes of
   the ring from outStart (ZSTD_limitCopy); when all are out it goes to zdss_read, restarting the ring at 0 when the
   frame is larger than the ring and a block of blockSizeMax would not fit after outStart (LNext); otherwise the
   loop stops (LStop).  The bytes copied are the ring's cells, which the exact relation (S3XRel.zrel) pins to the
   model's ring zs_mem; the restart's comparisons are the model's because the exact relation bounds the header's
   content size and block size (S3XRel.drel). *)
Require Import Zstd.proof.dec.v3.FS.stream.S3RetStmts Zstd.proof.dec.v3.FS.stream.flush.S3FlushLem.
Require Import Zstd.proof.dec.v3.FS.stream.S3XKit.
Require Import Zstd.proof.model.ExCall Zstd.proof.model.ExStream Zstd.proof.model.ExStreamFacts.
Require Zstd.proof.model.ExStream Zstd.proof.model.ExHuf Zstd.proof.model.ExBlock Zstd.proof.model.Exact.

Lemma flush_zbytes_inj (x y: list Z) : bytes_ok x -> bytes_ok y -> zbytes x = zbytes y -> x = y.
Proof.
  revert y. induction x as [ | u x IH]; intros [ | v y] Hx Hy E; simpl in E; try discriminate; auto.
  assert (Hu: Vint (Int.repr u) = Vint (Int.repr v)) by congruence.
  assert (Ht: zbytes x = zbytes y) by congruence.
  inv Hx. inv Hy. f_equal; [| apply IH; auto].
  unfold is_byte in *.
  apply (f_equal (fun w => match w with Vint i => Int.unsigned i | _ => 0 end)) in Hu. simpl in Hu.
  rewrite !Int.unsigned_repr in Hu by rep_lia. auto.
Qed.

Lemma flush_slice_sublist (l: list Z) (i k: Z) : 0 <= i -> 0 <= k -> slice l i k = sublist i (i + k) l.
Proof. intros Hi Hk. unfold slice, sublist. rewrite skipn_firstn_comm. f_equal. lia. Qed.

(* the bytes the flush delivers: the first m pending bytes are the model's ring cells from outStart *)
Lemma flush_dl_eq (pend mem: list Z) (ro: list val) (ostart oend m: Z) :
  0 <= ostart <= oend -> oend <= Zlength mem -> 0 <= m <= oend - ostart ->
  ro = zbytes mem -> sublist ostart oend ro = zbytes pend -> bytes_ok (sublist 0 m pend) -> bytes_ok mem ->
  sublist 0 m pend = slice mem ostart m.
Proof.
  intros Ho Hl Hm Hro Hp Hb Hbm. subst ro.
  rewrite sublist_map in Hp.
  assert (Hlp: Zlength pend = oend - ostart).
  { rewrite <- (Zlength_map _ _ (fun b : Z => Vint (Int.repr b)) pend), <- Hp, Zlength_map, Zlength_sublist; lia. }
  rewrite flush_slice_sublist by lia.
  apply flush_zbytes_inj; [exact Hb | apply Forall_sublist; exact Hbm |].
  rewrite <- !sublist_map. rewrite <- Hp, sublist_map, sublist_map, sublist_sublist by (try rewrite Zlength_map; lia).
  do 2 f_equal; lia.
Qed.

(* the stream state after the flush: streamStage st, outStart os, outEnd oe; the rest of the state is the model's *)
Lemma zrel_after (z: zstate_x) (s: sfields) (fs: fstate) (t: tabs3) (st os oe: Z) :
  zrel z (sf_strip s) fs t -> ZDSS_read <= ExStream.zs_stage XS z -> (st = ZDSS_read \/ st = ZDSS_flush) ->
  0 <= os <= oe -> oe <= ExStream.zs_outbs XS z ->
  zrel_end (ExStream.z_ring XS (ExStream.z_stage XS z st) os oe) (sf_strip (sf_after s st os oe)) fs t.
Proof.
  intros Hz Hs Hst Ho Hoe.
  destruct Hz as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & _ & Hr).
  destruct (Hr Hs) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & (ts & Et & Hd) & _).
  pose proof Hd as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstg & Hexp & _).
  unfold zrel_end, zrel. destruct z; cbn in *.
  assert (Hst2: 0 <= st <= 4 /\ st <> ZDSS_loadHeader /\ ZDSS_read <= st /\ st <> ZDSS_load)
    by (unfold ZDSS_read, ZDSS_flush, ZDSS_loadHeader, ZDSS_load in *; lia).
  destruct Hst2 as (Hst2 & Hst3 & Hst4 & Hst5).
  split.
  { repeat split; auto; try congruence; try (intros X; contradiction); try lia.
    exists ts. split; [exact Et | exact Hd]. }
  split; [intros _; split; [exact Hexp | intros _; exact Hstg] |].
  split; [intros X; unfold ZDSS_init, ZDSS_read in *; lia |].
  repeat split; auto.
Qed.

Section CM_S3FlushX_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.

(* what ex_call gives at the start of the flush: the model's loop state zi, related to the context *)
Lemma flush_x_start (a: dsa) (w: lw) (pend: list Z) (ostart oend m: Z) :
  fresh_cfg (a_st a) -> ex_call a w -> w_smw w = 1 ->
  sf_stage (c3_s (w_k w)) = zdss_flush ->
  sf_outStart (c3_s (w_k w)) = vlong ostart -> sf_outEnd (c3_s (w_k w)) = vlong oend ->
  0 <= ostart <= oend -> oend <= sf_outSize (c3_s (w_k w)) -> sf_outSize (c3_s (w_k w)) <= Int64.max_unsigned ->
  sublist ostart oend (ring_out (c3_s (w_k w))) = zbytes pend ->
  0 <= m <= oend - ostart -> bytes_ok (sublist 0 m pend) ->
  exists z0 zi f, ex_loop a z0 zi f (w_ipc w - a_ipos a) (w_dl w) /\
    zrel zi (w_sx w) (w_fs w) (w_tabs w) /\ ExStream.zs_stage XS zi = ZDSS_flush /\
    ExStream.zs_ostart XS zi = ostart /\ ExStream.zs_oend XS zi = oend /\
    sublist 0 m pend = slice (ExStream.zs_mem XS zi) ostart m.
Proof.
  intros Hf Hx Hs Hst Hos Hoe Ho Hoe2 Hmax Hp Hm Hb.
  destruct (ex_call_go a w Hx Hs Hf) as (z0 & zi & f & Hl & Hz).
  assert (Hzr: zrel zi (w_sx w) (w_fs w) (w_tabs w)) by (destruct Hz as [(_ & _ & _ & H) | (H & _)]; exact H).
  exists z0, zi, f. split; [exact Hl|]. split; [exact Hzr|].
  pose proof Hzr as (E1 & E2 & E3 & E4 & _ & _ & E7 & E8 & E9 & _ & _ & Hr).
  unfold w_sx in *; cbn [sf_strip sf_stage sf_inSize sf_outSize sf_ring sf_outStart sf_outEnd sf_inPos] in *.
  assert (Hs4: ExStream.zs_stage XS zi = ZDSS_flush) by (rewrite <- E1, Hst; reflexivity).
  split; [exact Hs4|].
  destruct Hr as (F1 & F2 & F3 & F4 & F5 & _) ; [rewrite Hs4; unfold ZDSS_read, ZDSS_flush; lia |].
  cbn [sf_strip sf_outStart sf_outEnd] in F2, F3.
  assert (Eos: ExStream.zs_ostart XS zi = ostart) by (apply vlong_inj; [lia | lia | congruence]).
  assert (Eoe: ExStream.zs_oend XS zi = oend) by (apply vlong_inj; [lia | lia | congruence]).
  split; [exact Eos|]. split; [exact Eoe|].
  apply (flush_dl_eq pend (ExStream.zs_mem XS zi) (ring_out (c3_s (w_k w))) ostart oend m); auto; try lia.
  unfold ring_out. rewrite E3, E4. exact E9.
Qed.

End CM_S3FlushX_1.

(* the input facts of a loop state the model's iteration lemmas need *)
Lemma flush_xin (a: dsa) (w: lw) :
  bytes_ok (a_ibs a) -> Zlength (a_ibs a) = a_isz a -> 0 <= a_ipos a -> a_ipos a <= w_ipc w <= a_isz a ->
  bytes_ok (a_xin a) /\ 0 <= w_ipc w - a_ipos a <= Zlength (a_xin a).
Proof.
  intros Hb Hl H0 Hi. unfold a_xin. split; [apply Forall_sublist; exact Hb |].
  rewrite Zlength_sublist by lia. lia.
Qed.

(* the C's ring-restart test (U64 comparisons on the fields zstd stores) is the model's *)
Lemma flush_restart_test (zi: zstate_x) (fs: fstate) (h: frame_header) (b outbs oend: Z) :
  fs_fParams fs = fh_val (ExStream.zs_fp XS zi) ->
  0 <= fh_contentSize (ExStream.zs_fp XS zi) <= Int64.max_unsigned ->
  0 <= fh_blockSizeMax (ExStream.zs_fp XS zi) <= Int.max_unsigned ->
  fs_fParams fs = fh_val (fh_adj h b) -> 0 <= oend <= outbs -> outbs <= 2 ^ 32 ->
  Int64.ltu (Int64.repr outbs) (Int64.repr (fh_contentSize h)) =
    (outbs <? fh_contentSize (ExStream.zs_fp XS zi)) /\
  Int64.unsigned (Int64.repr (oend + Int.unsigned (Int.repr b))) = oend + fh_blockSizeMax (ExStream.zs_fp XS zi).
Proof.
  intros E1 Hc Hb E2 Ho Hm. rewrite E1 in E2.
  assert (Ec: Int64.repr (fh_contentSize (ExStream.zs_fp XS zi)) = Int64.repr (fh_contentSize h)).
  { apply (f_equal fst) in E2. unfold fh_val in E2. cbn [fst fh_adj fh_contentSize] in E2. congruence. }
  assert (Eb: Int.repr (fh_blockSizeMax (ExStream.zs_fp XS zi)) = Int.repr b).
  { apply (f_equal (fun x => fst (snd (snd x)))) in E2. unfold fh_val in E2.
    cbn [fst snd fh_adj fh_blockSizeMax] in E2. congruence. }
  rewrite <- Ec, <- Eb. rewrite Int.unsigned_repr by lia. split.
  - unfold Int64.ltu. rewrite !Int64.unsigned_repr by rep_lia.
    destruct (zlt _ _); symmetry; [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
  - rewrite Int64.unsigned_repr by rep_lia. reflexivity.
Qed.

Section CM_S3FlushX_2.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.

(* a complete flush (all of [outStart, outEnd) out; wr: the ring restarts): the loop goes on at zdss_read, as the
   model's iteration (LNext) *)
Lemma flush_x_cpl (a: dsa) (w w': lw) (pend: list Z) (ostart oend: Z) (h: frame_header) (b: Z) (wr: bool) :
  ex_call a w -> w_smw w = 1 ->
  bytes_ok (a_ibs a) -> Zlength (a_ibs a) = a_isz a -> 0 <= a_ipos a -> a_ipos a <= w_ipc w <= a_isz a ->
  Zlength (w_dl w) = w_opc w - a_opos a ->
  sf_stage (c3_s (w_k w)) = zdss_flush ->
  sf_outStart (c3_s (w_k w)) = vlong ostart -> sf_outEnd (c3_s (w_k w)) = vlong oend ->
  0 <= ostart <= oend -> oend <= sf_outSize (c3_s (w_k w)) -> sf_outSize (c3_s (w_k w)) <= 2 ^ 32 ->
  sublist ostart oend (ring_out (c3_s (w_k w))) = zbytes pend ->
  oend - ostart <= a_osz a - w_opc w ->
  fs_fParams (c3_fs (w_k w)) = fh_val (fh_adj h b) ->
  (wr = true -> Int64.ltu (Int64.repr (sf_outSize (c3_s (w_k w)))) (Int64.repr (fh_contentSize h)) = true /\
     Int64.unsigned (Int64.repr (sf_outSize (c3_s (w_k w)))) <
     Int64.unsigned (Int64.repr (oend + Int.unsigned (Int.repr b)))) ->
  (wr = false -> Int64.ltu (Int64.repr (sf_outSize (c3_s (w_k w)))) (Int64.repr (fh_contentSize h)) = false \/
     Int64.unsigned (Int64.repr (oend + Int.unsigned (Int.repr b))) <=
     Int64.unsigned (Int64.repr (sf_outSize (c3_s (w_k w))))) ->
  w_smw w' = 1 -> w_ipc w' = w_ipc w -> w_dl w' = w_dl w ++ sublist 0 (oend - ostart) pend ->
  bytes_ok (w_dl w') ->
  w_sx w' = sf_strip (sf_after (c3_s (w_k w)) zdss_read (if wr then 0 else oend) (if wr then 0 else oend)) ->
  w_fs w' = w_fs w -> w_tabs w' = w_tabs w ->
  ex_call a w'.
Proof.
  intros Hx Hs Hib Hil Hip0 Hip Hdl Hst Hos Hoe Ho Hoe2 Hosz Hp Hroom Hfh Hwr Hnwr Hs' Hip' Hdl' Hbdl' Hsx' Hfs' Ht'.
  apply ex_call_next_mk; [exact Hs'|]. intros Hf.
  assert (Hb: bytes_ok (sublist 0 (oend - ostart) pend))
    by (rewrite Hdl' in Hbdl'; apply Forall_app in Hbdl'; tauto).
  destruct (flush_x_start a w pend ostart oend (oend - ostart) Hf Hx Hs Hst Hos Hoe Ho Hoe2 ltac:(rep_lia) Hp
              ltac:(lia) Hb) as (z0 & zi & f & Hl & Hzr & Hs4 & Eos & Eoe & Edl).
  pose proof Hzr as (_ & _ & _ & E4 & _ & _ & _ & _ & _ & _ & _ & Hr).
  destruct Hr as (_ & _ & _ & _ & _ & _ & _ & (ts & _ & Hd) & _); [rewrite Hs4; unfold ZDSS_read, ZDSS_flush; lia |].
  destruct Hd as (Efp & Hcs & Hbsm & _).
  unfold w_sx, w_fs in E4, Efp. cbn [sf_strip sf_outSize] in E4.
  destruct (flush_restart_test zi (c3_fs (w_k w)) h b (sf_outSize (c3_s (w_k w))) oend Efp Hcs Hbsm Hfh
              ltac:(lia) Hosz) as (Elt & Eadd).
  set (os' := if wr then 0 else oend).
  set (z' := ExStream.z_ring XS (ExStream.z_stage XS zi ZDSS_read) os' os').
  destruct (flush_xin a w Hib Hil Hip0 Hip) as (Hbx & Hipx).
  assert (Hit: one_iter_x (a_xin a) (a_xroom a) zi (w_ipc w - a_ipos a) (w_dl w) =
               ExStream.LNext XS z' (w_ipc w - a_ipos a) (w_dl w ++ slice (ExStream.zs_mem XS zi) ostart (oend - ostart))).
  { unfold one_iter_x, ExStream.one_iter. rewrite Hs4. cbn - [ExStream.st_flush].
    unfold ExStream.st_flush. rewrite Eos, Eoe.
    replace (Z.min (a_xroom a - Zlength (w_dl w)) (oend - ostart)) with (oend - ostart)
      by (unfold a_xroom; rewrite Hdl; lia).
    rewrite Z.eqb_refl.
    replace (ostart + (oend - ostart)) with oend by lia.
    cbn [ExStream.zs_outbs ExStream.zs_fp ExStream.zs_ostart ExStream.z_stage ExStream.z_ring].
    rewrite <- E4.
    assert (Ewr: andb (sf_outSize (c3_s (w_k w)) <? fh_contentSize (ExStream.zs_fp XS zi))
                  (oend + fh_blockSizeMax (ExStream.zs_fp XS zi) >? sf_outSize (c3_s (w_k w))) = wr).
    { rewrite <- Elt, <- Eadd. destruct wr.
      - destruct (Hwr eq_refl) as (H1 & H2). rewrite H1. cbn. apply Z.gtb_lt.
        rewrite (Int64.unsigned_repr (sf_outSize (c3_s (w_k w)))) in H2 by rep_lia. exact H2.
      - destruct (Hnwr eq_refl) as [H1 | H1]; [rewrite H1; reflexivity |].
        rewrite (Int64.unsigned_repr (sf_outSize (c3_s (w_k w)))) in H1 by rep_lia.
        replace (_ >? _) with false by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; exact H1). apply andb_false_r. }
    rewrite Ewr. subst z' os'. destruct wr; destruct zi; reflexivity. }
  destruct (ex_loop_next a z0 zi f _ (w_dl w) _ _ _ Hbx Hipx ltac:(unfold a_xroom; lia) Hl Hit) as (f1 & Hl1 & _).
  exists z0, z', f1. rewrite Hip', Hdl', Edl. split; [exact Hl1 |].
  rewrite Hsx', Hfs', Ht'. subst z'.
  apply zrel_after; [exact Hzr | rewrite Hs4; unfold ZDSS_read, ZDSS_flush; lia | left; reflexivity |
                     subst os'; destruct wr; lia | subst os'; destruct wr; rewrite <- E4; lia].
Qed.

(* an incomplete flush (the caller's room is full first): the loop stops at zdss_flush, as the model's iteration
   (LStop) *)
Lemma flush_x_inc (a: dsa) (w w': lw) (pend: list Z) (ostart oend: Z) :
  ex_call a w -> w_smw w = 1 ->
  bytes_ok (a_ibs a) -> Zlength (a_ibs a) = a_isz a -> 0 <= a_ipos a -> a_ipos a <= w_ipc w <= a_isz a ->
  Zlength (w_dl w) = w_opc w - a_opos a -> w_opc w <= a_osz a ->
  sf_stage (c3_s (w_k w)) = zdss_flush ->
  sf_outStart (c3_s (w_k w)) = vlong ostart -> sf_outEnd (c3_s (w_k w)) = vlong oend ->
  0 <= ostart <= oend -> oend <= sf_outSize (c3_s (w_k w)) -> sf_outSize (c3_s (w_k w)) <= 2 ^ 32 ->
  sublist ostart oend (ring_out (c3_s (w_k w))) = zbytes pend ->
  a_osz a - w_opc w < oend - ostart ->
  w_smw w' = 0 -> w_ipc w' = w_ipc w -> w_dl w' = w_dl w ++ sublist 0 (a_osz a - w_opc w) pend ->
  bytes_ok (w_dl w') ->
  w_sx w' = sf_strip (sf_after (c3_s (w_k w)) zdss_flush (ostart + (a_osz a - w_opc w)) oend) ->
  w_fs w' = w_fs w -> w_tabs w' = w_tabs w ->
  ex_call a w'.
Proof.
  intros Hx Hs Hib Hil Hip0 Hip Hdl Hopc Hst Hos Hoe Ho Hoe2 Hosz Hp Hroom Hs' Hip' Hdl' Hbdl' Hsx' Hfs' Ht'.
  apply ex_call_stop_mk; [exact Hs'|]. intros Hf.
  set (m := a_osz a - w_opc w) in *.
  assert (Hb: bytes_ok (sublist 0 m pend)) by (rewrite Hdl' in Hbdl'; apply Forall_app in Hbdl'; tauto).
  destruct (flush_x_start a w pend ostart oend m Hf Hx Hs Hst Hos Hoe Ho Hoe2 ltac:(rep_lia) Hp
              ltac:(lia) Hb) as (z0 & zi & f & Hl & Hzr & Hs4 & Eos & Eoe & Edl).
  pose proof Hzr as (_ & _ & _ & E4 & _).
  unfold w_sx in E4. cbn [sf_strip sf_outSize] in E4.
  set (z1 := ExStream.z_ring XS (ExStream.z_stage XS zi ZDSS_flush) (ostart + m) oend).
  destruct (flush_xin a w Hib Hil Hip0 Hip) as (Hbx & Hipx).
  assert (Hit: one_iter_x (a_xin a) (a_xroom a) zi (w_ipc w - a_ipos a) (w_dl w) =
               ExStream.LStop XS z1 (w_ipc w - a_ipos a) (w_dl w ++ slice (ExStream.zs_mem XS zi) ostart m)).
  { unfold one_iter_x, ExStream.one_iter. rewrite Hs4. cbn - [ExStream.st_flush].
    unfold ExStream.st_flush. rewrite Eos, Eoe.
    replace (Z.min (a_xroom a - Zlength (w_dl w)) (oend - ostart)) with m
      by (unfold a_xroom; rewrite Hdl; subst m; lia).
    replace (m =? oend - ostart) with false by (symmetry; apply Z.eqb_neq; lia).
    subst z1. destruct zi; cbn in Hs4 |- *; subst; reflexivity. }
  destruct (ex_loop_stop a z0 zi f _ (w_dl w) _ _ _ Hbx Hipx ltac:(unfold a_xroom; lia) Hl Hit) as (Hal & Hz1).
  pose proof Hl as (Hr0 & Hz0 & _).
  exists z0, z1. rewrite Hip', Hdl', Edl.
  split; [exact Hr0|]. split; [exact Hz0|]. split; [exact Hz1|]. split; [exact Hal|].
  rewrite Hsx', Hfs', Ht'. subst z1.
  apply zrel_after; [exact Hzr | rewrite Hs4; unfold ZDSS_read, ZDSS_flush; lia | right; reflexivity | lia |
                     rewrite <- E4; lia].
Qed.

End CM_S3FlushX_2.
