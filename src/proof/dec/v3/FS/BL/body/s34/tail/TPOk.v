(* FS3-bl BODY, stages 3/4, the tail: the post of a successful call (pure): the new state ba'
   (the model's next state when it follows, else ba_st = None), BRc for the new stage (t34_next). *)
Require Export Zstd.proof.dec.v3.FS.BL.body.s34.tail.TFp.
Local Open Scope logic.

Section CM_TPOk_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* ---------- helpers ---------- *)

Lemma t34_fsx_fields fs ob osz opos pcs c e' cold ds r x stg e :
  let f := t34_fsE (t34_fsB (t34_fsm fs ob osz opos pcs c e' cold) ds r x ob opos) stg e in
  let fc := continuity fs (offset_val opos ob) (osz - opos) in
  fs_expected f = vlong e /\ fs_stage f = Vint (Int.repr (bl_stz stg)) /\
  fs_isFrameDecompression f = fs_isFrameDecompression fs /\ fs_ddictIsCold f = cold /\
  fs_dictID f = fs_dictID fs /\ fs_processedCSize f = vlong (pcs + Zlength c) /\
  fs_decodedSize f = vlong (ds + r) /\ fs_fParams f = fs_fParams fs /\
  fs_validateChecksum f = fs_validateChecksum fs /\ fs_xxh f = x /\
  fs_bType f = fs_bType fs /\ fs_rleSize f = fs_rleSize fs /\
  fs_previousDstEnd f = offset_val (opos + r) ob /\ fs_gpDictCopy f = Vint (Int.repr 0) /\
  fs_prefixStart f = fs_prefixStart fc /\ fs_virtualStart f = fs_virtualStart fc /\ fs_dictEnd f = fs_dictEnd fc.
Proof.
  unfold t34_fsE, t34_fsB, t34_fsm, bl_fs1, continuity. destruct (cont_moves _ _ _); cbn; repeat split.
Qed.

Lemma t34_vlong_inj a b : vlong a = vlong b -> 0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned -> a = b.
Proof.
  unfold vlong; intros H Ha Hb.
  assert (H1: Int64.repr a = Int64.repr b) by congruence.
  apply (f_equal Int64.unsigned) in H1. rewrite !Int64.unsigned_repr in H1 by lia. exact H1.
Qed.

Lemma t34_vlong_norm a : vlong a = vlong (Int64.unsigned (Int64.repr a)) /\
  0 <= Int64.unsigned (Int64.repr a) <= Int64.max_unsigned.
Proof. unfold vlong. rewrite Int64.repr_unsigned. split; [reflexivity|]. pose proof (Int64.unsigned_range_2 (Int64.repr a)); lia. Qed.

Lemma t34_cells_app l1 l2 : cells_bytes l1 -> cells_bytes l2 -> cells_bytes (l1 ++ l2).
Proof.
  intros (b1 & -> & H1) (b2 & -> & H2). exists (b1 ++ b2). split.
  - rewrite map_app; reflexivity.
  - apply Forall_app; auto.
Qed.

Lemma t34_cells_tc (l: list Z) : Forall (tc_val' tuchar) (zbytes l) -> cells_bytes (zbytes l).
Proof.
  intros H. exists (map (fun z => Int.unsigned (Int.repr z)) l). split.
  - rewrite map_map. apply map_ext. intros z. rewrite Int.repr_unsigned. reflexivity.
  - induction l as [|a l IH]; cbn in *; constructor.
    + inversion H as [|? ? Ha _]; subst. specialize (Ha ltac:(discriminate)).
      unfold tc_val in Ha; cbn in Ha. unfold is_byte. rep_lia.
    + inversion H; subst; apply IH; auto.
Qed.

Lemma t34_Forall_sublist {A} (P: A -> Prop) (l: list A) i j : Forall P l -> Forall P (sublist i j l).
Proof. intros H. apply Forall_sublist. exact H. Qed.
Lemma t34_lay od osz ba ob opos r fc f (ba': blabs) :
  bl_lay od osz (bl_moved ba ob opos) fc -> 0 <= r <= osz - opos ->
  ba_out ba' = Some (ob, bl_start ba opos, opos + r) ->
  fs_previousDstEnd f = offset_val (opos + r) ob -> fs_gpDictCopy f = Vint (Int.repr 0) ->
  fs_prefixStart f = fs_prefixStart fc -> fs_virtualStart f = fs_virtualStart fc -> fs_dictEnd f = fs_dictEnd fc ->
  bl_lay od osz ba' f.
Proof.
  unfold bl_lay, bl_moved; cbn [ba_out]. intros L Hr Ho Hp Hg Hps Hvs Hde. rewrite Ho.
  destruct L as [(L1 & L2 & L3 & L4 & L5 & L6) | [(ob0 & f0 & L1 & L2 & L3 & L4 & L5 & L6 & L7) |
                 (ob0 & f0 & pe & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9)]].
  - cbn in L6. destruct L6 as [E2 E1]. assert (r = 0) by lia. subst r. rewrite Z.add_0_r in *.
    right; left. exists ob, osz. rewrite E1 in *. rewrite <- E2 in *. repeat split; try congruence.
  - assert (E1: bl_start ba opos = osz) by congruence. assert (E2: opos = osz) by congruence.
    assert (r = 0) by lia. subst r. rewrite Z.add_0_r in *.
    right; left. exists ob, osz. rewrite E1, E2 in *. repeat split; try congruence.
  - inversion L1; subst ob0 f0 pe.
    right; right. exists ob, (bl_start ba opos), (opos + r). repeat split; try congruence; lia.
Qed.

Lemma t34_sub_pre (oc oc': list val) f0 opos :
  0 <= f0 <= opos -> sublist 0 opos oc' = sublist 0 opos oc -> sublist f0 opos oc' = sublist f0 opos oc.
Proof.
  intros Hf E.
  assert (G: forall l: list val, sublist f0 opos (sublist 0 opos l) = sublist f0 opos l).
  { intros l. rewrite sublist_sublist by lia. rewrite !Z.add_0_r. reflexivity. }
  rewrite <- (G oc'), <- (G oc), E. reflexivity.
Qed.

Lemma t34_hist ba (ba': blabs) ob opos oc oc' r cnt :
  bl_hist_ok ba ob opos oc -> 0 <= opos -> 0 <= r -> opos + r <= Zlength oc' ->
  sublist 0 opos oc' = sublist 0 opos oc -> sublist opos (opos + r) oc' = zbytes cnt -> bytes_ok cnt ->
  Forall (tc_val' tuchar) oc' ->
  ba_out ba' = Some (ob, bl_start ba opos, opos + r) ->
  (forall b', ba_st ba' = Some b' -> exists b, ba_st ba = Some b /\ bs_out b' = bs_out b ++ cnt) ->
  bl_hist_ok ba' ob (opos + r) oc'.
Proof.
  intros Hh Ho Hr Hl Hpre Hc Hcb Htc Hout Hst.
  assert (Hseg: 0 <= bl_start ba opos <= opos /\
    match ba_st ba with Some b => sublist (bl_start ba opos) opos oc = zbytes (bs_out b)
    | None => cells_bytes (sublist (bl_start ba opos) opos oc) end).
  { unfold bl_hist_ok, bl_start in *. destruct (ba_out ba) as [[[ob0 f0] pe]|].
    - destruct Hh as (_ & -> & Hf & Hm). split; [lia | exact Hm].
    - split; [lia|]. rewrite sublist_nil' by reflexivity.
      destruct (ba_st ba); [rewrite Hh; reflexivity | exists nil; split; [reflexivity | constructor]]. }
  destruct Hseg as [Hf Hm].
  pose proof (t34_sub_pre oc oc' (bl_start ba opos) opos Hf Hpre) as Hs.
  unfold bl_hist_ok. rewrite Hout. split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
  rewrite (sublist_split (bl_start ba opos) opos (opos + r)) by lia.
  destruct (ba_st ba') as [b'|] eqn:Eb'.
  - destruct (Hst b' eq_refl) as (b & Eb & Eo). rewrite Eb in Hm. rewrite Eo, map_app, Hs, Hm, Hc. reflexivity.
  - apply t34_cells_app; [| exists cnt; auto].
    destruct (ba_st ba) as [b|].
    + rewrite Hs, Hm. apply t34_cells_tc. rewrite <- Hm, <- Hs. apply Forall_sublist, Htc.
    + rewrite Hs. exact Hm.
Qed.

(* the block's state after its content (bl_block_done's b1) *)
Definition t34_b1 (b: blst) (ts: dstate) (cnt: list Z) : blst :=
  {| bs_stage := bs_stage b; bs_expect := 0; bs_hbuf := bs_hbuf b; bs_hdr := bs_hdr b; bs_ds := ts;
     bs_out := bs_out b ++ cnt; bs_btype := bs_btype b; bs_rle := bs_rle b |}.

Lemma t34_done b ts cnt v :
  bs_stage b = bv_stage v -> (bv_stage v = BBlk \/ bv_stage v = BLastBlk) -> bs_hdr b = bv_h v ->
  Zlength cnt <= fh_blockSizeMax (bv_h v) ->
  (bv_stage v = BLastBlk -> fh_contentSize (bv_h v) = ZSTD_CONTENTSIZE_UNKNOWN \/
                            Zlength (bs_out b ++ cnt) = fh_contentSize (bv_h v)) ->
  bl_block_done b ts cnt = BLOk (bl_set (t34_b1 b ts cnt) (fst (t34_next v 0)) (snd (t34_next v 0))) cnt.
Proof.
  intros Hs Hst Hh Hl Hf. unfold bl_block_done, t34_next, t34_b1. cbv zeta. rewrite Hs, Hh.
  destruct (Zlength cnt >? fh_blockSizeMax (bv_h v)) eqn:E; [apply Z.gtb_lt in E; lia|].
  destruct Hst as [Hst|Hst]; rewrite Hst; [reflexivity|].
  unfold bl_frame_end. rewrite Hh.
  destruct (Hf Hst) as [F|F].
  - rewrite F, Z.eqb_refl. cbn [negb andb]. destruct (fh_checksumFlag (bv_h v) =? 1); reflexivity.
  - rewrite F, Z.eqb_refl, andb_false_r. destruct (fh_checksumFlag (bv_h v) =? 1); reflexivity.
Qed.

Lemma t34_step md dm b c v ts cnt :
  bs_stage b = bv_stage v -> (bv_stage v = BBlk \/ bv_stage v = BLastBlk) -> bs_hdr b = bv_h v ->
  bs_btype b = bv_bt v -> 0 <= bv_bt v <= 2 ->
  (forall x, blk_model dm b c = Some x -> x = (ts, cnt)) ->
  Zlength cnt <= fh_blockSizeMax (bv_h v) ->
  (bv_stage v = BLastBlk -> fh_contentSize (bv_h v) = ZSTD_CONTENTSIZE_UNKNOWN \/
                            Zlength (bs_out b ++ cnt) = fh_contentSize (bv_h v)) ->
  bl_step_nc md dm b c = BLUnk \/
  bl_step_nc md dm b c = BLOk (bl_set (t34_b1 b ts cnt) (fst (t34_next v 0)) (snd (t34_next v 0))) cnt.
Proof.
  intros Hs Hst Hh Hbt Hbr Hm Hl Hf.
  assert (Hst': bs_stage b = BBlk \/ bs_stage b = BLastBlk) by (rewrite Hs; exact Hst).
  assert (Hd := t34_done b ts cnt v Hs Hst Hh Hl Hf).
  assert (Hb: bl_step_nc md dm b c = bl_step md dm b c).
  { unfold bl_step_nc. destruct Hst' as [E|E]; rewrite E; reflexivity. }
  rewrite Hb. unfold bl_step. destruct Hst' as [E|E]; rewrite E;
  unfold blk_model in Hm; rewrite Hbt in *;
  (destruct (bv_bt v =? 0) eqn:E0;
   [ specialize (Hm _ eq_refl); injection Hm as -> ->; right; exact Hd
   | destruct (bv_bt v =? 1) eqn:E1;
     [ specialize (Hm _ eq_refl); injection Hm as -> ->; right; exact Hd
     | destruct (bv_bt v =? 2) eqn:E2;
       [ destruct (decode_block _ _ _ _ _ _) as [x|];
         [ specialize (Hm _ eq_refl); subst x; right; exact Hd | left; reflexivity ]
       | apply Z.eqb_neq in E0, E1, E2; lia ] ] ]).
Qed.

Lemma t34_out_len ba ob opos oc b :
  bl_hist_ok ba ob opos oc -> ba_st ba = Some b -> 0 <= opos <= Zlength oc -> 0 <= Zlength (bs_out b) <= opos.
Proof.
  unfold bl_hist_ok. intros Hh Eb Ho. rewrite Eb in Hh. destruct (ba_out ba) as [[[ob0 f0] pe]|].
  - destruct Hh as (_ & -> & Hf & Hm). apply (f_equal (@Zlength val)) in Hm.
    rewrite Zlength_map, Zlength_sublist in Hm by lia. lia.
  - rewrite Hh. rewrite Zlength_nil. lia.
Qed.

Lemma t34_hdr ign (v v': blv) fs f cnt :
  bv_h v' = bv_h v -> hdr_fields ign v fs -> fs_fParams f = fs_fParams fs ->
  fs_validateChecksum f = fs_validateChecksum fs -> fs_xxh f = t34_xxh (bl_val ign (bv_h v)) (fs_xxh fs) cnt ->
  hdr_fields ign v' f.
Proof.
  unfold hdr_fields, t34_xxh. intros Hv (H1 & H2 & H3 & H4) E1 E2 E3. rewrite Hv, E1, E2, E3.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  intros Hb. rewrite Hb. destruct (H4 Hb) as [l ->]. exists (l ++ cnt). reflexivity.
Qed.

(* the new state: the model's next state ost (or None), the new expected, the output extended by r *)
Definition t34_ba (ba: blabs) (ost: option blst) (v: blv) (e' : Z) (ob: val) (opos r: Z) : blabs :=
  {| ba_dict := ba_dict ba; ba_st := ost; ba_expect := snd (t34_next v e');
     ba_out := Some (ob, bl_start ba opos, opos + r) |}.

(* v with the new stage *)
Definition t34_v' (v: blv) (e': Z) : blv :=
  {| bv_stage := fst (t34_next v e'); bv_hdr := bv_hdr v; bv_hs := bv_hs v; bv_h := bv_h v; bv_bt := bv_bt v;
     bv_rle := bv_rle v |}.

Lemma t34_common (W: list ptr_witness) (pr: dparams) (od: option bldict) (osz0: Z) (ba: blabs)
    (fs: fstate) (ts: tstate) (hb: list val) (shk shd: share) (ob: val) (osz opos: Z) (oc: list val) (shs: share)
    (src: val) (c: list Z) (v: blv) (pcs: Z) (r: Z) (oc': list val) (e': Z) (cold: val) (t': tabs3) (ds: Z) (cnt: list Z) (ts': tstate)
    (ost: option blst) :
  t34_H W pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v pcs ->
  s34_mid_ok od ba v osz opos oc c r oc' e' cold t' ->
  is_error_code r = false -> r <= fh_blockSizeMax (bv_h v) -> t34_cnt od ba c opos oc' r t' cnt ts' ->
  fs_decodedSize fs = vlong ds -> 0 <= ds <= Int64.max_unsigned ->
  Forall (tc_val' tuchar) oc' ->
  (forall b', ost = Some b' -> exists b, ba_st ba = Some b /\ e' = 0 /\
     b' = bl_set (t34_b1 b ts' cnt) (fst (t34_next v 0)) (snd (t34_next v 0))) ->
  bl_claim_nc (dmode_of pr) ba (t34_ba ba ost v e' ob opos r) c r opos osz oc' ->
  t34_pp (dmode_of pr) od ba ob osz opos oc c r oc' (t34_ba ba ost v e' ob opos r)
    (t34_fsE (t34_fsB (t34_fsm fs ob osz opos pcs c e' cold) ds r (t34_xxh (t34_vc pr v) (fs_xxh fs) cnt) ob opos) (fst (t34_next v e')) (snd (t34_next v e'))) t' hb.
Proof.
  intros H M Herr Hbsm Hcnt Hds Hdsr Htc Host Hcl.
  destruct H as (Hpar & Hpre & Hci & Hmr & Hbd & Hfpo & Hstg & Hpcs & Hpcsr & Hsz & Hlay).
  destruct Hpre as (Hexp0 & Hhist & Hosz & _ & _ & _ & _ & _ & _ & Hopos & Hosz30 & Hloc & Hlc & Hbc).
  destruct M as (Mr & Mloc' & Mpre & Mcold & _ & Mok).
  destruct (Mok Herr) as (Mr2 & Me' & Mbt & _).
  destruct Hcnt as (Ccnt & Cbytes & Clen & Ct' & Cmod).
  destruct Hci as (Cexp & Cexpr & Cstage & Cifd & Ccold & Cdid & _ & _ & Chb & Cwf & Ccst & Clay).
  assert (Ccst': hdr_fields (md_ignore (dmode_of pr)) v fs /\ fs_bType fs = Vint (Int.repr (bv_bt v)) /\
     0 <= bv_bt v <= 2 /\ fs_rleSize fs = vlong (bv_rle v) /\ 0 <= bv_rle v < 2 ^ 21 /\
     0 < ba_expect ba <= fh_blockSizeMax (bv_h v) /\ (bv_bt v = 1 -> ba_expect ba = 1)).
  { unfold bl_cstage in Ccst. destruct Hstg as [E|E]; rewrite E in Ccst; exact Ccst. }
  destruct Ccst' as (Khf & Kbt & Kbtr & Krle & Krler & Kexp & _).
  assert (He: 0 <= e' /\ (0 < e' -> bv_bt v = 0 /\ e' < ba_expect ba)).
  { unfold bl_size_ok in Hsz. destruct Hstg as [E|E]; rewrite E in Hsz;
    destruct (bv_bt v =? 0) eqn:B; rewrite Me';
    (apply Z.eqb_eq in B || apply Z.eqb_neq in B); try (specialize (Mbt B)); split; intros; lia. }
  destruct He as [He0 He1].
  pose proof (t34_fsx_fields fs ob osz opos pcs c e' cold ds r (t34_xxh (t34_vc pr v) (fs_xxh fs) cnt)
                (fst (t34_next v e')) (snd (t34_next v e'))) as F.
  cbv zeta in F.
  destruct F as (Fe & Fst & Fifd & Fcold & Fdid & Fpcs & Fds & Ffp & Fvc & Fx & Fbt & Frle & Fpde & Fgp & Fps & Fvs & Fde).
  match goal with |- t34_pp _ _ _ _ _ _ _ _ _ _ _ ?f _ _ => set (f' := f) in * end.
  assert (Hcold': cold01 f') by (unfold cold01; rewrite Fcold; exact Mcold).
  unfold t34_pp.
  split; [exact Mr|]. split; [exact Mloc'|]. split; [exact Mpre|]. split; [exact Hcold'|]. split; [exact Chb|].
  split; [unfold f'; t34_fp Hfpo|].
  split; [|exact Hcl].
  intros _.
  split; [lia|]. split; [exists cnt; split; [exact Ccnt | exact Cbytes]|].
  split; [reflexivity|]. split; [reflexivity|].
  split.
  { apply (t34_hist ba (t34_ba ba ost v e' ob opos r) ob opos oc oc' r cnt Hhist ltac:(lia) ltac:(lia) ltac:(lia) Mpre Ccnt Cbytes Htc eq_refl).
    intros b' E. cbn in E. destruct (Host b' E) as (b & Eb & _ & ->). exists b. split; [exact Eb | reflexivity]. }
  split.
  { intros b' E. cbn in E. destruct (Host b' E) as (b & _ & E0 & ->). cbn. rewrite E0. reflexivity. }
  exists ts'. split; [exact Ct'|].
  exists (t34_v' v e'). split; [|split; [|exact Hbd]].
  - (* bl_cinv *)
    unfold bl_cinv. cbn [ba_expect t34_ba].
    split; [exact Fe|].
    split.
    { unfold t34_next. destruct (0 <? e') eqn:Ee; [apply Z.ltb_lt in Ee; specialize (He1 Ee); cbn; lia|].
      destruct Hstg as [E|E]; rewrite E; [|destruct (fh_checksumFlag (bv_h v) =? 1)]; cbn; unfold ZSTD_blockHeaderSize; lia. }
    split; [exact Fst|]. split; [rewrite Fifd; exact Cifd|]. split; [exact Hcold'|].
    split; [rewrite Fdid; exact Cdid|].
    split; [exists (Int64.unsigned (Int64.repr (pcs + Zlength c))); rewrite Fpcs; apply t34_vlong_norm|].
    split; [exists (Int64.unsigned (Int64.repr (ds + r))); rewrite Fds; apply t34_vlong_norm|].
    split; [exact Chb|]. split; [exact Cwf|].
    split.
    + assert (Hh': hdr_fields (md_ignore (dmode_of pr)) (t34_v' v e') f')
        by (apply (t34_hdr _ v _ fs f' cnt); [reflexivity | exact Khf | exact Ffp | exact Fvc | exact Fx]).
      unfold bl_cstage. unfold t34_v' at 1. cbn [bv_stage]. unfold t34_next in *.
      destruct (0 <? e') eqn:Ee.
      * apply Z.ltb_lt in Ee. destruct (He1 Ee) as [B0 Elt]. cbn [fst snd].
        destruct Hstg as [E|E]; rewrite E;
        (split; [exact Hh'|]); cbn [t34_v' bv_bt bv_rle bv_h];
        rewrite Fbt, Frle; repeat split; auto; lia.
      * destruct Hstg as [E|E]; rewrite E in *; [|destruct (fh_checksumFlag (bv_h v) =? 1) eqn:Ck]; cbn [fst snd];
        try (split; [exact Hh'|]); try (left; reflexivity); try reflexivity.
        split; [|reflexivity]. cbn. apply Z.eqb_eq in Ck. exact Ck.
    + apply (t34_lay od osz ba ob opos r _ f' (t34_ba ba ost v e' ob opos r) Hlay ltac:(lia) eq_refl Fpde Fgp Fps Fvs Fde).
  - (* bl_mrel *)
    intros b' Eb'. cbn in Eb'. destruct (Host b' Eb') as (b & Eb & E0 & ->).
    assert (Hn: t34_next v e' = t34_next v 0) by (rewrite E0; reflexivity).
    destruct (Hmr b Eb) as (R1 & R2 & R3 & R4 & Rb & R5).
    pose proof (t34_out_len ba ob opos oc b Hhist Eb ltac:(lia)) as Lo.
    assert (Eds: ds = Zlength (bs_out b)) by (apply t34_vlong_inj; [congruence | lia | rep_lia]).
    unfold t34_v', t34_ba. rewrite Hn. cbn [ba_expect bv_stage bs_stage bs_expect bs_ds bs_out bs_hdr bl_set t34_b1].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [rewrite Fds, Zlength_app, Eds, Clen; reflexivity|].
    split; [apply Forall_app; split; [exact Rb | exact Cbytes]|].
    unfold t34_next. replace (0 <? 0) with false by reflexivity.
    destruct Hstg as [E|E]; rewrite E in R5 |- *; destruct R5 as (R6 & _ & _ & R9);
    [|destruct (fh_checksumFlag (bv_h v) =? 1)]; cbn [fst snd bv_h bv_stage bs_hdr bs_out bl_set t34_b1]; try exact I;
    try (intros Hne; exfalso; apply Hne; reflexivity);
    (split; [exact R6|]); intros Hb; rewrite Fx; unfold t34_xxh, t34_vc; rewrite Hb, (R9 Hb); reflexivity.
Qed.

Lemma t34_ok_pp (W: list ptr_witness) (pr: dparams) (od: option bldict) (osz0: Z) (ba: blabs)
    (fs: fstate) (ts: tstate) (hb: list val) (shk shd: share) (ob: val) (osz opos: Z) (oc: list val) (shs: share)
    (src: val) (c: list Z) (v: blv) (pcs: Z) (r: Z) (oc': list val) (e': Z) (cold: val) (t': tabs3) (ds: Z) (cnt: list Z) (ts': tstate) :
  t34_H W pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v pcs ->
  s34_mid_ok od ba v osz opos oc c r oc' e' cold t' ->
  is_error_code r = false -> r <= fh_blockSizeMax (bv_h v) -> t34_cnt od ba c opos oc' r t' cnt ts' ->
  fs_decodedSize fs = vlong ds -> 0 <= ds <= Int64.max_unsigned ->
  (bv_stage v = BLastBlk -> e' = 0 -> t34_fcs_ok v ds r) ->
  Forall (tc_val' tuchar) oc' ->
  exists ba', t34_pp (dmode_of pr) od ba ob osz opos oc c r oc' ba'
    (t34_fsE (t34_fsB (t34_fsm fs ob osz opos pcs c e' cold) ds r (t34_xxh (t34_vc pr v) (fs_xxh fs) cnt) ob opos) (fst (t34_next v e')) (snd (t34_next v e'))) t' hb.
Proof.
  intros H M Herr Hbsm Hcnt Hds Hdsr Hfcs Htc.
  pose proof (t34_common W pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v pcs r oc' e' cold t' ds cnt ts')
    as Hc.
  specialize (fun ost => Hc ost H M Herr Hbsm Hcnt Hds Hdsr Htc).
  destruct (ba_st ba) as [b|] eqn:Eb;
    [destruct (dictref_model (ba_dict ba)) as [dm|] eqn:Edm; [destruct (Zlength c =? bs_expect b) eqn:Ec|]|].
  - (* the model follows *)
    apply Z.eqb_eq in Ec.
    destruct H as (Hpar & Hpre & Hci & Hmr & Hbd & Hfpo & Hstg & Hpcs & Hpcsr & Hsz & Hlay).
    destruct Hpre as (Hexp0 & Hhist & Hosz & _ & _ & _ & _ & _ & _ & Hopos & Hosz30 & Hloc & Hlc & Hbc).
    destruct M as (Mr & Mloc' & Mpre & Mcold & _ & Mok).
    destruct (Mok Herr) as (Mr2 & Me' & Mbt & _).
    destruct Hcnt as (Ccnt & Cbytes & Clen & Ct' & Cmod).
    destruct Hci as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ccst & _).
    assert (Kbtr: 0 <= bv_bt v <= 2).
    { unfold bl_cstage in Ccst. destruct Hstg as [E|E]; rewrite E in Ccst; apply Ccst. }
    destruct (Hmr b Eb) as (R1 & R2 & R3 & R4 & _ & R5).
    assert (R5': bs_hdr b = bv_h v /\ bs_btype b = bv_bt v).
    { destruct Hstg as [E|E]; rewrite E in R5; split; apply R5. }
    destruct R5' as [R6 R7].
    assert (E0: e' = 0).
    { rewrite Me'. destruct (bv_bt v =? 0) eqn:B; [apply Z.eqb_eq in B; rewrite (Mbt B); lia | reflexivity]. }
    pose proof (t34_out_len ba ob opos oc b Hhist Eb ltac:(lia)) as Lo.
    assert (Eds: ds = Zlength (bs_out b)) by (apply t34_vlong_inj; [congruence | lia | rep_lia]).
    assert (Hfol: s34_fol ba c b dm) by (split; [exact Eb | split; [exact Edm | exact Ec]]).
    destruct (t34_step (dmode_of pr) dm b c v ts' cnt R1 Hstg R6 R7 Kbtr (fun x => Cmod b dm x Hfol)
                ltac:(lia)) as [Su|So].
    { intros Elast. rewrite E0 in Hfcs. destruct (Hfcs Elast eq_refl) as [F|F]; [left; exact F | right].
      rewrite <- F, Zlength_app, Clen, Eds. rewrite Z.mod_small by rep_lia. reflexivity. }
    + exists (t34_ba ba None v e' ob opos r). apply Hc; [intros; discriminate|].
      unfold bl_claim_nc. rewrite Eb, Edm. intros _. rewrite Su. exact I.
    + exists (t34_ba ba (Some (bl_set (t34_b1 b ts' cnt) (fst (t34_next v 0)) (snd (t34_next v 0)))) v e' ob opos r).
      apply Hc.
      * intros b' E. injection E as <-. exists b. auto.
      * unfold bl_claim_nc. rewrite Eb, Edm. intros _. rewrite So.
        split; [intros _; split; [lia | split; [exact Ccnt | reflexivity]] | intros; congruence].
  - exists (t34_ba ba None v e' ob opos r). apply Hc; [intros; discriminate|].
    unfold bl_claim_nc. rewrite Eb, Edm. intros E. apply Z.eqb_neq in Ec. contradiction.
  - exists (t34_ba ba None v e' ob opos r). apply Hc; [intros; discriminate|].
    unfold bl_claim_nc. rewrite Eb, Edm. exact I.
  - exists (t34_ba ba None v e' ob opos r). apply Hc; [intros; discriminate|].
    unfold bl_claim_nc. rewrite Eb. exact I.
Qed.

End CM_TPOk_1.
