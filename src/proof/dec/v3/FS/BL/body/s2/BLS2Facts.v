(* FS3-bl BODY stage 2: pure facts of the block-header case (ZSTDds_decodeBlockHeader). *)
Require Export Zstd.proof.dec.v3.FS.BL.body.BLCase.

Section CM_BLS2Facts_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.

(* the stage and expected after a block header of compressed size cs (bp its properties) *)
Definition bh_stg (h: frame_header) (cs: Z) (bp: block_props) : blstage :=
  if cs =? 0 then (if bp_last bp =? 1 then (if fh_checksumFlag h =? 1 then BCk else BHdrPrefix) else BBlkHdr)
  else (if bp_last bp =? 1 then BLastBlk else BBlk).

Definition bh_e (h: frame_header) (cs: Z) (bp: block_props) : Z :=
  if cs =? 0 then (if bp_last bp =? 1 then (if fh_checksumFlag h =? 1 then 4 else 0) else ZSTD_blockHeaderSize)
  else cs.

(* the model's next state *)
Definition bh_next (b: blst) (cs: Z) (bp: block_props) : blst :=
  {| bs_stage := bh_stg (bs_hdr b) cs bp; bs_expect := bh_e (bs_hdr b) cs bp; bs_hbuf := bs_hbuf b;
     bs_hdr := bs_hdr b; bs_ds := bs_ds b; bs_out := bs_out b; bs_btype := bp_type bp; bs_rle := bp_origSize bp |}.

Definition bh_ba (ba: blabs) (ob: val) (opos: Z) (h: frame_header) (cs: Z) (bp: block_props) : blabs :=
  {| ba_dict := ba_dict ba; ba_st := option_map (fun b => bh_next b cs bp) (ba_st ba);
     ba_expect := bh_e h cs bp; ba_out := Some (pair (pair ob (bl_start ba opos)) (opos + 0)) |}.

Definition bh_fs (fs1: fstate) (h: frame_header) (cs: Z) (bp: block_props) : fstate :=
  fsu_stage (fsu_expected (fsu_rleSize (fsu_bType fs1 (Vint (Int.repr (bp_type bp))))
    (vlong (bp_origSize bp))) (vlong (bh_e h cs bp))) (Vint (Int.repr (bl_stz (bh_stg h cs bp)))).

Definition bh_v (v: blv) (cs: Z) (bp: block_props) : blv :=
  {| bv_stage := bh_stg (bv_h v) cs bp; bv_hdr := bv_hdr v; bv_hs := bv_hs v; bv_h := bv_h v;
     bv_bt := bp_type bp; bv_rle := bp_origSize bp |}.

(* an empty last block passes the content size check (in the model's view, when the model describes the frame) *)
Definition bh_fcs_ok (ba: blabs) (h: frame_header) (cs: Z) (bp: block_props) : Prop :=
  cs = 0 -> bp_last bp = 1 -> forall b, ba_st ba = Some b ->
    fh_contentSize h = ZSTD_CONTENTSIZE_UNKNOWN \/ Zlength (bs_out b) = fh_contentSize h.

Lemma bh_fcs_nz ba h cs bp : cs <> 0 -> bh_fcs_ok ba h cs bp.
Proof. intros H E. contradiction. Qed.

Lemma bh_fcs_nl ba h cs bp : bp_last bp = 0 -> bh_fcs_ok ba h cs bp.
Proof. intros H _ E. rewrite H in E. discriminate. Qed.

Lemma bh_step md dm b c cs :
  bs_stage b = BBlkHdr -> cblock_size c = Some cs -> cs <= fh_blockSizeMax (bs_hdr b) ->
  (cs = 0 -> bp_last (block_props_of c) = 1 ->
     fh_contentSize (bs_hdr b) = ZSTD_CONTENTSIZE_UNKNOWN \/ Zlength (bs_out b) = fh_contentSize (bs_hdr b)) ->
  bl_step_nc md dm b c = BLOk (bh_next b cs (block_props_of c)) nil.
Proof.
  intros Es Ec Hc Hf. unfold bl_step_nc. rewrite Es. unfold bl_step. rewrite Es, Ec.
  replace (cs >? fh_blockSizeMax (bs_hdr b)) with false by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
  unfold bh_next, bh_stg, bh_e, bl_frame_end, bl_set.
  destruct (Z.eqb_spec cs 0) as [E0 | E0]; [| reflexivity].
  destruct (Z.eqb_spec (bp_last (block_props_of c)) 1) as [El | El]; [| reflexivity].
  assert (Hk: andb (negb (fh_contentSize (bs_hdr b) =? ZSTD_CONTENTSIZE_UNKNOWN))
                   (negb (Zlength (bs_out b) =? fh_contentSize (bs_hdr b))) = false).
  { destruct (Hf E0 El) as [F | F]; rewrite F, Z.eqb_refl; cbn [negb]; [reflexivity | apply andb_false_r]. }
  rewrite Hk. destruct (fh_checksumFlag _ =? 1); reflexivity.
Qed.

Lemma bh_step_err md dm b c :
  bs_stage b = BBlkHdr ->
  (cblock_size c = None \/ exists cs, cblock_size c = Some cs /\ fh_blockSizeMax (bs_hdr b) < cs) ->
  bl_step_nc md dm b c = BLErr.
Proof.
  intros Es Hc. unfold bl_step_nc. rewrite Es. unfold bl_step. rewrite Es.
  destruct Hc as [-> | (cs & -> & Hl)]; [reflexivity |].
  replace (cs >? fh_blockSizeMax (bs_hdr b)) with true by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_lt; lia).
  reflexivity.
Qed.

Lemma lev_range3 (l: list Z) : bytes_ok l -> 0 <= le_value l < 2 ^ (8 * Zlength l).
Proof.
  intros H. induction H; cbn [le_value].
  - rewrite Zlength_nil. simpl. lia.
  - unfold is_byte in H. rewrite Zlength_cons. replace (8 * Z.succ (Zlength l)) with (8 + 8 * Zlength l) by lia.
    rewrite Z.pow_add_r by (pose proof (Zlength_nonneg l); lia).
    change (2^8) with 256. lia.
Qed.

Lemma lef_range3 (l: list Z) i k : bytes_ok l -> 0 <= k -> 0 <= le_field l i k < 2 ^ (8 * k).
Proof.
  intros H Hk. unfold le_field, slice.
  assert (Hb: bytes_ok (firstn (Z.to_nat k) (skipn (Z.to_nat i) l))).
  { unfold bytes_ok in *. apply Forall_firstn, Forall_skipn; auto. }
  pose proof (lev_range3 _ Hb).
  assert (Zlength (firstn (Z.to_nat k) (skipn (Z.to_nat i) l)) <= k).
  { rewrite Zlength_correct, firstn_length. lia. }
  assert (2 ^ (8 * Zlength (firstn (Z.to_nat k) (skipn (Z.to_nat i) l))) <= 2 ^ (8 * k)).
  { apply Z.pow_le_mono_r; [lia |]. pose proof (Zlength_nonneg (firstn (Z.to_nat k) (skipn (Z.to_nat i) l))). lia. }
  lia.
Qed.

Lemma cblock_size_range3 (u: list Z) k : bytes_ok u -> cblock_size u = Some k -> 0 <= k < 2 ^ 21.
Proof.
  intros Hb Hc. unfold cblock_size in Hc.
  destruct (Zlength u <? ZSTD_blockHeaderSize); [discriminate |].
  destruct (bp_type (block_props_of u) =? 1); [inv Hc; lia |].
  destruct (bp_type (block_props_of u) =? 3); [discriminate |]. inv Hc.
  unfold block_props_of; simpl. pose proof (lef_range3 u 0 3 Hb ltac:(lia)).
  rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia |].
  apply Z.div_lt_upper_bound; [lia |]. change (2 ^ 3 * 2 ^ 21) with (2 ^ (8 * 3)). lia.
Qed.

Lemma bp_orig_range (u: list Z) : bytes_ok u -> 0 <= bp_origSize (block_props_of u) < 2 ^ 21.
Proof.
  intros Hb. unfold block_props_of; simpl. pose proof (lef_range3 u 0 3 Hb ltac:(lia)).
  rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia |].
  apply Z.div_lt_upper_bound; [lia |]. change (2 ^ 3 * 2 ^ 21) with (2 ^ (8 * 3)). lia.
Qed.

Lemma bp_last01_3 (u: list Z) : bp_last (block_props_of u) = 0 \/ bp_last (block_props_of u) = 1.
Proof.
  unfold block_props_of; simpl.
  assert (Z.land (le_field u 0 3) 1 = le_field u 0 3 mod 2) as -> by (apply (Z.land_ones _ 1); lia).
  pose proof (Z.mod_pos_bound (le_field u 0 3) 2). lia.
Qed.

Lemma bp_type_range (u: list Z) k : cblock_size u = Some k -> 0 <= bp_type (block_props_of u) <= 2.
Proof.
  intros Hc.
  assert (0 <= bp_type (block_props_of u) <= 3).
  { unfold block_props_of; simpl.
    assert (Z.land (Z.shiftr (le_field u 0 3) 1) 3 = Z.shiftr (le_field u 0 3) 1 mod 2 ^ 2) as ->
      by (apply (Z.land_ones _ 2); lia).
    pose proof (Z.mod_pos_bound (Z.shiftr (le_field u 0 3) 1) (2 ^ 2)). lia. }
  unfold cblock_size in Hc.
  destruct (Zlength u <? ZSTD_blockHeaderSize); [discriminate |].
  destruct (bp_type (block_props_of u) =? 1) eqn:E1; [apply Z.eqb_eq in E1; lia |].
  destruct (bp_type (block_props_of u) =? 3) eqn:E3; [discriminate |]. apply Z.eqb_neq in E3. lia.
Qed.

Lemma bp_type1 (u: list Z) k : cblock_size u = Some k -> bp_type (block_props_of u) = 1 -> k = 1.
Proof.
  unfold cblock_size. destruct (Zlength u <? ZSTD_blockHeaderSize); [discriminate |].
  intros Hc E. rewrite E in Hc. inv Hc. reflexivity.
Qed.

Lemma cont_fields fs d n :
  let f := continuity fs d n in
  fs_expected f = fs_expected fs /\ fs_fParams f = fs_fParams fs /\
  fs_processedCSize f = fs_processedCSize fs /\ fs_decodedSize f = fs_decodedSize fs /\
  fs_bType f = fs_bType fs /\ fs_stage f = fs_stage fs /\ fs_xxh f = fs_xxh fs /\
  fs_headerSize f = fs_headerSize fs /\ fs_validateChecksum f = fs_validateChecksum fs /\
  fs_rleSize f = fs_rleSize fs /\ fs_isFrameDecompression f = fs_isFrameDecompression fs /\
  fs_dictID f = fs_dictID fs /\ fs_ddictIsCold f = fs_ddictIsCold fs.
Proof. unfold continuity. destruct (cont_moves fs d n); repeat split; reflexivity. Qed.

Lemma bl_lay_ext od o ba ba' fs fs' :
  bl_lay od o ba fs -> ba_out ba' = ba_out ba ->
  fs_previousDstEnd fs' = fs_previousDstEnd fs -> fs_prefixStart fs' = fs_prefixStart fs ->
  fs_virtualStart fs' = fs_virtualStart fs -> fs_dictEnd fs' = fs_dictEnd fs ->
  fs_gpDictCopy fs' = fs_gpDictCopy fs -> bl_lay od o ba' fs'.
Proof. intros H E1 E2 E3 E4 E5 E6. unfold bl_lay in *. rewrite E1, E2, E3, E4, E5, E6. exact H. Qed.

Lemma bh_cold fs ob osz opos pcs n : cold01 fs -> cold01 (bl_fs1 fs ob osz opos pcs n).
Proof.
  unfold cold01, bl_fs1. intros H. cbn [fs_ddictIsCold fsu_processedCSize].
  destruct (cont_fields fs (offset_val opos ob) (osz - opos)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E).
  rewrite E. exact H.
Qed.

(* the error returns: the model errs too *)
Lemma bh_err_claim md ba c r opos osz oc fs ts v :
  bl_mrel md ba fs ts v -> bv_stage v = BBlkHdr -> is_error_code r = true ->
  (cblock_size c = None \/ exists cs, cblock_size c = Some cs /\ fh_blockSizeMax (bv_h v) < cs) ->
  bl_claim_nc md ba ba c r opos osz oc.
Proof.
  intros Hm Hv Er Hc. unfold bl_claim_nc. destruct (ba_st ba) as [b |] eqn:B; auto.
  destruct (dictref_model (ba_dict ba)) as [dm |]; auto. intros _.
  destruct (Hm b B) as (Es & _ & _ & _ & _ & M). rewrite Hv in Es, M. destruct M as [Eh _].
  rewrite bh_step_err; auto. rewrite Eh. exact Hc.
Qed.

(* an empty last block of a frame whose content differs from its declared size: the model errs too *)
Lemma bh_err_fcs_claim md ba c r opos osz oc fs ts v :
  bl_mrel md ba fs ts v -> bv_stage v = BBlkHdr -> is_error_code r = true ->
  cblock_size c = Some 0 -> bp_last (block_props_of c) = 1 ->
  fh_contentSize (bv_h v) <> ZSTD_CONTENTSIZE_UNKNOWN ->
  (forall b, ba_st ba = Some b -> Zlength (bs_out b) <> fh_contentSize (bv_h v)) ->
  bl_claim_nc md ba ba c r opos osz oc.
Proof.
  intros Hm Hv Er Ec El Hu Hn. unfold bl_claim_nc. destruct (ba_st ba) as [b |] eqn:B; auto.
  destruct (dictref_model (ba_dict ba)) as [dm |]; auto. intros _.
  destruct (Hm b B) as (Es & _ & _ & _ & _ & M). rewrite Hv in Es, M. destruct M as [Eh _].
  unfold bl_step_nc. rewrite Es. unfold bl_step. rewrite Es, Ec. cbv zeta. rewrite El, Eh.
  destruct (0 >? fh_blockSizeMax (bv_h v)); [exact Er |]. rewrite !Z.eqb_refl.
  replace (fh_contentSize (bv_h v) =? ZSTD_CONTENTSIZE_UNKNOWN) with false by (symmetry; apply Z.eqb_neq; exact Hu).
  replace (Zlength (bs_out b) =? fh_contentSize (bv_h v)) with false
    by (symmetry; apply Z.eqb_neq; apply Hn; reflexivity).
  exact Er.
Qed.

(* the frame's content so far fits in the output buffer *)
Lemma bl_out_len ba ob opos oc b :
  bl_hist_ok ba ob opos oc -> 0 <= opos <= Zlength oc -> ba_st ba = Some b -> Zlength (bs_out b) <= Zlength oc.
Proof.
  intros Hh Ho B. unfold bl_hist_ok in Hh. rewrite B in Hh.
  destruct (ba_out ba) as [[[ob' f] pe] |].
  - destruct Hh as (_ & -> & Hf & E). apply (f_equal (@Zlength val)) in E.
    rewrite Zlength_sublist, Zlength_map in E by lia. lia.
  - rewrite Hh, Zlength_nil. lia.
Qed.

(* the test of the content size check: t'10 = (fcs != -1) ? (decodedSize != fcs) : 0 *)
Definition bh_fcs_t (f a: Z) : Z := if f =? 2 ^ 64 - 1 then 0 else if a mod 2 ^ 64 =? f then 0 else 1.

Lemma bh_fcs_then a f : 0 <= f < 2 ^ 64 -> Int64.repr f <> Int64.repr (- (1)) ->
  Vint (Int.repr (bh_fcs_t f a)) = bool2val (Int64.cmpu Cne (Int64.repr a) (Int64.repr f)).
Proof.
  intros Hf Hn. unfold bh_fcs_t.
  assert (Hne: f <> 2 ^ 64 - 1).
  { intros ->. apply Hn. apply Int64.eqm_samerepr. exists 1. reflexivity. }
  rewrite (proj2 (Z.eqb_neq _ _) Hne). unfold Int64.cmpu, Int64.eq. rewrite !Int64.unsigned_repr_eq.
  change Int64.modulus with (2 ^ 64). rewrite (Z.mod_small f) by lia.
  destruct (zeq (a mod 2 ^ 64) f), (Z.eqb_spec (a mod 2 ^ 64) f); simpl; auto; congruence.
Qed.

Lemma bh_fcs_else a f : 0 <= f < 2 ^ 64 -> Int64.repr f = Int64.repr (- (1)) -> bh_fcs_t f a = 0.
Proof.
  intros Hf He. unfold bh_fcs_t. apply (f_equal Int64.unsigned) in He.
  rewrite Int64.unsigned_repr in He by (unfold Int64.max_unsigned; simpl; lia).
  rewrite He. reflexivity.
Qed.

Lemma bh_fcs_01 a f : bh_fcs_t f a = 0 \/ bh_fcs_t f a = 1.
Proof. unfold bh_fcs_t. repeat destruct (_ =? _); auto. Qed.

(* the test passes: no declared size, or the decoded size ds (a 64-bit value) is the declared one *)
Lemma bh_fcs_pass a f : 0 <= a < 2 ^ 64 -> bh_fcs_t f a = 0 -> f = ZSTD_CONTENTSIZE_UNKNOWN \/ a = f.
Proof.
  unfold bh_fcs_t, ZSTD_CONTENTSIZE_UNKNOWN. intros Ha. destruct (Z.eqb_spec f (2 ^ 64 - 1)); [auto |].
  destruct (Z.eqb_spec (a mod 2 ^ 64) f); [| discriminate]. rewrite Z.mod_small in e by lia. auto.
Qed.

Lemma bh_fcs_fail a f : 0 <= a < 2 ^ 64 -> bh_fcs_t f a <> 0 -> f <> ZSTD_CONTENTSIZE_UNKNOWN /\ a <> f.
Proof.
  unfold bh_fcs_t, ZSTD_CONTENTSIZE_UNKNOWN. intros Ha. destruct (Z.eqb_spec f (2 ^ 64 - 1)); [congruence |].
  destruct (Z.eqb_spec (a mod 2 ^ 64) f); [congruence |]. rewrite Z.mod_small in n0 by lia. auto.
Qed.

Lemma bh_cstage md v fs1 hb cs bp :
  hdr_fields (md_ignore md) v fs1 -> 0 <= cs < 2 ^ 21 -> cs <= fh_blockSizeMax (bv_h v) ->
  0 <= bp_type bp <= 2 -> 0 <= bp_origSize bp < 2 ^ 21 -> (bp_type bp = 1 -> cs = 1) ->
  bl_cstage md (bh_v v cs bp) (bh_e (bv_h v) cs bp) (bh_fs fs1 (bv_h v) cs bp) hb.
Proof.
  intros Hh Hcs Hcb Hbt Hor Ht1.
  assert (Hh': hdr_fields (md_ignore md) (bh_v v cs bp) (bh_fs fs1 (bv_h v) cs bp)).
  { unfold hdr_fields, bh_v, bh_fs in *. cbn [bv_h fs_fParams fs_validateChecksum fs_xxh fsu_stage fsu_expected
      fsu_rleSize fsu_bType]. exact Hh. }
  unfold bl_cstage. cbn [bv_stage bh_v]. unfold bh_stg, bh_e.
  destruct (Z.eqb_spec cs 0) as [E0 | E0].
  - destruct (bp_last bp =? 1).
    + destruct (fh_checksumFlag (bv_h v) =? 1) eqn:Ec.
      * split; [exact Hh' | split; [apply Z.eqb_eq; exact Ec | reflexivity]].
      * left; reflexivity.
    + split; [exact Hh' | reflexivity].
  - assert (B: hdr_fields (md_ignore md) (bh_v v cs bp) (bh_fs fs1 (bv_h v) cs bp) /\
      fs_bType (bh_fs fs1 (bv_h v) cs bp) = Vint (Int.repr (bv_bt (bh_v v cs bp))) /\
      0 <= bv_bt (bh_v v cs bp) <= 2 /\
      fs_rleSize (bh_fs fs1 (bv_h v) cs bp) = vlong (bv_rle (bh_v v cs bp)) /\
      0 <= bv_rle (bh_v v cs bp) < 2 ^ 21 /\ 0 < cs <= fh_blockSizeMax (bv_h (bh_v v cs bp)) /\
      (bv_bt (bh_v v cs bp) = 1 -> cs = 1)).
    { cbn [bh_v bv_bt bv_rle bv_h]. split; [exact Hh' |]. split; [reflexivity |]. split; [lia |].
      split; [reflexivity |]. split; [lia |]. split; [lia | exact Ht1]. }
    destruct (bp_last bp =? 1); exact B.
Qed.

Lemma bh_e_range h cs bp : 0 <= cs < 2 ^ 21 -> 0 <= bh_e h cs bp < 2 ^ 32.
Proof.
  intros. unfold bh_e, ZSTD_blockHeaderSize.
  destruct (cs =? 0); [destruct (bp_last bp =? 1); [destruct (fh_checksumFlag h =? 1) |] |]; lia.
Qed.

Lemma bh_ok_post md od osz0 ba fs ts hb v W shk shd ob osz opos oc shs src c pcs cs :
  bl_pre_ok W od osz0 ba shk shd ob osz opos oc shs src c ->
  bl_cinv md od osz0 ba fs hb v -> bl_mrel md ba fs ts v -> bd_model_ok (ba_dict ba) od ->
  bv_stage v = BBlkHdr -> fs_processedCSize fs = vlong pcs -> 0 <= pcs <= Int64.max_unsigned ->
  cblock_size c = Some cs -> cs <= fh_blockSizeMax (bv_h v) ->
  bl_lay od osz (bl_moved ba ob opos) (continuity fs (offset_val opos ob) (osz - opos)) ->
  bh_fcs_ok ba (bv_h v) cs (block_props_of c) ->
  cold01 (bh_fs (bl_fs1 fs ob osz opos pcs (Zlength c)) (bv_h v) cs (block_props_of c)) /\
  (is_error_code 0 = false ->
     0 <= osz - opos /\ cells_bytes (sublist opos (opos + 0) oc) /\
     ba_dict (bh_ba ba ob opos (bv_h v) cs (block_props_of c)) = ba_dict ba /\
     ba_out (bh_ba ba ob opos (bv_h v) cs (block_props_of c)) = Some (pair (pair ob (bl_start ba opos)) (opos + 0)%Z) /\
     bl_hist_ok (bh_ba ba ob opos (bv_h v) cs (block_props_of c)) ob (opos + 0) oc /\
     (forall b', ba_st (bh_ba ba ob opos (bv_h v) cs (block_props_of c)) = Some b' ->
        ba_expect (bh_ba ba ob opos (bv_h v) cs (block_props_of c)) = bs_expect b') /\
     exists ts', TInit (bd_oxo od) ts = TInit (bd_oxo od) ts' /\
       BRc md od osz (bh_ba ba ob opos (bv_h v) cs (block_props_of c))
         (bh_fs (bl_fs1 fs ob osz opos pcs (Zlength c)) (bv_h v) cs (block_props_of c)) ts' hb) /\
  bl_claim_nc md ba (bh_ba ba ob opos (bv_h v) cs (block_props_of c)) c 0 opos osz oc.
Proof.
  intros Hpre Hci Hmr Hmd Hv Hpcs Hpcsr Ec Hcb Hlay Hfcs.
  destruct Hpre as (Hne & Hhist & Hosz & _ & _ & _ & _ & _ & _ & Hop & _ & Hoc & _ & Hbc).
  destruct Hci as (Hexp & Her & Hst & Hifd & Hcold & Hdid & Hpcs0 & Hds & Hhb & Hwf & Hcs & Hlay0).
  cbv [bl_cstage] in Hcs. rewrite Hv in Hcs. destruct Hcs as [Hhf He3].
  pose proof (cblock_size_range3 _ _ Hbc Ec) as Hcsr.
  pose proof (bp_orig_range _ Hbc) as Hor.
  pose proof (bp_type_range _ _ Ec) as Hbt.
  pose proof (bp_type1 _ _ Ec) as Ht1.
  set (bp := block_props_of c) in *.
  set (fs1 := bl_fs1 fs ob osz opos pcs (Zlength c)).
  destruct (cont_fields fs (offset_val opos ob) (osz - opos))
    as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13).
  assert (Hhf1: hdr_fields (md_ignore md) v fs1).
  { unfold hdr_fields in *. subst fs1. unfold bl_fs1, fsu_processedCSize. cbn [fs_fParams fs_validateChecksum fs_xxh].
    rewrite C2, C9, C7. exact Hhf. }
  (* the model's view of the state before *)
  assert (Hmb: forall b, ba_st ba = Some b ->
            bs_stage b = BBlkHdr /\ bs_expect b = ba_expect ba /\ bs_ds b = ts /\
            fs_decodedSize fs = vlong (Zlength (bs_out b)) /\ bytes_ok (bs_out b) /\ bs_hdr b = bv_h v /\
            (bl_val (md_ignore md) (bv_h v) = true -> fs_xxh fs = Some (bs_out b))).
  { intros b B. destruct (Hmr b B) as (Es & Ee & Eds & Edec & Ebo & M). rewrite Hv in Es, M.
    destruct M as [Eh Ex]. repeat split; auto. }
  split; [apply (bh_cold fs ob osz opos pcs (Zlength c)) in Hcold; exact Hcold |].
  split.
  2:{ unfold bl_claim_nc. destruct (ba_st ba) as [b |] eqn:B; auto.
      destruct (dictref_model (ba_dict ba)) as [dm |]; auto. intros _.
      destruct (Hmb b eq_refl) as (Es & _ & _ & _ & _ & Eh & _).
      rewrite (bh_step md dm b c cs Es Ec ltac:(rewrite Eh; exact Hcb)
        ltac:(rewrite Eh; intros E0 E1; exact (Hfcs E0 E1 b B))).
      split; [| intros X; vm_compute in X; discriminate X].
      intros _. split; [reflexivity |]. split; [rewrite Z.add_0_r, sublist_nil; reflexivity |].
      unfold bh_ba. rewrite B. reflexivity. }
  intros _.
  split; [lia |].
  split; [rewrite Z.add_0_r, sublist_nil; exists nil; split; [reflexivity | constructor] |].
  split; [reflexivity |]. split; [reflexivity |].
  split.
  { unfold bl_hist_ok, bh_ba. cbn [ba_out ba_st]. rewrite Z.add_0_r.
    unfold bl_hist_ok, bl_start in *.
    destruct (ba_out ba) as [[[ob' f] pe] |] eqn:Bo.
    - destruct Hhist as (-> & -> & Hf & M). split; [auto |]. split; [auto |]. split; [lia |].
      destruct (ba_st ba) as [b |]; cbn [option_map]; [exact M | exact M].
    - split; [auto |]. split; [auto |]. split; [lia |]. rewrite sublist_nil.
      destruct (ba_st ba) as [b |]; cbn [option_map bh_next bs_out].
      + rewrite Hhist. reflexivity.
      + exists nil; split; [reflexivity | constructor]. }
  split.
  { unfold bh_ba. cbn [ba_st ba_expect]. intros b' Eb'.
    destruct (ba_st ba) as [b |] eqn:B; cbn [option_map] in Eb'; [| discriminate].
    injection Eb' as <-. destruct (Hmb b eq_refl) as (_ & _ & _ & _ & _ & Eh & _).
    unfold bh_next; cbn [bs_expect]. rewrite Eh. reflexivity. }
  exists ts. split; [reflexivity |].
  exists (bh_v v cs bp). split; [| split].
  - (* bl_cinv *)
    unfold bl_cinv.
    split; [reflexivity |]. split; [apply bh_e_range; lia |]. split; [reflexivity |].
    unfold bh_fs. cbn [fs_isFrameDecompression fs_ddictIsCold fs_dictID fs_processedCSize fs_decodedSize
      fsu_stage fsu_expected fsu_rleSize fsu_bType].
    subst fs1. unfold bl_fs1, fsu_processedCSize at 1 2 3 4 5.
    cbn [fs_isFrameDecompression fs_ddictIsCold fs_dictID fs_processedCSize fs_decodedSize].
    rewrite C11, C12, C4.
    split; [exact Hifd |].
    split; [unfold cold01; cbn [fs_ddictIsCold]; rewrite C13; exact Hcold |].
    split; [exact Hdid |].
    split.
    { exists (Int64.unsigned (Int64.repr (pcs + Zlength c))). split.
      - unfold vlong. rewrite Int64.repr_unsigned. reflexivity.
      - pose proof (Int64.unsigned_range_2 (Int64.repr (pcs + Zlength c))). lia. }
    split; [exact Hds |]. split; [exact Hhb |]. split; [exact Hwf |].
    split.
    + apply bh_cstage; auto; lia.
    + eapply bl_lay_ext; [exact Hlay | | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity].
      unfold bh_ba, bl_moved. cbn [ba_out]. rewrite Z.add_0_r. reflexivity.
  - (* bl_mrel *)
    intros b' Eb'. unfold bh_ba in Eb'. cbn [ba_st] in Eb'.
    destruct (ba_st ba) as [b |] eqn:B; cbn [option_map] in Eb'; [| discriminate].
    injection Eb' as <-. destruct (Hmb b eq_refl) as (Es & Ee & Eds & Edec & Ebo & Eh & Ex).
    unfold bh_next, bh_v. cbn [bs_stage bs_expect bs_ds bs_out bs_hdr bs_btype bs_rle bv_stage bv_h bv_bt bv_rle].
    rewrite Eh.
    split; [reflexivity |]. split; [reflexivity |]. split; [exact Eds |].
    assert (Ex1: bl_val (md_ignore md) (bv_h v) = true -> fs_xxh (bh_fs fs1 (bv_h v) cs bp) = Some (bs_out b)).
    { intros X. unfold bh_fs; cbn [fs_xxh fsu_stage fsu_expected fsu_rleSize fsu_bType].
      subst fs1. unfold bl_fs1, fsu_processedCSize. cbn [fs_xxh]. rewrite C7. auto. }
    split.
    { unfold bh_fs; cbn [fs_decodedSize fsu_stage fsu_expected fsu_rleSize fsu_bType].
      subst fs1. unfold bl_fs1, fsu_processedCSize. cbn [fs_decodedSize]. rewrite C4. exact Edec. }
    split; [exact Ebo |].
    unfold bh_stg, bh_e.
    destruct (cs =? 0); [destruct (bp_last bp =? 1); [destruct (fh_checksumFlag (bv_h v) =? 1) |] |].
    all: try (split; [reflexivity | exact Ex1]).
    all: try exact I.
    all: try (intros X; exfalso; apply X; reflexivity).
    all: destruct (bp_last bp =? 1); cbn iota; repeat split; auto.
  - exact Hmd.
Qed.

(* the globals, folded back after a read of one of them *)
Section G.
Local Open Scope logic.
Lemma zstd_globals_fold3 gv :
  data_at Ews tint g_debuglevel_val (gv _g_debuglevel) *
  data_at Ers (tarray tuint 32) DeBruijnBytePos_val (gv _DeBruijnBytePos) *
  data_at Ers (tarray tuint 32) DeBruijnClz_val (gv _DeBruijnClz) *
  data_at Ers tulong zeroFilled_val (gv _zeroFilled) *
  data_at Ers (Tstruct ___gp_ZSTD_customMem noattr) ZSTD_defaultCMem_val (gv _ZSTD_defaultCMem) *
  data_at Ers (tarray tuint 3) repStartValue_val (gv _repStartValue) *
  data_at Ers (tarray tulong 4) ZSTD_fcs_fieldSize_val (gv _ZSTD_fcs_fieldSize) *
  data_at Ers (tarray tulong 4) ZSTD_did_fieldSize_val (gv _ZSTD_did_fieldSize) *
  data_at Ers tulong ZSTD_blockHeaderSize_val (gv _ZSTD_blockHeaderSize) *
  data_at Ers (tarray tuchar 36) LL_bits_val (gv _LL_bits) *
  data_at Ers (tarray tuchar 53) ML_bits_val (gv _ML_bits) *
  data_at Ers (tarray (tarray (Tstruct ___gp_algo_time_t noattr) 2) 16) algoTime_val (gv _algoTime) *
  data_at Ers (tarray tuint 36) LL_base_val (gv _LL_base) *
  data_at Ers (tarray tuint 32) OF_base_val (gv _OF_base) *
  data_at Ers (tarray tuchar 32) OF_bits_val (gv _OF_bits) *
  data_at Ers (tarray tuint 53) ML_base_val (gv _ML_base) *
  data_at Ers (tarray (Tstruct ___gp_ZSTD_seqSymbol noattr) 65) LL_defaultDTable_val (gv _LL_defaultDTable) *
  data_at Ers (tarray (Tstruct ___gp_ZSTD_seqSymbol noattr) 33) OF_defaultDTable_val (gv _OF_defaultDTable) *
  data_at Ers (tarray (Tstruct ___gp_ZSTD_seqSymbol noattr) 65) ML_defaultDTable_val (gv _ML_defaultDTable) *
  data_at Ers (tarray tuint 8) dec32table_val (gv _dec32table) *
  data_at Ers (tarray tint 8) dec64table_val (gv _dec64table) * eb_res gv |-- zstd_globals gv.
Proof. unfold zstd_globals. cancel. Qed.

(* the frame group without the five fields the block-header case touches *)
Definition fc2_rest (p: val) (fs: fstate) (pr: dparams) : mpred :=
  cfg_fmt p (dp_fmt pr) * cfg_lit p *
  field_at Ews t_dctx (DOT _previousDstEnd) (fs_previousDstEnd fs) p *
  field_at Ews t_dctx (DOT _gpDictCopy) (fs_gpDictCopy fs) p *
  field_at Ews t_dctx (DOT _prefixStart) (fs_prefixStart fs) p *
  field_at Ews t_dctx (DOT _virtualStart) (fs_virtualStart fs) p *
  field_at Ews t_dctx (DOT _dictEnd) (fs_dictEnd fs) p *
  field_at Ews t_dctx (DOT _processedCSize) (fs_processedCSize fs) p *
  field_at Ews t_dctx (DOT _decodedSize) (fs_decodedSize fs) p *
  xxh_field p (fs_xxh fs) *
  field_at Ews t_dctx (DOT _headerSize) (fs_headerSize fs) p *
  field_at Ews t_dctx (DOT _validateChecksum) (fs_validateChecksum fs) p *
  field_at Ews t_dctx (DOT _isFrameDecompression) (fs_isFrameDecompression fs) p *
  field_at Ews t_dctx (DOT _dictID) (fs_dictID fs) p *
  field_at Ews t_dctx (DOT _ddictIsCold) (fs_ddictIsCold fs) p *
  field_at Ews t_dctx (DOT _forceIgnoreChecksum) (Vint (Int.repr (dp_ignore pr))) p *
  field_at Ews t_dctx (DOT _maxBlockSizeParam) (Vint (Int.repr (dp_bmax pr))) p *
  field_at Ews t_dctx (DOT _refMultipleDDicts) (Vint (Int.repr (dp_multi pr))) p *
  field_at Ews t_dctx (DOT _ddictSet) nullval p.

(* fc2_rest unfolded (its fields read one by one) and folded back *)
Lemma fc2_rest_fold p fs pr :
  ltac:(let t := eval cbv delta [fc2_rest] beta in (fc2_rest p fs pr) in exact (t |-- fc2_rest p fs pr)).
Proof. apply derives_refl. Qed.

Lemma fcore3_split2 p fs pr f :
  fs_fParams fs = f ->
  fcore3 p fs pr nullval |--
  !! par_ok pr && (field_at Ews t_dctx (DOT _stage) (fs_stage fs) p * field_at Ews t_dctx (DOT _bType) (fs_bType fs) p *
                   field_at Ews t_dctx (DOT _expected) (fs_expected fs) p *
                   field_at Ews t_dctx (DOT _rleSize) (fs_rleSize fs) p *
                   field_at Ews t_dctx (DOT _fParams) f p * fc2_rest p fs pr).
Proof. intros <-. unfold fcore3, fc2_rest, frame_fields. entailer!. Qed.

Lemma fcore3_join2 p fs1 fs' pr f vst vbt vex vrl :
  par_ok pr -> fs_fParams fs' = f -> fs_stage fs' = vst -> fs_bType fs' = vbt -> fs_expected fs' = vex ->
  fs_rleSize fs' = vrl -> fc2_rest p fs' pr = fc2_rest p fs1 pr ->
  field_at Ews t_dctx (DOT _stage) vst p * field_at Ews t_dctx (DOT _bType) vbt p *
  field_at Ews t_dctx (DOT _expected) vex p * field_at Ews t_dctx (DOT _rleSize) vrl p *
  field_at Ews t_dctx (DOT _fParams) f p * fc2_rest p fs1 pr |-- fcore3 p fs' pr nullval.
Proof.
  intros Hp <- <- <- <- <- E. rewrite <- E. unfold fcore3, fc2_rest, frame_fields. entailer!.
Qed.
End G.

End CM_BLS2Facts_1.

Ltac head_dw0 c :=
  lazymatch c with Sloop _ Sbreak => idtac | Ssequence ?a _ => head_dw0 a end.
Ltac dw0 :=
  match goal with |- semax _ ?P ?c _ => head_dw0 c;
    first [ forward_loop P break: P; [entailer! | forward; entailer! | ]
          | forward_loop P break: P;
            [entailer! | forward_if P; [exfalso; lia | forward; entailer! | forward; entailer!] | ] ] end.

Section CM_BLS2Facts_2.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.

(* DEBUGLOG's do { } while (0) loops, for any state *)
Section DW.
Local Open Scope logic.
Context {Espec: OracleKind}.

Lemma dw_skip Delta P c R :
  semax Delta P c R -> semax Delta P (Ssequence (Sloop Sskip Sbreak) c) R.
Proof.
  intros H.
  destruct R as [Rn Rb Rc Rr]. apply semax_seq with (Q := P); [| exact H]. apply semax_loop with (Q' := P).
  - eapply semax_post; [ | | | | apply semax_skip]; intros; simpl.
    all: intros x; apply andp_left2; first [apply derives_refl | apply prop_left; intros []].
  - eapply semax_pre; [| apply semax_break]. simpl. intros x; apply andp_left2, derives_refl.
Qed.

Lemma dw_if0 Delta P s c R :
  semax Delta P c R ->
  semax Delta P (Ssequence (Sloop (Sifthenelse (Econst_int (Int.repr 0) tint) s Sskip) Sbreak) c) R.
Proof.
  intros H.
  destruct R as [Rn Rb Rc Rr]. apply semax_seq with (Q := P); [| exact H]. apply semax_loop with (Q' := P).
  - eapply semax_pre; [| apply semax_ifthenelse; [reflexivity | |]].
    + intros x. simpl. eapply derives_trans; [| apply now_later].
      apply andp_right; [| apply andp_left2, derives_refl]. unfold tc_expr; simpl. apply prop_right; auto.
    + eapply semax_pre with (P' := FF); [| apply semax_ff]. intros x. simpl. apply andp_left2, andp_left2.
      unfold local, lift1, liftx; simpl. apply prop_left; intros Ht. vm_compute in Ht. discriminate Ht.
    + eapply semax_post; [ | | | | apply semax_skip]; intros; simpl.
      all: intros x; apply andp_left2; first [apply andp_left1, derives_refl | apply prop_left; intros []].
  - eapply semax_pre; [| apply semax_break]. simpl. intros x; apply andp_left2, derives_refl.
Qed.

End DW.

End CM_BLS2Facts_2.

Ltac dwq := first [apply dw_skip | apply dw_if0 | apply -> seq_assoc; first [apply dw_skip | apply dw_if0]].

