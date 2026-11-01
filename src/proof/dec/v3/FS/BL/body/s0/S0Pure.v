(* FS3-bl BODY stage 0: the pure part of the POST of ZSTDds_getFrameHeaderSize (model step to BSkipHdr
   or BHdrRest). *)
Require Export Zstd.proof.dec.v3.FS.BL.body.s0.S0Help.
Local Open Scope logic.

Section CM_S0Pure_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* the skippable branch of the C (zstd1 format and a skippable magic number) *)
Definition s0_skip (mg: bool) (c: list Z) : bool := andb (negb mg) (is_skippable_magic (le_field c 0 4)).

(* Params.bl_step at BHdrPrefix *)
Definition s0_step (mg: bool) (b: blst) (c: list Z) : blst :=
  if s0_skip mg c then
    {| bs_stage := BSkipHdr; bs_expect := ZSTD_SKIPPABLEHEADERSIZE - Zlength c; bs_hbuf := c;
       bs_hdr := bs_hdr b; bs_ds := bs_ds b; bs_out := bs_out b; bs_btype := 0; bs_rle := 0 |}
  else
    {| bs_stage := BHdrRest; bs_expect := header_size_m mg c - Zlength c; bs_hbuf := c;
       bs_hdr := bs_hdr b; bs_ds := bs_ds b; bs_out := bs_out b; bs_btype := 0; bs_rle := 0 |}.

Lemma s0_step_eq md dm b c :
  bs_stage b = BHdrPrefix -> bl_step_nc md dm b c = BLOk (s0_step (md_magicless md) b c) nil.
Proof. intros H. unfold bl_step_nc, bl_step, s0_step, s0_skip. rewrite H. destruct (andb _ _); reflexivity. Qed.

Definition s0_e (mg: bool) (c: list Z) : Z :=
  if s0_skip mg c then ZSTD_SKIPPABLEHEADERSIZE - Zlength c else header_size_m mg c - Zlength c.

Definition s0_ba (mg: bool) (ba: blabs) (c: list Z) (ob: val) (opos: Z) : blabs :=
  {| ba_dict := ba_dict ba; ba_st := option_map (fun b => s0_step mg b c) (ba_st ba); ba_expect := s0_e mg c;
     ba_out := Some (ob, bl_start ba opos, opos) |}.

(* headerSize after the call: unchanged in the skippable branch *)
Definition s0_hsv (mg: bool) (c: list Z) (h: val) : val := if s0_skip mg c then h else vlong (header_size_m mg c).

Definition s0_stv (mg: bool) (c: list Z) : val := Vint (Int.repr (if s0_skip mg c then 6 else 1)).

Definition s0_fs' (mg: bool) (fs: fstate) (ob: val) (osz opos pcs: Z) (c: list Z) : fstate :=
  let fs1 := bl_fs1 fs ob osz opos pcs (Zlength c) in
  s0_fs fs1 (s0_hsv mg c (fs_headerSize fs1)) (vlong (s0_e mg c)) (s0_stv mg c).

Lemma s0_cont_eq fs d n :
  fs_ddictIsCold (continuity fs d n) = fs_ddictIsCold fs /\
  fs_isFrameDecompression (continuity fs d n) = fs_isFrameDecompression fs /\
  fs_dictID (continuity fs d n) = fs_dictID fs /\
  fs_decodedSize (continuity fs d n) = fs_decodedSize fs.
Proof. unfold continuity. destruct (cont_moves fs d n); repeat split; reflexivity. Qed.

Lemma s0_e_range mg c : Zlength c = starting_len mg -> 0 <= s0_e mg c < 2 ^ 32.
Proof.
  intros H. unfold s0_e, s0_skip. destruct mg; cbn [negb andb].
  - pose proof (s0_hs_range true c). unfold starting_len in *. lia.
  - destruct (is_skippable_magic _).
    + rewrite H. cbv. split; congruence.
    + pose proof (s0_hs_range false c). unfold starting_len in *. change ZSTD_FRAMEHEADERSIZE_PREFIX with 5 in *. lia.
Qed.

Lemma s0_lay_ext od osz ba f1 f2 :
  fs_previousDstEnd f2 = fs_previousDstEnd f1 -> fs_prefixStart f2 = fs_prefixStart f1 ->
  fs_virtualStart f2 = fs_virtualStart f1 -> fs_dictEnd f2 = fs_dictEnd f1 -> fs_gpDictCopy f2 = fs_gpDictCopy f1 ->
  bl_lay od osz ba f1 -> bl_lay od osz ba f2.
Proof. intros E1 E2 E3 E4 E5. unfold bl_lay. rewrite E1, E2, E3, E4, E5. auto. Qed.

Lemma s0_lay_ba od osz ba1 ba2 f : ba_out ba2 = ba_out ba1 -> bl_lay od osz ba1 f -> bl_lay od osz ba2 f.
Proof. intros E. unfold bl_lay. rewrite E. auto. Qed.

Lemma s0_post_pure md od osz osz0 ba fs ts hb v ob opos oc c pcs :
  bl_hist_ok ba ob opos oc -> 0 <= opos <= osz -> Zlength oc = osz ->
  bl_cinv md od osz0 ba fs hb v -> bl_mrel md ba fs ts v -> bd_model_ok (ba_dict ba) od ->
  bv_stage v = BHdrPrefix -> Zlength c = starting_len (md_magicless md) -> bytes_ok c ->
  bl_lay od osz (bl_moved ba ob opos) (continuity fs (offset_val opos ob) (osz - opos)) ->
  ba_expect ba <> 0 ->
  let mg := md_magicless md in
  let ba' := s0_ba mg ba c ob opos in
  let fs' := s0_fs' mg fs ob osz opos pcs c in
  let a := 0 in
  0 <= a <= Int64.max_unsigned /\
  Zlength oc = osz /\
  sublist 0 opos oc = sublist 0 opos oc /\
  cold01 fs' /\
  Zlength (s0_hb hb c) = 18 /\
  (is_error_code a = false ->
   a <= osz - opos /\
   cells_bytes (sublist opos (opos + a) oc) /\
   ba_dict ba' = ba_dict ba /\
   ba_out ba' = Some (ob, bl_start ba opos, opos + a) /\
   bl_hist_ok ba' ob (opos + a) oc /\
   (forall b' : blst, ba_st ba' = Some b' -> ba_expect ba' = bs_expect b') /\
   (exists ts' : tstate, TInit (bd_oxo od) ts = TInit (bd_oxo od) ts' /\ BRc md od osz ba' fs' ts' (s0_hb hb c))) /\
  bl_claim_nc md ba ba' c a opos osz oc.
Proof.
  intros Hho Hop Hoc Hci Hmr Hmd Hst Hn Hcb Hlay Hne0 mg ba' fs' a.
  set (fc := continuity fs (offset_val opos ob) (osz - opos)) in *.
  assert (PJ: fs_expected fs' = vlong (s0_e mg c) /\ fs_stage fs' = s0_stv mg c /\
              fs_isFrameDecompression fs' = fs_isFrameDecompression fc /\ fs_ddictIsCold fs' = fs_ddictIsCold fc /\
              fs_dictID fs' = fs_dictID fc /\ fs_processedCSize fs' = vlong (pcs + Zlength c) /\
              fs_decodedSize fs' = fs_decodedSize fc /\ fs_headerSize fs' = s0_hsv mg c (fs_headerSize fc) /\
              fs_previousDstEnd fs' = fs_previousDstEnd fc /\ fs_prefixStart fs' = fs_prefixStart fc /\
              fs_virtualStart fs' = fs_virtualStart fc /\ fs_dictEnd fs' = fs_dictEnd fc /\
              fs_gpDictCopy fs' = fs_gpDictCopy fc).
  { repeat split; reflexivity. }
  clearbody fs'.
  destruct PJ as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13).
  destruct Hci as (Hexp & Her & Hstg & Hifd & Hcold & Hdid & Hpcs' & Hds & Hhb & Hwf & Hcs & Hly).
  assert (Hn5: 1 <= Zlength c <= 5).
  { rewrite Hn. unfold starting_len. destruct (md_magicless _); cbv; split; congruence. }
  assert (He: 0 <= s0_e mg c < 2 ^ 32) by (apply s0_e_range; exact Hn).
  destruct (s0_cont_eq fs (offset_val opos ob) (osz - opos)) as (Ec1 & Ec2 & Ec3 & Ec4). fold fc in Ec1, Ec2, Ec3, Ec4.
  assert (Hcold': cold01 fs') by (unfold cold01; rewrite P4, Ec1; exact Hcold).
  assert (Hmr': forall b', ba_st ba' = Some b' -> ba_expect ba' = bs_expect b').
  { intros b'. unfold ba', s0_ba; cbn [ba_st ba_expect]. destruct (ba_st ba) as [b|] eqn:B; [|discriminate].
    intros E; inversion E; subst b'. unfold s0_step, s0_e. destruct (s0_skip mg c); reflexivity. }
  unfold a. rewrite !Z.add_0_r.
  split; [rep_lia |]. split; [auto |]. split; [reflexivity |]. split; [exact Hcold' |].
  split; [apply s0_hb_len; auto; lia |]. split.
  2:{ (* bl_claim_nc *)
    unfold bl_claim_nc. destruct (ba_st ba) as [b|] eqn:B; [| exact I].
    destruct (dictref_model (ba_dict ba)) as [dm|]; [| exact I].
    intros _. destruct (Hmr b B) as (Hs & _). rewrite Hst in Hs.
    rewrite (s0_step_eq md dm b c Hs).
    split.
    + intros _. rewrite Z.add_0_r, sublist_nil. split; [reflexivity | split; [reflexivity |]].
      unfold ba', s0_ba; cbn [ba_st]. rewrite B. reflexivity.
    + intros H; exfalso; compute in H; discriminate. }
  intros _. split; [lia |]. split.
  { rewrite sublist_nil. exists nil. split; [reflexivity | constructor]. }
  split; [reflexivity |]. split; [reflexivity |]. split.
  { (* bl_hist_ok *)
    unfold bl_hist_ok, ba', s0_ba, bl_start; cbn [ba_out ba_st].
    unfold bl_hist_ok in Hho. destruct (ba_out ba) as [[[ob' f] pe]|] eqn:O.
    + destruct Hho as (-> & -> & Hf & Hm). split; [reflexivity | split; [reflexivity | split; [lia |]]].
      destruct (ba_st ba) as [b|]; cbn [option_map]; auto.
      unfold s0_step. destruct (s0_skip mg c); exact Hm.
    + split; [reflexivity | split; [reflexivity | split; [lia |]]].
      destruct (ba_st ba) as [b|]; cbn [option_map]; [| exists nil; rewrite sublist_nil; split; [reflexivity | constructor]].
      unfold s0_step. destruct (s0_skip mg c); cbn [bs_out]; rewrite Hho, sublist_nil; reflexivity. }
  split; [exact Hmr' |].
  (* BRc *)
  exists ts. split; [reflexivity |].
  exists {| bv_stage := if s0_skip mg c then BSkipHdr else BHdrRest; bv_hdr := c; bv_hs := header_size_m mg c;
            bv_h := bv_h v; bv_bt := bv_bt v; bv_rle := bv_rle v |}.
  split; [| split].
  - unfold bl_cinv. rewrite P1, P2, P3, P5, P6, P7.
    cbn [ba_expect ba' s0_ba bv_stage bv_hdr bv_hs].
    split; [reflexivity |]. split; [exact He |].
    split; [unfold s0_stv; destruct (s0_skip mg c); reflexivity |].
    split; [rewrite Ec2; exact Hifd |].
    split; [exact Hcold' |].
    split; [rewrite Ec3; exact Hdid |].
    split.
    { exists (Int64.unsigned (Int64.repr (pcs + Zlength c))). unfold vlong. rewrite Int64.repr_unsigned.
      split; [reflexivity | pose proof (Int64.unsigned_range_2 (Int64.repr (pcs + Zlength c))); lia]. }
    split; [rewrite Ec4; exact Hds |].
    split; [apply s0_hb_len; auto; lia |].
    split; [exact Hwf |].
    split.
    2:{ eapply s0_lay_ext; [exact P9 | exact P10 | exact P11 | exact P12 | exact P13 |].
        eapply s0_lay_ba; [| exact Hlay]. reflexivity. }
    unfold bl_cstage. rewrite P8. fold mg.
    assert (Hpre: sublist 0 (Zlength c) (s0_hb hb c) = zbytes c) by (apply s0_hb_pre; auto; lia).
    unfold s0_e, s0_hsv. destruct (s0_skip mg c) eqn:K; cbn [bv_stage bv_hdr bv_hs].
    + unfold s0_skip in K. apply andb_prop in K. destruct K as [K1 _].
      assert (Hn': Zlength c = ZSTD_FRAMEHEADERSIZE_PREFIX).
      { rewrite Hn. unfold mg in K1. unfold starting_len. destruct (md_magicless md); [discriminate K1 | reflexivity]. }
      destruct mg; [discriminate K1 |]. rewrite <- Hn'. repeat split; auto.
    + assert (Hn2: Zlength c = starting_len mg) by exact Hn. rewrite <- Hn2. repeat split; auto.
      intros Hmg. unfold s0_skip in K. rewrite Hmg in K. exact K.
  - intros b'. unfold ba', s0_ba; cbn [ba_st]. destruct (ba_st ba) as [b|] eqn:B; [|discriminate].
    intros E; inversion E; subst b'. destruct (Hmr b B) as (Hs & Hbe & Hbd & Hdz & Hbo & Hm0).
    rewrite Hst in Hm0. assert (Hnil: bs_out b = nil) by (apply Hm0; lia).
    assert (Hdz': fs_decodedSize fs' = vlong (Zlength (bs_out b))) by (rewrite P7, Ec4; exact Hdz).
    unfold s0_step, s0_e. cbn [ba_expect].
    destruct (s0_skip mg c); cbn [bs_stage bs_expect bs_ds bs_out bs_hbuf bv_stage bv_hdr];
      repeat split; auto.
  - exact Hmd.
Qed.

End CM_S0Pure_1.
