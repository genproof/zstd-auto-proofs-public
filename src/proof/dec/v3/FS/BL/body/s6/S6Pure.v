(* FS3-bl BODY stage 6: the pure part of the POST of ZSTDds_decodeSkippableHeader (model step to BSkip). *)
Require Export Zstd.proof.dec.v3.FS.BL.body.s6.S6Join.
Local Open Scope logic.

Section CM_S6Pure_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* Params.bl_step at BSkipHdr *)
Definition s6_step (b: blst) (c: list Z) : blst :=
  {| bs_stage := BSkip; bs_expect := le_field (bs_hbuf b ++ c) 4 4; bs_hbuf := bs_hbuf b ++ c;
     bs_hdr := bs_hdr b; bs_ds := bs_ds b; bs_out := bs_out b; bs_btype := 0; bs_rle := 0 |}.

Definition s6_ba (ba: blabs) (c: list Z) (e: Z) (ob: val) (opos: Z) : blabs :=
  {| ba_dict := ba_dict ba; ba_st := option_map (fun b => s6_step b c) (ba_st ba); ba_expect := e;
     ba_out := Some (ob, bl_start ba opos, opos) |}.

Definition s6_fs (fs: fstate) (ob: val) (osz opos pcs e: Z) : fstate :=
  fsu_stage (fsu_expected (bl_fs1 fs ob osz opos pcs 3) (vlong e)) (Vint (Int.repr 7)).

Lemma s6_cont_eq fs d n :
  fs_ddictIsCold (continuity fs d n) = fs_ddictIsCold fs /\
  fs_isFrameDecompression (continuity fs d n) = fs_isFrameDecompression fs /\
  fs_dictID (continuity fs d n) = fs_dictID fs /\
  fs_decodedSize (continuity fs d n) = fs_decodedSize fs.
Proof. unfold continuity. destruct (cont_moves fs d n); repeat split; reflexivity. Qed.

Lemma s6_post_pure md od osz osz0 ba fs ts hb v ob opos oc c pcs :
  bl_hist_ok ba ob opos oc -> 0 <= opos <= osz -> Zlength oc = osz ->
  bl_cinv md od osz0 ba fs hb v -> bl_mrel md ba fs ts v -> bd_model_ok (ba_dict ba) od ->
  fp_ok (fs_fParams fs) ->
  bv_stage v = BSkipHdr -> Zlength c = 3 -> bytes_ok c ->
  bl_lay od osz (bl_moved ba ob opos) (continuity fs (offset_val opos ob) (osz - opos)) ->
  let e := le_field (bv_hdr v ++ c) 4 4 in
  let ba' := s6_ba ba c e ob opos in
  let fs' := s6_fs fs ob osz opos pcs e in
  let a := 0 in
  0 <= a <= Int64.max_unsigned /\
  Zlength oc = osz /\
  sublist 0 opos oc = sublist 0 opos oc /\
  cold01 fs' /\
  Zlength (s6_hb hb c) = 18 /\
  fp_ok (fs_fParams fs') /\
  (is_error_code a = false ->
   a <= osz - opos /\
   cells_bytes (sublist opos (opos + a) oc) /\
   ba_dict ba' = ba_dict ba /\
   ba_out ba' = Some (ob, bl_start ba opos, opos + a) /\
   bl_hist_ok ba' ob (opos + a) oc /\
   (forall b' : blst, ba_st ba' = Some b' -> ba_expect ba' = bs_expect b') /\
   (exists ts' : tstate, TInit (bd_oxo od) ts = TInit (bd_oxo od) ts' /\ BRc md od osz ba' fs' ts' (s6_hb hb c))) /\
  bl_claim_nc md ba ba' c a opos osz oc.
Proof.
  intros Hho Hop Hoc Hci Hmr Hmd Hfp Hst Hc3 Hcb Hlay e ba' fs' a.
  destruct Hci as (Hexp & Her & Hstg & Hifd & Hcold & Hdid & Hpcs' & Hds & Hhb & Hwf & Hcs & Hly).
  cbv [bl_cstage] in Hcs; rewrite Hst in Hcs; destruct Hcs as (Hmg & Hhl & Hhok & Hhb5 & He3).
  change ZSTD_FRAMEHEADERSIZE_PREFIX with 5 in Hhl, Hhb5.
  assert (He: 0 <= e < 2 ^ 32) by (apply s6_le_field_range, Forall_app; auto).
  destruct (s6_cont_eq fs (offset_val opos ob) (osz - opos)) as (Ec1 & Ec2 & Ec3 & Ec4).
  assert (Hcold': cold01 fs').
  { unfold cold01, fs', s6_fs, bl_fs1; cbn [fs_ddictIsCold fsu_stage fsu_expected fsu_processedCSize].
    unfold fsu_stage, fsu_expected, fsu_processedCSize; cbn [fs_ddictIsCold]. rewrite Ec1. exact Hcold. }
  assert (Hmr': forall b', ba_st ba' = Some b' -> ba_expect ba' = bs_expect b').
  { intros b'. unfold ba', s6_ba; cbn [ba_st ba_expect]. destruct (ba_st ba) as [b|] eqn:B; [|discriminate].
    intros E; inversion E; subst b'. destruct (Hmr b B) as (_ & _ & _ & _ & _ & Hhb'). rewrite Hst in Hhb'.
    unfold s6_step; cbn [bs_expect]. rewrite Hhb'. reflexivity. }
  unfold a. rewrite !Z.add_0_r.
  split; [rep_lia |]. split; [auto |]. split; [reflexivity |]. split; [exact Hcold' |].
  split; [apply s6_hb_len; auto |].
  split; [unfold fs', s6_fs, fsu_stage, fsu_expected; cbn [fs_fParams]; rewrite bl_fs1_fParams; exact Hfp |].
  split.
  2:{ (* bl_claim_nc *)
    unfold bl_claim_nc. destruct (ba_st ba) as [b|] eqn:B; [| exact I].
    destruct (dictref_model (ba_dict ba)) as [dm|]; [| exact I].
    intros _. destruct (Hmr b B) as (Hs & _). rewrite Hst in Hs.
    unfold bl_step_nc. rewrite Hs. unfold bl_step. rewrite Hs.
    split.
    + intros _. rewrite Z.add_0_r, sublist_nil. split; [reflexivity | split; [reflexivity |]].
      unfold ba', s6_ba; cbn [ba_st]. rewrite B. reflexivity.
    + intros H; exfalso; compute in H; discriminate. }
  intros _. split; [lia |]. split.
  { rewrite sublist_nil. exists nil. split; [reflexivity | constructor]. }
  split; [reflexivity |]. split; [reflexivity |]. split.
  { (* bl_hist_ok *)
    unfold bl_hist_ok, ba', s6_ba, bl_start; cbn [ba_out ba_st].
    unfold bl_hist_ok in Hho. destruct (ba_out ba) as [[[ob' f] pe]|] eqn:O.
    + destruct Hho as (-> & -> & Hf & Hm). split; [reflexivity | split; [reflexivity | split; [lia |]]].
      destruct (ba_st ba) as [b|]; cbn [option_map]; auto.
    + split; [reflexivity | split; [reflexivity | split; [lia |]]].
      destruct (ba_st ba) as [b|]; cbn [option_map]; [| exists nil; rewrite sublist_nil; split; [reflexivity | constructor]].
      unfold s6_step; cbn [bs_out]. rewrite Hho, sublist_nil. reflexivity. }
  split; [exact Hmr' |].
  (* BRc *)
  exists ts. split; [reflexivity |].
  exists {| bv_stage := BSkip; bv_hdr := bv_hdr v; bv_hs := bv_hs v; bv_h := bv_h v; bv_bt := 0; bv_rle := 0 |}.
  split; [| split].
  - unfold bl_cinv. unfold fs', s6_fs, bl_fs1, fsu_stage, fsu_expected, fsu_processedCSize. cbn [fs_expected fs_stage
      fs_isFrameDecompression fs_ddictIsCold fs_dictID fs_processedCSize fs_decodedSize ba_expect ba' s6_ba bv_stage bl_stz].
    split; [reflexivity |]. split; [exact He |]. split; [reflexivity |].
    split; [rewrite Ec2; exact Hifd |].
    split; [unfold cold01 in Hcold' |- *; exact Hcold' |].
    split; [rewrite Ec3; exact Hdid |].
    split.
    { exists (Int64.unsigned (Int64.repr (pcs + 3))). unfold vlong. rewrite Int64.repr_unsigned.
      split; [reflexivity | pose proof (Int64.unsigned_range_2 (Int64.repr (pcs + 3))); lia]. }
    split; [rewrite Ec4; exact Hds |].
    split; [apply s6_hb_len; auto |].
    split; [exact Hwf |].
    split; [exact I |].
    exact Hlay.
  - intros b'. unfold ba', s6_ba; cbn [ba_st]. destruct (ba_st ba) as [b|] eqn:B; [|discriminate].
    intros E; inversion E; subst b'. destruct (Hmr b B) as (Hs & Hbe & Hbd & Hdz & Hbo & Hhb').
    rewrite Hst in Hhb'. unfold s6_step; cbn [bs_stage bs_expect bs_ds bs_out bv_stage].
    split; [reflexivity |]. split; [rewrite Hhb'; reflexivity |]. split; [exact Hbd |].
    split; [| exact (conj Hbo I)].
    unfold fs', s6_fs, bl_fs1, fsu_stage, fsu_expected, fsu_processedCSize. cbn [fs_decodedSize]. rewrite Ec4. exact Hdz.
  - exact Hmd.
Qed.

End CM_S6Pure_1.
