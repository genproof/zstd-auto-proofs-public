(* FS3-bl BODY stage 1: the pure part of the POST of ZSTDds_decodeFrameHeader (model step to BBlkHdr,
   or an error). *)
Require Export Zstd.proof.dec.v3.FS.BL.body.s1.S1Help.
Local Open Scope logic.

Section CM_S1Pure_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* the header decoded (fh_none when there is none) *)
Definition s1_h (mg: bool) (s: list Z) : frame_header :=
  match get_frame_header_m mg s with FH_ok h => h | _ => fh_none end.

(* bl_step_nc's next state at BHdrRest *)
Definition s1_st (b: blst) (c: list Z) (h: frame_header) : blst :=
  {| bs_stage := BBlkHdr; bs_expect := ZSTD_blockHeaderSize; bs_hbuf := bs_hbuf b ++ c; bs_hdr := h;
     bs_ds := bs_ds b; bs_out := bs_out b; bs_btype := 0; bs_rle := 0 |}.

Definition s1_ba (ba: blabs) (c: list Z) (h: frame_header) (ob: val) (opos: Z) : blabs :=
  {| ba_dict := ba_dict ba; ba_st := option_map (fun b => s1_st b c h) (ba_st ba); ba_expect := 3;
     ba_out := Some (ob, bl_start ba opos, opos) |}.

Definition s1_v (v: blv) (h: frame_header) : blv :=
  {| bv_stage := BBlkHdr; bv_hdr := bv_hdr v; bv_hs := bv_hs v; bv_h := h; bv_bt := 0; bv_rle := 0 |}.

Lemma s1_did_rng md od osz0 ba fs hb v :
  bl_cinv md od osz0 ba fs hb v -> 0 <= bd_idz od <= Int.max_unsigned.
Proof.
  intros (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hwf & _). destruct od as [d |]; cbn; [| rep_lia].
  destruct Hwf as [(_ & _ & _ & _ & H & _) | (_ & _ & _ & Hid & _)]; [exact H | rewrite Hid; rep_lia].
Qed.

Ltac s1_unf := unfold fsu_fParams, fsu_dictID, fsu_xxh, fsu_validateChecksum, fsu_processedCSize, s1_fs2,
  fsu_stage, fsu_expected; cbn [fs_ddictIsCold fs_dictID fs_isFrameDecompression fs_decodedSize fs_expected fs_stage
  fs_processedCSize fs_fParams fs_validateChecksum fs_xxh fs_previousDstEnd fs_prefixStart fs_virtualStart
  fs_dictEnd fs_gpDictCopy fs_headerSize].

(* the error return *)
Lemma s1_err_pure md od osz0 ba fs ts hb v c ob osz opos oc pcs d l tbl r fs' d' :
  bl_cinv md od osz0 ba fs hb v -> bl_mrel md ba fs ts v -> bd_model_ok (ba_dict ba) od -> bv_stage v = BHdrRest ->
  bytes_ok c -> fp_ok (fs_fParams fs) ->
  dfh_post3 md false d l tbl (bl_fs1 fs ob osz opos pcs (Zlength c)) (bd_idz od) (pcs + Zlength c)
    (bv_hdr v ++ c) r fs' d' ->
  is_error_code r = true ->
  cold01 fs' /\ fp_ok (fs_fParams fs') /\ bl_claim_nc md ba ba c r opos osz oc.
Proof.
  intros Hci Hmr Hmd Hst Hcb Hfp Hdfh Hr.
  assert (Hfp': fp_ok (fs_fParams fs')).
  { destruct Hci as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcs & _).
    cbv [bl_cstage] in Hcs; rewrite Hst in Hcs; destruct Hcs as (_ & Hhok & _).
    assert (Hbs: bytes_ok (bv_hdr v ++ c)) by (apply Forall_app; auto).
    rewrite <- (bl_fs1_fParams fs ob osz opos pcs (Zlength c)) in Hfp.
    set (fs1 := bl_fs1 fs ob osz opos pcs (Zlength c)) in *.
    unfold dfh_post3 in Hdfh. cbv zeta in Hdfh. cbn [sel_r] in Hdfh.
    destruct (eq_dec nullval nullval) as [_ | NE]; [| contradiction NE; reflexivity].
    destruct (get_frame_header_m (md_magicless md) (bv_hdr v ++ c)) as [| k | h] eqn:G.
    - destruct Hdfh as (_ & _ & w & -> & [-> | Hw]); s1_unf; [exact Hfp | exists 0; split; [exact Hw | rep_lia]].
    - destruct Hdfh as (_ & _ & w & -> & [-> | Hw]); s1_unf; [exact Hfp | exists 0; split; [exact Hw | rep_lia]].
    - pose proof (s1_did_ok _ _ _ Hbs G) as Hdi.
      destruct Hdfh as (_ & Hdfh).
      destruct (orb (fh_dictID h =? 0) (fh_dictID h =? bd_idz od)); destruct Hdfh as (_ & ->); s1_unf;
        apply s1_fp_ok_val; exact Hdi. }
  enough (cold01 fs' /\ bl_claim_nc md ba ba c r opos osz oc) by tauto. clear Hfp'.
  destruct Hci as (_ & _ & _ & _ & Hcold & _).
  destruct (s1_fs1_eq fs ob osz opos pcs (Zlength c)) as (_ & _ & _ & E4 & _).
  set (fs1 := bl_fs1 fs ob osz opos pcs (Zlength c)) in *.
  unfold dfh_post3 in Hdfh. cbv zeta in Hdfh. cbn [sel_r] in Hdfh.
  destruct (eq_dec nullval nullval) as [_ | NE]; [| contradiction NE; reflexivity].
  assert (Hcl: cold01 fs').
  { unfold cold01 in *.
    destruct (get_frame_header_m (md_magicless md) (bv_hdr v ++ c)) as [| k | h].
    - destruct Hdfh as (_ & _ & w & -> & _). s1_unf; rewrite E4; exact Hcold.
    - destruct Hdfh as (_ & _ & w & -> & _). s1_unf; rewrite E4; exact Hcold.
    - destruct Hdfh as (_ & Hdfh).
      destruct (orb (fh_dictID h =? 0) (fh_dictID h =? bd_idz od)); destruct Hdfh as (_ & ->); s1_unf; rewrite E4; exact Hcold. }
  split; [exact Hcl |].
  unfold bl_claim_nc. destruct (ba_st ba) as [b |] eqn:B; [| exact I].
  destruct (dictref_model (ba_dict ba)) as [dm |] eqn:Dm; [| exact I].
  intros _. destruct (Hmr b B) as (Hbs & _ & _ & _ & _ & Hhb). rewrite Hst in Hhb. destruct Hhb as (Hhb & _).
  destruct (Hmd dm Dm) as (Hid & _).
  unfold bl_step_nc. rewrite Hbs, Hst, Hhb.
  destruct (get_frame_header_m (md_magicless md) (bv_hdr v ++ c)) as [| k | h]; auto.
  destruct Hdfh as (_ & Hdfh).
  destruct (andb (negb (fh_dictID h =? 0)) (negb (fh_dictID h =? dm_id dm))) eqn:Eid; auto.
  rewrite Hid in Eid.
  destruct (fh_dictID h =? 0) eqn:E0; destruct (fh_dictID h =? bd_idz od) eqn:E1; cbn in Eid; try discriminate;
    cbn in Hdfh; destruct Hdfh as (-> & _); compute in Hr; discriminate.
Qed.

(* the success return: stage 2 *)
Lemma s1_ok_pure md od osz0 ba fs ts hb v c ob osz opos oc pcs d l tbl r fs' d' :
  bl_hist_ok ba ob opos oc -> 0 <= opos <= osz -> Zlength oc = osz ->
  bl_cinv md od osz0 ba fs hb v -> bl_mrel md ba fs ts v -> bd_model_ok (ba_dict ba) od -> bv_stage v = BHdrRest ->
  bytes_ok c -> Zlength c = ba_expect ba ->
  bl_lay od osz (bl_moved ba ob opos) (continuity fs (offset_val opos ob) (osz - opos)) ->
  (md_magicless md = false -> is_skippable_magic (le_field (bv_hdr v) 0 4) = false) ->
  (forall b, ba_st ba = Some b -> bs_out b = nil) ->
  dfh_post3 md false d l tbl (bl_fs1 fs ob osz opos pcs (Zlength c)) (bd_idz od) (pcs + Zlength c)
    (bv_hdr v ++ c) r fs' d' ->
  is_error_code r = false ->
  let h := s1_h (md_magicless md) (bv_hdr v ++ c) in
  let ba' := s1_ba ba c h ob opos in
  let fs2 := s1_fs2 fs' in
  let hb' := s1_hb hb c (starting_len (md_magicless md)) (bv_hs v) in
  r = 0 /\ cold01 fs2 /\ Zlength hb' = 18 /\ fp_ok (fs_fParams fs2) /\
  bl_hist_ok ba' ob opos oc /\
  (forall b', ba_st ba' = Some b' -> ba_expect ba' = bs_expect b') /\
  BRc md od osz ba' fs2 ts hb' /\
  bl_claim_nc md ba ba' c 0 opos osz oc.
Proof.
  intros Hho Hop Hoc Hci Hmr Hmd Hst Hcb Hce Hlay Hnsk Hout Hdfh Hr h ba' fs2 hb'.
  pose proof (s1_did_rng _ _ _ _ _ _ _ Hci) as Hdr.
  destruct Hci as (Hexp & Her & Hstg & Hifd & Hcold & Hdid & Hpcs' & Hds & Hhb & Hwf & Hcs & Hly).
  cbv [bl_cstage] in Hcs; rewrite Hst in Hcs; destruct Hcs as (Hhl & Hhok & Hhb5 & Hhs & Hfhs & He & Hnsk0).
  assert (Hn: 0 <= Zlength c) by apply Zlength_nonneg.
  assert (Hrng: (starting_len (md_magicless md) = 1 \/ starting_len (md_magicless md) = 5) /\ bv_hs v <= 18).
  { split; [unfold starting_len; destruct (md_magicless md); auto |]. rewrite Hhs. apply s1_hsize_le. }
  destruct (s1_fs1_eq fs ob osz opos pcs (Zlength c)) as (E1 & E2 & E3 & E4 & E5 & E6 & E7).
  set (fs1 := bl_fs1 fs ob osz opos pcs (Zlength c)) in *.
  assert (Hlay1: bl_lay od osz (bl_moved ba ob opos) fs1) by exact Hlay. clearbody fs1. clear Hlay.
  unfold dfh_post3 in Hdfh. cbv zeta in Hdfh. cbn [sel_r] in Hdfh.
  destruct (eq_dec nullval nullval) as [_ | NE]; [| contradiction NE; reflexivity].
  assert (Hbs: bytes_ok (bv_hdr v ++ c)) by (apply Forall_app; auto).
  destruct (get_frame_header_m (md_magicless md) (bv_hdr v ++ c)) as [| k | h0] eqn:G;
    [destruct Hdfh as (Hd & _); destruct Hd as (Hd & _); rewrite Hd in Hr; discriminate
    | destruct Hdfh as (Hd & _); destruct Hd as (Hd & _); rewrite Hd in Hr; discriminate |].
  assert (Eh: h = h0) by (unfold h, s1_h; rewrite G; reflexivity).
  clearbody h. subst h0.
  destruct Hdfh as (_ & Hdfh).
  destruct (orb (fh_dictID h =? 0) (fh_dictID h =? bd_idz od)) eqn:Eid;
    [| destruct Hdfh as ((Hd & _) & _); rewrite Hd in Hr; discriminate].
  destruct Hdfh as (-> & Efs).
  assert (Hsk: md_magicless md = false -> is_skippable_magic (le_field (bv_hdr v ++ c) 0 4) = false).
  { intros M. rewrite <- (Hnsk M). f_equal. unfold le_field, slice. f_equal.
    change (Z.to_nat 0) with O. cbn [skipn].
    rewrite firstn_app. replace (Z.to_nat 4 - length (bv_hdr v))%nat with O; [rewrite firstn_O, app_nil_r; reflexivity |].
    rewrite Zlength_correct in Hhl. unfold starting_len, ZSTD_FRAMEHEADERSIZE_PREFIX in Hhl. rewrite M in Hhl.
    change (Z.to_nat 4) with 4%nat. lia. }
  destruct (s1_hdr_ok _ _ _ Hbs G Hsk) as (Hhok' & Hidr).
  assert (F: fs_ddictIsCold fs2 = fs_ddictIsCold fs1 /\ fs_isFrameDecompression fs2 = fs_isFrameDecompression fs1 /\
     fs_dictID fs2 = Vint (Int.repr (bd_idz od)) /\ fs_expected fs2 = vlong 3 /\ fs_stage fs2 = Vint (Int.repr 2) /\
     fs_processedCSize fs2 = Vlong (Int64.repr (pcs + Zlength c + Zlength (bv_hdr v ++ c))) /\
     fs_decodedSize fs2 = fs_decodedSize fs1 /\ fs_fParams fs2 = fh_val h /\
     fs_validateChecksum fs2 = Vint (Int.repr (if bl_val (md_ignore md) h then 1 else 0)) /\
     fs_xxh fs2 = (if bl_val (md_ignore md) h then Some [] else fs_xxh fs1) /\
     fs_previousDstEnd fs2 = fs_previousDstEnd fs1 /\ fs_prefixStart fs2 = fs_prefixStart fs1 /\
     fs_virtualStart fs2 = fs_virtualStart fs1 /\ fs_dictEnd fs2 = fs_dictEnd fs1 /\
     fs_gpDictCopy fs2 = fs_gpDictCopy fs1).
  { unfold fs2, s1_fs2. rewrite Efs. repeat split; reflexivity. }
  clearbody fs2. clear Efs.
  destruct F as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15).
  assert (Hcl2: cold01 fs2) by (unfold cold01; rewrite F1, E4; exact Hcold).
  assert (Hsl: Zlength c = bv_hs v - starting_len (md_magicless md)) by lia.
  assert (Hhb2: Zlength hb' = 18) by (unfold hb'; apply s1_hb_len; auto; lia).
  split; [reflexivity |]. split; [exact Hcl2 |]. split; [exact Hhb2 |].
  split; [rewrite F8; apply s1_fp_ok_val; exact Hidr |].
  split.
  { unfold bl_hist_ok, ba', s1_ba, bl_start; cbn [ba_out ba_st].
    unfold bl_hist_ok in Hho. destruct (ba_out ba) as [[[ob' f] pe]|] eqn:O.
    + destruct Hho as (-> & -> & Hf & Hm). split; [reflexivity | split; [reflexivity | split; [lia |]]].
      destruct (ba_st ba) as [b|]; cbn [option_map s1_st bs_out]; auto.
    + split; [reflexivity | split; [reflexivity | split; [lia |]]].
      destruct (ba_st ba) as [b|]; cbn [option_map];
        [| rewrite sublist_nil; exists nil; split; [reflexivity | constructor]].
      unfold s1_st; cbn [bs_out]. rewrite Hho, sublist_nil. reflexivity. }
  split.
  { intros b'. unfold ba', s1_ba; cbn [ba_st ba_expect]. destruct (ba_st ba); [| discriminate].
    intros E; inversion E; reflexivity. }
  split.
  { exists (s1_v v h). split; [| split].
    - unfold bl_cinv. cbn [ba_expect ba' s1_ba s1_v bv_stage bl_stz].
      rewrite F2, F3, F4, F5, F6, F7.
      split; [reflexivity |]. split; [lia |]. split; [reflexivity |].
      split; [rewrite E5; exact Hifd |].
      split; [exact Hcl2 |].
      split; [reflexivity |].
      split.
      { exists (Int64.unsigned (Int64.repr (pcs + Zlength c + Zlength (bv_hdr v ++ c)))). unfold vlong.
        rewrite Int64.repr_unsigned. split; [reflexivity | rep_lia]. }
      split; [rewrite E6; exact Hds |].
      split; [exact Hhb2 |].
      split; [exact Hwf |].
      split.
      { cbv [bl_cstage]. cbn [bv_stage s1_v]. split; [| reflexivity].
        unfold hdr_fields. cbn [bv_h s1_v]. rewrite F8, F9, F10. split; [exact Hhok' |]. split; [reflexivity |].
        split; [reflexivity |]. intros Hv. cbn [bv_h s1_v] in Hv. rewrite Hv. eexists; reflexivity. }
      unfold bl_lay in *. rewrite F11, F12, F13, F14, F15. exact Hlay1.
    - intros b' Hb'. unfold ba', s1_ba in Hb'; cbn [ba_st] in Hb'.
      destruct (ba_st ba) as [b|] eqn:B; [| discriminate]. cbn [option_map] in Hb'. injection Hb' as <-.
      destruct (Hmr b B) as (Hs & Hbe & Hbd & Hdz & Hob & Hhb'). cbn [s1_v bv_stage].
      unfold s1_st; cbn [bs_stage bs_expect bs_ds bs_out bs_hdr bv_h].
      split; [reflexivity |]. split; [reflexivity |]. split; [exact Hbd |].
      split; [rewrite F7, E6; exact Hdz |]. split; [exact Hob |].
      split; [reflexivity |]. intros Hv. cbn [bv_h s1_v] in Hv. rewrite F10, Hv, (Hout b eq_refl). reflexivity.
    - exact Hmd. }
  unfold bl_claim_nc, ba', s1_ba; cbn [ba_st].
  destruct (ba_st ba) as [b|] eqn:B; [| exact I].
  destruct (dictref_model (ba_dict ba)) as [dm|] eqn:Dm; [| exact I].
  intros _. destruct (Hmr b B) as (Hbs0 & _ & _ & _ & _ & Hhbm). rewrite Hst in Hhbm. destruct Hhbm as (Hhbm & _).
  destruct (Hmd dm Dm) as (Hid & _).
  unfold bl_step_nc. rewrite Hbs0, Hst, Hhbm, G, Hid.
  destruct (fh_dictID h =? 0); destruct (fh_dictID h =? bd_idz od); try discriminate Eid; cbn [negb andb].
  all: split; [intros _; split; [reflexivity |]; split; [rewrite Z.add_0_r, sublist_nil; reflexivity |];
               cbn [option_map]; unfold s1_st; rewrite Hhbm; reflexivity
              | intros H; compute in H; discriminate].
Qed.

End CM_S1Pure_1.
