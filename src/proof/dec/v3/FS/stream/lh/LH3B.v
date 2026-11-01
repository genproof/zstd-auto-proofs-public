(* FS3 streaming, case zdss_loadHeader: piece B (s6: the single-pass
   shortcut, the selection on or off). *)
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3Bsel Zstd.proof.dec.v3.FS.stream.lh.LH3Bclaim Zstd.proof.dec.v3.FS.stream.lh.LH3Bsw.
Require Zstd.proof.dec.v3.FS.stream.lh.LH3RetG Zstd.proof.dec.v3.FS.stream.modelw.MW3Series.
Require Import Zstd.proof.zstd.NullBuf.
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3XDefs.

Section CM_LH3B_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* ---------- the shortcut's capacity (fix F7) ----------
   zstd now passes the frame's declared content size as the capacity of ZSTD_decompress_usingDDict (the shortcut
   runs only when that size is known and fits the output space), so the call's claims are on that capacity.  A
   frame that declares its content size decodes to exactly that many bytes or not at all, so the claims carry
   over to the whole output space (the capacity lhB_facts speaks of), with the bytes after the call's part of
   the output left as they were. *)

(* one Zstandard frame x (all of x) that declares its content size decodes, when the lenient one-shot model
   decodes it, to exactly that many bytes (Frame.v / Params.v: a content of another size is FUnk) *)
Lemma lhB_fcs_len : forall md dm x c h,
  frame_compressed_size_m (md_magicless md) x = Some (Zlength x) ->
  get_frame_header_m (md_magicless md) x = FH_ok h -> fh_frameType h = 0 ->
  decode_series_m md sel_none (Some dm) no_wlim x = SOk c ->
  fh_contentSize h <> ZSTD_CONTENTSIZE_UNKNOWN -> Zlength c = fh_contentSize h.
Proof.
  intros md dm x c h Hfc G Ht Hd Hu.
  assert (Hs: MW3Series.sc_frame md sel_none (Some dm) x dm).
  { split; [exact Hfc|]. split; [exists h; split; assumption|]. unfold frame_dict. rewrite G. reflexivity. }
  rewrite (MW3Series.scg_series _ _ _ _ _ Hs) in Hd.
  destruct (decode_frame_m md dm no_wlim x) as [c1 k| | |] eqn:D; try discriminate.
  injection Hd as <-.
  destruct (MW3FrameM.dfm_hdr_inv md dm no_wlim x) as [h' [G' [_ [_ [_ [_ [_ D']]]]]]]; try congruence.
  rewrite G in G'. injection G' as <-. rewrite D in D'.
  unfold MW3Frame.df_tail in D'. cbv zeta in D'.
  destruct (MW3Base.dblocks _ _ _ _ _ _ _ _) as [[out kb]|]; [|discriminate].
  destruct (negb (fh_contentSize h =? ZSTD_CONTENTSIZE_UNKNOWN) && negb (Zlength out =? fh_contentSize h))%bool eqn:C;
    [discriminate|].
  assert (out = c1).
  { repeat match type of D' with context [if ?b then _ else _] => destruct b end; congruence. }
  subst out. apply Bool.andb_false_iff in C. destruct C as [C|C].
  - apply Bool.negb_false_iff, Z.eqb_eq in C. contradiction.
  - apply Bool.negb_false_iff, Z.eqb_eq in C. auto.
Qed.

(* the one-shot claims on the capacity fh_contentSize h (the output outv) give the claims on any larger
   capacity cap, the output outv followed by any cells rest: a success fits, and a capacity error cannot be
   one (the frame's content is exactly fh_contentSize h bytes) *)
Lemma lhB_os_cap : forall md odm x h cap r (outv rest: list val),
  frame_compressed_size_m (md_magicless md) x = Some (Zlength x) ->
  get_frame_header_m (md_magicless md) x = FH_ok h -> fh_frameType h = 0 ->
  fh_contentSize h <> ZSTD_CONTENTSIZE_UNKNOWN -> fh_contentSize h <= cap ->
  Zlength outv = fh_contentSize h -> 0 <= r ->
  oneshot_ok md odm x (fh_contentSize h) r outv -> oneshot_ok md odm x cap r (outv ++ rest).
Proof.
  intros md odm x h cap r outv rest Hfc G Ht Hu Hcap Hlo Hr0 [Hr Hm].
  split; [intros E; specialize (Hr E); lia|].
  destruct odm as [dm|]; [|exact I].
  destruct (decode_series_m md sel_none (Some dm) no_wlim x) as [c| |] eqn:Hd; auto.
  destruct Hm as [Hok Herr]. split.
  - intros E. destruct (Hok E) as [Hrc Hsub]. split; [exact Hrc|].
    rewrite sublist_app1 by (specialize (Hr E); lia). exact Hsub.
  - intros E. destruct (Herr E) as [Hlt|Hma]; [|right; exact Hma].
    pose proof (lhB_fcs_len md dm x c h Hfc G Ht Hd Hu). lia.
Qed.

(* the frame the shortcut decodes, input[ipos, ipos + cSize), starts with the loaded header hb and is one whole
   frame (as in lhB_sw_of) *)
Lemma lhB_x_frame (mg: bool) (ibs: list Z) (ipos ipc isz cSize: Z) (hb: list Z) (h: frame_header) :
  bytes_ok ibs -> Zlength ibs = isz -> 0 <= ipos -> ipos <= ipc -> ipc <= isz ->
  hb = sublist ipos ipc ibs -> get_frame_header_m mg hb = FH_ok h -> fh_headerSize h = Zlength hb ->
  frame_compressed_size_m mg (sublist ipos isz ibs) = Some cSize -> cSize <= isz - ipos ->
  get_frame_header_m mg (sublist ipos (ipos + cSize) ibs) = FH_ok h /\
  frame_compressed_size_m mg (sublist ipos (ipos + cSize) ibs) = Some (Zlength (sublist ipos (ipos + cSize) ibs)).
Proof.
intros Hb Hl H0 H1 H2 Ehb G Hs F Hc.
assert (Hgap: ipc <= ipos + cSize)
  by exact (LH3RetG.RG.gap_of_hdr_m _ ibs ipos ipc isz hb h cSize Hb Hl H0 H1 H2 (eq_sym Ehb) G Hs F).
assert (Hbh: bytes_ok hb) by (rewrite Ehb; unfold bytes_ok in *; apply Forall_sublist; auto).
assert (Hx: sublist ipos (ipos + cSize) ibs = hb ++ sublist ipc (ipos + cSize) ibs)
  by (rewrite Ehb, <- sublist_split; auto; lia).
assert (Hlx: Zlength (sublist ipos (ipos + cSize) ibs) = cSize) by (rewrite Zlength_sublist; lia).
split.
- rewrite Hx; apply LH3RetG.RG.gfh_m_ext; auto.
- assert (Hbs: bytes_ok (sublist ipos isz ibs)) by (unfold bytes_ok in *; apply Forall_sublist; auto).
  destruct (LH3RetG.RG.fcs_m_trunc _ _ _ Hbs F) as [_ Ht']. rewrite <- sublist_firstn, sublist_sublist in Ht' by lia.
  rewrite Hlx. rewrite <- Ht'. f_equal. f_equal; lia.
Qed.

Local Open Scope logic.

(* the four byte ranges lent to ZSTD_decompress_usingDDict as witnesses: the output before and after the call's
   part, the input before and after the frame *)
Lemma lhB_pws4 : forall sh1 n1 c1 p1 sh2 n2 c2 p2 sh3 n3 c3 p3 sh4 n4 c4 p4 W,
  data_at sh1 (tarray tuchar n1) c1 p1 * data_at sh2 (tarray tuchar n2) c2 p2 * data_at sh3 (tarray tuchar n3) c3 p3 *
  data_at sh4 (tarray tuchar n4) c4 p4 * pws_pred W =
  pws_pred (pw_bytes sh1 n1 c1 p1 :: pw_bytes sh2 n2 c2 p2 :: pw_bytes sh3 n3 c3 p3 :: pw_bytes sh4 n4 c4 p4 :: W).
Proof. intros. unfold pws_pred. cbn [map fold_right pw_pred]. apply pred_ext; cancel. Qed.

Lemma lhB_pws4_i : forall sh1 n1 c1 p1 sh2 n2 c2 p2 sh3 n3 c3 p3 sh4 n4 c4 p4 W,
  data_at sh1 (tarray tuchar n1) c1 p1 * data_at sh2 (tarray tuchar n2) c2 p2 * data_at sh3 (tarray tuchar n3) c3 p3 *
  data_at sh4 (tarray tuchar n4) c4 p4 * pws_pred W |--
  pws_pred (pw_bytes sh1 n1 c1 p1 :: pw_bytes sh2 n2 c2 p2 :: pw_bytes sh3 n3 c3 p3 :: pw_bytes sh4 n4 c4 p4 :: W).
Proof. intros. rewrite lhB_pws4. auto. Qed.

Lemma lhB_pws4_e : forall sh1 n1 c1 p1 sh2 n2 c2 p2 sh3 n3 c3 p3 sh4 n4 c4 p4 W,
  pws_pred (pw_bytes sh1 n1 c1 p1 :: pw_bytes sh2 n2 c2 p2 :: pw_bytes sh3 n3 c3 p3 :: pw_bytes sh4 n4 c4 p4 :: W) |--
  data_at sh1 (tarray tuchar n1) c1 p1 * data_at sh2 (tarray tuchar n2) c2 p2 * data_at sh3 (tarray tuchar n3) c3 p3 *
  data_at sh4 (tarray tuchar n4) c4 p4 * pws_pred W.
Proof. intros. rewrite lhB_pws4. auto. Qed.

Lemma lhB_hset_sel : forall pr am sp l hb tbl, sel_on pr sp = true ->
  hset_t am sp l hb tbl |-- !! (l <> nil /\ hs_inv l tbl).
Proof.
  intros pr am sp l hb tbl Hs. unfold hset_t. destruct (eq_dec sp nullval) as [E|E].
  - subst sp. unfold sel_on, veqb in Hs. destruct (Val.eq nullval nullval); [|congruence].
    rewrite andb_false_r in Hs. discriminate.
  - unfold hset_tbl. Intros tp. entailer!.
Qed.

(* the stream fields after the shortcut: the set's bytes are unchanged, the allocator holds the local DDict of d'
   instead of that of k1 *)
Lemma lhB_s_held : forall k1 d',
  sf_held (lhB_s k1 d') - local_held d' = sf_held (c3_s k1) - local_held (c3_dict k1).
Proof. intros. unfold lhB_s. apply held_redict_set. Qed.

Lemma lhB_s_given : forall k1 d',
  sf_given (lhB_s k1 d') = sf_given (c3_s k1) - local_held (c3_dict k1) + local_held d'.
Proof. intros. unfold lhB_s. rewrite <- sf_given_redict. reflexivity. Qed.

(* ---------- the exact facts (from the configuration of a new context) ---------- *)

(* the tables' representation holds litExtraBuffer's full LITEXTRA_N bytes *)
Lemma lhB_fg_lxb : forall TABS gv p fs t pr sp, TABS_OK TABS ->
  fgroup3 TABS gv p fs t pr sp |-- !! (Zlength (tabs_lxb t) = LITEXTRA_N).
Proof.
  intros TABS gv p fs t pr sp HT. unfold fgroup3. destruct t as [lxb | ox ts]; cbn [tabs_rep tabs_lxb].
  - unfold tables_uninit, lit_extra_at. entailer!.
  - Intros. sep_apply (HT gv p ox ts). unfold tables_uninit, lit_extra_at. entailer!.
Qed.

(* without a dictionary or a set, ZSTD_getDDict returns NULL (dictUses is 0) *)
Lemma lhB_fresh_ddict : forall st d, fresh_cfg st -> dict_rel3 st d -> fst (getddict_res d) = nullval.
Proof.
  intros st d (Hd & _ & Hs & _) [Hr | [Hn _]]; [| contradiction].
  unfold dict_rel3_of in Hr. rewrite Hd in Hr. destruct Hr as [Hu _].
  unfold getddict_res. rewrite Hu. reflexivity.
Qed.

(* a dictionary argument whose DDict pointer is NULL is no dictionary: a DDict's struct is at a pointer *)
Lemma lhB_darg_none : forall DENT gv pr sp d ad, darg_is_ddict ad -> sel_on pr sp = false -> darg_ddict ad = nullval ->
  darg_res3 DENT gv pr sp d ad |-- !! (ad = DA_none).
Proof.
  intros DENT gv pr sp d ad Hi Hs Hn. destruct ad as [ | sh pk b | x buf sh]; [entailer! | contradiction | ].
  unfold darg_res3. rewrite Hs. cbn [andb]. unfold darg_res, ddict_rep_at, ddict_struct.
  cbn [darg_ddict] in Hn. rewrite Hn. Intros. contradiction.
Qed.

Section Gen.
Context (Espec: OracleKind) (DENT: dent_pred) (TABS: tabs_pred) (BR: blrel).

(* the distance between two positions of a caller's char buffer of any size (up to PTRDIFF_MAX) *)
Lemma sub_pp_tschar_any : forall p i j, isptr p -> 0 <= j <= i -> i <= 2 ^ 63 - 1 ->
  force_val (sem_sub_pp tschar (offset_val i p) (offset_val j p)) = Vlong (Int64.repr (i - j)).
Proof.
intros p i j Hp Hj Hi. destruct p; try contradiction.
unfold sem_sub_pp; simpl. rewrite if_true by auto. simpl. f_equal.
rewrite !(Ptrofs.add_commut i0), Ptrofs.sub_shifted. rewrite Ptrofs.divs_one by reflexivity.
unfold Vptrofs, Ptrofs.sub. rewrite !Ptrofs.unsigned_repr by rep_lia. simpl.
unfold Ptrofs.to_int64. rewrite Ptrofs.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma lhB_gen : forall (a: dsa) (w: lw) (hb: list Z) (h: frame_header) (tbl: list val) (k1: cst3),
  MF3 -> lend_use_ok -> hs_probe_ok -> DENT_OK DENT -> TABS_OK TABS -> dsa_ok a ->
  (0 <= sf_held (c3_s k1) - local_held (c3_dict k1) -> lh_entry a (lw_k w k1) hb) -> dd_bytes_ok (a_st a) -> lh_hb_in a w hb -> get_frame_header_m (lh_mg k1) hb = FH_ok h ->
  gfh3_facts (lh_mg k1) hb h -> fs_fParams (c3_fs k1) = fh_val h ->
  (forall cSize r out fs' d' lxb', lhB_facts a w k1 hb h cSize r out -> dec_err r -> lhB_dict k1 d' ->
     fp_ok (fs_fParams fs') ->
     lh_rc a w hb r (a_ipos a)
       {| w_smw := w_smw w; w_k := lhB_k k1 fs' d' lxb'; w_sv := w_sv w; w_ipc := w_ipc w; w_opc := w_opc w;
          w_oc := sublist 0 (w_opc w) (w_oc w) ++ out; w_dl := w_dl w |}) ->
  lh_mg k1 = lh_mg (w_k w) ->
  (forall cSize r out fs' d' lxb', lhB_facts a w k1 hb h cSize r out -> is_error_code r = true ->
     (fresh_cfg (a_st a) ->
        os_match (sublist (a_ipos a) (a_ipos a + cSize) (a_ibs a)) (fh_contentSize h) r (sublist 0 (fh_contentSize h) out)) ->
     Zlength (tabs_lxb (c3_tabs k1)) = LITEXTRA_N ->
     lh_xok a w hb r (a_ipos a)
       {| w_smw := w_smw w; w_k := lhB_k k1 fs' d' lxb'; w_sv := w_sv w; w_ipc := w_ipc w; w_opc := w_opc w;
          w_oc := sublist 0 (w_opc w) (w_oc w) ++ out; w_dl := w_dl w |}) ->
  semax (ds_Delta DENT TABS BR) (lh_stt DENT TABS a (lw_k w k1) tbl) lh_B (lhB_post_x DENT TABS a w hb h k1 tbl).
Proof.
intros a w hb h tbl k1 MFh Hlend Hprobe HD HT Ha HeI Hddb Hhbi Hgh Hf Hfp HRC Hmg HRX.
unfold lh_stt, lhB_post_x, ds_Delta. simplify_func_tycontext. unfold lh_B. abbreviate_semax.
unfold ds_LI_St, ds_LI_L, ctx_rep3t, sgroup. rewrite lhB_fg_split. Intros.
assert_PROP (0 <= sf_held (c3_s k1) - local_held (c3_dict k1)) as Hhs0.
{ set (k1' := w_k (lw_k w k1)).
  sep_apply (hset_t_held (sf_mem (c3_s k1')) (c3_sp k1') (c3_set k1') (sf_held (c3_s k1') - local_held (c3_dict k1'))
               tbl).
  entailer!. }
assert (He := HeI Hhs0). clear HeI.
assert (Ha0 := Ha). assert (He0 := He). assert (Hf0 := Hf).
assert (Hdsa: bytes_ok (a_ibs a) /\ 0 <= a_ipos a /\ Zlength (a_ibs a) = a_isz a) by (unfold dsa_ok in Ha; tauto).
assert (Hent: bytes_ok hb /\ a_ipos a <= w_ipc w <= a_isz a /\ hdr_lenok (lh_mg k1) hb)
  by (unfold lh_entry in He; cbn [lw_k w_k w_ipc] in He; tauto).
cbn [lw_k w_k w_smw w_ipc w_opc w_oc] in *.
destruct Ha as (Hbo & Hbi & Hst & Wsho & Wshi & Wshob & Rshb & Hdn & Hse & Hopos & Hosz & Hoc & Hipos & Hisz & Hibs & Hbok & Hstout & Hw0 & Hstab2 & _).
destruct He as (Hstg & Hlh & Hhb18 & Hhbok & Hhbsub & Hhost & Hinp & Hos & Hoe & Hipc & Hopc & Hoc' & Hsmw & Hbc & Hlen).
destruct Hf as (Hhb5 & Hfcs & Hws & Hbsm & Hbsm' & Hck & Hft & Hft1 & Hft2 & Hdid & Hhs).
rewrite Hfp.
cbn [lw_k w_k w_smw w_ipc w_opc w_oc] in Hstg, Hlh, Hhbsub, Hhost, Hinp, Hos, Hoe, Hipc, Hopc, Hoc', Hsmw, Hbc, Hlen.
assert_PROP (isptr (a_ob a)) as Hob by entailer!.
assert_PROP (Forall (fun e => isptr (fst e)) (c3_set k1)) as Hsetp.
{ sep_apply (lhB_hset_isptr (sf_mem (c3_s k1)) (c3_sp k1) (c3_set k1) (sf_held (c3_s k1) - local_held (c3_dict k1))
               tbl).
  entailer!. }
assert_PROP (sel_on (c3_par k1) (c3_sp k1) = true -> c3_set k1 <> nil /\ hs_inv (c3_set k1) tbl) as Hsel.
{ destruct (sel_on (c3_par k1) (c3_sp k1)) eqn:Es; [| entailer!; discriminate].
  sep_apply (lhB_hset_sel (c3_par k1) (sf_mem (c3_s k1)) (c3_sp k1) (c3_set k1) (sf_held (c3_s k1) - local_held (c3_dict k1))
               tbl Es).
  entailer!. }
destruct Hbc as (Hbst & Hbpar & Hbset & Hbdr & Hbcur & Hbfp & Hbmem).
assert_PROP (isptr (a_ib a)) as Hib by entailer!.
freeze FR0 := (dctx_token _) (dctx_pad _) (cgroup3 _ _ _) (field_at _ _ (DOT _inBuff) _ _)
  (field_at _ _ (DOT _inBuffSize) _ _) (field_at _ _ (DOT _inPos) _ _) (field_at _ _ (DOT _outBuff) _ _).
freeze FR1 := (field_at _ _ (DOT _outBuffSize) _ _) (field_at _ _ (DOT _outStart) _ _) (field_at _ _ (DOT _outEnd) _ _)
  (field_at _ _ (DOT _hostageByte) _ _) (field_at _ _ (DOT _noForwardProgress) _ _)
  (field_at _ _ (DOT _expectedOutBuffer) _ _).
freeze FR2 := (field_at _ _ (DOT _headerBuffer) _ _)
  (field_at _ _ (DOT _oversizedDuration) _ _) (ring_rep _ _ _ _) (data_at _ t_outBuffer _ _) (data_at _ t_inBuffer _ _).
freeze FRF := (lhB_frest _ _ _ _ _ _ _).
clear Ha0 He0 Hf0.
forward.
match goal with |- context [temp _t'145 ?v] => change v with (Vlong (Int64.repr (fh_contentSize h))) end.
forward_if (temp _t'28 (Vint (Int.repr (if andb (negb (fh_contentSize h =? ZSTD_CONTENTSIZE_UNKNOWN))
  (negb (fh_frameType h =? 1)) then 1 else 0)))).
{ forward. forward. entailer!. apply lhB_t26; auto. }
{ forward. entailer!. rewrite lhB_t26'; auto. }
forward_if (temp _t'29 (Vint (Int.repr (if andb (andb (negb (fh_contentSize h =? ZSTD_CONTENTSIZE_UNKNOWN))
  (negb (fh_frameType h =? 1))) (fh_contentSize h <=? a_osz a - w_opc w) then 1 else 0)))).
{ forward. forward.
  match goal with |- context [temp _t'144 ?v] => change v with (Vlong (Int64.repr (fh_contentSize h))) end.
  forward.
  { entailer!. apply prop_right. destruct (a_ob a); try contradiction. simpl. unfold sameblock.
    destruct (peq b b); [reflexivity | congruence]. }
  entailer!. rewrite sub_pp_tschar_any by (auto; lia). simpl. unfold Int64.ltu.
  rewrite !Int64.unsigned_repr by rep_lia.
  match goal with H: (if _ then 1 else 0) <> 0 |- _ => rename H into Hnz end.
  destruct (negb _ && negb _)%bool; simpl in Hnz |- *; [|lia].
  destruct (zlt _ _); destruct (Z.leb_spec (fh_contentSize h) (a_osz a - w_opc w)); try lia; reflexivity. }
{ forward. entailer!. destruct (negb _ && negb _)%bool; [discriminate | reflexivity]. }
forward_if (temp _t'30 (Vint (Int.repr (if andb (andb (andb (negb (fh_contentSize h =? ZSTD_CONTENTSIZE_UNKNOWN))
  (negb (fh_frameType h =? 1))) (fh_contentSize h <=? a_osz a - w_opc w)) (Zlength hb =? w_ipc w - a_ipos a)
  then 1 else 0)))).
{ rewrite Hlh. forward. forward.
  { entailer!. apply prop_right. destruct (a_ib a); try contradiction. simpl. unfold sameblock.
    destruct (peq b b); [reflexivity | congruence]. }
  pose proof (Zlength_nonneg hb).
  entailer!.
  - rewrite sub_pp_tschar_any by (auto; lia). unfold vlong. simpl.
    match goal with H: (if _ then 1 else 0) <> 0 |- _ => rename H into Hnz end.
    destruct (negb _ && negb _ && _)%bool; simpl in Hnz |- *; [|lia].
    unfold Int64.eq. rewrite !Int64.unsigned_repr by rep_lia.
    destruct (zeq _ _); destruct (Z.eqb_spec (Zlength hb) (w_ipc w - a_ipos a)); try lia; reflexivity.
  - rewrite Hlh. cancel. }
{ forward. entailer!. destruct (negb _ && negb _ && _)%bool; [discriminate | reflexivity]. }
forward_if.
2: { forward.
  (* the shortcut's conditions fail *)
  assert (Hn: lhB_none a w hb h).
  { unfold lhB_none. intros Hu Ht Hcc Hl cS' _. exfalso.
    match goal with H: context [if ?b then 1 else 0] |- _ =>
      let Eb := fresh "Eb" in
      assert (Eb: b = true) by (rewrite !andb_true_iff, !negb_true_iff, !Z.eqb_neq, Z.leb_le, Z.eqb_eq; lia);
      rewrite Eb in H; revert H; clear; intro H;
      first [discriminate H | exact (Int.one_not_zero H) | apply H; reflexivity | inversion H] end. }
  thaw FRF; thaw FR2; thaw FR1; thaw FR0.
  unfold lh_stt, ds_LI_St, ds_LI_L, ctx_rep3t, sgroup. cbn [lw_k w_k w_smw w_ipc w_opc w_oc].
  rewrite lhB_fg_split, Hfp.
  entailer!. }
match goal with H: (if ?b then 1 else 0) <> 0 |- _ => assert (Hc: b = true) by (destruct b; auto; lia) end.
match goal with H: Int.repr _ <> Int.zero |- _ => clear H end.
match goal with H: (if _ then 1 else 0) <> 0 |- _ => clear H end.
rewrite !andb_true_iff in Hc. destruct Hc as [[[Hc1 Hc2] Hc3] Hc4].
rewrite negb_true_iff, Z.eqb_neq in Hc1, Hc2. rewrite Z.leb_le in Hc3. rewrite Z.eqb_eq in Hc4.
assert (Hfmt: dp_fmt (c3_par k1) = 0 \/ dp_fmt (c3_par k1) = 1) by (destruct H11; tauto).
forward.
forward_call (a_gv a, a_shb a, a_ib a, a_isz a, zbytes (a_ibs a), a_ipos a, sublist (a_ipos a) (a_isz a) (a_ibs a),
  dp_fmt (c3_par k1)).
{ entailer!; try apply prop_right; destruct (a_ib a); try contradiction; simpl; unfold sameblock;
  destruct (peq b b); simpl; auto; congruence. }
{ entailer!. rewrite sub_pp_tschar_any by (auto; lia). rewrite Zlength_sublist by lia. reflexivity. }
{ unfold win_ok.
  rewrite !Zlength_sublist by lia; replace (a_ipos a + (a_isz a - a_ipos a)) with (a_isz a) by lia.
  split; auto; split; [lia|]; split; [lia|]; split; [lia|]; split; [rewrite Zlength_map; auto|].
  split; [rewrite ?Zlength_sublist by lia; lia|]; split; [apply lhB_bytes_sub; auto|];
  rewrite sublist_map; f_equal; f_equal; lia. }
Intros cSize. match goal with H: 0 <= cSize <= _ |- _ => rename H into HcS end.
match goal with H: match frame_compressed_size_m _ _ with _ => _ end |- _ => rename H into Hfc0 end.
forward.
forward_if.
{ entailer!; try apply prop_right; destruct (a_ib a); try contradiction; simpl; unfold sameblock;
  destruct (peq b b); simpl; auto; congruence. }
2: { forward.
  (* the frame does not end within the input *)
  assert (Hn: lhB_none a w hb h).
  { unfold lhB_none. intros _ _ _ _ cS' Hc'.
    match goal with H: typed_false _ _ |- _ => rename H into Htf end.
    rewrite sub_pp_tschar_any in Htf by (auto; lia). unfold typed_false in Htf. simpl in Htf. unfold Int64.ltu in Htf.
    rewrite !Int64.unsigned_repr in Htf by rep_lia.
    rewrite <- Hmg in Hc'. unfold lh_mg in Hc'.
    change (dp_fmt (c3_par k1) =? 1) with (fmt_mg (dp_fmt (c3_par k1))) in Hc'.
    rewrite Hc' in Hfc0. cbv beta iota in Hfc0. subst cS'.
    destruct (zlt (a_isz a - a_ipos a) cSize); [lia|]. simpl in Htf. discriminate. }
  thaw FRF; thaw FR2; thaw FR1; thaw FR0.
  unfold lh_stt, ds_LI_St, ds_LI_L, ctx_rep3t, sgroup. cbn [lw_k w_k w_smw w_ipc w_opc w_oc].
  rewrite lhB_fg_split, Hfp.
  entailer!. }
match goal with H: typed_true _ _ |- _ => rename H into Htt end.
rewrite sub_pp_tschar_any in Htt by (auto; lia). unfold typed_true in Htt. simpl in Htt. unfold Int64.ltu in Htt.
rewrite !Int64.unsigned_repr in Htt by rep_lia.
destruct (zlt (a_isz a - a_ipos a) cSize); simpl in Htt; [discriminate|].
assert (HcS2: cSize <= a_isz a - a_ipos a) by lia. clear Htt.
assert (Hfc: frame_compressed_size_m (lh_mg k1) (sublist (a_ipos a) (a_isz a) (a_ibs a)) = Some cSize).
{ unfold lh_mg. change (dp_fmt (c3_par k1) =? 1) with (fmt_mg (dp_fmt (c3_par k1))).
  destruct (frame_compressed_size_m _ _); [subst; auto|]. unfold is_error_code in Hfc0. apply Z.ltb_lt in Hfc0. lia. }
clear Hfc0.
(* ZSTD_getDDict may free the local DDict through the context's allocator; its argument is the number of bytes the
   allocator has given out besides the local DDict (the context, the set, the stream buffer) *)
unfold mgroup. Intros.
match goal with H: cmem_ok _ |- _ => rename H into Hcm end.
assert (Hlm: local_mem (sf_mem (c3_s k1)) (c3_dict k1)) by (destruct Hbmem as (_ & _ & Hl); exact Hl).
assert (Hdz: 0 <= dctx_size) by (unfold dctx_size; simpl; lia).
assert (Hhb: 0 <= sf_given (c3_s k1) - local_held (c3_dict k1)) by (unfold sf_given; lia).
replace (cm_have (sf_mem (c3_s k1)) (sf_given (c3_s k1)))
  with (cm_have (sf_mem (c3_s k1)) (sf_given (c3_s k1) - local_held (c3_dict k1) + local_held (c3_dict k1)))
  by (f_equal; lia).
freeze FRM := (field_at _ _ (DOT _customMem) _ _) (blk_tok _ _ _).
forward_call (a_gv a, a_d a, c3_dict k1, sf_mem (c3_s k1), sf_given (c3_s k1) - local_held (c3_dict k1)).
{ apply (lhB_getddict_pre (a_st a)); auto. rewrite <- Hbset; auto. }
set (d2 := snd (getddict_res (c3_dict k1))).
forward. forward.
(* F7: the capacity is fParams.frameContentSize *)
match goal with |- context [temp _t'140 ?v] => change v with (Vlong (Int64.repr (fh_contentSize h))) end.
assert_PROP (field_compatible (tarray tuchar (a_osz a)) [] (a_ob a)) as Hfo by entailer!.
assert_PROP (field_compatible (tarray tuchar (a_isz a)) [] (a_ib a)) as Hfi by entailer!.
rewrite (lhB_arr_split (a_shob a) (a_osz a) (w_opc w)) by (auto; lia).
(* the call's output is the first fh_contentSize h cells of the output space; the cells ro after it stay *)
assert_PROP (field_compatible (tarray tuchar (a_osz a - w_opc w)) [] (offset_val (w_opc w) (a_ob a))) as Hfo2
  by entailer!.
assert (Hlo2: Zlength (sublist (w_opc w) (a_osz a) (w_oc w)) = a_osz a - w_opc w) by (rewrite Zlength_sublist; lia).
rewrite (lhB_arr_split (a_shob a) (a_osz a - w_opc w) (fh_contentSize h) (sublist (w_opc w) (a_osz a) (w_oc w)))
  by (auto; lia).
rewrite offset_offset_val.
set (ro := sublist (fh_contentSize h) (a_osz a - w_opc w) (sublist (w_opc w) (a_osz a) (w_oc w))).
assert (Hlro: Zlength ro = a_osz a - w_opc w - fh_contentSize h) by (subst ro; rewrite Zlength_sublist; lia).
rewrite (lhB_arr_split (a_shb a) (a_isz a) (a_ipos a) (zbytes (a_ibs a))) by (auto; rewrite ?Zlength_map; lia).
assert_PROP (field_compatible (tarray tuchar (a_isz a - a_ipos a)) [] (offset_val (a_ipos a) (a_ib a))) as Hfi2
  by entailer!.
rewrite (lhB_arr_split (a_shb a) (a_isz a - a_ipos a) cSize) by (auto; rewrite ?Zlength_sublist; rewrite ?Zlength_map; lia).
rewrite offset_offset_val.
set (s := sublist (a_ipos a) (a_ipos a + cSize) (a_ibs a)).
assert (Hls: Zlength s = cSize) by (subst s; rewrite Zlength_sublist; lia).
assert (Es: sublist 0 cSize (sublist (a_ipos a) (a_isz a) (zbytes (a_ibs a))) = zbytes s).
{ subst s. rewrite sublist_sublist by lia. rewrite sublist_map. f_equal. f_equal; lia. }
rewrite Es.
sep_apply (data_at_data_at_ (a_shob a) (tarray tuchar (fh_contentSize h))
  (sublist 0 (fh_contentSize h) (sublist (w_opc w) (a_osz a) (w_oc w))) (offset_val (w_opc w) (a_ob a))).
set (W' := pw_bytes (a_shob a) (w_opc w) (sublist 0 (w_opc w) (w_oc w)) (a_ob a) ::
           pw_bytes (a_shob a) (a_osz a - w_opc w - fh_contentSize h) ro
             (offset_val (w_opc w + fh_contentSize h) (a_ob a)) ::
           pw_bytes (a_shb a) (a_ipos a) (sublist 0 (a_ipos a) (zbytes (a_ibs a))) (a_ib a) ::
           pw_bytes (a_shb a) (a_isz a - a_ipos a - cSize)
             (sublist cSize (a_isz a - a_ipos a) (sublist (a_ipos a) (a_isz a) (zbytes (a_ibs a))))
             (offset_val (a_ipos a + cSize) (a_ib a)) :: a_W a).
assert (HbW1: buf_ok W' (a_shob a) (fh_contentSize h) (offset_val (w_opc w) (a_ob a))).
{ apply lhB_buf_ok3; auto; try lia. apply lhB_buf_ok_cons, lhB_buf_ok_cons.
  replace (w_opc w + fh_contentSize h + (a_osz a - w_opc w - fh_contentSize h)) with (a_osz a) by lia. auto. }
assert (HbW2: buf_ok W' (a_shb a) (Zlength s) (offset_val (a_ipos a) (a_ib a))).
{ apply lhB_buf_ok_cons, lhB_buf_ok_cons. rewrite Hls. apply lhB_buf_ok3; auto; try lia.
  replace (a_ipos a + cSize + (a_isz a - a_ipos a - cSize)) with (a_isz a) by lia. auto. }
assert (HdnW: stream_dict_ok W' (a_st a)) by (unfold W'; repeat apply lhB_stream_dict_ok_cons; auto).
destruct (lend_B Hlend DENT (a_gv a) (a_d a) W' (a_st a) k1 tbl (a_shob a) (fh_contentSize h)
  (offset_val (w_opc w) (a_ob a)) (sf_mem (c3_s k1)) (sf_given (c3_s k1) - local_held (c3_dict k1))
  (sf_held (c3_s k1) - local_held (c3_dict k1)) Hbset Hbdr Hbcur HdnW Hddb Wshob HbW1 ltac:(lia)) as [Rf [HL1 HL2]].
unfold lb_pre, lb_post, lb_mid in HL1, HL2. unfold lb_d2 in HL1, HL2. fold d2 in HL1, HL2.
sep_apply HL1. Intros ad.
match goal with H: lb_facts _ _ _ _ _ _ ad |- _ => rename H into Hfa end.
assert (Hfa0 := Hfa). destruct Hfa as (Hdd & Hdq & Hdok & Hmsel & Hmod & Hmods).
unfold lb_d2 in Hmsel. fold d2 in Hmsel.
try flatten_sepcon_in_SEP.
(* from the configuration of a new context: no dictionary argument, the default parameters *)
assert_PROP (sel_on (c3_par k1) (c3_sp k1) = false -> darg_ddict ad = nullval -> ad = DA_none) as Hadn.
{ destruct (sel_on (c3_par k1) (c3_sp k1)) eqn:Esel; [apply prop_right; intros E; discriminate E|].
  destruct (Val.eq (darg_ddict ad) nullval) as [En|En]; [|apply prop_right; intros _ E; contradiction].
  sep_apply (lhB_darg_none DENT (a_gv a) (c3_par k1) (c3_sp k1) d2 ad Hdd Esel En). entailer!. }
assert (Hfrx: fresh_cfg (a_st a) -> ad = DA_none /\ c3_par k1 = dparams_dflt).
{ intros Hfr. assert (Hp: c3_par k1 = dparams_dflt) by (rewrite Hbpar; exact (proj1 (proj2 Hfr))).
  split; [|exact Hp]. apply Hadn; [rewrite Hp; reflexivity|].
  rewrite Hdq. exact (lhB_fresh_ddict (a_st a) (c3_dict k1) Hfr Hbdr). }
thaw FRM. thaw FRF. rewrite <- Hfp.
sep_apply (lhB_fg_fold TABS (a_gv a) (a_d a) (c3_fs k1) (c3_tabs k1) (c3_par k1) (c3_sp k1) H10 H11).
assert_PROP (Zlength (tabs_lxb (c3_tabs k1)) = LITEXTRA_N) as Hlxlen
  by (sep_apply (lhB_fg_lxb TABS (a_gv a) (a_d a) (c3_fs k1) (c3_tabs k1) (c3_par k1) (c3_sp k1) HT); entailer!).
freeze FRW := (Rf ad).
sep_apply (lhB_pws4_i (a_shob a) (w_opc w) (sublist 0 (w_opc w) (w_oc w)) (a_ob a)
  (a_shob a) (a_osz a - w_opc w - fh_contentSize h) ro (offset_val (w_opc w + fh_contentSize h) (a_ob a))
  (a_shb a) (a_ipos a) (sublist 0 (a_ipos a) (zbytes (a_ibs a))) (a_ib a)
  (a_shb a) (a_isz a - a_ipos a - cSize)
  (sublist cSize (a_isz a - a_ipos a) (sublist (a_ipos a) (a_isz a) (zbytes (a_ibs a))))
  (offset_val (a_ipos a + cSize) (a_ib a)) (a_W a)).
replace (data_at (a_shb a) (tarray tuchar cSize) (zbytes s) (offset_val (a_ipos a) (a_ib a)))
  with (data_at (a_shb a) (tarray tuchar (Zlength s)) (zbytes s) (offset_val (a_ipos a) (a_ib a)))
  by (rewrite Hls; auto).
rewrite <- Hdq.
(* the call's destination is a pointer: its array is the callee's mbuf *)
assert (Hpo: isptr (offset_val (w_opc w) (a_ob a))) by (destruct Hfo as [Hp _]; destruct (a_ob a); try contradiction; exact I).
sep_apply (data_at__mbuf (a_shob a) (fh_contentSize h) (offset_val (w_opc w) (a_ob a))).
(* the selection's free (of getDDict's local DDict) through the context's allocator *)
assert (Hselm: sel_mem (c3_par k1) (c3_sp k1) d2 (sf_mem (c3_s k1)) (sf_given (c3_s k1) - local_held (c3_dict k1))).
{ intros _. split; [| split; auto]. apply (local_mem_redict _ (c3_dict k1)); [apply redict_ok_getddict | exact Hlm]. }
forward_call (W', a_gv a, a_d a, c3_fs k1, c3_tabs k1, c3_par k1, c3_sp k1, d2, c3_set k1, tbl, Ews,
  a_shob a, offset_val (w_opc w) (a_ob a), fh_contentSize h, a_shb a, offset_val (a_ipos a) (a_ib a), s, ad,
  sf_mem (c3_s k1), sf_given (c3_s k1) - local_held (c3_dict k1)).
all: try solve [entailer!; try apply prop_right; destruct (a_ob a); try contradiction; simpl; unfold sameblock;
  destruct (peq b b); simpl; auto; congruence].
all: try solve [entailer!; rewrite sub_pp_tschar_any by (auto; lia); rewrite Hls; reflexivity].
all: try solve [entailer!; rewrite Hls; reflexivity].
all: try solve [unfold W'; cancel].
all: try solve [subst s; apply lhB_bytes_sub; auto].
all: try solve [exact Hselm].
Intros vr. destruct vr as [[[[r outv] fs1] d'] lxb1]. cbn [fst snd] in *.
match goal with H: ad = DA_none -> c3_par k1 = dparams_dflt -> os_match _ _ _ _ |- _ => rename H into Hosm end.
match goal with H: context [lxb1 = ExBlock.x_lxb _ _] |- _ => rename H into Hlxp end.
rewrite mbuf_isptr by exact Hpo.
match goal with H: d' = d2 \/ _ |- _ => rename H into Hd' end.
assert (Hfp1: fp_ok (fs_fParams fs1))
  by (match goal with H: fp_ok (fs_fParams (c3_fs k1)) -> fp_ok (fs_fParams fs1) |- _ => exact (H Hbfp) end).
thaw FRW.
sep_apply (HL2 ad d' Hfa0 Hd').
flatten_sepcon_in_SEP.
unfold W'.
sep_apply (lhB_pws4_e (a_shob a) (w_opc w) (sublist 0 (w_opc w) (w_oc w)) (a_ob a)
  (a_shob a) (a_osz a - w_opc w - fh_contentSize h) ro (offset_val (w_opc w + fh_contentSize h) (a_ob a))
  (a_shb a) (a_ipos a) (sublist 0 (a_ipos a) (zbytes (a_ibs a))) (a_ib a)
  (a_shb a) (a_isz a - a_ipos a - cSize)
  (sublist cSize (a_isz a - a_ipos a) (sublist (a_ipos a) (a_isz a) (zbytes (a_ibs a))))
  (offset_val (a_ipos a + cSize) (a_ib a)) (a_W a)).
match goal with H: Zlength outv = _ |- _ => rename H into Hlo end.
assert (Jo1: data_at (a_shob a) (tarray tuchar (fh_contentSize h)) outv (offset_val (w_opc w) (a_ob a)) *
  data_at (a_shob a) (tarray tuchar (a_osz a - w_opc w - fh_contentSize h)) ro
    (offset_val (w_opc w + fh_contentSize h) (a_ob a)) |--
  data_at (a_shob a) (tarray tuchar (a_osz a - w_opc w)) (outv ++ ro) (offset_val (w_opc w) (a_ob a))).
{ apply lhB_join; auto; try lia; rewrite offset_offset_val; reflexivity. }
sep_apply Jo1. clear Jo1.
assert (Jo: data_at (a_shob a) (tarray tuchar (w_opc w)) (sublist 0 (w_opc w) (w_oc w)) (a_ob a) *
  data_at (a_shob a) (tarray tuchar (a_osz a - w_opc w)) (outv ++ ro) (offset_val (w_opc w) (a_ob a)) |--
  data_at (a_shob a) (tarray tuchar (a_osz a)) (sublist 0 (w_opc w) (w_oc w) ++ (outv ++ ro)) (a_ob a)).
{ apply lhB_join; auto; try list_solve; rewrite Zlength_app; lia. }
sep_apply Jo. clear Jo.
set (rest := sublist cSize (a_isz a - a_ipos a) (sublist (a_ipos a) (a_isz a) (zbytes (a_ibs a)))).
assert (Ji1: data_at (a_shb a) (tarray tuchar (Zlength s)) (zbytes s) (offset_val (a_ipos a) (a_ib a)) *
  data_at (a_shb a) (tarray tuchar (a_isz a - a_ipos a - cSize)) rest (offset_val (a_ipos a + cSize) (a_ib a)) |--
  data_at (a_shb a) (tarray tuchar (a_isz a - a_ipos a)) (zbytes s ++ rest) (offset_val (a_ipos a) (a_ib a))).
{ apply lhB_join; auto.
  - rewrite Zlength_map; auto.
  - subst rest. list_solve.
  - subst rest. list_solve.
  - rewrite offset_offset_val, Hls. auto. }
sep_apply Ji1. clear Ji1.
assert (Ji2: data_at (a_shb a) (tarray tuchar (a_ipos a)) (sublist 0 (a_ipos a) (zbytes (a_ibs a))) (a_ib a) *
  data_at (a_shb a) (tarray tuchar (a_isz a - a_ipos a)) (zbytes s ++ rest) (offset_val (a_ipos a) (a_ib a)) |--
  data_at (a_shb a) (tarray tuchar (a_isz a)) (sublist 0 (a_ipos a) (zbytes (a_ibs a)) ++ (zbytes s ++ rest)) (a_ib a)).
{ apply lhB_join; auto; subst rest s; list_solve. }
sep_apply Ji2. clear Ji2.
replace (sublist 0 (a_ipos a) (zbytes (a_ibs a)) ++ (zbytes s ++ rest)) with (zbytes (a_ibs a))
  by (subst rest s; list_solve).
forward.
assert (Hbs: bytes_ok s) by (subst s; apply lhB_bytes_sub; auto).
match goal with H: is_error_code r = false -> r <= fh_contentSize h |- _ => rename H into Hrf end.
assert (Ht0: fh_frameType h = 0) by (destruct Hft as [Ht0 | Ht1]; [exact Ht0 | contradiction]).
destruct Hdsa as (Hbibs & Hip0 & Hlibs). destruct Hent as (Hbhb & Hipc' & Hlenok).
assert (Hsz: fh_headerSize h = Zlength hb) by (unfold hdr_lenok in Hlenok; rewrite Hgh in Hlenok; exact Hlenok).
destruct (lhB_x_frame (lh_mg k1) (a_ibs a) (a_ipos a) (w_ipc w) (a_isz a) cSize hb h Hbibs Hlibs Hip0
  (proj1 Hipc') (proj2 Hipc') (Hhbi (eq_sym Hc4)) Hgh Hsz Hfc HcS2) as [Hgx Hfx].
(* the claims on the call's capacity fh_contentSize h carry over to the output space (F7) *)
assert (Hfacts: lhB_facts a w k1 hb h cSize r (outv ++ ro)).
{ unfold lhB_facts. split; [auto|]. split; [auto|]. split; [auto|]. split; [lia|]. split; [auto|].
  split; [lia|]. split; [auto|]. split; [rewrite Zlength_app; lia|].
  split; [intros E; specialize (Hrf E); lia|]. split; [auto|].
  intros dm Hdm.
  match goal with H1: sel_on _ _ = false \/ _ -> oneshot_ok _ _ _ _ _ _,
                  H2: sel_on _ _ = true -> _ -> oneshot_sel _ _ _ _ _ _ _ |- _ =>
    pose proof (lhB_claim MFh Hprobe a k1 tbl ad s (fh_contentSize h) r outv Hbset Hsel Hdq Hmod Hmods Hbs H1 H2
                  dm Hdm) as Hosf end.
  exact (lhB_os_cap (dmode_of (c3_par k1)) (Some dm) s h (a_osz a - w_opc w) r outv ro Hfx Hgx Ht0 Hc1 Hc3 Hlo
           ltac:(lia) Hosf). }
(* the exact facts: the one-shot model's result on the call's capacity, litExtraBuffer as the frame's model leaves it *)
assert (Hom: fresh_cfg (a_st a) -> os_match s (fh_contentSize h) r (sublist 0 (fh_contentSize h) (outv ++ ro))).
{ intros Hfr. destruct (Hfrx Hfr) as [E1 E2].
  rewrite sublist_app1 by lia. rewrite sublist_same by lia. exact (Hosm E1 E2). }
assert (Hlhx: lhB_x a w k1 h cSize r (outv ++ ro) lxb1).
{ unfold lhB_x. cbv zeta. intros Hfr. destruct (Hfrx Hfr) as [E1 E2].
  split; [exact (Hom Hfr)|]. split; [rewrite Hlxlen; reflexivity|].
  intros _ Hsk st0 e0 c0 Hst0 Hxf. first [exact (Hlxp E1 E2 Hsk st0 e0 c0 Hst0 Hxf) | exact (Hlxp E1 E2 st0 e0 c0 Hst0 Hxf)]. }
assert (Hdict: lhB_dict k1 d').
{ destruct Hd' as [E | [Hon [q [Hq E]]]]; [left; exact E | right; split; [exact Hon | exists q; auto]]. }
clear Hdok HdnW HbW1 HbW2.
forward_call r. forward_if.
{ apply semax_seq with (Q := FF); [| apply semax_ff].
  match goal with H: context [Int.repr (if is_error_code r then _ else _)] |- _ => rename H into Hie end.
  assert (Er: is_error_code r = true)
    by (revert Hie; destruct (is_error_code r); intros Hie; [auto | contradiction Hie; reflexivity]).
  clear Hie.
  lhB_return.
  thaw FR2; thaw FR1; thaw FR0.
  cbv beta iota delta [overridePost lhB_post_x RA_return lh_ret_x].
  Exists r (a_ipos a) {| w_smw := w_smw w; w_k := lhB_k k1 fs1 d' lxb1; w_sv := w_sv w; w_ipc := w_ipc w;
         w_opc := w_opc w; w_oc := sublist 0 (w_opc w) (w_oc w) ++ (outv ++ ro); w_dl := w_dl w |}.
  sep_apply (lhB_hset_fold (sf_mem (c3_s k1)) (c3_sp k1) (c3_set k1) (sf_held (c3_s k1) - local_held (c3_dict k1)) tbl).
  (* the allocator's bytes and the set's after the shortcut, as the stream fields lhB_s k1 d' count them *)
  replace (cm_have (sf_mem (c3_s k1)) (sf_given (c3_s k1) - local_held (c3_dict k1) + local_held d'))
    with (cm_have (sf_mem (c3_s k1)) (sf_given (lhB_s k1 d'))) by (rewrite lhB_s_given; reflexivity).
  rewrite <- (lhB_s_held k1 d').
  pose proof (local_held_nonneg d') as Hlh'.
  unfold ds_S_ip, ds_LI_L, ctx_rep3, ctx_body3, sgroup, mgroup, lhB_k.
  cbn [w_smw w_k w_sv w_ipc w_opc w_oc w_dl c3_fs c3_s c3_tabs c3_dict c3_stable c3_par c3_sp c3_set c3_with_dict c3_with_fs
       c3_with_s].
  unfold lhB_s, held_redict, sf_with_held.
  cbn [sf_stage_set sf_stage sf_inBuff sf_inSize sf_inPos sf_outBuff sf_outSize sf_outStart sf_outEnd
       sf_lhSize sf_hostage sf_nfp sf_expOut sf_hbuf sf_over sf_ring sf_mem sf_held].
  (* F10: ZSTD_decompress_usingDDict left streamStage = zdss_init *)
  unfold zdss_init.
  rewrite !prop_true_andp by (first [tauto | (repeat split; auto; rep_lia)]).
  go_lower. apply andp_right.
  { apply prop_right. split; [reflexivity|]. split; [lia|].
    split; [apply (HRC cSize r (outv ++ ro) fs1 d' lxb1); auto|].
    split; [exact (HRX cSize r (outv ++ ro) fs1 d' lxb1 Hfacts Er Hom Hlxlen)|].
    repeat split. }
  unfold sf_given; cbn [sf_mem sf_held sf_inSize sf_outSize sf_stage_set]; cancel. }
match goal with H: context [Int.repr (if is_error_code r then _ else _)] |- _ => rename H into Hie end.
assert (Er: is_error_code r = false)
  by (revert Hie; destruct (is_error_code r); intros Hie; [exfalso; apply Int.one_not_zero; exact Hie | auto]).
clear Hie.
match goal with H: is_error_code r = false -> exists c, _ |- _ => destruct (H Er) as (c & Hcb & Hcl & Hcs) end.
assert (Hcs': sublist 0 r (outv ++ ro) = zbytes c)
  by (rewrite sublist_app1 by (pose proof (Hrf Er); lia); exact Hcs).
assert (Hsfp: lhB_sel_fp k1 tbl s fs1 d').
{ intros Hon Hn Hx.
  match goal with H: is_error_code r = false -> sel_on _ _ = true -> _ -> _ -> exists id, _ |- _ =>
    exact (H Er Hon Hn Hx) end. }
assert (Hswx: lhB_sw k1 tbl (sublist (a_ipos a) (a_ipos a + cSize) (a_ibs a)) d').
{ match goal with H: is_error_code r = false -> sel_on _ _ = true -> frame_compressed_size_m _ _ = Some _ -> _ |- _ =>
    exact (lhB_sw_of k1 tbl (a_ibs a) (a_ipos a) (w_ipc w) (a_isz a) cSize hb h d' Hbibs Hlibs Hip0
             (proj1 Hipc') (proj2 Hipc') (Hhbi (eq_sym Hc4)) Hgh Hsz Ht0 Hfc HcS2 Hdict (H Er)) end. }
assert (Hrc: r <= a_osz a - w_opc w) by (pose proof (Hrf Er); lia).
(* the frame declares its content size: a success decodes exactly that many bytes, so the cells after them are
   the output space's (ro) *)
assert (Hrfcs: r = fh_contentSize h).
{ match goal with H: is_error_code r = false -> frame_compressed_size_m _ s = Some (Zlength s) -> _ |- _ =>
    exact (H Er Hfx h Hgx Ht0 Hc1) end. }
assert (Hut: sublist (w_opc w + r) (a_osz a) (sublist 0 (w_opc w) (w_oc w) ++ (outv ++ ro)) =
             sublist (w_opc w + r) (a_osz a) (w_oc w)).
{ subst ro. rewrite Hrfcs. list_solve. }
unfold MORE_COMMANDS, abbreviate. apply semax_dowhile0.
forward. forward.
forward_if (temp _t'27 (offset_val (w_opc w + r) (a_ob a))).
{ assert (Hw: pws_pred (a_W a) * data_at (a_shob a) (tarray tuchar (a_osz a))
     (sublist 0 (w_opc w) (w_oc w) ++ (outv ++ ro)) (a_ob a) * TT |-- weak_valid_pointer (offset_val (w_opc w) (a_ob a)))
    by (apply wvp_buf; auto; lia).
  revert Hw. destruct (a_ob a) eqn:Eob; try contradiction. intros Hw.
  Transparent denote_tc_test_eq. unfold denote_tc_test_eq. simpl.
  apply andp_right; [apply prop_right; auto|]. eapply derives_trans; [|exact Hw]. cancel. }
Opaque denote_tc_test_eq.
{ forward. forward. entailer!. }
{ exfalso. match goal with H: context [Ptrofs.repr (w_opc w)] |- _ => revert H end.
  destruct (a_ob a); try contradiction. simpl. intro X; inversion X. }
forward.
rewrite lhB_fg_exp. Intros.
forward. forward. forward.
forward.
thaw FR2; thaw FR1; thaw FR0.
cbv beta iota delta [overridePost lhB_post_x RA_break].
Exists cSize r (outv ++ ro) c fs1 d' lxb1.
sep_apply (lhB_hset_fold (sf_mem (c3_s k1)) (c3_sp k1) (c3_set k1) (sf_held (c3_s k1) - local_held (c3_dict k1)) tbl).
(* the allocator's bytes and the set's after the shortcut, as the stream fields lhB_s k1 d' count them *)
replace (cm_have (sf_mem (c3_s k1)) (sf_given (c3_s k1) - local_held (c3_dict k1) + local_held d'))
  with (cm_have (sf_mem (c3_s k1)) (sf_given (lhB_s k1 d'))) by (rewrite lhB_s_given; reflexivity).
rewrite <- (lhB_s_held k1 d').
pose proof (local_held_nonneg d') as Hlh'.
unfold lhB_brk, ds_LI_L, ds_LI_S, ctx_rep3, ctx_body3, sgroup, mgroup, lhB_k.
rewrite lhB_fg_exp.
cbn [w_smw w_k w_sv w_ipc w_opc w_oc w_dl c3_fs c3_s c3_tabs c3_dict c3_stable c3_par c3_sp c3_set c3_with_dict
  c3_with_fs c3_with_s].
unfold lhB_s, held_redict, sf_with_held.
cbn [sf_stage_set sf_stage sf_inBuff sf_inSize sf_inPos sf_outBuff sf_outSize sf_outStart sf_outEnd
  sf_lhSize sf_hostage sf_nfp sf_expOut sf_hbuf sf_over sf_ring sf_mem sf_held fs_expected fsu_expected].
change (lhB_fgx TABS (a_gv a) (a_d a) (fsu_expected fs1 (vlong 0)) (TUninit lxb1) (c3_par k1) (c3_sp k1))
  with (lhB_fgx TABS (a_gv a) (a_d a) fs1 (TUninit lxb1) (c3_par k1) (c3_sp k1)).
rewrite !prop_true_andp by (first [tauto | (repeat split; auto; unfold zdss_init; rep_lia)]).
change (Int.repr zdss_init) with (Int.repr 0).
change (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with (vlong 0).
go_lower. apply andp_right.
{ apply prop_right. split; [auto|]. split; [exact Er|]. split; [exact Hcb|]. split; [exact Hcl|].
  split; [exact Hcs'|]. split; [exact Hdict|]. split; [exact Hfp1|]. split; [exact Hsfp|]. split; [exact Hswx|].
  split; [exact Hut|]. split; [exact Hlhx|].
  repeat split. apply lhB_ip_add; auto. }
unfold sf_given; cbn [sf_mem sf_held sf_inSize sf_outSize sf_stage_set]; cancel.
Qed.

End Gen.

(* the context after the selection of piece A is described by the entry facts (a hit is a member of the set) *)
Lemma lhB_entry_k1 : forall (a: dsa) (w: lw) (hb: list Z) (h: frame_header) (tbl: list val) (d1: dfields) (did1: val),
  hs_probe_ok -> lh_entry a w hb -> 0 <= fh_dictID h <= Int.max_unsigned ->
  lhA_sel (w_k w) hb 0 (fh_val h) tbl d1 did1 ->
  0 <= sf_held (c3_s (k_A (w_k w) (fh_val h) d1 did1)) - local_held (c3_dict (k_A (w_k w) (fh_val h) d1 did1)) ->
  lh_entry a (lw_k w (k_A (w_k w) (fh_val h) d1 did1)) hb.
Proof.
intros a w hb h tbl d1 did1 Hprobe He Hdid Hsel Hh1.
(* the set's bytes are the same before and after the selection *)
assert (Hh0: 0 <= sf_held (c3_s (w_k w)) - local_held (c3_dict (w_k w))).
{ unfold k_A, k_redict in Hh1. cbn [c3_s c3_dict c3_with_dict c3_with_s c3_with_fs] in Hh1.
  rewrite held_redict_set in Hh1. exact Hh1. }
pose proof (lhA_sel_redict _ _ _ _ _ _ _ Hsel) as Hrd.
destruct Hsel as (_ & _ & id & _ & Hby).
assert (Hd1: dict_rel3 (a_st a) (c3_dict (w_k w)) -> c3_set (w_k w) = dc_set (a_st a) -> dict_rel3 (a_st a) d1).
{ intros Hr Hs. unfold sel_by in Hby. destruct (sel_on _ _).
  - destruct Hby as (Hinv & Hid & Ed & _). subst d1. unfold sel_dict.
    destruct (eq_dec (sel_r (c3_dict (w_k w)) (c3_set (w_k w)) tbl id) nullval) as [E|E]; [exact Hr|].
    unfold sel_r in E |- *. destruct (eq_dec (df_ddict (c3_dict (w_k w))) nullval) as [E2|E2]; [congruence|].
    destruct (Hprobe _ _ _ Hinv Hid) as [[Hn|Hin] _]; [congruence|].
    right. rewrite <- Hs. split.
    + intros En. rewrite En in Hin. contradiction.
    + unfold dict_switched, switch_fields. cbn. auto.
  - destruct Hby as [Ed _]. subst d1. exact Hr. }
unfold lh_entry in *. cbn [lw_k w_k w_smw w_ipc w_opc w_oc] in *.
destruct He as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & Hbc & Hlen).
destruct Hbc as (B1 & B2 & B3 & B4 & B5 & B6 & Bm).
(* the allocator facts after the selection, which keeps the local DDict or frees it *)
assert (Hm: mem_call (a_st a) (k_A (w_k w) (fh_val h) d1 did1)).
{ unfold k_A. apply mem_call_redict; [exact Bm | exact Hh0 | exact Hrd]. }
clear Bm.
unfold k_A, k_redict, held_redict, sf_with_held, base_call, lh_mg in *.
cbn [c3_with_dict c3_with_fs c3_with_s c3_s c3_par c3_set c3_stable c3_dict c3_fs sf_stage sf_lhSize sf_hbuf
     sf_hostage sf_inPos sf_outStart sf_outEnd] in *.
repeat match goal with |- _ /\ _ => split end; auto; try lia.
exists (fh_dictID h). split; [reflexivity | exact Hdid].
Qed.

End CM_LH3B_1.
