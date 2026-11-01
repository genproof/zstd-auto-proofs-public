(* FS3 streaming: helpers for the body of ZSTD_decompressContinue against S3Specs (port of v2
   body_stream_continue.v). *)
Require Import Zstd.proof.dec.v3.FS.stream.S3Specs.
Require Import Zstd.proof.zstd.XxhLemmas.

Section CM_C3Base_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* ---------- the frame stage of a unit ---------- *)

Lemma bp_type_range (s: list Z) : 0 <= bp_type (block_props_of s) <= 3.
Proof.
  unfold block_props_of; simpl.
  assert (Z.land (Z.shiftr (le_field s 0 3) 1) 3 = Z.shiftr (le_field s 0 3) 1 mod 4) as ->
    by (apply (Z.land_ones _ 2); lia).
  pose proof (Z.mod_pos_bound (Z.shiftr (le_field s 0 3) 1) 4). lia.
Qed.

Lemma cf_stage fs tabs fp l dd n :
  c_frame fs tabs fp l dd -> fp_complete fp = false -> unit_ok fp n -> 0 <= n <= Int64.max_unsigned ->
  exists st e,
    fs_stage fs = Vint (Int.repr st) /\ fs_expected fs = Vlong (Int64.repr e) /\
    0 <= e <= Int64.max_unsigned /\
    (st = 2 \/ st = 3 \/ st = 4 \/ st = 5 \/ st = 7) /\
    ((st = 3 \/ st = 4) -> exists b, fs_bType fs = Vint (Int.repr b) /\ 0 <= b <= 3) /\
    next_size st (match fs_bType fs with Vint b => Int.signed b | _ => 0 end) e n = n.
Proof.
  intros Hc Hnc Hu Hn. destruct Hc as (_ & _ & _ & _ & _ & Hc).
  destruct fp as [ | | hdr got | hdr z]; try contradiction.
  - destruct Hc as (_ & _ & _ & Hg & Hle & Hst). simpl in Hnc, Hu. destruct Hu as [-> ->].
    rewrite Hnc in Hst. destruct Hst as [Hs He].
    exists ds_skipFrame, (le_field hdr 4 4). split; [auto | split; [auto |]].
    split; [rep_lia |]. split; [unfold ds_skipFrame; lia |].
    split; [unfold ds_skipFrame; lia |]. reflexivity.
  - destruct Hc as (_ & _ & Hbsm & Hbsm2 & _ & _ & _ & _ & _ & _ & Hph & _ & _ & _ & _ & Hm & _).
    unfold phase_fields in Hph. cbn [fp_complete unit_ok] in Hnc, Hu.
    destruct (zp_ph z) as [ | bh | | ] eqn:Ez; try discriminate.
    + destruct Hph as [Hs He]. destruct Hu as [_ ->].
      exists ds_decodeBlockHeader, ZSTD_blockHeaderSize. unfold ds_decodeBlockHeader, ZSTD_blockHeaderSize in *.
      repeat split; auto; try rep_lia; intros [? | ?]; lia.
    + destruct Hph as (c & Hcs & Hs & Hb & _ & He). destruct Hu as (c' & Hc' & Hu).
      rewrite Hcs in Hc'. inv Hc'.
      pose proof (bp_type_range bh) as Hbt.
      destruct Hm as (_ & _ & c2 & Hc2 & Hcr & Hgl & _).
      rewrite Hcs in Hc2; inv Hc2.
      exists (if bp_last (block_props_of bh) =? 1 then ds_decompressLastBlock else ds_decompressBlock).
      exists (if bp_type (block_props_of bh) =? 0 then c2 - Zlength (zp_got z) else c2).
      split; [auto | split; [auto |]].
      split. { pose proof (Zlength_nonneg (zp_got z)). unfold ZSTD_BLOCKSIZE_MAX in Hbsm2.
               destruct (_ =? 0); rep_lia. }
      split. { destruct (_ =? 1); unfold ds_decompressLastBlock, ds_decompressBlock; lia. }
      split. { intros _. exists (bp_type (block_props_of bh)). split; auto. }
      rewrite Hb. rewrite Int.signed_repr by rep_lia. unfold next_size.
      replace (orb _ _) with true
        by (destruct (_ =? 1); unfold ds_decompressLastBlock, ds_decompressBlock; reflexivity).
      destruct (bp_type (block_props_of bh) =? 0) eqn:Et; simpl.
      * lia.
      * lia.
    + destruct Hph as [Hs He]. destruct Hu as [_ ->].
      exists ds_checkChecksum, 4. unfold ds_checkChecksum in *.
      repeat split; auto; try rep_lia; intros [? | ?]; lia.
Qed.

Lemma lev_range (l: list Z) : bytes_ok l -> 0 <= le_value l < 2 ^ (8 * Zlength l).
Proof.
  intros H. induction H; cbn [le_value].
  - rewrite Zlength_nil. simpl. lia.
  - unfold is_byte in H. rewrite Zlength_cons. replace (8 * Z.succ (Zlength l)) with (8 + 8 * Zlength l) by lia.
    rewrite Z.pow_add_r by (pose proof (Zlength_nonneg l); lia).
    change (2^8) with 256. lia.
Qed.

Lemma lef_range (l: list Z) i k : bytes_ok l -> 0 <= k -> 0 <= le_field l i k < 2 ^ (8 * k).
Proof.
  intros H Hk. unfold le_field, slice.
  assert (Hb: bytes_ok (firstn (Z.to_nat k) (skipn (Z.to_nat i) l))).
  { unfold bytes_ok in *. apply Forall_firstn, Forall_skipn; auto. }
  pose proof (lev_range _ Hb).
  assert (Zlength (firstn (Z.to_nat k) (skipn (Z.to_nat i) l)) <= k).
  { rewrite Zlength_correct, firstn_length. lia. }
  assert (2 ^ (8 * Zlength (firstn (Z.to_nat k) (skipn (Z.to_nat i) l))) <= 2 ^ (8 * k)).
  { apply Z.pow_le_mono_r; [lia |]. pose proof (Zlength_nonneg (firstn (Z.to_nat k) (skipn (Z.to_nat i) l))). lia. }
  lia.
Qed.

Lemma ck_iff a D : 0 <= a < 2 ^ 32 -> (Int.repr a = Int.repr (Int64.Z_mod_modulus D) <-> a = D mod 2 ^ 32).
Proof.
  intros Ha. rewrite Int64.Z_mod_modulus_eq.
  assert (Hm: (D mod Int64.modulus) mod 2 ^ 32 = D mod 2 ^ 32).
  { change Int64.modulus with (2 ^ 32 * 2 ^ 32). rewrite Z.rem_mul_r by lia.
    rewrite Z.mul_comm, Z_mod_plus_full. apply Z.mod_mod. lia. }
  split; intros E.
  - apply (f_equal Int.unsigned) in E. rewrite Int.unsigned_repr in E by rep_lia.
    rewrite Int.unsigned_repr_eq in E. change Int.modulus with (2 ^ 32) in E. rewrite Hm in E. auto.
  - rewrite <- (Int.repr_unsigned (Int.repr (D mod Int64.modulus))). rewrite Int.unsigned_repr_eq.
    change Int.modulus with (2 ^ 32). rewrite Hm, <- E. reflexivity.
Qed.

(* ---------- pointers into the output array ---------- *)

Lemma fc_arr N base :
  field_compatible (tarray tuchar N) [] base -> 0 <= N ->
  exists b ofs, base = Vptr b ofs /\ Ptrofs.unsigned ofs + N < Ptrofs.modulus.
Proof.
  intros (Hp & _ & Hs & _) HN. destruct base; try contradiction. exists b, i. split; auto.
  red in Hs. simpl in Hs. rewrite Z.max_r in Hs by lia. lia.
Qed.

Lemma off_unsigned ofs d :
  0 <= d -> Ptrofs.unsigned ofs + d < Ptrofs.modulus ->
  Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr d)) = Ptrofs.unsigned ofs + d.
Proof.
  intros. rewrite Ptrofs.add_unsigned, (Ptrofs.unsigned_repr d) by rep_lia.
  apply Ptrofs.unsigned_repr. rep_lia.
Qed.

Lemma vptr_add2 b ofs x y :
  Vptr b (Ptrofs.add (Ptrofs.add ofs (Ptrofs.repr x)) (Ptrofs.repr y)) = offset_val (x + y) (Vptr b ofs).
Proof. simpl. rewrite Ptrofs.add_assoc, ptrofs_add_repr. reflexivity. Qed.

Lemma veqb_off b ofs N x y :
  Ptrofs.unsigned ofs + N < Ptrofs.modulus -> 0 <= x <= N -> 0 <= y <= N ->
  veqb (offset_val x (Vptr b ofs)) (offset_val y (Vptr b ofs)) = (x =? y).
Proof.
  intros HN Hx Hy. unfold veqb. simpl.
  destruct (Val.eq _ _) as [E | E]; destruct (Z.eqb_spec x y) as [-> | Ne]; auto.
  - exfalso. assert (E': Ptrofs.add ofs (Ptrofs.repr x) = Ptrofs.add ofs (Ptrofs.repr y)) by congruence.
    apply (f_equal Ptrofs.unsigned) in E'. rewrite !off_unsigned in E' by lia. lia.
Qed.

Lemma vptr_diff_off b ofs N x y :
  Ptrofs.unsigned ofs + N < Ptrofs.modulus -> 0 <= x <= N -> 0 <= y <= N ->
  vptr_diff (offset_val x (Vptr b ofs)) (offset_val y (Vptr b ofs)) = x - y.
Proof. intros. simpl. rewrite !off_unsigned by lia. lia. Qed.

Lemma arr_wvp sh N (c: list val) p d :
  sepalg.nonidentity sh -> 0 <= d <= N -> 0 < N ->
  data_at sh (tarray tuchar N) c p |-- weak_valid_pointer (offset_val d p).
Proof.
  intros. eapply derives_trans; [apply data_at_memory_block |].
  apply memory_block_weak_valid_pointer; auto; simpl; rep_lia.
Qed.

Lemma arr_test_eq_pp sh N (c: list val) b ofs x y R :
  sepalg.nonidentity sh -> 0 <= x <= N -> 0 <= y <= N -> 0 < N ->
  data_at sh (tarray tuchar N) c (Vptr b ofs) * R
  |-- denote_tc_test_eq (offset_val x (Vptr b ofs)) (offset_val y (Vptr b ofs)).
Proof.
  intros. Transparent denote_tc_test_eq. unfold denote_tc_test_eq; simpl.
  unfold test_eq_ptrs, sameblock. destruct (peq b b) as [Hb | Hn]; [simpl | congruence].
  apply andp_right; apply sepcon_weak_valid_pointer1.
  - change (Vptr b (Ptrofs.add ofs (Ptrofs.repr x))) with (offset_val x (Vptr b ofs)). apply arr_wvp; auto.
  - change (Vptr b (Ptrofs.add ofs (Ptrofs.repr y))) with (offset_val y (Vptr b ofs)). apply arr_wvp; auto.
Qed.

Lemma arr_test_eq_pn sh N (c: list val) b ofs x R :
  sepalg.nonidentity sh -> 0 <= x <= N -> 0 < N ->
  data_at sh (tarray tuchar N) c (Vptr b ofs) * R |-- denote_tc_test_eq (offset_val x (Vptr b ofs)) nullval.
Proof.
  intros. Transparent denote_tc_test_eq. unfold denote_tc_test_eq; simpl.
  apply andp_right; [apply prop_right; auto |]. apply sepcon_weak_valid_pointer1.
  change (Vptr b (Ptrofs.add ofs (Ptrofs.repr x))) with (offset_val x (Vptr b ofs)). apply arr_wvp; auto.
Qed.

Lemma test_eq_nn R : R |-- denote_tc_test_eq nullval nullval.
Proof. Transparent denote_tc_test_eq. unfold denote_tc_test_eq; simpl. apply andp_right; apply prop_right; auto. Qed.

Lemma pws_cons_bytes sh N c base W :
  pws_pred (pw_bytes sh N c base :: W) = (data_at sh (tarray tuchar N) c base * pws_pred W)%logic.
Proof. reflexivity. Qed.

Lemma pws_cons_fold sh N c base W :
  data_at sh (tarray tuchar N) c base * pws_pred W |-- pws_pred (pw_bytes sh N c base :: W).
Proof. rewrite pws_cons_bytes. apply derives_refl. Qed.

(* ---------- ZSTD_checkContinuity on the layout ---------- *)

(* the dictionary array of an HL_dict layout fits in its block *)
Definition lay_ptr (l: hlay) : Prop :=
  match l with
  | HL_dict eb ec _ => exists b ofs, eb = Vptr b ofs /\ Ptrofs.unsigned ofs + Zlength ec < Ptrofs.modulus
  | _ => True
  end.

Lemma veqb_refl v : veqb v v = true.
Proof. unfold veqb; destruct (Val.eq v v); congruence. Qed.

Lemma veqb_ptr_null v : isptr v -> veqb v nullval = false.
Proof. intros Hv. unfold veqb. destruct (Val.eq v nullval); auto. subst. contradiction. Qed.

Lemma veqb_01 : veqb (Vint (Int.repr 1)) (Vint (Int.repr 0)) = false.
Proof. reflexivity. Qed.

Lemma vptr_diff_base b ofs k :
  0 <= k -> Ptrofs.unsigned ofs + k < Ptrofs.modulus -> vptr_diff (offset_val k (Vptr b ofs)) (Vptr b ofs) = k.
Proof. intros. simpl. rewrite off_unsigned by lia. lia. Qed.

End CM_C3Base_1.

Ltac vp_solve := rewrite ?vptr_add2; unfold offset_val; repeat f_equal; lia.

Section CM_C3Base_2.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.

Lemma cont_cframe fs tabs fp l dd o b ofs W :
  c_frame fs tabs fp l dd -> lay_at l o -> outarr_ok o -> (is_skip fp = true -> oa_cap o = 0) ->
  lay_wit W l -> lay_ptr l ->
  oa_base o = Vptr b ofs -> Ptrofs.unsigned ofs + oa_N o < Ptrofs.modulus ->
  c_frame (continuity fs (offset_val (oa_d o) (oa_base o)) (oa_cap o)) tabs fp
    (lmove l (oa_base o) (oa_d o) (oa_cap o)) dd.
Proof.
  intros Hc Hl Ho Hsk Hw Hp Eb HN. destruct Ho as (_ & _ & _ & Hd & Hcap & Hdc).
  unfold continuity, cont_moves, lmove.
  destruct (Z.ltb_spec 0 (oa_cap o)) as [Hc0 | Hc0];
    [| replace (oa_cap o <=? 0) with true by lia; exact Hc].
  replace (oa_cap o <=? 0) with false by lia. simpl andb.
  destruct Hc as (A1 & A2 & A3 & Lf & Ld & M).
  assert (Hm: match fp with FP_skip _ _ => False | _ => True end)
    by (destruct fp; auto; simpl in Hsk; lia).
  assert (Ev1: veqb nullval nullval = true) by apply veqb_refl.
  rewrite Eb in *.
  destruct l as [ | eb ec gp | bb pe od | bb ps pe e].
  - destruct Lf as ((G0 & P2 & P3 & P4) & P1). rewrite G0, veqb_refl, P1, (veqb_ptr_null (offset_val _ _)) by exact I.
    cbn [negb orb].
    split; [exact A1 |]. split; [exact A2 |]. split; [exact A3 |]. split; [| split].
    + try rewrite Ev1.
      unfold fsu_gpDictCopy, fsu_previousDstEnd, fsu_prefixStart, fsu_virtualStart, fsu_dictEnd. cbn.
      split; [auto |]. split; [exact I |]. split; [lia |].
      split; [auto |]. split; [auto |]. split; [| auto].
      vp_solve.
    + exact Ld.
    + destruct fp; try contradiction; exact M.
  - destruct Lf as ((Hpe & G0 & P2 & P3 & P4) & P1). destruct Hp as (b' & ofs' & -> & HN').
    destruct Hw as (Hle & [-> | (-> & -> & Hv)]).
    + rewrite G0, veqb_01. cbn [negb orb].
      split; [exact A1 |]. split; [exact A2 |]. split; [exact A3 |]. split; [| split].
      * rewrite P1. replace (veqb (offset_val (Zlength ec) (Vptr b' ofs')) nullval) with false by reflexivity.
        rewrite P2, (vptr_diff_base b' ofs') by (pose proof (Zlength_nonneg ec); lia).
        unfold fsu_gpDictCopy, fsu_previousDstEnd, fsu_prefixStart, fsu_virtualStart, fsu_dictEnd. cbn.
        split; [auto |]. split; [exact I |]. split; [lia |].
        split; [auto |]. split; [auto |]. split; [| split; [auto | lia]].
        vp_solve.
      * cbn. split; [auto |]. split; [auto |]. split; [auto |]. split; [auto |]. exists 1. exact Ld.
      * destruct fp; try contradiction; exact M.
    + rewrite G0, veqb_refl. cbn [negb orb]. rewrite Zlength_nil in *.
      destruct (veqb (offset_val (oa_d o) (Vptr b ofs)) (fs_previousDstEnd fs)) eqn:Eq; cbn [negb].
      * unfold veqb in Eq. destruct (Val.eq _ _) as [Eq' | _]; [| discriminate]. rewrite P1 in Eq'.
        split; [exact A1 |]. split; [exact A2 |]. split; [exact A3 |]. split; [| split].
        -- split; [auto |]. split; [exact I |]. split; [lia |].
           assert (Eb': offset_val (oa_d o) (Vptr b ofs) = Vptr b' ofs')
             by (rewrite Eq'; simpl; rewrite Ptrofs.add_zero; auto).
           cbn [ext_of_dict ext_len lay_fields]. rewrite P1, P2, P3, P4, Zlength_nil, !Z.sub_0_r, Eb'.
           rewrite !isptr_offset_val_zero by exact I. repeat split; auto; lia.
        -- cbn. split; [auto |]. split; [auto |]. split; [auto |]. split; [auto |]. exists 0. exact Ld.
        -- destruct fp; try contradiction; exact M.
      * split; [exact A1 |]. split; [exact A2 |]. split; [exact A3 |]. split; [| split].
        -- rewrite P1. replace (veqb (offset_val 0 (Vptr b' ofs')) nullval) with false by reflexivity.
           rewrite P2, (vptr_diff_base b' ofs') by lia.
           unfold fsu_gpDictCopy, fsu_previousDstEnd, fsu_prefixStart, fsu_virtualStart, fsu_dictEnd. cbn.
           split; [auto |]. split; [exact I |]. split; [lia |].
           split; [auto |]. split; [auto |]. split; [| split; [auto | lia]].
           vp_solve.
        -- cbn. split; [auto |]. split; [auto |]. split; [auto |]. split; [auto |]. exists 0. exact Ld.
        -- destruct fp; try contradiction; exact M.
  - simpl in Hl. lia.
  - simpl in Hl. destruct Hl as (-> & Hps & HpeN & Hpsd & He).
    destruct Lf as (Gp & Hpp & Hps' & P1 & P2 & P3 & P4). rewrite Eb in *. rewrite Gp, veqb_refl. cbn [negb orb].
    rewrite P1. rewrite (veqb_off b ofs (oa_N o)) by lia.
    destruct (Z.eqb_spec (oa_d o) pe) as [<- | Ne].
    { rewrite Z.eqb_refl. simpl. split; [exact A1 |]. split; [exact A2 |]. split; [exact A3 |].
      split; [| split; [exact Ld | exact M]]. split; [exact Gp |]. auto 7. }
    replace (pe =? oa_d o) with false by lia. cbn [negb].
    split; [exact A1 |]. split; [exact A2 |]. split; [exact A3 |]. split; [| split].
    + replace (veqb (offset_val pe (Vptr b ofs)) nullval) with false by reflexivity.
      rewrite P2, (vptr_diff_off b ofs (oa_N o)) by lia.
      unfold fsu_gpDictCopy, fsu_previousDstEnd, fsu_prefixStart, fsu_virtualStart, fsu_dictEnd. cbn.
      split; [auto |]. split; [exact I |]. split; [lia |].
      split; [auto |]. split; [auto |]. split; [| split; [auto | lia]].
      cbn [ext_len]; vp_solve.
    + exact I.
    + destruct fp; try contradiction; exact M.
Qed.

(* ---------- the checkContinuity call: witnesses ---------- *)

(* the DDict content of an HL_dict layout lent to the witnesses (its end is compared with NULL) *)
Definition lay_W (l: hlay) : list ptr_witness :=
  match l with HL_dict eb ec _ => [pw_bytes Ews (Zlength ec) ec eb] | _ => [] end.

Definition lay_rest (l: hlay) : mpred := match l with HL_dict _ _ _ => emp | _ => lay_res l end.

Lemma lay_res_split l : lay_res l = (pws_pred (lay_W l) * lay_rest l)%logic.
Proof.
  destruct l; unfold lay_W, lay_rest, pws_pred; simpl; rewrite ?sepcon_emp, ?emp_sepcon; auto.
Qed.

Lemma pws_app W1 W2 : pws_pred (W1 ++ W2) = (pws_pred W1 * pws_pred W2)%logic.
Proof.
  induction W1; simpl.
  - unfold pws_pred at 2. simpl. rewrite emp_sepcon. auto.
  - unfold pws_pred in *. simpl. rewrite IHW1. rewrite sepcon_assoc. auto.
Qed.

(* a fact S3Defs.dd_pre did not carry at first: the DDict content is bytes, and a copied
   DDict's content is not empty (both hold by DecRep.ddict_struct) *)
Definition dd_gap : Prop :=
  forall dd eb ec gp, dd_pre dd (eb, ec, gp) ->
    byte_cells ec /\ (gp = 1 -> 0 < Zlength ec) /\ (forall dm, dd_model dd dm -> bytes_ok (dm_content dm)).

(* dd_pre now carries ddict_struct's facts *)
Lemma dd_gap_holds : dd_gap.
Proof.
  intros dd eb ec gp (x & -> & -> & -> & Hb & Hc & _). split; [| split].
  - unfold byte_cells. apply Forall_map. eapply Forall_impl; [| exact Hb].
    intros a Ha. unfold is_byte in Ha. exists a. split; [lia | reflexivity].
  - intros E. destruct (ddx_copied x); [| discriminate]. rewrite Zlength_map. apply Hc; reflexivity.
  - intros dm Hm. cbn in Hm. unfold ddx_model in Hm. destruct (dx_raw x); [inv Hm; exact Hb |].
    unfold dict_auto_c in Hm.
    destruct (Zlength (dx_bytes x) <? 8); [inv Hm; exact Hb |].
    destruct (negb _); [inv Hm; exact Hb |].
    destruct (dx_ld x) as [[st es] |]; inv Hm. cbn. unfold bytes_ok in *. apply Forall_skipn. exact Hb.
Qed.

Lemma test_eq_vv (P Q: mpred) p q :
  isptr p -> isptr q -> (P |-- valid_pointer p) -> (Q |-- valid_pointer q) -> P * Q |-- denote_tc_test_eq p q.
Proof.
  intros Hp Hq HP HQ. destruct p; try contradiction. destruct q; try contradiction.
  Transparent denote_tc_test_eq. unfold denote_tc_test_eq, test_eq_ptrs. Opaque denote_tc_test_eq.
  destruct (sameblock _ _); apply andp_right.
  - apply sepcon_weak_valid_pointer1. eapply derives_trans; [exact HP | apply valid_pointer_weak].
  - apply sepcon_weak_valid_pointer2. eapply derives_trans; [exact HQ | apply valid_pointer_weak].
  - apply sepcon_valid_pointer1. exact HP.
  - apply sepcon_valid_pointer2. exact HQ.
Qed.

Lemma test_eq_null_wvp (P: mpred) p : isptr p -> (P |-- weak_valid_pointer p) -> P |-- denote_tc_test_eq p nullval.
Proof.
  intros Hp HP. destruct p; try contradiction.
  Transparent denote_tc_test_eq. unfold denote_tc_test_eq. Opaque denote_tc_test_eq. simpl.
  apply andp_right; [apply prop_right; reflexivity | exact HP].
Qed.

Lemma arr_vp sh N (c: list val) p d :
  sepalg.nonidentity sh -> 0 <= d < N ->
  data_at sh (tarray tuchar N) c p |-- valid_pointer (offset_val d p).
Proof.
  intros. eapply derives_trans; [apply data_at_memory_block |].
  apply memory_block_valid_pointer; auto; simpl; rep_lia.
Qed.

Lemma cont_pre_ok fs l dd o b ofs W :
  lay_fields fs l -> lay_dd l dd -> lay_at l o -> lay_wit W l -> dd_gap ->
  writable_share (oa_sh o) -> 0 <= oa_d o -> 0 <= oa_cap o -> oa_d o + oa_cap o <= oa_N o ->
  oa_base o = Vptr b ofs ->
  (fs_gpDictCopy fs = Vint (Int.repr 0) \/ fs_gpDictCopy fs = Vint (Int.repr 1)) /\
  (0 < oa_cap o -> fs_gpDictCopy fs = Vint (Int.repr 0) ->
     pws_pred (pw_bytes (oa_sh o) (oa_N o) (oa_c o) (oa_base o) :: lay_W l ++ W)
       |-- denote_tc_test_eq (offset_val (oa_d o) (oa_base o)) (fs_previousDstEnd fs)) /\
  (cont_moves fs (offset_val (oa_d o) (oa_base o)) (oa_cap o) = true ->
     isptr (offset_val (oa_d o) (oa_base o)) /\
     (pws_pred (pw_bytes (oa_sh o) (oa_N o) (oa_c o) (oa_base o) :: lay_W l ++ W)
        |-- denote_tc_test_eq (fs_previousDstEnd fs) nullval) /\
     (fs_previousDstEnd fs <> nullval -> sameblock (fs_previousDstEnd fs) (fs_prefixStart fs) = true)).
Proof.
  intros Lf Ld Hl Hw Hg Hsh Hd Hcap Hdc Eb. rewrite pws_cons_bytes, pws_app, Eb.
  assert (Hni: sepalg.nonidentity (oa_sh o)) by (apply readable_nonidentity, writable_readable; auto).
  assert (Hmv: cont_moves fs (offset_val (oa_d o) (Vptr b ofs)) (oa_cap o) = true -> 0 < oa_cap o)
    by (unfold cont_moves; destruct (Z.ltb_spec 0 (oa_cap o)); [lia | discriminate]).

  destruct l as [ | eb ec gp | bb pe od | bb ps pe e]; simpl in Hl.
  - destruct Lf as ((G0 & P2 & P3 & P4) & P1). rewrite P1. split; [left; exact G0 |]. split.
    + intros. unfold lay_W, pws_pred; simpl. rewrite emp_sepcon. apply arr_test_eq_pn; auto; lia.
    + intros _. split; [exact I |]. split; [apply test_eq_nn |]. intros []; reflexivity.
  - destruct Lf as ((Hpe & G0 & P2 & P3 & P4) & P1). rewrite P1, P2, G0.
    destruct Hw as (Hle & [-> | (-> & -> & Hv)]).
    + split; [right; reflexivity |]. split; [intros _ E; inv E |].
      intros Hm. split; [exact I |]. split; [| intros _; destruct eb; try contradiction; simpl; apply peq_true].
      destruct (Hg dd eb ec 1 Ld) as (_ & Hec & _). specialize (Hec eq_refl).
      unfold lay_W, pws_pred; simpl. rewrite sepcon_emp.
      apply test_eq_null_wvp; [destruct eb; try contradiction; exact I |].
      apply sepcon_weak_valid_pointer2, sepcon_weak_valid_pointer1.
      apply arr_wvp; [apply readable_nonidentity, writable_readable, writable_Ews | lia | lia].
    + split; [left; reflexivity |]. rewrite Zlength_nil. unfold lay_W, pws_pred; simpl. rewrite sepcon_emp.
      rewrite isptr_offset_val_zero by exact Hpe. split.
      * intros Hc0 _. rewrite <- sepcon_assoc. apply test_eq_vv; [exact I | exact Hpe | | ].
        -- apply sepcon_valid_pointer1. apply (arr_vp (oa_sh o) (oa_N o) (oa_c o) (Vptr b ofs) (oa_d o)); auto; lia.
        -- exact Hv.
      * intros Hm. split; [exact I |]. split; [| intros _; destruct eb; try contradiction; simpl; apply peq_true].
        apply test_eq_null_wvp; [exact Hpe |].
        apply sepcon_weak_valid_pointer2, sepcon_weak_valid_pointer2.
        eapply derives_trans; [exact Hv | apply valid_pointer_weak].
  - destruct Hl as (_ & _ & Hc0).
    split; [destruct od as [[[eb ec] gp] |]; [destruct Lf as (_ & _ & _ & (_ & G & _)) | destruct Lf as (_ & _ & _ & (G & _))];
            [destruct Hw as (_ & [-> | (-> & _)]); rewrite G; auto | left; exact G] |].
    split; [lia | intros Hm; specialize (Hmv Hm); lia].
  - destruct Hl as (-> & Hps & HpeN & Hpsd & He). rewrite Eb in Lf. destruct Lf as (G0 & _ & Hpp & P1 & P2 & _).
    rewrite P1, P2. split; [left; exact G0 |]. split.
    + intros. unfold lay_W, pws_pred; simpl. rewrite emp_sepcon. apply arr_test_eq_pp; auto; lia.
    + intros Hm. specialize (Hmv Hm). split; [exact I |]. split.
      * unfold lay_W, pws_pred; simpl. rewrite emp_sepcon. apply arr_test_eq_pn; auto; lia.
      * intros _. simpl. destruct (peq b b); [reflexivity | congruence].
Qed.

Lemma int_repr_small_inj a b : 0 <= a <= 7 -> 0 <= b <= 7 -> Vint (Int.repr a) = Vint (Int.repr b) -> a = b.
Proof.
  intros Ha Hb E. assert (Int.repr a = Int.repr b) by congruence.
  apply (f_equal Int.unsigned) in H. rewrite !Int.unsigned_repr in H by rep_lia. auto.
Qed.

Lemma stage_inv fs tabs fp l dd st :
  c_frame fs tabs fp l dd -> fp_complete fp = false -> fs_stage fs = Vint (Int.repr st) -> 0 <= st <= 7 ->
  match fp with
  | FP_skip _ _ => st = ds_skipFrame
  | FP_zstd _ z =>
      match zp_ph z with
      | ZP_bhdr => st = ds_decodeBlockHeader
      | ZP_body bh => st = if bp_last (block_props_of bh) =? 1 then ds_decompressLastBlock else ds_decompressBlock
      | ZP_ck => st = ds_checkChecksum
      | ZP_end => False
      end
  | _ => False
  end.
Proof.
  intros Hc Hnc Hs Hst. destruct Hc as (_ & _ & _ & _ & _ & M).
  destruct fp as [ | | hdr got | hdr z]; try contradiction.
  - destruct M as (_ & _ & _ & _ & _ & Hm). simpl in Hnc. rewrite Hnc in Hm. destruct Hm as [Hs' _].
    rewrite Hs in Hs'. apply int_repr_small_inj in Hs'; unfold ds_skipFrame in *; lia.
  - destruct M as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hph & _). unfold phase_fields in Hph.
    simpl in Hnc. destruct (zp_ph z); try discriminate.
    + destruct Hph as [Hs' _]. rewrite Hs in Hs'. apply int_repr_small_inj in Hs'; unfold ds_decodeBlockHeader in *; lia.
    + destruct Hph as (c & _ & Hs' & _). rewrite Hs in Hs'.
      unfold ds_decompressLastBlock, ds_decompressBlock in *.
      destruct (_ =? 1); apply int_repr_small_inj in Hs'; lia.
    + destruct Hph as [Hs' _]. rewrite Hs in Hs'. apply int_repr_small_inj in Hs'; unfold ds_checkChecksum in *; lia.
Qed.

(* the skippable frame after its content: expected 0, stage 0 *)
Lemma cf_skip_done fs tabs hdr l dd pcs :
  c_frame fs tabs (FP_skip hdr 0) l dd ->
  c_frame (fsu_stage (fsu_expected (fsu_processedCSize fs (Vlong (Int64.repr pcs))) (Vlong (Int64.repr 0)))
             (Vint (Int.repr 0))) tabs (FP_skip hdr (le_field hdr 4 4)) l dd.
Proof.
  intros (A1 & A2 & A3 & Lf & Ld & M). destruct M as (Hl & Ht & Hh & Hg & Hle & _).
  split; [exact A1 |]. split; [exact A2 |]. split; [exists pcs; reflexivity |].
  split; [exact Lf |]. split; [exact Ld |].
  split; [exact Hl |]. split; [exact Ht |]. split; [exact Hh |]. split; [lia |]. split; [exact Hle |].
  rewrite Z.eqb_refl. split; [left |]; reflexivity.
Qed.

(* ---------- an array around a window of bytes ---------- *)

Lemma fa0_sub N p k :
  field_compatible (tarray tuchar N) [] p -> 0 <= k <= N ->
  field_address0 (Tarray tuchar N noattr) (SUB k) p = offset_val k p.
Proof.
  intros. rewrite field_address0_offset by auto with field_compatible. simpl. f_equal. lia.
Qed.

Definition arr_rest (sh: share) (N: Z) (c: list val) (base: val) (off k: Z) : mpred :=
  (data_at sh (Tarray tuchar off noattr) (sublist 0 off c) base *
   data_at sh (Tarray tuchar (N - (off + k)) noattr) (sublist (off + k) N c) (offset_val (off + k) base))%logic.

Lemma arr_split sh N c base off (s: list Z) :
  field_compatible (tarray tuchar N) [] base -> Zlength c = N -> 0 <= off -> off + Zlength s <= N ->
  sublist off (off + Zlength s) c = zbytes s ->
  data_at sh (tarray tuchar N) c base =
  (arr_rest sh N c base off (Zlength s) *
   data_at sh (tarray tuchar (Zlength s)) (zbytes s) (offset_val off base))%logic.
Proof.
  intros Fc HN Ho Hs Hw. unfold arr_rest. pose proof (Zlength_nonneg s).
  unfold tarray. rewrite (split3_data_at_Tarray_tuchar sh N off (off + Zlength s) c base) by lia.
  rewrite !fa0_sub by (auto; lia). replace (off + Zlength s - off) with (Zlength s) by lia.
  rewrite Hw. apply pred_ext; cancel.
Qed.

(* ---------- the frame fields of a Zstandard frame after a unit ---------- *)

(* what a unit keeps of a Zstandard frame's progress *)
Definition zp_keep (z' z: zprog) : Prop :=
  zp_h z' = zp_h z /\ zp_dm z' = zp_dm z /\ zp_bsm z' = zp_bsm z /\ zp_ign z' = zp_ign z.

Lemma zstep_keep z u cnt ts : zp_keep (zstep z u cnt ts) z.
Proof.
  unfold zstep, zp_keep.
  destruct (zp_ph z) as [ | bh | | ]; [destruct (cblock_size u) as [c |]; [destruct (c =? 0) |] | | |];
    try (destruct (bp_type _ =? 0); [destruct (match cblock_size bh with Some c => _ | None => false end) |]);
    cbn; auto.
Qed.

Definition fcheck (z: zprog) : bool := andb (fh_checksumFlag (zp_h z) =? 1) (negb (zp_ign z)).

Lemma cf_zstd_mk fs fs' tabs hdr z z' l l' dd (ts': tstate) :
  c_frame fs tabs (FP_zstd hdr z) l dd -> zp_keep z' z -> lay_fields fs' l' -> lay_dd l' dd ->
  fs_isFrameDecompression fs' = fs_isFrameDecompression fs ->
  (fs_ddictIsCold fs' = Vint (Int.repr 0) \/ fs_ddictIsCold fs' = Vint (Int.repr 1)) ->
  (exists pcs, fs_processedCSize fs' = Vlong (Int64.repr pcs)) ->
  fs_fParams fs' = fs_fParams fs -> fs_validateChecksum fs' = fs_validateChecksum fs ->
  phase_fields fs' z' -> fs_decodedSize fs' = Vlong (Int64.repr (Zlength (zp_out z'))) ->
  (fcheck z = true -> fs_xxh fs' = Some (zp_out z')) ->
  bytes_ok (zp_out z') ->
  match zp_ph z' with
  | ZP_bhdr => Zlength (zp_got z') < ZSTD_blockHeaderSize
  | ZP_body bh =>
      Zlength bh = ZSTD_blockHeaderSize /\ bytes_ok bh /\
      exists c, cblock_size bh = Some c /\ 0 < c <= zp_bsm z /\ Zlength (zp_got z') < c /\
                bp_type (block_props_of bh) <> 3
  | ZP_ck => Zlength (zp_got z') < 4 /\ fh_checksumFlag (zp_h z) = 1
  | ZP_end => True
  end ->
  bytes_ok (zp_got z') -> ts_d ts' = zp_ts z' ->
  c_frame fs' (TInit (dd_ox dd) ts') (FP_zstd hdr z') l' dd.
Proof.
  intros Hc (Eh & Edm & Eb & Ei) Lf Ld E1 E2 E4 E5 E6 Ph Ed Ex Bo Mz Bg Et.
  destruct Hc as (A1 & _ & A3 & _ & _ & M).
  destruct M as (T0 & Fp & B1 & B2 & W1 & W2 & Fc & Ck & Dm & _ & _ & _ & Vc & _).
  unfold fcheck in Ex.
  rewrite <- Eh, <- Eb, <- Ei, <- Edm in *.
  split; [congruence |]. split; [exact E2 |]. split; [exact E4 |]. split; [exact Lf |]. split; [exact Ld |].
  split; [exact T0 |]. split; [congruence |]. split; [exact B1 |]. split; [exact B2 |]. split; [exact W1 |].
  split; [exact W2 |]. split; [exact Fc |]. split; [exact Ck |]. split; [exact Dm |].
  split; [exists ts'; split; [reflexivity | exact Et] |].
  split; [exact Ph |].
  split; [exact Ed |]. split; [congruence |]. split; [exact Ex |]. split; [exact Bo |].
  split; [exact Mz | exact Bg].
Qed.

Lemma arr_join sh N c base off (s: list Z) :
  field_compatible (tarray tuchar N) [] base -> Zlength c = N -> 0 <= off -> off + Zlength s <= N ->
  sublist off (off + Zlength s) c = zbytes s ->
  arr_rest sh N c base off (Zlength s) *
  data_at sh (tarray tuchar (Zlength s)) (zbytes s) (offset_val off base) |-- data_at sh (tarray tuchar N) c base.
Proof. intros. rewrite (arr_split sh N c base off s) by auto. apply derives_refl. Qed.

Lemma cont_res_ck fs1 hdr z l dd o u pcs (ts: tstate) :
  c_frame fs1 (TInit (dd_ox dd) ts) (FP_zstd hdr z) (lmove l (oa_base o) (oa_d o) (oa_cap o)) dd ->
  zp_ph z = ZP_ck -> bytes_ok u -> oa_N o = Zlength (oa_c o) -> 0 <= oa_d o <= oa_N o ->
  (zp_ign z = true \/ le_field u 0 4 = xxh64 (zp_out z) 0 mod 2 ^ 32) ->
  cont_res (FP_zstd hdr z) l dd o u 0 (oa_c o)
    (fsu_stage (fsu_expected (fsu_processedCSize fs1 (Vlong (Int64.repr pcs))) (Vlong (Int64.repr 0)))
       (Vint (Int.repr 0))) (Some ts).
Proof.
  intros Hc Ez Bu HN Hd Hck.
  destruct (c_frame_ts _ _ _ _ _ _ _ Hc) as [_ Ets].
  split; [rep_lia |]. split; [auto |]. split; [intros j _ _; auto |]. split; [intros X; exact X |].
  replace (is_error_code 0) with false by reflexivity.
  exists nil, ts. rewrite Ets. unfold cnt_safe, cnt_ok, cont_checks, zstep, lnext. rewrite Ez.
  split; [auto |]. split; [auto |]. split; [auto |]. split; [reflexivity |]. split; [auto |].
  split; [rewrite sublist_nil'; auto; lia |]. split; [intros j _ _; auto |].
  pose proof Hc as (_ & Hcold & _ & Lf & Ld & _).
  eapply cf_zstd_mk with (z' := zp_with z (zp_bl z) (zp_ts z) (zp_out z) ZP_end u); eauto; try reflexivity;
    try exact Ets.
  all: try (unfold zp_keep; cbn; auto; fail).
  all: try (eexists; reflexivity).
  all: destruct Hc as (_ & _ & _ & _ & _ & M);
       destruct M as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ed & _ & Ex & Bo & _).
  all: cbn; auto.
Qed.

Lemma zstd_globals_fold gv :

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
  data_at Ers (tarray tint 8) dec64table_val (gv _dec64table) *
  eb_res gv |-- zstd_globals gv.
Proof. unfold zstd_globals. cancel. Qed.

Lemma cblock_size_range (u: list Z) k : bytes_ok u -> cblock_size u = Some k -> 0 <= k < 2 ^ 21.
Proof.
  intros Hb Hc. unfold cblock_size in Hc.
  destruct (Zlength u <? ZSTD_blockHeaderSize); [discriminate |].
  destruct (bp_type (block_props_of u) =? 1); [inv Hc; lia |].
  destruct (bp_type (block_props_of u) =? 3); [discriminate |]. inv Hc.
  unfold block_props_of; simpl. pose proof (lef_range u 0 3 Hb ltac:(lia)).
  rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia |].
  apply Z.div_lt_upper_bound; [lia |]. change (2 ^ 3 * 2 ^ 21) with (2 ^ (8 * 3)). lia.
Qed.

Lemma is_error_small k : 0 <= k < 2 ^ 21 -> is_error_code k = false.
Proof. intros. unfold is_error_code. apply Z.ltb_ge. lia. Qed.

End CM_C3Base_2.

Ltac ff_unfold :=
  unfold frame_fields; cbn [fs_previousDstEnd fs_gpDictCopy fs_prefixStart fs_virtualStart fs_dictEnd fs_expected
      fs_fParams fs_processedCSize fs_decodedSize fs_bType fs_stage fs_xxh fs_headerSize fs_validateChecksum
      fs_rleSize fs_isFrameDecompression fs_dictID fs_ddictIsCold fsu_stage fsu_expected fsu_processedCSize
      fsu_bType fsu_rleSize fsu_decodedSize fsu_xxh fsu_previousDstEnd fsu_gpDictCopy].

Section CM_C3Base_3.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.

Lemma bp_last01 (u: list Z) : bp_last (block_props_of u) = 0 \/ bp_last (block_props_of u) = 1.
Proof.
  unfold block_props_of; simpl.
  assert (Z.land (le_field u 0 3) 1 = le_field u 0 3 mod 2) as -> by (apply (Z.land_ones _ 1); lia).
  pose proof (Z.mod_pos_bound (le_field u 0 3) 2). lia.
Qed.

Lemma cblock_type3 (u: list Z) c : cblock_size u = Some c -> bp_type (block_props_of u) <> 3.
Proof.
  unfold cblock_size. destruct (Zlength u <? ZSTD_blockHeaderSize); [discriminate |].
  destruct (bp_type (block_props_of u) =? 1) eqn:E1; [apply Z.eqb_eq in E1; lia |].
  destruct (bp_type (block_props_of u) =? 3) eqn:E3; [discriminate |]. apply Z.eqb_neq in E3. auto.
Qed.

Lemma cont_res_bhdr fs1 fs' hdr z l dd o u c (ts: tstate) :
  c_frame fs1 (TInit (dd_ox dd) ts) (FP_zstd hdr z) (lmove l (oa_base o) (oa_d o) (oa_cap o)) dd ->
  zp_ph z = ZP_bhdr -> bytes_ok u -> Zlength u = ZSTD_blockHeaderSize ->
  cblock_size u = Some c -> c <= zp_bsm z ->
  (c = 0 -> bp_last (block_props_of u) = 1 -> fcs_okm (zp_h z) (zp_out z)) ->
  lay_fields fs' (lmove l (oa_base o) (oa_d o) (oa_cap o)) ->
  fs_isFrameDecompression fs' = fs_isFrameDecompression fs1 -> fs_ddictIsCold fs' = fs_ddictIsCold fs1 ->
  (exists pcs, fs_processedCSize fs' = Vlong (Int64.repr pcs)) ->
  fs_fParams fs' = fs_fParams fs1 -> fs_validateChecksum fs' = fs_validateChecksum fs1 ->
  fs_decodedSize fs' = fs_decodedSize fs1 -> fs_xxh fs' = fs_xxh fs1 ->
  phase_fields fs' (zstep z u nil (zp_ts z)) ->
  oa_N o = Zlength (oa_c o) -> 0 <= oa_d o <= oa_N o ->
  cont_res (FP_zstd hdr z) l dd o u 0 (oa_c o) fs' (Some ts).
Proof.
  intros Hc Ez Bu Lu Ec Hcb Hf6 Lf E1 E2 E4 E5 E6 E7 E8 Ph HN Hd.
  destruct (c_frame_ts _ _ _ _ _ _ _ Hc) as [_ Ets].
  split; [rep_lia |]. split; [auto |]. split; [intros j _ _; auto |]. split; [intros X; exact X |].
  replace (is_error_code 0) with false by reflexivity.
  exists nil, ts. rewrite Ets. unfold cnt_safe, cnt_ok, cont_checks, lnext. rewrite Ez.
  split; [auto |]. split; [auto |]. split; [exists c; auto |]. split; [reflexivity |]. split; [auto |].
  split; [rewrite sublist_nil'; auto; lia |]. split; [intros j _ _; auto |].
  pose proof Hc as (_ & Hcold & _ & _ & Ld & M).
  destruct M as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ed & _ & Ex & Bo & _ & Bg).
  assert (Eo: zp_out (zstep z u [] (zp_ts z)) = zp_out z)
    by (unfold zstep; rewrite Ez, Ec; destruct (c =? 0); reflexivity).
  assert (Et: zp_ts (zstep z u [] (zp_ts z)) = zp_ts z)
    by (unfold zstep; rewrite Ez, Ec; destruct (c =? 0); reflexivity).
  pose proof (zstep_keep z u [] (zp_ts z)) as Hk.
  eapply cf_zstd_mk; eauto; try congruence.
  all: try (rewrite E2; exact Hcold).
  all: try (rewrite Eo, E7; exact Ed).
  all: try (intros Hf; rewrite Eo, E8; auto; fail).
  all: try (rewrite Eo; auto; fail).
  all: try (unfold zstep; rewrite Ez, Ec; destruct (c =? 0); cbn; constructor; fail).
  all: unfold zstep; rewrite Ez, Ec; destruct (Z.eqb_spec c 0) as [-> | Hc0]; cbn [zp_with zp_ph zp_got zp_h].
  all: try (unfold next_phase; destruct (bp_last _ =? 1);
       [destruct (fh_checksumFlag _ =? 1) eqn:Ef; cbn; try rewrite Zlength_nil; [split; [lia | apply Z.eqb_eq; auto] | auto] |
        cbn; try rewrite Zlength_nil; unfold ZSTD_blockHeaderSize; lia]; fail).
  all: pose proof (cblock_size_range _ _ Bu Ec); split; [auto |]; split; [auto |].
  all: exists c; split; [auto |]; split; [lia |]; split; [rewrite Zlength_nil; lia |]; eapply cblock_type3; eauto.
Qed.

(* ---------- the layout after a block ---------- *)

Lemma lmove_at l o :
  lay_at l o ->
  match lmove l (oa_base o) (oa_d o) (oa_cap o) with
  | HL_seg b ps _ _ => b = oa_base o /\ ps <= oa_d o
  | _ => True
  end.
Proof.
  intros Hl. unfold lmove. destruct (oa_cap o <=? 0).
  - destruct l; simpl in *; auto; tauto.
  - destruct l as [ | eb ec gp | bb pe od | bb ps pe e]; simpl in *; try (split; [auto | lia]); auto.
    destruct (pe =? oa_d o); simpl; try tauto; split; auto; lia.
Qed.

Lemma lmove_seg l dd W o :
  lay_at l o -> lay_dd l dd -> lay_wit W l -> outarr_ok o -> 0 < oa_cap o ->
  exists ps e, lmove l (oa_base o) (oa_d o) (oa_cap o) = HL_seg (oa_base o) ps (oa_d o) e /\
    layout_ok_seg ps e (oa_N o) /\ ps <= oa_d o.
Proof.
  intros Hl Ld Hw (_ & _ & HN & Hd & Hc & Hdc) Hc0. unfold lmove.
  replace (oa_cap o <=? 0) with false by (symmetry; apply Z.leb_gt; lia).
  destruct l as [ | eb ec gp | b pe od | b ps pe e]; cbn in Hl.
  - exists (oa_d o), ExtNone. split; [auto |]. split; [| lia]. unfold layout_ok_seg; cbn. repeat split; lia.
  - exists (oa_d o), (ext_of_dict eb ec). split; [auto |]. split; [| lia].
    destruct Hw as (Hle & _). pose proof (Zlength_nonneg ec).
    unfold layout_ok_seg, ext_of_dict; cbn. repeat split; try lia. apply writable_readable, writable_Ews.
  - lia.
  - destruct Hl as (-> & Hps & HpN & Hpd & He).
    destruct (Z.eqb_spec pe (oa_d o)) as [-> | Hne].
    + exists ps, e. split; [auto |]. split; [| lia].
      destruct e as [ | e1 elen | sh eb en ec e1 elen]; unfold layout_ok_seg; cbn in *; try (repeat split; lia).
      destruct Ld as (-> & -> & -> & -> & _). destruct Hw as (Hle & _). pose proof (Zlength_nonneg ec).
      repeat split; try lia. apply writable_readable, writable_Ews.
    + exists (oa_d o), (ExtIn pe (pe - ps)). split; [auto |]. split; [| lia]. unfold layout_ok_seg; cbn. repeat split; lia.
Qed.

(* a fact S3Defs.lay_fields did not state at first: after a block written at capacity 0 without a
   segment, zstd has set gpDictCopy = 0 (ZSTD_decompressContinue's genproof line), so lay_fields of the
   stuck layout must ask for gpDictCopy 0, not the DDict's *)
Definition stuck_gap : Prop :=
  forall fs base pe eb ec gp, isptr base -> 0 <= pe -> fs_previousDstEnd fs = offset_val pe base ->
    pre_fields fs (Some (eb, ec, 0)) -> lay_fields fs (HL_stuck base pe (Some (eb, ec, gp))).

(* lay_fields of a stuck layout now asks for gpDictCopy 0 *)
Lemma stuck_gap_holds : stuck_gap.
Proof.
  intros fs base pe eb ec gp Hb Hpe Hd Hpre. cbn [lay_fields]. split; [exact Hb |]. split; [exact Hpe |]. split; [exact Hd | exact Hpre].
Qed.

Lemma lay_lwrite fs1 fs' l1 o r :
  stuck_gap -> lay_fields fs1 l1 ->
  match l1 with HL_seg b ps _ _ => b = oa_base o /\ ps <= oa_d o | _ => True end ->
  isptr (oa_base o) -> 0 <= oa_d o -> 0 <= r ->
  fs_previousDstEnd fs' = offset_val (oa_d o + r) (oa_base o) -> fs_gpDictCopy fs' = Vint (Int.repr 0) ->
  fs_prefixStart fs' = fs_prefixStart fs1 -> fs_virtualStart fs' = fs_virtualStart fs1 ->
  fs_dictEnd fs' = fs_dictEnd fs1 ->
  lay_fields fs' (lwrite l1 (oa_base o) (oa_d o) r).
Proof.
  intros Hg Lf Hb Hp Hd Hr E1 E2 E3 E4 E5.
  destruct l1 as [ | eb ec gp | bb pe od | bb ps pe e]; simpl in *.
  - destruct Lf as ((_ & P2 & P3 & P4) & _). rewrite E3, E4, E5. repeat split; auto; lia.
  - destruct Lf as ((Hpe & _ & P2 & P3 & P4) & _). rewrite E3, E4, E5. repeat split; auto; lia.
  - destruct Lf as (_ & _ & _ & Pf). split; [auto |]. split; [lia |]. split; [auto |].
    destruct od as [[[eb ec] gp] |].
    + destruct Pf as (Hpe & _ & P2 & P3 & P4). unfold pre_fields. rewrite E3, E4, E5. repeat split; auto.
    + destruct Pf as (_ & P2 & P3 & P4). unfold pre_fields. rewrite E3, E4, E5. repeat split; auto.
  - destruct Hb as [-> Hps]. destruct Lf as (_ & Hpp & Hps0 & _ & P3 & P4 & P5). rewrite E3, E4, E5.
    split; [exact E2 |]. split; [auto |]. split; [lia |]. split; [exact E1 |]. split; [exact P3 |].
    split; [exact P4 | exact P5].
Qed.

Lemma lay_dd_lwrite l1 dd base d r : lay_dd l1 dd -> lay_dd (lwrite l1 base d r) dd.
Proof. destruct l1; cbn; auto. Qed.

Lemma zstep_body_facts z bh u cnt ts' :
  zp_ph z = ZP_body bh -> cnt_safe z u cnt ts' ->
  zp_h (zstep z u cnt ts') = zp_h z /\ zp_out (zstep z u cnt ts') = zp_out z ++ cnt /\
  zp_ts (zstep z u cnt ts') = ts'.
Proof.
  intros Ez Hc. unfold cnt_safe in Hc. unfold zstep. rewrite Ez in *.
  destruct (bp_type (block_props_of bh) =? 0).
  - destruct Hc as [-> ->]. destruct (match cblock_size bh with Some c => _ | None => false end); auto.
  - destruct (bp_type (block_props_of bh) =? 1); auto.
Qed.

(* R6: bytes in, bytes out (the calloc'd ring holds only bytes) *)
Definition win_bytes (oc oc': list val) : Prop := byte_cells oc -> byte_cells oc'.

Lemma cont_res_blk fs1 fs' hdr z bh l dd o u r oc' cnt (ts': tstate) c (tabs1: tabs3) :
  c_frame fs1 tabs1 (FP_zstd hdr z) (lmove l (oa_base o) (oa_d o) (oa_cap o)) dd ->
  zp_ph z = ZP_body bh -> cblock_size bh = Some c -> unit_ok (FP_zstd hdr z) (Zlength u) -> bytes_ok u ->
  0 <= r <= Int64.max_unsigned -> Zlength oc' = oa_N o ->
  unchanged_outside (oa_c o) oc' (oa_d o) (oa_d o + oa_cap o) -> is_error_code r = false ->
  Zlength cnt = r -> sublist (oa_d o) (oa_d o + r) oc' = zbytes cnt -> cnt_safe z u cnt ts' ->
  (hist_pre (FP_zstd hdr z) l o -> cnt_ok z (lay_H z l o) u cnt ts') ->
  unchanged_outside (oa_c o) oc' (oa_d o)
    (oa_d o + Z.min (oa_cap o) (zp_bsm z + WILDCOPY_OVERLENGTH)) ->
  win_bytes (oa_c o) oc' ->
  cont_checks z u cnt ->
  bytes_ok cnt ->
  lay_fields fs' (lnext (FP_zstd hdr z) l o r) ->
  lay_dd (lnext (FP_zstd hdr z) l o r) dd ->
  fs_isFrameDecompression fs' = fs_isFrameDecompression fs1 ->
  (fs_ddictIsCold fs' = Vint (Int.repr 0) \/ fs_ddictIsCold fs' = Vint (Int.repr 1)) ->
  (exists pcs, fs_processedCSize fs' = Vlong (Int64.repr pcs)) ->
  fs_fParams fs' = fs_fParams fs1 -> fs_validateChecksum fs' = fs_validateChecksum fs1 ->
  fs_decodedSize fs' = Vlong (Int64.repr (Zlength (zp_out z ++ cnt))) ->
  (fcheck z = true -> fs_xxh fs' = Some (zp_out z ++ cnt)) ->
  phase_fields fs' (zstep z u cnt ts') ->
  cont_res (FP_zstd hdr z) l dd o u r oc' fs' (Some ts').
Proof.
  intros Hc Ez Ec Hu Bu Hr HN Hun Er Lc Hs Hcnt Hok Hun2 Hby Hck Bc Lf Ld E1 E2 E4 E5 E6 Ed Ex Ph.
  split; [auto |]. split; [auto |]. split; [auto |]. split; [exact Hby |]. rewrite Er.
  exists cnt, ts'. split; [auto |]. split; [auto |]. split; [auto |]. split; [lia |]. split; [auto |].
  split; [exact Hs |]. split; [exact Hun2 |].
  destruct (zstep_body_facts z bh u cnt ts' Ez Hcnt) as (Eh & Eo & Et).
  pose proof (zstep_keep z u cnt ts') as Hk.
  pose proof Hc as (_ & _ & _ & _ & _ & M).
  destruct M as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Bo & Mz & Bg).
  rewrite Ez in Mz. destruct Mz as (Lbh & Bbh & c' & Ec' & Hc' & Hgc & Ht3). rewrite Ec in Ec'. inv Ec'.
  eapply cf_zstd_mk; eauto; try congruence.
  all: try (rewrite Eo; unfold bytes_ok in *; apply Forall_app; auto; fail).
  all: try (rewrite Eo; auto; fail).
  all: try (intros Hf; rewrite Eo; auto; fail).
  all: unfold zstep; rewrite Ez, Ec; unfold cnt_safe in Hcnt; rewrite Ez in Hcnt.
  all: cbn [unit_ok] in Hu; rewrite Ez, Ec in Hu.
  all: destruct (bp_type (block_props_of bh) =? 0) eqn:E0.
  all: try (rewrite Zlength_app; destruct (Zlength (zp_got z) + Zlength u =? c') eqn:Ef).
  all: cbn [zp_with zp_ph zp_got zp_h].
  all: try (unfold bytes_ok in *; constructor; fail).
  all: try (unfold bytes_ok in *; apply Forall_app; auto; fail).
  all: try (apply Z.eqb_neq in Ef; destruct Hu as (c2 & E2' & Hu2); inv E2';
            split; [auto |]; split; [auto |]; exists c2; split; [auto |]; split; [lia |];
            split; [rewrite Zlength_app; lia | auto]; fail).
  all: unfold next_phase; destruct (bp_last (block_props_of bh) =? 1);
         [destruct (fh_checksumFlag (zp_h z) =? 1) eqn:Eck |]; cbn [zp_h].
  all: try exact I.
  all: try (rewrite Zlength_nil; unfold ZSTD_blockHeaderSize; lia).
  all: split; [rewrite Zlength_nil; lia | apply Z.eqb_eq; auto].
Qed.

End CM_C3Base_3.
