(* FS3-bl BODY, stage 5 (ZSTDds_checkChecksum): the pure facts of the case: the frame fields at the
   switch (bl_fs1), the state after the case (bl5_ba, bl5_fs), the claim on an error and on success. *)
Require Export Zstd.proof.dec.v3.FS.BL.body.BLCase.
Local Open Scope Z_scope.

(* the DEBUGLOG loops (a copy of BLHelp.dw0: BLHelp depends on this case) *)
Ltac bl5_head_dw0 c :=
  lazymatch c with Sloop _ Sbreak => idtac | Ssequence ?a _ => bl5_head_dw0 a end.
Ltac bl5_dw0 :=
  match goal with |- semax _ ?P ?c _ => bl5_head_dw0 c;
    first [ forward_loop P break: P; [entailer! | forward; entailer! | ]
          | forward_loop P break: P;
            [entailer! | forward_if P; [exfalso; lia | forward; entailer! | forward; entailer!] | ] ] end.

Section CM_BL5Facts_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma bl5_lev_range (l: list Z) : bytes_ok l -> 0 <= le_value l < 2 ^ (8 * Zlength l).
Proof.
  intros H. induction H; cbn [le_value].
  - rewrite Zlength_nil. simpl. lia.
  - unfold is_byte in H. rewrite Zlength_cons. replace (8 * Z.succ (Zlength l)) with (8 + 8 * Zlength l) by lia.
    rewrite Z.pow_add_r by (pose proof (Zlength_nonneg l); lia).
    change (2^8) with 256. lia.
Qed.

Lemma bl5_lef_range (l: list Z) i k : bytes_ok l -> 0 <= k -> 0 <= le_field l i k < 2 ^ (8 * k).
Proof.
  intros H Hk. unfold le_field, slice.
  assert (Hb: bytes_ok (firstn (Z.to_nat k) (skipn (Z.to_nat i) l))).
  { unfold bytes_ok in *. apply Forall_firstn, Forall_skipn; auto. }
  pose proof (bl5_lev_range _ Hb).
  assert (Zlength (firstn (Z.to_nat k) (skipn (Z.to_nat i) l)) <= k).
  { rewrite Zlength_correct, firstn_length. lia. }
  assert (2 ^ (8 * Zlength (firstn (Z.to_nat k) (skipn (Z.to_nat i) l))) <= 2 ^ (8 * k)).
  { apply Z.pow_le_mono_r; [lia |]. pose proof (Zlength_nonneg (firstn (Z.to_nat k) (skipn (Z.to_nat i) l))). lia. }
  lia.
Qed.

Lemma bl5_ck_iff a D : 0 <= a < 2 ^ 32 -> (Int.repr a = Int.repr (Int64.Z_mod_modulus D) <-> a = D mod 2 ^ 32).
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

(* a copy of XxhLemmas.xxh64_digest_model_eq_all (its .vo is not on this chain) *)
Lemma bl5_digest_eq: forall seed l, xxh64_digest_model seed l = xxh64 l seed.
Proof.
  intros seed l.
  unfold xxh64_digest_model, xxh64, xxh_lanes, xxh_rest. fold (xxh_init seed). rewrite Zlength_correct.
  destruct (xxh_stripes (length l) (xxh_init seed) l) as [[[[v1 v2] v3] v4] r]. cbv zeta.
  unfold xxh_lane1, xxh_lane2, xxh_lane3, xxh_lane4; simpl fst; simpl snd. cbv beta iota.
  assert (Hm: forall x y, m64 (x + m64 y) = m64 (x + y)) by (intros; unfold m64; apply Zplus_mod_idemp_r).
  rewrite Hm. reflexivity.
Qed.

(* the fields of the frame at the switch that the case reads or keeps *)
Lemma bl5_fs1 fs ob osz opos pcs n :
  let f := bl_fs1 fs ob osz opos pcs n in
  fs_validateChecksum f = fs_validateChecksum fs /\ fs_xxh f = fs_xxh fs /\ fs_decodedSize f = fs_decodedSize fs /\
  fs_processedCSize f = vlong (pcs + n) /\ fs_isFrameDecompression f = fs_isFrameDecompression fs /\
  fs_dictID f = fs_dictID fs /\ fs_ddictIsCold f = fs_ddictIsCold fs /\ fs_fParams f = fs_fParams fs.
Proof.
  unfold bl_fs1, continuity. destruct (cont_moves _ _ _); cbn; repeat split.
Qed.

(* the state after the case *)
Definition bl5_ba (ba: blabs) (ob: val) (opos: Z) : blabs :=
  {| ba_dict := ba_dict ba; ba_st := option_map (fun b => bl_set b BHdrPrefix 0) (ba_st ba); ba_expect := 0;
     ba_out := Some (pair (pair ob (bl_start ba opos)) (opos + 0)%Z) |}.

Definition bl5_fs (f: fstate) : fstate := fsu_stage (fsu_expected f (vlong 0)) (Vint (Int.repr 0)).

Lemma bl5_err_claim md ba ba' c r opos osz oc' fs ts v l :
  bl_mrel md ba fs ts v -> bv_stage v = BCk -> bl_val (md_ignore md) (bv_h v) = true -> fs_xxh fs = Some l ->
  le_field c 0 4 <> xxh64 l 0 mod 2 ^ 32 -> is_error_code r = true -> bl_claim_nc md ba ba' c r opos osz oc'.
Proof.
  intros Hmr Hst Hv Hx Hne Hr. unfold bl_claim_nc.
  destruct (ba_st ba) as [b |] eqn:B; auto. destruct (dictref_model _); auto. intros _.
  destruct (Hmr b B) as (Hs & _ & _ & _ & _ & Hm). rewrite Hst in Hm. destruct Hm as [Hh Hxx].
  rewrite Hxx in Hx by exact Hv. injection Hx as Hx. subst l.
  unfold bl_step_nc. rewrite Hs, Hst. unfold bl_step. rewrite Hs, Hst.
  replace ((fh_checksumFlag (bs_hdr b) =? 1) && negb (md_ignore md))%bool with true by (rewrite Hh; symmetry; exact Hv).
  cbn [andb]. destruct (le_field c 0 4 =? _) eqn:E; [apply Z.eqb_eq in E; contradiction |].
  exact Hr.
Qed.

Lemma bl5_lay_congr od o ba1 ba2 f1 f2 :
  ba_out ba1 = ba_out ba2 -> fs_previousDstEnd f1 = fs_previousDstEnd f2 -> fs_prefixStart f1 = fs_prefixStart f2 ->
  fs_virtualStart f1 = fs_virtualStart f2 -> fs_dictEnd f1 = fs_dictEnd f2 -> fs_gpDictCopy f1 = fs_gpDictCopy f2 ->
  bl_lay od o ba1 f1 -> bl_lay od o ba2 f2.
Proof. intros E1 E2 E3 E4 E5 E6. unfold bl_lay. rewrite <- E1, <- E2, <- E3, <- E4, <- E5, <- E6. auto. Qed.

(* the success: the new state, its relation, the claim *)
Lemma bl5_ok W pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v pcs :
  let md := dmode_of pr in
  let fs' := bl5_fs (bl_fs1 fs ob osz opos pcs (Zlength c)) in
  bl_pre_ok W od osz0 ba shk shd ob osz opos oc shs src c ->
  bl_cinv md od osz0 ba fs hb v -> bl_mrel md ba fs ts v -> bd_model_ok (ba_dict ba) od -> bv_stage v = BCk ->
  fs_processedCSize fs = vlong pcs ->
  bl_lay od osz (bl_moved ba ob opos) (continuity fs (offset_val opos ob) (osz - opos)) ->
  (bl_val (md_ignore md) (bv_h v) = true -> exists l, fs_xxh fs = Some l /\ le_field c 0 4 = xxh64 l 0 mod 2 ^ 32) ->
  bl_hist_ok (bl5_ba ba ob opos) ob (opos + 0) oc /\
  (forall b', ba_st (bl5_ba ba ob opos) = Some b' -> ba_expect (bl5_ba ba ob opos) = bs_expect b') /\
  BRc md od osz (bl5_ba ba ob opos) fs' ts hb /\
  bl_claim_nc md ba (bl5_ba ba ob opos) c 0 opos osz oc.
Proof.
  intros md fs' Hpre Hci Hmr Hmd Hst Hpcs Hlay Hck.
  destruct (bl5_fs1 fs ob osz opos pcs (Zlength c)) as (Fv & Fx & Fd & Fp & Fi & Fdi & Fc & Ff).
  destruct Hci as (Hexp & Hexr & Hstg & Hifd & Hcold & Hdid & _ & (ds & Hds & Hdsr) & Hhb & Hwf & Hcs & Hly).
  destruct Hpre as (_ & Hh & _ & _ & _ & _ & _ & _ & _ & Hop & _).
  split; [| split; [| split]].
  - unfold bl_hist_ok in *. unfold bl5_ba. cbn [ba_out ba_st]. rewrite Z.add_0_r.
    unfold bl_start. destruct (ba_out ba) as [[[ob' f] pe] |].
    + destruct Hh as (-> & -> & Hf & Hm). split; [auto | split; [auto | split; [lia |]]].
      destruct (ba_st ba); cbn; auto.
    + split; [auto | split; [auto | split; [lia |]]].
      rewrite sublist_nil. destruct (ba_st ba) as [b |]; cbn.
      * rewrite Hh. reflexivity.
      * exists nil. split; [reflexivity | constructor].
  - intros b' Hb'. unfold bl5_ba in Hb' |- *. cbn [ba_st ba_expect] in *.
    destruct (ba_st ba); cbn in Hb'; inversion Hb'; reflexivity.
  - exists {| bv_stage := BHdrPrefix; bv_hdr := bv_hdr v; bv_hs := bv_hs v; bv_h := bv_h v; bv_bt := bv_bt v;
              bv_rle := bv_rle v |}.
    split; [| split].
    + unfold bl_cinv, fs', bl5_fs, bl5_ba. cbn [fs_expected fs_stage fs_isFrameDecompression fs_ddictIsCold
        fs_dictID fs_processedCSize fs_decodedSize fsu_stage fsu_expected ba_expect bv_stage bl_stz].
      rewrite Fi, Fdi, Fp, Fd.
      split; [reflexivity | split; [lia | split; [reflexivity | split; [auto | split]]]].
      { unfold cold01 in *. cbn [fs_ddictIsCold fsu_stage fsu_expected]. rewrite Fc. auto. }
      split; [auto | split].
      { exists ((pcs + Zlength c) mod Int64.modulus). split.
        - unfold vlong. rewrite <- Int64.unsigned_repr_eq, Int64.repr_unsigned. reflexivity.
        - pose proof (Z.mod_pos_bound (pcs + Zlength c) Int64.modulus ltac:(reflexivity)).
          unfold Int64.max_unsigned. lia. }
      split; [exists ds; auto |]. split; [auto | split; [auto | split]].
      { cbv [bl_cstage]. left. reflexivity. }
      eapply bl5_lay_congr; [| | | | | | exact Hlay].
      * cbn. rewrite Z.add_0_r. reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
    + intros b' Hb'. unfold bl5_ba in Hb'. cbn [ba_st] in Hb'.
      destruct (ba_st ba) as [b |] eqn:B; cbn in Hb'; inversion Hb'; subst b'.
      destruct (Hmr b B) as (Hs & Hbe & Hbd & Hdec & Hbo & _).
      cbn. split; [reflexivity | split; [reflexivity | split; [auto |]]].
      split; [unfold continuity; destruct (cont_moves _ _ _); exact Hdec |].
      split; [exact Hbo |]. intros X; exfalso; apply X; reflexivity.
    + exact Hmd.
  - unfold bl_claim_nc. destruct (ba_st ba) as [b |] eqn:B; auto. destruct (dictref_model _); auto. intros _.
    destruct (Hmr b B) as (Hs & _ & _ & _ & _ & Hm). rewrite Hst in Hm. destruct Hm as [Hh' Hxx].
    unfold bl_step_nc. rewrite Hs, Hst. unfold bl_step. rewrite Hs, Hst.
    replace ((fh_checksumFlag (bs_hdr b) =? 1) && negb (md_ignore md))%bool with (bl_val (md_ignore md) (bv_h v))
      by (rewrite Hh'; reflexivity).
    destruct (bl_val (md_ignore md) (bv_h v)) eqn:Ev.
    + destruct (Hck eq_refl) as (l & Hl & Hle). rewrite (Hxx eq_refl) in Hl. injection Hl as <-.
      rewrite Hle, Z.eqb_refl. cbn [andb negb].
      split; [intros _ | intros X; discriminate X].
      split; [reflexivity | split; [rewrite Z.add_0_r, sublist_nil; reflexivity |]].
      unfold bl5_ba. cbn. rewrite B. reflexivity.
    + cbn [andb].
      split; [intros _ | intros X; discriminate X].
      split; [reflexivity | split; [rewrite Z.add_0_r, sublist_nil; reflexivity |]].
      unfold bl5_ba. cbn. rewrite B. reflexivity.
Qed.

(* the DEBUGLOG loops as lemmas: for(;;break){} and for(;;break){ if (0) s } before c *)
Lemma bl5_loop_break {cs: compspecs} {Espec: OracleKind} Delta P body Post :
  semax Delta P body (loop1_ret_assert P (overridePost P Post)) ->
  semax Delta P (Sloop body Sbreak) (overridePost P Post).
Proof.
  intros H. eapply semax_loop; [exact H |].
  eapply semax_pre; [| apply semax_break]. intros rho. destruct Post; cbn. apply andp_left2, derives_refl.
Qed.

Lemma bl5_dw_skip {cs: compspecs} {Espec: OracleKind} Delta P c Post :
  semax Delta P c Post -> semax Delta P (Ssequence (Sloop Sskip Sbreak) c) Post.
Proof.
  intros H. eapply semax_seq; [| exact H]. apply bl5_loop_break.
  destruct Post. eapply semax_post; [| | | | apply semax_skip]; intros; intros rho; cbn; apply andp_left2;
    first [apply derives_refl | apply FF_left].
Qed.

Lemma bl5_dw_if0 {cs: compspecs} {Espec: OracleKind} Delta P s c Post :
  semax Delta P c Post ->
  semax Delta P (Ssequence (Sloop (Sifthenelse (Econst_int (Int.repr 0) tint) s Sskip) Sbreak) c) Post.
Proof.
  intros H. eapply semax_seq; [| exact H]. apply bl5_loop_break.
  eapply semax_pre; [| apply semax_ifthenelse; [reflexivity | |]].
  - apply andp_left2. eapply derives_trans; [| apply now_later]. apply andp_right; [| apply derives_refl].
    intros rho. cbn. apply TT_right.
  - eapply semax_pre; [| apply semax_ff]. apply andp_left2.
    intros rho. unfold local, lift1, liftx. cbn. apply andp_left2. apply prop_left. intros Hf.
    cbv in Hf. inversion Hf.
  - destruct Post. eapply semax_post; [| | | | apply semax_skip]; intros; intros rho; cbn; apply andp_left2;
      first [apply andp_left1, derives_refl | apply FF_left].
Qed.

End CM_BL5Facts_1.
