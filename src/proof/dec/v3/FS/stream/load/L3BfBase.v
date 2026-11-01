(* FS3 streaming, case zdss_load: a copy of read/R3Base.v on L3Borrow
   (tabs_of, fp_dm_ok come from L3Stmts). *)
Require Export Zstd.proof.dec.v3.FS.stream.load.L3Borrow.
Local Open Scope logic.

Section CM_L3BfBase_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* do { } while (0) (a DEBUGLOG/assert remnant) *)
Lemma semax_dowhile0 : forall {CS: compspecs} {Espec: OracleKind} Delta P c R,
  semax Delta P c R -> semax Delta P (Ssequence (Sloop Sskip Sbreak) c) R.
Proof.
intros CS Espec Delta P c R H.
apply semax_seq with P; [| exact H].
destruct R as [Rn Rb Rc Rr]; simpl.
apply semax_loop with (Q' := P).
- eapply semax_post_flipped; [apply semax_skip | ..]; simpl; intros; try apply andp_left2; auto;
    try apply FF_left.
- eapply semax_pre; [| apply semax_break]. simpl. intros; apply andp_left2; auto.
Qed.

Lemma land3_range : forall x, 0 <= Z.land x 3 <= 3.
Proof.
intros x. assert (E: Z.land x 3 = x mod 4) by (change 3 with (Z.ones 2); apply Z.land_ones; lia).
rewrite E. pose proof (Z.mod_pos_bound x 4). lia.
Qed.

(* do { c } while (0) *)
Lemma semax_dowhile0_gen : forall {CS: compspecs} {Espec: OracleKind} Delta P c R,
  semax Delta P c (loop1_ret_assert (RA_normal R) R) -> semax Delta P (Sloop c Sbreak) R.
Proof.
intros CS Espec Delta P c R H.
apply semax_loop with (Q' := RA_normal R); auto.
eapply semax_pre; [| apply semax_break]. destruct R; simpl; intros; apply andp_left2; auto.
Qed.

Definition bt_of (v: val) : Z := match v with Vint b => Int.signed b | _ => 0 end.

(* ---------- byte cells (R6) ---------- *)
Lemma byte_cells_Znth : forall l j, byte_cells l -> 0 <= j < Zlength l -> is_byte_val (Znth j l).
Proof. intros l j H Hj. unfold byte_cells in H. rewrite Forall_Znth in H. exact (H j Hj). Qed.

Lemma byte_cells_zbytes : forall l, bytes_ok l -> byte_cells (zbytes l).
Proof.
intros l H. unfold byte_cells, bytes_ok in *. induction H; simpl; constructor; auto.
all: try (exists x; split; auto; unfold is_byte in H; lia).
Qed.

Lemma byte_cells_app : forall l1 l2, byte_cells l1 -> byte_cells l2 -> byte_cells (l1 ++ l2).
Proof. intros. unfold byte_cells in *. apply Forall_app; auto. Qed.

Lemma byte_cells_sublist : forall l i j, byte_cells l -> byte_cells (sublist i j l).
Proof. intros. unfold byte_cells in *. apply Forall_sublist; auto. Qed.

(* the history of a segment [0, d) and an extDict inside an array of bytes is bytes *)
Lemma hist_def_bytes : forall oc d e, byte_cells oc -> 0 <= d <= Zlength oc ->
  match e with ExtNone => True | ExtIn e1 elen => 0 <= elen <= e1 /\ e1 <= Zlength oc | _ => False end ->
  hist_def oc d 0 e.
Proof.
intros oc d e Hb Hd He k Hk. unfold chist. destruct (k <=? d - 0) eqn:E.
- apply Z.leb_le in E. apply byte_cells_Znth; auto; lia.
- apply Z.leb_gt in E. destruct e as [|e1 elen|]; simpl in Hk, He; try lia; try contradiction.
  apply byte_cells_Znth; auto; lia.
Qed.


(* the frame stage, expected and bType at zdss_read, and ZSTD_nextSrcSizeToDecompressWithInputSize *)
Lemma read_ns : forall fs tabs fp l dd, c_frame fs tabs fp l dd ->
  (match fp with FP_skip _ got => got = 0 \/ fp_complete fp = true | _ => True end) ->
  (fp_rawbody fp = true \/ fp_loaded fp = nil \/ fp_complete fp = true) ->
  exists stage e, fs_stage fs = Vint (Int.repr stage) /\ fs_expected fs = Vlong (Int64.repr e) /\
    0 <= stage <= 7 /\ 0 <= e <= Int64.max_unsigned /\
    ((stage = ds_decompressBlock \/ stage = ds_decompressLastBlock) ->
       exists b, fs_bType fs = Vint (Int.repr b) /\ 0 <= b <= 3) /\
    (fp_complete fp = true -> (stage = 0 \/ stage = 7) /\ e = 0) /\
    (fp_complete fp = false -> forall n, 0 <= n ->
       let ns := next_size stage (bt_of (fs_bType fs)) e n in
       0 < ns <= Int64.max_unsigned /\ (ns <= n -> unit_ok fp ns) /\
       (n < ns -> 0 < n -> fp_rawbody fp = false)).
Proof.
intros fs tabs fp l dd Hc Hsk Hraw.
destruct fp as [|hb|hdr got|hdr z]; unfold c_frame in Hc; try tauto.
- destruct Hc as (_&_&_&_&_&Hl&_&(h&Hh&Ht&Hf)&Hg&Hlt&Hst).
  simpl fp_complete in *.
  unfold ds_decompressBlock, ds_decompressLastBlock.
  destruct (got =? le_field hdr 4 4) eqn:E.
  + destruct Hst as [[Hs|Hs] He]; [exists 0, 0 | exists 7, 0]; rewrite Hs, He.
    all: repeat split; auto; try rep_lia; intros; try lia; discriminate.
  + destruct Hst as [Hs He]. apply Z.eqb_neq in E.
    destruct Hsk as [Hsk|Hsk]; [|discriminate].
    exists 7, (le_field hdr 4 4). rewrite Hs, He.
    repeat split; auto; try rep_lia; intros; try lia; try discriminate.
    all: unfold next_size; simpl; try rep_lia; auto.
- destruct Hc as (_&_&_&_&_&_&_&Hbsm&Hbeq&_&_&_&_&_&_&Hph&_&_&_&_&Hpc&_).
  unfold phase_fields in Hph. unfold fp_rawbody, fp_loaded, fp_complete in Hraw. simpl fp_complete.
  unfold ds_decompressBlock, ds_decompressLastBlock, ZSTD_blockHeaderSize, ZSTD_BLOCKSIZE_MAX in *.
  destruct (zp_ph z) as [|bh| |] eqn:Ep.
  + destruct Hph as [Hs He]. exists 2, 3. rewrite Hs, He.
    destruct Hraw as [Hraw|[Hraw|Hraw]]; try (rewrite Ep in Hraw; discriminate); try discriminate.
    repeat split; auto; try rep_lia; intros; try lia; try discriminate.
    all: unfold next_size, unit_ok, fp_rawbody; rewrite ?Ep; simpl; try rep_lia; auto.
  + destruct Hph as (c&Hcb&Hs&Hb&_&He). destruct Hpc as (_&_&c'&Hcb'&Hc&Hg&Hbt3).
    rewrite Hcb in Hcb'; inversion Hcb'; subst c'; clear Hcb'.
    assert (Hbt: 0 <= bp_type (block_props_of bh) <= 3)
      by (unfold block_props_of; simpl; apply land3_range).
    set (bt := bp_type (block_props_of bh)) in *.
    assert (Hlz: 0 <= Zlength (zp_got z)) by apply Zlength_nonneg.
    assert (Hbo: bt_of (Vint (Int.repr bt)) = bt) by (simpl; rewrite Int.signed_repr; rep_lia).
    destruct (bp_last (block_props_of bh) =? 1) eqn:EL;
    [exists 4 | exists 3]; exists (if bt =? 0 then c - Zlength (zp_got z) else c);
    rewrite Hs, He, Hb, Hbo;
    (split; [reflexivity|]); (split; [reflexivity|]); (split; [lia|]);
    (split; [destruct (bt =? 0); rep_lia|]);
    (split; [intros; exists bt; auto|]);
    (split; [discriminate|]);
    intros _ n Hn;
    unfold next_size, unit_ok, fp_rawbody; rewrite Ep; fold bt;
    destruct (bt =? 0) eqn:E0; unfold ds_decompressBlock, ds_decompressLastBlock; simpl.
    all: destruct Hraw as [Hraw|[Hraw|Hraw]]; try discriminate.
    all: split; [rep_lia|]; split; [intros; exists c; split; auto; rewrite ?E0; simpl; try lia; auto|].
    all: intros; try lia; auto.
  + destruct Hph as [Hs He]. exists 5, 4. rewrite Hs, He.
    destruct Hraw as [Hraw|[Hraw|Hraw]]; try (rewrite Ep in Hraw; discriminate); try discriminate.
    repeat split; auto; try rep_lia; intros; try lia; try discriminate.
    all: unfold next_size, unit_ok, fp_rawbody; rewrite ?Ep; simpl; try rep_lia; auto.
  + destruct Hph as [Hs He]. exists 0, 0. rewrite Hs, He.
    repeat split; auto; try rep_lia; intros; try lia; discriminate.
Qed.

(* ---------- the stream buffer [inBuff | outBuff] around ZSTD_decompressContinueStream ---------- *)

Lemma ring_data_split : forall b n1 n2 (c: list val), 0 <= n1 -> 0 <= n2 -> Zlength c = n1 + n2 ->
  field_compatible (tarray tuchar (n1 + n2)) [] b ->
  data_at Ews (tarray tuchar (n1 + n2)) c b =
  (data_at Ews (tarray tuchar n1) (sublist 0 n1 c) b *
   data_at Ews (tarray tuchar n2) (sublist n1 (n1 + n2) c) (offset_val n1 b))%logic.
Proof.
intros b n1 n2 c H1 H2 Hc Hf.
unfold tarray. rewrite (split2_data_at_Tarray_tuchar Ews (n1 + n2) n1 c b) by lia.
replace (n1 + n2 - n1) with n2 by lia.
rewrite field_address0_offset by auto with field_compatible.
simpl. rewrite Z.mul_1_l. reflexivity.
Qed.

(* the weak validity of the output part [outBuff, outBuff + nO] (outBuff = inBuff + nI): the input part,
   lent as a witness, covers outBuff itself (nO may be 0) *)
Lemma wvp_ring : forall (W: list ptr_witness) b nI nO (cI cO: list val) (R: mpred) x,
  0 < nI -> 0 <= x <= nO ->
  (pws_pred (pw_bytes Ews nI cI b :: W) * data_at Ews (tarray tuchar nO) cO (offset_val nI b) * R
     |-- weak_valid_pointer (offset_val x (offset_val nI b)))%logic.
Proof.
intros W b nI nO cI cO R x HnI Hx.
unfold pws_pred. simpl map. simpl fold_right. unfold pw_pred at 1.
rewrite offset_offset_val.
destruct (Z.eq_dec x 0) as [->|Hx0].
- rewrite Z.add_0_r. rewrite !sepcon_assoc. apply sepcon_weak_valid_pointer1.
  eapply derives_trans; [apply data_at_memory_block|].
  simpl sizeof. rewrite Z.max_r by lia. rewrite Z.mul_1_l.
  replace (offset_val nI b) with (offset_val nI b) by reflexivity.
  apply memory_block_weak_valid_pointer; [lia | lia | apply readable_nonidentity; auto].

- apply sepcon_weak_valid_pointer1. apply sepcon_weak_valid_pointer2.
  eapply derives_trans; [apply data_at_memory_block|].
  simpl sizeof. rewrite Z.max_r by lia. rewrite Z.mul_1_l.
  rewrite <- offset_offset_val.
  apply memory_block_weak_valid_pointer; [lia | lia | apply readable_nonidentity; auto].
Qed.

(* the caller's output buffer (stable mode): its ends from buf_ok, its inside from the cells *)
Lemma wvp_buf : forall (W: list ptr_witness) sh n (c: list val) p (R: mpred) x,
  buf_ok W sh n p -> readable_share sh -> 0 <= x <= n ->
  (pws_pred W * data_at sh (tarray tuchar n) c p * R |-- weak_valid_pointer (offset_val x p))%logic.
Proof.
intros W sh n c p R x Hb Hr Hx.
apply sepcon_weak_valid_pointer1.
assert_PROP (isptr p) as Pp by (saturate_local; entailer!).
destruct (Z.eq_dec x n) as [->|Hxn].
- sep_apply (data_at_data_at_ sh (tarray tuchar n) c p).
  rewrite sepcon_comm. eapply derives_trans; [apply Hb|]. apply andp_left2. auto.
- destruct (Z.eq_dec x 0) as [->|Hx0].
  + sep_apply (data_at_data_at_ sh (tarray tuchar n) c p).
    rewrite sepcon_comm. eapply derives_trans; [apply Hb|]. apply andp_left1. rewrite isptr_offset_val_zero by auto. auto.
  + apply sepcon_weak_valid_pointer2.
    eapply derives_trans; [apply data_at_memory_block|].
    simpl sizeof. rewrite Z.max_r by lia. rewrite Z.mul_1_l.
    eapply derives_trans; [apply (memory_block_valid_pointer sh n p x); [lia | apply readable_nonidentity; auto]|].
    apply valid_pointer_weak.
Qed.

(* iend - ip *)
Lemma sub_pp_tschar : forall p i j, isptr p -> 0 <= j <= i -> i <= 2 ^ 30 ->
  force_val (sem_sub_pp tschar (offset_val i p) (offset_val j p)) = Vlong (Int64.repr (i - j)).
Proof.
intros p i j Hp Hj Hi. destruct p; try contradiction.
unfold sem_sub_pp; simpl. rewrite if_true by auto. simpl. f_equal.
rewrite !(Ptrofs.add_commut i0), Ptrofs.sub_shifted. rewrite Ptrofs.divs_one by reflexivity.
unfold Vptrofs, Ptrofs.sub. rewrite !Ptrofs.unsigned_repr by rep_lia. simpl.
unfold Ptrofs.to_int64. rewrite Ptrofs.unsigned_repr by rep_lia. reflexivity.
Qed.

(* comparing two pointers into one array *)
Local Transparent denote_tc_test_eq.
Lemma tc_test_eq_same : forall (P: mpred) p i j, isptr p ->
  (P |-- weak_valid_pointer (offset_val i p)) -> (P |-- weak_valid_pointer (offset_val j p)) ->
  P |-- denote_tc_test_eq (offset_val i p) (offset_val j p).
Proof.
intros P p i j Hp Hi Hj. destruct p; try contradiction.
unfold denote_tc_test_eq, offset_val in *. simpl. unfold test_eq_ptrs.
unfold sameblock. destruct (peq b b); [|congruence]. simpl.
apply andp_right; auto.
Qed.
Global Opaque denote_tc_test_eq.

(* ---------- ZSTD_decompressContinueStream in zdss_read ---------- *)

(* the frame fields but stage, bType, expected *)
Definition frame_rest (p: val) (fs: fstate) : mpred :=
  (field_at Ews t_dctx (DOT _previousDstEnd) (fs_previousDstEnd fs) p *
  field_at Ews t_dctx (DOT _gpDictCopy) (fs_gpDictCopy fs) p *
  field_at Ews t_dctx (DOT _prefixStart) (fs_prefixStart fs) p *
  field_at Ews t_dctx (DOT _virtualStart) (fs_virtualStart fs) p *
  field_at Ews t_dctx (DOT _dictEnd) (fs_dictEnd fs) p *
  field_at Ews t_dctx (DOT _fParams) (fs_fParams fs) p *
  field_at Ews t_dctx (DOT _processedCSize) (fs_processedCSize fs) p *
  field_at Ews t_dctx (DOT _decodedSize) (fs_decodedSize fs) p *
  xxh_field p (fs_xxh fs) *
  field_at Ews t_dctx (DOT _headerSize) (fs_headerSize fs) p *
  field_at Ews t_dctx (DOT _validateChecksum) (fs_validateChecksum fs) p *
  field_at Ews t_dctx (DOT _rleSize) (fs_rleSize fs) p *
  field_at Ews t_dctx (DOT _isFrameDecompression) (fs_isFrameDecompression fs) p *
  field_at Ews t_dctx (DOT _dictID) (fs_dictID fs) p *
  field_at Ews t_dctx (DOT _ddictIsCold) (fs_ddictIsCold fs) p)%logic.

Lemma frame_fields_split : forall p fs,
  frame_fields p fs =
  (field_at Ews t_dctx (DOT _stage) (fs_stage fs) p * field_at Ews t_dctx (DOT _bType) (fs_bType fs) p *
   field_at Ews t_dctx (DOT _expected) (fs_expected fs) p * frame_rest p fs)%logic.
Proof. intros. unfold frame_fields, frame_rest. apply pred_ext; cancel. Qed.

(* the stream fields after ZSTD_decompressContinueStream (buffered): stage, outEnd and the ring *)
Definition sf_cont (s: sfields) (stage: Z) (oe: val) (ring: list val) : sfields :=
  {| sf_stage := stage; sf_inBuff := sf_inBuff s; sf_inSize := sf_inSize s; sf_inPos := sf_inPos s;
     sf_outBuff := sf_outBuff s; sf_outSize := sf_outSize s; sf_outStart := sf_outStart s;
     sf_outEnd := oe; sf_lhSize := sf_lhSize s; sf_hostage := sf_hostage s; sf_nfp := sf_nfp s;
     sf_expOut := sf_expOut s; sf_hbuf := sf_hbuf s; sf_over := sf_over s; sf_ring := ring; sf_mem := sf_mem s; sf_held := sf_held s |}.

Definition oa_stable (sh: share) (ob: val) (osz: Z) (fp: fprog) (oc: list val) (opc: Z) : outarr :=
  {| oa_sh := sh; oa_base := ob; oa_N := osz; oa_c := oc; oa_d := opc;
     oa_cap := if is_skip fp then 0 else osz - opc |}.

Definition oa_ring (s: sfields) (fp: fprog) (ostart: Z) : outarr :=
  {| oa_sh := Ews; oa_base := sf_outBuff s; oa_N := sf_outSize s;
     oa_c := sublist (sf_inSize s) (sf_inSize s + sf_outSize s) (sf_ring s); oa_d := ostart;
     oa_cap := if is_skip fp then 0 else sf_outSize s - ostart |}.

Definition iw_read (sh: share) (ib: val) (isz: Z) (ibs: list Z) (ipc ns: Z) : inwin :=
  {| iw_sh := sh; iw_base := ib; iw_N := isz; iw_c := zbytes ibs; iw_off := ipc;
     iw_s := sublist ipc (ipc + ns) ibs |}.

Lemma in_res_split : forall fp sh ib isz ibs ipc ns,
  data_at sh (tarray tuchar isz) (zbytes ibs) ib =
  (in_res fp (iw_read sh ib isz ibs ipc ns) *
   (if is_skip fp then data_at sh (tarray tuchar isz) (zbytes ibs) ib else emp))%logic.
Proof.
intros. unfold in_res. destruct (is_skip fp); simpl.
- rewrite emp_sepcon. reflexivity.
- rewrite sepcon_emp. reflexivity.
Qed.

Lemma c_frame_tabs : forall fs tabs fp l dd, c_frame fs tabs fp l dd -> exists ts, tabs = TInit (dd_ox dd) ts.
Proof.
intros fs tabs fp l dd H. destruct fp; unfold c_frame in H; try tauto.
destruct H as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&(ts&Ht&_)&_); eauto.
Qed.

Lemma c_ring_ostart : forall stable obuf sout s fp pend l,
  c_ring stable obuf sout s fp pend l -> 0 <= sf_outSize s ->
  exists ostart oend, sf_outStart s = vlong ostart /\ sf_outEnd s = vlong oend /\ 0 <= ostart <= oend /\
    oend <= sf_outSize s /\ (stable = true -> ostart = 0 /\ oend = 0).
Proof.
intros stable obuf sout s fp pend l H Hn. destruct H as (_&_&_&ostart&oend&Hs&He&Ho&Hr).
exists ostart, oend. split; [auto|]. split; [auto|]. split; [lia|]. destruct stable.
- destruct Hr as (->&->&_). split; [lia | auto].
- destruct Hr as (Hr&_). split; [lia | discriminate].
Qed.

(* the input part of the ring makes the output part's start weakly valid *)
Lemma pw_ring_wvp : forall nI (cI: list val) b, 0 < nI ->
  pw_pred (pw_bytes Ews nI cI b) |-- weak_valid_pointer (offset_val nI b).
Proof.
intros nI cI b H. unfold pw_pred.
eapply derives_trans; [apply data_at_memory_block|].
simpl sizeof. rewrite Z.max_r by lia. rewrite Z.mul_1_l.
rewrite <- (Z.add_0_r nI) at 2.
replace (offset_val nI b) with (offset_val nI b) by reflexivity.
apply memory_block_weak_valid_pointer; [lia | lia | apply readable_nonidentity; auto].
Qed.

Lemma zstep_h : forall z u cnt ts', zp_h (zstep z u cnt ts') = zp_h z.
Proof.
intros z u cnt ts'. unfold zstep. destruct (zp_ph z); try reflexivity.
- destruct (cblock_size u); [destruct (_ =? 0)|]; reflexivity.
- destruct (_ =? 0); [destruct (match cblock_size bh with Some c => _ | None => false end)|]; reflexivity.
Qed.

Lemma zstep_out : forall z u cnt ts', cnt_safe z u cnt ts' -> zp_out (zstep z u cnt ts') = zp_out z ++ cnt.
Proof.
intros z u cnt ts'. unfold cnt_safe, zstep. destruct (zp_ph z) as [|bh| |]; intros H.
- destruct H as [-> _]. rewrite app_nil_r. destruct (cblock_size u); [destruct (_ =? 0)|]; reflexivity.
- destruct (bp_type (block_props_of bh) =? 0).
  + destruct H as [-> _]. destruct (match cblock_size bh with Some c => _ | None => false end); reflexivity.
  + reflexivity.
- destruct H as [-> _]. rewrite app_nil_r. reflexivity.
- destruct H as [-> _]. rewrite app_nil_r. reflexivity.
Qed.

(* the unit leaves no loaded bytes (all units but the checksum) *)
Lemma zstep_loaded : forall hdr z u cnt ts' n, unit_ok (FP_zstd hdr z) n -> zp_ph z <> ZP_ck ->
  fp_rawbody (FP_zstd hdr (zstep z u cnt ts')) = true \/ fp_loaded (FP_zstd hdr (zstep z u cnt ts')) = nil.
Proof.
intros hdr z u cnt ts' n Hu Hck. unfold unit_ok in Hu. unfold fp_rawbody, fp_loaded, zstep.
destruct (zp_ph z) as [|bh| |] eqn:Ep.
- destruct Hu as [Hg _]. destruct (cblock_size u); [destruct (_ =? 0)|]; simpl; auto.
- destruct (bp_type (block_props_of bh) =? 0) eqn:E0.
  + destruct (match cblock_size bh with Some c => _ | None => false end); simpl; auto.
  + simpl; auto.
- congruence.
- contradiction.
Qed.

Lemma sublist_app_tail : forall {A} (l c: list A) ps, 0 <= ps <= Zlength l ->
  sublist ps (Zlength l + Zlength c) (l ++ c) = sublist ps (Zlength l) l ++ c.
Proof.
intros A l c ps H. pose proof (Zlength_nonneg c).
rewrite (sublist_split ps (Zlength l) (Zlength l + Zlength c)) by (rewrite ?Zlength_app; lia).
rewrite sublist_app1 by lia. rewrite sublist_app2 by lia.
rewrite Z.sub_diag. replace (Zlength l + Zlength c - Zlength l) with (Zlength c) by lia.
rewrite (sublist_same 0 (Zlength c)); auto.
Qed.

Lemma unch_sublist : forall (oc oc': list val) lo hi i j, unchanged_outside oc oc' lo hi ->
  Zlength oc' = Zlength oc -> 0 <= i <= j -> j <= lo -> j <= Zlength oc -> sublist i j oc' = sublist i j oc.
Proof.
intros oc oc' lo hi i j Hu Hl Hij Hj Hjo.
apply Znth_eq_ext; [rewrite !Zlength_sublist; lia|].
intros x Hx. rewrite Zlength_sublist in Hx by lia. rewrite !Znth_sublist by lia. apply Hu; lia.
Qed.

Lemma sublist_len_bound : forall {A} (l: list A) lo hi, 0 <= lo <= hi -> lo <= Zlength l ->
  Zlength (sublist lo hi l) = hi - lo -> hi <= Zlength l.
Proof.
intros A l lo hi H Hlo Hz. destruct (Z_le_gt_dec hi (Zlength l)); auto. exfalso.
rewrite Zlength_correct in g, Hlo. unfold sublist in Hz. rewrite firstn_all2 in Hz by lia.
rewrite Zlength_correct in Hz. rewrite skipn_length in Hz. lia.
Qed.

(* a checksum unit completes the frame *)
Lemma zstep_ck_complete : forall hdr z u cnt ts', zp_ph z = ZP_ck ->
  fp_complete (FP_zstd hdr (zstep z u cnt ts')) = true.
Proof. intros hdr z u cnt ts' Hp. unfold zstep, fp_complete. rewrite Hp. reflexivity. Qed.

(* the new output part of the stream buffer *)
Lemma ring_out_cells : forall nI nO (ring oc': list val),
  Zlength ring = nI + nO -> 0 <= nI -> 0 <= nO -> Zlength oc' = nO ->
  sublist nI (nI + nO) (sublist 0 nI ring ++ oc') = oc'.
Proof.
intros nI nO ring oc' Hl HI HO Ho.
rewrite sublist_app2 by (rewrite Zlength_sublist by lia; lia).
rewrite Zlength_sublist by lia. rewrite sublist_same by lia. reflexivity.
Qed.

(* the ring's arithmetic: a frame that does not fit has a ring of at least a window and two blocks *)
Lemma ring_big : forall h bsm N, N >= ring_needed h bsm -> N < fh_contentSize h -> 0 <= fh_windowSize h ->
  0 <= bsm <= Z.min (fh_windowSize h) ZSTD_BLOCKSIZE_MAX ->
  fh_windowSize h + 2 * bsm + 2 * WILDCOPY_OVERLENGTH <= N.
Proof.
intros h bsm N Hr Hf Hw Hb. unfold ring_needed in Hr. unfold ZSTD_WINDOWSIZE_ABSMIN, ZSTD_BLOCKSIZE_MAX in *.
lia.
Qed.

(* ---------- read_cont_buf: one unit of a Zstandard frame ---------- *)

Lemma cnt_len : forall hdr z u cnt ts', cnt_safe z u cnt ts' -> 0 <= zp_bsm z ->
  (forall bh, zp_ph z = ZP_body bh -> exists c, cblock_size bh = Some c /\ c <= zp_bsm z) ->
  0 <= Zlength (zp_got z) -> unit_ok (FP_zstd hdr z) (Zlength u) -> Zlength cnt <= zp_bsm z.
Proof.
intros hdr z u cnt ts' H Hb Hc Hg Hu. unfold cnt_safe, unit_ok in *. destruct (zp_ph z) as [|bh| |].
- destruct H as [-> _]. rewrite Zlength_nil. lia.
- destruct (Hc bh eq_refl) as (c&Ec&Hcb). destruct Hu as (c'&Ec'&Hu). rewrite Ec in Ec'. inversion Ec'; subst c'.
  destruct (bp_type (block_props_of bh) =? 0); [|destruct (bp_type (block_props_of bh) =? 1)].
  + destruct H as [-> _]. lia.
  + destruct H as (->&_&Ho). rewrite Zlength_correct, repeat_length. lia.
  + destruct H as [_ H]. exact H.
- destruct H as [-> _]. rewrite Zlength_nil. lia.
- destruct H as [-> _]. rewrite Zlength_nil. lia.
Qed.

(* the stage is not zdss_load: the next unit is not loaded (a block header, a whole body), or a raw block *)
Lemma zstep_loaded_u : forall hdr z u cnt ts', unit_ok (FP_zstd hdr z) (Zlength u) -> zp_ph z <> ZP_ck ->
  fp_rawbody (FP_zstd hdr (zstep z u cnt ts')) = true \/ fp_loaded (FP_zstd hdr (zstep z u cnt ts')) = nil.
Proof.
intros hdr z u cnt ts' Hu Hck. unfold unit_ok in Hu. unfold zstep, fp_rawbody, fp_loaded.
destruct (zp_ph z) as [|bh| |] eqn:Ep.
- destruct Hu as [Hg _]. destruct (cblock_size u) as [c|]; [destruct (c =? 0)|]; simpl; rewrite ?Ep; auto.
- destruct (bp_type (block_props_of bh) =? 0) eqn:E0.
  + destruct (cblock_size bh) as [c|]; [destruct (Zlength (zp_got z ++ u) =? c)|]; cbn [zp_with zp_ph zp_got];
      [right; reflexivity|left; exact E0|left; exact E0].
  + right. reflexivity.
- contradiction.
- contradiction.
Qed.

(* after the checksum the frame is complete *)
Lemma zstep_loaded_ck : forall hdr z u cnt ts', zp_ph z = ZP_ck ->
  fp_complete (FP_zstd hdr (zstep z u cnt ts')) = true.
Proof. intros hdr z u cnt ts' Ep. unfold fp_complete, zstep. rewrite Ep. reflexivity. Qed.

Lemma c_frame_body : forall fs tabs hdr z l dd bh, c_frame fs tabs (FP_zstd hdr z) l dd -> zp_ph z = ZP_body bh ->
  exists c, cblock_size bh = Some c /\ 0 < c <= zp_bsm z /\ Zlength (zp_got z) < c.
Proof.
intros fs tabs hdr z l dd bh H Ep. destruct H as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&Hx&_).
rewrite Ep in Hx. destruct Hx as (_&_&c&Hc&Hb&Hg&_). eauto.
Qed.

Lemma lcp_vlong_inj : forall x y, 0 <= x <= Int64.max_unsigned -> 0 <= y <= Int64.max_unsigned ->
  vlong x = vlong y -> x = y.
Proof.
intros x y Hx Hy H. unfold vlong in H. inversion H as [H1].
rewrite <- (Int64.unsigned_repr x), <- (Int64.unsigned_repr y) by rep_lia. congruence.
Qed.

Lemma is_prefix_app_r : forall (x y r: list Z), is_prefix (x ++ y) (x ++ y ++ r).
Proof.
intros. unfold is_prefix. rewrite app_assoc. rewrite firstn_app, firstn_all, Nat.sub_diag. simpl. apply app_nil_r.
Qed.

Lemma is_prefix_trans : forall (x y s: list Z), is_prefix x y -> is_prefix y s -> is_prefix x s.
Proof.
unfold is_prefix. intros x y s H1 H2. rewrite <- H1 at 2. rewrite <- H2.
rewrite firstn_firstn. f_equal. rewrite <- H1, length_firstn. lia.
Qed.

(* a cell of an unsigned char array that is an int is a byte *)
Lemma fits_byte : forall i, value_fits tuchar (Vint i) -> is_byte_val (Vint i).
Proof.
intros i Hf. exists (Int.unsigned i). rewrite Int.repr_unsigned. split; [|reflexivity].
simpl in Hf. unfold tc_val' in Hf. specialize (Hf ltac:(discriminate)). simpl in Hf. rep_lia.
Qed.

Lemma tc_ret_temp_ulong : forall {CS: compspecs} Delta id v (P: environ -> mpred),
  Maps.PTree.get id (temp_types Delta) = Some tulong ->
  local (tc_environ Delta) && (local (locald_denote (temp id (Vlong v))) && P) |--
    tc_expr Delta (Ecast (Etempvar id tulong) tulong).
Proof.
intros CS Delta id v P Hid.
unfold tc_expr. cbn [typecheck_expr]. rewrite Hid.
simpl. intro rho. unfold local, lift1. simpl. normalize. apply prop_right.
destruct H0 as [H0 _]. assert (E: Vlong v = eval_id id rho) by exact H0. clear H0.
unfold eval_id in E. destruct (Map.get (te_of rho) id) eqn:E2; simpl in E; [|discriminate].
subst. exists (Vlong v). split; auto. simpl. auto.
Qed.

(* ---------- conventions shared with case zdss_load (load/) ---------- *)

(* lay_cbound: L3Stmts *)

(* the DDict facts the buffered step uses (read/R3Base.v's dd_facts reduced to what ld_dd gives) *)
Definition dd_bf (W: list ptr_witness) (dd: option (ddx * val)) : Prop :=
  match dd with
  | None => True
  | Some (x, buf) => bytes_ok (dx_bytes x) /\ Zlength (dx_bytes x) <= 2 ^ 63 - 1 /\ (isptr buf \/ (buf = nullval /\ dx_ref x = Some nullval /\ dx_bytes x = nil))
  end.

Lemma dd_bf_of : forall W dd, ld_dd dd -> dd_bf W dd.
Proof.
intros W [[x buf]|] H; cbn [dd_bf]; [|exact I].
destruct (H x buf eq_refl) as (H1&H2&H3&_). auto.
Qed.

End CM_L3BfBase_1.
