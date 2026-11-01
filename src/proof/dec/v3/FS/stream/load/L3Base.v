(* FS3 streaming, case zdss_load: generic helpers, the views after loading, load_facts, the partial
   load; ported from v2 StreamSeg_load.v. *)
Require Export Zstd.proof.dec.v3.FS.stream.S3RetStmts Zstd.proof.dec.v3.FS.stream.S3ModelStmts.
Local Open Scope logic.

(* the precondition with old replaced by new (in LOCAL and SEP) as the join point of an if *)
Ltac rep_in T old new :=
  let f := eval pattern old in T in
  match f with ?g _ => let r := eval cbv beta in (g new) in exact r end.

Ltac fif_rep old new :=
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    let Q2 := constr:(ltac:(rep_in Q old new)) in
    let R2 := constr:(ltac:(rep_in R old new)) in
    forward_if (PROPx P (LOCALx Q2 (SEPx R2)))
  end.

(* the precondition with a new temp, as the join point of an if *)
Ltac fif_temp id v :=
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp id v :: Q) (SEPx R)))
  end.

Section CM_L3Base_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma sameblock_off : forall p i j, isptr p -> is_true (sameblock (offset_val i p) (offset_val j p)).
Proof.
intros p i j Hp. destruct p; try contradiction. unfold sameblock; simpl.
destruct (peq b b); [reflexivity | congruence].
Qed.

Lemma sub_pp_off : forall p i j, isptr p -> 0 <= j <= i -> i <= Ptrofs.max_unsigned ->
  sem_sub_pp tschar (offset_val i p) (offset_val j p) = Some (Vlong (Int64.repr (i - j))).
Proof.
intros p i j Hp Hij Hi. destruct p; try contradiction. unfold sem_sub_pp; simpl.
destruct (eq_block b b); [|congruence]. simpl. f_equal.
rewrite (Ptrofs.add_commut i0 (Ptrofs.repr i)), (Ptrofs.add_commut i0 (Ptrofs.repr j)).
rewrite Ptrofs.sub_shifted. unfold Ptrofs.sub. rewrite !Ptrofs.unsigned_repr by rep_lia.
unfold Ptrofs.divs. rewrite (Ptrofs.signed_repr 1) by rep_lia. rewrite Z.quot_1_r, Ptrofs.repr_signed.
unfold Vptrofs. simpl. f_equal. unfold Ptrofs.to_int64. rewrite Ptrofs.unsigned_repr by rep_lia.
reflexivity.
Qed.

Lemma tt_ltu64 : forall x y, 0 <= x <= Int64.max_unsigned -> 0 <= y <= Int64.max_unsigned ->
  typed_true tint (bool2val (Int64.ltu (Int64.repr x) (Int64.repr y))) -> x < y.
Proof.
intros x y Hx Hy H. unfold Int64.ltu in H. rewrite !Int64.unsigned_repr in H by rep_lia.
destruct (zlt x y); auto. inversion H.
Qed.

Lemma tf_ltu64 : forall x y, 0 <= x <= Int64.max_unsigned -> 0 <= y <= Int64.max_unsigned ->
  typed_false tint (bool2val (Int64.ltu (Int64.repr x) (Int64.repr y))) -> y <= x.
Proof.
intros x y Hx Hy H. unfold Int64.ltu in H. rewrite !Int64.unsigned_repr in H by rep_lia.
destruct (zlt x y); [inversion H | lia].
Qed.

Lemma ltu64_t : forall x y, 0 <= x <= Int64.max_unsigned -> 0 <= y <= Int64.max_unsigned ->
  Int64.ltu (Int64.repr x) (Int64.repr y) = true -> x < y.
Proof.
intros x y Hx Hy H. unfold Int64.ltu in H. rewrite !Int64.unsigned_repr in H by rep_lia.
destruct (zlt x y); auto. inversion H.
Qed.

Lemma ltu64_f : forall x y, 0 <= x <= Int64.max_unsigned -> 0 <= y <= Int64.max_unsigned ->
  Int64.ltu (Int64.repr x) (Int64.repr y) = false -> y <= x.
Proof.
intros x y Hx Hy H. unfold Int64.ltu in H. rewrite !Int64.unsigned_repr in H by rep_lia.
destruct (zlt x y); [inversion H | lia].
Qed.

Lemma Zlength_copy_cells : forall oc od cs os m,
  0 <= od -> 0 <= m -> od + m <= Zlength oc -> 0 <= os -> os + m <= Zlength cs ->
  Zlength (copy_cells oc od cs os m) = Zlength oc.
Proof.
intros. unfold copy_cells. rewrite !Zlength_app, !Zlength_sublist by lia. lia.
Qed.

Lemma tarray_len : forall sh n (c: list val) p, Zlength c = n ->
  data_at sh (tarray tuchar n) c p |-- data_at sh (tarray tuchar (Zlength c)) c p.
Proof. intros; subst; auto. Qed.

Lemma tarray_len' : forall sh n (c: list val) p, Zlength c = n ->
  data_at sh (tarray tuchar (Zlength c)) c p |-- data_at sh (tarray tuchar n) c p.
Proof. intros; subst; auto. Qed.

Lemma sub64_repr : forall x y, 0 <= y <= x -> x <= Int64.max_unsigned ->
  Int64.sub (Int64.repr x) (Int64.repr y) = Int64.repr (x - y).
Proof. intros x y H1 H2. unfold Int64.sub. rewrite !Int64.unsigned_repr by rep_lia. reflexivity. Qed.

Lemma add_ptr_long_off : forall p i j, isptr p -> 0 <= j <= Int64.max_unsigned ->
  force_val (sem_add_ptr_long tschar (offset_val i p) (vlong j)) = offset_val (i + j) p.
Proof.
intros p i j Hp Hj. destruct p; try contradiction. unfold sem_add_ptr_long, vlong; simpl.
change (Ptrofs.repr 1) with Ptrofs.one. rewrite Ptrofs.mul_commut, Ptrofs.mul_one.
unfold Ptrofs.of_int64. rewrite Int64.unsigned_repr by rep_lia.
rewrite Ptrofs.add_assoc, ptrofs_add_repr. reflexivity.
Qed.

End CM_L3Base_1.

(* the branch condition of a comparison with iend - ip: to a Prop *)
Ltac cond64 H :=
  repeat match type of H with context [sem_sub_pp tschar (offset_val ?i ?p) (offset_val ?j ?p)] =>
    rewrite (sub_pp_off p i j) in H by (auto; rep_lia) end;
  repeat match type of H with context [Int64.sub (Int64.repr ?x) (Int64.repr ?y)] =>
    rewrite (sub64_repr x y) in H by rep_lia end;
  cbn [force_val both_long sem_cast_pointer] in H;
  first [apply tt_ltu64 in H | apply tf_ltu64 in H | apply ltu64_t in H | apply ltu64_f in H];
  [| rep_lia | rep_lia].

Ltac cond64h :=
  match goal with
  | H: typed_true _ _ |- _ => cond64 H
  | H: typed_false _ _ |- _ => cond64 H
  | H: Int64.ltu _ _ = _ |- _ => cond64 H
  end.

(* the side condition of iend - ip *)
Ltac sbk :=
  first [ apply sameblock_off; auto
        | apply prop_right; apply sameblock_off; auto
        | entailer!; first [apply sameblock_off; auto | apply prop_right; apply sameblock_off; auto]
        | fail 0 "sbk" ].

Section CM_L3Base_2.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.

(* ddictIsCold is 0 or 1 in the invariant *)
(* do { } while (0), and do { if (0) X; } while (0): no-ops (cheap replacements of forward_loop) *)
Lemma ld_dowhile0 : forall {CS: compspecs} {Espec: OracleKind} Delta P c R,
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

Lemma ld_dowhile0_if0 : forall {CS: compspecs} {Espec: OracleKind} Delta P X c R,
  semax Delta P c R ->
  semax Delta P (Ssequence (Sloop (Sifthenelse (Econst_int (Int.repr 0) tint) X Sskip) Sbreak) c) R.
Proof.
intros CS Espec Delta P X c R H.
apply semax_seq with P; [| exact H].
destruct R as [Rn Rb Rc Rr]; simpl.
apply semax_loop with (Q' := P).
- eapply semax_pre; [| apply semax_ifthenelse; [reflexivity | | ]].
  + apply andp_left2. eapply derives_trans; [| apply now_later].
    apply andp_right; [| apply derives_refl].
    intro rho. unfold tc_expr. simpl. apply TT_right.
  + eapply semax_pre; [| apply semax_ff].
    intro rho. unfold local, lift1; unfold_lift. simpl. apply andp_left2. apply andp_left2. apply prop_derives. intros Hf.
    unfold_lift in Hf. unfold typed_true, strict_bool_val in Hf. simpl in Hf. discriminate.
  + eapply semax_post_flipped; [apply semax_skip | ..]; simpl; intros; try apply andp_left2; auto;
      try apply FF_left; apply andp_left1; auto.
- eapply semax_pre; [| apply semax_break]. simpl. intros; apply andp_left2; auto.
Qed.


Lemma call_inv_cold : forall a k sv ipc opc oc dl, call_inv a k sv ipc opc oc dl -> cold01 (c3_fs k).
Proof.
intros a k sv ipc opc oc dl H.
destruct H as (_&_&_&_&_&_&_&_&_&_&_&_&Hc&_). unfold c_core in Hc. unfold cold01. tauto.
Qed.

(* the facts of the invariant at zdss_load *)
Lemma load_facts : forall stable obuf sout k sv,
  c_core stable obuf sout k sv -> sf_stage (c3_s k) = zdss_load ->
  exists E st, fs_expected (c3_fs k) = vlong E /\ sf_inPos (c3_s k) = vlong (fp_inpos (sv_fp sv)) /\
    0 <= fp_inpos (sv_fp sv) < E /\ E < 2 ^ 32 /\
    fs_stage (c3_fs k) = Vint (Int.repr st) /\ 0 <= st <= 7 /\
    (st = ds_skipFrame <-> is_skip (sv_fp sv) = true) /\
    (is_skip (sv_fp sv) = false -> E <= sf_inSize (c3_s k)) /\
    (exists ts, c3_tabs k = TInit (dd_ox (sv_dd sv)) ts) /\ isptr (sf_inBuff (c3_s k)).
Proof.
intros stable obuf sout k sv Hc Hst.
unfold c_core in Hc. destruct Hc as (_ & _ & _ & Hc).
assert (H1: (sf_stage (c3_s k) =? zdss_init) = false) by (rewrite Hst; reflexivity).
assert (H2: (sf_stage (c3_s k) =? zdss_loadHeader) = false) by (rewrite Hst; reflexivity).
rewrite H1, H2 in Hc. clear H1 H2.
destruct Hc as (_ & Hfr & Hring & _ & Hld & _).
specialize (Hld Hst). destruct Hld as (_ & Hcomp & Hraw & _ & Hpos & _).
destruct Hring as (_ & Hib & Hin & _).
unfold c_frame in Hfr. destruct Hfr as (_ & _ & _ & _ & _ & Hf).
destruct (sv_fp sv) as [|hb|hdr got|hdr z] eqn:Hfp; try contradiction.
- destruct Hf as (_ & Hts & _ & Hgot & H32 & Hif).
  simpl in Hcomp. rewrite Hcomp in Hif. destruct Hif as [Hstg Hexp]. apply Z.eqb_neq in Hcomp.
  exists (le_field hdr 4 4), ds_skipFrame. simpl fp_inpos. simpl is_skip.
  unfold ds_skipFrame in *.
  repeat split; auto; try lia; try discriminate.
- destruct Hf as (_ & _ & Hbsm0 & Hbsm & _ & _ & _ & _ & _ & Hts & Hph & _ & _ & _ & _ & Hphx & _).
  assert (Hts': exists ts, c3_tabs k = TInit (dd_ox (sv_dd sv)) ts) by (destruct Hts as (ts & ? & _); exists ts; auto).
  clear Hts.
  simpl fp_inpos. simpl is_skip. simpl fp_bsm in Hin. simpl fp_complete in Hcomp. simpl fp_rawbody in Hraw.
  unfold phase_fields in Hph.
  destruct (zp_ph z) as [|bh| |] eqn:Hz.
  + destruct Hph as [Hstg Hexp].
    exists ZSTD_blockHeaderSize, ds_decodeBlockHeader.
    unfold ZSTD_blockHeaderSize, ds_decodeBlockHeader, ds_skipFrame in *.
    repeat split; eauto; try rep_lia; try discriminate.
  + destruct Hph as (c & Hc & Hstg & _ & _ & Hexp).
    destruct Hphx as (_ & _ & c' & Hc' & Hcb & Hgl & _).
    rewrite Hc in Hc'. inversion Hc'. subst c'.
    assert (Hr: (bp_type (block_props_of bh) =? 0) = false) by exact Hraw. rewrite Hr in Hexp.
    exists c, (if bp_last (block_props_of bh) =? 1 then ds_decompressLastBlock else ds_decompressBlock).
    unfold ZSTD_BLOCKSIZE_MAX, ds_decompressLastBlock, ds_decompressBlock, ds_skipFrame in *.
    destruct (bp_last (block_props_of bh) =? 1);
    repeat split; eauto; try rep_lia; try discriminate.
  + destruct Hph as [Hstg Hexp]. destruct Hphx as [Hgl _].
    exists 4, ds_checkChecksum.
    unfold ds_checkChecksum, ds_skipFrame in *.
    repeat split; eauto; try rep_lia; try discriminate.
  + discriminate.
Qed.

(* ---------- the view after loading u (not the whole unit) ---------- *)

Definition fp_load (fp: fprog) (u: list Z) : fprog :=
  match fp with
  | FP_skip hdr got => FP_skip hdr (got + Zlength u)
  | FP_zstd hdr z => FP_zstd hdr (zp_set_got z (zp_got z ++ u))
  | x => x
  end.

Definition sv_load (sv: sview) (u: list Z) : sview :=
  {| sv_fp := fp_load (sv_fp sv) u; sv_pend := sv_pend sv; sv_ahead := sv_ahead sv; sv_lay := sv_lay sv;
     sv_dd := sv_dd sv |}.

(* the stream fields with inPos and the stream buffer's cells changed *)
Definition s_load (s: sfields) (inpos: Z) (ring: list val) : sfields :=
  {| sf_stage := sf_stage s; sf_inBuff := sf_inBuff s; sf_inSize := sf_inSize s; sf_inPos := vlong inpos;
     sf_outBuff := sf_outBuff s; sf_outSize := sf_outSize s; sf_outStart := sf_outStart s;
     sf_outEnd := sf_outEnd s; sf_lhSize := sf_lhSize s; sf_hostage := sf_hostage s; sf_nfp := sf_nfp s;
     sf_expOut := sf_expOut s; sf_hbuf := sf_hbuf s; sf_over := sf_over s; sf_ring := ring; sf_mem := sf_mem s; sf_held := sf_held s |}.

Definition ring_load (fp: fprog) (ring: list val) (P: Z) (ibs: list Z) (ipc L: Z) : list val :=
  if is_skip fp then ring else copy_cells ring P (zbytes ibs) ipc L.

Definition k_load (k: cst3) (inpos: Z) (ring: list val) : cst3 := c3_with_s k (s_load (c3_s k) inpos ring).

(* the statements after the computation of loadedSize, and the cases after zdss_load *)
Definition ld_rest : statement :=
  match ds_case_load with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ r))) => r | _ => Sskip end.
Definition ld_tail : statement :=
  seq_of_labeled_statement (LScons (Some 4) ds_case_flush (LScons None ds_case_default LSnil)).

(* the state once loadedSize = L is known (the cells of the stream buffer as loaded) *)
Definition ld_join (DENT: dent_pred) (TABS: tabs_pred) (a: dsa) (k: cst3) (sv: sview) (ipc opc: Z)
    (oc: list val) (dl: list Z) (E L: Z) : environ -> mpred :=
  let w := {| w_smw := 1; w_k := k; w_sv := sv; w_ipc := ipc; w_opc := opc; w_oc := oc; w_dl := dl |} in
  PROPx [] (LOCALx (temp _loadedSize (vlong L) :: temp _toLoad__1 (vlong (E - fp_inpos (sv_fp sv))) ::
                    temp _neededInSize__1 (vlong E) :: ds_LI_L a w)
           (SEPx (ds_LI_S DENT TABS a w))).

(* ---------- facts for load_partial_inv ---------- *)

Lemma vlong_eq : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> vlong x = vlong y -> x = y.
Proof.
intros x y Hx Hy H. unfold vlong in H. assert (H1: Int64.repr x = Int64.repr y) by congruence.
apply (f_equal Int64.unsigned) in H1. rewrite !Int64.unsigned_repr in H1 by rep_lia. exact H1.
Qed.
Lemma sublist_skip_eq : forall {A} (l1 l2: list A) n i j, 0 <= n <= i ->
  skipn (Z.to_nat n) l1 = skipn (Z.to_nat n) l2 -> sublist i j l1 = sublist i j l2.
Proof.
intros A l1 l2 n i j Hn H. unfold sublist. rewrite !skipn_firstn_comm.
replace (Z.to_nat i) with (Z.to_nat i - Z.to_nat n + Z.to_nat n)%nat by lia.
rewrite <- !skipn_skipn, H. reflexivity.
Qed.

Lemma skipn_copy_cells : forall (ring cs: list val) P os L,
  0 <= P <= Zlength ring -> 0 <= L -> 0 <= os -> os + L <= Zlength cs ->
  skipn (Z.to_nat (P + L)) (copy_cells ring P cs os L) = skipn (Z.to_nat (P + L)) ring.
Proof.
intros ring cs P os L HP HL Hos Hcs. unfold copy_cells. rewrite app_assoc, skipn_app.
assert (HX: Zlength (sublist 0 P ring ++ sublist os (os + L) cs) = P + L)
  by (rewrite Zlength_app, !Zlength_sublist by lia; lia).
rewrite Zlength_correct in HX.
rewrite skipn_all2 by lia.
replace (Z.to_nat (P + L) - length (sublist 0 P ring ++ sublist os (os + L) cs))%nat with O by lia.
cbn [app skipn]. unfold sublist. rewrite firstn_all2. reflexivity.
rewrite Zlength_correct. lia.
Qed.

Lemma sublist_copy_cells_pre : forall (ring cs: list val) P os L,
  0 <= P <= Zlength ring -> 0 <= L -> 0 <= os -> os + L <= Zlength cs ->
  sublist 0 (P + L) (copy_cells ring P cs os L) = sublist 0 P ring ++ sublist os (os + L) cs.
Proof.
intros ring cs P os L HP HL Hos Hcs. unfold copy_cells.
assert (HX: Zlength (sublist 0 P ring ++ sublist os (os + L) cs) = P + L)
  by (rewrite Zlength_app, !Zlength_sublist by lia; lia).
rewrite app_assoc, sublist_app1 by (try rewrite HX; lia).
apply sublist_same; lia.
Qed.

Lemma c_ring_load : forall stable obuf sout s fp pend l inpos ring' u,
  sublist (sf_inSize s) (sf_inSize s + sf_outSize s) ring' =
    sublist (sf_inSize s) (sf_inSize s + sf_outSize s) (sf_ring s) ->
  c_ring stable obuf sout s fp pend l -> c_ring stable obuf sout (s_load s inpos ring') (fp_load fp u) pend l.
Proof.
intros stable obuf sout s fp pend l inpos ring' u Heq H.
destruct fp as [|hb|hdr got|hdr z]; unfold c_ring in *;
  cbn [s_load sf_inBuff sf_inSize sf_outSize sf_outStart sf_outEnd sf_ring sf_outBuff fp_load fp_bsm
       fp_content fp_fcs fp_ws zp_set_got zp_h zp_out] in *; rewrite Heq; exact H.
Qed.

Lemma fr_load : forall fs tabs fp l dd u E,
  c_frame fs tabs fp l dd -> fs_expected fs = vlong E -> 0 <= E < 2 ^ 32 ->
  fp_complete fp = false -> fp_rawbody fp = false -> fp_inpos fp + Zlength u < E -> bytes_ok u ->
  c_frame fs tabs (fp_load fp u) l dd /\ fp_inpos (fp_load fp u) = fp_inpos fp + Zlength u /\
  fp_content (fp_load fp u) = fp_content fp /\ fp_ws (fp_load fp u) = fp_ws fp /\
  fp_complete (fp_load fp u) = false /\ fp_rawbody (fp_load fp u) = false /\
  (forall md sel cd fb, MF3 -> cur_rel md sel cd fb fp -> cur_rel md sel cd (fb ++ u) (fp_load fp u)) /\
  (is_skip fp = true -> fp_loaded (fp_load fp u) = nil) /\
  (is_skip fp = false -> fp_loaded (fp_load fp u) = fp_loaded fp ++ u /\
     Zlength (fp_loaded fp) = fp_inpos fp /\ E <= Z.max (fp_bsm fp) 4).
Proof.
intros fs tabs fp l dd u E Hf HE HE0 Hc Hr Hlt Hu. pose proof (Zlength_nonneg u) as Hu0.
destruct fp as [|hb|hdr got|hdr z].
- destruct Hf as (_&_&_&_&_&[]).
- destruct Hf as (_&_&_&_&_&[]).
- destruct Hf as (Hif&Hcold&Hdid&Hpcs&Hlay&Hl&Hts&Hh&Hgot&Hsz&Hst).
  cbn [fp_complete] in Hc. rewrite Hc in Hst. destruct Hst as [Hst Hexp].
  rewrite HE in Hexp. change (Vlong (Int64.repr (le_field hdr 4 4))) with (vlong (le_field hdr 4 4)) in Hexp.
  apply vlong_eq in Hexp; [| lia | lia]. subst E.
  cbn [fp_inpos] in Hlt. apply Z.eqb_neq in Hc.
  split.
  { unfold c_frame; cbn [fp_load].
    do 5 (split; [assumption|]). split; [exact Hl|]. split; [exact Hts|]. split; [exact Hh|].
    split; [lia|]. split; [exact Hsz|].
    rewrite (proj2 (Z.eqb_neq _ _)) by lia. split; [exact Hst|exact HE]. }
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [cbn [fp_complete fp_load]; apply Z.eqb_neq; lia|]. split; [reflexivity|].
  split; [intros md sel cd fb M Hcur; exact (mf_skip_more M md sel cd fb hdr got u Hcur ltac:(lia))|].
  split; [reflexivity|intros H; discriminate].
- destruct z as [h dm bsm ign bl ts out ph got].
  destruct Hf as (Hif&Hcold&Hdid&Hpcs&Hlay&Hz).
  cbv beta iota zeta delta [zp_h zp_dm zp_bsm zp_ign zp_bl zp_ts zp_out zp_ph zp_got zp_with] in Hz.
  destruct Hz as (HfT&HfP&Hbsm0&Hbsm1&Hws&Hws2&Hcs&Hck&Hdm&Htabs&Hph&Hdec&Hval&Hxxh&Hbout&Hphase&Hbgot).
  cbn [fp_inpos zp_got] in Hlt.
  assert (Hbg: bytes_ok (got ++ u)) by (apply Forall_app; split; auto).
  destruct ph as [|bh| |].
  + (* block header *)
    destruct Hph as [Hst Hexp]. rewrite HE in Hexp.
    change (Vlong (Int64.repr ZSTD_blockHeaderSize)) with (vlong 3) in Hexp.
    apply vlong_eq in Hexp; [| lia | lia]. subst E.
    split.
    { unfold c_frame; cbv beta iota zeta delta [fp_load zp_set_got zp_h zp_dm zp_bsm zp_ign zp_bl zp_ts zp_out zp_ph zp_got zp_with].
      do 5 (split; [assumption|]). do 10 (split; [first [assumption | split; assumption]|]).
      split; [split; assumption|]. do 4 (split; [assumption|]).
      split; [|exact Hbg]. rewrite Zlength_app. unfold ZSTD_blockHeaderSize. lia. }
    split; [cbn [fp_inpos fp_load zp_set_got zp_with zp_got]; apply Zlength_app|]. do 4 (split; [reflexivity|]).
    split.
    { intros md sel cd fb M Hcur. unfold cur_rel in Hcur |- *.
      cbv beta iota zeta delta [fp_load zp_set_got zp_h zp_dm zp_bsm zp_ign zp_bl zp_ts zp_out zp_ph zp_got zp_with] in Hcur |- *.
      destruct Hcur as (Hg&Hhs&Hft&Hfd&Hdi&Hbsq&Hign&outc&last&Hbp&Hfb&Hp).
      do 7 (split; [assumption|]). exists outc, last. split; [exact Hbp|].
      split; [rewrite Hfb, <- !app_assoc; reflexivity|].
      destruct Hp as (Hp1&Hp2&Hp3). split; [exact Hp1|]. split; [exact Hp2|].
      rewrite Zlength_app. unfold ZSTD_blockHeaderSize. lia. }
    split; [intros H; discriminate|]. intros _. split; [reflexivity|]. split; [reflexivity|].
    cbn [fp_bsm zp_bsm]. lia.
  + (* block body (not raw) *)
    cbn [fp_rawbody zp_ph] in Hr.
    destruct Hph as (c&Hc1&Hst&HbT&Hrle&Hexp). rewrite Hr in Hexp. rewrite HE in Hexp.
    change (Vlong (Int64.repr c)) with (vlong c) in Hexp.
    destruct Hphase as (Hbh&Hbbh&c'&Hc'&Hc0&Hcg&Hb3). rewrite Hc1 in Hc'. inversion Hc'; subst c'.
    apply vlong_eq in Hexp; [| lia | unfold ZSTD_BLOCKSIZE_MAX in Hbsm1; lia]. subst E.
    split.
    { unfold c_frame; cbv beta iota zeta delta [fp_load zp_set_got zp_h zp_dm zp_bsm zp_ign zp_bl zp_ts zp_out zp_ph zp_got zp_with].
      do 5 (split; [assumption|]). do 10 (split; [first [assumption | split; assumption]|]).
      split. { exists c. rewrite Hr. auto. }
      do 4 (split; [assumption|]).
      split; [|exact Hbg]. split; [exact Hbh|]. split; [exact Hbbh|]. exists c.
      rewrite Zlength_app. split; [exact Hc1|]. split; [lia|]. split; [lia|exact Hb3]. }
    split; [cbn [fp_inpos fp_load zp_set_got zp_with zp_got]; apply Zlength_app|]. do 3 (split; [reflexivity|]). split; [exact Hr|].
    split.
    { intros md sel cd fb M Hcur. unfold cur_rel in Hcur |- *.
      cbv beta iota zeta delta [fp_load zp_set_got zp_h zp_dm zp_bsm zp_ign zp_bl zp_ts zp_out zp_ph zp_got zp_with] in Hcur |- *.
      destruct Hcur as (Hg&Hhs&Hft&Hfd&Hdi&Hbsq&Hign&outc&last&Hbp&Hfb&Hp).
      do 7 (split; [assumption|]). exists outc, last. split; [exact Hbp|].
      split; [rewrite Hfb, <- !app_assoc; reflexivity|].
      destruct Hp as (Hp1&Hp2&c2&Hc2&Hc20&Hc2g&Hout). rewrite Hc1 in Hc2. inversion Hc2; subst c2.
      split; [exact Hp1|]. split; [exact Hp2|]. exists c. rewrite Hr in Hout |- *.
      rewrite Zlength_app. split; [exact Hc1|]. split; [lia|]. split; [lia|exact Hout]. }
    split; [intros H; discriminate|]. intros _. split; [reflexivity|]. split; [reflexivity|].
    cbn [fp_bsm zp_bsm]. lia.
  + (* checksum *)
    destruct Hph as [Hst Hexp]. rewrite HE in Hexp.
    change (Vlong (Int64.repr 4)) with (vlong 4) in Hexp.
    apply vlong_eq in Hexp; [| lia | lia]. subst E.
    destruct Hphase as [Hg4 Hck1].
    split.
    { unfold c_frame; cbv beta iota zeta delta [fp_load zp_set_got zp_h zp_dm zp_bsm zp_ign zp_bl zp_ts zp_out zp_ph zp_got zp_with].
      do 5 (split; [assumption|]). do 10 (split; [first [assumption | split; assumption]|]).
      split; [split; assumption|]. do 4 (split; [assumption|]).
      split; [|exact Hbg]. rewrite Zlength_app. split; [lia|exact Hck1]. }
    split; [cbn [fp_inpos fp_load zp_set_got zp_with zp_got]; apply Zlength_app|]. do 4 (split; [reflexivity|]).
    split.
    { intros md sel cd fb M Hcur. unfold cur_rel in Hcur |- *.
      cbv beta iota zeta delta [fp_load zp_set_got zp_h zp_dm zp_bsm zp_ign zp_bl zp_ts zp_out zp_ph zp_got zp_with] in Hcur |- *.
      destruct Hcur as (Hg&Hhs&Hft&Hfd&Hdi&Hbsq&Hign&outc&last&Hbp&Hfb&Hp).
      do 7 (split; [assumption|]). exists outc, last. split; [exact Hbp|].
      split; [rewrite Hfb, <- !app_assoc; reflexivity|].
      destruct Hp as (Hp1&Hp2&Hp3&Hp4&Hp5). do 4 (split; [assumption|]).
      rewrite Zlength_app. lia. }
    split; [intros H; discriminate|]. intros _. split; [reflexivity|]. split; [reflexivity|].
    cbn [fp_bsm zp_bsm]. lia.
  + (* end: complete *)
    discriminate Hc.
Qed.

End CM_L3Base_2.

Ltac nfp_carry H Hst := destruct H as [Hx|[Hx|[Hx|Hx]]];
  [ left; lia | right; left; first [exact Hx | lia] | right; right; left; exact Hx
  | exfalso; rewrite Hst in Hx; unfold zdss_load, zdss_init, zdss_loadHeader in Hx;
    destruct Hx as [Hx|[Hx _]]; lia ].

Section CM_L3Base_3.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.

(* not enough input for the unit: all of it is loaded, someMoreWork := 0 *)
Lemma load_partial_inv : forall a k0 sv ipc opc oc dl E L,
  MF3 -> dsa_ok a -> call_inv a k0 sv ipc opc oc dl -> sf_stage (c3_s k0) = zdss_load ->
  fs_expected (c3_fs k0) = vlong E -> 0 <= E < 2 ^ 32 ->
  L = Z.min (E - fp_inpos (sv_fp sv)) (a_isz a - ipc) -> L < E - fp_inpos (sv_fp sv) ->
  call_inv a (k_load k0 (fp_inpos (sv_fp sv) + L)
                (ring_load (sv_fp sv) (sf_ring (c3_s k0)) (fp_inpos (sv_fp sv)) (a_ibs a) ipc L))
           (sv_load sv (sublist ipc (ipc + L) (a_ibs a))) (ipc + L) opc oc dl.
Proof.
intros a k0 sv ipc opc oc dl E L HMF Ha Hinv Hstage HE HE0 HL Hlt.
destruct Hinv as (Hipc & Hopc & Hoc & Hoc0 & Hdl & Hdl2 & Hbdl & Hbase & Hbin & Hnfp & Hnfp2 & Hinit &
                  Hcore & Hdd & Hstout & Hahead & Hbsm & Hrel & Hlh & Hsah & Hexp & HTT).
destruct Ha as (_&_&_&_&_&_&_&_&_&_&_&_&Hipos&Hisz&Hzl&Hbibs&_&_).
assert (HL': L = a_isz a - ipc) by (destruct (Z.min_spec (E - fp_inpos (sv_fp sv)) (a_isz a - ipc)); lia).
cbv beta zeta delta [c_core] in Hcore.
destruct Hcore as (Hhost & Hcold & Hsz & Hrest).
rewrite Hstage in Hrest.
replace (zdss_load =? zdss_init) with false in Hrest by reflexivity.
replace (zdss_load =? zdss_loadHeader) with false in Hrest by reflexivity.
destruct Hrest as (_ & Hfr & Hring & Hstst & Hld & _ & _).
destruct (Hld eq_refl) as (Hpend & Hncomp & Hnraw & Hoso & Hinpos & Hpre).
assert (Hah: sf_hostage (c3_s k0) = Vint (Int.repr 0) /\ sv_ahead sv = nil).
{ destruct Hhost as [[Hs _]|[Hh|(_&_&_&_&_&Hs)]]; auto; rewrite Hstage in Hs.
  - unfold zdss_load, zdss_init in Hs; lia.
  - unfold zdss_load, zdss_init, zdss_read, zdss_flush in Hs; lia. }
destruct Hah as [Hh0 Hah].
set (u := sublist ipc (ipc + L) (a_ibs a)).
assert (Hu: Zlength u = L) by (unfold u; rewrite Zlength_sublist; lia).
assert (Hbu: bytes_ok u) by (unfold u, bytes_ok in *; apply Forall_sublist; auto).
destruct (fr_load _ _ _ _ _ u E Hfr HE HE0 Hncomp Hnraw ltac:(lia) Hbu)
  as (Hfr' & Hip' & Hcnt' & Hws' & Hcomp' & Hraw' & Hcur' & Hsk1 & Hsk2).
set (ring' := ring_load (sv_fp sv) (sf_ring (c3_s k0)) (fp_inpos (sv_fp sv)) (a_ibs a) ipc L).
assert (Hring2: sublist (sf_inSize (c3_s k0)) (sf_inSize (c3_s k0) + sf_outSize (c3_s k0)) ring' =
                sublist (sf_inSize (c3_s k0)) (sf_inSize (c3_s k0) + sf_outSize (c3_s k0)) (sf_ring (c3_s k0)) /\
                sublist 0 (Zlength (fp_loaded (fp_load (sv_fp sv) u))) ring' = zbytes (fp_loaded (fp_load (sv_fp sv) u))).
{ unfold ring', ring_load. destruct (is_skip (sv_fp sv)) eqn:Hsk.
  - rewrite (Hsk1 eq_refl). split; reflexivity.
  - destruct (Hsk2 eq_refl) as (Hld' & HzP & HEb).
    destruct Hring as (_ & _ & Hin & _).
    pose proof (Zlength_nonneg (fp_loaded (sv_fp sv))).
    assert (HPr: fp_inpos (sv_fp sv) <= Zlength (sf_ring (c3_s k0))).
    { destruct (Z_le_gt_dec (fp_inpos (sv_fp sv)) (Zlength (sf_ring (c3_s k0)))) as [?|Hgt]; auto.
      rewrite sublist_same_gen in Hpre by lia. apply (f_equal (@Zlength val)) in Hpre.
      rewrite Zlength_map in Hpre. lia. }
    assert (Hzl': Zlength (zbytes (a_ibs a)) = a_isz a) by (rewrite Zlength_map; lia).
    split.
    + apply sublist_skip_eq with (n := fp_inpos (sv_fp sv) + L); [lia|].
      apply skipn_copy_cells; lia.
    + rewrite Hld', Zlength_app, HzP, Hu.
      rewrite sublist_copy_cells_pre by lia.
      rewrite <- HzP, Hpre, sublist_map, map_app. reflexivity. }
destruct Hring2 as [Hring2 Hpre'].
assert (Hsin: a_sin a ++ sublist (a_ipos a) (ipc + L) (a_ibs a) ++ sv_ahead sv =
              (a_sin a ++ sublist (a_ipos a) ipc (a_ibs a) ++ sv_ahead sv) ++ u).
{ rewrite Hah, !app_nil_r. rewrite (sublist_split (a_ipos a) ipc (ipc + L)) by lia.
  rewrite !app_assoc. reflexivity. }
assert (Hcore': c_core (dc_stable (a_st a)) (Some (a_ob a, a_osz a)) (ss_out (dc_ss (a_st a)) ++ dl)
                  (k_load k0 (fp_inpos (sv_fp sv) + L) ring') (sv_load sv u)).
{ cbv beta zeta delta [c_core]. unfold k_load, c3_with_s, sv_load.
  cbn [c3_s c3_fs c3_tabs c3_par sv_fp sv_pend sv_ahead sv_lay sv_dd].
  cbn [s_load sf_stage sf_hostage sf_inSize sf_outSize sf_inPos sf_outStart sf_outEnd sf_ring].
  rewrite Hstage.
  replace (zdss_load =? zdss_init) with false by reflexivity.
  replace (zdss_load =? zdss_loadHeader) with false by reflexivity.
  split; [right; left; split; [exact Hh0|exact Hah]|].
  split; [exact Hcold|]. split; [exact Hsz|].
  split; [right; left; reflexivity|].
  split; [exact Hfr'|].
  split; [exact (c_ring_load _ _ _ _ _ _ _ (fp_inpos (sv_fp sv) + L) ring' u Hring2 Hring)|].
  split; [exact Hstst|].
  split.
  { intros _. rewrite Hpend. split; [reflexivity|]. split; [exact Hcomp'|]. split; [exact Hraw'|].
    split; [exact Hoso|]. split; [rewrite Hip', Hu; reflexivity|exact Hpre']. }
  split; [intros H; contradiction H; reflexivity|].
  intros H. unfold zdss_load, zdss_read in H; lia. }
assert (Hhist': hist_ok (dc_stable (a_st a)) k0 sv ->
                hist_ok (dc_stable (a_st a)) (k_load k0 (fp_inpos (sv_fp sv) + L) ring') (sv_load sv u)).
{ unfold hist_ok, k_load, c3_with_s, sv_load.
  cbn [c3_s sv_fp sv_lay s_load sf_stage sf_inSize sf_outSize sf_ring].
  assert (Hfh: fp_hist (fp_load (sv_fp sv) u) (sv_lay sv) = fp_hist (sv_fp sv) (sv_lay sv))
    by (destruct (sv_fp sv); reflexivity).
  rewrite Hring2, Hcnt', Hws', Hfh. auto. }
unfold call_inv. cbv zeta.
change (sv_ahead (sv_load sv u)) with (sv_ahead sv).
change (sv_pend (sv_load sv u)) with (sv_pend sv).
change (sv_fp (sv_load sv u)) with (fp_load (sv_fp sv) u).
change (sf_nfp (c3_s (k_load k0 (fp_inpos (sv_fp sv) + L) ring'))) with (sf_nfp (c3_s k0)).
change (c3_par (k_load k0 (fp_inpos (sv_fp sv) + L) ring')) with (c3_par k0).
rewrite Hsin.
split; [lia|]. split; [exact Hopc|]. split; [exact Hoc|]. split; [exact Hoc0|]. split; [exact Hdl|].
split; [exact Hdl2|]. split; [exact Hbdl|]. split; [exact Hbase|].
split; [exact Hbin|]. split; [exact Hnfp|].
split; [nfp_carry Hnfp2 Hstage|]. split; [exact Hinit|].
split; [exact Hcore'|].
split; [exact Hdd|].
split; [exact Hstout|].
split; [rewrite Hah; intros H; contradiction H; reflexivity|].
split; [exact Hbsm|].
split; [|unfold k_load, c3_with_s; cbn [c3_s s_load sf_stage sf_expOut sf_hostage]; rewrite Hstage;
         split; [intros Hx; unfold zdss_load, zdss_loadHeader in Hx; lia|];
         split; [exact Hsah|]; split; [intros Hx _; apply Hexp; [exact Hx|rewrite Hstage; unfold zdss_load, zdss_init; lia]|];
         intros Hx; unfold zdss_load, zdss_flush in Hx; lia].
destruct Hrel as [Hd|(cd & Hm & Hcd & Hh)].
- left. exact (mf_dead_app HMF _ _ u Hd).
- right. exists cd. split; [|split; [|exact (Hhist' Hh)]].
  + destruct Hm as (dsin & fb & recs & Hs & Hser & Hc & Hcr & Ho).
    exists dsin, (fb ++ u), recs.
    split; [rewrite Hs, app_assoc; reflexivity|]. split; [exact Hser|]. split; [exact Hc|].
    split; [exact (Hcur' _ _ _ fb HMF Hcr)|]. cbn [sv_fp sv_pend sv_load]. rewrite Hcnt'. exact Ho.
  + assert (Hn: next_cd (sm_of (a_st a)) (fp_load (sv_fp sv) u) cd = next_cd (sm_of (a_st a)) (sv_fp sv) cd) by (destruct (sv_fp sv); reflexivity).
    cbn [sv_fp sv_load]. rewrite Hn. exact Hcd.
Qed.

(* R4: the loop stops at zdss_load when the input is all read (exit_ok) *)
Lemma load_partial_exit : forall a k0 sv ipc opc oc dl L ring,
  call_inv a k0 sv ipc opc oc dl -> sf_stage (c3_s k0) = zdss_load -> L = a_isz a - ipc ->
  exit_ok a {| w_smw := 0; w_k := k_load k0 (fp_inpos (sv_fp sv) + L) ring;
               w_sv := sv_load sv (sublist ipc (ipc + L) (a_ibs a)); w_ipc := ipc + L; w_opc := opc;
               w_oc := oc; w_dl := dl |}.
Proof.
intros a k0 sv ipc opc oc dl L ring Hi Hs HL _.
destruct Hi as (H1&H2&_&_&_&_&_&_&_&Hn1&Hn2&_).
unfold exit_ok, k_load, c3_with_s; cbn [w_k w_sv w_ipc w_opc w_smw c3_s s_load sf_stage sf_nfp]. rewrite Hs.
split; [unfold zdss_load, zdss_loadHeader; lia|].
split; [intros _; lia|].
split; [intros Hx; unfold zdss_load, zdss_flush in Hx; lia|].
split.
- intros Hip Hop. destruct Hn2 as [Hx|[Hx|[Hx|Hx]]]; [lia|lia|exact Hx|].
  rewrite Hs in Hx. unfold zdss_load, zdss_init, zdss_loadHeader in Hx. destruct Hx as [Hx|[Hx _]]; lia.
- intros Hx; unfold zdss_load, zdss_init in Hx; lia.
Qed.

End CM_L3Base_3.
