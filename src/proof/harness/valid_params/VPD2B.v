(* valid_params main, segment D2, the end of the loop body (D2_tail): ZSTD_isError(r), the error
   assert and break, the stalled counter, and on r == 0 the at_end loop and the end of the series. *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.harness.valid_params.VPD2Defs.

Local Notation HCS := Zstd.proof.harness.valid_params.HOK_valid_params.CompSpecs.
Local Notation ZCS := Zstd.proof.zstd.Base.CompSpecs.
Local Notation tout := (Tstruct _ZSTD_outBuffer_s noattr).
Local Notation tin := (Tstruct _ZSTD_inBuffer_s noattr).

(* main's at_end loop after k frames of sr (positions relative to base) *)
Definition D2_at (fs: list winfo) (base ipos got: Z) (k: Z) : bool :=
  existsb (fun f => andb (wi_start f + wi_size f - base =? ipos) (got =? wi_cstart f + wi_csize f)) (firstn (Z.to_nat k) fs).

Lemma D2_at_step fs base ipos got k : 0 <= k < Zlength fs ->
  D2_at fs base ipos got (k + 1) =
  orb (D2_at fs base ipos got k) (andb (wi_start (Znth k fs) + wi_size (Znth k fs) - base =? ipos)
                                       (got =? wi_cstart (Znth k fs) + wi_csize (Znth k fs))).
Proof.
  intros. unfold D2_at. rewrite <- !sublist_firstn.
  rewrite (sublist_split 0 k (k + 1)) by lia. rewrite sublist_len_1 by lia.
  rewrite existsb_app. simpl. rewrite orb_false_r. reflexivity.
Qed.

Lemma D2_at_all fs base ipos got : D2_at fs base ipos got (Zlength fs) =
  existsb (fun f => andb (wi_start f + wi_size f - base =? ipos) (got =? wi_cstart f + wi_csize f)) fs.
Proof. unfold D2_at. rewrite ZtoNat_Zlength, firstn_all. reflexivity. Qed.

Lemma D2_at_0 fs base ipos got : D2_at fs base ipos got 0 = false.
Proof. reflexivity. Qed.

Lemma D2_EQ64 a b : 0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int64.eq (Int64.repr a) (Int64.repr b) = (a =? b).
Proof.
  intros Ha Hb. unfold Int64.eq. rewrite !Int64.unsigned_repr by lia.
  destruct (zeq a b); symmetry; [apply Z.eqb_eq | apply Z.eqb_neq]; auto.
Qed.

Section Seg.
Context {Espec: OracleKind}.
Variable DC : globals -> val -> dctx_st -> mpred.
Variable DD : globals -> val -> ddict_st -> mpred.
Variable WG : globals -> mpred.
Variable WDS : wdict -> reptype t_wstate -> Prop.
Local Notation Delta := (VP_Delta DC DD WG WDS).

Lemma D2_tail_ok (gv: globals) (vz vi vo: val) (wsr ws': wseries) (p: dparams) (base wlim: Z) (src dctx: val)
    (calls ip2 got2 stalled: Z) (ib: val) (ilen ipos': Z) (ob: val) (osz opos' r: Z) (st': dctx_st)
    (R0: ret_assert) :
  D2_M2_ok wsr ws' p base wlim calls ip2 got2 stalled ilen ipos' osz opos' r st' ->
  semax Delta
    (D2_M2 DC WG gv vz vi vo wsr ws' base (D2_wb wsr wlim) src dctx calls ip2 got2 stalled ib ilen ipos' ob osz opos' r st')
    D2_tail
    (D2_RA DC WG gv vz vi vo wsr ws' p base (D2_wb wsr wlim) src dctx R0).
Proof.
intros HM. destruct R0 as [Rn Rb Rc Rr].
unfold D2_M2, D2_L, D2_tail, D2_RA, overridePost, loop1_ret_assert, VP_Delta. simplify_func_tycontext. abbreviate_semax.
destruct HM as (Hd & Hcalls & Hstl & Hip2 & Hgot2 & Hipos' & Hilen & Hopos' & Hosz & Hr & Hpar & Hdict & Hset & Hbl
  & Hstab & Herr & Hin & Hout & Hs1 & Hs2 & Hwerr & Hr0).
pose proof Hd as (Hw & Hc & Hbs' & Hbase & HN0 & Hbok & Hcok & HN & HC & Hnf & Hwf & Hfb & Hwl & _).
assert (HNb: Zlength (ws_bytes ws') <= 2 ^ 19).
{ rewrite Hbs'. destruct (Z_le_gt_dec base (Zlength (ws_bytes wsr))).
  - rewrite Zlength_sublist by lia; lia.
  - rewrite sublist_nil_gen by lia. rewrite Zlength_nil; lia. }
forward_call r.
forward_if.
{ match goal with H: Int.repr (if is_error_code r then 1 else 0) <> Int.zero |- _ => rename H into Herr' end.
  destruct (is_error_code r) eqn:Er; [|contradiction Herr'; reflexivity]. clear Herr'.
  assert (He: r = 2 ^ 64 - error_of r) by (unfold error_of; rewrite Er; lia).
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
    forward_if (EX v9: int, PROPx ((v9 = Int.zero -> D2_wb wsr wlim = true /\ error_of r <> 64) :: P)
                 (LOCALx (temp _x_valid_params__t'55 (Vint v9) :: L) (SEPx R)))
  end.
  { forward. Exists Int.one. entailer!. exfalso; apply Int.one_not_zero; assumption. }
  { forward_call r. forward.
    Exists (if Int.eq (Int.repr (error_of r)) (Int.repr 64) then Int.one else Int.zero). entailer!.
    split.
    { intro X. destruct (D2_wb wsr wlim); [|contradiction H; reflexivity].
      split; auto. intro E. rewrite E, Int.eq_true in X. exfalso; apply Int.one_not_zero; exact X. }
    destruct (Int.eq _ _); reflexivity. }
  Intros v9.
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
    forward_if (EX v11: int, PROPx ((v11 <> Int.zero) :: P)
                 (LOCALx (temp _x_valid_params__t'57 (Vint v11) :: L) (SEPx R)))
  end.
  { forward. Exists Int.one. entailer!. }
  { match goal with H: v9 = Int.zero -> _ |- _ => rename H into Hv9 end.
    destruct (Hv9 ltac:(assumption)) as [Hws He64].
    assert (Hst: stall_error_b (error_of r) stalled ipos' ilen opos' osz 0 = true).
    { destruct (Hwerr eq_refl Hws (error_of r) He) as [X | X]; [contradiction | exact X]. }
    forward_call r.
    forward_call (error_of r, stalled, Tsh, vi, ib, ilen, ipos', Tsh, vo, ob, osz, opos', 0).
    { unfold error_of; rewrite Er. unfold is_error_code in Er. apply Z.ltb_lt in Er. rep_lia. }
    forward. Exists Int.one. rewrite Hst. entailer!. }
  Intros v11. forward_call v11. forward.
  unfold D2_brk, VP_SD1. Exists st'. entailer!. }
match goal with H: Int.repr (if is_error_code r then 1 else 0) = Int.zero |- _ => rename H into Herr' end.
destruct (is_error_code r) eqn:Er; [exfalso; inv Herr'|]. clear Herr'.
forward.
match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
  forward_if (PROPx P (LOCALx (temp _x_valid_params__t'61
    (Vint (if andb (ipos' =? 0) (opos' =? 0) then Int.one else Int.zero)) :: L) (SEPx R)))
end.
{ forward. forward. entailer!.
  match goal with H: Int64.repr ipos' = Int64.zero |- _ =>
    apply (f_equal Int64.unsigned) in H; rewrite Int64.unsigned_repr in H by rep_lia;
    change (Int64.unsigned Int64.zero) with 0 in H; subst ipos' end.
  unfold Int64.cmpu. destruct (Z.eqb_spec opos' 0) as [E|E]; [rewrite E; reflexivity|].
  rewrite Int64.eq_false; [reflexivity|]. intro X. apply (f_equal Int64.unsigned) in X.
  rewrite !Int64.unsigned_repr in X by rep_lia. lia. }
{ forward. entailer!.
  destruct (Z.eqb_spec ipos' 0); [subst; contradiction|]. reflexivity. }
set (b0 := andb (ipos' =? 0) (opos' =? 0)).
assert (Hst2: 0 <= ss_stall (dc_ss st') <= (if b0 then stalled + 1 else 0)).
{ subst b0. destruct (Z.eqb_spec ipos' 0), (Z.eqb_spec opos' 0); simpl.
  - specialize (Hs2 eq_refl ltac:(assumption) ltac:(assumption)). lia.
  - rewrite (Hs1 eq_refl ltac:(right; assumption)). lia.
  - rewrite (Hs1 eq_refl ltac:(left; assumption)). lia.
  - rewrite (Hs1 eq_refl ltac:(left; assumption)). lia. }
match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
  forward_if (PROPx P (LOCALx (temp _x_valid_params__t'62
    (Vlong (Int64.repr (if b0 then stalled + 1 else 0))) :: L) (SEPx R)))
end.
{ forward. entailer!. destruct b0; [|contradiction]. try rewrite add64_repr. reflexivity. }
{ forward. entailer!. destruct b0; [discriminate|]. reflexivity. }
forward.
assert (Hsl: 0 <= (if b0 then stalled + 1 else 0) <= calls + 1) by (destruct b0; lia).
assert (Hok2: D2_st_ok p ws' (ws_content wsr) st' ip2 got2 (if b0 then stalled + 1 else 0))
  by (unfold D2_st_ok; auto 20).
clearbody b0.
forward_if.
{ match goal with H: Int64.repr r = Int64.zero |- _ =>
    apply (f_equal Int64.unsigned) in H; rewrite Int64.unsigned_repr in H by rep_lia;
    change (Int64.unsigned Int64.zero) with 0 in H; subst r end.
  specialize (Hr0 eq_refl).
  pose proof Hd as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hat).
  rewrite Hat in Hr0. clear Hat.
  assert (Hnf': 1 <= Zlength (ws_frames wsr) <= 4) by (rewrite Zlength_correct; lia).
  sep_apply (VP_sr_unfold7w wsr (gv _x_valid_params__sr)). Intros.
  unfold VP_Rf, VP_Rnf.
  forward. forward.
  match goal with |- semax _ (PROPx ?P (LOCALx (_ :: _ :: ?L) (SEPx ?R))) _ _ =>
    forward_loop (EX k: Z, PROPx ((0 <= k <= Zlength (ws_frames wsr)) :: P) (LOCALx (temp _k (Vint (Int.repr k)) ::
         temp _at_end (Vint (Int.repr (if D2_at (ws_frames wsr) base ip2 got2 k then 1 else 0))) :: L) (SEPx R)))
     continue: (EX k: Z, PROPx ((0 <= k < Zlength (ws_frames wsr)) :: P) (LOCALx (temp _k (Vint (Int.repr k)) ::
         temp _at_end (Vint (Int.repr (if D2_at (ws_frames wsr) base ip2 got2 (k + 1) then 1 else 0))) :: L) (SEPx R)))
     break: (PROPx P (LOCALx (temp _at_end (Vint (Int.repr 1)) :: L) (SEPx R)))
  end.
  { Exists 0. entailer!. }
  { Intros k. forward. forward_if.
    2: { forward. entailer!.
         try match goal with H: Int.unsigned (Int.repr k) >= _ |- _ => rewrite !Int.unsigned_repr in H by rep_lia end.
         replace k with (Zlength (ws_frames wsr)) by lia. rewrite D2_at_all, Hr0. reflexivity. }
    try match goal with H: Int.unsigned (Int.repr k) < _ |- _ => rewrite !Int.unsigned_repr in H by rep_lia end.
    assert (Fk: forall d, @Znth (reptype t_winfo) d k (map winfo_val (ws_frames wsr) ++
              Zrepeat (winfo_val winfo0) (4 - Zlength (ws_frames wsr))) = winfo_val (Znth k (ws_frames wsr))).
    { intros. rewrite Znth_app1 by (rewrite Zlength_map; lia). rewrite Znth_map by lia. reflexivity. }
    pose proof (proj1 (Forall_Znth _ _) Hfb k ltac:(lia)) as Bf. cbv beta in Bf.
    forward.
    { entailer!. rewrite Fk. exact I. }
    forward.
    { entailer!. rewrite Fk. exact I. }
    rewrite !Fk. unfold winfo_val at 1 2. cbv beta iota zeta.
    set (f := Znth k (ws_frames wsr)) in *.
    match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp _x_valid_params__t'63 (Vint (if andb (wi_start f + wi_size f - base =? ip2)
        (got2 =? wi_cstart f + wi_csize f) then Int.one else Int.zero)) :: L) (SEPx R)))
    end.
    { match goal with H: Int64.eq _ _ = true |- _ => rewrite add64_repr, sub64_repr in H;
        rewrite D2_EQ64 in H by rep_lia; apply Z.eqb_eq in H; rename H into Hend end.
      forward.
      { entailer!. rewrite Fk. exact I. }
      forward.
      { entailer!. rewrite Fk. exact I. }
      rewrite !Fk. unfold winfo_val at 1 2. cbv beta iota zeta.
      forward. rewrite (proj2 (Z.eqb_eq _ _) Hend). simpl andb. entailer!.
      try unfold Int64.cmpu. try rewrite add64_repr. rewrite D2_EQ64 by rep_lia. unfold bool2val.
      destruct (got2 =? wi_cstart f + wi_csize f); reflexivity. }
    { match goal with H: Int64.sub _ _ <> _ |- _ => rewrite add64_repr, sub64_repr in H; rename H into Hne end.
      destruct (Z.eqb_spec (wi_start f + wi_size f - base) ip2) as [E|E]; [rewrite E in Hne; contradiction|].
      forward. entailer!. }
    forward_if.
    { forward. Exists k. entailer!.
      rewrite D2_at_step by lia. fold f.
      destruct (andb (wi_start f + wi_size f - base =? ip2) (got2 =? wi_cstart f + wi_csize f));
        [rewrite orb_true_r; reflexivity | exfalso; match goal with H: _ <> Int.zero |- _ => apply H; reflexivity end]. }
    { forward. Exists k. entailer!.
      rewrite D2_at_step by lia. fold f.
      destruct (andb (wi_start f + wi_size f - base =? ip2) (got2 =? wi_cstart f + wi_csize f));
        [exfalso; apply Int.one_not_zero; assumption | rewrite orb_false_r; reflexivity]. } }
  { Intros k. forward. Exists (k + 1). entailer!. }
  forward_call Int.one.
  fold (VP_Rnf (vu (Zlength (ws_frames wsr))) (gv _x_valid_params__sr)).
  fold (VP_Rf (map winfo_val (ws_frames wsr) ++ Zrepeat (winfo_val winfo0) (4 - Zlength (ws_frames wsr))) (gv _x_valid_params__sr)).
  sep_apply (VP_sr_fold7w wsr (gv _x_valid_params__sr)).
  forward_if.
  { forward. unfold D2_brk, VP_SD1. Exists st'. entailer!. }
  { forward. unfold D2_cont, D2_A, D2_R, D2_L. Exists calls ip2 got2 (if b0 then stalled + 1 else 0) st'.
    entailer!. } }
forward. unfold D2_cont, D2_A, D2_R, D2_L. Exists calls ip2 got2 (if b0 then stalled + 1 else 0) st'.
entailer!.
Qed.

End Seg.
