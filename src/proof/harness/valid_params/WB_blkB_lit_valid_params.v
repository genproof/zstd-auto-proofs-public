(* w_compressed_block, segment B, statement 14 (the literals loop of a sequence: for (j = 0; j < ll; j++) a
   literal of the mode into w_lit[nlit++] and w_hist at hn, hn += 1) in the unit valid_params: segB_lit of
   WBlkBDefs_valid_params.  Template: WB_blkB_lit.

   Same proof as segment C's trailing literals (the template WB_blk_C): R destructed, the
   untouched SEP items opaque (set .. in *; clearbody), st/newhuf split into the huf_t hp points to and a rest,
   forward_for_simple_bound with the literals L drawn so far; blk_tail .. 0 = []. *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.harness.valid_params.WBlkBDefs_valid_params.
Local Open Scope logic.

Lemma blkBL_perm6 : forall A B C D E F : mpred,
  A * (B * (C * (D * E))) * F = B * (A * (C * (D * E)) * F).
Proof. intros. apply pred_ext; cancel. Qed.

(* st (and newhuf) with the code hp points to (modes 2, 3) taken out *)
Lemma blkBL_hsplit : forall lm Hl stv1 nhv ssh stp gv,
  readable_share ssh -> 0 <= lm <= 3 -> (lm = 2 -> huf_rep Hl nhv) -> (lm = 3 -> huf_rep Hl (wv_huf stv1)) ->
  exists sh hv Q, readable_share sh /\ (2 <= lm -> huf_rep Hl hv) /\
    data_at ssh t_wstate stv1 stp * data_at Ews t_huf nhv (gv _x_valid_params__newhuf) =
    (if 2 <=? lm then data_at sh t_huf hv
       (if lm =? 2 then gv _x_valid_params__newhuf
        else if lm =? 3 then field_address t_wstate (DOT _huf) stp else nullval) else emp) * Q.
Proof.
  intros until gv. intros Hsh Hlm H2 H3.
  destruct (Z_lt_le_dec lm 2).
  - exists Ews, nhv, (data_at ssh t_wstate stv1 stp * data_at Ews t_huf nhv (gv _x_valid_params__newhuf)).
    split; [auto |]. split; [lia |].
    replace (2 <=? lm) with false by lia. rewrite emp_sepcon. reflexivity.
  - assert (lm = 2 \/ lm = 3) as [-> | ->] by lia.
    + exists Ews, nhv, (data_at ssh t_wstate stv1 stp). split; [auto |]. split; [auto |].
      simpl. apply sepcon_comm.
    + exists ssh, (wv_huf stv1).
      simpl. unfold_data_at (data_at ssh t_wstate stv1 stp).
      rewrite (field_at_data_at ssh t_wstate (DOT _huf)).
      eexists. split; [auto |]. split; [auto |].
      change (nested_field_type t_wstate (DOT _huf)) with t_huf.
      apply blkBL_perm6.
Qed.

Lemma blkBL_huf3 : forall S rep lm rleb Hl stv1,
  lm_ok S lm rleb Hl -> wstate_rep (set_rep S rep) stv1 -> lm = 3 -> huf_rep Hl (wv_huf stv1).
Proof.
  intros S rep lm rleb Hl stv1 (_ & _ & _ & H3) (_ & _ & _ & Hh & _) E.
  apply Hh. destruct S; apply H3; auto.
Qed.

(* ---------- the literal drawn ---------- *)

Lemma blkBL_filter_len : forall (f: Z -> bool) l, Zlength (filter f l) <= Zlength l.
Proof.
  intros f l. induction l as [| x l IH]; simpl; [lia |].
  rewrite Zlength_cons. destruct (f x); [rewrite Zlength_cons |]; lia.
Qed.

Lemma blkBL_used_len : forall Hl, huf_ok Hl -> 2 <= Zlength (wh_used Hl) <= 256.
Proof.
  intros Hl (_ & _ & _ & _ & Hu & H2 & _). split; [exact H2 |].
  rewrite Hu. eapply Z.le_trans; [apply blkBL_filter_len |].
  unfold syms256. rewrite Zlength_map, Zlength_correct, seq_length. simpl. lia.
Qed.

Lemma blkBL_used : forall Hl hv k, huf_ok Hl -> huf_rep Hl hv -> 0 <= k < Zlength (wh_used Hl) ->
  Znth k (hf_used hv) = vu (Znth k (wh_used Hl)) /\ huf_present Hl (Znth k (wh_used Hl)).
Proof.
  intros Hl hv k Hok (_ & _ & _ & Hu & _) Hk. split.
  - assert (E: Znth k (sublist 0 (Zlength (wh_used Hl)) (hf_used hv)) = Znth k (map vu (wh_used Hl)))
      by (rewrite Hu; reflexivity).
    rewrite Znth_map in E by lia. rewrite Znth_sublist in E by lia. rewrite Z.add_0_r in E. exact E.
  - destruct Hok as (_ & _ & _ & _ & Hused & _).
    set (x := Znth k (wh_used Hl)).
    assert (Hin: In x (wh_used Hl)) by (apply Znth_In; lia).
    clearbody x. rewrite Hused in Hin. apply filter_In in Hin. destruct Hin as [Hin Hw].
    unfold syms256 in Hin. apply in_map_iff in Hin. destruct Hin as (n & En & Hn).
    apply in_seq in Hn. unfold huf_present. split; [lia |].
    intros E0. rewrite E0 in Hw. discriminate.
Qed.

Lemma blkBL_lit_byte : forall S lm rleb Hl c, lm_ok S lm rleb Hl -> lit_in lm rleb Hl c -> 0 <= c < 256.
Proof.
  intros S lm rleb Hl c (_ & Hr & _) Hc. unfold lit_in in Hc.
  destruct (lm =? 0); [lia |]. destruct (lm =? 1); [lia |]. apply Hc.
Qed.

Lemma blkBL_lit2 : forall lm rleb Hl c, 2 <= lm -> huf_present Hl c -> lit_in lm rleb Hl c.
Proof.
  intros. unfold lit_in. replace (lm =? 0) with false by lia. replace (lm =? 1) with false by lia. assumption.
Qed.

Lemma blkBL_add64 : forall a,
  Int64.add (Int64.repr a) (Int64.repr (Int.signed (Int.repr 1))) = Int64.repr (a + 1).
Proof.
  intros. unfold Int64.add. apply Int64.eqm_samerepr. apply Int64.eqm_add.
  - apply Int64.eqm_sym, Int64.eqm_unsigned_repr.
  - rewrite Int.signed_repr by rep_lia. rewrite Int64.unsigned_repr by rep_lia. apply Int64.eqm_refl.
Qed.

Lemma blkBL_zext : forall c, 0 <= c < 256 -> Int.zero_ext 8 (Int.repr c) = Int.repr c.
Proof.
  intros. apply zero_ext_inrange. rewrite Int.unsigned_repr by rep_lia. simpl. lia.
Qed.

(* ---------- the two stores ---------- *)

Lemma blkBL_upd_gen : forall (a: list Z) (tl: list val) c, 0 < Zlength tl ->
  upd_Znth (Zlength a) (zbytes a ++ tl) (Vint (Int.repr c)) = zbytes (a ++ [c]) ++ sublist 1 (Zlength tl) tl.
Proof.
  intros a tl c Htl.
  rewrite upd_Znth_app2 by (rewrite Zlength_map; lia).
  rewrite Zlength_map, Z.sub_diag.
  destruct tl as [| v tl]; [rewrite Zlength_nil in Htl; lia |].
  rewrite upd_Znth0. rewrite map_app, <- app_assoc. simpl. f_equal. f_equal.
  rewrite Zlength_cons, sublist_1_cons, sublist_same by lia. reflexivity.
Qed.

Lemma blkBL_lit_step : forall N lits L c, Zlength (lits ++ L) < N ->
  upd_Znth (Zlength lits + Zlength L) (zbytes (lits ++ L) ++ Zrepeat Vundef (N - Zlength (lits ++ L)))
    (Vint (Int.repr c)) =
  zbytes (lits ++ (L ++ [c])) ++ Zrepeat Vundef (N - Zlength (lits ++ (L ++ [c]))).
Proof.
  intros. rewrite <- Zlength_app, blkBL_upd_gen by (rewrite Zlength_Zrepeat; lia).
  rewrite app_assoc. f_equal.
  rewrite sublist_Zrepeat by (rewrite ?Zlength_Zrepeat; lia).
  rewrite !Zlength_Zrepeat by lia. f_equal. rewrite (Zlength_app _ (lits ++ L) [c]). change (Zlength [c]) with 1. lia.
Qed.

Lemma blkBL_hist_step : forall hist out cont L tl c, Zlength L < Zlength tl ->
  upd_Znth (Zlength hist + Zlength out + Zlength cont + Zlength L)
    (zbytes (hist ++ out ++ cont ++ L) ++ sublist (Zlength L) (Zlength tl) tl) (Vint (Int.repr c)) =
  zbytes (hist ++ out ++ cont ++ (L ++ [c])) ++ sublist (Zlength L + 1) (Zlength tl) tl.
Proof.
  intros. pose proof (Zlength_nonneg L).
  replace (Zlength hist + Zlength out + Zlength cont + Zlength L) with (Zlength (hist ++ out ++ cont ++ L))
    by (rewrite !Zlength_app; lia).
  rewrite blkBL_upd_gen by (rewrite Zlength_sublist by lia; lia).
  rewrite !app_assoc. f_equal.
  rewrite Zlength_sublist by lia.
  rewrite sublist_sublist by lia. f_equal; lia.
Qed.

Lemma blkBL_tail0 : forall E cont L off, blk_tail E cont L off 0 = [].
Proof.
  intros. unfold blk_tail, lz_tail. simpl. apply skipn_all.
Qed.

Lemma segB_lit_ok : segB_lit.
Proof.
  unfold segB_lit. blkB_start.
  unfold blk_it, blk_env_ok, blk_locals, blk_bsm, hp_val in *.
  rewrite blkBL_tail0.
  destruct E as [gv osh bsh o p cap bs tl ssh stp stv S hsh hnp hist out htl t window
                 vblk vmode vopts vvalid vforms vopts1 vbt]; blk_env_simpl.
  destruct H as (Hosh & Hbsh & Hssh & Hhsh & Hwt & Hrep & Hbh & Hbo & Hlh & Hlo & Hwin & Ht & Hhs & Hhl).
  destruct R as [Rn Rb Rc Rr].
  Intros stv1 htl1 nhv.
  rename H into Hlmok, H1 into Hst1, H3 into Hnh, H13 into Hlen, H25 into Hhtl1.
  clear H20 H21 H22 H23 H24.
  rewrite !app_nil_r in *. rewrite Zlength_nil, Z.add_0_r, Z.add_0_r.
  destruct (blkBL_hsplit lm Hl stv1 nhv ssh stp gv) as (hsh' & hv & Q & Hrsh & Hhv & HQ);
    [auto | apply Hlmok | assumption | eapply blkBL_huf3; eassumption |].
  sep_apply (derives_refl' _ _ HQ).
  set (X2 := out_rep Tsh Ews vblk (gv _x_valid_params__blk_buf) 135168 [] (Zrepeat Vundef 135168)) in *.
  set (X3 := out_rep osh bsh o p cap bs tl) in *.
  set (X4 := data_at Ews (tarray (tarray tuchar 65536) 3) (code_rows seqs) (gv _x_valid_params__w_code)) in *.
  set (X5 := data_at Ews (tarray (tarray tuint 65536) 3) (extra_rows seqs) (gv _x_valid_params__w_extra)) in *.
  set (X6 := blk_fixed gv) in *.
  clearbody X2 X3 X4 X5 X6.
  set (hpv := if lm =? 2 then gv _x_valid_params__newhuf
              else if lm =? 3 then field_address t_wstate (DOT _huf) stp else nullval) in *.
  clearbody hpv.
  set (HX := if 2 <=? lm then data_at hsh' t_huf hv hpv else emp).
  flatten_sepcon_in_SEP.
  forward_for_simple_bound ll
    (EX i: Z, EX L: list Z,
     PROP (Zlength L = i; Forall (lit_in lm rleb Hl) L; bytes_ok L)
     LOCAL (temp _ll (vl ll); temp _ml (vl ml); temp _off (vl off); temp _ov (vl ov);
       lvar _b t_bits vbt; lvar _opts__1 (tarray tuint 4) vopts1;
       lvar _forms (tarray tuint 3) vforms; lvar _valid (tarray tuint 3) vvalid;
       lvar _opts (tarray tuint 4) vopts; lvar _mode (tarray tuint 3) vmode;
       lvar _blk t_out vblk; gvars gv; temp _o o; temp _st__1 stp;
       temp _dictn (vl (Zlength hist)); temp _hn hnp;
       temp _t__1 (vl t); temp _window (vl window);
       temp _bmax (vl (Z.min window (2 ^ 17))); temp _nseq (vl (Zlength seqs));
       temp _nlit (vl (Zlength lits + i)); temp _rem (vl (t - Zlength cont));
       temp _litmode (vu lm); temp _rleb (vu rleb); temp _hp hpv)
     SEP (HX; Q; data_at_ Tsh t_bits vbt; data_at_ Tsh (tarray tuint 4) vopts1;
       data_at_ Tsh (tarray tuint 3) vforms; data_at_ Tsh (tarray tuint 3) vvalid;
       data_at_ Tsh (tarray tuint 4) vopts; data_at_ Tsh (tarray tuint 3) vmode; X2; X3;
       data_at hsh tulong (vl (Zlength hist + Zlength out + Zlength cont + i)) hnp;
       data_at Ews (tarray tuchar HIST_SIZE)
         (zbytes (hist ++ out ++ cont ++ L) ++ sublist i (Zlength htl1) htl1) (gv _x_valid_params__w_hist);
       data_at Ews (tarray tuchar 131072)
         (zbytes (lits ++ L) ++ Zrepeat Vundef (131072 - Zlength (lits ++ L))) (gv _x_valid_params__w_lit);
       X4; X5; X6)).
  - (* entry *)
    Exists (@nil Z). rewrite !app_nil_r, sublist_same by reflexivity. rewrite Z.add_0_r.
    entailer!. constructor.
  - (* one literal *)
    assert (Hlm: 0 <= lm <= 3) by apply Hlmok.
    assert (Hrb: 0 <= rleb < 256) by apply Hlmok.
    lazymatch goal with |- semax _ (PROPx ?P (LOCALx ?Lc (SEPx ?Sc))) _ _ =>
      forward_if (EX c: Z, PROPx (lit_in lm rleb Hl c :: P)
                             (LOCALx (temp _x_valid_params__t'24 (vu c) :: Lc) (SEPx Sc))) end.
    + forward_call 256. Intros r. forward.
      Exists r. rewrite blkBL_zext by lia. entailer!.
    + forward_if.
      * forward. forward. Exists rleb. rewrite blkBL_zext by exact Hrb. entailer!.
      * assert (Hge: 2 <= lm) by lia.
        unfold HX. replace (2 <=? lm) with true by (symmetry; apply Z.leb_le; lia).
        pose proof (proj1 (proj2 (proj2 Hlmok)) Hge) as Hok.
        pose proof (Hhv Hge) as Hrv. pose proof (blkBL_used_len Hl Hok) as Hul.
        assert (Hn: hf_nused hv = vu (Zlength (wh_used Hl))) by apply Hrv.
        forward.
        { match goal with |- context [tc_val tuint ?v] => replace v with (hf_nused hv) by reflexivity end.
          rewrite Hn. entailer!. }
        match goal with |- context [temp _x_valid_params__t'104 ?v] => replace v with (hf_nused hv) by reflexivity end.
        rewrite Hn.
        forward_call (Zlength (wh_used Hl)). Intros k.
        destruct (blkBL_used Hl hv k Hok Hrv) as [Hk Hpk]; [lia |].
        assert (Hpb: 0 <= Znth k (wh_used Hl) < 256) by apply Hpk.
        forward.
        { match goal with |- context [tc_val tuchar (Znth k ?l)] =>
            replace (Znth k l) with (vu (Znth k (wh_used Hl))) by (rewrite <- Hk; reflexivity) end.
          entailer!. rep_lia. }
        match goal with |- context [temp _x_valid_params__t'103 (Znth k ?l)] =>
          replace (Znth k l) with (vu (Znth k (wh_used Hl))) by (rewrite <- Hk; reflexivity) end.
        forward. forward.
        Exists (Znth k (wh_used Hl)). entailer!.
        -- apply blkBL_lit2; assumption.
        -- unfold HX. replace (2 <=? lm) with true by (symmetry; apply Z.leb_le; lia). apply derives_refl.
    + Intros c.
      assert (Hcb: 0 <= c < 256) by (eapply blkBL_lit_byte; eassumption).
      assert (Ht17: t <= 131072) by (pose proof (Z.le_min_r window (2 ^ 17)) as Hm; change (2 ^ 17) with 131072 in Hm; lia).
      forward.
      forward. forward.
      rewrite blkBL_zext by lia.
      subst i.
      assert (Hhtl: Zlength L < Zlength htl1)
        by (rewrite Zlength_app, Zlength_map, !Zlength_app in Hhtl1; lia).
      assert (Hlits: Zlength (lits ++ L) < 131072) by (rewrite Zlength_app; lia).
      remember 131072 as NL eqn:HNL. remember HIST_SIZE as NH eqn:HNH.
      forward.
      { entailer!. }
      rewrite blkBL_zext by lia.
      forward. forward.
      match goal with |- context [temp _x_valid_params__t'28 (vl ?x)] =>
        change (vl x) with (Vlong (Int64.repr x)) end.
      forward.
      { entailer!. }
      rewrite blkBL_zext by lia.
      rewrite blkBL_hist_step by lia. rewrite blkBL_lit_step by assumption.
      rewrite !blkBL_add64.
      Exists (L ++ [c]).
      entailer!.
      * split; [rewrite Zlength_app, Zlength_cons, Zlength_nil; lia |].
        split; [apply Forall_app; auto |].
        split; [apply Forall_app; split; [assumption | constructor; [unfold is_byte; lia | constructor]] |].
        unfold vl. rewrite Z.add_assoc. reflexivity.
      * unfold vl. rewrite Z.add_assoc. apply derives_refl.
  - (* after the loop: L, |L| = ll *)
    Intros L.
    eapply semax_pre; [| exact H0].
    unfold HX. sep_apply (derives_refl' _ _ (eq_sym HQ)).
    Exists L. rewrite blkBL_tail0, app_nil_r.
    Exists stv1 (sublist ll (Zlength htl1) htl1) nhv.
    rewrite Zlength_app, Z.add_0_r.
    entailer!.
Qed.
