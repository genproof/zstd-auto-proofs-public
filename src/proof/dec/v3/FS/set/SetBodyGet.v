(* FS3 set part: the body of ZSTD_DDictHashSet_getDDict. *)
Require Import Zstd.proof.dec.v3.FS.set.SetDefs.
Local Open Scope logic.

Section CM_SetBodyGet_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma sbg_inv0 l tbl : hs_inv l tbl -> hs_inv0 l tbl.
Proof.
  unfold hs_inv, hs_inv0, hs_nonnull. intros (? & _ & ?). tauto.
Qed.

Lemma sbg_land_mod x k : 0 <= k -> Z.land x (2 ^ k - 1) = x mod 2 ^ k.
Proof.
  intros Hk. rewrite <- Z.land_ones by lia. f_equal. rewrite Z.ones_equiv. lia.
Qed.

Lemma sbg_fc_bound p n : 0 <= n -> field_compatible (tarray (tptr t_ddict) n) [] p -> 8 * n < Ptrofs.modulus.
Proof.
  intros Hn [Hp [_ [Hsz _]]]. destruct p; try contradiction. simpl in Hsz.
  rewrite Z.max_r in Hsz by lia. pose proof (Ptrofs.unsigned_range i). lia.
Qed.

Lemma sbg_probe_null f l tbl j n id :
  Znth j tbl = nullval -> hs_probe_f (S f) l tbl j n id = nullval.
Proof. intros H. simpl. rewrite H. rewrite if_true by auto. auto. Qed.

Lemma sbg_probe_hit f l tbl j n id :
  Znth j tbl <> nullval -> (set_id_of l (Znth j tbl) = id \/ set_id_of l (Znth j tbl) = 0) ->
  hs_probe_f (S f) l tbl j n id = Znth j tbl.
Proof.
  intros H1 H2. simpl. rewrite if_false by auto.
  destruct H2 as [H2|H2]; rewrite H2, Z.eqb_refl; [reflexivity|]. rewrite orb_true_r. reflexivity.
Qed.

Lemma sbg_probe_miss f l tbl j n id :
  Znth j tbl <> nullval -> set_id_of l (Znth j tbl) <> id -> set_id_of l (Znth j tbl) <> 0 ->
  hs_probe_f (S f) l tbl j n id = hs_probe_f f l tbl ((j + 1) mod n) n id.
Proof.
  intros H1 H2 H3. simpl. rewrite if_false by auto.
  apply Z.eqb_neq in H2, H3. rewrite H2, H3. reflexivity.
Qed.

Lemma sbg_tbl_ptr l tbl j : hs_inv l tbl -> 0 <= j < Zlength tbl -> Znth j tbl = nullval \/ isptr (Znth j tbl).
Proof.
  intros Hi Hj. unfold hs_inv in Hi. destruct Hi as (_ & _ & _ & _ & _ & _ & _ & Hf & _).
  rewrite Forall_forall in Hf. apply Hf. apply Znth_In. auto.
Qed.

Lemma sbg_pon l tbl j : hs_inv l tbl -> 0 <= j < Zlength tbl -> is_pointer_or_null (Znth j tbl).
Proof.
  intros Hi Hj. destruct (sbg_tbl_ptr l tbl j Hi Hj) as [E|E]; [rewrite E; simpl; auto|].
  destruct (Znth j tbl); try contradiction; simpl; auto.
Qed.

Lemma sbg_eq_true a b : 0 <= a <= Int.max_unsigned -> 0 <= b <= Int.max_unsigned ->
  Int64.eq (Int64.repr a) (Int64.repr (Int.unsigned (Int.repr b))) = true -> a = b.
Proof.
  intros Ha Hb E. rewrite Int.unsigned_repr in E by lia. apply Int64.same_if_eq in E.
  apply repr_inj_unsigned64 in E; rep_lia.
Qed.

Lemma sbg_eq_false a b : 0 <= a <= Int.max_unsigned -> 0 <= b <= Int.max_unsigned ->
  Int64.eq (Int64.repr a) (Int64.repr (Int.unsigned (Int.repr b))) = false -> a <> b.
Proof.
  intros Ha Hb E ->. rewrite Int.unsigned_repr in E by lia. rewrite Int64.eq_true in E. discriminate.
Qed.

Lemma sbg_neq a b : 0 <= b <= Int.max_unsigned ->
  Int64.repr a <> Int64.repr (Int.unsigned (Int.repr b)) -> a <> b.
Proof. intros Hb E ->. rewrite Int.unsigned_repr in E by lia. contradiction. Qed.

Lemma sbg_cmp0 a b : 0 <= a <= Int.max_unsigned -> a <> b ->
  Vint (if orb (a =? b) (a =? 0) then Int.one else Int.zero) = bool2val (Int64.cmpu Ceq (Int64.repr a) (Int64.repr 0)).
Proof.
  intros Ha Hab. apply Z.eqb_neq in Hab. rewrite Hab. simpl orb.
  destruct (Z.eqb_spec a 0) as [->|Ha0]; [reflexivity|].
  unfold Int64.cmpu. rewrite Int64.eq_false; [reflexivity|].
  intros E. apply repr_inj_unsigned64 in E; rep_lia.
Qed.

Lemma sbg_next s n k : 0 <= k -> n = 2 ^ k -> 0 <= s < n -> n <= Int64.max_unsigned ->
  Int64.and (Int64.add (Int64.repr s) (Int64.repr 1)) (Int64.repr (n - 1)) = Int64.repr ((s + 1) mod n).
Proof.
  intros Hk Hn Hs Hm. unfold Int64.and, Int64.add.
  rewrite (Int64.unsigned_repr s), (Int64.unsigned_repr 1), Int64.unsigned_repr, (Int64.unsigned_repr (n - 1)) by rep_lia.
  subst n. rewrite sbg_land_mod by lia. reflexivity.
Qed.

Lemma sbg_slot_next h t n : 0 < n -> hs_slot h (t + 1) n = (hs_slot h t n + 1) mod n.
Proof. intros Hn. unfold hs_slot. rewrite Zplus_mod_idemp_l. f_equal. lia. Qed.

Lemma sbg_nodup l tbl : hs_inv l tbl -> NoDup (map fst l).
Proof. unfold hs_inv. tauto. Qed.

Lemma set_body_get : MF_ddid_wvp -> MF_ddid_range -> MF_ids_focus -> PF_member -> PF_set_id -> PF_notfull ->
  semax_body Vprog G_getDDict f_ZSTD_DDictHashSet_getDDict ZSTD_DDictHashSet_getDDict_spec.
Proof.
  intros Hwvp Hrange Hfocus Hmember Hsetid Hnotfull.
  start_function.
  unfold hset_tbl, hs_table. Intros tp.
  set (n := Zlength tbl) in *.
  assert (Hinv0 := sbg_inv0 _ _ H0).
  assert (Hk: exists k, 6 <= k /\ n = 2 ^ k) by (unfold hs_inv in H0; destruct H0 as [Hk _]; exact Hk).
  destruct Hk as (k & Hk6 & Hnk).
  assert (Hn64: 64 <= n) by (rewrite Hnk; replace 64 with (2 ^ 6) by reflexivity; apply Z.pow_le_mono_r; lia).
  assert (Hnb: 8 * n < Ptrofs.modulus) by (apply (sbg_fc_bound tp); auto; lia).
  assert (Hnb': n <= Int64.max_unsigned) by rep_lia.
  assert (Hh: 0 <= hs_home id n < n).
  { unfold hs_home. rewrite Hnk, sbg_land_mod by lia. apply Z.mod_pos_bound. lia. }
  assert (Hs0: hs_slot (hs_home id n) 0 n = hs_home id n) by (unfold hs_slot; rewrite Z.add_0_r; apply Z.mod_small; lia).
  assert (Hpr: hs_probe l tbl id = hs_probe_f (Z.to_nat n) l tbl (hs_home id n) n id) by reflexivity.
  forward_call (Ews, sp, tp, n, Vlong (Int64.repr (Zlength l)), id).
  revert Hh Hs0 Hpr. generalize (hs_home id n). intros h Hh Hs0 Hpr.
  forward.
  forward.
  match goal with |- semax _ ?P _ _ => forward_loop P break: P end; [entailer! | forward; entailer! | ].
  forward_loop (EX t: Z,
    PROP (0 <= t < n; forall t', 0 <= t' < t -> Znth (hs_slot h t' n) tbl <> nullval;
          hs_probe l tbl id = hs_probe_f (Z.to_nat (n - t)) l tbl (hs_slot h t n) n id)
    LOCAL (temp _idxRangeMask (Vlong (Int64.repr (n - 1))); temp _idx (Vlong (Int64.repr (hs_slot h t n)));
           temp _hashSet sp; temp _dictID (Vint (Int.repr id)))
    SEP (data_at Ews t_hset (tp, (Vlong (Int64.repr n), Vlong (Int64.repr (Zlength l)))) sp;
         blk_tok am t_hset sp; blk_tok am (tarray tuchar (8 * n)) tp;
         data_at Ews (tarray (tptr t_ddict) n) tbl tp; set_ids l))%assert
  break: (EX j: Z,
    PROP (0 <= j < n; hs_probe l tbl id = Znth j tbl)
    LOCAL (temp _idx (Vlong (Int64.repr j)); temp _hashSet sp)
    SEP (data_at Ews t_hset (tp, (Vlong (Int64.repr n), Vlong (Int64.repr (Zlength l)))) sp;
         blk_tok am t_hset sp; blk_tok am (tarray tuchar (8 * n)) tp;
         data_at Ews (tarray (tptr t_ddict) n) tbl tp; set_ids l))%assert.
  { Exists 0. entailer!. rewrite Hs0, Hpr, ZtoNat_Zlength. reflexivity. }
  { Intros t.
    assert (Hs: 0 <= hs_slot h t n < n) by (unfold hs_slot; apply Z.mod_pos_bound; lia).
    forward.
    forward.
    { entailer!. apply (sbg_pon l); auto. }
    destruct (eq_dec (Znth (hs_slot h t n) tbl) nullval) as [Hnull|Hnn].
    - forward_call (Znth (hs_slot h t n) tbl, 0, nullval). { rewrite if_true by auto. cancel. }
      rewrite !if_true by auto.
      forward.
      match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
        forward_if (PROPx P (LOCALx (temp _t'3 (Vint Int.one) :: Q) (SEPx R))) end.
      { forward. entailer!. }
      { forward. entailer!. }
      forward_if.
      2: { match goal with Hc: Int.one = Int.zero |- _ => apply Int.one_not_zero in Hc; contradiction end. }
      forward.
      assert (Hp: hs_probe l tbl id = Znth (hs_slot h t n) tbl).
      { rewrite H4. replace (Z.to_nat (n - t)) with (S (Z.to_nat (n - t - 1))) by (rewrite <- Z2Nat.inj_succ by lia; f_equal; lia).
        rewrite sbg_probe_null by auto. symmetry; auto. }
      Exists (hs_slot h t n). entailer!.
    - destruct (Hmember l tbl (hs_slot h t n) Hinv0 Hs Hnn) as (e & Hin & Hfe).
      destruct (Hfocus l e Hin) as (L1 & L2 & HL & Hids).
      rewrite Hfe in Hids. rewrite Hids.
      assert_PROP (0 <= dd_id (snd e) <= Int.max_unsigned) by (sep_apply (Hrange (Znth (hs_slot h t n) tbl) (dd_id (snd e)) (ddb (snd e))); entailer!).
      forward_call (Znth (hs_slot h t n) tbl, dd_id (snd e), ddb (snd e)).
      { rewrite if_false by auto. cancel. }
      rewrite !if_false by auto.
      forward.
      assert (Hsid: set_id_of l (Znth (hs_slot h t n) tbl) = dd_id (snd e))
        by (rewrite <- Hfe; apply Hsetid; auto; apply (sbg_nodup l tbl); auto).
      gather_SEP 0 5. rewrite <- Hids.
      set (did := dd_id (snd e)) in *. clearbody did.
      rewrite Int.unsigned_repr by lia.
      match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
        forward_if (PROPx P (LOCALx (temp _t'3 (Vint (if orb (Z.eqb did id) (Z.eqb did 0) then Int.one else Int.zero)) :: Q) (SEPx R))) end.
      { forward. entailer!.
        match goal with Hc: Int64.eq _ _ = true |- _ => apply sbg_eq_true in Hc; [|lia|lia]; rewrite Hc, Z.eqb_refl end.
        reflexivity. }
      { forward. entailer!.
        apply sbg_cmp0; [lia|]. apply sbg_neq; auto. }
      clear HL Hids Hfe Hin e L1 L2.
      destruct (orb (did =? id) (did =? 0)) eqn:Hb.
      + forward_if.
        2: { match goal with Hc: Int.one = Int.zero |- _ => apply Int.one_not_zero in Hc; contradiction end. }
        forward.
        assert (Hp: hs_probe l tbl id = Znth (hs_slot h t n) tbl).
        { rewrite H4. replace (Z.to_nat (n - t)) with (S (Z.to_nat (n - t - 1))) by (rewrite <- Z2Nat.inj_succ by lia; f_equal; lia).
          apply sbg_probe_hit; auto. rewrite Hsid. apply orb_true_iff in Hb. destruct Hb as [Hb|Hb]; apply Z.eqb_eq in Hb; auto. }
        Exists (hs_slot h t n). entailer!.
      + forward_if.
        { match goal with Hc: 0 <> 0 |- _ => contradiction end. }
        forward.
        apply orb_false_iff in Hb. destruct Hb as [Hb1 Hb2]. apply Z.eqb_neq in Hb1, Hb2.
        assert (Ht1: t + 1 < n).
        { destruct (Z.lt_ge_cases (t + 1) n) as [|Hge]; auto. exfalso.
          destruct (Hnotfull l tbl h Hinv0 Hh) as (t0 & Ht0 & Ht0n). fold n in Ht0, Ht0n.
          destruct (Z.lt_ge_cases t0 t); [apply (H3 t0); auto; lia|]. replace t0 with t in Ht0n by lia. auto. }
        assert (Hq: forall t', 0 <= t' < t + 1 -> Znth (hs_slot h t' n) tbl <> nullval).
        { intros t' Ht'. destruct (Z.lt_ge_cases t' t); [apply H3; lia|]. replace t' with t by lia. auto. }
        assert (Hp: hs_probe l tbl id = hs_probe_f (Z.to_nat (n - (t + 1))) l tbl (hs_slot h (t + 1) n) n id).
        { rewrite H4. replace (Z.to_nat (n - t)) with (S (Z.to_nat (n - (t + 1)))) by (rewrite <- Z2Nat.inj_succ by lia; f_equal; lia).
          rewrite sbg_probe_miss by (auto; rewrite Hsid; auto). rewrite sbg_slot_next by lia. reflexivity. }
        assert (Hidx: Int64.and (Int64.add (Int64.repr (hs_slot h t n)) (Int64.repr (Int.signed (Int.repr 1)))) (Int64.repr (n - 1))
                      = Int64.repr (hs_slot h (t + 1) n)).
        { rewrite sbg_slot_next by lia. apply (sbg_next _ _ k); auto; lia. }
        Exists (t + 1). rewrite Hidx. entailer!. }
  Intros j.
  match goal with |- semax _ ?P _ _ => forward_loop P break: P end; [entailer! | forward; entailer! | ].
  forward.
  forward.
  { entailer!. apply (sbg_pon l); auto. }
  forward.
  unfold hset_tbl, hs_table. Exists tp. entailer!.
Qed.

End CM_SetBodyGet_1.
