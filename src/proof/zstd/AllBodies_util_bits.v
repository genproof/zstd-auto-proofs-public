(* The proof obligations of group(s) util, bits (fields of ZstdBodies, in order).  Prove each
   conjunct by a body lemma `body_X` (in src/proof/zstd/body_<group>*.v files that this file Requires),
   or by `semax_body_vacuous` for a function whose specification stays vacuous. *)
Require Import Zstd.proof.zstd.Gprog.
Require Import Zstd.proof.zstd.body_util_mem Zstd.proof.zstd.body_util_write64 Zstd.proof.zstd.body_util_count Zstd.proof.zstd.body_util_misc Zstd.proof.zstd.body_bits_init Zstd.proof.zstd.body_bits_reload Zstd.proof.zstd.body_bits_read.

(* API v2: the bodies whose specifications changed (Spec_bits.v), proved here. *)

Lemma v2_body_BIT_initDStream :
  semax_body Vprog Gprog f_BIT_initDStream BIT_initDStream_spec.
Proof.
  start_function.
  assert_PROP (field_compatible (tarray tuchar (Zlength buf)) [] bp) as FCb
    by (unfold bit_src; entailer!).
  assert (Hbp: isptr bp) by apply FCb. destruct bp as [| | | | | b0 i0]; try contradiction.
  assert (HL: Zlength buf < Ptrofs.modulus).
  { pose proof FCb as FC'. destruct FC' as (Hp & _ & Hsz & _).
    unfold size_compatible in Hsz. simpl sizeof in Hsz. pose proof (Ptrofs.unsigned_range i0).
    rewrite Z.max_r in Hsz by list_solve. lia. }
  forward_if.
  { (* srcSize < 1 *)
    assert (n = 0) by (rewrite !Int64.unsigned_repr in H3 by rep_lia; lia). subst n.
    rewrite data_at__memory_block. Intros.
    forward_call (sh, p, 0, sizeof (Tstruct ___gp_BIT_DStream_t noattr)).
    forward.
    Exists (2^64 - 72).
    rewrite sublist_nil. change (bs_wf []) with false. cbv iota.
    entailer!.
    { f_equal. apply Int64.eqm_samerepr. exists (-1). reflexivity. }
    rewrite data_at__memory_block. sep_apply data_at_memory_block. entailer!. simpl sizeof. cancel. }
  assert (Hn1: 1 <= n) by (rewrite !Int64.unsigned_repr in H3 by rep_lia; lia).
  set (s := sublist off (off + n) buf) in *.
  assert (Hs: Zlength s = n) by (unfold s; list_solve).
  unfold bit_src. rewrite (bi_src_split3 shs (Vptr b0 i0) buf off n) by (auto; lia). fold s. Intros.
  forward. forward. forward.
  forward_if (PROP (bs_wf s = true)
    LOCAL (temp _srcSize (Vlong (Int64.repr n)))
    SEP (BIT_DStream_rep sh gv s (offset_val off (Vptr b0 i0)) (bs_total s) (8 * Z.max 0 (n - 8)) p;
         data_at shs (tarray tuchar off) (zbytes (sublist 0 off buf)) (Vptr b0 i0);
         data_at shs (tarray tuchar n) (zbytes s) (offset_val off (Vptr b0 i0));
         data_at shs (tarray tuchar (Zlength buf - (off + n)))
           (zbytes (sublist (off + n) (Zlength buf) buf)) (offset_val (off + n) (Vptr b0 i0));
         zstd_globals gv)).
  { (* n >= 8 *)
    forward. forward.
    forward_call (shs, offset_val off (Vptr b0 i0), s, n - 8).
    { entailer!. rewrite bi_ptr_eq by rep_lia. simpl. repeat f_equal; lia. }
    { rewrite Hs. cancel. }
    { split; auto. split; [lia|]. split; [lia|]. apply Forall_sublist. auto. }
    rewrite Hs, bi_ptr_eq by rep_lia.
    forward.
    assert (Hb: 0 <= Znth (n-1) s <= Byte.max_unsigned) by (apply bi_byte; auto; lia).
    forward.
    { entailer!. apply Hb. }
    forward. rewrite bi_zext by auto.
    forward_if (temp _t'2 (Vint (Int.repr (if Znth (n-1) s =? 0 then 0 else 8 - highbit (Znth (n-1) s))))).
    { apply bi_true in H5; auto.
      forward_call (Znth (n-1) s, gv).
      forward. entailer!. rewrite (proj2 (Z.eqb_neq _ _) H5). reflexivity. }
    { apply bi_false in H5; auto.
      forward. entailer!. rewrite H5. reflexivity. }
    forward.
    forward_if.
    { forward.
      assert (Hwf: bs_wf s = false) by (rewrite bi_bs_wf by lia; rewrite Hs, H5; reflexivity).
      Exists (2^64 - 1). rewrite Hwf. cbv iota.
      entailer!.
      { f_equal. apply Int64.eqm_samerepr. exists (-1). reflexivity. }
      unfold bit_src. rewrite (bi_src_split3 shs (Vptr b0 i0) buf off n) by (auto; lia). fold s.
      cancel. }
    { forward.
      assert (Hwf: bs_wf s = true)
        by (rewrite bi_bs_wf by lia; rewrite Hs; apply Bool.negb_true_iff, Z.eqb_neq; auto).
      rewrite (proj2 (Z.eqb_neq _ _) H5).
      assert (Hb1: 1 <= Znth (n-1) s <= Byte.max_unsigned) by rep_lia.
      pose proof (bi_highbit (Znth (n-1) s) Hb1).
      pose proof (bi_bitC_big s H2 ltac:(lia)) as HC. rewrite Hs in HC.
      unfold BIT_DStream_rep. rewrite Z.max_r by lia. rewrite HC, bi_bs_total by lia. rewrite Hs.
      Exists (offset_val (off + (n - 8)) (Vptr b0 i0))
        (Vptr b0 (Ptrofs.add (Ptrofs.add i0 (Ptrofs.repr off))
              (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_int64 (Ptrofs.to_int64 (Ptrofs.repr 8)))))).
      entailer!.
      { assert (E: 8 * (n - 8) / 8 = n - 8) by (rewrite Z.mul_comm, Z.div_mul; lia).
        split.
        - unfold bit_inv. rewrite Hs, E, Z.max_r by lia.
          split; [auto|]. split; [lia|]. split; [lia|].
          split. { rewrite Z.mul_comm, Z_mod_mult. reflexivity. }
          split; [lia|]. split; rep_lia.
        - left. rewrite E. reflexivity. }
      replace (8 * (n - 8) + 64 - (8 * (n - 1) + highbit (Znth (n - 1) s)))
        with (8 - highbit (Znth (n - 1) s)) by lia.
      apply derives_refl. } }
  { (* n < 8 *)
    assert (Hb0: 0 <= Znth 0 s <= Byte.max_unsigned) by (apply bi_byte; auto; lia).
    forward. forward. forward.
    assert_PROP (field_compatible (tarray tuchar n) [] (offset_val off (Vptr b0 i0))) as FCs.
    { entailer!. rewrite H8 in H10. exact H10. }
    rewrite (bi_split_first shs n (zbytes s)) by (auto; list_solve). Intros.
    forward.
    { entailer!. apply Hb0. }
    gather_SEP (data_at shs tuchar _ _) (data_at shs (tarray tuchar (n - 1)) _ _).
    rewrite <- (bi_split_first shs n (zbytes s)) by (auto; list_solve).
    forward.
    assert (Hbytes: forall i, 0 <= i < n -> 0 <= Znth i s <= Byte.max_unsigned)
      by (intros; apply bi_byte; auto; lia).
    rewrite Int.unsigned_repr by rep_lia.
    forward_if (PROP ()
      LOCAL (gvars gv; temp _bitD p; temp _srcBuffer (offset_val off (Vptr b0 i0));
             temp _srcSize (Vlong (Int64.repr n)))
      SEP (data_at shs (tarray tuchar n) (zbytes s) (offset_val off (Vptr b0 i0));
           data_at sh (Tstruct ___gp_BIT_DStream_t noattr)
             (Vlong (Int64.repr (le_value s)),
              (fst (snd (default_val (Tstruct ___gp_BIT_DStream_t noattr))),
               (offset_val off (Vptr b0 i0),
                (offset_val off (Vptr b0 i0),
                 Vptr b0
                   (Ptrofs.add (Ptrofs.add i0 (Ptrofs.repr off))
                      (Ptrofs.mul (Ptrofs.repr 1)
                         (Ptrofs.of_int64 (Ptrofs.to_int64 (Ptrofs.repr 8))))))))) p;
           data_at shs (tarray tuchar off) (zbytes (sublist 0 off buf)) (Vptr b0 i0);
           data_at shs (tarray tuchar (Zlength buf - (off + n)))
             (zbytes (sublist (off + n) (Zlength buf) buf))
             (offset_val (off + n) (Vptr b0 i0)); zstd_globals gv)).
    { bi_byte 48. bi_byte 40. bi_byte 32. bi_byte 24. bi_byte 16. bi_byte 8. bi_fin Hs E. }
    { bi_byte 40. bi_byte 32. bi_byte 24. bi_byte 16. bi_byte 8. bi_fin Hs E. }
    { bi_byte 32. bi_byte 24. bi_byte 16. bi_byte 8. bi_fin Hs E. }
    { bi_byte 24. bi_byte 16. bi_byte 8. bi_fin Hs E. }
    { bi_byte 16. bi_byte 8. bi_fin Hs E. }
    { bi_byte 8. bi_fin Hs E. }
    { assert (E: n = 1).
      { repeat match goal with H: Int.unsigned (Int.repr n) <> _ |- _ =>
          rewrite !Int.unsigned_repr in H by rep_lia end. lia. }
      bi_fin Hs E. }
    assert (Hb: 0 <= Znth (n-1) s <= Byte.max_unsigned) by (apply Hbytes; lia).
    forward.
    { entailer!. try rewrite Int.unsigned_repr by rep_lia; apply Hb. }
    forward. rewrite bi_zext by auto.
    forward_if (temp _t'4 (Vint (Int.repr (if Znth (n-1) s =? 0 then 0 else 8 - highbit (Znth (n-1) s))))).
    { match goal with Ht: typed_true _ _ |- _ => apply bi_true in Ht; auto; rename Ht into Hnz end.
      forward_call (Znth (n-1) s, gv).
      forward. entailer!. rewrite (proj2 (Z.eqb_neq _ _) Hnz). reflexivity. }
    { match goal with Ht: typed_false _ _ |- _ => apply bi_false in Ht; auto; rename Ht into Hz end.
      forward. entailer!. rewrite Hz. reflexivity. }
    forward.
    forward_if.
    { forward.
      match goal with Hz: Znth (n - 1) s = 0 |- _ =>
        assert (Hwf: bs_wf s = false) by (rewrite bi_bs_wf by lia; rewrite Hs, Hz; reflexivity) end.
      Exists (2^64 - 20). rewrite Hwf. cbv iota.
      entailer!.
      { f_equal. apply Int64.eqm_samerepr. exists (-1). reflexivity. }
      unfold bit_src. rewrite (bi_src_split3 shs (Vptr b0 i0) buf off n) by (auto; lia). fold s.
      cancel. }
    match goal with Hnz: Znth (n - 1) s <> 0 |- _ => rename Hnz into H5 end.
    forward. forward.
    assert (Hwf: bs_wf s = true)
      by (rewrite bi_bs_wf by lia; rewrite Hs; apply Bool.negb_true_iff, Z.eqb_neq; auto).
    rewrite (proj2 (Z.eqb_neq _ _) H5).
    assert (Hb1: 1 <= Znth (n-1) s <= Byte.max_unsigned) by rep_lia.
    pose proof (bi_highbit (Znth (n-1) s) Hb1).
    assert (Hbits: Int.add (Int.repr (8 - highbit (Znth (n - 1) s)))
              (Int.mul (Int.repr (Int64.Z_mod_modulus (8 - Int64.Z_mod_modulus n))) (Int.repr 8)) =
            Int.repr (0 + 64 - (8 * (n - 1) + highbit (Znth (n - 1) s)))).
    { rewrite !Int64.Z_mod_modulus_eq. rewrite (Z.mod_small n) by rep_lia.
      rewrite (Z.mod_small (8 - n)) by rep_lia. rewrite mul_repr, add_repr. f_equal. lia. }
    rewrite Hbits.
    unfold BIT_DStream_rep. rewrite Z.max_l by lia. rewrite Z.mul_0_r.
    rewrite bi_bitC_small by (auto; lia). rewrite bi_bs_total by lia. rewrite Hs.
    Exists (offset_val off (Vptr b0 i0))
      (Vptr b0 (Ptrofs.add (Ptrofs.add i0 (Ptrofs.repr off))
            (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_int64 (Ptrofs.to_int64 (Ptrofs.repr 8)))))).
    entailer!.
    unfold bit_inv. rewrite Hs. rewrite Z.max_l by lia.
    repeat split; auto; try rep_lia.
    all: rewrite Zdiv_0_l; lia. }
  Intros. forward.
  Exists n. match goal with Hw: bs_wf s = true |- _ => rewrite Hw end. cbv iota.
  entailer!.
  unfold bit_src. rewrite (bi_src_split3 shs (Vptr b0 i0) buf off n) by (auto; lia). fold s.
  cancel.
Qed.

Lemma v2_body_BIT_skipBits: semax_body Vprog Gprog f_BIT_skipBits BIT_skipBits_spec.
Proof.
  start_function. destruct np; unfold BIT_DStream_rep_g.
  - unfold BIT_DStream_rep_np. Intros lim.
    forward. forward.
    unfold BIT_DStream_rep_g, BIT_DStream_rep_np. Exists lim. rewrite add_repr.
    replace (lo + 64 - pos + nb) with (lo + 64 - (pos - nb)) by lia.
    unfold bit_inv in *. entailer!. destruct H1 as (? & ? & ? & ? & ? & ? & ?). repeat split; auto; lia.
  - unfold BIT_DStream_rep. Intros ptr lim.
    forward. forward.
    unfold BIT_DStream_rep_g, BIT_DStream_rep. Exists ptr lim. rewrite add_repr.
    replace (lo + 64 - pos + nb) with (lo + 64 - (pos - nb)) by lia.
    unfold bit_inv in *. entailer!. split. tauto.
    destruct H2 as [? | [? ?]]; [left; auto | right; split; auto; lia].
Qed.

Lemma v2_body_BIT_lookBitsFast: semax_body Vprog Gprog f_BIT_lookBitsFast BIT_lookBitsFast_spec.
Proof.
  start_function. destruct np; unfold BIT_DStream_rep_g.
{ unfold BIT_DStream_rep_np. Intros lim.
  assert (Hinv := H0). destruct Hinv as (? & ? & ? & ? & ? & ? & ?).
  pose proof (br_C_range s lo) as HC.
  assert (0 <= (lo + 64 - pos) mod 64 < 64) by (apply Z.mod_pos_bound; lia).
  forward. forward. forward. forward.
  - entailer!. change (Int.unsigned Int64.iwordsize') with 64.
    rewrite !br_land63 by lia. rewrite !Int.unsigned_repr by (try pose proof (Z.mod_pos_bound (63 + 1 - nb) 64); rep_lia).
    split; [apply Z.mod_pos_bound | ]; lia.
  - set (x := (Z.shiftl (bit_C s lo) ((lo + 64 - pos) mod 64)) mod 2 ^ 64).
    assert (0 <= x < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
    Exists (Z.shiftr x (64 - nb)).
    unfold BIT_DStream_rep_g, BIT_DStream_rep_np. Exists lim. entailer!.
    split3.
    + rewrite Z.shiftr_div_pow2 by lia. split. apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia].
      apply Z.div_lt_upper_bound. apply Z.pow_pos_nonneg; lia.
      rewrite <- Z.pow_add_r by lia. replace (64 - nb + nb) with 64 by lia. lia.
    + intros. unfold x, bit_C. apply br_fast; auto; lia.
    + simpl. rewrite !br_land63 by lia.
      rewrite (Int.unsigned_repr ((lo + 64 - pos) mod 64)) by rep_lia.
      rewrite (Z.mod_small (63 + 1 - nb)) by lia.
      rewrite (Int.unsigned_repr (63 + 1 - nb)) by rep_lia.
      unfold Int64.shru, Int64.shl. rewrite (Int64.unsigned_repr (bit_C s lo)) by lia.
      rewrite (Int64.unsigned_repr ((lo + 64 - pos) mod 64)) by rep_lia.
      rewrite Int64.unsigned_repr_eq. change Int64.modulus with (2 ^ 64). fold x.
      rewrite (Int64.unsigned_repr (63 + 1 - nb)) by rep_lia.
      replace (63 + 1 - nb) with (64 - nb) by lia. reflexivity.
}
{ unfold BIT_DStream_rep. Intros ptr lim.
  assert (Hinv := H0). destruct Hinv as (? & ? & ? & ? & ? & ? & ?).
  pose proof (br_C_range s lo) as HC.
  assert (0 <= (lo + 64 - pos) mod 64 < 64) by (apply Z.mod_pos_bound; lia).
  forward. forward. forward. forward.
  - entailer!. change (Int.unsigned Int64.iwordsize') with 64.
    rewrite !br_land63 by lia. rewrite !Int.unsigned_repr by (try pose proof (Z.mod_pos_bound (63 + 1 - nb) 64); rep_lia).
    split; [apply Z.mod_pos_bound | ]; lia.
  - set (x := (Z.shiftl (bit_C s lo) ((lo + 64 - pos) mod 64)) mod 2 ^ 64).
    assert (0 <= x < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
    Exists (Z.shiftr x (64 - nb)).
    unfold BIT_DStream_rep_g, BIT_DStream_rep. Exists ptr lim. entailer!.
    split3.
    + rewrite Z.shiftr_div_pow2 by lia. split. apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia].
      apply Z.div_lt_upper_bound. apply Z.pow_pos_nonneg; lia.
      rewrite <- Z.pow_add_r by lia. replace (64 - nb + nb) with 64 by lia. lia.
    + intros. unfold x, bit_C. apply br_fast; auto; lia.
    + simpl. rewrite !br_land63 by lia.
      rewrite (Int.unsigned_repr ((lo + 64 - pos) mod 64)) by rep_lia.
      rewrite (Z.mod_small (63 + 1 - nb)) by lia.
      rewrite (Int.unsigned_repr (63 + 1 - nb)) by rep_lia.
      unfold Int64.shru, Int64.shl. rewrite (Int64.unsigned_repr (bit_C s lo)) by lia.
      rewrite (Int64.unsigned_repr ((lo + 64 - pos) mod 64)) by rep_lia.
      rewrite Int64.unsigned_repr_eq. change Int64.modulus with (2 ^ 64). fold x.
      rewrite (Int64.unsigned_repr (63 + 1 - nb)) by rep_lia.
      replace (63 + 1 - nb) with (64 - nb) by lia. reflexivity.
}
Qed.

Lemma v2_body_BIT_readBits: semax_body Vprog Gprog f_BIT_readBits BIT_readBits_spec.
Proof.
  start_function.
  forward_call (sh, p, gv, s, start, pos, lo, nb).
  Intros r.
  forward_call (sh, p, gv, s, start, pos, lo, nb, false).
  { unfold BIT_DStream_rep_g. cancel. }
  unfold BIT_DStream_rep_g.
  forward.
  Exists r. entailer!.
Qed.

Lemma v2_body_BIT_readBitsFast: semax_body Vprog Gprog f_BIT_readBitsFast BIT_readBitsFast_spec.
Proof.
  start_function.
  forward_call (sh, p, gv, s, start, pos, lo, nb, false).
  { unfold BIT_DStream_rep_g. cancel. }
  Intros r. unfold BIT_DStream_rep_g.
  forward_call (sh, p, gv, s, start, pos, lo, nb, false).
  { unfold BIT_DStream_rep_g. cancel. }
  unfold BIT_DStream_rep_g.
  forward.
  (* the peek's exact value (BIT_lookBitsFast_spec's last PROP) replaced r *)
  Exists (Z.shiftr ((Z.shiftl (bit_C s lo) ((lo + 64 - pos) mod 64)) mod 2 ^ 64) (64 - nb)). entailer!.
Qed.

Lemma v2_body_BIT_reloadDStreamFast :
  semax_body Vprog Gprog f_BIT_reloadDStreamFast BIT_reloadDStreamFast_spec.
Proof.
  start_function.
  unfold BIT_DStream_rep_np. Intros lim.
  pose proof H1 as Hinv.
  destruct H1 as (Hok & Hn & Hlo0 & Hlom & Hlok & Hpos & Hbc).
  rename H0 into Hpre.
  pose proof H as Hsrc.
  destruct H as (Hst & Hoff & Hlen & Hsub). subst start.
  unfold bit_src. assert_PROP (isptr bp) as Hbp by entailer!.
  rewrite offset_offset_val.
  remember (lo / 8) as k eqn:Hk.
  assert (Hlo: lo = 8 * k) by (pose proof (Z.div_mod lo 8 ltac:(lia)); lia).
  forward. forward.
  destruct bp as [| | | | | b o]; try contradiction.
  assert_PROP (Ptrofs.unsigned o + Zlength buf < Ptrofs.modulus) as Hbo.
  { entailer!. match goal with H: field_compatible _ _ _ |- _ => destruct H as (_ & _ & Hsz & _) end.
    simpl in Hsz. rewrite Z.max_r in Hsz by rep_lia. lia. }
  assert (Hkn: k <= Zlength s) by lia.
  forward_if.
  { entailer!. unfold sameblock. destruct (peq b b); [exact I | congruence]. }
  { change (Vptr b (Ptrofs.add o (Ptrofs.repr (off + k)))) with (offset_val (off + k) (Vptr b o)) in H.
    change (Vptr b (Ptrofs.add o (Ptrofs.repr off))) with (offset_val off (Vptr b o)) in H.
    rewrite br_sub_pp in H by rep_lia. replace (off + k - off) with k in H by lia.
    simpl in H. unfold Int64.ltu in H. rewrite !Int64.unsigned_repr in H by rep_lia.
    change (Int64.unsigned (Ptrofs.to_int64 (Ptrofs.repr 8))) with 8 in H.
    destruct (zlt k 8); [| unfold typed_true in H; simpl in H; discriminate].
    forward. unfold bs_reload_fast. rewrite <- Hk. destruct (Z.ltb_spec k 8); [| lia].
    simpl fst; simpl snd. unfold BIT_DStream_rep_np. Exists lim.
    entailer!. rewrite <- Hk. apply derives_refl. }
  { change (Vptr b (Ptrofs.add o (Ptrofs.repr (off + k)))) with (offset_val (off + k) (Vptr b o)) in H.
    change (Vptr b (Ptrofs.add o (Ptrofs.repr off))) with (offset_val off (Vptr b o)) in H.
    rewrite br_sub_pp in H by rep_lia. replace (off + k - off) with k in H by lia.
    simpl in H. unfold Int64.ltu in H. rewrite !Int64.unsigned_repr in H by rep_lia.
    change (Int64.unsigned (Ptrofs.to_int64 (Ptrofs.repr 8))) with 8 in H.
    destruct (zlt k 8); [unfold typed_false in H; simpl in H; discriminate |].
    assert (Hlp: lo <= pos) by (destruct Hpre; lia).
    forward_call (sh, p, gv, s, offset_val off (Vptr b o), pos, lo, shs, Vptr b o, buf, off).
    { unfold BIT_DStream_rep. Exists (offset_val (off + k) (Vptr b o)) lim. entailer!.
      left. rewrite <- Hk. reflexivity. }
    forward. unfold bs_reload_fast. rewrite <- Hk. destruct (Z.ltb_spec k 8); [lia |].
    simpl fst; simpl snd. entailer!.
    apply BIT_DStream_rep_rep_np.
    pose proof (Z.mod_pos_bound (8 * k + 64 - pos) 8 ltac:(lia)).
    pose proof (Z.div_mod (8 * k + 64 - pos) 8 ltac:(lia)).
    change (let (q, _) := Z.div_eucl (8 * k + 64 - pos) 8 in q) with ((8 * k + 64 - pos) / 8). lia. }
Qed.

Lemma bodies_util_bits :
  semax_body Vprog Gprog f_ZSTD_wrappedPtrAdd ZSTD_wrappedPtrAdd_spec /\
  semax_body Vprog Gprog f_ZSTD_wrappedPtrSub ZSTD_wrappedPtrSub_spec /\
  semax_body Vprog Gprog f_ZSTD_maybeNullPtrAdd ZSTD_maybeNullPtrAdd_spec /\
  semax_body Vprog Gprog f_MEM_32bits MEM_32bits_spec /\
  semax_body Vprog Gprog f_MEM_64bits MEM_64bits_spec /\
  semax_body Vprog Gprog f_MEM_isLittleEndian MEM_isLittleEndian_spec /\
  semax_body Vprog Gprog f_MEM_read16 MEM_read16_spec /\
  semax_body Vprog Gprog f_MEM_read32 MEM_read32_spec /\
  semax_body Vprog Gprog f_MEM_read64 MEM_read64_spec /\
  semax_body Vprog Gprog f_MEM_write16 MEM_write16_spec /\
  semax_body Vprog Gprog f_MEM_write32 MEM_write32_spec /\
  semax_body Vprog Gprog f_MEM_write64 MEM_write64_spec /\
  semax_body Vprog Gprog f_MEM_swap32_fallback MEM_swap32_fallback_spec /\
  semax_body Vprog Gprog f_MEM_swap32 MEM_swap32_spec /\
  semax_body Vprog Gprog f_MEM_swap64_fallback MEM_swap64_fallback_spec /\
  semax_body Vprog Gprog f_MEM_swap64 MEM_swap64_spec /\
  semax_body Vprog Gprog f_MEM_readLE16 MEM_readLE16_spec /\
  semax_body Vprog Gprog f_MEM_readLE24 MEM_readLE24_spec /\
  semax_body Vprog Gprog f_MEM_readLE32 MEM_readLE32_spec /\
  semax_body Vprog Gprog f_MEM_writeLE32 MEM_writeLE32_spec /\
  semax_body Vprog Gprog f_MEM_readLE64 MEM_readLE64_spec /\
  semax_body Vprog Gprog f_MEM_readLEST MEM_readLEST_spec /\
  semax_body Vprog Gprog f_ERR_isError ERR_isError_spec /\
  semax_body Vprog Gprog f_ERR_getErrorCode ERR_getErrorCode_spec /\
  semax_body Vprog Gprog f__force_has_format_string _force_has_format_string_spec /\
  semax_body Vprog Gprog f_ZSTD_countTrailingZeros32_fallback ZSTD_countTrailingZeros32_fallback_spec /\
  semax_body Vprog Gprog f_ZSTD_countTrailingZeros32 ZSTD_countTrailingZeros32_spec /\
  semax_body Vprog Gprog f_ZSTD_countLeadingZeros32_fallback ZSTD_countLeadingZeros32_fallback_spec /\
  semax_body Vprog Gprog f_ZSTD_countLeadingZeros32 ZSTD_countLeadingZeros32_spec /\
  semax_body Vprog Gprog f_ZSTD_countTrailingZeros64 ZSTD_countTrailingZeros64_spec /\
  semax_body Vprog Gprog f_ZSTD_highbit32 ZSTD_highbit32_spec /\
  semax_body Vprog Gprog f_FSE_isError FSE_isError_spec /\
  semax_body Vprog Gprog f_ZSTD_copy8 ZSTD_copy8_spec /\
  semax_body Vprog Gprog f_ZSTD_copy16 ZSTD_copy16_spec /\
  semax_body Vprog Gprog f_ZSTD_isError ZSTD_isError_spec /\
  semax_body Vprog Gprog f_ZSTD_getErrorCode ZSTD_getErrorCode_spec /\
  semax_body Vprog Gprog f_ZSTD_DCtx_get_bmi2 ZSTD_DCtx_get_bmi2_spec /\
  semax_body Vprog Gprog f_ZSTD_copy4 ZSTD_copy4_spec /\
  semax_body Vprog Gprog f_BIT_initDStream BIT_initDStream_spec /\
  semax_body Vprog Gprog f_BIT_getMiddleBits BIT_getMiddleBits_spec /\
  semax_body Vprog Gprog f_BIT_lookBits BIT_lookBits_spec /\
  semax_body Vprog Gprog f_BIT_lookBitsFast BIT_lookBitsFast_spec /\
  semax_body Vprog Gprog f_BIT_skipBits BIT_skipBits_spec /\
  semax_body Vprog Gprog f_BIT_readBits BIT_readBits_spec /\
  semax_body Vprog Gprog f_BIT_readBitsFast BIT_readBitsFast_spec /\
  semax_body Vprog Gprog f_BIT_reloadDStream_internal BIT_reloadDStream_internal_spec /\
  semax_body Vprog Gprog f_BIT_reloadDStreamFast BIT_reloadDStreamFast_spec /\
  semax_body Vprog Gprog f_BIT_reloadDStream BIT_reloadDStream_spec /\
  semax_body Vprog Gprog f_BIT_endOfDStream BIT_endOfDStream_spec.
Proof.
  pose proof bodies_util_mem. pose proof body_MEM_write64. pose proof bodies_util_count.
  pose proof bodies_util_misc. pose proof v2_body_BIT_initDStream.
  pose proof body_BIT_reloadDStream_internal. pose proof v2_body_BIT_reloadDStreamFast.
  pose proof body_BIT_reloadDStream. pose proof body_BIT_endOfDStream.
  pose proof body_BIT_getMiddleBits. pose proof body_BIT_lookBits. pose proof v2_body_BIT_lookBitsFast.
  pose proof v2_body_BIT_skipBits. pose proof v2_body_BIT_readBits. pose proof v2_body_BIT_readBitsFast.
  repeat match goal with H: _ /\ _ |- _ => destruct H end.
  repeat match goal with |- semax_body _ _ _ _ /\ _ =>
    split; [first [assumption | apply semax_body_vacuous] | ] end;
  assumption.
Qed.