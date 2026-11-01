(* Group ENT: body of FSE_decompress_wksp_body. *)
Require Import Zstd.proof.dec.B.ent.EntSpecs.
Local Open Scope logic.

(* ---------- memory: the U32 workspace as the ncount shorts, the dtable and the rest ---------- *)

Lemma ew_fc_align4 : forall n b ofs, 0 < n -> field_compatible (tarray tuint n) nil (Vptr b ofs) ->
  (4 | Ptrofs.unsigned ofs).
Proof.
  intros n b ofs Hn (_ & _ & _ & Ha & _).
  red in Ha. pose proof (align_compatible_rec_Tarray_inv _ _ _ _ _ Ha 0 ltac:(lia)) as H0.
  rewrite Z.mul_0_r, Z.add_0_r in H0. inv H0. inv H. assumption.
Qed.

Lemma ew_ac_short_arr z n : (2 | z) -> align_compatible_rec cenv_cs (tarray tshort n) z.
Proof.
  intros [k ->]. apply align_compatible_rec_Tarray. intros.
  eapply align_compatible_rec_by_value; [reflexivity | ]. simpl align_chunk.
  change (Ctypes.sizeof tshort) with 2. exists (k + i)%Z. lia.
Qed.

Lemma ew_ac_uint_arr z n : (4 | z) -> align_compatible_rec cenv_cs (tarray tuint n) z.
Proof.
  intros [k ->]. apply align_compatible_rec_Tarray. intros.
  eapply align_compatible_rec_by_value; [reflexivity | ]. simpl align_chunk.
  change (Ctypes.sizeof tuint) with 4. exists (k + i)%Z. lia.
Qed.

(* U32[n] = short[256] (the FSE_DecompressWksp) then U32[n - 128] *)
Lemma ew_split sh p n : 128 <= n ->
  data_at_ sh (tarray tuint n) p |--
  !! field_compatible (tarray tuint n) nil p &&
  (data_at_ sh (tarray tshort 256) p * data_at_ sh (tarray tuint (n - 128)) (offset_val 512 p)).
Proof.
  intros Hn. rewrite data_at__memory_block. Intros. rename H into Hfc.
  apply andp_right; [apply prop_right; auto | ].
  destruct p; try (destruct Hfc; contradiction).
  pose proof (ew_fc_align4 n b i ltac:(lia) Hfc) as Ha.
  destruct Hfc as (_ & _ & Hs & _ & _). red in Hs. simpl sizeof in *. rewrite Z.max_r in * by lia.
  pose proof (Ptrofs.unsigned_range i).
  rewrite <- (Ptrofs.repr_unsigned i).
  replace (4 * n)%Z with (512 + 4 * (n - 128))%Z at 1 by ring.
  rewrite memory_block_split by rep_lia. simpl offset_val.
  rewrite Ptrofs.add_unsigned, Ptrofs.unsigned_repr, (Ptrofs.unsigned_repr 512) by rep_lia.
  rewrite <- (memory_block_data_at_ sh (tarray tshort 256)), <- (memory_block_data_at_ sh (tarray tuint (n - 128))).
  simpl sizeof. rewrite !Z.max_r by lia. cancel.
  all: split3; [simpl; auto | reflexivity | ]; split3; [ | | simpl; auto]; red; rewrite ?Ptrofs.unsigned_repr by rep_lia.
  all: simpl sizeof; rewrite ?Z.max_r by lia; try lia.
  - apply ew_ac_uint_arr. destruct Ha as [k ->]. exists (k + 128)%Z. lia.
  - apply ew_ac_short_arr. destruct Ha as [k ->]. exists (2 * k)%Z. lia.
Qed.

Lemma ew_join sh p n : 128 <= n -> field_compatible (tarray tuint n) nil p ->
  data_at_ sh (tarray tshort 256) p * data_at_ sh (tarray tuint (n - 128)) (offset_val 512 p) |--
  data_at_ sh (tarray tuint n) p.
Proof.
  intros Hn Hfc. rewrite (data_at__memory_block sh (tarray tuint n)). apply andp_right; [apply prop_right; auto | ].
  destruct p; try (destruct Hfc; contradiction).
  destruct Hfc as (_ & _ & Hs & _ & _). red in Hs. simpl sizeof in *. rewrite Z.max_r in * by lia.
  pose proof (Ptrofs.unsigned_range i).
  rewrite <- (Ptrofs.repr_unsigned i).
  replace (4 * n)%Z with (512 + 4 * (n - 128))%Z by ring.
  rewrite memory_block_split by rep_lia. simpl offset_val.
  rewrite Ptrofs.add_unsigned, Ptrofs.unsigned_repr, (Ptrofs.unsigned_repr 512) by rep_lia.
  rewrite !data_at__memory_block. Intros. simpl sizeof. rewrite !Z.max_r by lia. cancel.
Qed.

(* the built table gives back its U32 region *)
Lemma ew_dt_join sh t fm dt : field_compatible (tarray tuint (1 + 2 ^ ft_log t)) nil dt ->
  fsedt_at sh t fm dt |-- data_at_ sh (tarray tuint (1 + 2 ^ ft_log t)) dt.
Proof.
  intros Hfc. unfold fsedt_at. Intros. destruct H as (Hl & _).
  assert (Hp: 1 <= 2 ^ ft_log t <= 4096) by (split; [pose proof (Z.pow_pos_nonneg 2 (ft_log t) ltac:(lia) ltac:(lia)); lia|
    change 4096 with (2 ^ 12); apply Z.pow_le_mono_r; lia]).
  sep_apply (data_at_data_at_ sh t_fhdr). sep_apply (data_at_data_at_ sh (tarray t_fdec (2 ^ ft_log t))).
  rewrite (data_at__memory_block sh (tarray tuint _)). apply andp_right; [apply prop_right; auto | ].
  rewrite !data_at__memory_block. Intros.
  destruct dt; try (destruct Hfc; contradiction).
  destruct Hfc as (_ & _ & Hs & _ & _). red in Hs. simpl sizeof in *. rewrite Z.max_r in * by lia.
  pose proof (Ptrofs.unsigned_range i).
  rewrite ?Z.max_r by lia. rewrite <- (Ptrofs.repr_unsigned i).
  replace (4 * (1 + 2 ^ ft_log t))%Z with (4 + 4 * 2 ^ ft_log t)%Z by ring.
  rewrite memory_block_split by rep_lia. simpl offset_val.
  rewrite Ptrofs.add_unsigned, Ptrofs.unsigned_repr by rep_lia. change (Ptrofs.unsigned (Ptrofs.repr 4)) with 4.
  rewrite sepcon_comm. apply derives_refl.
Qed.

Lemma ew_dt_fold sh t fm dt : fse_dt_ok t -> fm = 0 \/ fm = 1 ->
  data_at sh t_fhdr (Vint (Int.repr (ft_log t)), Vint (Int.repr fm)) dt *
  data_at sh (tarray t_fdec (2 ^ ft_log t)) (map fdcell (ft_cells t)) (offset_val 4 dt) |--
  fsedt_at sh t fm dt.
Proof. intros. unfold fsedt_at. entailer!. Qed.

(* the rest of the window after the description *)
Lemma ew_win sh N c off s size : win_ok sh N c off (Zlength s) s -> 0 <= size <= Zlength s ->
  win_ok sh N c (off + size) (Zlength (skipn (Z.to_nat size) s)) (skipn (Z.to_nat size) s) /\
  Zlength (skipn (Z.to_nat size) s) = Zlength s - size.
Proof.
  intros (Hsh & Hoff & Hend & HN & Hc & _ & Hbo & Hsub) Hsz.
  rewrite <- sublist_skip by lia.
  assert (Hl: Zlength (sublist size (Zlength s) s) = Zlength s - size) by (rewrite Zlength_sublist; lia).
  rewrite Hl. split; auto.
  unfold win_ok. repeat split; auto; try lia.
  - unfold bytes_ok in *. apply Forall_sublist; auto.
  - replace (off + size + (Zlength s - size)) with (off + Zlength s) by lia.
    rewrite <- sublist_map, <- Hsub. rewrite sublist_sublist by lia. f_equal; lia.
Qed.

Lemma ew_err44 : Vlong (Int64.repr (- (44))) = Vlong (Int64.repr (Int64.modulus - 44)).
Proof.
  f_equal. apply Int64.eqm_samerepr. red. red. exists (-1). change Int64.modulus with 18446744073709551616. lia.
Qed.

Lemma ew_shl1 log : 0 <= log <= 30 -> Int.shl (Int.repr 1) (Int.repr log) = Int.repr (2 ^ log).
Proof.
  intros. rewrite Int.shl_mul_two_p, Int.unsigned_repr by rep_lia.
  rewrite two_p_equiv, Int.mul_commut, Int.mul_one. reflexivity.
Qed.

Lemma ew_shl1L log : 0 <= log <= 62 -> Int64.shl (Int64.repr 1) (Int64.repr log) = Int64.repr (2 ^ log).
Proof.
  intros. rewrite Int64.shl_mul_two_p, Int64.unsigned_repr by rep_lia.
  rewrite two_p_equiv, Int64.mul_commut, Int64.mul_one. reflexivity.
Qed.

Lemma ew_pow log : 5 <= log <= 6 -> 32 <= 2 ^ log <= 64.
Proof.
  intros. split.
  - change 32 with (2 ^ 5). apply Z.pow_le_mono_r; lia.
  - change 64 with (2 ^ 6). apply Z.pow_le_mono_r; lia.
Qed.

(* FSE_DECOMPRESS_WKSP_SIZE(tableLog, maxSymbolValue) as the C computes it *)
Lemma ew_wksz log m : 5 <= log <= 6 -> 0 <= m <= 255 ->
  Int64.unsigned (Int64.mul (Int64.add (Int64.add (Int64.add
    (Int64.repr (Int.signed (Int.add (Int.add (Int.repr 1) (Int.shl (Int.repr 1) (Int.repr log))) (Int.repr 1))))
    (Int64.divu (Int64.sub (Int64.add (Int64.add (Int64.add
       (Int64.mul (Int64.repr 2) (Int64.repr (Int.unsigned (Int.repr (m + 1)))))
       (Int64.shl (Int64.repr 1) (Int64.repr (Int.unsigned (Int.repr log)))))
       (Int64.repr 8)) (Int64.repr 4)) (Int64.repr 1)) (Int64.repr 4)))
    (Int64.repr (Int.signed (Int.divs (Int.repr (255 + 1)) (Int.repr 2)))))
    (Int64.repr 1)) (Int64.repr 4))
  = fse_dwksp log m.
Proof.
  intros Hl Hm. pose proof (ew_pow log Hl) as Hp.
  rewrite ew_shl1 by lia. rewrite !add_repr. rewrite Int.signed_repr by rep_lia.
  rewrite !Int.unsigned_repr by rep_lia. rewrite ew_shl1L by lia.
  change (Int.signed (Int.divs (Int.repr (255 + 1)) (Int.repr 2))) with 128.
  rewrite mul64_repr, !add64_repr, sub64_repr.
  rewrite divu_repr64 by rep_lia.
  rewrite !add64_repr, mul64_repr.
  unfold fse_dwksp. set (P := 2 ^ log) in *. clearbody P.
  rewrite Int64.unsigned_repr.
  2: { pose proof (Z.div_pos (2 * (m + 1) + P + 8 + 4 - 1) 4 ltac:(lia) ltac:(lia)).
       pose proof (Z.div_le_upper_bound (2 * (m + 1) + P + 8 + 4 - 1) 4 1000 ltac:(lia) ltac:(lia)).
       split; [lia | change Int64.max_unsigned with 18446744073709551615; lia]. }
  replace (2 * (m + 1) + P + 8 + 4 - 1) with (2 * (m + 1) + P + 8 + 3) by lia. ring.
Qed.

Lemma ew_short_val (l: list Z) : Forall (fun x => -1 <= x <= 64) l ->
  map short_val l = map (fun x => Vint (Int.repr x)) l.
Proof.
  induction 1; simpl; auto. rewrite IHForall. f_equal. unfold short_val. f_equal.
  apply sign_ext_inrange. rewrite Int.signed_repr by rep_lia. simpl. lia.
Qed.

Ltac ew_tc :=
  entailer!; rewrite ?ew_shl1 by lia; rewrite ?add_repr; rewrite ?Int.signed_repr by rep_lia; simpl;
  change (Int.unsigned Int64.iwordsize') with 64; change (Int.unsigned Int.iwordsize) with 32; rep_lia.

(* the workspace back from its three regions at the end *)
Lemma ew_join_all sh p nk m (nc: list val) : 0 <= m <= nk - 128 -> Zlength nc = 256 ->
  field_compatible (tarray tuint nk) nil p -> field_compatible (tarray tuint (nk - 128)) nil (offset_val 512 p) ->
  data_at sh (tarray tshort (Zlength nc)) nc p * data_at_ sh (tarray tuint m) (offset_val 512 p) *
  data_at_ sh (tarray tuint (nk - 128 - m)) (offset_val (512 + 4 * m) p) |-- data_at_ sh (tarray tuint nk) p.
Proof.
  intros Hm Hnc FC FC2. rewrite Hnc.
  assert (Hfa: field_address0 (tarray tuint (nk - 128)) (SUB m) (offset_val 512 p) = offset_val (512 + 4 * m) p).
  { rewrite field_address0_offset by auto with field_compatible. rewrite offset_offset_val. f_equal; try (simpl; lia). }
  rewrite <- Hfa, sepcon_assoc, <- (split2_data_at__Tarray_app m (nk - 128) sh tuint (offset_val 512 p)) by lia.
  sep_apply (data_at_data_at_ sh (tarray tshort 256) nc p).
  apply ew_join; auto; lia.
Qed.

Ltac ew_close Hft FC FC2 nk m :=
  match goal with |- context [fsedt_at ?sh ?t ?fm ?dt] =>
    sep_apply (ew_dt_join sh t fm dt ltac:(rewrite Hft; auto)) end;
  rewrite Hft;
  match goal with |- context [data_at ?sh (tarray tshort (Zlength ?nc)) ?nc ?p] =>
    sep_apply (ew_join_all sh p nk m nc ltac:(lia) ltac:(auto) FC FC2) end;
  cancel.

Lemma body_ent_wksp : NCOUNT_RES_OK -> FSE_WF_SLOW ->
  semax_body Vprog
    (G_B0 ++ [FSE_readNCount_bmi2_spec; FSE_buildDTable_internal_spec; FSE_decompress_usingDTable_generic_spec])
    f_FSE_decompress_wksp_body FSE_decompress_wksp_body_spec.
Proof.
  intros Hnc Hwf.
  start_function.
  match goal with Hb: Zlength s <= 2 ^ 63 - 1 |- _ => rename Hb into Hslen end.
  forward. forward. forward. forward. forward. forward.
  assert_PROP (field_compatible (tarray tuint nk) [] pk) as FC by entailer!.
  destruct pk as [ | | | | | bk ok]; try (destruct FC; contradiction).
  forward_if.
  { exfalso; lia. }
  sep_apply (ew_split shk (Vptr bk ok) nk ltac:(lia)). Intros.
  forward_call (gv, shk, Vptr bk ok, 256, Tsh, v_maxSymbolValue, Tsh, v_tableLog, 255, sh, base, N, c, off, s).
  Intros vret. destruct vret as [[r nc] res]. simpl fst in *; simpl snd in *.
  match goal with Hr: nc_rel _ _ _ |- _ => rename Hr into Hrel end.
  match goal with Hx: res = x_ncount _ _ |- _ => rename Hx into Hxr end.
  match goal with Hm: match res with Some _ => _ | None => _ end |- _ => rename Hm into H5 end.
  destruct res as [[[norm log] size] | ].
  2: {
    forward_call r.
    rewrite H5.
    forward_if.
    2: { exfalso. discriminate. }
    forward.
    Exists r oc (@None (list Z * Z * Z)). cbn [weights_of].
    entailer!.
    sep_apply (data_at_data_at_ shk (tarray tshort 256) nc (Vptr bk ok)).
    sep_apply (ew_join shk (Vptr bk ok) nk ltac:(lia) FC). cancel.
  }
  assert (Hok: ncount_ok norm log 255 /\ size <= Zlength s).
  { unfold nc_rel in Hrel. destruct (Zlength s <? 8).
    - destruct Hrel as [_ [Hz Hk]]; split; [exact Hk | exact Hz].
    - symmetry in Hrel. destruct (Hnc s 255 norm log size ltac:(lia) Hrel) as [Hk Hz]. split; [exact Hk | lia]. }
  destruct Hok as [Hok Hsz].
  destruct H5 as [-> Hncs].
  pose proof Hok as (Hlog & Hlen & Hrng & Hsum).
  pose proof H0 as Hwin0.
  destruct H0 as (Hsh & Hoff & Hend & HN & Hc & _ & Hbo & Hsub).
  assert (Hne: is_error_code size = false).
  { unfold is_error_code. apply Z.ltb_ge. change (2 ^ 64 - 120) with 18446744073709551496. lia. }
  forward_call size.
  rewrite Hne.
  forward_if.
  { exfalso; lia. }
  Intros. forward.
  forward_if.
  { forward.
    Exists (Int64.modulus - 44) oc (Some (norm, log, size)). cbn [weights_of].
    replace (log >? 6) with true by (symmetry; apply Z.gtb_lt; lia).
    rewrite ew_err44.
    entailer!.
    sep_apply (data_at_data_at_ shk (tarray tshort 256) nc (Vptr bk ok)).
    sep_apply (ew_join shk (Vptr bk ok) nk ltac:(lia) FC). cancel.
  }
  forward. forward.
  forward. forward. forward.
  pose proof (ew_pow log ltac:(lia)) as Hp.
  forward_if.
  { entailer!. rewrite ew_shl1 by lia. rewrite !add_repr. rewrite !Int.signed_repr by rep_lia. simpl.
    change (Int.unsigned Int64.iwordsize') with 64. change (Int.unsigned Int.iwordsize) with 32. rep_lia. }
  { rewrite ew_wksz in H6 by lia. rewrite Int64.unsigned_repr in H6 by rep_lia.
    forward.
    Exists (Int64.modulus - 44) oc (Some (norm, log, size)). cbn [weights_of].
    replace (log >? 6) with false by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
    replace (fse_dwksp log (Zlength norm - 1) >? 4 * nk) with true by (symmetry; apply Z.gtb_lt; lia).
    rewrite ew_err44.
    entailer!.
    sep_apply (data_at_data_at_ shk (tarray tshort 256) nc (Vptr bk ok)).
    sep_apply (ew_join shk (Vptr bk ok) nk ltac:(lia) FC). cancel.
  }
  rewrite ew_wksz in H6 by lia. rewrite Int64.unsigned_repr in H6 by rep_lia.
  forward. forward. 1: ew_tc. forward. forward. 1: ew_tc.
  assert_PROP (isptr base) as Pbase by entailer!.
  destruct base as [ | | | | | bb ob]; try contradiction.
  match goal with |- context [temp _wkspSize ?v] =>
    replace v with (Vlong (Int64.repr (4 * (nk - 128 - (1 + 2 ^ log))))) end.
  2: { rewrite ew_shl1 by lia. rewrite add_repr, Int.signed_repr by rep_lia.
       change (Ptrofs.to_int64 (Ptrofs.repr (sizeof (Tstruct ___gp_FSE_DecompressWksp noattr)))) with (Int64.repr 512).
       change (Ptrofs.to_int64 (Ptrofs.repr (sizeof tuint))) with (Int64.repr 4).
       rewrite mul64_repr, add64_repr, sub64_repr. f_equal. f_equal. lia. }
  match goal with |- context [temp _workSpace ?v] =>
    replace v with (offset_val (512 + 4 * (1 + 2 ^ log)) (Vptr bk ok)) end.
  2: { rewrite ew_shl1 by lia. rewrite add_repr, Int.signed_repr by rep_lia.
       change (Ptrofs.to_int64 (Ptrofs.repr (sizeof (Tstruct ___gp_FSE_DecompressWksp noattr)))) with (Int64.repr 512).
       change (Ptrofs.to_int64 (Ptrofs.repr (sizeof tuint))) with (Int64.repr 4).
       change (Ctypes.sizeof tuchar) with 1.
       rewrite mul64_repr. unfold Ptrofs.of_int64. rewrite !Int64.unsigned_repr by rep_lia.
       rewrite !ptrofs_mul_repr. simpl offset_val. f_equal.
       rewrite Ptrofs.add_assoc, ptrofs_add_repr. f_equal. f_equal. lia. }
  match goal with |- context [temp _dtable ?v] =>
    replace v with (offset_val 512 (Vptr bk ok)) end.
  2: { simpl. f_equal. }
  match goal with |- context [temp _ip ?v] =>
    replace v with (offset_val (off + size) (Vptr bb ob)) end.
  2: { simpl. f_equal. rewrite Ptrofs.add_assoc. f_equal. unfold Ptrofs.of_int64.
       rewrite Int64.unsigned_repr by rep_lia. rewrite ptrofs_mul_repr, ptrofs_add_repr. f_equal. lia. }
  rewrite sub64_repr.
  assert_PROP (field_compatible (tarray tuint (nk - 128)) [] (offset_val 512 (Vptr bk ok))) as FC2 by entailer!.
  rewrite (split2_data_at__Tarray_app (1 + 2 ^ log) (nk - 128) shk tuint (offset_val 512 (Vptr bk ok))) by lia.
  assert (Hfa: field_address0 (tarray tuint (nk - 128)) (SUB (1 + 2 ^ log)) (offset_val 512 (Vptr bk ok)) =
               offset_val (512 + 4 * (1 + 2 ^ log)) (Vptr bk ok)).
  { rewrite field_address0_offset by auto with field_compatible. rewrite offset_offset_val. f_equal; try (simpl; lia). }
  rewrite Hfa.
  assert_PROP (field_compatible (tarray tuint (1 + 2 ^ log)) [] (offset_val 512 (Vptr bk ok))) as FC3 by entailer!.
  assert (Ensh: data_at shk (tarray tshort 256) nc (Vptr bk ok) =
                data_at shk (tarray tshort (Zlength nc)) nc (Vptr bk ok)) by (rewrite H4; auto).
  rewrite Ensh.
  assert (Hnorm: sublist 0 (Zlength norm) nc = map (fun x => Vint (Int.repr x)) norm).
  { rewrite Hncs by (right; lia). apply ew_short_val. eapply Forall_impl; [ | exact Hrng]. simpl. intros; lia. }
  assert (HW: 2 * Zlength norm + 2 ^ log + 8 <= 4 * (nk - 128 - (1 + 2 ^ log)) <= Int.max_unsigned).
  { unfold fse_dwksp in H6. set (P := 2 ^ log) in *. clearbody P.
    pose proof (Z.mul_succ_div_gt (2 * (Zlength norm - 1 + 1) + P + 8 + 3) 4 ltac:(lia)).
    rep_lia. }
  forward_loop (PROP ( )
   LOCAL (temp _wkspSize (Vlong (Int64.repr (4 * (nk - 128 - (1 + 2 ^ log)))));
   temp _workSpace (offset_val (512 + 4 * (1 + 2 ^ log)) (Vptr bk ok));
   temp _cSrcSize (Vlong (Int64.repr (Zlength s - size)));
   temp _ip (offset_val (off + size) (Vptr bb ob));
   temp _dtable (offset_val 512 (Vptr bk ok));
   temp _wksp (Vptr bk ok);
   lvar _maxSymbolValue tuint v_maxSymbolValue;
   lvar _tableLog tuint v_tableLog; gvars gv; temp _dst pw;
   temp _dstCapacity (Vlong (Int64.repr 255)))
   SEP (zstd_globals gv; data_at shk (tarray tshort (Zlength nc)) nc (Vptr bk ok);
   data_at Tsh tuint (Vint (Int.repr (Zlength norm - 1))) v_maxSymbolValue;
   data_at Tsh tuint (Vint (Int.repr log)) v_tableLog;
   data_at sh (tarray tuchar N) c (Vptr bb ob);
   data_at_ shk (tarray tuint (1 + 2 ^ log)) (offset_val 512 (Vptr bk ok));
   data_at_ shk (tarray tuint (nk - 128 - (1 + 2 ^ log))) (offset_val (512 + 4 * (1 + 2 ^ log)) (Vptr bk ok));
   data_at shw (tarray tuchar 256) oc pw))
  continue: (PROP ( )
   LOCAL (temp _cSrcSize (Vlong (Int64.repr (Zlength s - size)));
   temp _ip (offset_val (off + size) (Vptr bb ob));
   temp _dtable (offset_val 512 (Vptr bk ok));
   lvar _maxSymbolValue tuint v_maxSymbolValue;
   lvar _tableLog tuint v_tableLog; gvars gv; temp _dst pw;
   temp _dstCapacity (Vlong (Int64.repr 255)))
   SEP (zstd_globals gv; data_at shk (tarray tshort (Zlength nc)) nc (Vptr bk ok);
   data_at Tsh tuint (Vint (Int.repr (Zlength norm - 1))) v_maxSymbolValue;
   data_at Tsh tuint (Vint (Int.repr log)) v_tableLog;
   data_at sh (tarray tuchar N) c (Vptr bb ob);
   fsedt_at shk (fse_build norm log) (fse_fm norm log) (offset_val 512 (Vptr bk ok));
   data_at_ shk (tarray tuint (nk - 128 - (1 + 2 ^ log))) (offset_val (512 + 4 * (1 + 2 ^ log)) (Vptr bk ok));
   data_at shw (tarray tuchar 256) oc pw))
  break: (PROP ( )
   LOCAL (temp _cSrcSize (Vlong (Int64.repr (Zlength s - size)));
   temp _ip (offset_val (off + size) (Vptr bb ob));
   temp _dtable (offset_val 512 (Vptr bk ok));
   lvar _maxSymbolValue tuint v_maxSymbolValue;
   lvar _tableLog tuint v_tableLog; gvars gv; temp _dst pw;
   temp _dstCapacity (Vlong (Int64.repr 255)))
   SEP (zstd_globals gv; data_at shk (tarray tshort (Zlength nc)) nc (Vptr bk ok);
   data_at Tsh tuint (Vint (Int.repr (Zlength norm - 1))) v_maxSymbolValue;
   data_at Tsh tuint (Vint (Int.repr log)) v_tableLog;
   data_at sh (tarray tuchar N) c (Vptr bb ob);
   fsedt_at shk (fse_build norm log) (fse_fm norm log) (offset_val 512 (Vptr bk ok));
   data_at_ shk (tarray tuint (nk - 128 - (1 + 2 ^ log))) (offset_val (512 + 4 * (1 + 2 ^ log)) (Vptr bk ok));
   data_at shw (tarray tuchar 256) oc pw)).
  { entailer!. }
  { forward. forward.
    forward_call (gv, shk, offset_val 512 (Vptr bk ok), shk, Vptr bk ok, nc, norm, log, shk,
                  offset_val (512 + 4 * (1 + 2 ^ log)) (Vptr bk ok), nk - 128 - (1 + 2 ^ log)).
    forward.
    forward_loop (PROP ( )
     LOCAL (temp __var_err__ (Vlong (Int64.repr 0));
     temp _cSrcSize (Vlong (Int64.repr (Zlength s - size)));
     temp _ip (offset_val (off + size) (Vptr bb ob));
     temp _dtable (offset_val 512 (Vptr bk ok));
     lvar _maxSymbolValue tuint v_maxSymbolValue;
     lvar _tableLog tuint v_tableLog; gvars gv; temp _dst pw;
     temp _dstCapacity (Vlong (Int64.repr 255)))
     SEP (zstd_globals gv; data_at shk (tarray tshort (Zlength nc)) nc (Vptr bk ok);
     data_at Tsh tuint (Vint (Int.repr (Zlength norm - 1))) v_maxSymbolValue;
     data_at Tsh tuint (Vint (Int.repr log)) v_tableLog;
     data_at sh (tarray tuchar N) c (Vptr bb ob);
     fsedt_at shk (fse_build norm log) (fse_fm norm log) (offset_val 512 (Vptr bk ok));
     data_at_ shk (tarray tuint (nk - 128 - (1 + 2 ^ log))) (offset_val (512 + 4 * (1 + 2 ^ log)) (Vptr bk ok));
     data_at shw (tarray tuchar 256) oc pw))
    break: (PROP ( )
     LOCAL (temp _cSrcSize (Vlong (Int64.repr (Zlength s - size)));
     temp _ip (offset_val (off + size) (Vptr bb ob));
     temp _dtable (offset_val 512 (Vptr bk ok));
     lvar _maxSymbolValue tuint v_maxSymbolValue;
     lvar _tableLog tuint v_tableLog; gvars gv; temp _dst pw;
     temp _dstCapacity (Vlong (Int64.repr 255)))
     SEP (zstd_globals gv; data_at shk (tarray tshort (Zlength nc)) nc (Vptr bk ok);
     data_at Tsh tuint (Vint (Int.repr (Zlength norm - 1))) v_maxSymbolValue;
     data_at Tsh tuint (Vint (Int.repr log)) v_tableLog;
     data_at sh (tarray tuchar N) c (Vptr bb ob);
     fsedt_at shk (fse_build norm log) (fse_fm norm log) (offset_val 512 (Vptr bk ok));
     data_at_ shk (tarray tuint (nk - 128 - (1 + 2 ^ log))) (offset_val (512 + 4 * (1 + 2 ^ log)) (Vptr bk ok));
     data_at shw (tarray tuchar 256) oc pw)).
    { entailer!. }
    { forward_call 0. change (is_error_code 0) with false. forward_if.
      { exfalso. first [lia | contradiction | (simpl in *; lia)]. }
      forward. entailer!. }
  }
  { forward. entailer!. }
  pose proof (Hwf norm log 255 Hok) as (Hft & Hcl & Hcells & Hfm1 & _).
  assert_PROP (fse_dt_ok (fse_build norm log) /\ (fse_fm norm log = 0 \/ fse_fm norm log = 1)) as Hdt.
  { unfold fsedt_at. entailer!. }
  destruct (ew_win sh N c off s size Hwin0 ltac:(lia)) as [Hwin Hzs].
  unfold fsedt_at. Intros.
  forward. forward. forward.
  1: { entailer!. destruct Hdt as [_ [E | E]]; rewrite E; simpl; try rewrite Int.unsigned_repr by rep_lia; rep_lia. }
  sep_apply (ew_dt_fold shk (fse_build norm log) (fse_fm norm log) (offset_val 512 (Vptr bk ok)) H7 H8).
  assert (Hdw: (fse_dwksp log (Zlength norm - 1) >? 4 * nk) = false)
    by (rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
  assert (Hl6: (log >? 6) = false) by (rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
  forward_if.
  { assert (Hf1: fse_fm norm log = 1).
    { destruct H8 as [E | E]; auto. rewrite E in H9. exfalso. apply H9. reflexivity. }
    pose proof (Hfm1 Hf1) as Hnb. rewrite Hf1.
    forward_call (gv, shw, pw, oc, sh, Vptr bb ob, N, c, off + size, skipn (Z.to_nat size) s, shk,
                  offset_val 512 (Vptr bk ok), fse_build norm log, 1).
    1: { rewrite Hzs. entailer!. }
    Intros vret. destruct vret as [r oc']. simpl fst in *; simpl snd in *.
    forward.
    Exists r oc' (Some (norm, log, size)). cbn [weights_of]. rewrite Hl6, Hdw.
    entailer!.
    ew_close Hft FC FC2 nk (1 + 2 ^ log).
  }
  assert (Hf0: fse_fm norm log = 0).
  { destruct H8 as [E | E]; auto. rewrite E in H9. exfalso.
    apply (f_equal Int.unsigned) in H9. rewrite Int.unsigned_repr in H9 by rep_lia. discriminate. }
  rewrite Hf0.
  forward_call (gv, shw, pw, oc, sh, Vptr bb ob, N, c, off + size, skipn (Z.to_nat size) s, shk,
                offset_val 512 (Vptr bk ok), fse_build norm log, 0).
  1: { rewrite Hzs. entailer!. }
  Intros vret. destruct vret as [r oc']. simpl fst in *; simpl snd in *.
  forward.
  Exists r oc' (Some (norm, log, size)). cbn [weights_of]. rewrite Hl6, Hdw.
  entailer!.
  ew_close Hft FC FC2 nk (1 + 2 ^ log).
Qed.
