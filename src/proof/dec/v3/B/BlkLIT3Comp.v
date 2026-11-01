(* ZSTD_decodeLiteralsBlock, the arms set_compressed (a Huffman tree description, then one or four streams) and
   set_repeat (the previous table, after the litEntropy check): the header and its checks, the allocation of the
   literals buffer, the prefetch of the table, then the Huffman call (BlkLIT3Comp2.v), the split layout's copy and
   move (BlkLIT3Comp3.v) and the end (BlkLIT3Comp4.v); exactly as model/ExBlock.v (BlkLIT3Exact.lx_huf).  The
   parts are separate files to keep each compilation short. *)
Require Export Zstd.proof.dec.v3.B.BlkLIT3Comp4.
Local Open Scope logic.
Local Ltac solve_load_rule_evaluation ::= lit_slre.

Lemma seg_comp_tail (Espec: OracleKind) (gv: globals) (p: val) (fs: fstate) (ox: option ddx) (oh: option huf_table)
    (x2: bool) (lxb: list Z) (bsm streaming: Z) (W: list ptr_witness) (o0 o: outarr) (i: inwin) (e lh n cs: Z)
    (single: bool) :
  lit_hyps fs oh bsm streaming W o0 i -> lit_hyps fs oh bsm streaming W o i -> lit_o1 o0 o streaming bsm n ->
  lit_kfacts oh bsm (oa_cap o) e (iw_s i) lh n cs single -> Zlength lxb = LITEXTRA_N -> bytes_ok lxb ->
  lit_slack0 streaming (oa_cap o) bsm n (oa_d o) (oa_c o) ->
  semax lit_Delta (lit_J gv p fs ox oh x2 lxb bsm streaming W o i e lh n cs single) lit_tail
    (overridePost FF (switch_ret_assert (lit_R gv p fs ox oh x2 lxb bsm streaming W o0 i))).
Proof.
  intros HY0 HY HO HK Hlxb Hlxbb HS0. unfold lit_J. Intros r oc1 ex1 l ht.
  rewrite lit_tail_eq. eapply semax_seq'.
  - exact (lit_tail_if Espec gv p fs ox oh x2 lxb bsm streaming W o i e lh n cs single r oc1 ex1 l ht _
             HY HK Hlxb H HS0).
  - exact (lit_tail_rest Espec gv p fs ox oh x2 lxb bsm streaming W o0 o i e lh n cs single r oc1 ex1 l ht
             HY0 HY HO HK Hlxb Hlxbb H).
Qed.

Lemma seg_comp (e: Z) : e = 2 \/ e = 3 -> lit_seg 2 e (fun oh => e = 3 -> oh <> None).
Proof.
  intros He. unfold lit_seg. intros Espec gv p fs ox oh x2 lxb bsm streaming W o i R HY Hty Hx HR.
  apply semax_post with (R' := switch_ret_assert (lit_R gv p fs ox oh x2 lxb bsm streaming W o i));
    [ intros; destruct R as [Rn Rb Rc Rr]; unfold lit_R, switch_ret_assert, frame_ret_assert, function_body_ret_assert in *;
      simpl in HR |- *; try subst Rr; first [normalize; fail | intros ?; apply andp_left2, derives_refl] .. | ].
  clear HR R.
  assert_PROP (Zlength lxb = LITEXTRA_N /\ bytes_ok lxb) as Hlx.
  { unfold lit_S, lit_L, lit_scratch_x, lit_extra_at. Intros. apply prop_right. auto. }
  destruct Hlx as [Hlxb Hlxbb].
  pose proof HY as HY0.
  unfold lit_R, lit_post.
  change (Int.unsigned (Int.repr 2)) with 2. rewrite lit_sw2.
  apply semax_seq with FF; [| apply semax_ff].
  destruct o as [osh ob oN oc d cap]; destruct i as [ish ib iN ic ioff s].
  destruct HY as (Hoo & Hio & Hstr & Hbsm0 & Hsb & Hfp & Hfd & Hcold & HW & Hoh & Hs2).
  destruct Hoo as (Hosh & HoN & HoN32 & Hd & Hcap & Hdc).
  destruct Hio as (Hish & Hioff & Hin & HiN32 & HiN & _ & Hbytes & Hwin).
  cbn [oa_sh oa_base oa_N oa_c oa_d oa_cap iw_sh iw_base iw_N iw_c iw_off iw_s] in *.
  subst iN oN.
  assert (Hbsm: 0 <= bsm <= 131072) by (unfold ZSTD_BLOCKSIZE_MAX in Hbsm0; lia).
  unfold lit_L, lit_S. cbn [oa_sh oa_base oa_N oa_c oa_d oa_cap iw_sh iw_base iw_N iw_c iw_off iw_s].
  cbv [lit_c2 lit_sw f_ZSTD_decodeLiteralsBlock fn_body]. abbreviate_semax.
  lit_check (5 <= Zlength s).
  { entailer!. }
  { forward_if.
    - assert (DL: decode_literals oh s bsm = None).
      { apply lit_dl_lt5 with e; auto. rewrite !Int64.unsigned_repr in H by rep_lia. lia. }
      lit_errp. lit_err 20 oc oh x2 lxb. all: try (rewrite DL; auto).
      cbn [iw_s oa_cap]. apply xl_comp_short; [first [exact He | rewrite Hty; exact He] | rewrite !Int64.unsigned_repr in H by rep_lia; lia].
    - forward. entailer!. rewrite !Int64.unsigned_repr in * by rep_lia. lia. }
  Intros.
  forward.
  assert_PROP (force_val (sem_add_ptr_int tuchar Signed (offset_val ioff ib) (Vint (Int.repr 0))) =
               field_address (tarray tuchar (Zlength ic)) [ArraySubsc ioff] ib) as FA0.
  { entailer!. rewrite lit_fa by (auto; lia). reflexivity. }
  assert (B0: @Znth val Vundef ioff ic = Vint (Int.repr (byte_at s 0))).
  { rewrite <- (Z.add_0_r ioff) at 1. apply lit_win_byte; auto; lia. }
  pose proof (lit_byte_range s 0 Hbytes) as R0.
  forward.
  { entailer!. rewrite B0. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
  rewrite B0.
  forward.
  assert_PROP (field_compatible (tarray tuchar (Zlength ic)) [] ib) as FCi by entailer!.
  rewrite (litc_win_split ish ic ib ioff s) by auto. Intros.
  forward_call (ish, offset_val ioff ib, s, 0).
  { split; [auto | split; [lia | split; [lia |]]]. apply Forall_sublist. exact Hbytes. }
  sep_apply (lit_win_join ish ic ib ioff s); auto.
  forward_if (temp _t'3 (Vlong (Int64.repr (Z.min bsm cap)))).
  { forward. entailer!. rewrite Z.min_l; [reflexivity | lia]. }
  { forward. entailer!. rewrite Z.min_r; [reflexivity | lia]. }
  forward.
  assert_PROP (isptr p) as Pp by (unfold frame_fields; entailer!).
  forward_call p.
  forward_if (temp _t'5 (Vint (Int.repr 0))); [exfalso; lia | forward; entailer! |].
  unfold cfg_lit. forward.
  forward_if (temp _t'6 (Vint (Int.repr 0))); [exfalso; lia | forward; entailer! |].
  forward. sep_apply (lit_cfg_fold p).
  rewrite litc_lhl by lia.
  pose proof (lit_lhc_range s Hbytes ltac:(lia)) as Hlhc.
  destruct (lit_hdr s) as [[[lh n] cs] single] eqn:Hh.
  pose proof (lit_land3c (Z.shiftr (byte_at s 0) 2)) as Hl4.
  match goal with |- semax _ _ (Ssequence (Sswitch _ _) _) _ => apply semax_seq with (PROP ()
    LOCAL (temp _litCSize (Vlong (Int64.repr cs)); temp _litSize (Vlong (Int64.repr n));
           temp _lhSize (Vlong (Int64.repr lh)); temp _singleStream (Vint (Int.repr (if single then 1 else 0)));
           temp _flags (Vint (Int.repr 0)); temp _expectedWriteSize (Vlong (Int64.repr (Z.min bsm cap)));
           temp _blockSizeMax (Vlong (Int64.repr bsm)); temp _litEncType (Vint (Int.repr e));
           temp _istart (offset_val ioff ib); gvars gv; temp _dctx p;
           temp _srcSize (Vlong (Int64.repr (Zlength s))); temp _dst (offset_val d ob);
           temp _dstCapacity (Vlong (Int64.repr cap)); temp _streaming (Vint (Int.repr streaming)))
    SEP (data_at ish (tarray tuchar (Zlength ic)) ic ib; frame_fields p fs; zstd_globals gv; pws_pred W;
         cfg_lit p; tabs_huf gv p ox oh x2; dent_of dent_def gv ox; field_at_ Ews t_dctx (DOT _workspace) p;
         lit_scratch_x p lxb; data_at osh (tarray tuchar (Zlength oc)) oc ob)) end.
  { eapply semax_switch_PQR with (n := Z.land (Z.shiftr (byte_at s 0) 2) 3); [reflexivity | entailer! | entailer! |].
    unfold lit_hdr in Hh. cbv zeta in Hh.
    assert (Hl: Z.land (Z.shiftr (byte_at s 0) 2) 3 = 0 \/ Z.land (Z.shiftr (byte_at s 0) 2) 3 = 1 \/
                Z.land (Z.shiftr (byte_at s 0) 2) 3 = 2 \/ Z.land (Z.shiftr (byte_at s 0) 2) 3 = 3) by lia.
    destruct Hl as [E|[E|[E|E]]]; rewrite E in Hh |- *; cbn [Z.eqb Pos.eqb] in Hh; apply lit_tup4 in Hh; destruct Hh as (<- & <- & <- & <-);
      simpl select_switch; simpl seq_of_labeled_statement.
    - forward. forward. forward. forward. forward. forward. forward.
      rewrite (lit_fld _ 14 1023 10), (lit_fld _ 4 1023 10) by (first [reflexivity | lia]). entailer!.
    - forward. forward. forward. forward. forward. forward.
      rewrite (lit_fld _ 14 1023 10), (lit_fld _ 4 1023 10) by (first [reflexivity | lia]). entailer!.
    - forward. forward. forward. forward.
      rewrite (lit_fld _ 4 16383 14), litc_shru by (first [reflexivity | lia]). entailer!.
    - assert_PROP (force_val (sem_add_ptr_int tuchar Signed (offset_val ioff ib) (Vint (Int.repr 4))) =
                   field_address (tarray tuchar (Zlength ic)) [ArraySubsc (ioff + 4)] ib) as FA4.
      { entailer!. rewrite lit_fa by (auto; lia). reflexivity. }
      assert (B4: @Znth val Vundef (ioff + 4) ic = Vint (Int.repr (byte_at s 4))) by (apply lit_win_byte; auto; lia).
      pose proof (lit_byte_range s 4 Hbytes) as R4.
      forward. forward. forward.
      { entailer!. rewrite B4. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
      rewrite B4. forward. forward.
      pose proof (litc_shiftr_le (le_field s 0 4) 22 ltac:(lia) ltac:(lia)).
      rewrite (Int.unsigned_repr (byte_at s 4)), (Int.unsigned_repr 10), litc_shru, lit_cs3,
        (lit_fld _ 4 262143 18) by (first [reflexivity | rep_lia]).
      entailer!. }
  pose proof (lit_hdr_range s lh n cs single Hbytes H Hh) as (Hlh & Hn & Hcs & Hsg).
  change (2 ^ 18) with 262144 in Hcs.
  pose proof (lit_dl_comp oh s bsm e lh n cs single H Hty He Hx Hh ltac:(lia) ltac:(lia)) as DLC.
  pose proof (xl_comp (option_map (xhuf_of x2) oh) s bsm (Z.min bsm cap) (streaming =? 1) e lh n cs single Hbytes H Hty He
                ltac:(intros E3; destruct oh; [discriminate | exfalso; apply Hx; auto]) Hh) as XLC.
  unfold MORE_COMMANDS, abbreviate. clear MORE_COMMANDS.
  lit_check True.
  { entailer!. }
  { forward_if (temp _t'7 (Vint (Int.repr 0))).
    - forward.
      { entailer!. destruct ob; try contradiction. apply litc_tc_null.
        destruct (Z.eq_dec cap 0) as [C0 | C0].
        - sep_apply (HW C0). apply sepcon_weak_valid_pointer1, derives_refl.
        - sep_apply (lit_arr_wvp osh oc (Vptr b i) d); [auto | lia |].
          apply sepcon_weak_valid_pointer1, derives_refl. }
      entailer!. destruct ob; try contradiction. reflexivity.
    - forward. entailer!.
    - forward_if; [lit_false |]. forward. entailer!. }
  Intros.
  lit_check (n <= bsm).
  { entailer!. }
  { forward_if.
    - assert (DL: decode_literals oh s bsm = None).
      { rewrite DLC. rewrite ?Int64.unsigned_repr in H0 by rep_lia.
        replace (n >? bsm) with true by (symmetry; apply Z.gtb_lt; lia). reflexivity. }
      lit_errp. lit_err 20 oc oh x2 lxb. all: try (rewrite DL; auto).
      cbn [iw_s oa_cap]. rewrite XLC. rewrite ?Int64.unsigned_repr in H0 by rep_lia.
      replace (n >? bsm) with true by (symmetry; apply Z.gtb_lt; lia). reflexivity.
    - forward. entailer!; rewrite ?Int64.unsigned_repr in * by rep_lia; lia. }
  Intros.
  forward_if (single = false -> 6 <= n).
  { destruct single; [apply (f_equal Int.unsigned) in H1; vm_compute in H1; discriminate |].
    apply <- semax_seq_skip.
    lit_check (6 <= n).
    { entailer!. }
    { forward_if.
      - assert (DL: decode_literals oh s bsm = None).
        { rewrite DLC. replace (n >? bsm) with false by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
          replace (n <? 6) with true by (symmetry; apply Z.ltb_lt; rewrite ?Int64.unsigned_repr in H2 by rep_lia; lia).
          reflexivity. }
        lit_errp. lit_err 24 oc oh x2 lxb. all: try (rewrite DL; auto).
        cbn [iw_s oa_cap]. rewrite XLC. replace (n >? bsm) with false by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
        replace (n <? 6) with true by (symmetry; apply Z.ltb_lt; rewrite ?Int64.unsigned_repr in H2 by rep_lia; lia).
        reflexivity.
      - forward. entailer!; rewrite ?Int64.unsigned_repr in * by rep_lia; lia. }
    entailer!. }
  { destruct single; [| exfalso; apply H1; reflexivity]. forward. entailer!. }
  apply semax_extract_PROP; intro Hs6.
  assert (Hsf: andb (negb single) (n <? 6) = false).
  { destruct single; [reflexivity |]. cbn [negb andb]. apply Z.ltb_ge. auto. }
  assert (Hnb: (n >? bsm) = false) by (rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
  lit_check (cs + lh <= Zlength s).
  { entailer!. }
  { forward_if.
    - assert (DL: decode_literals oh s bsm = None).
      { rewrite DLC, Hnb, Hsf. rewrite lit_ltu_add in H1 by rep_lia. apply Z.ltb_lt in H1.
        replace (cs + lh >? Zlength s) with true by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_lt; lia).
        reflexivity. }
      lit_errp. lit_err 20 oc oh x2 lxb. all: try (rewrite DL; auto).
      cbn [iw_s oa_cap]. rewrite XLC, Hnb, Hsf.
      first [rewrite lit_ltu_add in H1 by rep_lia; apply Z.ltb_lt in H1
            | apply Int64.ltu_inv in H1; rewrite !Int64.unsigned_repr in H1 by rep_lia].
      replace (cs + lh >? Zlength s) with true by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_lt; lia).
      reflexivity.
    - forward. entailer!. unfold Int64.ltu in H1. rewrite !Int64.unsigned_repr in H1 by rep_lia.
      destruct (zlt _ _) in H1; [discriminate | lia]. }
  Intros.
  assert (Hcl: (cs + lh >? Zlength s) = false) by (rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
  lit_check (n <= Z.min bsm cap).
  { entailer!. }
  { forward_if.
    - lit_errp. lit_err 70 oc oh x2 lxb.
      all: try (rewrite DLC, Hnb, Hsf, Hcl;
                destruct (lit_model _ _ _ _ _) as [[l t] |] eqn:LM; [| auto];
                right; apply lit_model_len in LM; [| lia]; rewrite LM; lia).
      cbn [iw_s oa_cap]. rewrite XLC, Hnb, Hsf, Hcl.
      replace (Z.min bsm cap <? n) with true
        by (symmetry; apply Z.ltb_lt; rewrite ?Int64.unsigned_repr in * by rep_lia; lia).
      reflexivity.
    - forward. entailer!; rewrite ?Int64.unsigned_repr in * by rep_lia; lia. }
  Intros.
  unfold lit_scratch_x. Intros.
  assert_PROP (isptr ob) as Pob by entailer!.
  forward_call (p, fs, bsm, ob, d, cap, n, streaming, 0, osh, oc).
  destruct (lit_alloc_out oc streaming cap bsm n d 0 ltac:(lia) ltac:(lia) ltac:(lia))
    as (AL & AU & AUs & AB & AD & AS1 & AS2 & AE).
  set (oc1 := alloc_out oc streaming cap bsm n d (Z.min bsm cap) 0) in *.
  assert (HO: lit_o1 {| oa_sh := osh; oa_base := ob; oa_N := Zlength oc; oa_c := oc; oa_d := d; oa_cap := cap |}
                {| oa_sh := osh; oa_base := ob; oa_N := Zlength oc; oa_c := oc1; oa_d := d; oa_cap := cap |}
                streaming bsm n) by (unfold lit_o1; cbn; auto 7).
  clearbody oc1.
  (* the prefetch of the Huffman table: no effect *)
  match goal with |- semax _ ?P (Ssequence ?A _) _ => apply semax_seq with P end.
  { unfold frame_fields. Intros.
    destruct Hcold as [Hc | Hc]; rewrite Hc; forward.
    - forward_if (temp _t'8 (Vint (Int.repr 0))).
      { lit_false. }
      { forward. entailer!. }
      forward_if; [lit_false |]. forward. entailer!.
    - forward_if (temp _t'8 (Vint (Int.repr (if 768 <? n then 1 else 0)))).
      { forward. entailer!. rewrite lit_cmpu_gt by rep_lia. destruct (768 <? n); reflexivity. }
      { lit_false. }
      forward_if.
      2: { forward. entailer!. }
      unfold tabs_huf. Intros hp.
      assert_PROP (is_pointer_or_null hp) as Hhp.
      { destruct oh as [ht |].
        - cbv iota. go_lower. eapply derives_trans; [| apply (lit_hp_frame gv p ox ht x2 hp)]. cancel.
        - cbv iota. entailer!. rewrite lit_ctx_huf_eq by auto. destruct p; try contradiction; exact I. }
      match goal with |- semax _ ?Q (Sloop _ _) _ => forward_loop Q break: Q end.
      { entailer!. }
      2: { unfold tabs_huf. Exists hp. entailer!. }
      forward. forward. forward. forward.
      match goal with |- semax _ (PROPx ?Ps (LOCALx (_ :: ?Qs) (SEPx ?Rs))) _ _ =>
        forward_loop (EX v: int64, PROPx Ps (LOCALx (temp __pos (Vlong v) :: Qs) (SEPx Rs)))
          break: (EX v: int64, PROPx Ps (LOCALx (temp __pos (Vlong v) :: Qs) (SEPx Rs))) end.
      { Exists (Int64.repr 0). entailer!. }
      2: { Intros v. forward. entailer!. }
      Intros v.
      match goal with |- semax _ ?P0 _ _ => forward_if P0 end.
      { forward. entailer!. }
      { forward. Exists v. entailer!. }
      lit_skiploop. forward. Exists (Int64.add v (Int64.repr 64)). entailer!. }
  unfold MORE_COMMANDS, abbreviate. clear MORE_COMMANDS.
  (* from here on the output array is oc1, the one after ZSTD_allocateLiteralsBuffer *)
  assert (HY1: lit_hyps fs oh bsm streaming W
     {| oa_sh := osh; oa_base := ob; oa_N := Zlength oc; oa_c := oc1; oa_d := d; oa_cap := cap |}
     {| iw_sh := ish; iw_base := ib; iw_N := Zlength ic; iw_c := ic; iw_off := ioff; iw_s := s |}).
  { unfold lit_hyps, outarr_ok, inwin_ok, win_ok; simpl.
    repeat (match goal with |- _ /\ _ => split end); auto; try lia. }
  assert (HK: lit_kfacts oh bsm cap e s lh n cs single).
  { unfold lit_kfacts. repeat (match goal with |- _ /\ _ => split end); auto; lia. }
  apply semax_seq with (lit_J gv p fs ox oh x2 lxb bsm streaming W
     {| oa_sh := osh; oa_base := ob; oa_N := Zlength oc; oa_c := oc1; oa_d := d; oa_cap := cap |}
     {| iw_sh := ish; iw_base := ib; iw_N := Zlength ic; iw_c := ic; iw_off := ioff; iw_s := s |} e lh n cs single).
  - eapply semax_pre; [| eapply semax_post; [| | | | exact (seg_comp_huf Espec gv p fs ox oh x2 lxb bsm streaming W _ _ e lh n cs single HY1 HK)]].
    + unfold lit_K, lit_KL, lit_KF. cbn [oa_sh oa_base oa_N oa_c oa_d oa_cap iw_sh iw_base iw_N iw_c iw_off iw_s app].
      entailer!.
    + intros. apply andp_left2. apply derives_refl.
    + intros. apply andp_left2. first [cbn [RA_break normal_ret_assert]; apply FF_left | simpl; normalize].
    + intros. apply andp_left2. first [cbn [RA_continue normal_ret_assert]; apply FF_left | simpl; normalize].
    + intros. apply andp_left2. first [cbn [RA_return normal_ret_assert]; intros; apply FF_left | simpl; normalize].
  - exact (seg_comp_tail Espec gv p fs ox oh x2 lxb bsm streaming W _ _ _ e lh n cs single HY0 HY1 HO HK Hlxb Hlxbb AS1).
Qed.
