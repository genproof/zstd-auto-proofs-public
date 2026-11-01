(* API v3, subtree B, group BLK, sub-group LIT: v2's B/blk/BlkLIT.v with the literals decoder holding cfg_lit p
   (disableHufAsm) instead of cfg_b p (BSpecs3.ZSTD_decodeLiteralsBlock_spec3), and its outcome exactly
   model/ExBlock.v's (BlkIface.lits_exact).  The common part (ZSTD_allocateLiteralsBuffer, ZSTD_blockSizeMax, the
   frame of the proof) is BlkLIT3Base.v; the arms of the switch are BlkLIT3Raw.v, BlkLIT3Rle.v, BlkLIT3Comp.v;
   here the dispatch on the literals type and the group's obligation. *)
Require Export Zstd.proof.dec.v3.B.BlkLIT3Raw Zstd.proof.dec.v3.B.BlkLIT3Rle Zstd.proof.dec.v3.B.BlkLIT3Comp.
Local Open Scope logic.

(* case 3 = its litEntropy check, then case 2 *)
Definition lit_c3 : statement := match lit_sw with LScons _ c _ => c | _ => Sskip end.

Lemma lit_sw3 : seq_of_labeled_statement (select_switch 3 lit_sw) =
  Ssequence lit_c3 (seq_of_labeled_statement (select_switch 2 lit_sw)).
Proof. reflexivity. Qed.

Lemma lit_and3 (b: Z) : 0 <= b < 256 -> Int.and (Int.repr b) (Int.repr 3) = Int.repr (Z.land b 3).
Proof.
  intros Hb. unfold Int.and. rewrite !Int.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma lit_land3 (b: Z) : 0 <= Z.land b 3 <= 3.
Proof.
  change (Z.land b 3) with (Z.land b (Z.ones 2)). rewrite Z.land_ones by lia.
  assert (H4: 0 < 2 ^ 2) by reflexivity. pose proof (Z.mod_pos_bound b (2 ^ 2) H4).
  change (2 ^ 2) with 4 in *. lia.
Qed.

(* set_repeat without a table: the model fails *)
Lemma lit_dl_rep_none (s: list Z) (bsm: Z) :
  Z.land (byte_at s 0) 3 = 3 -> decode_literals None s bsm = None.
Proof.
  intros H. unfold decode_literals. rewrite H. simpl.
  destruct (Zlength s <? 2); reflexivity.
Qed.

Lemma body_decodeLiteralsBlock : body_ok LIT_G ZSTD_decodeLiteralsBlock_spec3.
Proof.
  exists f_ZSTD_decodeLiteralsBlock; split; [reflexivity | split; [reflexivity |]].
  start_function.
  destruct o as [osh ob oN oc d cap]; destruct i as [ish ib iN ic ioff s].
  destruct H as (Hosh & HoN & HoN32 & Hd & Hcap & Hdc).
  destruct H0 as (Hish & Hioff & Hin & HiN32 & HiN & _ & Hbytes & Hwin).
  cbn [oa_sh oa_base oa_N oa_c oa_d oa_cap iw_sh iw_base iw_N iw_c iw_off iw_s] in *.
  subst iN oN.
  assert (Hbsm: 0 <= bsm <= 131072) by (unfold ZSTD_BLOCKSIZE_MAX in H2; lia).
  lit_skiploop.
  lit_check (2 <= Zlength s).
  { entailer!. }
  { forward_if.
    - lit_errpath. lit_err 20 oc oh x2 lxb.
      + rewrite lit_dl_short by (rewrite !Int64.unsigned_repr in H by rep_lia; lia). auto.
      + apply xl_short. cbn [iw_s]. rewrite !Int64.unsigned_repr in H by rep_lia. lia.
    - forward. entailer!. rewrite !Int64.unsigned_repr in H by rep_lia. lia. }
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
  forward_call (p, fs, bsm).
  rewrite lit_and3 by lia.
  pose proof (lit_land3 (byte_at s 0)) as Hk.
  set (k := Z.land (byte_at s 0) 3) in *.
  eapply semax_switch_PQR with (n := k); [reflexivity | entailer! | entailer! |].
  match goal with |- context [select_switch _ ?SL] => change SL with lit_sw end.
  assert (HY: lit_hyps fs oh bsm streaming W
     {| oa_sh := osh; oa_base := ob; oa_N := Zlength oc; oa_c := oc; oa_d := d; oa_cap := cap |}
     {| iw_sh := ish; iw_base := ib; iw_N := Zlength ic; iw_c := ic; iw_off := ioff; iw_s := s |}).
  { unfold lit_hyps, outarr_ok, inwin_ok, win_ok; simpl.
    repeat (match goal with |- _ /\ _ => split end); auto; try lia. }
  assert (Hk4: k = 0 \/ k = 1 \/ k = 2 \/ k = 3) by lia.
  destruct Hk4 as [Hk0 | [Hk1 | [Hk2 | Hk3]]].
  - rewrite Hk0. eapply semax_pre; [| apply (seg_basic Espec gv p fs ox oh x2 lxb bsm streaming W _ _ _ HY Hk0 I eq_refl)].
    unfold lit_L, lit_S. simpl. entailer!. lit_fin.
  - rewrite Hk1. eapply semax_pre; [| apply (seg_rle Espec gv p fs ox oh x2 lxb bsm streaming W _ _ _ HY Hk1 I eq_refl)].
    unfold lit_L, lit_S. simpl. entailer!. lit_fin.
  - rewrite Hk2. eapply semax_pre;
      [| apply (seg_comp 2 (or_introl eq_refl) Espec gv p fs ox oh x2 lxb bsm streaming W _ _ _ HY Hk2
                  (fun H => ltac:(discriminate)) eq_refl)].
    unfold lit_L, lit_S. simpl. entailer!. lit_fin.
  - rewrite Hk3. change (Int.unsigned (Int.repr 3)) with 3. rewrite lit_sw3.
    remember (seq_of_labeled_statement (select_switch 2 lit_sw)) as REST.
    cbv [lit_c3 lit_sw f_ZSTD_decodeLiteralsBlock fn_body]. abbreviate_semax.
    lit_skiploop. unfold tabs_huf. Intros hp.
    lit_check (oh <> None).
    { entailer!. }
    { forward. forward_if.
      - destruct oh as [ht |]; [apply (f_equal Int.unsigned) in H0; vm_compute in H0; discriminate |].
        lit_errpath. lit_err 30 oc (@None huf_table) x2 lxb.
        + rewrite lit_dl_rep_none by exact Hk3. auto.
        + apply xl_rep_none. exact Hk3.
      - forward. entailer!. }
    Intros. rename H0 into Hne. subst REST.
    eapply semax_pre;
      [| apply (seg_comp 3 (or_intror eq_refl) Espec gv p fs ox oh x2 lxb bsm streaming W _ _ _ HY Hk3
                  (fun _ => Hne) eq_refl)].
    unfold lit_L, lit_S. cbn [oa_sh oa_base oa_N oa_c oa_d oa_cap iw_sh iw_base iw_N iw_c iw_off iw_s].
    entailer!. unfold tabs_huf. Exists hp. cancel.
Qed.


Lemma LIT3_ok : LIT3_obligation.
Proof.
  exists LIT_S. split; [reflexivity |]. split.
  - intros x Hx. simpl in Hx |- *. tauto.
  - repeat constructor.
    + apply body_blockSizeMax.
    + apply body_allocate.
    + apply body_decodeLiteralsBlock.
Qed.
