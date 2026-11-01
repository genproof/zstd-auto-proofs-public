(* X1D: the body of HUF_decompress1X1_usingDTable_internal_body against the byte_cells spec (HufX1DSpecsBC.v, contract item 17). *)
Require Export Zstd.proof.dec.B.huf.HufX1DSpecsBC.
Require Import Zstd.proof.dec.B.BMemcpyOk.
Local Open Scope logic.

(* the window s of the input array, as the bitstream's source buffer *)
Lemma x1d_win_split sh N c off s base :
  field_compatible (tarray tuchar N) [] base -> win_ok sh N c off (Zlength s) s ->
  data_at sh (tarray tuchar N) c base =
  data_at sh (tarray tuchar off) (sublist 0 off c) base *
  bit_src sh (offset_val off base) s *
  data_at sh (tarray tuchar (N - (off + Zlength s))) (sublist (off + Zlength s) N c)
    (offset_val (off + Zlength s) base).
Proof.
  intros Hfc (Hsh & Hoff & Hn & HN & Hc & _ & Hbytes & Hwin). pose proof (Zlength_nonneg s).
  unfold tarray. rewrite (split3_data_at_Tarray_tuchar sh N off (off + Zlength s) c base) by lia.
  rewrite !field_address0_offset by auto with field_compatible.
  simpl nested_field_offset. rewrite !Z.add_0_l, !Z.mul_1_l.
  unfold bit_src. rewrite Hwin. replace (off + Zlength s - off) with (Zlength s) by lia.
  reflexivity.
Qed.

Lemma x1d_okb_wf s : bs_okb s = true -> bs_wf s = true.
Proof.
  unfold bs_okb, bs_wf. intros H. apply andb_prop in H as [H1 H3]. apply andb_prop in H1 as [_ H2].
  destruct s as [|z s]; [discriminate|]. rewrite H3, andb_true_r.
  apply negb_true_iff, Z.eqb_neq. rewrite Zlength_cons. pose proof (Zlength_nonneg s). lia.
Qed.

Lemma x1d_nowf ht s n : bs_wf s = false -> huf_lits_with false ht s n = None.
Proof.
  intros Hwf. unfold huf_lits_with, huf_decode_stream.
  destruct (bs_okb s) eqn:E; [rewrite (x1d_okb_wf _ E) in Hwf; discriminate | reflexivity].
Qed.

Lemma x1d_model ht s n l : huf_lits_with false ht s n = Some l ->
  bs_wf s = true /\ huf_decode_syms ht s (Z.to_nat n) (bs_total s) = Some (l, 0).
Proof.
  unfold huf_lits_with, huf_decode_stream. destruct (bs_okb s) eqn:E; [|discriminate]. simpl.
  intros H. split; [apply x1d_okb_wf; auto|].
  destruct (huf_decode_syms ht s (Z.to_nat n) (bs_total s)) as [[l' p]|]; [|discriminate].
  destruct p; try discriminate. congruence.
Qed.

Lemma x1d_err_small r : 0 <= r <= 2 ^ 32 -> is_error_code r = false.
Proof. intros. unfold is_error_code. apply Z.ltb_ge. lia. Qed.

(* the stream state after BIT_initDStream: at most 64 bits consumed *)
Lemma x1d_init_consumed s : bytes_ok s -> 1 <= Zlength s ->
  8 * Z.max 0 (Zlength s - 8) + 64 - bs_total s <= 64.
Proof.
  intros Hb Hn. unfold bs_total, highbit. rewrite <- Zlength_correct.
  pose proof (Z.log2_nonneg (last s 0)). lia.
Qed.

Lemma x1d_wf_len s : bs_wf s = true -> 1 <= Zlength s.
Proof.
  unfold bs_wf. intros H. apply andb_prop in H as [H _]. apply negb_true_iff, Z.eqb_neq in H.
  pose proof (Zlength_nonneg s). lia.
Qed.

(* the window base after BIT_initDStream is below the stream's payload size *)
Lemma x1d_lo_le s : bytes_ok s -> 1 <= Zlength s -> 8 * Z.max 0 (Zlength s - 8) <= bs_total s.
Proof.
  intros Hb Hn. unfold bs_total, highbit. rewrite <- Zlength_correct.
  pose proof (Z.log2_nonneg (last s 0)). lia.
Qed.

Lemma x1d_out_after (oc: list val) d n (l: list Z) : 0 <= d -> 0 <= n -> d + n <= Zlength oc -> Zlength l = n ->
  out_after oc (sublist 0 d oc ++ zbytes l ++ sublist (d + n) (Zlength oc) oc) d n.
Proof.
  intros. split; [list_solve|]. intros i Hi Hni.
  assert (i < d \/ d + n <= i) as [Hlt|Hge] by lia; list_solve.
Qed.

Lemma x1d_out_sub (oc: list val) d n (l: list Z) : 0 <= d -> 0 <= n -> d + n <= Zlength oc -> Zlength l = n ->
  sublist d (d + n) (sublist 0 d oc ++ zbytes l ++ sublist (d + n) (Zlength oc) oc) = zbytes l.
Proof. intros. list_solve. Qed.

Lemma x1d_neg_code k : 0 < k < 2 ^ 63 -> Vlong (Int64.repr (- k)) = Vlong (Int64.repr (2 ^ 64 - k)).
Proof.
  intros. f_equal. apply Int64.eqm_samerepr. unfold Int64.eqm, Zbits.eqmod. exists (-1).
  change Int64.modulus with (2 ^ 64). lia.
Qed.

Lemma x1d_rep_data_at_ sh gv s start pos lo p :
  BIT_DStream_rep sh gv s start pos lo p |-- data_at_ sh t_bitD p.
Proof. unfold BIT_DStream_rep. Intros ptr lim. unfold t_bitD. cancel. Qed.

(* the table's log (kept folded, so that VST's substitutions leave L alone) *)
Definition x1d_log_is (ht: huf_table) (L: Z) : Prop := L = hufdt_log false ht.

Lemma x1d_rep_inv sh gv s start pos lo p :
  BIT_DStream_rep sh gv s start pos lo p |-- !! bit_inv s pos lo.
Proof. unfold BIT_DStream_rep. Intros ptr lim. entailer!. Qed.

(* the exact model (ExHuf.x_huf_decode, one X1 stream) when BIT_initDStream fails *)
Lemma x1d_xdec_nowf ht s m : bytes_ok s -> bs_wf s = false -> x_huf_decode (xhuf_of false ht) true s m = None.
Proof. intros Hb Hwf. unfold x_huf_decode, xh_1stream. cbn [xhuf_of xh_x2]. rewrite xb_init_eq, Hwf by exact Hb. reflexivity. Qed.

(* ... and when it succeeds: HUF_decodeStreamX1's run from the initial state, then BIT_endOfDStream *)
Lemma x1d_xdec_wf ht s m l pos' lo' : bytes_ok s -> bs_wf s = true -> bit_inv s pos' lo' ->
  let r := xh_x1_stream (xhuf_of false ht) s (xb_of s (bs_total s) (8 * Z.max 0 (Zlength s - 8))) m in
  fst r = l -> xb_rel s pos' lo' (snd r) ->
  x_huf_decode (xhuf_of false ht) true s m = if andb (lo' =? 0) (pos' =? 0) then Some l else None.
Proof.
  intros Hb Hwf Hi r Hl Hr. unfold x_huf_decode, xh_1stream. cbn [xhuf_of xh_x2]. rewrite xb_init_eq, Hwf by exact Hb.
  rewrite <- (xb_end_rel s pos' lo' (snd r) Hi Hr). subst r.
  destruct (xh_x1_stream _ s _ m) as [l1 d1]. cbn [fst snd] in *. subst l1. reflexivity.
Qed.

Lemma body_HUF_decompress1X1_usingDTable_internal_body :
  semax_body Vprog G_1X1 f_HUF_decompress1X1_usingDTable_internal_body
    HUF_decompress1X1_usingDTable_internal_body_bc_spec.
Proof.
  start_function.
  assert_PROP (isptr ob /\ field_compatible (tarray tuchar N) [] base) as Hpf by entailer!.
  destruct Hpf as [Hob Hfc].
  rewrite (x1d_win_split sh N c off s base) by auto.
  pose proof H4 as Hw. destruct Hw as (Hsh & Hoff & Hn & HN & Hc & _ & Hbytes & Hwin).
  pose proof (Zlength_nonneg s) as Hsn. subst N.
  unfold hufdt_x_at. Intros L res. rename H8 into Hres.
  match goal with HLe: L = hufdt_log false ht |- _ => assert (HLx: x1d_log_is ht L) by exact HLe; clear HLe end.
  assert (HL: 1 <= L <= 12) by (destruct H5 as (Hlog & _); unfold HUF_TABLELOG_MAX in *; lia).
  forward.
  forward_call (offset_val d ob, n).
  1: (unfold ZSTD_BLOCKSIZE_MAX in H1; rep_lia).
  assert (Eoe: (if 0 <? n then offset_val n (offset_val d ob) else offset_val d ob) = offset_val (d + n) ob).
  { destruct (0 <? n) eqn:E. - rewrite offset_offset_val. f_equal; lia.
    - apply Z.ltb_ge in E. replace n with 0 by lia. rewrite Z.add_0_r. reflexivity. }
  rewrite Eoe; clear Eoe.
  assert_PROP (isptr dt) as Hdt by entailer!.
  forward. forward.
  forward_call (Tsh, v_dtd, sht, dt, (Vint (Int.repr 12), (Vint (Int.repr 0), (Vint (Int.repr L), res)))).
  { memcpy_ok_B. }
  forward.
  1: (entailer!; rep_lia).
  match goal with |- context [force_val (sem_binary_operation' ?op ?t1 ?t2 dt ?v)] =>
    replace (force_val (sem_binary_operation' op t1 t2 dt v)) with (offset_val 4 dt)
      by (destruct dt; try contradiction; reflexivity) end.
  assert (Hsub: sublist 0 (0 + Zlength s) s = s) by (rewrite Z.add_0_l; apply sublist_same; lia).
  assert (Hbp: isptr (offset_val off base)) by (destruct Hfc as [Hb _]; destruct base; try contradiction; exact I).
  destruct (bs_wf s) eqn:Hwf.
  2: { match goal with |- semax _ ?Pre _ _ => forward_loop Pre break: (@FF (environ -> mpred) _) end.
       { entailer!. }
       forward_call (Tsh, v_bitD, sh, offset_val off base, s, 0, Zlength s, gv).
       Intros r. rewrite Hsub, Hwf in *.
       unfold POSTCONDITION, abbreviate.
       match goal with |- semax _ ?Pre _ (loop_nocontinue_ret_assert _ (overridePost ?Q _)) =>
         forward_loop Pre break: Q end.
       { entailer!. }
       forward_call r.
       match goal with Hx: is_error_code r = true |- _ => rewrite Hx end.
       forward_if.
       { forward. Exists r oc.
         rewrite (x1d_win_split sh (Zlength c) c off s base) by auto.
         change (negb false) with true. rewrite (x1d_nowf ht s n Hwf), (x1d_xdec_nowf ht s n Hbytes Hwf).
         unfold hufdt_x_at. Exists L res.
         entailer!. unfold out_after, unchanged_outside. split; [reflexivity | intros; reflexivity]. }
       { match goal with Hx: Int.repr 1 = Int.zero |- _ => discriminate Hx end. } }
  pose proof (x1d_wf_len s Hwf) as Hs1.
  pose proof (x1d_init_consumed s Hbytes Hs1) as Hcons.
  pose proof (x1d_lo_le s Hbytes Hs1) as Hlo.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx (?A :: ?B :: _ :: ?R)))) _ _ =>
    forward_loop (PROPx P (LOCALx Q (SEPx (A :: B :: data_at_ Tsh t_bitD v_bitD :: R))))
    break: (PROPx P (LOCALx Q (SEPx (
      BIT_DStream_rep Tsh gv s (offset_val off base) (bs_total s) (8 * Z.max 0 (Zlength s - 8)) v_bitD ::
      A :: B :: R)))) end.
  { entailer!. }
  { forward_call (Tsh, v_bitD, sh, offset_val off base, s, 0, Zlength s, gv).
    Intros r. rewrite Hsub, Hwf in *. rewrite isptr_offset_val_zero by auto. subst r.
    unfold POSTCONDITION, abbreviate.
    match goal with |- semax _ ?Pre _ (loop_nocontinue_ret_assert _ (overridePost ?Q _)) =>
      forward_loop Pre break: Q end.
    { entailer!. }
    forward_call (Zlength s).
    rewrite x1d_err_small by (unfold ZSTD_BLOCKSIZE_MAX in H3; rep_lia).
    forward_if.
    { match goal with Hx: Int.repr 0 <> Int.zero |- _ => contradiction Hx; reflexivity end. }
    forward. { entailer!. }
    forward. entailer!. }
  forward_call (Tsh, v_bitD, gv, s, offset_val off base, bs_total s, (8 * Z.max 0 (Zlength s - 8))%Z,
                sh, offset_val off base, s, 0, sht, offset_val 4 dt, ht, L, sho, ob, oc, d, n).
  { split; [| unfold ZSTD_BLOCKSIZE_MAX in *; rep_lia].
    unfold bit_src_ok. rewrite isptr_offset_val_zero by auto.
    split3; [reflexivity | lia | split; [lia|]]. rewrite Z.add_0_l; apply sublist_same; lia. }
  Intros vret. destruct vret as [[pos' lo'] l]. simpl fst in *; simpl snd in *.
  match goal with Hm: _ <= bs_total s -> forall l', _ -> _ |- _ => specialize (Hm Hlo); rename Hm into Hmodel end.
  match goal with Hx: forall dx, xb_rel _ _ _ dx -> _ |- _ =>
    destruct (Hx _ (xb_rel_of s (bs_total s) (8 * Z.max 0 (Zlength s - 8)))) as [Hxl Hxr]; clear Hx end.
  assert_PROP (bit_inv s pos' lo') as Hinv' by (sep_apply x1d_rep_inv; entailer!).
  pose proof (x1d_xdec_wf ht s _ l pos' lo' Hbytes Hwf Hinv' Hxl Hxr) as Hxdec. clear Hxl Hxr.
  forward_call (Tsh, v_bitD, gv, s, offset_val off base, pos', lo', sh, offset_val off base, s, 0).
  { unfold bit_src_ok. rewrite isptr_offset_val_zero by auto.
    split3; [reflexivity | lia | split; [lia|]]. rewrite Z.add_0_l; apply sublist_same; lia. }
  forward_if.
  { forward.
    Exists (2 ^ 64 - 20) (sublist 0 d oc ++ zbytes l ++ sublist (d + Zlength l) (Zlength oc) oc).
    rewrite (x1d_win_split sh (Zlength c) c off s base) by auto.
    unfold hufdt_x_at. Exists L res.
    sep_apply (x1d_rep_data_at_ Tsh gv s (offset_val off base) pos' lo' v_bitD).
    entailer!.
    split; [intros Hbc; apply byte_cells_splice; auto|].
    split3; [apply x1d_out_after; auto; lia | intros Hx; vm_compute in Hx; discriminate |
             split; [| split; [| apply (x1d_neg_code 20); lia]]].
    2: { change (negb false) with true. rewrite Hxdec.
         destruct (andb (lo' =? 0) (pos' =? 0)); [simpl in H11; discriminate H11 | reflexivity]. }
    destruct (huf_lits_with false ht s (Zlength l)) as [l0|] eqn:Ehl; [|auto].
    apply x1d_model in Ehl as [_ Hd]. destruct (Hmodel l0 Hd) as (_ & -> & ->).
    simpl in H11. discriminate H11. }
  { forward.
    Exists (Zlength l) (sublist 0 d oc ++ zbytes l ++ sublist (d + Zlength l) (Zlength oc) oc).
    rewrite (x1d_win_split sh (Zlength c) c off s base) by auto.
    unfold hufdt_x_at. Exists L res.
    sep_apply (x1d_rep_data_at_ Tsh gv s (offset_val off base) pos' lo' v_bitD).
    entailer!.
    split; [intros Hbc; apply byte_cells_splice; auto|].
    split; [unfold ZSTD_BLOCKSIZE_MAX in H1; rep_lia|].
    split3; [apply x1d_out_after; auto; lia | intros _; split; [reflexivity|] |].
    { exists l. split; [apply x1d_out_sub; auto; lia | auto]. }
    split.
    { destruct (huf_lits_with false ht s (Zlength l)) as [l0|] eqn:Ehl; [|auto].
      apply x1d_model in Ehl as [_ Hd]. destruct (Hmodel l0 Hd) as (<- & _ & _).
      split; [reflexivity|]. apply x1d_out_sub; auto; lia. }
    change (negb false) with true. rewrite Hxdec.
    destruct (andb (lo' =? 0) (pos' =? 0)); [| contradiction H11; reflexivity].
    split; [reflexivity|]. apply x1d_out_sub; auto; lia. }
Qed.
