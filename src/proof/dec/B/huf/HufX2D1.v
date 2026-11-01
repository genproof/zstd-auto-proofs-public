(* X2D: the body of HUF_decompress1X2_usingDTable_internal_body (spec in HufX2DSpecs.v). *)
Require Export Zstd.proof.dec.B.huf.HufX2DSpecs.
Require Import Zstd.proof.dec.B.BMemcpyOk.
Local Open Scope logic.

(* the window s of the input array, as the bitstream's source buffer *)
Lemma x2d_win_split sh N c off s base :
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

Lemma x2d_okb_wf s : bs_okb s = true -> bs_wf s = true.
Proof.
  unfold bs_okb, bs_wf. intros H. apply andb_prop in H as [H1 H3]. apply andb_prop in H1 as [_ H2].
  destruct s as [|z s]; [discriminate|]. rewrite H3, andb_true_r.
  apply negb_true_iff, Z.eqb_neq. rewrite Zlength_cons. pose proof (Zlength_nonneg s). lia.
Qed.

Lemma x2d_nowf ht s n : bs_wf s = false -> huf_lits_with false ht s n = None.
Proof.
  intros Hwf. unfold huf_lits_with, huf_decode_stream.
  destruct (bs_okb s) eqn:E; [rewrite (x2d_okb_wf _ E) in Hwf; discriminate | reflexivity].
Qed.

Lemma x2d_model ht s n l : huf_lits_with false ht s n = Some l ->
  bs_wf s = true /\ huf_decode_syms ht s (Z.to_nat n) (bs_total s) = Some (l, 0).
Proof.
  unfold huf_lits_with, huf_decode_stream. destruct (bs_okb s) eqn:E; [|discriminate]. simpl.
  intros H. split; [apply x2d_okb_wf; auto|].
  destruct (huf_decode_syms ht s (Z.to_nat n) (bs_total s)) as [[l' p]|]; [|discriminate].
  destruct p; try discriminate. congruence.
Qed.

Lemma x2d_err_small r : 0 <= r <= 2 ^ 32 -> is_error_code r = false.
Proof. intros. unfold is_error_code. apply Z.ltb_ge. lia. Qed.

(* the stream state after BIT_initDStream: at most 64 bits consumed *)
Lemma x2d_init_consumed s : bytes_ok s -> 1 <= Zlength s ->
  8 * Z.max 0 (Zlength s - 8) + 64 - bs_total s <= 64.
Proof.
  intros Hb Hn. unfold bs_total, highbit. rewrite <- Zlength_correct.
  pose proof (Z.log2_nonneg (last s 0)). lia.
Qed.

Lemma x2d_wf_len s : bs_wf s = true -> 1 <= Zlength s.
Proof.
  unfold bs_wf. intros H. apply andb_prop in H as [H _]. apply negb_true_iff, Z.eqb_neq in H.
  pose proof (Zlength_nonneg s). lia.
Qed.

(* the window base after BIT_initDStream is below the stream's payload size *)
Lemma x2d_lo_le s : bytes_ok s -> 1 <= Zlength s -> 8 * Z.max 0 (Zlength s - 8) <= bs_total s.
Proof.
  intros Hb Hn. unfold bs_total, highbit. rewrite <- Zlength_correct.
  pose proof (Z.log2_nonneg (last s 0)). lia.
Qed.

Lemma x2d_out_after (oc: list val) d n (l: list Z) : 0 <= d -> 0 <= n -> d + n <= Zlength oc -> Zlength l = n ->
  out_after oc (sublist 0 d oc ++ zbytes l ++ sublist (d + n) (Zlength oc) oc) d n.
Proof.
  intros. split; [list_solve|]. intros i Hi Hni.
  assert (i < d \/ d + n <= i) as [Hlt|Hge] by lia; list_solve.
Qed.

Lemma x2d_out_sub (oc: list val) d n (l: list Z) : 0 <= d -> 0 <= n -> d + n <= Zlength oc -> Zlength l = n ->
  sublist d (d + n) (sublist 0 d oc ++ zbytes l ++ sublist (d + n) (Zlength oc) oc) = zbytes l.
Proof. intros. list_solve. Qed.

Lemma x2d_neg_code k : 0 < k < 2 ^ 63 -> Vlong (Int64.repr (- k)) = Vlong (Int64.repr (2 ^ 64 - k)).
Proof.
  intros. f_equal. apply Int64.eqm_samerepr. unfold Int64.eqm, Zbits.eqmod. exists (-1).
  change Int64.modulus with (2 ^ 64). lia.
Qed.

Lemma x2d_rep_data_at_ sh gv s start pos lo p :
  BIT_DStream_rep sh gv s start pos lo p |-- data_at_ sh t_bitD2 p.
Proof. unfold BIT_DStream_rep. Intros ptr lim. unfold t_bitD2. cancel. Qed.

(* The exact model of the one-stream X2 decoder (ExHuf.x_huf_decode, single stream): no stream when the
   input is not a well-formed bitstream (BIT_initDStream fails) *)
Lemma x2d_xnowf ht s n : bytes_ok s -> bs_wf s = false -> x_huf_decode (xhuf_of true ht) (negb false) s n = None.
Proof.
  intros Hb Hwf. change (xh_1stream (xh_x2_stream (xhuf_of true ht)) s n = None).
  unfold xh_1stream. rewrite (xb_init_eq s Hb), Hwf. reflexivity.
Qed.

(* ... and otherwise the bytes HUF_decodeStreamX2 writes from the initial state, accepted exactly when
   BIT_endOfDStream finds the stream consumed (a model-level summary of the C's last steps) *)
Lemma x2d_xwf ht s n pos' lo' (l: list Z) : bytes_ok s -> bs_wf s = true -> bit_inv s pos' lo' ->
  (forall dx, xb_rel s (bs_total s) (8 * Z.max 0 (Zlength s - 8)) dx ->
     fst (xh_x2_stream (xhuf_of true ht) s dx n) = l /\
     xb_rel s pos' lo' (snd (xh_x2_stream (xhuf_of true ht) s dx n))) ->
  x_huf_decode (xhuf_of true ht) (negb false) s n = if andb (lo' =? 0) (pos' =? 0) then Some l else None.
Proof.
  intros Hb Hwf Hinv Hst. change (xh_1stream (xh_x2_stream (xhuf_of true ht)) s n =
    if andb (lo' =? 0) (pos' =? 0) then Some l else None).
  unfold xh_1stream. rewrite (xb_init_eq s Hb), Hwf.
  specialize (Hst _ (xb_rel_of s (bs_total s) (8 * Z.max 0 (Zlength s - 8)))).
  destruct (xh_x2_stream (xhuf_of true ht) s (xb_of s (bs_total s) (8 * Z.max 0 (Zlength s - 8))) n)
    as [l1 d1]. simpl in Hst. destruct Hst as [<- Hr].
  rewrite (xb_end_rel s pos' lo' d1 Hinv Hr). reflexivity.
Qed.

Lemma body_HUF_decompress1X2_usingDTable_internal_body :
  semax_body Vprog G_1X2 f_HUF_decompress1X2_usingDTable_internal_body
    HUF_decompress1X2_usingDTable_internal_body_spec.
Proof.
  start_function.
  repeat match goal with Hx: context [if false then _ else _] |- _ => simpl in Hx end.
  assert_PROP (isptr ob /\ field_compatible (tarray tuchar N) [] base) as Hpf by entailer!.
  destruct Hpf as [Hob Hfc].
  match goal with Hw: win_ok _ _ _ _ _ _ |- _ => rename Hw into Hwin0 end.
  rewrite (x2d_win_split sh N c off s base) by auto.
  pose proof Hwin0 as Hw. destruct Hw as (Hsh & Hoff & Hn & HN & Hc & _ & Hbytes & Hwin).
  pose proof (Zlength_nonneg s) as Hsn. subst N.
  unfold hufdt_x_at. Intros L res c2.
  (* the reader's log and cells, as local definitions (VST's automation would substitute equations) *)
  subst L c2. set (L := hufdt_log true ht) in *. set (c2 := map x2v (xh_cells_x2 ht L)) in *.
  match goal with Hx: huf_ok ht |- _ => rename Hx into Hhok end.
  match goal with Hx: ht_log ht <= L <= HUF_TABLELOG_MAX |- _ => rename Hx into HlogL end.
  assert (Hsub: sublist 0 (0 + Zlength s) s = s) by (rewrite Z.add_0_l; apply sublist_same; lia).
  assert (Hbp: isptr (offset_val off base)) by (destruct Hfc as [Hb _]; destruct base; try contradiction; exact I).
  assert (HL: 1 <= L <= 12) by (destruct Hhok as (Hlog & _); unfold HUF_TABLELOG_MAX in *; lia).
  destruct (bs_wf s) eqn:Hwf.
  2: { match goal with |- semax _ ?Pre _ _ => forward_loop Pre break: (@FF (environ -> mpred) _) end.
       { entailer!. }
       forward_call (Tsh, v_bitD, sh, offset_val off base, s, 0, Zlength s, gv).
       Intros r. rewrite Hsub, Hwf in *.
       unfold POSTCONDITION, abbreviate.
       match goal with |- semax _ ?Pre _ (loop_nocontinue_ret_assert _ (overridePost ?Q _)) =>
         forward_loop Pre break: Q end.
       { entailer!. }
       assert (Hr: 0 <= r <= Int64.max_unsigned) by lia.
       forward_call r.
       match goal with Hx: is_error_code r = true |- _ => rewrite Hx end.
       forward_if.
       { forward. Exists r oc.
         rewrite (x2d_win_split sh (Zlength c) c off s base) by auto.
         rewrite (x2d_nowf ht s n Hwf), (x2d_xnowf ht s n Hbytes Hwf).
         unfold hufdt_x_at. Exists L res c2.
         entailer!. unfold out_after, unchanged_outside. split; [reflexivity | intros; reflexivity]. }
       { match goal with Hx: Int.repr 1 = Int.zero |- _ => discriminate Hx end. } }
  pose proof (x2d_wf_len s Hwf) as Hs1.
  pose proof (x2d_init_consumed s Hbytes Hs1) as Hcons.
  pose proof (x2d_lo_le s Hbytes Hs1) as Hlo.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx (?A :: _ :: ?R)))) _ _ =>
    forward_loop (PROPx P (LOCALx Q (SEPx (A :: data_at_ Tsh t_bitD2 v_bitD :: R))))
    break: (PROPx P (LOCALx Q (SEPx (
      BIT_DStream_rep Tsh gv s (offset_val off base) (bs_total s) (8 * Z.max 0 (Zlength s - 8)) v_bitD ::
      A :: R)))) end.
  { entailer!. }
  { forward_call (Tsh, v_bitD, sh, offset_val off base, s, 0, Zlength s, gv).
    Intros r. rewrite Hsub, Hwf in *. rewrite isptr_offset_val_zero by auto. subst r.
    unfold POSTCONDITION, abbreviate.
    match goal with |- semax _ ?Pre _ (loop_nocontinue_ret_assert _ (overridePost ?Q _)) =>
      forward_loop Pre break: Q end.
    { entailer!. }
    forward_call (Zlength s).
    rewrite x2d_err_small by (unfold ZSTD_BLOCKSIZE_MAX in *; rep_lia).
    forward_if.
    { match goal with Hx: Int.repr 0 <> Int.zero |- _ => contradiction Hx; reflexivity end. }
    forward. { entailer!. }
    forward. entailer!. }
  forward.
  forward_call (offset_val d ob, n).
  1: (unfold ZSTD_BLOCKSIZE_MAX in *; rep_lia).
  assert (Eoe: (if 0 <? n then offset_val n (offset_val d ob) else offset_val d ob) = offset_val (d + n) ob).
  { destruct (0 <? n) eqn:E. - rewrite offset_offset_val. f_equal; lia.
    - apply Z.ltb_ge in E. replace n with 0 by lia. rewrite Z.add_0_r. reflexivity. }
  rewrite Eoe; clear Eoe.
  assert_PROP (isptr dt) as Hdt by entailer!.
  forward. forward.
  forward_call (Tsh, v_dtd, sht, dt, (Vint (Int.repr 12), (Vint (Int.repr 1), (Vint (Int.repr L), res)))).
  { memcpy_ok_B. }
  forward.
  1: (entailer!; rep_lia).
  match goal with |- context [force_val (sem_binary_operation' ?op ?t1 ?t2 dt ?v)] =>
    replace (force_val (sem_binary_operation' op t1 t2 dt v)) with (offset_val 4 dt)
      by (destruct dt; try contradiction; reflexivity) end.
  forward_call (Tsh, v_bitD, gv, s, offset_val off base, bs_total s, (8 * Z.max 0 (Zlength s - 8))%Z,
                sh, offset_val off base, s, 0, sht, offset_val 4 dt, ht, L, c2, sho, ob, oc, d, n).
  { split; [unfold bit_src_ok; rewrite isptr_offset_val_zero by auto;
            split3; [reflexivity | lia | split; [lia|]]; rewrite Z.add_0_l; apply sublist_same; lia|].
    split; [unfold x2_tab_ok; auto|].
    unfold ZSTD_BLOCKSIZE_MAX in *; rep_lia. }
  Intros vret. destruct vret as [[pos' lo'] l]. simpl fst in *; simpl snd in *.
  match goal with Hm: _ <= bs_total s -> forall l', _ -> _ |- _ => specialize (Hm Hlo); rename Hm into Hmodel end.
  match goal with Hx: forall dx, xb_rel _ _ _ dx -> _ |- _ => rename Hx into Hxst end.
  assert_PROP (bit_inv s pos' lo') as Hinv by (unfold BIT_DStream_rep; Intros ptr lim; entailer!).
  pose proof (x2d_xwf ht s n pos' lo' l Hbytes Hwf Hinv Hxst) as Hxd.
  forward_call (Tsh, v_bitD, gv, s, offset_val off base, pos', lo', sh, offset_val off base, s, 0).
  { unfold bit_src_ok. rewrite isptr_offset_val_zero by auto.
    split3; [reflexivity | lia | split; [lia|]]. rewrite Z.add_0_l; apply sublist_same; lia. }
  forward_if.
  { forward.
    Exists (2 ^ 64 - 20) (sublist 0 d oc ++ zbytes l ++ sublist (d + Zlength l) (Zlength oc) oc).
    rewrite (x2d_win_split sh (Zlength c) c off s base) by auto.
    unfold hufdt_x_at. Exists L res c2.
    sep_apply (x2d_rep_data_at_ Tsh gv s (offset_val off base) pos' lo' v_bitD).
    entailer!.
    split; [apply x2d_out_after; auto; lia|].
    split; [intros Hbc; apply byte_cells_splice; auto|].
    split; [intros Hx; vm_compute in Hx; discriminate|].
    split; [| split; [| apply (x2d_neg_code 20); lia]].
    2: { rewrite Hxd. destruct (andb (lo' =? 0) (pos' =? 0)) eqn:Ea; [|reflexivity].
         match goal with Hx: Int.repr 1 = Int.zero |- _ => discriminate Hx end. }
    destruct (huf_lits_with false ht s (Zlength l)) as [l0|] eqn:Ehl; [|auto].
    apply x2d_model in Ehl as [_ Hd]. destruct (Hmodel l0 Hd) as (_ & -> & ->).
    match goal with Hx: Int.repr (if _ then _ else _) = _ |- _ => simpl in Hx; discriminate Hx end. }
  { forward.
    Exists (Zlength l) (sublist 0 d oc ++ zbytes l ++ sublist (d + Zlength l) (Zlength oc) oc).
    rewrite (x2d_win_split sh (Zlength c) c off s base) by auto.
    unfold hufdt_x_at. Exists L res c2.
    sep_apply (x2d_rep_data_at_ Tsh gv s (offset_val off base) pos' lo' v_bitD).
    entailer!.
    split; [unfold ZSTD_BLOCKSIZE_MAX in *; rep_lia|].
    split; [apply x2d_out_after; auto; lia|].
    split; [intros Hbc; apply byte_cells_splice; auto|].
    split; [intros _; split; [reflexivity|] |].
    { exists l. split; [apply x2d_out_sub; auto; lia | auto]. }
    split.
    2: { rewrite Hxd. destruct (andb (lo' =? 0) (pos' =? 0)) eqn:Ea.
         - split; [reflexivity|]. apply x2d_out_sub; auto; lia.
         - match goal with Hx: Int.repr 0 <> Int.zero |- _ => contradiction Hx; reflexivity end. }
    destruct (huf_lits_with false ht s (Zlength l)) as [l0|] eqn:Ehl; [|auto].
    apply x2d_model in Ehl as [_ Hd]. destruct (Hmodel l0 Hd) as (<- & _ & _).
    split; [reflexivity|]. apply x2d_out_sub; auto; lia. }
Qed.
