(* FS3 streaming, case zdss_flush: helper lemmas (port of v2 StreamSeg_flush.v). *)
Require Import Zstd.proof.dec.v3.FS.stream.S3RetStmts Zstd.proof.dec.v3.FS.stream.S3ModelStmts.
Local Open Scope logic.

Section CM_S3FlushLem_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma ptr_diff_char : forall i x y, 0 <= y <= x -> x <= Ptrofs.max_signed ->
  Vptrofs (Ptrofs.divs (Ptrofs.sub (Ptrofs.add i (Ptrofs.repr x)) (Ptrofs.add i (Ptrofs.repr y))) (Ptrofs.repr 1))
  = Vlong (Int64.repr (x - y)).
Proof.
intros i x y Hy Hx.
rewrite (Ptrofs.add_commut i (Ptrofs.repr x)), (Ptrofs.add_commut i (Ptrofs.repr y)), Ptrofs.sub_shifted.
rewrite ptrofs_sub_repr.
assert (Hm: Ptrofs.max_signed <= Ptrofs.max_unsigned) by (compute; congruence).
unfold Ptrofs.divs. rewrite (Ptrofs.signed_repr 1) by (compute; split; congruence).
rewrite Z.quot_1_r. rewrite (Ptrofs.signed_repr (x - y)).
2: { assert (Ptrofs.min_signed < 0) by (compute; reflexivity). lia. }
unfold Vptrofs. destruct Archi.ptr64 eqn:E; [|discriminate].
f_equal. unfold Ptrofs.to_int64. rewrite Ptrofs.unsigned_repr by lia. reflexivity.
Qed.

(* for (;;break) {} : a no-op *)
Lemma semax_skipbreak_seq : forall {Espec: OracleKind} {cs: compspecs} Delta (P: environ -> mpred) c R,
  semax Delta P c R -> semax Delta P (Ssequence (Sloop Sskip Sbreak) c) R.
Proof.
intros Espec cs Delta P c R H.
apply semax_seq with P; [|exact H].
apply semax_loop with P.
2: { eapply semax_pre; [|apply semax_break]. destruct R; unfold loop2_ret_assert, overridePost. cbv beta iota.
     apply andp_left2, derives_refl. }
eapply semax_post; [| | | | apply semax_skip].
all: destruct R; unfold normal_ret_assert, loop1_ret_assert, overridePost.
- intros rho; simpl; apply andp_left2, derives_refl.
- intros rho; simpl; apply andp_left2, FF_left.
- intros rho; simpl; apply andp_left2, FF_left.
- intros vl rho; simpl; apply andp_left2, FF_left.
Qed.

Lemma semax_skipbreak_seq2 : forall {Espec: OracleKind} {cs: compspecs} Delta (P: environ -> mpred) c rest R,
  semax Delta P (Ssequence c rest) R -> semax Delta P (Ssequence (Ssequence (Sloop Sskip Sbreak) c) rest) R.
Proof.
intros. apply seq_assoc. apply semax_skipbreak_seq. exact H.
Qed.

Lemma ring_join : forall sh n1 n2 (v: list val) p,
  0 <= n1 -> 0 <= n2 -> Zlength v = n1 + n2 -> field_compatible (tarray tuchar (n1 + n2)) nil p ->
  (data_at sh (Tarray tuchar n1 noattr) (sublist 0 n1 v) p *
   data_at sh (tarray tuchar n2) (sublist n1 (n1 + n2) v) (offset_val n1 p))%logic
  |-- data_at sh (tarray tuchar (n1 + n2)) v p.
Proof.
intros sh n1 n2 v p H1 H2 Hl Hfc.
rewrite (split2_data_at_Tarray_tuchar sh (n1 + n2) n1 v p) by lia.
rewrite field_address0_offset by auto with field_compatible.
replace (n1 + n2 - n1) with n2 by lia.
replace (nested_field_offset (Tarray tuchar (n1 + n2) noattr) (SUB n1)) with n1
  by (unfold nested_field_offset; simpl; lia).
apply derives_refl.
Qed.

Local Transparent denote_tc_test_eq.
Lemma arr_tc_test : forall W sh n p (v: list val) i (Q: mpred),
  buf_ok W sh n p -> readable_share sh -> 0 <= i <= n -> field_compatible (tarray tuchar n) nil p ->
  (pws_pred W * data_at sh (tarray tuchar n) v p * Q)%logic |-- denote_tc_test_eq (offset_val i p) (Vlong Int64.zero).
Proof.
intros W sh n p v i Q Hb Hr Hi Hfc.
assert (Hp: isptr p) by (destruct Hfc; auto).
destruct p; try contradiction.
assert (Hw: (pws_pred W * data_at sh (tarray tuchar n) v (Vptr b i0))%logic |-- weak_valid_pointer (offset_val i (Vptr b i0))).
{ destruct (zeq n 0).
  - subst n. assert (i = 0) by lia. subst i. rewrite isptr_offset_val_zero by exact I.
    eapply derives_trans; [|apply andp_left1, derives_refl]. eapply derives_trans; [|apply Hb].
    apply sepcon_derives; [apply derives_refl | apply data_at_data_at_].
  - eapply derives_trans; [apply sepcon_derives; [apply TT_right | apply data_at_memory_block] |].
    rewrite sepcon_comm. eapply derives_trans; [|apply (extend_weak_valid_pointer _ TT)].
    apply sepcon_derives; [|apply derives_refl].
    apply memory_block_weak_valid_pointer; [simpl; rewrite Z.max_r by lia; lia | simpl; rewrite Z.max_r by lia; lia |].
    apply readable_nonidentity; auto. }
eapply derives_trans; [apply sepcon_derives; [exact Hw | apply derives_refl] |].
eapply derives_trans; [apply extend_weak_valid_pointer |].
simpl. unfold denote_tc_test_eq. simpl.
apply andp_right; [apply prop_right; reflexivity | apply derives_refl].
Qed.

(* what the flush case needs of the invariant *)
Lemma flush_pre : forall a k sv ipc opc oc dl,
  call_inv a k sv ipc opc oc dl -> sf_stage (c3_s k) = zdss_flush ->
  dc_stable (a_st a) = false /\ c3_stable k = false /\
  isptr (sf_inBuff (c3_s k)) /\ sf_inBuff (c3_s k) <> nullval /\
  (exists h b, fs_fParams (c3_fs k) = fh_val (fh_adj h b)) /\
  exists ostart oend,
    sf_outStart (c3_s k) = vlong ostart /\ sf_outEnd (c3_s k) = vlong oend /\
    0 <= ostart <= oend /\ oend <= sf_outSize (c3_s k) /\
    sublist ostart oend (sublist (sf_inSize (c3_s k)) (sf_inSize (c3_s k) + sf_outSize (c3_s k)) (sf_ring (c3_s k)))
      = zbytes (sv_pend sv).
Proof.
intros a k sv ipc opc oc dl Hinv Hst.
destruct Hinv as (_&_&_&_&_&_&_&Hbase&_&_&_&_&Hcore&_).
destruct Hbase as (Hstab&_).
unfold c_core in Hcore. destruct Hcore as (_&_&_&Hcore).
rewrite Hst in Hcore. simpl in Hcore.
destruct Hcore as (_&Hfr&Hring&Hnst&_).
destruct (dc_stable (a_st a)) eqn:Es.
{ exfalso. apply (Hnst eq_refl). reflexivity. }
split; [reflexivity|]. split; [exact Hstab|].
destruct Hring as (Hnn&Hip&_&ostart&oend&Hos&Hoe&Ho&Hr).
destruct Hr as (Hoe2&Hpend&_).
split; [exact Hip|]. split; [exact Hnn|]. split.
- destruct Hfr as (_&_&_&_&_&Hfp). destruct (sv_fp sv); try contradiction.
  + destruct Hfp as (_&_&(h&_&_&Hf)&_). exists h, (fh_blockSizeMax h); exact Hf.
  + destruct Hfp as (_&Hf&_). exists (zp_h z), (zp_bsm z); exact Hf.
- exists ostart, oend. repeat split; auto; lia.
Qed.

(* the stream fields after the flush: streamStage, outStart, outEnd *)
Definition sf_after (s: sfields) (stage os oe: Z) : sfields :=
  {| sf_stage := stage; sf_inBuff := sf_inBuff s; sf_inSize := sf_inSize s; sf_inPos := sf_inPos s;
     sf_outBuff := sf_outBuff s; sf_outSize := sf_outSize s; sf_outStart := vlong os; sf_outEnd := vlong oe;
     sf_lhSize := sf_lhSize s; sf_hostage := sf_hostage s; sf_nfp := sf_nfp s; sf_expOut := sf_expOut s;
     sf_hbuf := sf_hbuf s; sf_over := sf_over s; sf_ring := sf_ring s; sf_mem := sf_mem s; sf_held := sf_held s |}.

Definition sv_flushed (sv: sview) (m: Z) : sview :=
  {| sv_fp := sv_fp sv; sv_pend := sublist m (Zlength (sv_pend sv)) (sv_pend sv); sv_ahead := sv_ahead sv;
     sv_lay := sv_lay sv; sv_dd := sv_dd sv |}.

Definition ring_out (s: sfields) : list val := sublist (sf_inSize s) (sf_inSize s + sf_outSize s) (sf_ring s).

Lemma vlong_inj : forall x y, 0 <= x <= Int64.max_unsigned -> 0 <= y <= Int64.max_unsigned ->
  vlong x = vlong y -> x = y.
Proof.
intros x y Hx Hy H. unfold vlong in H.
apply (f_equal (fun v => match v with Vlong i => Int64.unsigned i | _ => 0 end)) in H.
cbv beta iota in H. rewrite !Int64.unsigned_repr in H by lia. exact H.
Qed.

(* the facts of the invariant at zdss_flush (buffered) *)
Lemma flush_facts : forall a k sv ipc opc oc dl ostart oend,
  call_inv a k sv ipc opc oc dl -> sf_stage (c3_s k) = zdss_flush ->
  sf_outStart (c3_s k) = vlong ostart -> sf_outEnd (c3_s k) = vlong oend ->
  0 <= ostart <= oend -> oend <= sf_outSize (c3_s k) -> 0 <= sf_inSize (c3_s k) ->
  sf_inSize (c3_s k) + sf_outSize (c3_s k) <= Ptrofs.max_unsigned ->
  Zlength (sf_ring (c3_s k)) = sf_inSize (c3_s k) + sf_outSize (c3_s k) ->
  dc_stable (a_st a) = false /\
  Zlength (sv_pend sv) = oend - ostart /\ bytes_ok (sv_pend sv) /\
  sublist ostart oend (ring_out (c3_s k)) = zbytes (sv_pend sv) /\
  sf_inSize (c3_s k) + sf_outSize (c3_s k) <= 2 ^ 32.
Proof.
intros a k sv ipc opc oc dl ostart oend Hinv Hst Hos Hoe Ho Hoe2 Hin Hmax Hrl.
destruct Hinv as (_&_&_&_&_&_&_&_&_&_&_&_&Hcore&_).
destruct Hcore as (_&_&Hsz&Hcore). rewrite Hst in Hcore. simpl in Hcore.
destruct Hcore as (_&Hfr&Hring&Hnst&_).
destruct (dc_stable (a_st a)) eqn:Es; [exfalso; apply (Hnst eq_refl); reflexivity|].
destruct Hring as (_&_&_&os'&oe'&Hos'&Hoe'&Ho'&Hr). cbv iota in Hr.
destruct Hr as (Hoe2'&Hpend&_&_&Hlay).
assert (Hmx: Ptrofs.max_unsigned = Int64.max_unsigned) by reflexivity.
assert (os' = ostart) by (apply vlong_inj; try lia; congruence).
assert (oe' = oend) by (apply vlong_inj; try lia; congruence).
subst os' oe'.
assert (Hlp: Zlength (sv_pend sv) = oend - ostart).
{ apply (f_equal (@Zlength val)) in Hpend. rewrite Zlength_map, Zlength_sublist in Hpend; [lia|lia|].
  rewrite Zlength_sublist; lia. }
split; [reflexivity|]. split; [exact Hlp|]. split; [|split; [exact Hpend|exact Hsz]].
destruct (sv_lay sv) as [|eb ec gp|base pe od|base ps pe e].
- destruct Hlay as (_&Hz&Hz'). destruct (sv_pend sv); [constructor|]. rewrite Zlength_cons in Hlp.
  pose proof (Zlength_nonneg l). lia.
- destruct Hlay as (_&Hz&Hz'). destruct (sv_pend sv); [constructor|]. rewrite Zlength_cons in Hlp.
  pose proof (Zlength_nonneg l). lia.
- destruct Hlay as (_&_&_&Hz&Hz'&_). destruct (sv_pend sv); [constructor|]. rewrite Zlength_cons in Hlp.
  pose proof (Zlength_nonneg l). lia.
- destruct Hlay as (_&_&_&_&_&_&(pre&Hpre)&_).
  destruct Hfr as (_&_&_&_&_&Hx).
  destruct (sv_fp sv) as [|hb|hdr got|hdr z]; try contradiction.
  + destruct Hx as ([Hx|(?&?&?&Hx)]&_); discriminate.
  + destruct Hx as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&Hb&_). cbn [fp_content] in Hpre. rewrite Hpre in Hb.
    apply Forall_app in Hb. tauto.
Qed.

(* the call's invariant after delivering the first m pending bytes, given the new context's core *)
Lemma flush_cells : forall a k sv ipc opc oc dl ostart oend m s' sv',
  dsa_ok a -> call_inv a k sv ipc opc oc dl -> dc_stable (a_st a) = false ->
  sublist ostart oend (ring_out (c3_s k)) = zbytes (sv_pend sv) -> bytes_ok (sv_pend sv) ->
  0 <= ostart -> Zlength (sv_pend sv) = oend - ostart -> oend <= Zlength (ring_out (c3_s k)) ->
  0 <= m <= oend - ostart -> m <= a_osz a - opc ->
  sf_nfp s' = sf_nfp (c3_s k) ->
  sv_fp sv' = sv_fp sv -> sv_pend sv' = sublist m (Zlength (sv_pend sv)) (sv_pend sv) ->
  sv_ahead sv' = sv_ahead sv -> sv_lay sv' = sv_lay sv -> sv_dd sv' = sv_dd sv ->
  (sf_stage s' = zdss_read \/ sf_stage s' = zdss_flush) ->
  sf_stage (c3_s k) = zdss_flush -> sf_hostage s' = sf_hostage (c3_s k) ->
  sf_mem s' = sf_mem (c3_s k) -> sf_held s' = sf_held (c3_s k) ->
  c_core (dc_stable (a_st a)) (Some (a_ob a, a_osz a))
    (ss_out (dc_ss (a_st a)) ++ (dl ++ sublist 0 m (sv_pend sv))) (c3_with_s k s') sv' ->
  (hist_ok (dc_stable (a_st a)) k sv -> hist_ok (dc_stable (a_st a)) (c3_with_s k s') sv') ->
  call_inv a (c3_with_s k s') sv' ipc (opc + m) (copy_cells oc opc (ring_out (c3_s k)) ostart m)
    (dl ++ sublist 0 m (sv_pend sv)).
Proof.
intros a k sv ipc opc oc dl ostart oend m s' sv' Ha Hinv Hs Hpend Hbp Hos Hlp Hle Hm Hcap
  Hnfp' Hfp' Hpend' Hahead' Hlay' Hdd' Hstage' Hst0 Hhost' Hmem' Hheld' Hcore' Hhist'.
pose proof Ha as (_&_&_&_&_&_&_&_&_&Hopos&_).
destruct Hinv as (H1&H2&H3&H4&H5&H6&H7&Hbase&Hssin&Hnfp1&Hnfp2&Hnfp3&Hcore&Hdd&Hstout&Hahead&Hbound&Hmod&Hlh&Hhs&Hexp&HT).
set (ocs := ring_out (c3_s k)) in *.
set (pend := sv_pend sv) in *.
assert (Hsub: sublist ostart (ostart + m) ocs = zbytes (sublist 0 m pend)).
{ replace (sublist ostart (ostart + m) ocs) with (sublist 0 m (sublist ostart oend ocs)).
  - rewrite Hpend. rewrite sublist_map. reflexivity.
  - rewrite sublist_sublist by lia. f_equal; lia. }
assert (Hlocs: Zlength (sublist ostart (ostart + m) ocs) = m) by (rewrite Zlength_sublist; lia).
unfold call_inv. cbn [c3_with_s c3_s c3_par c3_fs c3_dict c3_stable c3_set c3_tabs].
rewrite Hnfp', Hahead', Hpend', Hfp'.
unfold copy_cells.
split; [exact H1|]. split; [lia|].
split; [rewrite !Zlength_app, !Zlength_sublist by lia; lia|].
split.
{ rewrite sublist0_app1 by (rewrite Zlength_sublist; lia). rewrite sublist_sublist00 by lia. exact H4. }
split; [rewrite Zlength_app, Zlength_sublist by (pose proof (Zlength_nonneg pend); lia); lia|].
split.
{ rewrite sublist_app' by (try rewrite Zlength_app; rewrite ?Zlength_sublist by lia; lia).
  rewrite Zlength_sublist by lia.
  rewrite sublist_sublist by lia. replace (a_opos a + 0) with (a_opos a) by lia.
  rewrite sublist_app' by (rewrite ?Zlength_sublist by lia; lia).
  rewrite Zlength_sublist by lia.
  replace (opc + m - (opc - 0) - (opc - 0 - (opc - 0))) with m by lia.
  autorewrite with sublist. rewrite map_app. f_equal.
  - rewrite <- H6. f_equal; lia.
  - rewrite Z.add_comm. exact Hsub. }
split; [apply Forall_app; split; [exact H7 | apply Forall_sublist; exact Hbp]|].
(* the flush keeps the allocator's fields *)
split; [unfold base_call, mem_call, mem_room in Hbase |- *; cbn [c3_with_s c3_s c3_par c3_dict c3_sp c3_fs c3_stable c3_set];
        rewrite Hmem', Hheld'; exact Hbase|].
split; [exact Hssin|].
split; [exact Hnfp1|].
split.
{ destruct (Z.eq_dec m 0) as [E|E].
  - subst m. rewrite Z.add_0_r.
    destruct Hnfp2 as [X|[X|[X|[X|[X _]]]]]; auto; rewrite Hst0 in X; discriminate.
  - right; left; lia. }
split; [exact Hnfp3|].
split; [exact Hcore'|].
split.
{ unfold sv_dd_ok in *. cbn [c3_with_s c3_s c3_dict]. rewrite Hdd'. intros _ x buf Hx.
  apply (Hdd ltac:(rewrite Hst0; unfold zdss_read, zdss_flush; lia) x buf Hx). }
split; [rewrite Hs; discriminate|].
split; [exact Hahead|].
split.
{ intros Hi Hst. specialize (Hbound Hi Hst). rewrite Zlength_app, !Zlength_sublist by lia. lia. }
split.
2: { split; [intro Hx; destruct Hstage' as [X|X]; rewrite X in Hx; discriminate|]. split; [exact Hhs|].
     split; [rewrite Hs; discriminate|].
     intros Hf Hc Hp Hh0. rewrite Hhost' in Hh0. apply (HT Hst0 Hc); auto.
     intro E. apply Hp. rewrite E. apply sublist_nil_gen. rewrite Zlength_nil. lia. }
destruct Hmod as [Hd|(cd&Hm'&Hcd&Hh)]; [left; exact Hd|right].
exists cd. split; [|split; [rewrite Hfp'; exact Hcd | apply Hhist'; exact Hh]].
rewrite Hfp', Hpend'.
destruct Hm' as (dsin&fb&recs&Hsin&Hser&Hcur&Hcrel&Hcont).
exists dsin, fb, recs. split; [exact Hsin|]. split; [exact Hser|]. split; [exact Hcur|]. split; [exact Hcrel|].
rewrite <- Hcont. rewrite !app_assoc. rewrite <- (app_assoc _ (sublist 0 m pend)).
rewrite sublist_rejoin by lia. rewrite sublist_same by lia. reflexivity.
Qed.

(* the ring after a partial flush of m < |pend| bytes *)
Lemma ring_inc : forall obuf sout s fp pend lay ostart oend m sout',
  c_ring false obuf sout s fp pend lay ->
  sf_outStart s = vlong ostart -> sf_outEnd s = vlong oend -> 0 <= ostart <= oend -> oend <= sf_outSize s ->
  0 <= sf_inSize s -> sf_inSize s + sf_outSize s <= Ptrofs.max_unsigned ->
  Zlength pend = oend - ostart -> 0 <= m < oend - ostart ->
  c_ring false obuf sout' (sf_after s zdss_flush (ostart + m) oend) fp (sublist m (Zlength pend) pend) lay.
Proof.
intros obuf sout s fp pend lay ostart oend m sout' Hring Hos Hoe Ho Hoe2 Hin Hmax Hlp Hm.
assert (Hmx: Ptrofs.max_unsigned = Int64.max_unsigned) by reflexivity.
destruct Hring as (Hnn&Hip&Hin'&os'&oe'&Hos'&Hoe'&Ho'&Hr). cbv iota in Hr.
destruct Hr as (Hoe2'&Hpend&Hplen&Hneed&Hlay).
assert (os' = ostart) by (apply vlong_inj; try lia; congruence).
assert (oe' = oend) by (apply vlong_inj; try lia; congruence).
subst os' oe'.
unfold c_ring. cbn [sf_after sf_inBuff sf_inSize sf_outSize sf_ring sf_outStart sf_outEnd sf_outBuff].
split; [exact Hnn|]. split; [exact Hip|]. split; [exact Hin'|].
exists (ostart + m), oend.
split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. cbv iota.
split; [exact Hoe2'|].
split.
{ replace (sublist (ostart + m) oend _) with
    (sublist m (oend - ostart) (sublist ostart oend
       (sublist (sf_inSize s) (sf_inSize s + sf_outSize s) (sf_ring s)))).
  - rewrite Hpend, sublist_map, Hlp. reflexivity.
  - rewrite sublist_sublist by lia. f_equal; lia. }
split; [rewrite Zlength_sublist by lia; lia|].
split; [exact Hneed|].
destruct lay as [|eb ec gp|base pe od|base ps pe e].
- exfalso; lia.
- exfalso; lia.
- exfalso; lia.
- destruct Hlay as (Hb&Hps&Hpe2&Hpec&Hlr&Hhd&(pre&Hpre)&Hw&Hfcs&Hroom).
  split; [exact Hb|]. split; [exact Hps|]. split; [exact Hpe2|]. split; [exact Hpec|]. split; [exact Hlr|]. split; [exact Hhd|].
  split.
  { exists (pre ++ sublist 0 m pend). rewrite Hpre, <- app_assoc. f_equal.
    rewrite sublist_rejoin by lia. rewrite sublist_same by lia. reflexivity. }
  split.
  { destruct Hw as [Hw|(_&_&Hn&_)]; [left; exact Hw|]. subst pend. rewrite Zlength_nil in Hlp. lia. }
  split; [exact Hfcs|]. intro; lia.
Qed.

(* the ring after a complete flush: nothing pending, outStart = outEnd (both 0 when the ring restarts);
   fParams = fh_val (fh_adj h b): the code reads frameContentSize and blockSizeMax (= b) *)
Lemma ring_cpl : forall obuf sout s fp pend lay ostart oend (wr: bool) sout' fs tabs dd h b,
  c_ring false obuf sout s fp pend lay -> c_frame fs tabs fp lay dd -> fs_fParams fs = fh_val (fh_adj h b) ->
  sf_outStart s = vlong ostart -> sf_outEnd s = vlong oend -> 0 <= ostart <= oend -> oend <= sf_outSize s ->
  0 <= sf_inSize s -> sf_inSize s + sf_outSize s <= 2 ^ 32 ->
  Zlength pend = oend - ostart ->
  (wr = true -> Int64.ltu (Int64.repr (sf_outSize s)) (Int64.repr (fh_contentSize h)) = true /\
     Int64.unsigned (Int64.repr (sf_outSize s)) <
     Int64.unsigned (Int64.add (Int64.repr oend) (Int64.repr (Int.unsigned (Int.repr b))))) ->
  (wr = false -> Int64.ltu (Int64.repr (sf_outSize s)) (Int64.repr (fh_contentSize h)) = false \/
     Int64.unsigned (Int64.add (Int64.repr oend) (Int64.repr (Int.unsigned (Int.repr b)))) <=
     Int64.unsigned (Int64.repr (sf_outSize s))) ->
  c_ring false obuf sout' (sf_after s zdss_read (if wr then 0 else oend) (if wr then 0 else oend)) fp
    (sublist (oend - ostart) (Zlength pend) pend) lay.
Proof.
intros obuf sout s fp pend lay ostart oend wr sout' fs tabs dd h b Hring Hfr Hfh Hos Hoe Ho Hoe2 Hin Hsz Hlp Hwr Hnwr.
assert (Hmx: Int64.max_unsigned = 2 ^ 64 - 1) by reflexivity.
destruct Hring as (Hnn&Hip&Hin'&os'&oe'&Hos'&Hoe'&Ho'&Hr). cbv iota in Hr.
destruct Hr as (Hoe2'&Hpend&Hplen&Hneed&Hlay).
assert (os' = ostart) by (apply vlong_inj; try lia; congruence).
assert (oe' = oend) by (apply vlong_inj; try lia; congruence).
subst os' oe'.
assert (Hpn': sublist (oend - ostart) (Zlength pend) pend = []) by (rewrite Hlp; apply sublist_nil).
rewrite Hpn'.
pose proof (Zlength_nonneg pend) as Hpl0.
unfold c_ring. cbn [sf_after sf_inBuff sf_inSize sf_outSize sf_ring sf_outStart sf_outEnd sf_outBuff].
split; [exact Hnn|]. split; [exact Hip|]. split; [exact Hin'|].
exists (if wr then 0 else oend), (if wr then 0 else oend).
split; [reflexivity|]. split; [reflexivity|]. split; [destruct wr; lia|]. cbv iota.
split; [destruct wr; lia|].
split; [rewrite sublist_nil; reflexivity|].
split; [rewrite Zlength_nil; destruct fp as [| | |hdr z]; cbn [fp_bsm] in *; try lia;
        destruct Hfr as (_&_&_&_&_&_&_&Hb&_); lia|].
split; [exact Hneed|].
destruct lay as [|eb ec gp|base pe od|base ps pe e].
- destruct Hlay as (Hc&Hz&Hz'). destruct wr; split; auto; lia.
- destruct Hlay as (Hc&Hz&Hz'). destruct wr; split; auto; lia.
- destruct Hlay as (Hb&Hc&Hz&Hz1&Hz2&Hz3). destruct wr; repeat split; auto; lia.
- destruct Hlay as (Hb&Hps&Hpe2&Hpec&Hlr&Hhd&(pre&Hpre)&Hw&Hfcs&Hroom).
  destruct Hfr as (_&_&_&_&_&Hx).
  destruct fp as [|hb|hdr got|hdr z]; try contradiction.
  { destruct Hx as ([Hx|(?&?&?&Hx)]&_); discriminate. }
  destruct Hx as (_&Hfp&Hbsm&Hbsm2&Hws&Hws2&Hfcs0&_).
  rewrite Hfh in Hfp.
  unfold fh_val in Hfp. cbn [fh_adj fh_contentSize fh_blockSizeMax] in Hfp.
  apply pair_equal_spec in Hfp. destruct Hfp as [Hcq Hr]. apply pair_equal_spec in Hr. destruct Hr as [_ Hr].
  apply pair_equal_spec in Hr. destruct Hr as [Hbq _].
  assert (Hfcs': Int64.repr (fh_contentSize h) = Int64.repr (fh_contentSize (zp_h z))) by congruence.
  assert (Hbsm': Int.repr b = Int.repr (zp_bsm z)) by congruence.
  cbn [fp_bsm fp_fcs fp_content fp_ws] in *.
  unfold ZSTD_BLOCKSIZE_MAX in Hbsm2.
  assert (HB: Int.unsigned (Int.repr b) = zp_bsm z)
    by (rewrite Hbsm'; apply Int.unsigned_repr; rep_lia).
  assert (Hadd: Int64.unsigned (Int64.add (Int64.repr oend) (Int64.repr (Int.unsigned (Int.repr b))))
                = oend + zp_bsm z)
    by (rewrite HB, add64_repr; apply Int64.unsigned_repr; lia).
  assert (HO: Int64.unsigned (Int64.repr (sf_outSize s)) = sf_outSize s) by (apply Int64.unsigned_repr; lia).
  assert (Hlt: Int64.ltu (Int64.repr (sf_outSize s)) (Int64.repr (fh_contentSize h)) = true <->
               sf_outSize s < fh_contentSize (zp_h z)).
  { unfold Int64.ltu. rewrite Hfcs', HO, Int64.unsigned_repr by lia.
    destruct (zlt _ _); split; intro; try lia; discriminate. }
  split; [exact Hb|]. split; [exact Hps|]. split; [exact Hpe2|]. split; [exact Hpec|]. split; [exact Hlr|]. split; [exact Hhd|].
  split; [exists (pre ++ pend); rewrite app_nil_r; exact Hpre|].
  split.
  { destruct wr.
    + destruct (Hwr eq_refl) as [Hl1 Hl2]. apply Hlt in Hl1. rewrite HO, Hadd in Hl2.
      right. destruct Hw as [Hw|(_&_&_&_&Hw)]; repeat split; auto; lia.
    + destruct Hw as [Hw|(Hz1&Hz2&_&Hw1&Hw2)]; [left; exact Hw|right]. repeat split; auto. }
  split; [exact Hfcs|].
  intros _. destruct wr.
  + left. destruct (Hwr eq_refl) as [Hl1 _]. apply Hlt in Hl1.
    unfold ring_needed, WILDCOPY_OVERLENGTH, ZSTD_WINDOWSIZE_ABSMIN in Hneed. unfold ZSTD_BLOCKSIZE_MAX in *. lia.
  + destruct (Hnwr eq_refl) as [Hl|Hl].
    * right. destruct (zlt (sf_outSize s) (fh_contentSize (zp_h z))) as [Hc|Hc]; [|lia].
      apply Hlt in Hc. congruence.
    * left. rewrite Hadd, HO in Hl. lia.
Qed.

(* the output is full before the flush completes: someMoreWork := 0, streamStage stays zdss_flush *)
Lemma flush_post_inc : forall a k sv ipc opc oc dl ostart oend,
  dsa_ok a -> call_inv a k sv ipc opc oc dl -> sf_stage (c3_s k) = zdss_flush ->
  sf_outStart (c3_s k) = vlong ostart -> sf_outEnd (c3_s k) = vlong oend ->
  0 <= ostart <= oend -> oend <= sf_outSize (c3_s k) ->
  0 <= sf_inSize (c3_s k) -> sf_inSize (c3_s k) + sf_outSize (c3_s k) <= Ptrofs.max_unsigned ->
  Zlength (sf_ring (c3_s k)) = sf_inSize (c3_s k) + sf_outSize (c3_s k) ->
  a_osz a - opc < oend - ostart ->
  call_inv a (c3_with_s k (sf_after (c3_s k) zdss_flush (ostart + (a_osz a - opc)) oend))
    (sv_flushed sv (a_osz a - opc)) ipc (opc + (a_osz a - opc))
    (copy_cells oc opc (ring_out (c3_s k)) ostart (a_osz a - opc)) (dl ++ sublist 0 (a_osz a - opc) (sv_pend sv)).
Proof.
intros a k sv ipc opc oc dl ostart oend Ha Hinv Hst Hos Hoe Ho Hoe2 Hin Hmax Hrl Hlt.
destruct (flush_facts _ _ _ _ _ _ _ _ _ Hinv Hst Hos Hoe Ho Hoe2 Hin Hmax Hrl) as (Hs&Hlp&Hbp&Hpend&Hsz).
pose proof Hinv as (_&Hopc&_&_&_&_&_&_&_&_&_&_&Hcore&_).
assert (Hlo: Zlength (ring_out (c3_s k)) = sf_outSize (c3_s k)) by (unfold ring_out; rewrite Zlength_sublist; lia).
eapply flush_cells; eauto; try lia; try reflexivity; try (right; reflexivity).
- rewrite Hs in Hcore |- *.
  destruct Hcore as (Hhost&Hcold&Hsz'&Hrest). rewrite Hst in Hhost, Hrest.
  change (zdss_flush =? zdss_init) with false in Hrest. change (zdss_flush =? zdss_loadHeader) with false in Hrest.
  cbv iota in Hrest. destruct Hrest as (Hdisj&Hfr&Hring&Hnst&Hload&Hnl&Hread).
  unfold c_core. cbn [c3_with_s c3_s c3_fs c3_tabs c3_par sf_after sf_stage sf_hostage sf_inPos sf_inSize sf_outSize
                      sv_flushed sv_ahead sv_fp sv_pend sv_lay sv_dd].
  split; [exact Hhost|]. split; [exact Hcold|]. split; [exact Hsz'|].
  change (zdss_flush =? zdss_init) with false. change (zdss_flush =? zdss_loadHeader) with false. cbv iota.
  split; [right; right; reflexivity|]. split; [exact Hfr|].
  split; [eapply ring_inc; eauto; lia|].
  split; [intro Hx; discriminate|]. split; [intro Hx; discriminate|]. split; [exact Hnl|].
  intro Hx; discriminate.
- unfold hist_ok. cbn [c3_with_s c3_s sf_after sf_stage sf_inSize sf_outSize sf_ring sv_flushed sv_lay sv_fp].
  intros Hh Hf _ _. apply Hh; [exact Hf | rewrite Hst; discriminate | rewrite Hst; discriminate].
Qed.

(* the flush completed: streamStage := read, and the ring restarts (wr) or not *)
Lemma flush_post_cpl : forall a k sv ipc opc oc dl h b ostart oend (wr: bool),
  dsa_ok a -> call_inv a k sv ipc opc oc dl -> sf_stage (c3_s k) = zdss_flush ->
  fs_fParams (c3_fs k) = fh_val (fh_adj h b) ->
  sf_outStart (c3_s k) = vlong ostart -> sf_outEnd (c3_s k) = vlong oend ->
  0 <= ostart <= oend -> oend <= sf_outSize (c3_s k) ->
  0 <= sf_inSize (c3_s k) -> sf_inSize (c3_s k) + sf_outSize (c3_s k) <= Ptrofs.max_unsigned ->
  Zlength (sf_ring (c3_s k)) = sf_inSize (c3_s k) + sf_outSize (c3_s k) ->
  oend - ostart <= a_osz a - opc ->
  (wr = true -> Int64.ltu (Int64.repr (sf_outSize (c3_s k))) (Int64.repr (fh_contentSize h)) = true /\
     Int64.unsigned (Int64.repr (sf_outSize (c3_s k))) <
     Int64.unsigned (Int64.add (Int64.repr oend) (Int64.repr (Int.unsigned (Int.repr b))))) ->
  (wr = false -> Int64.ltu (Int64.repr (sf_outSize (c3_s k))) (Int64.repr (fh_contentSize h)) = false \/
     Int64.unsigned (Int64.add (Int64.repr oend) (Int64.repr (Int.unsigned (Int.repr b)))) <=
     Int64.unsigned (Int64.repr (sf_outSize (c3_s k)))) ->
  call_inv a (c3_with_s k (sf_after (c3_s k) zdss_read (if wr then 0 else oend) (if wr then 0 else oend)))
    (sv_flushed sv (oend - ostart)) ipc (opc + (oend - ostart))
    (copy_cells oc opc (ring_out (c3_s k)) ostart (oend - ostart)) (dl ++ sublist 0 (oend - ostart) (sv_pend sv)).
Proof.
intros a k sv ipc opc oc dl h b ostart oend wr Ha Hinv Hst Hfh Hos Hoe Ho Hoe2 Hin Hmax Hrl Hcap Hwr Hnwr.
destruct (flush_facts _ _ _ _ _ _ _ _ _ Hinv Hst Hos Hoe Ho Hoe2 Hin Hmax Hrl) as (Hs&Hlp&Hbp&Hpend&Hsz).
pose proof Hinv as (_&Hopc&_&_&_&_&_&_&_&_&_&_&Hcore&_).
assert (Hlo: Zlength (ring_out (c3_s k)) = sf_outSize (c3_s k)) by (unfold ring_out; rewrite Zlength_sublist; lia).
eapply flush_cells; eauto; try lia; try reflexivity; try (left; reflexivity).
- rewrite Hs in Hcore |- *.
  destruct Hcore as (Hhost&Hcold&Hsz'&Hrest). rewrite Hst in Hhost, Hrest.
  change (zdss_flush =? zdss_init) with false in Hrest. change (zdss_flush =? zdss_loadHeader) with false in Hrest.
  cbv iota in Hrest. destruct Hrest as (Hdisj&Hfr&Hring&Hnst&Hload&Hnl&Hread).
  unfold c_core. cbn [c3_with_s c3_s c3_fs c3_tabs c3_par sf_after sf_stage sf_hostage sf_inPos sf_inSize sf_outSize
                      sv_flushed sv_ahead sv_fp sv_pend sv_lay sv_dd].
  split.
  { destruct Hhost as [[Hx _]|[Hx|(H1&H2&H3&H4&H5&_)]]; [discriminate | right; left; exact Hx |].
    right; right. repeat split; auto; right; left; reflexivity. }
  split; [exact Hcold|]. split; [exact Hsz'|].
  change (zdss_read =? zdss_init) with false. change (zdss_read =? zdss_loadHeader) with false. cbv iota.
  split; [left; reflexivity|]. split; [exact Hfr|].
  split; [eapply ring_cpl; eauto; lia|].
  split; [intro Hx; discriminate|]. split; [intro Hx; discriminate|].
  split; [intros _; apply Hnl; discriminate|].
  intros _. split; [rewrite Hlp; apply sublist_nil | reflexivity].
- unfold hist_ok. cbn [c3_with_s c3_s sf_after sf_stage sf_inSize sf_outSize sf_ring sv_flushed sv_lay sv_fp].
  intros Hh Hf _ _. apply Hh; [exact Hf | rewrite Hst; discriminate | rewrite Hst; discriminate].
Qed.

(* a partial flush leaves output pending *)
Lemma pend_left_nonnil : forall (ocs: list val) ostart oend (pend: list Z) m,
  0 <= ostart <= oend -> oend <= Zlength ocs -> sublist ostart oend ocs = zbytes pend ->
  0 <= m < oend - ostart -> sublist m (Zlength pend) pend <> nil.
Proof.
intros ocs ostart oend pend m Ho Hl Hp Hm E.
apply (f_equal (@Zlength val)) in Hp. rewrite Zlength_sublist in Hp by lia. rewrite Zlength_map in Hp.
apply (f_equal (@Zlength Z)) in E. rewrite Zlength_sublist in E by lia. rewrite Zlength_nil in E. lia.
Qed.

(* the flush cannot complete: someMoreWork := 0 with the output full *)
Lemma flush_exit_inc : forall a k sv ipc opc oc dl s' sv' oc' dl' opc',
  call_inv a k sv ipc opc oc dl -> sf_stage (c3_s k) = zdss_flush -> opc' = a_osz a ->
  sf_stage s' = zdss_flush -> sf_nfp s' = sf_nfp (c3_s k) -> sv_pend sv' <> nil ->
  exit_ok a {| w_smw := 0; w_k := c3_with_s k s'; w_sv := sv'; w_ipc := ipc; w_opc := opc'; w_oc := oc';
               w_dl := dl' |}.
Proof.
intros a k sv ipc opc oc dl s' sv' oc' dl' opc' Hinv Hst Ho Hst' Hnfp Hpn.
destruct Hinv as (_&H2&_&_&_&_&_&_&_&_&Hnfp2&_).
unfold exit_ok. cbn [w_smw w_k w_sv w_ipc w_opc w_oc w_dl c3_with_s c3_s c3_fs]. rewrite Hst', Hnfp.
intros _. unfold zdss_flush, zdss_loadHeader, zdss_read, zdss_load, zdss_init.
split; [lia|]. split; [intros [X|X]; lia|]. split; [intros _; split; [exact Ho | exact Hpn]|]. split.
- intros Hi Ho'. rewrite Hst in Hnfp2. unfold zdss_flush, zdss_loadHeader, zdss_init in Hnfp2.
  destruct Hnfp2 as [X|[X|[X|[X|[X _]]]]]; try lia; auto.
- intros X; lia.
Qed.

End CM_S3FlushLem_1.
