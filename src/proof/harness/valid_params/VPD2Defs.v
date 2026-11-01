(* valid_params main, segment D2 (the streaming branch of s16): the loop's statements, states and
   the facts main draws from one ZSTD_decompressStream call (template: valid_stream's v2 main,
   WMain_valid_stream.v, and VSFacts.v). *)
Require Import VST.floyd.proofauto.
Require Export Zstd.proof.harness.valid_params.VPMain.
Require Export Zstd.proof.harness.valid_params.VPMem Zstd.proof.harness.valid_params.VPMem2 Zstd.proof.harness.valid_params.VPMem3.
Require Export Zstd.proof.harness.valid_stream.VSFacts.
Require Import Zstd.proof.zstd.ApiBridge.

Local Notation HCS := Zstd.proof.harness.valid_params.HOK_valid_params.CompSpecs.
Local Notation ZCS := Zstd.proof.zstd.Base.CompSpecs.
Local Notation tout := (Tstruct _ZSTD_outBuffer_s noattr).
Local Notation tin := (Tstruct _ZSTD_inBuffer_s noattr).

(* ---------- the statements ---------- *)

(* VP_stream_s = ipos = 0; got = 0; stalled = 0; within = ...; calls = 0; for (;; calls++) D2_body *)
Definition D2_parts : statement * statement * statement := ltac:(
  let s := eval cbv [VP_stream_s] in VP_stream_s in
  lazymatch s with
  | Ssequence _ (Ssequence _ (Ssequence _ (Ssequence ?w (Ssequence _ (Sloop ?b ?i))))) => exact (w, b, i)
  end).
Definition D2_within : statement := ltac:(let x := eval cbv [D2_parts fst snd] in (fst (fst D2_parts)) in exact x).
Definition D2_body : statement := ltac:(let x := eval cbv [D2_parts fst snd] in (snd (fst D2_parts)) in exact x).
Definition D2_incr : statement := ltac:(let x := eval cbv [D2_parts fst snd] in (snd D2_parts) in exact x).

(* the body from the asserts after the call (D2_mid), and from ZSTD_isError(r) (D2_tail) *)
Definition D2_mid : statement := ltac:(let x := eval cbv [VP_drop D2_body] in (VP_drop 13 D2_body) in exact x).
Definition D2_tail : statement := ltac:(let x := eval cbv [VP_drop D2_body] in (VP_drop 20 D2_body) in exact x).

(* ---------- pure facts ---------- *)

(* main's view of the stream's read bytes: zstd has read ss_ahead (0 or 1) bytes beyond main's ipos *)
Definition D2_in_ok (ss: sstate) (ipos: Z) (bs: list Z) : Prop :=
  0 <= ss_ahead ss <= 1 /\ ipos + ss_ahead ss <= Zlength bs /\ ss_in ss = sublist 0 (ipos + ss_ahead ss) bs.

(* the context during the loop: the parameters p, no dictionary, a stream reading ws' at ipos, having delivered
   got bytes of the content *)
Definition D2_st_ok (p: dparams) (ws': wseries) (C: list Z) (st: dctx_st) (ipos got stalled: Z) : Prop :=
  dc_par st = p /\ dc_dict st = None /\ dc_set st = nil /\ dc_bl st = None /\ dc_stable st = false /\
  ss_err (dc_ss st) = false /\ D2_in_ok (dc_ss st) ipos (ws_bytes ws') /\ ss_out (dc_ss st) = sublist 0 got C /\
  0 <= ss_stall (dc_ss st) <= stalled.

Definition D2_wb (wsr: wseries) (wlim: Z) : bool :=
  andb (within_oneshot_b (ws_frames wsr)) (windows_within_b (ws_frames wsr) wlim).

Lemma D2_sel st : dc_set st = nil -> dc_dict st = None -> st_sel st = (sel_none, Some no_dict).
Proof. intros H1 H2. rewrite st_sel_nil by exact H1. rewrite H2. reflexivity. Qed.

Lemma D2_sin0 (l: list Z) ipos a : 0 <= ipos -> 0 <= a -> ipos + a <= Zlength l ->
  sublist 0 (Zlength (sublist 0 (ipos + a) l) - a) (sublist 0 (ipos + a) l) = sublist 0 ipos l.
Proof.
  intros. rewrite Zlength_sublist by lia. rewrite sublist_sublist by lia. f_equal; lia.
Qed.

(* what main draws from one call on the chunk bs[ipos, ipos + ilen) *)
Lemma D2_post wsr ws' p base wlim st st' r ob osz opos' oc oc' ipos ilen ipos' got stalled :
  VP_dfacts wsr ws' p base wlim ->
  D2_st_ok p ws' (ws_content wsr) st ipos got stalled ->
  0 <= ipos -> 0 <= ilen -> ipos + ilen <= Zlength (ws_bytes ws') -> 0 <= got <= Zlength (ws_content wsr) ->
  stream_post st st' r ob osz 0 opos' oc oc' (sublist ipos (ipos + ilen) (ws_bytes ws')) ilen 0 ipos' ->
  exists dl a' stall',
    (0 <= ipos' <= ilen /\ opos' = Zlength dl /\ Zlength dl <= osz /\ Zlength oc' = osz) /\
    (sublist 0 (Zlength dl) oc' = zbytes dl /\ bytes_ok dl) /\
    (got + Zlength dl <= Zlength (ws_content wsr) /\ dl = sublist got (got + Zlength dl) (ws_content wsr)) /\
    (0 <= a' <= 1 /\ ipos + ipos' + a' <= Zlength (ws_bytes ws')) /\
    st' = set_last (set_ss st {| ss_in := sublist 0 (ipos + ipos' + a') (ws_bytes ws');
                                 ss_out := sublist 0 (got + Zlength dl) (ws_content wsr);
                                 ss_stall := stall'; ss_err := is_error_code r; ss_obuf := None;
                                 ss_ahead := a';
                                 ss_calls := ss_calls (dc_ss st) ++
                                   [(sublist 0 ilen (sublist ipos (ipos + ilen) (ws_bytes ws')), osz - 0)] |})
                    (Some stream_mark) /\
    (is_error_code r = false -> (ipos' <> 0 \/ Zlength dl <> 0) -> stall' = 0) /\
    (is_error_code r = false -> ipos' = 0 -> Zlength dl = 0 -> 0 <= stall' <= stalled + 1) /\
    (is_error_code r = true -> D2_wb wsr wlim = true -> forall e, r = 2 ^ 64 - e ->
       e = ZSTD_error_memory_allocation \/ stall_error_b e stalled ipos' ilen (Zlength dl) osz 0 = true) /\
    (r = 0 -> a' = 0 /\ h_at_end (ws_frames ws') (ipos + ipos') (got + Zlength dl) = true).
Proof.
  intros Hd (Hpar & Hdict & Hset & Hbl & Hstab & Herr & (Ha0 & Ha1 & Ha2) & Hout & Hstl) Hip Hil Hiln Hg Hp.
  pose proof Hd as (Hw & Hc & _). apply VPS_written_w in Hw.
  pose proof Hw as (Hbs & _).
  assert (Hsel: st_sel st = (sel_none, Some no_dict)) by (apply D2_sel; auto).
  destruct Hp as (dl & stall' & a' & H). cbv zeta in H.
  destruct H as (Hop & Hip' & Hoc & _ & Hdlen0 & Hcells & Ha' & Hia & Hia2 & Hhost & Hst' & Hs1 & Hs2 & _ & Hstall & Hcl & _).
  rewrite Hsel, Hpar, Hstab in *. cbn [fst snd] in *.
  rewrite Ha2 in Hst', Hcl, Hcells. rewrite Hout in Hst', Hcl.
  destruct (VSF_read (ws_bytes ws') ipos ilen (ss_ahead (dc_ss st)) ipos' a') as [Hsin Hlen']; try lia.
  rewrite Hsin in Hst', Hcl, Hcells.
  rewrite D2_sin0 in Hcl by lia.
  assert (Hpin: is_prefix (sublist 0 (ipos + ipos' + a') (ws_bytes ws')) (ws_bytes ws'))
    by (apply VSF_is_prefix_sublist; lia).
  assert (Hsall: is_prefix (sublist 0 (ipos + ipos' + a') (ws_bytes ws') ++
                   sublist (ipos' + a') ilen (sublist ipos (ipos + ilen) (ws_bytes ws'))) (ws_bytes ws'))
    by (apply VSF_sall; lia).
  destruct (Hcells (or_intror (VPS_alive _ ws' _ Hw Hpin))) as [Hdl Hbo]. clear Hcells.
  pose proof (VPS_content _ ws' _ _ _ _ _ _ _ _ _ Hw Hpin Hcl) as Hpre'.
  rewrite Hc in Hpre'.
  apply VSF_prefix_app in Hpre'; [|lia]. destruct Hpre' as [Hgot' Hdl'].
  exists dl, a', stall'.
  rewrite Z.sub_0_r in Hdlen0. subst opos'.
  split; [lia|].
  split; [split; assumption|].
  split; [split; assumption|].
  split; [lia|].
  split.
  { rewrite Hst'. f_equal. f_equal. f_equal. apply VSF_out_app; auto; lia. }
  split; [intros E1 E2; apply Hs1; auto; lia|].
  split; [intros E1 E2 E3; specialize (Hs2 E1 ltac:(lia) ltac:(lia)); lia|].
  split.
  { intros Er Hwb e He.
    unfold D2_wb in Hwb. apply andb_prop in Hwb. destruct Hwb as [Hw1 Hw2].
    pose proof Hd as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hall & _).
    specialize (Hall Hw1 Hw2).
    destruct (VPS_err _ ws' _ _ _ _ _ _ _ _ Hw Hall Hpin Hsall Hcl Er e He) as [X | X]; [left; exact X|].
    right. apply (VSF_stall r e (ss_stall (dc_ss st))); auto; lia. }
  intros Hr0. subst r.
  assert (Ea: a' = 0) by (apply (stream_hostage_zero a' 0); auto).
  split; [exact Ea|]. subst a'.
  pose proof (VPS_zero _ ws' _ _ _ _ _ _ _ _ 0 Hw Hpin Hcl eq_refl) as Hz.
  rewrite Zlength_sublist, Zlength_app, Zlength_sublist in Hz by lia.
  replace (ipos + ipos' + 0 - 0) with (ipos + ipos') in Hz by lia.
  replace (got - 0 + Zlength dl) with (got + Zlength dl) in Hz by lia. exact Hz.
Qed.

(* ---------- the loop's states ---------- *)

Section States.
Variable DC : globals -> val -> dctx_st -> mpred.
Variable WG : globals -> mpred.

(* the frame of the loop: main's memory with the context in state st *)
Definition D2_R (gv: globals) (vz vi vo: val) (wsr ws': wseries) (src dctx: val) (st: dctx_st) : list mpred :=
  [mem_mgr gv; zstd_globals gv; WG gv; DC gv dctx st;
   data_at Ews t_wseries (wseries_val wsr) (gv _x_valid_params__sr);
   malloc_token Ews (tarray tuchar (Zlength (ws_bytes ws'))) src;
   data_at Ews (tarray tuchar (Zlength (ws_bytes ws'))) (zbytes (ws_bytes ws')) src;
   data_at_ Tsh t_fh vz; data_at_ Tsh tin vi; data_at_ Tsh tout vo; TT; has_ext tt].

(* the loop's locals other than its counters *)
Definition D2_L (gv: globals) (vz vi vo: val) (ws': wseries) (base: Z) (wb: bool) (src dctx: val) : list localdef :=
  [temp _within (Vint (Int.repr (if wb then 1 else 0))); temp _base (Vlong (Int64.repr base));
   temp _n (Vlong (Int64.repr (Zlength (ws_bytes ws')))); temp _src src; temp _dctx dctx;
   lvar _zfh t_fh vz; lvar _in tin vi; lvar _out tout vo; gvars gv].

(* the loop's state at the top of an iteration (Pc: the bounds of calls and stalled) *)
Definition D2_A (gv: globals) (vz vi vo: val) (wsr ws': wseries) (p: dparams) (base: Z) (wb: bool) (src dctx: val)
    (Pc: Prop) (calls ipos got stalled: Z) (st: dctx_st) : environ -> mpred :=
  PROPx (Pc :: (0 <= ipos <= Zlength (ws_bytes ws')) :: (0 <= got <= Zlength (ws_content wsr)) ::
         D2_st_ok p ws' (ws_content wsr) st ipos got stalled :: nil)
  (LOCALx (temp _calls (Vlong (Int64.repr calls)) :: temp _ipos (Vlong (Int64.repr ipos)) ::
           temp _got (Vlong (Int64.repr got)) :: temp _stalled (Vlong (Int64.repr stalled)) ::
           D2_L gv vz vi vo ws' base wb src dctx)
  (SEPx (D2_R gv vz vi vo wsr ws' src dctx st))).

Definition D2_inv gv vz vi vo wsr ws' p base wb src dctx : environ -> mpred :=
  EX calls: Z, EX ipos: Z, EX got: Z, EX stalled: Z, EX st: dctx_st,
    D2_A gv vz vi vo wsr ws' p base wb src dctx (0 <= calls <= 4096 /\ 0 <= stalled <= calls) calls ipos got stalled st.

Definition D2_cont gv vz vi vo wsr ws' p base wb src dctx : environ -> mpred :=
  EX calls: Z, EX ipos: Z, EX got: Z, EX stalled: Z, EX st: dctx_st,
    D2_A gv vz vi vo wsr ws' p base wb src dctx (0 <= calls < 4096 /\ 0 <= stalled <= calls + 1) calls ipos got stalled st.

Definition D2_brk gv vz vi vo wsr ws' src dctx : environ -> mpred :=
  EX st: dctx_st, VP_SD1 DC WG gv vz vi vo wsr ws' src dctx st.

(* the body's post: continue with D2_cont, break with D2_brk *)
Definition D2_RA gv vz vi vo wsr ws' p base wb src dctx (R0: ret_assert) : ret_assert :=
  loop1_ret_assert (D2_cont gv vz vi vo wsr ws' p base wb src dctx) (overridePost (D2_brk gv vz vi vo wsr ws' src dctx) R0).

(* at D2_tail (after free(ob)): the call returned r, read ipos' of the chunk of ilen bytes at ib and delivered
   opos' bytes into ob of osz bytes; main's counters are ip2 (ipos + ipos'), got2 (got + opos'), stalled *)
Definition D2_M2 (gv: globals) (vz vi vo: val) (wsr ws': wseries) (base: Z) (wb: bool) (src dctx: val)
    (calls ip2 got2 stalled: Z) (ib: val) (ilen ipos': Z) (ob: val) (osz opos' r: Z) (st': dctx_st)
    : environ -> mpred :=
  PROPx nil
  (LOCALx (temp _r (Vlong (Int64.repr r)) ::
           temp _calls (Vlong (Int64.repr calls)) :: temp _ipos (Vlong (Int64.repr ip2)) ::
           temp _got (Vlong (Int64.repr got2)) :: temp _stalled (Vlong (Int64.repr stalled)) ::
           D2_L gv vz vi vo ws' base wb src dctx)
  (SEPx [mem_mgr gv; zstd_globals gv; WG gv; DC gv dctx st';
         data_at Ews t_wseries (wseries_val wsr) (gv _x_valid_params__sr);
         malloc_token Ews (tarray tuchar (Zlength (ws_bytes ws'))) src;
         data_at Ews (tarray tuchar (Zlength (ws_bytes ws'))) (zbytes (ws_bytes ws')) src;
         data_at_ Tsh t_fh vz;
         data_at Tsh tin (ib, (Vlong (Int64.repr ilen), Vlong (Int64.repr ipos'))) vi;
         data_at Tsh tout (ob, (Vlong (Int64.repr osz), Vlong (Int64.repr opos'))) vo;
         TT; has_ext tt])).

End States.

(* the facts at D2_tail (from D2_post) *)
Definition D2_M2_ok (wsr ws': wseries) (p: dparams) (base wlim: Z)
    (calls ip2 got2 stalled ilen ipos' osz opos' r: Z) (st': dctx_st) : Prop :=
  VP_dfacts wsr ws' p base wlim /\
  0 <= calls < 4096 /\ 0 <= stalled <= calls /\
  0 <= ip2 <= Zlength (ws_bytes ws') /\ 0 <= got2 <= Zlength (ws_content wsr) /\
  0 <= ipos' <= ilen /\ ilen <= Zlength (ws_bytes ws') /\ 0 <= opos' <= osz /\ osz <= 2 ^ 18 + 1 /\
  0 <= r <= Int64.max_unsigned /\
  dc_par st' = p /\ dc_dict st' = None /\ dc_set st' = nil /\ dc_bl st' = None /\ dc_stable st' = false /\
  ss_err (dc_ss st') = is_error_code r /\ D2_in_ok (dc_ss st') ip2 (ws_bytes ws') /\
  ss_out (dc_ss st') = sublist 0 got2 (ws_content wsr) /\
  (is_error_code r = false -> (ipos' <> 0 \/ opos' <> 0) -> ss_stall (dc_ss st') = 0) /\
  (is_error_code r = false -> ipos' = 0 -> opos' = 0 -> 0 <= ss_stall (dc_ss st') <= stalled + 1) /\
  (is_error_code r = true -> D2_wb wsr wlim = true -> forall e, r = 2 ^ 64 - e ->
     e = ZSTD_error_memory_allocation \/ stall_error_b e stalled ipos' ilen opos' osz 0 = true) /\
  (r = 0 -> h_at_end (ws_frames ws') ip2 got2 = true).
