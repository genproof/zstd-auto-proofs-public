(* res_free's streaming step (harness/res_free.c):

     do { in.size += upto(n - in.size); out.size = out.pos + upto(cap - out.pos); }
     while (!ZSTD_isError(r = ZSTD_decompressStream(dctx, &out, &in)) && nondet_u8() != 0);
     if (ZSTD_isError(r)) ZSTD_DCtx_reset(dctx, ZSTD_reset_session_only);

   on a context in any rf_inv state without a failed stream (rf_ok): it may be inside a frame, since a reset with
   ZSTD_reset_parameters does not end a stream.  Each call gets the prefixes of the two buffers up to in.size and
   out.size, with the rest of each buffer and its token as the pointer witnesses (buf_ok_split), and the harness's
   DDict when the context reads it (dd_lend).  A call that fails ends the loop, and the session reset that follows
   gives a context without a failed stream again. *)
Require Import VST.floyd.proofauto.
Require Export Zstd.proof.harness.res_free.Kit_res_free.

Section Stream.
Variable DC : globals -> val -> dctx_st -> mpred.
Variable DD : globals -> val -> ddict_st -> mpred.

(* a byte array as its first k bytes and the rest, and back: each call of the loop gets the prefix of a buffer
   up to its size, the rest is lent as a witness and joined again after the call *)
Lemma bytes_split {cs: compspecs} sh n k (v: list val) p : 0 <= k <= n -> Zlength v = n ->
  data_at sh (tarray tuchar n) v p |--
  !! field_compatible (tarray tuchar n) nil p &&
  (data_at sh (tarray tuchar k) (sublist 0 k v) p * data_at sh (tarray tuchar (n - k)) (sublist k n v) (offset_val k p)).
Proof.
  intros Hk Hv. apply andp_right; [entailer! |].
  assert_PROP (field_compatible (tarray tuchar n) nil p) by entailer!.
  unfold tarray in *. rewrite (split2_data_at_Tarray_tuchar sh n k v p) by auto.
  rewrite field_address0_offset by auto with field_compatible.
  simpl nested_field_offset. replace (0 + 1 * k) with k by lia. cancel.
Qed.

Lemma bytes_join {cs: compspecs} sh n k (v1 v2: list val) p : field_compatible (tarray tuchar n) nil p ->
  Zlength v1 = k -> Zlength v2 = n - k -> 0 <= k <= n ->
  data_at sh (tarray tuchar k) v1 p * data_at sh (tarray tuchar (n - k)) v2 (offset_val k p) |--
  data_at sh (tarray tuchar n) (v1 ++ v2) p.
Proof.
  intros Hf H1 H2 Hk. unfold tarray in *.
  rewrite (split2_data_at_Tarray_tuchar sh n k (v1 ++ v2) p) by (try rewrite Zlength_app; lia).
  rewrite field_address0_offset by auto with field_compatible.
  simpl nested_field_offset. replace (0 + 1 * k) with k by lia.
  rewrite sublist_app1 by lia. rewrite sublist_app2 by lia.
  rewrite sublist_same by lia. rewrite sublist_same by lia. cancel.
Qed.

(* the stream's buffers as ZSTD_decompressStream takes them (mbuf: NULL only for an empty buffer); main's are never
   NULL *)
Lemma mbuf_i sh n c p : isptr p -> @data_at Zstd.proof.zstd.Base.CompSpecs sh (tarray tuchar n) c p |-- mbuf sh n c p.
Proof. intros Hp. unfold mbuf. rewrite if_false by (intro E; subst; contradiction). apply derives_refl. Qed.

Lemma mbuf_e sh n c p : isptr p -> mbuf sh n c p |-- @data_at Zstd.proof.zstd.Base.CompSpecs sh (tarray tuchar n) c p.
Proof. intros Hp. unfold mbuf. rewrite if_false by (intro E; subst; contradiction). apply derives_refl. Qed.

(* the streaming step, from a context in any rf_inv state (also inside a frame) without a failed stream, the input
   s at ps and the output buffer of c bytes at pd *)
Lemma stream_seg {Espec: OracleKind} gv v_now v_mem v_in v_out dctx (m: cmem) q dd st s c ps b i :
  m = the_cm gv v_now -> rf_inv m q dd st -> rf_ok st -> is_pointer_or_null q -> dctx <> nullval -> isptr v_now ->
  0 <= Zlength s <= 9223372036854775807 -> 0 <= c <= 9223372036854775807 -> bytes_ok s -> isptr ps ->
  semax (func_tycontext f_main Vprog (G0 DC DD) nil)
   (PROP ( )
    LOCAL (temp _dst (Vptr b i); temp _src ps; temp _cap (Vlong (Int64.repr c));
           temp _n (Vlong (Int64.repr (Zlength s))); temp _dctx dctx; temp _ddict q;
           lvar _out (Tstruct _ZSTD_outBuffer_s noattr) v_out; lvar _in (Tstruct _ZSTD_inBuffer_s noattr) v_in;
           lvar _mem (Tstruct ___gp_ZSTD_customMem noattr) v_mem; lvar _now tulong v_now; gvars gv)
    SEP (mem_mgr gv; malloc_token Ews (tarray tuchar c) (Vptr b i); data_at_ Ews (tarray tuchar c) (Vptr b i);
         malloc_token Ews (tarray tuchar (Zlength s)) ps; data_at Ews (tarray tuchar (Zlength s)) (zbytes s) ps;
         DC gv dctx st;
         data_at Tsh (Tstruct ___gp_ZSTD_customMem noattr) (gv _count_alloc, (gv _count_free, v_now)) v_mem;
         data_at Tsh (Tstruct _ZSTD_outBuffer_s noattr)
           (Vptr b i, (fst (snd (default_val (Tstruct _ZSTD_outBuffer_s noattr))),
                       Vlong (Int64.repr (Int.signed (Int.repr 0))))) v_out;
         data_at Tsh (Tstruct _ZSTD_inBuffer_s noattr)
           (ps, (Vlong (Int64.repr (Int.signed (Int.repr 0))), Vlong (Int64.repr (Int.signed (Int.repr 0))))) v_in;
         ddict_hold DD gv q dd; dd_tok q dd; zstd_globals gv; TT))
   stream_part
   (normal_ret_assert (dec_post DC DD gv v_now v_mem v_in v_out dctx m q dd s c ps (Vptr b i))).
Proof.
  intros Em Hinv Hok Hq Hd Hnow Hs Hc Hbs Hps.
  unfold stream_part.
  forward_loop (EX st1: dctx_st, EX isz: Z, EX ipos: Z, EX opos: Z, EX ov: val, EX oc: list val,
    PROP (rf_inv m q dd st1; rf_ok st1; 0 <= ipos <= isz; isz <= Zlength s; 0 <= opos <= c; Zlength oc = c)
    LOCAL (temp _dst (Vptr b i); temp _src ps; temp _cap (Vlong (Int64.repr c));
           temp _n (Vlong (Int64.repr (Zlength s))); temp _dctx dctx; temp _ddict q;
           lvar _out (Tstruct _ZSTD_outBuffer_s noattr) v_out; lvar _in (Tstruct _ZSTD_inBuffer_s noattr) v_in;
           lvar _mem (Tstruct ___gp_ZSTD_customMem noattr) v_mem; lvar _now tulong v_now; gvars gv)
    SEP (mem_mgr gv; malloc_token Ews (tarray tuchar c) (Vptr b i); data_at Ews (tarray tuchar c) oc (Vptr b i);
         malloc_token Ews (tarray tuchar (Zlength s)) ps; data_at Ews (tarray tuchar (Zlength s)) (zbytes s) ps;
         DC gv dctx st1;
         data_at Tsh (Tstruct ___gp_ZSTD_customMem noattr) (gv _count_alloc, (gv _count_free, v_now)) v_mem;
         data_at Tsh (Tstruct _ZSTD_outBuffer_s noattr) (Vptr b i, (ov, Vlong (Int64.repr opos))) v_out;
         data_at Tsh (Tstruct _ZSTD_inBuffer_s noattr) (ps, (Vlong (Int64.repr isz), Vlong (Int64.repr ipos))) v_in;
         ddict_hold DD gv q dd; dd_tok q dd; zstd_globals gv; TT))%assert
    break: (EX st1: dctx_st, EX r: Z, EX oc: list val, EX vi: reptype (Tstruct _ZSTD_inBuffer_s noattr),
      EX vo: reptype (Tstruct _ZSTD_outBuffer_s noattr),
    PROP (rf_inv m q dd st1; ss_err (dc_ss st1) = is_error_code r; 0 <= r <= Int64.max_unsigned; Zlength oc = c)
    LOCAL (temp _r (Vlong (Int64.repr r)); temp _dst (Vptr b i); temp _src ps; temp _cap (Vlong (Int64.repr c));
           temp _n (Vlong (Int64.repr (Zlength s))); temp _dctx dctx; temp _ddict q;
           lvar _out (Tstruct _ZSTD_outBuffer_s noattr) v_out; lvar _in (Tstruct _ZSTD_inBuffer_s noattr) v_in;
           lvar _mem (Tstruct ___gp_ZSTD_customMem noattr) v_mem; lvar _now tulong v_now; gvars gv)
    SEP (mem_mgr gv; malloc_token Ews (tarray tuchar c) (Vptr b i); data_at Ews (tarray tuchar c) oc (Vptr b i);
         malloc_token Ews (tarray tuchar (Zlength s)) ps; data_at Ews (tarray tuchar (Zlength s)) (zbytes s) ps;
         DC gv dctx st1;
         data_at Tsh (Tstruct ___gp_ZSTD_customMem noattr) (gv _count_alloc, (gv _count_free, v_now)) v_mem;
         data_at Tsh (Tstruct _ZSTD_outBuffer_s noattr) vo v_out; data_at Tsh (Tstruct _ZSTD_inBuffer_s noattr) vi v_in;
         ddict_hold DD gv q dd; dd_tok q dd; zstd_globals gv; TT))%assert.
  { Exists st 0 0 0 (fst (snd (default_val (Tstruct _ZSTD_outBuffer_s noattr)))) (default_val (tarray tuchar c)).
    entailer!. unfold default_val; simpl. rewrite Zlength_Zrepeat by lia. reflexivity. }
  2: { (* after the loop: a failed stream is reset (zstd.h: "it must be first reset") *)
    Intros st1 r oc vi vo.
    forward_call r.
    destruct (is_error_code r) eqn:Herr.
    - forward_if; [| discriminate].
      forward_call (gv, dctx, st1, ZSTD_reset_session_only).
      Intros vret. destruct vret as [r1 st2]. cbn [fst snd] in *.
      match goal with Hr: reset_post _ _ _ _ |- _ => destruct (reset_post_session _ _ _ Hr) as [_ ->] end.
      assert (Hi2: rf_inv m q dd (set_ex (set_ss st1 ss_init) false)) by (apply rf_set_ex, rf_set_ss; assumption).
      assert (Ho2: rf_ok (set_ex (set_ss st1 ss_init) false)) by (unfold rf_ok; reflexivity).
      unfold dec_post. Exists (set_ex (set_ss st1 ss_init) false) oc vi vo.
      entailer; cancel.
    - forward_if; [exfalso; match goal with Hn: Int.repr 0 <> Int.zero |- _ => apply Hn; reflexivity end |].
      assert (Ho1: rf_ok st1) by (unfold rf_ok; congruence).
      forward. unfold dec_post. Exists st1 oc vi vo. entailer; cancel. }
  Intros st1 isz ipos opos ov oc.
  forward.
  forward_call (Zlength s - isz).
  Intros k1. forward. forward. forward. forward_call (c - opos). Intros k2. forward. forward.
  rewrite !add64_repr.
  set (isz' := isz + k1). set (osz := opos + k2). set (pd := Vptr b i).
  assert (Hi': isz <= isz' <= Zlength s) by (unfold isz'; lia).
  assert (Ho': opos <= osz <= c) by (unfold osz; lia).
  sep_apply (bytes_split Ews (Zlength s) isz' (zbytes s) ps ltac:(lia) ltac:(rewrite Zlength_map; reflexivity)).
  sep_apply (bytes_split Ews c osz oc pd ltac:(lia) ltac:(lia)).
  Intros.
  rewrite !sublist_map.
  set (W := [pw_token Ews (tarray tuchar (Zlength s)) ps;
             pw_bytes Ews (Zlength s - isz') (zbytes (sublist isz' (Zlength s) s)) (offset_val isz' ps);
             pw_token Ews (tarray tuchar c) pd; pw_bytes Ews (c - osz) (sublist osz c oc) (offset_val osz pd)]
            ++ dd_wits q dd).
  sep_apply (to_Z Ews isz' (zbytes (sublist 0 isz' s)) ps).
  sep_apply (mbuf_i Ews isz' (zbytes (sublist 0 isz' s)) ps Hps).
  sep_apply (to_Z Ews (Zlength s - isz') (zbytes (sublist isz' (Zlength s) s)) (offset_val isz' ps)).
  sep_apply (to_Z Ews osz (sublist 0 osz oc) pd).
  sep_apply (mbuf_i Ews osz (sublist 0 osz oc) pd Logic.I).
  sep_apply (to_Z Ews (c - osz) (sublist osz c oc) (offset_val osz pd)).
  sep_apply (tok_to_Z Ews (Zlength s) ps).
  sep_apply (tok_to_Z Ews c pd).
  sep_apply (inb_to_Z Tsh ps (Vlong (Int64.repr isz')) (Vlong (Int64.repr ipos)) v_in).
  sep_apply (outb_to_Z Tsh pd (Vlong (Int64.repr osz)) (Vlong (Int64.repr opos)) v_out).
  assert (Ew: pws_pred W = (@malloc_token Zstd.units.Zstd.CS Ews (tarray tuchar (Zlength s)) ps *
     (@data_at Zstd.units.Zstd.CS Ews (tarray tuchar (Zlength s - isz')) (zbytes (sublist isz' (Zlength s) s)) (offset_val isz' ps) *
     (@malloc_token Zstd.units.Zstd.CS Ews (tarray tuchar c) pd *
     (@data_at Zstd.units.Zstd.CS Ews (tarray tuchar (c - osz)) (sublist osz c oc) (offset_val osz pd) * dd_tok q dd))))%logic).
  { unfold W, pws_pred. rewrite map_app, fold_right_app. rewrite <- dd_wits_pred. reflexivity. }
  sep_apply (dd_lend DD m gv q dd st1 H).
  assert (HW1: In (pw_token Ews (tarray tuchar (Zlength s)) ps) W) by (unfold W; simpl; tauto).
  assert (HW2: In (pw_bytes Ews (Zlength s - isz') (zbytes (sublist isz' (Zlength s) s)) (offset_val isz' ps)) W)
    by (unfold W; simpl; tauto).
  assert (HW3: In (pw_token Ews (tarray tuchar c) pd) W) by (unfold W; simpl; tauto).
  assert (HW4: In (pw_bytes Ews (c - osz) (sublist osz c oc) (offset_val osz pd)) W) by (unfold W; simpl; tauto).
  assert (HW5: incl (dd_wits q dd) W) by (unfold W; intros x Hx; simpl; tauto).
  forward_call (W, gv, dctx, st1, v_out, v_in, Tsh, Tsh, Ews, pd, osz, opos, sublist 0 osz oc,
                Ews, ps, isz', ipos, sublist 0 isz' s).
  { rewrite Ew. cancel. }
  { destruct H as (Hm1 & Hb1 & Hst1 & Hrest).
    split; [eapply buf_ok_split; [exact HW3 | exact HW4 | auto | auto | lia | exact Logic.I] |].
    split; [eapply buf_ok_split; [exact HW1 | exact HW2 | auto | auto | lia | exact Hps] |].
    split; [intros E; congruence |]. split; [intros E; congruence |].
    split; [apply (rf_stream_dict_ok m W q dd st1); [split; auto | exact HW5] |].
    split; [rewrite Zlength_sublist; lia |]. split; [rewrite Zlength_sublist; lia |].
    apply Forall_sublist; exact Hbs. }
  Intros vret. destruct vret as [[[[r opos'] ipos'] oc'] st']. cbn [fst snd] in *.
  match goal with Hp: stream_post _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    destruct (rf_stream m q dd st1 st' r pd osz opos opos' (sublist 0 osz oc) oc' (sublist 0 isz' s) isz' ipos ipos' H Hp)
      as (Hinv' & Herr' & Hop & Hip & Hoc') end.
  sep_apply (dd_unlend DD m gv q dd st1 H).
  rewrite Ew. Intros.
  sep_apply (drop_vp (DC gv dctx st') dctx).
  sep_apply (mbuf_e Ews osz oc' pd Logic.I).
  sep_apply (mbuf_e Ews isz' (zbytes (sublist 0 isz' s)) ps Hps).
  sep_apply (of_Z Ews osz oc' pd).
  sep_apply (of_Z Ews isz' (zbytes (sublist 0 isz' s)) ps).
  sep_apply (of_Z Ews (Zlength s - isz') (zbytes (sublist isz' (Zlength s) s)) (offset_val isz' ps)).
  sep_apply (of_Z Ews (c - osz) (sublist osz c oc) (offset_val osz pd)).
  sep_apply (tok_of_Z Ews (Zlength s) ps).
  sep_apply (tok_of_Z Ews c pd).
  sep_apply (inb_of_Z Tsh ps (Vlong (Int64.repr isz')) (Vlong (Int64.repr ipos')) v_in).
  sep_apply (outb_of_Z Tsh pd (Vlong (Int64.repr osz)) (Vlong (Int64.repr opos')) v_out).
  sep_apply (bytes_join Ews c osz oc' (sublist osz c oc) pd H7 Hoc' ltac:(rewrite Zlength_sublist; lia) ltac:(lia)).
  sep_apply (bytes_join Ews (Zlength s) isz' (zbytes (sublist 0 isz' s)) (zbytes (sublist isz' (Zlength s) s)) ps H8
    ltac:(rewrite Zlength_map, Zlength_sublist; lia) ltac:(rewrite Zlength_map, Zlength_sublist; lia) ltac:(lia)).
  rewrite <- map_app, sublist_rejoin, sublist_same by lia.
  forward.
  forward_call r.
  apply semax_if_seq. destruct (is_error_code r) eqn:Herr.
  { forward_if; [discriminate | ]. forward. forward_if; [contradiction |]. forward.
    Exists st' r (oc' ++ sublist osz c oc) (ps, (Vlong (Int64.repr isz'), Vlong (Int64.repr ipos')))
      (pd, (Vlong (Int64.repr osz), Vlong (Int64.repr opos'))).
    entailer!.
    apply derives_refl. }
  forward_if; [| first [discriminate | contradiction]]. forward_call tt. Intros u8. forward.
  forward_if.
  { forward. Exists st' isz' ipos' opos' (Vlong (Int64.repr osz)) (oc' ++ sublist osz c oc).
    assert (rf_ok st') by (unfold rf_ok; exact Herr'). entailer!.
    apply derives_refl. }
  forward.
  Exists st' r (oc' ++ sublist osz c oc) (ps, (Vlong (Int64.repr isz'), Vlong (Int64.repr ipos')))
    (pd, (Vlong (Int64.repr osz), Vlong (Int64.repr opos'))).
  entailer!.
  apply derives_refl.
Qed.

End Stream.
