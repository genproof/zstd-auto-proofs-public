(* valid_params main, segment D2 (see the header of VPMain.v). *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.harness.valid_params.VPMain.
Require Import Zstd.proof.harness.valid_params.VPD2Defs.
Require Import Zstd.proof.harness.valid_params.VPD2A.

Local Notation HCS := Zstd.proof.harness.valid_params.HOK_valid_params.CompSpecs.
Local Notation ZCS := Zstd.proof.zstd.Base.CompSpecs.
Local Notation tout := (Tstruct _ZSTD_outBuffer_s noattr).
Local Notation tin := (Tstruct _ZSTD_inBuffer_s noattr).

Section Seg.
Context {Espec: OracleKind}.
Variable DC : globals -> val -> dctx_st -> mpred.
Variable DD : globals -> val -> ddict_st -> mpred.
Variable WG : globals -> mpred.
Variable WDS : wdict -> reptype t_wstate -> Prop.
Local Notation Delta := (VP_Delta DC DD WG WDS).

(* D2: the streaming branch of s16 *)
Lemma VP_segD2 (gv: globals) (vz vi vo: val) (wsr ws': wseries) (p: dparams) (base wlim: Z) (src dctx: val) :
  semax Delta (VP_SD0 DC WG gv vz vi vo wsr ws' p base wlim src dctx) VP_stream_s
    (normal_ret_assert (EX st: dctx_st, VP_SD1 DC WG gv vz vi vo wsr ws' src dctx st)).
Proof.
unfold VP_SD0, VP_stream_s, VP_Delta. simplify_func_tycontext. abbreviate_semax. Intros.
match goal with H: VP_dfacts _ _ _ _ _ |- _ => rename H into Hd end.
pose proof Hd as (Hw & Hc & Hbs' & Hbase & HN0 & Hbok & Hcok & HN & HC & Hnf & Hwf & Hfb & Hwl & _).
unfold vl.
forward. forward. forward.
forward_call (Ews, gv _x_valid_params__sr, wsr).
change (Int.signed (Int.repr 0)) with 0. unfold vb.
forward_if (PROP () LOCAL (temp _x_valid_params__t'47 (Vint (Int.repr (if D2_wb wsr wlim then 1 else 0)));
   temp _stalled (Vlong (Int64.repr 0)); temp _got (Vlong (Int64.repr 0)); temp _ipos (Vlong (Int64.repr 0));
   temp _wlim (Vlong (Int64.repr wlim)); temp _base (Vlong (Int64.repr base));
   temp _n (Vlong (Int64.repr (Zlength (ws_bytes ws')))); temp _src src; temp _dctx dctx;
   lvar _zfh t_fh vz; lvar _in tin vi; lvar _out tout vo; gvars gv)
  SEP (data_at Ews t_wseries (wseries_val wsr) (gv _x_valid_params__sr);
   mem_mgr gv; zstd_globals gv; WG gv; DC gv dctx (set_par dctx_init p);
   malloc_token Ews (tarray tuchar (Zlength (ws_bytes ws'))) src;
   data_at Ews (tarray tuchar (Zlength (ws_bytes ws'))) (zbytes (ws_bytes ws')) src; data_at_ Tsh t_fh vz;
   data_at_ Tsh tin vi; data_at_ Tsh tout vo; TT; has_ext tt)).
{ forward_call (gv, Ews, wsr, wlim).
  unfold vb. forward. entailer!.
  unfold D2_wb. destruct (within_oneshot_b _); [|contradiction H'; reflexivity].
  destruct (windows_within_b _ _); reflexivity. }
{ forward. entailer!. unfold D2_wb. destruct (within_oneshot_b _); [discriminate|]. reflexivity. }
forward. forward.
apply (semax_post1_flipped (D2_brk DC WG gv vz vi vo wsr ws' src dctx)).
2: { unfold D2_brk. Intros st. apply andp_left2. Exists st. apply derives_refl. }
apply semax_pre with (D2_inv DC WG gv vz vi vo wsr ws' p base (D2_wb wsr wlim) src dctx).
{ unfold D2_inv, D2_A, D2_R, D2_L. Exists 0 0 0 0 (set_par dctx_init p). entailer!.
  unfold D2_st_ok, D2_in_ok; simpl. rewrite !sublist_nil. repeat split; auto; lia. }
apply (semax_loop _ _ (D2_cont DC WG gv vz vi vo wsr ws' p base (D2_wb wsr wlim) src dctx)).
2: { unfold D2_cont, D2_inv, D2_A, D2_L. Intros calls ipos got stalled st. forward.
     Exists (calls + 1) ipos got stalled st. entailer!. }
unfold D2_inv. Intros calls ipos got stalled st.
apply (D2_body_ok DC DD WG WDS gv vz vi vo wsr ws' p base wlim src dctx calls ipos got stalled st _ Hd Psrc).
Qed.

End Seg.
