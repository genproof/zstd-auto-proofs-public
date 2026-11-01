(* valid_params main, segment DE (see the header of VPMain.v). *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.harness.valid_params.VPMain.
Require Import Zstd.proof.harness.valid_params.VPSegD1.
Require Import Zstd.proof.harness.valid_params.VPSegD2.

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

(* D: s16, dispatching to D1 / D2 *)
Lemma VP_segD (gv: globals) (vz vi vo: val) (mode: Z) (ws: wseries) (b': list Z) (p: dparams) (wlim: Z)
    (src dctx: val) :
  (forall st, semax Delta (VP_SD1 DC WG gv vz vi vo (ws_ck ws b') (vp_view mode ws b') src dctx st) (VP_rest 17) VP_RR) ->
  semax Delta (VP_SB DC WG gv vz vi vo mode ws b' p wlim src dctx) (VP_rest 16) VP_RR.
Proof.
  intros HE. unfold VP_rest.
  assert (E16: VP_drop 16 VP_body0 = Ssequence VP_s16 (VP_drop 17 VP_body0)) by reflexivity.
  rewrite E16. apply -> seq_assoc.
  eapply semax_seq' with (P' := EX st: dctx_st, VP_SD1 DC WG gv vz vi vo (ws_ck ws b') (vp_view mode ws b') src dctx st).
  2: { Intros st. apply HE. }
  unfold VP_SB, VP_Delta. Intros.
  match goal with H: VP_SB_facts _ _ _ _ _ |- _ => destruct H as (HA & HD & Hsrc & _) end.
  rewrite <- Hsrc.
  match goal with |- semax _ _ ?c _ => let x := eval cbv [VP_s16 VP_drop VP_body0] in c in change c with x end.
  abbreviate_semax.
  forward_call 2.
  Intros t.
  forward_if.
  - unfold MORE_COMMANDS, POSTCONDITION, abbreviate.
    eapply semax_pre; [| apply (VP_segD1 DC DD WG WDS gv vz vi vo (ws_ck ws b') (vp_view mode ws b') p (vp_base mode) wlim src dctx)].
    unfold VP_SD0. entailer!.
  - unfold MORE_COMMANDS, POSTCONDITION, abbreviate.
    eapply semax_pre; [| apply (VP_segD2 DC DD WG WDS gv vz vi vo (ws_ck ws b') (vp_view mode ws b') p (vp_base mode) wlim src dctx)].
    unfold VP_SD0. entailer!.
Qed.

(* E: s17..s19 *)
Lemma VP_segE (gv: globals) (vz vi vo: val) (wsr ws': wseries) (src dctx: val) (st: dctx_st) :
  semax Delta (VP_SD1 DC WG gv vz vi vo wsr ws' src dctx st) (VP_rest 17) VP_RR.
Proof.
  unfold VP_rest, VP_RR, VP_SD1, VP_Delta.
  match goal with |- semax _ _ (Ssequence ?a _) _ => let x := eval cbv [VP_drop VP_body0] in a in change a with x end.
  abbreviate_semax.
  forward_call (gv, dctx, Some st).
  assert_PROP (isptr src) by entailer!.
  forward_call (tarray tuchar (Zlength (ws_bytes ws')), src, gv).
  rewrite if_false by (destruct src; try contradiction; discriminate).
  sep_apply (data_at_data_at_ Ews (tarray tuchar (Zlength (ws_bytes ws'))) (zbytes (ws_bytes ws')) src). cancel.
  (* the return with only the stack frame left (no big struct at a return: keeps Qed fast) *)
  eapply semax_pre with (P' := PROP () LOCAL (lvar _zfh t_fh vz; lvar _in tin vi; lvar _out tout vo)
                                SEP (data_at_ Tsh t_fh vz; data_at_ Tsh tin vi; data_at_ Tsh tout vo; TT)).
  1: entailer!.
  forward.
  cancel.
Qed.

End Seg.
