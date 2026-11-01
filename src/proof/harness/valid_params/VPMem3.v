(* valid_params's main: folding the fields of sr back (for within_stream). *)
Require Import VST.floyd.proofauto.
Require Export Zstd.proof.harness.valid_params.VPMem.

Local Notation HCS := Zstd.proof.harness.valid_params.HOK_valid_params.CompSpecs.

Lemma VP_sr_fold7 ws p :
  @field_at HCS Ews t_wseries (DOT _bytes)
    (zbytes (ws_bytes ws) ++ Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength (ws_bytes ws))) p *
  @field_at HCS Ews t_wseries (DOT _n) (vl (Zlength (ws_bytes ws))) p *
  @field_at HCS Ews t_wseries (DOT _content)
    (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws))) p *
  @field_at HCS Ews t_wseries (DOT _content_n) (vl (Zlength (ws_content ws))) p *
  @field_at HCS Ews t_wseries (DOT _f)
    (map winfo_val (ws_frames ws) ++ Zrepeat (winfo_val winfo0) (4 - Zlength (ws_frames ws))) p *
  @field_at HCS Ews t_wseries (DOT _nframes) (vu (Zlength (ws_frames ws))) p *
  spacer Ews 786932 786936 p |-- @data_at HCS Ews t_wseries (wseries_val ws) p.
Proof.
  pose proof (VP_sr_fold ws p) as H. unfold VP_fields in H. simpl fold_right_sepcon in H.
  rewrite !sepcon_assoc. rewrite sepcon_emp in H. exact H.
Qed.

(* ... and unfolding them, as a lemma: unfolding the 786936-byte struct inside main costs the kernel minutes
   at Qed *)
Lemma VP_sr_unfold7 ws p :
  @data_at HCS Ews t_wseries (wseries_val ws) p |--
  @field_at HCS Ews t_wseries (DOT _bytes)
    (zbytes (ws_bytes ws) ++ Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength (ws_bytes ws))) p *
  @field_at HCS Ews t_wseries (DOT _n) (vl (Zlength (ws_bytes ws))) p *
  @field_at HCS Ews t_wseries (DOT _content)
    (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws))) p *
  @field_at HCS Ews t_wseries (DOT _content_n) (vl (Zlength (ws_content ws))) p *
  @field_at HCS Ews t_wseries (DOT _f)
    (map winfo_val (ws_frames ws) ++ Zrepeat (winfo_val winfo0) (4 - Zlength (ws_frames ws))) p *
  @field_at HCS Ews t_wseries (DOT _nframes) (vu (Zlength (ws_frames ws))) p *
  spacer Ews 786932 786936 p.
Proof.
  unfold_data_at (@data_at HCS Ews t_wseries _ _). unfold wseries_val; cbn [fst snd].
  cancel.
Qed.

(* the fields of sr as plain mpreds: main's SEP keeps these names, so the kernel does not recompute their
   field types (reptype through the composite environment) at every step of the proof; main unfolds one
   only around the loads from it *)
Definition VP_Rb (v: list val) (p: val) : mpred := @field_at HCS Ews t_wseries (DOT _bytes) v p.
Definition VP_Rn (v: val) (p: val) : mpred := @field_at HCS Ews t_wseries (DOT _n) v p.
Definition VP_Rc (v: list val) (p: val) : mpred := @field_at HCS Ews t_wseries (DOT _content) v p.
Definition VP_Rcn (v: val) (p: val) : mpred := @field_at HCS Ews t_wseries (DOT _content_n) v p.
Definition VP_Rf (v: list (reptype t_winfo)) (p: val) : mpred := @field_at HCS Ews t_wseries (DOT _f) v p.
Definition VP_Rnf (v: val) (p: val) : mpred := @field_at HCS Ews t_wseries (DOT _nframes) v p.

Lemma VP_sr_unfold7w ws p :
  @data_at HCS Ews t_wseries (wseries_val ws) p |--
  VP_Rb (zbytes (ws_bytes ws) ++ Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength (ws_bytes ws))) p *
  VP_Rn (vl (Zlength (ws_bytes ws))) p *
  VP_Rc (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws))) p *
  VP_Rcn (vl (Zlength (ws_content ws))) p *
  VP_Rf (map winfo_val (ws_frames ws) ++ Zrepeat (winfo_val winfo0) (4 - Zlength (ws_frames ws))) p *
  VP_Rnf (vu (Zlength (ws_frames ws))) p *
  spacer Ews 786932 786936 p.
Proof. unfold VP_Rb, VP_Rn, VP_Rc, VP_Rcn, VP_Rf, VP_Rnf. apply VP_sr_unfold7. Qed.

Lemma VP_sr_fold7w ws p :
  VP_Rb (zbytes (ws_bytes ws) ++ Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength (ws_bytes ws))) p *
  VP_Rn (vl (Zlength (ws_bytes ws))) p *
  VP_Rc (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws))) p *
  VP_Rcn (vl (Zlength (ws_content ws))) p *
  VP_Rf (map winfo_val (ws_frames ws) ++ Zrepeat (winfo_val winfo0) (4 - Zlength (ws_frames ws))) p *
  VP_Rnf (vu (Zlength (ws_frames ws))) p *
  spacer Ews 786932 786936 p |-- @data_at HCS Ews t_wseries (wseries_val ws) p.
Proof. unfold VP_Rb, VP_Rn, VP_Rc, VP_Rcn, VP_Rf, VP_Rnf. apply VP_sr_fold7. Qed.

Lemma VP_bytes_borrow_w (ws: wseries) p ipos ilen :
  0 <= ipos -> 0 <= ilen -> ipos + ilen <= Zlength (ws_bytes ws) -> Zlength (ws_bytes ws) <= 2 ^ 19 ->
  VP_Rb (zbytes (ws_bytes ws) ++ Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength (ws_bytes ws))) p |--
  @data_at HCS Ews (tarray tuchar (Zlength (sublist ipos (ipos + ilen) (ws_bytes ws))))
    (zbytes (sublist ipos (ipos + ilen) (ws_bytes ws))) (offset_val ipos p) *
  (@data_at HCS Ews (tarray tuchar (Zlength (sublist ipos (ipos + ilen) (ws_bytes ws))))
     (zbytes (sublist ipos (ipos + ilen) (ws_bytes ws))) (offset_val ipos p) -*
   VP_Rb (zbytes (ws_bytes ws) ++ Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength (ws_bytes ws))) p).
Proof. unfold VP_Rb. apply VP_bytes_borrow. Qed.
