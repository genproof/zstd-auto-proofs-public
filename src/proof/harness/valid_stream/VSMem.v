(* valid_stream's main and the harness's static sr (a wseries_t of 786936 bytes): its fields one by one, and the
   bytes main lends to exact_copy.  Never let VST compute on the whole struct: forward on data_at t_wseries
   overflows the stack (it builds lists of 2^19 elements); main works on the six field_at's. *)
Require Import VST.floyd.proofauto.
Require Export Zstd.proof.harness.valid_stream.WTopSpecs_valid_stream.

Local Notation HCS := Zstd.proof.harness.valid_stream.HOK_valid_stream.CompSpecs.

(* the fields of sr holding ws *)
Definition VS_fields (ws: wseries) (p: val) : list mpred :=
  [@field_at HCS Ews t_wseries (DOT _bytes)
     (zbytes (ws_bytes ws) ++ Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength (ws_bytes ws))) p;
   @field_at HCS Ews t_wseries (DOT _n) (vl (Zlength (ws_bytes ws))) p;
   @field_at HCS Ews t_wseries (DOT _content)
     (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws))) p;
   @field_at HCS Ews t_wseries (DOT _content_n) (vl (Zlength (ws_content ws))) p;
   @field_at HCS Ews t_wseries (DOT _f)
     (map winfo_val (ws_frames ws) ++ Zrepeat (winfo_val winfo0) (4 - Zlength (ws_frames ws))) p;
   @field_at HCS Ews t_wseries (DOT _nframes) (vu (Zlength (ws_frames ws))) p;
   spacer Ews 786932 786936 p].

Lemma VS_sr_fold ws p :
  fold_right_sepcon (VS_fields ws p) |-- @data_at HCS Ews t_wseries (wseries_val ws) p.
Proof.
  unfold VS_fields. simpl fold_right_sepcon.
  unfold_data_at (@data_at HCS Ews t_wseries _ _). unfold wseries_val; cbn [fst snd].
  cancel.
Qed.

(* the bytes [ipos, ipos + ilen) of sr.bytes, lent to exact_copy(sr.bytes + ipos, ilen) *)
Lemma VS_bytes_borrow (ws: wseries) p ipos ilen :
  0 <= ipos -> 0 <= ilen -> ipos + ilen <= Zlength (ws_bytes ws) -> Zlength (ws_bytes ws) <= 2 ^ 19 ->
  @field_at HCS Ews t_wseries (DOT _bytes)
    (zbytes (ws_bytes ws) ++ Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength (ws_bytes ws))) p |--
  @data_at HCS Ews (tarray tuchar (Zlength (sublist ipos (ipos + ilen) (ws_bytes ws))))
    (zbytes (sublist ipos (ipos + ilen) (ws_bytes ws))) (offset_val ipos p) *
  (@data_at HCS Ews (tarray tuchar (Zlength (sublist ipos (ipos + ilen) (ws_bytes ws))))
     (zbytes (sublist ipos (ipos + ilen) (ws_bytes ws))) (offset_val ipos p) -*
   @field_at HCS Ews t_wseries (DOT _bytes)
     (zbytes (ws_bytes ws) ++ Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength (ws_bytes ws))) p).
Proof.
  intros H0 H1 H2 H3.
  assert_PROP (@field_compatible HCS t_wseries (DOT _bytes) p) by entailer!.
  rewrite field_at_data_at. rewrite field_address_offset by auto.
  set (bs := ws_bytes ws) in *. set (L := zbytes bs ++ _).
  simpl nested_field_type. simpl nested_field_offset.
  assert (HL: Zlength L = 524288) by (subst L; list_solve).
  assert (HB: sublist ipos (ipos + ilen) L = zbytes (sublist ipos (ipos + ilen) bs)) by (subst L; list_solve).
  assert (HZ: Zlength (sublist ipos (ipos + ilen) bs) = ilen) by list_solve.
  rewrite HZ.
  assert_PROP (field_compatible (tarray tuchar 524288) nil (offset_val 0 p)) by entailer!.
  unfold tarray. rewrite (split3_data_at_Tarray_tuchar Ews 524288 ipos (ipos + ilen) L) by lia.
  rewrite HB. replace (ipos + ilen - ipos) with ilen by lia.
  rewrite field_address0_offset by auto with field_compatible.
  replace (offset_val (nested_field_offset (Tarray tuchar 524288 noattr) (SUB ipos)) (offset_val 0 p))
    with (offset_val ipos p)
    by (rewrite offset_offset_val; simpl nested_field_offset; f_equal; simpl sizeof; lia).
  match goal with |- sepcon (sepcon ?A ?B) ?C |-- _ =>
    apply derives_trans with (sepcon B (sepcon A C));
    [cancel | apply sepcon_derives; [apply derives_refl | rewrite <- wand_sepcon_adjoint; cancel]] end.
Qed.
