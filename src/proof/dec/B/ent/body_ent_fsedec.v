(* Group ENT: bodies of FSE_decode_copy, FSE_initDState, FSE_decodeSymbol, FSE_decodeSymbolFast. *)
Require Import Zstd.proof.dec.B.ent.EntSpecs.
Local Open Scope logic.

Lemma body_FSE_decode_copy : semax_body Vprog G_B0 f_FSE_decode_copy FSE_decode_copy_spec.
Proof.
  start_function.
  assert_PROP (value_fits t_fdec (Znth i (map fdcell es))).
  { entailer!. apply Forall_Znth; auto. rewrite Zlength_map; lia. }
  rewrite Znth_map in H0 by lia. unfold fdcell in H0. rewrite value_fits_eq in H0. simpl in H0.
  destruct H0 as (Hb & Hs & Hn).
  rewrite value_fits_eq in Hb, Hs, Hn. simpl in Hb, Hs, Hn.
  specialize (Hb ltac:(discriminate)). specialize (Hs ltac:(discriminate)).
  specialize (Hn ltac:(discriminate)).
  assert_PROP (field_compatible (tarray t_fdec (Zlength es)) [] tb) by entailer!.
  assert (Hp: offset_val (4 * i) tb = field_address (tarray t_fdec (Zlength es)) [ArraySubsc i] tb).
  { rewrite field_address_offset by auto with field_compatible. simpl. f_equal. }
  rewrite Hp.
  forward. { entailer!. rewrite Znth_map by lia. exact Hb. }
  forward.
  forward. { entailer!. rewrite Znth_map by lia. exact Hs. }
  forward.
  forward. { entailer!. rewrite Znth_map by lia. exact Hn. }
  forward.
  entailer!. rewrite Znth_map by lia. unfold fdcell. simpl. cancel.
Qed.

Lemma body_FSE_initDState : semax_body Vprog G_B0 f_FSE_initDState FSE_initDState_spec.
Proof.
  start_function.
  unfold fsedt_at. Intros. destruct H1 as (Hlog & Hlen & Hcells).
  forward. forward. forward.
  { entailer!. lia. }
  forward_call (shb, bp, gv, s, start, pos, lo, ft_log t).
  Intros r.
  forward.
  forward_call (shb, bp, gv, s, start, pos - ft_log t, lo, shsrc, srcp, buf, off).
  forward.
  Exists r. unfold fsedt_at. entailer!.
  - unfold fse_dt_ok; auto.
  - apply derives_refl.
Qed.

Lemma fse_cell_Znth (t: fse_table) (st: Z) :
  0 <= st < Zlength (ft_cells t) -> fse_cell t st = Znth st (ft_cells t).
Proof.
  intros. unfold fse_cell, Znth. rewrite if_false by lia. reflexivity.
Qed.

Lemma body_FSE_decodeSymbol :
  semax_body Vprog (G_B0 ++ [FSE_decode_copy_spec]) f_FSE_decodeSymbol FSE_decodeSymbol_spec.
Proof.
  start_function.
  unfold fsedt_at. Intros. destruct H2 as (Hlog & Hlen & Hcells).
  rewrite fse_cell_Znth in * by lia.
  assert (He := proj1 (Forall_Znth _ _) Hcells st ltac:(lia)). simpl in He.
  set (e := Znth st (ft_cells t)) in *.
  assert (Hp1: 2 ^ ft_log t <= 4096) by (change 4096 with (2 ^ 12); apply Z.pow_le_mono_r; lia).
  assert (Hp2: 0 < 2 ^ fe_nb e) by (apply Z.pow_pos_nonneg; lia).
  forward. forward.
  rewrite <- Hlen.
  forward_call (sht, offset_val 4 dt, ft_cells t, st, Tsh, v_DInfo).
  { entailer!. }
  fold e.
  change (fdcell e) with
    (Vint (Int.repr (fe_base e)), (Vint (Int.repr (fe_sym e)), Vint (Int.repr (fe_nb e)))).
  forward. { entailer!; rep_lia. }
  forward. { entailer!; rep_lia. }
  forward.
  forward_call (shb, bp, gv, s, start, pos, lo, fe_nb e).
  Intros r.
  forward. { entailer!; rep_lia. }
  forward.
  forward.
  Exists r. unfold fsedt_at. rewrite Hlen. rewrite fse_cell_Znth by lia. fold e. entailer!.
  unfold fse_dt_ok; auto.
Qed.

Lemma body_FSE_decodeSymbolFast :
  semax_body Vprog (G_B0 ++ [FSE_decode_copy_spec]) f_FSE_decodeSymbolFast FSE_decodeSymbolFast_spec.
Proof.
  start_function.
  unfold fsedt_at. Intros. destruct H2 as (Hlog & Hlen & Hcells).
  rewrite fse_cell_Znth in * by lia.
  assert (He := proj1 (Forall_Znth _ _) Hcells st ltac:(lia)). simpl in He.
  set (e := Znth st (ft_cells t)) in *.
  specialize (H1 eq_refl).
  assert (Hp1: 2 ^ ft_log t <= 4096) by (change 4096 with (2 ^ 12); apply Z.pow_le_mono_r; lia).
  assert (Hp2: 0 < 2 ^ fe_nb e) by (apply Z.pow_pos_nonneg; lia).
  forward. forward.
  rewrite <- Hlen.
  forward_call (sht, offset_val 4 dt, ft_cells t, st, Tsh, v_DInfo).
  { entailer!. }
  fold e.
  change (fdcell e) with
    (Vint (Int.repr (fe_base e)), (Vint (Int.repr (fe_sym e)), Vint (Int.repr (fe_nb e)))).
  forward. { entailer!; rep_lia. }
  forward. { entailer!; rep_lia. }
  forward.
  forward_call (shb, bp, gv, s, start, pos, lo, fe_nb e).
  Intros r.
  forward. { entailer!; rep_lia. }
  forward.
  forward.
  Exists r. unfold fsedt_at. rewrite Hlen. rewrite fse_cell_Znth by lia. fold e. entailer!.
  unfold fse_dt_ok; auto.
Qed.

Lemma body_ent_fsedec :
  semax_body Vprog G_B0 f_FSE_decode_copy FSE_decode_copy_spec /\
  semax_body Vprog G_B0 f_FSE_initDState FSE_initDState_spec /\
  semax_body Vprog (G_B0 ++ [FSE_decode_copy_spec]) f_FSE_decodeSymbol FSE_decodeSymbol_spec /\
  semax_body Vprog (G_B0 ++ [FSE_decode_copy_spec]) f_FSE_decodeSymbolFast FSE_decodeSymbolFast_spec.
Proof.
  split; [exact body_FSE_decode_copy |].
  split; [exact body_FSE_initDState |].
  split; [exact body_FSE_decodeSymbol | exact body_FSE_decodeSymbolFast].
Qed.
