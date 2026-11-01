(* X1D: the body of HUF_decodeSymbolX1 (spec in HufX1DSpecs.v). *)
Require Export Zstd.proof.dec.B.huf.HufX1DSpecs.
Local Open Scope logic.

Lemma x1_cells_length (ht: huf_table) (L: Z) : 0 <= L -> Zlength (x1_cells ht L) = 2 ^ L.
Proof.
  intros HL. unfold x1_cells. rewrite Zlength_map, Zlength_correct, length_seq.
  rewrite Z2Nat.id; [reflexivity|]. apply Z.pow_nonneg; lia.
Qed.

Lemma x1_cells_nth (ht: huf_table) (L v: Z) :
  0 <= v < 2 ^ L -> Znth v (x1_cells ht L) = x1cell (hsym ht L v).
Proof.
  intros Hv. unfold x1_cells.
  assert (HL: 0 <= L) by (destruct (Z_lt_le_dec L 0) as [H|H]; [rewrite Z.pow_neg_r in Hv by lia; lia | lia]).
  rewrite Znth_map by (rewrite Zlength_correct, length_seq, Z2Nat.id by (apply Z.pow_nonneg; lia); lia).
  f_equal. f_equal. rewrite <- nth_Znth by (rewrite Zlength_correct, length_seq, Z2Nat.id by (apply Z.pow_nonneg; lia); lia).
  rewrite seq_nth by lia. simpl. lia.
Qed.

Lemma body_HUF_decodeSymbolX1 :
  semax_body Vprog G_sym f_HUF_decodeSymbolX1 HUF_decodeSymbolX1_spec.
Proof.
  start_function.
  pose proof H as Hok. destruct H as [Hlog1 _].
  assert (Hpow: 2 <= 2 ^ L) by (replace 2 with (2 ^ 1) at 1 by reflexivity; apply Z.pow_le_mono_r; lia).
  assert (HLc: Zlength (x1_cells ht L) = 2 ^ L) by (apply x1_cells_length; lia).
  forward_call (sh, p, gv, s, start, pos, lo, L, np).
  { unfold HUF_TABLELOG_MAX in *; lia. }
  Intros v.
  (* the exact peek: the C's value is xb_look_fast of the reader's state *)
  assert (Hxv: v = xb_look_fast (xb_of s pos lo) L).
  { rewrite (xb_look_rel s pos lo (xb_of s pos lo) L (xb_rel_of s pos lo)) by (unfold HUF_TABLELOG_MAX in *; lia).
    assumption. }
  clear H3.
  destruct (hsym_range ht L v Hok ltac:(lia) ltac:(lia)) as [Hs Hn].
  unfold HUF_TABLELOG_MAX in *.
  forward.
  { entailer!. rewrite x1_cells_nth by lia. unfold x1cell. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
  rewrite x1_cells_nth by lia. unfold x1cell. cbv iota beta.
  forward.
  forward.
  { entailer!. rewrite x1_cells_nth by lia. unfold x1cell. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
  rewrite x1_cells_nth by lia. unfold x1cell. cbv iota beta.
  forward_call (sh, p, gv, s, start, pos, lo, snd (hsym ht L v), np).
  forward.
  Exists (xb_look_fast (xb_of s pos lo) L). entailer!.
Qed.
