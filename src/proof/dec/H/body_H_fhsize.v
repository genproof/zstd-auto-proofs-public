(* Subtree H: ZSTD_frameHeaderSize_internal, ZSTD_errorFrameSizeInfo, ZSTD_findFrameCompressedSize_advanced.  Prove each body against H_G (HSpecs.v); helper lemmas go above. *)
Require Import Zstd.proof.dec.H.HLemmas.
Local Open Scope logic.

Lemma body_errorFrameSizeInfo :
  semax_body Vprog H_G f_ZSTD_errorFrameSizeInfo ZSTD_errorFrameSizeInfo_spec.
Proof.
  start_function.
  forward. forward. entailer!.
  replace (Int64.repr (- (2))) with (Int64.repr ZSTD_CONTENTSIZE_ERROR);
    [cancel | apply Int64.eqm_samerepr; exists 1; reflexivity].
Qed.

Lemma body_findFrameCompressedSize_advanced :
  semax_body Vprog H_G f_ZSTD_findFrameCompressedSize_advanced ZSTD_findFrameCompressedSize_advanced_spec.
Proof.
  start_function.
  forward_call (gv, Tsh, v_frameSizeInfo, sh, base, N, c, off, s).
  Intros vret. destruct vret as [[nb cs] db]; simpl fst in *; simpl snd in *.
  forward. forward.
  Exists cs. entailer!.
  rewrite frame_compressed_size_info. destruct (frame_size_info s) as [[k b]|]; simpl; tauto.
Qed.

(* the do { ... } while (0) blocks of zstd's error macros *)
Ltac dw0_side :=
  first [ solve [entailer!] | solve [forward; entailer!]
        | solve [match goal with |- semax _ ?Pre _ _ => forward_if Pre; [congruence | ..]; try forward; entailer! end] ].
Ltac dw0 :=
  match goal with |- semax _ ?Pre (Ssequence (Sloop _ Sbreak) _) _ =>
    forward_loop Pre break: Pre; [dw0_side .. | idtac] end.

(* the two tables read by ZSTD_frameHeaderSize_internal, apart from the other globals *)
Definition zg_rest_fhs (gv: globals) : mpred := (
  data_at Ews tint g_debuglevel_val (gv _g_debuglevel) *
  data_at Ers (tarray tuint 32) DeBruijnBytePos_val (gv _DeBruijnBytePos) *
  data_at Ers (tarray tuint 32) DeBruijnClz_val (gv _DeBruijnClz) *
  data_at Ers tulong zeroFilled_val (gv _zeroFilled) *
  data_at Ers (Tstruct ___gp_ZSTD_customMem noattr) ZSTD_defaultCMem_val (gv _ZSTD_defaultCMem) *
  data_at Ers (tarray tuint 3) repStartValue_val (gv _repStartValue) *
  data_at Ers tulong ZSTD_blockHeaderSize_val (gv _ZSTD_blockHeaderSize) *
  data_at Ers (tarray tuchar 36) LL_bits_val (gv _LL_bits) *
  data_at Ers (tarray tuchar 53) ML_bits_val (gv _ML_bits) *
  data_at Ers (tarray (tarray (Tstruct ___gp_algo_time_t noattr) 2) 16) algoTime_val (gv _algoTime) *
  data_at Ers (tarray tuint 36) LL_base_val (gv _LL_base) *
  data_at Ers (tarray tuint 32) OF_base_val (gv _OF_base) *
  data_at Ers (tarray tuchar 32) OF_bits_val (gv _OF_bits) *
  data_at Ers (tarray tuint 53) ML_base_val (gv _ML_base) *
  data_at Ers (tarray (Tstruct ___gp_ZSTD_seqSymbol noattr) 65) LL_defaultDTable_val (gv _LL_defaultDTable) *
  data_at Ers (tarray (Tstruct ___gp_ZSTD_seqSymbol noattr) 33) OF_defaultDTable_val (gv _OF_defaultDTable) *
  data_at Ers (tarray (Tstruct ___gp_ZSTD_seqSymbol noattr) 65) ML_defaultDTable_val (gv _ML_defaultDTable) *
  data_at Ers (tarray tuint 8) dec32table_val (gv _dec32table) *
  data_at Ers (tarray tint 8) dec64table_val (gv _dec64table) *
  eb_res gv)%logic.

Lemma zg_fhs gv : zstd_globals gv =
  (data_at Ers (tarray tulong 4) ZSTD_did_fieldSize_val (gv _ZSTD_did_fieldSize) *
   data_at Ers (tarray tulong 4) ZSTD_fcs_fieldSize_val (gv _ZSTD_fcs_fieldSize) * zg_rest_fhs gv)%logic.
Proof. unfold zstd_globals, zg_rest_fhs. apply pred_ext; cancel. Qed.

Lemma did_at (dflt: Inhabitant val) d: 0 <= d < 4 ->
  @Znth val dflt d ZSTD_did_fieldSize_val = Vlong (Int64.repr (nth (Z.to_nat d) [0; 1; 2; 4] 0)).
Proof. intros Hd. assert (d = 0 \/ d = 1 \/ d = 2 \/ d = 3) as [-> | [-> | [-> | ->]]] by lia; reflexivity. Qed.

Lemma fcs_at (dflt: Inhabitant val) f: 0 <= f < 4 ->
  @Znth val dflt f ZSTD_fcs_fieldSize_val = Vlong (Int64.repr (nth (Z.to_nat f) [0; 2; 4; 8] 0)).
Proof. intros Hf. assert (f = 0 \/ f = 1 \/ f = 2 \/ f = 3) as [-> | [-> | [-> | ->]]] by lia; reflexivity. Qed.

(* the bit fields of the frame header descriptor, checked on every byte *)
Definition fhd_bits_ok (b: Z) : bool :=
  Int.eq (Int.zero_ext 8 (Int.repr b)) (Int.repr b) &&
  Int.eq (Int.shr (Int.repr b) (Int.repr 6)) (Int.repr (Z.shiftr b 6)) &&
  Int.eq (Int.and (Int.shr (Int.repr b) (Int.repr 5)) (Int.repr 1)) (Int.repr (Z.land (Z.shiftr b 5) 1)) &&
  Int.eq (Int.and (Int.repr b) (Int.repr 3)) (Int.repr (Z.land b 3)) &&
  (0 <=? Z.shiftr b 6) && (Z.shiftr b 6 <? 4) && (0 <=? Z.land b 3) && (Z.land b 3 <? 4) &&
  ((Z.land (Z.shiftr b 5) 1 =? 0) || (Z.land (Z.shiftr b 5) 1 =? 1)).

Lemma fhd_bits_all: forallb fhd_bits_ok (map Z.of_nat (seq 0 256)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma fhd_bits: forall b, 0 <= b < 256 ->
  Int.zero_ext 8 (Int.repr b) = Int.repr b /\
  Int.shr (Int.repr b) (Int.repr 6) = Int.repr (Z.shiftr b 6) /\
  Int.and (Int.shr (Int.repr b) (Int.repr 5)) (Int.repr 1) = Int.repr (Z.land (Z.shiftr b 5) 1) /\
  Int.and (Int.repr b) (Int.repr 3) = Int.repr (Z.land b 3) /\
  0 <= Z.shiftr b 6 < 4 /\ 0 <= Z.land b 3 < 4 /\
  (Z.land (Z.shiftr b 5) 1 = 0 \/ Z.land (Z.shiftr b 5) 1 = 1).
Proof.
  intros b Hb. assert (Hin: In b (map Z.of_nat (seq 0 256))).
  { apply in_map_iff. exists (Z.to_nat b). split; [lia|]. apply in_seq. lia. }
  pose proof (proj1 (forallb_forall _ _) fhd_bits_all b Hin) as H. unfold fhd_bits_ok in H.
  repeat match goal with Hx: andb _ _ = true |- _ => apply andb_prop in Hx; destruct Hx end.
  repeat match goal with
         | Hx: Int.eq _ _ = true |- _ => apply Int.same_if_eq in Hx
         | Hx: (_ <=? _) = true |- _ => apply Z.leb_le in Hx
         | Hx: (_ <? _) = true |- _ => apply Z.ltb_lt in Hx
         | Hx: orb _ _ = true |- _ => apply orb_true_iff in Hx; rewrite !Z.eqb_eq in Hx
         end.
  tauto.
Qed.

Lemma body_frameHeaderSize_internal :
  semax_body Vprog H_G f_ZSTD_frameHeaderSize_internal ZSTD_frameHeaderSize_internal_spec.
Proof.
  start_function.
  forward_call tt.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_loop (PROPx P (LOCALx Q (SEPx R)))
      continue: (PROPx ((5 <= Zlength s) :: P) (LOCALx Q (SEPx R)))
      break: (PROPx ((5 <= Zlength s) :: P) (LOCALx Q (SEPx R))) end.
  { entailer!. }
  { forward_if.
    { do 4 dw0.
      forward.
      destruct H as (Hr & Ho & Hn & HN & Hc & Hs & Hb & Hsub).
      Exists (Int64.modulus - 72). entailer!.
      apply Int64.ltu_inv in H0. unfold ZSTD_FRAMEHEADERSIZE_PREFIX in H0.
      rewrite !Int64.unsigned_repr in H0 by rep_lia.
      unfold frame_header_size. rewrite (proj2 (Z.ltb_lt _ _)) by (unfold ZSTD_FRAMEHEADERSIZE_PREFIX; lia).
      split; [unfold dec_err, ZSTD_error_noForwardProgress_destFull, ZSTD_error_noForwardProgress_inputEmpty;
              split; [reflexivity | split; let E := fresh "E" in intro E; compute in E; discriminate]|]. f_equal. apply Int64.eqm_samerepr. exists (-1). reflexivity. }
    { forward. destruct H as (Hr & Ho & Hn & HN & Hc & Hs & Hb & Hsub).
      unfold Int64.ltu, ZSTD_FRAMEHEADERSIZE_PREFIX in H0.
      rewrite !Int64.unsigned_repr in H0 by rep_lia. if_tac in H0; [discriminate|]. entailer!. } }
  { forward. entailer!. }
  Intros. pose proof H as Hw. destruct H as (Hr & Ho & Hn & HN & Hc & Hs & Hb & Hsub).
  assert_PROP (field_compatible (tarray tuchar N) [] base) as Hfc by entailer!.
  rewrite (win_split sh N c off s base Hw Hfc). Intros.
  assert (0 <= ZSTD_FRAMEHEADERSIZE_PREFIX - 1 < Zlength s) by (unfold ZSTD_FRAMEHEADERSIZE_PREFIX; lia).
  forward.
  all: unfold ZSTD_FRAMEHEADERSIZE_PREFIX in *; simpl Z.sub.
  all: assert (Hb4: 0 <= Znth 4 s < 256) by (apply (proj1 (Forall_Znth _ _) Hb); lia).
  1: { entailer!. rep_lia. }
  assert (Hbat: byte_at s 4 = Znth 4 s) by reflexivity.
  forget (Znth 4 s) as b.
  forward. forward. forward. forward.
  destruct (fhd_bits b Hb4) as (E1 & E2 & E3 & E4 & Rf & Rd & Rs).
  rewrite E1, E2, E3, E4.
  set (f := Z.shiftr b 6) in *. set (d := Z.land b 3) in *. set (ss := Z.land (Z.shiftr b 5) 1) in *.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _t'2 (Vint (Int.repr (if andb (ss =? 1) (f =? 0) then 1 else 0))) :: Q) (SEPx R))) end.
  { forward. entailer!. destruct Rs as [Hz|Hz]; [contradiction|]. rewrite Hz. simpl.
    destruct (Z.eqb_spec f 0) as [Ef|Ef]; [rewrite Ef; reflexivity|].
    rewrite Int.eq_false; [reflexivity|]. intro Hf. apply Ef. apply repr_inj_unsigned in Hf; rep_lia. }
  { forward. entailer!. destruct Rs as [Hz|Hz]; rewrite Hz in *; [reflexivity|].
    apply repr_inj_unsigned in H1; rep_lia. }
  assert (Hfhd: fhd_header_size b = 5 + (1 - ss) + nth (Z.to_nat d) [0; 1; 2; 4] 0 + nth (Z.to_nat f) [0; 2; 4; 8] 0
                  + (if andb (ss =? 1) (f =? 0) then 1 else 0)) by reflexivity.
  clearbody f d ss.
  rewrite zg_fhs. Intros.
  forward.
  1: { rewrite (did_at _ d Rd). entailer!. }
  rewrite (did_at _ d Rd).
  forward.
  1: { rewrite (fcs_at _ f Rf). entailer!. }
  rewrite (fcs_at _ f Rf).
  forward. Exists (fhd_header_size (byte_at s 4)).
  rewrite zg_fhs. rewrite (win_split sh _ c off s base Hw Hfc). entailer!.
  unfold frame_header_size, ZSTD_FRAMEHEADERSIZE_PREFIX. rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite Hfhd.
  assert (d = 0 \/ d = 1 \/ d = 2 \/ d = 3) as [-> | [-> | [-> | ->]]] by lia;
  assert (f = 0 \/ f = 1 \/ f = 2 \/ f = 3) as [-> | [-> | [-> | ->]]] by lia;
  destruct Rs as [-> | ->]; (split; [compute; split; congruence | split; reflexivity]).
Qed.

Lemma bodies_H_fhsize :
  semax_body Vprog H_G f_ZSTD_frameHeaderSize_internal ZSTD_frameHeaderSize_internal_spec /\
  semax_body Vprog H_G f_ZSTD_errorFrameSizeInfo ZSTD_errorFrameSizeInfo_spec /\
  semax_body Vprog H_G f_ZSTD_findFrameCompressedSize_advanced ZSTD_findFrameCompressedSize_advanced_spec.
Proof.
  split; [|split]; [apply body_frameHeaderSize_internal | apply body_errorFrameSizeInfo | apply body_findFrameCompressedSize_advanced].
Qed.
