(* VST helper lemmas for main of harness/valid_info.c (WMain_valid_info): the fields of sr / wd, one frame
   record of sr.f, splitting src at a frame's start and dst at its capacity. *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.harness.valid_info.WTopSpecs_valid_info.

Lemma VI_wd_fields sh (v: reptype t_wdict) p :
  data_at sh t_wdict v p |--
  field_at sh t_wdict (DOT _bytes) (fst v) p * field_at sh t_wdict (DOT _n) (fst (snd v)) p *
  field_at sh t_wdict (DOT _formatted) (fst (snd (snd v))) p *
  field_at sh t_wdict (DOT _id) (fst (snd (snd (snd v)))) p * TT.
Proof.
  unfold_data_at (data_at sh t_wdict v p). cancel.
Qed.

Lemma VI_wd_bytes sh b rest p :
  Zlength b <= 6144 ->
  field_at sh t_wdict (DOT _bytes) (zbytes b ++ rest) p |--
  data_at sh (tarray tuchar (Zlength b)) (zbytes b) (field_address t_wdict (DOT _bytes) p) * TT.
Proof.
  intros Hb. pose proof (Zlength_nonneg b). rewrite field_at_data_at.
  change (nested_field_type t_wdict (DOT _bytes)) with (tarray tuchar 6144).
  assert_PROP (Zlength (zbytes b ++ rest) = 6144) as Hl.
  { entailer!. }
  rewrite (split2_data_at_Tarray_tuchar sh 6144 (Zlength b)) by (rewrite ?Zlength_map in *; lia).
  rewrite sublist0_app1 by (rewrite Zlength_map; lia).
  rewrite sublist_same by (rewrite ?Zlength_map; lia).
  cancel.
Qed.

Lemma VI_sr_fields sh (v: reptype t_wseries) p :
  data_at sh t_wseries v p |--
  field_at sh t_wseries (DOT _bytes) (fst v) p * field_at sh t_wseries (DOT _n) (fst (snd v)) p *
  field_at sh t_wseries (DOT _content_n) (fst (snd (snd (snd v)))) p *
  data_at sh (tarray t_winfo 4) (fst (snd (snd (snd (snd v))))) (field_address t_wseries (DOT _f) p) *
  field_at sh t_wseries (DOT _nframes) (snd (snd (snd (snd (snd v))))) p * TT.
Proof.
  unfold_data_at (data_at sh t_wseries v p).
  rewrite (field_at_data_at sh t_wseries (DOT _f)). cancel.
Qed.

Lemma VI_sr_bytes sh b rest p :
  Zlength b <= 524288 ->
  field_at sh t_wseries (DOT _bytes) (zbytes b ++ rest) p |--
  data_at sh (tarray tuchar (Zlength b)) (zbytes b) (field_address t_wseries (DOT _bytes) p) * TT.
Proof.
  intros Hb. pose proof (Zlength_nonneg b). rewrite field_at_data_at.
  change (nested_field_type t_wseries (DOT _bytes)) with (tarray tuchar 524288).
  assert_PROP (Zlength (zbytes b ++ rest) = 524288) as Hl.
  { entailer!. }
  rewrite (split2_data_at_Tarray_tuchar sh 524288 (Zlength b)) by (rewrite ?Zlength_map in *; lia).
  rewrite sublist0_app1 by (rewrite Zlength_map; lia).
  rewrite sublist_same by (rewrite ?Zlength_map; lia).
  cancel.
Qed.

(* the k-th frame record of sr.f *)
#[export] Instance VI_winfo_inh : Inhabitant winfo := winfo0.

Definition VI_frecs (fs: list winfo) : list (reptype t_winfo) :=
  map winfo_val fs ++ Zrepeat (winfo_val winfo0) (4 - Zlength fs).

Lemma VI_frecs_len fs : Zlength fs <= 4 -> Zlength (VI_frecs fs) = 4.
Proof.
  intros H. unfold VI_frecs. rewrite Zlength_app, Zlength_map, Zlength_Zrepeat; pose proof (Zlength_nonneg fs); lia.
Qed.

Lemma VI_frecs_nth fs k : 0 <= k < Zlength fs ->
  Znth k (VI_frecs fs) = winfo_val (Znth k fs).
Proof.
  intros H. unfold VI_frecs. rewrite app_Znth1 by (rewrite Zlength_map; lia).
  rewrite Znth_map by lia. reflexivity.
Qed.

(* generic in the element type: no reptype computation at t_winfo *)
Lemma VI_elem_gen {cs: compspecs} sh t n (L: list (reptype t)) q k :
  naturally_aligned t -> Zlength L = n -> 0 <= k < n -> field_compatible (tarray t n) [] q ->
  data_at sh (tarray t n) L q =
  (data_at sh (tarray t k) (sublist 0 k L) q *
   data_at sh t (Znth k L) (offset_val (sizeof t * k)%Z q) *
   data_at sh (tarray t (n - (k + 1))) (sublist (k + 1) n L) (offset_val (sizeof t * (k + 1))%Z q))%logic.
Proof.
  intros Hn HL Hk Hc.
  rewrite (split3_data_at_Tarray sh t n k (k + 1) L L (sublist 0 k L) (sublist k (k + 1) L)
    (sublist (k + 1) n L)); try lia; try reflexivity; auto.
  2: rewrite sublist_same by lia; reflexivity.
  change (Tarray t n noattr) with (tarray t n).
  change (Tarray t k noattr) with (tarray t k).
  change (Tarray t (k + 1 - k) noattr) with (tarray t (k + 1 - k)).
  change (Tarray t (n - (k + 1)) noattr) with (tarray t (n - (k + 1))).
  rewrite !arr_field_address0 by (auto; lia).
  replace (k + 1 - k) with 1 by lia.
  rewrite (data_at_singleton_array_eq sh t (Znth k L)); [reflexivity |].
  apply sublist_one; lia.
Qed.

Lemma VI_winfo_aligned : naturally_aligned t_winfo.
Proof. unfold naturally_aligned. simpl. auto. Qed.

(* src from a frame's start *)
Lemma VI_src_split sh b s q :
  0 <= s <= Zlength b -> field_compatible (tarray tuchar (Zlength b)) [] q ->
  data_at sh (tarray tuchar (Zlength b)) (zbytes b) q =
  (data_at sh (tarray tuchar s) (zbytes (firstn (Z.to_nat s) b)) q *
   data_at sh (tarray tuchar (Zlength (skipn (Z.to_nat s) b))) (zbytes (skipn (Z.to_nat s) b)) (offset_val s q))%logic.
Proof.
  intros Hs Hc.
  rewrite (split2_data_at_Tarray_tuchar sh (Zlength b) s) by (rewrite ?Zlength_map; lia).
  change (Tarray tuchar (Zlength b) noattr) with (tarray tuchar (Zlength b)).
  rewrite arr_field_address0 by (auto; lia).
  change (sizeof tuchar) with 1. rewrite Z.mul_1_l.
  assert (Hl2: Zlength (skipn (Z.to_nat s) b) = Zlength b - s).
  { rewrite !Zlength_correct, skipn_length. rewrite Zlength_correct in Hs. lia. }
  rewrite Hl2.
  rewrite sublist_map, sublist_firstn.
  replace (Zlength (zbytes b)) with (Zlength b) by (rewrite Zlength_map; reflexivity).
  rewrite <- (Zlength_map _ _ (fun x => Vint (Int.repr x)) b) at 2.
  rewrite sublist_skip by lia. rewrite map_skipn. reflexivity.
Qed.

(* dst: the capacity, and the byte malloc(1) adds for cap = 0 *)
Lemma VI_dst_split sh cap q :
  0 <= cap -> field_compatible (tarray tuchar (Z.max 1 cap)) [] q ->
  data_at_ sh (tarray tuchar (Z.max 1 cap)) q =
  (data_at_ sh (tarray tuchar cap) q * data_at_ sh (tarray tuchar (Z.max 1 cap - cap)) (offset_val cap q))%logic.
Proof.
  intros Hc Hf. rewrite !data_at__eq.
  change (default_val (tarray tuchar (Z.max 1 cap))) with (Zrepeat Vundef (Z.max 1 cap)).
  change (default_val (tarray tuchar cap)) with (Zrepeat Vundef cap).
  change (default_val (tarray tuchar (Z.max 1 cap - cap))) with (Zrepeat Vundef (Z.max 1 cap - cap)).
  rewrite (split2_data_at_Tarray_tuchar sh (Z.max 1 cap) cap) by (rewrite ?Zlength_Zrepeat; lia).
  change (Tarray tuchar (Z.max 1 cap) noattr) with (tarray tuchar (Z.max 1 cap)).
  rewrite arr_field_address0 by (auto; lia).
  change (sizeof tuchar) with 1. rewrite Z.mul_1_l.
  rewrite !sublist_Zrepeat by lia.
  f_equal; f_equal; f_equal; lia.
Qed.
