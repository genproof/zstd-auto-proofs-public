(* X2D: the body of HUF_decodeSymbolX2 (spec in HufX2DSpecs.v). *)
Require Export Zstd.proof.dec.B.huf.HufX2DSpecs.
Require Import Zstd.proof.zstd.PickLemmas.
Require Import Zstd.proof.dec.B.BMemcpyOk.
Local Open Scope logic.

(* the cell of v: its sequence (first symbol, second byte b2), nbBits nb, length k, one x2_step *)
Lemma x2_cell_step (ht: huf_table) (L v: Z) (c: val * (val * val)) :
  huf_ok ht -> ht_log ht <= L -> 0 <= v < 2 ^ L -> x2_cell_ok ht L v c ->
  exists k b2 nb, c = (Vint (Int.repr (fst (hsym ht L v) + 256 * b2)), (Vint (Int.repr nb), Vint (Int.repr k))) /\
                  x2_step ht L v k b2 nb /\ (k = 1 \/ k = 2).
Proof.
  intros Hok HL Hv Hc. unfold x2_cell_ok, x2_step in *.
  pose proof (hsym_range ht L v Hok HL Hv) as [Hs1 Hn1].
  destruct (hsym ht L v) as [s1 n1] eqn:Hh. simpl fst in *; simpl snd in *.
  destruct Hc as [(hi & Hhi & ->) | Hc2].
  - exists 1, hi, n1. split; [reflexivity|]. split; [|lia]. split; [lia|]. split; [lia|]. left; lia.
  - assert (Hw: 0 <= (v * 2 ^ n1) mod 2 ^ L < 2 ^ L) by (apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia).
    pose proof (hsym_range ht L _ Hok HL Hw) as [Hs2 Hn2].
    destruct (hsym ht L ((v * 2 ^ n1) mod 2 ^ L)) as [s2 n2] eqn:Hh2. simpl fst in *; simpl snd in *.
    destruct Hc2 as (Hle & ->).
    exists 2, s2, (n1 + n2). split; [reflexivity|]. split; [|lia]. split; [lia|]. split; [lia|].
    right. auto.
Qed.

(* the model's cell of v (ExHuf.xh_cells_x2) has the field values the C reads from its x2v image *)
Lemma x2_cell_model (ht: huf_table) (L v sq nb k: Z) :
  huf_ok ht -> ht_log ht <= L -> 0 <= v < 2 ^ L ->
  Znth v (map x2v (xh_cells_x2 ht L)) = (Vint (Int.repr sq), (Vint (Int.repr nb), Vint (Int.repr k))) ->
  0 <= sq <= Int.max_unsigned -> 0 <= nb <= Int.max_unsigned -> 0 <= k <= Int.max_unsigned ->
  nth (Z.to_nat v) (xh_cells_x2 ht L) (0, 0, 0) = (sq, nb, k).
Proof.
  intros Hok HL Hv Hc Hsq Hnb Hk.
  rewrite xh_cells_x2_Znth in Hc by exact Hv.
  assert (He: nth (Z.to_nat v) (xh_cells_x2 ht L) (0, 0, 0) = xh_x2_fields (x2_elt ht L v)).
  { unfold xh_cells_x2.
    assert (Hlen: (Z.to_nat v < length (seq 0 (Z.to_nat (2 ^ L))))%nat) by (rewrite length_seq; lia).
    set (f := fun n : nat => xh_x2_fields (x2_elt ht L (Z.of_nat n))).
    rewrite (nth_indep _ _ (f O)) by (rewrite length_map; exact Hlen).
    rewrite map_nth, seq_nth by (rewrite length_seq in Hlen; exact Hlen).
    unfold f. rewrite Nat.add_0_l, Z2Nat.id by lia. reflexivity. }
  assert (Hrange: 0 <= x2_elt ht L v < 2 ^ 32).
  { pose proof Hok as (Hlog & _ & _).
    unfold x2_elt.
    pose proof (hsym_range ht L v Hok HL Hv) as [Hs1 Hn1].
    destruct (hsym ht L v) as [s1 n1]. simpl fst in *; simpl snd in *.
    assert (Hw: 0 <= (v * 2 ^ n1) mod 2 ^ L < 2 ^ L) by (apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia).
    pose proof (hsym_range ht L _ Hok HL Hw) as [Hs2 Hn2].
    unfold x2_cellu.
    destruct (hsym ht L ((v * 2 ^ n1) mod 2 ^ L)) as [s2 n2]. simpl fst in *; simpl snd in *.
    unfold deltu, HUF_TABLELOG_MAX in *. destruct (n1 + n2 <=? L); simpl; lia. }
  rewrite He in Hc |- *. unfold xh_x2_fields in *. unfold x2v in Hc.
  set (e := x2_elt ht L v) in *.
  assert (B1: 0 <= e mod 65536 < 65536) by (apply Z.mod_pos_bound; lia).
  assert (B2: 0 <= (e / 65536) mod 256 < 256) by (apply Z.mod_pos_bound; lia).
  assert (B3: 0 <= e / 16777216 <= Int.max_unsigned).
  { split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; rep_lia. }
  set (gi := fun w: val => match w with Vint i => i | _ => Int.zero end).
  assert (E1: Int.repr (e mod 65536) = Int.repr sq) by exact (f_equal (fun x => gi (fst x)) Hc).
  assert (E2: Int.repr ((e / 65536) mod 256) = Int.repr nb) by exact (f_equal (fun x => gi (fst (snd x))) Hc).
  assert (E3: Int.repr (e / 16777216) = Int.repr k) by exact (f_equal (fun x => gi (snd (snd x))) Hc).
  apply repr_inj_unsigned in E1; [|rep_lia|rep_lia].
  apply repr_inj_unsigned in E2; [|rep_lia|rep_lia].
  apply repr_inj_unsigned in E3; [|rep_lia|rep_lia].
  rewrite E1, E2, E3. reflexivity.
Qed.

(* the cell v of an X2 table, apart *)
Lemma x2_tab_split (sh: share) (n v: Z) (c2: list (val * (val * val))) (dt: val) :
  0 <= v < n -> Zlength c2 = n -> field_compatible (tarray t_deltx2 n) [] dt ->
  data_at sh (tarray t_deltx2 n) c2 dt =
  data_at sh (tarray t_deltx2 v) (sublist 0 v c2) dt *
  data_at sh t_deltx2 (Znth v c2) (offset_val (4 * v) dt) *
  data_at sh (tarray t_deltx2 (n - (v + 1))) (sublist (v + 1) n c2) (offset_val (4 * (v + 1)) dt).
Proof.
  intros Hv Hn FC.
  rewrite (@split3_data_at_Tarray CompSpecs sh t_deltx2 n v (v + 1) c2 c2 (sublist 0 v c2) (sublist v (v + 1) c2) (sublist (v + 1) n c2)).
  2: (unfold naturally_aligned; simpl; auto).
  2: lia.
  2: (split; [lia|]; apply Z.eq_le_incl; exact (eq_sym Hn)).
  2: (symmetry; apply sublist_same; [reflexivity | exact (eq_sym Hn)]).
  2-4: reflexivity.
  change (Tarray t_deltx2 n noattr) with (tarray t_deltx2 n).
  rewrite !arr_field_address0 by (auto; lia).
  replace (v + 1 - v) with 1 by lia.
  rewrite (sublist_len_1 v c2) by lia.
  rewrite (@data_at_singleton_array_eq CompSpecs sh t_deltx2 (Znth v c2)) by reflexivity.
  simpl sizeof. reflexivity.
Qed.

(* the 2 bytes of a sequence s1 + 256 * b2 *)
Lemma le_bytes2_seq (s1 b2: Z) : 0 <= s1 < 256 -> le_bytes 2 (s1 + 256 * b2) = [s1; b2 mod 256].
Proof.
  intros Hs. cbn [le_bytes]. rewrite (Z.mul_comm 256 b2), Z.mod_add, Z.div_add by lia.
  rewrite Z.mod_small, Z.div_small by lia. reflexivity.
Qed.

(* a cell: its sequence field as 2 bytes, and its two other fields *)
Lemma x2_cell_bytes (sh: share) (s1 b2: Z) (nb k: val) (q: val) :
  0 <= s1 < 256 -> 0 <= b2 < 256 -> field_compatible t_deltx2 [] q ->
  data_at sh t_deltx2 (Vint (Int.repr (s1 + 256 * b2)), (nb, k)) q =
  data_at sh (tarray tuchar 2) (zbytes [s1; b2]) q *
  field_at sh t_deltx2 (DOT _nbBits) nb q * field_at sh t_deltx2 (DOT _length) k q.
Proof.
  intros Hs Hb FC.
  unfold_data_at (data_at sh t_deltx2 _ q).
  rewrite (field_at_data_at sh t_deltx2 (DOT _sequence)).
  assert (FCs: field_compatible tushort [] (field_address t_deltx2 (DOT _sequence) q)).
  { change tushort with (nested_field_type t_deltx2 (DOT _sequence)).
    apply (field_compatible_app [] t_deltx2 (DOT _sequence) q). simpl app. auto with field_compatible. }
  rewrite field_address_offset in FCs |- * by auto with field_compatible.
  simpl nested_field_type. simpl nested_field_offset in *.
  rewrite isptr_offset_val_zero in FCs |- * by auto with field_compatible.
  rewrite tushort_bytes2 by (auto; rep_lia).
  rewrite le_bytes2_seq by lia. rewrite (Z.mod_small b2) by lia.
  rewrite !sepcon_assoc. reflexivity.
Qed.

Lemma x2_cell_join (sh: share) (s1 b2: Z) (nb k: val) (q: val) :
  0 <= s1 < 256 -> 0 <= b2 < 256 -> field_compatible t_deltx2 [] q ->
  data_at sh (tarray tuchar 2) (zbytes [s1; b2]) q *
  field_at sh t_deltx2 (DOT _nbBits) nb q * field_at sh t_deltx2 (DOT _length) k q |--
  data_at sh t_deltx2 (Vint (Int.repr (s1 + 256 * b2)), (nb, k)) q.
Proof. intros. rewrite x2_cell_bytes by auto. apply derives_refl. Qed.

Lemma x2_tab_join (sh: share) (n v: Z) (c2: list (val * (val * val))) (dt: val) :
  0 <= v < n -> Zlength c2 = n -> field_compatible (tarray t_deltx2 n) [] dt ->
  data_at sh (tarray t_deltx2 v) (sublist 0 v c2) dt *
  data_at sh t_deltx2 (Znth v c2) (offset_val (4 * v) dt) *
  data_at sh (tarray t_deltx2 (n - (v + 1))) (sublist (v + 1) n c2) (offset_val (4 * (v + 1)) dt) |--
  data_at sh (tarray t_deltx2 n) c2 dt.
Proof. intros. rewrite (x2_tab_split sh n v c2 dt) by auto. apply derives_refl. Qed.

(* the 2 bytes at a of an output array, apart (zstd/body_util_mem.v: arr_split3) *)
Lemma out_split3 (sh: share) (n i k: Z) (l: list val) (p: val) :
  0 <= i -> 0 <= k -> i + k <= n -> Zlength l = n ->
  field_compatible (tarray tuchar n) [] p ->
  data_at sh (tarray tuchar n) l p =
  data_at sh (tarray tuchar i) (sublist 0 i l) p *
  data_at sh (tarray tuchar k) (sublist i (i + k) l) (offset_val i p) *
  data_at sh (tarray tuchar (n - (i + k))) (sublist (i + k) n l) (offset_val (i + k) p).
Proof.
  intros. rewrite (split3_data_at_Tarray_tuchar sh n i (i + k)) by lia.
  change (Tarray tuchar n noattr) with (tarray tuchar n). rewrite !arr_field_address0 by (auto; lia).
  replace (i + k - i) with k by lia. simpl sizeof. rewrite !Z.mul_1_l. reflexivity.
Qed.

Lemma body_HUF_decodeSymbolX2 :
  semax_body Vprog G_sym2 f_HUF_decodeSymbolX2 HUF_decodeSymbolX2_spec.
Proof.
  start_function.
  destruct H as (Hok & HL & Hlen & Hcells).
  pose proof Hok as (Hlog1 & _ & _).
  unfold HUF_TABLELOG_MAX in *.
  forward_call (sh, p, gv, s, start, pos, lo, L, np).
  Intros v.
  specialize (Hcells v ltac:(lia)).
  destruct (hsym_range ht L v Hok ltac:(lia) ltac:(lia)) as [Hs1 Hn1].
  destruct (x2_cell_step ht L v (Znth v c2) Hok ltac:(lia) H Hcells) as (k & b2 & nb & Hc & Hst & Hk).
  pose proof Hst as (Hb2 & Hnb & _).
  (* the exact clause: the peek is ExHuf's, and the cell read is the model's cell *)
  assert (Hx: (v = xb_look_fast (xb_of s pos lo) L /\ 
               nth (Z.to_nat v) (xh_cells_x2 ht L) (0, 0, 0) = ((fst (hsym ht L v) + 256 * b2)%Z, nb, k))%type).
  { split.
    - rewrite (xb_look_rel s pos lo (xb_of s pos lo) L (xb_rel_of s pos lo) ltac:(lia)). exact H5.
    - apply x2_cell_model; [exact Hok | lia | lia | rewrite <- H3; exact Hc | rep_lia | rep_lia | rep_lia]. }
  clear H5 H3.
  assert_PROP (field_compatible (tarray t_deltx2 (2 ^ L)) [] dt) as FCt by entailer!.
  assert_PROP (field_compatible (tarray tuchar (Zlength oc)) [] ob) as FCo by entailer!.
  rewrite (x2_tab_split sht (2 ^ L) v c2 dt) by (auto; lia). rewrite Hc.
  assert_PROP (field_compatible t_deltx2 [] (offset_val (4 * v) dt)) as FCc by entailer!.
  rewrite (x2_cell_bytes sht (fst (hsym ht L v)) b2) by auto.
  rewrite (out_split3 sho (Zlength oc) a 2 oc ob) by (auto; lia).
  sep_apply (data_at_data_at_ sho (tarray tuchar 2) (sublist a (a + 2) oc) (offset_val a ob)).
  forward_call (sht, sho, offset_val (4 * v) dt, offset_val a ob,
                existT (fun t => reptype t) (tarray tuchar 2) (zbytes [fst (hsym ht L v); b2])).
  { memcpy_side_B. }
  simpl projT1; simpl projT2.
  sep_apply (x2_cell_join sht (fst (hsym ht L v)) b2 (Vint (Int.repr nb)) (Vint (Int.repr k))
              (offset_val (4 * v) dt) Hs1 Hb2 FCc).
  rewrite <- Hc.
  sep_apply (x2_tab_join sht (2 ^ L) v c2 dt ltac:(lia) Hlen FCt).
  forward.
  { entailer!. change (@Znth (val * (val * val)) (Vundef, (Vundef, Vundef)) v c2) with (Znth v c2).
    rewrite Hc. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
  change (@Znth (val * (val * val)) (Vundef, (Vundef, Vundef)) v c2) with (Znth v c2).
  rewrite Hc. cbv iota beta.
  forward_call (sh, p, gv, s, start, pos, lo, nb, np).
  forward.
  { entailer!. change (@Znth (val * (val * val)) (Vundef, (Vundef, Vundef)) v c2) with (Znth v c2).
    rewrite Hc. simpl. destruct Hk as [-> | ->]; rewrite Int.unsigned_repr by rep_lia; rep_lia. }
  change (@Znth (val * (val * val)) (Vundef, (Vundef, Vundef)) v c2) with (Znth v c2).
  rewrite Hc. cbv iota beta.
  forward.
  Exists v k b2 nb. entailer!.
  { exact (proj2 Hx). }
  set (w1 := Vint (Int.repr (fst (hsym ht L v)))). set (w2 := Vint (Int.repr b2)).
  set (oc' := sublist 0 a oc ++ w1 :: w2 :: sublist (a + 2) (Zlength oc) oc).
  assert (E0: Zlength oc' = Zlength oc) by (unfold oc'; list_solve).
  assert (E1: sublist 0 a oc' = sublist 0 a oc) by (unfold oc'; list_solve).
  assert (E2: sublist a (a + 2) oc' = [w1; w2]) by (unfold oc'; list_solve).
  assert (E3: sublist (a + 2) (Zlength oc) oc' = sublist (a + 2) (Zlength oc) oc) by (unfold oc'; list_solve).
  rewrite (out_split3 sho (Zlength oc) a 2 oc' ob H0 ltac:(lia) H1 E0 FCo).
  rewrite E1, E2, E3. cancel.
Qed.
