(* X2D: the body of HUF_decodeLastSymbolX2 (spec in HufX2DSpecs.v). *)
Require Export Zstd.proof.dec.B.huf.HufX2DSpecs.
Require Import Zstd.proof.zstd.PickLemmas.
Require Import Zstd.proof.dec.B.BMemcpyOk.
Require Zstd.proof.dec.B.huf.HufX2DSym.
Local Open Scope logic.

(* helpers copied from HufX2DSym.v *)
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


(* the 2 bytes of a sequence, one by one *)
Lemma bytes2_split (sh: share) (s1 b2: Z) (q: val) :
  field_compatible (tarray tuchar 2) [] q ->
  data_at sh (tarray tuchar 2) (zbytes [s1; b2]) q =
  data_at sh (tarray tuchar 1) (zbytes [s1]) q * data_at sh (tarray tuchar 1) (zbytes [b2]) (offset_val 1 q).
Proof.
  intros FC.
  rewrite (split2_data_at_Tarray_tuchar sh 2 1 (zbytes [s1; b2])) by (simpl; auto; lia).
  rewrite field_address0_offset by auto with field_compatible. reflexivity.
Qed.

Lemma bytes2_join (sh: share) (s1 b2: Z) (q: val) :
  field_compatible (tarray tuchar 2) [] q ->
  data_at sh (tarray tuchar 1) (zbytes [s1]) q * data_at sh (tarray tuchar 1) (zbytes [b2]) (offset_val 1 q) |--
  data_at sh (tarray tuchar 2) (zbytes [s1; b2]) q.
Proof. intros. rewrite bytes2_split by auto. apply derives_refl. Qed.

Lemma body_HUF_decodeLastSymbolX2 :
  semax_body Vprog G_sym2 f_HUF_decodeLastSymbolX2 HUF_decodeLastSymbolX2_spec.
Proof.
  start_function.
  destruct H as (Hok & HL & Hlen & Hcells).
  pose proof Hok as (Hlog1 & _ & _).
  unfold HUF_TABLELOG_MAX in *.
  change (BIT_DStream_rep sh gv s start pos lo p) with (BIT_DStream_rep_g false sh gv s start pos lo p).
  forward_call (sh, p, gv, s, start, pos, lo, L, false).
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
    - apply HufX2DSym.x2_cell_model; [exact Hok | lia | lia | rewrite <- H3; exact Hc | rep_lia | rep_lia | rep_lia]. }
  clear H5 H3.
  assert_PROP (field_compatible (tarray t_deltx2 (2 ^ L)) [] dt) as FCt by entailer!.
  assert_PROP (field_compatible (tarray tuchar (Zlength oc)) [] ob) as FCo by entailer!.
  rewrite (x2_tab_split sht (2 ^ L) v c2 dt) by (auto; lia). rewrite Hc.
  assert_PROP (field_compatible t_deltx2 [] (offset_val (4 * v) dt)) as FCc by entailer!.
  rewrite (x2_cell_bytes sht (fst (hsym ht L v)) b2) by auto.
  assert_PROP (field_compatible (tarray tuchar 2) [] (offset_val (4 * v) dt)) as FC2
    by (entailer!; autorewrite with sublist in *; assumption).
  rewrite (bytes2_split sht (fst (hsym ht L v)) b2) by auto.
  rewrite (out_split3 sho (Zlength oc) a 1 oc ob) by (auto; lia).
  sep_apply (data_at_data_at_ sho (tarray tuchar 1) (sublist a (a + 1) oc) (offset_val a ob)).
  forward_call (sht, sho, offset_val (4 * v) dt, offset_val a ob,
                existT (fun t => reptype t) (tarray tuchar 1) (zbytes [fst (hsym ht L v)])).
  { memcpy_side_B. }
  simpl projT1; simpl projT2.
  sep_apply (bytes2_join sht (fst (hsym ht L v)) b2 (offset_val (4 * v) dt) FC2).
  sep_apply (x2_cell_join sht (fst (hsym ht L v)) b2 (Vint (Int.repr nb)) (Vint (Int.repr k))
              (offset_val (4 * v) dt) Hs1 Hb2 FCc).
  rewrite <- Hc.
  sep_apply (x2_tab_join sht (2 ^ L) v c2 dt ltac:(lia) Hlen FCt).
  forward.
  { entailer!. change (@Znth (val * (val * val)) (Vundef, (Vundef, Vundef)) v c2) with (Znth v c2).
    rewrite Hc. simpl. destruct Hk as [-> | ->]; rewrite Int.unsigned_repr by rep_lia; rep_lia. }
  change (@Znth (val * (val * val)) (Vundef, (Vundef, Vundef)) v c2) with (Znth v c2).
  rewrite Hc. cbv iota beta.
  set (oc' := sublist 0 a oc ++ zbytes [fst (hsym ht L v)] ++ sublist (a + 1) (Zlength oc) oc).
  assert (E0: Zlength oc' = Zlength oc) by (unfold oc'; list_solve).
  assert (E1: sublist 0 a oc' = sublist 0 a oc) by (unfold oc'; list_solve).
  assert (E2: sublist a (a + 1) oc' = zbytes [fst (hsym ht L v)]) by (unfold oc'; list_solve).
  assert (E3: sublist (a + 1) (Zlength oc) oc' = sublist (a + 1) (Zlength oc) oc) by (unfold oc'; list_solve).
  assert (J: data_at sho (tarray tuchar a) (sublist 0 a oc) ob *
             data_at sho (tarray tuchar 1) (zbytes [fst (hsym ht L v)]) (offset_val a ob) *
             data_at sho (tarray tuchar (Zlength oc - (a + 1))) (sublist (a + 1) (Zlength oc) oc) (offset_val (a + 1) ob)
             |-- data_at sho (tarray tuchar (Zlength oc)) oc' ob).
  { rewrite (out_split3 sho (Zlength oc) a 1 oc' ob H0 ltac:(lia) H1 E0 FCo).
    rewrite E1, E2, E3. apply derives_refl. }
  sep_apply J. clear J.
  unfold BIT_DStream_rep_g.
  forward_if (PROP () LOCAL ()
    SEP (data_at sht (tarray t_deltx2 (2 ^ L)) c2 dt; data_at sho (tarray tuchar (Zlength oc)) oc' ob;
         BIT_DStream_rep sh gv s start (x2_last_pos pos lo k nb) lo p)).
  - (* one symbol *)
    forward.
    { entailer!. change (@Znth (val * (val * val)) (Vundef, (Vundef, Vundef)) v c2) with (Znth v c2).
      rewrite Hc. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    change (@Znth (val * (val * val)) (Vundef, (Vundef, Vundef)) v c2) with (Znth v c2).
    rewrite Hc. cbv iota beta.
    assert (k = 1) by (destruct Hk; subst; auto; discriminate). subst k.
    change (BIT_DStream_rep sh gv s start pos lo p) with (BIT_DStream_rep_g false sh gv s start pos lo p).
    forward_call (sh, p, gv, s, start, pos, lo, nb, false).
    entailer!. unfold x2_last_pos; simpl. apply derives_refl.
  - (* two symbols *)
    assert (k = 2) by lia. subst k.
    forward.
    forward_if (PROP () LOCAL ()
      SEP (data_at sht (tarray t_deltx2 (2 ^ L)) c2 dt; data_at sho (tarray tuchar (Zlength oc)) oc' ob;
           BIT_DStream_rep sh gv s start (x2_last_pos pos lo 2 nb) lo p)).
    + pose proof H5 as (Hb & Hs & Hlo & Hl8 & Hlb & Hpl & Hpm).
      change (Int64.unsigned (Int64.mul (Int64.repr 8) (Int64.repr 8))) with 64 in H7.
      rewrite Int.unsigned_repr in H7 by lia. rewrite Int64.unsigned_repr in H7 by rep_lia.
      assert (Hptr: ptr = offset_val (lo / 8) start) by (destruct H6 as [? | [? ?]]; [auto | lia]).
      subst ptr.
      forward.
      { entailer!. change (@Znth (val * (val * val)) (Vundef, (Vundef, Vundef)) v c2) with (Znth v c2).
        rewrite Hc. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
      change (@Znth (val * (val * val)) (Vundef, (Vundef, Vundef)) v c2) with (Znth v c2).
      rewrite Hc. cbv iota beta.
      (* bitsConsumed < 64: the window pointer is the stream's, skip on rep_np *)
      assert (Fn: data_at sh (Tstruct ___gp_BIT_DStream_t noattr)
           (Vlong (Int64.repr (bit_C s lo)), (Vint (Int.repr (lo + 64 - pos)), (offset_val (lo / 8) start, (start, lim)))) p
         |-- BIT_DStream_rep_g true sh gv s start pos lo p)
        by (unfold BIT_DStream_rep_g, BIT_DStream_rep_np; Exists lim; entailer!).
      sep_apply Fn. clear Fn.
      forward_call (sh, p, gv, s, start, pos, lo, nb, true).
      unfold BIT_DStream_rep_g, BIT_DStream_rep_np. Intros lim'.
      forward.
      pose proof H8 as (_ & _ & _ & _ & _ & Hpl' & Hpm').
      forward_if.
      * change (Int64.unsigned (Int64.mul (Int64.repr 8) (Int64.repr 8))) with 64 in *.
        rewrite Int.unsigned_repr in * by lia. rewrite Int64.unsigned_repr in * by rep_lia.
        forward.
        assert (E: x2_last_pos pos lo 2 nb = lo) by (unfold x2_last_pos; simpl; destruct (pos <=? lo) eqn:?; lia).
        rewrite E. unfold BIT_DStream_rep. Exists (offset_val (lo / 8) start) lim'. entailer!.
        { unfold bit_inv. repeat split; auto; rep_lia. }
        replace (lo + 64 - lo) with 64 by lia. apply derives_refl.
      * change (Int64.unsigned (Int64.mul (Int64.repr 8) (Int64.repr 8))) with 64 in *.
        rewrite Int.unsigned_repr in * by lia. rewrite Int64.unsigned_repr in * by rep_lia.
        forward.
        assert (E: x2_last_pos pos lo 2 nb = pos - nb) by (unfold x2_last_pos; simpl; destruct (pos <=? lo) eqn:?; lia).
        rewrite E. unfold BIT_DStream_rep. Exists (offset_val (lo / 8) start) lim'. entailer!.
    + pose proof H5 as (_ & _ & _ & _ & _ & Hpl & Hpm).
      change (Int64.unsigned (Int64.mul (Int64.repr 8) (Int64.repr 8))) with 64 in H7.
      rewrite Int.unsigned_repr in H7 by lia. rewrite Int64.unsigned_repr in H7 by rep_lia.
      assert (E: x2_last_pos pos lo 2 nb = pos) by (unfold x2_last_pos; simpl; destruct (pos <=? lo) eqn:?; lia).
      forward. rewrite E. unfold BIT_DStream_rep. Exists ptr lim. entailer!.
  - forward. Exists v k b2 nb. entailer!.
    exact (proj2 Hx).
Qed.
