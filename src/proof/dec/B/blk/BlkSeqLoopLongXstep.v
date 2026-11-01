(* LOOP / long loop: the executor's steps (pure), shared by
   MAIN and FIN: from XP and the executors' postconditions to XQ (next state) or XERR (an error return). *)
Require Import Zstd.proof.dec.B.blk.BlkSeqLoopLongMainDefs.
Local Open Scope logic.

(* ===================== list helpers ===================== *)

Lemma xs_Forall_sub (l: list val) (a b: Z) :
  0 <= a <= b -> b <= Zlength l ->
  (Forall is_byte_val (sublist a b l) <-> forall q, a <= q < b -> is_byte_val (Znth q l)).
Proof.
  intros Hab Hb. rewrite VST.zlist.list_solver.Forall_Znth. rewrite Zlength_sublist by lia. split.
  - intros H q Hq. specialize (H (q - a) ltac:(lia)). rewrite Znth_sublist in H by lia.
    replace (q - a + a) with q in H by lia. exact H.
  - intros H q Hq. rewrite Znth_sublist by lia. apply H; lia.
Qed.

Lemma xs_zbytes_def (l0: list Z) : bytes_ok l0 -> Forall is_byte_val (zbytes l0).
Proof.
  induction 1; simpl; constructor; auto. exists x. unfold is_byte in H. split; [lia|reflexivity].
Qed.

Lemma xs_sublist_ext (l1 l2: list val) (a b: Z) :
  0 <= a <= b -> b <= Zlength l1 -> Zlength l2 = Zlength l1 ->
  (forall q, a <= q < b -> Znth q l2 = Znth q l1) -> sublist a b l2 = sublist a b l1.
Proof.
  intros Hab Hb Hl H. apply Znth_eq_ext; [rewrite !Zlength_sublist; lia|].
  intros q Hq. rewrite Zlength_sublist in Hq by lia. rewrite !Znth_sublist by lia. apply H; lia.
Qed.

(* the forward copy from ahead (di < si) reads only bytes not yet written *)
Lemma xs_listcopy_ahead (c: list val) (si di: Z) (n: nat) :
  0 <= di < si -> si + Z.of_nat n <= Zlength c ->
  forall t, 0 <= t < Z.of_nat n -> Znth (di + t) (listcopy c si di n) = Znth (si + t) c.
Proof.
  revert c si di. induction n as [|m IH]; intros c si di Hd Hn t Ht; [simpl in Ht; lia|].
  rewrite Nat2Z.inj_succ in *. simpl.
  assert (Hu: Zlength (upd_Znth di c (Znth si c)) = Zlength c) by (apply Zlength_upd_Znth).
  destruct (Z.eq_dec t 0) as [->|Ht0].
  - rewrite listcopy_outside by (rewrite ?Hu; lia). rewrite Z.add_0_r, upd_Znth_same by lia.
    rewrite Z.add_0_r. reflexivity.
  - replace (di + t) with ((di + 1) + (t - 1)) by lia.
    rewrite IH by (rewrite ?Hu; lia). rewrite upd_Znth_diff by lia. f_equal; lia.
Qed.

Lemma xs_listcopy_ahead_sub (c: list val) (si di n: Z) :
  0 <= di < si -> 0 <= n -> si + n <= Zlength c ->
  sublist di (di + n) (listcopy c si di (Z.to_nat n)) = sublist si (si + n) c.
Proof.
  intros Hd Hn Hs. assert (Hl: Zlength (listcopy c si di (Z.to_nat n)) = Zlength c)
    by (apply listcopy_Zlength; lia).
  apply Znth_eq_ext; [rewrite !Zlength_sublist; lia|].
  intros q Hq. rewrite Zlength_sublist in Hq by lia. rewrite !Znth_sublist by lia.
  replace (q + di) with (di + q) by lia. rewrite xs_listcopy_ahead by lia. f_equal; lia.
Qed.

(* ===================== model helpers ===================== *)

Lemma xs_exec_len (wsize: Z) (rep: Z * Z * Z) (hist lits out: list Z) (seqs: list sequence)
    (out' lits': list Z) (rep': Z * Z * Z) :
  exec_seqs wsize rep hist lits out seqs = Some (out', lits', rep') ->
  Zlength out + Zlength lits <= Zlength out' + Zlength lits'.
Proof.
  revert rep lits out. induction seqs as [|sq rest IH]; intros rep lits out H.
  - simpl in H. inversion H; subst. lia.
  - simpl in H.
    destruct (sq_ll sq >? Zlength lits) eqn:Ell; [discriminate|].
    destruct (resolve_offset rep (sq_ll sq) (sq_ov sq)) as [[offset rep2]|] eqn:E2; [|discriminate].
    destruct (offset >? Zlength hist + Zlength (out ++ firstn (Z.to_nat (sq_ll sq)) lits)); [discriminate|].
    destruct (offset >? wsize + Zlength hist); [discriminate|].
    specialize (IH _ _ _ H).
    rewrite lz_copy_length, Zlength_app in IH. repeat rewrite Zlength_correct in IH. repeat rewrite Zlength_correct.
    pose proof (firstn_skipn (Z.to_nat (sq_ll sq)) lits) as Hfs.
    apply (f_equal (@length Z)) in Hfs. rewrite app_length in Hfs. lia.
Qed.

Lemma xs_sum_llml_app (l1 l2: list sequence) : sum_llml (l1 ++ l2) = sum_llml l1 + sum_llml l2.
Proof. induction l1 as [|sq l IH]; simpl; [reflexivity|]. rewrite IH. lia. Qed.

Lemma xs_sum_ll_app (l1 l2: list sequence) : sum_ll (l1 ++ l2) = sum_ll l1 + sum_ll l2.
Proof. induction l1 as [|sq l IH]; simpl; [reflexivity|]. rewrite IH. lia. Qed.

Lemma xs_rep_chain_app (r: Z * Z * Z) (l1 l2: list sequence) :
  rep_chain r (l1 ++ l2) = rep_chain (rep_chain r l1) l2.
Proof. revert r; induction l1 as [|sq l1 IH]; intros r; simpl; [reflexivity | apply IH]. Qed.

Lemma xs_sub_snoc (seqs: list sequence) (ie: Z) :
  0 <= ie < Zlength seqs -> sublist 0 (ie + 1) seqs = sublist 0 ie seqs ++ [Znth ie seqs].
Proof.
  intros H. rewrite (sublist_split 0 ie (ie + 1)) by lia. rewrite sublist_len_1 by lia. reflexivity.
Qed.

Lemma xs_sub_cons (seqs: list sequence) (ie nb: Z) :
  0 <= ie < nb -> nb <= Zlength seqs -> sublist ie nb seqs = Znth ie seqs :: sublist (ie + 1) nb seqs.
Proof.
  intros H Hn. rewrite (sublist_split ie (ie + 1) nb) by lia. rewrite sublist_len_1 by lia. reflexivity.
Qed.

Lemma xs_firstn_sub {A} {IA: Inhabitant A} (l: list A) (j n t: Z) :
  0 <= j -> 0 <= t -> j + t <= n -> n <= Zlength l ->
  firstn (Z.to_nat t) (sublist j n l) = sublist j (j + t) l.
Proof.
  intros. rewrite <- sublist_firstn. rewrite sublist_sublist by lia. f_equal; lia.
Qed.

Lemma xs_skipn_sub {A} {IA: Inhabitant A} (l: list A) (j n t: Z) :
  0 <= j -> 0 <= t -> j + t <= n -> n <= Zlength l ->
  skipn (Z.to_nat t) (sublist j n l) = sublist (j + t) n l.
Proof.
  intros. rewrite <- sublist_skip by lia. rewrite Zlength_sublist by lia.
  rewrite sublist_sublist by lia. f_equal; lia.
Qed.

(* ===================== the context ===================== *)

Ltac xs_fold := change (oa_d (a_o ?a)) with (a_d a) in *; change (oa_cap (a_o ?a)) with (a_cap a) in *;
  change (hc_ps (a_h ?a)) with (a_ps a) in *; change (hc_ext (a_h ?a)) with (a_x a) in *;
  change (Zlength (a_lits ?a)) with (a_n a) in *.

Lemma xs_basic (a: la) (x: lfx) :
  la_ok a -> la_pend a -> lfx_ok a x -> 0 < a_nb a ->
  Zlength (oa_c (a_o a)) = oa_N (a_o a) /\ oa_N (a_o a) <= 2 ^ 63 - 1 /\ 0 <= a_d a /\ 0 < a_cap a /\
  a_d a + a_cap a <= oa_N (a_o a) /\
  0 <= a_ps a <= a_d a /\ 0 <= ext_len (a_x a) <= 2 ^ 63 - 1 /\ ext_in_bounds (a_x a) (oa_N (a_o a)) /\
  bytes_ok (a_lits a) /\ 0 <= a_n a <= a_bsm a /\ a_bsm a <= ZSTD_BLOCKSIZE_MAX /\ rep_ok (a_rep a) /\
  a_d a <= a_E a <= a_d a + a_cap a /\ a_os a = Some (x_t x).
Proof.
  intros (Ho & Hi & Hla & Hbsm & Hn & Hnb & Hcap & Hso & Hrep & Hfe & Hc0 & Hlay) Hpend (Hos & _) Hnb0.
  destruct (Hcap ltac:(lia)) as [_ Hcap0]. specialize (Hlay Hcap0).
  destruct Ho as (_ & Hoc & HoN & Hod & Hocap & Hodc).
  destruct Hlay as (Hps & _ & _ & Hel & Hext).
  destruct Hla as (Hlb & Hln & Hl).
  xs_fold. unfold a_n.
  repeat split; try lia; auto.
  - unfold ext_in_bounds. destruct (a_x a); simpl in *; tauto || lia.
  - pose proof (Zlength_nonneg (a_lits a)). lia.
  - unfold a_E. revert Hl. unfold WILDCOPY_OVERLENGTH. destruct (a_l a); lia.
  - unfold a_E. revert Hl. unfold WILDCOPY_OVERLENGTH. destruct (a_l a); lia.
Qed.

(* ext_read_ok from ext_clean (or ext_far while the literals end within bsm) and the offset in the history *)
Lemma xs_ext_read (a: la) (k E' ll ml off: Z) :
  la_ok a -> 0 < a_cap a ->
  (ext_clean (a_d a) (a_cap a) (a_x a) \/
   (k + ll <= a_d a + a_bsm a /\ ext_far (a_d a) (a_cap a) (a_bsm a) (a_x a))) ->
  a_d a <= k -> E' <= a_d a + a_cap a -> 0 <= ll -> 0 <= ml ->
  off <= k + ll - a_ps a + ext_len (a_x a) ->
  ext_read_ok (a_x a) k E' ll ml off (a_ps a).
Proof.
  intros Hok Hcap Hcl Hk HE Hll Hml Hoff.
  unfold ext_read_ok. destruct (a_x a) as [|e1 elen|sh eb en ec e1 elen] eqn:Hx; auto.
  simpl in Hoff. unfold ext_clean, ext_far in Hcl. unfold WILDCOPY_OVERLENGTH in *.
  destruct (Z_le_gt_dec off (k + ll - a_ps a)) as [H|H]; [left; exact H|right].
  destruct Hcl as [[Hc|Hc]|[Hb Hc]]; [right; lia|left; lia|left; lia].
Qed.

(* the clean / far premise is monotone in K *)
Lemma xs_cl_mono (a: la) (K K': Z) :
  K <= K' ->
  (ext_clean (a_d a) (a_cap a) (a_x a) \/ (K' <= a_bsm a /\ ext_far (a_d a) (a_cap a) (a_bsm a) (a_x a))) ->
  (ext_clean (a_d a) (a_cap a) (a_x a) \/ (K <= a_bsm a /\ ext_far (a_d a) (a_cap a) (a_bsm a) (a_x a))).
Proof. intros H [H1|[H2 H3]]; [left; exact H1|right; split; [lia|exact H3]]. Qed.

Lemma xs_cl_k (a: la) (K' k ll: Z) :
  k + ll <= a_d a + K' ->
  (ext_clean (a_d a) (a_cap a) (a_x a) \/ (K' <= a_bsm a /\ ext_far (a_d a) (a_cap a) (a_bsm a) (a_x a))) ->
  (ext_clean (a_d a) (a_cap a) (a_x a) \/ (k + ll <= a_d a + a_bsm a /\ ext_far (a_d a) (a_cap a) (a_bsm a) (a_x a))).
Proof. intros H [H1|[H2 H3]]; [left; exact H1|right; split; [lia|exact H3]]. Qed.

(* the prefix [ps, d) is defined when the history is *)
Lemma xs_prefix_def (a: la) (cc: list val) :
  0 <= a_ps a <= a_d a -> 0 <= ext_len (a_x a) -> hist_def (oa_c (a_o a)) (a_d a) (a_ps a) (a_x a) ->
  Zlength cc = Zlength (oa_c (a_o a)) -> a_d a <= Zlength cc ->
  (forall q, 0 <= q < a_d a -> Znth q cc = Znth q (oa_c (a_o a))) ->
  Forall is_byte_val (sublist (a_ps a) (a_d a) cc).
Proof.
  intros Hps Hel Hhd Hl Hd Hu. rewrite xs_Forall_sub by lia. intros q Hq.
  rewrite Hu by lia. specialize (Hhd (a_d a - q) ltac:(lia)). unfold chist in Hhd.
  rewrite (proj2 (Z.leb_le _ _)) in Hhd by lia. replace (a_d a - (a_d a - q)) with q in Hhd by lia. exact Hhd.
Qed.

(* the extDict is defined when the history is and the array is unchanged outside [d, d + cap) *)
Lemma xs_ext_def_hi (a: la) (cc: list val) (hi: Z) :
  la_ok a -> 0 < a_cap a -> hist_def (oa_c (a_o a)) (a_d a) (a_ps a) (a_x a) ->
  match a_x a with ExtIn e1 elen => e1 <= a_d a \/ hi <= e1 - elen | _ => True end ->
  Zlength cc = Zlength (oa_c (a_o a)) ->
  unchanged_outside (oa_c (a_o a)) cc (a_d a) hi ->
  ext_def (a_x a) cc.
Proof.
  intros (Ho & Hi & Hla & Hbsm & Hn & Hnb & Hcap & Hso & Hrep & Hfe & Hc0 & Hlay) Hcap0 Hhd Hcl Hl Hu.
  specialize (Hlay Hcap0). destruct Hlay as (Hps & _ & _ & Hel & Hext).
  destruct Ho as (_ & Hoc & HoN & Hod & Hocap & Hodc). xs_fold.
  unfold ext_def. destruct (a_x a) as [|e1 elen|sh eb en ec e1 elen] eqn:Hx; auto.
  - destruct Hext as (_ & He1 & He2). simpl in Hel.
    rewrite xs_Forall_sub by lia. intros q Hq.
    rewrite Hu by lia.
    specialize (Hhd (a_d a - a_ps a + (e1 - q))). simpl in Hhd.
    specialize (Hhd ltac:(lia)). unfold chist in Hhd.
    rewrite (proj2 (Z.leb_gt _ _)) in Hhd by lia.
    replace (e1 - (a_d a - a_ps a + (e1 - q) - (a_d a - a_ps a))) with q in Hhd by lia. exact Hhd.
  - destruct Hext as (_ & _ & Hen & He1 & He2). simpl in Hel.
    rewrite xs_Forall_sub by lia. intros q Hq.
    specialize (Hhd (a_d a - a_ps a + (e1 - q))). simpl in Hhd.
    specialize (Hhd ltac:(lia)). unfold chist in Hhd.
    rewrite (proj2 (Z.leb_gt _ _)) in Hhd by lia.
    replace (e1 - (a_d a - a_ps a + (e1 - q) - (a_d a - a_ps a))) with q in Hhd by lia. exact Hhd.
Qed.

(* ... under the clean / far premise, the array unchanged outside [d, min(oend, d + Kb + 32)) *)
Lemma xs_ext_def (a: la) (cc: list val) (Kb: Z) :
  la_ok a -> 0 < a_cap a -> hist_def (oa_c (a_o a)) (a_d a) (a_ps a) (a_x a) ->
  (ext_clean (a_d a) (a_cap a) (a_x a) \/ (Kb <= a_bsm a /\ ext_far (a_d a) (a_cap a) (a_bsm a) (a_x a))) ->
  a_E a <= a_d a + a_cap a -> 0 <= Kb ->
  Zlength cc = Zlength (oa_c (a_o a)) ->
  unchanged_outside (oa_c (a_o a)) cc (a_d a) (Z.min (a_E a) (a_d a + Kb + WILDCOPY_OVERLENGTH)) ->
  ext_def (a_x a) cc.
Proof.
  intros Hok Hcap Hhd Hcl HE HKb Hl Hu. unfold WILDCOPY_OVERLENGTH in *.
  destruct Hcl as [Hcl|[Hkb Hfar]].
  - apply (xs_ext_def_hi a cc (a_d a + a_cap a)); auto.
    + unfold ext_clean in Hcl. destruct (a_x a); auto; unfold WILDCOPY_OVERLENGTH in Hcl; lia.
    + intros q Hq Hnq. apply Hu; [exact Hq|]. lia.
  - apply (xs_ext_def_hi a cc (a_d a + Z.min (a_cap a) (a_bsm a + 32))); auto.
    + unfold ext_far in Hfar. destruct (a_x a); auto; unfold WILDCOPY_OVERLENGTH in Hfar; lia.
    + intros q Hq Hnq. apply Hu; [exact Hq|]. lia.
Qed.

(* ===================== the model step ===================== *)

(* under the model, with the content within the capacity: the executed bytes so far, the head's step
   (BlkSeqLoopModel.loop_exec_step), the model at ie + 1; the bytes of the step from any leftover lo already
   in place *)
Lemma xs_m0 (a: la) (x: lfx) (ie K j: Z) (sw: bool) (c: list val) (ll ml off: Z) (seqs: list sequence)
    (out' lits': list Z) (rep2: Z * Z * Z) :
  la_ok a -> la_pend a -> lfx_ok a x -> XP a x ie K j sw c (ll, ml, off) -> DM a (x_t x) seqs ->
  EM a seqs out' lits' rep2 -> cnt_len a out' lits' <= a_cap a ->
  exists blk crep' mb,
    Zlength blk = K /\ sublist (a_d a) (a_d a + K) c = zbytes blk /\ lit_intact a j sw c /\
    ll <= a_n a - j /\ K + ll + ml + (a_n a - (j + ll)) <= cnt_len a out' lits' /\
    cnt_len a out' lits' <= a_bsm a /\
    off <= a_d a + K + ll - a_ps a + ext_len (a_x a) /\ Zlength mb = ml /\ rep_ok crep' /\
    K + ll + ml = sum_llml (sublist 0 (ie + 1) seqs) /\ j + ll = sum_ll (sublist 0 (ie + 1) seqs) /\
    rep_chain (a_rep a) (sublist 0 (ie + 1) seqs) = crep' /\
    exec_seqs (hc_wsize (a_h a)) crep' (hc_hist (a_h a)) (sublist (j + ll) (a_n a) (a_lits a))
      (hc_out (a_h a) ++ (blk ++ sublist j (j + ll) (a_lits a) ++ mb)) (sublist (ie + 1) (a_nb a) seqs)
      = Some (out', lits', rep2) /\
    (forall lo cc, 0 <= lo <= ll -> Zlength cc = oa_N (a_o a) ->
       unchanged_outside (oa_c (a_o a)) cc (a_d a) (a_d a + Z.min (a_cap a) (a_bsm a + WILDCOPY_OVERLENGTH)) ->
       sublist (a_d a) (a_d a + K + lo) cc = zbytes (blk ++ sublist j (j + lo) (a_lits a)) ->
       (forall E', E' <= a_d a + a_cap a -> ext_read_ok (a_x a) (a_d a + K + lo) E' (ll - lo) ml off (a_ps a)) /\
       sublist (a_d a + K + lo) (a_d a + K + ll + ml)
         (exec_c cc (a_d a + K + lo) (zbytes (sublist (j + lo) (j + ll) (a_lits a))) ml off (a_ps a) (a_x a)) =
       zbytes (sublist (j + lo) (j + ll) (a_lits a) ++ mb)).
Proof.
  intros Hok Hpend Hfx HXP HDM HEM Hcnt.
  destruct HXP as (Hie & Hsafe & Hdef & Hll & Hml & Hoff & Hm).
  destruct (Hm seqs HDM) as (Hlen & Hov & Hll' & Hml' & Hoff' & HK & Hj & Hexm).
  destruct (Hexm out' lits' rep2 HEM Hcnt) as (Hrep & blk & Hblk & Hsub & Hexb & Hli).
  destruct (xs_basic a x Hok Hpend Hfx ltac:(lia))
    as (Hoc & HoN & Hod & Hcap & Hodc & Hps & Hel & Hib & Hlb & Hn & Hbsm & Hrep0 & HE & Hos).
  destruct Hsafe as (HK0 & HKE & Hj0 & Hsw & Hc & Hu & Hbc0).
  pose proof HEM as (Hex & Hcb & Hhv & Hecl).
  rewrite (xs_sub_cons seqs ie (a_nb a)) in Hexb by lia.
  pose proof (xs_exec_len _ _ _ _ _ _ _ _ _ Hexb) as Hlen0.
  rewrite Zlength_app, Zlength_sublist in Hlen0 by (unfold a_n in *; lia).
  unfold cnt_len in Hcnt, Hcb. xs_fold.
  set (crep := rep_chain (a_rep a) (sublist 0 ie seqs)) in *.
  set (lr := sublist j (a_n a) (a_lits a)) in *.
  assert (Hlrb: bytes_ok lr) by (apply Forall_sublist; exact Hlb).
  assert (Hlrl: Zlength lr = a_n a - j) by (unfold lr, a_n in *; rewrite Zlength_sublist; lia).
  assert (Hstep: forall lo cc, 0 <= lo <= ll -> Zlength cc = oa_N (a_o a) ->
       unchanged_outside (oa_c (a_o a)) cc (a_d a) (a_d a + Z.min (a_cap a) (a_bsm a + WILDCOPY_OVERLENGTH)) ->
       sublist (a_d a) (a_d a + Zlength blk + lo) cc = zbytes (blk ++ firstn (Z.to_nat lo) lr) ->
       exists off0 crep' mb,
         c_offset crep ll (sq_ov (Znth ie seqs)) = (off0, crep') /\ rep_ok crep' /\
         ll <= Zlength lr /\
         a_d a + Zlength blk + ll + ml <= a_d a + cnt_len a out' lits' /\
         1 <= off0 <= a_d a + Zlength blk + ll - a_ps a + ext_len (a_x a) /\
         Zlength mb = ml /\ lz_copy (hc_hist (a_h a)) (hc_out (a_h a) ++ blk ++ firstn (Z.to_nat ll) lr) off0 (Z.to_nat ml) =
           hc_out (a_h a) ++ blk ++ firstn (Z.to_nat ll) lr ++ mb /\
         (a_d a + Zlength blk + ll + ml <= a_d a + a_cap a ->
          (forall E, E <= a_d a + a_cap a -> ext_read_ok (a_x a) (a_d a + Zlength blk + lo) E (ll - lo) ml off0 (a_ps a)) /\
          sublist (a_d a + Zlength blk + lo) (a_d a + Zlength blk + ll + ml)
            (exec_c cc (a_d a + Zlength blk + lo) (zbytes (skipn (Z.to_nat lo) (firstn (Z.to_nat ll) lr))) ml off0 (a_ps a) (a_x a)) =
          zbytes (skipn (Z.to_nat lo) (firstn (Z.to_nat ll) lr) ++ mb)) /\
         exec_seqs (hc_wsize (a_h a)) crep' (hc_hist (a_h a)) (skipn (Z.to_nat ll) lr)
           (hc_out (a_h a) ++ blk ++ firstn (Z.to_nat ll) lr ++ mb) (sublist (ie + 1) (a_nb a) seqs) = Some (out', lits', rep2)).
  { intros lo cc Hlo Hcc Hucc Hscc.
    rewrite Hll', Hml'. unfold cnt_len.
    apply (loop_exec_step_core (oa_c (a_o a)) cc (a_d a) (a_ps a) (a_cap a) (a_bsm a) (a_x a)); try lia;
      try assumption.
    all: first [ rewrite Hcc, Hoc; reflexivity | rewrite Hcc; exact Hib | unfold cnt_len; lia
               | rewrite <- Hll'; exact Hlo | rewrite <- Hml'; lia ]. }
  destruct (Hstep 0 c ltac:(lia) Hc) as (off0 & crep' & mb & Hco & Hrep' & Hllr & Hend & Hoff0 & Hmb & Hlz & Hfit & Hexr).
  { intros q Hq Hnq. apply Hu; [lia|]. intros Hq2. apply Hnq. unfold WILDCOPY_OVERLENGTH in *. lia. }
  { rewrite Z.add_0_r, Hblk. simpl. rewrite app_nil_r. exact Hsub. }
  assert (Hoo: off = off0) by (rewrite Hoff', Hco; reflexivity). subst off0.
  rewrite Hblk in *. unfold lr in *.
  rewrite (xs_firstn_sub (a_lits a) j (a_n a) ll) in * by (unfold a_n in *; lia).
  rewrite (xs_skipn_sub (a_lits a) j (a_n a) ll) in * by (unfold a_n in *; lia).
  pose proof (xs_exec_len _ _ _ _ _ _ _ _ _ Hexr) as Hlen1.
  rewrite !Zlength_app, !Zlength_sublist in Hlen1 by (unfold a_n in *; lia).
  exists blk, crep', mb.
  split; [exact Hblk|]. split; [exact Hsub|]. split; [exact Hli|].
  split; [lia|]. split; [unfold cnt_len; lia|]. split; [unfold cnt_len; lia|].
  split; [lia|]. split; [exact Hmb|]. split; [exact Hrep'|].
  rewrite (xs_sub_snoc seqs ie) by lia.
  rewrite xs_sum_llml_app, xs_sum_ll_app, xs_rep_chain_app, <- HK, <- Hj. cbn [rep_chain].
  rewrite <- Hll'. fold crep. rewrite Hco. cbn [snd].
  split; [simpl; lia|]. split; [simpl; lia|]. split; [reflexivity|]. split; [exact Hexr|].
  intros lo cc Hlo Hcc Hucc Hscc.
  destruct (Hstep lo cc Hlo Hcc Hucc) as (off2 & crep2 & mb2 & Hco2 & _ & _ & _ & _ & Hmb2 & Hlz2 & Hfit2 & _).
  { rewrite (xs_firstn_sub (a_lits a) j (a_n a) lo) by (unfold a_n in *; lia). exact Hscc. }
  rewrite Hco in Hco2. inversion Hco2; subst off2 crep2.
  rewrite Hlz in Hlz2. rewrite !app_assoc in Hlz2. apply app_inv_head in Hlz2. subst mb2.
  rewrite (xs_skipn_sub (a_lits a) j (j + ll) lo) in Hfit2
    by (unfold a_n in *; lia).
  apply Hfit2. unfold cnt_len in Hend. lia.
Qed.

(* ===================== bytes in, bytes out ===================== *)

(* the literal array execSequence reads holds bytes *)
Lemma xs_lit_bytes (a: la) (x: lfx) (c: list val) :
  lfx_ok a x -> byte_cells (iw_c (a_i a)) -> byte_cells c -> byte_cells (lit_arr (lsrc a x) c).
Proof.
  intros (_ & _ & _ & _ & (_ & Hxb & _)) Hi Hc. unfold lsrc. destruct (a_l a); simpl; auto.
Qed.

(* a copy of bytes into a byte array *)
Lemma xs_bytes_patch (c c1: list val) (lo hi: Z) :
  byte_cells c -> Zlength c1 = Zlength c -> unchanged_outside c c1 lo hi -> 0 <= lo <= hi -> hi <= Zlength c ->
  Forall is_byte_val (sublist lo hi c1) -> byte_cells c1.
Proof.
  intros Hc Hl Hu Hlh Hh Hs. unfold byte_cells.
  apply VST.zlist.list_solver.Forall_Znth. intros q Hq.
  destruct (Z_lt_le_dec q lo) as [H1|H1]; [|destruct (Z_lt_le_dec q hi) as [H2|H2]].
  - rewrite Hu by lia. unfold byte_cells in Hc. rewrite VST.zlist.list_solver.Forall_Znth in Hc. apply Hc. lia.
  - rewrite xs_Forall_sub in Hs by lia. apply Hs. lia.
  - rewrite Hu by lia. unfold byte_cells in Hc. rewrite VST.zlist.list_solver.Forall_Znth in Hc. apply Hc. lia.
Qed.

Lemma xs_bytes_sub (c: list val) (lo hi: Z) : byte_cells c -> Forall is_byte_val (sublist lo hi c).
Proof. intros H. apply Forall_sublist. exact H. Qed.

(* ===================== the error return ===================== *)

Lemma xs_err (a: la) (x: lfx) (ie K j: Z) (sw: bool) (c c': list val) (e0: Z * Z * Z) :
  la_ok a -> la_pend a -> lfx_ok a x -> XP a x ie K j sw c e0 ->
  Zlength c' = Zlength c -> unchanged_outside c c' (a_d a) (a_d a + a_cap a) ->
  (byte_cells (oa_c (a_o a)) -> byte_cells (iw_c (a_i a)) -> ext_bytes (a_x a) -> byte_cells c') ->
  (forall seqs out' lits' rep2, DM a (x_t x) seqs -> EM a seqs out' lits' rep2 ->
     cnt_len a out' lits' <= a_cap a -> False) ->
  XERR a c'.
Proof.
  intros Hok Hpend Hfx HXP Hl' Hu' Hb' Hno.
  assert (Hie: 0 <= ie < a_nb a) by (destruct e0 as [[? ?] ?]; apply HXP).
  assert (Hsafe: ex_safe a K j sw c) by (destruct e0 as [[? ?] ?]; apply HXP).
  destruct (xs_basic a x Hok Hpend Hfx ltac:(lia))
    as (Hoc & HoN & Hod & Hcap & Hodc & Hps & Hel & Hib & Hlb & Hn & Hbsm & Hrep0 & HE & Hos).
  destruct Hsafe as (HK0 & HKE & Hj0 & Hsw & Hc & Hu & Hbc0).
  unfold XERR. xs_fold. split.
  { intros q Hq Hnq. rewrite Hu' by lia. apply Hu; [lia|]. unfold WILDCOPY_OVERLENGTH. lia. }
  split; [|exact Hb'].
  intros [Hc0|(Hhv & Hecl)]; [lia|].
  unfold seqs_model. rewrite Hos.
  replace (a_nb a =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  destruct (x_t x) as [[tLL tOF] tML] eqn:Ht.
  destruct (decode_seq_stream tLL tOF tML (iw_s (a_i a)) (a_nb a)) as [seqs|] eqn:Hds; [|exact I].
  destruct (exec_seqs (hc_wsize (a_h a)) (a_rep a) (hc_hist (a_h a)) (a_lits a) (hc_out (a_h a)) seqs)
    as [[[out' lits'] rep2]|] eqn:Hex; [|exact I].
  destruct (exec_seqs_app _ _ _ _ _ _ _ _ _ Hex) as [mid Hmid].
  assert (Hlen: Zlength (skipn (length (hc_out (a_h a))) (out' ++ lits')) = cnt_len a out' lits').
  { unfold cnt_len. rewrite Hmid, <- app_assoc, skipn_app, skipn_all, Nat.sub_diag, skipn_O. simpl.
    rewrite !Zlength_app. lia. }
  rewrite Hlen. intros Hcb.
  destruct (Z_lt_le_dec (a_cap a) (cnt_len a out' lits')) as [H|H]; [exact H|].
  exfalso. apply (Hno seqs out' lits' rep2).
  - unfold DM. exact Hds.
  - unfold EM. xs_fold. refine (conj Hex (conj Hcb (conj Hhv Hecl))).
  - exact H.
Qed.

(* ===================== literal and capacity facts ===================== *)

Lemma xs_sub_in {A} {IA: Inhabitant A} (l L: list A) (lo hi p q: Z) :
  sublist lo hi l = L -> 0 <= lo -> hi <= Zlength l -> lo <= p -> p <= q -> q <= hi ->
  sublist p q l = sublist (p - lo) (q - lo) L.
Proof. intros H H1 H2 H3 H4 H5. rewrite <- H. rewrite sublist_sublist by lia. f_equal; lia. Qed.

Lemma xs_lim_N (a: la) (sw: bool) (j: Z) :
  nosplit a sw -> lit_lim a sw - lit_li a sw j = a_n a - j.
Proof. unfold nosplit, lit_lim, lit_li. destruct (a_l a); intros; try subst sw; lia. Qed.

(* the literals execSequence reads (not the split head) *)
Lemma xs_lits_N (a: la) (x: lfx) (K j: Z) (sw: bool) (c: list val) (ll: Z) :
  la_ok a -> lfx_ok a x -> ex_safe a K j sw c -> nosplit a sw -> 0 <= ll -> j + ll <= a_n a ->
  sublist (lit_li a sw j) (lit_li a sw j + ll) (lit_arr (lsrc a x) c) = zbytes (sublist j (j + ll) (a_lits a)).
Proof.
  intros (Ho & Hi & Hla & Hbsm & Hn & _) (_ & _ & _ & _ & Hxc) (HK0 & HKE & Hj0 & Hsw & Hc & Hu & Hbc0) Hns Hll Hjl.
  destruct Ho as (_ & Hoc & HoN & Hod & Hocap & Hodc).
  destruct Hla as (Hlb & Hln & Hl). destruct Hxc as (Hxl & Hxbc & Hxc).
  unfold lit_li, lsrc, lit_arr, nosplit, a_E, a_n, a_d, a_cap in *.
  destruct (a_l a) as [off| |lb|lb] eqn:Hloc.
  - destruct Hl as (Hoff & HoffN & Hs & _). destruct Hi as (_ & _ & _ & _ & HiN & _).
    rewrite (xs_sub_in _ _ _ _ _ _ Hs) by (unfold WILDCOPY_OVERLENGTH in *; lia).
    rewrite sublist_map. f_equal; f_equal; lia.
  - rewrite (xs_sub_in _ _ _ _ _ _ Hxc) by (unfold LITEXTRA_N, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *; lia).
    rewrite sublist_map. f_equal; f_equal; lia.
  - destruct Hl as (Hlb0 & HlbE & Hs).
    rewrite (xs_sublist_ext (oa_c (a_o a)) c) by (unfold WILDCOPY_OVERLENGTH in *; first [lia | intros q Hq; apply Hu; lia]).
    rewrite (xs_sub_in _ _ _ _ _ _ Hs) by (unfold WILDCOPY_OVERLENGTH in *; lia).
    rewrite sublist_map. f_equal; f_equal; lia.
  - subst sw. destruct Hl as (Hbig & Hlb0 & HlbE & Hs).
    rewrite (xs_sub_in _ _ _ _ _ _ Hxc) by (unfold LITEXTRA_N, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *; lia).
    rewrite sublist_map. rewrite sublist_sublist by (unfold a_n in *; lia). f_equal; f_equal; lia.
Qed.

(* oend is beyond the content within min(cap, bsm) *)
Lemma xs_E_big (a: la) : la_pend a -> a_d a + Z.min (a_cap a) (a_bsm a) <= a_E a.
Proof. intros (_ & Hp). unfold a_E. destruct (a_l a); lia. Qed.

(* the positions of the model after the head *)
Lemma xs_sums (a: la) (x: lfx) (ie K j: Z) (sw: bool) (c: list val) (ll ml off: Z) (seqs: list sequence) :
  XP a x ie K j sw c (ll, ml, off) -> DM a (x_t x) seqs ->
  K + (ll + ml) = sum_llml (sublist 0 (ie + 1) seqs) /\ j + ll = sum_ll (sublist 0 (ie + 1) seqs).
Proof.
  intros (Hie & _ & _ & _ & _ & _ & Hm) HDM.
  destruct (Hm seqs HDM) as (Hlen & _ & Hll' & Hml' & _ & HK & Hj & _).
  rewrite (xs_sub_snoc seqs ie) by lia. rewrite xs_sum_llml_app, xs_sum_ll_app, <- HK, <- Hj.
  simpl. lia.
Qed.

(* ===================== (N) execSequence, literals not the split head ===================== *)

Lemma xs_case_N (a: la) (x: lfx) (ie K j: Z) (sw: bool) (c: list val) (ll ml off: Z) :
  la_ok a -> la_pend a -> lfx_ok a x -> XP a x ie K j sw c (ll, ml, off) ->
  let k := a_d a + K in let E := a_E a in let ps := a_ps a in let xs := a_x a in let elen := ext_len (a_x a) in
  (nosplit a sw ->
   let li := lit_li a sw j in let lim := lit_lim a sw in let ls := lsrc a x in
   forall c', Zlength c' = Zlength c ->
   (byte_cells c -> byte_cells (lit_arr ls c) -> ext_bytes xs -> byte_cells c') -> xd_ub c c' ->
   (exec_err k E li lim ll ml off ps elen = true -> unchanged_outside c c' k E -> XERR a c') /\
   (exec_err k E li lim ll ml off ps elen = false ->
    unchanged_outside c c' k (Z.min E (k + (ll + ml) + WILDCOPY_OVERLENGTH)) ->
    Forall is_byte_val (sublist k (k + (ll + ml)) c') ->
    (ext_read_ok xs k E ll ml off ps ->
       sublist k (k + (ll + ml)) c' =
         sublist k (k + (ll + ml)) (exec_c c k (sublist li (li + ll) (lit_arr ls c)) ml off ps xs) /\
       (Forall is_byte_val (sublist ps k c) -> Forall is_byte_val (sublist li (li + ll) (lit_arr ls c)) ->
        ext_def xs c -> Forall is_byte_val (sublist k (k + (ll + ml)) c'))) ->
    XQ a x (ie + 1) (K + (ll + ml)) (j + ll) sw c')).
Proof.
  intros Hok Hpend Hfx HXP k E ps xs elen Hns li lim ls c' Hl' Hbyc' Hxu.
  pose proof HXP as (Hie & Hsafe & Hdef & Hll & Hml & Hoff & Hm).
  destruct (xs_basic a x Hok Hpend Hfx ltac:(lia))
    as (Hoc & HoN & Hod & Hcap & Hodc & Hps & Hel & Hib & Hlb & Hn & Hbsm & Hrep0 & HE & Hos).
  pose proof Hsafe as (HK0 & HKE & Hj0 & Hsw & Hc & Hu & Hbc0).
  assert (Hlim: lim - li = a_n a - j) by apply xs_lim_N, Hns.
  pose proof (xs_E_big a Hpend) as HEb.
  split.
  - intros Herr Hu'. apply (xs_err a x ie K j sw c c' (ll, ml, off)); auto.
    + intros q Hq Hnq. apply Hu'; [lia|]. unfold k, E in *. lia.
    + intros Hb1 Hb2 Hb3. apply Hbyc'; [apply Hbc0; auto | apply xs_lit_bytes; auto; apply Hbc0; auto | exact Hb3].
    + intros seqs out' lits' rep2 HDM HEM Hcnt.
      destruct (xs_m0 a x ie K j sw c ll ml off seqs out' lits' rep2 Hok Hpend Hfx HXP HDM HEM Hcnt)
        as (blk & crep' & mb & Hblk & Hsub & Hli & Hlln & Hcntb & Hcb & Hoffb & _).
      unfold exec_err in Herr. rewrite !orb_true_iff, !Z.ltb_lt in Herr.
      unfold k, E, ps, elen in *. lia.
  - intros Hnerr Hu' Hxf Hby. unfold exec_err in Hnerr. rewrite !orb_false_iff, !Z.ltb_ge in Hnerr.
    destruct Hnerr as ((H1 & H2) & H3).
    assert (Hlits: sublist li (li + ll) (lit_arr ls c) = zbytes (sublist j (j + ll) (a_lits a)))
      by (apply xs_lits_N with (K := K); auto; lia).
    assert (Hu0: unchanged_outside (oa_c (a_o a)) c (a_d a) (a_d a + a_cap a)).
    { intros q Hq Hnq. apply Hu; [lia|]. lia. }
    assert (Hc'd: sublist (a_d a) (a_d a + K) c' = sublist (a_d a) (a_d a + K) c).
    { apply xs_sublist_ext; try lia. intros q Hq. apply Hu'; [lia|]. unfold k. lia. }
    split; [|split].
    + unfold ex_safe. split; [lia|]. split; [unfold k, E in *; lia|]. split; [lia|].
      split; [revert Hsw Hns; clear - Hll; unfold nosplit; destruct (a_l a); auto; intros; subst; lia|].
      split; [lia|].
      split; [intros q Hq Hnq; rewrite Hu' by (unfold k, E in *; lia); apply Hu; [lia|]; lia|].
      intros Hb1 Hb2 Hb3. apply Hbyc'; [apply Hbc0; auto | apply xs_lit_bytes; auto; apply Hbc0; auto | exact Hb3].
    + apply (ex_def_step a K (ll + ml) j (j + ll) sw sw c c'); unfold k, E in *; auto; try lia.
    + intros seqs HDM.
      destruct (xs_sums a x ie K j sw c ll ml off seqs HXP HDM) as (Hs1 & Hs2).
      unfold ex_model. split; [exact Hs1|]. split; [exact Hs2|].
      intros out' lits' rep2 HEM Hcnt.
      destruct (xs_m0 a x ie K j sw c ll ml off seqs out' lits' rep2 Hok Hpend Hfx HXP HDM HEM Hcnt)
        as (blk & crep' & mb & Hblk & Hsub & Hli & Hlln & Hcntb & Hcb & Hoffb & Hmb & Hrep' & _ & _ & Hrc &
            Hexr & Hstep).
      split; [rewrite Hrc; exact Hrep'|].
      destruct (Hstep 0 c) as (Hro0 & Hb0).
      { lia. }
      { exact Hc. }
      { intros q Hq Hnq. apply Hu; [lia|]. unfold WILDCOPY_OVERLENGTH in *. lia. }
      { rewrite !Z.add_0_r, sublist_nil, app_nil_r. exact Hsub. }
      rewrite !Z.add_0_r, !Z.sub_0_r in Hro0. rewrite !Z.add_0_r in Hb0.
      exists (blk ++ sublist j (j + ll) (a_lits a) ++ mb).
      split; [rewrite !Zlength_app, Zlength_sublist by (unfold a_n in *; lia); lia|].
      split.
      * rewrite (sublist_split (a_d a) (a_d a + K) (a_d a + (K + (ll + ml)))) by lia.
        rewrite map_app. f_equal; [rewrite Hc'd; exact Hsub|].
        replace (a_d a + (K + (ll + ml))) with (k + (ll + ml)) by (unfold k; lia).
        change (a_d a + K) with k. rewrite (proj1 (Hby (Hro0 E ltac:(unfold E; lia)))). rewrite Hlits.
        replace (k + (ll + ml)) with (a_d a + K + ll + ml) by (unfold k; lia). exact Hb0.
      * split; [rewrite Hrc; exact Hexr|].
        unfold lit_intact. revert Hns. unfold nosplit. destruct (a_l a); auto. intros -> ?. discriminate.
Qed.

(* ===================== (S) execSequenceSplitLitBuffer ===================== *)

(* the split literals still in place, cut at j + t *)
Lemma xs_split_lits (a: la) (lb j t: Z) (c: list val) :
  a_l a = LSplit lb -> lit_intact a j false c -> 0 <= lb -> 0 <= j -> 0 <= t ->
  j + t <= a_n a - LITBUFFEREXTRASIZE -> lb + (a_n a - LITBUFFEREXTRASIZE) <= Zlength c ->
  sublist (lb + j) (lb + j + t) c = zbytes (sublist j (j + t) (a_lits a)) /\
  sublist (lb + j + t) (lb + (a_n a - LITBUFFEREXTRASIZE)) c =
    zbytes (sublist (j + t) (a_n a - LITBUFFEREXTRASIZE) (a_lits a)).
Proof.
  intros Hl Hli Hlb Hj Ht Hjt Hc. unfold lit_intact in Hli. rewrite Hl in Hli. specialize (Hli eq_refl).
  assert (Hn: a_n a = Zlength (a_lits a)) by reflexivity.
  split.
  - rewrite (xs_sub_in _ _ _ _ _ _ Hli) by lia. rewrite sublist_map, sublist_sublist by lia.
    f_equal; f_equal; lia.
  - rewrite (xs_sub_in _ _ _ _ _ _ Hli) by lia. rewrite sublist_map, sublist_sublist by lia.
    f_equal; f_equal; lia.
Qed.

Lemma xs_case_S (a: la) (x: lfx) (ie K j: Z) (sw: bool) (c: list val) (ll ml off: Z) :
  la_ok a -> la_pend a -> lfx_ok a x -> XP a x ie K j sw c (ll, ml, off) ->
  let k := a_d a + K in let E := a_E a in let ps := a_ps a in let xs := a_x a in let elen := ext_len (a_x a) in
  (forall lb, a_l a = LSplit lb -> sw = false -> lit_li a false j + ll <= lit_lim a false ->
   let li := lit_li a false j in
   forall c', Zlength c' = Zlength c ->
   (byte_cells c -> ext_bytes xs -> byte_cells c') -> xd_ub c c' ->
   (exec_split_err k E li ll ml off ps elen = true -> unchanged_outside c c' k E -> XERR a c') /\
   (exec_split_err k E li ll ml off ps elen = false ->
    unchanged_outside c c' k (Z.min (Z.min E (k + (ll + ml) + WILDCOPY_OVERLENGTH)) (Z.max (k + (ll + ml)) (li + ll))) ->
    Forall is_byte_val (sublist k (k + (ll + ml)) c') ->
    (ext_read_ok xs k E ll ml off ps ->
       (lit_exact_split k li ll ->
          sublist k (k + (ll + ml)) c' = sublist k (k + (ll + ml)) (exec_c c k (sublist li (li + ll) c) ml off ps xs)) /\
       (Forall is_byte_val (sublist ps k c) -> Forall is_byte_val (sublist li (li + ll) c) ->
        ext_def xs c -> Forall is_byte_val (sublist k (k + (ll + ml)) c'))) ->
    XQ a x (ie + 1) (K + (ll + ml)) (j + ll) false c')).
Proof.
  intros Hok Hpend Hfx HXP k E ps xs elen lb Hl Hsw0 Hlil li c' Hl' Hbyc' Hxu. subst sw.
  pose proof HXP as (Hie & Hsafe & Hdef & Hll & Hml & Hoff & Hm).
  destruct (xs_basic a x Hok Hpend Hfx ltac:(lia))
    as (Hoc & HoN & Hod & Hcap & Hodc & Hps & Hel & Hib & Hlb & Hn & Hbsm & Hrep0 & HE & Hos).
  pose proof Hsafe as (HK0 & HKE & Hj0 & Hsw & Hc & Hu & Hbc0).
  pose proof Hok as (_ & _ & (_ & _ & Hla) & _). rewrite Hl in Hla.
  destruct Hla as (Hbig & Hlb0 & HlbE & Hlbs).
  pose proof Hpend as (_ & Hpl). rewrite Hl in Hpl, Hsw.
  assert (HEe: E = a_d a + a_cap a) by (unfold E, a_E; rewrite Hl; reflexivity).
  assert (HEa: a_E a = a_d a + a_cap a) by (unfold a_E; rewrite Hl; reflexivity).
  rewrite HEa in *.
  assert (Hlie: li = lb + j) by (unfold li, lit_li; rewrite Hl; reflexivity).
  clearbody E li. subst E li.
  unfold lit_li, lit_lim in Hlil. rewrite Hl in Hlil.
  xs_fold. unfold WILDCOPY_OVERLENGTH, LITBUFFEREXTRASIZE in *.
  (* under the model: the literals are far ahead of op *)
  assert (Hfar: forall seqs out' lits' rep2, DM a (x_t x) seqs -> EM a seqs out' lits' rep2 ->
            cnt_len a out' lits' <= a_cap a -> k + ml + 32 <= lb + j).
  { intros seqs out' lits' rep2 HDM HEM Hcnt.
    destruct (xs_m0 a x ie K j false c ll ml off seqs out' lits' rep2 Hok Hpend Hfx HXP HDM HEM Hcnt)
      as (blk & crep' & mb & Hblk & Hsub & Hli & Hlln & Hcntb & Hcb & _).
    unfold k. lia. }
  split.
  - intros Herr Hu'. apply (xs_err a x ie K j false c c' (ll, ml, off)); auto.
    + intros q Hq Hnq. apply Hu'; [lia|]. unfold k in *. lia.
    + intros seqs out' lits' rep2 HDM HEM Hcnt.
      pose proof (Hfar seqs out' lits' rep2 HDM HEM Hcnt) as Hf.
      destruct (xs_m0 a x ie K j false c ll ml off seqs out' lits' rep2 Hok Hpend Hfx HXP HDM HEM Hcnt)
        as (blk & crep' & mb & Hblk & Hsub & Hli & Hlln & Hcntb & Hcb & Hoffb & _).
      unfold exec_split_err in Herr. rewrite !orb_true_iff, !andb_true_iff, !Z.ltb_lt in Herr.
      unfold k, ps, elen in *. lia.
  - intros Hnerr Hu' Hxf Hby. unfold exec_split_err in Hnerr.
    rewrite !orb_false_iff, !Z.ltb_ge in Hnerr. destruct Hnerr as ((H1 & H2) & H3).
    assert (Hc'd: sublist (a_d a) (a_d a + K) c' = sublist (a_d a) (a_d a + K) c).
    { apply xs_sublist_ext; try lia. intros q Hq. apply Hu'; [lia|]. unfold k. lia. }
    split; [|split].
    + unfold ex_safe. rewrite Hl, HEa. unfold LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *. split; [lia|]. split; [unfold k in *; lia|].
      split; [lia|]. split; [lia|]. split; [lia|].
      split; [intros q Hq Hnq; rewrite Hu' by (unfold k in *; lia); apply Hu; [lia|]; lia|].
      intros Hb1 Hb2 Hb3. apply Hbyc'; [apply Hbc0; auto | exact Hb3].
    + apply (ex_def_step a K (ll + ml) j (j + ll) false false c c'); unfold k in *; auto; try lia.
    + intros seqs HDM.
      destruct (xs_sums a x ie K j false c ll ml off seqs HXP HDM) as (Hs1 & Hs2).
      unfold ex_model. split; [exact Hs1|]. split; [exact Hs2|].
      intros out' lits' rep2 HEM Hcnt.
      pose proof (Hfar seqs out' lits' rep2 HDM HEM Hcnt) as Hf.
      destruct (xs_m0 a x ie K j false c ll ml off seqs out' lits' rep2 Hok Hpend Hfx HXP HDM HEM Hcnt)
        as (blk & crep' & mb & Hblk & Hsub & Hli & Hlln & Hcntb & Hcb & Hoffb & Hmb & Hrep' & _ & _ & Hrc &
            Hexr & Hstep).
      split; [rewrite Hrc; exact Hrep'|].
      destruct (Hstep 0 c) as (Hro0 & Hb0).
      { lia. }
      { exact Hc. }
      { intros q Hq Hnq. apply Hu; [lia|]. unfold WILDCOPY_OVERLENGTH in *. lia. }
      { rewrite !Z.add_0_r, sublist_nil, app_nil_r. exact Hsub. }
      rewrite !Z.add_0_r, !Z.sub_0_r in Hro0. rewrite !Z.add_0_r in Hb0.
      destruct (xs_split_lits a lb j ll c Hl Hli ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(unfold LITBUFFEREXTRASIZE; lia) ltac:(unfold LITBUFFEREXTRASIZE; lia)) as (HL1 & HL2).
      exists (blk ++ sublist j (j + ll) (a_lits a) ++ mb).
      split; [rewrite !Zlength_app, Zlength_sublist by (unfold a_n in *; lia); lia|].
      split.
      * rewrite (sublist_split (a_d a) (a_d a + K) (a_d a + (K + (ll + ml)))) by lia.
        rewrite map_app. f_equal; [rewrite Hc'd; exact Hsub|].
        replace (a_d a + (K + (ll + ml))) with (k + (ll + ml)) by (unfold k; lia).
        change (a_d a + K) with k.
        rewrite (proj1 (Hby (Hro0 (a_d a + a_cap a) ltac:(lia)))) by (unfold lit_exact_split; right; right; lia).
        rewrite HL1.
        replace (k + (ll + ml)) with (a_d a + K + ll + ml) by (unfold k; lia). exact Hb0.
      * split; [rewrite Hrc; exact Hexr|].
        unfold lit_intact. rewrite Hl. intros _. unfold LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *.
        rewrite <- HL2. replace (lb + (j + ll)) with (lb + j + ll) by lia.
        apply xs_sublist_ext; try lia. intros q Hq. apply Hu'; [lia|]. lia.
Qed.

(* ===================== (X1) leftover, switch, execSequence on litExtraBuffer ===================== *)

(* litExtraBuffer holds the last 65536 literals *)
Lemma xs_xc_lits (a: la) (x: lfx) (lb s t: Z) :
  la_ok a -> lfx_ok a x -> a_l a = LSplit lb -> 0 <= s -> 0 <= t -> s + t <= LITBUFFEREXTRASIZE ->
  sublist s (s + t) (x_xc x) =
    zbytes (sublist (a_n a - LITBUFFEREXTRASIZE + s) (a_n a - LITBUFFEREXTRASIZE + s + t) (a_lits a)).
Proof.
  intros (_ & _ & (_ & _ & Hla) & _) (_ & _ & _ & _ & (Hxl & _ & Hxc)) Hl Hs Ht Hst.
  rewrite Hl in Hla, Hxc. destruct Hla as (Hbig & _).
  assert (Hn: a_n a = Zlength (a_lits a)) by reflexivity.
  rewrite (xs_sub_in _ _ _ _ _ _ Hxc) by (unfold LITEXTRA_N, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *; lia).
  rewrite sublist_map, sublist_sublist by lia. f_equal; f_equal; lia.
Qed.

Lemma xs_case_X1 (a: la) (x: lfx) (ie K j: Z) (sw: bool) (c: list val) (ll ml off: Z) :
  la_ok a -> la_pend a -> lfx_ok a x -> XP a x ie K j sw c (ll, ml, off) ->
  let k := a_d a + K in let E := a_E a in let ps := a_ps a in let xs := a_x a in let elen := ext_len (a_x a) in
  (forall lb, a_l a = LSplit lb -> sw = false -> lit_lim a false - lit_li a false j < ll ->
   let li := lit_li a false j in let lo := lit_lim a false - li in
   (0 < lo -> E - k < lo -> XERR a c) /\
   forall c1, (lo = 0 -> c1 = c) -> (0 < lo -> lo <= E - k /\ copied c c1 k li lo) ->
   let k1 := k + lo in let ls := lsrc a x in let li1 := lit_li a true (j + lo) in let lim1 := lit_lim a true in
   forall c', Zlength c' = Zlength c ->
   (byte_cells c1 -> byte_cells (lit_arr ls c1) -> ext_bytes xs -> byte_cells c') -> xd_ub c1 c' ->
   (exec_err k1 E li1 lim1 (ll - lo) ml off ps elen = true -> unchanged_outside c1 c' k1 E -> XERR a c') /\
   (exec_err k1 E li1 lim1 (ll - lo) ml off ps elen = false ->
    unchanged_outside c1 c' k1 (Z.min E (k1 + (ll - lo + ml) + WILDCOPY_OVERLENGTH)) ->
    Forall is_byte_val (sublist k1 (k1 + (ll - lo + ml)) c') ->
    (ext_read_ok xs k1 E (ll - lo) ml off ps ->
       sublist k1 (k1 + (ll - lo + ml)) c' =
         sublist k1 (k1 + (ll - lo + ml)) (exec_c c1 k1 (sublist li1 (li1 + (ll - lo)) (lit_arr ls c1)) ml off ps xs) /\
       (Forall is_byte_val (sublist ps k1 c1) -> Forall is_byte_val (sublist li1 (li1 + (ll - lo)) (lit_arr ls c1)) ->
        ext_def xs c1 -> Forall is_byte_val (sublist k1 (k1 + (ll - lo + ml)) c'))) ->
    XQ a x (ie + 1) (K + (ll + ml)) (j + ll) true c')).
Proof.
  intros Hok Hpend Hfx HXP k E ps xs elen lb Hl Hsw0 Hlil li lo. subst sw.
  pose proof HXP as (Hie & Hsafe & Hdef & Hll & Hml & Hoff & Hm).
  destruct (xs_basic a x Hok Hpend Hfx ltac:(lia))
    as (Hoc & HoN & Hod & Hcap & Hodc & Hps & Hel & Hib & Hlb & Hn & Hbsm & Hrep0 & HE & Hos).
  pose proof Hsafe as (HK0 & HKE & Hj0 & Hsw & Hc & Hu & Hbc0).
  pose proof Hok as (_ & _ & (_ & _ & Hla) & _). rewrite Hl in Hla.
  destruct Hla as (Hbig & Hlb0 & HlbE & Hlbs).
  pose proof Hpend as (_ & Hpl). rewrite Hl in Hpl, Hsw.
  assert (HEe: E = a_d a + a_cap a) by (unfold E, a_E; rewrite Hl; reflexivity).
  assert (HEa: a_E a = a_d a + a_cap a) by (unfold a_E; rewrite Hl; reflexivity).
  rewrite HEa in *.
  assert (Hlie: li = lb + j) by (unfold li, lit_li; rewrite Hl; reflexivity).
  assert (Hloe: lo = a_n a - LITBUFFEREXTRASIZE - j) by (unfold lo, lit_lim; rewrite Hl, Hlie; lia).
  clearbody E li lo. subst E li.
  unfold lit_li, lit_lim in Hlil. rewrite Hl in Hlil.
  xs_fold. unfold WILDCOPY_OVERLENGTH, LITBUFFEREXTRASIZE in *.
  assert (Hlo0: 0 <= lo < ll) by lia.
  split.
  { intros Hlo Hbad. apply (xs_err a x ie K j false c c (ll, ml, off)); auto.
    - intros q Hq Hnq. reflexivity.
    - intros seqs out' lits' rep2 HDM HEM Hcnt.
      destruct (xs_m0 a x ie K j false c ll ml off seqs out' lits' rep2 Hok Hpend Hfx HXP HDM HEM Hcnt)
        as (blk & crep' & mb & Hblk & Hsub & Hli & Hlln & Hcntb & Hcb & _).
      unfold k in *. lia. }
  intros c1 Hc1z Hc1p c' Hl' Hbyc' Hxu.
  assert (Hli1: lit_li a true (j + lo) = 0) by (unfold lit_li; rewrite Hl; unfold LITBUFFEREXTRASIZE; lia).
  assert (Hlim1: lit_lim a true = LITBUFFEREXTRASIZE) by (unfold lit_lim; rewrite Hl; reflexivity).
  assert (Hls: lit_arr (lsrc a x) c1 = x_xc x) by (unfold lsrc; rewrite Hl; reflexivity).
  rewrite Hli1, Hlim1, Hls. set (k1 := k + lo) in *.
  (* the leftover copy *)
  assert (Hc1: Zlength c1 = Zlength c /\ k + lo <= a_d a + a_cap a /\
               unchanged_outside c c1 k (k + lo) /\
               (Forall is_byte_val (sublist (lb + j) (lb + j + lo) c) -> Forall is_byte_val (sublist k (k + lo) c1)) /\
               (k + 32 <= lb + j -> sublist k (k + lo) c1 = sublist (lb + j) (lb + j + lo) c) /\
               (byte_cells c -> byte_cells c1)).
  { destruct (Z.eq_dec lo 0) as [H0|H0].
    - rewrite (Hc1z H0). rewrite H0, Z.add_0_r, !sublist_nil. unfold k.
      repeat split; auto; try lia. intros _. rewrite Z.add_0_r, sublist_nil. reflexivity.
    - destruct (Hc1p ltac:(lia)) as (Hloe' & Hcl & Hcd & Hcb & Hcu).
      split; [exact Hcl|]. split; [lia|]. split; [exact Hcu|]. split; [exact Hcb|].
      split.
      + intros Hfar. rewrite Hcd by (unfold WILDCOPY_VECLEN, WILDCOPY_OVERLENGTH; lia).
        apply xs_listcopy_ahead_sub; unfold k in *; lia.
      + intros Hb. apply (xs_bytes_patch c c1 k (k + lo)); auto; unfold k in *; try lia.
        apply Hcb, xs_bytes_sub, Hb. }
  destruct Hc1 as (Hc1l & Hk1E & Hc1u & Hc1b & Hc1e & Hc1y).
  assert (Hxcb: byte_cells (x_xc x)) by (destruct Hfx as (_ & _ & _ & _ & (_ & Hxb & _)); exact Hxb).
  assert (Hc1o: unchanged_outside (oa_c (a_o a)) c1 (a_d a) (a_d a + a_cap a)).
  { intros q Hq Hnq. rewrite Hc1u by (unfold k in *; lia). apply Hu; lia. }
  (* under the model: the literals are far ahead of op *)
  assert (Hfar: forall seqs out' lits' rep2, DM a (x_t x) seqs -> EM a seqs out' lits' rep2 ->
            cnt_len a out' lits' <= a_cap a -> k + ml + 32 <= lb + j).
  { intros seqs out' lits' rep2 HDM HEM Hcnt.
    destruct (xs_m0 a x ie K j false c ll ml off seqs out' lits' rep2 Hok Hpend Hfx HXP HDM HEM Hcnt)
      as (blk & crep' & mb & Hblk & Hsub & Hli & Hlln & Hcntb & Hcb & _).
    unfold k. lia. }
  split.
  - intros Herr Hu'. apply (xs_err a x ie K j false c c' (ll, ml, off)); auto.
    + intros q Hq Hnq. rewrite Hu' by (unfold k1, k in *; lia). apply Hc1u; unfold k in *; lia.
    + intros Hb1 Hb2 Hb3. apply Hbyc'; [apply Hc1y, Hbc0; auto | rewrite Hls; exact Hxcb | exact Hb3].
    + intros seqs out' lits' rep2 HDM HEM Hcnt.
      destruct (xs_m0 a x ie K j false c ll ml off seqs out' lits' rep2 Hok Hpend Hfx HXP HDM HEM Hcnt)
        as (blk & crep' & mb & Hblk & Hsub & Hli & Hlln & Hcntb & Hcb & Hoffb & _).
      unfold exec_err in Herr. rewrite !orb_true_iff, !Z.ltb_lt in Herr.
      unfold k1, k, ps, elen, LITBUFFEREXTRASIZE in *. lia.
  - intros Hnerr Hu' Hxf Hby. unfold exec_err in Hnerr. rewrite !orb_false_iff, !Z.ltb_ge in Hnerr.
    destruct Hnerr as ((H1 & H2) & H3). unfold LITBUFFEREXTRASIZE in H2.
    assert (Hc'd: sublist (a_d a) (a_d a + K) c' = sublist (a_d a) (a_d a + K) c).
    { apply xs_sublist_ext; try lia. intros q Hq.
      rewrite Hu' by (unfold k1, k in *; lia). apply Hc1u; unfold k in *; lia. }
    assert (Hc'k: sublist k k1 c' = sublist k (k + lo) c1).
    { unfold k1. apply xs_sublist_ext; unfold k in *; try lia. intros q Hq. apply Hu'; lia. }
    split; [|split].
    + unfold ex_safe. rewrite Hl, HEa. unfold LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *.
      split; [lia|]. split; [unfold k1, k in *; lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [intros q Hq Hnq; rewrite Hu' by (unfold k1, k in *; lia);
              rewrite Hc1u by (unfold k in *; lia); apply Hu; [lia|]; lia|].
      intros Hb1 Hb2 Hb3. apply Hbyc'; [apply Hc1y, Hbc0; auto | rewrite Hls; exact Hxcb | exact Hb3].
    + assert (Hsrc: Forall is_byte_val (sublist (lb + j) (lb + j + lo) c)).
      { pose proof (ex_def_lits a (x_xc x) K j false c Hok ltac:(destruct Hfx as (_ & _ & _ & _ & Hxc); exact Hxc)
                      Hcap ltac:(unfold a_n in *; lia) Hc Hdef) as Hs.
        rewrite Hl in Hs. destruct Hs as (Hs1 & _).
        specialize (Hs1 ltac:(unfold a_n, LITBUFFEREXTRASIZE in *; lia)).
        apply (xd_sub _ (lb + j) (lb + (a_n a - LITBUFFEREXTRASIZE) + WILDCOPY_OVERLENGTH)); auto;
          unfold a_n, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *; lia. }
      assert (Hc1d: ex_def a (K + lo) j false c1).
      { destruct (Z.eq_dec lo 0) as [H0|H0].
        - rewrite (Hc1z H0), H0, Z.add_0_r. exact Hdef.
        - apply (ex_def_step a K lo j j false false c c1); unfold k in *; auto; try lia;
            first [ apply (xd_ub_frame c c1 (a_d a + K) (a_d a + K + lo));
                      [exact Hc1u | apply xd_Forall_rng; [lia | lia | apply Hc1b; exact Hsrc]]
                  | apply Hc1b; exact Hsrc ]. }
      replace (K + (ll + ml)) with (K + lo + (ll - lo + ml)) by lia.
      apply (ex_def_step a (K + lo) (ll - lo + ml) j (j + ll) false true c1 c'); unfold k1, k in *; auto; try lia.
      all: replace (a_d a + (K + lo)) with (a_d a + K + lo) by lia; exact Hxf.
    + intros seqs HDM.
      destruct (xs_sums a x ie K j false c ll ml off seqs HXP HDM) as (Hs1 & Hs2).
      unfold ex_model. split; [exact Hs1|]. split; [exact Hs2|].
      intros out' lits' rep2 HEM Hcnt.
      pose proof (Hfar seqs out' lits' rep2 HDM HEM Hcnt) as Hf.
      destruct (xs_m0 a x ie K j false c ll ml off seqs out' lits' rep2 Hok Hpend Hfx HXP HDM HEM Hcnt)
        as (blk & crep' & mb & Hblk & Hsub & Hli & Hlln & Hcntb & Hcb & Hoffb & Hmb & Hrep' & _ & _ & Hrc &
            Hexr & Hstep).
      split; [rewrite Hrc; exact Hrep'|].
      destruct (xs_split_lits a lb j lo c Hl Hli ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(unfold LITBUFFEREXTRASIZE; lia) ltac:(unfold LITBUFFEREXTRASIZE; lia)) as (HL1 & _).
      assert (Hlo1: sublist k (k + lo) c1 = zbytes (sublist j (j + lo) (a_lits a)))
        by (rewrite Hc1e by lia; exact HL1).
      destruct (Hstep lo c1) as (Hro1 & Hb1).
      { lia. }
      { lia. }
      { intros q Hq Hnq. unfold WILDCOPY_OVERLENGTH in *. rewrite Hc1u by (unfold k in *; lia). apply Hu; [lia|].
        unfold WILDCOPY_OVERLENGTH in *. lia. }
      { rewrite (sublist_split (a_d a) (a_d a + K) (a_d a + K + lo)) by lia.
        rewrite map_app. f_equal; [|exact Hlo1].
        rewrite (xs_sublist_ext c c1) by (try lia; intros q Hq; apply Hc1u; unfold k; lia). exact Hsub. }
      exists (blk ++ sublist j (j + ll) (a_lits a) ++ mb).
      split; [rewrite !Zlength_app, Zlength_sublist by (unfold a_n in *; lia); lia|].
      split.
      * rewrite (sublist_split (a_d a) (a_d a + K) (a_d a + (K + (ll + ml)))) by lia.
        rewrite map_app. f_equal; [rewrite Hc'd; exact Hsub|].
        change (a_d a + K) with k.
        rewrite (sublist_split k k1 (a_d a + (K + (ll + ml)))) by (unfold k1, k in *; lia).
        rewrite (sublist_split j (j + lo) (j + ll)) by (unfold a_n in *; lia).
        rewrite <- app_assoc, !map_app. f_equal; [rewrite Hc'k; exact Hlo1|].
        replace (a_d a + (K + (ll + ml))) with (k1 + (ll - lo + ml)) by (unfold k1, k; lia).
        rewrite (proj1 (Hby (Hro1 (a_d a + a_cap a) ltac:(lia)))).
        rewrite (xs_xc_lits a x lb 0 (ll - lo)) by (auto; unfold LITBUFFEREXTRASIZE; lia).
        replace (a_n a - LITBUFFEREXTRASIZE + 0) with (j + lo) by (unfold LITBUFFEREXTRASIZE; lia).
        replace (j + lo + (ll - lo)) with (j + ll) by lia.
        replace (k1 + (ll - lo + ml)) with (a_d a + K + ll + ml) by (unfold k1, k; lia). rewrite <- map_app. exact Hb1.
      * split; [rewrite Hrc; exact Hexr|].
        unfold lit_intact. rewrite Hl. intros; discriminate.
Qed.

Lemma lg_xstep_ok : XSTEP.
Proof.
  unfold XSTEP. intros a x ie K j sw c ll ml off Hok Hpend Hfx HXP.
  pose proof (xs_case_N a x ie K j sw c ll ml off Hok Hpend Hfx HXP) as HN.
  pose proof (xs_case_S a x ie K j sw c ll ml off Hok Hpend Hfx HXP) as HS.
  pose proof (xs_case_X1 a x ie K j sw c ll ml off Hok Hpend Hfx HXP) as HX.
  cbv zeta in HN, HS, HX |- *. exact (conj HN (conj HS HX)).
Qed.
