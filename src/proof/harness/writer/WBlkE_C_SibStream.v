(* Verbatim copy of the proved src/proof/harness/writer/model/WM_BlkStream.v (same statements and proofs; only its import of WM_BlkCodes points at the copy WBlkE_C_SibCodes),
   used by segment E's proofs in place of model.WM_BlkStream. *)
(* w_compressed_block, the sequences bitstream (plain Coq): the fields the C writes (seq_fields: per sequence from the
   last, the state
   updates and the extra bits; then the initial states), ended by the mark, decode
   (decode_seq_stream) to the sequences. *)
Require Import Zstd.proof.harness.writer.model.WM_BlkDefs.
Require Import Zstd.proof.harness.writer.model.WM_Bits.
Require Import Zstd.proof.harness.writer.model.WM_FseTab.
Require Import Zstd.proof.harness.writer.WBlkE_C_SibCodes.

(* ---- the number of bits of a list of fields ---- *)

Lemma wbs_snd_wl : forall fs W L, snd (fields_wl fs W L) = L + fold_right (fun f a => snd f + a) 0 fs.
Proof.
  induction fs as [| [v nb] fs IH]; intros; simpl; [lia | rewrite IH; lia].
Qed.

Lemma wbs_L_app : forall a b, fields_L (a ++ b) = fields_L a + fields_L b.
Proof.
  intros. unfold fields_L. rewrite !wbs_snd_wl.
  induction a as [| x a IH]; simpl; [lia |]. lia.
Qed.

Lemma wbs_L_cons : forall x l, fields_L (x :: l) = snd x + fields_L l.
Proof. intros. unfold fields_L. rewrite !wbs_snd_wl. simpl. lia. Qed.

Lemma wbs_L_nil : fields_L nil = 0.
Proof. reflexivity. Qed.

Lemma wbs_L_nonneg : forall fs, fields_ok fs -> 0 <= fields_L fs.
Proof.
  induction fs as [| x fs IH]; intros Hok; [reflexivity |].
  inversion Hok; subst. rewrite wbs_L_cons. specialize (IH H2). lia.
Qed.

(* ---- reading one field of a marked stream backwards ---- *)

Lemma wbs_rd_at : forall FS A v nb B pos,
  FS = A ++ (v, nb) :: B -> fields_ok FS -> pos = fields_L A + nb ->
  rd (fields_mark FS) pos nb = Some (v, fields_L A).
Proof.
  intros FS A v nb B pos HFS Hok Hpos.
  assert (HA: fields_ok A) by (subst; apply Forall_app in Hok; tauto).
  assert (HvB: fields_ok ((v, nb) :: B)) by (subst; apply Forall_app in Hok; tauto).
  inversion HvB as [| ? ? [Hnb Hv] HB]; subst x l. simpl in Hnb, Hv.
  pose proof (wbs_L_nonneg A HA) as HA0. pose proof (wbs_L_nonneg B HB) as HB0.
  assert (HL: fields_L FS = fields_L A + nb + fields_L B)
    by (rewrite HFS, wbs_L_app, wbs_L_cons; simpl; lia).
  destruct (fields_wl_range FS 0 0 Hok ltac:(lia) ltac:(simpl; lia)) as [_ HW].
  fold (fields_W FS) (fields_L FS) in HW.
  unfold rd. destruct (Z.ltb_spec (pos - nb) 0); [lia |].
  replace (pos - nb) with (fields_L A) by lia. f_equal. f_equal.
  unfold fields_mark. rewrite bs_peek_mark by lia.
  unfold bs_peek. subst pos.
  assert (E: 2 ^ (fields_L A + nb) = 2 ^ fields_L A * 2 ^ nb) by (apply Z.pow_add_r; lia).
  assert (0 < 2 ^ fields_L A) by (apply wmb_pow_pos; lia).
  assert (0 < 2 ^ nb) by (apply wmb_pow_pos; lia).
  rewrite E at 2. rewrite Z.div_mul_cancel_r by lia.
  rewrite <- (Z.mod_small (_ / 2 ^ fields_L A) (2 ^ nb)).
  2: { split; [apply Z.div_pos; [apply Z.mod_pos_bound; lia | lia] |].
       apply Z.div_lt_upper_bound; [lia |]. rewrite <- E. apply Z.mod_pos_bound; lia. }
  rewrite wmb_mod_div_mod by lia.
  rewrite HFS in *. apply fields_field. exact Hok.
Qed.

(* ---- the tables ---- *)

Lemma wbs_table : forall F, wf_ok F ->
  0 <= ft_log (wf_table F) <= 9 /\ (forall i, 0 <= i < 2 ^ ft_log (wf_table F) -> 0 <= fe_nb (fse_cell (wf_table F) i) <= 9).
Proof.
  intros F Hok. unfold wf_ok, wf_table in *. destruct (wf_log F =? 0).
  - simpl. split; [lia |]. intros i Hi. assert (i = 0) by lia. subst. simpl. lia.
  - destruct Hok as [Hnd _]. destruct (fse_build_cells _ _ Hnd) as [Hl [_ Hc]].
    pose proof Hnd as [Hlog _]. rewrite Hl. split; [lia |].
    intros i Hi. destruct (Hc i Hi) as [_ [_ [Hnb _]]]. lia.
Qed.

Lemma wbs_zn_map : forall (f: sequence -> Z) seqs i, 0 <= i < Zlength seqs ->
  zn (map f seqs) i = f (sqn seqs i).
Proof.
  intros f seqs i Hi. unfold zn, sqn. rewrite Zlength_correct in Hi.
  rewrite (nth_indep _ 0 (f seq0)) by (rewrite length_map; lia). apply map_nth.
Qed.

Lemma wbs_sqn_ok : forall seqs i, Forall seq_ok seqs -> 0 <= i < Zlength seqs -> seq_ok (sqn seqs i).
Proof.
  intros seqs i H Hi. rewrite Forall_forall in H. apply H. unfold sqn. apply nth_In.
  rewrite Zlength_correct in Hi. lia.
Qed.

(* the facts of one chain *)
Lemma wbs_chain : forall F ty seqs s, wf_ok F -> 0 <= ty <= 2 ->
  fse_chain (wf_table F) (map (sq_code ty) seqs) s ->
  forall i, 0 <= i < Zlength seqs ->
    0 <= zn s i < 2 ^ ft_log (wf_table F) /\ 
    fe_sym (fse_cell (wf_table F) (zn s i)) = sq_code ty (sqn seqs i) /\ 
    0 <= fe_nb (fse_cell (wf_table F) (zn s i)) <= 9 /\ 
    (i + 1 < Zlength seqs ->
     0 <= fst (fse_upd_field (wf_table F) s i) < 2 ^ snd (fse_upd_field (wf_table F) s i)).
Proof.
  intros F ty seqs s Hok Hty [Hlen [H2 H3]] i Hi.
  assert (Hzm: Zlength (map (sq_code ty) seqs) = Zlength seqs)
    by (rewrite !Zlength_correct, length_map; reflexivity).
  rewrite Hzm in *. destruct (H2 i Hi) as [Hs Hsym].
  rewrite wbs_zn_map in Hsym by lia.
  destruct (wbs_table F Hok) as [_ Hnb]. specialize (Hnb _ Hs).
  split; [lia | split; [exact Hsym | split; [lia |]]].
  intros Hi1. specialize (H3 i ltac:(lia)). unfold fse_upd_field. simpl. lia.
Qed.

Lemma wbs_flat_S : forall {A} (f: nat -> list A) m,
  flat_map f (seq 0 (S m)) = flat_map f (seq 0 m) ++ f m.
Proof.
  intros. rewrite seq_S, flat_map_app. simpl. rewrite app_nil_r. reflexivity.
Qed.

Lemma wbs_flat_prefix : forall {A} (f: nat -> list A) m p,
  flat_map f (seq 0 (m + p)) = flat_map f (seq 0 m) ++ flat_map f (seq m p).
Proof.
  intros. rewrite seq_app, flat_map_app. reflexivity.
Qed.

Lemma wbs_skipn : forall {A} (l: list A) i d, (i < length l)%nat ->
  skipn i l = nth i l d :: skipn (S i) l.
Proof.
  induction l as [| x l IH]; intros i d Hi; simpl in Hi; [lia |].
  destruct i as [| i]; [reflexivity |]. simpl. apply IH. lia.
Qed.

(* the fields of the sequences n-1 down to n-m *)
Definition wbs_f T0 T1 T2 s0 s1 s2 seqs (j: nat) : list (Z * Z) :=
  seq_fields_at T0 T1 T2 s0 s1 s2 seqs (Zlength seqs - 1 - Z.of_nat j).
Definition wbs_G T0 T1 T2 s0 s1 s2 seqs (m: nat) : list (Z * Z) :=
  flat_map (wbs_f T0 T1 T2 s0 s1 s2 seqs) (seq 0 m).

Lemma wbs_G_S : forall T0 T1 T2 s0 s1 s2 seqs m,
  wbs_G T0 T1 T2 s0 s1 s2 seqs (S m) =
  wbs_G T0 T1 T2 s0 s1 s2 seqs m ++ wbs_f T0 T1 T2 s0 s1 s2 seqs m.
Proof. intros. apply wbs_flat_S. Qed.

Lemma wbs_G_pre : forall T0 T1 T2 s0 s1 s2 seqs m p, exists R,
  wbs_G T0 T1 T2 s0 s1 s2 seqs (m + p) = wbs_G T0 T1 T2 s0 s1 s2 seqs m ++ R.
Proof. intros. eexists. apply wbs_flat_prefix. Qed.

Lemma wbs_eta : forall sq, {| sq_ll := sq_ll sq; sq_ml := sq_ml sq; sq_ov := sq_ov sq |} = sq.
Proof. destruct sq; reflexivity. Qed.

Ltac wbs_pos := rewrite ?wbs_L_app, ?wbs_L_cons, ?wbs_L_nil; try unfold fse_upd_field; cbn [fst snd]; lia.

Ltac wbs_rd FS A v nb B HFS Hok :=
  erewrite (wbs_rd_at FS A v nb B);
  [ | rewrite HFS; rewrite <- ?app_assoc; reflexivity | exact Hok | wbs_pos ];
  cbv beta iota zeta.

Lemma wbs_decode_seqs : forall F0 F1 F2 s0 s1 s2 seqs FS R,
  wf_ok F0 -> wf_ok F1 -> wf_ok F2 -> Forall seq_ok seqs ->
  fse_chain (wf_table F0) (map (sq_code 0) seqs) s0 ->
  fse_chain (wf_table F1) (map (sq_code 1) seqs) s1 ->
  fse_chain (wf_table F2) (map (sq_code 2) seqs) s2 ->
  fields_ok FS ->
  FS = wbs_G (wf_table F0) (wf_table F1) (wf_table F2) s0 s1 s2 seqs (length seqs) ++ R ->
  forall m, (m <= length seqs)%nat ->
  decode_seqs (wf_table F0) (wf_table F1) (wf_table F2) (fields_mark FS) m
    (zn s0 (Z.of_nat (length seqs - m))) (zn s1 (Z.of_nat (length seqs - m)))
    (zn s2 (Z.of_nat (length seqs - m)))
    (fields_L (wbs_G (wf_table F0) (wf_table F1) (wf_table F2) s0 s1 s2 seqs m)) =
  Some (skipn (length seqs - m) seqs, 0).
Proof.
  intros F0 F1 F2 s0 s1 s2 seqs FS R Hw0 Hw1 Hw2 Hseqs Hc0 Hc1 Hc2 Hok HFS.
  assert (HnZ : Zlength seqs = Z.of_nat (length seqs)) by apply Zlength_correct.
  induction m as [| m IH]; intros Hm.
  - cbn [decode_seqs]. rewrite Nat.sub_0_r, skipn_all. reflexivity.
  - remember (Z.of_nat (length seqs - S m)) as k eqn:Hkd.
    assert (Hk: 0 <= k < Zlength seqs) by lia.
    assert (Ek: Zlength seqs - 1 - Z.of_nat m = k) by lia.
    pose proof (wbs_sqn_ok seqs k Hseqs Hk) as Hsq.
    destruct (sq_rebuild _ Hsq) as [Rb0 [Rb2 [Rb1 [Rbn0 [Rbn2 Rbn1]]]]].
    destruct (wbs_chain F0 0 seqs s0 Hw0 ltac:(lia) Hc0 k Hk) as [Ca0 [Cb0 [Cc0 Cd0]]].
    destruct (wbs_chain F1 1 seqs s1 Hw1 ltac:(lia) Hc1 k Hk) as [Ca1 [Cb1 [Cc1 Cd1]]].
    destruct (wbs_chain F2 2 seqs s2 Hw2 ltac:(lia) Hc2 k Hk) as [Ca2 [Cb2 [Cc2 Cd2]]].
    destruct (wbs_G_pre (wf_table F0) (wf_table F1) (wf_table F2) s0 s1 s2 seqs (S m) (length seqs - S m))
      as [R1 HR1].
    replace (S m + (length seqs - S m))%nat with (length seqs) in HR1 by lia.
    rewrite HR1, wbs_G_S in HFS. clear HR1.
    rewrite wbs_G_S. unfold wbs_f in *. rewrite Ek in *. unfold seq_fields_at, seq_ex_fields in *.
    cbn [decode_seqs].
    rewrite Cb0, Cb1, Cb2, Rbn0, Rbn2, Rbn1.
    set (G := wbs_G (wf_table F0) (wf_table F1) (wf_table F2) s0 s1 s2 seqs) in *.
    set (U := if k + 1 <? Zlength seqs then _ else _) in *.
    set (sq := sqn seqs k) in *.
    wbs_rd FS (G m ++ U ++ [(sq_extra 0 sq, sq_nbits 0 sq); (sq_extra 2 sq, sq_nbits 2 sq)])
      (sq_extra 1 sq) (sq_nbits 1 sq) (R1 ++ R) HFS Hok.
    wbs_rd FS (G m ++ U ++ [(sq_extra 0 sq, sq_nbits 0 sq)])
      (sq_extra 2 sq) (sq_nbits 2 sq) ((sq_extra 1 sq, sq_nbits 1 sq) :: R1 ++ R) HFS Hok.
    wbs_rd FS (G m ++ U)
      (sq_extra 0 sq) (sq_nbits 0 sq) ((sq_extra 2 sq, sq_nbits 2 sq) :: (sq_extra 1 sq, sq_nbits 1 sq) :: R1 ++ R)
      HFS Hok.
    rewrite Rb0, Rb2, <- Rbn1, Rb1, wbs_eta.
    destruct m as [| m].
    + assert (HU: U = []) by (subst U; destruct (Z.ltb_spec (k + 1) (Zlength seqs)); [lia | reflexivity]).
      rewrite HU. change (fields_L (G 0%nat ++ [])) with 0.
      rewrite (wbs_skipn seqs (length seqs - 1) seq0) by lia.
      replace (S (length seqs - 1)) with (length seqs) by lia. rewrite skipn_all.
      unfold sq, sqn. replace (Z.to_nat k) with (length seqs - 1)%nat by lia. reflexivity.
    + assert (HU: U = [fse_upd_field (wf_table F1) s1 k; fse_upd_field (wf_table F2) s2 k;
                       fse_upd_field (wf_table F0) s0 k])
        by (subst U; destruct (Z.ltb_spec (k + 1) (Zlength seqs)); [reflexivity | lia]).
      clearbody U. subst U.
      wbs_rd FS (G (S m) ++ [fse_upd_field (wf_table F1) s1 k; fse_upd_field (wf_table F2) s2 k])
        (zn s0 (k + 1) - fe_base (fse_cell (wf_table F0) (zn s0 k))) (fe_nb (fse_cell (wf_table F0) (zn s0 k)))
        ([(sq_extra 0 sq, sq_nbits 0 sq); (sq_extra 2 sq, sq_nbits 2 sq); (sq_extra 1 sq, sq_nbits 1 sq)] ++ R1 ++ R)
        HFS Hok.
      wbs_rd FS (G (S m) ++ [fse_upd_field (wf_table F1) s1 k])
        (zn s2 (k + 1) - fe_base (fse_cell (wf_table F2) (zn s2 k))) (fe_nb (fse_cell (wf_table F2) (zn s2 k)))
        (fse_upd_field (wf_table F0) s0 k ::
         [(sq_extra 0 sq, sq_nbits 0 sq); (sq_extra 2 sq, sq_nbits 2 sq); (sq_extra 1 sq, sq_nbits 1 sq)] ++ R1 ++ R)
        HFS Hok.
      wbs_rd FS (G (S m))
        (zn s1 (k + 1) - fe_base (fse_cell (wf_table F1) (zn s1 k))) (fe_nb (fse_cell (wf_table F1) (zn s1 k)))
        (fse_upd_field (wf_table F2) s2 k :: fse_upd_field (wf_table F0) s0 k ::
         [(sq_extra 0 sq, sq_nbits 0 sq); (sq_extra 2 sq, sq_nbits 2 sq); (sq_extra 1 sq, sq_nbits 1 sq)] ++ R1 ++ R)
        HFS Hok.
      assert (Ek1: Z.of_nat (length seqs - S m) = k + 1) by lia. rewrite Ek1 in IH.
      replace (fe_base (fse_cell (wf_table F0) (zn s0 k)) + (zn s0 (k + 1) - fe_base (fse_cell (wf_table F0) (zn s0 k))))
        with (zn s0 (k + 1)) by lia.
      replace (fe_base (fse_cell (wf_table F1) (zn s1 k)) + (zn s1 (k + 1) - fe_base (fse_cell (wf_table F1) (zn s1 k))))
        with (zn s1 (k + 1)) by lia.
      replace (fe_base (fse_cell (wf_table F2) (zn s2 k)) + (zn s2 (k + 1) - fe_base (fse_cell (wf_table F2) (zn s2 k))))
        with (zn s2 (k + 1)) by lia.
      rewrite IH by lia. cbv beta iota zeta.
      rewrite (wbs_skipn seqs (length seqs - S (S m)) seq0) by lia.
      replace (S (length seqs - S (S m))) with (length seqs - S m)%nat by lia.
      unfold sq, sqn. replace (Z.to_nat k) with (length seqs - S (S m))%nat by lia. reflexivity.
Qed.

Theorem seq_stream_ok : forall F0 F1 F2 s0 s1 s2 seqs,
  wf_ok F0 -> wf_ok F1 -> wf_ok F2 -> 1 <= Zlength seqs -> Forall seq_ok seqs ->
  fse_chain (wf_table F0) (map (sq_code 0) seqs) s0 ->
  fse_chain (wf_table F1) (map (sq_code 1) seqs) s1 ->
  fse_chain (wf_table F2) (map (sq_code 2) seqs) s2 ->
  fields_ok (seq_fields (wf_table F0) (wf_table F1) (wf_table F2) s0 s1 s2 seqs) /\
  decode_seq_stream (wf_table F0) (wf_table F1) (wf_table F2)
    (fields_mark (seq_fields (wf_table F0) (wf_table F1) (wf_table F2) s0 s1 s2 seqs)) (Zlength seqs) =
  Some seqs.
Proof.
  intros F0 F1 F2 s0 s1 s2 seqs Hw0 Hw1 Hw2 Hn Hseqs Hc0 Hc1 Hc2.
  set (FS := seq_fields (wf_table F0) (wf_table F1) (wf_table F2) s0 s1 s2 seqs).
  set (G := wbs_G (wf_table F0) (wf_table F1) (wf_table F2) s0 s1 s2 seqs).
  assert (HFS: FS = G (length seqs) ++
    [(zn s2 0, ft_log (wf_table F2)); (zn s1 0, ft_log (wf_table F1)); (zn s0 0, ft_log (wf_table F0))])
    by reflexivity.
  assert (HnZ : Zlength seqs = Z.of_nat (length seqs)) by apply Zlength_correct.
  destruct (wbs_table F0 Hw0) as [Tl0 _]. destruct (wbs_table F1 Hw1) as [Tl1 _].
  destruct (wbs_table F2 Hw2) as [Tl2 _].
  assert (Hok: fields_ok FS).
  { rewrite HFS. apply Forall_app. split.
    - apply Forall_forall. intros x Hx. unfold G, wbs_G in Hx. apply in_flat_map in Hx.
      destruct Hx as [j [Hj Hx]]. apply in_seq in Hj. unfold wbs_f, seq_fields_at, seq_ex_fields in Hx.
      assert (Hq: 0 <= Zlength seqs - 1 - Z.of_nat j < Zlength seqs) by lia.
      revert Hx. generalize dependent (Zlength seqs - 1 - Z.of_nat j). intros q Hq Hx.
      pose proof (wbs_sqn_ok seqs q Hseqs Hq) as Hsq.
      destruct (sq_code_facts 0 _ Hsq ltac:(lia)) as [_ [X0 Y0]].
      destruct (sq_code_facts 1 _ Hsq ltac:(lia)) as [_ [X1 Y1]].
      destruct (sq_code_facts 2 _ Hsq ltac:(lia)) as [_ [X2 Y2]].
      destruct (wbs_chain F0 0 seqs s0 Hw0 ltac:(lia) Hc0 q Hq) as [_ [_ [Cc0 Cd0]]].
      destruct (wbs_chain F1 1 seqs s1 Hw1 ltac:(lia) Hc1 q Hq) as [_ [_ [Cc1 Cd1]]].
      destruct (wbs_chain F2 2 seqs s2 Hw2 ltac:(lia) Hc2 q Hq) as [_ [_ [Cc2 Cd2]]].
      apply in_app_or in Hx. destruct Hx as [Hx | Hx].
      + destruct (Z.ltb_spec (q + 1) (Zlength seqs)) as [Hq1 | Hq1]; [| contradiction].
        specialize (Cd0 Hq1). specialize (Cd1 Hq1). specialize (Cd2 Hq1).
        destruct Hx as [<- | [<- | [<- | []]]]; (split; [unfold fse_upd_field; cbn [snd]; lia | assumption]).
      + destruct Hx as [<- | [<- | [<- | []]]]; cbn [fst snd]; lia.
    - assert (H0: 0 <= 0 < Zlength seqs) by lia.
      destruct (wbs_chain F0 0 seqs s0 Hw0 ltac:(lia) Hc0 0 H0) as [Ca0 _].
      destruct (wbs_chain F1 1 seqs s1 Hw1 ltac:(lia) Hc1 0 H0) as [Ca1 _].
      destruct (wbs_chain F2 2 seqs s2 Hw2 ltac:(lia) Hc2 0 H0) as [Ca2 _].
      repeat constructor; cbn [fst snd]; lia. }
  split; [exact Hok |].
  destruct (fields_wl_range FS 0 0 Hok ltac:(lia) ltac:(simpl; lia)) as [HL HW].
  destruct (bw_mark_stream (fields_W FS) (fields_L FS) HL HW) as [Hbs Htot].
  change (bw_mark (fields_W FS) (fields_L FS)) with (fields_mark FS) in Hbs, Htot.
  rewrite HFS in Htot at 2.
  unfold decode_seq_stream. rewrite Hbs, Htot. cbn [negb].
  wbs_rd FS (G (length seqs) ++ [(zn s2 0, ft_log (wf_table F2)); (zn s1 0, ft_log (wf_table F1))])
    (zn s0 0) (ft_log (wf_table F0)) (@nil (Z * Z)) HFS Hok.
  wbs_rd FS (G (length seqs) ++ [(zn s2 0, ft_log (wf_table F2))])
    (zn s1 0) (ft_log (wf_table F1)) [(zn s0 0, ft_log (wf_table F0))] HFS Hok.
  wbs_rd FS (G (length seqs))
    (zn s2 0) (ft_log (wf_table F2)) [(zn s1 0, ft_log (wf_table F1)); (zn s0 0, ft_log (wf_table F0))] HFS Hok.
  pose proof (wbs_decode_seqs F0 F1 F2 s0 s1 s2 seqs FS _ Hw0 Hw1 Hw2 Hseqs Hc0 Hc1 Hc2 Hok HFS
    (length seqs) (le_n _)) as D.
  rewrite Nat.sub_diag in D. change (Z.of_nat 0) with 0 in D.
  rewrite HnZ, Nat2Z.id. fold G in D. rewrite D. reflexivity.
Qed.
