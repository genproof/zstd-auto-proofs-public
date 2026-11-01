(* Plain-Coq facts for phase B of segment E of w_compressed_block (the sequences bitstream): the fields put so far by
   the while loop over q (ebq_pre: sequences n-1 down to q),
   their inclusion in seq_fields (so fields_ok of seq_stream_ok bounds each of them), the table facts. *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.harness.writer.model.WM_BlkDefs.
Require Import Zstd.proof.harness.writer.model.WM_FseTab.
Require Import Zstd.proof.harness.writer.model.WM_Bits.
Require Import Zstd.proof.harness.writer.WBlkEB_Codes.

(* the table of a writer fse_t: its log, and the cells' ranges *)
Lemma ebq_tab : forall F, wf_ok F ->
  ft_log (wf_table F) = wf_log F /\ 0 <= wf_log F <= 9 /\
  forall i, 0 <= i < 2 ^ wf_log F ->
    0 <= fe_sym (fse_cell (wf_table F) i) < 256 /\
    0 <= fe_nb (fse_cell (wf_table F) i) <= wf_log F /\ 0 <= fe_base (fse_cell (wf_table F) i) /\
    fe_base (fse_cell (wf_table F) i) + 2 ^ fe_nb (fse_cell (wf_table F) i) <= 2 ^ wf_log F.
Proof.
  intros F Hok. unfold wf_ok, wf_table in *. destruct (wf_log F =? 0) eqn:E.
  - apply Z.eqb_eq in E. rewrite E. split; [reflexivity|]. split; [lia|].
    intros i Hi. simpl in Hi. assert (i = 0) by lia. subst i. unfold fse_cell, fse_rle; simpl. lia.
  - destruct Hok as [Hnd Hn]. destruct (fse_build_cells _ _ Hnd) as [H1 [_ H3]].
    pose proof Hnd as [Hl [Hlen _]]. split; [auto|]. split; [lia|].
    intros i Hi. specialize (H3 i Hi). cbv zeta in H3. lia.
Qed.

Section Pre.
Variables (T0 T1 T2: fse_table) (s0 s1 s2: list Z) (seqs: list sequence).

Definition ebq_f (j: nat) : list (Z * Z) :=
  seq_fields_at T0 T1 T2 s0 s1 s2 seqs (Zlength seqs - 1 - Z.of_nat j).

(* the fields of the sequences n-1 down to q *)
Definition ebq_pre (q: Z) : list (Z * Z) := flat_map ebq_f (seq 0 (Z.to_nat (Zlength seqs - q))).

Definition ebq_upds (q: Z) : list (Z * Z) :=
  [fse_upd_field T1 s1 q; fse_upd_field T2 s2 q; fse_upd_field T0 s0 q].

Definition ebq_inits : list (Z * Z) :=
  [(zn s2 0, ft_log T2); (zn s1 0, ft_log T1); (zn s0 0, ft_log T0)].

Lemma ebq_pre_n : ebq_pre (Zlength seqs) = [].
Proof. unfold ebq_pre. rewrite Z.sub_diag. reflexivity. Qed.

Lemma ebq_pre_step : forall q, 0 <= q < Zlength seqs ->
  ebq_pre q = ebq_pre (q + 1) ++ seq_fields_at T0 T1 T2 s0 s1 s2 seqs q.
Proof.
  intros q Hq. unfold ebq_pre.
  replace (Z.to_nat (Zlength seqs - q)) with (S (Z.to_nat (Zlength seqs - (q + 1)))) by lia.
  rewrite seq_S, flat_map_app. simpl. rewrite app_nil_r. f_equal.
  unfold ebq_f. f_equal. lia.
Qed.

Lemma ebq_fields_eq : seq_fields T0 T1 T2 s0 s1 s2 seqs = ebq_pre 0 ++ ebq_inits.
Proof.
  unfold seq_fields, ebq_pre, ebq_inits, ebq_f. rewrite Z.sub_0_r, Zlength_correct, Nat2Z.id. reflexivity.
Qed.

Lemma ebq_at_eq : forall q,
  seq_fields_at T0 T1 T2 s0 s1 s2 seqs q =
  (if q + 1 <? Zlength seqs then ebq_upds q else []) ++ seq_ex_fields (sqn seqs q).
Proof. reflexivity. Qed.

Lemma ebq_at_incl : forall q, 0 <= q < Zlength seqs ->
  incl (seq_fields_at T0 T1 T2 s0 s1 s2 seqs q) (seq_fields T0 T1 T2 s0 s1 s2 seqs).
Proof.
  intros q Hq x Hx. rewrite ebq_fields_eq. apply in_or_app. left. unfold ebq_pre.
  apply in_flat_map. exists (Z.to_nat (Zlength seqs - 1 - q)). split.
  - apply in_seq. lia.
  - unfold ebq_f. replace (Zlength seqs - 1 - Z.of_nat (Z.to_nat (Zlength seqs - 1 - q))) with q by lia. exact Hx.
Qed.

Lemma ebq_pre_incl : forall q, 0 <= q ->
  incl (ebq_pre q) (seq_fields T0 T1 T2 s0 s1 s2 seqs).
Proof.
  intros q Hq x Hx. rewrite ebq_fields_eq. apply in_or_app. left. unfold ebq_pre in *.
  apply in_flat_map in Hx. destruct Hx as [j [Hj Hx]]. apply in_flat_map. exists j. split; [| exact Hx].
  apply in_seq in Hj. apply in_seq. lia.
Qed.

Lemma ebq_inits_incl : incl ebq_inits (seq_fields T0 T1 T2 s0 s1 s2 seqs).
Proof. intros x Hx. rewrite ebq_fields_eq. apply in_or_app. right. exact Hx. Qed.

Lemma ebq_at_len : forall q, Zlength (seq_fields_at T0 T1 T2 s0 s1 s2 seqs q) =
  (if q + 1 <? Zlength seqs then 3 else 0) + 3.
Proof. intros. unfold seq_fields_at. destruct (q + 1 <? Zlength seqs); reflexivity. Qed.

End Pre.

(* the fields put so far in the iteration of sequence q: a prefix of seq_fields_at q *)
Lemma ebq_snoc_nat : forall {A} (l: list A) n d, (n < length l)%nat ->
  firstn (S n) l = firstn n l ++ [nth n l d].
Proof.
  intros A l. induction l as [| a l IH]; intros n d Hn; simpl in Hn; [lia |].
  destruct n as [| n]; [reflexivity |].
  change (firstn (S (S n)) (a :: l)) with (a :: firstn (S n) l). rewrite (IH n d) by lia. reflexivity.
Qed.

Lemma ebq_snoc : forall (l: list (Z * Z)) j, 0 <= j < Zlength l ->
  firstn (Z.to_nat (j + 1)) l = firstn (Z.to_nat j) l ++ [Znth j l].
Proof.
  intros l j Hj. rewrite Z2Nat.inj_add, Nat.add_1_r by lia. rewrite Zlength_correct in Hj.
  rewrite (ebq_snoc_nat l (Z.to_nat j) (0, 0)) by lia. f_equal. f_equal.
  unfold Znth. destruct (Z_lt_dec j 0); [lia | reflexivity].
Qed.


Lemma ebq_ok_incl : forall fs fs', fields_ok fs -> incl fs' fs -> fields_ok fs'.
Proof.
  intros fs fs' Hok Hi. unfold fields_ok in *. rewrite Forall_forall in *. intros x Hx. apply Hok, Hi, Hx.
Qed.

Lemma ebq_done_ok : forall T0 T1 T2 s0 s1 s2 seqs q j,
  fields_ok (seq_fields T0 T1 T2 s0 s1 s2 seqs) -> 0 <= q < Zlength seqs ->
  fields_ok (ebq_pre T0 T1 T2 s0 s1 s2 seqs (q + 1) ++ firstn j (seq_fields_at T0 T1 T2 s0 s1 s2 seqs q)).
Proof.
  intros. apply (ebq_ok_incl _ _ H). intros x Hx. apply in_app_or in Hx as [Hx | Hx].
  - apply (ebq_pre_incl T0 T1 T2 s0 s1 s2 seqs (q + 1)); [lia | exact Hx].
  - apply (ebq_at_incl T0 T1 T2 s0 s1 s2 seqs q); [lia |].
    rewrite <- (firstn_skipn j (seq_fields_at T0 T1 T2 s0 s1 s2 seqs q)). apply in_or_app. left. exact Hx.
Qed.

Lemma ebq_ok_app : forall a b, fields_ok a -> fields_ok b -> fields_ok (a ++ b).
Proof. intros. unfold fields_ok in *. apply Forall_app. auto. Qed.

Lemma ebq_ok_field : forall fs v nb, fields_ok fs -> In (v, nb) fs -> 0 <= nb <= 32 /\ 0 <= v < 2 ^ nb.
Proof. intros fs v nb Hok Hin. unfold fields_ok in Hok. rewrite Forall_forall in Hok. apply (Hok _ Hin). Qed.

(* one more field *)
Lemma ebq_wl_snoc : forall d v nb W L, fields_wl d 0 0 = (W, L) ->
  fields_wl (d ++ [(v, nb)]) 0 0 = (W + v * 2 ^ L, L + nb).
Proof. intros. rewrite fields_wl_app, H. reflexivity. Qed.

Lemma ebq_put_step : forall P l j v nb W L, fields_wl (P ++ firstn (Z.to_nat j) l) 0 0 = (W, L) ->
  0 <= j < Zlength l -> Znth j l = (v, nb) ->
  fields_wl (P ++ firstn (Z.to_nat (j + 1)) l) 0 0 = (W + v * 2 ^ L, L + nb).
Proof.
  intros. rewrite ebq_snoc by auto. rewrite H1, app_assoc. apply ebq_wl_snoc. exact H.
Qed.

Lemma ebq_wl_range : forall d W L, fields_ok d -> fields_wl d 0 0 = (W, L) -> 0 <= L /\ 0 <= W < 2 ^ L.
Proof.
  intros d W L Hok Hd. destruct (fields_wl_range d 0 0 Hok ltac:(lia) ltac:(simpl; lia)) as [A B].
  rewrite Hd in A, B. simpl in A, B. lia.
Qed.

(* zn and Znth *)
Lemma ebq_zn : forall l i, 0 <= i -> zn l i = Znth i l.
Proof.
  intros. unfold zn, Znth. destruct (Z_lt_dec i 0); [lia | reflexivity].
Qed.

Lemma ebq_Znth_d : forall {A} (d1 d2: Inhabitant A) (l: list A) i, 0 <= i < Zlength l ->
  @Znth A d1 i l = @Znth A d2 i l.
Proof.
  intros. unfold Znth. destruct (Z_lt_dec i 0); [lia|]. apply nth_indep. rewrite Zlength_correct in H. lia.
Qed.

(* ---------- separation-logic helpers ---------- *)
Local Open Scope logic.

(* the unwritten tail of an out_t stays undefined *)
Definition ebq_undef (tl: list val) : Prop := Forall (fun x => x = Vundef) tl.

Lemma ebq_undef_Zrepeat : forall m, ebq_undef (Zrepeat Vundef m).
Proof.
  intros. unfold ebq_undef. apply Forall_forall. intros x Hx.
  unfold Zrepeat in Hx. apply repeat_spec in Hx. exact Hx.
Qed.

Lemma ebq_undef_sublist : forall a b tl, ebq_undef tl -> ebq_undef (sublist a b tl).
Proof. intros. unfold ebq_undef in *. apply Forall_sublist. exact H. Qed.

Lemma ebq_undef_eq : forall tl, ebq_undef tl -> tl = Zrepeat Vundef (Zlength tl).
Proof.
  induction tl; intros HF; [reflexivity |]. inversion HF; subst.
  specialize (IHtl H2). unfold Zrepeat in *. rewrite Zlength_cons, Z2Nat.inj_succ by apply Zlength_nonneg.
  cbn [repeat]. f_equal. exact IHtl.
Qed.

(* element k of an array, borrowed with the rest as a hole (any Inhabitant d: never default_val of a big type,
   simpl would compute it) *)
Lemma ebq_split : forall {cs: compspecs} sh t n (d: Inhabitant (reptype t)) (al: list (reptype t)) p k,
  0 <= k < n -> Zlength al = n -> field_compatible (tarray t n) nil p ->
  data_at sh (tarray t n) al p =
  data_at sh t (@Znth (reptype t) d k al) (offset_val (sizeof t * k) p) *
  array_with_hole sh t k (k + 1) n al p.
Proof.
  intros. rewrite (wand_slice_array k (k + 1) n sh t al p) by lia.
  rewrite prop_true_andp by auto. rewrite arr_field_address0 by (auto; lia).
  replace (k + 1 - k) with 1 by lia.
  rewrite (data_at_singleton_array_eq sh t (@Znth (reptype t) d k al)); [reflexivity |].
  rewrite (@sublist_len_1 _ d) by lia. reflexivity.
Qed.

(* read-only borrows: one element / one cell of a 2-D array, the whole back by modus ponens (loads from a
   data_at of a 65536-element array overflow the stack) *)
Lemma ebq_borrow : forall {cs: compspecs} sh t n (d: Inhabitant (reptype t)) (al: list (reptype t)) p k,
  0 <= k < n -> Zlength al = n ->
  data_at sh (tarray t n) al p |--
  data_at sh t (@Znth (reptype t) d k al) (offset_val (sizeof t * k) p) *
  (data_at sh t (@Znth (reptype t) d k al) (offset_val (sizeof t * k) p) -* data_at sh (tarray t n) al p).
Proof.
  intros. eapply derives_trans; [apply (andp_right _ _ _ (data_at_local_facts sh (tarray t n) al p) (derives_refl _)) |].
  apply derives_extract_prop. intros [Hfc _].
  rewrite (ebq_split sh t n d al p k) by auto.
  apply sepcon_derives; [apply derives_refl |].
  apply wand_sepcon_adjoint. rewrite sepcon_comm. rewrite <- (ebq_split sh t n d al p k) by auto. apply derives_refl.
Qed.

Lemma ebq_borrow2 : forall {cs: compspecs} sh t m n (d1: Inhabitant (reptype (tarray t m))) (d2: Inhabitant (reptype t))
    (al: list (reptype (tarray t m))) p k i,
  0 <= k < n -> 0 <= i < m -> Zlength al = n -> Zlength (@Znth _ d1 k al) = m ->
  data_at sh (tarray (tarray t m) n) al p |--
  data_at sh t (@Znth (reptype t) d2 i (@Znth _ d1 k al)) (offset_val (sizeof t * i) (offset_val (sizeof (tarray t m) * k) p)) *
  (data_at sh t (@Znth (reptype t) d2 i (@Znth _ d1 k al)) (offset_val (sizeof t * i) (offset_val (sizeof (tarray t m) * k) p))
     -* data_at sh (tarray (tarray t m) n) al p).
Proof.
  intros. eapply derives_trans; [apply (ebq_borrow sh (tarray t m) n d1 al p k); auto |].
  eapply derives_trans; [apply sepcon_derives; [apply (ebq_borrow sh t m d2 (@Znth _ d1 k al) _ i); auto | apply derives_refl] |].
  rewrite sepcon_assoc. apply sepcon_derives; [apply derives_refl |].
  apply wand_sepcon_adjoint.
  set (C := data_at sh t _ _). set (Rw := data_at sh (tarray t m) _ _). set (Wh := data_at sh (tarray (tarray t m) n) al p).
  apply -> wand_sepcon_adjoint. apply -> wand_sepcon_adjoint.
  rewrite (sepcon_comm (C -* Rw)), sepcon_assoc.
  eapply derives_trans; [apply sepcon_derives; [apply derives_refl | rewrite sepcon_comm; apply modus_ponens_wand] |].
  rewrite sepcon_comm. apply modus_ponens_wand.
Qed.

Lemma ebq_Znth_map_sqn : forall {B} (d: Inhabitant B) (g: sequence -> B) seqs i, 0 <= i < Zlength seqs ->
  @Znth B d i (map g seqs) = g (sqn seqs i).
Proof.
  intros. unfold Znth, sqn. destruct (Z_lt_dec i 0); [lia |].
  rewrite nth_indep with (d' := g seq0) by (rewrite map_length; rewrite Zlength_correct in H; lia).
  apply map_nth.
Qed.

Lemma ebq_borrow2v : forall {cs: compspecs} sh t m n (d1: Inhabitant (reptype (tarray t m))) (d2: Inhabitant (reptype t))
    (al: list (reptype (tarray t m))) p k i v,
  0 <= k < n -> 0 <= i < m -> Zlength al = n -> Zlength (@Znth _ d1 k al) = m ->
  @Znth (reptype t) d2 i (@Znth _ d1 k al) = v ->
  data_at sh (tarray (tarray t m) n) al p |--
  data_at sh t v (offset_val (sizeof t * i) (offset_val (sizeof (tarray t m) * k) p)) *
  (data_at sh t v (offset_val (sizeof t * i) (offset_val (sizeof (tarray t m) * k) p))
     -* data_at sh (tarray (tarray t m) n) al p).
Proof. intros. subst v. apply ebq_borrow2; auto. Qed.

(* the address of a[k][i] in a 2-D array at p *)
Lemma ebq_cell2_eq : forall {cs: compspecs} t m p k (x: int64) i, isptr p ->
  complete_type cenv_cs t = true -> complete_type cenv_cs (tarray t m) = true ->
  Int.min_signed <= k <= Int.max_signed -> Int64.unsigned x = i ->
  field_compatible t [] (offset_val (sizeof t * i) (offset_val (sizeof (tarray t m) * k) p)) ->
  force_val (sem_add_ptr_long t (force_val (sem_add_ptr_int (tarray t m) Signed p (Vint (Int.repr k)))) (Vlong x)) =
  field_address t [] (offset_val (sizeof t * i) (offset_val (sizeof (tarray t m) * k) p)).
Proof.
  intros. rewrite sem_add_pi_ptr_special by auto. simpl force_val.
  rewrite <- (Int64.repr_unsigned x), H3. rewrite sem_add_pl_ptr_special by (auto; destruct p; try contradiction; exact I).
  simpl force_val. rewrite field_address_offset by auto. simpl nested_field_offset.
  rewrite isptr_offset_val_zero; [reflexivity |]. destruct p; try contradiction; exact I.
Qed.

(* ---------- every field of the bitstream is one bits_put accepts ---------- *)
Lemma ebq_upd_ok : forall F cs s q, wf_ok F -> fse_chain (wf_table F) cs s -> 0 <= q -> q + 1 < Zlength cs ->
  0 <= snd (fse_upd_field (wf_table F) s q) <= 32 /\
  0 <= fst (fse_upd_field (wf_table F) s q) < 2 ^ snd (fse_upd_field (wf_table F) s q).
Proof.
  intros F cs s q Hw (Hl & H2 & H3) Hq Hq1. unfold fse_upd_field; simpl.
  destruct (ebq_tab F Hw) as (Hft & Hlg & Hc).
  destruct (H2 q ltac:(lia)) as [Hs _]. rewrite Hft in Hs.
  destruct (Hc _ Hs) as (_ & Hnb & _ & _).
  destruct (H3 q ltac:(lia)) as [A B]. lia.
Qed.

Lemma ebq_init_ok : forall F cs s, wf_ok F -> fse_chain (wf_table F) cs s -> 1 <= Zlength cs ->
  0 <= ft_log (wf_table F) <= 32 /\ 0 <= zn s 0 < 2 ^ ft_log (wf_table F).
Proof.
  intros F cs s Hw (Hl & H2 & H3) Hn. destruct (ebq_tab F Hw) as (Hft & Hlg & Hc).
  destruct (H2 0 ltac:(lia)) as [Hs _]. rewrite Hft in *. split; [lia | exact Hs].
Qed.

Lemma ebq_fields_ok : forall F0 F1 F2 s0 s1 s2 seqs,
  wf_ok F0 -> wf_ok F1 -> wf_ok F2 -> 1 <= Zlength seqs -> Forall seq_ok seqs ->
  fse_chain (wf_table F0) (map (sq_code 0) seqs) s0 ->
  fse_chain (wf_table F1) (map (sq_code 1) seqs) s1 ->
  fse_chain (wf_table F2) (map (sq_code 2) seqs) s2 ->
  fields_ok (seq_fields (wf_table F0) (wf_table F1) (wf_table F2) s0 s1 s2 seqs).
Proof.
  intros F0 F1 F2 s0 s1 s2 seqs W0 W1 W2 Hn Hs C0 C1 C2.
  assert (Hm: forall ty, Zlength (map (sq_code ty) seqs) = Zlength seqs) by (intros; apply Zlength_map).
  unfold fields_ok, seq_fields. apply Forall_app. split.
  - apply Forall_forall. intros x Hx. apply in_flat_map in Hx as [j [Hj Hx]]. apply in_seq in Hj.
    rewrite Zlength_correct in Hn. set (q := Zlength seqs - 1 - Z.of_nat j) in Hx.
    assert (Hq: 0 <= q < Zlength seqs) by (unfold q; rewrite Zlength_correct; lia).
    unfold seq_fields_at in Hx. apply in_app_or in Hx as [Hx | Hx].
    + destruct (q + 1 <? Zlength seqs) eqn:E; [| contradiction]. apply Z.ltb_lt in E.
      simpl in Hx. destruct Hx as [<- | [<- | [<- | []]]].
      * apply (ebq_upd_ok F1 (map (sq_code 1) seqs)); auto; try lia; rewrite Hm; lia.
      * apply (ebq_upd_ok F2 (map (sq_code 2) seqs)); auto; try lia; rewrite Hm; lia.
      * apply (ebq_upd_ok F0 (map (sq_code 0) seqs)); auto; try lia; rewrite Hm; lia.
    + assert (Hsq: seq_ok (sqn seqs q)).
      { unfold sqn. apply Forall_nth; [exact Hs | rewrite Zlength_correct in Hq; lia]. }
      unfold seq_ex_fields in Hx. simpl in Hx.
      destruct Hx as [<- | [<- | [<- | []]]]; simpl;
        [ destruct (ebc_sq_code_facts 0 _ Hsq ltac:(lia)) as (_ & A & B)
        | destruct (ebc_sq_code_facts 2 _ Hsq ltac:(lia)) as (_ & A & B)
        | destruct (ebc_sq_code_facts 1 _ Hsq ltac:(lia)) as (_ & A & B) ]; lia.
  - assert (H1n: forall ty, 1 <= Zlength (map (sq_code ty) seqs)) by (intros; rewrite Hm; lia).
    destruct (ebq_init_ok F0 _ s0 W0 C0 (H1n 0)). destruct (ebq_init_ok F1 _ s1 W1 C1 (H1n 1)).
    destruct (ebq_init_ok F2 _ s2 W2 C2 (H1n 2)).
    repeat constructor; simpl; lia.
Qed.
