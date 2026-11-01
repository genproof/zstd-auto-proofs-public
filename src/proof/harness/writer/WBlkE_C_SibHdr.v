(* Verbatim copy of the proved src/proof/harness/writer/model/WM_BlkHdr.v (same statements and proofs),
   used by segment E's proofs in place of model.WM_BlkHdr. *)
(* w_compressed_block, the sequences section header (plain Coq): Number_of_Sequences in its three forms, the modes byte
   and the table
   descriptions decode (decode_seq_header) to the writer's tables. *)
Require Import Zstd.proof.harness.writer.model.WM_BlkDefs.
Require Import Zstd.proof.harness.writer.model.WM_Bits Zstd.proof.harness.writer.model.WM_NCount.

Lemma wbh_skipn_at : forall (l a c: list Z) p, l = a ++ c -> p = Zlength a -> skipn (Z.to_nat p) l = c.
Proof.
  intros l a c p -> ->. rewrite Zlength_correct, Nat2Z.id. induction a; simpl; auto.
Qed.

Lemma wbh_byte_at : forall (l a c: list Z) x p, l = a ++ x :: c -> p = Zlength a -> byte_at l p = x.
Proof.
  intros l a c x p -> ->. unfold byte_at. rewrite Zlength_correct, Nat2Z.id. induction a; simpl; auto.
Qed.

Lemma wbh_mode_range : forall ty m p F, mode_ok ty m p F -> 0 <= m <= 3.
Proof. intros ty m p F H. unfold mode_ok in H. lia. Qed.

Lemma wbh_modes : forall m0 m1 m2, 0 <= m0 <= 3 -> 0 <= m1 <= 3 -> 0 <= m2 <= 3 ->
  Z.land (m0 * 64 + m1 * 16 + m2 * 4) 3 = 0 /\ Z.shiftr (m0 * 64 + m1 * 16 + m2 * 4) 6 = m0 /\
  Z.land (Z.shiftr (m0 * 64 + m1 * 16 + m2 * 4) 4) 3 = m1 /\
  Z.land (Z.shiftr (m0 * 64 + m1 * 16 + m2 * 4) 2) 3 = m2 /\ 0 <= m0 * 64 + m1 * 16 + m2 * 4 < 256.
Proof.
  intros m0 m1 m2 H0 H1 H2.
  assert (E0: m0 = 0 \/ m0 = 1 \/ m0 = 2 \/ m0 = 3) by lia.
  assert (E1: m1 = 0 \/ m1 = 1 \/ m1 = 2 \/ m1 = 3) by lia.
  assert (E2: m2 = 0 \/ m2 = 1 \/ m2 = 2 \/ m2 = 3) by lia.
  destruct E0 as [-> | [-> | [-> | ->]]]; destruct E1 as [-> | [-> | [-> | ->]]]; destruct E2 as [-> | [-> | [-> | ->]]];
    vm_compute; repeat split; congruence.
Qed.

Lemma wbh_ty_max : forall ty, ty_max ty <= 255.
Proof. intros. unfold ty_max. destruct (ty =? 0); [|destruct (ty =? 1)]; lia. Qed.

Lemma wbh_desc_ok : forall ty m p F, mode_ok ty m p F -> bytes_ok (wtab_desc m F).
Proof.
  intros ty m p F H.
  destruct H as [[-> ->]|[[-> [c [Hc ->]]]|[[-> (Hd & Hn & Hl & Hz)]|[-> Hp]]]].
  - constructor.
  - unfold wtab_desc. cbn -[Z.add Z.sub ty_max]. pose proof (wbh_ty_max ty).
    constructor; [unfold is_byte; lia | constructor].
  - unfold wtab_desc. cbn -[fse_desc_bytes]. apply fse_desc_bytes_ok; auto.
  - constructor.
Qed.

Lemma wbh_nseq_ok : forall f n, nseq_form_ok f n -> bytes_ok (nseq_bytes f n).
Proof.
  intros f n H. destruct H as [[-> Hn]|[[-> Hn]|[-> Hn]]]; unfold nseq_bytes; cbn -[Z.add Z.sub Z.div Z.modulo].
  - constructor; [unfold is_byte; lia | constructor].
  - assert (0 <= n / 256 < 127) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
    pose proof (Z.mod_pos_bound n 256 ltac:(lia)).
    constructor; [unfold is_byte; lia | constructor; [unfold is_byte; lia | constructor]].
  - constructor; [unfold is_byte; lia | apply (wmb_le_bytes_ok 2)].
Qed.

Lemma wbh_nseq : forall f n t, 1 <= n -> nseq_form_ok f n -> 1 <= Zlength t ->
  (if byte_at (nseq_bytes f n ++ t) 0 <=? 127 then (byte_at (nseq_bytes f n ++ t) 0, 1, true)
   else if byte_at (nseq_bytes f n ++ t) 0 =? 255
   then (le_field (nseq_bytes f n ++ t) 1 2 + LONGNBSEQ, 3, 3 <=? Zlength (nseq_bytes f n ++ t))
   else ((byte_at (nseq_bytes f n ++ t) 0 - 128) * 256 + byte_at (nseq_bytes f n ++ t) 1, 2,
         2 <=? Zlength (nseq_bytes f n ++ t))) = (n, Zlength (nseq_bytes f n), true).
Proof.
  intros f n t Hn1 H Ht. destruct H as [[-> Hn]|[[-> Hn]|[-> Hn]]]; unfold nseq_bytes.
  - change (0 =? 0) with true. cbv iota. unfold byte_at. cbn -[Z.leb].
    replace (n <=? 127) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
  - change (1 =? 0) with false. change (1 =? 1) with true. cbv iota. unfold byte_at.
    cbn -[Z.leb Z.eqb Z.add Z.sub Z.mul Z.div Z.modulo Zlength].
    assert (0 <= n / 256 < 127) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
    replace (128 + n / 256 <=? 127) with false by (symmetry; apply Z.leb_gt; lia).
    replace (128 + n / 256 =? 255) with false by (symmetry; apply Z.eqb_neq; lia).
    rewrite !Zlength_cons. replace (2 <=? Z.succ (Z.succ (Zlength t))) with true
      by (symmetry; apply Z.leb_le; lia).
    change (Pos.to_nat 1) with 1%nat. cbv iota. rewrite Zlength_nil.
    f_equal. f_equal. pose proof (Z.div_mod n 256 ltac:(lia)). lia.
  - change (2 =? 0) with false. change (2 =? 1) with false. cbv iota.
    assert (Eb: byte_at ((255 :: le_bytes 2 (n - 32512)) ++ t) 0 = 255) by reflexivity.
    rewrite Eb. change (255 <=? 127) with false. change (255 =? 255) with true. cbv iota.
    assert (Ef: le_field ((255 :: le_bytes 2 (n - 32512)) ++ t) 1 2 = le_value (le_bytes 2 (n - 32512))).
    { unfold le_field, slice. f_equal. }
    rewrite Ef, wmb_le_value_le_bytes, Z.mod_small by (change (2 ^ (8 * Z.of_nat 2)) with 65536; lia).
    rewrite Zlen_app. change (Zlength (255 :: le_bytes 2 (n - 32512))) with 3.
    replace (3 <=? 3 + Zlength t) with true by (symmetry; apply Z.leb_le; lia).
    unfold LONGNBSEQ. f_equal. f_equal. lia.
Qed.

Lemma wbh_seq_table : forall ty m p F rest,
  mode_ok ty m p F ->
  seq_table m (wf_table (pre_wfse ty)) (option_map wf_table p) (ty_max ty) (ty_maxlog ty) (wtab_desc m F ++ rest)
  = Some (wf_table F, Zlength (wtab_desc m F)).
Proof.
  intros ty m p F rest H.
  destruct H as [[-> ->]|[[-> [c [Hc ->]]]|[[-> (Hd & Hn & Hl & Hz)]|[-> Hp]]]].
  - reflexivity.
  - unfold seq_table, wtab_desc, rle_wfse, wf_table. cbn -[Z.add Z.sub ty_max].
    replace (c + 1 - 1) with c by lia.
    destruct (c >? ty_max ty) eqn:E; [rewrite Z.gtb_ltb, Z.ltb_lt in E; lia|].
    replace (Zlength_aux (Z.succ 0) Z rest <? 1) with false; [reflexivity|].
    change (Zlength_aux (Z.succ 0) Z rest) with (Zlength (c :: rest)).
    rewrite Zlength_cons. pose proof (Zlen_nn rest). symmetry; apply Z.ltb_ge; lia.
  - unfold seq_table, wtab_desc. cbn -[fse_desc_bytes read_ncount ty_max ty_maxlog fse_build].
    rewrite fse_desc_read by (auto; pose proof (wbh_ty_max ty); lia).
    destruct (wf_log F >? ty_maxlog ty) eqn:E; [rewrite Z.gtb_ltb, Z.ltb_lt in E; lia|].
    unfold wf_table. destruct Hd as [Hlog _].
    destruct (wf_log F =? 0) eqn:E2; [rewrite Z.eqb_eq in E2; lia|]. reflexivity.
  - subst p. reflexivity.
Qed.

(* no sequences: the 1-byte or the 2-byte form of 0, the end of the block *)
Lemma seq_hdr_zero : forall f prev, 0 <= f <= 1 ->
  decode_seq_header prev (nseq_bytes f 0) = Some (0, prev, Zlength (nseq_bytes f 0)).
Proof.
  intros f prev Hf.
  assert (E: f = 0 \/ f = 1) by lia. destruct E as [-> | ->]; reflexivity.
Qed.

Lemma seq_hdr_ok : forall f n m0 m1 m2 F0 F1 F2 (prev: option (wfse * wfse * wfse)) rest,
  1 <= n -> nseq_form_ok f n ->
  mode_ok 0 m0 (option_map wtabs_ll prev) F0 ->
  mode_ok 1 m1 (option_map wtabs_of prev) F1 ->
  mode_ok 2 m2 (option_map wtabs_ml prev) F2 ->
  decode_seq_header (option_map (fun '(a, b, c) => (wf_table a, wf_table b, wf_table c)) prev)
    (seq_hdr_bytes f n m0 m1 m2 F0 F1 F2 ++ rest) =
  Some (n, Some (wf_table F0, wf_table F1, wf_table F2), Zlength (seq_hdr_bytes f n m0 m1 m2 F0 F1 F2)).
Proof.
  intros f n m0 m1 m2 F0 F1 F2 prev rest Hn Hf H0 H1 H2.
  pose proof (wbh_mode_range _ _ _ _ H0). pose proof (wbh_mode_range _ _ _ _ H1).
  pose proof (wbh_mode_range _ _ _ _ H2).
  destruct (wbh_modes m0 m1 m2) as (Ml & M0 & M1 & M2 & Mb); auto.
  remember (nseq_bytes f n) as N eqn:EN.
  remember (m0 * 64 + m1 * 16 + m2 * 4) as mb eqn:Emb.
  remember (wtab_desc m0 F0) as D0 eqn:ED0.
  remember (wtab_desc m1 F1) as D1 eqn:ED1.
  remember (wtab_desc m2 F2) as D2 eqn:ED2.
  assert (EB: seq_hdr_bytes f n m0 m1 m2 F0 F1 F2 ++ rest = N ++ mb :: D0 ++ D1 ++ D2 ++ rest).
  { unfold seq_hdr_bytes. subst. rewrite <- !app_assoc. reflexivity. }
  assert (EL: Zlength (seq_hdr_bytes f n m0 m1 m2 F0 F1 F2) =
              Zlength N + 1 + Zlength D0 + Zlength D1 + Zlength D2).
  { unfold seq_hdr_bytes. subst. rewrite !Zlen_app. change (Zlength [_]) with 1. lia. }
  rewrite EB, EL.
  unfold decode_seq_header. cbv zeta. rewrite EN. rewrite wbh_nseq;
    [| lia | exact Hf | rewrite Zlength_cons; pose proof (Zlen_nn (D0 ++ D1 ++ D2 ++ rest)); lia].
  rewrite <- EN.
  pose proof (Zlen_nn N). pose proof (Zlen_nn D0). pose proof (Zlen_nn D1). pose proof (Zlen_nn D2).
  pose proof (Zlen_nn rest).
  assert (LB: Zlength (N ++ mb :: D0 ++ D1 ++ D2 ++ rest) =
              Zlength N + 1 + Zlength D0 + Zlength D1 + Zlength D2 + Zlength rest)
    by (rewrite !Zlen_app, Zlength_cons, !Zlen_app; lia).
  rewrite LB.
  replace (_ <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  destruct (Zlength N + 1 >? _) eqn:E; [rewrite Z.gtb_ltb, Z.ltb_lt in E; lia|].
  rewrite (wbh_byte_at _ N (D0 ++ D1 ++ D2 ++ rest) mb (Zlength N)) by auto.
  rewrite Ml, M0, M1, M2. cbn [negb Z.eqb].
  assert (P0: option_map (fun '(l, _, _) => l)
                (option_map (fun '(a, b, c) => (wf_table a, wf_table b, wf_table c)) prev) =
              option_map wf_table (option_map wtabs_ll prev)) by (destruct prev as [[[a b] c]|]; reflexivity).
  assert (P1: option_map (fun '(_, o, _) => o)
                (option_map (fun '(a, b, c) => (wf_table a, wf_table b, wf_table c)) prev) =
              option_map wf_table (option_map wtabs_of prev)) by (destruct prev as [[[a b] c]|]; reflexivity).
  assert (P2: option_map (fun '(_, _, m) => m)
                (option_map (fun '(a, b, c) => (wf_table a, wf_table b, wf_table c)) prev) =
              option_map wf_table (option_map wtabs_ml prev)) by (destruct prev as [[[a b] c]|]; reflexivity).
  rewrite P0, P1, P2.
  change LL_predef with (wf_table (pre_wfse 0)). change MaxLL with (ty_max 0).
  change LLFSELog with (ty_maxlog 0).
  change OF_predef with (wf_table (pre_wfse 1)). change MaxOff with (ty_max 1).
  change OffFSELog with (ty_maxlog 1).
  change ML_predef with (wf_table (pre_wfse 2)). change MaxML with (ty_max 2).
  change MLFSELog with (ty_maxlog 2).
  rewrite (wbh_skipn_at _ (N ++ [mb]) (D0 ++ D1 ++ D2 ++ rest))
    by first [rewrite <- app_assoc; reflexivity | rewrite Zlen_app; reflexivity].
  rewrite ED0 at 1. rewrite (wbh_seq_table 0 m0 _ F0 _ H0). rewrite <- ED0. cbv iota beta.
  rewrite (wbh_skipn_at _ (N ++ mb :: D0) (D1 ++ D2 ++ rest))
    by first [rewrite <- app_assoc; reflexivity | rewrite Zlen_app, Zlength_cons; lia].
  rewrite ED1 at 1. rewrite (wbh_seq_table 1 m1 _ F1 _ H1). rewrite <- ED1. cbv iota beta.
  rewrite (wbh_skipn_at _ (N ++ mb :: D0 ++ D1) (D2 ++ rest))
    by first [repeat (rewrite <- app_assoc || rewrite <- app_comm_cons); reflexivity | rewrite !Zlen_app, Zlength_cons, !Zlen_app; lia].
  rewrite ED2 at 1. rewrite (wbh_seq_table 2 m2 _ F2 _ H2). rewrite <- ED2. cbv iota beta.
  reflexivity.
Qed.

Lemma seq_hdr_bytes_ok : forall f n m0 m1 m2 F0 F1 F2 prev,
  nseq_form_ok f n -> 0 <= m0 <= 3 -> 0 <= m1 <= 3 -> 0 <= m2 <= 3 ->
  mode_ok 0 m0 prev F0 -> mode_ok 1 m1 prev F1 -> mode_ok 2 m2 prev F2 ->
  bytes_ok (nseq_bytes f n) /\ bytes_ok (seq_hdr_bytes f n m0 m1 m2 F0 F1 F2).
Proof.
  intros f n m0 m1 m2 F0 F1 F2 prev Hf R0 R1 R2 H0 H1 H2.
  destruct (wbh_modes m0 m1 m2) as (_ & _ & _ & _ & Mb); auto.
  pose proof (wbh_nseq_ok f n Hf). split; auto.
  unfold seq_hdr_bytes. unfold bytes_ok in *.
  apply Forall_app; split; [auto|].
  apply Forall_app; split; [constructor; [unfold is_byte; lia | constructor]|].
  apply Forall_app; split; [eapply wbh_desc_ok; eauto|].
  apply Forall_app; split; eapply wbh_desc_ok; eauto.
Qed.

(* every lemma above together *)
Theorem wm_blkhdr_all :
  (forall f prev, 0 <= f <= 1 ->
     decode_seq_header prev (nseq_bytes f 0) = Some (0, prev, Zlength (nseq_bytes f 0))) /\
  (forall f n m0 m1 m2 F0 F1 F2 (prev: option (wfse * wfse * wfse)) rest,
     1 <= n -> nseq_form_ok f n ->
     mode_ok 0 m0 (option_map wtabs_ll prev) F0 -> mode_ok 1 m1 (option_map wtabs_of prev) F1 ->
     mode_ok 2 m2 (option_map wtabs_ml prev) F2 ->
     decode_seq_header (option_map (fun '(a, b, c) => (wf_table a, wf_table b, wf_table c)) prev)
       (seq_hdr_bytes f n m0 m1 m2 F0 F1 F2 ++ rest) =
     Some (n, Some (wf_table F0, wf_table F1, wf_table F2), Zlength (seq_hdr_bytes f n m0 m1 m2 F0 F1 F2))) /\
  (forall f n m0 m1 m2 F0 F1 F2 prev,
     nseq_form_ok f n -> 0 <= m0 <= 3 -> 0 <= m1 <= 3 -> 0 <= m2 <= 3 ->
     mode_ok 0 m0 prev F0 -> mode_ok 1 m1 prev F1 -> mode_ok 2 m2 prev F2 ->
     bytes_ok (nseq_bytes f n) /\ bytes_ok (seq_hdr_bytes f n m0 m1 m2 F0 F1 F2)).
Proof. exact (conj seq_hdr_zero (conj seq_hdr_ok seq_hdr_bytes_ok)). Qed.
