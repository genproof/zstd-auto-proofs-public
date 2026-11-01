(* Empty buffers passed as NULL (fix F9).  The API specifications state a caller's byte buffer that may be NULL when it
   is empty as Spec_api6.mbuf.  ZSTD_decompressStream and ZSTD_decompressMultiFrame compute with a non-NULL base
   instead: the buffer itself, or ZSTD_emptyBuffer (nbase).  A body that does so lends a part of zstd_globals'
   ZSTD_emptyBuffer (eb_res) to its callees as the pointer witness of that base (eb_wit), and joins it back at the
   end.  This file holds those facts. *)
Require Import Zstd.proof.zstd.Spec_api6.
Local Open Scope logic.

(* ---------- mbuf ---------- *)

Lemma mbuf_isptr : forall sh n c p, isptr p -> mbuf sh n c p = data_at sh (tarray tuchar n) c p.
Proof. intros sh n c p Hp. unfold mbuf. rewrite if_false; auto. intros ->. exact Hp. Qed.

Lemma mbuf_null : forall sh n c, mbuf sh n c nullval = !! (n = 0 /\ c = []) && emp.
Proof. intros. unfold mbuf. rewrite if_true; auto. Qed.

(* the callers that pass a pointer: data_at is mbuf *)
Lemma data_at_mbuf : forall sh n c p, data_at sh (tarray tuchar n) c p |-- mbuf sh n c p.
Proof.
  intros sh n c p. assert_PROP (isptr p) as Hp by entailer!. rewrite mbuf_isptr by auto. apply derives_refl.
Qed.

Lemma data_at__mbuf : forall sh n p, data_at_ sh (tarray tuchar n) p |-- mbuf sh n (Zrepeat Vundef n) p.
Proof.
  intros sh n p. eapply derives_trans; [| apply data_at_mbuf]. unfold data_at_. apply derives_refl.
Qed.

Lemma mbuf_local_facts : forall sh n c p,
  0 <= n -> mbuf sh n c p |-- !! (Zlength c = n /\ (p = nullval -> n = 0 /\ c = [])).
Proof.
  intros sh n c p Hn. unfold mbuf. destruct (eq_dec p nullval) as [E | E].
  - Intros. subst. apply prop_right. split; [reflexivity | auto].
  - entailer!.
Qed.

(* ---------- the base of a buffer that may be NULL ---------- *)

Definition nbase (gv: globals) (p: val) : val := if eq_dec p nullval then gv _ZSTD_emptyBuffer else p.
Arguments nbase : simpl never.

Lemma nbase_ptr : forall gv p, p <> nullval -> nbase gv p = p.
Proof. intros. unfold nbase. rewrite if_false; auto. Qed.

Lemma nbase_null : forall gv, nbase gv nullval = gv _ZSTD_emptyBuffer.
Proof. intros. unfold nbase. rewrite if_true; auto. Qed.

Lemma nbase_cases : forall gv p, (p <> nullval /\ nbase gv p = p) \/ (p = nullval /\ nbase gv p = gv _ZSTD_emptyBuffer).
Proof. intros. unfold nbase. destruct (eq_dec p nullval); auto. Qed.

(* ---------- the witness lent from ZSTD_emptyBuffer ---------- *)

Definition eb_cells : list val := [Vint (Int.repr 0)].

Definition eb_wit (gv: globals) (sh: share) : ptr_witness := pw_bytes sh 1 eb_cells (gv _ZSTD_emptyBuffer).

(* two readable parts of one byte are parts of a readable share (they cannot overlap) *)
Lemma eb_rejoin : forall gv sh1 sh2,
  readable_share sh1 ->
  data_at sh1 (tarray tuchar 1) eb_cells (gv _ZSTD_emptyBuffer) *
  data_at sh2 (tarray tuchar 1) eb_cells (gv _ZSTD_emptyBuffer) |-- eb_res gv.
Proof.
  intros gv sh1 sh2 H1.
  destruct (eq_dec (Share.glb sh1 sh2) Share.bot) as [E | E].
  - assert (J: sepalg.join sh1 sh2 (Share.lub sh1 sh2)) by (split; auto).
    unfold eb_res, eb_cells. Exists (Share.lub sh1 sh2).
    rewrite (data_at_share_join sh1 sh2 (Share.lub sh1 sh2)) by exact J.
    entailer!. eapply join_sub_readable; [exists sh2; exact J | exact H1].
  - eapply derives_trans; [apply data_at_conflict_glb | apply FF_left].
    + intros Hi. apply E. apply identity_share_bot in Hi. exact Hi.
    + simpl. lia.
Qed.

(* lend a readable part of ZSTD_emptyBuffer: zstd_globals stays whole *)
Lemma zstd_globals_lend : forall gv,
  zstd_globals gv |-- EX sh: share, !! readable_share sh && (zstd_globals gv * pw_pred (eb_wit gv sh)).
Proof.
  intros gv. unfold zstd_globals, eb_res at 1. Intros sh.
  destruct (slice.split_readable_share sh H) as (sh1 & sh2 & R1 & R2 & J).
  Exists sh2. unfold eb_res, eb_wit, pw_pred, eb_cells.
  rewrite <- (data_at_share_join sh1 sh2 sh) by exact J.
  Exists sh1. entailer!.
Qed.

(* and give it back *)
Lemma zstd_globals_return : forall gv sh, zstd_globals gv * pw_pred (eb_wit gv sh) |-- zstd_globals gv.
Proof.
  intros gv sh. unfold zstd_globals at 1. unfold eb_res at 1. Intros sh1.
  unfold zstd_globals. cancel. unfold eb_wit, pw_pred.
  apply eb_rejoin; auto.
Qed.

Lemma eb_wit_field_compatible : forall gv sh n,
  0 <= n <= 1 -> pw_pred (eb_wit gv sh) |-- !! field_compatible (tarray tuchar n) [] (gv _ZSTD_emptyBuffer).
Proof.
  intros gv sh n Hn. unfold eb_wit, pw_pred. entailer!.
Qed.

Lemma pws_pred_cons : forall w W, pws_pred (w :: W) = pw_pred w * pws_pred W.
Proof. intros. reflexivity. Qed.

(* the base's witness: ZSTD_emptyBuffer is (strictly) valid *)
Lemma eb_wit_valid : forall gv sh W,
  readable_share sh -> pws_pred (eb_wit gv sh :: W) |-- valid_pointer (gv _ZSTD_emptyBuffer).
Proof.
  intros gv sh W Hr. rewrite pws_pred_cons. apply sepcon_valid_pointer1.
  unfold eb_wit, pw_pred, eb_cells.
  eapply derives_trans; [apply data_at_valid_ptr; [apply readable_nonidentity; auto | simpl; lia] |].
  apply derives_refl.
Qed.

(* buf_ok is kept when a witness is added *)
Lemma buf_ok_cons : forall w W sh n p, buf_ok W sh n p -> buf_ok (w :: W) sh n p.
Proof.
  intros w W sh n p Hb. unfold buf_ok in *. rewrite pws_pred_cons.
  rewrite sepcon_assoc. eapply derives_trans; [apply sepcon_derives; [apply derives_refl | exact Hb] |].
  apply andp_right; [apply sepcon_weak_valid_pointer2 | apply sepcon_weak_valid_pointer2];
  [apply andp_left1 | apply andp_left2]; apply derives_refl.
Qed.

(* the empty base ZSTD_emptyBuffer with its witness *)
Lemma buf_ok_eb : forall gv sh W shb,
  readable_share sh -> buf_ok (eb_wit gv sh :: W) shb 0 (gv _ZSTD_emptyBuffer).
Proof.
  intros gv sh W shb Hr. unfold buf_ok.
  assert_PROP (isptr (gv _ZSTD_emptyBuffer)) as Hp by (rewrite pws_pred_cons; unfold eb_wit, pw_pred; entailer!).
  rewrite isptr_offset_val_zero by exact Hp.
  eapply derives_trans; [apply sepcon_derives; [apply eb_wit_valid; exact Hr | apply derives_refl] |].
  apply andp_right; apply sepcon_weak_valid_pointer1; apply valid_pointer_weak.
Qed.

(* a buffer that may be NULL as the array at its base (with the witness for ZSTD_emptyBuffer at hand) ... *)
Lemma mbuf_base : forall gv sh2 sh n c p,
  mbuf sh n c p * pw_pred (eb_wit gv sh2) |-- data_at sh (tarray tuchar n) c (nbase gv p) * pw_pred (eb_wit gv sh2).
Proof.
  intros gv sh2 sh n c p. unfold mbuf. destruct (nbase_cases gv p) as [[Hn E] | [Hn E]]; rewrite E.
  - rewrite if_false by exact Hn. apply derives_refl.
  - rewrite if_true by exact Hn. Intros. subst n c.
    sep_apply (eb_wit_field_compatible gv sh2 0 ltac:(lia)). Intros.
    rewrite data_at_zero_array_eq by auto. entailer!.
Qed.

(* ... and back *)
Lemma base_mbuf : forall gv sh n c p,
  (p = nullval -> n = 0) -> data_at sh (tarray tuchar n) c (nbase gv p) |-- mbuf sh n c p.
Proof.
  intros gv sh n c p H. unfold mbuf. destruct (nbase_cases gv p) as [[Hn E] | [Hn E]]; rewrite E.
  - rewrite if_false by exact Hn. apply derives_refl.
  - rewrite if_true by exact Hn. specialize (H Hn). subst n.
    assert_PROP (Zlength c = 0 /\ isptr (gv _ZSTD_emptyBuffer)) as Hcp by entailer!. destruct Hcp as [Hc Hp].
    apply Zlength_nil_inv in Hc. subst c. rewrite data_at_zero_array_eq; auto. entailer!.
Qed.
