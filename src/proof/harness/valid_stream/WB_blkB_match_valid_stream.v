(* w_compressed_block, segment B, statement 15 (the match copy loop of a sequence: for (j = 0; j < ml; j++)
   w_hist[hn] = w_hist[hn - off], hn += 1, hn = *_hn) in the unit valid_stream: segB_match of WBlkBDefs_valid_stream.
   Template: WB_blkB_match.

   forward_for_simple_bound ml with m bytes of the match copied: w_hist holds hist ++ out ++ cont ++ L ++
   blk_tail .. m, then the rest of htl1; the byte read at |hist|+|out|+|cont|+|L|+m-off is the next byte of
   lz_copy (blkBM_tail_snoc, from lz_copy_snoc / lz_copy_app); the untouched SEP items are matched as is. *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.harness.valid_stream.WBlkBDefs_valid_stream.
Local Open Scope logic.

(* ---------- lz_copy (local proofs of WM_BlkGen's lz_copy facts) ---------- *)

Lemma blkBM_copy_prefix : forall hist cur off m, exists t, lz_copy hist cur off m = cur ++ t.
Proof.
  intros hist cur off m. revert cur. induction m as [| m IH]; intros cur; simpl.
  - exists []. rewrite app_nil_r. reflexivity.
  - destruct (IH (cur ++ [byte_at (hist ++ cur) (Zlength hist + Zlength cur - off)])) as [t E].
    rewrite E, <- app_assoc. eexists. reflexivity.
Qed.

Lemma lz_copy_app : forall hist cur off m, lz_copy hist cur off m = cur ++ lz_tail hist cur off m.
Proof.
  intros. unfold lz_tail. destruct (blkBM_copy_prefix hist cur off m) as [t E].
  rewrite E. f_equal. rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity.
Qed.

Lemma blkBM_copy_len : forall hist cur off m, length (lz_copy hist cur off m) = (length cur + m)%nat.
Proof.
  intros hist cur off m. revert cur. induction m as [| m IH]; intros cur; simpl; [lia |].
  rewrite IH, app_length. simpl. lia.
Qed.

Lemma lz_tail_len : forall hist cur off m, Zlength (lz_tail hist cur off m) = Z.of_nat m.
Proof.
  intros. rewrite Zlength_correct. unfold lz_tail. rewrite skipn_length, blkBM_copy_len. f_equal. lia.
Qed.

Lemma lz_copy_snoc : forall hist cur off m,
  lz_copy hist cur off (S m) =
  lz_copy hist cur off m ++
    [byte_at (hist ++ lz_copy hist cur off m) (Zlength hist + Zlength (lz_copy hist cur off m) - off)].
Proof.
  intros hist cur off m. revert cur. induction m as [| m IH]; intros cur.
  - reflexivity.
  - change (lz_copy hist cur off (S (S m))) with
      (lz_copy hist (cur ++ [byte_at (hist ++ cur) (Zlength hist + Zlength cur - off)]) off (S m)).
    rewrite IH. reflexivity.
Qed.

Lemma lz_copy_bytes : forall hist cur off m,
  bytes_ok hist -> bytes_ok cur -> bytes_ok (lz_copy hist cur off m).
Proof.
  intros hist cur off m Hh. revert cur. induction m as [| m IH]; intros cur Hc; simpl; [assumption |].
  apply IH. apply Forall_app. split; [assumption |]. constructor; [| constructor].
  unfold byte_at. set (k := Z.to_nat _). clearbody k.
  assert (Hb: bytes_ok (hist ++ cur)) by (apply Forall_app; split; assumption).
  destruct (Nat.lt_ge_cases k (length (hist ++ cur))) as [Hk | Hk].
  - eapply Forall_forall; [exact Hb |]. apply nth_In. exact Hk.
  - rewrite nth_overflow by exact Hk. unfold is_byte. lia.
Qed.

Lemma blkBM_tail0 : forall E cont L off, blk_tail E cont L off 0 = [].
Proof.
  intros. unfold blk_tail, lz_tail. simpl. apply skipn_all.
Qed.

Lemma blkBM_tail_len : forall E cont L off m, 0 <= m -> Zlength (blk_tail E cont L off m) = m.
Proof.
  intros. unfold blk_tail. rewrite lz_tail_len. apply Z2Nat.id. assumption.
Qed.

Lemma blkBM_tail_bytes : forall E cont L off m,
  bytes_ok (be_hist E) -> bytes_ok (be_out E ++ cont ++ L) -> bytes_ok (blk_tail E cont L off m).
Proof.
  intros E cont L off m Hh Hc. unfold blk_tail.
  pose proof (lz_copy_bytes (be_hist E) (be_out E ++ cont ++ L) off (Z.to_nat m) Hh Hc) as B.
  rewrite lz_copy_app in B. apply Forall_app in B. apply B.
Qed.

Lemma blkBM_tail_snoc : forall E cont L off m, 0 <= m ->
  blk_tail E cont L off (m + 1) =
  blk_tail E cont L off m ++
    [byte_at (be_hist E ++ be_out E ++ cont ++ L ++ blk_tail E cont L off m)
       (Zlength (be_hist E) + Zlength (be_out E) + Zlength cont + Zlength L + m - off)].
Proof.
  intros E cont L off m Hm. unfold blk_tail.
  replace (Z.to_nat (m + 1)) with (S (Z.to_nat m)) by lia.
  set (cur := be_out E ++ cont ++ L).
  pose proof (lz_copy_snoc (be_hist E) cur off (Z.to_nat m)) as S1.
  rewrite !(lz_copy_app (be_hist E) cur off) in S1.
  rewrite <- app_assoc in S1. apply app_inv_head in S1. rewrite S1. unfold cur.
  rewrite Zlength_app, lz_tail_len, Z2Nat.id by lia. rewrite !Zlength_app, !app_assoc.
  f_equal. f_equal. f_equal. lia.
Qed.

Lemma blkBM_read : forall (X: list Z) (tl: list val) i, 0 <= i < Zlength X ->
  Znth i (zbytes X ++ tl) = Vint (Int.repr (byte_at X i)).
Proof.
  intros. rewrite app_Znth1 by (rewrite Zlength_map; lia).
  rewrite Znth_map by lia. unfold byte_at, Znth. destruct (Z_lt_dec i 0); [lia |]. reflexivity.
Qed.

Lemma blkBM_byte : forall (X: list Z) i, bytes_ok X -> 0 <= i < Zlength X -> 0 <= byte_at X i < 256.
Proof.
  intros X i HX Hi. unfold byte_at.
  replace (nth (Z.to_nat i) X 0) with (Znth i X) by (unfold Znth; destruct (Z_lt_dec i 0); [lia | reflexivity]).
  apply (proj1 (Forall_Znth X is_byte) HX i Hi).
Qed.

Lemma blkBM_zext : forall c, 0 <= c < 256 -> Int.zero_ext 8 (Int.repr c) = Int.repr c.
Proof.
  intros. apply zero_ext_inrange. rewrite Int.unsigned_repr by rep_lia. simpl. lia.
Qed.

Lemma blkBM_upd : forall (a: list Z) (tl: list val) k m c, k = Zlength a -> 0 <= m < Zlength tl ->
  upd_Znth k (zbytes a ++ sublist m (Zlength tl) tl) (Vint (Int.repr c)) =
  zbytes (a ++ [c]) ++ sublist (m + 1) (Zlength tl) tl.
Proof.
  intros a tl k m c -> Htl.
  rewrite upd_Znth_app2 by (rewrite Zlength_map, Zlength_sublist by lia; lia).
  rewrite Zlength_map, Z.sub_diag.
  rewrite (sublist_split m (m + 1) (Zlength tl)) by lia.
  rewrite (sublist_one m (m + 1)) by lia.
  simpl. rewrite upd_Znth0. rewrite map_app, <- app_assoc. reflexivity.
Qed.

Lemma blkBM_sub64 : forall a b,
  Int64.sub (Int64.repr a) (Int64.repr b) = Int64.repr (a - b).
Proof.
  intros. apply Int64.eqm_samerepr. apply Int64.eqm_sub; apply Int64.eqm_sym, Int64.eqm_unsigned_repr.
Qed.

Lemma blkBM_add64 : forall a,
  Int64.add (Int64.repr a) (Int64.repr (Int.signed (Int.repr 1))) = Int64.repr (a + 1).
Proof.
  intros. unfold Int64.add. apply Int64.eqm_samerepr. apply Int64.eqm_add.
  - apply Int64.eqm_sym, Int64.eqm_unsigned_repr.
  - rewrite Int.signed_repr by rep_lia. rewrite Int64.unsigned_repr by rep_lia. apply Int64.eqm_refl.
Qed.

Lemma segB_match_ok : segB_match.
Proof.
  unfold segB_match. blkB_start.
  unfold blk_it, blk_env_ok in *.
  destruct H as (Hosh & Hbsh & Hssh & Hhsh & Hwt & Hrep & Hbh & Hbo & Hlh & Hlo & Hwin & Ht & Hhs & Hhl).
  destruct R as [Rn Rb Rc Rr].
  Intros stv1 htl1 nhv.
  rewrite blkBM_tail0, Z.add_0_r, app_nil_r in *.
  match goal with Hx: Zlength (_ ++ htl1) = _ |- _ => rename Hx into Hlen end.
  lazymatch goal with |- semax _ (PROPx _ (LOCALx ?Lc (SEPx (?A1 :: ?A2 :: ?A3 :: ?A4 :: _ :: _ :: ?A7 :: ?A8 :: ?A9 :: ?A10 :: ?A11 :: nil)))) _ _ =>
  forward_for_simple_bound ml
    (EX m: Z,
     PROP ()
     (LOCALx Lc
     (SEPx (A1 :: A2 :: A3 :: A4 ::
       data_at (be_hsh E) tulong (vl (Zlength (be_hist E) + Zlength (be_out E) + Zlength cont + Zlength L + m))
         (be_hnp E) ::
       data_at Ews (tarray tuchar HIST_SIZE)
         (zbytes (be_hist E ++ be_out E ++ cont ++ L ++ blk_tail E cont L off m) ++ sublist m (Zlength htl1) htl1)
         (be_gv E _x_valid_stream__w_hist) ::
       A7 :: A8 :: A9 :: A10 :: A11 :: nil))))
  end.
  - (* entry *)
    rewrite blkBM_tail0, app_nil_r, sublist_same by reflexivity. rewrite Z.add_0_r.
    entailer!.
  - (* one byte *)
    forward. forward.
    set (n := Zlength (be_hist E) + Zlength (be_out E) + Zlength cont + Zlength L + i).
    set (X := be_hist E ++ be_out E ++ cont ++ L ++ blk_tail E cont L off i).
    assert (HX: Zlength X = n) by (unfold X, n; rewrite !Zlength_app, blkBM_tail_len by lia; lia).
    assert (Hn: n < HIST_SIZE) by (unfold n; lia).
    assert (Htl: i < Zlength htl1) by (rewrite Zlength_app, Zlength_map, !Zlength_app in Hlen; unfold n in Hn; lia).
    assert (HbX: bytes_ok X).
    { unfold X. repeat (apply Forall_app; split); try assumption.
      apply blkBM_tail_bytes; [assumption |]. repeat (apply Forall_app; split); assumption. }
    set (b := byte_at X (n - off)).
    assert (Hb: 0 <= b < 256) by (apply blkBM_byte; [assumption | unfold n in *; lia]).
    assert (Hrd: Znth (n - off) (zbytes X ++ sublist i (Zlength htl1) htl1) = Vint (Int.repr b))
      by (apply blkBM_read; unfold n in *; lia).
    assert (HX1: be_hist E ++ be_out E ++ cont ++ L ++ blk_tail E cont L off (i + 1) = X ++ [b]).
    { unfold b, X, n. rewrite blkBM_tail_snoc by lia. rewrite <- !app_assoc. reflexivity. }
    clearbody X b.
    remember HIST_SIZE as NH eqn:HNH.
    forward.
    { match goal with |- context [Znth ?k ?l] =>
        replace (Znth k l) with (Vint (Int.repr b)) by (rewrite <- Hrd; reflexivity) end.
      entailer!. rep_lia. }
    match goal with |- context [temp _x_valid_stream__t'102 (Znth ?k ?l)] =>
      replace (Znth k l) with (Vint (Int.repr b)) by (rewrite <- Hrd; reflexivity) end.
    match goal with |- context [temp _x_valid_stream__t'100 (vl ?x)] =>
      change (vl x) with (Vlong (Int64.repr x)) end.
    forward.
    rewrite blkBM_zext by assumption.
    rewrite (blkBM_upd X htl1 n i b) by (auto; lia).
    forward. forward.
    rewrite blkBM_add64, HX1.
    replace (Zlength (be_hist E) + Zlength (be_out E) + Zlength cont + Zlength L + (i + 1)) with (n + 1)
      by (unfold n; lia).
    unfold vl. entailer!.
  - (* after the loop: m = ml *)
    eapply semax_pre; [| exact H1].
    Exists stv1 (sublist ml (Zlength htl1) htl1) nhv.
    entailer!.
Qed.
