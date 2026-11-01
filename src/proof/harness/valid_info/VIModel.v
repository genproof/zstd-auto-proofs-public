(* Plain-Coq facts for main of harness/valid_info.c: the loop's accumulators (bound, allfcs, anybig) against
   expected_fds / expected_bound of series_facts, and the frames' positions (WMain_valid_info). *)
From Coq Require Import Bool.
Require Import Zstd.proof.harness.writer.WTop Zstd.proof.model.Info.
Local Open Scope bool_scope.

(* the harness's accumulators over the frames seen so far *)
Definition vi_bterm (f: winfo) : Z :=
  if wi_skippable f then 0
  else if wi_fcs_present f then wi_fcs f else wi_blocks f * Z.min (wi_window f) ZSTD_BLOCKSIZE_MAX.

Fixpoint vi_bsum (fs: list winfo) : Z :=
  match fs with nil => 0 | f :: fs' => vi_bterm f + vi_bsum fs' end.

Definition vi_allfcs (fs: list winfo) : bool := forallb (fun f => wi_skippable f || wi_fcs_present f) fs.

Definition vi_anybig (fs: list winfo) : bool := existsb wi_big fs.

Fixpoint vi_csum (fs: list winfo) : Z :=
  match fs with nil => 0 | f :: fs' => wi_csize f + vi_csum fs' end.

Lemma vi_bsum_app l1 l2 : vi_bsum (l1 ++ l2) = vi_bsum l1 + vi_bsum l2.
Proof. induction l1; simpl; lia. Qed.

Lemma vi_tiles_csum fs off coff n cn : tiles fs off coff n cn -> coff + vi_csum fs = cn.
Proof.
  revert off coff. induction fs as [|f fs IH]; simpl; intros off coff H.
  - lia.
  - destruct H as (_ & _ & _ & _ & _ & H). apply IH in H. lia.
Qed.

Lemma vi_fds_gen fs acc :
  Forall (fun f => wi_skippable f = false -> wi_fcs_present f = true -> wi_fcs f = wi_csize f) fs ->
  Forall (fun f => wi_skippable f = true -> wi_csize f = 0) fs ->
  (vi_anybig fs = true /\ expected_fds fs acc = ZSTD_CONTENTSIZE_ERROR) \/
  expected_fds fs acc = (if vi_allfcs fs then acc + vi_csum fs else ZSTD_CONTENTSIZE_UNKNOWN).
Proof.
  revert acc. induction fs as [|f fs IH]; intros acc H1 H2; simpl.
  - right. lia.
  - inversion H1 as [|? ? Hf H1']; subst. inversion H2 as [|? ? Hg H2']; subst.
    unfold vi_anybig, vi_allfcs in *; simpl.
    destruct (wi_skippable f) eqn:Es; simpl.
    + rewrite (Hg eq_refl). destruct (IH acc H1' H2') as [[-> ->] | ->].
      * left. rewrite orb_true_r. auto.
      * right. destruct (forallb _ fs); lia.
    + destruct (wi_big f) eqn:Eb; simpl.
      * left. auto.
      * destruct (wi_fcs_present f) eqn:Ef; simpl.
        -- rewrite (Hf eq_refl eq_refl).
           destruct (IH (acc + wi_csize f) H1' H2') as [[-> ->] | ->]; [left; auto | right].
           destruct (forallb _ fs); lia.
        -- right. reflexivity.
Qed.

Lemma vi_bound_gen fs acc :
  (vi_anybig fs = true /\ expected_bound fs acc = ZSTD_CONTENTSIZE_ERROR) \/
  expected_bound fs acc = acc + vi_bsum fs.
Proof.
  revert acc. induction fs as [|f fs IH]; intros acc; simpl.
  - right. lia.
  - unfold vi_anybig in *; simpl. unfold vi_bterm.
    destruct (wi_skippable f) eqn:Es; simpl.
    + destruct (IH acc) as [[-> ->] | ->]; [left; rewrite orb_true_r; auto | right; lia].
    + destruct (wi_big f) eqn:Eb; simpl.
      * left. auto.
      * simpl. match goal with |- context [expected_bound fs ?a] => destruct (IH a) as [[-> ->] | ->] end;
          [left; auto | right; lia].
Qed.

Lemma vi_tiles_skip fs off coff n cn : tiles fs off coff n cn ->
  Forall (fun f => wi_skippable f = true -> wi_csize f = 0) fs.
Proof.
  revert off coff. induction fs as [|f fs IH]; simpl; intros off coff H; constructor.
  - apply H.
  - destruct H as (_ & _ & _ & _ & _ & H). eapply IH; eauto.
Qed.

Lemma vi_fds dm ws : series_facts dm ws ->
  (vi_anybig (ws_frames ws) = true /\ find_decompressed_size (ws_bytes ws) = ZSTD_CONTENTSIZE_ERROR) \/
  find_decompressed_size (ws_bytes ws) =
    (if vi_allfcs (ws_frames ws) then Zlength (ws_content ws) else ZSTD_CONTENTSIZE_UNKNOWN).
Proof.
  intros (_ & _ & _ & _ & _ & Ht & _ & Hfcs & Hd & _). rewrite Hd.
  pose proof (vi_tiles_csum _ _ _ _ _ Ht) as Hc.
  destruct (vi_fds_gen (ws_frames ws) 0 Hfcs (vi_tiles_skip _ _ _ _ _ Ht)) as [H | ->]; [left; exact H | right].
  destruct (vi_allfcs _); lia.
Qed.

Lemma vi_bound dm ws : series_facts dm ws ->
  (vi_anybig (ws_frames ws) = true /\ decompress_bound (ws_bytes ws) = ZSTD_CONTENTSIZE_ERROR) \/
  decompress_bound (ws_bytes ws) = vi_bsum (ws_frames ws).
Proof.
  intros (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hb). rewrite Hb.
  destruct (vi_bound_gen (ws_frames ws) 0) as [H | ->]; [left; exact H | right; lia].
Qed.

Lemma vi_tiles_le fs off coff n cn : tiles fs off coff n cn -> off <= n.
Proof.
  revert off coff. induction fs as [|f fs IH]; simpl; intros off coff H; [lia|].
  destruct H as (_ & _ & Hp & _ & _ & H). apply IH in H. lia.
Qed.

(* the k-th frame lies within the bytes *)
Lemma vi_tiles_nth fs off coff n cn : tiles fs off coff n cn -> forall k, (k < length fs)%nat ->
  off <= wi_start (nth k fs winfo0) /\ wi_start (nth k fs winfo0) + wi_size (nth k fs winfo0) <= n /\
  0 < wi_size (nth k fs winfo0).
Proof.
  revert off coff. induction fs as [|f fs IH]; simpl; intros off coff H k Hk; [lia|].
  destruct H as (Hs & _ & Hp & Hc & _ & H).
  destruct k as [|k].
  - apply vi_tiles_le in H. lia.
  - destruct (IH _ _ H k ltac:(lia)) as (A & B & C). lia.
Qed.
