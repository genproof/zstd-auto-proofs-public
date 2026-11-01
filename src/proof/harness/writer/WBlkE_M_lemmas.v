(* Plain-Coq facts of phase M of segment E of w_compressed_block: the modes
   loop.  The predefined tables have a state for every code they may get, the RLE table for its symbol,
   fse_pick's table for every needed symbol; need_of: the need[] array of a list of codes. *)
Require Import VST.zlist.sublist VST.zlist.list_solver.
Require Import Zstd.proof.harness.writer.model.WM_BlkDefs.
Require Import Zstd.proof.harness.writer.model.WM_FseTab.
Local Open Scope Z_scope.

Lemma blkM_pre_has0 : forall n, (n < 36)%nat -> fse_has_b (pre_wfse 0) (Z.of_nat n) = true.
Proof. intros n Hn. do 36 (destruct n; [reflexivity |]). lia. Qed.

Lemma blkM_pre_has1 : forall n, (n < 29)%nat -> fse_has_b (pre_wfse 1) (Z.of_nat n) = true.
Proof. intros n Hn. do 29 (destruct n; [reflexivity |]). lia. Qed.

Lemma blkM_pre_has2 : forall n, (n < 53)%nat -> fse_has_b (pre_wfse 2) (Z.of_nat n) = true.
Proof. intros n Hn. do 53 (destruct n; [reflexivity |]). lia. Qed.

Lemma blkM_pre_has : forall ty c, 0 <= ty <= 2 -> 0 <= c <= ty_max ty -> (ty = 1 -> c <= 28) ->
  fse_has_b (pre_wfse ty) c = true.
Proof.
  intros ty c Hty Hc H1. rewrite <- (Z2Nat.id c) by lia.
  assert (ty = 0 \/ ty = 1 \/ ty = 2) as [-> | [-> | ->]] by lia; cbn in Hc.
  - apply blkM_pre_has0. lia.
  - apply blkM_pre_has1. specialize (H1 eq_refl). lia.
  - apply blkM_pre_has2. lia.
Qed.

Lemma blkM_mode0 : forall ty prev, mode_ok ty 0 prev (pre_wfse ty).
Proof. intros. left. auto. Qed.

Lemma blkM_mode1 : forall ty prev c, 0 <= c <= ty_max ty -> mode_ok ty 1 prev (rle_wfse c).
Proof. intros. right. left. split; [reflexivity | exists c; auto]. Qed.

Lemma blkM_mode3 : forall ty prev F, prev = Some F -> mode_ok ty 3 prev F.
Proof. intros. right. right. right. auto. Qed.

Lemma blkM_wf_rle : forall c, 0 <= c <= 52 -> wf_ok (rle_wfse c).
Proof. intros. unfold wf_ok, rle_wfse. cbn. lia. Qed.

Lemma blkM_has_rle : forall c0 c, c = c0 -> fse_has_b (rle_wfse c0) c = true.
Proof. intros. subst. unfold fse_has_b, rle_wfse. cbn. apply Z.eqb_eq. lia. Qed.

Definition pick_wfse (log: Z) (norm: list Z) : wfse := {| wf_log := log; wf_nsym := Zlength norm; wf_norm := norm |}.

Lemma blkM_mode2 : forall ty prev log maxsym need norm,
  ndist_ok log norm -> ndist_need maxsym need norm -> log <= ty_maxlog ty -> maxsym = ty_max ty ->
  mode_ok ty 2 prev (pick_wfse log norm).
Proof.
  intros ty prev log maxsym need norm Hok [Hl _] Hlog Hm. subst maxsym.
  right. right. left. cbn. refine (conj eq_refl (conj Hok (conj eq_refl (conj Hlog Hl)))).
Qed.

Lemma blkM_wf_pick : forall log norm, ndist_ok log norm -> wf_ok (pick_wfse log norm).
Proof.
  intros log norm (Hlog & Hn & Hf & Hs & _). unfold wf_ok, pick_wfse. cbn.
  destruct (Z.eqb_spec log 0); [lia |]. unfold ndist_base. auto.
Qed.

Lemma blkM_has_pick : forall log maxsym need norm c,
  ndist_ok log norm -> ndist_need maxsym need norm -> 0 <= c <= maxsym -> zn need c <> 0 ->
  fse_has_b (pick_wfse log norm) c = true.
Proof.
  intros log maxsym need norm c (Hlog & _) [_ Hn] Hc Hz. destruct (Hn c Hc Hz) as [H1 H2].
  unfold fse_has_b, pick_wfse. cbn. destruct (Z.eqb_spec log 0); [lia |].
  apply andb_true_intro. split; [apply Z.ltb_lt; exact H1 | apply Bool.negb_true_iff, Z.eqb_neq; exact H2].
Qed.

(* need[] after `need[s] = 0` for every s and `need[c] = 1` for the codes cs *)
Definition blkM_ix : list Z := map Z.of_nat (seq 0 53).
Definition need_of (cs: list Z) : list Z := map (fun s => if existsb (Z.eqb s) cs then 1 else 0) blkM_ix.

Lemma blkM_ix_len : Zlength blkM_ix = 53.
Proof. reflexivity. Qed.

Lemma blkM_ix_Znth : forall i, 0 <= i < 53 -> Znth i blkM_ix = i.
Proof.
  intros i Hi. unfold blkM_ix. rewrite Znth_map by (change (Zlength (seq 0 53)) with 53; lia).
  unfold Znth. destruct (ZArith_dec.Z_lt_dec i 0); [lia |]. rewrite seq_nth by lia. lia.
Qed.

Lemma need_of_len : forall cs, Zlength (need_of cs) = 53.
Proof. intros. unfold need_of. rewrite Zlength_map. reflexivity. Qed.

Lemma need_of_range : forall cs, Forall (fun x => 0 <= x <= 1) (need_of cs).
Proof.
  intros. unfold need_of. apply Forall_map. apply Forall_forall. intros x _. cbv beta.
  destruct (existsb _ _); lia.
Qed.

Lemma need_of_nil : need_of [] = Zrepeat 0 53.
Proof. reflexivity. Qed.

Lemma need_of_Znth : forall cs i, 0 <= i < 53 ->
  Znth i (need_of cs) = if existsb (Z.eqb i) cs then 1 else 0.
Proof.
  intros. unfold need_of. rewrite Znth_map by (rewrite blkM_ix_len; lia). rewrite blkM_ix_Znth by lia.
  reflexivity.
Qed.

Lemma need_of_snoc : forall cs c, 0 <= c < 53 -> upd_Znth c (need_of cs) 1 = need_of (cs ++ [c]).
Proof.
  intros cs c Hc. apply Znth_eq_ext.
  - rewrite Zlength_upd_Znth, !need_of_len. reflexivity.
  - intros i Hi. rewrite Zlength_upd_Znth, need_of_len in Hi.
    rewrite (need_of_Znth (cs ++ [c])) by lia. rewrite existsb_app. cbn [existsb].
    destruct (Z.eq_dec i c) as [-> | Hne].
    + rewrite upd_Znth_same by (rewrite need_of_len; lia). rewrite Z.eqb_refl. cbn. destruct (existsb _ _); reflexivity.
    + rewrite upd_Znth_diff by (rewrite ?need_of_len; lia). rewrite need_of_Znth by lia.
      apply Z.eqb_neq in Hne. rewrite Hne. cbn. destruct (existsb _ _); reflexivity.
Qed.

Lemma need_of_in : forall cs c, In c cs -> 0 <= c < 53 -> zn (need_of cs) c <> 0.
Proof.
  intros cs c Hin Hc. unfold zn. replace (nth (Z.to_nat c) (need_of cs) 0) with (Znth c (need_of cs)).
  - rewrite need_of_Znth by lia.
    assert (existsb (Z.eqb c) cs = true) as -> by (apply existsb_exists; exists c; split; auto; apply Z.eqb_refl).
    lia.
  - unfold Znth. destruct (ZArith_dec.Z_lt_dec c 0); [lia |]. reflexivity.
Qed.

(* the code of a sequence is within the table's symbols (the first part of WM_BlkCodes.sq_code_facts) *)
Lemma blkM_lcode_bound : forall b c x, 0 <= lcode b c x <= Z.of_nat c.
Proof. intros b c x. induction c; cbn [lcode]; [lia | destruct (_ <=? x); lia]. Qed.

Lemma blkM_code_range : forall ty sq, seq_ok sq -> 0 <= ty <= 2 -> 0 <= sq_code ty sq <= ty_max ty.
Proof.
  intros ty sq Hs Hty. unfold sq_code, ty_max, seq_ok, ll_code_of, ml_code_of in *.
  destruct (ty =? 0); [| destruct (ty =? 1)].
  - pose proof (blkM_lcode_bound LL_base_tab 35 (sq_ll sq)). lia.
  - pose proof (Z.log2_nonneg (sq_ov sq)).
    assert (Z.log2 (sq_ov sq) < 32) by (apply Z.log2_lt_pow2; lia). lia.
  - pose proof (blkM_lcode_bound ML_base_tab 52 (sq_ml sq)). lia.
Qed.
