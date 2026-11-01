(* w_compressed_block, drawing the sequences (plain Coq): the C's repeat-offset update against resolve_offset, the
   w_hist copy loop
   against lz_copy, and gen_ok (the sequences drawn so far execute to the content written so far). *)
Require Import Zstd.proof.harness.writer.model.WM_BlkDefs.

(* an Offset_Value the C may choose gives off, and the C's update of st->rep is the decoder's *)
Lemma resolve_c : forall rep ll off ov,
  rep_ok rep -> 1 <= off < 2 ^ 32 -> 0 <= ll -> ov_valid rep ll off ov ->
  resolve_offset rep ll ov = Some (off, c_rep_upd rep ll ov off) /\ rep_ok (c_rep_upd rep ll ov off).
Proof.
  intros [[r1 r2] r3] ll off ov Hr Hoff Hll Hv.
  unfold rep_ok in *; unfold ov_valid in Hv; unfold resolve_offset, c_rep_upd.
  destruct Hv as [-> | [[Hl Hc] | [Hl Hc]]].
  - assert (E: off + 3 >? 3 = true) by (apply Z.gtb_lt; lia). rewrite E. simpl.
    replace (off + 3 - 3) with off by lia. split; [reflexivity | lia].
  - assert (E: ll =? 0 = false) by (apply Z.eqb_neq; lia). rewrite E.
    destruct Hc as [[-> ->] | [[-> ->] | [-> ->]]]; simpl; split; auto; lia.
  - subst ll. destruct Hc as [[-> ->] | [[-> ->] | [-> [H1 <-]]]]; simpl; try (split; auto; lia).
    assert (E: r1 - 1 <=? 0 = false) by (apply Z.leb_gt; lia). rewrite E. split; [reflexivity | lia].
Qed.

Lemma lz_copy_prefix : forall hist off m cur, exists t, lz_copy hist cur off m = cur ++ t.
Proof.
  intros hist off m; induction m as [|m IH]; intros cur; simpl.
  - exists []. rewrite app_nil_r. reflexivity.
  - destruct (IH (cur ++ [byte_at (hist ++ cur) (Zlength hist + Zlength cur - off)])) as [t Ht].
    rewrite Ht, <- app_assoc. eexists. reflexivity.
Qed.

Lemma lz_copy_length : forall hist off m cur, length (lz_copy hist cur off m) = (length cur + m)%nat.
Proof.
  intros hist off m; induction m as [|m IH]; intros cur; simpl.
  - lia.
  - rewrite IH, app_length. simpl. lia.
Qed.

Lemma lz_copy_app : forall hist cur off m, lz_copy hist cur off m = cur ++ lz_tail hist cur off m.
Proof.
  intros hist cur off m. unfold lz_tail.
  destruct (lz_copy_prefix hist off m cur) as [t Ht]. rewrite Ht.
  rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity.
Qed.

Lemma lz_tail_len : forall hist cur off m, Zlength (lz_tail hist cur off m) = Z.of_nat m.
Proof.
  intros hist cur off m. unfold lz_tail.
  rewrite Zlength_correct, skipn_length, lz_copy_length. f_equal. lia.
Qed.

(* one more byte of the copy (the C's w_hist[*hn] = w_hist[*hn - off]) *)
Lemma lz_copy_snoc : forall hist cur off m,
  lz_copy hist cur off (S m) =
  lz_copy hist cur off m ++
    [byte_at (hist ++ lz_copy hist cur off m) (Zlength hist + Zlength (lz_copy hist cur off m) - off)].
Proof.
  intros hist cur off m. revert cur; induction m as [|m IH]; intros cur.
  - reflexivity.
  - change (lz_copy hist cur off (S (S m))) with
      (lz_copy hist (cur ++ [byte_at (hist ++ cur) (Zlength hist + Zlength cur - off)]) off (S m)).
    rewrite IH. reflexivity.
Qed.

Lemma lz_copy_bytes : forall hist cur off m,
  bytes_ok hist -> bytes_ok cur -> bytes_ok (lz_copy hist cur off m).
Proof.
  intros hist cur off m Hh. revert cur; induction m as [|m IH]; intros cur Hc; simpl.
  - exact Hc.
  - apply IH. unfold bytes_ok in *. apply Forall_app. split; [exact Hc |].
    constructor; [| constructor]. unfold byte_at.
    destruct (nth_in_or_default (Z.to_nat (Zlength hist + Zlength cur - off)) (hist ++ cur) 0) as [Hi | ->].
    + rewrite Forall_forall in Hh, Hc. apply in_app_or in Hi. destruct Hi; auto.
    + unfold is_byte; lia.
Qed.

Lemma gen_nil : forall wsize rep0 hist out, gen_ok wsize rep0 hist out [] [] [] rep0.
Proof.
  intros wsize rep0 hist out Y. simpl. rewrite app_nil_r. reflexivity.
Qed.

Lemma exec_seqs_app : forall wsize s1 s2 rep hist lits out,
  exec_seqs wsize rep hist lits out (s1 ++ s2) =
  match exec_seqs wsize rep hist lits out s1 with
  | Some (o, l, r) => exec_seqs wsize r hist l o s2
  | None => None
  end.
Proof.
  intros wsize s1; induction s1 as [|sq s1 IH]; intros s2 rep hist lits out; simpl.
  - reflexivity.
  - destruct (sq_ll sq >? Zlength lits); [reflexivity |].
    destruct (resolve_offset rep (sq_ll sq) (sq_ov sq)) as [[o r]|]; [| reflexivity].
    destruct (o >? _); [reflexivity |]. destruct (o >? _); [reflexivity |]. apply IH.
Qed.

(* one more sequence: its literals L, then a match of ml bytes at offset off *)
Lemma gen_step : forall wsize rep0 hist out lits seqs cont rep L ll ml ov off rep',
  gen_ok wsize rep0 hist out lits seqs cont rep ->
  Zlength L = ll -> 0 <= ml ->
  resolve_offset rep ll ov = Some (off, rep') ->
  off <= Zlength hist + Zlength out + Zlength cont + ll -> off <= wsize + Zlength hist ->
  gen_ok wsize rep0 hist out (lits ++ L) (seqs ++ [{| sq_ll := ll; sq_ml := ml; sq_ov := ov |}])
    (cont ++ L ++ lz_tail hist (out ++ cont ++ L) off (Z.to_nat ml)) rep'.
Proof.
  intros wsize rep0 hist out lits seqs cont rep L ll ml ov off rep' Hg HL Hml Hres Hoff1 Hoff2 Y.
  rewrite exec_seqs_app, <- app_assoc, Hg. simpl.
  assert (E1: ll >? Zlength (L ++ Y) = false).
  { rewrite Z.gtb_ltb; apply Z.ltb_ge. rewrite <- HL, !Zlength_correct, app_length. lia. }
  rewrite E1.
  assert (Hn: Z.to_nat ll = length L) by (rewrite <- HL, Zlength_correct; lia).
  rewrite Hn, firstn_app, firstn_all, Nat.sub_diag, firstn_O, app_nil_r.
  rewrite skipn_app, skipn_all, Nat.sub_diag, skipn_O. simpl. rewrite Hres.
  assert (E2: off >? Zlength hist + Zlength ((out ++ cont) ++ L) = false).
  { rewrite Z.gtb_ltb; apply Z.ltb_ge. rewrite !Zlength_correct, !app_length in *. lia. }
  assert (E3: off >? wsize + Zlength hist = false) by (rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
  rewrite E2, E3. simpl. rewrite lz_copy_app, !app_assoc. reflexivity.
Qed.

(* every lemma above together *)
Theorem wm_blkgen_all :
  (forall rep ll off ov, rep_ok rep -> 1 <= off < 2 ^ 32 -> 0 <= ll -> ov_valid rep ll off ov ->
     resolve_offset rep ll ov = Some (off, c_rep_upd rep ll ov off) /\ rep_ok (c_rep_upd rep ll ov off)) /\
  (forall hist cur off m, lz_copy hist cur off m = cur ++ lz_tail hist cur off m) /\
  (forall hist cur off m, Zlength (lz_tail hist cur off m) = Z.of_nat m) /\
  (forall hist cur off m, lz_copy hist cur off (S m) = lz_copy hist cur off m ++
     [byte_at (hist ++ lz_copy hist cur off m) (Zlength hist + Zlength (lz_copy hist cur off m) - off)]) /\
  (forall hist cur off m, bytes_ok hist -> bytes_ok cur -> bytes_ok (lz_copy hist cur off m)) /\
  (forall wsize rep0 hist out, gen_ok wsize rep0 hist out [] [] [] rep0) /\
  (forall wsize rep0 hist out lits seqs cont rep L ll ml ov off rep',
     gen_ok wsize rep0 hist out lits seqs cont rep -> Zlength L = ll -> 0 <= ml ->
     resolve_offset rep ll ov = Some (off, rep') ->
     off <= Zlength hist + Zlength out + Zlength cont + ll -> off <= wsize + Zlength hist ->
     gen_ok wsize rep0 hist out (lits ++ L) (seqs ++ [{| sq_ll := ll; sq_ml := ml; sq_ov := ov |}])
       (cont ++ L ++ lz_tail hist (out ++ cont ++ L) off (Z.to_nat ml)) rep').
Proof.
  exact (conj resolve_c (conj lz_copy_app (conj lz_tail_len (conj lz_copy_snoc
    (conj lz_copy_bytes (conj gen_nil gen_step)))))).
Qed.
