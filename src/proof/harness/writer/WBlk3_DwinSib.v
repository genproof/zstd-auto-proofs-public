(* Local copy of the proofs of parts 1 and 2 of WM3_Dwin.wm3_dwin_all (helpers renamed dw_ -> dws_), used by the
   block's proof: gen_step3_l = WM3_Dwin.gen_step3, decode_block_ok_w_l = WM3_Dwin.decode_block_ok_w (same
   statements). *)
Require Import Zstd.proof.harness.writer.model.WM_BlkDefs.
Require Import Zstd.proof.model.Params.
Require Import Zstd.proof.harness.writer.model.WM3_Dwin.

Lemma dws_lz_copy_prefix : forall hist off m cur, exists t, lz_copy hist cur off m = cur ++ t.
Proof.
  intros hist off m; induction m as [|m IH]; intros cur; simpl.
  - exists []. rewrite app_nil_r. reflexivity.
  - destruct (IH (cur ++ [byte_at (hist ++ cur) (Zlength hist + Zlength cur - off)])) as [t Ht].
    rewrite Ht, <- app_assoc. eexists. reflexivity.
Qed.

Lemma dws_lz_copy_app : forall hist cur off m, lz_copy hist cur off m = cur ++ lz_tail hist cur off m.
Proof.
  intros hist cur off m. unfold lz_tail.
  destruct (dws_lz_copy_prefix hist off m cur) as [t Ht]. rewrite Ht.
  rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity.
Qed.

Lemma dws_exec_seqs_app : forall wsize s1 s2 rep hist lits out,
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

Lemma dws_exec_seqs_w_app : forall wsize s1 s2 rep hist lits out,
  exec_seqs_w wsize rep hist lits out (s1 ++ s2) =
  match exec_seqs_w wsize rep hist lits out s1 with
  | Some (o, l, r) => exec_seqs_w wsize r hist l o s2
  | None => None
  end.
Proof.
  intros wsize s1; induction s1 as [|sq s1 IH]; intros s2 rep hist lits out; simpl.
  - reflexivity.
  - destruct (sq_ll sq >? Zlength lits); [reflexivity |].
    destruct (resolve_offset rep (sq_ll sq) (sq_ov sq)) as [[o r]|]; [| reflexivity].
    destruct (o >? _); [reflexivity |]. destruct (andb _ _); [reflexivity |]. apply IH.
Qed.

Lemma dws_gen_step : forall wsize rep0 hist out lits seqs cont rep L ll ml ov off rep',
  gen_ok wsize rep0 hist out lits seqs cont rep ->
  Zlength L = ll -> 0 <= ml ->
  resolve_offset rep ll ov = Some (off, rep') ->
  off <= Zlength hist + Zlength out + Zlength cont + ll -> off <= wsize + Zlength hist ->
  gen_ok wsize rep0 hist out (lits ++ L) (seqs ++ [{| sq_ll := ll; sq_ml := ml; sq_ov := ov |}])
    (cont ++ L ++ lz_tail hist (out ++ cont ++ L) off (Z.to_nat ml)) rep'.
Proof.
  intros wsize rep0 hist out lits seqs cont rep L ll ml ov off rep' Hg HL Hml Hres Hoff1 Hoff2 Y.
  rewrite dws_exec_seqs_app, <- app_assoc, Hg. simpl.
  assert (E1: ll >? Zlength (L ++ Y) = false).
  { rewrite Z.gtb_ltb; apply Z.ltb_ge. rewrite <- HL, !Zlength_correct, app_length. lia. }
  rewrite E1.
  assert (Hn: Z.to_nat ll = length L) by (rewrite <- HL, Zlength_correct; lia).
  rewrite Hn, firstn_app, firstn_all, Nat.sub_diag, firstn_O, app_nil_r.
  rewrite skipn_app, skipn_all, Nat.sub_diag, skipn_O. simpl. rewrite Hres.
  assert (E2: off >? Zlength hist + Zlength ((out ++ cont) ++ L) = false).
  { rewrite Z.gtb_ltb; apply Z.ltb_ge. rewrite !Zlength_correct, !app_length in *. lia. }
  assert (E3: off >? wsize + Zlength hist = false) by (rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
  rewrite E2, E3. simpl. rewrite dws_lz_copy_app, !app_assoc. reflexivity.
Qed.

Lemma dws_gen_step_w : forall wsize rep0 hist out lits seqs cont rep L ll ml ov off rep',
  gen_ok_w wsize rep0 hist out lits seqs cont rep ->
  Zlength L = ll -> 0 <= ml ->
  resolve_offset rep ll ov = Some (off, rep') ->
  off <= Zlength hist + Zlength out + Zlength cont + ll ->
  off_dwin wsize (Zlength out + Zlength cont + ll) ml off ->
  gen_ok_w wsize rep0 hist out (lits ++ L) (seqs ++ [{| sq_ll := ll; sq_ml := ml; sq_ov := ov |}])
    (cont ++ L ++ lz_tail hist (out ++ cont ++ L) off (Z.to_nat ml)) rep'.
Proof.
  intros wsize rep0 hist out lits seqs cont rep L ll ml ov off rep' Hg HL Hml Hres Hoff1 Hdw Y.
  rewrite dws_exec_seqs_w_app, <- app_assoc, Hg. simpl.
  assert (E1: ll >? Zlength (L ++ Y) = false).
  { rewrite Z.gtb_ltb; apply Z.ltb_ge. rewrite <- HL, !Zlength_correct, app_length. lia. }
  rewrite E1.
  assert (Hn: Z.to_nat ll = length L) by (rewrite <- HL, Zlength_correct; lia).
  rewrite Hn, firstn_app, firstn_all, Nat.sub_diag, firstn_O, app_nil_r.
  rewrite skipn_app, skipn_all, Nat.sub_diag, skipn_O. simpl. rewrite Hres.
  assert (HZ: Zlength ((out ++ cont) ++ L) = Zlength out + Zlength cont + ll).
  { rewrite <- HL, !Zlength_correct, !app_length. lia. }
  assert (E2: off >? Zlength hist + Zlength ((out ++ cont) ++ L) = false).
  { rewrite Z.gtb_ltb; apply Z.ltb_ge. lia. }
  assert (E3: ((off >? wsize) && negb ((off >? Zlength ((out ++ cont) ++ L)) &&
                (Zlength ((out ++ cont) ++ L) + ml <=? wsize)))%bool = false).
  { rewrite HZ. unfold off_dwin in Hdw. destruct (Z.ltb_spec wsize off) as [Hlt|Hge].
    - destruct (Hdw Hlt) as [Ha Hb].
      replace (off >? Zlength out + Zlength cont + ll) with true by (symmetry; apply Z.gtb_lt; lia).
      replace (Zlength out + Zlength cont + ll + ml <=? wsize) with true by (symmetry; apply Z.leb_le; lia).
      apply Bool.andb_false_r.
    - replace (off >? wsize) with false by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; lia). reflexivity. }
  rewrite E2, E3. simpl. rewrite dws_lz_copy_app, !app_assoc. reflexivity.
Qed.

Lemma dws_decode_block_ok_w : forall st hist out lb sb bsm wsize lits seqs hnew tabs cont trail rep',
  lit_ok (st_huf st) bsm lits hnew lb ->
  seqsec_ok (st_seq st) seqs tabs sb ->
  exec_seqs_w wsize (st_rep st) hist lits out seqs = Some (out ++ cont, trail, rep') ->
  Zlength (lb ++ sb) <= bsm -> Zlength (cont ++ trail) <= bsm ->
  decode_block_w st hist out (lb ++ sb) bsm wsize =
    Some ({| st_huf := hnew; st_seq := tabs; st_rep := rep' |}, cont ++ trail).
Proof.
  intros st hist out lb sb bsm wsize lits seqs hnew tabs cont trail rep' Hlit Hseq Hex Hlen Hc.
  destruct Hseq as [_ [Hsb [hused [Hhdr Hstr]]]].
  destruct Hlit as [_ Hlit].
  specialize (Hlit sb Hsb).
  unfold decode_block_w.
  destruct (Zlength (lb ++ sb) >? bsm) eqn:E1; [apply Z.gtb_lt in E1; lia |].
  rewrite Hlit.
  rewrite Zlength_correct, Nat2Z.id, skipn_app, skipn_all, Nat.sub_diag, skipn_O; simpl app.
  rewrite Hhdr.
  assert (Hs: (if Zlength seqs =? 0 then Some nil else
     match tabs with
     | Some (tLL, tOF, tML) => decode_seq_stream tLL tOF tML (skipn (Z.to_nat hused) sb) (Zlength seqs)
     | None => None
     end) = Some seqs).
  { destruct Hstr as [-> | [tLL [tOF [tML [-> Hd]]]]]; [reflexivity |].
    destruct (Zlength seqs =? 0) eqn:E2; [| exact Hd].
    apply Z.eqb_eq, Zlength_nil_inv in E2; subst; reflexivity. }
  rewrite Hs, Hex.
  rewrite <- app_assoc, skipn_app, skipn_all, Nat.sub_diag, skipn_O; simpl app.
  destruct (Zlength (cont ++ trail) >? bsm) eqn:E3; [apply Z.gtb_lt in E3; lia |].
  reflexivity.
Qed.

Lemma gen_step3_l : forall wsize rep0 hist out lits seqs cont rep L ll ml ov off rep',
  gen_ok3 wsize rep0 hist out lits seqs cont rep ->
  Zlength L = ll -> 0 <= ml ->
  resolve_offset rep ll ov = Some (off, rep') ->
  off <= Zlength hist + Zlength out + Zlength cont + ll -> off <= wsize + Zlength hist ->
  off_dwin wsize (Zlength out + Zlength cont + ll) ml off ->
  gen_ok3 wsize rep0 hist out (lits ++ L) (seqs ++ [{| sq_ll := ll; sq_ml := ml; sq_ov := ov |}])
    (cont ++ L ++ lz_tail hist (out ++ cont ++ L) off (Z.to_nat ml)) rep'.
Proof.
  intros wsize rep0 hist out lits seqs cont rep L ll ml ov off rep' [Hg Hw] HL Hml Hres Hoff1 Hoff2 Hdw.
  split; [eapply dws_gen_step | eapply dws_gen_step_w]; eauto.
Qed.

Lemma decode_block_ok_w_l : forall st hist out lb sb bsm wsize lits seqs hnew tabs cont trail rep',
  lit_ok (st_huf st) bsm lits hnew lb ->
  seqsec_ok (st_seq st) seqs tabs sb ->
  exec_seqs_w wsize (st_rep st) hist lits out seqs = Some (out ++ cont, trail, rep') ->
  Zlength (lb ++ sb) <= bsm -> Zlength (cont ++ trail) <= bsm ->
  decode_block_w st hist out (lb ++ sb) bsm wsize =
    Some ({| st_huf := hnew; st_seq := tabs; st_rep := rep' |}, cont ++ trail).
Proof. exact dws_decode_block_ok_w. Qed.
