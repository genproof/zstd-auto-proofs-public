(* The sequences section header as zstd reads it (ExBlock.x_seq_header with the C-exact FSE_readNCount) is the
   format model's (Block.decode_seq_header) wherever the latter reads it, and the tables it leaves have the
   format's codes (of_ok).  Plain Coq. *)
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Import ListNotations.
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Bitstream Zstd.proof.model.BitsFast Zstd.proof.model.Fse.
Require Import Zstd.proof.model.NCount Zstd.proof.model.Huffman Zstd.proof.model.Block.
Require Import Zstd.proof.model.ExHuf Zstd.proof.model.ExCSeq Zstd.proof.model.ExBlock.
Require Import Zstd.proof.model.ExAgreeDefs Zstd.proof.model.ExAgreeBlkDefs.
Local Open Scope Z_scope.


(* ---------- the symbols of a table built by fse_build ---------- *)

(* every cell of fse_build norm log is a symbol of norm or the initial 0: so its symbols lie in
   [0, M] as soon as norm has at most M + 1 symbols *)
Section BuildSyms.
Variables (norm: list Z) (log M: Z).
Let SymOk (x: Z) : Prop := 0 <= x <= M.

Lemma upd_Forall {A} (P: A -> Prop) (l: list A) (i: nat) (x: A) :
  Forall P l -> P x -> Forall P (upd l i x).
Proof.
  revert i; induction l as [|y l IH]; intros i Hl Hx; destruct i; simpl; auto;
    inversion Hl; subst; constructor; auto.
Qed.

Lemma sym_of_nat_ok (s: nat) : Zlength norm <= M + 1 -> (s < length norm)%nat -> SymOk (Z.of_nat s).
Proof.
  intros Hlen Hs. unfold SymOk. rewrite Zlength_correct in Hlen. lia.
Qed.

Lemma nth_nonzero_lt (s: nat) : nth s norm 0 <> 0 -> (s < length norm)%nat.
Proof.
  intros H. destruct (Nat.lt_ge_cases s (length norm)) as [?|Hge]; auto.
  rewrite nth_overflow in H by exact Hge. congruence.
Qed.

Lemma place_low_syms (s n: nat) (tab: list Z) (high: Z) : Zlength norm <= M + 1 ->
  Forall SymOk tab -> Forall SymOk (fst (place_low norm s n tab high)).
Proof.
  intros Hlen; revert s tab high; induction n as [|n IH]; intros s tab high Ht; simpl; auto.
  destruct (nth s norm 0 =? -1) eqn:E; apply IH; auto.
  apply upd_Forall; auto. apply sym_of_nat_ok; auto; apply nth_nonzero_lt.
  apply Z.eqb_eq in E. lia.
Qed.

Lemma spread_one_syms (k: nat) (sy high: Z) (tab: list Z) (pos: Z) :
  SymOk sy -> Forall SymOk tab -> Forall SymOk (fst (spread_one log k sy high tab pos)).
Proof.
  revert tab pos; induction k as [|k IH]; intros tab pos Hs Ht; simpl; auto.
  apply IH; auto. apply upd_Forall; auto.
Qed.

Lemma spread_syms (s n: nat) (high: Z) (tab: list Z) (pos: Z) : Zlength norm <= M + 1 ->
  Forall SymOk tab -> Forall SymOk (spread norm log s n high tab pos).
Proof.
  intros Hlen; revert s tab pos; induction n as [|n IH]; intros s tab pos Ht; simpl; auto.
  destruct (nth s norm 0 >? 0) eqn:E.
  - destruct (spread_one log (Z.to_nat (nth s norm 0)) (Z.of_nat s) high tab pos) as [tab' pos'] eqn:E2.
    apply IH. change tab' with (fst (tab', pos')). rewrite <- E2.
    apply spread_one_syms; auto. apply sym_of_nat_ok; auto; apply nth_nonzero_lt.
    apply Z.gtb_lt in E. lia.
  - apply IH; auto.
Qed.

Lemma states_syms (tab next: list Z) :
  map fe_sym (states log tab next) = tab.
Proof.
  revert next; induction tab as [|x tab IH]; intros next; simpl; auto. f_equal; auto.
Qed.

Lemma fse_build_syms : 0 <= M -> Zlength norm <= M + 1 -> Forall (fun e => 0 <= fe_sym e <= M) (ft_cells (fse_build norm log)).
Proof.
  intros HM Hlen. unfold fse_build.
  destruct (place_low norm 0 (length norm) (repeat 0 (Z.to_nat (2 ^ log))) (2 ^ log - 1)) as [tab high] eqn:E.
  simpl. apply Forall_forall. intros e He.
  assert (Hs : Forall SymOk (map fe_sym (states log (spread norm log 0 (length norm) high tab 0)
                   (map (fun c => if c =? -1 then 1 else c) norm)))).
  2:{ rewrite Forall_forall in Hs. apply (Hs (fe_sym e)), in_map, He. }
  rewrite states_syms.
  apply spread_syms; auto. change tab with (fst (tab, high)). rewrite <- E.
  apply place_low_syms; auto. apply Forall_forall. intros x Hx. apply repeat_spec in Hx. subst. unfold SymOk. lia.
Qed.
End BuildSyms.

(* ---------- one table: zstd's ZSTD_buildSeqTable is the format's seq_table ---------- *)

Lemma Forall_skipn' {A} (P: A -> Prop) (n: nat) (l: list A) : Forall P l -> Forall P (skipn n l).
Proof.
  revert l; induction n as [|n IH]; intros l Hl; simpl; auto. destruct l; auto. inversion Hl; auto.
Qed.

Lemma byte_at_nonneg (b: list Z) (i: Z) : bytes_ok b -> 0 <= byte_at b i.
Proof.
  intros Hb. unfold byte_at. destruct (Nat.lt_ge_cases (Z.to_nat i) (length b)) as [Hl|Hl].
  - assert (Hin := nth_In b 0 Hl). unfold bytes_ok in Hb. rewrite Forall_forall in Hb. apply Hb in Hin. unfold is_byte in Hin. lia.
  - rewrite nth_overflow by exact Hl. lia.
Qed.

Lemma forallb_syms (t: fse_table) (M: Z) :
  forallb (fun e => andb (0 <=? fe_sym e) (fe_sym e <=? M)) (ft_cells t) = true ->
  Forall (fun e => 0 <= fe_sym e <= M) (ft_cells t).
Proof.
  intros H. apply Forall_forall. intros e He. rewrite forallb_forall in H. apply H in He.
  apply Bool.andb_true_iff in He. destruct He as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

Lemma LL_predef_syms : Forall (fun e => 0 <= fe_sym e <= MaxLL) (ft_cells LL_predef).
Proof. apply forallb_syms. vm_compute. reflexivity. Qed.
Lemma OF_predef_syms : Forall (fun e => 0 <= fe_sym e <= MaxOff) (ft_cells OF_predef).
Proof. apply forallb_syms. vm_compute. reflexivity. Qed.
Lemma ML_predef_syms : Forall (fun e => 0 <= fe_sym e <= MaxML) (ft_cells ML_predef).
Proof. apply forallb_syms. vm_compute. reflexivity. Qed.

(* zstd's FSE_readNCount wrapper of the exact model (ExBlock's, on the C body) is ExHuf's *)
Lemma x_ncount_exhuf (s: list Z) (maxsv: Z) : ExBlock.x_ncount ncount_c s maxsv = ExHuf.x_ncount s maxsv.
Proof. reflexivity. Qed.

Lemma seq_table_agree : ncount_agree ->
  forall (mode: Z) (predef: fse_table) (prev: option fse_table) (max maxLog: Z) (b: list Z) t k,
  0 <= max <= 255 -> bytes_ok b ->
  Forall (fun e => 0 <= fe_sym e <= max) (ft_cells predef) ->
  (forall p, prev = Some p -> Forall (fun e => 0 <= fe_sym e <= max) (ft_cells p)) ->
  seq_table mode predef prev max maxLog b = Some (t, k) ->
  x_seq_table ncount_c mode predef prev max maxLog b = Some (t, k) /\
  Forall (fun e => 0 <= fe_sym e <= max) (ft_cells t).
Proof.
  intros Hnc mode predef prev max maxLog b t k Hmax Hb Hpre Hprev H.
  unfold seq_table in H; unfold x_seq_table.
  destruct (mode =? 0); [inversion H; subst; auto|].
  destruct (mode =? 1).
  { destruct (Zlength b <? 1); [discriminate|].
    destruct (byte_at b 0 >? max) eqn:E; [discriminate|].
    inversion H; subst. split; auto. rewrite Z.gtb_ltb, Z.ltb_ge in E.
    unfold fse_rle; simpl. constructor; [simpl; pose proof (byte_at_nonneg b 0 Hb); lia | constructor]. }
  destruct (mode =? 3).
  { destruct prev as [p|]; [|discriminate]. inversion H; subst. split; auto. }
  destruct (read_ncount b max) as [[[norm log] size]|] eqn:E; [|discriminate].
  rewrite x_ncount_exhuf, (Hnc _ _ _ Hmax E).
  destruct (log >? maxLog); [discriminate|]. inversion H; subst. split; auto.
  apply fse_build_syms; [lia|].
  unfold read_ncount in E.
  destruct (Zlength b =? 0); [discriminate|].
  destruct (fbits b 0 4 + FSE_MIN_TABLELOG >? FSE_TABLELOG_ABSOLUTE_MAX); [discriminate|].
  match type of E with context [match ?m with _ => _ end] => destruct m as [[[n r] p]|] end; [|discriminate].
  destruct (negb (r =? 1)); [discriminate|].
  destruct (Zlength n >? max + 1) eqn:E2; [discriminate|].
  destruct ((p + 7) / 8 >? Zlength b); [discriminate|].
  inversion E; subst. rewrite Z.gtb_ltb, Z.ltb_ge in E2. lia.
Qed.

Lemma x_seq_header_agree : ncount_agree ->
  forall (prev: option seq_tabs) (b: list Z) (nbSeq: Z) (tabs: option seq_tabs) (hused: Z),
  bytes_ok b -> of_ok prev -> decode_seq_header prev b = Some (nbSeq, tabs, hused) ->
  x_seq_header ncount_c prev b = Some (nbSeq, tabs, hused) /\ of_ok tabs.
Proof.
  intros Hnc prev b nbSeq tabs hused Hb Hprev H.
  unfold decode_seq_header in H; unfold x_seq_header.
  destruct (Zlength b <? 1); [discriminate|].
  match type of H with context [match ?e with pair _ _ => _ end] => destruct e as [[nb pos] ok] end.
  destruct (negb ok); [discriminate|].
  destruct (nb =? 0).
  { destruct (pos =? Zlength b); [|discriminate]. inversion H; subst. auto. }
  destruct (pos + 1 >? Zlength b); [discriminate|].
  destruct (negb (Z.land (byte_at b pos) 3 =? 0)); [discriminate|].
  assert (HpLL : forall p, option_map (fun '(l, _, _) => l) prev = Some p ->
            Forall (fun e => 0 <= fe_sym e <= MaxLL) (ft_cells p)).
  { intros p Hp. destruct prev as [[[l o] m]|]; inversion Hp; subst. apply Hprev. }
  assert (HpOF : forall p, option_map (fun '(_, o, _) => o) prev = Some p ->
            Forall (fun e => 0 <= fe_sym e <= MaxOff) (ft_cells p)).
  { intros p Hp. destruct prev as [[[l o] m]|]; inversion Hp; subst. apply Hprev. }
  assert (HpML : forall p, option_map (fun '(_, _, m) => m) prev = Some p ->
            Forall (fun e => 0 <= fe_sym e <= MaxML) (ft_cells p)).
  { intros p Hp. destruct prev as [[[l o] m]|]; inversion Hp; subst. apply Hprev. }
  destruct (seq_table (Z.shiftr (byte_at b pos) 6) LL_predef _ MaxLL LLFSELog _) as [[tLL k1]|] eqn:E1;
    [|discriminate].
  apply seq_table_agree in E1 as [-> HLL]; auto;
    [|unfold MaxLL; lia | apply Forall_skipn'; exact Hb | exact LL_predef_syms].
  destruct (seq_table (Z.land (Z.shiftr (byte_at b pos) 4) 3) OF_predef _ MaxOff OffFSELog _) as [[tOF k2]|] eqn:E2;
    [|discriminate].
  apply seq_table_agree in E2 as [-> HOF]; auto;
    [|unfold MaxOff; lia | apply Forall_skipn'; exact Hb | exact OF_predef_syms].
  destruct (seq_table (Z.land (Z.shiftr (byte_at b pos) 2) 3) ML_predef _ MaxML MLFSELog _) as [[tML k3]|] eqn:E3;
    [|discriminate].
  apply seq_table_agree in E3 as [-> HML]; auto;
    [|unfold MaxML; lia | apply Forall_skipn'; exact Hb | exact ML_predef_syms].
  inversion H; subst. split; [reflexivity|]. simpl. auto.
Qed.
