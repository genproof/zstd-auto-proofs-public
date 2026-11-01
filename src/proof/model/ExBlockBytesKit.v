(* The pieces of ExBlockBytes.xblock_bytes: every store of the exact block model (ExBlock.x_block) writes a byte
   when the memory it reads holds bytes, and the exact Huffman decoders (ExHuf) emit bytes from a table whose
   cells hold byte symbols (X1) or two-byte sequences (X2), which every table zstd builds does.

   - mb m: the written destination cells and litExtraBuffer of a block memory hold bytes; each copy primitive,
     each sequence, the sequence loop, the last literals and the literals' stores keep it (given that the
     block's input holds bytes: the copies of raw literals read it);
   - xt_good t: the cells of a Huffman table hold bytes (X1) or U16 sequences (X2); the decoders emit bytes from
     such a table, and the tables x_huf_read builds are good (a description has at most 256 weights).
   Plain Coq. *)
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Fse Zstd.proof.model.Huffman Zstd.proof.model.Block.
Require Import Zstd.proof.model.ExHuf Zstd.proof.model.ExBlock.
Local Open Scope Z_scope.

(* ---------- lists of bytes ---------- *)

Lemma xbk_byte_at (l: list Z) (i: Z) : bytes_ok l -> is_byte (byte_at l i).
Proof.
  intros H. unfold byte_at. destruct (Nat.lt_ge_cases (Z.to_nat i) (length l)) as [Hl|Hl].
  - unfold bytes_ok in H. rewrite Forall_forall in H. apply H, nth_In, Hl.
  - rewrite nth_overflow by exact Hl. unfold is_byte. lia.
Qed.

Lemma xbk_app (a b: list Z) : bytes_ok a -> bytes_ok b -> bytes_ok (a ++ b).
Proof. intros. apply Forall_app. auto. Qed.

Lemma xbk_repeat (v: Z) (k: nat) : is_byte v -> bytes_ok (repeat v k).
Proof. intros H. unfold bytes_ok. apply Forall_forall. intros x Hx. apply repeat_spec in Hx. subst. exact H. Qed.

Lemma xbk_firstn (k: nat) (l: list Z) : bytes_ok l -> bytes_ok (firstn k l).
Proof.
  revert l. induction k as [|k IH]; intros l H; [constructor|].
  destruct l as [|x l]; [constructor|]. inversion H; subst. cbn. constructor; [assumption|apply IH; assumption].
Qed.

Lemma xbk_skipn (k: nat) (l: list Z) : bytes_ok l -> bytes_ok (skipn k l).
Proof.
  revert l. induction k as [|k IH]; intros l H; [exact H|].
  destruct l as [|x l]; [constructor|]. inversion H; subst. cbn. apply IH; assumption.
Qed.

Lemma xbk_slice (l: list Z) (i k: Z) : bytes_ok l -> bytes_ok (slice l i k).
Proof. intros H. unfold slice. apply xbk_firstn, xbk_skipn, H. Qed.

(* ---------- the memory of a block ---------- *)

Definition cell_byte (c: option Z) : Prop := match c with Some v => is_byte v | None => True end.

(* the written destination cells and litExtraBuffer hold bytes *)
Definition mb (m: xmem) : Prop := Forall cell_byte (xm_dst m) /\ bytes_ok (xm_lxb m).

Lemma xbk_upd {A} (P: A -> Prop) (l: list A) (i: nat) (x: A) : Forall P l -> P x -> Forall P (upd l i x).
Proof.
  revert i. induction l as [|y l IH]; intros i H Hx; [destruct i; constructor|].
  inversion H; subst. destruct i; cbn; constructor; auto.
Qed.

Lemma xbk_nth_cell (d: list (option Z)) (k: nat) (v: Z) :
  Forall cell_byte d -> nth k d None = Some v -> is_byte v.
Proof.
  intros H E. destruct (Nat.lt_ge_cases k (length d)) as [Hl|Hl].
  - rewrite Forall_forall in H. specialize (H _ (nth_In _ None Hl)). rewrite E in H. exact H.
  - rewrite nth_overflow in E by exact Hl. discriminate.
Qed.

Lemma mb_written (d: list (option Z)) : Forall cell_byte d -> bytes_ok (x_written d).
Proof.
  unfold bytes_ok. induction d as [|c d IH]; intros H; [constructor|].
  inversion H; subst. destruct c as [v|]; cbn; [constructor; auto|constructor].
Qed.

Lemma mb_init (mem L: list Z) : bytes_ok mem -> bytes_ok L -> mb {| xm_dst := map Some mem; xm_lxb := L |}.
Proof.
  intros Hm HL. split; [|exact HL]. cbn [xm_dst]. apply Forall_map.
  eapply Forall_impl; [|exact Hm]. intros a Ha. exact Ha.
Qed.

Section Copies.
Variable src : list Z.
Hypothesis Hsrc : bytes_ok src.

Lemma rd_mb : forall m r i v, mb m -> xm_rd src m r i = Some v -> is_byte v.
Proof.
  intros m r i v [Hd Hl] H. unfold xm_rd in H. destruct (i <? 0); [discriminate|].
  destruct r.
  - eapply xbk_nth_cell; eauto.
  - destruct (i <? Zlength (xm_lxb m)); [|discriminate]. injection H as <-. apply xbk_byte_at, Hl.
  - destruct (i <? Zlength src); [|discriminate]. injection H as <-. apply xbk_byte_at, Hsrc.
Qed.

Lemma wr_mb : forall m r i v m', mb m -> is_byte v -> xm_wr m r i v = Some m' -> mb m'.
Proof.
  intros m r i v m' [Hd Hl] Hv H. unfold xm_wr in H. destruct (i <? 0); [discriminate|].
  destruct r.
  - injection H as <-. split; [cbn [xm_dst]|exact Hl].
    destruct (i <? Zlength (xm_dst m)).
    + apply xbk_upd; auto.
    + apply Forall_app. split; [exact Hd|]. apply Forall_app. split.
      * apply Forall_forall. intros x Hx. apply repeat_spec in Hx. subst. exact I.
      * constructor; [exact Hv|constructor].
  - destruct (i <? Zlength (xm_lxb m)); [|discriminate]. injection H as <-.
    split; [exact Hd|]. cbn [xm_lxb]. apply xbk_upd; auto.
  - discriminate.
Qed.

Lemma fwd_mb : forall k m rd d rs s m', mb m -> xm_fwd src k m rd d rs s = Some m' -> mb m'.
Proof.
  induction k as [|k IH]; intros m rd d rs s m' Hm H; cbn [xm_fwd] in H.
  - injection H as <-. exact Hm.
  - destruct (xm_rd src m rs s) as [v|] eqn:Er; [|discriminate].
    destruct (xm_wr m rd d v) as [m1|] eqn:Ew; [|discriminate].
    eapply IH; [|exact H]. eapply wr_mb; [exact Hm| |exact Ew]. eapply rd_mb; eauto.
Qed.

Lemma rdn_mb : forall k m r i vs, mb m -> xm_rdn src k m r i = Some vs -> bytes_ok vs.
Proof.
  induction k as [|k IH]; intros m r i vs Hm H; cbn [xm_rdn] in H.
  - injection H as <-. constructor.
  - destruct (xm_rd src m r i) as [v|] eqn:Er; [|discriminate].
    destruct (xm_rdn src k m r (i + 1)) as [vs'|] eqn:E; [|discriminate].
    injection H as <-. constructor; [eapply rd_mb; eauto|eapply IH; eauto].
Qed.

Lemma wrn_mb : forall vs m r i m', mb m -> bytes_ok vs -> xm_wrn vs m r i = Some m' -> mb m'.
Proof.
  induction vs as [|v vs IH]; intros m r i m' Hm Hv H; cbn [xm_wrn] in H.
  - injection H as <-. exact Hm.
  - inversion Hv; subst. destruct (xm_wr m r i v) as [m1|] eqn:Ew; [|discriminate].
    eapply IH; [eapply wr_mb; eauto|auto|exact H].
Qed.

Lemma move_mb : forall k m rd d rs s m', mb m -> xm_move src k m rd d rs s = Some m' -> mb m'.
Proof.
  intros k m rd d rs s m' Hm H. unfold xm_move in H.
  destruct (xm_rdn src k m rs s) as [vs|] eqn:E; [|discriminate].
  eapply wrn_mb; [exact Hm|eapply rdn_mb; eauto|exact H].
Qed.

Lemma chunks_mb : forall k m d rs s m', mb m -> xm_chunks16 src k m d rs s = Some m' -> mb m'.
Proof.
  induction k as [|k IH]; intros m d rs s m' Hm H; cbn [xm_chunks16] in H.
  - injection H as <-. exact Hm.
  - destruct (xm_move src 16 m R_dst d rs s) as [m1|] eqn:E; [|discriminate].
    eapply IH; [eapply move_mb; eauto|exact H].
Qed.

Lemma wild_mb : forall m d rs s len srcb4 m', mb m -> xm_wild src m d rs s len srcb4 = Some m' -> mb m'.
Proof.
  intros m d rs s len srcb4 m' Hm H. unfold xm_wild in H.
  destruct (srcb4 && (d - s <? 16))%bool; [eapply fwd_mb|eapply chunks_mb]; eauto.
Qed.

Lemma ov8_mb : forall m op ip off m' op' ip', mb m -> xm_ov8 src m op ip off = Some (m', op', ip') -> mb m'.
Proof.
  intros m op ip off m' op' ip' Hm H. unfold xm_ov8 in H.
  destruct (off <? 8).
  - destruct (xm_fwd src 4 m R_dst op R_dst ip) as [m1|] eqn:E1; [|discriminate].
    destruct (xm_fwd src 4 m1 R_dst (op + 4) R_dst _) as [m2|] eqn:E2; [|discriminate].
    injection H as <- _ _. eapply fwd_mb; [eapply fwd_mb; eauto|eauto].
  - destruct (xm_fwd src 8 m R_dst op R_dst ip) as [m1|] eqn:E1; [|discriminate].
    injection H as <- _ _. eapply fwd_mb; eauto.
Qed.

Lemma safecopy_mb : forall m op oend_w rs ip len srcb4 m', mb m ->
  xm_safecopy src m op oend_w rs ip len srcb4 = Some m' -> mb m'.
Proof.
  intros m op oend_w rs ip len srcb4 m' Hm H. unfold xm_safecopy in H.
  destruct (len <? 8); [eapply fwd_mb; eauto|].
  assert (Hp: forall m1 op1 ip1, (if srcb4 then xm_ov8 src m op ip (op - ip) else Some (m, op, ip)) =
                                 Some (m1, op1, ip1) -> mb m1).
  { intros m1 op1 ip1 E. destruct srcb4; [eapply ov8_mb; eauto|injection E as <- _ _; exact Hm]. }
  destruct (if srcb4 then xm_ov8 src m op ip (op - ip) else Some (m, op, ip)) as [[[m1 op1] ip1]|] eqn:E;
    [|discriminate].
  specialize (Hp _ _ _ eq_refl).
  destruct (oend_w - (op + len) >=? 0); [eapply wild_mb; eauto|].
  destruct (oend_w - op1 >=? 0).
  - destruct (xm_wild src m1 op1 rs ip1 (oend_w - op1) srcb4) as [m2|] eqn:E2; [|discriminate].
    eapply fwd_mb; [eapply wild_mb; eauto|exact H].
  - eapply fwd_mb; eauto.
Qed.

Lemma sdbs_mb : forall m op ip len m', mb m -> xm_sdbs src m op ip len = Some m' -> mb m'.
Proof.
  intros m op ip len m' Hm H. unfold xm_sdbs in H.
  destruct ((len <? 8) || (op - ip >? -8))%bool; [eapply fwd_mb; eauto|].
  destruct ((len >=? 32) && (op - ip <? -16))%bool.
  - destruct (xm_wild src m op R_dst ip (len - 32) false) as [m1|] eqn:E2; [|discriminate].
    eapply fwd_mb; [eapply wild_mb; eauto|exact H].
  - eapply fwd_mb; eauto.
Qed.
End Copies.

(* ---------- the sequences ---------- *)

Section Seqs.
Variable e : xenv.
Hypothesis He : bytes_ok (xe_src e).

Lemma prefix_mb : forall m op mt ml off wo m', mb m -> xm_prefix e m op mt ml off wo = Some m' -> mb m'.
Proof.
  intros m op mt ml off wo m' Hm H. unfold xm_prefix in H. destruct wo as [w|].
  - eapply safecopy_mb; eauto.
  - destruct (off >=? 16); [eapply wild_mb; eauto|].
    destruct (xm_ov8 (xe_src e) m op mt off) as [[[m1 op1] mt1]|] eqn:E; [|discriminate].
    apply ov8_mb in E; auto.
    destruct (ml >? 8); [eapply wild_mb; eauto|injection H as <-; exact E].
Qed.

Lemma match_mb : forall m oLitEnd ml off wo m', mb m -> xm_match e m oLitEnd ml off wo = Some m' -> mb m'.
Proof.
  intros m oLitEnd ml off wo m' Hm H. unfold xm_match in H.
  destruct (off >? oLitEnd - xe_ps e); [|eapply prefix_mb; eauto].
  destruct (off >? oLitEnd - xe_vs e); [discriminate|].
  destruct (xe_de e - (xe_de e + (oLitEnd - off - xe_ps e)) >=? ml); [eapply move_mb; eauto|].
  destruct (xm_move (xe_src e) _ m R_dst oLitEnd R_dst _) as [m1|] eqn:E; [|discriminate].
  eapply prefix_mb; [eapply move_mb; eauto|exact H].
Qed.

Lemma exec_mb : forall m op lr li llim ll ml off m' op' li', mb m ->
  x_exec e m op lr li llim ll ml off = Some (m', op', li') -> mb m'.
Proof.
  intros m op lr li llim ll ml off m' op' li' Hm H. unfold x_exec in H. cbv zeta in H.
  destruct ((llim - li <? ll) || (xe_oend e - XWILDCOPY - op <? ll + ml))%bool.
  - destruct (ll + ml >? xe_oend e - op); [discriminate|].
    destruct (ll >? llim - li); [discriminate|].
    destruct (xm_safecopy (xe_src e) m op (xe_oend e - XWILDCOPY) lr li ll false) as [m1|] eqn:E1; [|discriminate].
    destruct (xm_match e m1 (op + ll) ml off _) as [m2|] eqn:E2; [|discriminate].
    injection H as <- _ _. eapply match_mb; [eapply safecopy_mb; eauto|eauto].
  - destruct (xm_move (xe_src e) 16 m R_dst op lr li) as [m1|] eqn:E1; [|discriminate].
    apply move_mb in E1; auto.
    destruct (if ll >? 16 then xm_wild (xe_src e) m1 (op + 16) lr (li + 16) (ll - 16) false else Some m1)
      as [m2|] eqn:E2; [|discriminate].
    assert (mb m2) by (destruct (ll >? 16); [eapply wild_mb; eauto|injection E2 as <-; exact E1]).
    destruct (xm_match e m2 (op + ll) ml off None) as [m3|] eqn:E3; [|discriminate].
    injection H as <- _ _. eapply match_mb; eauto.
Qed.

Lemma exec_split_mb : forall m op li llim ll ml off m' op' li', mb m ->
  x_exec_split e m op li llim ll ml off = Some (m', op', li') -> mb m'.
Proof.
  intros m op li llim ll ml off m' op' li' Hm H. unfold x_exec_split in H. cbv zeta in H.
  destruct ((llim - li <? ll) || (li + ll - XWILDCOPY - op <? ll + ml))%bool.
  - destruct (ll + ml >? xe_oend e - op); [discriminate|].
    destruct (ll >? llim - li); [discriminate|].
    destruct ((op >? li) && (op <? li + ll))%bool; [discriminate|].
    destruct (xm_sdbs (xe_src e) m op li ll) as [m1|] eqn:E1; [|discriminate].
    destruct (xm_match e m1 (op + ll) ml off _) as [m2|] eqn:E2; [|discriminate].
    injection H as <- _ _. eapply match_mb; [eapply sdbs_mb; eauto|eauto].
  - destruct (xm_move (xe_src e) 16 m R_dst op R_dst li) as [m1|] eqn:E1; [|discriminate].
    apply move_mb in E1; auto.
    destruct (if ll >? 16 then xm_wild (xe_src e) m1 (op + 16) R_dst (li + 16) (ll - 16) false else Some m1)
      as [m2|] eqn:E2; [|discriminate].
    assert (mb m2) by (destruct (ll >? 16); [eapply wild_mb; eauto|injection E2 as <-; exact E1]).
    destruct (xm_match e m2 (op + ll) ml off None) as [m3|] eqn:E3; [|discriminate].
    injection H as <- _ _. eapply match_mb; eauto.
Qed.

Lemma step_mb : forall s ll ml off s', mb (xmm s) -> x_step e s ll ml off = Some s' -> mb (xmm s').
Proof.
  intros s ll ml off s' Hm H. unfold x_step in H. cbv zeta in H.
  destruct (xsp s).
  - destruct (xlim s - xli s <? ll).
    + assert (Hmo: forall m1 op1, (if xlim s - xli s =? 0 then Some (xmm s, xop s) else
          if xlim s - xli s >? xe_oend e - xop s then None else
          match xm_sdbs (xe_src e) (xmm s) (xop s) (xli s) (xlim s - xli s) with
          | Some m => Some (m, xop s + (xlim s - xli s)) | None => None end) = Some (m1, op1) -> mb m1).
      { intros m1 op1 E. destruct (xlim s - xli s =? 0); [injection E as <- _; exact Hm|].
        destruct (xlim s - xli s >? xe_oend e - xop s); [discriminate|].
        destruct (xm_sdbs _ _ _ _ _) as [m2|] eqn:Es; [|discriminate].
        injection E as <- _. eapply sdbs_mb; eauto. }
      destruct (if xlim s - xli s =? 0 then _ else _) as [[m1 op1]|]; [|discriminate].
      specialize (Hmo _ _ eq_refl).
      destruct (x_exec e m1 op1 R_lxb 0 XLITEXTRA _ ml off) as [[[m2 op2] li2]|] eqn:Ex; [|discriminate].
      injection H as <-. cbn [xmm]. eapply exec_mb; eauto.
    + destruct (x_exec_split e (xmm s) (xop s) (xli s) (xlim s) ll ml off) as [[[m2 op2] li2]|] eqn:Ex;
        [|discriminate].
      injection H as <-. cbn [xmm]. eapply exec_split_mb; eauto.
  - destruct (x_exec e (xmm s) (xop s) (xlr s) (xli s) (xlim s) ll ml off) as [[[m2 op2] li2]|] eqn:Ex;
      [|discriminate].
    injection H as <-. cbn [xmm]. eapply exec_mb; eauto.
Qed.

Lemma loop_mb : forall dso cof tLL tOF tML V k st pos rep s s' pos' rep', mb (xmm s) ->
  x_seq_loop dso cof e tLL tOF tML V k st pos rep s = Some (s', pos', rep') -> mb (xmm s').
Proof.
  intros dso cof tLL tOF tML V k. induction k as [|k IH]; intros st pos rep s s' pos' rep' Hm H;
    destruct st as [[sLL sOF] sML]; cbn [x_seq_loop] in H.
  - injection H as <- _ _. exact Hm.
  - destruct (dso tLL tOF tML V (Nat.eqb k 0) sLL sOF sML pos) as [[[sq st1] pos1]|]; [|discriminate].
    destruct (cof rep (sq_ll sq) (sq_ov sq)) as [off rep1].
    destruct (x_step e s (sq_ll sq) (sq_ml sq) off) as [s1|] eqn:Es; [|discriminate].
    eapply IH; [eapply step_mb; eauto|exact H].
Qed.

Lemma last_mb : forall s m op', mb (xmm s) -> x_last e s = Some (m, op') -> mb m.
Proof.
  intros s m op' Hm H. unfold x_last in H. cbv zeta in H.
  destruct (xsp s).
  - destruct (xlim s - xli s >? xe_oend e - xop s); [discriminate|].
    destruct (xm_move (xe_src e) (Z.to_nat (xlim s - xli s)) (xmm s) R_dst (xop s) R_dst (xli s)) as [m1|] eqn:E1;
      [|discriminate].
    cbv iota beta zeta in H.
    destruct (XLITEXTRA - 0 >? _); [discriminate|].
    destruct (xm_fwd _ _ _ _ _ _ _) as [m2|] eqn:E2; [|discriminate].
    injection H as <- _. eapply fwd_mb; [eauto|eapply move_mb; eauto|exact E2].
  - cbv iota beta zeta in H. destruct (_ >? _); [discriminate|].
    destruct (xm_fwd _ _ _ _ _ _ _) as [m2|] eqn:E2; [|discriminate].
    injection H as <- _. eapply fwd_mb; eauto.
Qed.

Lemma seqs_mb : forall dso cof tabs rep bits nbSeq s0 m op' rep', mb (xmm s0) ->
  x_seqs dso cof e tabs rep bits nbSeq s0 = Some (m, op', rep') -> mb m.
Proof.
  intros dso cof tabs rep bits nbSeq s0 m op' rep' Hm H. destruct tabs as [[tLL tOF] tML]. unfold x_seqs in H.
  destruct (negb (Bitstream.bs_okb bits)); [discriminate|].
  destruct (rd bits (Bitstream.bs_total bits) (ft_log tLL)) as [[sLL p1]|]; [|discriminate].
  destruct (rd bits p1 (ft_log tOF)) as [[sOF p2]|]; [|discriminate].
  destruct (rd bits p2 (ft_log tML)) as [[sML p3]|]; [|discriminate].
  destruct (x_seq_loop _ _ _ _ _ _ _ _ _ _ _ _) as [[[s1 pos] r]|] eqn:El; [|discriminate].
  destruct (negb (pos =? 0)); [discriminate|].
  destruct (x_last e s1) as [[m1 o1]|] eqn:Ex; [|discriminate].
  injection H as <- _ _. eapply last_mb; [eapply loop_mb; eauto|exact Ex].
Qed.
End Seqs.

(* ---------- the literals' stores ---------- *)

Lemma lits_store_mb : forall body lits lused m op0 ews bsm cap str m' lr li lim sp,
  bytes_ok body -> bytes_ok lits -> mb m ->
  x_lits_store body lits lused m op0 ews bsm cap str = Some (m', lr, li, lim, sp) -> mb m'.
Proof.
  intros body lits lused m op0 ews bsm cap str m' lr li lim sp Hb Hl Hm H.
  assert (Z0: bytes_ok (repeat 0 32)) by (apply xbk_repeat; unfold is_byte; lia).
  assert (Hv: forall k, bytes_ok (repeat (byte_at body (lused - 1)) k)) by (intros; apply xbk_repeat, xbk_byte_at, Hb).
  unfold x_lits_store in H. cbv zeta in H. revert H.
  match goal with |- (match ?p with pair _ _ => _ end = _) -> _ => destruct p as [[lr0 lb] lbe] end.
  match goal with |- (match ?mz with _ => _ end = _) -> _ =>
    assert (Hz: forall m1, mz = Some m1 -> mb m1);
    [|destruct mz as [m1|]; [specialize (Hz m1 eq_refl)|discriminate]] end.
  { intros m1 E. destruct (x_alloc_loc _ _ _ _); try (injection E as <-; exact Hm).
    - eapply wrn_mb; eauto.
    - destruct (_ <=? 1); [eapply wrn_mb; eauto|injection E as <-; exact Hm]. }
  repeat match goal with
  | |- (match xm_wrn ?vs ?mm ?r ?d with _ => _ end = _) -> _ =>
      let E := fresh "W" in destruct (xm_wrn vs mm r d) as [?|] eqn:E; [apply wrn_mb in E; auto|discriminate]
  | |- (match xm_fwd ?sr ?k ?mm ?rd ?d ?rs ?s with _ => _ end = _) -> _ =>
      let E := fresh "W" in destruct (xm_fwd sr k mm rd d rs s) as [?|] eqn:E; [apply fwd_mb in E; auto|discriminate]
  | |- (match xm_move ?sr ?k ?mm ?rd ?d ?rs ?s with _ => _ end = _) -> _ =>
      let E := fresh "W" in destruct (xm_move sr k mm rd d rs s) as [?|] eqn:E; [apply move_mb in E; auto|discriminate]
  | |- ((if ?c then _ else _) = _) -> _ => destruct c
  | |- (Some _ = Some _) -> _ => let E := fresh in intros E; injection E as <- _ _ _ _; assumption
  end.
Qed.

(* ---------- the Huffman tables and decoders ---------- *)

(* the cells of a table hold bytes (X1) or U16 sequences (X2): the body of ExBlockBytes.xh_good *)
Definition xt_good (t: xhuf) : Prop :=
  Forall (fun c : Z * Z * Z => let '(sq, _, _) := c in 0 <= sq < (if xh_x2 t then 65536 else 256)) (xh_cells t).

Lemma xt_cell (t: xhuf) (v: Z) : xt_good t ->
  0 <= fst (fst (xh_cell t v)) < (if xh_x2 t then 65536 else 256).
Proof.
  intros H. unfold xh_cell. destruct (Nat.lt_ge_cases (Z.to_nat v) (length (xh_cells t))) as [Hl|Hl].
  - unfold xt_good in H. rewrite Forall_forall in H. specialize (H _ (nth_In _ (0, 0, 0) Hl)).
    destruct (nth _ _ _) as [[sq nb] ln]. exact H.
  - rewrite nth_overflow by exact Hl. cbn. destruct (xh_x2 t); lia.
Qed.

(* X1 *)
Lemma x1_sym_b (t: xhuf) (d: xbit) : xt_good t -> xh_x2 t = false -> is_byte (fst (xh_x1_sym t d)).
Proof.
  intros H H2. unfold xh_x1_sym. pose proof (xt_cell t (xb_look_fast d (xh_log t)) H) as C. rewrite H2 in C.
  destruct (xh_cell _ _) as [[sq nb] ln]. exact C.
Qed.

Lemma x1_n_b (t: xhuf) : (forall d, is_byte (fst (xh_x1_sym t d))) ->
  forall k d, bytes_ok (fst (xh_x1_n t d k)).
Proof.
  intros Hs. induction k as [|k IH]; intros d; [constructor|]. cbn [xh_x1_n].
  pose proof (Hs d) as H1. destruct (xh_x1_sym t d) as [c d1].
  pose proof (IH d1) as H2. destruct (xh_x1_n t d1 k) as [l d2]. cbn in *. constructor; auto.
Qed.

Lemma x1_loop4_b (t: xhuf) (s: list Z) : (forall d, is_byte (fst (xh_x1_sym t d))) ->
  forall fuel d rem acc, bytes_ok acc -> bytes_ok (fst (fst (xh_x1_loop4 fuel s t d rem acc))).
Proof.
  intros Hs. induction fuel as [|f IH]; intros d rem acc Ha; [exact Ha|]. cbn [xh_x1_loop4].
  destruct (xb_reload s d) as [st d1]. destruct (_ && _)%bool; [|exact Ha].
  pose proof (x1_n_b t Hs 4 d1) as H4. destruct (xh_x1_n t d1 4) as [l d2].
  apply IH. apply xbk_app; auto.
Qed.

Lemma x1_stream_b (t: xhuf) : (forall d, is_byte (fst (xh_x1_sym t d))) ->
  forall s d rem, bytes_ok (fst (xh_x1_stream t s d rem)).
Proof.
  intros Hs s d rem. unfold xh_x1_stream.
  assert (HA: forall a d1 r, (if 3 <? rem then xh_x1_loop4 (Z.to_nat rem + 1) s t d rem nil
            else let '(_, d) := xb_reload s d in (nil, d, rem)) = (a, d1, r) -> bytes_ok a).
  { intros a d1 r E. destruct (3 <? rem).
    - pose proof (x1_loop4_b t s Hs (Z.to_nat rem + 1) d rem nil ltac:(constructor)) as B.
      rewrite E in B. exact B.
    - destruct (xb_reload s d). injection E as <- _ _. constructor. }
  destruct (if 3 <? rem then _ else _) as [[a d1] r]. specialize (HA _ _ _ eq_refl).
  pose proof (x1_n_b t Hs (Z.to_nat r) d1) as B. destruct (xh_x1_n t d1 (Z.to_nat r)) as [b d2].
  apply xbk_app; auto.
Qed.

(* X2 *)
Lemma x2_sym_b (t: xhuf) (d: xbit) : xt_good t -> xh_x2 t = true -> bytes_ok (fst (xh_x2_sym t d)).
Proof.
  intros H H2. unfold xh_x2_sym. pose proof (xt_cell t (xb_look_fast d (xh_log t)) H) as C. rewrite H2 in C.
  destruct (xh_cell _ _) as [[sq nb] ln]. cbn [fst] in *. apply xbk_firstn.
  constructor; [|constructor; [|constructor]]; unfold is_byte.
  - apply Z.mod_pos_bound. lia.
  - split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia.
Qed.

Lemma x2_last_b (t: xhuf) (d: xbit) : bytes_ok (fst (xh_x2_last t d)).
Proof.
  unfold xh_x2_last. destruct (xh_cell _ _) as [[sq nb] ln]. cbn. constructor; [|constructor].
  unfold is_byte. apply Z.mod_pos_bound. lia.
Qed.

Lemma x2_n_b (t: xhuf) : (forall d, bytes_ok (fst (xh_x2_sym t d))) ->
  forall k d, bytes_ok (fst (xh_x2_n t d k)).
Proof.
  intros Hs. induction k as [|k IH]; intros d; [constructor|]. cbn [xh_x2_n].
  pose proof (Hs d) as H1. destruct (xh_x2_sym t d) as [c d1].
  pose proof (IH d1) as H2. destruct (xh_x2_n t d1 k) as [l d2]. cbn in *. apply xbk_app; auto.
Qed.

Lemma x2_loopr_b (t: xhuf) (s: list Z) (k: nat) (cond: Z -> bool) : (forall d, bytes_ok (fst (xh_x2_sym t d))) ->
  forall fuel d rem acc, bytes_ok acc -> bytes_ok (fst (fst (xh_x2_loopr fuel s t k cond d rem acc))).
Proof.
  intros Hs. induction fuel as [|f IH]; intros d rem acc Ha; [exact Ha|]. cbn [xh_x2_loopr].
  destruct (xb_reload s d) as [st d1]. destruct (_ && _)%bool; [|exact Ha].
  pose proof (x2_n_b t Hs k d1) as H4. destruct (xh_x2_n t d1 k) as [l d2].
  apply IH. apply xbk_app; auto.
Qed.

Lemma x2_loop1_b (t: xhuf) : (forall d, bytes_ok (fst (xh_x2_sym t d))) ->
  forall fuel d rem acc, bytes_ok acc -> bytes_ok (fst (fst (xh_x2_loop1 fuel t d rem acc))).
Proof.
  intros Hs. induction fuel as [|f IH]; intros d rem acc Ha; [exact Ha|]. cbn [xh_x2_loop1].
  destruct (2 <=? rem); [|exact Ha].
  pose proof (Hs d) as H4. destruct (xh_x2_sym t d) as [l d2].
  apply IH. apply xbk_app; auto.
Qed.

Lemma x2_stream_b (t: xhuf) : (forall d, bytes_ok (fst (xh_x2_sym t d))) ->
  forall s d rem, bytes_ok (fst (xh_x2_stream t s d rem)).
Proof.
  intros Hs s d rem. unfold xh_x2_stream. cbv zeta.
  set (fuel := (Z.to_nat rem + 1)%nat).
  assert (HA: forall a d1 r, (if 8 <=? rem then
              if xh_log t <=? 11 then xh_x2_loopr fuel s t 5 (fun r => 9 <? r) d rem nil
              else xh_x2_loopr fuel s t 4 (fun r => 7 <? r) d rem nil
            else let '(_, d) := xb_reload s d in (nil, d, rem)) = (a, d1, r) -> bytes_ok a).
  { intros a d1 r E. destruct (8 <=? rem); [destruct (xh_log t <=? 11)|].
    - pose proof (x2_loopr_b t s 5 (fun r => 9 <? r) Hs fuel d rem nil ltac:(constructor)) as B.
      rewrite E in B. exact B.
    - pose proof (x2_loopr_b t s 4 (fun r => 7 <? r) Hs fuel d rem nil ltac:(constructor)) as B.
      rewrite E in B. exact B.
    - destruct (xb_reload s d). injection E as <- _ _. constructor. }
  destruct (if 8 <=? rem then _ else _) as [[a d1] r]. specialize (HA _ _ _ eq_refl).
  assert (HB: forall b d2 r2, (if 2 <=? r then
              let '(b1, d, rem) := xh_x2_loopr fuel s t 1 (fun r => 2 <=? r) d1 r nil in
              let '(b2, d, rem) := xh_x2_loop1 fuel t d rem nil in (b1 ++ b2, d, rem)
            else (nil, d1, r)) = (b, d2, r2) -> bytes_ok b).
  { intros b d2 r2 E. destruct (2 <=? r); [|injection E as <- _ _; constructor].
    pose proof (x2_loopr_b t s 1 (fun r => 2 <=? r) Hs fuel d1 r nil ltac:(constructor)) as B1.
    destruct (xh_x2_loopr _ _ _ _ _ _ _ _) as [[b1 d3] r3].
    pose proof (x2_loop1_b t Hs fuel d3 r3 nil ltac:(constructor)) as B2.
    destruct (xh_x2_loop1 _ _ _ _ _) as [[b2 d4] r4]. injection E as <- _ _. apply xbk_app; auto. }
  destruct (if 2 <=? r then _ else _) as [[b d2] r2]. specialize (HB _ _ _ eq_refl).
  assert (HC: bytes_ok (fst (if 0 <? r2 then xh_x2_last t d2 else (nil, d2)))).
  { destruct (0 <? r2); [apply x2_last_b|constructor]. }
  destruct (if 0 <? r2 then _ else _) as [c d3]. cbn in *. apply xbk_app; [|apply xbk_app]; auto.
Qed.

(* one stream and four streams *)
Lemma onestream_b (fin: list Z -> xbit -> Z -> list Z * xbit) (src: list Z) (n: Z) (l: list Z) :
  (forall s d r, bytes_ok (fst (fin s d r))) -> xh_1stream fin src n = Some l -> bytes_ok l.
Proof.
  intros Hf H. unfold xh_1stream in H. destruct (xb_init src) as [d|]; [|discriminate].
  pose proof (Hf src d n) as B. destruct (fin src d n) as [l1 d1].
  destruct (xb_end d1); [injection H as <-; exact B|discriminate].
Qed.

Lemma loop4s_b (dec4: xbit -> list Z * xbit) (lim4: Z) (s1 s2 s3 s4: list Z) :
  (forall d, bytes_ok (fst (dec4 d))) ->
  forall fuel d1 d2 d3 d4 o1 o2 o3 o4 D p1 p2 p3 p4,
  bytes_ok o1 -> bytes_ok o2 -> bytes_ok o3 -> bytes_ok o4 ->
  xh_loop4s fuel dec4 lim4 s1 s2 s3 s4 d1 d2 d3 d4 o1 o2 o3 o4 = (D, (p1, p2, p3, p4)) ->
  bytes_ok p1 /\ bytes_ok p2 /\ bytes_ok p3 /\ bytes_ok p4.
Proof.
  intros Hd. induction fuel as [|f IH]; intros d1 d2 d3 d4 o1 o2 o3 o4 D p1 p2 p3 p4 H1 H2 H3 H4 H;
    cbn [xh_loop4s] in H.
  - injection H as _ <- <- <- <-. auto.
  - destruct (negb (Zlength o4 <? lim4)); [injection H as _ <- <- <- <-; auto|].
    pose proof (Hd d1) as B1. destruct (dec4 d1) as [a1 e1].
    pose proof (Hd d2) as B2. destruct (dec4 d2) as [a2 e2].
    pose proof (Hd d3) as B3. destruct (dec4 d3) as [a3 e3].
    pose proof (Hd d4) as B4. destruct (dec4 d4) as [a4 e4].
    destruct (xb_reload_fast s1 e1) as [r1 f1]. destruct (xb_reload_fast s2 e2) as [r2 f2].
    destruct (xb_reload_fast s3 e3) as [r3 f3]. destruct (xb_reload_fast s4 e4) as [r4 f4].
    cbn [fst] in *. destruct (_ && _)%bool.
    + eapply IH; [| | | |exact H]; apply xbk_app; auto.
    + injection H as _ <- <- <- <-. repeat split; apply xbk_app; auto.
Qed.

Lemma fourstreams_b (dec4: xbit -> list Z * xbit) (slack: Z) (fin: list Z -> xbit -> Z -> list Z * xbit)
    (src: list Z) (n: Z) (l: list Z) :
  (forall d, bytes_ok (fst (dec4 d))) -> (forall s d r, bytes_ok (fst (fin s d r))) ->
  xh_4streams dec4 slack fin src n = Some l -> bytes_ok l.
Proof.
  intros Hd Hf H. unfold xh_4streams in H.
  destruct (Zlength src <? 10); [discriminate|]. destruct (n <? 6); [discriminate|].
  destruct (xh_split4 src) as [[[[s1 s2] s3] s4]|]; [|discriminate]. cbv zeta in H.
  destruct (n <? 3 * ((n + 3) / 4)); [discriminate|].
  destruct (xb_init s1) as [d1|]; [|discriminate]. destruct (xb_init s2) as [d2|]; [|discriminate].
  destruct (xb_init s3) as [d3|]; [|discriminate]. destruct (xb_init s4) as [d4|]; [|discriminate].
  match type of H with (match ?p with pair _ _ => _ end = _) =>
    assert (HP: forall D p1 p2 p3 p4, p = (D, (p1, p2, p3, p4)) ->
              bytes_ok p1 /\ bytes_ok p2 /\ bytes_ok p3 /\ bytes_ok p4);
    [|destruct p as [[[[e1 e2] e3] e4] [[[o1 o2] o3] o4]]; destruct (HP _ _ _ _ _ eq_refl) as (B1 & B2 & B3 & B4)] end.
  { intros D p1 p2 p3 p4 E. destruct (8 <=? _).
    - eapply loop4s_b; [exact Hd| | | | |exact E]; constructor.
    - injection E as _ <- <- <- <-. repeat split; constructor. }
  destruct (_ <? Zlength o1); [discriminate|]. destruct (_ <? Zlength o2); [discriminate|].
  destruct (_ <? Zlength o3); [discriminate|].
  pose proof (Hf s1 e1 ((n + 3) / 4 - Zlength o1)) as T1. destruct (fin s1 e1 _) as [t1 f1].
  pose proof (Hf s2 e2 ((n + 3) / 4 - Zlength o2)) as T2. destruct (fin s2 e2 _) as [t2 f2].
  pose proof (Hf s3 e3 ((n + 3) / 4 - Zlength o3)) as T3. destruct (fin s3 e3 _) as [t3 f3].
  pose proof (Hf s4 e4 (n - 3 * ((n + 3) / 4) - Zlength o4)) as T4. destruct (fin s4 e4 _) as [t4 f4].
  cbn [fst] in *. destruct (_ && _)%bool; [|discriminate]. injection H as <-.
  repeat (apply xbk_app; auto).
Qed.

Lemma huf_decode_b (t: xhuf) (single: bool) (streams: list Z) (litSize: Z) (l: list Z) :
  xt_good t -> x_huf_decode t single streams litSize = Some l -> bytes_ok l.
Proof.
  intros Ht H. unfold x_huf_decode in H. destruct (xh_x2 t) eqn:E2.
  - assert (Hs: forall d, bytes_ok (fst (xh_x2_sym t d))) by (intros; apply x2_sym_b; auto).
    destruct single.
    + eapply onestream_b; [|exact H]. apply x2_stream_b, Hs.
    + eapply fourstreams_b; [| |exact H]; [intros; apply x2_n_b, Hs|apply x2_stream_b, Hs].
  - assert (Hs: forall d, is_byte (fst (xh_x1_sym t d))) by (intros; apply x1_sym_b; auto).
    destruct single.
    + eapply onestream_b; [|exact H]. apply x1_stream_b, Hs.
    + eapply fourstreams_b; [| |exact H]; [intros; apply x1_n_b, Hs|apply x1_stream_b, Hs].
Qed.

(* ---------- the tables zstd builds ---------- *)

(* HUF_readStats gives at most 256 weights: at most 128 direct ones (a header byte below 256) or at most 255
   FSE-coded ones, and the implied last one *)
Lemma weights_of_len (res: option (list Z * Z * Z)) (nk: Z) (s ws: list Z) :
  weights_of res nk s = Some ws -> Zlength ws <= 255.
Proof.
  intros H. unfold weights_of in H. destruct res as [[[norm log] nsize]|]; [|discriminate].
  destruct (log >? 6); [discriminate|]. destruct (_ >? _); [discriminate|].
  unfold fse_weights_dec in H. destruct (negb _); [discriminate|]. cbv zeta in H.
  destruct (_ <? 0); [discriminate|]. destruct (Huffman.fse2_loop _ _ _ _ _ _ _) as [w|]; [|discriminate].
  destruct (Z.gtb_spec (Zlength w) 255); [discriminate|]. injection H as <-. lia.
Qed.

Lemma desc_len (fw: list Z -> option (list Z)) (b ws: list Z) (size: Z) :
  (forall s w, fw s = Some w -> Zlength w <= 255) -> bytes_ok b ->
  huf_desc_weights_w fw b = Some (ws, size) -> Zlength ws <= 255.
Proof.
  intros Hf Hb H. unfold huf_desc_weights_w in H. cbv zeta in H.
  pose proof (xbk_byte_at b 0 Hb) as H0. unfold is_byte in H0.
  destruct (Zlength b <? 1); [discriminate|].
  destruct (byte_at b 0 >=? 128).
  - destruct (Zlength b <? _); [discriminate|]. injection H as <- _.
    unfold huf_direct_weights. rewrite Zlength_correct, map_length, seq_length. lia.
  - destruct (Zlength b <? _); [discriminate|].
    destruct (fw (slice b 1 (byte_at b 0))) as [w|] eqn:E; [|discriminate]. injection H as <- _.
    eapply Hf; exact E.
Qed.

Lemma readstats_len (b: list Z) (ht: huf_table) (size: Z) :
  bytes_ok b -> x_readstats b = Some (ht, size) -> (length (ht_weights ht) <= 256)%nat.
Proof.
  intros Hb H. unfold x_readstats, huf_parse_res, huf_parse_w in H.
  destruct (huf_desc_weights_w _ b) as [[ws sz]|] eqn:E; [|discriminate].
  apply desc_len in E; [|intros s w; apply weights_of_len|exact Hb].
  cbv zeta in H.
  destruct (existsb _ ws); [discriminate|]. destruct (_ =? 0); [discriminate|].
  destruct (_ >? HUF_TABLELOG_MAX); [discriminate|]. destruct (negb _); [discriminate|].
  destruct (_ || _)%bool; [discriminate|]. injection H as <- _. cbn [ht_weights].
  rewrite app_length. rewrite Zlength_correct in E. cbn [length]. lia.
Qed.

Lemma huf_cells_sym (ht: huf_table) (a b: Z) : In (a, b) (huf_cells ht) -> 0 <= a < Z.of_nat (length (ht_weights ht)).
Proof.
  intros H. unfold huf_cells in H. apply in_flat_map in H. destruct H as [w [_ H]].
  apply in_flat_map in H. destruct H as [s [Hs H]]. apply in_seq in Hs.
  destruct (_ =? w); [|contradiction]. apply repeat_spec in H. injection H as -> _. lia.
Qed.

Lemma hsym_byte (ht: huf_table) (L x: Z) : (length (ht_weights ht) <= 256)%nat -> 0 <= fst (hsym ht L x) < 256.
Proof.
  intros Hl. unfold hsym. destruct (Nat.lt_ge_cases (Z.to_nat (x / 2 ^ (L - ht_log ht))) (length (huf_cells ht))) as [Hc|Hc].
  - pose proof (nth_In _ (0, 0) Hc) as Hi. destruct (nth _ _ _) as [a b]. apply huf_cells_sym in Hi. cbn. lia.
  - rewrite nth_overflow by exact Hc. cbn. lia.
Qed.

Lemma xhuf_of_good (x2: bool) (ht: huf_table) : (length (ht_weights ht) <= 256)%nat -> xt_good (xhuf_of x2 ht).
Proof.
  intros Hl. unfold xt_good, xhuf_of. destruct x2; cbn [xh_cells xh_x2].
  - unfold xh_cells_x2. apply Forall_map, Forall_forall. intros n _. unfold xh_x2_fields.
    apply Z.mod_pos_bound. lia.
  - unfold xh_cells_x1. apply Forall_map, Forall_forall. intros n _.
    pose proof (hsym_byte ht (xh_x1_log ht) (Z.of_nat n) Hl) as B. destruct (hsym _ _ _) as [a b]. exact B.
Qed.

Lemma huf_read_good (x2: bool) (b: list Z) (t: xhuf) (h: Z) :
  bytes_ok b -> x_huf_read x2 b = Some (t, h) -> xt_good t.
Proof.
  intros Hb H. unfold x_huf_read in H. destruct (x_readstats b) as [[ht size]|] eqn:E; [|discriminate].
  injection H as <- _. apply xhuf_of_good. eapply readstats_len; eauto.
Qed.

(* the Huffman literals: bytes, and a good table after them *)
Lemma lits_huf_b (hprev: option xhuf) (ty: Z) (single: bool) (cb: list Z) (litSize: Z) (l: list Z) (t: xhuf) :
  bytes_ok cb -> (forall t0, hprev = Some t0 -> xt_good t0) ->
  x_lits_huf hprev ty single cb litSize = Some (l, t) -> bytes_ok l /\ xt_good t.
Proof.
  intros Hb Hp H. unfold x_lits_huf in H.
  assert (D: forall x2 single', xh_dctx x2 single' cb litSize = Some (l, t) -> bytes_ok l /\ xt_good t).
  { intros x2 single' E. unfold xh_dctx in E. destruct (x_huf_read x2 cb) as [[t' h]|] eqn:Er; [|discriminate].
    apply huf_read_good in Er; auto.
    destruct (Zlength cb <=? h); [discriminate|].
    destruct (x_huf_decode t' single' _ litSize) as [l'|] eqn:Ed; [|discriminate].
    injection E as <- <-. split; [eapply huf_decode_b; eauto|exact Er]. }
  destruct (ty =? 2).
  - destruct single; [eapply D; exact H|].
    destruct (litSize =? 0); [discriminate|]. destruct (Zlength cb =? 0); [discriminate|]. eapply D; exact H.
  - destruct (ty =? 3); [|discriminate]. destruct hprev as [t'|]; [|discriminate].
    specialize (Hp t' eq_refl).
    destruct (x_huf_decode t' single cb litSize) as [l'|] eqn:Ed; [|discriminate].
    injection H as <- <-. split; [eapply huf_decode_b; eauto|exact Hp].
Qed.

(* ---------- the literals section ---------- *)

(* the literals of a section of bytes are bytes (raw: a slice of it; RLE: one of its bytes; Huffman: decoded with a
   good table), and the table kept after it is good *)
Lemma lits_b (h: option xhuf) (b: list Z) (bsm wmax: Z) (str: bool) (lits: list Z) (lused: Z) (huf: option xhuf) :
  bytes_ok b -> (forall t, h = Some t -> xt_good t) ->
  x_lits xhuf x_lits_huf h b bsm wmax str = Some (lits, lused, huf) ->
  bytes_ok lits /\ (forall t, huf = Some t -> xt_good t).
Proof.
  intros Hb Hh H. unfold x_lits in H. cbv zeta in H.
  destruct (Zlength b <? 2); [discriminate|].
  destruct (Z.land (byte_at b 0) 3 =? 0).
  - destruct (_ && _)%bool; [discriminate|].
    destruct (if _ =? 1 then _ else _) as [lh ls].
    destruct (ls >? bsm); [discriminate|]. destruct (wmax <? ls); [discriminate|].
    destruct (lh + ls >? Zlength b); [discriminate|].
    injection H as <- _ <-. split; [apply xbk_slice, Hb|exact Hh].
  - destruct (Z.land (byte_at b 0) 3 =? 1).
    + destruct (_ && _)%bool; [discriminate|]. destruct (_ && _)%bool; [discriminate|].
      destruct (if _ =? 1 then _ else _) as [lh ls].
      destruct (ls >? bsm); [discriminate|]. destruct (wmax <? ls); [discriminate|].
      injection H as <- _ <-. split; [apply xbk_repeat, xbk_byte_at, Hb|exact Hh].
    + destruct (_ && _)%bool; [discriminate|]. destruct (Zlength b <? 5); [discriminate|].
      destruct (if _ =? 2 then _ else _) as [[[lh ls] cs] single].
      destruct (ls >? bsm); [discriminate|]. destruct (_ && _)%bool; [discriminate|].
      destruct (cs + lh >? Zlength b); [discriminate|]. destruct (wmax <? ls); [discriminate|].
      destruct (x_lits_huf h _ single (slice b lh cs) ls) as [[l t]|] eqn:E; [|discriminate].
      injection H as <- _ <-. apply lits_huf_b in E; [|apply xbk_slice, Hb|exact Hh].
      destruct E as [E1 E2]. split; [exact E1|]. intros t' Et. injection Et as <-. exact E2.
Qed.
