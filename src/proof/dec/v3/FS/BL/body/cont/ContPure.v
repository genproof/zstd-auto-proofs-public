(* FS3-bl BODY, BLCont: pure facts about ZSTD_checkContinuity on the buffer-less layouts. *)
Require Export Zstd.proof.dec.v3.FS.BL.body.BLCase.

Section CM_ContPure_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* the dictionary's array fits in its block (from bd_res), unless it is at NULL *)
Definition bc_fc (od: option bldict) : Prop :=
  match od with
  | None => True
  | Some d => isptr (bd_eb d) -> field_compatible (tarray tuchar (Zlength (bd_b d))) nil (bd_eb d)
  end.

Lemma bc_veqb_refl v : veqb v v = true.
Proof. unfold veqb. destruct (Val.eq v v); congruence. Qed.

Lemma bc_veqb_pn b o : veqb (Vptr b o) nullval = false.
Proof. unfold veqb. destruct (Val.eq _ _) as [E|E]; [discriminate E | reflexivity]. Qed.

Lemma bc_veqb_10 : veqb (Vint (Int.repr 1)) (Vint (Int.repr 0)) = false.
Proof. unfold veqb. destruct (Val.eq _ _) as [E|E]; [inversion E | reflexivity]. Qed.

Lemma bc_fc_arr N base :
  field_compatible (tarray tuchar N) [] base -> 0 <= N ->
  exists b ofs, base = Vptr b ofs /\ Ptrofs.unsigned ofs + N < Ptrofs.modulus.
Proof.
  intros (Hp & _ & Hs & _) HN. destruct base; try contradiction. exists b, i. split; auto.
  red in Hs. simpl in Hs. rewrite Z.max_r in Hs by lia. lia.
Qed.

Lemma bc_off_unsigned ofs d :
  0 <= d -> Ptrofs.unsigned ofs + d < Ptrofs.modulus ->
  Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr d)) = Ptrofs.unsigned ofs + d.
Proof.
  intros. rewrite Ptrofs.add_unsigned, (Ptrofs.unsigned_repr d) by rep_lia.
  apply Ptrofs.unsigned_repr. rep_lia.
Qed.

Lemma bc_vptr_diff_off b ofs N x y :
  Ptrofs.unsigned ofs + N < Ptrofs.modulus -> 0 <= x <= N -> 0 <= y <= N ->
  vptr_diff (offset_val x (Vptr b ofs)) (offset_val y (Vptr b ofs)) = x - y.
Proof. intros. simpl. rewrite !bc_off_unsigned by lia. lia. Qed.

Lemma bc_g01 od osz0 ba fs : bd_wf od -> bl_lay od osz0 ba fs ->
  fs_gpDictCopy fs = Vint (Int.repr 0) \/ fs_gpDictCopy fs = Vint (Int.repr 1).
Proof.
  intros Hwf [(_ & _ & _ & _ & -> & _) | [(? & ? & _ & _ & _ & _ & _ & _ & ->) | (? & ? & ? & _ & _ & _ & _ & _ & _ & _ & _ & ->)]];
    auto.
  destruct od as [d|]; simpl; auto.
  destruct Hwf as [(_ & _ & _ & _ & _ & [-> | (-> & _)] & _) | (_ & _ & _ & _ & -> & _)]; auto.
Qed.

(* the moved case: from the Begin's pointers, the output starts a new segment at ob + opos *)
Lemma bc_moved od fs ob osz opos ba :
  ba_out ba = None -> isptr ob -> 0 <= opos <= osz -> bd_wf od -> bc_fc od ->
  fs_previousDstEnd fs = bd_end od -> fs_prefixStart fs = bd_start od ->
  cont_moves fs (offset_val opos ob) (osz - opos) = true ->
  bl_lay od osz (bl_moved ba ob opos) (continuity fs (offset_val opos ob) (osz - opos)).
Proof.
  intros Hn Hob Hp Hwf Hfc Hpe Hps Hm. unfold continuity. rewrite Hm. right; right.
  exists ob, opos, opos. unfold bl_moved, bl_start. rewrite Hn. cbn.
  rewrite Hpe, Hps. split; [reflexivity|]. split; [exact Hob|]. split; [lia|]. split; [lia|].
  split; [reflexivity|]. split; [reflexivity|]. split; [|split; reflexivity].
  rewrite offset_offset_val. f_equal.
  destruct od as [d|]; simpl.
  - destruct Hwf as [(Hds & Hb & _ & Heb & _) | (Heb & Hb & Hds & _)].
    + destruct (bc_fc_arr _ _ (Hfc Heb) ltac:(lia)) as (b & o & Eb & Ho).
      cbn [bd_end bd_start bd_clen]. rewrite !bd_off_ptr by exact Heb. rewrite Eb. simpl offset_val at 1. rewrite bc_veqb_pn. rewrite (bc_vptr_diff_off b o (Zlength (bd_b d))) by lia.
      lia.
    + rewrite Heb, Hb, Hds. simpl. rewrite bc_veqb_refl. lia.
  - rewrite bc_veqb_refl. lia.
Qed.

Lemma bc_nomove fs dst n : cont_moves fs dst n = false -> continuity fs dst n = fs.
Proof. unfold continuity. intros ->. reflexivity. Qed.

Lemma bc_cap0 fs dst : cont_moves fs dst 0 = false.
Proof. reflexivity. Qed.

(* a 0-byte dictionary at dst (dict_ptr_ok's second case): no move, and the layout is the moved one *)
Lemma bc_stay d fs ob osz opos ba :
  ba_out ba = None -> isptr ob -> 0 <= opos <= osz -> bd_wf (Some d) -> isptr (bd_eb d) ->
  (bd_de0 d = nullval -> 0 < Zlength (bd_b d)) -> Zlength (bd_b d) = 0 ->
  fs_previousDstEnd fs = bd_end (Some d) -> fs_prefixStart fs = bd_start (Some d) ->
  fs_virtualStart fs = bd_start (Some d) -> fs_dictEnd fs = bd_de0o (Some d) ->
  fs_gpDictCopy fs = Vint (Int.repr 0) -> offset_val opos ob = bd_end (Some d) ->
  bl_lay (Some d) osz (bl_moved ba ob opos) fs.
Proof.
  intros Hn Hob Hp Hwf Heb D12 H0 Hpe Hps Hvs Hde Hg E. right; right.
  destruct Hwf as [(Hds & _ & _ & _ & _ & _ & Hde0 & _) | (Hn0 & _)]; [| rewrite Hn0 in Heb; contradiction].
  assert (Es: bd_start (Some d) = bd_end (Some d)) by (simpl; f_equal; lia).
  exists ob, opos, opos. unfold bl_moved, bl_start. rewrite Hn. cbn [ba_out].
  split; [reflexivity|]. split; [exact Hob|]. split; [lia|]. split; [lia|].
  split; [rewrite Hpe; auto|]. split; [rewrite Hps, Es; auto|].
  split; [rewrite Hvs, Es, <- E; simpl bd_clen; f_equal; lia|].
  split; [|exact Hg]. rewrite Hde. simpl. rewrite bd_off_ptr by exact Heb.
  destruct Hde0 as [Hd|Hd]; [specialize (D12 Hd); lia|exact Hd].
Qed.

Lemma bc_veqb_true a b : veqb a b = true -> a = b.
Proof. unfold veqb. destruct (Val.eq a b); auto; discriminate. Qed.

Lemma bc_nomove_eq fs dst n : 0 < n -> cont_moves fs dst n = false ->
  fs_gpDictCopy fs = Vint (Int.repr 0) /\ dst = fs_previousDstEnd fs.
Proof.
  unfold cont_moves. intros Hn Em. apply Z.ltb_lt in Hn. rewrite Hn in Em. simpl in Em.
  destruct (veqb (fs_gpDictCopy fs) _) eqn:E1; [|discriminate].
  destruct (veqb dst _) eqn:E2; [|discriminate]. split; apply bc_veqb_true; auto.
Qed.

(* ZSTD_checkContinuity's comparison on the Begin's layout with a capacity: the output starts a new segment, or
   (a 0-byte dictionary at dst) it continues the dictionary *)
Lemma bc_begin W od fs shk shd ob osz opos ba :
  ba_out ba = None -> 0 <= opos < osz -> field_compatible (tarray tuchar osz) nil ob ->
  bd_buf_ok W shk od shd (osz - opos) (offset_val opos ob) ->
  bd_wf od -> (forall d, od = Some d -> bd_de0 d = nullval -> isptr (bd_eb d) -> 0 < Zlength (bd_b d)) -> bc_fc od ->
  fs_previousDstEnd fs = bd_end od -> fs_prefixStart fs = bd_start od ->
  fs_virtualStart fs = bd_start od -> fs_dictEnd fs = bd_de0o od -> fs_gpDictCopy fs = Vint (Int.repr (bd_g0o od)) ->
  bl_lay od osz (bl_moved ba ob opos) (continuity fs (offset_val opos ob) (osz - opos)).
Proof.
  intros Hn Hp Fob Hbd Hwf D12 Hfc Hpe Hps Hvs Hde Hg.
  destruct (bc_fc_arr _ _ Fob ltac:(lia)) as (B & o & Eob & Hob).
  destruct (cont_moves fs (offset_val opos ob) (osz - opos)) eqn:Em.
  { apply bc_moved; auto; try lia; rewrite Eob; exact I. }
  rewrite (bc_nomove _ _ _ Em). assert (Hc: 0 < osz - opos) by lia. destruct (bc_nomove_eq _ _ _ Hc Em) as (Hg0 & E).
  rewrite Hpe in E. destruct od as [d|].
  2:{ rewrite Eob in E. discriminate E. }
  assert (Heb: isptr (bd_eb d)).
  { destruct Hwf as [(_ & _ & _ & Heb & _) | (Heb & _)]; [exact Heb |].
    cbn [bd_end] in E. rewrite Heb, Eob in E. discriminate E. }
  pose proof Hwf as Hwf0.
  destruct Hwf as [Hwf | (Hn0 & _)]; [| rewrite Hn0 in Heb; contradiction].
  assert (Hg1: bd_g0 d = 0).
  { rewrite Hg0 in Hg. simpl bd_g0o in Hg. destruct Hwf as (_ & _ & _ & _ & _ & [Hd | (Hd & _)] & _); auto.
    rewrite Hd in Hg. inversion Hg. }
  destruct (Hbd Hg1 Heb) as [(Hsb & Hoff & _) | (H0 & _ & _)].
  - exfalso. destruct Hwf as (Hds & Hb & _).
    destruct (bc_fc_arr _ _ (Hfc Heb) ltac:(lia)) as (B2 & o2 & Eb & Ho2).
    simpl bd_end in E. rewrite bd_off_ptr in E by exact Heb. rewrite Eob, Eb in E, Hoff. simpl in E, Hoff.
    assert (E2: Ptrofs.unsigned (Ptrofs.add o (Ptrofs.repr opos)) =
                Ptrofs.unsigned (Ptrofs.add o2 (Ptrofs.repr (Zlength (bd_b d))))) by congruence.
    pose proof (Zlength_nonneg (bd_b d)). rewrite !bc_off_unsigned in E2 by lia. rewrite bc_off_unsigned in Hoff by lia. lia.
  - apply bc_stay; auto; try lia; rewrite Eob; exact I.
Qed.

Ltac bc_z := match goal with |- context [continuity _ _ ?n] => replace n with 0 by lia end;
  rewrite (bc_nomove _ _ _ (bc_cap0 _ _)).

(* the layout after ZSTD_checkContinuity *)
Lemma bc_lay W od osz0 ba fs shk shd ob osz opos oc :
  bl_hist_ok ba ob opos oc -> (ba_out ba <> None -> osz = osz0) ->
  bd_buf_ok W shk od shd (osz - opos) (offset_val opos ob) -> 0 <= opos <= osz ->
  bd_wf od -> (forall d, od = Some d -> bd_de0 d = nullval -> isptr (bd_eb d) -> 0 < Zlength (bd_b d)) ->
  bc_fc od -> field_compatible (tarray tuchar osz) nil ob ->
  bl_lay od osz0 ba fs ->
  bl_lay od osz (bl_moved ba ob opos) (continuity fs (offset_val opos ob) (osz - opos)).
Proof.
  intros Hh Ho Hbd Hp Hwf D12 Hfc Fob Hl.
  unfold bl_hist_ok in Hh. unfold bl_moved, bl_start.
  destruct Hl as [(Hpe & Hps & Hvs & Hde & Hg & Hout) |
                  [(ob' & f0 & Eo & Hf0 & Hpe & Hps & Hvs & Hde & Hg) |
                   (ob' & f0 & pe & Eo & Hisp & Hf & Hpe0 & Hpe & Hps & Hvs & Hde & Hg')]].
  - destruct (ba_out ba) as [[[ob' f0] pe]|] eqn:Eo.
    + destruct Hh as (E1 & E2 & Hf0 & _). subst ob' pe. destruct Hout as (E3 & E4). subst f0.
      assert (osz = osz0) by (apply Ho; congruence). assert (osz = opos) by lia. subst osz.
      bc_z.
      left. cbn [ba_out]. repeat split; auto.
    + destruct (Z.eq_dec opos osz) as [<- | Hne].
      * bc_z.
        left. cbn [ba_out]. repeat split; auto.
      * assert (Hm: bl_lay od osz (bl_moved ba ob opos) (continuity fs (offset_val opos ob) (osz - opos)))
          by (eapply bc_begin; eauto; lia).
        unfold bl_moved, bl_start in Hm. rewrite Eo in Hm. exact Hm.
  - rewrite Eo in Hh |- *. destruct Hh as (E1 & E2 & _ & _). subst ob' f0.
    assert (osz = opos) by (rewrite Hf0; apply Ho; congruence). subst osz.
    bc_z.
    right; left. exists ob, opos. cbn [ba_out]. repeat split; auto.
  - rewrite Eo in Hh |- *. destruct Hh as (E1 & E2 & _ & _). subst ob' pe.
    assert (osz = osz0) by (apply Ho; congruence). subst osz0.
    assert (Em: cont_moves fs (offset_val opos ob) (osz - opos) = false).
    { unfold cont_moves. rewrite Hg', Hpe, !bc_veqb_refl. simpl. apply andb_false_r. }
    rewrite (bc_nomove _ _ _ Em). right; right. exists ob, f0, opos. cbn [ba_out]. repeat split; auto; lia.
Qed.

End CM_ContPure_1.
