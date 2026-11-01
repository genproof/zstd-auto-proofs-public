(* A compressed block decoded one-shot (Exact.xblock with prefixStart = 0, op = the frame's output so far, no
   extDict, not streaming) does not depend on the stale bytes of litExtraBuffer: two runs from states that differ
   only in litExtraBuffer's contents (same length), with nonzero repeat offsets, both fail, or both succeed with the same size, the same
   content and states that again differ only in litExtraBuffer's contents.

   Why it holds: zstd's wild copies read up to 32 bytes past the literals they copy (from litExtraBuffer, past
   the literals this block wrote there: bytes of earlier blocks) and store them past the sequence's end; the
   next sequence (or nothing) overwrites them before anything reads them as history, and without an extDict no
   match reaches a cell at or beyond op.  So the bytes of litExtraBuffer this block did not write only ever
   reach destination cells past the block's content, and the state's litExtraBuffer.  No control decision of
   the model reads a memory value.

   The repeat offsets must be nonzero: a repeat offset 0 makes a match copy from its own write position, which
   holds the overshoot of the literal copy (stale litExtraBuffer bytes), and zstd does the same.  They are, on
   every block of a one-shot frame (ZSTD_decompressBegin sets 1, 4, 8; ExBlockReps.xblock_reps keeps them in
   [1, 2^32)).

   This is what lets ZSTD_decompressDCtx's exact result (Spec_api6.oneshot_exact, model/Exact.v's os_res from a
   zeroed litExtraBuffer) hold for a context whose litExtraBuffer holds anything (ExOneshot.v).  Plain Coq. *)
Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import Zstd.proof.model.Bytes Zstd.proof.model.ExHuf Zstd.proof.model.ExBlock Zstd.proof.model.Exact.
Require Import Coq.micromega.Lia Zstd.proof.model.ExCSeq Zstd.proof.model.ExAgreeBlkDefs.
Require Import Zstd.proof.model.ExBlockIndepMem Zstd.proof.model.ExBlockIndepCopy.
Require Import Zstd.proof.model.ExBlockIndepExec Zstd.proof.model.ExBlockIndepLits.
Local Open Scope Z_scope.

(* two states that differ at most in litExtraBuffer's contents *)
Definition xrel (a b: xstate) : Prop :=
  x_huf xhuf a = x_huf xhuf b /\ x_seq xhuf a = x_seq xhuf b /\ x_rep xhuf a = x_rep xhuf b /\
  Zlength (x_lxb xhuf a) = Zlength (x_lxb xhuf b).

(* the destination as one-shot decoding gives it (the frame's output so far), the same in both runs; the two
   litExtraBuffers of the same length, none of their cells clean *)
Lemma rel_init : forall d l1 l2, Zlength l1 = Zlength l2 ->
  rel (fun r _ => r = R_dst) {| xm_dst := d; xm_lxb := l1 |} {| xm_dst := d; xm_lxb := l2 |}.
Proof.
  intros d l1 l2 Hl. unfold rel; cbn. repeat split; auto. intros i _ H. discriminate.
Qed.

(* the written cells below P are those the clean cells determine *)
Lemma written_firstn : forall n d1 d2, (forall k, (k < n)%nat -> nth k d1 None = nth k d2 None) ->
  firstn n (x_written d1) = firstn n (x_written d2).
Proof.
  induction n as [|n IH]; intros d1 d2 H; [reflexivity|].
  pose proof (H O ltac:(lia)) as H0.
  destruct d1 as [|[v1|] d1]; destruct d2 as [|[v2|] d2]; simpl in H0 |- *; try discriminate; auto.
  injection H0 as ->. f_equal. apply IH. intros k Hk. apply (H (S k)). lia.
Qed.

Lemma written_slice : forall c m1 m2 i P, rel c m1 m2 -> PC c P -> 0 <= i ->
  slice (x_written (xm_dst m1)) i (P - i) = slice (x_written (xm_dst m2)) i (P - i).
Proof.
  intros c m1 m2 i P HR HP Hi. unfold slice.
  destruct (Z.lt_ge_cases P i).
  - replace (Z.to_nat (P - i)) with O by lia. reflexivity.
  - rewrite !firstn_skipn_comm. replace (Z.to_nat i + Z.to_nat (P - i))%nat with (Z.to_nat P) by lia.
    f_equal. apply written_firstn. intros k Hk.
    destruct HR as (_ & H2 & _). pose proof (H2 (Z.of_nat k) ltac:(lia) (HP (Z.of_nat k) ltac:(lia))) as Hq.
    unfold dcell in Hq. rewrite Nat2Z.id in Hq. exact Hq.
Qed.

Lemma xblock_indep (a b: xstate) (mem body: list Z) (bsm cap: Z) :
  xrel a b -> (let '(r1, r2, r3) := x_rep xhuf a in 1 <= r1 /\ 1 <= r2 /\ 1 <= r3) ->
  match xblock a mem 0 (Zlength mem) 0 0 body bsm cap false, xblock b mem 0 (Zlength mem) 0 0 body bsm cap false with
  | None, None => True
  | Some (a', m1, n1), Some (b', m2, n2) =>
      n1 = n2 /\ xrel a' b' /\ slice m1 (Zlength mem) n1 = slice m2 (Zlength mem) n2
  | _, _ => False
  end.
Proof.
  intros (Hh & Hs & Hr & Hl) Hrep.
  unfold xblock, x_block. rewrite <- Hh, <- Hs, <- Hr.
  destruct (Zlength body >? bsm); [exact I|].
  destruct (x_lits xhuf x_lits_huf (x_huf xhuf a) body bsm (Z.min bsm cap) false) as [[[lits lused] huf]|];
    [|exact I].
  destruct (x_seq_header ncount_c (x_seq xhuf a) (skipn (Z.to_nat lused) body)) as [[[nbSeq tabs] hused]|]; [|exact I].
  destruct ((nbSeq >? 0) && (cap =? 0))%bool; [exact I|].
  pose proof (lits_store_inv body lits lused _ _ (Zlength mem) (Z.min bsm cap) bsm cap false _
                (rel_init (map Some mem) (x_lxb xhuf a) (x_lxb xhuf b) Hl) (fun x => eq_refl)) as K1.
  destruct (x_lits_store body lits lused {| xm_dst := map Some mem; xm_lxb := x_lxb xhuf a |} (Zlength mem)
              (Z.min bsm cap) bsm cap false) as [[[[[m1 lr] li] lim] sp]|];
    destruct (x_lits_store body lits lused {| xm_dst := map Some mem; xm_lxb := x_lxb xhuf b |} (Zlength mem)
              (Z.min bsm cap) bsm cap false) as [[[[[m2 lr2] li2] lim2] sp2]|];
    cbn [orel LS] in K1; try contradiction; [|exact I].
  destruct K1 as (<- & <- & <- & <- & c & K1 & HA & HL).
  set (e := {| xe_src := body; xe_ps := 0; xe_vs := 0 - (0 - 0); xe_de := 0;
               xe_oend := match x_litloc body lused (Zlength lits) bsm cap false with
                          | XL_in_dst => Zlength mem + bsm + XWILDCOPY
                          | _ => Zlength mem + cap
                          end |}).
  set (s1 := {| xmm := m1; xop := Zlength mem; xlr := lr; xli := li; xlim := lim; xsp := sp |}).
  set (s2 := {| xmm := m2; xop := Zlength mem; xlr := lr; xli := li; xlim := lim; xsp := sp |}).
  assert (Hinv: xinv s1 s2).
  { unfold xinv, s1, s2; cbn. repeat (split; [reflexivity|]). exists c. split; auto.
    destruct sp; [split; auto|]. destruct lr; auto. split; [intros x _; apply HA|auto]. }
  assert (Hps: xe_ps e = 0) by reflexivity.
  assert (Hvs: xe_vs e = 0) by reflexivity.
  assert (Hres: orel (fun a b => let '(m1', o1, r1) := a in let '(m2', o2, r2) := b in
                        o1 = o2 /\ r1 = r2 /\ exists c, rel c m1' m2' /\ PC c o1)
            (if nbSeq =? 0 then match x_last e s1 with Some (m, op') => Some (m, op', x_rep xhuf a) | None => None end
             else match tabs with Some t => x_seqs dseq_one c_offset e t (x_rep xhuf a) (skipn (Z.to_nat hused)
                    (skipn (Z.to_nat lused) body)) nbSeq s1 | None => None end)
            (if nbSeq =? 0 then match x_last e s2 with Some (m, op') => Some (m, op', x_rep xhuf a) | None => None end
             else match tabs with Some t => x_seqs dseq_one c_offset e t (x_rep xhuf a) (skipn (Z.to_nat hused)
                    (skipn (Z.to_nat lused) body)) nbSeq s2 | None => None end)).
  { destruct (nbSeq =? 0).
    - pose proof (last_inv e s1 s2 Hinv) as K2.
      destruct (x_last e s1) as [[ma oa]|]; destruct (x_last e s2) as [[mb ob]|]; cbn [orel] in K2;
        try contradiction; [|exact I].
      destruct K2 as (<- & K2). cbn. auto.
    - destruct tabs as [t|]; [|exact I].
      apply (seqs_inv e Hps Hvs); auto.
      }
  destruct (if nbSeq =? 0 then _ else _) as [[[ma oa] ra]|];
    destruct (if nbSeq =? 0 then _ else _) as [[[mb ob] rb]|]; cbn [orel] in Hres; try contradiction; [|exact I].
  destruct Hres as (<- & <- & c' & Hrel & HP).
  split; [reflexivity|]. split.
  - unfold xrel; cbn. repeat (split; [reflexivity|]). destruct Hrel as (_ & _ & _ & Hlx & _). exact Hlx.
  - apply (written_slice c'); auto. apply Zlength_nonneg.
Qed.
