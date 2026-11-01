(* LOOP / long loop: one ZSTD_decodeSequence step of the decoder invariant (pure). *)
Require Import Zstd.proof.dec.B.blk.BlkSeqLoopLongDefs.
Local Open Scope logic.

Lemma lgd_rep_chain_app (r: Z * Z * Z) (l1 l2: list sequence) :
  rep_chain r (l1 ++ l2) = rep_chain (rep_chain r l1) l2.
Proof. revert r; induction l1 as [|sq l1 IH]; intros r; simpl; [reflexivity | apply IH]. Qed.

Lemma lgd_q_of_app (r: Z * Z * Z) (l1 l2: list sequence) :
  q_of r (l1 ++ l2) = q_of r l1 ++ q_of (rep_chain r l1) l2.
Proof. revert r; induction l1 as [|sq l1 IH]; intros r; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma lgd_rep64 (k: Z) (r: Z * Z * Z) :
  0 <= k < 2 ^ 32 -> rep_c_ok k r -> rep64_ok r.
Proof.
  destruct r as [[r1 r2] r3]. unfold rep_c_ok, rc1, rep64_ok, SIZE_MAX. intros Hk (H1 & H2 & H3). lia.
Qed.

Lemma lgd_rc1_mono (k v: Z) : rc1 k v -> rc1 (k + 1) v.
Proof. unfold rc1. lia. Qed.

Lemma lgd_rc_step (k: Z) (r: Z * Z * Z) (ll ov: Z) :
  0 <= k < 2 ^ 32 -> rep_c_ok k r -> 1 <= ov < 2 ^ 32 -> rep_c_ok (k + 1) (snd (c_offset r ll ov)).
Proof.
  destruct r as [[r1 r2] r3]. intros Hk Hr Hov.
  assert (M1 := lgd_rc1_mono k r1). assert (M2 := lgd_rc1_mono k r2). assert (M3 := lgd_rc1_mono k r3).
  unfold rep_c_ok in Hr. destruct Hr as (H1 & H2 & H3).
  unfold c_offset, rep_c_ok.
  destruct (ov >? 3) eqn:E; [apply Z.gtb_lt in E; cbv [snd]; unfold rc1 in *; repeat split; auto; lia|].
  destruct ((if ll =? 0 then ov + 1 else ov) =? 1); [cbv [snd]; auto|].
  destruct ((if ll =? 0 then ov + 1 else ov) =? 2); [cbv [snd]; auto|].
  destruct ((if ll =? 0 then ov + 1 else ov) =? 3); [cbv [snd]; auto|].
  cbv [snd]. unfold rc1, SIZE_MAX in *.
  rewrite Z.mod_small by lia.
  destruct (r1 - 1 =? 0) eqn:E0; [apply Z.eqb_eq in E0 | apply Z.eqb_neq in E0]; repeat split; auto; lia.
Qed.

Lemma lg_dstep_ok : DSTEP.
Proof.
  unfold DSTEP.
  intros a x id pos lo st drep ll ml ov pos' lo' st' Hla Hlfx Hid Hsafe Hdm H0lo H8 Hpl Hll Hml Hov Hst'
    Hp' Hlo' Hlast Hdec.
  destruct Hsafe as (Hst & Hrc & Hbc).
  assert (Hnb: a_nb a <= LONGNBSEQ + 65535) by (unfold la_ok in Hla; tauto).
  unfold LONGNBSEQ in Hnb.
  assert (Hr64: rep64_ok drep) by (apply (lgd_rep64 id); [lia | exact Hrc]).
  split; [apply c_offset_ok; assumption|].
  split.
  { split; [exact Hst'|]. split; [apply lgd_rc_step; [lia | exact Hrc | exact Hov]|].
    unfold bcons, DSEQ_BITS in *. lia. }
  intros seqs HDM.
  destruct (Hdm seqs HDM) as [Hlen (Hdm1 & _ & Hdrep)].
  assert (Hos: seqs_ok (Some (x_t x))).
  { destruct Hlfx as [Hos _]. rewrite <- Hos. unfold la_ok in Hla. tauto. }
  clear Hdm HDM Hlfx.
  destruct (x_t x) as [[tLL tOF] tML]. destruct st as [[sLL sOF] sML].
  destruct Hos as (FLL & FOF & FML). destruct Hst as (S1 & S2 & S3).
  destruct (Hdm1 ltac:(lia)) as [Hds Hrdy]. clear Hdm1.
  replace (Z.to_nat (a_nb a - id)) with (S (Z.to_nat (a_nb a - id - 1))) in Hds by lia.
  destruct (loop_dec_step _ _ _ _ _ _ _ _ _ _ Hds) as (sq & a1 & b1 & c1 & pn & rest & Hl & Hone & Hrest & Hk0).
  assert (Heqb: Nat.eqb (Z.to_nat (a_nb a - id - 1)) 0 = (id =? a_nb a - 1)).
  { destruct (Nat.eqb_spec (Z.to_nat (a_nb a - id - 1)) 0); destruct (Z.eqb_spec id (a_nb a - 1)); lia. }
  rewrite Heqb in Hone.
  destruct (Hdec Hrdy sq (a1, b1, c1) pn Hone) as (-> & -> & -> & -> & Hnl). clear Hdec.
  assert (HZ: Znth id seqs = sq).
  { assert (E: Znth 0 (sublist id (a_nb a) seqs) = sq) by (rewrite Hl; reflexivity).
    rewrite Znth_sublist in E by lia. rewrite Z.add_0_l in E. exact E. }
  assert (Hrest': rest = sublist (id + 1) (a_nb a) seqs).
  { rewrite (sublist_next id (a_nb a) seqs) in Hl by lia. injection Hl as _ ->. reflexivity. }
  assert (Hsub: sublist 0 (id + 1) seqs = sublist 0 id seqs ++ [sq]).
  { rewrite sublist_last_1 by lia. rewrite HZ. reflexivity. }
  split; [|split; [rewrite HZ; reflexivity|split; [rewrite HZ; reflexivity|split; [rewrite HZ; reflexivity|]]]].
  - split; [|split].
    + destruct st' as [[s1 s2] s3]. intros Hlt.
      assert (Hf: (id =? a_nb a - 1) = false) by (apply Z.eqb_neq; lia).
      destruct (Hnl Hf) as [E Hrdy']. injection E as -> -> ->. split; [|exact Hrdy'].
      replace (Z.to_nat (a_nb a - (id + 1))) with (Z.to_nat (a_nb a - id - 1)) by lia.
      rewrite Hrest, Hrest'. reflexivity.
    + intros Heq.
      destruct (Hk0 ltac:(lia)) as [_ Hpn0]. subst pn. split; [reflexivity|].
      assert (Ht: (id =? a_nb a - 1) = true) by (apply Z.eqb_eq; lia).
      rewrite Ht in Hone.
      exact (loop_end_lo _ _ _ _ _ _ _ _ _ _ _ _ FLL FOF FML S1 S2 S3 H0lo H8 Hpl Hrdy Hlo' Hone).
    + rewrite Hsub, lgd_rep_chain_app, <- Hdrep. reflexivity.
  - intros ie Hie.
    rewrite (sublist_last_1 ie id seqs) by lia. rewrite lgd_q_of_app, HZ.
    rewrite <- lgd_rep_chain_app, <- (sublist_split 0 ie id seqs) by lia. rewrite <- Hdrep.
    reflexivity.
Qed.
