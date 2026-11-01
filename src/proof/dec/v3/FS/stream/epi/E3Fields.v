(* FS3 streaming: what the epilogue reads of the context when the loop stops (someMoreWork = 0):
   expected, outStart/outEnd, hostageByte, stage, inPos, against the view sv (plain facts of call_inv and
   exit_ok); port of v2 src/proof/dec/FS/StreamEpiFields.v. *)
Require Import Zstd.proof.dec.v3.FS.stream.S3Main Zstd.proof.dec.v3.FS.stream.epi.E3Defs Zstd.proof.dec.v3.FS.stream.epi.E3Rem.

Section CM_E3Fields_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* the expected size and the frame stage of a frame in progress (c_frame), against the progress fp *)
Lemma ef_frame : forall (fs: fstate) tabs (fp: fprog) l dd (s: sfields),
  c_frame fs tabs fp l dd ->
  (sf_stage s = zdss_load ->
     fp_complete fp = false /\ fp_rawbody fp = false /\ sf_inPos s = vlong (fp_inpos fp)) ->
  (sf_stage s <> zdss_load ->
     sf_inPos s = vlong 0 /\ (fp_rawbody fp = true \/ fp_loaded fp = nil \/ fp_complete fp = true) /\
     match fp with FP_skip _ got => got = 0 \/ fp_complete fp = true | _ => True end) ->
  exists e, fs_expected fs = vlong e /\ 0 <= e <= Int64.max_unsigned /\
  (e = 0 -> fp_complete fp = true) /\
  (e <> 0 -> fp_complete fp = false /\
     exists fstg ip0, fs_stage fs = Vint (Int.repr fstg) /\ 0 <= fstg <= 7 /\
       sf_inPos s = vlong ip0 /\ 0 <= ip0 <= Int64.max_unsigned /\
       e + ZSTD_blockHeaderSize * nit_blk fstg - ip0 = fp_rem fp /\ 0 < fp_rem fp /\ fp_rem fp <= 2 ^ 32).
Proof.
intros fs tabs fp l dd s Hcf HL HN.
destruct Hcf as (_ & _ & _ & _ & _ & Hm).
destruct fp as [|hb|hdr got|hdr z]; try contradiction.
- (* a skippable frame *)
  destruct Hm as (_ & _ & _ & Hg & Hsz & Hif).
  destruct (got =? le_field hdr 4 4) eqn:Eg.
  + destruct Hif as (_ & He). exists 0.
    split; [exact He|]. split; [rep_lia|]. split; [intros _; cbn [fp_complete]; exact Eg|].
    intros C; congruence.
  + destruct Hif as (Hs & He). apply Z.eqb_neq in Eg.
    exists (le_field hdr 4 4).
    split; [exact He|]. split; [rep_lia|]. split; [lia|]. intros _.
    split; [cbn [fp_complete]; apply Z.eqb_neq; exact Eg|].
    exists ds_skipFrame.
    destruct (Z.eq_dec (sf_stage s) zdss_load) as [L|L].
    * destruct (HL L) as (_ & _ & E). exists got.
      split; [exact Hs|]. split; [unfold ds_skipFrame; lia|]. split; [exact E|]. split; [rep_lia|].
      cbn [fp_rem]. unfold nit_blk, next_input_type, ds_skipFrame; simpl. lia.
    * destruct (HN L) as (E & _ & D). cbn [fp_complete] in D.
      destruct D as [D|D]; [|apply Z.eqb_eq in D; congruence]. subst got. exists 0.
      split; [exact Hs|]. split; [unfold ds_skipFrame; lia|]. split; [exact E|]. split; [rep_lia|].
      cbn [fp_rem]. unfold nit_blk, next_input_type, ds_skipFrame; simpl. lia.
- (* a Zstandard frame *)
  destruct Hm as (_ & _ & Hbsm & Hbsm2 & _ & _ & _ & _ & _ & _ & Hph & _ & _ & _ & _ & Hm2 & _).
  assert (Hip: fp_rawbody (FP_zstd hdr z) = false -> fp_complete (FP_zstd hdr z) = false ->
                sf_inPos s = vlong (Zlength (zp_got z))).
  { intros R C. destruct (Z.eq_dec (sf_stage s) zdss_load) as [L|L].
    - destruct (HL L) as (_ & _ & E). exact E.
    - destruct (HN L) as (E & D & _). cbn [fp_loaded] in D.
      destruct D as [D|[D|D]]; try congruence. rewrite D, Zlength_nil. exact E. }
  pose proof (Zlength_nonneg (zp_got z)) as Hg0.
  unfold phase_fields in Hph.
  cbn [fp_rawbody fp_complete fp_rem] in Hip |- *.
  destruct (zp_ph z) as [|bh| |] eqn:Eph.
  + (* a block header *)
    destruct Hph as (Hs & He). exists ZSTD_blockHeaderSize.
    unfold ZSTD_blockHeaderSize in *.
    split; [exact He|]. split; [rep_lia|]. split; [lia|]. intros _. split; [reflexivity|].
    exists ds_decodeBlockHeader, (Zlength (zp_got z)).
    split; [exact Hs|]. split; [unfold ds_decodeBlockHeader; lia|]. split; [apply Hip; reflexivity|].
    split; [rep_lia|]. unfold nit_blk, next_input_type, ds_decodeBlockHeader; simpl. lia.
  + (* a block body *)
    destruct Hph as (c & Hc & Hs & _ & _ & He).
    destruct Hm2 as (_ & _ & c' & Hc' & Hcr & Hgc & _).
    rewrite Hc in Hc'. inversion Hc'. subst c'. rewrite Hc.
    assert (Hn: forall b: bool, ZSTD_blockHeaderSize *
              nit_blk (if b then ds_decompressLastBlock else ds_decompressBlock) =
              if b then 0 else ZSTD_blockHeaderSize).
    { intros []; reflexivity. }
    assert (Hb: 0 <= (if bp_last (block_props_of bh) =? 1 then ds_decompressLastBlock else ds_decompressBlock)
                <= 7) by (unfold ds_decompressLastBlock, ds_decompressBlock; destruct (_ =? 1); lia).
    assert (H3: 0 <= (if bp_last (block_props_of bh) =? 1 then 0 else ZSTD_blockHeaderSize) <= 3)
      by (unfold ZSTD_blockHeaderSize; destruct (_ =? 1); lia).
    assert (Hbs: zp_bsm z <= 131072) by (rewrite Hbsm2 in Hbsm; unfold ZSTD_BLOCKSIZE_MAX in Hbsm; lia).
    destruct (bp_type (block_props_of bh) =? 0) eqn:Et.
    * (* raw: streamed, not loaded *)
      exists (c - Zlength (zp_got z)).
      split; [exact He|]. split; [rep_lia|]. split; [lia|]. intros _. split; [reflexivity|].
      assert (L: sf_stage s <> zdss_load).
      { intros L. destruct (HL L) as (_ & R & _). cbn [fp_rawbody] in R. rewrite Eph, Et in R. discriminate. }
      destruct (HN L) as (E & _ & _).
      eexists _, 0. split; [exact Hs|]. split; [exact Hb|]. split; [exact E|]. split; [rep_lia|].
      rewrite Hn. split; [lia|]. split; lia.
    * exists c.
      split; [exact He|]. split; [rep_lia|]. split; [lia|]. intros _. split; [reflexivity|].
      eexists _, (Zlength (zp_got z)). split; [exact Hs|]. split; [exact Hb|].
      split; [apply Hip; reflexivity|]. split; [rep_lia|].
      rewrite Hn. split; [lia|]. split; lia.
  + (* the checksum *)
    destruct Hph as (Hs & He). destruct Hm2 as (Hgl & _). exists 4.
    split; [exact He|]. split; [rep_lia|]. split; [lia|]. intros _. split; [reflexivity|].
    exists ds_checkChecksum, (Zlength (zp_got z)).
    split; [exact Hs|]. split; [unfold ds_checkChecksum; lia|]. split; [apply Hip; reflexivity|].
    split; [rep_lia|]. unfold nit_blk, next_input_type, ds_checkChecksum, ZSTD_blockHeaderSize; simpl. lia.
  + (* the end *)
    destruct Hph as (_ & He). exists 0.
    split; [exact He|]. split; [rep_lia|]. split; [reflexivity|]. intros C; congruence.
Qed.

(* outStart/outEnd of a frame in progress (c_ring) *)
Lemma ef_ring : forall stable obuf sout (s: sfields) (fp: fprog) pend l,
  c_ring stable obuf sout s fp pend l -> sf_inSize s + sf_outSize s <= 2 ^ 32 ->
  exists os oe, sf_outStart s = vlong os /\ sf_outEnd s = vlong oe /\
    0 <= os <= Int64.max_unsigned /\ 0 <= oe <= Int64.max_unsigned /\ (os = oe -> pend = nil).
Proof.
intros stable obuf sout s fp pend l Hr Hsz.
destruct Hr as (_ & _ & Hin & ostart & oend & Hos & Hoe & Hle & Hm).
pose proof (Z.le_max_r (fp_bsm fp) 4).
exists ostart, oend. split; [exact Hos|]. split; [exact Hoe|].
destruct stable.
- destruct Hm as (-> & -> & -> & _). split; [rep_lia|]. split; [rep_lia|]. tauto.
- destruct Hm as (Hoe' & Hsub & _).
  split; [rep_lia|]. split; [rep_lia|].
  intros <-. rewrite sublist_nil in Hsub. destruct pend; [reflexivity|discriminate].
Qed.

Lemma vlong_inj : forall x y, 0 <= x <= Int64.max_unsigned -> 0 <= y <= Int64.max_unsigned ->
  vlong x = vlong y -> x = y.
Proof.
intros x y Hx Hy H. unfold vlong in H.
assert (H1: Int64.unsigned (Int64.repr x) = Int64.unsigned (Int64.repr y)) by congruence.
rewrite !Int64.unsigned_repr in H1 by lia. exact H1.
Qed.

Lemma epi_fields : forall (a: dsa) (w: lw),
  call_inv a (w_k w) (w_sv w) (w_ipc w) (w_opc w) (w_oc w) (w_dl w) -> exit_ok a w -> w_smw w = 0 ->
  let k := w_k w in let s := c3_s k in let sv := w_sv w in
  exists e, fs_expected (c3_fs k) = vlong e /\ 0 <= e <= Int64.max_unsigned /\
  (e = 0 ->
     (sf_stage s = zdss_init \/ fp_complete (sv_fp sv) = true) /\
     exists os oe h, sf_outStart s = vlong os /\ sf_outEnd s = vlong oe /\ sf_hostage s = Vint h /\
       0 <= os <= Int64.max_unsigned /\ 0 <= oe <= Int64.max_unsigned /\
       (h = Int.zero \/ h = Int.one) /\
       (os = oe -> sv_pend sv = nil) /\ (os <> oe -> sf_stage s = zdss_flush)) /\
  (e <> 0 ->
     sf_stage s <> zdss_init /\ fp_complete (sv_fp sv) = false /\
     exists fstg ip0, fs_stage (c3_fs k) = Vint (Int.repr fstg) /\ 0 <= fstg <= 7 /\
       sf_inPos s = vlong ip0 /\ 0 <= ip0 <= Int64.max_unsigned /\
       e + ZSTD_blockHeaderSize * nit_blk fstg - ip0 = fp_rem (sv_fp sv) /\ 0 < fp_rem (sv_fp sv) /\
       fp_rem (sv_fp sv) <= 2 ^ 32).
Proof.
intros a w Hci Hx Hs0. cbv zeta.
specialize (Hx Hs0). destruct Hx as (X1 & _ & _ & _ & X4).
destruct Hci as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcore & _).
destruct (Z.eq_dec (sf_stage (c3_s (w_k w))) zdss_init) as [Hi|Hi].
- (* zdss_init *)
  destruct (X4 Hi) as (He & (o & Ho1 & Ho2 & Hor) & Hh).
  destruct Hcore as (_ & _ & _ & Hif). rewrite (proj2 (Z.eqb_eq _ _) Hi) in Hif. destruct Hif as (_ & Hp).
  exists 0. split; [exact He|]. split; [rep_lia|]. split.
  + intros _. split; [left; exact Hi|].
    exists o, o.
    destruct Hh as [(Hh & _)|(Hh & _)]; [exists Int.zero | exists Int.one];
      (split; [exact Ho1|]); (split; [exact Ho2|]); (split; [exact Hh|]);
      (split; [lia|]); (split; [lia|]); (split; [auto|]); (split; [auto|]); intros C; congruence.
  + intros C; congruence.
- (* a frame in progress *)
  destruct Hcore as (Hh & _ & Hsz & Hif).
  rewrite (proj2 (Z.eqb_neq _ _) Hi), (proj2 (Z.eqb_neq _ _) X1) in Hif.
  destruct Hif as (Hst & Hcf & Hcr & _ & Hload & Hnload & Hread).
  destruct (ef_frame _ _ _ _ _ (c3_s (w_k w)) Hcf) as (e & He & Hrng & H0 & Hn0).
  { intros L. destruct (Hload L) as (_ & ? & ? & _ & ? & _). auto. }
  { exact Hnload. }
  destruct (ef_ring _ _ _ _ _ _ _ Hcr Hsz) as (os & oe & Hos & Hoe & Hosr & Hoer & Hp).
  exists e. split; [exact He|]. split; [exact Hrng|]. split.
  + intros E0. split; [right; apply H0; exact E0|].
    assert (Hh': sf_hostage (c3_s (w_k w)) = Vint Int.zero \/ sf_hostage (c3_s (w_k w)) = Vint Int.one).
    { destruct Hh as [(C & _)|[(Hh & _)|(Hh & _)]]; [congruence|left|right]; exact Hh. }
    exists os, oe.
    destruct Hh' as [Hh'|Hh']; [exists Int.zero|exists Int.one];
      (split; [exact Hos|]); (split; [exact Hoe|]); (split; [exact Hh'|]);
      (split; [lia|]); (split; [lia|]); (split; [auto|]); (split; [exact Hp|]);
      intros Hne; (destruct Hst as [Hr|[Hl|Hf]]; [exfalso|exfalso|exact Hf]);
      apply Hne; apply vlong_inj; try lia; rewrite <- Hos, <- Hoe;
      first [apply (Hread Hr) | apply (Hload Hl)].
  + intros En. split; [exact Hi|]. exact (Hn0 En).
Qed.

End CM_E3Fields_1.
