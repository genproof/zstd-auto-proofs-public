(* The dictionary window rule (Params.v, md_dwin; API v3.1): the strict model decodes less than Block.v's
   (where it decodes, Block.v's gives the same), and without a dictionary it is Block.v's.  Plain Coq.
   params_w is the one statement to prove; the lemmas below are its parts. *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Block Zstd.proof.model.Series.
Require Import Zstd.proof.model.StreamModel Zstd.proof.model.Params.

Require Import Zstd.proof.model.BitsFast Zstd.proof.model.Fse.

(* ---------- helpers ---------- *)
Local Open Scope bool_scope.

Lemma pw_rd_nonneg (V: list Z) (pos nb e p: Z) : rd V pos nb = Some (e, p) -> 0 <= nb -> 0 <= e.
Proof.
  unfold rd. intros H Hnb. destruct (pos - nb <? 0); [discriminate|]. inversion H; subst; clear H.
  unfold bs_peek_s. destruct (pos <? 0) eqn:E0; [lia|]. apply Z.ltb_ge in E0.
  destruct (pos - nb >=? 0).
  - apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
  - apply Z.mul_nonneg_nonneg.
    + apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
    + apply Z.pow_nonneg; lia.
Qed.

Lemma pw_nth_nonneg (l: list Z) (n: nat) : Forall (fun x => 0 <= x) l -> 0 <= nth n l 0.
Proof.
  revert l; induction n; intros l H; destruct l; simpl; try lia; inversion H; subst; auto.
Qed.

Lemma pw_ML_base_nonneg (n: nat) : 0 <= nth n ML_base_tab 0.
Proof. apply pw_nth_nonneg. unfold ML_base_tab. repeat constructor; lia. Qed.

Lemma pw_ML_bits_nonneg (n: nat) : 0 <= nth n ML_bits_tab 0.
Proof. apply pw_nth_nonneg. unfold ML_bits_tab. repeat constructor; lia. Qed.

Lemma pw_decode_seqs_ml (tLL tOF tML: fse_table) (V: list Z) (k: nat) :
  forall sLL sOF sML pos l p, decode_seqs tLL tOF tML V k sLL sOF sML pos = Some (l, p) ->
  Forall (fun sq => 0 <= sq_ml sq) l.
Proof.
  induction k; intros sLL sOF sML pos l p H; cbn [decode_seqs] in H.
  - inversion H; subst; constructor.
  - destruct (rd V pos (fe_sym (fse_cell tOF sOF))) as [[eOF p1]|] eqn:R1; [|discriminate].
    destruct (rd V p1 (nth (Z.to_nat (fe_sym (fse_cell tML sML))) ML_bits_tab 0)) as [[eML p2]|] eqn:R2; [|discriminate].
    destruct (rd V p2 (nth (Z.to_nat (fe_sym (fse_cell tLL sLL))) LL_bits_tab 0)) as [[eLL p3]|] eqn:R3; [|discriminate].
    assert (HML: 0 <= nth (Z.to_nat (fe_sym (fse_cell tML sML))) ML_base_tab 0 + eML).
    { pose proof (pw_ML_base_nonneg (Z.to_nat (fe_sym (fse_cell tML sML)))).
      pose proof (pw_rd_nonneg _ _ _ _ _ R2 (pw_ML_bits_nonneg _)). lia. }
    destruct k.
    + inversion H; subst. constructor; [exact HML|constructor].
    + destruct (rd V p3 _) as [[uLL p4]|]; [|discriminate].
      destruct (rd V p4 _) as [[uML p5]|]; [|discriminate].
      destruct (rd V p5 _) as [[uOF p6]|]; [|discriminate].
      destruct (decode_seqs _ _ _ _ _ _ _ _ _) as [[l' p']|] eqn:RD; [|discriminate].
      inversion H; subst. constructor; [exact HML|]. eapply IHk; exact RD.
Qed.

Lemma pw_decode_seq_stream_ml (tLL tOF tML: fse_table) (s: list Z) (nbSeq: Z) (l: list sequence) :
  decode_seq_stream tLL tOF tML s nbSeq = Some l -> Forall (fun sq => 0 <= sq_ml sq) l.
Proof.
  unfold decode_seq_stream. intros H.
  match type of H with (if ?b then _ else _) = _ => destruct b; [discriminate|] end.
  destruct (rd s _ (ft_log tLL)) as [[a p1]|]; [|discriminate].
  destruct (rd s p1 (ft_log tOF)) as [[b p2]|]; [|discriminate].
  destruct (rd s p2 (ft_log tML)) as [[c p3]|]; [|discriminate].
  destruct (decode_seqs _ _ _ _ _ _ _ _ _) as [[l' p']|] eqn:RD; [|discriminate].
  destruct p'; try discriminate. inversion H; subst. eapply pw_decode_seqs_ml; exact RD.
Qed.

Lemma pw_exec_seqs_w (wsize: Z) (hist: list Z) (seqs: list sequence) :
  Forall (fun sq => 0 <= sq_ml sq) seqs ->
  forall rep lits out x, exec_seqs_w wsize rep hist lits out seqs = Some x ->
  exec_seqs wsize rep hist lits out seqs = Some x.
Proof.
  induction 1 as [|sq rest Hml Hrest IH]; intros rep lits out x H; simpl in *; [exact H|].
  destruct (sq_ll sq >? Zlength lits); [discriminate|].
  destruct (resolve_offset rep (sq_ll sq) (sq_ov sq)) as [[o r]|]; [|discriminate].
  set (out' := out ++ firstn (Z.to_nat (sq_ll sq)) lits) in *.
  destruct (o >? Zlength hist + Zlength out') eqn:E1; [discriminate|].
  destruct ((o >? wsize) && negb ((o >? Zlength out') && (Zlength out' + sq_ml sq <=? wsize))) eqn:E2;
    [discriminate|].
  replace (o >? wsize + Zlength hist) with false; [apply IH; exact H|].
  symmetry. assert (0 <= Zlength hist) by (rewrite Zlength_correct; lia).
  rewrite !Z.gtb_ltb in *. apply Z.ltb_ge in E1. apply Z.ltb_ge.
  destruct (Z.ltb_spec wsize o); destruct (Z.ltb_spec (Zlength out') o);
    destruct (Z.leb_spec (Zlength out' + sq_ml sq) wsize); simpl in E2; try discriminate; lia.
Qed.

Lemma pw_decode_block_w (st: dstate) (hist out b: list Z) (bsm wsize: Z) (x: dstate * list Z) :
  decode_block_w st hist out b bsm wsize = Some x -> decode_block st hist out b bsm wsize = Some x.
Proof.
  unfold decode_block_w, decode_block. intros H.
  destruct (Zlength b >? bsm); [discriminate|].
  destruct (decode_literals (st_huf st) b bsm) as [[[lits lused] huf]|]; [|discriminate].
  destruct (decode_seq_header _ _) as [[[nbSeq tabs] hused]|]; [|discriminate].
  match goal with |- match ?e with _ => _ end = _ => destruct e as [seqs|] eqn:ES end; [|discriminate].
  assert (HF: Forall (fun sq => 0 <= sq_ml sq) seqs).
  { destruct (nbSeq =? 0); [inversion ES; constructor|].
    destruct tabs as [[[tLL tOF] tML]|]; [|discriminate]. eapply pw_decode_seq_stream_ml; exact ES. }
  destruct (exec_seqs_w wsize (st_rep st) hist lits out seqs) as [y|] eqn:EX; [|discriminate].
  rewrite (pw_exec_seqs_w wsize hist seqs HF _ _ _ _ EX). exact H.
Qed.

Lemma pw_blocks_w (fuel: nat) : forall (st: dstate) (hist s out: list Z) (bsm wsize: Z) (x: list Z * Z),
  decode_blocks_w fuel st hist s out bsm wsize = Some x -> decode_blocks fuel st hist s out bsm wsize = Some x.
Proof.
  induction fuel; intros st hist s out bsm wsize x H; cbn [decode_blocks_w decode_blocks] in *; [exact H|].
  destruct (cblock_size s) as [c|]; [|exact H].
  destruct (c >? Zlength s - ZSTD_blockHeaderSize); [exact H|].
  destruct (bp_type (block_props_of s) =? 0); [|destruct (bp_type (block_props_of s) =? 1)].
  3: destruct (decode_block_w st hist out (slice s ZSTD_blockHeaderSize c) bsm wsize) as [[st0 content]|] eqn:EB;
       [rewrite (pw_decode_block_w _ _ _ _ _ _ _ EB)|discriminate].
  1,2: match goal with H: match ?R with _ => _ end = _ |- _ => destruct R as [[st' out']|]; [|exact H] end.
  all: destruct (bp_last (block_props_of s) =? 1); [exact H|].
  all: destruct (decode_blocks_w fuel _ hist _ _ bsm wsize) as [[o k]|] eqn:ER; [|discriminate].
  all: rewrite (IHfuel _ _ _ _ _ _ _ ER); exact H.
Qed.

Lemma pw_exec_seqs_nodict (wsize: Z) (seqs: list sequence) : forall rep lits out,
  exec_seqs_w wsize rep nil lits out seqs = exec_seqs wsize rep nil lits out seqs.
Proof.
  induction seqs as [|sq rest IH]; intros rep lits out; simpl; [reflexivity|].
  destruct (sq_ll sq >? Zlength lits); [reflexivity|].
  destruct (resolve_offset rep (sq_ll sq) (sq_ov sq)) as [[o r]|]; [|reflexivity].
  set (out' := out ++ firstn (Z.to_nat (sq_ll sq)) lits).
  rewrite !Z.gtb_ltb. change (Zlength (@nil Z)) with 0. rewrite ?Z.add_0_l, ?Z.add_0_r.
  destruct (Z.ltb_spec (Zlength out') o); [reflexivity|]. simpl. rewrite Bool.andb_true_r.
  destruct (wsize <? o); [reflexivity|]. apply IH.
Qed.

Lemma pw_decode_block_nodict (st: dstate) (out b: list Z) (bsm wsize: Z) :
  decode_block_w st nil out b bsm wsize = decode_block st nil out b bsm wsize.
Proof.
  unfold decode_block_w, decode_block.
  destruct (Zlength b >? bsm); [reflexivity|].
  destruct (decode_literals (st_huf st) b bsm) as [[[lits lused] huf]|]; [|reflexivity].
  destruct (decode_seq_header _ _) as [[[nbSeq tabs] hused]|]; [|reflexivity].
  match goal with |- match ?e with _ => _ end = _ => destruct e as [seqs|] end; [|reflexivity].
  rewrite pw_exec_seqs_nodict. reflexivity.
Qed.

Lemma pw_blocks_nodict (fuel: nat) : forall (st: dstate) (s out: list Z) (bsm wsize: Z),
  decode_blocks_w fuel st nil s out bsm wsize = decode_blocks fuel st nil s out bsm wsize.
Proof.
  induction fuel; intros st s out bsm wsize; cbn [decode_blocks_w decode_blocks]; [reflexivity|].
  destruct (cblock_size s) as [c|]; [|reflexivity].
  rewrite pw_decode_block_nodict.
  destruct (c >? Zlength s - ZSTD_blockHeaderSize); [reflexivity|].
  match goal with |- match ?R with _ => _ end = _ => destruct R as [[st' out']|]; [|reflexivity] end.
  rewrite IHfuel. reflexivity.
Qed.

Theorem params_w :
  (* strict blocks imply Block.v's blocks, with the same result *)
  (forall (fuel: nat) (st: dstate) (hist s out: list Z) (bsm wsize: Z) (x: list Z * Z),
     decode_blocks_w fuel st hist s out bsm wsize = Some x -> decode_blocks fuel st hist s out bsm wsize = Some x) /\
  (* a frame the strict model decides is decided the same way by the lenient one *)
  (forall (md: dmode) (dm: dict_model) (wl: Z) (s: list Z) (r: fres),
     decode_frame_m (dmode_w md) dm wl s = r -> r <> FUnk -> decode_frame_m md dm wl s = r) /\
  (* without a dictionary the two models agree *)
  (forall (md: dmode) (wl: Z) (s: list Z), decode_frame_m (dmode_w md) no_dict wl s = decode_frame_m md no_dict wl s) /\
  (forall (md: dmode) (wl: Z) (s: list Z),
     series_frames_m (dmode_w md) sel_none (Some no_dict) wl s = series_frames_m md sel_none (Some no_dict) wl s).
Proof.
  split; [exact pw_blocks_w|].
  split.
  { intros md dm wl s r H Hr. subst r. revert Hr. unfold decode_frame_m.
    cbn [md_magicless md_ignore md_bmax md_dwin dmode_w].
    destruct (md_dwin md); [intros; reflexivity|].
    repeat match goal with |- (if ?b then _ else _) <> _ -> _ => destruct b; [intros; reflexivity|] end.
    destruct (get_frame_header_m (md_magicless md) s) as [h| |]; try (intros; reflexivity).
    repeat match goal with |- (if ?b then _ else _) <> _ -> _ => destruct b; [intros; reflexivity|] end.
    match goal with |- match decode_blocks_w ?a ?b ?c ?d ?e ?f ?g with _ => _ end <> _ -> _ =>
      destruct (decode_blocks_w a b c d e f g) as [[out k]|] eqn:EW end.
    - rewrite (pw_blocks_w _ _ _ _ _ _ _ _ EW). intros; reflexivity.
    - intros H; exfalso; apply H; reflexivity. }
  assert (HN: forall (md: dmode) (wl: Z) (s: list Z),
    decode_frame_m (dmode_w md) no_dict wl s = decode_frame_m md no_dict wl s).
  { intros md wl s. unfold decode_frame_m.
    cbn [md_magicless md_ignore md_bmax md_dwin dmode_w].
    destruct (md_dwin md); [reflexivity|].
    destruct (get_frame_header_m (md_magicless md) s) as [h| |]; try reflexivity.
    change (dm_content no_dict) with (@nil Z). rewrite pw_blocks_nodict. reflexivity. }
  split; [exact HN|].
  intros md wl s. unfold series_frames_m.
  assert (FD: forall mg d s', frame_dict mg sel_none (Some d) s' = Some d).
  { intros mg d s'. unfold frame_dict. destruct (get_frame_header_m mg s'); reflexivity. }
  assert (W: forall fuel off s', walk_m fuel (dmode_w md) sel_none (Some no_dict) wl s' off =
                                 walk_m fuel md sel_none (Some no_dict) wl s' off).
  2: apply W.
  clear s. induction fuel; intros off s; cbn [walk_m]; [reflexivity|].
  cbn [md_magicless dmode_w].
  destruct (Zlength s <? starting_len (md_magicless md)); [reflexivity|].
  destruct (negb (md_magicless md) && is_skippable_magic (le_field s 0 4)).
  - destruct (skippable_frame_size s); [|reflexivity].
    unfold sel_none. cbn [md_dwin dmode_w]. destruct (md_dwin md); rewrite IHfuel; reflexivity.
  - rewrite !FD, HN. destruct (decode_frame_m md no_dict wl s); try reflexivity. rewrite IHfuel. reflexivity.
Qed.

Lemma decode_blocks_w_lenient (fuel: nat) (st: dstate) (hist s out: list Z) (bsm wsize: Z) (x: list Z * Z) :
  decode_blocks_w fuel st hist s out bsm wsize = Some x -> decode_blocks fuel st hist s out bsm wsize = Some x.
Proof. apply params_w. Qed.

Lemma decode_frame_m_w_lenient (md: dmode) (dm: dict_model) (wl: Z) (s: list Z) (r: fres) :
  decode_frame_m (dmode_w md) dm wl s = r -> r <> FUnk -> decode_frame_m md dm wl s = r.
Proof. apply params_w. Qed.

Lemma decode_frame_m_w_nodict (md: dmode) (wl: Z) (s: list Z) :
  decode_frame_m (dmode_w md) no_dict wl s = decode_frame_m md no_dict wl s.
Proof. apply params_w. Qed.

Lemma series_frames_m_w_nodict (md: dmode) (wl: Z) (s: list Z) :
  series_frames_m (dmode_w md) sel_none (Some no_dict) wl s = series_frames_m md sel_none (Some no_dict) wl s.
Proof. apply params_w. Qed.
