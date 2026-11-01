(* The writer respects the dictionary window rule of API v3.1 streaming (Params.v md_dwin, exec_seqs_w,
   decode_block_w, decode_frame_m (dmode_w md_dflt)): the strict model decodes the writer's blocks and frames as
   the lenient one does.
   harness/writer.h w_compressed_block draws offsets off <= maxoff = min(pos, window - 1), or pos + dictn when
   dictn > 0 and pos + ml <= window (pos: the frame's content before the match): off_dwin.  Plain Coq;
   wm3_dwin_all is the one statement to prove, the lemmas below are its parts. *)
Require Import Zstd.proof.harness.writer.model.WF_Defs.
Require Import Zstd.proof.harness.writer.model.WF_Header.
Require Import Zstd.proof.harness.writer.model.WF_Frame.
Require Import Zstd.proof.harness.writer.model.WM_BlkDefs.
Require Import Zstd.proof.model.Params.

(* ---------- definitions ---------- *)

(* gen_ok under the strict execution *)
Definition gen_ok_w (wsize: Z) (rep0: Z * Z * Z) (hist out lits: list Z) (seqs: list sequence) (cont: list Z)
    (rep: Z * Z * Z) : Prop :=
  forall Y, exec_seqs_w wsize rep0 hist (lits ++ Y) out seqs = Some (out ++ cont, Y, rep).

(* both: what the writer's sequence loop maintains *)
Definition gen_ok3 (wsize: Z) (rep0: Z * Z * Z) (hist out lits: list Z) (seqs: list sequence) (cont: list Z)
    (rep: Z * Z * Z) : Prop :=
  gen_ok wsize rep0 hist out lits seqs cont rep /\ gen_ok_w wsize rep0 hist out lits seqs cont rep.

(* the window rule of a match at offset off of ml bytes, after pos bytes of the frame's content *)
Definition off_dwin (wsize pos ml off: Z) : Prop := wsize < off -> pos < off /\ pos + ml <= wsize.

(* the strict part of WF_Defs.wblock_ok: a compressed block decodes the same under decode_block_w *)
Definition wblock_w (bsm wsize: Z) (hist: list Z) (st: dstate) (out: list Z) (last: bool)
    (b: list Z) (st': dstate) (c: list Z) : Prop :=
  exists ty bsize body,
    b = le_bytes 3 (blk_hv last ty bsize) ++ body /\ bytes_ok body /\ bytes_ok c /\ 0 <= bsize <= bsm /\
    ((ty = 0 /\ body = c /\ bsize = Zlength c /\ st' = st) \/
     (ty = 1 /\ 1 <= bsm /\ (exists x, body = [x] /\ c = repeat x (Z.to_nat bsize)) /\ st' = st) \/
     (ty = 2 /\ bsize = Zlength body /\ decode_block st hist out body bsm wsize = Some (st', c) /\
      decode_block_w st hist out body bsm wsize = Some (st', c))).

(* WF_Defs.wblocks_pre with wblock_w *)
Inductive wblocks_pre_w (bsm wsize: Z) (hist: list Z) (st0: dstate) : list Z -> dstate -> list Z -> Z -> Prop :=
| wbpw_nil : wblocks_pre_w bsm wsize hist st0 [] st0 [] 0
| wbpw_snoc : forall bb st out nb b st' c,
    wblocks_pre_w bsm wsize hist st0 bb st out nb ->
    wblock_w bsm wsize hist st out false b st' c ->
    wblocks_pre_w bsm wsize hist st0 (bb ++ b) st' (out ++ c) (nb + 1).

(* a Zstandard frame fb decodes under the strict streaming model as under Series.v's, followed by anything *)
Definition zframe_w (dm: dict_model) (fb: list Z) : Prop :=
  forall wl t, decode_frame_m (dmode_w md_dflt) dm wl (fb ++ t) = decode_frame dm wl (fb ++ t).

(* ---------- helpers ---------- *)

Lemma dw_lz_copy_prefix : forall hist off m cur, exists t, lz_copy hist cur off m = cur ++ t.
Proof.
  intros hist off m; induction m as [|m IH]; intros cur; simpl.
  - exists []. rewrite app_nil_r. reflexivity.
  - destruct (IH (cur ++ [byte_at (hist ++ cur) (Zlength hist + Zlength cur - off)])) as [t Ht].
    rewrite Ht, <- app_assoc. eexists. reflexivity.
Qed.

Lemma dw_lz_copy_app : forall hist cur off m, lz_copy hist cur off m = cur ++ lz_tail hist cur off m.
Proof.
  intros hist cur off m. unfold lz_tail.
  destruct (dw_lz_copy_prefix hist off m cur) as [t Ht]. rewrite Ht.
  rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity.
Qed.

Lemma dw_exec_seqs_app : forall wsize s1 s2 rep hist lits out,
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

Lemma dw_exec_seqs_w_app : forall wsize s1 s2 rep hist lits out,
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

Lemma dw_gen_step : forall wsize rep0 hist out lits seqs cont rep L ll ml ov off rep',
  gen_ok wsize rep0 hist out lits seqs cont rep ->
  Zlength L = ll -> 0 <= ml ->
  resolve_offset rep ll ov = Some (off, rep') ->
  off <= Zlength hist + Zlength out + Zlength cont + ll -> off <= wsize + Zlength hist ->
  gen_ok wsize rep0 hist out (lits ++ L) (seqs ++ [{| sq_ll := ll; sq_ml := ml; sq_ov := ov |}])
    (cont ++ L ++ lz_tail hist (out ++ cont ++ L) off (Z.to_nat ml)) rep'.
Proof.
  intros wsize rep0 hist out lits seqs cont rep L ll ml ov off rep' Hg HL Hml Hres Hoff1 Hoff2 Y.
  rewrite dw_exec_seqs_app, <- app_assoc, Hg. simpl.
  assert (E1: ll >? Zlength (L ++ Y) = false).
  { rewrite Z.gtb_ltb; apply Z.ltb_ge. rewrite <- HL, !Zlength_correct, app_length. lia. }
  rewrite E1.
  assert (Hn: Z.to_nat ll = length L) by (rewrite <- HL, Zlength_correct; lia).
  rewrite Hn, firstn_app, firstn_all, Nat.sub_diag, firstn_O, app_nil_r.
  rewrite skipn_app, skipn_all, Nat.sub_diag, skipn_O. simpl. rewrite Hres.
  assert (E2: off >? Zlength hist + Zlength ((out ++ cont) ++ L) = false).
  { rewrite Z.gtb_ltb; apply Z.ltb_ge. rewrite !Zlength_correct, !app_length in *. lia. }
  assert (E3: off >? wsize + Zlength hist = false) by (rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
  rewrite E2, E3. simpl. rewrite dw_lz_copy_app, !app_assoc. reflexivity.
Qed.

Lemma dw_gen_step_w : forall wsize rep0 hist out lits seqs cont rep L ll ml ov off rep',
  gen_ok_w wsize rep0 hist out lits seqs cont rep ->
  Zlength L = ll -> 0 <= ml ->
  resolve_offset rep ll ov = Some (off, rep') ->
  off <= Zlength hist + Zlength out + Zlength cont + ll ->
  off_dwin wsize (Zlength out + Zlength cont + ll) ml off ->
  gen_ok_w wsize rep0 hist out (lits ++ L) (seqs ++ [{| sq_ll := ll; sq_ml := ml; sq_ov := ov |}])
    (cont ++ L ++ lz_tail hist (out ++ cont ++ L) off (Z.to_nat ml)) rep'.
Proof.
  intros wsize rep0 hist out lits seqs cont rep L ll ml ov off rep' Hg HL Hml Hres Hoff1 Hdw Y.
  rewrite dw_exec_seqs_w_app, <- app_assoc, Hg. simpl.
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
  rewrite E2, E3. simpl. rewrite dw_lz_copy_app, !app_assoc. reflexivity.
Qed.

Lemma dw_decode_block_ok_w : forall st hist out lb sb bsm wsize lits seqs hnew tabs cont trail rep',
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

Lemma dw_fh_bmax (s: list Z) (h: frame_header) :
  get_frame_header s = FH_ok h -> fh_blockSizeMax h <= ZSTD_BLOCKSIZE_MAX.
Proof.
  unfold get_frame_header. intros H.
  repeat match type of H with
  | context [if ?c then _ else _] => destruct c
  end; try discriminate; inversion H; subst; simpl;
  unfold ZSTD_BLOCKSIZE_MAX; lia.
Qed.

Lemma dw_frame_dflt (dm: dict_model) (wl: Z) (s: list Z) : decode_frame_m md_dflt dm wl s = decode_frame dm wl s.
Proof.
  unfold decode_frame_m, decode_frame, get_frame_header_m. simpl md_magicless. simpl md_ignore. simpl md_bmax.
  cbv beta iota zeta. rewrite !Z.sub_0_r.
  destruct (get_frame_header s) as [|k|h] eqn:E; try reflexivity.
  cbn [negb andb]. rewrite (Z.min_l _ _ (dw_fh_bmax s h E)). reflexivity.
Qed.

Lemma dw_frame_bridge (dm: dict_model) (wl: Z) (s: list Z) :
  (forall h, get_frame_header s = FH_ok h ->
     decode_blocks_w (length (skipn (Z.to_nat (fh_headerSize h)) s)) (dm_state dm) (dm_content dm)
       (skipn (Z.to_nat (fh_headerSize h)) s) nil (Z.min (fh_blockSizeMax h) ZSTD_BLOCKSIZE_MAX) (fh_windowSize h) =
     decode_blocks (length (skipn (Z.to_nat (fh_headerSize h)) s)) (dm_state dm) (dm_content dm)
       (skipn (Z.to_nat (fh_headerSize h)) s) nil (Z.min (fh_blockSizeMax h) ZSTD_BLOCKSIZE_MAX) (fh_windowSize h)) ->
  decode_frame_m (dmode_w md_dflt) dm wl s = decode_frame dm wl s.
Proof.
  intros H. rewrite <- dw_frame_dflt.
  unfold decode_frame_m, get_frame_header_m. simpl md_magicless. simpl md_ignore. simpl md_bmax. simpl md_dwin.
  cbv beta iota zeta.
  destruct (get_frame_header s) as [|k|h] eqn:E; try reflexivity.
  cbn [md_dwin dmode_w md_dflt negb]. rewrite (H h eq_refl). reflexivity.
Qed.

(* a block whose compressed case also decodes strictly (the shape wf_zframe_w needs of each block) *)
Definition dw_blk (bsm wsize: Z) (hist: list Z) (st: dstate) (out: list Z) (last: bool)
    (b: list Z) (st': dstate) (c: list Z) : Prop :=
  exists ty bsize body,
    b = le_bytes 3 (blk_hv last ty bsize) ++ body /\ bytes_ok body /\ bytes_ok c /\ 0 <= bsize <= bsm /\
    ((ty = 0 /\ body = c /\ bsize = Zlength c /\ st' = st) \/
     (ty = 1 /\ 1 <= bsm /\ (exists x, body = [x] /\ c = repeat x (Z.to_nat bsize)) /\ st' = st) \/
     (ty = 2 /\ bsize = Zlength body /\ decode_block_w st hist out body bsm wsize = Some (st', c))).

Lemma dw_step : forall bsm wsize hist st out last b st' c f t,
  bsm <= 2 ^ 17 ->
  dw_blk bsm wsize hist st out last b st' c ->
  3 <= Zlength b /\
  decode_blocks_w (S f) st hist (b ++ t) out bsm wsize =
    (if last then Some (out ++ c, Zlength b)
     else match decode_blocks_w f st' hist t (out ++ c) bsm wsize with
          | Some (o, k) => Some (o, Zlength b + k) | None => None end).
Proof.
  intros bsm wsize hist st out last b st' c f t Hbsm
    (ty & bsize & body & -> & Hbody & Hc & Hbs & Hcase).
  assert (Hty: 0 <= ty <= 2) by (destruct Hcase as [(-> & _) | [(-> & _) | (-> & _)]]; lia).
  pose proof (WF_Blocks.wfb_props last ty bsize body t Hty ltac:(lia)) as Hp.
  pose proof (WF_Blocks.wfb_zlen_nonneg t).
  pose proof (WF_Blocks.wfb_zlen_nonneg body).
  assert (Hlen3: Zlength (le_bytes 3 (blk_hv last ty bsize)) = 3).
  { rewrite Zlength_correct, WF_Blocks.wfb_le_bytes_len. reflexivity. }
  assert (Hskip: skipn (Z.to_nat (3 + Zlength body)) ((le_bytes 3 (blk_hv last ty bsize) ++ body) ++ t) = t).
  { rewrite Zlength_correct.
    replace (Z.to_nat (3 + Z.of_nat (length body))) with (length (le_bytes 3 (blk_hv last ty bsize) ++ body))
      by (rewrite app_length, WF_Blocks.wfb_le_bytes_len; lia).
    rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity. }
  assert (Hslice: slice ((le_bytes 3 (blk_hv last ty bsize) ++ body) ++ t) 3 (Zlength body) = body).
  { unfold slice. rewrite <- app_assoc. change (Z.to_nat 3) with 3%nat.
    rewrite skipn_app, WF_Blocks.wfb_le_bytes_len.
    rewrite skipn_all2 by (rewrite WF_Blocks.wfb_le_bytes_len; lia).
    simpl. rewrite firstn_app, Zlength_correct, Nat2Z.id, firstn_all, Nat.sub_diag, firstn_O, app_nil_r.
    reflexivity. }
  assert (HlenS: Zlength ((le_bytes 3 (blk_hv last ty bsize) ++ body) ++ t) = 3 + Zlength body + Zlength t).
  { rewrite !WF_Blocks.wfb_zlen_app, Hlen3. lia. }
  assert (Hbl: Zlength (le_bytes 3 (blk_hv last ty bsize) ++ body) = 3 + Zlength body).
  { rewrite WF_Blocks.wfb_zlen_app, Hlen3. lia. }
  split; [lia |].
  unfold cblock_size. cbn [decode_blocks_w]. unfold cblock_size.
  rewrite Hp, HlenS. cbn [bp_type bp_last bp_origSize]. unfold ZSTD_blockHeaderSize.
  replace (3 + Zlength body + Zlength t <? 3) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite Hbl.
  destruct Hcase as [(-> & -> & -> & ->) | [(-> & Hb1 & (x & -> & ->) & ->) | (-> & -> & Hd)]].
  - simpl (0 =? 1); simpl (0 =? 3); simpl (0 =? 0); cbv iota.
    rewrite Hslice, Hskip. repeat (rewrite WF_Blocks.wfb_gtb_false by lia).
    destruct last; cbn; auto.
  - change (Zlength [x]) with 1 in *. simpl (1 =? 1); simpl (1 =? 0); cbv iota.
    rewrite Hslice, Hskip.
    repeat (rewrite WF_Blocks.wfb_gtb_false by lia).
    destruct last; cbn; auto.
  - simpl (2 =? 1); simpl (2 =? 3); simpl (2 =? 0); cbv iota.
    rewrite Hslice, Hd, Hskip. repeat (rewrite WF_Blocks.wfb_gtb_false by lia).
    destruct last; cbn; auto.
Qed.

Lemma dw_conv : forall bsm wsize hist st out last b st' c,
  wblock_w bsm wsize hist st out last b st' c -> dw_blk bsm wsize hist st out last b st' c.
Proof.
  intros bsm wsize hist st out last b st' c (ty & bsize & body & Hb & Hbo & Hc & Hbs & Hcase).
  exists ty, bsize, body. split; [exact Hb|]. split; [exact Hbo|]. split; [exact Hc|]. split; [exact Hbs|].
  destruct Hcase as [H | [H | (H1 & H2 & _ & H4)]]; [left | right; left | right; right]; auto.
Qed.

Lemma dw_pre : forall bsm wsize hist st0 bb st out nb,
  bsm <= 2 ^ 17 ->
  (forall st out last b st' c, wblock_w bsm wsize hist st out last b st' c -> dw_blk bsm wsize hist st out last b st' c) ->
  wblocks_pre_w bsm wsize hist st0 bb st out nb ->
  0 <= nb /\ 3 * nb <= Zlength bb /\
  (forall f t, decode_blocks_w (Z.to_nat nb + f) st0 hist (bb ++ t) nil bsm wsize =
     match decode_blocks_w f st hist t out bsm wsize with
     | Some (o, k) => Some (o, Zlength bb + k) | None => None end).
Proof.
  intros bsm wsize hist st0 bb st out nb Hbsm Hconv H.
  induction H as [| bb st out nb b st' c Hpre IH Hb].
  - split; [lia |]. split; [rewrite Zlength_correct; simpl; lia |].
    intros f t; simpl.
    destruct (decode_blocks_w f st0 hist t [] bsm wsize) as [[o k]|]; auto.
  - apply Hconv in Hb.
    destruct IH as (Hnb & Hlen & IHd).
    split; [lia | split].
    + destruct (dw_step _ _ _ _ _ _ _ _ _ O nil Hbsm Hb) as (H3 & _).
      rewrite WF_Blocks.wfb_zlen_app. lia.
    + intros f t; replace (Z.to_nat (nb + 1) + f)%nat with (Z.to_nat nb + S f)%nat by lia;
        rewrite <- app_assoc.
      rewrite IHd. destruct (dw_step _ _ _ _ _ _ _ _ _ f t Hbsm Hb) as (_ & ->).
      destruct (decode_blocks_w f st' hist t (out ++ c) bsm wsize) as [[o k]|]; auto.
      rewrite WF_Blocks.wfb_zlen_app. f_equal. f_equal. lia.
Qed.

Lemma dw_blocks : forall bsm wsize hist st0 bb st out nb b st' c t fuel,
  0 <= bsm <= 2 ^ 17 ->
  (forall st out last b st' c, wblock_w bsm wsize hist st out last b st' c -> dw_blk bsm wsize hist st out last b st' c) ->
  wblocks_pre_w bsm wsize hist st0 bb st out nb ->
  wblock_w bsm wsize hist st out true b st' c ->
  (length (bb ++ b) <= fuel)%nat ->
  decode_blocks_w fuel st0 hist (bb ++ b ++ t) nil bsm wsize = Some (out ++ c, Zlength (bb ++ b)).
Proof.
  intros bsm wsize hist st0 bb st out nb b st' c t fuel Hbsm Hconv Hpre Hb Hfuel.
  apply Hconv in Hb.
  destruct (dw_pre bsm wsize hist st0 bb st out nb ltac:(lia) Hconv Hpre) as (Hnb & Hlen & Hd).
  destruct (dw_step bsm wsize hist st out true b st' c O nil ltac:(lia) Hb) as (H3 & _).
  rewrite app_length in Hfuel.
  rewrite Zlength_correct in Hlen, H3.
  replace fuel with (Z.to_nat nb + S (fuel - Z.to_nat nb - 1))%nat by lia.
  rewrite Hd.
  destruct (dw_step bsm wsize hist st out true b st' c (fuel - Z.to_nat nb - 1) t ltac:(lia) Hb) as (_ & ->).
  rewrite WF_Blocks.wfb_zlen_app. reflexivity.
Qed.

Definition dw_f0 : winfo :=
  {| wi_skippable := false; wi_variant := 0; wi_start := 0; wi_size := 0; wi_cstart := 0; wi_csize := 0;
     wi_fcs_present := false; wi_fcs := 0; wi_did_size := 0; wi_did := 0; wi_single := false; wi_window := 0;
     wi_window_log := 0; wi_checksum := false; wi_blocks := 0; wi_skip_n := 0; wi_hsize := 0;
     wi_uses_dict := false |}.

Lemma dw_zframe : forall dm p nb bb st out b st' c,
  (forall st out last b st' c, wblock_w (hp_bsm p) (hp_window p) (dm_content dm) st out last b st' c ->
     dw_blk (hp_bsm p) (hp_window p) (dm_content dm) st out last b st' c) ->
  hp_ok dm p ->
  wblocks_pre (hp_bsm p) (hp_window p) (dm_content dm) (dm_state dm) bb st out nb ->
  wblock_ok (hp_bsm p) (hp_window p) (dm_content dm) st out true b st' c ->
  wblocks_pre_w (hp_bsm p) (hp_window p) (dm_content dm) (dm_state dm) bb st out nb ->
  wblock_w (hp_bsm p) (hp_window p) (dm_content dm) st out true b st' c ->
  zframe_w dm (hp_bytes p ++ bb ++ b ++ hp_ck_bytes p (out ++ c)).
Proof.
  intros dm p nb bb st out b st' c Hconv Hok Hpre Hb Hprew Hbw wl t.
  pose proof (wfz_window_nonneg dm p Hok) as Hw0.
  assert (Hbsm: 0 <= hp_bsm p <= 2 ^ 17) by (unfold hp_bsm; lia).
  apply dw_frame_bridge. intros h Eh.
  set (r := hp_ck_bytes p (out ++ c) ++ t).
  assert (Hs: (hp_bytes p ++ bb ++ b ++ hp_ck_bytes p (out ++ c)) ++ t = hp_bytes p ++ bb ++ b ++ r)
    by (subst r; rewrite !app_assoc; reflexivity).
  rewrite Hs in *.
  rewrite (wf_hdr_gfh dm dw_f0 p 0 false (bb ++ b ++ r) Hok eq_refl) in Eh.
  destruct (wi_big (hp_info dw_f0 p 0 false)); [discriminate|].
  inversion Eh as [Eh']; clear Eh. subst h. rewrite wfz_header by reflexivity.
  cbn [fh_headerSize fh_blockSizeMax fh_windowSize].
  rewrite WF_Frame.wfz_skipn_app.
  rewrite Z.min_l by (unfold hp_bsm, ZSTD_BLOCKSIZE_MAX; lia).
  assert (Hf: (length (bb ++ b) <= length (bb ++ b ++ r))%nat) by (rewrite app_assoc, (app_length (bb ++ b)); lia).
  rewrite (dw_blocks _ _ _ _ _ _ _ _ _ _ _ _ _ Hbsm Hconv Hprew Hbw Hf).
  destruct (WF_Blocks.wf_blocks (hp_bsm p) (hp_window p) (dm_content dm) (dm_state dm) bb st out nb b st' c r
               (length (bb ++ b ++ r)) Hbsm Hpre Hb Hf) as (_ & _ & _ & H1 & _).
  rewrite H1. reflexivity.
Qed.

(* ---------- the statement ---------- *)

Theorem wm3_dwin_all :
  (* WM_BlkGen.gen_step, for both executions *)
  (forall wsize rep0 hist out lits seqs cont rep L ll ml ov off rep',
    gen_ok3 wsize rep0 hist out lits seqs cont rep ->
    Zlength L = ll -> 0 <= ml ->
    resolve_offset rep ll ov = Some (off, rep') ->
    off <= Zlength hist + Zlength out + Zlength cont + ll -> off <= wsize + Zlength hist ->
    off_dwin wsize (Zlength out + Zlength cont + ll) ml off ->
    gen_ok3 wsize rep0 hist out (lits ++ L) (seqs ++ [{| sq_ll := ll; sq_ml := ml; sq_ov := ov |}])
      (cont ++ L ++ lz_tail hist (out ++ cont ++ L) off (Z.to_nat ml)) rep') /\
  (* WM_BlkAsm.decode_block_ok, strict *)
  (forall st hist out lb sb bsm wsize lits seqs hnew tabs cont trail rep',
    lit_ok (st_huf st) bsm lits hnew lb ->
    seqsec_ok (st_seq st) seqs tabs sb ->
    exec_seqs_w wsize (st_rep st) hist lits out seqs = Some (out ++ cont, trail, rep') ->
    Zlength (lb ++ sb) <= bsm -> Zlength (cont ++ trail) <= bsm ->
    decode_block_w st hist out (lb ++ sb) bsm wsize =
      Some ({| st_huf := hnew; st_seq := tabs; st_rep := rep' |}, cont ++ trail)) /\
  (* WF_Frame.wf_zframe_ok, strict *)
  (forall dm p nb bb st out b st' c,
    hp_ok dm p -> 0 <= nb < 6 ->
    wblocks_pre (hp_bsm p) (hp_window p) (dm_content dm) (dm_state dm) bb st out nb ->
    wblock_ok (hp_bsm p) (hp_window p) (dm_content dm) st out true b st' c ->
    wblocks_pre_w (hp_bsm p) (hp_window p) (dm_content dm) (dm_state dm) bb st out nb ->
    wblock_w (hp_bsm p) (hp_window p) (dm_content dm) st out true b st' c ->
    Zlength (out ++ c) = hp_n p ->
    zframe_w dm (hp_bytes p ++ bb ++ b ++ hp_ck_bytes p (out ++ c))).
Proof.
  split; [| split].
  - intros. split.
    + eapply dw_gen_step; eauto. apply H.
    + eapply dw_gen_step_w; eauto. apply H.
  - exact dw_decode_block_ok_w.
  - intros dm p nb bb st out b st' c Hok _ Hpre Hb Hprew Hbw _.
    apply (dw_zframe dm p nb bb st out b st' c); auto.
    intros. apply dw_conv. assumption.
Qed.

(* ---------- the parts ---------- *)

Lemma gen_nil3 : forall wsize rep0 hist out, gen_ok3 wsize rep0 hist out [] [] [] rep0.
Proof. intros. split; intros Y; simpl; rewrite app_nil_r; reflexivity. Qed.

Lemma gen_ok3_ok : forall wsize rep0 hist out lits seqs cont rep,
  gen_ok3 wsize rep0 hist out lits seqs cont rep -> gen_ok wsize rep0 hist out lits seqs cont rep.
Proof. intros. apply H. Qed.

Lemma gen_ok3_w : forall wsize rep0 hist out lits seqs cont rep,
  gen_ok3 wsize rep0 hist out lits seqs cont rep -> gen_ok_w wsize rep0 hist out lits seqs cont rep.
Proof. intros. apply H. Qed.

Lemma gen_step3 : forall wsize rep0 hist out lits seqs cont rep L ll ml ov off rep',
  gen_ok3 wsize rep0 hist out lits seqs cont rep ->
  Zlength L = ll -> 0 <= ml ->
  resolve_offset rep ll ov = Some (off, rep') ->
  off <= Zlength hist + Zlength out + Zlength cont + ll -> off <= wsize + Zlength hist ->
  off_dwin wsize (Zlength out + Zlength cont + ll) ml off ->
  gen_ok3 wsize rep0 hist out (lits ++ L) (seqs ++ [{| sq_ll := ll; sq_ml := ml; sq_ov := ov |}])
    (cont ++ L ++ lz_tail hist (out ++ cont ++ L) off (Z.to_nat ml)) rep'.
Proof. exact (proj1 wm3_dwin_all). Qed.

Theorem decode_block_ok_w : forall st hist out lb sb bsm wsize lits seqs hnew tabs cont trail rep',
  lit_ok (st_huf st) bsm lits hnew lb ->
  seqsec_ok (st_seq st) seqs tabs sb ->
  exec_seqs_w wsize (st_rep st) hist lits out seqs = Some (out ++ cont, trail, rep') ->
  Zlength (lb ++ sb) <= bsm -> Zlength (cont ++ trail) <= bsm ->
  decode_block_w st hist out (lb ++ sb) bsm wsize =
    Some ({| st_huf := hnew; st_seq := tabs; st_rep := rep' |}, cont ++ trail).
Proof. exact (proj1 (proj2 wm3_dwin_all)). Qed.

Theorem wf_zframe_w : forall dm p nb bb st out b st' c,
  hp_ok dm p -> 0 <= nb < 6 ->
  wblocks_pre (hp_bsm p) (hp_window p) (dm_content dm) (dm_state dm) bb st out nb ->
  wblock_ok (hp_bsm p) (hp_window p) (dm_content dm) st out true b st' c ->
  wblocks_pre_w (hp_bsm p) (hp_window p) (dm_content dm) (dm_state dm) bb st out nb ->
  wblock_w (hp_bsm p) (hp_window p) (dm_content dm) st out true b st' c ->
  Zlength (out ++ c) = hp_n p ->
  zframe_w dm (hp_bytes p ++ bb ++ b ++ hp_ck_bytes p (out ++ c)).
Proof. exact (proj2 (proj2 wm3_dwin_all)). Qed.
