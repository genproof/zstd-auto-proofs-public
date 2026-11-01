(* ZSTD_decompressBlock_internal is exact (DecIface.block_exact): the model facts behind it, one lemma per exit of
   the C's body (lib/decompress/zstd_decompress_block.c 2194-2303), each from the exact clauses of the callees
   (BlkIface.lits_exact for ZSTD_decodeLiteralsBlock, xb_seq_header for ZSTD_decodeSeqHeaders, seqs_exact for the
   three sequence decoders).  Plain reasoning over model/ExBlock.v's x_block; the VST proof (BlkTOP3.v) only
   collects the callees' clauses and applies these lemmas. *)
Require Export Zstd.proof.dec.B.blk.BlkIface.
Require Import Zstd.proof.model.ExHuf Zstd.proof.model.ExCSeq Zstd.proof.model.ExBlock.

(* the block is larger than blockSizeMax: srcSize_wrong, before anything else *)
Lemma bx_big (ts: tstate) (o: outarr) (i: inwin) (h: hctx) (bsm streaming r: Z) (oc': list val)
    (ts': option tstate) :
  bsm < Zlength (iw_s i) -> is_error_code r = true ->
  block_exact ts o i h bsm streaming r oc' ts'.
Proof.
  intros Hb Herr rb mem ps ds de _ _ _ _ _ _ _. unfold x_block. rewrite (proj2 (Z.gtb_lt _ _) Hb). exact Herr.
Qed.

(* the literals section fails: the block returns its error *)
Lemma bx_lits_err (ts: tstate) (o: outarr) (i: inwin) (h: hctx) (bsm streaming r1: Z) (oc1: list val)
    (l: litloc) (lits: list Z) (hx': option xhuf) (lxb': list Z) (oc': list val) (ts': option tstate) :
  Zlength (iw_s i) <= bsm ->
  lits_exact (option_map (xhuf_of (ts_x2 ts)) (st_huf ts)) (ts_lxb ts) o i bsm streaming r1 oc1 l lits hx' lxb' ->
  is_error_code r1 = true ->
  block_exact ts o i h bsm streaming r1 oc' ts'.
Proof.
  intros Hs HL Herr rb mem ps ds de Hrb HN Hsub _ _ _ _. specialize (HL rb mem Hrb HN Hsub). cbv zeta in HL.
  unfold xb_lits in HL. unfold x_block. rewrite Z.gtb_ltb, (proj2 (Z.ltb_ge _ _) Hs). cbn [ts_x x_huf x_seq x_rep x_lxb].
  destruct (x_lits _ _ _ _ _ _ _) as [[[lits0 lused] hx0]|]; [| exact Herr].
  destruct (x_seq_header _ _ _) as [[[nbSeq tabs] hused]|]; [| exact Herr].
  destruct ((nbSeq >? 0) && (oa_cap o =? 0))%bool; [exact Herr |].
  destruct (x_lits_store _ _ _ _ _ _ _ _ _) as [[[[[m lr] li] lim] sp]|];
    [destruct HL as [HL _]; congruence | exact Herr].
Qed.

(* the literals section succeeds (r1 bytes) and the sequences header after it fails *)
Lemma bx_hdr_err (ts: tstate) (o: outarr) (i: inwin) (h: hctx) (bsm streaming r1: Z) (oc1: list val)
    (l: litloc) (lits: list Z) (oh': option huf_table) (x2': bool) (lxb': list Z) (r: Z) (oc': list val)
    (ts': option tstate) :
  Zlength (iw_s i) <= bsm ->
  lits_exact (option_map (xhuf_of (ts_x2 ts)) (st_huf ts)) (ts_lxb ts) o i bsm streaming r1 oc1 l lits
    (option_map (xhuf_of x2') oh') lxb' ->
  is_error_code r1 = false ->
  xb_seq_header (st_seq ts) (skipn (Z.to_nat r1) (iw_s i)) = None ->
  is_error_code r = true ->
  block_exact ts o i h bsm streaming r oc' ts'.
Proof.
  intros Hs HL Herr1 Hh Herr rb mem ps ds de Hrb HN Hsub _ _ _ _. specialize (HL rb mem Hrb HN Hsub). cbv zeta in HL.
  unfold xb_lits in HL. unfold x_block. rewrite Z.gtb_ltb, (proj2 (Z.ltb_ge _ _) Hs). cbn [ts_x x_huf x_seq x_rep x_lxb].
  destruct (x_lits _ _ _ _ _ _ _) as [[[lits0 lused] hx0]|]; [| congruence].
  destruct (x_lits_store _ _ _ _ _ _ _ _ _) as [[[[[m lr] li] lim] sp]|]; [| congruence].
  destruct HL as (_ & <- & _). unfold xb_seq_header in Hh. rewrite Hh. exact Herr.
Qed.

(* nbSeq > 0 sequences and no room (dstCapacity = 0): dstSize_tooSmall *)
Lemma bx_room_err (ts: tstate) (o: outarr) (i: inwin) (h: hctx) (bsm streaming r1: Z) (oc1: list val)
    (l: litloc) (lits: list Z) (oh': option huf_table) (x2': bool) (lxb': list Z)
    (nb: Z) (os': option seq_tabs) (used: Z) (r: Z) (oc': list val) (ts': option tstate) :
  Zlength (iw_s i) <= bsm ->
  lits_exact (option_map (xhuf_of (ts_x2 ts)) (st_huf ts)) (ts_lxb ts) o i bsm streaming r1 oc1 l lits
    (option_map (xhuf_of x2') oh') lxb' ->
  is_error_code r1 = false ->
  xb_seq_header (st_seq ts) (skipn (Z.to_nat r1) (iw_s i)) = Some (nb, os', used) ->
  oa_cap o = 0 -> 0 < nb ->
  is_error_code r = true ->
  block_exact ts o i h bsm streaming r oc' ts'.
Proof.
  intros Hs HL Herr1 Hh Hc Hnb Herr rb mem ps ds de Hrb HN Hsub _ _ _ _. specialize (HL rb mem Hrb HN Hsub).
  cbv zeta in HL. unfold xb_lits in HL. unfold x_block. rewrite Z.gtb_ltb, (proj2 (Z.ltb_ge _ _) Hs).
  cbn [ts_x x_huf x_seq x_rep x_lxb].
  destruct (x_lits _ _ _ _ _ _ _) as [[[lits0 lused] hx0]|]; [| congruence].
  destruct (x_lits_store _ _ _ _ _ _ _ _ _) as [[[[[m lr] li] lim] sp]|]; [| congruence].
  destruct HL as (_ & <- & _). unfold xb_seq_header in Hh. rewrite Hh, Hc, Z.gtb_ltb, (proj2 (Z.ltb_lt _ _) Hnb).
  exact Herr.
Qed.

(* ---------- model facts behind the success exit ---------- *)

(* the never-written cells of the destination region after m' are never-written after m: the model's stores
   only add written cells *)
Definition dst_le (m m': xmem) : Prop :=
  forall j, nth j (xm_dst m) None <> None -> nth j (xm_dst m') None <> None.

Lemma dst_le_refl (m: xmem) : dst_le m m.
Proof. intros j H; exact H. Qed.

Lemma dst_le_trans (m1 m2 m3: xmem) : dst_le m1 m2 -> dst_le m2 m3 -> dst_le m1 m3.
Proof. unfold dst_le; auto. Qed.

Lemma nth_upd_ne {A} (l: list A) (i j: nat) (x d: A) : i <> j -> nth j (upd l i x) d = nth j l d.
Proof.
  revert i j; induction l as [|y l IH]; intros [|i] [|j] H; cbn; auto; congruence.
Qed.

Lemma nth_upd_eq {A} (l: list A) (i: nat) (x d: A) : (i < length l)%nat -> nth i (upd l i x) d = x.
Proof.
  revert i; induction l as [|y l IH]; intros [|i] H; cbn in *; try lia; auto. apply IH; lia.
Qed.

(* one store: it adds its cell (a destination store keeps litExtraBuffer) *)
Lemma xm_wr_facts (m: xmem) (r: xreg) (i v: Z) (m': xmem) :
  xm_wr m r i v = Some m' ->
  dst_le m m' /\ 0 <= i /\ (r = R_dst -> nth (Z.to_nat i) (xm_dst m') None = Some v /\ xm_lxb m' = xm_lxb m).
Proof.
  unfold xm_wr. destruct (i <? 0) eqn:Hi; [discriminate |]. apply Z.ltb_ge in Hi.
  destruct r.
  - intros [= <-]. unfold dst_le; cbn [xm_dst xm_lxb]. destruct (i <? Zlength (xm_dst m)) eqn:Hl.
    + apply Z.ltb_lt in Hl. rewrite Zlength_correct in Hl. split; [| split; [lia |]].
      * intros j Hj. destruct (Nat.eq_dec (Z.to_nat i) j) as [<- | Hne].
        -- rewrite nth_upd_eq by lia. congruence.
        -- rewrite nth_upd_ne by exact Hne. exact Hj.
      * intros _. split; [| reflexivity]. apply nth_upd_eq. lia.
    + apply Z.ltb_ge in Hl. rewrite Zlength_correct in Hl. split; [| split; [lia |]].
      * intros j Hj. destruct (Nat.lt_ge_cases j (length (xm_dst m))) as [Hlt | Hge].
        -- rewrite app_nth1 by exact Hlt. exact Hj.
        -- rewrite nth_overflow in Hj by exact Hge. congruence.
      * intros _. split; [| reflexivity]. rewrite Zlength_correct, app_nth2 by lia. rewrite app_nth2 by (rewrite repeat_length; lia).
        rewrite repeat_length. replace (Z.to_nat i - length (xm_dst m) - Z.to_nat (i - Z.of_nat (length (xm_dst m))))%nat
          with O by lia. reflexivity.
  - destruct (i <? Zlength (xm_lxb m)); [intros [= <-] | discriminate].
    split; [intros j Hj; exact Hj |]. split; [lia | discriminate].
  - discriminate.
Qed.

(* k bytes copied forwards: the cells [d, d + k) are written (for a destination copy), litExtraBuffer is kept *)
Lemma xm_fwd_facts (src: list Z) (k: nat) : forall (m: xmem) (rd: xreg) (d: Z) (rs: xreg) (s: Z) (m': xmem),
  xm_fwd src k m rd d rs s = Some m' ->
  dst_le m m' /\ ((k > 0)%nat -> 0 <= d) /\
  (rd = R_dst -> xm_lxb m' = xm_lxb m /\
                 forall j, d <= j < d + Z.of_nat k -> nth (Z.to_nat j) (xm_dst m') None <> None).
Proof.
  induction k as [|k IH]; intros m rd d rs s m' H; cbn in H.
  - injection H as <-. split; [apply dst_le_refl |]. split; [lia |]. intros _. split; [reflexivity | lia].
  - destruct (xm_rd src m rs s) as [v |]; [| discriminate].
    destruct (xm_wr m rd d v) as [m1 |] eqn:Hw; [| discriminate].
    apply xm_wr_facts in Hw as (Hle1 & Hd & Hw). apply IH in H as (Hle2 & _ & H2).
    split; [exact (dst_le_trans _ _ _ Hle1 Hle2) |]. split; [intros _; exact Hd |].
    intros Hr. destruct (Hw Hr) as [Hv Hk1]. destruct (H2 Hr) as [Hk2 Hc]. split; [congruence |].
    intros j Hj. destruct (Z.eq_dec j d) as [-> | Hne].
    + apply Hle2. rewrite Hv. discriminate.
    + apply Hc. lia.
Qed.

(* the bytes vs stored at i: the cells [i, i + |vs|) are written (for destination stores), litExtraBuffer is kept *)
Lemma xm_wrn_facts (vs: list Z) : forall (m: xmem) (r: xreg) (i: Z) (m': xmem),
  xm_wrn vs m r i = Some m' ->
  dst_le m m' /\ (vs <> nil -> 0 <= i) /\
  (r = R_dst -> xm_lxb m' = xm_lxb m /\
                forall j, i <= j < i + Zlength vs -> nth (Z.to_nat j) (xm_dst m') None <> None).
Proof.
  induction vs as [|v vs IH]; intros m r i m' H; cbn in H.
  - injection H as <-. split; [apply dst_le_refl |]. split; [congruence |]. intros _. split; [reflexivity |].
    rewrite Zlength_nil. lia.
  - destruct (xm_wr m r i v) as [m1 |] eqn:Hw; [| discriminate].
    apply xm_wr_facts in Hw as (Hle1 & Hd & Hw). apply IH in H as (Hle2 & _ & H2).
    split; [exact (dst_le_trans _ _ _ Hle1 Hle2) |]. split; [intros _; exact Hd |].
    intros Hr. destruct (Hw Hr) as [Hv Hk1]. destruct (H2 Hr) as [Hk2 Hc]. split; [congruence |].
    intros j Hj. rewrite Zlength_cons in Hj. destruct (Z.eq_dec j i) as [-> | Hne].
    + apply Hle2. rewrite Hv. discriminate.
    + apply Hc. lia.
Qed.

Lemma xm_move_facts (src: list Z) (k: nat) (m: xmem) (rd: xreg) (d: Z) (rs: xreg) (s: Z) (m': xmem) :
  xm_move src k m rd d rs s = Some m' -> dst_le m m' /\ (rd = R_dst -> xm_lxb m' = xm_lxb m).
Proof.
  unfold xm_move. destruct (xm_rdn src k m rs s) as [vs |]; [| discriminate].
  intros H. apply xm_wrn_facts in H as (Hle & _ & H). split; [exact Hle |]. intros Hr. apply (H Hr).
Qed.

(* the sequences' execution stores only into the destination: litExtraBuffer is kept by every copy, every
   sequence, the last literals, the whole section (with or without sequences) *)
Ltac dsome :=
  repeat match goal with
  | H: match ?e with _ => _ end = Some _ |- _ => destruct e eqn:?; try discriminate
  | H: Some _ = Some _ |- _ => injection H; clear H; intros; subst
  end.

Ltac keep_step :=
  match goal with
  | H: xm_fwd _ _ _ R_dst _ _ _ = Some _ |- _ =>
      apply xm_fwd_facts in H; destruct H as (_ & _ & H); destruct (H eq_refl) as [? _]; clear H
  | H: xm_move _ _ _ R_dst _ _ _ = Some _ |- _ =>
      apply xm_move_facts in H; destruct H as (_ & H); specialize (H eq_refl)
  end.

Lemma xm_chunks16_keep (src: list Z) (k: nat) : forall (m: xmem) (d: Z) (rs: xreg) (s: Z) (m': xmem),
  xm_chunks16 src k m d rs s = Some m' -> xm_lxb m' = xm_lxb m.
Proof.
  induction k as [|k IH]; intros m d rs s m' H; cbn in H; dsome; [reflexivity |].
  apply IH in H. keep_step. congruence.
Qed.

Lemma xm_wild_keep (src: list Z) (m: xmem) (d: Z) (rs: xreg) (s len: Z) (b: bool) (m': xmem) :
  xm_wild src m d rs s len b = Some m' -> xm_lxb m' = xm_lxb m.
Proof.
  unfold xm_wild. destruct (andb b (d - s <? 16)); intros H.
  - keep_step. assumption.
  - apply xm_chunks16_keep in H. exact H.
Qed.

Lemma xm_ov8_keep (src: list Z) (m: xmem) (op ip off: Z) (m': xmem) (op' ip': Z) :
  xm_ov8 src m op ip off = Some (m', op', ip') -> xm_lxb m' = xm_lxb m.
Proof. unfold xm_ov8. intros H; dsome; repeat keep_step; congruence. Qed.

Ltac keep_all :=
  repeat match goal with
  | H: xm_fwd _ _ _ R_dst _ _ _ = Some _ |- _ =>
      apply xm_fwd_facts in H; destruct H as (_ & _ & H); destruct (H eq_refl) as [? _]; clear H
  | H: xm_move _ _ _ R_dst _ _ _ = Some _ |- _ =>
      apply xm_move_facts in H; destruct H as (_ & H); specialize (H eq_refl)
  | H: xm_wild _ _ _ _ _ _ _ = Some _ |- _ => apply xm_wild_keep in H
  | H: xm_ov8 _ _ _ _ _ = Some _ |- _ => apply xm_ov8_keep in H
  end.

Lemma xm_safecopy_keep (src: list Z) (m: xmem) (op w: Z) (rs: xreg) (ip len: Z) (b: bool) (m': xmem) :
  xm_safecopy src m op w rs ip len b = Some m' -> xm_lxb m' = xm_lxb m.
Proof.
  unfold xm_safecopy. intros H. destruct (len <? 8); [keep_all; congruence |].
  destruct (if b then xm_ov8 src m op ip (op - ip) else Some (m, op, ip)) as [[[m1 op1] ip1] |] eqn:H1;
    [| discriminate].
  assert (Hk1: xm_lxb m1 = xm_lxb m) by (destruct b; [keep_all; congruence | congruence]). clear H1.
  destruct (w - (op + len) >=? 0); [keep_all; congruence |].
  destruct (w - op1 >=? 0); dsome; keep_all; congruence.
Qed.

Lemma xm_sdbs_keep (src: list Z) (m: xmem) (op ip len: Z) (m': xmem) :
  xm_sdbs src m op ip len = Some m' -> xm_lxb m' = xm_lxb m.
Proof.
  unfold xm_sdbs. intros H. destruct (orb (len <? 8) (op - ip >? -8)); [keep_all; congruence |].
  destruct (andb (len >=? 32) (op - ip <? -16)); dsome; keep_all; congruence.
Qed.

Lemma xm_prefix_keep (e: xenv) (m: xmem) (op mt ml off: Z) (wo: option Z) (m': xmem) :
  xm_prefix e m op mt ml off wo = Some m' -> xm_lxb m' = xm_lxb m.
Proof.
  unfold xm_prefix. intros H. destruct wo; [apply xm_safecopy_keep in H; exact H |].
  destruct (off >=? 16); [keep_all; congruence |]. dsome; keep_all; congruence.
Qed.

Lemma xm_match_keep (e: xenv) (m: xmem) (oLitEnd ml off: Z) (wo: option Z) (m': xmem) :
  xm_match e m oLitEnd ml off wo = Some m' -> xm_lxb m' = xm_lxb m.
Proof.
  unfold xm_match. intros H. dsome; keep_all; try congruence.
  apply xm_prefix_keep in H. congruence. apply xm_prefix_keep in H. congruence.
Qed.

Ltac keep_all2 :=
  repeat match goal with
  | H: xm_safecopy _ _ _ _ _ _ _ _ = Some _ |- _ => apply xm_safecopy_keep in H
  | H: xm_sdbs _ _ _ _ _ = Some _ |- _ => apply xm_sdbs_keep in H
  | H: xm_match _ _ _ _ _ _ = Some _ |- _ => apply xm_match_keep in H
  end; keep_all.

Lemma x_exec_keep (e: xenv) (m: xmem) (op: Z) (lr: xreg) (li llim ll ml off: Z) (m': xmem) (op' li': Z) :
  x_exec e m op lr li llim ll ml off = Some (m', op', li') -> xm_lxb m' = xm_lxb m.
Proof. unfold x_exec. intros H. dsome; keep_all2; congruence. Qed.

Lemma x_exec_split_keep (e: xenv) (m: xmem) (op li llim ll ml off: Z) (m': xmem) (op' li': Z) :
  x_exec_split e m op li llim ll ml off = Some (m', op', li') -> xm_lxb m' = xm_lxb m.
Proof. unfold x_exec_split. intros H. dsome; keep_all2; congruence. Qed.

Lemma x_step_keep (e: xenv) (s: xex) (ll ml off: Z) (s': xex) :
  x_step e s ll ml off = Some s' -> xm_lxb (xmm s') = xm_lxb (xmm s).
Proof.
  unfold x_step. intros H. dsome; cbn;
    repeat match goal with
    | H: x_exec _ _ _ _ _ _ _ _ _ = Some _ |- _ => apply x_exec_keep in H
    | H: x_exec_split _ _ _ _ _ _ _ _ = Some _ |- _ => apply x_exec_split_keep in H
    end; keep_all2; congruence.
Qed.

Lemma x_seq_loop_keep dseq coff (e: xenv) (tLL tOF tML: fse_table) (V: list Z) (k: nat) :
  forall st pos rep s s' pos' rep',
  x_seq_loop dseq coff e tLL tOF tML V k st pos rep s = Some (s', pos', rep') -> xm_lxb (xmm s') = xm_lxb (xmm s).
Proof.
  induction k as [|k IH]; intros st pos rep s s' pos' rep' H; cbn in H.
  - congruence.
  - destruct st as [[sLL sOF] sML]. dsome. apply IH in H. apply x_step_keep in Heqo0. congruence.
Qed.

Lemma x_last_keep (e: xenv) (s: xex) (m': xmem) (op': Z) :
  x_last e s = Some (m', op') -> xm_lxb m' = xm_lxb (xmm s).
Proof. unfold x_last. intros H. dsome; keep_all; congruence. Qed.

Lemma x_seq_section_keep (e: xenv) (os: option seq_tabs) (rep: Z * Z * Z) (bits: list Z) (nb: Z) (s0: xex)
    (mm: xmem) (op': Z) (rep2: Z * Z * Z) :
  x_seq_section e os rep bits nb s0 = Some (mm, op', rep2) -> xm_lxb mm = xm_lxb (xmm s0).
Proof.
  unfold x_seq_section, xb_seqs, x_seqs. intros H. dsome;
    repeat match goal with
    | H: x_last _ _ = Some _ |- _ => apply x_last_keep in H
    | H: x_seq_loop _ _ _ _ _ _ _ _ _ _ _ _ = Some _ |- _ => apply x_seq_loop_keep in H
    end; congruence.
Qed.

(* ZSTD_decodeLiteralsBlock's stores: they only add written cells; literals in dst are written with the 32 cells
   after their limit (raw / RLE: the zeroed slack; Huffman split: the decoded bytes above the moved part);
   literals read in place have 32 body bytes after them; the literal index is not negative; the literals lie
   in dst unsplit exactly when they are placed after the block's room (x_litloc = XL_in_dst), then at
   op0 + bsm + 32 *)
Lemma x_lits_store_facts (body lits: list Z) (lused: Z) (m: xmem) (op0 ews bsm cap: Z) (st: bool)
    (m': xmem) (lr: xreg) (li lim: Z) (sp: bool) :
  x_lits_store body lits lused m op0 ews bsm cap st = Some (m', lr, li, lim, sp) ->
  dst_le m m' /\
  (lr = R_dst -> forall j, li <= j < lim + XWILDCOPY -> nth (Z.to_nat j) (xm_dst m') None <> None) /\
  (lr = R_src -> lim + XWILDCOPY <= Zlength body /\ li = lused - Zlength lits /\ Z.land (byte_at body 0) 3 = 0) /\
  (lr <> R_src -> 0 <= op0 -> 0 <= bsm -> 0 <= li) /\
  (x_litloc body lused (Zlength lits) bsm cap st = XL_in_dst <-> lr = R_dst /\ sp = false) /\
  (x_litloc body lused (Zlength lits) bsm cap st = XL_in_dst -> li = op0 + bsm + XWILDCOPY).
Proof.
  unfold x_lits_store, x_litloc. intros H.
  pose proof (Zlength_nonneg lits) as Hn0.
  assert (Hty: 0 <= Z.land (byte_at body 0) 3) by (apply Z.land_nonneg; right; lia).
  assert (Hsp: x_alloc_loc cap (Zlength lits) bsm st = XL_split -> XLITEXTRA < Zlength lits).
  { unfold x_alloc_loc. destruct (negb st && (cap >? bsm + XWILDCOPY + Zlength lits + XWILDCOPY))%bool;
      [discriminate |]. destruct (Zlength lits <=? XLITEXTRA) eqn:E; [discriminate |]. intros _.
    apply Z.leb_gt in E. exact E. }
  destruct (x_alloc_loc cap (Zlength lits) bsm st) eqn:Hloc;
  destruct (Z.land (byte_at body 0) 3 <=? 1) eqn:Himm; cbv beta iota zeta in H; dsome;
  try (match goal with E: xl_is_split _ = _ |- _ => cbn in E; discriminate E end);
  repeat match goal with
  | E: (?a =? ?b) = _ |- context [?a =? ?b] => rewrite E
  | E: (?a <=? ?b) = _ |- context [?a <=? ?b] => rewrite E
  end; cbn [andb];
  repeat match goal with
  | E: (_ =? _) = true |- _ => apply Z.eqb_eq in E
  | E: (_ =? _) = false |- _ => apply Z.eqb_neq in E
  | E: (_ <=? _) = true |- _ => apply Z.leb_le in E
  | E: (_ <=? _) = false |- _ => apply Z.leb_gt in E
  end;
  try (exfalso; lia);
  repeat match goal with
  | E: xm_wrn _ _ _ _ = Some _ |- _ =>
      let a := fresh "Hle" in let b := fresh "Hnn" in
      apply xm_wrn_facts in E; destruct E as (a & b & E); try (specialize (E eq_refl); destruct E as [_ E])
  | E: xm_fwd _ _ _ _ _ _ _ = Some _ |- _ =>
      let a := fresh "Hle" in let b := fresh "Hnn" in
      apply xm_fwd_facts in E; destruct E as (a & b & E); try (specialize (E eq_refl); destruct E as [_ E])
  | E: xm_move _ _ _ _ _ _ _ = Some _ |- _ =>
      let a := fresh "Hle" in apply xm_move_facts in E; destruct E as (a & _)
  end;
  rewrite ?Zlength_repeat' in *; unfold x_split_L0 in *; unfold XWILDCOPY, XLITEXTRA in *;
  refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
  all: try (intros E; first [discriminate E | reflexivity | lia]).
  all: try (split; [intros E; first [discriminate E | split; reflexivity]
                   | intros [E1 E2]; first [reflexivity | discriminate E1 | discriminate E2]]).
  all: try (intros Hr; try discriminate Hr; repeat split; lia).
  all: try (eauto using dst_le_trans, dst_le_refl; fail).
  all: try (intros Hr ? ?; try (exfalso; apply Hr; reflexivity);
            match goal with
            | Hnn: ?P -> 0 <= ?x |- 0 <= _ =>
                assert (0 <= x) by (apply Hnn; first
                  [ lia
                  | intros E; apply (f_equal (@Zlength Z)) in E; rewrite ?Zlength_repeat', Zlength_nil in E;
                    specialize (Hsp eq_refl); lia ]); lia
            | |- _ => lia
            end).
  all: try (intros Hr j Hj; try discriminate Hr;
    repeat match goal with
    | Hl: dst_le ?a ?b, Hc: forall k, _ <= k < _ -> nth (Z.to_nat k) (xm_dst ?a) None <> None |- _ =>
        let H' := fresh "Hc" in pose proof (fun k Hk => Hl _ (Hc k Hk)) as H'; cbv beta in H'; clear Hc
    end;
    first
    [ match goal with Hc: forall k, _ <= k < _ -> nth (Z.to_nat k) (xm_dst _) None <> None |- _ => apply Hc; lia end
    | match goal with
      | H1: forall k, _ <= k < ?h1 -> nth (Z.to_nat k) (xm_dst _) None <> None,
        H2: forall k, _ <= k < _ -> nth (Z.to_nat k) (xm_dst _) None <> None |- _ =>
          destruct (Z_lt_le_dec j h1); [apply H1 | apply H2]; lia
      end ]).
Qed.

(* raw literals (block type 0) of a byte string: the section takes at least the literals' bytes (so literals
   read in place start at a non-negative index of the body) *)
Lemma le_value_nonneg (l: list Z) : bytes_ok l -> 0 <= le_value l.
Proof.
  induction l as [|b l IH]; intros H; cbn; [lia |]. inversion H as [|? ? Hb Hl]; subst.
  specialize (IH Hl). unfold is_byte in Hb. lia.
Qed.

Lemma x_lits_raw_len {X: Type} (huf: option X -> Z -> bool -> list Z -> Z -> option (list Z * X))
    (hx: option X) (b: list Z) (bsm wmax: Z) (st: bool) (lits: list Z) (lused: Z) (hx': option X) :
  bytes_ok b -> x_lits X huf hx b bsm wmax st = Some (lits, lused, hx') -> Z.land (byte_at b 0) 3 = 0 ->
  Zlength lits <= lused.
Proof.
  intros Hb H Hty. unfold x_lits in H. rewrite Hty in H. cbn [Z.eqb] in H.
  assert (Hb0: 0 <= byte_at b 0).
  { unfold byte_at. destruct b as [|y b]; cbn; [lia |]. inversion Hb as [|? ? Hy]; subst. unfold is_byte in Hy. lia. }
  assert (Hf: forall i k, 0 <= le_field b i k).
  { intros i k. apply le_value_nonneg. unfold slice. apply Forall_firstn. apply Forall_skipn. exact Hb. }
  destruct (Zlength b <? 2); [discriminate |].
  destruct ((Z.land (Z.shiftr (byte_at b 0) 2) 3 =? 3) && (Zlength b <? 3))%bool; [discriminate |].
  match type of H with context [let '(lh, litSize) := ?p in _] => destruct p as [lh ls] eqn:Hp end.
  assert (Hls: 1 <= lh /\ 0 <= ls).
  { destruct (Z.land (Z.shiftr (byte_at b 0) 2) 3 =? 1); [| destruct (Z.land (Z.shiftr (byte_at b 0) 2) 3 =? 3)];
      injection Hp as <- <-; split; try lia; apply Z.shiftr_nonneg; auto. }
  destruct (ls >? bsm); [discriminate |]. destruct (wmax <? ls); [discriminate |].
  destruct (lh + ls >? Zlength b); [discriminate |]. injection H as <- <- _.
  unfold slice. rewrite Zlength_correct, firstn_length. lia.
Qed.

(* the written cells of a region related to the output array at rb (dst_rel) are the array's bytes there *)
Lemma x_written_nth (d: list (option Z)) (j: nat) :
  (j < length (x_written d))%nat -> nth j d None = Some (nth j (x_written d) 0).
Proof.
  revert j; induction d as [|[v |] d IH]; intros j Hj; cbn in *; try lia.
  destruct j; [reflexivity |]. apply IH. lia.
Qed.

Lemma dst_rel_written (oc: list val) (rb: Z) (d: list (option Z)) :
  dst_rel oc rb d -> 0 <= rb -> sublist rb (rb + Zlength (x_written d)) oc = zbytes (x_written d).
Proof.
  intros Hr Hrb. set (w := x_written d).
  assert (Hw: forall j, 0 <= j < Zlength w -> Znth (rb + j) oc = Vint (Int.repr (Znth j w))).
  { intros j Hj. apply Hr; [lia |]. rewrite Zlength_correct in Hj. unfold Znth, w in *.
    rewrite (x_written_nth d (Z.to_nat j)) by lia. destruct (Z_lt_dec j 0); [lia | reflexivity]. }
  destruct (Z_le_gt_dec (Zlength w) 0) as [H0 | H0].
  { destruct w as [| v w']; [| rewrite Zlength_cons in H0; pose proof (Zlength_nonneg w'); lia].
    rewrite Zlength_nil, Z.add_0_r, sublist_nil. reflexivity. }
  assert (Hlen: rb + Zlength w <= Zlength oc).
  { specialize (Hw (Zlength w - 1) ltac:(lia)).
    destruct (Z_lt_le_dec (rb + (Zlength w - 1)) (Zlength oc)); [lia |].
    rewrite Znth_outofbounds in Hw by lia. discriminate. }
  apply Znth_eq_ext.
  - rewrite Zlength_sublist, Zlength_map by (pose proof (Zlength_nonneg w); lia). lia.
  - intros j Hj. rewrite Zlength_sublist in Hj by (pose proof (Zlength_nonneg w); lia).
    rewrite Znth_sublist by lia. rewrite Znth_map by lia. rewrite Z.add_comm. apply Hw. lia.
Qed.

(* x_block's sequences part is the section the sequence decoders' clause states (BlkIface.x_seq_section) *)
Lemma x_block_res_eq (e: xenv) (tabs: option seq_tabs) (rep: Z * Z * Z) (bits: list Z) (nb: Z) (s0: xex) :
  (if nb =? 0 then match x_last e s0 with Some (m, op') => Some (m, op', rep) | None => None end
   else match tabs with Some t => x_seqs dseq_one c_offset e t rep bits nb s0 | None => None end)
  = x_seq_section e tabs rep bits nb s0.
Proof. reflexivity. Qed.

(* the sequences section (any of the three decoders), on the output array oc1 the literals section left (o1) and
   the input after the literals and the header (i3): the block's result is the decoder's, and on success the new
   state is the literals' Huffman table (oh', of type x2'), the header's tables os', the decoder's repeat offsets
   and litExtraBuffer as the literals section left it *)
Lemma bx_seqs (ts: tstate) (o: outarr) (i: inwin) (h: hctx) (bsm streaming r1: Z) (oc1: list val)
    (l: litloc) (lits: list Z) (oh': option huf_table) (x2': bool) (lxb': list Z)
    (nb: Z) (os': option seq_tabs) (used: Z) (o1: outarr) (i3: inwin) (r3: Z) (oc': list val)
    (rep': Z * Z * Z) :
  outarr_ok o -> inwin_ok i ->
  Zlength (iw_s i) <= bsm ->
  lits_exact (option_map (xhuf_of (ts_x2 ts)) (st_huf ts)) (ts_lxb ts) o i bsm streaming r1 oc1 l lits
    (option_map (xhuf_of x2') oh') lxb' ->
  is_error_code r1 = false ->
  xb_seq_header (st_seq ts) (skipn (Z.to_nat r1) (iw_s i)) = Some (nb, os', used) ->
  (oa_cap o = 0 -> nb = 0) ->
  oa_N o1 = oa_N o -> oa_c o1 = oc1 -> oa_d o1 = oa_d o -> oa_cap o1 = oa_cap o ->
  iw_N i3 = iw_N i -> iw_c i3 = iw_c i -> iw_s i3 = skipn (Z.to_nat used) (skipn (Z.to_nat r1) (iw_s i)) ->
  seqs_exact os' (st_rep ts) l lits lxb' nb o1 i3 h r3 oc' rep' ->
  block_exact ts o i h bsm streaming r3 oc'
    (if is_error_code r3 then None
     else Some (mk_tstate {| st_huf := oh'; st_seq := os'; st_rep := rep' |} x2' lxb')).
Proof.
  intros Ho Hi Hs HL Herr1 Hh Hcap HoN Hoc Hod Hocap HiN Hic His HS rb mem ps ds de Hrb HN Hsub Hreg Hps Hds Hin.
  specialize (HL rb mem Hrb HN Hsub). cbv zeta in HL. unfold xb_lits in HL.
  unfold x_block. rewrite Z.gtb_ltb, (proj2 (Z.ltb_ge _ _) Hs). cbn [ts_x x_huf x_seq x_rep x_lxb].
  destruct (x_lits _ _ _ _ _ _ _) as [[[lits0 lused] hx0]|] eqn:Hx; [| congruence].
  destruct (x_lits_store _ _ _ _ _ _ _ _ _) as [[[[[m lr] li] lim] sp]|] eqn:Hst; [| congruence].
  destruct HL as (_ & -> & -> & Hhx & Hlxb & Hdr & Hll).
  unfold xb_seq_header in Hh. rewrite Hh.
  destruct (andb (nb >? 0) (oa_cap o =? 0)) eqn:Hc0.
  { apply andb_true_iff in Hc0 as [Hc1 Hc2]. apply Z.gtb_lt in Hc1. apply Z.eqb_eq in Hc2.
    specialize (Hcap Hc2). lia. }
  apply x_lits_store_facts in Hst as Hf. destruct Hf as (Hle & Hcov & Hsrc & Hnn & Hiff & Hindst).
  destruct Hi as (_ & Hoff & Hoffn & _ & _ & _ & Hbytes & Hwin).
  pose proof (Zlength_nonneg (iw_s i)) as Hb0.
  (* the sequences' output end is x_block's *)
  assert (He: match x_litloc (iw_s i) lused (Zlength lits0) bsm (oa_cap o) (streaming =? 1) with
              | XL_in_dst => oa_d o - rb + bsm + XWILDCOPY | _ => oa_d o - rb + oa_cap o end = seq_oend l rb o1).
  { unfold seq_oend. rewrite Hod, Hocap.
    destruct (x_litloc (iw_s i) lused (Zlength lits0) bsm (oa_cap o) (streaming =? 1)) eqn:Hloc.
    - destruct (proj1 Hiff eq_refl) as [-> ->]. specialize (Hindst eq_refl).
      destruct l; cbn in Hll; destruct Hll as (? & ? & ? & ?); try discriminate. lia.
    - destruct l; cbn in Hll; destruct Hll as (? & ? & ? & ?); subst; try lia.
      discriminate (proj2 Hiff (conj eq_refl eq_refl)).
    - destruct l; cbn in Hll; destruct Hll as (? & ? & ? & ?); subst; try lia.
      discriminate (proj2 Hiff (conj eq_refl eq_refl)).
    - destruct l; cbn in Hll; destruct Hll as (? & ? & ? & ?); subst; try lia.
      discriminate (proj2 Hiff (conj eq_refl eq_refl)). }
  specialize (HS rb (xm_dst m) (iw_s i) (iw_off i) lr li lim sp ps ds de Hreg ltac:(rewrite Hod; lia)
    ltac:(rewrite Hoc; exact Hdr)).
  spec HS.
  { intros j Hj. rewrite Hod in Hj. specialize (Hin j Hj). apply Hle. cbn [xm_dst].
    rewrite (nth_indep _ None (Some 0)) by (rewrite map_length, <- ZtoNat_Zlength; lia).
    rewrite map_nth. discriminate. }
  specialize (HS Hoff ltac:(rewrite HiN; lia) ltac:(rewrite Hic; exact Hwin) Hll Hps Hds).
  spec HS.
  { destruct lr.
    - apply Hnn; [discriminate | lia | lia].
    - apply Hnn; [discriminate | lia | lia].
    - destruct (Hsrc eq_refl) as (_ & -> & Hty). pose proof (x_lits_raw_len _ _ _ _ _ _ _ _ _ Hbytes Hx Hty). lia. }
  specialize (HS Hcov ltac:(intros Hr; apply Hsrc, Hr)).
  cbv zeta in HS. rewrite Hod, His, <- He in HS. rewrite Hlxb in HS.
  rewrite x_block_res_eq.
  replace {| xm_dst := xm_dst m; xm_lxb := xm_lxb m |} with m in HS by (destruct m; reflexivity).
  revert HS.
  destruct (x_seq_section _ _ _ _ _ _) as [[[mm op'] rep2] |] eqn:Hres; [| tauto].
  intros (Herr & Hr3 & Hdr' & ->). split; [exact Hr3 |]. split; [apply dst_rel_written; [exact Hdr' | lia] |].
  rewrite Herr. eexists. split; [reflexivity |]. unfold ts_x. cbn [st_huf st_seq st_rep ts_d ts_x2 ts_lxb].
  apply x_seq_section_keep in Hres. cbn [xmm] in Hres. rewrite Hres, <- Hhx, Hlxb. reflexivity.
Qed.
