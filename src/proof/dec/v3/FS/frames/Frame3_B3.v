(* FS3 one-shot frames: the loop body's statements 9..16 (error check, checksum update, advance, last block) (port of v2 body_frame.v's fr_B3_ok). *)
Require Import Zstd.proof.dec.v3.FS.frames.Frames3Defs Zstd.proof.dec.v3.FS.frames.Frames3Model.
Require Import Zstd.proof.dec.v3.FS.frames.Frame3_codes.
Require Import Zstd.proof.model.ExHuf Zstd.proof.model.ExBlock Zstd.proof.model.ExFrame Zstd.proof.model.ExFrameFacts.
Require Import Zstd.proof.model.Exact Zstd.proof.model.ExBlockBytes.

Local Open Scope Z_scope.

Local Open Scope logic.

Section CM_Frame3_B3_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.



Lemma b3_forall_firstn: forall {A} (P: A -> Prop) n l, Forall P l -> Forall P (firstn n l).
Proof. induction n; intros; destruct l; simpl; auto. inversion H; subst; constructor; auto. Qed.

Lemma b3_forall_skipn: forall {A} (P: A -> Prop) n l, Forall P l -> Forall P (skipn n l).
Proof. induction n; intros; destruct l; simpl; auto. inversion H; subst; auto. Qed.

Lemma b3_le_value_nonneg: forall l, Forall is_byte l -> 0 <= le_value l.
Proof.
  induction l; intros; simpl; [lia | ]. inversion H; subst. unfold is_byte in *.
  specialize (IHl H3). lia.
Qed.

Lemma b3_le3_nonneg: forall t, bytes_ok t -> 0 <= le_field t 0 3.
Proof.
  intros. unfold le_field, slice. apply b3_le_value_nonneg, b3_forall_firstn, b3_forall_skipn. exact H.
Qed.

Lemma b3_cbs_nonneg: forall t c, bytes_ok t -> cblock_size t = Some c -> 0 <= c.
Proof.
  intros t c Ht Hc. unfold cblock_size in Hc.
  destruct (Zlength t <? ZSTD_blockHeaderSize); [discriminate | ].
  destruct (bp_type (block_props_of t) =? 1); [inversion Hc; lia | ].
  destruct (bp_type (block_props_of t) =? 3); [discriminate | ].
  inversion Hc; subst. unfold block_props_of; cbn [bp_origSize].
  apply Z.shiftr_nonneg. apply b3_le3_nonneg; auto.
Qed.

Lemma b3_last_range: forall t, bytes_ok t -> 0 <= bp_last (block_props_of t) <= 1.
Proof.
  intros. unfold block_props_of; cbn [bp_last]. pose proof (b3_le3_nonneg t H).
  pose proof (Z.land_ones (le_field t 0 3) 1 ltac:(lia)) as E.
  change (Z.ones 1) with 1 in E. change (2 ^ 1) with 2 in E. rewrite E.
  pose proof (Z.mod_pos_bound (le_field t 0 3) 2 ltac:(lia)). lia.
Qed.

Lemma b3_uo_trans: forall (oc oc1 oc2: list val) lo lo' hi,
  unchanged_outside oc oc1 lo hi -> unchanged_outside oc1 oc2 lo' hi -> lo <= lo' ->
  Zlength oc1 = Zlength oc -> unchanged_outside oc oc2 lo hi.
Proof.
  unfold unchanged_outside. intros. rewrite H0 by lia. apply H; auto.
Qed.

Lemma b3_uo_prefix: forall (oc1 oc2: list val) lo hi a b,
  unchanged_outside oc1 oc2 lo hi -> 0 <= a <= b -> b <= lo -> b <= Zlength oc1 ->
  Zlength oc2 = Zlength oc1 -> sublist a b oc2 = sublist a b oc1.
Proof.
  intros. apply Znth_eq_ext; [rewrite !Zlength_sublist by lia; lia | ].
  intros i Hi. rewrite Zlength_sublist in Hi by lia. rewrite !Znth_sublist by lia.
  apply H; lia.
Qed.

Lemma b3_split3: forall sh n i k (l: list val) p,
  0 <= i -> 0 <= k -> i + k <= n -> Zlength l = n ->
  field_compatible (tarray tuchar n) [] p ->
  data_at sh (tarray tuchar n) l p =
  (data_at sh (tarray tuchar i) (sublist 0 i l) p *
   data_at sh (tarray tuchar k) (sublist i (i + k) l) (offset_val i p) *
   data_at sh (tarray tuchar (n - (i + k))) (sublist (i + k) n l) (offset_val (i + k) p))%logic.
Proof.
  intros. rewrite (split3_data_at_Tarray_tuchar sh n i (i + k)) by lia.
  change (Tarray tuchar n noattr) with (tarray tuchar n). rewrite !arr_field_address0 by (auto; lia).
  replace (i + k - i) with k by lia. simpl sizeof. rewrite !Z.mul_1_l. reflexivity.
Qed.

Lemma b3_wvp_off: forall sh n c p i, readable_share sh -> 0 <= i <= n -> 0 < n ->
  data_at sh (tarray tuchar n) c p |-- weak_valid_pointer (offset_val i p).
Proof.
  intros. sep_apply (data_at_data_at_ sh (tarray tuchar n) c p).
  rewrite data_at__memory_block. Intros. simpl sizeof.
  apply memory_block_weak_valid_pointer; try lia. apply readable_nonidentity; auto.
Qed.

Lemma b3_zero_at: forall sh n c base a, isptr base ->
  data_at sh (tarray tuchar n) c base |--
  (data_at sh (tarray tuchar n) c base * data_at sh (tarray tuchar 0) (xxh_bytes []) (offset_val a base))%logic.
Proof.
  intros. rewrite <- (sepcon_emp (data_at sh (tarray tuchar n) c base)) at 1.
  apply sepcon_derives; [apply derives_refl | ]. apply data_at_zero_array; auto.
Qed.

Section B3.
Context (dm: dict_model) (h: frame_header) (s: list Z) (hs j: Z) (out: list Z) (st: dstate) (c r: Z)
  (st2: dstate) (cnt: list Z) (ocap: Z).
Hypotheses (HOT: fr_OT dm h s hs j out st) (Hhs0: 0 <= hs) (Hj: 0 <= j) (Hhj: hs + j <= Zlength s)
  (Hcb: cblock_size (fr_t s hs j) = Some c) (Hc0: 0 <= c) (Hct: c <= Zlength (fr_t s hs j) - ZSTD_blockHeaderSize)
  (Hlink: forall st' out',
     blk_res st (dm_content dm) out (fr_t s hs j) c (fh_blockSizeMax h) (fh_windowSize h) = Some (st', out') ->
     (is_error_code r = false -> out' = out ++ cnt /\ st2 = st') /\
     (is_error_code r = true -> ocap < Zlength out'))
  (Hlink2: fr_RL dm h s hs j out st c r cnt st2).

(* a successful block's content and state are zstd's (Refuse.rblock): compressed blocks by Hlink, raw and RLE
   blocks by Hlink2 *)
Lemma b3_rlink: is_error_code r = false -> forall st' out',
  rblock false st (dm_content dm) (fr_t s hs j) out c (fh_blockSizeMax h) (fh_windowSize h) = Some (st', out') ->
  out' = out ++ cnt /\ st' = st2.
Proof.
  intros Hr st' out' Hb.
  destruct (Z.eq_dec (bp_type (block_props_of (fr_t s hs j))) 2) as [E|E].
  - rewrite rblock_cmp in Hb by exact E. destruct (Hlink _ _ Hb) as [X _]. destruct (X Hr) as [-> ->]. auto.
  - destruct (Hlink2 Hr E _ _ Hb) as [-> ->]. auto.
Qed.

Lemma b3_err_model: forall md sel, fr_hdr3 md sel dm s hs h -> is_error_code r = true ->
  forall c' sz, decode_frame_m md dm no_wlim s = FOk c' sz -> ocap < Zlength c'.
Proof.
  intros md sel Hh Hr c' sz Hd. destruct (fr_frame_ok3_any _ _ _ _ _ _ _ _ Hh Hd) as (k & Hk & _).
  remember (blk_res st (dm_content dm) out (fr_t s hs j) c (fh_blockSizeMax h) (fh_windowSize h)) as B eqn:E.
  symmetry in E. destruct B as [[st' out'] | ].
  - destruct (Hlink _ _ eq_refl) as [_ X]. specialize (X Hr).
    pose proof (fr_OT_grow dm h s hs j out st c st' out' HOT Hj Hhj Hcb Hc0 Hct E c' k Hk). lia.
  - exfalso. eapply (fr_OT_none dm h s hs j out st HOT Hj Hhj); [ | exact Hk].
    right; right. exists c; auto.
Qed.

Lemma b3_next: is_error_code r = false -> bp_last (block_props_of (fr_t s hs j)) <> 1 ->
  fr_OT dm h s hs (j + ZSTD_blockHeaderSize + c) (out ++ cnt) st2.
Proof.
  intros Hr Hl.
  assert (Hrb: forall st'' out'', rblock false st (dm_content dm) (fr_t s hs j) out c (fh_blockSizeMax h)
                 (fh_windowSize h) = Some (st'', out'') -> out'' = out ++ cnt /\ st'' = st2)
    by (intros st'' out'' Hb; exact (b3_rlink Hr _ _ Hb)).
  remember (blk_res st (dm_content dm) out (fr_t s hs j) c (fh_blockSizeMax h) (fh_windowSize h)) as B eqn:E.
  symmetry in E. destruct B as [[st' out'] | ].
  - destruct (Hlink _ _ eq_refl) as [X _]. destruct (X Hr) as [-> ->].
    first [exact (fr_OT_next dm h s hs j out st c st' (out ++ cnt) HOT Hj Hhj Hcb Hc0 Hct E Hl Hrb)
          | exact (fr_OT_next dm h s hs j out st c st' (out ++ cnt) HOT Hhs0 Hj Hhj Hcb Hc0 Hct E Hl Hrb)].
  - assert (Ht: fr_t s hs (j + ZSTD_blockHeaderSize + c) =
                skipn (Z.to_nat (ZSTD_blockHeaderSize + c)) (fr_t s hs j)).
    { unfold fr_t. rewrite !frm_sub_end, skipn_skipn. f_equal. unfold ZSTD_blockHeaderSize. lia. }
    refine (conj _ (conj _ (conj _ _)));
      [ | | | exact (fr_RF_next dm h s hs j out st c st2 (out ++ cnt) (proj2 (proj2 (proj2 HOT))) Hhs0 Hj Hcb Hc0 Hct Hl Hrb)].
    + intros o k Hk. exfalso. eapply (fr_OT_none dm h s hs j out st HOT Hj Hhj); [ | exact Hk].
      right; right. exists c; auto.
    + destruct HOT as [_ [HBS _]]. intros f kk nb Hb.
      rewrite Ht in Hb.
      destruct (HBS (S f) (ZSTD_blockHeaderSize + c + kk) (nb + 1)) as (f' & nb' & Hr2).
      * cbn [blocks_size]. rewrite Hcb.
        replace (ZSTD_blockHeaderSize + c >? Zlength (fr_t s hs j)) with false
          by (rewrite Z.gtb_ltb; symmetry; apply Z.ltb_ge; unfold ZSTD_blockHeaderSize in *; lia).
        destruct (Z.eqb_spec (bp_last (block_props_of (fr_t s hs j))) 1); [contradiction|].
        rewrite Hb. reflexivity.
      * exists f', nb'. rewrite Hr2. f_equal. f_equal. lia.
    + destruct HOT as [_ [_ [HRR _]]]. intros Hr0. specialize (HRR Hr0). rewrite Ht.
      inversion HRR as [t0 c0 _ _ Hl1 | t0 c0 Hc1 _ _ Hn].
      * contradiction.
      * rewrite Hcb in Hc1. injection Hc1 as <-. exact Hn.
Qed.

(* after a successful last block: a refused frame's end is refused *)
Lemma b3_last_re: is_error_code r = false -> bp_last (block_props_of (fr_t s hs j)) = 1 ->
  fr_RE dm h s hs (j + ZSTD_blockHeaderSize + c) (out ++ cnt).
Proof.
  intros Hr Hl. apply (fr_RF_last dm h s hs j out st c st2 (out ++ cnt) (proj2 (proj2 (proj2 HOT))) Hhs0 Hj Hcb Hc0 Hct Hl).
  intros st'' out'' Hb. exact (b3_rlink Hr _ _ Hb).
Qed.

Lemma b3_last_bs: bp_last (block_props_of (fr_t s hs j)) = 1 ->
  exists f nb, blocks_size f (fr_rest s hs) = Some (j + ZSTD_blockHeaderSize + c, nb).
Proof. intros Hl. exact (fr_OT_last_bs dm h s hs j out st c HOT Hcb Hct Hl). Qed.

Lemma b3_last: is_error_code r = false -> bp_last (block_props_of (fr_t s hs j)) = 1 ->
  forall o k, fr_DB dm h s hs = Some (o, k) -> o = out ++ cnt /\ k = j + ZSTD_blockHeaderSize + c.
Proof.
  intros Hr Hl o k Hk.
  remember (blk_res st (dm_content dm) out (fr_t s hs j) c (fh_blockSizeMax h) (fh_windowSize h)) as B eqn:E.
  symmetry in E. destruct B as [[st' out'] | ].
  - destruct (Hlink _ _ eq_refl) as [X _]. destruct (X Hr) as [-> ->].
    exact (fr_OT_last dm h s hs j out st c st' (out ++ cnt) HOT Hj Hhj Hcb Hc0 Hct E Hl o k Hk).
  - exfalso. eapply (fr_OT_none dm h s hs j out st HOT Hj Hhj); [ | exact Hk].
    right; right. exists c; auto.
Qed.

End B3.

(* ---------- the exact model along the loop (ExFrameFacts) ---------- *)

(* a block that is not the last one: the model's blocks from the next block on, shifted, are the frame's *)
Lemma b3_xinv_next: forall ox dm e ocap s pr h hs ts0 j out st r st2 cnt c,
  0 <= hs -> 0 <= j -> hs + j <= Zlength s -> bytes_ok s ->
  cblock_size (fr_t s hs j) = Some c -> bp_last (block_props_of (fr_t s hs j)) <> 1 -> is_error_code r = false ->
  fr_xinv ox dm e ocap s pr h hs ts0 j out st -> fr_xdec ox dm e ocap s pr h hs j out st r st2 cnt ->
  fr_xinv ox dm e ocap s pr h hs ts0 (j + ZSTD_blockHeaderSize + c) (out ++ cnt) st2.
Proof.
  intros ox dm e ocap s pr h hs ts0 j out st r st2 cnt c Hhs Hj Hhj Hs Hcb Hl Hr Hxi Hxd Hon.
  destruct (Hxi Hon) as [Hg Heq]. specialize (Hxd Hon).
  assert (Hbt: bytes_ok (fr_t s hs j)) by (unfold fr_t; apply Forall_sublist; auto).
  destruct (xb_one xstate xblock (ts_x st) (fr_t s hs j) out ocap (fh_blockSizeMax h))
    as [[[[st' cn] n] lst]|] eqn:E; [|congruence].
  destruct Hxd as (_ & <- & Hst2).
  destruct (xb_one_bounds xstate xblock _ _ _ _ _ _ _ _ _ Hbt E) as [Hn (c' & Hc' & -> & Hlst)].
  rewrite Hcb in Hc'. injection Hc' as <-.
  subst lst. rewrite (proj2 (Z.eqb_neq _ _) Hl) in E.
  split; [rewrite Hst2; exact (xb_one_good _ _ _ _ _ _ _ _ _ Hbt Hg E)|].
  rewrite Heq, (xbs_next xstate xblock _ _ _ _ _ _ _ _ Hbt E), xb_shift_shift, Hst2.
  assert (Ht: fr_t s hs (j + ZSTD_blockHeaderSize + c) = skipn (Z.to_nat (ZSTD_blockHeaderSize + c)) (fr_t s hs j)).
  { unfold fr_t. rewrite !frm_sub_end, skipn_skipn. f_equal. unfold ZSTD_blockHeaderSize in *. lia. }
  rewrite Ht. replace (j + (ZSTD_blockHeaderSize + c)) with (j + ZSTD_blockHeaderSize + c) by lia. reflexivity.
Qed.

(* the last block: the model's blocks of the frame end after it, with the output and the tables' state after it *)
Lemma b3_xaft: forall ox dm e ocap s pr h hs ts0 j out st r st2 cnt c,
  0 <= hs -> 0 <= j -> hs + j <= Zlength s -> bytes_ok s ->
  cblock_size (fr_t s hs j) = Some c -> bp_last (block_props_of (fr_t s hs j)) = 1 -> is_error_code r = false ->
  fr_xinv ox dm e ocap s pr h hs ts0 j out st -> fr_xdec ox dm e ocap s pr h hs j out st r st2 cnt ->
  fr_xaft ox dm e ocap s pr h hs ts0 (j + ZSTD_blockHeaderSize + c) (out ++ cnt) st2.
Proof.
  intros ox dm e ocap s pr h hs ts0 j out st r st2 cnt c Hhs Hj Hhj Hs Hcb Hl Hr Hxi Hxd Hon.
  destruct (Hxi Hon) as [_ Heq]. specialize (Hxd Hon).
  assert (Hbt: bytes_ok (fr_t s hs j)) by (unfold fr_t; apply Forall_sublist; auto).
  destruct (xb_one xstate xblock (ts_x st) (fr_t s hs j) out ocap (fh_blockSizeMax h))
    as [[[[st' cn] n] lst]|] eqn:E; [|congruence].
  destruct Hxd as (_ & <- & Hst2).
  destruct (xb_one_bounds xstate xblock _ _ _ _ _ _ _ _ _ Hbt E) as [Hn (c' & Hc' & -> & Hlst)].
  rewrite Hcb in Hc'. injection Hc' as <-.
  rewrite Hl in Hlst. cbn in Hlst. subst lst.
  rewrite Heq, (xbs_last xstate xblock _ _ _ _ _ _ _ _ E), Hst2. cbn [xb_shift].
  replace (j + (ZSTD_blockHeaderSize + c)) with (j + ZSTD_blockHeaderSize + c) by lia. reflexivity.
Qed.

Ltac b3_drop_op L :=
  lazymatch L with
  | temp _op _ :: ?t => constr:(t)
  | ?x :: ?t => let t' := b3_drop_op t in constr:(x :: t')
  end.

Section Seg.
Context (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR: blrel)
  (W: list ptr_witness) (gv: globals) (p: val) (fs: fstate) (ox: option ddx) (dm: dict_model) (e: ext_seg)
  (osh: share) (obase: val) (oN: Z) (oc: list val) (od ocap: Z)
  (ish: share) (ibase: val) (iN: Z) (ic: list val) (ioff: Z) (s: list Z) (sp ssp: val) (v_bp: val)
  (pr: dparams) (dsp: val) (d: dfields) (l: list (val * ddict_st)) (tbl: list val) (xq: option (val * val)) (lent: bool)
  (am: option cmem) (hb: Z) (h: frame_header) (hs: Z) (fdid: Z) (d1: dfields) (ts0: tstate).

(* a failed block: the model's step fails too, so do the model's blocks of the frame and the exact frame *)
Lemma b3_exact_err: forall j out st r st2 cnt oc' lxb',
  fr_ctx W fs ox dm e osh obase oN oc od ocap ish ibase iN ic ioff s pr dsp d l tbl lent h hs d1 ->
  fr_xinv ox dm e ocap s pr h hs ts0 j out st -> fr_xdec ox dm e ocap s pr h hs j out st r st2 cnt ->
  is_error_code r = true ->
  ox = None -> dm = no_dict -> pr = dparams_dflt -> e = ExtNone -> frame_exact ts0 s ocap r oc' od 0 lxb'.
Proof.
  intros j out st r st2 cnt oc' lxb' HC Hxi Hxd Hr Hox Hdm Hpr He.
  assert (Hon: fx_on ox dm e pr) by (repeat split; assumption).
  unfold frame_exact.
  rewrite (fr_x_frame DENT TABS SR BR W gv p fs ox dm e osh obase oN oc od ocap ish ibase iN ic ioff s sp ssp v_bp
             pr dsp d l tbl xq lent am hb h hs fdid d1 ts0 HC Hon).
  rewrite (proj2 (Hxi Hon)). specialize (Hxd Hon).
  destruct (xb_one xstate xblock (ts_x st) (fr_t s hs j) out ocap (fh_blockSizeMax h))
    as [[[[st' cn] n] lst]|] eqn:E; [destruct Hxd as [Hf _]; congruence|].
  rewrite (xbs_err xstate xblock _ _ _ _ _ E). exact Hr.
Qed.

Lemma fr_B3_ok3: DENT_OK DENT -> TABS_OK TABS ->
  fr_B3_stmt DENT TABS SR BR W gv p fs ox dm e osh obase oN oc od ocap ish ibase iN ic ioff s sp ssp v_bp pr dsp d l tbl xq lent am hb h hs fdid d1 ts0.
Proof.
  intros HD HT Espec j out oc1 st cold c r oc2 st2 cold2 cnt HC.
  cbv [Frames3Defs.seq_drop Frames3Defs.fr_lb Frames3Defs.fr_loop Frames3Defs.seq_nth Frames3Defs.fr_body f_ZSTD_decompressFrame fn_body].
  unfold S_dec, fr_SEP, fr_LOC, fr_outP. cbn [app].
  pose proof HC as HC0.
  destruct HC0 as [Hosh HoN HoN32 Hod Hocap Hodcap Hwin Hext Hifd Hcold HW Hlay Hhp Hhb Hed He0 Hob Hib
                   Hpar Hhdr Hd1 Hlent].
  Intros.
  match goal with Hx: fr_RL _ _ _ _ _ _ _ _ _ _ _ |- _ => rename Hx into Hrl end.
  match goal with Hx: fr_xinv _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rename Hx into Hxinv end.
  match goal with Hx: fr_xdec _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rename Hx into Hxdec end.
  pose proof Hhdr as (Hs & Hlen9 & Hhs & Hlenh & Hgfh).
  assert (Hhs0: 0 <= hs).
  { rewrite Hhs. pose proof (hs3_range (md_magicless (dmode_of pr)) s Hs) as X.
    unfold mg_sh in *. destruct (md_magicless (dmode_of pr)); unfold starting_len, ZSTD_FRAMEHEADERSIZE_PREFIX,
      ZSTD_FRAMEHEADERSIZE_MIN, ZSTD_blockHeaderSize in *; lia. }
  clear Hhs.
  assert (Hbt: bytes_ok (fr_t s hs j)) by (unfold fr_t; apply Forall_sublist; auto).
  assert (Hc0: 0 <= c) by (eapply b3_cbs_nonneg; eauto).
  assert (Hlt: Zlength (fr_t s hs j) = Zlength s - (hs + j)) by (unfold fr_t; rewrite Zlength_sublist; lia).
  pose proof (b3_last_range _ Hbt) as Hlast.
  assert (Herr: is_error_code r = true ->
                forall c' sz, decode_frame_m (dmode_of pr) dm no_wlim s = FOk c' sz -> ocap < Zlength c').
  { intros Hr. eapply b3_err_model; eauto; lia. }
  assert (Hnext: is_error_code r = false -> bp_last (block_props_of (fr_t s hs j)) <> 1 ->
                 fr_OT dm h s hs (j + ZSTD_blockHeaderSize + c) (out ++ cnt) st2).
  { intros Hr Hl. eapply b3_next; eauto; lia. }
  assert (Hlst: is_error_code r = false -> bp_last (block_props_of (fr_t s hs j)) = 1 ->
                 forall o k, fr_DB dm h s hs = Some (o, k) -> o = out ++ cnt /\ k = j + ZSTD_blockHeaderSize + c).
  { intros Hr Hl. eapply b3_last; eauto; lia. }
  assert (Hlbs: bp_last (block_props_of (fr_t s hs j)) = 1 ->
                exists f nb, blocks_size f (fr_rest s hs) = Some (j + ZSTD_blockHeaderSize + c, nb)).
  { intros Hl. eapply b3_last_bs; eauto; lia. }
  assert (Hcodes: is_error_code r = true -> frame_codes3 (dmode_of pr) dm s ocap r).
  { intros Hr. apply (fr_codes_blk (dmode_of pr) (sel_on pr dsp) dm s hs h j out st c ocap r Hhdr);
      try assumption; try lia.
    - intros st' out' E. exact (proj2 (H15 _ _ E) Hr).
    - match goal with Hx: bp_type _ <> 2 -> _ |- _ => intro Hn; exact (Hx Hn Hr) end. }
  assert (Hre: is_error_code r = false -> bp_last (block_props_of (fr_t s hs j)) = 1 ->
               fr_RE dm h s hs (j + ZSTD_blockHeaderSize + c) (out ++ cnt)).
  { intros Hr Hl. eapply b3_last_re; eauto; lia. }
  (* the exact model: an error fails the frame; otherwise the loop invariant's exact conjunct moves to the next
     block, or the last block ends the model's blocks *)
  assert (Hxerr: is_error_code r = true -> ox = None -> dm = no_dict -> pr = dparams_dflt -> e = ExtNone ->
                 frame_exact ts0 s ocap r oc2 od 0 (ts_lxb st2))
    by (intros Hr; exact (b3_exact_err j out st r st2 cnt oc2 (ts_lxb st2) HC Hxinv Hxdec Hr)).
  assert (Hxn: is_error_code r = false -> bp_last (block_props_of (fr_t s hs j)) <> 1 ->
               fr_xinv ox dm e ocap s pr h hs ts0 (j + ZSTD_blockHeaderSize + c) (out ++ cnt) st2)
    by (intros Hr Hl; eapply b3_xinv_next; eauto).
  assert (Hxa: is_error_code r = false -> bp_last (block_props_of (fr_t s hs j)) = 1 ->
               fr_xaft ox dm e ocap s pr h hs ts0 (j + ZSTD_blockHeaderSize + c) (out ++ cnt) st2)
    by (intros Hr Hl; eapply b3_xaft; eauto).
  clear H15 Hrl Hxinv Hxdec.
  unfold fr_Delta, fr_LR, fr_R. abbreviate_semax.
  dw0p (is_error_code r = false).
  { forward. forward_call r.
    forward_if.
    { destruct (is_error_code r) eqn:Hr; [ | ctr].
      assert (Hxe := Hxerr eq_refl).
      errblk. forward.
      Exists r oc2 (fr_fs fs pr h hs fdid cold2 (fr_xx fs pr h out)) 0 d1 (ts_lxb st2). rewrite Z.add_0_r, Z.sub_0_r.
      sep_apply (fr_selR_post DENT W gv p fs ox dm e osh obase _ oc od ocap ish ibase _ ic ioff s pr dsp d l tbl xq
                   lent am hb h _ d1 HC).
      sep_apply (zg_fold gv). unfold fcore3, cfg_fmt, cfg_lit. entailer!.
      split; [apply (b3_uo_trans oc oc1 oc2 od (od + Zlength out) (od + ocap)); auto; pose proof (Zlength_nonneg out); lia | ].
      split; [apply fr_err3; [assumption | apply (Herr eq_refl)] | ].
      split; [solve_cold | split; [intro Hl; apply Hlent; exact Hl | intros _; eapply fr_fp; exact HC]]. }
    forward. entailer!.
    destruct (is_error_code r); [ | reflexivity].
    match goal with Hx: Int.repr 1 = Int.zero |- _ => discriminate Hx end. }
  Intros. match goal with Hx: is_error_code r = false |- _ => rename Hx into Hne end.
  destruct (H13 Hne) as (Hrc & Hlc & Hbc & Hsc). clear H13. rewrite Hne.
  subst r.
  dw0; [forward; apply andp_left2; apply derives_refl | ].
  unfold frame_fields, fr_fs. cbn [fs_previousDstEnd fs_gpDictCopy fs_prefixStart fs_virtualStart fs_dictEnd
    fs_expected fs_fParams fs_processedCSize fs_decodedSize fs_bType fs_stage fs_xxh fs_headerSize
    fs_validateChecksum fs_rleSize fs_isFrameDecompression fs_dictID fs_ddictIsCold].
  Intros.
  forward.
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
    let F := eval pattern out in R in
    lazymatch F with ?G _ => forward_if (PROPx P (LOCALx L (SEPx (G (out ++ cnt))))) end end.
  { assert (Hck1: fr_vck pr h = true).
    { destruct (fr_vck pr h); [reflexivity | exfalso].
      match goal with Hx: Int.repr 0 <> Int.zero |- _ => apply Hx; reflexivity end. }
    unfold fr_xx. rewrite Hck1. unfold xxh_field.
    assert_PROP (field_compatible (tarray tuchar oN) [] obase) as Hfc by entailer!.
    assert_PROP (field_compatible t_dctx (DOT _format) p) as Hff by entailer!.
    assert (Hfx: field_compatible t_dctx (DOT _xxhState) p).
    { destruct Hff as (A & B & C & D & _). refine (conj A (conj B (conj C (conj D _)))).
      cbv - [Z.lt Z.le]. split; [exact I | ]. repeat (first [left; reflexivity | right]). }
    destruct (Z.eq_dec (Zlength cnt) 0) as [Hz | Hz].
    - assert (cnt = []) by (destruct cnt; [reflexivity | rewrite Zlength_cons in Hz; pose proof (Zlength_nonneg cnt); lia]).
      subst cnt.
      sep_apply (b3_zero_at osh oN oc2 obase (od + Zlength out) Hob).
      destruct (Z.eq_dec ocap 0) as [HN | HN].
      + assert (Hlo: Zlength out = 0) by (pose proof (Zlength_nonneg out); lia).
        forward_call (Ews, field_address t_dctx (DOT _xxhState) p, 0, out, osh,
                      offset_val (od + Zlength out) obase, @nil Z, W).
        { rewrite ?Zlength_nil; cancel. }
        { try intros _. rewrite Hlo, Z.add_0_r. apply HW; auto. }
        unfold fr_xx. rewrite Hck1. unfold xxh_field. rewrite Zlength_nil.
        sep_apply (data_at_zero_array_inv osh tuchar (xxh_bytes []) (offset_val (od + Zlength out) obase) eq_refl eq_refl).
        entailer!.
      + forward_call (Ews, field_address t_dctx (DOT _xxhState) p, 0, out, osh,
                      offset_val (od + Zlength out) obase, @nil Z, [pw_bytes osh oN oc2 obase]).
        { change (pws_pred [pw_bytes osh oN oc2 obase]) with (data_at osh (tarray tuchar oN) oc2 obase * emp)%logic; rewrite sepcon_emp; rewrite ?Zlength_nil; cancel. }
        { try intros _. change (pws_pred [pw_bytes osh oN oc2 obase]) with (data_at osh (tarray tuchar oN) oc2 obase * emp)%logic; rewrite sepcon_emp.
          apply b3_wvp_off; [apply writable_readable_share; auto | pose proof (Zlength_nonneg out); lia | lia]. }
        unfold fr_xx. rewrite Hck1. unfold xxh_field.
        change (pws_pred [pw_bytes osh oN oc2 obase]) with (data_at osh (tarray tuchar oN) oc2 obase * emp)%logic; rewrite sepcon_emp. rewrite Zlength_nil.
        sep_apply (data_at_zero_array_inv osh tuchar (xxh_bytes []) (offset_val (od + Zlength out) obase) eq_refl eq_refl).
        entailer!.
    - assert (Hsplit: data_at osh (tarray tuchar oN) oc2 obase =
        (data_at osh (tarray tuchar (od + Zlength out)) (sublist 0 (od + Zlength out) oc2) obase *
         data_at osh (tarray tuchar (Zlength cnt)) (xxh_bytes cnt) (offset_val (od + Zlength out) obase) *
         data_at osh (tarray tuchar (oN - (od + Zlength out + Zlength cnt)))
           (sublist (od + Zlength out + Zlength cnt) oN oc2) (offset_val (od + Zlength out + Zlength cnt) obase))%logic).
      { rewrite (b3_split3 osh oN (od + Zlength out) (Zlength cnt) oc2 obase)
          by (auto; pose proof (Zlength_nonneg out); pose proof (Zlength_nonneg cnt); lia).
        rewrite Hsc. reflexivity. }
      rewrite Hsplit. Intros.
      forward_call (Ews, field_address t_dctx (DOT _xxhState) p, 0, out, osh,
                    offset_val (od + Zlength out) obase, cnt, @nil ptr_witness).
      { change (pws_pred []) with (@emp mpred _ _). cancel. }
      unfold fr_xx. rewrite Hck1. unfold xxh_field. change (pws_pred []) with (@emp mpred _ _). rewrite Hsplit.
      entailer!. }
  { forward.
    assert (Hck0: fr_vck pr h = false).
    { destruct (fr_vck pr h); [exfalso | reflexivity].
      match goal with Hx: Int.repr 1 = Int.zero |- _ => discriminate Hx end. }
    unfold fr_xx. rewrite Hck0. entailer!. }
  match goal with |- semax _ (PROPx ?P (LOCALx ?L ?R)) _ _ =>
    let L' := b3_drop_op L in
    forward_if (PROPx P (LOCALx (temp _op (offset_val (od + Zlength (out ++ cnt)) obase) :: L') R)) end.
  { forward. entailer!. rewrite Zlength_app. f_equal; lia. }
  { forward. entailer!. rewrite Zlength_app.
    match goal with Hx: Int64.repr (Zlength cnt) = Int64.zero |- _ =>
      apply repr_inj_unsigned64 in Hx; [ | rep_lia | rep_lia] end.
    f_equal; lia. }
  forward. forward.
  unfold bp_val. forward.
  pose proof (Zlength_nonneg out) as Hlo0. pose proof (Zlength_nonneg cnt) as Hlc0.
  assert (Hsub2: sublist od (od + Zlength (out ++ cnt)) oc2 = zbytes (out ++ cnt)).
  { rewrite Zlength_app. replace (od + (Zlength out + Zlength cnt)) with (od + Zlength out + Zlength cnt) by lia.
    rewrite (sublist_split od (od + Zlength out) (od + Zlength out + Zlength cnt)) by lia.
    rewrite Hsc, (b3_uo_prefix oc1 oc2 (od + Zlength out) (od + ocap) od (od + Zlength out)), H8, map_app;
      auto; lia. }
  assert (Huo2: unchanged_outside oc oc2 od (od + ocap))
    by (apply (b3_uo_trans oc oc1 oc2 od (od + Zlength out) (od + ocap)); auto; lia).
  assert (Hbo2: bytes_ok (out ++ cnt)) by (apply Forall_app; auto).
  assert (Hlo2: Zlength (out ++ cnt) <= ocap) by (rewrite Zlength_app; lia).
  assert (Hj2: hs + (j + ZSTD_blockHeaderSize + c) <= Zlength s) by (unfold ZSTD_blockHeaderSize in *; lia).
  forward_if.
  { assert (Hl1: bp_last (block_props_of (fr_t s hs j)) = 1).
    { unfold block_props_of in *; cbn [bp_last] in *. lia. }
    forward.
    unfold fr_Brk, S_aft, fr_SEP, fr_LOC, fr_outP.
    Exists (j + ZSTD_blockHeaderSize + c) (out ++ cnt) oc2 st2 cold2.
    unfold frame_fields, fr_fs. cbn [fs_previousDstEnd fs_gpDictCopy fs_prefixStart fs_virtualStart fs_dictEnd
      fs_expected fs_fParams fs_processedCSize fs_decodedSize fs_bType fs_stage fs_xxh fs_headerSize
      fs_validateChecksum fs_rleSize fs_isFrameDecompression fs_dictID fs_ddictIsCold].
    pose proof (Hlbs Hl1) as Hbs3. pose proof (Hre Hne Hl1) as Hre3. pose proof (Hxa Hne Hl1) as Hxa3. cbn [app].
    entailer!.
    split3; [unfold ZSTD_blockHeaderSize; lia | f_equal; lia | do 2 f_equal; lia]. }
  { assert (Hl1: bp_last (block_props_of (fr_t s hs j)) <> 1).
    { unfold block_props_of in *; cbn [bp_last] in *. intro E.
      match goal with Hx: Int.repr _ = Int.zero |- _ => rewrite E in Hx; discriminate Hx end. }
    pose proof (Hnext Hne Hl1) as Hot2. pose proof (Hxn Hne Hl1) as Hxn3.
    forward.
    unfold fr_Inv, S_inv, fr_SEP, fr_LOC, fr_outP.
    Exists (j + ZSTD_blockHeaderSize + c) (out ++ cnt) oc2 st2 cold2.
    unfold frame_fields, fr_fs. cbn [fs_previousDstEnd fs_gpDictCopy fs_prefixStart fs_virtualStart fs_dictEnd
      fs_expected fs_fParams fs_processedCSize fs_decodedSize fs_bType fs_stage fs_xxh fs_headerSize
      fs_validateChecksum fs_rleSize fs_isFrameDecompression fs_dictID fs_ddictIsCold].
    entailer!.
    split3; [unfold ZSTD_blockHeaderSize; lia | f_equal; lia | do 2 f_equal; lia]. }
Qed.

End Seg.

End CM_Frame3_B3_1.
