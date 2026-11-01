(* FS3 one-shot frames: a compressed block (case 2 of the switch) (port of v2 body_frame.v's fr_cmp_ok). *)
Require Import Zstd.proof.dec.v3.FS.frames.Frames3Defs Zstd.proof.dec.v3.FS.frames.Frames3Model.
Require Import Zstd.proof.model.ExHuf Zstd.proof.model.ExBlock Zstd.proof.model.ExFrame Zstd.proof.model.ExFrameFacts.
Require Import Zstd.proof.model.Exact Zstd.proof.model.ExBlockWritten Zstd.proof.model.ExBlockBytes.
Local Open Scope logic.

Section CM_Frame3_cmp_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* ---------- helpers of the compressed block (v2 body_frame.v) ---------- *)

(* the block size bound of a parsed header (Frames3Model.gfh3_range's first conjunct, proved here) *)
Lemma fr3c_bytes_ok_magic: forall s, bytes_ok s -> bytes_ok (magic_bytes ++ s).
Proof.
  intros. unfold bytes_ok. apply Forall_app. split; [|exact H].
  change magic_bytes with [40; 181; 47; 253]. repeat constructor; unfold is_byte; lia.
Qed.

Lemma fr3c_gfh_bsm: forall mg x h,
  bytes_ok x -> get_frame_header_m mg x = FH_ok h -> 0 <= fh_blockSizeMax h <= ZSTD_BLOCKSIZE_MAX.
Proof.
  intros [|] x h Hb H.
  - cbn [get_frame_header_m negb] in H. destruct (Zlength x <? 1); [discriminate|].
    destruct (get_frame_header (magic_bytes ++ x)) as [|k|h'] eqn:G; try discriminate.
    injection H as <-. exact (proj1 (gfh_range _ h' (fr3c_bytes_ok_magic _ Hb) G)).
  - exact (proj1 (gfh_range x h Hb H)).
Qed.

Lemma fr3c_slice_sub: forall (l: list Z) i k,
  0 <= i -> 0 <= k -> slice l i k = sublist i (i + k) l.
Proof.
  intros. unfold slice, sublist. rewrite firstn_skipn_comm. f_equal. f_equal. lia.
Qed.

Lemma fr3c_sub_pp: forall p a c, isptr p ->
  force_val (sem_sub_pp tuchar (offset_val a p) (offset_val c p)) = Vlong (Int64.repr (a - c)).
Proof.
  intros. destruct p; try contradiction. unfold sem_sub_pp. simpl. rewrite if_true by auto. simpl.
  rewrite (Ptrofs.add_commut i (Ptrofs.repr a)), (Ptrofs.add_commut i (Ptrofs.repr c)).
  rewrite Ptrofs.sub_shifted. change (Ptrofs.repr 1) with Ptrofs.one. rewrite Ptrofs.divs_one by reflexivity.
  unfold Vptrofs. simpl. f_equal. unfold Ptrofs.to_int64. apply repr_eqm.
  unfold Ptrofs.sub. rewrite !Ptrofs.unsigned_repr_eq. change Ptrofs.modulus with (2^64).
  rewrite Zmod_mod. rewrite <- Zminus_mod. reflexivity.
Qed.

Lemma fr3c_pws_app: forall W x, pws_pred (W ++ [x]) = pws_pred W * pw_pred x.
Proof.
  intros. unfold pws_pred. induction W as [|a W IH]; simpl.
  - rewrite sepcon_emp, emp_sepcon. auto.
  - unfold pws_pred in IH. rewrite IH, sepcon_assoc. auto.
Qed.

Lemma fr3c_hs0: forall md sel dm s hs h, fr_hdr3 md sel dm s hs h -> 0 <= hs.
Proof.
  intros md sel dm s hs h (Hb & Hm & Hhs & _). subst hs. unfold header_size_m, mg_sh in *.
  unfold ZSTD_FRAMEHEADERSIZE_MIN, ZSTD_blockHeaderSize in Hm.
  destruct (md_magicless md).
  - pose proof (fhs_range _ (byte_at_range s 0 Hb ltac:(lia))). lia.
  - pose proof (fhs_range _ (byte_at_range s 4 Hb ltac:(lia))). lia.
Qed.

Lemma fr3c_byte_at_Znth: forall l i, 0 <= i -> byte_at l i = Znth i l.
Proof.
  intros. unfold byte_at, Znth. rewrite if_false by lia. reflexivity.
Qed.

(* the history zstd sees after the frame's output out (written at od .. od + |out|), the extDict e
   ending with hist *)
Lemma fr3c_hist_view: forall oc1 od out e hist ws,
  match e with ExtIn _ _ => False | _ => True end ->
  0 <= ext_len e -> ext_view e hist ->
  0 <= od -> od + Zlength out <= Zlength oc1 -> sublist od (od + Zlength out) oc1 = zbytes out ->
  hist_view oc1 (od + Zlength out) od e hist out ws.
Proof.
  intros oc1 od out e hist ws He Hel Hev Hod Hoc Hsub k Hk.
  rewrite Zlength_app in Hk. pose proof (Zlength_nonneg hist). pose proof (Zlength_nonneg out).
  unfold chist. rewrite Zlength_app.
  replace (od + Zlength out - od) with (Zlength out) by lia.
  destruct (Z_le_gt_dec k (Zlength out)) as [Hko | Hko].
  - rewrite (proj2 (Z.leb_le _ _) Hko). split; [lia | ].
    assert (Hz: Znth (Zlength out - k) (sublist od (od + Zlength out) oc1) =
                Znth (Zlength out - k) (zbytes out)) by (rewrite Hsub; reflexivity).
    rewrite Znth_sublist in Hz by lia. rewrite Znth_map in Hz by lia.
    replace (Zlength out - k + od) with (od + Zlength out - k) in Hz by lia. rewrite Hz.
    rewrite !fr3c_byte_at_Znth by lia. rewrite app_Znth2 by lia. do 3 f_equal. lia.
  - replace (k <=? Zlength out) with false by (symmetry; apply Z.leb_gt; lia).
    destruct (Hev (k - Zlength out)) as [Hkl Hb]; [lia | ].
    split; [lia | ].
    destruct e as [ | e1 elen | sh eb en ec e1 elen]; [simpl in Hkl; lia | contradiction | ].
    simpl in Hb. rewrite Hb. rewrite !fr3c_byte_at_Znth by lia. rewrite app_Znth1 by lia.
    do 3 f_equal. lia.
Qed.

(* the history zstd may read is defined bytes: the frame's output, then the extDict (its bytes are the
   dictionary content's) *)
Lemma fr3c_hist_def: forall oc1 od out e,
  match e with ExtIn _ _ => False | _ => True end ->
  (forall k, 1 <= k <= ext_len e -> is_byte_val (ext_byte e k)) ->
  0 <= od -> od + Zlength out <= Zlength oc1 -> sublist od (od + Zlength out) oc1 = zbytes out ->
  bytes_ok out ->
  hist_def oc1 (od + Zlength out) od e.
Proof.
  intros oc1 od out e He Hed Hod Hoc Hsub Hob k Hk.
  pose proof (Zlength_nonneg out).
  unfold chist. replace (od + Zlength out - od) with (Zlength out) in * by lia.
  destruct (Z_le_gt_dec k (Zlength out)) as [Hko | Hko].
  - rewrite (proj2 (Z.leb_le _ _) Hko).
    assert (Hz: Znth (Zlength out - k) (sublist od (od + Zlength out) oc1) =
                Znth (Zlength out - k) (zbytes out)) by (rewrite Hsub; reflexivity).
    rewrite Znth_sublist in Hz by lia. rewrite Znth_map in Hz by lia.
    replace (Zlength out - k + od) with (od + Zlength out - k) in Hz by lia. rewrite Hz.
    exists (Znth (Zlength out - k) out). split; [ | reflexivity].
    unfold bytes_ok in Hob. rewrite Forall_Znth in Hob. apply Hob. lia.
  - replace (k <=? Zlength out) with false by (symmetry; apply Z.leb_gt; lia).
    destruct e as [ | e1 elen | sh eb en ec e1 elen]; [simpl in Hk; lia | contradiction | ].
    specialize (Hed (k - Zlength out) ltac:(simpl in Hk |- *; lia)). exact Hed.
Qed.

(* the bytes before op when the dictionary content hist lies in the output array just before the frame (at
   od - |hist| .. od, outside what the blocks write): the content, then the frame's output out *)
Lemma fr3c_pre_byte: forall oc oc1 od ocap hist out k,
  Zlength hist <= od -> od + ocap <= Zlength oc -> Zlength oc1 = Zlength oc -> Zlength out <= ocap ->
  unchanged_outside oc oc1 od (od + ocap) ->
  sublist (od - Zlength hist) od oc = zbytes hist ->
  sublist od (od + Zlength out) oc1 = zbytes out ->
  1 <= k <= Zlength out + Zlength hist ->
  Znth (od + Zlength out - k) oc1 = Vint (Int.repr (Znth (Zlength hist + Zlength out - k) (hist ++ out))).
Proof.
  intros oc oc1 od ocap hist out k Hh Hoc Hl1 Ho Hun Hsh Hso Hk.
  pose proof (Zlength_nonneg hist). pose proof (Zlength_nonneg out).
  destruct (Z_le_gt_dec k (Zlength out)) as [Hko | Hko].
  - assert (Hz: Znth (Zlength out - k) (sublist od (od + Zlength out) oc1) =
                Znth (Zlength out - k) (zbytes out)) by (rewrite Hso; reflexivity).
    rewrite Znth_sublist in Hz by lia. rewrite Znth_map in Hz by lia.
    replace (Zlength out - k + od) with (od + Zlength out - k) in Hz by lia. rewrite Hz.
    rewrite app_Znth2 by lia. do 3 f_equal. lia.
  - rewrite Hun by lia.
    assert (Hz: Znth (Zlength hist + Zlength out - k) (sublist (od - Zlength hist) od oc) =
                Znth (Zlength hist + Zlength out - k) (zbytes hist)) by (rewrite Hsh; reflexivity).
    rewrite Znth_sublist in Hz by lia. rewrite Znth_map in Hz by lia.
    replace (Zlength hist + Zlength out - k + (od - Zlength hist)) with (od + Zlength out - k) in Hz by lia.
    rewrite Hz. rewrite app_Znth1 by lia. reflexivity.
Qed.

(* the history the block decoder sees at op = od + |out|, wherever the frame's history lies (frame_hist): the
   segment start ps, the layout, the history's view and its defined bytes *)
Lemma fr3c_hist_any: forall fs obase oN oc od ocap e hist oc1 out ws,
  match e with ExtIn _ _ => False | _ => True end -> ext_def e ->
  frame_hist fs obase oN oc od e hist -> Zlength oc = oN ->
  0 <= od -> od + ocap <= oN -> Zlength oc1 = oN -> Zlength out <= ocap ->
  unchanged_outside oc oc1 od (od + ocap) ->
  sublist od (od + Zlength out) oc1 = zbytes out -> bytes_ok out -> bytes_ok hist ->
  exists ps, (ps = od \/ ps = od - Zlength hist) /\ layout_ok fs obase oN (od + Zlength out) ps e /\
    hist_view oc1 (od + Zlength out) ps e hist out ws /\ hist_def oc1 (od + Zlength out) ps e.
Proof.
  intros fs obase oN oc od ocap e hist oc1 out ws He Hed Hfh Hl0 Hod Hoc Hl1 Ho Hun Hso Hbo Hbh. subst oN.
  pose proof (Zlength_nonneg hist). pose proof (Zlength_nonneg out).
  destruct Hfh as [[Hlay Hev] | (-> & Hh & Hlay & Hsh)].
  - exists od. split; [left; reflexivity|]. split; [| split].
    + unfold layout_ok in *. destruct Hlay as (Hp & Hps & Hvs & Hel & Hm). repeat split; auto; lia.
    + apply fr3c_hist_view; auto; [destruct Hlay as (_ & _ & _ & ? & _); lia | lia].
    + apply fr3c_hist_def; auto; lia.
  - exists (od - Zlength hist). split; [right; reflexivity|]. split; [| split].
    + unfold layout_ok in *. destruct Hlay as (Hp & Hps & Hvs & Hel & Hm). repeat split; auto; lia.
    + intros k Hk. rewrite Zlength_app in Hk. simpl ext_len. unfold chist.
      rewrite (proj2 (Z.leb_le _ _)) by lia. split; [lia |].
      rewrite (fr3c_pre_byte oc oc1 od ocap hist out k) by first [assumption | lia].
      rewrite fr3c_byte_at_Znth by (rewrite Zlength_app; lia). rewrite Zlength_app. do 3 f_equal; lia.
    + intros k Hk. simpl ext_len in Hk. unfold chist.
      rewrite (proj2 (Z.leb_le _ _)) by lia.
      rewrite (fr3c_pre_byte oc oc1 od ocap hist out k) by first [assumption | lia].
      eexists; split; [| reflexivity].
      assert (Hb: bytes_ok (hist ++ out)) by (unfold bytes_ok in *; apply Forall_app; auto).
      unfold bytes_ok in Hb. rewrite Forall_Znth in Hb. apply Hb. rewrite Zlength_app. lia.
Qed.

(* the empty window at op (no room left, cap = 0): the history described is only the extDict, defined bytes *)
Lemma fr3c_hist_def0: forall od e,
  match e with ExtIn _ _ => False | _ => True end ->
  (forall k, 1 <= k <= ext_len e -> is_byte_val (ext_byte e k)) ->
  0 <= od -> hist_def [] 0 od e.
Proof.
  intros od e He Hed Hod k Hk. unfold chist.
  replace (k <=? 0 - od) with false by (symmetry; apply Z.leb_gt; lia).
  destruct e as [ | e1 elen | sh eb en ec e1 elen]; [simpl in Hk; lia | contradiction | ].
  specialize (Hed (k + od) ltac:(simpl in Hk |- *; lia)). simpl in Hed.
  replace (e1 - (k - (0 - od))) with (e1 - (k + od)) by lia. exact Hed.
Qed.


(* ---------- the exact model of the compressed block (DecIface.block_exact) ---------- *)

Lemma fr3c_zbytes_inj (a b: list Z) : bytes_ok a -> bytes_ok b -> zbytes a = zbytes b -> a = b.
Proof.
  revert b. induction a as [ | x a IH]; intros [ | y b] Ha Hb E; simpl in E; try discriminate; auto.
  assert (Hx: Vint (Int.repr x) = Vint (Int.repr y)) by congruence.
  assert (Ht: zbytes a = zbytes b) by congruence.
  inv Ha. inv Hb. f_equal; [| apply IH; auto].
  unfold is_byte in *.
  apply (f_equal (fun v => match v with Vint i => Int.unsigned i | _ => 0 end)) in Hx. simpl in Hx.
  rewrite !Int.unsigned_repr in Hx by rep_lia. auto.
Qed.

(* the stores of an empty literals section with no room: none; the literal pointer does not depend on the
   destination *)
Lemma fr3c_store0: forall body lused bsm, 0 <= bsm ->
  exists lr li, forall m op, x_lits_store body [] lused m op 0 bsm 0 false = Some (m, lr, li, li, false).
Proof.
  intros body lused bsm Hb. unfold x_lits_store, x_alloc_loc. rewrite Zlength_nil.
  replace (0 >? bsm + XWILDCOPY + 0 + XWILDCOPY) with false
    by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; unfold XWILDCOPY; lia).
  change (0 <=? XLITEXTRA) with true. cbn [andb negb xl_is_split].
  destruct (Z.land (byte_at body 0) 3 =? 0).
  - destruct (lused + XWILDCOPY <=? Zlength body).
    + exists R_src, (lused - 0). intros m op. rewrite Z.add_0_r. reflexivity.
    + exists R_lxb, 0. intros m op. reflexivity.
  - destruct (Z.land (byte_at body 0) 3 =? 1); exists R_lxb, 0; intros m op; reflexivity.
Qed.

(* the last literals when none are left: nothing copied *)
Lemma fr3c_last0: forall e s, xsp s = false -> xlim s = xli s -> xop s <= xe_oend e ->
  x_last e s = Some (xmm s, xop s).
Proof.
  intros e s Hsp Hl Ho. unfold x_last. rewrite Hsp. rewrite Hl, Z.sub_diag.
  replace (0 >? xe_oend e - xop s) with false by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
  cbn. rewrite Z.add_0_r. reflexivity.
Qed.

(* the sequences of a block declaring no positive number of them, with no literals left: no execution; the
   outcome depends only on the bitstream *)
Lemma fr3c_seqs0: forall e1 s1 e2 s2 tabs rep bits nbSeq, nbSeq <= 0 ->
  xsp s1 = false -> xlim s1 = xli s1 -> xop s1 <= xe_oend e1 ->
  xsp s2 = false -> xlim s2 = xli s2 -> xop s2 <= xe_oend e2 ->
  match x_seqs ExCSeq.dseq_one ExCSeq.c_offset e1 tabs rep bits nbSeq s1,
        x_seqs ExCSeq.dseq_one ExCSeq.c_offset e2 tabs rep bits nbSeq s2 with
  | None, None => True
  | Some (m1, o1, r1), Some (m2, o2, r2) => m1 = xmm s1 /\ o1 = xop s1 /\ m2 = xmm s2 /\ o2 = xop s2 /\ r1 = r2
  | _, _ => False
  end.
Proof.
  intros e1 s1 e2 s2 [[tLL tOF] tML] rep bits nbSeq Hn H1 H2 H3 H4 H5 H6. unfold x_seqs.
  destruct (negb (bs_okb bits)); [exact I|].
  replace (Z.to_nat nbSeq) with O by lia.
  repeat match goal with |- context [match rd ?a ?b ?c with _ => _ end] =>
    destruct (rd a b c) as [[? ?]|]; [|exact I] end.
  cbn [x_seq_loop].
  match goal with |- context [negb (?p =? 0)] => destruct (negb (p =? 0)); [exact I|] end.
  rewrite !fr3c_last0 by assumption. auto.
Qed.

(* with no room (cap = 0) a compressed block's outcome does not depend on its destination region nor on the
   history pointers: its literals must be empty (expectedWriteSize = 0), a block with sequences fails, and the
   empty last literals copy nothing *)
Lemma fr3c_xblock_cap0: forall (st: xstate) mem1 ps1 op1 ds1 de1 mem2 ps2 op2 ds2 de2 body bsm,
  match xblock st mem1 ps1 op1 ds1 de1 body bsm 0 false, xblock st mem2 ps2 op2 ds2 de2 body bsm 0 false with
  | None, None => True
  | Some (a, _, n1), Some (b, _, n2) => a = b /\ n1 = n2
  | _, _ => False
  end.
Proof.
  intros. unfold xblock, x_block.
  destruct (Z.gtb_spec (Zlength body) bsm) as [Hb|Hb]; [exact I|].
  pose proof (Zlength_nonneg body) as Hb0.
  replace (Z.min bsm 0) with 0 by lia.
  destruct (x_lits xhuf x_lits_huf (x_huf xhuf st) body bsm 0 false) as [[[lits lused] huf]|] eqn:El; [|exact I].
  pose proof (lits_len _ _ _ _ _ _ _ _ El) as Hl.
  destruct lits as [|x lits]; [| rewrite Zlength_cons in Hl; pose proof (Zlength_nonneg lits); lia].
  destruct (x_seq_header ncount_c (x_seq xhuf st) (skipn (Z.to_nat lused) body)) as [[[nbSeq tabs] hused]|];
    [|exact I].
  destruct (Z.gtb_spec nbSeq 0) as [Hn|Hn]; cbn [andb Z.eqb]; [exact I|].
  destruct (fr3c_store0 body lused bsm ltac:(lia)) as (lr & li & Hs). rewrite !Hs.
  assert (Hloc: forall op, op <= match x_litloc body lused (Zlength (@nil Z)) bsm 0 false with
                                 | XL_in_dst => op + bsm + XWILDCOPY | _ => op + 0 end).
  { intros op. unfold x_litloc, x_alloc_loc. rewrite Zlength_nil.
    replace (0 >? bsm + XWILDCOPY + 0 + XWILDCOPY) with false
      by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; unfold XWILDCOPY; lia).
    change (0 <=? XLITEXTRA) with true. cbn [andb negb].
    destruct (_ && _)%bool; lia. }
  destruct (nbSeq =? 0).
  - rewrite !fr3c_last0 by (cbn; first [reflexivity | apply Hloc]).
    cbn [xmm xop xm_lxb]. split; [reflexivity | lia].
  - destruct tabs as [tb|]; [|exact I].
    set (X1 := x_seqs _ _ _ _ _ _ _ {| xmm := {| xm_dst := map Some mem1; xm_lxb := _ |}; xop := op1;
                                      xlr := _; xli := _; xlim := _; xsp := _ |}).
    set (X2 := x_seqs _ _ _ _ _ _ _ {| xmm := {| xm_dst := map Some mem2; xm_lxb := _ |}; xop := op2;
                                      xlr := _; xli := _; xlim := _; xsp := _ |}).
    assert (HR: match X1, X2 with
                | None, None => True
                | Some (m1, o1, r1), Some (m2, o2, r2) =>
                    m1 = {| xm_dst := map Some mem1; xm_lxb := x_lxb xhuf st |} /\ o1 = op1 /\
                    m2 = {| xm_dst := map Some mem2; xm_lxb := x_lxb xhuf st |} /\ o2 = op2 /\ r1 = r2
                | _, _ => False
                end) by (unfold X1, X2; apply fr3c_seqs0; first [lia | reflexivity | apply Hloc]).
    clearbody X1 X2.
    destruct X1 as [[[m1 o1] r1]|]; destruct X2 as [[[m2 o2] r2]|]; try exact HR; try exact I.
    destruct HR as (-> & -> & -> & -> & ->). cbn. split; [reflexivity | lia].
Qed.

(* the compressed block's call with room (DecIface.block_exact at the region of the frame's output, base od, no
   extDict, prefixStart at the frame's start): an error iff the model fails, else the model's state and the content
   the C wrote (cnt, bytes) *)
Lemma fr3c_exact_room: forall (st: tstate) osh obase oN oc1 od room ish ibase iN ic ioff body hist out wsize bsm
    r oc2 ts' cnt,
  0 <= od -> od + Zlength out <= oN -> sublist od (od + Zlength out) oc1 = zbytes out ->
  bytes_ok out -> bytes_ok body -> bytes_ok (ts_lxb st) -> xh_good (x_huf xhuf (ts_x st)) ->
  block_exact st (Build_outarr osh obase oN oc1 (od + Zlength out) room) (Build_inwin ish ibase iN ic ioff body)
    (Build_hctx ExtNone od hist out wsize) bsm 0 r oc2 ts' ->
  (is_error_code r = true -> ts' = None) ->
  (is_error_code r = false -> bytes_ok cnt /\ Zlength cnt = r /\
     sublist (od + Zlength out) (od + Zlength out + r) oc2 = zbytes cnt) ->
  match xblock (ts_x st) out 0 (Zlength out) 0 0 body bsm room false with
  | None => is_error_code r = true
  | Some (st2', mem2, n) =>
      is_error_code r = false /\ slice mem2 (Zlength out) n = cnt /\ exists ts2, ts' = Some ts2 /\ ts_x ts2 = st2'
  end.
Proof.
  intros st osh obase oN oc1 od room ish ibase iN ic ioff body hist out wsize bsm r oc2 ts' cnt
    Hod HoN Hsub Hbo Hbb Hbl Hg Hbe Herr Hok.
  pose proof (Zlength_nonneg out) as Ho0.
  assert (Hreg: hc_region (Build_hctx ExtNone od hist out wsize) od = Some (0, 0, 0))
    by (cbn; rewrite Z.sub_diag; reflexivity).
  specialize (Hbe od out 0 0 0 ltac:(cbn; lia) ltac:(cbn; lia) Hsub Hreg ltac:(lia) ltac:(lia)
                ltac:(intros j Hj; cbn in Hj; lia)).
  cbn [oa_d oa_cap iw_s] in Hbe.
  replace (od + Zlength out - od) with (Zlength out) in Hbe by lia.
  change (x_block xhuf x_lits_huf ncount_c ExCSeq.dseq_one ExCSeq.c_offset) with xblock in Hbe.
  change (0 =? 1) with false in Hbe.
  destruct (xblock (ts_x st) out 0 (Zlength out) 0 0 body bsm room false) as [[[st2' mem2] n]|] eqn:E;
    [|exact Hbe].
  destruct Hbe as (Hr & Hs2 & ts2 & Hts & Hx).
  assert (Hre: is_error_code r = false).
  { destruct (is_error_code r) eqn:X; [rewrite (Herr eq_refl) in Hts; discriminate | reflexivity]. }
  destruct (Hok Hre) as (Hbc & Hlc & Hsc).
  destruct (xblock_written_cap _ _ _ _ _ _ _ _ _ _ _ _ _ (conj Ho0 (Z.le_refl (Zlength out))) E) as (Hn & Hm & _ & _).
  destruct (xblock_bytes (ts_x st) _ _ _ _ _ _ _ _ _ _ _ _ Hbo Hbb Hbl Hg E) as (Hbm & _ & _).
  split; [exact Hre|]. split; [|eauto].
  apply fr3c_zbytes_inj; [apply xbb_slice, Hbm | exact Hbc |].
  rewrite <- Hsc. subst r.
  rewrite fr3c_slice_sub by lia.
  replace (sublist (od + Zlength out) (od + Zlength out + n) oc2)
    with (sublist (Zlength out) (Zlength out + n) (sublist od (od + Zlength mem2) oc2))
    by (rewrite sublist_sublist by lia; f_equal; lia).
  rewrite Hs2, sublist_map. reflexivity.
Qed.

(* the compressed block's call without room (the empty output array at op): its outcome is the model's at the
   frame's output, with capacity 0 *)
Lemma fr3c_exact_cap0: forall (st: tstate) osh q od ish ibase iN ic ioff body hist out wsize bsm r oc2 ts' cnt,
  0 <= od -> bytes_ok out -> bytes_ok body ->
  block_exact st (Build_outarr osh q 0 [] 0 0) (Build_inwin ish ibase iN ic ioff body)
    (Build_hctx ExtNone od hist out wsize) bsm 0 r oc2 ts' ->
  (is_error_code r = true -> ts' = None) ->
  (is_error_code r = false -> Zlength cnt = r) ->
  match xblock (ts_x st) out 0 (Zlength out) 0 0 body bsm 0 false with
  | None => is_error_code r = true
  | Some (st2', mem2, n) =>
      is_error_code r = false /\ slice mem2 (Zlength out) n = cnt /\ exists ts2, ts' = Some ts2 /\ ts_x ts2 = st2'
  end.
Proof.
  intros st osh q od ish ibase iN ic ioff body hist out wsize bsm r oc2 ts' cnt Hod Hbo Hbb Hbe Herr Hlen.
  pose proof (Zlength_nonneg out) as Ho0.
  assert (Hreg: hc_region (Build_hctx ExtNone od hist out wsize) 0 = Some (od, od, od))
    by (cbn; rewrite Z.sub_0_r; reflexivity).
  specialize (Hbe 0 [] od od od ltac:(cbn; lia) ltac:(cbn; try rewrite Zlength_nil; lia) eq_refl Hreg Hod Hod
                ltac:(intros j Hj; cbn in Hj; try rewrite Zlength_nil; lia)).
  cbn [oa_d oa_cap iw_s] in Hbe.
  change (x_block xhuf x_lits_huf ncount_c ExCSeq.dseq_one ExCSeq.c_offset) with xblock in Hbe.
  change (0 =? 1) with false in Hbe. change (0 - 0) with 0 in Hbe.
  pose proof (fr3c_xblock_cap0 (ts_x st) [] od 0 od od out 0 (Zlength out) 0 0 body bsm) as HC.
  destruct (xblock (ts_x st) [] od 0 od od body bsm 0 false) as [[[a m1] n1]|];
    destruct (xblock (ts_x st) out 0 (Zlength out) 0 0 body bsm 0 false) as [[[b m2] n2]|] eqn:E2;
    try contradiction; [|exact Hbe].
  destruct HC as [<- <-]. destruct Hbe as (Hr & _ & ts2 & Hts & Hx).
  assert (Hre: is_error_code r = false).
  { destruct (is_error_code r) eqn:X; [rewrite (Herr eq_refl) in Hts; discriminate | reflexivity]. }
  destruct (xblock_written_cap _ _ _ _ _ _ _ _ _ _ _ _ _ (conj Ho0 (Z.le_refl (Zlength out))) E2) as (Hn & _).
  assert (Hn0: n1 = 0) by lia.
  assert (Hc: cnt = []) by (apply Zlength_nil_inv; rewrite (Hlen Hre); lia).
  split; [exact Hre|]. split; [|eauto]. rewrite Hc, Hn0. reflexivity.
Qed.

(* fr_xdec of a compressed block from the model's outcome of its call *)
Lemma fr3c_xdec: forall ox dm e ocap s pr h hs j out st r st2 cnt c ts',
  cblock_size (fr_t s hs j) = Some c -> c <= Zlength (fr_t s hs j) - 3 ->
  bp_type (block_props_of (fr_t s hs j)) = 2 ->
  (is_error_code r = false -> ts' = Some st2) ->
  (fx_on ox dm e pr ->
   match xblock (ts_x st) out 0 (Zlength out) 0 0 (slice (fr_t s hs j) 3 c) (fh_blockSizeMax h)
           (ocap - Zlength out) false with
   | None => is_error_code r = true
   | Some (st2', mem2, n) =>
       is_error_code r = false /\ slice mem2 (Zlength out) n = cnt /\ exists ts2, ts' = Some ts2 /\ ts_x ts2 = st2'
   end) ->
  fr_xdec ox dm e ocap s pr h hs j out st r st2 cnt.
Proof.
  intros ox dm e ocap s pr h hs j out st r st2 cnt c ts' Hc Hle Hty Hst HX Hon. specialize (HX Hon).
  unfold xb_one. rewrite Hc. unfold ZSTD_blockHeaderSize.
  replace (c >? Zlength (fr_t s hs j) - 3) with false by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
  cbv zeta. rewrite Hty. cbn [Z.eqb Pos.eqb].
  destruct (xblock (ts_x st) out 0 (Zlength out) 0 0 (slice (fr_t s hs j) 3 c) (fh_blockSizeMax h)
              (ocap - Zlength out) false) as [[[st2' mem2] n]|]; [|exact HX].
  destruct HX as (Hr & Hs & ts2 & Hts & Hx). rewrite (Hst Hr) in Hts. injection Hts as <-.
  auto.
Qed.

Section Seg.
Context (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR: blrel)
  (W: list ptr_witness) (gv: globals) (p: val) (fs: fstate) (ox: option ddx) (dm: dict_model) (e: ext_seg)
  (osh: share) (obase: val) (oN: Z) (oc: list val) (od ocap: Z)
  (ish: share) (ibase: val) (iN: Z) (ic: list val) (ioff: Z) (s: list Z) (sp ssp: val) (v_bp: val)
  (pr: dparams) (dsp: val) (d: dfields) (l: list (val * ddict_st)) (tbl: list val) (xq: option (val * val)) (lent: bool)
  (am: option cmem) (hb: Z) (h: frame_header) (hs: Z) (fdid: Z) (d1: dfields) (ts0: tstate).

Lemma fr_cmp_ok3: DENT_OK DENT -> TABS_OK TABS ->
  fr_case_stmt DENT TABS SR BR W gv p fs ox dm e osh obase oN oc od ocap ish ibase iN ic ioff s sp ssp v_bp pr dsp d l tbl xq lent am hb h hs fdid d1 ts0 2.
Proof.
  intros HD HT. unfold fr_case_stmt. intros Espec j out oc1 st cold c Hctx Hty.
  change (fr_case 2) with
    (Ssequence
      (Scall (Some _t'11)
        (Evar _ZSTD_decompressBlock_internal
          (Tfunction ((tptr (Tstruct _ZSTD_DCtx_s noattr)) :: (tptr tvoid) :: tulong :: (tptr tvoid) ::
                      tulong :: tint :: nil) tulong cc_default))
        ((Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr))) :: (Etempvar _op (tptr tuchar)) ::
         (Ecast (Ebinop Osub (Etempvar _oBlockEnd (tptr tuchar)) (Etempvar _op (tptr tuchar)) tlong) tulong) ::
         (Etempvar _ip (tptr tuchar)) :: (Etempvar _cBlockSize tulong) :: (Econst_int (Int.repr 0) tint) :: nil))
      (Sset _decodedSize (Etempvar _t'11 tulong))).
  destruct Hctx. unfold S_sw, S_dec, fr_SEP, fr_LOC, fr_outP. simpl app. Intros.
  rename H2 into Hxinv.
  (* litExtraBuffer holds bytes (the exact model's content is then bytes: ExBlockBytes) *)
  assert_PROP (bytes_ok (ts_lxb st)) as Hlxb.
  { sep_apply (HT gv p ox st). unfold tables_uninit, lit_extra_at. entailer!. }
  pose proof (fr3c_hs0 _ _ _ _ _ _ fc_hdr) as Hhs0.
  pose proof fc_hdr as (Hbs & Hmin & Hhs & Hhs3 & h0 & Hgfh & Hh & _).
  assert (Hbsm: 0 <= fh_blockSizeMax h <= ZSTD_BLOCKSIZE_MAX).
  { pose proof (fr3c_gfh_bsm _ _ _ (Forall_sublist _ _ _ _ Hbs) Hgfh) as Hb0.
    destruct fc_par as (_ & _ & Hbm & _). subst h. simpl. unfold dmode_of; simpl.
    destruct (dp_bmax pr =? 0); [ | destruct Hbm as [Hbm | Hbm]; [rewrite Hbm |]]; unfold ZSTD_BLOCKSIZE_MAX in *; lia. }
  set (t := fr_t s hs j) in *.
  assert (Hlt: Zlength t = Zlength s - (hs + j)) by (unfold t, fr_t; rewrite Zlength_sublist; lia).
  assert (Hc0: 0 <= c).
  { match goal with Hcs: cblock_size t = Some c |- _ =>
      pose proof (cblock_size_range t c ltac:(unfold t, fr_t; apply Forall_sublist; auto) Hcs) end; lia. }
  unfold ZSTD_blockHeaderSize in *.
  set (body := slice t 3 c).
  assert (Hbody: body = sublist (hs + j + 3) (hs + j + 3 + c) s).
  { unfold body. rewrite fr3c_slice_sub by lia. unfold t, fr_t. rewrite sublist_sublist by lia. f_equal; lia. }
  assert (Hlb: Zlength body = c) by (rewrite Hbody, Zlength_sublist; lia).
  assert (Hwin: inwin_ok (Build_inwin ish ibase iN ic (ioff + hs + (j + 3)) body)).
  { unfold inwin_ok; simpl. rewrite Hbody. eapply win_sub; eauto; lia. }
  assert (Hblk: blk_res st (dm_content dm) out t c (fh_blockSizeMax h) (fh_windowSize h) =
                match decode_block st (dm_content dm) out body (fh_blockSizeMax h) (fh_windowSize h) with
                | Some (st', content) => Some (st', out ++ content) | None => None end).
  { unfold blk_res. rewrite Hty. reflexivity. }
  assert (Hbd: slice t 3 c = body) by reflexivity.
  assert (Hbb: bytes_ok body) by (rewrite Hbody; apply Forall_sublist; auto).
  clearbody body. clear Hhs.
  assert (Hrl: forall r' cnt' st2', fr_RL dm h s hs j out st c r' cnt' st2')
    by (intros r' cnt' st2' _ Hn; exfalso; exact (Hn Hty)).
  unfold fr_Delta. abbreviate_semax.
  pose proof (Zlength_nonneg out) as Hout0.
  gather_SEP (data_at Ers tulong (Vlong (Int64.repr 3)) (gv _ZSTD_blockHeaderSize)) (zg_rest gv).
  replace_SEP 0 (zstd_globals gv) by (entailer!; apply zg_fold).
  replace_SEP 4 (cfg_lit p) by (unfold cfg_lit; entailer!).
  freeze [1;3;6;7;8;9;10;16;17] FR1.
  assert (Hcold: fs_ddictIsCold (fr_fs fs pr h hs fdid cold (fr_xx fs pr h out)) = Vint (Int.repr 0) \/
                 fs_ddictIsCold (fr_fs fs pr h hs fdid cold (fr_xx fs pr h out)) = Vint (Int.repr 1)).
  { simpl. destruct H10 as [-> | ->]; auto. }
  destruct (zlt (Zlength out) ocap) as [Hol | Hoe].
  - (* the history the block's matches copy: the frame's output so far, then the dictionary content *)
    destruct (fr3c_hist_any fs obase oN oc od ocap e (dm_content dm) oc1 out (fh_windowSize h) fc_ext fc_ed
                (fc_lay ltac:(lia)) fc_oN) as (ps & Hps & Hlay & Hhv & Hhd); auto; try lia.
    forward_call (gv, p, fr_fs fs pr h hs fdid cold (fr_xx fs pr h out), ox, st, fh_blockSizeMax h, 0, W,
                  Build_outarr osh obase oN oc1 (od + Zlength out) (ocap - Zlength out),
                  Build_inwin ish ibase iN ic (ioff + hs + (j + 3)) body,
                  Build_hctx e ps (dm_content dm) out (fh_windowSize h)).
    { entailer!. destruct obase; try contradiction. simpl. destruct (peq b b); [reflexivity | congruence]. }
    { entailer!. simpl. rewrite fr3c_sub_pp by auto. try rewrite Hlb.
      replace (od + ocap - (od + Zlength out)) with (ocap - Zlength out) by lia. reflexivity. }
    { simpl. cancel. }
    { unfold outarr_ok; cbn [oa_cap oa_d oa_sh oa_N oa_c oa_base hc_ps hc_ext]. split; [ | split; [ | split]].
      - refine (conj fc_osh _). repeat split; lia.
      - intros; lia.
      - destruct e; auto; contradiction.
      - assert (Hhp: hist_ptrs_ok (fr_fs fs pr h hs fdid cold (fr_xx fs pr h out))
                       (Build_outarr osh obase oN oc1 (od + Zlength out) (ocap - Zlength out)) e).
        { destruct fc_hp as (Hp1 & Hp2 & Hp3). unfold hist_ptrs_ok, dictend_ok; simpl.
          refine (conj Hp1 (conj Hp2 _)). destruct Hp3 as [Hp3 | Hp3]; [left; exact Hp3 | right; right].
          destruct e; try contradiction; exact Hp3. }
        first [exact Hhp | exact (conj Hhp Hhd)]. }
    cbn [oa_cap oa_d oa_sh oa_N oa_c oa_base iw_s iw_sh iw_N iw_c iw_base iw_off hc_ps hc_ext hc_hist hc_out hc_wsize].
    Intros vret. destruct vret as [[[r oc2] cold2] ts2]; simpl fst in *; simpl snd in *.
    forward. thaw FR1.
    assert (Hec: ext_clear (od + Zlength out) ps (ocap - Zlength out) (fh_blockSizeMax h) e (dm_content dm) out
                   (fh_windowSize h)).
    { destruct e; simpl; auto; contradiction. }
    assert (Hob: bytes_ok out) by assumption.
    match goal with Hb: _ \/ _ -> bytes_ok _ -> bytes_ok _ -> block_ok _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      specialize (Hb (or_intror (conj Hhv Hec)) fc_hb Hob); rename Hb into Hbok end.
    assert (Hcl: ext_clean (od + Zlength out) (ocap - Zlength out) e) by (destruct e; simpl; auto; contradiction).
    match goal with Hu: unchanged_outside oc1 oc2 _ _ |- _ =>
      replace (od + Zlength out + (ocap - Zlength out)) with (od + ocap) in Hu by lia end.
    rewrite (zg_eq gv). unfold cfg_lit.
    change (fs_set_cold (fr_fs fs pr h hs fdid cold (fr_xx fs pr h out)) cold2) with (fr_fs fs pr h hs fdid cold2 (fr_xx fs pr h out)).
    assert (Hcold2: cold2 = fs_ddictIsCold fs \/ cold2 = Vint (Int.repr 0)).
    { match goal with Hc: cold2 = fs_ddictIsCold _ \/ _ |- _ => simpl in Hc; destruct Hc as [-> | ->] end;
      destruct H10; auto. }
    (* the exact model (DecIface.block_exact at the frame's output): the block's outcome is the model's step *)
    assert (HXg: forall cnt st2,
      (is_error_code r = false -> ts2 = Some st2) ->
      (is_error_code r = false -> bytes_ok cnt /\ Zlength cnt = r /\
         sublist (od + Zlength out) (od + Zlength out + r) oc2 = zbytes cnt) ->
      fr_xdec ox dm e ocap s pr h hs j out st r st2 cnt).
    { intros cnt st2 Hst Hok. apply (fr3c_xdec ox dm e ocap s pr h hs j out st r st2 cnt c ts2); auto.
      intros Hon. pose proof Hon as (Hox & Hdm & Hpr & He). rewrite (Hbd : slice (fr_t s hs j) 3 c = body).
      assert (Hps0: ps = od) by (rewrite Hdm in Hps; cbn in Hps; lia).
      match goal with Hx: ox = None -> block_exact _ _ _ _ _ _ _ _ _ |- _ => pose proof (Hx Hox) as Hbe end.
      rewrite He, Hps0 in Hbe.
      apply (fr3c_exact_room st osh obase oN oc1 od (ocap - Zlength out) ish ibase iN ic (ioff + hs + (j + 3))
               body (dm_content dm) out (fh_windowSize h) (fh_blockSizeMax h) r oc2 ts2 cnt); auto; try lia.
      - exact (proj1 (Hxinv Hon)).
      - intros Hx. match goal with Hy: is_error_code r = true -> ts2 = None /\ _ |- _ => exact (proj1 (Hy Hx)) end. }
    destruct (is_error_code r) eqn:Herr.
    + (* an error *)
      match goal with Hx: true = true -> _ = None /\ dec_err _ |- _ => destruct (Hx eq_refl) as [? Hde] end.
      subst ts2. cbv iota. Intros lxb.
      assert (Hxd: fr_xdec ox dm e ocap s pr h hs j out st r (mk_tstate st false lxb) [])
        by (apply HXg; intros Hf; discriminate Hf).
      assert (Hmod: forall st' out',
        blk_res st (dm_content dm) out t c (fh_blockSizeMax h) (fh_windowSize h) = Some (st', out') ->
        (true = false -> out' = out ++ [] /\ ts_d (mk_tstate st false lxb) = st') /\
        (true = true -> ocap < Zlength out')).
      { intros st' out' Hb. rewrite Hblk in Hb.
        destruct (decode_block st (dm_content dm) out body (fh_blockSizeMax h) (fh_windowSize h))
          as [[tsm cm] | ] eqn:Hd; [ | discriminate].
        injection Hb as <- <-. unfold block_ok in Hbok. rewrite Hd in Hbok.
        destruct Hbok as [(Hx & _) | (_ & Hlc)]; [congruence | ].
        split; intros; [discriminate | rewrite Zlength_app; lia]. }
      Exists r oc2 (mk_tstate st false lxb) cold2 (@nil Z). rewrite Herr. entailer!.
        all: try apply Hrl.
      all: try (intros; discriminate).
      all: try (intros; assumption).
      all: try match goal with Hb: blk_res _ _ _ _ _ _ _ = Some _ |- _ => destruct (Hmod _ _ Hb); auto end.
      all: try apply derives_refl.
    + (* a success *)
      match goal with Hs: false = false -> _ <= _ /\ _ |- _ => destruct (Hs eq_refl) as (Hrc & _ & Hts & _ & Hcx) end.
      destruct (Hcx Hhd (or_introl Hcl)) as (cnt0 & Hcnt0 & Hbc0).
      destruct ts2 as [ts2 | ]; [ | congruence].
      assert (Hl0: Zlength cnt0 = r).
      { apply (f_equal (@Zlength val)) in Hcnt0. rewrite Zlength_sublist, Zlength_map in Hcnt0 by lia. lia. }
      destruct (decode_block st (dm_content dm) out body (fh_blockSizeMax h) (fh_windowSize h))
        as [[tsm cm] | ] eqn:Hd.
      * unfold block_ok in Hbok. rewrite Hd in Hbok.
        destruct Hbok as [(_ & Hr & Hsub & Hbm & Hts2 & _) | (Hx & _)]; [ | destruct Hx as [Hx' _]; congruence].
        cbn [option_map] in Hts2. injection Hts2 as <-.
        assert (Hmod: forall st' out',
          blk_res st (dm_content dm) out t c (fh_blockSizeMax h) (fh_windowSize h) = Some (st', out') ->
          (false = false -> out' = out ++ cm /\ ts_d ts2 = st') /\ (false = true -> ocap < Zlength out')).
        { intros st' out' Hb. rewrite Hblk in Hb. injection Hb as <- <-.
          split; intros; [split; auto | discriminate]. }
        assert (Hxd: fr_xdec ox dm e ocap s pr h hs j out st r ts2 cm)
          by (apply HXg; [intros _; reflexivity | intros _; split; [|split]; auto; lia]).
        Exists r oc2 ts2 cold2 cm. rewrite Herr. entailer!.
        all: try apply Hrl.
        all: try (intros; discriminate).
        all: try match goal with Hb: blk_res _ _ _ _ _ _ _ = Some _ |- _ => destruct (Hmod _ _ Hb); auto end.
        all: try (intros _; repeat split; auto; lia).
      * assert (Hmod: forall st' out',
          blk_res st (dm_content dm) out t c (fh_blockSizeMax h) (fh_windowSize h) = Some (st', out') ->
          (false = false -> out' = out ++ cnt0 /\ ts_d ts2 = st') /\ (false = true -> ocap < Zlength out')).
        { intros st' out' Hb. rewrite Hblk in Hb. discriminate. }
        assert (Hxd: fr_xdec ox dm e ocap s pr h hs j out st r ts2 cnt0)
          by (apply HXg; [intros _; reflexivity | intros _; split; [|split]; auto]).
        Exists r oc2 ts2 cold2 cnt0. rewrite Herr. entailer!.
        all: try apply Hrl.
        all: try (intros; discriminate).
        all: try match goal with Hb: blk_res _ _ _ _ _ _ _ = Some _ |- _ => destruct (Hmod _ _ Hb); auto end.
        all: try (intros _; repeat split; auto; lia).
  - (* no room left: op = oBlockEnd; the callee's weak validity of op comes from the output array, moved
       into its witness list; its output is the empty array at op *)
    assert (Heq: Zlength out = ocap) by lia.
    assert (Hop: isptr (offset_val (od + Zlength out) obase)) by (destruct obase; try contradiction; simpl; auto).
    assert (Hwv: pws_pred W * data_at osh (tarray tuchar oN) oc1 obase |--
                 weak_valid_pointer (offset_val (od + Zlength out) obase)).
    { destruct (Z.eq_dec ocap 0) as [Hz | Hz].
      - rewrite Heq, Hz, Z.add_0_r.
        eapply derives_trans; [apply sepcon_derives; [apply fc_W; auto | apply derives_refl] | ].
        apply extend_weak_valid_pointer.
      - rewrite sepcon_comm.
        eapply derives_trans; [apply sepcon_derives; [apply data_at_memory_block | apply derives_refl] | ].
        eapply derives_trans; [apply sepcon_derives; [apply memory_block_weak_valid_pointer | apply derives_refl] | ].
        4: apply extend_weak_valid_pointer.
        all: simpl; try rewrite Z.max_r by lia; try lia.
        apply readable_nonidentity, writable_readable; auto. }
    gather_SEP (pws_pred W) (data_at osh (tarray tuchar oN) oc1 obase).
    replace_SEP 0 (pws_pred (W ++ [pw_bytes osh oN oc1 obase]) *
                   data_at osh (tarray tuchar 0) [] (offset_val (od + Zlength out) obase)).
    { entailer!. rewrite fr3c_pws_app. simpl pw_pred. rewrite data_at_tuchar_zero_array_eq by auto. cancel. }
    flatten_sepcon_in_SEP.
    assert (Hhd0: hist_def [] 0 od e) by (apply fr3c_hist_def0; auto; first [exact fc_ed | lia]).
    forward_call (gv, p, fr_fs fs pr h hs fdid cold (fr_xx fs pr h out), ox, st, fh_blockSizeMax h, 0,
                  W ++ [pw_bytes osh oN oc1 obase],
                  Build_outarr osh (offset_val (od + Zlength out) obase) 0 [] 0 0,
                  Build_inwin ish ibase iN ic (ioff + hs + (j + 3)) body,
                  Build_hctx e od (dm_content dm) out (fh_windowSize h)).
    { entailer!. destruct obase; try contradiction. simpl. destruct (peq b b); [reflexivity | congruence]. }
    { entailer!. simpl. rewrite fr3c_sub_pp by auto. try rewrite Hlb.
      replace (od + Zlength out - (od + Zlength out)) with 0 by lia.
      try rewrite isptr_offset_val_zero by auto. reflexivity. }
    { simpl. cancel. }
    { unfold outarr_ok; cbn [oa_cap oa_d oa_sh oa_N oa_c oa_base hc_ps hc_ext]. split; [ | split; [ | split; [ | split; [ | split]]]].
      - refine (conj fc_osh _). repeat split; try reflexivity; lia.
      - intros _. try rewrite isptr_offset_val_zero by auto. rewrite fr3c_pws_app. exact Hwv.
      - intros; lia.
      - destruct e; auto; contradiction.
      - destruct fc_hp as (Hp1 & Hp2 & Hp3). unfold hist_ptrs_ok, dictend_ok; simpl.
        refine (conj Hp1 (conj Hp2 _)). destruct Hp3 as [Hp3 | Hp3]; [left; exact Hp3 | right; right].
        destruct e; try contradiction; exact Hp3.
      - assert (Hx0: ext0_ok (W ++ [pw_bytes osh oN oc1 obase]) (fr_fs fs pr h hs fdid cold (fr_xx fs pr h out)) e).
        { match goal with He0: ext0_ok W fs e |- _ => revert He0 end.
          unfold ext0_ok; destruct e; auto. intros He0 Hen. rewrite fr3c_pws_app.
          unfold fr_fs; cbn [fs_dictEnd].
          eapply derives_trans; [apply sepcon_derives; [apply (He0 Hen) | apply derives_refl] | ].
          apply extend_weak_valid_pointer. }
        first [exact Hx0 | exact (conj Hx0 Hhd0)]. }
    cbn [oa_cap oa_d oa_sh oa_N oa_c oa_base iw_s iw_sh iw_N iw_c iw_base iw_off hc_ps hc_ext hc_hist hc_out hc_wsize].
    Intros vret. destruct vret as [[[r oc2] cold2] ts2]; simpl fst in *; simpl snd in *.
    forward. thaw FR1. rewrite fr3c_pws_app. simpl pw_pred.
    assert (Hob: bytes_ok out) by assumption.
    match goal with Hb: _ \/ _ -> bytes_ok _ -> bytes_ok _ -> block_ok _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      specialize (Hb (or_introl eq_refl) fc_hb Hob); rename Hb into Hbok end.
    assert (Hoc2: oc2 = []) by (apply Zlength_nil_inv; auto). subst oc2.
    sep_apply (data_at_tuchar_zero_array_inv osh (offset_val (od + Zlength out) obase)).
    rewrite (zg_eq gv). unfold cfg_lit.
    change (fs_set_cold (fr_fs fs pr h hs fdid cold (fr_xx fs pr h out)) cold2) with (fr_fs fs pr h hs fdid cold2 (fr_xx fs pr h out)).
    assert (Hcold2: cold2 = fs_ddictIsCold fs \/ cold2 = Vint (Int.repr 0)).
    { match goal with Hc: cold2 = fs_ddictIsCold _ \/ _ |- _ => simpl in Hc; destruct Hc as [-> | ->] end;
      destruct H10; auto. }
    assert (Hun: unchanged_outside oc1 oc1 (od + Zlength out) (od + ocap)) by (intros ? ? ?; reflexivity).
    (* the exact model (DecIface.block_exact at the empty array at op): the model's step with no room *)
    assert (HXg: forall cnt st2,
      (is_error_code r = false -> ts2 = Some st2) -> (is_error_code r = false -> Zlength cnt = r) ->
      fr_xdec ox dm e ocap s pr h hs j out st r st2 cnt).
    { intros cnt st2 Hst Hok. apply (fr3c_xdec ox dm e ocap s pr h hs j out st r st2 cnt c ts2); auto.
      intros Hon. pose proof Hon as (Hox & Hdm & Hpr & He). rewrite (Hbd : slice (fr_t s hs j) 3 c = body).
      replace (ocap - Zlength out) with 0 by lia.
      match goal with Hx: ox = None -> block_exact _ _ _ _ _ _ _ _ _ |- _ => pose proof (Hx Hox) as Hbe end.
      rewrite He in Hbe.
      apply (fr3c_exact_cap0 st osh (offset_val (od + Zlength out) obase) od ish ibase iN ic (ioff + hs + (j + 3))
               body (dm_content dm) out (fh_windowSize h) (fh_blockSizeMax h) r [] ts2 cnt); auto.
      intros Hx. match goal with Hy: is_error_code r = true -> ts2 = None /\ _ |- _ => exact (proj1 (Hy Hx)) end. }
    destruct (is_error_code r) eqn:Herr.
    + (* an error *)
      match goal with Hx: true = true -> _ = None /\ dec_err _ |- _ => destruct (Hx eq_refl) as [? Hde] end.
      subst ts2. cbv iota. Intros lxb.
      assert (Hxd: fr_xdec ox dm e ocap s pr h hs j out st r (mk_tstate st false lxb) [])
        by (apply HXg; intros Hf; discriminate Hf).
      assert (Hmod: forall st' out',
        blk_res st (dm_content dm) out t c (fh_blockSizeMax h) (fh_windowSize h) = Some (st', out') ->
        (true = false -> out' = out ++ [] /\ ts_d (mk_tstate st false lxb) = st') /\
        (true = true -> ocap < Zlength out')).
      { intros st' out' Hb. rewrite Hblk in Hb.
        destruct (decode_block st (dm_content dm) out body (fh_blockSizeMax h) (fh_windowSize h))
          as [[tsm cm] | ] eqn:Hd; [ | discriminate].
        injection Hb as <- <-. unfold block_ok in Hbok. rewrite Hd in Hbok.
        destruct Hbok as [(Hx & _) | (_ & Hlc)]; [congruence | ].
        split; intros; [discriminate | rewrite Zlength_app; lia]. }
      Exists r oc1 (mk_tstate st false lxb) cold2 (@nil Z). rewrite Herr. entailer!.
        all: try apply Hrl.
      all: try (intros; discriminate).
      all: try (intros; assumption).
      all: try match goal with Hb: blk_res _ _ _ _ _ _ _ = Some _ |- _ => destruct (Hmod _ _ Hb); auto end.
      all: try apply derives_refl.
    + (* a success: nothing written *)
      match goal with Hs: false = false -> _ <= _ /\ _ |- _ => destruct (Hs eq_refl) as (Hrc & _ & Hts & _) end.
      assert (r = 0) by lia. subst r.
      destruct ts2 as [ts2 | ]; [ | congruence].
      destruct (decode_block st (dm_content dm) out body (fh_blockSizeMax h) (fh_windowSize h))
        as [[tsm cm] | ] eqn:Hd.
      * unfold block_ok in Hbok. rewrite Hd in Hbok.
        destruct Hbok as [(_ & Hr & _ & _ & Hts2 & _) | (Hx & _)]; [ | destruct Hx as [Hx' _]; congruence].
        cbn [option_map] in Hts2. injection Hts2 as <-.
        assert (Hcm: cm = []) by (apply Zlength_nil_inv; auto). subst cm.
        assert (Hmod: forall st' out',
          blk_res st (dm_content dm) out t c (fh_blockSizeMax h) (fh_windowSize h) = Some (st', out') ->
          (false = false -> out' = out ++ [] /\ ts_d ts2 = st') /\ (false = true -> ocap < Zlength out')).
        { intros st' out' Hb. rewrite Hblk in Hb. injection Hb as <- <-.
          split; intros; [split; auto | discriminate]. }
        assert (Hxd: fr_xdec ox dm e ocap s pr h hs j out st 0 ts2 [])
          by (apply HXg; intros _; reflexivity).
        Exists 0 oc1 ts2 cold2 (@nil Z). rewrite Herr. entailer!.
        all: try apply Hrl.
        all: try (intros; discriminate).
        all: try match goal with Hb: blk_res _ _ _ _ _ _ _ = Some _ |- _ => destruct (Hmod _ _ Hb); auto end.
        all: try (try intros _; repeat split; try constructor; try lia; rewrite ?Z.add_0_r; apply sublist_nil).
      * assert (Hmod: forall st' out',
          blk_res st (dm_content dm) out t c (fh_blockSizeMax h) (fh_windowSize h) = Some (st', out') ->
          (false = false -> out' = out ++ [] /\ ts_d ts2 = st') /\ (false = true -> ocap < Zlength out')).
        { intros st' out' Hb. rewrite Hblk in Hb. discriminate. }
        assert (Hxd: fr_xdec ox dm e ocap s pr h hs j out st 0 ts2 [])
          by (apply HXg; intros _; reflexivity).
        Exists 0 oc1 ts2 cold2 (@nil Z). rewrite Herr. entailer!.
        all: try apply Hrl.
        all: try (intros; discriminate).
        all: try match goal with Hb: blk_res _ _ _ _ _ _ _ = Some _ |- _ => destruct (Hmod _ _ Hb); auto end.
        all: try (try intros _; repeat split; try constructor; try lia; rewrite ?Z.add_0_r; apply sublist_nil).
Qed.

End Seg.

End CM_Frame3_cmp_1.
