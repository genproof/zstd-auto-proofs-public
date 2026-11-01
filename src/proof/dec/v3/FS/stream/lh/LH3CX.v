(* ZSTD_decompressStream, case zdss_loadHeader with the exact claim: piece C (the stable-buffer check, ZSTD_decompressBegin_usingDDict, the skippable frame or ZSTD_decodeFrameHeader, the window), litExtraBuffer kept (LH3XDefs.lhC_x), its returns' model outcome. *)
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3XDefs Zstd.proof.dec.v3.FS.stream.lh.LH3C_lib Zstd.proof.dec.v3.FS.stream.lh.LH3C.
Require Import Zstd.proof.model.ParamsH Zstd.proof.model.ExCall Zstd.proof.model.ExStreamFacts.
Require Zstd.proof.model.ExStream Zstd.proof.model.ExHuf Zstd.proof.model.ExBlock Zstd.proof.model.Exact.
Local Open Scope logic.

Section CM_LH3CX_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.

(* ---------- the model at piece C's returns ---------- *)

(* the model's st_header_done fails when its single-pass shortcut is not taken and either the frame is a
   Zstandard frame (not a skippable magic) with a Dictionary_ID (no dictionary in the model: dres = None), or
   the window, raised to 1 KiB, is beyond ZSTD_MAXWINDOWSIZE_DEFAULT *)
Lemma lhC_st_err (inp: list Z) (room: Z) (z: zstate_x) (h: frame_header) (ip: Z) :
  ((negb (fh_contentSize h =? ZSTD_CONTENTSIZE_UNKNOWN) && negb (fh_frameType h =? 1)
     && (room - Zlength (@nil Z) >=? fh_contentSize h) && (Zlength (ExStream.zs_hbuf XS z) =? ip))%bool = true ->
   forall cs, frame_compressed_size inp = Some cs -> Zlength inp < cs) ->
  ((is_skippable_magic (le_field (ExStream.zs_hbuf XS z) 0 4) = false /\ fh_dictID h <> 0) \/
   Z.max (fh_windowSize h) (2 ^ ZSTD_WINDOWLOG_ABSOLUTEMIN) > ExStream.ZS_MAXWINDOWSIZE_DEFAULT) ->
  ExStream.st_header_done XS (ExBlock.xst_begin ExHuf.xhuf) Exact.xblock xframe1 inp room z h ip nil =
    ExStream.LErr XS.
Proof.
  intros Hsc Hcase. unfold ExStream.st_header_done. cbv zeta.
  match goal with |- (match ?s with Some _ => _ | None => _ end) = _ => destruct s as [cs|] eqn:Es end.
  - exfalso.
    match type of Es with (if ?b then _ else _) = _ => destruct b eqn:Eb end; [| discriminate].
    destruct (frame_compressed_size inp) as [cs'|] eqn:Ef; [| discriminate].
    destruct (Z.leb_spec cs' (Zlength inp)); [| discriminate].
    specialize (Hsc eq_refl cs' eq_refl). lia.
  - destruct Hcase as [(Hm & Hd) | Hw].
    + rewrite Hm. apply Z.eqb_neq in Hd. rewrite Hd. reflexivity.
    + destruct (is_skippable_magic (le_field (ExStream.zs_hbuf XS z) 0 4)); [| destruct (negb (fh_dictID h =? 0))];
        try reflexivity;
        (destruct (Z.gtb_spec (Z.max (fh_windowSize h) (2 ^ ZSTD_WINDOWLOG_ABSOLUTEMIN))
                     ExStream.ZS_MAXWINDOWSIZE_DEFAULT); [reflexivity | lia]).
Qed.

(* the configuration of a new context: format zstd1, default parameters, a buffered output *)
Lemma lhC_fresh (a: dsa) (w: lw) (hb: list Z) :
  lh_entry a w hb -> fresh_cfg (a_st a) ->
  c3_par (w_k w) = dparams_dflt /\ lh_mg (w_k w) = false /\ c3_stable (w_k w) = false.
Proof.
  intros He (_ & Hp & _ & Hst & _).
  destruct He as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hbc & _).
  destruct Hbc as (Hstab & Hpar & _).
  unfold lh_mg. rewrite Hpar, Hp. split; [reflexivity |]. split; [reflexivity |]. rewrite Hstab; exact Hst.
Qed.

(* a return of piece C is a model error or a memory allocation (S3Main.ex_err): from the entry, with the header
   h parsed and the shortcut not taken (lhB_none), the model's iteration is st_header_done on h without its
   shortcut; a Dictionary_ID without a dictionary, or a window beyond the default maximum, fails there too; a
   stable output buffer is not the configuration of a new context; the other returns of lh_rc are not piece
   C's (another header result, or the shortcut taken) *)
Lemma lhC_rc_xok (a: dsa) (w: lw) (hb: list Z) (h: frame_header) (r ipos': Z) (w': lw) :
  dsa_ok a -> lh_entry a w hb -> w_opc w = a_opos a ->
  get_frame_header_m (lh_mg (w_k w)) hb = FH_ok h -> gfh3_facts (lh_mg (w_k w)) hb h -> lhB_none a w hb h ->
  lh_rc a w hb r ipos' w' -> lh_xok a w hb r ipos' w'.
Proof.
  intros Ha He Hop Hh Hgf Hn Hrc Hx. left.
  assert (Hlen: Zlength (a_xin a) = a_isz a - a_ipos a).
  { unfold a_xin. destruct Ha as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hi & _ & Hib & _).
    rewrite Zlength_sublist by lia. lia. }
  (* the model's step at the entry is st_header_done on h without the shortcut *)
  assert (Hm: fresh_cfg (a_st a) ->
    ((is_skippable_magic (le_field hb 0 4) = false /\ fh_dictID h <> 0) \/
     Z.max (fh_windowSize h) (2 ^ ZSTD_WINDOWLOG_ABSOLUTEMIN) > ExStream.ZS_MAXWINDOWSIZE_DEFAULT) ->
    exists z0 zi f ip dl, ex_loop a z0 zi f ip dl /\ one_iter_x (a_xin a) (a_xroom a) zi ip dl = ExStream.LErr XS).
  { intros Hf Hcase.
    destruct (lhC_fresh a w hb He Hf) as (_ & Hmg & _).
    destruct (lhx_view a w hb He Hx Hf) as (z0 & zi & f & Hl & _ & _ & Hhb & Hit).
    exists z0, zi, f, (w_ipc w - a_ipos a), nil. split; [exact Hl |]. rewrite Hit.
    unfold ExStream.st_load_header. rewrite Hhb.
    rewrite <- get_frame_header_zstd1, <- Hmg, Hh.
    apply lhC_st_err; cbn [ExStream.zs_hbuf ExStream.z_fp]; rewrite ?Hhb; [| exact Hcase].
    intros Hb cs Hcs.
    apply andb_prop in Hb. destruct Hb as (Hb & Hip). apply andb_prop in Hb. destruct Hb as (Hb & Hroom).
    apply andb_prop in Hb. destruct Hb as (Hu & Hft).
    apply negb_true_iff, Z.eqb_neq in Hu. apply negb_true_iff, Z.eqb_neq in Hft.
    apply Z.geb_le in Hroom. apply Z.eqb_eq in Hip. rewrite Zlength_nil in Hroom.
    rewrite Hlen. unfold a_xroom in Hroom.
    apply (Hn Hu Hft); [lia | lia |].
    rewrite Hmg, frame_compressed_size_zstd1. exact Hcs. }
  destruct Hrc.
  - (* RC_hdr *) congruence.
  - (* RC_more_err *) congruence.
  - (* RC_hint *) congruence.
  - (* RC_short: the shortcut was taken *)
    exfalso. assert (h0 = h) by congruence. subst h0.
    destruct H1 as (Hft & Hu & Hcap & Hip & Hcs & Hle & _).
    specialize (Hn Hu Hft Hcap Hip cSize Hcs). lia.
  - (* RC_small *)
    intros Hf. destruct (lhC_fresh a w hb He Hf) as (_ & _ & Hst). congruence.
  - (* RC_dict *)
    apply ex_err_of_loop. intros Hf. apply Hm; [exact Hf |]. left.
    assert (h0 = h) by congruence. subst h0. split; [| exact H4].
    destruct (lhC_fresh a w hb He Hf) as (_ & Hmg & _). rewrite Hmg in Hgf.
    destruct Hgf as (_ & _ & _ & _ & _ & _ & _ & Hft1 & _).
    destruct (is_skippable_magic (le_field hb 0 4)) eqn:E; [| reflexivity].
    exfalso. apply H1. apply Hft1. auto.
  - (* RC_window *)
    apply ex_err_of_loop. intros Hf. apply Hm; [exact Hf |]. right.
    assert (h0 = h) by congruence. subst h0.
    destruct (lhC_fresh a w hb He Hf) as (Hp & _ & _). rewrite Hp in H3.
    cbn in H3. unfold ZSTD_WINDOWSIZE_ABSMIN, dp_wmax_dflt in H3.
    unfold ExStream.ZS_MAXWINDOWSIZE_DEFAULT, ZSTD_WINDOWLOG_ABSOLUTEMIN. lia.
  - (* RC_mem *)
    intros _. left. reflexivity.
Qed.

(* ---------- piece C ---------- *)

(* the relational piece C with litExtraBuffer kept (LH3C.lhC_l_ok); its returns are lh_xok by lhC_rc_xok, the
   output position at the entry being the call's (nothing delivered: call_inv of lh_ctx) *)
Lemma lhC_x_ok : lhC_x_stmt.
Proof.
unfold lhC_x_stmt.
intros Hsel Hbeg Hpr Espec DENT TABS BR a w hb h tbl d1 did1 HD HT Ha He Hs Hx Hc Hg Hf HA Hn.
set (k1 := k_A (w_k w) (fh_val h) d1 did1).
assert (Hop: w_opc w = a_opos a).
{ destruct Hc as (_ & _ & Hci & _ & _ & _ & _ & Hdl & _).
  destruct Hci as (_ & _ & _ & _ & Hl & _). rewrite Hdl, Zlength_nil in Hl. lia. }
eapply semax_post with (R' := lhC_post_l DENT TABS a w hb h k1);
  [ | | | | exact (lhC_l_ok Hsel Hbeg Hpr Espec DENT TABS BR a w hb h tbl d1 did1 HD HT Ha He Hs Hg Hf HA) ].
- apply andp_left2. cbn [RA_normal lhC_post_l lhC_post_x].
  apply exp_left; intro c; apply (exp_right c). unfold lhC_x. apply derives_refl.
- apply andp_left2. cbn [RA_break lhC_post_l lhC_post_x]. apply derives_refl.
- apply andp_left2. cbn [RA_continue lhC_post_l lhC_post_x]. apply derives_refl.
- intros vl. apply andp_left2. cbn [RA_return lhC_post_l lhC_post_x]. unfold lh_ret, lh_ret_x.
  apply exp_left; intro r; apply (exp_right r).
  apply exp_left; intro ip'; apply (exp_right ip').
  apply exp_left; intro w'; apply (exp_right w').
  unfold PROPx. apply andp_derives; [| apply derives_refl].
  apply prop_derives. cbn [fold_right]. intros (H1 & H2 & H3 & _).
  exact (conj H1 (conj H2 (conj H3 (conj (lhC_rc_xok a w hb h r ip' w' Ha He Hop Hg Hf Hn H3) I)))).
Qed.

End CM_LH3CX_1.
