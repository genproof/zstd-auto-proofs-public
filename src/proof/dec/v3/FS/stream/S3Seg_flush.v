(* FS3 streaming: case zdss_flush (template v2 StreamSeg_flush.v), with the exact claim: the loop invariant after the
   flush carries S3Main.ex_call, the model's iteration ExStream.st_flush (flush/S3FlushX.v: a complete flush goes on
   at zdss_read, the ring restarted or not; an incomplete one stops the loop). *)
Require Import Zstd.proof.dec.v3.FS.stream.S3RetStmts Zstd.proof.dec.v3.FS.stream.S3ModelStmts.
Require Import Zstd.proof.dec.v3.FS.stream.flush.S3FlushLem Zstd.proof.dec.v3.FS.stream.flush.S3FlushLeaf.
Require Import Zstd.proof.dec.v3.FS.stream.S3XKit Zstd.proof.dec.v3.FS.stream.flush.S3FlushX.
Local Open Scope logic.

(* a leaf where the flush completed: flush_leaf_cpl *)
Ltac flush_leaf wrv :=
  try match goal with Hx: Int64.eq (Int64.repr _) (Int64.repr _) = true |- _ => apply Int64.same_if_eq in Hx end;
  match goal with Hx: Int64.repr ?m = Int64.repr (?oend - ?ostart) |- _ =>
    assert (m = oend - ostart) by (apply vlong_inj; [rep_lia | rep_lia | unfold vlong; rewrite Hx; reflexivity])
  end;
  match goal with Hd: ?m = Z.min _ _ |- _ => clear Hd; subst m end;
  rewrite ?add64_repr in *;
  try (match goal with |- context [?os + (?oe - ?os)] =>
    assert (Eo: os + (oe - os) = oe) by lia; rewrite Eo in * end);
  match goal with Hfh: fs_fParams _ = fh_val (fh_adj ?h ?b) |- _ =>
    eapply (flush_leaf_cpl _ _ _ _ _ _ _ h b _ _ wrv) end;
  try eassumption; try lia;
  [ .. | let d := fresh "d" in let Hd := fresh "Hd" in
         intros d Hd; unfold ds_LI_L in Hd;
         repeat (destruct Hd as [<-|Hd]; [simpl; repeat (first [left; reflexivity | right]) |]); destruct Hd ];
  try (intros X; discriminate);
  try (intros _; first [split; assumption | left; assumption | right; lia]).

Section CM_S3Seg_flush_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* case zdss_flush: no error return; both exits are breaks of the switch *)
Lemma seg_flush_x_ok : MF3 -> RET3x -> seg_case_x 4.
Proof.
intros HMF HRET Espec DENT TABS BR a w R HD HT Ha Hinv Hsmw Hlx Hst HRn HRr Hstart Hentry Hun Hxw.
unfold ds_tail. simpl seq_of_labeled_statement.
unfold ds_LI_L, ds_LI_S, ctx_rep3, ctx_body3, sgroup. Intros.
rename H6 into Hbyc. rename H7 into H6.
assert (Hpmax: sf_inSize (c3_s (w_k w)) + sf_outSize (c3_s (w_k w)) <= Ptrofs.max_unsigned) by rep_lia.
pose proof (flush_pre _ _ _ _ _ _ _ Hinv Hst) as (Hs1&Hs2&Hip&Hnn&(h&b&Hfh)&ostart&oend&Hos&Hoe&Ho&Hoe2&Hpend).
unfold ring_rep. rewrite if_false by exact Hnn. Intros.
rewrite Hos, Hoe. unfold vlong.
rewrite (H6 Hnn).
pose proof Ha as Ha0. destruct Ha0 as (Hbo&Hbi&_&Hsho&Hshi&Hshob&Hshb&_&_&Hopos&Hosz&Hloc&Hipos&Hisz&Hlibs&Hibs).
pose proof Hinv as Hinv0. destruct Hinv0 as (Hipc&Hopc&Hloc'&Hpre&Hldl&Hdl&Hbdl&Hinv').
assert_PROP (field_compatible (tarray tuchar (sf_inSize (c3_s (w_k w)) + sf_outSize (c3_s (w_k w)))) nil (sf_inBuff (c3_s (w_k w)))) as Hfc by entailer!.
rewrite (split2_data_at_Tarray_tuchar Ews (sf_inSize (c3_s (w_k w)) + sf_outSize (c3_s (w_k w))) (sf_inSize (c3_s (w_k w)))) by lia.
rewrite field_address0_offset by auto with field_compatible.
replace (sf_inSize (c3_s (w_k w)) + sf_outSize (c3_s (w_k w)) - sf_inSize (c3_s (w_k w))) with (sf_outSize (c3_s (w_k w))) by lia.
set (ocs := sublist (sf_inSize (c3_s (w_k w))) (sf_inSize (c3_s (w_k w)) + sf_outSize (c3_s (w_k w))) (sf_ring (c3_s (w_k w)))) in *.
assert (Hlocs: Zlength ocs = sf_outSize (c3_s (w_k w))) by (subst ocs; rewrite Zlength_sublist; lia).
Intros.
assert_PROP (field_compatible (tarray tuchar (a_osz a)) nil (a_ob a)) as Hfob by entailer!.
unfold ds_case_flush.
destruct R as [Rn Rb Rc Rr]; cbn [RA_normal RA_return] in HRn, HRr; subst Rn Rr.
unfold switch_ret_assert. cbv beta iota.
unfold ds_Delta. simplify_func_tycontext. abbreviate_semax.
forward. forward. forward. forward. forward. forward. forward.
match goal with |- context [nested_field_offset ?t ?g] =>
  replace (nested_field_offset t g) with (sf_inSize (c3_s (w_k w))) by (unfold nested_field_offset; simpl; lia) end.
rewrite sub64_repr.
forward_call (a_shob a, a_ob a, w_oc w, w_opc w, a_osz a - w_opc w, Ews,
  offset_val (sf_inSize (c3_s (w_k w))) (sf_inBuff (c3_s (w_k w))), ocs, ostart, oend - ostart).
3: (rewrite Hloc', Hlocs; cancel).
1: (entailer!; destruct (a_ob a); try (destruct Hfob; contradiction); simpl; unfold sameblock; simpl;
    destruct (peq b0 b0); [reflexivity| congruence]).
1: { entailer!. clear - Hfob Hopc Hopos Hosz Hip. destruct (a_ob a); try (destruct Hfob; contradiction).
     destruct (sf_inBuff (c3_s (w_k w))); try contradiction. unfold sem_sub_pp; simpl. rewrite if_true by auto.
     simpl. rewrite ptr_diff_char by rep_lia. reflexivity. }
(* the flushed bytes are defined: the ring holds bytes *)
all: try (apply Forall_sublist; unfold ocs; apply Forall_sublist; exact Hbyc).
rewrite Hlocs.
sep_apply (ring_join Ews (sf_inSize (c3_s (w_k w))) (sf_outSize (c3_s (w_k w))) (sf_ring (c3_s (w_k w)))
  (sf_inBuff (c3_s (w_k w))) H H0 H7 Hfc).
set (m := Z.min (a_osz a - w_opc w) (oend - ostart)).
assert (Hm: 0 <= m <= oend - ostart /\ m <= a_osz a - w_opc w) by (subst m; lia).
forward. forward.
forward_if (temp _t'61 (offset_val (w_opc w + m) (a_ob a))).
{ apply derives_trans with (pws_pred (a_W a) * data_at (a_shob a) (tarray tuchar (Zlength (w_oc w)))
     (copy_cells (w_oc w) (w_opc w) ocs ostart m) (a_ob a) * TT)%logic; [cancel|].
  rewrite Hloc'. apply arr_tc_test; auto; lia. }
{ forward. forward. entailer!. }
{ match goal with H: _ = nullval |- _ => rename H into Hf end.
  destruct (a_ob a); try (destruct Hfob; contradiction). discriminate. }
assert (Hmdef: m = Z.min (a_osz a - w_opc w) (oend - ostart)) by reflexivity.
clearbody m.
forward. forward. forward. forward_if.
{ (* flush complete *)
  forward. unfold fgroup3, frame_fields. rewrite Hfh. Intros. forward. forward.
  unfold MORE_COMMANDS, abbreviate. apply semax_if_seq. forward_if.
  { forward. forward. forward. forward.
    apply semax_if_seq. forward_if.
    { (* the ring restarts *)
      apply semax_skipbreak_seq2. forward. forward. forward. forward.
      change (Int.signed (Int.repr 0)) with 0.
      flush_leaf true. }
    { forward. flush_leaf false. } }
  { forward. apply semax_if_seq. forward_if.
    { match goal with Hx: Int.repr 0 <> Int.zero |- _ => contradiction Hx; reflexivity end. }
    { forward. flush_leaf false. } } }
{ (* flush incomplete *)
  forward. forward.
  assert (Hmn: m <> oend - ostart)
    by (intro E; match goal with Hx: Int64.repr m <> _ |- _ => apply Hx; rewrite E; reflexivity end).
  assert (Hmv: m = a_osz a - w_opc w) by lia.
  clear Hmdef. subst m.
  assert (Hci: call_inv a (c3_with_s (w_k w) (sf_after (c3_s (w_k w)) zdss_flush (ostart + (a_osz a - w_opc w)) oend))
      (sv_flushed (w_sv w) (a_osz a - w_opc w)) (w_ipc w) (w_opc w + (a_osz a - w_opc w))
      (copy_cells (w_oc w) (w_opc w) (ring_out (c3_s (w_k w))) ostart (a_osz a - w_opc w))
      (w_dl w ++ sublist 0 (a_osz a - w_opc w) (sv_pend (w_sv w))))
    by (apply (flush_post_inc a (w_k w) (w_sv w) (w_ipc w) (w_opc w) (w_oc w) (w_dl w) ostart oend); auto; lia).
  assert (Hxc: ex_call a
           {| w_smw := 0;
              w_k := c3_with_s (w_k w) (sf_after (c3_s (w_k w)) zdss_flush (ostart + (a_osz a - w_opc w)) oend);
              w_sv := sv_flushed (w_sv w) (a_osz a - w_opc w); w_ipc := w_ipc w;
              w_opc := w_opc w + (a_osz a - w_opc w);
              w_oc := copy_cells (w_oc w) (w_opc w) (ring_out (c3_s (w_k w))) ostart (a_osz a - w_opc w);
              w_dl := w_dl w ++ sublist 0 (a_osz a - w_opc w) (sv_pend (w_sv w)) |}).
  { pose proof Ha as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hip0 & _ & Hil & Hib & _).
    pose proof Hci as (_ & _ & _ & _ & _ & _ & Hbdl' & _).
    eapply (flush_x_inc a w _ (sv_pend (w_sv w)) ostart oend); try eassumption; try reflexivity; try lia. }
  unfold ds_inv_x;
  Exists {| w_smw := 0;
            w_k := c3_with_s (w_k w) (sf_after (c3_s (w_k w)) zdss_flush (ostart + (a_osz a - w_opc w)) oend);
            w_sv := sv_flushed (w_sv w) (a_osz a - w_opc w); w_ipc := w_ipc w;
            w_opc := w_opc w + (a_osz a - w_opc w);
            w_oc := copy_cells (w_oc w) (w_opc w) (ring_out (c3_s (w_k w))) ostart (a_osz a - w_opc w);
            w_dl := w_dl w ++ sublist 0 (a_osz a - w_opc w) (sv_pend (w_sv w)) |};
  unfold ds_LI_Px, ds_LI_L, ds_LI_S, ctx_rep3, ctx_body3, sgroup, ring_rep;
  cbn [w_smw w_k w_sv w_ipc w_opc w_oc w_dl c3_with_s c3_fs c3_tabs c3_stable c3_dict c3_s c3_par c3_sp c3_set
       sf_after sf_stage sf_inBuff sf_inSize sf_inPos sf_outBuff sf_outSize sf_outStart sf_outEnd sf_lhSize
       sf_hostage sf_nfp sf_expOut sf_hbuf sf_over sf_ring sf_mem sf_held];
  (* the flush changes no size: the allocator has given out the same bytes *)
  change (sf_given (sf_after ?s ?st ?os ?oe)) with (sf_given s);
  rewrite if_false by exact Hnn;
  rewrite Hst, add64_repr, Hloc', (H6 Hnn); unfold vlong, zdss_flush;
  entailer!;
  repeat match goal with |- _ /\ _ => split end;
  try exact Hxc; try close_lx; try close_en; try close_un;
  try (eapply flush_exit_inc; [exact Hinv | exact Hst | lia | reflexivity | reflexivity |
         cbn [sv_flushed sv_pend]; apply (pend_left_nonnil ocs ostart oend); [exact Ho | lia | exact Hpend | lia]]);
  try (apply (flush_post_inc a (w_k w) (w_sv w) (w_ipc w) (w_opc w) (w_oc w) (w_dl w) ostart oend); auto; lia). }
Qed.

End CM_S3Seg_flush_1.
