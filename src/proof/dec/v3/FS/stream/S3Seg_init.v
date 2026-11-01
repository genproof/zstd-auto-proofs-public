(* FS3 streaming: case zdss_init with the exact claim (ExStream.z_new_frame,
   then the fall-through into case zdss_loadHeader). *)
Require Import Zstd.proof.dec.v3.FS.stream.S3RetStmts Zstd.proof.dec.v3.FS.stream.S3ModelStmts.
Require Import Zstd.proof.dec.v3.FS.stream.S3XKit.
Require Import Zstd.proof.model.ExCall Zstd.proof.model.ExStreamFacts.
Require Zstd.proof.model.ExStream.
Local Open Scope logic.

Section CM_S3Seg_init_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* the stream fields after case zdss_init: stage loadHeader, lhSize = inPos = outStart = outEnd = 0,
   hostageByte = 0, expectedOutBuffer = ev *)
Definition s_after_init (s: sfields) (ev: reptype t_outBuffer) : sfields :=
  {| sf_stage := 1; sf_inBuff := sf_inBuff s; sf_inSize := sf_inSize s; sf_inPos := vlong 0;
     sf_outBuff := sf_outBuff s; sf_outSize := sf_outSize s; sf_outStart := vlong 0; sf_outEnd := vlong 0;
     sf_lhSize := vlong 0; sf_hostage := Vint (Int.repr 0); sf_nfp := sf_nfp s; sf_expOut := ev;
     sf_hbuf := sf_hbuf s; sf_over := sf_over s; sf_ring := sf_ring s; sf_mem := sf_mem s; sf_held := sf_held s |}.

Definition sv_after_init (sv: sview) : sview :=
  {| sv_fp := FP_hdr nil; sv_pend := nil; sv_ahead := nil; sv_lay := sv_lay sv; sv_dd := None |}.

Lemma hdr_lenok_nil : forall mg, hdr_lenok mg nil.
Proof. intros [|]; unfold hdr_lenok; vm_compute; reflexivity. Qed.

Lemma fh_nil_more : forall mg, exists k0, get_frame_header_m mg nil = FH_more k0.
Proof. intros [|]; eexists; vm_compute; reflexivity. Qed.

Lemma cur_rel_hdr_nil : forall md sel cd, cur_rel md sel cd nil (FP_hdr nil).
Proof. intros. simpl. split; [reflexivity|]. apply hdr_lenok_nil. Qed.

Lemma m_rel_after_init : MF3 -> forall sm sin sout fp cd, bytes_ok sin ->
  (fp = FP_none \/ fp_complete fp = true) ->
  m_rel_cd sm sin sout fp nil cd -> m_rel_cd sm sin sout (FP_hdr nil) nil (next_cd sm fp cd).
Proof.
intros M sm sin sout fp cd Hb Hfp (dsin & fb & recs & Hsin & Hser & Hcd & Hcur & Hout).
pose proof (cur_rel_hdr_nil (sm_md sm) (sm_sel sm)) as Hhdr.
destruct Hfp as [-> | Hc].
- simpl in Hcur. subst fb.
  exists dsin, nil, recs. split; [exact Hsin|]. split; [exact Hser|]. split; [exact Hcd|].
  split; [apply Hhdr|].
  simpl in Hout |- *. exact Hout.
- subst sin. unfold bytes_ok in Hb. apply Forall_app in Hb. destruct Hb as [Hb1 Hb2].
  destruct (mf_frames_done_app M sm cd dsin recs fb fp Hb1 Hb2 Hser Hcd Hcur Hc)
    as (recs' & Hser' & Hfl & _ & Hcd').
  exists (dsin ++ fb), nil, recs'. split; [rewrite app_nil_r; reflexivity|].
  split; [exact Hser'|]. split; [exact Hcd'|]. split; [apply Hhdr|].
  simpl. rewrite app_nil_r in Hout |- *. rewrite !app_nil_r, Hfl. exact Hout.
Qed.

Lemma call_inv_after_init : MF3 -> forall a k sv ipc opc oc dl ev,
  dsa_ok a -> call_inv a k sv ipc opc oc dl -> sf_stage (c3_s k) = 0 -> sv_ahead sv = nil ->
  ev = (a_obf a, (vlong (a_osz a), vlong (a_opos a))) -> ipc = a_ipos a ->
  call_inv a (c3_with_s k (s_after_init (c3_s k) ev)) (sv_after_init sv) ipc opc oc dl.
Proof.
intros M a k sv ipc opc oc dl ev Ha H Hs Hnil Hev Hipc.
assert (Hibs: bytes_ok (a_ibs a)) by (unfold dsa_ok in Ha; tauto).
unfold call_inv in *.
destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & Hcore & H14 & H15 & H16 & H17
  & H18 & H19 & H20 & H21 & H22).
unfold c_core in Hcore. rewrite Hs in Hcore. simpl in Hcore.
destruct Hcore as (Hah & Hcold & Hsz & Hfp & Hpend).
rewrite Hnil in H18, H20.
destruct (fh_nil_more (dp_fmt (c3_par k) =? 1)) as [k0 Hk0].
simpl.
refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj H10
  (conj _ (conj H12 (conj _ (conj _ (conj H15 (conj _ (conj _ (conj _ (conj _
  (conj H20 (conj _ _))))))))))))))))))))).
- right; right; right; right. split; [reflexivity|]. exists nil, k0. split; [reflexivity|exact Hk0].
- unfold c_core. simpl. split; [right; left; auto|]. split; [exact Hcold|]. split; [exact Hsz|].
  split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|].
  exists nil. split; [auto|]. split; [rewrite Zlength_nil; lia|]. split; [constructor|].
  split; [reflexivity|]. split; [reflexivity|]. apply hdr_lenok_nil.
- unfold sv_dd_ok. simpl. intros X; exfalso; unfold zdss_read in X; lia.
- simpl. congruence.
- rewrite Hpend in H17. intros; simpl; auto.
- destruct H18 as [Hd | (cd & Hm & Hcd & _)]; [left; exact Hd | right].
  rewrite Hpend in Hm. eexists. split; [|split].
  + eapply m_rel_after_init; eauto.
    rewrite app_nil_r. unfold bytes_ok in *. apply Forall_app; split; [exact H9|].
    apply Forall_sublist; exact Hibs.
  + exact Hcd.
  + unfold hist_ok. simpl. intros _ _ X; exfalso; apply X; reflexivity.
- intros _ hb Hhb. simpl in Hhb. inversion Hhb; subst hb.
  exists nil, ipc. split; [lia|]. split; [rewrite sublist_nil; reflexivity | lia].
- intros _ _. exact Hev.
- intros X; discriminate X.
Qed.

(* `do { } while (0)` *)
Ltac skip_loop :=
  match goal with |- semax _ ?P _ _ =>
    forward_loop P break: P;
      [solve [apply andp_left2, derives_refl | entailer!] |
       forward; try solve [apply andp_left2, derives_refl | entailer!] | ] end.

(* the model's side of case zdss_init: the first iteration of the model's loop at stage zdss_init is the one of
   z_new_frame at stage zdss_loadHeader (ExStreamFacts.one_iter_init), whose fields are the ones zdss_init writes *)
(* the fields zdss_init writes are those of the model's new frame (stage loadHeader, no header byte, inPos, outStart,
   outEnd and the hostage byte 0); at zdss_loadHeader zrel_end reads nothing else *)
Lemma zrel_new_frame (z: zstate_x) (s: sfields) (ev: reptype t_outBuffer) (fs: fstate) (t: tabs3) :
  zrel z (sf_strip s) fs t -> ExStream.zs_stage XS z = ExStream.ZDSS_init ->
  zrel_end (ExStream.z_new_frame XS z) (sf_strip (s_after_init s ev)) fs t.
Proof.
intros (E1 & R & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & _ & _) Hs.
unfold zrel_end, zrel, ExStream.z_new_frame, ExStream.z_host, ExStream.z_ring, ExStream.z_in, ExStream.z_hbuf,
  ExStream.z_stage.
simpl in *.
unfold ExStream.ZDSS_loadHeader, ExStream.ZDSS_init, ExStream.ZDSS_read in *.
split; [split; [reflexivity|] | ].
- split; [lia|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|]. split; [exact E6|].
  split; [exact E7|]. split; [exact E8|]. split; [exact E9|]. split; [exact E10|].
  split; [| intros X; lia].
  intros _. rewrite sublist_nil. repeat split; try reflexivity; [rewrite Zlength_nil; lia | constructor].
- split; [intros X; lia|]. split; [intros X; lia|].
  repeat split; try reflexivity. left; reflexivity.
Qed.

Lemma init_ex_call (a: dsa) (w: lw) (ev: reptype t_outBuffer) :
  w_smw w = 1 -> sf_stage (c3_s (w_k w)) = 0 -> ex_call a w ->
  ex_call a {| w_smw := 1; w_k := c3_with_s (w_k w) (s_after_init (c3_s (w_k w)) ev);
               w_sv := sv_after_init (w_sv w); w_ipc := w_ipc w; w_opc := w_opc w; w_oc := w_oc w; w_dl := w_dl w |}.
Proof.
intros Hs Hst Hx. apply ex_call_next_mk; [reflexivity|]. intros Hf.
destruct (ex_call_go a w Hx Hs Hf) as (z0 & zi & f & Hl & Hz).
assert (Hzr: zrel zi (w_sx w) (w_fs w) (w_tabs w)) by (destruct Hz as [(_ & _ & _ & H) | (H & _)]; exact H).
assert (Hsi: ExStream.zs_stage XS zi = ExStream.ZDSS_init).
{ destruct Hzr as (E1 & _). unfold w_sx in E1. simpl in E1. rewrite <- E1, Hst. reflexivity. }
exists z0, (ExStream.z_new_frame XS zi), f. split.
- eapply ex_loop_fall; [exact Hl | | |].
  + destruct Hl as (_ & _ & Hzi & _).
    unfold zinv_x. apply zinv_new_frame; [exact Hzi | exact Hsi].
  + unfold one_iter_x, ExStream.one_iter. rewrite Hsi. reflexivity.
  + unfold zpot. rewrite Hsi. simpl. lia.
- exact (zrel_new_frame zi (c3_s (w_k w)) ev (w_fs w) (w_tabs w) Hzr Hsi).
Qed.

(* case zdss_init: the stream fields of a new frame (the model's z_new_frame), then case zdss_loadHeader *)
Lemma seg_init_x_ok : MF3 -> RET3x -> seg_case_x 1 -> seg_case_x 0.
Proof.
intros M _ H1. unfold seg_case_x. intros Espec DENT TABS BR a w R HD HT Ha Hci Hsmw Hle Hst HRn HRr Hso Hent Hun Hx.
destruct (Hle Hsmw) as [Hdl Hah]; [rewrite Hst; unfold zdss_loadHeader; lia|].
change (seq_of_labeled_statement (ds_tail 0))
  with (Ssequence ds_case_init (seq_of_labeled_statement (ds_tail 1))).
pose (ev := (a_obf a, (vlong (a_osz a), vlong (a_opos a)))).
set (w' := {| w_smw := 1; w_k := c3_with_s (w_k w) (s_after_init (c3_s (w_k w)) ev);
              w_sv := sv_after_init (w_sv w); w_ipc := w_ipc w; w_opc := w_opc w; w_oc := w_oc w;
              w_dl := w_dl w |}).
apply semax_seq with (Q := PROPx [] (LOCALx (ds_LI_L a w') (SEPx (ds_LI_S DENT TABS a w')))).
2: { apply (H1 Espec DENT TABS BR a w' R HD HT Ha); auto.
     - apply call_inv_after_init; auto.
     - intros _ _. simpl. auto.
     - intros _ X. discriminate X.
     - apply init_ex_call; auto. }
destruct R as [Rn Rb Rc Rr]. unfold switch_ret_assert, overridePost.
unfold ds_Delta. simplify_func_tycontext. unfold ds_case_init. abbreviate_semax.
unfold ds_LI_S, ds_LI_L, ctx_rep3, ctx_body3, sgroup. Intros.
skip_loop.
forward. forward. forward. forward. forward. forward. forward. forward. forward.
destruct Ha as (_ & _ & _ & Wsho & _ & _ & _ & _ & _ & Hopos & Hosz & _).
assert_PROP (isptr (a_ob a)) as Hob by entailer!.
assert_PROP (field_compatible t_dctx (DOT _expectedOutBuffer) (a_d a)) as Hfc by entailer!.
forward_call (Ews, field_address t_dctx (DOT _expectedOutBuffer) (a_d a), a_sho a, a_outp a,
              a_obf a, a_osz a, a_opos a).
{ rewrite (field_at_data_at Ews t_dctx (DOT _expectedOutBuffer)). simpl nested_field_type. cancel. }
{ (* the output field may be NULL; otherwise it is the base, a pointer *)
  destruct (nbase_cases (a_gv a) (a_obf a)) as [[_ E]|[E _]];
  [unfold a_ob in Hob; rewrite E in Hob; destruct (a_obf a); try contradiction; simpl; auto
  | rewrite E; simpl; auto]. }
change (data_at Ews t_outBuffer ?v (field_address t_dctx (DOT _expectedOutBuffer) ?p))
  with (data_at Ews (nested_field_type t_dctx (DOT _expectedOutBuffer)) v
          (field_address t_dctx (DOT _expectedOutBuffer) p)).
rewrite <- field_at_data_at.
unfold w', ds_LI_L, ds_LI_S, ctx_rep3, ctx_body3, sgroup.
cbn [w_smw w_k w_sv w_ipc w_opc w_oc w_dl c3_s c3_fs c3_tabs c3_stable c3_dict c3_par c3_sp c3_set c3_with_s
     s_after_init sf_stage sf_inBuff sf_inSize sf_inPos sf_outBuff sf_outSize sf_outStart sf_outEnd sf_lhSize
     sf_hostage sf_nfp sf_expOut sf_hbuf sf_over sf_ring sf_mem sf_held].
match goal with |- context [!! ?P && _] => assert P as HP; [|rewrite (prop_true_andp P _ HP)] end.
{ repeat split; auto; rep_lia. }
rewrite Hsmw. subst ev. unfold vlong. entailer!.
(* the allocator's part: the bytes given out do not change (sf_given reads sizes and sf_held only) *)
apply derives_refl.
Qed.


End CM_S3Seg_init_1.
