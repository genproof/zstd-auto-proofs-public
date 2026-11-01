(* FS3 streaming, case zdss_read: the generic stable-mode unit step, copied from
   load/L3StGen.v, on this file's helpers. *)
Require Export Zstd.proof.dec.v3.FS.stream.read.R3Step.
Local Open Scope logic.

Section CM_R3StGen_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* the stable layout rule of c_ring *)
Definition sring (ob: val) (osz: Z) (sout out: list Z) (l: hlay) : Prop :=
  match l with
  | HL_none => out = nil
  | HL_dict _ _ _ => out = nil
  | HL_stuck base pe _ => base = ob /\ out = nil /\ pe = Zlength sout /\ pe = osz
  | HL_seg base ps pe e =>
      base = ob /\ (match e with ExtIn _ _ => False | _ => True end) /\
      pe = Zlength sout /\ ps = pe - Zlength out /\ sublist ps pe sout = out
  end.

Lemma sring_move : forall ob osz sout out l opc,
  sring ob osz sout out l -> Zlength sout = opc -> opc <= osz ->
  sring ob osz sout out (lmove l ob opc (osz - opc)).
Proof.
intros ob osz sout out l opc H Hl Ho. unfold lmove.
destruct (osz - opc <=? 0) eqn:E; [exact H|]. apply Z.leb_gt in E.
destruct l as [|eb ec gp|b pe od|b ps pe e]; simpl in H |- *.
- subst out. rewrite sublist_nil. repeat split; auto; rewrite ?Zlength_nil; lia.
- subst out. rewrite sublist_nil. repeat split; auto; rewrite ?Zlength_nil; lia.
- lia.
- destruct H as (->&He&->&->&Hs). rewrite (proj2 (Z.eqb_eq _ _) Hl). simpl. auto.
Qed.

Lemma sring_write : forall ob osz sout out l opc cnt,
  sring ob osz sout out l -> Zlength sout = opc -> opc + Zlength cnt <= osz ->
  (forall b ps pe e, l = HL_seg b ps pe e -> 0 <= ps) ->
  sring ob osz (sout ++ cnt) (out ++ cnt) (lwrite (lmove l ob opc (osz - opc)) ob opc (Zlength cnt)).
Proof.
intros ob osz sout out l opc cnt H Hl Ho Hps. pose proof (Zlength_nonneg cnt).
unfold lmove. destruct (osz - opc <=? 0) eqn:E.
- apply Z.leb_le in E. assert (Hc: cnt = nil) by (apply Zlength_nil_inv; lia). subst cnt.
  rewrite !app_nil_r. rewrite Zlength_nil in *.
  destruct l as [|eb ec gp|b pe od|b ps pe e]; simpl in H |- *; rewrite ?Z.add_0_r.
  + subst out. repeat split; auto; lia.
  + subst out. repeat split; auto; lia.
  + destruct H as (->&->&->&->). repeat split; auto; lia.
  + destruct H as (->&He&->&Hps'&Hs). rewrite <- Hl. auto 6.
- apply Z.leb_gt in E.
  destruct l as [|eb ec gp|b pe od|b ps pe e]; simpl in H |- *.
  + subst out. simpl. rewrite Zlength_app. repeat split; auto; try lia.
    rewrite <- Hl. pose proof (Zlength_nonneg sout). rewrite sublist_app2 by lia. rewrite Z.sub_diag.
    replace (Zlength sout + Zlength cnt - Zlength sout) with (Zlength cnt) by lia.
    apply sublist_same; lia.
  + subst out. simpl. rewrite Zlength_app. repeat split; auto; try lia.
    rewrite <- Hl. pose proof (Zlength_nonneg sout). rewrite sublist_app2 by lia. rewrite Z.sub_diag.
    replace (Zlength sout + Zlength cnt - Zlength sout) with (Zlength cnt) by lia.
    apply sublist_same; lia.
  + lia.
  + destruct H as (->&He&->&->&Hs). rewrite (proj2 (Z.eqb_eq _ _) Hl). simpl.
    specialize (Hps _ _ _ _ eq_refl).
    rewrite !Zlength_app. repeat split; auto; try lia.
    rewrite <- Hl. rewrite sublist_app_tail by (pose proof (Zlength_nonneg out); lia).
    rewrite Hs. reflexivity.
Qed.

(* the stable ring after a unit of a Zstandard frame written at opc = |sout| *)
Lemma c_ring_stable_zunit : forall sh ob osz oc sout s hdr z z' l cnt opc fs,
  c_ring true (Some (ob, osz)) sout s (FP_zstd hdr z) nil l -> lay_fields fs l ->
  Zlength sout = opc -> opc + Zlength cnt <= osz ->
  zp_bsm z' = zp_bsm z -> zp_out z' = zp_out z ++ cnt ->
  (match zp_ph z with ZP_body _ => True | _ => cnt = nil end) ->
  c_ring true (Some (ob, osz)) (sout ++ cnt) s (FP_zstd hdr z') nil
    (lnext (FP_zstd hdr z) l (oa_stable sh ob osz (FP_zstd hdr z) oc opc) (Zlength cnt)).
Proof.
intros sh ob osz oc sout s hdr z z' l cnt opc fs Hr Hlf Hl Ho Hh Hout Hc.
destruct Hr as (Hi1&Hi2&Hi3&ostart&oend&Hos&Hoe&Hoo&Hst).
destruct Hst as (Ho0&Ho1&_&ob'&osz'&Hob&Hly). inversion Hob; subst ob' osz'.
assert (Hps: forall b ps pe e, l = HL_seg b ps pe e -> 0 <= ps)
  by (intros; subst l; destruct Hlf as (_&_&?&_); lia).
pose proof (Zlength_nonneg cnt).
split; [auto|]. split; [auto|]. split; [cbn [fp_bsm] in *; rewrite Hh; auto|].
exists ostart, oend. do 3 (split; [auto|]). do 3 (split; [auto|]). exists ob, osz. split; [auto|].
refine (_ : sring ob osz (sout ++ cnt) (fp_content (FP_zstd hdr z')) _).
change (sring ob osz sout (fp_content (FP_zstd hdr z)) l) in Hly.
cbn [fp_content] in *. rewrite Hout.
unfold lnext, oa_stable; cbn [oa_base oa_d oa_cap is_skip].
destruct (zp_ph z).
- subst cnt. rewrite !app_nil_r. apply sring_move; auto. rewrite Zlength_nil in Ho; lia.
- apply sring_write; auto.
- subst cnt. rewrite !app_nil_r. apply sring_move; auto. rewrite Zlength_nil in Ho; lia.
- subst cnt. rewrite !app_nil_r. apply sring_move; auto. rewrite Zlength_nil in Ho; lia.
Qed.

Lemma c_ring_stable_eq : forall obuf sout s s' fp fp' pend l,
  c_ring true obuf sout s fp pend l ->
  sf_inBuff s' = sf_inBuff s -> sf_inSize s' = sf_inSize s -> sf_outStart s' = sf_outStart s ->
  sf_outEnd s' = sf_outEnd s -> fp_bsm fp' = fp_bsm fp -> fp_content fp' = fp_content fp ->
  c_ring true obuf sout s' fp' pend l.
Proof.
intros obuf sout s s' fp fp' pend l H H1 H2 H3 H4 H5 H6. unfold c_ring in *.
rewrite H1, H2, H3, H4, H5, H6. exact H.
Qed.

Lemma c_core_read_stable : forall obuf sout k sv,
  sf_stage (c3_s k) = zdss_read -> sf_hostage (c3_s k) = Vint (Int.repr 0) -> sv_ahead sv = nil ->
  sv_pend sv = nil ->
  sf_inSize (c3_s k) + sf_outSize (c3_s k) <= 2 ^ 32 ->
  sf_inPos (c3_s k) = vlong 0 -> sf_outStart (c3_s k) = sf_outEnd (c3_s k) ->
  c_frame (c3_fs k) (c3_tabs k) (sv_fp sv) (sv_lay sv) (sv_dd sv) ->
  c_ring true obuf sout (c3_s k) (sv_fp sv) nil (sv_lay sv) ->
  (fp_rawbody (sv_fp sv) = true \/ fp_loaded (sv_fp sv) = nil \/ fp_complete (sv_fp sv) = true) ->
  (match sv_fp sv with FP_skip _ got => got = 0 \/ fp_complete (sv_fp sv) = true | _ => True end) ->
  c_core true obuf sout k sv.
Proof.
intros obuf sout k sv Hs Hh Ha Hp Hsz Hip Hoo Hcf Hr Hraw Hsk.
unfold c_core. rewrite Hp.
split; [right; left; auto|].
split; [destruct Hcf as (_&Hc&_); exact Hc|].
split; [exact Hsz|].
rewrite Hs. unfold zdss_read, zdss_init, zdss_loadHeader, zdss_load, zdss_flush. simpl.
split; [left; reflexivity|]. split; [exact Hcf|]. split; [exact Hr|].
split; [intros _; discriminate|]. split; [intros; discriminate|].
split; [intros _; split; [exact Hip|]; split; [tauto|exact Hsk]|].
intros _; auto.
Qed.

(* the model after a unit of a Zstandard frame (generic: sin, sout are the bytes read / delivered before) *)
Lemma model_zunit3 : MF3 -> forall sm cd sin sout hdr z H u cnt ts' fs' tabs' l' dd',
  bytes_ok sin -> bytes_ok u -> dm_ok (zp_dm z) -> zhist_ok sm z H ->
  m_rel_cd sm sin sout (FP_zstd hdr z) nil cd ->
  (match zp_ph z with
   | ZP_body bh => bp_type (block_props_of bh) = 0 \/ zp_got z = nil
   | _ => zp_got z = nil
   end) ->
  unit_ok (FP_zstd hdr z) (Zlength u) -> cnt_safe z u cnt ts' -> cnt_ok z H u cnt ts' -> cont_checks z u cnt ->
  c_frame fs' tabs' (FP_zstd hdr (zstep z u cnt ts')) l' dd' ->
  dead sm (sin ++ u) \/ m_rel_cd sm (sin ++ u) (sout ++ cnt) (FP_zstd hdr (zstep z u cnt ts')) nil cd.
Proof.
intros M sm cd sin sout hdr z H u cnt ts' fs' tabs' l' dd' Hbs Hbu Hdm Hzh Hm Hgot Hun Hsafe Hok Hchk Hcf'.
destruct Hm as (dsin&fb&recs&Hsin&Hser&Hcd&Hcur&Hout). subst sin.
apply Forall_app in Hbs. destruct Hbs as [Hbd Hbf].
assert (Hbc: forall bh c, zp_ph (zstep z u cnt ts') = ZP_body bh -> cblock_size bh = Some c -> c <= zp_bsm z).
{ intros bh c E Ec. destruct (c_frame_body _ _ _ _ _ _ _ Hcf' E) as (c'&Ec'&Hc'&_).
  rewrite zstep_bsm in Hc'. rewrite Ec in Ec'. injection Ec' as <-. lia. }
destruct (mf_zunit_step M sm cd fb hdr z H u cnt ts' Hbf Hdm Hzh Hbc Hcur Hgot Hun Hbu Hsafe Hok Hchk) as [[Hc _]|Hfd].
- right. exists dsin, (fb ++ u), recs. split; [rewrite app_assoc; reflexivity|]. split; [exact Hser|].
  split; [exact Hcd|]. split; [exact Hc|].
  cbn [fp_content] in *. rewrite (zstep_out _ _ _ _ Hsafe). rewrite app_nil_r in *. rewrite Hout, app_assoc.
  reflexivity.
- left. rewrite <- app_assoc. exact (mf_dead_of_fdead M sm cd dsin recs (fb ++ u) Hbd Hser Hcd Hfd).
Qed.

End CM_R3StGen_1.
