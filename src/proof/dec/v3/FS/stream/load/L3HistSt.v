(* FS3 streaming, case zdss_load: stable-mode history of the call (P_load_cont_hist_st, statement in L3Stmts). *)
Require Import Zstd.proof.dec.v3.FS.stream.load.L3Stmts.
Local Open Scope logic.

Section CM_L3HistSt_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma hst_zbytes_byte : forall b j, bytes_ok b -> 0 <= j < Zlength b -> is_byte_val (Znth j (zbytes b)).
Proof.
intros b j Hb Hj. erewrite Znth_map by lia. exists (Znth j b). split; [|reflexivity].
unfold bytes_ok in Hb. rewrite Forall_Znth in Hb. specialize (Hb j Hj). unfold is_byte in Hb. lia.
Qed.

Lemma load_cont_hist_st_ok : P_load_cont_hist_st.
Proof.
intros a k0 sv ipc opc oc dl E L Hok Hstb.
destruct Hok as (Ha & Hinv & Hst & _).
assert (Hop0: 0 <= a_opos a) by (destruct Ha as (_&_&_&_&_&_&_&_&_&Ho&_); lia).
destruct Hinv as (Hipc & Hopc & Hoc & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcore & _ & Hst1 & _).
specialize (Hst1 Hstb). rewrite Hstb in Hcore.
set (sout := ss_out (dc_ss (a_st a)) ++ dl) in *.
assert (Hls: Zlength sout = opc).
{ apply (f_equal (@Zlength val)) in Hst1. rewrite Zlength_map, Zlength_sublist in Hst1 by lia. lia. }
destruct Hcore as (_&_&_&Hcs). rewrite Hst in Hcs. simpl in Hcs. destruct Hcs as (_&Hcf&Hring&_).
unfold cont_hist. destruct sv as [fp pend ahead lay dd]; cbn [sv_fp sv_pend sv_ahead sv_lay sv_dd] in *.
destruct fp as [|hb|hdr got|hdr z]; simpl fp_unit; try exact I.
unfold zp_set_got, zp_with; cbn [zp_ph].
destruct (zp_ph z) eqn:Hph; try exact I. intros _ Hcap.
unfold c_frame in Hcf. destruct Hcf as (_&_&_&Hlf&Hld&Hf).
unfold o_st in *; cbn [oa_base oa_d oa_cap oa_c is_skip sv_fp] in *.
unfold lmove. rewrite (proj2 (Z.leb_gt _ 0) Hcap).
destruct lay as [|eb ec gp|b pe od|b ps pe e].
- split; [intros kk Hk; simpl in Hk; lia | left; exact I].
- cbn [lay_dd] in Hld. destruct Hld as (x & Edd & -> & _ & Hbx & _).
  split; [|left; exact I].
  intros kk Hk. cbn [ext_of_dict ext_len] in Hk. rewrite Zlength_map in Hk.
  unfold chist, ext_of_dict. rewrite (proj2 (Z.leb_gt kk (opc - opc))) by lia.
  rewrite Zlength_map. apply hst_zbytes_byte; auto; lia.
- exact I.
- destruct Hring as (_&_&_&os&oe&_&_&_&Hr). destruct Hr as (_&_&_&ob'&osz'&_&Hl).
  destruct Hl as (_&Hne&Hpe&Hps&Hsub). rewrite Hpe, Hls, Z.eqb_refl.
  destruct Hlf as (_&_&Hpsle&_).
  destruct Hf as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&Hbo&_).
  cbn [fp_content] in Hps, Hsub.
  assert (Hbs: forall j, ps <= j < opc -> is_byte_val (Znth j oc)).
  { intros j Hj.
    assert (Ez: Znth j oc = Znth j (sublist 0 opc oc)) by (rewrite Znth_sublist by lia; f_equal; lia).
    rewrite Ez, Hst1, Znth_map by lia.
    exists (Znth j sout). split; [|reflexivity].
    assert (Hz2: Znth (j - ps) (sublist ps pe sout) = Znth j sout)
      by (rewrite Znth_sublist by lia; f_equal; lia).
    rewrite <- Hz2, Hsub.
    apply (Forall_Znth (zp_out z) is_byte); [exact Hbo|].
    assert (Zlength (sublist ps pe sout) = pe - ps) by (rewrite Zlength_sublist by lia; lia).
    rewrite Hsub in H. lia. }
  split; [|left; destruct e; simpl; auto; simpl in Hne; contradiction].
  intros kk Hk. unfold chist. destruct (kk <=? opc - ps) eqn:Ek.
  + apply Z.leb_le in Ek. apply Hbs. lia.
  + apply Z.leb_gt in Ek. destruct e as [|e1 elen|sh eb en ec e1 elen]; cbn [ext_len] in Hk; try lia; try (simpl in Hne; contradiction).
    * cbn [lay_dd] in Hld. destruct Hld as (-> & -> & -> & -> & gp & x & Edd & -> & _ & Hbx & _).
      rewrite Zlength_map in Hk |- *. apply hst_zbytes_byte; auto; lia.
Qed.

End CM_L3HistSt_1.
