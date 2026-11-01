(* FS3-bl BODY, stages 3/4: the raw block (case 0) part (S34Defs.v). *)
Require Export Zstd.proof.dec.v3.FS.BL.body.s34.S34Defs.
Require Import Zstd.proof.dec.v3.FS.BL.body.s34.raw.RawAfter.
Require Import Zstd.proof.dec.v3.FS.BL.body.s34.comp.S34Delta.
Local Open Scope logic.

Section CM_Raw_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma s34_raw_ok : s34_case_spec 0.
Proof.
  unfold s34_case_spec.
  intros Espec DENT TABS SR BR' H H0 W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v_bp v pcs st
    H1 H2 H3 H4 H5 Hfp H6 H7 H8 H9 H10 H11 H12. subst.
  pose proof H3 as (Hex & Hexr & Hst & Hfd & Hcold & Hdid & _ & Hds & Hhb & Hwf & Hcs & Hlay).
  pose proof H2 as (Hne & Hhist & Hoz & Hbo & Hbs & Hbd & SHd & SHs & SHk & Hop & Hosz & Hoc & Hcl & Hcb).
  assert (Hsz: 1 <= Zlength c <= ba_expect ba).
  { unfold bl_size_ok in H10. rewrite H12 in H10. destruct H6 as [E | E]; rewrite E in H10; exact H10. }
  subst osz.
  unfold bl_case_pre, bl_R, bl_post. s34c_simplify. abbreviate_semax.
  cbv [s34_ls select_switch select_switch_case select_switch_default]. simpl seq_of_labeled_statement.
  set (o := {| oa_sh := shd; oa_base := ob; oa_N := Zlength oc; oa_c := oc; oa_d := opos; oa_cap := Zlength oc - opos |}).
  set (i := {| iw_sh := shs; iw_base := src; iw_N := Zlength c; iw_c := zbytes c; iw_off := 0; iw_s := c |}).
  assert_PROP (field_compatible (tarray tuchar (Zlength oc)) [] ob) as Fob by entailer!.
  assert_PROP (field_compatible (tarray tuchar (Zlength c)) [] src) as Fsrc by entailer!.
  assert (Hoo: outarr_ok o) by (unfold o; split; [exact SHd |]; cbn; repeat split; lia).
  assert (Hiw: inwin_ok i).
  { assert (Lz: Zlength (zbytes c) = Zlength c) by apply Zlength_map.
    unfold inwin_ok, win_ok, i; cbn [iw_sh iw_N iw_c iw_off iw_s]. rewrite Z.add_0_l, sublist_same by lia.
    repeat split; auto; lia. }
  change (data_at shd (tarray tuchar (Zlength oc)) oc ob) with (data_at (oa_sh o) (tarray tuchar (oa_N o)) (oa_c o) (oa_base o)).
  rewrite (out_split o) by auto. Intros.
  sep_apply (pws_app_fold W (side_W o)).
  forward_call (W ++ side_W o, mid_o o, i).
  { split; [apply mid_ok; auto |]. intros Hc0. cbn [oa_d oa_base mid_o oa_cap] in *.
    rewrite isptr_offset_val_zero by (destruct ob; try contradiction; destruct Fob; auto).
    apply mid_wvp; auto. intros HN. unfold o in HN |- *; cbn in HN |- *. rewrite HN in Hbo, Fob.
    apply buf0_wvp with shd; auto. }
  Intros vret. destruct vret as [r ocm]; cbn [fst snd] in *.
  match goal with Hx: if _ >? _ then _ else _ |- _ => rename Hx into Hraw end.
  match goal with Hx: 0 <= r <= Int64.max_unsigned |- _ => rename Hx into Hr end.
  sep_apply (pws_app_unfold W (side_W o)). Intros.
  exact (@raw_after_ok CMI Espec DENT TABS SR BR' W gv p pr od ba fs ts hb shk shd ob opos oc shs src c v_bp v pcs r ocm
           H1 H4 H6 H12 Hcold Hfp Hex Hexr Hhb SHd Hop Hosz Hcl Hcb Hsz Fob Hr Hraw).
Qed.

End CM_Raw_1.
