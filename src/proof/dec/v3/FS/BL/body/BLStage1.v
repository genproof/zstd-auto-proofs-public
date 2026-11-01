(* FS3-bl BODY: stage 1 (ZSTDds_decodeFrameHeader): rest of the header into headerBuffer, ZSTD_decodeFrameHeader.  Statement: BLCase.bl_case_spec. *)
Require Export Zstd.proof.dec.v3.FS.BL.body.BLCase.
Require Import Zstd.proof.dec.v3.FS.BL.body.s1.S1Defs.
Require Import Zstd.proof.dec.v3.FS.BL.body.s1.S1Loop.
Require Import Zstd.proof.dec.v3.FS.BL.body.s1.S1Tail.
Local Open Scope logic.

Section CM_BLStage1_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma bl_stage1_ok : bl_case_spec (fun v => bv_stage v = BHdrRest) 1.
Proof.
  intros Espec DENT TABS SR BR' HD HT W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v_bp v pcs st
    Hpr Hpre Hci Hmr Hmd Hfp Hst Hstz Hpcs Hpcsr Hsz Hlay.
  assert (Hh: s1_hyps pr W od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v pcs)
    by exact (conj Hpr (conj Hpre (conj Hci (conj Hmr (conj Hmd (conj Hst (conj Hpcs (conj Hpcsr (conj Hsz (conj Hlay Hfp)))))))))).
  unfold bl_case_pre. rewrite s1_cmd_eq. apply seq_assoc1.
  apply semax_seq with
    (s1_pre_loop DENT TABS W gv p pr od (bl_fs1 fs ob osz opos pcs (Zlength c)) ts
       (s1_hb hb c (starting_len (md_magicless (dmode_of pr))) (bv_hs v)) shk shd ob osz oc shs src c v_bp).
  2: { apply seq_assoc1.
       apply semax_seq with
         (s1_Q DENT TABS W gv p pr od (bl_fs1 fs ob osz opos pcs (Zlength c)) (pcs + Zlength c) (bv_hdr v ++ c) ts
            (s1_hb hb c (starting_len (md_magicless (dmode_of pr))) (bv_hs v)) shk shd ob osz oc shs src c v_bp).
       - exact (@s1_loop_ok CMI Espec DENT TABS SR BR' HD HT W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c
                  v_bp v pcs Hh).
       - exact (@s1_tail_ok CMI Espec DENT TABS SR BR' HD HT W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c
                  v_bp v pcs Hh). }
  unfold s1_pre_loop, bl_R, bl_post. s1_delta. unfold s1_memcpy. abbreviate_semax.
  pose proof Hci as Hci0.
  destruct Hci as (Hexp & Her & Hstg & Hifd & Hcold & Hdid & Hpcs' & Hds & Hhb & Hwf & Hcs & Hly).
  cbv [bl_cstage] in Hcs; rewrite Hst in Hcs; destruct Hcs as (Hhl & Hhok & Hhb5 & Hhs & Hfhs & He & Hnsk0).
  unfold bl_size_ok in Hsz; rewrite Hst in Hsz.
  destruct Hpre as (Hne & Hho & Hoz & Hbo & Hbs & Hbd & Hwd & Hrs & Hrk & Hop & Hosz & Hoc & Hcl & Hcb).
  destruct (s1_fs1_eq fs ob osz opos pcs (Zlength c)) as (E1 & E2 & E3 & E4 & E5 & E6 & E7).
  assert (Hn: 0 < Zlength c) by lia.
  destruct (s1_hsize_rng (dmode_of pr) v Hhl Hhs ltac:(lia)) as (Hsl & Hhs18).
  set (mg := md_magicless (dmode_of pr)) in *. set (sl := starting_len mg) in *.
  sep_apply (s1_fcore3_split p (bl_fs1 fs ob osz opos pcs (Zlength c)) pr). Intros.
  rewrite E1, Hfhs.
  forward.
  rewrite <- s1_hb_eq.
  set (q := field_address t_dctx (DOT _headerBuffer) p).
  assert_PROP (field_compatible (tarray tuchar 18) [] q) as Hfc by entailer!.
  rewrite (s1_hb_before hb sl (bv_hs v) q) by (auto; lia).
  sep_apply (data_at_data_at_ Ews (tarray tuchar (bv_hs v - sl)) (sublist sl (bv_hs v) hb) (offset_val sl q)).
  replace (bv_hs v - sl) with (Zlength c) by lia.
  forward_call (shs, Ews, src, offset_val sl q, existT (fun t => reptype t) (tarray tuchar (Zlength c)) (zbytes c)).
  { entailer!. simpl. unfold q in *. unfold field_address in *.
    destruct (field_compatible_dec t_dctx (DOT _headerBuffer) p) as [Hf | Hf];
      [| destruct Hfc as (Hfc & _); contradiction Hfc].
    rewrite offset_offset_val. replace (bv_hs v - Zlength c) with (starting_len mg) by lia.
    rewrite Z.mul_1_l, Z.max_r by lia. reflexivity. }
  { memcpy_side. }
  cbn [projT1 projT2].
  sep_apply (s1_hb_after' hb c sl (bv_hs v) q Hhb ltac:(lia) ltac:(lia) ltac:(lia) Hfc).
  sep_apply (s1_fcore3_join_hs p (bl_fs1 fs ob osz opos pcs (Zlength c)) pr (vlong (bv_hs v)) Hpr
               ltac:(rewrite E1; exact Hfhs)).
  entailer!.
Qed.

End CM_BLStage1_1.
