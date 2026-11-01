(* FS3 streaming, case zdss_loadHeader, G4: the pure facts G4 takes from the representation. *)
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3Stmts Zstd.proof.dec.v3.FS.stream.lh.LH3G42_dict.
Require Import Coq.Logic.Classical.
Local Open Scope logic.

Section CM_LH3G42_sep_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma g4_fold_in {A: Type} (f: A -> mpred) (l: list A) (e: A) :
  In e l -> fold_right sepcon emp (map f l) |-- f e * TT.
Proof.
induction l as [|e0 l IH]; intros Hin; [ contradiction | ].
cbn [map fold_right]. destruct Hin as [<- | Hin].
- cancel.
- sep_apply (IH Hin). cancel.
Qed.

Lemma g4_struct_conflict : forall x buf x' buf', dx_q x = dx_q x' -> ddict_struct x buf * ddict_struct x' buf' |-- FF.
Proof.
intros x buf x' buf' Hq. unfold ddict_struct. Intros. rewrite Hq.
sep_apply (field_at_conflict Ews (Tstruct _ZSTD_DDict_s noattr) (DOT _cMem) (dx_q x') (cmem_v (dx_mem x)) (cmem_v (dx_mem x'))).
all: try solve [ apply readable_nonidentity; auto | simpl; lia ].
rewrite FF_sepcon. apply derives_refl.
Qed.

Lemma g4_dd_res_struct : forall DENT gv sh q dd,
  ddict_res (DD3x DENT) gv sh q dd |-- ddict_struct (dd_x q dd) (dd_buf dd) * TT.
Proof.
intros. unfold ddict_res, DD3x, DD3_of, ddict_rep_at.
eapply derives_trans; [ apply sepcon_derives; [ apply andp_left1, derives_refl | apply derives_refl ] | ].
cancel.
Qed.

Lemma g4_par : forall DENT TABS a w, lh_st DENT TABS a w |-- !! par_ok (c3_par (w_k w)).
Proof.
intros. unfold lh_st, ds_LI_S, ctx_rep3, ctx_body3, fgroup3. go_lowerx. Intros. apply prop_right. tauto.
Qed.

Lemma g4_sp : forall DENT TABS a w,
  lh_st DENT TABS a w |-- !! ((c3_set (w_k w) <> nil -> c3_sp (w_k w) <> nullval) /\
                              (c3_set (w_k w) = nil -> c3_sp (w_k w) = nullval)).
Proof.
intros. unfold lh_st, ds_LI_S, ctx_rep3, ctx_body3, hset_rep.
destruct (eq_dec (c3_sp (w_k w)) nullval).
- go_lowerx. Intros. apply prop_right. split; [ intros Hn; contradiction | auto ].
- go_lowerx. Intros tp tbl. apply prop_right. split; [ auto | intros Hn; tauto ].
Qed.

Lemma g4_local_ff : forall DENT TABS a w x buf dd,
  let d := c3_dict (w_k w) in
  df_lx d = Some (x, buf) -> df_local d <> nullval -> In (df_local d, dd) (dc_set (a_st a)) ->
  cur_ddict (dc_dict (a_st a)) <> Some (df_local d) ->
  lh_st DENT TABS a w |-- FF.
Proof.
intros DENT TABS a w x buf dd d Hlx Hl Hin Hcur.
unfold lh_st, ds_LI_S, ctx_rep3, ctx_body3, dgroup, local_rep. fold d.
rewrite Hlx. destruct (eq_dec (df_local d) nullval) as [E|_]; [ contradiction | ].
unfold set_res. go_lowerx. Intros.
sep_apply (g4_fold_in (fun e => match cur_ddict (dc_dict (a_st a)) with
                                | Some q => if Val.eq (fst e) q then emp else ddict_res (DD3x DENT) (a_gv a) Ews (fst e) (snd e)
                                | None => ddict_res (DD3x DENT) (a_gv a) Ews (fst e) (snd e)
                                end) _ _ Hin).
cbn [fst snd].
assert (Hm: match cur_ddict (dc_dict (a_st a)) with
            | Some q => if Val.eq (df_local d) q then emp else ddict_res (DD3x DENT) (a_gv a) Ews (df_local d) dd
            | None => ddict_res (DD3x DENT) (a_gv a) Ews (df_local d) dd
            end = ddict_res (DD3x DENT) (a_gv a) Ews (df_local d) dd).
{ destruct (cur_ddict (dc_dict (a_st a))) as [q|]; auto.
  destruct (Val.eq (df_local d) q) as [E|_]; [ subst q; contradiction | auto ]. }
rewrite Hm. sep_apply (g4_dd_res_struct DENT (a_gv a) Ews (df_local d) dd).
unfold ddict_rep_at.
assert (Hqq: dx_q x = dx_q (dd_x (df_local d) dd)) by (cbn [dd_x dx_q]; congruence).
sep_apply (g4_struct_conflict x buf (dd_x (df_local d) dd) (dd_buf dd) Hqq).
rewrite !FF_sepcon. apply FF_left.
Qed.

Lemma g4_local : forall DENT TABS a w, lh_st DENT TABS a w |-- !! g4_local_ok (a_st a) (c3_dict (w_k w)).
Proof.
intros. destruct (classic (g4_local_ok (a_st a) (c3_dict (w_k w)))) as [H|H].
- apply prop_right. exact H.
- unfold g4_local_ok in H.
  apply not_all_ex_not in H. destruct H as (x & H). apply not_all_ex_not in H. destruct H as (buf & H).
  apply not_all_ex_not in H. destruct H as (dd & H).
  apply imply_to_and in H. destruct H as (H1 & H). apply imply_to_and in H. destruct H as (H2 & H).
  apply imply_to_and in H. destruct H as (H3 & H4).
  eapply derives_trans; [ apply (g4_local_ff DENT TABS a w x buf dd); auto | ]. apply FF_left.
Qed.

Lemma g4_sizes : forall DENT TABS a w,
  lh_st DENT TABS a w |-- !! (0 <= sf_inSize (c3_s (w_k w)) /\ 0 <= sf_outSize (c3_s (w_k w)))%Z.
Proof.
intros. unfold lh_st, ds_LI_S, ctx_rep3, ctx_body3, sgroup. go_lowerx. Intros. apply prop_right. tauto.
Qed.

(* R1: dd_pre's facts of the frame's DDict (ddict_struct), from the representation *)
Lemma g4_ddres_facts : forall DENT gv sh q dd,
  ddict_res (DD3x DENT) gv sh q dd |-- !! (bytes_ok (dd_bytes dd) /\ (dd_xref dd = None -> 0 < Zlength (dd_bytes dd))) && TT.
Proof.
intros. sep_apply (g4_dd_res_struct DENT gv sh q dd). unfold ddict_struct. Intros.
unfold dd_x, ddx_copied in *. cbn [dx_bytes dx_ref dx_q dx_ld dx_raw] in *.
assert (Hf: bytes_ok (dd_bytes dd) /\ (dd_xref dd = None -> 0 < Zlength (dd_bytes dd))).
{ split; [ tauto | ]. intros E. rewrite E in *. tauto. }
first [ apply prop_right; exact Hf | apply andp_right; [ apply prop_right; exact Hf | apply TT_right ] ].
Qed.

Lemma g4_ddb_caller : forall DENT TABS a w q dd, set_cur_ok (a_st a) -> dd_caller (a_st a) q dd ->
  lh_st DENT TABS a w |-- !! (bytes_ok (dd_bytes dd) /\ (dd_xref dd = None -> 0 < Zlength (dd_bytes dd))).
Proof.
intros DENT TABS a w q dd Hsco Hc.
unfold lh_st, ds_LI_S. go_lowerx. Intros.
destruct Hc as [Hin | (dr & Ed & Hs)].
- unfold set_res.
  sep_apply (g4_fold_in (fun e => match cur_ddict (dc_dict (a_st a)) with
                                  | Some q => if Val.eq (fst e) q then emp else ddict_res (DD3x DENT) (a_gv a) Ews (fst e) (snd e)
                                  | None => ddict_res (DD3x DENT) (a_gv a) Ews (fst e) (snd e)
                                  end) _ _ Hin).
  cbn [fst snd].
  destruct (cur_ddict (dc_dict (a_st a))) as [q'|] eqn:Ec.
  + destruct (Val.eq q q') as [<-|Hne].
    * unfold cur_ddict in Ec. destruct (dc_dict (a_st a)) as [dr|] eqn:Ed; [ | discriminate ].
      destruct (dr_src dr) as [ | | q0 dd0] eqn:Es; try discriminate. inversion Ec; subst q0.
      pose proof (Hsco dr q dd0 dd Ed Es Hin) as ->.
      unfold dict_res. rewrite Es. sep_apply (g4_ddres_facts DENT (a_gv a) Ews q dd0). Intros. apply prop_right. auto.
    * sep_apply (g4_ddres_facts DENT (a_gv a) Ews q dd). Intros. apply prop_right. auto.
  + sep_apply (g4_ddres_facts DENT (a_gv a) Ews q dd). Intros. apply prop_right. auto.
- unfold dict_res. rewrite Ed, Hs. sep_apply (g4_ddres_facts DENT (a_gv a) Ews q dd). Intros. apply prop_right. auto.
Qed.

Lemma g4_ddb : forall DENT TABS a w x buf, set_cur_ok (a_st a) -> dx_q x <> nullval -> dd_src (a_st a) (w_k w) x buf ->
  lh_st DENT TABS a w |-- !! (bytes_ok (dx_bytes x) /\ (ddx_copied x = true -> 0 < Zlength (dx_bytes x))).
Proof.
intros DENT TABS a w x buf Hsco Hq [(Hl & _ & _ & Hlx) | (dd & Hc & Ex & Eb)].
- unfold lh_st, ds_LI_S, ctx_rep3, ctx_body3, dgroup, local_rep. rewrite Hlx, Hl.
  destruct (eq_dec (dx_q x) nullval) as [E|_]; [ contradiction | ].
  unfold ddict_rep_at, ddict_struct. go_lowerx. Intros. apply prop_right. tauto.
- eapply derives_trans; [ apply (g4_ddb_caller DENT TABS a w (dx_q x) dd Hsco Hc) | ].
  apply prop_derives. rewrite Ex. cbn [dd_x dx_bytes ddx_copied dx_ref].
  intros (H1 & H2). split; [ exact H1 | ]. unfold ddx_copied, dd_x; cbn [dx_ref].
  destruct (dd_xref dd); [ discriminate | auto ].
Qed.

End CM_LH3G42_sep_1.
