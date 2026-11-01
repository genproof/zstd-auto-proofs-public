(* ZSTD_decompressStream, case zdss_loadHeader with the exact claim: G1, the break after a complete load of the header bytes: the loop invariant with ex_call (the model's LNext). *)
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3XDefs.
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3G1.
Local Open Scope logic.

Section CM_LH3G1X_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.

(* adding a proved proposition at the end of a PROP list *)
Lemma g1x_PROP_app : forall (P: Prop) Ps QR, P -> PROPx Ps QR |-- PROPx (Ps ++ [P]) QR.
Proof.
intros P Ps QR HP. unfold PROPx. apply andp_derives; [ | apply derives_refl ].
intro rho. simpl. apply prop_derives. clear rho QR. induction Ps as [|p Ps IH]; cbn; tauto.
Qed.

(* the model's slice is VST's sublist *)
Lemma g1x_slice : forall (l: list Z) i k, 0 <= i -> 0 <= k -> slice l i k = sublist i (i + k) l.
Proof.
intros l i k Hi Hk. unfold slice, sublist. rewrite skipn_firstn_comm.
f_equal. lia.
Qed.

(* from the configuration of a new context the format is zstd1 (not magicless) *)
Lemma g1x_mg : forall st k, base_call st k -> fresh_cfg st -> lh_mg k = false.
Proof.
intros st k Hb Hf. destruct Hb as (_ & Hpar & _). destruct Hf as (_ & Hp & _).
unfold lh_mg. rewrite Hpar, Hp. reflexivity.
Qed.

(* the exact conjunct of the loop state after the break: the model's st_load_header loads the same m bytes and goes
   on (LNext) to the state whose header bytes the new context holds *)
Lemma g1x_call : MF3 ->
  forall (a: dsa) (w: lw) (hb: list Z) (kk: Z) (v: reptype t_fh) (tbl: list val) (d1: dfields) (did1: val),
    lh_ctx a w hb -> lhx_entry a w -> lhA_sel (w_k w) hb kk v tbl d1 did1 ->
    get_frame_header_m (lh_mg (w_k w)) hb = FH_more kk -> kk - Zlength hb <= a_isz a - w_ipc w ->
    ex_call a (g1_w a w hb kk v d1 did1).
Proof.
intros MFh a w hb kk v tbl d1 did1 Hctx Hlhx Hsel Hk Hkk.
pose proof Hctx as (Ha & Hstart & Hci & Hsmw & Hle & He & Hfp & Hdl & Hah & Hpend & Hentry & Hunt).
apply ex_call_next_mk; [ exact Hsmw | ].
intros Hf.
destruct (lhx_view a w hb He Hlhx Hf) as (z0 & zi & f & Hl & Hz & Hst & Hhb & Hone).
assert (Hmg: lh_mg (w_k w) = false).
{ destruct He as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hb0 & _). exact (g1x_mg _ _ Hb0 Hf). }
pose proof (mf_hdr_more_size MFh _ hb kk Hk) as Hlt.
pose proof (g1_more_rng _ hb kk Hk) as Hk18.
rewrite Hmg in Hk. unfold get_frame_header_m in Hk. cbn [negb] in Hk.
unfold ExStream.st_load_header in Hone. rewrite Hhb, Hk in Hone. cbv zeta in Hone.
assert (Hib: Zlength (a_ibs a) = a_isz a /\ bytes_ok (a_ibs a) /\ 0 <= a_ipos a <= a_isz a)
  by (unfold dsa_ok in Ha; tauto).
destruct Hib as (Hibl & Hibb & Hip0).
pose proof He as (Hs & Hlh & H18 & Hbo & Hsub & Hhost & HinPos & Hos & Hoe & Hipc' & _).
set (m := kk - Zlength hb) in *.
set (ip := w_ipc w - a_ipos a) in *.
assert (Hxl: Zlength (a_xin a) = a_isz a - a_ipos a) by (unfold a_xin; rewrite Zlength_sublist; lia).
rewrite Hxl in Hone.
destruct (m >? a_isz a - a_ipos a - ip) eqn:E; [ apply Z.gtb_lt in E; lia | ].
rewrite g1x_slice in Hone by lia.
assert (Hu: sublist ip (ip + m) (a_xin a) = sublist (w_ipc w) (w_ipc w + m) (a_ibs a)).
{ unfold a_xin. rewrite sublist_sublist by lia. f_equal; lia. }
rewrite Hu in Hone.
assert (Hxb: bytes_ok (a_xin a)) by (unfold a_xin, bytes_ok in *; apply Forall_sublist; auto).
assert (Hroom: Zlength (@nil Z) <= a_xroom a).
{ destruct Ha as (_&_&_&_&_&_&_&_&_&Hop&_). unfold a_xroom; rewrite Zlength_nil; lia. }
destruct (ex_loop_next a z0 zi f ip nil _ _ _ Hxb ltac:(lia) Hroom Hl Hone) as (f1 & Hl1 & _).
unfold g1_w; cbv zeta; cbn [w_smw w_k w_ipc w_dl]. fold m.
exists z0, (ExStream.z_hbuf XS zi (hb ++ sublist (w_ipc w) (w_ipc w + m) (a_ibs a))), f1.
split; [ replace (w_ipc w + m - a_ipos a) with (ip + m) by lia; exact Hl1 | ].
clear Hone Hl Hl1 Hctx Hci Hentry Hunt Hlhx Hle Hstart.
destruct Hz as (Hz1 & Hz2 & Hz3 & Hz4 & Hz5 & Hz6 & Hz7 & Hz8 & Hz9 & Hz10 & Hzl & _).
destruct (Hzl Hst) as (_ & _ & _ & _ & Ezi & Ezi' & Ezo & Ezo' & Ezs1 & Ezs2 & Ezh & Ezh').
set (u := sublist (w_ipc w) (w_ipc w + m) (a_ibs a)) in *.
assert (Hlu: Zlength u = m) by (unfold u; rewrite Zlength_sublist; lia).
assert (Hub: bytes_ok u) by (unfold u, bytes_ok in *; apply Forall_sublist; auto).
(* the new context's streaming fields: the old ones with the header bytes hb ++ u *)
assert (Hs': sf_strip (c3_s (w_k (lhA_brk a w (k_A (w_k w) v d1 did1) hb kk))) =
             sf_lh (w_sx w) (Zlength hb + m) (hb_splice (sf_hbuf (c3_s (w_k w))) (Zlength hb) u)) by reflexivity.
assert (Ht': c3_tabs (w_k (lhA_brk a w (k_A (w_k w) v d1 did1) hb kk)) = w_tabs w) by reflexivity.
unfold w_sx at 1, w_fs, w_tabs at 1. cbn [w_k]. rewrite Hs', Ht'.
unfold zrel_end, zrel.
cbn [ExStream.zs_stage ExStream.zs_inbs ExStream.zs_outbs ExStream.zs_over ExStream.zs_nfp ExStream.zs_mem
     ExStream.zs_dc ExStream.zs_hbuf ExStream.zs_inpos ExStream.zs_ostart ExStream.zs_oend ExStream.zs_host
     ExStream.zs_fp ExStream.zs_ibuf ExStream.z_hbuf].
cbn [sf_lh sf_stage sf_inSize sf_outSize sf_over sf_nfp sf_ring sf_lhSize sf_hbuf sf_inPos sf_outStart sf_outEnd
     sf_hostage sf_outBuff].
rewrite Hst.
assert (Hrd: ExStream.ZDSS_read <= ExStream.ZDSS_loadHeader -> False)
  by (unfold ExStream.ZDSS_read, ExStream.ZDSS_loadHeader; lia).
assert (Hin: ExStream.ZDSS_loadHeader = ExStream.ZDSS_init -> False)
  by (unfold ExStream.ZDSS_init, ExStream.ZDSS_loadHeader; lia).
repeat match goal with |- _ /\ _ => split end.
all: try assumption.
all: try (intros; exfalso; auto; fail).
all: try (rewrite Hst in Hz1; exact Hz1).
all: try (rewrite Ezh'; auto; fail).
all: try (rewrite Ezi'; auto; fail).
all: try (rewrite Ezs1; auto; fail).
all: try (rewrite Ezs2; auto; fail).
all: try (unfold ExStream.ZDSS_loadHeader; lia).
intros _.
split; [ rewrite Zlength_app, Hlu; reflexivity | ].
split; [ rewrite Zlength_app, Hlu; lia | ].
split; [ unfold bytes_ok in *; apply Forall_app; auto | ].
split; [ | tauto ].
unfold hb_splice. rewrite Hsub, map_app, app_assoc.
replace (Zlength (hb ++ u)) with (Zlength (zbytes hb ++ zbytes u)) by (rewrite !Zlength_app, !Zlength_map; auto).
rewrite sublist0_app1 by (split; [ apply Zlength_nonneg | rewrite !Zlength_app, !Zlength_map; lia ]).
apply sublist_same; auto.
Qed.

Lemma lh_brkA_x_ok : lh_brkA_x_stmt.
Proof.
intros MFh Hpr DENT TABS a w hb kk v tbl d1 did1 Hctx Hlhx Hsel Hk Hkk.
eapply derives_trans; [ exact (lh_brkA_w MFh Hpr DENT TABS a w hb kk v tbl d1 did1 Hctx Hsel Hk Hkk) | ].
unfold ds_inv_x. Exists (g1_w a w hb kk v d1 did1).
change (ds_LI_Px a (g1_w a w hb kk v d1 did1)) with (ds_LI_P a (g1_w a w hb kk v d1 did1) ++
  [ex_call a (g1_w a w hb kk v d1 did1)]).
apply g1x_PROP_app. eapply g1x_call; eauto.
Qed.

End CM_LH3G1X_1.
