(* The epilogue's exact claim (Spec_api6.stream_exact and the next context's exact relation, FSRep3.ex_on3 with
   S3XRel.xrel3).  The code after ZSTD_decompressStream's loop is ExStreamFacts.z_epi on the loop's outcome.  At the
   loop's exit the loop invariant's exact conjunct (S3Main.ex_call) gives the model's stop state zi, related to the
   context by zrel_end (epi_xm); zstd's fields hold zi's values (the bounds of ExStreamBnd.zbnd_x read them back);
   each return of the epilogue is one branch of z_epi (ex_tail once the no-progress guard is passed), and the context
   it leaves is the image of the state that branch leaves (zrel).  epi_x_ret turns such a branch into the exact part
   of a return (E3Defs.epi_xok); epi_x_zero .. epi_x_take are the branches, epi_x_err the no-progress errors. *)
Require Import Zstd.proof.dec.v3.FS.stream.S3Main Zstd.proof.dec.v3.FS.stream.S3XKit Zstd.proof.dec.v3.FS.stream.epi.E3Defs.
Require Import Zstd.proof.model.ExCall Zstd.proof.model.ExStream Zstd.proof.model.ExStreamFacts Zstd.proof.model.ExStreamBnd.
Require Zstd.proof.model.Exact.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

Section CM_E3X_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.

(* the model at the loop's exit: the calls before this one lead to z0, the call's loop stops in zi at input position
   ipc - ipos with the bytes dl delivered, and zi is related to the context *)
Definition epi_xm (a: dsa) (w: lw) : Prop :=
  fresh_cfg (a_st a) ->
  exists z0 zi, zs_run_x (ss_calls (dc_ss (a_st a))) = Some z0 /\ zinv_x zi /\
    a_loop a z0 = LStop XS zi (w_ipc w - a_ipos a) (w_dl w) /\
    zrel_end zi (w_sx w) (w_fs w) (w_tabs w).

Lemma epi_xm_of (a: dsa) (w: lw) : ex_call a w -> w_smw w = 0 -> epi_xm a w.
Proof.
  intros H Hs Hf. destruct (ex_call_stop a w H Hs Hf) as (z0 & zi & Hr & _ & Hi & Hl & Hz).
  exists z0, zi. auto.
Qed.

(* noForwardProgress after the call (zstd's, from the context's) and the context after its update *)
Definition epi_n_x (a: dsa) (w: lw) : Z :=
  if (w_ipc w =? a_ipos a) && (w_opc w =? a_opos a) then sf_nfp (c3_s (w_k w)) + 1 else 0.
Definition epi_kx (a: dsa) (w: lw) : cst3 := k_nfp a (w_k w) (w_opc w) (epi_n_x a w).

(* z_epi once the no-progress guard is passed *)
Definition ex_tail (inp: list Z) (z1: zstate_x) (ip: Z) (dl: list Z) (nfp: Z)
    : option (zstate_x * (Z * Z * list Z * Z * Z)) :=
  let z2 := z_nfp XS z1 nfp in
  if d_expected XS (zs_dc XS z2) =? 0 then
    if zs_oend XS z2 =? zs_ostart XS z2 then
      if zs_host XS z2 =? 1 then
        if ip >=? Zlength inp then Some (z_stage XS z2 ZDSS_read, (1, ip, dl, nfp, 1))
        else Some (z2, (0, ip + 1, dl, nfp, 0))
      else Some (z2, (0, ip, dl, nfp, 0))
    else if zs_host XS z2 =? 0 then Some (z_host XS z2 1, (1, ip - 1, dl, nfp, 1))
    else Some (z2, (1, ip, dl, nfp, 1))
  else
    let d := zs_dc XS z2 in
    Some (z2, (d_expected XS d + (if d_stage XS d =? DS_decompressBlock then ZSTD_blockHeaderSize else 0)
                 - zs_inpos XS z2, ip, dl, nfp, zs_host XS z2)).

Lemma ex_epi_stop (inp: list Z) (room: Z) (z1: zstate_x) (ip: Z) (dl: list Z) :
  ((ip =? 0) && (Zlength dl =? 0) &&
   ((if (ip =? 0) && (Zlength dl =? 0) then zs_nfp XS z1 + 1 else 0) >=? ZS_NO_FORWARD_PROGRESS_MAX) &&
   ((room =? 0) || (Zlength inp =? 0))) = false ->
  z_epi XS inp room (LStop XS z1 ip dl) =
  ex_tail inp z1 ip dl (if (ip =? 0) && (Zlength dl =? 0) then zs_nfp XS z1 + 1 else 0).
Proof. intros H. unfold z_epi. cbv zeta. rewrite H. reflexivity. Qed.

Lemma ex_epi_guard (inp: list Z) (room: Z) (z1: zstate_x) (ip: Z) (dl: list Z) :
  ((ip =? 0) && (Zlength dl =? 0) &&
   ((if (ip =? 0) && (Zlength dl =? 0) then zs_nfp XS z1 + 1 else 0) >=? ZS_NO_FORWARD_PROGRESS_MAX) &&
   ((room =? 0) || (Zlength inp =? 0))) = true ->
  z_epi XS inp room (LStop XS z1 ip dl) = None.
Proof. intros H. unfold z_epi. cbv zeta. rewrite H. reflexivity. Qed.

(* the model's input position and output length at the exit, from the loop invariant *)
Lemma epi_x_lens (a: dsa) (w: lw) :
  dsa_ok a -> call_inv a (w_k w) (w_sv w) (w_ipc w) (w_opc w) (w_oc w) (w_dl w) ->
  ((w_ipc w - a_ipos a =? 0) = (w_ipc w =? a_ipos a)) /\ ((Zlength (w_dl w) =? 0) = (w_opc w =? a_opos a)) /\
  ((a_xroom a =? 0) = (a_opos a =? a_osz a)) /\ ((Zlength (a_xin a) =? 0) = (a_ipos a =? a_isz a)) /\
  Zlength (a_xin a) = a_isz a - a_ipos a.
Proof.
  intros Ha CI.
  pose proof CI as (Hipc & Hopc & _ & _ & Hdl & _).
  pose proof Ha as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hopos & _ & _ & Hipos & _ & Hlibs & _).
  assert (Hx: Zlength (a_xin a) = a_isz a - a_ipos a) by (unfold a_xin; rewrite Zlength_sublist; lia).
  unfold a_xroom. rewrite Hx, Hdl.
  split; [destruct (Z.eqb_spec (w_ipc w - a_ipos a) 0), (Z.eqb_spec (w_ipc w) (a_ipos a)); auto; lia|].
  split; [destruct (Z.eqb_spec (w_opc w - a_opos a) 0), (Z.eqb_spec (w_opc w) (a_opos a)); auto; lia|].
  split; [destruct (Z.eqb_spec (a_osz a - a_opos a) 0), (Z.eqb_spec (a_opos a) (a_osz a)); auto; lia|].
  split; [destruct (Z.eqb_spec (a_isz a - a_ipos a) 0), (Z.eqb_spec (a_ipos a) (a_isz a)); auto; lia|].
  reflexivity.
Qed.

(* the model's state at the loop's exit and its epilogue, when zstd's no-progress guard did not fire *)
Lemma epi_x_model (a: dsa) (w: lw) :
  dsa_ok a -> call_inv a (w_k w) (w_sv w) (w_ipc w) (w_opc w) (w_oc w) (w_dl w) -> epi_xm a w ->
  (w_ipc w = a_ipos a -> w_opc w = a_opos a ->
     ~ (sf_nfp (c3_s (w_k w)) + 1 >= ZSTD_NO_FORWARD_PROGRESS_MAX /\ (w_opc w = a_osz a \/ w_ipc w = a_isz a))) ->
  fresh_cfg (a_st a) ->
  exists z0 zi, zs_run_x (ss_calls (dc_ss (a_st a))) = Some z0 /\ zinv_x zi /\
    a_loop a z0 = LStop XS zi (w_ipc w - a_ipos a) (w_dl w) /\
    zrel_end zi (w_sx w) (w_fs w) (w_tabs w) /\
    z_epi XS (a_xin a) (a_xroom a) (LStop XS zi (w_ipc w - a_ipos a) (w_dl w)) =
    ex_tail (a_xin a) zi (w_ipc w - a_ipos a) (w_dl w) (epi_n_x a w).
Proof.
  intros Ha CI Hxm Hg Hf. destruct (Hxm Hf) as (z0 & zi & Hr & Hzi & Hl & Hze).
  exists z0, zi. split; [exact Hr|]. split; [exact Hzi|]. split; [exact Hl|]. split; [exact Hze|].
  destruct (epi_x_lens a w Ha CI) as (E1 & E2 & E3 & E4 & _).
  assert (Hn: sf_nfp (c3_s (w_k w)) = zs_nfp XS zi).
  { destruct Hze as ((_ & _ & _ & _ & _ & Hn & _) & _). exact Hn. }
  unfold epi_n_x. rewrite <- E1, <- E2, Hn.
  apply ex_epi_stop. rewrite E1, E2, E3, E4.
  destruct (Z.eqb_spec (w_ipc w) (a_ipos a)) as [Ei|Ei]; [|reflexivity].
  destruct (Z.eqb_spec (w_opc w) (a_opos a)) as [Eo|Eo]; [|reflexivity].
  cbn [andb]. rewrite <- Hn.
  destruct (Z.geb_spec (sf_nfp (c3_s (w_k w)) + 1) ZS_NO_FORWARD_PROGRESS_MAX) as [Ge|Lt]; [|reflexivity].
  destruct (Z.eqb_spec (a_opos a) (a_osz a)) as [Eo2|Eo2];
    [exfalso; apply (Hg Ei Eo); unfold ZSTD_NO_FORWARD_PROGRESS_MAX, ZS_NO_FORWARD_PROGRESS_MAX in *; split; [lia|left; lia]|].
  destruct (Z.eqb_spec (a_ipos a) (a_isz a)) as [Ei2|Ei2];
    [exfalso; apply (Hg Ei Eo); unfold ZSTD_NO_FORWARD_PROGRESS_MAX, ZS_NO_FORWARD_PROGRESS_MAX in *; split; [lia|right; lia]|].
  reflexivity.
Qed.

(* the no-progress errors: the model fails on this call too *)
Lemma epi_x_err (a: dsa) (w: lw) :
  dsa_ok a -> call_inv a (w_k w) (w_sv w) (w_ipc w) (w_opc w) (w_oc w) (w_dl w) -> epi_xm a w ->
  w_ipc w = a_ipos a -> w_opc w = a_opos a -> sf_nfp (c3_s (w_k w)) + 1 >= ZSTD_NO_FORWARD_PROGRESS_MAX ->
  (w_opc w = a_osz a \/ w_ipc w = a_isz a) ->
  fresh_cfg (a_st a) -> Exact.zs_call (ss_calls (dc_ss (a_st a))) (a_xin a, a_xroom a) = None.
Proof.
  intros Ha CI Hxm Ei Eo Hge Hc Hf. destruct (Hxm Hf) as (z0 & zi & Hr & Hzi & Hl & Hze).
  apply (ex_epi_none a z0 zi (w_ipc w - a_ipos a) (w_dl w) Hr Hl).
  destruct (epi_x_lens a w Ha CI) as (E1 & E2 & E3 & E4 & _).
  assert (Hn: sf_nfp (c3_s (w_k w)) = zs_nfp XS zi).
  { destruct Hze as ((_ & _ & _ & _ & _ & Hn & _) & _). exact Hn. }
  apply ex_epi_guard. rewrite E1, E2, E3, E4, <- Hn.
  rewrite (proj2 (Z.eqb_eq _ _) Ei), (proj2 (Z.eqb_eq _ _) Eo). cbn [andb].
  rewrite (proj2 (Z.geb_le _ _)) by (unfold ZSTD_NO_FORWARD_PROGRESS_MAX, ZS_NO_FORWARD_PROGRESS_MAX in *; lia).
  cbn [andb]. destruct Hc as [Hc|Hc].
  - rewrite (proj2 (Z.eqb_eq (a_opos a) (a_osz a))) by lia. reflexivity.
  - rewrite (proj2 (Z.eqb_eq (a_ipos a) (a_isz a))) by lia. apply Bool.orb_true_r.
Qed.

(* a return whose model branch is known: the exact part of the return *)
Lemma epi_x_ret (a: dsa) (w: lw) (k': cst3) (r ipos' a': Z) :
  dsa_ok a -> call_inv a (w_k w) (w_sv w) (w_ipc w) (w_opc w) (w_oc w) (w_dl w) -> start_ok a -> epi_xm a w ->
  (w_ipc w = a_ipos a -> w_opc w = a_opos a ->
     ~ (sf_nfp (c3_s (w_k w)) + 1 >= ZSTD_NO_FORWARD_PROGRESS_MAX /\ (w_opc w = a_osz a \/ w_ipc w = a_isz a))) ->
  a_ipos a + ss_ahead (dc_ss (a_st a)) <= ipos' + a' ->
  (ipos' + a' <= a_isz a \/ ipos' + a' = a_ipos a + ss_ahead (dc_ss (a_st a))) ->
  (forall zi, zinv_x zi -> zrel_end zi (w_sx w) (w_fs w) (w_tabs w) ->
     exists z' ipm, ipm = ipos' - a_ipos a /\
       ex_tail (a_xin a) zi (w_ipc w - a_ipos a) (w_dl w) (epi_n_x a w) =
         Some (z', (r, ipm, w_dl w, epi_n_x a w, a')) /\
       zrel z' (sf_strip (c3_s k')) (c3_fs k') (c3_tabs k')) ->
  forall stall', epi_xok a k' r ipos' (w_opc w) (w_oc w) (epi_st a r ipos' a' stall' (w_dl w)).
Proof.
  intros Ha CI Hst Hxm Hg Ha1 Ha2 Hpath stall'.
  pose proof CI as (Hipc & Hopc & _ & _ & Hdl & Hdlc & _).
  pose proof Ha as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hopos & _ & _ & Hipos & _ & Hlibs & _).
  pose proof Hst as (_ & Hah & _).
  assert (Hro: 0 <= a_xroom a) by (unfold a_xroom; lia).
  assert (Hm: fresh_cfg (a_st a) -> exists z0 zi z',
     zs_run_x (ss_calls (dc_ss (a_st a))) = Some z0 /\ zinv_x zi /\
     a_loop a z0 = LStop XS zi (w_ipc w - a_ipos a) (w_dl w) /\
     z_epi XS (a_xin a) (a_xroom a) (LStop XS zi (w_ipc w - a_ipos a) (w_dl w)) =
       Some (z', (r, ipos' - a_ipos a, w_dl w, epi_n_x a w, a')) /\
     zrel z' (sf_strip (c3_s k')) (c3_fs k') (c3_tabs k')).
  { intros Hf. destruct (epi_x_model a w Ha CI Hxm Hg Hf) as (z0 & zi & Hr & Hzi & Hl & Hze & He).
    destruct (Hpath zi Hzi Hze) as (z' & ipm & -> & Ht & Hz').
    exists z0, zi, z'. rewrite He. auto. }
  split.
  - intros Hf. right. destruct (Hm Hf) as (z0 & zi & z' & Hr & Hzi & Hl & He & Hz').
    destruct (ex_epi a z0 zi _ _ z' _ Hr Hro Hl He) as [Hc _].
    cbv zeta. change (sublist (a_ipos a) (a_isz a) (a_ibs a)) with (a_xin a).
    change (a_osz a - a_opos a) with (a_xroom a). rewrite Hc.
    split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [exact Hdlc|].
    exists stall'.
    assert (Hin: sublist (a_ipos a + ss_ahead (dc_ss (a_st a))) (ipos' + a') (a_ibs a) =
                 sublist (ss_ahead (dc_ss (a_st a))) (ipos' - a_ipos a + a') (a_xin a)).
    { destruct Ha2 as [Hle|Heq].
      - unfold a_xin. rewrite sublist_sublist by lia. f_equal; lia.
      - rewrite !sublist_nil' by lia. reflexivity. }
    destruct Hf as (_ & _ & _ & Hstab & _).
    unfold epi_st, ss_after. rewrite Hin, Hstab. reflexivity.
  - intros Hex Herr Hcase.
    assert (Hf: fresh_cfg (a_st a)).
    { destruct Hcase as [Hi|(H1 & H2 & H3 & H4)].
      - exfalso. apply (f_equal ss_calls) in Hi. unfold epi_st in Hi. cbn in Hi.
        exact (app_cons_not_nil _ _ _ (eq_sym Hi)).
      - unfold epi_st in *. cbn in H1, H2, H3, H4, Hex. split; [exact H1|]. split; [exact H2|].
        split; [exact H3|]. split; [exact H4|exact Hex]. }
    destruct (Hm Hf) as (z0 & zi & z' & Hr & Hzi & Hl & He & Hz').
    destruct (ex_epi a z0 zi _ _ z' _ Hr Hro Hl He) as [_ Hrun].
    cbn [sr_ex SR3]. exists z'.
    split; [unfold epi_st; cbn; exact Hrun|].
    split; [|exact Hz'].
    unfold zinv_x. eapply z_epi_zinv with (r := LStop XS zi (w_ipc w - a_ipos a) (w_dl w));
      first [exact Hzi | exact He | exact xgood_x_begin | exact xgood_x_frame1 | exact xgood_x_block].
Qed.

(* ---------- zstd's fields hold the stop state's values ---------- *)

(* outBuffSize is at most 2^32: the ring holds the outBuffSize cells after the inBuffSize ones *)
Lemma zrel_outbs (z: zstate_x) (s: sfields) (fs: fstate) (t: tabs3) :
  zrel z s fs t -> sf_inSize s + sf_outSize s <= 2 ^ 32 -> 0 <= zs_outbs XS z <= 2 ^ 32.
Proof.
  intros (_ & _ & Hin & Hout & _ & _ & Hlen & _ & Hring & _) Hle.
  pose proof (Zlength_nonneg (zs_mem XS z)) as H0.
  split; [lia|].
  destruct (Z_le_gt_dec 0 (zs_inbs XS z)) as [Hp|Hn]; [lia|].
  destruct (Z_le_gt_dec (zs_outbs XS z) 0) as [Hz|Hz]; [lia|].
  exfalso. apply (f_equal (@Zlength val)) in Hring. rewrite !Zlength_map, Hlen in Hring.
  rewrite Zlength_sublist2 in Hring. lia.
Qed.

Lemma epi_x_fields (w: lw) (zi: zstate_x) :
  zinv_x zi -> zrel_end zi (w_sx w) (w_fs w) (w_tabs w) ->
  sf_stage (c3_s (w_k w)) <> zdss_loadHeader -> sf_inSize (c3_s (w_k w)) + sf_outSize (c3_s (w_k w)) <= 2 ^ 32 ->
  let s := c3_s (w_k w) in let d := zs_dc XS zi in
  zs_stage XS zi = sf_stage s /\
  fs_expected (c3_fs (w_k w)) = vlong (d_expected XS d) /\ 0 <= d_expected XS d < 2 ^ 32 /\
  (d_expected XS d <> 0 -> fs_stage (c3_fs (w_k w)) = Vint (Int.repr (d_stage XS d))) /\
  0 <= d_stage XS d <= DS_skipFrame /\
  sf_outStart s = vlong (zs_ostart XS zi) /\ sf_outEnd s = vlong (zs_oend XS zi) /\
  0 <= zs_ostart XS zi <= zs_oend XS zi /\ zs_oend XS zi <= 2 ^ 32 /\
  sf_inPos s = vlong (zs_inpos XS zi) /\ 0 <= zs_inpos XS zi < 2 ^ 32 /\
  sf_hostage s = Vint (Int.repr (zs_host XS zi)) /\ (zs_host XS zi = 0 \/ zs_host XS zi = 1).
Proof.
  intros Hzi Hze Hlh Hsz s d.
  pose proof (zinv_x_bnd zi Hzi) as (Hst & _ & Hexp & _ & Ho1 & Ho2 & _).
  pose proof Hzi as (_ & _ & (Hld & Hnld & _) & _).
  destruct Hze as (Hz & Hed & _ & Hip & Hos & Hoe & Hh & Hh01).
  assert (Hob: 0 <= zs_outbs XS zi <= 2 ^ 32) by (apply (zrel_outbs zi (w_sx w) (w_fs w) (w_tabs w) Hz); exact Hsz).
  assert (Hs: zs_stage XS zi = sf_stage s) by (destruct Hz as (H & _); unfold w_sx in H; exact (eq_sym H)).
  assert (Hlh': zs_stage XS zi <> ZDSS_loadHeader) by (rewrite Hs; exact Hlh).
  destruct (Hed Hlh') as (He & Hfs).
  unfold w_sx, w_fs in *. cbn [sf_strip sf_inPos sf_outStart sf_outEnd sf_hostage] in *.
  split; [exact Hs|]. split; [exact He|]. split; [exact Hexp|]. split; [exact Hfs|]. split; [exact Hst|].
  split; [exact Hos|]. split; [exact Hoe|]. split; [lia|]. split; [lia|]. split; [exact Hip|].
  split; [|split; [exact Hh|exact Hh01]].
  destruct (Z.eq_dec (zs_stage XS zi) ZDSS_load) as [El|El]; [specialize (Hld El); lia|].
  rewrite (proj1 (Hnld El)). lia.
Qed.

(* ---------- the context the epilogue leaves is the image of z_epi's state ---------- *)

(* noForwardProgress updated *)
Lemma zrel_nfp (z: zstate_x) (s: sfields) (fs: fstate) (t: tabs3) (n: Z) (ev: reptype t_outBuffer) :
  zrel z (sf_strip s) fs t ->
  zrel (z_nfp XS z n) (sf_strip (sf_epi s (sf_stage s) n (sf_hostage s) ev)) fs t.
Proof.
  intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12).
  unfold zrel. cbn [sf_strip sf_epi sf_stage sf_inSize sf_outSize sf_over sf_nfp sf_ring sf_lhSize sf_hbuf sf_inPos
    sf_outStart sf_outEnd sf_hostage sf_outBuff z_nfp zs_stage zs_inbs zs_outbs zs_over zs_nfp zs_mem zs_dc zs_hbuf
    zs_inpos zs_ostart zs_oend zs_host zs_fp zs_ibuf] in *.
  repeat (split; [assumption|]). split; [reflexivity|]. repeat (split; [assumption|]). assumption.
Qed.

(* the hostage byte taken (in a stage other than zdss_loadHeader) *)
Lemma zrel_host1 (z: zstate_x) (s: sfields) (fs: fstate) (t: tabs3) (ev: reptype t_outBuffer) :
  zrel z (sf_strip s) fs t -> zs_stage XS z <> ZDSS_loadHeader ->
  zrel (z_host XS z 1) (sf_strip (sf_epi s (sf_stage s) (sf_nfp s) (Vint (Int.repr 1)) ev)) fs t.
Proof.
  intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12) Hlh.
  unfold zrel. cbn [sf_strip sf_epi sf_stage sf_inSize sf_outSize sf_over sf_nfp sf_ring sf_lhSize sf_hbuf sf_inPos
    sf_outStart sf_outEnd sf_hostage sf_outBuff z_host zs_stage zs_inbs zs_outbs zs_over zs_nfp zs_mem zs_dc zs_hbuf
    zs_inpos zs_ostart zs_oend zs_host zs_fp zs_ibuf] in *.
  repeat (split; [assumption|]). split; [intros E; contradiction|].
  intros Hr. destruct (H12 Hr) as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9).
  repeat (split; [assumption|]). split; [reflexivity|]. split; [right; reflexivity|]. split; assumption.
Qed.

(* back to zdss_read (from zdss_init: the frame state kept by zrel_end; from a later stage: as it was) *)
Lemma zrel_read (z: zstate_x) (s: sfields) (fs: fstate) (t: tabs3) (ev: reptype t_outBuffer) :
  zrel z (sf_strip s) fs t -> zs_stage XS z <> ZDSS_loadHeader ->
  (zs_stage XS z = ZDSS_init ->
     sf_inPos s = vlong (zs_inpos XS z) /\ sf_outStart s = vlong (zs_ostart XS z) /\
     sf_outEnd s = vlong (zs_oend XS z) /\ 0 <= zs_ostart XS z <= zs_oend XS z /\ zs_oend XS z <= zs_outbs XS z /\
     sf_hostage s = Vint (Int.repr (zs_host XS z)) /\ (zs_host XS z = 0 \/ zs_host XS z = 1) /\
     (exists ts, t = TInit None ts /\ drel (zs_fp XS z) (zs_dc XS z) (sf_outBuff s) fs ts)) ->
  zrel (z_stage XS z ZDSS_read) (sf_strip (sf_epi s zdss_read (sf_nfp s) (sf_hostage s) ev)) fs t.
Proof.
  intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12) Hlh Hinit.
  assert (Hr: zs_stage XS z = ZDSS_init \/ ZDSS_read <= zs_stage XS z)
    by (unfold ZDSS_init, ZDSS_loadHeader, ZDSS_read in *; lia).
  assert (Hc: sf_inPos s = vlong (zs_inpos XS z) /\ sf_outStart s = vlong (zs_ostart XS z) /\
     sf_outEnd s = vlong (zs_oend XS z) /\ 0 <= zs_ostart XS z <= zs_oend XS z /\ zs_oend XS z <= zs_outbs XS z /\
     sf_hostage s = Vint (Int.repr (zs_host XS z)) /\ (zs_host XS z = 0 \/ zs_host XS z = 1) /\
     (exists ts, t = TInit None ts /\ drel (zs_fp XS z) (zs_dc XS z) (sf_outBuff s) fs ts)).
  { destruct Hr as [Hi|Hr]; [exact (Hinit Hi)|].
    destruct (H12 Hr) as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & _). cbn [sf_strip] in *. tauto. }
  clear Hinit H11 H12.
  destruct Hc as (Hip & Hos & Hoe & Ho1 & Ho2 & Hhs & Hh & Hd).
  unfold zrel. cbn [sf_strip sf_epi sf_stage sf_inSize sf_outSize sf_over sf_nfp sf_ring sf_lhSize sf_hbuf sf_inPos
    sf_outStart sf_outEnd sf_hostage sf_outBuff z_stage zs_stage zs_inbs zs_outbs zs_over zs_nfp zs_mem zs_dc zs_hbuf
    zs_inpos zs_ostart zs_oend zs_host zs_fp zs_ibuf] in *.
  split; [reflexivity|]. split; [unfold ZDSS_read; lia|].
  repeat (split; [assumption|]). split; [unfold ZDSS_read, ZDSS_loadHeader; intros E; discriminate|].
  intros _. split; [exact Hip|]. split; [exact Hos|]. split; [exact Hoe|]. split; [lia|]. split; [lia|].
  split; [exact Hhs|]. split; [exact Hh|]. split; [exact Hd|].
  unfold ZDSS_read, ZDSS_load; intros E; discriminate.
Qed.

(* ---------- the returns of the epilogue: one branch of z_epi each ---------- *)

Lemma ex_vlong_inj (x y: Z) : 0 <= x <= Int64.max_unsigned -> 0 <= y <= Int64.max_unsigned -> vlong x = vlong y -> x = y.
Proof.
  intros Hx Hy H. unfold vlong in H.
  assert (H1: Int64.unsigned (Int64.repr x) = Int64.unsigned (Int64.repr y)) by congruence.
  rewrite !Int64.unsigned_repr in H1 by lia. exact H1.
Qed.

Lemma ex_vint_inj (x y: Z) : 0 <= x <= Int.max_unsigned -> 0 <= y <= Int.max_unsigned ->
  Vint (Int.repr x) = Vint (Int.repr y) -> x = y.
Proof.
  intros Hx Hy H.
  assert (H1: Int.unsigned (Int.repr x) = Int.unsigned (Int.repr y)) by congruence.
  rewrite !Int.unsigned_repr in H1 by lia. exact H1.
Qed.

(* the branch of z_epi a return takes, and the context it leaves related to z_epi's state *)
Definition epi_xbr (a: dsa) (w: lw) (k': cst3) (r ipos' a': Z) : Prop :=
  forall zi, zinv_x zi -> zrel_end zi (w_sx w) (w_fs w) (w_tabs w) ->
  exists z' ipm, ipm = ipos' - a_ipos a /\
    ex_tail (a_xin a) zi (w_ipc w - a_ipos a) (w_dl w) (epi_n_x a w) =
      Some (z', (r, ipm, w_dl w, epi_n_x a w, a')) /\
    zrel z' (sf_strip (c3_s k')) (c3_fs k') (c3_tabs k').

(* the facts of zstd's fields every return reads, as the model's values *)
Ltac ex_facts w zi Hzi Hze Hlh Hsz :=
  let Hs := fresh "Hs" in let He := fresh "He" in let Her := fresh "Her" in let Hfs := fresh "Hfs" in
  let Hdst := fresh "Hdst" in let Hos := fresh "Hos" in let Hoe := fresh "Hoe" in let Ho := fresh "Ho" in
  let Ho2 := fresh "Ho2" in let Hip := fresh "Hip" in let Hipr := fresh "Hipr" in let Hh := fresh "Hh" in
  let Hh01 := fresh "Hh01" in
  destruct (epi_x_fields w zi Hzi Hze Hlh Hsz)
    as (Hs & He & Her & Hfs & Hdst & Hos & Hoe & Ho & Ho2 & Hip & Hipr & Hh & Hh01).

Lemma epi_kx_fields (a: dsa) (w: lw) :
  c3_s (epi_kx a w) = sf_epi (c3_s (w_k w)) (sf_stage (c3_s (w_k w))) (epi_n_x a w) (sf_hostage (c3_s (w_k w)))
                        (epi_ev a (w_opc w)) /\
  c3_fs (epi_kx a w) = c3_fs (w_k w) /\ c3_tabs (epi_kx a w) = c3_tabs (w_k w).
Proof. split; [|split]; reflexivity. Qed.

(* return 0, the hostage byte not held, all flushed *)
Lemma epi_x_zero (a: dsa) (w: lw) (os: Z) :
  sf_stage (c3_s (w_k w)) <> zdss_loadHeader -> sf_inSize (c3_s (w_k w)) + sf_outSize (c3_s (w_k w)) <= 2 ^ 32 ->
  fs_expected (c3_fs (w_k w)) = vlong 0 -> sf_outStart (c3_s (w_k w)) = vlong os ->
  sf_outEnd (c3_s (w_k w)) = vlong os -> 0 <= os <= Int64.max_unsigned ->
  sf_hostage (c3_s (w_k w)) = Vint (Int.repr 0) ->
  epi_xbr a w (epi_kx a w) 0 (w_ipc w) 0.
Proof.
  intros Hlh Hsz He0 Hos0 Hoe0 Hosr Hh0 zi Hzi Hze. ex_facts w zi Hzi Hze Hlh Hsz.
  assert (Ed: d_expected XS (zs_dc XS zi) = 0) by (rewrite He0 in He; apply ex_vlong_inj in He; rep_lia).
  assert (Eo: zs_oend XS zi = zs_ostart XS zi).
  { rewrite Hos0 in Hos. rewrite Hoe0 in Hoe. apply ex_vlong_inj in Hos; [|rep_lia|rep_lia].
    apply ex_vlong_inj in Hoe; [|rep_lia|rep_lia]. lia. }
  assert (Eh: zs_host XS zi = 0) by (rewrite Hh0 in Hh; apply ex_vint_inj in Hh; rep_lia).
  exists (z_nfp XS zi (epi_n_x a w)), (w_ipc w - a_ipos a). split; [reflexivity|]. split.
  - unfold ex_tail. cbn [z_nfp zs_dc zs_oend zs_ostart zs_host]. rewrite Ed, Eo, !Z.eqb_refl, Eh. reflexivity.
  - destruct (epi_kx_fields a w) as (-> & -> & ->). apply zrel_nfp. exact (proj1 Hze).
Qed.

(* return 1, the hostage byte held, output pending *)
Lemma epi_x_held (a: dsa) (w: lw) (os oe: Z) :
  sf_stage (c3_s (w_k w)) <> zdss_loadHeader -> sf_inSize (c3_s (w_k w)) + sf_outSize (c3_s (w_k w)) <= 2 ^ 32 ->
  fs_expected (c3_fs (w_k w)) = vlong 0 -> sf_outStart (c3_s (w_k w)) = vlong os ->
  sf_outEnd (c3_s (w_k w)) = vlong oe -> 0 <= os <= Int64.max_unsigned -> 0 <= oe <= Int64.max_unsigned -> os <> oe ->
  sf_hostage (c3_s (w_k w)) = Vint (Int.repr 1) ->
  epi_xbr a w (epi_kx a w) 1 (w_ipc w) 1.
Proof.
  intros Hlh Hsz He0 Hos0 Hoe0 Hosr Hoer Hne Hh1 zi Hzi Hze. ex_facts w zi Hzi Hze Hlh Hsz.
  assert (Ed: d_expected XS (zs_dc XS zi) = 0) by (rewrite He0 in He; apply ex_vlong_inj in He; rep_lia).
  assert (Eo: (zs_oend XS zi =? zs_ostart XS zi) = false).
  { rewrite Hos0 in Hos. rewrite Hoe0 in Hoe. apply ex_vlong_inj in Hos; [|rep_lia|rep_lia].
    apply ex_vlong_inj in Hoe; [|rep_lia|rep_lia]. apply Z.eqb_neq. lia. }
  assert (Eh: zs_host XS zi = 1) by (rewrite Hh1 in Hh; apply ex_vint_inj in Hh; rep_lia).
  exists (z_nfp XS zi (epi_n_x a w)), (w_ipc w - a_ipos a). split; [reflexivity|]. split.
  - unfold ex_tail. cbn [z_nfp zs_dc zs_oend zs_ostart zs_host]. rewrite Ed, Eo, Eh. reflexivity.
  - destruct (epi_kx_fields a w) as (-> & -> & ->). apply zrel_nfp. exact (proj1 Hze).
Qed.

(* return 0 releasing the hostage byte (in.pos + 1) *)
Lemma epi_x_rel (a: dsa) (w: lw) (os: Z) :
  dsa_ok a -> call_inv a (w_k w) (w_sv w) (w_ipc w) (w_opc w) (w_oc w) (w_dl w) ->
  sf_stage (c3_s (w_k w)) <> zdss_loadHeader -> sf_inSize (c3_s (w_k w)) + sf_outSize (c3_s (w_k w)) <= 2 ^ 32 ->
  fs_expected (c3_fs (w_k w)) = vlong 0 -> sf_outStart (c3_s (w_k w)) = vlong os ->
  sf_outEnd (c3_s (w_k w)) = vlong os -> 0 <= os <= Int64.max_unsigned ->
  sf_hostage (c3_s (w_k w)) = Vint (Int.repr 1) -> w_ipc w < a_isz a ->
  epi_xbr a w (epi_kx a w) 0 (w_ipc w + 1) 0.
Proof.
  intros Ha CI Hlh Hsz He0 Hos0 Hoe0 Hosr Hh1 Hlt zi Hzi Hze. ex_facts w zi Hzi Hze Hlh Hsz.
  destruct (epi_x_lens a w Ha CI) as (_ & _ & _ & _ & Hlen).
  assert (Ed: d_expected XS (zs_dc XS zi) = 0) by (rewrite He0 in He; apply ex_vlong_inj in He; rep_lia).
  assert (Eo: zs_oend XS zi = zs_ostart XS zi).
  { rewrite Hos0 in Hos. rewrite Hoe0 in Hoe. apply ex_vlong_inj in Hos; [|rep_lia|rep_lia].
    apply ex_vlong_inj in Hoe; [|rep_lia|rep_lia]. lia. }
  assert (Eh: zs_host XS zi = 1) by (rewrite Hh1 in Hh; apply ex_vint_inj in Hh; rep_lia).
  assert (Ei: (w_ipc w - a_ipos a >=? Zlength (a_xin a)) = false) by (rewrite Hlen; destruct (Z.geb_spec (w_ipc w - a_ipos a) (a_isz a - a_ipos a)); [lia|reflexivity]).
  exists (z_nfp XS zi (epi_n_x a w)), (w_ipc w - a_ipos a + 1). split; [lia|]. split.
  - unfold ex_tail. cbn [z_nfp zs_dc zs_oend zs_ostart zs_host]. rewrite Ed, Eo, !Z.eqb_refl, Eh, Ei. reflexivity.
  - destruct (epi_kx_fields a w) as (-> & -> & ->). apply zrel_nfp. exact (proj1 Hze).
Qed.

(* return 1 when the hostage byte cannot be released (not in this call's input): back to zdss_read *)
Lemma epi_x_cr (a: dsa) (w: lw) (os: Z) :
  dsa_ok a -> call_inv a (w_k w) (w_sv w) (w_ipc w) (w_opc w) (w_oc w) (w_dl w) ->
  sf_stage (c3_s (w_k w)) <> zdss_loadHeader -> sf_inSize (c3_s (w_k w)) + sf_outSize (c3_s (w_k w)) <= 2 ^ 32 ->
  fs_expected (c3_fs (w_k w)) = vlong 0 -> sf_outStart (c3_s (w_k w)) = vlong os ->
  sf_outEnd (c3_s (w_k w)) = vlong os -> 0 <= os <= Int64.max_unsigned ->
  sf_hostage (c3_s (w_k w)) = Vint (Int.repr 1) -> a_isz a <= w_ipc w ->
  epi_xbr a w (k_sh (epi_kx a w) zdss_read (sf_hostage (c3_s (epi_kx a w)))) 1 (w_ipc w) 1.
Proof.
  intros Ha CI Hlh Hsz He0 Hos0 Hoe0 Hosr Hh1 Hge zi Hzi Hze. ex_facts w zi Hzi Hze Hlh Hsz.
  destruct (epi_x_lens a w Ha CI) as (_ & _ & _ & _ & Hlen).
  assert (Ed: d_expected XS (zs_dc XS zi) = 0) by (rewrite He0 in He; apply ex_vlong_inj in He; rep_lia).
  assert (Eo: zs_oend XS zi = zs_ostart XS zi).
  { rewrite Hos0 in Hos. rewrite Hoe0 in Hoe. apply ex_vlong_inj in Hos; [|rep_lia|rep_lia].
    apply ex_vlong_inj in Hoe; [|rep_lia|rep_lia]. lia. }
  assert (Eh: zs_host XS zi = 1) by (rewrite Hh1 in Hh; apply ex_vint_inj in Hh; rep_lia).
  assert (Ei: (w_ipc w - a_ipos a >=? Zlength (a_xin a)) = true) by (rewrite Hlen; destruct (Z.geb_spec (w_ipc w - a_ipos a) (a_isz a - a_ipos a)); [reflexivity|lia]).
  exists (z_stage XS (z_nfp XS zi (epi_n_x a w)) ZDSS_read), (w_ipc w - a_ipos a). split; [lia|]. split.
  - unfold ex_tail. cbn [z_nfp zs_dc zs_oend zs_ostart zs_host]. rewrite Ed, Eo, !Z.eqb_refl, Eh, Ei. reflexivity.
  - unfold k_sh, k_epi. cbn [c3_with_s c3_s c3_fs c3_tabs].
    destruct (epi_kx_fields a w) as (Es & -> & ->).
    replace (sf_nfp (c3_s (epi_kx a w))) with (sf_nfp (c3_s (epi_kx a w))) by reflexivity.
    apply zrel_read.
    + rewrite Es. apply zrel_nfp. exact (proj1 Hze).
    + cbn [z_nfp zs_stage]. rewrite Hs. exact Hlh.
    + intros Hi. cbn [z_nfp zs_stage zs_inpos zs_ostart zs_oend zs_outbs zs_host zs_fp zs_dc] in *.
      destruct Hze as ((_ & _ & _ & Hout & _) & _ & Hd & _).
      rewrite Es. cbn [sf_epi sf_inPos sf_outStart sf_outEnd sf_hostage sf_outBuff].
      split; [exact Hip|]. split; [exact Hos|]. split; [exact Hoe|]. split; [lia|].
      pose proof (zinv_x_bnd zi Hzi) as (_ & _ & _ & _ & _ & Hob & _).
      split; [exact Hob|]. split; [exact Hh|]. split; [exact Hh01|].
      destruct (Hd Hi Eh) as (ts & Ht & Hdr). exists ts. split; [exact Ht|]. unfold w_sx in Hdr. exact Hdr.
Qed.

(* return 1 taking the hostage byte (in.pos - 1): output pending *)
Lemma epi_x_take (a: dsa) (w: lw) (os oe: Z) :
  sf_stage (c3_s (w_k w)) <> zdss_loadHeader -> sf_inSize (c3_s (w_k w)) + sf_outSize (c3_s (w_k w)) <= 2 ^ 32 ->
  fs_expected (c3_fs (w_k w)) = vlong 0 -> sf_outStart (c3_s (w_k w)) = vlong os ->
  sf_outEnd (c3_s (w_k w)) = vlong oe -> 0 <= os <= Int64.max_unsigned -> 0 <= oe <= Int64.max_unsigned -> os <> oe ->
  sf_hostage (c3_s (w_k w)) = Vint (Int.repr 0) ->
  epi_xbr a w (k_sh (epi_kx a w) (sf_stage (c3_s (epi_kx a w))) (Vint (Int.repr 1))) 1 (w_ipc w - 1) 1.
Proof.
  intros Hlh Hsz He0 Hos0 Hoe0 Hosr Hoer Hne Hh0 zi Hzi Hze. ex_facts w zi Hzi Hze Hlh Hsz.
  assert (Ed: d_expected XS (zs_dc XS zi) = 0) by (rewrite He0 in He; apply ex_vlong_inj in He; rep_lia).
  assert (Eo: (zs_oend XS zi =? zs_ostart XS zi) = false).
  { rewrite Hos0 in Hos. rewrite Hoe0 in Hoe. apply ex_vlong_inj in Hos; [|rep_lia|rep_lia].
    apply ex_vlong_inj in Hoe; [|rep_lia|rep_lia]. apply Z.eqb_neq. lia. }
  assert (Eh: zs_host XS zi = 0) by (rewrite Hh0 in Hh; apply ex_vint_inj in Hh; rep_lia).
  exists (z_host XS (z_nfp XS zi (epi_n_x a w)) 1), (w_ipc w - a_ipos a - 1). split; [lia|]. split.
  - unfold ex_tail. cbn [z_nfp zs_dc zs_oend zs_ostart zs_host]. rewrite Ed, Eo, Eh. reflexivity.
  - unfold k_sh, k_epi. cbn [c3_with_s c3_s c3_fs c3_tabs].
    destruct (epi_kx_fields a w) as (Es & -> & ->). rewrite Es.
    apply zrel_host1.
    + apply zrel_nfp. exact (proj1 Hze).
    + cbn [z_nfp zs_stage]. rewrite Hs. exact Hlh.
Qed.

(* the hint (the frame not complete): expected + the next block's header - inPos *)
Lemma epi_x_hint (a: dsa) (w: lw) (e fstg ip0: Z) :
  sf_stage (c3_s (w_k w)) <> zdss_loadHeader -> sf_inSize (c3_s (w_k w)) + sf_outSize (c3_s (w_k w)) <= 2 ^ 32 ->
  fs_expected (c3_fs (w_k w)) = vlong e -> 0 <= e <= Int64.max_unsigned -> e <> 0 ->
  fs_stage (c3_fs (w_k w)) = Vint (Int.repr fstg) -> 0 <= fstg <= 7 ->
  sf_inPos (c3_s (w_k w)) = vlong ip0 -> 0 <= ip0 <= Int64.max_unsigned ->
  sf_hostage (c3_s (w_k w)) = Vint (Int.repr 0) ->
  epi_xbr a w (epi_kx a w) (e + ZSTD_blockHeaderSize * nit_blk fstg - ip0) (w_ipc w) 0.
Proof.
  intros Hlh Hsz He0 Her0 Hne Hfs0 Hfr Hip0 Hipr0 Hh0 zi Hzi Hze. ex_facts w zi Hzi Hze Hlh Hsz.
  assert (Ed: d_expected XS (zs_dc XS zi) = e) by (rewrite He0 in He; apply ex_vlong_inj in He; rep_lia).
  assert (Edn: (d_expected XS (zs_dc XS zi) =? 0) = false) by (apply Z.eqb_neq; lia).
  assert (Est: d_stage XS (zs_dc XS zi) = fstg).
  { specialize (Hfs ltac:(lia)). rewrite Hfs0 in Hfs. unfold DS_skipFrame in Hdst.
    apply ex_vint_inj in Hfs; rep_lia. }
  assert (Eip: zs_inpos XS zi = ip0) by (rewrite Hip0 in Hip; apply ex_vlong_inj in Hip; rep_lia).
  assert (Eh: zs_host XS zi = 0) by (rewrite Hh0 in Hh; apply ex_vint_inj in Hh; rep_lia).
  assert (Enit: ZSTD_blockHeaderSize * nit_blk fstg =
                (if fstg =? DS_decompressBlock then ZSTD_blockHeaderSize else 0)).
  { assert (fstg = 0 \/ fstg = 1 \/ fstg = 2 \/ fstg = 3 \/ fstg = 4 \/ fstg = 5 \/ fstg = 6 \/ fstg = 7) as Hc by lia.
    destruct Hc as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; reflexivity. }
  exists (z_nfp XS zi (epi_n_x a w)), (w_ipc w - a_ipos a). split; [reflexivity|]. split.
  - unfold ex_tail. cbn [z_nfp zs_dc zs_oend zs_ostart zs_host zs_inpos]. rewrite Edn, Est, Eip, Eh, Enit, Ed.
    reflexivity.
  - destruct (epi_kx_fields a w) as (-> & -> & ->). apply zrel_nfp. exact (proj1 Hze).
Qed.

End CM_E3X_1.
