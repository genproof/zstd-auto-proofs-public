(* FS3 streaming, the prologue of ZSTD_decompressStream: the pure part (template v2 StreamSeg_pro.v). *)
Require Import Zstd.proof.dec.v3.FS.stream.S3Main Zstd.proof.dec.v3.FS.stream.S3Mem.
Require Import Zstd.proof.dec.v3.FS.stream.pro2.Q3Content.
Local Open Scope logic.

Section CM_Q3ProPure_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma repr64_0 : forall x, 0 <= x <= Int64.max_unsigned -> Int64.repr x = Int64.zero -> x = 0.
Proof.
intros x Hx E. apply repr_inj_unsigned64 in E; [lia | lia | rep_lia].
Qed.

Ltac fin0 :=
  try (match goal with E: ?x = 0 |- offset_val ?x ?p = ?p => rewrite E; apply isptr_offset_val_zero; auto end).

(* ---------- the view at the call's entry ---------- *)

(* c_core reads obuf only in stable mode, where it is Some *)
Lemma c_core_obuf : forall b o1 o2 sout k sv,
  c_core b o1 sout k sv -> (b = true -> forall x, o1 = Some x -> o2 = Some x) -> c_core b o2 sout k sv.
Proof.
intros b o1 o2 sout k sv Hc Ho. unfold c_core in *. destruct Hc as (Hh & Hd & Hz & Hc).
split; [exact Hh|]. split; [exact Hd|]. split; [exact Hz|].
destruct (sf_stage (c3_s k) =? zdss_init); [exact Hc|].
destruct (sf_stage (c3_s k) =? zdss_loadHeader); [exact Hc|].
destruct Hc as (H1 & H2 & H3 & H4). split; [exact H1|]. split; [exact H2|]. split; [|exact H4].
unfold c_ring in *. destruct H3 as (R1 & R2 & R3 & ostart & oend & R4 & R5 & R6 & R7).
split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. exists ostart, oend.
split; [exact R4|]. split; [exact R5|]. split; [exact R6|].
destruct b; [|exact R7].
destruct R7 as (S1 & S2 & S3 & ob & osz & S4 & S5).
split; [exact S1|]. split; [exact S2|]. split; [exact S3|]. exists ob, osz. split; [|exact S5].
apply Ho; auto.
Qed.

(* buffered mode: the pending output is at most a block *)
Lemma c_core_pend : forall obuf sout k sv,
  c_core false obuf sout k sv -> Zlength (sv_pend sv) <= ZSTD_BLOCKSIZE_MAX.
Proof.
intros obuf sout k sv Hc. unfold c_core in Hc. destruct Hc as (_ & _ & _ & Hc).
destruct (sf_stage (c3_s k) =? zdss_init).
{ destruct Hc as [_ ->]. rewrite Zlength_nil. unfold ZSTD_BLOCKSIZE_MAX; lia. }
destruct (sf_stage (c3_s k) =? zdss_loadHeader).
{ destruct Hc as [-> _]. rewrite Zlength_nil. unfold ZSTD_BLOCKSIZE_MAX; lia. }
destruct Hc as (_ & Hf & Hr & _).
unfold c_ring in Hr. destruct Hr as (_ & _ & _ & ostart & oend & _ & _ & _ & _ & _ & Hp & _).
unfold c_frame in Hf. destruct Hf as (_ & _ & _ & _ & _ & Hf).
assert (0 < ZSTD_BLOCKSIZE_MAX) by (unfold ZSTD_BLOCKSIZE_MAX; simpl; lia).
destruct (sv_fp sv) eqn:E; try contradiction; unfold fp_bsm in Hp.
- lia.
- destruct Hf as (_ & _ & Hb & Hb2 & _).
  assert (Z.min (fh_windowSize (zp_h z)) ZSTD_BLOCKSIZE_MAX <= ZSTD_BLOCKSIZE_MAX) by lia. lia.
Qed.

(* ---------- a fresh stream ---------- *)

Lemma walk_nil : forall md sel cur w, series_frames_m md sel cur w [] = ([], TEnd).
Proof. intros. unfold series_frames_m. simpl. destruct (md_magicless md); reflexivity. Qed.

Lemma cur_nil : forall md sel cur w, series_cur md sel cur w [] = cur.
Proof. intros. unfold series_cur. simpl. destruct (md_magicless md); reflexivity. Qed.

Lemma m_rel_init : forall sm, m_rel_cd sm [] [] FP_none [] (sm_cur sm).
Proof.
intros sm. exists [], [], []. split; [reflexivity|]. split; [apply walk_nil|]. split; [apply cur_nil|].
split; reflexivity.
Qed.

Lemma cur_dict_init : forall st k, cur_dict_ok st k (snd (st_sel st)).
Proof.
intros st k dm. unfold st_sel. destruct (dc_set st) as [|e l] eqn:Es.
- simpl. intros E. left. auto.
- destruct (dc_dict st); [|discriminate].
  destruct (_ && _)%bool; discriminate.
Qed.

Definition sv0 : sview := {| sv_fp := FP_none; sv_pend := []; sv_ahead := []; sv_lay := HL_none; sv_dd := None |}.

(* the view of the stream at the call's entry: SR3's, or sv0 at ss_init (ob: the caller's output pointer, maybe NULL;
   the history is on its base nbase gv ob) *)
Definition pro_view_res (gv: globals) (st: dctx_st) (k: cst3) (ob: val) (osz: Z) : Prop :=
  exists sv,
    0 <= ss_stall (dc_ss st) /\
    0 <= sf_nfp (c3_s k) <= ZSTD_NO_FORWARD_PROGRESS_MAX /\
    ((sf_nfp (c3_s k) <= ss_stall (dc_ss st) /\ sf_nfp (c3_s k) < ZSTD_NO_FORWARD_PROGRESS_MAX) \/
     sf_stage (c3_s k) = zdss_init \/
     (sf_stage (c3_s k) = zdss_loadHeader /\ exists hb k0, sv_fp sv = FP_hdr hb /\
        get_frame_header_m (dp_fmt (c3_par k) =? 1) hb = FH_more k0)) /\
    (sf_stage (c3_s k) = zdss_flush -> fp_complete (sv_fp sv) = true -> sv_pend sv <> nil ->
       sf_hostage (c3_s k) = Vint (Int.repr 1)) /\
    c_core (dc_stable st) (Some (nbase gv ob, osz)) (ss_out (dc_ss st)) k sv /\
    sv_dd_ok st k sv /\
    ss_ahead (dc_ss st) = Zlength (sv_ahead sv) /\
    (exists sin0, ss_in (dc_ss st) = sin0 ++ sv_ahead sv) /\
    alive_ok st k sv (ss_in (dc_ss st)) (ss_out (dc_ss st)) /\
    (dc_stable st = true -> sf_stage (c3_s k) <> zdss_init ->
       sf_expOut (c3_s k) = (ob, (vlong osz, vlong (Zlength (ss_out (dc_ss st)))))) /\
    (sf_stage (c3_s k) <= zdss_loadHeader -> sv_ahead sv = nil) /\
    bytes_ok (ss_in (dc_ss st)).

Lemma pro_view : forall gv st k ob osz,
  (cold01 (c3_fs k) /\ sf_inSize (c3_s k) + sf_outSize (c3_s k) <= 2 ^ 32) ->
  base_rel3 st k ->
  (dc_ss st <> ss_init -> ss_err (dc_ss st) = false ->
     SR3 gv st k \/ (dc_ss st = ss_restart /\ sf_stage (c3_s k) = 0)) ->
  ss_err (dc_ss st) = false ->
  (dc_stable st = true ->
     match ss_obuf (dc_ss st) with Some (ob', osz') => ob' = ob /\ osz' = osz | None => True end) ->
  pro_view_res gv st k ob osz.
Proof.
intros gv st k ob osz HF Hb HSR0 Herr Hsob. unfold pro_view_res.
(* a new stream (ss_init, or ss_restart after a setter or a one-shot: the same empty state but for the stall
   count, and a count of calls without progress within its bound), or a running one (SR3) *)
assert (HSR: ((dc_ss st = ss_init \/ dc_ss st = ss_restart) /\ sf_stage (c3_s k) = 0) \/
             (dc_ss st <> ss_init /\ SR3 gv st k)).
{ destruct (Classical_Prop.classic (dc_ss st = ss_init)) as [E | E].
  - left. split; [left; exact E|].
    destruct Hb as (_ & _ & _ & _ & _ & _ & (_ & Hi) & _). exact (proj1 (Hi E)).
  - destruct (HSR0 E Herr) as [H | [H1 H2]]; [right; split; assumption | left; split; [right|]; assumption]. }
destruct HSR as [[E Hst] | [E HSR]].
- destruct HF as [Hd Hz].
  destruct Hb as (_ & _ & _ & _ & _ & _ & (Hnfp & _) & _).
  exists sv0.
  assert (Hpr: (sf_nfp (c3_s k) <= ss_stall (dc_ss st) /\ sf_nfp (c3_s k) < ZSTD_NO_FORWARD_PROGRESS_MAX) \/
               sf_stage (c3_s k) = zdss_init \/
               (sf_stage (c3_s k) = zdss_loadHeader /\ exists hb k0, sv_fp sv0 = FP_hdr hb /\
                  get_frame_header_m (dp_fmt (c3_par k) =? 1) hb = FH_more k0))
    by (right; left; exact Hst).
  destruct E as [E | E]; rewrite E in Hpr |- *; simpl.
  all: split; [unfold ss_init, ss_restart, ZSTD_NO_FORWARD_PROGRESS_MAX; simpl; lia|].
  all: split; [exact (Hnfp Herr)|].
  all: split; [exact Hpr|].
  all: split; [intros _ Hc; discriminate|].
  all: split; [
    unfold c_core; rewrite Hst; simpl; split; [left; auto|]; split; [exact Hd|]; split; [exact Hz|];
    split; [left|]; reflexivity |].
  all: split; [intros Hr; rewrite Hst in Hr; unfold zdss_read in Hr; lia|].
  all: split; [reflexivity|]. all: split; [exists []; reflexivity|].
  all: split; [
    right; exists (sm_cur (sm_of st)); split; [apply m_rel_init|]; split;
    [simpl; apply cur_dict_init | intros _ Hne; rewrite Hst in Hne; contradiction] |].
  all: split; [intros _ Hne; contradiction|]. all: split; [reflexivity | constructor].
- destruct HSR as (sv & Hc & Hby & Hsa & Hsin & Hm). unfold c_rel in Hc.
  destruct Hc as (N0 & N1 & N2 & NT & Hexp & Hah & Hdd & Hcore).
  exists sv. split; [exact N0|]. split; [exact N1|]. split; [exact N2|]. split; [exact NT|].
  split; [|split; [exact Hdd | split; [exact Hsa | split; [exact Hsin | split; [exact Hm|split; [|split; [exact Hah | exact Hby]]]]]]].
  + eapply c_core_obuf; [exact Hcore|]. intros Hs x Hx. specialize (Hsob Hs).
    destruct (ss_obuf (dc_ss st)) as [[ob' osz'] |]; [| discriminate]. simpl in Hx.
    inversion Hx; subst x. destruct Hsob; subst; auto.
  + intros Hs Hne. destruct (Hexp Hs Hne) as (ob' & osz' & Ho & He). specialize (Hsob Hs).
    rewrite Ho in Hsob. destruct Hsob; subst; exact He.
Qed.

Lemma pro_view_exp : forall gv st k ob osz, pro_view_res gv st k ob osz ->
  dc_stable st = true -> sf_stage (c3_s k) <> zdss_init ->
  sf_expOut (c3_s k) = (ob, (vlong osz, vlong (Zlength (ss_out (dc_ss st))))).
Proof.
intros gv st k ob osz (sv & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H.
Qed.

(* ---------- ZSTD_checkOutBuffer's result ---------- *)

Lemma veqb_refl : forall v, veqb v v = true.
Proof. intros v. unfold veqb. destruct (Val.eq v v); congruence. Qed.

Lemma check_out_zero : forall st k ob osz opos,
  base_rel3 st k ->
  (dc_stable st = true -> sf_stage (c3_s k) <> zdss_init ->
     sf_expOut (c3_s k) = (ob, (vlong osz, vlong (Zlength (ss_out (dc_ss st)))))) ->
  (dc_stable st = true -> opos = Zlength (ss_out (dc_ss st))) ->
  check_out (c3_stable k) (sf_stage (c3_s k)) (sf_expOut (c3_s k)) ob osz opos = 0.
Proof.
intros st k ob osz opos Hb Hexp Hpos. unfold check_out. destruct Hb as [Hs _]. rewrite Hs.
destruct (dc_stable st) eqn:Es; simpl; [|auto].
destruct (sf_stage (c3_s k) =? zdss_init) eqn:Ez; simpl; [auto|].
apply Z.eqb_neq in Ez. rewrite (Hexp eq_refl Ez). simpl. rewrite (Hpos eq_refl), !veqb_refl. reflexivity.
Qed.

(* ---------- the loop invariant at the loop's entry ---------- *)

Lemma a_sin_eq : forall (a: dsa) sin0 ah,
  ss_in (dc_ss (a_st a)) = sin0 ++ ah -> ss_ahead (dc_ss (a_st a)) = Zlength ah -> a_sin a = sin0.
Proof.
intros a sin0 ah E H. unfold a_sin. rewrite H, E, Zlength_app.
replace (Zlength sin0 + Zlength ah - Zlength ah) with (Zlength sin0) by lia.
rewrite sublist_app1 by (try rep_lia; pose proof (Zlength_nonneg sin0); lia).
apply sublist_same; lia.
Qed.

Lemma pro_call_inv : forall (a: dsa) k sv,
  dsa_ok a ->
  base_rel3 (a_st a) k -> bytes_ok (ss_in (dc_ss (a_st a))) ->
  0 <= sf_nfp (c3_s k) <= ZSTD_NO_FORWARD_PROGRESS_MAX ->
  ((sf_nfp (c3_s k) <= ss_stall (dc_ss (a_st a)) /\ sf_nfp (c3_s k) < ZSTD_NO_FORWARD_PROGRESS_MAX) \/
   sf_stage (c3_s k) = zdss_init \/
   (sf_stage (c3_s k) = zdss_loadHeader /\ exists hb k0, sv_fp sv = FP_hdr hb /\
      get_frame_header_m (dp_fmt (c3_par k) =? 1) hb = FH_more k0)) ->
  (sf_stage (c3_s k) = zdss_flush -> fp_complete (sv_fp sv) = true -> sv_pend sv <> nil ->
     sf_hostage (c3_s k) = Vint (Int.repr 1)) ->
  (dc_stable (a_st a) = true -> sf_stage (c3_s k) <> zdss_init ->
     sf_expOut (c3_s k) = (a_obf a, (vlong (a_osz a), vlong (Zlength (ss_out (dc_ss (a_st a))))))) ->
  c_core (dc_stable (a_st a)) (Some (a_ob a, a_osz a)) (ss_out (dc_ss (a_st a))) k sv ->
  sv_dd_ok (a_st a) k sv ->
  ss_ahead (dc_ss (a_st a)) = Zlength (sv_ahead sv) ->
  (exists sin0, ss_in (dc_ss (a_st a)) = sin0 ++ sv_ahead sv) ->
  alive_ok (a_st a) k sv (ss_in (dc_ss (a_st a))) (ss_out (dc_ss (a_st a))) ->
  call_inv a (c3_raise k (dp_wmax (dc_par (a_st a)))) sv (a_ipos a) (a_opos a) (a_oc a) [].
Proof.
intros a k sv Hok Hb Hby N1 N2 NT Hexp Hc Hdd Hsa [sin0 Hsin] Hm.
pose proof (a_sin_eq a sin0 (sv_ahead sv) Hsin Hsa) as Ea.
pose proof (base_call_raise _ _ Hb) as Hbc.
destruct Hok as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hopos & _ & Hoc & Hipos & _ & _ & _ & HI2 & _ & Hpos & _).
destruct Hb as (Hs & Hp & Hst & Hd & Hsc & Hfp & Hi & _).
unfold call_inv. cbv zeta. rewrite Ea. rewrite !sublist_nil, !app_nil_r. simpl. rewrite <- Hsin.
split; [lia|]. split; [lia|]. split; [auto|]. split; [auto|]. split; [rewrite Zlength_nil; lia|].
split; [reflexivity|]. split; [constructor|].
split; [exact Hbc|].
split; [rewrite Hsin in Hby; apply Forall_app in Hby; tauto|].
split; [exact N1|]. split; [right; right; exact N2|].
split; [intros E; apply Hi; auto|]. split; [exact Hc|]. split; [exact Hdd|]. split; [exact HI2|].
split; [auto|]. split; [|split; [exact Hm|]].
- intros _ Hst1. rewrite Hst1 in Hc. rewrite Zlength_nil. apply c_core_pend in Hc. lia.
- split; [intros _ hb _; exists hb, (a_ipos a); split; [lia|]; rewrite sublist_nil, app_nil_r; auto|].
  split; [reflexivity|]. split.
  + intros Hs1 Hne. rewrite (Hexp Hs1 Hne), (Hpos Hs1). reflexivity.
  + intros H1 H2 H3 H4. rewrite (NT H1 H2 H3) in H4.
    assert (Int.unsigned (Int.repr 1) = Int.unsigned (Int.repr 0)) by congruence.
    rewrite !Int.unsigned_repr in H by rep_lia. lia.
Qed.

Lemma pro_start_ok : forall (a: dsa) k sv,
  c_core (dc_stable (a_st a)) (Some (a_ob a, a_osz a)) (ss_out (dc_ss (a_st a))) k sv ->
  bytes_ok (ss_in (dc_ss (a_st a))) ->
  ss_ahead (dc_ss (a_st a)) = Zlength (sv_ahead sv) ->
  (exists sin0, ss_in (dc_ss (a_st a)) = sin0 ++ sv_ahead sv) ->
  alive_ok (a_st a) k sv (ss_in (dc_ss (a_st a))) (ss_out (dc_ss (a_st a))) ->
  0 <= ss_stall (dc_ss (a_st a)) ->
  start_ok a.
Proof.
intros a k sv Hc Hby Hsa [sin0 Hsin] Hm Hst0. unfold start_ok.
split.
{ destruct Hm as [Hm | (cd & Hm & _)].
  - intros s Hp. cbv zeta. rewrite (proj1 Hm s Hp). intros [E|E]; discriminate.
  - eapply content_ok_of_m_rel_cd; eauto. }
rewrite Hsa. split.
- destruct Hc as [Ha _]. destruct Ha as [[_ ->]|[[_ ->]|(_ & _ & _ & -> & _)]]; auto.
- split; [|exact Hst0]. rewrite Hsin, Zlength_app. pose proof (Zlength_nonneg sin0). lia.
Qed.


(* ---------- the pieces of the prologue (one file each, for the checker's time budget) ---------- *)

(* the statement after the first n top-level statements *)
Fixpoint sdrop (n: nat) (s: statement) : statement :=
  match n with O => s | S n' => match s with Ssequence _ t => sdrop n' t | _ => s end end.

(* the continuation (the loop, with the exact conjunct ex_call), as one opaque hypothesis while the prologue runs *)
Definition pro_rest (Espec: OracleKind) DENT TABS (BR: blrel) (a: dsa) (REST: statement) : Prop :=
  forall w, call_inv a (w_k w) (w_sv w) (w_ipc w) (w_opc w) (w_oc w) (w_dl w) -> w_smw w = 1 ->
    loop_extra w -> start_ok a -> exit_ok a w -> entry_ok a w -> untouched_ok a w -> ex_call a w ->
    semax (ds_Delta DENT TABS BR) (PROPx [] (LOCALx (ds_LI_L a w) (SEPx (ds_LI_S DENT TABS a w))))
      REST (ds_R_x DENT TABS BR a).

(* what every piece knows; the context's exact relation (DC3_of's last conjunct) gives the loop's start in the
   model *)
Definition pro_hyp (Espec: OracleKind) DENT TABS (BR: blrel) (a: dsa) (REST: statement) (k: cst3) : Prop :=
  (DENT_OK DENT /\ TABS_OK TABS /\ dsa_ok a /\ base_rel3 (a_st a) k /\
   pro_view_res (a_gv a) (a_st a) k (a_obf a) (a_osz a) /\ pro_rest Espec DENT TABS BR a REST /\
   ex_on3 SR3 (a_st a) k)%type.

(* the separation part before `op = ostart` *)
Definition pro_S0 DENT TABS (a: dsa) (k: cst3) : list mpred :=
  [data_at_ Tsh (tptr tschar) (a_vop a); pws_pred (a_W a); mem_mgr (a_gv a); zstd_globals (a_gv a);
   ctx_rep3 DENT TABS (a_gv a) (a_d a) k;
   dict_res (DD3x DENT) (a_gv a) Ews (dc_dict (a_st a));
   set_res (DD3x DENT) (a_gv a) Ews (dc_set (a_st a)) (dc_dict (a_st a));
   data_at (a_sho a) t_outBuffer (a_obf a, (Vlong (Int64.repr (a_osz a)), Vlong (Int64.repr (a_opos a)))) (a_outp a);
   data_at (a_shi a) t_inBuffer (a_ibf a, (Vlong (Int64.repr (a_isz a)), Vlong (Int64.repr (a_ipos a)))) (a_inp a);
   data_at (a_shob a) (tarray tuchar (a_osz a)) (a_oc a) (a_ob a);
   data_at (a_shb a) (tarray tuchar (a_isz a)) (zbytes (a_ibs a)) (a_ib a)].

(* the locals before statement 2 (istart set) and before statement 5 (dst set) *)
Definition pro_L2 (a: dsa) : list localdef :=
  [lvar _op (tptr tschar) (a_vop a); gvars (a_gv a); temp _zds (a_d a); temp _output (a_outp a);
   temp _input (a_inp a); temp _src (a_ib a); temp _istart (offset_val (a_ipos a) (a_ib a))].

Definition pro_L5 (a: dsa) : list localdef :=
  [lvar _op (tptr tschar) (a_vop a); gvars (a_gv a); temp _zds (a_d a); temp _output (a_outp a);
   temp _input (a_inp a); temp _src (a_ib a); temp _istart (offset_val (a_ipos a) (a_ib a));
   temp _iend (offset_val (a_isz a) (a_ib a)); temp _ip (offset_val (a_ipos a) (a_ib a)); temp _dst (a_ob a)].

(* the loop's first state (from statement 7 on: op set, someMoreWork = 1) *)
Definition pro_w0 (a: dsa) (k: cst3) : lw :=
  {| w_smw := 1; w_k := k; w_sv := sv0; w_ipc := a_ipos a; w_opc := a_opos a; w_oc := a_oc a; w_dl := [] |}.

End CM_Q3ProPure_1.

(* `do { } while (0)` *)
Ltac skip_loop :=
  match goal with |- semax _ ?P _ _ =>
    forward_loop P break: P;
      [solve [apply andp_left2, derives_refl | entailer!] |
       forward; try solve [apply andp_left2, derives_refl | entailer!] | ] end.

(* `do { c } while (0)`, c ending normally (the then-branch of an unreachable check returns) *)
Ltac do0_loop :=
  match goal with |- semax _ ?P _ _ =>
    forward_loop P break: P;
      [solve [apply andp_left2, derives_refl | entailer!] | | ] end.

Ltac z0 := match goal with Hx: Int64.repr ?x = Int64.zero |- _ => apply repr64_0 in Hx; [ | rep_lia] end.
