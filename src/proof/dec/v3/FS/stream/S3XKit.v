(* The model side of the stream's exact claim, for the pieces of the proof of ZSTD_decompressStream (plain Coq on
   S3Main.ex_call and model/ExStreamFacts.v):
   - ex_loop: the model's loop at state zi (input position ip, bytes dl delivered), from the state z0 of the calls
     before this one, with fuel f above the potential, ends as the call's whole loop (S3Main.a_loop);
   - ex_call_go / ex_call_stop: what ex_call gives while the loop goes on / once it stopped; ex_call_next_mk,
     ex_call_stop_mk: how a piece re-establishes it;
   - ex_call_start: the loop's first iteration from the context's exact relation;
   - ex_loop_next, ex_loop_stop, ex_loop_err, ex_loop_early: one iteration (ExStream.one_iter at model/Exact.v's
     instance) that goes on, stops, fails, or returns early; ex_loop_fall: a fall-through of the switch inside it;
   - ex_epi: the call's outcome (Exact.zs_call) and the next state of the history from the loop's stop. *)
Require Import Zstd.proof.dec.v3.FS.stream.S3Main.
Require Import Zstd.proof.model.ExCall Zstd.proof.model.ExStreamFacts.
Require Zstd.proof.model.ExStream Zstd.proof.model.ExHuf Zstd.proof.model.ExBlock Zstd.proof.model.Exact.

(* one iteration of the loop at model/Exact.v's instance *)
Definition one_iter_x (inp: list Z) (room: Z) (z: zstate_x) (ip: Z) (dl: list Z) : ExStream.lstep XS :=
  ExStream.one_iter XS (ExBlock.xst_begin ExHuf.xhuf) Exact.xblock xframe1 inp room z ip dl.

Definition ex_loop (a: dsa) (z0 zi: zstate_x) (f: nat) (ip: Z) (dl: list Z) : Prop :=
  zs_run_x (ss_calls (dc_ss (a_st a))) = Some z0 /\ zinv_x z0 /\ zinv_x zi /\
  zpot XS (a_xin a) zi ip < Z.of_nat f /\ z_loop_x f (a_xin a) (a_xroom a) zi ip dl = a_loop a z0.

(* the streaming fields, frame fields and tables of a loop state, as the exact relation sees them *)
Definition w_sx (w: lw) : sfields := sf_strip (c3_s (w_k w)).
Definition w_fs (w: lw) : fstate := c3_fs (w_k w).
Definition w_tabs (w: lw) : tabs3 := c3_tabs (w_k w).

(* ---------- ex_call ---------- *)

Lemma ex_call_go (a: dsa) (w: lw) :
  ex_call a w -> w_smw w = 1 -> fresh_cfg (a_st a) ->
  exists z0 zi f, ex_loop a z0 zi f (w_ipc w - a_ipos a) (w_dl w) /\
    ((w_ipc w = a_ipos a /\ w_dl w = nil /\ zi = z0 /\ zrel zi (w_sx w) (w_fs w) (w_tabs w)) \/
     zrel_end zi (w_sx w) (w_fs w) (w_tabs w)).
Proof.
  intros H Hs Hf. destruct (H Hf) as (z0 & zi & f & Hr & H0 & Hi & Hgo & _).
  destruct (Hgo Hs) as (Hp & Hl & Hz). exists z0, zi, f. unfold ex_loop. tauto.
Qed.

Lemma ex_call_stop (a: dsa) (w: lw) :
  ex_call a w -> w_smw w = 0 -> fresh_cfg (a_st a) ->
  exists z0 zi, zs_run_x (ss_calls (dc_ss (a_st a))) = Some z0 /\ zinv_x z0 /\ zinv_x zi /\
    a_loop a z0 = ExStream.LStop XS zi (w_ipc w - a_ipos a) (w_dl w) /\ zrel_end zi (w_sx w) (w_fs w) (w_tabs w).
Proof.
  intros H Hs Hf. destruct (H Hf) as (z0 & zi & f & Hr & H0 & Hi & _ & Hst).
  destruct (Hst Hs) as (Hl & Hz). exists z0, zi. tauto.
Qed.

(* after an iteration that goes on *)
Lemma ex_call_next_mk (a: dsa) (w: lw) :
  w_smw w = 1 ->
  (fresh_cfg (a_st a) ->
     exists z0 zi f, ex_loop a z0 zi f (w_ipc w - a_ipos a) (w_dl w) /\ zrel_end zi (w_sx w) (w_fs w) (w_tabs w)) ->
  ex_call a w.
Proof.
  intros Hs H Hf. destruct (H Hf) as (z0 & zi & f & (Hr & H0 & Hi & Hp & Hl) & Hz).
  exists z0, zi, f. split; [exact Hr|]. split; [exact H0|]. split; [exact Hi|].
  split; [intros _; split; [exact Hp|]; split; [exact Hl | right; exact Hz] | intros E; congruence].
Qed.

(* once the loop stops (someMoreWork = 0) *)
Lemma ex_call_stop_mk (a: dsa) (w: lw) :
  w_smw w = 0 ->
  (fresh_cfg (a_st a) ->
     exists z0 zi, zs_run_x (ss_calls (dc_ss (a_st a))) = Some z0 /\ zinv_x z0 /\ zinv_x zi /\
       a_loop a z0 = ExStream.LStop XS zi (w_ipc w - a_ipos a) (w_dl w) /\
       zrel_end zi (w_sx w) (w_fs w) (w_tabs w)) ->
  ex_call a w.
Proof.
  intros Hs H Hf. destruct (H Hf) as (z0 & zi & Hr & H0 & Hi & Hl & Hz).
  exists z0, zi, O. split; [exact Hr|]. split; [exact H0|]. split; [exact Hi|].
  split; [intros E; congruence | intros _; split; [exact Hl | exact Hz]].
Qed.

(* the loop's first iteration: the state of the calls before this one, related to the context at the call's
   start (FSRep3.ex_on3 with S3XRel.xrel3) *)
Lemma ex_call_start (a: dsa) (w: lw) :
  (fresh_cfg (a_st a) -> xrel3 (ss_calls (dc_ss (a_st a))) (w_sx w) (w_fs w) (w_tabs w)) ->
  w_smw w = 1 -> w_ipc w = a_ipos a -> w_dl w = nil -> ex_call a w.
Proof.
  intros H Hs Hi Hd Hf. destruct (H Hf) as (z0 & Hr & Hz0 & Hz).
  exists z0, z0, (zfuel (a_xin a)). split; [exact Hr|]. split; [exact Hz0|]. split; [exact Hz0|].
  split; [| intros E; congruence]. intros _.
  rewrite Hi, Hd, Z.sub_diag. split; [apply zpot_start |]. split; [reflexivity |].
  left. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. exact Hz.
Qed.

(* ---------- one iteration ---------- *)

Lemma ex_loop_next (a: dsa) (z0 zi: zstate_x) (f: nat) (ip: Z) (dl: list Z) (z1: zstate_x) (ip1: Z) (dl1: list Z) :
  bytes_ok (a_xin a) -> 0 <= ip <= Zlength (a_xin a) -> Zlength dl <= a_xroom a -> ex_loop a z0 zi f ip dl ->
  one_iter_x (a_xin a) (a_xroom a) zi ip dl = ExStream.LNext XS z1 ip1 dl1 ->
  exists f1, ex_loop a z0 z1 f1 ip1 dl1 /\ ip <= ip1 <= Zlength (a_xin a).
Proof.
  intros Hb Hip Hdl (Hr & H0 & Hi & Hp & Hl) He.
  pose proof (one_iter_ok_x (a_xin a) (a_xroom a) zi ip dl Hi Hb Hip Hdl) as Ho.
  unfold one_iter_x in He. rewrite He in Ho. destruct Ho as (Hi1 & Hip1 & Hp1 & _).
  destruct f as [|f1]; [pose proof (zpot_pos XS (a_xin a) zi ip (proj2 Hip)); simpl in Hp; lia |].
  exists f1. split; [| exact Hip1].
  unfold z_loop_x in Hl. rewrite z_loop_S in Hl. rewrite He in Hl.
  split; [exact Hr|]. split; [exact H0|]. split; [exact Hi1|]. split; [rewrite Nat2Z.inj_succ in Hp; lia | exact Hl].
Qed.

Lemma ex_loop_stop (a: dsa) (z0 zi: zstate_x) (f: nat) (ip: Z) (dl: list Z) (z1: zstate_x) (ip1: Z) (dl1: list Z) :
  bytes_ok (a_xin a) -> 0 <= ip <= Zlength (a_xin a) -> Zlength dl <= a_xroom a -> ex_loop a z0 zi f ip dl ->
  one_iter_x (a_xin a) (a_xroom a) zi ip dl = ExStream.LStop XS z1 ip1 dl1 ->
  a_loop a z0 = ExStream.LStop XS z1 ip1 dl1 /\ zinv_x z1.
Proof.
  intros Hb Hip Hdl (Hr & H0 & Hi & Hp & Hl) He.
  pose proof (one_iter_ok_x (a_xin a) (a_xroom a) zi ip dl Hi Hb Hip Hdl) as Ho.
  unfold one_iter_x in He. rewrite He in Ho.
  destruct f as [|f1]; [pose proof (zpot_pos XS (a_xin a) zi ip (proj2 Hip)); simpl in Hp; lia |].
  unfold z_loop_x in Hl. rewrite z_loop_S, He in Hl. split; [symmetry; exact Hl | exact Ho].
Qed.

(* a fall-through of the C switch inside one iteration (zdss_loadHeader into zdss_read, zdss_read into zdss_load):
   the model's iteration from zi is the iteration of the next case's state zj (st_header_done ends with st_read on
   the stage-read state, st_read with st_load on the stage-load state), so the loop goes on from zj *)
Lemma ex_loop_fall (a: dsa) (z0 zi zj: zstate_x) (f: nat) (ip: Z) (dl: list Z) :
  ex_loop a z0 zi f ip dl -> zinv_x zj ->
  one_iter_x (a_xin a) (a_xroom a) zj ip dl = one_iter_x (a_xin a) (a_xroom a) zi ip dl ->
  zpot XS (a_xin a) zj ip <= zpot XS (a_xin a) zi ip ->
  ex_loop a z0 zj f ip dl.
Proof.
  intros (Hr & H0 & Hi & Hp & Hl) Hj He Hpj.
  split; [exact Hr|]. split; [exact H0|]. split; [exact Hj|]. split; [lia|].
  rewrite <- Hl. unfold z_loop_x. destruct f as [|f1]; [reflexivity|].
  rewrite !z_loop_S. unfold one_iter_x in He. rewrite He. reflexivity.
Qed.

(* the call's outcome is the epilogue of its loop *)
Lemma a_loop_step (a: dsa) (z0: zstate_x) :
  zstep_x z0 (a_xin a, a_xroom a) =
  if a_xroom a <? 0 then None else z_epi XS (a_xin a) (a_xroom a) (a_loop a z0).
Proof. reflexivity. Qed.

Lemma ex_loop_err (a: dsa) (z0 zi: zstate_x) (f: nat) (ip: Z) (dl: list Z) :
  ex_loop a z0 zi f ip dl ->
  one_iter_x (a_xin a) (a_xroom a) zi ip dl = ExStream.LErr XS ->
  Exact.zs_call (ss_calls (dc_ss (a_st a))) (a_xin a, a_xroom a) = None.
Proof.
  intros (Hr & H0 & Hi & Hp & Hl) He.
  destruct f as [|f1]; [unfold z_loop_x in Hl; simpl in Hl |].
  - rewrite zs_call_x, Hr, a_loop_step, <- Hl. destruct (a_xroom a <? 0); reflexivity.
  - unfold z_loop_x in Hl. rewrite z_loop_S in Hl. unfold one_iter_x in He. rewrite He in Hl.
    rewrite zs_call_x, Hr, a_loop_step, <- Hl. destruct (a_xroom a <? 0); reflexivity.
Qed.

(* an error return of the code where the model fails too (S3Main.ex_err) *)
Lemma ex_err_of_loop (a: dsa) (r: Z) :
  (fresh_cfg (a_st a) -> exists z0 zi f ip dl, ex_loop a z0 zi f ip dl /\
     one_iter_x (a_xin a) (a_xroom a) zi ip dl = ExStream.LErr XS) ->
  ex_err a r.
Proof.
  intros H Hf. right. destruct (H Hf) as (z0 & zi & f & ip & dl & Hl & He). eapply ex_loop_err; eauto.
Qed.

(* the early return of a partial frame header (the hint) *)
Lemma ex_loop_early (a: dsa) (z0 zi: zstate_x) (f: nat) (ip: Z) (dl: list Z) (z1: zstate_x) (r: Z) :
  0 <= a_xroom a -> 0 <= ip <= Zlength (a_xin a) -> ex_loop a z0 zi f ip dl ->
  one_iter_x (a_xin a) (a_xroom a) zi ip dl = ExStream.LEarly XS z1 r ->
  Exact.zs_call (ss_calls (dc_ss (a_st a))) (a_xin a, a_xroom a) =
    Some (r, Zlength (a_xin a), nil, ExStream.zs_nfp XS z1, 0) /\
  zs_run_x (ss_calls (dc_ss (a_st a)) ++ [(a_xin a, a_xroom a)]) = Some z1.
Proof.
  intros Hro Hip (Hr & H0 & Hi & Hp & Hl) He.
  assert (Hs: zstep_x z0 (a_xin a, a_xroom a) = Some (z1, (r, Zlength (a_xin a), nil, ExStream.zs_nfp XS z1, 0))).
  { rewrite a_loop_step. destruct (Z.ltb_spec (a_xroom a) 0); [lia|].
    destruct f as [|f1]; [pose proof (zpot_pos XS (a_xin a) zi ip (proj2 Hip)); simpl in Hp; lia |].
    unfold z_loop_x in Hl. rewrite z_loop_S in Hl. unfold one_iter_x in He. rewrite He in Hl.
    rewrite <- Hl. reflexivity. }
  exact (zs_call_x_step _ _ _ _ _ Hr Hs).
Qed.

(* ---------- the epilogue ---------- *)

Lemma ex_epi (a: dsa) (z0 z1: zstate_x) (ip: Z) (dl: list Z) z' o :
  zs_run_x (ss_calls (dc_ss (a_st a))) = Some z0 -> 0 <= a_xroom a ->
  a_loop a z0 = ExStream.LStop XS z1 ip dl ->
  z_epi XS (a_xin a) (a_xroom a) (ExStream.LStop XS z1 ip dl) = Some (z', o) ->
  Exact.zs_call (ss_calls (dc_ss (a_st a))) (a_xin a, a_xroom a) = Some o /\
  zs_run_x (ss_calls (dc_ss (a_st a)) ++ [(a_xin a, a_xroom a)]) = Some z'.
Proof.
  intros Hr Hro Hl He.
  assert (Hs: zstep_x z0 (a_xin a, a_xroom a) = Some (z', o)).
  { rewrite a_loop_step. destruct (Z.ltb_spec (a_xroom a) 0); [lia|]. rewrite Hl. exact He. }
  exact (zs_call_x_step _ _ _ _ _ Hr Hs).
Qed.

Lemma ex_epi_none (a: dsa) (z0 z1: zstate_x) (ip: Z) (dl: list Z) :
  zs_run_x (ss_calls (dc_ss (a_st a))) = Some z0 ->
  a_loop a z0 = ExStream.LStop XS z1 ip dl ->
  z_epi XS (a_xin a) (a_xroom a) (ExStream.LStop XS z1 ip dl) = None ->
  Exact.zs_call (ss_calls (dc_ss (a_st a))) (a_xin a, a_xroom a) = None.
Proof.
  intros Hr Hl He. rewrite zs_call_x, Hr, a_loop_step, Hl, He. destruct (a_xroom a <? 0); reflexivity.
Qed.
