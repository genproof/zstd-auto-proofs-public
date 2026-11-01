(* FS3 streaming: the epilogue of ZSTD_decompressStream, the pure side: the states after the
   epilogue's writes and what each return needs (epi_ok: Spec_api6.stream_post, base_rel3, SR3, the progress claim
   Spec_api6.stream_progress, the untouched output cells Spec_api6.stream_untouched).
   Port of v2 src/proof/dec/FS/StreamEpiDefs.v. *)
Require Import Zstd.proof.dec.v3.FS.stream.S3Main Zstd.proof.dec.v3.FS.stream.S3Mem Zstd.proof.model.StreamProgress Zstd.proof.dec.v3.FS.stream.epi.E3Prog.

Section CM_E3Defs_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* ---------- the state between the pieces of the epilogue ---------- *)

(* the stream fields the epilogue writes: streamStage, hostageByte, noForwardProgress, expectedOutBuffer *)
Definition sf_epi (s: sfields) (stage nfp: Z) (hst: val) (ev: reptype t_outBuffer) : sfields :=
  {| sf_stage := stage; sf_inBuff := sf_inBuff s; sf_inSize := sf_inSize s; sf_inPos := sf_inPos s;
     sf_outBuff := sf_outBuff s; sf_outSize := sf_outSize s; sf_outStart := sf_outStart s;
     sf_outEnd := sf_outEnd s; sf_lhSize := sf_lhSize s; sf_hostage := hst; sf_nfp := nfp;
     sf_expOut := ev; sf_hbuf := sf_hbuf s; sf_over := sf_over s; sf_ring := sf_ring s; sf_mem := sf_mem s; sf_held := sf_held s |}.

Definition k_epi (k: cst3) (stage nfp: Z) (hst: val) (ev: reptype t_outBuffer) : cst3 :=
  c3_with_s k (sf_epi (c3_s k) stage nfp hst ev).

Definition epi_ev (a: dsa) (opc: Z) : reptype t_outBuffer := (a_obf a, (vlong (a_osz a), vlong opc)).

Definition k_nfp (a: dsa) (k: cst3) (opc n: Z) : cst3 :=
  k_epi k (sf_stage (c3_s k)) n (sf_hostage (c3_s k)) (epi_ev a opc).

(* what a return with value r, in.pos ipos', out.pos opc, output cells oc1 and context k' needs of the next state
   st': the relational part (Spec_api6.stream_post, base_rel3, SR3's run relation, the progress claim, the
   untouched cells) and the exact part (Spec_api6.stream_exact, the exact relation of st' and k') *)
Definition epi_okr (a: dsa) (k': cst3) (r ipos' opc: Z) (oc1: list val) (st': dctx_st) : Prop :=
  stream_post (a_st a) st' r (a_obf a) (a_osz a) (a_opos a) opc (a_oc a) oc1 (a_ibs a) (a_isz a) (a_ipos a) ipos' /\
  base_rel3 st' k' /\ (dc_ss st' <> ss_init -> ss_err (dc_ss st') = false -> SR3 (a_gv a) st' k') /\
  dc_bl st' = None /\ ep_prog_st a st' r ipos' opc /\
  stream_untouched (a_st a) r (a_osz a) opc (a_oc a) oc1.

Definition epi_xok (a: dsa) (k': cst3) (r ipos' opc: Z) (oc1: list val) (st': dctx_st) : Prop :=
  stream_exact (a_st a) st' r (a_osz a) (a_opos a) opc oc1 (a_ibs a) (a_isz a) (a_ipos a) ipos' /\
  ex_on3 SR3 st' k'.

Definition epi_ok (a: dsa) (k': cst3) (r ipos' opc: Z) (oc1: list val) : Prop :=
  0 <= r <= Int64.max_unsigned /\
  exists st', epi_okr a k' r ipos' opc oc1 st' /\ epi_xok a k' r ipos' opc oc1 st'.

Definition k_sh (k: cst3) (stage: Z) (hst: val) : cst3 :=
  k_epi k stage (sf_nfp (c3_s k)) hst (sf_expOut (c3_s k)).

Definition nit_blk (fstg: Z) : Z := if next_input_type fstg =? 2 then 1 else 0.

(* what each return of the tail needs *)
Definition tail_ok (a: dsa) (k: cst3) (ipc opc: Z) (oc1: list val) : Prop :=
  let s := c3_s k in
  exists e, fs_expected (c3_fs k) = vlong e /\ 0 <= e <= Int64.max_unsigned /\
  (e = 0 ->
     exists os oe h, sf_outStart s = vlong os /\ sf_outEnd s = vlong oe /\ sf_hostage s = Vint h /\
       0 <= os <= Int64.max_unsigned /\ 0 <= oe <= Int64.max_unsigned /\
       (os = oe -> h <> Int.zero -> a_isz a <= ipc -> epi_ok a (k_sh k zdss_read (sf_hostage s)) 1 ipc opc oc1) /\
       (os = oe -> h <> Int.zero -> ipc < a_isz a -> epi_ok a k 0 (ipc + 1) opc oc1) /\
       (os = oe -> h = Int.zero -> epi_ok a k 0 ipc opc oc1) /\
       (os <> oe -> h = Int.zero -> epi_ok a (k_sh k (sf_stage s) (Vint (Int.repr 1))) 1 (ipc - 1) opc oc1) /\
       (os <> oe -> h <> Int.zero -> epi_ok a k 1 ipc opc oc1)) /\
  (e <> 0 ->
     exists fstg ip0, fs_stage (c3_fs k) = Vint (Int.repr fstg) /\ 0 <= fstg <= 7 /\
       sf_inPos s = vlong ip0 /\ 0 <= ip0 <= Int64.max_unsigned /\
       epi_ok a k (e + ZSTD_blockHeaderSize * nit_blk fstg - ip0) ipc opc oc1).

Definition head_ok (a: dsa) (k: cst3) (ipc opc: Z) (oc1: list val) : Prop :=
  let n := sf_nfp (c3_s k) in
  0 <= n <= 16 /\
  (ipc = a_ipos a -> opc = a_opos a -> n + 1 >= 16 -> opc = a_osz a ->
     epi_ok a (k_nfp a k opc (n + 1)) (2 ^ 64 - ZSTD_error_noForwardProgress_destFull) ipc opc oc1) /\
  (ipc = a_ipos a -> opc = a_opos a -> n + 1 >= 16 -> opc <> a_osz a -> ipc = a_isz a ->
     epi_ok a (k_nfp a k opc (n + 1)) (2 ^ 64 - ZSTD_error_noForwardProgress_inputEmpty) ipc opc oc1) /\
  (ipc = a_ipos a -> opc = a_opos a -> ~ (n + 1 >= 16 /\ (opc = a_osz a \/ ipc = a_isz a)) ->
     tail_ok a (k_nfp a k opc (n + 1)) ipc opc oc1) /\
  ((ipc <> a_ipos a \/ opc <> a_opos a) -> tail_ok a (k_nfp a k opc 0) ipc opc oc1).

Definition epi_st (a: dsa) (r ipos' a' stall': Z) (dl: list Z) : dctx_st :=
  let st := a_st a in let ss := dc_ss st in
  set_last
    (set_ss st {| ss_in := ss_in ss ++ sublist (a_ipos a + ss_ahead ss) (ipos' + a') (a_ibs a);
                  ss_out := ss_out ss ++ dl; ss_stall := stall'; ss_err := is_error_code r;
                  ss_obuf := if dc_stable st then Some (a_obf a, a_osz a) else None; ss_ahead := a' ;
                  ss_calls := ss_calls ss ++ [(sublist (a_ipos a) (a_isz a) (a_ibs a), a_osz a - a_opos a)] |})
    (Some stream_mark).

Lemma epi_bl : forall (a: dsa) (r ipos' a' stall': Z) (dl: list Z),
  dsa_ok a -> dc_bl (epi_st a r ipos' a' stall' dl) = None.
Proof.
intros a r ipos' a' stall' dl Hok.
destruct Hok as (_ & _ & _ & _ & _ & _ & _ & Hdict & _).
destruct Hdict as (_ & _ & Hbl). exact Hbl.
Qed.

Lemma epi_base : forall (a: dsa) (k: cst3) (r ipos' a' stall': Z) (dl: list Z),
  dsa_ok a -> base_call (a_st a) k ->
  (is_error_code r = false -> 0 <= sf_nfp (c3_s k) <= ZSTD_NO_FORWARD_PROGRESS_MAX) ->
  (dc_ss (epi_st a r ipos' a' stall' dl) = ss_init -> sf_stage (c3_s k) = 0 /\ sf_nfp (c3_s k) = 0) ->
  base_rel3 (epi_st a r ipos' a' stall' dl) k.
Proof.
intros a k r ipos' a' stall' dl Hok Hb Hnfp Hinit.
pose proof (epi_bl a r ipos' a' stall' dl Hok) as Hbl.
destruct Hb as (H1 & H2 & H3 & H4 & H5 & H6 & H7).
unfold base_rel3.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
split; [exact H6|]. split.
- split; [exact Hnfp | exact Hinit].
- split; [intros H; contradiction | unfold epi_st; mem_call_tac].
Qed.

(* the no-progress errors: positions unchanged, nothing delivered *)
Lemma epi_err_ok : forall (a: dsa) (k: cst3) (oc1: list val) (r: Z),
  dsa_ok a -> start_ok a -> base_call (a_st a) k ->
  Zlength oc1 = a_osz a -> sublist 0 (a_opos a) oc1 = sublist 0 (a_opos a) (a_oc a) ->
  ss_stall (dc_ss (a_st a)) + 1 >= ZSTD_NO_FORWARD_PROGRESS_MAX ->
  (r = 2 ^ 64 - ZSTD_error_noForwardProgress_destFull /\ a_opos a = a_osz a \/
   r = 2 ^ 64 - ZSTD_error_noForwardProgress_inputEmpty /\ a_opos a < a_osz a /\ a_ipos a = a_isz a) ->
  (fresh_cfg (a_st a) -> Exact.zs_call (ss_calls (dc_ss (a_st a))) (a_xin a, a_xroom a) = None) ->
  epi_ok a k r (a_ipos a) (a_opos a) oc1.
Proof.
intros a k oc1 r Hok Hst Hb Hoc Hpre Hstall Hr Hx.
pose proof Hok as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hopos & _ & _ & Hipos & _).
destruct Hst as (Hcont & Hah & Hahlen & _).
assert (Herr: is_error_code r = true).
{ unfold is_error_code, ZSTD_error_noForwardProgress_destFull, ZSTD_error_noForwardProgress_inputEmpty in *.
  destruct Hr as [[-> _]|[-> _]]; reflexivity. }
assert (Hr2: 0 <= r <= Int64.max_unsigned).
{ unfold ZSTD_error_noForwardProgress_destFull, ZSTD_error_noForwardProgress_inputEmpty in *.
  destruct Hr as [[-> _]|[-> _]]; rep_lia. }
split; [exact Hr2|].
exists (epi_st a r (a_ipos a) (ss_ahead (dc_ss (a_st a))) (ss_stall (dc_ss (a_st a))) nil).
split.
2:{ (* the model fails on this call too; the next state holds an error, so it carries no exact relation *)
  split.
  - intros Hf. right. cbv zeta. unfold a_xin, a_xroom in Hx. rewrite (Hx Hf). exact Herr.
  - intros _ E. unfold epi_st in E. cbn [set_last set_ss dc_ss ss_err] in E. rewrite Herr in E. discriminate. }
unfold epi_okr. split; [|split; [|split]].
- unfold stream_post.
  exists nil, (ss_stall (dc_ss (a_st a))), (ss_ahead (dc_ss (a_st a))).
  cbv zeta. rewrite !sublist_nil, !app_nil_r.
  split; [lia|]. split; [lia|]. split; [assumption|]. split; [assumption|].
  split; [rewrite Zlength_nil; lia|]. split; [intros _; split; [rewrite ?sublist_nil; reflexivity|constructor]|].
  split; [lia|]. split; [lia|]. split; [right; reflexivity|].
  split; [intros _ H; congruence|].
  split; [unfold epi_st; rewrite ?sublist_nil, ?app_nil_r; reflexivity|].
  split; [intros H; congruence|]. split; [intros H; congruence|].
  split; [intros _ _; unfold ZSTD_BLOCKSIZE_MAX; lia|].
  split.
  + unfold stall_ok. intros _. unfold ZSTD_NO_FORWARD_PROGRESS_MAX in *.
    destruct Hr as [[-> E]|[-> E]]; (repeat split; try lia);
      first [left; split; [reflexivity|lia] | right; repeat split; lia].
  + split.
    * unfold stream_claims_m. intros s0 Hb0 Hs0.
      split; [|split; [|split]].
      -- intros Ht. apply Hcont; auto.
      -- intros Hr0. subst r. discriminate Herr.
      -- intros _ Hf. rewrite Herr in Hf. discriminate.
      -- intros _ _ _ e He. subst r.
         unfold ZSTD_error_noForwardProgress_destFull, ZSTD_error_noForwardProgress_inputEmpty in *.
         destruct Hr as [[E _]|[E _]]; [right; left|right; right; left]; lia.
    * (* an error is not 0 *)
      intros s0 _ _ _ Hr0. subst r. discriminate Herr.
- apply epi_base; auto; [intros E; rewrite Herr in E; discriminate |].
  intros H. unfold epi_st in H. simpl in H. unfold ss_init in H. inversion H. congruence.
- intros _ H. unfold epi_st in H. simpl in H. congruence.
- split; [apply epi_bl; auto|].
  split; [unfold ep_prog_st, stream_progress_m; intros H; rewrite Herr in H; discriminate |
          intros _ H; rewrite Herr in H; discriminate].
Qed.

End CM_E3Defs_1.
