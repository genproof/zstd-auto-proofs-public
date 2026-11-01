(* The API's results on a fresh context, as the harnesses use them.  Spec_api6 states ZSTD_decompressDCtx,
   ZSTD_DCtx_loadDictionary and ZSTD_DCtx_refDDict for a context in any state (after a stream: oneshot_after,
   after_stage) and with any allocator (cm_raised, set_mem).  A harness that calls them on a context before any
   stream (dc_ss = ss_init) with the default allocator (dc_mem = None) gets back the plain results: these lemmas
   and the tactic api_init do that conversion. *)
Require Import Zstd.proof.zstd.Spec_api6.

Lemma set_mem_same (st: dctx_st) : set_mem st (dc_mem st) = st.
Proof. destruct st; reflexivity. Qed.

Lemma cm_raised_none (om: option cmem) : cm_raised None om -> om = None.
Proof. destruct om; simpl; tauto. Qed.

Lemma load_after_init (st st': dctx_st) (r: Z) (dr: dictref) :
  dc_ss st = ss_init -> dc_mem st = None ->
  after_stage (fun st0 r0 st1 => exists om, cm_raised (dc_mem st0) om /\ load_result (set_mem st0 om) st1 r0 dr)
    st r st' ->
  load_result st st' r dr.
Proof.
  intros Hs Hm H. apply after_stage_init in H; auto. destruct H as (om & Hr & H).
  rewrite Hm in Hr. apply cm_raised_none in Hr. subst om. rewrite <- Hm, set_mem_same in H. exact H.
Qed.

Lemma refddict_after_init (st st': dctx_st) (r: Z) (q: val) (dd: ddict_st) :
  q <> nullval -> dc_ss st = ss_init -> dc_mem st = None ->
  after_stage (fun st0 r0 st1 =>
    if eq_dec q nullval then r0 = 0 /\ st1 = set_dict st0 None
    else exists om, cm_raised (dc_mem st0) om /\ refddict_result (set_mem st0 om) st1 r0 q dd) st r st' ->
  refddict_result st st' r q dd.
Proof.
  intros Hq Hs Hm H. apply after_stage_init in H; auto. rewrite if_false in H by auto.
  destruct H as (om & Hr & H).
  rewrite Hm in Hr. apply cm_raised_none in Hr. subst om. rewrite <- Hm, set_mem_same in H. exact H.
Qed.

(* turns the results of ZSTD_decompressDCtx, ZSTD_DCtx_loadDictionary and ZSTD_DCtx_refDDict in the context into
   their plain forms (after_decode, load_result, refddict_result), when tac proves the side conditions
   (dc_ss st = ss_init, dc_mem st = None, q <> nullval) *)
Ltac api_init_with tac :=
  repeat match goal with
  | H: oneshot_after _ _ |- _ => apply oneshot_after_init in H; [| solve [tac]]
  | H: after_stage (fun _ _ _ => exists _, cm_raised _ _ /\ load_result _ _ _ _) _ _ _ |- _ =>
      apply load_after_init in H; [| solve [tac] | solve [tac]]
  | H: after_stage (fun _ _ _ => if eq_dec _ nullval then _ else _) _ _ _ |- _ =>
      apply refddict_after_init in H; [| solve [tac] | solve [tac] | solve [tac]]
  end.

Ltac api_init := api_init_with ltac:(first [reflexivity | assumption | auto | (simpl; auto) | congruence]).
