(* FS3 streaming, case zdss_read: the loop invariant on the branches without a call (end of frame,
   no input, fall into zdss_load); ported from v2 StreamSeg_read.v. *)
Require Import Zstd.proof.dec.v3.FS.stream.read.R3Base.
Local Open Scope logic.

Section CM_R3Inv_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Definition k_stage (k: cst3) (z: Z) : cst3 := c3_with_s k (sf_set_stage (c3_s k) z).

End CM_R3Inv_1.


Ltac zlia := unfold zdss_init, zdss_loadHeader, zdss_read, zdss_load, zdss_flush in *; lia.

Section CM_R3Inv_2.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* end of frame (neededInSize = 0): streamStage := zdss_init *)
Lemma read_end_inv' : forall a k sv ipc opc oc dl,
  call_inv a k sv ipc opc oc dl -> sf_stage (c3_s k) = zdss_read -> fp_complete (sv_fp sv) = true ->
  call_inv a (k_stage k zdss_init) sv ipc opc oc dl.
Proof.
intros a k sv ipc opc oc dl Hi Hs Hc.
unfold call_inv in *.
cbn [k_stage c3_with_s sf_set_stage c3_s c3_stable c3_dict c3_fs c3_par c3_set sf_nfp sf_stage sf_expOut] in *.
destruct Hi as (H1&H2&H3&H4&H5&H6&H7&H8&Hbin&H10&H11&H12&Hcore&Hdd&H15&H16&H17&H18&H19&Hsin&Hexp&HT).
do 10 (split; [assumption|]).
split; [right; right; right; left; reflexivity|].
split; [assumption|].
destruct Hcore as (Hhost&Hcold&Hsz&Hcs). rewrite Hs in Hcs. simpl in Hcs.
destruct Hcs as (_&_&_&_&_&_&Hrd). destruct Hrd as [Hp _]; [reflexivity|].
split.
- unfold c_core. cbn [k_stage c3_with_s sf_set_stage c3_s c3_fs sf_stage sf_hostage sf_inSize sf_outSize].
  split; [|split; [exact Hcold|split; [exact Hsz|simpl; auto]]].
  destruct Hhost as [[Hx _]|[Hx|Hx]]; [rewrite Hs in Hx; discriminate | right; left; auto |].
  right; right. destruct Hx as (?&?&?&?&?&_). repeat split; auto; try (left; reflexivity).
- split; [unfold sv_dd_ok; cbn [k_stage c3_with_s c3_s sf_set_stage sf_stage]; intros X; exfalso; zlia|].
  do 3 (split; [assumption|]).
  split.
  { destruct H18 as [H18|(cd&Hm&Hcd&Hh)]; [left; auto | right; exists cd; split; [auto|split]].
    - unfold cur_dict_ok in *. cbn [c3_with_s c3_dict c3_fs]. exact Hcd.
    - unfold hist_ok. cbn [c3_with_s sf_set_stage c3_s sf_stage]. intros _ Hx. exfalso; apply Hx; reflexivity. }
  split; [intros Hx; exfalso; zlia|].
  split; [assumption|].
  split; [intros _ Hx; exfalso; apply Hx; reflexivity|].
  intros Hx; exfalso; zlia.
Qed.

End CM_R3Inv_2.

Ltac entry_tac := unfold entry_ok; cbn; intros ?Hsm ?Hx;
  first [ discriminate | exfalso; zlia
        | exfalso; match goal with H: (if ?b then _ else _) = _ |- _ => destruct b; zlia end ].

Section CM_R3Inv_3.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.

(* not enough input for the unit, some input left: streamStage := zdss_load *)
Lemma read_load_inv : forall a k sv ipc opc oc dl,
  call_inv a k sv ipc opc oc dl -> sf_stage (c3_s k) = zdss_read -> fp_complete (sv_fp sv) = false ->
  fp_rawbody (sv_fp sv) = false ->
  call_inv a (k_stage k zdss_load) sv ipc opc oc dl.
Proof.
intros a k sv ipc opc oc dl Hi Hs Hc Hr.
unfold zdss_init, zdss_loadHeader, zdss_read, zdss_load, zdss_flush in *.
unfold call_inv in *.
cbn [k_stage c3_with_s sf_set_stage c3_s c3_stable c3_dict c3_fs c3_par c3_set sf_nfp sf_stage sf_expOut] in *.
destruct Hi as (H1&H2&H3&H4&H5&H6&H7&H8&Hbin&H10&H11&H12&Hcore&Hdd&H15&H16&H17&H18&H19&Hsin&Hexp&HT).
do 10 (split; [assumption|]).
split; [destruct H11 as [?|[?|[?|[?|[? _]]]]]; [left|right;left|right;right;left| zlia | zlia]; assumption|].
split; [assumption|].
assert (Hcore0 := Hcore).
destruct Hcore as (Hhost&Hcold&Hsz&Hcs). rewrite Hs in Hcs. simpl in Hcs.
destruct Hcs as (_&Hcf&Hring&_&_&Hnld&Hrd).
destruct Hnld as (Hinpos&Hraw&Hsk); [zlia|].
destruct Hrd as (Hpend&Hoso); [reflexivity|].
split.
{ unfold c_core. cbn [k_stage c3_with_s sf_set_stage c3_s c3_fs c3_tabs sf_stage sf_hostage sf_inPos sf_outStart
                      sf_outEnd sf_ring sf_inSize sf_outSize].
  split; [|split; [exact Hcold|split; [exact Hsz|]]].
  - destruct Hhost as [[Hx _]|[Hx|Hx]]; [rewrite Hs in Hx; zlia | right; left; auto | ].
    destruct Hx as (_&_&Hx&_). congruence.
  - simpl. split; [right; left; reflexivity|]. split; [auto|]. split.
    + unfold c_ring in *. cbn [sf_set_stage sf_inBuff sf_inSize sf_outStart sf_outEnd sf_outSize sf_ring sf_outBuff].
      exact Hring.
    + split; [intros _; zlia|].
      split; [|split; intros Hx; exfalso; zlia].
      intros _. destruct Hraw as [Hraw|[Hl|Hl]]; [congruence| |congruence].
      split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|].
      destruct (sv_fp sv) as [|hb|hdr got|hdr z] eqn:Ef; unfold c_frame in Hcf; [destruct Hcf as (_&_&_&_&_&F); contradiction F ..| |].
      * simpl in Hc, Hsk. destruct Hsk as [Hg|Hg]; [|congruence]. subst got. simpl. split; auto.
      * simpl in Hl |- *. rewrite Hl. simpl. split; auto. }
split; [unfold sv_dd_ok in *; cbn [k_stage c3_with_s c3_s sf_set_stage sf_stage c3_dict] in *; intros _; apply Hdd; zlia|].
do 3 (split; [assumption|]).
split.
{ destruct H18 as [H18|(cd&Hm&Hcd&Hh)]; [left; auto | right; exists cd; split; [auto|split]].
  - unfold cur_dict_ok in *. cbn [c3_with_s c3_dict c3_fs]. exact Hcd.
  - unfold hist_ok in *. cbn [k_stage c3_with_s sf_set_stage c3_s sf_stage sf_inSize sf_outSize sf_ring] in *.
    intros Hx _ _. apply Hh; auto; rewrite Hs; discriminate. }
split; [intros Hx; exfalso; zlia|].
split; [assumption|].
split; [intros Hst _; apply Hexp; [exact Hst | zlia]|].
intros Hx; exfalso; zlia.
Qed.

Lemma k_stage_back : forall k, sf_stage (c3_s k) = zdss_read ->
  c3_with_s (k_stage k zdss_init) (sf_set_stage (sf_set_stage (c3_s k) zdss_init) zdss_read) = k.
Proof.
intros [fs tabs st dc s pr sp l] Hs. destruct s. cbn in Hs |- *. subst. reflexivity.
Qed.

(* someMoreWork = 0 at the end of a frame (streamStage := zdss_init) *)
Lemma read_end_exit : forall a k sv ipc opc oc dl,
  call_inv a k sv ipc opc oc dl -> sf_stage (c3_s k) = zdss_read -> fp_complete (sv_fp sv) = true ->
  fs_expected (c3_fs k) = vlong 0 ->
  exit_ok a {| w_smw := 0; w_k := k_stage k zdss_init; w_sv := sv; w_ipc := ipc; w_opc := opc; w_oc := oc;
               w_dl := dl |}.
Proof.
intros a k sv ipc opc oc dl Hi Hs Hc He.
pose proof Hi as Hi0.
destruct Hi as (H1&H2&H3&H4&H5&H6&H7&H8&Hbin&H10&H11&H12&Hcore&Hdd&H15&H16&H17&H18&H19&Hsin&Hexp&HT).
unfold exit_ok. cbn [w_smw w_k w_sv w_ipc w_opc w_dl k_stage c3_with_s sf_set_stage c3_s c3_fs sf_stage sf_nfp
  sf_outStart sf_outEnd sf_hostage].
intros _.
split; [zlia|]. split; [intros [Hx|Hx]; exfalso; zlia|]. split; [intros Hx; exfalso; zlia|].
split.
{ intros Ei Eo. destruct H11 as [Hx|[Hx|[Hx|[Hx|[Hx _]]]]]; try congruence; try zlia; exact Hx. }
intros _. split; [exact He|].
destruct Hcore as (Hhost&Hcold&Hsz&Hcs). pose proof Hcs as Hcs0. rewrite Hs in Hcs. simpl in Hcs.
destruct Hcs as (_&_&Hring&_&_&_&Hrd). destruct Hrd as [Hp Hoso]; [reflexivity|].
split.
{ destruct Hring as (_&_&Hin&os&oe&Hos&Hoe&Hoo&Hr).
  exists os. split; [exact Hos|]. split; [rewrite <- Hoso; exact Hos|].
  split; [lia|].
  destruct (dc_stable (a_st a)).
  - destruct Hr as (->&_). rep_lia.
  - destruct Hr as (Hoe2&_). pose proof (Zlength_nonneg (sf_ring (c3_s k))).
    pose proof (Z.le_max_r (fp_bsm (sv_fp sv)) 4).
    rep_lia. }
destruct Hhost as [[Hx _]|[[Hh Ha]|Hx]]; [zlia| left; auto |].
destruct Hx as (Hh&Hstb&_&Hal&_&_). right. split; [exact Hh|]. split; [exact Hal|].
rewrite (k_stage_back k Hs). split; [|split].
- destruct Hi0 as (_&_&_&_&_&_&_&_&_&_&_&_&Hc0&_). exact Hc0.
- exact Hdd.
- destruct H18 as [Hd|(cd&_&_&Hh2)]; [left; exact Hd|right; exact Hh2].
Qed.

(* someMoreWork = 0 with all the input read (streamStage stays zdss_read) *)
Lemma read_noin_exit : forall a k sv ipc opc oc dl,
  call_inv a k sv ipc opc oc dl -> sf_stage (c3_s k) = zdss_read -> ipc = a_isz a ->
  exit_ok a {| w_smw := 0; w_k := k; w_sv := sv; w_ipc := ipc; w_opc := opc; w_oc := oc; w_dl := dl |}.
Proof.
intros a k sv ipc opc oc dl Hi Hs Hip.
destruct Hi as (H1&H2&H3&H4&H5&H6&H7&H8&Hbin&H10&H11&_).
unfold exit_ok. cbn [w_smw w_k w_sv w_ipc w_opc w_dl]. intros _.
split; [zlia|]. split; [intros _; exact Hip|]. split; [intros Hx; exfalso; zlia|].
split; [|intros Hx; exfalso; zlia].
intros Ei Eo. destruct H11 as [Hx|[Hx|[Hx|[Hx|[Hx _]]]]]; try congruence; try zlia; exact Hx.
Qed.

End CM_R3Inv_3.
