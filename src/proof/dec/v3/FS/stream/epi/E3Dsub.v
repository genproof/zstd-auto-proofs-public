(* FS3 streaming: the epilogue's pieces without calls are proved in the function's type context with
   no function specifications (much cheaper for Floyd), then lifted to ds_Delta. *)
Require Import Zstd.proof.dec.v3.FS.stream.S3Main.
Local Open Scope logic.

Section CM_E3Dsub_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Definition epi_Delta0 : tycontext := func_tycontext f_ZSTD_decompressStream Vprog nil nil.

Lemma epi_get_V : forall (V: varspecs) id t,
  Maps.PTree.get id (fold_right (fun (v: ident * type) (m: Maps.PTree.t type) => Maps.PTree.set (fst v) (snd v) m)
                       (Maps.PTree.empty type) V) = Some t -> In id (map fst V).
Proof.
induction V as [|[i ty] V IH]; intros id t H; simpl in *.
- rewrite Maps.PTree.gempty in H. discriminate.
- destruct (Pos.eq_dec id i) as [->|Hne]; [left; reflexivity|].
  rewrite Maps.PTree.gso in H by exact Hne. right. eapply IH; eauto.
Qed.

Lemma epi_get_G : forall (G: funspecs) (m: Maps.PTree.t type) id,
  ~ In id (map fst G) ->
  Maps.PTree.get id (fold_right (fun (var: ident * funspec) => Maps.PTree.set (fst var) (type_of_funspec (snd var))) m G)
  = Maps.PTree.get id m.
Proof.
induction G as [|[i f] G IH]; intros m id H; simpl in *; auto.
rewrite Maps.PTree.gso by (intros E; apply H; left; auto). apply IH. intros E; apply H; right; exact E.
Qed.

Lemma epi_subVG : forall (V: varspecs) (G: funspecs),
  forallb (fun id => negb (existsb (Pos.eqb id) (map fst G))) (map fst V) = true ->
  tycontext_subVG V nil V G.
Proof.
intros V G Hd. split; intros id.
- unfold make_tycontext_g. simpl fold_right at 1.
  destruct (in_dec Pos.eq_dec id (map fst G)) as [Hin|Hnin].
  + match goal with |- tycontext.sub_option (Maps.PTree.get id ?m) _ =>
      destruct (Maps.PTree.get id m) as [t|] eqn:E end; simpl; auto.
    exfalso. apply epi_get_V in E. rewrite forallb_forall in Hd. specialize (Hd id E).
    apply Bool.negb_true_iff in Hd. rewrite <- Bool.not_true_iff_false in Hd. apply Hd.
    apply existsb_exists. exists id. split; [exact Hin|apply Pos.eqb_refl].
  + rewrite epi_get_G by exact Hnin.
    match goal with |- tycontext.sub_option (Maps.PTree.get id ?m) _ =>
      destruct (Maps.PTree.get id m); simpl; auto end.
- simpl. auto.
Qed.

Lemma epi_disj : forall DENT TABS BR,
  forallb (fun id => negb (existsb (Pos.eqb id) (map fst (stream_G3 DENT TABS BR)))) (map fst Vprog) = true.
Proof. intros. lazy. reflexivity. Qed.

Lemma epi_Delta_sub : forall DENT TABS BR, tycontext_sub epi_Delta0 (ds_Delta DENT TABS BR).
Proof.
intros DENT TABS BR. unfold epi_Delta0, ds_Delta. apply tycontext_sub_i99. apply epi_subVG. apply epi_disj.
Qed.

Lemma epi_Delta_lift : forall {Espec: OracleKind} DENT TABS BR P c R,
  semax epi_Delta0 P c R -> semax (ds_Delta DENT TABS BR) P c R.
Proof. intros. eapply semax_Delta_subsumption; [apply epi_Delta_sub|exact H]. Qed.

(* one callee: the context with just its specification *)
Lemma epi_subVG1 : forall (V: varspecs) (G: funspecs) (sp: ident * funspec),
  forallb (fun id => negb (existsb (Pos.eqb id) (map fst G))) (map fst V) = true ->
  Maps.PTree.get (fst sp) (make_tycontext_s G) = Some (snd sp) ->
  Maps.PTree.get (fst sp) (make_tycontext_g V G) = Some (type_of_funspec (snd sp)) ->
  tycontext_subVG V [sp] V G.
Proof.
intros V G [i f] Hd Hs Hg. cbn [fst snd] in Hs, Hg. split; intros id.
- unfold make_tycontext_g at 1. cbn [fold_right fst snd].
  destruct (Pos.eq_dec id i) as [->|Hne].
  + rewrite Maps.PTree.gss. simpl. exact Hg.
  + rewrite Maps.PTree.gso by exact Hne. fold (make_tycontext_g V nil).
    pose proof (proj1 (epi_subVG V G Hd) id) as H. exact H.
- apply subsumespec_i. simpl.
  destruct (Pos.eq_dec id i) as [->|Hne].
  + rewrite Maps.PTree.gss. exists f. split; [exact Hs|apply funspec_sub_si_refl].
  + rewrite Maps.PTree.gso by exact Hne. rewrite Maps.PTree.gempty. auto.
Qed.

Definition epi_Delta1 (sp: ident * funspec) : tycontext := func_tycontext f_ZSTD_decompressStream Vprog [sp] nil.

Lemma epi_G3_nodup : forall DENT TABS BR, NoDup (map fst (stream_G3 DENT TABS BR)).
Proof.
intros. apply list_norepet_NoDup. apply compute_list_norepet_e. lazy. reflexivity.
Qed.

Lemma epi_in_fixed : forall DENT TABS BR sp, In sp (FS3_fixed DENT TABS SR3 BR) -> In sp (stream_G3 DENT TABS BR).
Proof.
intros DENT TABS BR sp H. unfold stream_G3, FS3_G. apply in_or_app; left.
repeat (apply in_or_app; right). exact H.
Qed.

Lemma epi_Delta_lift1 : forall {Espec: OracleKind} DENT TABS BR (sp: ident * funspec) P c R,
  In sp (FS3_fixed DENT TABS SR3 BR) ->
  semax (epi_Delta1 sp) P c R -> semax (ds_Delta DENT TABS BR) P c R.
Proof.
intros Espec DENT TABS BR sp P c R Hin H. eapply semax_Delta_subsumption; [|exact H].
assert (Hs: Maps.PTree.get (fst sp) (make_tycontext_s (stream_G3 DENT TABS BR)) = Some (snd sp)).
{ apply semax_prog.make_tycontext_s_distinct; [apply epi_in_fixed; exact Hin|apply epi_G3_nodup]. }
unfold epi_Delta1, ds_Delta. apply tycontext_sub_i99. apply epi_subVG1; [apply epi_disj|exact Hs|].
apply semax_prog.make_tycontext_s_g. exact Hs.
Qed.

Ltac epi_in_fixed_tac :=
  unfold FS3_fixed; simpl In; repeat (first [left; reflexivity | right]).

Lemma epi_nit_in : forall DENT TABS BR, In ZSTD_nextInputType_spec (FS3_fixed DENT TABS SR3 BR).
Proof. intros. epi_in_fixed_tac. Qed.
Lemma epi_nss_in : forall DENT TABS BR, In ZSTD_nextSrcSizeToDecompress_spec (FS3_fixed DENT TABS SR3 BR).
Proof. intros. epi_in_fixed_tac. Qed.
Lemma epi_obc_in : forall DENT TABS BR, In ZSTD_outBuffer_copy_spec (FS3_fixed DENT TABS SR3 BR).
Proof. intros. epi_in_fixed_tac. Qed.

End CM_E3Dsub_1.
