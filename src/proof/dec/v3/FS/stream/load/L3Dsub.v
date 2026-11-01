(* FS3 streaming, case zdss_load: pieces of the case are proved in the function's type context with
   only the specifications they call (much cheaper for Floyd and Qed), then lifted to ds_Delta (after
   epi/E3Dsub.v, generalised to a list of callees). *)
Require Import Zstd.proof.dec.v3.FS.stream.S3Main.
Local Open Scope logic.

Section CM_L3Dsub_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Definition ld_DeltaG (Gs: funspecs) : tycontext := func_tycontext f_ZSTD_decompressStream Vprog Gs nil.

Lemma ld_get_V : forall (V: varspecs) id t,
  Maps.PTree.get id (fold_right (fun (v: ident * type) (m: Maps.PTree.t type) => Maps.PTree.set (fst v) (snd v) m)
                       (Maps.PTree.empty type) V) = Some t -> In id (map fst V).
Proof.
induction V as [|[i ty] V IH]; intros id t H; simpl in *.
- rewrite Maps.PTree.gempty in H. discriminate.
- destruct (Pos.eq_dec id i) as [->|Hne]; [left; reflexivity|].
  rewrite Maps.PTree.gso in H by exact Hne. right. eapply IH; eauto.
Qed.

Lemma ld_get_G : forall (G: funspecs) (m: Maps.PTree.t type) id,
  ~ In id (map fst G) ->
  Maps.PTree.get id (fold_right (fun (var: ident * funspec) => Maps.PTree.set (fst var) (type_of_funspec (snd var))) m G)
  = Maps.PTree.get id m.
Proof.
induction G as [|[i f] G IH]; intros m id H; simpl in *; auto.
rewrite Maps.PTree.gso by (intros E; apply H; left; auto). apply IH. intros E; apply H; right; exact E.
Qed.

Lemma ld_subVG0 : forall (V: varspecs) (G: funspecs),
  forallb (fun id => negb (existsb (Pos.eqb id) (map fst G))) (map fst V) = true ->
  tycontext_subVG V nil V G.
Proof.
intros V G Hd. split; intros id.
- unfold make_tycontext_g. simpl fold_right at 1.
  destruct (in_dec Pos.eq_dec id (map fst G)) as [Hin|Hnin].
  + match goal with |- tycontext.sub_option (Maps.PTree.get id ?m) _ =>
      destruct (Maps.PTree.get id m) as [t|] eqn:E end; simpl; auto.
    exfalso. apply ld_get_V in E. rewrite forallb_forall in Hd. specialize (Hd id E).
    apply Bool.negb_true_iff in Hd. rewrite <- Bool.not_true_iff_false in Hd. apply Hd.
    apply existsb_exists. exists id. split; [exact Hin|apply Pos.eqb_refl].
  + rewrite ld_get_G by exact Hnin.
    match goal with |- tycontext.sub_option (Maps.PTree.get id ?m) _ =>
      destruct (Maps.PTree.get id m); simpl; auto end.
- simpl. auto.
Qed.

Lemma ld_subVGn : forall (V: varspecs) (G Gs: funspecs),
  forallb (fun id => negb (existsb (Pos.eqb id) (map fst G))) (map fst V) = true ->
  (forall sp, In sp Gs -> Maps.PTree.get (fst sp) (make_tycontext_s G) = Some (snd sp)) ->
  tycontext_subVG V Gs V G.
Proof.
intros V G Gs Hd. induction Gs as [|[i f] Gs IH]; intros Hs.
- apply ld_subVG0; exact Hd.
- assert (Hi: Maps.PTree.get i (make_tycontext_s G) = Some f) by (apply (Hs (i, f)); left; reflexivity).
  destruct (IH (fun sp H => Hs sp (or_intror H))) as [IHg IHs].
  split; intros id.
  + unfold make_tycontext_g at 1. cbn [fold_right fst snd].
    destruct (Pos.eq_dec id i) as [->|Hne].
    * rewrite Maps.PTree.gss. simpl. apply semax_prog.make_tycontext_s_g. exact Hi.
    * rewrite Maps.PTree.gso by exact Hne. fold (make_tycontext_g V Gs). apply IHg.
  + specialize (IHs id). unfold make_tycontext_s at 1. cbn [fold_right fst snd].
    destruct (Pos.eq_dec id i) as [->|Hne].
    * rewrite Maps.PTree.gss. apply subsumespec_i. exists f. split; [exact Hi|apply funspec_sub_si_refl].
    * rewrite Maps.PTree.gso by exact Hne. exact IHs.
Qed.

Lemma ld_disj : forall DENT TABS BR,
  forallb (fun id => negb (existsb (Pos.eqb id) (map fst (stream_G3 DENT TABS BR)))) (map fst Vprog) = true.
Proof. intros. lazy. reflexivity. Qed.

Lemma ld_G3_nodup : forall DENT TABS BR, NoDup (map fst (stream_G3 DENT TABS BR)).
Proof. intros. apply list_norepet_NoDup. apply compute_list_norepet_e. lazy. reflexivity. Qed.

Lemma ld_Delta_lift : forall {Espec: OracleKind} DENT TABS BR (Gs: funspecs) P c R,
  (forall sp, In sp Gs -> In sp (stream_G3 DENT TABS BR)) ->
  semax (ld_DeltaG Gs) P c R -> semax (ds_Delta DENT TABS BR) P c R.
Proof.
intros Espec DENT TABS BR Gs P c R Hin H. eapply semax_Delta_subsumption; [|exact H].
unfold ld_DeltaG, ds_Delta. apply tycontext_sub_i99. apply ld_subVGn; [apply ld_disj|].
intros sp Hsp. apply semax_prog.make_tycontext_s_distinct; [apply Hin; exact Hsp|apply ld_G3_nodup].
Qed.

Lemma ld_in_fixed : forall DENT TABS BR sp, In sp (FS3_fixed DENT TABS SR3 BR) -> In sp (stream_G3 DENT TABS BR).
Proof.
intros DENT TABS BR sp H. unfold stream_G3, FS3_G. apply in_or_app; left.
repeat (apply in_or_app; right). exact H.
Qed.

Lemma ld_in_ss : forall DENT TABS BR sp, In sp (stream_ss3 DENT TABS) -> In sp (stream_G3 DENT TABS BR).
Proof. intros DENT TABS BR sp H. unfold stream_G3. apply in_or_app; right. exact H. Qed.

End CM_L3Dsub_1.

Ltac ld_in_tac :=
  first [ apply ld_in_fixed; unfold FS3_fixed; simpl In; repeat (first [left; reflexivity | right])
        | apply ld_in_ss; unfold stream_ss3; simpl In; repeat (first [left; reflexivity | right]) ].

Section CM_L3Dsub_2.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.

(* a prefix A; B; C; D proved alone (e.g. in a smaller Delta), then the rest R; T *)
Lemma ld_split_seq : forall {Espec: OracleKind} Delta P Q A X R T Post,
  semax Delta P A (overridePost Q Post) -> semax Delta Q (Ssequence X (Ssequence R T)) Post ->
  semax Delta P (Ssequence (Ssequence A (Ssequence X R)) T) Post.
Proof.
intros Espec Delta P Q A X R T Post HA HX.
apply seq_assoc. eapply semax_seq; [exact HA|].
apply seq_assoc. exact HX.
Qed.

Lemma ld_split4 : forall {Espec: OracleKind} Delta P Q A B C D R Post,
  semax Delta P (Ssequence (Ssequence (Ssequence A B) C) D) (overridePost Q Post) ->
  semax Delta Q R Post ->
  semax Delta P (Ssequence A (Ssequence B (Ssequence C (Ssequence D R)))) Post.
Proof.
intros Espec Delta P Q A B C D R Post H1 H2.
apply (proj2 (seq_assoc _ _ _ _ _ _)). apply (proj2 (seq_assoc _ _ _ _ _ _)).
apply (proj2 (seq_assoc _ _ _ _ _ _)).
eapply semax_seq; [exact H1|exact H2].
Qed.

(* in the prefix's proof: back to the right-nested form *)
Lemma ld_unsplit4 : forall {Espec: OracleKind} Delta P A B C D R,
  semax Delta P (Ssequence A (Ssequence B (Ssequence C D))) R ->
  semax Delta P (Ssequence (Ssequence (Ssequence A B) C) D) R.
Proof.
intros Espec Delta P A B C D R H.
apply (proj1 (seq_assoc _ _ _ _ _ _)). apply (proj1 (seq_assoc _ _ _ _ _ _)). exact H.
Qed.

End CM_L3Dsub_2.
