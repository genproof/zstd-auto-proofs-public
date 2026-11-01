(* FS3 streaming, case zdss_read: pieces proved in the function's type context with only the
   specifications they call (much cheaper for Floyd), then lifted to ds_Delta (generalises
   epi/E3Dsub.v to a list of callees). *)
Require Import Zstd.proof.dec.v3.FS.stream.S3Main.
Local Open Scope logic.

Section CM_R3Dsub_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Definition rd_Delta (sps: funspecs) : tycontext := func_tycontext f_ZSTD_decompressStream Vprog sps nil.

Lemma rd_get_V : forall (V: varspecs) id t,
  Maps.PTree.get id (fold_right (fun (v: ident * type) (m: Maps.PTree.t type) => Maps.PTree.set (fst v) (snd v) m)
                       (Maps.PTree.empty type) V) = Some t -> In id (map fst V).
Proof.
induction V as [|[i ty] V IH]; intros id t H; simpl in *.
- rewrite Maps.PTree.gempty in H. discriminate.
- destruct (Pos.eq_dec id i) as [->|Hne]; [left; reflexivity|].
  rewrite Maps.PTree.gso in H by exact Hne. right. eapply IH; eauto.
Qed.

Lemma rd_get_G : forall (G: funspecs) (m: Maps.PTree.t type) id,
  ~ In id (map fst G) ->
  Maps.PTree.get id (fold_right (fun (var: ident * funspec) => Maps.PTree.set (fst var) (type_of_funspec (snd var))) m G)
  = Maps.PTree.get id m.
Proof.
induction G as [|[i f] G IH]; intros m id H; simpl in *; auto.
rewrite Maps.PTree.gso by (intros E; apply H; left; auto). apply IH. intros E; apply H; right; exact E.
Qed.

Lemma rd_subVG0 : forall (V: varspecs) (G: funspecs),
  forallb (fun id => negb (existsb (Pos.eqb id) (map fst G))) (map fst V) = true ->
  tycontext_subVG V nil V G.
Proof.
intros V G Hd. split; intros id.
- unfold make_tycontext_g. simpl fold_right at 1.
  destruct (in_dec Pos.eq_dec id (map fst G)) as [Hin|Hnin].
  + match goal with |- tycontext.sub_option (Maps.PTree.get id ?m) _ =>
      destruct (Maps.PTree.get id m) as [t|] eqn:E end; simpl; auto.
    exfalso. apply rd_get_V in E. rewrite forallb_forall in Hd. specialize (Hd id E).
    apply Bool.negb_true_iff in Hd. rewrite <- Bool.not_true_iff_false in Hd. apply Hd.
    apply existsb_exists. exists id. split; [exact Hin|apply Pos.eqb_refl].
  + rewrite rd_get_G by exact Hnin.
    match goal with |- tycontext.sub_option (Maps.PTree.get id ?m) _ =>
      destruct (Maps.PTree.get id m); simpl; auto end.
- simpl. auto.
Qed.

Lemma rd_subVG : forall (V: varspecs) (G sps: funspecs),
  forallb (fun id => negb (existsb (Pos.eqb id) (map fst G))) (map fst V) = true ->
  Forall (fun sp => Maps.PTree.get (fst sp) (make_tycontext_s G) = Some (snd sp) /\
                    Maps.PTree.get (fst sp) (make_tycontext_g V G) = Some (type_of_funspec (snd sp))) sps ->
  tycontext_subVG V sps V G.
Proof.
intros V G sps Hd Hs. induction sps as [|[i f] sps IH].
- apply rd_subVG0; exact Hd.
- inversion Hs as [|? ? [Hs1 Hg1] Hs2]; subst. specialize (IH Hs2). destruct IH as [IHg IHs].
  cbn [fst snd] in Hs1, Hg1. split; intros id.
  + unfold make_tycontext_g at 1. cbn [fold_right fst snd].
    destruct (Pos.eq_dec id i) as [->|Hne].
    * rewrite Maps.PTree.gss. simpl. rewrite Hg1. reflexivity.
    * rewrite Maps.PTree.gso by exact Hne. exact (IHg id).
  + unfold make_tycontext_s at 1. cbn [fold_right fst snd].
    destruct (Pos.eq_dec id i) as [->|Hne].
    * rewrite Maps.PTree.gss. apply subsumespec_i. rewrite Hs1. exists f. split; [reflexivity|apply funspec_sub_si_refl].
    * rewrite Maps.PTree.gso by exact Hne. exact (IHs id).
Qed.

Lemma rd_disj : forall DENT TABS BR,
  forallb (fun id => negb (existsb (Pos.eqb id) (map fst (stream_G3 DENT TABS BR)))) (map fst Vprog) = true.
Proof. intros. lazy. reflexivity. Qed.

Lemma rd_G3_nodup : forall DENT TABS BR, NoDup (map fst (stream_G3 DENT TABS BR)).
Proof.
intros. apply list_norepet_NoDup. apply compute_list_norepet_e. lazy. reflexivity.
Qed.

Lemma rd_Delta_lift : forall {Espec: OracleKind} DENT TABS BR (sps: funspecs) P c R,
  Forall (fun sp => In sp (stream_G3 DENT TABS BR)) sps ->
  semax (rd_Delta sps) P c R -> semax (ds_Delta DENT TABS BR) P c R.
Proof.
intros Espec DENT TABS BR sps P c R Hin H. eapply semax_Delta_subsumption; [|exact H].
unfold rd_Delta, ds_Delta. apply tycontext_sub_i99. apply rd_subVG; [apply rd_disj|].
rewrite Forall_forall in Hin |- *. intros sp Hsp. specialize (Hin sp Hsp).
assert (Hs: Maps.PTree.get (fst sp) (make_tycontext_s (stream_G3 DENT TABS BR)) = Some (snd sp)).
{ apply semax_prog.make_tycontext_s_distinct; [exact Hin|apply rd_G3_nodup]. }
split; [exact Hs|]. apply semax_prog.make_tycontext_s_g. exact Hs.
Qed.

(* the callees of the read case *)
Lemma rd_in_cs : forall DENT TABS BR, In (ZSTD_decompressContinueStream_spec3 DENT TABS) (stream_G3 DENT TABS BR).
Proof. intros. unfold stream_G3. apply in_or_app; right. simpl. right; left; reflexivity. Qed.

Lemma rd_in_err : forall DENT TABS BR, In ERR_isError_spec (stream_G3 DENT TABS BR).
Proof.
intros. unfold stream_G3, FS3_G. apply in_or_app; left. apply in_or_app; left.
unfold Gprog, Specs_L0. simpl. repeat (first [left; reflexivity | right]).
Qed.

Lemma rd_in_nss : forall DENT TABS BR, In ZSTD_nextSrcSizeToDecompressWithInputSize_spec (stream_G3 DENT TABS BR).
Proof.
intros. unfold stream_G3, FS3_G. apply in_or_app; left.
repeat (apply in_or_app; right). unfold FS3_fixed. simpl In. repeat (first [left; reflexivity | right]).
Qed.

(* the case's branch that decodes a unit directly from the input (iend - ip >= neededInSize) *)
Definition rd_direct : statement :=
  match ds_case_read with
  | Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence (Sifthenelse _ c _) _)))) => c
  | _ => Sskip
  end.

End CM_R3Dsub_1.
