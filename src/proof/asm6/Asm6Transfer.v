(* Generic facts of the assembly: moving a function's obligation (SF) from a unit's compspecs and
   function context to the whole program's, and what QPlink_progs preserves.  No specification is
   unfolded.  Unlike VST's SF_ctx_subsumption, the unit's context may repeat names (a harness's
   context holds the API, an arbitrary sublist of the decoder's specifications). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.veric.Clight_initial_world.
Require Zstd.proof.asm6.Asm6Lib.
Import compcert.lib.Maps.

Lemma tyg_find V G j: (make_tycontext_g V G) ! j =
  match find_id j G with Some phi => Some (type_of_funspec phi) | None => find_id j V end.
Proof.
  induction G as [|[i phi] G IH]; simpl.
  - apply semax_prog.make_tycontext_g_nilG_find_id.
  - rewrite PTree.gsspec. destruct (peq j i); subst.
    + destruct (Memory.EqDec_ident i i); congruence.
    + destruct (Memory.EqDec_ident j i); congruence.
Qed.

Lemma funspec_sub_type psi psi': funspec_sub psi' psi -> type_of_funspec psi' = type_of_funspec psi.
Proof.
  destruct psi as [[a r] cc A P Q NP NQ], psi' as [[a' r'] cc' A' P' Q' NP' NQ'].
  intros [[Hs Hc] _]. inv Hs. subst. reflexivity.
Qed.

Lemma In_map_fst_find_id' (F: funspecs) i: In i (map fst F) -> exists phi, find_id i F = Some phi.
Proof.
  induction F as [|[j psi] F IH]; simpl; [tauto|]. intros H.
  destruct (Memory.EqDec_ident i j) as [E|E]; [eauto|].
  destruct H as [H|H]; [congruence | auto].
Qed.

Lemma InternalInfo_subsumption' {ge cs V V' F F' i f phi}
  (HVF : forall i, (sub_option (make_tycontext_g V F) ! i) ((make_tycontext_g V' F') ! i))
  (HF : forall i, subsumespec (find_id i F) (find_id i F'))
  (H : semaxfunc_InternalInfo cs V F ge i f phi):
  semaxfunc_InternalInfo cs V' F' ge i f phi.
Proof.
  destruct H as [Hb1 [Hb2 [Hb3 [Hb4 [Hb5 Hb6]]]]].
  repeat split; trivial.
  + apply andb_true_iff in Hb1; destruct Hb1 as [X Y]; rewrite Y, andb_true_r.
    clear - X HF. apply assoclists.id_in_list_true_i. apply id_in_list_true in X.
    apply In_map_fst_find_id' in X. destruct X as [phi PHI].
    specialize (HF i); rewrite PHI in HF. destruct HF as [phi' [PHI' Sub]].
    apply find_id_In_map_fst in PHI'; trivial.
  + eapply semax_body_subsumption. eassumption. clear - HF HVF.
    red; simpl. repeat split; trivial; intros i.
    - destruct ((make_tycontext_t (fn_params f) (fn_temps f)) ! i); trivial.
    - rewrite 2 make_tycontext_s_find_id; trivial.
Qed.

Lemma SF_ctx_subsumption' {Espec} V G ge i fd phi cs
  (HSF:  @SF Espec cs V ge G i fd phi) G' V' ge' cs'
  (SubCS: cspecs_sub cs cs')
  (FD: genv_find_func ge' i fd)
  (SubFG: forall j, sub_option (make_tycontext_g V G) ! j (make_tycontext_g V' G') ! j)
  (SubG: forall j : ident, subsumespec (find_id j G) (find_id j G')):
  @SF Espec cs' V' ge' G' i fd phi.
Proof.
  destruct fd; simpl.
 + eapply InternalInfo_subsumption'.
    3: eapply (@InternalInfo_envs_sub cs cs' SubCS); eassumption.
    assumption. assumption.
 + eapply ExternalInfo_envs_sub; eassumption.
Qed.

Lemma SF_transfer {Espec} (cs cs': compspecs) V G V' G' ge ge' i fd phi:
  cspecs_sub cs cs' ->
  @SF Espec cs V ge G i fd phi -> genv_find_func ge' i fd ->
  (forall j psi, find_id j G = Some psi -> exists psi', find_id j G' = Some psi' /\ funspec_sub psi' psi) ->
  (forall j t, find_id j G = None -> find_id j V = Some t -> find_id j G' = None /\ find_id j V' = Some t) ->
  @SF Espec cs' V' ge' G' i fd phi.
Proof.
  intros CSUB HSF FD HG HV.
  apply (SF_ctx_subsumption' V G ge i fd phi cs HSF G' V' ge' cs' CSUB FD).
  - intros j. rewrite !tyg_find. destruct (find_id j G) as [psi|] eqn:E.
    + destruct (HG _ _ E) as [psi' [E' S]]. rewrite E'. simpl. f_equal. apply funspec_sub_type; auto.
    + destruct (find_id j V) as [t|] eqn:EV; simpl; auto.
      destruct (HV _ _ E EV) as [E1 E2]. rewrite E1, E2. auto.
  - intros j. destruct (find_id j G) as [psi|] eqn:E; simpl; auto.
    destruct (HG _ _ E) as [psi' [E' S]]. exists psi'; split; auto. apply funspec_sub_sub_si; auto.
Qed.

(* QPlink_progs keeps every internal function of either side. *)
Lemma link_internal p1 p2 p i f: QPlink_progs p1 p2 = Errors.OK p ->
  (QP.prog_defs p1) ! i = Some (Gfun (Internal f)) \/ (QP.prog_defs p2) ! i = Some (Gfun (Internal f)) ->
  (QP.prog_defs p) ! i = Some (Gfun (Internal f)).
Proof.
  intros L H. pose proof (Linked_Functions_preserved _ _ _ L i) as FP. hnf in FP.
  destruct H as [H|H]; rewrite H in FP.
  - destruct ((QP.prog_defs p2) ! i) as [[[]|]|]; tauto.
  - destruct ((QP.prog_defs p1) ! i) as [[[]|]|]; try tauto.
Qed.

(* Every specification of the unit's context is weakened by the one of the whole context. *)
Definition ctx_sub (Gu G': funspecs) : Prop :=
  forall j psi, find_id j Gu = Some psi -> exists psi', find_id j G' = Some psi' /\ funspec_sub psi' psi.

Lemma ctx_sub_app A B G': ctx_sub A G' -> ctx_sub B G' -> ctx_sub (A ++ B) G'.
Proof.
  intros HA HB j psi H. rewrite assoclists.find_id_app_char in H.
  destruct (find_id j A) eqn:E; [inv H; apply HA; auto | apply HB; auto].
Qed.

Lemma ctx_sub_nil G': ctx_sub nil G'.
Proof. intros j psi H. discriminate. Qed.

Lemma ctx_sub_cons i phi A G':
  (exists psi', find_id i G' = Some psi' /\ funspec_sub psi' phi) -> ctx_sub A G' -> ctx_sub ((i, phi) :: A) G'.
Proof.
  intros H1 HA j psi H. simpl in H. destruct (Memory.EqDec_ident j i); [subst; inv H; auto | auto].
Qed.

Lemma ctx_sub_cons_eq i phi A G':
  find_id i G' = Some phi -> ctx_sub A G' -> ctx_sub ((i, phi) :: A) G'.
Proof. intros H1 HA. apply ctx_sub_cons; auto. exists phi; split; auto. apply funspec_sub_refl. Qed.

(* Any context whose entries are all found verbatim. *)
Lemma ctx_sub_In A G': (forall j psi, In (j, psi) A -> find_id j G' = Some psi) -> ctx_sub A G'.
Proof.
  intros H j psi F. exists psi; split; [apply H; apply find_id_e; auto | apply funspec_sub_refl].
Qed.

Lemma SF_of_fun_ok {Espec cs V} ge G i f phi:
  Asm6Lib.fun_ok cs f = true -> semax_body V G f (i, phi) ->
  fn_callconv f = callingconvention_of_funspec phi ->
  genv_find_func ge i (Internal f) -> In i (map fst G) ->
  @SF Espec cs V ge G i (Internal f) phi.
Proof.
  intros F SB CC GF IN.
  unfold Asm6Lib.fun_ok in F. rewrite !andb_true_iff in F. destruct F as [[F1 F2] F3].
  simpl. split; [| split; [| split; [| split; [| split]]]].
  - rewrite (assoclists.id_in_list_true_i _ _ IN), F1. reflexivity.
  - rewrite forallb_forall in F2. apply Forall_forall. intros; apply F2; auto.
  - rewrite forallb_forall in F3. apply Forall_forall. intros x H.
    apply F3 in H. apply Z.leb_le in H. exact H.
  - exact CC.
  - exact SB.
  - exact GF.
Qed.

(* The obligation of one internal function of a unit (program q, compspecs cs, its varspecs Vu and
   function context Gu), moved to the whole program p (compspecs CSW, varspecs V', context G'). *)
Lemma SF_unit {Espec} (cs CSW: compspecs) (q p: QP.program function) (OKp: QPprogram_OK p)
  (FOK: Asm6Lib.prog_funs_ok cs q = true) (CSUB: cspecs_sub cs CSW)
  (LINK: forall i f, (QP.prog_defs q) ! i = Some (Gfun (Internal f)) -> (QP.prog_defs p) ! i = Some (Gfun (Internal f)))
  (Vu V': varspecs) (Gu G': funspecs)
  (HG: ctx_sub Gu G')
  (HV: forall j t, find_id j Gu = None -> find_id j Vu = Some t -> find_id j G' = None /\ find_id j V' = Some t)
  i phi f (Hf: (QP.prog_defs q) ! i = Some (Gfun (Internal f)))
  (CC: fn_callconv f = callingconvention_of_funspec phi) (SB: @semax_body Vu Gu cs f (i, phi))
  (IN: In i (map fst Gu)):
  forall fd, (QP.prog_defs p) ! i = Some (Gfun fd) -> @SF Espec CSW V' (QPglobalenv p) G' i fd phi.
Proof.
  intros fd Hp. pose proof (LINK _ _ Hf) as Hp'. rewrite Hp in Hp'. inv Hp'.
  assert (GF: genv_find_func (QPglobalenv p) i (Internal f)) by apply (QPprogdefs_GFF OKp Hp).
  apply (SF_transfer cs CSW Vu Gu V' G' (QPglobalenv p) (QPglobalenv p)); auto.
  apply SF_of_fun_ok; auto.
  apply (Asm6Lib.prog_funs_ok_e cs q i f FOK Hf).
Qed.
