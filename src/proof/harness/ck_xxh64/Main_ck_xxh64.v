(* The harness obligation of harness/ck_xxh64.c: main's body, and HarnessOK with the API [ZSTD_XXH64_spec]
   and the helper specifications of Specs_ck_xxh64.v.  main draws a length (upto), that many bytes
   (any_bytes) and a seed (pick); ZSTD_XXH64 returns xxh64 bs seed (Spec_xxh.ZSTD_XXH64_spec), and so does
   the harness's own xxh64 (xxh64_spec, Body_xxh64.v): the gp_assert compares two equal values. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Pick.
Require Import Zstd.proof.harness.ck_xxh64.Specs_ck_xxh64.
Require Import Zstd.proof.harness.ck_xxh64.Bodies_ck_xxh64.
Require Import Zstd.proof.harness.ck_xxh64.Body_xxh64.
Local Open Scope logic.

#[local] Instance CCE_HZ : change_composite_env Zstd.proof.harness.ck_xxh64.HOK_ck_xxh64.CompSpecs Zstd.units.Zstd.CS.
Proof. make_cs_preserve Zstd.proof.harness.ck_xxh64.HOK_ck_xxh64.CompSpecs Zstd.units.Zstd.CS. Defined.

(* the bytes and the malloc_token of the input, at the decoder's compspecs for the call of ZSTD_XXH64 *)
Lemma cs_bytes sh n v p :
  @data_at Zstd.proof.harness.ck_xxh64.HOK_ck_xxh64.CompSpecs sh (tarray tuchar n) v p =
  @data_at Zstd.units.Zstd.CS sh (tarray tuchar n) v p.
Proof.
  rewrite (@data_at_change_composite _ _ CCE_HZ sh (tarray tuchar n) v v); [reflexivity | apply JMeq_refl | reflexivity].
Qed.

Lemma cs_token sh n p :
  @malloc_token Zstd.proof.harness.ck_xxh64.HOK_ck_xxh64.CompSpecs sh (tarray tuchar n) p =
  @malloc_token Zstd.units.Zstd.CS sh (tarray tuchar n) p.
Proof. rewrite (@malloc_token_change_composite _ _ CCE_HZ sh (tarray tuchar n)) by reflexivity. reflexivity. Qed.

(* the variable seed as the 8 bytes pick(seed) writes *)
Lemma fc_bytes8 p : field_compatible tulong [] p -> field_compatible (tarray tuchar 8) [] p.
Proof.
  intros (Hp & Hl & Hs & Ha & _). destruct p; try contradiction.
  split; [exact I | split; [reflexivity | split; [| split; [| exact I]]]].
  - simpl in Hs |- *. exact Hs.
  - apply align_compatible_rec_Tarray. intros j Hj.
    eapply align_compatible_rec_by_value; [reflexivity |]. apply Z.divide_1_l.
Qed.

Lemma seed_bytes p : field_compatible tulong [] p ->
  data_at_ Tsh tulong p |-- data_at_ Tsh (tarray tuchar 8) p.
Proof.
  intros Hfc. rewrite !data_at__memory_block. normalize.
  apply andp_right; [apply prop_right; apply fc_bytes8; exact Hfc | apply derives_refl].
Qed.

Lemma make_tycontext_g_isSome (V: varspecs) (G: funspecs) i :
  In i (map fst V) -> isSome (Maps.PTree.get i (make_tycontext_g V G)).
Proof.
  intros Hi. unfold make_tycontext_g.
  induction G as [|[j fs] G IH]; simpl.
  - induction V as [|[k t] V IHV]; simpl in *; [contradiction|].
    rewrite Maps.PTree.gsspec. destruct (peq i k); [exact Logic.I|]. apply IHV. destruct Hi; [congruence|auto].
  - rewrite Maps.PTree.gsspec. destruct (peq i j); [exact Logic.I|]. exact IH.
Qed.

(* main sees every global variable of the program *)
Lemma vars_in_Vprog (G: funspecs) :
  Forall (fun ig : ident * globvar type => isSome (Maps.PTree.get (fst ig) (make_tycontext_g Vprog G)))
    (QPprog_vars Zstd.contracts.ck_xxh64.whole_prog).
Proof.
  apply Forall_forall. intros [i v] Hin. apply make_tycontext_g_isSome.
  unfold Vprog, QPvarspecs. rewrite map_map.
  apply in_map_iff. exists (i, v). split; [reflexivity | exact Hin].
Qed.

Lemma body_main : semax_body Vprog G f_main main_spec.
Proof.
  change (semax_body Vprog G f_main (_main, WITH gv: globals PRE [] VST.floyd.VSU.main_pre
    Zstd.contracts.ck_xxh64.whole_prog tt gv POST [tint] (fun _ : environ => TT))).
  replace (fun _ : environ => @TT mpred _) with (PROP () LOCAL () SEP (@TT mpred _))
    by (extensionality rho; unfold PROPx, LOCALx, SEPx; simpl; normalize).
  start_function1.
  eapply (main_pre_InitGpred TT).
  { intros _. apply TT_right. }
  { reflexivity. }
  { apply vars_in_Vprog. }
  start_function3.
  sep_apply (create_mem_mgr gv).
  forward_call (9223372036854775807).
  Intros len.
  forward_call (len, gv).
  Intros vret. destruct vret as [p bs]. cbn [fst snd] in *.
  (* pick(seed): the 8 bytes nondet_bytes writes are some unsigned long *)
  assert_PROP (field_compatible tulong [] v_seed) as FCs by entailer!.
  sep_apply (seed_bytes v_seed FCs).
  forward_call (v_seed, 8, Tsh).
  Intros sb.
  match goal with H: Zlength sb = 8, H': Forall _ sb |- _ => sep_apply (pick_tulong Tsh sb v_seed H H' FCs) end.
  Intros sv.
  destruct (eq_dec p nullval) as [Hp|Hp].
  { forward_if.
    - forward. sep_apply (data_at_data_at_ Tsh tulong (Vlong sv) v_seed). entailer!.
    - subst p. congruence. }
  forward_if.
  { subst p. congruence. }
  Intros.
  forward.
  (* ZSTD_XXH64, at the decoder's compspecs; the malloc_token vouches for p when the input is empty *)
  subst len. rewrite cs_bytes, cs_token. rewrite <- (Int64.repr_unsigned sv).
  change (zbytes bs) with (xxh_bytes bs).
  forward_call (Ews, p, bs, Int64.unsigned sv, pw_token Ews (tarray tuchar (Zlength bs)) p).
  { simpl pw_pred. unfold Zstd.proof.zstd.Base.CompSpecs. cancel. }
  { simpl pw_pred.
    eapply derives_trans; [apply malloc_token_valid_pointer; simpl; lia | apply valid_pointer_weak]. }
  simpl pw_pred. unfold xxh_bytes. unfold Zstd.proof.zstd.Base.CompSpecs. rewrite <- cs_bytes, <- cs_token.
  (* the harness's xxh64 *)
  forward.
  forward_call (Ews, p, bs, Int64.unsigned sv).
  (* the two hashes are equal *)
  forward_call (Int.one).
  { entailer!. unfold Int64.cmpu. rewrite Int64.eq_true. reflexivity. }
  forward.
  sep_apply (data_at_data_at_ Tsh tulong (Vlong (Int64.repr (Int64.unsigned sv))) v_seed). entailer!.
Qed.

(* the harness unit's obligation, with the API [ZSTD_XXH64_spec] *)
Theorem ck_xxh64_ok : HarnessOK API Hs.
Proof.
  split; [exact Hs_ids |].
  repeat apply Forall_cons; try apply Forall_nil;
    (eexists; split; [reflexivity | split; [reflexivity |]]).
  - exact body_any_bytes.
  - exact body_merge.
  - exact body_upto.
  - exact body_xxh64.
  - exact body_le.
  - exact body_round64.
  - exact body_rotl.
  - exact body_main.
Qed.
