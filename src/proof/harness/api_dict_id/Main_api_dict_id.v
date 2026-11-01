(* The harness obligation of api_dict_id (harness/api_dict_id.c): with the API [ZSTD_getDictID_fromFrame;
   ZSTD_XXH64] (the second for new_frame's checksums), the helpers of laws_common.h and frames.h (proved once in
   the frames kit) and main satisfy their specifications.

   main builds a frame of new_frame (no content, any Dictionary_ID) or a skippable frame, followed by any bytes;
   ZSTD_getDictID_fromFrame's specification returns the model's dict_id_from_frame, which is the ID of the frame
   or 0 for the skippable one (Facts_api_dict_id).  The input has any length up to PTRDIFF_MAX: this needs the
   frame inspection specifications of Spec_api6 (src_spec_pre) with sizes up to 2 ^ 63 - 1. *)
Require Import VST.floyd.proofauto.
Require Export Zstd.proof.zstd.Spec_api6.
Require Export Zstd.proof.harness.api_dict_id.HOK_api_dict_id.
Require Zstd.proof.top.MainPre6.
Require Zstd.proof.harness.HCsConv.
Require Zstd.proof.harness.frames.FSpecs Zstd.proof.harness.frames.FBodiesSmall Zstd.proof.harness.frames.FTransfer.
Require Zstd.proof.harness.frames.FBodyNewFrame Zstd.proof.harness.frames.FFacts Zstd.proof.harness.frames.FSeries.
Require Import Zstd.proof.harness.api_dict_id.Facts_api_dict_id.
Import Zstd.proof.harness.frames.FSpecs.

Local Ltac expand_main_pre ::= idtac.

Lemma make_tycontext_g_isSome (V: varspecs) (G: funspecs) i :
  In i (map fst V) -> isSome (Maps.PTree.get i (make_tycontext_g V G)).
Proof.
  intros Hi. unfold make_tycontext_g.
  induction G as [|[j fs] G IH]; simpl.
  - induction V as [|[k t] V IHV]; simpl in *; [contradiction|].
    rewrite Maps.PTree.gsspec. destruct (peq i k); [exact Logic.I|]. apply IHV. destruct Hi; [congruence|auto].
  - rewrite Maps.PTree.gsspec. destruct (peq i j); [exact Logic.I|]. exact IH.
Qed.

Lemma vars_in_Vprog (G: funspecs) :
  Forall (fun ig : ident * globvar type => isSome (Maps.PTree.get (fst ig) (make_tycontext_g Vprog G)))
    (QPprog_vars Zstd.contracts.api_dict_id.whole_prog).
Proof.
  apply Forall_forall. intros [i v] Hin. apply make_tycontext_g_isSome.
  unfold Vprog, QPvarspecs. rewrite map_map.
  apply in_map_iff. exists (i, v). split; [reflexivity | exact Hin].
Qed.

(* main's precondition: the decoder's globals, split off as in MainPre6.main_pre_fact6 (whose list of
   programs has the x_ laws only) *)
Lemma pre_globals gv :
  InitGPred (Vardefs Zstd.contracts.api_dict_id.whole_prog) gv |-- zstd_globals gv * TT.
Proof.
  assert (Hincl: incl Zstd.proof.top.MainPre6.zstd_vardefs (Vardefs Zstd.contracts.api_dict_id.whole_prog)).
  { apply Zstd.proof.top.MainPre6.MP_incl_Vardefs; vm_compute; reflexivity. }
  rewrite (Zstd.proof.top.MainPre6.MP_split_zstd _ gv Hincl).
  apply sepcon_derives; [apply Zstd.proof.top.MainPre6.zstd_vardefs_globals | apply TT_right].
Qed.

(* ---------- byte arrays between the harness's compspecs and the decoder's ---------- *)

Lemma to_Z sh n v p :
  @data_at CompSpecs sh (tarray tuchar n) v p |-- @data_at Zstd.units.Zstd.CS sh (tarray tuchar n) v p.
Proof. rewrite (Zstd.proof.harness.HCsConv.data_at_bytes_cs CompSpecs Zstd.units.Zstd.CS). apply derives_refl. Qed.

Lemma of_Z sh n v p :
  @data_at Zstd.units.Zstd.CS sh (tarray tuchar n) v p |-- @data_at CompSpecs sh (tarray tuchar n) v p.
Proof. rewrite (Zstd.proof.harness.HCsConv.data_at_bytes_cs CompSpecs Zstd.units.Zstd.CS). apply derives_refl. Qed.

(* ---------- the 1-byte array none: new_frame's empty data, and the witness of its pointer ---------- *)

(* none[1] lends new_frame an empty array at its address and, as the witness that this address is weakly
   valid (ZSTD_XXH64 compares it with NULL), its one byte *)
Lemma none_split p :
  @data_at_ CompSpecs Tsh (tarray tuchar 1) p |--
  @data_at CompSpecs Tsh (tarray tuchar 0) (zbytes []) p *
  Zstd.proof.zstd.Spec_xxh.pw_pred (Zstd.proof.zstd.Spec_xxh.pw_bytes Tsh 1 [Vundef] p).
Proof.
  assert_PROP (isptr p) as Hp by entailer!.
  rewrite (@data_at_zero_array_eq CompSpecs) by auto. rewrite emp_sepcon.
  unfold Zstd.proof.zstd.Spec_xxh.pw_pred. apply to_Z.
Qed.

Lemma none_wvp p :
  Zstd.proof.zstd.Spec_xxh.pw_pred (Zstd.proof.zstd.Spec_xxh.pw_bytes Tsh 1 [Vundef] p) |-- weak_valid_pointer p.
Proof.
  unfold Zstd.proof.zstd.Spec_xxh.pw_pred.
  eapply derives_trans; [apply data_at_valid_ptr; [auto | simpl; lia] | apply valid_pointer_weak].
Qed.

Lemma none_join p l :
  @data_at CompSpecs Tsh (tarray tuchar 0) l p *
  Zstd.proof.zstd.Spec_xxh.pw_pred (Zstd.proof.zstd.Spec_xxh.pw_bytes Tsh 1 [Vundef] p) |--
  @data_at_ CompSpecs Tsh (tarray tuchar 1) p.
Proof.
  unfold Zstd.proof.zstd.Spec_xxh.pw_pred.
  eapply derives_trans; [apply sepcon_derives; [apply derives_refl | apply of_Z] |].
  assert_PROP (isptr p) as Hp by entailer!.
  assert_PROP (Zlength l = 0) as Hl by entailer!. apply Zlength_nil_inv in Hl. subst l.
  rewrite (@data_at_zero_array_eq CompSpecs) by auto. rewrite emp_sepcon. apply derives_refl.
Qed.

(* skippable = nondet_u8() & 1 *)
Lemma and_one b : 0 <= b <= Int.max_unsigned -> Int.and (Int.repr b) (Int.repr 1) = Int.repr (b mod 2).
Proof.
  intros Hb. unfold Int.and. rewrite !Int.unsigned_repr by rep_lia.
  change 1 with (Z.ones 1). rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma mbytes_fold {cs: compspecs} n l q : q <> nullval ->
  malloc_token Ews (tarray tuchar n) q * data_at Ews (tarray tuchar n) (zbytes l) q |-- mbytes n l q.
Proof. intros Hq. unfold mbytes. rewrite if_false by exact Hq. apply derives_refl. Qed.

Lemma isptr_of p : is_pointer_or_null p -> p <> nullval -> isptr p.
Proof. intros H1 H2. destruct p; simpl in *; auto. subst. contradiction. Qed.

(* the API of the law *)
Definition API : funspecs := [ZSTD_getDictID_fromFrame_spec; Zstd.proof.zstd.Spec_xxh.ZSTD_XXH64_spec].

(* the functions main calls *)
Definition G0 : funspecs :=
  [ZSTD_getDictID_fromFrame_spec;
   nondet_u8_spec; nondet_u32_spec; gp_assert_spec;
   upto_spec; @any_bytes_spec CompSpecs; @new_frame_spec CompSpecs; @new_skippable_spec CompSpecs;
   @join_spec CompSpecs].

Lemma body_main_G0 : semax_body Vprog G0 f_main main_spec.
Proof.
  change (semax_body Vprog G0 f_main (_main, WITH gv: globals PRE [] VST.floyd.VSU.main_pre
    Zstd.contracts.api_dict_id.whole_prog tt gv POST [tint] (fun _ : environ => TT))).
  replace (fun _ : environ => @TT mpred _) with (PROP () LOCAL () SEP (@TT mpred _))
    by (extensionality rho; unfold PROPx, LOCALx, SEPx; simpl; normalize).
  start_function1.
  eapply (main_pre_InitGpred (zstd_globals gv * TT)%logic).
  { intros _. apply pre_globals. }
  { reflexivity. }
  { apply vars_in_Vprog. }
  start_function3.
  sep_apply (create_mem_mgr gv).
  forward_call tt.
  Intros did.
  forward_call 9223372036854775807.
  Intros after.
  forward_call tt.
  Intros u8.
  forward.
  rewrite and_one by rep_lia.
  assert (Hm: 0 <= u8 mod 2 < 2) by (apply Z.mod_pos_bound; lia).
  (* the frame: a skippable frame, or a frame of new_frame with the ID did; NULL when out of memory *)
  forward_if (EX q: val, EX fl: list Z,
    PROP (q <> nullval -> bytes_ok fl /\ Zlength fl <= 2 ^ 33 /\
            forall rest, dict_id_from_frame (fl ++ rest) = (if Z.eq_dec (u8 mod 2) 0 then did else 0))
    LOCAL (temp _t'4 q; temp _skippable (Vint (Int.repr (u8 mod 2))); temp _after (Vlong (Int64.repr after));
           temp _dict_id (Vint (Int.repr did)); lvar _len tulong v_len; lvar _none (tarray tuchar 1) v_none;
           gvars gv)
    SEP (mem_mgr gv;
         if eq_dec q nullval then data_at_ Tsh tulong v_len
         else data_at Tsh tulong (Vlong (Int64.repr (Zlength fl))) v_len;
         mbytes (Zlength fl) fl q; data_at_ Tsh (tarray tuchar 1) v_none; zstd_globals gv; TT)).
  - (* new_skippable *)
    forward_call (gv, Tsh, v_len).
    Intros q.
    forward.
    destruct (eq_dec q nullval) as [Hq|Hq].
    + subst q. Exists nullval (@nil Z). unfold mbytes.
      destruct (eq_dec nullval nullval) as [_|C]; [|contradiction]. entailer!.
    + destruct (eq_dec q nullval) as [C|_]; [contradiction|].
      Intros k u. Exists q (sk_bytes k u).
      destruct (eq_dec q nullval) as [C|_]; [contradiction|].
      entailer!.
      split; [apply Zstd.proof.harness.frames.FSeries.sk_bytes_ok; auto |].
      split; [rewrite Zstd.proof.harness.frames.FSeries.sk_bytes_length; lia |].
      intros rest. rewrite dict_id_skippable by lia.
      destruct (Z.eq_dec (u8 mod 2) 0); [contradiction | reflexivity].
  - (* new_frame(none, 0, 0, ONE_CALL_WINDOW, dict_id, &len) *)
    apply -> seq_assoc. apply semax_if_seq. forward_if.
    { discriminate. }
    forward.
    sep_apply (none_split v_none).
    forward_call (gv, Tsh, v_none, @nil Z, 0, 2 ^ 31, did, Tsh, v_len,
                  Zstd.proof.zstd.Spec_xxh.pw_bytes Tsh 1 [Vundef] v_none).
    { rewrite Zlength_nil. cancel. }
    { split; [apply Forall_nil | split; [rewrite Zlength_nil; rep_lia | intros _; apply none_wvp]]. }
    Intros vret. destruct vret as [q d']. cbn [fst snd] in *.
    rewrite Zlength_nil in *.
    sep_apply (none_join v_none (zbytes d')).
    forward.
    destruct (eq_dec q nullval) as [Hq|Hq].
    + subst q. Exists nullval (@nil Z). unfold mbytes.
      destruct (eq_dec nullval nullval) as [_|C]; [|contradiction]. entailer!.
    + Intros c. Exists q (nf_bytes [] 0 did c).
      destruct (eq_dec q nullval) as [C|_]; [contradiction|].
      entailer!.
      match goal with Hc: nf_ok _ _ _ _ c |- _ => rename Hc into Hok end.
      split; [apply (Zstd.proof.harness.frames.FFacts.nf_bytes_ok [] 0 (2 ^ 31) did c Hok); apply Forall_nil |].
      split; [pose proof (Zstd.proof.harness.frames.FFacts.nf_bytes_length [] 0 (2 ^ 31) did c Hok); rewrite Zlength_nil in *; lia |].
      intros rest. rewrite (dict_id_new_frame [] 0 (2 ^ 31) did c rest Hok) by rep_lia.
      destruct (Z.eq_dec (u8 mod 2) 0); [reflexivity |].
      exfalso. match goal with Hn: u8 mod 2 <> 0 |- _ => apply Hn end.
      apply (f_equal Int.unsigned) in H2. rewrite Int.unsigned_repr in H2 by rep_lia. exact H2.
  - Intros q fl.
    forward.
    repeat apply -> seq_assoc. apply semax_if_seq.
    destruct (eq_dec q nullval) as [Hq|Hq].
    { (* out of memory: src = NULL, the run ends *)
      subst q. forward_if; [| contradiction]. forward. forward.
      forward_if; [forward; cancel | contradiction]. }
    match goal with Hf: q <> nullval -> _ |- _ => destruct (Hf Hq) as (Hfb & Hfl & Hfd) end.
    unfold mbytes at 1. destruct (eq_dec q nullval) as [C|_]; [contradiction|]. Intros.
    assert_PROP (isptr q) as Hq' by entailer!.
    forward_if; [destruct q; try contradiction; discriminate |].
    sep_apply (@mbytes_fold CompSpecs (Zlength fl) fl q Hq).
    (* the frame followed by after bytes *)
    forward_call (gv, after).
    Intros vret. destruct vret as [pa la]. cbn [fst snd] in *.
    forward.
    subst after.
    forward_call (gv, q, fl, pa, la).
    Intros src.
    forward. forward.
    destruct (eq_dec src nullval) as [Hs|Hs].
    { subst src. forward_if; [forward; cancel | contradiction]. }
    match goal with Hj: src <> nullval -> _ |- _ =>
      assert (Hlen: Zlength fl + Zlength la <= PTRDIFF_MAX) by (apply Hj; auto; unfold PTRDIFF_MAX; lia) end.
    unfold mbytes at 1. destruct (eq_dec src nullval) as [C|_]; [contradiction|]. Intros.
    assert_PROP (isptr src) as Hs' by entailer!.
    forward_if.
    { destruct src; try contradiction; discriminate. }
    forward.
    (* ZSTD_getDictID_fromFrame(src, len + after) *)
    rewrite <- Zlength_app.
    sep_apply (to_Z Ews (Zlength (fl ++ la)) (zbytes (fl ++ la)) src).
    forward_call (gv, Ews, src, fl ++ la).
    { entailer!. rewrite Zlength_app. reflexivity. }
    { unfold src_spec_pre. split3; [auto | rewrite Zlength_app; unfold PTRDIFF_MAX in Hlen; lia |].
      apply Zstd.proof.harness.frames.FFacts.ff_bytes_ok_app; auto. }
    forward.
    rewrite Hfd.
    (* the check: id == (skippable ? 0 : dict_id) *)
    repeat apply -> seq_assoc. apply semax_if_seq.
    forward_if.
    + destruct (Z.eq_dec (u8 mod 2) 0) as [E|_]; [rewrite E in *; contradiction |].
      forward.
      forward_call Int.one.
      forward. cancel.
    + destruct (Z.eq_dec (u8 mod 2) 0) as [_|E]; [| apply (f_equal Int.unsigned) in H7; rewrite Int.unsigned_repr in H7 by rep_lia; contradiction].
      forward.
      forward_call Int.one.
      { entailer!. simpl. rewrite Int.eq_true. reflexivity. }
      forward. cancel.
Qed.

(* ---------- from G0 to Gprog API Hs ---------- *)

(* the harness's own functions besides main (in the order of helper_ids): the frames kit's helpers *)
Definition Hs : funspecs :=
  [@copy_of_spec CompSpecs; @any_bytes_spec CompSpecs; upto_spec; @put_le_spec CompSpecs;
   @join_spec CompSpecs; @new_skippable_spec CompSpecs; @new_frame_spec CompSpecs].

Lemma Externals_eq : Externals =
  [nondet_u8_spec; nondet_u32_spec; nondet_size_spec; nondet_bytes_nn_spec; gp_assert_spec; gp_assume_spec].
Proof.
  unfold Externals, present, env_harness, filter.
  repeat match goal with |- context [id_in_list ?i ?l] =>
    let b := eval lazy in (id_in_list i l) in change (id_in_list i l) with b end.
  reflexivity.
Qed.

Lemma find_cons {A} i (a: ident * A) l :
  initial_world.find_id i (a :: l) = if Pos.eqb i (fst a) then Some (snd a) else initial_world.find_id i l.
Proof.
  destruct a as [j x]. simpl. destruct (Memory.EqDec_ident i j) as [E|Hne].
  - subst. rewrite Pos.eqb_refl. reflexivity.
  - destruct (Pos.eqb_spec i j); [contradiction | reflexivity].
Qed.

Ltac find_steps :=
  repeat (rewrite find_cons;
          match goal with |- context [Pos.eqb ?i (fst ?a)] =>
            let b := eval lazy in (Pos.eqb i (fst a)) in change (Pos.eqb i (fst a)) with b end;
          cbv beta iota).

Lemma Gprog_cons : Gprog API Hs =
  (_quickproof_malloc, malloc_spec') :: (_quickproof_free, free_spec') ::
  ZSTD_getDictID_fromFrame_spec :: Zstd.proof.zstd.Spec_xxh.ZSTD_XXH64_spec ::
  [nondet_u8_spec; nondet_u32_spec; nondet_size_spec; nondet_bytes_nn_spec; gp_assert_spec; gp_assume_spec] ++
  Hs ++ [main_spec].
Proof. unfold Gprog, Imports. rewrite Externals_eq. reflexivity. Qed.

(* an entry (i, fs) of a list found in Gprog *)
Ltac in_gprog :=
  match goal with |- initial_world.find_id ?i _ = Some ?fs =>
    rewrite Gprog_cons; unfold Hs; cbn [app]; find_steps; reflexivity end.

Lemma G0_in_Gprog i fs : initial_world.find_id i G0 = Some fs ->
  initial_world.find_id i (Gprog API Hs) = Some fs.
Proof.
  intros Hi. apply initial_world.find_id_e in Hi. unfold G0 in Hi.
  rewrite Gprog_cons. unfold Hs. cbn [app].
  repeat destruct Hi as [E|Hi];
    try match type of E with ?a = (i, fs) =>
      replace i with (fst a) by (rewrite E; reflexivity);
      replace fs with (snd a) by (rewrite E; reflexivity) end;
    try contradiction;
    find_steps; reflexivity.
Qed.

Lemma make_tycontext_g_find (Vs: varspecs) (G: funspecs) i :
  Maps.PTree.get i (make_tycontext_g Vs G) =
  match initial_world.find_id i G with Some fs => Some (type_of_funspec fs) | None => Maps.PTree.get i (make_tycontext_g Vs nil) end.
Proof.
  induction G as [|[j fs] G IH]; simpl; auto.
  rewrite Maps.PTree.gsspec. unfold make_tycontext_g in IH |- *. simpl in IH.
  destruct (peq i j) as [->|Hne].
  - rewrite if_true by reflexivity. reflexivity.
  - rewrite if_false by exact Hne. exact IH.
Qed.

Lemma mtg_none (V: varspecs) i : ~ In i (map fst V) -> Maps.PTree.get i (make_tycontext_g V []) = None.
Proof.
  unfold make_tycontext_g. induction V as [|[k t] V IH]; simpl; intros Hn.
  - apply Maps.PTree.gempty.
  - rewrite Maps.PTree.gsspec. destruct (peq i k); [subst; tauto |]. apply IH. tauto.
Qed.

(* no function name of Gprog is a global variable of the program *)
Lemma Gprog_not_var i : In i (map fst (Gprog API Hs)) -> ~ In i (map fst Vprog).
Proof.
  intros Hin Hv.
  assert (Hb: forallb (fun j => negb (id_in_list j (map fst Vprog))) (map fst (Gprog API Hs)) = true).
  { match goal with |- forallb ?f ?l = true => let L := eval lazy in l in change l with L end.
    vm_compute. reflexivity. }
  rewrite forallb_forall in Hb. specialize (Hb i Hin).
  rewrite (Zstd.proof.top.MainPre6.MP_id_in_list_true_i i _ Hv) in Hb. discriminate.
Qed.

(* a helper of the frames kit: its body, proved once at any compspecs, in Gprog *)
Ltac kit_body fn fk Gk body :=
  exists fn; split; [vm_compute; reflexivity|]; split; [reflexivity|];
  let E := fresh "E" in
  assert (E: fn = fk) by (vm_compute; reflexivity);
  rewrite E; apply (Zstd.proof.harness.frames.FTransfer.fk_transfer Vprog _ Gk);
  [ exact body
  | apply Zstd.proof.harness.frames.FTransfer.fk_find_all; repeat constructor; in_gprog ].

Theorem api_dict_id_ok : HarnessOK API Hs.
Proof.
  split.
  - vm_compute. reflexivity.
  - constructor; [| constructor; [| constructor; [| constructor; [| constructor; [| constructor;
      [| constructor; [| constructor; [| constructor]]]]]]]].
    + kit_body Zstd.harness.api_dict_id.code.f_copy_of FSpecs.f_copy_of (@G_copy_of CompSpecs)
        (@Zstd.proof.harness.frames.FBodiesSmall.body_copy_of CompSpecs).
    + kit_body Zstd.harness.api_dict_id.code.f_any_bytes FSpecs.f_any_bytes (@G_any_bytes CompSpecs)
        (@Zstd.proof.harness.frames.FBodiesSmall.body_any_bytes CompSpecs).
    + kit_body Zstd.harness.api_dict_id.code.f_upto FSpecs.f_upto G_upto (@Zstd.proof.harness.frames.FBodiesSmall.body_upto CompSpecs).
    + kit_body Zstd.harness.api_dict_id.code.f_put_le FSpecs.f_put_le G_put_le
        (@Zstd.proof.harness.frames.FBodiesSmall.body_put_le CompSpecs).
    + kit_body Zstd.harness.api_dict_id.code.f_join FSpecs.f_join (@G_join CompSpecs)
        (@Zstd.proof.harness.frames.FBodiesSmall.body_join CompSpecs).
    + kit_body Zstd.harness.api_dict_id.code.f_new_skippable FSpecs.f_new_skippable (@G_new_skippable CompSpecs)
        (@Zstd.proof.harness.frames.FBodiesSmall.body_new_skippable CompSpecs).
    + kit_body Zstd.harness.api_dict_id.code.f_new_frame FSpecs.f_new_frame (@G_new_frame CompSpecs)
        (@Zstd.proof.harness.frames.FBodyNewFrame.body_new_frame CompSpecs).
    + (* main *)
      exists f_main. split; [reflexivity|]. split; [reflexivity|].
      eapply semax_body_subsumption; [apply body_main_G0 |].
      apply tycontext_sub_i99. split; intro i.
      * rewrite (make_tycontext_g_find Vprog G0 i).
        rewrite (make_tycontext_g_find Vprog (Gprog API Hs) i).
        destruct (initial_world.find_id i G0) as [fs|] eqn:E.
        -- rewrite (G0_in_Gprog i fs E). apply sub_option_refl.
        -- destruct (initial_world.find_id i (Gprog API Hs)) as [fs'|] eqn:E'.
           ++ rewrite mtg_none; [exact Logic.I |].
              apply (Gprog_not_var i).
              apply initial_world.find_id_e in E'. apply (in_map fst) in E'. exact E'.
           ++ apply sub_option_refl.
      * rewrite !semax_prog.find_id_maketycontext_s.
        destruct (initial_world.find_id i G0) as [fs|] eqn:E; [|exact Logic.I].
        rewrite (G0_in_Gprog i fs E). exists fs. split; [reflexivity|]. apply funspec_sub_si_refl.
Qed.
