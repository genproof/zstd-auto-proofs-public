(* The harness obligation of rj_reserved_block (harness/rj_reserved_block.c): for ANY predicates DC, DD of the
   decoder's API (Spec_api6), with the API [ZSTD_isError; ZSTD_getErrorCode; ZSTD_decompress; ZSTD_createDStream;
   ZSTD_decompressStream; ZSTD_XXH64] (the last for new_frame's checksums), the helpers of laws_common.h and
   frames.h (proved once in the frames kit) and main (Body_rj_reserved_block) satisfy their specifications. *)
Require Import VST.floyd.proofauto.
Require Zstd.proof.harness.frames.FBodiesSmall Zstd.proof.harness.frames.FTransfer.
Require Zstd.proof.harness.frames.FBodyNewFrame Zstd.proof.harness.frames.FBodyStreamAll.
Require Import Zstd.proof.harness.frames.FStreamRefused.
Require Import Zstd.proof.harness.rj_reserved_block.Facts_rj_reserved_block.
Import Zstd.proof.harness.frames.FSpecs Zstd.proof.harness.frames.FStreamSpec.
Require Export Zstd.proof.harness.rj_reserved_block.Body_rj_reserved_block.

(* the model facts main's proof uses, proved *)
Lemma rb_facts_ok : rb_facts.
Proof.
  exact (conj rb_first (conj rb_hdr_in (conj rb_last (conj rb_next (conj rb_refused (conj rb_series_unk
           (conj reserved_at_length (conj reserved_at_ok stream_refused_no_end)))))))).
Qed.

(* the API of the law *)
Definition API DC DD : funspecs :=
  [Zstd.proof.zstd.Spec_util.ZSTD_isError_spec; Zstd.proof.zstd.Spec_util.ZSTD_getErrorCode_spec;
   ZSTD_decompress_spec; ZSTD_createDStream_spec DC; ZSTD_decompressStream_spec DC DD;
   Zstd.proof.zstd.Spec_xxh.ZSTD_XXH64_spec].

(* ---------- from G0 to Gprog (API DC DD) Hs ---------- *)

(* the harness's own functions besides main (in the order of helper_ids): the frames kit's helpers *)
Definition Hs DC DD : funspecs :=
  [out_of_memory_spec; @copy_of_spec CompSpecs; @stream_all_spec CompSpecs DC DD; @any_bytes_spec CompSpecs;
   upto_spec; @put_le_spec CompSpecs; @new_frame_spec CompSpecs].

Lemma Externals_eq : Externals =
  [nondet_u8_spec; nondet_size_spec; nondet_bytes_nn_spec; gp_assert_spec; gp_assume_spec].
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

Lemma Gprog_cons DC DD : Gprog (API DC DD) (Hs DC DD) =
  (_quickproof_malloc, malloc_spec') :: (_quickproof_free, free_spec') ::
  API DC DD ++
  [nondet_u8_spec; nondet_size_spec; nondet_bytes_nn_spec; gp_assert_spec; gp_assume_spec] ++
  Hs DC DD ++ [main_spec].
Proof. unfold Gprog, Imports. rewrite Externals_eq. reflexivity. Qed.

(* an entry (i, fs) of a list found in Gprog *)
Ltac in_gprog :=
  match goal with |- initial_world.find_id ?i _ = Some ?fs =>
    rewrite Gprog_cons; unfold API, Hs; cbn [app]; find_steps; reflexivity end.

Lemma G0_in_Gprog DC DD i fs : initial_world.find_id i (G0 DC DD) = Some fs ->
  initial_world.find_id i (Gprog (API DC DD) (Hs DC DD)) = Some fs.
Proof.
  intros Hi. apply initial_world.find_id_e in Hi. unfold G0 in Hi.
  rewrite Gprog_cons. unfold API, Hs. cbn [app].
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
Lemma Gprog_not_var DC DD i : In i (map fst (Gprog (API DC DD) (Hs DC DD))) -> ~ In i (map fst Vprog).
Proof.
  intros Hin Hv.
  assert (Hb: forallb (fun j => negb (id_in_list j (map fst Vprog))) (map fst (Gprog (API DC DD) (Hs DC DD))) = true).
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

Theorem rj_reserved_block_ok :
  forall (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred),
    HarnessOK (API DC DD) (Hs DC DD).
Proof.
  intros DC DD. split.
  - vm_compute. reflexivity.
  - constructor; [| constructor; [| constructor; [| constructor; [| constructor; [| constructor;
      [| constructor; [| constructor; [| constructor]]]]]]]].
    + kit_body Zstd.harness.rj_reserved_block.code.f_out_of_memory FSpecs.f_out_of_memory G_out_of_memory
        (@Zstd.proof.harness.frames.FBodiesSmall.body_out_of_memory CompSpecs).
    + kit_body Zstd.harness.rj_reserved_block.code.f_copy_of FSpecs.f_copy_of (@G_copy_of CompSpecs)
        (@Zstd.proof.harness.frames.FBodiesSmall.body_copy_of CompSpecs).
    + kit_body Zstd.harness.rj_reserved_block.code.f_stream_all FStreamSpec.f_stream_all (G_stream_all DC DD)
        (@Zstd.proof.harness.frames.FBodyStreamAll.body_stream_all CompSpecs
           ltac:(Zstd.proof.harness.frames.FBodyStreamAll.fs_cspecs_sub) DC DD).
    + kit_body Zstd.harness.rj_reserved_block.code.f_any_bytes FSpecs.f_any_bytes (@G_any_bytes CompSpecs)
        (@Zstd.proof.harness.frames.FBodiesSmall.body_any_bytes CompSpecs).
    + kit_body Zstd.harness.rj_reserved_block.code.f_upto FSpecs.f_upto G_upto
        (@Zstd.proof.harness.frames.FBodiesSmall.body_upto CompSpecs).
    + kit_body Zstd.harness.rj_reserved_block.code.f_put_le FSpecs.f_put_le G_put_le
        (@Zstd.proof.harness.frames.FBodiesSmall.body_put_le CompSpecs).
    + kit_body Zstd.harness.rj_reserved_block.code.f_new_frame FSpecs.f_new_frame (@G_new_frame CompSpecs)
        (@Zstd.proof.harness.frames.FBodyNewFrame.body_new_frame CompSpecs).
    + (* main *)
      exists f_main. split; [reflexivity|]. split; [reflexivity|].
      eapply semax_body_subsumption; [apply (body_main_G0 DC DD rb_facts_ok) |].
      apply tycontext_sub_i99. split; intro i.
      * rewrite (make_tycontext_g_find Vprog (G0 DC DD) i).
        rewrite (make_tycontext_g_find Vprog (Gprog (API DC DD) (Hs DC DD)) i).
        destruct (initial_world.find_id i (G0 DC DD)) as [fs|] eqn:E.
        -- rewrite (G0_in_Gprog DC DD i fs E). apply sub_option_refl.
        -- destruct (initial_world.find_id i (Gprog (API DC DD) (Hs DC DD))) as [fs'|] eqn:E'.
           ++ rewrite mtg_none; [exact Logic.I |].
              apply (Gprog_not_var DC DD i).
              apply initial_world.find_id_e in E'. apply (in_map fst) in E'. exact E'.
           ++ apply sub_option_refl.
      * rewrite !semax_prog.find_id_maketycontext_s.
        destruct (initial_world.find_id i (G0 DC DD)) as [fs|] eqn:E; [|exact Logic.I].
        rewrite (G0_in_Gprog DC DD i fs E). exists fs. split; [reflexivity|]. apply funspec_sub_si_refl.
Qed.
