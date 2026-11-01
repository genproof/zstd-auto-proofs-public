(* BSubs3.v on DecLiftP34 (DecLift.v with the fParams conjunct of usingDict_spec3's error branch), plus ins34_sub.
   The v3 specifications of group DICT imply their v2 versions (funspec_sub), so that the v2 body
   proofs of the unchanged DICT functions lift to the v3 context (DecLift.body_ok_sub); and the decompressBegin
   spec B proves implies DecIface3's export. *)
Require Export Zstd.proof.dec.v3.B.BSpecs34 Zstd.proof.dec.v3.B.DecLiftP34.
Require Import Zstd.proof.dec.B.dict.body_dict_ins.
Local Open Scope logic.

Lemma begin3s_sub : funspec_sub (snd ZSTD_decompressBegin_spec3s) (snd ZSTD_decompressBegin_spec).
Proof.
  apply NDsubsume_subsume; [split; reflexivity|].
  split; [split; reflexivity|].
  intros [[[gv p] fs] lxb] [g args]. simpl.
  Exists (gv, p, fs, 0, lxb) (cfg_lit p). simpl.
  rewrite cfg_b_split, fs_begin3_zstd1. apply andp_right.
  - apply andp_left2. unfold PROPx, LOCALx, SEPx, PARAMSx, GLOBALSx; simpl. normalize.
    apply andp_right; [apply prop_right; auto |]. unfold argsassert2assert; simpl.
    unfold LOCALx; simpl. unfold local, lift1; simpl. normalize. cancel.
  - apply prop_right; intros rho'. unfold PROPx, LOCALx, SEPx; simpl. normalize.
    unfold local, lift1; simpl. normalize. cancel.
Qed.

Lemma begin3s_api_sub :
  funspec_sub (snd ZSTD_decompressBegin_spec3s) (snd (ZSTD_decompressBegin_spec3 tabs_def)).
Proof.
  apply NDsubsume_subsume; [split; reflexivity|].
  split; [split; reflexivity|].
  intros [[[[gv p] fs] f] lxb] [g args]. simpl.
  Exists (gv, p, fs, f, lxb) (@emp mpred _ _). rewrite emp_sepcon. simpl.
  apply andp_right.
  - apply andp_left2. apply derives_refl.
  - apply prop_right; intros rho'. rewrite emp_sepcon. unfold PROPx, LOCALx, SEPx; simpl. normalize.
    apply andp_derives; [auto |]. sep_apply (begin_tabs_init gv p false lxb). unfold tstate_begin. cancel.
Qed.

Lemma ins3_sub :
  funspec_sub (snd ZSTD_decompress_insertDictionary_spec3) (snd ZSTD_decompress_insertDictionary_spec).
Proof.
  apply NDsubsume_subsume; [split; reflexivity|].
  split; [split; reflexivity|].
  intros [[[[[[gv p] fs] shk] dk] b] lxb] [g args]. simpl.
  Exists (gv, p, fs, shk, dk, b, 0, lxb) (@emp mpred _ _). rewrite emp_sepcon. simpl.
  rewrite !fs_begin3_zstd1. apply andp_right.
  - apply andp_left2. apply derives_refl.
  - apply prop_right; intros rho'. rewrite emp_sepcon. apply andp_left2. apply derives_refl.
Qed.

Lemma loadinto3_sub :
  funspec_sub (snd ZSTD_loadEntropy_intoDDict_spec3) (snd ZSTD_loadEntropy_intoDDict_spec).
Proof.
  apply NDsubsume_subsume; [split; reflexivity|].
  split; [split; reflexivity|].
  intros [[[[[gv q] sh] buf] b] ctype] [g args]. simpl.
  Exists (gv, q, sh, buf, b, ctype) (@emp mpred _ _). rewrite emp_sepcon. simpl.
  match goal with |- ?L |-- _ => assert (Hct: L |-- !! (ctype = 0 \/ ctype = 1)) end.
  { apply andp_left2. unfold PROPx; simpl. normalize. }
  rewrite (add_andp _ _ Hct). clear Hct. rewrite andp_comm. apply derives_extract_prop; intros Hct.
  assert (E2: (ctype =? 2) = false) by (apply Z.eqb_neq; lia).
  (* v2's bytes are at a pointer (data_at) *)
  match goal with |- ?L |-- _ => assert (Hb: L |-- !! isptr buf) end.
  { apply andp_left2. unfold PROPx, LOCALx, SEPx, PARAMSx, GLOBALSx; simpl. normalize.
    unfold LOCALx, argsassert2assert; simpl. unfold local, lift1; simpl. entailer!. }
  rewrite (add_andp _ _ Hb). clear Hb. rewrite andp_comm. apply derives_extract_prop; intros Hb.
  apply andp_right.
  - apply andp_left2. unfold PROPx, LOCALx, SEPx, PARAMSx, GLOBALSx; simpl. normalize.
    rewrite (bytes_at_ptr sh b buf Hb).
    apply andp_right; [apply prop_right | apply derives_refl].
    split; [| auto]. split; [auto |]. split; [auto |]. split; [tauto |].
    split; [intros E; subst buf; contradiction | auto].
  - apply prop_right; intros rho'. rewrite emp_sepcon. apply andp_left2. rewrite E2. simpl andb.
    rewrite (bytes_at_ptr sh b buf Hb).
    apply derives_refl.
Qed.

Lemma ins34_sub :
  funspec_sub (snd ZSTD_decompress_insertDictionary_spec34) (snd ZSTD_decompress_insertDictionary_spec).
Proof. eapply funspec_sub_trans; [apply ins34_sub3 | apply ins3_sub]. Qed.
