(* Shared definitions of the harness obligations (src/proof/harness/<h>/HOK_<h>.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Export QuickProof.Env.
Require Export Zstd.proof.libc.LibcOk.
Import compcert.lib.Maps.

(* the external functions a unit declares *)
Definition ExtIDs (p: QP.program function) : list ident :=
  map fst (filter (fun x => match snd x with Gfun (External _ _ _ _) => true | _ => false end)
                  (PTree.elements (QP.prog_defs p))).

(* nondet_bytes on a buffer that is not NULL, as the harness proofs call it: a weakening of
   QuickProof.Env.nondet_bytes_spec, which also allows NULL with n = 0 (nondet_bytes_nn_sub below). *)
Definition nondet_bytes_nn_spec {cs: compspecs} :=
  DECLARE _nondet_bytes
  WITH buf: val, n: Z, sh: share
  PRE  [ tptr tuchar, tulong ]
       PROP (writable_share sh; 0 <= n <= Int64.max_unsigned)
       PARAMS (buf; Vlong (Int64.repr n))
       SEP (data_at_ sh (tarray tuchar n) buf)
  POST [ tvoid ] EX bs: list Z,
       PROP (Zlength bs = n; Forall (fun b => 0 <= b <= Byte.max_unsigned) bs)
       RETURN ()
       SEP (data_at sh (tarray tuchar n) (map (fun b => Vint (Int.repr b)) bs) buf).

Lemma nondet_bytes_nn_sub {cs: compspecs} : funspec_sub (snd nondet_bytes_spec) (snd nondet_bytes_nn_spec).
Proof.
  apply NDsubsume_subsume; [split; reflexivity|].
  split; [split; reflexivity|].
  intros x gargs. destruct x as [[buf n] sh]. destruct gargs as [g args]. simpl.
  unfold PROPx; simpl. unfold_for_go_lower; simpl. normalize.
  assert_PROP (isptr buf) as Hp by entailer!.
  Exists (buf, n, sh) (@emp mpred _ _). rewrite emp_sepcon. simpl.
  rewrite if_false by (intro E; subst; contradiction).
  apply andp_right.
  - apply andp_right; [apply prop_right; split; [auto | split; [lia | auto]] |].
    apply andp_right; [apply prop_right; reflexivity |].
    apply andp_right; [apply TT_right |]. rewrite !sepcon_emp. apply derives_refl.
  - apply prop_right; intros rho'. rewrite emp_sepcon. apply andp_left2.
    apply exp_derives; intros bs. rewrite if_false by (intro E; subst; contradiction). apply derives_refl.
Qed.

(* the functions a harness may call besides malloc/free (its Imports): the environment's, and memcpy of the
   libc unit (the harnesses copy byte strings) *)
Definition env_harness {cs: compspecs} : funspecs :=
  [ nondet_u8_spec; nondet_u32_spec; nondet_size_spec; nondet_bytes_nn_spec;
    gp_assert_spec; gp_assume_spec; memcpy_spec ].

(* the entries of fs whose function is among ids *)
Definition present (ids: list ident) (fs: funspecs) : funspecs :=
  filter (fun ix => id_in_list (fst ix) ids) fs.
