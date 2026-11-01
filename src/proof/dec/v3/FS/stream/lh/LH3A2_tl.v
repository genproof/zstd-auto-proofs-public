(* FS3 streaming, case zdss_loadHeader, piece A: what the tail lemmas share (opening the state between
   the prefix and the tail, rewriting the projections of k_A / lw_k). *)
Require Export Zstd.proof.dec.v3.FS.stream.lh.LH3A_lib.
Require Export Zstd.proof.dec.v3.FS.stream.lh.LH3A2_pre.
Local Open Scope logic.

Section CM_LH3A2_tl_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma kA_fp k v d1 did1 : fs_fParams (c3_fs (k_A k v d1 did1)) = v.
Proof. reflexivity. Qed.
Lemma kA_s k v d1 did1 : c3_s (k_A k v d1 did1) = held_redict (c3_s k) (c3_dict k) d1.
Proof. reflexivity. Qed.
Lemma kA_par k v d1 did1 : c3_par (k_A k v d1 did1) = c3_par k.
Proof. reflexivity. Qed.
Lemma lw_k_k w k : w_k (lw_k w k) = k.
Proof. reflexivity. Qed.
Lemma lw_k_opc w k : w_opc (lw_k w k) = w_opc w.
Proof. reflexivity. Qed.
Lemma lw_k_oc w k : w_oc (lw_k w k) = w_oc w.
Proof. reflexivity. Qed.
Lemma lw_k_ipc w k : w_ipc (lw_k w k) = w_ipc w.
Proof. reflexivity. Qed.
Lemma lw_k_smw w k : w_smw (lw_k w k) = w_smw w.
Proof. reflexivity. Qed.

End CM_LH3A2_tl_1.

Ltac a3_rw := rewrite ?lw_k_k, ?lw_k_opc, ?lw_k_oc, ?lw_k_ipc, ?lw_k_smw, ?kA_fp, ?kA_s, ?kA_par, ?hr_lh, ?hr_hbuf, ?hr_mem.

Ltac a3_open :=
  unfold lhA_mid, ds_LI_St, ds_LI_L; rewrite ctxA_split; Intros; a3_rw;
  repeat match goal with H: ctxA_props (w_k (lw_k _ _)) |- _ => rewrite lw_k_k in H end;
  unfold ds_Delta; simplify_func_tycontext; unfold lhA_t; abbreviate_semax.

Section CM_LH3A2_tl_2.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.

(* the context after the header bytes were copied *)
Lemma kL_fp a w k hb m v' : fs_fParams (c3_fs (lh_k_load a w k hb m v')) = v'.
Proof. reflexivity. Qed.
Lemma kL_par a w k hb m v' : c3_par (lh_k_load a w k hb m v') = c3_par k.
Proof. reflexivity. Qed.
Lemma kL_lh a w k hb m v' : sf_lhSize (c3_s (lh_k_load a w k hb m v')) = vlong (Zlength hb + m).
Proof. reflexivity. Qed.
Lemma kL_hbuf a w k hb m v' :
  sf_hbuf (c3_s (lh_k_load a w k hb m v')) =
  hb_splice (sf_hbuf (c3_s k)) (Zlength hb) (sublist (w_ipc w) (w_ipc w + m) (a_ibs a)).
Proof. reflexivity. Qed.
Lemma kL_props a w k hb m v' :
  ctxA_props k -> Zlength (hb_splice (sf_hbuf (c3_s k)) (Zlength hb) (sublist (w_ipc w) (w_ipc w + m) (a_ibs a))) = 18 ->
  ctxA_props (lh_k_load a w k hb m v').
Proof.
intros (H1 & H2 & H3) H4. split3; auto.
unfold sg_props in *. simpl. tauto.
Qed.

Lemma brk_k a w k1 hb kk : w_k (lhA_brk a w k1 hb kk) = lh_k_load a w k1 hb (kk - Zlength hb) (fs_fParams (c3_fs k1)).
Proof. reflexivity. Qed.
Lemma brk_opc a w k1 hb kk : w_opc (lhA_brk a w k1 hb kk) = w_opc w.
Proof. reflexivity. Qed.
Lemma brk_oc a w k1 hb kk : w_oc (lhA_brk a w k1 hb kk) = w_oc w.
Proof. reflexivity. Qed.
Lemma brk_ipc a w k1 hb kk : w_ipc (lhA_brk a w k1 hb kk) = w_ipc w + (kk - Zlength hb).
Proof. reflexivity. Qed.
Lemma brk_smw a w k1 hb kk : w_smw (lhA_brk a w k1 hb kk) = w_smw w.
Proof. reflexivity. Qed.

End CM_LH3A2_tl_2.

Ltac a3_rwL := rewrite ?brk_k, ?brk_opc, ?brk_oc, ?brk_ipc, ?brk_smw, ?kL_fp, ?kL_par, ?kL_lh, ?kL_hbuf, ?ctxA_rest_load.

