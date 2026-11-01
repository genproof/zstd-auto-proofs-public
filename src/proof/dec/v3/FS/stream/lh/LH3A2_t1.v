(* FS3 streaming, case zdss_loadHeader, piece A: the tail lh_A after the selection, cases "the header
   is invalid" (error return) and "a complete header" (normal exit). *)
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3A2_tl.
Local Open Scope logic.

Section CM_LH3A2_t1_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.



Lemma lhA_t_err : forall (Espec: OracleKind) DENT TABS BR (a: dsa) (w: lw) (hb: list Z) r v tbl d1 did1,
  DENT_OK DENT -> TABS_OK TABS -> dsa_ok a -> lh_entry a w hb ->
  lhA_sel (w_k w) hb r v tbl d1 did1 -> get_frame_header_m (lh_mg (w_k w)) hb = FH_err ->
  GAP_fherr -> fp_ok v ->
  semax (ds_Delta DENT TABS BR) (lhA_mid DENT TABS a w r v tbl d1 did1) lhA_t (lhA_post DENT TABS a w hb).
Proof.
intros Espec DENT TABS BR a w hb r v tbl d1 did1 HD HT Ha He Hsel Eg Hfh Hfpv.
a3_open.
assert (Hsel' := Hsel). destruct Hsel' as (Hr & Hpost & _).
unfold fh_post_m in Hpost. rewrite Eg in Hpost.
forward_call r.
destruct Hpost as [[Hpe _] _]. rewrite Hpe.
forward_if False.
2: { Intros. discriminate. }
a3_return.
cbv beta iota delta [overridePost lhA_post RA_return lh_ret].
Exists r (a_ipos a) (lw_k w (k_A (w_k w) v d1 did1)).
unfold ds_S_ip, ds_LI_L. rewrite ctx_rep3_t. Exists tbl. rewrite ctxA_split. a3_rw.
entailer!.
apply (RC_hdr a w hb r v tbl d1 did1); auto.
Qed.

Lemma lhA_t_ok : forall (Espec: OracleKind) DENT TABS BR (a: dsa) (w: lw) (hb: list Z) r v tbl d1 did1 h,
  DENT_OK DENT -> TABS_OK TABS -> dsa_ok a -> lh_entry a w hb ->
  lhA_sel (w_k w) hb r v tbl d1 did1 -> get_frame_header_m (lh_mg (w_k w)) hb = FH_ok h ->
  semax (ds_Delta DENT TABS BR) (lhA_mid DENT TABS a w r v tbl d1 did1) lhA_t (lhA_post DENT TABS a w hb).
Proof.
intros Espec DENT TABS BR a w hb r v tbl d1 did1 h HD HT Ha He Hsel Eg.
assert (Hsel' := Hsel). destruct Hsel' as (Hr & Hpost & _).
unfold fh_post_m in Hpost. rewrite Eg in Hpost. destruct Hpost as [-> ->].
a3_open.
forward_call 0.
rewrite (a3_small_noerr 0) by lia.
match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
  forward_if (PROPx P (LOCALx Q (SEPx R))) end.
{ a3_absurd. }
{ forward. apply ENTAIL_refl. }
forward_if.
{ a3_absurd. }
forward.
cbv beta iota delta [overridePost lhA_post RA_normal].
Exists h tbl d1 did1.
unfold ds_LI_St, ds_LI_L. rewrite ctxA_split. a3_rw.
entailer!.
Qed.

End CM_LH3A2_t1_1.
