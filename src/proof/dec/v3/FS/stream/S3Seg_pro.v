(* FS3 streaming: the prologue of ZSTD_decompressStream with the exact claim.
   Split for the checker's time budget: pure facts (pro2/Q3ProPure, pro2/Q3Content), the context split (pro/P3ProCtx),
   and the statements of the prologue in pieces, each the next one's caller: here statements 0-1, then
   pro2/Q3ProB (2-4), Q3ProC (5-6), Q3ProD (7-10), Q3ProD2 (11-12), Q3ProE (13: ZSTD_checkOutBuffer; the loop
   invariant and the model's loop start). *)
Require Import Zstd.proof.dec.v3.FS.stream.S3RetStmts Zstd.proof.dec.v3.FS.stream.S3ModelStmts.
Require Import Zstd.proof.dec.v3.FS.stream.pro2.Q3ProPure Zstd.proof.dec.v3.FS.stream.pro2.Q3ProB.
Local Open Scope logic.

Section CM_S3Seg_pro_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* the prologue: from the precondition (the context's exact relation included) to the loop's first state, where the
   model's loop starts at the state of the calls before this one (S3XKit.ex_call_start, in pro2/Q3ProE) *)
Lemma seg_prologue_x_ok : MF3 -> RET3x -> seg_prologue_x.
Proof.
intros _ _. unfold seg_prologue_x. intros Espec DENT TABS BR a REST HD HT Hok HREST0.
assert (HREST: pro_rest Espec DENT TABS BR a REST) by exact HREST0. clear HREST0.
pose proof Hok as Hok0. unfold dsa_ok in Hok.
destruct Hok as (Hbo & Hbi & Hsob & Wsho & Wshi & Wshob & Rshb & Hdict & Herr & Hopos & Hosz & Hoc & Hipos & Hisz & Hibs & Hbibs & HI2 & HF6 & Hpos & _).
unfold DC3x, DC3_of. Intros k.
match goal with H: base_rel3 _ _ |- _ => rename H into Hbr end.
match goal with H: dc_ss (a_st a) <> ss_init -> _ |- _ => rename H into HSR end.
match goal with H: ex_on3 _ _ _ |- _ => rename H into HX end.
assert_PROP (cold01 (c3_fs k) /\ sf_inSize (c3_s k) + sf_outSize (c3_s k) <= 2 ^ 32) as HF.
{ unfold ctx_rep3, ctx_body3, fgroup3, sgroup. entailer!. }
pose proof (pro_view (a_gv a) (a_st a) k (a_obf a) (a_osz a) HF Hbr HSR Herr Hsob) as PV.
assert (H0: pro_hyp Espec DENT TABS BR a REST k) by (split; [exact HD | split; [exact HT | split; [exact Hok0 | split; [exact Hbr | split; [exact PV | split; [exact HREST | exact HX]]]]]]).
clear HSR HF PV HREST HX.
pose proof (pro_segB Espec DENT TABS BR a REST k H0) as HE.
unfold pro_L2, pro_S0, ds_R_x, ds_post_x in HE |- *.
unfold ds_prologue. simpl sdrop.
unfold ds_Delta. simplify_func_tycontext.
assert_PROP (isptr (a_ib a)) as Hib by entailer!.
(* the input field may be NULL; otherwise it is the base, a pointer *)
assert (Hibf: is_pointer_or_null (a_ibf a)).
{ destruct (nbase_cases (a_gv a) (a_ibf a)) as [[_ E]|[E _]];
  [unfold a_ib in Hib; rewrite E in Hib; destruct (a_ibf a); try contradiction; simpl; auto
  | rewrite E; simpl; auto]. }
forward.
(* F9: src = input->src != NULL ? input->src : ZSTD_emptyBuffer, the base a_ib a *)
forward_if (temp _t'1 (a_ib a)).
{ destruct (nbase_cases (a_gv a) (a_ibf a)) as [[Hin Eib] | [Hin Eib]]; change (nbase (a_gv a) (a_ibf a)) with (a_ib a) in Eib.
  - rewrite Eib in Hbi.
    eapply derives_trans; [| apply (buf_ok_null_test (a_W a) (a_shb a) (a_isz a) (zbytes (a_ibs a)) (a_ibf a) TT Hbi)].
    rewrite Eib. cancel.
  - rewrite Hin. entailer!. }
{ forward. forward. entailer!. all: unfold a_ib; rewrite nbase_ptr; auto. }
{ forward. entailer!. all: unfold a_ib; rewrite H, nbase_null; destruct a; reflexivity. }
forward.
forward.
forward_if (temp _t'2 (offset_val (a_ipos a) (a_ib a))).
{ forward. forward. entailer!. }
{ z0. forward. entailer!; match goal with E: ?x = 0 |- offset_val ?x _ = _ => rewrite E; apply isptr_offset_val_zero; auto end. }
forward.
eapply semax_pre; [| exact HE].
entailer!.
Qed.

End CM_S3Seg_pro_1.
