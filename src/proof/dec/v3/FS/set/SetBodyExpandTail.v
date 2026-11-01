(* FS3 set part, ZSTD_DDictHashSet_expand: from the test of the new table (calloc succeeded) to the end. *)
Require Import Zstd.proof.dec.v3.FS.set.SetDefs Zstd.proof.dec.v3.FS.set.SetBodyExpandLoop.
Local Open Scope logic.

Section CM_SetBodyExpandTail_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* `RETURN_ERROR_IF(!newTable, ...)` and the rest of the body *)
Definition exp_rest : statement :=
  ltac:(let f := eval cbv delta [f_ZSTD_DDictHashSet_expand] in f_ZSTD_DDictHashSet_expand in
        lazymatch f with context [Ssequence (Sloop (Sifthenelse (Eunop Onotbool (Etempvar _newTable ?t1) ?t2) ?a Sskip) Sbreak) ?R] =>
          exact (Ssequence (Sloop (Sifthenelse (Eunop Onotbool (Etempvar _newTable t1) t2) a Sskip) Sbreak) R) end).

Lemma exp_tail {Espec: OracleKind} : MF_ddid_wvp -> MF_ids_focus -> PF_member -> MF_tbl_bytes -> PF_inv0 ->
  PF_exp_init -> PF_exp_step -> PF_exp_skip -> PF_exp_end ->
  forall gv sp l tbl shm pm am h otp q,
  readable_share shm -> hs_inv l tbl -> Zlength tbl <= 2 ^ 23 -> cmem_ok am -> cm_room am h (8 * (2 * Zlength tbl)) ->
  field_compatible (tarray (tptr t_ddict) (Zlength tbl)) nil otp -> q <> nullval ->
  semax (func_tycontext f_ZSTD_DDictHashSet_expand Vprog G_expand nil)
   (PROP ()
    LOCAL (temp _oldTableSize (Vlong (Int64.repr (Zlength tbl))); temp _oldTable otp; temp _newTable q;
           temp _t'1 q; temp _newTableSize (Vlong (Int64.repr (2 * Zlength tbl)));
           temp _t'6 (Vlong (Int64.repr (Zlength tbl))); gvars gv; temp _hashSet sp; temp _customMem pm)
    SEP (blk_tok am (tarray tuchar (8 * (2 * Zlength tbl))) q;
         data_at Ews (tarray (tptr t_ddict) (2 * Zlength tbl)) (Zrepeat nullval (2 * Zlength tbl)) q; mem_mgr gv;
         data_at shm t_cmem (cmem_v am) pm; cm_have am (h + 8 * (2 * Zlength tbl)); blk_tok am t_hset sp;
         data_at Ews t_hset (otp, (Vlong (Int64.repr (Zlength tbl)), Vlong (Int64.repr (Zlength l)))) sp;
         blk_tok am (tarray tuchar (8 * Zlength tbl)) otp;
         data_at Ews (tarray (tptr t_ddict) (Zlength tbl)) tbl otp; set_ids l))
   exp_rest
   (frame_ret_assert
     (function_body_ret_assert tulong
       (EX r: Z, EX tbl': list val,
        PROP ((r = 0 /\ hs_inv0 l tbl' /\ Zlength tbl' = (2 * Zlength tbl)%Z) \/
              (r = err_code ZSTD_error_memory_allocation /\ tbl' = tbl))
        RETURN (Vlong (Int64.repr r))
        SEP (mem_mgr gv; data_at shm t_cmem (cmem_v am) pm;
             cm_have am (h + set_bytes am (Zlength tbl') - set_bytes am (Zlength tbl)); hs_raw am sp l tbl'; set_ids l))%argsassert)
     (stackframe_of f_ZSTD_DDictHashSet_expand)).
Proof.
intros Hwvp Hfocus Hmem Hbytes Hinv0 Hinit Hstep Hskip Hend gv sp l tbl shm pm am h otp q SH H H0 Hok Hroom H1 Hq.
unfold exp_rest. abbreviate_semax.
assert (Hk: exists k, 6 <= k /\ Zlength tbl = 2 ^ k) by (destruct H; tauto).
destruct Hk as [k [Hk6 Hkn]].
assert (H64: 64 <= Zlength tbl). { rewrite Hkn. replace 64 with (2^6) by reflexivity. apply Z.pow_le_mono_r; lia. }
assert (H23: Zlength tbl <= 8388608) by (simpl in H0; lia).
reassoc. match goal with |- semax _ ?P _ _ => forward_loop P break: P end.
{ entailer!. }
{ forward_if.
  { contradiction. }
  { forward. entailer!. } }
abbreviate_semax.
forward. forward. forward.
assert (Hk1: (2 * Zlength tbl = 2 ^ (k + 1))%Z) by (rewrite Z.pow_add_r by lia; rewrite Hkn; lia).
forward_for_simple_bound (Zlength tbl)
 (EX i: Z, EX t: list val,
   PROP (hs_inv0 (l_upto l tbl i) t; Zlength t = (2 * Zlength tbl)%Z)
   LOCAL (temp _oldTableSize (Vlong (Int64.repr (Zlength tbl))); temp _oldTable otp; temp _newTable q;
          gvars gv; temp _hashSet sp; temp _customMem pm)
   SEP (blk_tok am (tarray tuchar (8 * (2 * Zlength tbl))) q;
        data_at Ews (tarray (tptr t_ddict) (2 * Zlength tbl)) t q; mem_mgr gv;
        data_at shm t_cmem (cmem_v am) pm; cm_have am (h + 8 * (2 * Zlength tbl)); blk_tok am t_hset sp;
        data_at Ews t_hset (q, (Vlong (Int64.repr (2 * Zlength tbl)), Vlong (Int64.repr (Zlength (l_upto l tbl i))))) sp;
        blk_tok am (tarray tuchar (8 * Zlength tbl)) otp;
        data_at Ews (tarray (tptr t_ddict) (Zlength tbl)) tbl otp; set_ids l))%argsassert.
{ Exists (Zrepeat nullval (2 * Zlength tbl)).
  assert (Hl0: l_upto l tbl 0 = nil) by (unfold l_upto; rewrite sublist_nil; reflexivity).
  rewrite Hl0. entailer!.
  rewrite Hk1. apply Hinit. lia. }
{ cbv beta. Intros t.
  unfold POSTCONDITION, MORE_COMMANDS, abbreviate.
  eapply semax_post; [ | | | | exact (exp_loop_step Hwvp Hfocus Hmem Hinv0 Hstep Hskip gv sp l tbl shm pm am (h + 8 * (2 * Zlength tbl)) otp q i t H H0 H2 H3 H4) ].
  all: unfold normal_ret_assert, for_ret_assert; simpl RA_normal; simpl RA_break; simpl RA_continue; simpl RA_return.
  { apply andp_left2, derives_refl. }
  1,2: apply andp_left2; intro rho; apply prop_left; contradiction.
  intros vl; apply andp_left2; intro rho; apply prop_left; contradiction. }
Intros t.
match goal with Hi: hs_inv0 (l_upto l tbl (Zlength tbl)) t |- _ => destruct (Hend l tbl t H Hi) as [Hinv' Hlen'] end.
sep_apply (Hbytes otp (Zlength tbl) tbl eq_refl).
assert (Hotp: otp <> nullval) by (intro; subst; destruct H1 as [Hp _]; contradiction).
forward_call (gv, tarray tuchar (8 * Zlength tbl)%Z, otp, shm, pm, am, h + 8 * (2 * Zlength tbl)).
{ destruct (eq_dec otp nullval); [contradiction|]. cancel. }
{ try split; intros; destruct am; simpl in *; auto; lia. }
skb. unabbr.
forward.
Exists 0 t.
destruct (eq_dec otp nullval); [contradiction|].
entailer!.
unfold hs_raw, hs_table. Exists q. rewrite H3, Hlen'. entailer!.
apply cm_have_eq. intros Hm. destruct am; [| contradiction]. simpl. lia.
Qed.

End CM_SetBodyExpandTail_1.
