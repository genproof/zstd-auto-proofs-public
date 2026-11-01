(* FS3 set part, ZSTD_DDictHashSet_expand: shared helpers and the body of the re-emplace loop (one old slot). *)
Require Import Zstd.proof.dec.v3.FS.set.SetDefs.
Local Open Scope logic.

Section CM_SetBodyExpandLoop_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* for (;;break) {} (DEBUGLOG): a no-op (as BlkSeqDEC.dec_skipbreak_seq) *)
Lemma exp_skipbreak_seq : forall {Espec: OracleKind} {cs: compspecs} Delta (P: environ -> mpred) c R,
  semax Delta P c R -> semax Delta P (Ssequence (Sloop Sskip Sbreak) c) R.
Proof.
intros Espec cs Delta P c R H.
apply semax_seq with P; [|exact H].
apply semax_loop with P.
2: { eapply semax_pre; [|apply semax_break]. destruct R; unfold loop2_ret_assert, overridePost. cbv beta iota.
     apply andp_left2, derives_refl. }
eapply semax_post; [| | | | apply semax_skip].
all: destruct R; unfold normal_ret_assert, loop1_ret_assert, overridePost.
- intros rho; simpl; apply andp_left2, derives_refl.
- intros rho; simpl; apply andp_left2, FF_left.
- intros rho; simpl; apply andp_left2, FF_left.
- intros vl rho; simpl; apply andp_left2, FF_left.
Qed.

Lemma exp_test_eq_null (q: val) : isptr q -> weak_valid_pointer q |-- denote_tc_test_eq q (Vlong (Int64.repr 0)).
Proof. intros. destruct q; try contradiction. Transparent denote_tc_test_eq. unfold denote_tc_test_eq. simpl. entailer!. Opaque denote_tc_test_eq. Qed.

End CM_SetBodyExpandLoop_1.

Ltac reassoc := repeat match goal with
  |- semax _ _ (Ssequence (Ssequence _ _) _) _ => apply -> seq_assoc end.
Ltac unabbr := repeat match goal with M := @abbreviate statement _ |- _ => unfold M; clear M end;
  try match goal with |- semax _ _ (@abbreviate statement _) _ => unfold abbreviate end.
Ltac skb := unabbr; reassoc; apply exp_skipbreak_seq; abbreviate_semax.
(* do { if (0) ... } while (0) *)
Ltac if0 := unabbr; reassoc;
  match goal with |- semax _ ?P _ _ => forward_loop P break: P end;
  [ entailer!
  | match goal with |- semax _ ?P _ _ => forward_if P end;
    [ exfalso; match goal with H: Int.repr 0 <> Int.zero |- _ => apply H; reflexivity end
    | forward; try entailer!
    | forward; try entailer! ]
  | abbreviate_semax ].
Ltac skip_loop :=
  match goal with |- semax _ ?P _ _ => forward_loop P break: P end; try solve [entailer!]; try solve [forward; entailer!].

Section CM_SetBodyExpandLoop_2.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.

(* the body of `for (i = 0; i < oldTableSize; ++i)` *)
Definition exp_body : statement :=
  ltac:(let f := eval cbv delta [f_ZSTD_DDictHashSet_expand] in f_ZSTD_DDictHashSet_expand in
        lazymatch f with context [Sloop (Ssequence (Sifthenelse (Ebinop Olt (Etempvar _i _) _ _) Sskip Sbreak) ?B) _] =>
          exact B end).

Lemma exp_loop_step {Espec: OracleKind} : MF_ddid_wvp -> MF_ids_focus -> PF_member -> PF_inv0 -> PF_exp_step -> PF_exp_skip ->
  forall gv sp l tbl shm pm am hc otp q i t,
  hs_inv l tbl -> Zlength tbl <= 2 ^ 23 -> 0 <= i < Zlength tbl ->
  hs_inv0 (l_upto l tbl i) t -> Zlength t = (2 * Zlength tbl)%Z ->
  semax (func_tycontext f_ZSTD_DDictHashSet_expand Vprog G_expand nil)
   (PROP ()
    LOCAL (temp _i (Vlong (Int64.repr i)); temp _oldTableSize (Vlong (Int64.repr (Zlength tbl)));
           temp _oldTable otp; temp _newTable q; gvars gv; temp _hashSet sp; temp _customMem pm)
    SEP (blk_tok am (tarray tuchar (8 * (2 * Zlength tbl))) q;
         data_at Ews (tarray (tptr t_ddict) (2 * Zlength tbl)) t q; mem_mgr gv;
         data_at shm t_cmem (cmem_v am) pm; cm_have am hc; blk_tok am t_hset sp;
         data_at Ews t_hset (q, (Vlong (Int64.repr (2 * Zlength tbl)), Vlong (Int64.repr (Zlength (l_upto l tbl i))))) sp;
         blk_tok am (tarray tuchar (8 * Zlength tbl)) otp;
         data_at Ews (tarray (tptr t_ddict) (Zlength tbl)) tbl otp; set_ids l))
   exp_body
   (normal_ret_assert
    (EX t': list val,
     PROP (hs_inv0 (l_upto l tbl (i + 1)) t'; Zlength t' = (2 * Zlength tbl)%Z)
     LOCAL (temp _i (Vlong (Int64.repr i)); temp _oldTableSize (Vlong (Int64.repr (Zlength tbl)));
            temp _oldTable otp; temp _newTable q; gvars gv; temp _hashSet sp; temp _customMem pm)
     SEP (blk_tok am (tarray tuchar (8 * (2 * Zlength tbl))) q;
          data_at Ews (tarray (tptr t_ddict) (2 * Zlength tbl)) t' q; mem_mgr gv;
          data_at shm t_cmem (cmem_v am) pm; cm_have am hc; blk_tok am t_hset sp;
          data_at Ews t_hset (q, (Vlong (Int64.repr (2 * Zlength tbl)), Vlong (Int64.repr (Zlength (l_upto l tbl (i + 1)))))) sp;
          blk_tok am (tarray tuchar (8 * Zlength tbl)) otp;
          data_at Ews (tarray (tptr t_ddict) (Zlength tbl)) tbl otp; set_ids l))%argsassert).
Proof.
intros Hwvp Hfocus Hmem Hinv0 Hstep Hskip gv sp l tbl shm pm am hc otp q i t H H0 H2 H3 H4.
unfold exp_body. abbreviate_semax.
  assert (Hzi: Znth i tbl = nullval \/ isptr (Znth i tbl)).
  { pose proof H as H'. unfold hs_inv in H'. destruct H' as (_&_&_&_&_&_&_&Hf&_).
    rewrite Forall_Znth in Hf. apply Hf. lia. }
  assert (Hpn: is_pointer_or_null (Znth i tbl)).
  { destruct Hzi as [Hn | Hp]. rewrite Hn. reflexivity. destruct (Znth i tbl); try contradiction; simpl; auto. }
  forward.
  change (@Znth val Vundef i tbl) with (Znth i tbl).
  destruct (eq_dec (Znth i tbl) nullval) as [Hz | Hz].
  { forward_if.
    { rewrite Hz. entailer!. }
    { contradiction. }
    { forward. Exists t. rewrite (Hskip l tbl i ltac:(lia) Hz). entailer!. } }
  destruct Hzi as [Hzi|Hzi]; [contradiction|].
  destruct (Hstep l tbl i H ltac:(lia) Hz) as (Hse & Hin & Hincl & Hnin & Hlen & Hadd).
  assert (Hw: set_ids l |-- weak_valid_pointer (Znth i tbl)).
  { destruct (Hmem l tbl i (Hinv0 _ _ H) ltac:(lia) Hz) as [e [He Hfe]].
    destruct (Hfocus l e He) as [L1 [L2 [_ Hids]]].
    rewrite Hids, <- Hfe. apply sepcon_weak_valid_pointer1. apply Hwvp. }
  forward_if.
  { eapply derives_trans; [| apply exp_test_eq_null; auto].
    apply sepcon_weak_valid_pointer2. exact Hw. }
  2: { contradiction. }
  pose proof H as Hc. unfold hs_inv in Hc. destruct Hc as (_ & _ & Hlt & Hnd & _).
  match goal with |- semax _ ?P _ _ => forward_loop P end.
  { entailer!. }
  forward.
  rewrite <- H4.
  forward_call (sp, q, l, l_upto l tbl i, t, Znth i tbl, snd (set_entry l (Znth i tbl))).
  Intros t'. rewrite Hadd in *.
  forward.
  forward_call 0.
  forward_if.
  { exfalso. lia. }
  forward.
  Exists t'. rewrite H4. entailer!.
Qed.

End CM_SetBodyExpandLoop_2.
