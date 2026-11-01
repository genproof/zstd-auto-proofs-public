(* The body of stream_all (harness/frames.h) satisfies its specification (FStreamSpec.v).

   stream_all's locals in and out are structs (ZSTD_inBuffer, ZSTD_outBuffer): its body is proved at the
   compspecs of the harnesses that include frames.h (FSCS; their composites are the same two structs), and
   body_stream_all moves it to any compspecs that has those composites (cspecs_sub FSCS cs: a law's own
   compspecs), with the specification at that compspecs. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zstd.proof.harness.HCsConv.
Require Import Zstd.proof.harness.frames.FStreamSpec.
Require Import Zstd.proof.zstd.NullBuf.
Require Import Zstd.harness.api_split_invariant.code.
Local Open Scope logic.

#[local] Instance FSCS : compspecs. make_compspecs Zstd.harness.api_split_invariant.code.prog. Defined.

Local Notation ZCS := Zstd.proof.zstd.Base.CompSpecs.
Local Notation tin := (Tstruct _ZSTD_inBuffer_s noattr).
Local Notation tout := (Tstruct _ZSTD_outBuffer_s noattr).

Lemma sa_in_cs: forall sh (a b c: val) p,
  @data_at ZCS sh t_inBuffer (a, (b, c)) p = @data_at FSCS sh tin (a, (b, c)) p.
Proof.
  intros. pose proof (@data_at_change_composite ZCS FSCS (cce_any ZCS FSCS) sh tin (a, (b, c)) (a, (b, c))
    (JMeq_refl _) ltac:(vm_compute; reflexivity)) as E. exact (f_equal (fun f => f p) E).
Qed.

Lemma sa_out_cs: forall sh (a b c: val) p,
  @data_at ZCS sh t_outBuffer (a, (b, c)) p = @data_at FSCS sh tout (a, (b, c)) p.
Proof.
  intros. pose proof (@data_at_change_composite ZCS FSCS (cce_any ZCS FSCS) sh tout (a, (b, c)) (a, (b, c))
    (JMeq_refl _) ltac:(vm_compute; reflexivity)) as E. exact (f_equal (fun f => f p) E).
Qed.

(* a buffer of n > 0 bytes: its ends are weakly valid without any witness *)
Lemma sa_buf_ok_pos W sh n p : 0 < n -> sepalg.nonidentity sh -> buf_ok W sh n p.
Proof.
  intros Hn Hsh. unfold buf_ok. rewrite data_at__memory_block. rewrite sepcon_andp_prop.
  apply derives_extract_prop; intros FC.
  replace (sizeof (tarray tuchar n)) with n by (simpl; lia).
  assert (Hp: isptr p) by (destruct FC; auto).
  apply andp_right; apply sepcon_weak_valid_pointer2.
  - eapply derives_trans; [apply (memory_block_weak_valid_pointer sh n p 0); auto; try lia |].
    rewrite isptr_offset_val_zero by auto. apply derives_refl.
  - apply memory_block_weak_valid_pointer; auto; lia.
Qed.

(* a part of a buffer: of n > 0 bytes, or of 0 bytes when the whole has 0 bytes *)
Lemma sa_buf_ok_sub W sh n m p : buf_ok W sh n p -> sepalg.nonidentity sh -> 0 <= m -> (m = 0 -> n = 0) ->
  buf_ok W sh m p.
Proof.
  intros B Hsh Hm H0. destruct (Z.eq_dec m 0) as [E|E].
  - subst m. rewrite H0 in B by auto. exact B.
  - apply sa_buf_ok_pos; auto; lia.
Qed.

Lemma sa_split {cs: compspecs} sh n m (v: list val) p : 0 <= m <= n -> Zlength v = n ->
  data_at sh (tarray tuchar n) v p =
  data_at sh (tarray tuchar m) (sublist 0 m v) p *
  data_at sh (tarray tuchar (n - m)) (sublist m n v) (field_address0 (tarray tuchar n) [ArraySubsc m] p).
Proof. intros. apply split2_data_at_Tarray_tuchar; auto. Qed.

Lemma sa_join {cs: compspecs} sh n m (a b: list val) p : 0 <= m <= n -> Zlength a = m -> Zlength b = n - m ->
  data_at sh (tarray tuchar m) a p *
  data_at sh (tarray tuchar (n - m)) b (field_address0 (tarray tuchar n) [ArraySubsc m] p) =
  data_at sh (tarray tuchar n) (a ++ b) p.
Proof.
  intros Hm Ha Hb. rewrite (sa_split sh n m (a ++ b) p) by (auto; rewrite Zlength_app; lia).
  rewrite sublist_app1 by lia. rewrite sublist_same by lia.
  rewrite sublist_app2 by lia. rewrite sublist_same by lia. reflexivity.
Qed.

(* *completed += result == 0 *)
Lemma sa_count k r : 0 <= r <= Int64.max_unsigned ->
  Int64.add (Int64.repr k) (Int64.repr (Int.signed (Int.repr (Z.b2z
    (Int64.eq (Int64.repr r) (Int64.repr (Int.signed (Int.repr 0)))))))) =
  Int64.repr (k + (if r =? 0 then 1 else 0)).
Proof.
  intros Hr. change (Int.signed (Int.repr 0)) with 0.
  destruct (Z.eqb_spec r 0) as [->|Hne].
  - rewrite Int64.eq_true. simpl. rewrite add64_repr. reflexivity.
  - rewrite Int64.eq_false.
    + simpl. rewrite add64_repr. f_equal; lia.
    + intro E. apply Hne. apply (f_equal Int64.unsigned) in E.
      rewrite !Int64.unsigned_repr in E by rep_lia. exact E.
Qed.

(* the facts the loop keeps on its state x (e: whether the last call failed) *)
Definition sa_ok (st: dctx_st) (len cap: Z) (e: bool) (x: sa_state) : Prop :=
  0 <= sa_ipos x <= len /\ 0 <= sa_opos x <= cap /\ Zlength (sa_out x) = cap /\
  dc_stable (sa_st x) = false /\ ss_err (dc_ss (sa_st x)) = e /\
  dc_dict (sa_st x) = dc_dict st /\ dc_set (sa_st x) = dc_set st /\ dc_bl (sa_st x) = dc_bl st.

Lemma sa_ok_init st len cap oc :
  0 <= len -> 0 <= cap -> Zlength oc = cap -> dc_stable st = false -> ss_err (dc_ss st) = false ->
  sa_ok st len cap false (sa_init st oc).
Proof. intros. unfold sa_ok, sa_init; simpl. repeat split; auto; lia. Qed.

Lemma sa_ok_dict W st len cap e x : sa_ok st len cap e x -> stream_dict_ok W st -> stream_dict_ok W (sa_st x).
Proof.
  intros (_ & _ & _ & _ & _ & Hd & Hs & Hb) H. unfold stream_dict_ok in *. rewrite Hd, Hs, Hb. exact H.
Qed.

(* the state after a call *)
Definition sa_next (x: sa_state) (st': dctx_st) (ipos' opos': Z) (oc': list val) (osz cap r: Z) : sa_state :=
  {| sa_st := st'; sa_ipos := ipos'; sa_opos := opos'; sa_out := oc' ++ sublist osz cap (sa_out x);
     sa_done := sa_done x + (if r =? 0 then 1 else 0) |}.

Lemma sa_size_range pos n sz : 0 <= pos <= n -> sa_size pos n sz -> pos <= sz <= n /\ (sz = 0 -> n = 0).
Proof.
  unfold sa_size. intros H Hs. destruct (Z.eqb_spec pos n); lia.
Qed.

Lemma sa_ok_next st s cap dst x r st' ipos' opos' oc' isz osz :
  sa_ok st (Zlength s) cap false x -> sa_size (sa_ipos x) (Zlength s) isz -> sa_size (sa_opos x) cap osz ->
  stream_post (sa_st x) st' r dst osz (sa_opos x) opos' (sublist 0 osz (sa_out x)) oc'
    (sublist 0 isz s) isz (sa_ipos x) ipos' ->
  sa_ok st (Zlength s) cap (is_error_code r) (sa_next x st' ipos' opos' oc' osz cap r) /\ Zlength oc' = osz.
Proof.
  intros (Hi & Ho & Hl & Hst & He & Hd & Hs & Hb) Hisz Hosz Hp.
  apply sa_size_range in Hisz; [|lia]. apply sa_size_range in Hosz; [|lia].
  destruct Hp as (dl & stall' & a' & Hp). simpl in Hp.
  destruct Hp as (Ho' & Hi' & Hloc & _ & _ & _ & _ & _ & _ & _ & Est & _).
  subst st'. unfold sa_ok, sa_next; simpl.
  rewrite Zlength_app, Zlength_sublist by lia. repeat split; auto; lia.
Qed.

Definition sa_more_b (len: Z) (x: sa_state) (r: Z) (y: sa_state) : bool :=
  negb (is_error_code r) &&
  (if r =? 0 then sa_ipos y <? len else negb (sa_ipos y =? sa_ipos x) || negb (sa_opos y =? sa_opos x)).

Lemma sa_more_b_spec len x r y : stream_more len x r y <-> sa_more_b len x r y = true.
Proof.
  unfold stream_more, sa_more_b. destruct (is_error_code r); simpl; [split; [intros [H _]; discriminate | discriminate]|].
  destruct (r =? 0).
  - rewrite Z.ltb_lt. tauto.
  - rewrite orb_true_iff, !negb_true_iff, !Z.eqb_neq. tauto.
Qed.

Lemma sa_repr_inj a b : 0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int64.eq (Int64.repr a) (Int64.repr b) = true -> a = b.
Proof.
  intros Ha Hb E. apply Int64.same_if_eq in E.
  rewrite <- (Int64.unsigned_repr a), <- (Int64.unsigned_repr b) by auto. rewrite E; reflexivity.
Qed.

Lemma sa_repr_neq a b : Int64.eq (Int64.repr a) (Int64.repr b) = false -> a <> b.
Proof. intros E ->. rewrite Int64.eq_true in E. discriminate. Qed.

(* the size the loop chooses, in its two cases *)
Lemma sa_size_full n : sa_size n n n.
Proof. unfold sa_size. rewrite Z.eqb_refl. reflexivity. Qed.

Lemma sa_size_part pos n v : pos <> n -> 0 <= v <= n - pos - 1 -> sa_size pos n (pos + 1 + v).
Proof. intros. unfold sa_size. destruct (Z.eqb_spec pos n); [contradiction | lia]. Qed.

Section Body.
Variable DC : globals -> val -> dctx_st -> mpred.
Variable DD : globals -> val -> ddict_st -> mpred.

Lemma body_stream_all_FSCS : semax_body [] (G_stream_all DC DD) f_stream_all (@stream_all_spec FSCS DC DD).
Proof.
  start_function.
  forward. forward. forward. forward. forward.
  forward_loop
    (EX x: sa_state, EX isv: val, EX osv: val,
     PROP (stream_run s cap dst (sa_init st oc) x; sa_ok st (Zlength s) cap false x)
     LOCAL (lvar _out tout v_out; lvar _in tin v_in; gvars gv; temp _zds d; temp _src src;
            temp _len (Vlong (Int64.repr (Zlength s))); temp _dst dst; temp _cap (Vlong (Int64.repr cap));
            temp _written wp; temp _completed cp)
     SEP (data_at Tsh tout (dst, (osv, Vlong (Int64.repr (sa_opos x)))) v_out;
          data_at Tsh tin (src, (isv, Vlong (Int64.repr (sa_ipos x)))) v_in;
          pws_pred W; mem_mgr gv; zstd_globals gv; DC gv d (sa_st x);
          dict_res DD gv Ews (dc_dict st); set_res DD gv Ews (dc_set st) (dc_dict st);
          data_at shs (tarray tuchar (Zlength s)) (zbytes s) src;
          data_at shd (tarray tuchar cap) (sa_out x) dst; data_at_ shw tulong wp;
          data_at shc tulong (Vlong (Int64.repr (sa_done x))) cp))%assert
  continue:
    (EX x: sa_state, EX r: Z, EX y: sa_state, EX isv: val, EX osv: val,
     PROP (stream_run s cap dst (sa_init st oc) x; sa_ok st (Zlength s) cap false x; stream_call s cap dst x r y;
           sa_ok st (Zlength s) cap (is_error_code r) y)
     LOCAL (temp _result (Vlong (Int64.repr r)); temp _read (Vlong (Int64.repr (sa_ipos x)));
            temp _wrote (Vlong (Int64.repr (sa_opos x)));
            lvar _out tout v_out; lvar _in tin v_in; gvars gv; temp _zds d; temp _src src;
            temp _len (Vlong (Int64.repr (Zlength s))); temp _dst dst; temp _cap (Vlong (Int64.repr cap));
            temp _written wp; temp _completed cp)
     SEP (data_at Tsh tout (dst, (osv, Vlong (Int64.repr (sa_opos y)))) v_out;
          data_at Tsh tin (src, (isv, Vlong (Int64.repr (sa_ipos y)))) v_in;
          pws_pred W; mem_mgr gv; zstd_globals gv; DC gv d (sa_st y);
          dict_res DD gv Ews (dc_dict st); set_res DD gv Ews (dc_set st) (dc_dict st);
          data_at shs (tarray tuchar (Zlength s)) (zbytes s) src;
          data_at shd (tarray tuchar cap) (sa_out y) dst; data_at_ shw tulong wp;
          data_at shc tulong (Vlong (Int64.repr (sa_done y))) cp))%assert
  break:
    (EX x: sa_state, EX r: Z, EX y: sa_state, EX isv: val, EX osv: val,
     PROP (stream_run s cap dst (sa_init st oc) x; stream_call s cap dst x r y; ~ stream_more (Zlength s) x r y;
           0 <= sa_opos y <= cap)
     LOCAL (temp _result (Vlong (Int64.repr r));
            lvar _out tout v_out; lvar _in tin v_in; gvars gv; temp _zds d; temp _src src;
            temp _len (Vlong (Int64.repr (Zlength s))); temp _dst dst; temp _cap (Vlong (Int64.repr cap));
            temp _written wp; temp _completed cp)
     SEP (data_at Tsh tout (dst, (osv, Vlong (Int64.repr (sa_opos y)))) v_out;
          data_at Tsh tin (src, (isv, Vlong (Int64.repr (sa_ipos y)))) v_in;
          pws_pred W; mem_mgr gv; zstd_globals gv; DC gv d (sa_st y);
          dict_res DD gv Ews (dc_dict st); set_res DD gv Ews (dc_set st) (dc_dict st);
          data_at shs (tarray tuchar (Zlength s)) (zbytes s) src;
          data_at shd (tarray tuchar cap) (sa_out y) dst; data_at_ shw tulong wp;
          data_at shc tulong (Vlong (Int64.repr (sa_done y))) cp))%assert.
  - (* the loop's entry *)
    Exists (sa_init st oc) Vundef Vundef. entailer!.
    split; [constructor | apply sa_ok_init; auto; rep_lia].
    apply derives_refl.
  - (* one call *)
    Intros x isv osv.
    assert (Hx := H9). destruct H9 as (Hxi & Hxo & Hxl & Hxst & Hxe & Hxd & Hxs & Hxb).
    forward. forward. forward.
    match goal with |- semax _ (PROPx _ (LOCALx ?L (SEPx ?S))) _ _ =>
      forward_if (EX isz: Z, PROPx [sa_size (sa_ipos x) (Zlength s) isz]
                   (LOCALx (temp _t'3 (Vlong (Int64.repr isz)) :: L) (SEPx S)))%assert
    end.
    { forward. Exists (Zlength s). entailer!.
      apply sa_repr_inj in H9; [| rep_lia | rep_lia].
      rewrite H9. apply sa_size_full. }
    { assert (Hne: sa_ipos x <> (Zlength s)) by (intro E; apply H9; rewrite E; reflexivity).
      forward. forward_call ((Zlength s) - sa_ipos x - 1).
      Intros v. forward. forward. Exists (sa_ipos x + 1 + v). entailer!.
      apply sa_size_part; auto; lia. }
    Intros isz.
    assert (Hisz := sa_size_range _ _ _ Hxi H9).
    forward. forward.
    match goal with |- semax _ (PROPx _ (LOCALx ?L (SEPx ?S))) _ _ =>
      forward_if (EX osz: Z, PROPx [sa_size (sa_opos x) cap osz]
                   (LOCALx (temp _t'5 (Vlong (Int64.repr osz)) :: L) (SEPx S)))%assert
    end.
    { forward. Exists cap. entailer!.
      apply sa_repr_inj in H10; [| rep_lia | rep_lia].
      rewrite H10. apply sa_size_full. }
    { assert (Hne: sa_opos x <> cap) by (intro E; apply H10; rewrite E; reflexivity).
      forward. forward_call (cap - sa_opos x - 1).
      Intros v. forward. forward. Exists (sa_opos x + 1 + v). entailer!.
      apply sa_size_part; auto; lia. }
    Intros osz.
    assert (Hosz := sa_size_range _ _ _ Hxo H10).
    forward.
    (* the call: dst[0..osz-1] and src[0..isz-1], at the decoder's compspecs *)
    rewrite (sa_split shd cap osz (sa_out x) dst) by lia.
    rewrite (sa_split shs (Zlength s) isz (zbytes s) src) by (try rewrite Zlength_map; lia).
    rewrite (data_at_bytes_cs FSCS ZCS shd osz), (data_at_bytes_cs FSCS ZCS shs isz).
    rewrite <- sa_out_cs, <- sa_in_cs.
    rewrite <- Hxd, <- Hxs.
    rewrite sublist_map.
    (* both buffers are pointers: the decoder's buffers (mbuf, possibly NULL when empty) are their bytes *)
    assert_PROP (isptr dst /\ isptr src) as Pds.
    { entailer!. match goal with A: field_compatible (Tarray tuchar osz _) _ dst,
                                 B: field_compatible (Tarray tuchar isz _) _ src |- _ =>
        split; [apply (proj1 A) | apply (proj1 B)] end. }
    destruct Pds as [Pdst Psrc].
    forward_call (W, gv, d, sa_st x, v_out, v_in, Tsh, Tsh, shd, dst, osz, sa_opos x, sublist 0 osz (sa_out x),
                  shs, src, isz, sa_ipos x, sublist 0 isz s).
    { rewrite !mbuf_isptr by assumption. cancel. }
    { split; [|split; [|split; [|split; [|split]]]].
      - apply (sa_buf_ok_sub W shd cap); [auto | apply readable_nonidentity, writable_readable_share; auto | lia | lia].
      - apply (sa_buf_ok_sub W shs (Zlength s)); [auto | apply readable_nonidentity; auto | lia | lia].
      - eapply sa_ok_dict; eauto.
      - list_solve.
      - list_solve.
      - apply Forall_sublist; auto. }
    Intros vret. destruct vret as [[[[r opos'] ipos'] oc'] st']. simpl fst in *; simpl snd in *.
    rewrite !mbuf_isptr by assumption.
    forward. forward.
    destruct (sa_ok_next st s cap dst x r st' ipos' opos' oc' isz osz Hx H9 H10 H12) as [Hy Hoc'].
    assert (Hcall: stream_call s cap dst x r (sa_next x st' ipos' opos' oc' osz cap r)).
    { exists isz, osz, oc'. simpl. split; [|split; [|split; [|split; [|split; [|split]]]]]; auto. }
    Exists x r (sa_next x st' ipos' opos' oc' osz cap r) (Vlong (Int64.repr isz)) (Vlong (Int64.repr osz)).
    rewrite Hxd, Hxs.
    rewrite sa_out_cs, sa_in_cs, (data_at_bytes_cs ZCS FSCS shd osz), (data_at_bytes_cs ZCS FSCS shs isz).
    rewrite <- sublist_map.
    sep_apply (andp_left1 (DC gv d st') (valid_pointer d) (DC gv d st') (derives_refl _)).
    rewrite sa_count by auto.
    unfold sa_next; cbn [sa_st sa_ipos sa_opos sa_out sa_done].
    rewrite (sa_split shs (Zlength s) isz (zbytes s) src) by (try rewrite Zlength_map; lia).
    rewrite <- (sa_join shd cap osz oc' (sublist osz cap (sa_out x)) dst) by list_solve.
    entailer!.
  - (* the loop's test *)
    Intros x r y isv osv.
    assert (Hr: 0 <= r <= Int64.max_unsigned) by (destruct H10 as (? & ? & ? & ? & ? & Hr & _); exact Hr).
    forward_call r.
    match goal with |- semax _ (PROPx _ (LOCALx ?L (SEPx ?S))) _ _ =>
      forward_if (PROPx [] (LOCALx (temp _t'2 (Vint (Int.repr (if sa_more_b (Zlength s) x r y then 1 else 0))) :: L)
                   (SEPx S)))
    end.
    + assert (He: is_error_code r = false) by (destruct (is_error_code r); [apply (f_equal Int.unsigned) in H12;
        rewrite Int.unsigned_repr in H12 by rep_lia; discriminate | reflexivity]).
      pose proof H11 as (Hyi & Hyo & _). pose proof H9 as (Hxi & Hxo & _).
      forward_if.
      { match goal with Hz: Int64.repr r = Int64.zero |- _ =>
          apply (f_equal Int64.unsigned) in Hz; rewrite Int64.unsigned_repr in Hz by rep_lia end.
        subst r. change (Int64.unsigned Int64.zero) with 0 in *.
        forward. forward. forward. entailer!.
        unfold sa_more_b. rewrite He. simpl.
        destruct (zlt (sa_ipos y) (Zlength s));
          [rewrite (proj2 (Z.ltb_lt _ _)) by lia | rewrite (proj2 (Z.ltb_ge _ _)) by lia]; reflexivity. }
      assert (Hr0: r <> 0)
        by (intro E; subst r; match goal with Hz: Int64.repr 0 <> Int64.repr 0 |- _ => apply Hz; reflexivity end).
      forward. forward_if.
      { forward. forward. entailer!.
        assert (Hne: sa_ipos y <> sa_ipos x)
          by (intro E; match goal with Hz: Int64.repr (sa_ipos y) <> _ |- _ => apply Hz; rewrite E; reflexivity end).
        unfold sa_more_b. rewrite He, (proj2 (Z.eqb_neq r 0) Hr0), (proj2 (Z.eqb_neq _ _) Hne). reflexivity. }
      { forward. forward. forward. forward. entailer!.
        assert (Ei: sa_ipos y = sa_ipos x)
          by (match goal with Hz: Int64.eq _ _ = true |- _ => apply sa_repr_inj in Hz; [exact Hz | rep_lia | rep_lia] end).
        unfold sa_more_b. rewrite He, (proj2 (Z.eqb_neq r 0) Hr0), Ei, Z.eqb_refl. simpl.
        unfold Int64.cmpu. destruct (Z.eqb_spec (sa_opos y) (sa_opos x)) as [E|E].
        - rewrite E, Int64.eq_true. reflexivity.
        - rewrite Int64.eq_false; [reflexivity |].
          intro F. apply E. apply sa_repr_inj; [rep_lia | rep_lia | rewrite F; apply Int64.eq_true]. }
    + forward. entailer!. unfold sa_more_b. destruct (is_error_code r); [reflexivity | exfalso; apply H12; reflexivity].
    + forward_if.
      * forward. Exists y isv osv. entailer!.
        assert (Hm: sa_more_b (Zlength s) x r y = true)
          by (destruct (sa_more_b (Zlength s) x r y); [reflexivity | contradiction]).
        assert (He: is_error_code r = false)
          by (unfold sa_more_b in Hm; destruct (is_error_code r); [discriminate | reflexivity]).
        rewrite He in H11. split; [| exact H11].
        apply (stream_run_snoc s (Zlength oc) dst _ x r y); auto. apply sa_more_b_spec; auto.
      * forward. Exists x r y isv osv. entailer!.
        assert (Hm: sa_more_b (Zlength s) x r y = false).
        { destruct (sa_more_b (Zlength s) x r y); [|reflexivity].
          apply (f_equal Int.unsigned) in H12. rewrite Int.unsigned_repr in H12 by rep_lia. discriminate. }
        split; [rewrite sa_more_b_spec, Hm; discriminate | destruct H11 as (_ & Ho & _); exact Ho].
  - (* after the loop *)
    Intros x r y isv osv.
    forward. forward. forward.
    Exists r x y. entailer!.
Qed.

End Body.

Lemma sa_ulong_cs (cs1 cs2: compspecs) sh (v: val) p :
  @data_at cs1 sh tulong v p = @data_at cs2 sh tulong v p.
Proof.
  pose proof (@data_at_change_composite cs1 cs2 (cce_any cs1 cs2) sh tulong v v
    (JMeq_refl _) ltac:(reflexivity)) as E. rewrite E; reflexivity.
Qed.

Lemma sa_ulong__cs (cs1 cs2: compspecs) sh p :
  @data_at_ cs1 sh tulong p = @data_at_ cs2 sh tulong p.
Proof.
  pose proof (@data_at__change_composite cs1 cs2 (cce_any cs1 cs2) sh tulong ltac:(reflexivity)) as E.
  rewrite E; reflexivity.
Qed.

Lemma stream_all_spec_sub (cs1 cs2: compspecs) DC DD :
  funspec_sub (snd (@stream_all_spec cs1 DC DD)) (snd (@stream_all_spec cs2 DC DD)).
Proof.
  do_funspec_sub.
  destruct w as [[[[[[[[[[[[[[W gv] d] st] shs] src] s] shd] dst] cap] oc] shw] wp] shc] cp].
  Exists (W, gv, d, st, shs, src, s, shd, dst, cap, oc, shw, wp, shc, cp) (emp: mpred).
  cbv beta iota zeta.
  repeat rewrite (data_at_bytes_cs cs1 cs2). repeat rewrite (sa_ulong_cs cs1 cs2).
  repeat rewrite (sa_ulong__cs cs1 cs2).
  rewrite emp_sepcon. apply andp_right; [apply derives_refl |].
  apply prop_right. intros rho'. rewrite emp_sepcon. apply andp_left2.
  Intros r x y. Exists r x y.
  repeat rewrite (data_at_bytes_cs cs1 cs2). repeat rewrite (sa_ulong_cs cs1 cs2).
  entailer!.
Qed.

(* stream_all's body at a law's compspecs cs: any cs that has the two structs of the kit's (cspecs_sub FSCS cs,
   e.g. the compspecs of a harness that includes frames.h) *)
Lemma body_stream_all {cs: compspecs} (CSUB: cspecs_sub FSCS cs) DC DD :
  semax_body [] (G_stream_all DC DD) f_stream_all (@stream_all_spec cs DC DD).
Proof.
  apply (semax_body_funspec_sub (phi := snd (@stream_all_spec FSCS DC DD))).
  - apply (@semax_body_cenv_sub FSCS cs CSUB).
    + repeat constructor.
    + apply body_stream_all_FSCS.
  - apply stream_all_spec_sub.
  - repeat constructor; simpl; intuition discriminate.
Qed.

(* cspecs_sub FSCS cs for a harness's compspecs cs (its composites contain the kit's two structs) *)
Ltac fs_cspecs_sub := split3; intros ?i; apply sub_option_get; repeat constructor.
