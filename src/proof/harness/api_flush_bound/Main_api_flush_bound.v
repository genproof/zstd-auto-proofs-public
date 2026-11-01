(* The harness obligation of api_flush_bound (harness/api_flush_bound.c): for ANY predicates DC, DD of the
   decoder's API (Spec_api6), the helpers upto and any_bytes (laws_common.h, proved once in the frames kit) and
   main satisfy their specifications.

   main streams one input object src (n bytes) into one output object dst (cap bytes) through the same
   ZSTD_inBuffer / ZSTD_outBuffer: each call sees the prefix in.size of src and the prefix out.size of dst, so
   the two objects are split there for the call (the decoder's specification takes exactly in.size and
   out.size bytes) and joined again after it.  The buffer witnesses of the call (buf_ok) are the rest of each
   object and its malloc_token: an empty prefix is then still a valid pointer.
   The stream stays dictionary-less and in buffered mode (ZSTD_createDStream gives dctx_init; a call and
   ZSTD_DCtx_reset only change its streaming state), and it never carries an error into a call: a call that
   returns an error is followed by ZSTD_DCtx_reset(session_only).  The check is the clause of stream_post
   for a call with no input in buffered mode: opos' - opos <= ZSTD_BLOCKSIZE_MAX.  The buffers have any size
   up to PTRDIFF_MAX: this needs the streaming specification with sizes up to 2 ^ 63 - 1 (stage 1 of the size
   bounds of Spec_api6). *)
Require Import VST.floyd.proofauto.
Require Export Zstd.proof.zstd.Spec_api6.
Require Export Zstd.proof.harness.api_flush_bound.HOK_api_flush_bound.
Require Zstd.proof.top.MainPre6.
Require Zstd.proof.harness.HCsConv.
Require Zstd.proof.harness.frames.FSpecs Zstd.proof.harness.frames.FBodiesSmall Zstd.proof.harness.frames.FTransfer.

Local Ltac expand_main_pre ::= idtac.

Local Notation ZCS := Zstd.proof.zstd.Base.CompSpecs.
Local Notation HCS := Zstd.proof.harness.api_flush_bound.HOK_api_flush_bound.CompSpecs.
Local Notation tout := (Tstruct _ZSTD_outBuffer_s noattr).
Local Notation tin := (Tstruct _ZSTD_inBuffer_s noattr).

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
    (QPprog_vars Zstd.contracts.api_flush_bound.whole_prog).
Proof.
  apply Forall_forall. intros [i v] Hin. apply make_tycontext_g_isSome.
  unfold Vprog, QPvarspecs. rewrite map_map.
  apply in_map_iff. exists (i, v). split; [reflexivity | exact Hin].
Qed.

(* main's precondition: the decoder's globals, split off as in MainPre6.main_pre_fact6 (whose list of
   programs has the x_ laws only) *)
Lemma pre_globals gv :
  InitGPred (Vardefs Zstd.contracts.api_flush_bound.whole_prog) gv |-- zstd_globals gv * TT.
Proof.
  assert (Hincl: incl Zstd.proof.top.MainPre6.zstd_vardefs (Vardefs Zstd.contracts.api_flush_bound.whole_prog)).
  { apply Zstd.proof.top.MainPre6.MP_incl_Vardefs; vm_compute; reflexivity. }
  rewrite (Zstd.proof.top.MainPre6.MP_split_zstd _ gv Hincl).
  apply sepcon_derives; [apply Zstd.proof.top.MainPre6.zstd_vardefs_globals | apply TT_right].
Qed.

(* ---------- memory between the harness's compspecs and the decoder's ---------- *)

Lemma to_Z sh n v p :
  @data_at HCS sh (tarray tuchar n) v p |-- @data_at ZCS sh (tarray tuchar n) v p.
Proof. rewrite (Zstd.proof.harness.HCsConv.data_at_bytes_cs HCS ZCS). apply derives_refl. Qed.

Lemma to_Z_ sh n p :
  @data_at_ HCS sh (tarray tuchar n) p |-- @data_at_ ZCS sh (tarray tuchar n) p.
Proof. rewrite (Zstd.proof.harness.HCsConv.data_at__bytes_cs HCS ZCS). apply derives_refl. Qed.

Lemma tok_to_Z sh n p :
  @malloc_token HCS sh (tarray tuchar n) p |-- @malloc_token ZCS sh (tarray tuchar n) p.
Proof.
  rewrite (@malloc_token_change_composite _ _ (Zstd.proof.harness.HCsConv.cce_any HCS ZCS)
    sh (tarray tuchar n)) by reflexivity.
  apply derives_refl.
Qed.

Definition cce (cs1 cs2: compspecs) : change_composite_env cs1 cs2 :=
  {| coeq := cs_preserve_env cs1 cs2;
     coeq_consistent := cs_preserve_env_consistent cs1 cs2 _ eq_refl;
     coeq_complete := cs_preserve_completeness cs1 cs2 _ eq_refl |}.

Lemma out_Z: forall sh (a b c: val) p,
  @data_at ZCS sh t_outBuffer (a, (b, c)) p = @data_at HCS sh tout (a, (b, c)) p.
Proof.
  intros. pose proof (@data_at_change_composite ZCS HCS (cce ZCS HCS) sh tout (a, (b, c)) (a, (b, c))
    (JMeq_refl _) ltac:(vm_compute; reflexivity)) as E. exact (f_equal (fun f => f p) E).
Qed.

Lemma in_Z: forall sh (a b c: val) p,
  @data_at ZCS sh t_inBuffer (a, (b, c)) p = @data_at HCS sh tin (a, (b, c)) p.
Proof.
  intros. pose proof (@data_at_change_composite ZCS HCS (cce ZCS HCS) sh tin (a, (b, c)) (a, (b, c))
    (JMeq_refl _) ltac:(vm_compute; reflexivity)) as E. exact (f_equal (fun f => f p) E).
Qed.

(* ---------- a prefix of a byte object, and its buffer witnesses ---------- *)

(* the object of n cells at p as its first k cells and the rest *)
Lemma arr_split sh n k (v: list val) p : @field_compatible ZCS (tarray tuchar n) [] p -> 0 <= k <= n -> Zlength v = n ->
  @data_at ZCS sh (tarray tuchar n) v p =
  (@data_at ZCS sh (tarray tuchar k) (sublist 0 k v) p *
   @data_at ZCS sh (tarray tuchar (n - k)) (sublist k n v) (offset_val k p))%logic.
Proof.
  intros Hf Hk Hv. unfold tarray. rewrite (split2_data_at_Tarray_tuchar sh n k) by auto.
  change (Tarray tuchar n noattr) with (tarray tuchar n). rewrite arr_field_address0; [| exact Hf | lia].
  change (sizeof tuchar) with 1. rewrite Z.mul_1_l. reflexivity.
Qed.

Lemma arr_join sh n k (v1 v2: list val) p : @field_compatible ZCS (tarray tuchar n) [] p -> 0 <= k <= n ->
  Zlength v1 = k -> Zlength v2 = n - k ->
  (@data_at ZCS sh (tarray tuchar k) v1 p * @data_at ZCS sh (tarray tuchar (n - k)) v2 (offset_val k p))%logic |--
  @data_at ZCS sh (tarray tuchar n) (v1 ++ v2) p.
Proof.
  intros Hf Hk H1 H2. rewrite (arr_split sh n k (v1 ++ v2) p Hf Hk) by (rewrite Zlength_app; lia).
  rewrite sublist0_app1 by lia. rewrite sublist_same by lia.
  rewrite sublist_app2 by lia. rewrite sublist_same by lia. replace (k - Zlength v1) with 0 by lia.
  apply derives_refl.
Qed.

Lemma pws_in W w : In w W -> pws_pred W |-- pw_pred w * TT.
Proof.
  unfold pws_pred. induction W as [|a W IH]; simpl; [contradiction|]. intros [<-|Hin].
  - apply sepcon_derives; [apply derives_refl | apply TT_right].
  - eapply derives_trans; [apply sepcon_derives; [apply derives_refl | apply IH; exact Hin] |].
    rewrite <- sepcon_assoc, (sepcon_comm (pw_pred a)), sepcon_assoc.
    apply sepcon_derives; [apply derives_refl | apply TT_right].
Qed.

(* the first k bytes of a malloc'ed object of n bytes are weakly valid at both ends, given the rest of the
   object and its token (an empty prefix of an empty object: the token) *)
Lemma buf_ok_pre W sh n k c p :
  In (pw_bytes Ews (n - k) c (offset_val k p)) W -> In (pw_token Ews (tarray tuchar n) p) W ->
  0 <= k <= n -> isptr p -> readable_share sh -> buf_ok W sh k p.
Proof.
  intros Hb Ht Hk Hp Hsh. unfold buf_ok.
  destruct (zlt 0 k) as [Hpos|Hz].
  - rewrite (@data_at__memory_block ZCS). normalize.
    replace (sizeof (tarray tuchar k)) with k by (simpl; lia).
    apply andp_right; apply sepcon_weak_valid_pointer2.
    + rewrite <- (isptr_offset_val_zero p) at 2 by exact Hp.
      apply memory_block_weak_valid_pointer; [lia | lia | apply readable_nonidentity; exact Hsh].
    + apply memory_block_weak_valid_pointer; [lia | lia | apply readable_nonidentity; exact Hsh].
  - assert (k = 0) by lia. subst k. rewrite isptr_offset_val_zero by exact Hp.
    assert (Hv: pws_pred W |-- valid_pointer p).
    { destruct (zlt 0 n) as [Hn|Hn].
      - eapply derives_trans; [apply (pws_in W _ Hb) |]. simpl pw_pred.
        rewrite isptr_offset_val_zero by exact Hp.
        apply sepcon_valid_pointer1. apply data_at_valid_ptr; [apply readable_nonidentity; auto | simpl; lia].
      - eapply derives_trans; [apply (pws_in W _ Ht) |]. simpl pw_pred.
        apply sepcon_valid_pointer1. apply malloc_token_valid_pointer. simpl. lia. }
    apply andp_right; apply sepcon_weak_valid_pointer1;
      (eapply derives_trans; [exact Hv | apply valid_pointer_weak]).
Qed.

(* the witnesses of a call: the rest and the token of the input object, then of the output object *)
Definition wits (n isz: Z) (r: list val) (src: val) (cap osz: Z) (r': list val) (dst: val) : list ptr_witness :=
  [pw_bytes Ews (n - isz) r (offset_val isz src); pw_token Ews (tarray tuchar n) src;
   pw_bytes Ews (cap - osz) r' (offset_val osz dst); pw_token Ews (tarray tuchar cap) dst].

Lemma wits_fold n isz r src cap osz r' dst :
  (@data_at ZCS Ews (tarray tuchar (n - isz)) r (offset_val isz src) *
   @malloc_token ZCS Ews (tarray tuchar n) src *
   @data_at ZCS Ews (tarray tuchar (cap - osz)) r' (offset_val osz dst) *
   @malloc_token ZCS Ews (tarray tuchar cap) dst)%logic |--
  pws_pred (wits n isz r src cap osz r' dst).
Proof. unfold pws_pred, wits. simpl. rewrite sepcon_emp, !sepcon_assoc. apply derives_refl. Qed.

Lemma wits_unfold n isz r src cap osz r' dst :
  pws_pred (wits n isz r src cap osz r' dst) |--
  (@data_at ZCS Ews (tarray tuchar (n - isz)) r (offset_val isz src) *
   @malloc_token ZCS Ews (tarray tuchar n) src *
   @data_at ZCS Ews (tarray tuchar (cap - osz)) r' (offset_val osz dst) *
   @malloc_token ZCS Ews (tarray tuchar cap) dst)%logic.
Proof. unfold pws_pred, wits. simpl. rewrite sepcon_emp, !sepcon_assoc. apply derives_refl. Qed.

(* ---------- small facts ---------- *)

Lemma ltu_Z x y : 0 <= x <= Int64.max_unsigned -> 0 <= y <= Int64.max_unsigned ->
  Int64.ltu (Int64.repr x) (Int64.repr y) = (x <? y).
Proof.
  intros. unfold Int64.ltu. rewrite !Int64.unsigned_repr by lia.
  destruct (zlt x y); symmetry; [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Qed.

Lemma isptr_of p : is_pointer_or_null p -> p <> nullval -> isptr p.
Proof. intros H1 H2. destruct p; simpl in *; auto. subst. contradiction. Qed.

Lemma drop_vp (P: mpred) p : (P && valid_pointer p) |-- P.
Proof. apply andp_left1. apply derives_refl. Qed.

(* a stream without dictionary or DDict set: the dictionary resources of ZSTD_decompressStream are emp *)
Lemma DC_res (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred) gv ds st sh :
  dc_dict st = None -> dc_set st = nil ->
  DC gv ds st = (DC gv ds st * dict_res DD gv sh (dc_dict st) * set_res DD gv sh (dc_set st) (dc_dict st))%logic.
Proof. intros Hd Hs. rewrite Hd, Hs. unfold dict_res, set_res. simpl. rewrite !sepcon_emp. reflexivity. Qed.

Lemma stream_dict_ok_none W st : dc_dict st = None -> dc_set st = nil -> dc_bl st = None -> stream_dict_ok W st.
Proof. intros Hd Hs Hb. unfold stream_dict_ok. rewrite Hd, Hs, Hb. auto. Qed.

Lemma bytes_ok_sublist (l: list Z) i j : bytes_ok l -> bytes_ok (sublist i j l).
Proof. unfold bytes_ok. apply Forall_sublist. Qed.

Lemma repr1_neq0: Int.repr 1 <> Int.zero.
Proof. intro H; inv H. Qed.

(* the impossible branch of a test whose value is known *)
Ltac bad := first [contradiction | exfalso; eapply repr1_neq0; eassumption | discriminate |
  exfalso; match goal with H: ?x <> ?x |- _ => apply H; reflexivity end].

(* an entry of the witnesses of a call *)
Ltac in_wits := unfold wits; simpl; repeat first [left; reflexivity | right].

Section Main.
Variable DC : globals -> val -> dctx_st -> mpred.
Variable DD : globals -> val -> ddict_st -> mpred.

(* the functions main calls *)
Definition G0 : funspecs :=
  [(_quickproof_malloc, malloc_spec');
   ZSTD_isError_spec; ZSTD_createDStream_spec DC; ZSTD_freeDStream_spec DC;
   ZSTD_DCtx_reset_spec DC; ZSTD_decompressStream_spec DC DD;
   nondet_u8_spec; gp_assert_spec;
   Zstd.proof.harness.frames.FSpecs.upto_spec; @Zstd.proof.harness.frames.FSpecs.any_bytes_spec CompSpecs].

Lemma body_main_G0 : semax_body Vprog G0 f_main main_spec.
Proof.
  change (semax_body Vprog G0 f_main (_main, WITH gv: globals PRE [] VST.floyd.VSU.main_pre
    Zstd.contracts.api_flush_bound.whole_prog tt gv POST [tint] (fun _ : environ => TT))).
  replace (fun _ : environ => @TT mpred _) with (PROP () LOCAL () SEP (@TT mpred _))
    by (extensionality rho; unfold PROPx, LOCALx, SEPx; simpl; normalize).
  start_function1.
  eapply (main_pre_InitGpred (zstd_globals gv * TT)%logic).
  { intros _. apply pre_globals. }
  { reflexivity. }
  { apply vars_in_Vprog. }
  start_function3.
  sep_apply (create_mem_mgr gv).
  forward_call 9223372036854775807.
  Intros n.
  forward_call 9223372036854775807.
  Intros cap.
  forward_call (gv, n).
  Intros vret. destruct vret as [src l]. cbn [fst snd] in *.
  forward_call (tarray tuchar cap, gv).
  { simpl. rep_lia. }
  Intros dst.
  forward_call gv.
  Intros zds.
  unfold FSpecs.mbytes.
  (* src, dst or zds NULL: the run ends *)
  destruct (eq_dec src nullval) as [Hs|Hs].
  { subst src. repeat apply -> seq_assoc. apply semax_if_seq. forward_if; [| bad]. forward.
    apply semax_if_seq. forward_if; [| bad]. forward.
    forward_if; [forward; cancel | bad]. }
  Intros.
  destruct (eq_dec dst nullval) as [Hd|Hd].
  { subst dst. repeat apply -> seq_assoc. apply semax_if_seq. forward_if; [bad |]. forward.
    apply semax_if_seq. forward_if; [| bad]. forward.
    forward_if; [forward; cancel | bad]. }
  Intros.
  assert_PROP (isptr dst) as Hdp by entailer!.
  destruct dst as [| | | | | bd od]; try contradiction.
  destruct (eq_dec zds nullval) as [Hz|Hz].
  { subst zds. repeat apply -> seq_assoc. apply semax_if_seq. forward_if; [bad |]. forward.
    apply semax_if_seq. forward_if; [bad |]. forward.
    forward_if; [forward; cancel | bad]. }
  Intros.
  pose proof (isptr_of zds PNzds Hz) as Hzp.
  destruct zds as [| | | | | bz oz]; try contradiction.
  repeat apply -> seq_assoc. apply semax_if_seq. forward_if; [bad |]. forward.
  apply semax_if_seq. forward_if; [bad |]. forward.
  forward_if; [bad |].
  set (dst := Vptr bd od) in *. set (zds := Vptr bz oz) in *.
  sep_apply (drop_vp (DC gv zds dctx_init) zds).
  assert_PROP (isptr src) as Hsp by entailer!.
  forward. forward. forward. forward. forward.
  (* the two objects at the decoder's compspecs *)
  sep_apply (to_Z Ews n (zbytes l) src). sep_apply (tok_to_Z Ews n src).
  sep_apply (to_Z_ Ews cap dst). sep_apply (tok_to_Z Ews cap dst).
  rewrite (@data_at__eq ZCS).
  forward_loop
    (EX st: dctx_st, EX isz: Z, EX ipos: Z, EX opos: Z, EX osv: val, EX oc: list val,
     PROP (0 <= ipos <= isz; isz <= n; 0 <= opos <= cap; Zlength oc = cap;
           dc_dict st = None; dc_set st = nil; dc_bl st = None; dc_stable st = false; ss_err (dc_ss st) = false)
     LOCAL (temp _zds zds; temp _dst dst; temp _src src; temp _cap (Vlong (Int64.repr cap));
            temp _n (Vlong (Int64.repr n)); lvar _out tout v_out; lvar _in tin v_in; gvars gv)
     SEP (mem_mgr gv; zstd_globals gv; DC gv zds st;
          @data_at ZCS Ews (tarray tuchar n) (zbytes l) src; @malloc_token ZCS Ews (tarray tuchar n) src;
          @data_at ZCS Ews (tarray tuchar cap) oc dst; @malloc_token ZCS Ews (tarray tuchar cap) dst;
          data_at Tsh tin (src, (Vlong (Int64.repr isz), Vlong (Int64.repr ipos))) v_in;
          data_at Tsh tout (dst, (osv, Vlong (Int64.repr opos))) v_out; TT))%assert
    break:
    (EX st: dctx_st,
     PROP ()
     LOCAL (temp _zds zds; lvar _out tout v_out; lvar _in tin v_in; gvars gv)
     SEP (mem_mgr gv; zstd_globals gv; DC gv zds st; data_at_ Tsh tin v_in; data_at_ Tsh tout v_out; TT))%assert.
  { Exists dctx_init 0 0 0 (fst (snd (default_val tout))) (@default_val ZCS (tarray tuchar cap)). entailer!. }
  2: { Intros st. forward_call (gv, zds, Some st). forward. cancel. }
  Intros st isz ipos opos osv oc.
  (* in.size += upto(n - in.size); out.size = out.pos + upto(cap - out.pos) *)
  forward. forward_call (n - isz). Intros v. forward. forward.
  forward. forward_call (cap - opos). Intros w. forward. forward.
  forward. forward. forward. forward.
  rewrite !add64_repr.
  (* the call sees the first isz + v bytes of src and the first opos + w cells of dst *)
  assert_PROP (@field_compatible ZCS (tarray tuchar n) [] src) as Fs by entailer!.
  assert_PROP (@field_compatible ZCS (tarray tuchar cap) [] dst) as Fd by entailer!.
  rewrite (arr_split Ews n (isz + v) (zbytes l) src Fs) by (try rewrite Zlength_map; lia).
  rewrite (arr_split Ews cap (opos + w) oc dst Fd) by lia.
  rewrite !sublist_map.
  Intros.
  sep_apply (wits_fold n (isz + v) (zbytes (sublist (isz + v) n l)) src cap (opos + w) (sublist (opos + w) cap oc) dst).
  rewrite <- out_Z, <- in_Z.
  rewrite (DC_res DC DD gv zds st Ews) by auto.
  Intros.
  assert (Hsrc0: src <> nullval) by (intros ->; destruct Fs; contradiction).
  assert (Hdst0: dst <> nullval) by (intros ->; destruct Fd; contradiction).
  forward_call (wits n (isz + v) (zbytes (sublist (isz + v) n l)) src cap (opos + w) (sublist (opos + w) cap oc) dst,
    gv, zds, st, v_out, v_in, Tsh, Tsh, Ews, dst, opos + w, opos, sublist 0 (opos + w) oc, Ews, src, isz + v, ipos,
    sublist 0 (isz + v) l).
  { unfold mbuf; rewrite ?if_false by auto. cancel. }
  { split; [apply (buf_ok_pre _ Ews cap (opos + w) (sublist (opos + w) cap oc) dst);
            [in_wits | in_wits | lia | auto | apply writable_readable, writable_Ews] |].
    split; [apply (buf_ok_pre _ Ews n (isz + v) (zbytes (sublist (isz + v) n l)) src);
            [in_wits | in_wits | lia | auto | apply writable_readable, writable_Ews] |].
    split; [apply stream_dict_ok_none; auto |].
    split; [rewrite Zlength_sublist; lia |]. split; [rewrite Zlength_sublist; lia |].
    apply bytes_ok_sublist; auto. }
  Intros vret. destruct vret as [[[[r opos'] ipos'] oc'] st']. cbn [fst snd] in *.
  unfold mbuf; rewrite ?if_false by auto.
  match goal with H: stream_post _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    destruct H as (dl & stall' & a' & Hop & Hip & Hoc & Hpre & Hdl & Hbo & Ha' & Hah & Hor & Hr0 & Hst' & Hs1 & Hs2 &
                   Hbm & Hstall & Hcl) end.
  sep_apply (drop_vp (DC gv zds st') zds).
  rewrite H10, H11. change (dict_res DD gv Ews None) with emp. change (set_res DD gv Ews nil None) with emp.
  (* the two objects again *)
  sep_apply (wits_unfold n (isz + v) (zbytes (sublist (isz + v) n l)) src cap (opos + w) (sublist (opos + w) cap oc) dst).
  sep_apply (arr_join Ews cap (opos + w) oc' (sublist (opos + w) cap oc) dst Fd);
    try (rewrite ?Zlength_map; rewrite ?Zlength_sublist by lia; lia).
  sep_apply (arr_join Ews n (isz + v) (zbytes (sublist 0 (isz + v) l)) (zbytes (sublist (isz + v) n l)) src Fs);
    try (rewrite ?Zlength_map; rewrite ?Zlength_sublist by lia; lia).
  replace (zbytes (sublist 0 (isz + v) l) ++ zbytes (sublist (isz + v) n l)) with (zbytes l)
    by (rewrite <- map_app, <- sublist_split by lia; rewrite sublist_same by lia; reflexivity).
  rewrite out_Z, in_Z.
  (* the check: a call given no input wrote at most ZSTD_BLOCKSIZE_MAX bytes *)
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx L (SEPx R))) end.
  { forward. forward_call Int.one.
    { entailer!.
      match goal with H: Int.signed (Int.repr (Z.b2z (Int64.eq ?a ?b))) <> 0 |- _ =>
        destruct (Int64.eq a b) eqn:E; [| exfalso; apply H; reflexivity] end.
      apply Int64.same_if_eq in E. apply (f_equal Int64.unsigned) in E.
      rewrite !Int64.unsigned_repr in E by rep_lia.
      assert (Hb: opos' - opos <= ZSTD_BLOCKSIZE_MAX) by (apply Hbm; auto).
      unfold ZSTD_BLOCKSIZE_MAX in Hb. simpl in Hb.
      change (Int.signed (Int.shl (Int.repr 1) (Int.repr 17))) with 131072.
      rewrite ltu_Z by rep_lia.
      replace (131072 <? opos' - opos) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
    entailer!. }
  { forward. entailer!. }
  (* after an error, ZSTD_DCtx_reset(session_only): the stream never carries an error into a call *)
  forward_call r.
  subst st'.
  match goal with |- context [DC gv zds (set_last (set_ss st ?x) _)] => set (s2 := x) end.
  set (st2 := set_last (set_ss st s2) (Some stream_mark)).
  forward_if (EX st3: dctx_st,
     PROP (dc_dict st3 = None; dc_set st3 = nil; dc_bl st3 = None; dc_stable st3 = false; ss_err (dc_ss st3) = false)
     LOCAL (temp _zds zds; temp _dst dst; temp _src src; temp _cap (Vlong (Int64.repr cap));
            temp _n (Vlong (Int64.repr n)); lvar _out tout v_out; lvar _in tin v_in; gvars gv)
     SEP (mem_mgr gv; zstd_globals gv; DC gv zds st3;
          @data_at ZCS Ews (tarray tuchar n) (zbytes l) src; @malloc_token ZCS Ews (tarray tuchar n) src;
          @data_at ZCS Ews (tarray tuchar cap) (oc' ++ sublist (opos + w) cap oc) dst;
          @malloc_token ZCS Ews (tarray tuchar cap) dst;
          data_at Tsh tin (src, (Vlong (Int64.repr (isz + v)), Vlong (Int64.repr ipos'))) v_in;
          data_at Tsh tout (dst, (Vlong (Int64.repr (opos + w)), Vlong (Int64.repr opos'))) v_out; TT))%assert.
  { forward_call (gv, zds, st2, ZSTD_reset_session_only).
    Intros vret. destruct vret as [r0 st0]. cbn [fst snd] in *.
    match goal with H: reset_post _ _ _ _ |- _ => destruct (reset_post_session _ _ _ H) as [-> ->]; clear H end.
    Exists (set_ex (set_ss st2 ss_init) false). entailer!. }
  { destruct (is_error_code r) eqn:Er; [bad |].
    forward. Exists st2. entailer!. }
  Intros st3.
  (* do ... while (nondet_u8() != 0) *)
  forward_call tt. Intros u.
  forward_if.
  { forward. Exists st3 (isz + v) ipos' opos' (Vlong (Int64.repr (opos + w))) (oc' ++ sublist (opos + w) cap oc).
    entailer!. }
  { forward. Exists st3. entailer!. }
Qed.

End Main.

(* ---------- from G0 to Gprog (Specs_api DC DD) Hs ---------- *)

(* the harness's own functions besides main (in the order of helper_ids): the frames kit's any_bytes and upto
   (laws_common.h) *)
Definition Hs : funspecs :=
  [@Zstd.proof.harness.frames.FSpecs.any_bytes_spec CompSpecs; Zstd.proof.harness.frames.FSpecs.upto_spec].

Lemma Externals_eq : Externals = [nondet_u8_spec; nondet_size_spec; nondet_bytes_nn_spec; gp_assert_spec].
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

Lemma Gprog_cons DC DD : Gprog (Specs_api DC DD) Hs =
  (_quickproof_malloc, malloc_spec') :: (_quickproof_free, free_spec') ::
  (Specs_api DC DD ++ [nondet_u8_spec; nondet_size_spec; nondet_bytes_nn_spec; gp_assert_spec;
                       @Zstd.proof.harness.frames.FSpecs.any_bytes_spec CompSpecs;
                       Zstd.proof.harness.frames.FSpecs.upto_spec; main_spec]).
Proof. unfold Gprog, Imports. rewrite Externals_eq. reflexivity. Qed.

(* an entry (i, fs) of a list found in Gprog *)
Ltac in_gprog :=
  match goal with |- initial_world.find_id ?i _ = Some ?fs =>
    rewrite Gprog_cons; unfold Specs_api; cbn [app]; find_steps; reflexivity end.

Lemma G0_in_Gprog DC DD i fs : initial_world.find_id i (G0 DC DD) = Some fs ->
  initial_world.find_id i (Gprog (Specs_api DC DD) Hs) = Some fs.
Proof.
  intros Hi. apply initial_world.find_id_e in Hi. unfold G0 in Hi.
  rewrite Gprog_cons. unfold Specs_api. cbn [app].
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
Lemma Gprog_not_var DC DD i : In i (map fst (Gprog (Specs_api DC DD) Hs)) -> ~ In i (map fst Vprog).
Proof.
  intros Hin Hv.
  assert (Hb: forallb (fun j => negb (id_in_list j (map fst Vprog))) (map fst (Gprog (Specs_api DC DD) Hs)) = true).
  { match goal with |- forallb ?f ?l = true => let L := eval lazy in l in change l with L end.
    vm_compute. reflexivity. }
  rewrite forallb_forall in Hb. specialize (Hb i Hin).
  rewrite (Zstd.proof.top.MainPre6.MP_id_in_list_true_i i _ Hv) in Hb. discriminate.
Qed.

Theorem api_flush_bound_ok :
  forall (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred),
    exists Hs, HarnessOK (Specs_api DC DD) Hs.
Proof.
  intros DC DD. exists Hs. split.
  - vm_compute. reflexivity.
  - constructor; [| constructor; [| constructor; [| constructor]]].
    + (* any_bytes *)
      exists f_any_bytes. split; [vm_compute; reflexivity|]. split; [reflexivity|].
      assert (E: f_any_bytes = Zstd.proof.harness.frames.FSpecs.f_any_bytes) by (vm_compute; reflexivity).
      rewrite E. apply (Zstd.proof.harness.frames.FTransfer.fk_transfer Vprog _ (@Zstd.proof.harness.frames.FSpecs.G_any_bytes CompSpecs)).
      * exact (@Zstd.proof.harness.frames.FBodiesSmall.body_any_bytes CompSpecs).
      * apply Zstd.proof.harness.frames.FTransfer.fk_find_all. repeat constructor; in_gprog.
    + (* upto *)
      exists f_upto. split; [vm_compute; reflexivity|]. split; [reflexivity|].
      assert (E: f_upto = Zstd.proof.harness.frames.FSpecs.f_upto) by (vm_compute; reflexivity).
      rewrite E. apply (Zstd.proof.harness.frames.FTransfer.fk_transfer Vprog _ Zstd.proof.harness.frames.FSpecs.G_upto).
      * exact (@Zstd.proof.harness.frames.FBodiesSmall.body_upto CompSpecs).
      * apply Zstd.proof.harness.frames.FTransfer.fk_find_all. repeat constructor; in_gprog.
    + (* main *)
      exists f_main. split; [reflexivity|]. split; [reflexivity|].
      eapply semax_body_subsumption; [apply (body_main_G0 DC DD) |].
      apply tycontext_sub_i99. split; intro i.
      * (* both lists abstracted, so that the rewriting never compares them with the empty one by computation *)
        remember (G0 DC DD) as GG eqn:HGG. remember (Gprog (Specs_api DC DD) Hs) as GP eqn:HGP.
        rewrite (make_tycontext_g_find Vprog GG i), (make_tycontext_g_find Vprog GP i).
        subst GG GP.
        destruct (initial_world.find_id i (G0 DC DD)) as [fs|] eqn:E.
        -- rewrite (G0_in_Gprog DC DD i fs E). apply sub_option_refl.
        -- destruct (initial_world.find_id i (Gprog (Specs_api DC DD) Hs)) as [fs'|] eqn:E'.
           ++ rewrite mtg_none; [exact Logic.I |].
              apply (Gprog_not_var DC DD i).
              apply initial_world.find_id_e in E'. apply (in_map fst) in E'. exact E'.
           ++ apply sub_option_refl.
      * rewrite !semax_prog.find_id_maketycontext_s.
        destruct (initial_world.find_id i (G0 DC DD)) as [fs|] eqn:E; [|exact Logic.I].
        rewrite (G0_in_Gprog DC DD i fs E). exists fs. split; [reflexivity|]. apply funspec_sub_si_refl.
Qed.
