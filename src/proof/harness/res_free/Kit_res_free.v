(* The pieces of res_free's harness proof (harness/res_free.c) that its main body and its streaming loop share:
   conversions between the harness's compspecs and the decoder's, the buffer witnesses, the harness's DDict lent to
   the calls that read it (ddict_hold, dd_lend), the functions main calls (G0) and what main has after its
   decoding step (dec_post). *)
Require Import VST.floyd.proofauto.
Require Export Zstd.proof.zstd.Spec_api6.
Require Export Zstd.proof.harness.res_free.Facts_res_free.
Require Export Zstd.proof.harness.res_free.Alloc_res_free.
Require Export Zstd.proof.harness.res_free.HOK_res_free.
Require Zstd.proof.top.MainPre6.
Require Zstd.proof.harness.HCsConv.
Require Zstd.proof.harness.frames.FSpecs Zstd.proof.harness.frames.FBodiesSmall Zstd.proof.harness.frames.FTransfer.

Local Ltac expand_main_pre ::= idtac.

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
    (QPprog_vars Zstd.contracts.res_free.whole_prog).
Proof.
  apply Forall_forall. intros [i v] Hin. apply make_tycontext_g_isSome.
  unfold Vprog, QPvarspecs. rewrite map_map.
  apply in_map_iff. exists (i, v). split; [reflexivity | exact Hin].
Qed.

(* main's precondition: the decoder's globals, split off as in MainPre6.main_pre_fact6 (whose list of
   programs has the x_ laws only) *)
Lemma pre_globals gv :
  InitGPred (Vardefs Zstd.contracts.res_free.whole_prog) gv |-- zstd_globals gv * TT.
Proof.
  assert (Hincl: incl Zstd.proof.top.MainPre6.zstd_vardefs (Vardefs Zstd.contracts.res_free.whole_prog)).
  { apply Zstd.proof.top.MainPre6.MP_incl_Vardefs; vm_compute; reflexivity. }
  rewrite (Zstd.proof.top.MainPre6.MP_split_zstd _ gv Hincl).
  apply sepcon_derives; [apply Zstd.proof.top.MainPre6.zstd_vardefs_globals | apply TT_right].
Qed.

(* ---------- byte arrays and tokens between the harness's compspecs and the decoder's ---------- *)

Lemma to_Z sh n v p :
  @data_at CompSpecs sh (tarray tuchar n) v p |-- @data_at Zstd.units.Zstd.CS sh (tarray tuchar n) v p.
Proof. rewrite (Zstd.proof.harness.HCsConv.data_at_bytes_cs CompSpecs Zstd.units.Zstd.CS). apply derives_refl. Qed.

Lemma to_Z_ sh n p :
  @data_at_ CompSpecs sh (tarray tuchar n) p |-- @data_at_ Zstd.units.Zstd.CS sh (tarray tuchar n) p.
Proof. rewrite (Zstd.proof.harness.HCsConv.data_at__bytes_cs CompSpecs Zstd.units.Zstd.CS). apply derives_refl. Qed.

Lemma of_Z_ sh n p :
  @data_at_ Zstd.units.Zstd.CS sh (tarray tuchar n) p |-- @data_at_ CompSpecs sh (tarray tuchar n) p.
Proof. rewrite (Zstd.proof.harness.HCsConv.data_at__bytes_cs CompSpecs Zstd.units.Zstd.CS). apply derives_refl. Qed.

Lemma of_Z sh n v p :
  @data_at Zstd.units.Zstd.CS sh (tarray tuchar n) v p |-- @data_at CompSpecs sh (tarray tuchar n) v p.
Proof. rewrite (Zstd.proof.harness.HCsConv.data_at_bytes_cs CompSpecs Zstd.units.Zstd.CS). apply derives_refl. Qed.

Lemma tok_to_Z sh n p :
  @malloc_token CompSpecs sh (tarray tuchar n) p |-- @malloc_token Zstd.units.Zstd.CS sh (tarray tuchar n) p.
Proof.
  rewrite (@malloc_token_change_composite _ _ (Zstd.proof.harness.HCsConv.cce_any CompSpecs Zstd.units.Zstd.CS)
    sh (tarray tuchar n)) by reflexivity.
  apply derives_refl.
Qed.

Lemma tok_of_Z sh n p :
  @malloc_token Zstd.units.Zstd.CS sh (tarray tuchar n) p |-- @malloc_token CompSpecs sh (tarray tuchar n) p.
Proof.
  rewrite (@malloc_token_change_composite _ _ (Zstd.proof.harness.HCsConv.cce_any CompSpecs Zstd.units.Zstd.CS)
    sh (tarray tuchar n)) by reflexivity.
  apply derives_refl.
Qed.

(* ---------- the buffer witnesses of a one-shot call: the malloc_tokens of its two buffers ---------- *)

Lemma pws_fold t1 p1 t2 p2 :
  (@malloc_token Zstd.units.Zstd.CS Ews t1 p1 * @malloc_token Zstd.units.Zstd.CS Ews t2 p2) |--
  pws_pred [pw_token Ews t1 p1; pw_token Ews t2 p2].
Proof. unfold pws_pred. simpl. rewrite sepcon_emp. apply derives_refl. Qed.

Lemma pws_unfold t1 p1 t2 p2 :
  pws_pred [pw_token Ews t1 p1; pw_token Ews t2 p2] |--
  (@malloc_token Zstd.units.Zstd.CS Ews t1 p1 * @malloc_token Zstd.units.Zstd.CS Ews t2 p2).
Proof. unfold pws_pred. simpl. rewrite sepcon_emp. apply derives_refl. Qed.

Lemma pws_in W w : In w W -> pws_pred W |-- pw_pred w * TT.
Proof.
  unfold pws_pred. induction W as [|a W IH]; simpl; [contradiction|]. intros [<-|Hin].
  - apply sepcon_derives; [apply derives_refl | apply TT_right].
  - eapply derives_trans; [apply sepcon_derives; [apply derives_refl | apply IH; exact Hin] |].
    rewrite <- sepcon_assoc, (sepcon_comm (pw_pred a)), sepcon_assoc.
    apply sepcon_derives; [apply derives_refl | apply TT_right].
Qed.

(* a malloc'ed buffer (also of 0 bytes) is weakly valid at both ends, given its token *)
Lemma buf_ok_tok W sh n p : In (pw_token Ews (tarray tuchar n) p) W -> readable_share sh -> 0 <= n -> isptr p ->
  buf_ok W sh n p.
Proof.
  intros Hin Hsh Hn Hp. unfold buf_ok.
  eapply derives_trans; [apply sepcon_derives; [apply (pws_in W _ Hin) | apply derives_refl] |].
  simpl pw_pred.
  destruct (zlt 0 n) as [Hpos|Hz].
  - rewrite (@data_at__memory_block Zstd.units.Zstd.CS). normalize.
    replace (sizeof (tarray tuchar n)) with n by (simpl; lia).
    apply andp_right; apply sepcon_weak_valid_pointer2.
    + rewrite <- (isptr_offset_val_zero p) at 2 by exact Hp.
      apply memory_block_weak_valid_pointer; [lia | lia | apply readable_nonidentity; exact Hsh].
    + apply memory_block_weak_valid_pointer; [lia | lia | apply readable_nonidentity; exact Hsh].
  - assert (n = 0) by lia. subst n. rewrite isptr_offset_val_zero by exact Hp.
    rewrite sepcon_assoc.
    assert (Hv: @malloc_token Zstd.units.Zstd.CS Ews (tarray tuchar 0) p |-- weak_valid_pointer p)
      by (eapply derives_trans; [apply malloc_token_valid_pointer; simpl; lia | apply valid_pointer_weak]).
    apply andp_right; apply sepcon_weak_valid_pointer1; exact Hv.
Qed.

Lemma isptr_of p : is_pointer_or_null p -> p <> nullval -> isptr p.
Proof. intros H1 H2. destruct p; simpl in *; auto. subst. contradiction. Qed.

Lemma ltu_Z x y : 0 <= x <= Int64.max_unsigned -> 0 <= y <= Int64.max_unsigned ->
  Int64.ltu (Int64.repr x) (Int64.repr y) = (x <? y).
Proof.
  intros. unfold Int64.ltu. rewrite !Int64.unsigned_repr by lia.
  destruct (zlt x y); symmetry; [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Qed.

Lemma vp_frame (P Q: mpred) p : ((P && valid_pointer p) * Q) |-- valid_pointer p.
Proof. apply sepcon_valid_pointer1. apply andp_left2. apply derives_refl. Qed.

Lemma drop_vp (P: mpred) p : (P && valid_pointer p) |-- P.
Proof. apply andp_left1. apply derives_refl. Qed.

Lemma free_pre {cs: compspecs} t p : isptr p ->
  (malloc_token Ews t p * data_at_ Ews t p) |-- (if eq_dec p nullval then emp else (malloc_token Ews t p * data_at_ Ews t p)).
Proof. intros. rewrite if_false by (intro; subst; contradiction). apply derives_refl. Qed.


(* the ZSTD_customMem main passes to ZSTD_createDCtx_advancedP, at the decoder's compspecs: the struct is the
   same in both (three pointers) *)
Lemma cmem_to_Z sh (a b c: val) p :
  @data_at CompSpecs sh (Tstruct ___gp_ZSTD_customMem noattr) (a, (b, c)) p |--
  @data_at Zstd.units.Zstd.CS sh (Tstruct ___gp_ZSTD_customMem noattr) (a, (b, c)) p.
Proof.
  pose proof (@data_at_change_composite CompSpecs Zstd.units.Zstd.CS
    (Zstd.proof.harness.HCsConv.cce_any CompSpecs Zstd.units.Zstd.CS) sh (Tstruct ___gp_ZSTD_customMem noattr)
    (a, (b, c)) (a, (b, c)) (JMeq_refl _) ltac:(vm_compute; reflexivity)) as E.
  rewrite E. apply derives_refl.
Qed.

Lemma cmem_of_Z sh (a b c: val) p :
  @data_at Zstd.units.Zstd.CS sh (Tstruct ___gp_ZSTD_customMem noattr) (a, (b, c)) p |--
  @data_at CompSpecs sh (Tstruct ___gp_ZSTD_customMem noattr) (a, (b, c)) p.
Proof.
  pose proof (@data_at_change_composite CompSpecs Zstd.units.Zstd.CS
    (Zstd.proof.harness.HCsConv.cce_any CompSpecs Zstd.units.Zstd.CS) sh (Tstruct ___gp_ZSTD_customMem noattr)
    (a, (b, c)) (a, (b, c)) (JMeq_refl _) ltac:(vm_compute; reflexivity)) as E.
  rewrite E. apply derives_refl.
Qed.

(* the stream's buffer structs, at the decoder's compspecs (the same three fields in both) *)
Lemma inb_to_Z sh (a b c: val) p :
  @data_at CompSpecs sh (Tstruct _ZSTD_inBuffer_s noattr) (a, (b, c)) p |--
  @data_at Zstd.units.Zstd.CS sh (Tstruct _ZSTD_inBuffer_s noattr) (a, (b, c)) p.
Proof.
  pose proof (@data_at_change_composite CompSpecs Zstd.units.Zstd.CS
    (Zstd.proof.harness.HCsConv.cce_any CompSpecs Zstd.units.Zstd.CS) sh (Tstruct _ZSTD_inBuffer_s noattr)
    (a, (b, c)) (a, (b, c)) (JMeq_refl _) ltac:(vm_compute; reflexivity)) as E.
  rewrite E. apply derives_refl.
Qed.

Lemma inb_of_Z sh (a b c: val) p :
  @data_at Zstd.units.Zstd.CS sh (Tstruct _ZSTD_inBuffer_s noattr) (a, (b, c)) p |--
  @data_at CompSpecs sh (Tstruct _ZSTD_inBuffer_s noattr) (a, (b, c)) p.
Proof.
  pose proof (@data_at_change_composite CompSpecs Zstd.units.Zstd.CS
    (Zstd.proof.harness.HCsConv.cce_any CompSpecs Zstd.units.Zstd.CS) sh (Tstruct _ZSTD_inBuffer_s noattr)
    (a, (b, c)) (a, (b, c)) (JMeq_refl _) ltac:(vm_compute; reflexivity)) as E.
  rewrite E. apply derives_refl.
Qed.

Lemma outb_to_Z sh (a b c: val) p :
  @data_at CompSpecs sh (Tstruct _ZSTD_outBuffer_s noattr) (a, (b, c)) p |--
  @data_at Zstd.units.Zstd.CS sh (Tstruct _ZSTD_outBuffer_s noattr) (a, (b, c)) p.
Proof.
  pose proof (@data_at_change_composite CompSpecs Zstd.units.Zstd.CS
    (Zstd.proof.harness.HCsConv.cce_any CompSpecs Zstd.units.Zstd.CS) sh (Tstruct _ZSTD_outBuffer_s noattr)
    (a, (b, c)) (a, (b, c)) (JMeq_refl _) ltac:(vm_compute; reflexivity)) as E.
  rewrite E. apply derives_refl.
Qed.

Lemma outb_of_Z sh (a b c: val) p :
  @data_at Zstd.units.Zstd.CS sh (Tstruct _ZSTD_outBuffer_s noattr) (a, (b, c)) p |--
  @data_at CompSpecs sh (Tstruct _ZSTD_outBuffer_s noattr) (a, (b, c)) p.
Proof.
  pose proof (@data_at_change_composite CompSpecs Zstd.units.Zstd.CS
    (Zstd.proof.harness.HCsConv.cce_any CompSpecs Zstd.units.Zstd.CS) sh (Tstruct _ZSTD_outBuffer_s noattr)
    (a, (b, c)) (a, (b, c)) (JMeq_refl _) ltac:(vm_compute; reflexivity)) as E.
  rewrite E. apply derives_refl.
Qed.

(* the allocator main gives the context: count_alloc, count_free, its counter now, the context's size as bound *)
Definition the_cm (gv: globals) (o: val) : cmem :=
  {| cm_alloc := gv _count_alloc; cm_free := gv _count_free; cm_opaque := o; cm_bound := dctx_size |}.

Lemma count_init_dctx o : data_at Tsh tulong (Vlong (Int64.repr 0)) o |-- @CM count_cm o dctx_size 0.
Proof. apply count_CM_init. rewrite dctx_size_eq. lia. Qed.

Lemma cm_funs_fold gv o :
  (func_ptr' cm_free_spec (gv _count_free) * func_ptr' cm_alloc_spec (gv _count_alloc)) |--
  @cm_funs count_cm (the_cm gv o).
Proof. unfold cm_funs; simpl. rewrite sepcon_comm. apply derives_refl. Qed.

(* a buffer that is a prefix of k bytes of a malloc'ed block of N bytes: its ends are weakly valid, given the
   block's token and the rest of the block (a witness lent for the call) *)
Lemma buf_ok_split W sh shr k N cr p :
  In (pw_token Ews (tarray tuchar N) p) W -> In (pw_bytes shr (N - k) cr (offset_val k p)) W ->
  readable_share sh -> readable_share shr -> 0 <= k <= N -> isptr p -> buf_ok W sh k p.
Proof.
  intros Ht Hb Hsh Hshr Hk Hp.
  destruct (Z.eq_dec k N) as [->|Hne]; [apply buf_ok_tok; auto; lia |].
  unfold buf_ok.
  assert (Hv: pws_pred W |-- valid_pointer (offset_val k p)).
  { eapply derives_trans; [apply (pws_in W _ Hb) |]. simpl pw_pred.
    apply sepcon_valid_pointer1. apply data_at_valid_ptr; [apply readable_nonidentity; auto | simpl; lia]. }
  apply andp_right.
  - destruct (zlt 0 k) as [Hpos|Hz].
    + apply sepcon_weak_valid_pointer2.
      rewrite (@data_at__memory_block Zstd.units.Zstd.CS). normalize.
      replace (sizeof (tarray tuchar k)) with k by (simpl; lia).
      rewrite <- (isptr_offset_val_zero p) at 2 by exact Hp.
      apply memory_block_weak_valid_pointer; [lia | lia | apply readable_nonidentity; exact Hsh].
    + assert (k = 0) by lia. subst k. rewrite isptr_offset_val_zero in Hv by exact Hp.
      apply sepcon_weak_valid_pointer1. apply valid_pointer_weak'. exact Hv.
  - apply sepcon_weak_valid_pointer1. apply valid_pointer_weak'. exact Hv.
Qed.

(* ---------- the harness's DDict, lent to the calls that read it ---------- *)

Section DDict.
Variable DD : globals -> val -> ddict_st -> mpred.

(* the token of the 0-byte copy a DDict made from 0 bytes refers to: a witness of its pointer *)
Definition dd_tok (q: val) (dd: ddict_st) : mpred :=
  if eq_dec q nullval then emp
  else match dd_ref dd with Some p => @malloc_token Zstd.units.Zstd.CS Ews (tarray tuchar 0) p | None => emp end.

Definition dd_wits (q: val) (dd: ddict_st) : list ptr_witness :=
  if eq_dec q nullval then nil
  else match dd_ref dd with Some p => pw_token Ews (tarray tuchar 0) p :: nil | None => nil end.

Lemma dd_wits_pred q dd : pws_pred (dd_wits q dd) = dd_tok q dd.
Proof.
  unfold dd_wits, dd_tok, pws_pred. destruct (eq_dec q nullval); [reflexivity |].
  destruct (dd_ref dd); simpl; [rewrite sepcon_emp |]; reflexivity.
Qed.

(* the DDict the harness holds (none while q is NULL) *)
Definition ddict_hold (gv: globals) (q: val) (dd: ddict_st) : mpred :=
  if eq_dec q nullval then emp else ddict_res DD gv Ews q dd.

(* whether a context in an rf_inv state reads the harness's DDict (its dictionary, or its set) *)
Definition dd_used (q: val) (st: dctx_st) : bool :=
  if eq_dec q nullval then false
  else match dc_set st with
       | nil => match dc_dict st with Some dr => match dr_src dr with DSDDict _ _ => true | _ => false end | None => false end
       | _ :: _ => true
       end.

Lemma dd_lend m gv q dd st : rf_inv m q dd st ->
  ddict_hold gv q dd |--
  dict_res DD gv Ews (dc_dict st) * set_res DD gv Ews (dc_set st) (dc_dict st) *
  (if dd_used q st then emp else ddict_hold gv q dd).
Proof.
  intros (_ & _ & _ & Hd & Hl & _). unfold ddict_hold, dd_used.
  destruct (eq_dec q nullval) as [Eq|Nq].
  - destruct Hd as [-> | [[b ->] | [Hn _]]]; [| | contradiction];
      (destruct Hl as [-> | [Hn _]]; [| contradiction]); unfold set_res; simpl; rewrite ?emp_sepcon, ?sepcon_emp; apply derives_refl.
  - destruct Hl as [-> | [_ ->]].
    + destruct Hd as [-> | [[b ->] | [_ ->]]]; unfold set_res; simpl; rewrite ?emp_sepcon, ?sepcon_emp; apply derives_refl.
    + unfold set_res, cur_ddict. destruct Hd as [-> | [[b ->] | [_ ->]]]; simpl.
      * rewrite emp_sepcon, !sepcon_emp. apply derives_refl.
      * rewrite emp_sepcon, !sepcon_emp. apply derives_refl.
      * destruct (Val.eq q q); [| contradiction]. rewrite !sepcon_emp. apply derives_refl.
Qed.

Lemma dd_unlend m gv q dd st : rf_inv m q dd st ->
  dict_res DD gv Ews (dc_dict st) * set_res DD gv Ews (dc_set st) (dc_dict st) *
  (if dd_used q st then emp else ddict_hold gv q dd) |-- ddict_hold gv q dd.
Proof.
  intros (_ & _ & _ & Hd & Hl & _). unfold ddict_hold, dd_used.
  destruct (eq_dec q nullval) as [Eq|Nq].
  - destruct Hd as [-> | [[b ->] | [Hn _]]]; [| | contradiction];
      (destruct Hl as [-> | [Hn _]]; [| contradiction]); unfold set_res; simpl; rewrite ?emp_sepcon, ?sepcon_emp; apply derives_refl.
  - destruct Hl as [-> | [_ ->]].
    + destruct Hd as [-> | [[b ->] | [_ ->]]]; unfold set_res; simpl; rewrite ?emp_sepcon, ?sepcon_emp; apply derives_refl.
    + unfold set_res, cur_ddict. destruct Hd as [-> | [[b ->] | [_ ->]]]; simpl.
      * rewrite emp_sepcon, !sepcon_emp. apply derives_refl.
      * rewrite emp_sepcon, !sepcon_emp. apply derives_refl.
      * destruct (Val.eq q q); [| contradiction]. rewrite !sepcon_emp. apply derives_refl.
Qed.

(* the call's witnesses contain the 0-byte copy's token: its pointer is valid *)
Lemma dd_wits_valid W q dd p : incl (dd_wits q dd) W -> q <> nullval -> dd_ref dd = Some p ->
  pws_pred W |-- valid_pointer p.
Proof.
  intros Hi Hq Hp.
  assert (Hin: In (pw_token Ews (tarray tuchar 0) p) W).
  { apply Hi. unfold dd_wits. rewrite if_false by exact Hq. rewrite Hp. left; reflexivity. }
  eapply derives_trans; [apply (pws_in W _ Hin) |]. simpl pw_pred.
  apply sepcon_valid_pointer1. apply malloc_token_valid_pointer. simpl. lia.
Qed.

(* a malloc'ed buffer of cap bytes, with its token among the witnesses, is valid at its start *)
Lemma buf_valid W sh cap p : In (pw_token Ews (tarray tuchar cap) p) W -> readable_share sh -> 0 <= cap ->
  sepcon (pws_pred W) (@data_at_ Zstd.proof.zstd.Base.CompSpecs sh (tarray tuchar cap) p) |-- valid_pointer p.
Proof.
  intros Hin Hsh Hc. destruct (zlt 0 cap) as [Hpos|Hz].
  - apply sepcon_valid_pointer2. apply data_at__valid_ptr; [apply readable_nonidentity; exact Hsh | simpl; lia].
  - assert (cap = 0) by lia. subst cap.
    apply sepcon_valid_pointer1.
    eapply derives_trans; [apply (pws_in W _ Hin) |]. simpl pw_pred.
    apply sepcon_valid_pointer1. apply malloc_token_valid_pointer. simpl. lia.
Qed.

(* ZSTD_decompressDCtx's conditions on the dictionaries' pointers *)
Lemma rf_dict_buf_ok m W sh shd q dd st cap p : rf_inv m q dd st ->
  incl (dd_wits q dd) W -> In (pw_token Ews (tarray tuchar cap) p) W -> readable_share shd -> 0 <= cap ->
  dict_buf_ok W sh (dc_dict st) shd cap p /\ Forall (fun e => ddict_buf_ok W sh (snd e) shd cap p) (dc_set st).
Proof.
  intros (_ & _ & _ & Hd & Hl & Hq) Hi Hin Hsh Hc.
  assert (Hdd: q <> nullval -> ddict_buf_ok W sh dd shd cap p).
  { intros Nq. unfold ddict_buf_ok. destruct (Hq Nq) as [-> | (p0 & Ep & Eb & Hp0)]; [exact Logic.I |].
    rewrite Ep. right. split; [rewrite Eb; reflexivity |]. split.
    - exact (dd_wits_valid W q dd p0 Hi Nq Ep).
    - exact (buf_valid W shd cap p Hin Hsh Hc). }
  split.
  - destruct Hd as [-> | [[b ->] | [Nq ->]]]; simpl; auto. exact (Hdd Nq).
  - destruct Hl as [-> | [Nq ->]]; constructor; [exact (Hdd Nq) | constructor].
Qed.

(* ZSTD_decompressStream's conditions on the dictionaries *)
Lemma rf_stream_dict_ok m W q dd st : rf_inv m q dd st -> incl (dd_wits q dd) W -> stream_dict_ok W st.
Proof.
  intros (_ & Hb & _ & Hd & Hl & Hq) Hi.
  assert (Hdd: q <> nullval -> sddict_ok W dd).
  { intros Nq. unfold sddict_ok. destruct (Hq Nq) as [-> | (p0 & Ep & Eb & Hp0)]; [exact Logic.I |].
    rewrite Ep. split; [exact Eb | exact (dd_wits_valid W q dd p0 Hi Nq Ep)]. }
  unfold stream_dict_ok. split; [| split; [| exact Hb]].
  - destruct Hd as [-> | [[b ->] | [Nq ->]]]; simpl; auto.
  - destruct Hl as [-> | [Nq ->]]; constructor; [exact (Hdd Nq) | constructor].
Qed.

(* a context in an rf_inv state for the harness without a DDict reads no DDict *)
Lemma dd_res_null m gv sh dd0 st : rf_inv m nullval dd0 st ->
  emp |-- dict_res DD gv sh (dc_dict st) * set_res DD gv sh (dc_set st) (dc_dict st).
Proof.
  intros (_ & _ & _ & Hd & Hl & _).
  destruct Hl as [-> | [Hn _]]; [| contradiction].
  destruct Hd as [-> | [[b ->] | [Hn _]]]; [| | contradiction]; unfold set_res; simpl; rewrite sepcon_emp; apply derives_refl.
Qed.

Lemma dd_res_null_e m gv sh dd0 st : rf_inv m nullval dd0 st ->
  dict_res DD gv sh (dc_dict st) * set_res DD gv sh (dc_set st) (dc_dict st) |-- emp.
Proof.
  intros (_ & _ & _ & Hd & Hl & _).
  destruct Hl as [-> | [Hn _]]; [| contradiction].
  destruct Hd as [-> | [[b ->] | [Hn _]]]; [| | contradiction]; unfold set_res; simpl; rewrite sepcon_emp; apply derives_refl.
Qed.

(* the witnesses of the caller's copy kept of the n bytes s, given to ZSTD_createDDict (none for NULL) *)
Definition kept_wits (kept: val) (s: list Z) : list ptr_witness :=
  if eq_dec kept nullval then nil else pw_token Ews (tarray tuchar (Zlength s)) kept :: nil.

(* what ZSTD_createDDict gives back is the harness's new DDict: the DDict, and the 0-byte copy it refers to with
   its token (a DDict by copy refers to nothing of the caller's) *)
Lemma dd_hold_new gv kept s q2 dd2 :
  is_pointer_or_null kept -> dd_bytes dd2 = s ->
  dd_ref dd2 = (if eq_dec kept nullval then None else if Zlength s =? 0 then Some kept else None) ->
  (if eq_dec q2 nullval then emp else (DD gv q2 dd2 && valid_pointer q2)) * bytes_at Ews s kept *
  pws_pred (kept_wits kept s) |-- ddict_hold gv q2 dd2 * dd_tok q2 dd2 * TT.
Proof.
  intros Hk Hb Hr. unfold ddict_hold, dd_tok, ddict_res, kept_wits, bytes_at, pws_pred.
  destruct (eq_dec q2 nullval); [cancel |].
  destruct (eq_dec kept nullval) as [Ek|Nk]; rewrite Hr.
  - cancel.
  - destruct (Zlength s =? 0) eqn:Ez.
    + apply Z.eqb_eq in Ez. rewrite Hb, Ez. simpl. cancel. apply sepcon_TT.
    + cancel.
Qed.

(* what ZSTD_freeDDict takes at the end: the DDict, or nothing for NULL *)
Lemma dd_hold_free gv q dd : ddict_hold gv q dd |--
  (match (if eq_dec q nullval then None else Some dd) with Some dd0 => DD gv q dd0 | None => emp end) * TT.
Proof.
  unfold ddict_hold, ddict_res. destruct (eq_dec q nullval); [cancel |].
  sep_apply (drop_vp (DD gv q dd) q). cancel.
Qed.

End DDict.

Section Shared.
Variable DC : globals -> val -> dctx_st -> mpred.
Variable DD : globals -> val -> ddict_st -> mpred.
Hypothesis DCM : @dc_cm_ok DC count_cm.

(* the counter now, taken out of a context of its own allocator: to give main's variable back at an early return
   (the context is then dropped) *)
Lemma dc_now_out gv d st m : dc_mem st = Some m ->
  DC gv d st |-- data_at_ Tsh tulong (cm_opaque m) * TT.
Proof.
  intros Hm. sep_apply (DCM gv d st m Hm). Intros h.
  simpl CM. unfold count_CM. Intros.
  sep_apply (data_at_data_at_ Tsh tulong). cancel.
Qed.

(* the functions main calls *)
Definition G0 : funspecs :=
  [(_quickproof_malloc, malloc_spec'); (_quickproof_free, free_spec');
   ZSTD_isError_spec; ZSTD_decompressDCtx_spec DC DD; ZSTD_decompressStream_spec DC DD;
   @ZSTD_createDCtx_advancedP_spec DC count_cm; @ZSTD_freeDCtx_spec DC count_cm; ZSTD_DCtx_reset_spec DC;
   ZSTD_DCtx_loadDictionary_spec DC; ZSTD_DCtx_setParameter_spec DC; ZSTD_createDDict_spec DD;
   ZSTD_DCtx_refDDict_spec DC DD; ZSTD_freeDDict_spec DD;
   nondet_u8_spec; nondet_u32_spec; gp_assert_spec;
   (_count_alloc, cm_alloc_spec); (_count_free, cm_free_spec);
   Zstd.proof.harness.frames.FSpecs.upto_spec; @Zstd.proof.harness.frames.FSpecs.any_bytes_spec CompSpecs;
   @Zstd.proof.harness.frames.FSpecs.copy_of_spec CompSpecs].

(* what main has after its decoding of the iteration (one-shot or streamed): the context in an rf_inv state, the
   output buffer with any cells, the input buffer unchanged, the two buffer structs with any contents *)
Definition dec_post (gv: globals) (v_now v_mem v_in v_out dctx: val) (m: cmem) (q: val) (dd: ddict_st) (s: list Z)
    (c: Z) (ps pd: val) : environ -> mpred :=
  (EX st1: dctx_st, EX oc: list val, EX vi: reptype (Tstruct _ZSTD_inBuffer_s noattr),
   EX vo: reptype (Tstruct _ZSTD_outBuffer_s noattr),
   PROP (rf_inv m q dd st1; rf_ok st1; Zlength oc = c)
   LOCAL (temp _dst pd; temp _src ps; temp _cap (Vlong (Int64.repr c)); temp _n (Vlong (Int64.repr (Zlength s)));
          temp _dctx dctx; temp _ddict q; lvar _out (Tstruct _ZSTD_outBuffer_s noattr) v_out;
          lvar _in (Tstruct _ZSTD_inBuffer_s noattr) v_in; lvar _mem (Tstruct ___gp_ZSTD_customMem noattr) v_mem;
          lvar _now tulong v_now; gvars gv)
   SEP (mem_mgr gv; malloc_token Ews (tarray tuchar c) pd; data_at Ews (tarray tuchar c) oc pd;
        malloc_token Ews (tarray tuchar (Zlength s)) ps; data_at Ews (tarray tuchar (Zlength s)) (zbytes s) ps;
        DC gv dctx st1; data_at Tsh (Tstruct ___gp_ZSTD_customMem noattr) (gv _count_alloc, (gv _count_free, v_now)) v_mem;
        data_at Tsh (Tstruct _ZSTD_outBuffer_s noattr) vo v_out; data_at Tsh (Tstruct _ZSTD_inBuffer_s noattr) vi v_in;
        ddict_hold DD gv q dd; dd_tok q dd; zstd_globals gv; TT))%assert.

(* main's streaming step: do { in.size += upto(n - in.size); out.size = out.pos + upto(cap - out.pos); }
   while (!ZSTD_isError(r = ZSTD_decompressStream(dctx, &out, &in)) && nondet_u8() != 0);
   if (ZSTD_isError(r)) ZSTD_DCtx_reset(dctx, ZSTD_reset_session_only);   (the Clight of f_main) *)
Definition stream_part : statement :=
(Ssequence
                                              (Sloop
                                                (Ssequence
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sset _t'31
                                                        (Efield
                                                          (Evar _in (Tstruct _ZSTD_inBuffer_s noattr))
                                                          _size tulong))
                                                      (Scall (Some _t'14)
                                                        (Evar _upto (Tfunction
                                                                    (tulong ::
                                                                    nil)
                                                                    tulong
                                                                    cc_default))
                                                        ((Ebinop Osub
                                                           (Etempvar _n tulong)
                                                           (Etempvar _t'31 tulong)
                                                           tulong) :: nil)))
                                                    (Ssequence
                                                      (Sset _t'30
                                                        (Efield
                                                          (Evar _in (Tstruct _ZSTD_inBuffer_s noattr))
                                                          _size tulong))
                                                      (Sassign
                                                        (Efield
                                                          (Evar _in (Tstruct _ZSTD_inBuffer_s noattr))
                                                          _size tulong)
                                                        (Ebinop Oadd
                                                          (Etempvar _t'30 tulong)
                                                          (Etempvar _t'14 tulong)
                                                          tulong))))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sset _t'29
                                                        (Efield
                                                          (Evar _out (Tstruct _ZSTD_outBuffer_s noattr))
                                                          _pos tulong))
                                                      (Scall (Some _t'15)
                                                        (Evar _upto (Tfunction
                                                                    (tulong ::
                                                                    nil)
                                                                    tulong
                                                                    cc_default))
                                                        ((Ebinop Osub
                                                           (Etempvar _cap tulong)
                                                           (Etempvar _t'29 tulong)
                                                           tulong) :: nil)))
                                                    (Ssequence
                                                      (Sset _t'28
                                                        (Efield
                                                          (Evar _out (Tstruct _ZSTD_outBuffer_s noattr))
                                                          _pos tulong))
                                                      (Sassign
                                                        (Efield
                                                          (Evar _out (Tstruct _ZSTD_outBuffer_s noattr))
                                                          _size tulong)
                                                        (Ebinop Oadd
                                                          (Etempvar _t'28 tulong)
                                                          (Etempvar _t'15 tulong)
                                                          tulong)))))
                                                (Ssequence
                                                  (Ssequence
                                                    (Ssequence
                                                      (Ssequence
                                                        (Ssequence
                                                          (Scall (Some _t'9)
                                                            (Evar _ZSTD_decompressStream 
                                                            (Tfunction
                                                              ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
                                                               (tptr (Tstruct _ZSTD_outBuffer_s noattr)) ::
                                                               (tptr (Tstruct _ZSTD_inBuffer_s noattr)) ::
                                                               nil) tulong
                                                              cc_default))
                                                            ((Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
                                                             (Eaddrof
                                                               (Evar _out (Tstruct _ZSTD_outBuffer_s noattr))
                                                               (tptr (Tstruct _ZSTD_outBuffer_s noattr))) ::
                                                             (Eaddrof
                                                               (Evar _in (Tstruct _ZSTD_inBuffer_s noattr))
                                                               (tptr (Tstruct _ZSTD_inBuffer_s noattr))) ::
                                                             nil))
                                                          (Sset _t'10
                                                            (Ecast
                                                              (Etempvar _t'9 tulong)
                                                              tulong)))
                                                        (Sset _r
                                                          (Etempvar _t'10 tulong)))
                                                      (Scall (Some _t'11)
                                                        (Evar _ZSTD_isError 
                                                        (Tfunction
                                                          (tulong :: nil)
                                                          tuint cc_default))
                                                        ((Etempvar _t'10 tulong) ::
                                                         nil)))
                                                    (Sifthenelse (Eunop Onotbool
                                                                   (Etempvar _t'11 tuint)
                                                                   tint)
                                                      (Ssequence
                                                        (Scall (Some _t'13)
                                                          (Evar _nondet_u8 
                                                          (Tfunction nil
                                                            tuchar
                                                            cc_default)) nil)
                                                        (Sset _t'12
                                                          (Ecast
                                                            (Ebinop Cop.One
                                                              (Etempvar _t'13 tuchar)
                                                              (Econst_int (Int.repr 0) tint)
                                                              tint) tbool)))
                                                      (Sset _t'12
                                                        (Econst_int (Int.repr 0) tint))))
                                                  (Sifthenelse (Etempvar _t'12 tint)
                                                    Sskip
                                                    Sbreak)))
                                              (Ssequence
                                                (Scall (Some _t'16)
                                                  (Evar _ZSTD_isError 
                                                  (Tfunction (tulong :: nil)
                                                    tuint cc_default))
                                                  ((Etempvar _r tulong) ::
                                                   nil))
                                                (Sifthenelse (Etempvar _t'16 tuint)
                                                  (Scall None
                                                    (Evar _ZSTD_DCtx_reset 
                                                    (Tfunction
                                                      ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
                                                       tint :: nil) tulong
                                                      cc_default))
                                                    ((Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
                                                     (Econst_int (Int.repr 1) tint) ::
                                                     nil))
                                                  Sskip))).

End Shared.
