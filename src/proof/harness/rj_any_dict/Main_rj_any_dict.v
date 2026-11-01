(* The harness obligation of rj_any_dict (harness/rj_any_dict.c): for ANY predicates DC, DD of the decoder's
   API, the helpers upto and any_bytes (laws_common.h, proved once in the frames kit) and main satisfy their
   specifications.

   main's loop keeps one context with no session, no buffer-less stage and no DDict set (dc_ss = ss_init,
   dc_bl = None, dc_set = nil): ZSTD_decompress_usingDict changes at most the context's last dictionary
   (after_decode, set_last).  Each call's check is the first conjunct of oneshot_ok: a result that is not an
   error code is at most the capacity.  The dictionary and the output are one object [dict | gap | dst] of any
   size up to PTRDIFF_MAX: this needs ZSTD_decompress_usingDict with dictionaries of any length before dst
   (Spec_api6): its dict_ptr_ok_any allows [dict | gap | dst].

   The buffer witnesses of a call: the malloc_tokens of src and of the block, and the block itself at a
   nonempty retainer share shx (Ews = shw + shx, the data at the writable shw).  Every length may be 0 (with
   dict_len = gap = 0 the dictionary pointer is dst), so the weak validity of each pointer into the block
   comes from the block at shx (or, for a block of 0 bytes, its token). *)
Require Import VST.floyd.proofauto.
Require Export Zstd.proof.zstd.Spec_api6.
Require Export Zstd.proof.harness.rj_any_dict.HOK_rj_any_dict.
Require Zstd.proof.top.MainPre6.
Require Zstd.proof.harness.HCsConv.
Require Zstd.proof.harness.frames.FSpecs Zstd.proof.harness.frames.FBodiesSmall Zstd.proof.harness.frames.FTransfer.
Require Import Zstd.proof.harness.ApiAfterKit.

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
    (QPprog_vars Zstd.contracts.rj_any_dict.whole_prog).
Proof.
  apply Forall_forall. intros [i v] Hin. apply make_tycontext_g_isSome.
  unfold Vprog, QPvarspecs. rewrite map_map.
  apply in_map_iff. exists (i, v). split; [reflexivity | exact Hin].
Qed.

(* main's precondition: the decoder's globals, split off as in MainPre6.main_pre_fact6 (whose list of
   programs has the x_ laws only) *)
Lemma pre_globals gv :
  InitGPred (Vardefs Zstd.contracts.rj_any_dict.whole_prog) gv |-- zstd_globals gv * TT.
Proof.
  assert (Hincl: incl Zstd.proof.top.MainPre6.zstd_vardefs (Vardefs Zstd.contracts.rj_any_dict.whole_prog)).
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

(* ---------- buffer witnesses ---------- *)

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

Lemma ltu_Z x y : 0 <= x <= Int64.max_unsigned -> 0 <= y <= Int64.max_unsigned ->
  Int64.ltu (Int64.repr x) (Int64.repr y) = (x <? y).
Proof.
  intros. unfold Int64.ltu. rewrite !Int64.unsigned_repr by lia.
  destruct (zlt x y); symmetry; [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Qed.

Lemma drop_vp (P: mpred) p : (P && valid_pointer p) |-- P.
Proof. apply andp_left1. apply derives_refl. Qed.

Lemma free_pre {cs: compspecs} t p : isptr p ->
  (malloc_token Ews t p * data_at_ Ews t p) |-- (if eq_dec p nullval then emp else (malloc_token Ews t p * data_at_ Ews t p)).
Proof. intros. rewrite if_false by (intro; subst; contradiction). apply derives_refl. Qed.

(* ---------- the block [dict | gap | dst] at two shares ---------- *)

(* Ews = shw + shx: shw is writable (the harness's accesses and the decoder's), shx is a nonempty retainer
   share kept as the buffer witness of the whole block (weak validity of every pointer into it) *)
Definition shx : share := snd (Share.split extern_retainer).
Definition shw : share := Share.lub (fst (Share.split extern_retainer)) Share.Rsh.

Lemma er_parts : Share.lub (fst (Share.split extern_retainer)) shx = extern_retainer /\
  Share.glb (fst (Share.split extern_retainer)) shx = Share.bot.
Proof.
  unfold shx. destruct (Share.split extern_retainer) as [a b] eqn:E. simpl. split.
  - exact (Share.split_together _ _ _ E).
  - exact (Share.split_disjoint _ _ _ E).
Qed.

Lemma er_sub_Lsh : Share.glb extern_retainer Share.Lsh = extern_retainer.
Proof.
  unfold extern_retainer. destruct (Share.split Share.Lsh) as [a b] eqn:E. simpl.
  pose proof (Share.split_together _ _ _ E) as H. rewrite <- H.
  apply Share.glb_absorb.
Qed.

Lemma sub_er_Rsh s : Share.glb s extern_retainer = s -> Share.glb s Share.Rsh = Share.bot.
Proof.
  intros H. rewrite <- H, <- er_sub_Lsh, <- !Share.glb_assoc.
  rewrite (Share.glb_assoc _ Share.Lsh), glb_Lsh_Rsh, !Share.glb_bot. reflexivity.
Qed.

Lemma x_sub_er : Share.glb (fst (Share.split extern_retainer)) extern_retainer = fst (Share.split extern_retainer).
Proof.
  destruct er_parts as [H _]. set (x := fst (Share.split extern_retainer)) in *. clearbody x.
  rewrite <- H. apply Share.glb_absorb.
Qed.

Lemma y_sub_er : Share.glb shx extern_retainer = shx.
Proof.
  destruct er_parts as [H _]. set (x := fst (Share.split extern_retainer)) in *. clearbody x.
  rewrite <- H, Share.lub_commute. apply Share.glb_absorb.
Qed.

Lemma er_parts_nonbot : fst (Share.split extern_retainer) <> Share.bot /\ shx <> Share.bot.
Proof.
  unfold shx. destruct (Share.split extern_retainer) as [a b] eqn:E. simpl.
  pose proof (Share.split_nontrivial _ _ _ E) as Hn.
  split; intro Hb; apply nonidentity_extern_retainer; rewrite Hn by auto; apply bot_identity.
Qed.

Lemma shares_join : sepalg.join shw shx Ews.
Proof.
  destruct er_parts as [Hl Hg]. split.
  - unfold shw. rewrite Share.glb_commute, Share.distrib1, Share.glb_commute, Hg.
    rewrite (sub_er_Rsh _ y_sub_er). apply Share.lub_bot.
  - unfold shw, Ews. rewrite Share.lub_assoc, (Share.lub_commute Share.Rsh), <- Share.lub_assoc, Hl.
    reflexivity.
Qed.

Lemma shw_writable : writable_share shw.
Proof.
  split.
  - unfold shw. rewrite Share.distrib1, glb_Lsh_Rsh, Share.lub_bot.
    pose proof (proj1 er_parts_nonbot) as Hb. pose proof x_sub_er as Hx.
    set (x := fst (Share.split extern_retainer)) in *. clearbody x.
    rewrite Share.glb_commute, <- Hx, Share.glb_assoc, er_sub_Lsh, Hx.
    intro Hi. apply identity_share_bot in Hi. exact (Hb Hi).
  - exists (fst (Share.split extern_retainer)). split.
    + rewrite Share.glb_commute. apply sub_er_Rsh, x_sub_er.
    + unfold shw. apply Share.lub_commute.
Qed.

Lemma shx_nonidentity : sepalg.nonidentity shx.
Proof. intro Hi. apply identity_share_bot in Hi. exact (proj2 er_parts_nonbot Hi). Qed.

(* the three pieces of the block: dictionary, gap and output *)
Lemma split3_bytes {cs: compspecs} sh a g c (v: list val) p :
  0 <= a -> 0 <= g -> 0 <= c -> Zlength v = a + g + c -> field_compatible (tarray tuchar (a + g + c)) [] p ->
  data_at sh (tarray tuchar (a + g + c)) v p =
  (data_at sh (tarray tuchar a) (sublist 0 a v) p * data_at sh (tarray tuchar g) (sublist a (a + g) v) (offset_val a p) *
   data_at sh (tarray tuchar c) (sublist (a + g) (a + g + c) v) (offset_val (a + g) p))%logic.
Proof.
  intros Ha Hg Hc Hv Hf.
  pose proof (split3_data_at_Tarray_tuchar sh (a + g + c) a (a + g) v p) as E.
  unfold tarray in *. rewrite E by lia. clear E.
  change (Tarray tuchar (a + g + c) noattr) with (tarray tuchar (a + g + c)) in *.
  rewrite !arr_field_address0 by (auto; lia).
  replace (a + g - a) with g by lia. replace (a + g + c - (a + g)) with c by lia.
  change (sizeof tuchar) with 1. rewrite !Z.mul_1_l. reflexivity.
Qed.

Lemma join3_bytes {cs: compspecs} sh a g c p :
  0 <= a -> 0 <= g -> 0 <= c -> field_compatible (tarray tuchar (a + g + c)) [] p ->
  data_at_ sh (tarray tuchar a) p * data_at_ sh (tarray tuchar g) (offset_val a p) *
  data_at_ sh (tarray tuchar c) (offset_val (a + g) p) |-- data_at_ sh (tarray tuchar (a + g + c)) p.
Proof.
  intros Ha Hg Hc Hf. rewrite !data_at__eq.
  rewrite (split3_bytes sh a g c (default_val (tarray tuchar (a + g + c))) p); auto;
    [| unfold default_val; simpl; rewrite Zlength_Zrepeat; lia].
  unfold default_val; simpl. rewrite !sublist_Zrepeat by lia.
  replace (a - 0) with a by lia. replace (a + g - a) with g by lia. replace (a + g + c - (a + g)) with c by lia.
  apply derives_refl.
Qed.

(* the witnesses of one call: the tokens of src and of the block, and the block at shx *)
Definition W3 (n: Z) (ps: val) (L: Z) (pb: val) (l: list val) : list ptr_witness :=
  [pw_token Ews (tarray tuchar n) ps; pw_token Ews (tarray tuchar L) pb; pw_bytes shx L l pb].

Lemma pws_fold3 n ps L pb l :
  (@malloc_token Zstd.units.Zstd.CS Ews (tarray tuchar n) ps * @malloc_token Zstd.units.Zstd.CS Ews (tarray tuchar L) pb *
   @data_at Zstd.units.Zstd.CS shx (tarray tuchar L) l pb) |-- pws_pred (W3 n ps L pb l).
Proof. unfold pws_pred, W3. simpl. rewrite sepcon_emp, sepcon_assoc. apply derives_refl. Qed.

Lemma pws_unfold3 n ps L pb l :
  pws_pred (W3 n ps L pb l) |--
  (@malloc_token Zstd.units.Zstd.CS Ews (tarray tuchar n) ps * @malloc_token Zstd.units.Zstd.CS Ews (tarray tuchar L) pb *
   @data_at Zstd.units.Zstd.CS shx (tarray tuchar L) l pb).
Proof. unfold pws_pred, W3. simpl. rewrite sepcon_emp, sepcon_assoc. apply derives_refl. Qed.

(* every pointer into the block (both ends included) is weakly valid, given the witnesses *)
Lemma W3_wvp n ps L pb l k : 0 <= k <= L -> isptr pb ->
  pws_pred (W3 n ps L pb l) |-- weak_valid_pointer (offset_val k pb).
Proof.
  intros Hk Hp. destruct (zlt 0 L) as [HL|HL].
  - eapply derives_trans; [apply (pws_in _ (pw_bytes shx L l pb)); unfold W3; simpl; tauto |].
    apply sepcon_weak_valid_pointer1. simpl pw_pred.
    eapply derives_trans; [apply data_at_memory_block |].
    replace (sizeof (tarray tuchar L)) with L by (simpl; lia).
    apply memory_block_weak_valid_pointer; [lia | lia | apply shx_nonidentity].
  - assert (k = 0) by lia. subst k. rewrite isptr_offset_val_zero by exact Hp.
    eapply derives_trans; [apply (pws_in _ (pw_token Ews (tarray tuchar L) pb)); unfold W3; simpl; tauto |].
    apply sepcon_weak_valid_pointer1. simpl pw_pred.
    eapply derives_trans; [apply malloc_token_valid_pointer; simpl; lia | apply valid_pointer_weak].
Qed.

Lemma buf_ok_blk n ps L pb l sh k m : 0 <= k -> 0 <= m -> k + m <= L -> isptr pb ->
  buf_ok (W3 n ps L pb l) sh m (offset_val k pb).
Proof.
  intros. unfold buf_ok. rewrite offset_offset_val.
  apply andp_right; apply sepcon_weak_valid_pointer1; apply W3_wvp; auto; lia.
Qed.

Lemma buf_ok_blk0 n ps L pb l sh m : 0 <= m -> m <= L -> isptr pb -> buf_ok (W3 n ps L pb l) sh m pb.
Proof.
  intros. pose proof (buf_ok_blk n ps L pb l sh 0 m) as Hk.
  rewrite isptr_offset_val_zero in Hk by assumption. apply Hk; auto; lia.
Qed.

Lemma buf_ok_src n ps L pb l sh : readable_share sh -> 0 <= n -> isptr ps ->
  buf_ok (W3 n ps L pb l) sh n ps.
Proof. intros. apply buf_ok_tok; auto. unfold W3; simpl; tauto. Qed.

(* the dictionary lies before dst in the block [dict | gap | dst] of at most PTRDIFF_MAX bytes, dictionary and
   dst at the same share: the caller's side of dict_ptr_ok_any for ZSTD_decompress_usingDict *)
Lemma dict_ok_blk {cs: compspecs} W sh a g c pb :
  isptr pb -> 0 <= a -> 0 <= g -> 0 <= c -> a + g + c <= 2 ^ 63 - 1 ->
  field_compatible (tarray tuchar (a + g + c)) [] pb ->
  buf_ok W sh a pb -> dict_ptr_ok_any W sh a pb sh c (offset_val (a + g) pb).
Proof.
  intros Hp Ha Hg Hc Hmax Hf Hb. right. destruct pb as [| | | | | b i]; try contradiction.
  destruct Hf as (_ & _ & Hsz & _). simpl in Hsz. rewrite Z.max_r in Hsz by lia.
  split; [| split; [| exact Hb]].
  - simpl. destruct (peq b b); [reflexivity | contradiction].
  - simpl. rewrite Ptrofs.add_unsigned, (Ptrofs.unsigned_repr (a + g)) by rep_lia.
    rewrite Ptrofs.unsigned_repr by (pose proof (Ptrofs.unsigned_range i); rep_lia).
    split; [lia | intros _ _; split; [reflexivity | lia]].
Qed.

Lemma join_shares_ {cs: compspecs} t p : data_at_ shw t p * data_at_ shx t p |-- data_at_ Ews t p.
Proof. rewrite !data_at__eq, (data_at_share_join _ _ _ _ _ _ shares_join). apply derives_refl. Qed.

Lemma bytes_ok_sublist lo hi l : bytes_ok l -> bytes_ok (sublist lo hi l).
Proof. apply Forall_sublist. Qed.

Lemma mbytes_null {cs: compspecs} n l : FSpecs.mbytes n l nullval = emp.
Proof. unfold FSpecs.mbytes. apply if_true. reflexivity. Qed.

(* a one-shot decoding changes at most the context's last dictionary *)
Lemma after_keep st st' l : after_decode st st' l ->
  dc_ss st' = dc_ss st /\ dc_bl st' = dc_bl st /\ dc_set st' = dc_set st.
Proof. intros [-> | ->]; auto. Qed.

Lemma ints_le x y : 0 <= x <= Int64.max_unsigned -> 0 <= y <= Int64.max_unsigned ->
  negb (Int64.ltu (Int64.repr y) (Int64.repr x)) = (x <=? y).
Proof.
  intros. unfold Int64.ltu. rewrite !Int64.unsigned_repr by lia.
  destruct (zlt y x); symmetry; [apply Z.leb_gt | apply Z.leb_le]; lia.
Qed.

Section Main.
Variable DC : globals -> val -> dctx_st -> mpred.

(* the functions main calls *)
Definition G0 : funspecs :=
  [(_quickproof_malloc, malloc_spec'); (_quickproof_free, free_spec');
   ZSTD_isError_spec; ZSTD_decompress_usingDict_spec DC;
   ZSTD_createDCtx_spec DC; ZSTD_freeDCtx_spec DC;
   nondet_u8_spec; gp_assert_spec;
   Zstd.proof.harness.frames.FSpecs.upto_spec; @Zstd.proof.harness.frames.FSpecs.any_bytes_spec CompSpecs].

(* main's loop: one context with no session, no buffer-less stage and no DDict set *)
Definition loop_inv (gv: globals) (dctx: val) : environ -> mpred :=
  EX st: dctx_st,
  PROP (dc_ss st = ss_init; dc_bl st = None; dc_set st = nil)
  LOCAL (temp _dctx dctx; gvars gv)
  SEP (DC gv dctx st; mem_mgr gv; zstd_globals gv; TT).

Lemma body_main_G0 : semax_body Vprog G0 f_main main_spec.
Proof.
  change (semax_body Vprog G0 f_main (_main, WITH gv: globals PRE [] VST.floyd.VSU.main_pre
    Zstd.contracts.rj_any_dict.whole_prog tt gv POST [tint] (fun _ : environ => TT))).
  replace (fun _ : environ => @TT mpred _) with (PROP () LOCAL () SEP (@TT mpred _))
    by (extensionality rho; unfold PROPx, LOCALx, SEPx; simpl; normalize).
  start_function1.
  eapply (main_pre_InitGpred (zstd_globals gv * TT)%logic).
  { intros _. apply pre_globals. }
  { reflexivity. }
  { apply vars_in_Vprog. }
  start_function3.
  sep_apply (create_mem_mgr gv).
  forward_call gv.
  Intros dctx.
  destruct (eq_dec dctx nullval) as [Hd|Hd].
  { subst dctx. forward_if; [forward | contradiction]. }
  forward_if.
  { contradiction. }
  Intros. sep_apply (drop_vp (DC gv dctx dctx_init) dctx).
  forward_loop (loop_inv gv dctx) break: (loop_inv gv dctx).
  { unfold loop_inv. Exists dctx_init. entailer!. }
  { (* one iteration *)
    unfold loop_inv. Intros st.
    forward_call 9223372036854775807.
    Intros n.
    forward_call 9223372036854775807.
    Intros a.
    forward_call 9223372036854775807.
    Intros g.
    forward_call 9223372036854775807.
    Intros c.
    forward_call (gv, n).
    Intros vret. destruct vret as [ps s]. cbn [fst snd] in *.
    forward.
    (* both = any_bytes(dict_len + gap + cap) when the sum is at most PTRDIFF_MAX *)
    forward_if (EX i: int, PROP (i <> Int.zero -> a + g + c <= 9223372036854775807)
      LOCAL (temp _t'9 (Vint i); temp _both nullval; temp _src ps; temp _cap (Vlong (Int64.repr c));
             temp _gap (Vlong (Int64.repr g)); temp _dict_len (Vlong (Int64.repr a));
             temp _n (Vlong (Int64.repr n)); temp _dctx dctx; gvars gv)
      SEP (mem_mgr gv; FSpecs.mbytes n s ps; DC gv dctx st; zstd_globals gv; TT)).
    { forward.
      Exists (Int.repr (Z.b2z (Int64.cmpu Cle (Int64.add (Int64.repr a) (Int64.repr g))
                                (Int64.sub (Int64.repr 9223372036854775807) (Int64.repr c))))).
      entailer!.
      match goal with Hz: Int.repr (Z.b2z ?b) <> Int.zero |- _ => destruct b eqn:Eb; [| contradiction] end.
      unfold Int64.cmpu in Eb. rewrite ints_le in Eb by rep_lia. apply Z.leb_le in Eb. lia. }
    { forward. Exists Int.zero. entailer!. }
    Intros i9.
    forward_if (EX pb: val, EX l: list Z,
      PROP (pb <> nullval -> (Zlength l = a + g + c /\ a + g + c <= 9223372036854775807 /\ bytes_ok l)%Z)
      LOCAL (temp _both pb; temp _src ps; temp _cap (Vlong (Int64.repr c));
             temp _gap (Vlong (Int64.repr g)); temp _dict_len (Vlong (Int64.repr a));
             temp _n (Vlong (Int64.repr n)); temp _dctx dctx; gvars gv)
      SEP (mem_mgr gv; FSpecs.mbytes (a + g + c)%Z l pb; FSpecs.mbytes n s ps; DC gv dctx st; zstd_globals gv; TT)).
    { match goal with Hi: i9 <> Int.zero -> _ , Hz: i9 <> Int.zero |- _ => specialize (Hi Hz) end.
      forward_call (gv, a + g + c).
      Intros vret. destruct vret as [pb l]. cbn [fst snd] in *.
      forward. Exists pb l. entailer!. }
    { forward. Exists nullval (@nil Z). rewrite mbytes_null. entailer!. }
    Intros pb l.
    unfold FSpecs.mbytes.
    repeat apply -> seq_assoc.
    (* src or both NULL: the run ends *)
    destruct (eq_dec ps nullval) as [Hps|Hps].
    { subst ps. Intros. apply semax_if_seq. forward_if; [| contradiction]. forward.
      forward_if; [forward | exfalso; exact (Int.one_not_zero ltac:(assumption))]. }
    destruct (eq_dec pb nullval) as [Hpb|Hpb].
    { subst pb. Intros. apply semax_if_seq. forward_if; [contradiction |]. forward.
      change (bool2val (Int64.cmpu Ceq Int64.zero (Int64.repr (Int.signed (Int.repr 0))))) with (Vint Int.one).
      forward_if; [forward | exfalso; exact (Int.one_not_zero ltac:(assumption))]. }
    Intros.
    match goal with Hb: pb <> nullval -> _ |- _ => destruct (Hb Hpb) as (Hl & HL & Hbl) end.
    assert_PROP (isptr pb) as Hpb' by entailer!.
    assert_PROP (isptr ps) as Hps' by entailer!.
    apply semax_if_seq. forward_if; [contradiction |].
    destruct pb as [| | | | | b i]; try contradiction. forward.
    forward_if; [discriminate |].
    set (pb := Vptr b i) in *. subst n.
    (* the buffers at the decoder's compspecs; the block at shw as [dict | gap | dst], at shx as the witness *)
    sep_apply (to_Z Ews (Zlength s) (zbytes s) ps).
    sep_apply (to_Z Ews (a + g + c) (zbytes l) pb).
    sep_apply (tok_to_Z Ews (Zlength s) ps).
    sep_apply (tok_to_Z Ews (a + g + c) pb).
    assert_PROP (@field_compatible Zstd.units.Zstd.CS (tarray tuchar (a + g + c)) [] pb) as Hfc by entailer!.
    rewrite <- (@data_at_share_join Zstd.units.Zstd.CS shw shx Ews (tarray tuchar (a + g + c)) (zbytes l) pb shares_join).
    rewrite (@split3_bytes Zstd.units.Zstd.CS shw a g c (zbytes l) pb) by (auto; lia || (rewrite Zlength_map; lia)).
    rewrite !sublist_map.
    sep_apply (@data_at_data_at_ Zstd.units.Zstd.CS shw (tarray tuchar c) (zbytes (sublist (a + g) (a + g + c) l))
                 (offset_val (a + g) pb)).
    sep_apply (pws_fold3 (Zlength s) ps (a + g + c) pb (zbytes l)).
    assert (Hb0: Zlength (sublist 0 a l) = a) by (rewrite Zlength_sublist; lia).
    replace (@data_at Zstd.units.Zstd.CS shw (tarray tuchar a) (zbytes (sublist 0 a l)) pb)
      with (@data_at Zstd.units.Zstd.CS shw (tarray tuchar (Zlength (sublist 0 a l))) (zbytes (sublist 0 a l)) pb)
      by (rewrite Hb0; reflexivity).
    forward_call (W3 (Zlength s) ps (a + g + c) pb (zbytes l), gv, dctx, st, shw, offset_val (a + g) pb, c,
                  Ews, ps, s, shw, pb, sublist 0 a l).
    { (* dst = both + dict_len + gap *)
      rewrite Hb0. entailer!. simpl. rewrite Ptrofs.add_assoc. unfold Ptrofs.of_int64.
      rewrite !Int64.unsigned_repr by rep_lia.
      rewrite !(Ptrofs.mul_commut (Ptrofs.repr 1)), !Ptrofs.mul_one, ptrofs_add_repr. reflexivity. }
    { rewrite Hb0.
      split; [apply buf_ok_blk; auto; lia |].
      split; [apply buf_ok_src; auto; lia |].
      split.
      { apply (@dict_ok_blk Zstd.units.Zstd.CS); auto; try lia.
        apply buf_ok_blk0; auto; lia. }
      split; [apply shw_writable |].
      split; [apply writable_readable_share, shw_writable |].
      apply bytes_ok_sublist; exact Hbl. }
    Intros vret. destruct vret as [[r out] st']. cbn [fst snd] in *.
    rewrite Hb0.
    match goal with Ho: Zlength out = c |- _ => clear Ho end.
    (* a result that is not an error is at most cap (oneshot_ok's first conjunct) *)
    assert (Hr: is_error_code r = false -> r <= c)
      by (match goal with Hk: oneshot_ok _ _ _ _ _ _ |- _ => exact (proj1 Hk) end).
    api_init; match goal with Ha: after_decode _ _ _ |- _ => destruct (after_keep _ _ _ Ha) as (Ess & Ebl & Eset) end.
    (* the block back in one piece, at Ews *)
    sep_apply (@data_at_data_at_ Zstd.units.Zstd.CS shw (tarray tuchar a) (zbytes (sublist 0 a l)) pb).
    sep_apply (@data_at_data_at_ Zstd.units.Zstd.CS shw (tarray tuchar g) (zbytes (sublist a (a + g) l)) (offset_val a pb)).
    sep_apply (@data_at_data_at_ Zstd.units.Zstd.CS shw (tarray tuchar c) out (offset_val (a + g) pb)).
    sep_apply (@join3_bytes Zstd.units.Zstd.CS shw a g c pb ltac:(lia) ltac:(lia) ltac:(lia) Hfc).
    sep_apply pws_unfold3.
    sep_apply (@data_at_data_at_ Zstd.units.Zstd.CS shx (tarray tuchar (a + g + c)) (zbytes l) pb).
    sep_apply (@join_shares_ Zstd.units.Zstd.CS (tarray tuchar (a + g + c)) pb).
    forward_call r.
    (* the check: an error code, or at most cap *)
    forward_if (PROP () LOCAL (temp _t'13 (Vint Int.one); temp _both pb; temp _src ps; temp _dctx dctx; gvars gv)
      SEP (@malloc_token Zstd.units.Zstd.CS Ews (tarray tuchar (a + g + c)) pb;
           @malloc_token Zstd.units.Zstd.CS Ews (tarray tuchar (Zlength s)) ps;
           @data_at_ Zstd.units.Zstd.CS Ews (tarray tuchar (a + g + c)) pb;
           @data_at Zstd.units.Zstd.CS Ews (tarray tuchar (Zlength s)) (zbytes s) ps;
           mem_mgr gv; DC gv dctx st'; zstd_globals gv; TT)).
    + forward. entailer!.
    + forward.
      destruct (is_error_code r) eqn:Er; [exfalso; exact (Int.one_not_zero ltac:(assumption)) |].
      specialize (Hr eq_refl).
      entailer!.
      unfold Int64.cmpu. rewrite ltu_Z by rep_lia.
      destruct (Z.ltb_spec c r); [lia | reflexivity].
    + forward_call Int.one.
      (* free the two buffers *)
      sep_apply (@data_at_data_at_ Zstd.units.Zstd.CS Ews (tarray tuchar (Zlength s)) (zbytes s) ps).
      sep_apply (of_Z_ Ews (Zlength s) ps).
      sep_apply (tok_of_Z Ews (Zlength s) ps).
      sep_apply (@free_pre CompSpecs (tarray tuchar (Zlength s)) ps Hps').
      forward_call (tarray tuchar (Zlength s), ps, gv).
      sep_apply (of_Z_ Ews (a + g + c) pb).
      sep_apply (tok_of_Z Ews (a + g + c) pb).
      sep_apply (@free_pre CompSpecs (tarray tuchar (a + g + c)) pb Hpb').
      forward_call (tarray tuchar (a + g + c), pb, gv).
      (* do ... while (nondet_u8() != 0) *)
      forward_call tt. Intros u2.
      forward_if.
      * forward. Exists st'. entailer!.
      * forward. Exists st'. entailer!. }
  (* after the loop: free the context *)
  unfold loop_inv. Intros st.
  forward_call (gv, dctx, Some st).
  forward.
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

Lemma G0_in_Gprog DC DD i fs : initial_world.find_id i (G0 DC) = Some fs ->
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

Theorem rj_any_dict_ok :
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
      eapply semax_body_subsumption; [apply (body_main_G0 DC) |].
      apply tycontext_sub_i99. split; intro i.
      * rewrite (make_tycontext_g_find Vprog (G0 DC) i).
        remember (Gprog (Specs_api DC DD) Hs) as GP eqn:HGP. (* abstract while rewriting: no comparison with [] by computation *)
        rewrite (make_tycontext_g_find Vprog GP i). subst GP.
        destruct (initial_world.find_id i (G0 DC)) as [fs|] eqn:E.
        -- rewrite (G0_in_Gprog DC DD i fs E). apply sub_option_refl.
        -- destruct (initial_world.find_id i (Gprog (Specs_api DC DD) Hs)) as [fs'|] eqn:E'.
           ++ rewrite mtg_none; [exact Logic.I |].
              apply (Gprog_not_var DC DD i).
              apply initial_world.find_id_e in E'. apply (in_map fst) in E'. exact E'.
           ++ apply sub_option_refl.
      * rewrite !semax_prog.find_id_maketycontext_s.
        destruct (initial_world.find_id i (G0 DC)) as [fs|] eqn:E; [|exact Logic.I].
        rewrite (G0_in_Gprog DC DD i fs E). exists fs. split; [reflexivity|]. apply funspec_sub_si_refl.
Qed.
