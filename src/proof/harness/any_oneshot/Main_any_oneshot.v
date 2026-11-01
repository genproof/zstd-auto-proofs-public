(* The harness obligation of harness/any_oneshot.c under the decoder's API v3.
   Adapted from its proof against API v2. *)
Require Import VST.floyd.proofauto.
Require Export Zstd.proof.zstd.Spec_api6.
Require Export Zstd.proof.harness.any_oneshot.HOK_any_oneshot.
Require Zstd.proof.top.MainPre6.
Require Import Zstd.proof.zstd.NullBuf.
Require Import Zstd.proof.harness.ApiAfterKit.


#[local] Instance CCE_HZ : change_composite_env Zstd.proof.harness.any_oneshot.HOK_any_oneshot.CompSpecs Zstd.units.Zstd.CS.
Proof. make_cs_preserve Zstd.proof.harness.any_oneshot.HOK_any_oneshot.CompSpecs Zstd.units.Zstd.CS. Defined.

Lemma cs_bytes sh n v p :
  @data_at Zstd.proof.harness.any_oneshot.HOK_any_oneshot.CompSpecs sh (tarray tuchar n) v p =
  @data_at Zstd.units.Zstd.CS sh (tarray tuchar n) v p.
Proof.
  rewrite (@data_at_change_composite _ _ CCE_HZ sh (tarray tuchar n) v v); [reflexivity | apply JMeq_refl | reflexivity].
Qed.

Lemma cs_bytes_ sh n p :
  @data_at_ Zstd.proof.harness.any_oneshot.HOK_any_oneshot.CompSpecs sh (tarray tuchar n) p =
  @data_at_ Zstd.units.Zstd.CS sh (tarray tuchar n) p.
Proof.
  rewrite (@data_at__change_composite _ _ CCE_HZ sh (tarray tuchar n)); reflexivity.
Qed.

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
    (QPprog_vars Zstd.contracts.x_any_oneshot.whole_prog).
Proof.
  apply Forall_forall. intros [i v] Hin. apply make_tycontext_g_isSome.
  unfold Vprog, QPvarspecs. rewrite map_map.
  apply in_map_iff. exists (i, v). split; [reflexivity | exact Hin].
Qed.

Lemma pre_globals gv : globals_ok gv ->
  InitGPred (Vardefs Zstd.contracts.x_any_oneshot.whole_prog) gv |-- zstd_globals gv * TT.
Proof.
  intros Hgv. eapply derives_trans.
  - apply (Zstd.proof.top.MainPre6.main_pre_fact6 Zstd.contracts.x_any_oneshot.whole_prog); [|exact Hgv].
    unfold Zstd.proof.top.MainPre6.all_progs. do 3 right. left. reflexivity.
  - apply sepcon_derives; [apply derives_refl | apply TT_right].
Qed.

(* one input of the harness: n bytes s at src (malloc'd), a buffer of cap bytes at dst (malloc'd) *)
Record buf := { b_n : Z; b_s : list Z; b_src : val; b_cap : Z; b_dst : val }.

#[export] Instance Inhabitant_buf : Inhabitant buf := Build_buf 0 nil nullval 0 nullval.

Definition inp_ok (b: buf) : Prop :=
  Zlength (b_s b) = b_n b /\ 0 <= b_n b <= 4096 /\ 0 <= b_cap b <= 65536 /\ bytes_ok (b_s b) /\
  isptr (b_src b) /\ isptr (b_dst b).

Lemma isptr_of p : is_pointer_or_null p -> p <> nullval -> isptr p.
Proof. intros H1 H2. destruct p; simpl in *; auto. subst. contradiction. Qed.

(* the buffers, at the decoder's compspecs between the calls *)
Definition buf_res (b: buf) : mpred :=
  (@malloc_token Zstd.units.Zstd.CS Ews (tarray tuchar (b_n b)) (b_src b) *
  @data_at Zstd.units.Zstd.CS Ews (tarray tuchar (b_n b)) (zbytes (b_s b)) (b_src b) *
  @malloc_token Zstd.units.Zstd.CS Ews (tarray tuchar (b_cap b)) (b_dst b) *
  @data_at_ Zstd.units.Zstd.CS Ews (tarray tuchar (b_cap b)) (b_dst b))%logic.

Lemma upd_tail {A} (l: list A) (x y: A) i k : 0 <= i < k -> Zlength l = i ->
  upd_Znth i (l ++ Zrepeat x (k - i)) y = (l ++ [y]) ++ Zrepeat x (k - (i + 1)).
Proof.
  intros Hk Hl.
  replace (Zrepeat x (k - i)) with ([x] ++ Zrepeat x (k - (i + 1))).
  - rewrite upd_Znth_app2 by (rewrite ?Zlength_app, ?Zlength_Zrepeat; simpl; list_solve).
    rewrite Hl, Z.sub_diag, <- app_assoc. f_equal. rewrite upd_Znth_app1 by (simpl; list_solve).
    rewrite upd_Znth0. reflexivity.
  - replace (k - i) with (1 + (k - (i+1))) by lia. rewrite <- Zrepeat_app by lia. reflexivity.
Qed.

Lemma Znth_mid {A} {d: Inhabitant A} (l r: list A) (y: A) i :
  Zlength l = i -> Znth i ((l ++ [y]) ++ r) = y.
Proof.
  intros <-. rewrite <- app_assoc, app_Znth2 by lia. rewrite Z.sub_diag. reflexivity.
Qed.

Lemma ltu_Z x y : 0 <= x <= Int64.max_unsigned -> 0 <= y <= Int64.max_unsigned ->
  Int64.ltu (Int64.repr x) (Int64.repr y) = (x <? y).
Proof.
  intros. unfold Int64.ltu. rewrite !Int64.unsigned_repr by lia.
  destruct (zlt x y); symmetry; [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Qed.

Lemma to_Z sh n v p :
  @data_at Zstd.proof.harness.any_oneshot.HOK_any_oneshot.CompSpecs sh (tarray tuchar n) v p |--
  @data_at Zstd.units.Zstd.CS sh (tarray tuchar n) v p.
Proof. rewrite cs_bytes. apply derives_refl. Qed.

Lemma to_Z_ sh n p :
  @data_at_ Zstd.proof.harness.any_oneshot.HOK_any_oneshot.CompSpecs sh (tarray tuchar n) p |--
  @data_at_ Zstd.units.Zstd.CS sh (tarray tuchar n) p.
Proof. rewrite cs_bytes_. apply derives_refl. Qed.

Lemma of_Z_ sh n p :
  @data_at_ Zstd.units.Zstd.CS sh (tarray tuchar n) p |--
  @data_at_ Zstd.proof.harness.any_oneshot.HOK_any_oneshot.CompSpecs sh (tarray tuchar n) p.
Proof. rewrite cs_bytes_. apply derives_refl. Qed.

Lemma fold_sep_snoc (l: list mpred) x : fold_right sepcon emp (l ++ [x]) = (fold_right sepcon emp l * x)%logic.
Proof.
  induction l as [|a l IH]; simpl.
  - rewrite sepcon_emp, emp_sepcon. reflexivity.
  - rewrite IH, sepcon_assoc. reflexivity.
Qed.

Lemma bytes_ok_of (l: list Z) : Forall (fun b : Z => 0 <= b <= Byte.max_unsigned) l -> bytes_ok l.
Proof. intros H. eapply Forall_impl; [|exact H]. intros a Ha. unfold is_byte. rep_lia. Qed.

Lemma pick2 (bs: list buf) i : Zlength bs = 2 -> 0 <= i < 2 ->
  fold_right sepcon emp (map buf_res bs) = (buf_res (Znth i bs) * buf_res (Znth (1 - i) bs))%logic.
Proof.
  intros Hl Hi. destruct bs as [|a [|b [|c bs]]]; try (rewrite ?Zlength_cons, ?Zlength_nil in Hl; rep_lia).
  assert (i = 0 \/ i = 1) as [-> | ->] by lia; simpl; rewrite sepcon_emp; [reflexivity | apply sepcon_comm].
Qed.

Lemma inp_ok_at bs i : Forall inp_ok bs -> 0 <= i < Zlength bs -> inp_ok (Znth i bs).
Proof. intros. apply Forall_Znth; auto. Qed.

Lemma free_pre {cs: compspecs} t p : isptr p ->
  (malloc_token Ews t p * data_at_ Ews t p) |-- (if eq_dec p nullval then emp else (malloc_token Ews t p * data_at_ Ews t p)).
Proof. intros. rewrite if_false by (intro; subst; contradiction). apply derives_refl. Qed.

(* the fact a gp_assume(x <= k) gives *)
Ltac get_assume :=
  match goal with Hx: Int.repr (if Int64.ltu (Int64.repr ?k) (Int64.repr ?x) then 0 else 1) <> Int.zero |- _ =>
    let E := fresh "E" in
    rewrite ltu_Z in Hx by rep_lia; destruct (k <? x) eqn:E;
    [exact (False_ind _ (Hx eq_refl)) | apply Z.ltb_ge in E; clear Hx] end.

(* gp_assert(r <= cap) when r <= cap *)
Ltac assert_fits :=
  rewrite ltu_Z by rep_lia;
  match goal with |- context [?x <? ?y] => replace (x <? y) with false by (symmetry; apply Z.ltb_ge; lia) end;
  reflexivity.

Lemma tok_to_Z sh n p :
  @malloc_token Zstd.proof.harness.any_oneshot.HOK_any_oneshot.CompSpecs sh (tarray tuchar n) p |--
  @malloc_token Zstd.units.Zstd.CS sh (tarray tuchar n) p.
Proof. rewrite (@malloc_token_change_composite _ _ CCE_HZ sh (tarray tuchar n)) by reflexivity. apply derives_refl. Qed.

Lemma tok_of_Z sh n p :
  @malloc_token Zstd.units.Zstd.CS sh (tarray tuchar n) p |--
  @malloc_token Zstd.proof.harness.any_oneshot.HOK_any_oneshot.CompSpecs sh (tarray tuchar n) p.
Proof. rewrite (@malloc_token_change_composite _ _ CCE_HZ sh (tarray tuchar n)) by reflexivity. apply derives_refl. Qed.

(* the buffer witnesses main lends to a one-shot call: the malloc_tokens of its two buffers *)
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

Lemma refold bs i : Zlength bs = 2 -> 0 <= i < 2 -> Zlength (b_s (Znth i bs)) = b_n (Znth i bs) ->
  (@malloc_token Zstd.units.Zstd.CS Ews (tarray tuchar (Zlength (b_s (Znth i bs)))) (b_src (Znth i bs)) *
   @data_at Zstd.units.Zstd.CS Ews (tarray tuchar (Zlength (b_s (Znth i bs)))) (zbytes (b_s (Znth i bs))) (b_src (Znth i bs)) *
   @malloc_token Zstd.units.Zstd.CS Ews (tarray tuchar (b_cap (Znth i bs))) (b_dst (Znth i bs)) *
   @data_at_ Zstd.units.Zstd.CS Ews (tarray tuchar (b_cap (Znth i bs))) (b_dst (Znth i bs)) *
   buf_res (Znth (1 - i) bs)) |-- fold_right sepcon emp (map buf_res bs).
Proof.
  intros Hl Hi Hn. rewrite (pick2 bs i Hl Hi). rewrite Hn. unfold buf_res. cancel.
Qed.

Lemma vp_frame (P Q: mpred) p : ((P && valid_pointer p) * Q) |-- valid_pointer p.
Proof. apply sepcon_valid_pointer1. apply andp_left2. apply derives_refl. Qed.

Lemma drop_vp (P: mpred) p : (P && valid_pointer p) |-- P.
Proof. apply andp_left1. apply derives_refl. Qed.

Lemma dict_res_none_i DD0 gv sh : emp |-- dict_res DD0 gv sh (dc_dict dctx_init).
Proof. apply derives_refl. Qed.

Lemma dict_res_none_e DD0 gv sh : dict_res DD0 gv sh (dc_dict dctx_init) |-- emp.
Proof. apply derives_refl. Qed.

Lemma res_none_i DD0 gv sh :
  emp |-- dict_res DD0 gv sh (dc_dict dctx_init) * set_res DD0 gv sh (dc_set dctx_init) (dc_dict dctx_init).
Proof. simpl. rewrite emp_sepcon. apply derives_refl. Qed.

Lemma res_none_e DD0 gv sh :
  dict_res DD0 gv sh (dc_dict dctx_init) * set_res DD0 gv sh (dc_set dctx_init) (dc_dict dctx_init) |-- emp.
Proof. simpl. rewrite emp_sepcon. apply derives_refl. Qed.

(* a decoding clears dc_ex (the stream may then read what it left behind); nothing else of a new context changes *)
Lemma dctx_init_after ex st' :
  after_decode (after_use (set_ex dctx_init ex)) st' (dc_dict (set_ex dctx_init ex)) -> st' = set_ex dctx_init false.
Proof. intros [-> | ->]; reflexivity. Qed.

Lemma res_none_ex_i DD0 gv sh ex :
  emp |-- dict_res DD0 gv sh (dc_dict (set_ex dctx_init ex)) *
          set_res DD0 gv sh (dc_set (set_ex dctx_init ex)) (dc_dict (set_ex dctx_init ex)).
Proof. simpl. rewrite emp_sepcon. apply derives_refl. Qed.

Lemma res_none_ex_e DD0 gv sh ex :
  dict_res DD0 gv sh (dc_dict (set_ex dctx_init ex)) *
  set_res DD0 gv sh (dc_set (set_ex dctx_init ex)) (dc_dict (set_ex dctx_init ex)) |-- emp.
Proof. simpl. rewrite emp_sepcon. apply derives_refl. Qed.

(* the loads of dst[i], cap[i], src[i], n[i] *)
Ltac load_inputs i :=
  do 4 (forward; [entailer!; rewrite Znth_map by lia; first [exact Logic.I | auto] |]);
  rewrite ?(Znth_map i) by lia.

(* return from main: the local arrays go back to the stack frame *)
Ltac ret_frame :=
  repeat match goal with |- context [data_at Tsh ?t ?v ?p] => sep_apply (data_at_data_at_ Tsh t v p) end;
  cancel.

Section Main.
Variable DC : globals -> val -> dctx_st -> mpred.
Variable DD : globals -> val -> ddict_st -> mpred.

(* the functions main calls *)
Definition G0 : funspecs :=
  [(_quickproof_malloc, malloc_spec'); (_quickproof_free, free_spec');
   ZSTD_isError_spec; ZSTD_decompress_spec; ZSTD_decompressDCtx_spec DC DD;
   ZSTD_createDCtx_spec DC; ZSTD_freeDCtx_spec DC;
   nondet_size_spec; nondet_bytes_nn_spec; gp_assert_spec; gp_assume_spec].

Lemma body_main_G0 : semax_body Vprog G0 f_main main_spec.
Proof.
  change (semax_body Vprog G0 f_main (_main, WITH gv: globals PRE [] VST.floyd.VSU.main_pre
    Zstd.contracts.x_any_oneshot.whole_prog tt gv POST [tint] (fun _ : environ => TT))).
  replace (fun _ : environ => @TT mpred _) with (PROP () LOCAL () SEP (@TT mpred _))
    by (extensionality rho; unfold PROPx, LOCALx, SEPx; simpl; normalize).
  start_function1.
  eapply (main_pre_InitGpred (zstd_globals gv * TT)%logic).
  { apply pre_globals. }
  { reflexivity. }
  { apply vars_in_Vprog. }
  start_function3.
  sep_apply (create_mem_mgr gv).
  forward_for_simple_bound 2 (EX i: Z, EX bs: list buf,
    PROP (Zlength bs = i; Forall inp_ok bs)
    LOCAL (lvar _cap (tarray tulong 2) v_cap; lvar _n (tarray tulong 2) v_n;
           lvar _dst (tarray (tptr tuchar) 2) v_dst; lvar _src (tarray (tptr tuchar) 2) v_src; gvars gv)
    SEP (data_at Tsh (tarray tulong 2) (map (fun b => Vlong (Int64.repr (b_cap b))) bs ++ Zrepeat Vundef (2 - i)) v_cap;
         data_at Tsh (tarray tulong 2) (map (fun b => Vlong (Int64.repr (b_n b))) bs ++ Zrepeat Vundef (2 - i)) v_n;
         data_at Tsh (tarray (tptr tuchar) 2) (map b_dst bs ++ Zrepeat Vundef (2 - i)) v_dst;
         data_at Tsh (tarray (tptr tuchar) 2) (map b_src bs ++ Zrepeat Vundef (2 - i)) v_src;
         fold_right sepcon emp (map buf_res bs); mem_mgr gv; zstd_globals gv; TT))%assert.
  { Exists (@nil buf). entailer!. }
  { (* one input *)
    cbv beta. Intros bs.
    forward_call tt.
    Intros n.
    forward.
    rewrite upd_tail by (try rewrite Zlength_map; lia).
    forward.
    { entailer!. rewrite Znth_mid by (rewrite Zlength_map; lia). exact Logic.I. }
    rewrite Znth_mid by (rewrite Zlength_map; lia).
    forward_call (Int.repr (if Int64.ltu (Int64.repr 4096) (Int64.repr n) then 0 else 1)).
    { entailer!. simpl. destruct (Int64.ltu (Int64.repr 4096) (Int64.repr n)); reflexivity. }
    get_assume.
    forward.
    { entailer!. rewrite Znth_mid by (rewrite Zlength_map; lia). exact Logic.I. }
    rewrite Znth_mid by (rewrite Zlength_map; lia).
    forward_call (tarray tuchar n, gv).
    { simpl. rep_lia. }
    Intros ps.
    forward.
    rewrite upd_tail by (try rewrite Zlength_map; lia).
    forward.
    { entailer!. rewrite Znth_mid by (rewrite Zlength_map; lia). assumption. }
    rewrite Znth_mid by (rewrite Zlength_map; lia).
    repeat apply -> seq_assoc. apply semax_if_seq.
    destruct (eq_dec ps nullval) as [Hps|Hps].
    { forward_if.
      - forward. ret_frame.
      - subst ps. congruence. }
    forward_if.
    { exfalso. subst ps. apply Hps. reflexivity. }
    Intros.
    forward.
    { entailer!. rewrite Znth_mid by (rewrite Zlength_map; lia). auto. }
    rewrite Znth_mid by (rewrite Zlength_map; lia).
    forward.
    { entailer!. rewrite Znth_mid by (rewrite Zlength_map; lia). exact Logic.I. }
    rewrite Znth_mid by (rewrite Zlength_map; lia).
    forward_call (ps, n, Ews).
    Intros sb.
    (* the capacity *)
    forward_call tt.
    Intros c.
    forward.
    rewrite upd_tail by (try rewrite Zlength_map; lia).
    forward.
    { entailer!. rewrite Znth_mid by (rewrite Zlength_map; lia). exact Logic.I. }
    rewrite Znth_mid by (rewrite Zlength_map; lia).
    forward_call (Int.repr (if Int64.ltu (Int64.repr 65536) (Int64.repr c) then 0 else 1)).
    { entailer!. simpl. destruct (Int64.ltu (Int64.repr 65536) (Int64.repr c)); reflexivity. }
    get_assume.
    forward.
    { entailer!. rewrite Znth_mid by (rewrite Zlength_map; lia). exact Logic.I. }
    rewrite Znth_mid by (rewrite Zlength_map; lia).
    forward_call (tarray tuchar c, gv).
    { simpl. rep_lia. }
    Intros pd.
    forward.
    rewrite upd_tail by (try rewrite Zlength_map; lia).
    forward.
    { entailer!. rewrite Znth_mid by (rewrite Zlength_map; lia). assumption. }
    rewrite Znth_mid by (rewrite Zlength_map; lia).
    destruct (eq_dec pd nullval) as [Hpd|Hpd].
    { forward_if.
      - forward. ret_frame.
      - subst pd. congruence. }
    forward_if.
    { exfalso. subst pd. apply Hpd. reflexivity. }
    Intros.
    sep_apply (to_Z Ews n (zbytes sb) ps).
    sep_apply (to_Z_ Ews c pd).
    sep_apply (tok_to_Z Ews n ps).
    sep_apply (tok_to_Z Ews c pd).
    forward.
    Exists (bs ++ [Build_buf n sb ps c pd]).
    rewrite !map_app. simpl map. rewrite fold_sep_snoc.
    entailer!.
    - split; [list_solve|]. apply Forall_app. split; [exact H1|].
      constructor; [|constructor]. unfold inp_ok; simpl. split; [reflexivity|]. split; [lia|].
      split; [lia|]. split; [apply bytes_ok_of; assumption|]. split; apply isptr_of; assumption.
    - unfold buf_res; simpl. cancel. }
  (* after the loop: two inputs *)
  Intros bs.
  match goal with Hl: Zlength bs = 2, Hf: Forall inp_ok bs |- _ => rename Hl into Hlen; rename Hf into Hok end.
  change (Zrepeat Vundef (2 - 2)) with (@nil val). rewrite !app_nil_r.
  abbreviate_semax.
  (* ZSTD_decompress on the first input *)
  destruct (inp_ok_at bs 0 Hok ltac:(lia)) as (Hn & Hn' & Hc & Hs & Hps & Hpd).
  load_inputs 0.
  rewrite (pick2 bs 0) by lia. unfold buf_res at 1. Intros. rewrite <- Hn.
  sep_apply (pws_fold (tarray tuchar (Zlength (b_s (Znth 0 bs)))) (b_src (Znth 0 bs))
                      (tarray tuchar (b_cap (Znth 0 bs))) (b_dst (Znth 0 bs))).
  sep_apply (data_at__mbuf Ews (b_cap (Znth 0 bs)) (b_dst (Znth 0 bs))).
  forward_call ([pw_token Ews (tarray tuchar (Zlength (b_s (Znth 0 bs)))) (b_src (Znth 0 bs));
                 pw_token Ews (tarray tuchar (b_cap (Znth 0 bs))) (b_dst (Znth 0 bs))],
                gv, Ews, b_dst (Znth 0 bs), b_cap (Znth 0 bs), Ews, b_src (Znth 0 bs), b_s (Znth 0 bs)).
  { split; (apply buf_ok_tok; [simpl; tauto | auto | lia | auto]). }
  Intros vret. destruct vret as [r out]. cbn [fst snd]. rewrite mbuf_isptr by auto.
  match goal with H1: 0 <= fst _ <= _, H2: Zlength (snd _) = _, H3: oneshot_ok _ _ _ _ _ _ |- _ =>
    cbn [fst snd] in H1, H2, H3; rename H1 into Hr; rename H2 into Hout; rename H3 into Hok1 end.
  sep_apply pws_unfold.
  sep_apply (@data_at_data_at_ Zstd.units.Zstd.CS Ews (tarray tuchar (b_cap (Znth 0 bs))) out (b_dst (Znth 0 bs))).
  forward.
  forward_call r.
  destruct Hok1 as [Hfit _].
  forward_if True.
  - assert (Er: is_error_code r = false) by (destruct (is_error_code r); [discriminate | reflexivity]).
    specialize (Hfit Er).
    forward. { entailer!. rewrite Znth_map by lia. exact Logic.I. }
    rewrite Znth_map by lia.
    forward_call Int.one.
    { entailer!. simpl. assert_fits. }
    entailer!.
  - forward. entailer!.
  - Intros. sep_apply (refold bs 0 Hlen ltac:(lia) Hn). clear Hfit Hr Hout.
    deadvars!.
    repeat match goal with H: oneshot_codes _ _ _ _ _ _ |- _ => clear H end.
    clear Hn Hn' Hc Hs Hps Hpd r out.
    forward_call gv.
    Intros dctx.
    forward_if (EX ex: bool, PROP ()
      LOCAL (temp _dctx dctx; lvar _cap (tarray tulong 2) v_cap; lvar _n (tarray tulong 2) v_n;
             lvar _dst (tarray (tptr tuchar) 2) v_dst; lvar _src (tarray (tptr tuchar) 2) v_src; gvars gv)
      SEP ((if eq_dec dctx nullval then emp else DC gv dctx (set_ex dctx_init ex));
           fold_right sepcon emp (map buf_res bs); mem_mgr gv; zstd_globals gv;
           data_at Tsh (tarray tulong 2) (map (fun b : buf => Vlong (Int64.repr (b_cap b))) bs) v_cap;
           data_at Tsh (tarray tulong 2) (map (fun b : buf => Vlong (Int64.repr (b_n b))) bs) v_n;
           data_at Tsh (tarray (tptr tuchar) 2) (map b_dst bs) v_dst;
           data_at Tsh (tarray (tptr tuchar) 2) (map b_src bs) v_src; TT)).
    { destruct (eq_dec dctx nullval) as [E|E]; apply denote_tc_test_eq_split;
        try apply valid_pointer_null; try (subst; apply valid_pointer_null).
      eapply derives_trans; [| apply (vp_frame (DC gv dctx dctx_init) TT dctx)]. cancel. }
    { (* the context: two decodings *)
      rewrite if_false by assumption. Intros.
      sep_apply (drop_vp (DC gv dctx dctx_init) dctx).
      forward_for_simple_bound 2 (EX i: Z, EX ex: bool,
        PROP ()
        LOCAL (temp _dctx dctx; lvar _cap (tarray tulong 2) v_cap; lvar _n (tarray tulong 2) v_n;
               lvar _dst (tarray (tptr tuchar) 2) v_dst; lvar _src (tarray (tptr tuchar) 2) v_src; gvars gv)
        SEP (DC gv dctx (set_ex dctx_init ex);
             fold_right sepcon emp (map buf_res bs); mem_mgr gv; zstd_globals gv;
             data_at Tsh (tarray tulong 2) (map (fun b : buf => Vlong (Int64.repr (b_cap b))) bs) v_cap;
             data_at Tsh (tarray tulong 2) (map (fun b : buf => Vlong (Int64.repr (b_n b))) bs) v_n;
             data_at Tsh (tarray (tptr tuchar) 2) (map b_dst bs) v_dst;
             data_at Tsh (tarray (tptr tuchar) 2) (map b_src bs) v_src; TT))%assert.
      - Exists true. change (set_ex dctx_init true) with dctx_init. entailer!.
      - destruct (inp_ok_at bs i Hok ltac:(lia)) as (Hn & Hn' & Hc & Hs & Hps & Hpd).
        load_inputs i.
        rewrite (pick2 bs i) by lia. unfold buf_res at 1. Intros. rewrite <- Hn.
        sep_apply (pws_fold (tarray tuchar (Zlength (b_s (Znth i bs)))) (b_src (Znth i bs))
                            (tarray tuchar (b_cap (Znth i bs))) (b_dst (Znth i bs))).
        sep_apply (data_at__mbuf Ews (b_cap (Znth i bs)) (b_dst (Znth i bs))).
        sep_apply (res_none_ex_i DD gv Ews ex).
        forward_call ([pw_token Ews (tarray tuchar (Zlength (b_s (Znth i bs)))) (b_src (Znth i bs));
                       pw_token Ews (tarray tuchar (b_cap (Znth i bs))) (b_dst (Znth i bs))],
                      gv, dctx, set_ex dctx_init ex, Ews,
                      Ews, b_dst (Znth i bs), b_cap (Znth i bs), Ews, b_src (Znth i bs), b_s (Znth i bs)).
        { cancel. }
        { split; (apply buf_ok_tok; [simpl; tauto | auto | lia | auto]). }
        Intros vret. destruct vret as [[r out] st']. cbn [fst snd]. rewrite mbuf_isptr by auto. api_init.
        match goal with H1: 0 <= fst (fst _) <= _, H2: Zlength (snd (fst _)) = _, H3: oneshot_dctx _ _ _ _ _,
                        H4: after_decode _ _ _ |- _ =>
          cbn [fst snd] in H1, H2, H3, H4; unfold oneshot_dctx in H3; cbn [dc_set set_ex dctx_init] in H3;
          rename H1 into Hr; rename H2 into Hout; rename H3 into Hok1;
          apply dctx_init_after in H4; subst st' end.
        sep_apply (res_none_ex_e DD gv Ews ex).
        sep_apply pws_unfold.
        sep_apply (@data_at_data_at_ Zstd.units.Zstd.CS Ews (tarray tuchar (b_cap (Znth i bs))) out (b_dst (Znth i bs))).
        forward.
        forward_call r.
        destruct Hok1 as [Hfit _].
        forward_if True.
        + assert (Er: is_error_code r = false) by (destruct (is_error_code r); [discriminate | reflexivity]).
          specialize (Hfit Er).
          forward. { entailer!. rewrite Znth_map by lia. exact Logic.I. }
          rewrite Znth_map by lia.
          forward_call Int.one.
          { entailer!. simpl. assert_fits. }
          entailer!.
        + forward. entailer!.
        + Intros. sep_apply (refold bs i Hlen ltac:(lia) Hn). Exists false. entailer!.
      - Intros ex. Exists ex. rewrite if_false by assumption. entailer!. }
    { forward. Exists true. rewrite if_true by assumption. entailer!. }
    Intros ex.
    (* free the context, and NULL *)
    replace (if eq_dec dctx nullval then emp else DC gv dctx (set_ex dctx_init ex))
      with (match (if eq_dec dctx nullval then None else Some (set_ex dctx_init ex)) with
            | None => emp | Some st => DC gv dctx st end)
      by (destruct (eq_dec dctx nullval); reflexivity).
    forward_call (gv, dctx, if eq_dec dctx nullval then None else Some (set_ex dctx_init ex)).
    { destruct (eq_dec dctx nullval); auto. }
    forward_call (gv, nullval, @None dctx_st).
    { cancel. }
    (* free the buffers *)
    abbreviate_semax.
    forward_for_simple_bound 2 (EX i: Z,
      PROP ()
      LOCAL (lvar _cap (tarray tulong 2) v_cap; lvar _n (tarray tulong 2) v_n;
             lvar _dst (tarray (tptr tuchar) 2) v_dst; lvar _src (tarray (tptr tuchar) 2) v_src; gvars gv)
      SEP (fold_right sepcon emp (map buf_res (sublist i 2 bs)); mem_mgr gv; zstd_globals gv;
           data_at Tsh (tarray tulong 2) (map (fun b : buf => Vlong (Int64.repr (b_cap b))) bs) v_cap;
           data_at Tsh (tarray tulong 2) (map (fun b : buf => Vlong (Int64.repr (b_n b))) bs) v_n;
           data_at Tsh (tarray (tptr tuchar) 2) (map b_dst bs) v_dst;
           data_at Tsh (tarray (tptr tuchar) 2) (map b_src bs) v_src; TT))%assert.
    + rewrite (sublist_same 0 2 bs) by lia. entailer!.
    + destruct (inp_ok_at bs i Hok ltac:(lia)) as (Hn & Hn' & Hc & Hs & Hps & Hpd).
      rewrite (sublist_next i 2 bs) by lia. cbn [map fold_right]. unfold buf_res at 1. Intros.
      forward. { entailer!. rewrite Znth_map by lia. auto. }
      rewrite Znth_map by lia.
      sep_apply (@data_at_data_at_ Zstd.units.Zstd.CS Ews (tarray tuchar (b_n (Znth i bs))) (zbytes (b_s (Znth i bs))) (b_src (Znth i bs))).
      sep_apply (of_Z_ Ews (b_n (Znth i bs)) (b_src (Znth i bs))).
      sep_apply (tok_of_Z Ews (b_n (Znth i bs)) (b_src (Znth i bs))).
      sep_apply (@free_pre Zstd.proof.harness.any_oneshot.HOK_any_oneshot.CompSpecs (tarray tuchar (b_n (Znth i bs))) (b_src (Znth i bs)) Hps).
      forward_call (tarray tuchar (b_n (Znth i bs)), b_src (Znth i bs), gv).
      forward. { entailer!. rewrite Znth_map by lia. auto. }
      rewrite Znth_map by lia.
      sep_apply (of_Z_ Ews (b_cap (Znth i bs)) (b_dst (Znth i bs))).
      sep_apply (tok_of_Z Ews (b_cap (Znth i bs)) (b_dst (Znth i bs))).
      sep_apply (@free_pre Zstd.proof.harness.any_oneshot.HOK_any_oneshot.CompSpecs (tarray tuchar (b_cap (Znth i bs))) (b_dst (Znth i bs)) Hpd).
      forward_call (tarray tuchar (b_cap (Znth i bs)), b_dst (Znth i bs), gv).
      entailer!.
    + rewrite sublist_nil. cbn [map fold_right].
      forward. ret_frame.
Qed.

End Main.

(* ---------- from G0 to Gprog (Specs_api DC DD) [] ---------- *)

Lemma Externals_eq : Externals = [nondet_size_spec; nondet_bytes_nn_spec; gp_assert_spec; gp_assume_spec].
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

Lemma Gprog_cons DC DD : Gprog (Specs_api DC DD) [] =
  (_quickproof_malloc, malloc_spec') :: (_quickproof_free, free_spec') ::
  (Specs_api DC DD ++ [nondet_size_spec; nondet_bytes_nn_spec; gp_assert_spec; gp_assume_spec; main_spec]).
Proof. unfold Gprog, Imports. rewrite Externals_eq. reflexivity. Qed.

Lemma G0_in_Gprog DC DD i fs : initial_world.find_id i (G0 DC DD) = Some fs ->
  initial_world.find_id i (Gprog (Specs_api DC DD) []) = Some fs.
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
Lemma Gprog_not_var DC DD i : In i (map fst (Gprog (Specs_api DC DD) [])) -> ~ In i (map fst Vprog).
Proof.
  intros Hin Hv.
  assert (Hb: forallb (fun j => negb (id_in_list j (map fst Vprog))) (map fst (Gprog (Specs_api DC DD) [])) = true).
  { match goal with |- forallb ?f ?l = true => let L := eval lazy in l in change l with L end.
    vm_compute. reflexivity. }
  rewrite forallb_forall in Hb. specialize (Hb i Hin).
  rewrite (Zstd.proof.top.MainPre6.MP_id_in_list_true_i i _ Hv) in Hb. discriminate.
Qed.

Theorem any_oneshot_ok :
  forall (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred),
    exists Hs, HarnessOK (Specs_api DC DD) Hs.
Proof.
  intros DC DD. exists []. split.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    exists f_main. split; [reflexivity|]. split; [reflexivity|].
    eapply semax_body_subsumption; [apply (body_main_G0 DC DD) |].
    apply tycontext_sub_i99. split; intro i.
    + (* both lists abstracted, so that the rewriting never compares them with the empty one by computation *)
      remember (G0 DC DD) as GG eqn:HGG. remember (Gprog (Specs_api DC DD) []) as GP eqn:HGP.
      rewrite (make_tycontext_g_find Vprog GG i), (make_tycontext_g_find Vprog GP i).
      subst GG GP.
      destruct (initial_world.find_id i (G0 DC DD)) as [fs|] eqn:E.
      * rewrite (G0_in_Gprog DC DD i fs E). apply sub_option_refl.
      * destruct (initial_world.find_id i (Gprog (Specs_api DC DD) [])) as [fs'|] eqn:E'.
        -- rewrite mtg_none; [exact Logic.I |].
           apply (Gprog_not_var DC DD i).
           apply initial_world.find_id_e in E'. apply (in_map fst) in E'. exact E'.
        -- apply sub_option_refl.
    + rewrite !semax_prog.find_id_maketycontext_s.
      destruct (initial_world.find_id i (G0 DC DD)) as [fs|] eqn:E; [|exact Logic.I].
      rewrite (G0_in_Gprog DC DD i fs E). exists fs. split; [reflexivity|]. apply funspec_sub_si_refl.
Qed.
