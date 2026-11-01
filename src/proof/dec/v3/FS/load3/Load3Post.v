(* FS3 load3: the abstract state after loading a dictionary (pure) *)
Require Import Zstd.proof.dec.v3.FS.FSOblig3.
Local Open Scope logic.

Section CM_Load3Post_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Definition not_ddict (dr: dictref) : Prop := match dr_src dr with DSDDict _ _ => False | _ => True end.

(* ---------- records rebuilt from their own fields ---------- *)

Lemma sf_with_held_same (s: sfields) : sf_with_held s (sf_held s) = s.
Proof. destruct s; reflexivity. Qed.

Lemma sf_with_mem_same (s: sfields) : sf_with_mem s (sf_mem s) = s.
Proof. destruct s; reflexivity. Qed.

Lemma c3_with_s_same (k: cst3) : c3_with_s k (c3_s k) = k.
Proof. destruct k; reflexivity. Qed.

Lemma set_mem_same (st: dctx_st) : set_mem st (dc_mem st) = st.
Proof. destruct st; reflexivity. Qed.

(* ---------- the bytes of the local DDict ---------- *)

(* a context with the default allocator holds none for its local DDict (it is the default allocator's) *)
Lemma local_held_none (d: dfields) : local_mem None d -> local_held d = 0.
Proof.
  unfold local_mem, local_held. intros H. destruct (eq_dec (df_local d) nullval) as [E|E]; [reflexivity |].
  destruct (df_lx d) as [[x buf]|] eqn:Ex; [| reflexivity].
  destruct (H E) as [_ H2]. specialize (H2 x buf eq_refl).
  unfold ddx_held. destruct (dx_mem x); [contradiction | reflexivity].
Qed.

(* the local DDict a load makes is of the context's allocator *)
Lemma load_res3_local am pk b m t r d : load_res3 am pk b m t r d -> local_mem am d.
Proof.
  unfold load_res3, local_mem. destruct (Zlength b =? 0).
  - intros [_ ->]. simpl. intros E; contradiction.
  - intros [[_ [_ (q & buf & ores & _ & _ & ->)]] | [_ ->]]; simpl; intros E.
    + split; [discriminate |]. intros x buf' Hx. inversion Hx; subst. simpl. apply cm_same_refl.
    + contradiction.
Qed.

Lemma load_res3_r am pk b m t r d : load_res3 am pk b m t r d -> r = 0 \/ r = err_code ZSTD_error_memory_allocation.
Proof.
  unfold load_res3. destruct (Zlength b =? 0); [intros [-> _]; auto |].
  intros [[-> _] | [-> _]]; auto.
Qed.

(* ZSTD_DCtx_loadDictionary_advanced at stage 0: the new dictionary fields *)
Lemma load_int_res_stage0 k pk b m t r k' :
  sf_stage (c3_s k) = 0 -> load_int_res k pk b m t r k' ->
  exists d', load_res3 (sf_mem (c3_s k)) pk b m t r d' /\
    k' = c3_with_dict (c3_with_s k (sf_with_held (c3_s k)
                                      (sf_held (c3_s k) - local_held (c3_dict k) + local_held d'))) d'.
Proof. intros H [[Hn _] | [_ Hx]]; [contradiction | exact Hx]. Qed.

(* ... with the default allocator: only the dictionary fields change *)
Lemma load_int_res_none k pk b m t r k' :
  sf_stage (c3_s k) = 0 -> sf_mem (c3_s k) = None -> local_mem None (c3_dict k) -> load_int_res k pk b m t r k' ->
  exists d', load_res3 None pk b m t r d' /\ k' = c3_with_dict k d'.
Proof.
  intros Hs Hm Hl H. destruct (load_int_res_stage0 _ _ _ _ _ _ _ Hs H) as [d' [Hd ->]].
  rewrite Hm in Hd. exists d'. split; [exact Hd |].
  rewrite (local_held_none _ Hl), (local_held_none d' (load_res3_local _ _ _ _ _ _ _ Hd)).
  rewrite Z.sub_0_r, Z.add_0_r, sf_with_held_same, c3_with_s_same. reflexivity.
Qed.

(* ---------- the relation after a load ---------- *)

(* the context a load acts on: the abstract st0 (the caller's, or it with a new stream between two frames) is related
   to k0 at zdss_init, without a buffer-less frame, but for its allocator's bound (st0 with the allocator of k0); a
   stream that did not fail is a new one (ss_restart) *)
Definition load_pre (st0: dctx_st) (k0: cst3) : Prop :=
  base_rel3 (set_mem st0 (sf_mem (c3_s k0))) k0 /\ sf_stage (c3_s k0) = 0 /\ dc_bl st0 = None /\
  (dc_ss st0 <> ss_init -> ss_err (dc_ss st0) = false -> dc_ss st0 = ss_restart).

(* ---------- a function refused while a frame is being streamed (Spec_api6.after_stage) ---------- *)

Definition ss_eq_dec (a b: sstate) : {a = b} + {a <> b}.
Proof.
  assert (Hp: forall x y: val * Z, {x = y} + {x <> y})
    by (intros; decide equality; first [apply Z.eq_dec | apply Val.eq]).
  assert (Ho: forall x y: option (val * Z), {x = y} + {x <> y}) by (intros; decide equality).
  assert (Hc: forall x y: zcall, {x = y} + {x <> y})
    by (unfold zcall; intros; decide equality; first [apply Z.eq_dec | apply (list_eq_dec Z.eq_dec)]).
  decide equality;
    first [apply Z.eq_dec | apply bool_dec | apply (list_eq_dec Z.eq_dec) | apply Ho | apply (list_eq_dec Hc)].
Defined.

(* the context such a function acts on when zstd does not refuse: the caller's before any stream, else a new stream
   (or the failed one) between two frames *)
Definition st_next (st: dctx_st) : dctx_st :=
  if ss_eq_dec (dc_ss st) ss_init then st else set_ss st (ss_next (dc_ss st)).

(* ... and the state it leaves: its result, with dc_ex cleared between two frames (the context is no longer the image
   of its calls on a clean one) *)
Definition ex_next (st st1: dctx_st) : dctx_st :=
  if ss_eq_dec (dc_ss st) ss_init then st1 else set_ex st1 false.

Lemma after_stage_next (res: dctx_st -> Z -> dctx_st -> Prop) (st: dctx_st) (r: Z) (st': dctx_st) :
  res (st_next st) r st' -> after_stage res st r (ex_next st st').
Proof.
  unfold st_next, ex_next, after_stage. destruct (ss_eq_dec (dc_ss st) ss_init) as [E|E]; intros H.
  - left. auto.
  - right. split; [exact E | right; exists st'; split; [exact H | reflexivity]].
Qed.

(* DC3_of's clauses after such a function, from those of its result st1 on st_next st (at stage 0, a new stream
   between two frames): the exact relation is kept before any stream (the stream, the streaming fields up to the
   allocator, the frame fields and the tables unchanged), vacuous between two frames *)
Lemma ex_next_dc3 (SR: srel3) (gv: globals) (BR: blrel) (st st1: dctx_st) (k k1: cst3) :
  ex_on3 SR st k -> dc_ss st1 = dc_ss (st_next st) -> dc_ex st1 = dc_ex st ->
  sf_strip (c3_s k1) = sf_strip (c3_s k) -> c3_fs k1 = c3_fs k -> c3_tabs k1 = c3_tabs k -> sf_stage (c3_s k1) = 0 ->
  base_rel3 st1 k1 ->
  (dc_ss st1 <> ss_init -> ss_err (dc_ss st1) = false ->
     SR gv st1 k1 \/ (dc_ss st1 = ss_restart /\ sf_stage (c3_s k1) = 0)) ->
  (forall ba, dc_bl st1 = Some ba -> BR (c3_par k1) ba (c3_fs k1) (c3_tabs k1) (sf_hbuf (c3_s k1))) ->
  base_rel3 (ex_next st st1) k1 /\
  (dc_ss (ex_next st st1) <> ss_init -> ss_err (dc_ss (ex_next st st1)) = false ->
     SR gv (ex_next st st1) k1 \/ (dc_ss (ex_next st st1) = ss_restart /\ sf_stage (c3_s k1) = 0)) /\
  (forall ba, dc_bl (ex_next st st1) = Some ba -> BR (c3_par k1) ba (c3_fs k1) (c3_tabs k1) (sf_hbuf (c3_s k1))) /\
  ex_on3 SR (ex_next st st1) k1.
Proof.
  intros Hex Ess Eex Es Efs Et Hs0 Hb Hsr Hbr. unfold ex_next, st_next in *.
  destruct (ss_eq_dec (dc_ss st) ss_init) as [E|E].
  - split; [exact Hb | split; [exact Hsr | split; [exact Hbr |]]].
    apply (ex_on3_keep SR st st1 k k1 Hex Ess); [rewrite Eex; auto | exact Es | exact Efs | exact Et | left; exact E].
  - split; [exact Hb | split; [| split; [exact Hbr | apply ex_on3_noex; reflexivity]]].
    cbn [dc_ss set_ex]. intros _ Herr. right. split; [| exact Hs0].
    rewrite Ess in *. cbn [dc_ss set_ss] in *. unfold ss_next in *.
    destruct (ss_err (dc_ss st)) eqn:Ee; [rewrite Ee in Herr; discriminate | reflexivity].
Qed.

Lemma after_stage_refuse (res: dctx_st -> Z -> dctx_st -> Prop) (st: dctx_st) (r: Z) :
  dc_ss st <> ss_init -> is_error_code r = true -> after_stage res st r st.
Proof. intros E H. right. split; [exact E | left; auto]. Qed.

(* a context at a stage other than zdss_init is not before any stream *)
Lemma base_rel3_stage (st: dctx_st) (k: cst3) : base_rel3 st k -> sf_stage (c3_s k) <> 0 -> dc_ss st <> ss_init.
Proof. intros (_ & _ & _ & _ & _ & _ & [_ Hs] & _) Hn E. apply Hn. exact (proj1 (Hs E)). Qed.

Lemma ss_restart_not_init : ss_restart <> ss_init.
Proof. unfold ss_restart, ss_init. intros E. inversion E. Qed.

Lemma dc_bl_st_next (st: dctx_st) : dc_bl (st_next st) = dc_bl st.
Proof. unfold st_next. destruct (ss_eq_dec (dc_ss st) ss_init); reflexivity. Qed.

Lemma dc_par_st_next (st: dctx_st) : dc_par (st_next st) = dc_par st.
Proof. unfold st_next. destruct (ss_eq_dec (dc_ss st) ss_init); reflexivity. Qed.

Lemma dc_set_st_next (st: dctx_st) : dc_set (st_next st) = dc_set st.
Proof. unfold st_next. destruct (ss_eq_dec (dc_ss st) ss_init); reflexivity. Qed.

Lemma dc_dict_st_next (st: dctx_st) : dc_dict (st_next st) = dc_dict st.
Proof. unfold st_next. destruct (ss_eq_dec (dc_ss st) ss_init); reflexivity. Qed.

Lemma dc_ex_st_next (st: dctx_st) : dc_ex (st_next st) = dc_ex st.
Proof. unfold st_next. destruct (ss_eq_dec (dc_ss st) ss_init); reflexivity. Qed.

(* the context st_next st is related to k at stage 0 (but for the allocator's bound) *)
Lemma load_pre_next (st: dctx_st) (k: cst3) :
  base_rel3 st k -> sf_stage (c3_s k) = 0 -> dc_bl st = None -> load_pre (st_next st) k.
Proof.
  intros Hb Hs Hbl. unfold load_pre, st_next.
  destruct (ss_eq_dec (dc_ss st) ss_init) as [E|E].
  - destruct (base_rel3_mem _ _ Hb) as [Hm _]. rewrite Hm, set_mem_same.
    split; [exact Hb | split; [exact Hs | split; [exact Hbl | intros N; contradiction]]].
  - destruct Hb as (H1 & H2 & H3 & H4 & H5 & H5' & [H6a H6b] & H7 & [Hm1 [Hm2 Hm3]]).
    split; [| split; [exact Hs | split; [exact Hbl |]]].
    + unfold base_rel3, set_mem, set_ss; simpl.
      split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 |]. split; [exact H4 |]. split; [exact H5 |].
      split; [exact H5' |]. split.
      { unfold ss_next. destruct (ss_err (dc_ss st)) eqn:Ee.
        - split; [intros Hx; congruence | intros Hx; contradiction].
        - split; [intros _; exact (H6a eq_refl) | intros Hx; exfalso; exact (ss_restart_not_init Hx)]. }
      split; [rewrite Hbl; intros Hx; contradiction |].
      unfold mem_rel3; simpl. split; [reflexivity | split; [exact Hm2 | exact Hm3]].
    + simpl. unfold ss_next. destruct (ss_err (dc_ss st)) eqn:Ee; [intros _ Hx; congruence | auto].
Qed.

(* the streaming estimate grows with the window limit *)
Lemma dstream_size_mono (w w': Z) : w <= w' -> dstream_size w <= dstream_size w'.
Proof. unfold dstream_size. lia. Qed.

(* the context's allocator raised to cover the window limit w (at least the context's own) is a raise of the
   allocator of st_next st *)
Lemma cm_raised_next (st: dctx_st) (w: Z) :
  dp_wmax (dc_par st) <= w -> cm_raised (dc_mem (st_next st)) (cm_raise (dc_mem st) w).
Proof.
  intros Hw. unfold st_next. destruct (ss_eq_dec (dc_ss st) ss_init) as [E|E].
  - destruct (dc_mem st) as [m|]; simpl; [repeat split; lia | exact I].
  - unfold set_ss; simpl. destruct (dc_mem st) as [m|]; simpl; [| exact I].
    pose proof (dstream_size_mono _ _ Hw). repeat split; lia.
Qed.

(* the local DDict of a load holds at most its struct and its copy *)
Lemma local_held_load am pk b m t r d :
  load_res3 am pk b m t r d -> 0 <= local_held d <= sizeof t_ddict + Zlength b.
Proof.
  pose proof (Zlength_nonneg b). unfold load_res3. destruct (Zlength b =? 0).
  - intros [_ ->]. unfold local_held; simpl. destruct (eq_dec nullval nullval); simpl; lia.
  - intros [[_ [_ (q & buf & ores & Hq & _ & ->)]] | [_ ->]].
    + unfold local_held; simpl. destruct (EqDec_val q nullval) as [E|E]; [subst; contradiction |].
      unfold ddx_held, ddx_of3; simpl. destruct am; [| simpl; lia].
      destruct (ddx_copied _); simpl; lia.
    + unfold local_held; simpl. destruct (eq_dec nullval nullval); simpl; lia.
Qed.

(* a context's local DDict is of its allocator, also with a raised bound *)
Lemma local_mem_raise (am: option cmem) (w: Z) (d: dfields) : local_mem am d -> local_mem (cm_raise am w) d.
Proof.
  unfold local_mem. intros H E. destruct (H E) as [H1 H2]. split.
  - intros N. apply H1. intros N'. apply N. rewrite N'. reflexivity.
  - intros x buf Hx. exact (cm_same_trans _ _ _ (H2 x buf Hx) (cm_same_raise _ _)).
Qed.

(* DC3_of's relation after a load through the allocator om (the context's, maybe with a raised bound), the context's
   other blocks then holding h' bytes *)
Lemma load3_rel_any (SR: srel3) (gv: globals) (BR: blrel) (st0: dctx_st) (k0: cst3) (om: option cmem) (h': Z)
    (od: option dictref) (d': dfields) :
  load_pre st0 k0 ->
  (forall dr, od = Some dr -> not_ddict dr) -> dict_rel3_of od d' -> local_mem om d' ->
  mem_room (sf_with_held (sf_with_mem (c3_s k0) om) h') ->
  let k1 := c3_with_s k0 (sf_with_mem (c3_s k0) om) in
  let k' := c3_with_dict (c3_with_s k1 (sf_with_held (c3_s k1) h')) d' in
  let st' := set_dict (set_mem st0 om) od in
  base_rel3 st' k' /\
  (dc_ss st' <> ss_init -> ss_err (dc_ss st') = false ->
     SR gv st' k' \/ (dc_ss st' = ss_restart /\ sf_stage (c3_s k') = 0)) /\
  (forall ba, dc_bl st' = Some ba ->
     BR (c3_par k') ba (c3_fs k') (c3_tabs k') (sf_hbuf (c3_s k'))).
Proof.
  intros [[H1 [H2 [H3 [H4 [H5 [H5' [H6 [H7 H8]]]]]]]] [Hst [Hbl Hss]]] Hnd Hd Hlm Hroom k1 k' st'.
  split; [| split].
  - unfold base_rel3; simpl. split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 |].
    split; [left; exact Hd |].
    split.
    { intros dr q dd dd' Hdr Hs _. simpl in Hdr. specialize (Hnd dr Hdr). unfold not_ddict in Hnd.
      rewrite Hs in Hnd. contradiction. }
    split; [exact H5' |]. split; [exact H6 |]. split; [intros E; contradiction |].
    unfold mem_rel3; simpl. split; [reflexivity |]. split; [exact Hroom | exact Hlm].
  - simpl. intros E Herr. right. split; [exact (Hss E Herr) | exact Hst].
  - simpl. rewrite Hbl. discriminate.
Qed.

(* ... with the result r: the dictionary dr or (a memory error) none *)
Lemma load3_rel_any_r (SR: srel3) (gv: globals) (BR: blrel) (st0: dctx_st) (k0: cst3) (om: option cmem) (h': Z)
    (r: Z) (d': dfields) (dr: dictref) :
  load_pre st0 k0 -> not_ddict dr -> local_mem om d' ->
  mem_room (sf_with_held (sf_with_mem (c3_s k0) om) h') ->
  (r = 0 /\ dict_rel3_of (Some dr) d') \/ (r = err_code ZSTD_error_memory_allocation /\ d' = df_none) ->
  let k1 := c3_with_s k0 (sf_with_mem (c3_s k0) om) in
  let k' := c3_with_dict (c3_with_s k1 (sf_with_held (c3_s k1) h')) d' in
  let st' := if r =? 0 then set_dict (set_mem st0 om) (Some dr) else set_dict (set_mem st0 om) None in
  0 <= r <= Int64.max_unsigned /\
  base_rel3 st' k' /\
  (dc_ss st' <> ss_init -> ss_err (dc_ss st') = false ->
     SR gv st' k' \/ (dc_ss st' = ss_restart /\ sf_stage (c3_s k') = 0)) /\
  (forall ba, dc_bl st' = Some ba ->
     BR (c3_par k') ba (c3_fs k') (c3_tabs k') (sf_hbuf (c3_s k'))).
Proof.
  intros Hp Hnd Hlm Hroom Hr k1 k' st'.
  destruct Hr as [[-> Hd] | [-> ->]].
  - split; [rep_lia |]. subst st'. simpl Z.eqb. cbv iota.
    apply (load3_rel_any SR gv BR st0 k0 om h' (Some dr) d' Hp); auto.
    intros dr0 E; inversion E; subst; auto.
  - split; [compute; split; congruence |]. subst st'.
    replace (err_code ZSTD_error_memory_allocation =? 0) with false by reflexivity.
    apply (load3_rel_any SR gv BR st0 k0 om h' None df_none Hp); auto.
    + intros ? E; discriminate.
    + split; [reflexivity | left; reflexivity].
Qed.

(* the same for a context with the default allocator before any stream: only the dictionary changes *)
Lemma load3_rel_r (SR: srel3) (gv: globals) (BR: blrel) (st: dctx_st) (k: cst3) (r: Z) (d': dfields) (dr: dictref) :
  base_rel3 st k -> dc_mem st = None -> dc_ss st = ss_init -> dc_bl st = None -> not_ddict dr -> local_mem None d' ->
  (r = 0 /\ dict_rel3_of (Some dr) d') \/ (r = err_code ZSTD_error_memory_allocation /\ d' = df_none) ->
  ex_on3 SR st k ->
  let st' := if r =? 0 then set_dict st (Some dr) else set_dict st None in
  0 <= r <= Int64.max_unsigned /\
  base_rel3 st' (c3_with_dict k d') /\
  (dc_ss st' <> ss_init -> ss_err (dc_ss st') = false ->
     SR gv st' (c3_with_dict k d') \/ (dc_ss st' = ss_restart /\ sf_stage (c3_s (c3_with_dict k d')) = 0)) /\
  (forall ba, dc_bl st' = Some ba ->
     BR (c3_par (c3_with_dict k d')) ba (c3_fs (c3_with_dict k d')) (c3_tabs (c3_with_dict k d'))
        (sf_hbuf (c3_s (c3_with_dict k d')))) /\
  ex_on3 SR st' (c3_with_dict k d').
Proof.
  intros Hb Hmem Hss Hbl Hnd Hlm Hr Hex st'.
  assert (Hm := base_rel3_mem _ _ Hb). destruct Hm as [Hm1 [Hm2 _]].
  assert (Hst: sf_stage (c3_s k) = 0).
  { destruct Hb as (_ & _ & _ & _ & _ & _ & [_ Hs] & _). exact (proj1 (Hs Hss)). }
  assert (Hp: load_pre st k).
  { split; [| split; [exact Hst | split; [exact Hbl | intros E; contradiction]]].
    rewrite Hm1, Hmem, <- Hmem, set_mem_same. exact Hb. }
  rewrite Hmem in Hm1.
  pose proof (load3_rel_any_r SR gv BR st k None (sf_held (c3_s k)) r d' dr Hp Hnd Hlm) as X.
  rewrite <- Hm1, sf_with_mem_same, sf_with_held_same in X. rewrite Hm1 in X.
  specialize (X Hm2 Hr). cbv zeta in X.
  rewrite !c3_with_s_same, sf_with_held_same, c3_with_s_same in X.
  replace (set_mem st None) with st in X by (rewrite <- Hmem; symmetry; apply set_mem_same).
  destruct X as (X0 & X1 & X2 & X3). refine (conj X0 (conj X1 (conj X2 (conj X3 _)))).
  (* only the dictionary changes, before any stream *)
  subst st'. destruct (r =? 0);
    (apply (ex_on3_keep SR st _ k _ Hex); [reflexivity | intros e; exact e | reflexivity | reflexivity | reflexivity |
                                            left; exact Hss]).
Qed.

Lemma load_result_of st r dr :
  r = 0 \/ r = err_code ZSTD_error_memory_allocation ->
  load_result st (if r =? 0 then set_dict st (Some dr) else set_dict st None) r dr.
Proof.
  intros [-> | ->].
  - left. split; reflexivity.
  - right. split; [reflexivity |]. split; [reflexivity |]. right; reflexivity.
Qed.

End CM_Load3Post_1.
