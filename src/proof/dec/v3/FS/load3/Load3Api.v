(* FS3 load3: ZSTD_DCtx_loadDictionary_byReference, ZSTD_DCtx_loadDictionary, ZSTD_DCtx_refPrefix against the API
   (port of v2 body_FS_load.v).  ZSTD_DCtx_loadDictionary is specified after any use and for any
   allocator: zstd refuses it while a frame is being streamed; else the context's own allocator gets a raised bound
   (ghost: CMem.CM_mono) with room for the copy and, beside it, for the largest stream buffers *)
Require Import Zstd.proof.dec.v3.FS.FSOblig3.
Require Import Zstd.proof.dec.v3.FS.load3.Load3Lift Zstd.proof.dec.v3.FS.load3.Load3Split Zstd.proof.dec.v3.FS.load3.Load3Post
  Zstd.proof.dec.v3.FS.load3.Load3Adv.
Local Open Scope logic.

Section CM_Load3Api_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Section Api.
Variables (DENT : dent_pred) (TABS : tabs_pred) (SR : srel3) (BR : blrel).

Definition G_ldadv : funspecs := [ZSTD_DCtx_loadDictionary_advanced_spec3 DENT TABS].
Definition G_rpadv : funspecs := [ZSTD_DCtx_refPrefix_advanced_spec3 DENT TABS].

Lemma body_loadDictionary_byReference3_small :
  body_ok G_ldadv (ZSTD_DCtx_loadDictionary_byReference_spec (DC3x DENT TABS SR BR)).
Proof.
  exists f_ZSTD_DCtx_loadDictionary_byReference; split; [reflexivity | split; [reflexivity | ]].
  unfold G_ldadv.
  start_function.
  unfold DC3x, DC3_of. Intros kk.
  match goal with Hb0: base_rel3 _ _ |- _ => rename Hb0 into Hb end.
  match goal with Hs0: dc_ss _ = ss_init |- _ => rename Hs0 into Hss end.
  match goal with Hx: forall ba, dc_bl st = Some ba -> _ |- _ => rename Hx into Hbr end.
  match goal with Hx: ex_on3 SR st kk |- _ => rename Hx into Hex end.
  match goal with Hx: dc_bl st = None |- _ => rename Hx into Hbl end.
  match goal with Hx: dc_mem st = None |- _ => rename Hx into Hmem end.
  assert (Hstage: sf_stage (c3_s kk) = 0)
    by (destruct Hb as (_ & _ & _ & _ & _ & _ & [_ Hs] & _); exact (proj1 (Hs Hss))).
  assert (Hsm: sf_mem (c3_s kk) = None) by (destruct (base_rel3_mem _ _ Hb) as [E _]; rewrite E; assumption).
  assert (Hlm: local_mem (sf_mem (c3_s kk)) (c3_dict kk)) by (destruct (base_rel3_mem _ _ Hb) as [_ [_ E]]; exact E).
  assert (Hroom: sf_stage (c3_s kk) = 0 -> cm_room (sf_mem (c3_s kk)) (sf_given (c3_s kk)) (sizeof t_ddict + Zlength b))
    by (intros _; rewrite Hsm; exact I).
  forward_call (W, gv, d, kk, sh, p, b, 1, 0).
  Intros vret. destruct vret as [r k']. simpl fst in *; simpl snd in *.
  rewrite Hsm in Hlm.
  match goal with Hx: load_int_res _ _ _ _ _ _ _ |- _ =>
    destruct (load_int_res_none _ _ _ _ _ _ _ Hstage Hsm Hlm Hx) as [d' [HL ->]] end.
  pose proof (load_res3_local _ _ _ _ _ _ _ HL) as Hlm'.
  forward.
  set (dr := {| dr_src := DSRef p; dr_raw := false; dr_once := false; dr_bytes := b |}).
  assert (Hr: (r = 0 /\ dict_rel3_of (Some dr) d') \/ (r = err_code ZSTD_error_memory_allocation /\ d' = df_none)).
  { unfold load_res3 in HL. unfold dict_rel3_of; simpl.
    destruct (Zlength b =? 0) eqn:E.
    - left. destruct HL as [-> ->]. simpl. auto.
    - destruct HL as [[-> [_ [q [buf [ores [Hq [Hbuf ->]]]]]]] | [-> ->]]; [left | right]; auto.
      rewrite <- Hbuf by auto. simpl. split; auto. split; auto. split; auto. split; auto.
      exists ores, None. reflexivity. }
  assert (Hr01: r = 0 \/ r = err_code ZSTD_error_memory_allocation) by (destruct Hr as [[? _]|[? _]]; auto).
  pose proof (load3_rel_r SR gv BR st kk r d' dr Hb Hmem Hss Hbl I Hlm' Hr Hex) as Hrel. cbv zeta in Hrel.
  Exists r (if r =? 0 then set_dict st (Some dr) else set_dict st None).
  unfold DC3x, DC3_of. Exists (c3_with_dict kk d').
  pose proof (load_result_of st r dr Hr01).
  entailer!.
  all: try exact (proj2 Hrel).
Qed.

(* the bound a load by copy of b raises the context's own allocator to: room for the DDict next to what the context
   holds, and for the largest stream buffers next to that (mem_room) *)
Definition load_w (s: sfields) (b: list Z) : Z :=
  sf_given s + sizeof t_ddict + Zlength b + dstream_size (2 ^ 31) + 2 ^ 31.

Lemma body_loadDictionary3_small :
  body_ok G_ldadv (ZSTD_DCtx_loadDictionary_spec (DC3x DENT TABS SR BR)).
Proof.
  exists f_ZSTD_DCtx_loadDictionary; split; [reflexivity | split; [reflexivity | ]].
  unfold G_ldadv.
  start_function.
  unfold DC3x, DC3_of. Intros kk.
  match goal with Hb0: base_rel3 _ _ |- _ => rename Hb0 into Hb end.
  match goal with Hx: forall ba, dc_bl st = Some ba -> _ |- _ => rename Hx into Hbr end.
  match goal with Hx: ex_on3 SR st kk |- _ => rename Hx into Hex end.
  match goal with Hx: dc_bl st = None |- _ => rename Hx into Hbl end.
  destruct (base_rel3_mem _ _ Hb) as (Hm1 & Hm2 & Hm3).
  assert_PROP (0 <= sf_held (c3_s kk) - local_held (c3_dict kk) /\ 0 <= sf_inSize (c3_s kk) /\
               0 <= sf_outSize (c3_s kk) /\ par_ok (c3_par kk)) as Hk.
  { rewrite ctx_rep3_split. Intros.
    sep_apply (hset_rep_hb (sf_mem (c3_s kk)) (c3_sp kk) (c3_set kk) (sf_held (c3_s kk) - local_held (c3_dict kk))).
    sep_apply (ctx_rest3k_props TABS gv d kk). entailer!. }
  destruct Hk as (Hhb & Hin & Hout & Hpar).
  pose proof (local_held_nonneg (c3_dict kk)) as Hlh.
  assert (Hds: 0 <= dstream_size (2 ^ 31)) by (unfold dstream_size, ZSTD_BLOCKSIZE_MAX; rewrite dctx_size_eq; lia).
  destruct (Z.eq_dec (sf_stage (c3_s kk)) 0) as [Hs0 | Hs0].
  2: { (* a frame is being streamed: refused *)
    assert (Hroom: sf_stage (c3_s kk) = 0 -> cm_room (sf_mem (c3_s kk)) (sf_given (c3_s kk)) (sizeof t_ddict + Zlength b))
      by (intros E; contradiction).
    forward_call (W, gv, d, kk, sh, p, b, 0, 0).
    Intros vret. destruct vret as [r k']. simpl fst in *; simpl snd in *.
    match goal with Hx: load_int_res _ _ _ _ _ _ _ |- _ => destruct Hx as [[_ [He ->]] | [E _]]; [| contradiction] end.
    forward.
    Exists r st. unfold DC3x, DC3_of. Exists kk.
    pose proof (after_stage_refuse
      (fun st0 r0 st1 => exists om, cm_raised (dc_mem st0) om /\
         load_result (set_mem st0 om) st1 r0 {| dr_src := DSOwn; dr_raw := false; dr_once := false; dr_bytes := b |})
      st r (base_rel3_stage _ _ Hb Hs0) He).
    entailer!. }
  (* between two frames or before any stream: the context's own allocator raised for the copy *)
  assert (Hw: dp_wmax (dc_par st) <= load_w (c3_s kk) b /\ sf_given (c3_s kk) + sizeof t_ddict + Zlength b + dstream_size (2 ^ 31) <= dstream_size (load_w (c3_s kk) b)).
  { destruct Hb as (_ & Hpk & _). rewrite <- Hpk. destruct Hpar as (_ & _ & _ & Hwm & _).
    pose proof (Zlength_nonneg b). unfold load_w, dstream_size, sf_given, ZSTD_BLOCKSIZE_MAX in *.
    rewrite dctx_size_eq in *. simpl sizeof in *. lia. }
  destruct Hw as [Hw1 Hw2].
  sep_apply (ctx_rep3_raise DENT TABS gv d kk (load_w (c3_s kk) b)).
  set (w := load_w (c3_s kk) b) in *.
  assert (Hroom: sf_stage (c3_s (c3_raise kk w)) = 0 ->
                 cm_room (sf_mem (c3_s (c3_raise kk w))) (sf_given (c3_s (c3_raise kk w))) (sizeof t_ddict + Zlength b)).
  { intros _. unfold c3_raise, c3_with_s, sf_with_mem, sf_given in *; simpl.
    destruct (sf_mem (c3_s kk)) as [m|]; simpl; [| exact I].
    rewrite dctx_size_eq in *. simpl sizeof in *. pose proof (Zlength_nonneg b). lia. }
  assert (Hlm1: local_mem (sf_mem (c3_s (c3_raise kk w))) (c3_dict (c3_raise kk w)))
    by (simpl; apply local_mem_raise; exact Hm3).
  forward_call (W, gv, d, c3_raise kk w, sh, p, b, 0, 0).
  Intros vret. destruct vret as [r k']. simpl fst in *; simpl snd in *.
  match goal with Hx: load_int_res _ _ _ _ _ _ _ |- _ =>
    destruct (load_int_res_stage0 _ _ _ _ _ _ _ (Hs0 : sf_stage (c3_s (c3_raise kk w)) = 0) Hx) as [d' [HL ->]] end.
  forward.
  set (om := cm_raise (sf_mem (c3_s kk)) w) in *.
  set (dr := {| dr_src := DSOwn; dr_raw := false; dr_once := false; dr_bytes := b |}).
  assert (Hr: (r = 0 /\ dict_rel3_of (Some dr) d') \/ (r = err_code ZSTD_error_memory_allocation /\ d' = df_none)).
  { unfold load_res3 in HL. unfold dict_rel3_of; simpl.
    destruct (Zlength b =? 0) eqn:E.
    - left. destruct HL as [-> ->]. auto.
    - destruct HL as [[-> [_ [q [buf [ores [Hq [_ ->]]]]]]] | [-> ->]]; [left | right]; auto.
      split; auto. split; auto. exists buf, ores, om. unfold ddx_of3. rewrite E. simpl. auto. }
  assert (Hr01: r = 0 \/ r = err_code ZSTD_error_memory_allocation) by (destruct Hr as [[? _]|[? _]]; auto).
  pose proof (load_res3_local _ _ _ _ _ _ _ HL) as Hlm'.
  pose proof (local_held_load _ _ _ _ _ _ _ HL) as Hld.
  assert (Hp: load_pre (st_next st) kk) by (apply load_pre_next; auto).
  set (h' := sf_held (c3_s kk) - local_held (c3_dict kk) + local_held d').
  assert (Hroom': mem_room (sf_with_held (sf_with_mem (c3_s kk) om) h')).
  { unfold mem_room, h' in *; simpl in *. subst om.
    destruct (sf_mem (c3_s kk)) as [m|] eqn:Em; simpl in *.
    - right. unfold sf_given in Hw2. rewrite dctx_size_eq in Hw2. lia.
    - rewrite (local_held_none _ Hm3), (local_held_none _ Hlm'). lia. }
  pose proof (load3_rel_any_r SR gv BR (st_next st) kk om h' r d' dr Hp I Hlm' Hroom' Hr) as Hrel. cbv zeta in Hrel.
  assert (Hres: after_stage (fun st0 r0 st1 => exists om, cm_raised (dc_mem st0) om /\ load_result (set_mem st0 om) st1 r0 dr)
                  st r (ex_next st (if r =? 0 then set_dict (set_mem (st_next st) om) (Some dr)
                                    else set_dict (set_mem (st_next st) om) None))).
  { apply after_stage_next. exists om. split; [subst om; rewrite Hm1; apply cm_raised_next; exact Hw1 |].
    apply load_result_of; exact Hr01. }
  set (st1 := if r =? 0 then set_dict (set_mem (st_next st) om) (Some dr) else set_dict (set_mem (st_next st) om) None)
    in Hres, Hrel.
  set (k1 := c3_with_dict (c3_with_s (c3_with_s kk (sf_with_mem (c3_s kk) om))
                                     (sf_with_held (sf_with_mem (c3_s kk) om) h')) d').
  destruct Hrel as (Hrange & X1 & X2 & X3).
  assert (Hrel: base_rel3 (ex_next st st1) k1 /\
    (dc_ss (ex_next st st1) <> ss_init -> ss_err (dc_ss (ex_next st st1)) = false ->
       SR gv (ex_next st st1) k1 \/ (dc_ss (ex_next st st1) = ss_restart /\ sf_stage (c3_s k1) = 0)) /\
    (forall ba, dc_bl (ex_next st st1) = Some ba -> BR (c3_par k1) ba (c3_fs k1) (c3_tabs k1) (sf_hbuf (c3_s k1))) /\
    ex_on3 SR (ex_next st st1) k1).
  { apply (ex_next_dc3 SR gv BR st st1 kk k1 Hex); try exact X1; try exact X2; try exact X3; try exact Hs0;
      subst st1; try (destruct (r =? 0); reflexivity).
    destruct (r =? 0); exact (dc_ex_st_next st). }
  Exists r (ex_next st st1).
  unfold DC3x, DC3_of.
  Exists k1.
  entailer!.
  all: try exact Hrel.
  apply derives_refl.
Qed.

Lemma body_refPrefix3_small :
  body_ok G_rpadv (ZSTD_DCtx_refPrefix_spec (DC3x DENT TABS SR BR)).
Proof.
  exists f_ZSTD_DCtx_refPrefix; split; [reflexivity | split; [reflexivity | ]].
  unfold G_rpadv.
  start_function.
  unfold DC3x, DC3_of. Intros kk.
  match goal with Hb0: base_rel3 _ _ |- _ => rename Hb0 into Hb end.
  match goal with Hs0: dc_ss _ = ss_init |- _ => rename Hs0 into Hss end.
  match goal with Hx: forall ba, dc_bl st = Some ba -> _ |- _ => rename Hx into Hbr end.
  match goal with Hx: ex_on3 SR st kk |- _ => rename Hx into Hex end.
  match goal with Hx: dc_bl st = None |- _ => rename Hx into Hbl end.
  match goal with Hx: dc_mem st = None |- _ => rename Hx into Hmem end.
  assert (Hstage: sf_stage (c3_s kk) = 0)
    by (destruct Hb as (_ & _ & _ & _ & _ & _ & [_ Hs] & _); exact (proj1 (Hs Hss))).
  assert (Hsm: sf_mem (c3_s kk) = None) by (destruct (base_rel3_mem _ _ Hb) as [E _]; rewrite E; assumption).
  assert (Hlm: local_mem (sf_mem (c3_s kk)) (c3_dict kk)) by (destruct (base_rel3_mem _ _ Hb) as [_ [_ E]]; exact E).
  forward_call (W, gv, d, kk, sh, p, b, 1).
  Intros vret. destruct vret as [r d']. simpl fst in *; simpl snd in *.
  match goal with Hl: exists d0, load_res3 _ _ _ _ _ _ d0 /\ _ |- _ => rename Hl into HL end.
  assert (Hlm': local_mem None d')
    by (destruct HL as [d0 [Hd0 ->]]; pose proof (load_res3_local _ _ _ _ _ _ _ Hd0) as Hl0;
        destruct (r =? 0); exact Hl0).
  forward.
  set (dr := {| dr_src := DSRef p; dr_raw := true; dr_once := true; dr_bytes := b |}).
  assert (Hr: (r = 0 /\ dict_rel3_of (Some dr) d') \/ (r = err_code ZSTD_error_memory_allocation /\ d' = df_none)).
  { destruct HL as [d0 [Hl ->]]. unfold load_res3 in Hl. unfold dict_rel3_of; simpl.
    destruct (Zlength b =? 0) eqn:E.
    - left. destruct Hl as [-> ->]. simpl. auto.
    - destruct Hl as [[-> [_ [q [buf [ores [Hq [Hbuf ->]]]]]]] | [-> ->]]; [left | right]; auto.
      rewrite <- Hbuf by auto. simpl. split; auto. split; auto. split; auto. split; auto.
      exists ores, None. reflexivity. }
  assert (Hr01: r = 0 \/ r = err_code ZSTD_error_memory_allocation) by (destruct Hr as [[? _]|[? _]]; auto).
  pose proof (load3_rel_r SR gv BR st kk r d' dr Hb Hmem Hss Hbl I Hlm' Hr Hex) as Hrel. cbv zeta in Hrel.
  Exists r (if r =? 0 then set_dict st (Some dr) else set_dict st None).
  unfold DC3x, DC3_of. Exists (c3_with_dict kk d').
  pose proof (load_result_of st r dr Hr01).
  entailer!.
  all: try exact (proj2 Hrel).
Qed.

End Api.

Lemma body_loadDictionary_byReference3 :
  FS3_body (fun DENT TABS SR BR => ZSTD_DCtx_loadDictionary_byReference_spec (DC3x DENT TABS SR BR)).
Proof.
  intros DENT TABS SR BR HD HT.
  apply (load3_lift (G_ldadv DENT TABS)); [unfold G_ldadv; load3_in | apply body_loadDictionary_byReference3_small].
Qed.

Lemma body_loadDictionary3 :
  FS3_body (fun DENT TABS SR BR => ZSTD_DCtx_loadDictionary_spec (DC3x DENT TABS SR BR)).
Proof.
  intros DENT TABS SR BR HD HT.
  apply (load3_lift (G_ldadv DENT TABS)); [unfold G_ldadv; load3_in | apply body_loadDictionary3_small].
Qed.

Lemma body_refPrefix3 :
  FS3_body (fun DENT TABS SR BR => ZSTD_DCtx_refPrefix_spec (DC3x DENT TABS SR BR)).
Proof.
  intros DENT TABS SR BR HD HT.
  apply (load3_lift (G_rpadv DENT TABS)); [unfold G_rpadv; load3_in | apply body_refPrefix3_small].
Qed.

End CM_Load3Api_1.
