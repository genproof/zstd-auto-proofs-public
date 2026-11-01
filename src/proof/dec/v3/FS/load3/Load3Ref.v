(* FS3 load3: ZSTD_DCtx_refDDict with the DDict set (refMultipleDDicts) (port of v2 body_refDDict_int).  Any stage (zstd
   refuses it while a frame is being streamed), any allocator: the old local
   DDict is freed and the set is created and grown through the context's allocator, whose bytes for the set the
   context's representation counts (FSRepC.sf_held) *)
Require Import Zstd.proof.dec.v3.FS.FSOblig3.
Require Import Zstd.proof.dec.v3.FS.FSLift3.
Require Import Zstd.proof.dec.v3.FS.load3.Load3Lift Zstd.proof.dec.v3.FS.load3.Load3Split Zstd.proof.dec.v3.FS.load3.Load3Adv.
Local Open Scope logic.

Section CM_Load3Ref_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Definition G_ref (DENT: dent_pred) : funspecs :=
  [ZSTD_clearDict_spec DENT; ZSTD_createDDictHashSet_spec; ZSTD_DDictHashSet_addDDict_spec; ERR_isError_spec].

Lemma set_add_nonnil l q dd : set_add l q dd <> nil.
Proof.
  unfold set_add. destruct (existsb _ l) eqn:E.
  - destruct l; [discriminate | simpl; discriminate].
  - destruct l; simpl; discriminate.
Qed.

Lemma veqb_ptr q : isptr q -> veqb q nullval = false.
Proof. intros H. unfold veqb. destruct (Val.eq q nullval); [subst; contradiction | reflexivity]. Qed.

Lemma pon_isptr v : is_pointer_or_null v -> v <> nullval -> isptr v.
Proof. intros H1 H2. destruct v; simpl in *; try contradiction; auto. subst. contradiction. Qed.

Lemma ddid_valid q id db : ddid q id db |-- valid_pointer q.
Proof. unfold ddid. Intros. apply sepcon_valid_pointer1. apply field_at_valid_ptr0; auto; reflexivity. Qed.

Lemma veqb_null : veqb nullval nullval = true.
Proof. unfold veqb. destruct (Val.eq nullval nullval); [reflexivity | congruence]. Qed.

(* the bytes of a set of the default allocator: none *)
Lemma hset_rep_none_hb am sp l hb : hset_rep am sp l hb |-- !! (am = None -> hb = 0).
Proof.
  unfold hset_rep. destruct (eq_dec sp nullval).
  - entailer!.
  - Intros tp tbl. entailer!. match goal with Hx: am = None |- _ => rewrite Hx end. reflexivity.
Qed.

Lemma hset_at_hb am sp l hb : hset_at am sp l hb |-- !! (0 <= hb /\ (am = None -> hb = 0)).
Proof.
  unfold hset_at. Intros tbl. apply prop_right. subst hb. pose proof (Zlength_nonneg tbl).
  destruct am; simpl; split; try lia; try discriminate; try (unfold sizeof, t_hset; simpl; lia).
Qed.

(* the bytes of a new set *)
Lemma set_bytes_new am : 0 <= set_bytes am 64 <= set_new_bytes.
Proof. unfold set_bytes, set_new_bytes. destruct am; simpl; lia. Qed.

(* an expansion at most doubles the set's bytes *)
Lemma set_grow_le hb : 0 <= hb -> 0 <= set_grow hb <= 2 * hb.
Proof. unfold set_grow. assert (0 <= sizeof t_hset) by (simpl; lia). lia. Qed.

(* room for n' <= n bytes from h' <= h *)
Lemma cm_room_le2 (am: option cmem) (h h' n n': Z) :
  cm_room am h n -> 0 <= h' <= h -> 0 <= n' <= n -> cm_room am h' n'.
Proof. destruct am as [m|]; simpl; [lia | auto]. Qed.

(* room for n' bytes from h' when h' + n' <= h + n *)
Lemma cm_room_sum (am: option cmem) (h h' n n': Z) :
  cm_room am h n -> 0 <= h' -> 0 <= n' -> h' + n' <= h + n -> cm_room am h' n'.
Proof. destruct am as [m|]; simpl; [lia | auto]. Qed.

(* do { body } while (0): the loop invariant is the current precondition *)
Ltac dw0 tac :=
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end;
  [ apply ENTAIL_refl | tac | forward; apply ENTAIL_refl | abbreviate_semax ].
Ltac dw0_skip := dw0 ltac:(forward; apply ENTAIL_refl).
Ltac dw0_if0 := dw0 ltac:(forward_if; [contradiction | forward; apply ENTAIL_refl]).

Lemma body_refDDict_int3_small DENT TABS :
  body_ok (G_ref DENT) (ZSTD_DCtx_refDDict_int_spec3 DENT TABS).
Proof.
  exists f_ZSTD_DCtx_refDDict; split; [reflexivity | split; [reflexivity | ]].
  unfold G_ref.
  start_function.
  rewrite ctx_rep3_split. Intros.
  assert_PROP (0 <= sf_held (c3_s k) - local_held (c3_dict k)) as Hhb by (sep_apply hset_rep_hb; entailer!).
  assert_PROP (sf_mem (c3_s k) = None -> sf_held (c3_s k) - local_held (c3_dict k) = 0) as Hhn
    by (sep_apply hset_rep_none_hb; entailer!).
  assert_PROP (Int.min_signed <= sf_stage (c3_s k) <= Int.max_signed /\ 0 <= sf_inSize (c3_s k) /\
               0 <= sf_outSize (c3_s k) /\ cmem_ok (sf_mem (c3_s k)) /\ par_ok (c3_par k)) as Hrest
    by (sep_apply (ctx_rest3k_props TABS gv p k); entailer!).
  destruct Hrest as (Hsr & Hin & Hout & Hcm & Hpar).
  pose proof (local_held_nonneg (c3_dict k)) as Hlh.
  match goal with Hx: local_mem _ _ |- _ => rename Hx into Hlm end.
  match goal with Hx: sf_stage (c3_s k) = 0 -> q <> nullval -> _ |- _ => rename Hx into Hroom end.
  freeze FR := (cfg_fmt _ _) (ctx_rest3k _ _ _ _).
  match goal with |- semax _ (PROPx ?Pr (LOCALx ?L (SEPx ?S))) _ _ =>
    forward_loop (PROPx Pr (LOCALx L (SEPx S))) break: (PROPx ((sf_stage (c3_s k) = 0) :: Pr) (LOCALx L (SEPx S))) end.
  { entailer!. }
  { forward. forward_if.
    { (* a frame is being streamed: stage_wrong, nothing changed *)
      dw0_skip. dw0_if0. dw0_skip. dw0_skip.
      forward.
      Exists (Int64.unsigned (Int64.repr (-60))) k.
      thaw FR. rewrite (ctx_rep3_split DENT TABS gv p k).
      entailer!.
      split; [ | rewrite Int64.repr_unsigned; reflexivity].
      left. split; [intros E; rewrite E in *; contradiction | split; [reflexivity | reflexivity]]. }
    { forward. entailer!. } }
  Intros.
  match goal with Hx: sf_stage (c3_s k) = 0 |- _ => rename Hx into Hst0 end.
  specialize (Hroom Hst0).
  assert (Hgv: 0 <= sf_given (c3_s k) - local_held (c3_dict k)) by (unfold sf_given; rewrite dctx_size_eq; lia).
  replace (sf_given (c3_s k)) with ((sf_given (c3_s k) - local_held (c3_dict k)) + local_held (c3_dict k)) by lia.
  forward_call (gv, p, c3_dict k, sf_mem (c3_s k), sf_given (c3_s k) - local_held (c3_dict k)).
  unfold dgroup. Intros.
  cbn [df_local df_ddict df_uses df_lx df_none].
  (* the context with the dictionary fields d and the set sp l of h bytes *)
  set (hbset := sf_held (c3_s k) - local_held (c3_dict k)) in *.
  match goal with Hx: q = nullval \/ _ |- _ => destruct Hx as [Hq | [Hq Hw]] end.
  - subst q.
    unfold MORE_COMMANDS, abbreviate. apply semax_if_seq.
    forward_if. { exfalso. auto. }
    forward.
    Exists 0 (c3_with_set (c3_with_dict (c3_with_s k (sf_with_held (c3_s k) hbset)) df_none) (c3_sp k) (c3_set k)).
    rewrite veqb_null. simpl andb. cbv iota.
    thaw FR. rewrite (ctx_rep3_split DENT TABS gv p (c3_with_set _ _ _)).
    rewrite ctx_rest3k_with_set, ctx_rest3k_with_dict, ctx_rest3k_with_held.
    unfold dgroup, local_rep; cbn [c3_with_set c3_with_dict c3_with_s c3_dict c3_s c3_par c3_sp c3_set
                                  df_local df_ddict df_uses df_lx df_none sf_mem sf_held sf_with_held].
    rewrite sf_given_with_held.
    replace (local_held df_none) with 0 by reflexivity.
    replace (sf_given (c3_s k) - sf_held (c3_s k) + hbset) with (sf_given (c3_s k) - local_held (c3_dict k))
      by (subst hbset; lia).
    rewrite Z.sub_0_r.
    rewrite if_true by auto.
    entailer!.
    right. split; [exact Hst0 |]. exists (c3_sp k), (c3_set k), hbset.
    split; [unfold refddict_res3; rewrite veqb_null; simpl; auto |].
    split; [unfold hbset, set_new_bytes in *; simpl sizeof in *; lia |]. split; [exact Hhn |]. split; [intros _; reflexivity |].
    rewrite if_true by auto. reflexivity.
  - (* a DDict *)
    assert (Hwv: pws_pred W * (if (negb (veqb q nullval) && (dp_multi (c3_par k) =? 1))%bool
                                then set_ids (c3_set k) * ddid q (dd_id dd) (ddb dd) else emp)
                  |-- weak_valid_pointer q).
    { destruct Hw as [Hm1 | Hw].
      - rewrite (veqb_ptr q Hq), Hm1. simpl andb. cbv iota.
        apply derives_trans with (ddid q (dd_id dd) (ddb dd) * TT); [cancel |].
        apply sepcon_weak_valid_pointer1. eapply derives_trans; [apply ddid_valid | apply valid_pointer_weak].
      - apply sepcon_weak_valid_pointer1. exact Hw. }
    assert (Hqn: q <> nullval) by (intros E; subst q; exact Hq).
    specialize (Hroom Hqn).
    unfold MORE_COMMANDS, abbreviate. apply semax_if_seq.
    forward_if.
    { destruct q; try contradiction. entailer!.
      Transparent denote_tc_test_eq. unfold denote_tc_test_eq; simpl. Opaque denote_tc_test_eq.
      apply andp_right; [apply prop_right; reflexivity | ].
      match type of Hwv with ?A |-- _ =>
        eapply derives_trans; [ | apply (sepcon_weak_valid_pointer1 A TT); exact Hwv ] end.
      cancel. }
    2: { exfalso. subst q. exact Hq. }
    forward. forward. forward.
    rewrite (veqb_ptr q Hq). simpl negb. cbv iota beta.
    destruct Hpar as [_ [_ [_ [_ Hm]]]].
    destruct Hm as [Hm | Hm].
    + (* refMultipleDDicts off *)
      rewrite Hm. simpl andb. cbv iota.
      try (unfold MORE_COMMANDS, abbreviate); apply semax_if_seq.
      forward_if. { exfalso. rewrite Hm in *. discriminate. }
      forward.
      Exists 0 (c3_with_set (c3_with_dict (c3_with_s k (sf_with_held (c3_s k) hbset)) (ddict_ref_fields q))
                            (c3_sp k) (c3_set k)).
      rewrite (veqb_ptr q Hq), Hm. simpl andb. cbv iota.
      thaw FR. rewrite (ctx_rep3_split DENT TABS gv p (c3_with_set _ _ _)).
      rewrite ctx_rest3k_with_set, ctx_rest3k_with_dict, ctx_rest3k_with_held.
      unfold dgroup, local_rep; cbn [c3_with_set c3_with_dict c3_with_s c3_dict c3_s c3_par c3_sp c3_set
                                    ddict_ref_fields df_local df_ddict df_uses df_lx sf_mem sf_held sf_with_held].
      rewrite sf_given_with_held.
      replace (local_held (ddict_ref_fields q)) with 0 by reflexivity.
      replace (sf_given (c3_s k) - sf_held (c3_s k) + hbset) with (sf_given (c3_s k) - local_held (c3_dict k))
        by (subst hbset; lia).
      rewrite Z.sub_0_r.
      rewrite if_true by auto. rewrite ?Hm.
      entailer!.
      right. split; [exact Hst0 |]. exists (c3_sp k), (c3_set k), hbset.
      split; [unfold refddict_res3; rewrite ?(veqb_ptr q Hq), ?Hm; simpl; auto |].
      split; [unfold hbset, set_new_bytes in *; simpl sizeof in *; lia |]. split; [exact Hhn |]. split; [intros E; contradiction |].
      rewrite if_false by auto. reflexivity.
    + (* refMultipleDDicts on: the set *)
      rewrite Hm. simpl andb. cbv iota.
      match goal with Hx: q <> nullval -> dp_multi (c3_par k) = 1 -> _ |- _ => destruct (Hx Hqn Hm) as [Hnin Hlen] end.
      try (unfold MORE_COMMANDS, abbreviate); apply semax_if_seq.
      forward_if; [ | exfalso; rewrite Hm in *; auto ].
      Intros.
      freeze FR2 := (field_at _ _ (DOT _ddictLocal) _ _) (field_at _ _ (DOT _ddict) _ _)
        (field_at _ _ (DOT _dictUses) _ _) (local_rep _ _ _ _) (pws_pred _) (field_at _ _ (DOT _streamStage) _ _)
        (zstd_globals _) (field_at _ _ (DOT _refMultipleDDicts) _ _).
      assert_PROP (is_pointer_or_null (c3_sp k)) as Hspn.
      { unfold hset_rep. destruct (eq_dec (c3_sp k) nullval) as [E|E]; [rewrite E; entailer! |].
        Intros tp tbl. entailer!. }
      forward.
      assert_PROP (field_compatible t_dctx (DOT _customMem) p) as Hfc by entailer!.
      rewrite (field_at_data_at Ews t_dctx (DOT _customMem)).
      (* the context's allocator besides the set: the context and the stream buffer *)
      set (base := sf_given (c3_s k) - sf_held (c3_s k)).
      assert (Hbase: 0 <= base /\ base + sf_held (c3_s k) = sf_given (c3_s k))
        by (subst base; unfold sf_given; rewrite dctx_size_eq; lia).
      replace (sf_given (c3_s k) - local_held (c3_dict k)) with (base + hbset) by (subst base hbset; lia).
      forward_if (EX sp1: val, EX hbs: Z,
        PROP (isptr sp1; c3_set k <> nil -> sp1 = c3_sp k; c3_sp k <> nullval -> sp1 = c3_sp k;
              c3_set k <> nil -> hbs = hbset; 0 <= hbs <= set_new_bytes + sf_held (c3_s k))
        LOCAL (gvars gv; temp _dctx p; temp _ddict q)
        SEP (mem_mgr gv; FRZL FR2; FRZL FR;
             data_at Ews (nested_field_type t_dctx (DOT _customMem)) (cmem_v (sf_mem (c3_s k)))
               (field_address t_dctx (DOT _customMem) p);
             cm_have (sf_mem (c3_s k)) (base + hbs);
             field_at Ews t_dctx (DOT _ddictSet) sp1 p; hset_at (sf_mem (c3_s k)) sp1 (c3_set k) hbs;
             set_ids (c3_set k); ddid q (dd_id dd) (ddb dd)))%assert.
      { destruct (eq_dec (c3_sp k) nullval) as [Hsp | Hsp]; [rewrite Hsp; entailer! |].
        rewrite (hset_rep_at _ _ _ _ Hsp). unfold hset_at, hset_tbl. Intros tbl tp. entailer!. }
      { (* no set yet: create it *)
        match goal with Hx: c3_sp k = nullval |- _ => rename Hx into Hsp end.
        unfold hset_rep at 1. rewrite if_true by auto. Intros.
        match goal with Hl: c3_set k = nil |- _ => rename Hl into Hnil end.
        match goal with Hl: hbset = 0 |- _ => rename Hl into Hb0 end.
        forward_call (gv, Ews, field_address t_dctx (DOT _customMem) p, sf_mem (c3_s k), base + hbset).
        { apply (cm_room_le2 _ _ _ _ _ Hroom); unfold set_new_bytes; simpl sizeof; lia. }
        Intros sp'.
        forward. forward.
        destruct (eq_dec sp' nullval) as [Hsp' | Hsp'].
        - subst sp'.
          forward_if; [ | exfalso; auto ].
          match goal with |- semax _ ?P _ _ =>
            forward_loop P continue: (FF: environ -> mpred) break: (FF: environ -> mpred) end.
          { apply ENTAIL_refl. }
          { dw0_skip. dw0_if0. dw0_skip. dw0_skip.
            forward.
            rewrite Hb0. subst base.
            Exists (err_code ZSTD_error_memory_allocation)
              (c3_with_set (c3_with_dict (c3_with_s k (sf_with_held (c3_s k) 0)) (ddict_ref_fields q))
                           (c3_sp k) (c3_set k)).
            rewrite (veqb_ptr q Hq), Hm. simpl andb. cbv iota.
            thaw FR2. thaw FR. rewrite (ctx_rep3_split DENT TABS gv p (c3_with_set _ _ _)).
            rewrite ctx_rest3k_with_set, ctx_rest3k_with_dict, ctx_rest3k_with_held.
            unfold dgroup, local_rep; cbn [c3_with_set c3_with_dict c3_with_s c3_dict c3_s c3_par c3_sp c3_set
              ddict_ref_fields df_local df_ddict df_uses df_lx sf_mem sf_held sf_with_held].
            rewrite sf_given_with_held.
            replace (local_held (ddict_ref_fields q)) with 0 by reflexivity.
            rewrite Z.sub_0_r.
            rewrite !if_true by auto. rewrite ?Hm, Hsp, Hnil.
            rewrite (field_at_data_at Ews t_dctx (DOT _customMem)).
            unfold hset_rep. rewrite if_true by auto.
            entailer!.
            repeat match goal with |- _ /\ _ => split end.
            all: try (unfold err_code, ZSTD_error_memory_allocation; rep_lia).
            all: try (f_equal; apply Int64.eqm_samerepr; exists (-1); reflexivity).
            right. split; [exact Hst0 |]. exists nullval, nil, 0.
            split; [unfold refddict_res3; rewrite ?(veqb_ptr q Hq), ?Hm, ?Hsp, ?Hnil; simpl; right; auto |].
            split; [unfold set_new_bytes in *; simpl sizeof in *; lia |]. split; [intros _; reflexivity |].
            split; [intros E; contradiction |].
            rewrite if_false by auto. rewrite ?Hsp, ?Hnil. reflexivity. }
          all: apply andp_left2, FF_left.
        - Intros.
          unfold hset_at at 1, hset_tbl at 1. Intros tbl tp.
          forward_if; [ exfalso; destruct sp'; try contradiction; simpl in *; congruence | ].
          forward.
          pose proof (set_bytes_new (sf_mem (c3_s k))) as Hsb.
          Exists sp' (set_bytes (sf_mem (c3_s k)) 64). unfold hset_at, hset_tbl. Exists tbl tp. rewrite Hnil.
          rewrite Hb0, Z.add_0_r.
          entailer!.
          all: try (split; [intros E; contradiction | lia]). }
      { (* the set exists *)
        match goal with Hx: c3_sp k <> nullval |- _ => rename Hx into Hsp end.
        rewrite (hset_rep_at _ _ _ _ Hsp). Intros.
        forward.
        Exists (c3_sp k) hbset. entailer!. split; [apply pon_isptr; auto | unfold hbset, set_new_bytes in *; simpl sizeof; lia]. }
      Intros sp1 hbs.
      match goal with Hx: isptr sp1 |- _ => rename Hx into Hsp1 end.
      match goal with Hx: c3_set k <> nil -> sp1 = c3_sp k |- _ => rename Hx into Hsp1a end.
      match goal with Hx: c3_sp k <> nullval -> sp1 = c3_sp k |- _ => rename Hx into Hsp1b end.
      match goal with Hx: c3_set k <> nil -> hbs = hbset |- _ => rename Hx into Hhbs end.
      match goal with Hx: 0 <= hbs <= set_new_bytes + sf_held (c3_s k) |- _ => rename Hx into Hhbs2 end.
      assert_PROP (sf_mem (c3_s k) = None -> hbs = 0) as Hhbn by (sep_apply hset_at_hb; entailer!).
      match goal with |- semax _ ?P _ _ =>
        forward_loop P
          continue: (EX hb': Z, PROP (hbs <= hb' <= hbs + set_grow hbs) LOCAL (gvars gv; temp _dctx p; temp _ddict q)
            SEP (mem_mgr gv; FRZL FR2; FRZL FR;
                 data_at Ews (nested_field_type t_dctx (DOT _customMem)) (cmem_v (sf_mem (c3_s k)))
                   (field_address t_dctx (DOT _customMem) p);
                 cm_have (sf_mem (c3_s k)) (base + hb');
                 field_at Ews t_dctx (DOT _ddictSet) sp1 p; hset_at (sf_mem (c3_s k)) sp1 (set_add (c3_set k) q dd) hb';
                 set_ids (c3_set k); ddid q (dd_id dd) (ddb dd)))%assert
          break: (EX hb': Z, PROP (hbs <= hb' <= hbs + set_grow hbs) LOCAL (gvars gv; temp _dctx p; temp _ddict q)
            SEP (mem_mgr gv; FRZL FR2; FRZL FR;
                 data_at Ews (nested_field_type t_dctx (DOT _customMem)) (cmem_v (sf_mem (c3_s k)))
                   (field_address t_dctx (DOT _customMem) p);
                 cm_have (sf_mem (c3_s k)) (base + hb');
                 field_at Ews t_dctx (DOT _ddictSet) sp1 p; hset_at (sf_mem (c3_s k)) sp1 (set_add (c3_set k) q dd) hb';
                 set_ids (c3_set k); ddid q (dd_id dd) (ddb dd)))%assert end.
      { apply ENTAIL_refl. }
      { forward.
        pose proof (set_grow_le hbs (proj1 Hhbs2)) as Hgr.
        forward_call (gv, sp1, c3_set k, q, dd, Ews, field_address t_dctx (DOT _customMem) p,
                      sf_mem (c3_s k), base + hbs, hbs).
        { apply (cm_room_sum _ _ _ _ _ Hroom); unfold base, set_new_bytes in *; simpl sizeof in *; lia. }
        Intros vret. destruct vret as [r hb']. simpl fst in *; simpl snd in *.
        forward.
        replace (base + hbs - hbs + hb') with (base + hb') by lia.
        match goal with Hx: r = 0 \/ r = _ |- _ => rename Hx into Hr end.
        match goal with Hx: c3_set k = nil -> r = 0 |- _ => rename Hx into Hr0 end.
        destruct Hr as [-> | ->].
        2: assert (Hne: c3_set k <> nil)
             by (intro E; specialize (Hr0 E); unfold err_code, ZSTD_error_memory_allocation in *; lia).
        - forward_call 0.
          replace (is_error_code 0) with false by reflexivity.
          forward_if; [ exfalso; auto | ].
          forward.
          rewrite if_true by auto.
          Exists hb'. entailer!.
        - forward_call (err_code ZSTD_error_memory_allocation).
          { unfold err_code, ZSTD_error_memory_allocation; rep_lia. }
          replace (is_error_code (err_code ZSTD_error_memory_allocation)) with true by reflexivity.
          forward_if; [ | exfalso; apply Int.one_not_zero; assumption ].
          dw0_skip. dw0_if0. dw0_skip. dw0_skip.
          forward.
          specialize (Hsp1a Hne). subst sp1. specialize (Hhbs Hne). subst hbs.
          Exists (err_code ZSTD_error_memory_allocation)
            (c3_with_set (c3_with_dict (c3_with_s k (sf_with_held (c3_s k) hb')) (ddict_ref_fields q))
                         (c3_sp k) (c3_set k)).
          rewrite (veqb_ptr q Hq), Hm. simpl andb. cbv iota.
          rewrite if_false by (unfold err_code, ZSTD_error_memory_allocation; lia).
          thaw FR2. thaw FR. rewrite (ctx_rep3_split DENT TABS gv p (c3_with_set _ _ _)).
          rewrite ctx_rest3k_with_set, ctx_rest3k_with_dict, ctx_rest3k_with_held.
          unfold dgroup, local_rep; cbn [c3_with_set c3_with_dict c3_with_s c3_dict c3_s c3_par c3_sp c3_set
            ddict_ref_fields df_local df_ddict df_uses df_lx sf_mem sf_held sf_with_held].
          rewrite sf_given_with_held.
          replace (local_held (ddict_ref_fields q)) with 0 by reflexivity.
          replace (sf_given (c3_s k) - sf_held (c3_s k) + hb') with (base + hb') by (subst base; lia).
          rewrite Z.sub_0_r.
          rewrite !if_true by auto. rewrite ?Hm.
          rewrite (field_at_data_at Ews t_dctx (DOT _customMem)).
          rewrite (hset_rep_at _ _ _ _ ltac:(intro E; rewrite E in Hsp1; simpl in Hsp1; contradiction)).
          assert_PROP (sf_mem (c3_s k) = None -> hb' = 0) as Hhn' by (sep_apply hset_at_hb; entailer!).
          entailer!.
          repeat match goal with |- _ /\ _ => split end.
          all: try (unfold err_code, ZSTD_error_memory_allocation; rep_lia).
          right. split; [exact Hst0 |]. exists (c3_sp k), (c3_set k), hb'.
          split; [unfold refddict_res3; rewrite ?(veqb_ptr q Hq), ?Hm; simpl; right; auto |].
          split; [unfold set_new_bytes in *; simpl sizeof in *; lia |]. split; [exact Hhn' |].
          split; [intros E; contradiction |].
          rewrite if_false by auto. reflexivity. }
      { Intros hb'. forward. Exists hb'. entailer!. }
      Intros hb'.
      pose proof (set_grow_le hbs (proj1 Hhbs2)) as Hgr.
      assert_PROP (sf_mem (c3_s k) = None -> hb' = 0) as Hhn' by (sep_apply hset_at_hb; entailer!).
      forward.
      Exists 0 (c3_with_set (c3_with_dict (c3_with_s k (sf_with_held (c3_s k) hb')) (ddict_ref_fields q))
                            sp1 (set_add (c3_set k) q dd)).
      rewrite (veqb_ptr q Hq), Hm. simpl andb. cbv iota.
      thaw FR2. thaw FR. rewrite (ctx_rep3_split DENT TABS gv p (c3_with_set _ _ _)).
      rewrite ctx_rest3k_with_set, ctx_rest3k_with_dict, ctx_rest3k_with_held.
      unfold dgroup, local_rep; cbn [c3_with_set c3_with_dict c3_with_s c3_dict c3_s c3_par c3_sp c3_set
        ddict_ref_fields df_local df_ddict df_uses df_lx sf_mem sf_held sf_with_held].
      rewrite sf_given_with_held.
      replace (local_held (ddict_ref_fields q)) with 0 by reflexivity.
      replace (sf_given (c3_s k) - sf_held (c3_s k) + hb') with (base + hb') by (subst base; lia).
      rewrite Z.sub_0_r.
      rewrite !if_true by auto. rewrite ?Hm.
      rewrite (field_at_data_at Ews t_dctx (DOT _customMem)).
      rewrite (hset_rep_at _ _ _ _ ltac:(intro E; rewrite E in Hsp1; simpl in Hsp1; contradiction)).
      entailer!.
      repeat match goal with |- _ /\ _ => split end.
      all: try apply set_add_nonnil.
      right. split; [exact Hst0 |]. exists sp1, (set_add (c3_set k) q dd), hb'.
      split; [unfold refddict_res3; rewrite ?(veqb_ptr q Hq), ?Hm; simpl; left; auto |].
      split; [unfold set_new_bytes in *; simpl sizeof in *; lia |]. split; [exact Hhn' |].
      split; [intros E; contradiction |].
      rewrite if_false by auto. reflexivity.
Qed.

Lemma body_refDDict_int3 : FS3_body (fun DENT TABS SR BR => ZSTD_DCtx_refDDict_int_spec3 DENT TABS).
Proof.
  intros DENT TABS SR BR HD HT.
  apply (load3_lift (G_ref DENT)); [unfold G_ref; load3_in | apply body_refDDict_int3_small].
Qed.

End CM_Load3Ref_1.
