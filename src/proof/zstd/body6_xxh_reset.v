(* Body of ZSTD_XXH64_reset (group xxh).  Run 6: the proof of this body (body_xxh_state.v holds the group's other lemmas). *)
Require Import Zstd.proof.zstd.Gprog.
Require Import Zstd.proof.zstd.XxhLemmas.
Require Import Zstd.proof.zstd.body_xxh_state.

Lemma xr_lanes_nil: forall seed, xxh_lanes seed [] = xxh_init seed.
Proof. reflexivity. Qed.

Lemma xr_rest_nil: forall seed, xxh_rest seed [] = [].
Proof. reflexivity. Qed.

Lemma xr_mem64: forall sh v st, field_compatible t_xxh64_state [] st ->
  field_at sh t_xxh64_state (DOT _mem64) v st |--
  data_at sh (tarray tuchar 32) (Zrepeat Vundef 32) (field_address t_xxh64_state (DOT _mem64) st).
Proof.
  intros sh v st Hfc.
  sep_apply (field_at_field_at_ sh t_xxh64_state (DOT _mem64)).
  rewrite field_at__memory_block.
  change (Zrepeat Vundef 32) with (default_val (tarray tuchar 32)).
  change (data_at sh (tarray tuchar 32) (default_val (tarray tuchar 32)))
    with (data_at_ sh (tarray tuchar 32)).
  rewrite data_at__memory_block. apply andp_right; [apply prop_right | simpl; cancel].
  apply fc_scalar_bytes with (t := tarray tulong 4); [reflexivity | apply Z.divide_1_l |].
  assert (H: field_compatible t_xxh64_state (DOT _mem64) st) by auto with field_compatible.
  unfold field_address. rewrite if_true by auto.
  apply (field_compatible_nested_field t_xxh64_state (DOT _mem64) st H).
Qed.

Lemma xr_v4: forall (l: list val) a b c d, Zlength l = 4 ->
  upd_Znth 3 (upd_Znth 2 (upd_Znth 1 (upd_Znth 0 l a) b) c) d = [a; b; c; d].
Proof.
  intros. destruct l as [|? [|? [|? [|? [|]]]]]; try (rewrite Zlength_correct in H; simpl in H; lia).
  reflexivity.
Qed.

Lemma xr_lanes: forall seed,
  map Vlong (map Int64.repr [xxh_lane1 (xxh_init seed); xxh_lane2 (xxh_init seed);
                             xxh_lane3 (xxh_init seed); xxh_lane4 (xxh_init seed)]) =
  [Vlong (Int64.repr (seed + -7046029288634856825 + -4417276706812531889));
   Vlong (Int64.repr (seed + -4417276706812531889)); Vlong (Int64.repr seed);
   Vlong (Int64.repr (seed - -7046029288634856825))].
Proof.
  intros. unfold xxh_init, xxh_lane1, xxh_lane2, xxh_lane3, xxh_lane4.
  cbn [map]. rewrite !repr_m64.
  assert (E1: Int64.eqm (-7046029288634856825) XXH_P1) by (exists (-1); reflexivity).
  assert (E2: Int64.eqm (-4417276706812531889) XXH_P2) by (exists (-1); reflexivity).
  replace (Int64.repr (seed + -7046029288634856825 + -4417276706812531889))
    with (Int64.repr (seed + XXH_P1 + XXH_P2))
    by (apply Int64.eqm_samerepr; repeat apply Int64.eqm_add; auto using Int64.eqm_refl, Int64.eqm_sym).
  replace (Int64.repr (seed + -4417276706812531889)) with (Int64.repr (seed + XXH_P2))
    by (apply Int64.eqm_samerepr; repeat apply Int64.eqm_add; auto using Int64.eqm_refl, Int64.eqm_sym).
  replace (Int64.repr (seed - -7046029288634856825)) with (Int64.repr (seed - XXH_P1))
    by (apply Int64.eqm_samerepr; apply Int64.eqm_sub; auto using Int64.eqm_refl, Int64.eqm_sym).
  reflexivity.
Qed.

Lemma body6_ZSTD_XXH64_reset: semax_body Vprog Gprog f_ZSTD_XXH64_reset ZSTD_XXH64_reset_spec.
Proof.
  start_function.
  assert_PROP (isptr st) as Hst by entailer!.
  forward_if True.
  { destruct st; try contradiction. inv H0. }
  { forward. entailer!. }
  Intros.
  assert_PROP (field_compatible t_xxh64_state [] st) as Hfc by entailer!.
  rewrite data_at__memory_block. Intros.
  assert (Hsz: sizeof t_xxh64_state = 88) by reflexivity. rewrite Hsz.
  forward_call (sh, st, 0, 88).
  rewrite <- Hsz.
  sep_apply (memset_zero_data_at sh t_xxh64_state st); auto.
  unfold_data_at (data_at _ _ _ st).
  simpl zero_val.
  forward. forward. forward. forward. forward.
  match goal with |- context [field_at _ _ (DOT _total_len) ?x _] =>
    replace x with (Vlong Int64.zero)
      by (rewrite zero_val_eq; unfold fold_reptype; simpl; symmetry; apply zero_val_tulong) end.
  match goal with |- context [field_at _ _ (DOT _memsize) ?x _] =>
    replace x with (Vint Int.zero)
      by (rewrite zero_val_eq; unfold fold_reptype; simpl; symmetry; apply zero_val_tuint) end.
  match goal with |- context [upd_Znth 0 ?x] =>
    replace x with (Zrepeat (Vlong Int64.zero) 4)
      by (rewrite zero_val_eq; unfold fold_reptype; simpl; rewrite zero_val_tarray, zero_val_tulong; reflexivity) end.
  rewrite xr_v4 by reflexivity.
  sep_apply (xr_mem64 sh (fst (snd (snd (zero_val t_xxh64_state)))) st Hfc).
  sep_apply (field_at_field_at_ sh t_xxh64_state (DOT _reserved32)).
  sep_apply (field_at_field_at_ sh t_xxh64_state (DOT _reserved64)).
  unfold xxh64_state. Exists (Zrepeat Vundef 32). rewrite xr_lanes_nil, xr_rest_nil, xr_lanes.
  apply andp_right; [apply prop_right; split; [constructor | reflexivity] |]. cancel.
Qed.
