(* FS3 streaming, case zdss_loadHeader, G4: a skippable header with the selection on: zstd's
   selectFrameDDict probes the magic variant, the model's skip_cd selects with it. *)
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3Stmts Zstd.proof.dec.v3.FS.stream.lh.LH3G42_dict.
Local Open Scope Z_scope.

Section CM_LH3G42_skip_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma g4_magic_variant : forall m, 0 <= m < 2 ^ 32 -> is_skippable_magic m = true ->
  m - ZSTD_MAGIC_SKIPPABLE_START = Z.land m 15.
Proof.
intros m Hm Hs. unfold is_skippable_magic in Hs. apply Z.eqb_eq in Hs.
assert (Hmask: ZSTD_MAGIC_SKIPPABLE_MASK = Z.ldiff (Z.ones 32) (Z.ones 4)) by reflexivity.
assert (H1: Z.land m (Z.ones 32) = m).
{ rewrite Z.land_ones by lia. apply Z.mod_small. exact Hm. }
assert (H2: Z.land m ZSTD_MAGIC_SKIPPABLE_MASK = Z.ldiff m (Z.ones 4)).
{ rewrite Hmask. rewrite <- H1 at 2. apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec, !Z.ldiff_spec, Z.land_spec. destruct (Z.testbit m n), (Z.testbit (Z.ones 32) n), (Z.testbit (Z.ones 4) n); reflexivity. }
rewrite H2 in Hs. rewrite Z.ldiff_ones_r in Hs by lia.
change 15 with (Z.ones 4). rewrite Z.land_ones by lia.
rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 in Hs by lia.
pose proof (Z.div_mod m (2 ^ 4) ltac:(lia)). lia.
Qed.

Lemma g4s_lev_range (l: list Z) : bytes_ok l -> 0 <= le_value l < 2 ^ (8 * Zlength l).
Proof.
  intros H. induction H; cbn [le_value].
  - rewrite Zlength_nil. simpl. lia.
  - unfold is_byte in H. rewrite Zlength_cons. replace (8 * Z.succ (Zlength l)) with (8 + 8 * Zlength l) by lia.
    rewrite Z.pow_add_r by (pose proof (Zlength_nonneg l); lia).
    change (2^8) with 256. lia.
Qed.

Lemma g4s_lef_range (l: list Z) i k : bytes_ok l -> 0 <= k -> 0 <= le_field l i k < 2 ^ (8 * k).
Proof.
  intros H Hk. unfold le_field, slice.
  assert (Hb: bytes_ok (firstn (Z.to_nat k) (skipn (Z.to_nat i) l))).
  { unfold bytes_ok in *. apply Forall_firstn, Forall_skipn; auto. }
  pose proof (g4s_lev_range _ Hb).
  assert (Zlength (firstn (Z.to_nat k) (skipn (Z.to_nat i) l)) <= k).
  { rewrite Zlength_correct, firstn_length. lia. }
  assert (2 ^ (8 * Zlength (firstn (Z.to_nat k) (skipn (Z.to_nat i) l))) <= 2 ^ (8 * k)).
  { apply Z.pow_le_mono_r; [ lia | ]. pose proof (Zlength_nonneg (firstn (Z.to_nat k) (skipn (Z.to_nat i) l))). lia. }
  lia.
Qed.

(* a skippable header's Dictionary_ID field (ZSTD_getFrameHeader: the magic variant) *)
Lemma g4_skip_did : forall hb h, bytes_ok hb -> get_frame_header hb = FH_ok h -> fh_frameType h = 1 ->
  is_skippable_magic (le_field hb 0 4) = true -> fh_dictID h = Z.land (le_field hb 0 4) 15.
Proof.
intros hb h Hbo H Ft Hsk.
rewrite <- g4_magic_variant by (exact Hsk || (pose proof (g4s_lef_range hb 0 4 Hbo ltac:(lia)); lia)).
unfold get_frame_header in H.
destruct (Zlength hb <? 5).
{ destruct (Zlength hb >? 0); [ destruct (_ && _)%bool | ]; discriminate. }
cbv zeta in H.
destruct (le_field hb 0 4 =? ZSTD_MAGICNUMBER) eqn:Em.
{ apply Z.eqb_eq in Em. rewrite Em in Hsk. discriminate. }
cbn [negb] in H. rewrite Hsk in H. destruct (Zlength hb <? ZSTD_SKIPPABLEHEADERSIZE); [ discriminate | ].
inversion H; reflexivity.
Qed.

(* the streaming selection with a set, with st_sel's condition on the context's dictionary (v3.4) *)
Definition g4_cur_dd (od: option dictref) : Prop :=
  match od with
  | Some dr => match dr_src dr with DSDDict _ _ => True | _ => dr_bytes dr <> nil end
  | None => False
  end.

Lemma g4_st_sel2 : forall st, dc_set st <> nil ->
  st_sel st = (sel_none, None) \/
  (st_sel st = (set_sel (dc_set st), None) /\ dp_multi (dc_par st) = 1 /\ set_clean (dc_set st) = true /\
   g4_cur_dd (dc_dict st)).
Proof.
intros st Hne. unfold st_sel. destruct (dc_set st) as [|e0 l0]; [ contradiction | ].
destruct (dc_dict st) as [dr|]; [ | left; reflexivity ].
destruct ((dp_multi (dc_par st) =? 1) && set_clean (e0 :: l0) &&
          match dr_src dr with DSDDict _ _ => true | _ => negb (Nat.eqb (length (dr_bytes dr)) 0) end)%bool
  eqn:E; [ | left; reflexivity ].
apply andb_prop in E. destruct E as [E E3]. apply andb_prop in E. destruct E as [E1 E2]. apply Z.eqb_eq in E1.
right. split; [ reflexivity | ]. split; [ exact E1 | ]. split; [ exact E2 | ]. cbn [g4_cur_dd].
destruct (dr_src dr); auto; apply negb_true_iff, Nat.eqb_neq in E3; intros En; rewrite En in E3; apply E3; reflexivity.
Qed.

(* with the selection described (st_sel), the context has a current DDict *)
Lemma g4_sel_ddict : forall W st d, stream_dict_ok W st -> dict_rel3 st d ->
  (forall q dd, In (q, dd) (dc_set st) -> q <> nullval) -> g4_cur_dd (dc_dict st) -> df_ddict d <> nullval.
Proof.
intros W st d Hsd Hdr Hptr' Hc.
destruct Hdr as [Hdr | (_ & (_ & _ & _ & Hin'))].
- destruct (dc_dict st) as [dr|] eqn:Ed; [ | contradiction ]. cbn [dict_rel3_of g4_cur_dd] in Hdr, Hc.
  unfold stream_dict_ok in Hsd. rewrite Ed in Hsd. destruct Hsd as ((Ho & Hs) & _).
  destruct (dr_src dr) as [pk | | q' pref]; [ contradiction | | ].
  + destruct Hdr as (_ & Hz).
    destruct (Z.eqb_spec (Zlength (dr_bytes dr)) 0) as [Z0|Z0].
    * exfalso. apply Hc. apply Zlength_nil_inv. exact Z0.
    * destruct Hz as (buf0 & ld & am0 & Hlp & Hdd & _). rewrite Hdd. intros E. rewrite E in Hlp. exact Hlp.
  + destruct Hdr as (_ & _ & Hq & _ & Hdd & _). rewrite Hdd. intros E. rewrite E in Hq. exact Hq.
- apply list_in_map_inv in Hin'. destruct Hin' as ([q' dd'] & Eq & Hin'). cbn in Eq. rewrite Eq.
  exact (Hptr' _ _ Hin').
Qed.

(* the dictionary the model has after a skippable header (skip_cd) is the one the context has after zstd's
   selection on the magic variant *)
Lemma g4_cd_skip2 : hs_probe_ok -> forall W a k hb h tbl d1 did1 cd k',
  base_call (a_st a) k -> stream_dict_ok W (a_st a) ->
  (c3_set k = nil -> c3_sp k = nullval) -> (c3_set k <> nil -> c3_sp k <> nullval) ->
  lhA_sel k hb 0 (fh_val h) tbl d1 did1 -> 0 <= fh_dictID h <= Int.max_unsigned ->
  fh_dictID h = Z.land (le_field hb 0 4) 15 ->
  (st_sel (a_st a) = (sel_none, None) -> cd = None) ->
  cur_dict_ok (a_st a) k cd ->
  c3_dict k' = snd (getddict_res d1) ->
  fp_dictID (fs_fParams (c3_fs k')) = Vint (Int.repr (fh_dictID h)) ->
  cur_dict_ok (a_st a) k' (skip_cd (dmode_w (dmode_of (dc_par (a_st a)))) (fst (st_sel (a_st a))) hb cd).
Proof.
intros Hpr W a k hb h tbl d1 did1 cd k' Hb Hsd Hsp0 Hsp1 Hsel Hidr Hvar Hcd0 Hcd Hk' Hfp'.
pose proof Hb as Hb'. destruct Hb' as (Hstab & Hpar & Hset & Hdr & Hsco & _).
destruct Hsel as (_ & _ & id & Hid & Hsb). unfold sel_by in Hsb.
unfold skip_cd. cbn [md_dwin dmode_w]. rewrite <- Hvar.
assert (Hcase: dc_set (a_st a) = nil \/ dc_set (a_st a) <> nil)
  by (destruct (dc_set (a_st a)); [ left; auto | right; discriminate ]).
destruct Hcase as [Es | Hne].
- (* no set: the model's sel is sel_none, cur_dict_ok's no-set case does not read k *)
  assert (Hss: fst (st_sel (a_st a)) = sel_none) by (unfold st_sel; rewrite Es; reflexivity).
  rewrite Hss. unfold sel_none. intros dm Hdm. destruct (Hcd dm Hdm) as [Hl | (Hn & _)]; [ left; exact Hl | contradiction ].
- destruct (g4_st_sel2 _ Hne) as [Hss | (Hss & Hmulti & Hclean & Hcdd)].
  { rewrite (Hcd0 Hss), Hss. cbn [fst]. unfold sel_none. intros dm E; discriminate. }
  rewrite Hss. cbn [fst].
  pose proof (g4_sel_on_t k (a_st a) Hb Hne Hsp1 Hmulti) as Hon.
  specialize (Hid Hon). rewrite g4_fpid in Hid. rewrite Hon in Hsb.
  destruct Hsb as (Hinv & Hidr' & Hd1 & _).
  pose proof (g4_repr_inj _ _ Hidr Hidr' Hid) as <-. clear Hid Hidr'.
  rewrite Hset in Hinv. pose proof Hinv as Hinv'.
  destruct Hinv' as (_ & _ & _ & Hnd & _ & Hptr & _).
  pose proof (g4_clean_ids _ Hclean) as Hnz.
  assert (Hptr': forall q dd, In (q, dd) (dc_set (a_st a)) -> q <> nullval).
  { intros q dd Hin E. rewrite Forall_forall in Hptr. specialize (Hptr _ Hin). cbn in Hptr. subst q. exact Hptr. }
  (* zstd selects only with a current DDict: st_sel's condition gives one *)
  pose proof (g4_sel_ddict W (a_st a) (c3_dict k) Hsd Hdr Hptr' Hcdd) as Dn.
  assert (Hr: sel_r (c3_dict k) (c3_set k) tbl (fh_dictID h) = set_find (dc_set (a_st a)) (fh_dictID h)).
  { unfold sel_r. destruct (eq_dec (df_ddict (c3_dict k)) nullval); [ contradiction | ].
    rewrite Hset. destruct (Hpr _ _ _ Hinv Hidr) as [_ Hf]. apply Hf, Hnz. }
  rewrite Hr in Hd1.
  destruct (set_sel (dc_set (a_st a)) (fh_dictID h)) as [dq|] eqn:Esel.
  + (* a hit: the set's DDict *)
    destruct (g4_find_hit _ _ _ Esel) as (Hid0 & e & Hin & Hide & Hfind & Hauto).
    destruct e as [q dd0]. cbn [fst snd] in *.
    rewrite Hfind in Hd1. unfold sel_dict in Hd1.
    destruct (eq_dec q nullval) as [Eq|_]; [ exfalso; exact (Hptr' _ _ Hin Eq) | ]. subst d1.
    intros dm' E. inversion E; subst dm'. right. rewrite Hk'. cbn [getddict_res snd].
    split; [ exact Hne | ]. split; [ reflexivity | ]. split; [ exists dd0; split; [ exact Hin | exact Hauto ] | ].
    exists (fh_dictID h). split; [ exact Hfp' | ]. split; [ exact Hidr | ]. right. rewrite Hfind. reflexivity.
  + (* a miss: the current DDict, which cur_dict_ok describes *)
    rewrite (g4_find_miss _ _ Hclean Esel) in Hd1. unfold sel_dict in Hd1.
    destruct (eq_dec nullval nullval) as [_|E]; [ | congruence ]. subst d1.
    intros dm Hdm. destruct (Hcd dm Hdm) as [(Hn & _) | (_ & Hu & Hdd0 & _)]; [ contradiction | ].
    right. rewrite Hk', (g4_getddict_m1 _ Hu). cbn [snd].
    split; [ exact Hne | ]. split; [ exact Hu | ]. split; [ exact Hdd0 | ].
    exists (fh_dictID h). split; [ exact Hfp' | ]. split; [ exact Hidr | ]. left. apply g4_find_miss; auto.
Qed.

End CM_LH3G42_skip_1.
