(* valid_params main, segment A (see the header of VPMain.v). *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.harness.valid_params.VPMain.
Require Import Zstd.proof.harness.valid_params.VPMem Zstd.proof.harness.valid_params.VPMem2 Zstd.proof.harness.valid_params.VPMem3.

Local Notation HCS := Zstd.proof.harness.valid_params.HOK_valid_params.CompSpecs.
Local Notation ZCS := Zstd.proof.zstd.Base.CompSpecs.
Local Notation tout := (Tstruct _ZSTD_outBuffer_s noattr).
Local Notation tin := (Tstruct _ZSTD_inBuffer_s noattr).


(* ---------- pure facts ---------- *)

Lemma VPA_byte_at (l: list Z) i : 0 <= i -> byte_at l i = Znth i l.
Proof. intros. unfold byte_at, Znth. destruct (Z_lt_dec i 0); [lia | reflexivity]. Qed.

Lemma VPA_ck_refl fs b : bytes_ok b -> ck_agree fs b b.
Proof. intros Hb. split; [reflexivity|]. split; [exact Hb|]. intros i _ Hne. contradiction. Qed.

Lemma VPA_ck_upd fs b b' f i c :
  ck_agree fs b b' -> In f fs -> wi_skippable f = false -> wi_checksum f = true ->
  wi_end f - 4 <= i < wi_end f -> 0 <= i < Zlength b' -> 0 <= c < 256 ->
  ck_agree fs b (upd_Znth i b' c).
Proof.
  intros (Hl & Hb & Hd) Hf Hs Hc Hi Hi' Hcr.
  split; [rewrite Zlength_upd_Znth; exact Hl|].
  split.
  { unfold bytes_ok in *. apply Forall_upd_Znth; auto; unfold is_byte; lia. }
  intros i' Hi'' Hne.
  destruct (Z.eq_dec i' i) as [->|Hne'].
  - exists f. auto.
  - rewrite !VPA_byte_at in * by lia.
    rewrite upd_Znth_diff in Hne by lia. apply Hd; [lia|]. rewrite !VPA_byte_at by lia. exact Hne.
Qed.

Lemma VPA_ck_self ws : ws_ck ws (ws_bytes ws) = ws.
Proof. destruct ws; reflexivity. Qed.

Lemma VPA_frame_ck ws f : series_facts no_dict ws -> wseries_wf ws -> In f (ws_frames ws) ->
  wi_skippable f = false -> wi_checksum f = true ->
  0 <= wi_start f /\ 7 <= wi_size f /\ wi_end f <= Zlength (ws_bytes ws).
Proof.
  intros Hsf (Hw & _ & Hlay) Hin Hs Hc.
  pose proof Hsf as (_ & _ & _ & _ & _ & Ht & _).
  apply sl_tiles_bounds in Ht. destruct Ht as (_ & _ & Hb).
  rewrite Forall_forall in Hb, Hw, Hlay.
  specialize (Hb f Hin). specialize (Hw f Hin). specialize (Hlay f Hin Hs Hc).
  destruct Hw as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hh). unfold u64 in Hh.
  unfold wi_end in *. lia.
Qed.

Lemma VPA_len_pos ws : series_facts no_dict ws -> 0 < Zlength (ws_bytes ws).
Proof.
  intros (_ & _ & _ & _ & Hn & Ht & _).
  apply sl_tiles_bounds in Ht. destruct Ht as (_ & _ & Hb).
  destruct (ws_frames ws) as [|f fs]; [simpl in Hn; lia|].
  inversion Hb as [|? ? (A & B & C & _) _]; subst. unfold wi_end in C. lia.
Qed.

Lemma VPA_mg_len ws f : series_facts no_dict ws -> ws_frames ws = [f] -> wi_skippable f = false ->
  5 <= Zlength (ws_bytes ws).
Proof.
  intros Hsf Hf Hs. pose proof Hsf as (_ & _ & _ & _ & _ & Ht & Hff & _).
  rewrite Hf in Ht, Hff. simpl in Ht. destruct Ht as (Hst & _).
  inversion Hff as [|? ? Hfa _]; subst.
  destruct Hfa as (_ & _ & _ & _ & _ & _ & Hhs & _).
  specialize (Hhs Hs). rewrite Hst in Hhs.
  change (skipn (Z.to_nat 0) (ws_bytes ws)) with (ws_bytes ws) in Hhs.
  unfold frame_header_size in Hhs.
  destruct (Zlength (ws_bytes ws) <? ZSTD_FRAMEHEADERSIZE_PREFIX) eqn:E; [discriminate|].
  apply Z.ltb_ge in E. unfold ZSTD_FRAMEHEADERSIZE_PREFIX in E. lia.
Qed.

Lemma VPA_base_lt mode ws (b': list Z) : series_facts no_dict ws -> Zlength b' = Zlength (ws_bytes ws) ->
  (mode = 3 -> exists f, ws_frames ws = [f] /\ wi_skippable f = false) -> vp_base mode < Zlength b'.
Proof.
  intros Hsf Hl H3. unfold vp_base. rewrite Hl.
  destruct (Z.eqb_spec mode 3) as [E|E].
  - destruct (H3 E) as (f & Hf & Hs). pose proof (VPA_mg_len ws f Hsf Hf Hs). lia.
  - pose proof (VPA_len_pos ws Hsf). lia.
Qed.

#[local] Instance VPA_inh_winfo : Inhabitant winfo := winfo0.

Lemma VPA_frame_f (fs: list winfo) k : 0 <= k < Zlength fs ->
  Znth k (map winfo_val fs ++ Zrepeat (winfo_val winfo0) (4 - Zlength fs)) = winfo_val (Znth k fs).
Proof.
  intros. rewrite Znth_app1 by (rewrite Zlength_map; lia). rewrite Znth_map by lia. reflexivity.
Qed.

Lemma VPA_wdict_null WDS : emp |-- wdict_arg WDS nullval WANone.
Proof. unfold wdict_arg. entailer!. Qed.

Lemma VPA_zext8 c : 0 <= c < 256 -> Int.zero_ext 8 (Int.repr c) = Int.repr c.
Proof.
  intros. unfold Int.zero_ext. rewrite Int.unsigned_repr by rep_lia.
  rewrite Zbits.Zzero_ext_mod by lia. rewrite Z.mod_small; [reflexivity|].
  change (two_p 8) with 256. lia.
Qed.

(* ---------- one byte of sr.bytes ---------- *)

Lemma VPA_bytes_split sh (VB: list val) i p : 0 <= i < 524288 -> Zlength VB = 524288 ->
  @field_at HCS sh t_wseries (DOT _bytes) VB p =
  (@array_at HCS sh t_wseries (DOT _bytes) 0 i (sublist 0 i VB) p *
   @field_at HCS sh t_wseries (DOT _bytes SUB i) (Znth i VB) p *
   @array_at HCS sh t_wseries (DOT _bytes) (i + 1) 524288 (sublist (i + 1) 524288 VB) p)%logic.
Proof.
  intros Hi Hl.
  erewrite field_at_Tarray; [ | auto with field_compatible | reflexivity | lia | apply JMeq_refl].
  2: { split; [exact I | left; reflexivity]. }
  erewrite (split3_array_at sh t_wseries (DOT _bytes) 0 i 524288); [| lia | exact Hl | rewrite Z.sub_0_r; apply JMeq_refl].
  rewrite !Z.sub_0_r. reflexivity.
Qed.

Lemma VPA_bytes_join sh (VB: list val) i v p : 0 <= i < 524288 -> Zlength VB = 524288 ->
  (@array_at HCS sh t_wseries (DOT _bytes) 0 i (sublist 0 i VB) p *
   @field_at HCS sh t_wseries (DOT _bytes SUB i) v p *
   @array_at HCS sh t_wseries (DOT _bytes) (i + 1) 524288 (sublist (i + 1) 524288 VB) p)%logic
  |-- @field_at HCS sh t_wseries (DOT _bytes) (upd_Znth i VB v) p.
Proof.
  intros Hi Hl.
  rewrite (VPA_bytes_split sh (upd_Znth i VB v) i p) by (try rewrite Zlength_upd_Znth; lia).
  rewrite upd_Znth_same by lia.
  rewrite sublist_upd_Znth_l by lia. rewrite sublist_upd_Znth_r by lia.
  apply derives_refl.
Qed.

(* sr's byte i lent out: the byte c stored there gives back sr holding ws_ck ws (upd_Znth i b c) *)
Lemma VPA_cell ws b i c p : 0 <= i < Zlength b -> Zlength b <= 2 ^ 19 ->
  @data_at HCS Ews t_wseries (wseries_val (ws_ck ws b)) p |--
  @field_at HCS Ews t_wseries (DOT _bytes SUB i) (Vint (Int.repr (Znth i b))) p *
  (@field_at HCS Ews t_wseries (DOT _bytes SUB i) (Vint (Int.repr c)) p -*
   @data_at HCS Ews t_wseries (wseries_val (ws_ck ws (upd_Znth i b c))) p).
Proof.
  intros Hi Hb.
  eapply derives_trans; [apply VP_sr_unfold7|]. cbn [ws_ck ws_bytes ws_content ws_frames].
  set (VB := zbytes b ++ Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength b)).
  assert (HVB: Zlength VB = 524288) by (subst VB; list_solve).
  assert (EZ: Znth i VB = Vint (Int.repr (Znth i b))).
  { subst VB. rewrite Znth_app1 by list_solve. rewrite Znth_map by lia. reflexivity. }
  rewrite (VPA_bytes_split Ews VB i p) by lia. rewrite EZ.
  rewrite !sepcon_assoc. rewrite (sepcon_comm (array_at _ _ _ _ _ _ _)).
  rewrite !sepcon_assoc. apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint.
  eapply derives_trans; [|apply VP_sr_fold7]. cbn [ws_ck ws_bytes ws_content ws_frames].
  rewrite Zlength_upd_Znth.
  replace (zbytes (upd_Znth i b c) ++ Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength b)) with
    (upd_Znth i VB (Vint (Int.repr c))).
  2: { subst VB. rewrite upd_Znth_app1 by list_solve. rewrite <- upd_Znth_map. reflexivity. }
  sep_apply (VPA_bytes_join Ews VB i (Vint (Int.repr c)) p ltac:(lia) HVB).
  cancel.
Qed.

(* a field of sr.f[k] after a load: Znth k of the frame table is winfo_val f (EF), whatever instance *)
Ltac VPA_fix f :=
  repeat match goal with |- context [@Znth ?A ?I ?k ?l] =>
    replace (@Znth A I k l) with (winfo_val f : A) end;
  cbn [winfo_val].

Ltac VPA_fix_tc f :=
  VPA_fix f; entailer!;
  repeat match goal with |- context [@Znth ?A ?I ?k ?l] =>
    replace (@Znth A I k l) with (winfo_val f : A) end;
  unfold winfo_val; simpl; unfold vb, vu, vl;
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; simpl; auto.

Lemma VPA_vp (P R: mpred) p : (P && valid_pointer p) * R |-- valid_pointer p.
Proof. apply sepcon_valid_pointer1. apply andp_left2. apply derives_refl. Qed.

Lemma VPA_if_data_at_ {cs: compspecs} sh t q (v: reptype t) :
  (if eq_dec q nullval then emp else (malloc_token sh t q * data_at sh t v q))%logic |--
  (if eq_dec q nullval then emp else (malloc_token sh t q * data_at_ sh t q))%logic.
Proof. destruct (eq_dec q nullval); [apply derives_refl | cancel]. Qed.

Lemma VPA_isptr p : is_pointer_or_null p -> p <> nullval -> isptr p.
Proof. intros H1 H2. destruct p; try contradiction; simpl; auto. simpl in H1. subst. contradiction. Qed.

Lemma VPA_repr1_neq0: Int.repr 1 <> Int.zero.
Proof. intro H; inv H. Qed.

Ltac VPA_tc_null_test p :=
  apply denote_tc_test_eq_split; [|apply valid_pointer_null];
  destruct (eq_dec p nullval); [subst; apply valid_pointer_null|];
  rewrite ?(if_false (p = nullval)) by auto;
  match goal with |- context [malloc_token ?sh ?t p] =>
    destruct (zlt 0 (sizeof t));
    [ apply derives_trans with (data_at_ sh t p * TT)%logic; [cancel|];
      apply sepcon_valid_pointer1; apply data_at__valid_ptr; [auto | lia]
    | apply derives_trans with (malloc_token sh t p * TT)%logic; [cancel|];
      apply sepcon_valid_pointer1; apply malloc_token_valid_pointer; lia ]
  end.

Section Seg.
Context {Espec: OracleKind}.
Variable DC : globals -> val -> dctx_st -> mpred.
Variable DD : globals -> val -> ddict_st -> mpred.
Variable WG : globals -> mpred.
Variable WDS : wdict -> reptype t_wstate -> Prop.
Local Notation Delta := (VP_Delta DC DD WG WDS).

(* A: s0..s11 *)
Lemma VP_segA (gv: globals) (vz vi vo: val) :
  (forall mode ws b' src dctx, VP_SA_facts mode ws b' -> isptr src -> isptr dctx ->
     semax Delta (VP_SA DC WG gv vz vi vo mode ws b' src dctx) (VP_rest 12) VP_RR) ->
  semax Delta (VP_S0 WG gv vz vi vo) (VP_rest 0) VP_RR.
Proof.
intros HK.
unfold VP_S0, VP_rest, VP_Delta, VP_RR.
let B := eval cbv [VP_drop VP_body0] in (VP_drop 0 VP_body0) in
let rec build k t := lazymatch k with
  | O => constr:(VP_drop 12 VP_body0)
  | S ?k' => lazymatch t with Ssequence ?a ?b => let b' := build k' b in constr:(Ssequence a b') end end in
let B' := build 12%nat B in
change (VP_drop 0 VP_body0) with B'.
simplify_func_tycontext.
abbreviate_semax.
forward_call 4.
Intros mode.
forward. forward. forward. forward.
sep_apply (VPA_wdict_null WDS).
forward_call (gv, Ews, gv _x_valid_params__sr, nullval, WANone).
Intros ws.
unfold wdict_arg. Intros.
simpl wdict_model in *.
match goal with H: series_facts no_dict ws |- _ => rename H into Hsf end.
match goal with H: wseries_wf ws |- _ => rename H into Hwf end.
pose proof Hsf as (Hbok & Hcok & HbL & HcL & Hnf & Htl & _).
assert (HnfZ: 1 <= Zlength (ws_frames ws) <= 4) by (rewrite Zlength_correct; lia).
change (Int.signed (Int.repr 0)) with 0.
change (Int.signed (Int.shl (Int.repr 1) (Int.repr 17))) with (2 ^ 17).
change (Int64.shl (Int64.repr 1) (Int64.repr (Int.unsigned (Int.repr 27)))) with (Int64.repr (2 ^ 27)).
forward_if (EX b': list Z,
  PROP (ck_agree (ws_frames ws) (ws_bytes ws) b'; mode <> 0 -> b' = ws_bytes ws)
  LOCAL (temp _documented (Vint (Int.repr 1)); temp _base (vl 0); temp _blim (vl (2 ^ 17));
         temp _wlim (vl (2 ^ 27)); temp _mode (Vint (Int.repr mode));
         lvar _zfh t_fh vz; lvar _in tin vi; lvar _out tout vo; gvars gv)
  SEP (WG gv; data_at Ews t_wseries (wseries_val (ws_ck ws b')) (gv _x_valid_params__sr);
       mem_mgr gv; zstd_globals gv; data_at_ Tsh t_fh vz; data_at_ Tsh tin vi; data_at_ Tsh tout vo;
       TT; has_ext tt)).
{ (* mode 0: the checksums *)
  match goal with H: mode = 0 |- _ => subst mode end.
  forward.
  forward_loop
    (EX k: Z, EX b': list Z,
     PROP (0 <= k <= Zlength (ws_frames ws); ck_agree (ws_frames ws) (ws_bytes ws) b')
     LOCAL (temp _k (Vint (Int.repr k)); temp _documented (Vint (Int.repr 1)); temp _base (vl 0);
            temp _blim (vl (2 ^ 17)); temp _wlim (vl (2 ^ 27)); temp _mode (Vint (Int.repr 0));
            lvar _zfh t_fh vz; lvar _in tin vi; lvar _out tout vo; gvars gv)
     SEP (WG gv; data_at Ews t_wseries (wseries_val (ws_ck ws b')) (gv _x_valid_params__sr);
          mem_mgr gv; zstd_globals gv; data_at_ Tsh t_fh vz; data_at_ Tsh tin vi; data_at_ Tsh tout vo;
          TT; has_ext tt))
  continue:
    (EX k: Z, EX b': list Z,
     PROP (0 <= k < Zlength (ws_frames ws); ck_agree (ws_frames ws) (ws_bytes ws) b')
     LOCAL (temp _k (Vint (Int.repr k)); temp _documented (Vint (Int.repr 1)); temp _base (vl 0);
            temp _blim (vl (2 ^ 17)); temp _wlim (vl (2 ^ 27)); temp _mode (Vint (Int.repr 0));
            lvar _zfh t_fh vz; lvar _in tin vi; lvar _out tout vo; gvars gv)
     SEP (WG gv; data_at Ews t_wseries (wseries_val (ws_ck ws b')) (gv _x_valid_params__sr);
          mem_mgr gv; zstd_globals gv; data_at_ Tsh t_fh vz; data_at_ Tsh tin vi; data_at_ Tsh tout vo;
          TT; has_ext tt)).
  { Exists 0 (ws_bytes ws). rewrite VPA_ck_self. entailer!. apply VPA_ck_refl; auto. }
  2: { Intros k b'. forward. Exists (k + 1) b'. entailer!. }
  Intros k b'.
  sep_apply (VP_sr_unfold7w (ws_ck ws b') (gv _x_valid_params__sr)). Intros.
  unfold VP_Rnf. forward.
  forward_if.
  2: { forward. fold (VP_Rnf (vu (Zlength (ws_frames (ws_ck ws b')))) (gv _x_valid_params__sr)).
       sep_apply (VP_sr_fold7w (ws_ck ws b') (gv _x_valid_params__sr)).
       Exists b'. entailer!. }
  fold (VP_Rnf (vu (Zlength (ws_frames (ws_ck ws b')))) (gv _x_valid_params__sr)).
  set (f := Znth k (ws_frames ws)).
  assert (EF: Znth k (map winfo_val (ws_frames (ws_ck ws b')) ++
                      Zrepeat (winfo_val winfo0) (4 - Zlength (ws_frames (ws_ck ws b')))) = winfo_val f)
    by (apply VPA_frame_f; simpl; lia).
  assert (Hinf: In f (ws_frames ws)) by (apply Znth_In; lia).
  unfold VP_Rf.
  forward. { VPA_fix_tc f. } VPA_fix f.
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _x_valid_params__t'3 (vb (negb (wi_skippable f) && wi_checksum f)) :: L)
      (SEPx R))) end.
  { forward. { VPA_fix_tc f. } VPA_fix f. forward. entailer!.
    destruct (wi_skippable f); [discriminate|]. destruct (wi_checksum f); reflexivity. }
  { forward. entailer!. destruct (wi_skippable f); [reflexivity|]. contradiction. }
  fold (VP_Rf (map winfo_val (ws_frames (ws_ck ws b')) ++
    Zrepeat (winfo_val winfo0) (4 - Zlength (ws_frames (ws_ck ws b')))) (gv _x_valid_params__sr)).
  sep_apply (VP_sr_fold7w (ws_ck ws b') (gv _x_valid_params__sr)).
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
    forward_if (EX c: bool, PROPx ((c = true -> wi_skippable f = false /\ wi_checksum f = true) :: P)
                 (LOCALx (temp _x_valid_params__t'4 (vb c) :: L) (SEPx R))) end.
  { forward_call 2. Intros r. forward. Exists (negb (r =? 0)). entailer!.
    split.
    - intros _. destruct (wi_skippable f), (wi_checksum f); simpl in *; auto; contradiction.
    - assert (r = 0 \/ r = 1) as [-> | ->] by lia; reflexivity. }
  { forward. Exists false. entailer!. }
  Intros c4.
  destruct c4.
  2: { forward_if; [lia|]. forward. Exists k b'. entailer!. }
  match goal with H: true = true -> _ |- _ => destruct (H eq_refl) as [Hsk Hck] end.
  destruct (VPA_frame_ck ws f Hsf Hwf Hinf Hsk Hck) as (Hst & Hsz & Hend).
  forward_if; [| discriminate].
  forward.
  forward_loop
    (EX j: Z, EX b2: list Z,
     PROP (0 <= j <= 4; ck_agree (ws_frames ws) (ws_bytes ws) b2)
     LOCAL (temp _j (Vint (Int.repr j)); temp _k (Vint (Int.repr k)); temp _documented (Vint (Int.repr 1));
            temp _base (vl 0); temp _blim (vl (2 ^ 17)); temp _wlim (vl (2 ^ 27)); temp _mode (Vint (Int.repr 0));
            lvar _zfh t_fh vz; lvar _in tin vi; lvar _out tout vo; gvars gv)
     SEP (data_at Ews t_wseries (wseries_val (ws_ck ws b2)) (gv _x_valid_params__sr); WG gv;
          mem_mgr gv; zstd_globals gv; data_at_ Tsh t_fh vz; data_at_ Tsh tin vi; data_at_ Tsh tout vo;
          TT; has_ext tt))
  continue:
    (EX j: Z, EX b2: list Z,
     PROP (0 <= j < 4; ck_agree (ws_frames ws) (ws_bytes ws) b2)
     LOCAL (temp _j (Vint (Int.repr j)); temp _k (Vint (Int.repr k)); temp _documented (Vint (Int.repr 1));
            temp _base (vl 0); temp _blim (vl (2 ^ 17)); temp _wlim (vl (2 ^ 27)); temp _mode (Vint (Int.repr 0));
            lvar _zfh t_fh vz; lvar _in tin vi; lvar _out tout vo; gvars gv)
     SEP (data_at Ews t_wseries (wseries_val (ws_ck ws b2)) (gv _x_valid_params__sr); WG gv;
          mem_mgr gv; zstd_globals gv; data_at_ Tsh t_fh vz; data_at_ Tsh tin vi; data_at_ Tsh tout vo;
          TT; has_ext tt))
  break:
    (EX b2: list Z,
     PROP (ck_agree (ws_frames ws) (ws_bytes ws) b2)
     LOCAL (temp _k (Vint (Int.repr k)); temp _documented (Vint (Int.repr 1));
            temp _base (vl 0); temp _blim (vl (2 ^ 17)); temp _wlim (vl (2 ^ 27)); temp _mode (Vint (Int.repr 0));
            lvar _zfh t_fh vz; lvar _in tin vi; lvar _out tout vo; gvars gv)
     SEP (data_at Ews t_wseries (wseries_val (ws_ck ws b2)) (gv _x_valid_params__sr); WG gv;
          mem_mgr gv; zstd_globals gv; data_at_ Tsh t_fh vz; data_at_ Tsh tin vi; data_at_ Tsh tout vo;
          TT; has_ext tt)).
  { Exists 0 b'. entailer!. }
  2: { Intros j b2. forward. Exists (j + 1) b2. entailer!. }
  2: { Intros b2. unfold POSTCONDITION, abbreviate, normal_ret_assert; cbn [RA_normal].
       Exists k b2. entailer!. }
  Intros j b2.
  forward_if.
  2: { forward. Exists b2. entailer!. }
  forward_call 256. Intros c.
  match goal with H: ck_agree _ _ b2 |- _ => rename H into Hb2 end.
  pose proof Hb2 as (Hlb2 & Hbb2 & _).
  sep_apply (VP_sr_unfold7w (ws_ck ws b2) (gv _x_valid_params__sr)). Intros.
  assert (EF2: Znth k (map winfo_val (ws_frames (ws_ck ws b2)) ++
                       Zrepeat (winfo_val winfo0) (4 - Zlength (ws_frames (ws_ck ws b2)))) = winfo_val f)
    by (apply VPA_frame_f; simpl; lia).
  unfold VP_Rf.
  forward. { VPA_fix_tc f. } VPA_fix f.
  forward. { VPA_fix_tc f. } VPA_fix f.
  fold (VP_Rf (map winfo_val (ws_frames (ws_ck ws b2)) ++
    Zrepeat (winfo_val winfo0) (4 - Zlength (ws_frames (ws_ck ws b2)))) (gv _x_valid_params__sr)).
  sep_apply (VP_sr_fold7w (ws_ck ws b2) (gv _x_valid_params__sr)).
  sep_apply (VPA_cell ws b2 (wi_start f + wi_size f - 4 + j) c (gv _x_valid_params__sr)); [unfold wi_end in *; lia | lia |]. Intros.
  forward.
  rewrite !VPA_zext8 by lia.
  sep_apply (wand_frame_elim
    (field_at Ews t_wseries (DOT _bytes SUB (wi_start f + wi_size f - 4 + j)) (Vint (Int.repr c))
       (gv _x_valid_params__sr))).
  Exists j (upd_Znth (wi_start f + wi_size f - 4 + j) b2 c). entailer!.
  apply (VPA_ck_upd _ _ _ f); auto; unfold wi_end in *; lia. }
{ forward. Exists (ws_bytes ws). rewrite VPA_ck_self. entailer!.
  apply VPA_ck_refl; auto. }
Intros b'.
match goal with H: ck_agree _ _ b' |- _ => rename H into Hck end.
match goal with H: mode <> 0 -> _ |- _ => rename H into Hb0 end.
pose proof Hck as (Hlb & Hbb & _).
forward_if (
  PROP (mode = 3 -> exists f, ws_frames ws = [f] /\ wi_skippable f = false)
  LOCAL (temp _documented (Vint (Int.repr 1)); temp _base (vl (vp_base mode)); temp _blim (vl (2 ^ 17));
         temp _wlim (vl (2 ^ 27)); temp _mode (Vint (Int.repr mode));
         lvar _zfh t_fh vz; lvar _in tin vi; lvar _out tout vo; gvars gv)
  SEP (WG gv; data_at Ews t_wseries (wseries_val (ws_ck ws b')) (gv _x_valid_params__sr);
       mem_mgr gv; zstd_globals gv; data_at_ Tsh t_fh vz; data_at_ Tsh tin vi; data_at_ Tsh tout vo;
       TT; has_ext tt)).
{ (* mode 3: one Zstandard frame *)
  match goal with H: mode = 3 |- _ => subst mode end.
  sep_apply (VP_sr_unfold7w (ws_ck ws b') (gv _x_valid_params__sr)). Intros.
  unfold VP_Rnf. forward.
  fold (VP_Rnf (vu (Zlength (ws_frames (ws_ck ws b')))) (gv _x_valid_params__sr)).
  set (f := Znth 0 (ws_frames ws)).
  assert (EF: Znth 0 (map winfo_val (ws_frames (ws_ck ws b')) ++
                      Zrepeat (winfo_val winfo0) (4 - Zlength (ws_frames (ws_ck ws b')))) = winfo_val f)
    by (apply VPA_frame_f; simpl; lia).
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _x_valid_params__t'6
      (vb ((Zlength (ws_frames ws) =? 1) && negb (wi_skippable f))) :: L) (SEPx R))) end.
  { unfold VP_Rf. forward. { VPA_fix_tc f. } VPA_fix f. forward.
    fold (VP_Rf (map winfo_val (ws_frames (ws_ck ws b')) ++
      Zrepeat (winfo_val winfo0) (4 - Zlength (ws_frames (ws_ck ws b')))) (gv _x_valid_params__sr)).
    entailer!. rewrite H0. destruct (wi_skippable f); reflexivity. }
  { forward. entailer!. destruct (Z.eqb_spec (Zlength (ws_frames ws)) 1); [contradiction | reflexivity]. }
  forward_call (Int.repr (if andb (Zlength (ws_frames ws) =? 1) (negb (wi_skippable f)) then 1 else 0)).
  forward.
  assert (Hm3: exists f0, ws_frames ws = [f0] /\ wi_skippable f0 = false).
  { match goal with H: Int.repr (if _ then 1 else 0) <> Int.zero |- _ => rename H into Ha end.
    destruct (Z.eqb_spec (Zlength (ws_frames ws)) 1) as [E1|E1];
      [| simpl in Ha; contradiction Ha; reflexivity].
    destruct (wi_skippable f) eqn:E2; [simpl in Ha; contradiction Ha; reflexivity|].
    subst f. destruct (ws_frames ws) as [|g [|h t]]; [list_solve | | list_solve].
    exists g. split; [reflexivity | exact E2]. }
  sep_apply (VP_sr_fold7w (ws_ck ws b') (gv _x_valid_params__sr)).
  change (Int.signed (Int.repr 4)) with 4.
  entailer!. }
{ forward. entailer!. unfold vp_base. destruct (Z.eqb_spec mode 3); [contradiction | reflexivity]. }
Intros.
match goal with H: mode = 3 -> _ |- _ => rename H into Hm3 end.
pose proof (VPA_base_lt mode ws b' Hsf Hlb Hm3) as Hbase.
assert (Hb0': 0 <= vp_base mode <= 4) by (unfold vp_base; destruct (mode =? 3); lia).
sep_apply (VP_sr_unfold7w (ws_ck ws b') (gv _x_valid_params__sr)). Intros.
unfold VP_Rn. forward. forward.
fold (VP_Rn (vl (Zlength (ws_bytes (ws_ck ws b')))) (gv _x_valid_params__sr)).
sep_apply (VP_bytes_borrow_w (ws_ck ws b') (gv _x_valid_params__sr) (vp_base mode)
  (Zlength (ws_bytes (ws_ck ws b')) - vp_base mode)); [simpl; lia..|]. Intros.
forward_call (gv, Ews, offset_val (vp_base mode) (gv _x_valid_params__sr),
  sublist (vp_base mode) (vp_base mode + (Zlength (ws_bytes (ws_ck ws b')) - vp_base mode)) (ws_bytes (ws_ck ws b'))).
{ entailer!. simpl. rewrite Zlength_sublist by (simpl; lia). f_equal; [| f_equal; f_equal; f_equal; lia].
  clear Frame. destruct (gv _x_valid_params__sr); try contradiction. unfold vl. simpl. f_equal. f_equal.
  change (Ptrofs.repr 1) with Ptrofs.one. rewrite Ptrofs.mul_commut, Ptrofs.mul_one.
  unfold Ptrofs.of_int64. rewrite Int64.unsigned_repr by rep_lia. reflexivity. }
{ simpl. rewrite Zlength_sublist by lia. split; [rep_lia|].
  unfold bytes_ok in *. apply Forall_sublist. auto. }
Intros src.
replace (sublist (vp_base mode) (vp_base mode + (Zlength (ws_bytes (ws_ck ws b')) - vp_base mode))
  (ws_bytes (ws_ck ws b'))) with (vp_src mode b') by (unfold vp_src; simpl; f_equal; lia).
assert (Hsrc: Zlength (vp_src mode b') = Zlength b' - vp_base mode)
  by (unfold vp_src; rewrite Zlength_sublist by lia; lia).
sep_apply (wand_frame_elim
  (data_at Ews (tarray tuchar (Zlength (vp_src mode b'))) (zbytes (vp_src mode b'))
     (offset_val (vp_base mode) (gv _x_valid_params__sr)))).
fold (@app val).
sep_apply (VP_sr_fold7w (ws_ck ws b') (gv _x_valid_params__sr)).
rewrite Z.max_r by lia. rewrite Z.sub_diag. change (Zrepeat Vundef 0) with (@nil val). rewrite app_nil_r.
rewrite sub64_repr. replace (Zlength (ws_bytes (ws_ck ws b')) - vp_base mode) with (Zlength (vp_src mode b'))
  by (simpl; lia).
forward_call gv.
Intros dctx.
assert (Hfacts: VP_SA_facts mode ws b').
{ unfold VP_SA_facts. split; [lia|]. do 5 (split; [auto|]). lia. }
match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
  forward_if (PROPx P (LOCALx (temp _x_valid_params__t'9 (Vint (Int.repr
      (if eq_dec src nullval then 1 else if eq_dec dctx nullval then 1 else 0))) :: L) (SEPx R))) end.
{ VPA_tc_null_test src. }
{ forward. destruct (eq_dec src nullval); [|contradiction]. entailer!. }
{ forward.
  { entailer!. apply denote_tc_test_eq_split; [|apply valid_pointer_null].
    destruct (eq_dec dctx nullval); [subst; apply valid_pointer_null|].
    eapply derives_trans; [|apply (VPA_vp (DC gv dctx dctx_init) TT dctx)]. cancel. }
  destruct (eq_dec src nullval); [contradiction|].
  destruct (eq_dec dctx nullval); entailer!;
    try reflexivity; destruct dctx; try contradiction;
    first [reflexivity | exfalso; simpl in PNdctx; subst; auto]. }
forward_if.
{ (* out of memory: free, return *)
  sep_apply (VPA_if_data_at_ Ews (tarray tuchar (Zlength (vp_src mode b'))) src (zbytes (vp_src mode b'))).
  forward_call (tarray tuchar (Zlength (vp_src mode b')), src, gv).
  destruct (eq_dec dctx nullval) as [Hd|Hd].
  - forward_call (gv, dctx, @None dctx_st).
    eapply semax_pre with (P' := PROP () LOCAL (lvar _zfh t_fh vz; lvar _in tin vi; lvar _out tout vo)
      SEP (data_at_ Tsh t_fh vz; data_at_ Tsh tin vi; data_at_ Tsh tout vo; TT)).
    { go_lower. apply andp_right; [apply prop_right; rewrite !eqb_type_refl; auto | cancel]. }
    forward. cancel.
  - sep_apply (andp_left1 (DC gv dctx dctx_init) (valid_pointer dctx) (DC gv dctx dctx_init) (derives_refl _)).
    forward_call (gv, dctx, Some dctx_init).
    eapply semax_pre with (P' := PROP () LOCAL (lvar _zfh t_fh vz; lvar _in tin vi; lvar _out tout vo)
      SEP (data_at_ Tsh t_fh vz; data_at_ Tsh tin vi; data_at_ Tsh tout vo; TT)).
    { go_lower. apply andp_right; [apply prop_right; rewrite !eqb_type_refl; auto | cancel]. }
    forward. cancel. }
match goal with H: Int.repr _ = Int.zero |- _ => rename H into Ht9 end.
change (EqDec_val src nullval) with (eq_dec src nullval) in Ht9.
change (EqDec_val dctx nullval) with (eq_dec dctx nullval) in Ht9.
destruct (eq_dec src nullval) as [|Hs]; [now apply VPA_repr1_neq0 in Ht9|].
destruct (eq_dec dctx nullval) as [|Hd]; [now apply VPA_repr1_neq0 in Ht9|].
clear Ht9.
sep_apply (andp_left1 (DC gv dctx dctx_init) (valid_pointer dctx) (DC gv dctx dctx_init) (derives_refl _)).
eapply semax_pre; [| apply (HK mode ws b' src dctx Hfacts (VPA_isptr src PNsrc Hs) (VPA_isptr dctx PNdctx Hd))].
unfold VP_SA. entailer!.
apply VPA_isptr; auto.
Qed.

End Seg.
