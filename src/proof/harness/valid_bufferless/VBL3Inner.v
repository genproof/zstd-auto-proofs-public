(* valid_bufferless: the body of the step loop (VBLInv.VL_inner_stmt). *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.harness.valid_bufferless.VBL3Inv.
Require Import Zstd.proof.model.ParamsDflt Zstd.proof.harness.valid_bufferless.VBL3InnerModel.

Local Notation ZCS := Zstd.proof.zstd.Base.CompSpecs.
Local Notation HCS := Zstd.proof.harness.valid_bufferless.HOK_valid_bufferless.CompSpecs.


(* ---------- lists ---------- *)

Lemma VLI_slice_sub (l: list Z) s n : 0 <= s -> 0 <= n -> s + n <= Zlength l ->
  slice l s n = sublist s (s + n) l.
Proof.
  intros Hs Hn Hl. unfold slice, sublist. rewrite skipn_firstn_comm. f_equal. lia.
Qed.

Lemma VLI_slice_Znth (l: list Z) s n x : 0 <= s -> 0 <= x < n -> s + n <= Zlength l ->
  Znth x (slice l s n) = Znth (s + x) l.
Proof.
  intros Hs Hx Hl. rewrite VLI_slice_sub by lia. rewrite Znth_sublist by lia. f_equal. lia.
Qed.

Lemma VLI_bytes_sub (l: list Z) a c : bytes_ok l -> 0 <= a <= c -> c <= Zlength l -> bytes_ok (sublist a c l).
Proof. intros Hb Ha Hc. unfold bytes_ok in *. apply Forall_sublist. exact Hb. Qed.

(* ---------- the source bytes: the piece exact_copy reads ---------- *)

Lemma VLI_src_split (l: list Z) (src: val) a w :
  0 <= a -> 0 <= w -> a + w <= Zlength l -> @field_compatible ZCS (tarray tuchar (Zlength l)) [] src ->
  @data_at ZCS Ews (tarray tuchar (Zlength l)) (zbytes l) src =
  (@data_at ZCS Ews (tarray tuchar a) (zbytes (sublist 0 a l)) src *
   @data_at HCS Ews (tarray tuchar w) (zbytes (sublist a (a + w) l)) (offset_val a src) *
   @data_at ZCS Ews (tarray tuchar (Zlength l - (a + w))) (zbytes (sublist (a + w) (Zlength l) l))
     (offset_val (a + w) src))%logic.
Proof.
  intros Ha Hw Hl Hf. unfold tarray.
  rewrite (split3_data_at_Tarray_tuchar Ews (Zlength l) a (a + w)) by (rewrite ?Zlength_map; lia).
  rewrite !field_address0_offset by auto with field_compatible.
  simpl nested_field_offset. rewrite !Z.mul_1_l, !Z.add_0_l.
  replace (a + w - a) with w by lia. rewrite !sublist_map.
  rewrite (VLB_cs ZCS HCS Ews w). reflexivity.
Qed.

Lemma VLI_src_merge (l: list Z) (src: val) a w :
  0 <= a -> 0 <= w -> a + w <= Zlength l -> @field_compatible ZCS (tarray tuchar (Zlength l)) [] src ->
  @data_at ZCS Ews (tarray tuchar a) (zbytes (sublist 0 a l)) src *
  @data_at HCS Ews (tarray tuchar w) (zbytes (sublist a (a + w) l)) (offset_val a src) *
  @data_at ZCS Ews (tarray tuchar (Zlength l - (a + w))) (zbytes (sublist (a + w) (Zlength l) l))
     (offset_val (a + w) src)
  |-- @data_at ZCS Ews (tarray tuchar (Zlength l)) (zbytes l) src.
Proof. intros. rewrite (VLI_src_split l src a w) by auto. apply derives_refl. Qed.

(* ---------- the call's buffers ---------- *)

Lemma VLI_buf_ok_pos W n p : 0 < n -> buf_ok W Ews n p.
Proof.
  intros Hn. unfold buf_ok.
  destruct (isptr_dec p) as [Hp|Hp].
  - destruct p; try contradiction. apply andp_right; apply sepcon_weak_valid_pointer2.
    + VLB_piece n 0.
    + VLB_piece n n.
  - rewrite data_at__isptr. normalize.
Qed.

Lemma VLI_dict_buf_ok src n bb ob cap pos mode q db dd :
  0 <= pos <= cap -> @field_compatible ZCS (tarray tuchar (cap + 1 + Zlength db)) [] (Vptr bb ob) -> VL_ddok db dd ->
  dict_buf_ok (VLB_W src n (Vptr bb ob) cap) Ews (VL_dr mode q (offset_val (cap + 1) (Vptr bb ob)) db dd) Ews
    (cap - pos) (offset_val pos (Vptr bb ob)).
Proof.
  intros Hp Hf Hdd. pose proof (Zlength_nonneg db). unfold VL_dr, dict_buf_ok.
  destruct (mode =? 0); [exact I|]. destruct (mode =? 1); [| cbn; rewrite (proj2 Hdd); exact I].
  cbn [dr_src dr_bytes]. left. split; [simpl; unfold sameblock; apply peq_true |].
  split; [| apply VLB_buf_ok_dict; simpl; auto; lia].
  destruct Hf as (_ & _ & Hsz & _). simpl in Hsz. rewrite Z.max_r in Hsz by lia.
  simpl. rewrite !Ptrofs.add_unsigned.
  rewrite (Ptrofs.unsigned_repr (cap + 1)) by rep_lia. rewrite (Ptrofs.unsigned_repr pos) by rep_lia.
  rewrite !Ptrofs.unsigned_repr by rep_lia. lia.
Qed.

(* ---------- the dictionary's memory (dict_res) ---------- *)

Definition VLI_drest (mode: Z) (db: list Z) (p: val) : mpred :=
  if mode =? 1 then emp else @data_at ZCS Ews (tarray tuchar (Zlength db)) (zbytes db) p.

Lemma VLI_dict_res_eq DD gv mode q p db dd : 0 <= mode < 3 -> VL_qok mode q -> VL_ddok db dd ->
  (VL_qres DD gv q dd * @data_at ZCS Ews (tarray tuchar (Zlength db)) (zbytes db) p)%logic =
  (dict_res DD gv Ews (VL_dr mode q p db dd) * VLI_drest mode db p)%logic.
Proof.
  intros Hm (Hq2 & Hqn) Hdd. unfold VL_qres, VL_dr, VLI_drest.
  destruct (Z.eqb_spec mode 0).
  - subst. rewrite Hqn by lia. rewrite if_true by auto. simpl. rewrite !emp_sepcon. reflexivity.
  - destruct (Z.eqb_spec mode 1).
    + subst. rewrite Hqn by lia. rewrite if_true by auto. simpl. rewrite emp_sepcon, sepcon_emp. reflexivity.
    + assert (mode = 2) by lia. subst. specialize (Hq2 eq_refl).
      rewrite if_false by (destruct q; simpl in Hq2; try contradiction; discriminate).
      unfold dict_res, ddict_ref, ddict_res. simpl. rewrite (proj2 Hdd). rewrite !sepcon_emp. reflexivity.
Qed.

Lemma VLI_dict_take DD gv mode q p db dd : 0 <= mode < 3 -> VL_qok mode q -> VL_ddok db dd ->
  VL_qres DD gv q dd * @data_at ZCS Ews (tarray tuchar (Zlength db)) (zbytes db) p |--
  dict_res DD gv Ews (VL_dr mode q p db dd) * VLI_drest mode db p.
Proof. intros. rewrite (VLI_dict_res_eq DD gv mode q p db dd) by auto. apply derives_refl. Qed.

Lemma VLI_dict_back DD gv mode q p db dd : 0 <= mode < 3 -> VL_qok mode q -> VL_ddok db dd ->
  dict_res DD gv Ews (VL_dr mode q p db dd) * VLI_drest mode db p |--
  VL_qres DD gv q dd * @data_at ZCS Ews (tarray tuchar (Zlength db)) (zbytes db) p.
Proof. intros. rewrite (VLI_dict_res_eq DD gv mode q p db dd) by auto. apply derives_refl. Qed.

Lemma VLI_dm mode q p db dd dm : 0 <= mode < 3 -> VL_dfacts mode db dm -> VL_ddok db dd ->
  dictref_model (VL_dr mode q p db dd) = Some dm.
Proof.
  intros Hm [(E0 & -> & ->) | (En & _ & _ & Ha)] Hdd.
  - subst. reflexivity.
  - unfold VL_dr. destruct (Z.eqb_spec mode 0); [lia|]. destruct (mode =? 1); [exact Ha|].
    cbn. rewrite (proj1 Hdd). exact Ha.
Qed.

(* ---------- the model ---------- *)

Lemma VLI_within ws k : 0 <= k < Zlength (ws_frames ws) -> wi_big (VL_f ws k) = true ->
  within_oneshot_b (ws_frames ws) = false.
Proof.
  intros Hk Hb. unfold within_oneshot_b. apply Bool.not_true_is_false. intro H.
  rewrite forallb_forall in H. assert (Hin: In (VL_f ws k) (ws_frames ws)).
  { unfold VL_f. apply nth_In. rewrite Zlength_correct in Hk. lia. }
  specialize (H _ Hin). rewrite Hb in H. discriminate.
Qed.

Lemma VLI_ok_step dm ws k i b b' out :
  series_facts dm ws -> wseries_wf ws -> 0 <= k < Zlength (ws_frames ws) ->
  vbl_reach dm (wi_bytes ws (VL_f ws k)) i b -> 0 < bs_expect b -> i + bs_expect b <= wi_size (VL_f ws k) ->
  bl_step md_dflt dm b (slice (wi_bytes ws (VL_f ws k)) i (bs_expect b)) = BLOk b' out ->
  vbl_reach dm (wi_bytes ws (VL_f ws k)) (i + bs_expect b) b' /\ bs_out b' = bs_out b ++ out /\
  Zlength (bs_out b) + Zlength out <= wi_csize (VL_f ws k) /\
  (forall j, 0 <= j < Zlength out ->
     Znth j out = Znth (wi_cstart (VL_f ws k) + Zlength (bs_out b) + j) (ws_content ws)).
Proof.
  intros Hs Hw Hk Hr He Hle Hst.
  assert (Hk': (Z.to_nat k < length (ws_frames ws))%nat) by (rewrite Zlength_correct in Hk; lia).
  pose proof (vbl_frame_bounds dm ws (Z.to_nat k) Hs Hw Hk') as Hbd. cbv zeta in Hbd.
  change (nth (Z.to_nat k) (ws_frames ws) winfo0) with (VL_f ws k) in Hbd.
  destruct Hbd as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
  assert (Hr': vbl_reach dm (wi_bytes ws (VL_f ws k)) (i + bs_expect b) b').
  { apply (vbl_reach_step dm _ i b b' out Hr He); [rewrite B7; exact Hle | exact Hst]. }
  pose proof (bl_step_out _ _ _ _ _ _ Hst) as Eo.
  pose proof (vbi_reach_out dm ws (Z.to_nat k) _ b' Hs Hw Hk' Hr') as (O1 & O2).
  change (nth (Z.to_nat k) (ws_frames ws) winfo0) with (VL_f ws k) in O1, O2.
  rewrite Eo, Zlength_app in O1.
  split; [exact Hr'|]. split; [exact Eo|]. split; [exact O1|].
  intros j Hj. pose proof (Zlength_nonneg (bs_out b)).
  transitivity (Znth (Zlength (bs_out b) + j) (bs_out b')).
  { rewrite Eo. rewrite app_Znth2 by lia. f_equal. lia. }
  rewrite O2. rewrite Eo, Zlength_app.
  rewrite VLI_slice_Znth by (try rewrite B8; lia).
  unfold wi_content. rewrite VLI_slice_Znth by lia. f_equal. lia.
Qed.

Lemma VLI_c_eq ws f i w : 0 <= wi_start f -> 0 <= i -> 0 <= w -> i + w <= wi_size f ->
  wi_start f + wi_size f <= Zlength (ws_bytes ws) ->
  slice (wi_bytes ws f) i w = sublist (wi_start f + i) (wi_start f + i + w) (ws_bytes ws).
Proof.
  intros H1 H2 H3 H4 H5. unfold wi_bytes. rewrite (VLI_slice_sub (ws_bytes ws)) by lia.
  rewrite VLI_slice_sub by (try rewrite Zlength_sublist by lia; lia).
  rewrite sublist_sublist by lia. f_equal; lia.
Qed.


(* ---------- sr: borrowing frame k and the content ---------- *)

Lemma VLI_f_split (sh: share) (p: val) (l: list (reptype t_winfo)) (i: Z) : 0 <= i < 4 -> Zlength l = 4 ->
  @field_at HCS sh t_wseries (DOT _f) l p =
  (@array_at HCS sh t_wseries (DOT _f) 0 i (sublist 0 i l) p *
   @data_at HCS sh t_winfo (Znth i l) (@field_address HCS t_wseries (DOT _f SUB i) p) *
   @array_at HCS sh t_wseries (DOT _f) (i + 1) 4 (sublist (i + 1) 4 l) p)%logic.
Proof.
  intros.
  erewrite field_at_Tarray; [ | | reflexivity | lia | apply JMeq_refl]; [ | split; [simpl; auto | compute; auto]].
  erewrite (split3seg_array_at sh t_wseries (DOT _f) 0 i (i + 1) 4); [ | lia | lia | lia | ].
  2: { change (Zlength l = 4 - 0). lia. }
  rewrite !Z.sub_0_r. rewrite sublist_len_1 by (change (0 <= i < Zlength l); lia).
  erewrite array_at_len_1 by apply JMeq_refl.
  rewrite field_at_data_at. reflexivity.
  simpl; tauto.
Qed.

Lemma VLI_F_len (fs: list winfo) : Zlength fs <= 4 ->
  Zlength (map winfo_val fs ++ Zrepeat (winfo_val winfo0) (4 - Zlength fs)) = 4.
Proof. intros. rewrite Zlength_app, Zlength_map, Zlength_Zrepeat by lia. lia. Qed.

Lemma VLI_f_nth ws k d : 0 <= k < Zlength (ws_frames ws) ->
  @Znth (reptype t_winfo) d k (map winfo_val (ws_frames ws) ++ Zrepeat (winfo_val winfo0) (4 - Zlength (ws_frames ws)))
  = winfo_val (VL_f ws k).
Proof.
  intros Hk. rewrite app_Znth1 by (rewrite Zlength_map; lia).
  unfold Znth. rewrite if_false by lia. unfold VL_f.
  rewrite nth_indep with (d' := winfo_val winfo0) by (rewrite length_map; rewrite Zlength_correct in Hk; lia).
  apply map_nth.
Qed.

Lemma VLI_take_f ws p k : 0 <= k < Zlength (ws_frames ws) -> Zlength (ws_frames ws) <= 4 ->
  Zlength (ws_bytes ws) <= 2 ^ 19 ->
  @data_at HCS Ews t_wseries (wseries_val ws) p |--
  @data_at HCS Ews t_winfo (winfo_val (VL_f ws k)) (@field_address HCS t_wseries (DOT _f SUB k) p) *
  (@data_at HCS Ews t_winfo (winfo_val (VL_f ws k)) (@field_address HCS t_wseries (DOT _f SUB k) p) -*
   @data_at HCS Ews t_wseries (wseries_val ws) p).
Proof.
  intros Hk Hf Hb. pose proof (VLB_ws_unfold ws p Hb) as U. pose proof (VLB_ws_fold ws p Hb) as F.
  unfold VLB_sr_rest in U, F.
  rewrite (VLI_f_split Ews p _ k) in U, F by (try apply VLI_F_len; lia).
  rewrite VLI_f_nth in U, F by lia.
  eapply derives_trans; [exact U|]. cancel.
  rewrite <- wand_sepcon_adjoint. eapply derives_trans; [| exact F]. cancel.
Qed.

Lemma VLI_fc_content p : @field_compatible HCS t_wseries [] p -> @field_compatible HCS t_wseries (DOT _content) p.
Proof.
  intros FC. apply field_compatible_cons. split; [compute; repeat (first [left; reflexivity | right]) | exact FC].
Qed.

Lemma VLI_take_content ws p : Zlength (ws_bytes ws) <= 2 ^ 19 -> Zlength (ws_content ws) <= 2 ^ 18 ->
  @field_compatible HCS t_wseries [] p ->
  @data_at HCS Ews t_wseries (wseries_val ws) p |--
  @data_at HCS Ews (tarray tuchar (Zlength (ws_content ws))) (zbytes (ws_content ws))
    (@field_address HCS t_wseries (DOT _content) p) *
  (@data_at HCS Ews (tarray tuchar (Zlength (ws_content ws))) (zbytes (ws_content ws))
     (@field_address HCS t_wseries (DOT _content) p) -*
   @data_at HCS Ews t_wseries (wseries_val ws) p).
Proof.
  intros Hb Hc FC. pose proof (VLB_ws_unfold ws p Hb) as U. pose proof (VLB_ws_fold ws p Hb) as F.
  rewrite (VLI_content_split ws p Hc (VLI_fc_content p FC)) in U, F.
  eapply derives_trans; [exact U|]. cancel.
  rewrite <- wand_sepcon_adjoint. eapply derives_trans; [| exact F]. cancel.
Qed.

Lemma VLI_fc_arr (cs1 cs2: compspecs) n m p : 0 <= n <= m -> @field_compatible cs1 (tarray tuchar m) [] p ->
  @field_compatible cs2 (tarray tuchar n) [] p.
Proof.
  intros Hn Hf. apply (@field_compatible_change_composite cs1 cs2 (VLB_cce cs1 cs2)); [reflexivity |].
  eapply field_compatible_array_smaller0; [exact Hf | lia].
Qed.

Lemma VLI_fst_winfo f : (let (x, _) := winfo_val f in x) = vb (wi_skippable f).
Proof. reflexivity. Qed.

Lemma VLI_oc_at (l: list val) (o: list Z) p r j :
  sublist p (p + r) l = zbytes o -> r = Zlength o -> 0 <= p -> p + r <= Zlength l -> 0 <= j < r ->
  Znth (p + j) l = Vint (Int.repr (Znth j o)).
Proof.
  intros Hs Hr Hp Hl Hj.
  replace (Znth (p + j) l) with (Znth j (sublist p (p + r) l)) by (rewrite Znth_sublist by lia; f_equal; lia).
  rewrite Hs. rewrite Znth_map by lia. reflexivity.
Qed.

Lemma VLI_ptr_idx b o x n : 0 <= x < n -> field_compatible (tarray tuchar n) [] (Vptr b o) ->
  Vptr b (Ptrofs.add o (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_int64 (Int64.repr x)))) =
  field_address (tarray tuchar n) (SUB x) (Vptr b o).
Proof.
  intros Hx Hf. pose proof Hf as (_ & _ & Hsz & _). simpl in Hsz. rewrite Z.max_r in Hsz by lia.
  pose proof (Ptrofs.unsigned_range o). change Ptrofs.modulus with (2 ^ 64) in *.
  rewrite field_address_offset by auto with field_compatible. simpl. f_equal. f_equal.
  rewrite (Ptrofs.mul_commut (Ptrofs.repr 1)), Ptrofs.mul_one. unfold Ptrofs.of_int64.
  rewrite Int64.unsigned_repr by rep_lia. f_equal. lia.
Qed.

Lemma VLI_tc_byte l i : bytes_ok l -> 0 <= i < Zlength l -> tc_val tuchar (Vint (Int.repr (Znth i l))).
Proof.
  intros Hb Hi. unfold bytes_ok in Hb. pose proof (proj1 (Forall_Znth _ _) Hb i Hi) as Hx. unfold is_byte in Hx.
  simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia.
Qed.

Lemma VLI_content_idx p x n : 0 <= x < n -> n <= 2 ^ 18 ->
  @field_compatible HCS t_wseries [] p ->
  @field_compatible HCS (tarray tuchar n) [] (@field_address HCS t_wseries (DOT _content) p) ->
  offset_val (524296 + x) p =
  @field_address HCS (tarray tuchar n) (SUB x) (@field_address HCS t_wseries (DOT _content) p).
Proof.
  intros Hx Hn F1 F2.
  rewrite (field_address_offset (tarray tuchar n)) by auto with field_compatible.
  rewrite (field_address_offset t_wseries (DOT _content)) by (apply VLI_fc_content; auto).
  change (nested_field_offset t_wseries (DOT _content)) with 524296.
  rewrite offset_offset_val. f_equal. simpl. lia.
Qed.

Ltac VLI_ic :=
  match goal with
  | H: not (@eq int _ _) |- _ => apply H; reflexivity
  | H: @eq int _ _ |- _ => vm_compute in H; discriminate H
  end.

Ltac VLI_tc :=
  repeat match goal with
  | |- context [zeq ?a ?b] => destruct (zeq a b)
  | |- context [?a <=? ?b] =>
      let E := fresh "E" in destruct (a <=? b) eqn:E; [apply Z.leb_le in E | apply Z.leb_gt in E]
  | H: context [?a <=? ?b] |- _ =>
      let E := fresh "E" in destruct (a <=? b) eqn:E; [apply Z.leb_le in E | apply Z.leb_gt in E]
  end;
  try match goal with
      | H: not (@eq int _ _) |- _ => exfalso; apply H; reflexivity
      | H: @eq int _ _ |- _ => exfalso; vm_compute in H; discriminate H
      end;
  try lia; try reflexivity.

Lemma VL_inner_ok : VL_inner_stmt.
Proof.
  intros Espec DC DD WG WDS gv ws db dd dm mode src buf dctx q k R Hh Hk Hq Hdd.
  destruct R as [R1 R2 R3 R4]. unfold loop1_ret_assert, overridePost.
  simplify_func_tycontext. unfold VL_inner_s, VL_inner, VL_sep, VL_loc. abbreviate_semax.
  Intros i b ba oc.
  destruct Hh as (Hm & Hsf & Hwf & Hdf & (bs & os & ->) & (bb & ob & ->) & (bd & od & ->) & Hfs & Hfb).
  pose proof Hsf as (Hbok & Hcok & Hnb & Hnc & Hnf & _).
  assert (Hk': (Z.to_nat k < length (ws_frames ws))%nat) by (rewrite Zlength_correct in Hk; lia).
  pose proof (vbl_frame_bounds dm ws (Z.to_nat k) Hsf Hwf Hk') as Hbd. cbv zeta in Hbd.
  change (nth (Z.to_nat k) (ws_frames ws) winfo0) with (VL_f ws k) in Hbd.
  destruct Hbd as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
  pose proof (vbi_reach_out dm ws (Z.to_nat k) i b Hsf Hwf Hk' H) as Hout. cbv zeta in Hout.
  change (nth (Z.to_nat k) (ws_frames ws) winfo0) with (VL_f ws k) in Hout.
  destruct Hout as (O1 & O2).
  assert (Hi: 0 <= i <= wi_size (VL_f ws k)) by (destruct H as (Hi & _); rewrite B7 in Hi; exact Hi).
  pose proof (Zlength_nonneg (bs_out b)).
  forward_call (gv, Vptr bd od, set_ex (set_bl dctx_init (Some ba)) false, ba).
  forward_call (gv, Vptr bd od, set_ex (set_bl dctx_init (Some ba)) false, ba).
  Intros t.
  forward_if (temp _x_valid_bufferless__t'17 (Vint (if t <=? 1 then Int.one else Int.zero))).
  { forward. entailer!; VLI_tc. }
  { forward. entailer!; VLI_tc. }
  forward_if (temp _x_valid_bufferless__t'18 (Vint (if t <=? 2 then Int.one else Int.zero))).
  { forward. entailer!; VLI_tc. }
  { forward. entailer!; VLI_tc. }
  forward_if (temp _x_valid_bufferless__t'19 (Vint (if t <=? 3 then Int.one else Int.zero))).
  { forward. entailer!; VLI_tc. }
  { forward. entailer!; VLI_tc. }
  forward_if (temp _x_valid_bufferless__t'20 (Vint (if t <=? 4 then Int.one else Int.zero))).
  { forward. entailer!; VLI_tc. }
  { forward. entailer!; VLI_tc. }
  forward_if (temp _x_valid_bufferless__t'21 (Vint Int.one)).
  { forward. entailer!; VLI_tc. }
  { forward. entailer!; VLI_tc. }
  forward_call Int.one.
  forward_if.
  { (* want = 0: the frame's end *)
    assert (Hw0: ba_expect ba = 0).
    { match goal with Hx: Int64.repr _ = Int64.zero |- _ =>
        change Int64.zero with (Int64.repr 0) in Hx; apply repr_inj_unsigned64 in Hx; rep_lia end. }
    rewrite H1 in Hw0.
    destruct (vbi_end dm ws (Z.to_nat k) i b Hsf Hwf Hk' H Hw0) as (Ei & Eo).
    change (nth (Z.to_nat k) (ws_frames ws) winfo0) with (VL_f ws k) in Ei, Eo.
    assert (Elo: Zlength (bs_out b) = wi_csize (VL_f ws k)) by (rewrite Eo; exact B8).
    rewrite Ei, Elo.
    forward_if (temp _x_valid_bufferless__t'22 (Vint Int.one)).
    { forward. entailer!. }
    { exfalso. auto. }
    forward_call Int.one.
    forward.
    unfold VL_inner_exit, VL_loc, VL_sep.
    Exists 0 (wi_start (VL_f ws k) + wi_size (VL_f ws k)) (wi_cstart (VL_f ws k) + wi_csize (VL_f ws k)) (Some ba) oc false.
    entailer!. }
  (* want <> 0: the step *)
  assert (Hw0: bs_expect b <> 0).
  { rewrite <- H1. intro E. match goal with Hx: Int64.repr (ba_expect ba) <> _ |- _ => apply Hx end.
    rewrite E. reflexivity. }
  destruct (vbi_step dm ws (Z.to_nat k) i b Hsf Hwf Hk' H Hw0) as (S1 & S2 & S3).
  change (nth (Z.to_nat k) (ws_frames ws) winfo0) with (VL_f ws k) in S2, S3.
  rewrite H1.
  forward_call Int.one.
  { entailer!. simpl. rewrite VLI_ltu64 by rep_lia.
    replace (_ <? _) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }

  set (s0 := wi_start (VL_f ws k) + i).
  set (w := bs_expect b).
  assert (Hfs': @field_compatible ZCS (tarray tuchar (Zlength (ws_bytes ws))) [] (Vptr bs os)).
  { apply (VLI_fc_arr HCS ZCS (Zlength (ws_bytes ws)) (Z.max 1 (Zlength (ws_bytes ws)))); [lia | exact Hfs]. }
  rewrite (VLI_src_split (ws_bytes ws) (Vptr bs os) s0 w) by (auto; unfold s0, w; lia).
  Intros.
  assert (Hcl: Zlength (sublist s0 (s0 + w) (ws_bytes ws)) = w) by (rewrite Zlength_sublist; unfold s0, w in *; lia).
  forward_call (gv, Ews, offset_val s0 (Vptr bs os), sublist s0 (s0 + w) (ws_bytes ws)).
  { entailer!. simpl. rewrite Zlength_sublist by lia.
    f_equal; [| do 3 f_equal; lia].
    f_equal. rewrite (Ptrofs.mul_commut (Ptrofs.repr 1)), Ptrofs.mul_one. unfold Ptrofs.of_int64.
    rewrite Int64.unsigned_repr by rep_lia. reflexivity. }
  { rewrite Hcl. cancel. }
  { apply VLI_bytes_sub; auto; unfold s0, w in *; lia. }
  rewrite Hcl. Intros ib.
  assert (Hs0: 0 <= s0) by (unfold s0; lia). assert (Hw: 0 < w) by (unfold w; lia).
  assert (Hsw: s0 + w <= Zlength (ws_bytes ws)) by (unfold s0, w in *; lia).
  sep_apply (VLI_src_merge (ws_bytes ws) (Vptr bs os) s0 w Hs0 ltac:(lia) Hsw Hfs').
  rewrite Z.max_r by (unfold w; lia). rewrite Z.sub_diag. change (Zrepeat Vundef 0) with (@nil val).
  rewrite app_nil_r.
  destruct (eq_dec ib nullval) as [Hib|Hib].
  { (* exact_copy out of memory *)
    subst ib. forward_if; [| VL_kill].
    forward. forward.
    unfold VL_inner_exit, VL_loc, VL_sep.
    Exists 1 s0 (wi_cstart (VL_f ws k) + Zlength (bs_out b)) (Some ba) oc false.
    entailer!. }
  forward_if; [contradiction |].
  try rewrite if_false by exact Hib. Intros.
  set (pos := wi_cstart (VL_f ws k) + Zlength (bs_out b)) in *.
  set (cap := Zlength (ws_content ws)) in *.
  set (c := sublist s0 (s0 + w) (ws_bytes ws)).
  assert (Hpos: 0 <= pos <= cap) by (unfold pos, cap; lia).
  sep_apply (VLI_dict_take DD gv mode q (offset_val (cap + 1) (Vptr bb ob)) db dd Hm Hq Hdd).
  rewrite <- H2.
  rewrite (VLB_cs HCS ZCS Ews w).
  assert (Hc: Zlength c = w) by exact Hcl.
  assert (Hpib: isptr ib).
  { match goal with H: is_pointer_or_null ib |- _ => destruct ib; simpl in H; try contradiction; auto;
      subst; exfalso; apply Hib; reflexivity end. }
  destruct ib as [| | | | | bi oi]; try contradiction.
  forward_call (VLB_W (Vptr bs os) (Zlength (ws_bytes ws)) (Vptr bb ob) cap, gv, Vptr bd od,
                set_ex (set_bl dctx_init (Some ba)) false, ba, Ews, Ews, Vptr bb ob, cap, pos, oc, Ews, Vptr bi oi, c).
  { entailer!. simpl. rewrite (Ptrofs.mul_commut (Ptrofs.repr 1)), Ptrofs.mul_one. unfold Ptrofs.of_int64.
    rewrite Int64.unsigned_repr by rep_lia. rewrite Hc. reflexivity. }
  { rewrite Hc. cancel. }
  { split; [apply VLB_buf_ok_dst; simpl; auto; lia |].
    split; [apply VLI_buf_ok_pos; lia |].
    split; [rewrite H2; apply VLI_dict_buf_ok; [lia | | exact Hdd]; [exact (VLI_fc_arr _ _ (cap + 1 + Zlength db) (cap + 1 + Zlength db) _ ltac:(pose proof (Zlength_nonneg db); lia) Hfb)] |].
    unfold c; apply VLI_bytes_sub; auto; lia. }
  Intros vret. destruct vret as [[r oc'] ba']. cbn [fst snd] in *.
  match goal with Hx: bl_claim _ _ _ _ _ _ _ _ |- _ => rename Hx into Hclaim end.
  change (dmode_of (dc_par (set_ex (set_bl dctx_init (Some ba)) false))) with md_dflt in Hclaim.
  unfold bl_claim in Hclaim. rewrite H0, H2, (VLI_dm mode q _ db dd dm Hm Hdf Hdd) in Hclaim.
  rewrite Hc in Hclaim. specialize (Hclaim eq_refl).
  rewrite (VLI_c_eq ws (VL_f ws k) i (bs_expect b)) in S3 by lia. fold s0 w c in S3.
  rewrite Hc.
  forward_call (tarray tuchar w, Vptr bi oi, gv).
  { rewrite if_false by discriminate.
    sep_apply (@data_at_data_at_ ZCS Ews (tarray tuchar w) (zbytes c) (Vptr bi oi)).
    rewrite (VLB_cs_ ZCS HCS Ews w). cancel. }
  forward_call r.
  rewrite H2. sep_apply (VLI_dict_back DD gv mode q (offset_val (cap + 1) (Vptr bb ob)) db dd Hm Hq Hdd). Intros.
  assert (Hcs: c = slice (wi_bytes ws (VL_f ws k)) i (bs_expect b))
    by (unfold c, s0, w; rewrite VLI_c_eq by lia; reflexivity).
  destruct S3 as [(b' & out & Est & Hsk) | (Hbig & Est)]; rewrite Est in Hclaim.
  2:{ (* a frame beyond zstd's window range: the error *)
    rewrite Hclaim.
    forward_if; [| exfalso; VLI_ic].
    forward_call (Ews, VL_sr gv, ws).
    rewrite (VLI_within ws k Hk Hbig).
    forward_call Int.one.
    forward. forward.
    change (set_ex (set_bl (set_ex (set_bl dctx_init (Some ba)) false) None) false) with (set_ex (set_bl dctx_init None) false).
    unfold VL_inner_exit, VL_loc, VL_sep.
    Exists 1 s0 pos (@None blabs) oc' false.
    entailer!. }
  (* the step succeeds *)
  rewrite Hcs in Est.
  destruct (VLI_ok_step dm ws k i b b' out Hsf Hwf Hk H S1 S2 Est) as (Rr & Eo & Hlen & Hcont).
  rewrite <- Hcs in Est.
  destruct Hclaim as (Cok & Cerr).
  destruct (is_error_code r) eqn:Er.
  { exfalso. specialize (Cerr eq_refl). unfold pos, cap in *; lia. }
  destruct (Cok eq_refl) as (Er' & Esub & Est').
  destruct (H14 eq_refl) as (Hr1 & Hcb & Hd' & Ho' & Hh' & He').
  clear Cok Cerr H14.
  forward_if; [exfalso; VLI_ic |].
  forward_call Int.one.
  { entailer!. simpl. rewrite VLI_ltu64 by rep_lia.
    replace (_ <? _) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
  assert (Hnf4: Zlength (ws_frames ws) <= 4) by (rewrite Zlength_correct; lia).
  sep_apply (VLI_take_f ws (VL_sr gv) k Hk Hnf4 Hnb). Intros.
  assert_PROP (offset_val 0 (field_address t_wseries [ArraySubsc k; StructField _f] (VL_sr gv)) =
               field_address t_winfo (DOT _skippable) (field_address t_wseries [ArraySubsc k; StructField _f] (VL_sr gv)))
    as Efa.
  { entailer!. rewrite (field_address_offset t_winfo (DOT _skippable)) by auto with field_compatible.
    change (nested_field_offset t_winfo (DOT _skippable)) with 0.
    rewrite isptr_offset_val_zero by auto with field_compatible. reflexivity. }
  forward.
  rewrite VLI_fst_winfo.
  sep_apply (wand_frame_elim
    (@data_at HCS Ews t_winfo (winfo_val (VL_f ws k)) (field_address t_wseries [ArraySubsc k; StructField _f] (VL_sr gv)))
    (@data_at HCS Ews t_wseries (wseries_val ws) (VL_sr gv))).
  forward_if (temp _x_valid_bufferless__t'29 (vb (wi_skippable (VL_f ws k)))).
  { destruct (wi_skippable (VL_f ws k)) eqn:Esk; [| exfalso; VLI_ic].
    rewrite (Hsk eq_refl) in *.
    forward_call Int.one.
    all: entailer!. }
  { forward. entailer!. }
  (* the bytes delivered are the content *)
  assert_PROP (@field_compatible HCS t_wseries [] (VL_sr gv)) as FCsr by entailer!.
  subst cap.
  sep_apply (VLI_take_content ws (VL_sr gv) Hnb Hnc FCsr). Intros.
  rewrite (VLB_cs ZCS HCS Ews (Zlength (ws_content ws)) oc' (Vptr bb ob)).
  forward.
  match goal with |- semax _ (PROPx _ (LOCALx (_ :: ?Q) (SEPx ?S))) _ _ =>
    forward_loop (EX j: Z, PROPx [0 <= j <= r] (LOCALx (temp _j (Vlong (Int64.repr j)) :: Q) (SEPx S)))
      continue: (EX j: Z, PROPx [0 <= j < r] (LOCALx (temp _j (Vlong (Int64.repr j)) :: Q) (SEPx S)))
      break: (PROPx [] (LOCALx Q (SEPx S)))
  end.
  { Exists 0. entailer!. }
  { Intros j.
    forward_if.
    match goal with Hx: j < r |- _ => rename Hx into Hjr end.
    assert (Hoc: Znth (pos + j) oc' = Vint (Int.repr (Znth j out))).
    { apply (VLI_oc_at oc' out pos r j); auto; unfold pos in *; lia. }
    assert_PROP (Vptr bb (Ptrofs.add ob (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_int64 (Int64.add (Int64.repr pos) (Int64.repr j))))) =
                 field_address (tarray tuchar (Zlength (ws_content ws))) (SUB (pos + j)) (Vptr bb ob)) as Ea.
    { entailer!. apply VLI_ptr_idx; [unfold pos in *; lia |].
      eapply VLI_fc_arr; [| exact Hfb]. pose proof (Zlength_nonneg db); lia. }
    forward.
    { entailer!.
      match goal with |- context [@Znth val ?d ?x oc'] =>
        replace (@Znth val d x oc') with (Vint (Int.repr (Znth j out))) by (rewrite <- Hoc; reflexivity) end.
      rewrite (Hcont j) by lia. apply VLI_tc_byte; auto. unfold pos in *; lia. }
    assert_PROP (force_val (sem_add_ptr_long tuchar (offset_val 524296 (gv _x_valid_bufferless__sr))
                   (Vlong (Int64.add (Int64.repr pos) (Int64.repr j)))) =
                 field_address (tarray tuchar (Zlength (ws_content ws))) (SUB (pos + j))
                   (field_address t_wseries (DOT _content) (VL_sr gv))) as Eb.
    { entailer!. apply VLI_content_idx; auto; unfold pos in *; lia. }
    forward.
    { entailer!. apply VLI_tc_byte; auto; unfold pos in *; lia. }
    forward_call Int.one.
    { entailer!.
      try (match goal with |- context [@Znth val ?d ?x oc'] =>
        replace (@Znth val d x oc') with (Vint (Int.repr (Znth j out))) by (rewrite <- Hoc; reflexivity) end;
        rewrite (Hcont j) by lia).
      unfold pos. simpl. rewrite Int.eq_true. reflexivity. }
    Exists j. entailer!.
    forward. entailer!. }
  { Intros j. forward. Exists (j + 1). entailer!. }
  sep_apply (wand_frame_elim
    (@data_at HCS Ews (tarray tuchar (Zlength (ws_content ws))) (zbytes (ws_content ws))
       (@field_address HCS t_wseries (DOT _content) (VL_sr gv)))
    (@data_at HCS Ews t_wseries (wseries_val ws) (VL_sr gv))).
  rewrite (VLB_cs HCS ZCS Ews (Zlength (ws_content ws)) oc' (Vptr bb ob)).
  forward. forward.
  change (set_ex (set_bl (set_ex (set_bl dctx_init (Some ba)) false) (Some ba')) false) with (set_ex (set_bl dctx_init (Some ba')) false).
  Exists (i + w) b' ba' oc'.
  assert (Elb: Zlength (bs_out b') = Zlength (bs_out b) + r) by (rewrite Eo, Zlength_app; lia).
  entailer!.
  replace (wi_cstart (VL_f ws k) + Zlength (bs_out b')) with (pos + Zlength out)
    by (unfold pos; rewrite Eo, Zlength_app; lia).
  split; [exact Hh' | split; [do 2 f_equal; unfold s0; lia | reflexivity]].
Qed.
