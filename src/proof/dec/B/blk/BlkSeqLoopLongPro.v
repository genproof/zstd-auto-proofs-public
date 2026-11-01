(* The long loop (ZSTD_decompressSequencesLong_body, cut in segments by BlkSeqLoopLongDefs): the prologue lg_pro;
   litExtraBuffer holds the bytes lxb of the precondition (the exact model's a_lxb). *)
Require Import Zstd.proof.dec.B.blk.BlkSeqLoopLongDefs.
Local Open Scope logic.

(* the literal fields in one shape for every location: litBuffer (read only for literals in dst) *)
Definition lg_lbuf (a: la) : mpred :=
  match a_l a with
  | LIn _ => field_at_ Ews t_dctx (DOT _litBuffer) (a_p a)
  | LExtra => field_at Ews t_dctx (DOT _litBuffer) (lit_extra (a_p a)) (a_p a)
  | LDst lb | LSplit lb => field_at Ews t_dctx (DOT _litBuffer) (offset_val lb (a_ob a)) (a_p a)
  end.

Definition lg_lits (a: la) (xc: list val) : mpred :=
  field_at Ews t_dctx (DOT _litSize) (Vlong (Int64.repr (a_n a))) (a_p a) *
  field_at Ews t_dctx (DOT _litBufferLocation) (Vint (Int.repr (loc_code (a_l a)))) (a_p a) *
  field_at Ews t_dctx (DOT _litPtr) (offset_val (lit_li a false 0) (lit_base a false)) (a_p a) *
  field_at Ews t_dctx (DOT _litBufferEnd) (offset_val (lit_lim a false) (lit_base a false)) (a_p a) *
  lg_lbuf a * data_at Ews (tarray tuchar LITEXTRA_N) xc (lit_extra (a_p a)).

Lemma lg_off0 (p: val) : offset_val 0 (lit_extra p) = lit_extra p.
Proof.
  unfold lit_extra, field_address. destruct (field_compatible_dec _ _ _); [|reflexivity].
  rewrite offset_offset_val, Z.add_0_r. reflexivity.
Qed.

Lemma lg_zbytes_cells (l: list Z) : bytes_ok l -> byte_cells (zbytes l).
Proof.
  unfold bytes_ok, byte_cells. intros H. rewrite Forall_map.
  eapply Forall_impl; [|exact H]. intros b Hb. exists b. split; [exact Hb | reflexivity].
Qed.

Lemma lg_xc_len (p: val) (xc: list val) :
  data_at Ews (tarray tuchar LITEXTRA_N) xc (lit_extra p) |-- !! (Zlength xc = LITEXTRA_N).
Proof. entailer!. Qed.

(* the literal fields of the precondition (litExtraBuffer holding lxb) in the loop's shape, litExtraBuffer as
   the byte array zbytes lxb *)
Lemma lg_lits_pre (a: la) :
  la_ok a ->
  litfields (a_p a) (a_ob a) (iw_base (a_i a)) (a_l a) (a_lits a) (a_lxb a) |--
  !! (xc_ok (a_l a) (a_lits a) (zbytes (a_lxb a)) /\ xl_lxb_ok a) && lg_lits a (zbytes (a_lxb a)).
Proof.
  intros Hok. pose proof Hok as (_ & _ & Hlits & _). pose proof (Zlength_nonneg (a_lits a)).
  unfold litfields, lit_extra_at, lg_lits, lg_lbuf, lit_li, lit_lim, lit_base, a_n, xc_ok, xl_lxb_ok.
  assert (LITBUFFEREXTRASIZE = 65536) by reflexivity.
  destruct (a_l a) as [off | | lb | lb]; unfold lits_at in Hlits; destruct Hlits as (Hb & _ & Hl); Intros;
    rewrite <- ?litextra_data_at, ?Z.add_0_r, ?lg_off0; (apply andp_right; [apply prop_right | cancel]).
  all: refine (conj _ (conj (conj _ _) (conj _ (conj _ _)))); try assumption; try exact I;
    try (rewrite Zlength_map; assumption); try (apply lg_zbytes_cells; assumption);
    rewrite sublist_map; f_equal; assumption.
Qed.

Lemma lg_lits_now (a: la) (xc: list val) : lg_lits a xc |-- lit_now a xc false.
Proof.
  unfold lit_now, lit_fix, lg_lits, lg_lbuf, lit_li, lit_lim, lit_base, lit_code, a_n.
  destruct (a_l a); rewrite ?Z.add_0_r, ?lg_off0; cancel.
Qed.

Lemma lg_lbuf_dst (a: la) (lb: Z) :
  a_l a = LDst lb ->
  lg_lbuf a = field_at Ews t_dctx (DOT _litBuffer) (offset_val lb (a_ob a)) (a_p a).
Proof. unfold lg_lbuf. intros ->. reflexivity. Qed.

Lemma lg_wvp_pon (v: val) : weak_valid_pointer v |-- !! is_pointer_or_null v.
Proof.
  destruct v; try (apply prop_right; simpl; auto; fail).
  all: unfold weak_valid_pointer; constructor; intros w Hw; destruct Hw as [Hw|Hw]; simpl in Hw; try contradiction.
  all: subst; exact (eq_refl Int64.zero).
Qed.

Lemma lg_pro_ok : SEG_PRO.
Proof.
  intros Espec a REST Hok Hpend HREST.
  unfold lg_pro, L_pre, S_pre.
  pose proof Hok as (Ho & Hi & Hlits & Hbsm & Hn & Hnb & Hnbo & Hos & Hrep & Hfe & Hw & Hlay).
  destruct Hpend as ((Hps & Hvs & Hde) & Hlb).
  destruct Ho as (Hosh & HoN & HN32 & Hd & Hcap & HdN).
  assert_PROP (isptr (oa_base (a_o a))) as Hob by entailer!.
  assert_PROP (is_pointer_or_null (fs_dictEnd (a_fs a))) as Hde'.
  { destruct Hde as [Hde | Hwv].
    - unfold la_dictend_ok, a_x in Hde. destruct Hde as [-> | [(k & _ & ->) | Hx]].
      + entailer!.
      + destruct (oa_base (a_o a)); try contradiction. entailer!.
      + destruct (hc_ext (a_h a)); try contradiction. destruct Hx as [-> _].
        unfold ext_res. entailer!.
    - sep_apply Hwv. sep_apply (lg_wvp_pon (fs_dictEnd (a_fs a))). entailer!. }
  sep_apply (lg_lits_pre a Hok). Intros. set (xc := zbytes (a_lxb a)).
  match goal with H: xc_ok _ _ _ |- _ => rename H into Hxc end.
  match goal with H: xl_lxb_ok a |- _ => rename H into Hx end.
  unfold lg_lits. Intros.
  assert_PROP (isptr (lit_base a false)) as Hbase.
  { unfold lit_base, a_ob. destruct (a_l a); entailer!. }
  assert (Hlp: is_pointer_or_null (offset_val (lit_li a false 0) (lit_base a false))).
  { destruct (lit_base a false); try contradiction; exact I. }
  forward. forward.
  match goal with |- semax _ (PROPx _ (LOCALx ?L (SEPx ?S))) _ _ =>
    forward_if (PROPx [] (LOCALx (temp _t'1 (offset_val (a_E a) (oa_base (a_o a))) :: L) (SEPx S))) end.
  - assert (exists lb, a_l a = LDst lb) as [lb El].
    { destruct (a_l a) as [off | | lb | lb]; [exfalso; cbn in H; discriminate | exfalso; cbn in H; discriminate
      | exists lb; reflexivity | exfalso; cbn in H; discriminate]. }
    rewrite (lg_lbuf_dst a lb El). forward. forward.
    rewrite (lg_lbuf_dst a lb El). replace (a_E a) with lb by (unfold a_E; rewrite El; reflexivity).
    unfold a_ob. destruct (lg_R a). unfold tycontext.RA_normal. entailer!.
  - assert (HE: a_E a = oa_d (a_o a) + oa_cap (a_o a)).
    { unfold a_E, a_d, a_cap. destruct (a_l a); auto. exfalso. apply H. reflexivity. }
    forward_call (offset_val (oa_d (a_o a)) (oa_base (a_o a)), oa_cap (a_o a)).
    forward. rewrite HE. destruct (lg_R a). unfold tycontext.RA_normal. entailer!.
    destruct (Z.ltb_spec 0 (oa_cap (a_o a))); [rewrite ?offset_offset_val; reflexivity |].
    replace (oa_cap (a_o a)) with 0 by lia. rewrite Z.add_0_r. reflexivity.
  - forward. forward. forward. forward. forward. unfold frame_fields. Intros.
    forward. forward. forward. forward. forward. forward.
    eapply semax_pre; [| apply (HREST xc Hxc eq_refl Hx)].
    pose proof (lg_lits_now a xc) as Hnow. unfold lg_lits in Hnow. sep_apply Hnow.
    unfold L_ex, L_base, XI_S, a_start, frame_fields, a_ob.
    fold (fs_dictEnd (a_fs a)) (fs_virtualStart (a_fs a)) (fs_prefixStart (a_fs a)).
    unfold a_x, a_d. rewrite Z.add_0_r. cbn [app]. entailer!.
Qed.
