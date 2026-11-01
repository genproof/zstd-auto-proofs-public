(* Sub-group X1T of group HUF (HufGroups.v): building an X1 table: HUF_DEltX1_set4, HUF_rescaleStats, HUF_readDTableX1_wksp.
   Choose one specification per function of ids_X1T (containing X1T_exports) and prove every body against
   G_HUF ++ X1T_imports and them. *)
Require Export Zstd.proof.dec.B.huf.HufGroups.
Require Export Zstd.proof.dec.B.huf.HufMRescale Zstd.proof.dec.B.huf.HufMDesc.
Require Import Zstd.proof.dec.B.huf.HufX1TSpecs Zstd.proof.dec.B.huf.HufX1TRescale Zstd.proof.dec.B.huf.HufX1TSort Zstd.proof.dec.B.huf.HufX1TFill.
Require Import Zstd.proof.dec.B.BMemcpyOk.
Require Import Zstd.proof.model.ExHuf.
Local Open Scope logic.

(* ---------- HUF_DEltX1_set4 ---------- *)

Lemma body_HUF_DEltX1_set4 :
  semax_body Vprog [MEM_isLittleEndian_spec] f_HUF_DEltX1_set4 HUF_DEltX1_set4_spec.
Proof.
  start_function.
  forward_call.
  forward_if (PROP () LOCAL (temp _D4 (Vlong (Int64.repr (sym * 256 + nb)))) SEP ()).
  - forward. entailer!. do 2 f_equal.
    rewrite Int.shl_mul_two_p, Int.mul_signed, Int.add_signed.
    change (two_p (Int.unsigned (Int.repr 8))) with 256.
    rewrite (Int.signed_repr sym), (Int.signed_repr 256), (Int.signed_repr (sym * 256)), (Int.signed_repr nb)
      by rep_lia.
    rewrite Int.signed_repr by rep_lia. reflexivity.
  - discriminate.
  - forward. forward.
Qed.

(* ---------- the workspace ---------- *)

Lemma x1_al_uint (n z: Z) : (4 | z) -> align_compatible_rec cenv_cs (tarray tuint n) z.
Proof.
  intros H. apply align_compatible_rec_Tarray. intros i Hi.
  eapply align_compatible_rec_by_value; [reflexivity|]. simpl.
  apply Z.divide_add_r; auto. apply Z.divide_factor_l.
Qed.

Lemma x1_al_uchar (n z: Z) : align_compatible_rec cenv_cs (tarray tuchar n) z.
Proof.
  apply align_compatible_rec_Tarray. intros i Hi.
  eapply align_compatible_rec_by_value; [reflexivity|]. apply Z.divide_1_l.
Qed.

Lemma x1wksp_compat (p: val) (nk: Z) :
  373 <= nk -> field_compatible (tarray tuint nk) nil p -> field_compatible t_x1wksp nil p.
Proof.
  intros Hn Hfc. unfold field_compatible in *.
  destruct Hfc as (Hp & Hlegal & Hsz & Hal & _).
  destruct p; try contradiction.
  split; [exact I|]. split; [reflexivity|].
  split; [simpl in Hsz |- *; rewrite Z.max_r in Hsz by lia; lia|]. split; [|exact I].
  assert (H4: (4 | Ptrofs.unsigned i)).
  { unfold align_compatible in Hal. eapply align_compatible_rec_Tarray_inv with (i:=0) in Hal; [|lia].
    rewrite Z.add_0_r in Hal. inv Hal. inv H. exact H0. }
  clear Hal Hsz. hnf. eapply align_compatible_rec_Tstruct; [reflexivity|reflexivity|].
  intros i0 t0 z0 Hf Ho.
  destruct (ident_eq i0 _rankVal); [subst; vm_compute in Hf, Ho; inv Hf; inv Ho;
    apply x1_al_uint; rewrite Z.add_0_r; auto|].
  destruct (ident_eq i0 _rankStart); [subst; vm_compute in Hf, Ho; inv Hf; inv Ho;
    apply x1_al_uint; apply Z.divide_add_r; auto; exists 13; reflexivity|].
  destruct (ident_eq i0 _statsWksp); [subst; vm_compute in Hf, Ho; inv Hf; inv Ho;
    apply x1_al_uint; apply Z.divide_add_r; auto; exists 26; reflexivity|].
  destruct (ident_eq i0 _symbols); [subst; vm_compute in Hf, Ho; inv Hf; inv Ho; apply x1_al_uchar|].
  destruct (ident_eq i0 _huffWeight); [subst; vm_compute in Hf, Ho; inv Hf; inv Ho; apply x1_al_uchar|].
  exfalso. revert Hf. unfold Ctypes.field_type. simpl co_members.
  intro Hf. cbv fix beta iota in Hf. cbn [name_member] in Hf.
  repeat (destruct (ident_eq _ _) in Hf; [congruence|]). discriminate.
Qed.

Lemma x1wksp_eq (shk: share) (pk: val) (nk: Z) :
  373 <= nk <= 4096 -> field_compatible (tarray tuint nk) nil pk ->
  data_at_ shk (tarray tuint nk) pk =
  data_at_ shk t_x1wksp pk * memory_block shk (4 * nk - 1492) (offset_val 1492 pk).
Proof.
  intros Hn Hfc.
  assert (Hfc2: field_compatible t_x1wksp nil pk) by (eapply x1wksp_compat; eauto; lia).
  rewrite data_at__memory_block. rewrite (prop_true_andp (field_compatible _ _ _)) by auto.
  rewrite <- (memory_block_data_at_ shk t_x1wksp pk) by auto.
  change (sizeof (tarray tuint nk)) with (4 * Z.max 0 nk)%Z. rewrite Z.max_r by lia.
  change (sizeof t_x1wksp) with 1492.
  destruct Hfc as (Hp & _ & Hsz & _).
  destruct pk; try contradiction. simpl in Hsz. rewrite Z.max_r in Hsz by lia.
  rewrite <- (Ptrofs.repr_unsigned i).
  replace (4 * nk)%Z with (1492 + (4 * nk - 1492))%Z at 1 by lia.
  rewrite memory_block_split by (pose proof (Ptrofs.unsigned_range i); lia).
  simpl offset_val. rewrite ptrofs_add_repr. reflexivity.
Qed.

Lemma x1wksp_fields (shk: share) (pk: val) :
  data_at_ shk t_x1wksp pk =
  field_at_ shk t_x1wksp (DOT _rankVal) pk * field_at_ shk t_x1wksp (DOT _rankStart) pk *
  field_at_ shk t_x1wksp (DOT _statsWksp) pk * field_at_ shk t_x1wksp (DOT _symbols) pk *
  field_at_ shk t_x1wksp (DOT _huffWeight) pk.
Proof.
  unfold_data_at (data_at_ _ _ _). rewrite !sepcon_assoc. reflexivity.
Qed.

Lemma x1wksp_join (shk: share) (pk: val) (nk: Z) :
  373 <= nk <= 4096 -> field_compatible (tarray tuint nk) nil pk ->
  data_at_ shk (tarray tuint 13) (field_address t_x1wksp (DOT _rankVal) pk) *
  data_at_ shk (tarray tuint 13) (field_address t_x1wksp (DOT _rankStart) pk) *
  data_at_ shk (tarray tuint 219) (field_address t_x1wksp (DOT _statsWksp) pk) *
  data_at_ shk (tarray tuchar 256) (field_address t_x1wksp (DOT _symbols) pk) *
  data_at_ shk (tarray tuchar 256) (field_address t_x1wksp (DOT _huffWeight) pk) *
  memory_block shk (4 * nk - 1492) (offset_val 1492 pk)
  |-- data_at_ shk (tarray tuint nk) pk.
Proof.
  intros Hn Hfc. rewrite (x1wksp_eq shk pk nk) by auto. rewrite x1wksp_fields.
  rewrite !field_at__data_at_. simpl nested_field_type.
  cancel.
Qed.

Lemma hufhdr_intro (sh: share) (p ty lg res: val) :
  align_compatible tuint p -> byte_val ty -> byte_val lg -> byte_val res ->
  data_at sh t_dtdesc (vint 12, (ty, (lg, res))) p * memory_block sh HUF_CELLBYTES (offset_val 4 p)
  |-- hufhdr_at sh p.
Proof. intros Hal Hty Hlg Hres. unfold hufhdr_at. Exists ty lg res. entailer!. Qed.

(* the X1 cells of BRep are ExHuf's xh_cells_x1 read as HUF_DEltX1 {nbBits; byte} *)
Lemma x1_cells_x (ht: huf_table) (L: Z) :
  x1_cells ht L = map (fun c => let '(sq, nb, _) := c in x1cell (sq, nb)) (xh_cells_x1 ht L).
Proof.
  unfold x1_cells, xh_cells_x1. rewrite map_map. apply map_ext. intros n.
  destruct (hsym ht L (Z.of_nat n)); reflexivity.
Qed.

(* the built table: zstd's X1 reader raises the log to max(tableLog, 11) *)
Lemma x1_hufdt (shd: share) (ht: huf_table) (L: Z) (res dt: val) :
  huf_ok ht -> ht_log ht <= L <= HUF_TABLELOG_MAX -> L = Z.max (ht_log ht) 11 ->
  align_compatible tuint dt -> byte_val res ->
  data_at shd t_dtdesc (vint 12, (vint 0, (vint L, res))) dt *
  data_at shd (tarray t_deltx1 (2 ^ L)) (x1_cells ht L) (offset_val 4 dt) *
  memory_block shd (HUF_CELLBYTES - 2 * 2 ^ L) (offset_val (4 + 2 * 2 ^ L) dt)
  |-- hufdt_x_at false shd ht dt.
Proof.
  intros Hok HL HLx Hal Hres. unfold hufdt_x_at. Exists L res. simpl. entailer!.
Qed.

(* ---------- HUF_readDTableX1_wksp ---------- *)

Definition X1_G : funspecs :=
  [ HUF_readStats_wksp_spec; ERR_isError_spec; HUF_getDTableDesc_spec; HUF_rescaleStats_spec; memcpy_spec;
    HUF_DEltX1_set4_spec; MEM_write64_spec ].

Fixpoint x1_nodupb (l: list ident) : bool :=
  match l with nil => true | i :: r => negb (existsb (Pos.eqb i) r) && x1_nodupb r end.

Lemma x1_nodupb_ok (l: list ident) : x1_nodupb l = true -> NoDup l.
Proof.
  induction l as [|i r IH]; simpl; intros H; [constructor|].
  apply andb_prop in H as [H1 H2]. constructor; [|apply IH, H2].
  intros Hin. destruct (existsb (Pos.eqb i) r) eqn:E; [discriminate|].
  assert (existsb (Pos.eqb i) r = true) by (apply existsb_exists; exists i; split; [exact Hin | apply Pos.eqb_refl]).
  congruence.
Qed.

Lemma x1_G_nodup : NoDup (map fst Vprog ++ map fst X1_G).
Proof. apply x1_nodupb_ok. vm_compute. reflexivity. Qed.

Lemma x1_lift {Espec: OracleKind} (G: funspecs) P c R :
  incl G X1_G -> semax (x1_Delta G) P c R ->
  semax (func_tycontext f_HUF_readDTableX1_wksp Vprog X1_G nil) P c R.
Proof.
  intros HG H. eapply semax_Delta_subsumption; [|exact H].
  apply semax_prog.func_tycontext_sub; [apply incl_refl | exact HG | exact x1_G_nodup].
Qed.

Ltac x1_params :=
  apply prop_right; rewrite !field_address_offset by auto;
  match goal with Hfw: field_compatible t_x1wksp nil ?pk |- _ =>
    let Hp := fresh in destruct Hfw as [Hp _]; destruct pk; try contradiction; reflexivity end.

Lemma body_HUF_readDTableX1_wksp :
  semax_body Vprog X1_G f_HUF_readDTableX1_wksp HUF_readDTableX1_wksp_spec.
Proof.
  start_function.
  unfold hufhdr_at. Intros ty lg res.
  match goal with H: align_compatible tuint dt |- _ => rename H into Hal end.
  assert_PROP (field_compatible (tarray tuint nk) nil pk) as Hfck by entailer!.
  assert_PROP (isptr dt) as Hdt by entailer!.
  rewrite (x1wksp_eq shk pk nk) by (auto; lia).
  rewrite x1wksp_fields. Intros.
  forward. forward. forward. forward. forward.
  forward_if.
  { exfalso; lia. }
  assert (Hfw: field_compatible t_x1wksp nil pk) by (eapply x1wksp_compat; eauto; lia).
  assert (field_compatible t_x1wksp (DOT _huffWeight) pk) by auto with field_compatible.
  assert (field_compatible t_x1wksp (DOT _rankVal) pk) by auto with field_compatible.
  assert (field_compatible t_x1wksp (DOT _statsWksp) pk) by auto with field_compatible.
  rewrite !field_at__data_at_. simpl nested_field_type.
  forward_call (gv, shk, field_address t_x1wksp (DOT _huffWeight) pk, shk, field_address t_x1wksp (DOT _rankVal) pk,
                Tsh, v_nbSymbols, Tsh, v_tableLog, sh, base, N, c, off, s, shk,
                field_address t_x1wksp (DOT _statsWksp) pk).
  { x1_params. }
  Intros vret. destruct vret as [[r wc] ores]. simpl fst in *. simpl snd in *.
  match goal with Hm: forall x, huf_parse_desc s = Some x -> ores = Some x |- _ => rename Hm into Hmod end.
  destruct ores as [[ht size]|] eqn:Hpd.
  2:{ Intros. forward_call r. match goal with Herr: is_error_code r = true |- _ => rewrite Herr end.
      forward_if.
      2:{ discriminate. }
      forward.
      Exists r (@None (huf_table * Z)). entailer!. sep_apply hufhdr_intro; auto.
      sep_apply (data_at_data_at_ shk (tarray tuchar 256) wc (field_address t_x1wksp (DOT _huffWeight) pk)).
      sep_apply (x1wksp_join shk pk nk); auto; try lia.
      cancel. }
  match goal with Hm: r = size /\ _ |- _ => destruct Hm as (-> & Hsz & Hok & Hlen & Hwr & Hws) end. Intros.
  assert (Hne: is_error_code size = false).
  { destruct H0 as (_ & Hoff & Hon & HN & _). unfold is_error_code. apply Z.ltb_ge.
    change (2 ^ 64 - 120) with 18446744073709551496. change (2 ^ 32) with 4294967296 in HN. lia. }
  forward_call size. rewrite Hne.
  forward_if.
  { match goal with Hc: Int.repr 0 <> Int.zero |- _ => elim Hc; reflexivity end. }
  forward_call (Tsh, v_dtd, shd, dt, (vint 12, (ty, (lg, res)))).
  { memcpy_ok_B. }
  forward. forward.
  forward_if (temp _t'3 (vint 11)).
  { lia. }
  { forward. entailer!. }
  set (ws := ht_weights ht) in *. set (tl := ht_log ht) in *.
  assert (Htl: 1 <= tl <= 12) by (destruct Hok as [? _]; unfold HUF_TABLELOG_MAX in *; lia).
  replace wc with (zbytes ws ++ sublist (Zlength ws) 256 wc)
    by (rewrite <- Hws, sublist_rejoin, sublist_same by lia; auto).
  forward. forward. forward.
  forward_call (shk, field_address t_x1wksp (DOT _huffWeight) pk, ws, sublist (Zlength ws) 256 wc,
                shk, field_address t_x1wksp (DOT _rankVal) pk, tl, 11).
  { x1_params. }
  { repeat split; auto; unfold HUF_TABLELOG_MAX in *; try lia. rewrite Zlength_sublist by lia; lia. }
  forward. forward. forward.
  forward_if.
  { exfalso; lia. }
  set (L := Z.max tl 11) in *.
  assert (HL: 11 <= L <= 12) by (subst L; lia).
  assert (HLt: tl <= L) by (subst L; lia).
  forward. forward. forward.
  assert (Hz: Int.zero_ext 8 (Int.zero_ext 8 (Int.repr L)) = Int.repr L).
  { assert (Hz1: Int.zero_ext 8 (Int.repr L) = Int.repr L)
      by (apply zero_ext_inrange; rewrite Int.unsigned_repr by rep_lia; simpl; rep_lia).
    rewrite !Hz1. reflexivity. }
  rewrite Hz. change (Int.zero_ext 8 (Int.repr 0)) with (Int.repr 0).
  forward_call (Tsh, shd, v_dtd, dt, existT (fun t => reptype t) t_dtdesc (vint 12, (vint 0, (vint L, res)))).
  { memcpy_side_B. }
  cbn [projT1 projT2].
  (* statement 9: the sorted symbols *)
  set (rws := x1_rescale_ws ws tl L) in *.
  set (wr := sublist (Zlength ws) 256 wc) in *.
  assert (Hrl: Zlength rws = Zlength ws) by (subst rws; unfold x1_rescale_ws; rewrite Zlength_map; auto).
  assert (Hrw: Forall (fun w => 0 <= w <= L) rws).
  { subst rws; unfold x1_rescale_ws. rewrite Forall_map. eapply Forall_impl; [|exact Hwr].
    intros w Hw. simpl in Hw |- *. destruct (w =? 0); lia. }
  assert (Hwrl: Zlength wr = 256 - Zlength rws) by (subst wr; rewrite Zlength_sublist by lia; lia).
  pose (F1 := data_at Tsh t_dtdesc (vint 12, (vint 0, (vint L, res))) v_dtd *
       data_at shd t_dtdesc (vint 12, (vint 0, (vint L, res))) dt * zstd_globals gv *
       data_at sh (tarray tuchar N) c base *
       data_at_ shk (tarray tuint 219) (field_address t_x1wksp (DOT _statsWksp) pk) *
       data_at_ Tsh (Tstruct ___gp_HUF_DEltX1 noattr) v_D__1 * data_at_ Tsh (Tstruct ___gp_HUF_DEltX1 noattr) v_D *
       memory_block shd HUF_CELLBYTES (offset_val 4 dt) * memory_block shk (4 * nk - 1492) (offset_val 1492 pk)).
  eapply semax_seq'.
  { eapply semax_pre; [|apply (x1_lift nil); [intros ? [] | ]].
    2: apply (x1_sort Espec F1 size (offset_val 4 dt) pk v_tableLog v_nbSymbols v_dtd v_D v_D__1 shk rws wr L);
       auto; try lia.
    2: unfold HUF_TABLELOG_MAX; lia.
    rewrite !field_at_data_at, !field_at__data_at_. simpl nested_field_type. unfold F1. rewrite Hrl.
    entailer!. }
  (* statement 10: the fill *)
  assert (Hcl: map x1cell (huf_cells {| ht_log := L; ht_weights := rws |}) = x1_cells ht L).
  { subst rws ws tl. rewrite <- x1_rescale_ws_eq. apply x1_cells_rescale; auto; unfold HUF_TABLELOG_MAX; lia. }
  assert (Hkr: Zlength (huf_cells {| ht_log := L; ht_weights := rws |}) = 2 ^ L).
  { rewrite <- (Zlength_map _ _ x1cell), Hcl. unfold x1_cells. rewrite Zlength_map, Zlength_correct, seq_length.
    rewrite Z2Nat.id; auto. apply Z.pow_nonneg; lia. }
  pose (F2 := data_at Tsh tuint (vint (Zlength rws)) v_nbSymbols *
       field_at_ shk t_x1wksp (DOT _rankStart) pk *
       field_at shk t_x1wksp (DOT _huffWeight) (zbytes rws ++ wr) pk *
       data_at Tsh t_dtdesc (vint 12, (vint 0, (vint L, res))) v_dtd *
       data_at shd t_dtdesc (vint 12, (vint 0, (vint L, res))) dt * zstd_globals gv *
       data_at sh (tarray tuchar N) c base *
       data_at_ shk (tarray tuint 219) (field_address t_x1wksp (DOT _statsWksp) pk) *
       memory_block shk (4 * nk - 1492) (offset_val 1492 pk)).
  eapply semax_seq'.
  { eapply semax_pre; [|apply (x1_lift [HUF_DEltX1_set4_spec; MEM_write64_spec]);
      [intros x Hx; repeat (destruct Hx as [<-|Hx]; [unfold X1_G; repeat (first [left; reflexivity | right])|]); contradiction | ]].
    2: apply (x1_fill Espec F2 size (offset_val 4 dt) pk v_tableLog v_nbSymbols v_dtd v_D v_D__1 shk shd rws
                (Zrepeat Vundef (256 - Zlength rws)) L); auto; try lia.
    2: unfold HUF_TABLELOG_MAX; lia.
    2: rewrite Zlength_Zrepeat; lia.
    unfold F1, F2. entailer!. }
  (* the return *)
  unfold F2. Intros.
  forward.
  Exists size (Some (ht, size)). entailer!. rewrite Hcl.
  sep_apply (x1_hufdt shd ht L res dt); auto; [unfold HUF_TABLELOG_MAX; lia|].
  rewrite !field_at_data_at, !field_at__data_at_. simpl nested_field_type.
  sep_apply (data_at_data_at_ shk (tarray tuint 13) (rank_stats rws) (field_address t_x1wksp (DOT _rankVal) pk)).
  sep_apply (data_at_data_at_ shk (tarray tuchar 256) (zbytes (x1_sorted rws) ++ Zrepeat Vundef (256 - Zlength rws))
    (field_address t_x1wksp (DOT _symbols) pk)).
  sep_apply (data_at_data_at_ shk (tarray tuchar 256) (zbytes rws ++ wr) (field_address t_x1wksp (DOT _huffWeight) pk)).
  sep_apply (x1wksp_join shk pk nk); auto; try lia.
  cancel.
Qed.

(* ---------- the sub-group ---------- *)

Ltac x1_in := solve [repeat (first [left; reflexivity | right])].
Ltac x1_find :=
  unfold G_HUF, G_B0, Gprog, Specs_L0, X1T_imports, X1T_specs, ENT_exports;
  repeat rewrite in_app_iff;
  first [ do 4 left; right; right; apply in_or_app; left; unfold Specs_util; x1_in
        | do 4 left; right; left; reflexivity
        | do 2 left; right; x1_in
        | left; right; x1_in
        | right; x1_in ].

Ltac x1_incl := intros x Hx; repeat (destruct Hx as [<-|Hx]; [x1_find|]); destruct Hx.

Lemma X1T_ok : X1T_obligation.
Proof.
  exists X1T_specs. split; [reflexivity|]. split.
  - intros x [<-|[]]. unfold X1T_specs. x1_in.
  - assert (Hnd: NoDup (map fst Vprog ++ map fst ((G_HUF ++ X1T_imports) ++ X1T_specs)))
      by (apply x1_nodupb_ok; vm_compute; reflexivity).
    unfold X1T_specs at 2. repeat apply Forall_cons; try apply Forall_nil.
    + eapply (body_ok_mono [MEM_isLittleEndian_spec]); [| x1_incl | exact Hnd].
      exists f_HUF_DEltX1_set4. split; [vm_compute; reflexivity|]. split; [reflexivity|].
      exact body_HUF_DEltX1_set4.
    + eapply (body_ok_mono nil); [| intros ? [] | exact Hnd].
      exists f_HUF_rescaleStats. split; [vm_compute; reflexivity|]. split; [reflexivity|].
      exact body_HUF_rescaleStats.
    + eapply (body_ok_mono X1_G); [| unfold X1_G; x1_incl | exact Hnd].
      exists f_HUF_readDTableX1_wksp. split; [vm_compute; reflexivity|]. split; [reflexivity|].
      exact body_HUF_readDTableX1_wksp.
Qed.
