(* FS3 one-shot frames, ZSTD_decompressMultiFrame: v2's helpers of body_multiframe.v ported to API v3
   (darg_ok3, fs_begin3 with the format, any dictionary argument a' for the frame). *)
Require Export Zstd.proof.dec.v3.FS.frames.Frames3Spec Zstd.proof.dec.v3.FS.frames.Frames3SeriesSel.
Local Open Scope logic.

Section CM_Multi3Pre_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma sres_prepend_nil: forall r, sres_prepend nil r = r.
Proof. destruct r; reflexivity. Qed.

Lemma sres_prepend_app: forall c1 c2 r, sres_prepend c1 (sres_prepend c2 r) = sres_prepend (c1 ++ c2) r.
Proof. destruct r; simpl; auto. rewrite app_assoc; auto. Qed.

Lemma skipn_sublist_end: forall (s: list Z) off k,
  0 <= off -> 0 <= k -> off + k <= Zlength s ->
  skipn (Z.to_nat k) (sublist off (Zlength s) s) = sublist (off + k) (Zlength s) s.
Proof.
  intros. unfold sublist. rewrite skipn_skipn. f_equal. lia.
Qed.

(* the bytes written so far *)
Lemma bytes_step: forall u r oc oc' acc c,
  sublist 0 u oc = zbytes acc -> Zlength acc = u -> Zlength oc >= u ->
  sublist 0 r oc' = zbytes c -> Zlength c = r -> r <= Zlength oc' ->
  sublist 0 (u + r) (sublist 0 u oc ++ oc') = zbytes (acc ++ c).
Proof.
  intros. rewrite map_app, <- H, <- H2. pose proof (Zlength_nonneg c). list_solve.
Qed.

Lemma bytes_ok_sublist: forall s i j, bytes_ok s -> bytes_ok (sublist i j s).
Proof. intros. unfold bytes_ok in *. apply Forall_sublist. auto. Qed.

(* ---------- the dictionary argument, split for the calls ---------- *)

(* the DDict a context's tables may point into *)
Definition darg_ox (a: darg) : option ddx := match a with DA_ddict x _ _ => Some x | _ => None end.

(* the value of the local `dict` after ZSTD_DDict_dictContent *)
Definition darg_dictv (a: darg) : val := match a with DA_ddict _ buf _ => buf | _ => darg_dict a end.
Definition darg_dsize (a: darg) : Z :=
  match a with DA_ddict x _ _ => Zlength (dx_bytes x) | _ => darg_size a end.

(* the extDict a frame sees once the output moved: none, the caller's bytes (the content of the dictionary
   dm as zstd loaded it), or the DDict's content; none for the DDict without content (buf = NULL, not a copy:
   a copy's buf is always a pointer, ddict_struct) *)
Definition ext_of (a: darg) (dm: dict_model) : ext_seg :=
  match a with
  | DA_none => ExtNone
  | DA_dict sh pk b =>
      if Zlength b =? 0 then ExtNone else ExtSep sh pk (Zlength b) (zbytes b) (Zlength b) (Zlength (dm_content dm))
  | DA_ddict x buf sh =>
      match buf with
      | Vptr _ _ =>
          ExtSep (if ddx_copied x then Ews else sh) buf (Zlength (dx_bytes x)) (zbytes (dx_bytes x))
            (Zlength (dx_bytes x)) (Zlength (dx_bytes x))
      | _ =>
          if ddx_copied x
          then ExtSep Ews buf (Zlength (dx_bytes x)) (zbytes (dx_bytes x)) (Zlength (dx_bytes x)) (Zlength (dx_bytes x))
          else ExtNone
      end
  end.

(* the rest of darg_res *)
Definition darg_rest (a: darg) : mpred :=
  match a with
  | DA_none => emp
  | DA_dict sh pk b => if Zlength b =? 0 then data_at sh (tarray tuchar (Zlength b)) (zbytes b) pk else emp
  | DA_ddict x buf sh =>
      ddict_struct x buf * blk_tok (dx_mem x) (Tstruct _ZSTD_DDict_s noattr) (dx_q x) *
      (if ddx_copied x then blk_tok (dx_mem x) (tarray tuchar (Zlength (dx_bytes x))) buf else emp) *
      ddict_pad (dx_q x)
  end.

(* the content pointer fact of a DDict's struct *)
Lemma ddict_struct_cont: forall x buf,
  ddict_struct x buf |-- !! (isptr buf \/ (buf = nullval /\ dx_ref x = Some nullval /\ dx_bytes x = nil)).
Proof. intros. unfold ddict_struct. Intros. apply prop_right. tauto. Qed.

Lemma darg_res_split: forall DENT gv a dm,
  darg_res DENT gv a = dent_of DENT gv (darg_ox a) * ext_res (ext_of a dm) * darg_rest a.
Proof.
  intros. destruct a as [| sh pk b | x buf sh]; simpl.
  - rewrite !sepcon_emp. reflexivity.
  - destruct (Zlength b =? 0); simpl; rewrite ?emp_sepcon, ?sepcon_emp; reflexivity.
  - apply pred_ext.
    + assert_PROP (isptr buf \/ (buf = nullval /\ dx_ref x = Some nullval /\ dx_bytes x = nil)) as Hb.
      { unfold ddict_rep_at. sep_apply (ddict_struct_cont x buf). entailer!. }
      destruct Hb as [Hp | (-> & Hr & Hn)]; unfold ddict_rep_at, ddict_mem.
      * destruct buf; try contradiction. simpl. rewrite bytes_at_ptr by exact I.
        destruct (ddx_copied x); simpl; cancel.
      * assert (Hc: ddx_copied x = false) by (unfold ddx_copied; rewrite Hr; reflexivity).
        rewrite Hc, bytes_at_null. simpl. cancel.
    + assert_PROP (isptr buf \/ (buf = nullval /\ dx_ref x = Some nullval /\ dx_bytes x = nil)) as Hb.
      { sep_apply (ddict_struct_cont x buf). entailer!. }
      destruct Hb as [Hp | (-> & Hr & Hn)]; unfold ddict_rep_at, ddict_mem.
      * destruct buf; try contradiction. simpl. rewrite bytes_at_ptr by exact I.
        destruct (ddx_copied x); simpl; cancel.
      * assert (Hc: ddx_copied x = false) by (unfold ddx_copied; rewrite Hr; reflexivity).
        rewrite Hc, bytes_at_null. simpl. cancel.
Qed.

(* ---------- dictionary models ---------- *)

Lemma dict_auto_nil: dict_auto nil = Some no_dict.
Proof. reflexivity. Qed.

Lemma le_value_range: forall l, bytes_ok l -> 0 <= le_value l < 256 ^ Zlength l.
Proof.
  induction l as [| b l IH]; intros Hb; simpl; [lia |].
  inversion Hb as [| ? ? Hb1 Hb2]; subst. specialize (IH Hb2). unfold is_byte in Hb1.
  rewrite Zlength_cons, Z.pow_succ_r by (apply Zlength_nonneg). nia.
Qed.

Lemma le_field_4_range: forall l i, bytes_ok l -> 0 <= le_field l i 4 <= Int.max_unsigned.
Proof.
  intros. unfold le_field, slice.
  assert (Hok: bytes_ok (firstn (Z.to_nat 4) (skipn (Z.to_nat i) l))).
  { unfold bytes_ok in *. apply Forall_firstn, Forall_skipn. auto. }
  pose proof (le_value_range _ Hok).
  assert (Zlength (firstn (Z.to_nat 4) (skipn (Z.to_nat i) l)) <= 4).
  { rewrite Zlength_correct, firstn_length. lia. }
  assert (256 ^ Zlength (firstn (Z.to_nat 4) (skipn (Z.to_nat i) l)) <= 256 ^ 4)
    by (apply Z.pow_le_mono_r; [lia | auto]).
  rep_lia.
Qed.

Lemma dict_id_of_range: forall b, bytes_ok b -> 0 <= dict_id_of b <= Int.max_unsigned.
Proof.
  intros. unfold dict_id_of. destruct (Zlength b <? 8); [rep_lia |].
  destruct (negb _); [rep_lia | apply le_field_4_range; auto].
Qed.

(* the dictionary as zstd loads it (C-result form) *)
Lemma dict_auto_c_suffix: forall b ores dm, dict_auto_c b ores = Some dm -> exists pre, b = pre ++ dm_content dm.
Proof.
  unfold dict_auto_c. intros b ores dm H.
  destruct (Zlength b <? 8); [inversion H; subst; exists nil; reflexivity |].
  destruct (negb _); [inversion H; subst; exists nil; reflexivity |].
  destruct ores as [[st es] |]; inversion H; subst; simpl.
  exists (firstn (Z.to_nat es) b). symmetry. apply firstn_skipn.
Qed.

Lemma dict_auto_c_id: forall b ores dm, dict_auto_c b ores = Some dm -> dm_id dm = dict_id_of b.
Proof.
  unfold dict_auto_c, dict_id_of. intros b ores dm H.
  destruct (Zlength b <? 8); [inversion H; subst; reflexivity |].
  destruct (negb _); [inversion H; subst; reflexivity |].
  destruct ores as [[st es] |]; inversion H; subst; reflexivity.
Qed.

Lemma dict_auto_c_id_range: forall b ores dm, bytes_ok b -> dict_auto_c b ores = Some dm ->
  0 <= dm_id dm <= Int.max_unsigned.
Proof. intros. erewrite dict_auto_c_id by eauto. apply dict_id_of_range; auto. Qed.

(* a DDict's model: its ID, entropy state and content as Begin_usingDDict sets them *)
Lemma ddx_model_facts: forall x dm, ddx_model x = Some dm ->
  dm_id dm = (if dx_raw x then 0 else dict_id_of (dx_bytes x)) /\ dm_state dm = ddx_state x /\
  exists pre, dx_bytes x = pre ++ dm_content dm.
Proof.
  intros x dm H. unfold ddx_model, ddx_state, ddx_ent, ddict_ent_c in *.
  destruct (dx_raw x).
  - inversion H; subst. simpl. split; [auto | split; [auto | exists nil; auto]].
  - pose proof (dict_auto_c_suffix _ _ _ H) as Hs. split; [| split; [| auto]].
    + eapply dict_auto_c_id; eauto.
    + unfold dict_auto_c, is_formatted in *.
      destruct (Zlength (dx_bytes x) <? 8) eqn:E1.
      * inversion H; subst. simpl. rewrite Z.ltb_lt in E1. replace (8 <=? Zlength (dx_bytes x)) with false
          by (symmetry; apply Z.leb_gt; lia). reflexivity.
      * rewrite Z.ltb_ge in E1. replace (8 <=? Zlength (dx_bytes x)) with true by (symmetry; apply Z.leb_le; lia).
        simpl. destruct (le_field (dx_bytes x) 0 4 =? ZSTD_MAGIC_DICTIONARY); simpl in *.
        -- destruct (dx_ld x) as [[st es] |]; inversion H; auto.
        -- inversion H; auto.
Qed.

(* the dictionary zstd actually uses for a frame: for the caller's bytes, what Begin_usingDict loaded (ores:
   ZSTD_loadDEntropy's result of that call); it is the model's wherever the model has one (darg_c_model) *)
Definition darg_c (a: darg) (dm: dict_model) : Prop :=
  match a with
  | DA_none => dm = no_dict
  | DA_dict _ _ b => exists ores, ld_rel b ores /\ (if Zlength b =? 0 then Some no_dict else dict_auto_c b ores) = Some dm
  | DA_ddict x _ _ => ddx_model x = Some dm
  end.

Lemma darg_c_model: forall a dm dm0, darg_c a dm -> darg_model a = Some dm0 -> dm0 = dm.
Proof.
  intros a dm dm0 Hc Hm. destruct a as [| sh pk b | x buf sh]; simpl in *.
  - congruence.
  - destruct Hc as (ores & Hl & Hc). destruct (Zlength b =? 0) eqn:E.
    + apply Z.eqb_eq, Zlength_nil_inv in E. subst b. rewrite dict_auto_nil in Hm. congruence.
    + rewrite (ld_rel_auto_some _ _ _ Hl Hm) in Hc. congruence.
  - congruence.
Qed.

(* the content of the dictionary zstd uses ends the bytes given *)
Lemma darg_c_suffix: forall sh pk b dm, darg_c (DA_dict sh pk b) dm -> Zlength b <> 0 ->
  exists pre, b = pre ++ dm_content dm.
Proof.
  intros sh pk b dm (ores & _ & Hc) Hb. rewrite (proj2 (Z.eqb_neq _ _) Hb) in Hc.
  eapply dict_auto_c_suffix; eauto.
Qed.

(* ---------- the frame fields after Begin and checkContinuity ---------- *)

(* after ZSTD_decompressBegin_usingDict / usingDDict (success; cold: the DDict's ddictIsCold; dm: the
   dictionary zstd loaded, darg_c) *)
Definition fs_after_begin (a: darg) (fs1: fstate) (cold: val) (dm: dict_model) (f: Z) : fstate :=
  match a with
  | DA_none => fs_begin3 fs1 f
  | DA_dict _ pk b =>
      if Zlength b =? 0 then fs_begin3 fs1 f else
      fs_with_dict (fs_begin3 fs1 f) (offset_val (Zlength b - Zlength (dm_content dm)) pk)
        (offset_val (Zlength b) pk) 0 (dm_id dm)
  | DA_ddict x buf _ =>
      fs_set_dictEnd
        (fs_with_dict (fs_set_cold (fs_begin3 fs1 f) cold) buf (ddx_end x buf)
           (if ddx_copied x then 1 else 0) (if dx_raw x then 0 else dict_id_of (dx_bytes x)))
        (ddx_end x buf)
  end.

Definition cold_ok (v: val) : Prop := v = Vint (Int.repr 0) \/ v = Vint (Int.repr 1).

(* the pure facts of the dictionary argument (from darg_ok and its resources) *)
Definition darg_wf (a: darg) : Prop :=
  match a with
  | DA_none => True
  | DA_dict sh pk b => readable_share sh /\ Zlength b <= 2 ^ 63 - 1 /\ bytes_ok b /\ isptr pk /\
      (exists bk o, pk = Vptr bk o /\ Ptrofs.unsigned o + Zlength b <= Ptrofs.max_unsigned)
  | DA_ddict x buf sh => isptr (dx_q x) /\ Zlength (dx_bytes x) <= 2 ^ 63 - 1 /\ bytes_ok (dx_bytes x) /\
      (dx_raw x = true \/ dict_auto_c (dx_bytes x) (dx_ld x) <> None) /\
      (ddx_copied x = false -> buf <> nullval -> readable_share sh) /\ (ddx_copied x = true -> 0 < Zlength (dx_bytes x)) /\
      ((exists bk o, buf = Vptr bk o /\ Ptrofs.unsigned o + Zlength (dx_bytes x) <= Ptrofs.max_unsigned) \/
       (buf = nullval /\ dx_ref x = Some nullval /\ dx_bytes x = nil))
  end.

Lemma begin_fields: forall a fs1 cold dm f ,
  darg_c a dm -> darg_wf a -> cold_ok (fs_ddictIsCold fs1) -> cold_ok cold ->
  let fsB := fs_after_begin a fs1 cold dm f in
  fs_isFrameDecompression fsB = Vint (Int.repr 1) /\ cold_ok (fs_ddictIsCold fsB) /\
  fs_dictID fsB = Vint (Int.repr (dm_id dm)) /\ 0 <= dm_id dm <= Int.max_unsigned /\
  fs_processedCSize fsB = Vlong (Int64.repr 0) /\
  (fs_gpDictCopy fsB = Vint (Int.repr 0) \/ fs_gpDictCopy fsB = Vint (Int.repr 1)).
Proof.
  intros a fs1 cold dm f Hm Hwf Hc1 Hc fsB. subst fsB.
  destruct a as [| sh pk b | x buf sh]; simpl in Hm |- *.
  - inversion Hm; subst. simpl. repeat split; auto; rep_lia.
  - destruct Hwf as (_ & _ & Hb & _). destruct Hm as (ores & _ & Hm).
    destruct (Zlength b =? 0) eqn:E.
    + inversion Hm; subst. simpl. repeat split; auto; rep_lia.
    + simpl. pose proof (dict_auto_c_id_range _ _ _ Hb Hm). repeat split; auto; lia.
  - destruct Hwf as (_ & _ & Hb & _). destruct (ddx_model_facts _ _ Hm) as (Hid & _ & _).
    simpl. rewrite Hid. repeat split; auto.
    + destruct (dx_raw x); [rep_lia | apply dict_id_of_range; auto].
    + destruct (dx_raw x); [rep_lia | apply dict_id_of_range; auto].
    + destruct (ddx_copied x); auto.
Qed.

Lemma continuity_keeps: forall fs d n,
  fs_isFrameDecompression (continuity fs d n) = fs_isFrameDecompression fs /\
  fs_ddictIsCold (continuity fs d n) = fs_ddictIsCold fs /\
  fs_dictID (continuity fs d n) = fs_dictID fs /\
  fs_processedCSize (continuity fs d n) = fs_processedCSize fs.
Proof. intros. unfold continuity. destruct (cont_moves fs d n); simpl; auto. Qed.

Lemma cont_dictEnd: forall a fs1 cold dm f d n,
  fs_dictEnd (continuity (fs_after_begin a fs1 cold dm f) d n) = nullval \/
  fs_dictEnd (continuity (fs_after_begin a fs1 cold dm f) d n) = darg_end a.
Proof.
  intros. unfold continuity. destruct (cont_moves _ d n); simpl.
  - destruct a as [| sh pk b | x buf sh]; simpl; auto.
    destruct (Zlength b =? 0); simpl; auto.
  - destruct a as [| sh pk b | x buf sh]; simpl; auto.
    destruct (Zlength b =? 0); simpl; auto.
Qed.

Lemma byte_at_Znth: forall l i, 0 <= i -> byte_at l i = Znth i l.
Proof. intros. unfold byte_at, Znth. destruct (Z_lt_dec i 0); [lia | reflexivity]. Qed.

(* the extDict ends with the content: the bytes b = pre ++ content seen from their end *)
Lemma ext_view_suffix: forall sh eb pre c L,
  Zlength c <= L ->
  ext_view (ExtSep sh eb (Zlength (pre ++ c)) (zbytes (pre ++ c)) (Zlength (pre ++ c)) L) c.
Proof.
  intros sh eb pre c L Hl k Hk. simpl. split; [lia |].
  rewrite Zlength_app in *. pose proof (Zlength_nonneg pre).
  rewrite Znth_map by (rewrite Zlength_app; lia). rewrite byte_at_Znth by lia.
  rewrite Znth_app2 by lia. do 3 f_equal. lia.
Qed.

Lemma veqb_ptr_null: forall b o, veqb (Vptr b o) nullval = false.
Proof. intros. unfold veqb. destruct (Val.eq _ _); [discriminate | reflexivity]. Qed.

Lemma ptr_diff_offsets: forall o n m,
  0 <= m <= n -> Ptrofs.unsigned o + n <= Ptrofs.max_unsigned ->
  Ptrofs.unsigned (Ptrofs.add o (Ptrofs.repr n)) - Ptrofs.unsigned (Ptrofs.add o (Ptrofs.repr (n - m))) = m.
Proof.
  intros. pose proof (Ptrofs.unsigned_range o).
  rewrite !Ptrofs.add_unsigned, (Ptrofs.unsigned_repr n), (Ptrofs.unsigned_repr (n - m)) by rep_lia.
  rewrite !Ptrofs.unsigned_repr by rep_lia. lia.
Qed.

Lemma cont_layout: forall a fs1 cold dm f dstc n,
  darg_c a dm -> darg_wf a -> isptr dstc -> 0 < n ->
  cont_moves (fs_after_begin a fs1 cold dm f) dstc n = true ->
  layout_ok (continuity (fs_after_begin a fs1 cold dm f) dstc n) dstc n 0 0 (ext_of a dm) /\
  ext_view (ext_of a dm) (dm_content dm).
Proof.
  intros a fs1 cold dm f dstc n Hm Hwf Hd Hn Hc.
  unfold continuity. rewrite Hc. unfold layout_ok. simpl.
  destruct dstc as [| | | | | db dofs]; try contradiction.
  destruct a as [| sh pk b | x buf sh]; simpl in Hm, Hwf |- *.
  - inversion Hm; subst. simpl. split; [| intros k Hk; rewrite Zlength_nil in Hk; lia].
    destruct (veqb _ _); rewrite Z.opp_0, !Ptrofs.add_zero; repeat split; auto; rep_lia.
  - destruct Hwf as (Hsh & Hlb & Hb & _ & bk & o & -> & Ho).
    destruct (Zlength b =? 0) eqn:E.
    + destruct Hm as (ores & _ & Hm).
      inversion Hm; subst. simpl. split; [| intros k Hk; rewrite Zlength_nil in Hk; lia].
      destruct (veqb _ _); rewrite Z.opp_0, !Ptrofs.add_zero; repeat split; auto; rep_lia.
    + simpl.
      destruct Hm as (ores & _ & Hm). destruct (dict_auto_c_suffix _ _ _ Hm) as [pre Hpre].
      assert (Hle: Zlength (dm_content dm) <= Zlength b) by (rewrite Hpre, Zlength_app; pose proof (Zlength_nonneg pre); lia).
      pose proof (Zlength_nonneg (dm_content dm)).
      rewrite veqb_ptr_null, ptr_diff_offsets by lia. split.
      * replace (0 - Zlength (dm_content dm)) with (- Zlength (dm_content dm)) by lia.
        rewrite Ptrofs.add_zero. repeat split; auto; try rep_lia. rewrite Zlength_map. auto.
      * rewrite Hpre. apply ext_view_suffix. lia.
  - destruct Hwf as (Hq & Hlb & Hb & Hraw & Hsh & Hcp & [(bk & o & -> & Ho) | (-> & Hr & Hn0)]).
    2:{ (* the DDict without content: no extDict, as for no dictionary *)
      destruct (ddx_model_facts _ _ Hm) as (_ & _ & pre & Hpre). rewrite Hn0 in Hpre.
      assert (Hc0: dm_content dm = nil) by (destruct pre; [exact (eq_sym Hpre) | discriminate]).
      assert (Hcf: ddx_copied x = false) by (unfold ddx_copied; rewrite Hr; reflexivity).
      rewrite Hc0, Hcf. simpl. split; [| intros k Hk; rewrite Zlength_nil in Hk; lia].
      destruct (veqb _ _); rewrite Z.opp_0, !Ptrofs.add_zero; repeat split; auto; rep_lia. }
    destruct (ddx_model_facts _ _ Hm) as (_ & _ & pre & Hpre).
    pose proof (Zlength_nonneg (dx_bytes x)).
    pose proof (ptr_diff_offsets o (Zlength (dx_bytes x)) (Zlength (dx_bytes x))) as Hdf.
    rewrite Z.sub_diag, Ptrofs.add_zero in Hdf.
    unfold ddx_end. simpl. rewrite veqb_ptr_null, Hdf by lia. split.
    + replace (0 - Zlength (dx_bytes x)) with (- Zlength (dx_bytes x)) by lia.
      rewrite Ptrofs.add_zero. repeat split; auto; try rep_lia.
      * destruct (ddx_copied x) eqn:Ec; [auto | apply Hsh; [reflexivity | discriminate]].
      * rewrite Zlength_map. auto.
    + rewrite Hpre. apply ext_view_suffix. rewrite Hpre in *. rewrite Zlength_app in *. pose proof (Zlength_nonneg pre). lia.
Qed.

(* ---------- facts from the resources ---------- *)

Lemma fc_bound: forall n p, 0 <= n -> field_compatible (tarray tuchar n) nil p ->
  exists b o, p = Vptr b o /\ Ptrofs.unsigned o + n <= Ptrofs.max_unsigned.
Proof.
  intros n p Hn Hfc. destruct Hfc as (Hp & _ & Hsz & _).
  destruct p as [| | | | | b o]; try contradiction. exists b, o. split; auto.
  simpl in Hsz. rewrite Z.max_r in Hsz by lia. rep_lia.
Qed.

Lemma darg_wf_res: forall DENT gv W a shd cap dst,
  darg_ok3 W a shd cap dst -> darg_res DENT gv a |-- !! darg_wf a.
Proof.
  intros DENT gv W a shd cap dst Hok. destruct a as [| sh pk b | x buf sh]; simpl in *.
  - entailer!.
  - destruct Hok as (Hsh & Hlb & Hb & _). entailer!.
    destruct (fc_bound (Zlength b) pk) as (bk & o & -> & Ho); auto. rep_lia.
    eauto.
  - assert_PROP (isptr buf \/ (buf = nullval /\ dx_ref x = Some nullval /\ dx_bytes x = nil)) as Hbd.
    { unfold ddict_rep_at. sep_apply (ddict_struct_cont x buf). entailer!. }
    unfold ddict_rep_at, ddict_mem, ddict_struct. Intros.
    rename Hok into Hsh. destruct Hbd as [Hp | (-> & Hr & Hn0)].
    2:{ (* the DDict without content *)
      assert (Hcf: ddx_copied x = false) by (unfold ddx_copied; rewrite Hr; reflexivity).
      rewrite Hcf, bytes_at_null. entailer!. }
    destruct (ddx_copied x) eqn:Ec.
    + entailer!. destruct (fc_bound (Zlength (dx_bytes x)) buf) as (bk & o & -> & Ho); auto. rep_lia.
      repeat split; auto; try (intros; discriminate);
        try (intros; match goal with Hc: ddx_copied x = true -> _ |- _ => apply Hc; auto end); left; eauto.
    + rewrite bytes_at_ptr by exact Hp. entailer!.
      destruct (Hsh eq_refl) as [Hsh1 _]; [intros E; subst buf; contradiction |].
      destruct (fc_bound (Zlength (dx_bytes x)) buf) as (bk & o & -> & Ho); auto. rep_lia.
      repeat split; auto; try (intros; congruence); left; eauto.
Qed.


Lemma sub_pp_offset: forall b o u, 0 <= u <= 2 ^ 30 -> Ptrofs.unsigned o + u <= Ptrofs.max_unsigned ->
  force_val (sem_sub_pp tuchar (offset_val u (Vptr b o)) (Vptr b o)) = Vlong (Int64.repr u).
Proof.
  intros. unfold sem_sub_pp. simpl. rewrite if_true by auto.
  simpl. pose proof (Ptrofs.unsigned_range o).
  rewrite Ptrofs.sub_add_l, Ptrofs.sub_idem, Ptrofs.add_zero_l. unfold Ptrofs.divs.
  rewrite (Ptrofs.signed_repr 1) by rep_lia. rewrite (Ptrofs.signed_repr u) by rep_lia.
  rewrite Z.quot_1_r. unfold Vptrofs. simpl. unfold Ptrofs.to_int64.
  rewrite Ptrofs.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma le_field_sublist4: forall s off, 0 <= off -> off + 4 <= Zlength s ->
  le_field s off 4 = le_field (sublist off (Zlength s) s) 0 4.
Proof.
  intros. unfold le_field, slice. f_equal. simpl skipn. unfold sublist.
  rewrite (firstn_all2 (n:=Z.to_nat (Zlength s)) s) by (rewrite Zlength_correct, Nat2Z.id; lia). reflexivity.
Qed.

Lemma magic_test: forall m, 0 <= m <= Int.max_unsigned ->
  Int.and (Int.repr m) (Int.repr (-16)) = Int.repr 407710288 <-> is_skippable_magic m = true.
Proof.
  intros m Hm. unfold is_skippable_magic, ZSTD_MAGIC_SKIPPABLE_MASK, ZSTD_MAGIC_SKIPPABLE_START.
  unfold Int.and. rewrite Int.unsigned_repr by auto.
  change (Int.unsigned (Int.repr (-16))) with 4294967280.
  assert (0 <= Z.land m 4294967280 <= Int.max_unsigned).
  { assert (Hc: Z.land 4294967280 (Z.ones 32) = 4294967280) by reflexivity.
    assert (E: Z.land m 4294967280 = (Z.land m 4294967280) mod 2 ^ 32)
      by (rewrite <- Z.land_ones by lia; rewrite <- Z.land_assoc, Hc; reflexivity).
    rewrite E. pose proof (Z.mod_pos_bound (Z.land m 4294967280) (2 ^ 32)). rep_lia. }
  rewrite Z.eqb_eq. split; intros.
  - apply (f_equal Int.unsigned) in H0. rewrite !Int.unsigned_repr in H0 by rep_lia. auto.
  - rewrite H0. reflexivity.
Qed.

Lemma ltu64_repr: forall a b, 0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int64.ltu (Int64.repr a) (Int64.repr b) = (a <? b).
Proof.
  intros. unfold Int64.ltu. rewrite !Int64.unsigned_repr by auto.
  destruct (zlt a b); symmetry; [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Qed.

Lemma win_ok_suffix: forall sh s off, readable_share sh -> bytes_ok s -> Zlength s <= 2 ^ 30 ->
  0 <= off <= Zlength s ->
  win_ok sh (Zlength s) (zbytes s) off (Zlength (sublist off (Zlength s) s)) (sublist off (Zlength s) s).
Proof.
  intros. unfold win_ok. rewrite Zlength_sublist by lia.
  repeat split; auto; try lia.
  - rewrite Zlength_map. auto.
  - apply bytes_ok_sublist. auto.
  - rewrite sublist_map. f_equal. f_equal. lia.
Qed.

Lemma sub64_repr: forall a b, Int64.sub (Int64.repr a) (Int64.repr b) = Int64.repr (a - b).
Proof.
  intros. apply Int64.eqm_samerepr. unfold Int64.sub.
  apply Int64.eqm_sub; apply Int64.eqm_sym; apply Int64.eqm_unsigned_repr.
Qed.

Lemma add_ptr_long_offset: forall p r, isptr p -> 0 <= r <= 2 ^ 30 ->
  force_val (sem_add_ptr_long tuchar p (Vlong (Int64.repr r))) = offset_val r p.
Proof.
  intros. destruct p; try contradiction. unfold sem_add_ptr_long. simpl. f_equal. f_equal.
  unfold Ptrofs.of_int64. rewrite Int64.unsigned_repr by rep_lia.
  rewrite Ptrofs.mul_commut, Ptrofs.mul_one. reflexivity.
Qed.

(* a skippable frame of size r (no error) lies within the input *)
Lemma skip_size_ok: forall s off r, bytes_ok s -> 0 <= off <= Zlength s ->
  match skippable_frame_size (sublist off (Zlength s) s) with
  | Some k => r = k | None => is_error_code r = true end ->
  is_error_code r = false ->
  skippable_frame_size (sublist off (Zlength s) s) = Some r /\ 8 <= r <= Zlength s - off.
Proof.
  intros s off r Hb Ho Hm He. destruct (skippable_frame_size (sublist off (Zlength s) s)) eqn:E.
  - subst. split; auto. pose proof (skippable_frame_size_bound _ _ (bytes_ok_sublist _ _ _ Hb) E).
    rewrite Zlength_sublist in H by lia. unfold ZSTD_SKIPPABLEHEADERSIZE in H. lia.
  - congruence.
Qed.

Lemma ret_err72: Vlong (Int64.repr (- (72))) = Vlong (Int64.repr (2 ^ 64 - 72)).
Proof. f_equal. apply Int64.eqm_samerepr. exists (-1). reflexivity. Qed.

(* srcSize_wrong is a decoding error, not a noForwardProgress code *)
Lemma dec_err72: dec_err (2 ^ 64 - 72).
Proof.
  unfold dec_err, is_error_code, ZSTD_error_noForwardProgress_destFull, ZSTD_error_noForwardProgress_inputEmpty.
  split; [reflexivity | split; discriminate].
Qed.

(* ---------- pointer witnesses ---------- *)

Lemma pws_pred_app: forall A B, pws_pred (A ++ B) = pws_pred A * pws_pred B.
Proof.
  intros. unfold pws_pred. rewrite map_app. induction A as [| w A IH]; simpl.
  - rewrite emp_sepcon. auto.
  - rewrite IH, sepcon_assoc. auto.
Qed.

Lemma pws_pred_one: forall w, pws_pred [w] = pw_pred w.
Proof. intros. unfold pws_pred. simpl. rewrite sepcon_emp. auto. Qed.

Lemma weak_valid_extend2: forall p q R S, R |-- weak_valid_pointer p && weak_valid_pointer q ->
  R * S |-- weak_valid_pointer p && weak_valid_pointer q.
Proof.
  intros. apply andp_right.
  - eapply derives_trans; [apply sepcon_derives; [exact H | apply derives_refl] |].
    eapply derives_trans; [apply sepcon_derives; [apply andp_left1, derives_refl | apply derives_refl] |].
    apply extend_weak_valid_pointer.
  - eapply derives_trans; [apply sepcon_derives; [exact H | apply derives_refl] |].
    eapply derives_trans; [apply sepcon_derives; [apply andp_left2, derives_refl | apply derives_refl] |].
    apply extend_weak_valid_pointer.
Qed.

(* the caller's dictionary bytes: buf_ok once the output array is a witness *)
Lemma dict_buf_ok_ext: forall W sh n pk shd cap dst oc,
  dict_ptr_ok W sh n pk shd cap dst -> Zlength oc = cap ->
  buf_ok (W ++ [pw_bytes shd cap oc dst]) sh n pk.
Proof.
  intros W sh n pk shd cap dst oc [(_ & _ & Hb) | [-> Hv]] Hoc; unfold buf_ok in *;
    rewrite pws_pred_app, pws_pred_one; simpl pw_pred.
  - eapply derives_trans; [| apply (weak_valid_extend2 _ _ _ (data_at shd (tarray tuchar cap) oc dst) Hb)].
    cancel.
  - destruct Hv as [Hv _]. assert_PROP (isptr pk) by entailer!. rewrite isptr_offset_val_zero by auto.
    assert (H1: pws_pred W * data_at shd (tarray tuchar cap) oc dst * data_at_ sh (tarray tuchar 0) pk
                |-- valid_pointer pk).
    { rewrite sepcon_assoc. eapply derives_trans; [apply sepcon_derives; [exact Hv | apply derives_refl] |].
      apply extend_valid_pointer. }
    apply andp_right; (eapply derives_trans; [exact H1 | apply valid_pointer_weak]).
Qed.

(* the same for ZSTD_decompress_usingDict's dictionary, which may also lie before dst (dict_ptr_ok_any) *)
Lemma dict_buf_ok_ext_any: forall W sh n pk shd cap dst oc,
  dict_ptr_ok_any W sh n pk shd cap dst -> Zlength oc = cap ->
  buf_ok (W ++ [pw_bytes shd cap oc dst]) sh n pk.
Proof.
  intros W sh n pk shd cap dst oc [Hd | (_ & _ & Hb)] Hoc; [apply dict_buf_ok_ext; auto |].
  unfold buf_ok in *. rewrite pws_pred_app, pws_pred_one; simpl pw_pred.
  eapply derives_trans; [| apply (weak_valid_extend2 _ _ _ (data_at shd (tarray tuchar cap) oc dst) Hb)].
  cancel.
Qed.


Lemma data_at_weak_valid_end: forall sh n c p, readable_share sh -> 0 < n ->
  data_at sh (tarray tuchar n) c p |-- weak_valid_pointer (offset_val n p).
Proof.
  intros. sep_apply (data_at_memory_block sh (tarray tuchar n) c p).
  simpl sizeof. rewrite Z.max_r by lia. rewrite Z.mul_1_l.
  apply memory_block_weak_valid_pointer; [lia | lia | apply readable_nonidentity; auto].
Qed.

(* Begin_usingDDict's weak validity of the DDict's end *)
Lemma ddict_begin_wv: forall W sh shd cap dst oc x buf,
  (ddx_copied x = false -> dict_ptr_ok W sh (Zlength (dx_bytes x)) buf shd cap dst) ->
  (ddx_copied x = true -> isptr buf /\ 0 < Zlength (dx_bytes x)) ->
  Zlength oc = cap ->
  pws_pred (W ++ [pw_bytes shd cap oc dst] ++
    (if ddx_copied x then [] else [pw_bytes sh (Zlength (dx_bytes x)) (zbytes (dx_bytes x)) buf])) *
  ddict_mem x buf |-- weak_valid_pointer (ddx_end x buf).
Proof.
  intros W sh shd cap dst oc x buf Hr Hc Hoc. unfold ddict_mem.
  destruct (ddx_copied x) eqn:E.
  - destruct (Hc eq_refl) as [Hp Hn]. rewrite ddx_end_ptr by exact Hp.
    sep_apply (data_at_weak_valid_end Ews (Zlength (dx_bytes x)) (zbytes (dx_bytes x)) buf (writable_readable writable_Ews) Hn).
    apply extend_weak_valid_pointer.
  - pose proof (dict_buf_ok_ext W sh (Zlength (dx_bytes x)) buf shd cap dst oc (Hr eq_refl) Hoc) as Hb.
    unfold buf_ok in Hb. rewrite app_assoc, pws_pred_app, pws_pred_one. simpl pw_pred.
    assert_PROP (isptr buf) as Hp by entailer!. rewrite ddx_end_ptr by exact Hp.
    sep_apply (data_at_data_at_ sh (tarray tuchar (Zlength (dx_bytes x))) (zbytes (dx_bytes x)) buf).
    sep_apply Hb. eapply derives_trans; [apply sepcon_derives; [apply andp_left2, derives_refl | apply derives_refl] |].
    apply extend_weak_valid_pointer.
Qed.

(* ---------- checkContinuity and the frame: witnesses, comparisons, the output split ---------- *)

Definition ext_wit (e: ext_seg) : list ptr_witness :=
  match e with ExtSep sh eb en ec _ _ => [pw_bytes sh en ec eb] | _ => [] end.

Lemma pws_ext: forall e, pws_pred (ext_wit e) = ext_res e.
Proof. intros. destruct e; simpl; unfold pws_pred; simpl; rewrite ?sepcon_emp; auto. Qed.

Definition wcont (W: list ptr_witness) (shd: share) (cap: Z) (oc: list val) (dst: val) (a: darg) (dm: dict_model) :=
  W ++ [pw_bytes shd cap oc dst] ++ ext_wit (ext_of a dm).

Lemma wcont_split: forall W shd cap oc dst a dm,
  pws_pred (wcont W shd cap oc dst a dm) =
  pws_pred W * data_at shd (tarray tuchar cap) oc dst * ext_res (ext_of a dm).
Proof.
  intros. unfold wcont. rewrite !pws_pred_app, pws_pred_one, pws_ext. simpl pw_pred.
  rewrite sepcon_assoc. auto.
Qed.

Transparent denote_tc_test_eq.
Lemma test_eq_weak: forall P x y, sameblock x y = true ->
  P |-- weak_valid_pointer x -> P |-- weak_valid_pointer y -> P |-- denote_tc_test_eq x y.
Proof.
  intros P x y Hs Hx Hy. destruct x; try discriminate; destruct y; try discriminate.
  unfold denote_tc_test_eq, test_eq_ptrs. rewrite Hs. apply andp_right; auto.
Qed.

Lemma test_eq_null_weak: forall P x, isptr x -> P |-- weak_valid_pointer x -> P |-- denote_tc_test_eq x nullval.
Proof.
  intros P x Hx H. destruct x; try contradiction. unfold denote_tc_test_eq, nullval. simpl.
  apply andp_right; [apply prop_right; auto | auto].
Qed.

Lemma test_eq_null_null: forall P, P |-- denote_tc_test_eq nullval nullval.
Proof. intros. unfold denote_tc_test_eq, nullval. simpl. apply andp_right; apply prop_right; auto. Qed.
Opaque denote_tc_test_eq.

Lemma data_at_valid_inside: forall sh n c p i, readable_share sh -> 0 <= i < n ->
  data_at sh (tarray tuchar n) c p |-- valid_pointer (offset_val i p).
Proof.
  intros. sep_apply (data_at_memory_block sh (tarray tuchar n) c p).
  simpl sizeof. rewrite Z.max_r by lia. rewrite Z.mul_1_l.
  apply memory_block_valid_pointer; [lia | apply readable_nonidentity; auto].
Qed.

Lemma data_at_weak_valid_any: forall sh n c p i, readable_share sh -> 0 <= i <= n -> 0 < n ->
  data_at sh (tarray tuchar n) c p |-- weak_valid_pointer (offset_val i p).
Proof.
  intros. sep_apply (data_at_memory_block sh (tarray tuchar n) c p).
  simpl sizeof. rewrite Z.max_r by lia. rewrite Z.mul_1_l.
  apply memory_block_weak_valid_pointer; [lia | lia | apply readable_nonidentity; auto].
Qed.

(* the output array split at the bytes written so far *)
Lemma split_out: forall sh cap (oc: list val) dst u, 0 <= u <= cap -> Zlength oc = cap ->
  field_compatible (tarray tuchar cap) [] dst ->
  data_at sh (tarray tuchar cap) oc dst =
  data_at sh (tarray tuchar u) (sublist 0 u oc) dst *
  data_at sh (tarray tuchar (cap - u)) (sublist u cap oc) (offset_val u dst).
Proof.
  intros. unfold tarray. rewrite (split2_data_at_Tarray_tuchar sh cap u oc dst) by auto.
  rewrite field_address0_offset by auto with field_compatible.
  simpl nested_field_offset. rewrite Z.mul_1_l, Z.add_0_l. auto.
Qed.

Lemma dict_end_wv: forall W sh n (c: list val) pk shd cap oc dst,
  dict_ptr_ok W sh n pk shd cap dst -> Zlength oc = cap ->
  pws_pred W * data_at shd (tarray tuchar cap) oc dst * data_at sh (tarray tuchar n) c pk
  |-- weak_valid_pointer (offset_val n pk).
Proof.
  intros. pose proof (dict_buf_ok_ext W sh n pk shd cap dst oc H H0) as Hb. unfold buf_ok in Hb.
  rewrite pws_pred_app, pws_pred_one in Hb. simpl pw_pred in Hb.
  sep_apply (data_at_data_at_ sh (tarray tuchar n) c pk).
  sep_apply Hb. apply andp_left2, derives_refl.
Qed.

Lemma dict_end_wv_any: forall W sh n (c: list val) pk shd cap oc dst,
  dict_ptr_ok_any W sh n pk shd cap dst -> Zlength oc = cap ->
  pws_pred W * data_at shd (tarray tuchar cap) oc dst * data_at sh (tarray tuchar n) c pk
  |-- weak_valid_pointer (offset_val n pk).
Proof.
  intros. pose proof (dict_buf_ok_ext_any W sh n pk shd cap dst oc H H0) as Hb. unfold buf_ok in Hb.
  rewrite pws_pred_app, pws_pred_one in Hb. simpl pw_pred in Hb.
  sep_apply (data_at_data_at_ sh (tarray tuchar n) c pk).
  sep_apply Hb. apply andp_left2, derives_refl.
Qed.

Lemma sameblock_offset: forall i j x y, sameblock (offset_val i x) (offset_val j y) = sameblock x y.
Proof. intros. destruct x, y; reflexivity. Qed.

Lemma sameblock_refl_ptr: forall x, isptr x -> sameblock x x = true.
Proof. intros. destruct x; try contradiction. simpl. destruct (peq b b); auto. Qed.

(* the preconditions of ZSTD_checkContinuity after Begin, at dst + u with n = cap - u *)
Lemma cont_pre: forall W shd cap oc dst a fs1 cold dm f u,
  darg_ok3 W a shd cap dst -> darg_wf a -> darg_c a dm -> Zlength oc = cap ->
  field_compatible (tarray tuchar cap) [] dst -> readable_share shd -> 0 <= u <= cap ->
  (0 < cap - u -> fs_gpDictCopy (fs_after_begin a fs1 cold dm f) = Vint (Int.repr 0) ->
     pws_pred (wcont W shd cap oc dst a dm) |--
     denote_tc_test_eq (offset_val u dst) (fs_previousDstEnd (fs_after_begin a fs1 cold dm f))) /\
  (cont_moves (fs_after_begin a fs1 cold dm f) (offset_val u dst) (cap - u) = true ->
     isptr (offset_val u dst) /\
     (pws_pred (wcont W shd cap oc dst a dm) |-- denote_tc_test_eq (fs_previousDstEnd (fs_after_begin a fs1 cold dm f)) nullval) /\
     (fs_previousDstEnd (fs_after_begin a fs1 cold dm f) <> nullval ->
        sameblock (fs_previousDstEnd (fs_after_begin a fs1 cold dm f)) (fs_prefixStart (fs_after_begin a fs1 cold dm f)) = true)).
Proof.
  intros W shd cap oc dst a fs1 cold dm f u Hok Hwf Hm Hoc Hfc Hsh Hu.
  assert (Hd: isptr dst) by (destruct Hfc; auto).
  assert (Hdc: isptr (offset_val u dst)) by (destruct dst; try contradiction; exact I).
  rewrite wcont_split.
  assert (Hval: forall R, 0 < cap - u -> pws_pred W * data_at shd (tarray tuchar cap) oc dst * R
                 |-- valid_pointer (offset_val u dst)).
  { intros. sep_apply (data_at_valid_inside shd cap oc dst u Hsh). lia.
    apply extend_valid_pointer. }
  destruct a as [| sh pk b | x buf sh]; simpl.
  - split; [intros Hn _ | intros _; split; [auto | split; [apply test_eq_null_null | congruence]]].
    apply test_eq_null_weak; auto. eapply derives_trans; [apply Hval; lia | apply valid_pointer_weak].
  - destruct (Zlength b =? 0) eqn:Eb.
    + simpl. split; [intros Hn _ | intros _; split; [auto | split; [apply test_eq_null_null | congruence]]].
      apply test_eq_null_weak; auto. eapply derives_trans; [apply Hval; lia | apply valid_pointer_weak].
    + simpl.
      pose proof Hok as (_ & _ & _ & Hdp).
      assert (Hsb: sameblock dst pk = true).
      { destruct Hdp as [[(Hsb & _) | (Hb0 & _)] | (Hsb & _)]; auto. rewrite Hb0 in Eb; discriminate. }
      assert (Hpk: isptr pk) by (destruct Hwf as (_ & _ & _ & Hpk & _); auto).
      assert (Hwv: pws_pred W * data_at shd (tarray tuchar cap) oc dst *
                   data_at sh (tarray tuchar (Zlength b)) (zbytes b) pk |-- weak_valid_pointer (offset_val (Zlength b) pk))
        by (apply dict_end_wv_any; auto).
      assert (Hpb: isptr (offset_val (Zlength b) pk)) by (destruct pk; try contradiction; exact I).
      split; [intros Hn _ | intros _; split; [auto | split]].
      * apply test_eq_weak; [rewrite sameblock_offset; auto | | auto].
        eapply derives_trans; [apply Hval; lia | apply valid_pointer_weak].
      * apply test_eq_null_weak; auto.
      * intros _. rewrite sameblock_offset. apply sameblock_refl_ptr; auto.
  - destruct Hwf as (_ & _ & _ & _ & Hrs & Hcp & [(bk & o & Hbuf & _) | (Hbuf & Hr & Hn0)]); subst buf.
    2:{ (* the DDict without content: no extDict, previousDstEnd NULL *)
      assert (Hcf: ddx_copied x = false) by (unfold ddx_copied; rewrite Hr; reflexivity).
      simpl. rewrite Hcf. simpl.
      split; [intros Hn _ | intros _; split; [auto | split; [apply test_eq_null_null | congruence]]].
      apply test_eq_null_weak; auto. eapply derives_trans; [apply Hval; lia | apply valid_pointer_weak]. }
    cbv beta iota. set (buf := Vptr bk o).
    assert (Hbn: buf <> nullval) by (unfold buf; discriminate).
    rewrite (ddx_end_ptr x buf) by exact I.
    assert (Hbp: isptr buf) by exact I.
    assert (Hpb: isptr (offset_val (Zlength (dx_bytes x)) buf)) by exact I.
    assert (Hwv: pws_pred W * data_at shd (tarray tuchar cap) oc dst *
                 data_at (if ddx_copied x then Ews else sh) (tarray tuchar (Zlength (dx_bytes x)))
                   (zbytes (dx_bytes x)) buf |-- weak_valid_pointer (offset_val (Zlength (dx_bytes x)) buf)).
    { destruct (ddx_copied x) eqn:Ec.
      - sep_apply (data_at_weak_valid_end Ews (Zlength (dx_bytes x)) (zbytes (dx_bytes x)) buf
                     (writable_readable writable_Ews) (Hcp eq_refl)).
        eapply derives_trans; [| apply (extend_weak_valid_pointer _ (pws_pred W * data_at shd (tarray tuchar cap) oc dst))].
        cancel.
      - destruct (Hok Ec Hbn) as [_ [Hp | (_ & Hn0 & Hv)]].
        + apply dict_end_wv; auto.
        + rewrite Hn0, isptr_offset_val_zero by auto.
          eapply derives_trans; [| apply valid_pointer_weak].
          sep_apply Hv. apply extend_valid_pointer. }
    split; [intros Hn Hg | intros _; split; [auto | split]].
    + destruct (ddx_copied x) eqn:Ec; [inversion Hg |].
      destruct (Hok Ec Hbn) as [_ [[[Hsb _] | [Hn0 Hv]] | (Hc0 & _)]]; [| | lia].
      * apply test_eq_weak; [rewrite sameblock_offset; auto | | auto].
        eapply derives_trans; [apply Hval; lia | apply valid_pointer_weak].
      * rewrite Hn0. rewrite isptr_offset_val_zero by auto.
        apply denote_tc_test_eq_split.
        -- apply Hval; lia.
        -- destruct Hv as [Hv _]. sep_apply Hv. apply extend_valid_pointer.
    + apply test_eq_null_weak; auto.
    + intros _. unfold buf. simpl. destruct (peq bk bk); auto.
Qed.

(* a non-empty dictionary used by reference lies after dst + cap (dict_ptr_ok), so its end is never the
   current output position dst + u (u < cap) *)
Lemma dict_end_ne: forall W sh n p shd cap dst u,
  dict_ptr_ok W sh n p shd cap dst -> 0 < n -> 0 <= u < cap ->
  (exists bk o, p = Vptr bk o /\ Ptrofs.unsigned o + n <= Ptrofs.max_unsigned) ->
  offset_val u dst <> offset_val n p.
Proof.
  intros W sh n p shd cap dst u Hd Hn Hu (bk & o & -> & Ho).
  destruct Hd as [(_ & Hpos & _) | (Hn0 & _)]; [| lia].
  destruct dst as [| | | | | b1 o1]; try contradiction. simpl in Hpos |- *.
  intros E. pose proof (Ptrofs.unsigned_range o1). pose proof (Ptrofs.unsigned_range o).
  assert (Eo: Ptrofs.unsigned (Ptrofs.add o1 (Ptrofs.repr u)) = Ptrofs.unsigned (Ptrofs.add o (Ptrofs.repr n)))
    by congruence.
  rewrite !Ptrofs.add_unsigned in Eo. rewrite (Ptrofs.unsigned_repr u), (Ptrofs.unsigned_repr n) in Eo by rep_lia.
  rewrite !Ptrofs.unsigned_repr in Eo by rep_lia. lia.
Qed.

Lemma veqb_ne: forall a b, a <> b -> veqb a b = false.
Proof. intros. unfold veqb. destruct (Val.eq a b); congruence. Qed.

(* the caller's non-empty dictionary ends exactly at dst and nothing was written yet (u = 0), with room left:
   ZSTD_checkContinuity finds dst contiguous with the dictionary and keeps it as the prefix of dst's output
   (ZSTD_decompress_usingDict with [dict | dst] in one object, dict_ptr_ok_any) *)
Definition gap0 (a: darg) (dst: val) (cap u: Z) : bool :=
  match a with
  | DA_dict _ pk b => (0 <? Zlength b) && (u =? 0) && (0 <? cap) && veqb (offset_val (Zlength b) pk) dst
  | _ => false
  end.

Lemma gap0_intro: forall sh pk b dst cap, 0 < Zlength b -> 0 < cap -> offset_val (Zlength b) pk = dst ->
  gap0 (DA_dict sh pk b) dst cap 0 = true.
Proof.
  intros. unfold gap0. rewrite (proj2 (Z.ltb_lt _ _) H), (proj2 (Z.ltb_lt _ _) H0). subst dst.
  unfold veqb. destruct (Val.eq _ _); [reflexivity | congruence].
Qed.

Lemma gap0_elim: forall a dst cap u, gap0 a dst cap u = true ->
  exists sh pk b, a = DA_dict sh pk b /\ 0 < Zlength b /\ u = 0 /\ 0 < cap /\ offset_val (Zlength b) pk = dst.
Proof.
  intros a dst cap u H. destruct a as [| sh pk b | x buf sh]; try discriminate. simpl in H.
  apply andb_prop in H. destruct H as [H H4]. apply andb_prop in H. destruct H as [H H3].
  apply andb_prop in H. destruct H as [H1 H2].
  exists sh, pk, b. apply Z.ltb_lt in H1. apply Z.eqb_eq in H2. apply Z.ltb_lt in H3.
  unfold veqb in H4. destruct (Val.eq _ _); [| discriminate]. auto 6.
Qed.

(* the end of a non-empty dictionary before dst (dict_ptr_ok_any) is the output position dst + u only at u = 0 *)
Lemma dict_end_eq_any: forall W sh n p shd cap dst u,
  dict_ptr_ok_any W sh n p shd cap dst -> 0 < n -> 0 <= u < cap ->
  (exists bk o, p = Vptr bk o /\ Ptrofs.unsigned o + n <= Ptrofs.max_unsigned) ->
  (exists bd od, dst = Vptr bd od /\ Ptrofs.unsigned od + cap <= Ptrofs.max_unsigned) ->
  offset_val u dst = offset_val n p -> u = 0.
Proof.
  intros W sh n p shd cap dst u Hd Hn Hu Hp (bd & od & -> & Hod) E.
  destruct Hd as [Hd | (_ & Hpos & _)].
  - exfalso. exact (dict_end_ne W sh n p shd cap (Vptr bd od) u Hd Hn Hu Hp E).
  - destruct Hp as (bk & o & -> & Ho). simpl in Hpos, E. destruct Hpos as [Hle _].
    pose proof (Ptrofs.unsigned_range o). pose proof (Ptrofs.unsigned_range od).
    assert (Eo: Ptrofs.unsigned (Ptrofs.add od (Ptrofs.repr u)) = Ptrofs.unsigned (Ptrofs.add o (Ptrofs.repr n)))
      by congruence.
    rewrite !Ptrofs.add_unsigned in Eo. rewrite (Ptrofs.unsigned_repr u), (Ptrofs.unsigned_repr n) in Eo by rep_lia.
    rewrite !Ptrofs.unsigned_repr in Eo by rep_lia. lia.
Qed.

(* with room left in the output, ZSTD_checkContinuity starts a new segment at dst + u, except for an empty
   DDict used by reference that sits exactly at dst + u (then the context already starts there) *)
Lemma cont_moves_cases: forall W shd cap dst a fs1 cold dm f u,
  darg_ok3 W a shd cap dst -> darg_wf a -> darg_c a dm ->
  field_compatible (tarray tuchar cap) [] dst -> 0 <= u < cap -> gap0 a dst cap u = false ->
  cont_moves (fs_after_begin a fs1 cold dm f) (offset_val u dst) (cap - u) = true \/
  exists x buf sh, a = DA_ddict x buf sh /\ ddx_copied x = false /\ dx_bytes x = [] /\ buf = offset_val u dst.
Proof.
  intros W shd cap dst a fs1 cold dm f u Hok Hwf Hm Hfc Hu Hg.
  assert (Hd: isptr dst) by (destruct Hfc; auto).
  assert (Hdb: exists bd od, dst = Vptr bd od /\ Ptrofs.unsigned od + cap <= Ptrofs.max_unsigned)
    by (apply fc_bound; auto; lia).
  unfold cont_moves. replace (0 <? cap - u) with true by (symmetry; apply Z.ltb_lt; lia). simpl.
  assert (Hdn: offset_val u dst <> nullval) by (destruct dst; try contradiction; discriminate).
  destruct a as [| sh pk b | x buf sh]; simpl.
  - left. rewrite (veqb_ne (offset_val u dst)) by auto. simpl negb; rewrite orb_true_r. auto.
  - left. destruct (Zlength b =? 0) eqn:Eb.
    + simpl. rewrite (veqb_ne (offset_val u dst)) by auto. simpl negb; rewrite orb_true_r. auto.
    + simpl. rewrite (veqb_ne (offset_val u dst)); [simpl negb; rewrite orb_true_r; auto |].
      destruct Hok as (_ & _ & _ & Hp). destruct Hwf as (_ & _ & _ & _ & Hwb).
      apply Z.eqb_neq in Eb. pose proof (Zlength_nonneg b).
      intros E. pose proof (dict_end_eq_any W sh (Zlength b) pk shd cap dst u Hp ltac:(lia) Hu Hwb Hdb E) as Hu0.
      subst u. rewrite isptr_offset_val_zero in E by auto.
      rewrite (gap0_intro sh pk b dst cap) in Hg; [discriminate | lia | lia | auto].
  - destruct (ddx_copied x) eqn:Ec; simpl.
    + left. auto.
    + destruct Hwf as (_ & _ & _ & _ & _ & _ & [(bk & o & Ebuf & Ho) | (Ebuf & _ & _)]).
      2:{ (* the DDict without content: previousDstEnd is NULL *)
        subst buf. left. rewrite (veqb_ne (offset_val u dst)) by exact Hdn. simpl negb; rewrite orb_true_r. auto. }
      assert (Hbn: buf <> nullval) by (subst buf; discriminate).
      pose proof (Zlength_nonneg (dx_bytes x)).
      destruct (Zlength (dx_bytes x) =? 0) eqn:Ez.
      * apply Z.eqb_eq in Ez. apply Zlength_nil_inv in Ez.
        destruct (veqb (offset_val u dst) (ddx_end x buf)) eqn:Ev.
        -- right. exists x, buf, sh. split; [auto | split; [auto | split; [auto |]]].
           unfold veqb in Ev. destruct (Val.eq _ _) as [Eq |]; [| discriminate].
           unfold ddx_end in Eq. rewrite Ez, Zlength_nil in Eq. subst buf. simpl in Eq.
           rewrite Ptrofs.add_zero in Eq. auto.
        -- left. simpl negb. rewrite orb_true_r. auto.
      * left. rewrite (ddx_end_ptr x buf) by (subst buf; exact I).
        rewrite (veqb_ne (offset_val u dst)); [simpl negb; rewrite orb_true_r; auto |].
        destruct (Hok Ec Hbn) as [_ [Hp | (Hc0 & _)]]; [| lia]. apply Z.eqb_neq in Ez.
        eapply dict_end_ne; eauto; lia.
Qed.

(* the frame's layout after ZSTD_checkContinuity, in every case *)
Lemma cont_layout_sep: forall W shd cap dst a fs1 cold dm f u,
  darg_ok3 W a shd cap dst -> darg_wf a -> darg_c a dm ->
  field_compatible (tarray tuchar cap) [] dst -> 0 <= u < cap -> gap0 a dst cap u = false ->
  layout_ok (continuity (fs_after_begin a fs1 cold dm f) (offset_val u dst) (cap - u)) (offset_val u dst) (cap - u) 0 0
    (ext_of a dm) /\ ext_view (ext_of a dm) (dm_content dm).
Proof.
  intros W shd cap dst a fs1 cold dm f u Hok Hwf Hm Hfc Hu Hg.
  assert (Hd: isptr dst) by (destruct Hfc; auto).
  assert (Hdu: isptr (offset_val u dst)) by (destruct dst; try contradiction; simpl; auto).
  destruct (cont_moves_cases W shd cap dst a fs1 cold dm f u Hok Hwf Hm Hfc Hu Hg) as [Hc | (x & buf & sh & -> & Ec & Ex & Eb)].
  - apply cont_layout; auto. lia.
  - destruct (cont_moves (fs_after_begin (DA_ddict x buf sh) fs1 cold dm f) (offset_val u dst) (cap - u)) eqn:Hc.
    + apply cont_layout; auto. lia.
    + unfold continuity. rewrite Hc. clear Hc.
      destruct (ddx_model_facts _ _ Hm) as (_ & _ & pre & Hpre).
      rewrite Ex in Hpre. destruct pre; [| apply (f_equal (@Zlength Z)) in Hpre; rewrite Zlength_nil, Zlength_app, Zlength_cons in Hpre;
        pose proof (Zlength_nonneg pre); pose proof (Zlength_nonneg (dm_content dm)); lia].
      simpl in Hpre. subst buf. unfold ext_of, layout_ok, ddx_end. rewrite Ec, Ex. simpl.
      destruct dst as [| | | | | db dofs]; try contradiction. simpl.
      rewrite !Ptrofs.add_zero. split.
      * destruct (Hok Ec ltac:(discriminate)) as [Hsh _].
        rewrite ?Ex, ?Zlength_nil, ?Ptrofs.add_zero. repeat split; auto; rep_lia.
      * rewrite <- Hpre. intros k Hk. rewrite Zlength_nil in Hk. lia.
Qed.

Lemma wcont_fold: forall W shd cap oc dst a dm,
  pws_pred W * data_at shd (tarray tuchar cap) oc dst * ext_res (ext_of a dm) |-- pws_pred (wcont W shd cap oc dst a dm).
Proof. intros. rewrite wcont_split. auto. Qed.

Lemma wcont_unfold: forall W shd cap oc dst a dm,
  pws_pred (wcont W shd cap oc dst a dm) |-- pws_pred W * data_at shd (tarray tuchar cap) oc dst * ext_res (ext_of a dm).
Proof. intros. rewrite wcont_split. auto. Qed.

Lemma ext_of_not_in: forall a dm, match ext_of a dm with ExtIn _ _ => False | _ => True end.
Proof.
  intros. destruct a as [| sh pk b | x buf sh]; simpl; auto;
    [destruct (Zlength b =? 0) | destruct buf; try destruct (ddx_copied x)]; auto.
Qed.

(* ZSTD_decompressFrame with no capacity left: the output position is weakly valid *)
Lemma frame_wv: forall W shd cap oc dst u, buf_ok W shd cap dst -> u = cap -> 0 <= u ->
  writable_share shd -> field_compatible (tarray tuchar cap) [] dst ->
  pws_pred (W ++ [pw_bytes shd u (sublist 0 u oc) dst]) |-- weak_valid_pointer (offset_val 0 (offset_val u dst)).
Proof.
  intros W shd cap oc dst u Hb -> Hu Hsh Hfc.
  assert (Hd: isptr dst) by (destruct Hfc; auto).
  rewrite isptr_offset_val_zero by (destruct dst; try contradiction; exact I).
  rewrite pws_pred_app, pws_pred_one. simpl pw_pred.
  destruct (zlt 0 cap).
  - sep_apply (data_at_weak_valid_end shd cap (sublist 0 cap oc) dst (writable_readable Hsh) l).
    eapply derives_trans; [| apply (extend_weak_valid_pointer _ (pws_pred W))]. cancel.
  - assert (cap = 0) by lia. subst cap. unfold buf_ok in Hb.
    sep_apply (data_at_data_at_ shd (tarray tuchar 0) (sublist 0 0 oc) dst).
    sep_apply Hb. apply andp_left2. rewrite isptr_offset_val_zero by auto. apply derives_refl.
Qed.

(* after the frame: the output array again in one piece *)
Lemma merge_out: forall sh cap (oc oc': list val) dst u, 0 <= u <= cap -> Zlength oc = cap -> Zlength oc' = cap - u ->
  field_compatible (tarray tuchar cap) [] dst ->
  data_at sh (tarray tuchar u) (sublist 0 u oc) dst * data_at sh (tarray tuchar (cap - u)) oc' (offset_val u dst)
  = data_at sh (tarray tuchar cap) (sublist 0 u oc ++ oc') dst.
Proof.
  intros. subst cap. assert (Hl: Zlength (sublist 0 u oc) = u) by (rewrite Zlength_sublist by lia; lia).
  rewrite (split_out sh (Zlength oc) (sublist 0 u oc ++ oc') dst u); auto; [| rewrite Zlength_app; lia].
  rewrite sublist0_app1 by lia. rewrite sublist_sublist00 by lia.
  rewrite sublist_app2 by lia. rewrite Hl, Z.sub_diag. rewrite (sublist_same 0 _ oc') by lia. reflexivity.
Qed.

Lemma error_of_10: forall r, error_of r = 10 -> is_error_code r = true.
Proof. intros. unfold error_of in H. destruct (is_error_code r); auto. discriminate. Qed.

Lemma error_of_range: forall r, 0 <= r <= Int64.max_unsigned -> 0 <= error_of r < 120.
Proof.
  intros. unfold error_of. destruct (is_error_code r) eqn:E; [| lia].
  unfold is_error_code in E. apply Z.ltb_lt in E. rep_lia.
Qed.

Lemma error_of_eq10: forall r, 0 <= r <= Int64.max_unsigned ->
  Int.repr (error_of r) = Int.repr 10 -> error_of r = 10.
Proof.
  intros. pose proof (error_of_range r H). apply (f_equal Int.unsigned) in H0.
  rewrite !Int.unsigned_repr in H0 by rep_lia. auto.
Qed.

Lemma dictEnd_after: forall fs a fs1 cold dm f d n fs',
  fs_dictEnd fs' = fs_dictEnd (continuity (fs_after_begin a fs1 cold dm f) d n) ->
  fs_dictEnd fs' = fs_dictEnd fs \/ fs_dictEnd fs' = nullval \/ fs_dictEnd fs' = darg_end a.
Proof. intros. rewrite H. destruct (cont_dictEnd a fs1 cold dm f d n); auto. Qed.

(* the witnesses for Begin_usingDDict: the output array and the caller's bytes of a DDict by reference *)
Definition wddict (W: list ptr_witness) (shd: share) (cap: Z) (oc: list val) (dst: val) (x: ddx) (buf: val) (sh: share) :=
  W ++ [pw_bytes shd cap oc dst] ++
  (if ddx_copied x then [] else [pw_bytes sh (Zlength (dx_bytes x)) (zbytes (dx_bytes x)) buf]).

Lemma wddict_split: forall W shd cap oc dst x buf sh,
  pws_pred (wddict W shd cap oc dst x buf sh) =
  pws_pred W * data_at shd (tarray tuchar cap) oc dst *
  (if ddx_copied x then emp else data_at sh (tarray tuchar (Zlength (dx_bytes x))) (zbytes (dx_bytes x)) buf).
Proof.
  intros. unfold wddict. rewrite !pws_pred_app, pws_pred_one. simpl pw_pred.
  destruct (ddx_copied x); [unfold pws_pred; simpl | rewrite pws_pred_one; simpl pw_pred];
    rewrite ?sepcon_emp, ?sepcon_assoc; auto.
Qed.

Lemma wddict_fold: forall W shd cap oc dst x buf sh,
  pws_pred W * data_at shd (tarray tuchar cap) oc dst *
  (if ddx_copied x then emp else data_at sh (tarray tuchar (Zlength (dx_bytes x))) (zbytes (dx_bytes x)) buf)
  |-- pws_pred (wddict W shd cap oc dst x buf sh).
Proof. intros. rewrite wddict_split. auto. Qed.

Lemma wddict_unfold: forall W shd cap oc dst x buf sh,
  pws_pred (wddict W shd cap oc dst x buf sh) |--
  pws_pred W * data_at shd (tarray tuchar cap) oc dst *
  (if ddx_copied x then emp else data_at sh (tarray tuchar (Zlength (dx_bytes x))) (zbytes (dx_bytes x)) buf).
Proof. intros. rewrite wddict_split. auto. Qed.

Lemma pws_fold1: forall W sh n c q,
  pws_pred W * data_at sh (tarray tuchar n) c q |-- pws_pred (W ++ [pw_bytes sh n c q]).
Proof. intros. rewrite pws_pred_app, pws_pred_one. apply derives_refl. Qed.

Lemma pws_unfold1: forall W sh n c q,
  pws_pred (W ++ [pw_bytes sh n c q]) |-- pws_pred W * data_at sh (tarray tuchar n) c q.
Proof. intros. rewrite pws_pred_app, pws_pred_one. apply derives_refl. Qed.

(* ZSTD_decompressBegin_usingDict on the caller's bytes: its model and frame fields as fs_after_begin *)
Lemma usingdict_dict: forall sh pk b ores dm fs1 cold f, isptr pk -> ld_rel b ores ->
  usingdict_model pk b ores = Some dm ->
  darg_c (DA_dict sh pk b) dm /\
  (if Zlength b =? 0 then fs_begin3 fs1 f
   else fs_with_dict (fs_begin3 fs1 f) (offset_val (Zlength b - Zlength (dm_content dm)) pk)
          (offset_val (Zlength b) pk) 0 (dm_id dm)) = fs_after_begin (DA_dict sh pk b) fs1 cold dm f.
Proof.
  intros sh pk b ores dm fs1 cold f Hp Hl Hu. unfold usingdict_model in Hu.
  rewrite if_false in Hu by (destruct pk; try contradiction; discriminate).
  split; [exists ores; auto | reflexivity].
Qed.

(* ---------- the premises of ZSTD_decompressFrame on the dictionary ---------- *)

Lemma darg_c_content: forall a dm, darg_wf a -> darg_c a dm -> bytes_ok (dm_content dm).
Proof.
  intros a dm Hwf Hc. destruct a as [| sh pk b | x buf sh]; simpl in *.
  - subst. unfold bytes_ok. simpl. constructor.
  - destruct Hwf as (_ & _ & Hb & _). destruct Hc as (ores & _ & Hc).
    destruct (Zlength b =? 0); [inversion Hc; subst; unfold bytes_ok; simpl; constructor |].
    destruct (dict_auto_c_suffix _ _ _ Hc) as [pre Hpre]. rewrite Hpre in Hb.
    unfold bytes_ok in *. apply Forall_app in Hb. tauto.
  - destruct Hwf as (_ & _ & Hb & _). destruct (ddx_model_facts _ _ Hc) as (_ & _ & pre & Hpre).
    rewrite Hpre in Hb. unfold bytes_ok in *. apply Forall_app in Hb. tauto.
Qed.

Lemma zbytes_byte_val: forall b i, bytes_ok b -> 0 <= i < Zlength b ->
  is_byte_val (Znth i (zbytes b)).
Proof.
  intros b i Hb Hi. rewrite Znth_map by lia. exists (Znth i b). split; [| reflexivity].
  unfold bytes_ok in Hb. rewrite Forall_forall in Hb. apply Hb. apply Znth_In. lia.
Qed.

Lemma ext_def_of: forall a dm, darg_wf a -> darg_c a dm -> ext_def (ext_of a dm).
Proof.
  intros a dm Hwf Hc k Hk. destruct a as [| sh pk b | x buf sh]; simpl in Hk |- *.
  - lia.
  - destruct (Zlength b =? 0) eqn:E; simpl in Hk |- *; [lia |].
    destruct Hwf as (_ & _ & Hb & _). destruct Hc as (ores & _ & Hc). rewrite E in Hc.
    destruct (dict_auto_c_suffix _ _ _ Hc) as [pre Hpre].
    assert (Zlength (dm_content dm) <= Zlength b)
      by (apply (f_equal (@Zlength Z)) in Hpre; rewrite Zlength_app in Hpre; pose proof (Zlength_nonneg pre); lia).
    apply zbytes_byte_val; auto; lia.
  - destruct Hwf as (_ & _ & Hb & _). destruct buf; try destruct (ddx_copied x); simpl in Hk |- *; try lia;
      apply zbytes_byte_val; auto; lia.
Qed.

Lemma hist_ptrs_after: forall a fs1 cold dm f d n, darg_wf a -> isptr d ->
  hist_ptrs_e (continuity (fs_after_begin a fs1 cold dm f) d n) (ext_of a dm).
Proof.
  intros a fs1 cold dm f d n Hwf Hd. unfold continuity.
  destruct (cont_moves _ d n); unfold hist_ptrs_e.
  - destruct d as [| | | | | db dofs]; try contradiction. simpl. split; [exact I | split; [exact I |]].
    destruct a as [| sh pk b | x buf sh]; simpl; auto.
    + destruct (Zlength b =? 0) eqn:E; simpl; auto. right. split; auto.
      pose proof (Zlength_nonneg b). lia.
    + destruct Hwf as (_ & _ & _ & _ & _ & _ & [(bk & o & -> & _) | (-> & _ & _)]); simpl.
      * right. split; auto. pose proof (Zlength_nonneg (dx_bytes x)). lia.
      * left. reflexivity.
  - destruct a as [| sh pk b | x buf sh]; simpl.
    + split; [| split]; auto.
    + destruct (Zlength b =? 0) eqn:E; simpl; [split; [| split]; auto |].
      destruct Hwf as (_ & _ & _ & Hpk & _).
      split; [| split]; auto; destruct pk; try contradiction; exact I.
    + destruct Hwf as (_ & _ & _ & _ & _ & _ & [(bk & o & -> & _) | (-> & _ & _)]).
      * split; [exact I | split; [exact I |]]. right. unfold ddx_end. split; auto.
        pose proof (Zlength_nonneg (dx_bytes x)). lia.
      * simpl. split; [| split]; auto.
Qed.

Lemma ext0_after: forall W shd cap dst a fs1 cold dm f d n w,
  darg_ok3 W a shd cap dst -> darg_wf a ->
  ext0_ok (W ++ [w]) (continuity (fs_after_begin a fs1 cold dm f) d n) (ext_of a dm).
Proof.
  intros W shd cap dst a fs1 cold dm f d n w Hok Hwf.
  destruct a as [| sh pk b | x buf sh]; simpl; auto.
  - destruct (Zlength b =? 0) eqn:E; simpl; auto. intros H0. apply Z.eqb_neq in E. contradiction.
  - destruct Hwf as (_ & _ & _ & _ & _ & Hcp & [(bk & o & Ebuf & _) | (-> & Hr & _)]);
      [| unfold ddx_copied; rewrite Hr; simpl; auto].
    subst buf. cbv beta iota. set (buf := Vptr bk o).
    intros H0.
    assert (Ed: fs_dictEnd (continuity (fs_after_begin (DA_ddict x buf sh) fs1 cold dm f) d n) = ddx_end x buf)
      by (unfold continuity; destruct (cont_moves _ d n); reflexivity).
    cbn [fs_after_begin] in Ed. rewrite Ed. rewrite (ddx_end_ptr x buf) by exact I. rewrite H0.
    assert (Hbp: isptr buf) by exact I.
    rewrite isptr_offset_val_zero by auto.
    rewrite pws_pred_app, pws_pred_one.
    eapply derives_trans; [| apply (extend_weak_valid_pointer buf (pw_pred w))].
    apply sepcon_derives; [| apply derives_refl].
    destruct (ddx_copied x) eqn:Ec; [specialize (Hcp eq_refl); rewrite H0 in Hcp; lia |].
    destruct (Hok Ec ltac:(unfold buf; discriminate)) as [_ Hd]. rewrite H0 in Hd.
    destruct Hd as [[(_ & _ & Hb) | (_ & Hv & _)] | (_ & _ & Hv)].
    + unfold buf_ok in Hb. eapply derives_trans; [| apply andp_left1, derives_refl].
      eapply derives_trans; [| exact Hb]. rewrite <- (sepcon_emp (pws_pred W)) at 1.
      apply sepcon_derives; [apply derives_refl |]. unfold data_at_. apply data_at_zero_array; auto.
    + eapply derives_trans; [exact Hv | apply valid_pointer_weak].
    + eapply derives_trans; [exact Hv | apply valid_pointer_weak].
Qed.


(* ---------- the dictionary as the prefix of dst's output ([dict | dst], gap0) ---------- *)

(* the output array and the extDict ZSTD_decompressFrame gets at dst + u: the rest of dst and the dictionary
   argument's extDict; or, when ZSTD_checkContinuity keeps the dictionary as dst's prefix (gap0), the dictionary's
   bytes and dst as ONE array (same share, dict_ptr_ok_any) written after the dictionary, with no extDict *)
Definition mf_oa (a: darg) (shd: share) (cap: Z) (oc: list val) (dst: val) (u: Z) : outarr :=
  if gap0 a dst cap u then
    match a with
    | DA_dict _ pk b => Build_outarr shd pk (Zlength b + cap) (zbytes b ++ sublist u cap oc) (Zlength b) cap
    | _ => Build_outarr shd (offset_val u dst) (cap - u) (sublist u cap oc) 0 (cap - u)
    end
  else Build_outarr shd (offset_val u dst) (cap - u) (sublist u cap oc) 0 (cap - u).

Definition mf_e (a: darg) (dm: dict_model) (dst: val) (cap u: Z) : ext_seg :=
  if gap0 a dst cap u then ExtNone else ext_of a dm.

(* dst's part of the frame's output array oc' *)
Definition mf_back (a: darg) (dst: val) (cap u: Z) (oc': list val) : list val :=
  if gap0 a dst cap u then
    match a with DA_dict _ _ b => sublist (Zlength b) (Zlength oc') oc' | _ => oc' end
  else oc'.

Lemma gap0_no_move: forall a fs1 cold dm f dst cap u, isptr dst -> gap0 a dst cap u = true ->
  continuity (fs_after_begin a fs1 cold dm f) (offset_val u dst) (cap - u) = fs_after_begin a fs1 cold dm f.
Proof.
  intros a fs1 cold dm f dst cap u Hd G.
  destruct (gap0_elim _ _ _ _ G) as (sh & pk & b & -> & Hb & -> & Hc & E).
  unfold continuity, cont_moves, fs_after_begin.
  rewrite (proj2 (Z.eqb_neq (Zlength b) 0)) by lia. cbn [fs_with_dict fs_gpDictCopy fs_previousDstEnd].
  rewrite isptr_offset_val_zero by auto. subst dst.
  unfold veqb. destruct (Val.eq (Vint (Int.repr 0)) (Vint (Int.repr 0))); [| congruence].
  destruct (Val.eq _ _); [| congruence]. rewrite andb_false_r. reflexivity.
Qed.

(* with gap0, the dictionary is the caller's bytes just before dst, of dst's share, the two together of at most
   2^63 - 1 bytes *)
Lemma gap0_facts: forall W a shd cap dst u, darg_ok3 W a shd cap dst -> darg_wf a -> gap0 a dst cap u = true ->
  exists sh pk b bk o, a = DA_dict sh pk b /\ sh = shd /\ 0 < Zlength b /\ u = 0 /\ 0 < cap /\
    Zlength b + cap <= 2 ^ 63 - 1 /\ pk = Vptr bk o /\ Ptrofs.unsigned o + Zlength b <= Ptrofs.max_unsigned /\
    offset_val (Zlength b) pk = dst.
Proof.
  intros W a shd cap dst u Hok Hwf G.
  destruct (gap0_elim _ _ _ _ G) as (sh & pk & b & -> & Hb & -> & Hc & E).
  destruct Hwf as (_ & _ & _ & _ & bk & o & -> & Ho). destruct Hok as (_ & _ & _ & Hdp).
  pose proof (Ptrofs.unsigned_range o).
  assert (Eo: Ptrofs.unsigned (Ptrofs.add o (Ptrofs.repr (Zlength b))) = Ptrofs.unsigned o + Zlength b).
  { rewrite Ptrofs.add_unsigned, (Ptrofs.unsigned_repr (Zlength b)) by rep_lia. apply Ptrofs.unsigned_repr. rep_lia. }
  subst dst. simpl in Hdp.
  destruct Hdp as [[(_ & Hpos & _) | (Hn0 & _)] | (_ & (_ & Himp) & _)].
  - rewrite Eo in Hpos. lia.
  - lia.
  - destruct (Himp Hb (eq_sym Eo)) as [Esh Hn]. exists sh, (Vptr bk o), b, bk, o. repeat split; auto.
Qed.

(* the frame's history with the dictionary in dst's array (frame_hist, its second case) or in the extDict *)
Lemma cont_layout_any: forall W shd cap oc dst a fs1 cold dm f u,
  darg_ok3 W a shd cap dst -> darg_wf a -> darg_c a dm ->
  field_compatible (tarray tuchar cap) [] dst -> 0 <= u < cap -> Zlength oc = cap ->
  frame_hist (continuity (fs_after_begin a fs1 cold dm f) (offset_val u dst) (cap - u))
    (oa_base (mf_oa a shd cap oc dst u)) (oa_N (mf_oa a shd cap oc dst u)) (oa_c (mf_oa a shd cap oc dst u))
    (oa_d (mf_oa a shd cap oc dst u)) (mf_e a dm dst cap u) (dm_content dm).
Proof.
  intros W shd cap oc dst a fs1 cold dm f u Hok Hwf Hm Hfc Hu Hoc.
  assert (Hd: isptr dst) by (destruct Hfc; auto).
  destruct (gap0 a dst cap u) eqn:G.
  - rewrite gap0_no_move by auto. unfold mf_oa, mf_e. rewrite G.
    destruct (gap0_facts W a shd cap dst u Hok Hwf G) as (sh & pk & b & bk & o & -> & <- & Hb & -> & Hc & Hn & -> & Ho & E).
    cbn [oa_base oa_N oa_c oa_d]. right.
    destruct (darg_c_suffix sh (Vptr bk o) b dm Hm ltac:(lia)) as [pre Hpre].
    assert (Hl: Zlength b = Zlength pre + Zlength (dm_content dm)) by (rewrite Hpre, Zlength_app; auto).
    pose proof (Zlength_nonneg pre). pose proof (Zlength_nonneg (dm_content dm)).
    split; [reflexivity | split; [lia | split]].
    + unfold layout_ok, fs_after_begin. rewrite (proj2 (Z.eqb_neq (Zlength b) 0)) by lia.
      cbn [fs_with_dict fs_prefixStart fs_virtualStart ext_len]. rewrite Z.sub_0_r. repeat split; auto; lia.
    + rewrite sublist_app1 by (rewrite ?Zlength_map; lia).
      rewrite Hpre, map_app, Zlength_app. rewrite sublist_app2 by (rewrite Zlength_map; lia). rewrite Zlength_map.
      apply sublist_same; rewrite ?Zlength_map; lia.
  - unfold mf_oa, mf_e. rewrite G. cbn [oa_base oa_N oa_c oa_d]. left.
    eapply cont_layout_sep; eauto.
Qed.

Lemma mf_e_not_in: forall a dm dst cap u, match mf_e a dm dst cap u with ExtIn _ _ => False | _ => True end.
Proof. intros. unfold mf_e. destruct (gap0 a dst cap u); [exact I | apply ext_of_not_in]. Qed.

Lemma hist_ptrs_mf: forall a fs1 cold dm f dst cap u, darg_wf a -> isptr dst ->
  hist_ptrs_e (continuity (fs_after_begin a fs1 cold dm f) (offset_val u dst) (cap - u)) (mf_e a dm dst cap u).
Proof.
  intros a fs1 cold dm f dst cap u Hwf Hd. unfold mf_e. destruct (gap0 a dst cap u) eqn:G.
  - rewrite gap0_no_move by auto. destruct (gap0_elim _ _ _ _ G) as (sh & pk & b & -> & Hb & -> & Hc & E).
    destruct Hwf as (_ & _ & _ & Hpk & _). unfold hist_ptrs_e, fs_after_begin.
    rewrite (proj2 (Z.eqb_neq (Zlength b) 0)) by lia. cbn [fs_with_dict fs_prefixStart fs_virtualStart fs_dictEnd fs_begin3].
    destruct pk; try contradiction. split; [exact I | split; [exact I | left; reflexivity]].
  - apply hist_ptrs_after; auto; destruct dst; try contradiction; exact I.
Qed.

Lemma ext_def_mf: forall a dm dst cap u, darg_wf a -> darg_c a dm -> ext_def (mf_e a dm dst cap u).
Proof.
  intros. unfold mf_e. destruct (gap0 a dst cap u); [intros k Hk; simpl in Hk; lia | apply ext_def_of; auto].
Qed.

Lemma ext0_mf: forall W shd cap dst a fs1 cold dm f d n w u,
  darg_ok3 W a shd cap dst -> darg_wf a ->
  ext0_ok (W ++ [w]) (continuity (fs_after_begin a fs1 cold dm f) d n) (mf_e a dm dst cap u).
Proof.
  intros. unfold mf_e. destruct (gap0 a dst cap u); [exact I | eapply ext0_after; eauto].
Qed.

(* ZSTD_decompressFrame's arguments dst + u and cap - u, in terms of mf_oa *)
Lemma mf_oa_dst: forall a shd cap oc dst u, isptr dst ->
  offset_val (oa_d (mf_oa a shd cap oc dst u)) (oa_base (mf_oa a shd cap oc dst u)) = offset_val u dst /\
  oa_cap (mf_oa a shd cap oc dst u) = cap - u.
Proof.
  intros a shd cap oc dst u Hd. unfold mf_oa. destruct (gap0 a dst cap u) eqn:G.
  2: { cbn [oa_d oa_base oa_cap]. rewrite isptr_offset_val_zero by (destruct dst; try contradiction; exact I).
       split; reflexivity. }
  destruct (gap0_elim _ _ _ _ G) as (sh & pk & b & -> & Hb & -> & Hc & E). cbn [oa_d oa_base oa_cap].
  rewrite isptr_offset_val_zero by auto. split; [auto | lia].
Qed.

Lemma mf_oa_ok: forall W a shd cap oc dst u,
  darg_ok3 W a shd cap dst -> darg_wf a -> writable_share shd -> Zlength oc = cap -> 0 <= u <= cap ->
  cap <= 2 ^ 63 - 1 -> outarr_ok (mf_oa a shd cap oc dst u).
Proof.
  intros W a shd cap oc dst u Hok Hwf Hsh Hoc Hu Hc. unfold mf_oa, outarr_ok.
  destruct (gap0 a dst cap u) eqn:G.
  - destruct (gap0_facts W a shd cap dst u Hok Hwf G) as (sh & pk & b & bk & o & -> & <- & Hb & -> & Hc0 & Hn & -> & Ho & E).
    cbn [oa_sh oa_N oa_c oa_d oa_cap]. rewrite Zlength_app, Zlength_map, Zlength_sublist by lia.
    refine (conj Hsh _). repeat split; lia.
  - cbn [oa_sh oa_N oa_c oa_d oa_cap]. rewrite Zlength_sublist by lia. refine (conj Hsh _). repeat split; lia.
Qed.

(* with no room left the output position is weakly valid (never gap0: then the room is cap > 0) *)
Lemma mf_wv: forall W shd cap oc dst a u, buf_ok W shd cap dst -> 0 <= u <= cap ->
  writable_share shd -> field_compatible (tarray tuchar cap) [] dst ->
  oa_cap (mf_oa a shd cap oc dst u) = 0 ->
  pws_pred (W ++ [pw_bytes shd u (sublist 0 u oc) dst]) |--
    weak_valid_pointer (offset_val (oa_d (mf_oa a shd cap oc dst u)) (oa_base (mf_oa a shd cap oc dst u))).
Proof.
  intros W shd cap oc dst a u Hb Hu Hsh Hfc Hz. unfold mf_oa in *. destruct (gap0 a dst cap u) eqn:G.
  - destruct (gap0_elim _ _ _ _ G) as (sh & pk & b & -> & Hb0 & -> & Hc & E). cbn [oa_cap] in Hz. lia.
  - cbn [oa_cap oa_d oa_base] in *. apply (frame_wv W shd cap oc dst u); auto; lia.
Qed.

(* the selection never lends the local DDict's entropy with the caller's bytes as the dictionary *)
Lemma mf_lent: forall pr sp dcur l tbl a dm dst cap u s lent,
  (lent = true -> lent_ok pr sp dcur l tbl (darg_ox a) s /\ lent_ext dcur (ext_of a dm)) ->
  lent = true -> lent_ok pr sp dcur l tbl (darg_ox a) s /\ lent_ext dcur (mf_e a dm dst cap u).
Proof.
  intros pr sp dcur l tbl a dm dst cap u s lent H Hl. destruct (H Hl) as [H1 H2]. split; auto.
  unfold mf_e. destruct (gap0 a dst cap u) eqn:G; auto. exfalso.
  destruct (gap0_elim _ _ _ _ G) as (sh & pk & b & -> & _). destruct H1 as (_ & (x & buf & E & _) & _).
  discriminate.
Qed.

(* the array of dst + u cells (with room) followed by n more is one array at the start *)
Lemma fc_tuchar_merge: forall n m bk o, 0 <= n -> 0 <= m ->
  field_compatible (tarray tuchar m) [] (offset_val n (Vptr bk o)) -> Ptrofs.unsigned o + n <= Ptrofs.max_unsigned ->
  field_compatible (tarray tuchar (n + m)) [] (Vptr bk o).
Proof.
  intros n m bk o Hn Hm (_ & Hc & Hs & Ha & Hl) Ho. pose proof (Ptrofs.unsigned_range o).
  unfold size_compatible in Hs. simpl offset_val in Hs.
  rewrite Ptrofs.add_unsigned, (Ptrofs.unsigned_repr n), Ptrofs.unsigned_repr in Hs by rep_lia.
  simpl sizeof in Hs. rewrite Z.max_r in Hs by lia.
  split; [exact I | split; [exact Hc | split; [| split; [| exact Hl]]]].
  - unfold size_compatible. simpl sizeof. rewrite Z.max_r by lia. lia.
  - apply align_compatible_rec_Tarray. intros.
    eapply align_compatible_rec_by_value; [reflexivity | apply Z.divide_1_l].
Qed.

(* the frame's output array and extDict from dst's rest and the dictionary argument's resources *)
Lemma mf_pre_sep: forall W shd cap (oc: list val) dst a dm u,
  darg_ok3 W a shd cap dst -> darg_wf a -> Zlength oc = cap -> field_compatible (tarray tuchar cap) [] dst ->
  0 <= u <= cap ->
  data_at shd (tarray tuchar (cap - u)) (sublist u cap oc) (offset_val u dst) * ext_res (ext_of a dm) |--
  data_at (oa_sh (mf_oa a shd cap oc dst u)) (tarray tuchar (oa_N (mf_oa a shd cap oc dst u)))
    (oa_c (mf_oa a shd cap oc dst u)) (oa_base (mf_oa a shd cap oc dst u)) * ext_res (mf_e a dm dst cap u).
Proof.
  intros W shd cap oc dst a dm u Hok Hwf Hoc Hfc Hu. unfold mf_oa, mf_e.
  destruct (gap0 a dst cap u) eqn:G; [| apply derives_refl].
  destruct (gap0_facts W a shd cap dst u Hok Hwf G) as (sh & pk & b & bk & o & -> & <- & Hb & -> & Hc0 & Hn & -> & Ho & E).
  cbn [oa_sh oa_N oa_c oa_base ext_of ext_res]. rewrite (proj2 (Z.eqb_neq (Zlength b) 0)) by lia.
  cbn [ext_res]. rewrite Z.sub_0_r, isptr_offset_val_zero by (subst dst; exact I).
  assert (Hfm: field_compatible (tarray tuchar (Zlength b + cap)) [] (Vptr bk o))
    by (apply fc_tuchar_merge; auto; try lia; rewrite E; auto).
  rewrite (split_out sh (Zlength b + cap) (zbytes b ++ sublist 0 cap oc) (Vptr bk o) (Zlength b))
    by (auto; try lia; rewrite Zlength_app, Zlength_map, Zlength_sublist by lia; lia).
  rewrite sublist0_app1 by (rewrite Zlength_map; lia).
  rewrite sublist_app2 by (rewrite Zlength_map; lia). rewrite Zlength_map, Z.sub_diag.
  replace (Zlength b + cap - Zlength b) with cap by lia.
  rewrite (sublist_same 0 (Zlength b) (zbytes b)) by (rewrite ?Zlength_map; auto).
  rewrite (sublist_same 0 cap (sublist 0 cap oc)) by (try rewrite Zlength_sublist by lia; lia).
  rewrite E. rewrite sepcon_emp. cancel.
Qed.

Lemma unchanged_prefix: forall (oc oc': list val) lo hi n, Zlength oc' = Zlength oc -> 0 <= n <= lo -> n <= Zlength oc ->
  unchanged_outside oc oc' lo hi -> sublist 0 n oc' = sublist 0 n oc.
Proof.
  intros oc oc' lo hi n Hl Hn Hn2 Hu. apply Znth_eq_ext; [rewrite !Zlength_sublist by lia; lia |].
  intros i Hi. rewrite Zlength_sublist in Hi by lia. rewrite !Znth_sublist by lia. apply Hu; lia.
Qed.

(* ... and back after the frame: dst's rest is mf_back of the output, the dictionary's bytes are unchanged *)
Lemma mf_post_sep: forall W shd cap (oc: list val) dst a dm u (oc': list val),
  darg_ok3 W a shd cap dst -> darg_wf a -> Zlength oc = cap -> field_compatible (tarray tuchar cap) [] dst ->
  0 <= u <= cap -> Zlength oc' = oa_N (mf_oa a shd cap oc dst u) ->
  unchanged_outside (oa_c (mf_oa a shd cap oc dst u)) oc' (oa_d (mf_oa a shd cap oc dst u))
    (oa_d (mf_oa a shd cap oc dst u) + oa_cap (mf_oa a shd cap oc dst u)) ->
  data_at (oa_sh (mf_oa a shd cap oc dst u)) (tarray tuchar (oa_N (mf_oa a shd cap oc dst u))) oc'
    (oa_base (mf_oa a shd cap oc dst u)) * ext_res (mf_e a dm dst cap u) |--
  data_at shd (tarray tuchar (cap - u)) (mf_back a dst cap u oc') (offset_val u dst) * ext_res (ext_of a dm).
Proof.
  intros W shd cap oc dst a dm u oc' Hok Hwf Hoc Hfc Hu Hl Hun. unfold mf_oa, mf_e, mf_back in *.
  destruct (gap0 a dst cap u) eqn:G; [| apply derives_refl].
  destruct (gap0_facts W a shd cap dst u Hok Hwf G) as (sh & pk & b & bk & o & -> & <- & Hb & -> & Hc0 & Hn & -> & Ho & E).
  cbn [oa_sh oa_N oa_c oa_base oa_d oa_cap ext_of ext_res] in *. rewrite (proj2 (Z.eqb_neq (Zlength b) 0)) by lia.
  cbn [ext_res]. rewrite Z.sub_0_r, isptr_offset_val_zero by (subst dst; exact I).
  assert (Hfm: field_compatible (tarray tuchar (Zlength b + cap)) [] (Vptr bk o))
    by (apply fc_tuchar_merge; auto; try lia; rewrite E; auto).
  rewrite (split_out sh (Zlength b + cap) oc' (Vptr bk o) (Zlength b)) by (auto; lia).
  rewrite (unchanged_prefix (zbytes b ++ sublist 0 cap oc) oc' (Zlength b) (Zlength b + cap) (Zlength b))
    by (rewrite ?Zlength_app, ?Zlength_map, ?Zlength_sublist by lia; lia || auto).
  rewrite sublist0_app1 by (rewrite Zlength_map; lia).
  rewrite (sublist_same 0 (Zlength b) (zbytes b)) by (rewrite ?Zlength_map; auto).
  replace (Zlength b + cap - Zlength b) with cap by lia. rewrite Hl. rewrite E, sepcon_emp. cancel.
Qed.

(* the frame's results on its output array oc', seen on dst's part mf_back of it *)
Lemma mf_back_facts: forall a shd cap oc dst u oc', 0 <= u <= cap -> Zlength oc = cap ->
  Zlength oc' = oa_N (mf_oa a shd cap oc dst u) ->
  Zlength (mf_back a dst cap u oc') = cap - u /\
  forall r, 0 <= r <= cap - u ->
    sublist (oa_d (mf_oa a shd cap oc dst u)) (oa_d (mf_oa a shd cap oc dst u) + r) oc' =
    sublist 0 r (mf_back a dst cap u oc').
Proof.
  intros a shd cap oc dst u oc' Hu Hoc Hl. unfold mf_oa, mf_back in *.
  destruct (gap0 a dst cap u) eqn:G; [| cbn [oa_N oa_d] in *; split; [auto | intros; reflexivity]].
  destruct (gap0_elim _ _ _ _ G) as (sh & pk & b & -> & Hb & -> & Hc & E). cbn [oa_N oa_d] in *.
  pose proof (Zlength_nonneg b).
  split; [rewrite Zlength_sublist by lia; lia |].
  intros r Hr. rewrite sublist_sublist by lia. f_equal; lia.
Qed.

Lemma frame_res3_shift: forall md dm s cap r oc' d k oc2,
  (is_error_code r = false -> sublist d (d + r) oc' = sublist 0 r oc2) ->
  frame_res3 md dm s cap r oc' d k -> frame_res3 md dm s cap r oc2 0 k.
Proof.
  unfold frame_res3. intros md dm s cap r oc' d k oc2 Hs H.
  destruct (decode_frame_m md dm no_wlim s) as [c sz | | |]; auto.
  destruct H as [H1 H2]. split; auto. intros He. destruct (H1 He) as (Hr & Hsub & Hk).
  split; [auto | split; [| auto]]. rewrite Z.add_0_l, <- (Hs He). auto.
Qed.

End CM_Multi3Pre_1.
