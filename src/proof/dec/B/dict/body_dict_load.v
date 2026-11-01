(* ZSTD_loadDEntropy *)
Require Export Zstd.proof.dec.B.dict.DictSpecs.
Local Open Scope logic.

(* ---------- memory layout of the entropy struct (offsets: LLTable 0, OFTable 4104, MLTable 6160,
   hufTable 10264, rep 26652, workspace 26664, size 27292) ---------- *)

(* the Huffman table field before (None) or after (Some ht) HUF_readDTableX2_wksp *)
Definition dl_huf (oh: option huf_table) (p: val) : mpred :=
  match oh with None => hufhdr_at Ews p | Some ht => hufdt_at Ews ht p end.

(* the three sequence tables without content are HUF_readDTableX2_wksp's workspace: 2566 U32 at
   &entropy->LLTable *)
Lemma dl_ws_split (pe: val) :
  field_compatible t_entropy nil pe ->
  seqspace_at Ews KLL None (ent_seq KLL pe) * seqspace_at Ews KOF None (ent_seq KOF pe) *
  seqspace_at Ews KML None (ent_seq KML pe) = data_at_ Ews (tarray tuint 2566) pe.
Proof.
  intros H.
  assert (FL := field_compatible_app nil t_entropy (DOT _LLTable) pe ltac:(simpl; auto with field_compatible)).
  assert (FO := field_compatible_app nil t_entropy (DOT _OFTable) pe ltac:(simpl; auto with field_compatible)).
  assert (FM := field_compatible_app nil t_entropy (DOT _MLTable) pe ltac:(simpl; auto with field_compatible)).
  assert (FH := field_compatible_app nil t_entropy (DOT _hufTable) pe ltac:(simpl; auto with field_compatible)).
  rewrite field_compatible_field_address in FL, FO, FM, FH by auto with field_compatible.
  simpl in FL, FO, FM, FH.
  unfold seqspace_at, ent_seq, sk_size, sk_maxlog, sk_tfield.
  rewrite !field_compatible_field_address by auto with field_compatible.
  simpl.
  rewrite !data_at__memory_block. unfold t_seqSymbol.
  rewrite !prop_true_andp by assumption.
  destruct pe as [| | | | | b i]; try contradiction (proj1 H).
  pose proof (proj1 (proj2 (proj2 H))) as SZ. unfold size_compatible in SZ. simpl in SZ.
  pose proof (Ptrofs.unsigned_range i) as RI.
  assert (U: forall n, 0 <= n <= 27292 ->
             Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr n)) = Ptrofs.unsigned i + n).
  { intros n Hn. rewrite Ptrofs.add_unsigned. rewrite (Ptrofs.unsigned_repr n) by rep_lia.
    apply Ptrofs.unsigned_repr. rep_lia. }
  assert (A4: (4 | Ptrofs.unsigned i)).
  { destruct FH as [_ [_ [_ [AH _]]]].
    cbv beta iota delta [align_compatible offset_val] in AH.
    apply align_compatible_rec_Tarray_inv with (i := 0) in AH; [|lia].
    rewrite U in AH by lia.
    apply align_compatible_rec_by_value_inv with (ch := Mint32) in AH; [|reflexivity].
    change (align_chunk Mint32) with 4 in AH.
    replace (Ptrofs.unsigned i) with (Ptrofs.unsigned i + 10264 + sizeof tuint * 0 - 4 * 2566) by (simpl; lia).
    apply Z.divide_sub_r; [assumption | exists 2566; lia]. }
  assert (FC: field_compatible (tarray tuint 2566) [] (Vptr b i)).
  { split3; [exact I | reflexivity | split3].
    - unfold size_compatible. change (sizeof (tarray tuint 2566)) with 10264. lia.
    - unfold align_compatible. apply align_compatible_rec_Tarray. intros j Hj.
      eapply align_compatible_rec_by_value; [reflexivity|]. change (align_chunk Mint32) with 4.
      apply Z.divide_add_r; [assumption|]. exists j. simpl. lia.
    - simpl; auto. }
  rewrite prop_true_andp by exact FC.
  change (sizeof (tarray (Tstruct ___gp_ZSTD_seqSymbol noattr) 513)) with 4104.
  change (sizeof (tarray (Tstruct ___gp_ZSTD_seqSymbol noattr) 257)) with 2056.
  change (sizeof (tarray tuint 2566)) with (4104 + 2056 + 4104).
  rewrite <- (Ptrofs.repr_unsigned i). unfold offset_val. rewrite !ptrofs_add_repr.
  rewrite !memory_block_split by rep_lia.
  rewrite Z.add_0_r. reflexivity.
Qed.

(* dl_release: every piece is a memory block, then the blocks join *)
Lemma dlr_split (sh: share) (b: block) (o n m: Z) :
  0 <= o -> 0 <= n -> 0 <= m -> o + n + m < Ptrofs.modulus ->
  memory_block sh (n + m) (Vptr b (Ptrofs.repr o)) =
  memory_block sh n (Vptr b (Ptrofs.repr o)) * memory_block sh m (Vptr b (Ptrofs.repr (o + n))).
Proof. intros. apply memory_block_split; lia. Qed.

Lemma dlr_off (b: block) (o k: Z) : offset_val k (Vptr b (Ptrofs.repr o)) = Vptr b (Ptrofs.repr (o + k)).
Proof. simpl. rewrite ptrofs_add_repr. reflexivity. Qed.

Lemma dlr_seq (k: seqkind) (ot: option fse_table) (b: block) (o: Z) :
  0 <= o -> o + 8 * sk_size k < Ptrofs.modulus ->
  seqspace_at Ews k ot (Vptr b (Ptrofs.repr o)) |-- memory_block Ews (8 * sk_size k) (Vptr b (Ptrofs.repr o)).
Proof.
  intros Ho Hm.
  assert (Hmx: 0 <= sk_maxlog k) by (destruct k; simpl; unfold LLFSELog, OffFSELog, MLFSELog; lia).
  destruct ot as [t|]; simpl seqspace_at.
  - unfold seqtab_at, seqtab_at_fm. Intros fm.
    match goal with H: fse_ok _ _ |- _ => destruct H as [Hl _] end.
    assert (H2: 0 < 2 ^ ft_log t <= 2 ^ sk_maxlog k)
      by (split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]).
    unfold sk_size in *.
    rewrite !dlr_off, ?ptrofs_add_repr.
    sep_apply (data_at_memory_block Ews t_seqhdr). sep_apply data_at_memory_block.
    rewrite data_at__memory_block. Intros.
    simpl sizeof. rewrite Z.max_r by lia.
    replace (8 * (1 + 2 ^ sk_maxlog k))%Z with (8 + (8 * 2 ^ ft_log t + 8 * (1 + 2 ^ sk_maxlog k - 1 - 2 ^ ft_log t)))%Z by lia.
    rewrite dlr_split by lia. rewrite dlr_split by lia.
    replace (o + 8 + 8 * 2 ^ ft_log t)%Z with (o + 8 * (1 + 2 ^ ft_log t))%Z by lia.
    rewrite Z.max_r by lia. cancel.
  - rewrite data_at__memory_block. Intros. simpl sizeof. rewrite Z.max_r. cancel.
    unfold sk_size. pose proof (Z.pow_nonneg 2 (sk_maxlog k)). lia.
Qed.

Lemma dlr_huf (oh: option huf_table) (b: block) (o: Z) :
  0 <= o -> o + 16388 < Ptrofs.modulus ->
  dl_huf oh (Vptr b (Ptrofs.repr o)) |-- memory_block Ews 16388 (Vptr b (Ptrofs.repr o)).
Proof.
  intros Ho Hm. unfold HUF_CELLBYTES.
  replace 16388 with (4 + 16384)%Z by reflexivity.
  destruct oh as [ht|]; simpl dl_huf.
  - unfold hufdt_at, hufdt_x_at. Intros x2 L res.
    match goal with H: huf_ok _ |- _ => destruct H as [Hl _] end.
    unfold HUF_TABLELOG_MAX in *.
    assert (Hp2: 0 < 2 ^ L <= 2 ^ 12) by (split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]).
    change (2 ^ 12)%Z with 4096%Z in Hp2.
    sep_apply (data_at_memory_block Ews t_dtdesc).
    rewrite (dlr_split Ews b o 4 16384) by lia.
    destruct x2.
    + Intros c2. sep_apply data_at_memory_block. rewrite !dlr_off.
      simpl sizeof. rewrite Z.max_r by lia. unfold HUF_CELLBYTES.
      replace 16384 with (4 * 2 ^ L + (16384 - 4 * 2 ^ L))%Z by lia.
      rewrite (dlr_split Ews b (o + 4) (4 * 2 ^ L)) by lia.
      replace (o + 4 + 4 * 2 ^ L)%Z with (o + (4 + 4 * 2 ^ L))%Z by lia.
      cancel; apply derives_refl'; f_equal; lia.
    + sep_apply data_at_memory_block. rewrite !dlr_off.
      simpl sizeof. rewrite Z.max_r by lia. unfold HUF_CELLBYTES.
      replace 16384 with (2 * 2 ^ L + (16384 - 2 * 2 ^ L))%Z by lia.
      rewrite (dlr_split Ews b (o + 4) (2 * 2 ^ L)) by lia.
      replace (o + 4 + 2 * 2 ^ L)%Z with (o + (4 + 2 * 2 ^ L))%Z by lia.
      cancel; apply derives_refl'; f_equal; lia.
  - unfold hufhdr_at. Intros ty lg res.
    sep_apply (data_at_memory_block Ews t_dtdesc).
    rewrite (dlr_split Ews b o 4 16384) by lia. rewrite dlr_off. simpl sizeof.
    unfold HUF_CELLBYTES. cancel.
Qed.

(* any stage of ZSTD_loadDEntropy: the struct's whole memory (the error returns) *)
Lemma dl_release (pe: val) (oh: option huf_table) (oLL oOF oML: option fse_table) :
  field_compatible t_entropy nil pe ->
  dl_huf oh (ent_huf pe) *
  seqspace_at Ews KLL oLL (ent_seq KLL pe) * seqspace_at Ews KOF oOF (ent_seq KOF pe) *
  seqspace_at Ews KML oML (ent_seq KML pe) *
  field_at_ Ews t_entropy (DOT _rep) pe * field_at_ Ews t_entropy (DOT _workspace) pe
  |-- data_at_ Ews t_entropy pe.
Proof.
  intros Hpe. pose proof Hpe as Hfc.
  destruct pe as [| | | | | b i]; try (destruct Hfc; contradiction).
  assert (Hsz: Ptrofs.unsigned i + 27292 < Ptrofs.modulus)
    by (destruct Hfc as (_ & _ & Hs & _); simpl in Hs; exact Hs).
  pose proof (Ptrofs.unsigned_range i) as Hi.
  set (o := Ptrofs.unsigned i) in *.
  unfold ent_huf, ent_seq; simpl sk_tfield. unfold field_at_. rewrite !field_at_data_at.
  rewrite !field_address_offset by auto with field_compatible.
  simpl nested_field_offset. simpl nested_field_type.
  rewrite <- (Ptrofs.repr_unsigned i). fold o. rewrite !dlr_off.
  sep_apply (data_at_memory_block Ews (tarray tuint 157)).
  sep_apply (data_at_memory_block Ews (tarray tuint 3)).
  simpl sizeof.
  sep_apply (dlr_huf oh b (o + 10264)); [lia | lia |].
  sep_apply (dlr_seq KLL oLL b (o + 0)); [lia | simpl; lia |].
  sep_apply (dlr_seq KOF oOF b (o + 4104)); [lia | simpl; lia |].
  sep_apply (dlr_seq KML oML b (o + 6160)); [lia | simpl; lia |].
  rewrite <- memory_block_data_at_ by (rewrite <- (Ptrofs.repr_unsigned i) in Hpe; exact Hpe).
  simpl sizeof.
  change (8 * sk_size KLL)%Z with 4104%Z. change (8 * sk_size KOF)%Z with 2056%Z.
  change (8 * sk_size KML)%Z with 4104%Z. rewrite Z.add_0_r.
  change 27292%Z with (4104 + (2056 + (4104 + (16388 + (12 + 628)))))%Z.
  rewrite (dlr_split Ews b o) by lia.
  rewrite (dlr_split Ews b (o + 4104)) by lia.
  rewrite (dlr_split Ews b (o + 4104 + 2056)) by lia.
  rewrite (dlr_split Ews b (o + 4104 + 2056 + 4104)) by lia.
  rewrite (dlr_split Ews b (o + 4104 + 2056 + 4104 + 16388)) by lia.
  replace (o + 4104 + 2056)%Z with (o + 6160)%Z by lia.
  replace (o + 6160 + 4104)%Z with (o + 10264)%Z by lia.
  replace (o + 10264 + 16388)%Z with (o + 26652)%Z by lia.
  replace (o + 26652 + 12)%Z with (o + 26664)%Z by lia.
  cancel.
Qed.

(* zstd's do { ... } while (0) around a statement without effect (the RETURN_ERROR_IF debug parts) *)
(* the suffix of the dictionary from p is a window of it *)
Lemma dl_win (sh: share) (b: list Z) (p: Z) :
  readable_share sh -> bytes_ok b -> Zlength b <= 2 ^ 63 - 1 -> 0 <= p <= Zlength b ->
  win_ok sh (Zlength b) (zbytes b) p (Zlength b - p) (skipn (Z.to_nat p) b).
Proof.
  intros Hsh Hb Hn Hp. unfold win_ok.
  assert (Hs: skipn (Z.to_nat p) b = sublist p (Zlength b) b).
  { rewrite sublist_skip by lia. reflexivity. }
  rewrite Hs, Zlength_map, Zlength_sublist by lia.
  refine (conj Hsh (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))); try lia.
  all: try (rewrite ?Zlength_map; lia).
  - unfold bytes_ok in *. apply Forall_sublist; auto.
  - rewrite sublist_map. do 2 f_equal. lia.
Qed.

Lemma dl_ws_to (pe: val) :
  field_compatible t_entropy nil pe ->
  seqspace_at Ews KLL None (ent_seq KLL pe) * seqspace_at Ews KOF None (ent_seq KOF pe) *
  seqspace_at Ews KML None (ent_seq KML pe) |-- data_at_ Ews (tarray tuint 2566) pe.
Proof. intros H; rewrite dl_ws_split by auto; auto. Qed.

Lemma dl_ws_from (pe: val) :
  field_compatible t_entropy nil pe ->
  data_at_ Ews (tarray tuint 2566) pe |--
  seqspace_at Ews KLL None (ent_seq KLL pe) * seqspace_at Ews KOF None (ent_seq KOF pe) *
  seqspace_at Ews KML None (ent_seq KML pe).
Proof. intros H; rewrite dl_ws_split by auto; auto. Qed.

(* dictEnd - dictPtr *)
Lemma dl_sub_pp (bk: block) (i: ptrofs) (n m: Z) :
  0 <= m <= n -> n <= Ptrofs.max_unsigned ->
  force_val (sem_sub_pp tuchar (Vptr bk (Ptrofs.add i (Ptrofs.repr n))) (Vptr bk (Ptrofs.add i (Ptrofs.repr m))))
  = Vlong (Int64.repr (n - m)).
Proof.
  intros Hm Hn. unfold sem_sub_pp. simpl. destruct (eq_block bk bk); [| congruence]. simpl.
  rewrite !(Ptrofs.add_commut i), Ptrofs.sub_shifted.
  unfold Ptrofs.divs. rewrite (Ptrofs.signed_repr 1) by rep_lia. rewrite Z.quot_1_r, Ptrofs.repr_signed.
  unfold Ptrofs.sub. rewrite !Ptrofs.unsigned_repr by rep_lia.
  unfold Vptrofs. simpl. unfold Ptrofs.to_int64. rewrite Ptrofs.unsigned_repr by rep_lia. reflexivity.
Qed.

(* the error return (size_t)-ZSTD_error_dictionary_corrupted *)
Lemma dl_err30 : 0 <= err_code 30 <= Int64.max_unsigned /\
  Vlong (Int64.repr (- (30))) = Vlong (Int64.repr (err_code 30)).
Proof.
  split; [unfold err_code; rep_lia |].
  f_equal. apply Int64.eqm_samerepr. exists (-1). reflexivity.
Qed.

Ltac dl_body :=
  solve [ forward; entailer!
        | match goal with |- semax _ ?Q _ _ => forward_if Q end;
          [ contradiction | forward; entailer! | forward; entailer! ]
        | match goal with |- semax _ ?Q _ _ => forward_if Q end;
          [ contradiction | forward; entailer! ] ].

Ltac dl_skiploop :=
  repeat match goal with |- semax _ _ (Ssequence (Ssequence _ _) _) _ => apply -> seq_assoc end;
  match goal with |- semax _ ?P (Ssequence (Sloop _ Sbreak) _) _ =>
    forward_loop P break: P; [ entailer! | dl_body | ] end.

(* the else branch of if (ERR_isError(x)) *)
Ltac dl_noerr :=
  match goal with H: Int.repr (if ?e then 1 else 0) = Int.zero |- ?e = false =>
    destruct e; [apply (f_equal Int.unsigned) in H; vm_compute in H; discriminate | reflexivity] end.

(* RETURN_ERROR_IF(cond, ...): the loop around it; after it, C holds *)
Ltac dl_check C :=
  repeat match goal with |- semax _ _ (Ssequence (Ssequence _ _) _) _ => apply -> seq_assoc end;
  match goal with |- semax _ (PROPx ?Ps (LOCALx ?Qs (SEPx ?Rs))) (Ssequence (Sloop _ Sbreak) _) _ =>
    forward_loop (PROPx Ps (LOCALx Qs (SEPx Rs)))
      break: (PROPx (C :: Ps) (LOCALx Qs (SEPx Rs))) end.

(* a size bound of the Huffman description *)
Lemma dl_huf_size (s: list Z) (ht: huf_table) (hs: Z) :
  huf_parse_desc s = Some (ht, hs) -> hs <= Zlength s.
Proof.
  unfold huf_parse_desc, huf_desc_weights. intros H.
  destruct (Zlength s <? 1); [discriminate |].
  destruct (byte_at s 0 >=? 128).
  - destruct (Zlength s <? (byte_at s 0 - 127 + 1) / 2 + 1) eqn:E; [discriminate |].
    apply Z.ltb_ge in E. set (q := (byte_at s 0 - 127 + 1) / 2) in *. clearbody q. revert H.
    repeat match goal with |- context [if ?c then _ else _] => destruct c end;
      intros H; try discriminate; inversion H; lia.
  - destruct (Zlength s <? byte_at s 0 + 1) eqn:E; [discriminate |].
    apply Z.ltb_ge in E. destruct (huf_fse_weights _); [| discriminate]. revert H.
    repeat match goal with |- context [if ?c then _ else _] => destruct c end;
      intros H; try discriminate; inversion H; lia.
Qed.

(* a size bound of a normalized-count description *)
Lemma dl_nc_size (s: list Z) (m: Z) (norm: list Z) (log sz: Z) :
  read_ncount s m = Some (norm, log, sz) -> sz <= Zlength s.
Proof.
  intros H. unfold read_ncount in H. cbv zeta in H.
  destruct (Zlength s =? 0); [discriminate |].
  destruct (fbits s 0 4 + FSE_MIN_TABLELOG >? FSE_TABLELOG_ABSOLUTE_MAX); [discriminate |].
  destruct (ncount_loop _ _ _ _ _ _ _ _ _) as [[[n0 r0] p0] |]; [| discriminate].
  destruct (negb (r0 =? 1)); [discriminate |].
  destruct (Zlength n0 >? m + 1); [discriminate |].
  set (q := (p0 + 7) / 8) in *. clearbody q.
  destruct (q >? Zlength s) eqn:E; [discriminate |].
  inversion H; subst. rewrite Z.gtb_ltb, Z.ltb_ge in E. lia.
Qed.

(* dictPtr + n *)
Lemma dl_add_ptr (d: val) (n: Z) :
  isptr d -> 0 <= n <= Int64.max_unsigned ->
  force_val (sem_binary_operation' Oadd (tptr tuchar) tulong d (Vlong (Int64.repr n))) = offset_val n d.
Proof.
  intros Hd Hn. destruct d; try contradiction. simpl. f_equal. f_equal.
  rewrite Ptrofs.mul_commut, Ptrofs.mul_one. unfold Ptrofs.of_int64.
  rewrite Int64.unsigned_repr by rep_lia. reflexivity.
Qed.

(* the side goals of a call reading the window (dictPtr, dictEnd - dictPtr) of the dictionary at d *)
Ltac dl_sameblock d :=
  entailer!; destruct d; try contradiction; simpl; unfold sameblock; simpl;
  destruct peq; auto; congruence.
Ltac dl_params d Hl :=
  entailer!; destruct d; try contradiction; rewrite Hl; simpl;
  rewrite dl_sub_pp by rep_lia; reflexivity.

(* if (maxValue > Max) with maxValue = Zlength norm - 1 <= Max: impossible *)
Ltac dl_nomax :=
  exfalso;
  match goal with H: _ < Int.unsigned (Int.repr _) |- _ =>
    rewrite Int.unsigned_repr in H by (unfold MaxOff, MaxML, MaxLL in *; rep_lia) end;
  unfold MaxOff, MaxML, MaxLL in *; lia.

Lemma dl_gtb_false (x y: Z) : x <= y -> (x >? y) = false.
Proof. intros; rewrite Z.gtb_ltb; apply Z.ltb_ge; lia. Qed.

Lemma dl_ws_fold (pe: val) :
  data_at_ Ews (tarray tuint 157) (field_address t_entropy (DOT _workspace) pe) |--
  field_at_ Ews t_entropy (DOT _workspace) pe.
Proof. rewrite field_at__data_at_. apply derives_refl. Qed.

(* the condition dictEnd - dictPtr < 12 *)
Ltac dl_cond12 d :=
  match goal with H: ?tf tint _ |- _ =>
    lazymatch tf with typed_true => idtac | typed_false => idtac end;
    revert H; destruct d as [| | | | | ? ?]; try contradiction;
    intro H; simpl offset_val in H; rewrite dl_sub_pp in H by rep_lia; simpl in H;
    unfold Int64.lt in H; rewrite !Int64.signed_repr in H by rep_lia;
    rewrite Int.signed_repr in H by rep_lia;
    destruct (zlt _ 12); try lia; unfold typed_true, typed_false in H; simpl in H; discriminate end.

(* ---------- the repeat offsets ---------- *)

Definition dl_rv (b: list Z) (p j: Z) : val := Vint (Int.repr (le_field b (p + 4 * j) 4)).
Definition dl_repv (b: list Z) (p i: Z) : list val :=
  sublist 0 i [dl_rv b p 0; dl_rv b p 1; dl_rv b p 2] ++ Zrepeat Vundef (3 - i).

Lemma dl_rep_init (b: list Z) (p: Z) (pe: val) :
  field_at_ Ews t_entropy (DOT _rep) pe |-- field_at Ews t_entropy (DOT _rep) (dl_repv b p 0) pe.
Proof. unfold field_at_. apply derives_refl. Qed.

Lemma dl_repv_upd (b: list Z) (p i: Z) :
  0 <= i < 3 -> upd_Znth i (dl_repv b p i) (dl_rv b p i) = dl_repv b p (i + 1).
Proof.
  intros Hi. assert (i = 0 \/ i = 1 \/ i = 2) as [-> | [-> | ->]] by lia; reflexivity.
Qed.

Lemma dl_repv_3 (b: list Z) (p: Z) :
  dl_repv b p 3 = rep_vals (le_field b p 4, le_field b (p + 4) 4, le_field b (p + 8) 4).
Proof. unfold dl_repv, dl_rv, rep_vals. simpl. rewrite Z.add_0_r. reflexivity. Qed.

Lemma dl_le_value (l: list Z) : Forall is_byte l -> 0 <= le_value l < 256 ^ Zlength l.
Proof.
  induction l as [| x l IH]; intros Hl.
  - rewrite Zlength_nil. simpl. lia.
  - inversion Hl; subst. specialize (IH H2). unfold is_byte in H1.
    rewrite Zlength_cons, Z.pow_succ_r by (apply Zlength_nonneg). simpl. nia.
Qed.

Lemma dl_le4 (b: list Z) (i: Z) : bytes_ok b -> 0 <= le_field b i 4 < 2 ^ 32.
Proof.
  intros Hb. unfold le_field, slice.
  assert (Hf: Forall is_byte (firstn (Z.to_nat 4) (skipn (Z.to_nat i) b))).
  { apply Forall_forall. intros x Hx. apply firstn_In in Hx.
    eapply Forall_forall; [apply Forall_skipn, Hb | exact Hx]. }
  pose proof (dl_le_value _ Hf) as Hv.
  assert (Hl: Zlength (firstn (Z.to_nat 4) (skipn (Z.to_nat i) b)) <= 4).
  { rewrite Zlength_correct, firstn_length. lia. }
  assert (256 ^ Zlength (firstn (Z.to_nat 4) (skipn (Z.to_nat i) b)) <= 2 ^ 32).
  { change (2 ^ 32) with (256 ^ 4). apply Z.pow_le_mono_r; [lia | lia]. }
  lia.
Qed.

Lemma dl_hufdt_ok (sh: share) (ht: huf_table) (p: val) : hufdt_at sh ht p |-- !! huf_ok ht.
Proof. unfold hufdt_at, hufdt_x_at. Intros x2 L res. entailer!. Qed.

Lemma dl_seq_ok (sh: share) (k: seqkind) (t: fse_table) (p: val) :
  seqspace_at sh k (Some t) p |-- !! fse_ok k t.
Proof. unfold seqspace_at, seqtab_at, seqtab_at_fm. Intros fm. entailer!. Qed.

Lemma dl_sub_pp0 (bk: block) (i: ptrofs) (n: Z) :
  0 <= n <= Ptrofs.max_unsigned ->
  force_val (sem_sub_pp tuchar (Vptr bk (Ptrofs.add i (Ptrofs.repr n))) (Vptr bk i)) = Vlong (Int64.repr n).
Proof.
  intros Hn. rewrite <- (Ptrofs.add_zero i) at 2. rewrite <- (Z.sub_0_r n) at 2.
  apply dl_sub_pp; lia.
Qed.

Lemma dl_add_int (d: val) (n: Z) :
  isptr d -> 0 <= n <= Int.max_signed ->
  force_val (sem_binary_operation' Oadd (tptr tuchar) tint d (Vint (Int.repr n))) = offset_val n d.
Proof.
  intros Hd Hn. destruct d; try contradiction. simpl. f_equal. f_equal.
  rewrite Ptrofs.mul_commut, Ptrofs.mul_one. unfold Ptrofs.of_ints.
  rewrite Int.signed_repr by rep_lia. reflexivity.
Qed.

Lemma dl_x2_at (sh: share) (ht: huf_table) (p: val) : hufdt_x_at true sh ht p |-- hufdt_at sh ht p.
Proof. unfold hufdt_at. Exists true. apply derives_refl. Qed.

(* ld_rel b ores: follow Series.load_dentropy along zstd's results (each callee's result is the model's
   when the model reads the description) *)
Ltac dl_res_step t :=
  match goal with R: forall x, t = Some x -> @?P x |- _ =>
    let E := fresh "Em" in let y := fresh "y" in
    destruct t as [y |] eqn:E;
    [ first [ specialize (R y eq_refl) | specialize (R y E) ];
      first [ discriminate R | injection R as R; subst y ]
    | let Hn := fresh in intros Hn; discriminate Hn ]
  end.

Ltac dl_ld :=
  unfold ld_rel; let x := fresh "x" in intros x;
  unfold load_dentropy; cbv zeta;
  repeat (cbv beta iota;
    match goal with
    | |- context [huf_parse_desc ?s] => dl_res_step (huf_parse_desc s)
    | |- context [read_ncount ?s ?m] => dl_res_step (read_ncount s m)
    | |- context [if ?c then None else _] =>
        let Ec := fresh "Ec" in destruct c eqn:Ec; [let Hn := fresh in intros Hn; discriminate Hn |]
    end).

Ltac dl_bools :=
  repeat match goal with
  | E: (_ >? _) = false |- _ => rewrite Z.gtb_ltb, Z.ltb_ge in E
  | E: (_ <=? _) = false |- _ => rewrite Z.leb_gt in E
  end.

(* the PROP of an error return: (size_t)-30 and ld_rel b None *)
Ltac dl_efin :=
  let E1 := fresh "E" in let E2 := fresh "E" in
  destruct dl_err30 as [E1 E2]; split; [exact E1 | split; [| exact E2]];
  dl_ld; try (intros ?; exfalso; dl_bools;
              first [congruence | unfold OffFSELog, MLFSELog, LLFSELog in *; lia]).

Lemma body_dict_load : body_ok DICT_G ZSTD_loadDEntropy_spec.
Proof.
  exists f_ZSTD_loadDEntropy; split; [reflexivity | split; [reflexivity | ]].
  start_function.
  assert (Hb64: 0 <= Zlength b <= Int64.max_unsigned) by (pose proof (Zlength_nonneg b); rep_lia).
  assert_PROP (isptr d) as Hd by entailer!.
  assert_PROP (field_compatible t_entropy nil pe) as Hpe.
  { unfold field_at_; entailer!.
    match goal with H: field_compatible t_entropy (DOT _rep) pe |- _ =>
      destruct H as (? & ? & ? & ? & ? & ?); repeat split; auto end. }
  forward. forward.
  match goal with |- semax _ (PROPx ?Ps (LOCALx ?Qs (SEPx ?Rs))) _ _ =>
    forward_loop (PROPx Ps (LOCALx Qs (SEPx Rs)))
      break: (PROPx ((8 < Zlength b) :: Ps) (LOCALx Qs (SEPx Rs))) end.
  - entailer!.
  - forward_if.
    + repeat dl_skiploop.
      assert (Hn: load_dentropy b = None).
      { match goal with H: Int64.unsigned _ >= Int64.unsigned _ |- _ =>
          rewrite !Int64.unsigned_repr in H by rep_lia end.
        unfold load_dentropy. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
      forward. Exists (err_code 30) (@None (dstate * Z)). unfold ent_blank.
      sep_apply (dl_release pe None None None None Hpe). entailer!. apply dl_err30.
    + forward. entailer!.
      match goal with H: Int64.unsigned _ < Int64.unsigned _ |- _ =>
        rewrite !Int64.unsigned_repr in H by rep_lia end; lia.
  - Intros. forward. forward. forward.
    assert (Hp8: force_val (sem_binary_operation' Oadd (tptr tuchar) tint d (Vint (Int.repr 8))) = offset_val 8 d)
      by (destruct d; try contradiction; reflexivity).
    rewrite Hp8.
    unfold ent_blank. sep_apply (dl_ws_to pe Hpe).
    assert (Hs8: skipn 8 b = skipn (Z.to_nat 8) b) by reflexivity.
    assert (Hl8: Zlength (skipn 8 b) = Zlength b - 8)
      by (rewrite Hs8, <- sublist_skip, Zlength_sublist by lia; lia).
    forward_call (gv, Ews, ent_huf pe, sh, d, Zlength b, zbytes b, 8, skipn 8 b, Ews, pe, 2566).
    { entailer!. destruct d; try contradiction. simpl. unfold sameblock. simpl.
      destruct (peq b0 b0); auto; congruence. }
    { entailer!. destruct d; try contradiction.
      rewrite Hl8. unfold ent_huf. simpl.
      rewrite field_address_offset by auto with field_compatible. simpl.
      rewrite dl_sub_pp by rep_lia. reflexivity. }
    { rewrite Hl8, Hs8. apply dl_win; auto; lia. }
    Intros rr. destruct rr as [r hres]. cbn [fst snd] in *.
    destruct hres as [[ht hs] |].
    2: {
         dl_check (is_error_code r = false).
         - entailer!.
         - forward_call r. forward_if.
           + repeat dl_skiploop. forward. Exists (err_code 30) (@None (dstate * Z)).
             sep_apply (dl_ws_from pe Hpe). sep_apply (dl_release pe None None None None Hpe).
             entailer!. dl_efin.
           + forward. entailer!. dl_noerr.
         - Intros. exfalso; congruence. }
    match goal with H: r = hs /\ _ |- _ => destruct H as [? Hhs] end. rewrite Hl8 in Hhs. subst r.
    sep_apply (dl_x2_at Ews ht (ent_huf pe)).
    assert (Hhe: is_error_code hs = false) by (unfold is_error_code; apply Z.ltb_ge; lia).
    dl_check (is_error_code hs = false).
    { entailer!. }
    { forward_call hs. rewrite Hhe. forward_if.
      - contradiction.
      - forward. entailer!. }
    Intros. forward.
    rewrite (dl_add_ptr d (Zlength b)) by (auto; rep_lia).
    rewrite (dl_add_ptr (offset_val 8 d) hs) by (auto; rep_lia).
    rewrite offset_offset_val.
    sep_apply (dl_ws_from pe Hpe). Intros.
    (* ---------- OF ---------- *)
    assert (Hp1: 0 <= 8 + hs <= Zlength b) by lia.
    assert (Hl1: Zlength (skipn (Z.to_nat (8 + hs)) b) = Zlength b - (8 + hs))
      by (rewrite <- sublist_skip, Zlength_sublist by lia; lia).
    forward.
    forward_call (gv, Tsh, v_offcodeNCount, 32, Tsh, v_offcodeMaxValue, Tsh, v_offcodeLog, MaxOff,
                  sh, d, Zlength b, zbytes b, 8 + hs, skipn (Z.to_nat (8 + hs)) b).
    { dl_sameblock d. }
    { dl_params d Hl1. }
    { rewrite Hl1. apply dl_win; auto; lia. }
    Intros rnc. destruct rnc as [[r ncOF] resOF]. cbn [fst snd] in *.
    destruct resOF as [[[nOF lOF] sOF] |].
    2: { dl_check (is_error_code r = false).
         - entailer!.
         - forward_call r. forward_if.
           + repeat dl_skiploop. forward. Exists (err_code 30) (@None (dstate * Z)).
             change (hufdt_at Ews ht (ent_huf pe)) with (dl_huf (Some ht) (ent_huf pe)).
             sep_apply (dl_release pe (Some ht) None None None Hpe).
             entailer!. dl_efin.
           + forward. entailer!. dl_noerr.
         - Intros. exfalso; congruence. }
    match goal with H: r = sOF /\ _ |- _ => destruct H as (? & HsOF & HncOF & HsubOF) end. subst r.
    rewrite Hl1 in HsOF.
    assert (HeOF: is_error_code sOF = false) by (unfold is_error_code; apply Z.ltb_ge; lia).
    dl_check (is_error_code sOF = false).
    { entailer!. }
    { forward_call sOF. rewrite HeOF. forward_if; [contradiction | forward; entailer!]. }
    Intros.
    pose proof HncOF as (HlogOF & HlenOF & HallOF & HsumOF).
    dl_check True.
    { entailer!. }
    { forward. forward_if; [dl_nomax | forward; entailer!]. }
    Intros.
    dl_check (lOF <= OffFSELog).
    { entailer!. }
    { forward. forward_if.
      - try match goal with H: _ < Int.unsigned (Int.repr lOF) |- _ =>
            rewrite Int.unsigned_repr in H by rep_lia end.
        repeat dl_skiploop. forward. Exists (err_code 30) (@None (dstate * Z)).
        change (hufdt_at Ews ht (ent_huf pe)) with (dl_huf (Some ht) (ent_huf pe)).
        sep_apply (dl_release pe (Some ht) None None None Hpe).
        entailer!. dl_efin.
      - forward. entailer!.
        try match goal with H: Int.unsigned (Int.repr lOF) <= _ |- _ =>
          rewrite Int.unsigned_repr in H by rep_lia end.
        unfold OffFSELog; lia. }
    Intros.
    specialize (HsubOF ltac:(unfold OffFSELog, MLFSELog, LLFSELog in *; lia)).
    forward. forward.
    change (seqspace_at Ews KOF None (ent_seq KOF pe))
      with (data_at_ Ews (tarray t_seqSymbol (sk_size KOF)) (ent_seq KOF pe)).
    rewrite (field_at__data_at_ Ews t_entropy (DOT _workspace)).
    forward_call (gv, KOF, Ews, ent_seq KOF pe, Tsh, v_offcodeNCount, ncOF, nOF, lOF, Ews,
                  field_address t_entropy (DOT _workspace) pe, 157).
    { entailer!. unfold ent_seq. simpl. rewrite !field_address_offset by auto with field_compatible.
      reflexivity. }
    { match goal with H: Zlength ncOF = _ |- _ => rewrite H end. cancel. }
    { unfold MaxOff in *. lia. }
    sep_apply (dl_ws_fold pe).
    match goal with H: Zlength ncOF = 32 |- _ => rewrite H end.
    forward.
    rewrite (dl_add_ptr (offset_val (8 + hs) d) sOF) by (auto; rep_lia).
    rewrite offset_offset_val.
    (* ---------- ML ---------- *)
    assert (Hp2: 0 <= 8 + hs + sOF <= Zlength b) by lia.
    assert (Hl2: Zlength (skipn (Z.to_nat (8 + hs + sOF)) b) = Zlength b - (8 + hs + sOF))
      by (rewrite <- sublist_skip, Zlength_sublist by lia; lia).
    forward.
    forward_call (gv, Tsh, v_matchlengthNCount, 53, Tsh, v_matchlengthMaxValue, Tsh, v_matchlengthLog, MaxML,
                  sh, d, Zlength b, zbytes b, 8 + hs + sOF, skipn (Z.to_nat (8 + hs + sOF)) b).
    { dl_sameblock d. }
    { dl_params d Hl2. }
    { rewrite Hl2. apply dl_win; auto; lia. }
    Intros rnc. destruct rnc as [[r ncML] resML]. cbn [fst snd] in *.
    destruct resML as [[[nML lML] sML] |].
    2: { dl_check (is_error_code r = false).
         - entailer!.
         - forward_call r. forward_if.
           + repeat dl_skiploop. forward. Exists (err_code 30) (@None (dstate * Z)).
             change (hufdt_at Ews ht (ent_huf pe)) with (dl_huf (Some ht) (ent_huf pe)).
             sep_apply (dl_release pe (Some ht) None (Some (fse_build nOF lOF)) None Hpe).
             entailer!. dl_efin.
           + forward. entailer!. dl_noerr.
         - Intros. exfalso; congruence. }
    match goal with H: r = sML /\ _ |- _ => destruct H as (? & HsML & HncML & HsubML) end. subst r.
    rewrite Hl2 in HsML.
    assert (HeML: is_error_code sML = false) by (unfold is_error_code; apply Z.ltb_ge; lia).
    dl_check (is_error_code sML = false).
    { entailer!. }
    { forward_call sML. rewrite HeML. forward_if; [contradiction | forward; entailer!]. }
    Intros.
    pose proof HncML as (HlogML & HlenML & HallML & HsumML).
    dl_check True.
    { entailer!. }
    { forward. forward_if; [dl_nomax | forward; entailer!]. }
    Intros.
    dl_check (lML <= MLFSELog).
    { entailer!. }
    { forward. forward_if.
      - try match goal with H: _ < Int.unsigned (Int.repr lML) |- _ =>
            rewrite Int.unsigned_repr in H by rep_lia end.
        repeat dl_skiploop. forward. Exists (err_code 30) (@None (dstate * Z)).
        change (hufdt_at Ews ht (ent_huf pe)) with (dl_huf (Some ht) (ent_huf pe)).
        sep_apply (dl_release pe (Some ht) None (Some (fse_build nOF lOF)) None Hpe).
        entailer!. dl_efin.
      - forward. entailer!.
        try match goal with H: Int.unsigned (Int.repr lML) <= _ |- _ =>
          rewrite Int.unsigned_repr in H by rep_lia end.
        unfold MLFSELog; lia. }
    Intros.
    specialize (HsubML ltac:(unfold OffFSELog, MLFSELog, LLFSELog in *; lia)).
    forward. forward.
    change (seqspace_at Ews KML None (ent_seq KML pe))
      with (data_at_ Ews (tarray t_seqSymbol (sk_size KML)) (ent_seq KML pe)).
    rewrite (field_at__data_at_ Ews t_entropy (DOT _workspace)).
    forward_call (gv, KML, Ews, ent_seq KML pe, Tsh, v_matchlengthNCount, ncML, nML, lML, Ews,
                  field_address t_entropy (DOT _workspace) pe, 157).
    { entailer!. unfold ent_seq. simpl. rewrite !field_address_offset by auto with field_compatible.
      reflexivity. }
    { match goal with H: Zlength ncML = _ |- _ => rewrite H end. cancel. }
    { unfold MaxML in *. lia. }
    sep_apply (dl_ws_fold pe).
    match goal with H: Zlength ncML = 53 |- _ => rewrite H end.
    forward.
    rewrite (dl_add_ptr (offset_val (8 + hs + sOF) d) sML) by (auto; rep_lia).
    rewrite offset_offset_val.
    (* ---------- LL ---------- *)
    assert (Hp3: 0 <= 8 + hs + sOF + sML <= Zlength b) by lia.
    assert (Hl3: Zlength (skipn (Z.to_nat (8 + hs + sOF + sML)) b) = Zlength b - (8 + hs + sOF + sML))
      by (rewrite <- sublist_skip, Zlength_sublist by lia; lia).
    forward.
    forward_call (gv, Tsh, v_litlengthNCount, 36, Tsh, v_litlengthMaxValue, Tsh, v_litlengthLog, MaxLL,
                  sh, d, Zlength b, zbytes b, 8 + hs + sOF + sML, skipn (Z.to_nat (8 + hs + sOF + sML)) b).
    { dl_sameblock d. }
    { dl_params d Hl3. }
    { rewrite Hl3. apply dl_win; auto; lia. }
    Intros rnc. destruct rnc as [[r ncLL] resLL]. cbn [fst snd] in *.
    destruct resLL as [[[nLL lLL] sLL] |].
    2: { dl_check (is_error_code r = false).
         - entailer!.
         - forward_call r. forward_if.
           + repeat dl_skiploop. forward. Exists (err_code 30) (@None (dstate * Z)).
             change (hufdt_at Ews ht (ent_huf pe)) with (dl_huf (Some ht) (ent_huf pe)).
             sep_apply (dl_release pe (Some ht) None (Some (fse_build nOF lOF)) (Some (fse_build nML lML)) Hpe).
             entailer!. dl_efin.
           + forward. entailer!. dl_noerr.
         - Intros. exfalso; congruence. }
    match goal with H: r = sLL /\ _ |- _ => destruct H as (? & HsLL & HncLL & HsubLL) end. subst r.
    rewrite Hl3 in HsLL.
    assert (HeLL: is_error_code sLL = false) by (unfold is_error_code; apply Z.ltb_ge; lia).
    dl_check (is_error_code sLL = false).
    { entailer!. }
    { forward_call sLL. rewrite HeLL. forward_if; [contradiction | forward; entailer!]. }
    Intros.
    pose proof HncLL as (HlogLL & HlenLL & HallLL & HsumLL).
    dl_check True.
    { entailer!. }
    { forward. forward_if; [dl_nomax | forward; entailer!]. }
    Intros.
    dl_check (lLL <= LLFSELog).
    { entailer!. }
    { forward. forward_if.
      - try match goal with H: _ < Int.unsigned (Int.repr lLL) |- _ =>
            rewrite Int.unsigned_repr in H by rep_lia end.
        repeat dl_skiploop. forward. Exists (err_code 30) (@None (dstate * Z)).
        change (hufdt_at Ews ht (ent_huf pe)) with (dl_huf (Some ht) (ent_huf pe)).
        sep_apply (dl_release pe (Some ht) None (Some (fse_build nOF lOF)) (Some (fse_build nML lML)) Hpe).
        entailer!. dl_efin.
      - forward. entailer!.
        try match goal with H: Int.unsigned (Int.repr lLL) <= _ |- _ =>
          rewrite Int.unsigned_repr in H by rep_lia end.
        unfold LLFSELog; lia. }
    Intros.
    specialize (HsubLL ltac:(unfold OffFSELog, MLFSELog, LLFSELog in *; lia)).
    forward. forward.
    change (seqspace_at Ews KLL None (ent_seq KLL pe))
      with (data_at_ Ews (tarray t_seqSymbol (sk_size KLL)) (ent_seq KLL pe)).
    rewrite (field_at__data_at_ Ews t_entropy (DOT _workspace)).
    forward_call (gv, KLL, Ews, ent_seq KLL pe, Tsh, v_litlengthNCount, ncLL, nLL, lLL, Ews,
                  field_address t_entropy (DOT _workspace) pe, 157).
    { entailer!. unfold ent_seq. simpl. rewrite !field_address_offset by auto with field_compatible.
      reflexivity. }
    { match goal with H: Zlength ncLL = _ |- _ => rewrite H end. cancel. }
    { unfold MaxLL in *. lia. }
    sep_apply (dl_ws_fold pe).
    match goal with H: Zlength ncLL = 36 |- _ => rewrite H end.
    forward.
    rewrite (dl_add_ptr (offset_val (8 + hs + sOF + sML) d) sLL) by (auto; rep_lia).
    rewrite offset_offset_val.
    (* ---------- the repeat offsets ---------- *)
    assert (HP: 0 <= 8 + hs + sOF + sML + sLL <= Zlength b) by lia.
    dl_check (8 + hs + sOF + sML + sLL + 12 <= Zlength b).
    { entailer!. }
    { forward_if.
      - dl_sameblock d.
      - assert (Hlt: Zlength b - (8 + hs + sOF + sML + sLL) < 12) by dl_cond12 d.
        repeat dl_skiploop. forward. Exists (err_code 30) (@None (dstate * Z)).
        change (hufdt_at Ews ht (ent_huf pe)) with (dl_huf (Some ht) (ent_huf pe)).
        sep_apply (dl_release pe (Some ht) (Some (fse_build nLL lLL)) (Some (fse_build nOF lOF))
                     (Some (fse_build nML lML)) Hpe).
        entailer!. dl_efin.
      - assert (Hge: 12 <= Zlength b - (8 + hs + sOF + sML + sLL)) by dl_cond12 d.
        forward. entailer!. }
    Intros.
    forward.
    { dl_sameblock d. }
    assert (Hcs: force_val (sem_binary_operation' Osub (tptr tuchar) (tptr tuchar) (offset_val (Zlength b) d)
                   (eval_binop Oadd (tptr tuchar) tint (offset_val (8 + hs + sOF + sML + sLL) d) (Vint (Int.repr 12))))
                 = Vlong (Int64.repr (Zlength b - ((8 + hs + sOF + sML + sLL) + 12)))).
    { unfold eval_binop, force_val2. rewrite dl_add_int by (auto; rep_lia). rewrite offset_offset_val.
      destruct d; try contradiction. simpl offset_val. simpl sem_binary_operation'.
      apply dl_sub_pp; rep_lia. }
    rewrite Hcs. clear Hcs.
    sep_apply (dl_rep_init b (8 + hs + sOF + sML + sLL) pe).
    forward_for_simple_bound 3 (EX i: Z,
      PROP (forall j, 0 <= j < i -> 0 < le_field b ((8 + hs + sOF + sML + sLL) + 4 * j) 4 <= Zlength b - ((8 + hs + sOF + sML + sLL) + 12))
      LOCAL (temp _dictPtr (offset_val ((8 + hs + sOF + sML + sLL) + 4 * i) d);
             temp _dictContentSize (Vlong (Int64.repr (Zlength b - ((8 + hs + sOF + sML + sLL) + 12))));
             temp _entropy pe; temp _dict d; gvars gv;
             lvar _litlengthLog tuint v_litlengthLog;
             lvar _litlengthMaxValue tuint v_litlengthMaxValue;
             lvar _litlengthNCount (tarray tshort 36) v_litlengthNCount;
             lvar _matchlengthLog tuint v_matchlengthLog;
             lvar _matchlengthMaxValue tuint v_matchlengthMaxValue;
             lvar _matchlengthNCount (tarray tshort 53) v_matchlengthNCount;
             lvar _offcodeLog tuint v_offcodeLog;
             lvar _offcodeMaxValue tuint v_offcodeMaxValue;
             lvar _offcodeNCount (tarray tshort 32) v_offcodeNCount)
      SEP (zstd_globals gv; hufdt_at Ews ht (ent_huf pe);
           seqspace_at Ews KLL (Some (fse_build nLL lLL)) (ent_seq KLL pe);
           seqspace_at Ews KOF (Some (fse_build nOF lOF)) (ent_seq KOF pe);
           seqspace_at Ews KML (Some (fse_build nML lML)) (ent_seq KML pe);
           field_at Ews t_entropy (DOT _rep) (dl_repv b (8 + hs + sOF + sML + sLL) i) pe;
           field_at_ Ews t_entropy (DOT _workspace) pe;
           data_at sh (tarray tuchar (Zlength b)) (zbytes b) d;
           data_at Tsh (tarray tshort 32) ncOF v_offcodeNCount;
           data_at Tsh tuint (Vint (Int.repr (Zlength nOF - 1))) v_offcodeMaxValue;
           data_at Tsh tuint (Vint (Int.repr lOF)) v_offcodeLog;
           data_at Tsh (tarray tshort 53) ncML v_matchlengthNCount;
           data_at Tsh tuint (Vint (Int.repr (Zlength nML - 1))) v_matchlengthMaxValue;
           data_at Tsh tuint (Vint (Int.repr lML)) v_matchlengthLog;
           data_at Tsh (tarray tshort 36) ncLL v_litlengthNCount;
           data_at Tsh tuint (Vint (Int.repr (Zlength nLL - 1))) v_litlengthMaxValue;
           data_at Tsh tuint (Vint (Int.repr lLL)) v_litlengthLog))%assert.
    { entailer!; intros; lia. }
    { forward_call (sh, d, b, (8 + hs + sOF + sML + sLL) + 4 * i).
      { unfold mem_read_pre. split; [auto |]. split; [lia |]. split; [lia |].
        unfold bytes_ok in *. apply Forall_sublist; auto. }
      Intros vret. subst vret.
      forward.
      rewrite (dl_add_int (offset_val ((8 + hs + sOF + sML + sLL) + 4 * i) d) 4) by (auto; rep_lia).
      rewrite offset_offset_val.
      pose proof (dl_le4 b ((8 + hs + sOF + sML + sLL) + 4 * i) H0) as Hr.
      dl_check (0 < le_field b ((8 + hs + sOF + sML + sLL) + 4 * i) 4 <= Zlength b - ((8 + hs + sOF + sML + sLL) + 12)).
      { entailer!. }
      { forward_if (temp _t'10 (Vint (Int.repr (if orb (le_field b ((8 + hs + sOF + sML + sLL) + 4 * i) 4 =? 0)
                         (le_field b ((8 + hs + sOF + sML + sLL) + 4 * i) 4 >? Zlength b - ((8 + hs + sOF + sML + sLL) + 12)) then 1 else 0)))).
        - forward. entailer!.
          match goal with H: le_field _ _ 4 = 0 |- _ => rewrite H end. reflexivity.
        - forward. entailer!.
          rewrite (proj2 (Z.eqb_neq _ _)) by assumption. cbn [orb].
          unfold Int64.cmpu, Int64.ltu. rewrite !Int64.unsigned_repr by rep_lia.
          destruct (zlt _ _); [rewrite (proj2 (Z.gtb_lt _ _)) by lia | rewrite dl_gtb_false by lia];
            reflexivity.
        - forward_if.
          + match goal with H: (if ?c then 1 else 0) <> 0 |- _ =>
              destruct c eqn:Ec; [clear H | contradiction] end.
            assert (Hex: existsb (fun r => orb (r =? 0) (r >? Zlength b - ((8 + hs + sOF + sML + sLL) + 12)))
                           [le_field b (8 + hs + sOF + sML + sLL) 4; le_field b ((8 + hs + sOF + sML + sLL) + 4) 4; le_field b ((8 + hs + sOF + sML + sLL) + 8) 4] = true).
            { apply existsb_exists. exists (le_field b ((8 + hs + sOF + sML + sLL) + 4 * i) 4). split; [| exact Ec].
              assert (i = 0 \/ i = 1 \/ i = 2) as [-> | [-> | ->]] by lia;
                [left | right; left | right; right; left]; f_equal; lia. }
            repeat dl_skiploop. forward. Exists (err_code 30) (@None (dstate * Z)).
            sep_apply (field_at_field_at_ Ews t_entropy (DOT _rep) (dl_repv b (8 + hs + sOF + sML + sLL) i) pe).
            change (hufdt_at Ews ht (ent_huf pe)) with (dl_huf (Some ht) (ent_huf pe)).
            sep_apply (dl_release pe (Some ht) (Some (fse_build nLL lLL)) (Some (fse_build nOF lOF))
                         (Some (fse_build nML lML)) Hpe).
            entailer!. dl_efin.
          + forward. entailer!.
            match goal with H: Int.repr (if ?c then 1 else 0) = Int.zero |- _ =>
              destruct c eqn:Ec; [apply (f_equal Int.unsigned) in H; vm_compute in H; discriminate | clear H] end.
            apply orb_false_iff in Ec as [E1 E2]. apply Z.eqb_neq in E1.
            rewrite Z.gtb_ltb, Z.ltb_ge in E2. lia. }
      Intros.
      forward.
      entailer!.
      - split.
        + intros j Hj. assert (j < i \/ j = i) as [Hj' | ->] by lia; [| lia].
          match goal with H: forall j, 0 <= j < i -> _ |- _ => apply H; lia end.
        + f_equal. lia.
      - rewrite <- (dl_repv_upd b _ i) by lia. apply derives_refl. }
    Intros.
    assert (Hex: existsb (fun r => orb (r =? 0) (r >? Zlength b - ((8 + hs + sOF + sML + sLL) + 12)))
                   [le_field b (8 + hs + sOF + sML + sLL) 4; le_field b ((8 + hs + sOF + sML + sLL) + 4) 4; le_field b ((8 + hs + sOF + sML + sLL) + 8) 4] = false).
    { match goal with H: forall j, 0 <= j < 3 -> _ |- _ =>
        pose proof (H 0 ltac:(lia)); pose proof (H 1 ltac:(lia)); pose proof (H 2 ltac:(lia)) end.
      rewrite Z.mul_0_r, Z.add_0_r in *. simpl Z.mul in *.
      simpl existsb.
      rewrite !(proj2 (Z.eqb_neq _ _)) by lia. rewrite !dl_gtb_false by lia. reflexivity. }
    assert_PROP (huf_ok ht) as Hho by (sep_apply (dl_hufdt_ok Ews ht (ent_huf pe)); entailer!).
    assert_PROP (fse_ok KLL (fse_build nLL lLL)) as Hfl
      by (sep_apply (dl_seq_ok Ews KLL (fse_build nLL lLL) (ent_seq KLL pe)); entailer!).
    assert_PROP (fse_ok KOF (fse_build nOF lOF)) as Hfo
      by (sep_apply (dl_seq_ok Ews KOF (fse_build nOF lOF) (ent_seq KOF pe)); entailer!).
    assert_PROP (fse_ok KML (fse_build nML lML)) as Hfm
      by (sep_apply (dl_seq_ok Ews KML (fse_build nML lML) (ent_seq KML pe)); entailer!).
    forward.
    { dl_sameblock d. }
    Exists ((8 + hs + sOF + sML + sLL) + 12)
      (Some ({| st_huf := Some ht;
                st_seq := Some (fse_build nLL lLL, fse_build nOF lOF, fse_build nML lML);
                st_rep := (le_field b (8 + hs + sOF + sML + sLL) 4, le_field b (8 + hs + sOF + sML + sLL + 4) 4, le_field b (8 + hs + sOF + sML + sLL + 8) 4) |},
             8 + hs + sOF + sML + sLL + 12)).
    unfold ent_full. cbn [st_huf st_seq st_rep].
    rewrite dl_repv_3.
    entailer!.
    match goal with H: forall j, 0 <= j < 3 -> _ |- _ =>
      pose proof (H 0 ltac:(lia)); pose proof (H 1 ltac:(lia)); pose proof (H 2 ltac:(lia)) end.
    rewrite Z.mul_0_r, Z.add_0_r in *. simpl Z.mul in *.
    pose proof (dl_le4 b (8 + hs + sOF + sML + sLL) H0). pose proof (dl_le4 b ((8 + hs + sOF + sML + sLL) + 4) H0). pose proof (dl_le4 b ((8 + hs + sOF + sML + sLL) + 8) H0).
    split; [dl_ld; intros Hx; exact Hx |].
    split.
    * unfold dstate_ok, seqs_ok, rep_ok. cbn [st_huf st_seq st_rep].
      split; [exact Hho |]. split; [exact (conj Hfl (conj Hfo Hfm)) |]. lia.
    * replace ((8 + hs + sOF + sML + sLL) + 12) with ((8 + hs + sOF + sML + sLL) + 12) by lia.
      destruct d; try contradiction. simpl offset_val. rewrite dl_sub_pp0 by rep_lia. reflexivity.
Qed.
