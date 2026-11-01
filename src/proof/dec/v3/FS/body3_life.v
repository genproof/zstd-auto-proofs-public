(* FS3 bodies, life3: context creation and freeing (port of v2 body_FS_life.v; freeDCtx frees the DDict set).
   (obligation FSOblig3.FS3_body: for ANY DENT/TABS of B, ANY SR, ANY BR). *)
Require Import Zstd.proof.dec.v3.FS.FSOblig3.
Local Open Scope logic.

Section CM_body3_life_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* ---------- the malloc'd struct as consecutive memory blocks (fields and padding) ---------- *)

Fixpoint consec (o: Z) (l: list (Z * Z)) (e: Z) : bool :=
  match l with
  | nil => Z.eqb o e
  | (o', s) :: r => Z.eqb o o' && Z.leb 0 s && consec (o + s) r e
  end.

Definition mbs (sh: share) (l: list (Z * Z)) (p: val) : mpred :=
  fold_right (fun x acc => memory_block sh (snd x) (offset_val (fst x) p) * acc) emp l.

Lemma consec_le: forall l o e, consec o l e = true -> o <= e.
Proof.
  induction l as [|[o' s] r IH]; simpl; intros o e H.
  - apply Z.eqb_eq in H; lia.
  - apply andb_prop in H as [H H2]; apply andb_prop in H as [H0 H1].
    apply Z.leb_le in H1. apply IH in H2. apply Z.eqb_eq in H0. lia.
Qed.

Lemma ov_repr (b: block) (i: ptrofs) (o: Z) : 0 <= o <= Ptrofs.max_unsigned ->
  offset_val o (Vptr b i) = Vptr b (Ptrofs.repr (Ptrofs.unsigned i + o)).
Proof.
  intros. simpl. f_equal. unfold Ptrofs.add. rewrite (Ptrofs.unsigned_repr o) by lia. reflexivity.
Qed.

Lemma mb_consec: forall sh l o e b i, consec o l e = true -> 0 <= o ->
  Ptrofs.unsigned i + e < Ptrofs.modulus ->
  memory_block sh (e - o) (offset_val o (Vptr b i)) = mbs sh l (Vptr b i).
Proof.
  induction l as [|[o' s] r IH]; intros o e b i H Ho Hb.
  - simpl in H. apply Z.eqb_eq in H. subst. rewrite Z.sub_diag, memory_block_zero.
    unfold mbs; simpl. rewrite prop_true_andp by auto. reflexivity.
  - simpl in H. apply andb_prop in H as [H H2]; apply andb_prop in H as [H0 H1].
    apply Z.eqb_eq in H0; apply Z.leb_le in H1. subst o'.
    pose proof (consec_le _ _ _ H2). pose proof (Ptrofs.unsigned_range i).
    change (mbs sh ((o, s) :: r) (Vptr b i))
      with (memory_block sh s (offset_val o (Vptr b i)) * mbs sh r (Vptr b i)).
    rewrite <- (IH (o + s) e b i H2 ltac:(lia) Hb).
    replace (e - o) with (s + (e - (o + s))) by lia.
    rewrite !ov_repr by rep_lia.
    rewrite memory_block_split by lia.
    rewrite Z.add_assoc. reflexivity.
Qed.

(* the tiling of ZSTD_DCtx_s: its 60 fields and 7 padding gaps *)
Definition dctx_tiles : list (Z * Z) :=
  [(0, 8); (8, 8); (16, 8); (24, 8); (32, 27292); (27324, 2560); (29884, 4); (29888, 8); (29896, 4); (29900, 4); (29904, 8); (29912, 8); (29920, 8); (29928, 8); (29936, 48); (29984, 8); (29992, 8); (30000, 4); (30004, 4); (30008, 4); (30012, 4); (30016, 88); (30104, 8); (30112, 4); (30116, 4); (30120, 4); (30124, 4); (30128, 8); (30136, 24); (30160, 8); (30168, 8); (30176, 8); (30184, 4); (30188, 4); (30192, 8); (30200, 8); (30208, 4); (30212, 4); (30216, 4); (30220, 4); (30224, 8); (30232, 4); (30236, 4); (30240, 4); (30244, 4); (30248, 8); (30256, 8); (30264, 8); (30272, 8); (30280, 8); (30288, 8); (30296, 8); (30304, 8); (30312, 8); (30320, 4); (30324, 4); (30328, 4); (30332, 4); (30336, 24); (30360, 8); (30368, 8); (30376, 4); (30380, 65568); (95948, 18); (95966, 2); (95968, 8)].

Lemma dctx_tiles_consec : consec 0 dctx_tiles 95976 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma fc_dctx (f: ident) (q: val) :
  field_compatible t_dctx nil q -> in_members f (co_members (get_co _ZSTD_DCtx_s)) ->
  field_compatible t_dctx (DOT f) q.
Proof. intros. apply field_compatible_cons. split; auto. Qed.

Lemma fa_mb (q: val) (f: ident) (o s: Z) :
  field_compatible t_dctx (DOT f) q -> nested_field_offset t_dctx (DOT f) = o ->
  sizeof (nested_field_type t_dctx (DOT f)) = s ->
  field_at_ Ews t_dctx (DOT f) q = memory_block Ews s (offset_val o q).
Proof. intros. rewrite field_at__memory_block, field_address_offset by auto. congruence. Qed.

Lemma dctx_fields_mbs (q: val) : field_compatible t_dctx nil q ->
  dctx_fields_ q = mbs Ews dctx_tiles q.
Proof.
  intros Hfc.
  assert (F: forall f, in_members f (co_members (get_co _ZSTD_DCtx_s)) -> field_compatible t_dctx (DOT f) q)
    by (intros; apply fc_dctx; auto).
  unfold dctx_fields_.
  rewrite (fa_mb q _LLTptr 0 8) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _MLTptr 8 8) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _OFTptr 16 8) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _HUFptr 24 8) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _entropy 32 27292) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _workspace 27324 2560) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _previousDstEnd 29888 8) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _gpDictCopy 29896 4) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _prefixStart 29904 8) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _virtualStart 29912 8) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _dictEnd 29920 8) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _expected 29928 8) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _fParams 29936 48) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _processedCSize 29984 8) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _decodedSize 29992 8) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _bType 30000 4) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _stage 30004 4) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _litEntropy 30008 4) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _fseEntropy 30012 4) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _xxhState 30016 88) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _headerSize 30104 8) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _format 30112 4) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _forceIgnoreChecksum 30116 4) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _validateChecksum 30120 4) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _litPtr 30128 8) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _customMem 30136 24) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _litSize 30160 8) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _rleSize 30168 8) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _staticSize 30176 8) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _isFrameDecompression 30184 4) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _ddictLocal 30192 8) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _ddict 30200 8) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _dictID 30208 4) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _ddictIsCold 30212 4) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _dictUses 30216 4) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _ddictSet 30224 8) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _refMultipleDDicts 30232 4) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _disableHufAsm 30236 4) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _maxBlockSizeParam 30240 4) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _streamStage 30244 4) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _inBuff 30248 8) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _inBuffSize 30256 8) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _inPos 30264 8) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _maxWindowSize 30272 8) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _outBuff 30280 8) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _outBuffSize 30288 8) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _outStart 30296 8) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _outEnd 30304 8) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _lhSize 30312 8) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _hostageByte 30320 4) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _noForwardProgress 30324 4) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _outBufferMode 30328 4) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _expectedOutBuffer 30336 24) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _litBuffer 30360 8) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _litBufferEnd 30368 8) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _litBufferLocation 30376 4) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _litExtraBuffer 30380 65568) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _headerBuffer 95948 18) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _oversizedDuration 95968 8) by (try apply F; try reflexivity; vm_compute; tauto).
  unfold dctx_pad, mbs, dctx_tiles; simpl fold_right.
  apply pred_ext; cancel.
Qed.

Lemma dctx_split (q: val) : data_at_ Ews t_dctx q |-- dctx_fields_ q.
Proof.
  rewrite data_at__memory_block. Intros. rewrite dctx_fields_mbs by auto.
  destruct q as [| | | | |b i]; try contradiction (proj1 H).
  change (sizeof t_dctx) with 95976.
  assert_PROP (Ptrofs.unsigned i + 95976 < Ptrofs.modulus) as Hb.
  { sep_apply memory_block_local_facts. entailer!. }
  rewrite <- (mb_consec Ews dctx_tiles 0 95976 b i dctx_tiles_consec) by lia.
  rewrite isptr_offset_val_zero by auto. cancel.
Qed.

Lemma dctx_merge (q: val) : field_compatible t_dctx nil q ->
  dctx_fields_ q |-- data_at_ Ews t_dctx q.
Proof.
  intros Hfc. rewrite dctx_fields_mbs by auto. rewrite data_at__memory_block.
  destruct q as [| | | | |b i]; try contradiction (proj1 Hfc).
  change (sizeof t_dctx) with 95976.
  assert_PROP (Ptrofs.unsigned i + 95976 < Ptrofs.modulus) as Hb.
  { destruct Hfc as (_ & _ & Hsz & _). red in Hsz. simpl sizeof in Hsz. entailer!. }
  rewrite <- (mb_consec Ews dctx_tiles 0 95976 b i dctx_tiles_consec) by lia.
  rewrite isptr_offset_val_zero by auto. entailer!. apply derives_refl.
Qed.

(* the tiles of dctx_tiles below and above litExtraBuffer (30380, 65568) *)
Definition dctx_tiles_lo1 : list (Z * Z) :=
  [(0, 8); (8, 8); (16, 8); (24, 8); (32, 27292); (27324, 2560); (29884, 4); (29888, 8); (29896, 4); (29900, 4); (29904, 8); (29912, 8); (29920, 8); (29928, 8)].
Definition dctx_tiles_lo2 : list (Z * Z) :=
  [(29984, 8); (29992, 8); (30000, 4); (30004, 4); (30008, 4); (30012, 4); (30016, 88); (30104, 8); (30112, 4); (30116, 4); (30120, 4); (30124, 4); (30128, 8); (30136, 24); (30160, 8); (30168, 8); (30176, 8); (30184, 4); (30188, 4); (30192, 8); (30200, 8); (30208, 4); (30212, 4); (30216, 4); (30220, 4); (30224, 8); (30232, 4); (30236, 4); (30240, 4); (30244, 4); (30248, 8); (30256, 8); (30264, 8); (30272, 8); (30280, 8); (30288, 8); (30296, 8); (30304, 8); (30312, 8); (30320, 4); (30324, 4); (30328, 4); (30332, 4); (30336, 24); (30360, 8); (30368, 8); (30376, 4)].
Definition dctx_tiles_hi : list (Z * Z) := [(95948, 18); (95966, 2); (95968, 8)].

Lemma dctx_tiles_lo1_consec : consec 0 dctx_tiles_lo1 29936 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma dctx_tiles_lo2_consec : consec 29984 dctx_tiles_lo2 30380 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma dctx_tiles_hi_consec : consec 95948 dctx_tiles_hi 95976 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma dctx_nofp_mbs (q: val) : field_compatible t_dctx nil q ->
  mbs Ews dctx_tiles_lo1 q * mbs Ews dctx_tiles_lo2 q * mbs Ews dctx_tiles_hi q * lit_extra_at q lxb_zero |--
  data_at_ Ews t_cmem (field_address t_dctx (DOT _customMem) q) * dctx_fields_nofp q * dctx_pad q.
Proof.
  intros Hfc.
  assert (F: forall f, in_members f (co_members (get_co _ZSTD_DCtx_s)) -> field_compatible t_dctx (DOT f) q)
    by (intros; apply fc_dctx; auto).
  replace (data_at_ Ews t_cmem (field_address t_dctx (DOT _customMem) q))
    with (field_at_ Ews t_dctx (DOT _customMem) q) by (rewrite field_at__data_at_; reflexivity).
  unfold dctx_fields_nofp.
  rewrite (fa_mb q _LLTptr 0 8) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _MLTptr 8 8) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _OFTptr 16 8) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _HUFptr 24 8) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _entropy 32 27292) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _workspace 27324 2560) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _previousDstEnd 29888 8) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _gpDictCopy 29896 4) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _prefixStart 29904 8) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _virtualStart 29912 8) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _dictEnd 29920 8) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _expected 29928 8) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _processedCSize 29984 8) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _decodedSize 29992 8) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _bType 30000 4) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _stage 30004 4) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _litEntropy 30008 4) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _fseEntropy 30012 4) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _xxhState 30016 88) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _headerSize 30104 8) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _format 30112 4) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _forceIgnoreChecksum 30116 4) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _validateChecksum 30120 4) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _litPtr 30128 8) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _customMem 30136 24) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _litSize 30160 8) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _rleSize 30168 8) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _staticSize 30176 8) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _isFrameDecompression 30184 4) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _ddictLocal 30192 8) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _ddict 30200 8) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _dictID 30208 4) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _ddictIsCold 30212 4) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _dictUses 30216 4) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _ddictSet 30224 8) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _refMultipleDDicts 30232 4) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _disableHufAsm 30236 4) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _maxBlockSizeParam 30240 4) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _streamStage 30244 4) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _inBuff 30248 8) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _inBuffSize 30256 8) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _inPos 30264 8) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _maxWindowSize 30272 8) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _outBuff 30280 8) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _outBuffSize 30288 8) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _outStart 30296 8) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _outEnd 30304 8) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _lhSize 30312 8) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _hostageByte 30320 4) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _noForwardProgress 30324 4) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _outBufferMode 30328 4) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _expectedOutBuffer 30336 24) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _litBuffer 30360 8) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _litBufferEnd 30368 8) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _litBufferLocation 30376 4) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _headerBuffer 95948 18) by (try apply F; try reflexivity; vm_compute; tauto).
  rewrite (fa_mb q _oversizedDuration 95968 8) by (try apply F; try reflexivity; vm_compute; tauto).
  unfold dctx_pad, mbs, dctx_tiles_lo1, dctx_tiles_lo2, dctx_tiles_hi; simpl fold_right.
  cancel.
Qed.

Lemma zv_fh : zero_val t_fh = fh_val fh_zero.
Proof.
  assert (E: forall z: reptype t_fh,
    fst z = Vlong Int64.zero -> fst (snd z) = Vlong Int64.zero -> fst (snd (snd z)) = Vint Int.zero ->
    fst (snd (snd (snd z))) = Vint Int.zero -> fst (snd (snd (snd (snd z)))) = Vint Int.zero ->
    fst (snd (snd (snd (snd (snd z))))) = Vint Int.zero -> fst (snd (snd (snd (snd (snd (snd z)))))) = Vint Int.zero ->
    fst (snd (snd (snd (snd (snd (snd (snd z))))))) = Vint Int.zero ->
    snd (snd (snd (snd (snd (snd (snd (snd z))))))) = Vint Int.zero -> z = fh_val fh_zero).
  { intros z. destruct z as [a1 [a2 [a3 [a4 [a5 [a6 [a7 [a8 a9]]]]]]]]. simpl.
    intros -> -> -> -> -> -> -> -> ->. reflexivity. }
  apply E;
    first [ transitivity (zero_val tulong); [rewrite (zero_val_eq t_fh); reflexivity | apply zero_val_Tlong]
          | transitivity (zero_val tuint); [rewrite (zero_val_eq t_fh); reflexivity | apply zero_val_Tint]
          | transitivity (zero_val tint); [rewrite (zero_val_eq t_fh); reflexivity | apply zero_val_Tint] ].
Qed.

(* the calloc's 48 zero bytes of fParams are the zero header (zstd's loadHeader reads fParams.dictID) *)
Lemma fp_zero (q: val) : field_compatible t_dctx nil q ->
  data_at Ews (Tarray tuchar 48 noattr) (Zrepeat (Vint Int.zero) 48) (offset_val 29936 q) |--
  field_at Ews t_dctx (DOT _fParams) (fh_val fh_zero) q.
Proof.
  intros Hfc.
  assert (Hf: field_compatible t_dctx (DOT _fParams) q) by (apply fc_dctx; auto; vm_compute; tauto).
  rewrite field_at_data_at, field_address_offset by exact Hf.
  change (nested_field_offset t_dctx (DOT _fParams)) with 29936.
  change (nested_field_type t_dctx (DOT _fParams)) with t_fh.
  assert (Hc: field_compatible t_fh nil (offset_val 29936 q)).
  { exact (field_compatible_nested_field t_dctx (DOT _fParams) q Hf). }
  change (Tarray tuchar 48 noattr) with (tarray tuchar (sizeof t_fh)).
  change 48 with (sizeof t_fh).
  eapply derives_trans; [apply memset_zero_data_at; auto; reflexivity |].
  rewrite zv_fh. apply derives_refl.
Qed.

(* a context zstd calloc'd (contract patch item 17) in a block aligned as malloc's (its allocation token, of either
   allocator, is kept apart) *)
Lemma dctx_calloc_split' (q: val) : malloc_compatible (sizeof (tarray tuchar (sizeof t_dctx))) q ->
  data_at Ews (tarray tuchar (sizeof t_dctx)) (Zrepeat (Vint Int.zero) (sizeof t_dctx)) q |--
  !! field_compatible t_dctx nil q &&
  (data_at_ Ews t_cmem (field_address t_dctx (DOT _customMem) q) *
   field_at Ews t_dctx (DOT _fParams) (fh_val fh_zero) q * dctx_fields_nofp q * dctx_pad q).
Proof.
  intros Hmc.
  assert (Hfc: field_compatible t_dctx nil q).
  { apply malloc_compatible_field_compatible; [|reflexivity|reflexivity].
    change (sizeof (tarray tuchar (sizeof t_dctx))) with (sizeof t_dctx) in Hmc. exact Hmc. }
  assert (Hfa: field_compatible (tarray tuchar (sizeof t_dctx)) nil q).
  { apply malloc_compatible_field_compatible; [exact Hmc|reflexivity|reflexivity]. }
  apply andp_right; [apply prop_right; exact Hfc|].
  change (sizeof t_dctx) with 95976 in *. unfold tarray in *.
  rewrite (split3_data_at_Tarray_tuchar Ews 95976 29936 29984) by (try rewrite Zlength_Zrepeat; lia).
  rewrite !sublist_Zrepeat by lia.
  rewrite !field_address0_offset by (apply field_compatible0_cons; split; [lia | exact Hfa]).
  change (29984 - 29936) with 48. change (95976 - 29984) with 65992. change (29936 - 0) with 29936.
  sep_apply (fp_zero q Hfc).
  change (nested_field_offset (Tarray tuchar 95976 noattr) (SUB 29984)) with 29984.
  assert (Hfc2: field_compatible (Tarray tuchar 65992 noattr) nil (offset_val 29984 q)).
  { destruct Hfa as (Hp & Hl & Hsz & Hal & _). destruct q as [| | | | |b i]; try contradiction.
    unfold size_compatible in Hsz. simpl sizeof in Hsz. pose proof (Ptrofs.unsigned_range i).
    split3; [exact I | reflexivity | ]. split3; [ | | simpl; auto].
    - simpl. unfold Ptrofs.add. rewrite (Ptrofs.unsigned_repr 29984) by rep_lia.
      rewrite Ptrofs.unsigned_repr by rep_lia. simpl sizeof. try rewrite Z.max_r by lia. lia.
    - constructor. intros. apply align_compatible_rec_by_value with Mint8unsigned; [reflexivity | apply Z.divide_1_l]. }
  rewrite (split3_data_at_Tarray_tuchar Ews 65992 396 65964) by (try rewrite Zlength_Zrepeat; lia).
  rewrite !sublist_Zrepeat by lia.
  rewrite !field_address0_offset by (apply field_compatible0_cons; split; [lia | exact Hfc2]).
  rewrite !offset_offset_val. simpl Z.add. simpl Z.mul. simpl Z.sub.
  assert (Hlit: forall n o, n = 65568 -> o = 30380 ->
    data_at Ews (Tarray tuchar n noattr) (Zrepeat (Vint Int.zero) n) (offset_val o q) |-- lit_extra_at q lxb_zero).
  { intros n o -> ->. unfold lit_extra_at. apply andp_right.
    - apply prop_right. split.
      { unfold lxb_zero. apply Zlength_repeat. unfold LITEXTRA_N, WILDCOPY_OVERLENGTH. lia. }
      unfold lxb_zero, bytes_ok. apply Forall_forall; intros x Hx.
      apply repeat_spec in Hx. subst x. unfold is_byte. lia.
    - replace (zbytes lxb_zero) with (Zrepeat (Vint Int.zero) 65568)
        by (unfold lxb_zero, Zrepeat; rewrite map_repeat; change LITEXTRA_N with 65568; reflexivity).
      rewrite field_at_data_at, field_address_offset by (apply fc_dctx; auto; vm_compute; tauto).
      apply derives_refl. }
  change (sizeof (Tarray tuchar 95976 noattr)) with 95976 in Hmc.
  destruct q as [| | | | |b i]; try contradiction Hmc. destruct Hmc as [_ Hb].
  assert (Hlo1: forall n, n = 29936 -> memory_block Ews n (Vptr b i) |-- mbs Ews dctx_tiles_lo1 (Vptr b i)).
  { intros n ->. rewrite <- (mb_consec Ews dctx_tiles_lo1 0 29936 b i dctx_tiles_lo1_consec) by lia.
    rewrite Z.sub_0_r, isptr_offset_val_zero by auto. apply derives_refl. }
  assert (Hlo2: forall n o, n = 396 -> o = 29984 ->
    memory_block Ews n (offset_val o (Vptr b i)) |-- mbs Ews dctx_tiles_lo2 (Vptr b i)).
  { intros n o -> ->. rewrite <- (mb_consec Ews dctx_tiles_lo2 29984 30380 b i dctx_tiles_lo2_consec) by lia.
    apply derives_refl. }
  assert (Hhi: forall n o, n = 28 -> o = 95948 ->
    memory_block Ews n (offset_val o (Vptr b i)) |-- mbs Ews dctx_tiles_hi (Vptr b i)).
  { intros n o -> ->. rewrite <- (mb_consec Ews dctx_tiles_hi 95948 95976 b i dctx_tiles_hi_consec) by lia.
    apply derives_refl. }
  eapply derives_trans; [apply sepcon_derives; [apply derives_refl |
    apply sepcon_derives;
    [eapply derives_trans; [apply data_at_memory_block | apply Hlo1; reflexivity]
    | apply sepcon_derives; [apply sepcon_derives;
      [eapply derives_trans; [apply data_at_memory_block | apply Hlo2; reflexivity]
      | apply Hlit; reflexivity]
      | eapply derives_trans; [apply data_at_memory_block | apply Hhi; reflexivity]]]] |].
  sep_apply (dctx_nofp_mbs _ Hfc). cancel.
Qed.

(* a context zstd calloc'd (contract patch item 17): sizeof t_dctx zero bytes split into the fields; the
   zeroed litExtraBuffer holds the zero bytes (lit_extra_at, lxb_zero), the zeroed fParams the zero header *)
Lemma dctx_calloc_split (q: val) : malloc_compatible (sizeof (tarray tuchar (sizeof t_dctx))) q ->
  data_at Ews (tarray tuchar (sizeof t_dctx)) (Zrepeat (Vint Int.zero) (sizeof t_dctx)) q |--
  !! field_compatible t_dctx nil q &&
  (dctx_token q * data_at_ Ews t_cmem (field_address t_dctx (DOT _customMem) q) *
   field_at Ews t_dctx (DOT _fParams) (fh_val fh_zero) q * dctx_fields_nofp q * dctx_pad q).
Proof.
  intros Hmc. sep_apply (dctx_calloc_split' q Hmc). Intros.
  apply andp_right; [apply prop_right; assumption|].
  unfold dctx_token. rewrite !sepcon_andp_prop'. apply andp_right; [apply prop_right; assumption|].
  rewrite emp_sepcon. apply derives_refl.
Qed.

(* the allocator's group of a context: its customMem field, the token of its block, the allocator's state *)
Lemma mgroup_fold (am: option cmem) (q: val) (h: Z) : cmem_ok am ->
  field_at Ews t_dctx (DOT _customMem) (cmem_v am) q * blk_tok am (tarray tuchar (sizeof t_dctx)) q * cm_have am h
  |-- mgroup am q h.
Proof. intros Hok. unfold mgroup. apply andp_right; [apply prop_right; exact Hok | apply derives_refl]. Qed.

(* the context's struct as the calloc'd byte array it is freed as *)
Lemma dctx_bytes (p: val) : field_compatible t_dctx nil p ->
  data_at_ Ews t_dctx p |-- data_at_ Ews (tarray tuchar (sizeof t_dctx)) p.
Proof.
  intros Hfc. rewrite !data_at__memory_block.
  change (sizeof (tarray tuchar (sizeof t_dctx))) with (sizeof t_dctx). entailer!.
  destruct Hfc as (Hp & _ & Hsz & _ & _). split3; auto. split; [simpl; auto | ]. split; [ | split; auto].
  unfold align_compatible. destruct p; try contradiction. constructor. intros.
  apply align_compatible_rec_by_value with Mint8unsigned; [reflexivity | apply Z.divide_1_l].
Qed.

Lemma cm_fold (q: val) (v: reptype t_cmem) :
  data_at Ews t_cmem v (field_address t_dctx (DOT _customMem) q) |-- field_at Ews t_dctx (DOT _customMem) v q.
Proof. rewrite field_at_data_at. apply derives_refl. Qed.

Lemma cm_unfold (q: val) (v: reptype t_cmem) :
  field_at Ews t_dctx (DOT _customMem) v q |-- data_at Ews t_cmem v (field_address t_dctx (DOT _customMem) q).
Proof. rewrite field_at_data_at. apply derives_refl. Qed.

Lemma ring_free (am: option cmem) (b: val) (n: Z) (c: list val) :
  ring_rep am b n c |--
  if eq_dec b nullval then emp else blk_tok am (tarray tuchar n) b * data_at_ Ews (tarray tuchar n) b.
Proof.
  unfold ring_rep. destruct (eq_dec b nullval); entailer!.
Qed.

(* xxh64_state is a data_at_ (as XxhLemmas.xxh64_state_data_at_) *)
Lemma xxh_st_data_at_: forall sh seed l p,
  xxh64_state sh seed l p |-- data_at_ sh t_xxh64_state p.
Proof.
  intros. unfold xxh64_state. Intros junk.
  assert_PROP (field_compatible t_xxh64_state [] p) as Hfc.
  { rewrite field_at_compatible'. entailer!.
    destruct H1 as [? [? [? [? [? ?]]]]]. repeat split; auto. }
  assert (data_at sh (tarray tuchar 32) (xxh_bytes (xxh_rest seed l) ++ junk)
            (field_address t_xxh64_state (DOT _mem64) p) |-- field_at_ sh t_xxh64_state (DOT _mem64) p).
  { rewrite field_at__memory_block. sep_apply (data_at_data_at_ sh (tarray tuchar 32)).
    rewrite data_at__memory_block. Intros. simpl sizeof. cancel. }
  sep_apply H1. clear H1.
  sep_apply (field_at_field_at_ sh t_xxh64_state (DOT _total_len)).
  sep_apply (field_at_field_at_ sh t_xxh64_state (DOT _v)).
  sep_apply (field_at_field_at_ sh t_xxh64_state (DOT _memsize)).
  unfold_data_at (data_at_ sh t_xxh64_state p). unfold field_at_. cancel.
Qed.

Lemma xxh_field_ (p: val) (x: option (list Z)) :
  xxh_field p x |-- field_at_ Ews t_dctx (DOT _xxhState) p.
Proof.
  destruct x as [l|]; simpl; [ | apply derives_refl].
  sep_apply (xxh_st_data_at_ Ews 0 l). rewrite field_at__data_at_. apply derives_refl.
Qed.


Section Life3.
Variables (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR: blrel).

Lemma life3_resetParameters:
  semax_body Vprog (FS3_G DENT TABS SR BR) f_ZSTD_DCtx_resetParameters ZSTD_DCtx_resetParameters_spec.
Proof.
  start_function. unfold params_, params0. Intros.
  forward. forward. forward. forward. forward. forward. forward.
  entailer!. unfold params0.
  change (Int.unsigned (Int.add (Int.shl (Int.repr 1) (Int.repr 27)) (Int.repr 1)))
    with ZSTD_MAXWINDOWSIZE_DEFAULT.
  cancel.
Qed.

(* the bytes the allocator of a fresh context has given out: the context only *)
Lemma sf_given_k03m (am: option cmem) : sf_given (c3_s (k03m am)) = dctx_size.
Proof. reflexivity. Qed.

Lemma life3_initDCtx_internal:
  semax_body Vprog (FS3_G DENT TABS SR BR) f_ZSTD_initDCtx_internal (ZSTD_initDCtx_internal_spec3 DENT TABS).
Proof.
  start_function. unfold dctx_fields_nofp. Intros.
  do 14 forward.
  forward_call p.
  { unfold params_. cancel. }
  entailer!.
  pose proof par_ok_dflt as HPD.
  (* the calloc'd litExtraBuffer holds zeros: the uninitialised tables of a fresh context *)
  unfold ctx_body3, sgroup. rewrite sf_given_k03m.
  unfold params0, fgroup3, cgroup3, dgroup, frame_fields, tabs_rep, tables_uninit, cfg_fmt, cfg_lit,
    xxh_field, local_rep, ring_rep, hset_rep, k03m, k03, c3_with_s, sf_with_mem, fs0, s0, df_none, cold01; simpl.
  entailer!; [constructor | unfold field_at_; cancel].
Qed.

Lemma ctx03_valid (gv: globals) (q: val) : ctx_rep3 DENT TABS gv q k03 |-- valid_pointer q.
Proof.
  unfold ctx_rep3, ctx_body3, fgroup3, k03; simpl tabs_rep. unfold tables_uninit. normalize.
  assert (V: field_at_ Ews t_dctx (DOT _LLTptr) q |-- valid_pointer q)
    by (apply field_at_valid_ptr0; auto; reflexivity).
  apply (derives_trans _ (field_at_ Ews t_dctx (DOT _LLTptr) q * TT)); [cancel | ].
  apply sepcon_valid_pointer1. exact V.
Qed.

Lemma dc3_init (gv: globals) (q: val) :
  ctx_rep3 DENT TABS gv q k03 |-- DC3x DENT TABS SR BR gv q dctx_init && valid_pointer q.
Proof.
  apply andp_right; [ | apply ctx03_valid].
  unfold DC3x, DC3_of. Exists k03. apply andp_right; [ | apply derives_refl].
  apply prop_right. split; [ | split; [ | split]].
  - unfold base_rel3, set_cur_ok; simpl. repeat split; auto; try discriminate.
    + left. unfold dict_rel3_of, dctx_init, df_none; simpl. auto.
    + exists 0. split; [reflexivity | rep_lia].
  - simpl. intros H; congruence.
  - simpl. intros ba H; discriminate.
  - (* a fresh context is clean: the exact relation holds of no call *)
    intros _ _ _. exact (sr_ex_clean SR (c3_s k03) (c3_fs k03) eq_refl eq_refl eq_refl eq_refl eq_refl).
Qed.

Lemma life3_createDCtx:
  semax_body Vprog (FS3_G DENT TABS SR BR) f_ZSTD_createDCtx (ZSTD_createDCtx_spec (DC3x DENT TABS SR BR)).
Proof.
  start_function.
  forward_loop (PROP () LOCAL (gvars gv) SEP (mem_mgr gv; zstd_globals gv))
    break: (PROP () LOCAL (gvars gv) SEP (mem_mgr gv; zstd_globals gv));
    [entailer! | forward; entailer! | ].
  unfold zstd_globals. Intros.
  forward_call (gv, Ers, gv _ZSTD_defaultCMem, @None cmem).
  { unfold cm_have; cancel. }
  Intros q.
  forward.
  Exists q. entailer!.
  unfold zstd_globals. destruct (eq_dec q nullval); [unfold cm_have; cancel | ].
  rewrite k03m_none. sep_apply dc3_init. cancel.
Qed.

Lemma life3_createDStream:
  semax_body Vprog (FS3_G DENT TABS SR BR) f_ZSTD_createDStream (ZSTD_createDStream_spec (DC3x DENT TABS SR BR)).
Proof.
  start_function.
  forward_loop (PROP () LOCAL (gvars gv) SEP (mem_mgr gv; zstd_globals gv))
    break: (PROP () LOCAL (gvars gv) SEP (mem_mgr gv; zstd_globals gv));
    [entailer! | forward; entailer! | ].
  unfold zstd_globals. Intros.
  forward_call (gv, Ers, gv _ZSTD_defaultCMem, @None cmem).
  { unfold cm_have; cancel. }
  Intros q.
  forward.
  Exists q. entailer!.
  unfold zstd_globals. destruct (eq_dec q nullval); [unfold cm_have; cancel | ].
  rewrite k03m_none. sep_apply dc3_init. cancel.
Qed.

Lemma life3_freeDStream:
  semax_body Vprog (FS3_G DENT TABS SR BR) f_ZSTD_freeDStream (ZSTD_freeDStream_spec (DC3x DENT TABS SR BR)).
Proof.
  start_function.
  forward_call (gv, p, ost).
  forward.
Qed.

(* the functions of a context's own allocator are pointers *)
Lemma cm_have_ptrs (m: cmem) (h: Z) :
  cm_have (Some m) h |-- !! (isptr (cm_alloc m) /\ isptr (cm_free m)).
Proof.
  unfold cm_have, cm_funs.
  sep_apply (func_ptr'_isptr cm_alloc_spec (cm_alloc m)). sep_apply (func_ptr'_isptr cm_free_spec (cm_free m)).
  entailer!.
Qed.

Lemma cm_have_valid (m: cmem) (h: Z) :
  cm_have (Some m) h |-- valid_pointer (cm_alloc m) && valid_pointer (cm_free m).
Proof.
  unfold cm_have, cm_funs. apply andp_right.
  - apply sepcon_valid_pointer1. apply sepcon_valid_pointer1. apply func_ptr'_valid_pointer.
  - apply sepcon_valid_pointer1. apply sepcon_valid_pointer2. apply func_ptr'_valid_pointer.
Qed.

Lemma life3_createDCtx_internal:
  semax_body Vprog (FS3_G DENT TABS SR BR) f_ZSTD_createDCtx_internal (ZSTD_createDCtx_internal_spec3 DENT TABS).
Proof.
  start_function.
  match goal with H: cmem_ok am |- _ => rename H into Hok end.
  match goal with H: cm_room am 0 dctx_size |- _ => rename H into Hroom end.
  (* the test of customAlloc and customFree: both NULL (the default allocator) or both functions *)
  assert (Hcm: exists ca cf co: val, cmem_v am = (ca, (cf, co)) /\ is_pointer_or_null ca /\ is_pointer_or_null cf)
    by (destruct am as [m|]; [exists (cm_alloc m), (cm_free m), (cm_opaque m); split; [reflexivity | destruct Hok as (? & ? & ?); split; assumption]
                             | exists nullval, nullval, nullval; split; [reflexivity | split; simpl; auto]]).
  destruct Hcm as (ca & cf & co & Ecm & Hca & Hcf).
  rewrite Ecm.
  assert_PROP (am <> None -> isptr ca /\ isptr cf) as Hpt.
  { destruct am as [m|]; [| entailer!; congruence].
    unfold cmem_v, cmem_val in Ecm. inversion Ecm; subst.
    sep_apply (cm_have_ptrs m 0). entailer!. }
  forward. forward.
  forward_if (PROP () LOCAL (temp _customMem pm; gvars gv)
    SEP (mem_mgr gv; data_at shm t_cmem (ca, (cf, co)) pm; cm_have am 0)).
  { destruct am as [m|].
    2: inversion Ecm; subst. 2: entailer!. 2: apply denote_tc_test_eq_split; apply valid_pointer_null.
    unfold cmem_v, cmem_val in Ecm. inversion Ecm; subst.
    apply andp_right; apply denote_tc_test_eq_split; try (apply valid_pointer_zero64; reflexivity);
      (apply (derives_trans _ (cm_have (Some m) 0 * TT)); [cancel | apply sepcon_valid_pointer1;
       eapply derives_trans; [apply (cm_have_valid m 0)
                             | first [apply andp_left1; apply derives_refl | apply andp_left2; apply derives_refl]]]). }
  { destruct am as [m|]; [destruct (Hpt ltac:(discriminate)) as [Ha Hf]; destruct ca; try contradiction;
                           destruct cf; try contradiction | inversion Ecm; subst]; simpl in *; inv H. }
  { forward. entailer!. }
  rewrite <- Ecm.
  forward_call (gv, sizeof t_dctx, shm, pm, am, 0).
  Intros q.
  destruct (eq_dec q nullval) as [Hq | Hq].
  { subst q. forward_if.
    - forward. Exists nullval. entailer!. rewrite if_true by auto. apply derives_refl.
    - exfalso. match goal with Hx: ?a <> ?a |- _ => apply Hx; reflexivity end. }
  Intros.
  match goal with H: _ -> malloc_compatible _ q |- _ => specialize (H Hq); rename H into Hmc end.
  sep_apply (dctx_calloc_split q Hmc). Intros.
  match goal with H: field_compatible t_dctx nil q |- _ => rename H into Hfc end.
  forward_if.
  { apply denote_tc_test_eq_split; [ | apply valid_pointer_null].
    apply derives_trans with (field_at_ Ews t_dctx (DOT _LLTptr) q * TT); [unfold dctx_fields_nofp; cancel | ].
    apply sepcon_valid_pointer1. apply field_at_valid_ptr0; auto; reflexivity. }
  { contradiction. }
  Intros.
  assert (Hfcm: field_compatible t_dctx (DOT _customMem) q)
    by (apply fc_dctx; auto; vm_compute; tauto).
  forward_call (Ews, field_address t_dctx (DOT _customMem) q, shm, pm, am).
  sep_apply (cm_fold q (cmem_v am)).
  replace (0 + sizeof t_dctx) with dctx_size by reflexivity.
  sep_apply (mgroup_fold am q dctx_size Hok).
  forward_call (gv, q, am).
  forward.
  Exists q. entailer!.
  rewrite if_false by auto. unfold ctx_rep3, dctx_token. entailer!.
Qed.

(* the tables in any state cover the uninitialised tables, litExtraBuffer holding some bytes *)
Lemma tabs_rep_any (gv: globals) (p: val) (t: tabs3) :
  TABS_OK TABS -> tabs_rep TABS gv p t |-- EX lxb: list Z, tables_uninit p lxb.
Proof.
  intros HT. destruct t as [lxb | ox ts]; simpl; [Exists lxb; apply derives_refl |].
  Exists (ts_lxb ts). apply HT.
Qed.

Lemma ctx_body3_valid (gv: globals) (p: val) (k: cst3) :
  TABS_OK TABS -> ctx_body3 DENT TABS gv p k |-- valid_pointer p.
Proof.
  intros HT. unfold ctx_body3, fgroup3. normalize.
  assert (V: field_at_ Ews t_dctx (DOT _LLTptr) p |-- valid_pointer p)
    by (apply field_at_valid_ptr0; auto; reflexivity).
  sep_apply (tabs_rep_any gv p (c3_tabs k) HT). Intros lxb. unfold tables_uninit.
  apply (derives_trans _ (field_at_ Ews t_dctx (DOT _LLTptr) p * TT)); [cancel | ].
  apply sepcon_valid_pointer1. exact V.
Qed.

(* the context's fields at the end of ZSTD_freeDCtx, all uninitialised (three groups) *)
Lemma ff3_frame (gv: globals) (p: val) (fs: fstate) (t: tabs3) (f ign bmax multi: Z) (sp: val) : TABS_OK TABS ->
  cfg_fmt p f * cfg_lit p * frame_fields p fs * tabs_rep TABS gv p t *
  field_at Ews t_dctx (DOT _forceIgnoreChecksum) (Vint (Int.repr ign)) p *
  field_at Ews t_dctx (DOT _maxBlockSizeParam) (Vint (Int.repr bmax)) p *
  field_at Ews t_dctx (DOT _refMultipleDDicts) (Vint (Int.repr multi)) p *
  field_at Ews t_dctx (DOT _ddictSet) sp p
  |-- field_at_ Ews t_dctx (DOT _previousDstEnd) p *
  field_at_ Ews t_dctx (DOT _gpDictCopy) p *
  field_at_ Ews t_dctx (DOT _prefixStart) p *
  field_at_ Ews t_dctx (DOT _virtualStart) p *
  field_at_ Ews t_dctx (DOT _dictEnd) p *
  field_at_ Ews t_dctx (DOT _expected) p *
  field_at_ Ews t_dctx (DOT _fParams) p *
  field_at_ Ews t_dctx (DOT _processedCSize) p *
  field_at_ Ews t_dctx (DOT _decodedSize) p *
  field_at_ Ews t_dctx (DOT _bType) p *
  field_at_ Ews t_dctx (DOT _stage) p *
  field_at_ Ews t_dctx (DOT _headerSize) p *
  field_at_ Ews t_dctx (DOT _validateChecksum) p *
  field_at_ Ews t_dctx (DOT _rleSize) p *
  field_at_ Ews t_dctx (DOT _isFrameDecompression) p *
  field_at_ Ews t_dctx (DOT _dictID) p *
  field_at_ Ews t_dctx (DOT _ddictIsCold) p *
  field_at_ Ews t_dctx (DOT _format) p *
  field_at_ Ews t_dctx (DOT _disableHufAsm) p *
  field_at_ Ews t_dctx (DOT _forceIgnoreChecksum) p *
  field_at_ Ews t_dctx (DOT _maxBlockSizeParam) p *
  field_at_ Ews t_dctx (DOT _refMultipleDDicts) p *
  field_at_ Ews t_dctx (DOT _ddictSet) p *
  field_at_ Ews t_dctx (DOT _xxhState) p * (EX lxb: list Z, tables_uninit p lxb).
Proof.
  intros HT.
  sep_apply (tabs_rep_any gv p t HT). Intros lxb. Exists lxb.
  unfold frame_fields, cfg_fmt, cfg_lit.
  sep_apply (xxh_field_ p (fs_xxh fs)).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _previousDstEnd)).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _gpDictCopy)).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _prefixStart)).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _virtualStart)).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _dictEnd)).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _expected)).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _fParams)).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _processedCSize)).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _decodedSize)).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _bType)).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _stage)).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _headerSize)).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _validateChecksum)).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _rleSize)).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _isFrameDecompression)).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _dictID)).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _ddictIsCold)).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _format)).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _disableHufAsm)).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _forceIgnoreChecksum)).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _maxBlockSizeParam)).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _refMultipleDDicts)).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _ddictSet)).
  cancel.
Qed.

Lemma ff3_misc (gv: globals) (p: val) (stable: bool) (wmax: Z) (v: reptype t_cmem) :
  dgroup DENT gv p df_none *
  data_at Ews t_cmem v (field_address t_dctx (DOT _customMem) p) *
  field_at Ews t_dctx (DOT _staticSize) (Vlong (Int64.repr 0)) p *
  field_at Ews t_dctx (DOT _maxWindowSize) (Vlong (Int64.repr wmax)) p *
  field_at Ews t_dctx (DOT _outBufferMode) (Vint (Int.repr (if stable then 1 else 0))) p
  |-- field_at_ Ews t_dctx (DOT _customMem) p *
  field_at_ Ews t_dctx (DOT _staticSize) p *
  field_at_ Ews t_dctx (DOT _maxWindowSize) p *
  field_at_ Ews t_dctx (DOT _outBufferMode) p *
  field_at_ Ews t_dctx (DOT _ddictLocal) p *
  field_at_ Ews t_dctx (DOT _ddict) p *
  field_at_ Ews t_dctx (DOT _dictUses) p.
Proof.
  sep_apply (cm_fold p v).
  unfold dgroup, local_rep. unfold df_none; cbn [df_local df_ddict df_uses df_lx].
  rewrite if_true by auto.
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _customMem)).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _staticSize)).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _maxWindowSize)).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _outBufferMode)).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _ddictLocal)).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _ddict)).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _dictUses)).
  cancel.
Qed.

Lemma ff_stream (p: val) (s: sfields) :
  field_at Ews t_dctx (DOT _streamStage) (Vint (Int.repr (sf_stage s))) p *
  field_at Ews t_dctx (DOT _inBuff) (Vlong (Int64.repr (Int.signed (Int.repr 0)))) p *
  field_at Ews t_dctx (DOT _inBuffSize) (Vlong (Int64.repr (sf_inSize s))) p *
  field_at Ews t_dctx (DOT _inPos) (sf_inPos s) p *
  field_at Ews t_dctx (DOT _outBuff) (sf_outBuff s) p *
  field_at Ews t_dctx (DOT _outBuffSize) (Vlong (Int64.repr (sf_outSize s))) p *
  field_at Ews t_dctx (DOT _outStart) (sf_outStart s) p *
  field_at Ews t_dctx (DOT _outEnd) (sf_outEnd s) p *
  field_at Ews t_dctx (DOT _lhSize) (sf_lhSize s) p *
  field_at Ews t_dctx (DOT _hostageByte) (sf_hostage s) p *
  field_at Ews t_dctx (DOT _noForwardProgress) (Vint (Int.repr (sf_nfp s))) p *
  field_at Ews t_dctx (DOT _expectedOutBuffer) (sf_expOut s) p *
  field_at Ews t_dctx (DOT _headerBuffer) (sf_hbuf s) p *
  field_at Ews t_dctx (DOT _oversizedDuration) (Vlong (Int64.repr (sf_over s))) p
  |-- field_at_ Ews t_dctx (DOT _streamStage) p *
  field_at_ Ews t_dctx (DOT _inBuff) p *
  field_at_ Ews t_dctx (DOT _inBuffSize) p *
  field_at_ Ews t_dctx (DOT _inPos) p *
  field_at_ Ews t_dctx (DOT _outBuff) p *
  field_at_ Ews t_dctx (DOT _outBuffSize) p *
  field_at_ Ews t_dctx (DOT _outStart) p *
  field_at_ Ews t_dctx (DOT _outEnd) p *
  field_at_ Ews t_dctx (DOT _lhSize) p *
  field_at_ Ews t_dctx (DOT _hostageByte) p *
  field_at_ Ews t_dctx (DOT _noForwardProgress) p *
  field_at_ Ews t_dctx (DOT _expectedOutBuffer) p *
  field_at_ Ews t_dctx (DOT _headerBuffer) p *
  field_at_ Ews t_dctx (DOT _oversizedDuration) p.
Proof.
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _streamStage)).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _inBuff)).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _inBuffSize)).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _inPos)).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _outBuff)).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _outBuffSize)).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _outStart)).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _outEnd)).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _lhSize)).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _hostageByte)).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _noForwardProgress)).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _expectedOutBuffer)).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _headerBuffer)).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _oversizedDuration)).
  cancel.
Qed.


Lemma free_fields3 (gv: globals) (p: val) (k: cst3) (sp: val) (v: reptype t_cmem) : TABS_OK TABS ->
  dctx_pad p * dgroup DENT gv p df_none *
  data_at Ews t_cmem v (field_address t_dctx (DOT _customMem) p) *
  cfg_fmt p (dp_fmt (c3_par k)) * cfg_lit p * frame_fields p (c3_fs k) * tabs_rep TABS gv p (c3_tabs k) *
  field_at Ews t_dctx (DOT _forceIgnoreChecksum) (Vint (Int.repr (dp_ignore (c3_par k)))) p *
  field_at Ews t_dctx (DOT _maxBlockSizeParam) (Vint (Int.repr (dp_bmax (c3_par k)))) p *
  field_at Ews t_dctx (DOT _refMultipleDDicts) (Vint (Int.repr (dp_multi (c3_par k)))) p *
  field_at Ews t_dctx (DOT _ddictSet) sp p *
  field_at Ews t_dctx (DOT _staticSize) (Vlong (Int64.repr 0)) p *
  field_at Ews t_dctx (DOT _maxWindowSize) (Vlong (Int64.repr (dp_wmax (c3_par k)))) p *
  field_at Ews t_dctx (DOT _outBufferMode) (Vint (Int.repr (if c3_stable k then 1 else 0))) p *
  field_at Ews t_dctx (DOT _streamStage) (Vint (Int.repr (sf_stage (c3_s k)))) p *
  field_at Ews t_dctx (DOT _inBuff) (Vlong (Int64.repr (Int.signed (Int.repr 0)))) p *
  field_at Ews t_dctx (DOT _inBuffSize) (Vlong (Int64.repr (sf_inSize (c3_s k)))) p *
  field_at Ews t_dctx (DOT _inPos) (sf_inPos (c3_s k)) p *
  field_at Ews t_dctx (DOT _outBuff) (sf_outBuff (c3_s k)) p *
  field_at Ews t_dctx (DOT _outBuffSize) (Vlong (Int64.repr (sf_outSize (c3_s k)))) p *
  field_at Ews t_dctx (DOT _outStart) (sf_outStart (c3_s k)) p *
  field_at Ews t_dctx (DOT _outEnd) (sf_outEnd (c3_s k)) p *
  field_at Ews t_dctx (DOT _lhSize) (sf_lhSize (c3_s k)) p *
  field_at Ews t_dctx (DOT _hostageByte) (sf_hostage (c3_s k)) p *
  field_at Ews t_dctx (DOT _noForwardProgress) (Vint (Int.repr (sf_nfp (c3_s k)))) p *
  field_at Ews t_dctx (DOT _expectedOutBuffer) (sf_expOut (c3_s k)) p *
  field_at Ews t_dctx (DOT _headerBuffer) (sf_hbuf (c3_s k)) p *
  field_at Ews t_dctx (DOT _oversizedDuration) (Vlong (Int64.repr (sf_over (c3_s k)))) p
  |-- dctx_fields_ p.
Proof.
  intros HT.
  sep_apply (ff3_frame gv p (c3_fs k) (c3_tabs k) (dp_fmt (c3_par k)) (dp_ignore (c3_par k)) (dp_bmax (c3_par k))
               (dp_multi (c3_par k)) sp HT).
  Intros lxb.
  sep_apply (ff3_misc gv p (c3_stable k) (dp_wmax (c3_par k)) v).
  sep_apply (ff_stream p (c3_s k)).
  unfold tables_uninit, dctx_fields_. cancel. unfold lit_extra_at. Intros. apply field_at_field_at_.
Qed.

Lemma hset_rep_vp (am: option cmem) (sp: val) (l: list (val * ddict_st)) (hb: Z) :
  hset_rep am sp l hb |-- valid_pointer sp.
Proof.
  unfold hset_rep. destruct (eq_dec sp nullval) as [E|E].
  - subst. Intros. apply valid_pointer_null.
  - Intros tp tbl. apply sepcon_valid_pointer1. apply sepcon_valid_pointer2.
    apply data_at_valid_ptr; [auto | simpl; lia].
Qed.

(* the set's bytes are not negative *)
Lemma hset_rep_hb (am: option cmem) (sp: val) (l: list (val * ddict_st)) (hb: Z) :
  hset_rep am sp l hb |-- !! (0 <= hb /\ (sp = nullval -> hb = 0)).
Proof.
  unfold hset_rep. destruct (eq_dec sp nullval) as [E|E].
  - entailer!.
  - Intros tp tbl. apply prop_right. split; [| contradiction].
    subst hb. unfold set_bytes. destruct am; [| lia]. pose proof (Zlength_nonneg tbl). simpl. lia.
Qed.

Lemma life3_freeDCtx: TABS_OK TABS -> DENT_OK DENT ->
  semax_body Vprog (FS3_G DENT TABS SR BR) f_ZSTD_freeDCtx (ZSTD_freeDCtx_spec (DC3x DENT TABS SR BR)).
Proof.
  intros HT HD. start_function.
  destruct ost as [st|].
  2: { subst p. forward_if.
       - forward. cancel.
       - contradiction H; reflexivity. }
  unfold DC3x, DC3_of. Intros k. unfold ctx_rep3, dctx_token. Intros.
  (* the context's allocator is the abstract one; besides the context and its stream buffer it gave out the local
     DDict's bytes (local_held) and the set's (hbs) *)
  assert (Hm: mem_rel3 st k)
    by (match goal with Hb: base_rel3 st k |- _ => exact (base_rel3_mem st k Hb) end).
  destruct Hm as (Hmem & Hroom & Hlm).
  match goal with H: field_compatible t_dctx nil p |- _ => rename H into Hfc0 end.
  assert (Hp: isptr p) by (destruct Hfc0; auto).
  forward_if (PROP () LOCAL (lvar _cMem t_cmem v_cMem; gvars gv; temp _dctx p)
    SEP (data_at_ Tsh t_cmem v_cMem; mem_mgr gv; zstd_globals gv; dctx_pad p; ctx_body3 DENT TABS gv p k)).
  { apply (derives_trans _ (ctx_body3 DENT TABS gv p k * TT)); [cancel | ].
    apply denote_tc_test_eq_split;
      [apply sepcon_valid_pointer1; apply ctx_body3_valid; auto | apply valid_pointer_zero64; reflexivity]. }
  { subst p; contradiction. }
  { forward. entailer!. }
  unfold ctx_body3, cgroup3, sgroup, mgroup. Intros.
  set (am := sf_mem (c3_s k)) in *.
  set (hbs := sf_held (c3_s k) - local_held (c3_dict k)) in *.
  assert_PROP (0 <= hbs /\ (c3_sp k = nullval -> hbs = 0)) as Hhbs
    by (sep_apply (hset_rep_hb am (c3_sp k) (c3_set k) hbs); entailer!).
  match goal with |- semax _ ?P _ _ => forward_loop P break: P end.
  { entailer!. }
  { forward. forward_if.
    - exfalso; match goal with H: (0 <> 0)%Z |- _ => apply H; reflexivity end.
    - forward. entailer!. }
  assert_PROP (field_compatible t_dctx (DOT _customMem) p) as Hfcm by entailer!.
  sep_apply (cm_unfold p (cmem_v am)).
  forward_call (Tsh, v_cMem, Ews, field_address t_dctx (DOT _customMem) p, am).
  assert (Eg: sf_given (c3_s k) = (dctx_size + hbs + sf_inSize (c3_s k) + sf_outSize (c3_s k)) + local_held (c3_dict k))
    by (unfold sf_given, hbs; lia).
  rewrite Eg.
  forward_call (gv, p, c3_dict k, am, dctx_size + hbs + sf_inSize (c3_s k) + sf_outSize (c3_s k)).
  { repeat match goal with |- _ /\ _ => split end; try exact Hlm; try assumption; rewrite ?dctx_size_eq; lia. }
  assert_PROP (is_pointer_or_null (sf_inBuff (c3_s k)) /\ (sf_inBuff (c3_s k) = nullval -> sf_inSize (c3_s k) + sf_outSize (c3_s k) = 0)) as Hib.
  { unfold ring_rep. destruct (eq_dec (sf_inBuff (c3_s k)) nullval) as [E|E]; [rewrite E; entailer! | ].
    Intros. entailer!. }
  destruct Hib as [Hib Hib0].
  forward.
  sep_apply (ring_free am (sf_inBuff (c3_s k)) (sf_inSize (c3_s k) + sf_outSize (c3_s k)) (sf_ring (c3_s k))).
  forward_call (gv, tarray tuchar (sf_inSize (c3_s k) + sf_outSize (c3_s k)), sf_inBuff (c3_s k), Tsh, v_cMem,
                am, dctx_size + hbs + sf_inSize (c3_s k) + sf_outSize (c3_s k)).
  { split.
    - intros _. unfold cm_held. destruct am; auto. simpl sizeof.
      rewrite Z.max_r by lia. rewrite dctx_size_eq. lia.
    - intros Nb _. match goal with Hx: sf_inBuff _ <> nullval -> 0 < _ |- _ => specialize (Hx Nb) end. simpl sizeof. rewrite Z.max_r by lia. lia. }
  replace (if eq_dec (sf_inBuff (c3_s k)) nullval then dctx_size + hbs + sf_inSize (c3_s k) + sf_outSize (c3_s k)
           else dctx_size + hbs + sf_inSize (c3_s k) + sf_outSize (c3_s k) -
                sizeof (tarray tuchar (sf_inSize (c3_s k) + sf_outSize (c3_s k)))) with (dctx_size + hbs).
  2: { destruct (eq_dec (sf_inBuff (c3_s k)) nullval) as [E|E]; [specialize (Hib0 E); lia |].
       simpl sizeof. rewrite Z.max_r by lia. lia. }
  forward.
  unfold fgroup3. Intros.
  assert_PROP (is_pointer_or_null (c3_sp k)) as Hspn.
  { unfold hset_rep. destruct (eq_dec (c3_sp k) nullval) as [E|E]; [rewrite E; entailer! | ].
    Intros tp tbl. entailer!. }
  forward.
  freeze FR := - (field_at _ _ (DOT _ddictSet) _ _) (hset_rep _ _ _ _) (data_at _ t_cmem3 _ v_cMem) (mem_mgr _)
                 (cm_have _ _).
  forward_if (PROP () LOCAL (lvar _cMem t_cmem v_cMem; gvars gv; temp _dctx p)
     SEP (FRZL FR; mem_mgr gv; data_at Tsh t_cmem3 (cmem_v am) v_cMem; field_at Ews t_dctx (DOT _ddictSet) nullval p;
          cm_have am dctx_size)).
  { apply (derives_trans _ (hset_rep (sf_mem (c3_s k)) (c3_sp k) (c3_set k) hbs * TT)); [cancel | ].
    apply denote_tc_test_eq_split;
      [apply sepcon_valid_pointer1; apply hset_rep_vp | apply valid_pointer_zero64; reflexivity]. }
  { match goal with H: isptr _ |- _ => change (isptr (c3_sp k)) in H; rename H into Hsp end.
    assert (Nsp: c3_sp k <> nullval) by (intro E; rewrite E in Hsp; contradiction).
    rewrite (hset_rep_at _ _ _ _ Nsp). Intros.
    forward.
    forward_call (gv, c3_sp k, c3_set k, Tsh, v_cMem, am, dctx_size + hbs, hbs).
    { rewrite if_false by auto. cancel. }
    { rewrite dctx_size_eq; lia. }
    forward. entailer!. rewrite if_false by auto. replace (dctx_size + hbs - hbs) with dctx_size by lia. cancel. }
  { match goal with H: _ = nullval |- _ => change (c3_sp k = nullval) in H; rename H into Esp end.
    unfold hset_rep. rewrite if_true by auto. Intros.
    forward. rewrite Esp. entailer!.
    match goal with H: sf_held _ - local_held _ = 0 |- _ => rewrite H, Z.add_0_r end. cancel. }
  thaw FR.
  sep_apply (free_fields3 gv p k nullval (cmem_v am) HT).
  sep_apply (dctx_merge p Hfc0).
  sep_apply (dctx_bytes p Hfc0).
  assert (FR2: blk_tok am (tarray tuchar (sizeof t_dctx)) p * data_at_ Ews (tarray tuchar (sizeof t_dctx)) p |--
              if eq_dec p nullval then emp
              else blk_tok am (tarray tuchar (sizeof t_dctx)) p * data_at_ Ews (tarray tuchar (sizeof t_dctx)) p)
    by (rewrite if_false by (intro E; subst; contradiction); apply derives_refl).
  sep_apply FR2.
  forward_call (gv, tarray tuchar (sizeof t_dctx), p, Tsh, v_cMem, am, dctx_size).
  { unfold cm_held. subst am. destruct (sf_mem (c3_s k)); [| exact I]. rewrite dctx_size_eq. simpl. lia. }
  rewrite if_false by (intro E; subst; contradiction).
  forward.
  replace (dctx_size - sizeof (tarray tuchar (sizeof t_dctx))) with 0 by reflexivity.
  sep_apply (data_at_data_at_ Tsh t_cmem3 (cmem_v (sf_mem (c3_s k))) v_cMem). unfold cm_back. rewrite <- Hmem.
  destruct (sf_mem (c3_s k)); simpl; cancel.
Qed.

Lemma ddict_rep_at_any3 (HD: DENT_OK DENT) gv x buf am : cm_same (dx_mem x) am ->
  ddict_rep_at DENT gv x buf |--
    ddict_any3 am (dx_q x) (if ddx_copied x then Zlength (dx_bytes x) else 0).
Proof.
  intros Hs.
  unfold ddict_rep_at, ddict_any3, ddict_failed3, ddict_struct, ddict_mem.
  rewrite (cmem_v_same _ _ Hs), !(blk_tok_same _ _ _ _ Hs).
  Intros.
  sep_apply (HD gv (dx_q x) (ddx_ent x)).
  Exists (Zlength (dx_bytes x)) (if ddx_copied x then buf else nullval).
  destruct (ddx_copied x) eqn:Hc.
  - match goal with H: isptr buf \/ _ |- _ => pose proof (ddx_buf_copied x buf Hc H) end.
    rewrite if_false by (intro Heq; subst buf; contradiction).
    entailer!.
    rewrite if_false by (intro Heq; subst buf; contradiction). cancel.
  - rewrite if_true by auto. entailer!.
Qed.

(* a leftover local DDict (no description: the default allocator's) *)
Lemma ddict_any_any3 (q: val) : ddict_any q |-- EX nb: Z, ddict_any3 None q nb.
Proof.
  unfold ddict_any, ddict_any3, ddict_failed, ddict_failed3. Intros n db.
  Exists (if eq_dec db nullval then 0 else n) n db.
  simpl blk_tok. entailer!.
Qed.

(* the local DDict as ZSTD_freeDDict frees it, through the context's allocator am: the bytes of am it holds besides
   its struct (local_held) *)
Lemma local_rep_any3 (HD: DENT_OK DENT) gv d am : local_mem am d ->
  local_rep DENT gv (df_local d) (df_lx d) |--
    EX nb: Z, !! (df_local d <> nullval -> am <> None -> 0 <= nb /\ local_held d = sizeof t_ddict + nb) &&
    (if eq_dec (df_local d) nullval then emp else ddict_any3 am (df_local d) nb).
Proof.
  intros Hl. unfold local_rep, local_held. destruct (eq_dec (df_local d) nullval) as [E|E].
  - Exists 0. entailer!.
  - specialize (Hl E). destruct (df_lx d) as [[x buf]|] eqn:Ex.
    + destruct Hl as [_ Hs]. specialize (Hs x buf eq_refl).
      Intros. rewrite <- H.
      sep_apply (ddict_rep_at_any3 HD gv x buf am Hs).
      Exists (if ddx_copied x then Zlength (dx_bytes x) else 0).
      apply andp_right; [| apply derives_refl]. apply prop_right.
      intros _ Ham. unfold ddx_held.
      destruct (dx_mem x) as [m|], am as [m'|]; simpl in Hs; try contradiction; try congruence.
      split; [destruct (ddx_copied x); [apply Zlength_nonneg | lia] | reflexivity].
    + destruct Hl as [Hn _]. assert (Ham: am = None) by (destruct am; [exfalso; apply Hn; congruence | auto]).
      subst am. sep_apply (ddict_any_any3 (df_local d)). Intros nb. Exists nb. entailer!.
Qed.

Lemma dgroup_fold3 gv p d :
  field_at Ews t_dctx (DOT _ddictLocal) (df_local d) p *
  field_at Ews t_dctx (DOT _ddict) (df_ddict d) p *
  field_at Ews t_dctx (DOT _dictUses) (Vint (Int.repr (df_uses d))) p *
  local_rep DENT gv (df_local d) (df_lx d) |-- dgroup DENT gv p d.
Proof. unfold dgroup. cancel. Qed.

Lemma life3_clearDict (HD: DENT_OK DENT) :
  semax_body Vprog (FS3_G DENT TABS SR BR) f_ZSTD_clearDict (ZSTD_clearDict_spec DENT).
Proof.
  start_function. unfold dgroup. Intros.
  sep_apply (local_rep_any3 HD gv d am H). Intros nb.
  assert_PROP (is_pointer_or_null (df_local d)).
  { destruct (eq_dec (df_local d) nullval) as [Hq | Hq]; [rewrite Hq; entailer! |].
    unfold ddict_any3, ddict_failed3. Intros nn db. entailer!. }
  forward.
  forward_call (gv, df_local d, am, hb + local_held d, nb).
  { match goal with Nq: df_local d <> nullval, Nam: am <> None |- _ =>
      destruct (H2 Nq Nam) as [Hn Hh]; lia end. }
  forward. forward. forward.
  unfold dgroup, local_rep, df_none; cbn [df_local df_ddict df_uses df_lx].
  rewrite (if_true (nullval = nullval)) by auto.
  entailer!.
  unfold local_held. destruct (eq_dec (df_local d) nullval) as [E|E]; [rewrite Z.add_0_r; apply derives_refl |].
  destruct am as [m|]; [| apply derives_refl].
  destruct (H2 E ltac:(discriminate)) as [_ Hh]. unfold local_held in Hh. rewrite if_false in Hh by auto.
  rewrite Hh. replace (hb + (sizeof t_ddict + nb) - (sizeof t_ddict + nb)) with hb by lia. apply derives_refl.
Qed.

Lemma life3_getDDict (HD: DENT_OK DENT) :
  semax_body Vprog (FS3_G DENT TABS SR BR) f_ZSTD_getDDict (ZSTD_getDDict_spec DENT).
Proof.
  start_function. unfold dgroup. Intros.
  forward.
  forward_switch'.
  - sep_apply (dgroup_fold3 gv p d).
    forward_call (gv, p, d, am, hb).
    forward.
    unfold getddict_res; rewrite E; simpl. entailer!.
    apply derives_refl.
  - assert (is_pointer_or_null (df_ddict d)) by (apply H0; lia).
    forward. forward.
    unfold getddict_res; rewrite E; simpl. entailer!.
    unfold dgroup; rewrite E; cancel.
  - assert (is_pointer_or_null (df_ddict d)) by (apply H0; lia).
    forward. forward. forward.
    unfold getddict_res; rewrite E; simpl. entailer!.
    unfold dgroup, df_set_uses, local_held; simpl. cancel.
  - exfalso. destruct H as [Hu | [Hu | Hu]]; rewrite Hu in *; contradiction.
Qed.

End Life3.

Lemma bodies_life3 :
  FS3_body (fun DENT TABS SR BR => ZSTD_DCtx_resetParameters_spec) /\
  FS3_body (fun DENT TABS SR BR => ZSTD_initDCtx_internal_spec3 DENT TABS) /\
  FS3_body (fun DENT TABS SR BR => ZSTD_createDCtx_internal_spec3 DENT TABS) /\
  FS3_body (fun DENT TABS SR BR => ZSTD_createDCtx_spec (DC3x DENT TABS SR BR)) /\
  FS3_body (fun DENT TABS SR BR => ZSTD_createDStream_spec (DC3x DENT TABS SR BR)) /\
  FS3_body (fun DENT TABS SR BR => ZSTD_freeDCtx_spec (DC3x DENT TABS SR BR)) /\
  FS3_body (fun DENT TABS SR BR => ZSTD_freeDStream_spec (DC3x DENT TABS SR BR)) /\
  FS3_body (fun DENT TABS SR BR => ZSTD_clearDict_spec DENT) /\
  FS3_body (fun DENT TABS SR BR => ZSTD_getDDict_spec DENT).
Proof.
  repeat split; intros DENT TABS SR BR HD HT.
  - exists f_ZSTD_DCtx_resetParameters; split; [reflexivity | split; [reflexivity | ]].
    apply life3_resetParameters.
  - exists f_ZSTD_initDCtx_internal; split; [reflexivity | split; [reflexivity | ]].
    apply life3_initDCtx_internal.
  - exists f_ZSTD_createDCtx_internal; split; [reflexivity | split; [reflexivity | ]].
    apply life3_createDCtx_internal.
  - exists f_ZSTD_createDCtx; split; [reflexivity | split; [reflexivity | ]].
    apply life3_createDCtx.
  - exists f_ZSTD_createDStream; split; [reflexivity | split; [reflexivity | ]].
    apply life3_createDStream.
  - exists f_ZSTD_freeDCtx; split; [reflexivity | split; [reflexivity | ]].
    apply life3_freeDCtx; auto.
  - exists f_ZSTD_freeDStream; split; [reflexivity | split; [reflexivity | ]].
    apply life3_freeDStream.
  - exists f_ZSTD_clearDict; split; [reflexivity | split; [reflexivity | ]].
    apply life3_clearDict; auto.
  - exists f_ZSTD_getDDict; split; [reflexivity | split; [reflexivity | ]].
    apply life3_getDDict; auto.
Qed.

End CM_body3_life_1.
