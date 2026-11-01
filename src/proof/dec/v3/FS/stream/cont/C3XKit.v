(* ZSTD_decompressContinue exactly: the model's state read off the frame fields (S3XRel.drel), the sanity check and
   ZSTD_checkContinuity on both sides, and cont_exact from the cases' claims (cont_exact1). *)
Require Import Zstd.proof.dec.v3.FS.stream.S3Specs.
Require Import Zstd.proof.dec.v3.FS.stream.cont.C3Base.
Require Import Zstd.proof.dec.v3.FS.stream.cont.C3XModel.
Require Import Zstd.proof.dec.v3.FS.stream.cont.C3XDefs.
Require Import Zstd.proof.model.ExStream.
Local Open Scope Z_scope.

(* ---------- pointers into the ring ---------- *)

Lemma off_inj b ofs x y :
  0 <= x <= Ptrofs.max_unsigned -> 0 <= y <= Ptrofs.max_unsigned ->
  offset_val x (Vptr b ofs) = offset_val y (Vptr b ofs) -> x = y.
Proof.
  intros Hx Hy E. simpl in E.
  assert (E1: Ptrofs.add ofs (Ptrofs.repr x) = Ptrofs.add ofs (Ptrofs.repr y)) by congruence.
  assert (E2: Ptrofs.repr x = Ptrofs.repr y).
  { rewrite <- (Ptrofs.add_zero_l (Ptrofs.repr x)), <- (Ptrofs.add_zero_l (Ptrofs.repr y)).
    rewrite <- (Ptrofs.add_neg_zero ofs), (Ptrofs.add_commut ofs (Ptrofs.neg ofs)), !Ptrofs.add_assoc, E1.
    reflexivity. }
  apply (f_equal Ptrofs.unsigned) in E2. rewrite !Ptrofs.unsigned_repr in E2 by lia. exact E2.
Qed.

Lemma off_congr b ofs x y : x mod Ptrofs.modulus = y mod Ptrofs.modulus ->
  offset_val x (Vptr b ofs) = offset_val y (Vptr b ofs).
Proof.
  intros E. simpl. f_equal. f_equal. apply Ptrofs.eqm_samerepr. unfold Ptrofs.eqm.
  apply Zbits.eqmod_trans with (x mod Ptrofs.modulus); [apply Zbits.eqmod_mod; reflexivity |].
  rewrite E. apply Zbits.eqmod_sym, Zbits.eqmod_mod. reflexivity.
Qed.

Lemma ring_ptr_off b ofs o y :
  (forall x, o = Some x -> 0 <= x <= Ptrofs.max_unsigned) -> 0 <= y <= Ptrofs.max_unsigned ->
  ring_ptr (Vptr b ofs) o = offset_val y (Vptr b ofs) -> o = Some y.
Proof.
  intros Ho Hy E. destruct o as [x |]; cbn in E; [| discriminate].
  f_equal. apply (off_inj b ofs); auto.
Qed.

Lemma ring_ptr_null b ofs o : ring_ptr (Vptr b ofs) o = nullval -> o = None.
Proof. destruct o; cbn; [discriminate | auto]. Qed.

(* ---------- the model's fields from drel ---------- *)

Lemma vint_small_inj a b : 0 <= a <= Int.max_unsigned -> 0 <= b <= Int.max_unsigned ->
  Vint (Int.repr a) = Vint (Int.repr b) -> a = b.
Proof.
  intros Ha Hb E. assert (E': Int.repr a = Int.repr b) by congruence.
  apply (f_equal Int.unsigned) in E'. rewrite !Int.unsigned_repr in E' by lia. exact E'.
Qed.

Lemma vlong_inj a b : 0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Vlong (Int64.repr a) = Vlong (Int64.repr b) -> a = b.
Proof.
  intros Ha Hb E. assert (E': Int64.repr a = Int64.repr b) by congruence.
  apply (f_equal Int64.unsigned) in E'. rewrite !Int64.unsigned_repr in E' by lia. exact E'.
Qed.

Lemma drel_stage fh d ob fs ts st :
  drel fh d ob fs ts -> fs_stage fs = Vint (Int.repr st) -> 0 <= st <= 7 -> d_stage XS d = st.
Proof.
  intros H E Hs. destruct H as (_ & _ & _ & _ & Hd & _ & _ & _ & _ & _ & _ & _ & Es & _).
  rewrite Es in E. apply vint_small_inj in E; unfold DS_skipFrame in Hd; rep_lia.
Qed.

Lemma drel_expected fh d ob fs ts e :
  drel fh d ob fs ts -> fs_expected fs = Vlong (Int64.repr e) -> 0 <= e <= Int64.max_unsigned -> d_expected XS d = e.
Proof.
  intros H E He. destruct H as (_ & _ & _ & _ & _ & Hd & _ & _ & _ & _ & _ & _ & _ & Ee & _).
  rewrite Ee in E. unfold vlong in E. apply vlong_inj in E; auto.
Qed.

(* the header zstd keeps: the model's fields as zstd's (fh_val, FSSpecs3) *)
Lemma drel_fh fh d ob fs ts h bsm :
  drel fh d ob fs ts -> fs_fParams fs = fh_val (fh_adj h bsm) ->
  0 <= fh_contentSize h <= Int64.max_unsigned -> 0 <= bsm <= Int.max_unsigned ->
  0 <= fh_checksumFlag h <= Int.max_unsigned ->
  fh_contentSize fh = fh_contentSize h /\ fh_blockSizeMax fh = bsm /\ fh_checksumFlag fh = fh_checksumFlag h.
Proof.
  intros H E Hc Hb Hk. destruct H as (Ep & Rc & Rb & Rk & _). rewrite Ep in E. unfold fh_val, fh_adj in E.
  cbn in E. inversion E as [[E1 E2 E3 E4 E5 E6 E7]].
  split; [| split].
  - apply (vlong_inj _ _ Rc Hc). congruence.
  - apply (vint_small_inj _ _ Rb Hb). congruence.
  - apply (vint_small_inj _ _ Rk Hk). congruence.
Qed.

Ltac drel_d H :=
  let Ep := fresh "Ep" in let Rc := fresh "Rc" in let Rb := fresh "Rb" in let Rk := fresh "Rk" in
  let Rst := fresh "Rst" in let Rex := fresh "Rex" in let Rbt := fresh "Rbt" in let Rrl := fresh "Rrl" in
  let Roff := fresh "Roff" in let Rxh := fresh "Rxh" in let Rts := fresh "Rts" in let Rfd := fresh "Rfd" in
  let Est := fresh "Est" in let Eex := fresh "Eex" in let Hblk := fresh "Hblk" in let Hptr := fresh "Hptr" in
  destruct H as (Ep & Rc & Rb & Rk & Rst & Rex & Rbt & Rrl & Roff & Rxh & Rts & Rfd & Est & Eex & Hblk & Hptr).

(* ---------- ZSTD_checkContinuity on both sides ---------- *)

Lemma offset_val_neg0 v : isptr v -> offset_val (- 0) v = v.
Proof. intros Hv. rewrite Z.opp_0. apply isptr_offset_val_zero, Hv. Qed.

Lemma vptr_diff_congr b ofs p q :
  vptr_diff (offset_val p (Vptr b ofs)) (offset_val q (Vptr b ofs)) mod Ptrofs.modulus = (p - q) mod Ptrofs.modulus.
Proof.
  cbn [offset_val vptr_diff]. rewrite !Ptrofs.add_unsigned, !Ptrofs.unsigned_repr_eq.
  rewrite Zminus_mod, !Zmod_mod, <- Zminus_mod.
  replace (Ptrofs.unsigned ofs + p mod Ptrofs.modulus - (Ptrofs.unsigned ofs + q mod Ptrofs.modulus))
    with (p mod Ptrofs.modulus - q mod Ptrofs.modulus) by lia.
  rewrite <- Zminus_mod. reflexivity.
Qed.

Lemma drel_continuity fh d b ofs fs ts dst cap :
  drel fh d (Vptr b ofs) fs ts -> 0 <= dst <= Ptrofs.max_unsigned ->
  (0 < cap -> DS_decodeBlockHeader <= d_stage XS d <= DS_checkChecksum) ->
  drel fh (d_continuity XS d dst cap) (Vptr b ofs) (continuity fs (offset_val dst (Vptr b ofs)) cap) ts.
Proof.
  intros H Hdst Hst. unfold d_continuity, continuity, cont_moves.
  destruct (Z.ltb_spec 0 cap) as [Hc | Hc].
  2: { replace (cap >? 0) with false by lia. cbn [andb]. exact H. }
  replace (cap >? 0) with true by lia. cbn [andb].
  specialize (Hst Hc). pose proof H as H0. drel_d H0.
  destruct (Hptr Hst) as (Dd & Bo & Vc & Xx & Ppe & Pps & Pde & Pvs & Pgp).
  rewrite Pgp. replace (veqb (Vint (Int.repr 0)) (Vint (Int.repr 0))) with true by (symmetry; apply veqb_refl).
  cbn [negb orb].
  assert (Hd': forall d', d_stage XS d' = d_stage XS d -> d_expected XS d' = d_expected XS d ->
            d_btype XS d' = d_btype XS d -> d_rle XS d' = d_rle XS d -> d_out XS d' = d_out XS d ->
            d_check XS d' = d_check XS d -> d_ent XS d' = d_ent XS d ->
            (forall x, d_prev XS d' = Some x \/ d_pfx XS d' = Some x \/ d_ds XS d' = Some x \/ d_de XS d' = Some x ->
               0 <= x <= Ptrofs.max_unsigned) ->
            forall fs', fs_fParams fs' = fs_fParams fs -> fs_isFrameDecompression fs' = fs_isFrameDecompression fs ->
            fs_stage fs' = fs_stage fs -> fs_expected fs' = fs_expected fs -> fs_bType fs' = fs_bType fs ->
            fs_rleSize fs' = fs_rleSize fs -> fs_decodedSize fs' = fs_decodedSize fs ->
            fs_validateChecksum fs' = fs_validateChecksum fs -> fs_xxh fs' = fs_xxh fs ->
            fs_gpDictCopy fs' = Vint (Int.repr 0) ->
            fs_previousDstEnd fs' = ring_ptr (Vptr b ofs) (d_prev XS d') ->
            fs_prefixStart fs' = ring_ptr (Vptr b ofs) (d_pfx XS d') ->
            fs_dictEnd fs' = ring_ptr (Vptr b ofs) (d_de XS d') -> fs_virtualStart fs' = vstart_of (Vptr b ofs) d' ->
            drel fh d' (Vptr b ofs) fs' ts).
  { intros d' S1 S2 S3 S4 S5 S6 S7 S8 fs' F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 F14.
    unfold drel. rewrite S1, S2, S3, S4, S5, S6, S7, F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, F11, F12, F13, F14.
    repeat (split; [assumption |]); intros; repeat split; auto. }
  destruct (d_prev XS d) as [p |] eqn:Ep'.
  - assert (Hp: 0 <= p <= Ptrofs.max_unsigned) by (apply Roff; left; reflexivity).
    rewrite Ppe. cbn [ring_ptr].
    destruct (Z.eqb_spec p dst) as [<- | Ne].
    + rewrite veqb_refl. cbn [negb andb]. exact H.
    + replace (veqb (offset_val dst (Vptr b ofs)) (offset_val p (Vptr b ofs))) with false.
      2: { unfold veqb. destruct (Val.eq _ _) as [E | _]; auto. exfalso. apply Ne. symmetry.
           apply (off_inj b ofs); auto. }
      cbn [negb andb].
      apply Hd'; try reflexivity.
      * intros x [E | [E | [E | E]]];
          [inversion E; subst; lia | inversion E; subst; lia | apply Roff; right; left; exact E |
           inversion E; subst; lia].
      * unfold vstart_of. cbn [d_pfx d_ds d_de].
        replace (veqb (offset_val p (Vptr b ofs)) nullval) with false by reflexivity.
        rewrite Pps. destruct (d_pfx XS d) as [q |] eqn:Eq; cbn [ring_ptr].
        -- rewrite offset_offset_val. apply off_congr.
           rewrite Z.add_opp_r, (Zminus_mod dst), vptr_diff_congr, <- Zminus_mod.
           reflexivity.
        -- cbn [vptr_diff]. rewrite offset_val_neg0 by exact I. reflexivity.
  - rewrite Ppe. cbn [ring_ptr].
    replace (veqb (offset_val dst (Vptr b ofs)) nullval) with false by reflexivity. cbn [negb andb].
    apply Hd'; try reflexivity.
    * intros x [E | [E | [E | E]]]; try discriminate; inversion E; subst; lia.
    * rewrite veqb_refl. rewrite offset_val_neg0 by exact I. reflexivity.
Qed.

(* ---------- the sanity check: the unit zstd checks is the model's ---------- *)

Lemma drel_next_in fh d ob fs ts st e n :
  drel fh d ob fs ts -> fs_stage fs = Vint (Int.repr st) -> 0 <= st <= 7 ->
  fs_expected fs = Vlong (Int64.repr e) -> 0 <= e <= Int64.max_unsigned ->
  next_size st (match fs_bType fs with Vint b => Int.signed b | _ => 0 end) e n = n -> d_next_in XS d n = n.
Proof.
  intros H Es Hs Ee He Hn. etransitivity; [| exact Hn].
  pose proof (drel_stage _ _ _ _ _ _ H Es Hs) as Ds. pose proof (drel_expected _ _ _ _ _ _ H Ee He) as De.
  drel_d H. unfold d_next_in, next_size. rewrite Ds, De.
  unfold ds_decompressBlock, ds_decompressLastBlock, DS_decompressBlock, DS_decompressLastBlock in *.
  destruct (Z.eqb_spec st 3) as [E3 | N3]; [| destruct (Z.eqb_spec st 4) as [E4 | N4]]; cbn [orb andb];
    try reflexivity.
  - destruct (Hblk ltac:(left; lia)) as [Bt _]. rewrite Bt, Int.signed_repr by rep_lia. reflexivity.
  - destruct (Hblk ltac:(right; lia)) as [Bt _]. rewrite Bt, Int.signed_repr by rep_lia. reflexivity.
Qed.

(* ---------- cont_exact from the cases ---------- *)

Lemma cont_exact_of fs fs1 ts o u n r oc' fs' tabs' b ofs st e :
  fs1 = continuity fs (offset_val (oa_d o) (oa_base o)) (oa_cap o) ->
  oa_base o = Vptr b ofs -> 0 <= oa_d o <= Ptrofs.max_unsigned ->
  fs_stage fs = Vint (Int.repr st) -> (st = 2 \/ st = 3 \/ st = 4 \/ st = 5 \/ st = 7) ->
  (st = 7 -> oa_cap o = 0) ->
  fs_expected fs = Vlong (Int64.repr e) -> 0 <= e <= Int64.max_unsigned ->
  next_size st (match fs_bType fs with Vint b => Int.signed b | _ => 0 end) e n = n ->
  cont_exact1 fs1 ts o u n r oc' fs' tabs' -> cont_exact fs ts o u n r oc' fs' tabs'.
Proof.
  intros E1 Eb Hd Es Hst Hsk Ee He Hn HX fh d0 mem Hdr Hm Hbm Hne.
  rewrite d_continue_body.
  rewrite (drel_next_in _ _ _ _ _ _ _ _ Hdr Es ltac:(lia) Ee He Hn), Z.eqb_refl. cbn [negb].
  assert (Ds: d_stage XS d0 = st) by (apply (drel_stage _ _ _ _ _ _ Hdr Es); lia).
  apply HX; auto.
  - subst fs1. rewrite Eb in *. apply drel_continuity; auto.
    intros Hc. unfold DS_decodeBlockHeader, DS_checkChecksum. destruct Hst as [-> | [-> | [-> | [-> | ->]]]]; lia.
  - unfold noext0, d_continuity. destruct (Z.ltb_spec 0 (oa_cap o)) as [Hc | Hc].
    + intros _ _ Hc0. lia.
    + replace (oa_cap o >? 0) with false by lia. exact Hne.
Qed.
