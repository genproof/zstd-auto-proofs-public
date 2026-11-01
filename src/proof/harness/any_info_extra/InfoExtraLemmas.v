(* The checks of harness/any_info_extra.c as facts about the frame-header model (model/Frame.v, model/Params.v),
   on ANY bytes. *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Params.
Require Import Zstd.proof.harness.any_info.InfoLemmas.
Local Open Scope bool_scope.

Lemma IE_Zlength_nonneg {A} (l: list A) : 0 <= Zlength l.
Proof. rewrite Zlength_correct. lia. Qed.

Lemma IE_Zlength_app {A} (a b: list A) : Zlength (a ++ b) = Zlength a + Zlength b.
Proof. rewrite !Zlength_correct, app_length. lia. Qed.

Lemma IE_le_value_bound l : bytes_ok l -> 0 <= le_value l < 256 ^ Zlength l.
Proof.
  induction l as [|b l IH]; intros H; [simpl; lia|].
  inversion H as [|? ? Hb Hl]; subst. specialize (IH Hl). red in Hb.
  assert (0 <= Zlength l) by (rewrite Zlength_correct; lia). rewrite Zlength_cons, Z.pow_succ_r by lia. cbn [le_value]. lia.
Qed.

Lemma IE_bytes_firstn n l : bytes_ok l -> bytes_ok (firstn n l).
Proof. unfold bytes_ok. revert l; induction n as [|n IH]; intros l H; destruct l; simpl; try constructor; inversion H; subst; auto. Qed.

Lemma IE_bytes_skipn n l : bytes_ok l -> bytes_ok (skipn n l).
Proof. unfold bytes_ok. revert l; induction n as [|n IH]; intros l H; destruct l; simpl; auto; inversion H; subst; auto. Qed.

Lemma IE_le_field_bound l i k : bytes_ok l -> 0 <= k -> 0 <= le_field l i k < 256 ^ k.
Proof.
  intros H Hk. unfold le_field, slice.
  assert (Hs: bytes_ok (firstn (Z.to_nat k) (skipn (Z.to_nat i) l))).
  { apply IE_bytes_firstn, IE_bytes_skipn, H. }
  pose proof (IE_le_value_bound _ Hs).
  assert (Zlength (firstn (Z.to_nat k) (skipn (Z.to_nat i) l)) <= k).
  { rewrite Zlength_correct, firstn_length. lia. }
  pose proof (Z.pow_le_mono_r 256 _ _ ltac:(lia) H1). split; [lia|].
  eapply Z.lt_le_trans; [apply H0 | lia].
Qed.

Lemma IE_byte_at_bound l i : bytes_ok l -> 0 <= byte_at l i < 256.
Proof.
  intros H. unfold byte_at. revert l H. induction (Z.to_nat i) as [|n IH]; intros l H;
    destruct l as [|b l]; simpl; try lia; inversion H; subst; auto.
Qed.

(* getFrameContentSize: a 64-bit value *)
Lemma IE_fcs_range s : bytes_ok s -> 0 <= frame_content_size s <= 2 ^ 64 - 1.
Proof.
  intros Hs. unfold frame_content_size, get_frame_header. cbv zeta.
  repeat match goal with |- context [if ?b then _ else _] =>
    lazymatch b with context [if _ then _ else _] => fail | _ => destruct b end end;
    cbn [fh_frameType fh_contentSize].
  all: unfold ZSTD_CONTENTSIZE_ERROR, ZSTD_CONTENTSIZE_UNKNOWN; try lia.
  all: repeat match goal with |- context [if ?b then _ else _] => destruct b end; try lia.
  all: repeat match goal with |- context [le_field ?s ?i ?k] =>
         let H := fresh in pose proof (IE_le_field_bound s i k Hs ltac:(lia)) as H; cbv [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul] in H;
         let x := fresh in set (x := le_field s i k) in *; clearbody x end.
  all: repeat match goal with |- context [byte_at ?s ?i] =>
         let H := fresh in pose proof (IE_byte_at_bound s i Hs) as H; let x := fresh in set (x := byte_at s i) in *; clearbody x end.
  all: lia.
Qed.

(* ZSTD_getDecompressedSize: the blending of getFrameContentSize's two special values *)
Lemma IE_ds s : bytes_ok s ->
  (if frame_content_size s >=? ZSTD_CONTENTSIZE_ERROR then 0 else frame_content_size s) =
  (if (frame_content_size s =? ZSTD_CONTENTSIZE_UNKNOWN) || (frame_content_size s =? ZSTD_CONTENTSIZE_ERROR)
   then 0 else frame_content_size s).
Proof.
  intros Hs. pose proof (IE_fcs_range s Hs). unfold ZSTD_CONTENTSIZE_ERROR, ZSTD_CONTENTSIZE_UNKNOWN in *.
  destruct (Z.geb_spec (frame_content_size s) (2 ^ 64 - 2));
  destruct (Z.eqb_spec (frame_content_size s) (2 ^ 64 - 1));
  destruct (Z.eqb_spec (frame_content_size s) (2 ^ 64 - 2)); simpl; lia.
Qed.

(* a complete header has at least 5 bytes *)
Lemma IE_gfh_ok s h : get_frame_header s = FH_ok h -> 5 <= fh_headerSize h <= Zlength s.
Proof.
  intros H. pose proof (IL_gfh_ok s h H) as Hle. split; [|lia].
  revert H. unfold get_frame_header. intros H.
  destruct (Zlength s <? 5) eqn:E5.
  - destruct (Zlength s >? 0); [destruct (_ && _)|]; discriminate.
  - destruct (negb (le_field s 0 4 =? ZSTD_MAGICNUMBER)).
    + destruct (is_skippable_magic (le_field s 0 4)); [|discriminate].
      destruct (Zlength s <? ZSTD_SKIPPABLEHEADERSIZE); [discriminate|].
      IL_some H. simpl. unfold ZSTD_SKIPPABLEHEADERSIZE. lia.
    + pose proof (IL_fhd_header_size_range (byte_at s 4)).
      destruct (Zlength s <? fhd_header_size (byte_at s 4)); [discriminate|].
      destruct (negb (Z.land (byte_at s 4) 8 =? 0)); [discriminate|].
      destruct (_ && _); [discriminate|].
      IL_some H. simpl. lia.
Qed.

(* ZSTD_getFrameHeader_advanced(ZSTD_f_zstd1_magicless) returns 0: the header is within src *)
Lemma IE_gfhm_ok s h : get_frame_header_m true s = FH_ok h -> 1 <= fh_headerSize h <= Zlength s.
Proof.
  unfold get_frame_header_m. cbn [negb]. intros H.
  destruct (Zlength s <? 1); [discriminate|].
  destruct (get_frame_header (magic_bytes ++ s)) as [|k|h'] eqn:E; try discriminate.
  IL_some H. apply IE_gfh_ok in E. rewrite IE_Zlength_app in E.
  change (Zlength magic_bytes) with 4 in E. simpl. lia.
Qed.

(* ... returns k > 0 (not an error): more than srcSize bytes wanted *)
Lemma IE_gfhm_more s k : get_frame_header_m true s = FH_more k -> Zlength s < k <= 18.
Proof.
  unfold get_frame_header_m. cbn [negb]. intros H.
  destruct (Zlength s <? 1) eqn:E1.
  - apply Z.ltb_lt in E1. IL_some H. pose proof (IE_Zlength_nonneg s). lia.
  - destruct (get_frame_header (magic_bytes ++ s)) as [|k'|h'] eqn:E; try discriminate.
    IL_some H. apply IL_gfh_more in E. rewrite IE_Zlength_app in E.
    change (Zlength magic_bytes) with 4 in E. lia.
Qed.

(* with ZSTD_f_zstd1 it is ZSTD_getFrameHeader *)
Lemma IE_gfhm_zstd1 s : get_frame_header_m false s = get_frame_header s.
Proof. reflexivity. Qed.
