(* FS3 bodies, dfh3: ZSTD_decodeFrameHeader with the format, the checksum policy and the DDict selection.
   (obligation FSOblig3.FS3_body: for ANY DENT/TABS of B, ANY SR, ANY BR).
   Port of v2 body_FS_blocks.v body_decodeFrameHeader. *)
Require Import Zstd.proof.dec.v3.FS.FSOblig3.
Local Open Scope logic.
Local Open Scope Z_scope.

Ltac fif_set id v :=
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp id v :: Q) (SEPx R))) end.

Ltac head_dw0 c :=
  lazymatch c with Sloop _ Sbreak => idtac | Ssequence ?a _ => head_dw0 a end.

Ltac dw0 :=
  match goal with |- semax _ ?P ?c _ => head_dw0 c;
    first [ forward_loop P break: P; [entailer! | forward; entailer! | ]
          | forward_loop P break: P;
            [entailer! | forward_if P; [exfalso; lia | forward; entailer! | forward; entailer!] | ] ] end.

Section CM_body3_dfh_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.




(* ---------- ranges of the parsed frame header ---------- *)

Lemma land_le_l (x m : Z) : 0 <= x -> Z.land x m <= x.
Proof.
  intros Hx.
  assert (Z.ldiff (Z.land x m) x = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.ldiff_spec, Z.land_spec, Z.bits_0.
    destruct (Z.testbit x i); simpl; auto. apply andb_false_r. }
  apply Z.ldiff_le in H; lia.
Qed.

Lemma lev_range (l: list Z) : bytes_ok l -> 0 <= le_value l < 2 ^ (8 * Zlength l).
Proof.
  intros H. induction H; cbn [le_value].
  - rewrite Zlength_nil. simpl. lia.
  - unfold is_byte in H. rewrite Zlength_cons. replace (8 * Z.succ (Zlength l)) with (8 + 8 * Zlength l) by lia.
    rewrite Z.pow_add_r by (pose proof (Zlength_nonneg l); lia).
    change (2^8) with 256. lia.
Qed.

Lemma lef_range (l: list Z) i k : bytes_ok l -> 0 <= k -> 0 <= le_field l i k < 2 ^ (8 * k).
Proof.
  intros H Hk. unfold le_field, slice.
  assert (Hb: bytes_ok (firstn (Z.to_nat k) (skipn (Z.to_nat i) l))).
  { unfold bytes_ok in *. apply Forall_firstn, Forall_skipn; auto. }
  pose proof (lev_range _ Hb).
  assert (Zlength (firstn (Z.to_nat k) (skipn (Z.to_nat i) l)) <= k).
  { rewrite Zlength_correct, firstn_length. lia. }
  assert (2 ^ (8 * Zlength (firstn (Z.to_nat k) (skipn (Z.to_nat i) l))) <= 2 ^ (8 * k)).
  { apply Z.pow_le_mono_r; [lia |]. pose proof (Zlength_nonneg (firstn (Z.to_nat k) (skipn (Z.to_nat i) l))). lia. }
  lia.
Qed.

Lemma land1_range x : 0 <= Z.land x 1 <= 1.
Proof.
  assert (Z.land x 1 = x mod 2) as -> by (apply (Z.land_ones x 1); lia).
  pose proof (Z.mod_pos_bound x 2). lia.
Qed.

Lemma nth4_nonneg n : 0 <= nth n [0; 1; 2; 4] 0 <= 4.
Proof. destruct n as [|[|[|[|n]]]]; simpl; try lia; destruct n; simpl; lia. Qed.

Lemma nth8_nonneg n : 0 <= nth n [0; 2; 4; 8] 0 <= 8.
Proof. destruct n as [|[|[|[|n]]]]; simpl; try lia; destruct n; simpl; lia. Qed.

Lemma fhd_size_pos fhd : fhd_header_size fhd > 0.
Proof.
  unfold fhd_header_size.
  pose proof (land1_range (Z.shiftr fhd 5)).
  pose proof (nth4_nonneg (Z.to_nat (Z.land fhd 3))). pose proof (nth8_nonneg (Z.to_nat (Z.shiftr fhd 6))).
  destruct (andb _ _); lia.
Qed.

Lemma gfh_more (s: list Z) k : get_frame_header s = FH_more k -> k > 0.
Proof.
  unfold get_frame_header. intros H.
  repeat match type of H with
  | context [if ?c then _ else _] => destruct c
  end; inv H; try (unfold ZSTD_SKIPPABLEHEADERSIZE; lia).
  apply fhd_size_pos.
Qed.

Lemma fhd_size_le fhd : fhd_header_size fhd <= 19.
Proof.
  unfold fhd_header_size.
  pose proof (land1_range (Z.shiftr fhd 5)).
  pose proof (nth4_nonneg (Z.to_nat (Z.land fhd 3))). pose proof (nth8_nonneg (Z.to_nat (Z.shiftr fhd 6))).
  destruct (andb _ _); lia.
Qed.

Lemma gfh_more_le (s: list Z) k : get_frame_header s = FH_more k -> k <= 19.
Proof.
  unfold get_frame_header. intros H.
  repeat match type of H with
  | context [if ?c then _ else _] => destruct c
  end; inv H; try (unfold ZSTD_SKIPPABLEHEADERSIZE; lia).
  apply fhd_size_le.
Qed.

Ltac dec_err_c := unfold dec_err; split; [reflexivity | split; compute; congruence].

Lemma gfh_ok (s: list Z) h :
  bytes_ok s -> get_frame_header s = FH_ok h ->
  0 <= fh_dictID h <= Int.max_unsigned /\ (fh_checksumFlag h = 0 \/ fh_checksumFlag h = 1).
Proof.
  intros Hb H. unfold get_frame_header in H. cbv zeta in H.
  repeat match type of H with context [if ?c then _ else _] => destruct c eqn:? end; inv H; simpl.
  1: { split; [| left; auto].
    assert (R := lef_range s 0 4 Hb). specialize (R ltac:(lia)).
    unfold is_skippable_magic in *. apply Z.eqb_eq in Heqb1.
    assert (L := land_le_l (le_field s 0 4) ZSTD_MAGIC_SKIPPABLE_MASK). specialize (L ltac:(lia)).
    unfold ZSTD_MAGIC_SKIPPABLE_START in *. rewrite Heqb1 in *. rep_lia. }
  all: match goal with |- 0 <= le_field ?l ?pos ?k <= _ /\ _ =>
      assert (Hk: 0 <= k <= 4) by (destruct (Z.to_nat (Z.land (byte_at l 4) 3)) as [|[|[|[|n]]]]; try destruct n; lia);
      assert (R := lef_range l pos k Hb); specialize (R ltac:(lia));
      assert (2 ^ (8 * k) <= 2 ^ 32) by (apply Z.pow_le_mono_r; lia) end.
    all: split; [rep_lia |]; pose proof (land1_range (Z.shiftr (byte_at s 4) 2)); lia.
Qed.

(* ---------- pointer comparisons (ZSTD_checkContinuity) ---------- *)

Lemma xxh64_state_lf sh seed l p :
  xxh64_state sh seed l p |-- !! (field_compatible t_xxh64_state [] p /\ bytes_ok l).
Proof.
  unfold xxh64_state. Intros junk.
  rewrite field_at_compatible'. Intros. apply prop_right. split; auto.
  destruct H1 as [? [? [? [? [? ?]]]]]. repeat split; auto.
Qed.

Lemma xxh64_state_to_data_at_ sh seed l p :
  xxh64_state sh seed l p |-- data_at_ sh t_xxh64_state p.
Proof.
  sep_apply (xxh64_state_lf sh seed l p). Intros. unfold xxh64_state. Intros junk.
  assert (data_at sh (tarray tuchar 32) (xxh_bytes (xxh_rest seed l) ++ junk)
            (field_address t_xxh64_state (DOT _mem64) p) |-- field_at_ sh t_xxh64_state (DOT _mem64) p).
  { rewrite field_at__memory_block. sep_apply (data_at_data_at_ sh (tarray tuchar 32)).
    rewrite data_at__memory_block. Intros. simpl sizeof. cancel. }
  sep_apply H2. clear H2.
  sep_apply (field_at_field_at_ sh t_xxh64_state (DOT _total_len)).
  sep_apply (field_at_field_at_ sh t_xxh64_state (DOT _v)).
  sep_apply (field_at_field_at_ sh t_xxh64_state (DOT _memsize)).
  unfold_data_at (data_at_ sh t_xxh64_state p). unfold field_at_. cancel.
Qed.

Lemma xxh_field_data_at_ p x :
  xxh_field p x |-- data_at_ Ews t_xxh64_state (field_address t_dctx (DOT _xxhState) p).
Proof.
  destruct x; simpl.
  - apply xxh64_state_to_data_at_.
  - rewrite field_at__data_at_. apply derives_refl.
Qed.

Lemma fhd_size_ge5 fhd : 5 <= fhd_header_size fhd.
Proof.
  unfold fhd_header_size.
  pose proof (land1_range (Z.shiftr fhd 5)).
  pose proof (nth4_nonneg (Z.to_nat (Z.land fhd 3))). pose proof (nth8_nonneg (Z.to_nat (Z.shiftr fhd 6))).
  destruct (andb _ _); lia.
Qed.

Lemma gfh_more_ge5 (s: list Z) k : get_frame_header s = FH_more k -> 5 <= k.
Proof.
  unfold get_frame_header. intros H.
  repeat match type of H with
  | context [if ?c then _ else _] => destruct c
  end; inv H; try (unfold ZSTD_SKIPPABLEHEADERSIZE; lia).
  apply fhd_size_ge5.
Qed.

(* the format-aware reading (model/Params.get_frame_header_m) *)
Lemma gfhm_more mg (s: list Z) k : get_frame_header_m mg s = FH_more k -> 0 < k <= 19.
Proof.
  unfold get_frame_header_m. destruct mg; cbn [negb]; intros H.
  - destruct (Zlength s <? 1); [inv H; lia |].
    destruct (get_frame_header (magic_bytes ++ s)) eqn:E; inv H.
    pose proof (gfh_more_ge5 _ _ E). pose proof (gfh_more_le _ _ E). lia.
  - pose proof (gfh_more _ _ H). pose proof (gfh_more_le _ _ H). lia.
Qed.

Lemma gfhm_ok mg (s: list Z) h :
  bytes_ok s -> get_frame_header_m mg s = FH_ok h ->
  0 <= fh_dictID h <= Int.max_unsigned /\ (fh_checksumFlag h = 0 \/ fh_checksumFlag h = 1).
Proof.
  unfold get_frame_header_m. destruct mg; cbn [negb]; intros Hb H.
  - destruct (Zlength s <? 1); [discriminate |].
    destruct (get_frame_header (magic_bytes ++ s)) eqn:E; inv H.
    assert (Hb': bytes_ok (magic_bytes ++ s)).
    { unfold bytes_ok in *. apply Forall_app; split; auto. vm_compute. repeat constructor; vm_compute; congruence. }
    exact (gfh_ok _ _ Hb' E).
  - exact (gfh_ok _ _ Hb H).
Qed.

Ltac fs_cbn := cbn [fs_previousDstEnd fs_gpDictCopy fs_prefixStart fs_virtualStart fs_dictEnd fs_expected fs_fParams fs_processedCSize fs_decodedSize fs_bType fs_stage fs_xxh fs_headerSize fs_validateChecksum fs_rleSize fs_isFrameDecompression fs_dictID fs_ddictIsCold fsu_fParams fsu_dictID fsu_processedCSize fsu_xxh fsu_validateChecksum].

Ltac int_contra := match goal with Hx: Int.repr ?a = Int.zero |- _ =>
  apply (f_equal Int.unsigned) in Hx; rewrite Int.unsigned_repr in Hx by rep_lia;
  change (Int.unsigned Int.zero) with 0 in Hx; lia end.

(* hides an equation of a variable from VST's subst *)
Definition dfh_hide (P: Prop) : Prop := P.
Lemma dfh_hide_intro (P: Prop) : P -> dfh_hide P.
Proof. auto. Qed.

Lemma sel_on_null pr : sel_on pr nullval = false.
Proof. unfold sel_on, veqb. destruct (Val.eq nullval nullval); [|contradiction]. apply andb_false_r. Qed.

Lemma frame_fields_dictID_same p fs : frame_fields p (fsu_dictID fs (fs_dictID fs)) = frame_fields p fs.
Proof. reflexivity. Qed.

(* L3: what an error (FH_err) of ZSTD_getFrameHeader_advanced leaves in the struct (C: the prefix errors return
   before the memset (struct untouched: v0), the later ones after it and before dictID is written (dictID 0));
   API v3.4's fh_post_m says it, fh_err_gap_ok below. *)
Definition fh_err_gap : Prop :=
  forall mg s r v0 v, fh_post_m mg s r v0 v -> get_frame_header_m mg s = FH_err ->
    v = v0 \/ fp_dictID v = Vint (Int.repr 0).

Lemma fp_dictID_zero : fp_dictID (fh_val fh_zero) = Vint (Int.repr 0).
Proof. reflexivity. Qed.

Local Open Scope logic.

Section Bodies.
Variables (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR: blrel).
Hypothesis Hgap: fh_err_gap.

Lemma body_decodeFrameHeader3 : body_ok (FS3_G DENT TABS SR BR) (ZSTD_decodeFrameHeader_spec3 DENT).
Proof.
  exists f_ZSTD_decodeFrameHeader; split; [reflexivity | split; [reflexivity | ]].
  start_function.
  rename H4 into Hsm.
  unfold fcore3, cfg_fmt, cfg_lit, frame_fields. Intros.
  rename H4 into Hpar. rename H3 into Hcur.
  pose proof H as Hw. destruct Hw as (Hr & Hoff & Hoffn & HN32 & HcN & _ & Hbytes & Hsub).
  forward.
  assert_PROP (field_compatible t_dctx (DOT _fParams) p) as Fp by entailer!.
  rewrite (field_at_data_at Ews t_dctx (DOT _fParams) (fs_fParams fs) p).
  change (nested_field_type t_dctx (DOT _fParams)) with t_fh.
  forward_call (gv, Ews, field_address t_dctx (DOT _fParams) p, fs_fParams fs, sh, base, N, c, off, s, dp_fmt pr).
  { destruct Hpar as [? _]; auto. }
  Intros vr. destruct vr as [r v]. simpl fst in *; simpl snd in *.
  match goal with Hp: fh_post_m _ _ _ _ _ |- _ => rename Hp into Hfh end.
  pose proof (Hgap _ _ _ _ _ Hfh) as Hg.
  change (fmt_mg (dp_fmt pr)) with (md_magicless (dmode_of pr)) in Hfh.
  change (data_at Ews t_fh v (field_address t_dctx (DOT _fParams) p)) with
    (data_at Ews (nested_field_type t_dctx (DOT _fParams)) v (field_address t_dctx (DOT _fParams) p)).
  rewrite <- field_at_data_at.
  forward.
  forward_call r.
  forward_if.
  - forward.
    assert (Herr: is_error_code r = true) by (destruct (is_error_code r); auto; contradiction).
    assert (dfh_post3 (dmode_of pr) (sel_on pr sp) d l tbl fs did pcs s r (fsu_fParams fs v) d).
    { unfold dfh_post3, fh_post_m in *. destruct (get_frame_header_m _ s) eqn:Eg.
      - split; [apply Hfh | split; [auto | exists v; split; [reflexivity | apply Hg; reflexivity]]].
      - exfalso. destruct Hfh as [-> _]. apply gfhm_more in Eg.
        unfold is_error_code in Herr. apply Z.ltb_lt in Herr. lia.
      - destruct Hfh; subst. discriminate. }
    Exists r (fsu_fParams fs v) d. unfold fcore3, cfg_fmt, cfg_lit, frame_fields. simpl. entailer!.
  - assert (Hne: is_error_code r = false)
      by (destruct (is_error_code r); auto; apply (f_equal Int.unsigned) in H4; vm_compute in H4; discriminate).
    destruct (zlt 0 r) as [Hpos | Hz].
    + match goal with |- semax _ ?P _ _ => forward_loop P break: (PROP (False) LOCAL () SEP ()) end.
      * entailer!.
      * forward_if.
        -- repeat dw0. forward.
           assert (dfh_post3 (dmode_of pr) (sel_on pr sp) d l tbl fs did pcs s (Int64.unsigned (Int64.repr (-72)))
                     (fsu_fParams fs v) d).
           { unfold dfh_post3, fh_post_m in *. destruct (get_frame_header_m _ s).
             - split; [dec_err_c | split; [auto | exists v; split; [reflexivity | apply Hg; reflexivity]]].
             - split; [dec_err_c | split; [auto | exists v; split; [reflexivity |]]].
               destruct Hfh as [_ ->]. destruct (_ <? _); [left; reflexivity | right; apply fp_dictID_zero].
             - exfalso. destruct Hfh. lia. }
           Exists (Int64.unsigned (Int64.repr (-72))) (fsu_fParams fs v) d.
           rewrite Int64.repr_unsigned. unfold fcore3, cfg_fmt, cfg_lit, frame_fields. simpl. entailer!.
        -- rewrite !Int64.unsigned_repr in * by rep_lia. lia.
    + assert (r = 0) by lia. subst r. clear Hz.
      unfold fh_post_m in Hfh. destruct (get_frame_header_m _ s) as [| k | h] eqn:Eg.
      { exfalso. destruct Hfh as [He _]. unfold dec_err in He. destruct He as [He _]. discriminate. }
      { apply gfhm_more in Eg. destruct Hfh. lia. }
      destruct Hfh as [_ ->]. destruct (gfhm_ok _ s h Hbytes Eg) as [Hdid Hcs].
      match goal with |- semax _ ?P _ _ =>
        forward_loop P break: P; [entailer! | forward_if P; [ | forward; entailer! | forward; entailer!] | ] end.
      { rewrite !Int64.unsigned_repr in * by rep_lia. lia. }
      forward.
      fif_set _t'3 (Vint (Int.repr (if sel_on pr sp then 1 else 0))).
      { assert (Hm: dp_multi pr = 1).
        { destruct Hpar as (_ & _ & _ & _ & [Hm|Hm]); rewrite Hm in H5; auto.
          apply (f_equal Int.unsigned) in H5. rewrite !Int.unsigned_repr in H5 by rep_lia. lia. }
        destruct (eq_dec sp nullval) as [Hsp|Hsp].
        - subst sp. forward. forward. entailer!.
          unfold sel_on, veqb. destruct (Val.eq nullval nullval); [|contradiction]. rewrite andb_false_r. reflexivity.
        - assert (Es: sel_on pr sp = true)
            by (unfold sel_on; rewrite Hm; simpl; unfold veqb; destruct (Val.eq sp nullval); [contradiction|reflexivity]).
          assert_PROP (isptr sp) as Psp.
          { unfold sel_res. rewrite Es. unfold hset_tbl. Intros tp. entailer!. }
          forward. forward.
          { unfold sel_res. rewrite Es. unfold hset_tbl. Intros tp. entailer!. }
          rewrite Es. destruct sp; try contradiction. entailer!. }
      { forward. entailer!.
        assert (Hm: dp_multi pr <> 1) by (intros Hm; rewrite Hm in H5; contradiction).
        unfold sel_on. destruct (dp_multi pr =? 1) eqn:E; [lia | reflexivity]. }
      forward_if (EX did': Z, EX d': dfields,
        PROP (did' = (if eq_dec (if sel_on pr sp then sel_r d l tbl (fh_dictID h) else nullval) nullval
                      then did else fh_dictID h);
              d' = sel_dict d (if sel_on pr sp then sel_r d l tbl (fh_dictID h) else nullval))
        LOCAL (gvars gv; temp _dctx p; temp _src (offset_val off base);
               temp _headerSize (Vlong (Int64.repr (Zlength s))))
        SEP (zstd_globals gv; data_at sh (tarray tuchar N) c base;
             fcore3 p (fsu_dictID (fsu_fParams fs (fh_val h)) (Vint (Int.repr did'))) pr sp;
             sel_res DENT gv p pr sp d' l tbl xq am hb)).
      { destruct (sel_on pr sp) eqn:Es; [| exfalso; simpl in *; contradiction].
        unfold sel_res. rewrite Es. Intros.
        destruct (Hsm Es) as (Hlm & Hcm & Hhb).
        forward_call (gv, p, fsu_fParams fs (fh_val h), fh_dictID h, d, sp, l, tbl, xq, am, hb).
        { unfold frame_fields. fs_cbn. cancel. }
        { rewrite sel_on_null in Es. discriminate. }
        destruct (eq_dec (sel_r d l tbl (fh_dictID h)) nullval) as [Er|Er].
        - Exists did (sel_dict d (sel_r d l tbl (fh_dictID h))). unfold fcore3, sel_res, frame_fields.
          rewrite Es, Er. fs_cbn. rewrite H0. entailer!.
        - Exists (fh_dictID h) (sel_dict d (sel_r d l tbl (fh_dictID h))). unfold fcore3, sel_res, frame_fields.
          rewrite Es. destruct (eq_dec (sel_r d l tbl (fh_dictID h)) nullval); [contradiction|].
          fs_cbn. entailer!. }
      { destruct (sel_on pr sp) eqn:Es; [exfalso; int_contra |].
        forward. Exists did d. unfold fcore3, sel_res, frame_fields. rewrite Es. fs_cbn. rewrite H0.
        destruct (eq_dec nullval nullval); [|contradiction]. entailer!. }
      Intros did' d'. rename H5 into Hdid'. rename H6 into Hd'.
      unfold fcore3, cfg_fmt, cfg_lit, frame_fields. Intros. fs_cbn.
      assert (Hdr: 0 <= did' <= Int.max_unsigned) by (rewrite Hdid'; destruct (eq_dec _ nullval); lia).
      assert (Hdid0 : fh_dictID h <> 0 -> Int.repr (fh_dictID h) <> Int.zero).
      { intros Hz Hc. apply (f_equal Int.unsigned) in Hc. rewrite Int.unsigned_repr in Hc by rep_lia.
        change (Int.unsigned Int.zero) with 0 in Hc. lia. }
      pose proof (conj Hdid' Hd') as Hsel. apply dfh_hide_intro in Hsel. clear Hdid' Hd'.
      destruct (orb (fh_dictID h =? 0) (fh_dictID h =? did')) eqn:Edid.
      * match goal with |- semax _ ?P _ _ => forward_loop P break: P end.
        { entailer!. }
        { unfold fh_val. forward.
          fif_set _t'4 (Vint (Int.repr 0)).
          { assert (Heq: fh_dictID h = did').
            { destruct (Z.eqb_spec (fh_dictID h) 0) as [e|e]. { rewrite e in *. contradiction. }
              simpl in Edid. lia. }
            forward. forward. forward. rewrite <- Heq. entailer!. }
          { forward. entailer!. }
          match goal with |- semax _ ?P _ _ => forward_if P end.
          { exfalso; lia. }
          { forward. entailer!. }
          forward. entailer!. }
        rewrite H2. unfold fh_val.
        remember (andb (fh_checksumFlag h =? 1) (negb (md_ignore (dmode_of pr)))) as vf eqn:Evf.
        apply dfh_hide_intro in Evf.
        assert (Hign: dp_ignore pr = 0 \/ dp_ignore pr = 1) by (destruct Hpar as (_ & ? & _); auto).
        forward.
        fif_set _t'5 (Vint (Int.repr (if vf then 1 else 0))).
        { assert (Hc1: fh_checksumFlag h = 1) by (destruct Hcs as [Hc|Hc]; rewrite Hc in *; [contradiction | auto]).
          forward. forward. entailer!. unfold dfh_hide in Evf. rewrite Evf, Hc1. unfold dmode_of; simpl.
          destruct Hign as [Hi|Hi]; rewrite Hi; reflexivity. }
        { assert (Hc0: fh_checksumFlag h = 0) by (destruct Hcs as [Hc|Hc]; auto; rewrite Hc in *; exfalso; int_contra).
          forward. entailer!. unfold dfh_hide in Evf. rewrite Evf, Hc0. reflexivity. }
        fif_set _t'6 (Vint (Int.repr (if vf then 1 else 0))).
        { forward. entailer!. destruct vf; [reflexivity | exfalso; int_contra]. }
        { forward. entailer!. destruct vf; [exfalso; int_contra | reflexivity]. }
        forward. forward.
        lazymatch goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
          lazymatch R with context C [xxh_field p (fs_xxh fs)] =>
            let R' := context C [xxh_field p (if vf then Some [] else fs_xxh fs)] in
            forward_if (PROPx P (LOCALx Q (SEPx R'))) end end.
        { destruct vf; [| exfalso; match goal with Hx: Int.repr 0 <> Int.zero |- _ => apply Hx; reflexivity end].
          assert (Fx: field_compatible t_dctx (DOT _xxhState) p).
          { apply field_compatible_cons in Fp as [_ Fp0]. apply field_compatible_cons; split; [| exact Fp0].
            simpl. repeat (first [left; reflexivity | right]). }
          sep_apply (xxh_field_data_at_ p (fs_xxh fs)).
          forward_call (Ews, field_address t_dctx (DOT _xxhState) p, 0).
          simpl xxh_field. entailer!. }
        { destruct vf; [exfalso; int_contra |]. forward. entailer!. }
        forward. forward. forward.
        assert (dfh_post3 (dmode_of pr) (sel_on pr sp) d l tbl fs did pcs s 0
                  (fsu_processedCSize
                     (fsu_xxh (fsu_validateChecksum (fsu_dictID (fsu_fParams fs (fh_val h)) (Vint (Int.repr did')))
                                 (Vint (Int.repr (if vf then 1 else 0))))
                        (if vf then Some nil else fs_xxh fs))
                     (Vlong (Int64.repr (pcs + Zlength s)))) d').
        { unfold dfh_hide in Hsel, Evf. destruct Hsel as [Hdid' Hd']. unfold dfh_post3. rewrite Eg. cbv zeta.
          rewrite <- Hdid', <- Hd', Edid, <- Evf. split; [reflexivity | split; reflexivity]. }
        Exists 0 (fsu_processedCSize
                     (fsu_xxh (fsu_validateChecksum (fsu_dictID (fsu_fParams fs (fh_val h)) (Vint (Int.repr did')))
                                 (Vint (Int.repr (if vf then 1 else 0))))
                        (if vf then Some nil else fs_xxh fs))
                     (Vlong (Int64.repr (pcs + Zlength s)))) d'.
        unfold fcore3, cfg_fmt, cfg_lit, frame_fields. fs_cbn. unfold fh_val in *. entailer!.
      * assert (Hd0: fh_dictID h <> 0 /\ fh_dictID h <> did').
        { apply orb_false_iff in Edid as [E1 E2]. apply Z.eqb_neq in E1, E2. auto. }
        destruct Hd0 as [Hd1 Hd2].
        match goal with |- semax _ ?P _ _ => forward_loop P break: (PROP (False) LOCAL () SEP ()) end.
        { entailer!. }
        unfold fh_val. forward.
        fif_set _t'4 (Vint (Int.repr 1)).
        { forward. forward. forward. entailer!. }
        { exfalso. apply (Hdid0 Hd1). assumption. }
        forward_if (PROP (False) LOCAL () SEP ()).
        { repeat dw0. forward.
          assert (dfh_post3 (dmode_of pr) (sel_on pr sp) d l tbl fs did pcs s (Int64.unsigned (Int64.repr (-32)))
                    (fsu_dictID (fsu_fParams fs (fh_val h)) (Vint (Int.repr did'))) d').
          { unfold dfh_hide in Hsel. destruct Hsel as [Hdid' Hd'].
            unfold dfh_post3. rewrite Eg. cbv zeta. rewrite <- Hdid', <- Hd', Edid.
            split; [reflexivity | split; [dec_err_c | reflexivity]]. }
          Exists (Int64.unsigned (Int64.repr (-32))) (fsu_dictID (fsu_fParams fs (fh_val h)) (Vint (Int.repr did'))) d'.
          rewrite Int64.repr_unsigned. unfold fcore3, cfg_fmt, cfg_lit, frame_fields. fs_cbn. unfold fh_val in *.
          entailer!. }
        { exfalso. int_contra. }
Qed.

End Bodies.

(* the gap L3, closed by API v3.4's fh_post_m *)
Lemma fh_err_gap_ok : fh_err_gap.
Proof. intros mg s r v0 v H E; unfold fh_post_m in H; rewrite E in H; tauto. Qed.

Lemma bodies_dfh3 :
  FS3_body (fun DENT TABS SR BR => ZSTD_decodeFrameHeader_spec3 DENT).
Proof.
  intros DENT TABS SR BR _ _. apply body_decodeFrameHeader3. exact fh_err_gap_ok.
Qed.

End CM_body3_dfh_1.
