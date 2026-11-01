(* w_frame's frame header: what the format model reads from hp_bytes p followed by anything. *)
Require Import Zstd.proof.harness.writer.model.WF_Defs.
Local Open Scope bool_scope.

(* ---------- helpers: little-endian fields ---------- *)

Lemma wfh_le_bytes_length : forall k v, length (le_bytes k v) = k.
Proof. induction k; intros; simpl; auto. Qed.

Lemma wfh_le_bytes_Zlength : forall k v, Zlength (le_bytes k v) = Z.of_nat k.
Proof. intros. rewrite Zlength_correct, wfh_le_bytes_length. reflexivity. Qed.

Lemma wfh_le_value_le_bytes : forall k v, le_value (le_bytes k v) = v mod 256 ^ Z.of_nat k.
Proof.
  induction k; intros v; cbn [le_bytes le_value].
  - rewrite Z.pow_0_r, Z.mod_1_r. reflexivity.
  - rewrite IHk, Nat2Z.inj_succ, Z.pow_succ_r by lia.
    rewrite Z.rem_mul_r by (try lia; apply Z.pow_pos_nonneg; lia). ring.
Qed.

Lemma wfh_le_bytes_ok : forall k v, bytes_ok (le_bytes k v).
Proof.
  induction k; intros v; cbn [le_bytes]; constructor.
  - unfold is_byte; apply Z.mod_pos_bound; lia.
  - apply IHk.
Qed.

Lemma wfh_le_field_at : forall a b t i k, i = Zlength a -> k = Zlength b ->
  le_field (a ++ b ++ t) i k = le_value b.
Proof.
  intros a b t i k -> ->. unfold le_field, slice. rewrite !Zlength_correct, !Nat2Z.id.
  rewrite skipn_app, skipn_all, Nat.sub_diag. simpl.
  rewrite firstn_app, firstn_all, Nat.sub_diag. simpl. rewrite app_nil_r. reflexivity.
Qed.

Lemma wfh_Zlength_app : forall a b : list Z, Zlength (a ++ b) = Zlength a + Zlength b.
Proof. intros. rewrite !Zlength_correct, app_length. lia. Qed.

Lemma wfh_byte_at_at : forall a x t i, i = Zlength a -> byte_at (a ++ x :: t) i = x.
Proof.
  intros a x t i ->. unfold byte_at. rewrite Zlength_correct, Nat2Z.id, app_nth2 by lia.
  rewrite Nat.sub_diag. reflexivity.
Qed.

(* ---------- helpers: the descriptor and window bytes ---------- *)

Definition wfh_fhd_check (fcs: Z) (single ck: bool) (didf: Z) : bool :=
  let fhd := Z.lor (Z.lor (Z.lor (Z.shiftl fcs 6) (Z.shiftl (zb single) 5)) (Z.shiftl (zb ck) 2)) didf in
  let hs := 5 + (1 - zb single) + nth (Z.to_nat didf) [0; 1; 2; 4] 0 + nth (Z.to_nat fcs) [0; 2; 4; 8] 0
            + (if single && (fcs =? 0) then 1 else 0) in
  (0 <=? fhd) && (fhd <? 256) && (Z.land fhd 8 =? 0) && (Z.land fhd 3 =? didf) &&
  (Z.land (Z.shiftr fhd 2) 1 =? zb ck) && (Z.land (Z.shiftr fhd 5) 1 =? zb single) &&
  (Z.shiftr fhd 6 =? fcs) && (Z.land (Z.shiftr (Z.lor fhd 8) 5) 1 =? zb single) &&
  (fhd_header_size fhd =? hs) && (fhd_header_size (Z.lor fhd 8) =? hs).

Lemma wfh_fhd_check_all : forall fcs single ck didf, 0 <= fcs <= 3 -> 0 <= didf <= 3 ->
  wfh_fhd_check fcs single ck didf = true.
Proof.
  intros fcs single ck didf Hf Hd.
  assert (fcs = 0 \/ fcs = 1 \/ fcs = 2 \/ fcs = 3) as Hf' by lia.
  assert (didf = 0 \/ didf = 1 \/ didf = 2 \/ didf = 3) as Hd' by lia.
  destruct single, ck; destruct Hf' as [-> | [-> | [-> | ->]]]; destruct Hd' as [-> | [-> | [-> | ->]]];
    vm_compute; reflexivity.
Qed.

Definition wfh_wbyte_check : bool :=
  forallb (fun e => forallb (fun m => let w := Z.lor (Z.shiftl e 3) m in
    (0 <=? w) && (w <? 256) && (Z.shiftr w 3 =? e) && (Z.land w 7 =? m))
    (map Z.of_nat (seq 0 8))) (map Z.of_nat (seq 0 32)).

Lemma wfh_wbyte : forall e m, 0 <= e <= 31 -> 0 <= m <= 7 ->
  0 <= Z.lor (Z.shiftl e 3) m < 256 /\ Z.shiftr (Z.lor (Z.shiftl e 3) m) 3 = e /\
  Z.land (Z.lor (Z.shiftl e 3) m) 7 = m.
Proof.
  intros e m He Hm.
  assert (Hc: wfh_wbyte_check = true) by (vm_compute; reflexivity).
  unfold wfh_wbyte_check in Hc. rewrite forallb_forall in Hc.
  specialize (Hc e). rewrite forallb_forall in Hc.
  specialize (Hc ltac:(apply in_map_iff; exists (Z.to_nat e); split; [lia|apply in_seq; lia]) m
                ltac:(apply in_map_iff; exists (Z.to_nat m); split; [lia|apply in_seq; lia])).
  rewrite !Bool.andb_true_iff, !Z.leb_le, !Z.ltb_lt, !Z.eqb_eq in Hc. lia.
Qed.

Lemma wfh_fhd : forall p, 0 <= hp_fcs p <= 3 -> 0 <= hp_didf p <= 3 ->
  0 <= hp_fhd p < 256 /\ Z.land (hp_fhd p) 8 = 0 /\ Z.land (hp_fhd p) 3 = hp_didf p /\
  Z.land (Z.shiftr (hp_fhd p) 2) 1 = zb (hp_ck p) /\ Z.land (Z.shiftr (hp_fhd p) 5) 1 = zb (hp_single p) /\
  Z.shiftr (hp_fhd p) 6 = hp_fcs p /\ Z.land (Z.shiftr (Z.lor (hp_fhd p) 8) 5) 1 = zb (hp_single p) /\
  fhd_header_size (Z.lor (hp_fhd p) 8) = fhd_header_size (hp_fhd p).
Proof.
  intros p Hf Hd. pose proof (wfh_fhd_check_all _ (hp_single p) (hp_ck p) _ Hf Hd) as Hc.
  cbv beta zeta delta [wfh_fhd_check] in Hc. unfold hp_fhd.
  rewrite !Bool.andb_true_iff, !Z.leb_le, !Z.ltb_lt, !Z.eqb_eq in Hc. intuition congruence.
Qed.

Lemma wfh_len : forall dm p, hp_ok dm p ->
  Zlength (hp_bytes p) = fhd_header_size (hp_fhd p) /\ 6 <= Zlength (hp_bytes p) <= 18.
Proof.
  intros dm [n single ck fcs e m didf did] Hok. unfold hp_ok in Hok; cbn [hp_n hp_single hp_ck hp_fcs hp_e hp_m hp_didf hp_did] in Hok.
  destruct Hok as (_ & Hf & _ & _ & _ & _ & Hd & _).
  assert (fcs = 0 \/ fcs = 1 \/ fcs = 2 \/ fcs = 3) as Hf' by lia.
  assert (didf = 0 \/ didf = 1 \/ didf = 2 \/ didf = 3) as Hd' by lia.
  destruct single, ck; destruct Hf' as [-> | [-> | [-> | ->]]]; destruct Hd' as [-> | [-> | [-> | ->]]];
    split; reflexivity || (vm_compute; split; discriminate).
Qed.

(* the header's bytes, descriptor and fields *)
Lemma wf_hdr_bytes : forall dm p s, hp_ok dm p ->
  6 <= Zlength (hp_bytes p) <= 18 /\ bytes_ok (hp_bytes p) /\
  0 <= hp_fhd p < 256 /\ 0 <= hp_wbyte p < 256 /\
  le_field (hp_bytes p ++ s) 0 4 = ZSTD_MAGICNUMBER /\
  byte_at (hp_bytes p ++ s) 4 = hp_fhd p /\
  fhd_header_size (hp_fhd p) = Zlength (hp_bytes p) /\
  fhd_header_size (Z.lor (hp_fhd p) 8) = Zlength (hp_bytes p) /\
  Z.land (hp_fhd p) 8 = 0 /\
  Z.land (Z.shiftr (hp_fhd p) 5) 1 = zb (hp_single p) /\
  Z.land (Z.shiftr (Z.lor (hp_fhd p) 8) 5) 1 = zb (hp_single p) /\
  (hp_single p = false -> byte_at (hp_bytes p ++ s) 5 = hp_wbyte p) /\
  Z.shiftr (hp_wbyte p) 3 = hp_e p.
Proof.
  intros dm p s Hok.
  pose proof (wfh_len dm p Hok) as [Hl Hl'].
  pose proof Hok as (Hn & Hf & Hs0 & Hf1 & He & Hm & Hd & Hd0 & Hd1 & Hd2 & Hdid & Hdm).
  pose proof (wfh_fhd p Hf Hd) as (Hfr & H8 & _ & _ & H5 & _ & H5' & Hhs).
  pose proof (wfh_wbyte (hp_e p) (hp_m p) He Hm) as (Hwr & Hwe & _).
  fold (hp_wbyte p) in Hwr, Hwe.
  assert (HE: hp_bytes p ++ s = le_bytes 4 ZSTD_MAGICNUMBER ++ hp_fhd p ::
     ((if hp_single p then [] else [hp_wbyte p]) ++
      le_bytes (Z.to_nat (hp_did_size p)) (hp_did p) ++ hp_fcs_bytes p ++ s)).
  { unfold hp_bytes. rewrite <- !app_assoc. reflexivity. }
  repeat split; try lia.
  - unfold hp_bytes, bytes_ok. rewrite !Forall_app.
    refine (conj (wfh_le_bytes_ok _ _) (conj _ (conj _ (conj (wfh_le_bytes_ok _ _) _)))).
    + constructor; [unfold is_byte; lia | constructor].
    + destruct (hp_single p); repeat constructor; unfold is_byte; lia.
    + unfold hp_fcs_bytes. repeat destruct (_ =? _); try destruct (hp_single p);
        try apply wfh_le_bytes_ok; constructor.
  - intros Hsg. rewrite HE, Hsg. change (hp_fhd p :: ?x) with ([hp_fhd p] ++ x).
    rewrite app_assoc. apply wfh_byte_at_at. reflexivity.
Qed.

(* ZSTD_getFrameHeader on the header followed by anything *)
Lemma wf_hdr_gfh : forall dm f0 p nb ud s, hp_ok dm p -> wi_skippable f0 = false ->
  get_frame_header (hp_bytes p ++ s) =
    if wi_big (hp_info f0 p nb ud) then FH_err else FH_ok (wi_header (hp_info f0 p nb ud)).
Proof.
  intros dm f0 p nb ud s Hok Hsk.
  pose proof (wf_hdr_bytes dm p s Hok) as (Hl & _ & _ & _ & Hmg & Hb4 & Hhs & _ & H8 & _ & _ & Hb5 & _).
  pose proof Hok as (Hn & Hf & Hs0 & Hf1 & He & Hm & Hd & Hd0 & Hd1 & Hd2 & Hdid & Hdm).
  pose proof (wfh_fhd p Hf Hd) as (_ & _ & H3 & H2 & H5 & H6 & _ & _).
  pose proof (wfh_wbyte (hp_e p) (hp_m p) He Hm) as (_ & Hwe & Hwm).
  fold (hp_wbyte p) in Hwe, Hwm.
  assert (HE: hp_bytes p ++ s = (le_bytes 4 ZSTD_MAGICNUMBER ++ hp_fhd p ::
     (if hp_single p then [] else [hp_wbyte p])) ++
      le_bytes (Z.to_nat (hp_did_size p)) (hp_did p) ++ hp_fcs_bytes p ++ s).
  { unfold hp_bytes. rewrite <- !app_assoc. reflexivity. }
  assert (Hs: 0 <= Zlength s) by (rewrite Zlength_correct; lia).
  assert (HL: Zlength (hp_bytes p ++ s) = Zlength (hp_bytes p) + Zlength s)
    by (rewrite !Zlength_correct, app_length; lia).
  unfold get_frame_header. rewrite HL.
  replace (Zlength (hp_bytes p) + Zlength s <? 5) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite Hmg, Z.eqb_refl, Hb4, Hhs, H8, H3, H2, H5, H6.
  replace (Zlength (hp_bytes p) + Zlength s <? Zlength (hp_bytes p)) with false by (symmetry; apply Z.ltb_ge; lia).
  cbn [negb Z.eqb].
  set (P := le_bytes 4 ZSTD_MAGICNUMBER ++ hp_fhd p :: (if hp_single p then [] else [hp_wbyte p])) in HE.
  set (D := le_bytes (Z.to_nat (hp_did_size p)) (hp_did p)) in HE.
  assert (HP: Zlength P = 5 + (1 - zb (hp_single p))) by (subst P; destruct (hp_single p); reflexivity).
  assert (HD: Zlength D = nth (Z.to_nat (hp_didf p)) [0; 1; 2; 4] 0 /\ le_value D = hp_did p).
  { subst D. rewrite wfh_le_bytes_Zlength, wfh_le_value_le_bytes. unfold hp_did_size.
    assert (hp_didf p = 0 \/ hp_didf p = 1 \/ hp_didf p = 2 \/ hp_didf p = 3) as H by lia.
    destruct H as [H | [H | [H | H]]]; rewrite H in *;
      [specialize (Hd0 eq_refl) | specialize (Hd1 eq_refl) | specialize (Hd2 eq_refl) | ];
      simpl; (split; [reflexivity | apply Z.mod_small; lia]). }
  destruct HD as [HDl HDv].
  assert (Hdid': le_field (hp_bytes p ++ s) (5 + (1 - zb (hp_single p))) (nth (Z.to_nat (hp_didf p)) [0; 1; 2; 4] 0)
                 = hp_did p).
  { rewrite HE, wfh_le_field_at; [exact HDv | symmetry; exact HP | symmetry; exact HDl]. }
  rewrite Hdid'.
  set (pos := 5 + (1 - zb (hp_single p)) + nth (Z.to_nat (hp_didf p)) [0; 1; 2; 4] 0).
  assert (HQ: hp_bytes p ++ s = (P ++ D) ++ hp_fcs_bytes p ++ s) by (rewrite HE, app_assoc; reflexivity).
  assert (HQl: pos = Zlength (P ++ D)) by (rewrite wfh_Zlength_app, HP, HDl; reflexivity).
  clearbody P D pos.
  assert (Hcs: (if hp_fcs p =? 0 then (if zb (hp_single p) =? 1 then byte_at (hp_bytes p ++ s) pos else ZSTD_CONTENTSIZE_UNKNOWN)
     else if hp_fcs p =? 1 then le_field (hp_bytes p ++ s) pos 2 + 256
     else if hp_fcs p =? 2 then le_field (hp_bytes p ++ s) pos 4
     else le_field (hp_bytes p ++ s) pos 8) = (if hp_single p || negb (hp_fcs p =? 0) then hp_n p else ZSTD_CONTENTSIZE_UNKNOWN)).
  { rewrite HQ. unfold hp_fcs_bytes.
    assert (hp_fcs p = 0 \/ hp_fcs p = 1 \/ hp_fcs p = 2 \/ hp_fcs p = 3) as H by lia.
    destruct (hp_single p) eqn:Es; destruct H as [H | [H | [H | H]]]; rewrite H in *;
      cbv [Z.eqb Pos.eqb zb negb orb];
      try reflexivity;
      try (specialize (Hs0 eq_refl eq_refl); change (le_bytes 1 (hp_n p) ++ s) with (hp_n p mod 256 :: s);
           rewrite wfh_byte_at_at by exact HQl; apply Z.mod_small; lia);
      try (specialize (Hf1 eq_refl));
      (rewrite wfh_le_field_at by (first [exact HQl | reflexivity]);
       rewrite wfh_le_value_le_bytes, Z.mod_small by (simpl; lia); lia). }
  rewrite Hcs.
  unfold wi_big, wi_header, hp_info; cbn [wi_skippable wi_fcs_present wi_fcs wi_did wi_single wi_window
    wi_window_log wi_checksum wi_hsize]; rewrite Hsk.
  destruct (hp_single p) eqn:Es.
  - cbv [Z.eqb Pos.eqb zb negb andb orb hp_window hp_window_log]. rewrite Es. reflexivity.
  - rewrite Hb5 by reflexivity. rewrite Hwe, Hwm.
    cbv [Z.eqb Pos.eqb zb negb andb orb hp_window hp_window_log ZSTD_WINDOWLOG_ABSOLUTEMIN ZSTD_WINDOWLOG_MAX].
    rewrite Es, (Z.add_comm (hp_e p) 10). destruct (10 + hp_e p >? 31); [reflexivity|].
    rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

(* the frame record's ranges *)
Lemma wf_hdr_info_wf : forall dm f0 p nb ud, hp_ok dm p -> winfo_wf f0 -> 0 <= nb < 2 ^ 32 ->
  winfo_wf (hp_info f0 p nb ud).
Proof.
  intros dm f0 p nb ud Hok Hwf Hnb.
  pose proof (wfh_len dm p Hok) as [_ Hl].
  pose proof Hok as (Hn & Hf & Hs0 & Hf1 & He & Hm & Hd & Hd0 & Hd1 & Hd2 & Hdid & Hdm).
  unfold winfo_wf, u32, u64 in *. unfold hp_info; cbn [wi_variant wi_start wi_size wi_cstart wi_csize
    wi_fcs wi_did_size wi_did wi_window wi_window_log wi_blocks wi_skip_n wi_hsize].
  assert (Hds: 0 <= hp_did_size p <= 4).
  { unfold hp_did_size. assert (hp_didf p = 0 \/ hp_didf p = 1 \/ hp_didf p = 2 \/ hp_didf p = 3) as H by lia.
    destruct H as [-> | [-> | [-> | ->]]]; simpl; lia. }
  assert (Hw: 0 <= hp_window p < 2 ^ 64).
  { unfold hp_window. destruct (hp_single p); [lia|].
    assert (H1: 0 < 2 ^ (10 + hp_e p) <= 2 ^ 41)
      by (split; [apply Z.pow_pos_nonneg | apply Z.pow_le_mono_r]; lia).
    assert (H2: 0 <= 2 ^ (10 + hp_e p) / 8 <= 2 ^ (10 + hp_e p))
      by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
    nia. }
  assert (Hwl: 0 <= hp_window_log p <= 41) by (unfold hp_window_log; destruct (hp_single p); lia).
  intuition lia.
Qed.

(* the three facts together *)
Theorem wf_header_ok :
  (forall dm p s, hp_ok dm p ->
     6 <= Zlength (hp_bytes p) <= 18 /\ bytes_ok (hp_bytes p) /\
     0 <= hp_fhd p < 256 /\ 0 <= hp_wbyte p < 256 /\
     le_field (hp_bytes p ++ s) 0 4 = ZSTD_MAGICNUMBER /\
     byte_at (hp_bytes p ++ s) 4 = hp_fhd p /\
     fhd_header_size (hp_fhd p) = Zlength (hp_bytes p) /\
     fhd_header_size (Z.lor (hp_fhd p) 8) = Zlength (hp_bytes p) /\
     Z.land (hp_fhd p) 8 = 0 /\
     Z.land (Z.shiftr (hp_fhd p) 5) 1 = zb (hp_single p) /\
     Z.land (Z.shiftr (Z.lor (hp_fhd p) 8) 5) 1 = zb (hp_single p) /\
     (hp_single p = false -> byte_at (hp_bytes p ++ s) 5 = hp_wbyte p) /\
     Z.shiftr (hp_wbyte p) 3 = hp_e p) /\
  (forall dm f0 p nb ud s, hp_ok dm p -> wi_skippable f0 = false ->
     get_frame_header (hp_bytes p ++ s) =
       if wi_big (hp_info f0 p nb ud) then FH_err else FH_ok (wi_header (hp_info f0 p nb ud))) /\
  (forall dm f0 p nb ud, hp_ok dm p -> winfo_wf f0 -> 0 <= nb < 2 ^ 32 ->
     winfo_wf (hp_info f0 p nb ud)).
Proof. exact (conj wf_hdr_bytes (conj wf_hdr_gfh wf_hdr_info_wf)). Qed.
