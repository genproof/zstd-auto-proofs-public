(* ZSTD_decodeLiteralsBlock, set_compressed / set_repeat, part 3: after the Huffman call, the split layout's copy of
   the last 65536 literals to litExtraBuffer and the move of the others by 65536 - 32 (patch items 18 and 20: only
   after a successful decode), from lit_J's state to lit_T, with the exact arrays (lit_oc2, lit_lxb2). *)
Require Export Zstd.proof.dec.v3.B.BlkLIT3Comp2.
Local Open Scope logic.
Local Ltac solve_load_rule_evaluation ::= lit_slre.

(* ---------- the end of set_compressed / set_repeat: the split shift and the literal fields ---------- *)
Lemma lit_loc3 (streaming cap bsm n: Z) :
  alloc_loc streaming cap bsm n = LOC_IN_DST \/ alloc_loc streaming cap bsm n = LOC_NOT_IN_DST \/
  alloc_loc streaming cap bsm n = LOC_SPLIT.
Proof. unfold alloc_loc. destruct (andb _ _); [| destruct (n <=? _)]; auto. Qed.

(* where the literals end up *)
Definition lit_lloc (streaming cap bsm n d: Z) : litloc :=
  if alloc_loc streaming cap bsm n =? LOC_IN_DST then LDst (d + bsm + WILDCOPY_OVERLENGTH)
  else if alloc_loc streaming cap bsm n =? LOC_NOT_IN_DST then LExtra
  else LSplit (d + Z.min bsm cap - n + LITBUFFEREXTRASIZE - WILDCOPY_OVERLENGTH).

(* the literals after the split shift: in the output array (oc2) and litExtraBuffer (ex2); the 32 cells after
   their part in the output array are defined *)
Definition lit_tok (streaming cap bsm n d: Z) (i: inwin) (oc2 ex2: list val) (l: list Z) : Prop :=
  lits_at (lit_lloc streaming cap bsm n d) oc2 d cap i l /\ Zlength l = n /\
  (match lit_lloc streaming cap bsm n d with LDst _ => streaming = 0 | _ => True end) /\
  match lit_lloc streaming cap bsm n d with
  | LExtra => sublist 0 n ex2 = zbytes l
  | LSplit _ => sublist 0 LITBUFFEREXTRASIZE ex2 = zbytes (sublist (n - LITBUFFEREXTRASIZE) n l)
  | _ => True
  end /\
  lit_slack_def (lit_lloc streaming cap bsm n d) oc2 n.

(* the slack after the literals in dst is defined in the array the Huffman call gets (zeroed by
   ZSTD_allocateLiteralsBuffer) *)
Definition lit_slack0 (streaming cap bsm n d: Z) (oc: list val) : Prop :=
  alloc_loc streaming cap bsm n = LOC_IN_DST ->
  Forall is_byte_val (sublist (d + bsm + WILDCOPY_OVERLENGTH + n)
                       (d + bsm + WILDCOPY_OVERLENGTH + n + WILDCOPY_OVERLENGTH) oc).

Lemma lit_mm_len (c: list val) (si di len: Z) :
  0 <= len -> 0 <= si -> si + len <= Zlength c -> 0 <= di -> di + len <= Zlength c ->
  Zlength (mm_result c (Zlength c) si di len) = Zlength c.
Proof.
  intros. unfold mm_result. rewrite !Zlength_app, !Zlength_sublist by lia. lia.
Qed.

Lemma lit_mm_unch (c: list val) (si di len: Z) :
  0 <= len -> 0 <= si -> si + len <= Zlength c -> 0 <= di -> di + len <= Zlength c ->
  unchanged_outside c (mm_result c (Zlength c) si di len) di (di + len).
Proof.
  intros H1 H2 H3 H4 H5 k Hk Hn. unfold mm_result.
  destruct (Z_lt_dec k di).
  - rewrite app_Znth1 by (rewrite Zlength_sublist by lia; lia). rewrite Znth_sublist by lia. f_equal; lia.
  - rewrite app_Znth2 by (rewrite Zlength_sublist by lia; lia). rewrite Zlength_sublist by lia.
    rewrite app_Znth2 by (rewrite Zlength_sublist by lia; lia). rewrite Zlength_sublist by lia.
    rewrite Znth_sublist by lia. f_equal; lia.
Qed.

Lemma lit_mm_mid (c: list val) (si di len: Z) :
  0 <= len -> 0 <= si -> si + len <= Zlength c -> 0 <= di -> di + len <= Zlength c ->
  sublist di (di + len) (mm_result c (Zlength c) si di len) = sublist si (si + len) c.
Proof.
  intros. unfold mm_result.
  rewrite sublist_app2 by (rewrite Zlength_sublist by lia; lia). rewrite Zlength_sublist by lia.
  rewrite sublist_app1 by (rewrite ?Zlength_sublist by lia; lia).
  replace (di - (di - 0)) with 0 by lia. replace (di + len - (di - 0)) with len by lia.
  rewrite sublist_sublist by lia. f_equal; lia.
Qed.

Lemma lit_zbytes_tc (l: list Z) : bytes_ok l -> Forall (tc_val tuchar) (zbytes l).
Proof.
  intros H. induction H as [| b l Hb _ IH]; constructor; auto.
  unfold is_byte in Hb. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia.
Qed.

Lemma lit_zbytes_sub (l: list Z) (a b: Z) : 0 <= a <= b -> b <= Zlength l ->
  sublist a b (zbytes l) = zbytes (sublist a b l).
Proof. intros. apply sublist_map. Qed.

Lemma lit_bytes_sub (l: list Z) (a b: Z) : bytes_ok l -> bytes_ok (sublist a b l).
Proof. intros H. unfold bytes_ok in *. apply Forall_sublist. exact H. Qed.


Lemma litc_bc_sub (l: list val) (a b: Z) : byte_cells l -> byte_cells (sublist a b l).
Proof. intros H. unfold byte_cells in *. apply Forall_sublist. exact H. Qed.

Lemma litc_bc_app (l1 l2: list val) : byte_cells l1 -> byte_cells l2 -> byte_cells (l1 ++ l2).
Proof. intros H1 H2. unfold byte_cells in *. apply Forall_app. auto. Qed.

Lemma litc_bc_mm (c: list val) (N si di len: Z) : byte_cells c -> byte_cells (mm_result c N si di len).
Proof. intros H. unfold mm_result. repeat apply litc_bc_app; apply litc_bc_sub; exact H. Qed.

Lemma lit_loc_dst (streaming cap bsm n: Z) :
  alloc_loc streaming cap bsm n = LOC_IN_DST -> streaming = 0 /\ bsm + WILDCOPY_OVERLENGTH + n + WILDCOPY_OVERLENGTH < cap.
Proof.
  unfold alloc_loc. destruct (andb _ _) eqn:E.
  - intros _. apply andb_prop in E. destruct E as [E1 E2]. split; [apply Z.eqb_eq | apply Z.ltb_lt]; auto.
  - destruct (n <=? _); discriminate.
Qed.

Lemma lit_loc_extra (streaming cap bsm n: Z) :
  alloc_loc streaming cap bsm n = LOC_NOT_IN_DST -> n <= LITBUFFEREXTRASIZE.
Proof.
  unfold alloc_loc. destruct (andb _ _); [discriminate |].
  destruct (n <=? _) eqn:E; [intros _; apply Z.leb_le; auto | discriminate].
Qed.

Lemma lit_loc_split (streaming cap bsm n: Z) :
  alloc_loc streaming cap bsm n = LOC_SPLIT -> LITBUFFEREXTRASIZE < n.
Proof.
  unfold alloc_loc. destruct (andb _ _); [discriminate |].
  destruct (n <=? _) eqn:E; [discriminate | intros _; apply Z.leb_gt; auto].
Qed.

(* cells outside the changed range keep their values *)
Lemma lit_unch_sub (oc oc1: list val) (lo hi a b: Z) :
  Zlength oc1 = Zlength oc -> unchanged_outside oc oc1 lo hi -> 0 <= a <= b -> b <= Zlength oc ->
  (b <= lo \/ hi <= a) -> sublist a b oc1 = sublist a b oc.
Proof.
  intros HL U Ha Hb Hd. apply Znth_eq_ext; [rewrite !Zlength_sublist by lia; lia |].
  intros k Hk. rewrite Zlength_sublist in Hk by lia.
  rewrite !Znth_sublist by lia. apply U; lia.
Qed.

(* not split: nothing moves *)
Lemma lit_nosplit_facts (streaming cap bsm n d: Z) (i: inwin) (oc oc1 ex1: list val) (l: list Z) :
  alloc_loc streaming cap bsm n <> LOC_SPLIT -> 0 <= d -> 0 <= n <= Z.min bsm cap -> 0 <= bsm <= 131072 ->
  d + cap <= Zlength oc -> Zlength oc1 = Zlength oc -> lit_slack0 streaming cap bsm n d oc ->
  (if alloc_loc streaming cap bsm n =? LOC_NOT_IN_DST then oc1 = oc
   else unchanged_outside oc oc1 (lit_hd streaming cap bsm n d) (lit_hd streaming cap bsm n d + n)) ->
  unchanged_outside oc oc1 d (d + cap) /\ (streaming = 1 -> unchanged_outside oc oc1 d (d + Z.min cap bsm)) /\
  (bytes_ok l -> Zlength l = n ->
   (if alloc_loc streaming cap bsm n =? LOC_NOT_IN_DST then sublist 0 n ex1 = zbytes l
    else sublist (lit_hd streaming cap bsm n d) (lit_hd streaming cap bsm n d + n) oc1 = zbytes l) ->
   lit_tok streaming cap bsm n d i oc1 ex1 l /\ lit_dk oc oc1).
Proof.
  intros HS Hd Hn Hb Hdc HL1 HS0 HU.
  destruct (lit_loc3 streaming cap bsm n) as [E | [E | E]]; [| | contradiction].
  - pose proof (lit_loc_dst _ _ _ _ E) as [Hs Hc]. specialize (HS0 E). unfold WILDCOPY_OVERLENGTH in Hc, HS0.
    unfold lit_tok, lit_lloc, lit_hd in *. rewrite E in *. cbn [Z.eqb Pos.eqb LOC_IN_DST LOC_NOT_IN_DST] in *.
    unfold LOC_IN_DST, LOC_NOT_IN_DST in HU |- *. cbn [Z.eqb Pos.eqb] in HU |- *.
    unfold WILDCOPY_OVERLENGTH in *.
    split; [| split].
    + eapply lit_unch_mono; [| | exact HU]; lia.
    + intros; lia.
    + intros Hl Hz Hsub. split.
      * unfold lits_at, lit_slack_def. rewrite Hz. unfold WILDCOPY_OVERLENGTH, ZSTD_BLOCKSIZE_MAX.
        pose proof (Z.le_min_l bsm cap). repeat split; auto; try lia.
        rewrite (lit_unch_sub oc oc1 (d + bsm + 32) (d + bsm + 32 + n)) by (auto; lia). exact HS0.
      * apply (lit_dk_unch oc oc1 (d + bsm + 32) (d + bsm + 32 + n)); auto; try lia.
        rewrite Hsub. apply lit_bv_zbytes. exact Hl.
  - pose proof (lit_loc_extra _ _ _ _ E) as Hx.
    unfold lit_tok, lit_lloc, lit_hd in *. rewrite E in *.
    unfold LOC_IN_DST, LOC_NOT_IN_DST in HU |- *. cbn [Z.eqb Pos.eqb] in HU |- *. subst oc1.
    split; [| split]; [apply lit_unch | intros; apply lit_unch |].
    intros Hl Hz Hsub. split; [| apply lit_dk_refl].
    unfold lits_at, lit_slack_def. rewrite Hz. unfold ZSTD_BLOCKSIZE_MAX.
    pose proof (Z.le_min_l bsm cap). repeat split; auto; try lia.
Qed.

Lemma lit_sub_in (c: list val) (si n a b: Z) (l: list Z) :
  0 <= si -> si + n <= Zlength c -> 0 <= a <= b -> b <= n -> Zlength l = n ->
  sublist si (si + n) c = zbytes l -> sublist (si + a) (si + b) c = zbytes (sublist a b l).
Proof.
  intros H1 H2 H3 H4 H5 H. rewrite <- lit_zbytes_sub by lia. rewrite <- H.
  rewrite sublist_sublist by lia. f_equal; lia.
Qed.

(* split: litExtraBuffer gets the last 65536 literals, the first ones move up by 65504 *)
Lemma lit_split_facts (streaming cap bsm n d: Z) (i: inwin) (oc oc1 ex1: list val) (l: list Z) :
  alloc_loc streaming cap bsm n = LOC_SPLIT -> 0 <= d -> 0 <= n <= Z.min bsm cap -> 0 <= bsm <= 131072 ->
  d + cap <= Zlength oc -> Zlength oc1 = Zlength oc -> Zlength ex1 = LITEXTRA_N ->
  unchanged_outside oc oc1 (d + Z.min bsm cap - n) (d + Z.min bsm cap - n + n) ->
  Zlength (mm_result oc1 (Zlength oc) (d + Z.min bsm cap - n) (d + Z.min bsm cap - n + 65504) (n - 65536)) = Zlength oc /\
  Zlength (sublist (d + Z.min bsm cap - 65536) (d + Z.min bsm cap) oc1 ++ sublist 65536 65568 ex1) = LITEXTRA_N /\
  unchanged_outside oc (mm_result oc1 (Zlength oc) (d + Z.min bsm cap - n) (d + Z.min bsm cap - n + 65504) (n - 65536))
    d (d + cap) /\
  (streaming = 1 -> unchanged_outside oc
     (mm_result oc1 (Zlength oc) (d + Z.min bsm cap - n) (d + Z.min bsm cap - n + 65504) (n - 65536))
     d (d + Z.min cap bsm)) /\
  (bytes_ok l -> Zlength l = n -> sublist (d + Z.min bsm cap - n) (d + Z.min bsm cap - n + n) oc1 = zbytes l ->
   lit_tok streaming cap bsm n d i
     (mm_result oc1 (Zlength oc) (d + Z.min bsm cap - n) (d + Z.min bsm cap - n + 65504) (n - 65536))
     (sublist (d + Z.min bsm cap - 65536) (d + Z.min bsm cap) oc1 ++ sublist 65536 65568 ex1) l /\
   lit_dk oc (mm_result oc1 (Zlength oc) (d + Z.min bsm cap - n) (d + Z.min bsm cap - n + 65504) (n - 65536))).
Proof.
  intros E Hd Hn Hb Hdc Hoc1 Hex1 HU.
  pose proof (lit_loc_split _ _ _ _ E) as Hx. unfold LITBUFFEREXTRASIZE in Hx.
  unfold LITEXTRA_N, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *.
  pose proof (Z.le_min_l bsm cap). pose proof (Z.le_min_r bsm cap). rewrite (Z.min_comm cap bsm).
  set (ews := Z.min bsm cap) in *.
  rewrite <- Hoc1 in *.
  assert (U2: unchanged_outside oc1 (mm_result oc1 (Zlength oc1) (d + ews - n) (d + ews - n + 65504) (n - 65536))
                d (d + ews)).
  { eapply lit_unch_mono; [| | apply lit_mm_unch]; lia. }
  assert (U: unchanged_outside oc (mm_result oc1 (Zlength oc1) (d + ews - n) (d + ews - n + 65504) (n - 65536))
                d (d + ews)).
  { apply lit_unch_trans with oc1; [lia | | exact U2]. eapply lit_unch_mono; [| | exact HU]; lia. }
  split; [| split; [| split; [| split]]].
  - apply lit_mm_len; lia.
  - rewrite Zlength_app, !Zlength_sublist by lia. lia.
  - eapply lit_unch_mono; [| | exact U]; lia.
  - intros _. exact U.
  - intros Hl Hz Hsub.
    assert (ML: Zlength (mm_result oc1 (Zlength oc1) (d + ews - n) (d + ews - n + 65504) (n - 65536)) = Zlength oc1)
      by (apply lit_mm_len; lia).
    split.
    + unfold lit_tok, lit_lloc. rewrite E. cbn [LOC_IN_DST LOC_NOT_IN_DST LOC_SPLIT Z.eqb Pos.eqb].
      unfold LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH. fold ews.
      replace (d + ews - n + 65536 - 32) with (d + ews - n + 65504) by lia.
      split; [| split; [exact Hz | split; [exact I | split]]].
      * unfold lits_at. rewrite Hz. unfold LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH, ZSTD_BLOCKSIZE_MAX.
        repeat split; auto; try lia.
        rewrite lit_mm_mid by lia.
        pose proof (lit_sub_in oc1 (d + ews - n) n 0 (n - 65536) l) as LS. rewrite Z.add_0_r in LS.
        apply LS; auto; lia.
      * rewrite sublist_app1 by (rewrite ?Zlength_sublist by lia; lia).
        rewrite sublist_sublist by lia.
        replace (0 + (d + ews - 65536)) with (d + ews - n + (n - 65536)) by lia.
        replace (65536 + (d + ews - 65536)) with (d + ews - n + n) by lia.
        apply (lit_sub_in oc1 (d + ews - n) n (n - 65536) n l); auto; lia.
      * unfold lit_slack_def, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH.
        replace (d + ews - n + 65504 + (n - 65536)) with (d + ews - n + (n - 32)) by lia.
        replace (d + ews - n + (n - 32) + 32) with (d + ews - n + n) by lia.
        rewrite (lit_unch_sub oc1 (mm_result oc1 (Zlength oc1) (d + ews - n) (d + ews - n + 65504) (n - 65536)) _ _
                   _ _ ML (lit_mm_unch oc1 (d + ews - n) (d + ews - n + 65504) (n - 65536) ltac:(lia) ltac:(lia)
                             ltac:(lia) ltac:(lia) ltac:(lia))) by lia.
        rewrite (lit_sub_in oc1 (d + ews - n) n (n - 32) n l) by (auto; lia).
        apply lit_bv_zbytes, lit_bytes_sub, Hl.
    + apply (lit_dk_trans oc oc1); [lia | |].
      * apply (lit_dk_unch oc oc1 (d + ews - n) (d + ews - n + n)); auto; try lia.
        rewrite Hsub. apply lit_bv_zbytes. exact Hl.
      * apply (lit_dk_unch oc1 _ (d + ews - n + 65504) (d + ews - n + 65504 + (n - 65536))); auto; try lia.
        -- apply lit_mm_unch; lia.
        -- rewrite lit_mm_mid by lia.
           rewrite <- (Z.add_0_r (d + ews - n)) at 1.
           rewrite (lit_sub_in oc1 (d + ews - n) n 0 (n - 65536) l) by (auto; lia).
           apply lit_bv_zbytes, lit_bytes_sub, Hl.
Qed.

(* a byte array as three pieces, the middle one of m bytes *)
Lemma lit_split3m (sh: share) (N a b m: Z) (c: list val) (q: val) :
  0 <= a <= b -> b <= N -> m = b - a -> Zlength c = N -> field_compatible (tarray tuchar N) [] q ->
  data_at sh (tarray tuchar N) c q =
  data_at sh (tarray tuchar a) (sublist 0 a c) q * data_at sh (tarray tuchar m) (sublist a b c) (offset_val a q) *
  data_at sh (tarray tuchar (N - b)) (sublist b N c) (offset_val b q).
Proof. intros H1 H2 -> H3 H4. apply litc_split3; auto. Qed.

Lemma lit_join3m (sh: share) (N a b m: Z) (c: list val) (q: val) :
  0 <= a <= b -> b <= N -> m = b - a -> Zlength c = N -> field_compatible (tarray tuchar N) [] q ->
  data_at sh (tarray tuchar a) (sublist 0 a c) q * data_at sh (tarray tuchar m) (sublist a b c) (offset_val a q) *
  data_at sh (tarray tuchar (N - b)) (sublist b N c) (offset_val b q) |--
  data_at sh (tarray tuchar N) c q.
Proof. intros. rewrite (lit_split3m sh N a b m c q) by auto. apply derives_refl. Qed.

(* litExtraBuffer as its 65536 + 32 cells *)
Lemma litc_extra_split (ex: list val) (p: val) :
  field_compatible t_dctx (DOT _litExtraBuffer) p -> Zlength ex = LITEXTRA_N ->
  field_at Ews t_dctx (DOT _litExtraBuffer) ex p =
  data_at Ews (tarray tuchar 65536) (sublist 0 65536 ex) (lit_extra p) *
  data_at Ews (tarray tuchar 32) (sublist 65536 65568 ex) (offset_val 65536 (lit_extra p)).
Proof.
  intros FC Hl. unfold LITEXTRA_N, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in Hl.
  rewrite field_at_data_at. change (nested_field_type t_dctx (DOT _litExtraBuffer)) with (tarray tuchar 65568).
  unfold lit_extra.
  assert (FC2: field_compatible (tarray tuchar 65568) [] (field_address t_dctx (DOT _litExtraBuffer) p)).
  { rewrite field_address_offset by auto. apply field_compatible_nested_field in FC. exact FC. }
  unfold tarray. rewrite (split2_data_at_Tarray_tuchar Ews 65568 65536) by (auto; lia).
  rewrite field_address0_offset.
  - simpl. reflexivity.
  - apply field_compatible0_cons. split; [simpl; lia | auto with field_compatible].
Qed.

Lemma litc_extra_join (a b: list val) (p: val) :
  field_compatible t_dctx (DOT _litExtraBuffer) p -> Zlength a = 65536 -> Zlength b = 32 ->
  data_at Ews (tarray tuchar 65536) a (lit_extra p) *
  data_at Ews (tarray tuchar 32) b (offset_val 65536 (lit_extra p)) |--
  field_at Ews t_dctx (DOT _litExtraBuffer) (a ++ b) p.
Proof.
  intros FC Ha Hb. rewrite (litc_extra_split (a ++ b) p FC)
    by (rewrite Zlength_app; unfold LITEXTRA_N, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH; lia).
  replace (sublist 0 65536 (a ++ b)) with a by list_solve.
  replace (sublist 65536 65568 (a ++ b)) with b by list_solve.
  apply derives_refl.
Qed.


(* the same with the length 65536 kept abstract (a literal 65536 makes VST build 65536-element lists) *)
Lemma lit_extra_splitK (K: Z) (ex: list val) (p: val) :
  K = 65536 -> field_compatible t_dctx (DOT _litExtraBuffer) p -> Zlength ex = LITEXTRA_N ->
  field_at Ews t_dctx (DOT _litExtraBuffer) ex p =
  data_at Ews (tarray tuchar K) (sublist 0 K ex) (lit_extra p) *
  data_at Ews (tarray tuchar 32) (sublist K 65568 ex) (offset_val K (lit_extra p)).
Proof. intros ->. apply litc_extra_split. Qed.

Lemma lit_extra_joinK (K: Z) (a b: list val) (p: val) :
  K = 65536 -> field_compatible t_dctx (DOT _litExtraBuffer) p -> Zlength a = K -> Zlength b = 32 ->
  data_at Ews (tarray tuchar K) a (lit_extra p) *
  data_at Ews (tarray tuchar 32) b (offset_val K (lit_extra p)) |--
  field_at Ews t_dctx (DOT _litExtraBuffer) (a ++ b) p.
Proof. intros ->. apply litc_extra_join. Qed.

(* the memmove of the split shift (litBuffer + 65504 <- litBuffer, litSize - 65536 bytes), inside its
   `if (!HUF_isError(hufSuccess))` (patch item 20) *)
Definition lit_mm : statement :=
  match lit_tail with
  | Ssequence (Ssequence _ (Sifthenelse _ (Ssequence _ (Ssequence (Ssequence _ (Sifthenelse _
      (Ssequence _ (Ssequence _ (Ssequence _ c))) _)) _)) _)) _ => c
  | _ => Sskip
  end.

(* the state at the memmove: litBuffer = ob + si in _t'64/_t'65, the constants, the output array (N, c) *)
Definition lit_mm_pre (gv: globals) (p: val) (bsm streaming e: Z) (ob: val) (d cap: Z) (ib: val) (ioff: Z)
    (s: list Z) (lh n cs: Z) (single: bool) (r: Z) (R: list mpred) (sh: share) (N: Z) (c: list val) (si: Z)
    : environ -> mpred :=
  PROPx [] (LOCALx (temp _t'64 (offset_val si ob) :: temp _t'65 (offset_val si ob) ::
                    temp _t'19 (Vint (Int.repr 65536)) :: temp _t'21 (Vint (Int.repr 65536)) ::
                    temp _hufSuccess (Vlong (Int64.repr r)) ::
                    lit_KL gv p bsm streaming e ob d cap ib ioff s lh n cs single)
    (SEPx (data_at sh (tarray tuchar N) c ob :: R))).

Ltac lit_mm_start :=
  unfold lit_mm_pre, lit_KL;
  let x := eval cbv [lit_mm lit_tail lit_drop lit_c2 lit_sw f_ZSTD_decodeLiteralsBlock fn_body] in lit_mm in
  change lit_mm with x;
  abbreviate_semax.

(* the move reads defined bytes: on success they are Huffman-decoded literals *)
Lemma lit_mm_def (Espec: OracleKind) (gv: globals) (p: val) (bsm streaming e: Z) (ob: val) (d cap: Z) (ib: val)
    (ioff: Z) (s: list Z) (lh n cs: Z) (single: bool) (r: Z) (R: list mpred) (sh: share) (N: Z) (c: list val)
    (si: Z) :
  writable_share sh -> isptr ob -> Zlength c = N -> N <= 2 ^ 63 - 1 -> 0 <= si -> 65536 <= n -> si + n - 32 <= N ->
  Forall byte_val (sublist si (si + (n - 65536)) c) ->
  semax lit_Delta (lit_mm_pre gv p bsm streaming e ob d cap ib ioff s lh n cs single r R sh N c si) lit_mm
    (normal_ret_assert (lit_mm_pre gv p bsm streaming e ob d cap ib ioff s lh n cs single r R sh N
       (mm_result c N si (si + 65504) (n - 65536)) si)).
Proof.
  intros Hsh Hob Hc HN Hsi Hn Hsn Hf. lit_mm_start.
  forward_call (mm_within sh ob N c si (si + 65504) (n - 65536)).
  - entailer!. destruct ob; try contradiction. simpl.
    rewrite Ptrofs.mul_commut, Ptrofs.mul_one.
    unfold Ptrofs.of_ints. rewrite Int.signed_repr by rep_lia.
    rewrite Ptrofs.sub_add_opp, Ptrofs.add_assoc, Ptrofs.neg_repr, ptrofs_add_repr.
    replace (si + 65536 + - (32)) with (si + 65504) by lia. reflexivity.
  - unfold mm_ok. split; [exact Hsh |]. repeat split; try lia; try rep_lia. exact Hf.
  - unfold mm_post. entailer!.
Qed.

(* the literal fields at the end (success) *)
Lemma lit_final_ok (oh: option huf_table) (o: outarr) (i: inwin) (bsm streaming e lh n cs r: Z) (single: bool)
    (oc2 ex2: list val) (l: list Z) (ht: huf_table) :
  lit_tok streaming (oa_cap o) bsm n (oa_d o) i oc2 ex2 l -> huf_ok ht -> n <= Z.min bsm (oa_cap o) ->
  3 <= lh -> 0 <= cs -> cs + lh <= Zlength (iw_s i) ->
  decode_literals oh (iw_s i) bsm =
    match lit_model e oh (negb single) (sublist lh (lh + cs) (iw_s i)) n with
    | Some (l0, t) => Some (l0, lh + cs, Some t) | None => None end ->
  match lit_model e oh (negb single) (sublist lh (lh + cs) (iw_s i)) n with
  | Some (l0, t0) => r = n /\ l = l0 /\ ht = t0 | None => True end ->
  lits_ok oh o i bsm streaming (cs + lh) oc2 (lit_lloc streaming (oa_cap o) bsm n (oa_d o)) l (Some ht).
Proof.
  intros (Hat & Hz & Hd & _ & Hsl) Hht Hn Hlh Hcs Hcl DL Hmod. unfold lits_ok.
  split; [lia |]. split; [exact Hat |]. split; [rewrite Hz, Z.min_comm; lia |].
  split; [exact Hd |]. split; [exact Hht |]. split.
  - rewrite DL. destruct (lit_model _ _ _ _ _) as [[l0 t0] |]; [| exact I].
    destruct Hmod as (_ & -> & ->). split; [lia | auto].
  - split; [| rewrite Hz; exact Hsl].
    unfold lit_pos, lit_lloc. rewrite Hz.
    destruct (_ =? LOC_IN_DST); [reflexivity |]. destruct (_ =? LOC_NOT_IN_DST); [exact I | reflexivity].
Qed.

(* the split shift and the end, as two statements *)
Definition lit_ifs : statement := match lit_tail with Ssequence c _ => c | _ => Sskip end.
Definition lit_rest : statement := match lit_tail with Ssequence _ c => c | _ => Sskip end.

Lemma lit_tail_eq : lit_tail = Ssequence lit_ifs lit_rest.
Proof. reflexivity. Qed.


(* after the split shift (lxb: litExtraBuffer before the arm, xt: the table type after it) *)
Definition lit_T (gv: globals) (p: val) (fs: fstate) (ox: option ddx) (lxb: list Z) (bsm streaming: Z)
    (W: list ptr_witness) (o: outarr) (i: inwin) (e lh n cs: Z) (single: bool) (r: Z) (ht: huf_table) (xt: bool)
    (l: list Z) : environ -> mpred :=
  (EX oc2: list val, EX ex2: list val,
  PROPx [Zlength oc2 = Zlength (oa_c o); Zlength ex2 = LITEXTRA_N; byte_cells ex2;
         byte_cells (oa_c o) -> byte_cells oc2;
         unchanged_outside (oa_c o) oc2 (oa_d o) (oa_d o + oa_cap o);
         streaming = 1 -> unchanged_outside (oa_c o) oc2 (oa_d o) (oa_d o + Z.min (oa_cap o) bsm);
         is_error_code r = false -> lit_tok streaming (oa_cap o) bsm n (oa_d o) i oc2 ex2 l;
         is_error_code r = false -> lit_dk (oa_c o) oc2;
         is_error_code r = false ->
           oc2 = lit_oc2 streaming (oa_cap o) bsm n (oa_d o) (oa_c o) l /\
           ex2 = zbytes (lit_lxb2 streaming (oa_cap o) bsm n lxb l)]
  (LOCALx (temp _hufSuccess (Vlong (Int64.repr r)) ::
           lit_KL gv p bsm streaming e (oa_base o) (oa_d o) (oa_cap o) (iw_base i) (iw_off i) (iw_s i) lh n cs single)
  (SEPx [frame_fields p fs; zstd_globals gv; pws_pred W; cfg_lit p; lit_hpart gv p ox e r ht xt;
         dent_of dent_def gv ox;
         field_at_ Ews t_dctx (DOT _workspace) p; field_at Ews t_dctx (DOT _litExtraBuffer) ex2 p;
         data_at (oa_sh o) (tarray tuchar (oa_N o)) oc2 (oa_base o);
         data_at (iw_sh i) (tarray tuchar (iw_N i)) (iw_c i) (iw_base i);
         field_at Ews t_dctx (DOT _litBuffer)
           (fst (alloc_buf p (oa_base o) streaming (oa_cap o) bsm n (oa_d o) (Z.min bsm (oa_cap o)) 1)) p;
         field_at Ews t_dctx (DOT _litBufferEnd)
           (snd (alloc_buf p (oa_base o) streaming (oa_cap o) bsm n (oa_d o) (Z.min bsm (oa_cap o)) 1)) p;
         field_at Ews t_dctx (DOT _litBufferLocation) (Vint (Int.repr (alloc_loc streaming (oa_cap o) bsm n))) p;
         field_at_ Ews t_dctx (DOT _litPtr) p; field_at_ Ews t_dctx (DOT _litSize) p])))%assert.

(* not split: the arrays after the call are the exact ones *)
Lemma lit_nosplit_exact (streaming cap bsm n d: Z) (oc oc1 ex1: list val) (lxb l: list Z) :
  alloc_loc streaming cap bsm n <> LOC_SPLIT -> 0 <= d -> 0 <= n <= Z.min bsm cap -> 0 <= bsm ->
  d + cap <= Zlength oc -> Zlength oc1 = Zlength oc ->
  (if alloc_loc streaming cap bsm n =? LOC_NOT_IN_DST then oc1 = oc
   else unchanged_outside oc oc1 (lit_hd streaming cap bsm n d) (lit_hd streaming cap bsm n d + n)) ->
  Zlength l = n ->
  (if alloc_loc streaming cap bsm n =? LOC_NOT_IN_DST then sublist 0 n ex1 = zbytes l
   else sublist (lit_hd streaming cap bsm n d) (lit_hd streaming cap bsm n d + n) oc1 = zbytes l) ->
  ex1 = zbytes (if alloc_loc streaming cap bsm n =? LOC_NOT_IN_DST then l ++ sublist n LITEXTRA_N lxb else lxb) ->
  oc1 = lit_oc2 streaming cap bsm n d oc l /\ ex1 = zbytes (lit_lxb2 streaming cap bsm n lxb l).
Proof.
  intros HS Hd Hn Hb Hdc HL HU Hl Hsub Hx.
  unfold lit_oc2, lit_lxb2, lit_hd in *.
  destruct (lit_loc3 streaming cap bsm n) as [E | [E | E]]; [| | contradiction]; rewrite E in *;
    unfold LOC_IN_DST, LOC_NOT_IN_DST in *; cbn [Z.eqb Pos.eqb] in *.
  - pose proof (lit_loc_dst _ _ _ _ E) as [_ Hc]. unfold WILDCOPY_OVERLENGTH in *.
    split; [| exact Hx]. apply lit_cwr_of with n; auto; try lia. rewrite Zlength_map; exact Hl.
  - split; [exact HU | exact Hx].
Qed.

(* split: the move and the copy to litExtraBuffer give the exact arrays *)
Lemma lit_split_exact (streaming cap bsm n d: Z) (oc oc1 ex1: list val) (lxb l: list Z) :
  alloc_loc streaming cap bsm n = LOC_SPLIT -> 0 <= d -> 0 <= n <= Z.min bsm cap -> 0 <= bsm ->
  d + cap <= Zlength oc -> Zlength oc1 = Zlength oc -> Zlength lxb = LITEXTRA_N -> ex1 = zbytes lxb ->
  unchanged_outside oc oc1 (d + Z.min bsm cap - n) (d + Z.min bsm cap - n + n) -> Zlength l = n ->
  sublist (d + Z.min bsm cap - n) (d + Z.min bsm cap - n + n) oc1 = zbytes l ->
  mm_result oc1 (Zlength oc) (d + Z.min bsm cap - n) (d + Z.min bsm cap - n + 65504) (n - 65536) =
    lit_oc2 streaming cap bsm n d oc l /\
  sublist (d + Z.min bsm cap - 65536) (d + Z.min bsm cap) oc1 ++ sublist 65536 65568 ex1 =
    zbytes (lit_lxb2 streaming cap bsm n lxb l).
Proof.
  intros E Hd Hn Hb Hdc HL Hlx Hx HU Hl Hsub.
  pose proof (lit_loc_split _ _ _ _ E) as Hx65.
  pose proof (Z.le_min_l bsm cap). pose proof (Z.le_min_r bsm cap).
  unfold lit_oc2, lit_lxb2. rewrite E. unfold LOC_IN_DST, LOC_NOT_IN_DST, LOC_SPLIT. cbn [Z.eqb Pos.eqb].
  unfold LITEXTRA_N, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *.
  set (ews := Z.min bsm cap) in *.
  assert (C1: oc1 = cwr oc (d + ews - n) (zbytes l))
    by (apply lit_cwr_of with n; auto; try lia; rewrite Zlength_map; exact Hl).
  split.
  - rewrite <- HL, lit_mm_cwr by lia.
    replace (d + ews - n + 65536 - 32) with (d + ews - n + 65504) by lia.
    pose proof (lit_sub_in oc1 (d + ews - n) n 0 (n - 65536) l) as LS. rewrite Z.add_0_r in LS.
    rewrite LS by (auto; lia). rewrite <- C1. reflexivity.
  - rewrite Hx, map_app, sublist_map. f_equal.
    replace (d + ews - 65536) with (d + ews - n + (n - 65536)) by lia.
    replace (d + ews) with (d + ews - n + n) at 2 by lia.
    apply (lit_sub_in oc1 (d + ews - n) n); auto; lia.
Qed.

Lemma lit_buf_ptr (p ob: val) (streaming cap bsm n d ews split: Z) :
  isptr ob -> isptr p -> field_compatible t_dctx (DOT _litBuffer) p ->
  isptr (fst (alloc_buf p ob streaming cap bsm n d ews split)) /\
  isptr (snd (alloc_buf p ob streaming cap bsm n d ews split)).
Proof.
  intros Hob Hp FC. unfold alloc_buf. rewrite (lit_extra_eq p FC).
  destruct ob; try contradiction. destruct p; try contradiction.
  destruct (_ =? _); [| destruct (_ =? _); [| destruct (split =? 1)]]; split; exact I.
Qed.


Lemma lit_buf10 (p ob: val) (streaming cap bsm n d ews: Z) :
  alloc_loc streaming cap bsm n <> LOC_SPLIT ->
  alloc_buf p ob streaming cap bsm n d ews 1 = alloc_buf p ob streaming cap bsm n d ews 0.
Proof.
  intros H. unfold alloc_buf.
  destruct (lit_loc3 streaming cap bsm n) as [E | [E | E]]; [| | contradiction]; rewrite E; reflexivity.
Qed.

(* litExtraBuffer after the guarded copy of the split case (contract patch item 18): the last 65536 literals
   after a successful Huffman decode, its previous bytes otherwise *)
Definition litc_xb2 (p: val) (oc1 ex1: list val) (r a b: Z) : mpred :=
  EX ex2: list val, !! (Zlength ex2 = LITEXTRA_N /\ byte_cells ex2 /\
    (is_error_code r = false -> ex2 = sublist a b oc1 ++ sublist 65536 65568 ex1)) &&
  field_at Ews t_dctx (DOT _litExtraBuffer) ex2 p.

(* the SEP list R with litExtraBuffer's item (contents ex1) replaced by X *)
Ltac litc_repl_xb R ex1 X :=
  lazymatch R with
  | field_at Ews t_dctx (DOT _litExtraBuffer) ex1 _ :: ?R' => constr:(X :: R')
  | ?a :: ?R' => let R'' := litc_repl_xb R' ex1 X in constr:(a :: R'')
  end.

(* the SEP list R with the output array's item (contents c) replaced by X *)
Ltac litc_repl_arr R c X :=
  lazymatch R with
  | data_at _ _ c _ :: ?R' => constr:(X :: R')
  | ?a :: ?R' => let R'' := litc_repl_arr R' c X in constr:(a :: R'')
  end.

(* the locals Q without the temps of the litBufferLocation test and of the two HUF_isError calls *)
Ltac lit_drop_temps Q :=
  lazymatch Q with
  | temp _t'22 _ :: ?Q' => lit_drop_temps Q'
  | temp _t'17 _ :: ?Q' => lit_drop_temps Q'
  | temp _t'61 _ :: ?Q' => lit_drop_temps Q'
  | ?a :: ?Q' => let Q'' := lit_drop_temps Q' in constr:(a :: Q'')
  | nil => constr:(@nil localdef)
  end.

Lemma lit_tail_if (Espec: OracleKind) (gv: globals) (p: val) (fs: fstate) (ox: option ddx) (oh: option huf_table)
    (x2: bool) (lxb: list Z) (bsm streaming: Z) (W: list ptr_witness) (o: outarr) (i: inwin) (e lh n cs: Z)
    (single: bool) (r: Z) (oc1 ex1: list val) (l: list Z) (ht: huf_table) (xt: bool) :
  lit_hyps fs oh bsm streaming W o i -> lit_kfacts oh bsm (oa_cap o) e (iw_s i) lh n cs single -> Zlength lxb = LITEXTRA_N ->
  lit_hfacts e ox oh x2 single (sublist lh (lh + cs) (iw_s i)) streaming (oa_cap o) bsm n (oa_d o) (oa_c o) oc1 lxb ex1
    r l ht ->
  lit_slack0 streaming (oa_cap o) bsm n (oa_d o) (oa_c o) ->
  semax lit_Delta
    (PROPx [] (LOCALx (temp _hufSuccess (Vlong (Int64.repr r)) ::
           lit_KL gv p bsm streaming e (oa_base o) (oa_d o) (oa_cap o) (iw_base i) (iw_off i) (iw_s i) lh n cs single)
     (SEPx ([frame_fields p fs; zstd_globals gv; pws_pred W; cfg_lit p; lit_hpart gv p ox e r ht xt; dent_of dent_def gv ox;
          field_at_ Ews t_dctx (DOT _workspace) p; field_at Ews t_dctx (DOT _litExtraBuffer) ex1 p;
          data_at (oa_sh o) (tarray tuchar (oa_N o)) oc1 (oa_base o);
          data_at (iw_sh i) (tarray tuchar (iw_N i)) (iw_c i) (iw_base i)] ++
         lit_KF p (oa_base o) streaming (oa_cap o) bsm n (oa_d o)))))
    lit_ifs (normal_ret_assert (lit_T gv p fs ox lxb bsm streaming W o i e lh n cs single r ht xt l)).
Proof.
  intros HY HK Hlxb HF HS0.
  destruct o as [osh ob oN oc d cap]; destruct i as [ish ib iN ic ioff s].
  destruct HY as (Hoo & Hio & Hstr & Hbsm0 & Hsb & Hfp & Hfd & Hcold & HW & Hoh & Hs2).
  destruct Hoo as (Hosh & HoN & HoN32 & Hd & Hcap & Hdc).
  destruct Hio as (Hish & Hioff & Hin & HiN32 & HiN & _ & Hbytes & Hwin).
  cbn [oa_sh oa_base oa_N oa_c oa_d oa_cap iw_sh iw_base iw_N iw_c iw_off iw_s] in *.
  subst iN oN.
  assert (Hbsm: 0 <= bsm <= 131072) by (unfold ZSTD_BLOCKSIZE_MAX in Hbsm0; lia).
  destruct HK as (He & Hty & Hx & H5 & Hh & Hlh & Hcs & Hsg & Hn & Hs6 & Hcl).
  pose proof (lit_hdr_range s lh n cs single Hbytes H5 Hh) as (_ & Hn0 & _ & _).
  unfold lit_hfacts in HF. cbv zeta in HF. destruct HF as (Hr & Hoc1 & Hex1 & Hbx1 & Hbo1 & HU & HSc & He3 & Hmod & HX1 & _).
  unfold lit_T, lit_KL, lit_KF. cbn [oa_sh oa_base oa_N oa_c oa_d oa_cap iw_sh iw_base iw_N iw_c iw_off iw_s app].
  let x := eval cbv [lit_ifs lit_tail lit_drop lit_c2 lit_sw f_ZSTD_decodeLiteralsBlock fn_body] in lit_ifs in
  change lit_ifs with x.
  abbreviate_semax.
  assert_PROP (isptr p) as Pp by (unfold frame_fields; entailer!).
  assert_PROP (isptr ob) as Pob by entailer!.
  assert_PROP (field_compatible t_dctx (DOT _litExtraBuffer) p) as FCx by entailer!.
  assert_PROP (field_compatible (tarray tuchar (Zlength oc)) [] ob) as FCo by entailer!.
  pose proof (Z.le_min_l bsm cap). pose proof (Z.le_min_r bsm cap).
  forward.
  forward_if.
  - assert (E: alloc_loc streaming cap bsm n = LOC_SPLIT).
    { destruct (lit_loc3 streaming cap bsm n) as [E | [E | E]]; rewrite E in H1; auto;
        apply (f_equal Int.unsigned) in H1; vm_compute in H1; discriminate. }
    pose proof (lit_loc_split _ _ _ _ E) as Hx65. unfold LITBUFFEREXTRASIZE in Hx65.
    unfold lit_hd in HU, HSc. rewrite E in HU, HSc. cbn [LOC_SPLIT LOC_IN_DST LOC_NOT_IN_DST Z.eqb Pos.eqb] in HU, HSc.
    unfold alloc_buf. rewrite E. cbn [LOC_SPLIT LOC_IN_DST LOC_NOT_IN_DST Z.eqb Pos.eqb fst snd].
    assert (Hex1': Zlength ex1 = 65568) by (rewrite Hex1; reflexivity).
    forward_call r.
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      let R' := litc_repl_xb R ex1 (litc_xb2 p oc1 ex1 r (d + Z.min bsm cap - 65536) (d + Z.min bsm cap)) in
      forward_if (PROPx P (LOCALx Q (SEPx R'))) end.
    { destruct (is_error_code r) eqn:Er; [lit_false |].
      forward_if (temp _t'13 (Vint (Int.repr 65536))); [forward; entailer! | discriminate |].
      forward_if (temp _t'14 (Vint (Int.repr 65536)));
        [discriminate | forward_if (temp _t'14 (Vint (Int.repr 65536))); [forward; forward; entailer! | discriminate] |].
      forward_if (temp _t'15 (Vint (Int.repr 65536))); [forward; entailer! | discriminate |].
      forward_if (temp _t'16 (Vint (Int.repr 65536)));
        [discriminate | forward_if (temp _t'16 (Vint (Int.repr 65536))); [forward; forward; entailer! | discriminate] |].
      forward.
      pose (K := 65536). assert (HK: 65536 <= K <= 65536) by (unfold K; lia). clearbody K.
      rewrite (lit_split3m osh (Zlength oc) (d + Z.min bsm cap - 65536) (d + Z.min bsm cap) K oc1 ob) by (auto; lia).
      rewrite (lit_extra_splitK K ex1 p ltac:(lia) FCx Hex1). Intros.
      sep_apply (data_at_data_at_ Ews (tarray tuchar K) (sublist 0 K ex1) (lit_extra p)).
      forward_call (osh, Ews, offset_val (d + Z.min bsm cap - 65536) ob, lit_extra p,
        existT (fun t => reptype t) (tarray tuchar K) (sublist (d + Z.min bsm cap - 65536) (d + Z.min bsm cap) oc1)).
      { entailer!. simpl. rewrite (lit_extra_eq p) by (eapply lit_fc; [exact FCx | apply compute_in_members_true_iff; reflexivity]).
        destruct p; try contradiction. destruct ob; try contradiction. simpl.
        rewrite Ptrofs.mul_commut, Ptrofs.mul_one. unfold Ptrofs.of_ints. rewrite !Int.signed_repr by rep_lia.
        rewrite Ptrofs.sub_add_opp, Ptrofs.add_assoc, Ptrofs.neg_repr, ptrofs_add_repr.
        match goal with |- context [Int64.repr (?a * Z.max 0 ?x)] =>
          let HM := fresh in assert (HM: Z.max 0 x = 65536) by lia; rewrite HM end.
        match goal with |- context [Ptrofs.repr (?a + - ?b)] => replace (a + - b) with (a - b) by lia end.
        reflexivity. }
      { cbn [projT1 projT2]. split; [simpl; rep_lia |].
        destruct (HSc eq_refl) as (_ & Hbl & Hlen & _ & Hsub).
        apply memcpy_ok_bytes; [rewrite Zlength_sublist by lia; lia |].
        replace (sublist (d + Z.min bsm cap - 65536) (d + Z.min bsm cap) oc1) with (zbytes (sublist (n - 65536) n l)).
        - apply byte_val_zbytes, lit_bytes_sub, Hbl.
        - rewrite <- (lit_sub_in oc1 (d + Z.min bsm cap - n) n (n - 65536) n l) by (auto; lia). f_equal; lia. }
      cbn [projT1 projT2].
      sep_apply (lit_join3m osh (Zlength oc) (d + Z.min bsm cap - 65536) (d + Z.min bsm cap) K oc1 ob
                   ltac:(lia) ltac:(lia) ltac:(lia) Hoc1 FCo).
      sep_apply (lit_extra_joinK K (sublist (d + Z.min bsm cap - 65536) (d + Z.min bsm cap) oc1)
                   (sublist K 65568 ex1) p ltac:(lia) FCx
                   ltac:(rewrite Zlength_sublist by lia; lia) ltac:(rewrite Zlength_sublist by lia; lia)).
      replace K with 65536 by lia.
      unfold litc_xb2. Exists (sublist (d + Z.min bsm cap - 65536) (d + Z.min bsm cap) oc1 ++ sublist 65536 65568 ex1).
      entailer!.
      destruct (HSc eq_refl) as (_ & Hbl & Hlen & _ & Hsub).
      split.
      - rewrite Zlength_app, !Zlength_sublist by lia. unfold LITEXTRA_N, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH. lia.
      - apply litc_bc_app; [| apply litc_bc_sub; exact Hbx1].
        assert (Hq: sublist (d + Z.min bsm cap - 65536) (d + Z.min bsm cap) oc1 = zbytes (sublist (n - 65536) n l)).
        { rewrite <- (lit_sub_in oc1 (d + Z.min bsm cap - n) n (n - 65536) n l) by (auto; lia). f_equal; lia. }
        rewrite Hq. apply litc_bc_zbytes, lit_bytes_sub, Hbl. }
    { forward. destruct (is_error_code r) eqn:Er;
        [| match goal with H: Int.repr _ <> Int.zero |- _ => exfalso; apply H; reflexivity end].
      unfold litc_xb2. Exists ex1. entailer!. }
    unfold litc_xb2. Intros ex2.
    rename H2 into Hx2l, H3 into Hbx2, H4 into Hx2e.
    (* the shift, only after a successful decode (patch item 20) *)
    forward_call r.
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      let R' := litc_repl_arr R oc1 (data_at osh (tarray tuchar (Zlength oc)) (if is_error_code r then oc1
                else mm_result oc1 (Zlength oc) (d + Z.min bsm cap - n) (d + Z.min bsm cap - n + 65504) (n - 65536)) ob) in
      let Q' := lit_drop_temps Q in
      forward_if (PROPx P (LOCALx Q' (SEPx R'))) end.
    { destruct (is_error_code r) eqn:Er; [lit_false |].
      forward_if (temp _t'18 (Vint (Int.repr 65536))); [forward; entailer! | discriminate |].
      forward_if (temp _t'19 (Vint (Int.repr 65536)));
        [discriminate | forward_if (temp _t'19 (Vint (Int.repr 65536))); [forward; forward; entailer! | discriminate] |].
      forward_if (temp _t'20 (Vint (Int.repr 65536))); [forward; entailer! | discriminate |].
      forward_if (temp _t'21 (Vint (Int.repr 65536)));
        [discriminate | forward_if (temp _t'21 (Vint (Int.repr 65536))); [forward; forward; entailer! | discriminate] |].
      forward. forward.
      focus_SEP 8.
      match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx (_ :: ?R)))) _ _ =>
        assert (MM: semax lit_Delta
          (lit_mm_pre gv p bsm streaming e ob d cap ib ioff s lh n cs single r R osh (Zlength oc) oc1
             (d + Z.min bsm cap - n)) lit_mm
          (normal_ret_assert (lit_mm_pre gv p bsm streaming e ob d cap ib ioff s lh n cs single r R osh (Zlength oc)
             (mm_result oc1 (Zlength oc) (d + Z.min bsm cap - n) (d + Z.min bsm cap - n + 65504) (n - 65536))
             (d + Z.min bsm cap - n))))
      end.
      { destruct (HSc eq_refl) as (_ & Hbl & Hlen & _ & Hsub).
        apply lit_mm_def; auto; try lia.
        assert (Hs: sublist (d + Z.min bsm cap - n) (d + Z.min bsm cap - n + (n - 65536)) oc1 =
                    zbytes (sublist 0 (n - 65536) l)).
        { pose proof (lit_sub_in oc1 (d + Z.min bsm cap - n) n 0 (n - 65536) l) as LS.
          rewrite Z.add_0_r in LS. apply LS; auto; lia. }
        rewrite Hs. apply byte_val_zbytes, lit_bytes_sub, Hbl. }
      eapply semax_pre; [| eapply semax_post; [| | | | exact MM]].
      - unfold lit_mm_pre, lit_KL. entailer!.
      - unfold POSTCONDITION, abbreviate. cbn [RA_normal normal_ret_assert overridePost].
        unfold lit_mm_pre, lit_KL. entailer!.
      - intros. apply andp_left2. simpl. normalize.
      - intros. apply andp_left2. simpl. normalize.
      - intros. apply andp_left2. simpl. normalize. }
    { forward. destruct (is_error_code r) eqn:Er;
        [| match goal with H: Int.repr _ <> Int.zero |- _ => exfalso; apply H; reflexivity end].
      entailer!. }
    forward_if (temp _t'23 (Vint (Int.repr 65536))); [forward; entailer! | discriminate |].
    forward_if (temp _t'24 (Vint (Int.repr 65536)));
      [discriminate | forward_if (temp _t'24 (Vint (Int.repr 65536))); [forward; forward; entailer! | discriminate] |].
    forward. forward. forward. forward.
    assert (Pq: forall k, isptr (offset_val k ob)) by (intros; destruct ob; try contradiction; exact I).
    rewrite sub_repr, lit_add_i, lit_sub_i, !offset_offset_val by (auto; rep_lia).
    unfold alloc_buf. rewrite E. cbn [LOC_SPLIT LOC_IN_DST LOC_NOT_IN_DST Z.eqb Pos.eqb fst snd].
    unfold LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH.
    replace (d + Z.min bsm cap - n + (65536 - 32)) with (d + Z.min bsm cap - n + 65536 - 32) by lia.
    replace (d + Z.min bsm cap + - (32)) with (d + Z.min bsm cap - 32) by lia.
    destruct (lit_split_facts streaming cap bsm n d
      {| iw_sh := ish; iw_base := ib; iw_N := Zlength ic; iw_c := ic; iw_off := ioff; iw_s := s |}
      oc oc1 ex1 l E Hd ltac:(lia) Hbsm Hdc Hoc1 Hex1 HU) as (F1 & F2 & F3 & F4 & F5).
    Exists (if is_error_code r then oc1
            else mm_result oc1 (Zlength oc) (d + Z.min bsm cap - n) (d + Z.min bsm cap - n + 65504) (n - 65536))
      ex2.
    destruct (is_error_code r) eqn:Er.
    + entailer!.
      repeat match goal with |- _ /\ _ => split end; try (intros ?; discriminate);
        try (intros _; eapply lit_unch_mono; [| | exact HU]; rewrite ?(Z.min_comm cap bsm); lia);
        eapply lit_unch_mono; [| | exact HU]; lia.
    + destruct (HSc eq_refl) as (_ & Hbl & Hlen & _ & Hsub).
      rewrite (Hx2e eq_refl) in *. destruct (F5 Hbl Hlen Hsub) as [T5 D5].
      assert (HX1': ex1 = zbytes lxb) by (rewrite (HX1 eq_refl), E; reflexivity).
      destruct (lit_split_exact streaming cap bsm n d oc oc1 ex1 lxb l E Hd ltac:(lia) ltac:(lia) Hdc Hoc1 Hlxb
                  HX1' HU Hlen Hsub) as [X1 X2].
      entailer!.
      repeat match goal with |- _ /\ _ => split end; try (intros _); auto; apply litc_bc_mm; auto.
  - forward.
    assert (NS: alloc_loc streaming cap bsm n <> LOC_SPLIT) by (intro E; rewrite E in H1; apply H1; reflexivity).
    rewrite (lit_buf10 p ob streaming cap bsm n d (Z.min bsm cap) NS).
    destruct (lit_nosplit_facts streaming cap bsm n d
      {| iw_sh := ish; iw_base := ib; iw_N := Zlength ic; iw_c := ic; iw_off := ioff; iw_s := s |}
      oc oc1 ex1 l NS Hd ltac:(lia) Hbsm Hdc Hoc1 HS0 HU) as (U1 & U2 & T).
    Exists oc1 ex1. entailer!.
    destruct (is_error_code r) eqn:Er; [repeat split; intros; discriminate |].
    destruct (HSc eq_refl) as (_ & Hbl & Hlen & _ & Hsub).
    destruct (T Hbl Hlen Hsub) as [T1 T2].
    destruct (lit_nosplit_exact streaming cap bsm n d oc oc1 ex1 lxb l NS Hd ltac:(lia) ltac:(lia) Hdc Hoc1 HU Hlen Hsub
                (HX1 eq_refl)) as [X1 X2].
    repeat match goal with |- _ /\ _ => split end; intros _; first [assumption | split; assumption].
Qed.
