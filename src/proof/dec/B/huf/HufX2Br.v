(* X2T body: HUF_readDTableX2_wksp.  The model facts and the final cell
   conversion are hypotheses (proved elsewhere). *)
Require Import Zstd.proof.dec.B.huf.HufX2S.
Require Import Zstd.proof.dec.B.BMemcpyOk.
Require Import Zstd.proof.model.ExHuf.
Local Open Scope logic.

Fixpoint sq_drop (k: nat) (s: statement) : statement :=
  match k, s with
  | O, _ => s
  | S k', Ssequence _ s2 => sq_drop k' s2
  | S _, _ => Sskip
  end.
Definition sq_head (s: statement) : statement := match s with Ssequence s1 _ => s1 | _ => s end.
Definition sq_tail (s: statement) : statement := match s with Ssequence _ s2 => s2 | _ => Sskip end.

(* ---------- the workspace ---------- *)

Definition t_x2wksp : type := Tstruct ___gp_HUF_ReadDTableX2_Workspace noattr.
Notation vint z := (Vint (Int.repr z)).

Lemma x2_al_uint (n z: Z) : (4 | z) -> align_compatible_rec cenv_cs (tarray tuint n) z.
Proof.
  intros H. apply align_compatible_rec_Tarray. intros i Hi.
  eapply align_compatible_rec_by_value; [reflexivity|]. simpl.
  apply Z.divide_add_r; auto. apply Z.divide_factor_l.
Qed.

Lemma x2_al_uchar (n z: Z) : align_compatible_rec cenv_cs (tarray tuchar n) z.
Proof.
  apply align_compatible_rec_Tarray. intros i Hi.
  eapply align_compatible_rec_by_value; [reflexivity|]. apply Z.divide_1_l.
Qed.

Lemma x2_al_rv (z: Z) : (4 | z) -> align_compatible_rec cenv_cs (tarray (tarray tuint 13) 12) z.
Proof.
  intros H. apply align_compatible_rec_Tarray. intros i Hi. apply x2_al_uint.
  apply Z.divide_add_r; auto. simpl sizeof. exists (13 * i)%Z. change (Ctypes.sizeof (tarray tuint 13)) with 52. lia.
Qed.

Lemma x2_al_ss (z: Z) : align_compatible_rec cenv_cs (tarray t_ssym 256) z.
Proof.
  apply align_compatible_rec_Tarray. intros i Hi.
  eapply align_compatible_rec_Tstruct; [reflexivity|reflexivity|].
  intros i0 t0 z0 Hf Ho.
  destruct (ident_eq i0 _symbol); [subst; vm_compute in Hf, Ho; inv Hf; inv Ho|].
  - eapply align_compatible_rec_by_value; [reflexivity|]. apply Z.divide_1_l.
  - exfalso. revert Hf. unfold Ctypes.field_type. simpl co_members.
    intro Hf. cbv fix beta iota in Hf. cbn [name_member] in Hf.
    repeat (destruct (ident_eq _ _) in Hf; [congruence|]). discriminate.
Qed.

Lemma x2wksp_compat (p: val) (nk: Z) :
  531 <= nk -> field_compatible (tarray tuint nk) nil p -> field_compatible t_x2wksp nil p.
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
    apply x2_al_rv; rewrite Z.add_0_r; auto|].
  destruct (ident_eq i0 _rankStats); [subst; vm_compute in Hf, Ho; inv Hf; inv Ho;
    apply x2_al_uint; apply Z.divide_add_r; auto; exists 156; reflexivity|].
  destruct (ident_eq i0 _rankStart0); [subst; vm_compute in Hf, Ho; inv Hf; inv Ho;
    apply x2_al_uint; apply Z.divide_add_r; auto; exists 169; reflexivity|].
  destruct (ident_eq i0 _sortedSymbol); [subst; vm_compute in Hf, Ho; inv Hf; inv Ho; apply x2_al_ss|].
  destruct (ident_eq i0 _weightList); [subst; vm_compute in Hf, Ho; inv Hf; inv Ho; apply x2_al_uchar|].
  destruct (ident_eq i0 _calleeWksp); [subst; vm_compute in Hf, Ho; inv Hf; inv Ho;
    apply x2_al_uint; apply Z.divide_add_r; auto; exists 312; reflexivity|].
  exfalso. revert Hf. unfold Ctypes.field_type. simpl co_members.
  intro Hf. cbv fix beta iota in Hf. cbn [name_member] in Hf.
  repeat (destruct (ident_eq _ _) in Hf; [congruence|]). discriminate.
Qed.

Lemma x2wksp_eq (shk: share) (pk: val) (nk: Z) :
  531 <= nk <= 4096 -> field_compatible (tarray tuint nk) nil pk ->
  data_at_ shk (tarray tuint nk) pk =
  data_at_ shk t_x2wksp pk * memory_block shk (4 * nk - 2124) (offset_val 2124 pk).
Proof.
  intros Hn Hfc.
  assert (Hfc2: field_compatible t_x2wksp nil pk) by (eapply x2wksp_compat; eauto; lia).
  rewrite data_at__memory_block. rewrite (prop_true_andp (field_compatible _ _ _)) by auto.
  rewrite <- (memory_block_data_at_ shk t_x2wksp pk) by auto.
  change (sizeof (tarray tuint nk)) with (4 * Z.max 0 nk)%Z. rewrite Z.max_r by lia.
  change (sizeof t_x2wksp) with 2124.
  destruct Hfc as (Hp & _ & Hsz & _).
  destruct pk; try contradiction. simpl in Hsz. rewrite Z.max_r in Hsz by lia.
  rewrite <- (Ptrofs.repr_unsigned i).
  replace (4 * nk)%Z with (2124 + (4 * nk - 2124))%Z at 1 by lia.
  rewrite memory_block_split by (pose proof (Ptrofs.unsigned_range i); lia).
  simpl offset_val. rewrite ptrofs_add_repr. reflexivity.
Qed.

Lemma x2wksp_fields (shk: share) (pk: val) :
  data_at_ shk t_x2wksp pk =
  field_at_ shk t_x2wksp (DOT _rankVal) pk * field_at_ shk t_x2wksp (DOT _rankStats) pk *
  field_at_ shk t_x2wksp (DOT _rankStart0) pk * field_at_ shk t_x2wksp (DOT _sortedSymbol) pk *
  field_at_ shk t_x2wksp (DOT _weightList) pk * field_at_ shk t_x2wksp (DOT _calleeWksp) pk.
Proof.
  unfold_data_at (data_at_ _ _ _). rewrite !sepcon_assoc. reflexivity.
Qed.

Lemma x2wksp_join (shk: share) (pk: val) (nk: Z) :
  531 <= nk <= 4096 -> field_compatible (tarray tuint nk) nil pk ->
  data_at_ shk (tarray (tarray tuint 13) 12) (field_address t_x2wksp (DOT _rankVal) pk) *
  data_at_ shk (tarray tuint 13) (field_address t_x2wksp (DOT _rankStats) pk) *
  data_at_ shk (tarray tuint 15) (field_address t_x2wksp (DOT _rankStart0) pk) *
  data_at_ shk (tarray t_ssym 256) (field_address t_x2wksp (DOT _sortedSymbol) pk) *
  data_at_ shk (tarray tuchar 256) (field_address t_x2wksp (DOT _weightList) pk) *
  data_at_ shk (tarray tuint 219) (field_address t_x2wksp (DOT _calleeWksp) pk) *
  memory_block shk (4 * nk - 2124) (offset_val 2124 pk)
  |-- data_at_ shk (tarray tuint nk) pk.
Proof.
  intros Hn Hfc. rewrite (x2wksp_eq shk pk nk) by auto. rewrite x2wksp_fields.
  rewrite !field_at__data_at_. simpl nested_field_type.
  cancel.
Qed.

Fixpoint x2_nodupb (l: list ident) : bool :=
  match l with nil => true | i :: r => negb (existsb (Pos.eqb i) r) && x2_nodupb r end.

Lemma x2_nodupb_ok (l: list ident) : x2_nodupb l = true -> NoDup l.
Proof.
  induction l as [|i r IH]; simpl; intros H; [constructor|].
  apply andb_prop in H as [H1 H2]. constructor; [|apply IH, H2].
  intros Hin. destruct (existsb (Pos.eqb i) r) eqn:E; [discriminate|].
  assert (existsb (Pos.eqb i) r = true) by (apply existsb_exists; exists i; split; [exact Hin | apply Pos.eqb_refl]).
  congruence.
Qed.

Lemma x2_G_nodup : NoDup (map fst Vprog ++ map fst G_X2).
Proof. apply x2_nodupb_ok. vm_compute. reflexivity. Qed.

(* ---------- the three loop segments of HUF_readDTableX2_wksp ----------
   Top-level statements of the body: 15 = rankStart (the start of each weight in sortedSymbol), 16 = the
   counting sort, 17 = rankVal.  Each is a semax triple in the function's context without calls (x2_Delta),
   with the locals the rest of the body uses and an abstract frame F. *)

Definition x2_rstart_stmt : statement :=
  Eval cbv [sq_head sq_drop fn_body f_HUF_readDTableX2_wksp] in sq_head (sq_drop 15 (fn_body f_HUF_readDTableX2_wksp)).
Definition x2_sort_stmt : statement :=
  Eval cbv [sq_head sq_drop fn_body f_HUF_readDTableX2_wksp] in sq_head (sq_drop 16 (fn_body f_HUF_readDTableX2_wksp)).
Definition x2_rv_stmt : statement :=
  Eval cbv [sq_head sq_drop fn_body f_HUF_readDTableX2_wksp] in sq_head (sq_drop 17 (fn_body f_HUF_readDTableX2_wksp)).

Definition x2_Delta : tycontext := func_tycontext f_HUF_readDTableX2_wksp Vprog nil nil.

(* rankStart0 after statement 15 (rankStart = rankStart0 + 1): rankStart[w] = rstart w for 1 <= w <= maxW,
   rankStart[0] = rankStart[maxW+1] = the number of symbols of weight >= 1; the rest still 0 (memset) *)
Definition x2_rsA (ht: huf_table) : list val :=
  map (fun i => vint (if i =? 0 then 0 else if i =? 1 then rstart ht (maxw ht + 1)
                      else if i <=? maxw ht + 2 then rstart ht (i - 1) else 0))
      (map Z.of_nat (seq 0 15)).

(* Statement 15: from the counts (rankStats) and maxW, the start index of each weight. *)
Definition x2_rstart_ok : Prop :=
  forall (Espec: OracleKind) (F: mpred) (ht: huf_table) (sz L: Z) (dtab pk vtl vnb vdtd: val) (shk: share),
  x2_count -> x2_ht_ok ht -> writable_share shk ->
  semax x2_Delta
    (PROP ()
     LOCAL (temp _maxW (vint (maxw ht)); temp _rankStart (offset_val 680 pk); temp _wksp pk;
            temp _dt (offset_val 4 dtab); temp _maxTableLog (vint L); temp _iSize (Vlong (Int64.repr sz));
            temp _DTable dtab; lvar _dtd t_dtdesc vdtd; lvar _nbSymbols tuint vnb; lvar _tableLog tuint vtl)
     SEP (field_at shk t_x2wksp (DOT _rankStats) (rank_stats (ht_weights ht)) pk;
          field_at shk t_x2wksp (DOT _rankStart0) (Zrepeat (vint 0) 15) pk;
          F))
    x2_rstart_stmt
    (normal_ret_assert
      (PROP ()
       LOCAL (temp _maxW (vint (maxw ht)); temp _rankStart (offset_val 680 pk); temp _wksp pk;
              temp _dt (offset_val 4 dtab); temp _maxTableLog (vint L); temp _iSize (Vlong (Int64.repr sz));
              temp _DTable dtab; lvar _dtd t_dtdesc vdtd; lvar _nbSymbols tuint vnb; lvar _tableLog tuint vtl)
       SEP (field_at shk t_x2wksp (DOT _rankStats) (rank_stats (ht_weights ht)) pk;
            field_at shk t_x2wksp (DOT _rankStart0) (x2_rsA ht) pk;
            F))).

(* Statement 16: the counting sort of the symbols by weight (weight-0 symbols last), then rankStart[0] = 0:
   sortedSymbol = sort_arr, rankStart0 as the fill wants it (x2_rs_ok). *)
Definition x2_sort_ok : Prop :=
  forall (Espec: OracleKind) (F: mpred) (ht: huf_table) (sz L: Z) (dtab pk vtl vnb vdtd: val) (shk: share)
         (wc a0: list val),
  x2_count -> x2_ht_ok ht -> writable_share shk -> Zlength wc = 256 -> Zlength a0 = 256 ->
  sublist 0 (Zlength (ht_weights ht)) wc = map (fun x => vint x) (ht_weights ht) ->
  semax x2_Delta
    (PROP ()
     LOCAL (temp _maxW (vint (maxw ht)); temp _rankStart (offset_val 680 pk); temp _wksp pk;
            temp _dt (offset_val 4 dtab); temp _maxTableLog (vint L); temp _iSize (Vlong (Int64.repr sz));
            temp _DTable dtab; lvar _dtd t_dtdesc vdtd; lvar _nbSymbols tuint vnb; lvar _tableLog tuint vtl)
     SEP (data_at Tsh tuint (vint (Zlength (ht_weights ht))) vnb;
          field_at shk t_x2wksp (DOT _rankStart0) (x2_rsA ht) pk;
          field_at shk t_x2wksp (DOT _weightList) wc pk;
          field_at shk t_x2wksp (DOT _sortedSymbol) a0 pk;
          F))
    x2_sort_stmt
    (normal_ret_assert
      (PROP ()
       LOCAL (temp _maxW (vint (maxw ht)); temp _rankStart (offset_val 680 pk); temp _wksp pk;
              temp _dt (offset_val 4 dtab); temp _maxTableLog (vint L); temp _iSize (Vlong (Int64.repr sz));
              temp _DTable dtab; lvar _dtd t_dtdesc vdtd; lvar _nbSymbols tuint vnb; lvar _tableLog tuint vtl)
       SEP (data_at Tsh tuint (vint (Zlength (ht_weights ht))) vnb;
            EX rs: list val, !! x2_rs_ok ht rs && field_at shk t_x2wksp (DOT _rankStart0) rs pk;
            field_at shk t_x2wksp (DOT _weightList) wc pk;
            field_at shk t_x2wksp (DOT _sortedSymbol) (sort_arr ht (length (ht_weights ht)) a0) pk;
            F))).

(* Statement 17: rankVal[0] (the first cell of each weight in the 2^L table) and the rows minBits ..
   L - minBits (rankVal[c][w] = rankVal[0][w] >> c). *)
Definition x2_rv_ok_stmt : Prop :=
  forall (Espec: OracleKind) (F: mpred) (ht: huf_table) (sz L: Z) (dtab pk vtl vnb vdtd: val) (shk: share),
  x2_count -> x2_layout -> x2_ht_ok ht -> writable_share shk -> ht_log ht <= L <= HUF_TABLELOG_MAX ->
  semax x2_Delta
    (PROP ()
     LOCAL (temp _maxW (vint (maxw ht)); temp _rankStart (offset_val 680 pk); temp _wksp pk;
            temp _dt (offset_val 4 dtab); temp _maxTableLog (vint L); temp _iSize (Vlong (Int64.repr sz));
            temp _DTable dtab; lvar _dtd t_dtdesc vdtd; lvar _nbSymbols tuint vnb; lvar _tableLog tuint vtl)
     SEP (data_at Tsh tuint (vint (ht_log ht)) vtl;
          field_at shk t_x2wksp (DOT _rankStats) (rank_stats (ht_weights ht)) pk;
          field_at_ shk t_x2wksp (DOT _rankVal) pk;
          F))
    x2_rv_stmt
    (normal_ret_assert
      (PROP ()
       LOCAL (temp _maxW (vint (maxw ht)); temp _rankStart (offset_val 680 pk); temp _wksp pk;
              temp _dt (offset_val 4 dtab); temp _maxTableLog (vint L); temp _iSize (Vlong (Int64.repr sz));
              temp _DTable dtab; lvar _dtd t_dtdesc vdtd; lvar _nbSymbols tuint vnb; lvar _tableLog tuint vtl)
       SEP (data_at Tsh tuint (vint (ht_log ht)) vtl;
            field_at shk t_x2wksp (DOT _rankStats) (rank_stats (ht_weights ht)) pk;
            EX rv: list (list val), !! x2_rv_ok ht L rv && field_at shk t_x2wksp (DOT _rankVal) rv pk;
            F))).

Lemma x2_rs_split (shk: share) (pk: val) (l: list val) :
  field_compatible t_x2wksp nil pk -> Zlength l = 15 ->
  field_at shk t_x2wksp (DOT _rankStart0) l pk =
  data_at shk tuint (Znth 0 l) (offset_val 676 pk) * data_at shk (tarray tuint 14) (sublist 1 15 l) (offset_val 680 pk).
Proof.
  intros Hfc Hl.
  rewrite field_at_data_at. rewrite field_compatible_field_address by auto with field_compatible.
  simpl nested_field_type. simpl nested_field_offset.
  assert (E: l = sublist 0 1 l ++ sublist 1 15 l) by list_solve. rewrite E at 1.
  rewrite (split2_data_at_Tarray_app 1 15 shk tuint (sublist 0 1 l) (sublist 1 15 l)) by list_solve.
  rewrite (sublist_one 0 1 l) by lia. erewrite data_at_singleton_array_eq by reflexivity. f_equal.
  rewrite field_address0_offset; [simpl; rewrite offset_offset_val; reflexivity|].
  assert (H1: field_compatible t_x2wksp (DOT _rankStart0) pk).
  { apply field_compatible_cons. simpl. split; [unfold in_members; simpl; auto 10 | auto]. }
  apply field_compatible_nested_field in H1. simpl in H1.
  apply field_compatible0_cons. simpl. split; [lia|auto].
Qed.

(* rankStart[1..w-1] filled (rankStart = rankStart0 + 1, 14 cells) *)
Definition x2_rs14 (ht: huf_table) (w: Z) : list val :=
  map (fun i => vint (if andb (1 <=? i) (i <? w) then rstart ht i else 0)) (map Z.of_nat (seq 0 14)).

Lemma x2_rs14_len ht w : Zlength (x2_rs14 ht w) = 14.
Proof. reflexivity. Qed.

Lemma x2_rs14_Znth ht w i : 0 <= i < 14 ->
  Znth i (x2_rs14 ht w) = vint (if andb (1 <=? i) (i <? w) then rstart ht i else 0).
Proof.
  intros Hi. unfold x2_rs14. rewrite Znth_map by (rewrite Zlength_map; change (Zlength (seq 0 14)) with 14; lia).
  replace (Znth i (map Z.of_nat (seq 0 14))) with i; [reflexivity|].
  assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/
          i = 10 \/ i = 11 \/ i = 12 \/ i = 13) as Hc by lia.
  repeat destruct Hc as [Hc|Hc]; subst i; reflexivity.
Qed.

Lemma x2_seqZ (n: nat) (k: Z) : 0 <= k < Z.of_nat n -> Znth k (map Z.of_nat (seq 0 n)) = k.
Proof.
  intros Hk. rewrite Znth_map by (rewrite Zlength_correct, length_seq; lia).
  unfold Znth. destruct (zlt k 0); [lia|].
  rewrite seq_nth by lia. destruct (Z_lt_dec k 0); [lia|]. rewrite Nat.add_0_l, Z2Nat.id by lia. reflexivity.
Qed.

Lemma x2_rstart : x2_rstart_ok.
Proof.
  intros Espec F ht sz L dtab pk vtl vnb vdtd shk Hc Hht Hsh.
  destruct (xc_maxw Hc ht Hht) as (Hmw & _ & _ & Hrs).
  unfold x2_rstart_stmt.
  assert_PROP (field_compatible t_x2wksp (DOT _rankStats) pk) as Hfc1 by entailer!.
  assert (Hfc: field_compatible t_x2wksp nil pk) by (apply field_compatible_cons in Hfc1; simpl in Hfc1; tauto).
  assert (Hlog: ht_log ht <= 12) by (destruct Hht as [[[_ Hl] _] _]; exact Hl).
  destruct (xc_rstart Hc ht 1 Hht ltac:(lia)) as (Hr1 & _).
  rewrite x2_rs_split by (auto; reflexivity).
  replace (sublist 1 15 (Zrepeat (vint 0) 15)) with (x2_rs14 ht 1).
  2: { apply Znth_eq_ext; [reflexivity|]. intros i Hi. rewrite x2_rs14_len in Hi.
       rewrite x2_rs14_Znth by lia. rewrite Znth_sublist by lia. rewrite Znth_Zrepeat by lia.
       destruct (1 <=? i) eqn:E1, (i <? 1) eqn:E2; try reflexivity. apply Z.leb_le in E1; apply Z.ltb_lt in E2; lia. }
  Intros. forward.
  forward_for_simple_bound (maxw ht + 1) (EX w: Z,
    PROP ()
    LOCAL (temp _nextRankStart (vint (rstart ht w));
           temp _maxW (vint (maxw ht)); temp _rankStart (offset_val 680 pk); temp _wksp pk;
           temp _dt (offset_val 4 dtab); temp _maxTableLog (vint L); temp _iSize (Vlong (Int64.repr sz));
           temp _DTable dtab; lvar _dtd t_dtdesc vdtd; lvar _nbSymbols tuint vnb; lvar _tableLog tuint vtl)
    SEP (field_at shk t_x2wksp (DOT _rankStats) (rank_stats (ht_weights ht)) pk;
         data_at shk tuint (Znth 0 (Zrepeat (vint 0) 15)) (offset_val 676 pk);
         data_at shk (tarray tuint 14) (x2_rs14 ht w) (offset_val 680 pk);
         F))%assert.
  - entailer!.
  - forward.
    assert (Hi12: 0 <= i <= 12) by lia.
    forward.
    { entailer!. rewrite Hrs by lia. auto. }
    rewrite Hrs by lia.
    forward.
    forward.
    entailer!.
    { destruct (xc_rstart Hc ht i Hht ltac:(lia)) as (_ & Hn & _). rewrite Hn. reflexivity. }
    apply derives_refl'. f_equal. apply Znth_eq_ext; [list_solve|]. intros j Hj.
    rewrite Zlength_upd_Znth, x2_rs14_len in Hj. rewrite x2_rs14_Znth by lia.
    destruct (Z.eq_dec j i) as [->|Hne].
    + rewrite upd_Znth_same by (rewrite x2_rs14_len; lia).
      replace ((1 <=? i) && (i <? i + 1))%bool with true; [reflexivity|].
      symmetry. apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
    + rewrite upd_Znth_diff by (rewrite ?x2_rs14_len; lia). rewrite x2_rs14_Znth by lia.
      replace (j <? i + 1) with (j <? i); [reflexivity|].
      destruct (Z.ltb_spec j i), (Z.ltb_spec j (i + 1)); auto; lia.
  - forward.
    forward.
    entailer!.
    rewrite (x2_rs_split shk pk (x2_rsA ht)) by (auto; reflexivity).
    apply derives_refl'. f_equal. f_equal.
    apply Znth_eq_ext; [list_solve|]. intros j Hj.
    rewrite !Zlength_upd_Znth, x2_rs14_len in Hj.
    unfold x2_rsA. rewrite Znth_sublist by lia.
    rewrite Znth_map by (rewrite Zlength_map, Zlength_correct, length_seq; simpl; lia).
    rewrite x2_seqZ by (simpl; lia).
    destruct (Z.eq_dec j (maxw ht + 1)) as [->|Hne1];
      [rewrite upd_Znth_same by (rewrite Zlength_upd_Znth, x2_rs14_len; lia)
      |rewrite upd_Znth_diff by (rewrite ?Zlength_upd_Znth, ?x2_rs14_len; lia)].
    + destruct (Z.eqb_spec (maxw ht + 1 + 1) 0), (Z.eqb_spec (maxw ht + 1 + 1) 1),
        (Z.leb_spec (maxw ht + 1 + 1) (maxw ht + 2)); try lia.
      f_equal. f_equal. f_equal. lia.
    + destruct (Z.eq_dec j 0) as [->|Hne0];
        [rewrite upd_Znth_same by (rewrite x2_rs14_len; lia)
        |rewrite upd_Znth_diff by (rewrite ?x2_rs14_len; lia)].
      * destruct (Z.eqb_spec (0 + 1) 0), (Z.eqb_spec (0 + 1) 1); try lia. reflexivity.
      * rewrite x2_rs14_Znth by lia.
        destruct (Z.leb_spec 1 j), (Z.ltb_spec j (maxw ht + 1)), (Z.eqb_spec (j + 1) 0), (Z.eqb_spec (j + 1) 1),
          (Z.leb_spec (j + 1) (maxw ht + 2)); simpl; try lia; try reflexivity.
        f_equal. f_equal. f_equal. lia.
Qed.

(* ---------- statement 16 (x2_sort): helpers ---------- *)

Lemma xs_rs_split (shk: share) (pk: val) (l: list val) :
  field_compatible t_x2wksp nil pk -> Zlength l = 15 ->
  field_at shk t_x2wksp (DOT _rankStart0) l pk =
  data_at shk tuint (Znth 0 l) (offset_val 676 pk) * data_at shk (tarray tuint 14) (sublist 1 15 l) (offset_val 680 pk).
Proof.
  intros Hfc Hl.
  rewrite field_at_data_at. rewrite field_compatible_field_address by auto with field_compatible.
  simpl nested_field_type. simpl nested_field_offset.
  assert (E: l = sublist 0 1 l ++ sublist 1 15 l) by list_solve. rewrite E at 1.
  rewrite (split2_data_at_Tarray_app 1 15 shk tuint (sublist 0 1 l) (sublist 1 15 l)) by list_solve.
  rewrite (sublist_one 0 1 l) by lia. erewrite data_at_singleton_array_eq by reflexivity. f_equal.
  rewrite field_address0_offset; [simpl; rewrite offset_offset_val; reflexivity|].
  assert (H1: field_compatible t_x2wksp (DOT _rankStart0) pk).
  { apply field_compatible_cons. simpl. split; [unfold in_members; simpl; auto 10 | auto]. }
  apply field_compatible_nested_field in H1. simpl in H1.
  apply field_compatible0_cons. simpl. split; [lia|auto].
Qed.

Lemma xs_seqZ (n: nat) (k: Z) : 0 <= k < Z.of_nat n -> Znth k (map Z.of_nat (seq 0 n)) = k.
Proof.
  intros Hk. rewrite Znth_map by (rewrite Zlength_correct, length_seq; lia).
  unfold Znth. destruct (zlt k 0); [lia|].
  rewrite seq_nth by lia. destruct (Z_lt_dec k 0); [lia|]. rewrite Nat.add_0_l, Z2Nat.id by lia. reflexivity.
Qed.

(* the symbols s' < s of weight w *)
Definition xs_cb (ht: huf_table) (s w: Z) : Z :=
  Zlength (filter (fun s' => hw ht s' =? w) (map Z.of_nat (seq 0 (Z.to_nat s)))).

(* rankStart (= rankStart0 + 1, 14 cells) after the symbols 0 .. s-1 *)
Definition xs_rs14 (ht: huf_table) (s: Z) : list val :=
  map (fun i => vint (if i =? 0 then rstart ht (maxw ht + 1) + xs_cb ht s 0
                      else if i <=? maxw ht + 1 then rstart ht i + xs_cb ht s i else 0))
      (map Z.of_nat (seq 0 14)).

Lemma xs_rs14_len ht s : Zlength (xs_rs14 ht s) = 14.
Proof. reflexivity. Qed.

Lemma xs_rs14_Znth {d: Inhabitant val} ht s i : 0 <= i < 14 ->
  Znth i (xs_rs14 ht s) = vint (if i =? 0 then rstart ht (maxw ht + 1) + xs_cb ht s 0
                                else if i <=? maxw ht + 1 then rstart ht i + xs_cb ht s i else 0).
Proof.
  intros Hi. unfold xs_rs14. rewrite Znth_map by (rewrite Zlength_map, Zlength_correct, length_seq; simpl; lia).
  rewrite xs_seqZ by (simpl; lia). reflexivity.
Qed.

Lemma xs_cb_0 ht w : xs_cb ht 0 w = 0.
Proof. reflexivity. Qed.

Lemma xs_cb_S ht s w : 0 <= s ->
  xs_cb ht (s + 1) w = xs_cb ht s w + (if hw ht s =? w then 1 else 0).
Proof.
  intros Hs. unfold xs_cb. rewrite Z2Nat.inj_add by lia. rewrite seq_app, map_app, filter_app, Zlength_app.
  simpl. rewrite Z2Nat.id by lia. destruct (hw ht s =? w); reflexivity.
Qed.

Lemma xs_count_map (f: Z -> Z) (w: Z) (xs: list Z) :
  Zlength (filter (fun s => f s =? w) xs) = Zlength (filter (fun x => x =? w) (map f xs)).
Proof.
  induction xs as [|x xs IH]; [reflexivity|]. simpl.
  destruct (f x =? w); rewrite ?Zlength_cons, IH; reflexivity.
Qed.

Lemma xs_map_nth (l: list Z) : map (fun s => nth (Z.to_nat s) l 0) (map Z.of_nat (seq 0 (length l))) = l.
Proof.
  rewrite map_map. rewrite (map_ext _ (fun x => nth x l 0)) by (intros; rewrite Nat2Z.id; reflexivity).
  apply nth_ext with (d := 0) (d' := 0); [rewrite length_map, length_seq; reflexivity|].
  intros k Hk. rewrite length_map, length_seq in Hk.
  rewrite (nth_indep _ 0 ((fun x => nth x l 0) 0%nat)) by (rewrite length_map, length_seq; lia).
  change (nth 0 l 0) with ((fun x => nth x l 0) 0%nat). rewrite map_nth, seq_nth by lia. reflexivity.
Qed.

Lemma xs_cb_all ht w : xs_cb ht (Zlength (ht_weights ht)) w = cntw ht w.
Proof.
  unfold xs_cb, cntw, hw. rewrite ZtoNat_Zlength.
  rewrite (xs_count_map (fun s => nth (Z.to_nat s) (ht_weights ht) 0)). rewrite xs_map_nth. reflexivity.
Qed.

Lemma xs_le_max (l: list Z) x : In x l -> x <= fold_right Z.max 0 l.
Proof. induction l as [|y l IH]; simpl; [tauto|]. intros [->|H]; [lia|]. specialize (IH H); lia. Qed.

Lemma xs_hw ht s : x2_ht_ok ht -> 0 <= s < Zlength (ht_weights ht) -> 0 <= hw ht s <= maxw ht.
Proof.
  intros (_ & _ & Hf) Hs. unfold hw, maxw.
  assert (Hin: In (nth (Z.to_nat s) (ht_weights ht) 0) (ht_weights ht)).
  { apply nth_In. rewrite Zlength_correct in Hs. lia. }
  rewrite Forall_forall in Hf. specialize (Hf _ Hin). split; [lia|]. apply xs_le_max; exact Hin.
Qed.

Lemma xs_hw_Znth ht s : 0 <= s -> Znth s (ht_weights ht) = hw ht s.
Proof. intros Hs. unfold Znth, hw. destruct (Z_lt_dec s 0); [lia|reflexivity]. Qed.

Lemma xs_sort_arr_S ht s a0 : 0 <= s ->
  sort_arr ht (Z.to_nat (s + 1)) a0 = upd_Znth (sort_pos ht s) (sort_arr ht (Z.to_nat s) a0) (vint s).
Proof.
  intros Hs. unfold sort_arr. rewrite Z2Nat.inj_add by lia. rewrite seq_app, fold_left_app. simpl.
  rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma xs_sort_arr_len ht k a0 : Zlength (sort_arr ht k a0) = Zlength a0.
Proof.
  unfold sort_arr. generalize a0. induction (seq 0 k) as [|x l IH]; intros a; [reflexivity|].
  simpl. rewrite IH. apply Zlength_upd_Znth.
Qed.

Lemma xs_bucket {d: Inhabitant val} ht s : x2_ht_ok ht -> maxw ht <= 12 -> 0 <= s < Zlength (ht_weights ht) ->
  Znth (hw ht s) (xs_rs14 ht s) = vint (sort_pos ht s).
Proof.
  intros Hht Hm Hs. pose proof (xs_hw ht s Hht Hs) as Hw.
  rewrite xs_rs14_Znth by lia. unfold sort_pos, xs_cb.
  destruct (Z.eqb_spec (hw ht s) 0) as [E|E]; [rewrite E; reflexivity|].
  destruct (Z.leb_spec (hw ht s) (maxw ht + 1)); [|lia]. reflexivity.
Qed.

Lemma xs_rs14_step ht s : x2_ht_ok ht -> maxw ht <= 12 -> 0 <= s < Zlength (ht_weights ht) ->
  upd_Znth (hw ht s) (xs_rs14 ht s) (vint (sort_pos ht s + 1)) = xs_rs14 ht (s + 1).
Proof.
  intros Hht Hm Hs. pose proof (xs_hw ht s Hht Hs) as Hw.
  apply Znth_eq_ext; [rewrite Zlength_upd_Znth, !xs_rs14_len; reflexivity|].
  intros j Hj. rewrite Zlength_upd_Znth, xs_rs14_len in Hj.
  rewrite (xs_rs14_Znth ht (s + 1)) by lia.
  destruct (Z.eq_dec j (hw ht s)) as [->|Hne].
  - rewrite upd_Znth_same by (rewrite xs_rs14_len; lia).
    unfold sort_pos. fold (xs_cb ht s (hw ht s)).
    destruct (Z.eqb_spec (hw ht s) 0) as [E|E].
    + rewrite E. rewrite xs_cb_S by lia. rewrite E. simpl. rewrite Z.add_assoc. reflexivity.
    + destruct (Z.leb_spec (hw ht s) (maxw ht + 1)); [|lia]. rewrite xs_cb_S, Z.eqb_refl by lia. rewrite Z.add_assoc. reflexivity.
  - rewrite upd_Znth_diff by (rewrite ?xs_rs14_len; lia). rewrite xs_rs14_Znth by lia.
    rewrite !(xs_cb_S ht s) by lia.
    destruct (Z.eqb_spec j 0) as [->|Hj0].
    + destruct (Z.eqb_spec (hw ht s) 0); [lia|]. rewrite Z.add_0_r; reflexivity.
    + destruct (Z.leb_spec j (maxw ht + 1)); [|reflexivity].
      destruct (Z.eqb_spec (hw ht s) j); [lia|]. rewrite Z.add_0_r; reflexivity.
Qed.

Lemma xs_rs_final ht : x2_count -> x2_ht_ok ht ->
  x2_rs_ok ht (vint 0 :: upd_Znth 0 (xs_rs14 ht (Zlength (ht_weights ht))) (vint 0)).
Proof.
  intros Hc Hht. destruct (xc_maxw Hc ht Hht) as (Hmw & _).
  assert (Hlog: ht_log ht <= 12) by (destruct Hht as [[[_ Hl] _] _]; exact Hl).
  split; [rewrite Zlength_cons, Zlength_upd_Znth, xs_rs14_len; reflexivity|].
  intros w Hw. rewrite Znth_pos_cons by lia.
  destruct (Z.eq_dec w 1) as [->|Hne].
  - rewrite upd_Znth_same by (rewrite xs_rs14_len; lia).
    destruct (xc_rstart Hc ht 1 Hht ltac:(lia)) as (Hr1 & _). rewrite Hr1. reflexivity.
  - rewrite upd_Znth_diff by (rewrite ?xs_rs14_len; lia). rewrite xs_rs14_Znth by lia.
    destruct (Z.eqb_spec (w - 1) 0); [lia|]. destruct (Z.leb_spec (w - 1) (maxw ht + 1)); [|lia].
    rewrite xs_cb_all. destruct (xc_rstart Hc ht (w - 1) Hht ltac:(lia)) as (_ & Hn & _).
    replace (w - 1 + 1) with w in Hn by lia. rewrite Hn. reflexivity.
Qed.

Lemma x2_sort : x2_sort_ok.
Proof.
  intros Espec F ht sz L dtab pk vtl vnb vdtd shk wc a0 Hc Hht Hsh Hwc Ha0 Hsub.
  destruct (xc_maxw Hc ht Hht) as (Hmw & _ & _ & _).
  assert (Hlog: ht_log ht <= 12) by (destruct Hht as [[[_ Hl] _] _]; exact Hl).
  assert (Hn: 2 <= Zlength (ht_weights ht) <= 256) by (destruct Hht as (_ & Hn & _); exact Hn).
  unfold x2_sort_stmt.
  assert_PROP (field_compatible t_x2wksp (DOT _rankStart0) pk) as Hfc1 by entailer!.
  assert (Hfc: field_compatible t_x2wksp nil pk) by (apply field_compatible_cons in Hfc1; simpl in Hfc1; tauto).
  rewrite xs_rs_split by (auto; reflexivity).
  replace (Znth 0 (x2_rsA ht)) with (vint 0) by reflexivity.
  replace (sublist 1 15 (x2_rsA ht)) with (xs_rs14 ht 0).
  2: { apply Znth_eq_ext; [reflexivity|]. intros i Hi. rewrite xs_rs14_len in Hi.
       rewrite xs_rs14_Znth by lia. rewrite Znth_sublist by lia.
       unfold x2_rsA. rewrite Znth_map by (rewrite Zlength_map, Zlength_correct, length_seq; simpl; lia).
       rewrite xs_seqZ by (simpl; lia). rewrite !xs_cb_0.
       destruct (Z.eqb_spec i 0), (Z.eqb_spec (i + 1) 0), (Z.eqb_spec (i + 1) 1), (Z.leb_spec i (maxw ht + 1)),
         (Z.leb_spec (i + 1) (maxw ht + 2)); try lia; subst; rewrite ?Z.add_0_r; try reflexivity.
       f_equal. f_equal. f_equal. lia. }
  Intros. forward.
  forward_loop
    (EX s: Z,
     PROP (0 <= s <= Zlength (ht_weights ht))
     LOCAL (temp _s (vint s); temp _maxW (vint (maxw ht)); temp _rankStart (offset_val 680 pk); temp _wksp pk;
            temp _dt (offset_val 4 dtab); temp _maxTableLog (vint L); temp _iSize (Vlong (Int64.repr sz));
            temp _DTable dtab; lvar _dtd t_dtdesc vdtd; lvar _nbSymbols tuint vnb; lvar _tableLog tuint vtl)
     SEP (data_at Tsh tuint (vint (Zlength (ht_weights ht))) vnb; data_at shk tuint (vint 0) (offset_val 676 pk);
          data_at shk (tarray tuint 14) (xs_rs14 ht (s)) (offset_val 680 pk);
          field_at shk t_x2wksp (DOT _weightList) wc pk;
          field_at shk t_x2wksp (DOT _sortedSymbol) (sort_arr ht (Z.to_nat (s)) a0) pk; F))%assert
  continue:
    (EX s: Z,
     PROP (0 <= s < Zlength (ht_weights ht))
     LOCAL (temp _s (vint s); temp _maxW (vint (maxw ht)); temp _rankStart (offset_val 680 pk); temp _wksp pk;
            temp _dt (offset_val 4 dtab); temp _maxTableLog (vint L); temp _iSize (Vlong (Int64.repr sz));
            temp _DTable dtab; lvar _dtd t_dtdesc vdtd; lvar _nbSymbols tuint vnb; lvar _tableLog tuint vtl)
     SEP (data_at Tsh tuint (vint (Zlength (ht_weights ht))) vnb; data_at shk tuint (vint 0) (offset_val 676 pk);
          data_at shk (tarray tuint 14) (xs_rs14 ht (s + 1)) (offset_val 680 pk);
          field_at shk t_x2wksp (DOT _weightList) wc pk;
          field_at shk t_x2wksp (DOT _sortedSymbol) (sort_arr ht (Z.to_nat (s + 1)) a0) pk; F))%assert
  break:
    (PROP ()
     LOCAL (temp _maxW (vint (maxw ht)); temp _rankStart (offset_val 680 pk); temp _wksp pk;
            temp _dt (offset_val 4 dtab); temp _maxTableLog (vint L); temp _iSize (Vlong (Int64.repr sz));
            temp _DTable dtab; lvar _dtd t_dtdesc vdtd; lvar _nbSymbols tuint vnb; lvar _tableLog tuint vtl)
     SEP (data_at Tsh tuint (vint (Zlength (ht_weights ht))) vnb; data_at shk tuint (vint 0) (offset_val 676 pk);
          data_at shk (tarray tuint 14) (xs_rs14 ht (Zlength (ht_weights ht))) (offset_val 680 pk);
          field_at shk t_x2wksp (DOT _weightList) wc pk;
          field_at shk t_x2wksp (DOT _sortedSymbol) (sort_arr ht (Z.to_nat (Zlength (ht_weights ht))) a0) pk; F))%assert.
  - Exists 0. entailer!.
  - Intros s.
    forward.
    forward_if.
    + assert (Hs: 0 <= s < Zlength (ht_weights ht)) by lia.
      pose proof (xs_hw ht s Hht Hs) as Hw.
      assert (Hwv: forall {d: Inhabitant val}, Znth s wc = vint (hw ht s)).
      { intros d. replace (Znth s wc) with (Znth s (sublist 0 (Zlength (ht_weights ht)) wc))
          by (rewrite Znth_sublist by lia; f_equal; lia).
        rewrite Hsub, Znth_map by lia. rewrite xs_hw_Znth by lia. reflexivity. }
      forward.
      { entailer!. rewrite Hwv. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
      rewrite Hwv.
      assert (Hm12: maxw ht <= 12) by lia.
      forward.
      { entailer!. rewrite (xs_bucket ht s) by auto. simpl; auto. }
      rewrite (xs_bucket ht s) by auto.
      pose proof (xc_sort_pos Hc ht s Hht Hs) as Hsp.
      forward.
      forward.
      forward.
      Exists s. rewrite xs_sort_arr_S by lia. rewrite <- xs_rs14_step by auto.
      rewrite add_repr.
      rewrite !zero_ext_inrange by (rewrite ?zero_ext_inrange, Int.unsigned_repr by (try rewrite Int.unsigned_repr; simpl; rep_lia); simpl; rep_lia).
      entailer!.
    + forward. assert (s = Zlength (ht_weights ht)) by lia. subst s. entailer!.
  - Intros s. forward. Exists (s + 1). entailer!.
  - forward.
    Exists (vint 0 :: upd_Znth 0 (xs_rs14 ht (Zlength (ht_weights ht))) (vint 0)).
    rewrite (xs_rs_split shk pk (vint 0 :: _)) by (auto; rewrite Zlength_cons, Zlength_upd_Znth, xs_rs14_len; reflexivity).
    rewrite Znth_0_cons, sublist_1_cons, sublist_same by (rewrite ?Zlength_upd_Znth, ?xs_rs14_len; lia).
    rewrite ZtoNat_Zlength.
    entailer!.
    apply xs_rs_final; auto.
Qed.

(* ---------- x2_rv: rankVal row by row ---------- *)

(* row c with the weights 1 .. n-1 written (rankVal[c][w] = rv0 w >> c) *)
Definition rv_row (ht: huf_table) (L c n: Z) : list val :=
  map (fun j => if andb (1 <=? j) (j <? n) then vint (rv0 ht L j / 2 ^ c) else Vundef) (map Z.of_nat (seq 0 13)).
(* rankVal with row 0 and the rows minBits .. c-1 complete, and row c written up to weight n-1 *)
Definition rv_rows (ht: huf_table) (L c n: Z) : list (list val) :=
  map (fun i => if i =? c then rv_row ht L i n
                else if orb (i =? 0) (andb (minbits ht <=? i) (i <? c)) then rv_row ht L i (maxw ht + 1)
                else Zrepeat Vundef 13) (map Z.of_nat (seq 0 12)).

Lemma rv_row_len ht L c n : Zlength (rv_row ht L c n) = 13.
Proof. reflexivity. Qed.

Lemma rv_row_Znth ht L c n j : 0 <= j < 13 ->
  Znth j (rv_row ht L c n) = if andb (1 <=? j) (j <? n) then vint (rv0 ht L j / 2 ^ c) else Vundef.
Proof.
  intros. unfold rv_row. rewrite Znth_map by (rewrite Zlength_map, Zlength_correct, seq_length; simpl; lia).
  rewrite Znth_map by (rewrite Zlength_correct, seq_length; simpl; lia).
  rewrite <- nth_Znth by (rewrite Zlength_correct, seq_length; simpl; lia).
  rewrite seq_nth by lia. simpl. rewrite Z2Nat.id by lia. auto.
Qed.

Lemma rv_row_1 ht L c : rv_row ht L c 1 = Zrepeat Vundef 13.
Proof.
  apply Znth_eq_ext. { rewrite rv_row_len. reflexivity. }
  intros j Hj. rewrite rv_row_len in Hj. rewrite rv_row_Znth by lia. rewrite Znth_Zrepeat by lia.
  destruct (1 <=? j) eqn:E1, (j <? 1) eqn:E2; simpl; auto; lia.
Qed.

Lemma rv_row_upd ht L c n : 1 <= n < 13 ->
  upd_Znth n (rv_row ht L c n) (vint (rv0 ht L n / 2 ^ c)) = rv_row ht L c (n + 1).
Proof.
  intros. apply Znth_eq_ext. { rewrite Zlength_upd_Znth, !rv_row_len. auto. }
  intros j Hj. rewrite Zlength_upd_Znth, rv_row_len in Hj.
  destruct (Z.eq_dec j n) as [->|Hne].
  - rewrite upd_Znth_same by (rewrite rv_row_len; lia). rewrite rv_row_Znth by lia.
    replace (andb (1 <=? n) (n <? n + 1)) with true by (symmetry; apply andb_true_iff; split; lia). auto.
  - rewrite upd_Znth_diff by (rewrite ?rv_row_len; lia). rewrite !rv_row_Znth by lia.
    destruct (1 <=? j) eqn:E1, (j <? n) eqn:E2, (j <? n + 1) eqn:E3; simpl; auto; lia.
Qed.

Lemma rv_row_upd0 ht L n : 1 <= n < 13 ->
  upd_Znth n (rv_row ht L 0 n) (vint (rv0 ht L n)) = rv_row ht L 0 (n + 1).
Proof. intros. rewrite <- rv_row_upd by lia. rewrite Z.pow_0_r, Z.div_1_r. auto. Qed.

Lemma rv_rows_len ht L c n : Zlength (rv_rows ht L c n) = 12.
Proof. reflexivity. Qed.

Lemma rv_rows_Znth ht L c n i : 0 <= i < 12 ->
  Znth i (rv_rows ht L c n) =
  if i =? c then rv_row ht L i n
  else if orb (i =? 0) (andb (minbits ht <=? i) (i <? c)) then rv_row ht L i (maxw ht + 1)
  else Zrepeat Vundef 13.
Proof.
  intros. unfold rv_rows. rewrite Znth_map by (rewrite Zlength_map, Zlength_correct, seq_length; simpl; lia).
  rewrite Znth_map by (rewrite Zlength_correct, seq_length; simpl; lia).
  rewrite <- nth_Znth by (rewrite Zlength_correct, seq_length; simpl; lia).
  rewrite seq_nth by lia. simpl. rewrite Z2Nat.id by lia. auto.
Qed.

Lemma rv_rows_init ht L : rv_rows ht L 0 1 = Zrepeat (Zrepeat Vundef 13) 12.
Proof.
  apply Znth_eq_ext. { reflexivity. }
  intros i Hi. rewrite rv_rows_len in Hi. rewrite rv_rows_Znth by lia. rewrite Znth_Zrepeat by lia.
  destruct (i =? 0) eqn:E0; [apply rv_row_1|].
  destruct (minbits ht <=? i) eqn:E1, (i <? 0) eqn:E2; simpl; auto; lia.
Qed.

Lemma rv_rows_next ht L c c' : 1 <= minbits ht -> 1 <= maxw ht <= 12 ->
  (c = 0 /\ c' = minbits ht \/ minbits ht <= c /\ c' = c + 1) ->
  rv_rows ht L c (maxw ht + 1) = rv_rows ht L c' 1.
Proof.
  intros Hmb Hmw Hc. apply Znth_eq_ext. { reflexivity. }
  intros i Hi. rewrite rv_rows_len in Hi. rewrite !rv_rows_Znth by lia.
  destruct (i =? c) eqn:Ec, (i =? c') eqn:Ec', (i =? 0) eqn:E0, (minbits ht <=? i) eqn:E1, (i <? c) eqn:E2,
    (i <? c') eqn:E3; simpl; rewrite ?rv_row_1; auto; lia.
Qed.

Lemma rv_rows_upd ht L c n : 0 <= c < 12 ->
  upd_Znth c (rv_rows ht L c n) (rv_row ht L c (n + 1)) = rv_rows ht L c (n + 1).
Proof.
  intros. apply Znth_eq_ext. { rewrite Zlength_upd_Znth. reflexivity. }
  intros i Hi. rewrite Zlength_upd_Znth, rv_rows_len in Hi.
  destruct (Z.eq_dec i c) as [->|Hne].
  - rewrite upd_Znth_same by (rewrite rv_rows_len; lia). rewrite rv_rows_Znth, Z.eqb_refl by lia. auto.
  - rewrite upd_Znth_diff by (rewrite ?rv_rows_len; lia). rewrite !rv_rows_Znth by lia.
    destruct (i =? c) eqn:E; [lia|]. auto.
Qed.

Lemma rv_rows_row ht L c n : 0 <= c < 12 -> Znth c (rv_rows ht L c n) = rv_row ht L c n.
Proof. intros. rewrite rv_rows_Znth, Z.eqb_refl by lia. auto. Qed.

Lemma rv_rows_row0 ht L c n : 1 <= c -> Znth 0 (rv_rows ht L c n) = rv_row ht L 0 (maxw ht + 1).
Proof. intros. rewrite rv_rows_Znth by lia. destruct (0 =? c) eqn:E; [lia|]. auto. Qed.

Lemma rv_rows_ok ht L ce : 1 <= minbits ht -> 1 <= ce <= 12 -> L - minbits ht + 1 <= ce -> 1 <= maxw ht <= 12 ->
  x2_rv_ok ht L (rv_rows ht L ce 1).
Proof.
  intros Hmb Hce HL Hmw. split; [reflexivity|]. split.
  { apply Forall_Znth. intros i Hi. rewrite rv_rows_len in Hi. rewrite rv_rows_Znth by lia.
    destruct (i =? _); [reflexivity|]. destruct (orb _ _); reflexivity. }
  intros c Hc. assert (0 <= c < 12) by lia.
  rewrite rv_rows_Znth by lia.
  destruct (c =? ce) eqn:E; [lia|].
  replace (orb (c =? 0) (andb (minbits ht <=? c) (c <? ce))) with true
    by (symmetry; destruct Hc as [->|Hc]; [reflexivity|]; apply orb_true_iff; right; apply andb_true_iff; lia).
  split; [apply rv_row_len|]. intros w Hw. rewrite rv_row_Znth by lia.
  replace (andb (1 <=? w) (w <? maxw ht + 1)) with true by (symmetry; apply andb_true_iff; lia). auto.
Qed.

(* the 12 x 13 array: row c and the rows around it *)
Lemma rv_split sh (rv: list (list val)) p c :
  field_compatible (tarray (tarray tuint 13) 12) nil p -> 0 <= c < 12 -> Zlength rv = 12 ->
  data_at sh (tarray (tarray tuint 13) 12) rv p =
  data_at sh (tarray (tarray tuint 13) c) (sublist 0 c rv) p *
  data_at sh (tarray tuint 13) (Znth c rv) (offset_val (52 * c) p) *
  data_at sh (tarray (tarray tuint 13) (12 - (c + 1))) (sublist (c + 1) 12 rv) (offset_val (52 * (c + 1)) p).
Proof.
  intros FC Hc Hl.
  rewrite <- (data_at_singleton_array_eq sh (tarray tuint 13) (Znth c rv) [Znth c rv]) by reflexivity.
  unfold tarray at 1 2 4 5.
  rewrite (split3_data_at_Tarray sh (tarray tuint 13) 12 c (c + 1) rv rv (sublist 0 c rv) [Znth c rv]
             (sublist (c + 1) 12 rv)); auto; try lia.
  all: try (rewrite sublist_same; auto; lia).
  all: try (rewrite sublist_len_1 by lia; auto).
  all: try (hnf; intros; simpl; auto; fail).
  all: try (split; [lia|]; apply Z.eq_le_incl; symmetry; exact Hl).
  all: try (unfold reptype; simpl; rewrite sublist_len_1 by lia; reflexivity).
  rewrite !field_address0_offset by (apply arr_field_compatible0; auto; lia).
  simpl nested_field_offset. simpl sizeof. rewrite !Z.add_0_l. replace (c + 1 - c) with 1 by lia. auto.
Qed.

Lemma rv_split_upd sh (rv: list (list val)) r p c :
  field_compatible (tarray (tarray tuint 13) 12) nil p -> 0 <= c < 12 -> Zlength rv = 12 ->
  data_at sh (tarray (tarray tuint 13) c) (sublist 0 c rv) p *
  data_at sh (tarray tuint 13) r (offset_val (52 * c) p) *
  data_at sh (tarray (tarray tuint 13) (12 - (c + 1))) (sublist (c + 1) 12 rv) (offset_val (52 * (c + 1)) p) =
  data_at sh (tarray (tarray tuint 13) 12) (upd_Znth c rv r) p.
Proof.
  intros FC Hc Hl. rewrite (rv_split sh (upd_Znth c rv r) p c) by (rewrite ?Zlength_upd_Znth; auto).
  rewrite upd_Znth_same by lia.
  rewrite sublist_upd_Znth_l by lia. rewrite sublist_upd_Znth_r by lia. auto.
Qed.

Lemma rv_borrow0 sh (rv: list (list val)) p :
  field_compatible (tarray (tarray tuint 13) 12) nil p -> Zlength rv = 12 ->
  data_at sh (tarray (tarray tuint 13) 12) rv p |--
  data_at sh (tarray tuint 13) (Znth 0 rv) p *
  (data_at sh (tarray tuint 13) (Znth 0 rv) p -* data_at sh (tarray (tarray tuint 13) 12) rv p).
Proof.
  intros FC Hl.
  assert (Hp: isptr p) by (destruct FC; auto).
  rewrite (rv_split sh rv p 0) at 1 by (auto; lia).
  change (52 * 0) with 0. rewrite isptr_offset_val_zero by auto.
  apply derives_trans with (data_at sh (tarray tuint 13) (Znth 0 rv) p *
    (data_at sh (tarray (tarray tuint 13) 0) (sublist 0 0 rv) p *
     data_at sh (tarray (tarray tuint 13) (12 - (0 + 1))) (sublist (0 + 1) 12 rv) (offset_val (52 * (0 + 1)) p)));
    [cancel|].
  apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint.
  rewrite (rv_split sh rv p 0) by (auto; lia).
  change (52 * 0) with 0. rewrite isptr_offset_val_zero by auto. cancel.
Qed.

Lemma rv_cnt_nonneg ht w : 0 <= cntw ht w.
Proof. unfold cntw. apply Zlength_nonneg. Qed.

Lemma rv_rv0_mono (XL: x2_layout) ht L w w' : x2_ht_ok ht -> ht_log ht <= L -> 1 <= w <= w' ->
  rv0 ht L w <= rv0 ht L w'.
Proof.
  intros Hok HL Hw.
  replace w' with (w + (w' - w)) by lia.
  assert (Hd: 0 <= w' - w) by lia. revert Hd. generalize (w' - w). intros d Hd.
  pattern d; apply natlike_ind; [rewrite Z.add_0_r; lia| |exact Hd].
  intros x Hx IH. replace (w + Z.succ x) with ((w + x) + 1) by lia.
  destruct (xl_rv0 XL ht L (w + x) Hok HL ltac:(lia)) as [_ [E _]]. rewrite E.
  pose proof (rv_cnt_nonneg ht (w + x)).
  assert (0 <= 2 ^ (L - nbw ht (w + x))) by (apply Z.pow_nonneg; lia).
  nia.
Qed.

Lemma rv_rv0_range (XC: x2_count) (XL: x2_layout) ht L w : x2_ht_ok ht -> ht_log ht <= L -> 1 <= w <= maxw ht + 1 ->
  0 <= rv0 ht L w <= 2 ^ L.
Proof.
  intros Hok HL Hw.
  destruct (xl_rv0 XL ht L 1 Hok HL ltac:(lia)) as [E1 [_ Eend]].
  pose proof (rv_rv0_mono XL ht L 1 w Hok HL ltac:(lia)).
  pose proof (rv_rv0_mono XL ht L w (maxw ht + 1) Hok HL ltac:(lia)). lia.
Qed.

Lemma rv_shl a k : 0 <= k < 32 -> Int.shl (Int.repr a) (Int.repr k) = Int.repr (a * 2 ^ k).
Proof.
  intros. rewrite Int.shl_mul_two_p, Int.unsigned_repr by rep_lia. rewrite two_p_equiv.
  rewrite mul_repr. auto.
Qed.

Lemma rv_shru a k : 0 <= a <= Int.max_unsigned -> 0 <= k < 32 -> Int.shru (Int.repr a) (Int.repr k) = Int.repr (a / 2 ^ k).
Proof.
  intros. rewrite Int.shru_div_two_p, !Int.unsigned_repr by rep_lia. rewrite two_p_equiv. auto.
Qed.

Lemma x2_rv : x2_rv_ok_stmt.
Proof.
  unfold x2_rv_ok_stmt, x2_rv_stmt.
  intros Espec F ht sz L dtab pk vtl vnb vdtd shk XC XL Hok Hsh HL.
  destruct (xc_maxw XC ht Hok) as [Hmw [Hcpos [Hc0 Hrs]]].
  unfold HUF_TABLELOG_MAX in HL.
  assert (Hmb: 1 <= minbits ht <= L) by (unfold minbits; lia).
  assert_PROP (field_compatible t_x2wksp (DOT _rankVal) pk) as Hfc by entailer!.
  assert (Hpk: isptr pk) by (destruct Hfc; auto).
  rewrite field_at__data_at_.
  rewrite field_address_offset by auto. simpl nested_field_type. simpl nested_field_offset.
  rewrite isptr_offset_val_zero by auto.
  assert_PROP (field_compatible (tarray (tarray tuint 13) 12) nil pk) as Hfc2 by entailer!.
  rewrite data_at__eq. change (default_val (tarray (tarray tuint 13) 12)) with (Zrepeat (Zrepeat Vundef 13) 12).
  rewrite <- (rv_rows_init ht L).
  assert (Haddr: forall c ti, (ti = tint \/ ti = tuint) -> 0 <= c <= 12 ->
    force_val (sem_binary_operation' Oadd (tarray (tarray tuint 13) 12) ti
      (eval_field (Tstruct ___gp_HUF_ReadDTableX2_Workspace noattr) _rankVal pk) (vint c)) = offset_val (52 * c) pk).
  { intros c ti Hti Hc. destruct pk; try contradiction.
    destruct Hti; subst ti; unfold eval_field; simpl; f_equal; rewrite Ptrofs.add_zero; f_equal;
      unfold Ptrofs.of_ints, Ptrofs.of_intu, Ptrofs.of_int; rewrite ?Int.signed_repr, ?Int.unsigned_repr by rep_lia;
      rewrite ptrofs_mul_repr; auto. }
  forward.
  rewrite (Haddr 0 tint) by (auto; lia). change (52 * 0) with 0. rewrite isptr_offset_val_zero by auto.
  forward. forward. forward. forward.
  forward_loop (EX w: Z,
    PROP (1 <= w <= maxw ht + 1)
    LOCAL (temp _w__2 (vint w); temp _nextRankVal (vint (rv0 ht L w)); temp _rescale (vint (L - ht_log ht - 1));
           temp _rankVal0 pk; temp _maxW (vint (maxw ht)); temp _rankStart (offset_val 680 pk); temp _wksp pk;
           temp _dt (offset_val 4 dtab); temp _maxTableLog (vint L); temp _iSize (Vlong (Int64.repr sz));
           temp _DTable dtab; lvar _dtd t_dtdesc vdtd; lvar _nbSymbols tuint vnb; lvar _tableLog tuint vtl)
    SEP (data_at Tsh tuint (vint (ht_log ht)) vtl;
         field_at shk t_x2wksp (DOT _rankStats) (rank_stats (ht_weights ht)) pk;
         data_at shk (tarray (tarray tuint 13) 12) (rv_rows ht L 0 w) pk; F))%assert
  continue: (EX w: Z,
    PROP (1 <= w <= maxw ht)
    LOCAL (temp _w__2 (vint w); temp _nextRankVal (vint (rv0 ht L (w + 1))); temp _rescale (vint (L - ht_log ht - 1));
           temp _rankVal0 pk; temp _maxW (vint (maxw ht)); temp _rankStart (offset_val 680 pk); temp _wksp pk;
           temp _dt (offset_val 4 dtab); temp _maxTableLog (vint L); temp _iSize (Vlong (Int64.repr sz));
           temp _DTable dtab; lvar _dtd t_dtdesc vdtd; lvar _nbSymbols tuint vnb; lvar _tableLog tuint vtl)
    SEP (data_at Tsh tuint (vint (ht_log ht)) vtl;
         field_at shk t_x2wksp (DOT _rankStats) (rank_stats (ht_weights ht)) pk;
         data_at shk (tarray (tarray tuint 13) 12) (rv_rows ht L 0 (w + 1)) pk; F))%assert
  break: (
    PROP ()
    LOCAL (temp _rankVal0 pk; temp _maxW (vint (maxw ht)); temp _rankStart (offset_val 680 pk); temp _wksp pk;
           temp _dt (offset_val 4 dtab); temp _maxTableLog (vint L); temp _iSize (Vlong (Int64.repr sz));
           temp _DTable dtab; lvar _dtd t_dtdesc vdtd; lvar _nbSymbols tuint vnb; lvar _tableLog tuint vtl)
    SEP (data_at Tsh tuint (vint (ht_log ht)) vtl;
         field_at shk t_x2wksp (DOT _rankStats) (rank_stats (ht_weights ht)) pk;
         data_at shk (tarray (tarray tuint 13) 12) (rv_rows ht L 0 (maxw ht + 1)) pk; F)).
  { Exists 1. entailer!. }
  { Intros w.
    forward_if.
    2: { forward. assert (w = maxw ht + 1) by lia. subst w. entailer!. }
    forward. forward.
    { entailer!. rewrite Hrs by lia. auto. }
    rewrite Hrs by lia.
    forward.
    { entailer!. change (Int.unsigned Int.iwordsize) with 32. lia. }
    rewrite add_repr, rv_shl, add_repr by lia.
    destruct (xl_rv0 XL ht L w Hok ltac:(lia) ltac:(lia)) as [_ [Erv _]].
    replace (rv0 ht L w + cntw ht w * 2 ^ (w + (L - ht_log ht - 1))) with (rv0 ht L (w + 1))
      by (rewrite Erv; unfold nbw; f_equal; f_equal; f_equal; lia).
    rewrite (rv_split shk (rv_rows ht L 0 w) pk 0) by (auto; lia).
    change (52 * 0) with 0. rewrite isptr_offset_val_zero by auto. rewrite rv_rows_row by lia.
    Intros. forward.
    Exists w. entailer!.
    rewrite rv_row_upd0 by lia. rewrite <- (rv_rows_upd ht L 0 w) by lia.
    rewrite <- (rv_split_upd shk _ _ pk 0) by (auto; rewrite ?rv_rows_len; lia).
    change (52 * 0) with 0. rewrite isptr_offset_val_zero by auto. cancel. }
  { Intros w. forward. Exists (w + 1). entailer!. }
  rewrite (rv_rows_next ht L 0 (minbits ht)) by (auto; lia).
  forward. forward. forward.
  forward_loop (EX c: Z,
    PROP (minbits ht <= c <= Z.max (minbits ht) (L - minbits ht + 1))
    LOCAL (temp _consumed (vint c); temp _minBits (vint (minbits ht));
           temp _rankVal0 pk; temp _maxW (vint (maxw ht)); temp _rankStart (offset_val 680 pk); temp _wksp pk;
           temp _dt (offset_val 4 dtab); temp _maxTableLog (vint L); temp _iSize (Vlong (Int64.repr sz));
           temp _DTable dtab; lvar _dtd t_dtdesc vdtd; lvar _nbSymbols tuint vnb; lvar _tableLog tuint vtl)
    SEP (data_at Tsh tuint (vint (ht_log ht)) vtl;
         field_at shk t_x2wksp (DOT _rankStats) (rank_stats (ht_weights ht)) pk;
         data_at shk (tarray (tarray tuint 13) 12) (rv_rows ht L c 1) pk; F))%assert
  continue: (EX c: Z,
    PROP (minbits ht <= c <= L - minbits ht)
    LOCAL (temp _consumed (vint c); temp _minBits (vint (minbits ht));
           temp _rankVal0 pk; temp _maxW (vint (maxw ht)); temp _rankStart (offset_val 680 pk); temp _wksp pk;
           temp _dt (offset_val 4 dtab); temp _maxTableLog (vint L); temp _iSize (Vlong (Int64.repr sz));
           temp _DTable dtab; lvar _dtd t_dtdesc vdtd; lvar _nbSymbols tuint vnb; lvar _tableLog tuint vtl)
    SEP (data_at Tsh tuint (vint (ht_log ht)) vtl;
         field_at shk t_x2wksp (DOT _rankStats) (rank_stats (ht_weights ht)) pk;
         data_at shk (tarray (tarray tuint 13) 12) (rv_rows ht L (c + 1) 1) pk; F))%assert
  break: (
    PROP ()
    LOCAL (temp _maxW (vint (maxw ht)); temp _rankStart (offset_val 680 pk); temp _wksp pk;
           temp _dt (offset_val 4 dtab); temp _maxTableLog (vint L); temp _iSize (Vlong (Int64.repr sz));
           temp _DTable dtab; lvar _dtd t_dtdesc vdtd; lvar _nbSymbols tuint vnb; lvar _tableLog tuint vtl)
    SEP (data_at Tsh tuint (vint (ht_log ht)) vtl;
         field_at shk t_x2wksp (DOT _rankStats) (rank_stats (ht_weights ht)) pk;
         data_at shk (tarray (tarray tuint 13) 12) (rv_rows ht L (Z.max (minbits ht) (L - minbits ht + 1)) 1) pk; F)).
  { Exists (minbits ht). entailer!. }
  { Intros c.
    forward_if; rewrite add_repr, Int.unsigned_repr in H0 by rep_lia.
    2: { forward. assert (c = Z.max (minbits ht) (L - minbits ht + 1)) by lia. subst c. entailer!. }
    forward.
    rewrite (Haddr c tuint) by (auto; lia).
    forward.
    forward_loop (EX w: Z,
      PROP (1 <= w <= maxw ht + 1)
      LOCAL (temp _w__3 (vint w); temp _rankValPtr (offset_val (52 * c) pk);
             temp _consumed (vint c); temp _minBits (vint (minbits ht));
             temp _rankVal0 pk; temp _maxW (vint (maxw ht)); temp _rankStart (offset_val 680 pk); temp _wksp pk;
             temp _dt (offset_val 4 dtab); temp _maxTableLog (vint L); temp _iSize (Vlong (Int64.repr sz));
             temp _DTable dtab; lvar _dtd t_dtdesc vdtd; lvar _nbSymbols tuint vnb; lvar _tableLog tuint vtl)
      SEP (data_at Tsh tuint (vint (ht_log ht)) vtl;
           field_at shk t_x2wksp (DOT _rankStats) (rank_stats (ht_weights ht)) pk;
           data_at shk (tarray (tarray tuint 13) 12) (rv_rows ht L c w) pk; F))%assert
    continue: (EX w: Z,
      PROP (1 <= w <= maxw ht)
      LOCAL (temp _w__3 (vint w); temp _rankValPtr (offset_val (52 * c) pk);
             temp _consumed (vint c); temp _minBits (vint (minbits ht));
             temp _rankVal0 pk; temp _maxW (vint (maxw ht)); temp _rankStart (offset_val 680 pk); temp _wksp pk;
             temp _dt (offset_val 4 dtab); temp _maxTableLog (vint L); temp _iSize (Vlong (Int64.repr sz));
             temp _DTable dtab; lvar _dtd t_dtdesc vdtd; lvar _nbSymbols tuint vnb; lvar _tableLog tuint vtl)
      SEP (data_at Tsh tuint (vint (ht_log ht)) vtl;
           field_at shk t_x2wksp (DOT _rankStats) (rank_stats (ht_weights ht)) pk;
           data_at shk (tarray (tarray tuint 13) 12) (rv_rows ht L c (w + 1)) pk; F))%assert
    break: (
      PROP ()
      LOCAL (temp _consumed (vint c); temp _minBits (vint (minbits ht));
             temp _rankVal0 pk; temp _maxW (vint (maxw ht)); temp _rankStart (offset_val 680 pk); temp _wksp pk;
             temp _dt (offset_val 4 dtab); temp _maxTableLog (vint L); temp _iSize (Vlong (Int64.repr sz));
             temp _DTable dtab; lvar _dtd t_dtdesc vdtd; lvar _nbSymbols tuint vnb; lvar _tableLog tuint vtl)
      SEP (data_at Tsh tuint (vint (ht_log ht)) vtl;
           field_at shk t_x2wksp (DOT _rankStats) (rank_stats (ht_weights ht)) pk;
           data_at shk (tarray (tarray tuint 13) 12) (rv_rows ht L c (maxw ht + 1)) pk; F)).
    { Exists 1. entailer!. }
    { Intros w.
      forward_if.
      2: { forward. assert (w = maxw ht + 1) by lia. subst w. entailer!. }
      pose proof (rv_rv0_range XC XL ht L w Hok ltac:(lia) ltac:(lia)) as Hrange.
      assert (Hpow: 2 ^ L <= 2 ^ 12) by (apply Z.pow_le_mono_r; lia).
      sep_apply (rv_borrow0 shk (rv_rows ht L c w) pk Hfc2 (rv_rows_len _ _ _ _)).
      rewrite rv_rows_row0 by lia.
      assert (Hz: Znth w (rv_row ht L 0 (maxw ht + 1)) = vint (rv0 ht L w)).
      { rewrite rv_row_Znth by lia. rewrite Z.pow_0_r, Z.div_1_r.
        replace (andb (1 <=? w) (w <? maxw ht + 1)) with true by (symmetry; apply andb_true_iff; lia). auto. }
      Intros. forward.
      { entailer!. change (@Znth val Vundef w (rv_row ht L 0 (maxw ht + 1))) with (Znth w (rv_row ht L 0 (maxw ht + 1))).
        rewrite Hz. auto. }
      change (@Znth val Vundef w (rv_row ht L 0 (maxw ht + 1))) with (Znth w (rv_row ht L 0 (maxw ht + 1))).
      rewrite Hz.
      sep_apply (wand_frame_elim (data_at shk (tarray tuint 13) (rv_row ht L 0 (maxw ht + 1)) pk)).
      rewrite (rv_split shk (rv_rows ht L c w) pk c) by (auto; lia).
      rewrite rv_rows_row by lia.
      Intros. forward.
      { entailer!. change (Int.unsigned Int.iwordsize) with 32. lia. }
      Exists w. entailer!.
      rewrite rv_shru by (rep_lia || lia).
      rewrite rv_row_upd by lia. rewrite <- (rv_rows_upd ht L c w) by lia.
      rewrite <- (rv_split_upd shk _ _ pk c) by (auto; rewrite ?rv_rows_len; lia).
      cancel. }
    { Intros w. forward. Exists (w + 1). entailer!. }
    Exists c. entailer!.
    rewrite (rv_rows_next ht L c (c + 1)) by (auto; lia). auto. }
  { Intros c. forward. Exists (c + 1). entailer!. }
  unfold POSTCONDITION, abbreviate. simpl RA_normal.
  Exists (rv_rows ht L (Z.max (minbits ht) (L - minbits ht + 1)) 1).
  rewrite (field_at_data_at shk t_x2wksp (DOT _rankVal)), field_address_offset by auto.
  simpl nested_field_type. simpl nested_field_offset.
  rewrite isptr_offset_val_zero by auto.
  entailer!.
  apply rv_rows_ok; lia.
Qed.

Lemma x2_zero_arr (sh: share) (n: Z) (p: val) :
  readable_share sh -> 0 <= n -> field_compatible (tarray tuint n) nil p ->
  data_at sh (tarray tuchar (4 * n)) (Zrepeat (vint 0) (4 * n)) p |-- data_at sh (tarray tuint n) (Zrepeat (vint 0) n) p.
Proof.
  intros Hsh Hn Hfc.
  assert (Hs: sizeof (tarray tuint n) = (4 * n)%Z) by (simpl; rewrite Z.max_r by lia; lia).
  rewrite <- Hs. eapply derives_trans; [apply memset_zero_data_at; auto|].
  rewrite zero_val_tarray, zero_val_tuint. apply derives_refl.
Qed.

Lemma x2_fcf (gfs: list gfield) (p: val) :
  field_compatible t_x2wksp gfs p -> field_compatible (nested_field_type t_x2wksp gfs) nil (field_address t_x2wksp gfs p).
Proof. intros H. apply (field_compatible_app nil). exact H. Qed.

Lemma hufhdr_intro (sh: share) (p ty lg res: val) :
  align_compatible tuint p -> byte_val ty -> byte_val lg -> byte_val res ->
  data_at sh t_dtdesc (vint 12, (ty, (lg, res))) p * memory_block sh HUF_CELLBYTES (offset_val 4 p)
  |-- hufhdr_at sh p.
Proof. intros Hal Hty Hlg Hres. unfold hufhdr_at. Exists ty lg res. entailer!. Qed.

Ltac x2_params :=
  apply prop_right; rewrite !field_address_offset by auto;
  match goal with Hfw: field_compatible t_x2wksp nil ?pk |- _ =>
    let Hp := fresh in destruct Hfw as [Hp _]; destruct pk; try contradiction; reflexivity end.

Lemma x2_fa_rankStats (sh: share) (v: list val) (p: val) :
  data_at sh (tarray tuint 13) v (field_address t_x2wksp (DOT _rankStats) p) = field_at sh t_x2wksp (DOT _rankStats) v p.
Proof. rewrite field_at_data_at. reflexivity. Qed.
Lemma x2_fa_rankStart0 (sh: share) (v: list val) (p: val) :
  data_at sh (tarray tuint 15) v (field_address t_x2wksp (DOT _rankStart0) p) = field_at sh t_x2wksp (DOT _rankStart0) v p.
Proof. rewrite field_at_data_at. reflexivity. Qed.
Lemma x2_fa_weightList (sh: share) (v: list val) (p: val) :
  data_at sh (tarray tuchar 256) v (field_address t_x2wksp (DOT _weightList) p) = field_at sh t_x2wksp (DOT _weightList) v p.
Proof. rewrite field_at_data_at. reflexivity. Qed.

Lemma x2_cntw_bound (ht: huf_table) (w: Z) : 0 <= cntw ht w <= Zlength (ht_weights ht).
Proof.
  unfold cntw. rewrite !Zlength_correct. split; [lia|]. apply Nat2Z.inj_le.
  induction (ht_weights ht) as [|a l IH]; simpl; [lia|]. destruct (a =? w); simpl; lia.
Qed.

Lemma x2_ss_default (sh: share) (p: val) :
  field_at_ sh t_x2wksp (DOT _sortedSymbol) p = field_at sh t_x2wksp (DOT _sortedSymbol) (Zrepeat Vundef 256) p.
Proof. reflexivity. Qed.

Lemma x2_fa_sortedSymbol (sh: share) (v: list val) (p: val) :
  data_at sh (tarray t_ssym 256) v (field_address t_x2wksp (DOT _sortedSymbol) p) =
  field_at sh t_x2wksp (DOT _sortedSymbol) v p.
Proof. rewrite field_at_data_at. reflexivity. Qed.
Lemma x2_fa_rankVal (sh: share) (v: list (list val)) (p: val) :
  data_at sh (tarray (tarray tuint 13) 12) v (field_address t_x2wksp (DOT _rankVal) p) =
  field_at sh t_x2wksp (DOT _rankVal) v p.
Proof. rewrite field_at_data_at. reflexivity. Qed.

Lemma x2_sort_arr_len (ht: huf_table) (n: nat) (a0: list val) : Zlength (sort_arr ht n a0) = Zlength a0.
Proof.
  unfold sort_arr. generalize (seq 0 n) as l. intros l. revert a0.
  induction l as [|x l IH]; simpl; intros; [reflexivity|]. rewrite IH, Zlength_upd_Znth. reflexivity.
Qed.

(* the cells of the table: 2^L U32s after the descriptor (needs dt aligned to 4) *)
Lemma x2_al4_add (i: ptrofs) (k: Z) :
  (4 | Ptrofs.unsigned i) -> (4 | k) -> (4 | Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr k))).
Proof.
  intros H1 H2. unfold Ptrofs.add. rewrite Ptrofs.unsigned_repr_eq.
  assert (Hm: (4 | Ptrofs.modulus)) by (exists (2 ^ 62); reflexivity).
  rewrite Z.mod_eq by (pose proof Ptrofs.modulus_pos; lia).
  apply Z.divide_sub_r; [|apply Z.divide_mul_l; exact Hm].
  apply Z.divide_add_r; auto. rewrite Ptrofs.unsigned_repr_eq.
  rewrite Z.mod_eq by (pose proof Ptrofs.modulus_pos; lia).
  apply Z.divide_sub_r; auto. apply Z.divide_mul_l; exact Hm.
Qed.

(* the cells of the table: 2^L U32s after the descriptor (needs dt aligned to 4) *)
Lemma x2_tbl_split (sh: share) (dt: val) (L: Z) :
  0 <= L <= 12 -> align_compatible tuint dt ->
  memory_block sh HUF_CELLBYTES (offset_val 4 dt) |--
  data_at_ sh (tarray tuint (2 ^ L)) (offset_val 4 dt) *
  memory_block sh (HUF_CELLBYTES - 4 * 2 ^ L) (offset_val (4 + 4 * 2 ^ L) dt).
Proof.
  intros HL Hal.
  assert (Hp: 4 * 2 ^ L <= HUF_CELLBYTES).
  { unfold HUF_CELLBYTES. assert (2 ^ L <= 2 ^ 12) by (apply Z.pow_le_mono_r; lia). change (2 ^ 12) with 4096 in H. lia. }
  assert (Hp0: 0 < 2 ^ L) by (apply Z.pow_pos_nonneg; lia).
  assert_PROP (isptr (offset_val 4 dt)) as Hpt by entailer!.
  destruct dt as [| | | | |b i]; try contradiction.
  assert (H4: (4 | Ptrofs.unsigned i)) by (unfold align_compatible in Hal; inv Hal; inv H; exact H0).
  replace HUF_CELLBYTES with (4 * 2 ^ L + (HUF_CELLBYTES - 4 * 2 ^ L)) at 1 by lia.
  simpl offset_val.
  assert_PROP (Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 4)) + (4 * 2 ^ L + (HUF_CELLBYTES - 4 * 2 ^ L)) < Ptrofs.modulus) as Hsz.
  { entailer!. }
  rewrite <- (Ptrofs.repr_unsigned (Ptrofs.add i (Ptrofs.repr 4))) at 1.
  rewrite memory_block_split by (pose proof (Ptrofs.unsigned_range (Ptrofs.add i (Ptrofs.repr 4))); unfold HUF_CELLBYTES in *; lia).
  rewrite Ptrofs.repr_unsigned. apply sepcon_derives.
  - rewrite <- memory_block_data_at_.
    + change (sizeof (tarray tuint (2 ^ L))) with (4 * Z.max 0 (2 ^ L))%Z. rewrite Z.max_r by lia. apply derives_refl.
    + split; [exact I|]. split; [reflexivity|]. split.
      * simpl. rewrite Z.max_r by lia. unfold HUF_CELLBYTES in *. lia.
      * split; [|exact I]. hnf. apply align_compatible_rec_Tarray. intros k Hk.
        eapply align_compatible_rec_by_value; [reflexivity|]. simpl.
        apply Z.divide_add_r; [apply x2_al4_add; auto; exists 1; reflexivity | apply Z.divide_factor_l].
  - apply derives_refl'.
    rewrite <- (ptrofs_add_repr 4 (4 * 2 ^ L)), <- Ptrofs.add_assoc, (Ptrofs.add_unsigned (Ptrofs.add i (Ptrofs.repr 4))).
    rewrite (Ptrofs.unsigned_repr (4 * 2 ^ L)) by (unfold HUF_CELLBYTES in *; rep_lia). reflexivity.
Qed.

(* the built table: the log zstd's X2 reader picks (11 or 12) and exactly ExHuf's cells *)
Lemma x2_hufdt (sh: share) (ht: huf_table) (L: Z) (r dt: val) (c2: list (val * (val * val))) :
  huf_ok ht -> ht_log ht <= L <= HUF_TABLELOG_MAX -> align_compatible tuint dt -> byte_val r ->
  L = (if ht_log ht <=? 11 then 11 else 12) ->
  Zlength c2 = 2 ^ L ->
  (forall v, 0 <= v < 2 ^ L -> x2_cell_ok ht L v (Znth v c2)) ->
  c2 = map x2v (xh_cells_x2 ht L) ->
  data_at sh t_dtdesc (vint 12, (vint 1, (vint L, r))) dt *
  data_at sh (tarray t_deltx2 (2 ^ L)) c2 (offset_val 4 dt) *
  memory_block sh (HUF_CELLBYTES - 4 * 2 ^ L) (offset_val (4 + 4 * 2 ^ L) dt)
  |-- hufdt_x_at true sh ht dt.
Proof.
  intros Hok HL Hal Hr HLx Hc Hcell Hcx. unfold hufdt_x_at. Exists L r. simpl. Exists c2. entailer!.
Qed.

Lemma x2_lift {Espec: OracleKind} P c R :
  semax x2_Delta P c R -> semax (func_tycontext f_HUF_readDTableX2_wksp Vprog G_X2 nil) P c R.
Proof.
  intros H. eapply semax_Delta_subsumption; [|exact H].
  apply semax_prog.func_tycontext_sub; [apply incl_refl | intros ? [] | exact x2_G_nodup].
Qed.

Lemma body_HUF_readDTableX2_wksp : x2_count -> x2_layout -> x2_cells_stmt ->
  semax_body Vprog G_X2 f_HUF_readDTableX2_wksp HUF_readDTableX2_wksp_spec.
Proof.
  intros Hcnt Hlay Hcells.
  start_function.
  unfold hufhdr_at. Intros ty lg res.
  match goal with H: align_compatible tuint dt |- _ => rename H into Hal end.
  match goal with H: byte_val ty |- _ => rename H into Hty end.
  match goal with H: byte_val lg |- _ => rename H into Hlg end.
  match goal with H: byte_val res |- _ => rename H into Hres end.
  assert_PROP (field_compatible (tarray tuint nk) nil pk) as Hfck by entailer!.
  assert_PROP (isptr dt) as Hdt by entailer!.
  rewrite (x2wksp_eq shk pk nk) by (auto; lia).
  rewrite x2wksp_fields. Intros.
  assert (Hfw: field_compatible t_x2wksp nil pk) by (eapply x2wksp_compat; eauto; lia).
  forward_call (Tsh, v_dtd, shd, dt, (vint 12, (ty, (lg, res)))).
  { memcpy_ok_B. }
  forward. forward. forward. forward.
  forward_if.
  { exfalso; lia. }
  forward.
  assert (Hrs: force_val (sem_binary_operation' Oadd (tarray tuint 15) tint
                 (eval_field t_x2wksp _rankStart0 pk) (vint 1)) = offset_val 680 pk).
  { destruct Hfw as [Hpk _]. destruct pk; try contradiction. simpl. rewrite Ptrofs.add_assoc. reflexivity. }
  assert (Hdt4: force_val (sem_binary_operation' Oadd (tptr tuint) tint dt (vint 1)) = offset_val 4 dt).
  { destruct dt; try contradiction. reflexivity. }
  unfold t_x2wksp in Hrs. rewrite Hrs, Hdt4. clear Hrs Hdt4.
  assert (field_compatible t_x2wksp (DOT _weightList) pk) by auto with field_compatible.
  assert (field_compatible t_x2wksp (DOT _rankStats) pk) by auto with field_compatible.
  assert (field_compatible t_x2wksp (DOT _rankStart0) pk) by auto with field_compatible.
  assert (field_compatible t_x2wksp (DOT _calleeWksp) pk) by auto with field_compatible.
  rewrite (field_at__memory_block shk t_x2wksp (DOT _rankStats) pk).
  rewrite (field_at__memory_block shk t_x2wksp (DOT _rankStart0) pk).
  change (sizeof (nested_field_type t_x2wksp (DOT _rankStats))) with 52.
  change (sizeof (nested_field_type t_x2wksp (DOT _rankStart0))) with 60.
  forward_call (shk, field_address t_x2wksp (DOT _rankStats) pk, 0, 52).
  forward_call (shk, field_address t_x2wksp (DOT _rankStart0) pk, 0, 60).
  pose proof (x2_fcf _ _ H3) as Hf3. pose proof (x2_fcf _ _ H4) as Hf4. simpl in Hf3, Hf4.
  sep_apply (x2_zero_arr shk 13 (field_address t_x2wksp (DOT _rankStats) pk) ltac:(auto) ltac:(lia) Hf3).
  sep_apply (x2_zero_arr shk 15 (field_address t_x2wksp (DOT _rankStart0) pk) ltac:(auto) ltac:(lia) Hf4).
  forward_if.
  { exfalso. lia. }
  sep_apply (data_at_data_at_ shk (tarray tuint 13) (Zrepeat (vint 0) 13) (field_address t_x2wksp (DOT _rankStats) pk)).
  rewrite (field_at__data_at_ shk t_x2wksp (DOT _weightList) pk).
  rewrite (field_at__data_at_ shk t_x2wksp (DOT _calleeWksp) pk).
  simpl nested_field_type.
  forward_call (gv, shk, field_address t_x2wksp (DOT _weightList) pk, shk, field_address t_x2wksp (DOT _rankStats) pk,
                Tsh, v_nbSymbols, Tsh, v_tableLog, sh, base, N, c, off, s, shk,
                field_address t_x2wksp (DOT _calleeWksp) pk).
  Intros vret. destruct vret as [[r wc] ores]. simpl fst in *. simpl snd in *.
  match goal with Hm: forall x, huf_parse_desc s = Some x -> ores = Some x |- _ => rename Hm into Hmodel end.
  destruct ores as [[ht size]|].
  2:{ Intros. forward_call r. match goal with Herr: is_error_code r = true |- _ => rewrite Herr end.
      forward_if.
      2:{ discriminate. }
      forward.
      Exists r (@None (huf_table * Z)). entailer!. sep_apply (hufhdr_intro shd dt ty lg res Hal Hty Hlg Hres).
      sep_apply (data_at_data_at_ shk (tarray tuchar 256) wc (field_address t_x2wksp (DOT _weightList) pk)).
      sep_apply (data_at_data_at_ shk (tarray tuint 15) (Zrepeat (vint 0) 15) (field_address t_x2wksp (DOT _rankStart0) pk)).
      rewrite (field_at__data_at_ shk t_x2wksp (DOT _rankVal) pk).
      rewrite (field_at__data_at_ shk t_x2wksp (DOT _sortedSymbol) pk).
      simpl nested_field_type.
      sep_apply (x2wksp_join shk pk nk); auto; try lia.
      cancel. }
  match goal with Hm: r = size /\ _ |- _ => destruct Hm as (-> & Hsz & Hok & Hlen & Hwr & Hws) end. Intros.
  assert (Hht: x2_ht_ok ht) by (split; [exact Hok | split; [exact Hlen | exact Hwr]]).
  assert (Hne: is_error_code size = false).
  { destruct H0 as (_ & Hoff & Hon & HN & _). unfold is_error_code. apply Z.ltb_ge.
    change (2 ^ 64 - 120) with 18446744073709551496. change (2 ^ 32) with 4294967296 in HN. lia. }
  forward_call size. rewrite Hne.
  forward_if.
  { match goal with Hc: Int.repr 0 <> Int.zero |- _ => elim Hc; reflexivity end. }
  set (T := ht_log ht) in *.
  assert (HT: 1 <= T <= 12) by (destruct Hht as ((? & _) & _); unfold HUF_TABLELOG_MAX in *; lia).
  forward. forward_if.
  { exfalso; lia. }
  set (L := if T <=? 11 then 11 else 12).
  forward.
  forward_if (temp _t'3 (vint (if T <=? 11 then 1 else 0))).
  { forward. entailer!. destruct (T <=? 11) eqn:E; [reflexivity | lia]. }
  { forward. entailer!. destruct (T <=? 11) eqn:E; [lia | reflexivity]. }
  forward_if (temp _maxTableLog (vint L)).
  { forward. entailer!. subst L. destruct (T <=? 11); [reflexivity | lia]. }
  { forward. entailer!. subst L. destruct (T <=? 11); [|reflexivity].
    match goal with Hx: Int.repr 1 = Int.zero |- _ => inv Hx end. }
  destruct (xc_maxw Hcnt ht Hht) as (Hmw & Hcm & Hc0 & Hrk).
  set (ws := ht_weights ht) in *.
  assert (Hrk': forall w, 0 <= w <= 12 -> @Znth val Vundef w (rank_stats ws) = vint (cntw ht w)) by exact Hrk.
  assert (HL: T <= L <= 12) by (subst L; destruct (T <=? 11) eqn:E; [apply Z.leb_le in E | apply Z.leb_gt in E]; lia).
  rewrite x2_fa_rankStats, x2_fa_rankStart0, x2_fa_weightList.
  deadvars!.
  forward.
  forward_loop (EX m: Z,
    PROP (maxw ht <= m <= T)
    LOCAL (temp _maxW (vint m); temp _maxTableLog (vint L); temp _iSize (Vlong (Int64.repr size));
           temp _rankStart (offset_val 680 pk); temp _wksp pk; temp _dt (offset_val 4 dt);
           lvar _dtd t_dtdesc v_dtd; lvar _nbSymbols tuint v_nbSymbols; lvar _tableLog tuint v_tableLog;
           temp _DTable dt)
    SEP (zstd_globals gv;
         field_at shk t_x2wksp (DOT _weightList) wc pk;
         field_at shk t_x2wksp (DOT _rankStats) (rank_stats ws) pk;
         data_at Tsh tuint (vint (Zlength ws)) v_nbSymbols; data_at Tsh tuint (vint T) v_tableLog;
         data_at sh (tarray tuchar N) c base;
         data_at_ shk (tarray tuint 219) (field_address t_x2wksp (DOT _calleeWksp) pk);
         field_at shk t_x2wksp (DOT _rankStart0) (Zrepeat (vint 0) 15) pk;
         data_at Tsh t_dtdesc (vint 12, (ty, (lg, res))) v_dtd;
         data_at shd t_dtdesc (vint 12, (ty, (lg, res))) dt;
         memory_block shd HUF_CELLBYTES (offset_val 4 dt);
         field_at_ shk t_x2wksp (DOT _rankVal) pk; field_at_ shk t_x2wksp (DOT _sortedSymbol) pk;
         memory_block shk (4 * nk - 2124) (offset_val 2124 pk)))%assert
  continue: (EX m: Z,
    PROP (maxw ht < m <= T)
    LOCAL (temp _maxW (vint m); temp _maxTableLog (vint L); temp _iSize (Vlong (Int64.repr size));
           temp _rankStart (offset_val 680 pk); temp _wksp pk; temp _dt (offset_val 4 dt);
           lvar _dtd t_dtdesc v_dtd; lvar _nbSymbols tuint v_nbSymbols; lvar _tableLog tuint v_tableLog;
           temp _DTable dt)
    SEP (zstd_globals gv;
         field_at shk t_x2wksp (DOT _weightList) wc pk;
         field_at shk t_x2wksp (DOT _rankStats) (rank_stats ws) pk;
         data_at Tsh tuint (vint (Zlength ws)) v_nbSymbols; data_at Tsh tuint (vint T) v_tableLog;
         data_at sh (tarray tuchar N) c base;
         data_at_ shk (tarray tuint 219) (field_address t_x2wksp (DOT _calleeWksp) pk);
         field_at shk t_x2wksp (DOT _rankStart0) (Zrepeat (vint 0) 15) pk;
         data_at Tsh t_dtdesc (vint 12, (ty, (lg, res))) v_dtd;
         data_at shd t_dtdesc (vint 12, (ty, (lg, res))) dt;
         memory_block shd HUF_CELLBYTES (offset_val 4 dt);
         field_at_ shk t_x2wksp (DOT _rankVal) pk; field_at_ shk t_x2wksp (DOT _sortedSymbol) pk;
         memory_block shk (4 * nk - 2124) (offset_val 2124 pk)))%assert
  break: (
    PROP ()
    LOCAL (temp _maxW (vint (maxw ht)); temp _maxTableLog (vint L); temp _iSize (Vlong (Int64.repr size));
           temp _rankStart (offset_val 680 pk); temp _wksp pk; temp _dt (offset_val 4 dt);
           lvar _dtd t_dtdesc v_dtd; lvar _nbSymbols tuint v_nbSymbols; lvar _tableLog tuint v_tableLog;
           temp _DTable dt)
    SEP (zstd_globals gv;
         field_at shk t_x2wksp (DOT _weightList) wc pk;
         field_at shk t_x2wksp (DOT _rankStats) (rank_stats ws) pk;
         data_at Tsh tuint (vint (Zlength ws)) v_nbSymbols; data_at Tsh tuint (vint T) v_tableLog;
         data_at sh (tarray tuchar N) c base;
         data_at_ shk (tarray tuint 219) (field_address t_x2wksp (DOT _calleeWksp) pk);
         field_at shk t_x2wksp (DOT _rankStart0) (Zrepeat (vint 0) 15) pk;
         data_at Tsh t_dtdesc (vint 12, (ty, (lg, res))) v_dtd;
         data_at shd t_dtdesc (vint 12, (ty, (lg, res))) dt;
         memory_block shd HUF_CELLBYTES (offset_val 4 dt);
         field_at_ shk t_x2wksp (DOT _rankVal) pk; field_at_ shk t_x2wksp (DOT _sortedSymbol) pk;
         memory_block shk (4 * nk - 2124) (offset_val 2124 pk))).
  { Exists T. entailer!. }
  { Intros m. assert (Hm12: 0 <= m <= 12) by lia.
    forward.
    { entailer!. rewrite (Hrk' m Hm12). auto. }
    rewrite (Hrk' m Hm12).
    forward_if.
    - forward. Exists m. entailer!.
      destruct (Z.eq_dec m (maxw ht)) as [->|Hne']; [|lia].
      exfalso. assert (Hz: Int.repr (cntw ht (maxw ht)) = Int.repr 0) by auto.
      apply repr_inj_unsigned in Hz; [lia| |rep_lia].
      pose proof (x2_cntw_bound ht (maxw ht)). destruct Hht as (_ & Hn & _). rep_lia.
    - forward. entailer!.
      destruct (Z.eq_dec m (maxw ht)) as [->|Hne']; [auto|].
      rewrite (Hc0 m) in * by lia. contradiction. }
  { Intros m. forward. Exists (m - 1). entailer!. }
  (* statement 15: rankStart *)
  pose (F1 := zstd_globals gv * field_at shk t_x2wksp (DOT _weightList) wc pk *
              data_at Tsh tuint (vint (Zlength ws)) v_nbSymbols * data_at Tsh tuint (vint T) v_tableLog *
              data_at sh (tarray tuchar N) c base *
              data_at_ shk (tarray tuint 219) (field_address t_x2wksp (DOT _calleeWksp) pk) *
              data_at Tsh t_dtdesc (vint 12, (ty, (lg, res))) v_dtd *
              data_at shd t_dtdesc (vint 12, (ty, (lg, res))) dt *
              memory_block shd HUF_CELLBYTES (offset_val 4 dt) *
              field_at_ shk t_x2wksp (DOT _rankVal) pk * field_at_ shk t_x2wksp (DOT _sortedSymbol) pk *
              memory_block shk (4 * nk - 2124) (offset_val 2124 pk)).
  eapply semax_seq'.
  { eapply semax_pre; [|apply x2_lift; apply (x2_rstart Espec F1 ht size L dt pk v_tableLog v_nbSymbols v_dtd shk); auto].
    unfold F1. entailer!. }
  (* statement 16: the counting sort *)
  pose (F2 := zstd_globals gv * field_at shk t_x2wksp (DOT _rankStats) (rank_stats ws) pk *
              data_at Tsh tuint (vint T) v_tableLog *
              data_at sh (tarray tuchar N) c base *
              data_at_ shk (tarray tuint 219) (field_address t_x2wksp (DOT _calleeWksp) pk) *
              data_at Tsh t_dtdesc (vint 12, (ty, (lg, res))) v_dtd *
              data_at shd t_dtdesc (vint 12, (ty, (lg, res))) dt *
              memory_block shd HUF_CELLBYTES (offset_val 4 dt) *
              field_at_ shk t_x2wksp (DOT _rankVal) pk *
              memory_block shk (4 * nk - 2124) (offset_val 2124 pk)).
  eapply semax_seq'.
  { eapply semax_pre; [|apply x2_lift; apply (x2_sort Espec F2 ht size L dt pk v_tableLog v_nbSymbols v_dtd shk wc
                                                 (Zrepeat Vundef 256)); auto].
    unfold F1, F2. rewrite x2_ss_default. entailer!. }
  Intros rs.
  (* statement 17: rankVal *)
  pose (F3 := zstd_globals gv * field_at shk t_x2wksp (DOT _rankStart0) rs pk *
              field_at shk t_x2wksp (DOT _weightList) wc pk *
              data_at Tsh tuint (vint (Zlength ws)) v_nbSymbols *
              field_at shk t_x2wksp (DOT _sortedSymbol) (sort_arr ht (length ws) (Zrepeat Vundef 256)) pk *
              data_at sh (tarray tuchar N) c base *
              data_at_ shk (tarray tuint 219) (field_address t_x2wksp (DOT _calleeWksp) pk) *
              data_at Tsh t_dtdesc (vint 12, (ty, (lg, res))) v_dtd *
              data_at shd t_dtdesc (vint 12, (ty, (lg, res))) dt *
              memory_block shd HUF_CELLBYTES (offset_val 4 dt) *
              memory_block shk (4 * nk - 2124) (offset_val 2124 pk)).
  eapply semax_seq'.
  { eapply semax_pre; [|apply x2_lift; apply (x2_rv Espec F3 ht size L dt pk v_tableLog v_nbSymbols v_dtd shk); auto].
    unfold F2, F3. entailer!. }
  Intros rv.
  unfold F3. repeat flatten_sepcon_in_SEP.
  (* statement 18: the fill *)
  forward.
  sep_apply (x2_tbl_split shd dt L ltac:(lia) Hal). repeat flatten_sepcon_in_SEP.
  rewrite <- x2_fa_sortedSymbol, <- x2_fa_rankStart0, <- x2_fa_rankVal.
  assert (Hss: x2_ss_ok ht (sort_arr ht (length ws) (Zrepeat Vundef 256))).
  { split; [rewrite x2_sort_arr_len; reflexivity|]. intros i Hi. apply (xc_sort_arr Hcnt); auto. }
  forward_call (shd, offset_val 4 dt, shk, ht, L, field_address t_x2wksp (DOT _sortedSymbol) pk,
                sort_arr ht (length ws) (Zrepeat Vundef 256), field_address t_x2wksp (DOT _rankStart0) pk, rs,
                field_address t_x2wksp (DOT _rankVal) pk, rv).
  { entailer!. rewrite !field_address_offset by auto. destruct Hfw as [Hp _]. destruct pk; try contradiction.
    reflexivity. }
  assert (HL': ht_log ht <= L <= HUF_TABLELOG_MAX) by (unfold HUF_TABLELOG_MAX; lia).
  sep_apply (Hcells shd ht L (offset_val 4 dt) Hht HL'). Intros c2.
  (* the descriptor *)
  forward. forward.
  assert (Hz: Int.zero_ext 8 (Int.repr L) = Int.repr L)
    by (apply zero_ext_inrange; rewrite Int.unsigned_repr by rep_lia; simpl; rep_lia).
  rewrite ?Hz.
  sep_apply (data_at_data_at_ shd t_dtdesc (vint 12, (ty, (lg, res))) dt).
  change (Int.zero_ext 8 (Int.repr 1)) with (Int.repr 1).
  forward_call (Tsh, shd, v_dtd, dt, existT (fun t => reptype t) t_dtdesc (vint 12, (vint 1, (vint L, res)))).
  { memcpy_side_B. }
  cbn [projT1 projT2].
  forward.
  Exists size (Some (ht, size)). entailer!.
  sep_apply (x2_hufdt shd ht L res dt); auto.
  rewrite <- x2_fa_rankStats, <- x2_fa_weightList.
  sep_apply (data_at_data_at_ shk (tarray t_ssym 256) (sort_arr ht (length (ht_weights ht)) (Zrepeat Vundef 256))
    (field_address t_x2wksp (DOT _sortedSymbol) pk)).
  sep_apply (data_at_data_at_ shk (tarray tuint 15) rs (field_address t_x2wksp (DOT _rankStart0) pk)).
  sep_apply (data_at_data_at_ shk (tarray (tarray tuint 13) 12) rv (field_address t_x2wksp (DOT _rankVal) pk)).
  sep_apply (data_at_data_at_ shk (tarray tuint 13) (rank_stats (ht_weights ht)) (field_address t_x2wksp (DOT _rankStats) pk)).
  sep_apply (data_at_data_at_ shk (tarray tuchar 256) wc (field_address t_x2wksp (DOT _weightList) pk)).
  sep_apply (x2wksp_join shk pk nk); auto; try lia.
  cancel.
Qed.
