(* FS3 streaming, case zdss_loadHeader, piece C, segment s10: the split of s10, its states, plain facts. *)
Require Export Zstd.proof.dec.v3.FS.stream.lh.LH3C_lib.
Local Open Scope logic.

Section CM_LH3C2_s10_lib_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Definition c10_a : statement := ltac:(
  let t := eval cbv delta [lhC_s10] in lhC_s10 in lazymatch t with Ssequence ?x _ => exact x end).
Definition c10_e : expr := ltac:(
  let t := eval cbv delta [lhC_s10] in lhC_s10 in lazymatch t with Ssequence _ (Sifthenelse ?e _ _) => exact e end).
Definition c10_t : statement := ltac:(
  let t := eval cbv delta [lhC_s10] in lhC_s10 in lazymatch t with Ssequence _ (Sifthenelse _ ?b _) => exact b end).
Definition c10_f : statement := ltac:(
  let t := eval cbv delta [lhC_s10] in lhC_s10 in lazymatch t with Ssequence _ (Sifthenelse _ _ ?c) => exact c end).
Lemma c10_eq : lhC_s10 = Ssequence c10_a (Sifthenelse c10_e c10_t c10_f).
Proof. reflexivity. Qed.

Definition c10_body : statement := ltac:(
  let t := eval cbv delta [c10_f] in c10_f in lazymatch t with Ssequence (Sloop ?x Sbreak) _ => exact x end).
Definition c10_r : statement := ltac:(
  let t := eval cbv delta [c10_f] in c10_f in lazymatch t with Ssequence _ ?y => exact y end).
Lemma c10_f_eq : c10_f = Ssequence (Sloop c10_body Sbreak) c10_r.
Proof. reflexivity. Qed.

Definition c10_call : statement := ltac:(
  let t := eval cbv delta [c10_body] in c10_body in lazymatch t with Ssequence (Ssequence ?x _) _ => exact x end).
Definition c10_test : statement := ltac:(
  let t := eval cbv delta [c10_body] in c10_body in
  lazymatch t with Ssequence (Ssequence _ ?y) ?z => exact (Ssequence y z) end).
Lemma c10_body_eq : forall {Espec: OracleKind} {cs: compspecs} Delta P Q R,
  semax Delta P c10_call (overridePost Q R) -> semax Delta Q c10_test R -> semax Delta P c10_body R.
Proof.
intros Espec cs Delta P Q R H1 H2. unfold c10_body. apply -> seq_assoc.
apply semax_seq with Q; [exact H1 | exact H2].
Qed.

(* ---------- plain facts ---------- *)

Section C10Z.
Local Open Scope Z_scope.

Lemma c10_le_value_lt : forall l, bytes_ok l -> 0 <= le_value l < 2 ^ (8 * Zlength l).
Proof.
intros l H. induction H as [|b l Hb Hl IH]; cbn [le_value].
- rewrite Zlength_nil. simpl. lia.
- rewrite Zlength_cons. replace (8 * Z.succ (Zlength l)) with (8 + 8 * Zlength l) by lia.
  rewrite Z.pow_add_r by (pose proof (Zlength_nonneg l); lia).
  unfold is_byte in Hb. change (2^8) with 256. lia.
Qed.

Lemma c10_le_field4_range : forall l i, bytes_ok l -> 0 <= le_field l i 4 < 2 ^ 32.
Proof.
intros l i H. unfold le_field, slice.
assert (Hb: bytes_ok (firstn (Z.to_nat 4) (skipn (Z.to_nat i) l))).
{ unfold bytes_ok in *. apply Forall_firstn. apply Forall_skipn. auto. }
assert (Hlen: Zlength (firstn (Z.to_nat 4) (skipn (Z.to_nat i) l)) <= 4).
{ rewrite Zlength_correct, firstn_length. lia. }
set (s := firstn (Z.to_nat 4) (skipn (Z.to_nat i) l)) in *.
pose proof (c10_le_value_lt _ Hb) as [H1 H2]. split; auto.
assert (2 ^ (8 * Zlength s) <= 2 ^ 32) by (apply Z.pow_le_mono_r; [lia | pose proof (Zlength_nonneg s); lia]).
lia.
Qed.

Lemma c10_skip_magic_eq : forall m, 0 <= m < 2 ^ 32 ->
  Int.eq (Int.and (Int.repr m) (Int.repr (-16))) (Int.repr 407710288) = is_skippable_magic m.
Proof.
intros m Hm. unfold Int.and. rewrite (Int.unsigned_repr m) by rep_lia.
change (Int.unsigned (Int.repr (-16))) with ZSTD_MAGIC_SKIPPABLE_MASK.
unfold Int.eq. rewrite Int.unsigned_repr_eq.
change (Int.unsigned (Int.repr 407710288)) with ZSTD_MAGIC_SKIPPABLE_START.
change Int.modulus with (2 ^ 32). rewrite <- Z.land_ones by lia. rewrite <- Z.land_assoc.
change (Z.land ZSTD_MAGIC_SKIPPABLE_MASK (Z.ones 32)) with ZSTD_MAGIC_SKIPPABLE_MASK.
unfold is_skippable_magic.
destruct (zeq (Z.land m ZSTD_MAGIC_SKIPPABLE_MASK) ZSTD_MAGIC_SKIPPABLE_START) as [E|E];
  destruct (Z.eqb_spec (Z.land m ZSTD_MAGIC_SKIPPABLE_MASK) ZSTD_MAGIC_SKIPPABLE_START); congruence.
Qed.

End C10Z.

(* ---------- the frame fields of s10 ---------- *)

Section C10M.
Local Open Scope Z_scope.

(* the frame fields after Begin_usingDDict *)
Definition c10_fsB (k1: cst3) (dd: option (ddx * val)) (cold: val) : fstate :=
  lh_dd_fs (c3_fs k1) (dp_fmt (c3_par k1)) dd cold.

(* the context's dictID after Begin_usingDDict (as an unsigned int) *)
Definition c10_did (dd: option (ddx * val)) : Z :=
  Int.unsigned (Int.repr (match dd with None => 0 | Some (x, _) => if dx_raw x then 0 else dict_id_of (dx_bytes x) end)).

Lemma c10_did_range (dd: option (ddx * val)) : 0 <= c10_did dd <= Int.max_unsigned.
Proof. unfold c10_did. apply Int.unsigned_range_2. Qed.

Lemma c10_fsB_dictID (k1: cst3) dd cold : fs_dictID (c10_fsB k1 dd cold) = Vint (Int.repr (c10_did dd)).
Proof. unfold c10_fsB, c10_did, lh_dd_fs. rewrite Int.repr_unsigned. destruct dd as [[x buf]|]; reflexivity. Qed.

Lemma c10_fsB_pcs (k1: cst3) dd cold : fs_processedCSize (c10_fsB k1 dd cold) = Vlong (Int64.repr 0).
Proof. unfold c10_fsB, lh_dd_fs. destruct dd as [[x buf]|]; reflexivity. Qed.

Lemma c10_fsB_fParams (k: cst3) v d1 did1 dd cold : fs_fParams (c10_fsB (k_A k v d1 did1) dd cold) = v.
Proof. unfold c10_fsB, lh_dd_fs. destruct dd as [[x buf]|]; reflexivity. Qed.

Lemma c10_fsu_fParams_same (fs: fstate) (v: reptype t_fh) : fs_fParams fs = v -> fsu_fParams fs v = fs.
Proof. destruct fs; simpl; intros ->; reflexivity. Qed.

Definition c10_vck (k1: cst3) (h: frame_header) : bool :=
  andb (fh_checksumFlag h =? 1) (negb (dp_ignore (c3_par k1) =? 1)).

(* fParams := the header, dictID := did' *)
Definition c10_fs1 (k1: cst3) (h: frame_header) dd cold (did': Z) : fstate :=
  fsu_dictID (fsu_fParams (c10_fsB k1 dd cold) (fh_val h)) (Vint (Int.repr did')).

(* after a successful ZSTD_decodeFrameHeader *)
Definition c10_fsok (k1: cst3) (hb: list Z) (h: frame_header) dd cold (did': Z) : fstate :=
  fsu_processedCSize
    (fsu_xxh (fsu_validateChecksum (c10_fs1 k1 h dd cold did') (Vint (Int.repr (if c10_vck k1 h then 1 else 0))))
       (if c10_vck k1 h then Some nil else fs_xxh (c10_fsB k1 dd cold)))
    (Vlong (Int64.repr (Zlength hb))).

(* the result of ZSTD_decodeFrameHeader (the dictionary fields unchanged) *)
Definition c10_res (k1: cst3) (hb: list Z) (h: frame_header) dd cold (did' r: Z) (fs': fstate) : Prop :=
  0 <= did' <= Int.max_unsigned /\ (dd = None -> did' = 0) /\
  if orb (fh_dictID h =? 0) (fh_dictID h =? did') then r = 0 /\ fs' = c10_fsok k1 hb h dd cold did'
  else dec_err r /\ fs' = c10_fs1 k1 h dd cold did' /\ did' = c10_did dd.

Lemma c10_fs0_skip (k: cst3) hb h d1 did1 (c: lhc) : fh_frameType h = 1 ->
  lhC_fs0 (k_A k (fh_val h) d1 did1) hb h c =
  fsu_stage (fsu_expected (c10_fsB (k_A k (fh_val h) d1 did1) (lc_dd c) (lc_cold c)) (vlong (le_field hb 4 4)))
    (Vint (Int.repr ds_skipFrame)).
Proof.
intros Hf. unfold lhC_fs0. rewrite Hf. cbn [Z.eqb Pos.eqb].
apply c10_fsu_fParams_same. apply (c10_fsB_fParams k (fh_val h) d1 did1).
Qed.

Lemma c10_fs0_ok (k: cst3) hb h d1 did1 (c: lhc) : fh_frameType h <> 1 ->
  lhC_fs0 (k_A k (fh_val h) d1 did1) hb h c =
  fsu_stage (fsu_expected (c10_fsok (k_A k (fh_val h) d1 did1) hb h (lc_dd c) (lc_cold c) (lc_did c))
     (vlong ZSTD_blockHeaderSize)) (Vint (Int.repr ds_decodeBlockHeader)).
Proof.
intros Hf. unfold lhC_fs0. replace (fh_frameType h =? 1) with false by (symmetry; apply Z.eqb_neq; auto).
apply c10_fsu_fParams_same. reflexivity.
Qed.

(* the frame's Dictionary_ID is fParams' *)
Lemma c10_id_eq (h: frame_header) (id: Z) : fp_dictID (fh_val h) = Vint (Int.repr id) ->
  0 <= id <= Int.max_unsigned -> 0 <= fh_dictID h <= Int.max_unsigned -> id = fh_dictID h.
Proof.
intros E H1 H2. change (fp_dictID (fh_val h)) with (Vint (Int.repr (fh_dictID h))) in E.
assert (E': Int.repr (fh_dictID h) = Int.repr id) by congruence.
rewrite <- (Int.unsigned_repr id) by auto. rewrite <- (Int.unsigned_repr (fh_dictID h)) by auto.
rewrite E'. reflexivity.
Qed.

Lemma c10_gd_ddict (d: dfields) :
  df_ddict (snd (getddict_res d)) = nullval \/ df_ddict (snd (getddict_res d)) = df_ddict d.
Proof. unfold getddict_res. destruct (df_uses d =? 0); [left; reflexivity|]. destruct (df_uses d =? 1); right; reflexivity. Qed.

(* the selection inside ZSTD_decodeFrameHeader finds what piece A's did *)
Lemma c10_sel_same (k: cst3) hb tbl h d1 did1 :
  lhA_sel k hb 0 (fh_val h) tbl d1 did1 -> sel_on (c3_par k) (c3_sp k) = true ->
  0 <= fh_dictID h <= Int.max_unsigned ->
  sel_dict (snd (getddict_res d1)) (sel_r (snd (getddict_res d1)) (c3_set k) tbl (fh_dictID h)) =
  snd (getddict_res d1).
Proof.
intros (_ & _ & id & Hid & Hsb) Hon Hr.
unfold sel_by in Hsb. rewrite Hon in Hsb. destruct Hsb as (Hinv & Hidr & -> & _).
pose proof (c10_id_eq h id (Hid Hon) Hidr Hr) as ->.
set (r1 := sel_r (c3_dict k) (c3_set k) tbl (fh_dictID h)) in *.
destruct (eq_dec r1 nullval) as [E|E].
- replace (sel_dict (c3_dict k) r1) with (c3_dict k) by (unfold sel_dict; rewrite if_true by auto; reflexivity).
  unfold sel_dict. destruct (eq_dec _ nullval) as [E'|E']; [reflexivity | exfalso; apply E'].
  subst r1. unfold sel_r in *.
  destruct (eq_dec (df_ddict (snd (getddict_res (c3_dict k)))) nullval) as [E2|E2]; [reflexivity|].
  destruct (eq_dec (df_ddict (c3_dict k)) nullval) as [E3|E3]; [| exact E].
  exfalso. destruct (c10_gd_ddict (c3_dict k)) as [E4|E4]; congruence.
- assert (Hr1: r1 = hs_probe (c3_set k) tbl (fh_dictID h)).
  { subst r1. unfold sel_r in *. destruct (eq_dec (df_ddict (c3_dict k)) nullval); [contradiction | reflexivity]. }
  clearbody r1.
  replace (sel_dict (c3_dict k) r1) with (switch_fields r1) by (unfold sel_dict; rewrite if_false by auto; reflexivity).
  cbn [getddict_res switch_fields df_uses snd Z.eqb Pos.eqb].
  unfold sel_r. change (df_ddict (switch_fields r1)) with r1. rewrite if_false by auto. rewrite <- Hr1.
  unfold sel_dict. rewrite if_false by auto. reflexivity.
Qed.

Lemma c10_cur_ok (k: cst3) hb tbl h d1 did1 (xq: option (val * val)) :
  hs_probe_ok -> lhA_sel k hb 0 (fh_val h) tbl d1 did1 -> sel_on (c3_par k) (c3_sp k) = true ->
  cur_ok (c3_dict k) (c3_set k) xq -> cur_ok (snd (getddict_res d1)) (c3_set k) xq.
Proof.
intros Hpr (_ & _ & id & Hid & Hsb) Hon Hc.
unfold sel_by in Hsb. rewrite Hon in Hsb. destruct Hsb as (Hinv & Hidr & -> & _).
set (r1 := sel_r (c3_dict k) (c3_set k) tbl id) in *.
destruct (eq_dec r1 nullval) as [E|E].
- replace (sel_dict (c3_dict k) r1) with (c3_dict k) by (unfold sel_dict; rewrite if_true by auto; reflexivity).
  destruct Hc as [Hu Hd]. unfold getddict_res.
  destruct (df_uses (c3_dict k) =? 0); [split; cbn; auto|].
  destruct (df_uses (c3_dict k) =? 1); split; cbn; auto.
- assert (Hr1: r1 = hs_probe (c3_set k) tbl id).
  { subst r1. unfold sel_r in *. destruct (eq_dec (df_ddict (c3_dict k)) nullval); [contradiction | reflexivity]. }
  clearbody r1.
  replace (sel_dict (c3_dict k) r1) with (switch_fields r1) by (unfold sel_dict; rewrite if_false by auto; reflexivity).
  destruct (Hpr (c3_set k) tbl id Hinv Hidr) as [[Hn|Hin] _]; rewrite <- Hr1 in *; [contradiction|].
  cbn [getddict_res switch_fields df_uses snd Z.eqb Pos.eqb]. split; cbn; auto.
Qed.

(* ZSTD_decodeFrameHeader's post on Begin_usingDDict's frame fields *)
Lemma c10_getdd_null (d: dfields) : fst (getddict_res d) = nullval -> df_ddict (snd (getddict_res d)) = nullval.
Proof.
unfold getddict_res. destruct (df_uses d =? 0); [ intros _; reflexivity | ].
destruct (df_uses d =? 1); cbn; auto.
Qed.

Lemma c10_did_ne (dd: option (ddx * val)) (x: Z) :
  0 <= x <= Int.max_unsigned -> x <> c10_did dd -> x <> lh_dd_did dd.
Proof.
unfold c10_did, lh_dd_did. intros Hx Hne E. apply Hne.
destruct dd as [[y buf]|]; rewrite <- E; rewrite Int.unsigned_repr by lia; reflexivity.
Qed.

Lemma c10_dfh (k: cst3) hb h tbl d1 did1 dd cold r fs' d' :
  (dd = None -> fst (getddict_res d1) = nullval) ->
  lhA_sel k hb 0 (fh_val h) tbl d1 did1 -> get_frame_header_m (lh_mg k) hb = FH_ok h ->
  0 <= fh_dictID h <= Int.max_unsigned ->
  dfh_post3 (dmode_of (c3_par k)) (sel_on (c3_par k) (c3_sp k)) (snd (getddict_res d1)) (c3_set k) tbl
    (c10_fsB (k_A k (fh_val h) d1 did1) dd cold) (c10_did dd) 0 hb r fs' d' ->
  d' = snd (getddict_res d1) /\ exists did', c10_res (k_A k (fh_val h) d1 did1) hb h dd cold did' r fs'.
Proof.
intros Hnull Hs Hg Hr Hp. unfold dfh_post3 in Hp.
change (md_magicless (dmode_of (c3_par k))) with (lh_mg k) in Hp. rewrite Hg in Hp. cbv zeta in Hp.
destruct Hp as [Hd Hp]. split.
- rewrite Hd. destruct (sel_on (c3_par k) (c3_sp k)) eqn:Hon.
  + apply (c10_sel_same k hb tbl h d1 did1 Hs Hon Hr).
  + unfold sel_dict. rewrite if_true by auto. reflexivity.
- assert (Hrq: dd = None ->
    (if sel_on (c3_par k) (c3_sp k) then sel_r (snd (getddict_res d1)) (c3_set k) tbl (fh_dictID h) else nullval)
    = nullval).
  { intros E. destruct (sel_on (c3_par k) (c3_sp k)); [ | reflexivity ].
    unfold sel_r. rewrite (c10_getdd_null d1 (Hnull E)). rewrite if_true by auto. reflexivity. }
  set (rq := if sel_on (c3_par k) (c3_sp k) then _ else _) in *. clearbody rq.
  exists (if eq_dec rq nullval then c10_did dd else fh_dictID h).
  split; [destruct (eq_dec rq nullval); [apply c10_did_range | exact Hr] |].
  split; [ intros E; rewrite (Hrq E); rewrite if_true by auto; subst dd; reflexivity | ].
  destruct (_ || _)%bool eqn:Eo; [destruct Hp as [-> ->]; rewrite Z.add_0_l; split; reflexivity |].
  destruct Hp as [Hr' ->]. split; [exact Hr' | split; [reflexivity | ]].
  destruct (eq_dec rq nullval); [ reflexivity | ]. exfalso.
  rewrite orb_false_iff in Eo. destruct Eo as [_ Eo]. rewrite Z.eqb_neq in Eo. apply Eo; reflexivity.
Qed.

Lemma c10_sk_flag (k: cst3) hb h : gfh3_facts (lh_mg k) hb h -> par_ok (c3_par k) ->
  (if dp_fmt (c3_par k) =? 0 then is_skippable_magic (le_field hb 0 4) else false) = (fh_frameType h =? 1).
Proof.
intros Hf (Hfmt & _). destruct Hf as (_ & _ & _ & _ & _ & _ & Hft & Hft1 & _).
unfold lh_mg in Hft1.
destruct Hfmt as [E|E]; rewrite E in *; cbn [Z.eqb] in *.
- destruct (is_skippable_magic _) eqn:Es; symmetry.
  + apply Z.eqb_eq. apply Hft1. auto.
  + apply Z.eqb_neq. intro E'. apply Hft1 in E'. destruct E'; congruence.
- symmetry. apply Z.eqb_neq. intro E'. apply Hft1 in E'. destruct E'; discriminate.
Qed.

End C10M.

(* ---------- resources ---------- *)

Lemma c10_fg_split (TABS: tabs_pred) gv p fs t pr sp :
  fgroup3 TABS gv p fs t pr sp = !! (cold01 fs /\ par_ok pr) && (fcore3 p fs pr sp * tabs_rep TABS gv p t).
Proof. unfold fgroup3, fcore3. apply pred_ext; entailer!. Qed.

Lemma c10_fg_fold (TABS: tabs_pred) gv p fs t pr sp : cold01 fs ->
  fcore3 p fs pr sp * tabs_rep TABS gv p t |-- fgroup3 TABS gv p fs t pr sp.
Proof. intros H. unfold fgroup3, fcore3. entailer!. Qed.

Lemma c10_sel_off (DENT: dent_pred) gv p pr sp d l tbl xq am hb : sel_on pr sp = false ->
  sel_res DENT gv p pr sp d l tbl xq am hb = emp.
Proof. intros H. unfold sel_res. rewrite H. reflexivity. Qed.

Lemma c10_sel_on (DENT: dent_pred) gv p pr sp d l tbl xq am hb : sel_on pr sp = true ->
  sel_res DENT gv p pr sp d l tbl xq am hb =
  mem_mgr gv * dgroup DENT gv p d * cm_have am (hb + local_held d) * hset_tbl am sp l tbl * set_ids l * opt_token xq.
Proof. intros H. unfold sel_res. rewrite H. reflexivity. Qed.

Lemma c10_sel_off_intro (DENT: dent_pred) gv p pr sp d l tbl xq am hb (R: mpred) : sel_on pr sp = false ->
  R |-- R * sel_res DENT gv p pr sp d l tbl xq am hb.
Proof. intros H. rewrite (c10_sel_off DENT gv p pr sp d l tbl xq am hb H), sepcon_emp. apply derives_refl. Qed.

Lemma c10_sel_off_elim (DENT: dent_pred) gv p pr sp d l tbl xq am hb (R: mpred) : sel_on pr sp = false ->
  R * sel_res DENT gv p pr sp d l tbl xq am hb |-- R.
Proof. intros H. rewrite (c10_sel_off DENT gv p pr sp d l tbl xq am hb H), sepcon_emp. apply derives_refl. Qed.

Lemma c10_hset_on (am: option cmem) (sp: val) l hb tbl : sp <> nullval ->
  hset_t am sp l hb tbl = !! (l <> nil /\ hb = set_bytes am (Zlength tbl)) && hset_tbl am sp l tbl.
Proof. intros H. unfold hset_t. rewrite if_false by auto. reflexivity. Qed.

Lemma c10_sel_on_t (pr: dparams) (sp: val) : sel_on pr sp = true -> sp <> nullval.
Proof.
unfold sel_on, veqb. intros H E. subst sp. rewrite andb_true_iff in H. destruct H as [_ H].
destruct (Val.eq nullval nullval); [discriminate | contradiction].
Qed.

Lemma c10_hb_eq (sh: share) (c: list val) (q: val) :
  data_at sh (tarray tuchar 18) c (field_address t_dctx (DOT _headerBuffer) q) =
  field_at sh t_dctx (DOT _headerBuffer) c q.
Proof. rewrite field_at_data_at. reflexivity. Qed.

(* the headerBuffer split at L *)
Lemma c10_hbuf_split : forall p (c: list val) L, 0 <= L <= 18 -> Zlength c = 18 ->
  field_at Ews t_dctx (DOT _headerBuffer) c p =
  data_at Ews (tarray tuchar L) (sublist 0 L c) (field_address t_dctx (DOT _headerBuffer) p) *
  data_at Ews (tarray tuchar (18 - L)) (sublist L 18 c)
    (field_address0 (tarray tuchar 18) (SUB L) (field_address t_dctx (DOT _headerBuffer) p)).
Proof. intros p c L HL Hc. rewrite field_at_data_at. apply (split2_data_at_Tarray_tuchar Ews 18 L c); auto. Qed.

(* the frame fields with expected and stage taken out *)
Definition c10_ff (p: val) (fs: fstate) : mpred :=
  field_at Ews t_dctx (DOT _previousDstEnd) (fs_previousDstEnd fs) p *
  field_at Ews t_dctx (DOT _gpDictCopy) (fs_gpDictCopy fs) p *
  field_at Ews t_dctx (DOT _prefixStart) (fs_prefixStart fs) p *
  field_at Ews t_dctx (DOT _virtualStart) (fs_virtualStart fs) p *
  field_at Ews t_dctx (DOT _dictEnd) (fs_dictEnd fs) p *
  field_at Ews t_dctx (DOT _fParams) (fs_fParams fs) p *
  field_at Ews t_dctx (DOT _processedCSize) (fs_processedCSize fs) p *
  field_at Ews t_dctx (DOT _decodedSize) (fs_decodedSize fs) p *
  field_at Ews t_dctx (DOT _bType) (fs_bType fs) p *
  xxh_field p (fs_xxh fs) *
  field_at Ews t_dctx (DOT _headerSize) (fs_headerSize fs) p *
  field_at Ews t_dctx (DOT _validateChecksum) (fs_validateChecksum fs) p *
  field_at Ews t_dctx (DOT _rleSize) (fs_rleSize fs) p *
  field_at Ews t_dctx (DOT _isFrameDecompression) (fs_isFrameDecompression fs) p *
  field_at Ews t_dctx (DOT _dictID) (fs_dictID fs) p *
  field_at Ews t_dctx (DOT _ddictIsCold) (fs_ddictIsCold fs) p.

Lemma c10_ff_split (p: val) (fs: fstate) :
  frame_fields p fs =
  field_at Ews t_dctx (DOT _expected) (fs_expected fs) p * field_at Ews t_dctx (DOT _stage) (fs_stage fs) p *
  c10_ff p fs.
Proof. unfold frame_fields, c10_ff. apply pred_ext; cancel. Qed.

Lemma c10_ff_fold (p: val) (fs: fstate) (e st: val) :
  field_at Ews t_dctx (DOT _expected) e p * field_at Ews t_dctx (DOT _stage) st p * c10_ff p fs |--
  frame_fields p (fsu_stage (fsu_expected fs e) st).
Proof. rewrite (c10_ff_split p (fsu_stage (fsu_expected fs e) st)). apply derives_refl. Qed.

Definition c10_zg_rest (gv: globals) : mpred := (
  data_at Ews tint g_debuglevel_val (gv _g_debuglevel) *
  data_at Ers (tarray tuint 32) DeBruijnBytePos_val (gv _DeBruijnBytePos) *
  data_at Ers (tarray tuint 32) DeBruijnClz_val (gv _DeBruijnClz) *
  data_at Ers tulong zeroFilled_val (gv _zeroFilled) *
  data_at Ers (Tstruct ___gp_ZSTD_customMem noattr) ZSTD_defaultCMem_val (gv _ZSTD_defaultCMem) *
  data_at Ers (tarray tuint 3) repStartValue_val (gv _repStartValue) *
  data_at Ers (tarray tulong 4) ZSTD_fcs_fieldSize_val (gv _ZSTD_fcs_fieldSize) *
  data_at Ers (tarray tulong 4) ZSTD_did_fieldSize_val (gv _ZSTD_did_fieldSize) *
  data_at Ers (tarray tuchar 36) LL_bits_val (gv _LL_bits) *
  data_at Ers (tarray tuchar 53) ML_bits_val (gv _ML_bits) *
  data_at Ers (tarray (tarray (Tstruct ___gp_algo_time_t noattr) 2) 16) algoTime_val (gv _algoTime) *
  data_at Ers (tarray tuint 36) LL_base_val (gv _LL_base) *
  data_at Ers (tarray tuint 32) OF_base_val (gv _OF_base) *
  data_at Ers (tarray tuchar 32) OF_bits_val (gv _OF_bits) *
  data_at Ers (tarray tuint 53) ML_base_val (gv _ML_base) *
  data_at Ers (tarray (Tstruct ___gp_ZSTD_seqSymbol noattr) 65) LL_defaultDTable_val (gv _LL_defaultDTable) *
  data_at Ers (tarray (Tstruct ___gp_ZSTD_seqSymbol noattr) 33) OF_defaultDTable_val (gv _OF_defaultDTable) *
  data_at Ers (tarray (Tstruct ___gp_ZSTD_seqSymbol noattr) 65) ML_defaultDTable_val (gv _ML_defaultDTable) *
  data_at Ers (tarray tuint 8) dec32table_val (gv _dec32table) *
  data_at Ers (tarray tint 8) dec64table_val (gv _dec64table) *
  eb_res gv).

Lemma c10_zg_eq (gv: globals) :
  zstd_globals gv = data_at Ers tulong (Vlong (Int64.repr 3)) (gv _ZSTD_blockHeaderSize) * c10_zg_rest gv.
Proof. unfold zstd_globals, c10_zg_rest, ZSTD_blockHeaderSize_val. apply pred_ext; cancel. Qed.

(* ---------- the allocator's count around a call that may free the local DDict ---------- *)

(* the stream group without the count of bytes the context's allocator has given out (cm_have): ZSTD_getDDict and
   the selection of ZSTD_decodeFrameHeader take that count, with the local DDict's bytes in it, and give it back with
   those of the local DDict they leave *)
Definition lhC_sgx (p: val) (s: sfields) : mpred :=
  !! (0 <= sf_inSize s /\ 0 <= sf_outSize s /\ sf_inSize s + sf_outSize s <= 2 ^ 32 /\
      Int.min_signed <= sf_stage s <= Int.max_signed /\ Int.min_signed <= sf_nfp s <= Int.max_signed /\
      0 <= sf_over s <= Int64.max_unsigned /\ Zlength (sf_hbuf s) = 18 /\ byte_cells (sf_ring s) /\
      (sf_inBuff s <> nullval -> sf_outBuff s = offset_val (sf_inSize s) (sf_inBuff s)) /\
      (sf_inBuff s <> nullval -> 0 < sf_inSize s + sf_outSize s)) &&
  (field_at Ews t_dctx (DOT _streamStage) (Vint (Int.repr (sf_stage s))) p *
   field_at Ews t_dctx (DOT _inBuff) (sf_inBuff s) p *
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
   field_at Ews t_dctx (DOT _oversizedDuration) (Vlong (Int64.repr (sf_over s))) p *
   ring_rep (sf_mem s) (sf_inBuff s) (sf_inSize s + sf_outSize s) (sf_ring s) *
   field_at Ews t_dctx (DOT _customMem) (cmem_v (sf_mem s)) p *
   blk_tok (sf_mem s) (tarray tuchar (sizeof t_dctx)) p).

(* the count taken out of the stream group, as the bytes hb besides the local DDict of d and the local DDict's *)
Lemma lhC_sg_take (p: val) (s: sfields) (d: dfields) :
  0 <= sf_held s - local_held d ->
  sgroup p s |-- !! (cmem_ok (sf_mem s) /\ 0 <= sf_given s - local_held d) &&
    (lhC_sgx p s * cm_have (sf_mem s) (sf_given s - local_held d + local_held d)).
Proof.
  intros Hh. unfold sgroup, mgroup, lhC_sgx. Intros.
  replace (sf_given s - local_held d + local_held d) with (sf_given s) by lia.
  assert (Hg: 0 <= sf_given s - local_held d) by (unfold sf_given; rewrite dctx_size_eq; lia).
  apply andp_right; [apply prop_right; tauto | cancel].
Qed.

(* ... and given back after the call left the dictionary fields d1 (the held bytes follow: LH3Defs.held_redict) *)
Lemma lhC_sg_put (p: val) (s: sfields) (d d1: dfields) :
  0 <= sf_held s - local_held d -> cmem_ok (sf_mem s) ->
  lhC_sgx p s * cm_have (sf_mem s) (sf_given s - local_held d + local_held d1) |-- sgroup p (held_redict s d d1).
Proof.
  intros Hh Hm. pose proof (local_held_nonneg d1).
  rewrite <- sf_given_redict.
  unfold sgroup, mgroup, lhC_sgx. Intros.
  unfold held_redict, sf_with_held; cbn [sf_stage sf_inBuff sf_inSize sf_inPos sf_outBuff sf_outSize sf_outStart
    sf_outEnd sf_lhSize sf_hostage sf_nfp sf_expOut sf_hbuf sf_over sf_ring sf_mem sf_held].
  apply andp_right; [apply prop_right; tauto || (repeat split; tauto || lia) |].
  cancel.
Qed.

Lemma lhC_hr_mem (s: sfields) (d d1: dfields) : sf_mem (held_redict s d d1) = sf_mem s.
Proof. reflexivity. Qed.

(* a return to any ret_assert *)
Lemma c10_semax_return : forall {Espec: OracleKind} {cs: compspecs} Delta P Q R ret v (Post: ret_assert),
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- local (fun rho => v = eval_expr (Ecast ret (ret_type Delta)) rho) ->
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- tc_expr Delta (Ecast ret (ret_type Delta)) ->
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- RA_return Post (Some v) ->
  semax Delta (PROPx P (LOCALx Q (SEPx R))) (Sreturn (Some ret)) Post.
Proof.
intros Espec cs Delta P Q R ret v Post H1 H2 H3.
eapply semax_pre; [| apply semax_return].
apply andp_right; [exact H2 |].
apply derives_trans with (local (fun rho => v = eval_expr (Ecast ret (ret_type Delta)) rho) && RA_return Post (Some v)).
{ apply andp_right; auto. }
intro rho. unfold local, lift1, cast_expropt. unfold_lift. simpl.
apply derives_extract_prop; intro Hv. rewrite <- Hv. auto.
Qed.

(* do { c } while (0) *)
Lemma c10_dowhile0_gen : forall {CS: compspecs} {Espec: OracleKind} Delta P c R,
  semax Delta P c (loop1_ret_assert (RA_normal R) R) -> semax Delta P (Sloop c Sbreak) R.
Proof.
intros CS Espec Delta P c R H.
apply semax_loop with (Q' := RA_normal R); auto.
eapply semax_pre; [| apply semax_break]. destruct R; simpl; intros; apply andp_left2; auto.
Qed.

(* ---------- the states inside s10 ---------- *)

Section States.
Variable DENT : dent_pred.
Variable TABS : tabs_pred.

(* lhC_S2 with its witnesses *)
Definition c10_S2x (a: dsa) (w: lw) (k1: cst3) (h: frame_header) (tbl: list val) dd cold lxb : environ -> mpred :=
  PROPx [lhC_small a w k1 h = false; lhC_dd a k1 dd; cold = Vint (Int.repr 0) \/ cold = Vint (Int.repr 1)]
  (LOCALx (ds_LI_L a (lw_k w k1))
  (SEPx (ds_LI_St DENT TABS a (lw_k w (lhC_kx k1 (c10_fsB k1 dd cold) dd lxb)) tbl))).

(* after the skippable test: _t'40 *)
Definition c10_S2b (a: dsa) (w: lw) (k1: cst3) (h: frame_header) (tbl: list val) dd cold lxb : environ -> mpred :=
  PROPx [lhC_small a w k1 h = false; lhC_dd a k1 dd; cold = Vint (Int.repr 0) \/ cold = Vint (Int.repr 1)]
  (LOCALx (temp _t'40 (Vint (Int.repr (if fh_frameType h =? 1 then 1 else 0))) :: ds_LI_L a (lw_k w k1))
  (SEPx (ds_LI_St DENT TABS a (lw_k w (lhC_kx k1 (c10_fsB k1 dd cold) dd lxb)) tbl))).

(* after ZSTD_decodeFrameHeader *)
Definition c10_SM (a: dsa) (w: lw) (k1: cst3) (hb: list Z) (h: frame_header) (tbl: list val) dd cold lxb
    : environ -> mpred :=
  EX r: Z, EX fs': fstate, EX did': Z,
  PROPx [lhC_small a w k1 h = false; lhC_dd a k1 dd; cold = Vint (Int.repr 0) \/ cold = Vint (Int.repr 1);
         0 <= r <= Int64.max_unsigned; c10_res k1 hb h dd cold did' r fs']
  (LOCALx (temp _t'38 (Vlong (Int64.repr r)) :: ds_LI_L a (lw_k w k1))
  (SEPx (ds_LI_St DENT TABS a (lw_k w (lhC_kx k1 fs' dd lxb)) tbl))).

(* after the successful test *)
Definition c10_S2c (a: dsa) (w: lw) (k1: cst3) (hb: list Z) (h: frame_header) (tbl: list val) dd cold lxb
    : environ -> mpred :=
  EX did': Z,
  PROPx [lhC_small a w k1 h = false; lhC_dd a k1 dd; cold = Vint (Int.repr 0) \/ cold = Vint (Int.repr 1);
         0 <= did' <= Int.max_unsigned; fh_dictID h = 0 \/ fh_dictID h = did'; dd = None -> did' = 0]
  (LOCALx (ds_LI_L a (lw_k w k1))
  (SEPx (ds_LI_St DENT TABS a (lw_k w (lhC_kx k1 (c10_fsok k1 hb h dd cold did') dd lxb)) tbl))).

End States.

End CM_LH3C2_s10_lib_1.
