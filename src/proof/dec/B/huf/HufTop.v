(* Sub-group TOP of group HUF (HufGroups.v): the descriptor, the dead fast loops, HUF_selectDecoder, the DCtx/usingDTable entry points.
   Choose one specification per function of ids_TOP (containing TOP_exports) and prove every body against
   G_HUF ++ TOP_imports and them. *)
Require Export Zstd.proof.dec.B.huf.HufGroups.
Require Export Zstd.proof.dec.B.huf.HufMDesc.
Require Import Zstd.proof.dec.B.BCompose Zstd.proof.dec.B.BMemcpyOk.
Require Import Zstd.proof.model.ExHuf.
Local Open Scope logic.

(* ---------- the specifications of TOP's own functions ---------- *)

(* HUF_decompress4X1_DCtx_wksp (x2 = false) / HUF_decompress4X2_DCtx_wksp (x2 = true): the two branches of
   HUF_decompress4X_hufOnly_wksp, each with its fixed table type x2.  As huf_dctx_spec true, but the table is
   built of type x2 and the exact outcome is ExHuf.xh_dctx x2's (hufOnly chooses x2 by HUF_selectDecoder). *)
Definition huf_dctx4_spec (x2: bool) : funspec :=
  WITH gv: globals, shd: share, dt: val, sho: share, ob: val, oc: list val, d: Z, n: Z,
       sh: share, base: val, N: Z, c: list val, off: Z, s: list Z, shk: share, pk: val, nk: Z
  PRE [ tptr tuint, tptr tvoid, tulong, tptr tvoid, tulong, tptr tvoid, tulong, tint ]
    PROP (writable_share shd; writable_share sho; writable_share shk; 640 <= nk <= 4096;
          0 <= d; 6 <= n <= ZSTD_BLOCKSIZE_MAX; d + n <= Zlength oc; 1 <= Zlength oc;
          Zlength s <= ZSTD_BLOCKSIZE_MAX; win_ok sh N c off (Zlength s) s)
    PARAMS (dt; offset_val d ob; Vlong (Int64.repr n); offset_val off base; Vlong (Int64.repr (Zlength s));
            pk; Vlong (Int64.repr (4 * nk)); Vint (Int.repr 0)) GLOBALS (gv)
    SEP (zstd_globals gv; hufhdr_at shd dt; data_at sho (tarray tuchar (Zlength oc)) oc ob;
         data_at sh (tarray tuchar N) c base; data_at_ shk (tarray tuint nk) pk)
  POST [ tulong ]
    EX r: Z, EX oc': list val,
    PROP (0 <= r <= Int64.max_unsigned; out_after oc oc' d n; (byte_cells oc -> byte_cells oc');
          is_error_code r = false -> r = n /\ exists l, sublist d (d + n) oc' = zbytes l /\ bytes_ok l;
          match huf_lits true s n with
          | Some (t, l) => r = n /\ sublist d (d + n) oc' = zbytes l
          | None => True
          end;
          match xh_dctx x2 false s n with
          | None => is_error_code r = true
          | Some (l, _) => r = n /\ sublist d (d + n) oc' = zbytes l
          end)
    RETURN (Vlong (Int64.repr r))
    SEP (zstd_globals gv; huf_built shd r (option_map fst (huf_lits true s n)) x2 s dt;
         data_at sho (tarray tuchar (Zlength oc)) oc' ob;
         data_at sh (tarray tuchar N) c base; data_at_ shk (tarray tuint nk) pk).

Definition HUF_decompress4X1_DCtx_wksp_spec : ident * funspec :=
  DECLARE _HUF_decompress4X1_DCtx_wksp huf_dctx4_spec false.
Definition HUF_decompress4X2_DCtx_wksp_spec : ident * funspec :=
  DECLARE _HUF_decompress4X2_DCtx_wksp huf_dctx4_spec true.

(* HUF_selectDecoder(dstSize, cSrcSize), 0 < dstSize <= 128 KB: 0 or 1, exactly ExHuf.x_huf_select's choice *)
Definition HUF_selectDecoder_spec : ident * funspec :=
  DECLARE _HUF_selectDecoder
  WITH gv: globals, n: Z, cs: Z
  PRE [ tulong, tulong ]
    PROP (0 < n <= ZSTD_BLOCKSIZE_MAX; 0 <= cs <= Int64.max_unsigned)
    PARAMS (Vlong (Int64.repr n); Vlong (Int64.repr cs)) GLOBALS (gv)
    SEP (zstd_globals gv)
  POST [ tuint ]
    EX r: Z,
    PROP (r = 0 \/ r = 1; r = Z.b2z (x_huf_select n cs))
    RETURN (Vint (Int.repr r))
    SEP (zstd_globals gv).

Definition S_TOP : funspecs :=
  [ HUF_getDTableDesc_spec; HUF_getDTableLog_spec; HUF_initFastDStream_spec; HUF_DecompressFastArgs_init_spec;
    HUF_initRemainingDStream_spec; HUF_decompress4X1_usingDTable_internal_fast_c_loop_spec;
    HUF_decompress4X1_usingDTable_internal_fast_spec; HUF_decompress4X1_DCtx_wksp_spec;
    HUF_decompress4X2_usingDTable_internal_fast_c_loop_spec; HUF_decompress4X2_usingDTable_internal_fast_spec;
    HUF_decompress4X2_DCtx_wksp_spec; HUF_selectDecoder_spec; HUF_decompress1X_usingDTable_spec;
    HUF_decompress1X1_DCtx_wksp_spec; HUF_decompress4X_usingDTable_spec; HUF_decompress4X_hufOnly_wksp_spec ].

Definition G_TOP : funspecs := (G_HUF ++ TOP_imports) ++ S_TOP.

(* ---------- bodies ---------- *)

Lemma body_HUF_getDTableDesc :
  semax_body Vprog Gprog f_HUF_getDTableDesc HUF_getDTableDesc_spec.
Proof.
  start_function. forward_call (sh, shd, p, q, existT (fun t => reptype t) t_dtdesc v).
  { simpl; rep_lia. }
  simpl projT1; simpl projT2. entailer!.
Qed.

Lemma algoTime_ints (Q: Z) : 0 <= Q < 16 ->
  exists a b c d, forall dflt: Inhabitant (list (val * val)),
    @Znth _ dflt Q algoTime_val = [(Vint a, Vint b); (Vint c, Vint d)].
Proof.
  intros HQ.
  assert (HF: Forall (fun x => exists a b c d, x = [(Vint a, Vint b); (Vint c, Vint d)]) algoTime_val).
  { unfold algoTime_val. repeat (apply Forall_cons; [do 4 eexists; reflexivity|]). apply Forall_nil. }
  rewrite Forall_forall in HF.
  assert (HL: Zlength algoTime_val = 16) by reflexivity.
  destruct (HF (Znth Q algoTime_val)) as (a & b & c & d & E); [apply Znth_In; lia|].
  exists a, b, c, d. intros dflt. rewrite <- E. unfold Znth.
  destruct (Z_lt_dec Q 0); [lia|]. apply nth_indep. rewrite Zlength_correct in HL. lia.
Qed.

(* the U32 arithmetic of HUF_selectDecoder does not wrap (times below 2^17): it is ExHuf's mod 2^32 one *)
Lemma sel_arith (t0 d0 t1 d1 D: Z) :
  0 <= t0 <= 4096 -> 0 <= d0 <= 256 -> 0 <= t1 <= 4096 -> 0 <= d1 <= 256 -> 0 <= D <= 512 ->
  Int.ltu (Int.add (Int.add (Int.repr t1) (Int.mul (Int.repr d1) (Int.repr D)))
                   (Int.shru (Int.add (Int.repr t1) (Int.mul (Int.repr d1) (Int.repr D))) (Int.repr 5)))
          (Int.add (Int.repr t0) (Int.mul (Int.repr d0) (Int.repr D))) =
  (((t1 + d1 * D) mod 2 ^ 32 + Z.shiftr ((t1 + d1 * D) mod 2 ^ 32) 5) mod 2 ^ 32 <? (t0 + d0 * D) mod 2 ^ 32).
Proof.
  intros. assert (0 <= d1 * D <= 256 * 512) by nia. assert (0 <= d0 * D <= 256 * 512) by nia.
  assert (Hs: 0 <= Z.shiftr (t1 + d1 * D) 5 <= t1 + d1 * D).
  { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]. }
  rewrite !(Z.mod_small (t1 + d1 * D)) by lia. rewrite (Z.mod_small (t0 + d0 * D)) by lia.
  rewrite (Z.mod_small (t1 + d1 * D + _)) by lia.
  unfold Int.ltu, Int.add, Int.mul, Int.shru.
  rewrite (Int.unsigned_repr d1), (Int.unsigned_repr D), (Int.unsigned_repr d0), (Int.unsigned_repr t1),
    (Int.unsigned_repr t0) by rep_lia.
  rewrite (Int.unsigned_repr (d1 * D)), (Int.unsigned_repr (d0 * D)) by rep_lia.
  rewrite (Int.unsigned_repr (t1 + d1 * D)), (Int.unsigned_repr (t0 + d0 * D)), (Int.unsigned_repr 5) by rep_lia.
  rewrite (Int.unsigned_repr (Z.shiftr _ _)) by rep_lia.
  rewrite Int.unsigned_repr by rep_lia.
  destruct (zlt _ _); symmetry; [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Qed.

(* HUF_selectDecoder's choice on algoTime's row Q is ExHuf.x_huf_select's *)
Lemma sel_exact (n cs Q: Z) (a b c d: int) :
  0 < n <= 131072 -> Q = (if cs >=? n then 15 else cs * 16 / n) -> 0 <= Q < 16 ->
  (forall dflt: Inhabitant (list (val * val)),
     @Znth _ dflt Q algoTime_val = [(Vint a, Vint b); (Vint c, Vint d)]) ->
  Int.ltu (Int.add (Int.add c (Int.mul d (Int.repr (Int64.Z_mod_modulus (Z.shiftr (Int64.Z_mod_modulus n) 8)))))
                   (Int.shru (Int.add c (Int.mul d (Int.repr (Int64.Z_mod_modulus
                                                                (Z.shiftr (Int64.Z_mod_modulus n) 8)))))
                             (Int.repr 5)))
          (Int.add a (Int.mul b (Int.repr (Int64.Z_mod_modulus (Z.shiftr (Int64.Z_mod_modulus n) 8))))) =
  x_huf_select n cs.
Proof.
  intros Hn HQ HQr HZ.
  assert (HD: 0 <= Z.shiftr n 8 <= 512).
  { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]. }
  rewrite !Int64.Z_mod_modulus_eq. rewrite (Z.mod_small n) by rep_lia.
  rewrite (Z.mod_small (Z.shiftr n 8)) by rep_lia.
  unfold x_huf_select. rewrite <- Z.geb_leb, <- HQ.
  rewrite (Z.mod_small (Z.shiftr n 8)) by lia.
  specialize (HZ []). clear HQ. generalize (Z.shiftr n 8) HD. intros D HD'.
  assert (HQ16: Q = 0 \/ Q = 1 \/ Q = 2 \/ Q = 3 \/ Q = 4 \/ Q = 5 \/ Q = 6 \/ Q = 7 \/ Q = 8 \/ Q = 9 \/
                Q = 10 \/ Q = 11 \/ Q = 12 \/ Q = 13 \/ Q = 14 \/ Q = 15) by lia.
  repeat (destruct HQ16 as [-> | HQ16]); try (subst Q);
    cbv [Znth algoTime_val] in HZ; simpl in HZ; inversion HZ; subst;
    simpl; apply sel_arith; lia.
Qed.

Lemma body_HUF_selectDecoder :
  semax_body Vprog Gprog f_HUF_selectDecoder HUF_selectDecoder_spec.
Proof.
  start_function. unfold ZSTD_BLOCKSIZE_MAX in *.
  forward_if (temp _t'1 (Vint (Int.repr (if cs >=? n then 15 else cs * 16 / n)))).
  - forward. destruct (cs >=? n) eqn:E; [|lia]. entailer!.
  - forward.
    { entailer!. apply (f_equal Int64.unsigned) in H2. rewrite Int64.unsigned_repr in H2 by rep_lia.
      rewrite Int64.unsigned_zero in H2. lia. }
    destruct (cs >=? n) eqn:E; [lia|]. entailer!.
    assert (0 <= cs * 16 / n) by (apply Z.div_pos; lia).
    assert (cs * 16 / n <= cs * 16) by (apply Z.div_le_upper_bound; nia).
    rewrite Int64.unsigned_repr by rep_lia; auto.
  - set (Q := if cs >=? n then 15 else cs * 16 / n).
    assert (HQ: 0 <= Q < 16).
    { subst Q. destruct (cs >=? n) eqn:E; [lia|].
      split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
    destruct (algoTime_ints Q HQ) as (a & b & c & d & HZ).
    forward. forward. unfold zstd_globals. Intros.
    forward. { rewrite HZ. entailer!. }
    forward. { rewrite HZ. entailer!. }
    forward. forward. { rewrite HZ. entailer!. }
    forward. { rewrite HZ. entailer!. }
    forward. forward. rewrite !HZ. simpl.
    forward.
    rewrite (sel_exact n cs Q a b c d ltac:(lia) eq_refl HQ HZ).
    Exists (Z.b2z (x_huf_select n cs)). unfold zstd_globals; entailer!.
    destruct (x_huf_select n cs); simpl; auto.
Qed.

Definition G_using : funspecs :=
  Gprog ++ [ HUF_getDTableDesc_spec; HUF_decompress1X1_usingDTable_internal_spec;
             HUF_decompress4X1_usingDTable_internal_spec; HUF_decompress1X2_usingDTable_internal_spec;
             HUF_decompress4X2_usingDTable_internal_spec ].

Lemma body_HUF_decompress1X_usingDTable :
  semax_body Vprog G_using f_HUF_decompress1X_usingDTable HUF_decompress1X_usingDTable_spec.
Proof.
  start_function. unfold hufdt_x_at at 1. Intros L res.
  match goal with HL: L = hufdt_log x2 ht |- _ => subst L end.
  forward_call (Tsh, v_dtd, sht, dt, (Vint (Int.repr 12), (Vint (Int.repr (if x2 then 1 else 0)),
                                       (Vint (Int.repr (hufdt_log x2 ht)), res)))).
  { memcpy_ok_B. }
  forward. { destruct x2; entailer!. }
  gather_SEP 1 3. replace_SEP 0 (hufdt_x_at x2 sht ht dt).
  { entailer!. unfold hufdt_x_at. Exists (hufdt_log x2 ht) res. entailer!. }
  apply semax_if_seq. forward_if.
  - destruct x2; [| match goal with Ht: typed_true _ _ |- _ => compute in Ht; discriminate end].
    forward_call (gv, sht, dt, ht, sho, ob, oc, d, n, sh, base, N, c, off, s).
    Intros vret. destruct vret as [r oc']. simpl fst in *; simpl snd in *. forward.
    Exists r oc'. entailer!.
  - destruct x2; [match goal with Ht: typed_false _ _ |- _ => compute in Ht; discriminate end |].
    forward_call (gv, sht, dt, ht, sho, ob, oc, d, n, sh, base, N, c, off, s).
    Intros vret. destruct vret as [r oc']. simpl fst in *; simpl snd in *. forward.
    Exists r oc'. entailer!.
Qed.

Lemma body_HUF_decompress4X_usingDTable :
  semax_body Vprog G_using f_HUF_decompress4X_usingDTable HUF_decompress4X_usingDTable_spec.
Proof.
  start_function. unfold hufdt_x_at at 1. Intros L res.
  match goal with HL: L = hufdt_log x2 ht |- _ => subst L end.
  forward_call (Tsh, v_dtd, sht, dt, (Vint (Int.repr 12), (Vint (Int.repr (if x2 then 1 else 0)),
                                       (Vint (Int.repr (hufdt_log x2 ht)), res)))).
  { memcpy_ok_B. }
  forward. { destruct x2; entailer!. }
  gather_SEP 1 3. replace_SEP 0 (hufdt_x_at x2 sht ht dt).
  { entailer!. unfold hufdt_x_at. Exists (hufdt_log x2 ht) res. entailer!. }
  apply semax_if_seq. forward_if.
  - destruct x2; [| match goal with Ht: typed_true _ _ |- _ => compute in Ht; discriminate end].
    forward_call (gv, sht, dt, ht, sho, ob, oc, d, n, sh, base, N, c, off, s).
    Intros vret. destruct vret as [r oc']. simpl fst in *; simpl snd in *. forward.
    Exists r oc'. entailer!.
  - destruct x2; [match goal with Ht: typed_false _ _ |- _ => compute in Ht; discriminate end |].
    forward_call (gv, sht, dt, ht, sho, ob, oc, d, n, sh, base, N, c, off, s).
    Intros vret. destruct vret as [r oc']. simpl fst in *; simpl snd in *. forward.
    Exists r oc'. entailer!.
Qed.

Definition G_dctx : funspecs :=
  Gprog ++ [ HUF_readDTableX1_wksp_spec; HUF_readDTableX2_wksp_spec; HUF_decompress1X1_usingDTable_internal_spec;
             HUF_decompress4X1_usingDTable_internal_spec; HUF_decompress4X2_usingDTable_internal_spec ].

(* ---------- the table field as raw memory, the window after the description ---------- *)

Lemma mb_merge (sh: share) (n m: Z) (p: val) : 0 <= n -> 0 <= m ->
  memory_block sh n p * memory_block sh m (offset_val n p) |-- memory_block sh (n + m) p.
Proof.
  intros Hn Hm. destruct p as [| | | | | b i]; try solve [entailer].
  assert_PROP (Ptrofs.unsigned i + n < Ptrofs.modulus /\
               Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr n)) + m < Ptrofs.modulus) as HB.
  { entailer!. }
  destruct HB as [HB1 HB2].
  assert (HA: Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr n)) = Ptrofs.unsigned i + n).
  { unfold Ptrofs.add. rewrite (Ptrofs.unsigned_repr n) by (pose proof (Ptrofs.unsigned_range i); rep_lia).
    apply Ptrofs.unsigned_repr. pose proof (Ptrofs.unsigned_range i); rep_lia. }
  rewrite HA in HB2.
  rewrite <- (Ptrofs.repr_unsigned i). rewrite memory_block_split by (pose proof (Ptrofs.unsigned_range i); lia).
  simpl offset_val. rewrite <- HA, !Ptrofs.repr_unsigned. cancel.
Qed.

Lemma hufhdr_mb (sh: share) (p: val) : hufhdr_at sh p |-- memory_block sh (4 + HUF_CELLBYTES) p.
Proof.
  unfold hufhdr_at. Intros ty lg res. sep_apply data_at_memory_block.
  change (sizeof t_dtdesc) with 4. apply mb_merge; unfold HUF_CELLBYTES; lia.
Qed.

Lemma hufdt_x_mb (x2: bool) (sh: share) (ht: huf_table) (p: val) :
  hufdt_x_at x2 sh ht p |-- memory_block sh (4 + HUF_CELLBYTES) p.
Proof.
  unfold hufdt_x_at. Intros L res. unfold HUF_TABLELOG_MAX in *.
  assert (HL: 1 <= 2 ^ L <= 4096).
  { destruct H as [[Hl _] _]. split.
    - change 1 with (2 ^ 0). apply Z.pow_le_mono_r; lia.
    - change 4096 with (2 ^ 12). apply Z.pow_le_mono_r; lia. }
  sep_apply data_at_memory_block. change (sizeof t_dtdesc) with 4. unfold HUF_CELLBYTES.
  destruct x2.
  - Intros c2. sep_apply data_at_memory_block. simpl sizeof. rewrite Z.max_r by lia.
    replace (4 + 4 * 2 ^ L) with (4 + 4 * 2 ^ L)%Z by lia.
    rewrite <- (offset_offset_val p 4 (4 * 2 ^ L)).
    sep_apply (mb_merge sh (4 * 2 ^ L) (16384 - 4 * 2 ^ L) (offset_val 4 p)); [lia | lia |].
    replace (4 * 2 ^ L + (16384 - 4 * 2 ^ L)) with 16384 by lia.
    sep_apply (mb_merge sh 4 16384 p); try lia; cancel.
  - sep_apply data_at_memory_block. simpl sizeof. rewrite Z.max_r by lia.
    rewrite <- (offset_offset_val p 4 (2 * 2 ^ L)).
    sep_apply (mb_merge sh (2 * 2 ^ L) (16384 - 2 * 2 ^ L) (offset_val 4 p)); [lia | lia |].
    replace (2 * 2 ^ L + (16384 - 2 * 2 ^ L)) with 16384 by lia.
    sep_apply (mb_merge sh 4 16384 p); try lia; cancel.
Qed.

Lemma win_ok_skip (sh: share) (N: Z) (c: list val) (off: Z) (s: list Z) (h: Z) :
  win_ok sh N c off (Zlength s) s -> 0 <= h <= Zlength s ->
  Zlength (skipn (Z.to_nat h) s) = Zlength s - h /\
  win_ok sh N c (off + h) (Zlength s - h) (skipn (Z.to_nat h) s).
Proof.
  intros (Hsh & Ho & Hon & HN & Hc & _ & Hb & Hw) Hh.
  assert (HZ: skipn (Z.to_nat h) s = sublist h (Zlength s) s).
  { unfold sublist. rewrite Zlength_correct, Nat2Z.id, firstn_all. reflexivity. }
  rewrite HZ. rewrite Zlength_sublist by lia.
  split; [lia|]. unfold win_ok. rewrite Zlength_sublist by lia.
  repeat split; auto; try lia.
  - unfold bytes_ok in *. apply Forall_sublist. auto.
  - replace (off + h + (Zlength s - h)) with (Zlength s + off) by lia. replace (off + h) with (h + off) by lia.
    rewrite <- (sublist_sublist (Zlength s) (off + Zlength s) h off) by lia. rewrite Hw.
    rewrite sublist_map. reflexivity.
Qed.

Lemma small_not_error (x: Z) : 0 <= x <= 2 ^ 32 -> is_error_code x = false.
Proof. intros. unfold is_error_code. apply Z.ltb_ge. lia. Qed.

Lemma out_after_refl (oc: list val) (d n: Z) : out_after oc oc d n.
Proof. split; [reflexivity | intros i _ _; reflexivity]. Qed.

(* ExHuf.xh_dctx by the outcome of the table reader x_readstats and of the size check hSize < cSrcSize *)
Lemma xh_dctx_none (x2 single: bool) (s: list Z) (n: Z) :
  x_readstats s = None -> xh_dctx x2 single s n = None.
Proof. intros E. unfold xh_dctx, x_huf_read. rewrite E. reflexivity. Qed.

Lemma xh_dctx_big (x2 single: bool) (s: list Z) (n: Z) (ht: huf_table) (h: Z) :
  x_readstats s = Some (ht, h) -> Zlength s <= h -> xh_dctx x2 single s n = None.
Proof.
  intros E Hh. unfold xh_dctx, x_huf_read. rewrite E. replace (Zlength s <=? h) with true by lia. reflexivity.
Qed.

Lemma xh_dctx_some (x2 single: bool) (s: list Z) (n: Z) (ht: huf_table) (h: Z) :
  x_readstats s = Some (ht, h) -> h < Zlength s ->
  xh_dctx x2 single s n =
  match x_huf_decode (xhuf_of x2 ht) single (skipn (Z.to_nat h) s) n with
  | Some l => Some (l, xhuf_of x2 ht)
  | None => None
  end.
Proof.
  intros E Hh. unfold xh_dctx, x_huf_read. rewrite E. replace (Zlength s <=? h) with false by lia. reflexivity.
Qed.

(* the exact clause at the end of the DCtx bodies: case on the internal decoder's model outcome *)
Ltac xfin :=
  try match goal with |- context [x_huf_decode ?t ?b ?ss ?m] =>
    let Ed := fresh "Ed" in destruct (x_huf_decode t b ss m) eqn:Ed; rewrite ?Ed in * end;
  cbv iota beta in *; repeat split; try reflexivity; try tauto.

Lemma body_HUF_decompress1X1_DCtx_wksp :
  semax_body Vprog G_dctx f_HUF_decompress1X1_DCtx_wksp HUF_decompress1X1_DCtx_wksp_spec.
Proof.
  start_function. forward.
  forward_call (gv, shd, dt, sh, base, N, c, off, s, shk, pk, nk).
  Intros vret. destruct vret as [h res]. simpl fst in *; simpl snd in *.
  match goal with Hr: forall x, huf_parse_desc s = Some x -> res = Some x |- _ => rename Hr into Hres end.
  match goal with Hx: res = x_readstats s |- _ => rename Hx into Hxr end.
  forward_call h.
  unfold ZSTD_BLOCKSIZE_MAX in *.
  destruct res as [[ht h']|].
  - match goal with Hm: h = h' /\ 1 <= h' <= Zlength s |- _ => destruct Hm as [<- Hh] end.
    assert (He: is_error_code h = false) by (apply small_not_error; lia).
    rewrite He. forward_if. { contradiction. }
    forward_if.
    + forward. Exists (Int64.unsigned (Int64.repr (-72))) oc. unfold huf_built.
      rewrite (xh_dctx_big _ _ s n ht h (eq_sym Hxr) ltac:(lia)).
      assert (huf_lits false s n = None) as ->.
      { unfold huf_lits. destruct (huf_parse_desc s) as [x|] eqn:Hp; [|reflexivity].
        specialize (Hres x eq_refl). inversion Hres; subst x.
        replace (h >=? Zlength s) with true by lia. reflexivity. }
      change (is_error_code (Int64.unsigned (Int64.repr (-72)))) with true.
      sep_apply hufdt_x_mb. rewrite Int64.repr_unsigned. entailer!. split; [rep_lia | apply out_after_refl].
    + forward. forward.
      destruct (win_ok_skip sh N c off s h ltac:(assumption) ltac:(lia)) as [Hzl Hwin].
      forward_call (gv, shd, dt, ht, sho, ob, oc, d, n, sh, base, N, c, off + h, skipn (Z.to_nat h) s).
      { entailer!. rewrite Hzl.
        match goal with Hb: field_compatible (Tarray tuchar N noattr) [] base |- _ =>
          pose proof (field_compatible_isptr _ _ _ Hb) end.
        match goal with Ho: field_compatible (Tarray tuchar (Zlength oc) noattr) [] ob |- _ =>
          pose proof (field_compatible_isptr _ _ _ Ho) end.
        destruct ob; try contradiction; destruct base; try contradiction; reflexivity. }
      { unfold ZSTD_BLOCKSIZE_MAX. lia. }
      Intros vret. destruct vret as [r oc']. simpl fst in *; simpl snd in *.
      forward. Exists r oc'.
      rewrite (xh_dctx_some _ _ s n ht h (eq_sym Hxr) ltac:(lia)). change (huf_dctx_x2 false n s) with false.
      assert (Hrs: exists h0, x_readstats s = Some (ht, h0)) by (exists h; auto).
      simpl negb in *.
      assert (HL: forall t l, huf_lits false s n = Some (t, l) ->
                  t = ht /\ huf_lits_with false ht (skipn (Z.to_nat h) s) n = Some l).
      { intros t l E. unfold huf_lits in E. destruct (huf_parse_desc s) as [x|] eqn:Hp; [|discriminate].
        specialize (Hres x eq_refl). inversion Hres; subst x.
        replace (h >=? Zlength s) with false in E by lia. unfold huf_lits_with.
        destruct (huf_decode_stream ht (skipn (Z.to_nat h) s) n); inversion E; auto. }
      unfold huf_built.
      destruct (huf_lits false s n) as [[t l]|] eqn:E.
      * destruct (HL t l eq_refl) as [<- Hw]. rewrite Hw in *. simpl option_map. cbv iota beta.
        destruct (is_error_code r) eqn:Er.
        { sep_apply hufdt_x_mb. entailer!. all: xfin. }
        { Exists t. entailer!. all: xfin. }
      * simpl option_map. cbv iota beta.
        destruct (is_error_code r) eqn:Er.
        { sep_apply hufdt_x_mb. entailer!. all: xfin. }
        { Exists ht. entailer!. all: xfin. }
  - match goal with Hm: is_error_code h = true |- _ => rename Hm into He end.
    rewrite He. forward_if.
    + forward. Exists h oc. unfold huf_built. rewrite He.
      rewrite (xh_dctx_none _ _ s n (eq_sym Hxr)).
      assert (huf_lits false s n = None) as ->.
      { unfold huf_lits. destruct (huf_parse_desc s) as [x|] eqn:Hp; [|reflexivity].
        specialize (Hres x eq_refl). discriminate. }
      sep_apply hufhdr_mb. entailer!. apply out_after_refl.
    + exfalso. apply Int.one_not_zero. assumption.
Qed.

Lemma body_HUF_decompress4X1_DCtx_wksp :
  semax_body Vprog G_dctx f_HUF_decompress4X1_DCtx_wksp HUF_decompress4X1_DCtx_wksp_spec.
Proof.
  start_function. forward.
  forward_call (gv, shd, dt, sh, base, N, c, off, s, shk, pk, nk).
  Intros vret. destruct vret as [h res]. simpl fst in *; simpl snd in *.
  match goal with Hr: forall x, huf_parse_desc s = Some x -> res = Some x |- _ => rename Hr into Hres end.
  match goal with Hx: res = x_readstats s |- _ => rename Hx into Hxr end.
  forward_call h.
  unfold ZSTD_BLOCKSIZE_MAX in *.
  destruct res as [[ht h']|].
  - match goal with Hm: h = h' /\ 1 <= h' <= Zlength s |- _ => destruct Hm as [<- Hh] end.
    assert (He: is_error_code h = false) by (apply small_not_error; lia).
    rewrite He. forward_if. { contradiction. }
    forward_if.
    + forward. Exists (Int64.unsigned (Int64.repr (-72))) oc. unfold huf_built.
      rewrite (xh_dctx_big _ _ s n ht h (eq_sym Hxr) ltac:(lia)).
      assert (huf_lits true s n = None) as ->.
      { unfold huf_lits. destruct (huf_parse_desc s) as [x|] eqn:Hp; [|reflexivity].
        specialize (Hres x eq_refl). inversion Hres; subst x.
        replace (h >=? Zlength s) with true by lia. reflexivity. }
      change (is_error_code (Int64.unsigned (Int64.repr (-72)))) with true.
      sep_apply hufdt_x_mb. rewrite Int64.repr_unsigned. entailer!. split; [rep_lia | apply out_after_refl].
    + forward. forward.
      destruct (win_ok_skip sh N c off s h ltac:(assumption) ltac:(lia)) as [Hzl Hwin].
      forward_call (gv, shd, dt, ht, sho, ob, oc, d, n, sh, base, N, c, off + h, skipn (Z.to_nat h) s).
      { entailer!. rewrite Hzl.
        match goal with Hb: field_compatible (Tarray tuchar N noattr) [] base |- _ =>
          pose proof (field_compatible_isptr _ _ _ Hb) end.
        match goal with Ho: field_compatible (Tarray tuchar (Zlength oc) noattr) [] ob |- _ =>
          pose proof (field_compatible_isptr _ _ _ Ho) end.
        destruct ob; try contradiction; destruct base; try contradiction; reflexivity. }
      { unfold ZSTD_BLOCKSIZE_MAX. lia. }
      Intros vret. destruct vret as [r oc']. simpl fst in *; simpl snd in *.
      forward. Exists r oc'.
      rewrite (xh_dctx_some _ _ s n ht h (eq_sym Hxr) ltac:(lia)).
      assert (Hrs: exists h0, x_readstats s = Some (ht, h0)) by (exists h; auto).
      simpl negb in *.
      assert (HL: forall t l, huf_lits true s n = Some (t, l) ->
                  t = ht /\ huf_lits_with true ht (skipn (Z.to_nat h) s) n = Some l).
      { intros t l E. unfold huf_lits in E. destruct (huf_parse_desc s) as [x|] eqn:Hp; [|discriminate].
        specialize (Hres x eq_refl). inversion Hres; subst x.
        replace (h >=? Zlength s) with false in E by lia. unfold huf_lits_with.
        destruct (huf_decode_4streams ht (skipn (Z.to_nat h) s) n); inversion E; auto. }
      unfold huf_built.
      destruct (huf_lits true s n) as [[t l]|] eqn:E.
      * destruct (HL t l eq_refl) as [<- Hw]. rewrite Hw in *. simpl option_map. cbv iota beta.
        destruct (is_error_code r) eqn:Er.
        { sep_apply hufdt_x_mb. entailer!. all: xfin. }
        { Exists t. entailer!. all: xfin. }
      * simpl option_map. cbv iota beta.
        destruct (is_error_code r) eqn:Er.
        { sep_apply hufdt_x_mb. entailer!. all: xfin. }
        { Exists ht. entailer!. all: xfin. }
  - match goal with Hm: is_error_code h = true |- _ => rename Hm into He end.
    rewrite He. forward_if.
    + forward. Exists h oc. unfold huf_built. rewrite He.
      rewrite (xh_dctx_none _ _ s n (eq_sym Hxr)).
      assert (huf_lits true s n = None) as ->.
      { unfold huf_lits. destruct (huf_parse_desc s) as [x|] eqn:Hp; [|reflexivity].
        specialize (Hres x eq_refl). discriminate. }
      sep_apply hufhdr_mb. entailer!. apply out_after_refl.
    + exfalso. apply Int.one_not_zero. assumption.
Qed.

Lemma body_HUF_decompress4X2_DCtx_wksp :
  semax_body Vprog G_dctx f_HUF_decompress4X2_DCtx_wksp HUF_decompress4X2_DCtx_wksp_spec.
Proof.
  start_function. forward.
  forward_call (gv, shd, dt, sh, base, N, c, off, s, shk, pk, nk).
  Intros vret. destruct vret as [h res]. simpl fst in *; simpl snd in *.
  match goal with Hr: forall x, huf_parse_desc s = Some x -> res = Some x |- _ => rename Hr into Hres end.
  match goal with Hx: res = x_readstats s |- _ => rename Hx into Hxr end.
  forward_call h.
  unfold ZSTD_BLOCKSIZE_MAX in *.
  destruct res as [[ht h']|].
  - match goal with Hm: h = h' /\ 1 <= h' <= Zlength s |- _ => destruct Hm as [<- Hh] end.
    assert (He: is_error_code h = false) by (apply small_not_error; lia).
    rewrite He. forward_if. { contradiction. }
    forward_if.
    + forward. Exists (Int64.unsigned (Int64.repr (-72))) oc. unfold huf_built.
      rewrite (xh_dctx_big _ _ s n ht h (eq_sym Hxr) ltac:(lia)).
      assert (huf_lits true s n = None) as ->.
      { unfold huf_lits. destruct (huf_parse_desc s) as [x|] eqn:Hp; [|reflexivity].
        specialize (Hres x eq_refl). inversion Hres; subst x.
        replace (h >=? Zlength s) with true by lia. reflexivity. }
      change (is_error_code (Int64.unsigned (Int64.repr (-72)))) with true.
      sep_apply hufdt_x_mb. rewrite Int64.repr_unsigned. entailer!. split; [rep_lia | apply out_after_refl].
    + forward. forward.
      destruct (win_ok_skip sh N c off s h ltac:(assumption) ltac:(lia)) as [Hzl Hwin].
      forward_call (gv, shd, dt, ht, sho, ob, oc, d, n, sh, base, N, c, off + h, skipn (Z.to_nat h) s).
      { entailer!. rewrite Hzl.
        match goal with Hb: field_compatible (Tarray tuchar N noattr) [] base |- _ =>
          pose proof (field_compatible_isptr _ _ _ Hb) end.
        match goal with Ho: field_compatible (Tarray tuchar (Zlength oc) noattr) [] ob |- _ =>
          pose proof (field_compatible_isptr _ _ _ Ho) end.
        destruct ob; try contradiction; destruct base; try contradiction; reflexivity. }
      { unfold ZSTD_BLOCKSIZE_MAX. lia. }
      Intros vret. destruct vret as [r oc']. simpl fst in *; simpl snd in *.
      forward. Exists r oc'.
      rewrite (xh_dctx_some _ _ s n ht h (eq_sym Hxr) ltac:(lia)).
      assert (Hrs: exists h0, x_readstats s = Some (ht, h0)) by (exists h; auto).
      simpl negb in *.
      assert (HL: forall t l, huf_lits true s n = Some (t, l) ->
                  t = ht /\ huf_lits_with true ht (skipn (Z.to_nat h) s) n = Some l).
      { intros t l E. unfold huf_lits in E. destruct (huf_parse_desc s) as [x|] eqn:Hp; [|discriminate].
        specialize (Hres x eq_refl). inversion Hres; subst x.
        replace (h >=? Zlength s) with false in E by lia. unfold huf_lits_with.
        destruct (huf_decode_4streams ht (skipn (Z.to_nat h) s) n); inversion E; auto. }
      unfold huf_built.
      destruct (huf_lits true s n) as [[t l]|] eqn:E.
      * destruct (HL t l eq_refl) as [<- Hw]. rewrite Hw in *. simpl option_map. cbv iota beta.
        destruct (is_error_code r) eqn:Er.
        { sep_apply hufdt_x_mb. entailer!. all: xfin. }
        { Exists t. entailer!. all: xfin. }
      * simpl option_map. cbv iota beta.
        destruct (is_error_code r) eqn:Er.
        { sep_apply hufdt_x_mb. entailer!. all: xfin. }
        { Exists ht. entailer!. all: xfin. }
  - match goal with Hm: is_error_code h = true |- _ => rename Hm into He end.
    rewrite He. forward_if.
    + forward. Exists h oc. unfold huf_built. rewrite He.
      rewrite (xh_dctx_none _ _ s n (eq_sym Hxr)).
      assert (huf_lits true s n = None) as ->.
      { unfold huf_lits. destruct (huf_parse_desc s) as [x|] eqn:Hp; [|reflexivity].
        specialize (Hres x eq_refl). discriminate. }
      sep_apply hufhdr_mb. entailer!. apply out_after_refl.
    + exfalso. apply Int.one_not_zero. assumption.
Qed.

(* the table reader fails on an empty description *)
Lemma x_readstats_nil : x_readstats [] = None.
Proof. vm_compute. reflexivity. Qed.

Definition G_only : funspecs :=
  Gprog ++ [ HUF_selectDecoder_spec; HUF_decompress4X1_DCtx_wksp_spec; HUF_decompress4X2_DCtx_wksp_spec ].

Lemma body_HUF_decompress4X_hufOnly_wksp :
  semax_body Vprog G_only f_HUF_decompress4X_hufOnly_wksp HUF_decompress4X_hufOnly_wksp_spec.
Proof.
  start_function. unfold ZSTD_BLOCKSIZE_MAX in *.
  forward_if.
  - exfalso. match goal with Hz: Int64.repr n = Int64.zero |- _ => rename Hz into Hn0 end.
    apply (f_equal Int64.unsigned) in Hn0. rewrite Int64.unsigned_repr in Hn0 by rep_lia.
    rewrite Int64.unsigned_zero in Hn0. lia.
  - forward_if.
    + forward. Exists (Int64.unsigned (Int64.repr (-20))) oc.
      assert (Hs0: Zlength s = 0).
      { match goal with Hz: Int64.repr (Zlength s) = Int64.zero |- _ => rename Hz into Hs0' end.
        apply (f_equal Int64.unsigned) in Hs0'.
        rewrite Int64.unsigned_repr in Hs0' by (pose proof (Zlength_nonneg s); rep_lia).
        rewrite Int64.unsigned_zero in Hs0'. lia. }
      assert (Hbs: bytes_ok s) by (match goal with Hw: win_ok _ _ _ _ _ _ |- _ => destruct Hw as (_ & _ & _ & _ & _ & _ & Hb & _); exact Hb end).
      assert (huf_lits true s n = None) as ->.
      { unfold huf_lits. destruct (huf_parse_desc s) as [[t h]|] eqn:Hp; [|reflexivity].
        destruct (huf_parse_desc_facts _ _ _ Hbs Hp) as (_ & _ & _ & Hh). lia. }
      assert (Hs: s = []) by (apply Zlength_nil_inv; lia). subst s.
      rewrite (xh_dctx_none _ _ [] n x_readstats_nil).
      unfold huf_built. change (is_error_code (Int64.unsigned (Int64.repr (-20)))) with true.
      sep_apply hufhdr_mb. rewrite Int64.repr_unsigned. entailer!. split; [rep_lia | apply out_after_refl].
    + forward_call (gv, n, Zlength s).
      Intros algo. apply semax_if_seq. forward_if.
      * assert (Hsel: huf_dctx_x2 true n s = true).
        { unfold huf_dctx_x2. destruct (x_huf_select n (Zlength s)); [reflexivity|].
          exfalso. subst algo. simpl Z.b2z in *. auto. }
        forward_call (gv, shd, dt, sho, ob, oc, d, n, sh, base, N, c, off, s, shk, pk, nk).
        Intros vret. destruct vret as [r oc']. simpl fst in *; simpl snd in *. forward.
        Exists r oc'. rewrite Hsel. entailer!.
      * assert (Hsel: huf_dctx_x2 true n s = false).
        { unfold huf_dctx_x2. destruct (x_huf_select n (Zlength s)); [|reflexivity].
          exfalso. subst algo. simpl Z.b2z in *. apply Int.one_not_zero. assumption. }
        forward_call (gv, shd, dt, sho, ob, oc, d, n, sh, base, N, c, off, s, shk, pk, nk).
        Intros vret. destruct vret as [r oc']. simpl fst in *; simpl snd in *. forward.
        Exists r oc'. rewrite Hsel. entailer!.
Qed.

(* ---------- the obligation ---------- *)

Lemma top_nodup : NoDup (map fst Vprog ++ map fst G_TOP).
Proof.
  apply nodupb_ok. vm_compute. reflexivity.
Qed.

Ltac in_spec := solve [repeat (first [left; reflexivity | right])].

Lemma top_lift (G: funspecs) (ix: ident * funspec) (f: function) :
  zstd_fun (fst ix) f -> fn_callconv f = callingconvention_of_funspec (snd ix) ->
  semax_body Vprog G f ix -> incl G G_TOP -> body_ok G_TOP ix.
Proof.
  intros Hf Hcc Hb Hinc. apply (body_ok_mono G); [exists f; auto | exact Hinc | exact top_nodup].
Qed.

Lemma incl_Gprog_TOP : incl Gprog G_TOP.
Proof.
  intros x Hx. unfold G_TOP, G_HUF, G_B0. rewrite !in_app_iff. tauto.
Qed.

Lemma in_imp_TOP x : In x TOP_imports -> In x G_TOP.
Proof. intros H. unfold G_TOP. rewrite !in_app_iff. tauto. Qed.

Lemma in_S_TOP x : In x S_TOP -> In x G_TOP.
Proof. intros H. unfold G_TOP. rewrite !in_app_iff. tauto. Qed.

Ltac incl_top :=
  apply incl_app; [apply incl_Gprog_TOP | intros x Hx; cbn [In] in Hx;
    repeat (destruct Hx as [<-|Hx]; [first [apply in_imp_TOP; unfold TOP_imports; in_spec
                                           | apply in_S_TOP; unfold S_TOP; in_spec] | ]); contradiction].

Lemma TOP_ok : TOP_obligation.
Proof.
  unfold TOP_obligation, subtree_ok. exists S_TOP. split; [reflexivity | split].
  - intros x Hx. unfold TOP_exports in Hx. unfold S_TOP. repeat (destruct Hx as [<-|Hx]; [in_spec|]); contradiction.
  - change ((G_HUF ++ TOP_imports) ++ S_TOP) with G_TOP. unfold S_TOP.
    repeat apply Forall_cons; try apply Forall_nil.
    + eapply top_lift; [reflexivity | reflexivity | exact body_HUF_getDTableDesc | apply incl_Gprog_TOP].
    + apply body_ok_vacuous. reflexivity.
    + apply body_ok_vacuous. reflexivity.
    + apply body_ok_vacuous. reflexivity.
    + apply body_ok_vacuous. reflexivity.
    + apply body_ok_vacuous. reflexivity.
    + apply body_ok_vacuous. reflexivity.
    + eapply top_lift; [reflexivity | reflexivity | exact body_HUF_decompress4X1_DCtx_wksp | unfold G_dctx; incl_top].
    + apply body_ok_vacuous. reflexivity.
    + apply body_ok_vacuous. reflexivity.
    + eapply top_lift; [reflexivity | reflexivity | exact body_HUF_decompress4X2_DCtx_wksp | unfold G_dctx; incl_top].
    + eapply top_lift; [reflexivity | reflexivity | exact body_HUF_selectDecoder | apply incl_Gprog_TOP].
    + eapply top_lift; [reflexivity | reflexivity | exact body_HUF_decompress1X_usingDTable | unfold G_using; incl_top].
    + eapply top_lift; [reflexivity | reflexivity | exact body_HUF_decompress1X1_DCtx_wksp | unfold G_dctx; incl_top].
    + eapply top_lift; [reflexivity | reflexivity | exact body_HUF_decompress4X_usingDTable | unfold G_using; incl_top].
    + eapply top_lift; [reflexivity | reflexivity | exact body_HUF_decompress4X_hufOnly_wksp | unfold G_only; incl_top].
Qed.
