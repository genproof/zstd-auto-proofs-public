(* X1D, contract item 17 ('bytes in, bytes out'): HufIface.huf_x_using_spec's POST has
   (byte_cells oc -> byte_cells oc').  The body specifications of HufX1DSpecs.v are restated here with that
   conjunct (first in PROP); HufX1D1BC.v / HufX1D4BC.v prove the bodies against them, HufX1D.v assembles X1D_ok
   with X1D_specs_bc.  (New module: the checker forbids editing the tracked HufX1DSpecs.v.) *)
Require Export Zstd.proof.dec.B.huf.HufX1DSpecs.
Local Open Scope logic.

(* byte_cells (DecRep): written model bytes keep an all-byte output array all-byte *)
Lemma byte_cells_zbytes (l: list Z) : bytes_ok l -> byte_cells (zbytes l).
Proof.
  intros H. unfold byte_cells. induction H as [|x l Hx _ IH]; constructor; [|exact IH].
  exists x. split; [exact Hx | reflexivity].
Qed.

Lemma byte_cells_app (a b: list val) : byte_cells a -> byte_cells b -> byte_cells (a ++ b).
Proof. intros Ha Hb. unfold byte_cells in *. apply Forall_app; auto. Qed.

Lemma byte_cells_sublist (l: list val) (i j: Z) : byte_cells l -> byte_cells (sublist i j l).
Proof. intros H. unfold byte_cells in *. apply Forall_sublist. exact H. Qed.

Lemma byte_cells_splice (oc: list val) (l: list Z) (a b: Z) :
  byte_cells oc -> bytes_ok l -> byte_cells (sublist 0 a oc ++ zbytes l ++ sublist b (Zlength oc) oc).
Proof.
  intros Hoc Hl. apply byte_cells_app; [apply byte_cells_sublist; exact Hoc|].
  apply byte_cells_app; [apply byte_cells_zbytes; exact Hl | apply byte_cells_sublist; exact Hoc].
Qed.

Lemma byte_cells_upd (oc: list val) (i z: Z) :
  byte_cells oc -> 0 <= z < 256 -> byte_cells (upd_Znth i oc (Vint (Int.repr z))).
Proof.
  intros Hoc Hz. unfold byte_cells in *.
  destruct (Z_lt_le_dec i 0) as [Hi|Hi]; [rewrite upd_Znth_out_of_range by lia; exact Hoc|].
  destruct (Z_lt_le_dec i (Zlength oc)) as [Hi'|Hi']; [|rewrite upd_Znth_out_of_range by lia; exact Hoc].
  rewrite upd_Znth_unfold by lia. apply Forall_app; split; [apply Forall_sublist; exact Hoc|].
  constructor; [exists z; split; [exact Hz | reflexivity] | apply Forall_sublist; exact Hoc].
Qed.

Lemma byte_cells_out (oc oc': list val) (d n: Z) (l: list Z) :
  out_after oc oc' d n -> 0 <= d -> 0 <= n -> d + n <= Zlength oc ->
  sublist d (d + n) oc' = zbytes l -> bytes_ok l -> byte_cells oc -> byte_cells oc'.
Proof.
  intros [Hlen Hout] Hd Hn Hdn Hsub Hl Hoc. unfold byte_cells in *.
  rewrite Forall_forall in Hoc. unfold bytes_ok in Hl. rewrite Forall_forall in Hl.
  apply Forall_forall. intros x Hx. apply In_Znth in Hx as (i & Hi & <-).
  destruct (Z_lt_le_dec i d) as [Hlt|Hge]; [rewrite Hout by lia; apply Hoc, Znth_In; lia|].
  destruct (Z_lt_le_dec i (d + n)) as [Hlt'|Hge']; [|rewrite Hout by lia; apply Hoc, Znth_In; lia].
  assert (HL: Zlength l = n).
  { rewrite <- (Zlength_map _ _ (fun b : Z => Vint (Int.repr b)) l), <- Hsub. rewrite Zlength_sublist; lia. }
  replace (Znth i oc') with (Znth (i - d) (sublist d (d + n) oc')) by (rewrite Znth_sublist by lia; f_equal; lia).
  rewrite Hsub, Znth_map by lia. exists (Znth (i - d) l). split; [|reflexivity].
  apply Hl, Znth_In; lia.
Qed.

(* ---------- the bodies (dst, dstSize, cSrc, cSrcSize, DTable) ----------
   huf_x_using_spec four false without the flags, and with a nonempty output array (a pointer comparison
   needs a valid pointer); exactly (last PROP): ExHuf.x_huf_decode's outcome. *)
Definition huf_x1_body_spec_bc (four: bool) : funspec :=
  WITH gv: globals, sht: share, dt: val, ht: huf_table, sho: share, ob: val, oc: list val, d: Z, n: Z,
       sh: share, base: val, N: Z, c: list val, off: Z, s: list Z
  PRE [ tptr tvoid, tulong, tptr tvoid, tulong, tptr tuint ]
    PROP (readable_share sht; writable_share sho; 1 <= Zlength oc;
          0 <= d; (if four then 6 else 0) <= n <= ZSTD_BLOCKSIZE_MAX; d + n <= Zlength oc;
          Zlength s <= ZSTD_BLOCKSIZE_MAX; win_ok sh N c off (Zlength s) s)
    PARAMS (offset_val d ob; Vlong (Int64.repr n); offset_val off base; Vlong (Int64.repr (Zlength s)); dt)
    GLOBALS (gv)
    SEP (zstd_globals gv; hufdt_x_at false sht ht dt; data_at sho (tarray tuchar (Zlength oc)) oc ob;
         data_at sh (tarray tuchar N) c base)
  POST [ tulong ]
    EX r: Z, EX oc': list val,
    PROP (byte_cells oc -> byte_cells oc'; 0 <= r <= Int64.max_unsigned; out_after oc oc' d n;
          is_error_code r = false -> r = n /\ exists l, sublist d (d + n) oc' = zbytes l /\ bytes_ok l;
          match huf_lits_with four ht s n with
          | Some l => r = n /\ sublist d (d + n) oc' = zbytes l
          | None => True
          end;
          match x_huf_decode (xhuf_of false ht) (negb four) s n with
          | None => is_error_code r = true
          | Some l => r = n /\ sublist d (d + n) oc' = zbytes l
          end)
    RETURN (Vlong (Int64.repr r))
    SEP (zstd_globals gv; hufdt_x_at false sht ht dt; data_at sho (tarray tuchar (Zlength oc)) oc' ob;
         data_at sh (tarray tuchar N) c base).

Definition HUF_decompress1X1_usingDTable_internal_body_bc_spec : ident * funspec :=
  DECLARE _HUF_decompress1X1_usingDTable_internal_body huf_x1_body_spec_bc false.
Definition HUF_decompress4X1_usingDTable_internal_body_bc_spec : ident * funspec :=
  DECLARE _HUF_decompress4X1_usingDTable_internal_body huf_x1_body_spec_bc true.
Definition HUF_decompress4X1_usingDTable_internal_default_bc_spec : ident * funspec :=
  DECLARE _HUF_decompress4X1_usingDTable_internal_default huf_x1_body_spec_bc true.

(* ---------- the specifications of ids_X1D, in its order ---------- *)
Definition X1D_specs_bc : funspecs :=
  [ HUF_decodeSymbolX1_spec; HUF_decodeStreamX1_spec; HUF_decompress1X1_usingDTable_internal_body_bc_spec;
    HUF_decompress4X1_usingDTable_internal_body_bc_spec; HUF_decompress4X1_usingDTable_internal_default_bc_spec;
    HUF_decompress1X1_usingDTable_internal_spec; HUF_decompress4X1_usingDTable_internal_spec ].

