(* Facts on the exact stream model (model/ExStream.v) that the proof of ZSTD_decompressStream's exact claim
   (Spec_api6.stream_exact) uses: plain Coq, generic in the block decoder like ExStream itself, then
   specialised to model/Exact.v's instance.

   - the history: zs_run of h ++ [c] is one zstep after zs_run h, and zs_call is that step's outcome;
   - the call: zstep is the loop z_loop followed by the epilogue z_epi (the code after ZSTD_decompressStream's
     loop); z_loop unfolds one iteration (one_iter) at a time, and one_iter is the switch's case of the
     stream stage (one lemma per stage);
   - the fuel: on the states the calls reach (zinv), every iteration that goes on lowers the potential zpot
     (twice the input left, plus 1, or 2 in zdss_flush), so the fuel 2 n + 4 of zstep is never exhausted
     and any fuel above the potential gives the same outcome.  The proof of the C loop carries "the
     model's loop from here, with fuel f > zpot, ends in the call's outcome" as its invariant;
   - zstate_init (a new context, or one reset with the parameters) and zinv on every reached state;
   - zinv also carries the bounds the proof reads the model's values back with (model/ExStreamBnd.v): fields in
     range, outStart <= outEnd <= outBuffSize, a ring of outBuffSize bytes, ring offsets within it, inBuff empty
     outside zdss_load, and room in the ring for a compressed block that meets an extDict.  They need properties of
     the block decoder (the Section's xgood hypotheses), proved for model/Exact.v's instance at the end;
   - and, last (zi_over), the bound on oversizedDuration that keeps it within its size_t (model/ExStreamOver.v). *)
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Xxh64.
Require Import Zstd.proof.model.ExCall Zstd.proof.model.ExStream.
Require Zstd.proof.model.ExHuf Zstd.proof.model.ExBlock Zstd.proof.model.ExFrame Zstd.proof.model.Exact.
Require Zstd.proof.model.ExFrameFacts Zstd.proof.model.ExBlockBytes Zstd.proof.model.ExBlockWritten.
Require Zstd.proof.model.ExBlockLen.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

(* ---------- bytes ---------- *)

Lemma zf_Zlength_nonneg {A: Type} (l: list A) : 0 <= Zlength l.
Proof. rewrite Zlength_correct. lia. Qed.

Lemma zf_forall_firstn {A: Type} (P: A -> Prop) (n: nat) (l: list A) : Forall P l -> Forall P (firstn n l).
Proof.
  revert l. induction n as [|n IH]; intros l H; [constructor|].
  destruct l as [|a l]; [constructor|]. inversion H; subst. simpl. constructor; auto.
Qed.

Lemma zf_forall_skipn {A: Type} (P: A -> Prop) (n: nat) (l: list A) : Forall P l -> Forall P (skipn n l).
Proof.
  revert l. induction n as [|n IH]; intros l H; [exact H|].
  destruct l as [|a l]; [constructor|]. inversion H; subst. simpl. auto.
Qed.

Lemma zf_bytes_slice (l: list Z) (i k: Z) : bytes_ok l -> bytes_ok (slice l i k).
Proof. intros H. unfold slice. apply zf_forall_firstn, zf_forall_skipn, H. Qed.

Lemma zf_bytes_app (l1 l2: list Z) : bytes_ok l1 -> bytes_ok l2 -> bytes_ok (l1 ++ l2).
Proof. intros H1 H2. apply Forall_app; split; assumption. Qed.

Lemma zf_le_value_nonneg (l: list Z) : bytes_ok l -> 0 <= le_value l.
Proof.
  induction 1 as [|b l Hb _ IH]; cbn [le_value]; [lia|]. unfold is_byte in Hb. lia.
Qed.

Lemma zf_le_field_nonneg (l: list Z) (i k: Z) : bytes_ok l -> 0 <= le_field l i k.
Proof. intros H. apply zf_le_value_nonneg, zf_bytes_slice, H. Qed.

(* ZSTD_getFrameHeader asks for more bytes than it has *)
Lemma get_frame_header_more (s: list Z) (k: Z) : get_frame_header s = FH_more k -> Zlength s < k.
Proof.
  unfold get_frame_header. intros H.
  destruct (Zlength s <? 5) eqn:E5.
  - apply Z.ltb_lt in E5.
    destruct (Zlength s >? 0); [destruct (_ && _)|]; inversion H; subst; lia.
  - destruct (negb (le_field s 0 4 =? ZSTD_MAGICNUMBER)).
    + destruct (is_skippable_magic (le_field s 0 4)); [|discriminate].
      destruct (Zlength s <? ZSTD_SKIPPABLEHEADERSIZE) eqn:E8; [|discriminate].
      apply Z.ltb_lt in E8. inversion H; subst; exact E8.
    + destruct (Zlength s <? fhd_header_size (byte_at s 4)) eqn:Eh.
      * apply Z.ltb_lt in Eh. inversion H; subst; exact Eh.
      * destruct (negb (Z.land (byte_at s 4) 8 =? 0)); [discriminate|].
        destruct (_ && _); discriminate.
Qed.

(* ZSTD_getcBlockSize's size is never negative on bytes *)
Lemma cblock_size_nonneg (s: list Z) (c: Z) : bytes_ok s -> cblock_size s = Some c -> 0 <= c.
Proof.
  intros Hb. unfold cblock_size.
  destruct (Zlength s <? ZSTD_blockHeaderSize); [discriminate|].
  destruct (bp_type (block_props_of s) =? 1); [intros H; inversion H; lia|].
  destruct (bp_type (block_props_of s) =? 3); [discriminate|].
  intros H; inversion H; subst. unfold block_props_of; simpl.
  apply Z.shiftr_nonneg, zf_le_field_nonneg, Hb.
Qed.

Lemma zf_byte_at (l: list Z) (i: Z) : bytes_ok l -> is_byte (byte_at l i).
Proof.
  intros H. unfold byte_at. destruct (nth_in_or_default (Z.to_nat i) l 0) as [Hi|Hi].
  - exact (proj1 (Forall_forall _ _) H _ Hi).
  - rewrite Hi. unfold is_byte. lia.
Qed.

Lemma zf_le_value_lt (l: list Z) : bytes_ok l -> le_value l < 2 ^ (8 * Zlength l).
Proof.
  induction 1 as [|b l Hb Hl IH]; cbn [le_value].
  - rewrite Zlength_nil. simpl. lia.
  - rewrite Zlength_cons. unfold is_byte in Hb. pose proof (zf_le_value_nonneg l Hl).
    pose proof (zf_Zlength_nonneg l).
    replace (8 * Z.succ (Zlength l)) with (8 + 8 * Zlength l) by lia.
    rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256. lia.
Qed.

Lemma zf_Zlength_slice_le (l: list Z) (i k: Z) : 0 <= k -> Zlength (slice l i k) <= k.
Proof.
  intros Hk. unfold slice. rewrite Zlength_correct, firstn_length. lia.
Qed.

Lemma zf_Zlength_slice (l: list Z) (i k: Z) :
  0 <= i -> 0 <= k -> i + k <= Zlength l -> Zlength (slice l i k) = k.
Proof.
  intros Hi Hk H. unfold slice. rewrite Zlength_correct in *. rewrite firstn_length, skipn_length. lia.
Qed.

(* a little-endian field of k bytes is below 2^(8k) *)
Lemma zf_le_field_lt (l: list Z) (i k: Z) : bytes_ok l -> 0 <= k -> le_field l i k < 2 ^ (8 * k).
Proof.
  intros Hb Hk. unfold le_field.
  pose proof (zf_le_value_lt _ (zf_bytes_slice l i k Hb)) as H.
  pose proof (zf_Zlength_slice_le l i k Hk). pose proof (zf_Zlength_nonneg (slice l i k)).
  assert (2 ^ (8 * Zlength (slice l i k)) <= 2 ^ (8 * k)) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

(* the fields of a block header: the type is one of four, the size a 21-bit number *)
Lemma zf_bp_bounds (s: list Z) :
  bytes_ok s -> 0 <= bp_type (block_props_of s) <= 3 /\ 0 <= bp_origSize (block_props_of s) < 2 ^ 21.
Proof.
  intros Hb. unfold block_props_of; cbn [bp_type bp_origSize].
  pose proof (zf_le_field_lt s 0 3 Hb ltac:(lia)) as Hlt. pose proof (zf_le_field_nonneg s 0 3 Hb) as H0.
  set (h := le_field s 0 3) in *. change (2 ^ (8 * 3)) with (2 ^ 24) in Hlt. split.
  - assert (E: Z.land (Z.shiftr h 1) 3 = Z.shiftr h 1 mod 4)
      by (change 3 with (Z.ones 2); rewrite Z.land_ones; [reflexivity | lia]).
    rewrite E. pose proof (Z.mod_pos_bound (Z.shiftr h 1) 4 ltac:(lia)). lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. change (2 ^ 21) with 2097152.
    change (2 ^ 24) with 16777216 in Hlt. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia.
Qed.

Lemma zf_cblock_bound (s: list Z) (c: Z) : bytes_ok s -> cblock_size s = Some c -> 0 <= c < 2 ^ 21.
Proof.
  intros Hb. unfold cblock_size. pose proof (zf_bp_bounds s Hb) as (_ & Ho).
  destruct (Zlength s <? ZSTD_blockHeaderSize); [discriminate|].
  destruct (bp_type (block_props_of s) =? 1); [intros H; inversion H; lia|].
  destruct (bp_type (block_props_of s) =? 3); [discriminate|].
  intros H; inversion H; subst; exact Ho.
Qed.

(* ZSTD_getFrameHeader on bytes: the content size and Block_Maximum_Size are never negative, and a frame (not a
   skippable one) with content has blocks of positive maximal size *)
Lemma zf_gfh_bounds (s: list Z) (h: frame_header) :
  bytes_ok s -> get_frame_header s = FH_ok h ->
  0 <= fh_contentSize h /\ 0 <= fh_blockSizeMax h /\
  (is_skippable_magic (le_field s 0 4) = false -> 0 < fh_contentSize h -> 0 < fh_blockSizeMax h).
Proof.
  intros Hb. unfold get_frame_header. cbv zeta.
  destruct (Zlength s <? 5).
  { destruct (Zlength s >? 0); [destruct (_ && _)|]; discriminate. }
  destruct (negb (le_field s 0 4 =? ZSTD_MAGICNUMBER)).
  { destruct (is_skippable_magic (le_field s 0 4)) eqn:Es; [|discriminate].
    destruct (Zlength s <? ZSTD_SKIPPABLEHEADERSIZE); [discriminate|].
    intros H; inversion H; subst; cbn [fh_contentSize fh_blockSizeMax]. split; [apply zf_le_field_nonneg, Hb|]. split; [lia|].
    intros E; discriminate. }
  destruct (Zlength s <? fhd_header_size (byte_at s 4)); [discriminate|].
  destruct (negb (Z.land (byte_at s 4) 8 =? 0)); [discriminate|].
  destruct (_ && _); [discriminate|].
  intros H; inversion H; subst; clear H; cbn [fh_contentSize fh_blockSizeMax].
  set (fcs := if Z.shiftr (byte_at s 4) 6 =? 0 then _ else _).
  assert (Hf: 0 <= fcs).
  { subst fcs.
    repeat match goal with |- context [if ?c then _ else _] => destruct c end;
    first [ unfold ZSTD_CONTENTSIZE_UNKNOWN; lia
          | match goal with |- 0 <= byte_at ?l ?i => pose proof (zf_byte_at l i Hb); unfold is_byte in *; lia end
          | match goal with |- 0 <= le_field ?l ?i ?k + _ => pose proof (zf_le_field_nonneg l i k Hb); lia end
          | apply zf_le_field_nonneg, Hb ]. }
  assert (Hw: 0 <= Z.shiftr (byte_at s 5) 3) by (apply Z.shiftr_nonneg; pose proof (zf_byte_at s 5 Hb); unfold is_byte in *; lia).
  assert (Hl: 0 <= Z.land (byte_at s 5) 7) by (apply Z.land_nonneg; right; lia).
  assert (Hp: 2 ^ 10 <= 2 ^ (Z.shiftr (byte_at s 5) 3 + ZSTD_WINDOWLOG_ABSOLUTEMIN))
    by (apply Z.pow_le_mono_r; unfold ZSTD_WINDOWLOG_ABSOLUTEMIN; lia).
  assert (Hq: 0 <= Z.shiftr (2 ^ (Z.shiftr (byte_at s 5) 3 + ZSTD_WINDOWLOG_ABSOLUTEMIN)) 3)
    by (apply Z.shiftr_nonneg; lia).
  assert (Hr: 0 <= Z.shiftr (2 ^ (Z.shiftr (byte_at s 5) 3 + ZSTD_WINDOWLOG_ABSOLUTEMIN)) 3 * Z.land (byte_at s 5) 7)
    by (apply Z.mul_nonneg_nonneg; lia).
  unfold ZSTD_BLOCKSIZE_MAX. split; [exact Hf|].
  destruct (Z.land (Z.shiftr (byte_at s 4) 5) 1 =? 1); split; try lia; intros _ _; lia.
Qed.

(* ZSTD_getFrameHeader: Block_Maximum_Size is at most ZSTD_BLOCKSIZE_MAX (0 for a skippable frame) *)
Lemma zf_gfh_bsm (s: list Z) (h: frame_header) :
  get_frame_header s = FH_ok h -> fh_blockSizeMax h <= ZSTD_BLOCKSIZE_MAX.
Proof.
  unfold get_frame_header. cbv zeta.
  destruct (Zlength s <? 5).
  { destruct (Zlength s >? 0); [destruct (_ && _)|]; discriminate. }
  destruct (negb (le_field s 0 4 =? ZSTD_MAGICNUMBER)).
  { destruct (is_skippable_magic (le_field s 0 4)); [|discriminate].
    destruct (Zlength s <? ZSTD_SKIPPABLEHEADERSIZE); [discriminate|].
    intros H; inversion H; subst; cbn [fh_blockSizeMax]. unfold ZSTD_BLOCKSIZE_MAX; lia. }
  destruct (Zlength s <? fhd_header_size (byte_at s 4)); [discriminate|].
  destruct (negb (Z.land (byte_at s 4) 8 =? 0)); [discriminate|].
  destruct (_ && _); [discriminate|].
  intros H; inversion H; subst; clear H; cbn [fh_blockSizeMax]. lia.
Qed.

Section Facts.
Variable xst : Type.
Variable xst_init : xst.
Variable xst_begin : xst -> xst.
Variable x_block : xst -> list Z -> Z -> Z -> Z -> Z -> list Z -> Z -> Z -> bool -> option (xst * list Z * Z).
Variable x_frame1 : xst -> list Z -> Z -> option (list Z * Z * xst).

Local Notation zstate := (zstate xst).
Local Notation lstep := (lstep xst).
Local Notation zstep := (zstep xst xst_begin x_block x_frame1).
Local Notation zs_run_from := (zs_run_from xst xst_begin x_block x_frame1).
Local Notation zs_run := (zs_run xst xst_init xst_begin x_block x_frame1).
Local Notation zs_call := (zs_call xst xst_init xst_begin x_block x_frame1).
Local Notation one_iter := (one_iter xst xst_begin x_block x_frame1).
Local Notation z_loop := (z_loop xst xst_begin x_block x_frame1).
Local Notation st_load_header := (st_load_header xst xst_begin x_block x_frame1).
Local Notation st_header_done := (st_header_done xst xst_begin x_block x_frame1).
Local Notation st_read := (st_read xst x_block).
Local Notation st_load := (st_load xst x_block).
Local Notation st_flush := (st_flush xst).
Local Notation z_dcs := (z_dcs xst x_block).
Local Notation d_continue := (d_continue xst x_block).

(* ---------- the history ---------- *)

Lemma zs_run_nil : zs_run nil = Some (zstate_init xst xst_init).
Proof. reflexivity. Qed.

Lemma zs_run_from_app (z: zstate) (h1 h2: list zcall) :
  zs_run_from z (h1 ++ h2) =
  match zs_run_from z h1 with Some z1 => zs_run_from z1 h2 | None => None end.
Proof.
  revert z. induction h1 as [|c h1 IH]; intros z; simpl; [reflexivity|].
  destruct (zstep z c) as [[z' o]|]; [apply IH | reflexivity].
Qed.

(* the run after one more call *)
Lemma zs_run_snoc (h: list zcall) (c: zcall) :
  zs_run (h ++ [c]) = match zs_run h with Some z => option_map fst (zstep z c) | None => None end.
Proof.
  unfold ExStream.zs_run. rewrite zs_run_from_app.
  destruct (zs_run_from _ h) as [z|]; [|reflexivity]. simpl.
  destruct (zstep z c) as [[z' o]|]; reflexivity.
Qed.

(* a call's outcome from the state its history reached: the outcome and the next run *)
Lemma zs_call_step (h: list zcall) (c: zcall) (z z': zstate) o :
  zs_run h = Some z -> zstep z c = Some (z', o) -> zs_call h c = Some o /\ zs_run (h ++ [c]) = Some z'.
Proof.
  intros Hr Hs. unfold ExStream.zs_call. rewrite zs_run_snoc, Hr, Hs. split; reflexivity.
Qed.

Lemma zs_call_step_none (h: list zcall) (c: zcall) (z: zstate) :
  zs_run h = Some z -> zstep z c = None -> zs_call h c = None.
Proof. intros Hr Hs. unfold ExStream.zs_call. rewrite Hr, Hs. reflexivity. Qed.

(* conversely, a call with an outcome comes from a run *)
Lemma zs_call_some (h: list zcall) (c: zcall) o :
  zs_call h c = Some o -> exists z z', zs_run h = Some z /\ zstep z c = Some (z', o) /\ zs_run (h ++ [c]) = Some z'.
Proof.
  unfold ExStream.zs_call. intros H. destruct (zs_run h) as [z|] eqn:Hr; [|discriminate].
  destruct (zstep z c) as [[z' o']|] eqn:Hs; [|discriminate]. simpl in H. injection H as <-.
  exists z, z'. split; [reflexivity|]. split; [exact Hs|].
  rewrite zs_run_snoc, Hr, Hs. reflexivity.
Qed.

(* ---------- one call: the loop, then the epilogue ---------- *)

(* the code after the loop (2404-2448): noForwardProgress, the hostage byte and the hint, from the loop's
   outcome *)
Definition z_epi (inp: list Z) (room: Z) (res: lstep) : option (zstate * (Z * Z * list Z * Z * Z)) :=
  match res with
  | LErr _ => None
  | LNext _ _ _ _ => None
  | LEarly _ z1 r => Some (z1, (r, Zlength inp, nil, zs_nfp xst z1, 0))
  | LStop _ z1 ip dl =>
      let noprog := (ip =? 0) && (Zlength dl =? 0) in
      let nfp := if noprog then zs_nfp xst z1 + 1 else 0 in
      if noprog && (nfp >=? ZS_NO_FORWARD_PROGRESS_MAX) && ((room =? 0) || (Zlength inp =? 0)) then None else
      let z2 := z_nfp xst z1 nfp in
      if d_expected xst (zs_dc xst z2) =? 0 then
        if zs_oend xst z2 =? zs_ostart xst z2 then
          if zs_host xst z2 =? 1 then
            if ip >=? Zlength inp then Some (z_stage xst z2 ZDSS_read, (1, ip, dl, nfp, 1))
            else Some (z2, (0, ip + 1, dl, nfp, 0))
          else Some (z2, (0, ip, dl, nfp, 0))
        else if zs_host xst z2 =? 0 then Some (z_host xst z2 1, (1, ip - 1, dl, nfp, 1))
        else Some (z2, (1, ip, dl, nfp, 1))
      else
        let d := zs_dc xst z2 in
        Some (z2, (d_expected xst d + (if d_stage xst d =? DS_decompressBlock then ZSTD_blockHeaderSize else 0)
                     - zs_inpos xst z2, ip, dl, nfp, zs_host xst z2))
  end.

(* the fuel zstep gives the loop *)
Definition zfuel (inp: list Z) : nat := (2 * length inp + 4)%nat.

Lemma zstep_unfold (z: zstate) (inp: list Z) (room: Z) :
  zstep z (inp, room) =
  if room <? 0 then None else z_epi inp room (z_loop (zfuel inp) inp room z 0 nil).
Proof. reflexivity. Qed.

Lemma z_loop_S (f: nat) (inp: list Z) (room: Z) (z: zstate) (ip: Z) (dl: list Z) :
  z_loop (S f) inp room z ip dl =
  match one_iter inp room z ip dl with
  | LNext _ z1 ip1 dl1 => z_loop f inp room z1 ip1 dl1
  | r => r
  end.
Proof. reflexivity. Qed.

(* one_iter is the case of the stream stage (with the fall-through of the C switch inside st_header_done,
   st_read) *)
Lemma one_iter_init inp room z ip dl :
  zs_stage xst z = ZDSS_init -> one_iter inp room z ip dl = st_load_header inp room (z_new_frame xst z) ip dl.
Proof. intros E. unfold ExStream.one_iter. rewrite E. reflexivity. Qed.

Lemma one_iter_lh inp room z ip dl :
  zs_stage xst z = ZDSS_loadHeader -> one_iter inp room z ip dl = st_load_header inp room z ip dl.
Proof. intros E. unfold ExStream.one_iter. rewrite E. reflexivity. Qed.

Lemma one_iter_read inp room z ip dl :
  zs_stage xst z = ZDSS_read -> one_iter inp room z ip dl = st_read inp z ip dl.
Proof. intros E. unfold ExStream.one_iter. rewrite E. reflexivity. Qed.

Lemma one_iter_load inp room z ip dl :
  zs_stage xst z = ZDSS_load -> one_iter inp room z ip dl = st_load inp z ip dl.
Proof. intros E. unfold ExStream.one_iter. rewrite E. reflexivity. Qed.

Lemma one_iter_flush inp room z ip dl :
  zs_stage xst z = ZDSS_flush -> one_iter inp room z ip dl = st_flush room z ip dl.
Proof. intros E. unfold ExStream.one_iter. rewrite E. reflexivity. Qed.

Lemma one_iter_other inp room z ip dl :
  ~ (0 <= zs_stage xst z <= 4) -> one_iter inp room z ip dl = LErr xst.
Proof.
  intros E. unfold ExStream.one_iter, ZDSS_init, ZDSS_loadHeader, ZDSS_read, ZDSS_load, ZDSS_flush.
  repeat match goal with |- context [?a =? ?b] => destruct (Z.eqb_spec a b); [lia|] end. reflexivity.
Qed.

(* ---------- the states the calls reach ---------- *)

(* What the invariant needs of the block decoder: a property `xgood` of its state (for model/Exact.v's instance:
   litExtraBuffer holds bytes and the Huffman table's cells are in range) that the new context has,
   ZSTD_decompressBegin and the one-shot frame keep, and that a compressed block decoded in streaming mode into a
   region with its capacity after op keeps, together with the region's bytes and length; the block's size is at
   most its capacity. *)
Variable xgood : xst -> Prop.
Hypothesis xgood_init : xgood xst_init.
Hypothesis xgood_begin : forall e, xgood e -> xgood (xst_begin e).
Hypothesis xgood_frame1 : forall e s cap c k e',
  xgood e -> bytes_ok s -> x_frame1 e s cap = Some (c, k, e') -> xgood e'.
Hypothesis xgood_block : forall e mem ps op ds de body bsm cap e' mem' n,
  xgood e -> bytes_ok mem -> bytes_ok body -> 0 <= op -> 0 <= cap -> op + cap <= Zlength mem ->
  x_block e mem ps op ds de body bsm cap true = Some (e', mem', n) ->
  xgood e' /\ bytes_ok mem' /\ Zlength mem' = Zlength mem /\ 0 <= n <= cap.

Local Notation dstate := (dstate xst).

(* inside a frame's blocks (decodeBlockHeader .. checkChecksum): ZSTD_decompressBegin has reset the ring offsets
   and fParams is this frame's header *)
Definition zin (d: dstate) : Prop := DS_decodeBlockHeader <= d_stage xst d <= DS_checkChecksum.

(* ZSTD_decompressContinue's state: stage, block type, expected and rleSize in range (expected is positive inside
   a frame's blocks), the block decoder's state good *)
Definition zi_dc (d: dstate) : Prop :=
  0 <= d_stage xst d <= DS_skipFrame /\ 0 <= d_btype xst d <= 3 /\
  0 <= d_expected xst d < 2 ^ 32 /\ 0 <= d_rle xst d < 2 ^ 32 /\
  (zin d -> 0 < d_expected xst d) /\ xgood (d_ent xst d).

(* the ring offsets previousDstEnd, prefixStart and the extDict's bounds are within a ring of n cells *)
Definition zi_off (d: dstate) (n: Z) : Prop :=
  forall x, d_prev xst d = Some x \/ d_pfx xst d = Some x \/ d_ds xst d = Some x \/ d_de xst d = Some x ->
  0 <= x <= n.

(* the ring: outStart <= outEnd <= outBuffSize, outBuffSize cells, all bytes *)
Definition zi_ring (z: zstate) : Prop :=
  0 <= zs_ostart xst z <= zs_oend xst z /\ zs_oend xst z <= zs_outbs xst z /\
  bytes_ok (zs_mem xst z) /\ Zlength (zs_mem xst z) = zs_outbs xst z /\ zi_off (zs_dc xst z) (zs_outbs xst z).

(* the stream's buffers and stage: inPos is below `expected` in zdss_load (inBuff then holds the inPos bytes
   loaded, except for a skippable frame's content, which is only counted), 0 with an empty inBuff otherwise; the
   header buffer holds bytes; zdss_init and zdss_loadHeader are between frames (expected 0), zdss_loadHeader
   with an empty ring; fParams' content size and Block_Maximum_Size are not negative *)
Definition zi_buf (z: zstate) : Prop :=
  let s := zs_stage xst z in
  let d := zs_dc xst z in
  (s = ZDSS_load -> 0 <= zs_inpos xst z < d_expected xst d) /\
  (s <> ZDSS_load -> zs_inpos xst z = 0 /\ zs_ibuf xst z = nil) /\
  (s = ZDSS_load -> d_stage xst d <> DS_skipFrame -> Zlength (zs_ibuf xst z) = zs_inpos xst z) /\
  bytes_ok (zs_hbuf xst z) /\ bytes_ok (zs_ibuf xst z) /\
  (s = ZDSS_init \/ s = ZDSS_loadHeader -> d_expected xst d = 0) /\
  (s = ZDSS_loadHeader -> zs_ostart xst z = 0 /\ zs_oend xst z = 0) /\
  0 <= fh_contentSize (zs_fp xst z) /\ 0 <= fh_blockSizeMax (zs_fp xst z).

(* Inside a frame's blocks, the ring and the extDict.  An extDict exists only after the ring restarted (zdss_flush:
   only when outBuffSize < frameContentSize), and the ring has room then.  In zdss_read / zdss_load,
   previousDstEnd is NULL, outStart, or the ring restarted at outStart = 0; in zdss_flush it is outEnd (the block
   just decoded ends there).  So a compressed block that meets an extDict has room: outStart < outBuffSize. *)
Definition zi_ext (z: zstate) : Prop :=
  let s := zs_stage xst z in
  let d := zs_dc xst z in
  let fcs := fh_contentSize (zs_fp xst z) in
  let ob := zs_outbs xst z in
  zin d ->
  (0 < fcs -> 0 < fh_blockSizeMax (zs_fp xst z)) /\
  (d_de xst d <> None -> ob < fcs /\ 0 < ob) /\
  (s = ZDSS_read \/ s = ZDSS_load ->
     (d_prev xst d = None \/ d_prev xst d = Some (zs_ostart xst z) \/ (zs_ostart xst z = 0 /\ ob < fcs)) /\
     (d_de xst d <> None -> zs_ostart xst z < ob)) /\
  (s = ZDSS_flush -> d_prev xst d = Some (zs_oend xst z)).

(* oversizedDuration (ZSTD_DCtx_updateOversizedDuration, 2061-2072): never negative; the buffers' sizes inBuffSize +
   outBuffSize are 0 or a frame's needs, below 2^29; from ZSTD_WORKSPACETOOLARGE_MAXDURATION (128) on, the buffers
   were reallocated to a frame's needs (at least 4 bytes) at every frame counted beyond 128, each needing 3 times
   less than the buffers before, so (inBuffSize + outBuffSize) * 3 ^ (oversizedDuration - 128) <= 2^32.  It keeps
   oversizedDuration far below its size_t range (model/ExStreamOver.v). *)
Definition zi_over (z: zstate) : Prop :=
  zs_inbs xst z + zs_outbs xst z <= 2 ^ 29 /\ 0 <= zs_over xst z /\
  (ZS_WORKSPACETOOLARGE_MAXDURATION <= zs_over xst z ->
     4 <= zs_inbs xst z + zs_outbs xst z /\
     (zs_inbs xst z + zs_outbs xst z) * 3 ^ (zs_over xst z - ZS_WORKSPACETOOLARGE_MAXDURATION) <= 2 ^ 32).

(* The states the calls reach.  The fuel argument needs zi_buf's first part (`expected` is never negative; inPos
   is 0 outside zdss_load and below `expected` in it; the buffers hold bytes); the rest are the bounds the proof
   of ZSTD_decompressStream reads (model/ExStreamBnd.v, model/ExStreamOver.v). *)
Definition zinv (z: zstate) : Prop := zi_dc (zs_dc xst z) /\ zi_ring z /\ zi_buf z /\ zi_ext z /\ zi_over z.

(* the potential of the loop at input position ip: an iteration that goes on lowers it *)
Definition zpot (inp: list Z) (z: zstate) (ip: Z) : Z :=
  2 * (Zlength inp - ip) + (if zs_stage xst z =? ZDSS_flush then 2 else 1).

Lemma zi_dc_not_in (d: dstate) : zi_dc d -> d_expected xst d = 0 -> ~ zin d.
Proof. intros (_ & _ & _ & _ & H & _) E Hi. specialize (H Hi). lia. Qed.

Lemma zinv_init : zinv (zstate_init xst xst_init).
Proof.
  unfold zinv, zi_dc, zi_ring, zi_buf, zi_ext, zi_over, zi_off, zin, zstate_init; cbn.
  unfold ZDSS_load, ZDSS_init, ZDSS_loadHeader, DS_getFrameHeaderSize, DS_skipFrame, DS_decodeBlockHeader,
    DS_checkChecksum, ZS_WORKSPACETOOLARGE_MAXDURATION.
  split; [repeat split; try lia; exact xgood_init|].
  repeat match goal with |- _ /\ _ => split | |- _ -> _ => intro | |- forall _, _ => intro
                       | H: _ \/ _ |- _ => destruct H | H: None = Some _ |- _ => discriminate end;
    try lia; try constructor; try discriminate.
Qed.

(* ZSTD_checkContinuity: either nothing changes (and then the write is contiguous when there is room), or a new
   segment starts at dst with room, the old previousDstEnd (not dst) becoming dictEnd *)
Lemma d_continuity_facts (d: dstate) (dst cap: Z) :
  let dc := d_continuity xst d dst cap in
  d_stage xst dc = d_stage xst d /\ d_expected xst dc = d_expected xst d /\ d_btype xst dc = d_btype xst d /\
  d_rle xst dc = d_rle xst d /\ d_ent xst dc = d_ent xst d /\
  ((d_prev xst dc = d_prev xst d /\ d_pfx xst dc = d_pfx xst d /\ d_ds xst dc = d_ds xst d /\
    d_de xst dc = d_de xst d /\ (0 < cap -> d_prev xst d = Some dst)) \/
   (0 < cap /\ d_prev xst dc = Some dst /\ d_pfx xst dc = Some dst /\ d_de xst dc = d_prev xst d /\
    d_prev xst d <> Some dst /\ (d_ds xst dc = None \/ d_ds xst dc = d_pfx xst d))).
Proof.
  cbv zeta. unfold d_continuity.
  destruct (d_prev xst d) as [p|] eqn:Ep.
  - destruct (Z.eqb_spec p dst) as [->|Hne].
    + change (negb true) with false. rewrite Bool.andb_false_r. repeat split; auto. left. repeat split; auto.
    + destruct (Z.gtb_spec cap 0); cbn.
      * repeat split; auto. right. repeat split; auto; try lia; congruence.
      * repeat split; auto. left. repeat split; auto. lia.
  - destruct (Z.gtb_spec cap 0); cbn.
    + repeat split; auto. right. repeat split; auto; congruence.
    + repeat split; auto. left. repeat split; auto. lia.
Qed.

Lemma zf_mem_write_len (mem b: list Z) (pos: Z) :
  0 <= pos -> pos + Zlength b <= Zlength mem -> Zlength (mem_write mem pos b) = Zlength mem.
Proof.
  intros Hp Hl. unfold mem_write. rewrite !Zlength_correct in *. rewrite !app_length, firstn_length, skipn_length.
  lia.
Qed.

Lemma zf_mem_write_bytes (mem b: list Z) (pos: Z) :
  bytes_ok mem -> bytes_ok b -> bytes_ok (mem_write mem pos b).
Proof.
  intros Hm Hb. unfold mem_write. apply zf_bytes_app; [apply zf_forall_firstn, Hm|].
  apply zf_bytes_app; [exact Hb | apply zf_forall_skipn, Hm].
Qed.

Ltac zd_simpl :=
  unfold d_goto, d_set_check, d_begin, d_after_shortcut, d_end_frame in *;
  cbn [d_stage d_expected d_btype d_rle d_out d_check d_ent d_prev d_pfx d_ds d_de] in *.

Ltac zd_consts :=
  unfold ZSTD_blockHeaderSize, DS_getFrameHeaderSize, DS_decodeFrameHeader, DS_decodeBlockHeader,
    DS_decompressBlock, DS_decompressLastBlock, DS_checkChecksum, DS_decodeSkippableHeader, DS_skipFrame,
    BT_reserved, ZSTD_FRAMEHEADERSIZE_PREFIX, ZDSS_init, ZDSS_loadHeader, ZDSS_read, ZDSS_load, ZDSS_flush in *.

Ltac zd_fin :=
  unfold zin, zi_dc in *; zd_simpl; zd_consts;
  repeat match goal with |- _ /\ _ => split | |- _ -> _ => intro | |- ~ _ => intro end;
  unfold zin in *; zd_simpl; zd_consts;
  try solve [ lia | reflexivity | assumption | congruence | f_equal; lia
            | match goal with H: d_ent _ _ = d_ent _ _ |- _ => rewrite H; assumption end
            | left; reflexivity | right; reflexivity | right; f_equal; lia ].

(* ZSTD_decompressContinue from a state in range, on bytes, into a region with its capacity after dst: the state
   after it is in range, the region keeps its bytes and length, at most the capacity is written; a state inside a
   frame's blocks comes from one; a skippable frame's content writes nothing and ends the frame; the offsets are
   those of ZSTD_checkContinuity, previousDstEnd possibly moved to the end of what was written *)
Lemma d_continue_bnd fp (d: dstate) mem dst cap src n d' mem' r :
  zi_dc d -> bytes_ok mem -> bytes_ok src -> Zlength src <= n -> 0 <= dst -> 0 <= cap -> dst + cap <= Zlength mem ->
  d_continue fp d mem dst cap src n = Some (d', mem', r) ->
  zi_dc d' /\ bytes_ok mem' /\ Zlength mem' = Zlength mem /\ 0 <= r <= cap /\
  (zin d' -> zin d) /\ (d_stage xst d = DS_skipFrame -> r = 0 /\ ~ zin d') /\
  d_pfx xst d' = d_pfx xst (d_continuity xst d dst cap) /\ d_ds xst d' = d_ds xst (d_continuity xst d dst cap) /\
  d_de xst d' = d_de xst (d_continuity xst d dst cap) /\
  (d_prev xst d' = d_prev xst (d_continuity xst d dst cap) \/ d_prev xst d' = Some (dst + r)) /\
  (0 < r -> d_prev xst d' = Some (dst + r)).
Proof.
  intros Hd Hm Hs Hn Hdst Hcap Hlen. unfold ExStream.d_continue.
  destruct (Z.eqb_spec n (d_next_in xst d n)) as [Esan|]; [|discriminate]. cbn [negb].
  pose proof (d_continuity_facts d dst cap) as Hc. cbv zeta in Hc.
  set (dc := d_continuity xst d dst cap) in *. clearbody dc.
  destruct Hc as (Cs & Ce & Cb & Cr & Cent & _).
  destruct Hd as (Hst & Hbt & Hex & Hrl & Hzin & Hg).
  unfold zin in *.
  unfold DS_skipFrame, DS_decodeBlockHeader, DS_decompressBlock, DS_decompressLastBlock, DS_checkChecksum in *.
  pose proof (zf_bp_bounds _ Hs) as (Hbt' & Hos).
  set (bp := block_props_of src) in *. clearbody bp.
  destruct (Z.eqb_spec (d_stage xst dc) 2) as [E2|E2].
  { destruct (cblock_size src) as [c|] eqn:Ec; [|discriminate].
    pose proof (zf_cblock_bound _ _ Hs Ec) as Hcb.
    destruct (c >? fh_blockSizeMax fp); [discriminate|].
    destruct (Z.gtb_spec c 0) as [Hc0|Hc0].
    - destruct (bp_last bp =? 1); intros H; injection H as <- <- <-; zd_fin.
    - destruct (bp_last bp =? 1).
      + unfold d_end_frame. destruct (_ && _); [discriminate|].
        destruct (fh_checksumFlag fp =? 1); intros H; injection H as <- <- <-; zd_fin.
      + intros H; injection H as <- <- <-; zd_fin. }
  destruct ((d_stage xst dc =? 3) || (d_stage xst dc =? 4)) eqn:E34.
  { assert (Hin: 2 <= d_stage xst d <= 5)
      by (apply Bool.orb_true_iff in E34; destruct E34 as [E|E]; apply Z.eqb_eq in E; lia).

    match goal with |- match ?res with _ => _ end = _ -> _ =>
      destruct res as [[[[e mem1] sz] ex]|] eqn:Er; [|discriminate] end.
    assert (Hres: xgood e /\ bytes_ok mem1 /\ Zlength mem1 = Zlength mem /\ 0 <= sz <= cap /\ ex < d_expected xst d).
    { revert Er. specialize (Hzin Hin).
      destruct (d_btype xst dc =? 2).
      - destruct (d_hist xst dc dst) as [[ps ds] de].
        destruct (x_block (d_ent xst dc) mem ps dst ds de src (fh_blockSizeMax fp) cap true)
          as [[[e1 m1] s1]|] eqn:Ex; [|discriminate].
        intros H; injection H as <- <- <- <-.
        rewrite Cent in Ex. destruct (xgood_block _ _ _ _ _ _ _ _ _ _ _ _ Hg Hm Hs Hdst Hcap Hlen Ex) as (? & ? & ? & ?).
        repeat split; auto; lia.
      - destruct (d_btype xst dc =? 0) eqn:Eb0.
        + destruct (Z.gtb_spec n cap) as [?|Hnc]; [discriminate|]. intros H; injection H as <- <- <- <-.
          assert (Hn1: 1 <= n <= d_expected xst d).
          { unfold d_next_in, DS_decompressBlock, DS_decompressLastBlock in Esan.
            rewrite <- Cs, <- Cb, <- Ce, E34, Eb0 in Esan; cbn in Esan. lia. }
          rewrite Cent. split; [auto|]. split; [apply zf_mem_write_bytes; auto|].
          split; [apply zf_mem_write_len; lia|]. lia.
        + destruct (d_btype xst dc =? 1); [|discriminate].
          destruct (Z.gtb_spec (d_rle xst dc) cap) as [?|Hrc]; [discriminate|]. intros H; injection H as <- <- <- <-.
          rewrite Cent. split; [auto|]. split.
          { apply zf_mem_write_bytes; auto. unfold bytes_ok. apply Forall_forall. intros x Hx.
            apply repeat_spec in Hx. subst x. apply zf_byte_at, Hs. }
          split; [apply zf_mem_write_len; [lia|]; rewrite Zlength_correct, repeat_length; lia|]. lia. }
    destruct Hres as (R1 & R2 & R3 & R4 & R5).
    destruct (sz >? fh_blockSizeMax fp); [discriminate|].
    destruct (Z.gtb_spec ex 0) as [Hx|Hx].
    - intros H; injection H as <- <- <-; zd_fin.
    - destruct (d_stage xst dc =? 4).
      + unfold d_end_frame. destruct (_ && _); [discriminate|].
        destruct (fh_checksumFlag fp =? 1); intros H; injection H as <- <- <-; zd_fin.
      + intros H; injection H as <- <- <-; zd_fin. }
  destruct (Z.eqb_spec (d_stage xst dc) 5) as [E5|E5].
  { destruct (_ && _); [discriminate|]. intros H; injection H as <- <- <-; zd_fin. }
  destruct (Z.eqb_spec (d_stage xst dc) 7) as [E7|E7]; [|discriminate].
  intros H; injection H as <- <- <-; zd_fin.
Qed.

(* lia without the invariant's hypotheses (they slow it down and it never needs them whole) *)
Ltac zclear :=
  repeat match goal with
  | H: zinv _ |- _ => clear H | H: zi_dc _ |- _ => clear H | H: zi_ring _ |- _ => clear H
  | H: zi_buf _ |- _ => clear H | H: zi_ext _ |- _ => clear H | H: zi_off _ _ |- _ => clear H
  | H: zi_over _ |- _ => clear H
  | H: ?A -> ?B |- _ => lazymatch B with False => fail | _ => clear H end
  end.
Ltac zlia := zclear; zd_consts; lia.

Lemma zi_off_cont (d: dstate) (n dst cap: Z) :
  zi_off d n -> 0 <= dst <= n -> zi_off (d_continuity xst d dst cap) n.
Proof.
  intros H Hd x Hx. pose proof (d_continuity_facts d dst cap) as F. cbv zeta in F.
  destruct F as (_ & _ & _ & _ & _ & [(P1 & P2 & P3 & P4 & _) | (_ & P1 & P2 & P4 & _ & P3)]).
  - rewrite P1, P2, P3, P4 in Hx. apply H, Hx.
  - destruct Hx as [Hx|[Hx|[Hx|Hx]]].
    + rewrite P1 in Hx. injection Hx as <-. zlia.
    + rewrite P2 in Hx. injection Hx as <-. zlia.
    + destruct P3 as [P3|P3]; rewrite P3 in Hx; [discriminate|]. apply H. right. left. exact Hx.
    + rewrite P4 in Hx. apply H. left. exact Hx.
Qed.

Lemma zf_Zlength_app (l1 l2: list Z) : Zlength (l1 ++ l2) = Zlength l1 + Zlength l2.
Proof. rewrite !Zlength_correct, app_length. zlia. Qed.

(* the fields of a stream state built by the update functions, in the goal *)
(* (lazily: unfolding the nested updates first would copy the inner state into every field) *)
Ltac zs_simpl :=
  cbn [zs_stage zs_hbuf zs_fp zs_ibuf zs_inpos zs_inbs zs_outbs zs_over zs_mem zs_ostart zs_oend zs_nfp zs_host
       zs_dc z_new_frame z_stage z_hbuf z_fp z_in z_bufs z_mem z_ring z_nfp z_host z_dc].

Ltac zd_simplg :=
  unfold d_goto, d_set_check, d_begin, d_after_shortcut, d_end_frame;
  cbn [d_stage d_expected d_btype d_rle d_out d_check d_ent d_prev d_pfx d_ds d_de].

Ltac zd_constsg :=
  unfold ZSTD_blockHeaderSize, DS_getFrameHeaderSize, DS_decodeFrameHeader, DS_decodeBlockHeader,
    DS_decompressBlock, DS_decompressLastBlock, DS_checkChecksum, DS_decodeSkippableHeader, DS_skipFrame,
    BT_reserved, ZSTD_FRAMEHEADERSIZE_PREFIX, ZDSS_init, ZDSS_loadHeader, ZDSS_read, ZDSS_load, ZDSS_flush.

(* ZSTD_decompressContinueStream from zdss_read or zdss_load (inBuff then already consumed): the invariant again,
   in zdss_read or zdss_flush *)
Lemma z_dcs_zinv z src n z' :
  zinv z -> (zs_stage xst z = ZDSS_read \/ zs_stage xst z = ZDSS_load) ->
  zs_inpos xst z = 0 -> zs_ibuf xst z = nil -> bytes_ok src -> Zlength src <= n ->
  z_dcs z src n = Some z' ->
  zinv z' /\ (zs_stage xst z' = ZDSS_read \/ zs_stage xst z' = ZDSS_flush) /\
  zs_inpos xst z' = 0 /\ zs_hbuf xst z' = zs_hbuf xst z /\ zs_ibuf xst z' = nil.
Proof.
  intros (Hd & Hr & Hb & He & Ho) Hs Hp Hi Hsrc Hn. unfold ExStream.z_dcs.
  destruct Hr as (Ho1 & Ho2 & Hmb & Hml & Hoff).
  set (skip := d_stage xst (zs_dc xst z) =? DS_skipFrame).
  set (cap := if skip then 0 else zs_outbs xst z - zs_ostart xst z).
  assert (Hcap: 0 <= cap /\ zs_ostart xst z + cap <= Zlength (zs_mem xst z)) by (subst cap; destruct skip; zlia).
  assert (Hcapv: skip = false -> cap = zs_outbs xst z - zs_ostart xst z) by (intros E; subst cap; rewrite E; reflexivity).
  destruct (d_continue (zs_fp xst z) (zs_dc xst z) (zs_mem xst z) (zs_ostart xst z) cap src n)
    as [[[d' mem'] r]|] eqn:Ed; [|discriminate].
  destruct (d_continue_bnd _ _ _ _ _ _ _ _ _ _ Hd Hmb Hsrc Hn (proj1 Ho1) (proj1 Hcap) (proj2 Hcap) Ed)
    as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11).
  pose proof (d_continuity_facts (zs_dc xst z) (zs_ostart xst z) cap) as F. cbv zeta in F.
  destruct F as (_ & _ & _ & _ & _ & F).
  set (dc := d_continuity xst (zs_dc xst z) (zs_ostart xst z) cap) in *.
  pose proof (zi_off_cont _ _ (zs_ostart xst z) cap Hoff ltac:(zlia)) as Hoff'. fold dc in Hoff'.
  assert (Hoff2: zi_off d' (zs_outbs xst z)).
  { intros x [Hx|Hx].
    - destruct D10 as [D10|D10]; rewrite D10 in Hx.
      + apply Hoff'. left. exact Hx.
      + injection Hx as <-. zlia.
    - apply Hoff'. right. rewrite <- D7, <- D8, <- D9. exact Hx. }
  assert (Hsk: zin d' -> zin (zs_dc xst z) /\ skip = false).
  { intros Hz. split; [apply D5, Hz|]. subst skip.
    destruct (Z.eqb_spec (d_stage xst (zs_dc xst z)) DS_skipFrame) as [E|E]; [|reflexivity].
    destruct (D6 E) as [_ C]. contradiction. }
  assert (HB: zin d' -> d_de xst d' <> None ->
              zs_outbs xst z < fh_contentSize (zs_fp xst z) /\ 0 < zs_outbs xst z).
  { intros Hz Hde. destruct (Hsk Hz) as [Hz0 Hs0]. destruct (He Hz0) as (E1 & E2 & E3 & E4).
    rewrite D9 in Hde. destruct F as [(_ & _ & _ & F4 & _) | (F1 & _ & _ & F4 & F5 & _)].
    - apply E2. rewrite <- F4. exact Hde.
    - rewrite F4 in Hde. destruct (proj1 (E3 Hs)) as [P|[P|P]]; [contradiction|contradiction|].
      split; [zlia|]. rewrite (Hcapv Hs0) in F1. zlia. }
  assert (HX: zin d' -> d_de xst d' <> None -> zs_ostart xst z < zs_outbs xst z).
  { intros Hz Hde. destruct (Hsk Hz) as [Hz0 Hs0]. destruct (He Hz0) as (E1 & E2 & E3 & E4).
    rewrite D9 in Hde. destruct F as [(_ & _ & _ & F4 & _) | (F1 & _)].
    - apply (proj2 (E3 Hs)). rewrite <- F4. exact Hde.
    - rewrite (Hcapv Hs0) in F1. zlia. }
  assert (HP: zin d' -> r = 0 ->
     d_prev xst d' = None \/ d_prev xst d' = Some (zs_ostart xst z) \/
     (zs_ostart xst z = 0 /\ zs_outbs xst z < fh_contentSize (zs_fp xst z))).
  { intros Hz Er. destruct (Hsk Hz) as [Hz0 Hs0]. destruct (He Hz0) as (E1 & E2 & E3 & E4).
    destruct D10 as [D10|D10]; [| right; left; rewrite D10, Er, Z.add_0_r; reflexivity].
    rewrite D10. destruct F as [(F1 & _) | (_ & F1 & _)].
    - rewrite F1. exact (proj1 (E3 Hs)).
    - right. left. exact F1. }
  intros H. destruct ((r =? 0) && negb skip) eqn:Eb; injection H as <-.
  - apply andb_prop in Eb. destruct Eb as [Er Es]. apply Z.eqb_eq in Er.
    unfold zinv, zi_ring, zi_buf, zi_ext; zs_simpl. split; [|split; [left; reflexivity|split; [exact Hp|split; [reflexivity|exact Hi]]]].
    destruct Hb as (Hl & Hn' & Hli & Hhb & Hib & Hih & Hlh & Hfc & Hbs).
    split; [exact D1|]. split; [split; [exact Ho1|split; [exact Ho2|split; [exact D2|split; [zlia|exact Hoff2]]]]|].
    split.
    + unfold zi_buf; zs_simpl. zd_constsg. split; [intros; zlia|]. split; [intros _; split; [exact Hp|exact Hi]|].
      split; [intros; zlia|]. split; [exact Hhb|]. split; [rewrite Hi; constructor|].
      split; [intros [E|E]; zlia|]. split; [intros; zlia|]. split; assumption.
    + split; [|exact Ho]. unfold zi_ext; zs_simpl. intros Hz. destruct (Hsk Hz) as [Hz0 Hs0]. destruct (He Hz0) as (E1 & E2 & E3 & E4).
      split; [exact E1|]. split; [apply HB, Hz|]. split; [|intros E; unfold ZDSS_read, ZDSS_flush in E; zlia].
      intros _. split; [apply HP; assumption | apply HX, Hz].
  - unfold zinv, zi_ring, zi_buf, zi_ext; zs_simpl. split; [|split; [right; reflexivity|split; [exact Hp|split; [reflexivity|exact Hi]]]].
    destruct Hb as (Hl & Hn' & Hli & Hhb & Hib & Hih & Hlh & Hfc & Hbs).
    split; [exact D1|].
    split; [split; [zlia|split; [zlia|split; [exact D2|split; [zlia|exact Hoff2]]]]|].
    split.
    + unfold zi_buf; zs_simpl. zd_constsg. split; [intros; zlia|]. split; [intros _; split; [exact Hp|exact Hi]|].
      split; [intros; zlia|]. split; [exact Hhb|]. split; [rewrite Hi; constructor|].
      split; [intros [E|E]; zlia|]. split; [intros; zlia|]. split; assumption.
    + split; [|exact Ho]. unfold zi_ext; zs_simpl. intros Hz. destruct (Hsk Hz) as [Hz0 Hs0]. destruct (He Hz0) as (E1 & E2 & E3 & E4).
      split; [exact E1|]. split; [apply HB, Hz|]. split; [intros [E|E]; unfold ZDSS_read, ZDSS_load, ZDSS_flush in E; zlia|].
      intros _. apply D11. rewrite Hs0 in Eb. cbn in Eb. rewrite Bool.andb_true_r in Eb. apply Z.eqb_neq in Eb. zlia.
Qed.

(* inBuff and inPos in zdss_load *)
Lemma zinv_in z ib k :
  zinv z -> zs_stage xst z = ZDSS_load -> 0 <= k < d_expected xst (zs_dc xst z) -> bytes_ok ib ->
  (d_stage xst (zs_dc xst z) <> DS_skipFrame -> Zlength ib = k) -> zinv (z_in xst z ib k).
Proof.
  intros (Hd & Hr & Hb & He & Ho) Hs Hk Hib Hl.
  destruct Hb as (Hl0 & Hn & Hli & Hhb & Hib0 & Hih & Hlh & Hfc & Hbs).
  split; [exact Hd|]. split; [exact Hr|]. split; [|exact (conj He Ho)].
  unfold zi_buf; zs_simpl. rewrite Hs. zd_constsg.
  split; [intros; exact Hk|]. split; [intros C; zlia|]. split; [intros _; exact Hl|].
  split; [exact Hhb|]. split; [exact Hib|]. split; [intros [C|C]; zlia|]. split; [intros C; zlia|].
  split; assumption.
Qed.

(* zdss_read to zdss_load (inBuff empty) *)
Lemma zinv_read_load z :
  zinv z -> zs_stage xst z = ZDSS_read -> 0 < d_expected xst (zs_dc xst z) -> zinv (z_stage xst z ZDSS_load).
Proof.
  intros (Hd & Hr & Hb & He & Ho) Hs Hk.
  destruct Hb as (Hl0 & Hn & Hli & Hhb & Hib0 & Hih & Hlh & Hfc & Hbs).
  assert (Hs': zs_stage xst z <> ZDSS_load) by (rewrite Hs; discriminate).
  destruct (Hn Hs') as [Hp Hi].
  split; [exact Hd|]. split; [exact Hr|]. split.
  - unfold zi_buf; zs_simpl. zd_constsg.
    split; [intros; zlia|]. split; [intros C; zlia|]. split; [intros _ _; rewrite Hi, Hp; reflexivity|].
    split; [exact Hhb|]. split; [exact Hib0|]. split; [intros [C|C]; zlia|]. split; [intros C; zlia|].
    split; assumption.
  - split; [|exact Ho]. unfold zi_ext; zs_simpl. intros Hz. destruct (He Hz) as (E1 & E2 & E3 & E4).
    split; [exact E1|]. split; [exact E2|]. split; [intros _; apply E3; left; exact Hs|].
    intros C; unfold ZDSS_load, ZDSS_flush in C; zlia.
Qed.

(* a new header byte string *)
Lemma zinv_hbuf z hb : zinv z -> bytes_ok hb -> zinv (z_hbuf xst z hb).
Proof.
  intros (Hd & Hr & Hb & He & Ho) Hh.
  destruct Hb as (Hl0 & Hn & Hli & Hhb & Hib0 & Hih & Hlh & Hfc & Hbs).
  split; [exact Hd|]. split; [exact Hr|]. split; [|exact (conj He Ho)].
  unfold zi_buf; zs_simpl. split; [exact Hl0|]. split; [exact Hn|]. split; [exact Hli|]. split; [exact Hh|].
  split; [exact Hib0|]. split; [exact Hih|]. split; [exact Hlh|]. split; assumption.
Qed.

(* zdss_init: a new frame (zdss_loadHeader, empty buffers and ring) *)
Lemma zinv_new_frame z : zinv z -> zs_stage xst z = ZDSS_init -> zinv (z_new_frame xst z).
Proof.
  intros (Hd & Hr & Hb & He & Ho) Hs.
  destruct Hb as (Hl0 & Hn & Hli & Hhb & Hib0 & Hih & Hlh & Hfc & Hbs).
  destruct Hr as (Ho1 & Ho2 & Hmb & Hml & Hoff).
  assert (He0: d_expected xst (zs_dc xst z) = 0) by (apply Hih; left; exact Hs).
  split; [exact Hd|]. split.
  - unfold zi_ring; zs_simpl. split; [zlia|]. split; [zlia|]. split; [exact Hmb|]. split; [exact Hml|]. exact Hoff.
  - split.
    + unfold zi_buf; zs_simpl. zd_constsg.
      split; [intros C; zlia|]. split; [intros _; split; reflexivity|]. split; [intros C; zlia|].
      split; [constructor|]. split; [constructor|]. split; [intros _; exact He0|].
      split; [intros _; split; reflexivity|]. split; assumption.
    + split; [|exact Ho]. unfold zi_ext; zs_simpl. intros Hz. exfalso. exact (zi_dc_not_in _ Hd He0 Hz).
Qed.

(* zdss_load *)
Lemma st_load_inv inp z ip dl :
  zinv z -> zs_stage xst z = ZDSS_load -> bytes_ok inp -> 0 <= ip <= Zlength inp ->
  match st_load inp z ip dl with
  | LErr _ => True
  | LNext _ z1 ip1 dl1 => zinv z1 /\ ip + 1 <= ip1 <= Zlength inp /\
                          (zs_stage xst z1 = ZDSS_read \/ zs_stage xst z1 = ZDSS_flush) /\ dl1 = dl
  | LStop _ z1 ip1 dl1 => zinv z1 /\ ip <= ip1 <= Zlength inp
  | LEarly _ _ _ => False
  end.
Proof.
  intros Hz Hs Hb Hip. pose proof Hz as (Hd & Hr & Hbf & He & Ho).
  destruct Hbf as (Hl & Hn & Hli & Hhb & Hib & Hih & Hlh & Hfc & Hbs). specialize (Hl Hs).
  unfold ExStream.st_load.
  destruct (negb _ && _); [exact I|].
  set (toLoad := d_expected xst (zs_dc xst z) - zs_inpos xst z).
  set (loaded := Z.min toLoad (Zlength inp - ip)).
  set (skip := d_stage xst (zs_dc xst z) =? DS_skipFrame).
  set (ib := if skip then zs_ibuf xst z else zs_ibuf xst z ++ slice inp ip loaded).
  assert (Hibb: bytes_ok ib).
  { subst ib. destruct skip; [exact Hib | apply zf_bytes_app; [exact Hib | apply zf_bytes_slice, Hb]]. }
  assert (Hld: 0 <= loaded <= Zlength inp - ip) by (subst loaded toLoad; zlia).
  assert (Hlen: d_stage xst (zs_dc xst z) <> DS_skipFrame -> Zlength ib = zs_inpos xst z + loaded).
  { intros E. subst ib skip. apply Z.eqb_neq in E. rewrite E, zf_Zlength_app, (Hli Hs (proj1 (Z.eqb_neq _ _) E)).
    rewrite zf_Zlength_slice by zlia. reflexivity. }
  assert (Hz1: zinv (z_in xst z ib (zs_inpos xst z + loaded)) \/ loaded = toLoad).
  { destruct (Z.eq_dec loaded toLoad) as [E|E]; [right; exact E|left].
    apply zinv_in; [exact Hz | exact Hs | subst loaded toLoad; zlia | exact Hibb | exact Hlen]. }
  destruct (loaded <? toLoad) eqn:Elt.
  - apply Z.ltb_lt in Elt. destruct Hz1 as [Hz1|Hz1]; [|zlia]. split; [exact Hz1|]. zlia.
  - apply Z.ltb_ge in Elt.
    assert (Eq: loaded = toLoad) by (subst loaded; zlia).
    assert (Hz2: zinv (z_in xst (z_in xst z ib (zs_inpos xst z + loaded)) nil 0)).
    { change (zinv (z_in xst z nil 0)). apply zinv_in; [exact Hz | exact Hs | zlia | constructor | intros _; reflexivity]. }
    destruct (z_dcs _ (if skip then nil else ib) _) as [z2|] eqn:Hd2; [|exact I].
    apply z_dcs_zinv in Hd2; [| exact Hz2 | right; exact Hs | reflexivity | reflexivity
                            | destruct skip; [constructor | exact Hibb] |].
    + destruct Hd2 as (Hz3 & Hs3 & _). split; [exact Hz3|]. split; [subst toLoad; zlia|]. split; [exact Hs3|reflexivity].
    + subst skip. destruct (Z.eqb_spec (d_stage xst (zs_dc xst z)) DS_skipFrame) as [E|E].
      * cbn. zlia.
      * rewrite (Hlen E). subst toLoad. zlia.
Qed.

(* zdss_read *)
Lemma st_read_inv inp z ip dl :
  zinv z -> zs_stage xst z = ZDSS_read -> bytes_ok inp -> 0 <= ip <= Zlength inp ->
  match st_read inp z ip dl with
  | LErr _ => True
  | LNext _ z1 ip1 dl1 => zinv z1 /\ ip + 1 <= ip1 <= Zlength inp /\
                          (zs_stage xst z1 = ZDSS_read \/ zs_stage xst z1 = ZDSS_flush) /\ dl1 = dl
  | LStop _ z1 ip1 dl1 => zinv z1 /\ ip <= ip1 <= Zlength inp
  | LEarly _ _ _ => False
  end.
Proof.
  intros Hz Hs Hb Hip. pose proof Hz as (Hd & Hr & Hbf & He & Ho).
  destruct Hbf as (Hl & Hn & Hli & Hhb & Hib & Hih & Hlh & Hfc & Hbs).
  assert (Hs': zs_stage xst z <> ZDSS_load) by (rewrite Hs; discriminate).
  destruct (Hn Hs') as [Hp0 Hi0].
  pose proof Hd as (_ & _ & Hex & _).
  unfold ExStream.st_read.
  set (avail := Zlength inp - ip).
  set (needed := d_next_in xst (zs_dc xst z) avail).
  assert (Hneed: 0 <= needed /\ (needed = 0 -> d_expected xst (zs_dc xst z) = 0) /\
                 (avail >= 1 -> needed <> d_expected xst (zs_dc xst z) -> 1 <= needed <= avail)).
  { subst needed. unfold d_next_in. destruct (_ && _); split; zlia. }
  destruct (needed =? 0) eqn:E0.
  { apply Z.eqb_eq in E0. split; [|zlia].
    assert (He0: d_expected xst (zs_dc xst z) = 0) by (apply Hneed, E0).
    split; [exact Hd|]. split; [exact Hr|]. split.
    - unfold zi_buf; zs_simpl. zd_constsg.
      split; [intros C; zlia|]. split; [intros _; split; assumption|]. split; [intros C; zlia|].
      split; [exact Hhb|]. split; [exact Hib|]. split; [intros _; exact He0|]. split; [intros C; zlia|].
      split; assumption.
    - split; [|exact Ho]. unfold zi_ext; zs_simpl. intros Hz0. exfalso. exact (zi_dc_not_in _ Hd He0 Hz0). }
  apply Z.eqb_neq in E0.
  destruct (avail >=? needed) eqn:Ea.
  { apply Z.geb_le in Ea.
    destruct (z_dcs z _ needed) as [z1|] eqn:Hd1; [|exact I].
    apply z_dcs_zinv in Hd1; [| exact Hz | left; exact Hs | exact Hp0 | exact Hi0 | apply zf_bytes_slice, Hb
                            | rewrite zf_Zlength_slice by zlia; zlia].
    destruct Hd1 as (Hz1 & Hs1 & _). split; [exact Hz1|]. split; [zlia|]. split; [exact Hs1|reflexivity]. }
  rewrite Z.geb_leb, Z.leb_gt in Ea.
  destruct (avail =? 0) eqn:Ez.
  { split; [exact Hz|zlia]. }
  apply Z.eqb_neq in Ez.
  (* the load from zdss_read: needed = expected > avail >= 1, so the load stops *)
  assert (Hex': needed = d_expected xst (zs_dc xst z)).
  { destruct (Z.eq_dec needed (d_expected xst (zs_dc xst z))) as [E|E]; [exact E|].
    exfalso. assert (avail >= 1) by zlia. specialize (proj2 (proj2 Hneed) H E). zlia. }
  assert (Hzl: zinv (z_stage xst z ZDSS_load)) by (apply zinv_read_load; auto; zlia).
  unfold ExStream.st_load; cbn [zs_dc zs_inpos zs_inbs zs_ibuf z_stage].
  destruct (negb _ && _); [exact I|].
  rewrite Hp0, Z.sub_0_r. fold avail. rewrite <- Hex'.
  destruct (Z.min needed avail <? needed) eqn:Elt.
  - apply Z.ltb_lt in Elt. split; [|zlia].
    replace (0 + Z.min needed avail) with avail by zlia.
    refine (zinv_in _ _ _ Hzl eq_refl _ _ _); [change (zs_dc xst (z_stage xst z ZDSS_load)) with (zs_dc xst z); zlia | |]; zs_simpl.
    + destruct (d_stage xst (zs_dc xst z) =? DS_skipFrame); [exact Hib|].
      apply zf_bytes_app; [exact Hib | apply zf_bytes_slice, Hb].
    + intros E. apply Z.eqb_neq in E. rewrite E, Hi0. cbn [app].
      rewrite zf_Zlength_slice by zlia. zlia.
  - apply Z.ltb_ge in Elt. zlia.
Qed.

(* zdss_flush: outStart moves by what the room takes; once all is out, zdss_read, with the ring restarted at 0
   when the frame is larger than the ring and a block of Block_Maximum_Size would not fit after outStart *)
Lemma st_flush_inv room z ip dl :
  zinv z -> zs_stage xst z = ZDSS_flush -> Zlength dl <= room ->
  match st_flush room z ip dl with
  | LErr _ => True
  | LNext _ z1 ip1 dl1 => zinv z1 /\ ip1 = ip /\ zs_stage xst z1 = ZDSS_read /\ Zlength dl1 <= room
  | LStop _ z1 ip1 dl1 => zinv z1 /\ ip1 = ip
  | LEarly _ _ _ => False
  end.
Proof.
  intros (Hd & Hr & Hbf & He & Ho) Hs Hdl.
  destruct Hbf as (Hl & Hn & Hli & Hhb & Hib & Hih & Hlh & Hfc & Hbs).
  destruct Hr as (Ho1 & Ho2 & Hmb & Hml & Hoff).
  assert (Hs': zs_stage xst z <> ZDSS_load) by (rewrite Hs; discriminate).
  destruct (Hn Hs') as [Hp0 Hi0].
  unfold ExStream.st_flush.
  set (fl := Z.min (room - Zlength dl) (zs_oend xst z - zs_ostart xst z)).
  assert (Hfl: 0 <= fl <= zs_oend xst z - zs_ostart xst z) by (subst fl; zlia).
  assert (Hsl: Zlength (slice (zs_mem xst z) (zs_ostart xst z) fl) = fl) by (apply zf_Zlength_slice; zlia).
  assert (Hbuf: forall z', zs_stage xst z' = ZDSS_read \/ zs_stage xst z' = ZDSS_flush ->
     zs_inpos xst z' = 0 -> zs_ibuf xst z' = nil -> zs_hbuf xst z' = zs_hbuf xst z -> zs_fp xst z' = zs_fp xst z ->
     zs_dc xst z' = zs_dc xst z -> zi_buf z').
  { intros z' Hs1 Hp1 Hi1 Hh1 Hf1 Hd1. unfold zi_buf. rewrite Hp1, Hi1, Hh1, Hf1. zd_constsg.
    split; [intros C; zlia|]. split; [intros _; split; reflexivity|]. split; [intros C; zlia|].
    split; [exact Hhb|]. split; [constructor|]. split; [intros [C|C]; zlia|]. split; [intros C; zlia|].
    split; assumption. }
  destruct (Z.eqb_spec fl (zs_oend xst z - zs_ostart xst z)) as [Ef|Ef].
  - set (z2 := z_stage xst (z_ring xst z (zs_ostart xst z + fl) (zs_oend xst z)) ZDSS_read).
    assert (Hdl1: Zlength (dl ++ slice (zs_mem xst z) (zs_ostart xst z) fl) <= room)
      by (rewrite zf_Zlength_app, Hsl; subst fl; zlia).
    destruct ((zs_outbs xst z2 <? fh_contentSize (zs_fp xst z2)) &&
              (zs_ostart xst z2 + fh_blockSizeMax (zs_fp xst z2) >? zs_outbs xst z2)) eqn:Er;
      subst z2; zs_simpl; cbn [zs_outbs zs_fp zs_ostart z_stage z_ring] in Er.
    + apply andb_prop in Er. destruct Er as [Er1 Er2]. apply Z.ltb_lt in Er1.
      split; [|split; [reflexivity|split; [reflexivity|exact Hdl1]]].
      split; [exact Hd|]. split; [unfold zi_ring; zs_simpl; split; [zlia|]; split; [zlia|]; split; [exact Hmb|]; split; [exact Hml|]; exact Hoff|].
      split; [apply Hbuf; zs_simpl; auto; left; reflexivity|].
      split; [|exact Ho]. unfold zi_ext; zs_simpl. intros Hz. destruct (He Hz) as (E1 & E2 & E3 & E4).
      split; [exact E1|]. split; [exact E2|]. split; [|intros C; unfold ZDSS_read, ZDSS_flush in C; zlia].
      intros _. split; [right; right; split; [reflexivity|exact Er1]|].
      intros Hde. exact (proj2 (E2 Hde)).
    + split; [|split; [reflexivity|split; [reflexivity|exact Hdl1]]].
      split; [exact Hd|]. split; [unfold zi_ring; zs_simpl; split; [zlia|]; split; [zlia|]; split; [exact Hmb|]; split; [exact Hml|]; exact Hoff|].
      split; [apply Hbuf; zs_simpl; auto; left; reflexivity|].
      split; [|exact Ho]. unfold zi_ext; zs_simpl. intros Hz. destruct (He Hz) as (E1 & E2 & E3 & E4).
      split; [exact E1|]. split; [exact E2|]. split; [|intros C; unfold ZDSS_read, ZDSS_flush in C; zlia].
      intros _. split.
      * right; left. rewrite (E4 Hs). f_equal. zlia.
      * intros Hde. destruct (E2 Hde) as [Hlt Hpos]. specialize (E1 ltac:(zlia)).
        apply Z.ltb_lt in Hlt. rewrite Hlt in Er. cbn [andb] in Er. rewrite Z.gtb_ltb, Z.ltb_ge in Er. zlia.
  - split; [|reflexivity]. zs_simpl.
    split; [exact Hd|]. split; [unfold zi_ring; zs_simpl; split; [zlia|]; split; [zlia|]; split; [exact Hmb|]; split; [exact Hml|]; exact Hoff|].
    split; [apply Hbuf; zs_simpl; auto|].
    split; [|exact Ho]. unfold zi_ext; zs_simpl. intros Hz. destruct (He Hz) as (E1 & E2 & E3 & E4).
    split; [exact E1|]. split; [exact E2|]. split; [intros C; rewrite Hs in C; unfold ZDSS_read, ZDSS_load, ZDSS_flush in C; zlia|].
    intros _. exact (E4 Hs).
Qed.

(* the outcome of an iteration from a reached state, in a stage other than zdss_flush: an iteration that goes on
   reaches a state again, takes at least one input byte and writes nothing; a stop or the early return reaches a
   state *)
Definition iter_ok (inp: list Z) (ip: Z) (dl: list Z) (r: lstep) : Prop :=
  match r with
  | LErr _ => True
  | LNext _ z1 ip1 dl1 => zinv z1 /\ ip + 1 <= ip1 <= Zlength inp /\ dl1 = dl
  | LStop _ z1 _ _ => zinv z1
  | LEarly _ z1 _ => zinv z1
  end.

Lemma st_read_ok inp z ip dl :
  zinv z -> zs_stage xst z = ZDSS_read -> bytes_ok inp -> 0 <= ip <= Zlength inp ->
  iter_ok inp ip dl (st_read inp z ip dl).
Proof.
  intros Hz Hs Hb Hip. pose proof (st_read_inv inp z ip dl Hz Hs Hb Hip) as H.
  unfold iter_ok. destruct (st_read inp z ip dl); tauto.
Qed.

Lemma st_load_ok inp z ip dl :
  zinv z -> zs_stage xst z = ZDSS_load -> bytes_ok inp -> 0 <= ip <= Zlength inp ->
  iter_ok inp ip dl (st_load inp z ip dl).
Proof.
  intros Hz Hs Hb Hip. pose proof (st_load_inv inp z ip dl Hz Hs Hb Hip) as H.
  unfold iter_ok. destruct (st_load inp z ip dl); tauto.
Qed.

(* ZSTD_DCtx_updateOversizedDuration and the reallocation of zdss_loadHeader keep zi_over: oversizedDuration
   reaches 128 only with a reallocation to the frame's needs (4 <= needIn + needOut <= 2^29), and beyond 128 only
   when the buffers before were 3 times larger than these needs *)
Lemma zi_over_bufs (z z1: zstate) (s needIn needOut: Z) (m: list Z) :
  zi_over z -> 4 <= needIn -> 0 <= needOut -> needIn + needOut <= 2 ^ 29 ->
  zi_over (z_stage xst
    (if (zs_inbs xst z <? needIn) || (zs_outbs xst z <? needOut) ||
        ((if zs_inbs xst z + zs_outbs xst z >=? (needIn + needOut) * ZS_WORKSPACETOOLARGE_FACTOR
          then zs_over xst z + 1 else 0) >=? ZS_WORKSPACETOOLARGE_MAXDURATION)
     then z_bufs xst z1 needIn needOut
            (if zs_inbs xst z + zs_outbs xst z >=? (needIn + needOut) * ZS_WORKSPACETOOLARGE_FACTOR
             then zs_over xst z + 1 else 0) m
     else z_bufs xst z1 (zs_inbs xst z) (zs_outbs xst z)
            (if zs_inbs xst z + zs_outbs xst z >=? (needIn + needOut) * ZS_WORKSPACETOOLARGE_FACTOR
             then zs_over xst z + 1 else 0) (zs_mem xst z)) s).
Proof.
  intros (O1 & O2 & O3) Hi Ho Hs.
  unfold ZS_WORKSPACETOOLARGE_FACTOR, ZS_WORKSPACETOOLARGE_MAXDURATION in *.
  destruct (Z.geb_spec (zs_inbs xst z + zs_outbs xst z) ((needIn + needOut) * 3)) as [Hg|Hg].
  - destruct (Z.geb_spec (zs_over xst z + 1) 128) as [Hc|Hc]; rewrite ?Bool.orb_true_r.
    + unfold zi_over; zs_simpl. unfold ZS_WORKSPACETOOLARGE_MAXDURATION.
      split; [lia|]. split; [lia|]. intros _. split; [lia|].
      destruct (Z.eq_dec (zs_over xst z) 127) as [E|E].
      { rewrite E. cbn. lia. }
      destruct (O3 ltac:(lia)) as [_ O4].
      replace (zs_over xst z + 1 - 128) with (Z.succ (zs_over xst z - 128)) by lia.
      rewrite Z.pow_succ_r by lia.
      assert (0 <= 3 ^ (zs_over xst z - 128)) by (apply Z.pow_nonneg; lia). nia.
    + rewrite Bool.orb_false_r.
      destruct ((zs_inbs xst z <? needIn) || (zs_outbs xst z <? needOut));
        unfold zi_over; zs_simpl; unfold ZS_WORKSPACETOOLARGE_MAXDURATION; lia.
  - rewrite Bool.orb_false_r.
    destruct ((zs_inbs xst z <? needIn) || (zs_outbs xst z <? needOut));
      unfold zi_over; zs_simpl; unfold ZS_WORKSPACETOOLARGE_MAXDURATION; lia.
Qed.

(* zdss_loadHeader once the header h is complete: the single-pass shortcut stops, otherwise zdss_read *)
Lemma st_header_done_ok inp room z h ip dl :
  zinv z -> zs_stage xst z = ZDSS_loadHeader -> get_frame_header (zs_hbuf xst z) = FH_ok h ->
  bytes_ok inp -> 0 <= ip <= Zlength inp ->
  iter_ok inp ip dl (st_header_done inp room z h ip dl).
Proof.
  intros Hz Hs Hg Hb Hip. pose proof Hz as (Hd & Hr & Hbf & He & Ho).
  destruct Hbf as (Hl & Hn & Hli & Hhb & Hib & Hih & Hlh & Hfc & Hbs).
  destruct Hr as (Ho1 & Ho2 & Hmb & Hml & Hoff).
  assert (Hs': zs_stage xst z <> ZDSS_load) by (rewrite Hs; discriminate).
  destruct (Hn Hs') as [Hp0 Hi0].
  assert (He0: d_expected xst (zs_dc xst z) = 0) by (apply Hih; right; exact Hs).
  destruct (Hlh Hs) as [Hos Hoe].
  destruct (zf_gfh_bounds _ _ Hhb Hg) as (G1 & G2 & G3).
  pose proof Hd as (Dst & Dbt & Dex & Drl & Din & Dg).
  unfold ExStream.st_header_done. cbv zeta.
  match goal with |- iter_ok _ _ _ (match ?s with Some _ => _ | None => _ end) => destruct s as [cs|] end.
  - match goal with |- iter_ok _ _ _ (match ?s with Some _ => _ | None => _ end) =>
      destruct s as [[[c k] e]|] eqn:Hf end; [|exact I].
    destruct (k =? cs); [|exact I]. cbn [iter_ok].
    assert (Hge: xgood e) by (exact (xgood_frame1 _ _ _ _ _ _ Dg (zf_forall_firstn _ _ _ Hb) Hf)).
    split; [|split; [|split]].
    + unfold zi_dc; zs_simpl; zd_simplg. split; [exact Dst|]. split; [exact Dbt|]. split; [zlia|].
      split; [exact Drl|]. split; [intros Hz0; exfalso; exact (zi_dc_not_in _ Hd He0 Hz0)|exact Hge].
    + unfold zi_ring; zs_simpl; zd_simplg. split; [zlia|]. split; [zlia|]. split; [exact Hmb|]. split; [exact Hml|].
      exact Hoff.
    + unfold zi_buf; zs_simpl; zd_simplg. zd_constsg.
      split; [intros C; zlia|]. split; [intros _; split; assumption|]. split; [intros C; zlia|].
      split; [exact Hhb|]. split; [exact Hib|]. split; [intros _; reflexivity|]. split; [intros C; zlia|].
      split; assumption.
    + split; [|exact Ho]. unfold zi_ext; zs_simpl. intros Hz0. exfalso. apply (zi_dc_not_in _ Hd He0). exact Hz0.
  - match goal with |- iter_ok _ _ _ (match ?s with Some _ => _ | None => _ end) => destruct s as [d1|] eqn:Hd1 end;
      [|exact I].
    assert (D1: zi_dc d1 /\ d_prev xst d1 = None /\ d_pfx xst d1 = None /\ d_ds xst d1 = None /\
                d_de xst d1 = None /\
                (zin d1 -> is_skippable_magic (le_field (zs_hbuf xst z) 0 4) = false)).
    { revert Hd1. destruct (is_skippable_magic _) eqn:Esk.
      - intros H; injection H as <-. zd_simplg. pose proof (zf_le_field_lt (zs_hbuf xst z) 4 4 Hhb ltac:(zlia)).
        pose proof (zf_le_field_nonneg (zs_hbuf xst z) 4 4 Hhb).
        unfold zi_dc, zin; zd_simplg; zd_constsg. change (2 ^ (8 * 4)) with (2 ^ 32) in *.
        split; [split; [zlia|]; split; [zlia|]; split; [zlia|]; split; [exact Drl|]; split; [intros; zlia|]; apply xgood_begin, Dg|].
        repeat split; auto. intros; zlia.
      - destruct (negb _); [discriminate|]. intros H; injection H as <-.
        unfold zi_dc, zin; zd_simplg; zd_constsg.
        split; [split; [zlia|]; split; [zlia|]; split; [zlia|]; split; [exact Drl|]; split; [intros; zlia|]; apply xgood_begin, Dg|].
        repeat split; auto. }
    destruct D1 as (D1 & P1 & P2 & P3 & P4 & Psk).
    destruct (_ >? ZS_MAXWINDOWSIZE_DEFAULT) eqn:Ews; [exact I|]. rewrite Z.gtb_ltb, Z.ltb_ge in Ews.
    match goal with |- iter_ok _ _ _ (ExStream.st_read _ _ _ ?z' _ _) => apply (st_read_ok inp z') end;
      [| reflexivity | exact Hb | exact Hip].
    set (ws := Z.max (fh_windowSize h) (2 ^ ZSTD_WINDOWLOG_ABSOLUTEMIN)).
    set (needOut := Z.min (fh_contentSize h)
                      (ws + 2 * Z.min (Z.min ws ZSTD_BLOCKSIZE_MAX) (fh_blockSizeMax h) + 2 * ZS_WILDCOPY_OVERLENGTH)).
    assert (Hno: 0 <= needOut).
    { subst needOut ws. unfold ZSTD_BLOCKSIZE_MAX, ZS_WILDCOPY_OVERLENGTH, ZSTD_WINDOWLOG_ABSOLUTEMIN. zlia. }
    assert (Hoffn: forall n, zi_off d1 n) by (intros n x [Hx|[Hx|[Hx|Hx]]]; congruence).
    pose proof (zf_gfh_bsm _ _ Hg) as Hbm.
    match goal with |- zinv ?w => assert (HOv: zi_over w) end.
    { apply zi_over_bufs; [exact Ho | zlia | exact Hno |].
      subst needOut ws. unfold ZS_MAXWINDOWSIZE_DEFAULT, ZSTD_BLOCKSIZE_MAX, ZS_WILDCOPY_OVERLENGTH,
        ZSTD_WINDOWLOG_ABSOLUTEMIN in *. zlia. }
    revert HOv.
    match goal with |- _ -> zinv (z_stage xst (if ?b then _ else _) ZDSS_read) => destruct b end;
      intros HOv; zs_simpl; (split; [exact D1|]); unfold zi_ring, zi_buf, zi_ext; zs_simpl; zd_constsg.
    + split.
      { split; [zlia|]. split; [zlia|]. split; [unfold bytes_ok, ring_fresh; apply Forall_forall; intros x Hx;
          apply repeat_spec in Hx; subst x; unfold is_byte; zlia|].
        split; [unfold ring_fresh; rewrite Zlength_correct, repeat_length; zlia|]. apply Hoffn. }
      split.
      { split; [intros C; zlia|]. split; [intros _; split; assumption|]. split; [intros C; zlia|].
        split; [exact Hhb|]. split; [exact Hib|]. split; [intros [C|C]; zlia|]. split; [intros C; zlia|].
        split; assumption. }
      split; [|exact HOv]. intros Hz0. split; [intros Hc; apply G3; [apply Psk, Hz0 | exact Hc]|].
      split; [intros C; contradiction|]. split; [intros _; split; [left; exact P1 | intros C; contradiction]|].
      intros C; zlia.
    + split.
      { split; [zlia|]. split; [zlia|]. split; [exact Hmb|]. split; [exact Hml|]. apply Hoffn. }
      split.
      { split; [intros C; zlia|]. split; [intros _; split; assumption|]. split; [intros C; zlia|].
        split; [exact Hhb|]. split; [exact Hib|]. split; [intros [C|C]; zlia|]. split; [intros C; zlia|].
        split; assumption. }
      split; [|exact HOv]. intros Hz0. split; [intros Hc; apply G3; [apply Psk, Hz0 | exact Hc]|].
      split; [intros C; contradiction|]. split; [intros _; split; [left; exact P1 | intros C; contradiction]|].
      intros C; zlia.
Qed.

(* zdss_init / zdss_loadHeader *)
Lemma st_load_header_ok inp room z ip dl :
  zinv z -> zs_stage xst z = ZDSS_loadHeader -> bytes_ok inp -> 0 <= ip <= Zlength inp ->
  iter_ok inp ip dl (st_load_header inp room z ip dl).
Proof.
  intros Hz Hs Hb Hip. pose proof Hz as (Hd & Hr & Hbf & He & Ho).
  destruct Hbf as (Hl & Hn & Hli & Hhb & Hib & Hih & Hlh & Hfc & Hbs).
  unfold ExStream.st_load_header. cbv zeta.
  destruct (get_frame_header (zs_hbuf xst z)) as [|hSize|h] eqn:Hg.
  - exact I.
  - pose proof (get_frame_header_more _ _ Hg) as Hlt.
    destruct (hSize - Zlength (zs_hbuf xst z) >? Zlength inp - ip) eqn:Et.
    + match goal with |- iter_ok _ _ _ (match get_frame_header ?l with _ => _ end) =>
        destruct (get_frame_header l) end; try exact I;
        (apply zinv_hbuf; [exact Hz | apply zf_bytes_app; [exact Hhb | apply zf_bytes_slice, Hb]]).
    + rewrite Z.gtb_ltb, Z.ltb_ge in Et. cbn [iter_ok].
      split; [apply zinv_hbuf; [exact Hz | apply zf_bytes_app; [exact Hhb | apply zf_bytes_slice, Hb]]|].
      split; [|reflexivity]. zlia.
  - destruct (zf_gfh_bounds _ _ Hhb Hg) as (G1 & G2 & G3).
    apply st_header_done_ok; auto.
    split; [exact Hd|]. split; [exact Hr|]. split.
    + unfold zi_buf; zs_simpl. split; [exact Hl|]. split; [exact Hn|]. split; [exact Hli|]. split; [exact Hhb|].
      split; [exact Hib|]. split; [exact Hih|]. split; [exact Hlh|]. split; assumption.
    + split; [|exact Ho]. unfold zi_ext; zs_simpl. intros Hz0. exfalso. apply (zi_dc_not_in _ Hd); [apply Hih; right; exact Hs | exact Hz0].
Qed.

(* the same with the potential: an iteration that goes on lowers it, and writes no more than the room *)
Definition iter_pot (inp: list Z) (room: Z) (z: zstate) (ip: Z) (r: lstep) : Prop :=
  match r with
  | LErr _ => True
  | LNext _ z1 ip1 dl1 => zinv z1 /\ ip <= ip1 <= Zlength inp /\ zpot inp z1 ip1 < zpot inp z ip /\
                          Zlength dl1 <= room
  | LStop _ z1 _ _ => zinv z1
  | LEarly _ z1 _ => zinv z1
  end.

Lemma iter_ok_pot inp room z ip dl r :
  zs_stage xst z <> ZDSS_flush -> Zlength dl <= room -> iter_ok inp ip dl r -> iter_pot inp room z ip r.
Proof.
  intros Hs Hdl. unfold iter_ok, iter_pot. destruct r as [|z1 ip1 dl1|z1 ip1 dl1|z1 r0]; auto.
  intros (H1 & H2 & ->). split; [exact H1|]. split; [zlia|]. split; [|exact Hdl]. unfold zpot.
  destruct (Z.eqb_spec (zs_stage xst z) ZDSS_flush); [contradiction|].
  destruct (zs_stage xst z1 =? ZDSS_flush); zlia.
Qed.

Lemma one_iter_ok inp room z ip dl :
  zinv z -> bytes_ok inp -> 0 <= ip <= Zlength inp -> Zlength dl <= room ->
  iter_pot inp room z ip (one_iter inp room z ip dl).
Proof.
  intros Hz Hb Hip Hdl.
  unfold ExStream.one_iter.
  destruct (zs_stage xst z =? ZDSS_flush) eqn:E4.
  { apply Z.eqb_eq in E4. rewrite E4. cbn - [ExStream.st_flush].
    pose proof (st_flush_inv room z ip dl Hz E4 Hdl) as H. unfold iter_pot.
    destruct (st_flush room z ip dl) as [|z1 ip1 dl1|z1 ip1 dl1|z1 r0]; try tauto.
    destruct H as (H1 & -> & H3 & H4). split; [exact H1|]. split; [zlia|]. split; [|exact H4].
    unfold zpot. rewrite E4, H3. cbn. zlia. }
  apply Z.eqb_neq in E4. apply (iter_ok_pot _ _ _ _ dl); [exact E4 | exact Hdl |].
  destruct (zs_stage xst z =? ZDSS_init) eqn:E0.
  { apply Z.eqb_eq in E0. apply st_load_header_ok; [apply zinv_new_frame; auto | reflexivity | exact Hb | exact Hip]. }
  destruct (zs_stage xst z =? ZDSS_loadHeader) eqn:E1.
  { apply Z.eqb_eq in E1. apply st_load_header_ok; auto. }
  destruct (zs_stage xst z =? ZDSS_read) eqn:E2.
  { apply Z.eqb_eq in E2. apply st_read_ok; auto. }
  destruct (zs_stage xst z =? ZDSS_load) eqn:E3.
  { apply Z.eqb_eq in E3. apply st_load_ok; auto. }
  exact I.
Qed.

(* ---------- the loop's fuel ---------- *)

Lemma zpot_pos inp z ip : ip <= Zlength inp -> 1 <= zpot inp z ip.
Proof. intros H. unfold zpot. destruct (_ =? _); lia. Qed.

(* the potential at the call's start is below zstep's fuel *)
Lemma zpot_start inp z : zpot inp z 0 < Z.of_nat (zfuel inp).
Proof.
  unfold zpot, zfuel. rewrite Zlength_correct, Nat2Z.inj_add, Nat2Z.inj_mul. destruct (_ =? _); lia.
Qed.

(* any fuel above the potential gives the same outcome *)
Lemma z_loop_fuel (f1 f2: nat) inp room z ip dl :
  zinv z -> bytes_ok inp -> 0 <= ip <= Zlength inp -> Zlength dl <= room ->
  zpot inp z ip < Z.of_nat f1 -> zpot inp z ip < Z.of_nat f2 ->
  z_loop f1 inp room z ip dl = z_loop f2 inp room z ip dl.
Proof.
  revert f2 z ip dl. induction f1 as [|f1 IH]; intros f2 z ip dl Hz Hb Hip Hdl H1 H2.
  - pose proof (zpot_pos inp z ip (proj2 Hip)). simpl in H1. lia.
  - destruct f2 as [|f2]; [pose proof (zpot_pos inp z ip (proj2 Hip)); simpl in H2; lia|].
    rewrite !z_loop_S. pose proof (one_iter_ok inp room z ip dl Hz Hb Hip Hdl) as H.
    destruct (one_iter inp room z ip dl) as [|z1 ip1 dl1|z1 ip1 dl1|z1 r0]; try reflexivity.
    destruct H as (Hz1 & Hip1 & Hp & Hdl1). apply IH; auto; try lia.
Qed.

(* the loop's outcome: never a pending iteration; a stop or an early return in a reached state *)
Definition loop_ok (r: lstep) : Prop :=
  match r with
  | LErr _ => True
  | LNext _ _ _ _ => False
  | LStop _ z1 _ _ => zinv z1
  | LEarly _ z1 _ => zinv z1
  end.

Lemma z_loop_ok (f: nat) inp room z ip dl :
  zinv z -> bytes_ok inp -> 0 <= ip <= Zlength inp -> Zlength dl <= room -> zpot inp z ip < Z.of_nat f ->
  loop_ok (z_loop f inp room z ip dl).
Proof.
  revert z ip dl. induction f as [|f IH]; intros z ip dl Hz Hb Hip Hdl H1.
  - pose proof (zpot_pos inp z ip (proj2 Hip)). simpl in H1. lia.
  - rewrite z_loop_S. pose proof (one_iter_ok inp room z ip dl Hz Hb Hip Hdl) as H.
    destruct (one_iter inp room z ip dl) as [|z1 ip1 dl1|z1 ip1 dl1|z1 r0]; simpl; auto.
    destruct H as (Hz1 & Hip1 & Hp & Hdl1). apply IH; auto; lia.
Qed.

(* a call from a reached state is its loop with any fuel above the potential, then the epilogue: the proof of
   the C loop may count its iterations down from any such fuel *)
Lemma zstep_loop z inp room (f: nat) :
  zinv z -> bytes_ok inp -> 0 <= room -> zpot inp z 0 < Z.of_nat f ->
  zstep z (inp, room) = z_epi inp room (z_loop f inp room z 0 nil).
Proof.
  intros Hz Hb Hr Hf. rewrite zstep_unfold.
  destruct (Z.ltb_spec room 0); [lia|]. f_equal.
  apply z_loop_fuel; auto.
  all: first [split; [lia | apply zf_Zlength_nonneg] | rewrite Zlength_nil; lia | apply zpot_start].
Qed.

(* the epilogue keeps the invariant *)
Lemma z_epi_zinv inp room r z' o : loop_ok r -> z_epi inp room r = Some (z', o) -> zinv z'.
Proof.
  unfold z_epi. destruct r as [|z1 ip1 dl1|z1 ip1 dl1|z1 r0]; simpl; try discriminate.
  - intros Hz. cbv zeta.
    pose proof Hz as (Hd & Hr & Hbf & He & Ho).
    destruct (_ && _ && _); [discriminate|].
    assert (Hn: forall n, zinv (z_nfp xst z1 n)) by (intros n; exact Hz).
    assert (Hh: forall n, zinv (z_host xst (z_nfp xst z1 n) 1)) by (intros n; exact Hz).
    match goal with |- context [if d_expected xst (zs_dc xst ?w) =? 0 then _ else _] =>
      destruct (d_expected xst (zs_dc xst w) =? 0) eqn:Ee end.
    + apply Z.eqb_eq in Ee. simpl in Ee.
      destruct Hbf as (Hl & Hn' & Hli & Hhb & Hib & Hih & Hlh & Hfc & Hbs).
      assert (Hs': zs_stage xst z1 <> ZDSS_load) by (intros Hs; specialize (Hl Hs); lia).
      destruct (Hn' Hs') as [Hp0 Hi0].
      assert (Hrd: forall n, zinv (z_stage xst (z_nfp xst z1 n) ZDSS_read)).
      { intros n. split; [exact Hd|]. split; [exact Hr|]. split.
        - unfold zi_buf; zs_simpl. zd_consts.
          split; [intros C; lia|]. split; [intros _; split; assumption|]. split; [intros C; lia|].
          split; [exact Hhb|]. split; [exact Hib|]. split; [intros [C|C]; lia|]. split; [intros C; lia|].
          split; assumption.
        - split; [|exact Ho]. unfold zi_ext; zs_simpl. intros Hz0. exfalso. exact (zi_dc_not_in _ Hd Ee Hz0). }
      repeat match goal with |- context [if ?b then _ else _] => destruct b end;
        intros H; injection H as <- _; auto.
    + intros H; injection H as <- _. apply Hn.
  - intros Hz H; injection H as <- _. exact Hz.
Qed.

Lemma zstep_zinv z c z' o : zinv z -> bytes_ok (fst c) -> zstep z c = Some (z', o) -> zinv z'.
Proof.
  destruct c as [inp room]. intros Hz Hb. simpl in Hb. rewrite zstep_unfold.
  destruct (Z.ltb_spec room 0); [discriminate|].
  apply z_epi_zinv, z_loop_ok; auto.
  all: first [split; [lia | apply zf_Zlength_nonneg] | rewrite Zlength_nil; lia | apply zpot_start].
Qed.

(* every state a history of byte inputs reaches satisfies the invariant *)
Lemma zs_run_from_zinv z h z' :
  zinv z -> Forall (fun c: zcall => bytes_ok (fst c)) h -> zs_run_from z h = Some z' -> zinv z'.
Proof.
  revert z. induction h as [|c h IH]; intros z Hz Hh; simpl.
  - intros H; inversion H; subst; exact Hz.
  - inversion Hh; subst.
    destruct (zstep z c) as [[z1 o]|] eqn:Hs; [|discriminate].
    apply IH; auto. eapply zstep_zinv; eauto.
Qed.

Lemma zs_run_zinv h z :
  Forall (fun c: zcall => bytes_ok (fst c)) h -> zs_run h = Some z -> zinv z.
Proof. intros Hh. apply zs_run_from_zinv; auto. apply zinv_init. Qed.

(* ---------- zstate_init ---------- *)

(* the image of a new context, or of one reset with the parameters: stage zdss_init, no buffers, no ring
   cells, oversizedDuration and noForwardProgress 0, the block decoder's state xst_init *)
Lemma zstate_init_fields :
  let z := zstate_init xst xst_init in
  zs_stage xst z = ZDSS_init /\ zs_inbs xst z = 0 /\ zs_outbs xst z = 0 /\ zs_mem xst z = nil /\
  zs_over xst z = 0 /\ zs_nfp xst z = 0 /\ d_ent xst (zs_dc xst z) = xst_init.
Proof. repeat split. Qed.

End Facts.

(* ---------- model/Exact.v's instance ---------- *)

(* the stream state of Exact.zs_call, the run of a history and one call *)
Definition zstate_x : Type := ExStream.zstate Exact.xstate.
Definition xframe1 := ExFrame.x_frame Exact.xstate (ExBlock.xst_begin ExHuf.xhuf) Exact.xblock.
Definition zs_run_x (h: list zcall) : option zstate_x :=
  ExStream.zs_run Exact.xstate (ExBlock.xst_init ExHuf.xhuf) (ExBlock.xst_begin ExHuf.xhuf) Exact.xblock xframe1 h.
Definition zstep_x (z: zstate_x) (c: zcall) : option (zstate_x * (Z * Z * list Z * Z * Z)) :=
  ExStream.zstep Exact.xstate (ExBlock.xst_begin ExHuf.xhuf) Exact.xblock xframe1 z c.

(* the block decoder's state is good: litExtraBuffer holds bytes, the Huffman table's cells are in range *)
Definition xgood_x (e: Exact.xstate) : Prop :=
  bytes_ok (ExBlock.x_lxb ExHuf.xhuf e) /\ ExBlockBytes.xh_good (ExBlock.x_huf ExHuf.xhuf e).

Lemma xgood_x_init : xgood_x (ExBlock.xst_init ExHuf.xhuf).
Proof.
  split; [|exact I]. unfold ExBlock.xst_init; cbn [ExBlock.x_lxb].
  apply Forall_forall. intros x Hx. apply repeat_spec in Hx. subst x. unfold is_byte. lia.
Qed.

Lemma xgood_x_begin (e: Exact.xstate) : xgood_x e -> xgood_x (ExBlock.xst_begin ExHuf.xhuf e).
Proof. intros [H _]. split; [exact H | exact I]. Qed.

(* a compressed block decoded into the ring keeps it: ExBlockBytes (bytes), ExBlockWritten (the size within the
   capacity), ExBlockLen (the ring's length) *)
Lemma xgood_x_block : forall e mem ps op ds de body bsm cap e' mem' n,
  xgood_x e -> bytes_ok mem -> bytes_ok body -> 0 <= op -> 0 <= cap -> op + cap <= Zlength mem ->
  Exact.xblock e mem ps op ds de body bsm cap true = Some (e', mem', n) ->
  xgood_x e' /\ bytes_ok mem' /\ Zlength mem' = Zlength mem /\ 0 <= n <= cap.
Proof.
  intros e mem ps op ds de body bsm cap e' mem' n [Hl Hh] Hm Hb Hop Hc Hle H.
  destruct (ExBlockBytes.xblock_bytes _ _ _ _ _ _ _ _ _ _ _ _ _ Hm Hb Hl Hh H) as (B1 & B2 & B3).
  assert (Hop': 0 <= op <= Zlength mem) by lia.
  destruct (ExBlockWritten.xblock_written_cap _ _ _ _ _ _ _ _ _ _ _ _ _ Hop' H) as (W1 & _).
  pose proof (ExBlockLen.xblock_len _ _ _ _ _ _ _ _ _ _ _ _ Hop Hc Hle H) as L.
  split; [split; assumption|]. auto.
Qed.

(* the block loop of a one-shot frame on bytes keeps a good state *)
Lemma xgood_x_blocks (f: nat) (st st': Exact.xstate) (t out o: list Z) (cap bsm k: Z) :
  xgood_x st -> bytes_ok t -> bytes_ok out ->
  ExFrame.x_blocks Exact.xstate Exact.xblock f st t out cap bsm = Some (o, k, st') -> xgood_x st'.
Proof.
  revert st t out o k. induction f as [|f IH]; intros st t out o k Hg Ht Ho H; [discriminate|].
  rewrite ExFrameFacts.x_blocks_S in H.
  destruct (ExFrameFacts.xb_one Exact.xstate Exact.xblock st t out cap bsm) as [[[[st1 cn] n] l]|] eqn:E;
    [|discriminate].
  destruct Hg as [Hl Hh].
  destruct (ExBlockBytes.xb_one_bytes _ _ _ _ _ _ _ _ _ Ht Ho Hl Hh E) as (Bc & Bl & Bh).
  destruct l.
  - injection H as _ _ <-. split; assumption.
  - destruct (ExFrame.x_blocks Exact.xstate Exact.xblock f st1 (skipn (Z.to_nat n) t) (out ++ cn) cap bsm)
      as [[[o' k'] st'']|] eqn:E2; [|discriminate].
    injection H as _ _ <-. eapply (IH st1); [split; [exact Bl | exact Bh] | apply zf_forall_skipn, Ht | apply zf_bytes_app; [exact Ho | exact Bc] | exact E2].
Qed.

Lemma xgood_x_frame1 : forall e s cap c k e',
  xgood_x e -> bytes_ok s -> xframe1 e s cap = Some (c, k, e') -> xgood_x e'.
Proof.
  intros e s cap c k e' Hg Hs. unfold xframe1, ExFrame.x_frame.
  destruct (_ <? _); [discriminate|]. destruct (_ <? _); [discriminate|].
  destruct (get_frame_header _) as [| |h]; try discriminate.
  destruct (negb _); [discriminate|].
  destruct (ExFrame.x_blocks _ _ _ _ _ _ _ _) as [[[out k1] st1]|] eqn:E; [|discriminate].
  assert (G: xgood_x st1).
  { eapply xgood_x_blocks; [apply xgood_x_begin, Hg | apply zf_forall_skipn, Hs | constructor | exact E]. }
  destruct (_ && _); [discriminate|].
  destruct (_ =? 1); [destruct (_ <? 4); [discriminate|]; destruct (negb _); [discriminate|]|];
    intros H; injection H as _ _ <-; exact G.
Qed.

Definition zinv_x (z: zstate_x) : Prop := zinv Exact.xstate xgood_x z.

Lemma zinv_x_init : zinv_x (zstate_init Exact.xstate (ExBlock.xst_init ExHuf.xhuf)).
Proof. apply zinv_init, xgood_x_init. Qed.

Lemma zs_call_x (h: list zcall) (c: zcall) :
  Exact.zs_call h c = match zs_run_x h with Some z => option_map snd (zstep_x z c) | None => None end.
Proof. reflexivity. Qed.

Lemma zs_run_x_nil : zs_run_x nil = Some (zstate_init Exact.xstate (ExBlock.xst_init ExHuf.xhuf)).
Proof. reflexivity. Qed.

Lemma zs_run_x_snoc (h: list zcall) (c: zcall) :
  zs_run_x (h ++ [c]) = match zs_run_x h with Some z => option_map fst (zstep_x z c) | None => None end.
Proof. apply zs_run_snoc. Qed.

(* what the proof of a call concludes: the C's outcome is zstep_x's from the state of the history *)
Lemma zs_call_x_step (h: list zcall) (c: zcall) (z z': zstate_x) o :
  zs_run_x h = Some z -> zstep_x z c = Some (z', o) -> Exact.zs_call h c = Some o /\ zs_run_x (h ++ [c]) = Some z'.
Proof. apply zs_call_step. Qed.

Lemma zs_call_x_none (h: list zcall) (c: zcall) (z: zstate_x) :
  zs_run_x h = Some z -> zstep_x z c = None -> Exact.zs_call h c = None.
Proof. apply zs_call_step_none. Qed.

Lemma zs_run_x_zinv (h: list zcall) (z: zstate_x) :
  Forall (fun c: zcall => bytes_ok (fst c)) h -> zs_run_x h = Some z -> zinv_x z.
Proof. apply zs_run_zinv; [exact xgood_x_init | exact xgood_x_begin | exact xgood_x_frame1 | exact xgood_x_block]. Qed.

Lemma zstep_x_loop (z: zstate_x) (inp: list Z) (room: Z) (f: nat) :
  zinv_x z -> bytes_ok inp -> 0 <= room -> zpot Exact.xstate inp z 0 < Z.of_nat f ->
  zstep_x z (inp, room) =
  z_epi Exact.xstate inp room
    (ExStream.z_loop Exact.xstate (ExBlock.xst_begin ExHuf.xhuf) Exact.xblock xframe1 f inp room z 0 nil).
Proof.
  intros Hz Hb Hr Hf.
  exact (zstep_loop _ _ _ _ xgood_x xgood_x_begin xgood_x_frame1 xgood_x_block
           z inp room f Hz Hb Hr Hf).
Qed.

(* one iteration of the loop from a reached state (the bytes dl delivered so far within the room) *)
Lemma one_iter_ok_x (inp: list Z) (room: Z) (z: zstate_x) (ip: Z) (dl: list Z) :
  zinv_x z -> bytes_ok inp -> 0 <= ip <= Zlength inp -> Zlength dl <= room ->
  iter_pot Exact.xstate xgood_x inp room z ip
    (ExStream.one_iter Exact.xstate (ExBlock.xst_begin ExHuf.xhuf) Exact.xblock xframe1 inp room z ip dl).
Proof.
  intros Hz Hb Hip Hdl.
  exact (one_iter_ok _ _ _ _ xgood_x xgood_x_begin xgood_x_frame1 xgood_x_block
           inp room z ip dl Hz Hb Hip Hdl).
Qed.
