(* The exact one-shot result (Exact.os_res) step by step, as the proof of ZSTD_decompressMultiFrame walks its input:
   xs_rest t cap acc is what os_res gives for the rest t of the input after the output acc, and each iteration of
   the C's loop (the end of the input, a skippable frame, a Zstandard frame) is one equation.

   os_res starts from a new context (litExtraBuffer zeroed); a context reaching ZSTD_decompressDCtx may hold any
   bytes there, and every frame starts from whatever the previous one left.  The equations therefore take a frame
   from ANY state whose litExtraBuffer has its full size: by ExBlockIndep.xblock_indep the content and the bytes
   taken do not depend on its contents (ExFrameFacts' independence, with ExBlockWritten.xblock_written for the
   size and ExBlockReps.xblock_reps for the nonzero repeat offsets every block starts with).  This is why oneshot_exact needs nothing of the context but no dictionary and the default parameters.
   Plain Coq. *)
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.ExHuf Zstd.proof.model.ExBlock.
Require Import Zstd.proof.model.ExFrame Zstd.proof.model.Exact Zstd.proof.model.ExFrameFacts.
Require Import Zstd.proof.model.ExAgreeDefs.
Require Import Zstd.proof.model.ExBlockIndep Zstd.proof.model.ExBlockWritten Zstd.proof.model.ExBlockReps.
Require Import Zstd.proof.dec.FS.FramesHdr.
Import ListNotations.
Local Open Scope Z_scope.

Local Notation XF := (x_frame xstate (xst_begin xhuf) xblock).
Local Notation XS := (x_series_loop xstate (xst_begin xhuf) xblock).

(* litExtraBuffer has its full size (XLITEXTRA + WILDCOPY_OVERLENGTH bytes, DecRep.LITEXTRA_N) *)
Definition lxb_ok (a: xstate) : Prop := Zlength (x_lxb xhuf a) = XLITEXTRA + XWILDCOPY.

Lemma lxb_ok_init : lxb_ok (xst_init xhuf).
Proof. unfold lxb_ok, xst_init. cbn [x_lxb]. rewrite Zlength_correct, repeat_length, Z2Nat.id; [reflexivity|]. unfold XLITEXTRA, XWILDCOPY. lia. Qed.

(* the relations of ExFrameFacts' independence: at a block, the same state up to litExtraBuffer's contents (of full
   size), with repeat offsets in [1, 2^32) and sequence tables of the format's codes; between frames, any two states
   with a full-size litExtraBuffer *)
Definition rb (a b: xstate) : Prop := xrel a b /\ lxb_ok a /\ reps_ok (x_rep xhuf a) /\ of_ok (x_seq xhuf a).
Definition rs (a b: xstate) : Prop := lxb_ok a /\ lxb_ok b.

Lemma rs_begin (a b: xstate) : rs a b -> rb (xst_begin xhuf a) (xst_begin xhuf b).
Proof.
  intros [Ha Hb]. unfold rb, xrel, lxb_ok, reps_ok, of_ok in *. cbn [xst_begin x_huf x_seq x_rep x_lxb].
  rewrite Ha, Hb. repeat split; lia.
Qed.

Lemma rb_rs (a b: xstate) : rb a b -> rs a b.
Proof. intros [(_ & _ & _ & E) [H _]]. unfold rs, lxb_ok in *. rewrite <- E. auto. Qed.

Lemma rb_block (a b: xstate) (mem body: list Z) (bsm cap: Z) :
  rb a b -> bytes_ok body ->
  match xblock a mem 0 (Zlength mem) 0 0 body bsm cap false, xblock b mem 0 (Zlength mem) 0 0 body bsm cap false with
  | None, None => True
  | Some (a', m1, n1), Some (b', m2, n2) =>
      n1 = n2 /\ rb a' b' /\ slice m1 (Zlength mem) n1 = slice m2 (Zlength mem) n2
  | _, _ => False
  end.
Proof.
  intros (R & L & Hr & Ho) Hbody.
  assert (Hr1: let '(r1, r2, r3) := x_rep xhuf a in 1 <= r1 /\ 1 <= r2 /\ 1 <= r3).
  { unfold reps_ok in Hr. destruct (x_rep xhuf a) as [[r1 r2] r3]. lia. }
  pose proof (xblock_indep a b mem body bsm cap R Hr1) as H.
  destruct (xblock a mem 0 (Zlength mem) 0 0 body bsm cap false) as [[[a' m1] n1]|] eqn:E1;
    destruct (xblock b mem 0 (Zlength mem) 0 0 body bsm cap false) as [[[b' m2] n2]|]; try contradiction; [|exact I].
  destruct H as (-> & R' & C). split; [reflexivity|]. split; [|exact C]. split; [exact R'|].
  assert (Hm: 0 <= Zlength mem <= Zlength mem) by (rewrite Zlength_correct; lia).
  destruct (xblock_written a a' mem m1 0 (Zlength mem) 0 0 body bsm cap false n2 Hm E1) as (_ & _ & _ & Hl).
  destruct (xblock_reps a a' mem m1 0 (Zlength mem) 0 0 body bsm cap false n2 Hbody Hr Ho E1) as [Hr' Ho'].
  unfold lxb_ok in *. rewrite Hl. auto.
Qed.

(* ---------- a frame does not depend on litExtraBuffer's contents ---------- *)

Lemma x_frame_indep (a b: xstate) (s: list Z) (cap: Z) :
  bytes_ok s -> lxb_ok a -> lxb_ok b ->
  match XF a s cap, XF b s cap with
  | None, None => True
  | Some (c1, k1, a'), Some (c2, k2, b') => c1 = c2 /\ k1 = k2 /\ lxb_ok a' /\ lxb_ok b'
  | _, _ => False
  end.
Proof.
  intros Hs Ha Hb.
  exact (x_frame_R xstate (xst_begin xhuf) xblock rb rs rs_begin rb_rs rb_block a b s cap (conj Ha Hb) Hs).
Qed.

Lemma x_series_loop_indep (f: nat) (a b: xstate) (s: list Z) (cap: Z) (out: list Z) :
  bytes_ok s -> lxb_ok a -> lxb_ok b -> XS f a s cap out = XS f b s cap out.
Proof.
  intros Hs Ha Hb.
  exact (x_series_loop_R xstate (xst_begin xhuf) xblock rb rs rs_begin rb_rs rb_block f a b s cap out (conj Ha Hb) Hs).
Qed.

(* ---------- the rest of a one-shot series ---------- *)

(* os_res for the rest t of the input, after the output acc *)
Definition xs_rest (t: list Z) (cap: Z) (acc: list Z) : option (list Z) :=
  XS (S (length t)) (xst_init xhuf) t cap acc.

Lemma os_res_rest (s: list Z) (cap: Z) : os_res s cap = xs_rest s cap nil.
Proof. reflexivity. Qed.

(* the loop ends (fewer than ZSTD_startingInputLength bytes): a success iff nothing is left *)
Lemma xs_rest_end (t: list Z) (cap: Z) (acc: list Z) :
  Zlength t < ZSTD_FRAMEHEADERSIZE_PREFIX -> xs_rest t cap acc = if Zlength t =? 0 then Some acc else None.
Proof.
  intros H. unfold xs_rest. rewrite x_series_loop_S.
  destruct (Z.ltb_spec (Zlength t) ZSTD_FRAMEHEADERSIZE_PREFIX); [reflexivity|lia].
Qed.

(* a skippable frame: readSkippableFrameSize's error, or the rest after it *)
Lemma xs_rest_skip (t: list Z) (cap: Z) (acc: list Z) :
  bytes_ok t -> ZSTD_FRAMEHEADERSIZE_PREFIX <= Zlength t -> is_skippable_magic (le_field t 0 4) = true ->
  xs_rest t cap acc =
  match skippable_frame_size t with
  | None => None
  | Some k => xs_rest (skipn (Z.to_nat k) t) cap acc
  end.
Proof.
  intros Hb Hl Hm. unfold xs_rest. rewrite x_series_loop_S.
  destruct (Z.ltb_spec (Zlength t) ZSTD_FRAMEHEADERSIZE_PREFIX); [lia|]. rewrite Hm.
  destruct (skippable_frame_size t) as [k|] eqn:E; [|reflexivity].
  pose proof (skippable_frame_size_bounds t k Hb E) as Hk. unfold ZSTD_SKIPPABLEHEADERSIZE in Hk.
  apply x_series_loop_fuel; [apply fh_Forall_skipn; exact Hb| |];
    rewrite skipn_length; rewrite Zlength_correct in Hk; lia.
Qed.

(* a Zstandard frame (not skippable), decoded from ANY state st with a full-size litExtraBuffer (the context's, after
   ZSTD_decompressBegin), with the capacity left: its error, or the rest after it *)
Lemma xs_rest_frame (st: xstate) (t: list Z) (cap: Z) (acc: list Z) :
  bytes_ok t -> ZSTD_FRAMEHEADERSIZE_PREFIX <= Zlength t -> is_skippable_magic (le_field t 0 4) = false ->
  lxb_ok st ->
  xs_rest t cap acc =
  match XF st t (cap - Zlength acc) with
  | None => None
  | Some (c, k, _) => xs_rest (skipn (Z.to_nat k) t) cap (acc ++ c)
  end.
Proof.
  intros Hb Hl Hm Hst. unfold xs_rest at 1. rewrite x_series_loop_S.
  destruct (Z.ltb_spec (Zlength t) ZSTD_FRAMEHEADERSIZE_PREFIX); [lia|]. rewrite Hm.
  pose proof (x_frame_indep (xst_init xhuf) st t (cap - Zlength acc) Hb lxb_ok_init Hst) as HF.
  destruct (XF (xst_init xhuf) t _) as [[[c1 k1] a']|] eqn:E1;
    destruct (XF st t _) as [[[c2 k2] b']|]; try contradiction; [|reflexivity].
  destruct HF as (<- & <- & Ha' & _).
  pose proof (x_frame_bounds xstate (xst_begin xhuf) xblock _ _ t c1 _ k1 Hb E1) as Hk.
  unfold xs_rest. rewrite (x_series_loop_indep _ a' (xst_init xhuf) _ _ _ (fh_Forall_skipn _ _ _ Hb) Ha' lxb_ok_init).
  apply x_series_loop_fuel; [apply fh_Forall_skipn; exact Hb| |];
    rewrite skipn_length; rewrite Zlength_correct in Hk; lia.
Qed.

(* the same frame equation with the frame's own unfolding (ExFrameFacts.x_frame_eq, x_fend) left to the caller:
   what ZSTD_decompressFrame's exact claim gives (frame_exact on the tables' state) is enough *)
Lemma xs_rest_frame_res (st: xstate) (t: list Z) (cap: Z) (acc c: list Z) (k: Z) (st': xstate) :
  bytes_ok t -> ZSTD_FRAMEHEADERSIZE_PREFIX <= Zlength t -> is_skippable_magic (le_field t 0 4) = false ->
  lxb_ok st -> XF st t (cap - Zlength acc) = Some (c, k, st') ->
  xs_rest t cap acc = xs_rest (skipn (Z.to_nat k) t) cap (acc ++ c).
Proof. intros Hb Hl Hm Hst E. rewrite (xs_rest_frame st) by assumption. rewrite E. reflexivity. Qed.

Lemma xs_rest_frame_err (st: xstate) (t: list Z) (cap: Z) (acc: list Z) :
  bytes_ok t -> ZSTD_FRAMEHEADERSIZE_PREFIX <= Zlength t -> is_skippable_magic (le_field t 0 4) = false ->
  lxb_ok st -> XF st t (cap - Zlength acc) = None -> xs_rest t cap acc = None.
Proof. intros Hb Hl Hm Hst E. rewrite (xs_rest_frame st) by assumption. rewrite E. reflexivity. Qed.

(* sanity check: the series "skippable frame, raw frame abc" of model/ExFrame.v, through the equations' functions *)
Example xs_rest_skip_raw :
  xs_rest [80; 42; 77; 24; 1; 0; 0; 0; 7; 40; 181; 47; 253; 32; 3; 25; 0; 0; 97; 98; 99] 10 nil = Some [97; 98; 99].
Proof. vm_compute. reflexivity. Qed.
