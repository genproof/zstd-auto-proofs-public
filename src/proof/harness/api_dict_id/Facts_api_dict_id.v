(* The model facts of the law api_dict_id (harness/api_dict_id.c), in plain Coq: what the model's
   ZSTD_getDictID_fromFrame (Info.dict_id_from_frame) returns on the two inputs the harness builds, a frame of
   new_frame (frames.h) or a skippable frame of new_skippable, each followed by any bytes. *)
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Info.
Require Import Zstd.proof.harness.frames.FModel Zstd.proof.harness.frames.FFacts Zstd.proof.harness.frames.FSeries.
Local Open Scope Z_scope.

(* a frame of new_frame (a window up to maxw < 2^32, e.g. ONE_CALL_WINDOW = 2^31) carries its Dictionary_ID:
   zstd reads a frame of type 0 whose header has the ID did (or no ID field when did = 0) *)
Lemma dict_id_new_frame : forall d fcs maxw did c rest,
  nf_ok (Zlength d) fcs maxw did c -> 0 <= fcs < 2 ^ 64 -> 0 <= did < 2 ^ 32 -> maxw < 2 ^ 32 ->
  dict_id_from_frame (nf_bytes d fcs did c ++ rest) = did.
Proof.
  intros d fcs maxw did c rest Hok Hfcs Hdid Hm.
  assert (Hw: nh_wlog_ok (nc_hdr c)) by (apply (nf_wlog_ok fcs maxw did); [apply Hok | exact Hm]).
  unfold dict_id_from_frame. rewrite (nf_get_frame_header d fcs maxw did c rest Hok Hfcs Hdid Hw).
  reflexivity.
Qed.

(* a skippable frame has no Dictionary_ID: zstd reads a frame of type 1 and returns 0 *)
Lemma dict_id_skippable : forall k u rest, 0 <= k < 16 -> Zlength u < 2 ^ 32 ->
  dict_id_from_frame (sk_bytes k u ++ rest) = 0.
Proof.
  intros k u rest Hk Hu. unfold dict_id_from_frame. rewrite (sk_get_frame_header k u rest Hk Hu).
  reflexivity.
Qed.
