(* oversizedDuration stays far below its size_t range on the exact stream model's reached states (model/Exact.v's
   instance of model/ExStream.v): it counts the frames in a row whose needs are 3 times smaller than the buffers
   (ZSTD_DCtx_updateOversizedDuration, zstd_decompress.c 2061-2072); from ZSTD_WORKSPACETOOLARGE_MAXDURATION (128) on,
   every such frame reallocates the buffers to its exact needs, so beyond 128 each further step needs buffers 3 times
   smaller than the last ones, which are at least 4 bytes and below 2^32: the count stays below 128 + 21.  The proof of
   ZSTD_decompressStream needs it to read the model's `zs_over + 1` back from zstd's `oversizedDuration++`.
   zinv_x_over: every state satisfying the fuel invariant ExStreamFacts.zinv_x satisfies it. *)
Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Zstd.proof.model.ExStream Zstd.proof.model.ExStreamFacts.
Require Zstd.proof.model.Exact.
Local Open Scope Z_scope.

(* ExStreamFacts.zi_over, the last part of zinv: beyond 128, (inBuffSize + outBuffSize) * 3 ^ (over - 128) <= 2^32
   with inBuffSize + outBuffSize >= 4, so over - 128 < 33 *)
Lemma zinv_x_over (z: zstate_x) : zinv_x z -> 0 <= zs_over Exact.xstate z < 2 ^ 32.
Proof.
  intros (_ & _ & _ & _ & O1 & O2 & O3). unfold ZS_WORKSPACETOOLARGE_MAXDURATION in O3.
  split; [exact O2|].
  destruct (Z.lt_ge_cases (zs_over Exact.xstate z) 128) as [Hl|Hl]; [lia|].
  destruct (O3 Hl) as [O4 O5].
  destruct (Z.lt_ge_cases (zs_over Exact.xstate z - 128) 33) as [Hk|Hk]; [lia|].
  assert (3 ^ 33 <= 3 ^ (zs_over Exact.xstate z - 128)) by (apply Z.pow_le_mono_r; lia).
  nia.
Qed.
