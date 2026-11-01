(* The error codes of one-shot decoding, as the API specifications state them (Spec_api6: ZSTD_decompress,
   ZSTD_decompressDCtx).  The model's side is model/ErrCodes.v.

   oneshot_codes md sel cur s cap r: a one-shot decoding of the series s under the mode md, with the dictionary
   selection sel and the dictionary cur before the first frame, into a capacity cap, that returned r:
   - refused by a frame's Content_Checksum (series_ck_m, c: everything decoded up to that checksum), with room
     for c: ZSTD_error_checksum_wrong;
   - a series the model decodes to c with only Raw and RLE blocks (series_rr_m), with less room than c:
     ZSTD_error_dstSize_tooSmall;
   in both cases ZSTD_error_memory_allocation is also possible (ZSTD_decompress allocates its context). *)
Require Export Zstd.proof.zstd.Spec_util.
Require Export Zstd.proof.model.ErrCodes.
Require Import Zstd.proof.model.Series Zstd.proof.model.StreamModel Zstd.proof.model.Params.

Definition oneshot_codes (md: dmode) (sel: Z -> option dict_model) (cur: option dict_model) (s: list Z)
    (cap r: Z) : Prop :=
  (forall c, series_ck_m md sel no_wlim cur s c -> Zlength c <= cap ->
     r = err_code ZSTD_error_checksum_wrong \/ r = err_code ZSTD_error_memory_allocation) /\
  (forall c, series_rr_m md sel no_wlim cur s c -> cap < Zlength c ->
     r = err_code ZSTD_error_dstSize_tooSmall \/ r = err_code ZSTD_error_memory_allocation).

(* a memory error satisfies both *)
Lemma oneshot_codes_mem: forall md sel cur s cap,
  oneshot_codes md sel cur s cap (err_code ZSTD_error_memory_allocation).
Proof. intros. split; intros; right; reflexivity. Qed.
