(* The writer-internals body group `misc`:
   the body obligations of its functions in the 7 writer units.  Each unit's proof is in the generated
   src/proof/harness/<u>/WB_misc_<u>.v (template WB_misc); this file concludes from them. *)
Require Import VST.floyd.proofauto.
Require Zstd.proof.harness.detect.WSpecs_detect.
Require Zstd.proof.harness.stable_out.WSpecs_stable_out.
Require Zstd.proof.harness.valid_dict.WSpecs_valid_dict.
Require Zstd.proof.harness.valid_dict_copy.WSpecs_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WSpecs_valid_info.
Require Zstd.proof.harness.valid_oneshot.WSpecs_valid_oneshot.
Require Zstd.proof.harness.valid_stream.WSpecs_valid_stream.
Require Zstd.proof.harness.detect.WB_misc_detect.
Require Zstd.proof.harness.stable_out.WB_misc_stable_out.
Require Zstd.proof.harness.valid_dict.WB_misc_valid_dict.
Require Zstd.proof.harness.valid_dict_copy.WB_misc_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WB_misc_valid_info.
Require Zstd.proof.harness.valid_oneshot.WB_misc_valid_oneshot.
Require Zstd.proof.harness.valid_stream.WB_misc_valid_stream.
Require Zstd.proof.harness.writer.WB_misc_pre.
Require Zstd.proof.harness.writer.WB_misc_within.

Theorem wb_misc :
  (Zstd.proof.harness.detect.WSpecs_detect.body_choose /\
   Zstd.proof.harness.detect.WSpecs_detect.body_choose_in /\
   Zstd.proof.harness.detect.WSpecs_detect.body_exact_copy /\
   Zstd.proof.harness.detect.WSpecs_detect.body_ll_code /\
   Zstd.proof.harness.detect.WSpecs_detect.body_ml_code /\
   Zstd.proof.harness.detect.WSpecs_detect.body_fse_rle /\
   Zstd.proof.harness.detect.WSpecs_detect.body_fse_has /\
   Zstd.proof.harness.detect.WSpecs_detect.body_fse_predefined) /\
  (Zstd.proof.harness.stable_out.WSpecs_stable_out.body_choose /\
   Zstd.proof.harness.stable_out.WSpecs_stable_out.body_choose_in /\
   Zstd.proof.harness.stable_out.WSpecs_stable_out.body_exact_copy /\
   Zstd.proof.harness.stable_out.WSpecs_stable_out.body_within_oneshot /\
   Zstd.proof.harness.stable_out.WSpecs_stable_out.body_within_stream /\
   Zstd.proof.harness.stable_out.WSpecs_stable_out.body_stall_error /\
   Zstd.proof.harness.stable_out.WSpecs_stable_out.body_ll_code /\
   Zstd.proof.harness.stable_out.WSpecs_stable_out.body_ml_code /\
   Zstd.proof.harness.stable_out.WSpecs_stable_out.body_fse_rle /\
   Zstd.proof.harness.stable_out.WSpecs_stable_out.body_fse_has /\
   Zstd.proof.harness.stable_out.WSpecs_stable_out.body_fse_predefined) /\
  (Zstd.proof.harness.valid_dict.WSpecs_valid_dict.body_choose /\
   Zstd.proof.harness.valid_dict.WSpecs_valid_dict.body_choose_in /\
   Zstd.proof.harness.valid_dict.WSpecs_valid_dict.body_exact_copy /\
   Zstd.proof.harness.valid_dict.WSpecs_valid_dict.body_within_oneshot /\
   Zstd.proof.harness.valid_dict.WSpecs_valid_dict.body_ll_code /\
   Zstd.proof.harness.valid_dict.WSpecs_valid_dict.body_ml_code /\
   Zstd.proof.harness.valid_dict.WSpecs_valid_dict.body_fse_rle /\
   Zstd.proof.harness.valid_dict.WSpecs_valid_dict.body_fse_has /\
   Zstd.proof.harness.valid_dict.WSpecs_valid_dict.body_fse_predefined) /\
  (Zstd.proof.harness.valid_dict_copy.WSpecs_valid_dict_copy.body_choose /\
   Zstd.proof.harness.valid_dict_copy.WSpecs_valid_dict_copy.body_choose_in /\
   Zstd.proof.harness.valid_dict_copy.WSpecs_valid_dict_copy.body_exact_copy /\
   Zstd.proof.harness.valid_dict_copy.WSpecs_valid_dict_copy.body_within_oneshot /\
   Zstd.proof.harness.valid_dict_copy.WSpecs_valid_dict_copy.body_ll_code /\
   Zstd.proof.harness.valid_dict_copy.WSpecs_valid_dict_copy.body_ml_code /\
   Zstd.proof.harness.valid_dict_copy.WSpecs_valid_dict_copy.body_fse_rle /\
   Zstd.proof.harness.valid_dict_copy.WSpecs_valid_dict_copy.body_fse_has /\
   Zstd.proof.harness.valid_dict_copy.WSpecs_valid_dict_copy.body_fse_predefined) /\
  (Zstd.proof.harness.valid_info.WSpecs_valid_info.body_choose /\
   Zstd.proof.harness.valid_info.WSpecs_valid_info.body_choose_in /\
   Zstd.proof.harness.valid_info.WSpecs_valid_info.body_exact_copy /\
   Zstd.proof.harness.valid_info.WSpecs_valid_info.body_ll_code /\
   Zstd.proof.harness.valid_info.WSpecs_valid_info.body_ml_code /\
   Zstd.proof.harness.valid_info.WSpecs_valid_info.body_fse_rle /\
   Zstd.proof.harness.valid_info.WSpecs_valid_info.body_fse_has /\
   Zstd.proof.harness.valid_info.WSpecs_valid_info.body_fse_predefined) /\
  (Zstd.proof.harness.valid_oneshot.WSpecs_valid_oneshot.body_choose /\
   Zstd.proof.harness.valid_oneshot.WSpecs_valid_oneshot.body_choose_in /\
   Zstd.proof.harness.valid_oneshot.WSpecs_valid_oneshot.body_exact_copy /\
   Zstd.proof.harness.valid_oneshot.WSpecs_valid_oneshot.body_within_oneshot /\
   Zstd.proof.harness.valid_oneshot.WSpecs_valid_oneshot.body_ll_code /\
   Zstd.proof.harness.valid_oneshot.WSpecs_valid_oneshot.body_ml_code /\
   Zstd.proof.harness.valid_oneshot.WSpecs_valid_oneshot.body_fse_rle /\
   Zstd.proof.harness.valid_oneshot.WSpecs_valid_oneshot.body_fse_has /\
   Zstd.proof.harness.valid_oneshot.WSpecs_valid_oneshot.body_fse_predefined) /\
  (Zstd.proof.harness.valid_stream.WSpecs_valid_stream.body_choose /\
   Zstd.proof.harness.valid_stream.WSpecs_valid_stream.body_choose_in /\
   Zstd.proof.harness.valid_stream.WSpecs_valid_stream.body_exact_copy /\
   Zstd.proof.harness.valid_stream.WSpecs_valid_stream.body_within_oneshot /\
   Zstd.proof.harness.valid_stream.WSpecs_valid_stream.body_within_stream /\
   Zstd.proof.harness.valid_stream.WSpecs_valid_stream.body_stall_error /\
   Zstd.proof.harness.valid_stream.WSpecs_valid_stream.body_chunk /\
   Zstd.proof.harness.valid_stream.WSpecs_valid_stream.body_ll_code /\
   Zstd.proof.harness.valid_stream.WSpecs_valid_stream.body_ml_code /\
   Zstd.proof.harness.valid_stream.WSpecs_valid_stream.body_fse_rle /\
   Zstd.proof.harness.valid_stream.WSpecs_valid_stream.body_fse_has /\
   Zstd.proof.harness.valid_stream.WSpecs_valid_stream.body_fse_predefined).
Proof.
  destruct Zstd.proof.harness.writer.WB_misc_pre.wb_misc_pre as (P_detect & P_stable_out & P_valid_dict & P_valid_dict_copy & P_valid_info & P_valid_oneshot & P_valid_stream).
  destruct Zstd.proof.harness.writer.WB_misc_within.wb_misc_within as (W_stable_out_within_oneshot & W_stable_out_within_stream & W_valid_dict_within_oneshot & W_valid_dict_copy_within_oneshot & W_valid_oneshot_within_oneshot & W_valid_stream_within_oneshot & W_valid_stream_within_stream).
  exact (conj (conj Zstd.proof.harness.detect.WB_misc_detect.wb_choose
    (conj Zstd.proof.harness.detect.WB_misc_detect.wb_choose_in
    (conj Zstd.proof.harness.detect.WB_misc_detect.wb_exact_copy
    (conj Zstd.proof.harness.detect.WB_misc_detect.wb_ll_code
    (conj Zstd.proof.harness.detect.WB_misc_detect.wb_ml_code
    (conj Zstd.proof.harness.detect.WB_misc_detect.wb_fse_rle
    (conj Zstd.proof.harness.detect.WB_misc_detect.wb_fse_has
    P_detect)))))))
    (conj (conj Zstd.proof.harness.stable_out.WB_misc_stable_out.wb_choose
    (conj Zstd.proof.harness.stable_out.WB_misc_stable_out.wb_choose_in
    (conj Zstd.proof.harness.stable_out.WB_misc_stable_out.wb_exact_copy
    (conj W_stable_out_within_oneshot
    (conj W_stable_out_within_stream
    (conj Zstd.proof.harness.stable_out.WB_misc_stable_out.wb_stall_error
    (conj Zstd.proof.harness.stable_out.WB_misc_stable_out.wb_ll_code
    (conj Zstd.proof.harness.stable_out.WB_misc_stable_out.wb_ml_code
    (conj Zstd.proof.harness.stable_out.WB_misc_stable_out.wb_fse_rle
    (conj Zstd.proof.harness.stable_out.WB_misc_stable_out.wb_fse_has
    P_stable_out))))))))))
    (conj (conj Zstd.proof.harness.valid_dict.WB_misc_valid_dict.wb_choose
    (conj Zstd.proof.harness.valid_dict.WB_misc_valid_dict.wb_choose_in
    (conj Zstd.proof.harness.valid_dict.WB_misc_valid_dict.wb_exact_copy
    (conj W_valid_dict_within_oneshot
    (conj Zstd.proof.harness.valid_dict.WB_misc_valid_dict.wb_ll_code
    (conj Zstd.proof.harness.valid_dict.WB_misc_valid_dict.wb_ml_code
    (conj Zstd.proof.harness.valid_dict.WB_misc_valid_dict.wb_fse_rle
    (conj Zstd.proof.harness.valid_dict.WB_misc_valid_dict.wb_fse_has
    P_valid_dict))))))))
    (conj (conj Zstd.proof.harness.valid_dict_copy.WB_misc_valid_dict_copy.wb_choose
    (conj Zstd.proof.harness.valid_dict_copy.WB_misc_valid_dict_copy.wb_choose_in
    (conj Zstd.proof.harness.valid_dict_copy.WB_misc_valid_dict_copy.wb_exact_copy
    (conj W_valid_dict_copy_within_oneshot
    (conj Zstd.proof.harness.valid_dict_copy.WB_misc_valid_dict_copy.wb_ll_code
    (conj Zstd.proof.harness.valid_dict_copy.WB_misc_valid_dict_copy.wb_ml_code
    (conj Zstd.proof.harness.valid_dict_copy.WB_misc_valid_dict_copy.wb_fse_rle
    (conj Zstd.proof.harness.valid_dict_copy.WB_misc_valid_dict_copy.wb_fse_has
    P_valid_dict_copy))))))))
    (conj (conj Zstd.proof.harness.valid_info.WB_misc_valid_info.wb_choose
    (conj Zstd.proof.harness.valid_info.WB_misc_valid_info.wb_choose_in
    (conj Zstd.proof.harness.valid_info.WB_misc_valid_info.wb_exact_copy
    (conj Zstd.proof.harness.valid_info.WB_misc_valid_info.wb_ll_code
    (conj Zstd.proof.harness.valid_info.WB_misc_valid_info.wb_ml_code
    (conj Zstd.proof.harness.valid_info.WB_misc_valid_info.wb_fse_rle
    (conj Zstd.proof.harness.valid_info.WB_misc_valid_info.wb_fse_has
    P_valid_info)))))))
    (conj (conj Zstd.proof.harness.valid_oneshot.WB_misc_valid_oneshot.wb_choose
    (conj Zstd.proof.harness.valid_oneshot.WB_misc_valid_oneshot.wb_choose_in
    (conj Zstd.proof.harness.valid_oneshot.WB_misc_valid_oneshot.wb_exact_copy
    (conj W_valid_oneshot_within_oneshot
    (conj Zstd.proof.harness.valid_oneshot.WB_misc_valid_oneshot.wb_ll_code
    (conj Zstd.proof.harness.valid_oneshot.WB_misc_valid_oneshot.wb_ml_code
    (conj Zstd.proof.harness.valid_oneshot.WB_misc_valid_oneshot.wb_fse_rle
    (conj Zstd.proof.harness.valid_oneshot.WB_misc_valid_oneshot.wb_fse_has
    P_valid_oneshot))))))))
    (conj Zstd.proof.harness.valid_stream.WB_misc_valid_stream.wb_choose
    (conj Zstd.proof.harness.valid_stream.WB_misc_valid_stream.wb_choose_in
    (conj Zstd.proof.harness.valid_stream.WB_misc_valid_stream.wb_exact_copy
    (conj W_valid_stream_within_oneshot
    (conj W_valid_stream_within_stream
    (conj Zstd.proof.harness.valid_stream.WB_misc_valid_stream.wb_stall_error
    (conj Zstd.proof.harness.valid_stream.WB_misc_valid_stream.wb_chunk
    (conj Zstd.proof.harness.valid_stream.WB_misc_valid_stream.wb_ll_code
    (conj Zstd.proof.harness.valid_stream.WB_misc_valid_stream.wb_ml_code
    (conj Zstd.proof.harness.valid_stream.WB_misc_valid_stream.wb_fse_rle
    (conj Zstd.proof.harness.valid_stream.WB_misc_valid_stream.wb_fse_has
    P_valid_stream))))))))))))))))).
Qed.
