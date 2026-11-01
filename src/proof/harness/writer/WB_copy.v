(* The writer-internals body group `copy`:
   the body obligations of its functions in the 7 writer units.  Each unit's proof is in the generated
   src/proof/harness/<u>/WB_copy_<u>.v (template WB_copy); this file concludes from them. *)
Require Import VST.floyd.proofauto.
Require Zstd.proof.harness.detect.WSpecs_detect.
Require Zstd.proof.harness.stable_out.WSpecs_stable_out.
Require Zstd.proof.harness.valid_dict.WSpecs_valid_dict.
Require Zstd.proof.harness.valid_dict_copy.WSpecs_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WSpecs_valid_info.
Require Zstd.proof.harness.valid_oneshot.WSpecs_valid_oneshot.
Require Zstd.proof.harness.valid_stream.WSpecs_valid_stream.
Require Zstd.proof.harness.detect.WB_copy_detect.
Require Zstd.proof.harness.stable_out.WB_copy_stable_out.
Require Zstd.proof.harness.valid_dict.WB_copy_valid_dict.
Require Zstd.proof.harness.valid_dict_copy.WB_copy_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WB_copy_valid_info.
Require Zstd.proof.harness.valid_oneshot.WB_copy_valid_oneshot.
Require Zstd.proof.harness.valid_stream.WB_copy_valid_stream.

Theorem wb_copy :
  (Zstd.proof.harness.detect.WSpecs_detect.body_fse_copy /\
   Zstd.proof.harness.detect.WSpecs_detect.body_huf_copy /\
   Zstd.proof.harness.detect.WSpecs_detect.body_wstate_copy) /\
  (Zstd.proof.harness.stable_out.WSpecs_stable_out.body_fse_copy /\
   Zstd.proof.harness.stable_out.WSpecs_stable_out.body_huf_copy /\
   Zstd.proof.harness.stable_out.WSpecs_stable_out.body_wstate_copy) /\
  (Zstd.proof.harness.valid_dict.WSpecs_valid_dict.body_fse_copy /\
   Zstd.proof.harness.valid_dict.WSpecs_valid_dict.body_huf_copy /\
   Zstd.proof.harness.valid_dict.WSpecs_valid_dict.body_wstate_copy) /\
  (Zstd.proof.harness.valid_dict_copy.WSpecs_valid_dict_copy.body_fse_copy /\
   Zstd.proof.harness.valid_dict_copy.WSpecs_valid_dict_copy.body_huf_copy /\
   Zstd.proof.harness.valid_dict_copy.WSpecs_valid_dict_copy.body_wstate_copy) /\
  (Zstd.proof.harness.valid_info.WSpecs_valid_info.body_fse_copy /\
   Zstd.proof.harness.valid_info.WSpecs_valid_info.body_huf_copy /\
   Zstd.proof.harness.valid_info.WSpecs_valid_info.body_wstate_copy) /\
  (Zstd.proof.harness.valid_oneshot.WSpecs_valid_oneshot.body_fse_copy /\
   Zstd.proof.harness.valid_oneshot.WSpecs_valid_oneshot.body_huf_copy /\
   Zstd.proof.harness.valid_oneshot.WSpecs_valid_oneshot.body_wstate_copy) /\
  (Zstd.proof.harness.valid_stream.WSpecs_valid_stream.body_fse_copy /\
   Zstd.proof.harness.valid_stream.WSpecs_valid_stream.body_huf_copy /\
   Zstd.proof.harness.valid_stream.WSpecs_valid_stream.body_wstate_copy).
Proof.
  exact
    (conj (conj Zstd.proof.harness.detect.WB_copy_detect.body_fse_copy_ok (conj Zstd.proof.harness.detect.WB_copy_detect.body_huf_copy_ok Zstd.proof.harness.detect.WB_copy_detect.body_wstate_copy_ok))
    (conj (conj Zstd.proof.harness.stable_out.WB_copy_stable_out.body_fse_copy_ok (conj Zstd.proof.harness.stable_out.WB_copy_stable_out.body_huf_copy_ok Zstd.proof.harness.stable_out.WB_copy_stable_out.body_wstate_copy_ok))
    (conj (conj Zstd.proof.harness.valid_dict.WB_copy_valid_dict.body_fse_copy_ok (conj Zstd.proof.harness.valid_dict.WB_copy_valid_dict.body_huf_copy_ok Zstd.proof.harness.valid_dict.WB_copy_valid_dict.body_wstate_copy_ok))
    (conj (conj Zstd.proof.harness.valid_dict_copy.WB_copy_valid_dict_copy.body_fse_copy_ok (conj Zstd.proof.harness.valid_dict_copy.WB_copy_valid_dict_copy.body_huf_copy_ok Zstd.proof.harness.valid_dict_copy.WB_copy_valid_dict_copy.body_wstate_copy_ok))
    (conj (conj Zstd.proof.harness.valid_info.WB_copy_valid_info.body_fse_copy_ok (conj Zstd.proof.harness.valid_info.WB_copy_valid_info.body_huf_copy_ok Zstd.proof.harness.valid_info.WB_copy_valid_info.body_wstate_copy_ok))
    (conj (conj Zstd.proof.harness.valid_oneshot.WB_copy_valid_oneshot.body_fse_copy_ok (conj Zstd.proof.harness.valid_oneshot.WB_copy_valid_oneshot.body_huf_copy_ok Zstd.proof.harness.valid_oneshot.WB_copy_valid_oneshot.body_wstate_copy_ok))
    (conj Zstd.proof.harness.valid_stream.WB_copy_valid_stream.body_fse_copy_ok (conj Zstd.proof.harness.valid_stream.WB_copy_valid_stream.body_huf_copy_ok Zstd.proof.harness.valid_stream.WB_copy_valid_stream.body_wstate_copy_ok)))))))).
Qed.
