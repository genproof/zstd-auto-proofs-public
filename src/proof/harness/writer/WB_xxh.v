(* The writer-internals body group `xxh`:
   the body obligations of its functions in the 7 writer units.  Each unit's proof is in the generated
   src/proof/harness/<u>/WB_xxh_<u>.v (template WB_xxh); this file concludes from them. *)
Require Import VST.floyd.proofauto.
Require Zstd.proof.harness.detect.WSpecs_detect.
Require Zstd.proof.harness.stable_out.WSpecs_stable_out.
Require Zstd.proof.harness.valid_dict.WSpecs_valid_dict.
Require Zstd.proof.harness.valid_dict_copy.WSpecs_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WSpecs_valid_info.
Require Zstd.proof.harness.valid_oneshot.WSpecs_valid_oneshot.
Require Zstd.proof.harness.valid_stream.WSpecs_valid_stream.
Require Zstd.proof.harness.detect.WB_xxh_detect.
Require Zstd.proof.harness.stable_out.WB_xxh_stable_out.
Require Zstd.proof.harness.valid_dict.WB_xxh_valid_dict.
Require Zstd.proof.harness.valid_dict_copy.WB_xxh_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WB_xxh_valid_info.
Require Zstd.proof.harness.valid_oneshot.WB_xxh_valid_oneshot.
Require Zstd.proof.harness.valid_stream.WB_xxh_valid_stream.

Theorem wb_xxh :
  (Zstd.proof.harness.detect.WSpecs_detect.body_xrotl /\
   Zstd.proof.harness.detect.WSpecs_detect.body_xread /\
   Zstd.proof.harness.detect.WSpecs_detect.body_xround /\
   Zstd.proof.harness.detect.WSpecs_detect.body_xmerge /\
   Zstd.proof.harness.detect.WSpecs_detect.body_xxh64) /\
  (Zstd.proof.harness.stable_out.WSpecs_stable_out.body_xrotl /\
   Zstd.proof.harness.stable_out.WSpecs_stable_out.body_xread /\
   Zstd.proof.harness.stable_out.WSpecs_stable_out.body_xround /\
   Zstd.proof.harness.stable_out.WSpecs_stable_out.body_xmerge /\
   Zstd.proof.harness.stable_out.WSpecs_stable_out.body_xxh64) /\
  (Zstd.proof.harness.valid_dict.WSpecs_valid_dict.body_xrotl /\
   Zstd.proof.harness.valid_dict.WSpecs_valid_dict.body_xread /\
   Zstd.proof.harness.valid_dict.WSpecs_valid_dict.body_xround /\
   Zstd.proof.harness.valid_dict.WSpecs_valid_dict.body_xmerge /\
   Zstd.proof.harness.valid_dict.WSpecs_valid_dict.body_xxh64) /\
  (Zstd.proof.harness.valid_dict_copy.WSpecs_valid_dict_copy.body_xrotl /\
   Zstd.proof.harness.valid_dict_copy.WSpecs_valid_dict_copy.body_xread /\
   Zstd.proof.harness.valid_dict_copy.WSpecs_valid_dict_copy.body_xround /\
   Zstd.proof.harness.valid_dict_copy.WSpecs_valid_dict_copy.body_xmerge /\
   Zstd.proof.harness.valid_dict_copy.WSpecs_valid_dict_copy.body_xxh64) /\
  (Zstd.proof.harness.valid_info.WSpecs_valid_info.body_xrotl /\
   Zstd.proof.harness.valid_info.WSpecs_valid_info.body_xread /\
   Zstd.proof.harness.valid_info.WSpecs_valid_info.body_xround /\
   Zstd.proof.harness.valid_info.WSpecs_valid_info.body_xmerge /\
   Zstd.proof.harness.valid_info.WSpecs_valid_info.body_xxh64) /\
  (Zstd.proof.harness.valid_oneshot.WSpecs_valid_oneshot.body_xrotl /\
   Zstd.proof.harness.valid_oneshot.WSpecs_valid_oneshot.body_xread /\
   Zstd.proof.harness.valid_oneshot.WSpecs_valid_oneshot.body_xround /\
   Zstd.proof.harness.valid_oneshot.WSpecs_valid_oneshot.body_xmerge /\
   Zstd.proof.harness.valid_oneshot.WSpecs_valid_oneshot.body_xxh64) /\
  (Zstd.proof.harness.valid_stream.WSpecs_valid_stream.body_xrotl /\
   Zstd.proof.harness.valid_stream.WSpecs_valid_stream.body_xread /\
   Zstd.proof.harness.valid_stream.WSpecs_valid_stream.body_xround /\
   Zstd.proof.harness.valid_stream.WSpecs_valid_stream.body_xmerge /\
   Zstd.proof.harness.valid_stream.WSpecs_valid_stream.body_xxh64).
Proof.
  exact (conj (conj Zstd.proof.harness.detect.WB_xxh_detect.body_xrotl_ok
     (conj Zstd.proof.harness.detect.WB_xxh_detect.body_xread_ok
     (conj Zstd.proof.harness.detect.WB_xxh_detect.body_xround_ok
     (conj Zstd.proof.harness.detect.WB_xxh_detect.body_xmerge_ok
           Zstd.proof.harness.detect.WB_xxh_detect.body_xxh64_ok))))
  (conj (conj Zstd.proof.harness.stable_out.WB_xxh_stable_out.body_xrotl_ok
     (conj Zstd.proof.harness.stable_out.WB_xxh_stable_out.body_xread_ok
     (conj Zstd.proof.harness.stable_out.WB_xxh_stable_out.body_xround_ok
     (conj Zstd.proof.harness.stable_out.WB_xxh_stable_out.body_xmerge_ok
           Zstd.proof.harness.stable_out.WB_xxh_stable_out.body_xxh64_ok))))
  (conj (conj Zstd.proof.harness.valid_dict.WB_xxh_valid_dict.body_xrotl_ok
     (conj Zstd.proof.harness.valid_dict.WB_xxh_valid_dict.body_xread_ok
     (conj Zstd.proof.harness.valid_dict.WB_xxh_valid_dict.body_xround_ok
     (conj Zstd.proof.harness.valid_dict.WB_xxh_valid_dict.body_xmerge_ok
           Zstd.proof.harness.valid_dict.WB_xxh_valid_dict.body_xxh64_ok))))
  (conj (conj Zstd.proof.harness.valid_dict_copy.WB_xxh_valid_dict_copy.body_xrotl_ok
     (conj Zstd.proof.harness.valid_dict_copy.WB_xxh_valid_dict_copy.body_xread_ok
     (conj Zstd.proof.harness.valid_dict_copy.WB_xxh_valid_dict_copy.body_xround_ok
     (conj Zstd.proof.harness.valid_dict_copy.WB_xxh_valid_dict_copy.body_xmerge_ok
           Zstd.proof.harness.valid_dict_copy.WB_xxh_valid_dict_copy.body_xxh64_ok))))
  (conj (conj Zstd.proof.harness.valid_info.WB_xxh_valid_info.body_xrotl_ok
     (conj Zstd.proof.harness.valid_info.WB_xxh_valid_info.body_xread_ok
     (conj Zstd.proof.harness.valid_info.WB_xxh_valid_info.body_xround_ok
     (conj Zstd.proof.harness.valid_info.WB_xxh_valid_info.body_xmerge_ok
           Zstd.proof.harness.valid_info.WB_xxh_valid_info.body_xxh64_ok))))
  (conj (conj Zstd.proof.harness.valid_oneshot.WB_xxh_valid_oneshot.body_xrotl_ok
     (conj Zstd.proof.harness.valid_oneshot.WB_xxh_valid_oneshot.body_xread_ok
     (conj Zstd.proof.harness.valid_oneshot.WB_xxh_valid_oneshot.body_xround_ok
     (conj Zstd.proof.harness.valid_oneshot.WB_xxh_valid_oneshot.body_xmerge_ok
           Zstd.proof.harness.valid_oneshot.WB_xxh_valid_oneshot.body_xxh64_ok))))
  (conj Zstd.proof.harness.valid_stream.WB_xxh_valid_stream.body_xrotl_ok
     (conj Zstd.proof.harness.valid_stream.WB_xxh_valid_stream.body_xread_ok
     (conj Zstd.proof.harness.valid_stream.WB_xxh_valid_stream.body_xround_ok
     (conj Zstd.proof.harness.valid_stream.WB_xxh_valid_stream.body_xmerge_ok
           Zstd.proof.harness.valid_stream.WB_xxh_valid_stream.body_xxh64_ok)))))))))).
Qed.
