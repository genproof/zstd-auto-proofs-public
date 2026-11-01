(* The writer-internals body group `bits`:
   the body obligations of its functions in the 7 writer units.  Each unit's proof is in the generated
   src/proof/harness/<u>/WB_bits_<u>.v (template WB_bits); this file concludes from them. *)
Require Import VST.floyd.proofauto.
Require Zstd.proof.harness.detect.WSpecs_detect.
Require Zstd.proof.harness.stable_out.WSpecs_stable_out.
Require Zstd.proof.harness.valid_dict.WSpecs_valid_dict.
Require Zstd.proof.harness.valid_dict_copy.WSpecs_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WSpecs_valid_info.
Require Zstd.proof.harness.valid_oneshot.WSpecs_valid_oneshot.
Require Zstd.proof.harness.valid_stream.WSpecs_valid_stream.
Require Zstd.proof.harness.detect.WB_bits_detect.
Require Zstd.proof.harness.stable_out.WB_bits_stable_out.
Require Zstd.proof.harness.valid_dict.WB_bits_valid_dict.
Require Zstd.proof.harness.valid_dict_copy.WB_bits_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WB_bits_valid_info.
Require Zstd.proof.harness.valid_oneshot.WB_bits_valid_oneshot.
Require Zstd.proof.harness.valid_stream.WB_bits_valid_stream.

Theorem wb_bits :
  (Zstd.proof.harness.detect.WSpecs_detect.body_highbit /\
   Zstd.proof.harness.detect.WSpecs_detect.body_put8 /\
   Zstd.proof.harness.detect.WSpecs_detect.body_put_le /\
   Zstd.proof.harness.detect.WSpecs_detect.body_put_bytes /\
   Zstd.proof.harness.detect.WSpecs_detect.body_bits_put /\
   Zstd.proof.harness.detect.WSpecs_detect.body_bits_end_mark /\
   Zstd.proof.harness.detect.WSpecs_detect.body_bits_pad) /\
  (Zstd.proof.harness.stable_out.WSpecs_stable_out.body_highbit /\
   Zstd.proof.harness.stable_out.WSpecs_stable_out.body_put8 /\
   Zstd.proof.harness.stable_out.WSpecs_stable_out.body_put_le /\
   Zstd.proof.harness.stable_out.WSpecs_stable_out.body_put_bytes /\
   Zstd.proof.harness.stable_out.WSpecs_stable_out.body_bits_put /\
   Zstd.proof.harness.stable_out.WSpecs_stable_out.body_bits_end_mark /\
   Zstd.proof.harness.stable_out.WSpecs_stable_out.body_bits_pad) /\
  (Zstd.proof.harness.valid_dict.WSpecs_valid_dict.body_highbit /\
   Zstd.proof.harness.valid_dict.WSpecs_valid_dict.body_put8 /\
   Zstd.proof.harness.valid_dict.WSpecs_valid_dict.body_put_le /\
   Zstd.proof.harness.valid_dict.WSpecs_valid_dict.body_put_bytes /\
   Zstd.proof.harness.valid_dict.WSpecs_valid_dict.body_bits_put /\
   Zstd.proof.harness.valid_dict.WSpecs_valid_dict.body_bits_end_mark /\
   Zstd.proof.harness.valid_dict.WSpecs_valid_dict.body_bits_pad) /\
  (Zstd.proof.harness.valid_dict_copy.WSpecs_valid_dict_copy.body_highbit /\
   Zstd.proof.harness.valid_dict_copy.WSpecs_valid_dict_copy.body_put8 /\
   Zstd.proof.harness.valid_dict_copy.WSpecs_valid_dict_copy.body_put_le /\
   Zstd.proof.harness.valid_dict_copy.WSpecs_valid_dict_copy.body_put_bytes /\
   Zstd.proof.harness.valid_dict_copy.WSpecs_valid_dict_copy.body_bits_put /\
   Zstd.proof.harness.valid_dict_copy.WSpecs_valid_dict_copy.body_bits_end_mark /\
   Zstd.proof.harness.valid_dict_copy.WSpecs_valid_dict_copy.body_bits_pad) /\
  (Zstd.proof.harness.valid_info.WSpecs_valid_info.body_highbit /\
   Zstd.proof.harness.valid_info.WSpecs_valid_info.body_put8 /\
   Zstd.proof.harness.valid_info.WSpecs_valid_info.body_put_le /\
   Zstd.proof.harness.valid_info.WSpecs_valid_info.body_put_bytes /\
   Zstd.proof.harness.valid_info.WSpecs_valid_info.body_bits_put /\
   Zstd.proof.harness.valid_info.WSpecs_valid_info.body_bits_end_mark /\
   Zstd.proof.harness.valid_info.WSpecs_valid_info.body_bits_pad) /\
  (Zstd.proof.harness.valid_oneshot.WSpecs_valid_oneshot.body_highbit /\
   Zstd.proof.harness.valid_oneshot.WSpecs_valid_oneshot.body_put8 /\
   Zstd.proof.harness.valid_oneshot.WSpecs_valid_oneshot.body_put_le /\
   Zstd.proof.harness.valid_oneshot.WSpecs_valid_oneshot.body_put_bytes /\
   Zstd.proof.harness.valid_oneshot.WSpecs_valid_oneshot.body_bits_put /\
   Zstd.proof.harness.valid_oneshot.WSpecs_valid_oneshot.body_bits_end_mark /\
   Zstd.proof.harness.valid_oneshot.WSpecs_valid_oneshot.body_bits_pad) /\
  (Zstd.proof.harness.valid_stream.WSpecs_valid_stream.body_highbit /\
   Zstd.proof.harness.valid_stream.WSpecs_valid_stream.body_put8 /\
   Zstd.proof.harness.valid_stream.WSpecs_valid_stream.body_put_le /\
   Zstd.proof.harness.valid_stream.WSpecs_valid_stream.body_put_bytes /\
   Zstd.proof.harness.valid_stream.WSpecs_valid_stream.body_bits_put /\
   Zstd.proof.harness.valid_stream.WSpecs_valid_stream.body_bits_end_mark /\
   Zstd.proof.harness.valid_stream.WSpecs_valid_stream.body_bits_pad).
Proof.
  exact (conj Zstd.proof.harness.detect.WB_bits_detect.wb_bits_detect
        (conj Zstd.proof.harness.stable_out.WB_bits_stable_out.wb_bits_stable_out
        (conj Zstd.proof.harness.valid_dict.WB_bits_valid_dict.wb_bits_valid_dict
        (conj Zstd.proof.harness.valid_dict_copy.WB_bits_valid_dict_copy.wb_bits_valid_dict_copy
        (conj Zstd.proof.harness.valid_info.WB_bits_valid_info.wb_bits_valid_info
        (conj Zstd.proof.harness.valid_oneshot.WB_bits_valid_oneshot.wb_bits_valid_oneshot
              Zstd.proof.harness.valid_stream.WB_bits_valid_stream.wb_bits_valid_stream)))))).
Qed.
