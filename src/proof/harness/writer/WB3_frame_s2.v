(* Segment 2 of w_frame's body (bmax, the decoder state,
   the dictionary content, fi->uses_dict, hn) in the 3 writer units of API v3, with the dictionary argument wdarg
   (WAExt: valid_dict_api mode 2).  Each unit's proof is in the generated
   src/proof/harness/<u>/WB_frame_s2p_<u>.v (v3 template WB_frame_s2p, from the template WB_frame_s2p). *)
Require Import VST.floyd.proofauto.
Require Zstd.proof.harness.valid_bufferless.WB3S2_valid_bufferless.
Require Zstd.proof.harness.valid_dict_api.WB3S2_valid_dict_api.
Require Zstd.proof.harness.valid_params.WB3S2_valid_params.

Theorem wb3_frame_s2 :
  Zstd.proof.harness.valid_bufferless.WB_frame_defs_valid_bufferless.wf_seg2_stmt /\
  Zstd.proof.harness.valid_dict_api.WB_frame_defs_valid_dict_api.wf_seg2_stmt /\
  Zstd.proof.harness.valid_params.WB_frame_defs_valid_params.wf_seg2_stmt.
Proof.
  exact (conj Zstd.proof.harness.valid_bufferless.WB3S2_valid_bufferless.wf_seg2
          (conj Zstd.proof.harness.valid_dict_api.WB3S2_valid_dict_api.wf_seg2
                Zstd.proof.harness.valid_params.WB3S2_valid_params.wf_seg2)).
Qed.
