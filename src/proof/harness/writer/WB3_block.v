(* The body of w_compressed_block in the 3 writer units of API v3.2, whose post also gives decode_block_w (the strict
   dictionary window rule).  Each unit's proof is
   WBlk3_block_<u>.wb3_block_body, in the generated src/proof/harness/<u>/WBlk3_block_<u>.v (the v3
   template WBlk3_block; segment B under the strict rule in WBlk3Defs_<u>, WBlk3_B_<u>, WBlk3_codes_<u>). *)
Require Import VST.floyd.proofauto.
Require Zstd.proof.harness.valid_bufferless.WBlk3_block_valid_bufferless Zstd.proof.harness.valid_dict_api.WBlk3_block_valid_dict_api Zstd.proof.harness.valid_params.WBlk3_block_valid_params.

Theorem wb3_block :
  Zstd.proof.harness.valid_bufferless.WSpecs_valid_bufferless.body_w_compressed_block /\
  Zstd.proof.harness.valid_dict_api.WSpecs_valid_dict_api.body_w_compressed_block /\
  Zstd.proof.harness.valid_params.WSpecs_valid_params.body_w_compressed_block.
Proof.
  exact (conj Zstd.proof.harness.valid_bufferless.WBlk3_block_valid_bufferless.wb3_block_body
          (conj Zstd.proof.harness.valid_dict_api.WBlk3_block_valid_dict_api.wb3_block_body
                Zstd.proof.harness.valid_params.WBlk3_block_valid_params.wb3_block_body)).
Qed.
