(* FS3 streaming: the epilogue of ZSTD_decompressStream, the hint's size (plain Coq). *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Block Zstd.proof.model.Series Zstd.proof.model.StreamModel Zstd.proof.model.Params.
Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Export Zstd.proof.dec.v3.FS.stream.S3ModelDefs.
Import ListNotations.
Local Open Scope Z_scope.

(* the bytes of the current frame zstd asks for (ZSTD_decompressStream's hint: expected, plus the next block
   header after a block that is not the last, minus what is already loaded) *)
Definition fp_rem (fp: fprog) : Z :=
  match fp with
  | FP_skip hdr got => le_field hdr 4 4 - got
  | FP_zstd _ z =>
      match zp_ph z with
      | ZP_bhdr => ZSTD_blockHeaderSize - Zlength (zp_got z)
      | ZP_body bh =>
          match cblock_size bh with Some c => c | None => 0 end - Zlength (zp_got z) +
          (if bp_last (block_props_of bh) =? 1 then 0 else ZSTD_blockHeaderSize)
      | ZP_ck => 4 - Zlength (zp_got z)
      | ZP_end => 0
      end
  | _ => 0
  end.
