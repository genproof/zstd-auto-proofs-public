(* A call of ZSTD_decompressStream as the exact stream model sees it: the input bytes zstd may read
   (ibs[ipos..isz)) and the output room (osz - opos).  Plain Coq. *)
Require Import Coq.ZArith.ZArith Coq.Lists.List.

Definition zcall : Type := (list Z * Z)%type.
