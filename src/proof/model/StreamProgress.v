(* The format model: when a call of ZSTD_decompressStream may make no progress (plain Coq).

   stream_progress_m md sel dm wl sin0 sout0 sall stall' r ipos ipos' isz opos opos' osz is a claim on one call
   that returns r, neither an error nor progress (in.pos and out.pos unchanged: ipos' = ipos, opos' = opos):
   - r = 0: all the call's input was read (ipos = isz), or zstd's count of calls without progress restarts
     (stall' = 0, the stream state's ss_stall after the call);
   - r <> 0: the input was all read (ipos = isz) or the output is full (opos = osz); and for every series s
     that extends sall (the bytes read, then the unread rest of the call's input) and that the model decodes
     with the window limit wl (series_frames_m ... wl s ends at TEnd), with content c:
       * the output is full and some of c is not delivered yet (zstd holds it, |sout0| < |c|), or
       * the input was all read, and s is longer than sall (its next bytes are not in the call), or
         everything of s was read (|s| <= |sin0|, sin0 the bytes read before the call, the hostage byte
         included) and delivered (|c| <= |sout0|) before the call.
   A caller that offers one more byte of input and one more byte of room in every call therefore never sees a
   positive return without progress on a series the model decodes, and a return of 0 without progress never
   counts towards zstd's no-progress errors (StreamModel.stall_ok) while it has input left. *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Series.
Require Import Zstd.proof.model.StreamModel Zstd.proof.model.Params.
Require Import Coq.ZArith.ZArith Coq.Lists.List.
Local Open Scope Z_scope.

Definition stream_progress_m (md: dmode) (sel: Z -> option dict_model) (dm: option dict_model) (wl: Z)
    (sin0 sout0 sall: list Z) (stall' r ipos ipos' isz opos opos' osz: Z) : Prop :=
  is_error_code r = false -> ipos' = ipos -> opos' = opos ->
  (r = 0 -> ipos = isz \/ stall' = 0) /\
  (r <> 0 ->
     (ipos = isz \/ opos = osz) /\
     forall s, bytes_ok s -> is_prefix sall s -> snd (series_frames_m md sel dm wl s) = TEnd ->
       let c := flat_map fr_content (fst (series_frames_m md sel dm wl s)) in
       (opos = osz /\ Zlength sout0 < Zlength c) \/
       (ipos = isz /\
        (Zlength sall < Zlength s \/ (Zlength s <= Zlength sin0 /\ Zlength c <= Zlength sout0)))).
