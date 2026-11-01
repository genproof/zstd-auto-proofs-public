(* The format model: what streaming decompression (ZSTD_decompressStream) promises on a series of frames,
   stated on the bytes a stream has read (sin) and delivered (sout) since its last reset.  Plain Coq.

   stream_claims sin sall sout ocap r, for every series s the bytes read are a prefix of, with
   (fl0, t0) = Series.series_frames no_dict no_wlim s (the model without a window limit: zstd's
   single-pass shortcut decodes any window) and (fl, t) = series_frames no_dict stream_wlim s:
   - content: sout is a prefix of the content of fl0, when fl0 ends the series (t0 = TEnd) or a frame
     zstd rejects at its header (t0 = TDetHdr: nothing of that frame is delivered);
   - zero returns: a 0 return means sin ends exactly at the end of the n-th frame of fl0 (n >= 1) and
     sout is the content of the first n frames, whenever t0 <> TUnk;
   - hints: when t0 = TEnd or TDetHdr and the call did not start with everything of s read (sin0) and
     delivered (sout0) (zstd then asks for a next frame's header), a positive return asks for at most the
     rest of the current frame (at least 1 while something is left to read or deliver; once the call has read
     and delivered everything, at most a1, the bytes read ahead: 1 with the hostage byte held, else 0);
   - errors, for every s that also extends sall (the bytes read and the unread rest of the call's input:
     zstd may read bad bytes without counting them) with t = TEnd: memory, zstd's guard against calls
     that make no progress, or any error when the stable output buffer (ocap = Some its size) cannot
     hold the series' content.  Every claim is for byte strings s (bytes_ok s). *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Series.
Local Open Scope bool_scope.

Definition ZSTD_error_memory_allocation : Z := 64.
Definition ZSTD_error_noForwardProgress_destFull : Z := 80.
Definition ZSTD_error_noForwardProgress_inputEmpty : Z := 82.
Definition ZSTD_NO_FORWARD_PROGRESS_MAX : Z := 16.
Definition ZSTD_error_dstSize_tooSmall : Z := 70.

(* an error code that is not one of zstd's no-progress guard (only ZSTD_decompressStream returns those) *)
Definition dec_err (r: Z) : Prop :=
  is_error_code r = true /\ r <> 2 ^ 64 - ZSTD_error_noForwardProgress_destFull /\
  r <> 2 ^ 64 - ZSTD_error_noForwardProgress_inputEmpty.

Definition fr_end (f: frec) : Z := fr_start f + fr_size f.

(* the end of the current frame: the first frame that ends after ipos, or ends at ipos with content not
   yet all delivered (got = bytes delivered); dflt if none (harness/valid_stream.c computes the same) *)
Fixpoint cur_end_aux (fl: list frec) (ipos got cacc dflt: Z) : Z :=
  match fl with
  | nil => dflt
  | f :: fl' =>
      let c := cacc + Zlength (fr_content f) in
      if (fr_end f >? ipos) || ((fr_end f =? ipos) && (got <? c)) then fr_end f
      else cur_end_aux fl' ipos got c dflt
  end.

Definition cur_end (fl: list frec) (ipos got dflt: Z) : Z := cur_end_aux fl ipos got 0 dflt.

Definition is_prefix (p l: list Z) : Prop := firstn (length p) l = p.

(* the bytes read so far can still begin a byte series whose frames the model decodes up to its end
   or up to a frame zstd rejects at its header (no window limit) *)
Definition stream_alive (sin: list Z) : Prop :=
  exists s, bytes_ok s /\ is_prefix sin s /\
    (snd (series_frames no_dict no_wlim s) = TEnd \/ snd (series_frames no_dict no_wlim s) = TDetHdr).

Definition fr_dflt : frec := {| fr_start := 0; fr_size := 0; fr_content := nil; fr_skippable := false |}.

Definition stream_claims (sin0 sout0 sin sall sout: list Z) (a1: Z) (ocap: option Z) (r: Z) : Prop :=
  forall s, bytes_ok s -> is_prefix sin s ->
  let fl0 := fst (series_frames no_dict no_wlim s) in
  let t0 := snd (series_frames no_dict no_wlim s) in
  let fl := fst (series_frames no_dict stream_wlim s) in
  let t := snd (series_frames no_dict stream_wlim s) in
  (t0 = TEnd \/ t0 = TDetHdr -> is_prefix sout (flat_map fr_content fl0)) /\
  (r = 0 -> t0 <> TUnk ->
     exists n, (1 <= n <= length fl0)%nat /\
       Zlength sin = fr_end (nth (n - 1) fl0 fr_dflt) /\
       sout = flat_map fr_content (firstn n fl0)) /\
  (t0 = TEnd \/ t0 = TDetHdr -> is_error_code r = false -> 0 < r ->
     (Zlength sin0 < Zlength s \/ Zlength sout0 < Zlength (flat_map fr_content fl0)) ->
     r <= Z.max (if (Zlength sin <? Zlength s) || (Zlength sout <? Zlength (flat_map fr_content fl0)) then 1 else a1)
                (cur_end fl0 (Zlength sin) (Zlength sout) (Zlength s) - Zlength sin)) /\
  (is_prefix sall s -> t = TEnd -> is_error_code r = true -> forall e, r = 2 ^ 64 - e ->
     e = ZSTD_error_memory_allocation \/ e = ZSTD_error_noForwardProgress_destFull \/
     e = ZSTD_error_noForwardProgress_inputEmpty \/
     (exists osz, ocap = Some osz /\ osz < Zlength (flat_map fr_content fl))).

(* zstd's no-progress guard: an error of this kind only on the 16th call in a row that read and wrote
   nothing (stall = the earlier ones), destFull iff the output is full, else inputEmpty with all input read *)
Definition stall_ok (r stall ipos ipos' isz opos opos' osz: Z) : Prop :=
  (r = 2 ^ 64 - ZSTD_error_noForwardProgress_destFull \/ r = 2 ^ 64 - ZSTD_error_noForwardProgress_inputEmpty) ->
  stall + 1 >= ZSTD_NO_FORWARD_PROGRESS_MAX /\ ipos' = ipos /\ opos' = opos /\
  ((r = 2 ^ 64 - ZSTD_error_noForwardProgress_destFull /\ opos' = osz) \/
   (r = 2 ^ 64 - ZSTD_error_noForwardProgress_inputEmpty /\ opos' < osz /\ ipos' = isz)).
