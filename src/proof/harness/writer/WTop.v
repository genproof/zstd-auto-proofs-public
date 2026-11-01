(* The writer's top-level interface, unit-independent part (plain Coq).
   The functions the harness mains call (w_series, w_dict, choose, choose_in, exact_copy, within_oneshot,
   within_stream, stall_error, chunk) are specified per unit in src/proof/harness/<u>/WTopSpecs_<u>.v,
   generated from the v2 template WTopSpecs; the pure parts are here. *)
Require Export Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Series Zstd.proof.model.WriterFacts Zstd.proof.model.StreamModel.
Local Open Scope bool_scope.

(* the range of every field of winfo_t (unsigned 32 bits, size_t / unsigned long long 64 bits) *)
Definition u32 (z: Z) : Prop := 0 <= z < 2 ^ 32.
Definition u64 (z: Z) : Prop := 0 <= z < 2 ^ 64.

Definition winfo_wf (f: winfo) : Prop :=
  u32 (wi_variant f) /\ u64 (wi_start f) /\ u64 (wi_size f) /\ u64 (wi_cstart f) /\ u64 (wi_csize f) /\
  u64 (wi_fcs f) /\ u32 (wi_did_size f) /\ u32 (wi_did f) /\ u64 (wi_window f) /\ u32 (wi_window_log f) /\
  u32 (wi_blocks f) /\ u64 (wi_skip_n f) /\ u64 (wi_hsize f).

(* fields of a skippable frame that winfo_t does not hold are 0 (the struct starts zeroed), and so are the
   fields of a Zstandard frame that only skippable frames have *)
Definition winfo_zeros (f: winfo) : Prop :=
  if wi_skippable f then
    wi_fcs_present f = false /\ wi_fcs f = 0 /\ wi_did_size f = 0 /\ wi_did f = 0 /\ wi_single f = false /\
    wi_window f = 0 /\ wi_window_log f = 0 /\ wi_checksum f = false /\ wi_blocks f = 0 /\
    wi_uses_dict f = false
  else wi_variant f = 0 /\ wi_skip_n f = 0.

(* a Zstandard frame with a checksum: header, at least one block header, the 4-byte checksum (series_facts says
   nothing of it for a frame beyond zstd's window range) *)
Definition winfo_layout (f: winfo) : Prop :=
  wi_skippable f = false -> wi_checksum f = true -> wi_hsize f + 7 <= wi_size f.

Definition wseries_wf (ws: wseries) : Prop :=
  Forall winfo_wf (ws_frames ws) /\ Forall winfo_zeros (ws_frames ws) /\ Forall winfo_layout (ws_frames ws).

Definition wdict_wf (wd: wdict) : Prop :=
  u32 (wd_id wd) /\ Zlength (wd_content wd) <= Zlength (wd_bytes wd) /\
  wd_content wd = skipn (Z.to_nat (Zlength (wd_bytes wd) - Zlength (wd_content wd))) (wd_bytes wd).

(* the all-zero frame record (the frames of winfo_t f[] past nframes) *)
Definition winfo0 : winfo :=
  {| wi_skippable := false; wi_variant := 0; wi_start := 0; wi_size := 0; wi_cstart := 0; wi_csize := 0;
     wi_fcs_present := false; wi_fcs := 0; wi_did_size := 0; wi_did := 0; wi_single := false; wi_window := 0;
     wi_window_log := 0; wi_checksum := false; wi_blocks := 0; wi_skip_n := 0; wi_hsize := 0;
     wi_uses_dict := false |}.

(* zlimits.h within_oneshot / within_stream *)
Definition within_oneshot_b (fs: list winfo) : bool := forallb (fun f => negb (wi_big f)) fs.

Definition within_stream_b (fs: list winfo) : bool :=
  forallb (fun f => wi_skippable f || (wi_window f <=? 2 ^ 27)) fs && within_oneshot_b fs.

(* zlimits.h stall_error(e, stalled, in, out, opos0), in = {_, isz, ipos}, out = {_, osz, opos} *)
Definition NO_PROGRESS_MAX : Z := 16.

Definition stall_error_b (e stalled ipos isz opos osz opos0: Z) : bool :=
  if (stalled + 1 <? NO_PROGRESS_MAX) || negb (ipos =? 0) || negb (opos =? opos0) then false
  else if e =? ZSTD_error_noForwardProgress_destFull then opos =? osz
  else (e =? ZSTD_error_noForwardProgress_inputEmpty) && (opos <? osz) && (ipos =? isz).
