(* What the decoder unit (patch/decoder.c) provides to the assembly.

   ZstdOK Int: Int is the unit's list of specifications:
   - one entry per internal function of the unit, plus memcpy (the unit's only VST-external, with the
     environment's memcpy_spec), no duplicates;
   - every internal function satisfies its entry in the context Zstd_Imports ++ Int (Layer.body_ok).
   Which specifications Int holds is the decoder's choice; the API that the harnesses import
   (Spec_api6.Specs_api) must follow from them (api_sub: each API function has a specification in Int
   that is a funspec_sub of its API specification; stated in the top-level theorem). *)
Require Export Zstd.proof.zstd.Layer.

Definition zstd_ids : list ident := _memcpy :: IntIDs Zstd.units.Zstd.qp.

Definition ZstdOK (Int: funspecs) : Prop :=
  NoDup (map fst Int) /\
  (forall i, In i (map fst Int) <-> In i zstd_ids) /\
  initial_world.find_id _memcpy Int = Some (snd memcpy_spec) /\
  Forall (fun ix => fst ix <> _memcpy -> body_ok (Zstd_Imports ++ Int) ix) Int.

(* every specification of API is implied (funspec_sub) by the specification of the same function in Int *)
Definition api_sub (API Int: funspecs) : Prop :=
  Forall (fun e => exists s, initial_world.find_id (fst e) Int = Some s /\ funspec_sub s (snd e)) API.
