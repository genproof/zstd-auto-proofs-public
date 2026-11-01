(* The specification of stream_all (harness/frames.h), once for all the laws that include frames.h.

   stream_all(zds, src, len, dst, cap, &written, &completed) gives src[0..len-1] to ZSTD_decompressStream in
   any pieces with any output room in dst[0..cap-1] (at least a byte of each while any is left), until a call
   returns an error, or 0 with all of src read, or anything else having read and written nothing.  Its
   specification is the trace of its calls: each call is one instance of ZSTD_decompressStream's
   specification (Spec_api6.stream_post) for the buffer sizes the loop chose, the calls before the last
   satisfy the loop's condition to go on, the last one does not.  A law argues on stream_post (and the
   claims of StreamModel.v) call by call, by induction on the trace.

   The loop's state between two calls (sa_state): the context's abstract state, in.pos, out.pos, the cells
   of dst and the number of calls that returned 0 so far (the value of *completed).  The context is in the default
   (buffered) output mode: stream_all changes out.size from call to call, which ZSTD_d_stableOutBuffer
   forbids.  Like the kit's other specifications, this one is stated at any compspecs cs (the byte arrays,
   the two size_t results); the decoder's own resources (DC, the dictionaries) are those of its API. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Export Zstd.proof.zstd.Spec_api6.
Require Export Zstd.proof.harness.frames.FSpecs.
Require Zstd.harness.api_split_invariant.code.

Local Open Scope logic.

Definition _stream_all : ident := Zstd.harness.api_split_invariant.code._stream_all.
Definition f_stream_all := Zstd.harness.api_split_invariant.code.f_stream_all.

(* the loop's state before a call: the context's state, in.pos, out.pos, dst's cells, *completed *)
Record sa_state := { sa_st : dctx_st; sa_ipos : Z; sa_opos : Z; sa_out : list val; sa_done : Z }.

(* the state when the loop starts *)
Definition sa_init (st: dctx_st) (oc: list val) : sa_state :=
  {| sa_st := st; sa_ipos := 0; sa_opos := 0; sa_out := oc; sa_done := 0 |}.

(* the sizes the loop gives a call: in.size = len when all input is read, else in (in.pos, len]; the same for
   out.size with cap *)
Definition sa_size (pos n sz: Z) : Prop := if pos =? n then sz = n else pos < sz <= n.

(* one call of the loop, from x to y, with the result r: the input buffer is src[0..isz-1] at in.pos
   sa_ipos x, the output buffer dst[0..osz-1] at out.pos sa_opos x; the call's claims (stream_post) and its
   progress claim (stream_progress: when a call may read and write nothing); the call leaves its output cells
   oc' in dst[0..osz-1] (the rest of dst untouched) and counts a 0 return *)
Definition stream_call (s: list Z) (cap: Z) (dst: val) (x: sa_state) (r: Z) (y: sa_state) : Prop :=
  exists isz osz oc',
    sa_size (sa_ipos x) (Zlength s) isz /\ sa_size (sa_opos x) cap osz /\
    0 <= r <= Int64.max_unsigned /\
    stream_post (sa_st x) (sa_st y) r dst osz (sa_opos x) (sa_opos y) (sublist 0 osz (sa_out x)) oc'
      (sublist 0 isz s) isz (sa_ipos x) (sa_ipos y) /\
    stream_progress (sa_st x) (sa_st y) r osz (sa_opos x) (sa_opos y) isz (sa_ipos x) (sa_ipos y) (sublist 0 isz s) /\
    sa_out y = oc' ++ sublist osz cap (sa_out x) /\
    sa_done y = sa_done x + (if r =? 0 then 1 else 0).

(* the loop's condition to call again after the call x -> y returned r (len = the input's length): no error,
   and either 0 with input left, or something else with some input read or some output written *)
Definition stream_more (len: Z) (x: sa_state) (r: Z) (y: sa_state) : Prop :=
  is_error_code r = false /\
  (if r =? 0 then sa_ipos y < len else sa_ipos y <> sa_ipos x \/ sa_opos y <> sa_opos x).

(* the calls before the last one: from x to y, each followed by the condition to go on *)
Inductive stream_run (s: list Z) (cap: Z) (dst: val) : sa_state -> sa_state -> Prop :=
| stream_run_nil x : stream_run s cap dst x x
| stream_run_snoc x y r z :
    stream_run s cap dst x y -> stream_call s cap dst y r z -> stream_more (Zlength s) y r z ->
    stream_run s cap dst x z.

Section Spec.
Context {cs: compspecs}.
Variable DC : globals -> val -> dctx_st -> mpred.
Variable DD : globals -> val -> ddict_st -> mpred.

(* stream_all(zds, src, len, dst, cap, written, completed) on a context in the state st (no error left, not
   in stable output mode, a dictionary a stream may use), src: the len defined bytes s, dst: any cap cells
   (witnesses W for buffers of 0 bytes, as ZSTD_decompressStream asks).  Returns the last call's result r:
   the calls make a run from the start to y, then the last call y -> z, after which the loop stops;
   *written = z's out.pos, *completed = the number of calls that returned 0, dst holds z's cells and the
   context is in z's state. *)
Definition stream_all_spec : ident * funspec :=
  DECLARE _stream_all
  WITH W: list ptr_witness, gv: globals, d: val, st: dctx_st,
       shs: share, src: val, s: list Z, shd: share, dst: val, cap: Z, oc: list val,
       shw: share, wp: val, shc: share, cp: val
  PRE [ tptr t_dctx, tptr tuchar, tulong, tptr tuchar, tulong, tptr tulong, tptr tulong ]
    PROP (dc_stable st = false; ss_err (dc_ss st) = false; stream_dict_ok W st;
          buf_ok W shs (Zlength s) src; buf_ok W shd cap dst;
          readable_share shs; writable_share shd; writable_share shw; writable_share shc;
          Zlength s <= 2 ^ 63 - 1; bytes_ok s; 0 <= cap <= 2 ^ 63 - 1; Zlength oc = cap)
    PARAMS (d; src; Vlong (Int64.repr (Zlength s)); dst; Vlong (Int64.repr cap); wp; cp) GLOBALS (gv)
    SEP (pws_pred W; mem_mgr gv; zstd_globals gv; DC gv d st;
         dict_res DD gv Ews (dc_dict st); set_res DD gv Ews (dc_set st) (dc_dict st);
         @data_at cs shs (tarray tuchar (Zlength s)) (zbytes s) src;
         @data_at cs shd (tarray tuchar cap) oc dst;
         @data_at_ cs shw tulong wp; @data_at_ cs shc tulong cp)
  POST [ tulong ]
    EX r: Z, EX y: sa_state, EX z: sa_state,
    PROP (stream_run s cap dst (sa_init st oc) y; stream_call s cap dst y r z; ~ stream_more (Zlength s) y r z)
    RETURN (Vlong (Int64.repr r))
    SEP (pws_pred W; mem_mgr gv; zstd_globals gv; DC gv d (sa_st z);
         dict_res DD gv Ews (dc_dict st); set_res DD gv Ews (dc_set st) (dc_dict st);
         @data_at cs shs (tarray tuchar (Zlength s)) (zbytes s) src;
         @data_at cs shd (tarray tuchar cap) (sa_out z) dst;
         @data_at cs shw tulong (Vlong (Int64.repr (sa_opos z))) wp;
         @data_at cs shc tulong (Vlong (Int64.repr (sa_done z))) cp).

(* what stream_all calls *)
Definition G_stream_all : funspecs :=
  [Zstd.proof.zstd.Spec_util.ZSTD_isError_spec; ZSTD_decompressStream_spec DC DD; upto_spec].

End Spec.
