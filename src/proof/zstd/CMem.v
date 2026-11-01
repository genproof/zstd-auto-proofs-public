(* A decompression context with its own allocator (ZSTD_customMem, given to ZSTD_createDCtx_advancedP; the laws
   res_memory_oneshot, res_memory_stream, res_free).  The allocator belongs to the law's harness: the decoder calls
   its two functions through the pointers it was given, so their specifications are stated here over two abstract
   predicates the law chooses (the class cmem_preds):

     CM o B h : the allocator's state at its opaque pointer o, h bytes given out, B a bound on h;
     CB o p n : what freeing the n-byte block p it gave out needs, besides the block's bytes.

   An allocation is only made when h + n <= B: the bound is the law's claim (zstd.h's ZSTD_estimate* functions).
   B is a ghost: zstd never sees it; a context records it (Spec_api6.dc_mem) and raises it to the streaming
   estimate of its window limit when it starts streaming (cm_raise), which a peak counter allows (CM_mono). *)
Require Export Zstd.proof.zstd.Gprog.
Require Import Zstd.proof.model.Frame.
Local Open Scope logic.

(* the allocator of a context: ZSTD_customMem's three fields, and the bound *)
Record cmem := { cm_alloc : val; cm_free : val; cm_opaque : val; cm_bound : Z }.

(* the value of a ZSTD_customMem holding it *)
Definition cmem_val (m: cmem) : reptype (Tstruct ___gp_ZSTD_customMem noattr) :=
  (cm_alloc m, (cm_free m, cm_opaque m)).

Class cmem_preds := {
  CM : val -> Z -> Z -> mpred;
  CB : val -> val -> Z -> mpred;
  CM_mono : forall o B B' h, B <= B' -> CM o B h |-- CM o B' h }.

(* the predicates of a law whose contexts all have the default allocator: no context of its own allocator
   exists (CM is never satisfied), so no specification says anything about one.  Of the lowest priority: a law
   with its own allocator declares its instance *)
Lemma cmem_none_mono : forall (o: val) (B B' h: Z), B <= B' -> (FF: mpred) |-- FF.
Proof. intros. apply derives_refl. Qed.

#[export] Instance cmem_none : cmem_preds | 1000 :=
  {| CM := fun _ _ _ => FF; CB := fun _ _ _ => FF; CM_mono := cmem_none_mono |}.

Section CMem.
Context {CMI: cmem_preds}.

(* customAlloc(opaque, n): NULL, or a block of n bytes (n a size_t), aligned as malloc's *)
Definition cm_alloc_spec : funspec :=
  WITH o: val, B: Z, h: Z, n: Z
  PRE [ tptr tvoid, tulong ]
    PROP (0 <= h; 0 <= n <= Int64.max_unsigned; h + n <= B)
    PARAMS (o; Vlong (Int64.repr n))
    SEP (CM o B h)
  POST [ tptr tvoid ]
    EX p: val,
    PROP (p = nullval \/ malloc_compatible n p)
    RETURN (p)
    SEP (if eq_dec p nullval then CM o B h else CM o B (h + n) * CB o p n * memory_block Ews n p).

(* customFree(opaque, p) of a block it gave out (zstd never frees NULL through it) *)
Definition cm_free_spec : funspec :=
  WITH o: val, B: Z, h: Z, p: val, n: Z
  PRE [ tptr tvoid, tptr tvoid ]
    PROP (0 <= n <= h)
    PARAMS (o; p)
    SEP (CM o B h; CB o p n; memory_block Ews n p)
  POST [ tvoid ]
    PROP () RETURN () SEP (CM o B (h - n)).

(* the allocator's two functions *)
Definition cm_funs (m: cmem) : mpred :=
  func_ptr' cm_alloc_spec (cm_alloc m) * func_ptr' cm_free_spec (cm_free m).

(* ---------- a context's allocator, own or default (am = None: malloc, calloc, free) ---------- *)

(* the ZSTD_customMem value: { NULL, NULL, NULL } for the default allocator *)
Definition cmem_v (am: option cmem) : reptype (Tstruct ___gp_ZSTD_customMem noattr) :=
  match am with None => (nullval, (nullval, nullval)) | Some m => cmem_val m end.

(* what a call through the allocator needs besides its ZSTD_customMem: for its own allocator, the two functions
   and its state with h bytes given out; nothing for the default one *)
Definition cm_have (am: option cmem) (h: Z) : mpred :=
  match am with None => emp | Some m => cm_funs m * CM (cm_opaque m) (cm_bound m) h end.

(* room for n more bytes *)
Definition cm_room (am: option cmem) (h n: Z) : Prop :=
  match am with None => True | Some m => 0 <= h /\ 0 <= n /\ h + n <= cm_bound m end.

(* a block of type t at q it gave out may be freed (it is part of the h bytes) *)
Definition cm_held (am: option cmem) (h: Z) (t: type) : Prop :=
  match am with None => True | Some m => 0 <= sizeof t <= h end.

(* what freeing the block of type t at q needs besides its bytes: malloc's token, or CB *)
Definition blk_tok (am: option cmem) (t: type) (q: val) : mpred :=
  match am with None => malloc_token Ews t q | Some m => CB (cm_opaque m) q (sizeof t) end.

(* the fields of a ZSTD_customMem are pointers or NULL (each is loaded and stored by ZSTD_customMem_copy) *)
Definition cmem_ok (am: option cmem) : Prop :=
  match am with
  | None => True
  | Some m => is_pointer_or_null (cm_alloc m) /\ is_pointer_or_null (cm_free m) /\ is_pointer_or_null (cm_opaque m)
  end.

End CMem.

(* ---------- the estimates ---------- *)

Definition dctx_size : Z := sizeof (Tstruct _ZSTD_DCtx_s noattr).

(* ZSTD_estimateDStreamSize(w): the context, an input buffer of one block (MIN(w, ZSTD_BLOCKSIZE_MAX)) and the
   output buffer ZSTD_decodingBufferSize_min(w, ZSTD_CONTENTSIZE_UNKNOWN) = w + 2 * block + 2 * WILDCOPY_OVERLENGTH
   (32); exact for w <= 2^63 (size_t arithmetic wraps beyond, as Int64.repr of this sum) *)
Definition dstream_size (w: Z) : Z := dctx_size + 3 * Z.min w ZSTD_BLOCKSIZE_MAX + w + 64.

(* the bound of a context's own allocator once it streams with the window limit w *)
Definition cm_raise (om: option cmem) (w: Z) : option cmem :=
  match om with
  | None => None
  | Some m => Some {| cm_alloc := cm_alloc m; cm_free := cm_free m; cm_opaque := cm_opaque m;
                      cm_bound := Z.max (cm_bound m) (dstream_size w) |}
  end.

Lemma dctx_size_eq : dctx_size = 95976.
Proof. reflexivity. Qed.

(* The stream buffers zstd allocates for a frame fit in the estimate of the window limit: in zdss_loadHeader the
   window ws (at least ZSTD_WINDOWSIZE_ABSMIN = 1024) is checked against maxWindowSize = wmax first; the buffer is
   MAX(bsm, 4) input bytes (bsm the frame's block size, at most MIN(ws, ZSTD_BLOCKSIZE_MAX)) and, in buffered mode,
   MIN(fcs, ws + 2 * MIN(MIN(ws, ZSTD_BLOCKSIZE_MAX), bsm) + 64) output bytes
   (ZSTD_decodingBufferSize_internal), 0 in stable mode. *)
Lemma stream_bufs_fit : forall ws fcs bsm wmax (stable: bool),
  1024 <= ws <= wmax -> 0 <= bsm <= Z.min ws ZSTD_BLOCKSIZE_MAX -> 0 <= fcs ->
  Z.max bsm 4 + (if stable then 0 else Z.min fcs (ws + Z.min (Z.min ws ZSTD_BLOCKSIZE_MAX) bsm * 2 + 64))
    <= dstream_size wmax - dctx_size.
Proof.
  intros ws fcs bsm wmax stable Hw Hb Hf. unfold dstream_size, ZSTD_BLOCKSIZE_MAX in *.
  destruct stable; lia.
Qed.

Lemma cm_raise_none : forall w, cm_raise None w = None.
Proof. reflexivity. Qed.

Lemma cm_raise_bound : forall m w,
  cm_raise (Some m) w = Some {| cm_alloc := cm_alloc m; cm_free := cm_free m; cm_opaque := cm_opaque m;
                                cm_bound := Z.max (cm_bound m) (dstream_size w) |}.
Proof. reflexivity. Qed.

Lemma cm_raise_idem : forall om w, cm_raise (cm_raise om w) w = cm_raise om w.
Proof.
  intros [m|] w; [| reflexivity]. unfold cm_raise; simpl. f_equal. f_equal. lia.
Qed.

(* raising the bound changes neither the ZSTD_customMem value nor what a block's free needs *)
Lemma cmem_v_raise : forall om w, cmem_v (cm_raise om w) = cmem_v om.
Proof. intros [m|] w; reflexivity. Qed.

Lemma cmem_ok_raise : forall om w, cmem_ok (cm_raise om w) <-> cmem_ok om.
Proof. intros [m|] w; reflexivity. Qed.

Lemma blk_tok_raise {CMI: cmem_preds} : forall om w t q, blk_tok (cm_raise om w) t q = blk_tok om t q.
Proof. intros [m|] w t q; reflexivity. Qed.

(* ... and the allocator's state with h bytes given out holds for the raised bound (CM_mono) *)
Lemma cm_have_raise {CMI: cmem_preds} : forall om w h, cm_have om h |-- cm_have (cm_raise om w) h.
Proof.
  intros [m|] w h; simpl; [| apply derives_refl].
  apply sepcon_derives; [apply derives_refl | apply CM_mono; lia].
Qed.

(* ---------- the specifications of the estimates (API; exported by Spec_api6) ---------- *)

Definition ZSTD_estimateDCtxSize_spec : ident * funspec :=
  DECLARE _ZSTD_estimateDCtxSize
  WITH u: unit
  PRE [ ]
    PROP () PARAMS () SEP ()
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr dctx_size)) SEP ().

(* any window limit up to 2^40 (zstd's are at most 2^31, ZSTD_WINDOWLOG_MAX) *)
Definition ZSTD_estimateDStreamSize_spec : ident * funspec :=
  DECLARE _ZSTD_estimateDStreamSize
  WITH w: Z
  PRE [ tulong ]
    PROP (0 <= w <= 2 ^ 40) PARAMS (Vlong (Int64.repr w)) SEP ()
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr (dstream_size w))) SEP ().

(* ---------- the same allocator, any bound ---------- *)

(* two descriptions of one allocator (the same functions and opaque pointer; the ghost bounds may differ): a DDict a
   context made keeps the bound of that time, the context's own may be raised later *)
Definition cm_same (om om': option cmem) : Prop :=
  match om, om' with
  | None, None => True
  | Some m, Some m' => cm_alloc m = cm_alloc m' /\ cm_free m = cm_free m' /\ cm_opaque m = cm_opaque m'
  | _, _ => False
  end.

Lemma cm_same_refl : forall om, cm_same om om.
Proof. intros [m|]; simpl; auto. Qed.

Lemma cm_same_sym : forall om om', cm_same om om' -> cm_same om' om.
Proof. intros [m|] [m'|]; simpl; intuition. Qed.

Lemma cm_same_trans : forall om om' om'', cm_same om om' -> cm_same om' om'' -> cm_same om om''.
Proof. intros [m|] [m'|] [m''|]; simpl; intuition congruence. Qed.

Lemma cm_same_raise : forall om w, cm_same om (cm_raise om w).
Proof. intros [m|] w; simpl; auto. Qed.

Lemma cmem_v_same : forall om om', cm_same om om' -> cmem_v om = cmem_v om'.
Proof.
  intros [m|] [m'|]; simpl; try contradiction; auto.
  intros (E1 & E2 & E3). unfold cmem_val. rewrite E1, E2, E3. reflexivity.
Qed.

Lemma cmem_ok_same : forall om om', cm_same om om' -> cmem_ok om -> cmem_ok om'.
Proof.
  intros [m|] [m'|]; simpl; try contradiction; auto.
  intros (E1 & E2 & E3). rewrite E1, E2, E3. auto.
Qed.

Lemma blk_tok_same {CMI: cmem_preds} : forall om om' t q, cm_same om om' -> blk_tok om t q = blk_tok om' t q.
Proof.
  intros [m|] [m'|] t q; simpl; try contradiction; auto.
  intros (_ & _ & E3). rewrite E3. reflexivity.
Qed.
