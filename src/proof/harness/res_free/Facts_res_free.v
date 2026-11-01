(* The abstract states of res_free's context (harness/res_free.c): the invariant main's loop keeps on the context's
   state (Spec_api6.dctx_st), and that every call of the loop keeps it.

   The context has its own allocator (count_alloc, count_free at its opaque pointer); its ghost bound may be raised by
   the calls, the functions and the opaque pointer stay (rf_mem).  No buffer-less frame and no stable output buffer
   are ever begun.  Its dictionary is none, one loaded by copy (DSOwn, sticky) or the harness's DDict q (made from dd,
   by copy); its DDict set is empty or that DDict alone (the harness makes at most one DDict, and references it once).
   The harness's DDict refers to nothing of the caller's, or to its 0-byte copy `kept` (a pointer), which zstd
   compares with its stream buffer (rf_dd). *)
Require Import VST.floyd.proofauto.
Require Export Zstd.proof.zstd.Spec_api6.

(* the context's own allocator is m's, with any bound *)
Definition rf_mem (m: cmem) (st: dctx_st) : Prop :=
  exists m', dc_mem st = Some m' /\ cm_alloc m' = cm_alloc m /\ cm_free m' = cm_free m /\ cm_opaque m' = cm_opaque m.

(* a dictionary loaded by copy *)
Definition own_dict (b: list Z) : dictref := {| dr_src := DSOwn; dr_raw := false; dr_once := false; dr_bytes := b |}.

Definition rf_dict (q: val) (dd: ddict_st) (d: option dictref) : Prop :=
  d = None \/ (exists b, d = Some (own_dict b)) \/ (q <> nullval /\ d = Some (ddict_ref q dd)).

Definition rf_set (q: val) (dd: ddict_st) (l: list (val * ddict_st)) : Prop :=
  l = nil \/ (q <> nullval /\ l = (q, dd) :: nil).

(* the harness's DDict: by copy (dd_ref None), or the 0-byte copy at a pointer *)
Definition rf_dd (q: val) (dd: ddict_st) : Prop :=
  q <> nullval -> dd_ref dd = None \/ (exists p, dd_ref dd = Some p /\ dd_bytes dd = nil /\ isptr p).

Definition rf_inv (m: cmem) (q: val) (dd: ddict_st) (st: dctx_st) : Prop :=
  rf_mem m st /\ dc_bl st = None /\ dc_stable st = false /\ rf_dict q dd (dc_dict st) /\ rf_set q dd (dc_set st) /\
  rf_dd q dd.

(* ---------- the new context ---------- *)

Lemma rf_init m dd : rf_inv m nullval dd (dctx_init_m m).
Proof.
  unfold rf_inv, rf_mem, rf_dict, rf_set, rf_dd; simpl.
  split; [exists m; auto |]. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|].
  intros H; contradiction.
Qed.

(* ---------- the state changes the calls make ---------- *)

Lemma rf_set_ss m q dd st ss : rf_inv m q dd st -> rf_inv m q dd (set_ss st ss).
Proof.
  intros (Hm & Hb & Hs & Hd & Hl & Hq). unfold rf_inv; simpl. repeat split; auto.
  destruct Hm as (m' & E & A & F & O). unfold rf_mem; simpl. rewrite E. simpl.
  eexists; split; [reflexivity |]. simpl. auto.
Qed.

Lemma rf_set_last m q dd st l : rf_inv m q dd st -> rf_inv m q dd (set_last st l).
Proof. intros (Hm & Hb & Hs & Hd & Hl & Hq). unfold rf_inv; simpl. repeat split; auto. Qed.

(* the invariant does not read the exactness flag dc_ex *)
Lemma rf_set_ex m q dd st b : rf_inv m q dd st -> rf_inv m q dd (set_ex st b).
Proof. intros (Hm & Hb & Hs & Hd & Hl & Hq). unfold rf_inv; simpl. repeat split; auto. Qed.

(* ZSTD_decompressDCtx *)
Lemma rf_oneshot m q dd st st' : rf_inv m q dd st -> oneshot_after st st' -> rf_inv m q dd st'.
Proof.
  intros H Ho.
  assert (Hu: forall st0, rf_inv m q dd st0 -> after_use st0 = st0).
  { intros st0 (_ & _ & _ & Hd & _ & _). unfold after_use.
    destruct Hd as [-> | [[b ->] | [_ ->]]]; reflexivity. }
  destruct Ho as [[_ Ha] | [_ Ha]].
  - rewrite (Hu st H) in Ha.
    destruct Ha as [-> | ->]; [apply rf_set_ex; exact H | apply rf_set_last, rf_set_ex; exact H].
  - pose proof (rf_set_ss m q dd st (ss_next (dc_ss st)) H) as H1.
    rewrite (Hu _ H1) in Ha.
    destruct Ha as [-> | ->]; [apply rf_set_ex; exact H1 | apply rf_set_last, rf_set_ex; exact H1].
Qed.

(* ZSTD_decompressStream: the state, whether the stream failed, and the positions and the output cells *)
Lemma rf_stream m q dd st st' r ob osz opos opos' oc oc' ibs isz ipos ipos' :
  rf_inv m q dd st -> stream_post st st' r ob osz opos opos' oc oc' ibs isz ipos ipos' ->
  rf_inv m q dd st' /\ ss_err (dc_ss st') = is_error_code r /\
  opos <= opos' <= osz /\ ipos <= ipos' <= isz /\ Zlength oc' = osz.
Proof.
  intros H Hs.
  destruct Hs as (dl & stall' & a' & Ho & Hi & Hl & _ & _ & _ & _ & _ & _ & _ & -> & _).
  split; [apply rf_set_last, rf_set_ss; exact H | auto].
Qed.

(* ZSTD_DCtx_reset, any directive *)
Lemma rf_reset m q dd st dir r st' : rf_inv m q dd st -> reset_post dir st r st' -> rf_inv m q dd st'.
Proof.
  intros H Hr.
  assert (Hp: forall st0, rf_inv m q dd st0 -> rf_inv m q dd (reset_par st0)).
  { intros st0 (Hm & Hb & Hs & Hd & Hl & Hq). unfold rf_inv, reset_par; simpl.
    split; [exact Hm |]. split; [auto |]. split; [auto |]. split; [left; auto |]. auto. }
  unfold reset_post in Hr.
  destruct (dir =? ZSTD_reset_session_only).
  - destruct Hr as [_ ->]. apply rf_set_ex, rf_set_ss; exact H.
  - destruct (dir =? ZSTD_reset_parameters).
    + destruct Hr as [[_ [_ ->]] | [_ [[_ ->] | (st1 & [_ ->] & ->)]]].
      * apply Hp; exact H.
      * exact H.
      * apply rf_set_ex, Hp, rf_set_ss; exact H.
    + destruct Hr as [_ ->]. apply Hp, rf_set_ss; exact H.
Qed.

(* ZSTD_DCtx_loadDictionary (by copy) *)
Lemma rf_load m q dd st b r st' : rf_inv m q dd st ->
  after_stage (fun st0 r0 st1 => exists om, cm_raised (dc_mem st0) om /\
    load_result (set_mem st0 om) st1 r0 {| dr_src := DSOwn; dr_raw := false; dr_once := false; dr_bytes := b |})
    st r st' ->
  rf_inv m q dd st'.
Proof.
  intros H Ha.
  assert (Hl: forall st0, rf_inv m q dd st0 -> forall r0 st1, (exists om, cm_raised (dc_mem st0) om /\
    load_result (set_mem st0 om) st1 r0 {| dr_src := DSOwn; dr_raw := false; dr_once := false; dr_bytes := b |}) ->
    rf_inv m q dd st1).
  { intros st0 (Hm & Hb & Hs & Hd & Hst & Hq) r0 st1 (om & Hr & Hres).
    destruct Hm as (m' & E & A & F & O). rewrite E in Hr.
    destruct om as [m''|]; [| contradiction]. destruct Hr as (A' & F' & O' & _).
    assert (Hm1: forall d, rf_mem m (set_dict (set_mem st0 (Some m'')) d)).
    { intros d. exists m''. simpl. repeat split; congruence. }
    destruct Hres as [[_ ->] | [_ [-> _]]]; unfold rf_inv; simpl.
    - split; [apply Hm1 |]. repeat split; auto. right; left; exists b; reflexivity.
    - split; [apply Hm1 |]. repeat split; auto. left; reflexivity. }
  destruct Ha as [[_ Ha] | [_ [[_ ->] | Ha]]].
  - exact (Hl st H r st' Ha).
  - exact H.
  - destruct Ha as (st1 & Ha & ->). apply rf_set_ex. exact (Hl _ (rf_set_ss m q dd st _ H) r st1 Ha).
Qed.

(* ZSTD_DCtx_setParameter with a parameter of param_set (refMultipleDDicts, windowLogMax) *)
Lemma rf_setpar m q dd st k v r st' : k <> ZSTD_d_stableOutBuffer -> rf_inv m q dd st ->
  after_stage (setpar_res k v) st r st' -> rf_inv m q dd st'.
Proof.
  intros Hk H Ha.
  assert (Hs: forall st0, rf_inv m q dd st0 -> forall r0 st1, setpar_res k v st0 r0 st1 -> rf_inv m q dd st1).
  { intros st0 H0 r0 st1 Hr. unfold setpar_res in Hr.
    destruct (Z.eqb_spec k ZSTD_d_stableOutBuffer) as [E|_]; [contradiction |].
    destruct (param_set (dc_par st0) k v) as [p'|].
    - destruct Hr as [_ ->]. destruct H0 as (Hm & Hb & Hst & Hd & Hl & Hq). unfold rf_inv; simpl.
      repeat split; auto.
    - destruct Hr as [_ ->]. exact H0. }
  destruct Ha as [[_ Ha] | [_ [[_ ->] | Ha]]].
  - exact (Hs st H r st' Ha).
  - exact H.
  - destruct Ha as (st1 & Ha & ->). apply rf_set_ex. exact (Hs _ (rf_set_ss m q dd st _ H) r st1 Ha).
Qed.

(* the harness makes its DDict (any result q, dd as ZSTD_createDDict gives it) while it has none *)
Lemma rf_new_ddict m dd0 q dd st : rf_inv m nullval dd0 st -> rf_dd q dd -> rf_inv m q dd st /\ dc_set st = nil.
Proof.
  intros (Hm & Hb & Hs & Hd & Hl & _) Hq.
  assert (Hn: dc_set st = nil) by (destruct Hl as [E | [E _]]; [exact E | contradiction]).
  split; [| exact Hn]. unfold rf_inv. repeat split; auto.
  - destruct Hd as [E | [E | [E _]]]; [left; exact E | right; left; exact E | contradiction].
  - left; exact Hn.
Qed.

(* ZSTD_DCtx_refDDict of the harness's DDict (or NULL), into a context with an empty set *)
Lemma rf_ref m q dd st r st' : rf_inv m q dd st -> dc_set st = nil ->
  after_stage (fun st0 r0 st1 =>
    if eq_dec q nullval then r0 = 0 /\ st1 = set_dict st0 None
    else exists om, cm_raised (dc_mem st0) om /\ refddict_result (set_mem st0 om) st1 r0 q dd) st r st' ->
  rf_inv m q dd st'.
Proof.
  intros H Hn Ha.
  assert (Hr: forall st0, rf_inv m q dd st0 -> dc_set st0 = nil -> forall r0 st1,
    (if eq_dec q nullval then r0 = 0 /\ st1 = set_dict st0 None
     else exists om, cm_raised (dc_mem st0) om /\ refddict_result (set_mem st0 om) st1 r0 q dd) ->
    rf_inv m q dd st1).
  { intros st0 H0 Hn0 r0 st1 Hres. destruct H0 as (Hm & Hb & Hst & Hd & Hl & Hq).
    destruct (eq_dec q nullval) as [Eq | Nq].
    - destruct Hres as [_ ->]. unfold rf_inv; simpl. repeat split; auto. left; reflexivity.
    - destruct Hres as (om & Hcm & Hres).
      destruct Hm as (m' & E & A & F & O). rewrite E in Hcm.
      destruct om as [m''|]; [| contradiction]. destruct Hcm as (A' & F' & O' & _).
      assert (Hm1: rf_mem m (set_mem st0 (Some m''))) by (exists m''; simpl; repeat split; congruence).
      unfold refddict_result in Hres. cbn [dc_set set_mem] in Hres. rewrite Hn0 in Hres.
      destruct Hres as [[_ ->] | [_ [_ ->]]]; unfold rf_inv; simpl.
      + split; [exact Hm1 |]. split; [auto |]. split; [auto |]. split; [right; right; auto |].
        split; [| exact Hq].
        destruct (dp_multi (dc_par st0) =? 1); [right; split; [exact Nq | reflexivity] | left; reflexivity].
      + split; [exact Hm1 |]. split; [auto |]. split; [auto |]. split; [right; right; auto |].
        split; [left; exact Hn0 | exact Hq]. }
  destruct Ha as [[_ Ha] | [_ [[_ ->] | Ha]]].
  - exact (Hr st H Hn r st' Ha).
  - exact H.
  - destruct Ha as (st1 & Ha & ->). apply rf_set_ex. exact (Hr _ (rf_set_ss m q dd st _ H) Hn r st1 Ha).
Qed.

(* ---------- no failed stream: ZSTD_decompressStream needs ss_err = false (the harness resets the session after an
   error) ---------- *)

Definition rf_ok (st: dctx_st) : Prop := ss_err (dc_ss st) = false.

Lemma rf_ok_init m : rf_ok (dctx_init_m m).
Proof. reflexivity. Qed.

Lemma rf_ok_set_ex st b : rf_ok st -> rf_ok (set_ex st b).
Proof. exact (fun H => H). Qed.

Lemma rf_ok_next ss : ss_err ss = false -> ss_err (ss_next ss) = false.
Proof. intros E. unfold ss_next. rewrite E. reflexivity. Qed.

(* a function zstd refuses inside a frame, whose effect keeps the stream state *)
Lemma rf_ok_stage (res: dctx_st -> Z -> dctx_st -> Prop) st r st' :
  (forall st0 r0 st1, res st0 r0 st1 -> dc_ss st1 = dc_ss st0) -> rf_ok st -> after_stage res st r st' -> rf_ok st'.
Proof.
  intros Hres Hok Ha. unfold rf_ok in *.
  destruct Ha as [[_ Ha] | [_ [[_ ->] | Ha]]].
  - rewrite (Hres _ _ _ Ha). exact Hok.
  - exact Hok.
  - destruct Ha as (st1 & Ha & ->). simpl. rewrite (Hres _ _ _ Ha). simpl. apply rf_ok_next. exact Hok.
Qed.

Lemma rf_ok_oneshot st st' : rf_ok st -> oneshot_after st st' -> rf_ok st'.
Proof.
  unfold rf_ok. intros Hok Ho.
  assert (Hu: forall st0, dc_ss (after_use st0) = dc_ss st0).
  { intros st0. unfold after_use. destruct (dc_dict st0) as [d|]; [destruct (dr_once d)|]; reflexivity. }
  destruct Ho as [[_ [-> | ->]] | [_ [-> | ->]]]; simpl; rewrite ?Hu; simpl; auto; apply rf_ok_next; exact Hok.
Qed.

Lemma rf_ok_reset dir st r st' : rf_ok st -> reset_post dir st r st' -> rf_ok st'.
Proof.
  intros Hok Hr. unfold reset_post in Hr.
  destruct (dir =? ZSTD_reset_session_only).
  - destruct Hr as [_ ->]. reflexivity.
  - destruct (dir =? ZSTD_reset_parameters).
    + eapply rf_ok_stage; [| exact Hok | exact Hr]. intros st0 r0 st1 [_ ->]. reflexivity.
    + destruct Hr as [_ ->]. reflexivity.
Qed.

Lemma rf_ok_load st b r st' : rf_ok st ->
  after_stage (fun st0 r0 st1 => exists om, cm_raised (dc_mem st0) om /\
    load_result (set_mem st0 om) st1 r0 {| dr_src := DSOwn; dr_raw := false; dr_once := false; dr_bytes := b |})
    st r st' -> rf_ok st'.
Proof.
  intros Hok Ha. eapply rf_ok_stage; [| exact Hok | exact Ha].
  intros st0 r0 st1 (om & _ & [[_ ->] | [_ [-> _]]]); reflexivity.
Qed.

Lemma rf_ok_setpar st k v r st' : rf_ok st -> after_stage (setpar_res k v) st r st' -> rf_ok st'.
Proof.
  intros Hok Ha. eapply rf_ok_stage; [| exact Hok | exact Ha].
  intros st0 r0 st1 Hr. unfold setpar_res in Hr.
  destruct (k =? ZSTD_d_stableOutBuffer).
  - destruct (((0 <=? v) && (v <=? 1))%bool); destruct Hr as [_ ->]; reflexivity.
  - destruct (param_set (dc_par st0) k v); destruct Hr as [_ ->]; reflexivity.
Qed.

Lemma rf_ok_ref q dd st r st' : rf_ok st ->
  after_stage (fun st0 r0 st1 =>
    if eq_dec q nullval then r0 = 0 /\ st1 = set_dict st0 None
    else exists om, cm_raised (dc_mem st0) om /\ refddict_result (set_mem st0 om) st1 r0 q dd) st r st' ->
  rf_ok st'.
Proof.
  intros Hok Ha. eapply rf_ok_stage; [| exact Hok | exact Ha].
  intros st0 r0 st1 Hr. destruct (eq_dec q nullval).
  - destruct Hr as [_ ->]. reflexivity.
  - destruct Hr as (om & _ & [[_ ->] | [_ [_ ->]]]); reflexivity.
Qed.

(* ---------- what the calls require of the state ---------- *)

Lemma rf_set_small m q dd st : rf_inv m q dd st -> Zlength (dc_set st) < 2 ^ 20.
Proof.
  intros (_ & _ & _ & _ & Hl & _). destruct Hl as [-> | [_ ->]]; reflexivity.
Qed.

(* the context's allocator, for ZSTD_freeDCtx's cm_back and for reading the counter *)
Lemma rf_mem_some m q dd st : rf_inv m q dd st ->
  exists m', dc_mem st = Some m' /\ cm_alloc m' = cm_alloc m /\ cm_free m' = cm_free m /\ cm_opaque m' = cm_opaque m.
Proof. intros [H _]. exact H. Qed.
