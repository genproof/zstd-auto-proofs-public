(* The harness obligation of rj_bad_checksum (harness/rj_bad_checksum.c): for ANY predicates DC, DD of the
   decoder's API (Spec_api6), with the API [ZSTD_isError; ZSTD_getErrorCode; ZSTD_decompress; ZSTD_createDStream;
   ZSTD_decompressStream; ZSTD_XXH64] (the last for new_frame's checksums), the helpers of laws_common.h and
   frames.h (proved once in the frames kit) and main satisfy their specifications.

   main builds a frame of new_frame with a Content_Checksum and replaces the checksum by another value
   (Facts_rj_bad_checksum.bad_frame).  One-shot: the model refuses this series by its checksum after the frame's
   content (series_ck_m), so ZSTD_decompress's error codes (Spec_codes.oneshot_codes) give
   ZSTD_error_checksum_wrong when the capacity holds the content, unless memory ran out.  Streamed: the model's
   walk over the series finds no complete frame (TDetCk), so no call of stream_all returns 0
   (FStreamNoEnd.stream_no_end) and *completed stays 0.  The buffers have any size up to PTRDIFF_MAX: this needs
   the one-shot and streaming specifications with sizes up to 2 ^ 63 - 1 (stage 1 of the size bounds of
   Spec_api6) and the error codes of ZSTD_decompress (stage 2, item (E)). *)
Require Import VST.floyd.proofauto.
Require Export Zstd.proof.zstd.Spec_api6.
Require Export Zstd.proof.harness.rj_bad_checksum.HOK_rj_bad_checksum.
Require Zstd.proof.top.MainPre6.
Require Import Zstd.proof.zstd.NullBuf.
Require Zstd.proof.harness.HCsConv.
Require Zstd.proof.harness.frames.FSpecs Zstd.proof.harness.frames.FBodiesSmall Zstd.proof.harness.frames.FTransfer.
Require Zstd.proof.harness.frames.FBodyNewFrame Zstd.proof.harness.frames.FFacts Zstd.proof.harness.frames.FSeries.
Require Zstd.proof.harness.frames.FStreamSpec Zstd.proof.harness.frames.FBodyStreamAll.
Require Import Zstd.proof.harness.frames.FStreamNoEnd.
Require Import Zstd.proof.harness.rj_bad_checksum.Facts_rj_bad_checksum.
Import Zstd.proof.harness.frames.FSpecs.

Local Ltac expand_main_pre ::= idtac.

Lemma make_tycontext_g_isSome (V: varspecs) (G: funspecs) i :
  In i (map fst V) -> isSome (Maps.PTree.get i (make_tycontext_g V G)).
Proof.
  intros Hi. unfold make_tycontext_g.
  induction G as [|[j fs] G IH]; simpl.
  - induction V as [|[k t] V IHV]; simpl in *; [contradiction|].
    rewrite Maps.PTree.gsspec. destruct (peq i k); [exact Logic.I|]. apply IHV. destruct Hi; [congruence|auto].
  - rewrite Maps.PTree.gsspec. destruct (peq i j); [exact Logic.I|]. exact IH.
Qed.

Lemma vars_in_Vprog (G: funspecs) :
  Forall (fun ig : ident * globvar type => isSome (Maps.PTree.get (fst ig) (make_tycontext_g Vprog G)))
    (QPprog_vars Zstd.contracts.rj_bad_checksum.whole_prog).
Proof.
  apply Forall_forall. intros [i v] Hin. apply make_tycontext_g_isSome.
  unfold Vprog, QPvarspecs. rewrite map_map.
  apply in_map_iff. exists (i, v). split; [reflexivity | exact Hin].
Qed.

(* main's precondition: the decoder's globals, split off as in MainPre6.main_pre_fact6 (whose list of
   programs has the x_ laws only) *)
Lemma pre_globals gv :
  InitGPred (Vardefs Zstd.contracts.rj_bad_checksum.whole_prog) gv |-- zstd_globals gv * TT.
Proof.
  assert (Hincl: incl Zstd.proof.top.MainPre6.zstd_vardefs (Vardefs Zstd.contracts.rj_bad_checksum.whole_prog)).
  { apply Zstd.proof.top.MainPre6.MP_incl_Vardefs; vm_compute; reflexivity. }
  rewrite (Zstd.proof.top.MainPre6.MP_split_zstd _ gv Hincl).
  apply sepcon_derives; [apply Zstd.proof.top.MainPre6.zstd_vardefs_globals | apply TT_right].
Qed.

(* ---------- byte arrays and tokens between the harness's compspecs and the decoder's ---------- *)

Lemma to_Z sh n v p :
  @data_at CompSpecs sh (tarray tuchar n) v p |-- @data_at Zstd.units.Zstd.CS sh (tarray tuchar n) v p.
Proof. rewrite (Zstd.proof.harness.HCsConv.data_at_bytes_cs CompSpecs Zstd.units.Zstd.CS). apply derives_refl. Qed.

Lemma of_Z sh n v p :
  @data_at Zstd.units.Zstd.CS sh (tarray tuchar n) v p |-- @data_at CompSpecs sh (tarray tuchar n) v p.
Proof. rewrite (Zstd.proof.harness.HCsConv.data_at_bytes_cs CompSpecs Zstd.units.Zstd.CS). apply derives_refl. Qed.

Lemma to_Z_ sh n p :
  @data_at_ CompSpecs sh (tarray tuchar n) p |-- @data_at_ Zstd.units.Zstd.CS sh (tarray tuchar n) p.
Proof. rewrite (Zstd.proof.harness.HCsConv.data_at__bytes_cs CompSpecs Zstd.units.Zstd.CS). apply derives_refl. Qed.

Lemma tok_to_Z sh n p :
  @malloc_token CompSpecs sh (tarray tuchar n) p |-- @malloc_token Zstd.units.Zstd.CS sh (tarray tuchar n) p.
Proof.
  rewrite (@malloc_token_change_composite _ _ (Zstd.proof.harness.HCsConv.cce_any CompSpecs Zstd.units.Zstd.CS)
    sh (tarray tuchar n)) by reflexivity.
  apply derives_refl.
Qed.

Lemma tok_of_Z sh n p :
  @malloc_token Zstd.units.Zstd.CS sh (tarray tuchar n) p |-- @malloc_token CompSpecs sh (tarray tuchar n) p.
Proof.
  rewrite (@malloc_token_change_composite _ _ (Zstd.proof.harness.HCsConv.cce_any CompSpecs Zstd.units.Zstd.CS)
    sh (tarray tuchar n)) by reflexivity.
  apply derives_refl.
Qed.

Lemma isptr_of p : is_pointer_or_null p -> p <> nullval -> isptr p.
Proof. intros H1 H2. destruct p; simpl in *; auto. subst. contradiction. Qed.

(* a new stream context has no dictionary resources *)
Lemma res_none_i DD0 gv sh :
  emp |-- dict_res DD0 gv sh (dc_dict dctx_init) * set_res DD0 gv sh (dc_set dctx_init) (dc_dict dctx_init).
Proof. simpl. rewrite emp_sepcon. apply derives_refl. Qed.

(* ---------- the model facts main uses (Facts_rj_bad_checksum, FStreamNoEnd) ---------- *)

Definition main_facts : Prop :=
  (forall d fcs did c, byte_at (nf_bytes d fcs did c) 4 = nh_fhd (nc_hdr c)) /\
  (forall fcs maxw did h, nh_ok fcs maxw did h -> Z.land (nh_fhd h) 4 <> 0 -> nh_checksum h = true) /\
  (forall d c v, nf_ok (Zlength d) (Zlength d) (2 ^ 27) 0 c -> nh_checksum (nc_hdr c) = true ->
     Zlength (bad_frame d c v) = Zlength (nf_bytes d (Zlength d) 0 c)) /\
  (forall d c v, nf_ok (Zlength d) (Zlength d) (2 ^ 27) 0 c -> bytes_ok d -> bytes_ok (bad_frame d c v)) /\
  (forall d c v,
     nf_ok (Zlength d) (Zlength d) (2 ^ 27) 0 c -> bytes_ok d -> Zlength d < 2 ^ 64 ->
     nh_checksum (nc_hdr c) = true -> 0 <= v < 2 ^ 32 -> v <> xxh64 (nf_data d c) 0 mod 2 ^ 32 ->
     series_ck_m md_dflt sel_none no_wlim (Some no_dict) (bad_frame d c v) (nf_data d c)) /\
  (forall md d c v,
     nf_ok (Zlength d) (Zlength d) (2 ^ 27) 0 c -> bytes_ok d -> Zlength d < 2 ^ 64 ->
     nh_checksum (nc_hdr c) = true -> 0 <= v < 2 ^ 32 -> v <> xxh64 (nf_data d c) 0 mod 2 ^ 32 ->
     md_magicless md = false -> md_ignore md = false -> ZSTD_BLOCKSIZE_MAX <= md_bmax md ->
     series_frames_m md sel_none (Some no_dict) no_wlim (bad_frame d c v) = (nil, TDetCk)) /\
  (forall s cap dst st oc y r z,
     bytes_ok s ->
     ss_in (dc_ss st) = nil -> ss_ahead (dc_ss st) = 0 ->
     fst (series_frames_m (dmode_w (dmode_of (dc_par st))) (fst (st_sel st)) (snd (st_sel st)) no_wlim s) = nil ->
     snd (series_frames_m (dmode_w (dmode_of (dc_par st))) (fst (st_sel st)) (snd (st_sel st)) no_wlim s) <> TUnk ->
     Zstd.proof.harness.frames.FStreamSpec.stream_run s cap dst (Zstd.proof.harness.frames.FStreamSpec.sa_init st oc) y ->
     Zstd.proof.harness.frames.FStreamSpec.stream_call s cap dst y r z ->
     Zstd.proof.harness.frames.FStreamSpec.sa_done z = 0).

Lemma main_facts_ok : main_facts.
Proof.
  exact (conj bad_byte4 (conj bad_fhd_checksum (conj bad_frame_length (conj bad_frame_ok
          (conj bad_series_ck (conj bad_series_frames stream_no_end)))))).
Qed.

Section Main.
Variable DC : globals -> val -> dctx_st -> mpred.
Variable DD : globals -> val -> ddict_st -> mpred.

(* the API of the law *)
Definition API : funspecs :=
  [Zstd.proof.zstd.Spec_util.ZSTD_isError_spec; Zstd.proof.zstd.Spec_util.ZSTD_getErrorCode_spec;
   ZSTD_decompress_spec; ZSTD_createDStream_spec DC; ZSTD_decompressStream_spec DC DD;
   Zstd.proof.zstd.Spec_xxh.ZSTD_XXH64_spec].

(* the functions main calls *)
Definition G0 : funspecs :=
  [(_quickproof_malloc, malloc_spec');
   Zstd.proof.zstd.Spec_util.ZSTD_getErrorCode_spec; ZSTD_decompress_spec; ZSTD_createDStream_spec DC;
   Zstd.proof.zstd.Spec_xxh.ZSTD_XXH64_spec;
   nondet_u32_spec; gp_assert_spec;
   out_of_memory_spec; @Zstd.proof.harness.frames.FStreamSpec.stream_all_spec CompSpecs DC DD; @any_bytes_spec CompSpecs; upto_spec;
   @put_le_spec CompSpecs; @new_frame_spec CompSpecs].

(* main: the frame with the wrong checksum is refused one-shot with ZSTD_error_checksum_wrong (or a memory error,
   which ends the run) and never reported complete by the stream; from the model facts main_facts *)
Lemma drop_vp (P: mpred) p : (P && valid_pointer p) |-- P.
Proof. apply andp_left1. apply derives_refl. Qed.

(* frame[4] & 4 *)
Lemma and4 b : 0 <= b <= 255 -> Int.and (Int.repr b) (Int.repr 4) = Int.repr (Z.land b 4).
Proof. intros. unfold Int.and. rewrite !Int.unsigned_repr by rep_lia. reflexivity. Qed.

Lemma land4_nz b : 0 <= b <= 255 -> Z.land b 4 <> 0 -> Int.repr (Z.land b 4) <> Int.zero.
Proof.
  intros Hb Hn E. apply Hn.
  assert (0 <= Z.land b 4 < 8).
  { split; [apply Z.land_nonneg; lia |].
    change 8 with (2 ^ 3). apply Z.log2_lt_pow2; [pose proof (Z.land_nonneg b 4); lia |].
    pose proof (Z.log2_land b 4 ltac:(lia) ltac:(lia)). change (Z.log2 4) with 2 in *. lia. }
  apply (f_equal Int.unsigned) in E. rewrite Int.unsigned_repr in E by rep_lia. exact E.
Qed.

Lemma Znth_byte_at l i : 0 <= i -> Znth i l = byte_at l i.
Proof. intros Hi. unfold Znth, byte_at. rewrite if_false by lia. reflexivity. Qed.

(* the data, at the decoder's compspecs, as ZSTD_XXH64 reads it *)
Lemma to_xxh sh n d p : Zlength d = n ->
  @data_at CompSpecs sh (tarray tuchar n) (zbytes d) p |--
  @data_at Zstd.proof.zstd.Base.CompSpecs sh (tarray tuchar (Zlength d)) (Zstd.proof.zstd.Spec_xxh.xxh_bytes d) p.
Proof. intros <-. apply to_Z. Qed.

(* ---------- the buffer witnesses of a one-shot call: the malloc_tokens of its two buffers ---------- *)

Lemma pws_fold t1 p1 t2 p2 :
  (@malloc_token Zstd.units.Zstd.CS Ews t1 p1 * @malloc_token Zstd.units.Zstd.CS Ews t2 p2) |--
  pws_pred [pw_token Ews t1 p1; pw_token Ews t2 p2].
Proof. unfold pws_pred. simpl. rewrite sepcon_emp. apply derives_refl. Qed.

Lemma pws_in W w : In w W -> pws_pred W |-- pw_pred w * TT.
Proof.
  unfold pws_pred. induction W as [|a W IH]; simpl; [contradiction|]. intros [<-|Hin].
  - apply sepcon_derives; [apply derives_refl | apply TT_right].
  - eapply derives_trans; [apply sepcon_derives; [apply derives_refl | apply IH; exact Hin] |].
    rewrite <- sepcon_assoc, (sepcon_comm (pw_pred a)), sepcon_assoc.
    apply sepcon_derives; [apply derives_refl | apply TT_right].
Qed.

(* a malloc'ed buffer (also of 0 bytes) is weakly valid at both ends, given its token *)
Lemma buf_ok_tok W sh n p : In (pw_token Ews (tarray tuchar n) p) W -> readable_share sh -> 0 <= n -> isptr p ->
  buf_ok W sh n p.
Proof.
  intros Hin Hsh Hn Hp. unfold buf_ok.
  eapply derives_trans; [apply sepcon_derives; [apply (pws_in W _ Hin) | apply derives_refl] |].
  simpl pw_pred.
  destruct (zlt 0 n) as [Hpos|Hz].
  - rewrite (@data_at__memory_block Zstd.units.Zstd.CS). normalize.
    replace (sizeof (tarray tuchar n)) with n by (simpl; lia).
    apply andp_right; apply sepcon_weak_valid_pointer2.
    + rewrite <- (isptr_offset_val_zero p) at 2 by exact Hp.
      apply memory_block_weak_valid_pointer; [lia | lia | apply readable_nonidentity; exact Hsh].
    + apply memory_block_weak_valid_pointer; [lia | lia | apply readable_nonidentity; exact Hsh].
  - assert (n = 0) by lia. subst n. rewrite isptr_offset_val_zero by exact Hp.
    rewrite sepcon_assoc.
    assert (Hv: @malloc_token Zstd.units.Zstd.CS Ews (tarray tuchar 0) p |-- weak_valid_pointer p)
      by (eapply derives_trans; [apply malloc_token_valid_pointer; simpl; lia | apply valid_pointer_weak]).
    apply andp_right; apply sepcon_weak_valid_pointer1; exact Hv.
Qed.

(* wrong <> (uint32_t) ZSTD_XXH64(data, n, 0) *)
Lemma wrong_ne w h : 0 <= w <= Int.max_unsigned ->
  Int.repr w <> Int.repr (Int64.Z_mod_modulus h) -> w <> h mod 2 ^ 32.
Proof.
  intros Hw Hn E. apply Hn.
  rewrite <- (Int.repr_unsigned (Int.repr w)), <- (Int.repr_unsigned (Int.repr (Int64.Z_mod_modulus h))).
  f_equal. rewrite !Int.unsigned_repr_eq, Int64.Z_mod_modulus_eq.
  change Int.modulus with (2 ^ 32). change Int64.modulus with (2 ^ 64).
  rewrite <- (Znumtheory.Zmod_div_mod (2 ^ 32) (2 ^ 64) h); [| lia | lia | exists (2 ^ 32); reflexivity].
  rewrite Z.mod_small by rep_lia. exact E.
Qed.

(* put_le's bytes over the frame's last 4 bytes: bad_frame *)
Lemma bad_written d c v : 4 <= Zlength (nf_bytes d (Zlength d) 0 c) ->
  Zstd.proof.zstd.Spec_util.mem_written (zbytes (nf_bytes d (Zlength d) 0 c))
    (Zlength (nf_bytes d (Zlength d) 0 c) - 4) 4 v = zbytes (bad_frame d c v).
Proof.
  intros Hl. unfold Zstd.proof.zstd.Spec_util.mem_written, bad_frame.
  set (F := nf_bytes d (Zlength d) 0 c) in *.
  rewrite !map_app. rewrite Zlength_map.
  replace (Zlength F - 4 + 4) with (Zlength F) by lia.
  rewrite sublist_nil, app_nil_r.
  rewrite sublist_map, sublist_firstn. reflexivity.
Qed.

(* a branch of a test whose condition is known to be the other way *)
Ltac dead_branch :=
  first [ discriminate | contradiction
        | exfalso; match goal with Hn: _ <> _ |- _ => apply Hn; reflexivity end ].

(* the end of a run whose frame (or data) is NULL: the test before put_le returns 0 *)
Ltac null_tail :=
  repeat apply -> seq_assoc; apply semax_if_seq; forward_if; [forward | dead_branch];
  repeat apply -> seq_assoc; apply semax_if_seq; forward_if; [forward | dead_branch];
  repeat apply -> seq_assoc; apply semax_if_seq; forward_if; [forward | dead_branch];
  forward_if; [forward | dead_branch];
  cancel.

Lemma body_main_G0_from : main_facts -> semax_body Vprog G0 f_main main_spec.
Proof.
  intros (Hb4 & Hck & Hblen & Hbok & Hser & Hsf & Hsne).
  change (semax_body Vprog G0 f_main (_main, WITH gv: globals PRE [] VST.floyd.VSU.main_pre
    Zstd.contracts.rj_bad_checksum.whole_prog tt gv POST [tint] (fun _ : environ => TT))).
  replace (fun _ : environ => @TT mpred _) with (PROP () LOCAL () SEP (@TT mpred _))
    by (extensionality rho; unfold PROPx, LOCALx, SEPx; simpl; normalize).
  start_function1.
  eapply (main_pre_InitGpred (zstd_globals gv * TT)%logic).
  { intros _. apply pre_globals. }
  { reflexivity. }
  { apply vars_in_Vprog. }
  start_function3.
  sep_apply (create_mem_mgr gv).
  forward_call 9223372036854775807.
  Intros n.
  forward_call (gv, n).
  Intros vret. destruct vret as [data l]. cbn [fst snd] in *.
  repeat apply -> seq_assoc. apply semax_if_seq.
  destruct (eq_dec data nullval) as [Hdn|Hdn].
  { subst data. unfold mbytes. rewrite if_true by reflexivity.
    forward_if; [| contradiction].
    forward. forward.
    forward_call tt. Intros wrong.
    forward_call (9223372036854775807 - n). Intros k.
    forward.
    forward_call (tarray tuchar (n + k), gv).
    { simpl. rep_lia. }
    Intros dst.
    forward_call gv. Intros zds.
    repeat apply -> seq_assoc. apply semax_if_seq.
    forward_if; [| contradiction].
    forward.
    null_tail. }
  unfold mbytes at 1. rewrite if_false by exact Hdn. Intros.
  assert_PROP (isptr data) as Hdp by entailer!.
  subst n.
  forward_if; [destruct data; try contradiction; discriminate |].
  sep_apply (tok_to_Z Ews (Zlength l) data).
  forward_call (gv, Ews, data, l, Zlength l, 2 ^ 27, 0, Tsh, v_len,
                Zstd.proof.zstd.Spec_xxh.pw_token Ews (tarray tuchar (Zlength l)) data).
  { simpl Zstd.proof.zstd.Spec_xxh.pw_pred.
    change (@malloc_token Zstd.proof.zstd.Base.CompSpecs) with (@malloc_token Zstd.units.Zstd.CS). cancel. }
  { simpl Zstd.proof.zstd.Spec_xxh.pw_pred.
    eapply derives_trans; [apply malloc_token_valid_pointer; simpl; match goal with Hz: Zlength l = 0 |- _ => rewrite Hz end; lia
                         | apply valid_pointer_weak]. }
  Intros vret. destruct vret as [frame d']. cbn [fst snd] in *.
  forward.
  destruct (eq_dec frame nullval) as [Hfn|Hfn].
  { subst frame.
    forward_call tt. Intros wrong.
    forward_call (9223372036854775807 - Zlength l). Intros k.
    forward.
    forward_call (tarray tuchar (Zlength l + k), gv).
    { simpl. rep_lia. }
    Intros dst.
    forward_call gv. Intros zds.
    repeat apply -> seq_assoc. apply semax_if_seq.
    forward_if; [| contradiction].
    forward.
    null_tail. }
  Intros c.
  unfold mbytes at 1. rewrite if_false by exact Hfn. Intros.
  rename H4 into Hnf. subst d'.
  pose proof (Zstd.proof.harness.frames.FFacts.nf_bytes_length l (Zlength l) (2 ^ 27) 0 c Hnf) as HFl.
  pose proof (Zstd.proof.harness.frames.FFacts.nf_bytes_ok l (Zlength l) (2 ^ 27) 0 c Hnf H1) as HFb.
  set (F := nf_bytes l (Zlength l) 0 c) in *.
  assert_PROP (isptr frame) as Hfp by entailer!.
  forward_call tt. Intros wrong.
  forward_call (9223372036854775807 - Zlength l). Intros k.
  forward.
  forward_call (tarray tuchar (Zlength l + k), gv).
  { simpl. rep_lia. }
  Intros dst.
  forward_call gv. Intros zds.
  repeat apply -> seq_assoc. apply semax_if_seq.
  forward_if; [destruct frame; try contradiction; discriminate |].
  destruct (eq_dec dst nullval) as [Hdsn|Hdsn].
  { subst dst. forward.
    repeat apply -> seq_assoc; apply semax_if_seq; forward_if; [forward | dead_branch].
    repeat apply -> seq_assoc; apply semax_if_seq; forward_if; [forward | dead_branch].
    repeat apply -> seq_assoc; apply semax_if_seq; forward_if; [forward | dead_branch].
    forward_if; [forward | dead_branch].
    cancel. }
  Intros. assert_PROP (isptr dst) as Hdsp by entailer!.
  forward.
  repeat apply -> seq_assoc. apply semax_if_seq.
  forward_if; [destruct dst; try contradiction; discriminate |].
  destruct (eq_dec zds nullval) as [Hzn|Hzn].
  { subst zds. forward.
    repeat apply -> seq_assoc; apply semax_if_seq; forward_if; [forward | dead_branch].
    repeat apply -> seq_assoc; apply semax_if_seq; forward_if; [forward | dead_branch].
    forward_if; [forward | dead_branch].
    cancel. }
  pose proof (isptr_of zds PNzds Hzn) as Hzp.
  forward.
  repeat apply -> seq_assoc. apply semax_if_seq.
  forward_if; [destruct zds; try contradiction; discriminate |].
  sep_apply (drop_vp (DC gv zds dctx_init) zds).
  (* frame[4], the Frame_Header_Descriptor *)
  assert (Hb: 0 <= Znth 4 F <= 255).
  { pose proof (proj1 (Forall_Znth _ _) HFb 4 ltac:(lia)) as Hz. unfold is_byte in Hz. lia. }
  forward.
  { entailer!. simpl. rep_lia. }
  forward.
  rewrite (and4 _ Hb).
  rewrite (Znth_byte_at F 4) in Hb by lia. rewrite (Znth_byte_at F 4) by lia.
  unfold F in Hb |- *. rewrite Hb4 in Hb |- *.
  destruct (Z.eq_dec (Z.land (nh_fhd (nc_hdr c)) 4) 0) as [Hl0|Hl0].
  { rewrite Hl0. repeat apply -> seq_assoc. apply semax_if_seq. forward_if; [| dead_branch]. forward.
    forward_if; [forward | dead_branch].
    cancel. }
  assert (Hcs: nh_checksum (nc_hdr c) = true) by exact (Hck _ _ _ _ (proj1 Hnf) Hl0).
  rewrite (Int.eq_false (Int.repr (Z.land (nh_fhd (nc_hdr c)) 4)) Int.zero)
    by (apply land4_nz; [lia | exact Hl0]).
  fold F.
  repeat apply -> seq_assoc. apply semax_if_seq.
  forward_if; [dead_branch |].
  sep_apply (to_xxh Ews (Zlength l) (nf_data l c) data H2).
  forward_call (Ews, data, nf_data l c, 0, Zstd.proof.zstd.Spec_xxh.pw_token Ews (tarray tuchar (Zlength l)) data).
  { rewrite H2. entailer!. }
  { simpl Zstd.proof.zstd.Spec_xxh.pw_pred.
    eapply derives_trans; [apply malloc_token_valid_pointer; simpl; lia | apply valid_pointer_weak]. }
  rewrite H2. change (Zstd.proof.zstd.Spec_xxh.xxh_bytes (nf_data l c)) with (zbytes (nf_data l c)).
  forward.
  forward_if; [forward; cancel |].
  match goal with Hn: Int.repr wrong <> _ |- _ => pose proof (wrong_ne _ _ H4 Hn) as Hw end.
  (* put_le(frame + len - 4, wrong, 4): the frame with the wrong checksum *)
  forward.
  forward_call (Ews, frame, zbytes F, Zlength F - 4, wrong, 4).
  { entailer!. simpl. destruct frame; try contradiction. simpl. rewrite Int.unsigned_repr by rep_lia.
    f_equal. f_equal. rewrite Ptrofs.sub_add_opp, Ptrofs.add_assoc. f_equal.
    replace (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_ints (Int.repr 4))) with (Ptrofs.repr 4) by reflexivity.
    rewrite Ptrofs.neg_repr, ptrofs_add_repr. f_equal; lia. }
  { rewrite Zlength_map. cancel. }
  { rewrite Zlength_map. rep_lia. }
  rewrite Zlength_map.
  replace (Zstd.proof.zstd.Spec_util.mem_written (zbytes F) (Zlength F - 4) 4 wrong)
    with (zbytes (bad_frame l c wrong)) by (symmetry; apply bad_written; unfold F in HFl; lia).
  set (B := bad_frame l c wrong) in *.
  assert (HB: Zlength B = Zlength F) by exact (Hblen l c wrong Hnf Hcs).
  assert (HBb: bytes_ok B) by exact (Hbok l c wrong Hnf H1).
  rewrite <- HB.
  (* result = ZSTD_decompress(dst, cap, frame, len) *)
  forward.
  rewrite add64_repr.
  set (cap := Zlength l + k) in *.
  sep_apply (to_Z Ews (Zlength B) (zbytes B) frame).
  sep_apply (to_Z_ Ews cap dst).
  sep_apply (data_at__mbuf Ews cap dst).
  sep_apply (tok_to_Z Ews (Zlength B) frame).
  sep_apply (tok_to_Z Ews cap dst).
  sep_apply (pws_fold (tarray tuchar (Zlength B)) frame (tarray tuchar cap) dst).
  assert (Hn4: Zlength l <= 2305843009213693945).
  { change ((PTRDIFF_MAX - 26) / 4) with 2305843009213693945 in H6. exact H6. }
  forward_call ([pw_token Ews (tarray tuchar (Zlength B)) frame; pw_token Ews (tarray tuchar cap) dst],
                gv, Ews, dst, cap, Ews, frame, B).
  { split; (apply buf_ok_tok; [simpl; tauto | auto | unfold cap; lia | auto]). }
  Intros vret. destruct vret as [r out]. cbn [fst snd] in *. rewrite mbuf_isptr by auto.
  (* the one-shot result: ZSTD_error_checksum_wrong, or a memory error *)
  assert (Hr: r = err_code ZSTD_error_checksum_wrong \/ r = err_code ZSTD_error_memory_allocation).
  { match goal with Hk: oneshot_codes _ _ _ _ _ _ |- _ => apply (proj1 Hk (nf_data l c)) end.
    - apply Hser; auto; rep_lia.
    - rewrite H2. unfold cap. lia. }
  forward.
  (* last = stream_all(zds, frame, len, dst, cap, &written, &completed) *)
  forward.
  sep_apply (of_Z Ews cap out dst).
  sep_apply (res_none_i DD gv Ews).
  forward_call ([pw_token Ews (tarray tuchar (Zlength B)) frame; pw_token Ews (tarray tuchar cap) dst],
                gv, zds, dctx_init, Ews, frame, B, Ews, dst, cap, out, Tsh, v_written, Tsh, v_completed).
  { cancel. }
  { split3; [unfold stream_dict_ok; simpl; auto |..].
    all: apply buf_ok_tok; [simpl; tauto | auto | unfold cap; lia | auto]. }
  Intros vret. destruct vret as [[r' y] z]. cbn [fst snd] in *.
  match goal with Hc: FStreamSpec.stream_call _ _ _ _ _ _ |- _ =>
    assert (Hr': 0 <= r' <= Int64.max_unsigned) by (destruct Hc as (? & ? & ? & _ & _ & ? & _); auto) end.
  (* the stream never reports the frame complete: the walk over B finds no frame and ends at the checksum *)
  assert (Hm: series_frames_m (dmode_w (dmode_of (dc_par dctx_init))) (fst (st_sel dctx_init))
                (snd (st_sel dctx_init)) no_wlim B = (nil, TDetCk)).
  { change (st_sel dctx_init) with (sel_none, Some no_dict). cbn [fst snd].
    apply Hsf; auto; [rep_lia | rep_lia | unfold dmode_w, dmode_of; simpl; lia]. }
  assert (Hz0: FStreamSpec.sa_done z = 0).
  { apply (Hsne B cap dst dctx_init out y r' z);
      [exact HBb | reflexivity | reflexivity | rewrite Hm; reflexivity | rewrite Hm; discriminate
      | eassumption | eassumption]. }
  forward.
  (* out_of_memory(result) || out_of_memory(last): the run ends *)
  forward_call r.
  repeat apply -> seq_assoc. apply semax_if_seq.
  destruct (Z.eq_dec (Zstd.proof.zstd.Spec_util.error_of r) 64) as [Hm64|Hm64].
  { forward_if; [forward | dead_branch]. forward_if; [forward; cancel | dead_branch]. }
  forward_if; [dead_branch |].
  apply -> seq_assoc.
  forward_call r'.
  forward.
  destruct (Z.eq_dec (Zstd.proof.zstd.Spec_util.error_of r') 64) as [Hm64'|Hm64'].
  { forward_if; [forward; cancel | dead_branch]. }
  forward_if; [dead_branch |].
  (* the check: ZSTD_error_checksum_wrong and *completed == 0 *)
  assert (Herr: Zstd.proof.zstd.Spec_util.error_of r = 22).
  { destruct Hr as [-> | ->]; [reflexivity | exfalso; apply Hm64; reflexivity]. }
  forward_call r.
  rewrite Herr.
  repeat apply -> seq_assoc. apply semax_if_seq.
  forward_if; [| dead_branch].
  forward. rewrite Hz0. forward.
  forward_call Int.one.
  forward. cancel.
  (* the call of ZSTD_XXH64 leaves open the change of compspecs of its byte array: any two agree on bytes *)
  Unshelve. all: exact (Zstd.proof.harness.HCsConv.cce_any _ _).
Qed.

Lemma body_main_G0 : semax_body Vprog G0 f_main main_spec.
Proof. exact (body_main_G0_from main_facts_ok). Qed.

End Main.

(* ---------- from G0 to Gprog (API DC DD) Hs ---------- *)

(* the harness's own functions besides main (in the order of helper_ids): the frames kit's helpers *)
Definition Hs DC DD : funspecs :=
  [out_of_memory_spec; @copy_of_spec CompSpecs; @Zstd.proof.harness.frames.FStreamSpec.stream_all_spec CompSpecs DC DD; @any_bytes_spec CompSpecs;
   upto_spec; @put_le_spec CompSpecs; @new_frame_spec CompSpecs].

Lemma Externals_eq : Externals =
  [nondet_u8_spec; nondet_u32_spec; nondet_size_spec; nondet_bytes_nn_spec; gp_assert_spec; gp_assume_spec].
Proof.
  unfold Externals, present, env_harness, filter.
  repeat match goal with |- context [id_in_list ?i ?l] =>
    let b := eval lazy in (id_in_list i l) in change (id_in_list i l) with b end.
  reflexivity.
Qed.

Lemma find_cons {A} i (a: ident * A) l :
  initial_world.find_id i (a :: l) = if Pos.eqb i (fst a) then Some (snd a) else initial_world.find_id i l.
Proof.
  destruct a as [j x]. simpl. destruct (Memory.EqDec_ident i j) as [E|Hne].
  - subst. rewrite Pos.eqb_refl. reflexivity.
  - destruct (Pos.eqb_spec i j); [contradiction | reflexivity].
Qed.

Ltac find_steps :=
  repeat (rewrite find_cons;
          match goal with |- context [Pos.eqb ?i (fst ?a)] =>
            let b := eval lazy in (Pos.eqb i (fst a)) in change (Pos.eqb i (fst a)) with b end;
          cbv beta iota).

Lemma Gprog_cons DC DD : Gprog (API DC DD) (Hs DC DD) =
  (_quickproof_malloc, malloc_spec') :: (_quickproof_free, free_spec') ::
  API DC DD ++
  [nondet_u8_spec; nondet_u32_spec; nondet_size_spec; nondet_bytes_nn_spec; gp_assert_spec; gp_assume_spec] ++
  Hs DC DD ++ [main_spec].
Proof. unfold Gprog, Imports. rewrite Externals_eq. reflexivity. Qed.

(* an entry (i, fs) of a list found in Gprog *)
Ltac in_gprog :=
  match goal with |- initial_world.find_id ?i _ = Some ?fs =>
    rewrite Gprog_cons; unfold API, Hs; cbn [app]; find_steps; reflexivity end.

Lemma G0_in_Gprog DC DD i fs : initial_world.find_id i (G0 DC DD) = Some fs ->
  initial_world.find_id i (Gprog (API DC DD) (Hs DC DD)) = Some fs.
Proof.
  intros Hi. apply initial_world.find_id_e in Hi. unfold G0 in Hi.
  rewrite Gprog_cons. unfold API, Hs. cbn [app].
  repeat destruct Hi as [E|Hi];
    try match type of E with ?a = (i, fs) =>
      replace i with (fst a) by (rewrite E; reflexivity);
      replace fs with (snd a) by (rewrite E; reflexivity) end;
    try contradiction;
    find_steps; reflexivity.
Qed.
Lemma make_tycontext_g_find (Vs: varspecs) (G: funspecs) i :
  Maps.PTree.get i (make_tycontext_g Vs G) =
  match initial_world.find_id i G with Some fs => Some (type_of_funspec fs) | None => Maps.PTree.get i (make_tycontext_g Vs nil) end.
Proof.
  induction G as [|[j fs] G IH]; simpl; auto.
  rewrite Maps.PTree.gsspec. unfold make_tycontext_g in IH |- *. simpl in IH.
  destruct (peq i j) as [->|Hne].
  - rewrite if_true by reflexivity. reflexivity.
  - rewrite if_false by exact Hne. exact IH.
Qed.

Lemma mtg_none (V: varspecs) i : ~ In i (map fst V) -> Maps.PTree.get i (make_tycontext_g V []) = None.
Proof.
  unfold make_tycontext_g. induction V as [|[k t] V IH]; simpl; intros Hn.
  - apply Maps.PTree.gempty.
  - rewrite Maps.PTree.gsspec. destruct (peq i k); [subst; tauto |]. apply IH. tauto.
Qed.

(* no function name of Gprog is a global variable of the program *)
Lemma Gprog_not_var DC DD i : In i (map fst (Gprog (API DC DD) (Hs DC DD))) -> ~ In i (map fst Vprog).
Proof.
  intros Hin Hv.
  assert (Hb: forallb (fun j => negb (id_in_list j (map fst Vprog))) (map fst (Gprog (API DC DD) (Hs DC DD))) = true).
  { match goal with |- forallb ?f ?l = true => let L := eval lazy in l in change l with L end.
    vm_compute. reflexivity. }
  rewrite forallb_forall in Hb. specialize (Hb i Hin).
  rewrite (Zstd.proof.top.MainPre6.MP_id_in_list_true_i i _ Hv) in Hb. discriminate.
Qed.


(* a helper of the frames kit: its body, proved once at any compspecs, in Gprog *)
Ltac kit_body fn fk Gk body :=
  exists fn; split; [vm_compute; reflexivity|]; split; [reflexivity|];
  let E := fresh "E" in
  assert (E: fn = fk) by (vm_compute; reflexivity);
  rewrite E; apply (Zstd.proof.harness.frames.FTransfer.fk_transfer Vprog _ Gk);
  [ exact body
  | apply Zstd.proof.harness.frames.FTransfer.fk_find_all; repeat constructor; in_gprog ].

Theorem rj_bad_checksum_ok :
  forall (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred),
    HarnessOK (API DC DD) (Hs DC DD).
Proof.
  intros DC DD. split.
  - vm_compute. reflexivity.
  - constructor; [| constructor; [| constructor; [| constructor; [| constructor; [| constructor;
      [| constructor; [| constructor; [| constructor]]]]]]]].
    + kit_body Zstd.harness.rj_bad_checksum.code.f_out_of_memory FSpecs.f_out_of_memory G_out_of_memory
        (@Zstd.proof.harness.frames.FBodiesSmall.body_out_of_memory CompSpecs).
    + kit_body Zstd.harness.rj_bad_checksum.code.f_copy_of FSpecs.f_copy_of (@G_copy_of CompSpecs)
        (@Zstd.proof.harness.frames.FBodiesSmall.body_copy_of CompSpecs).
    + kit_body Zstd.harness.rj_bad_checksum.code.f_stream_all Zstd.proof.harness.frames.FStreamSpec.f_stream_all
        (Zstd.proof.harness.frames.FStreamSpec.G_stream_all DC DD)
        (@Zstd.proof.harness.frames.FBodyStreamAll.body_stream_all CompSpecs
           ltac:(Zstd.proof.harness.frames.FBodyStreamAll.fs_cspecs_sub) DC DD).
    + kit_body Zstd.harness.rj_bad_checksum.code.f_any_bytes FSpecs.f_any_bytes (@G_any_bytes CompSpecs)
        (@Zstd.proof.harness.frames.FBodiesSmall.body_any_bytes CompSpecs).
    + kit_body Zstd.harness.rj_bad_checksum.code.f_upto FSpecs.f_upto G_upto
        (@Zstd.proof.harness.frames.FBodiesSmall.body_upto CompSpecs).
    + kit_body Zstd.harness.rj_bad_checksum.code.f_put_le FSpecs.f_put_le G_put_le
        (@Zstd.proof.harness.frames.FBodiesSmall.body_put_le CompSpecs).
    + kit_body Zstd.harness.rj_bad_checksum.code.f_new_frame FSpecs.f_new_frame (@G_new_frame CompSpecs)
        (@Zstd.proof.harness.frames.FBodyNewFrame.body_new_frame CompSpecs).
    + (* main *)
      exists f_main. split; [reflexivity|]. split; [reflexivity|].
      eapply semax_body_subsumption; [apply (body_main_G0 DC DD) |].
      apply tycontext_sub_i99. split; intro i.
      * rewrite (make_tycontext_g_find Vprog (G0 DC DD) i).
        rewrite (make_tycontext_g_find Vprog (Gprog (API DC DD) (Hs DC DD)) i).
        destruct (initial_world.find_id i (G0 DC DD)) as [fs|] eqn:E.
        -- rewrite (G0_in_Gprog DC DD i fs E). apply sub_option_refl.
        -- destruct (initial_world.find_id i (Gprog (API DC DD) (Hs DC DD))) as [fs'|] eqn:E'.
           ++ rewrite mtg_none; [exact Logic.I |].
              apply (Gprog_not_var DC DD i).
              apply initial_world.find_id_e in E'. apply (in_map fst) in E'. exact E'.
           ++ apply sub_option_refl.
      * rewrite !semax_prog.find_id_maketycontext_s.
        destruct (initial_world.find_id i (G0 DC DD)) as [fs|] eqn:E; [|exact Logic.I].
        rewrite (G0_in_Gprog DC DD i fs E). exists fs. split; [reflexivity|]. apply funspec_sub_si_refl.
Qed.
