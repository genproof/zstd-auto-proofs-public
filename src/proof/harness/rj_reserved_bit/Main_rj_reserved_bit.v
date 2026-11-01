(* The harness obligation of rj_reserved_bit (harness/rj_reserved_bit.c): for ANY predicates DC, DD of the
   decoder's API (Spec_api6), with the API [ZSTD_isError; ZSTD_getErrorCode; ZSTD_decompress; ZSTD_createDStream;
   ZSTD_decompressStream; ZSTD_XXH64] (the second for out_of_memory, the last for new_frame's checksums), the
   helpers of laws_common.h and frames.h (proved once in the frames kit) and main satisfy their specifications.

   main builds a frame of new_frame and sets the Reserved_bit of its Frame_Header_Descriptor
   (Facts_rj_reserved_bit.rb_frame).  The model refuses this series at the frame header, before any frame
   (TDetHdr).  One-shot: ZSTD_decompress's oneshot_ok then gives an error (SDet).  Streamed: no call of stream_all
   returns 0 (FStreamNoEnd.stream_no_end), so *completed stays 0.  The buffers have any size up to PTRDIFF_MAX:
   this needs the one-shot and streaming specifications with sizes up to 2 ^ 63 - 1 (stage 1 of the size bounds
   of Spec_api6). *)
Require Import VST.floyd.proofauto.
Require Export Zstd.proof.zstd.Spec_api6.
Require Export Zstd.proof.harness.rj_reserved_bit.HOK_rj_reserved_bit.
Require Zstd.proof.top.MainPre6.
Require Import Zstd.proof.zstd.NullBuf.
Require Zstd.proof.harness.HCsConv.
Require Zstd.proof.harness.frames.FSpecs Zstd.proof.harness.frames.FBodiesSmall Zstd.proof.harness.frames.FTransfer.
Require Zstd.proof.harness.frames.FBodyNewFrame Zstd.proof.harness.frames.FFacts Zstd.proof.harness.frames.FSeries.
Require Zstd.proof.harness.frames.FStreamSpec Zstd.proof.harness.frames.FBodyStreamAll.
Require Import Zstd.proof.harness.frames.FStreamNoEnd.
Require Import Zstd.proof.harness.rj_reserved_bit.Facts_rj_reserved_bit.
Import Zstd.proof.harness.frames.FSpecs Zstd.proof.harness.frames.FStreamSpec.
(* the harness's names (Vprog, CompSpecs) over those of Spec_api6, which FStreamSpec exports *)
Import Zstd.proof.harness.rj_reserved_bit.HOK_rj_reserved_bit.

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
    (QPprog_vars Zstd.contracts.rj_reserved_bit.whole_prog).
Proof.
  apply Forall_forall. intros [i v] Hin. apply make_tycontext_g_isSome.
  unfold Vprog, QPvarspecs. rewrite map_map.
  apply in_map_iff. exists (i, v). split; [reflexivity | exact Hin].
Qed.

(* main's precondition: the decoder's globals, split off as in MainPre6.main_pre_fact6 (whose list of
   programs has the x_ laws only) *)
Lemma pre_globals gv :
  InitGPred (Vardefs Zstd.contracts.rj_reserved_bit.whole_prog) gv |-- zstd_globals gv * TT.
Proof.
  assert (Hincl: incl Zstd.proof.top.MainPre6.zstd_vardefs (Vardefs Zstd.contracts.rj_reserved_bit.whole_prog)).
  { apply Zstd.proof.top.MainPre6.MP_incl_Vardefs; vm_compute; reflexivity. }
  rewrite (Zstd.proof.top.MainPre6.MP_split_zstd _ gv Hincl).
  apply sepcon_derives; [apply Zstd.proof.top.MainPre6.zstd_vardefs_globals | apply TT_right].
Qed.

(* ---------- byte arrays between the harness's compspecs and the decoder's ---------- *)

Lemma to_Z sh n v p :
  @data_at CompSpecs sh (tarray tuchar n) v p |-- @data_at Zstd.units.Zstd.CS sh (tarray tuchar n) v p.
Proof. rewrite (Zstd.proof.harness.HCsConv.data_at_bytes_cs CompSpecs Zstd.units.Zstd.CS). apply derives_refl. Qed.

Lemma of_Z sh n v p :
  @data_at Zstd.units.Zstd.CS sh (tarray tuchar n) v p |-- @data_at CompSpecs sh (tarray tuchar n) v p.
Proof. rewrite (Zstd.proof.harness.HCsConv.data_at_bytes_cs CompSpecs Zstd.units.Zstd.CS). apply derives_refl. Qed.

#[local] Instance CCE_HZ : change_composite_env CompSpecs Zstd.units.Zstd.CS.
Proof. make_cs_preserve CompSpecs Zstd.units.Zstd.CS. Defined.

(* the decoder's specifications are stated at Base.CompSpecs; forward_call moves their frame back to the harness's *)
#[local] Instance CCE_BH : change_composite_env Zstd.proof.zstd.Base.CompSpecs CompSpecs.
Proof. make_cs_preserve Zstd.proof.zstd.Base.CompSpecs CompSpecs. Defined.

Lemma to_Z_ sh n p :
  @data_at_ CompSpecs sh (tarray tuchar n) p |-- @data_at_ Zstd.units.Zstd.CS sh (tarray tuchar n) p.
Proof. rewrite (@data_at__change_composite _ _ CCE_HZ sh (tarray tuchar n)) by reflexivity. apply derives_refl. Qed.

Lemma tok_to_Z sh n p :
  @malloc_token CompSpecs sh (tarray tuchar n) p |-- @malloc_token Zstd.units.Zstd.CS sh (tarray tuchar n) p.
Proof. rewrite (@malloc_token_change_composite _ _ CCE_HZ sh (tarray tuchar n)) by reflexivity. apply derives_refl. Qed.

Lemma tok_of_Z sh n p :
  @malloc_token Zstd.units.Zstd.CS sh (tarray tuchar n) p |-- @malloc_token CompSpecs sh (tarray tuchar n) p.
Proof. rewrite (@malloc_token_change_composite _ _ CCE_HZ sh (tarray tuchar n)) by reflexivity. apply derives_refl. Qed.

(* ---------- the pointer witnesses: the malloc_tokens of the buffers ---------- *)

(* a malloc'ed block of 0 bytes: its token shows that its address is valid (new_frame on empty data, ZSTD_decompress
   with cap = 0) *)
Lemma tok_wvp n p : n = 0 ->
  Zstd.proof.zstd.Spec_xxh.pw_pred (Zstd.proof.zstd.Spec_xxh.pw_token Ews (tarray tuchar n) p) |-- weak_valid_pointer p.
Proof.
  intros ->. simpl. eapply derives_trans; [apply malloc_token_valid_pointer; simpl; lia | apply valid_pointer_weak].
Qed.

Lemma pws_fold t1 p1 t2 p2 :
  (@malloc_token Zstd.units.Zstd.CS Ews t1 p1 * @malloc_token Zstd.units.Zstd.CS Ews t2 p2) |--
  pws_pred [pw_token Ews t1 p1; pw_token Ews t2 p2].
Proof. unfold pws_pred. simpl. rewrite sepcon_emp. apply derives_refl. Qed.

Lemma pws_unfold t1 p1 t2 p2 :
  pws_pred [pw_token Ews t1 p1; pw_token Ews t2 p2] |--
  (@malloc_token Zstd.units.Zstd.CS Ews t1 p1 * @malloc_token Zstd.units.Zstd.CS Ews t2 p2).
Proof. unfold pws_pred. simpl. rewrite sepcon_emp. apply derives_refl. Qed.

Lemma pws_in W w : In w W -> pws_pred W |-- pw_pred w * TT.
Proof.
  unfold pws_pred. induction W as [|a W IH]; simpl; [contradiction|]. intros [<-|Hin].
  - apply sepcon_derives; [apply derives_refl | apply TT_right].
  - eapply derives_trans; [apply sepcon_derives; [apply derives_refl | apply IH; exact Hin] |].
    rewrite <- sepcon_assoc, (sepcon_comm (pw_pred a)), sepcon_assoc.
    apply sepcon_derives; [apply derives_refl | apply TT_right].
Qed.

(* a buffer whose malloc_token is among the witnesses is weakly valid at both ends *)
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

Lemma mbytes_fold {cs: compspecs} n l q : q <> nullval ->
  malloc_token Ews (tarray tuchar n) q * data_at Ews (tarray tuchar n) (zbytes l) q |-- mbytes n l q.
Proof. intros Hq. unfold mbytes. rewrite if_false by exact Hq. apply derives_refl. Qed.

Lemma isptr_of p : is_pointer_or_null p -> p <> nullval -> isptr p.
Proof. intros H1 H2. destruct p; simpl in *; auto. subst. contradiction. Qed.

(* a new stream context has no dictionary resources *)
Lemma res_none_i DD0 gv sh :
  emp |-- dict_res DD0 gv sh (dc_dict dctx_init) * set_res DD0 gv sh (dc_set dctx_init) (dc_dict dctx_init).
Proof. simpl. rewrite emp_sepcon. apply derives_refl. Qed.

(* ---------- the law's two facts in VST terms ---------- *)

(* the statement frame[4] |= 8 on the array of the bytes F leaves the bytes rb_frame F *)
Lemma rb_zbytes F : bytes_ok F -> 5 <= Zlength F ->
  upd_Znth 4 (zbytes F) (Vint (Int.zero_ext 8 (Int.or (Int.repr (Znth 4 F)) (Int.repr 8)))) = zbytes (rb_frame F).
Proof.
  intros Hok Hl.
  assert (HB: 0 <= Znth 4 F < 256) by (apply (proj1 (Forall_Znth F is_byte) Hok); lia).
  (* the byte arithmetic, checked on the 256 bytes *)
  assert (Hall: forallb (fun a => Int.eq (Int.zero_ext 8 (Int.or (Int.repr a) (Int.repr 8))) (Int.repr (Z.lor a 8)))
                  (map Z.of_nat (seq 0 256)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in Hall.
  assert (Hin: In (Znth 4 F) (map Z.of_nat (seq 0 256))).
  { apply in_map_iff. exists (Z.to_nat (Znth 4 F)). split; [lia |]. apply in_seq. lia. }
  specialize (Hall _ Hin).
  pose proof (Int.eq_spec (Int.zero_ext 8 (Int.or (Int.repr (Znth 4 F)) (Int.repr 8))) (Int.repr (Z.lor (Znth 4 F) 8)))
    as Heq.
  rewrite Hall in Heq. rewrite Heq.
  change (Vint (Int.repr (Z.lor (Znth 4 F) 8))) with ((fun b : Z => Vint (Int.repr b)) (Z.lor (Znth 4 F) 8)).
  rewrite upd_Znth_map. f_equal.
  unfold rb_frame. rewrite upd_Znth_unfold by lia.
  rewrite sublist_firstn. rewrite sublist_skip by lia. unfold byte_at. f_equal.
Qed.

(* streamed: on the changed frame of new_frame, a run of stream_all from a new context never returns 0 *)
Lemma rb_stream_done d fcs maxw did c cap dst oc y r z :
  nf_ok (Zlength d) fcs maxw did c -> 0 <= fcs < 2 ^ 64 -> 0 <= did < 2 ^ 32 -> bytes_ok d ->
  stream_run (rb_frame (nf_bytes d fcs did c)) cap dst (sa_init dctx_init oc) y ->
  stream_call (rb_frame (nf_bytes d fcs did c)) cap dst y r z -> sa_done z = 0.
Proof.
  intros Hok Hfcs Hdid Hd Hrun Hcall.
  assert (HS: series_frames_m (dmode_w (dmode_of (dc_par dctx_init))) (fst (st_sel dctx_init))
                (snd (st_sel dctx_init)) no_wlim (rb_frame (nf_bytes d fcs did c)) = (nil, TDetHdr))
    by (apply (rb_series_frames _ _ _ _ d fcs maxw did c); auto).
  apply (stream_no_end (rb_frame (nf_bytes d fcs did c)) cap dst dctx_init oc y r z); [| reflexivity | reflexivity | rewrite HS; reflexivity | rewrite HS; discriminate
                         | exact Hrun | exact Hcall].
  apply rb_frame_ok. apply (Zstd.proof.harness.frames.FFacts.nf_bytes_ok d fcs maxw did c Hok Hd).
Qed.

(* a branch closed by a hypothesis x <> x *)
Ltac neq_refl := exfalso; match goal with Hx: ?a <> ?a |- _ => apply Hx; reflexivity end.

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
   Zstd.proof.zstd.Spec_util.ZSTD_isError_spec; ZSTD_decompress_spec; ZSTD_createDStream_spec DC;
   gp_assert_spec;
   out_of_memory_spec; @stream_all_spec CompSpecs DC DD; @any_bytes_spec CompSpecs; upto_spec;
   @new_frame_spec CompSpecs].

(* main: the frame with the Reserved_bit set is refused one-shot (an error) and never reported complete by the
   stream *)
Lemma body_main_G0 : semax_body Vprog G0 f_main main_spec.
Proof.
  change (semax_body Vprog G0 f_main (_main, WITH gv: globals PRE [] VST.floyd.VSU.main_pre
    Zstd.contracts.rj_reserved_bit.whole_prog tt gv POST [tint] (fun _ : environ => TT))).
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
  destruct (eq_dec data nullval) as [Hd0|Hd0].
  { (* out of memory: no data, no frame; the run ends *)
    subst data. forward_if; [| contradiction]. forward. forward.
    forward_call 9223372036854775807. Intros u.
    forward_call (tarray tuchar u, gv). { simpl. rep_lia. }
    Intros dst.
    forward_call gv. Intros zds.
    repeat apply -> seq_assoc. apply semax_if_seq.
    forward_if; [| contradiction]. forward.
    repeat apply -> seq_assoc. apply semax_if_seq.
    forward_if; [| discriminate]. forward.
    forward_if; [forward; cancel | discriminate]. }
  subst n.
  unfold mbytes at 1. rewrite if_false by exact Hd0. Intros.
  assert_PROP (isptr data) as Hdp by entailer!.
  forward_if; [destruct data; try contradiction; discriminate |].
  sep_apply (tok_to_Z Ews (Zlength l) data).
  forward_call (gv, Ews, data, l, Zlength l, 2 ^ 27, 0, Tsh, v_len,
                Zstd.proof.zstd.Spec_xxh.pw_token Ews (tarray tuchar (Zlength l)) data).
  { simpl pw_pred. unfold Zstd.proof.zstd.Base.CompSpecs. cancel. }
  { apply tok_wvp. assumption. }
  Intros vret. destruct vret as [q d']. cbn [fst snd] in *.
  simpl pw_pred. unfold Zstd.proof.zstd.Base.CompSpecs. sep_apply (tok_of_Z Ews (Zlength l) data).
  forward.
  forward_call 9223372036854775807. Intros cap.
  forward_call (tarray tuchar cap, gv). { simpl. rep_lia. }
  Intros dst.
  forward_call gv. Intros zds.
  destruct (eq_dec q nullval) as [Hq0|Hq0].
  { (* out of memory in new_frame: no frame; the run ends *)
    subst q. repeat apply -> seq_assoc. apply semax_if_seq.
    forward_if; [| contradiction]. forward.
    repeat apply -> seq_assoc. apply semax_if_seq.
    forward_if; [| discriminate]. forward.
    forward_if; [forward; cancel | discriminate]. }
  Intros c.
  subst d'.
  set (F := nf_bytes l (Zlength l) 0 c) in *.
  unfold mbytes at 1. destruct (eq_dec q nullval) as [C|_]; [contradiction|]. Intros.
  assert_PROP (isptr q) as Hqp by entailer!.
  repeat apply -> seq_assoc. apply semax_if_seq.
  forward_if; [destruct q; try contradiction; discriminate |].
  destruct (eq_dec dst nullval) as [Hdst|Hdst].
  { (* out of memory for dst; the run ends *)
    subst dst. forward.
    repeat apply -> seq_assoc. apply semax_if_seq.
    forward_if; [| neq_refl]. forward.
    forward_if; [forward; cancel | discriminate]. }
  Intros.
  assert_PROP (isptr dst) as Hdstp by entailer!.
  destruct dst as [| | | | | bd od]; try contradiction.
  forward.
  repeat apply -> seq_assoc. apply semax_if_seq.
  forward_if; [discriminate |].
  destruct (eq_dec zds nullval) as [Hz|Hz].
  { (* no context; the run ends *)
    subst zds. forward. forward_if; [forward; cancel | neq_refl]. }
  assert (Hzp: isptr zds) by (apply isptr_of; auto).
  destruct zds as [| | | | | bz oz]; try contradiction.
  forward.
  forward_if; [discriminate |].
  (* frame[4] |= 8: the Reserved_bit *)
  pose proof (Zstd.proof.harness.frames.FFacts.nf_bytes_length l (Zlength l) (2 ^ 27) 0 c H5) as HFl.
  pose proof (Zstd.proof.harness.frames.FFacts.nf_bytes_ok l (Zlength l) (2 ^ 27) 0 c H5 H1) as HFok.
  fold F in HFl, HFok.
  assert (HnB: 26 + 4 * Zlength l <= 2 ^ 63 - 1).
  { unfold PTRDIFF_MAX in H7. change ((2 ^ 63 - 1 - 26) / 4) with 2305843009213693945 in H7. lia. }
  assert (HB4: is_byte (Znth 4 F)) by (apply (proj1 (Forall_Znth F is_byte) HFok); lia).
  unfold is_byte in HB4.
  forward.
  { entailer!. simpl. rep_lia. }
  forward.
  set (S := rb_frame F).
  assert (HSl: Zlength S = Zlength F) by (apply rb_frame_length; lia).
  assert (HSok: bytes_ok S) by (apply rb_frame_ok; exact HFok).
  rewrite (rb_zbytes F HFok) by lia. fold S.
  rewrite <- HSl.
  (* ZSTD_decompress(dst, cap, frame, len), at the decoder's compspecs; the malloc_tokens vouch for the buffers *)
  forward.
  sep_apply (to_Z Ews (Zlength S) (zbytes S) q).
  sep_apply (to_Z_ Ews cap (Vptr bd od)).
  sep_apply (tok_to_Z Ews (Zlength S) q).
  sep_apply (tok_to_Z Ews cap (Vptr bd od)).
  sep_apply (pws_fold (tarray tuchar (Zlength S)) q (tarray tuchar cap) (Vptr bd od)).
  set (W := [pw_token Ews (tarray tuchar (Zlength S)) q; pw_token Ews (tarray tuchar cap) (Vptr bd od)]).
  assert (HbS: buf_ok W Ews (Zlength S) q) by (apply buf_ok_tok; [simpl; tauto | auto | lia | auto]).
  assert (Hbd: buf_ok W Ews cap (Vptr bd od)) by (apply buf_ok_tok; [simpl; tauto | auto | lia | auto]).
  forward_call (W, gv, Ews, Vptr bd od, cap, Ews, q, S).
  Intros vret. destruct vret as [r out]. cbn [fst snd] in *. rewrite mbuf_isptr by auto.
  match goal with H1: 0 <= r <= _, H2: Zlength out = _, H3: oneshot_ok _ _ _ _ _ _ |- _ =>
    rename H1 into Hr; rename H2 into Hout; rename H3 into Hok1 end.
  (* the model: zstd certainly refuses the frame, so the result is an error *)
  assert (Herr: is_error_code r = true).
  { destruct Hok1 as [_ Hc]. unfold S, F in Hc.
    rewrite (rb_decode_series md_dflt sel_none (Some no_dict) no_wlim l (Zlength l) (2 ^ 27) 0 c) in Hc
      by (auto; rep_lia).
    exact Hc. }
  forward.
  (* stream_all(zds, frame, len, dst, cap, &written, &completed), at the harness's compspecs *)
  forward.
  sep_apply (of_Z Ews (Zlength S) (zbytes S) q).
  sep_apply (of_Z Ews cap out (Vptr bd od)).
  sep_apply (andp_left1 (DC gv (Vptr bz oz) dctx_init) (valid_pointer (Vptr bz oz)) (DC gv (Vptr bz oz) dctx_init)
    (derives_refl _)).
  forward_call (W, gv, Vptr bz oz, dctx_init, Ews, q, S, Ews, Vptr bd od, cap, out, Tsh, v_written, Tsh,
                v_completed).
  { simpl. cancel. }
  { unfold stream_dict_ok. simpl. split; [exact Logic.I | split; [constructor | reflexivity]]. }
  Intros vret. destruct vret as [[r2 y] z]. cbn [fst snd] in *.
  match goal with H1: stream_run _ _ _ _ _, H2: stream_call _ _ _ _ _ _ |- _ =>
    rename H1 into Hrun; rename H2 into Hcall end.
  (* the model: no call of the stream returns 0 *)
  assert (Hdone: sa_done z = 0).
  { unfold S, F in Hrun, Hcall. eapply rb_stream_done; eauto; rep_lia. }
  assert (Hr2: 0 <= r2 <= Int64.max_unsigned) by (destruct Hcall as (? & ? & ? & _ & _ & ? & _); assumption).
  rewrite Hdone.
  forward.
  (* out_of_memory(result) || out_of_memory(last): a memory error ends the run *)
  forward_call r.
  repeat apply -> seq_assoc. apply semax_if_seq.
  forward_if.
  { forward. forward_if; [forward; cancel | discriminate]. }
  (* t'14 = out_of_memory(last); t'13 = (_Bool) t'14: the call, then the cast as a statement of its own *)
  eapply semax_seq'.
  forward_call r2.
  forward. apply andp_left2. apply derives_refl.
  abbreviate_semax.
  forward_if.
  { forward. cancel. }
  (* the check: ZSTD_isError(result) && completed == 0 *)
  forward_call r.
  rewrite Herr.
  repeat apply -> seq_assoc. apply semax_if_seq.
  forward_if; [| discriminate].
  forward. forward.
  forward_call Int.one.
  forward.
  cancel.
Qed.

End Main.
(* ---------- from G0 to Gprog (API DC DD) Hs ---------- *)

(* the harness's own functions besides main (in the order of helper_ids): the frames kit's helpers *)
Definition Hs DC DD : funspecs :=
  [out_of_memory_spec; @copy_of_spec CompSpecs; @Zstd.proof.harness.frames.FStreamSpec.stream_all_spec CompSpecs DC DD; @any_bytes_spec CompSpecs;
   upto_spec; @put_le_spec CompSpecs; @new_frame_spec CompSpecs].

Lemma Externals_eq : Externals =
  [nondet_u8_spec; nondet_size_spec; nondet_bytes_nn_spec; gp_assert_spec; gp_assume_spec].
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
  [nondet_u8_spec; nondet_size_spec; nondet_bytes_nn_spec; gp_assert_spec; gp_assume_spec] ++
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

Theorem rj_reserved_bit_ok :
  forall (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred),
    HarnessOK (API DC DD) (Hs DC DD).
Proof.
  intros DC DD. split.
  - vm_compute. reflexivity.
  - constructor; [| constructor; [| constructor; [| constructor; [| constructor; [| constructor;
      [| constructor; [| constructor; [| constructor]]]]]]]].
    + kit_body Zstd.harness.rj_reserved_bit.code.f_out_of_memory FSpecs.f_out_of_memory G_out_of_memory
        (@Zstd.proof.harness.frames.FBodiesSmall.body_out_of_memory CompSpecs).
    + kit_body Zstd.harness.rj_reserved_bit.code.f_copy_of FSpecs.f_copy_of (@G_copy_of CompSpecs)
        (@Zstd.proof.harness.frames.FBodiesSmall.body_copy_of CompSpecs).
    + kit_body Zstd.harness.rj_reserved_bit.code.f_stream_all Zstd.proof.harness.frames.FStreamSpec.f_stream_all
        (Zstd.proof.harness.frames.FStreamSpec.G_stream_all DC DD)
        (@Zstd.proof.harness.frames.FBodyStreamAll.body_stream_all CompSpecs
           ltac:(Zstd.proof.harness.frames.FBodyStreamAll.fs_cspecs_sub) DC DD).
    + kit_body Zstd.harness.rj_reserved_bit.code.f_any_bytes FSpecs.f_any_bytes (@G_any_bytes CompSpecs)
        (@Zstd.proof.harness.frames.FBodiesSmall.body_any_bytes CompSpecs).
    + kit_body Zstd.harness.rj_reserved_bit.code.f_upto FSpecs.f_upto G_upto
        (@Zstd.proof.harness.frames.FBodiesSmall.body_upto CompSpecs).
    + kit_body Zstd.harness.rj_reserved_bit.code.f_put_le FSpecs.f_put_le G_put_le
        (@Zstd.proof.harness.frames.FBodiesSmall.body_put_le CompSpecs).
    + kit_body Zstd.harness.rj_reserved_bit.code.f_new_frame FSpecs.f_new_frame (@G_new_frame CompSpecs)
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
