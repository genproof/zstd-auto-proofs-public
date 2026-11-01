(* The harness obligation of rj_content_size (harness/rj_content_size.c): for ANY predicates DC, DD of the
   decoder's API (Spec_api6), with the API [ZSTD_isError; ZSTD_getErrorCode; ZSTD_decompress; ZSTD_createDStream;
   ZSTD_decompressStream; ZSTD_XXH64] (the second for out_of_memory, the last for new_frame's checksums), the helpers of laws_common.h and
   frames.h (proved once in the frames kit) and main satisfy their specifications.

   main builds a frame of new_frame whose Frame_Content_Size field declares a size other than its content's
   (Facts_rj_content_size).  The model says zstd certainly refuses this series (model/Refuse.v,
   series_refused_m) and its walk finds no complete frame in it.  One-shot: ZSTD_decompress's specification
   (oneshot_ok, the branch of the series the model does not decode) then gives an error.  Streamed: no call of
   stream_all returns 0 (FStreamRefused.stream_refused_no_end), so *completed stays 0.  The buffers have any size up
   to PTRDIFF_MAX: this needs the one-shot and streaming specifications with sizes up to 2 ^ 63 - 1 (stage 1 of
   the size bounds of Spec_api6) and their refusal claims (stage 2, item (R)). *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Pick.
Require Export Zstd.proof.zstd.Spec_api6.
Require Export Zstd.proof.harness.rj_content_size.HOK_rj_content_size.
Require Zstd.proof.top.MainPre6.
Require Import Zstd.proof.zstd.NullBuf.
Require Zstd.proof.harness.HCsConv.
Require Zstd.proof.harness.frames.FSpecs Zstd.proof.harness.frames.FBodiesSmall Zstd.proof.harness.frames.FTransfer.
Require Import Zstd.proof.harness.frames.FFacts.
Require Zstd.proof.harness.frames.FStreamSpec Zstd.proof.harness.frames.FBodyStreamAll.
Require Zstd.proof.harness.frames.FBodyNewFrame.
Require Import Zstd.proof.harness.frames.FStreamRefused.
Require Import Zstd.proof.harness.rj_content_size.Facts_rj_content_size.
Import Zstd.proof.harness.frames.FSpecs Zstd.proof.harness.frames.FStreamSpec.
(* the harness's own names (Vprog, Gprog, CompSpecs, main_spec) over those of the decoder's specifications *)
Import Zstd.proof.harness.rj_content_size.HOK_rj_content_size.

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
    (QPprog_vars Zstd.contracts.rj_content_size.whole_prog).
Proof.
  apply Forall_forall. intros [i v] Hin. apply make_tycontext_g_isSome.
  unfold Vprog, QPvarspecs. rewrite map_map.
  apply in_map_iff. exists (i, v). split; [reflexivity | exact Hin].
Qed.

(* main's precondition: the decoder's globals, split off as in MainPre6.main_pre_fact6 (whose list of
   programs has the x_ laws only) *)
Lemma pre_globals gv :
  InitGPred (Vardefs Zstd.contracts.rj_content_size.whole_prog) gv |-- zstd_globals gv * TT.
Proof.
  assert (Hincl: incl Zstd.proof.top.MainPre6.zstd_vardefs (Vardefs Zstd.contracts.rj_content_size.whole_prog)).
  { apply Zstd.proof.top.MainPre6.MP_incl_Vardefs; vm_compute; reflexivity. }
  rewrite (Zstd.proof.top.MainPre6.MP_split_zstd _ gv Hincl).
  apply sepcon_derives; [apply Zstd.proof.top.MainPre6.zstd_vardefs_globals | apply TT_right].
Qed.

(* the variable declared as the 8 bytes pick(declared) writes *)
Lemma fc_bytes8 p : field_compatible tulong [] p -> field_compatible (tarray tuchar 8) [] p.
Proof.
  intros (Hp & Hl & Hs & Ha & _). destruct p; try contradiction.
  split; [exact I | split; [reflexivity | split; [| split; [| exact I]]]].
  - simpl in Hs |- *. exact Hs.
  - apply align_compatible_rec_Tarray. intros j Hj.
    eapply align_compatible_rec_by_value; [reflexivity |]. apply Z.divide_1_l.
Qed.

Lemma ulong_bytes p : field_compatible tulong [] p ->
  data_at_ Tsh tulong p |-- data_at_ Tsh (tarray tuchar 8) p.
Proof.
  intros Hfc. rewrite !data_at__memory_block. normalize.
  apply andp_right; [apply prop_right; apply fc_bytes8; exact Hfc | apply derives_refl].
Qed.

(* ---------- byte arrays and tokens between the harness's compspecs and the decoder's ---------- *)

Lemma to_Z sh n v p :
  @data_at CompSpecs sh (tarray tuchar n) v p |-- @data_at Zstd.units.Zstd.CS sh (tarray tuchar n) v p.
Proof. rewrite (Zstd.proof.harness.HCsConv.data_at_bytes_cs CompSpecs Zstd.units.Zstd.CS). apply derives_refl. Qed.

Lemma of_Z sh n v p :
  @data_at Zstd.units.Zstd.CS sh (tarray tuchar n) v p |-- @data_at CompSpecs sh (tarray tuchar n) v p.
Proof. rewrite (Zstd.proof.harness.HCsConv.data_at_bytes_cs CompSpecs Zstd.units.Zstd.CS). apply derives_refl. Qed.

#[local] Instance CCE_HZ : change_composite_env CompSpecs Zstd.units.Zstd.CS.
Proof. make_cs_preserve CompSpecs Zstd.units.Zstd.CS. Defined.

#[local] Instance CCE_BH : change_composite_env Zstd.proof.zstd.Base.CompSpecs CompSpecs.
Proof. make_cs_preserve Zstd.proof.zstd.Base.CompSpecs CompSpecs. Defined.

Lemma to_Z_ sh n p :
  @data_at_ CompSpecs sh (tarray tuchar n) p |-- @data_at_ Zstd.units.Zstd.CS sh (tarray tuchar n) p.
Proof. rewrite (@data_at__change_composite _ _ CCE_HZ sh (tarray tuchar n)) by reflexivity. apply derives_refl. Qed.

Lemma of_Z_ sh n p :
  @data_at_ Zstd.units.Zstd.CS sh (tarray tuchar n) p |-- @data_at_ CompSpecs sh (tarray tuchar n) p.
Proof. rewrite (@data_at__change_composite _ _ CCE_HZ sh (tarray tuchar n)) by reflexivity. apply derives_refl. Qed.

Lemma tok_to_Z sh n p :
  @malloc_token CompSpecs sh (tarray tuchar n) p |-- @malloc_token Zstd.units.Zstd.CS sh (tarray tuchar n) p.
Proof. rewrite (@malloc_token_change_composite _ _ CCE_HZ sh (tarray tuchar n)) by reflexivity. apply derives_refl. Qed.

Lemma tok_of_Z sh n p :
  @malloc_token Zstd.units.Zstd.CS sh (tarray tuchar n) p |-- @malloc_token CompSpecs sh (tarray tuchar n) p.
Proof. rewrite (@malloc_token_change_composite _ _ CCE_HZ sh (tarray tuchar n)) by reflexivity. apply derives_refl. Qed.

(* ---------- the pointer witnesses: the malloc_tokens of the buffers ---------- *)

(* a malloc'ed block of 0 bytes: its token shows that its address is valid (new_frame on empty data) *)
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

Lemma isptr_of p : is_pointer_or_null p -> p <> nullval -> isptr p.
Proof. intros H1 H2. destruct p; simpl in *; auto. subst. contradiction. Qed.

(* the descriptor byte's tests in C *)
Lemma shr6 x : 0 <= x < 256 -> Int.shr (Int.repr x) (Int.repr 6) = Int.repr (Z.shiftr x 6).
Proof. intros. unfold Int.shr. rewrite Int.signed_repr, Int.unsigned_repr by rep_lia. reflexivity. Qed.

Lemma and32 x : 0 <= x < 256 -> Int.and (Int.repr x) (Int.repr 32) = Int.repr (Z.land x 32).
Proof. intros. unfold Int.and. rewrite !Int.unsigned_repr by rep_lia. reflexivity. Qed.

(* ---------- the model ---------- *)

(* a refused series whose walk finds no complete frame ends TUnk: the walk stops at its first frame *)
Lemma refused_first_tunk md sel cur wlim s :
  series_refused_m md sel cur wlim s -> fst (series_frames_m md sel cur wlim s) = nil ->
  snd (series_frames_m md sel cur wlim s) = TUnk.
Proof.
  unfold series_refused_m, series_frames_m. generalize (S (length s)) as fuel. intros [|f] Href Hnil;
    [contradiction |].
  cbn [walk_refused walk_m] in *.
  destruct (Zlength s <? starting_len (md_magicless md)).
  - destruct (Zlength s =? 0) eqn:E; [apply Z.eqb_eq in E; contradiction | reflexivity].
  - destruct (negb (md_magicless md) && is_skippable_magic (le_field s 0 4))%bool.
    + destruct (skippable_frame_size s); [| reflexivity].
      destruct (walk_m _ _ _ _ _ _ _); discriminate.
    + destruct (frame_dict _ _ _ _); [| contradiction].
      destruct (decode_frame_m _ _ _ _); try contradiction; [| reflexivity].
      destruct (walk_m _ _ _ _ _ _ _); discriminate.
Qed.

(* the descriptor's bit 5 is Single_Segment_flag *)
Lemma cs_fhd_bit5 h : 0 <= nh_fcs_flag h <= 3 -> In (nh_bits h) [0; 4; 16; 20] -> 0 <= nh_did_flag h <= 3 ->
  Z.land (nh_fhd h) 32 = 32 * zb (nh_single h).
Proof.
  destruct h as [f sg b df wd]. intros Hf Hb Hd. cbn [nh_fcs_flag nh_single nh_bits nh_did_flag nh_wd] in *.
  unfold nh_fhd; cbn [nh_fcs_flag nh_single nh_bits nh_did_flag nh_wd].
  destruct (ff_flag_cases _ Hf) as [-> | [-> | [-> | ->]]];
  destruct (ff_flag_cases _ Hd) as [-> | [-> | [-> | ->]]];
  destruct Hb as [<- | [<- | [<- | [<- | []]]]]; destruct sg; vm_compute; reflexivity.
Qed.

(* the fifth byte of new_frame's frame is its descriptor: a byte whose bits 7-6 are the Frame_Content_Size_flag and
   whose bit 5 is the Single_Segment_flag *)
Lemma cs_byte4 d fcs maxw c : nf_ok (Zlength d) fcs maxw 0 c ->
  Znth 4 (nf_bytes d fcs 0 c) = nh_fhd (nc_hdr c) /\ 0 <= nh_fhd (nc_hdr c) < 256 /\
  Z.shiftr (nh_fhd (nc_hdr c)) 6 = nh_fcs_flag (nc_hdr c) /\
  Z.land (nh_fhd (nc_hdr c)) 32 = 32 * zb (nh_single (nc_hdr c)).
Proof.
  intros [Hh _].
  pose proof Hh as (Hf & _ & _ & _ & _ & Hb & Hd & _).
  destruct (ff_fhd_facts _ Hf Hb Hd) as (Hr & _ & _ & Hs6 & _).
  split; [| split; [exact Hr | split; [exact Hs6 | apply cs_fhd_bit5; assumption]]].
  unfold nf_bytes, nh_bytes. rewrite <- !app_assoc.
  change (le_bytes 4 ZSTD_MAGICNUMBER) with [40; 181; 47; 253]. reflexivity.
Qed.

(* a new stream context: the default mode, no dictionary selection, no dictionary *)
Lemma init_sel : st_sel dctx_init = (sel_none, Some no_dict).
Proof. reflexivity. Qed.

Lemma init_mode : md_magicless (dmode_w (dmode_of (dc_par dctx_init))) = false /\
  ZSTD_BLOCKSIZE_MAX <= md_bmax (dmode_w (dmode_of (dc_par dctx_init))).
Proof. split; [reflexivity | cbv; discriminate]. Qed.

(* a new stream context has no dictionary resources *)
Lemma res_none_i DD0 gv sh :
  emp |-- dict_res DD0 gv sh (dc_dict dctx_init) * set_res DD0 gv sh (dc_set dctx_init) (dc_dict dctx_init).
Proof. simpl. rewrite emp_sepcon. apply derives_refl. Qed.

(* the context's resource without its validity *)
Lemma drop_vp (P: mpred) p : P && valid_pointer p |-- P.
Proof. apply andp_left1, derives_refl. Qed.

(* an impossible branch of an if *)
Ltac nope := solve [exfalso; first [congruence | discriminate | contradiction | lia]].

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
   nondet_bytes_nn_spec; gp_assert_spec;
   out_of_memory_spec; @stream_all_spec CompSpecs DC DD; @any_bytes_spec CompSpecs; upto_spec;
   @new_frame_spec CompSpecs].

(* main: the frame with the wrong declared size is refused one-shot and never reported complete by the stream (the
   harness ends the run on the declared size 2^64 - 1, which zstd reads as ZSTD_CONTENTSIZE_UNKNOWN) *)
Lemma body_main_G0 : semax_body Vprog G0 f_main main_spec.
Proof.
  change (semax_body Vprog G0 f_main (_main, WITH gv: globals PRE [] VST.floyd.VSU.main_pre
    Zstd.contracts.rj_content_size.whole_prog tt gv POST [tint] (fun _ : environ => TT))).
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
  (* pick(declared) *)
  assert_PROP (field_compatible tulong [] v_declared) as FCd by entailer!.
  sep_apply (ulong_bytes v_declared FCd).
  forward_call (v_declared, 8, Tsh).
  Intros db.
  match goal with H: Zlength db = 8, H': Forall _ db |- _ => sep_apply (pick_tulong Tsh db v_declared H H' FCd) end.
  Intros dv.
  forward_call (gv, n).
  Intros vret. destruct vret as [data l]. cbn [fst snd] in *.
  repeat apply -> seq_assoc. apply semax_if_seq.
  destruct (eq_dec data nullval) as [Hd0|Hd0].
  { (* out of memory: no data, no frame; the run ends *)
    subst data. forward_if; [| exfalso; auto]. forward. forward.
    forward_call (9223372036854775807 - n). Intros u. forward.
    forward_call (tarray tuchar (n + u), gv). { simpl. rep_lia. }
    Intros dst.
    forward_call gv. Intros zds.
    repeat apply -> seq_assoc. apply semax_if_seq.
    forward_if; [| exfalso; auto]. forward.
    repeat apply -> seq_assoc. apply semax_if_seq.
    forward_if; [| discriminate]. forward.
    repeat apply -> seq_assoc. apply semax_if_seq.
    forward_if; [| discriminate]. forward.
    repeat apply -> seq_assoc. apply semax_if_seq.
    forward_if; [| discriminate]. forward.
    forward_if; [forward; cancel | discriminate]. }
  subst n. unfold mbytes at 1. rewrite if_false by exact Hd0. Intros.
  assert_PROP (isptr data) as Hdp by entailer!.
  forward_if; [destruct data; try contradiction; discriminate |].
  forward.
  sep_apply (tok_to_Z Ews (Zlength l) data).
  rewrite <- (Int64.repr_unsigned dv).
  pose proof (Int64.unsigned_range_2 dv) as Hdv.
  forward_call (gv, Ews, data, l, Int64.unsigned dv, 2 ^ 27, 0, Tsh, v_len,
                Zstd.proof.zstd.Spec_xxh.pw_token Ews (tarray tuchar (Zlength l)) data).
  { simpl pw_pred. unfold Zstd.proof.zstd.Base.CompSpecs. cancel. }
  { apply tok_wvp. assumption. }
  Intros vret. destruct vret as [q d']. cbn [fst snd] in *.
  simpl pw_pred. unfold Zstd.proof.zstd.Base.CompSpecs. sep_apply (tok_of_Z Ews (Zlength l) data).
  set (fcs := Int64.unsigned dv) in *.
  forward. forward.
  forward_call (9223372036854775807 - Zlength l).
  Intros u. forward.
  forward_call (tarray tuchar (Zlength l + u), gv). { simpl. rep_lia. }
  Intros dst.
  forward_call gv. Intros zds.
  repeat apply -> seq_assoc. apply semax_if_seq.
  destruct (eq_dec q nullval) as [Hq0|Hq0].
  { (* out of memory in new_frame: no frame; the run ends *)
    subst q. forward_if; [| exfalso; auto]. forward.
    repeat apply -> seq_assoc. apply semax_if_seq.
    forward_if; [| discriminate]. forward.
    repeat apply -> seq_assoc. apply semax_if_seq.
    forward_if; [| discriminate]. forward.
    repeat apply -> seq_assoc. apply semax_if_seq.
    forward_if; [| discriminate]. forward.
    forward_if; [forward; cancel | discriminate]. }
  Intros c.
  match goal with Hx: nf_ok _ _ _ _ c |- _ => rename Hx into Hok end.
  match goal with Hx: d' = nf_data l c |- _ => subst d' end.
  match goal with Hx: Zlength l <= (PTRDIFF_MAX - 26) / 4 |- _ => rename Hx into Hnb end.
  pose proof (nf_bytes_length l fcs (2 ^ 27) 0 c Hok) as HFl.
  pose proof (nf_bytes_ok l fcs (2 ^ 27) 0 c Hok H3) as HFok.
  destruct (cs_byte4 l fcs (2 ^ 27) c Hok) as (B4 & Bfhd & Bshr & Band).
  assert (HnB: 26 + 4 * Zlength l <= 2 ^ 63 - 1).
  { unfold PTRDIFF_MAX in Hnb. change ((2 ^ 63 - 1 - 26) / 4) with 2305843009213693945 in Hnb. lia. }
  set (F := nf_bytes l fcs 0 c) in *.
  unfold mbytes at 1. destruct (eq_dec q nullval) as [C|_]; [contradiction|]. Intros.
  assert_PROP (isptr q) as Hqp by entailer!.
  forward_if; [destruct q; try contradiction; discriminate |].
  destruct (eq_dec dst nullval) as [Hdst|Hdst].
  { (* out of memory for dst; the run ends *)
    subst dst. forward.
    repeat apply -> seq_assoc. apply semax_if_seq.
    forward_if; [| nope]. forward.
    repeat apply -> seq_assoc. apply semax_if_seq.
    forward_if; [| nope]. forward.
    repeat apply -> seq_assoc. apply semax_if_seq.
    forward_if; [| nope]. forward.
    forward_if; [forward; cancel | nope]. }
  destruct (eq_dec dst nullval) as [C|_]; [contradiction|]. Intros.
  assert_PROP (isptr dst) as Hdstp by entailer!.
  destruct dst as [| | | | | bd od]; try contradiction.
  forward.
  repeat apply -> seq_assoc. apply semax_if_seq.
  forward_if; [nope |].
  destruct (eq_dec zds nullval) as [Hz|Hz].
  { (* out of memory for the stream; the run ends *)
    subst zds. forward.
    repeat apply -> seq_assoc. apply semax_if_seq.
    forward_if; [| nope]. forward.
    repeat apply -> seq_assoc. apply semax_if_seq.
    forward_if; [| nope]. forward.
    forward_if; [forward; cancel | nope]. }
  destruct (eq_dec zds nullval) as [C|_]; [contradiction|].
  assert (Hzp: isptr zds) by (apply isptr_of; assumption).
  destruct zds as [| | | | | bz oz]; try contradiction.
  forward.
  repeat apply -> seq_assoc. apply semax_if_seq.
  forward_if; [nope |].
  forward. forward.
  repeat apply -> seq_assoc. apply semax_if_seq.
  forward_if; [forward; forward_if; [forward; cancel | nope] |].
  match goal with Hx: context [zeq fcs] |- _ => rename Hx into Hz10 end.
  assert (Hne: fcs <> Zlength l) by (destruct (zeq fcs (Zlength l)); [discriminate | assumption]).
  forward. forward.
  forward_if; [forward; cancel |].
  (* the run goes on only with a declared size other than ZSTD_CONTENTSIZE_UNKNOWN *)
  match goal with Hx: Int64.repr fcs <> Int64.sub _ _ |- _ => rename Hx into Hz11 end.
  assert (Hknown: fcs <> 2 ^ 64 - 1) by (intro E; apply Hz11; rewrite E; apply Int64.same_if_eq; reflexivity).
  assert (Z4: Znth 4 (zbytes F) = Vint (Int.repr (nh_fhd (nc_hdr c)))).
  { rewrite Znth_map by lia. rewrite B4. reflexivity. }
  assert (HFe: F = nf_bytes l fcs 0 c) by reflexivity.
  clearbody F.
  forward; try solve [entailer!; rewrite ?Z4, ?B4; simpl; rep_lia].
  try rewrite Z4; try rewrite B4.
  assert (Hfl: 0 <= nh_fcs_flag (nc_hdr c) <= 3) by (destruct Hok as [(Hfl & _) _]; exact Hfl).
  assert (Hcase: (nh_fcs_flag (nc_hdr c) = 0 /\ nh_single (nc_hdr c) = false) \/
                 (nh_fcs_flag (nc_hdr c) <> 0 \/ nh_single (nc_hdr c) = true)).
  { destruct (nh_single (nc_hdr c)); [right; right; reflexivity |].
    destruct (Z.eq_dec (nh_fcs_flag (nc_hdr c)) 0); [left; auto | right; left; auto]. }
  destruct Hcase as [[F0 S0] | Hfield].
  { (* no Frame_Content_Size field: the run ends *)
    repeat apply -> seq_assoc. apply semax_if_seq.
    forward_if;
      [| match goal with Hx: Int.shr _ _ <> _ |- _ => rewrite shr6, Bshr, F0 in Hx by exact Bfhd; nope end].
    forward; try solve [entailer!; rewrite ?Z4, ?B4; simpl; rep_lia].
    try rewrite Z4; try rewrite B4.
    forward.
    rewrite and32 by exact Bfhd. rewrite Band, S0. change (32 * zb false) with 0.
    forward_if; [forward; cancel | nope]. }
  (* a Frame_Content_Size field: t'12 = 0 either way *)
  forward_if (temp _t'12 (Vint Int.zero)).
  { match goal with Hx: Int.shr _ _ = _ |- _ => rewrite shr6, Bshr in Hx by exact Bfhd; rename Hx into H14 end.
    apply repr_inj_unsigned in H14; [| rep_lia | rep_lia].
    assert (Esg: nh_single (nc_hdr c) = true) by (destruct Hfield; [contradiction | assumption]).
    forward; try solve [entailer!; rewrite ?Z4, ?B4; simpl; rep_lia].
    try rewrite Z4; try rewrite B4.
    forward.
    rewrite and32 by exact Bfhd. rewrite Band, Esg. change (32 * zb true) with 32.
    entailer!. }
  { forward. entailer!. }
  forward_if; [nope |].
  forward.
  rewrite add64_repr.
  set (cap := Zlength l + u) in *.
  sep_apply (to_Z Ews (Zlength F) (zbytes F) q).
  sep_apply (to_Z_ Ews cap (Vptr bd od)).
  sep_apply (tok_to_Z Ews (Zlength F) q).
  sep_apply (tok_to_Z Ews cap (Vptr bd od)).
  sep_apply (pws_fold (tarray tuchar (Zlength F)) q (tarray tuchar cap) (Vptr bd od)).
  forward_call ([pw_token Ews (tarray tuchar (Zlength F)) q; pw_token Ews (tarray tuchar cap) (Vptr bd od)],
                gv, Ews, Vptr bd od, cap, Ews, q, F).
  { split; (apply buf_ok_tok; [simpl; tauto | auto | unfold cap; lia | auto]). }
  Intros vret. destruct vret as [r out]. cbn [fst snd] in *. rewrite mbuf_isptr by auto.
  match goal with H1: 0 <= r <= _, H2: Zlength out = _, H3: oneshot_ok _ _ _ _ _ _ |- _ =>
    rename H1 into Hr; rename H2 into Hout; rename H3 into Hok1 end.
  (* the model: the series is refused, one-shot and streamed, with no complete frame *)
  assert (Hl63: Zlength l < 2 ^ 63) by lia.
  assert (Hfcs: 0 <= fcs < 2 ^ 64 - 1) by (unfold Int64.max_unsigned, Int64.modulus in Hdv; simpl in Hdv; lia).
  destruct (cs_series_refused md_dflt no_dict l fcs c Hok H3 Hl63 Hfcs Hne Hfield eq_refl ltac:(cbv; discriminate))
    as [Href1 Hnil1].
  rewrite <- HFe in Href1, Hnil1.
  assert (Herr: is_error_code r = true).
  { destruct Hok1 as [_ Hc].
    unfold decode_series_m in Hc.
    rewrite (surjective_pairing (series_frames_m md_dflt sel_none (Some no_dict) no_wlim F)) in Hc.
    rewrite (refused_first_tunk _ _ _ _ _ Href1 Hnil1) in Hc.
    exact (Hc Href1). }
  forward. forward.
  (* stream_all(zds, frame, len, dst, cap, &written, &completed), at the harness's compspecs *)
  sep_apply (of_Z Ews (Zlength F) (zbytes F) q).
  sep_apply (of_Z Ews cap out (Vptr bd od)).
  sep_apply (drop_vp (DC gv (Vptr bz oz) dctx_init) (Vptr bz oz)).
  sep_apply (res_none_i DD gv Ews).
  forward_call ([pw_token Ews (tarray tuchar (Zlength F)) q; pw_token Ews (tarray tuchar cap) (Vptr bd od)],
                gv, Vptr bz oz, dctx_init, Ews, q, F, Ews, Vptr bd od, cap, out, Tsh, v_written, Tsh, v_completed).
  { cancel. }
  { split; [unfold stream_dict_ok; simpl; auto |].
    split; (apply buf_ok_tok; [simpl; tauto | auto | unfold cap; lia | auto]). }
  Intros vret. destruct vret as [[r2 y] z]. cbn [fst snd] in *.
  match goal with H1: stream_run _ _ _ _ _, H2: stream_call _ _ _ _ _ _ |- _ =>
    rename H1 into Hrun; rename H2 into Hcall end.
  (* streamed: no call returned 0 *)
  assert (Hdone: sa_done z = 0).
  { destruct (cs_series_refused (dmode_w (dmode_of (dc_par dctx_init))) no_dict l fcs c Hok H3 Hl63 Hfcs Hne Hfield
                eq_refl ltac:(cbv; discriminate)) as [Href2 Hnil2].
    rewrite <- HFe in Href2, Hnil2.
    apply (stream_refused_no_end F cap (Vptr bd od) dctx_init out y r2 z HFok eq_refl eq_refl);
      [exact Href2 | exact Hnil2 | exact Hrun | exact Hcall]. }
  assert (Hr2: 0 <= r2 <= Int64.max_unsigned) by (destruct Hcall as (? & ? & ? & _ & _ & ? & _); assumption).
  forward.
  (* out_of_memory(result) || out_of_memory(last): the run may end *)
  forward_call r.
  repeat apply -> seq_assoc. apply semax_if_seq.
  forward_if.
  { forward. forward_if; [forward; cancel | nope]. }
  (* t'16 = out_of_memory(last); t'15 = (_Bool) t'16: the call, then the cast as a statement of its own *)
  eapply semax_seq'. forward_call r2. forward. apply andp_left2. apply derives_refl. abbreviate_semax.
  destruct (Z.eq_dec (Zstd.proof.zstd.Spec_util.error_of r2) 64) as [Em|Em].
  { forward_if; [forward; cancel | nope]. }
  forward_if; [nope |].
  (* the check: ZSTD_isError(result) && completed == 0 *)
  forward_call r.
  rewrite Herr.
  repeat apply -> seq_assoc. apply semax_if_seq.
  forward_if; [| nope].
  forward. forward.
  rewrite Hdone.
  forward_call Int.one.
  forward. cancel.
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

Theorem rj_content_size_ok :
  forall (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred),
    HarnessOK (API DC DD) (Hs DC DD).
Proof.
  intros DC DD. split.
  - vm_compute. reflexivity.
  - constructor; [| constructor; [| constructor; [| constructor; [| constructor; [| constructor;
      [| constructor; [| constructor; [| constructor]]]]]]]].
    + kit_body Zstd.harness.rj_content_size.code.f_out_of_memory FSpecs.f_out_of_memory G_out_of_memory
        (@Zstd.proof.harness.frames.FBodiesSmall.body_out_of_memory CompSpecs).
    + kit_body Zstd.harness.rj_content_size.code.f_copy_of FSpecs.f_copy_of (@G_copy_of CompSpecs)
        (@Zstd.proof.harness.frames.FBodiesSmall.body_copy_of CompSpecs).
    + kit_body Zstd.harness.rj_content_size.code.f_stream_all Zstd.proof.harness.frames.FStreamSpec.f_stream_all
        (Zstd.proof.harness.frames.FStreamSpec.G_stream_all DC DD)
        (@Zstd.proof.harness.frames.FBodyStreamAll.body_stream_all CompSpecs
           ltac:(Zstd.proof.harness.frames.FBodyStreamAll.fs_cspecs_sub) DC DD).
    + kit_body Zstd.harness.rj_content_size.code.f_any_bytes FSpecs.f_any_bytes (@G_any_bytes CompSpecs)
        (@Zstd.proof.harness.frames.FBodiesSmall.body_any_bytes CompSpecs).
    + kit_body Zstd.harness.rj_content_size.code.f_upto FSpecs.f_upto G_upto
        (@Zstd.proof.harness.frames.FBodiesSmall.body_upto CompSpecs).
    + kit_body Zstd.harness.rj_content_size.code.f_put_le FSpecs.f_put_le G_put_le
        (@Zstd.proof.harness.frames.FBodiesSmall.body_put_le CompSpecs).
    + kit_body Zstd.harness.rj_content_size.code.f_new_frame FSpecs.f_new_frame (@G_new_frame CompSpecs)
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
