(* The harness obligation of rfc_concat (harness/rfc_concat.c), with the API
   [ZSTD_decompress_spec; ZSTD_getErrorCode_spec; ZSTD_XXH64_spec] (out_of_memory reads the error code, new_frame
   computes a checksum with ZSTD_XXH64): the helpers of laws_common.h and frames.h (proved once in the frames kit)
   and main satisfy their specifications.

   main's loop keeps: the first `done` bytes of the data array are the contents of the frames written so far
   (each frame of new_frame leaves its piece as the frame's content, Facts_rfc_concat.rc_content), and the series
   holds these frames one after the other (rc_frames).  After the loop the whole array is the frames' contents.
   ZSTD_decompress's specification (oneshot_ok) with the model's decoding of the series (rc_series): a result that
   is not an error is the series' content, written to dst; an error with a capacity that holds the content is
   ZSTD_error_memory_allocation, which ends the run.  So the check holds.  The buffers have any size up to
   PTRDIFF_MAX: this uses ZSTD_decompress's specification with sizes up to 2 ^ 63 - 1 (stage 1 of the size bounds
   of Spec_api6). *)
Require Import VST.floyd.proofauto.
Require Export Zstd.proof.zstd.Spec_api6.
Require Export Zstd.proof.harness.rfc_concat.HOK_rfc_concat.
Require Zstd.proof.top.MainPre6.
Require Import Zstd.proof.zstd.NullBuf.
Require Zstd.proof.harness.HCsConv.
Require Import Zstd.proof.harness.frames.FSpecs.
Require Zstd.proof.harness.frames.FBodiesSmall Zstd.proof.harness.frames.FBodyNewFrame.
Require Zstd.proof.harness.frames.FTransfer.
Require Import Zstd.proof.harness.frames.FKit.
Require Import Zstd.proof.harness.rfc_concat.Facts_rfc_concat.
Local Open Scope logic.

Local Ltac expand_main_pre ::= idtac.

(* the API of the law *)
Definition API : funspecs :=
  [ZSTD_decompress_spec; Zstd.proof.zstd.Spec_util.ZSTD_getErrorCode_spec; Zstd.proof.zstd.Spec_xxh.ZSTD_XXH64_spec].

(* the harness's own functions besides main, in the order of helper_ids *)
Definition Hs : funspecs :=
  [out_of_memory_spec; copy_of_spec; any_bytes_spec; upto_spec; put_le_spec; join_spec; bytes_eq_spec;
   new_frame_spec].

Lemma Hs_ids : map fst Hs = helper_ids.
Proof. vm_compute. reflexivity. Qed.

(* the context of main's body *)
Definition G : funspecs := Gprog API Hs.

(* ---------- main's precondition, local variables ---------- *)

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
    (QPprog_vars Zstd.contracts.rfc_concat.whole_prog).
Proof.
  apply Forall_forall. intros [i v] Hin. apply make_tycontext_g_isSome.
  unfold Vprog, QPvarspecs. rewrite map_map.
  apply in_map_iff. exists (i, v). split; [reflexivity | exact Hin].
Qed.

(* the decoder's globals, split off as in MainPre6.main_pre_fact6 (whose list of programs has the x_ laws
   only) *)
Lemma pre_globals gv :
  InitGPred (Vardefs Zstd.contracts.rfc_concat.whole_prog) gv |-- zstd_globals gv * TT.
Proof.
  assert (Hincl: incl Zstd.proof.top.MainPre6.zstd_vardefs (Vardefs Zstd.contracts.rfc_concat.whole_prog)).
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

(* ---------- the buffer witnesses of ZSTD_decompress: the malloc_tokens of its two buffers ---------- *)

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

(* ---------- the data array around a piece ---------- *)

(* the array of n bytes as the bytes before the piece, the piece (k bytes from i) and the bytes after it *)
Lemma arr_split3 sh n i k (l: list Z) p :
  0 <= i -> 0 <= k -> i + k <= n -> Zlength l = n ->
  field_compatible (tarray tuchar n) [] p ->
  @data_at CompSpecs sh (tarray tuchar n) (zbytes l) p =
  (data_at sh (tarray tuchar i) (zbytes (sublist 0 i l)) p *
   data_at sh (tarray tuchar k) (zbytes (sublist i (i + k) l)) (offset_val i p) *
   data_at sh (tarray tuchar (n - (i + k))) (zbytes (sublist (i + k) n l)) (offset_val (i + k) p)).
Proof.
  intros. rewrite (split3_data_at_Tarray_tuchar sh n i (i + k)) by (try rewrite Zlength_map; lia).
  change (Tarray tuchar n noattr) with (tarray tuchar n). rewrite !arr_field_address0 by (auto; lia).
  replace (i + k - i) with k by lia. simpl sizeof. rewrite !Z.mul_1_l, !sublist_map. reflexivity.
Qed.

(* the array of n bytes as its first i bytes and the rest *)
Lemma arr_split2 sh n i (l: list val) p :
  0 <= i <= n -> Zlength l = n -> field_compatible (tarray tuchar n) [] p ->
  @data_at CompSpecs sh (tarray tuchar n) l p =
  (data_at sh (tarray tuchar i) (sublist 0 i l) p *
   data_at sh (tarray tuchar (n - i)) (sublist i n l) (offset_val i p)).
Proof.
  intros. rewrite (split2_data_at_Tarray_tuchar sh n i) by lia.
  change (Tarray tuchar n noattr) with (tarray tuchar n). rewrite arr_field_address0 by (auto; lia).
  simpl sizeof. rewrite Z.mul_1_l. reflexivity.
Qed.

(* what main lends new_frame besides the piece: for an empty piece a witness that data + done is weakly valid
   (the whole array if it has bytes, else its malloc_token), and keeps: the rest of the array and its token *)
Definition nf_wit (n done piece: Z) (dl: list Z) (data: val) : Zstd.proof.zstd.Spec_xxh.ptr_witness :=
  if zlt 0 piece then Zstd.proof.zstd.Spec_xxh.pw_none
  else if zlt 0 n then Zstd.proof.zstd.Spec_xxh.pw_bytes Ews n (zbytes dl) data
  else Zstd.proof.zstd.Spec_xxh.pw_token Ews (tarray tuchar 0) data.

Definition nf_keep (n done piece: Z) (dl: list Z) (data: val) : mpred :=
  if zlt 0 piece then
    @data_at CompSpecs Ews (tarray tuchar done) (zbytes (sublist 0 done dl)) data *
    @data_at CompSpecs Ews (tarray tuchar (n - (done + piece))) (zbytes (sublist (done + piece) n dl))
      (offset_val (done + piece) data) *
    @malloc_token CompSpecs Ews (tarray tuchar n) data
  else if zlt 0 n then @malloc_token CompSpecs Ews (tarray tuchar n) data
  else emp.

Lemma nf_lend n done piece dl data :
  0 <= done -> 0 <= piece -> done + piece <= n -> Zlength dl = n -> field_compatible (tarray tuchar n) [] data ->
  @data_at CompSpecs Ews (tarray tuchar n) (zbytes dl) data * @malloc_token CompSpecs Ews (tarray tuchar n) data |--
  @data_at CompSpecs Ews (tarray tuchar piece) (zbytes (sublist done (done + piece) dl)) (offset_val done data) *
  Zstd.proof.zstd.Spec_xxh.pw_pred (nf_wit n done piece dl data) * nf_keep n done piece dl data.
Proof.
  intros H0 H1 H2 H3 Hfc. unfold nf_wit, nf_keep.
  assert (Hp: isptr data) by (destruct Hfc; auto).
  destruct (zlt 0 piece).
  - rewrite (arr_split3 Ews n done piece dl data) by auto. simpl Zstd.proof.zstd.Spec_xxh.pw_pred. cancel.
  - assert (piece = 0) by lia. subst piece. rewrite Z.add_0_r, sublist_nil. simpl zbytes.
    assert (Hq: isptr (offset_val done data)) by (destruct data; try contradiction; exact I).
    sep_apply (@data_at_tuchar_zero_array CompSpecs Ews (offset_val done data) Hq).
    destruct (zlt 0 n); simpl Zstd.proof.zstd.Spec_xxh.pw_pred.
    + sep_apply (to_Z Ews n (zbytes dl) data). cancel.
    + subst n. assert (dl = []) by (apply Zlength_nil_inv; lia). subst dl. rewrite Zlength_nil in *.
      sep_apply (tok_to_Z Ews 0 data).
      sep_apply (@data_at_zero_array_inv CompSpecs Ews tuchar (zbytes []) data eq_refl eq_refl).
      cancel. apply derives_refl.
Qed.

Lemma nf_back n done piece dl data (d': list Z) :
  0 <= done -> 0 <= piece -> done + piece <= n -> Zlength dl = n -> Zlength d' = piece ->
  field_compatible (tarray tuchar n) [] data ->
  @data_at CompSpecs Ews (tarray tuchar piece) (zbytes d') (offset_val done data) *
  Zstd.proof.zstd.Spec_xxh.pw_pred (nf_wit n done piece dl data) * nf_keep n done piece dl data |--
  @data_at CompSpecs Ews (tarray tuchar n) (zbytes (sublist 0 done dl ++ d' ++ sublist (done + piece) n dl)) data *
  @malloc_token CompSpecs Ews (tarray tuchar n) data.
Proof.
  intros H0 H1 H2 H3 H4 Hfc. unfold nf_wit, nf_keep.
  assert (Hl: Zlength (sublist 0 done dl ++ d' ++ sublist (done + piece) n dl) = n)
    by (rewrite !Zlength_app, !Zlength_sublist by lia; lia).
  destruct (zlt 0 piece).
  - rewrite (arr_split3 Ews n done piece _ data) by auto.
    set (L := sublist 0 done dl ++ d' ++ sublist (done + piece) n dl) in *.
    assert (E1: sublist 0 done L = sublist 0 done dl) by (subst L; list_solve).
    assert (E2: sublist done (done + piece) L = d') by (subst L; list_solve).
    assert (E3: sublist (done + piece) n L = sublist (done + piece) n dl) by (subst L; list_solve).
    rewrite E1, E2, E3.
    simpl Zstd.proof.zstd.Spec_xxh.pw_pred. cancel.
  - assert (d' = []) by (apply Zlength_nil_inv; lia). subst d'. rewrite Zlength_nil in H4. subst piece.
    rewrite Z.add_0_r, app_nil_l, <- sublist_split, sublist_same by lia. simpl zbytes.
    sep_apply (@data_at_zero_array_inv CompSpecs Ews tuchar [] (offset_val done data) eq_refl eq_refl).
    destruct (zlt 0 n); simpl Zstd.proof.zstd.Spec_xxh.pw_pred.
    + sep_apply (of_Z Ews n (zbytes dl) data). cancel.
    + subst n. assert (dl = []) by (apply Zlength_nil_inv; lia). subst dl. rewrite Zlength_nil in *.
      rewrite (data_at_zero_array_eq Ews tuchar (zbytes []) data eq_refl (proj1 Hfc) eq_refl).
      rewrite !emp_sepcon, sepcon_emp. apply tok_of_Z.
Qed.

Lemma nf_wvp n done piece dl data :
  0 <= done <= n -> Zlength dl = n -> isptr data -> piece = 0 ->
  Zstd.proof.zstd.Spec_xxh.pw_pred (nf_wit n done piece dl data) |-- weak_valid_pointer (offset_val done data).
Proof.
  intros H0 H1 Hp ->. unfold nf_wit. destruct (zlt 0 0); [lia |].
  destruct (zlt 0 n); simpl Zstd.proof.zstd.Spec_xxh.pw_pred.
  - eapply derives_trans; [apply (@data_at_memory_block Zstd.units.Zstd.CS) |]. simpl sizeof.
    rewrite Z.mul_1_l, Z.max_r by lia.
    apply memory_block_weak_valid_pointer; [lia | lia | apply readable_nonidentity; auto].
  - assert (done = 0) by lia. subst done. rewrite isptr_offset_val_zero by exact Hp.
    eapply derives_trans; [apply malloc_token_valid_pointer; simpl; lia | apply valid_pointer_weak].
Qed.

(* ---------- the decoder's result ---------- *)

Lemma err_mem : Zstd.proof.zstd.Spec_util.error_of (Zstd.proof.zstd.Spec_util.err_code ZSTD_error_memory_allocation) = 64.
Proof. vm_compute. reflexivity. Qed.

Lemma ltu_Z x y : 0 <= x <= Int64.max_unsigned -> 0 <= y <= Int64.max_unsigned ->
  Int64.ltu (Int64.repr x) (Int64.repr y) = (x <? y).
Proof.
  intros. unfold Int64.ltu. rewrite !Int64.unsigned_repr by lia.
  destruct (zlt x y); symmetry; [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Qed.

Lemma body_main : semax_body Vprog G f_main main_spec.
Proof.
  change (semax_body Vprog G f_main (_main, WITH gv: globals PRE [] VST.floyd.VSU.main_pre
    Zstd.contracts.rfc_concat.whole_prog tt gv POST [tint] (fun _ : environ => TT))).
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
  forward. forward.
  forward_call (gv, n).
  Intros vret. destruct vret as [data dl0]. cbn [fst snd] in *.
  forward.
  change (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with (Vlong (Int64.repr 0)).
  unfold mbytes at 1.
  repeat apply -> seq_assoc. apply semax_if_seq.
  destruct (eq_dec data nullval) as [Hd|Hd].
  { subst data. forward_if; [forward; cancel | congruence]. }
  Intros.
  assert_PROP (field_compatible (tarray tuchar n) [] data) as FCd by entailer!.
  assert (Pd: isptr data) by (destruct FCd; auto).
  forward_if; [destruct data; try contradiction; discriminate |].
  (* the loop: the first done bytes of data are the contents of the frames ps of the series sp *)
  forward_loop (EX done: Z, EX ps: list rc_piece, EX dl: list Z, EX sp: val,
    PROP (0 <= done <= n; Forall rc_ok ps; Zlength dl = n; bytes_ok dl; sublist 0 done dl = rc_contents ps;
          Zlength (rc_frames ps) <= PTRDIFF_MAX)
    LOCAL (temp _series sp; temp _data data; temp _series_len (Vlong (Int64.repr (Zlength (rc_frames ps))));
           temp _done (Vlong (Int64.repr done)); temp _n (Vlong (Int64.repr n)); lvar _len tulong v_len; gvars gv)
    SEP (mem_mgr gv; @malloc_token CompSpecs Ews (tarray tuchar n) data;
         @data_at CompSpecs Ews (tarray tuchar n) (zbytes dl) data;
         mbytes (Zlength (rc_frames ps)) (rc_frames ps) sp; data_at_ Tsh tulong v_len; zstd_globals gv; TT))
    break: (EX ps: list rc_piece, EX sp: val,
    PROP (Forall rc_ok ps; Zlength (rc_contents ps) = n; bytes_ok (rc_contents ps);
          Zlength (rc_frames ps) <= PTRDIFF_MAX; sp <> nullval)
    LOCAL (temp _series sp; temp _data data; temp _series_len (Vlong (Int64.repr (Zlength (rc_frames ps))));
           temp _n (Vlong (Int64.repr n)); lvar _len tulong v_len; gvars gv)
    SEP (mem_mgr gv; @malloc_token CompSpecs Ews (tarray tuchar n) data;
         @data_at CompSpecs Ews (tarray tuchar n) (zbytes (rc_contents ps)) data;
         mbytes (Zlength (rc_frames ps)) (rc_frames ps) sp; data_at_ Tsh tulong v_len; zstd_globals gv; TT)).
  { Exists 0 (@nil rc_piece) dl0 nullval. unfold mbytes. rewrite if_true by reflexivity.
    entailer!. rewrite rc_frames_nil, Zlength_nil. unfold PTRDIFF_MAX. lia. }
  { Intros done ps dl sp.
    forward_call (n - done).
    Intros piece.
    unfold abbreviate in MORE_COMMANDS; subst MORE_COMMANDS.
    repeat apply -> seq_assoc. apply semax_if_seq.
    forward_if; [vm_compute in H10; discriminate |].
    forward.
    (* new_frame on the piece d of data from done *)
    sep_apply (nf_lend n done piece dl data ltac:(lia) ltac:(lia) ltac:(lia) H5 FCd).
    set (d := sublist done (done + piece) dl) in *.
    assert (Hdl: Zlength d = piece) by (subst d; rewrite Zlength_sublist; lia).
    forward_call (gv, Ews, offset_val done data, d, piece, 2 ^ 31, 0, Tsh, v_len, nf_wit n done piece dl data).
    { rewrite Hdl. entailer!. }
    { rewrite Hdl. cancel. }
    { split; [subst d; apply Forall_sublist; exact H6 | intros Hz; apply nf_wvp; auto; lia]. }
    Intros vret. destruct vret as [q d']. cbn [fst snd] in *. rewrite Hdl in *.
    sep_apply (nf_back n done piece dl data d' ltac:(lia) ltac:(lia) ltac:(lia) H5 ltac:(lia) FCd).
    Intros.
    forward.
    set (dl' := sublist 0 done dl ++ d' ++ sublist (done + piece) n dl) in *.
    destruct (eq_dec q nullval) as [Hq|Hq].
    { subst q. repeat apply -> seq_assoc. apply semax_if_seq. forward_if; [| congruence]. forward. forward.
      forward_if; [| congruence]. forward. cancel. }
    Intros c.
    assert (Hok: rc_ok (d, c)) by (split; [cbn [fst snd]; rewrite Hdl; exact H13 | split; [subst d; apply Forall_sublist; exact H6 | cbn [fst]; rep_lia]]).
    pose proof (rc_frame_length (d, c) Hok) as HF. cbn [fst] in HF.
    replace (nf_bytes d piece 0 c) with (rc_frame (d, c)) in *
      by (unfold rc_frame; cbn [fst snd]; rewrite Hdl; reflexivity).
    set (F := rc_frame (d, c)) in *.
    assert_PROP (isptr q) as Hq'.
    { unfold mbytes at 1. rewrite if_false by exact Hq. entailer!. }
    assert (HF2: Zlength F <= PTRDIFF_MAX) by (unfold PTRDIFF_MAX in *; simpl in H15; lia).
    (* join(series, series_len, frame, len) *)
    repeat apply -> seq_assoc. apply semax_if_seq.
    forward_if; [unfold mbytes at 1; rewrite if_false by exact Hq; entailer! | contradiction |].
    forward.
    forward_call (gv, sp, rc_frames ps, q, F).
    { split; [apply rc_frames_ok; auto | split; [unfold F, rc_frame; destruct Hok as (Hk & Hb & _);
        apply (nf_bytes_ok _ _ _ _ _ Hk Hb) | unfold PTRDIFF_MAX in *; rep_lia]]. }
    Intros sp'.
    forward. forward.
    destruct (eq_dec sp' nullval) as [Hs|Hs].
    { subst sp'. forward_if; [| congruence]. forward. cancel. }
    assert_PROP (isptr sp') as Hs'.
    { unfold mbytes at 1. rewrite if_false by exact Hs. entailer!. }
    forward_if; [unfold mbytes at 1; rewrite if_false by exact Hs; entailer! | contradiction |].
    forward. forward. forward.
    (* the invariant for ps ++ [(d, c)] *)
    specialize (H17 Hs HF2).
    assert (Hfr: rc_frames (ps ++ [(d, c)]) = rc_frames ps ++ F) by apply rc_frames_app.
    assert (Hzl: Zlength dl' = n) by (subst dl'; rewrite !Zlength_app, !Zlength_sublist by lia; lia).
    assert (Hsub: sublist 0 (done + piece) dl' = rc_contents (ps ++ [(d, c)])).
    { rewrite rc_contents_app, <- H7. unfold rc_content; cbn [fst snd]. rewrite <- H14.
      subst dl'. list_solve. }
    assert (Hbo: bytes_ok dl').
    { subst dl'. apply Forall_app; split; [apply Forall_sublist; exact H6 |].
      apply Forall_app; split; [exact H12 | apply Forall_sublist; exact H6]. }
    assert (Hall: Forall rc_ok (ps ++ [(d, c)])) by (apply Forall_app; split; [exact H4 | constructor; [exact Hok | constructor]]).
    unfold abbreviate in MORE_COMMANDS; subst MORE_COMMANDS.
    apply semax_if_seq.
    forward_if.
    - forward.
      forward_if.
      + forward. Exists (done + piece) (ps ++ [(d, c)]) dl' sp'. rewrite Hfr, Zlength_app.
        entailer!.
      + discriminate.
    - forward_call tt. Intros u.
      forward.
      forward_if.
      + forward. Exists (done + piece) (ps ++ [(d, c)]) dl' sp'. rewrite Hfr, Zlength_app.
        entailer!.
      + forward.
        (* the loop ends: the frames cover the whole data *)
        match goal with Hlt: Int64.ltu _ _ = false |- _ => rewrite add64_repr, ltu_Z in Hlt by rep_lia;
          apply Z.ltb_ge in Hlt end.
        assert (Hdl2: rc_contents (ps ++ [(d, c)]) = dl')
          by (rewrite <- Hsub, (Z.le_antisymm (done + piece) n) by lia; apply sublist_same; auto).
        Exists (ps ++ [(d, c)]) sp'. rewrite Hfr, Zlength_app, Hdl2.
        entailer!. }
  Intros ps sp.
  (* dst = malloc(cap), cap = n + upto(PTRDIFF_MAX - n) *)
  forward_call (9223372036854775807 - n).
  Intros v.
  forward.
  forward_call (tarray tuchar (n + v), gv).
  { simpl. rep_lia. }
  Intros pd.
  destruct (eq_dec pd nullval) as [Hpd|Hpd].
  { subst pd. forward_if; [forward; cancel | congruence]. }
  Intros. rewrite add64_repr.
  assert_PROP (isptr pd) as Hpd' by entailer!.
  forward_if; [contradiction |].
  (* ZSTD_decompress(dst, cap, series, series_len) *)
  set (S := rc_frames ps) in *. set (cap := n + v) in *.
  unfold mbytes; rewrite if_false by exact H7. Intros.
  assert_PROP (isptr sp) as Hsp by entailer!.
  sep_apply (to_Z Ews (Zlength S) (zbytes S) sp).
  sep_apply (to_Z_ Ews cap pd).
  sep_apply (data_at__mbuf Ews cap pd).
  sep_apply (tok_to_Z Ews (Zlength S) sp).
  sep_apply (tok_to_Z Ews cap pd).
  sep_apply (pws_fold (tarray tuchar (Zlength S)) sp (tarray tuchar cap) pd).
  forward_call ([pw_token Ews (tarray tuchar (Zlength S)) sp; pw_token Ews (tarray tuchar cap) pd],
                gv, Ews, pd, cap, Ews, sp, S).
  { split; [apply buf_ok_tok; [simpl; tauto | auto with share | lia | auto] |].
    split; [apply buf_ok_tok; [simpl; tauto | auto with share | rep_lia | auto] |].
    apply rc_frames_ok; auto. }
  Intros vret. destruct vret as [r out]. cbn [fst snd] in *. rewrite mbuf_isptr by auto.
  match goal with Hk: oneshot_ok _ _ _ _ _ _ |- _ => destruct Hk as [Hle Hk];
    cbv beta iota in Hk; subst S; rewrite (rc_series ps H3) in Hk; destruct Hk as [Hok Herr] end.
  forward_call r.
  (* out_of_memory(result) ends the run *)
  destruct (Z.eq_dec (Zstd.proof.zstd.Spec_util.error_of r) 64) as [Em|Em].
  { forward_if; [forward; cancel | exfalso; apply Int.one_not_zero; assumption]. }
  forward_if; [congruence |].
  (* any other error is excluded: the capacity holds the content *)
  assert (Er: is_error_code r = false).
  { destruct (is_error_code r) eqn:E; [| reflexivity].
    destruct (Herr eq_refl) as [Hc | Hm]; [unfold cap in Hc; lia |].
    subst r. rewrite err_mem in Em. congruence. }
  destruct (Hok Er) as [Hr Hout]. rewrite H4 in Hr. subst r.
  repeat apply -> seq_assoc. apply semax_if_seq.
  forward_if; [| congruence].
  (* bytes_eq(dst, data, n): dst's first n bytes are the content, and so is data *)
  sep_apply (of_Z Ews cap out pd).
  assert_PROP (field_compatible (tarray tuchar cap) [] pd) as FCp by entailer!.
  rewrite (arr_split2 Ews cap n out pd) by (auto; lia).
  rewrite Hout.
  unfold abbreviate in MORE_COMMANDS; subst MORE_COMMANDS.
  eapply semax_seq'.
  forward_call (Ews, pd, rc_contents ps, Ews, data, rc_contents ps).
  { rewrite H4. entailer!. }
  { rewrite H4. cancel. }
  destruct (list_eq_dec Z.eq_dec (rc_contents ps) (rc_contents ps)) as [_|Hne]; [| contradiction].
  forward.
  apply andp_left2; apply derives_refl.
  change (Int.eq Int.one Int.zero) with false. cbv iota.
  forward_call (Int.one).
  forward.
  cancel.
Qed.

(* ---------- the harness unit's obligation ---------- *)

Lemma Externals_eq :
  Externals = [nondet_u8_spec; nondet_size_spec; nondet_bytes_nn_spec; gp_assert_spec; gp_assume_spec].
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

Lemma Gprog_cons : Gprog API Hs =
  (_quickproof_malloc, malloc_spec') :: (_quickproof_free, free_spec') ::
  (API ++ [nondet_u8_spec; nondet_size_spec; nondet_bytes_nn_spec; gp_assert_spec; gp_assume_spec] ++
   Hs ++ [main_spec]).
Proof. unfold Gprog, Imports. rewrite Externals_eq. reflexivity. Qed.

(* an entry of a body's context found in Gprog *)
Ltac in_gprog :=
  match goal with |- initial_world.find_id ?i _ = Some ?fs =>
    rewrite Gprog_cons; unfold API, Hs; cbn [app]; find_steps; reflexivity end.

(* a helper of the frames kit: the harness's body is the kit's Clight term (the lookup in the harness's
   definitions computes to it), proved once in the kit and moved into Gprog *)
Ltac kit_body fk Gk body :=
  exists fk; split; [vm_compute; reflexivity |]; split; [reflexivity |];
  apply (Zstd.proof.harness.frames.FTransfer.fk_transfer Vprog _ Gk);
  [ exact body
  | apply Zstd.proof.harness.frames.FTransfer.fk_find_all; repeat constructor; in_gprog ].

Theorem rfc_concat_ok : HarnessOK API Hs.
Proof.
  split; [exact Hs_ids |].
  repeat apply Forall_cons; try apply Forall_nil.
  - kit_body FSpecs.f_out_of_memory G_out_of_memory
      (@Zstd.proof.harness.frames.FBodiesSmall.body_out_of_memory CompSpecs).
  - kit_body FSpecs.f_copy_of (@G_copy_of CompSpecs)
      (@Zstd.proof.harness.frames.FBodiesSmall.body_copy_of CompSpecs).
  - kit_body FSpecs.f_any_bytes (@G_any_bytes CompSpecs)
      (@Zstd.proof.harness.frames.FBodiesSmall.body_any_bytes CompSpecs).
  - kit_body FSpecs.f_upto G_upto (@Zstd.proof.harness.frames.FBodiesSmall.body_upto CompSpecs).
  - kit_body FSpecs.f_put_le G_put_le
      (@Zstd.proof.harness.frames.FBodiesSmall.body_put_le CompSpecs).
  - kit_body FSpecs.f_join (@G_join CompSpecs) (@Zstd.proof.harness.frames.FBodiesSmall.body_join CompSpecs).
  - kit_body FSpecs.f_bytes_eq G_bytes_eq
      (@Zstd.proof.harness.frames.FBodiesSmall.body_bytes_eq CompSpecs).
  - kit_body FSpecs.f_new_frame (@G_new_frame CompSpecs)
      (@Zstd.proof.harness.frames.FBodyNewFrame.body_new_frame CompSpecs).
  - exists f_main. split; [reflexivity |]. split; [reflexivity |]. exact body_main.
Qed.
