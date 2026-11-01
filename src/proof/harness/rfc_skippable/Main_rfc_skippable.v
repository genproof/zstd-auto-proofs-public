(* The harness obligation of rfc_skippable (harness/rfc_skippable.c): with the API [ZSTD_decompress;
   ZSTD_getErrorCode; ZSTD_XXH64] (the second for out_of_memory, the third for new_frame's checksums), the helpers
   of laws_common.h and frames.h (proved once in the frames kit) and main satisfy their specifications.

   main's loop keeps the series built so far as a list of pieces (Facts_rfc_skippable.chunk: skippable frames of
   new_skippable and frames of new_frame), with the data cut so far equal to the contents of the frames; at the
   end ZSTD_decompress's specification (oneshot_ok) gives exactly these contents, by the model fact
   Facts_rfc_skippable.chunks_decode.  The series and the output have any length up to PTRDIFF_MAX: this needs the
   one-shot specification with sizes up to 2 ^ 63 - 1 and skippable frames of up to 2 ^ 32 - 1 bytes of user data
   in the model (stage 1 of the size bounds and fix F5). *)
Require Import VST.floyd.proofauto.
Require Export Zstd.proof.zstd.Spec_api6.
Require Export Zstd.proof.harness.rfc_skippable.HOK_rfc_skippable.
Require Zstd.proof.top.MainPre6.
Require Import Zstd.proof.zstd.NullBuf.
Require Zstd.proof.harness.HCsConv.
Require Zstd.proof.harness.frames.FSpecs Zstd.proof.harness.frames.FBodiesSmall Zstd.proof.harness.frames.FTransfer.
Require Zstd.proof.harness.frames.FBodyNewFrame Zstd.proof.harness.frames.FFacts Zstd.proof.harness.frames.FSeries.
Require Import Zstd.proof.harness.rfc_skippable.Facts_rfc_skippable.
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
    (QPprog_vars Zstd.contracts.rfc_skippable.whole_prog).
Proof.
  apply Forall_forall. intros [i v] Hin. apply make_tycontext_g_isSome.
  unfold Vprog, QPvarspecs. rewrite map_map.
  apply in_map_iff. exists (i, v). split; [reflexivity | exact Hin].
Qed.

(* main's precondition: the decoder's globals, split off as in MainPre6.main_pre_fact6 (whose list of
   programs has the x_ laws only) *)
Lemma pre_globals gv :
  InitGPred (Vardefs Zstd.contracts.rfc_skippable.whole_prog) gv |-- zstd_globals gv * TT.
Proof.
  assert (Hincl: incl Zstd.proof.top.MainPre6.zstd_vardefs (Vardefs Zstd.contracts.rfc_skippable.whole_prog)).
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

Lemma mbytes_fold {cs: compspecs} n l q : q <> nullval ->
  malloc_token Ews (tarray tuchar n) q * data_at Ews (tarray tuchar n) (zbytes l) q |-- mbytes n l q.
Proof. intros Hq. unfold mbytes. rewrite if_false by exact Hq. apply derives_refl. Qed.

Lemma isptr_of p : is_pointer_or_null p -> p <> nullval -> isptr p.
Proof. intros H1 H2. destruct p; simpl in *; auto. subst. contradiction. Qed.

(* nondet_u8() & 1 *)
Lemma and_one b : 0 <= b <= Int.max_unsigned -> Int.and (Int.repr b) (Int.repr 1) = Int.repr (b mod 2).
Proof.
  intros Hb. unfold Int.and. rewrite !Int.unsigned_repr by rep_lia.
  change 1 with (Z.ones 1). rewrite Z.land_ones by lia. reflexivity.
Qed.

(* ---------- the data array cut at done: the piece new_frame writes ---------- *)

Lemma arr_split2 {cs: compspecs} sh n (v: list val) p i : 0 <= i <= n -> Zlength v = n ->
  field_compatible (tarray tuchar n) [] p ->
  data_at sh (tarray tuchar n) v p =
  (data_at sh (tarray tuchar i) (sublist 0 i v) p *
   data_at sh (tarray tuchar (n - i)) (sublist i n v) (offset_val i p))%logic.
Proof.
  intros. unfold tarray. rewrite (split2_data_at_Tarray_tuchar sh n i v p) by auto.
  rewrite field_address0_offset by auto with field_compatible.
  simpl nested_field_offset. rewrite Z.mul_1_l, Z.add_0_l. auto.
Qed.

(* a part of an array of bytes is an array *)
Lemma fc_sub {cs: compspecs} n p i m : field_compatible (tarray tuchar n) [] p -> 0 <= i -> 0 <= m -> i + m <= n ->
  field_compatible (tarray tuchar m) [] (offset_val i p).
Proof.
  intros (Hp & Hc & Hs & Ha & Hl) Hi Hm Him. destruct p; try contradiction.
  unfold field_compatible. simpl in Hs |- *. rewrite Z.max_r in Hs by lia. rewrite Z.max_r by lia.
  split3; [exact I | reflexivity |]. split3; [| | exact I].
  - rewrite Z.mul_1_l in *. unfold Ptrofs.add. rewrite (Ptrofs.unsigned_repr (Ptrofs.unsigned i0 + Ptrofs.unsigned (Ptrofs.repr i))).
    + rewrite Ptrofs.unsigned_repr by rep_lia. lia.
    + rewrite Ptrofs.unsigned_repr by rep_lia. pose proof (Ptrofs.unsigned_range i0). rep_lia.
  - apply align_compatible_rec_Tarray. intros j Hj. eapply align_compatible_rec_by_value; [reflexivity |].
    apply Z.divide_1_l.
Qed.

(* an array of n bytes = three arrays one after the other *)
Lemma arr3_eq {cs: compspecs} sh n a b c p : field_compatible (tarray tuchar n) [] p ->
  Zlength a + Zlength b + Zlength c = n ->
  data_at sh (tarray tuchar n) (zbytes (a ++ b ++ c)) p =
  (data_at sh (tarray tuchar (Zlength a)) (zbytes a) p *
   data_at sh (tarray tuchar (Zlength b)) (zbytes b) (offset_val (Zlength a) p) *
   data_at sh (tarray tuchar (Zlength c)) (zbytes c) (offset_val (Zlength a + Zlength b) p))%logic.
Proof.
  intros Hfc Hn.
  pose proof (Zlength_nonneg a). pose proof (Zlength_nonneg b). pose proof (Zlength_nonneg c).
  rewrite (arr_split2 sh n _ p (Zlength a)) by (try exact Hfc; rewrite ?Zlength_map, ?Zlength_app; lia).
  rewrite map_app, sublist_app1 by (rewrite ?Zlength_map; lia).
  rewrite sublist_same by (rewrite ?Zlength_map; lia).
  rewrite sublist_app2 by (rewrite ?Zlength_map; lia). rewrite Zlength_map, Z.sub_diag.
  rewrite sublist_same by (rewrite ?Zlength_map, ?map_app, ?Zlength_app, ?Zlength_map; lia).
  rewrite (arr_split2 sh (n - Zlength a) _ (offset_val (Zlength a) p) (Zlength b))
    by (first [apply fc_sub with n; auto; lia | rewrite ?Zlength_map, ?map_app, ?Zlength_app, ?Zlength_map; lia]).
  rewrite map_app, sublist_app1 by (rewrite ?Zlength_map; lia).
  rewrite sublist_same by (rewrite ?Zlength_map; lia).
  rewrite sublist_app2 by (rewrite ?Zlength_map; lia). rewrite Zlength_map, Z.sub_diag.
  rewrite sublist_same by (rewrite ?Zlength_map; lia).
  rewrite offset_offset_val, sepcon_assoc.
  replace (n - Zlength a - Zlength b) with (Zlength c) by lia. reflexivity.
Qed.

Lemma arr3_join {cs: compspecs} sh n a b c p i j : field_compatible (tarray tuchar n) [] p ->
  Zlength a = i -> Zlength b = j -> Zlength a + Zlength b + Zlength c = n ->
  (data_at sh (tarray tuchar i) (zbytes a) p * data_at sh (tarray tuchar j) (zbytes b) (offset_val i p) *
   data_at sh (tarray tuchar (Zlength c)) (zbytes c) (offset_val (i + j) p) |--
   data_at sh (tarray tuchar n) (zbytes (a ++ b ++ c)) p)%logic.
Proof. intros Hfc <- <- Hn. rewrite (arr3_eq sh n a b c p Hfc Hn). apply derives_refl. Qed.

(* ---------- an empty piece: new_frame's data of 0 bytes and the witness of its pointer ---------- *)

(* the witness that data + done is weakly valid (ZSTD_XXH64 compares it with NULL): the whole array, or the
   malloc_token of an empty one *)
Definition zw (n: Z) (D: list Z) (data: val) : Zstd.proof.zstd.Spec_xxh.ptr_witness :=
  if Z.eq_dec n 0 then Zstd.proof.zstd.Spec_xxh.pw_token Ews (tarray tuchar 0) data
  else Zstd.proof.zstd.Spec_xxh.pw_bytes Ews n (zbytes D) data.

(* what stays with main meanwhile *)
Definition zrest (n: Z) (D: list Z) (data: val) : mpred :=
  if Z.eq_dec n 0 then @data_at CompSpecs Ews (tarray tuchar n) (zbytes D) data
  else @malloc_token CompSpecs Ews (tarray tuchar n) data.

Lemma zero_split n D data done : 0 <= done <= n -> Zlength D = n ->
  (@malloc_token CompSpecs Ews (tarray tuchar n) data * @data_at CompSpecs Ews (tarray tuchar n) (zbytes D) data |--
   @data_at CompSpecs Ews (tarray tuchar 0) (zbytes []) (offset_val done data) *
   Zstd.proof.zstd.Spec_xxh.pw_pred (zw n D data) * zrest n D data)%logic.
Proof.
  intros Hd HD.
  assert_PROP (field_compatible (tarray tuchar n) [] data) as Hfc by entailer!.
  rewrite (@data_at_zero_array_eq CompSpecs Ews tuchar (zbytes []) (offset_val done data))
    by (auto; destruct Hfc as [Hp _]; destruct data; try contradiction; exact I).
  rewrite emp_sepcon. unfold zw, zrest, Zstd.proof.zstd.Spec_xxh.pw_pred. destruct (Z.eq_dec n 0) as [E|E].
  - rewrite E at 1. apply sepcon_derives; [apply tok_to_Z | apply derives_refl].
  - rewrite sepcon_comm. apply sepcon_derives; [apply to_Z | apply derives_refl].
Qed.

Lemma zero_join n D data done l : Zlength l = 0 ->
  (@data_at CompSpecs Ews (tarray tuchar 0) l (offset_val done data) *
   Zstd.proof.zstd.Spec_xxh.pw_pred (zw n D data) * zrest n D data |--
   @malloc_token CompSpecs Ews (tarray tuchar n) data * @data_at CompSpecs Ews (tarray tuchar n) (zbytes D) data)%logic.
Proof.
  intros Hl. apply Zlength_nil_inv in Hl. subst l.
  assert_PROP (isptr (offset_val done data)) as Hfc by entailer!.
  rewrite data_at_zero_array_eq by auto.
  rewrite emp_sepcon. unfold zw, zrest, Zstd.proof.zstd.Spec_xxh.pw_pred. destruct (Z.eq_dec n 0) as [E|E].
  - rewrite E at 2. apply sepcon_derives; [apply tok_of_Z | apply derives_refl].
  - rewrite sepcon_comm. apply sepcon_derives; [apply derives_refl | apply of_Z].
Qed.

Lemma zero_wvp n D data done : 0 <= done <= n -> isptr data ->
  Zstd.proof.zstd.Spec_xxh.pw_pred (zw n D data) |-- weak_valid_pointer (offset_val done data).
Proof.
  intros Hd Hp. unfold zw, Zstd.proof.zstd.Spec_xxh.pw_pred. destruct (Z.eq_dec n 0) as [E|E].
  - assert (done = 0) by lia. subst done. rewrite isptr_offset_val_zero by exact Hp.
    eapply derives_trans; [apply malloc_token_valid_pointer; simpl; lia | apply valid_pointer_weak].
  - sep_apply (@data_at_memory_block Zstd.units.Zstd.CS Ews (tarray tuchar n) (zbytes D) data).
    simpl sizeof. rewrite Z.max_r by lia. rewrite Z.mul_1_l.
    apply memory_block_weak_valid_pointer; [lia | lia | apply readable_nonidentity; auto].
Qed.


(* ---------- the buffer witnesses of a one-shot call: the malloc_tokens of its two buffers ---------- *)

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


(* the API of the law *)
Definition API : funspecs :=
  [ZSTD_decompress_spec; Zstd.proof.zstd.Spec_util.ZSTD_getErrorCode_spec; Zstd.proof.zstd.Spec_xxh.ZSTD_XXH64_spec].

(* the functions main calls *)
Definition G0 : funspecs :=
  [(_quickproof_malloc, malloc_spec'); ZSTD_decompress_spec;
   nondet_u8_spec; gp_assert_spec;
   upto_spec; @any_bytes_spec CompSpecs; @new_frame_spec CompSpecs; @new_skippable_spec CompSpecs;
   @join_spec CompSpecs; out_of_memory_spec; @bytes_eq_spec CompSpecs].

Lemma body_main_G0 : semax_body Vprog G0 f_main main_spec.
Proof.
  change (semax_body Vprog G0 f_main (_main, WITH gv: globals PRE [] VST.floyd.VSU.main_pre
    Zstd.contracts.rfc_skippable.whole_prog tt gv POST [tint] (fun _ : environ => TT))).
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
  Intros vret. destruct vret as [data D0]. cbn [fst snd] in *.
  forward.
  unfold mbytes at 1.
  repeat apply -> seq_assoc. apply semax_if_seq.
  destruct (eq_dec data nullval) as [Hdn|Hdn].
  { subst data. forward_if; [forward; cancel | exfalso; auto]. }
  Intros.
  assert_PROP (isptr data) as Hdp by entailer!.
  forward_if; [destruct data; try contradiction; discriminate |].
  assert_PROP (field_compatible (tarray tuchar n) [] data) as Hfc by entailer!.
  (* the loop: the series is the list l of pieces; the data cut so far is the content of l *)
  forward_loop (EX done: Z, EX D: list Z, EX l: list chunk, EX sp: val,
    PROP (0 <= done <= n; Zlength D = n; bytes_ok D; Forall chunk_ok l; sublist 0 done D = content_of l;
          Zlength (series_of l) <= PTRDIFF_MAX)
    LOCAL (temp _series sp; temp _data data; temp _series_len (Vlong (Int64.repr (Zlength (series_of l))));
           temp _done (Vlong (Int64.repr done)); temp _n (Vlong (Int64.repr n)); lvar _len tulong v_len; gvars gv)
    SEP (mem_mgr gv; malloc_token Ews (tarray tuchar n) data; data_at Ews (tarray tuchar n) (zbytes D) data;
         mbytes (Zlength (series_of l)) (series_of l) sp; data_at_ Tsh tulong v_len; zstd_globals gv; TT))
  break: (EX D: list Z, EX l: list chunk, EX sp: val,
    PROP (Zlength D = n; bytes_ok D; Forall chunk_ok l; D = content_of l; Zlength (series_of l) <= PTRDIFF_MAX;
          sp <> nullval)
    LOCAL (temp _series sp; temp _data data; temp _series_len (Vlong (Int64.repr (Zlength (series_of l))));
           temp _n (Vlong (Int64.repr n)); lvar _len tulong v_len; gvars gv)
    SEP (mem_mgr gv; malloc_token Ews (tarray tuchar n) data; data_at Ews (tarray tuchar n) (zbytes D) data;
         mbytes (Zlength (series_of l)) (series_of l) sp; data_at_ Tsh tulong v_len; zstd_globals gv; TT)).
  { Exists 0 D0 (@nil chunk) nullval. unfold mbytes. rewrite if_true by reflexivity.
    entailer!. unfold series_of; cbn [map concat]; rewrite Zlength_nil; unfold PTRDIFF_MAX; lia. }
  { Intros done D l sp.
    forward.
    forward_call tt.
    Intros u8.
    (* the piece: a skippable frame, or a frame of new_frame on the next piece bytes of data *)
    forward_if (EX piece: Z, EX fr: val, EX d': list Z, EX x: chunk,
      PROP (0 <= piece <= n - done; Zlength d' = piece; bytes_ok d';
            fr <> nullval -> chunk_ok x /\ chunk_data x = d' /\ Zlength (chunk_bytes x) <= PTRDIFF_MAX)
      LOCAL (temp _frame fr; temp _piece (Vlong (Int64.repr piece)); temp _series sp; temp _data data;
             temp _series_len (Vlong (Int64.repr (Zlength (series_of l))));
             temp _done (Vlong (Int64.repr done)); temp _n (Vlong (Int64.repr n)); lvar _len tulong v_len; gvars gv)
      SEP (mem_mgr gv; malloc_token Ews (tarray tuchar n) data;
           data_at Ews (tarray tuchar n) (zbytes (sublist 0 done D ++ d' ++ sublist (done + piece) n D)) data;
           mbytes (Zlength (series_of l)) (series_of l) sp;
           if eq_dec fr nullval then data_at_ Tsh tulong v_len
           else (data_at Tsh tulong (Vlong (Int64.repr (Zlength (chunk_bytes x)))) v_len *
                 mbytes (Zlength (chunk_bytes x)) (chunk_bytes x) fr);
           zstd_globals gv; TT)).
    - (* new_skippable *)
      forward_call (gv, Tsh, v_len).
      Intros q.
      forward.
      assert (E: sublist 0 done D ++ [] ++ sublist (done + 0) n D = D)
        by (rewrite app_nil_l, Z.add_0_r, <- sublist_split, sublist_same by lia; reflexivity).
      destruct (eq_dec q nullval) as [Hq|Hq].
      + subst q. Exists 0 nullval (@nil Z) (CSkip 0 []). rewrite E, if_true by reflexivity.
        entailer!. apply Forall_nil.
      + Intros k u. Exists 0 q (@nil Z) (CSkip k u). rewrite E, if_false by exact Hq.
        entailer!.
        split; [apply Forall_nil |]. intros _. split3; [cbn; auto | reflexivity |].
        cbn [chunk_bytes]. rewrite Zstd.proof.harness.frames.FSeries.sk_bytes_length. unfold PTRDIFF_MAX. lia.
    - (* new_frame(data + done, piece, piece, ONE_CALL_WINDOW, 0, &len) *)
      forward_call (n - done).
      Intros piece.
      repeat apply -> seq_assoc. apply semax_if_seq.
      forward_if; [vm_compute in H12; discriminate |].
      forward.
      destruct (Z.eq_dec piece 0) as [Hp0|Hp0].
      + (* an empty piece: the witness of data + done *)
        subst piece.
        sep_apply (zero_split n D data done ltac:(lia) H4).
        forward_call (gv, Ews, offset_val done data, @nil Z, 0, 2 ^ 31, 0, Tsh, v_len, zw n D data).
        { rewrite Zlength_nil. cancel. }
        { split; [apply Forall_nil | split; [rewrite Zlength_nil; rep_lia | intros _; apply zero_wvp; auto; lia]]. }
        Intros vret. destruct vret as [q d1]. cbn [fst snd] in *. rewrite Zlength_nil in *.
        sep_apply (zero_join n D data done (zbytes d1) ltac:(rewrite Zlength_map; auto)).
        Intros. forward.
        assert (E: sublist 0 done D ++ [] ++ sublist (done + 0) n D = D)
          by (rewrite app_nil_l, Z.add_0_r, <- sublist_split, sublist_same by lia; reflexivity).
        destruct (eq_dec q nullval) as [Hq|Hq].
        * subst q. Exists 0 nullval (@nil Z) (CSkip 0 []). rewrite E, if_true by reflexivity.
          entailer!. apply Forall_nil.
        * Intros c. Exists 0 q (@nil Z) (CFrame [] c). rewrite E, if_false by exact Hq.
          change (chunk_bytes (CFrame [] c)) with (nf_bytes [] 0 0 c).
          entailer!.
          split; [apply Forall_nil |]. intros _.
          match goal with Hc: nf_ok _ _ _ _ c |- _ => rename Hc into Hok end.
          split3.
          -- split3; [exact Hok | apply Forall_nil | rewrite Zlength_nil; lia].
          -- apply Zlength_nil_inv. auto.
          -- pose proof (Zstd.proof.harness.frames.FFacts.nf_bytes_length [] 0 (2 ^ 31) 0 c Hok) as L.
             rewrite Zlength_nil in L. cbn [chunk_bytes]. rewrite ?Zlength_nil. unfold PTRDIFF_MAX. lia.
      + (* the piece of data at data + done, between the data cut before and the rest *)
        assert (La: Zlength (sublist 0 done D) = done) by (rewrite Zlength_sublist; lia).
        assert (Lb: Zlength (sublist done (done + piece) D) = piece) by (rewrite Zlength_sublist; lia).
        assert (Lc: Zlength (sublist (done + piece) n D) = n - done - piece) by (rewrite Zlength_sublist; lia).
        assert (ED: D = sublist 0 done D ++ sublist done (done + piece) D ++ sublist (done + piece) n D)
          by (rewrite <- !sublist_split by lia; rewrite sublist_same by lia; reflexivity).
        replace (zbytes D) with (zbytes (sublist 0 done D ++ sublist done (done + piece) D ++ sublist (done + piece) n D))
          by (f_equal; symmetry; exact ED).
        rewrite (arr3_eq Ews n _ _ _ data Hfc) by lia.
        rewrite La. Intros.
        forward_call (gv, Ews, offset_val done data, sublist done (done + piece) D, piece, 2 ^ 31, 0, Tsh, v_len,
                      Zstd.proof.zstd.Spec_xxh.pw_none).
        { rewrite Lb. entailer!. }
        { unfold Zstd.proof.zstd.Spec_xxh.pw_pred. cancel. }
        { apply Forall_sublist. exact H5. }
        Intros vret. destruct vret as [q d1]. cbn [fst snd] in *.
        match goal with Hd: Zlength d1 = _ |- _ => rename Hd into Ld1 end.
        sep_apply (arr3_join Ews n (sublist 0 done D) d1 (sublist (done + piece) n D) data done
                     (Zlength (sublist done (done + piece) D)) Hfc La Ld1 ltac:(lia)).
        unfold Zstd.proof.zstd.Spec_xxh.pw_pred.
        forward.
        rewrite Lb in Ld1 |- *.
        destruct (eq_dec q nullval) as [Hq|Hq].
        * subst q. Exists piece nullval d1 (CSkip 0 []).
          rewrite if_true by reflexivity.
          entailer!.
        * Intros c. Exists piece q d1 (CFrame (sublist done (done + piece) D) c).
          rewrite if_false by exact Hq.
          change (chunk_bytes (CFrame (sublist done (done + piece) D) c))
            with (nf_bytes (sublist done (done + piece) D) (Zlength (sublist done (done + piece) D)) 0 c).
          rewrite Lb.
          entailer!.
          match goal with Hc: nf_ok piece piece _ _ c |- _ => rename Hc into Hok end.
          assert (Hok': nf_ok (Zlength (sublist done (done + piece) D)) piece (2 ^ 31) 0 c) by (rewrite Lb; exact Hok).
          split3.
          -- cbn [chunk_ok]. rewrite Lb. split3; [exact Hok | apply Forall_sublist; auto | rep_lia].
          -- reflexivity.
          -- pose proof (Zstd.proof.harness.frames.FFacts.nf_bytes_length _ _ _ _ c Hok') as L.
             rewrite Lb in L. pose proof (Z.mul_div_le (PTRDIFF_MAX - 26) 4 ltac:(lia)). nia.
    - Intros piece fr d' x.
      repeat apply -> seq_assoc. apply semax_if_seq.
      destruct (eq_dec fr nullval) as [Hf|Hf].
      { (* out of memory: the run ends *)
        subst fr.
        forward_if; [| exfalso; auto]. forward. forward.
        forward_if; [forward; cancel | exfalso; auto]. }
      match goal with Hx: fr <> nullval -> _ |- _ => destruct (Hx Hf) as (Hxo & Hxd & Hxl) end.
      unfold mbytes at 2. rewrite if_false by exact Hf. Intros.
      assert_PROP (isptr fr) as Hfp by entailer!.
      forward_if; [destruct fr; try contradiction; discriminate |].
      sep_apply (@mbytes_fold CompSpecs (Zlength (chunk_bytes x)) (chunk_bytes x) fr Hf).
      forward.
      forward_call (gv, sp, series_of l, fr, chunk_bytes x).
      { split; [apply series_of_ok; auto |]. split; [apply chunk_bytes_ok; auto |].
        unfold PTRDIFF_MAX in *. rep_lia. }
      Intros s'.
      forward. forward.
      destruct (eq_dec s' nullval) as [Hs|Hs].
      { subst s'. forward_if; [| exfalso; auto].
        sep_apply (data_at_data_at_ Tsh tulong (Vlong (Int64.repr (Zlength (chunk_bytes x)))) v_len).
        forward. cancel. }
      match goal with Hj: s' <> nullval -> _ |- _ =>
        assert (Hlen: Zlength (series_of l) + Zlength (chunk_bytes x) <= PTRDIFF_MAX) by (apply Hj; auto) end.
      unfold mbytes at 1. rewrite if_false by exact Hs. Intros.
      assert_PROP (isptr s') as Hsp by entailer!.
      forward_if; [destruct s'; try contradiction; discriminate |].
      forward. forward. forward.
      (* the new state: the piece x after the series, its content after the data cut before *)
      set (DD := sublist 0 done D ++ d' ++ sublist (done + piece) n D).
      assert (LD: Zlength DD = n) by (unfold DD; rewrite !Zlength_app, !Zlength_sublist by lia; lia).
      assert (BD: bytes_ok DD).
      { unfold DD. apply Zstd.proof.harness.frames.FFacts.ff_bytes_ok_app; [apply Forall_sublist; auto |].
        apply Zstd.proof.harness.frames.FFacts.ff_bytes_ok_app; [auto | apply Forall_sublist; auto]. }
      assert (CD: sublist 0 (done + piece) DD = content_of (l ++ [x])).
      { rewrite content_of_snoc, <- H7, Hxd. unfold DD. rewrite app_assoc.
        rewrite sublist_app1 by (rewrite ?Zlength_app, ?Zlength_sublist by lia; lia).
        apply sublist_same; [lia | rewrite ?Zlength_app, ?Zlength_sublist by lia; lia]. }
      assert (Fl: Forall chunk_ok (l ++ [x])) by (apply Forall_app; split; auto).
      assert (NL: Zlength (series_of (l ++ [x])) = Zlength (series_of l) + Zlength (chunk_bytes x))
        by (rewrite series_of_snoc, Zlength_app; auto).
      clearbody DD.
      sep_apply (@mbytes_fold CompSpecs (Zlength (series_of l) + Zlength (chunk_bytes x))
                   (series_of l ++ chunk_bytes x) s' Hs).
      sep_apply (data_at_data_at_ Tsh tulong (Vlong (Int64.repr (Zlength (chunk_bytes x)))) v_len).
      rewrite !add64_repr, <- series_of_snoc, <- NL.
      apply semax_if_seq.
      forward_if.
      + forward.
        forward_if.
        * forward. Exists (done + piece) DD (l ++ [x]) s'. entailer!.
        * match goal with Hz: Int.repr 1 = Int.zero |- _ => exfalso; exact (Int.one_not_zero Hz) end.
      + forward_call tt.
        Intros u.
        forward.
        forward_if.
        * forward. Exists (done + piece) DD (l ++ [x]) s'. entailer!.
        * forward. Exists DD (l ++ [x]) s'. entailer!.
          rewrite <- CD. rewrite sublist_same by lia. reflexivity. }
  (* after the loop: the series S decodes to D in the model *)
  Intros D l sp.
  set (S := series_of l) in *.
  assert (HS: decode_series_m md_dflt sel_none (Some no_dict) no_wlim S = SOk D)
    by (unfold S; subst D; apply chunks_decode; auto).
  assert (BS: bytes_ok S) by (apply series_of_ok; auto).
  clearbody S.
  match goal with Hn: Zlength D = n |- _ => rename Hn into LDn end.
  forward_call (9223372036854775807 - n).
  Intros e.
  forward.
  rewrite add64_repr.
  forward_call (tarray tuchar (n + e), gv).
  { simpl. rep_lia. }
  Intros dst.
  repeat apply -> seq_assoc. apply semax_if_seq.
  destruct (eq_dec dst nullval) as [Hdst|Hdst].
  { subst dst. forward_if; [forward; cancel | exfalso; auto]. }
  Intros.
  assert_PROP (isptr dst) as Hdstp by entailer!.
  forward_if; [destruct dst; try contradiction; discriminate |].
  (* ZSTD_decompress(dst, cap, series, series_len), the buffers at the decoder's compspecs *)
  unfold mbytes at 1. rewrite if_false by assumption. Intros.
  assert_PROP (isptr sp) as Hspp by entailer!.
  sep_apply (to_Z Ews (Zlength S) (zbytes S) sp).
  sep_apply (to_Z_ Ews (n + e) dst).
  sep_apply (data_at__mbuf Ews (n + e) dst).
  sep_apply (tok_to_Z Ews (Zlength S) sp).
  sep_apply (tok_to_Z Ews (n + e) dst).
  sep_apply (pws_fold (tarray tuchar (Zlength S)) sp (tarray tuchar (n + e)) dst).
  forward_call ([pw_token Ews (tarray tuchar (Zlength S)) sp; pw_token Ews (tarray tuchar (n + e)) dst],
                gv, Ews, dst, n + e, Ews, sp, S).
  { split; (apply buf_ok_tok; [simpl; tauto | auto | rep_lia | auto]). }
  Intros vret. destruct vret as [r out]. cbn [fst snd] in *. rewrite mbuf_isptr by auto.
  match goal with Ho: oneshot_ok _ _ _ _ _ _ |- _ => rename Ho into Hos end.
  sep_apply pws_unfold.
  forward_call r.
  forward_if.
  { (* ZSTD_error_memory_allocation: the run ends *)
    forward. cancel. }
  (* not out of memory: the result is the content D (oneshot_ok on the decoded series) *)
  assert (Hok: r = Zlength D /\ sublist 0 r out = zbytes D).
  { unfold oneshot_ok in Hos. rewrite HS in Hos. destruct Hos as (_ & Hs1 & Hs2).
    destruct (is_error_code r) eqn:Er.
    - exfalso. destruct (Hs2 eq_refl) as [Hc|Hm]; [lia |].
      match goal with Hz: (if Z.eq_dec _ 64 then _ else _) = Int.zero |- _ => revert Hz end.
      replace (Zstd.proof.zstd.Spec_util.error_of r) with 64.
      + rewrite if_true by reflexivity. intros Hz. exact (Int.one_not_zero Hz).
      + unfold Zstd.proof.zstd.Spec_util.error_of. rewrite Er. subst r.
        unfold Zstd.proof.zstd.Spec_util.err_code, ZSTD_error_memory_allocation. lia.
    - exact (Hs1 eq_refl). }
  destruct Hok as [Hr Hout]. subst r.
  repeat apply -> seq_assoc. apply semax_if_seq.
  forward_if.
  2: { exfalso. match goal with Hne: Int64.repr _ <> Int64.repr _ |- _ => apply Hne; f_equal; lia end. }
  (* bytes_eq(dst, data, n): the first n bytes of dst against the data *)
  rewrite <- LDn in *.
  assert_PROP (@field_compatible Zstd.units.Zstd.CS (tarray tuchar (Zlength D + e)) [] dst) as Hfd by entailer!.
  rewrite (arr_split2 Ews (Zlength D + e) out dst (Zlength D)) by (first [exact Hfd | lia]).
  rewrite Hout. Intros.
  sep_apply (of_Z Ews (Zlength D) (zbytes D) dst).
  apply -> seq_assoc.
  forward_call (Ews, dst, D, Ews, data, D).
  destruct (list_eq_dec Z.eq_dec D D) as [_|C]; [| contradiction].
  forward.
  forward_call Int.one.
  forward. cancel.
Qed.
(* ---------- from G0 to Gprog API Hs ---------- *)

(* the harness's own functions besides main (in the order of helper_ids): the frames kit's helpers *)
Definition Hs : funspecs :=
  [out_of_memory_spec; @copy_of_spec CompSpecs; @any_bytes_spec CompSpecs; upto_spec; @put_le_spec CompSpecs;
   @join_spec CompSpecs; @bytes_eq_spec CompSpecs; @new_skippable_spec CompSpecs; @new_frame_spec CompSpecs].

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

Lemma Gprog_cons : Gprog API Hs =
  (_quickproof_malloc, malloc_spec') :: (_quickproof_free, free_spec') ::
  ZSTD_decompress_spec :: Zstd.proof.zstd.Spec_util.ZSTD_getErrorCode_spec ::
  Zstd.proof.zstd.Spec_xxh.ZSTD_XXH64_spec ::
  [nondet_u8_spec; nondet_size_spec; nondet_bytes_nn_spec; gp_assert_spec; gp_assume_spec] ++
  Hs ++ [main_spec].
Proof. unfold Gprog, Imports. rewrite Externals_eq. reflexivity. Qed.

(* an entry (i, fs) of a list found in Gprog *)
Ltac in_gprog :=
  match goal with |- initial_world.find_id ?i _ = Some ?fs =>
    rewrite Gprog_cons; unfold Hs; cbn [app]; find_steps; reflexivity end.

Lemma G0_in_Gprog i fs : initial_world.find_id i G0 = Some fs ->
  initial_world.find_id i (Gprog API Hs) = Some fs.
Proof.
  intros Hi. apply initial_world.find_id_e in Hi. unfold G0 in Hi.
  rewrite Gprog_cons. unfold Hs. cbn [app].
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
Lemma Gprog_not_var i : In i (map fst (Gprog API Hs)) -> ~ In i (map fst Vprog).
Proof.
  intros Hin Hv.
  assert (Hb: forallb (fun j => negb (id_in_list j (map fst Vprog))) (map fst (Gprog API Hs)) = true).
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

Theorem rfc_skippable_ok : HarnessOK API Hs.
Proof.
  split.
  - vm_compute. reflexivity.
  - repeat constructor.
    + kit_body Zstd.harness.rfc_skippable.code.f_out_of_memory FSpecs.f_out_of_memory G_out_of_memory
        (@Zstd.proof.harness.frames.FBodiesSmall.body_out_of_memory CompSpecs).
    + kit_body Zstd.harness.rfc_skippable.code.f_copy_of FSpecs.f_copy_of (@G_copy_of CompSpecs)
        (@Zstd.proof.harness.frames.FBodiesSmall.body_copy_of CompSpecs).
    + kit_body Zstd.harness.rfc_skippable.code.f_any_bytes FSpecs.f_any_bytes (@G_any_bytes CompSpecs)
        (@Zstd.proof.harness.frames.FBodiesSmall.body_any_bytes CompSpecs).
    + kit_body Zstd.harness.rfc_skippable.code.f_upto FSpecs.f_upto G_upto (@Zstd.proof.harness.frames.FBodiesSmall.body_upto CompSpecs).
    + kit_body Zstd.harness.rfc_skippable.code.f_put_le FSpecs.f_put_le G_put_le
        (@Zstd.proof.harness.frames.FBodiesSmall.body_put_le CompSpecs).
    + kit_body Zstd.harness.rfc_skippable.code.f_join FSpecs.f_join (@G_join CompSpecs)
        (@Zstd.proof.harness.frames.FBodiesSmall.body_join CompSpecs).
    + kit_body Zstd.harness.rfc_skippable.code.f_bytes_eq FSpecs.f_bytes_eq G_bytes_eq
        (@Zstd.proof.harness.frames.FBodiesSmall.body_bytes_eq CompSpecs).
    + kit_body Zstd.harness.rfc_skippable.code.f_new_skippable FSpecs.f_new_skippable (@G_new_skippable CompSpecs)
        (@Zstd.proof.harness.frames.FBodiesSmall.body_new_skippable CompSpecs).
    + kit_body Zstd.harness.rfc_skippable.code.f_new_frame FSpecs.f_new_frame (@G_new_frame CompSpecs)
        (@Zstd.proof.harness.frames.FBodyNewFrame.body_new_frame CompSpecs).
    + (* main *)
      exists f_main. split; [reflexivity|]. split; [reflexivity|].
      eapply semax_body_subsumption; [apply body_main_G0 |].
      apply tycontext_sub_i99. split; intro i.
      * rewrite (make_tycontext_g_find Vprog G0 i).
        rewrite (make_tycontext_g_find Vprog (Gprog API Hs) i).
        destruct (initial_world.find_id i G0) as [fs|] eqn:E.
        -- rewrite (G0_in_Gprog i fs E). apply sub_option_refl.
        -- destruct (initial_world.find_id i (Gprog API Hs)) as [fs'|] eqn:E'.
           ++ rewrite mtg_none; [exact Logic.I |].
              apply (Gprog_not_var i).
              apply initial_world.find_id_e in E'. apply (in_map fst) in E'. exact E'.
           ++ apply sub_option_refl.
      * rewrite !semax_prog.find_id_maketycontext_s.
        destruct (initial_world.find_id i G0) as [fs|] eqn:E; [|exact Logic.I].
        rewrite (G0_in_Gprog i fs E). exists fs. split; [reflexivity|]. apply funspec_sub_si_refl.
Qed.
