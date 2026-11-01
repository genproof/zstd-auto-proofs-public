(* MainOK of the unit stable_out: the main of stable_out adapted to API v3 from its v2 proof. *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.harness.stable_out.WTopSpecs_stable_out.
Require Import Zstd.proof.harness.writer.SeriesLemmas.
Require Zstd.proof.top.MainPre6.
Require Import Zstd.proof.zstd.ApiBridge Zstd.proof.model.ParamsDflt.
Require Import Zstd.proof.model.ParamsWNodictSO.
Require Import Zstd.proof.zstd.NullBuf.

(* ApiBridge.stream_claims_v3_dflt without ParamsW.params_w: from its no-dictionary part, proved
   in ParamsWNodictSO *)
Lemma SO_stream_claims_v3_dflt (st: dctx_st) (sin0 sout0 sin sall sout: list Z) (a1: Z) (ocap: option Z) (r: Z) :
  dc_par st = dparams_dflt -> dc_set st = nil -> dc_dict st = None ->
  (stream_claims_m (dmode_w (dmode_of (dc_par st))) (fst (st_sel st)) (snd (st_sel st)) (dp_wmax (dc_par st))
     sin0 sout0 sin sall sout a1 ocap r <-> stream_claims sin0 sout0 sin sall sout a1 ocap r).
Proof.
  intros Hp Hs Hd. rewrite (st_sel_nil st Hs), Hd, Hp, dmode_of_dflt. simpl fst. simpl snd.
  change (dp_wmax dparams_dflt) with stream_wlim.
  rewrite <- stream_claims_m_dflt. unfold stream_claims_m.
  split; intros H s0 Hb Hpre; specialize (H s0 Hb Hpre);
  rewrite ?series_frames_m_w_nodict_so in *; exact H.
Qed.

(* ---------- what main_pre gives (formerly SOPre.v) ---------- *)

Lemma SO_filter_filter {A: Type} (h g: A -> bool) l:
  (forall x, In x l -> h x = true -> g x = true) -> filter h (filter g l) = filter h l.
Proof.
  induction l as [|a l IH]; simpl; intros H; [reflexivity | ].
  destruct (h a) eqn:Ha.
  - rewrite (H a (or_introl eq_refl) Ha). simpl. rewrite Ha. f_equal. apply IH; auto.
  - destruct (g a); simpl; [rewrite Ha | ]; apply IH; auto.
Qed.

Lemma SO_InitGPred_In x l gv: In x l -> InitGPred l gv |-- globs2pred gv x * TT.
Proof.
  induction l as [|a l IH]; simpl; [contradiction | ].
  rewrite InitGPred_consD. intros [<- | Hin].
  - apply sepcon_derives; [apply derives_refl | apply TT_right].
  - eapply derives_trans; [apply sepcon_derives; [apply derives_refl | apply IH; exact Hin] | ].
    rewrite <- sepcon_assoc, (sepcon_comm (globs2pred gv a)), sepcon_assoc.
    apply sepcon_derives; [apply derives_refl | apply TT_right].
Qed.

Lemma SO_sr_glob gv:
  globs2pred gv (_x_stable_out__sr, Gvar Zstd.harness.x_stable_out.code.v_x_stable_out__sr) |--
  @data_at Zstd.proof.harness.stable_out.HOK_stable_out.CompSpecs Ews t_wseries
    (@zero_val Zstd.proof.harness.stable_out.HOK_stable_out.CompSpecs t_wseries)
    (gv _x_stable_out__sr).
Proof.
  unfold globs2pred, globvar2pred. simpl.
  apply derives_extract_prop; intros Hh.
  unfold init_data_list2pred. rewrite sepcon_emp.
  replace 786936 with (@sizeof Zstd.proof.harness.stable_out.HOK_stable_out.CompSpecs t_wseries)
    by (vm_compute; reflexivity).
  apply (@mapsto_zero_data_at_zero Zstd.proof.harness.stable_out.HOK_stable_out.CompSpecs).
  - apply writable_readable; apply writable_Ews.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply headptr_field_compatible; auto.
    all: first [ vm_compute; reflexivity | apply la_env_cs_sound; vm_compute; reflexivity
               | simpl; rep_lia | simpl; auto ].
Qed.

Lemma so_pre_globals gv :
  globals_ok gv ->
  InitGPred (filter (fun ig => negb (id_in_list (fst ig) Zstd.proof.top.MainPre6.zstd_var_ids))
                    (Vardefs Zstd.contracts.x_stable_out.whole_prog)) gv
  |-- InitGPred wvardefs gv *
      @data_at Zstd.proof.harness.stable_out.HOK_stable_out.CompSpecs Ews t_wseries
        (@zero_val Zstd.proof.harness.stable_out.HOK_stable_out.CompSpecs t_wseries)
        (gv _x_stable_out__sr) * TT.
Proof.
  intros Hgv.
  rewrite (Zstd.proof.top.MainPre6.MP_InitGPred_filter (fun ig => id_in_list (fst ig) wvar_ids)).
  rewrite SO_filter_filter.
  2:{ intros [i g] _. cbn [fst]. intros Hw. apply negb_true_iff.
      apply id_in_list_true in Hw. revert i Hw.
      apply Forall_forall. vm_compute.
      repeat constructor. }
  rewrite (sepcon_assoc (InitGPred wvardefs gv)).
  apply sepcon_derives; [unfold wvardefs; apply derives_refl | ].
  eapply derives_trans;
    [ apply (SO_InitGPred_In (_x_stable_out__sr, Gvar Zstd.harness.x_stable_out.code.v_x_stable_out__sr))
    | apply sepcon_derives; [apply SO_sr_glob | apply derives_refl] ].
  apply filter_In. split; [apply filter_In; split | ].
  - apply (Zstd.proof.top.MainPre6.MP_incl_Vardefs _
             [(_x_stable_out__sr, Gvar Zstd.harness.x_stable_out.code.v_x_stable_out__sr)]);
      [vm_compute; reflexivity | vm_compute; reflexivity | left; reflexivity].
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
Qed.

(* ---------- the stream claims on a written series (formerly SOModel.v, on API v2) ---------- *)

(* ---------- helpers ---------- *)

Lemma so_ok_prefix_app wl fs : exists rest, ok_prefix wl fs ++ rest = fs.
Proof.
  induction fs as [|f fs IH]; simpl.
  - exists nil; reflexivity.
  - destruct (wi_rejected wl f).
    + exists (f :: fs); reflexivity.
    + destruct IH as [rest H]; exists rest; simpl; rewrite H; reflexivity.
Qed.

Lemma so_is_prefix_app (p l x: list Z) : is_prefix p l -> is_prefix p (l ++ x).
Proof.
  unfold is_prefix. revert l. induction p as [|a p IH]; intros l H; [reflexivity|].
  destruct l as [|b l]; simpl in *; [discriminate|].
  injection H as -> H. rewrite (IH l H). reflexivity.
Qed.

Lemma so_is_prefix_sublist (p l: list Z) :
  is_prefix p l -> Zlength p <= Zlength l /\ p = sublist 0 (Zlength p) l.
Proof.
  unfold is_prefix; intros H.
  assert (length p <= length l)%nat.
  { rewrite <- H at 1. rewrite firstn_length. lia. }
  rewrite !Zlength_correct. split; [lia|].
  rewrite sublist_firstn, Nat2Z.id. symmetry; exact H.
Qed.

Lemma so_prefix_of_sublist (l: list Z) ipos :
  0 <= ipos <= Zlength l -> is_prefix (sublist 0 ipos l) l.
Proof.
  intros H. unfold is_prefix. rewrite sublist_firstn.
  rewrite Zlength_correct in H.
  rewrite firstn_length. f_equal. lia.
Qed.

Lemma so_tiles_off fs off coff n cn : tiles fs off coff n cn -> off <= n /\ (fs <> nil -> off < n).
Proof.
  revert off coff. induction fs as [|f fs IH]; simpl; intros off coff H.
  - destruct H; split; [lia | congruence].
  - destruct H as (? & ? & ? & ? & ? & H). apply IH in H. split; intros; lia.
Qed.

Lemma so_tiles_last fs off coff n cn k :
  tiles fs off coff n cn -> (k < length fs)%nat -> wi_end (nth k fs winfo0) = n ->
  k = (length fs - 1)%nat.
Proof.
  revert off coff k. induction fs as [|f fs IH]; simpl; intros off coff k H Hk He; [lia|].
  destruct H as (? & ? & ? & ? & ? & H).
  destruct k as [|k].
  - destruct fs as [|f' fs']; [reflexivity|].
    apply so_tiles_off in H. unfold wi_end in He. destruct H as [_ H].
    specialize (H ltac:(discriminate)). lia.
  - specialize (IH _ _ k H ltac:(lia) He). lia.
Qed.


(* every byte delivered is the content *)
Lemma so_content {sin0 sout0: list Z} {a1: Z} ws ipos sall sout ocap r :
  series_facts no_dict ws -> 0 <= ipos <= Zlength (ws_bytes ws) ->
  stream_claims sin0 sout0 (sublist 0 ipos (ws_bytes ws)) sall sout a1 ocap r ->
  Zlength sout <= Zlength (ws_content ws) /\ sout = sublist 0 (Zlength sout) (ws_content ws).
Proof.
  intros Hf Hi Hc.
  destruct (Hc (ws_bytes ws) (proj1 Hf) (so_prefix_of_sublist _ _ Hi)) as [H _].
  rewrite (series_frames_written _ _ _ Hf) in H; simpl in H.
  assert (Hp : is_prefix sout (flat_map fr_content (map (frec_of ws) (ok_prefix no_wlim (ws_frames ws))))).
  { apply H. destruct (all_ok no_wlim (ws_frames ws)); auto. }
  apply so_is_prefix_sublist.
  rewrite <- (written_content _ _ Hf).
  destruct (so_ok_prefix_app no_wlim (ws_frames ws)) as [rest Hr].
  rewrite <- Hr, map_app, flat_map_app. apply so_is_prefix_app; exact Hp.
Qed.

(* a 0 return after all the bytes: the whole content *)
Lemma so_zero {sin0 sout0: list Z} {a1: Z} ws sall sout ocap :
  series_facts no_dict ws -> stream_claims sin0 sout0 (ws_bytes ws) sall sout a1 ocap 0 -> sout = ws_content ws.
Proof.
  intros Hf Hc.
  assert (Hpre : is_prefix (ws_bytes ws) (ws_bytes ws)) by (apply firstn_all).
  destruct (Hc (ws_bytes ws) (proj1 Hf) Hpre) as (_ & H & _).
  rewrite (series_frames_written _ _ _ Hf) in H; simpl in H.
  destruct H as (n & Hn & Hend & Hout); [reflexivity | destruct (all_ok _ _); discriminate |].
  destruct (so_ok_prefix_app no_wlim (ws_frames ws)) as [rest Hr].
  set (ok := ok_prefix no_wlim (ws_frames ws)) in *.
  rewrite map_length in Hn.
  assert (Hlen : length (ws_frames ws) = (length ok + length rest)%nat)
    by (rewrite <- Hr, app_length; reflexivity).
  rewrite (nth_indep _ _ (frec_of ws winfo0)) in Hend by (rewrite map_length; lia).
  rewrite map_nth in Hend.
  assert (Hnth : nth (n - 1) ok winfo0 = nth (n - 1) (ws_frames ws) winfo0)
    by (rewrite <- Hr, app_nth1 by lia; reflexivity).
  rewrite Hnth in Hend.
  pose proof Hf as (_ & _ & _ & _ & _ & Ht & _).
  pose proof (so_tiles_last _ _ _ _ _ (n - 1) Ht ltac:(lia) (eq_sym Hend)) as Hk.
  assert (rest = nil) by (destruct rest; [reflexivity | simpl in Hlen; lia]). subst rest.
  rewrite app_nil_r in Hr.
  rewrite Hout, firstn_all2 by (rewrite map_length; lia).
  rewrite Hr. exact (written_content _ _ Hf).
Qed.

Lemma so_all_ok_prefix wl fs : all_ok wl fs = true -> ok_prefix wl fs = fs.
Proof.
  unfold all_ok. induction fs as [|f fs IH]; simpl; [reflexivity|].
  intros Hb. apply andb_prop in Hb. destruct Hb as [H1 H2].
  destruct (wi_rejected wl f); [discriminate|]. rewrite IH; auto.
Qed.

(* the errors within zlimits.h's stream range: memory, or zstd's no-progress guard *)
Lemma so_error {sin0 sout0: list Z} {a1: Z} ws ipos sall sout cap r :
  series_facts no_dict ws -> wseries_wf ws -> within_stream_b (ws_frames ws) = true ->
  0 <= ipos <= Zlength (ws_bytes ws) -> is_prefix sall (ws_bytes ws) -> Zlength (ws_content ws) <= cap ->
  stream_claims sin0 sout0 (sublist 0 ipos (ws_bytes ws)) sall sout a1 (Some cap) r -> is_error_code r = true ->
  r = 2 ^ 64 - ZSTD_error_memory_allocation \/ r = 2 ^ 64 - ZSTD_error_noForwardProgress_destFull \/
  r = 2 ^ 64 - ZSTD_error_noForwardProgress_inputEmpty.
Proof.
  intros Hf Hw Hs Hi Hpa Hcap Hc He.
  destruct (Hc (ws_bytes ws) (proj1 Hf) (so_prefix_of_sublist _ _ Hi)) as (_ & _ & _ & H).
  rewrite (series_frames_written _ _ _ Hf) in H.
  pose proof (within_stream_all_ok _ Hw Hs) as Hok.
  rewrite Hok in H.
  specialize (H Hpa eq_refl He (2 ^ 64 - r) ltac:(lia)).
  assert (Hall: ok_prefix stream_wlim (ws_frames ws) = ws_frames ws) by (apply so_all_ok_prefix; exact Hok).
  cbn [fst] in H. rewrite Hall, (written_content _ _ Hf) in H.
  destruct H as [H | [H | [H | (osz & Hosz & Hlt)]]]; [| | | injection Hosz as <-; lia].
  all: unfold ZSTD_error_memory_allocation, ZSTD_error_noForwardProgress_destFull,
    ZSTD_error_noForwardProgress_inputEmpty in *.
  all: lia.
Qed.

Local Notation ZCS := Zstd.proof.zstd.Base.CompSpecs.
Local Notation HCS := Zstd.proof.harness.stable_out.HOK_stable_out.CompSpecs.
Local Notation tout := (Tstruct _ZSTD_outBuffer_s noattr).
Local Notation tin := (Tstruct _ZSTD_inBuffer_s noattr).

Lemma SO_tyc_g_isSome: forall (V: varspecs) G i, In i (map fst V) ->
  isSome (Maps.PTree.get i (make_tycontext_g V G)).
Proof.
  intros. unfold make_tycontext_g. induction G as [|[j f] G IH]; simpl.
  - induction V as [|[k t] V IHV]; simpl in *; [contradiction|].
    rewrite Maps.PTree.gsspec. destruct (peq i k); simpl; auto.
    apply IHV. destruct H; [congruence|auto].
  - rewrite Maps.PTree.gsspec. destruct (peq i j); simpl; auto.
Qed.

(* what each mode knows after its setup: valid = 0, any bytes; valid = 1, the written series ws in sr *)
Definition SO_mode (v n cap: Z) (bs: list Z) (srv: reptype t_wseries) : Prop :=
  (v = 0 /\ n <= 4096 /\ cap <= 65536) \/
  (v = 1 /\ exists ws, series_facts no_dict ws /\ wseries_wf ws /\ bs = ws_bytes ws /\ srv = wseries_val ws /\
           Zlength (ws_content ws) <= cap <= Zlength (ws_content ws) + 16).

(* a malloc'd block of max(1, n) bytes holding bs (then an undefined byte), or NULL *)
Definition SO_blk (p: val) (n: Z) (bs: list Z) : mpred :=
  if eq_dec p nullval then emp
  else (malloc_token Ews (tarray tuchar (Z.max 1 n)) p *
        data_at Ews (tarray tuchar (Z.max 1 n)) (zbytes bs ++ Zrepeat Vundef (Z.max 1 n - n)) p)%logic.

(* list append under a name: a field value written as l1 ++ l2 elaborates very slowly against reptype *)
Definition SO_app (l1 l2: list val) : list val := l1 ++ l2.

Lemma SO_bytes_join sh n (l: list val) p :
  field_compatible t_wseries (DOT _bytes) p -> 0 <= n <= 2 ^ 19 -> Zlength l = n ->
  data_at sh (tarray tuchar n) l (field_address t_wseries (DOT _bytes) p) *
  data_at sh (tarray tuchar (524288 - n)) (Zrepeat (Vint Int.zero) (2 ^ 19 - n))
    (field_address0 (tarray tuchar 524288) (SUB n) (field_address t_wseries (DOT _bytes) p))
  |-- field_at sh t_wseries (DOT _bytes) (SO_app l (Zrepeat (Vint Int.zero) (2 ^ 19 - n))) p.
Proof.
  intros Hfc Hn Hl.
  rewrite (field_at_data_at sh t_wseries (DOT _bytes)).
  change (nested_field_type t_wseries (DOT _bytes)) with (tarray tuchar 524288).
  unfold SO_app.
  rewrite (split2_data_at_Tarray_app n); [apply derives_refl | auto | rewrite Zlength_Zrepeat by lia; reflexivity].
Qed.

Lemma SO_undef_join sh m n (l: list val) p : 0 <= n <= m -> Zlength l = n ->
  data_at sh (tarray tuchar n) l p * data_at_ sh (tarray tuchar (m - n)) (field_address0 (tarray tuchar m) (SUB n) p)
  |-- data_at sh (tarray tuchar m) (l ++ Zrepeat Vundef (m - n)) p.
Proof.
  intros Hn Hl.
  rewrite (split2_data_at_Tarray_app n m sh tuchar l (Zrepeat Vundef (m - n)) p)
    by (auto; rewrite Zlength_Zrepeat; lia).
  apply sepcon_derives; [apply derives_refl|].
  unfold tarray. rewrite data_at__Tarray. apply derives_refl.
Qed.

Lemma SO_undef_split sh m n p : 0 <= n <= m ->
  data_at_ sh (tarray tuchar m) p |--
  data_at_ sh (tarray tuchar n) p * data_at_ sh (tarray tuchar (m - n)) (field_address0 (tarray tuchar m) (SUB n) p).
Proof.
  intros Hn. assert_PROP (field_compatible (tarray tuchar m) [] p) as Hfc by entailer!.
  unfold tarray. rewrite (split2_data_at__Tarray_tuchar sh m n p) by (auto; destruct Hfc; auto).
  apply derives_refl.
Qed.

Lemma SO_ltu_Z x y : 0 <= x <= Int64.max_unsigned -> 0 <= y <= Int64.max_unsigned ->
  Int64.ltu (Int64.repr x) (Int64.repr y) = (x <? y).
Proof.
  intros. unfold Int64.ltu. rewrite !Int64.unsigned_repr by lia.
  destruct (zlt x y); symmetry; [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Qed.

Lemma SO_ltu64_false: forall a b, 0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned -> a <= b ->
  Int64.ltu (Int64.repr b) (Int64.repr a) = false.
Proof.
  intros. unfold Int64.ltu. rewrite !Int64.unsigned_repr by lia.
  destruct (zlt b a); [lia | reflexivity].
Qed.

Ltac SO_absurd :=
  match goal with
  | H: Int.one = Int.zero |- _ => inv H
  | H: Int.repr 1 = Int.zero |- _ => inv H
  | H: Int.zero <> Int.zero |- _ => exfalso; apply H; reflexivity
  | H: Int.repr 0 <> Int.zero |- _ => exfalso; apply H; reflexivity
  end.

(* the test p == NULL / p != NULL of a pointer that is NULL or a malloc'd block *)
Ltac SO_tc_null_test p :=
  apply denote_tc_test_eq_split; [|apply valid_pointer_null];
  destruct (eq_dec p nullval); [subst; apply valid_pointer_null|];
  rewrite ?(if_false (p = nullval)) by auto;
  match goal with |- context [malloc_token ?sh ?t p] =>
    destruct (zlt 0 (sizeof t));
    [ apply derives_trans with (data_at_ sh t p * TT)%logic; [cancel|];
      apply sepcon_valid_pointer1; apply data_at__valid_ptr; [auto | lia]
    | apply derives_trans with (malloc_token sh t p * TT)%logic; [cancel|];
      apply sepcon_valid_pointer1; apply malloc_token_valid_pointer; lia ]
  end.

(* ---------- the decoder's compspecs (API) vs the harness's (main) ---------- *)

Definition SO_cce (cs1 cs2: compspecs) : change_composite_env cs1 cs2 :=
  {| coeq := cs_preserve_env cs1 cs2;
     coeq_consistent := cs_preserve_env_consistent cs1 cs2 _ eq_refl;
     coeq_complete := cs_preserve_completeness cs1 cs2 _ eq_refl |}.

Lemma SO_arr: forall sh n (v: list val) p,
  @data_at ZCS sh (tarray tuchar n) v p = @data_at HCS sh (tarray tuchar n) v p.
Proof.
  intros. pose proof (@data_at_change_composite ZCS HCS (SO_cce ZCS HCS) sh (tarray tuchar n) v v
    (JMeq_refl _) ltac:(reflexivity)) as E. rewrite E; reflexivity.
Qed.

Lemma SO_arr_: forall sh n p,
  @data_at_ ZCS sh (tarray tuchar n) p = @data_at_ HCS sh (tarray tuchar n) p.
Proof.
  intros. pose proof (@data_at__change_composite ZCS HCS (SO_cce ZCS HCS) sh (tarray tuchar n)
    ltac:(reflexivity)) as E. rewrite E; reflexivity.
Qed.

Lemma SO_out: forall sh (a b c: val) p,
  @data_at ZCS sh t_outBuffer (a, (b, c)) p = @data_at HCS sh tout (a, (b, c)) p.
Proof.
  intros. pose proof (@data_at_change_composite ZCS HCS (SO_cce ZCS HCS) sh tout (a, (b, c)) (a, (b, c))
    (JMeq_refl _) ltac:(vm_compute; reflexivity)) as E. exact (f_equal (fun f => f p) E).
Qed.

Lemma SO_in: forall sh (a b c: val) p,
  @data_at ZCS sh t_inBuffer (a, (b, c)) p = @data_at HCS sh tin (a, (b, c)) p.
Proof.
  intros. pose proof (@data_at_change_composite ZCS HCS (SO_cce ZCS HCS) sh tin (a, (b, c)) (a, (b, c))
    (JMeq_refl _) ltac:(vm_compute; reflexivity)) as E. exact (f_equal (fun f => f p) E).
Qed.

(* ---------- buffer witnesses (Spec_api6.buf_ok) ---------- *)

(* the spare byte of a block of max(1, n) bytes holding n bytes, lent when n = 0 *)
Definition SO_W (n: Z) (p: val) : list ptr_witness :=
  if zeq n 0 then [pw_bytes Ews 1 [Vundef] p] else [].

Lemma SO_pws_app W1 W2 : pws_pred (W1 ++ W2) = (pws_pred W1 * pws_pred W2)%logic.
Proof.
  unfold pws_pred. rewrite map_app. induction (map pw_pred W1) as [|a l IH]; simpl.
  - rewrite emp_sepcon; auto.
  - rewrite IH, sepcon_assoc; auto.
Qed.

Lemma SO_buf_ok_pos W n p : 0 < n -> buf_ok W Ews n p.
Proof.
  intros Hn. unfold buf_ok. rewrite data_at__memory_block. rewrite sepcon_andp_prop.
  apply derives_extract_prop; intros FC.
  replace (sizeof (tarray tuchar n)) with n by (simpl; lia).
  assert (Hp: isptr p) by (destruct FC; auto).
  apply andp_right; apply sepcon_weak_valid_pointer2.
  - eapply derives_trans; [apply (memory_block_weak_valid_pointer Ews n p 0); auto; try lia |].
    rewrite isptr_offset_val_zero by auto. apply derives_refl.
  - apply memory_block_weak_valid_pointer; auto; lia.
Qed.

Lemma SO_buf_ok_one W1 W2 c p : buf_ok (W1 ++ pw_bytes Ews 1 c p :: W2) Ews 0 p.
Proof.
  unfold buf_ok. rewrite SO_pws_app. unfold pws_pred at 2. simpl map. simpl fold_right. cbn [pw_pred].
  assert_PROP (isptr p) by (saturate_local; apply prop_right;
    match goal with H: field_compatible _ _ p |- _ => destruct H as [? _]; auto end).
  rewrite isptr_offset_val_zero by auto.
  apply andp_right;
    (apply derives_trans with (@data_at ZCS Ews (tarray tuchar 1) c p * TT)%logic; [cancel|];
     apply sepcon_weak_valid_pointer1;
     eapply derives_trans; [apply data_at_valid_ptr; auto; simpl; lia | apply valid_pointer_weak]).
Qed.

Lemma SO_buf_ok_l W1 W2 n p : buf_ok (W1 ++ W2) Ews n p -> buf_ok (W1 ++ SO_W n p ++ W2) Ews n p.
Proof.
  intros H. unfold SO_W. destruct (zeq n 0).
  - subst. apply SO_buf_ok_one.
  - simpl. auto.
Qed.

(* a block of max(1, cap) bytes as cap bytes and the witness *)
Lemma SO_blk_split n p : 0 <= n ->
  @data_at_ HCS Ews (tarray tuchar (Z.max 1 n)) p |--
  @data_at HCS Ews (tarray tuchar n) (Zrepeat Vundef n) p * pws_pred (SO_W n p).
Proof.
  intros Hn. unfold SO_W. destruct (zeq n 0).
  - subst. change (Z.max 1 0) with 1. unfold pws_pred; simpl map; simpl fold_right; cbn [pw_pred].
    rewrite sepcon_emp. rewrite SO_arr.
    assert_PROP (isptr p) by (saturate_local; apply prop_right;
      match goal with H: field_compatible _ _ p |- _ => destruct H as [? _]; auto end).
    unfold tarray at 1. rewrite data_at__Tarray. change (Zrepeat (default_val tuchar) 1) with [Vundef].
    rewrite <- (emp_sepcon (data_at Ews (Tarray tuchar 1 noattr) [Vundef] p)) at 1.
    apply sepcon_derives; [apply data_at_zero_array; auto | apply derives_refl].
  - rewrite Z.max_r by lia. unfold pws_pred; simpl. rewrite sepcon_emp.
    unfold tarray. rewrite data_at__Tarray. apply derives_refl.
Qed.

Lemma SO_blk_join n (l: list val) p : 0 <= n -> Zlength l = n ->
  @data_at HCS Ews (tarray tuchar n) l p * pws_pred (SO_W n p) |-- @data_at_ HCS Ews (tarray tuchar (Z.max 1 n)) p.
Proof.
  intros Hn Hl. unfold SO_W. destruct (zeq n 0).
  - rewrite e in *. change (Z.max 1 0) with 1. unfold pws_pred; simpl map; simpl fold_right; cbn [pw_pred].
    rewrite sepcon_emp. rewrite SO_arr. apply Zlength_nil_inv in Hl. subst l.
    sep_apply (@data_at_zero_array_inv HCS Ews tuchar (@nil val) p); auto.
    rewrite emp_sepcon. apply data_at_data_at_.
  - rewrite Z.max_r by lia. unfold pws_pred; simpl. rewrite sepcon_emp. apply data_at_data_at_.
Qed.

(* the copy exact_copy makes: its bytes, and the witness *)
Lemma SO_copy_split n (l: list val) p : 0 <= n -> Zlength l = n ->
  @data_at HCS Ews (tarray tuchar (Z.max 1 n)) (l ++ Zrepeat Vundef (Z.max 1 n - n)) p |--
  @data_at ZCS Ews (tarray tuchar n) l p * pws_pred (SO_W n p).
Proof.
  intros Hn Hl. unfold SO_W. destruct (zeq n 0).
  - rewrite e in *. apply Zlength_nil_inv in Hl. subst l. change (Z.max 1 0) with 1.
    unfold pws_pred; simpl map; simpl fold_right; cbn [pw_pred]. rewrite sepcon_emp.
    rewrite !SO_arr. change (@nil val ++ Zrepeat Vundef (1 - 0)) with [Vundef].
    assert_PROP (isptr p) by (saturate_local; apply prop_right;
      match goal with H: field_compatible _ _ p |- _ => destruct H as [? _]; auto end).
    rewrite <- (emp_sepcon (@data_at HCS Ews (tarray tuchar 1) [Vundef] p)) at 1.
    apply sepcon_derives; [apply data_at_zero_array; auto | apply derives_refl].
  - rewrite Z.max_r by lia. rewrite Z.sub_diag. change (Zrepeat Vundef 0) with (@nil val). rewrite app_nil_r.
    unfold pws_pred; simpl. rewrite sepcon_emp. rewrite SO_arr. apply derives_refl.
Qed.

(* the source: the slice [a, a+b) of a byte array, and the rest *)
Lemma SO_slice sh m (l: list val) a b p : 0 <= a -> 0 <= b -> a + b <= m -> Zlength l = m ->
  @data_at HCS sh (tarray tuchar m) l p |--
  @data_at HCS sh (tarray tuchar b) (sublist a (a + b) l) (offset_val a p) *
  (@data_at HCS sh (tarray tuchar b) (sublist a (a + b) l) (offset_val a p) -* @data_at HCS sh (tarray tuchar m) l p).
Proof.
  intros Ha Hb Hab Hl.
  assert_PROP (field_compatible (tarray tuchar m) [] p) as Hfc by entailer!.
  unfold tarray. rewrite (split3_data_at_Tarray_tuchar sh m a (a + b) l p) by lia.
  change (Tarray tuchar m noattr) with (tarray tuchar m).
  rewrite arr_field_address0 by (auto; lia). rewrite arr_field_address0 by (auto; lia).
  change (sizeof tuchar) with 1. rewrite !Z.mul_1_l. replace (a + b - a) with b by lia.
  apply derives_trans with
    (@data_at HCS sh (Tarray tuchar b noattr) (sublist a (a + b) l) (offset_val a p) *
     (@data_at HCS sh (Tarray tuchar a noattr) (sublist 0 a l) p *
      @data_at HCS sh (Tarray tuchar (m - (a + b)) noattr) (sublist (a + b) m l) (offset_val (a + b) p)))%logic;
    [cancel|].
  apply sepcon_derives; [apply derives_refl|]. apply (proj1 (wand_sepcon_adjoint _ _ _)). cancel.
Qed.

(* all three allocations of main succeeded *)
Definition SO_nn (src dst ds: val) : bool :=
  if eq_dec src nullval then false else if eq_dec dst nullval then false else if eq_dec ds nullval then false else true.

(* the context, or NULL *)
Definition SO_dc (DC: globals -> val -> dctx_st -> mpred) (gv: globals) (ds: val) (st: dctx_st) : mpred :=
  if eq_dec ds nullval then emp else DC gv ds st.

(* the output buffer dst (cap bytes oc, and the witness of an empty one), or NULL *)
Definition SO_dst (dst: val) (cap: Z) (oc: list val) : mpred :=
  if eq_dec dst nullval then emp
  else (malloc_token Ews (tarray tuchar (Z.max 1 cap)) dst * data_at Ews (tarray tuchar cap) oc dst *
        pws_pred (SO_W cap dst))%logic.

(* the stream's state between calls: positions, the stable buffer, and in mode valid = 1 the stall count and
   the bytes consumed (the series' first ipos bytes, no reset in that mode) *)
Definition SO_core (v n cap nn: Z) (src dst ds: val) (bs: list Z) (ipos stalled opos: Z) (st: dctx_st)
    (oc: list val) : Prop :=
  0 <= ipos <= nn /\ 0 <= opos <= cap /\
  (nn = 0 \/
   (nn = n /\ SO_nn src dst ds = true /\ dc_dict st = None /\
    dc_par st = dparams_dflt /\ dc_set st = nil /\ dc_bl st = None /\ dc_stable st = true /\ ss_err (dc_ss st) = false /\
    (ss_obuf (dc_ss st) = None \/ ss_obuf (dc_ss st) = Some (dst, cap)) /\ opos = Zlength (ss_out (dc_ss st)) /\
    sublist 0 opos oc = zbytes (ss_out (dc_ss st)) /\
    (v = 1 -> ss_stall (dc_ss st) <= stalled /\ ss_in (dc_ss st) = sublist 0 (ipos + ss_ahead (dc_ss st)) bs /\
              0 <= ss_ahead (dc_ss st) /\ ipos + ss_ahead (dc_ss st) <= n))).

Definition SO_inv (DC: globals -> val -> dctx_st -> mpred) (WG: globals -> mpred) (gv: globals) (v_in v_out: val)
    (v n cap nn: Z) (src dst ds: val) (bs: list Z) (srv: reptype t_wseries) (lo: Z)
    (calls ipos stalled opos: Z) (oc: list val) (st: dctx_st) : environ -> mpred :=
  PROP (SO_mode v n cap bs srv; Zlength bs = n; bytes_ok bs; 0 <= n <= 2 ^ 19; 0 <= cap <= 2 ^ 19; 0 <= v < 2;
        is_pointer_or_null src; is_pointer_or_null dst; is_pointer_or_null ds;
        0 <= calls; calls + lo <= 4096; 0 <= stalled <= calls + lo; Zlength oc = cap;
        SO_core v n cap nn src dst ds bs ipos stalled opos st oc)
  LOCAL (temp _calls (Vlong (Int64.repr calls)); temp _ipos (Vlong (Int64.repr ipos));
         temp _stalled (Vlong (Int64.repr stalled)); temp _n (Vlong (Int64.repr nn));
         temp _ds ds; temp _dst dst; temp _src src; temp _cap (Vlong (Int64.repr cap));
         temp _valid (Vint (Int.repr v)); lvar _in tin v_in; lvar _out tout v_out; gvars gv)
  SEP (mem_mgr gv; zstd_globals gv; SO_dc DC gv ds st; SO_dst dst cap oc; data_at_ Tsh tin v_in;
       data_at Tsh tout (dst, (Vlong (Int64.repr cap), Vlong (Int64.repr opos))) v_out; WG gv;
       data_at Ews t_wseries srv (gv _x_stable_out__sr); TT; has_ext tt; SO_blk src n bs).

Definition SO_brk (DC: globals -> val -> dctx_st -> mpred) (WG: globals -> mpred) (gv: globals) (v_in v_out: val)
    (n cap: Z) (src dst ds: val) (bs: list Z) : environ -> mpred :=
  EX st: dctx_st, EX oc: list val,
  PROP (Zlength oc = cap; 0 <= n <= 2 ^ 19; 0 <= cap <= 2 ^ 19; Zlength bs = n)
  LOCAL (temp _ds ds; temp _dst dst; temp _src src; lvar _in tin v_in; lvar _out tout v_out; gvars gv)
  SEP (mem_mgr gv; zstd_globals gv; SO_dc DC gv ds st; SO_dst dst cap oc; data_at_ Tsh tin v_in;
       data_at_ Tsh tout v_out; TT; has_ext tt; SO_blk src n bs).

Lemma SO_sub_zbytes (bs: list Z) (u: list val) a b : 0 <= a -> 0 <= b -> a + b <= Zlength bs ->
  sublist a (a + b) (zbytes bs ++ u) = zbytes (sublist a (a + b) bs).
Proof.
  intros. rewrite sublist_app1 by (rewrite ?Zlength_map; lia). rewrite sublist_map. reflexivity.
Qed.

(* the slice of the source exact_copy copies *)
Lemma SO_src_slice n (bs: list Z) a b p : 0 <= a -> 0 <= b -> a + b <= n -> Zlength bs = n ->
  data_at Ews (tarray tuchar (Z.max 1 n)) (zbytes bs ++ Zrepeat Vundef (Z.max 1 n - n)) p |--
  data_at Ews (tarray tuchar (Zlength (sublist a (a + b) bs))) (zbytes (sublist a (a + b) bs)) (offset_val a p) *
  (data_at Ews (tarray tuchar (Zlength (sublist a (a + b) bs))) (zbytes (sublist a (a + b) bs)) (offset_val a p) -*
   data_at Ews (tarray tuchar (Z.max 1 n)) (zbytes bs ++ Zrepeat Vundef (Z.max 1 n - n)) p).
Proof.
  intros Ha Hb Hab Hl.
  rewrite Zlength_sublist by lia. replace (a + b - a) with b by lia.
  rewrite <- (SO_sub_zbytes bs (Zrepeat Vundef (Z.max 1 n - n)) a b) by lia.
  apply SO_slice; try lia. rewrite Zlength_app, Zlength_map, Zlength_Zrepeat by lia. lia.
Qed.

(* the witnesses of ZSTD_decompressStream's two buffers *)
Lemma SO_buf_ok_dst cap dst il ib : 0 <= cap -> buf_ok (SO_W cap dst ++ SO_W il ib) Ews cap dst.
Proof.
  intros Hc. unfold SO_W at 1. destruct (zeq cap 0).
  - subst. apply (SO_buf_ok_one [] (SO_W il ib)).
  - apply SO_buf_ok_pos. lia.
Qed.

Lemma SO_buf_ok_ib cap dst il ib : 0 <= il -> buf_ok (SO_W cap dst ++ SO_W il ib) Ews il ib.
Proof.
  intros Hc. unfold SO_W at 2. destruct (zeq il 0).
  - subst. apply (SO_buf_ok_one (SO_W cap dst) []).
  - rewrite app_nil_r. apply SO_buf_ok_pos. lia.
Qed.

Lemma SO_pws_join W1 W2 : pws_pred W1 * pws_pred W2 |-- pws_pred (W1 ++ W2).
Proof. rewrite SO_pws_app. apply derives_refl. Qed.

Lemma SO_pws_split W1 W2 : pws_pred (W1 ++ W2) |-- pws_pred W1 * pws_pred W2.
Proof. rewrite SO_pws_app. apply derives_refl. Qed.

Lemma SO_dl_len opos opos' (oc: list val) dl : 0 <= opos <= opos' -> opos' <= Zlength oc ->
  sublist opos opos' oc = zbytes dl -> Zlength dl = opos' - opos.
Proof.
  intros H1 H2 H3. apply (f_equal (@Zlength val)) in H3. rewrite Zlength_sublist in H3 by lia.
  rewrite Zlength_map in H3. lia.
Qed.

(* the fields of a wseries_t (by the generic value, to keep the value's types out of the statement) *)
Lemma SO_ws_unfold sh (vs: reptype t_wseries) p :
  data_at sh t_wseries vs p |--
  field_at sh t_wseries (DOT _bytes) (fst vs) p *
  field_at sh t_wseries (DOT _n) (fst (snd vs)) p *
  field_at sh t_wseries (DOT _content) (fst (snd (snd vs))) p *
  field_at sh t_wseries (DOT _content_n) (fst (snd (snd (snd vs)))) p *
  field_at sh t_wseries (DOT _f) (fst (snd (snd (snd (snd vs))))) p *
  field_at sh t_wseries (DOT _nframes) (snd (snd (snd (snd (snd vs))))) p *
  spacer sh 786932 786936 p.
Proof. unfold_data_at (data_at _ _ _ _). cancel. Qed.

Lemma SO_ws_fold sh (vs: reptype t_wseries) p :
  field_at sh t_wseries (DOT _bytes) (fst vs) p *
  field_at sh t_wseries (DOT _n) (fst (snd vs)) p *
  field_at sh t_wseries (DOT _content) (fst (snd (snd vs))) p *
  field_at sh t_wseries (DOT _content_n) (fst (snd (snd (snd vs)))) p *
  field_at sh t_wseries (DOT _f) (fst (snd (snd (snd (snd vs))))) p *
  field_at sh t_wseries (DOT _nframes) (snd (snd (snd (snd (snd vs))))) p *
  spacer sh 786932 786936 p
  |-- data_at sh t_wseries vs p.
Proof. unfold_data_at (data_at _ _ _ _). cancel. Qed.

Lemma SO_in_app (bs: list Z) ipos il ipos' : 0 <= ipos -> 0 <= ipos' <= il -> ipos + il <= Zlength bs ->
  sublist 0 ipos bs ++ sublist 0 ipos' (sublist ipos (ipos + il) bs) = sublist 0 (ipos + ipos') bs.
Proof.
  intros. rewrite sublist_sublist by lia.
  replace (0 + ipos) with ipos by lia. replace (ipos' + ipos) with (ipos + ipos') by lia.
  rewrite <- (sublist_split 0 ipos (ipos + ipos')) by lia. reflexivity.
Qed.

(* the bytes zstd has read after a call: the series' first ipos + ipos' + a' bytes *)
Lemma SO_in_app2 (bs: list Z) ipos il ah ipos' a' : 0 <= ipos -> 0 <= ah -> ipos + il <= Zlength bs ->
  0 <= ipos' -> 0 <= a' -> ah <= ipos' + a' -> (ipos' + a' <= il \/ ipos' + a' = ah) ->
  sublist 0 (ipos + ah) bs ++ sublist (0 + ah) (ipos' + a') (sublist ipos (ipos + il) bs) =
  sublist 0 (ipos + (ipos' + a')) bs.
Proof.
  intros H0 H1 H2 H3 H4 H5 [H6 | H6].
  - rewrite sublist_sublist by lia.
    replace (0 + ah + ipos) with (ipos + ah) by lia. replace (ipos' + a' + ipos) with (ipos + (ipos' + a')) by lia.
    rewrite <- (sublist_split 0 (ipos + ah) (ipos + (ipos' + a'))) by lia. reflexivity.
  - rewrite H6, Z.add_0_l, sublist_nil, app_nil_r. first [reflexivity | f_equal; lia].
Qed.

(* the bytes read and the rest of the chunk: a prefix of the series *)
Lemma SO_sall_prefix (bs: list Z) ipos il j : 0 <= ipos -> 0 <= j -> ipos + il <= Zlength bs ->
  ipos + j <= Zlength bs -> 0 <= il ->
  is_prefix (sublist 0 (ipos + j) bs ++ sublist j il (sublist ipos (ipos + il) bs)) bs.
Proof.
  intros H0 H1 H2 H3 H4. destruct (Z_le_gt_dec j il).
  - rewrite sublist_sublist by lia.
    replace (j + ipos) with (ipos + j) by lia. replace (il + ipos) with (ipos + il) by lia.
    rewrite <- (sublist_split 0 (ipos + j) (ipos + il)) by lia.
    apply so_prefix_of_sublist. lia.
  - rewrite (sublist_nil_gen _ j il) by lia. rewrite app_nil_r. apply so_prefix_of_sublist. lia.
Qed.

(* the output buffer's first opos' bytes: what the stream has delivered *)
Lemma SO_out_prefix (oc oc': list val) opos opos' (so dl: list Z) : 0 <= opos <= opos' -> opos' <= Zlength oc' ->
  sublist 0 opos oc' = sublist 0 opos oc -> sublist 0 opos oc = zbytes so -> sublist opos opos' oc' = zbytes dl ->
  sublist 0 opos' oc' = zbytes (so ++ dl).
Proof.
  intros H1 H2 H3 H4 H5. rewrite (sublist_split 0 opos opos' oc') by lia.
  rewrite H3, H4, H5. rewrite map_app. reflexivity.
Qed.

(* a byte the stream delivered into dst is the content *)
Lemma SO_dst_byte (oc: list val) (sout dl c: list Z) opos opos' i :
  0 <= opos <= i -> i < opos' -> opos' <= Zlength oc ->
  opos = Zlength sout -> sublist opos opos' oc = zbytes dl ->
  sout ++ dl = sublist 0 opos' c -> opos' <= Zlength c ->
  Znth i oc = Vint (Int.repr (Znth i c)).
Proof.
  intros H1 H2 H3 H4 H5 H6 H7.
  assert (Hdl: Zlength dl = opos' - opos).
  { apply (f_equal (@Zlength val)) in H5. rewrite Zlength_sublist in H5 by lia. rewrite Zlength_map in H5. lia. }
  replace (Znth i oc) with (Znth (i - opos) (sublist opos opos' oc)) by (rewrite Znth_sublist by lia; f_equal; lia).
  rewrite H5. rewrite Znth_map by lia. f_equal. f_equal.
  replace (Znth (i - opos) dl) with (Znth i (sout ++ dl)) by (rewrite Znth_app2 by lia; f_equal; lia).
  rewrite H6. rewrite Znth_sublist by lia. f_equal. lia.
Qed.

(* the harness's error check: memory, or zstd's no-progress guard (zlimits.h stall_error) *)
Lemma SO_err_ok {sin0 sout0: list Z} {a1: Z} ws ipos sall sout r stall stalled opos opos' ipos' il cap :
  series_facts no_dict ws -> wseries_wf ws -> within_stream_b (ws_frames ws) = true ->
  0 <= ipos <= Zlength (ws_bytes ws) -> is_prefix sall (ws_bytes ws) -> Zlength (ws_content ws) <= cap ->
  stream_claims sin0 sout0 (sublist 0 ipos (ws_bytes ws)) sall sout a1 (Some cap) r ->
  is_error_code r = true -> stall_ok r stall 0 ipos' il opos opos' cap -> stall <= stalled ->
  error_of r = ZSTD_error_memory_allocation \/ stall_error_b (error_of r) stalled ipos' il opos' cap opos = true.
Proof.
  intros Hsf Hwf Hws Hip Hpa Hcap Hcl Herr Hst Hle.
  destruct (so_error ws ipos sall sout cap r Hsf Hwf Hws Hip Hpa Hcap Hcl Herr) as [E | [E | E]];
    unfold error_of; rewrite Herr.
  - left. rewrite E. reflexivity.
  - right. destruct (Hst (or_introl E)) as (Hs & -> & -> & [[_ Ho] | [E' _]]).
    + rewrite E. unfold stall_error_b, NO_PROGRESS_MAX, ZSTD_error_noForwardProgress_destFull,
        ZSTD_NO_FORWARD_PROGRESS_MAX in *.
      replace (2 ^ 64 - (2 ^ 64 - 80)) with 80 by lia.
      replace (stalled + 1 <? 16) with false by (symmetry; apply Z.ltb_ge; lia).
      rewrite ?Z.eqb_refl. simpl. subst. rewrite ?Z.eqb_refl. reflexivity.
    + rewrite E in E'. unfold ZSTD_error_noForwardProgress_destFull, ZSTD_error_noForwardProgress_inputEmpty in E'. lia.
  - right. destruct (Hst (or_intror E)) as (Hs & -> & -> & [[E' _] | [_ [Ho Hi]]]).
    + rewrite E in E'. unfold ZSTD_error_noForwardProgress_destFull, ZSTD_error_noForwardProgress_inputEmpty in E'. lia.
    + rewrite E. unfold stall_error_b, NO_PROGRESS_MAX, ZSTD_error_noForwardProgress_inputEmpty,
        ZSTD_error_noForwardProgress_destFull, ZSTD_NO_FORWARD_PROGRESS_MAX in *.
      replace (2 ^ 64 - (2 ^ 64 - 82)) with 82 by lia.
      replace (stalled + 1 <? 16) with false by (symmetry; apply Z.ltb_ge; lia).
      subst. rewrite ?Z.eqb_refl. simpl.
      replace (opos <? cap) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma SO_byte_range (c: list Z) i : bytes_ok c -> 0 <= i < Zlength c -> 0 <= Znth i c < 256.
Proof. intros Hc Hi. exact (proj1 (Forall_Znth _ _) Hc i Hi). Qed.

Lemma SO_tc_byte (c: list Z) i : bytes_ok c -> 0 <= i < Zlength c -> tc_val tuchar (Vint (Int.repr (Znth i c))).
Proof.
  intros Hc Hi. pose proof (SO_byte_range c i Hc Hi). simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia.
Qed.

Lemma SO_cont_byte (c: list Z) i : 0 <= i < Zlength c ->
  Znth i (zbytes c ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength c)) = Vint (Int.repr (Znth i c)).
Proof. intros. rewrite Znth_app1 by (rewrite Zlength_map; lia). rewrite Znth_map by lia. reflexivity. Qed.

(* API v3: the context's dictionary resources, empty for a context without dictionary or DDict set *)
Lemma SO_dc_res (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred) gv ds st :
  dc_dict st = None -> dc_set st = nil ->
  DC gv ds st |-- DC gv ds st * (dict_res DD gv Ews (dc_dict st) * set_res DD gv Ews (dc_set st) (dc_dict st)).
Proof. intros Hd Hs. rewrite Hd, Hs. unfold dict_res, set_res. simpl. rewrite !sepcon_emp. apply derives_refl. Qed.

Lemma SO_res_emp (DD: globals -> val -> ddict_st -> mpred) gv :
  dict_res DD gv Ews None = emp /\ set_res DD gv Ews nil None = emp.
Proof. split; reflexivity. Qed.

Theorem main_ok3_stable_out : MainOK.
Proof.
intros DC DD WG WDS HWG.
unfold main_spec, QPmain_spec_ext', NDmk_funspec.
split3; [reflexivity | reflexivity |].
intros Espec DTL gv.
simpl fn_body; simpl fn_params; simpl fn_return.
change (map fst []) with (@nil ident).
eapply (main_pre_InitGpred
          (Zstd.proof.zstd.Globals.zstd_globals gv * WG gv *
           @data_at HCS Ews t_wseries (@zero_val HCS t_wseries) (gv _x_stable_out__sr) * TT)%logic _ _ _
          Zstd.contracts.x_stable_out.whole_prog).
4: idtac.
- intros. eapply derives_trans.
  + apply (Zstd.proof.top.MainPre6.main_pre_fact6 Zstd.contracts.x_stable_out.whole_prog); [|exact H].
    unfold Zstd.proof.top.MainPre6.all_progs. do 7 right; left; reflexivity.
  + sep_apply (so_pre_globals gv H). sep_apply (HWG gv). cancel.
- reflexivity.
- apply Forall_forall; intros [i g] Hin; simpl fst.
  apply SO_tyc_g_isSome. unfold Vprog, QPvarspecs. rewrite map_map.
  apply in_map_iff. exists (i, g); auto.
- process_stackframe_of.
  repeat rewrite <- data_at__offset_zero.
  try simple apply start_function_aux1.
  match goal with |- semax ?D ?P ?c (frame_ret_assert (function_body_ret_assert ?t _) ?F) =>
    apply (semax_post (frame_ret_assert (function_body_ret_assert t (PROP () LOCAL () (SEP (TT)))) F))
  end.
  1,2,3: intros; simpl; normalize.
  1: intros [v|]; simpl; unfold bind_ret; simpl; normalize;
       intros x; apply andp_left2; apply sepcon_derives; [unfold_lift; apply TT_right | auto].
  abbreviate_semax.
  sep_apply (create_mem_mgr gv).
  forward_call 2.
  Intros v. forward. forward.
  forward_if (EX n: Z, EX cap: Z, EX src: val, EX bs: list Z, EX srv: reptype t_wseries,
    PROP (SO_mode v n cap bs srv; Zlength bs = n; bytes_ok bs; 0 <= n <= 2 ^ 19; 0 <= cap <= 2 ^ 19;
          is_pointer_or_null src)
    LOCAL (temp _src src; temp _cap (Vlong (Int64.repr cap)); temp _n (Vlong (Int64.repr n));
           temp _stalled (Vlong (Int64.repr 0)); temp _ipos (Vlong (Int64.repr 0));
           temp _valid (Vint (Int.repr v)); lvar _in tin v_in; lvar _out tout v_out; gvars gv)
    SEP (mem_mgr gv; data_at_ Tsh tin v_in; data_at_ Tsh tout v_out; zstd_globals gv; WG gv;
         data_at Ews t_wseries srv (gv _x_stable_out__sr); TT; has_ext tt; SO_blk src n bs)).
  { forward_call (gv, Ews, gv _x_stable_out__sr, nullval, @None (wdict * share)).
    { unfold wdict_arg. entailer!. }
    Intros ws.
    unfold_data_at (data_at _ _ (wseries_val _) _). unfold wseries_val. cbn [fst snd]. forward.
    pose proof H1 as Hsf.
    destruct H1 as (Hb & Hc & Hbn & Hcn & Hfr & Htl & Hff & Hfcs & Hfds & Hbd).
    assert_PROP (field_compatible t_wseries (DOT _bytes) (gv _x_stable_out__sr)) as Hfcb by entailer!.
    rewrite (field_at_data_at Ews t_wseries (DOT _bytes)).
    change (nested_field_type t_wseries (DOT _bytes)) with (tarray tuchar 524288).
    rewrite (split2_data_at_Tarray_app (Zlength (ws_bytes ws)));
      [| rewrite Zlength_map; reflexivity | rewrite Zlength_Zrepeat by lia; reflexivity].
    flatten_sepcon_in_SEP.
    forward_call (gv, Ews, field_address t_wseries (DOT _bytes) (gv _x_stable_out__sr), ws_bytes ws).
    { entailer!. simpl. unfold field_address. rewrite if_true by auto. reflexivity. }
    Intros src.
    forward. forward. forward_call (Zlength (ws_content ws), Zlength (ws_content ws) + 16).
    Intros cap. forward.
    sep_apply (SO_bytes_join Ews (Zlength (ws_bytes ws)) (zbytes (ws_bytes ws)) (gv _x_stable_out__sr) Hfcb
                 ltac:(rep_lia) ltac:(rewrite Zlength_map; reflexivity)).
    Exists (Zlength (ws_bytes ws)) cap src (ws_bytes ws) (wseries_val ws).
    unfold_data_at (data_at _ _ (wseries_val _) _). cbn [fst snd wseries_val]. unfold SO_app.
    entailer!.
    { right. split; [lia|]. exists ws. split; [exact Hsf|]. split; [auto|]. split; [auto|]. split; [auto|]. lia. }
    unfold SO_blk. cancel. }
  { assert (Hv0: v = 0) by (apply (f_equal Int.unsigned) in H0; rewrite Int.unsigned_repr in H0 by rep_lia; exact H0).
    forward_call tt. Intros n.
    forward_call (if Int64.ltu (Int64.repr 4096) (Int64.repr n) then Int.zero else Int.one).
    { entailer!. simpl. destruct (Int64.ltu _ _); reflexivity. }
    Intros. match goal with H: (if _ then _ else _) <> _ |- _ => rename H into Ha end.
    assert (Hn: n <= 4096).
    { destruct (Int64.ltu (Int64.repr 4096) (Int64.repr n)) eqn:E; [exfalso; apply Ha; reflexivity|].
      rewrite SO_ltu_Z in E by rep_lia. apply Z.ltb_ge in E. lia. }
    clear Ha.
    match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (cons (temp _x_stable_out__t'5 (Vlong (Int64.repr (Z.max 1 n)))) L) (SEPx R)))
    end.
    { forward. entailer!.
      match goal with H: Int64.unsigned _ < Int64.unsigned _ |- _ => rewrite !Int64.unsigned_repr in H by rep_lia end.
      rewrite Z.max_r by lia. reflexivity. }
    { forward. entailer!.
      match goal with H: Int64.unsigned _ >= Int64.unsigned _ |- _ => rewrite !Int64.unsigned_repr in H by rep_lia end.
      replace n with 0 by lia. reflexivity. }
    forward_call (tarray tuchar (Z.max 1 n), gv).
    { simpl. rewrite Z.max_r by lia. rep_lia. }
    Intros src. forward.
    match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx (cons _ (cons _ ?R))))) _ _ =>
      forward_if (EX bs: list Z, PROPx (cons (Zlength bs = n) (cons (bytes_ok bs) P)) (LOCALx L (SEPx (cons (mem_mgr gv) (cons (SO_blk src n bs) R)))))
    end.
    { SO_tc_null_test src. }
    { rewrite if_false by auto. Intros.
      sep_apply (SO_undef_split Ews (Z.max 1 n) n src ltac:(lia)).
      flatten_sepcon_in_SEP.
      forward_call (src, n, Ews).
      Intros bs. Exists bs. unfold SO_blk. rewrite if_false by auto.
      sep_apply (SO_undef_join Ews (Z.max 1 n) n (map (fun b => Vint (Int.repr b)) bs) src
                   ltac:(lia) ltac:(rewrite Zlength_map; auto)).
      entailer!.
      unfold bytes_ok, is_byte. eapply Forall_impl; [|eassumption]. intros; simpl in *; rep_lia. }
    { forward. Exists (Zrepeat 0 n). unfold SO_blk.
      assert (src = nullval) by (destruct (eq_dec src nullval); auto; contradiction).
      subst src. rewrite !if_true by auto. entailer!.
      rewrite Zlength_Zrepeat by lia. split; auto.
      unfold bytes_ok, Zrepeat. apply Forall_forall. intros x Hx. apply repeat_spec in Hx. subst. unfold is_byte; rep_lia. }
    Intros bs.
    forward_call tt. Intros cap.
    forward_call (if Int64.ltu (Int64.repr 65536) (Int64.repr cap) then Int.zero else Int.one).
    { entailer!. simpl. destruct (Int64.ltu _ _); reflexivity. }
    Intros. match goal with H: (if _ then _ else _) <> _ |- _ => rename H into Ha end.
    assert (Hcap: cap <= 65536).
    { destruct (Int64.ltu (Int64.repr 65536) (Int64.repr cap)) eqn:E; [exfalso; apply Ha; reflexivity|].
      rewrite SO_ltu_Z in E by rep_lia. apply Z.ltb_ge in E. lia. }
    clear Ha.
    Exists n cap src bs (@zero_val HCS t_wseries).
    entailer!.
    left. split; [lia|]. split; lia. }
  Intros n cap src bs srv.
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (cons (temp _x_stable_out__t'8 (Vlong (Int64.repr (Z.max 1 cap)))) L) (SEPx R)))
  end.
  { forward. entailer!.
    match goal with H: Int64.unsigned _ < Int64.unsigned _ |- _ => rewrite !Int64.unsigned_repr in H by rep_lia end.
    rewrite Z.max_r by lia. reflexivity. }
  { forward. entailer!.
    match goal with H: Int64.unsigned _ >= Int64.unsigned _ |- _ => rewrite !Int64.unsigned_repr in H by rep_lia end.
    replace cap with 0 by lia. reflexivity. }
  forward_call (tarray tuchar (Z.max 1 cap), gv).
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros dst. forward.
  forward_call gv. Intros ds.
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (cons (temp _x_stable_out__t'11 (Vint (if eq_dec src nullval then Int.one else if eq_dec dst nullval then Int.one else Int.zero))) L) (SEPx R)))
  end.
  { unfold SO_blk. SO_tc_null_test src. }
  { forward. destruct (eq_dec src nullval); [|contradiction]. entailer!. }
  { forward.
    { entailer!. SO_tc_null_test dst. }
    destruct (eq_dec src nullval); [contradiction|].
    destruct (eq_dec dst nullval); entailer!.
    destruct dst; try contradiction; try reflexivity; (hnf in PNdst; subst; exfalso; apply n1; reflexivity). }
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (cons (temp _x_stable_out__t'12 (Vint (if SO_nn src dst ds then Int.zero else Int.one))) L) (SEPx R)))
  end.
  { forward. entailer!. unfold SO_nn.
    change (EqDec_val src nullval) with (eq_dec src nullval) in *.
    change (EqDec_val dst nullval) with (eq_dec dst nullval) in *.
    destruct (eq_dec src nullval); auto. destruct (eq_dec dst nullval); auto.
    match goal with H: Int.repr 0 <> Int.zero |- _ => exfalso; apply H; reflexivity end. }
  { forward.
    { entailer!. apply denote_tc_test_eq_split; [|apply valid_pointer_null].
      destruct (eq_dec ds nullval); [subst; apply valid_pointer_null|].
      apply derives_trans with ((DC gv ds dctx_init && valid_pointer ds) * TT)%logic; [cancel|].
      apply sepcon_valid_pointer1. apply andp_left2. auto. }
    unfold SO_nn.
    change (EqDec_val src nullval) with (eq_dec src nullval) in *.
    change (EqDec_val dst nullval) with (eq_dec dst nullval) in *.
    destruct (eq_dec src nullval); [SO_absurd|]. destruct (eq_dec dst nullval); [SO_absurd|].
    destruct (eq_dec ds nullval); entailer!.
    destruct ds; try contradiction; try reflexivity; (hnf in PNds; subst; exfalso; apply n2; reflexivity). }
  forward_if (EX st: dctx_st,
    PROP (SO_nn src dst ds = true -> st = set_stable dctx_init true)
    LOCAL (temp _x_stable_out__t'13 (Vint (if SO_nn src dst ds then Int.zero else Int.one));
           temp _ds ds; temp _dst dst; temp _src src; temp _cap (Vlong (Int64.repr cap));
           temp _n (Vlong (Int64.repr n)); temp _stalled (Vlong (Int64.repr 0));
           temp _ipos (Vlong (Int64.repr 0)); temp _valid (Vint (Int.repr v));
           lvar _in tin v_in; lvar _out tout v_out; gvars gv)
    SEP (mem_mgr gv; zstd_globals gv; SO_dc DC gv ds st;
         if eq_dec dst nullval then emp
         else (malloc_token Ews (tarray tuchar (Z.max 1 cap)) dst * data_at_ Ews (tarray tuchar (Z.max 1 cap)) dst)%logic;
         data_at_ Tsh tin v_in; data_at_ Tsh tout v_out; WG gv;
         data_at Ews t_wseries srv (gv _x_stable_out__sr); TT; has_ext tt; SO_blk src n bs)).
  { forward. Exists dctx_init. unfold SO_dc.
    destruct (SO_nn src dst ds); [contradiction|].
    destruct (eq_dec ds nullval).
    - entailer!.
    - entailer!. apply sepcon_derives; [apply andp_left1; auto | auto]. }
  { assert (Hnn: SO_nn src dst ds = true) by (destruct (SO_nn src dst ds); auto; discriminate).
    unfold SO_nn in Hnn.
    destruct (eq_dec src nullval); [discriminate|]. destruct (eq_dec dst nullval); [discriminate|].
    destruct (eq_dec ds nullval); [discriminate|].
    sep_apply (andp_left1 (DC gv ds dctx_init) (valid_pointer ds) (DC gv ds dctx_init) (derives_refl _)).
    forward_call (gv, ds, dctx_init, ZSTD_d_stableOutBuffer, 1).
    { right; right; left; reflexivity. }
    Intros vret. destruct vret as [r st']. cbn [fst snd] in *.
    match goal with H: after_stage _ _ _ _ |- _ =>
      apply after_stage_init in H; [unfold setpar_res in H | reflexivity] end.
    match goal with H: if _ =? _ then _ else _ |- _ =>
      rewrite Z.eqb_refl in H; cbn [andb Z.leb Z.compare Z.eqb Pos.eqb] in H; destruct H as [-> ->] end.
    forward_call 0.
    forward.
    Exists (set_stable dctx_init true). unfold SO_dc, SO_nn.
    rewrite !if_false by auto. entailer!. }
  Intros st.
  forward_if (EX nn: Z,
    PROP (nn = 0 \/ (nn = n /\ SO_nn src dst ds = true))
    LOCAL (temp _ds ds; temp _dst dst; temp _src src; temp _cap (Vlong (Int64.repr cap));
           temp _n (Vlong (Int64.repr nn)); temp _stalled (Vlong (Int64.repr 0));
           temp _ipos (Vlong (Int64.repr 0)); temp _valid (Vint (Int.repr v));
           lvar _in tin v_in; lvar _out tout v_out; gvars gv)
    SEP (mem_mgr gv; zstd_globals gv; SO_dc DC gv ds st;
         if eq_dec dst nullval then emp
         else (malloc_token Ews (tarray tuchar (Z.max 1 cap)) dst * data_at_ Ews (tarray tuchar (Z.max 1 cap)) dst)%logic;
         data_at_ Tsh tin v_in; data_at_ Tsh tout v_out; WG gv;
         data_at Ews t_wseries srv (gv _x_stable_out__sr); TT; has_ext tt; SO_blk src n bs)).
  { forward. Exists 0. entailer!. }
  { forward. Exists n. entailer!.
    right. split; auto. destruct (SO_nn src dst ds); auto. discriminate. }
  Intros nn.
  assert (Hdst: SO_nn src dst ds = true -> dst <> nullval)
    by (unfold SO_nn; destruct (eq_dec src nullval), (eq_dec dst nullval); auto; discriminate).
  replace_SEP 3 (EX oc: list val, !!(Zlength oc = cap) && SO_dst dst cap oc).
  { entailer!. unfold SO_dst. destruct (eq_dec dst nullval).
    - Exists (Zrepeat Vundef cap). entailer!; rewrite Zlength_Zrepeat; lia.
    - Exists (Zrepeat Vundef cap). sep_apply (SO_blk_split cap dst ltac:(lia)). entailer!;
      rewrite Zlength_Zrepeat; lia. }
  Intros oc.
  forward. forward. forward. forward.
  forward_loop (EX calls: Z, EX ipos: Z, EX stalled: Z, EX opos: Z, EX oc: list val, EX st: dctx_st,
                SO_inv DC WG gv v_in v_out v n cap nn src dst ds bs srv 0 calls ipos stalled opos oc st)
    continue: (EX calls: Z, EX ipos: Z, EX stalled: Z, EX opos: Z, EX oc: list val, EX st: dctx_st,
                SO_inv DC WG gv v_in v_out v n cap nn src dst ds bs srv 1 calls ipos stalled opos oc st)
    break: (SO_brk DC WG gv v_in v_out n cap src dst ds bs).
  { Exists 0 0 0 0 oc st. unfold SO_inv, SO_core. entailer!.
    match goal with H: nn = 0 \/ _ |- _ => destruct H as [-> | [-> Hnn]]; [left; auto|] end. right.
    match goal with H: SO_nn src dst ds = true -> st = _ |- _ => specialize (H Hnn); subst st end.
    simpl. repeat split; auto; intros; lia. }
  2: { Intros calls ipos stalled opos oc' st'. unfold SO_inv. forward.
       Exists (calls + 1) ipos stalled opos oc' st'. unfold SO_inv, SO_core in *. entailer!.
       tauto. }
  2: { unfold SO_brk. Intros st' oc'.
       assert (Hds: exists ost, (match ost with None => ds = nullval | Some _ => True end) /\
                     SO_dc DC gv ds st' = match ost with None => emp | Some st => DC gv ds st end).
       { unfold SO_dc. destruct (eq_dec ds nullval). exists None; auto. exists (Some st'); auto. }
       destruct Hds as [ost [Host Hdc]]. rewrite Hdc.
       forward_call (gv, ds, ost).
       forward_call (tarray tuchar (Z.max 1 n), src, gv).
       { unfold SO_blk. destruct (eq_dec src nullval); [cancel|].
         sep_apply (data_at_data_at_ Ews (tarray tuchar (Z.max 1 n))). cancel. }
       forward_call (tarray tuchar (Z.max 1 cap), dst, gv).
       { unfold SO_dst. destruct (eq_dec dst nullval); [cancel|].
         sep_apply (SO_blk_join cap oc' dst ltac:(lia) ltac:(auto)). cancel. }
       forward. cancel. }
  Intros calls ipos stalled opos oc' st'. unfold SO_inv. Intros.
  match goal with H: SO_core _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => destruct H as (Hip & Hop & Hcore) end.
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
    forward_if (EX b: bool, PROPx (cons (b = true -> 0 < nn /\ calls < 4096) P)
                 (LOCALx (cons (temp _x_stable_out__t'16 (Vint (if b then Int.one else Int.zero))) L) (SEPx R)))
  end.
  { forward. Exists (calls <? 4096). entailer!. split.
    - match goal with H: Int64.unsigned _ < Int64.unsigned _ |- _ => rewrite !Int64.unsigned_repr in H by rep_lia end.
      intros Hb. apply Z.ltb_lt in Hb. lia.
    - unfold Int64.cmpu. rewrite SO_ltu_Z by rep_lia. destruct (calls <? 4096); reflexivity. }
  { forward. Exists false. entailer!. }
  Intros b. forward_if.
  2: { forward. unfold SO_brk. Exists st' oc'. entailer!. }
  destruct b; [|exfalso; match goal with H: _ <> Int.zero |- _ => apply H; reflexivity end].
  match goal with H: true = true -> _ |- _ => destruct (H eq_refl) as [Hnn0 Hcalls]; clear H end.
  destruct Hcore as [Hnn | (Hnn & Hall & Hdict & Hpar & Hset & Hbl0 & Hstab & Herr & Hobuf & Hopos & Hocp & Hval)]; [lia|]. subst nn.
  assert (Hsnn: src <> nullval /\ dst <> nullval /\ ds <> nullval)
    by (unfold SO_nn in Hall; destruct (eq_dec src nullval), (eq_dec dst nullval), (eq_dec ds nullval);
        try discriminate; auto).
  destruct Hsnn as (Hsrc & Hdst' & Hds).
  unfold SO_blk, SO_dst, SO_dc. rewrite !if_false by auto. Intros.
  forward_call (0, n - ipos).
  Intros il.
  forward.
  sep_apply (SO_src_slice n bs ipos il src ltac:(lia) ltac:(lia) ltac:(lia) ltac:(auto)).
  flatten_sepcon_in_SEP.
  forward_call (gv, Ews, offset_val ipos src, sublist ipos (ipos + il) bs).
  { entailer!. rewrite Zlength_sublist by lia. replace (ipos + il - ipos) with il by lia. reflexivity. }
  { split; [rewrite Zlength_sublist by lia; rep_lia|].
    unfold bytes_ok in *. apply Forall_sublist. auto. }
  Intros ib.
  sep_apply (modus_ponens_wand
    (data_at Ews (tarray tuchar (Zlength (sublist ipos (ipos + il) bs))) (zbytes (sublist ipos (ipos + il) bs)) (offset_val ipos src))).
  fold (zbytes bs ++ Zrepeat Vundef (Z.max 1 n - n)).
  forward_if.
  { SO_tc_null_test ib. }
  { forward. unfold SO_brk. Exists st' oc'. unfold SO_blk, SO_dst, SO_dc.
    rewrite (if_false (src = nullval)), (if_false (dst = nullval)), (if_false (ds = nullval)) by auto.
    rewrite if_true by auto. entailer!. }
  rewrite if_false by auto. Intros.
  forward. forward. forward.
  set (ibs := sublist ipos (ipos + il) bs) in *.
  assert (Hibl: Zlength ibs = il) by (subst ibs; rewrite Zlength_sublist; lia).
  assert (Hibb: bytes_ok ibs) by (subst ibs; unfold bytes_ok in *; apply Forall_sublist; auto).
  rewrite Hibl in *.
  sep_apply (SO_copy_split il (zbytes ibs) ib ltac:(lia) ltac:(rewrite Zlength_map; auto)).
  rewrite <- (SO_arr Ews cap oc' dst).
  rewrite <- SO_out, <- SO_in.
  sep_apply (SO_pws_join (SO_W cap dst) (SO_W il ib)).
  sep_apply (SO_dc_res DC DD gv ds st' Hdict Hset). do 2 try flatten_sepcon_in_SEP.
  assert (Hpd: isptr dst) by (destruct dst; simpl in *; try contradiction; auto; elim Hdst'; rewrite PNdst; reflexivity).
  assert (Hpi: isptr ib) by (destruct ib; simpl in *; try contradiction; auto; match goal with H: Vlong _ <> _ |- _ => elim H end; rewrite PNib; reflexivity).
  rewrite <- (mbuf_isptr Ews cap oc' dst Hpd), <- (mbuf_isptr Ews il (zbytes ibs) ib Hpi).
  forward_call (SO_W cap dst ++ SO_W il ib, gv, ds, st', v_out, v_in, Tsh, Tsh, Ews, dst, cap, opos, oc',
                Ews, ib, il, 0, ibs).
  { split; [apply SO_buf_ok_dst; lia|]. split; [apply SO_buf_ok_ib; lia|].
    split; [intros _; destruct Hobuf as [-> | ->]; auto|].
    unfold stream_dict_ok. rewrite Hdict, Hset, Hbl0. auto. }
  Intros vret. destruct vret as [[[[r opos'] ipos'] oc''] st''].
  simpl fst in *; simpl snd in *.
  rewrite (mbuf_isptr _ _ _ dst Hpd), (mbuf_isptr _ _ _ ib Hpi).
  rewrite Hdict, Hset, (proj1 (SO_res_emp DD gv)), (proj2 (SO_res_emp DD gv)).
  match goal with H: stream_post _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    destruct H as (dl & stall' & a' & Hop' & Hip' & Hoc & Hpre & Hdll0 & Hdlb & Ha' & Hah & Hadisj & Hr0 & Hst' &
                   Hs1 & Hs2 & Hbm & Hstall & Hcl & _) end.
  rewrite (SO_stream_claims_v3_dflt st') in Hcl by auto.
  destruct (Hdlb (or_introl Hstab)) as [Hdl Hbo]. clear Hdlb Hdll0.
  pose proof (stream_hostage_zero a' r Hr0 Ha') as Hr0'. clear Hr0. rename Hr0' into Hr0.
  assert (Hst3: dc_par st'' = dparams_dflt /\ dc_set st'' = nil /\ dc_bl st'' = None)
    by (rewrite Hst'; cbn; rewrite ?Hpar, ?Hset, ?Hbl0; repeat split).
  destruct Hst3 as (Hpar'' & Hset'' & Hbl'').
  assert (Hst'': dc_dict st'' = None /\ dc_stable st'' = true /\ ss_err (dc_ss st'') = is_error_code r /\
                 ss_obuf (dc_ss st'') = Some (dst, cap) /\ ss_out (dc_ss st'') = ss_out (dc_ss st') ++ dl /\
                 ss_stall (dc_ss st'') = stall' /\
                 ss_in (dc_ss st'') = ss_in (dc_ss st') ++ sublist (0 + ss_ahead (dc_ss st')) (ipos' + a') ibs /\
                 ss_ahead (dc_ss st'') = a')
    by (rewrite Hst'; cbn; rewrite ?Hstab, ?Hdict; repeat split).
  destruct Hst'' as (Hd'' & Hsb'' & Her'' & Hob'' & Hout'' & Hstl'' & Hin'' & Hah'').
  clear Hst'.
  assert (Hocp'': sublist 0 opos' oc'' = zbytes (ss_out (dc_ss st') ++ dl))
    by (apply (SO_out_prefix oc' oc'' opos opos'); auto; lia).
  sep_apply (andp_left1 (DC gv ds st'') (valid_pointer ds) (DC gv ds st'') (derives_refl _)).
  rewrite SO_out, SO_in, (SO_arr Ews cap oc'' dst).
  forward. forward.
  forward_call Int.one.
  { entailer!. rewrite SO_ltu64_false by rep_lia. reflexivity. }
  forward. forward.
  forward_call Int.one.
  { entailer!. rewrite SO_ltu64_false by rep_lia. reflexivity. }
  forward. forward.
  sep_apply (SO_pws_split (SO_W cap dst) (SO_W il ib)).
  rewrite (SO_arr Ews il (zbytes ibs) ib).
  sep_apply (SO_blk_join il (zbytes ibs) ib ltac:(lia) ltac:(rewrite Zlength_map; auto)).
  forward_call (tarray tuchar (Z.max 1 il), ib, gv).
  { rewrite if_false by auto. cancel. }
  assert (Hdll: Zlength dl = opos' - opos) by (apply (SO_dl_len opos opos' oc''); auto; lia).
  forward_if.
  { assert (Hv1: v = 1).
    { assert (v <> 0) by (intro; subst v; match goal with H: Int.repr 0 <> Int.zero |- _ => apply H; reflexivity end).
      lia. }
    match goal with H: SO_mode _ _ _ _ _ |- _ =>
      destruct H as [[? _] | [_ (ws & Hsf & Hwf & Hbs & Hsrv & Hcap)]]; [lia|] end.
    subst bs.
    destruct (Hval Hv1) as (Hstl & Hin & Hah0 & Hahn).
    assert (Hin': ss_in (dc_ss st') ++ sublist (0 + ss_ahead (dc_ss st')) (ipos' + a') ibs =
                  sublist 0 (ipos + (ipos' + a')) (ws_bytes ws))
      by (rewrite Hin; subst ibs; apply SO_in_app2; lia).
    rewrite Hin', Hstab in Hcl.
    destruct (so_content ws (ipos + (ipos' + a')) _ _ _ r Hsf ltac:(lia) Hcl) as [Hcn Hcs].
    assert (Hlen: Zlength (ss_out (dc_ss st') ++ dl) = opos') by (rewrite Zlength_app; lia).
    rewrite Hlen in Hcn, Hcs.
    forward.
    match goal with |- semax _ (PROPx ?P (LOCALx (cons _ ?L) (SEPx ?R))) _ _ =>
      forward_loop (EX i: Z, PROPx (cons (opos <= i <= opos') P) (LOCALx (cons (temp _i (Vlong (Int64.repr i))) L) (SEPx R)))
      continue: (EX i: Z, PROPx (cons (opos <= i < opos') P) (LOCALx (cons (temp _i (Vlong (Int64.repr i))) L) (SEPx R)))
      break: (PROPx P (LOCALx L (SEPx R)))
    end.
    { Exists opos. entailer!. }
    { Intros i. forward. forward_if.
      - pose proof Hsf as (Hbb & Hcc & Hbl & Hcl' & _).
        assert (Hi: 0 <= i < Zlength (ws_content ws)) by lia.
        assert (Hbyte: Znth i oc'' = Vint (Int.repr (Znth i (ws_content ws))))
          by (apply (SO_dst_byte oc'' (ss_out (dc_ss st')) dl (ws_content ws) opos opos'); auto; lia).
        unfold_data_at (data_at _ _ srv _). rewrite Hsrv. cbn [fst snd wseries_val].
        forward.
        forward_call Int.one.
        { entailer!. rewrite SO_ltu_Z by rep_lia.
          replace (i <? Zlength (ws_content ws)) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
        forward.
        { entailer!. match goal with |- context [@Znth val ?d i oc''] =>
            assert (Hb2: @Znth val d i oc'' = Vint (Int.repr (Znth i (ws_content ws))))
              by (rewrite <- Hbyte; unfold Znth; destruct (Z_lt_dec i 0); [lia|]; apply nth_indep;
                  rewrite <- ZtoNat_Zlength; lia) end.
          rewrite Hb2. apply SO_tc_byte; auto; lia. }
        assert_PROP (field_compatible t_wseries (DOT _content) (gv _x_stable_out__sr)) as Hfcc by entailer!.
        rewrite (field_at_data_at Ews t_wseries (DOT _content)).
        change (nested_field_type t_wseries (DOT _content)) with (tarray tuchar 262144).
        assert_PROP (force_val (sem_add_ptr_long tuchar (offset_val 524296 (gv _x_stable_out__sr)) (Vlong (Int64.repr i))) =
                     field_address (tarray tuchar 262144) (SUB i) (field_address t_wseries (DOT _content) (gv _x_stable_out__sr)))
          as Haddr.
        { entailer!. rewrite arr_field_address by (auto; lia). unfold field_address at 1. rewrite if_true by auto.
          simpl. rewrite offset_offset_val. f_equal; lia. }
        remember 262144 as K eqn:HK.
        forward.
        { entailer!. match goal with |- context [@Znth val ?d i (zbytes (ws_content ws) ++ ?u)] =>
            assert (Hb3: @Znth val d i (zbytes (ws_content ws) ++ u) = Vint (Int.repr (Znth i (ws_content ws))))
              by (rewrite <- (SO_cont_byte (ws_content ws) i) by lia; unfold Znth; destruct (Z_lt_dec i 0); [lia|];
                  apply nth_indep; rewrite <- ZtoNat_Zlength, Zlength_app, Zlength_map, Zlength_Zrepeat by lia; lia) end.
          rewrite Hb3. apply SO_tc_byte; auto; lia. }
        forward_call Int.one.
        { entailer!. match goal with |- context [@Znth val ?d i oc''] =>
            assert (Hb2: @Znth val d i oc'' = Vint (Int.repr (Znth i (ws_content ws))))
              by (rewrite <- Hbyte; unfold Znth; destruct (Z_lt_dec i 0); [lia|]; apply nth_indep;
                  rewrite <- ZtoNat_Zlength; lia) end.
          rewrite Hb2. match goal with |- context [@Znth val ?d i (zbytes (ws_content ws) ++ ?u)] =>
            assert (Hb3: @Znth val d i (zbytes (ws_content ws) ++ u) = Vint (Int.repr (Znth i (ws_content ws))))
              by (rewrite <- (SO_cont_byte (ws_content ws) i) by lia; unfold Znth; destruct (Z_lt_dec i 0); [lia|];
                  apply nth_indep; rewrite <- ZtoNat_Zlength, Zlength_app, Zlength_map, Zlength_Zrepeat by lia; lia) end.
          rewrite Hb3. simpl. rewrite Int.eq_true. reflexivity. }
        subst K.
        Exists i. rewrite (field_at_data_at Ews t_wseries (DOT _content)).
        change (nested_field_type t_wseries (DOT _content)) with (tarray tuchar 262144).
        entailer!.
      - forward. entailer!. }
    { Intros i. forward. Exists (i + 1). entailer!. }
    pose proof Hsf as (Hbb & Hcc & Hbl & Hcl' & Hnf & _).
    forward_call r.
    match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
      forward_if (PROPx (cons (is_error_code r = false) P) (LOCALx L (SEPx R)))
    end.
    { (* an error: the harness's check, then the end of the run *)
      assert (Herr': is_error_code r = true) by (destruct (is_error_code r); auto; SO_absurd).
      rewrite Hsrv.
      forward_call (Ews, gv _x_stable_out__sr, ws).
      match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
        forward_if (EX t21: int, PROPx (cons (t21 = Int.zero -> within_stream_b (ws_frames ws) = true /\ error_of r <> 64) P)
                      (LOCALx (cons (temp _x_stable_out__t'21 (Vint t21)) L) (SEPx R)))
      end.
      - forward. Exists Int.one. entailer!.
      - forward_call r. forward.
        Exists (Int.repr (if Int.eq (Int.repr (error_of r)) (Int.repr 64) then 1 else 0)). entailer!.
        all: first
          [ match goal with Hz: Int.repr (if Int.eq _ _ then 1 else 0) = Int.zero |- _ =>
              split; [destruct (within_stream_b (ws_frames ws)); auto; SO_absurd
                     | intros E; rewrite E in Hz; rewrite Int.eq_true in Hz; inv Hz] end
          | destruct (Int.eq _ _); reflexivity ].
      - Intros t21.
        match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
          forward_if (EX t23: int, PROPx (cons (t23 <> Int.zero) P)
                        (LOCALx (cons (temp _x_stable_out__t'23 (Vint t23)) L) (SEPx R)))
        end.
        + forward. Exists Int.one. entailer!.
        + match goal with H: t21 = Int.zero -> _ |- _ => destruct (H ltac:(auto)) as [Hws He64] end.
          assert (Heo: error_of r = ZSTD_error_memory_allocation \/
                       stall_error_b (error_of r) stalled ipos' il opos' cap opos = true)
            by (apply (SO_err_ok (sin0 := sublist 0 (Zlength (ss_in (dc_ss st')) - ss_ahead (dc_ss st')) (ss_in (dc_ss st'))) (sout0 := ss_out (dc_ss st')) (a1 := a') ws (ipos + (ipos' + a'))
                         (sublist 0 (ipos + (ipos' + a')) (ws_bytes ws) ++ sublist (ipos' + a') il ibs)
                         (ss_out (dc_ss st') ++ dl) r (ss_stall (dc_ss st'))); auto;
                try lia; subst ibs; apply SO_sall_prefix; lia).
          destruct Heo as [Heo | Heo]; [unfold ZSTD_error_memory_allocation in Heo; contradiction|].
          assert (Herange: 0 < error_of r < 120)
            by (unfold error_of; rewrite Herr'; unfold is_error_code in Herr'; apply Z.ltb_lt in Herr'; rep_lia).
          forward_call r.
          forward_call (error_of r, stalled, Tsh, v_in, ib, il, ipos', Tsh, v_out, dst, cap, opos', opos).
          forward.
          Exists Int.one. entailer!.
          rewrite Heo. reflexivity.
        + Intros t23. forward_call t23.
          forward. unfold SO_brk.
          Exists st'' oc''.
          unfold SO_blk, SO_dst, SO_dc.
          rewrite (if_false (src = nullval)), (if_false (dst = nullval)), (if_false (ds = nullval)) by auto.
          entailer!. }
    { forward. entailer!. destruct (is_error_code r); auto. SO_absurd. }
    Intros.
    forward.
    match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
      forward_if (EX b: bool, PROPx (cons (b = andb (ipos' =? 0) (opos' =? opos)) P)
                   (LOCALx (cons (temp _x_stable_out__t'27 (Vint (if b then Int.one else Int.zero))) L) (SEPx R)))
    end.
    { forward. forward. Exists (opos' =? opos). entailer!.
      match goal with Hz: Int64.repr ipos' = Int64.zero |- _ =>
        apply (f_equal Int64.unsigned) in Hz; rewrite Int64.unsigned_repr in Hz by rep_lia;
        change (Int64.unsigned Int64.zero) with 0 in Hz end.
      subst ipos'. split; [reflexivity|].
      destruct (zeq _ _) as [e|e]; [rewrite e, Z.eqb_refl | rewrite (proj2 (Z.eqb_neq _ _) e)]; reflexivity. }
    { forward. Exists false. entailer!.
      replace (ipos' =? 0) with false; [reflexivity|]. symmetry. apply Z.eqb_neq. intro E. subst ipos'.
      match goal with Hz: Int64.repr 0 <> _ |- _ => apply Hz; reflexivity end. }
    Intros b27.
    match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (cons (temp _x_stable_out__t'28 (Vlong (Int64.repr (if b27 then stalled + 1 else 0)))) L) (SEPx R)))
    end.
    { forward. destruct b27; [|SO_absurd]. entailer!. }
    { forward. destruct b27; [SO_absurd|]. entailer!. }
    forward.
    match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
      forward_if (EX b: bool, PROPx (cons (b = andb (r =? 0) (ipos + ipos' =? n)) P)
                   (LOCALx (cons (temp _x_stable_out__t'29 (Vint (if b then Int.one else Int.zero))) L) (SEPx R)))
    end.
    { forward. Exists (ipos + ipos' =? n). entailer!.
      match goal with Hz: Int64.repr r = Int64.zero |- _ =>
        apply (f_equal Int64.unsigned) in Hz; rewrite Int64.unsigned_repr in Hz by rep_lia;
        change (Int64.unsigned Int64.zero) with 0 in Hz end.
      subst r. split; [reflexivity|]. unfold Int64.cmpu, Int64.eq. rewrite !Int64.unsigned_repr by rep_lia.
      destruct (zeq _ _) as [e|e]; [rewrite e, Z.eqb_refl | rewrite (proj2 (Z.eqb_neq _ _) e)]; reflexivity. }
    { forward. Exists false. entailer!.
      replace (r =? 0) with false; [reflexivity|]. symmetry. apply Z.eqb_neq. intro E. subst r.
      match goal with Hz: Int64.repr 0 <> _ |- _ => apply Hz; reflexivity end. }
    Intros b29.
    match goal with H: b27 = _ |- _ => rename H into Hb27 end.
    match goal with H: b29 = _ |- _ => rename H into Hb29 end.
    match goal with H: is_error_code r = false |- _ => rename H into Hnerr end.
    forward_if.
    { destruct b29; [|SO_absurd].
      symmetry in Hb29. apply andb_true_iff in Hb29 as [E1 E2]. apply Z.eqb_eq in E1, E2. subst r.
      specialize (Hr0 eq_refl). rewrite Hr0 in Hcl.
      rewrite Z.add_0_r, E2 in Hcl. rewrite (sublist_same 0 _ (ws_bytes ws)) in Hcl by lia.
      pose proof (so_zero ws _ _ _ Hsf Hcl) as Hz.
      assert (Hoc': opos' = Zlength (ws_content ws)) by (rewrite <- Hlen, Hz; reflexivity).
      forward.
      unfold_data_at (data_at _ _ srv _). rewrite Hsrv. cbn [fst snd wseries_val].
      forward.
      forward_call Int.one.
      { entailer!. unfold Int64.cmpu, Int64.eq. rewrite !Int64.unsigned_repr by rep_lia.
        destruct (zeq _ _) as [|ne]; [reflexivity | exfalso; apply ne; rewrite Hz; reflexivity]. }
      forward. unfold SO_brk.
      Exists st'' oc''.
      unfold SO_blk, SO_dst, SO_dc.
      rewrite (if_false (src = nullval)), (if_false (dst = nullval)), (if_false (ds = nullval)) by auto.
      entailer!. }
    { destruct b29; [SO_absurd|].
      assert (Hst2: stall' <= (if b27 then stalled + 1 else 0) /\ 0 <= (if b27 then stalled + 1 else 0) <= calls + 1).
      { destruct b27.
        - symmetry in Hb27. apply andb_true_iff in Hb27 as [E1 E2]. apply Z.eqb_eq in E1, E2.
          specialize (Hs2 Hnerr E1 E2). lia.
        - symmetry in Hb27. apply andb_false_iff in Hb27.
          assert (Hp: ipos' <> 0 \/ opos' <> opos)
            by (destruct Hb27 as [E|E]; apply Z.eqb_neq in E; auto).
          specialize (Hs1 Hnerr Hp). lia. }
      forward.
      Exists calls (ipos + ipos') (if b27 then stalled + 1 else 0) opos' oc''
             st''.
      unfold SO_inv, SO_core, SO_blk, SO_dst, SO_dc.
      rewrite (if_false (src = nullval)), (if_false (dst = nullval)), (if_false (ds = nullval)) by auto.
      entailer!.
      split.
      - right. split; [reflexivity|]. exists ws. split; [auto|]. split; [auto|]. split; [reflexivity|].
        split; [reflexivity|]. lia.
      - right. rewrite Hd'', Hsb'', Her'', Hob'', Hout'', Hin''.
        split; [reflexivity|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|].
        split; [auto|]. split; [auto|]. split; [right; reflexivity|]. split; [first [reflexivity | rewrite Zlength_app; lia]|].
        split; [exact Hocp''|]. intros _. split; [lia|]. split; [rewrite Hin'; f_equal; lia|]. lia. } }
  { assert (Hv0: v = 0).
    { match goal with H: Int.repr v = Int.zero |- _ =>
        apply (f_equal Int.unsigned) in H; rewrite Int.unsigned_repr in H by rep_lia; exact H end. }
    forward_call r.
    forward_if.
    - forward_call (gv, ds, st'', ZSTD_reset_session_only).
      Intros vret. destruct vret as [r0 st0]. cbn [fst snd] in *.
      match goal with H: reset_post _ _ _ _ |- _ => destruct (reset_post_session _ _ _ H) as [-> ->]; clear H end.
      forward.
      Exists calls (ipos + ipos') stalled 0 oc''
             (set_ex (set_ss st'' ss_init) false).
      unfold SO_inv, SO_core, SO_blk, SO_dst, SO_dc.
      rewrite (if_false (src = nullval)), (if_false (dst = nullval)), (if_false (ds = nullval)) by auto.
      entailer!.
      right. cbn [set_ex set_ss dc_dict dc_stable dc_ss dc_par dc_set dc_bl ss_init ss_err ss_obuf ss_out]. rewrite Hd'', Hsb''.
      split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|].
      split; [auto|].
      split; [left; auto|]. split; [reflexivity|]. split; [reflexivity|]. intros; lia.
    - match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
        forward_if (EX b: int, PROPx P (LOCALx (cons (temp _x_stable_out__t'30 (Vint b)) L) (SEPx R)))
      end.
      + forward_if.
        * forward. Exists Int.one. entailer!.
        * forward. forward. Exists (Int.repr (if Int64.eq (Int64.repr il) (Int64.repr 0) then 1 else 0)). entailer!.
      + forward. Exists Int.zero. entailer!.
      + Intros b. forward_if.
        * forward. unfold SO_brk.
          Exists st'' oc''.
          unfold SO_blk, SO_dst, SO_dc.
          rewrite (if_false (src = nullval)), (if_false (dst = nullval)), (if_false (ds = nullval)) by auto.
          entailer!.
        * forward.
          Exists calls (ipos + ipos') stalled opos' oc''
             st''.
          unfold SO_inv, SO_core, SO_blk, SO_dst, SO_dc.
          rewrite (if_false (src = nullval)), (if_false (dst = nullval)), (if_false (ds = nullval)) by auto.
          entailer!.
          { right. rewrite Hd'', Hsb'', Her'', Hob'', Hout''. split; [auto|]. split; [auto|]. split; [auto|].
            split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [destruct (is_error_code r); auto; SO_absurd|].
            split; [right; auto|]. split; [first [reflexivity | rewrite Zlength_app; lia]|].
            split; [exact Hocp''|]. intros; lia. }
          all: try (sep_apply (data_at_data_at_ Tsh tin); cancel). }
Qed.
