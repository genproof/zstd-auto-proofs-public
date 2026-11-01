(* main of harness/valid_dict.c against the decoder's API v3 (adapted from WMain_valid_dict.v, API v2) and the writer's top-level specifications, in the small
   context G0 (WTopSpecs_valid_dict). *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.harness.valid_dict.WTopSpecs_valid_dict.
Require Import Zstd.proof.harness.writer.SeriesLemmas.
Require Import Zstd.proof.zstd.ApiBridge.
Require Zstd.proof.top.MainPre6.
Require Import Zstd.proof.zstd.NullBuf.
Require Import Zstd.proof.harness.ApiAfterKit.

Local Notation ZCS := Zstd.proof.zstd.Base.CompSpecs.
Local Notation HCS := Zstd.proof.harness.valid_dict.HOK_valid_dict.CompSpecs.

(* ---------- VDModel.v at API v3 (oneshot_ok at zstd's default parameters) ---------- *)

Lemma vd_ok_prefix_all wl fs : all_ok wl fs = true -> ok_prefix wl fs = fs.
Proof.
  induction fs as [|f fs IH]; simpl; auto.
  intros H. apply andb_prop in H as [H1 H2].
  destruct (wi_rejected wl f); simpl in H1; [discriminate|]. rewrite IH; auto.
Qed.

Lemma vd_decode dm ws : series_facts dm ws -> wseries_wf ws ->
  decode_series dm no_wlim (ws_bytes ws) =
    if within_oneshot_b (ws_frames ws) then SOk (ws_content ws) else SDet.
Proof.
  intros Hf Hw. unfold decode_series. rewrite (series_frames_written dm ws no_wlim Hf).
  rewrite (within_oneshot_all_ok ws Hw).
  destruct (all_ok no_wlim (ws_frames ws)) eqn:E; [|reflexivity].
  rewrite vd_ok_prefix_all by auto. rewrite (written_content dm ws Hf). reflexivity.
Qed.

Lemma vd_check dm ws cap r out :
  series_facts dm ws -> wseries_wf ws ->
  oneshot_ok md_dflt (Some dm) (ws_bytes ws) cap r out ->
  (is_error_code r = false -> r = Zlength (ws_content ws) /\ sublist 0 r out = zbytes (ws_content ws)) /\
  (is_error_code r = true -> Zlength (ws_content ws) <= cap -> within_oneshot_b (ws_frames ws) = true ->
   r = err_code ZSTD_error_memory_allocation).
Proof.
  intros Hf Hw Ho. apply oneshot_ok_dflt in Ho. destruct Ho as [_ H]. rewrite (vd_decode dm ws Hf Hw) in H.
  destruct (within_oneshot_b (ws_frames ws)) eqn:E.
  - destruct H as [H1 H2]. split; auto.
    intros He Hc _. destruct (H2 He) as [Hlt|Hm]; [lia | exact Hm].
  - split; intros He; [rewrite H in He; discriminate | intros _ Hx; discriminate].
Qed.

(* the context's state stays at zstd's defaults: default parameters, no DDict set, no buffer-less frame *)
Definition VM_df (st: dctx_st) : Prop := dc_par st = dparams_dflt /\ dc_set st = nil /\ dc_bl st = None.

Lemma VM_df_init : VM_df dctx_init.
Proof. unfold VM_df; auto. Qed.

Lemma VM_df_dict st d : VM_df st -> VM_df (set_dict st d).
Proof. unfold VM_df; cbn; auto. Qed.

Lemma VM_df_after st st' l : VM_df st -> after_decode st st' l -> VM_df st'.
Proof. unfold VM_df, after_decode. intros Hd [-> | ->]; cbn; auto. Qed.

Lemma VM_df_use st : VM_df st -> VM_df (after_use st).
Proof. unfold after_use. intros Hd. destruct (dc_dict st) as [d|]; [destruct (dr_once d)|]; auto using VM_df_dict. Qed.

Lemma VM_df_load st st' r dr : VM_df st -> load_result st st' r dr -> VM_df st'.
Proof. intros Hd [[_ ->] | [_ [-> _]]]; apply VM_df_dict; auto. Qed.

Lemma VM_df_md st : VM_df st -> dmode_of (dc_par st) = md_dflt.
Proof. intros (-> & _ & _). reflexivity. Qed.

(* ---------- the helpers of VDModel2.v, VDBuf.v, VDInv.v, adapted to API v2 ---------- *)

(* valid_dict: the API states and results the main proof goes through (plain Coq over Spec_api6). *)

Lemma VM_err64 : is_error_code (err_code ZSTD_error_memory_allocation) = true /\
  error_of (err_code ZSTD_error_memory_allocation) = ZSTD_error_memory_allocation /\
  0 <= err_code ZSTD_error_memory_allocation <= Int64.max_unsigned.
Proof. vm_compute. repeat split; congruence. Qed.

Definition VM_dr2 (dict: val) (b: list Z) : dictref :=
  {| dr_src := DSRef dict; dr_raw := false; dr_once := false; dr_bytes := b |}.

Definition VM_drp (dict: val) (b: list Z) : dictref :=
  {| dr_src := DSRef dict; dr_raw := true; dr_once := true; dr_bytes := b |}.

Definition VM_dr3 (q dict: val) (b: list Z) (e: ddict_st) : dictref :=
  {| dr_src := DSDDict q {| dd_bytes := b; dd_ref := Some dict; dd_buf := dd_buf e; dd_ld := dd_ld e |};
     dr_raw := false; dr_once := false; dr_bytes := b |}.

Lemma VM_load_ok st st' r dr : load_result st st' r dr -> is_error_code r = false ->
  st' = set_dict st (Some dr) /\ r = 0.
Proof. intros [[-> ->] | [E _]] F; [auto | congruence]. Qed.

(* a load of a dictionary zstd accepts fails only for memory *)
Lemma VM_load_err st st' r dr : load_result st st' r dr -> is_error_code r = true ->
  (dr_raw dr = true \/ dict_auto (dr_bytes dr) <> None) ->
  st' = set_dict st None /\ r = err_code ZSTD_error_memory_allocation.
Proof.
  intros [[-> ->] | [_ [-> H]]] F Hd.
  - discriminate.
  - split; auto. destruct H as [[Hr Ha] | Hm]; auto.
    destruct Hd as [Hd | Hd]; [congruence | contradiction].
Qed.

Lemma VM_after_ss st st2 l : after_decode (after_use st) st2 l -> dc_ss st2 = dc_ss st.
Proof.
  unfold after_decode, after_use. intros [-> | ->];
  destruct (dc_dict st) as [d|]; try destruct (dr_once d); reflexivity.
Qed.

Lemma VM_after_ss0 st st2 l : after_decode st st2 l -> dc_ss st2 = dc_ss st.
Proof. unfold after_decode. intros [-> | ->]; reflexivity. Qed.

(* api 2 after a decoding with the loaded dictionary: still there, and the last one *)
Lemma VM_after_dr2 dr st st2 : dr_once dr = false -> dc_dict st = Some dr -> last_ok st dr ->
  match dr_src dr with DSDDict _ dd => dd_ref dd <> None | _ => True end ->
  after_decode (after_use st) st2 (Some dr) ->
  dc_ss st2 = dc_ss st /\ dc_dict st2 = Some dr /\ last_ok st2 dr.
Proof.
  intros Ho Hd Hl Hs. unfold after_decode, after_use. rewrite Hd, Ho.
  intros [-> | ->]; unfold last_ok in *; cbn; auto.
Qed.

(* the dictionary model each API decodes with *)
Lemma VM_model_auto wd : dict_facts wd -> dict_auto (wd_bytes wd) = Some (wd_model wd).
Proof.
  intros (_ & _ & Ha & _). unfold wd_model. destruct (dict_auto (wd_bytes wd)); [reflexivity | contradiction].
Qed.

Lemma VM_model_raw wd : dict_facts wd -> wd_formatted wd = false -> Some (dict_raw (wd_bytes wd)) = Some (wd_model wd).
Proof. intros (_ & _ & _ & _ & _ & _ & H) Hf. destruct (H Hf) as [-> _]. reflexivity. Qed.

(* the harness's checks of one round: a decoding (oneshot_ok) or a failed load (memory) *)
Definition VM_round (dm: dict_model) (s: list Z) (cap r: Z) (out: list val) : Prop :=
  oneshot_ok md_dflt (Some dm) s cap r out \/ r = err_code ZSTD_error_memory_allocation.

Lemma VM_round_ok dm ws cap r out : series_facts dm ws -> wseries_wf ws ->
  VM_round dm (ws_bytes ws) cap r out -> is_error_code r = false ->
  r = Zlength (ws_content ws) /\ sublist 0 r out = zbytes (ws_content ws).
Proof.
  intros Hf Hw [Ho | ->] Er.
  - apply (proj1 (vd_check dm ws cap r out Hf Hw Ho)), Er.
  - pose proof VM_err64 as (E & _). congruence.
Qed.

Lemma VM_round_err dm ws cap r out : series_facts dm ws -> wseries_wf ws ->
  VM_round dm (ws_bytes ws) cap r out -> is_error_code r = true ->
  Zlength (ws_content ws) <= cap -> within_oneshot_b (ws_frames ws) = true ->
  error_of r = ZSTD_error_memory_allocation.
Proof.
  intros Hf Hw [Ho | ->] Er Hc Hwi.
  - rewrite (proj2 (vd_check dm ws cap r out Hf Hw Ho) Er Hc Hwi). apply VM_err64.
  - apply VM_err64.
Qed.

(* the number of rounds when every allocation succeeded *)
Definition VM_rnd (api: Z) : Z := if api =? 2 then 2 else 1.

Lemma VM_rnd_range api : 1 <= VM_rnd api <= 2.
Proof. unfold VM_rnd. destruct (api =? 2); lia. Qed.

(* valid_dict: the buffer witnesses lent to the decoder (Spec_api6), after
   src/proof/harness/any_dict (same layout: src of max(1,n) bytes, buf = [dst | 1 byte | dict]). *)

(* byte arrays mean the same under any two compspecs (as in HCsConv) *)
Definition VB_cce (cs1 cs2: compspecs) : change_composite_env cs1 cs2 :=
  {| coeq := cs_preserve_env cs1 cs2;
     coeq_consistent := cs_preserve_env_consistent cs1 cs2 _ eq_refl;
     coeq_complete := cs_preserve_completeness cs1 cs2 _ eq_refl |}.

Lemma VB_cs (cs1 cs2: compspecs) sh n (v: list val) p :
  @data_at cs1 sh (tarray tuchar n) v p = @data_at cs2 sh (tarray tuchar n) v p.
Proof.
  pose proof (@data_at_change_composite cs1 cs2 (VB_cce cs1 cs2) sh (tarray tuchar n) v v
    (JMeq_refl _) ltac:(reflexivity)) as E. rewrite E; reflexivity.
Qed.

Lemma VB_cs_ (cs1 cs2: compspecs) sh n p :
  @data_at_ cs1 sh (tarray tuchar n) p = @data_at_ cs2 sh (tarray tuchar n) p.
Proof.
  pose proof (@data_at__change_composite cs1 cs2 (VB_cce cs1 cs2) sh (tarray tuchar n)
    ltac:(reflexivity)) as E. rewrite E; reflexivity.
Qed.

Lemma VB_split_bytes_ {cs: compspecs} sh m k p : 0 <= k <= m -> field_compatible (tarray tuchar m) [] p ->
  data_at_ sh (tarray tuchar m) p =
  (data_at_ sh (tarray tuchar k) p * data_at_ sh (tarray tuchar (m - k)) (offset_val k p))%logic.
Proof.
  intros Hk Hf. unfold tarray. rewrite (split2_data_at__Tarray_tuchar sh m k p Hk) by auto with field_compatible.
  rewrite field_address0_offset by auto with field_compatible. simpl. rewrite Z.mul_1_l, Z.add_0_l. reflexivity.
Qed.

(* the slack of src's block and the gap byte between dst and dict *)
Definition VB_slack (src: val) (n: Z) : ptr_witness :=
  pw_bytes Ews (Z.max 1 n - n) (Zrepeat Vundef (Z.max 1 n - n)) (offset_val n src).
Definition VB_gap (buf: val) (cap: Z) : ptr_witness := pw_bytes Ews 1 [Vundef] (offset_val cap buf).
Definition VB_W (src: val) (n: Z) (buf: val) (cap: Z) : list ptr_witness := [VB_slack src n; VB_gap buf cap].

Lemma VB_pws src n buf cap : pws_pred (VB_W src n buf cap) =
  (@data_at_ ZCS Ews (tarray tuchar (Z.max 1 n - n)) (offset_val n src) *
   @data_at_ ZCS Ews (tarray tuchar 1) (offset_val cap buf))%logic.
Proof. unfold pws_pred, VB_W, map, fold_right. rewrite sepcon_emp. reflexivity. Qed.

Lemma VB_wvp_at {cs: compspecs} sh k p i q : readable_share sh -> 0 <= i <= k -> 0 < k -> q = offset_val i p ->
  data_at_ sh (tarray tuchar k) p |-- weak_valid_pointer q.
Proof.
  intros Hsh Hi Hk ->. eapply derives_trans; [apply data_at__memory_block_cancel|].
  simpl sizeof. rewrite Z.mul_1_l, Z.max_r by lia.
  apply memory_block_weak_valid_pointer; try lia. apply readable_nonidentity; auto.
Qed.

Lemma VB_ptr_eq b o i j : i = j -> offset_val i (Vptr b o) = offset_val j (Vptr b o).
Proof. intros ->; reflexivity. Qed.

Lemma VB_off_off b o i j : offset_val j (offset_val i (Vptr b o)) = offset_val (i + j) (Vptr b o).
Proof. rewrite offset_offset_val. reflexivity. Qed.

Lemma VB_off0 b o : Vptr b o = offset_val 0 (Vptr b o).
Proof. simpl. rewrite Ptrofs.add_zero. reflexivity. Qed.

Ltac VB_ptr_eq_tac :=
  first [ reflexivity
        | rewrite ?VB_off_off; apply VB_ptr_eq; lia
        | match goal with |- Vptr ?b ?o = _ => rewrite (VB_off0 b o) at 1 end; rewrite ?VB_off_off; apply VB_ptr_eq; lia ].

Ltac VB_piece k i :=
  eapply (VB_wvp_at _ k _ i); [auto | lia | lia | VB_ptr_eq_tac].

Lemma VB_buf_ok_src src n buf cap : isptr src -> 0 <= n -> buf_ok (VB_W src n buf cap) Ews n src.
Proof.
  intros Hp Hn. destruct src; try contradiction. unfold buf_ok. rewrite VB_pws.
  destruct (zlt 0 n).
  - apply andp_right; apply sepcon_weak_valid_pointer2.
    + VB_piece n 0.
    + VB_piece n n.
  - apply andp_right; apply sepcon_weak_valid_pointer1, sepcon_weak_valid_pointer1.
    + VB_piece (Z.max 1 n - n) 0.
    + VB_piece (Z.max 1 n - n) 0.
Qed.

Lemma VB_buf_ok_dst src n buf cap : isptr buf -> 0 <= cap -> buf_ok (VB_W src n buf cap) Ews cap buf.
Proof.
  intros Hp Hc. destruct buf; try contradiction. unfold buf_ok. rewrite VB_pws.
  destruct (zlt 0 cap).
  - apply andp_right; apply sepcon_weak_valid_pointer2.
    + VB_piece cap 0.
    + VB_piece cap cap.
  - apply andp_right; apply sepcon_weak_valid_pointer1, sepcon_weak_valid_pointer2.
    + VB_piece 1 0.
    + VB_piece 1 0.
Qed.

Lemma VB_buf_ok_dict src n buf cap dn : isptr buf -> 0 <= cap -> 0 <= dn ->
  buf_ok (VB_W src n buf cap) Ews dn (offset_val (cap + 1) buf).
Proof.
  intros Hp Hc Hd. destruct buf; try contradiction. unfold buf_ok. rewrite VB_pws.
  apply andp_right.
  - apply sepcon_weak_valid_pointer1, sepcon_weak_valid_pointer2. VB_piece 1 1.
  - destruct (zlt 0 dn).
    + apply sepcon_weak_valid_pointer2. VB_piece dn dn.
    + apply sepcon_weak_valid_pointer1, sepcon_weak_valid_pointer2. VB_piece 1 1.
Qed.

Lemma VB_sameblock_off buf k : isptr buf -> sameblock buf (offset_val k buf) = true.
Proof. intros Hp. destruct buf; try contradiction. simpl. unfold sameblock. apply peq_true. Qed.

Lemma VB_dict_ptr_ok src n buf cap dn : isptr buf -> 0 <= cap -> 0 <= dn ->
  field_compatible (tarray tuchar (cap + 1 + dn)) [] buf ->
  dict_ptr_ok (VB_W src n buf cap) Ews dn (offset_val (cap + 1) buf) Ews cap buf.
Proof.
  intros Hp Hc Hd Hf. left. split; [apply VB_sameblock_off; auto | split; [| apply VB_buf_ok_dict; auto]].
  destruct buf as [| | | | | b o]; try contradiction.
  destruct Hf as (_ & _ & Hsz & _). simpl in Hsz. rewrite Z.max_r in Hsz by lia.
  simpl. rewrite Ptrofs.add_unsigned. rewrite (Ptrofs.unsigned_repr (cap + 1)) by rep_lia.
  rewrite Ptrofs.unsigned_repr by rep_lia. lia.
Qed.

(* a buffer of n > 0 bytes needs no witness *)
Lemma VB_buf_ok_nil n p : 0 < n -> buf_ok [] Ews n p.
Proof.
  intros Hn. unfold buf_ok, pws_pred. simpl. rewrite emp_sepcon.
  destruct (isptr_dec p) as [Hp|Hp].
  - destruct p; try contradiction. apply andp_right.
    + VB_piece n 0.
    + VB_piece n n.
  - rewrite data_at__isptr. normalize.
Qed.

Lemma VB_split3_ {cs: compspecs} sh c d p : 0 <= c -> 0 <= d ->
  field_compatible (tarray tuchar (c + 1 + d)) [] p ->
  data_at_ sh (tarray tuchar (c + 1 + d)) p =
  (data_at_ sh (tarray tuchar c) p * data_at_ sh (tarray tuchar 1) (offset_val c p) *
   data_at_ sh (tarray tuchar d) (offset_val (c + 1) p))%logic.
Proof.
  intros Hc Hd Hf.
  rewrite (VB_split_bytes_ sh (c + 1 + d) (c + 1) p) by (auto; lia).
  replace (c + 1 + d - (c + 1)) with d by lia.
  rewrite (VB_split_bytes_ sh (c + 1) c p).
  - replace (c + 1 - c) with 1 by lia. reflexivity.
  - lia.
  - eapply field_compatible_array_smaller0; [exact Hf | lia].
Qed.

Lemma VB_Zrepeat {cs: compspecs} sh c p :
  data_at_ sh (tarray tuchar c) p = data_at sh (tarray tuchar c) (Zrepeat Vundef c) p.
Proof. unfold data_at_, field_at_, data_at. reflexivity. Qed.

Lemma VB_bytes_ok l : Forall (fun b => 0 <= b <= Byte.max_unsigned) l -> bytes_ok l.
Proof. unfold bytes_ok, is_byte. apply Forall_impl. intros x Hx. rep_lia. Qed.

(* src from exact_copy: n bytes, then the slack (Vundef) of its max(1, n) block *)
Lemma VB_src_split src bs : 
  field_compatible (tarray tuchar (Z.max 1 (Zlength bs))) [] src ->
  @data_at HCS Ews (tarray tuchar (Z.max 1 (Zlength bs))) (zbytes bs ++ Zrepeat Vundef (Z.max 1 (Zlength bs) - Zlength bs)) src
  = (@data_at ZCS Ews (tarray tuchar (Zlength bs)) (zbytes bs) src *
     @data_at_ ZCS Ews (tarray tuchar (Z.max 1 (Zlength bs) - Zlength bs)) (offset_val (Zlength bs) src))%logic.
Proof.
  intros Hf. pose proof (Zlength_nonneg bs).
  rewrite (VB_cs HCS ZCS).
  rewrite (split2_data_at_Tarray_app (Zlength bs) (Z.max 1 (Zlength bs)) Ews tuchar).
  - rewrite VB_Zrepeat. f_equal. f_equal.
    assert (Hf': @field_compatible ZCS (tarray tuchar (Z.max 1 (Zlength bs))) [] src).
    { apply (@field_compatible_change_composite HCS ZCS (VB_cce HCS ZCS)); [reflexivity | exact Hf]. }
    rewrite field_address0_offset by auto with field_compatible.
    simpl. f_equal. lia.
  - exact (Zlength_map _ _ _ _).
  - rewrite Zlength_Zrepeat; lia.
Qed.

Lemma VB_wit_fold src n buf cap :
  @data_at_ ZCS Ews (tarray tuchar (Z.max 1 n - n)) (offset_val n src) *
  @data_at_ ZCS Ews (tarray tuchar 1) (offset_val cap buf) |-- pws_pred (VB_W src n buf cap).
Proof. rewrite VB_pws. auto. Qed.

Lemma VB_wit_unfold src n buf cap :
  pws_pred (VB_W src n buf cap) |--
  @data_at_ ZCS Ews (tarray tuchar (Z.max 1 n - n)) (offset_val n src) *
  @data_at_ ZCS Ews (tarray tuchar 1) (offset_val cap buf).
Proof. rewrite VB_pws. auto. Qed.

(* everything back for free(src) and free(buf) *)
Lemma VB_final_merge src n buf cap dn out v vs :
  0 <= n -> 0 <= cap -> 0 <= dn ->
  field_compatible (tarray tuchar (Z.max 1 n)) [] src ->
  field_compatible (tarray tuchar (cap + 1 + dn)) [] buf ->
  pws_pred (VB_W src n buf cap) * @data_at ZCS Ews (tarray tuchar cap) out buf *
  @data_at ZCS Ews (tarray tuchar dn) v (offset_val (cap + 1) buf) *
  @data_at ZCS Ews (tarray tuchar n) vs src
  |-- @data_at_ HCS Ews (tarray tuchar (Z.max 1 n)) src * @data_at_ HCS Ews (tarray tuchar (cap + 1 + dn)) buf.
Proof.
  intros Hn Hc Hd Hfs Hfb.
  rewrite (VB_split_bytes_ Ews (Z.max 1 n) n src) by (auto; lia).
  rewrite (VB_split3_ Ews cap dn buf) by auto.
  rewrite VB_pws, !(VB_cs_ HCS ZCS).
  sep_apply (data_at_data_at_ Ews (tarray tuchar cap) out buf).
  sep_apply (data_at_data_at_ Ews (tarray tuchar dn) v (offset_val (cap + 1) buf)).
  sep_apply (data_at_data_at_ Ews (tarray tuchar n) vs src).
  cancel.
Qed.

Lemma VB_dict_val buf cap : isptr buf -> 0 <= cap <= Int64.max_unsigned - 1 ->
  force_val (sem_binary_operation' Oadd (tptr tuchar) tint
     (eval_binop Oadd (tptr tuchar) tulong buf (Vlong (Int64.repr cap))) (Vint (Int.repr 1)))
  = offset_val (cap + 1) buf.
Proof.
  intros Hp Hc. destruct buf; try contradiction. simpl.
  rewrite !(Ptrofs.mul_commut (Ptrofs.repr 1)), !Ptrofs.mul_one.
  rewrite Ptrofs.add_assoc.
  replace (Ptrofs.of_int64 (Int64.repr cap)) with (Ptrofs.repr cap)
    by (unfold Ptrofs.of_int64; rewrite Int64.unsigned_repr by rep_lia; reflexivity).
  rewrite ptrofs_add_repr. reflexivity.
Qed.

(* sr's bytes: the series' bytes for exact_copy, and the zeros after them *)
Lemma VB_bytes_split sh (bs: list Z) p : Zlength bs <= 2 ^ 19 ->
  field_at sh t_wseries (DOT _bytes) (zbytes bs ++ Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength bs)) p =
  (data_at sh (tarray tuchar (Zlength bs)) (zbytes bs) (field_address t_wseries (DOT _bytes) p) *
   data_at sh (tarray tuchar (2 ^ 19 - Zlength bs)) (Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength bs))
     (field_address0 (tarray tuchar (2 ^ 19)) (SUB (Zlength bs)) (field_address t_wseries (DOT _bytes) p)))%logic.
Proof.
  intros Hn. rewrite field_at_data_at.
  change (nested_field_type t_wseries (DOT _bytes)) with (tarray tuchar (2 ^ 19)).
  apply split2_data_at_Tarray_app.
  - rewrite Zlength_map. reflexivity.
  - rewrite Zlength_Zrepeat; [reflexivity|]. pose proof (Zlength_nonneg bs). lia.
Qed.

(* sr whole (within_oneshot) and by fields *)
Definition VB_sr_rest (ws: wseries) (p: val) : mpred :=
  (@data_at HCS Ews (tarray tuchar (Zlength (ws_bytes ws))) (zbytes (ws_bytes ws)) (@field_address HCS t_wseries (DOT _bytes) p) *
   @data_at HCS Ews (tarray tuchar (2 ^ 19 - Zlength (ws_bytes ws))) (Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength (ws_bytes ws)))
     (@field_address0 HCS (tarray tuchar (2 ^ 19)) (SUB (Zlength (ws_bytes ws))) (@field_address HCS t_wseries (DOT _bytes) p)) *
   @field_at HCS Ews t_wseries (DOT _f)
     (map winfo_val (ws_frames ws) ++ Zrepeat (winfo_val winfo0) (4 - Zlength (ws_frames ws))) p *
   @field_at HCS Ews t_wseries (DOT _nframes) (vu (Zlength (ws_frames ws))) p *
   spacer Ews 786932 786936 p)%logic.

Lemma VB_ws_fold ws p : Zlength (ws_bytes ws) <= 2 ^ 19 ->
  (VB_sr_rest ws p *
   @field_at HCS Ews t_wseries (DOT _n) (vl (Zlength (ws_bytes ws))) p *
   @field_at HCS Ews t_wseries (DOT _content)
     (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws))) p *
   @field_at HCS Ews t_wseries (DOT _content_n) (vl (Zlength (ws_content ws))) p) |--
  @data_at HCS Ews t_wseries (wseries_val ws) p.
Proof.
  intros Hn. unfold VB_sr_rest. rewrite <- VB_bytes_split by exact Hn.
  unfold_data_at (data_at _ _ _ p). cbn [fst snd wseries_val]. cancel.
Qed.

Lemma VB_ws_unfold ws p : Zlength (ws_bytes ws) <= 2 ^ 19 ->
  @data_at HCS Ews t_wseries (wseries_val ws) p |--
  (VB_sr_rest ws p *
   @field_at HCS Ews t_wseries (DOT _n) (vl (Zlength (ws_bytes ws))) p *
   @field_at HCS Ews t_wseries (DOT _content)
     (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws))) p *
   @field_at HCS Ews t_wseries (DOT _content_n) (vl (Zlength (ws_content ws))) p).
Proof.
  intros Hn. unfold VB_sr_rest. unfold_data_at (data_at _ _ _ p). cbn [fst snd wseries_val].
  rewrite (VB_bytes_split Ews (ws_bytes ws) p Hn). cancel.
Qed.

(* the bytes delivered and the content, at index i *)
Lemma VB_out_at (c: list Z) r out i : sublist 0 r out = zbytes c -> r = Zlength c -> 0 <= i < r ->
  Znth i out = Vint (Int.repr (Znth i c)).
Proof.
  intros Hs Hr Hi. replace (Znth i out) with (Znth (i + 0) out) by (rewrite Z.add_0_r; reflexivity).
  rewrite <- (Znth_sublist 0 i r out) by lia. rewrite Hs. rewrite Znth_map by lia. reflexivity.
Qed.

Lemma VB_content_at (c: list Z) k i : 0 <= i < Zlength c -> 
  Znth i (zbytes c ++ Zrepeat (Vint Int.zero) k) = Vint (Int.repr (Znth i c)).
Proof.
  intros Hi. rewrite app_Znth1 by (rewrite Zlength_map; lia). rewrite Znth_map by lia. reflexivity.
Qed.

(* the dictionary copy: dict[0..i) written *)
Lemma VB_copy_step (b: list Z) i n : 0 <= i < n -> Zlength b = n ->
  upd_Znth i (zbytes (sublist 0 i b) ++ Zrepeat Vundef (n - i)) (Vint (Int.repr (Znth i b))) =
  zbytes (sublist 0 (i + 1) b) ++ Zrepeat Vundef (n - (i + 1)).
Proof.
  intros Hi Hn.
  rewrite upd_Znth_app2 by (rewrite Zlength_map, Zlength_sublist, Zlength_Zrepeat; lia).
  rewrite Zlength_map, Zlength_sublist by lia. replace (i - (i - 0)) with 0 by lia.
  replace (n - i) with (1 + (n - (i + 1))) by lia.
  rewrite <- Zrepeat_app by lia. rewrite upd_Znth_app1 by (rewrite Zlength_Zrepeat; lia).
  change (Zrepeat Vundef 1) with [Vundef]. rewrite upd_Znth0.
  rewrite (sublist_split 0 i (i + 1) b) by lia. rewrite map_app, <- app_assoc.
  rewrite sublist_len_1 by lia. reflexivity.
Qed.

Lemma VB_rest_fold ws p :
  (@data_at HCS Ews (tarray tuchar (Zlength (ws_bytes ws))) (zbytes (ws_bytes ws)) (@field_address HCS t_wseries (DOT _bytes) p) *
   @data_at HCS Ews (tarray tuchar (2 ^ 19 - Zlength (ws_bytes ws))) (Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength (ws_bytes ws)))
     (@field_address0 HCS (tarray tuchar (2 ^ 19)) (SUB (Zlength (ws_bytes ws))) (@field_address HCS t_wseries (DOT _bytes) p)) *
   @field_at HCS Ews t_wseries (DOT _f)
     (map winfo_val (ws_frames ws) ++ Zrepeat (winfo_val winfo0) (4 - Zlength (ws_frames ws))) p *
   @field_at HCS Ews t_wseries (DOT _nframes) (vu (Zlength (ws_frames ws))) p *
   spacer Ews 786932 786936 p)%logic |-- VB_sr_rest ws p.
Proof. unfold VB_sr_rest. apply derives_refl. Qed.

(* wd: the fields main reads (bytes, n, formatted); the rest is dropped *)
Lemma VB_wd_take wd p stv :
  @data_at HCS Ews t_wdict (wdict_val wd p stv) p |--
  @field_at HCS Ews t_wdict (DOT _bytes) (zbytes (wd_bytes wd) ++ Zrepeat (Vint Int.zero) (6144 - Zlength (wd_bytes wd))) p *
  @field_at HCS Ews t_wdict (DOT _n) (vl (Zlength (wd_bytes wd))) p *
  @field_at HCS Ews t_wdict (DOT _formatted) (vb (wd_formatted wd)) p * TT.
Proof. unfold_data_at (data_at _ _ _ p). cbn [fst snd wdict_val]. cancel. Qed.

(* valid_dict: the dictionaries a context decodes with, and sr's content field split for the content checks. *)

(* the DDict made by reference from the dictionary at p *)
Definition VI_dd (p: val) (b: list Z) (e: ddict_st) : ddict_st :=
  {| dd_bytes := b; dd_ref := Some p; dd_buf := dd_buf e; dd_ld := dd_ld e |}.

(* the dictionary of the context after its round-0 setup: api 2 (loaded), 3 (the DDict), 4 (prefix) *)
Definition VI_dr (api: Z) (q p: val) (b: list Z) (e: ddict_st) : dictref :=
  if api =? 2 then VM_dr2 p b else if api =? 3 then VM_dr3 q p b e else VM_drp p b.

Section Res.
Variable DD : globals -> val -> ddict_st -> mpred.

Lemma VI_res2 gv sh p b : dict_res DD gv sh (Some (VM_dr2 p b)) = @data_at ZCS sh (tarray tuchar (Zlength b)) (zbytes b) p.
Proof. reflexivity. Qed.

Lemma VI_resp gv sh p b : dict_res DD gv sh (Some (VM_drp p b)) = @data_at ZCS sh (tarray tuchar (Zlength b)) (zbytes b) p.
Proof. reflexivity. Qed.

Lemma VI_res3 gv sh q p b e : dict_res DD gv sh (Some (VM_dr3 q p b e)) =
  ((DD gv q (VI_dd p b e) && valid_pointer q) * @data_at ZCS sh (tarray tuchar (Zlength b)) (zbytes b) p)%logic.
Proof. reflexivity. Qed.

Lemma VI_ddres gv sh q p b e : ddict_res DD gv sh q (VI_dd p b e) =
  ((DD gv q (VI_dd p b e) && valid_pointer q) * @data_at ZCS sh (tarray tuchar (Zlength b)) (zbytes b) p)%logic.
Proof. reflexivity. Qed.
End Res.

Lemma VI_res_init1 (DD : globals -> val -> ddict_st -> mpred) gv sh : dict_res DD gv sh (dc_dict dctx_init) = emp.
Proof. reflexivity. Qed.

Lemma VI_res_init2 (DD : globals -> val -> ddict_st -> mpred) gv sh :
  set_res DD gv sh (dc_set dctx_init) (dc_dict dctx_init) = emp.
Proof. reflexivity. Qed.

Lemma VI_dd_eta p b dd : dd_bytes dd = b -> dd_ref dd = Some p -> VI_dd p b dd = dd.
Proof. destruct dd; cbn. intros -> ->. reflexivity. Qed.

Lemma VI_ddq_drop (DD : globals -> val -> ddict_st -> mpred) gv q d :
  (if eq_dec q nullval then emp else (DD gv q d && valid_pointer q)) |--
  match (if eq_dec q nullval then None else Some d) with None => emp | Some x => DD gv q x end.
Proof. destruct (eq_dec q nullval); [apply derives_refl | apply andp_left1, derives_refl]. Qed.

Lemma VI_ddref q p b e : ddict_ref q (VI_dd p b e) = VM_dr3 q p b e.
Proof. reflexivity. Qed.

Lemma VI_model2 wd p : dict_facts wd -> dictref_model (Some (VM_dr2 p (wd_bytes wd))) = Some (wd_model wd).
Proof. intros Hf. cbn. apply VM_model_auto; auto. Qed.

Lemma VI_model3 wd q p e : dict_facts wd -> dictref_model (Some (VM_dr3 q p (wd_bytes wd) e)) = Some (wd_model wd).
Proof. intros Hf. cbn. apply VM_model_auto; auto. Qed.

Lemma VI_modelp wd p : dict_facts wd -> wd_formatted wd = false ->
  dictref_model (Some (VM_drp p (wd_bytes wd))) = Some (wd_model wd).
Proof. intros Hf Hr. cbn. apply VM_model_raw; auto. Qed.

(* sr.content as its bytes and the zeros after them *)
Lemma VI_content_split ws p : Zlength (ws_content ws) <= 2 ^ 18 -> field_compatible t_wseries (DOT _content) p ->
  field_at Ews t_wseries (DOT _content) (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws))) p =
  (data_at Ews (tarray tuchar (Zlength (ws_content ws))) (zbytes (ws_content ws)) (field_address t_wseries (DOT _content) p) *
   data_at Ews (tarray tuchar (262144 - Zlength (ws_content ws))) (Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws)))
     (field_address0 (tarray tuchar 262144) (SUB (Zlength (ws_content ws))) (field_address t_wseries (DOT _content) p)))%logic.
Proof.
  intros Hn Hfc. rewrite field_at_data_at.
  change (nested_field_type t_wseries (DOT _content)) with (tarray tuchar 262144).
  apply split2_data_at_Tarray_app; rewrite ?Zlength_map, ?Zlength_Zrepeat; rep_lia.
Qed.

Lemma VI_content_fold ws p : Zlength (ws_content ws) <= 2 ^ 18 -> field_compatible t_wseries (DOT _content) p ->
  data_at Ews (tarray tuchar (Zlength (ws_content ws))) (zbytes (ws_content ws)) (field_address t_wseries (DOT _content) p) *
  data_at Ews (tarray tuchar (262144 - Zlength (ws_content ws))) (Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws)))
     (field_address0 (tarray tuchar 262144) (SUB (Zlength (ws_content ws))) (field_address t_wseries (DOT _content) p))
  |-- field_at Ews t_wseries (DOT _content) (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws))) p.
Proof. intros Hn Hfc. rewrite (VI_content_split ws p Hn Hfc). apply derives_refl. Qed.

Lemma VI_ltu64 x y : 0 <= x <= Int64.max_unsigned -> 0 <= y <= Int64.max_unsigned ->
  Int64.ltu (Int64.repr x) (Int64.repr y) = (x <? y).
Proof.
  intros Hx Hy. unfold Int64.ltu. rewrite !Int64.unsigned_repr by lia.
  destruct (zlt x y); destruct (Z.ltb_spec x y); lia || reflexivity.
Qed.


(* ---------- main's precondition: the decoder's tables, the writer's statics, sr and wd ---------- *)

Lemma VD_filter_filter {A: Type} (f g: A -> bool) l :
  filter f (filter g l) = filter (fun x => andb (g x) (f x)) l.
Proof.
  induction l as [|a l IH]; simpl; auto.
  destruct (g a); simpl; [destruct (f a); simpl; rewrite IH; auto | exact IH].
Qed.

Lemma VD_wvar_not_zstd : forallb (fun i => negb (id_in_list i MainPre6.zstd_var_ids)) wvar_ids = true.
Proof. vm_compute. reflexivity. Qed.

Lemma VD_wvardefs :
  filter (fun ig => id_in_list (fst ig) wvar_ids)
    (filter (fun ig => negb (id_in_list (fst ig) MainPre6.zstd_var_ids)) (Vardefs Zstd.contracts.x_valid_dict.whole_prog))
  = wvardefs.
Proof.
  rewrite VD_filter_filter. unfold wvardefs. apply filter_ext. intros [i g]; cbn [fst].
  destruct (id_in_list i wvar_ids) eqn:E; [|apply andb_false_r].
  rewrite andb_true_r.
  pose proof VD_wvar_not_zstd as H. rewrite forallb_forall in H.
  apply id_in_list_true in E. exact (H i E).
Qed.

Lemma VD_InitGPred_in x l gv : In x l -> InitGPred l gv |-- globs2pred gv x * TT.
Proof.
  intros Hin. apply in_split in Hin as [l1 [l2 ->]].
  rewrite InitGPred_middleD. rewrite sepcon_assoc. apply sepcon_derives; [apply derives_refl | apply TT_right].
Qed.

Local Notation VD_rest :=
  (filter (fun ig : ident * globdef (fundef function) type => negb (id_in_list (fst ig) wvar_ids))
    (filter (fun ig : ident * globdef (fundef function) type => negb (id_in_list (fst ig) MainPre6.zstd_var_ids))
       (Vardefs Zstd.contracts.x_valid_dict.whole_prog))).

Lemma VD_sr_in : In (_x_valid_dict__sr, Gvar v_x_valid_dict__sr) VD_rest.
Proof.
  rewrite !filter_In. split; [split|].
  - unfold Vardefs. apply filter_In. split; [|reflexivity].
    apply Maps.PTree.elements_correct. vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.

Lemma VD_wd_in :
  In (_x_valid_dict__wd, Gvar v_x_valid_dict__wd)
    (filter (fun x : ident * globdef (fundef function) type => negb (Pos.eqb (fst x) _x_valid_dict__sr)) VD_rest).
Proof.
  rewrite filter_In. split; [|vm_compute; reflexivity].
  rewrite !filter_In. split; [split|].
  - unfold Vardefs. apply filter_In. split; [|reflexivity].
    apply Maps.PTree.elements_correct. vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.

Lemma VD_sr_only :
  filter (fun x : ident * globdef (fundef function) type => Pos.eqb (fst x) _x_valid_dict__sr) VD_rest = [(_x_valid_dict__sr, Gvar v_x_valid_dict__sr)].
Proof. vm_compute. reflexivity. Qed.

Lemma VD_sr_zero gv :
  globs2pred gv (_x_valid_dict__sr, Gvar v_x_valid_dict__sr) |-- data_at Ews t_wseries (zero_val t_wseries) (gv _x_valid_dict__sr).
Proof.
  unfold globs2pred. apply derives_extract_prop; intros Hh.
  unfold globvar2pred. simpl. rewrite sepcon_emp.
  change 786936 with (@sizeof HCS t_wseries).
  apply mapsto_zero_data_at_zero.
  - auto.
  - reflexivity.
  - reflexivity.
  - destruct Hh as [b ->]. repeat split; auto.
    hnf. rewrite Ptrofs.unsigned_zero. apply la_env_cs_sound; vm_compute; reflexivity.
Qed.

Lemma VD_wd_zero gv :
  globs2pred gv (_x_valid_dict__wd, Gvar v_x_valid_dict__wd) |-- data_at Ews t_wdict (zero_val t_wdict) (gv _x_valid_dict__wd).
Proof.
  unfold globs2pred. apply derives_extract_prop; intros Hh.
  unfold globvar2pred. simpl. rewrite sepcon_emp.
  change 13984 with (@sizeof HCS t_wdict).
  apply mapsto_zero_data_at_zero.
  - auto.
  - reflexivity.
  - reflexivity.
  - destruct Hh as [b ->]. repeat split; auto.
    hnf. rewrite Ptrofs.unsigned_zero. apply la_env_cs_sound; vm_compute; reflexivity.
Qed.

Lemma VD_rest_zero gv :
  InitGPred VD_rest gv |--
  data_at Ews t_wseries (zero_val t_wseries) (gv _x_valid_dict__sr) *
  (data_at Ews t_wdict (zero_val t_wdict) (gv _x_valid_dict__wd) * TT).
Proof.
  rewrite (MainPre6.MP_InitGPred_filter (fun x : ident * globdef (fundef function) type => Pos.eqb (fst x) _x_valid_dict__sr)).
  rewrite VD_sr_only. rewrite InitGPred_consD, InitGPred_nilD, sepcon_emp.
  apply sepcon_derives; [apply VD_sr_zero|].
  eapply derives_trans; [apply VD_InitGPred_in, VD_wd_in|].
  apply sepcon_derives; [apply VD_wd_zero | apply derives_refl].
Qed.

Lemma VD_pre (WG: globals -> mpred) (HWG: forall gv, InitGPred wvardefs gv |-- WG gv) gv :
  globals_ok gv ->
  InitGPred (Vardefs Zstd.contracts.x_valid_dict.whole_prog) gv |--
  zstd_globals gv * (WG gv * (data_at Ews t_wseries (zero_val t_wseries) (gv _x_valid_dict__sr) *
                              (data_at Ews t_wdict (zero_val t_wdict) (gv _x_valid_dict__wd) * TT))).
Proof.
  intros Hgv. eapply derives_trans.
  - apply (MainPre6.main_pre_fact6 Zstd.contracts.x_valid_dict.whole_prog); [|exact Hgv].
    unfold MainPre6.all_progs. do 8 right; left; reflexivity.
  - apply sepcon_derives; [apply derives_refl|].
    rewrite (MainPre6.MP_InitGPred_filter (fun ig => id_in_list (fst ig) wvar_ids)).
    rewrite VD_wvardefs. apply sepcon_derives; [apply HWG|].
    exact (VD_rest_zero gv).
Qed.

(* ---------- compspecs: the API's (decoder) and main's (this unit) ---------- *)

Definition VD_cce (cs1 cs2: compspecs) : change_composite_env cs1 cs2 :=
  {| coeq := cs_preserve_env cs1 cs2;
     coeq_consistent := cs_preserve_env_consistent cs1 cs2 _ eq_refl;
     coeq_complete := cs_preserve_completeness cs1 cs2 _ eq_refl |}.

Lemma VD_arr: forall sh n (v: list val) p,
  @data_at ZCS sh (tarray tuchar n) v p = @data_at HCS sh (tarray tuchar n) v p.
Proof.
  intros. pose proof (@data_at_change_composite ZCS HCS (VD_cce ZCS HCS) sh (tarray tuchar n) v v
    (JMeq_refl _) ltac:(reflexivity)) as E. rewrite E; reflexivity.
Qed.

Lemma VD_arr_: forall sh n p,
  @data_at_ ZCS sh (tarray tuchar n) p = @data_at_ HCS sh (tarray tuchar n) p.
Proof.
  intros. pose proof (@data_at__change_composite ZCS HCS (VD_cce ZCS HCS) sh (tarray tuchar n)
    ltac:(reflexivity)) as E. rewrite E; reflexivity.
Qed.

Lemma VD_Externals : Externals = [nondet_u32_spec; gp_assert_spec; gp_assume_spec].
Proof.
  unfold Externals, present, env_harness, filter.
  repeat match goal with |- context [id_in_list ?i ?l] =>
    let b := eval lazy in (id_in_list i l) in change (id_in_list i l) with b end.
  reflexivity.
Qed.

Lemma VD_tyc_g_isSome: forall (V: varspecs) G i, In i (map fst V) ->
  isSome (Maps.PTree.get i (make_tycontext_g V G)).
Proof.
  intros. unfold make_tycontext_g. induction G as [|[j f] G IH]; simpl.
  - induction V as [|[k t] V IHV]; simpl in *; [contradiction|].
    rewrite Maps.PTree.gsspec. destruct (peq i k); simpl; auto.
    apply IHV. destruct H; [congruence|auto].
  - rewrite Maps.PTree.gsspec. destruct (peq i j); simpl; auto.
Qed.

(* ---------- sr field by field (a load from the whole struct overflows the stack) ---------- *)

(* ---------- sr field by field (a load from the whole struct overflows the stack) ---------- *)

Definition VD_sr_fields (ws: wseries) (p: val) : mpred := (
  field_at Ews t_wseries (DOT _bytes) (fst (wseries_val ws)) p *
  (field_at Ews t_wseries (DOT _n) (fst (snd (wseries_val ws))) p *
  (field_at Ews t_wseries (DOT _content) (fst (snd (snd (wseries_val ws)))) p *
  (field_at Ews t_wseries (DOT _content_n) (fst (snd (snd (snd (wseries_val ws))))) p *
  (field_at Ews t_wseries (DOT _f) (fst (snd (snd (snd (snd (wseries_val ws)))))) p *
  (field_at Ews t_wseries (DOT _nframes) (snd (snd (snd (snd (snd (wseries_val ws)))))) p *
  spacer Ews 786932 786936 p))))))%logic.

Lemma VD_sr_eq ws p : data_at Ews t_wseries (wseries_val ws) p = VD_sr_fields ws p.
Proof.
  unfold_data_at (data_at _ _ _ _). reflexivity.
Qed.

Lemma VD_sr_sep {A: Type} ws p (R: list mpred) :
  @SEPx A (data_at Ews t_wseries (wseries_val ws) p :: R) =
  @SEPx A (field_at Ews t_wseries (DOT _bytes) (fst (wseries_val ws)) p ::
           field_at Ews t_wseries (DOT _n) (fst (snd (wseries_val ws))) p ::
           field_at Ews t_wseries (DOT _content) (fst (snd (snd (wseries_val ws)))) p ::
           field_at Ews t_wseries (DOT _content_n) (fst (snd (snd (snd (wseries_val ws))))) p ::
           field_at Ews t_wseries (DOT _f) (fst (snd (snd (snd (snd (wseries_val ws)))))) p ::
           field_at Ews t_wseries (DOT _nframes) (snd (snd (snd (snd (snd (wseries_val ws)))))) p ::
           spacer Ews 786932 786936 p :: R).
Proof.
  unfold SEPx. extensionality x. cbn [fold_right_sepcon].
  rewrite VD_sr_eq. unfold VD_sr_fields. rewrite !sepcon_assoc. reflexivity.
Qed.

Lemma VD_sr_nframes ws : snd (snd (snd (snd (snd (wseries_val ws))))) = vu (Zlength (ws_frames ws)).
Proof. reflexivity. Qed.

Lemma VD_sr_f ws : fst (snd (snd (snd (snd (wseries_val ws))))) =
  map winfo_val (ws_frames ws) ++ Zrepeat (winfo_val winfo0) (4 - Zlength (ws_frames ws)).
Proof. reflexivity. Qed.

Lemma VD_sr_content_n ws : fst (snd (snd (snd (wseries_val ws)))) = vl (Zlength (ws_content ws)).
Proof. reflexivity. Qed.

Lemma VD_sr_content ws : fst (snd (snd (wseries_val ws))) =
  zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws)).
Proof. reflexivity. Qed.

Lemma VD_sr_bytes ws : fst (wseries_val ws) =
  zbytes (ws_bytes ws) ++ Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength (ws_bytes ws)).
Proof. reflexivity. Qed.

Lemma VD_bytes_split ws p : field_compatible t_wseries (DOT _bytes) p -> Zlength (ws_bytes ws) <= 2 ^ 19 ->
  field_at Ews t_wseries (DOT _bytes) (fst (wseries_val ws)) p =
  (data_at Ews (tarray tuchar (Zlength (ws_bytes ws))) (zbytes (ws_bytes ws)) p *
   data_at Ews (tarray tuchar (2 ^ 19 - Zlength (ws_bytes ws))) (Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength (ws_bytes ws)))
     (offset_val (Zlength (ws_bytes ws)) p))%logic.
Proof.
  intros Hf Hl. rewrite field_at_data_at. rewrite VD_sr_bytes.
  rewrite field_address_offset by auto. simpl nested_field_offset. rewrite isptr_offset_val_zero by auto with field_compatible.
  change (nested_field_type t_wseries (DOT _bytes)) with (tarray tuchar 524288).
  assert (Hz: Zlength (zbytes (ws_bytes ws)) = Zlength (ws_bytes ws)) by (unfold zbytes; apply Zlength_map).
  pose proof (Zlength_nonneg (ws_bytes ws)).
  rewrite (split2_data_at_Tarray_app (Zlength (ws_bytes ws)) 524288 Ews tuchar (zbytes (ws_bytes ws))
             (Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength (ws_bytes ws)))); auto.
  - assert (Hf': field_compatible (tarray tuchar 524288) [] p).
    { pose proof (field_compatible_nested_field _ _ _ Hf) as X.
      change (nested_field_type t_wseries (DOT _bytes)) with (tarray tuchar 524288) in X.
      change (nested_field_offset t_wseries (DOT _bytes)) with 0 in X.
      rewrite isptr_offset_val_zero in X by auto with field_compatible. exact X. }
    rewrite field_address0_offset by auto with field_compatible.
    simpl nested_field_offset. rewrite Z.mul_1_l, Z.add_0_l. reflexivity.
  - rewrite Zlength_Zrepeat by lia. lia.
Qed.

Lemma VD_sr_n ws : fst (snd (wseries_val ws)) = vl (Zlength (ws_bytes ws)).
Proof. reflexivity. Qed.

Ltac kill :=
  match goal with
  | H: false = true |- _ => discriminate H
  | H: true = false |- _ => discriminate H
  | H: ?x <> ?x |- _ => exfalso; exact (H eq_refl)
  | H: Int.repr ?x = Int.repr ?y |- _ =>
      exfalso; apply repr_inj_unsigned in H; [lia | rep_lia | rep_lia]
  | H: typed_true _ _ |- _ => inv H
  | H: typed_false _ _ |- _ => inv H
  end.

Ltac ifs := repeat apply -> seq_assoc; apply semax_if_seq; forward_if; try solve [kill | exfalso; lia].

(* the rounds = 0 paths: through the ifs and the empty loop to the frees *)
Ltac VD_side := try (match goal with |- _ |-- _ =>
  first [rewrite if_true by auto | rewrite if_false by discriminate | idtac]; cancel end).
Ltac VD_front :=
  repeat (first [rewrite if_true by auto | rewrite if_false by discriminate]); Intros;
  repeat (first [ifs | forward]);
  (match goal with |- semax _ ?P _ _ => forward_loop P break: P end);
  [ entailer! | ifs; forward; entailer! | idtac ].

(* ---------- main in the context of only the functions it calls (lifted to G0 below) ---------- *)

Section Body.
Variable DC : globals -> val -> dctx_st -> mpred.
Variable DD : globals -> val -> ddict_st -> mpred.
Variable WG : globals -> mpred.
Variable WDS : wdict -> reptype t_wstate -> Prop.
Variable HWG : forall gv, InitGPred wvardefs gv |-- WG gv.

Definition VD_G1 : funspecs :=
  [(_quickproof_malloc, malloc_spec'); (_quickproof_free, free_spec');
   ZSTD_isError_spec; ZSTD_getErrorCode_spec; ZSTD_decompressDCtx_spec DC DD; ZSTD_decompress_usingDict_spec DC;
   ZSTD_decompress_usingDDict_spec DC DD;
   ZSTD_createDCtx_spec DC; ZSTD_freeDCtx_spec DC; ZSTD_createDDict_byReference_spec DD; ZSTD_freeDDict_spec DD;
   ZSTD_DCtx_loadDictionary_byReference_spec DC; ZSTD_DCtx_refPrefix_spec DC; ZSTD_DCtx_refDDict_spec DC DD;
   gp_assert_spec; gp_assume_spec;
   choose_spec; choose_in_spec; exact_copy_spec; within_oneshot_spec; w_dict_spec WG WDS; w_series_spec WG WDS].

(* the round loop's body, in two lemmas (each Qed checked separately) *)
Definition VD_loop_parts : statement * statement * statement := ltac:(
  let b := eval cbv delta [f_main fn_body] beta iota in (fn_body f_main) in
  lazymatch b with context [Sloop (Ssequence (Sifthenelse (Ebinop Olt (Etempvar _k ?t1) (Etempvar _rounds ?t2) ?t3) Sskip Sbreak)
                                   (Ssequence ?d ?c)) ?i] => exact (d, c, i) end).
Definition VD_dec_s : statement := ltac:(let x := eval cbv [VD_loop_parts fst snd] in (fst (fst VD_loop_parts)) in exact x).
Definition VD_chk_s : statement := ltac:(let x := eval cbv [VD_loop_parts fst snd] in (snd (fst VD_loop_parts)) in exact x).
Definition VD_incr_s : statement := ltac:(let x := eval cbv [VD_loop_parts fst snd] in (snd VD_loop_parts) in exact x).

Lemma VD_dec_ok {Espec: OracleKind} (gv: globals) (api: Z) (H: 0 <= api < 5) (wd: wdict) (H0: dict_facts wd) (H1: wdict_wf wd) (ws: wseries)
  (H2: series_facts (wdict_model (Some (wd, Ews))) ws) (H3: wseries_wf ws) (H4: readable_share Ews)
  (stv: reptype t_wstate) (H5: WDS wd stv) (Hfacts: series_facts (wd_model wd) ws)
  (Hbok: bytes_ok (ws_bytes ws)) (Hcok: bytes_ok (ws_content ws)) (Hnb: Zlength (ws_bytes ws) <= 2 ^ 19)
  (Hnc: Zlength (ws_content ws) <= 2 ^ 18) (Hnf: (1 <= Datatypes.length (ws_frames ws) <= 4)%nat)
  (Hdok: bytes_ok (wd_bytes wd)) (Hdl: 8 <= Zlength (wd_bytes wd) <= 2 ^ 12 + 2048) (Hda: dict_auto (wd_bytes wd) <> None)
  (Hdc: dm_content (wd_model wd) = wd_content wd) (Hdi: dm_id (wd_model wd) = wd_id wd) (Hdid: dict_id_of (wd_bytes wd) = wd_id wd)
  (Hraw: wd_formatted wd = false -> wd_model wd = dict_raw (wd_bytes wd) /\ wd_id wd = 0)
  (Hapi4: api = 4 -> wd_formatted wd = false /\ Zlength (ws_frames ws) = 1 /\ wi_skippable (hd winfo0 (ws_frames ws)) = false)
  (cap: Z) (H6: 0 <= cap <= Zlength (ws_content ws) + 16) (bs: block) (os: ptrofs) (PNsrc: is_pointer_or_null (Vptr bs os))
  (bb: block) (ob: ptrofs) (bd: block) (od: ptrofs) (PNdctx: is_pointer_or_null (Vptr bd od))
  (Hvp: forall (P: mpred) (q0: val), P && valid_pointer q0 |-- P)
  (Hs: Vptr bs os <> nullval) (Hps: isptr (Vptr bs os)) (Hb: Vptr bb ob <> nullval) (Hpb: isptr (Vptr bb ob))
  (Hd: Vptr bd od <> nullval) (Hpd: isptr (Vptr bd od)) (H7 H8 H9 H10: true = true)
  (Hrr: 1 <= VM_rnd api <= 2) (H11: 0 < VM_rnd api)
  (Hfb: field_compatible (tarray tuchar (cap + 1 + Zlength (wd_bytes wd))) [] (Vptr bb ob)) (q: val) (e: ddict_st) (rnd: Z)
  (H12: q = nullval /\ rnd = VM_rnd api /\ ((api =? 1) || (api =? 3))%bool = false \/
        ((api =? 1) || (api =? 3))%bool = true /\ (q = nullval /\ rnd = 0 \/ isptr q /\ rnd = 1))
  (Hfs: field_compatible (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws)))) [] (Vptr bs os))
  (k R: Z) (st: dctx_st) (out: list val) (H13: 0 <= k <= R) (H14: R <= 2) (H15: R = 2 -> api = 2)
  (H16: 0 < R -> ((api =? 1) || (api =? 3))%bool = true -> isptr q) (H17: ((api =? 1) || (api =? 3))%bool = false -> q = nullval)
  (H18: Zlength out = cap) (H19: dc_ss st = ss_init) (H19d: VM_df st) (H20: k = 0 -> st = dctx_init)
  (H21: 0 < k < R -> dc_dict st = Some (VM_dr2 (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd)) /\
                     last_ok st (VM_dr2 (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd)))
  (H22: k < R) :
  semax (func_tycontext f_main Vprog VD_G1 nil)
    (PROP () LOCAL (temp _k (Vint (Int.repr k)); temp _rounds (Vint (Int.repr R)); temp _ddict q; temp _dctx (Vptr bd od);
         temp _dst (Vptr bb ob); temp _buf (Vptr bb ob); temp _dict (offset_val (cap + 1) (Vptr bb ob)); temp _src (Vptr bs os); temp _cap (Vlong (Int64.repr cap));
         temp _api (Vint (Int.repr api)); gvars gv)
    SEP (mem_mgr gv; zstd_globals gv; DC gv (Vptr bd od) st;
         (if eq_dec q nullval then emp else (DD gv q (VI_dd (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd) e) && valid_pointer q));
         @data_at ZCS Ews (tarray tuchar (Zlength (wd_bytes wd))) (zbytes (wd_bytes wd)) (offset_val (cap + 1) (Vptr bb ob));
         pws_pred (VB_W (Vptr bs os) (Zlength (ws_bytes ws)) (Vptr bb ob) cap); @data_at ZCS Ews (tarray tuchar cap) out (Vptr bb ob);
         @data_at ZCS Ews (tarray tuchar (Zlength (ws_bytes ws))) (zbytes (ws_bytes ws)) (Vptr bs os);
         @malloc_token HCS Ews (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws)))) (Vptr bs os);
         @malloc_token HCS Ews (tarray tuchar (cap + 1 + Zlength (wd_bytes wd))) (Vptr bb ob);
         VB_sr_rest ws (gv _x_valid_dict__sr);
         @field_at HCS Ews t_wseries (DOT _n) (vl (Zlength (ws_bytes ws))) (gv _x_valid_dict__sr);
         @field_at HCS Ews t_wseries (DOT _content) (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws))) (gv _x_valid_dict__sr);
         @field_at HCS Ews t_wseries (DOT _content_n) (vl (Zlength (ws_content ws))) (gv _x_valid_dict__sr);
         @field_at HCS Ews t_wdict (DOT _n) (vl (Zlength (wd_bytes wd))) (gv _x_valid_dict__wd); TT))
    VD_dec_s
    (normal_ret_assert (EX r: Z, EX R': Z, EX st': dctx_st, EX out': list val,
        PROP (0 <= r <= Int64.max_unsigned; k + 1 <= R' <= R; Zlength out' = cap; dc_ss st' = ss_init; VM_df st';
              (0 < k + 1 < R' -> dc_dict st' = Some (VM_dr2 (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd)) /\ last_ok st' (VM_dr2 (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd)));
              VM_round (wd_model wd) (ws_bytes ws) cap r out')
        LOCAL (temp _r (Vlong (Int64.repr r)); temp _k (Vint (Int.repr k)); temp _rounds (Vint (Int.repr R')); temp _ddict q; temp _dctx (Vptr bd od);
             temp _dst (Vptr bb ob); temp _buf (Vptr bb ob); temp _dict (offset_val (cap + 1) (Vptr bb ob)); temp _src (Vptr bs os); temp _cap (Vlong (Int64.repr cap));
             temp _api (Vint (Int.repr api)); gvars gv)
        SEP (mem_mgr gv; zstd_globals gv; DC gv (Vptr bd od) st';
             (if eq_dec q nullval then emp else (DD gv q (VI_dd (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd) e) && valid_pointer q));
             @data_at ZCS Ews (tarray tuchar (Zlength (wd_bytes wd))) (zbytes (wd_bytes wd)) (offset_val (cap + 1) (Vptr bb ob));
             pws_pred (VB_W (Vptr bs os) (Zlength (ws_bytes ws)) (Vptr bb ob) cap); @data_at ZCS Ews (tarray tuchar cap) out' (Vptr bb ob);
             @data_at ZCS Ews (tarray tuchar (Zlength (ws_bytes ws))) (zbytes (ws_bytes ws)) (Vptr bs os);
             @malloc_token HCS Ews (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws)))) (Vptr bs os);
             @malloc_token HCS Ews (tarray tuchar (cap + 1 + Zlength (wd_bytes wd))) (Vptr bb ob);
             VB_sr_rest ws (gv _x_valid_dict__sr);
             @field_at HCS Ews t_wseries (DOT _n) (vl (Zlength (ws_bytes ws))) (gv _x_valid_dict__sr);
             @field_at HCS Ews t_wseries (DOT _content) (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws))) (gv _x_valid_dict__sr);
             @field_at HCS Ews t_wseries (DOT _content_n) (vl (Zlength (ws_content ws))) (gv _x_valid_dict__sr);
             @field_at HCS Ews t_wdict (DOT _n) (vl (Zlength (wd_bytes wd))) (gv _x_valid_dict__wd); TT))%assert).
Proof.
  simplify_func_tycontext. unfold VD_dec_s.
    forward_if (EX r: Z, EX R': Z, EX st': dctx_st, EX out': list val,
        PROP (0 <= r <= Int64.max_unsigned; k + 1 <= R' <= R; Zlength out' = cap; dc_ss st' = ss_init; VM_df st';
              (0 < k + 1 < R' -> dc_dict st' = Some (VM_dr2 (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd)) /\ last_ok st' (VM_dr2 (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd)));
              VM_round (wd_model wd) (ws_bytes ws) cap r out')
        LOCAL (temp _r (Vlong (Int64.repr r)); temp _k (Vint (Int.repr k)); temp _rounds (Vint (Int.repr R')); temp _ddict q; temp _dctx (Vptr bd od);
             temp _dst (Vptr bb ob); temp _buf (Vptr bb ob); temp _dict (offset_val (cap + 1) (Vptr bb ob)); temp _src (Vptr bs os); temp _cap (Vlong (Int64.repr cap));
             temp _api (Vint (Int.repr api)); gvars gv)
        SEP (mem_mgr gv; zstd_globals gv; DC gv (Vptr bd od) st';
             (if eq_dec q nullval then emp else (DD gv q (VI_dd (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd) e) && valid_pointer q));
             @data_at ZCS Ews (tarray tuchar (Zlength (wd_bytes wd))) (zbytes (wd_bytes wd)) (offset_val (cap + 1) (Vptr bb ob));
             pws_pred (VB_W (Vptr bs os) (Zlength (ws_bytes ws)) (Vptr bb ob) cap); @data_at ZCS Ews (tarray tuchar cap) out' (Vptr bb ob);
             @data_at ZCS Ews (tarray tuchar (Zlength (ws_bytes ws))) (zbytes (ws_bytes ws)) (Vptr bs os);
             @malloc_token HCS Ews (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws)))) (Vptr bs os);
             @malloc_token HCS Ews (tarray tuchar (cap + 1 + Zlength (wd_bytes wd))) (Vptr bb ob);
             VB_sr_rest ws (gv _x_valid_dict__sr);
             @field_at HCS Ews t_wseries (DOT _n) (vl (Zlength (ws_bytes ws))) (gv _x_valid_dict__sr);
             @field_at HCS Ews t_wseries (DOT _content) (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws))) (gv _x_valid_dict__sr);
             @field_at HCS Ews t_wseries (DOT _content_n) (vl (Zlength (ws_content ws))) (gv _x_valid_dict__sr);
             @field_at HCS Ews t_wdict (DOT _n) (vl (Zlength (wd_bytes wd))) (gv _x_valid_dict__wd); TT))%assert.
    { (* api 0: ZSTD_decompress_usingDict *)
      assert (Hk0: k = 0).
      { match goal with HR: R = 2 -> api = 2, Ha: api = 0 |- _ =>
          assert (R <> 2) by (intro HR2; specialize (HR HR2); lia) end. lia. }
      match goal with Hst: k = 0 -> st = dctx_init |- _ => rewrite (Hst Hk0) in * end.
      forward. forward.
      sep_apply (@data_at_data_at_ ZCS Ews (tarray tuchar cap) out (Vptr bb ob)).
      forward_call ((VB_W (Vptr bs os) (Zlength (ws_bytes ws)) (Vptr bb ob) cap), gv, Vptr bd od, dctx_init, Ews, Vptr bb ob, cap, Ews, Vptr bs os, ws_bytes ws, Ews, (offset_val (cap + 1) (Vptr bb ob)), wd_bytes wd).
      { split; [apply VB_buf_ok_dst; [exact I | lia] | split; [apply VB_buf_ok_src; [exact I | rep_lia] | left; apply VB_dict_ptr_ok; [exact I | lia | rep_lia | assumption]]]. }
      Intros vret. destruct vret as [[r out'] st']. cbn [fst snd] in *.
      forward.
      Exists r R st' out'. entailer!.
      split.
      - api_init; match goal with Ha: after_decode dctx_init st' _ |- _ => rewrite (VM_after_ss0 _ _ _ Ha); reflexivity end.
      - split; [eapply VM_df_after; [apply VM_df_init | eassumption] |].
        left. match goal with Ho: oneshot_ok _ _ _ _ _ _ |- _ => rewrite (VM_model_auto wd) in Ho by assumption; exact Ho end. }
    { forward_if (EX r: Z, EX R': Z, EX st': dctx_st, EX out': list val,
    PROP (0 <= r <= Int64.max_unsigned; k + 1 <= R' <= R; Zlength out' = cap; dc_ss st' = ss_init; VM_df st';
          (0 < k + 1 < R' -> dc_dict st' = Some (VM_dr2 (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd)) /\ last_ok st' (VM_dr2 (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd)));
          VM_round (wd_model wd) (ws_bytes ws) cap r out')
    LOCAL (temp _r (Vlong (Int64.repr r)); temp _k (Vint (Int.repr k)); temp _rounds (Vint (Int.repr R')); temp _ddict q; temp _dctx (Vptr bd od);
         temp _dst (Vptr bb ob); temp _buf (Vptr bb ob); temp _dict (offset_val (cap + 1) (Vptr bb ob)); temp _src (Vptr bs os); temp _cap (Vlong (Int64.repr cap));
         temp _api (Vint (Int.repr api)); gvars gv)
    SEP (mem_mgr gv; zstd_globals gv; DC gv (Vptr bd od) st';
         (if eq_dec q nullval then emp else (DD gv q (VI_dd (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd) e) && valid_pointer q));
         @data_at ZCS Ews (tarray tuchar (Zlength (wd_bytes wd))) (zbytes (wd_bytes wd)) (offset_val (cap + 1) (Vptr bb ob));
         pws_pred (VB_W (Vptr bs os) (Zlength (ws_bytes ws)) (Vptr bb ob) cap); @data_at ZCS Ews (tarray tuchar cap) out' (Vptr bb ob);
         @data_at ZCS Ews (tarray tuchar (Zlength (ws_bytes ws))) (zbytes (ws_bytes ws)) (Vptr bs os);
         @malloc_token HCS Ews (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws)))) (Vptr bs os);
         @malloc_token HCS Ews (tarray tuchar (cap + 1 + Zlength (wd_bytes wd))) (Vptr bb ob);
         VB_sr_rest ws (gv _x_valid_dict__sr);
         @field_at HCS Ews t_wseries (DOT _n) (vl (Zlength (ws_bytes ws))) (gv _x_valid_dict__sr);
         @field_at HCS Ews t_wseries (DOT _content) (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws))) (gv _x_valid_dict__sr);
         @field_at HCS Ews t_wseries (DOT _content_n) (vl (Zlength (ws_content ws))) (gv _x_valid_dict__sr);
         @field_at HCS Ews t_wdict (DOT _n) (vl (Zlength (wd_bytes wd))) (gv _x_valid_dict__wd); TT))%assert.
      { (* api 1: ZSTD_decompress_usingDDict *)
        assert (Hk0: k = 0).
        { match goal with HR: R = 2 -> api = 2, Ha: api = 1 |- _ =>
            assert (R <> 2) by (intro HR2; specialize (HR HR2); lia) end. lia. }
        match goal with Hst: k = 0 -> st = dctx_init |- _ => rewrite (Hst Hk0) in * end.
        assert (Hpq: isptr q).
        { match goal with HQ: 0 < R -> _ -> isptr q, Ha: api = 1 |- _ => apply HQ; [lia | subst api; reflexivity] end. }
        rewrite (if_false (q = nullval)) by (intro; subst; contradiction).
        forward.
        sep_apply (@data_at_data_at_ ZCS Ews (tarray tuchar cap) out (Vptr bb ob)).
        forward_call ((VB_W (Vptr bs os) (Zlength (ws_bytes ws)) (Vptr bb ob) cap), gv, Vptr bd od, dctx_init, Ews, Vptr bb ob, cap, Ews, Vptr bs os, ws_bytes ws, Ews, q, VI_dd (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd) e).
        { rewrite VI_ddres. cancel. }
        { split; [apply VB_buf_ok_dst; [exact I | lia] | split; [apply VB_buf_ok_src; [exact I | rep_lia] |]].
          unfold ddict_buf_ok, VI_dd. cbn [dd_ref dd_bytes]. apply VB_dict_ptr_ok; [exact I | lia | rep_lia | assumption]. }
        Intros vret. destruct vret as [[r out'] st']. cbn [fst snd] in *.
        rewrite VI_ddres. Intros.
        forward.
        Exists r R st' out'. rewrite (if_false (q = nullval)) by (intro; subst; contradiction). entailer!.
        split.
        - api_init; match goal with Ha: after_decode dctx_init st' _ |- _ => rewrite (VM_after_ss0 _ _ _ Ha); reflexivity end.
        - split; [eapply VM_df_after; [apply VM_df_init | eassumption] |].
          left. match goal with Ho: oneshot_ok _ _ _ _ _ _ |- _ => unfold VI_dd in Ho; cbn [dd_bytes] in Ho;
            rewrite (VM_model_auto wd) in Ho by assumption; exact Ho end. }
      { (* api 2, 3, 4 *)
        forward.
        forward_if (EX r1: Z, EX R': Z, EX st1: dctx_st,
    PROP (0 <= r1 <= Int64.max_unsigned; k + 1 <= R' <= R; dc_ss st1 = ss_init; VM_df st1; last_ok st1 (VI_dr api q (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd) e);
          (is_error_code r1 = false -> dc_dict st1 = Some (VI_dr api q (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd) e) /\ R' = R);
          (is_error_code r1 = true -> r1 = err_code ZSTD_error_memory_allocation /\ R' = (k + 1)%Z))
    LOCAL (temp _r (Vlong (Int64.repr r1)); temp _k (Vint (Int.repr k)); temp _rounds (Vint (Int.repr R')); temp _ddict q; temp _dctx (Vptr bd od);
         temp _dst (Vptr bb ob); temp _buf (Vptr bb ob); temp _dict (offset_val (cap + 1) (Vptr bb ob)); temp _src (Vptr bs os); temp _cap (Vlong (Int64.repr cap));
         temp _api (Vint (Int.repr api)); gvars gv)
    SEP (mem_mgr gv; zstd_globals gv; DC gv (Vptr bd od) st1;
         (if eq_dec q nullval then emp else (DD gv q (VI_dd (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd) e) && valid_pointer q));
         @data_at ZCS Ews (tarray tuchar (Zlength (wd_bytes wd))) (zbytes (wd_bytes wd)) (offset_val (cap + 1) (Vptr bb ob));
         pws_pred (VB_W (Vptr bs os) (Zlength (ws_bytes ws)) (Vptr bb ob) cap); @data_at ZCS Ews (tarray tuchar cap) out (Vptr bb ob);
         @data_at ZCS Ews (tarray tuchar (Zlength (ws_bytes ws))) (zbytes (ws_bytes ws)) (Vptr bs os);
         @malloc_token HCS Ews (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws)))) (Vptr bs os);
         @malloc_token HCS Ews (tarray tuchar (cap + 1 + Zlength (wd_bytes wd))) (Vptr bb ob);
         VB_sr_rest ws (gv _x_valid_dict__sr);
         @field_at HCS Ews t_wseries (DOT _n) (vl (Zlength (ws_bytes ws))) (gv _x_valid_dict__sr);
         @field_at HCS Ews t_wseries (DOT _content) (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws))) (gv _x_valid_dict__sr);
         @field_at HCS Ews t_wseries (DOT _content_n) (vl (Zlength (ws_content ws))) (gv _x_valid_dict__sr);
         @field_at HCS Ews t_wdict (DOT _n) (vl (Zlength (wd_bytes wd))) (gv _x_valid_dict__wd); TT))%assert.
        { (* k = 0: the dictionary of the round *)
          match goal with Hk: k = 0, Hst: k = 0 -> st = dctx_init |- _ => rewrite (Hst Hk) in * end.
          forward_if (EX r1: Z, EX st1: dctx_st,
    PROP (0 <= r1 <= Int64.max_unsigned; dc_ss st1 = ss_init; VM_df st1; dc_last st1 = None;
          (is_error_code r1 = false -> dc_dict st1 = Some (VI_dr api q (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd) e));
          (is_error_code r1 = true -> r1 = err_code ZSTD_error_memory_allocation))
    LOCAL (temp _x_valid_dict__t'15 (Vlong (Int64.repr r1)); temp _r (Vlong (Int64.repr 0)); temp _k (Vint (Int.repr k)); temp _rounds (Vint (Int.repr R)); temp _ddict q; temp _dctx (Vptr bd od);
         temp _dst (Vptr bb ob); temp _buf (Vptr bb ob); temp _dict (offset_val (cap + 1) (Vptr bb ob)); temp _src (Vptr bs os); temp _cap (Vlong (Int64.repr cap));
         temp _api (Vint (Int.repr api)); gvars gv)
    SEP (mem_mgr gv; zstd_globals gv; DC gv (Vptr bd od) st1;
         (if eq_dec q nullval then emp else (DD gv q (VI_dd (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd) e) && valid_pointer q));
         @data_at ZCS Ews (tarray tuchar (Zlength (wd_bytes wd))) (zbytes (wd_bytes wd)) (offset_val (cap + 1) (Vptr bb ob));
         pws_pred (VB_W (Vptr bs os) (Zlength (ws_bytes ws)) (Vptr bb ob) cap); @data_at ZCS Ews (tarray tuchar cap) out (Vptr bb ob);
         @data_at ZCS Ews (tarray tuchar (Zlength (ws_bytes ws))) (zbytes (ws_bytes ws)) (Vptr bs os);
         @malloc_token HCS Ews (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws)))) (Vptr bs os);
         @malloc_token HCS Ews (tarray tuchar (cap + 1 + Zlength (wd_bytes wd))) (Vptr bb ob);
         VB_sr_rest ws (gv _x_valid_dict__sr);
         @field_at HCS Ews t_wseries (DOT _n) (vl (Zlength (ws_bytes ws))) (gv _x_valid_dict__sr);
         @field_at HCS Ews t_wseries (DOT _content) (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws))) (gv _x_valid_dict__sr);
         @field_at HCS Ews t_wseries (DOT _content_n) (vl (Zlength (ws_content ws))) (gv _x_valid_dict__sr);
         @field_at HCS Ews t_wdict (DOT _n) (vl (Zlength (wd_bytes wd))) (gv _x_valid_dict__wd); TT))%assert.
          { (* api 2: ZSTD_DCtx_loadDictionary_byReference *)
            match goal with Ha: api = 2 |- _ => subst api end.
            forward.
            forward_call ([] : list ptr_witness, gv, Vptr bd od, dctx_init, Ews, (offset_val (cap + 1) (Vptr bb ob)), wd_bytes wd).
            { change (pws_pred []) with (@emp mpred _ _). cancel. }
            { apply VB_buf_ok_nil; lia. }
            Intros vret. destruct vret as [r1 st1]. cbn [fst snd] in *. change (pws_pred []) with (@emp mpred _ _).
            forward.
            Exists r1 st1. entailer!.
            api_init; match goal with HL: load_result _ _ _ _ |- _ =>
              destruct (is_error_code r1) eqn:Er;
              [ destruct (VM_load_err _ _ _ _ HL Er (or_intror Hda)) as [-> ->]
              | destruct (VM_load_ok _ _ _ _ HL Er) as [-> ->] ] end;
              repeat split; intros; try reflexivity; try discriminate. }
          { forward_if (EX r1: Z, EX st1: dctx_st,
    PROP (0 <= r1 <= Int64.max_unsigned; dc_ss st1 = ss_init; VM_df st1; dc_last st1 = None;
          (is_error_code r1 = false -> dc_dict st1 = Some (VI_dr api q (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd) e));
          (is_error_code r1 = true -> r1 = err_code ZSTD_error_memory_allocation))
    LOCAL (temp _x_valid_dict__t'15 (Vlong (Int64.repr r1)); temp _r (Vlong (Int64.repr 0)); temp _k (Vint (Int.repr k)); temp _rounds (Vint (Int.repr R)); temp _ddict q; temp _dctx (Vptr bd od);
         temp _dst (Vptr bb ob); temp _buf (Vptr bb ob); temp _dict (offset_val (cap + 1) (Vptr bb ob)); temp _src (Vptr bs os); temp _cap (Vlong (Int64.repr cap));
         temp _api (Vint (Int.repr api)); gvars gv)
    SEP (mem_mgr gv; zstd_globals gv; DC gv (Vptr bd od) st1;
         (if eq_dec q nullval then emp else (DD gv q (VI_dd (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd) e) && valid_pointer q));
         @data_at ZCS Ews (tarray tuchar (Zlength (wd_bytes wd))) (zbytes (wd_bytes wd)) (offset_val (cap + 1) (Vptr bb ob));
         pws_pred (VB_W (Vptr bs os) (Zlength (ws_bytes ws)) (Vptr bb ob) cap); @data_at ZCS Ews (tarray tuchar cap) out (Vptr bb ob);
         @data_at ZCS Ews (tarray tuchar (Zlength (ws_bytes ws))) (zbytes (ws_bytes ws)) (Vptr bs os);
         @malloc_token HCS Ews (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws)))) (Vptr bs os);
         @malloc_token HCS Ews (tarray tuchar (cap + 1 + Zlength (wd_bytes wd))) (Vptr bb ob);
         VB_sr_rest ws (gv _x_valid_dict__sr);
         @field_at HCS Ews t_wseries (DOT _n) (vl (Zlength (ws_bytes ws))) (gv _x_valid_dict__sr);
         @field_at HCS Ews t_wseries (DOT _content) (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws))) (gv _x_valid_dict__sr);
         @field_at HCS Ews t_wseries (DOT _content_n) (vl (Zlength (ws_content ws))) (gv _x_valid_dict__sr);
         @field_at HCS Ews t_wdict (DOT _n) (vl (Zlength (wd_bytes wd))) (gv _x_valid_dict__wd); TT))%assert.
            { (* api 3: ZSTD_DCtx_refDDict *)
              match goal with Ha: api = 3 |- _ => subst api end.
              assert (Hpq: isptr q) by (match goal with HQ: 0 < R -> _ -> isptr q |- _ => apply HQ; [lia | reflexivity] end).
              rewrite (if_false (q = nullval)) by (intro; subst; contradiction).
              sep_apply (Hvp (DD gv q (VI_dd (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd) e)) q).
              forward_call (gv, Vptr bd od, dctx_init, q, VI_dd (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd) e, Ews).
              { rewrite (VI_res_init1 DD gv Ews), (VI_res_init2 DD gv Ews).
                rewrite (if_false (q = nullval)) by (intro; subst; contradiction). cancel. }
              Intros vret. destruct vret as [r1 st1]. cbn [fst snd] in *.
              rewrite (VI_res_init1 DD gv Ews), (VI_res_init2 DD gv Ews).
              assert (Nq: q <> nullval) by (intro; subst; contradiction).
              rewrite (if_false (q = nullval)) by exact Nq.
              api_init; match goal with HR: refddict_result _ _ _ _ _ |- _ =>
                destruct HR as [[-> ->] | [Hm _]]; [| vm_compute in Hm; discriminate] end.
              forward.
              Exists 0 (set_dict dctx_init (Some (VM_dr3 q (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd) e))).
              entailer!.
              all: try (match goal with H: is_error_code 0 = true |- _ => vm_compute in H; discriminate end).
              rewrite (if_false (q = nullval)) by (intro; subst; contradiction). cancel.
              apply derives_refl. }
            { (* api 4: ZSTD_DCtx_refPrefix *)
              assert (Ha4: api = 4) by lia. subst api.
              forward.
              forward_call ([] : list ptr_witness, gv, Vptr bd od, dctx_init, Ews, (offset_val (cap + 1) (Vptr bb ob)), wd_bytes wd).
              { change (pws_pred []) with (@emp mpred _ _). cancel. }
              { apply VB_buf_ok_nil; lia. }
              Intros vret. destruct vret as [r1 st1]. cbn [fst snd] in *. change (pws_pred []) with (@emp mpred _ _).
              forward. forward.
              Exists r1 st1. entailer!.
              api_init; match goal with HL: load_result _ _ _ _ |- _ =>
                destruct (is_error_code r1) eqn:Er;
                [ destruct (VM_load_err _ _ _ _ HL Er (or_introl eq_refl)) as [-> ->]
                | destruct (VM_load_ok _ _ _ _ HL Er) as [-> ->] ] end;
                repeat split; intros; try reflexivity; try discriminate. } }
          Intros r1 st1.
          forward.
          forward_call r1.
          forward_if.
          { forward. Exists r1 1 st1. entailer!.
            split; [left; assumption |].
            intros Ef. exfalso. match goal with Hx: Int.repr (if is_error_code r1 then 1 else 0) <> _ |- _ =>
              rewrite Ef in Hx; apply Hx; reflexivity end. }
          { forward. Exists r1 R st1. entailer!.
            split; [left; assumption |].
            intros Et. exfalso. match goal with Hx: Int.repr (if is_error_code r1 then 1 else 0) = _ |- _ =>
              rewrite Et in Hx; apply repr_inj_unsigned in Hx; rep_lia end. } }
        { (* k > 0: api 2, the dictionary loaded in round 0 *)
          forward. Exists 0 R st. entailer!.
          assert (HR2: R = 2) by lia.
          assert (Ha2: api = 2) by (match goal with HR: R = 2 -> api = 2 |- _ => apply HR, HR2 end). subst api.
          match goal with H21: 0 < k < R -> _ |- _ => destruct (H21 ltac:(lia)) as [Hdd Hlo] end.
          split; [exact Hlo | split; [intros _; split; [exact Hdd | reflexivity] | intros E; vm_compute in E; discriminate]]. }
        Intros r1 R' st1.
        forward_call r1.
        forward_if (EX r: Z, EX R': Z, EX st': dctx_st, EX out': list val,
    PROP (0 <= r <= Int64.max_unsigned; k + 1 <= R' <= R; Zlength out' = cap; dc_ss st' = ss_init; VM_df st';
          (0 < k + 1 < R' -> dc_dict st' = Some (VM_dr2 (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd)) /\ last_ok st' (VM_dr2 (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd)));
          VM_round (wd_model wd) (ws_bytes ws) cap r out')
    LOCAL (temp _r (Vlong (Int64.repr r)); temp _k (Vint (Int.repr k)); temp _rounds (Vint (Int.repr R')); temp _ddict q; temp _dctx (Vptr bd od);
         temp _dst (Vptr bb ob); temp _buf (Vptr bb ob); temp _dict (offset_val (cap + 1) (Vptr bb ob)); temp _src (Vptr bs os); temp _cap (Vlong (Int64.repr cap));
         temp _api (Vint (Int.repr api)); gvars gv)
    SEP (mem_mgr gv; zstd_globals gv; DC gv (Vptr bd od) st';
         (if eq_dec q nullval then emp else (DD gv q (VI_dd (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd) e) && valid_pointer q));
         @data_at ZCS Ews (tarray tuchar (Zlength (wd_bytes wd))) (zbytes (wd_bytes wd)) (offset_val (cap + 1) (Vptr bb ob));
         pws_pred (VB_W (Vptr bs os) (Zlength (ws_bytes ws)) (Vptr bb ob) cap); @data_at ZCS Ews (tarray tuchar cap) out' (Vptr bb ob);
         @data_at ZCS Ews (tarray tuchar (Zlength (ws_bytes ws))) (zbytes (ws_bytes ws)) (Vptr bs os);
         @malloc_token HCS Ews (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws)))) (Vptr bs os);
         @malloc_token HCS Ews (tarray tuchar (cap + 1 + Zlength (wd_bytes wd))) (Vptr bb ob);
         VB_sr_rest ws (gv _x_valid_dict__sr);
         @field_at HCS Ews t_wseries (DOT _n) (vl (Zlength (ws_bytes ws))) (gv _x_valid_dict__sr);
         @field_at HCS Ews t_wseries (DOT _content) (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws))) (gv _x_valid_dict__sr);
         @field_at HCS Ews t_wseries (DOT _content_n) (vl (Zlength (ws_content ws))) (gv _x_valid_dict__sr);
         @field_at HCS Ews t_wdict (DOT _n) (vl (Zlength (wd_bytes wd))) (gv _x_valid_dict__wd); TT))%assert.
        { (* ZSTD_decompressDCtx *)
          assert (Ef: is_error_code r1 = false).
          { destruct (is_error_code r1) eqn:E; [exfalso | reflexivity].
            match goal with Hx: Int.repr 1 = Int.zero |- _ => apply repr_inj_unsigned in Hx; rep_lia end. }
          match goal with HE: is_error_code r1 = false -> _ /\ _ |- _ => destruct (HE Ef) as [Hd1 HR'] end.
          assert (Hapi: api = 2 \/ api = 3 \/ api = 4) by lia.
          assert (Hq3: api = 3 -> q <> nullval).
          { intros ->. match goal with HQ: 0 < R -> _ -> isptr q |- _ =>
              assert (isptr q) by (apply HQ; [lia | reflexivity]) end. intro; subst; contradiction. }
          forward.
          sep_apply (@data_at_data_at_ ZCS Ews (tarray tuchar cap) out (Vptr bb ob)).
          assert (Hfold: (if eq_dec q nullval then emp else (DD gv q (VI_dd (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd) e) && valid_pointer q)) *
             @data_at ZCS Ews (tarray tuchar (Zlength (wd_bytes wd))) (zbytes (wd_bytes wd)) (offset_val (cap + 1) (Vptr bb ob))
             |-- dict_res DD gv Ews (dc_dict st1) *
                 (if api =? 3 then emp else (if eq_dec q nullval then emp else (DD gv q (VI_dd (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd) e) && valid_pointer q)))).
          { rewrite Hd1. destruct Hapi as [-> | [-> | ->]].
            - replace (VI_dr 2 q (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd) e) with (VM_dr2 (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd)) by reflexivity.
              rewrite VI_res2. change (2 =? 3) with false. cbv iota. cancel.
            - replace (VI_dr 3 q (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd) e) with (VM_dr3 q (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd) e) by reflexivity.
              rewrite VI_res3. change (3 =? 3) with true. cbv iota. rewrite if_false by (apply Hq3; reflexivity). cancel.
            - replace (VI_dr 4 q (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd) e) with (VM_drp (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd)) by reflexivity.
              rewrite VI_resp. change (4 =? 3) with false. cbv iota. cancel. }
          assert (Hunfold: dict_res DD gv Ews (dc_dict st1) *
                 (if api =? 3 then emp else (if eq_dec q nullval then emp else (DD gv q (VI_dd (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd) e) && valid_pointer q)))
             |-- (if eq_dec q nullval then emp else (DD gv q (VI_dd (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd) e) && valid_pointer q)) *
             @data_at ZCS Ews (tarray tuchar (Zlength (wd_bytes wd))) (zbytes (wd_bytes wd)) (offset_val (cap + 1) (Vptr bb ob))).
          { rewrite Hd1. destruct Hapi as [-> | [-> | ->]].
            - replace (VI_dr 2 q (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd) e) with (VM_dr2 (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd)) by reflexivity.
              rewrite VI_res2. change (2 =? 3) with false. cbv iota. cancel.
            - replace (VI_dr 3 q (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd) e) with (VM_dr3 q (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd) e) by reflexivity.
              rewrite VI_res3. change (3 =? 3) with true. cbv iota. rewrite if_false by (apply Hq3; reflexivity). cancel.
            - replace (VI_dr 4 q (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd) e) with (VM_drp (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd)) by reflexivity.
              rewrite VI_resp. change (4 =? 3) with false. cbv iota. cancel. }
          sep_apply Hfold.
          match goal with Hdf: VM_df st1 |- _ => rename Hdf into Hdf1 end.
          forward_call ((VB_W (Vptr bs os) (Zlength (ws_bytes ws)) (Vptr bb ob) cap), gv, Vptr bd od, st1, Ews, Ews, Vptr bb ob, cap, Ews, Vptr bs os, ws_bytes ws).
          { rewrite (proj1 (proj2 Hdf1)), set_res_nil. cancel. }
          { split; [apply VB_buf_ok_dst; [exact I | lia] | split; [apply VB_buf_ok_src; [exact I | rep_lia] | split]].
            - rewrite Hd1. unfold dict_buf_ok, VI_dr. destruct Hapi as [-> | [-> | ->]]; cbn; apply VB_dict_ptr_ok; first [exact I | lia | rep_lia | assumption].
            - split; [rewrite (proj1 (proj2 Hdf1)); constructor | apply (proj2 (proj2 Hdf1))]. }
          Intros vret. destruct vret as [[r out'] st']. cbn [fst snd] in *. rewrite mbuf_isptr by auto.
          rewrite (proj1 (proj2 Hdf1)), set_res_nil.
          sep_apply Hunfold. Intros.
          forward.
          Exists r R' st' out'. entailer!.
          api_init; match goal with Ha: after_decode (after_use st1) st' _ |- _ => rewrite Hd1 in Ha end.
          match goal with Ho: oneshot_dctx _ _ _ _ _, Hdf: VM_df st1 |- _ =>
            apply (oneshot_dctx_nil st1 _ _ _ _ (proj1 (proj2 Hdf))) in Ho;
            rewrite (VM_df_md st1 Hdf), Hd1 in Ho end.
          split; [| split; [| split]].
          1: api_init; match goal with Ha: after_decode (after_use st1) st' _ |- _ => rewrite (VM_after_ss _ _ _ Ha); assumption end.
          1: eapply VM_df_after; [apply VM_df_use; exact Hdf1 | eassumption].
          1: intros Hk. 1: assert (HR2: R = 2) by lia.
          1: assert (Ha2: api = 2) by (match goal with HR: R = 2 -> api = 2 |- _ => apply HR, HR2 end).
          1: match type of Hd1 with _ = Some ?dr =>
               api_init; match goal with Ha: after_decode (after_use st1) st' _, Hl: last_ok st1 _ |- _ =>
                 destruct (VM_after_dr2 dr st1 st' ltac:(rewrite Ha2; reflexivity) Hd1 Hl ltac:(rewrite Ha2; cbn; exact I) Ha) as (_ & Hd' & Hl') end end.
          1: rewrite Ha2 in Hd', Hl'. 1: split; [exact Hd' | exact Hl'].
          1: left. 1: match goal with Ho: oneshot_ok _ (dictref_model (Some (VI_dr api q ?P ?Bb ?E))) _ _ _ _ |- _ =>
              assert (Hm: dictref_model (Some (VI_dr api q P Bb E)) = Some (wd_model wd))
                by (destruct Hapi as [-> | [-> | ->]];
                    [apply VI_model2 | apply VI_model3 | apply VI_modelp; [| apply Hapi4; reflexivity]]; assumption);
              rewrite Hm in Ho; exact Ho end. }
        { forward. Exists r1 R' st1 out. entailer!.
          assert (Et: is_error_code r1 = true).
          { destruct (is_error_code r1) eqn:E; auto. }
          match goal with HE: is_error_code r1 = true -> _ /\ _ |- _ => destruct (HE Et) as [Er ER] end.
          split; [intros; lia | right; exact Er]. } } }
Qed.

Lemma VD_chk_ok {Espec: OracleKind} (gv: globals) (api: Z) (H: 0 <= api < 5) (wd: wdict) (H0: dict_facts wd) (H1: wdict_wf wd) (ws: wseries)
  (H2: series_facts (wdict_model (Some (wd, Ews))) ws) (H3: wseries_wf ws) (H4: readable_share Ews)
  (stv: reptype t_wstate) (H5: WDS wd stv) (Hfacts: series_facts (wd_model wd) ws)
  (Hbok: bytes_ok (ws_bytes ws)) (Hcok: bytes_ok (ws_content ws)) (Hnb: Zlength (ws_bytes ws) <= 2 ^ 19)
  (Hnc: Zlength (ws_content ws) <= 2 ^ 18) (Hnf: (1 <= Datatypes.length (ws_frames ws) <= 4)%nat)
  (Hdok: bytes_ok (wd_bytes wd)) (Hdl: 8 <= Zlength (wd_bytes wd) <= 2 ^ 12 + 2048) (Hda: dict_auto (wd_bytes wd) <> None)
  (Hdc: dm_content (wd_model wd) = wd_content wd) (Hdi: dm_id (wd_model wd) = wd_id wd) (Hdid: dict_id_of (wd_bytes wd) = wd_id wd)
  (Hraw: wd_formatted wd = false -> wd_model wd = dict_raw (wd_bytes wd) /\ wd_id wd = 0)
  (Hapi4: api = 4 -> wd_formatted wd = false /\ Zlength (ws_frames ws) = 1 /\ wi_skippable (hd winfo0 (ws_frames ws)) = false)
  (cap: Z) (H6: 0 <= cap <= Zlength (ws_content ws) + 16) (bs: block) (os: ptrofs) (PNsrc: is_pointer_or_null (Vptr bs os))
  (bb: block) (ob: ptrofs) (bd: block) (od: ptrofs) (PNdctx: is_pointer_or_null (Vptr bd od))
  (Hvp: forall (P: mpred) (q0: val), P && valid_pointer q0 |-- P)
  (Hs: Vptr bs os <> nullval) (Hps: isptr (Vptr bs os)) (Hb: Vptr bb ob <> nullval) (Hpb: isptr (Vptr bb ob))
  (Hd: Vptr bd od <> nullval) (Hpd: isptr (Vptr bd od)) (H7 H8 H9 H10: true = true)
  (Hrr: 1 <= VM_rnd api <= 2) (H11: 0 < VM_rnd api)
  (Hfb: field_compatible (tarray tuchar (cap + 1 + Zlength (wd_bytes wd))) [] (Vptr bb ob)) (q: val) (e: ddict_st) (rnd: Z)
  (H12: q = nullval /\ rnd = VM_rnd api /\ ((api =? 1) || (api =? 3))%bool = false \/
        ((api =? 1) || (api =? 3))%bool = true /\ (q = nullval /\ rnd = 0 \/ isptr q /\ rnd = 1))
  (Hfs: field_compatible (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws)))) [] (Vptr bs os))
  (k R: Z) (st: dctx_st) (out: list val) (H13: 0 <= k <= R) (H14: R <= 2) (H15: R = 2 -> api = 2)
  (H16: 0 < R -> ((api =? 1) || (api =? 3))%bool = true -> isptr q) (H17: ((api =? 1) || (api =? 3))%bool = false -> q = nullval)
  (H18: Zlength out = cap) (H19: dc_ss st = ss_init) (H19d: VM_df st) (H20: k = 0 -> st = dctx_init)
  (H21: 0 < k < R -> dc_dict st = Some (VM_dr2 (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd)) /\
                     last_ok st (VM_dr2 (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd)))
  (H22: k < R)
  (r R': Z) (st': dctx_st) (out': list val) (H23: 0 <= r <= Int64.max_unsigned) (H24: k + 1 <= R' <= R)
  (H25: Zlength out' = cap) (H26: dc_ss st' = ss_init) (H26d: VM_df st')
  (H27: 0 < k + 1 < R' -> dc_dict st' = Some (VM_dr2 (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd)) /\
                          last_ok st' (VM_dr2 (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd)))
  (H28: VM_round (wd_model wd) (ws_bytes ws) cap r out') :
  semax (func_tycontext f_main Vprog VD_G1 nil)
    (PROP () LOCAL (temp _r (Vlong (Int64.repr r)); temp _k (Vint (Int.repr k)); temp _rounds (Vint (Int.repr R')); temp _ddict q; temp _dctx (Vptr bd od);
             temp _dst (Vptr bb ob); temp _buf (Vptr bb ob); temp _dict (offset_val (cap + 1) (Vptr bb ob)); temp _src (Vptr bs os); temp _cap (Vlong (Int64.repr cap));
             temp _api (Vint (Int.repr api)); gvars gv)
        SEP (mem_mgr gv; zstd_globals gv; DC gv (Vptr bd od) st';
             (if eq_dec q nullval then emp else (DD gv q (VI_dd (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd) e) && valid_pointer q));
             @data_at ZCS Ews (tarray tuchar (Zlength (wd_bytes wd))) (zbytes (wd_bytes wd)) (offset_val (cap + 1) (Vptr bb ob));
             pws_pred (VB_W (Vptr bs os) (Zlength (ws_bytes ws)) (Vptr bb ob) cap); @data_at ZCS Ews (tarray tuchar cap) out' (Vptr bb ob);
             @data_at ZCS Ews (tarray tuchar (Zlength (ws_bytes ws))) (zbytes (ws_bytes ws)) (Vptr bs os);
             @malloc_token HCS Ews (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws)))) (Vptr bs os);
             @malloc_token HCS Ews (tarray tuchar (cap + 1 + Zlength (wd_bytes wd))) (Vptr bb ob);
             VB_sr_rest ws (gv _x_valid_dict__sr);
             @field_at HCS Ews t_wseries (DOT _n) (vl (Zlength (ws_bytes ws))) (gv _x_valid_dict__sr);
             @field_at HCS Ews t_wseries (DOT _content) (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws))) (gv _x_valid_dict__sr);
             @field_at HCS Ews t_wseries (DOT _content_n) (vl (Zlength (ws_content ws))) (gv _x_valid_dict__sr);
             @field_at HCS Ews t_wdict (DOT _n) (vl (Zlength (wd_bytes wd))) (gv _x_valid_dict__wd); TT))
    (Ssequence VD_chk_s VD_incr_s)
    (normal_ret_assert (EX k: Z, EX R: Z, EX st: dctx_st, EX out: list val,
    PROP (0 <= k <= R; R <= 2; (R = 2 -> api = 2); (0 < R -> orb (api =? 1) (api =? 3) = true -> isptr q);
          (orb (api =? 1) (api =? 3) = false -> q = nullval); Zlength out = cap; dc_ss st = ss_init; VM_df st;
          (k = 0 -> st = dctx_init); (0 < k < R -> dc_dict st = Some (VM_dr2 (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd)) /\ last_ok st (VM_dr2 (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd))))
    LOCAL (temp _k (Vint (Int.repr k)); temp _rounds (Vint (Int.repr R)); temp _ddict q; temp _dctx (Vptr bd od);
         temp _dst (Vptr bb ob); temp _buf (Vptr bb ob); temp _dict (offset_val (cap + 1) (Vptr bb ob)); temp _src (Vptr bs os); temp _cap (Vlong (Int64.repr cap));
         temp _api (Vint (Int.repr api)); gvars gv)
    SEP (mem_mgr gv; zstd_globals gv; DC gv (Vptr bd od) st;
         (if eq_dec q nullval then emp else (DD gv q (VI_dd (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd) e) && valid_pointer q));
         @data_at ZCS Ews (tarray tuchar (Zlength (wd_bytes wd))) (zbytes (wd_bytes wd)) (offset_val (cap + 1) (Vptr bb ob));
         pws_pred (VB_W (Vptr bs os) (Zlength (ws_bytes ws)) (Vptr bb ob) cap); @data_at ZCS Ews (tarray tuchar cap) out (Vptr bb ob);
         @data_at ZCS Ews (tarray tuchar (Zlength (ws_bytes ws))) (zbytes (ws_bytes ws)) (Vptr bs os);
         @malloc_token HCS Ews (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws)))) (Vptr bs os);
         @malloc_token HCS Ews (tarray tuchar (cap + 1 + Zlength (wd_bytes wd))) (Vptr bb ob);
         VB_sr_rest ws (gv _x_valid_dict__sr);
         @field_at HCS Ews t_wseries (DOT _n) (vl (Zlength (ws_bytes ws))) (gv _x_valid_dict__sr);
         @field_at HCS Ews t_wseries (DOT _content) (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws))) (gv _x_valid_dict__sr);
         @field_at HCS Ews t_wseries (DOT _content_n) (vl (Zlength (ws_content ws))) (gv _x_valid_dict__sr);
         @field_at HCS Ews t_wdict (DOT _n) (vl (Zlength (wd_bytes wd))) (gv _x_valid_dict__wd); TT))%assert).
Proof.
  simplify_func_tycontext. unfold VD_chk_s, VD_incr_s.
    forward_call r.
    forward_if (PROP ()
    LOCAL (temp _k (Vint (Int.repr k)); temp _rounds (Vint (Int.repr R')); temp _ddict q; temp _dctx (Vptr bd od);
         temp _dst (Vptr bb ob); temp _buf (Vptr bb ob); temp _dict (offset_val (cap + 1) (Vptr bb ob)); temp _src (Vptr bs os); temp _cap (Vlong (Int64.repr cap));
         temp _api (Vint (Int.repr api)); gvars gv)
    SEP (mem_mgr gv; zstd_globals gv; DC gv (Vptr bd od) st';
         (if eq_dec q nullval then emp else (DD gv q (VI_dd (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd) e) && valid_pointer q));
         @data_at ZCS Ews (tarray tuchar (Zlength (wd_bytes wd))) (zbytes (wd_bytes wd)) (offset_val (cap + 1) (Vptr bb ob));
         pws_pred (VB_W (Vptr bs os) (Zlength (ws_bytes ws)) (Vptr bb ob) cap); @data_at ZCS Ews (tarray tuchar cap) out' (Vptr bb ob);
         @data_at ZCS Ews (tarray tuchar (Zlength (ws_bytes ws))) (zbytes (ws_bytes ws)) (Vptr bs os);
         @malloc_token HCS Ews (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws)))) (Vptr bs os);
         @malloc_token HCS Ews (tarray tuchar (cap + 1 + Zlength (wd_bytes wd))) (Vptr bb ob);
         VB_sr_rest ws (gv _x_valid_dict__sr);
         @field_at HCS Ews t_wseries (DOT _n) (vl (Zlength (ws_bytes ws))) (gv _x_valid_dict__sr);
         @field_at HCS Ews t_wseries (DOT _content) (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws))) (gv _x_valid_dict__sr);
         @field_at HCS Ews t_wseries (DOT _content_n) (vl (Zlength (ws_content ws))) (gv _x_valid_dict__sr);
         @field_at HCS Ews t_wdict (DOT _n) (vl (Zlength (wd_bytes wd))) (gv _x_valid_dict__wd); TT))%assert.
    { (* success: the content *)
      assert (He: is_error_code r = false) by (destruct (is_error_code r); auto; discriminate).
      match goal with Hr: VM_round _ _ _ _ _ |- _ =>
        destruct (VM_round_ok (wd_model wd) ws cap r out' Hfacts H3 Hr He) as [Er Esub] end.
      assert (Hrc: r <= cap).
      { match goal with Hr: VM_round _ _ _ _ _ |- _ => destruct Hr as [[Hle _] | Hm];
          [apply Hle, He | subst r; pose proof VM_err64 as (E & _); congruence] end. }
      forward.
      forward_call (Int.one).
      { entailer!. rewrite Int64.eq_true. reflexivity. }
      forward.
      forward_loop (EX i: Z, PROP (0 <= i <= r)
    LOCAL (temp _i (Vlong (Int64.repr i)); temp _r (Vlong (Int64.repr r)); temp _k (Vint (Int.repr k)); temp _rounds (Vint (Int.repr R')); temp _ddict q; temp _dctx (Vptr bd od);
         temp _dst (Vptr bb ob); temp _buf (Vptr bb ob); temp _dict (offset_val (cap + 1) (Vptr bb ob)); temp _src (Vptr bs os); temp _cap (Vlong (Int64.repr cap));
         temp _api (Vint (Int.repr api)); gvars gv)
    SEP (mem_mgr gv; zstd_globals gv; DC gv (Vptr bd od) st';
         (if eq_dec q nullval then emp else (DD gv q (VI_dd (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd) e) && valid_pointer q));
         @data_at ZCS Ews (tarray tuchar (Zlength (wd_bytes wd))) (zbytes (wd_bytes wd)) (offset_val (cap + 1) (Vptr bb ob));
         pws_pred (VB_W (Vptr bs os) (Zlength (ws_bytes ws)) (Vptr bb ob) cap); @data_at ZCS Ews (tarray tuchar cap) out' (Vptr bb ob);
         @data_at ZCS Ews (tarray tuchar (Zlength (ws_bytes ws))) (zbytes (ws_bytes ws)) (Vptr bs os);
         @malloc_token HCS Ews (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws)))) (Vptr bs os);
         @malloc_token HCS Ews (tarray tuchar (cap + 1 + Zlength (wd_bytes wd))) (Vptr bb ob);
         VB_sr_rest ws (gv _x_valid_dict__sr);
         @field_at HCS Ews t_wseries (DOT _n) (vl (Zlength (ws_bytes ws))) (gv _x_valid_dict__sr);
         @field_at HCS Ews t_wseries (DOT _content) (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws))) (gv _x_valid_dict__sr);
         @field_at HCS Ews t_wseries (DOT _content_n) (vl (Zlength (ws_content ws))) (gv _x_valid_dict__sr);
         @field_at HCS Ews t_wdict (DOT _n) (vl (Zlength (wd_bytes wd))) (gv _x_valid_dict__wd); TT))%assert
        break: (PROP ()
    LOCAL (temp _k (Vint (Int.repr k)); temp _rounds (Vint (Int.repr R')); temp _ddict q; temp _dctx (Vptr bd od);
         temp _dst (Vptr bb ob); temp _buf (Vptr bb ob); temp _dict (offset_val (cap + 1) (Vptr bb ob)); temp _src (Vptr bs os); temp _cap (Vlong (Int64.repr cap));
         temp _api (Vint (Int.repr api)); gvars gv)
    SEP (mem_mgr gv; zstd_globals gv; DC gv (Vptr bd od) st';
         (if eq_dec q nullval then emp else (DD gv q (VI_dd (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd) e) && valid_pointer q));
         @data_at ZCS Ews (tarray tuchar (Zlength (wd_bytes wd))) (zbytes (wd_bytes wd)) (offset_val (cap + 1) (Vptr bb ob));
         pws_pred (VB_W (Vptr bs os) (Zlength (ws_bytes ws)) (Vptr bb ob) cap); @data_at ZCS Ews (tarray tuchar cap) out' (Vptr bb ob);
         @data_at ZCS Ews (tarray tuchar (Zlength (ws_bytes ws))) (zbytes (ws_bytes ws)) (Vptr bs os);
         @malloc_token HCS Ews (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws)))) (Vptr bs os);
         @malloc_token HCS Ews (tarray tuchar (cap + 1 + Zlength (wd_bytes wd))) (Vptr bb ob);
         VB_sr_rest ws (gv _x_valid_dict__sr);
         @field_at HCS Ews t_wseries (DOT _n) (vl (Zlength (ws_bytes ws))) (gv _x_valid_dict__sr);
         @field_at HCS Ews t_wseries (DOT _content) (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws))) (gv _x_valid_dict__sr);
         @field_at HCS Ews t_wseries (DOT _content_n) (vl (Zlength (ws_content ws))) (gv _x_valid_dict__sr);
         @field_at HCS Ews t_wdict (DOT _n) (vl (Zlength (wd_bytes wd))) (gv _x_valid_dict__wd); TT))%assert.
      { Exists 0. entailer!. }
      { Intros i.
        forward_if.
        2: { forward. entailer!. }
        assert (Hi1: Znth i out' = Vint (Int.repr (Znth i (ws_content ws)))) by (apply (VB_out_at (ws_content ws) r out' i); auto; lia).
        assert (Hi2: Znth i (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws))) =
                     Vint (Int.repr (Znth i (ws_content ws)))) by (apply VB_content_at; lia).
        assert (Hbyte: 0 <= Znth i (ws_content ws) <= Byte.max_unsigned).
        { pose proof (proj1 (Forall_Znth _ _) Hcok i ltac:(lia)) as Hz. unfold is_byte in Hz. rep_lia. }
        rewrite (VB_cs ZCS HCS Ews cap out' (Vptr bb ob)).
        forward.
        1: { entailer!.
             all: try (replace (@Znth val Vundef i out') with (Vint (Int.repr (Znth i (ws_content ws)))) by (rewrite <- Hi1; reflexivity);
                       simpl; rewrite Int.unsigned_repr by rep_lia; rep_lia).
             all: lia. }
        assert_PROP (field_compatible t_wseries (DOT _content) (gv _x_valid_dict__sr)) as Hfcc by entailer!.
        rewrite (VI_content_split ws (gv _x_valid_dict__sr) Hnc Hfcc). Intros.
        assert_PROP (force_val (sem_add_ptr_long tuchar (offset_val 524296 (gv _x_valid_dict__sr)) (Vlong (Int64.repr i))) =
          field_address (tarray tuchar (Zlength (ws_content ws))) (SUB i) (field_address t_wseries (DOT _content) (gv _x_valid_dict__sr))) as Ea.
        { entailer!. rewrite (field_address_offset t_wseries) by auto.
          rewrite arr_field_address by (auto; try lia; rewrite field_address_offset in *; auto).
          simpl; rewrite offset_offset_val; f_equal; lia. }
        forward.
        1: { entailer!. apply Hbyte. }
        sep_apply (VI_content_fold ws (gv _x_valid_dict__sr) Hnc Hfcc).
        forward_call (Int.one).
        { entailer!. replace (@Znth val Vundef i out') with (Vint (Int.repr (Znth i (ws_content ws)))) by (rewrite <- Hi1; reflexivity).
          simpl. rewrite Int.eq_true. reflexivity. }
        forward.
        Exists (i + 1). rewrite (VB_cs HCS ZCS Ews cap out' (Vptr bb ob)).
        entailer!. } }
    { (* an error: memory_allocation when the capacity holds the content and the frames are within range *)
      assert (He: is_error_code r = true)
        by (destruct (is_error_code r); auto; match goal with H: Int.repr 0 <> Int.zero |- _ => contradiction H; reflexivity end).
      forward.
      forward_if (PROP ()
    LOCAL (temp _x_valid_dict__t'23 (Vint (Int.repr (if andb (Zlength (ws_content ws) <=? cap) (within_oneshot_b (ws_frames ws)) then 1 else 0))); temp _r (Vlong (Int64.repr r)); temp _k (Vint (Int.repr k)); temp _rounds (Vint (Int.repr R')); temp _ddict q; temp _dctx (Vptr bd od);
         temp _dst (Vptr bb ob); temp _buf (Vptr bb ob); temp _dict (offset_val (cap + 1) (Vptr bb ob)); temp _src (Vptr bs os); temp _cap (Vlong (Int64.repr cap));
         temp _api (Vint (Int.repr api)); gvars gv)
    SEP (mem_mgr gv; zstd_globals gv; DC gv (Vptr bd od) st';
         (if eq_dec q nullval then emp else (DD gv q (VI_dd (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd) e) && valid_pointer q));
         @data_at ZCS Ews (tarray tuchar (Zlength (wd_bytes wd))) (zbytes (wd_bytes wd)) (offset_val (cap + 1) (Vptr bb ob));
         pws_pred (VB_W (Vptr bs os) (Zlength (ws_bytes ws)) (Vptr bb ob) cap); @data_at ZCS Ews (tarray tuchar cap) out' (Vptr bb ob);
         @data_at ZCS Ews (tarray tuchar (Zlength (ws_bytes ws))) (zbytes (ws_bytes ws)) (Vptr bs os);
         @malloc_token HCS Ews (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws)))) (Vptr bs os);
         @malloc_token HCS Ews (tarray tuchar (cap + 1 + Zlength (wd_bytes wd))) (Vptr bb ob);
         VB_sr_rest ws (gv _x_valid_dict__sr);
         @field_at HCS Ews t_wseries (DOT _n) (vl (Zlength (ws_bytes ws))) (gv _x_valid_dict__sr);
         @field_at HCS Ews t_wseries (DOT _content) (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws))) (gv _x_valid_dict__sr);
         @field_at HCS Ews t_wseries (DOT _content_n) (vl (Zlength (ws_content ws))) (gv _x_valid_dict__sr);
         @field_at HCS Ews t_wdict (DOT _n) (vl (Zlength (wd_bytes wd))) (gv _x_valid_dict__wd); TT))%assert.
      { (* within_oneshot *)
        sep_apply (VB_ws_fold ws (gv _x_valid_dict__sr) Hnb).
        forward_call (Ews, gv _x_valid_dict__sr, ws).
        forward.
        sep_apply (VB_ws_unfold ws (gv _x_valid_dict__sr) Hnb). Intros.
        entailer!.
        rewrite (proj2 (Z.leb_le _ _)) by lia. destruct (within_oneshot_b _); reflexivity. }
      { forward. entailer!. rewrite (proj2 (Z.leb_gt _ _)) by lia. reflexivity. }
      forward_if (PROP ()
    LOCAL (temp _k (Vint (Int.repr k)); temp _rounds (Vint (Int.repr R')); temp _ddict q; temp _dctx (Vptr bd od);
         temp _dst (Vptr bb ob); temp _buf (Vptr bb ob); temp _dict (offset_val (cap + 1) (Vptr bb ob)); temp _src (Vptr bs os); temp _cap (Vlong (Int64.repr cap));
         temp _api (Vint (Int.repr api)); gvars gv)
    SEP (mem_mgr gv; zstd_globals gv; DC gv (Vptr bd od) st';
         (if eq_dec q nullval then emp else (DD gv q (VI_dd (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd) e) && valid_pointer q));
         @data_at ZCS Ews (tarray tuchar (Zlength (wd_bytes wd))) (zbytes (wd_bytes wd)) (offset_val (cap + 1) (Vptr bb ob));
         pws_pred (VB_W (Vptr bs os) (Zlength (ws_bytes ws)) (Vptr bb ob) cap); @data_at ZCS Ews (tarray tuchar cap) out' (Vptr bb ob);
         @data_at ZCS Ews (tarray tuchar (Zlength (ws_bytes ws))) (zbytes (ws_bytes ws)) (Vptr bs os);
         @malloc_token HCS Ews (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws)))) (Vptr bs os);
         @malloc_token HCS Ews (tarray tuchar (cap + 1 + Zlength (wd_bytes wd))) (Vptr bb ob);
         VB_sr_rest ws (gv _x_valid_dict__sr);
         @field_at HCS Ews t_wseries (DOT _n) (vl (Zlength (ws_bytes ws))) (gv _x_valid_dict__sr);
         @field_at HCS Ews t_wseries (DOT _content) (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws))) (gv _x_valid_dict__sr);
         @field_at HCS Ews t_wseries (DOT _content_n) (vl (Zlength (ws_content ws))) (gv _x_valid_dict__sr);
         @field_at HCS Ews t_wdict (DOT _n) (vl (Zlength (wd_bytes wd))) (gv _x_valid_dict__wd); TT))%assert.
      { assert (Hw: Zlength (ws_content ws) <= cap /\ within_oneshot_b (ws_frames ws) = true).
        { match goal with H: Int.repr (if (?b1 && ?b2)%bool then 1 else 0) <> Int.zero |- _ =>
            destruct (b1 && b2)%bool eqn:Eb; [|contradiction H; reflexivity] end.
          apply andb_prop in Eb as [E1 E2]. apply Z.leb_le in E1. auto. }
        destruct Hw as [Hw1 Hw2].
        assert (Er: error_of r = ZSTD_error_memory_allocation).
        { match goal with Hr: VM_round _ _ _ _ _ |- _ => exact (VM_round_err (wd_model wd) ws cap r out' Hfacts H3 Hr He Hw1 Hw2) end. }
        forward_call r.
        forward_call (Int.one).
        { entailer!. rewrite Er. reflexivity. }
        entailer!. }
      { forward. entailer!. } }
    forward.
    Exists (k + 1) R' st' out'.
    entailer!.
    all: try (match goal with |- isptr ?x => match goal with HQ: 0 < ?RR -> _ -> isptr x |- _ => apply HQ; [lia | assumption] end end).
    all: rewrite (VB_cs HCS ZCS Ews (Zlength (wd_bytes wd))), (VB_cs HCS ZCS Ews (Zlength (ws_bytes ws))); apply derives_refl.
  Unshelve. all: apply VB_cce.
Qed.

(* the runs where an allocation failed (rounds = 0): one lemma per case *)
Definition VD_rest_s : statement := ltac:(
  let b := eval cbv delta [f_main fn_body] beta iota in (fn_body f_main) in
  lazymatch b with context [Ssequence (Ssequence (Scall (Some ?t) (Evar _ZSTD_createDCtx ?ty) nil) (Sset _dctx ?e)) ?rest] =>
    exact rest end).

Lemma VD_zero1 {Espec: OracleKind} (gv: globals) (api: Z) (H: 0 <= api < 5) (wd: wdict) (H0: dict_facts wd) (H1: wdict_wf wd) (ws: wseries)
  (H2: series_facts (wdict_model (Some (wd, Ews))) ws) (H3: wseries_wf ws) (H4: readable_share Ews)
  (stv: reptype t_wstate) (H5: WDS wd stv) (Hfacts: series_facts (wd_model wd) ws)
  (Hbok: bytes_ok (ws_bytes ws)) (Hcok: bytes_ok (ws_content ws)) (Hnb: Zlength (ws_bytes ws) <= 2 ^ 19)
  (Hnc: Zlength (ws_content ws) <= 2 ^ 18) (Hnf: (1 <= Datatypes.length (ws_frames ws) <= 4)%nat)
  (Hdok: bytes_ok (wd_bytes wd)) (Hdl: 8 <= Zlength (wd_bytes wd) <= 2 ^ 12 + 2048) (Hda: dict_auto (wd_bytes wd) <> None)
  (Hdc: dm_content (wd_model wd) = wd_content wd) (Hdi: dm_id (wd_model wd) = wd_id wd) (Hdid: dict_id_of (wd_bytes wd) = wd_id wd)
  (Hraw: wd_formatted wd = false -> wd_model wd = dict_raw (wd_bytes wd) /\ wd_id wd = 0)
  (Hapi4: api = 4 -> wd_formatted wd = false /\ Zlength (ws_frames ws) = 1 /\ wi_skippable (hd winfo0 (ws_frames ws)) = false)
  (cap: Z) (H6: 0 <= cap <= Zlength (ws_content ws) + 16) (src: val) (PNsrc: is_pointer_or_null src) (buf dctx: val)
  (PNdctx: is_pointer_or_null dctx) (Hvp: forall (P: mpred) (q: val), P && valid_pointer q |-- P)
  (Hs: src = nullval) (Hb: buf = nullval) (Hd: dctx = nullval) :
  semax (func_tycontext f_main Vprog VD_G1 nil)
    (PROP () LOCAL (temp _dctx dctx; temp _buf buf; temp _src src; temp _cap (Vlong (Int64.repr cap));
       temp _ddict (Vlong (Int64.repr (Int.signed (Int.repr 0)))); temp _api (Vint (Int.repr api)); gvars gv)
     SEP (mem_mgr gv; zstd_globals gv;
       if eq_dec dctx nullval then emp else DC gv dctx dctx_init && valid_pointer dctx;
       if eq_dec buf nullval then emp
       else malloc_token Ews (tarray tuchar (cap + 1 + Zlength (wd_bytes wd))) buf *
            data_at_ Ews (tarray tuchar (cap + 1 + Zlength (wd_bytes wd))) buf;
       data_at Ews (tarray tuchar (Zlength (ws_bytes ws))) (zbytes (ws_bytes ws))
         (field_address t_wseries (DOT _bytes) (gv _x_valid_dict__sr));
       if eq_dec src nullval then emp
       else malloc_token Ews (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws)))) src *
            data_at Ews (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws))))
              (zbytes (ws_bytes ws) ++ Zrepeat Vundef (Z.max 1 (Zlength (ws_bytes ws)) - Zlength (ws_bytes ws))) src;
       data_at Ews (tarray tuchar (2 ^ 19 - Zlength (ws_bytes ws))) (Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength (ws_bytes ws)))
         (field_address0 (tarray tuchar (2 ^ 19)) (SUB Zlength (ws_bytes ws)) (field_address t_wseries (DOT _bytes) (gv _x_valid_dict__sr)));
       @field_at HCS Ews t_wseries (DOT _f) (map winfo_val (ws_frames ws) ++ Zrepeat (winfo_val winfo0) (4 - Zlength (ws_frames ws)))
         (gv _x_valid_dict__sr);
       field_at Ews t_wseries (DOT _nframes) (vu (Zlength (ws_frames ws))) (gv _x_valid_dict__sr);
       spacer Ews 786932 786936 (gv _x_valid_dict__sr);
       field_at Ews t_wseries (DOT _n) (vl (Zlength (ws_bytes ws))) (gv _x_valid_dict__sr);
       field_at Ews t_wseries (DOT _content) (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws)))
         (gv _x_valid_dict__sr);
       field_at Ews t_wseries (DOT _content_n) (vl (Zlength (ws_content ws))) (gv _x_valid_dict__sr);
       field_at Ews t_wdict (DOT _bytes) (zbytes (wd_bytes wd) ++ Zrepeat (Vint Int.zero) (6144 - Zlength (wd_bytes wd)))
         (gv _x_valid_dict__wd);
       field_at Ews t_wdict (DOT _n) (vl (Zlength (wd_bytes wd))) (gv _x_valid_dict__wd);
       field_at Ews t_wdict (DOT _formatted) (vb (wd_formatted wd)) (gv _x_valid_dict__wd); TT; WG gv; TT; has_ext tt))
    (Ssequence VD_rest_s (Sreturn (Some (Econst_int (Int.repr 0) tint))))
    (frame_ret_assert (function_body_ret_assert tint (PROP () RETURN () SEP (TT))) (stackframe_of f_main)).
Proof.
  simplify_func_tycontext. unfold VD_rest_s. abbreviate_semax.
  subst src buf dctx.
  (VD_front; forward_call (gv, nullval, @None ddict_st); VD_side; forward_call (gv, nullval, @None dctx_st); VD_side; forward_call (tarray tuchar 1, nullval, gv); VD_side; forward_call (tarray tuchar 1, nullval, gv); VD_side; forward).
Qed.

Lemma VD_zero2 {Espec: OracleKind} (gv: globals) (api: Z) (H: 0 <= api < 5) (wd: wdict) (H0: dict_facts wd) (H1: wdict_wf wd) (ws: wseries)
  (H2: series_facts (wdict_model (Some (wd, Ews))) ws) (H3: wseries_wf ws) (H4: readable_share Ews)
  (stv: reptype t_wstate) (H5: WDS wd stv) (Hfacts: series_facts (wd_model wd) ws)
  (Hbok: bytes_ok (ws_bytes ws)) (Hcok: bytes_ok (ws_content ws)) (Hnb: Zlength (ws_bytes ws) <= 2 ^ 19)
  (Hnc: Zlength (ws_content ws) <= 2 ^ 18) (Hnf: (1 <= Datatypes.length (ws_frames ws) <= 4)%nat)
  (Hdok: bytes_ok (wd_bytes wd)) (Hdl: 8 <= Zlength (wd_bytes wd) <= 2 ^ 12 + 2048) (Hda: dict_auto (wd_bytes wd) <> None)
  (Hdc: dm_content (wd_model wd) = wd_content wd) (Hdi: dm_id (wd_model wd) = wd_id wd) (Hdid: dict_id_of (wd_bytes wd) = wd_id wd)
  (Hraw: wd_formatted wd = false -> wd_model wd = dict_raw (wd_bytes wd) /\ wd_id wd = 0)
  (Hapi4: api = 4 -> wd_formatted wd = false /\ Zlength (ws_frames ws) = 1 /\ wi_skippable (hd winfo0 (ws_frames ws)) = false)
  (cap: Z) (H6: 0 <= cap <= Zlength (ws_content ws) + 16) (src: val) (PNsrc: is_pointer_or_null src) (buf dctx: val)
  (PNdctx: is_pointer_or_null dctx) (Hvp: forall (P: mpred) (q: val), P && valid_pointer q |-- P)
  (Hs: src = nullval) (Hb: buf = nullval) (Hd: dctx <> nullval) :
  semax (func_tycontext f_main Vprog VD_G1 nil)
    (PROP () LOCAL (temp _dctx dctx; temp _buf buf; temp _src src; temp _cap (Vlong (Int64.repr cap));
       temp _ddict (Vlong (Int64.repr (Int.signed (Int.repr 0)))); temp _api (Vint (Int.repr api)); gvars gv)
     SEP (mem_mgr gv; zstd_globals gv;
       if eq_dec dctx nullval then emp else DC gv dctx dctx_init && valid_pointer dctx;
       if eq_dec buf nullval then emp
       else malloc_token Ews (tarray tuchar (cap + 1 + Zlength (wd_bytes wd))) buf *
            data_at_ Ews (tarray tuchar (cap + 1 + Zlength (wd_bytes wd))) buf;
       data_at Ews (tarray tuchar (Zlength (ws_bytes ws))) (zbytes (ws_bytes ws))
         (field_address t_wseries (DOT _bytes) (gv _x_valid_dict__sr));
       if eq_dec src nullval then emp
       else malloc_token Ews (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws)))) src *
            data_at Ews (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws))))
              (zbytes (ws_bytes ws) ++ Zrepeat Vundef (Z.max 1 (Zlength (ws_bytes ws)) - Zlength (ws_bytes ws))) src;
       data_at Ews (tarray tuchar (2 ^ 19 - Zlength (ws_bytes ws))) (Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength (ws_bytes ws)))
         (field_address0 (tarray tuchar (2 ^ 19)) (SUB Zlength (ws_bytes ws)) (field_address t_wseries (DOT _bytes) (gv _x_valid_dict__sr)));
       @field_at HCS Ews t_wseries (DOT _f) (map winfo_val (ws_frames ws) ++ Zrepeat (winfo_val winfo0) (4 - Zlength (ws_frames ws)))
         (gv _x_valid_dict__sr);
       field_at Ews t_wseries (DOT _nframes) (vu (Zlength (ws_frames ws))) (gv _x_valid_dict__sr);
       spacer Ews 786932 786936 (gv _x_valid_dict__sr);
       field_at Ews t_wseries (DOT _n) (vl (Zlength (ws_bytes ws))) (gv _x_valid_dict__sr);
       field_at Ews t_wseries (DOT _content) (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws)))
         (gv _x_valid_dict__sr);
       field_at Ews t_wseries (DOT _content_n) (vl (Zlength (ws_content ws))) (gv _x_valid_dict__sr);
       field_at Ews t_wdict (DOT _bytes) (zbytes (wd_bytes wd) ++ Zrepeat (Vint Int.zero) (6144 - Zlength (wd_bytes wd)))
         (gv _x_valid_dict__wd);
       field_at Ews t_wdict (DOT _n) (vl (Zlength (wd_bytes wd))) (gv _x_valid_dict__wd);
       field_at Ews t_wdict (DOT _formatted) (vb (wd_formatted wd)) (gv _x_valid_dict__wd); TT; WG gv; TT; has_ext tt))
    (Ssequence VD_rest_s (Sreturn (Some (Econst_int (Int.repr 0) tint))))
    (frame_ret_assert (function_body_ret_assert tint (PROP () RETURN () SEP (TT))) (stackframe_of f_main)).
Proof.
  simplify_func_tycontext. unfold VD_rest_s. abbreviate_semax.
  subst src buf.
  assert (Hpd: isptr dctx) by (destruct dctx; simpl in *; try contradiction; auto; subst; contradiction).
  destruct dctx as [| | | | | bd od]; try contradiction.
  (VD_front; forward_call (gv, nullval, @None ddict_st); VD_side; sep_apply (Hvp (DC gv (Vptr bd od) dctx_init) (Vptr bd od)); forward_call (gv, Vptr bd od, Some dctx_init); VD_side; forward_call (tarray tuchar 1, nullval, gv); VD_side; forward_call (tarray tuchar 1, nullval, gv); VD_side; forward).
Qed.

Lemma VD_zero3 {Espec: OracleKind} (gv: globals) (api: Z) (H: 0 <= api < 5) (wd: wdict) (H0: dict_facts wd) (H1: wdict_wf wd) (ws: wseries)
  (H2: series_facts (wdict_model (Some (wd, Ews))) ws) (H3: wseries_wf ws) (H4: readable_share Ews)
  (stv: reptype t_wstate) (H5: WDS wd stv) (Hfacts: series_facts (wd_model wd) ws)
  (Hbok: bytes_ok (ws_bytes ws)) (Hcok: bytes_ok (ws_content ws)) (Hnb: Zlength (ws_bytes ws) <= 2 ^ 19)
  (Hnc: Zlength (ws_content ws) <= 2 ^ 18) (Hnf: (1 <= Datatypes.length (ws_frames ws) <= 4)%nat)
  (Hdok: bytes_ok (wd_bytes wd)) (Hdl: 8 <= Zlength (wd_bytes wd) <= 2 ^ 12 + 2048) (Hda: dict_auto (wd_bytes wd) <> None)
  (Hdc: dm_content (wd_model wd) = wd_content wd) (Hdi: dm_id (wd_model wd) = wd_id wd) (Hdid: dict_id_of (wd_bytes wd) = wd_id wd)
  (Hraw: wd_formatted wd = false -> wd_model wd = dict_raw (wd_bytes wd) /\ wd_id wd = 0)
  (Hapi4: api = 4 -> wd_formatted wd = false /\ Zlength (ws_frames ws) = 1 /\ wi_skippable (hd winfo0 (ws_frames ws)) = false)
  (cap: Z) (H6: 0 <= cap <= Zlength (ws_content ws) + 16) (src: val) (PNsrc: is_pointer_or_null src) (buf dctx: val)
  (PNdctx: is_pointer_or_null dctx) (Hvp: forall (P: mpred) (q: val), P && valid_pointer q |-- P)
  (Hs: src = nullval) (Hb: buf <> nullval) (Hd: dctx = nullval) :
  semax (func_tycontext f_main Vprog VD_G1 nil)
    (PROP () LOCAL (temp _dctx dctx; temp _buf buf; temp _src src; temp _cap (Vlong (Int64.repr cap));
       temp _ddict (Vlong (Int64.repr (Int.signed (Int.repr 0)))); temp _api (Vint (Int.repr api)); gvars gv)
     SEP (mem_mgr gv; zstd_globals gv;
       if eq_dec dctx nullval then emp else DC gv dctx dctx_init && valid_pointer dctx;
       if eq_dec buf nullval then emp
       else malloc_token Ews (tarray tuchar (cap + 1 + Zlength (wd_bytes wd))) buf *
            data_at_ Ews (tarray tuchar (cap + 1 + Zlength (wd_bytes wd))) buf;
       data_at Ews (tarray tuchar (Zlength (ws_bytes ws))) (zbytes (ws_bytes ws))
         (field_address t_wseries (DOT _bytes) (gv _x_valid_dict__sr));
       if eq_dec src nullval then emp
       else malloc_token Ews (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws)))) src *
            data_at Ews (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws))))
              (zbytes (ws_bytes ws) ++ Zrepeat Vundef (Z.max 1 (Zlength (ws_bytes ws)) - Zlength (ws_bytes ws))) src;
       data_at Ews (tarray tuchar (2 ^ 19 - Zlength (ws_bytes ws))) (Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength (ws_bytes ws)))
         (field_address0 (tarray tuchar (2 ^ 19)) (SUB Zlength (ws_bytes ws)) (field_address t_wseries (DOT _bytes) (gv _x_valid_dict__sr)));
       @field_at HCS Ews t_wseries (DOT _f) (map winfo_val (ws_frames ws) ++ Zrepeat (winfo_val winfo0) (4 - Zlength (ws_frames ws)))
         (gv _x_valid_dict__sr);
       field_at Ews t_wseries (DOT _nframes) (vu (Zlength (ws_frames ws))) (gv _x_valid_dict__sr);
       spacer Ews 786932 786936 (gv _x_valid_dict__sr);
       field_at Ews t_wseries (DOT _n) (vl (Zlength (ws_bytes ws))) (gv _x_valid_dict__sr);
       field_at Ews t_wseries (DOT _content) (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws)))
         (gv _x_valid_dict__sr);
       field_at Ews t_wseries (DOT _content_n) (vl (Zlength (ws_content ws))) (gv _x_valid_dict__sr);
       field_at Ews t_wdict (DOT _bytes) (zbytes (wd_bytes wd) ++ Zrepeat (Vint Int.zero) (6144 - Zlength (wd_bytes wd)))
         (gv _x_valid_dict__wd);
       field_at Ews t_wdict (DOT _n) (vl (Zlength (wd_bytes wd))) (gv _x_valid_dict__wd);
       field_at Ews t_wdict (DOT _formatted) (vb (wd_formatted wd)) (gv _x_valid_dict__wd); TT; WG gv; TT; has_ext tt))
    (Ssequence VD_rest_s (Sreturn (Some (Econst_int (Int.repr 0) tint))))
    (frame_ret_assert (function_body_ret_assert tint (PROP () RETURN () SEP (TT))) (stackframe_of f_main)).
Proof.
  simplify_func_tycontext. unfold VD_rest_s. abbreviate_semax.
  destruct (eq_dec src nullval); try contradiction; destruct (eq_dec buf nullval); try contradiction;
    destruct (eq_dec dctx nullval); try contradiction.
  subst src dctx.
  assert_PROP (isptr buf) as Hpb by entailer!.
  destruct buf as [| | | | | bb ob]; try contradiction.
  (VD_front; forward_call (gv, nullval, @None ddict_st); VD_side; forward_call (gv, nullval, @None dctx_st); VD_side; forward_call (tarray tuchar 1, nullval, gv); VD_side; forward_call (tarray tuchar (cap + 1 + Zlength (wd_bytes wd)), Vptr bb ob, gv); VD_side; forward).
Qed.

Lemma VD_zero4 {Espec: OracleKind} (gv: globals) (api: Z) (H: 0 <= api < 5) (wd: wdict) (H0: dict_facts wd) (H1: wdict_wf wd) (ws: wseries)
  (H2: series_facts (wdict_model (Some (wd, Ews))) ws) (H3: wseries_wf ws) (H4: readable_share Ews)
  (stv: reptype t_wstate) (H5: WDS wd stv) (Hfacts: series_facts (wd_model wd) ws)
  (Hbok: bytes_ok (ws_bytes ws)) (Hcok: bytes_ok (ws_content ws)) (Hnb: Zlength (ws_bytes ws) <= 2 ^ 19)
  (Hnc: Zlength (ws_content ws) <= 2 ^ 18) (Hnf: (1 <= Datatypes.length (ws_frames ws) <= 4)%nat)
  (Hdok: bytes_ok (wd_bytes wd)) (Hdl: 8 <= Zlength (wd_bytes wd) <= 2 ^ 12 + 2048) (Hda: dict_auto (wd_bytes wd) <> None)
  (Hdc: dm_content (wd_model wd) = wd_content wd) (Hdi: dm_id (wd_model wd) = wd_id wd) (Hdid: dict_id_of (wd_bytes wd) = wd_id wd)
  (Hraw: wd_formatted wd = false -> wd_model wd = dict_raw (wd_bytes wd) /\ wd_id wd = 0)
  (Hapi4: api = 4 -> wd_formatted wd = false /\ Zlength (ws_frames ws) = 1 /\ wi_skippable (hd winfo0 (ws_frames ws)) = false)
  (cap: Z) (H6: 0 <= cap <= Zlength (ws_content ws) + 16) (src: val) (PNsrc: is_pointer_or_null src) (buf dctx: val)
  (PNdctx: is_pointer_or_null dctx) (Hvp: forall (P: mpred) (q: val), P && valid_pointer q |-- P)
  (Hs: src = nullval) (Hb: buf <> nullval) (Hd: dctx <> nullval) :
  semax (func_tycontext f_main Vprog VD_G1 nil)
    (PROP () LOCAL (temp _dctx dctx; temp _buf buf; temp _src src; temp _cap (Vlong (Int64.repr cap));
       temp _ddict (Vlong (Int64.repr (Int.signed (Int.repr 0)))); temp _api (Vint (Int.repr api)); gvars gv)
     SEP (mem_mgr gv; zstd_globals gv;
       if eq_dec dctx nullval then emp else DC gv dctx dctx_init && valid_pointer dctx;
       if eq_dec buf nullval then emp
       else malloc_token Ews (tarray tuchar (cap + 1 + Zlength (wd_bytes wd))) buf *
            data_at_ Ews (tarray tuchar (cap + 1 + Zlength (wd_bytes wd))) buf;
       data_at Ews (tarray tuchar (Zlength (ws_bytes ws))) (zbytes (ws_bytes ws))
         (field_address t_wseries (DOT _bytes) (gv _x_valid_dict__sr));
       if eq_dec src nullval then emp
       else malloc_token Ews (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws)))) src *
            data_at Ews (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws))))
              (zbytes (ws_bytes ws) ++ Zrepeat Vundef (Z.max 1 (Zlength (ws_bytes ws)) - Zlength (ws_bytes ws))) src;
       data_at Ews (tarray tuchar (2 ^ 19 - Zlength (ws_bytes ws))) (Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength (ws_bytes ws)))
         (field_address0 (tarray tuchar (2 ^ 19)) (SUB Zlength (ws_bytes ws)) (field_address t_wseries (DOT _bytes) (gv _x_valid_dict__sr)));
       @field_at HCS Ews t_wseries (DOT _f) (map winfo_val (ws_frames ws) ++ Zrepeat (winfo_val winfo0) (4 - Zlength (ws_frames ws)))
         (gv _x_valid_dict__sr);
       field_at Ews t_wseries (DOT _nframes) (vu (Zlength (ws_frames ws))) (gv _x_valid_dict__sr);
       spacer Ews 786932 786936 (gv _x_valid_dict__sr);
       field_at Ews t_wseries (DOT _n) (vl (Zlength (ws_bytes ws))) (gv _x_valid_dict__sr);
       field_at Ews t_wseries (DOT _content) (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws)))
         (gv _x_valid_dict__sr);
       field_at Ews t_wseries (DOT _content_n) (vl (Zlength (ws_content ws))) (gv _x_valid_dict__sr);
       field_at Ews t_wdict (DOT _bytes) (zbytes (wd_bytes wd) ++ Zrepeat (Vint Int.zero) (6144 - Zlength (wd_bytes wd)))
         (gv _x_valid_dict__wd);
       field_at Ews t_wdict (DOT _n) (vl (Zlength (wd_bytes wd))) (gv _x_valid_dict__wd);
       field_at Ews t_wdict (DOT _formatted) (vb (wd_formatted wd)) (gv _x_valid_dict__wd); TT; WG gv; TT; has_ext tt))
    (Ssequence VD_rest_s (Sreturn (Some (Econst_int (Int.repr 0) tint))))
    (frame_ret_assert (function_body_ret_assert tint (PROP () RETURN () SEP (TT))) (stackframe_of f_main)).
Proof.
  simplify_func_tycontext. unfold VD_rest_s. abbreviate_semax.
  destruct (eq_dec src nullval); try contradiction; destruct (eq_dec buf nullval); try contradiction;
    destruct (eq_dec dctx nullval); try contradiction.
  subst src.
  assert_PROP (isptr buf) as Hpb by entailer!.
  destruct buf as [| | | | | bb ob]; try contradiction.
  assert (Hpd: isptr dctx) by (destruct dctx; simpl in *; try contradiction; auto; subst; contradiction).
  destruct dctx as [| | | | | bd od]; try contradiction.
  (VD_front; forward_call (gv, nullval, @None ddict_st); VD_side; sep_apply (Hvp (DC gv (Vptr bd od) dctx_init) (Vptr bd od)); forward_call (gv, Vptr bd od, Some dctx_init); VD_side; forward_call (tarray tuchar 1, nullval, gv); VD_side; forward_call (tarray tuchar (cap + 1 + Zlength (wd_bytes wd)), Vptr bb ob, gv); VD_side; forward).
Qed.

Lemma VD_zero5 {Espec: OracleKind} (gv: globals) (api: Z) (H: 0 <= api < 5) (wd: wdict) (H0: dict_facts wd) (H1: wdict_wf wd) (ws: wseries)
  (H2: series_facts (wdict_model (Some (wd, Ews))) ws) (H3: wseries_wf ws) (H4: readable_share Ews)
  (stv: reptype t_wstate) (H5: WDS wd stv) (Hfacts: series_facts (wd_model wd) ws)
  (Hbok: bytes_ok (ws_bytes ws)) (Hcok: bytes_ok (ws_content ws)) (Hnb: Zlength (ws_bytes ws) <= 2 ^ 19)
  (Hnc: Zlength (ws_content ws) <= 2 ^ 18) (Hnf: (1 <= Datatypes.length (ws_frames ws) <= 4)%nat)
  (Hdok: bytes_ok (wd_bytes wd)) (Hdl: 8 <= Zlength (wd_bytes wd) <= 2 ^ 12 + 2048) (Hda: dict_auto (wd_bytes wd) <> None)
  (Hdc: dm_content (wd_model wd) = wd_content wd) (Hdi: dm_id (wd_model wd) = wd_id wd) (Hdid: dict_id_of (wd_bytes wd) = wd_id wd)
  (Hraw: wd_formatted wd = false -> wd_model wd = dict_raw (wd_bytes wd) /\ wd_id wd = 0)
  (Hapi4: api = 4 -> wd_formatted wd = false /\ Zlength (ws_frames ws) = 1 /\ wi_skippable (hd winfo0 (ws_frames ws)) = false)
  (cap: Z) (H6: 0 <= cap <= Zlength (ws_content ws) + 16) (src: val) (PNsrc: is_pointer_or_null src) (buf dctx: val)
  (PNdctx: is_pointer_or_null dctx) (Hvp: forall (P: mpred) (q: val), P && valid_pointer q |-- P)
  (Hs: src <> nullval) (Hb: buf = nullval) (Hd: dctx = nullval) :
  semax (func_tycontext f_main Vprog VD_G1 nil)
    (PROP () LOCAL (temp _dctx dctx; temp _buf buf; temp _src src; temp _cap (Vlong (Int64.repr cap));
       temp _ddict (Vlong (Int64.repr (Int.signed (Int.repr 0)))); temp _api (Vint (Int.repr api)); gvars gv)
     SEP (mem_mgr gv; zstd_globals gv;
       if eq_dec dctx nullval then emp else DC gv dctx dctx_init && valid_pointer dctx;
       if eq_dec buf nullval then emp
       else malloc_token Ews (tarray tuchar (cap + 1 + Zlength (wd_bytes wd))) buf *
            data_at_ Ews (tarray tuchar (cap + 1 + Zlength (wd_bytes wd))) buf;
       data_at Ews (tarray tuchar (Zlength (ws_bytes ws))) (zbytes (ws_bytes ws))
         (field_address t_wseries (DOT _bytes) (gv _x_valid_dict__sr));
       if eq_dec src nullval then emp
       else malloc_token Ews (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws)))) src *
            data_at Ews (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws))))
              (zbytes (ws_bytes ws) ++ Zrepeat Vundef (Z.max 1 (Zlength (ws_bytes ws)) - Zlength (ws_bytes ws))) src;
       data_at Ews (tarray tuchar (2 ^ 19 - Zlength (ws_bytes ws))) (Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength (ws_bytes ws)))
         (field_address0 (tarray tuchar (2 ^ 19)) (SUB Zlength (ws_bytes ws)) (field_address t_wseries (DOT _bytes) (gv _x_valid_dict__sr)));
       @field_at HCS Ews t_wseries (DOT _f) (map winfo_val (ws_frames ws) ++ Zrepeat (winfo_val winfo0) (4 - Zlength (ws_frames ws)))
         (gv _x_valid_dict__sr);
       field_at Ews t_wseries (DOT _nframes) (vu (Zlength (ws_frames ws))) (gv _x_valid_dict__sr);
       spacer Ews 786932 786936 (gv _x_valid_dict__sr);
       field_at Ews t_wseries (DOT _n) (vl (Zlength (ws_bytes ws))) (gv _x_valid_dict__sr);
       field_at Ews t_wseries (DOT _content) (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws)))
         (gv _x_valid_dict__sr);
       field_at Ews t_wseries (DOT _content_n) (vl (Zlength (ws_content ws))) (gv _x_valid_dict__sr);
       field_at Ews t_wdict (DOT _bytes) (zbytes (wd_bytes wd) ++ Zrepeat (Vint Int.zero) (6144 - Zlength (wd_bytes wd)))
         (gv _x_valid_dict__wd);
       field_at Ews t_wdict (DOT _n) (vl (Zlength (wd_bytes wd))) (gv _x_valid_dict__wd);
       field_at Ews t_wdict (DOT _formatted) (vb (wd_formatted wd)) (gv _x_valid_dict__wd); TT; WG gv; TT; has_ext tt))
    (Ssequence VD_rest_s (Sreturn (Some (Econst_int (Int.repr 0) tint))))
    (frame_ret_assert (function_body_ret_assert tint (PROP () RETURN () SEP (TT))) (stackframe_of f_main)).
Proof.
  simplify_func_tycontext. unfold VD_rest_s. abbreviate_semax.
  destruct (eq_dec src nullval); try contradiction; destruct (eq_dec buf nullval); try contradiction;
    destruct (eq_dec dctx nullval); try contradiction.
  assert (Hps: isptr src) by (destruct src; simpl in *; try contradiction; auto; subst; contradiction).
  destruct src as [| | | | | bs os]; try contradiction.
  subst buf dctx.
  (VD_front; forward_call (gv, nullval, @None ddict_st); VD_side; forward_call (gv, nullval, @None dctx_st); VD_side; sep_apply (data_at_data_at_ Ews (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws))))); forward_call (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws))), Vptr bs os, gv); VD_side; forward_call (tarray tuchar 1, nullval, gv); VD_side; forward).
Qed.

Lemma VD_zero6 {Espec: OracleKind} (gv: globals) (api: Z) (H: 0 <= api < 5) (wd: wdict) (H0: dict_facts wd) (H1: wdict_wf wd) (ws: wseries)
  (H2: series_facts (wdict_model (Some (wd, Ews))) ws) (H3: wseries_wf ws) (H4: readable_share Ews)
  (stv: reptype t_wstate) (H5: WDS wd stv) (Hfacts: series_facts (wd_model wd) ws)
  (Hbok: bytes_ok (ws_bytes ws)) (Hcok: bytes_ok (ws_content ws)) (Hnb: Zlength (ws_bytes ws) <= 2 ^ 19)
  (Hnc: Zlength (ws_content ws) <= 2 ^ 18) (Hnf: (1 <= Datatypes.length (ws_frames ws) <= 4)%nat)
  (Hdok: bytes_ok (wd_bytes wd)) (Hdl: 8 <= Zlength (wd_bytes wd) <= 2 ^ 12 + 2048) (Hda: dict_auto (wd_bytes wd) <> None)
  (Hdc: dm_content (wd_model wd) = wd_content wd) (Hdi: dm_id (wd_model wd) = wd_id wd) (Hdid: dict_id_of (wd_bytes wd) = wd_id wd)
  (Hraw: wd_formatted wd = false -> wd_model wd = dict_raw (wd_bytes wd) /\ wd_id wd = 0)
  (Hapi4: api = 4 -> wd_formatted wd = false /\ Zlength (ws_frames ws) = 1 /\ wi_skippable (hd winfo0 (ws_frames ws)) = false)
  (cap: Z) (H6: 0 <= cap <= Zlength (ws_content ws) + 16) (src: val) (PNsrc: is_pointer_or_null src) (buf dctx: val)
  (PNdctx: is_pointer_or_null dctx) (Hvp: forall (P: mpred) (q: val), P && valid_pointer q |-- P)
  (Hs: src <> nullval) (Hb: buf = nullval) (Hd: dctx <> nullval) :
  semax (func_tycontext f_main Vprog VD_G1 nil)
    (PROP () LOCAL (temp _dctx dctx; temp _buf buf; temp _src src; temp _cap (Vlong (Int64.repr cap));
       temp _ddict (Vlong (Int64.repr (Int.signed (Int.repr 0)))); temp _api (Vint (Int.repr api)); gvars gv)
     SEP (mem_mgr gv; zstd_globals gv;
       if eq_dec dctx nullval then emp else DC gv dctx dctx_init && valid_pointer dctx;
       if eq_dec buf nullval then emp
       else malloc_token Ews (tarray tuchar (cap + 1 + Zlength (wd_bytes wd))) buf *
            data_at_ Ews (tarray tuchar (cap + 1 + Zlength (wd_bytes wd))) buf;
       data_at Ews (tarray tuchar (Zlength (ws_bytes ws))) (zbytes (ws_bytes ws))
         (field_address t_wseries (DOT _bytes) (gv _x_valid_dict__sr));
       if eq_dec src nullval then emp
       else malloc_token Ews (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws)))) src *
            data_at Ews (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws))))
              (zbytes (ws_bytes ws) ++ Zrepeat Vundef (Z.max 1 (Zlength (ws_bytes ws)) - Zlength (ws_bytes ws))) src;
       data_at Ews (tarray tuchar (2 ^ 19 - Zlength (ws_bytes ws))) (Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength (ws_bytes ws)))
         (field_address0 (tarray tuchar (2 ^ 19)) (SUB Zlength (ws_bytes ws)) (field_address t_wseries (DOT _bytes) (gv _x_valid_dict__sr)));
       @field_at HCS Ews t_wseries (DOT _f) (map winfo_val (ws_frames ws) ++ Zrepeat (winfo_val winfo0) (4 - Zlength (ws_frames ws)))
         (gv _x_valid_dict__sr);
       field_at Ews t_wseries (DOT _nframes) (vu (Zlength (ws_frames ws))) (gv _x_valid_dict__sr);
       spacer Ews 786932 786936 (gv _x_valid_dict__sr);
       field_at Ews t_wseries (DOT _n) (vl (Zlength (ws_bytes ws))) (gv _x_valid_dict__sr);
       field_at Ews t_wseries (DOT _content) (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws)))
         (gv _x_valid_dict__sr);
       field_at Ews t_wseries (DOT _content_n) (vl (Zlength (ws_content ws))) (gv _x_valid_dict__sr);
       field_at Ews t_wdict (DOT _bytes) (zbytes (wd_bytes wd) ++ Zrepeat (Vint Int.zero) (6144 - Zlength (wd_bytes wd)))
         (gv _x_valid_dict__wd);
       field_at Ews t_wdict (DOT _n) (vl (Zlength (wd_bytes wd))) (gv _x_valid_dict__wd);
       field_at Ews t_wdict (DOT _formatted) (vb (wd_formatted wd)) (gv _x_valid_dict__wd); TT; WG gv; TT; has_ext tt))
    (Ssequence VD_rest_s (Sreturn (Some (Econst_int (Int.repr 0) tint))))
    (frame_ret_assert (function_body_ret_assert tint (PROP () RETURN () SEP (TT))) (stackframe_of f_main)).
Proof.
  simplify_func_tycontext. unfold VD_rest_s. abbreviate_semax.
  destruct (eq_dec src nullval); try contradiction; destruct (eq_dec buf nullval); try contradiction;
    destruct (eq_dec dctx nullval); try contradiction.
  assert (Hps: isptr src) by (destruct src; simpl in *; try contradiction; auto; subst; contradiction).
  destruct src as [| | | | | bs os]; try contradiction.
  subst buf.
  assert (Hpd: isptr dctx) by (destruct dctx; simpl in *; try contradiction; auto; subst; contradiction).
  destruct dctx as [| | | | | bd od]; try contradiction.
  (VD_front; forward_call (gv, nullval, @None ddict_st); VD_side; sep_apply (Hvp (DC gv (Vptr bd od) dctx_init) (Vptr bd od)); forward_call (gv, Vptr bd od, Some dctx_init); VD_side; sep_apply (data_at_data_at_ Ews (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws))))); forward_call (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws))), Vptr bs os, gv); VD_side; forward_call (tarray tuchar 1, nullval, gv); VD_side; forward).
Qed.

Lemma VD_zero7 {Espec: OracleKind} (gv: globals) (api: Z) (H: 0 <= api < 5) (wd: wdict) (H0: dict_facts wd) (H1: wdict_wf wd) (ws: wseries)
  (H2: series_facts (wdict_model (Some (wd, Ews))) ws) (H3: wseries_wf ws) (H4: readable_share Ews)
  (stv: reptype t_wstate) (H5: WDS wd stv) (Hfacts: series_facts (wd_model wd) ws)
  (Hbok: bytes_ok (ws_bytes ws)) (Hcok: bytes_ok (ws_content ws)) (Hnb: Zlength (ws_bytes ws) <= 2 ^ 19)
  (Hnc: Zlength (ws_content ws) <= 2 ^ 18) (Hnf: (1 <= Datatypes.length (ws_frames ws) <= 4)%nat)
  (Hdok: bytes_ok (wd_bytes wd)) (Hdl: 8 <= Zlength (wd_bytes wd) <= 2 ^ 12 + 2048) (Hda: dict_auto (wd_bytes wd) <> None)
  (Hdc: dm_content (wd_model wd) = wd_content wd) (Hdi: dm_id (wd_model wd) = wd_id wd) (Hdid: dict_id_of (wd_bytes wd) = wd_id wd)
  (Hraw: wd_formatted wd = false -> wd_model wd = dict_raw (wd_bytes wd) /\ wd_id wd = 0)
  (Hapi4: api = 4 -> wd_formatted wd = false /\ Zlength (ws_frames ws) = 1 /\ wi_skippable (hd winfo0 (ws_frames ws)) = false)
  (cap: Z) (H6: 0 <= cap <= Zlength (ws_content ws) + 16) (src: val) (PNsrc: is_pointer_or_null src) (buf dctx: val)
  (PNdctx: is_pointer_or_null dctx) (Hvp: forall (P: mpred) (q: val), P && valid_pointer q |-- P)
  (Hs: src <> nullval) (Hb: buf <> nullval) (Hd: dctx = nullval) :
  semax (func_tycontext f_main Vprog VD_G1 nil)
    (PROP () LOCAL (temp _dctx dctx; temp _buf buf; temp _src src; temp _cap (Vlong (Int64.repr cap));
       temp _ddict (Vlong (Int64.repr (Int.signed (Int.repr 0)))); temp _api (Vint (Int.repr api)); gvars gv)
     SEP (mem_mgr gv; zstd_globals gv;
       if eq_dec dctx nullval then emp else DC gv dctx dctx_init && valid_pointer dctx;
       if eq_dec buf nullval then emp
       else malloc_token Ews (tarray tuchar (cap + 1 + Zlength (wd_bytes wd))) buf *
            data_at_ Ews (tarray tuchar (cap + 1 + Zlength (wd_bytes wd))) buf;
       data_at Ews (tarray tuchar (Zlength (ws_bytes ws))) (zbytes (ws_bytes ws))
         (field_address t_wseries (DOT _bytes) (gv _x_valid_dict__sr));
       if eq_dec src nullval then emp
       else malloc_token Ews (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws)))) src *
            data_at Ews (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws))))
              (zbytes (ws_bytes ws) ++ Zrepeat Vundef (Z.max 1 (Zlength (ws_bytes ws)) - Zlength (ws_bytes ws))) src;
       data_at Ews (tarray tuchar (2 ^ 19 - Zlength (ws_bytes ws))) (Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength (ws_bytes ws)))
         (field_address0 (tarray tuchar (2 ^ 19)) (SUB Zlength (ws_bytes ws)) (field_address t_wseries (DOT _bytes) (gv _x_valid_dict__sr)));
       @field_at HCS Ews t_wseries (DOT _f) (map winfo_val (ws_frames ws) ++ Zrepeat (winfo_val winfo0) (4 - Zlength (ws_frames ws)))
         (gv _x_valid_dict__sr);
       field_at Ews t_wseries (DOT _nframes) (vu (Zlength (ws_frames ws))) (gv _x_valid_dict__sr);
       spacer Ews 786932 786936 (gv _x_valid_dict__sr);
       field_at Ews t_wseries (DOT _n) (vl (Zlength (ws_bytes ws))) (gv _x_valid_dict__sr);
       field_at Ews t_wseries (DOT _content) (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws)))
         (gv _x_valid_dict__sr);
       field_at Ews t_wseries (DOT _content_n) (vl (Zlength (ws_content ws))) (gv _x_valid_dict__sr);
       field_at Ews t_wdict (DOT _bytes) (zbytes (wd_bytes wd) ++ Zrepeat (Vint Int.zero) (6144 - Zlength (wd_bytes wd)))
         (gv _x_valid_dict__wd);
       field_at Ews t_wdict (DOT _n) (vl (Zlength (wd_bytes wd))) (gv _x_valid_dict__wd);
       field_at Ews t_wdict (DOT _formatted) (vb (wd_formatted wd)) (gv _x_valid_dict__wd); TT; WG gv; TT; has_ext tt))
    (Ssequence VD_rest_s (Sreturn (Some (Econst_int (Int.repr 0) tint))))
    (frame_ret_assert (function_body_ret_assert tint (PROP () RETURN () SEP (TT))) (stackframe_of f_main)).
Proof.
  simplify_func_tycontext. unfold VD_rest_s. abbreviate_semax.
  destruct (eq_dec src nullval); try contradiction; destruct (eq_dec buf nullval); try contradiction;
    destruct (eq_dec dctx nullval); try contradiction.
  assert (Hps: isptr src) by (destruct src; simpl in *; try contradiction; auto; subst; contradiction).
  destruct src as [| | | | | bs os]; try contradiction.
  assert_PROP (isptr buf) as Hpb by entailer!.
  destruct buf as [| | | | | bb ob]; try contradiction.
  subst dctx.
  (VD_front; forward_call (gv, nullval, @None ddict_st); VD_side; forward_call (gv, nullval, @None dctx_st); VD_side; sep_apply (data_at_data_at_ Ews (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws))))); forward_call (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws))), Vptr bs os, gv); VD_side; forward_call (tarray tuchar (cap + 1 + Zlength (wd_bytes wd)), Vptr bb ob, gv); VD_side; forward).
Qed.

Lemma VD_body_main : semax_body Vprog VD_G1 f_main main_spec.
Proof.
unfold main_spec, QPmain_spec_ext', NDmk_funspec.
split3; [reflexivity | reflexivity |].
intros Espec DTL gv.
simpl fn_body; simpl fn_params; simpl fn_return.
change (map fst []) with (@nil ident).
eapply (main_pre_InitGpred
          (sepcon (zstd_globals gv) (sepcon (WG gv) (sepcon (data_at Ews t_wseries (zero_val t_wseries) (gv _x_valid_dict__sr))
             (sepcon (data_at Ews t_wdict (zero_val t_wdict) (gv _x_valid_dict__wd)) TT))))
          _ _ _ Zstd.contracts.x_valid_dict.whole_prog).
4: idtac.
- intros. apply VD_pre; auto.
- reflexivity.
- apply Forall_forall; intros [i g] Hin; simpl fst.
  apply VD_tyc_g_isSome. unfold Vprog, QPvarspecs. rewrite map_map.
  apply in_map_iff. exists (i, g); auto.
- process_stackframe_of.
  repeat rewrite <- data_at__offset_zero.
  try simple apply start_function_aux1.
  match goal with |- semax ?D ?P ?c (frame_ret_assert (function_body_ret_assert ?t _) ?F) =>
    apply (semax_post (frame_ret_assert (function_body_ret_assert t (PROP () LOCAL () (SEP (TT)))) F))
  end.
  1,2,3: intros; simpl; normalize.
  1: intros [v|]; simpl; unfold bind_ret; simpl; normalize;
       try (intros x; apply andp_left2; apply sepcon_derives; [unfold_lift; apply TT_right | auto]).
  abbreviate_semax.
  sep_apply (create_mem_mgr gv).
  forward_call 5.
  Intros api.
  forward.
  forward_call (gv, Ews, gv _x_valid_dict__wd).
  Intros wd.
  forward_call (gv, Ews, gv _x_valid_dict__sr, gv _x_valid_dict__wd, Some (wd, Ews)).
  { unfold wdict_arg. entailer!. }
  Intros ws. unfold wdict_arg, wdict_model, wdict_rep. Intros stv.
  pose proof H2 as Hfacts. unfold wdict_model in Hfacts.
  pose proof H2 as (Hbok & Hcok & Hnb & Hnc & Hnf & _).
  pose proof H0 as (Hdok & Hdl & Hda & Hdc & Hdi & Hdid & Hraw).
  sep_apply (VB_wd_take wd (gv _x_valid_dict__wd) stv).
  sep_apply (VB_ws_unfold ws (gv _x_valid_dict__sr) Hnb).
  Intros.
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
    forward_if (PROPx ((api = 4 -> wd_formatted wd = false /\ Zlength (ws_frames ws) = 1 /\
                               wi_skippable (hd winfo0 (ws_frames ws)) = false) :: P) (LOCALx L (SEPx R))) end.
  { unfold VB_sr_rest. Intros.
    forward.
    ifs.
    - forward. forward.
      ifs.
      + assert (Hl: Zlength (ws_frames ws) = 1).
        { match goal with Hx: Int.repr (Zlength (ws_frames ws)) = Int.repr 1 |- _ =>
            rewrite Zlength_correct in *; apply repr_inj_unsigned in Hx; rep_lia end. }
        forward.
        { entailer!. destruct (ws_frames ws) as [|f0 fs]; [rewrite Zlength_nil in Hl; lia |].
          cbn [map app]. rewrite Znth_0_cons. unfold winfo_val. destruct (wi_skippable f0); exact I. }
        forward.
        forward_call (Int.repr (if wi_skippable (hd winfo0 (ws_frames ws)) then 0 else 1)).
        { entailer!. destruct (ws_frames ws) as [|f0 fs]; [rewrite Zlength_nil in Hl; lia |].
          cbn [map app hd]. rewrite Znth_0_cons. unfold winfo_val. destruct (wi_skippable f0); reflexivity. }
        Intros. destruct (wi_skippable (hd winfo0 (ws_frames ws))) eqn:Es; [contradiction|].
        sep_apply (VB_rest_fold ws (gv _x_valid_dict__sr)).
        entailer!.
        destruct (wd_formatted wd); [discriminate|]. auto.
      + forward. forward_call (Int.repr 0). Intros. contradiction.
    - forward. ifs. forward. forward_call (Int.repr 0). Intros. contradiction. }
  { forward. entailer!. }
  Intros. match goal with Hx: api = 4 -> _ |- _ => rename Hx into Hapi4 end.
  forward.
  forward_call (0, Zlength (ws_content ws) + 16).
  Intros cap. forward. forward.
  unfold VB_sr_rest. Intros.
  forward_call (gv, Ews, field_address t_wseries (DOT _bytes) (gv _x_valid_dict__sr), ws_bytes ws).
  { entailer!.
    match goal with H: field_compatible _ [] (field_address t_wseries (DOT _bytes) ?p) |- _ =>
      unfold field_address in *; destruct (field_compatible_dec t_wseries (DOT _bytes) p) as [Hfc|Hfc];
      [| destruct H as [Hx _]; contradiction] end.
    simpl. destruct (gv _x_valid_dict__sr); try contradiction. reflexivity. }
  Intros src.
  forward. forward.
  forward_call (tarray tuchar (cap + 1 + Zlength (wd_bytes wd)), gv).
  { simpl. rep_lia. }
  Intros buf. forward.
  forward_call gv. Intros dctx.
  deadvars!.
  assert (Hvp: forall (P: mpred) q, (P && valid_pointer q) |-- P) by (intros; apply andp_left1, derives_refl).
  (* an allocation failed: rounds = 0 *)
  (* case splits that leave the goal's [if eq_dec _ nullval] alone, so that it unifies with the lemmas' *)
  pose proof (eq_dec src nullval) as Hs'. pose proof (eq_dec buf nullval) as Hb'. pose proof (eq_dec dctx nullval) as Hd'.
  destruct Hs' as [Hs|Hs].
  { destruct Hb' as [Hb|Hb]; destruct Hd' as [Hd|Hd];
      [eapply VD_zero1 | eapply VD_zero2 | eapply VD_zero3 | eapply VD_zero4]; eassumption. }
  destruct Hb' as [Hb|Hb].
  { destruct Hd' as [Hd|Hd]; [eapply VD_zero5 | eapply VD_zero6]; eassumption. }
  destruct Hd' as [Hd|Hd].
  { eapply VD_zero7; eassumption. }
  destruct (eq_dec src nullval); try contradiction; destruct (eq_dec buf nullval); try contradiction;
    destruct (eq_dec dctx nullval); try contradiction.
  assert (Hps: isptr src) by (destruct src; simpl in *; try contradiction; auto; subst; contradiction).
  destruct src as [| | | | | bs os]; try contradiction.
  assert_PROP (isptr buf) as Hpb by entailer!. destruct buf as [| | | | | bb ob]; try contradiction.
  assert (Hpd: isptr dctx) by (destruct dctx; simpl in *; try contradiction; auto; subst; contradiction).
  destruct dctx as [| | | | | bd od]; try contradiction.
  (* every allocation succeeded *)
  repeat (first [rewrite if_true by auto | rewrite if_false by discriminate]). Intros.
  ifs. forward. ifs. forward. ifs.
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _x_valid_dict__t'10 (Vint (Int.repr (VM_rnd api))) :: L) (SEPx R))) end.
  { forward. forward. entailer!. }
  { forward. forward. entailer!.
    all: try (unfold VM_rnd; destruct (Z.eqb_spec api 2); [subst api; contradiction | reflexivity]). }
  repeat forward.
  ifs. forward.
  match goal with |- context [temp _dict ?v] => replace v with (offset_val (cap + 1) (Vptr bb ob))
    by (rewrite <- (VB_dict_val (Vptr bb ob) cap I ltac:(rep_lia)); reflexivity) end.
  pose proof (VM_rnd_range api) as Hrr.
  ifs. deadvars!.
  assert_PROP (field_compatible (tarray tuchar (cap + 1 + Zlength (wd_bytes wd))) [] (Vptr bb ob)) as Hfb by entailer!.
  rewrite (VB_split3_ Ews cap (Zlength (wd_bytes wd)) (Vptr bb ob)) by (auto; lia). Intros.
  rewrite (VB_Zrepeat Ews (Zlength (wd_bytes wd))).
  (* the dictionary's bytes, copied into [dst | gap | dict] *)
  forward.
  freeze [0;1;2;3;4;5;7;8;9;10;11;12;13;14;15;16;19;20;21;22;23] FR1.
  match goal with |- semax _ (PROPx _ (LOCALx (_ :: ?L) (SEPx (?F :: _ :: ?R)))) _ _ =>
    forward_loop (EX i: Z, PROPx [0 <= i <= Zlength (wd_bytes wd)] (LOCALx (temp _i (Vlong (Int64.repr i)) :: L)
         (SEPx (F :: data_at Ews (tarray tuchar (Zlength (wd_bytes wd))) (zbytes (sublist 0 i (wd_bytes wd)) ++ Zrepeat Vundef (Zlength (wd_bytes wd) - i)) (offset_val (cap + 1) (Vptr bb ob)) :: R))))
      continue: (EX i: Z, PROPx [0 <= i < Zlength (wd_bytes wd)] (LOCALx (temp _i (Vlong (Int64.repr i)) :: L)
         (SEPx (F :: data_at Ews (tarray tuchar (Zlength (wd_bytes wd))) (zbytes (sublist 0 (i + 1) (wd_bytes wd)) ++ Zrepeat Vundef (Zlength (wd_bytes wd) - (i + 1))) (offset_val (cap + 1) (Vptr bb ob)) :: R))))
      break: (PROPx [] (LOCALx (temp _i (Vlong (Int64.repr (Zlength (wd_bytes wd)))) :: L)
         (SEPx (F :: data_at Ews (tarray tuchar (Zlength (wd_bytes wd))) (zbytes (wd_bytes wd)) (offset_val (cap + 1) (Vptr bb ob)) :: R))))
  end.
  { Exists 0. entailer!. simpl app. cancel. }
  { Intros i. forward. ifs.
    1: assert (Hbi: is_byte (Znth i (wd_bytes wd))) by (apply Forall_Znth; auto; lia).
    1: unfold is_byte in Hbi.
    1: forward.
    1: { entailer!. rewrite VB_content_at by lia. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    1: rewrite VB_content_at by lia.
    1: forward.
    1: Exists i. 1: entailer!.
    1: rewrite (VB_copy_step (wd_bytes wd) i (Zlength (wd_bytes wd))) by (auto; lia). 1: cancel.
    assert (Hin: i = Zlength (wd_bytes wd)) by lia. subst i.
    forward. entailer!. rewrite sublist_same by lia. rewrite Z.sub_diag. simpl. rewrite app_nil_r. cancel. }
  { Intros i. forward. Exists (i + 1). entailer!. }
  thaw FR1. deadvars!.
  rewrite (VB_cs HCS ZCS Ews (Zlength (wd_bytes wd)) (zbytes (wd_bytes wd)) (offset_val (cap + 1) (Vptr bb ob))).
  (* api 1 and 3: a DDict by reference *)
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _x_valid_dict__t'12 (Vint (Int.repr (if orb (api =? 1) (api =? 3) then 1 else 0))) :: L) (SEPx R))) end.
  { forward. entailer!. }
  { forward. entailer!.
    rewrite (proj2 (Z.eqb_neq api 1) H12). simpl orb. unfold bool2val.
    destruct (zeq api 3) as [->|Hn]; [reflexivity | rewrite (proj2 (Z.eqb_neq api 3) Hn); reflexivity]. }
  match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
  forward_if (EX q: val, EX rnd: Z, EX e: ddict_st,
    PROPx [(q = nullval /\ rnd = VM_rnd api /\ orb (api =? 1) (api =? 3) = false) \/
           (orb (api =? 1) (api =? 3) = true /\ ((q = nullval /\ rnd = 0) \/ (isptr q /\ rnd = 1)))]
    (LOCALx [temp _dict (offset_val (cap + 1) (Vptr bb ob)); temp _dst (Vptr bb ob); temp _rounds (Vint (Int.repr rnd));
           temp _dctx (Vptr bd od); temp _buf (Vptr bb ob); temp _src (Vptr bs os); temp _cap (Vlong (Int64.repr cap));
           temp _ddict q; temp _api (Vint (Int.repr api)); gvars gv]
    (SEPx ((if eq_dec q nullval then emp
            else (DD gv q (VI_dd (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd) e) && valid_pointer q)) :: R))))
  end.
  { match goal with Hx: Int.repr (if ?b then 1 else 0) <> Int.zero |- _ =>
      destruct b eqn:E13; [| exfalso; apply Hx; reflexivity] end.
    assert (Hr1: VM_rnd api = 1)
      by (unfold VM_rnd; apply orb_true_iff in E13; destruct E13 as [E|E]; apply Z.eqb_eq in E; subst; reflexivity).
    rewrite Hr1.
    forward.
    forward_call ([] : list ptr_witness, gv, Ews, (offset_val (cap + 1) (Vptr bb ob)), wd_bytes wd).
    { unfold pws_pred. cbn [map fold_right]. cancel. }
    { apply VB_buf_ok_nil. lia. }
    Intros vret. destruct vret as [q dd]. cbn [fst snd] in *. unfold pws_pred. cbn [map fold_right]. forward.
    match goal with Hb': dd_bytes dd = _, Hr': dd_ref dd = _ |- _ => rewrite <- (VI_dd_eta _ _ dd Hb' Hr') end.
    destruct (eq_dec q nullval) as [Hq|Hq].
    - subst q. forward_if.
      + forward. Exists nullval 0 dd. entailer!.
      + exfalso. auto.
    - assert (Hpq: isptr q) by (destruct q; simpl in *; try contradiction; auto; subst; contradiction).
      destruct q as [| | | | | bq oq]; try contradiction.
      forward_if.
      + discriminate.
      + forward. Exists (Vptr bq oq) 1 dd.
        entailer!. rewrite if_false by discriminate. cancel. }
  { forward. Exists nullval (VM_rnd api) {| dd_bytes := nil; dd_ref := None; dd_buf := nullval; dd_ld := None |}. entailer!.
    match goal with Hx: Int.repr (if ?b then 1 else 0) = Int.zero |- _ =>
      destruct b eqn:E13; [exfalso; apply repr_inj_unsigned in Hx; rep_lia | auto] end. }
  Intros q rnd e.
  (* the resources of the rounds: src split, the witness, dst at the API's compspecs *)
  assert_PROP (field_compatible (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws)))) [] (Vptr bs os)) as Hfs by entailer!.
  rewrite (VB_src_split (Vptr bs os) (ws_bytes ws) Hfs). Intros.
  rewrite (VB_cs_ HCS ZCS Ews 1 (offset_val cap (Vptr bb ob))).
  sep_apply (VB_wit_fold (Vptr bs os) (Zlength (ws_bytes ws)) (Vptr bb ob) cap).
  rewrite (VB_cs_ HCS ZCS Ews cap (Vptr bb ob)). rewrite (VB_Zrepeat Ews cap (Vptr bb ob)).
  sep_apply (Hvp (DC gv (Vptr bd od) dctx_init) (Vptr bd od)).
  sep_apply (VB_rest_fold ws (gv _x_valid_dict__sr)).
  forward.
  forward_loop (EX k: Z, EX R: Z, EX st: dctx_st, EX out: list val,
    PROP (0 <= k <= R; R <= 2; (R = 2 -> api = 2); (0 < R -> orb (api =? 1) (api =? 3) = true -> isptr q);
          (orb (api =? 1) (api =? 3) = false -> q = nullval); Zlength out = cap; dc_ss st = ss_init; VM_df st;
          (k = 0 -> st = dctx_init); (0 < k < R -> dc_dict st = Some (VM_dr2 (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd)) /\ last_ok st (VM_dr2 (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd))))
    LOCAL (temp _k (Vint (Int.repr k)); temp _rounds (Vint (Int.repr R)); temp _ddict q; temp _dctx (Vptr bd od);
         temp _dst (Vptr bb ob); temp _buf (Vptr bb ob); temp _dict (offset_val (cap + 1) (Vptr bb ob)); temp _src (Vptr bs os); temp _cap (Vlong (Int64.repr cap));
         temp _api (Vint (Int.repr api)); gvars gv)
    SEP (mem_mgr gv; zstd_globals gv; DC gv (Vptr bd od) st;
         (if eq_dec q nullval then emp else (DD gv q (VI_dd (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd) e) && valid_pointer q));
         @data_at ZCS Ews (tarray tuchar (Zlength (wd_bytes wd))) (zbytes (wd_bytes wd)) (offset_val (cap + 1) (Vptr bb ob));
         pws_pred (VB_W (Vptr bs os) (Zlength (ws_bytes ws)) (Vptr bb ob) cap); @data_at ZCS Ews (tarray tuchar cap) out (Vptr bb ob);
         @data_at ZCS Ews (tarray tuchar (Zlength (ws_bytes ws))) (zbytes (ws_bytes ws)) (Vptr bs os);
         @malloc_token HCS Ews (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws)))) (Vptr bs os);
         @malloc_token HCS Ews (tarray tuchar (cap + 1 + Zlength (wd_bytes wd))) (Vptr bb ob);
         VB_sr_rest ws (gv _x_valid_dict__sr);
         @field_at HCS Ews t_wseries (DOT _n) (vl (Zlength (ws_bytes ws))) (gv _x_valid_dict__sr);
         @field_at HCS Ews t_wseries (DOT _content) (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws))) (gv _x_valid_dict__sr);
         @field_at HCS Ews t_wseries (DOT _content_n) (vl (Zlength (ws_content ws))) (gv _x_valid_dict__sr);
         @field_at HCS Ews t_wdict (DOT _n) (vl (Zlength (wd_bytes wd))) (gv _x_valid_dict__wd); TT))%assert
    break: (EX R: Z, EX st: dctx_st, EX out: list val,
    PROP (Zlength out = cap)
    LOCAL (temp _rounds (Vint (Int.repr R)); temp _ddict q; temp _dctx (Vptr bd od);
         temp _dst (Vptr bb ob); temp _buf (Vptr bb ob); temp _dict (offset_val (cap + 1) (Vptr bb ob)); temp _src (Vptr bs os); temp _cap (Vlong (Int64.repr cap));
         temp _api (Vint (Int.repr api)); gvars gv)
    SEP (mem_mgr gv; zstd_globals gv; DC gv (Vptr bd od) st;
         (if eq_dec q nullval then emp else (DD gv q (VI_dd (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd) e) && valid_pointer q));
         @data_at ZCS Ews (tarray tuchar (Zlength (wd_bytes wd))) (zbytes (wd_bytes wd)) (offset_val (cap + 1) (Vptr bb ob));
         pws_pred (VB_W (Vptr bs os) (Zlength (ws_bytes ws)) (Vptr bb ob) cap); @data_at ZCS Ews (tarray tuchar cap) out (Vptr bb ob);
         @data_at ZCS Ews (tarray tuchar (Zlength (ws_bytes ws))) (zbytes (ws_bytes ws)) (Vptr bs os);
         @malloc_token HCS Ews (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws)))) (Vptr bs os);
         @malloc_token HCS Ews (tarray tuchar (cap + 1 + Zlength (wd_bytes wd))) (Vptr bb ob);
         VB_sr_rest ws (gv _x_valid_dict__sr);
         @field_at HCS Ews t_wseries (DOT _n) (vl (Zlength (ws_bytes ws))) (gv _x_valid_dict__sr);
         @field_at HCS Ews t_wseries (DOT _content) (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws))) (gv _x_valid_dict__sr);
         @field_at HCS Ews t_wseries (DOT _content_n) (vl (Zlength (ws_content ws))) (gv _x_valid_dict__sr);
         @field_at HCS Ews t_wdict (DOT _n) (vl (Zlength (wd_bytes wd))) (gv _x_valid_dict__wd); TT))%assert.
  { Exists 0 rnd dctx_init (Zrepeat Vundef cap). entailer!.
    match goal with Hd: (_ /\ _ /\ _) \/ (_ /\ _) |- _ => destruct Hd as [(Eq & Er & E) | (E & [(Eq & Er) | (Hp & Er)])] end;
      subst; repeat split; intros; try lia; try congruence; auto.
    all: unfold VM_rnd in *; destruct (Z.eqb_spec api 2); lia. }
  {
    Intros k R st out.
    forward_if.
    2: { forward. Exists R st out. entailer!. }
    apply -> seq_assoc.
    eapply semax_seq'.
    { eapply VD_dec_ok; eassumption. }
    Intros r R' st' out'.
    eapply VD_chk_ok with (st := st) (out := out) (rnd := rnd) (stv := stv); eassumption. }
  (* after the rounds: free everything *)
  Intros R st out.
  sep_apply (VI_ddq_drop DD gv q (VI_dd (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd) e)).
  forward_call (gv, q, if eq_dec q nullval then None else Some (VI_dd (offset_val (cap + 1) (Vptr bb ob)) (wd_bytes wd) e)).
  { destruct (eq_dec q nullval); auto. }
  forward_call (gv, Vptr bd od, Some st).
  sep_apply (VB_final_merge (Vptr bs os) (Zlength (ws_bytes ws)) (Vptr bb ob) cap (Zlength (wd_bytes wd)) out
               (zbytes (wd_bytes wd)) (zbytes (ws_bytes ws)) ltac:(rep_lia) ltac:(lia) ltac:(rep_lia) Hfs Hfb).
  forward_call (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws))), Vptr bs os, gv).
  { rewrite if_false by discriminate. cancel. }
  forward_call (tarray tuchar (cap + 1 + Zlength (wd_bytes wd)), Vptr bb ob, gv).
  { rewrite if_false by discriminate. cancel. }
  (* the return: drop the frame first (a forward on the full frame costs ~900 s of Qed) *)
  eapply semax_pre with (P' := PROP () LOCAL () SEP (TT)).
  { go_lower. apply TT_right. }
  forward.
Qed.
End Body.

(* ---------- from VD_G1 to G0 (Specs_api DC DD) WG WDS: every entry of VD_G1 is found there unchanged ---------- *)

Lemma VD_make_tycontext_g_find (Vs: varspecs) (G: funspecs) i :
  Maps.PTree.get i (make_tycontext_g Vs G) =
  match initial_world.find_id i G with Some fs => Some (type_of_funspec fs) | None => Maps.PTree.get i (make_tycontext_g Vs nil) end.
Proof.
  induction G as [|[j fs] G IH]; simpl; auto.
  rewrite Maps.PTree.gsspec. unfold make_tycontext_g in IH |- *. simpl in IH.
  destruct (peq i j) as [->|Hne].
  - rewrite if_true by reflexivity. reflexivity.
  - rewrite if_false by exact Hne. exact IH.
Qed.

Lemma VD_G1_in DC DD WG WDS i fs : initial_world.find_id i (VD_G1 DC DD WG WDS) = Some fs ->
  initial_world.find_id i (G0 (Specs_api DC DD) WG WDS) = Some fs.
Proof.
  intros Hi.
  assert (Hin: In i [_quickproof_malloc; _quickproof_free; _ZSTD_isError; _ZSTD_getErrorCode; _ZSTD_decompressDCtx;
     _ZSTD_decompress_usingDict; _ZSTD_decompress_usingDDict; _ZSTD_createDCtx; _ZSTD_freeDCtx;
     _ZSTD_createDDict_byReference; _ZSTD_freeDDict; _ZSTD_DCtx_loadDictionary_byReference; _ZSTD_DCtx_refPrefix;
     _ZSTD_DCtx_refDDict; _gp_assert; _gp_assume;
     _choose; _choose_in; _exact_copy; _within_oneshot; _w_dict; _w_series]).
  { apply initial_world.find_id_e in Hi. apply (in_map fst) in Hi. exact Hi. }
  unfold G0, Imports. rewrite VD_Externals.
  repeat destruct Hin as [<-|Hin]; try contradiction; rewrite <- Hi; reflexivity.
Qed.

Definition VD_fun_ids : list ident :=
  [_quickproof_malloc; _quickproof_free;
   _ZSTD_isError; _ZSTD_getErrorCode; _ZSTD_decompress; _ZSTD_decompressDCtx; _ZSTD_decompress_usingDict;
   _ZSTD_decompress_usingDDict; _ZSTD_createDCtx; _ZSTD_createDStream; _ZSTD_freeDCtx; _ZSTD_freeDStream;
   _ZSTD_DCtx_reset; _ZSTD_initDStream; _ZSTD_DCtx_setParameter; _ZSTD_DStreamOutSize;
   _ZSTD_createDDict; _ZSTD_createDDict_byReference; _ZSTD_freeDDict;
   _ZSTD_getDictID_fromDDict; _ZSTD_getDictID_fromDict;
   _ZSTD_DCtx_loadDictionary_byReference; _ZSTD_DCtx_loadDictionary;
   _ZSTD_DCtx_refPrefix; _ZSTD_DCtx_refDDict;
   _ZSTD_decompressStream;
   _ZSTD_findFrameCompressedSize; _ZSTD_getFrameContentSize; _ZSTD_findDecompressedSize;
   _ZSTD_decompressBound; _ZSTD_frameHeaderSize; _ZSTD_getDictID_fromFrame;
   _ZSTD_isFrame; _ZSTD_isSkippableFrame; _ZSTD_getFrameHeader; _ZSTD_readSkippableFrame;
   _ZSTD_DCtx_setFormat; _ZSTD_DCtx_setMaxWindowSize; _ZSTD_resetDStream;
   _ZSTD_DCtx_loadDictionary_advanced; _ZSTD_DCtx_refPrefix_advanced;
   _ZSTD_initDStream_usingDict; _ZSTD_initDStream_usingDDict;
   _ZSTD_getDecompressedSize; _ZSTD_getFrameHeader_advanced;
   _ZSTD_decompressBegin; _ZSTD_decompressBegin_usingDict; _ZSTD_decompressBegin_usingDDict;
   _ZSTD_nextSrcSizeToDecompress; _ZSTD_nextInputType; _ZSTD_decompressContinue;
   _ZSTD_createDCtx_advancedP; _ZSTD_estimateDCtxSize; _ZSTD_estimateDStreamSize;
   _nondet_u32; _gp_assert; _gp_assume;
   _choose; _choose_in; _exact_copy; _within_oneshot; _w_dict; _w_series].

Lemma VD_G0_ids DC DD WG WDS : map fst (G0 (Specs_api DC DD) WG WDS) = VD_fun_ids.
Proof. unfold G0, Imports. rewrite VD_Externals. reflexivity. Qed.

Lemma VD_vars_funs_b : forallb (fun i => negb (id_in_list i VD_fun_ids)) (map fst Vprog) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma VD_find_id_not_in {A} i (l: list (ident * A)) : ~ In i (map fst l) -> initial_world.find_id i l = None.
Proof.
  induction l as [|[j x] l IH]; simpl; intros H; auto.
  rewrite if_false by (intro; subst; tauto). apply IH; tauto.
Qed.

Lemma VD_tyc_g_nil_in (V: varspecs) i t : Maps.PTree.get i (make_tycontext_g V nil) = Some t -> In i (map fst V).
Proof.
  unfold make_tycontext_g. simpl. induction V as [|[k u] V IH]; simpl.
  - rewrite Maps.PTree.gempty. discriminate.
  - rewrite Maps.PTree.gsspec. destruct (peq i k); auto.
Qed.

Lemma VD_var_not_fun DC DD WG WDS i t : Maps.PTree.get i (make_tycontext_g Vprog nil) = Some t ->
  initial_world.find_id i (G0 (Specs_api DC DD) WG WDS) = None.
Proof.
  intros H. apply VD_tyc_g_nil_in in H. apply VD_find_id_not_in. rewrite VD_G0_ids.
  pose proof VD_vars_funs_b as B. rewrite forallb_forall in B. specialize (B i H).
  intro Hin. apply Zstd.proof.top.MainPre6.MP_id_in_list_true_i in Hin. rewrite Hin in B. discriminate.
Qed.

Theorem main_ok3_valid_dict : MainOK.
Proof.
  intros DC DD WG WDS HWG.
  eapply semax_body_subsumption; [apply (VD_body_main DC DD WG WDS HWG) |].
  apply tycontext_sub_i99. split; intro i.
  + rewrite (VD_make_tycontext_g_find Vprog (VD_G1 DC DD WG WDS) i).
    destruct (initial_world.find_id i (VD_G1 DC DD WG WDS)) as [fs|] eqn:E.
    * rewrite (VD_make_tycontext_g_find Vprog (G0 (Specs_api DC DD) WG WDS) i).
      rewrite (VD_G1_in DC DD WG WDS i fs E). apply sub_option_refl.
    * rewrite (VD_make_tycontext_g_find Vprog (G0 (Specs_api DC DD) WG WDS) i) at 1.
      destruct (Maps.PTree.get i (make_tycontext_g Vprog [])) as [t|] eqn:EV; [|exact Logic.I].
      rewrite (VD_var_not_fun DC DD WG WDS i t EV). reflexivity.
  + rewrite !semax_prog.find_id_maketycontext_s.
    destruct (initial_world.find_id i (VD_G1 DC DD WG WDS)) as [fs|] eqn:E; [|exact Logic.I].
    rewrite (VD_G1_in DC DD WG WDS i fs E). exists fs. split; [reflexivity|]. apply funspec_sub_si_refl.
Qed.
