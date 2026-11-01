(* main of harness/any_dict.c against a small context G0 (the functions it calls), generic in DC/DD; API v3.2 version
   (adapted from MainBody_any_dict_v3.v: createDDict's EX dd, DSDDict q dd, refDDict lends dict_res/set_res and gives
   back the DDict's validity, decompressDCtx's oneshot_dctx; the context's DDict set stays empty). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import Zstd.proof.zstd.Spec_api6.
Require Import Zstd.proof.harness.any_dict.HOK_any_dict.
Require Import Zstd.proof.top.MainPre6.
Require Import Zstd.proof.harness.HCsConv.
Require Import Zstd.proof.zstd.ApiBridge.
Require Import Zstd.proof.zstd.NullBuf.
Require Import Zstd.proof.harness.ApiAfterKit.

Local Ltac expand_main_pre ::= idtac.

Local Notation HCS := HOK_any_dict.CompSpecs.
Local Notation ZCS := Zstd.units.Zstd.CS.

(* ---------- the buffers: src (n bytes, malloc'd max 1 n) and [dst | gap | dict] (one block) ---------- *)

Lemma split_bytes_ {cs: compspecs} sh m k p : 0 <= k <= m -> field_compatible (tarray tuchar m) [] p ->
  data_at_ sh (tarray tuchar m) p =
  (data_at_ sh (tarray tuchar k) p * data_at_ sh (tarray tuchar (m - k)) (offset_val k p))%logic.
Proof.
  intros Hk Hf. unfold tarray. rewrite (split2_data_at__Tarray_tuchar sh m k p Hk) by auto with field_compatible.
  rewrite field_address0_offset by auto with field_compatible. simpl. rewrite Z.mul_1_l, Z.add_0_l. reflexivity.
Qed.

(* the witnesses lent to the decoder: the slack of src's block and the gap byte between dst and dict *)
Definition slack (src: val) (n: Z) : ptr_witness :=
  pw_bytes Ews (Z.max 1 n - n) (Zrepeat Vundef (Z.max 1 n - n)) (offset_val n src).
Definition gap (buf: val) (cap: Z) : ptr_witness := pw_bytes Ews 1 [Vundef] (offset_val cap buf).
Definition Wit (src: val) (n: Z) (buf: val) (cap: Z) : list ptr_witness := [slack src n; gap buf cap].

Lemma pws_Wit src n buf cap : pws_pred (Wit src n buf cap) =
  (@data_at_ ZCS Ews (tarray tuchar (Z.max 1 n - n)) (offset_val n src) *
   @data_at_ ZCS Ews (tarray tuchar 1) (offset_val cap buf))%logic.
Proof. unfold pws_pred, Wit, map, fold_right. rewrite sepcon_emp. reflexivity. Qed.

Lemma wvp_at {cs: compspecs} sh k p i q : readable_share sh -> 0 <= i <= k -> 0 < k -> q = offset_val i p ->
  data_at_ sh (tarray tuchar k) p |-- weak_valid_pointer q.
Proof.
  intros Hsh Hi Hk ->. eapply derives_trans; [apply data_at__memory_block_cancel|].
  simpl sizeof. rewrite Z.mul_1_l, Z.max_r by lia.
  apply memory_block_weak_valid_pointer; try lia. apply readable_nonidentity; auto.
Qed.

Lemma ptr_eq b o i j : i = j -> offset_val i (Vptr b o) = offset_val j (Vptr b o).
Proof. intros ->; reflexivity. Qed.

Lemma off_off b o i j : offset_val j (offset_val i (Vptr b o)) = offset_val (i + j) (Vptr b o).
Proof. rewrite offset_offset_val. reflexivity. Qed.

Lemma off0 b o : Vptr b o = offset_val 0 (Vptr b o).
Proof. simpl. rewrite Ptrofs.add_zero. reflexivity. Qed.

Ltac ptr_eq_tac :=
  first [ reflexivity
        | rewrite ?off_off; apply ptr_eq; lia
        | match goal with |- Vptr ?b ?o = _ => rewrite (off0 b o) at 1 end; rewrite ?off_off; apply ptr_eq; lia ].

Ltac wvp_piece k i :=
  eapply (wvp_at _ k _ i); [auto | lia | lia | ptr_eq_tac].

Lemma buf_ok_src src n buf cap : isptr src -> 0 <= n -> buf_ok (Wit src n buf cap) Ews n src.
Proof.
  intros Hp Hn. destruct src; try contradiction. unfold buf_ok. rewrite pws_Wit.
  destruct (zlt 0 n).
  - apply andp_right; apply sepcon_weak_valid_pointer2.
    + wvp_piece n 0.
    + wvp_piece n n.
  - apply andp_right; apply sepcon_weak_valid_pointer1, sepcon_weak_valid_pointer1.
    + wvp_piece (Z.max 1 n - n) 0.
    + wvp_piece (Z.max 1 n - n) 0.
Qed.

Lemma buf_ok_dst src n buf cap : isptr buf -> 0 <= cap -> buf_ok (Wit src n buf cap) Ews cap buf.
Proof.
  intros Hp Hc. destruct buf; try contradiction. unfold buf_ok. rewrite pws_Wit.
  destruct (zlt 0 cap).
  - apply andp_right; apply sepcon_weak_valid_pointer2.
    + wvp_piece cap 0.
    + wvp_piece cap cap.
  - apply andp_right; apply sepcon_weak_valid_pointer1, sepcon_weak_valid_pointer2.
    + wvp_piece 1 0.
    + wvp_piece 1 0.
Qed.

Lemma buf_ok_dict src n buf cap dn : isptr buf -> 0 <= cap -> 0 <= dn ->
  buf_ok (Wit src n buf cap) Ews dn (offset_val (cap + 1) buf).
Proof.
  intros Hp Hc Hd. destruct buf; try contradiction. unfold buf_ok. rewrite pws_Wit.
  apply andp_right.
  - apply sepcon_weak_valid_pointer1, sepcon_weak_valid_pointer2. wvp_piece 1 1.
  - destruct (zlt 0 dn).
    + apply sepcon_weak_valid_pointer2. wvp_piece dn dn.
    + apply sepcon_weak_valid_pointer1, sepcon_weak_valid_pointer2. wvp_piece 1 1.
Qed.

Lemma sameblock_off buf k : isptr buf -> sameblock buf (offset_val k buf) = true.
Proof. intros Hp. destruct buf; try contradiction. simpl. unfold sameblock. apply peq_true. Qed.

Lemma dict_ptr_ok_dict src n buf cap dn : field_compatible (tarray tuchar (cap + 1 + dn)) [] buf -> 0 <= cap -> 0 <= dn ->
  dict_ptr_ok (Wit src n buf cap) Ews dn (offset_val (cap + 1) buf) Ews cap buf.
Proof.
  intros Hf Hc Hd. assert (Hp: isptr buf) by auto with field_compatible.
  left. split; [apply sameblock_off; auto|]. split; [|apply buf_ok_dict; auto].
  destruct buf; try contradiction. destruct Hf as (_ & _ & Hsz & _).
  simpl in Hsz |- *. rewrite Z.max_r in Hsz by lia.
  pose proof (Ptrofs.unsigned_range i).
  unfold Ptrofs.add. rewrite (Ptrofs.unsigned_repr (cap + 1)) by rep_lia.
  rewrite Ptrofs.unsigned_repr by rep_lia. lia.
Qed.

Lemma split3_bytes_ {cs: compspecs} sh c d p : 0 <= c -> 0 <= d ->
  field_compatible (tarray tuchar (c + 1 + d)) [] p ->
  data_at_ sh (tarray tuchar (c + 1 + d)) p =
  (data_at_ sh (tarray tuchar c) p * data_at_ sh (tarray tuchar 1) (offset_val c p) *
   data_at_ sh (tarray tuchar d) (offset_val (c + 1) p))%logic.
Proof.
  intros Hc Hd Hf.
  rewrite (split_bytes_ sh (c + 1 + d) (c + 1) p) by (auto; lia).
  replace (c + 1 + d - (c + 1)) with d by lia.
  rewrite (split_bytes_ sh (c + 1) c p).
  - replace (c + 1 - c) with 1 by lia. reflexivity.
  - lia.
  - eapply field_compatible_array_smaller0; [exact Hf | lia].
Qed.

Lemma data_at__Zrepeat {cs: compspecs} sh c p :
  data_at_ sh (tarray tuchar c) p = data_at sh (tarray tuchar c) (Zrepeat Vundef c) p.
Proof. unfold data_at_, field_at_, data_at. reflexivity. Qed.

Lemma bytes_ok_of l : Forall (fun b => 0 <= b <= Byte.max_unsigned) l -> bytes_ok l.
Proof. unfold bytes_ok, is_byte. apply Forall_impl. intros x Hx. rep_lia. Qed.

Lemma wit_fold_le src n buf cap :
  @data_at_ HCS Ews (tarray tuchar (Z.max 1 n - n)) (offset_val n src) *
  @data_at_ HCS Ews (tarray tuchar 1) (offset_val cap buf) |-- pws_pred (Wit src n buf cap).
Proof. rewrite pws_Wit, !(data_at__bytes_cs HCS ZCS). auto. Qed.

Lemma wit_fold src n buf cap :
  (@data_at_ HCS Ews (tarray tuchar (Z.max 1 n - n)) (offset_val n src) *
   @data_at_ HCS Ews (tarray tuchar 1) (offset_val cap buf))%logic = pws_pred (Wit src n buf cap).
Proof. rewrite pws_Wit, !(data_at__bytes_cs HCS ZCS). reflexivity. Qed.

(* everything back for free(src) and free(buf) *)
Lemma final_merge src n buf cap dn out v vs :
  0 <= n -> 0 <= cap -> 0 <= dn ->
  field_compatible (tarray tuchar (Z.max 1 n)) [] src ->
  field_compatible (tarray tuchar (cap + 1 + dn)) [] buf ->
  pws_pred (Wit src n buf cap) * @data_at ZCS Ews (tarray tuchar cap) out buf *
  @data_at ZCS Ews (tarray tuchar dn) v (offset_val (cap + 1) buf) *
  @data_at ZCS Ews (tarray tuchar n) vs src
  |-- @data_at_ HCS Ews (tarray tuchar (Z.max 1 n)) src * @data_at_ HCS Ews (tarray tuchar (cap + 1 + dn)) buf.
Proof.
  intros Hn Hc Hd Hfs Hfb.
  rewrite (split_bytes_ Ews (Z.max 1 n) n src) by (auto; lia).
  rewrite (split3_bytes_ Ews cap dn buf) by auto.
  rewrite pws_Wit, !(data_at__bytes_cs ZCS HCS), !(data_at_bytes_cs ZCS HCS).
  cancel.
Qed.

Lemma dict_val buf cap : isptr buf -> 0 <= cap <= 65536 ->
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

Section Main.
Variable DC : globals -> val -> dctx_st -> mpred.
Variable DD : globals -> val -> ddict_st -> mpred.


Definition G0 : funspecs :=
  [ (_quickproof_malloc, @malloc_spec' HCS); (_quickproof_free, @free_spec' HCS);
    ZSTD_isError_spec;
    ZSTD_decompressDCtx_spec DC DD; ZSTD_decompress_usingDict_spec DC; ZSTD_decompress_usingDDict_spec DC DD;
    ZSTD_createDCtx_spec DC; ZSTD_freeDCtx_spec DC;
    ZSTD_createDDict_byReference_spec DD; ZSTD_freeDDict_spec DD;
    ZSTD_getDictID_fromDDict_spec DD; ZSTD_getDictID_fromDict_spec;
    ZSTD_DCtx_loadDictionary_byReference_spec DC; ZSTD_DCtx_refPrefix_spec DC; ZSTD_DCtx_refDDict_spec DC DD;
    nondet_u32_spec; nondet_size_spec; @nondet_bytes_nn_spec HCS; gp_assert_spec;
    gp_assume_spec ].

Lemma tyc_g_isSome (V: varspecs) (G: funspecs) i : In i (map fst V) ->
  isSome (Maps.PTree.get i (make_tycontext_g V G)).
Proof.
  intros H. unfold make_tycontext_g. induction G as [|[j f] G IH]; simpl.
  - induction V as [|[k t] V IHV]; simpl in *; [contradiction|].
    rewrite Maps.PTree.gsspec. destruct (peq i k); simpl; auto.
    apply IHV. destruct H; [congruence|auto].
  - rewrite Maps.PTree.gsspec. destruct (peq i j); simpl; auto.
Qed.

Lemma vars_in_Vprog (G: funspecs) :
  Forall (fun ig : ident * globvar type => isSome (Maps.PTree.get (fst ig) (make_tycontext_g Vprog G)))
    (QPprog_vars Zstd.contracts.x_any_dict.whole_prog).
Proof.
  apply Forall_forall. intros [i g] Hin. apply tyc_g_isSome.
  unfold Vprog, QPvarspecs. rewrite map_map.
  change (In i (map (fun x : ident * globvar type => fst x)
                  (QPprog_vars Zstd.contracts.x_any_dict.whole_prog))).
  apply (in_map (fun x : ident * globvar type => fst x)) in Hin. exact Hin.
Qed.

Lemma le64_val n c : 0 <= n <= Int64.max_unsigned -> 0 <= c <= Int64.max_unsigned ->
  bool2val (negb (Int64.ltu (Int64.repr c) (Int64.repr n))) = Vint (Int.repr (if n <=? c then 1 else 0)).
Proof.
  intros Hn Hc. unfold Int64.ltu. rewrite !Int64.unsigned_repr by lia.
  destruct (zlt c n); destruct (Z.leb_spec n c); try lia; reflexivity.
Qed.

Lemma assume_le n c : Int.repr (if n <=? c then 1 else 0) <> Int.zero -> n <= c.
Proof. destruct (Z.leb_spec n c) as [Hle|Hlt]; auto. intros Hz; contradiction Hz; reflexivity. Qed.

Ltac assume_call n c :=
  forward_call (Int.repr (if n <=? c then 1 else 0));
  [ entailer!; rewrite le64_val by rep_lia; reflexivity
  | match goal with H: Int.repr (if n <=? c then 1 else 0) <> Int.zero |- _ => apply assume_le in H end ].

Lemma drop_vp (P: mpred) q : P && valid_pointer q |-- P.
Proof. apply andp_left1, derives_refl. Qed.

Lemma src_merge {cs: compspecs} sh n v src : 0 <= n -> field_compatible (tarray tuchar (Z.max 1 n)) [] src ->
  data_at sh (tarray tuchar n) v src * data_at_ sh (tarray tuchar (Z.max 1 n - n)) (offset_val n src)
  |-- data_at_ sh (tarray tuchar (Z.max 1 n)) src.
Proof.
  intros Hn Hf. rewrite (split_bytes_ sh (Z.max 1 n) n src) by (auto; lia).
  cancel.
Qed.

Definition dr2 (dict: val) (b: list Z) : dictref :=
  {| dr_src := DSRef dict; dr_raw := false; dr_once := false; dr_bytes := b |}.

(* the loop: kv is the value of k, kk the number of rounds done *)
Definition Inv (gv: globals) (api rnd: Z) (dctx buf src q: val) (cap: Z) (s b: list Z) (DDres: mpred)
    (kv kk: Z) : environ -> mpred :=
  EX st: dctx_st, EX out: list val,
  PROP (0 <= kk <= rnd; Zlength out = cap; dc_ss st = ss_init; dc_set st = nil; dc_bl st = None; kk = 0 -> st = dctx_init;
        api = 2 -> kk = 1 -> (dc_dict st = None \/
          (dc_dict st = Some (dr2 (offset_val (cap + 1) buf) b) /\ last_ok st (dr2 (offset_val (cap + 1) buf) b))))
  LOCAL (temp _k (Vint (Int.repr kv)); temp _rounds (Vint (Int.repr rnd)); temp _api (Vint (Int.repr api));
         temp _dctx dctx; temp _dst buf; temp _cap (Vlong (Int64.repr cap)); temp _src src;
         temp _n (Vlong (Int64.repr (Zlength s))); temp _dict (offset_val (cap + 1) buf);
         temp _dn (Vlong (Int64.repr (Zlength b))); temp _ddict q; temp _buf buf; gvars gv)
  SEP (mem_mgr gv; zstd_globals gv; DC gv dctx st; DDres; pws_pred (Wit src (Zlength s) buf cap);
       @data_at ZCS Ews (tarray tuchar cap) out buf;
       @data_at ZCS Ews (tarray tuchar (Zlength b)) (zbytes b) (offset_val (cap + 1) buf);
       @data_at ZCS Ews (tarray tuchar (Zlength s)) (zbytes s) src;
       @malloc_token HCS Ews (tarray tuchar (Z.max 1 (Zlength s))) src;
       @malloc_token HCS Ews (tarray tuchar (cap + 1 + Zlength b)) buf; TT).

Lemma load_ok st st' r dr : load_result st st' r dr -> is_error_code r = false ->
  st' = set_dict st (Some dr) /\ r = 0.
Proof. intros [[-> ->] | [E _]] F; [auto | congruence]. Qed.

Lemma dict_res_dr2_eq gv sh d b :
  dict_res DD gv sh (Some (dr2 d b)) = @data_at ZCS sh (tarray tuchar (Zlength b)) (zbytes b) d.
Proof. reflexivity. Qed.

Lemma dict_res_dd gv sh q dd r o b :
  dict_res DD gv sh (Some {| dr_src := DSDDict q dd; dr_raw := r; dr_once := o; dr_bytes := b |}) =
  ddict_res DD gv sh q dd.
Proof. reflexivity. Qed.

Lemma oneshot_dctx_le st s cap r out : oneshot_dctx st s cap r out -> is_error_code r = false -> r <= cap.
Proof. unfold oneshot_dctx. destruct (dc_set st); intros H; apply (proj1 H). Qed.


Lemma dict_res_ref gv sh p r o b :
  dict_res DD gv sh (Some {| dr_src := DSRef p; dr_raw := r; dr_once := o; dr_bytes := b |}) =
  @data_at ZCS sh (tarray tuchar (Zlength b)) (zbytes b) p.
Proof. reflexivity. Qed.

Lemma dc_dict_set st x : dc_dict (set_dict st x) = x.
Proof. reflexivity. Qed.

Lemma after_decode_ss st st2 l : after_decode (after_use st) st2 l -> dc_ss st2 = dc_ss st.
Proof.
  unfold after_decode, after_use. intros [-> | ->];
  destruct (dc_dict st) as [d|]; try destruct (dr_once d); reflexivity.
Qed.

Lemma after_decode_dr2 d b st2 :
  after_decode (after_use (set_dict dctx_init (Some (dr2 d b)))) st2 (Some (dr2 d b)) ->
  dc_ss st2 = ss_init /\ dc_dict st2 = Some (dr2 d b) /\ last_ok st2 (dr2 d b) /\ dc_set st2 = nil /\ dc_bl st2 = None.
Proof. unfold after_decode, last_ok. intros [-> | ->]; simpl; repeat split; auto. Qed.

(* the DDict set and the buffer-less frame survive a decoding *)
Lemma after_decode_sb st st2 l : after_decode (after_use st) st2 l -> dc_set st2 = dc_set st /\ dc_bl st2 = dc_bl st.
Proof.
  unfold after_decode, after_use. intros [-> | ->];
  destruct (dc_dict st) as [d|]; try destruct (dr_once d); split; reflexivity.
Qed.

Lemma after_decode_sb0 st st2 l : after_decode st st2 l -> dc_set st2 = dc_set st /\ dc_bl st2 = dc_bl st.
Proof. unfold after_decode. intros [-> | ->]; split; reflexivity. Qed.

Lemma refddict_init q dd st' r : refddict_result dctx_init st' r q dd ->
  r = 0 /\ st' = set_dict dctx_init (Some (ddict_ref q dd)).
Proof. unfold refddict_result. intros [[-> ->] | [H _]]; [split; reflexivity | discriminate]. Qed.

Ltac side_one :=
  match goal with
  | |- buf_ok _ _ _ (offset_val _ _) => apply buf_ok_dict; [assumption | lia | lia]
  | |- buf_ok (Wit ?p _ _ _) _ _ ?p => apply buf_ok_src; [assumption | lia]
  | |- buf_ok (Wit _ _ ?p _) _ _ ?p => apply buf_ok_dst; [assumption | lia]
  | |- dict_ptr_ok _ _ _ _ _ _ _ => apply dict_ptr_ok_dict; [eassumption | lia | lia]
  | |- dict_ptr_ok_any _ _ _ _ _ _ _ => left; apply dict_ptr_ok_dict; [eassumption | lia | lia]
  | |- dict_buf_ok _ _ _ _ _ _ =>
      unfold dict_buf_ok; cbn [dc_dict set_dict dr2 dr_src dr_bytes dd_ref dd_bytes]; apply dict_ptr_ok_dict; [eassumption | lia | lia]
  | |- ddict_buf_ok _ _ _ _ _ _ =>
      unfold ddict_buf_ok; cbn [dd_ref dd_bytes]; apply dict_ptr_ok_dict; [eassumption | lia | lia]
  | |- bytes_ok _ => apply bytes_ok_of; assumption
  | |- isptr _ => assumption
  | |- True => exact I
  | |- dc_bl _ = None => first [reflexivity | assumption]
  | |- dc_set _ = nil => first [reflexivity | assumption]
  | |- Forall _ nil => constructor
  | |- readable_share _ => auto
  | |- Zlength nil < _ => rewrite Zlength_nil; lia
  | |- _ => first [ cbn [dc_dict set_dict dctx_init dr2]; unfold last_ok; cbn [dc_last set_dict dctx_init];
                    first [left; reflexivity | right; split; [reflexivity | exact I] | assumption]
                  | idtac ]
  end.

Lemma load_err st st' r dr : load_result st st' r dr -> is_error_code r = true -> st' = set_dict st None.
Proof. intros [[-> ->] | [_ [-> _]]] F; [discriminate | auto]. Qed.

Ltac side_ok := repeat (match goal with |- _ /\ _ => split end); side_one.

(* the destination of a decompressDCtx call (a pointer) as the spec's mbuf, from main's data_at *)
Ltac dst_mbuf :=
  match goal with |- context [mbuf ?sh ?n (Zrepeat Vundef ?n) ?p] =>
    match goal with |- context [@data_at ?cs sh (tarray tuchar n) ?c p] =>
      sep_apply (@data_at_data_at_ cs sh (tarray tuchar n) c p); sep_apply (data_at__mbuf sh n p) end end.

(* the frame of a decompressDCtx call: the context's set is empty (set_res is emp) *)
Ltac pre_sep :=
  cbn [dc_set dc_dict set_dict dctx_init ddict_ref dd_ref dd_bytes]; rewrite ?set_res_nil, ?dict_res_dd, ?dict_res_ref;
  unfold ddict_res; cbn [dd_ref dd_bytes]; try dst_mbuf; cancel.

Ltac assert_call r cap E :=
  forward_call (Int.repr (if r <=? cap then 1 else 0));
  [ entailer!; rewrite le64_val by rep_lia; reflexivity
  | let Hle := fresh "Hle" in
    assert (Hle: r <= cap) by
      (match goal with
       | HO: oneshot_ok _ _ _ cap r _ |- _ => apply (proj1 HO); exact E
       | HO: oneshot_dctx _ _ cap r _ |- _ => apply (oneshot_dctx_le _ _ _ _ _ HO); exact E end);
    apply Z.leb_le in Hle;
    match goal with H: Int.repr (if _ then _ else _) = Int.zero |- _ =>
      rewrite Hle in H; apply repr_inj_unsigned in H; rep_lia end
  | ].

Lemma ptr_of_nonnull q : is_pointer_or_null q -> q <> nullval -> isptr q.
Proof. destruct q; simpl; intros; subst; auto; try contradiction. Qed.

Lemma after_decode_ss0 st st2 l : after_decode st st2 l -> dc_ss st2 = dc_ss st.
Proof. unfold after_decode. intros [-> | ->]; reflexivity. Qed.

Ltac init_inv cap buf :=
  Exists 0; unfold Inv; Exists dctx_init (Zrepeat Vundef cap);
  rewrite (data_at__Zrepeat Ews cap buf); entailer!.

Ltac incr_inv :=
  let k := fresh "k" in let st := fresh "st" in let out := fresh "out" in
  Intros k; unfold Inv; Intros st out; forward; Exists (k + 1); unfold Inv; Exists st out; entailer!.

Ltac frees gv d src s buf cap b Hfs Hfb ddw :=
  let k := fresh "k" in let st := fresh "st" in let out := fresh "out" in
  Intros k; unfold Inv; Intros st out;
  forward_call (gv, d, Some st); try (match goal with |- _ |-- _ => cancel end);
  repeat (match goal with |- context [?P && valid_pointer ?q] => sep_apply (drop_vp P q) end);
  forward_call ddw; try (match goal with |- _ |-- _ => cancel end);
  forward_call (gv, nullval, @None ddict_st); try (match goal with |- _ |-- _ => cancel end);
  sep_apply (final_merge src (Zlength s) buf cap (Zlength b) out (zbytes b) (zbytes s)
               ltac:(lia) ltac:(lia) ltac:(lia) Hfs Hfb);
  forward_call (tarray tuchar (Z.max 1 (Zlength s)), src, gv); [rewrite if_false by auto; cancel | ];
  forward_call (tarray tuchar (cap + 1 + Zlength b), buf, gv); [rewrite if_false by auto; cancel | ];
  forward.

Ltac st0 := match goal with HI: 0 = 0 -> ?x = dctx_init |- _ => specialize (HI eq_refl); subst x end.

Ltac fwd_skip := try (match goal with |- semax _ _ _ _ => forward end).

Ltac kill :=
  match goal with
  | H: false = true |- _ => discriminate H
  | H: true = false |- _ => discriminate H
  | H: ?x <> ?x |- _ => exfalso; exact (H eq_refl)
  | H: Int.repr ?x = Int.repr ?y |- _ =>
      exfalso; apply repr_inj_unsigned in H; [lia | rep_lia | rep_lia]
  | H: Int.repr ?x = Int.zero |- _ =>
      exfalso; apply repr_inj_unsigned in H; [lia | rep_lia | rep_lia]
  | H: ?x <> ?y |- _ => exfalso; apply H; reflexivity
  | H: typed_true _ _ |- _ => inv H
  | H: typed_false _ _ |- _ => inv H
  end.

Ltac ifs := first [ repeat apply -> seq_assoc; apply semax_if_seq | idtac ]; forward_if; try solve [kill | exfalso; lia | contradiction].

Lemma body_main_G0 : @semax_body Vprog G0 HCS f_main main_spec.
Proof.
  change (@semax_body Vprog G0 HCS f_main (_main, WITH gv: globals PRE [] VST.floyd.VSU.main_pre
    Zstd.contracts.x_any_dict.whole_prog tt gv POST [tint] (fun _ : environ => TT))).
  replace (fun _ : environ => @TT mpred _) with (PROP () LOCAL () SEP (@TT mpred _))
    by (extensionality rho; unfold PROPx, LOCALx, SEPx; simpl; normalize).
  start_function1.
  eapply (main_pre_InitGpred
     (Zstd.proof.zstd.Globals.zstd_globals gv *
      InitGPred (filter (fun ig => negb (id_in_list (fst ig) zstd_var_ids))
                   (Vardefs Zstd.contracts.x_any_dict.whole_prog)) gv)%logic);
    [ intros Hgv; apply main_pre_fact6; [left; reflexivity | exact Hgv]
    | reflexivity | apply vars_in_Vprog | ].
  replace (stackframe_of f_main) with (@emp (environ->mpred) _ _) by reflexivity.
  rewrite sepcon_emp.
  eapply semax_pre with (P' := PROP () LOCAL (gvars gv) SEP (mem_mgr gv; zstd_globals gv; TT)).
  { go_lower. sep_apply (create_mem_mgr gv). rewrite prop_true_andp by auto. cancel. }
  abbreviate_semax.
  forward_call tt. Intros n.
  forward_call tt. Intros a.
  forward. forward.
  assume_call n 4096.
  forward_if (temp _t'3 (Vlong (Int64.repr (Z.max 1 n)))).
  { forward. entailer!. rewrite !Int64.unsigned_repr in H2 by rep_lia. rewrite Z.max_r by lia. reflexivity. }
  { forward. entailer!. rewrite !Int64.unsigned_repr in H2 by rep_lia. replace n with 0 by lia. reflexivity. }
  forward_call (tarray tuchar (Z.max 1 n), gv).
  { simpl. rep_lia. }
  Intros src. forward.
  destruct (eq_dec src nullval) as [Hs|Hs].
  { subst src. forward_if. { forward. } { exfalso. auto. } }
  forward_if.
  { exfalso. subst. auto. }
  assert_PROP (field_compatible (tarray tuchar (Z.max 1 n)) [] src) as Hfs by entailer!.
  rewrite (split_bytes_ Ews (Z.max 1 n) n src) by (auto; lia).
  repeat flatten_sepcon_in_SEP.
  forward_call (src, n, Ews).
  Intros s.
  forward_call tt. Intros cap.
  assume_call cap 65536.
  forward_call tt. Intros dn.
  assume_call dn 4096.
  forward_call (tarray tuchar (cap + 1 + dn), gv).
  { simpl. rep_lia. }
  Intros buf.
  forward_call gv.
  Intros dctx.
  destruct (eq_dec buf nullval) as [Hb|Hb].
  { (* no output buffer: rounds = 0 *)
    subst buf.
    ifs. forward. ifs. forward. forward. forward. forward. ifs. ifs. forward.
    match goal with |- semax _ ?P _ _ => forward_loop P break: P end.
    { entailer!. }
    { ifs. forward. entailer!. }
    destruct (eq_dec dctx nullval) as [Hd|Hd].
    - forward_call (gv, dctx, @None dctx_st).
      forward_call (gv, nullval, @None ddict_st); try (match goal with |- _ |-- _ => cancel end).
      forward_call (gv, nullval, @None ddict_st); try (match goal with |- _ |-- _ => cancel end).
      sep_apply (src_merge Ews n (zbytes s) src ltac:(lia) Hfs).
      forward_call (tarray tuchar (Z.max 1 n), src, gv).
      { rewrite if_false by auto. cancel. }
      forward_call (tarray tuchar 1, nullval, gv). { rewrite if_true by auto. cancel. }
      forward.
    - sep_apply (drop_vp (DC gv dctx dctx_init) dctx).
      forward_call (gv, dctx, Some dctx_init).
      forward_call (gv, nullval, @None ddict_st); try (match goal with |- _ |-- _ => cancel end).
      forward_call (gv, nullval, @None ddict_st); try (match goal with |- _ |-- _ => cancel end).
      sep_apply (src_merge Ews n (zbytes s) src ltac:(lia) Hfs).
      forward_call (tarray tuchar (Z.max 1 n), src, gv).
      { rewrite if_false by auto. cancel. }
      forward_call (tarray tuchar 1, nullval, gv). { rewrite if_true by auto. cancel. }
      forward. }
  destruct (eq_dec buf nullval) as [?|_]; [contradiction|]. repeat flatten_sepcon_in_SEP.
  assert_PROP (field_compatible (tarray tuchar (cap + 1 + dn)) [] buf) as Hfb by entailer!.
  destruct (eq_dec dctx nullval) as [Hd|Hd].
  { (* no context: rounds = 0 *)
    subst dctx.
    ifs. forward. ifs. forward. forward. forward. forward. ifs. forward. ifs. forward.
    match goal with |- semax _ ?P _ _ => forward_loop P break: P end.
    { entailer!. }
    { ifs. forward. entailer!. }
    forward_call (gv, nullval, @None dctx_st); try (match goal with |- _ |-- _ => cancel end).
    forward_call (gv, nullval, @None ddict_st); try (match goal with |- _ |-- _ => cancel end).
    forward_call (gv, nullval, @None ddict_st); try (match goal with |- _ |-- _ => cancel end).
    sep_apply (src_merge Ews n (zbytes s) src ltac:(lia) Hfs).
    forward_call (tarray tuchar (Z.max 1 n), src, gv).
    { rewrite if_false by auto. cancel. }
    forward_call (tarray tuchar (cap + 1 + dn), buf, gv).
    { rewrite if_false by auto. cancel. }
    forward. }
  destruct (eq_dec dctx nullval) as [?|_]; [contradiction|].
  subst n.
  assert (Hm: Int.modu (Int.repr a) (Int.repr 5) = Int.repr (a mod 5)).
  { unfold Int.modu. rewrite !Int.unsigned_repr by rep_lia. reflexivity. }
  rewrite Hm. clear Hm.
  assert (Hapi: 0 <= a mod 5 < 5) by (apply Z.mod_pos_bound; lia).
  forget (a mod 5) as api.
  destruct dctx as [| | | | | bd od]; try (simpl in PNdctx; subst; contradiction).
  assert (Hpb: isptr buf) by auto with field_compatible.
  assert (Hps: isptr src) by auto with field_compatible.
  ifs. forward. ifs. ifs.
  all: forward; forward; forward; forward; forward; ifs; forward; ifs.
  all: rewrite dict_val by first [exact Hpb | lia].
  all: rewrite (split3_bytes_ Ews cap dn buf) by first [exact Hfb | lia].
  all: repeat flatten_sepcon_in_SEP.
  all: forward_call (offset_val (cap + 1) buf, dn, Ews).
  all: Intros b.
  all: subst dn.
  all: sep_apply (wit_fold_le src (Zlength s) buf cap).
  all: rewrite !(data_at_bytes_cs HCS ZCS), !(data_at__bytes_cs HCS ZCS).
  all: forward_call (Ews, offset_val (cap + 1) buf, b).
  all: try (apply bytes_ok_of; assumption).
  all: ifs.
  - (* api = 2: loadDictionary_byReference, two decompressions *)
    subst api. forward. ifs. forward.
    sep_apply (drop_vp (DC gv (Vptr bd od) dctx_init) (Vptr bd od)).
    forward_loop (EX k: Z, Inv gv 2 2 (Vptr bd od) buf src nullval cap s b emp k k)
      continue: (EX k: Z, Inv gv 2 2 (Vptr bd od) buf src nullval cap s b emp k (k + 1))
      break: (EX k: Z, Inv gv 2 2 (Vptr bd od) buf src nullval cap s b emp k k).
    { Exists 0. unfold Inv. Exists dctx_init (Zrepeat Vundef cap).
      rewrite (data_at__Zrepeat Ews cap buf). entailer!. }
    2: { Intros k. unfold Inv. Intros st out. forward. Exists (k + 1). unfold Inv. Exists st out. entailer!. }
    2: { Intros k. unfold Inv. Intros st out.
         forward_call (gv, Vptr bd od, Some st); try (match goal with |- _ |-- _ => cancel end).
         forward_call (gv, nullval, @None ddict_st); try (match goal with |- _ |-- _ => cancel end).
         forward_call (gv, nullval, @None ddict_st); try (match goal with |- _ |-- _ => cancel end).
         sep_apply (final_merge src (Zlength s) buf cap (Zlength b) out (zbytes b) (zbytes s)
                      ltac:(lia) ltac:(lia) ltac:(lia) Hfs Hfb).
         forward_call (tarray tuchar (Z.max 1 (Zlength s)), src, gv).
         { rewrite if_false by auto. cancel. }
         forward_call (tarray tuchar (cap + 1 + Zlength b), buf, gv).
         { rewrite if_false by auto. cancel. }
         forward. }
    Intros k. unfold Inv. Intros st out.
    ifs.
    2: { forward. Exists k. unfold Inv. Exists st out. entailer!. }
    ifs. ifs. forward. ifs.
    { (* k = 0: load the dictionary, decompress *)
      subst k. st0. ifs.
      forward_call (Wit src (Zlength s) buf cap, gv, Vptr bd od, dctx_init, Ews, offset_val (cap + 1) buf, b).
      { side_ok. }
      Intros vret. destruct vret as [r st']. simpl fst in *; simpl snd in *.
      forward.
      forward_call r.
      destruct (is_error_code r) eqn:Er; ifs.
      2: { api_init; match goal with HL: load_result _ _ _ _ |- _ => destruct (load_ok _ _ _ _ HL Er) as [-> ->] end.
           forward_call (Wit src (Zlength s) buf cap, gv, Vptr bd od,
             set_dict dctx_init (Some (dr2 (offset_val (cap + 1) buf) b)), Ews, Ews, buf, cap, Ews, src, s).
           all: try solve [pre_sep | side_ok].
           Intros vret. destruct vret as [[r2 out2] st2]. simpl fst in *; simpl snd in *. rewrite mbuf_isptr by auto.
           rewrite dc_dict_set, dict_res_dr2_eq.
           forward_call r2.
           destruct (is_error_code r2) eqn:Er2; ifs.
           all: api_init; match goal with HA: after_decode _ _ _ |- _ =>
             rewrite dc_dict_set in HA; destruct (after_decode_dr2 _ _ _ HA) as (Hss & Hdd & Hlo & Hse & Hbl) end.
           2: assert_call r2 cap Er2.
           all: fwd_skip; Exists 0; unfold Inv; Exists st2 out2; entailer!. }
      (* the load failed *)
      api_init; match goal with HL: load_result _ _ _ _ |- _ => rewrite (load_err _ _ _ _ HL Er) in * end.
      forward_call r. rewrite Er. ifs.
      fwd_skip. Exists 0. unfold Inv. Exists (set_dict dctx_init None) out. entailer!. }
    (* k = 1: the second decompression with the sticky dictionary *)
    assert (k = 1) by lia. subst k.
    forward_call 0. ifs.
    destruct st as [d0 stb0 ss0 last0 par0 set0 bl0 mem0 ex0]. cbn [dc_dict dc_ss dc_last dc_set dc_bl] in *. subst ss0 set0 bl0.
    match goal with H2: 2 = 2 -> 1 = 1 -> _ |- _ => destruct (H2 eq_refl eq_refl) as [-> | [-> Hlo0]] end.
    + forward_call (Wit src (Zlength s) buf cap, gv, Vptr bd od,
        {| dc_dict := None; dc_stable := stb0; dc_ss := ss_init; dc_last := last0;
           dc_par := par0; dc_set := nil; dc_bl := None; dc_mem := mem0; dc_ex := ex0 |},
        Ews, Ews, buf, cap, Ews, src, s).
      all: try solve [pre_sep | side_ok].
      Intros vret. destruct vret as [[r2 out2] st2]. simpl fst in *; simpl snd in *. rewrite mbuf_isptr by auto.
      forward_call r2.
      destruct (is_error_code r2) eqn:Er2; ifs.
      2: assert_call r2 cap Er2.
      all: api_init; match goal with HA: after_decode _ _ _ |- _ => pose proof (after_decode_sb _ _ _ HA) as [HS1 HS2]; apply after_decode_ss in HA; cbn [dc_ss dc_set dc_bl] in HA, HS1, HS2 end.
      all: fwd_skip; Exists 1; unfold Inv; Exists st2 out2; entailer!.
    + forward_call (Wit src (Zlength s) buf cap, gv, Vptr bd od,
        {| dc_dict := Some (dr2 (offset_val (cap + 1) buf) b); dc_stable := stb0; dc_ss := ss_init; dc_last := last0;
           dc_par := par0; dc_set := nil; dc_bl := None; dc_mem := mem0; dc_ex := ex0 |},
        Ews, Ews, buf, cap, Ews, src, s).
      all: try solve [pre_sep | side_ok].
      Intros vret. destruct vret as [[r2 out2] st2]. simpl fst in *; simpl snd in *. rewrite mbuf_isptr by auto.
      cbn [dc_dict]. rewrite dict_res_dr2_eq.
      forward_call r2.
      destruct (is_error_code r2) eqn:Er2; ifs.
      2: assert_call r2 cap Er2.
      all: api_init; match goal with HA: after_decode _ _ _ |- _ => pose proof (after_decode_sb _ _ _ HA) as [HS1 HS2]; apply after_decode_ss in HA; cbn [dc_ss dc_set dc_bl] in HA, HS1, HS2 end.
      all: fwd_skip; Exists 1; unfold Inv; Exists st2 out2; entailer!.
  - (* api = 1: createDDict_byReference + decompress_usingDDict *)
    subst api. forward. ifs.
    forward_call (Wit src (Zlength s) buf cap, gv, Ews, offset_val (cap + 1) buf, b).
    { side_ok. }
    Intros vret. destruct vret as [q [db0 dr0 dbuf dld]]. simpl fst in *; simpl snd in *. cbn [dd_bytes dd_ref] in *; subst db0 dr0.
    sep_apply (drop_vp (DC gv (Vptr bd od) dctx_init) (Vptr bd od)).
    destruct (eq_dec q nullval) as [Hq|Hq].
    + (* no DDict: rounds = 0 *)
      subst q. ifs. forward. forward.
      forward_loop (EX k: Z, Inv gv 1 0 (Vptr bd od) buf src nullval cap s b emp k k)
        continue: (EX k: Z, Inv gv 1 0 (Vptr bd od) buf src nullval cap s b emp k (k + 1))
        break: (EX k: Z, Inv gv 1 0 (Vptr bd od) buf src nullval cap s b emp k k).
      { init_inv cap buf. }
      { Intros k. unfold Inv. Intros st out. ifs. forward. Exists k. unfold Inv. Exists st out. entailer!. }
      { incr_inv. }
      frees gv (Vptr bd od) src s buf cap b Hfs Hfb (gv, nullval, @None ddict_st).
    + ifs.
      sep_apply (drop_vp (DD gv q {| dd_bytes := b; dd_ref := Some (offset_val (cap + 1) buf); dd_buf := dbuf; dd_ld := dld |}) q).
      forward_call (gv, q, {| dd_bytes := b; dd_ref := Some (offset_val (cap + 1) buf); dd_buf := dbuf; dd_ld := dld |}).
      forward.
      forward_loop (EX k: Z, Inv gv 1 1 (Vptr bd od) buf src q cap s b
                      (DD gv q {| dd_bytes := b; dd_ref := Some (offset_val (cap + 1) buf); dd_buf := dbuf; dd_ld := dld |} && valid_pointer q) k k)
        continue: (EX k: Z, Inv gv 1 1 (Vptr bd od) buf src q cap s b
                      (DD gv q {| dd_bytes := b; dd_ref := Some (offset_val (cap + 1) buf); dd_buf := dbuf; dd_ld := dld |} && valid_pointer q) k (k + 1))
        break: (EX k: Z, Inv gv 1 1 (Vptr bd od) buf src q cap s b
                      (DD gv q {| dd_bytes := b; dd_ref := Some (offset_val (cap + 1) buf); dd_buf := dbuf; dd_ld := dld |} && valid_pointer q) k k).
      { init_inv cap buf. }
      2: { incr_inv. }
      2: { frees gv (Vptr bd od) src s buf cap b Hfs Hfb
             (gv, q, Some {| dd_bytes := b; dd_ref := Some (offset_val (cap + 1) buf); dd_buf := dbuf; dd_ld := dld |}). }
      Intros k. unfold Inv. Intros st out. ifs.
      2: { forward. Exists k. unfold Inv. Exists st out. entailer!. }
      assert (k = 0) by lia. subst k. st0.
      ifs. ifs.
      forward_call (Wit src (Zlength s) buf cap, gv, Vptr bd od, dctx_init, Ews, buf, cap, Ews, src, s, Ews, q,
                    {| dd_bytes := b; dd_ref := Some (offset_val (cap + 1) buf); dd_buf := dbuf; dd_ld := dld |}).
      all: try solve [unfold ddict_res; cbn [dd_ref dd_bytes]; cancel | side_ok].
      Intros vret. destruct vret as [[r2 out2] st2]. simpl fst in *; simpl snd in *.
      unfold ddict_res; cbn [dd_ref dd_bytes]. repeat flatten_sepcon_in_SEP.
      forward_call r2.
      destruct (is_error_code r2) eqn:Er2; ifs.
      2: assert_call r2 cap Er2.
      all: api_init; match goal with HA: after_decode _ _ _ |- _ => pose proof (after_decode_sb0 _ _ _ HA) as [HS1 HS2]; apply after_decode_ss0 in HA; cbn [dc_ss dctx_init dc_set dc_bl] in HA, HS1, HS2 end.
      all: fwd_skip; Exists 0; unfold Inv; Exists st2 out2; entailer!.
  - (* api = 3 or api in 0, 4 *)
    forward. destruct (zeq api 3) as [->|Hn3]; ifs.
    + (* api = 3: createDDict_byReference + refDDict + decompressDCtx *)
      forward_call (Wit src (Zlength s) buf cap, gv, Ews, offset_val (cap + 1) buf, b).
      { side_ok. }
      Intros vret. destruct vret as [q [db0 dr0 dbuf dld]]. simpl fst in *; simpl snd in *. cbn [dd_bytes dd_ref] in *; subst db0 dr0.
      sep_apply (drop_vp (DC gv (Vptr bd od) dctx_init) (Vptr bd od)).
      destruct (eq_dec q nullval) as [Hq|Hq].
      * subst q. ifs. forward. forward.
        forward_loop (EX k: Z, Inv gv 3 0 (Vptr bd od) buf src nullval cap s b emp k k)
          continue: (EX k: Z, Inv gv 3 0 (Vptr bd od) buf src nullval cap s b emp k (k + 1))
          break: (EX k: Z, Inv gv 3 0 (Vptr bd od) buf src nullval cap s b emp k k).
        { init_inv cap buf. }
        { Intros k. unfold Inv. Intros st out. ifs. forward. Exists k. unfold Inv. Exists st out. entailer!. }
        { incr_inv. }
        frees gv (Vptr bd od) src s buf cap b Hfs Hfb (gv, nullval, @None ddict_st).
      * ifs.
        assert (Hpq: isptr q) by (apply ptr_of_nonnull; auto).
        sep_apply (drop_vp (DD gv q {| dd_bytes := b; dd_ref := Some (offset_val (cap + 1) buf); dd_buf := dbuf; dd_ld := dld |}) q).
        forward_call (gv, q, {| dd_bytes := b; dd_ref := Some (offset_val (cap + 1) buf); dd_buf := dbuf; dd_ld := dld |}).
        forward.
        forward_loop (EX k: Z, Inv gv 3 1 (Vptr bd od) buf src q cap s b (DD gv q {| dd_bytes := b; dd_ref := Some (offset_val (cap + 1) buf); dd_buf := dbuf; dd_ld := dld |} && valid_pointer q) k k)
          continue: (EX k: Z, Inv gv 3 1 (Vptr bd od) buf src q cap s b (DD gv q {| dd_bytes := b; dd_ref := Some (offset_val (cap + 1) buf); dd_buf := dbuf; dd_ld := dld |} && valid_pointer q) k (k + 1))
          break: (EX k: Z, Inv gv 3 1 (Vptr bd od) buf src q cap s b (DD gv q {| dd_bytes := b; dd_ref := Some (offset_val (cap + 1) buf); dd_buf := dbuf; dd_ld := dld |} && valid_pointer q) k k).
        { init_inv cap buf. }
        2: { incr_inv. }
        2: { frees gv (Vptr bd od) src s buf cap b Hfs Hfb (gv, q, Some {| dd_bytes := b; dd_ref := Some (offset_val (cap + 1) buf); dd_buf := dbuf; dd_ld := dld |}). }
        Intros k. unfold Inv. Intros st out. ifs.
        2: { forward. Exists k. unfold Inv. Exists st out. entailer!. }
        assert (k = 0) by lia. subst k. st0.
        ifs. ifs. forward. ifs. ifs. ifs.
        sep_apply (drop_vp (DD gv q {| dd_bytes := b; dd_ref := Some (offset_val (cap + 1) buf); dd_buf := dbuf; dd_ld := dld |}) q).
        forward_call (gv, Vptr bd od, dctx_init, q, {| dd_bytes := b; dd_ref := Some (offset_val (cap + 1) buf); dd_buf := dbuf; dd_ld := dld |}, Ews).
        { cbn [dc_dict dc_set dctx_init]. rewrite set_res_nil. unfold dict_res.
          destruct (eq_dec q nullval); [subst q; contradiction|]. cancel. }
        Intros vret. destruct vret as [rq stq]. simpl fst in *; simpl snd in *.
        cbn [dc_dict dc_set dctx_init]. rewrite set_res_nil. unfold dict_res.
        assert (Nq: q <> nullval) by (destruct q; try contradiction; discriminate).
        api_init. destruct (eq_dec q nullval); [contradiction|].
        match goal with HR: refddict_result _ _ _ _ _ |- _ => destruct (refddict_init _ _ _ _ HR) as [-> ->] end.
        unfold ddict_ref; cbn [dd_ref dd_bytes].
        forward. forward.
        forward_call 0. ifs.
        forward_call (Wit src (Zlength s) buf cap, gv, Vptr bd od,
          set_dict dctx_init (Some {| dr_src := DSDDict q {| dd_bytes := b; dd_ref := Some (offset_val (cap + 1) buf); dd_buf := dbuf; dd_ld := dld |}; dr_raw := false;
                                      dr_once := false; dr_bytes := b |}), Ews, Ews, buf, cap, Ews, src, s).
        all: try solve [pre_sep | side_ok].
        Intros vret. destruct vret as [[r2 out2] st2]. simpl fst in *; simpl snd in *. rewrite mbuf_isptr by auto.
        rewrite dc_dict_set, dict_res_dd. unfold ddict_res; cbn [dd_ref dd_bytes]. repeat flatten_sepcon_in_SEP.
        forward_call r2.
        destruct (is_error_code r2) eqn:Er2; ifs.
        2: assert_call r2 cap Er2.
        all: api_init; match goal with HA: after_decode _ _ _ |- _ => pose proof (after_decode_sb _ _ _ HA) as [HS1 HS2]; apply after_decode_ss in HA; cbn [dc_ss set_dict dctx_init dc_set dc_bl] in HA, HS1, HS2 end.
        all: fwd_skip; Exists 0; unfold Inv; Exists st2 out2; entailer!.
    + (* api = 0 or 4 *)
      forward.
      sep_apply (drop_vp (DC gv (Vptr bd od) dctx_init) (Vptr bd od)).
      forward_loop (EX k: Z, Inv gv api 1 (Vptr bd od) buf src nullval cap s b emp k k)
        continue: (EX k: Z, Inv gv api 1 (Vptr bd od) buf src nullval cap s b emp k (k + 1))
        break: (EX k: Z, Inv gv api 1 (Vptr bd od) buf src nullval cap s b emp k k).
      { init_inv cap buf. }
      2: { incr_inv. }
      2: { frees gv (Vptr bd od) src s buf cap b Hfs Hfb (gv, nullval, @None ddict_st). }
      Intros k. unfold Inv. Intros st out. ifs.
      2: { forward. Exists k. unfold Inv. Exists st out. entailer!. }
      assert (k = 0) by lia. subst k. st0.
      ifs.
      * (* api = 0: decompress_usingDict *)
        forward_call (Wit src (Zlength s) buf cap, gv, Vptr bd od, dctx_init, Ews, buf, cap, Ews, src, s,
                      Ews, offset_val (cap + 1) buf, b).
        { side_ok. }
        Intros vret. destruct vret as [[r2 out2] st2]. simpl fst in *; simpl snd in *.
        forward_call r2.
        destruct (is_error_code r2) eqn:Er2; ifs.
        2: assert_call r2 cap Er2.
        all: api_init; match goal with HA: after_decode _ _ _ |- _ => pose proof (after_decode_sb0 _ _ _ HA) as [HS1 HS2]; apply after_decode_ss0 in HA; cbn [dc_ss dctx_init dc_set dc_bl] in HA, HS1, HS2 end.
        all: fwd_skip; Exists 0; unfold Inv; Exists st2 out2; entailer!.
      * (* api = 4: refPrefix + decompressDCtx *)
        ifs. forward. ifs. ifs. ifs.
        forward_call (Wit src (Zlength s) buf cap, gv, Vptr bd od, dctx_init, Ews, offset_val (cap + 1) buf, b).
        { side_ok. }
        Intros vret. destruct vret as [r st']. simpl fst in *; simpl snd in *.
        forward. forward.
        forward_call r.
        destruct (is_error_code r) eqn:Er; ifs.
        2: { api_init; match goal with HL: load_result _ _ _ _ |- _ => destruct (load_ok _ _ _ _ HL Er) as [-> ->] end.
             forward_call (Wit src (Zlength s) buf cap, gv, Vptr bd od,
               set_dict dctx_init (Some {| dr_src := DSRef (offset_val (cap + 1) buf); dr_raw := true;
                                           dr_once := true; dr_bytes := b |}), Ews, Ews, buf, cap, Ews, src, s).
             all: try solve [pre_sep | side_ok].
             Intros vret. destruct vret as [[r2 out2] st2]. simpl fst in *; simpl snd in *. rewrite mbuf_isptr by auto.
             rewrite dc_dict_set, dict_res_ref.
             forward_call r2.
             destruct (is_error_code r2) eqn:Er2; ifs.
             2: assert_call r2 cap Er2.
             all: api_init; match goal with HA: after_decode _ _ _ |- _ => pose proof (after_decode_sb _ _ _ HA) as [HS1 HS2]; apply after_decode_ss in HA; cbn [dc_ss set_dict dctx_init dc_set dc_bl] in HA, HS1, HS2 end.
             all: fwd_skip; Exists 0; unfold Inv; Exists st2 out2; entailer!. }
        api_init; match goal with HL: load_result _ _ _ _ |- _ => rewrite (load_err _ _ _ _ HL Er) in * end.
        forward_call r. rewrite Er. ifs.
        fwd_skip. Exists 0. unfold Inv. Exists (set_dict dctx_init None) out. entailer!.
Qed.
End Main.

(* ---------- from G0 to Gprog (Specs_api DC DD) [] (recipe) ---------- *)

Definition G_ext : funspecs :=
  [nondet_u32_spec; nondet_size_spec; @nondet_bytes_nn_spec HCS; gp_assert_spec; gp_assume_spec].

Lemma Externals_eq : Externals = G_ext.
Proof.
  unfold Externals, present, env_harness, filter.
  repeat match goal with |- context [id_in_list ?i ?l] =>
    let b := eval lazy in (id_in_list i l) in change (id_in_list i l) with b end.
  reflexivity.
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

(* A name that is not a function of G keeps its type of the global variables: stated for an abstract G, so that
   the rewriting never compares the concrete function list with the empty one (which unfolds the specifications). *)
Lemma sub_none_G (V: varspecs) (G: funspecs) i :
  (forall t, Maps.PTree.get i (make_tycontext_g V nil) = Some t -> initial_world.find_id i G = None) ->
  tycontext.sub_option (Maps.PTree.get i (make_tycontext_g V nil)) (Maps.PTree.get i (make_tycontext_g V G)).
Proof.
  intros H. rewrite (make_tycontext_g_find V G i).
  destruct (Maps.PTree.get i (make_tycontext_g V nil)) as [t|] eqn:EV; [|exact Logic.I].
  rewrite (H t eq_refl). reflexivity.
Qed.

Definition Lg : list ident :=
  [_quickproof_malloc; _quickproof_free;
   _ZSTD_isError; _ZSTD_getErrorCode; _ZSTD_decompress;
   _ZSTD_decompressDCtx; _ZSTD_decompress_usingDict;
   _ZSTD_decompress_usingDDict; _ZSTD_createDCtx; _ZSTD_createDStream;
   _ZSTD_freeDCtx; _ZSTD_freeDStream; _ZSTD_DCtx_reset;
   _ZSTD_initDStream; _ZSTD_DCtx_setParameter; _ZSTD_DStreamOutSize;
   _ZSTD_createDDict; _ZSTD_createDDict_byReference; _ZSTD_freeDDict;
   _ZSTD_getDictID_fromDDict; _ZSTD_getDictID_fromDict;
   _ZSTD_DCtx_loadDictionary_byReference; _ZSTD_DCtx_loadDictionary;
   _ZSTD_DCtx_refPrefix; _ZSTD_DCtx_refDDict; _ZSTD_decompressStream;
   _ZSTD_findFrameCompressedSize; _ZSTD_getFrameContentSize;
   _ZSTD_findDecompressedSize; _ZSTD_decompressBound;
   _ZSTD_frameHeaderSize; _ZSTD_getDictID_fromFrame; _ZSTD_isFrame;
   _ZSTD_isSkippableFrame; _ZSTD_getFrameHeader;
   _ZSTD_readSkippableFrame;
   _ZSTD_DCtx_setFormat; _ZSTD_DCtx_setMaxWindowSize; _ZSTD_resetDStream;
   _ZSTD_DCtx_loadDictionary_advanced; _ZSTD_DCtx_refPrefix_advanced;
   _ZSTD_initDStream_usingDict; _ZSTD_initDStream_usingDDict;
   _ZSTD_getDecompressedSize; _ZSTD_getFrameHeader_advanced;
   _ZSTD_decompressBegin; _ZSTD_decompressBegin_usingDict; _ZSTD_decompressBegin_usingDDict;
   _ZSTD_nextSrcSizeToDecompress; _ZSTD_nextInputType; _ZSTD_decompressContinue;
   _ZSTD_createDCtx_advancedP; _ZSTD_estimateDCtxSize; _ZSTD_estimateDStreamSize;
   _nondet_u32; _nondet_size; _nondet_bytes; _gp_assert; _gp_assume; _main].

Lemma Gprog_ids DC DD : map fst (Gprog (Specs_api DC DD) []) = Lg.
Proof. unfold Gprog, Imports. rewrite Externals_eq. reflexivity. Qed.

(* no function of Gprog is a global variable of the program *)
Lemma Lg_not_var :
  forallb (fun i => match Maps.PTree.get i (make_tycontext_g Vprog nil) with None => true | Some _ => false end) Lg
  = true.
Proof. vm_compute. reflexivity. Qed.

Lemma G0_entries DC DD :
  Forall (fun e => initial_world.find_id (fst e) (Gprog (Specs_api DC DD) []) = Some (snd e)) (G0 DC DD).
Proof.
  unfold Gprog, Imports. rewrite Externals_eq.
  repeat constructor; reflexivity.
Qed.

Lemma G0_in_Gprog DC DD i fs :
  initial_world.find_id i (G0 DC DD) = Some fs -> initial_world.find_id i (Gprog (Specs_api DC DD) []) = Some fs.
Proof.
  intros Hi. apply initial_world.find_id_e in Hi.
  pose proof (G0_entries DC DD) as HF. rewrite Forall_forall in HF.
  exact (HF (i, fs) Hi).
Qed.

Lemma any_dict_harness_ok DC DD : HarnessOK (Specs_api DC DD) [].
Proof.
  split.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    exists f_main. split; [reflexivity|]. split; [reflexivity|].
    eapply semax_body_subsumption; [apply (body_main_G0 DC DD) |].
    apply tycontext_sub_i99. split; intro i.
    + rewrite (make_tycontext_g_find Vprog (G0 DC DD) i).
      destruct (initial_world.find_id i (G0 DC DD)) as [fs|] eqn:E.
      * rewrite (make_tycontext_g_find Vprog (Gprog (Specs_api DC DD) []) i).
        rewrite (G0_in_Gprog DC DD i fs E). apply sub_option_refl.
      * apply (sub_none_G Vprog (Gprog (Specs_api DC DD) []) i). intros t Et.
        destruct (initial_world.find_id i (Gprog (Specs_api DC DD) [])) as [f|] eqn:E2; [|reflexivity].
        assert (Hin: In i Lg).
        { rewrite <- (Gprog_ids DC DD). apply in_map_iff. exists (i, f). split; [reflexivity|].
          apply initial_world.find_id_e; exact E2. }
        pose proof Lg_not_var as HL. rewrite forallb_forall in HL. specialize (HL i Hin).
        rewrite Et in HL. discriminate.
    + rewrite !semax_prog.find_id_maketycontext_s.
      destruct (initial_world.find_id i (G0 DC DD)) as [fs|] eqn:E; [|exact Logic.I].
      rewrite (G0_in_Gprog DC DD i fs E). exists fs. split; [reflexivity|]. apply funspec_sub_si_refl.
Qed.
