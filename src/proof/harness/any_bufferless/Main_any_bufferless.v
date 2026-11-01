(* The harness obligation of harness/any_bufferless.c under the decoder's API v3.
   A law added by a later revision of the contract: templates in the any_* proofs of the other laws. *)
Require Import VST.floyd.proofauto.
Require Export Zstd.proof.zstd.Spec_api6.
Require Export Zstd.proof.harness.any_bufferless.HOK_any_bufferless.
Require Zstd.proof.top.MainPre6.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import Zstd.proof.top.MainPre6.
Require Import Zstd.proof.harness.HCsConv.
Require Import Zstd.proof.harness.ApiAfterKit.

Local Ltac expand_main_pre ::= idtac.

Local Notation HCS := HOK_any_bufferless.CompSpecs.
Local Notation ZCS := Zstd.units.Zstd.CS.

(* ---------- byte arrays and pointer witnesses ---------- *)

Lemma ABL_split_bytes_ {cs: compspecs} sh m k p : 0 <= k <= m -> field_compatible (tarray tuchar m) [] p ->
  data_at_ sh (tarray tuchar m) p =
  (data_at_ sh (tarray tuchar k) p * data_at_ sh (tarray tuchar (m - k)) (offset_val k p))%logic.
Proof.
  intros Hk Hf. unfold tarray. rewrite (split2_data_at__Tarray_tuchar sh m k p Hk) by auto with field_compatible.
  rewrite field_address0_offset by auto with field_compatible. simpl. rewrite Z.mul_1_l, Z.add_0_l. reflexivity.
Qed.

Lemma ABL_split3_bytes_ {cs: compspecs} sh c d p : 0 <= c -> 0 <= d ->
  field_compatible (tarray tuchar (c + 1 + d)) [] p ->
  data_at_ sh (tarray tuchar (c + 1 + d)) p =
  (data_at_ sh (tarray tuchar c) p * data_at_ sh (tarray tuchar 1) (offset_val c p) *
   data_at_ sh (tarray tuchar d) (offset_val (c + 1) p))%logic.
Proof.
  intros Hc Hd Hf.
  rewrite (ABL_split_bytes_ sh (c + 1 + d) (c + 1) p) by (auto; lia).
  replace (c + 1 + d - (c + 1)) with d by lia.
  rewrite (ABL_split_bytes_ sh (c + 1) c p).
  - replace (c + 1 - c) with 1 by lia. reflexivity.
  - lia.
  - eapply field_compatible_array_smaller0; [exact Hf | lia].
Qed.

Lemma ABL_data_at__Zrepeat {cs: compspecs} sh c p :
  data_at_ sh (tarray tuchar c) p = data_at sh (tarray tuchar c) (Zrepeat Vundef c) p.
Proof. unfold data_at_, field_at_, data_at. reflexivity. Qed.

Lemma ABL_wvp_at {cs: compspecs} sh k p i q : readable_share sh -> 0 <= i <= k -> 0 < k -> q = offset_val i p ->
  data_at_ sh (tarray tuchar k) p |-- weak_valid_pointer q.
Proof.
  intros Hsh Hi Hk ->. eapply derives_trans; [apply data_at__memory_block_cancel|].
  simpl sizeof. rewrite Z.mul_1_l, Z.max_r by lia.
  apply memory_block_weak_valid_pointer; try lia. apply readable_nonidentity; auto.
Qed.

Lemma ABL_wvp_at1 {cs: compspecs} sh p i q : readable_share sh -> 0 <= i <= 1 -> q = offset_val i p ->
  data_at sh (tarray tuchar 1) [Vundef] p |-- weak_valid_pointer q.
Proof.
  intros Hsh Hi Hq. change [Vundef] with (Zrepeat Vundef 1). rewrite <- ABL_data_at__Zrepeat.
  eapply ABL_wvp_at; eauto; lia.
Qed.

Lemma ABL_ptr_eq b o i j : i = j -> offset_val i (Vptr b o) = offset_val j (Vptr b o).
Proof. intros ->; reflexivity. Qed.

Lemma ABL_off_off b o i j : offset_val j (offset_val i (Vptr b o)) = offset_val (i + j) (Vptr b o).
Proof. rewrite offset_offset_val. reflexivity. Qed.

Lemma ABL_off0 b o : Vptr b o = offset_val 0 (Vptr b o).
Proof. simpl. rewrite Ptrofs.add_zero. reflexivity. Qed.

Ltac ABL_ptr_eq_tac :=
  first [ reflexivity
        | rewrite ?ABL_off_off; apply ABL_ptr_eq; lia
        | match goal with |- Vptr ?b ?o = _ => rewrite (ABL_off0 b o) at 1 end; rewrite ?ABL_off_off; apply ABL_ptr_eq; lia ].

(* the gap byte between dst and dict, and the unused byte of ib = malloc(1) for an empty piece *)
Definition gapw (buf: val) (cap: Z) : ptr_witness := pw_bytes Ews 1 [Vundef] (offset_val cap buf).
Definition ibw (len: Z) (ib: val) : list ptr_witness := if zeq len 0 then [pw_bytes Ews 1 [Vundef] ib] else [].

Lemma ABL_pws1 w : pws_pred [w] = pw_pred w.
Proof. unfold pws_pred. simpl. apply sepcon_emp. Qed.

Lemma ABL_pws_cons w l : pws_pred (w :: l) = (pw_pred w * pws_pred l)%logic.
Proof. reflexivity. Qed.

Lemma ABL_buf_ok_dst l buf cap : isptr buf -> 0 <= cap -> buf_ok (gapw buf cap :: l) Ews cap buf.
Proof.
  intros Hp Hc. destruct buf; try contradiction. unfold buf_ok. rewrite ABL_pws_cons. cbn [pw_pred gapw].
  destruct (zlt 0 cap).
  - apply andp_right; apply sepcon_weak_valid_pointer2.
    + eapply (ABL_wvp_at _ cap _ 0); [auto | lia | lia | ABL_ptr_eq_tac].
    + eapply (ABL_wvp_at _ cap _ cap); [auto | lia | lia | ABL_ptr_eq_tac].
  - apply andp_right; apply sepcon_weak_valid_pointer1, sepcon_weak_valid_pointer1.
    + eapply (ABL_wvp_at1 _ _ 0); [auto | lia | ABL_ptr_eq_tac].
    + eapply (ABL_wvp_at1 _ _ 0); [auto | lia | ABL_ptr_eq_tac].
Qed.

Lemma ABL_buf_ok_dict l buf cap dn : isptr buf -> 0 <= cap -> 0 <= dn ->
  buf_ok (gapw buf cap :: l) Ews dn (offset_val (cap + 1) buf).
Proof.
  intros Hp Hc Hd. destruct buf; try contradiction. unfold buf_ok. rewrite ABL_pws_cons. cbn [pw_pred gapw].
  apply andp_right.
  - apply sepcon_weak_valid_pointer1, sepcon_weak_valid_pointer1.
    eapply (ABL_wvp_at1 _ _ 1); [auto | lia | ABL_ptr_eq_tac].
  - destruct (zlt 0 dn).
    + apply sepcon_weak_valid_pointer2. eapply (ABL_wvp_at _ dn _ dn); [auto | lia | lia | ABL_ptr_eq_tac].
    + apply sepcon_weak_valid_pointer1, sepcon_weak_valid_pointer1.
      eapply (ABL_wvp_at1 _ _ 1); [auto | lia | ABL_ptr_eq_tac].
Qed.

Lemma ABL_buf_ok_ib w len ib : isptr ib -> 0 <= len -> buf_ok (w :: ibw len ib) Ews len ib.
Proof.
  intros Hp Hl. destruct ib; try contradiction. unfold buf_ok. rewrite ABL_pws_cons. unfold ibw.
  destruct (zeq len 0) as [->|Hn].
  - rewrite ABL_pws1. cbn [pw_pred].
    apply andp_right; apply sepcon_weak_valid_pointer1, sepcon_weak_valid_pointer2;
      eapply (ABL_wvp_at1 _ _ 0); [auto | lia | ABL_ptr_eq_tac | auto | lia | ABL_ptr_eq_tac].
  - apply andp_right; apply sepcon_weak_valid_pointer2.
    + eapply (ABL_wvp_at _ len _ 0); [auto | lia | lia | ABL_ptr_eq_tac].
    + eapply (ABL_wvp_at _ len _ len); [auto | lia | lia | ABL_ptr_eq_tac].
Qed.

Lemma ABL_sameblock_off buf i k : isptr buf -> sameblock (offset_val i buf) (offset_val k buf) = true.
Proof. intros Hp. destruct buf; try contradiction. simpl. unfold sameblock. apply peq_true. Qed.

Lemma ABL_dict_ptr_ok l buf cap dn pos : field_compatible (tarray tuchar (cap + 1 + dn)) [] buf ->
  0 <= pos <= cap -> 0 <= dn ->
  dict_ptr_ok (gapw buf cap :: l) Ews dn (offset_val (cap + 1) buf) Ews (cap - pos) (offset_val pos buf).
Proof.
  intros Hf Hc Hd. assert (Hp: isptr buf) by auto with field_compatible.
  left. split; [apply ABL_sameblock_off; auto|]. split; [|apply ABL_buf_ok_dict; auto; lia].
  destruct buf; try contradiction. destruct Hf as (_ & _ & Hsz & _).
  simpl in Hsz |- *. rewrite Z.max_r in Hsz by lia.
  pose proof (Ptrofs.unsigned_range i).
  unfold Ptrofs.add. rewrite (Ptrofs.unsigned_repr (cap + 1)) by rep_lia.
  rewrite (Ptrofs.unsigned_repr pos) by rep_lia.
  rewrite !Ptrofs.unsigned_repr by rep_lia. lia.
Qed.

(* ib = malloc(max 1 len): its len bytes and the witness *)
Lemma ABL_ib_split ib il m A : Zlength A = il -> (0 < il /\ m = il) \/ (il = 0 /\ m = 1) ->
  @data_at ZCS Ews (tarray tuchar m) (A ++ Zrepeat Vundef (m - il)) ib |--
  @data_at ZCS Ews (tarray tuchar il) A ib * pws_pred (ibw il ib).
Proof.
  intros HA [[Hil ->] | [-> ->]].
  - unfold ibw. destruct (zeq il 0); [lia|]. rewrite Z.sub_diag.
    change (Zrepeat Vundef 0) with (@nil val). rewrite app_nil_r.
    unfold pws_pred; simpl. rewrite sepcon_emp. apply derives_refl.
  - apply Zlength_nil_inv in HA. subst A. unfold ibw. rewrite if_true by auto.
    rewrite ABL_pws1. cbn [pw_pred].
    assert_PROP (isptr ib) by (saturate_local; apply prop_right; match goal with H: field_compatible _ _ ib |- _ => destruct H as [? _]; auto end).
    change (Zrepeat Vundef (1 - 0)) with [Vundef].
    rewrite <- (emp_sepcon (@data_at ZCS Ews (tarray tuchar 1) [Vundef] ib)) at 1.
    apply sepcon_derives; [apply data_at_zero_array; auto | apply derives_refl'; apply data_at_bytes_cs].
Qed.

Lemma ABL_ib_join ib il m A : (0 < il /\ m = il) \/ (il = 0 /\ m = 1) ->
  @data_at ZCS Ews (tarray tuchar il) A ib * pws_pred (ibw il ib) |-- @data_at_ HCS Ews (tarray tuchar m) ib.
Proof.
  intros [[Hil ->] | [-> ->]].
  - unfold ibw. destruct (zeq il 0); [lia|]. unfold pws_pred; simpl. rewrite sepcon_emp.
    rewrite (data_at_bytes_cs ZCS HCS). apply data_at_data_at_.
  - unfold ibw. rewrite if_true by auto. rewrite ABL_pws1. cbn [pw_pred].
    assert_PROP (A = []) by (entailer!; apply Zlength_nil_inv; auto). subst A.
    sep_apply (@data_at_zero_array_inv ZCS Ews tuchar (@nil val) ib); auto.
    rewrite emp_sepcon. eapply derives_trans; [apply derives_refl'; apply data_at_bytes_cs|]. apply data_at_data_at_.
Qed.

Lemma ABL_dict_val buf cap : isptr buf -> 0 <= cap <= 65536 ->
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

Lemma ABL_le64_val n c : 0 <= n <= Int64.max_unsigned -> 0 <= c <= Int64.max_unsigned ->
  bool2val (negb (Int64.ltu (Int64.repr c) (Int64.repr n))) = Vint (Int.repr (if n <=? c then 1 else 0)).
Proof.
  intros Hn Hc. unfold Int64.ltu. rewrite !Int64.unsigned_repr by lia.
  destruct (zlt c n); destruct (Z.leb_spec n c); try lia; reflexivity.
Qed.

Lemma ABL_assume_le n c : Int.repr (if n <=? c then 1 else 0) <> Int.zero -> n <= c.
Proof. destruct (Z.leb_spec n c) as [Hle|Hlt]; auto. intros Hz; contradiction Hz; reflexivity. Qed.

Ltac ABL_assume_call n c :=
  forward_call (Int.repr (if n <=? c then 1 else 0));
  [ entailer!; rewrite ABL_le64_val by rep_lia; reflexivity
  | match goal with H: Int.repr (if n <=? c then 1 else 0) <> Int.zero |- _ => apply ABL_assume_le in H end ].

Lemma ABL_modu u n i : 0 <= u <= Int.max_unsigned -> 0 <= i < n -> n <= 4096 ->
  Int64.modu (Int64.repr (Int.unsigned (Int.repr u)))
    (Int64.add (Int64.sub (Int64.repr n) (Int64.repr i)) (Int64.repr (Int.signed (Int.repr 1))))
  = Int64.repr (u mod (n - i + 1)).
Proof.
  intros Hu Hi Hn. rewrite Int.unsigned_repr by rep_lia. change (Int.signed (Int.repr 1)) with 1.
  unfold Int64.modu, Int64.add, Int64.sub.
  rewrite (Int64.unsigned_repr n), (Int64.unsigned_repr i) by rep_lia.
  rewrite (Int64.unsigned_repr (n - i)), (Int64.unsigned_repr 1) by rep_lia.
  rewrite (Int64.unsigned_repr (n - i + 1)), (Int64.unsigned_repr u) by rep_lia.
  reflexivity.
Qed.

Lemma ABL_nz n i : 0 <= i < n -> n <= 4096 -> Int64.repr (n - i + Int.signed (Int.repr 1)) = Int64.zero -> False.
Proof.
  intros Hi Hn E. change (Int.signed (Int.repr 1)) with 1 in E.
  apply (f_equal Int64.unsigned) in E. rewrite Int64.unsigned_repr in E by rep_lia.
  change (Int64.unsigned Int64.zero) with 0 in E. lia.
Qed.

Lemma ABL_cle r cap pos : 0 <= r -> r <= cap - pos -> 0 <= pos <= cap -> cap <= Int64.max_unsigned ->
  bool2val (Int64.cmpu Cle (Int64.repr r) (Int64.sub (Int64.repr cap) (Int64.repr pos))) = Vint Int.one.
Proof.
  intros. rewrite sub64_repr. unfold Int64.cmpu, Int64.ltu. rewrite !Int64.unsigned_repr by rep_lia.
  destruct (zlt (cap - pos) r); [lia | reflexivity].
Qed.

Lemma ABL_bytes_ok_of l : Forall (fun b => 0 <= b <= Byte.max_unsigned) l -> bytes_ok l.
Proof. unfold bytes_ok, is_byte. apply Forall_impl. intros x Hx. rep_lia. Qed.

Lemma ABL_ptr_of_nonnull q : is_pointer_or_null q -> q <> nullval -> isptr q.
Proof. destruct q; simpl; intros; subst; auto; try contradiction. Qed.

Lemma ABL_ltu_Z x y : 0 <= x <= Int64.max_unsigned -> 0 <= y <= Int64.max_unsigned ->
  Int64.ltu (Int64.repr x) (Int64.repr y) = (x <? y).
Proof.
  intros. unfold Int64.ltu. rewrite !Int64.unsigned_repr by lia.
  destruct (zlt x y); symmetry; [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Qed.

(* ---------- the dictionary of a mode ---------- *)

Definition dr2 (dict: val) (b: list Z) : dictref :=
  {| dr_src := DSRef dict; dr_raw := false; dr_once := false; dr_bytes := b |}.

(* the DDict made of b at dict (createDDict's post: its hidden fields dd_buf/dd_ld are existential) *)
Definition dd_ok (dd: ddict_st) (dict: val) (b: list Z) : Prop :=
  dd_bytes dd = b /\ dd_ref dd = (if Zlength b =? 0 then Some dict else None).

Definition dd0 (dict: val) (b: list Z) : ddict_st :=
  {| dd_bytes := b; dd_ref := if Zlength b =? 0 then Some dict else None; dd_buf := nullval; dd_ld := None |}.

Lemma ABL_dd0_ok dict b : dd_ok (dd0 dict b) dict b.
Proof. split; reflexivity. Qed.

(* the dictionary every frame is begun with: mode 0 none, 1 the bytes by reference, 2 the DDict q (NULL: none) *)
Definition odict (mode: Z) (q dict: val) (b: list Z) (dd: ddict_st) : option dictref :=
  if mode =? 0 then None
  else if mode =? 1 then (if Zlength b =? 0 then None else Some (dr2 dict b))
  else if eq_dec q nullval then None else Some (ddict_ref q dd).

(* the frame begun: its dictionary is od, and the history is right *)
Definition begun_ok (st: dctx_st) (od: option dictref) (buf: val) (cap pos: Z) (oc: list val) : Prop :=
  exists ba, dc_bl st = Some ba /\ ba_dict ba = od /\ bl_hist_ok ba buf cap pos oc.

Lemma ABL_begin_ok st ex od buf cap pos oc :
  begun_ok (set_ex (set_bl st (Some (bl_begin st od))) ex) od buf cap pos oc.
Proof.
  exists (bl_begin st od). split; [reflexivity|]. split; [reflexivity|].
  unfold bl_hist_ok, bl_begin. cbn [ba_out ba_st]. destruct (dictref_model od); reflexivity.
Qed.

Lemma ABL_begin1 st st' r q dict b dd buf cap pos oc :
  (r = 0 /\ st' = set_ex (set_bl st (Some (bl_begin st
     (if Zlength b =? 0 then None
      else Some {| dr_src := DSRef dict; dr_raw := false; dr_once := false; dr_bytes := b |})))) false) \/
  (is_error_code r = true /\ dict_auto b = None /\ st' = set_ex (set_bl st None) false) ->
  dc_set st' = dc_set st /\ dc_ss st' = dc_ss st /\
  (is_error_code r = false -> begun_ok st' (odict 1 q dict b dd) buf cap pos oc).
Proof.
  intros [[-> ->] | (E & _ & ->)]; repeat split; auto.
  - intros _. apply ABL_begin_ok.
  - intros F; congruence.
Qed.

Lemma ABL_dict_buf_ok l mode q buf cap b dd pos : field_compatible (tarray tuchar (cap + 1 + Zlength b)) [] buf ->
  0 <= pos <= cap -> dd_ok dd (offset_val (cap + 1) buf) b ->
  dict_buf_ok (gapw buf cap :: l) Ews (odict mode q (offset_val (cap + 1) buf) b dd) Ews (cap - pos) (offset_val pos buf).
Proof.
  intros Hf Hp [Hdb Hdr]. pose proof (Zlength_nonneg b).
  unfold odict, dict_buf_ok.
  destruct (mode =? 0); [exact I|]. destruct (mode =? 1).
  - destruct (Zlength b =? 0); [exact I|]. cbn [dr2 dr_src dr_bytes]. apply ABL_dict_ptr_ok; auto.
  - destruct (eq_dec q nullval); [exact I|]. unfold ddict_ref. cbn [dr_src dr_bytes]. rewrite Hdr, Hdb.
    destruct (Zlength b =? 0); [|exact I]. apply ABL_dict_ptr_ok; auto.
Qed.

Lemma ABL_gap_fold buf cap : @data_at_ HOK_any_bufferless.CompSpecs Ews (tarray tuchar 1) (offset_val cap buf) = pw_pred (gapw buf cap).
Proof. cbn [pw_pred gapw]. rewrite ABL_data_at__Zrepeat. apply data_at_bytes_cs. Qed.

Lemma ABL_buf_merge buf cap dn oc v : 0 <= cap -> 0 <= dn ->
  field_compatible (tarray tuchar (cap + 1 + dn)) [] buf ->
  @data_at Zstd.units.Zstd.CS Ews (tarray tuchar cap) oc buf * pw_pred (gapw buf cap) *
  @data_at Zstd.units.Zstd.CS Ews (tarray tuchar dn) v (offset_val (cap + 1) buf)
  |-- @data_at_ HOK_any_bufferless.CompSpecs Ews (tarray tuchar (cap + 1 + dn)) buf.
Proof.
  intros Hc Hd Hf. rewrite (ABL_split3_bytes_ Ews cap dn buf) by auto.
  rewrite <- ABL_gap_fold.
  rewrite <- !(data_at__bytes_cs Zstd.units.Zstd.CS HOK_any_bufferless.CompSpecs).
  sep_apply (data_at_data_at_ Ews (tarray tuchar cap) oc buf).
  sep_apply (data_at_data_at_ Ews (tarray tuchar dn) v (offset_val (cap + 1) buf)).
  cancel.
Qed.

Lemma ABL_pws_fold w l : pw_pred w * pws_pred l |-- pws_pred (w :: l).
Proof. apply derives_refl. Qed.

Ltac ABL_kill :=
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

Ltac ABL_ifs := first [ repeat apply -> seq_assoc; apply semax_if_seq | idtac ]; forward_if;
  try solve [ABL_kill | exfalso; lia | contradiction].

Section Main.
Variable DC : globals -> val -> dctx_st -> mpred.
Variable DD : globals -> val -> ddict_st -> mpred.

Definition ddr (gv: globals) (q: val) (dd: ddict_st) : mpred :=
  if eq_dec q nullval then emp else (DD gv q dd && valid_pointer q).

Definition drest (od: option dictref) (dict: val) (b: list Z) : mpred :=
  match od with
  | Some r => match dr_src r with
              | DSRef _ => emp
              | DSDDict _ dd => match dd_ref dd with
                                | Some _ => emp
                                | None => @data_at ZCS Ews (tarray tuchar (Zlength b)) (zbytes b) dict
                                end
              | _ => @data_at ZCS Ews (tarray tuchar (Zlength b)) (zbytes b) dict
              end
  | None => @data_at ZCS Ews (tarray tuchar (Zlength b)) (zbytes b) dict
  end.

Lemma ABL_res_out gv mode q dict b dd : (mode <> 2 -> q = nullval) -> (0 <= mode < 3) -> dd_ok dd dict b ->
  ddr gv q dd * @data_at ZCS Ews (tarray tuchar (Zlength b)) (zbytes b) dict |--
  dict_res DD gv Ews (odict mode q dict b dd) * drest (odict mode q dict b dd) dict b.
Proof.
  intros Hq Hm [Hdb Hdr]. unfold odict, ddr.
  destruct (Z.eqb_spec mode 0).
  { rewrite Hq by lia. rewrite if_true by auto. simpl. cancel. }
  destruct (Z.eqb_spec mode 1).
  { rewrite Hq by lia. rewrite if_true by auto. destruct (Zlength b =? 0); simpl; cancel. }
  destruct (eq_dec q nullval); [simpl; cancel|].
  unfold dict_res, ddict_res, drest, ddict_ref. cbn [dr_src dr_bytes]. rewrite Hdr, Hdb.
  destruct (Zlength b =? 0); cancel.
Qed.

Lemma ABL_res_in gv mode q dict b dd : (mode <> 2 -> q = nullval) -> (0 <= mode < 3) -> dd_ok dd dict b ->
  dict_res DD gv Ews (odict mode q dict b dd) * drest (odict mode q dict b dd) dict b |--
  ddr gv q dd * @data_at ZCS Ews (tarray tuchar (Zlength b)) (zbytes b) dict.
Proof.
  intros Hq Hm [Hdb Hdr]. unfold odict, ddr.
  destruct (Z.eqb_spec mode 0).
  { rewrite Hq by lia. rewrite if_true by auto. simpl. cancel. }
  destruct (Z.eqb_spec mode 1).
  { rewrite Hq by lia. rewrite if_true by auto. destruct (Zlength b =? 0); simpl; cancel. }
  destruct (eq_dec q nullval); [simpl; cancel|].
  unfold dict_res, ddict_res, drest, ddict_ref. cbn [dr_src dr_bytes]. rewrite Hdr, Hdb.
  destruct (Zlength b =? 0); cancel.
Qed.

(* the main loop; lim bounds the call counter (511 at a continue) *)
Definition Locs (gv: globals) (mode: Z) (dctx buf src q: val) (cap: Z) (s b: list Z) (calls ipos pos begun: Z) : list localdef :=
  [temp _calls (Vint (Int.repr calls)); temp _ipos (Vlong (Int64.repr ipos));
   temp _pos (Vlong (Int64.repr pos)); temp _begun (Vint (Int.repr begun));
   temp _n (Vlong (Int64.repr (Zlength s))); temp _cap (Vlong (Int64.repr cap));
   temp _dn (Vlong (Int64.repr (Zlength b))); temp _src src; temp _buf buf; temp _dst buf;
   temp _dict (offset_val (cap + 1) buf); temp _mode (Vint (Int.repr mode)); temp _dctx dctx;
   temp _ddict q; gvars gv].

Definition Seps (gv: globals) (dctx buf src q: val) (cap: Z) (s b: list Z) (dd: ddict_st) (st: dctx_st) (oc: list val) : list mpred :=
  [mem_mgr gv; zstd_globals gv; DC gv dctx st; ddr gv q dd;
   pw_pred (gapw buf cap);
   @data_at ZCS Ews (tarray tuchar cap) oc buf;
   @data_at ZCS Ews (tarray tuchar (Zlength b)) (zbytes b) (offset_val (cap + 1) buf);
   @data_at HCS Ews (tarray tuchar (Zlength s)) (zbytes s) src;
   @malloc_token HCS Ews (tarray tuchar (Zlength s)) src;
   @malloc_token HCS Ews (tarray tuchar (cap + 1 + Zlength b)) buf; TT].

Definition Inv (gv: globals) (lim mode: Z) (dctx buf src q: val) (cap: Z) (s b: list Z) (dd: ddict_st) : environ -> mpred :=
  EX calls: Z, EX ipos: Z, EX pos: Z, EX begun: Z, EX st: dctx_st, EX oc: list val,
  PROPx [0 <= calls <= lim; 0 <= ipos <= Zlength s; 0 <= pos <= cap; Zlength oc = cap;
        dc_set st = nil; dc_ss st = ss_init;
        begun = 0 \/ (begun = 1 /\ begun_ok st (odict mode q (offset_val (cap + 1) buf) b dd) buf cap pos oc)]
  (LOCALx (Locs gv mode dctx buf src q cap s b calls ipos pos begun)
  (SEPx (Seps gv dctx buf src q cap s b dd st oc))).

Definition G0 : funspecs :=
  [ (_quickproof_malloc, @malloc_spec' HCS); (_quickproof_free, @free_spec' HCS);
    ZSTD_isError_spec;
    ZSTD_createDCtx_spec DC; ZSTD_freeDCtx_spec DC;
    ZSTD_createDDict_spec DD; ZSTD_freeDDict_spec DD;
    ZSTD_decompressBegin_aspec DC; ZSTD_decompressBegin_usingDict_aspec DC; ZSTD_decompressBegin_usingDDict_aspec DC DD;
    ZSTD_nextSrcSizeToDecompress_aspec DC; ZSTD_decompressContinue_aspec DC DD;
    nondet_u32_spec; nondet_size_spec; @nondet_bytes_nn_spec HCS; gp_assert_spec;
    gp_assume_spec ].

Lemma ABL_tyc_g_isSome (V: varspecs) (G: funspecs) i : In i (map fst V) ->
  isSome (Maps.PTree.get i (make_tycontext_g V G)).
Proof.
  intros H. unfold make_tycontext_g. induction G as [|[j f] G IH]; simpl.
  - induction V as [|[k t] V IHV]; simpl in *; [contradiction|].
    rewrite Maps.PTree.gsspec. destruct (peq i k); simpl; auto.
    apply IHV. destruct H; [congruence|auto].
  - rewrite Maps.PTree.gsspec. destruct (peq i j); simpl; auto.
Qed.

Lemma ABL_vars_in_Vprog (G: funspecs) :
  Forall (fun ig : ident * globvar type => isSome (Maps.PTree.get (fst ig) (make_tycontext_g Vprog G)))
    (QPprog_vars Zstd.contracts.x_any_bufferless.whole_prog).
Proof.
  apply Forall_forall. intros [i g] Hin. apply ABL_tyc_g_isSome.
  unfold Vprog, QPvarspecs. rewrite map_map.
  change (In i (map (fun x : ident * globvar type => fst x)
                  (QPprog_vars Zstd.contracts.x_any_bufferless.whole_prog))).
  apply (in_map (fun x : ident * globvar type => fst x)) in Hin. exact Hin.
Qed.

Lemma ABL_drop_vp (P: mpred) q : P && valid_pointer q |-- P.
Proof. apply andp_left1, derives_refl. Qed.

Lemma body_main_G0 : @semax_body Vprog G0 HCS f_main main_spec.
Proof.
  change (@semax_body Vprog G0 HCS f_main (_main, WITH gv: globals PRE [] VST.floyd.VSU.main_pre
    Zstd.contracts.x_any_bufferless.whole_prog tt gv POST [tint] (fun _ : environ => TT))).
  replace (fun _ : environ => @TT mpred _) with (PROP () LOCAL () SEP (@TT mpred _))
    by (extensionality rho; unfold PROPx, LOCALx, SEPx; simpl; normalize).
  start_function1.
  eapply (main_pre_InitGpred
     (Zstd.proof.zstd.Globals.zstd_globals gv *
      InitGPred (filter (fun ig => negb (id_in_list (fst ig) zstd_var_ids))
                   (Vardefs Zstd.contracts.x_any_bufferless.whole_prog)) gv)%logic);
    [ intros Hgv; apply main_pre_fact6; [do 13 right; left; reflexivity | exact Hgv]
    | reflexivity | apply ABL_vars_in_Vprog | ].
  replace (stackframe_of f_main) with (@emp (environ->mpred) _ _) by reflexivity.
  rewrite sepcon_emp.
  eapply semax_pre with (P' := PROP () LOCAL (gvars gv) SEP (mem_mgr gv; zstd_globals gv; TT)).
  { go_lower. sep_apply (create_mem_mgr gv). rewrite prop_true_andp by auto. cancel. }
  abbreviate_semax.
  forward_call tt. Intros n.
  forward. forward. forward. forward.
  ABL_assume_call n 4096.
  forward_call (tarray tuchar n, gv).
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros src.
  destruct (eq_dec src nullval) as [Hsrc|Hsrc].
  { subst src. forward_if. { forward. } { exfalso. auto. } }
  Intros. forward_if. { contradiction. }
  forward_call (src, n, Ews).
  Intros s.
  forward_call tt. Intros cap.
  ABL_assume_call cap 65536.
  forward_call tt. Intros a. forward.
  assert (Hm: Int.modu (Int.repr a) (Int.repr 3) = Int.repr (a mod 3)).
  { unfold Int.modu. rewrite !Int.unsigned_repr by rep_lia. reflexivity. }
  rewrite Hm. clear Hm.
  assert (Hmode: 0 <= a mod 3 < 3) by (apply Z.mod_pos_bound; lia).
  forget (a mod 3) as mode.
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
    forward_if (EX dn: Z, PROPx ((0 <= dn <= 512) :: (mode = 0 -> dn = 0) :: P)
                 (LOCALx (temp _t'5 (Vint (Int.repr dn)) :: L) (SEPx R)))
  end.
  { forward. Exists 0. entailer!. }
  { forward_call tt. Intros u. forward. Exists (u mod 513).
    pose proof (Z.mod_pos_bound u 513 ltac:(lia)).
    entailer!.
    all: try (unfold Int.modu; change (Int.add (Int.repr 512) (Int.repr 1)) with (Int.repr 513);
              rewrite !Int.unsigned_repr by rep_lia; reflexivity). }
  Intros dn. forward.
  rewrite Int.unsigned_repr by rep_lia.
  forward_call (tarray tuchar (cap + 1 + dn), gv).
  { simpl. rep_lia. }
  Intros buf.
  forward_call gv.
  Intros dctx.
  forward. forward.
  destruct (eq_dec buf nullval) as [Hb|Hb].
  { subst buf. ABL_ifs. ABL_ifs. forward. ABL_ifs.
    forward_call (tarray tuchar n, src, gv).
    { rewrite (if_false (src = nullval)) by auto. sep_apply (data_at_data_at_ Ews (tarray tuchar n) (zbytes s) src). cancel. }
    forward_call (tarray tuchar 1, nullval, gv). { rewrite (if_true (nullval = nullval)) by auto. cancel. }
    destruct (eq_dec dctx nullval) as [Hd|Hd].
    - forward_call (gv, dctx, @None dctx_st). forward.
    - sep_apply (ABL_drop_vp (DC gv dctx dctx_init) dctx). forward_call (gv, dctx, Some dctx_init). forward. }
  Intros.
  assert_PROP (field_compatible (tarray tuchar (cap + 1 + dn)) [] buf) as Hfb by entailer!.
  assert (Hpb: isptr buf) by auto with field_compatible.
  assert_PROP (isptr src) as Hps by entailer!.
  ABL_ifs.
  forward.
  rewrite ABL_dict_val by first [exact Hpb | lia].
  destruct (eq_dec dctx nullval) as [Hd|Hd].
  { subst dctx. ABL_ifs. forward. ABL_ifs.
    forward_call (tarray tuchar n, src, gv).
    { rewrite (if_false (src = nullval)) by auto. sep_apply (data_at_data_at_ Ews (tarray tuchar n) (zbytes s) src). cancel. }
    forward_call (tarray tuchar (cap + 1 + dn), buf, gv). { rewrite (if_false (buf = nullval)) by auto. cancel. }
    forward_call (gv, nullval, @None dctx_st); try (match goal with |- _ |-- _ => cancel end). forward. }
  try rewrite (if_false (dctx = nullval)) by auto.
  destruct dctx as [| | | | | bd od]; try (simpl in PNdctx; subst; contradiction).
  ABL_ifs. forward. ABL_ifs.
  sep_apply (ABL_drop_vp (DC gv (Vptr bd od) dctx_init) (Vptr bd od)).
  rewrite (ABL_split3_bytes_ Ews cap dn buf) by first [exact Hfb | lia].
  Intros.
  match goal with |- semax _ (PROPx ?P (LOCALx ?L _)) _ _ =>
    forward_if (EX b: list Z, PROPx ((Zlength b = dn) :: Forall (fun x => 0 <= x <= Byte.max_unsigned) b :: P)
      (LOCALx L (SEPx [DC gv (Vptr bd od) dctx_init; mem_mgr gv; zstd_globals gv;
         malloc_token Ews (tarray tuchar (cap + 1 + dn)) buf;
         data_at_ Ews (tarray tuchar cap) buf;
         data_at_ Ews (tarray tuchar 1) (offset_val cap buf);
         data_at Ews (tarray tuchar dn) (zbytes b) (offset_val (cap + 1) buf);
         data_at Ews (tarray tuchar n) (zbytes s) src;
         malloc_token Ews (tarray tuchar n) src; TT])))
  end.
  { forward_call (offset_val (cap + 1) buf, dn, Ews). Intros b. Exists b. entailer!. }
  { forward. Exists (@nil Z).
    match goal with H: Int64.unsigned _ >= Int64.unsigned _ |- _ => rewrite !Int64.unsigned_repr in H by rep_lia end.
    assert (dn = 0) by lia. subst dn. entailer!. }
  Intros b. subst dn.
  rewrite (ABL_gap_fold buf cap).
  rewrite (data_at__bytes_cs HCS ZCS Ews cap buf), (ABL_data_at__Zrepeat Ews cap buf).
  rewrite (data_at_bytes_cs HCS ZCS Ews (Zlength b) (zbytes b) (offset_val (cap + 1) buf)).
  forward_if (EX q: val, EX dd: ddict_st,
    PROP ((mode <> 2 -> q = nullval); (q <> nullval -> isptr q); dd_ok dd (offset_val (cap + 1) buf) b)
    LOCAL (temp _ddict q; temp _dict (offset_val (cap + 1) buf); temp _dst buf; temp _dctx (Vptr bd od);
           temp _buf buf; temp _dn (Vlong (Int64.repr (Zlength b))); temp _mode (Vint (Int.repr mode));
           temp _cap (Vlong (Int64.repr cap)); temp _src src; temp _begun (Vint (Int.repr 0));
           temp _pos (Vlong (Int64.repr 0)); temp _ipos (Vlong (Int64.repr 0)); temp _n (Vlong (Int64.repr n));
           gvars gv)
    SEP (DC gv (Vptr bd od) dctx_init; mem_mgr gv; zstd_globals gv;
         ddr gv q dd;
         malloc_token Ews (tarray tuchar (cap + 1 + Zlength b)) buf;
         @data_at ZCS Ews (tarray tuchar cap) (Zrepeat Vundef cap) buf;
         pw_pred (gapw buf cap);
         @data_at ZCS Ews (tarray tuchar (Zlength b)) (zbytes b) (offset_val (cap + 1) buf);
         data_at Ews (tarray tuchar n) (zbytes s) src;
         malloc_token Ews (tarray tuchar n) src; TT)).
  { rewrite <- (ABL_pws1 (gapw buf cap)).
    forward_call ([gapw buf cap], gv, Ews, offset_val (cap + 1) buf, b).
    { rewrite bytes_at_ptr by (destruct buf; try contradiction; exact I). cancel. }
    { split; [intro Hn; exfalso; destruct buf; try contradiction; discriminate Hn|].
      split; [intros _; apply ABL_buf_ok_dict; auto; lia|]. apply ABL_bytes_ok_of; auto. }
    Intros vret. destruct vret as [q dd]. simpl fst in *; simpl snd in *.
    rewrite bytes_at_ptr by (destruct buf; try contradiction; exact I).
    match goal with H: dd_ref dd = _ |- _ =>
      rewrite if_false in H by (intro Hn; destruct buf; try contradiction; discriminate Hn) end.
    forward. rewrite ABL_pws1. Exists q dd.
    unfold ddr. destruct (eq_dec q nullval).
    - entailer!. split; auto.
    - entailer!. split; [apply ABL_ptr_of_nonnull; auto | split; auto]. }
  { forward. Exists nullval (dd0 (offset_val (cap + 1) buf) b). unfold ddr. rewrite (if_true (nullval = nullval)) by auto.
    entailer!. apply ABL_dd0_ok. }
  Intros q dd. match goal with H: dd_ok dd _ _ |- _ => rename H into Hdd end. forward. subst n.
  forward_loop (Inv gv 512 mode (Vptr bd od) buf src q cap s b dd)
    continue: (Inv gv 511 mode (Vptr bd od) buf src q cap s b dd)
    break: (Inv gv 512 mode (Vptr bd od) buf src q cap s b dd).
  { unfold Inv, Locs, Seps. Exists 0 0 0 0 dctx_init (Zrepeat Vundef cap). entailer!. }
  2: { unfold Inv, Locs, Seps. Intros calls ipos pos begun st oc. forward.
       unfold Inv, Locs, Seps. Exists (calls + 1) ipos pos begun st oc. entailer!. }
  2: { unfold Inv, Locs, Seps. Intros calls ipos pos begun st oc.
       destruct (eq_dec q nullval) as [Hq|Hq].
       - subst q. unfold ddr. rewrite (if_true (nullval = nullval)) by auto.
         forward_call (gv, nullval, @None ddict_st); try (match goal with |- _ |-- _ => cancel end).
         forward_call (gv, Vptr bd od, Some st).
         forward_call (tarray tuchar (Zlength s), src, gv).
         { rewrite (if_false (src = nullval)) by auto. sep_apply (data_at_data_at_ Ews (tarray tuchar (Zlength s)) (zbytes s) src). cancel. }
         sep_apply (ABL_buf_merge buf cap (Zlength b) oc (zbytes b) ltac:(lia) ltac:(lia) Hfb).
         forward_call (tarray tuchar (cap + 1 + Zlength b), buf, gv). { rewrite (if_false (buf = nullval)) by auto. cancel. }
         forward.
       - unfold ddr. rewrite (if_false (q = nullval)) by auto.
         sep_apply (ABL_drop_vp (DD gv q dd) q).
         forward_call (gv, q, Some dd).
         forward_call (gv, Vptr bd od, Some st).
         forward_call (tarray tuchar (Zlength s), src, gv).
         { rewrite (if_false (src = nullval)) by auto. sep_apply (data_at_data_at_ Ews (tarray tuchar (Zlength s)) (zbytes s) src). cancel. }
         sep_apply (ABL_buf_merge buf cap (Zlength b) oc (zbytes b) ltac:(lia) ltac:(lia) Hfb).
         forward_call (tarray tuchar (cap + 1 + Zlength b), buf, gv). { rewrite (if_false (buf = nullval)) by auto. cancel. }
         forward. }
  unfold Inv, Locs, Seps. Intros calls ipos pos begun st oc.
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
    forward_if (EX bb: bool, PROPx ((bb = true -> calls < 512 /\ ipos < Zlength s) :: P)
                 (LOCALx (temp _t'11 (Vint (if bb then Int.one else Int.zero)) :: L) (SEPx R)))
  end.
  { forward. Exists (ipos <? Zlength s). entailer!.
    destruct (zlt ipos (Zlength s)); [rewrite (proj2 (Z.ltb_lt _ _)) by lia | rewrite (proj2 (Z.ltb_ge _ _)) by lia];
    reflexivity. }
  { forward. Exists false. entailer!. }
  Intros bb. forward_if.
  2: { forward. unfold Inv, Locs, Seps. Exists calls ipos pos begun st oc. entailer!. }
  destruct bb; [|exfalso; auto]. 
  forward_if (EX st1: dctx_st,
    PROPx [dc_set st1 = nil; dc_ss st1 = ss_init; begun_ok st1 (odict mode q (offset_val (cap + 1) buf) b dd) buf cap pos oc]
    (LOCALx (Locs gv mode (Vptr bd od) buf src q cap s b calls ipos pos 1)
    (SEPx (Seps gv (Vptr bd od) buf src q cap s b dd st1 oc)))).
  { assert (begun = 0) by (destruct H20 as [|[-> _]]; [auto | ABL_kill]). subst begun.
    forward_if (EX r: Z, EX st1: dctx_st,
      PROPx [0 <= r <= Int64.max_unsigned; dc_set st1 = nil; dc_ss st1 = ss_init;
             is_error_code r = false -> begun_ok st1 (odict mode q (offset_val (cap + 1) buf) b dd) buf cap pos oc]
      (LOCALx (temp _t'12 (Vlong (Int64.repr r)) :: Locs gv mode (Vptr bd od) buf src q cap s b calls ipos pos 0)
      (SEPx (Seps gv (Vptr bd od) buf src q cap s b dd st1 oc)))).
    { subst mode. forward_call (gv, Vptr bd od, st). forward. unfold Locs, Seps.
      Exists 0 (set_ex (set_bl st (Some (bl_begin st None))) false). entailer!.
      apply ABL_begin_ok. }
    { forward_if.
      - subst mode. rewrite <- (ABL_pws1 (gapw buf cap)).
        forward_call ([gapw buf cap], gv, Vptr bd od, st, Ews, offset_val (cap + 1) buf, b).
        { split; [apply ABL_buf_ok_dict; auto; lia|]. apply ABL_bytes_ok_of; auto. }
        Intros vret. destruct vret as [r st']. simpl fst in *; simpl snd in *.
        forward. rewrite ABL_pws1.
        match goal with H: (r = 0 /\ _) \/ _ |- _ =>
          destruct (ABL_begin1 _ _ _ q _ _ dd buf cap pos oc H) as (E1 & E2 & E3) end.
        unfold Locs, Seps. Exists r st'. entailer!.
      - assert (mode = 2) by (repeat match goal with H: Int.repr mode <> Int.repr ?k |- _ =>
            assert (mode <> k) by (intro; subst; auto); clear H end; lia).
        subst mode.
        destruct (eq_dec q nullval) as [Hq|Hq].
        + subst q. unfold ddr. rewrite (if_true (nullval = nullval)) by auto.
          forward_call (gv, Vptr bd od, st, nullval, @None ddict_st).
          forward. unfold Locs, Seps, ddr. try rewrite (if_true (nullval = nullval)) by auto.
          Exists 0 (set_ex (set_bl st (Some (bl_begin st None))) false). entailer!.
          unfold odict. simpl. try rewrite (if_true (nullval = nullval)) by auto. apply ABL_begin_ok.
        + unfold ddr. rewrite (if_false (q = nullval)) by auto.
          sep_apply (ABL_drop_vp (DD gv q dd) q).
          forward_call (gv, Vptr bd od, st, q, Some dd).
          forward. unfold Locs, Seps, ddr. try rewrite (if_false (q = nullval)) by auto.
          Exists 0 (set_ex (set_bl st (Some (bl_begin st (Some (ddict_ref q dd))))) false).
          entailer!.
          unfold odict. simpl. try rewrite (if_false (q = nullval)) by auto. apply ABL_begin_ok. }
    unfold Locs, Seps. Intros r st1. forward.
    forward_call r.
    destruct (is_error_code r) eqn:Er; forward_if; try ABL_kill.
    - forward. unfold Inv, Locs, Seps. Exists calls ipos pos 0 st1 oc. entailer!.
    - forward. unfold Locs, Seps. Exists st1. entailer!. }
  { destruct H20 as [-> | [-> Hok]]; [ABL_kill|].
    forward. unfold Locs, Seps. Exists st. entailer!. }
  unfold Locs, Seps. Intros st1.
  match goal with H: begun_ok st1 _ _ _ _ _ |- _ => destruct H as (ba & Hbl & Hbd & Hh) end.
  forward_call (gv, Vptr bd od, st1, ba). Intros.
  forward_if.
  { forward. forward. unfold Inv, Locs, Seps. Exists calls ipos pos 0 st1 oc. entailer!. }
  match goal with H: Int64.repr (ba_expect ba) <> Int64.repr 0 |- _ =>
    assert (Hne: ba_expect ba <> 0) by (intro E; rewrite E in H; auto) end.
  destruct (H21 eq_refl) as [Hcalls Hipos].
  forward_call tt. Intros u1.
  forward_if (EX l0: Z, PROPx [0 <= l0 <= Int64.max_unsigned]
    (LOCALx (temp _t'19 (Vlong (Int64.repr l0)) :: Locs gv mode (Vptr bd od) buf src q cap s b calls ipos pos 1)
    (SEPx (Seps gv (Vptr bd od) buf src q cap s b dd st1 oc)))).
  { forward. unfold Locs, Seps. Exists (ba_expect ba). entailer!. }
  { forward_call tt. Intros u2. forward.
    { entailer!. eapply ABL_nz; [|eassumption|eassumption]. lia. }
    rewrite ABL_modu by lia. unfold Locs, Seps.
    pose proof (Z.mod_pos_bound u2 (Zlength s - ipos + 1) ltac:(lia)).
    Exists (u2 mod (Zlength s - ipos + 1)). entailer!. }
  unfold Locs, Seps. Intros l0. forward.
  forward_if (PROPx []
    (LOCALx (temp _len (Vlong (Int64.repr (Z.min l0 (Zlength s - ipos)))) :: Locs gv mode (Vptr bd od) buf src q cap s b calls ipos pos 1)
    (SEPx (Seps gv (Vptr bd od) buf src q cap s b dd st1 oc)))).
  { forward. unfold Locs, Seps. entailer!.
    match goal with H: Int64.ltu _ _ = true |- _ => rewrite ABL_ltu_Z in H by rep_lia; apply Z.ltb_lt in H end.
    rewrite Z.min_r by lia. reflexivity. }
  { forward. unfold Locs, Seps. entailer!.
    match goal with H: Int64.ltu _ _ = false |- _ => rewrite ABL_ltu_Z in H by rep_lia; apply Z.ltb_ge in H end.
    rewrite Z.min_l by lia. reflexivity. }
  unfold Locs, Seps. Intros.
  assert (Hlen: 0 <= Z.min l0 (Zlength s - ipos) <= Zlength s - ipos) by lia.
  set (len := Z.min l0 (Zlength s - ipos)) in *. clearbody len.
  forward_if (PROPx []
    (LOCALx (temp _t'21 (Vlong (Int64.repr (Z.max 1 len))) :: temp _len (Vlong (Int64.repr len)) ::
             Locs gv mode (Vptr bd od) buf src q cap s b calls ipos pos 1)
    (SEPx (Seps gv (Vptr bd od) buf src q cap s b dd st1 oc)))).
  { forward. unfold Locs, Seps. entailer!.
    match goal with H: Int64.unsigned _ < Int64.unsigned _ |- _ => rewrite !Int64.unsigned_repr in H by rep_lia end.
    rewrite Z.max_r by lia. reflexivity. }
  { forward. unfold Locs, Seps. entailer!.
    match goal with H: Int64.unsigned _ >= Int64.unsigned _ |- _ => rewrite !Int64.unsigned_repr in H by rep_lia end.
    replace len with 0 by lia. reflexivity. }
  unfold Locs, Seps. Intros.
  forward_call (tarray tuchar (Z.max 1 len), gv).
  { simpl. rep_lia. }
  Intros ib. forward.
  destruct (eq_dec ib nullval) as [Hib|Hib].
  { subst ib. forward_if; [|ABL_kill].
    forward. unfold Inv, Locs, Seps. Exists calls ipos pos 1 st1 oc. entailer!.
    right; split; [auto|]. exists ba; auto. }
  Intros. forward_if; [contradiction|].
  assert (Hm: (0 < len /\ Z.max 1 len = len) \/ (len = 0 /\ Z.max 1 len = 1)) by lia.
  set (m := Z.max 1 len) in *. clearbody m.
  forward.
  forward_loop (EX i: Z, PROPx [0 <= i <= len]
     (LOCALx (temp _i (Vlong (Int64.repr i)) :: temp _ib ib :: temp _len (Vlong (Int64.repr len)) ::
              Locs gv mode (Vptr bd od) buf src q cap s b calls ipos pos 1)
     (SEPx (malloc_token Ews (tarray tuchar m) ib ::
            data_at Ews (tarray tuchar m) (sublist ipos (ipos + i) (zbytes s) ++ Zrepeat Vundef (m - i)) ib ::
            Seps gv (Vptr bd od) buf src q cap s b dd st1 oc))))
    continue: (EX i: Z, PROPx [0 <= i < len]
     (LOCALx (temp _i (Vlong (Int64.repr i)) :: temp _ib ib :: temp _len (Vlong (Int64.repr len)) ::
              Locs gv mode (Vptr bd od) buf src q cap s b calls ipos pos 1)
     (SEPx (malloc_token Ews (tarray tuchar m) ib ::
            data_at Ews (tarray tuchar m) (sublist ipos (ipos + (i + 1)) (zbytes s) ++ Zrepeat Vundef (m - (i + 1))) ib ::
            Seps gv (Vptr bd od) buf src q cap s b dd st1 oc))))
    break: (PROPx []
     (LOCALx (temp _ib ib :: temp _len (Vlong (Int64.repr len)) ::
              Locs gv mode (Vptr bd od) buf src q cap s b calls ipos pos 1)
     (SEPx (malloc_token Ews (tarray tuchar m) ib ::
            data_at Ews (tarray tuchar m) (sublist ipos (ipos + len) (zbytes s) ++ Zrepeat Vundef (m - len)) ib ::
            Seps gv (Vptr bd od) buf src q cap s b dd st1 oc)))).
  { Exists 0. unfold Locs, Seps. entailer!. rewrite sublist_nil, app_nil_l. cancel. }
  { Intros i. unfold Locs, Seps. forward_if.
    2: { forward. unfold Locs, Seps. entailer!. replace i with len by lia. cancel. }
    forward.
    { entailer!.
      match goal with Hf: Forall (fun b : Z => 0 <= b <= Byte.max_unsigned) s |- _ =>
        pose proof (proj1 (Forall_Znth _ _) Hf (ipos + i) ltac:(lia)) as Hbt end.
      cbv beta in Hbt. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    forward.
    Exists i. unfold Locs, Seps. entailer!.
    match goal with Hf: Forall (fun b : Z => 0 <= b <= Byte.max_unsigned) s |- _ =>
      pose proof (proj1 (Forall_Znth _ _) Hf (ipos + i) ltac:(lia)) as Hbt end.
    cbv beta in Hbt.
    try rewrite zero_ext_inrange by (rewrite Int.unsigned_repr by rep_lia; simpl; rep_lia).
    replace (Vint (Int.repr (Znth (ipos + i) s))) with (Znth (ipos + i) (zbytes s))
      by (rewrite Znth_map by lia; reflexivity).
    replace (upd_Znth i (sublist ipos (ipos + i) (zbytes s) ++ Zrepeat Vundef (m - i)) (Znth (ipos + i) (zbytes s)))
      with (sublist ipos (ipos + (i + 1)) (zbytes s) ++ Zrepeat Vundef (m - (i + 1))); [cancel|].
    list_solve. }
  { Intros i. unfold Locs, Seps. forward. Exists (i + 1). unfold Locs, Seps. entailer!. }
  unfold Locs, Seps. Intros.
  clear H20 H18 H19 H21 H26.
  assert (Hcl: Zlength (sublist ipos (ipos + len) s) = len) by (rewrite Zlength_sublist by lia; lia).
  assert (Hcb: bytes_ok (sublist ipos (ipos + len) s)).
  { apply ABL_bytes_ok_of. apply Forall_sublist. auto. }
  set (c := sublist ipos (ipos + len) s) in *. 
  assert (Hzc: sublist ipos (ipos + len) (zbytes s) = zbytes c) by (subst c; rewrite sublist_map; reflexivity).
  rewrite Hzc. clear Hzc.
  assert (Hc: Zlength (zbytes c) = len) by (rewrite Zlength_map; auto).
  clearbody c.
  assert_PROP (isptr ib) as Hpib by entailer!.
  rewrite (data_at_bytes_cs HCS ZCS Ews m _ ib).
  sep_apply (ABL_ib_split ib len m (zbytes c) Hc Hm).
  sep_apply (ABL_pws_fold (gapw buf cap) (ibw len ib)).
  sep_apply (ABL_res_out gv mode q (offset_val (cap + 1) buf) b dd H12 Hmode Hdd).
  rewrite <- Hbd.
  forward_call (gapw buf cap :: ibw len ib, gv, Vptr bd od, st1, ba, Ews, Ews, buf, cap, pos, oc, Ews, ib, c).
  { entailer!. }
  { rewrite Hcl. cancel. }
  { split; [apply ABL_buf_ok_dst; auto; lia|]. split; [rewrite Hcl; apply ABL_buf_ok_ib; auto; lia|].
    rewrite Hbd. apply ABL_dict_buf_ok; auto; lia. }
  Intros vret. destruct vret as [[r oc'] ba']. simpl fst in *; simpl snd in *.
  rewrite ABL_pws_cons. Intros.
  rewrite Hbd. sep_apply (ABL_res_in gv mode q (offset_val (cap + 1) buf) b dd H12 Hmode Hdd).
  rewrite Hcl.
  sep_apply (ABL_ib_join ib len m (zbytes c) Hm).
  forward_call (tarray tuchar m, ib, gv). { rewrite (if_false (ib = nullval)) by auto. cancel. }
  forward_call r.
  destruct (is_error_code r) eqn:Er.
  - ABL_ifs. forward. forward_call Int.one. forward. forward_call r. rewrite Er. ABL_ifs. forward.
    unfold Inv, Locs, Seps. Exists calls (ipos + len) pos 0 (set_ex (set_bl st1 None) false) oc'. entailer!.
  - destruct (H21 eq_refl) as (Hr & Hcells & Hbd' & Hout & Hh' & Hexp).
    ABL_ifs. forward.
    rewrite ABL_cle by lia.
    forward_call Int.one. forward. forward_call r. rewrite Er. ABL_ifs. forward.
    unfold Inv, Locs, Seps. Exists calls (ipos + len) (pos + r) 1 (set_ex (set_bl st1 (Some ba')) false) oc'. entailer!.
    right. split; [auto|]. exists ba'. split; [reflexivity|]. split; [congruence | auto].
Qed.

End Main.

(* ---------- from G0 to Gprog (Specs_api DC DD) [] (recipe: any_dict's v2 proof) ---------- *)

Definition ABL_G_ext : funspecs :=
  [nondet_u32_spec; nondet_size_spec; @nondet_bytes_nn_spec HCS; gp_assert_spec; gp_assume_spec].

Lemma ABL_Externals_eq : Externals = ABL_G_ext.
Proof.
  unfold Externals, present, env_harness, filter.
  repeat match goal with |- context [id_in_list ?i ?l] =>
    let b := eval lazy in (id_in_list i l) in change (id_in_list i l) with b end.
  reflexivity.
Qed.

Lemma ABL_make_tycontext_g_find (Vs: varspecs) (G: funspecs) i :
  Maps.PTree.get i (make_tycontext_g Vs G) =
  match initial_world.find_id i G with Some fs => Some (type_of_funspec fs) | None => Maps.PTree.get i (make_tycontext_g Vs nil) end.
Proof.
  induction G as [|[j fs] G IH]; simpl; auto.
  rewrite Maps.PTree.gsspec. unfold make_tycontext_g in IH |- *. simpl in IH.
  destruct (peq i j) as [->|Hne].
  - rewrite if_true by reflexivity. reflexivity.
  - rewrite if_false by exact Hne. exact IH.
Qed.

Definition ABL_Lg : list ident :=
  [_quickproof_malloc; _quickproof_free;
   _ZSTD_isError; _ZSTD_getErrorCode; _ZSTD_decompress; _ZSTD_decompressDCtx; _ZSTD_decompress_usingDict;
   _ZSTD_decompress_usingDDict; _ZSTD_createDCtx; _ZSTD_createDStream; _ZSTD_freeDCtx; _ZSTD_freeDStream;
   _ZSTD_DCtx_reset; _ZSTD_initDStream; _ZSTD_DCtx_setParameter; _ZSTD_DStreamOutSize;
   _ZSTD_createDDict; _ZSTD_createDDict_byReference; _ZSTD_freeDDict;
   _ZSTD_getDictID_fromDDict; _ZSTD_getDictID_fromDict;
   _ZSTD_DCtx_loadDictionary_byReference; _ZSTD_DCtx_loadDictionary;
   _ZSTD_DCtx_refPrefix; _ZSTD_DCtx_refDDict; _ZSTD_decompressStream;
   _ZSTD_findFrameCompressedSize; _ZSTD_getFrameContentSize; _ZSTD_findDecompressedSize;
   _ZSTD_decompressBound; _ZSTD_frameHeaderSize; _ZSTD_getDictID_fromFrame; _ZSTD_isFrame;
   _ZSTD_isSkippableFrame; _ZSTD_getFrameHeader; _ZSTD_readSkippableFrame;
   _ZSTD_DCtx_setFormat; _ZSTD_DCtx_setMaxWindowSize; _ZSTD_resetDStream;
   _ZSTD_DCtx_loadDictionary_advanced; _ZSTD_DCtx_refPrefix_advanced;
   _ZSTD_initDStream_usingDict; _ZSTD_initDStream_usingDDict;
   _ZSTD_getDecompressedSize; _ZSTD_getFrameHeader_advanced;
   _ZSTD_decompressBegin; _ZSTD_decompressBegin_usingDict; _ZSTD_decompressBegin_usingDDict;
   _ZSTD_nextSrcSizeToDecompress; _ZSTD_nextInputType; _ZSTD_decompressContinue;
   _ZSTD_createDCtx_advancedP; _ZSTD_estimateDCtxSize; _ZSTD_estimateDStreamSize;
   _nondet_u32; _nondet_size; _nondet_bytes; _gp_assert; _gp_assume; _main].

Lemma ABL_Gprog_ids DC DD : map fst (Gprog (Specs_api DC DD) []) = ABL_Lg.
Proof. unfold Gprog, Imports. rewrite ABL_Externals_eq. reflexivity. Qed.

(* no function of Gprog is a global variable of the program *)
Lemma ABL_Lg_not_var :
  forallb (fun i => match Maps.PTree.get i (make_tycontext_g Vprog nil) with None => true | Some _ => false end) ABL_Lg
  = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ABL_G0_entries DC DD :
  Forall (fun e => initial_world.find_id (fst e) (Gprog (Specs_api DC DD) []) = Some (snd e)) (G0 DC DD).
Proof.
  unfold Gprog, Imports. rewrite ABL_Externals_eq.
  repeat constructor; reflexivity.
Qed.

Lemma ABL_G0_in_Gprog DC DD i fs :
  initial_world.find_id i (G0 DC DD) = Some fs -> initial_world.find_id i (Gprog (Specs_api DC DD) []) = Some fs.
Proof.
  intros Hi. apply initial_world.find_id_e in Hi.
  pose proof (ABL_G0_entries DC DD) as HF. rewrite Forall_forall in HF.
  exact (HF (i, fs) Hi).
Qed.

Lemma ABL_harness_ok DC DD : HarnessOK (Specs_api DC DD) [].
Proof.
  split.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    exists f_main. split; [reflexivity|]. split; [reflexivity|].
    eapply semax_body_subsumption; [apply (body_main_G0 DC DD) |].
    apply tycontext_sub_i99. split; intro i.
    + rewrite (ABL_make_tycontext_g_find Vprog (G0 DC DD) i).
      destruct (initial_world.find_id i (G0 DC DD)) as [fs|] eqn:E.
      * remember (Gprog (Specs_api DC DD) []) as GP eqn:HGP. (* abstract while rewriting: no comparison with [] by computation *)
        rewrite (ABL_make_tycontext_g_find Vprog GP i). subst GP.
        rewrite (ABL_G0_in_Gprog DC DD i fs E). apply sub_option_refl.
      * remember (Gprog (Specs_api DC DD) []) as GP eqn:HGP. (* abstract while rewriting: no comparison with [] by computation *)
        rewrite (ABL_make_tycontext_g_find Vprog GP i). subst GP.
        destruct (initial_world.find_id i (Gprog (Specs_api DC DD) [])) as [f|] eqn:E2; [|apply sub_option_refl].
        assert (Hin: In i ABL_Lg).
        { rewrite <- (ABL_Gprog_ids DC DD). apply in_map_iff. exists (i, f). split; [reflexivity|].
          apply initial_world.find_id_e; exact E2. }
        pose proof ABL_Lg_not_var as HL. rewrite forallb_forall in HL. specialize (HL i Hin).
        destruct (Maps.PTree.get i (make_tycontext_g Vprog nil)); [discriminate | exact Logic.I].
    + rewrite !semax_prog.find_id_maketycontext_s.
      destruct (initial_world.find_id i (G0 DC DD)) as [fs|] eqn:E; [|exact Logic.I].
      rewrite (ABL_G0_in_Gprog DC DD i fs E). exists fs. split; [reflexivity|]. apply funspec_sub_si_refl.
Qed.

Theorem any_bufferless_ok :
  forall (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred),
    exists Hs, HarnessOK (Specs_api DC DD) Hs.
Proof.
  intros DC DD. exists []. exact (ABL_harness_ok DC DD).
Qed.
