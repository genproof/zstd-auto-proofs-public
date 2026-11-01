(* The body of main of the law rj_reserved_block (harness/rj_reserved_block.c), for ANY predicates DC, DD of the
   decoder's API (Spec_api6), with the functions main calls (G0): the frames kit's helpers (FSpecs, FStreamSpec),
   malloc, nondet_u8, gp_assert and the decoder's ZSTD_isError, ZSTD_decompress, ZSTD_createDStream.

   main builds a frame F of new_frame, walks its block headers from the first one over any number of blocks,
   never past the last one (Facts_rj_reserved_block: rb_first, rb_hdr_in, rb_last, rb_next; the loop's
   invariant: at is the offset of the i-th block header, blk_off), and sets Block_Type 3 (Reserved) in the
   header it stops at.  The result is a series zstd certainly refuses with no frame before the refused one
   (rb_refused).  One-shot: ZSTD_decompress's specification (oneshot_ok: decode_series_m is SUnk, rb_series_unk,
   and the series is refused) gives an error.  Streamed: no call of stream_all returns 0
   (FStreamRefused.stream_refused_no_end), so *completed stays 0.  The buffers have any size up to PTRDIFF_MAX:
   this needs the one-shot and streaming specifications with sizes up to 2 ^ 63 - 1 (stage 1 of the size
   bounds of Spec_api6) and the refusals (stage 2, item (R)). *)
Require Import VST.floyd.proofauto.
Require Export Zstd.proof.zstd.Spec_api6.
Require Zstd.proof.top.MainPre6.
Require Import Zstd.proof.zstd.NullBuf.
Require Zstd.proof.harness.HCsConv.
Require Zstd.proof.harness.frames.FSpecs Zstd.proof.harness.frames.FStreamSpec.
Require Zstd.proof.harness.frames.FFacts.
Require Import Zstd.proof.harness.frames.FStreamRefused.
Require Import Zstd.proof.harness.rj_reserved_block.Facts_rj_reserved_block.
Import Zstd.proof.harness.frames.FSpecs Zstd.proof.harness.frames.FStreamSpec.
(* last: its Vprog, CompSpecs, Gprog are the harness's *)
Require Export Zstd.proof.harness.rj_reserved_block.HOK_rj_reserved_block.

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
    (QPprog_vars Zstd.contracts.rj_reserved_block.whole_prog).
Proof.
  apply Forall_forall. intros [i v] Hin. apply make_tycontext_g_isSome.
  unfold Vprog, QPvarspecs. rewrite map_map.
  apply in_map_iff. exists (i, v). split; [reflexivity | exact Hin].
Qed.

(* main's precondition: the decoder's globals, split off as in MainPre6.main_pre_fact6 (whose list of
   programs has the x_ laws only) *)
Lemma pre_globals gv :
  InitGPred (Vardefs Zstd.contracts.rj_reserved_block.whole_prog) gv |-- zstd_globals gv * TT.
Proof.
  assert (Hincl: incl Zstd.proof.top.MainPre6.zstd_vardefs (Vardefs Zstd.contracts.rj_reserved_block.whole_prog)).
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


#[local] Instance CCE_HZ : change_composite_env CompSpecs Zstd.units.Zstd.CS.
Proof. make_cs_preserve CompSpecs Zstd.units.Zstd.CS. Defined.

(* the decoder's specifications are stated at Base.CompSpecs; forward_call moves their frame back to the harness's *)
#[local] Instance CCE_BH : change_composite_env Zstd.proof.zstd.Base.CompSpecs CompSpecs.
Proof. make_cs_preserve Zstd.proof.zstd.Base.CompSpecs CompSpecs. Defined.

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

Lemma drop_vp (A: mpred) p : A && valid_pointer p |-- A.
Proof. apply andp_left1, derives_refl. Qed.

(* the same, introduced next to the context's predicate (stream_all's precondition) *)
Lemma dc_res_intro (DC0: globals -> val -> dctx_st -> mpred) DD0 gv d sh :
  DC0 gv d dctx_init |--
  DC0 gv d dctx_init * dict_res DD0 gv sh (dc_dict dctx_init) * set_res DD0 gv sh (dc_set dctx_init) (dc_dict dctx_init).
Proof. unfold dict_res, set_res. simpl. rewrite !sepcon_emp. apply derives_refl. Qed.

(* the model's byte_at is the list's Znth *)
Lemma byte_at_Znth (s: list Z) k : 0 <= k -> byte_at s k = Znth k s.
Proof. intros Hk. unfold byte_at, Znth. rewrite if_false by lia. reflexivity. Qed.

(* a byte read from a frame is an unsigned char *)
Lemma tc_byte z : 0 <= z < 256 -> tc_val tuchar (Vint (Int.repr z)).
Proof. intros Hz. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. Qed.

(* a property of all bytes, checked by computation over 0 .. 255 *)
Lemma all_bytes (f: Z -> bool) :
  forallb f (map Z.of_nat (seq 0 256)) = true -> forall b, 0 <= b < 256 -> f b = true.
Proof.
  intros Hall b Hb. rewrite forallb_forall in Hall. apply Hall.
  apply in_map_iff. exists (Z.to_nat b). split; [lia|]. apply in_seq. lia.
Qed.

(* a frame of new_frame has at least one block *)
Lemma nf_blocks_pos n fcs maxw did c : nf_ok n fcs maxw did c -> (0 < length (nc_blocks c))%nat.
Proof. intros [_ Hbl]. destruct (nc_blocks c); [contradiction | simpl; lia]. Qed.

(* ---------- the harness's offset of the first block header, in C's unsigned int arithmetic ---------- *)

(* the size of Frame_Content_Size as main computes it from the Frame_Header_Descriptor b:
   fcs_flag == 0 ? single : 1 << fcs_flag *)
Definition hdr_t10 (b: Z) : Z := if Z.shiftr b 6 =? 0 then Z.land (Z.shiftr b 5) 1 else 2 ^ Z.shiftr b 6.

Lemma hdr_t10_then b : 0 <= b < 256 -> Int.shru (Int.repr b) (Int.repr 6) = Int.repr 0 ->
  Int.and (Int.shru (Int.repr b) (Int.repr 5)) (Int.repr 1) = Int.repr (hdr_t10 b).
Proof.
  intros Hb H0. apply Int.same_if_eq.
  pose proof (all_bytes (fun b => orb (negb (Int.eq (Int.shru (Int.repr b) (Int.repr 6)) (Int.repr 0)))
    (Int.eq (Int.and (Int.shru (Int.repr b) (Int.repr 5)) (Int.repr 1)) (Int.repr (hdr_t10 b))))
    ltac:(vm_compute; reflexivity) b Hb) as E.
  cbv beta in E. rewrite H0, Int.eq_true in E. exact E.
Qed.

Lemma hdr_t10_ltu b : 0 <= b < 256 -> Int.ltu (Int.shru (Int.repr b) (Int.repr 6)) Int.iwordsize = true.
Proof.
  intros Hb.
  exact (all_bytes (fun b => Int.ltu (Int.shru (Int.repr b) (Int.repr 6)) Int.iwordsize)
    ltac:(vm_compute; reflexivity) b Hb).
Qed.

Lemma hdr_t10_else b : 0 <= b < 256 -> Int.shru (Int.repr b) (Int.repr 6) <> Int.repr 0 ->
  Int.shl (Int.repr 1) (Int.shru (Int.repr b) (Int.repr 6)) = Int.repr (hdr_t10 b).
Proof.
  intros Hb H0. apply Int.same_if_eq.
  pose proof (all_bytes (fun b => orb (Int.eq (Int.shru (Int.repr b) (Int.repr 6)) (Int.repr 0))
    (Int.eq (Int.shl (Int.repr 1) (Int.shru (Int.repr b) (Int.repr 6))) (Int.repr (hdr_t10 b))))
    ltac:(vm_compute; reflexivity) b Hb) as E.
  cbv beta in E. rewrite Int.eq_false in E by exact H0. exact E.
Qed.

(* 5 + !single + (fhd & 3) + ((fhd & 3) == 3) + t10, as main computes it *)
Lemma hdr_at b : 0 <= b < 256 ->
  Int.unsigned (Int.add (Int.add (Int.add
    (Int.repr (5 + Z.b2z (negb (negb (Int.eq (Int.and (Int.shru (Int.repr b) (Int.repr 5)) (Int.repr 1)) Int.zero)))))
    (Int.and (Int.repr b) (Int.repr 3)))
    (Int.repr (Z.b2z (Int.eq (Int.and (Int.repr b) (Int.repr 3)) (Int.repr 3)))))
    (Int.repr (hdr_t10 b))) =
  5 + (1 - Z.land (Z.shiftr b 5) 1) + Z.land b 3 + (if Z.land b 3 =? 3 then 1 else 0) + hdr_t10 b.
Proof.
  intros Hb. apply Z.eqb_eq.
  exact (all_bytes (fun b => Int.unsigned (Int.add (Int.add (Int.add
    (Int.repr (5 + Z.b2z (negb (negb (Int.eq (Int.and (Int.shru (Int.repr b) (Int.repr 5)) (Int.repr 1)) Int.zero)))))
    (Int.and (Int.repr b) (Int.repr 3)))
    (Int.repr (Z.b2z (Int.eq (Int.and (Int.repr b) (Int.repr 3)) (Int.repr 3)))))
    (Int.repr (hdr_t10 b))) =?
    5 + (1 - Z.land (Z.shiftr b 5) 1) + Z.land b 3 + (if Z.land b 3 =? 3 then 1 else 0) + hdr_t10 b)
    ltac:(vm_compute; reflexivity) b Hb).
Qed.

(* ---------- the harness's step from a block header to the next, in C's int arithmetic ---------- *)

(* at += 3 + (Block_Type == 1 ? 1 : Block_Size): the step after the header's 3 bytes *)
Definition blk_step (b0 b1 b2: Z) : Z :=
  if Z.land (Z.shiftr b0 1) 3 =? 1 then 1
  else Z.shiftr (Z.lor (Z.lor b0 (Z.shiftl b1 8)) (Z.shiftl b2 16)) 3.

(* (b0 >> 1 & 3) == 1: an RLE block *)
Lemma blk_rle_eq b : 0 <= b < 256 ->
  Int.eq (Int.and (Int.shr (Int.repr b) (Int.repr 1)) (Int.repr 3)) (Int.repr 1) = (Z.land (Z.shiftr b 1) 3 =? 1).
Proof.
  intros Hb. apply Bool.eqb_prop.
  exact (all_bytes (fun b => Bool.eqb (Int.eq (Int.and (Int.shr (Int.repr b) (Int.repr 1)) (Int.repr 3)) (Int.repr 1))
    (Z.land (Z.shiftr b 1) 3 =? 1)) ltac:(vm_compute; reflexivity) b Hb).
Qed.

Lemma lor_bound a b n : 0 <= n -> 0 <= a < 2 ^ n -> 0 <= b < 2 ^ n -> 0 <= Z.lor a b < 2 ^ n.
Proof.
  intros Hn Ha Hb.
  assert (E: Z.lor a b = Z.lor a b mod 2 ^ n).
  { rewrite <- Z.land_ones by lia. rewrite Z.land_lor_distr_l, !Z.land_ones by lia.
    rewrite (Z.mod_small a), (Z.mod_small b) by lia. reflexivity. }
  rewrite E. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
Qed.

Lemma shl_repr b k : 0 <= b < 256 -> 0 <= k <= 16 -> Int.shl (Int.repr b) (Int.repr k) = Int.repr (Z.shiftl b k).
Proof. intros Hb Hk. unfold Int.shl. rewrite !Int.unsigned_repr by rep_lia. reflexivity. Qed.

Lemma or_repr x y : 0 <= x <= Int.max_unsigned -> 0 <= y <= Int.max_unsigned ->
  Int.or (Int.repr x) (Int.repr y) = Int.repr (Z.lor x y).
Proof. intros Hx Hy. unfold Int.or. rewrite !Int.unsigned_repr by lia. reflexivity. Qed.

(* (b0 | b1 << 8 | b2 << 16) >> 3: Block_Size, less than 2 ^ 21 *)
Lemma blk_size_int b0 b1 b2 : 0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 ->
  Int.shr (Int.or (Int.or (Int.repr b0) (Int.shl (Int.repr b1) (Int.repr 8))) (Int.shl (Int.repr b2) (Int.repr 16)))
    (Int.repr 3) = Int.repr (Z.shiftr (Z.lor (Z.lor b0 (Z.shiftl b1 8)) (Z.shiftl b2 16)) 3) /\
  0 <= Z.shiftr (Z.lor (Z.lor b0 (Z.shiftl b1 8)) (Z.shiftl b2 16)) 3 < 2 ^ 21.
Proof.
  intros H0 H1 H2.
  assert (E1: Z.shiftl b1 8 = b1 * 2 ^ 8) by (apply Z.shiftl_mul_pow2; lia).
  assert (E2: Z.shiftl b2 16 = b2 * 2 ^ 16) by (apply Z.shiftl_mul_pow2; lia).
  assert (B1: 0 <= Z.lor b0 (Z.shiftl b1 8) < 2 ^ 24) by (apply lor_bound; lia).
  assert (B2: 0 <= Z.lor (Z.lor b0 (Z.shiftl b1 8)) (Z.shiftl b2 16) < 2 ^ 24) by (apply lor_bound; lia).
  rewrite (shl_repr b1), (shl_repr b2) by lia.
  rewrite (or_repr b0) by rep_lia. rewrite or_repr by rep_lia.
  rewrite Z.shiftr_div_pow2 by lia.
  split.
  - unfold Int.shr. rewrite Int.signed_repr, Int.unsigned_repr by rep_lia.
    rewrite Z.shiftr_div_pow2 by lia. reflexivity.
  - split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

Lemma blk_step_bound b0 b1 b2 : 0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 ->
  0 <= blk_step b0 b1 b2 < 2 ^ 21.
Proof.
  intros H0 H1 H2. unfold blk_step. destruct (_ =? 1); [lia|]. apply blk_size_int; auto.
Qed.

(* frame[at] |= 6 as main stores it (an unsigned char): the frame with the header at o made Reserved *)
Lemma reserved_zbytes F o : bytes_ok F -> 0 <= o < Zlength F ->
  upd_Znth o (zbytes F) (Vint (Int.zero_ext 8 (Int.or (Int.repr (Znth o F)) (Int.repr 6)))) =
  zbytes (reserved_at F o).
Proof.
  intros Hok Ho.
  assert (Hb: 0 <= Znth o F < 256) by (apply Forall_Znth; first [exact Hok | lia]).
  assert (Ev: Int.zero_ext 8 (Int.or (Int.repr (Znth o F)) (Int.repr 6)) = Int.repr (Z.lor (Znth o F) 6)).
  { apply Int.same_if_eq.
    exact (all_bytes (fun b => Int.eq (Int.zero_ext 8 (Int.or (Int.repr b) (Int.repr 6))) (Int.repr (Z.lor b 6)))
      ltac:(vm_compute; reflexivity) _ Hb). }
  rewrite Ev. unfold reserved_at, set_byte. rewrite byte_at_Znth by lia.
  rewrite upd_Znth_unfold by (rewrite Zlength_map; lia).
  rewrite Zlength_map, !sublist_map, map_app. simpl app. try rewrite map_cons.
  rewrite sublist_firstn, sublist_skip by lia.
  replace (Z.to_nat (o + 1)) with (Z.to_nat o + 1)%nat by lia.
  reflexivity.
Qed.

(* one-shot: ZSTD_decompress's specification on a series its model answers SUnk for and that is refused *)
Lemma oneshot_refused
  (Hunk: forall s, bytes_ok s -> series_refused_m md_dflt sel_none (Some no_dict) no_wlim s ->
         decode_series_m md_dflt sel_none (Some no_dict) no_wlim s = SUnk)
  s cap r out : bytes_ok s -> series_refused_m md_dflt sel_none (Some no_dict) no_wlim s ->
  oneshot_ok md_dflt (Some no_dict) s cap r out -> is_error_code r = true.
Proof. intros Hs Hr [_ Hc]. cbv beta iota in Hc. rewrite (Hunk s Hs Hr) in Hc. exact (Hc Hr). Qed.

Ltac byte_tc :=
  entailer!; first [apply tc_byte; lia | change Byte.max_unsigned with 255 in *; lia | rep_lia].

Ltac dead_branch :=
  first [ contradiction | discriminate
        | exfalso; match goal with H: ?a <> ?a |- _ => apply H; reflexivity end ].

(* the model facts main's proof uses (Facts_rj_reserved_block, FStreamRefused), as one hypothesis: the body is
   proved from their statements, the law from their proofs (Main_rj_reserved_block.rb_facts_ok) *)
Definition rb_facts : Prop :=
  ltac:(let a1 := type of rb_first in let a2 := type of rb_hdr_in in let a3 := type of rb_last in
        let a4 := type of rb_next in let a5 := type of rb_refused in let a6 := type of rb_series_unk in
        let a7 := type of reserved_at_length in let a8 := type of reserved_at_ok in
        let a9 := type of stream_refused_no_end in
        exact (a1 /\ a2 /\ a3 /\ a4 /\ a5 /\ a6 /\ a7 /\ a8 /\ a9)).

Section Main.
Variable DC : globals -> val -> dctx_st -> mpred.
Variable DD : globals -> val -> ddict_st -> mpred.

(* the functions main calls *)
Definition G0 : funspecs :=
  [(_quickproof_malloc, malloc_spec');
   Zstd.proof.zstd.Spec_util.ZSTD_isError_spec; ZSTD_decompress_spec; ZSTD_createDStream_spec DC;
   nondet_u8_spec; gp_assert_spec;
   out_of_memory_spec; @stream_all_spec CompSpecs DC DD; @any_bytes_spec CompSpecs; upto_spec;
   @new_frame_spec CompSpecs].

(* main: the frame with a block made Reserved is refused one-shot (an error) and never reported complete by the
   stream *)
Lemma body_main_G0 : rb_facts -> semax_body Vprog G0 f_main main_spec.
Proof.
  intros FACTS.
  destruct FACTS as (Hfirst & Hhdr & Hlast & Hnext & Hrefused & Hunk & Hrlen & Hrok & Hnoend).
  change (semax_body Vprog G0 f_main (_main, WITH gv: globals PRE [] VST.floyd.VSU.main_pre
    Zstd.contracts.rj_reserved_block.whole_prog tt gv POST [tint] (fun _ : environ => TT))).
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
    forward_call 9223372036854775807.
    Intros cap.
    forward_call (tarray tuchar cap, gv). { simpl. rep_lia. }
    Intros dst.
    forward_call gv.
    Intros zds.
    repeat apply -> seq_assoc. apply semax_if_seq.
    forward_if; [| dead_branch]. forward.
    apply semax_if_seq. forward_if; [| dead_branch]. forward.
    forward_if; [| dead_branch]. forward. entailer!. }
  subst n.
  unfold mbytes at 1. rewrite if_false by exact Hd0. Intros.
  assert_PROP (isptr data) as Hdp by (entailer!; apply isptr_of; auto).
  forward_if; [destruct data; try contradiction; discriminate |].
  sep_apply (tok_to_Z Ews (Zlength l) data).
  forward_call (gv, Ews, data, l, Zlength l, 2 ^ 27, 0, Tsh, v_len,
                Zstd.proof.zstd.Spec_xxh.pw_token Ews (tarray tuchar (Zlength l)) data).
  { simpl pw_pred. unfold Zstd.proof.zstd.Base.CompSpecs. cancel. }
  { apply tok_wvp. assumption. }
  Intros vret. destruct vret as [q d']. cbn [fst snd] in *.
  simpl pw_pred. unfold Zstd.proof.zstd.Base.CompSpecs. sep_apply (tok_of_Z Ews (Zlength l) data).
  forward.
  forward_call 9223372036854775807.
  Intros cap.
  forward_call (tarray tuchar cap, gv). { simpl. rep_lia. }
  Intros dst.
  forward_call gv.
  Intros zds.
  repeat apply -> seq_assoc. apply semax_if_seq.
  destruct (eq_dec q nullval) as [Hq0|Hq0].
  { (* out of memory in new_frame: no frame; the run ends *)
    subst q. forward_if; [| dead_branch]. forward.
    apply semax_if_seq. forward_if; [| dead_branch]. forward.
    forward_if; [| dead_branch]. forward. entailer!. }
  Intros c. subst d'.
  match goal with H: nf_ok _ _ _ _ c |- _ => rename H into Hnf end.
  match goal with H: Zlength l <= (PTRDIFF_MAX - 26) / 4 |- _ => rename H into Hlmax end.
  pose proof (Zstd.proof.harness.frames.FFacts.nf_bytes_length l (Zlength l) (2 ^ 27) 0 c Hnf) as HFl.
  pose proof (Zstd.proof.harness.frames.FFacts.nf_bytes_ok l (Zlength l) (2 ^ 27) 0 c Hnf H1) as HFok.
  assert (HnB: 26 + 4 * Zlength l <= 2 ^ 63 - 1).
  { unfold PTRDIFF_MAX in Hlmax. change ((2 ^ 63 - 1 - 26) / 4) with 2305843009213693945 in Hlmax. lia. }
  set (F := nf_bytes l (Zlength l) 0 c) in *.
  unfold mbytes at 1. destruct (eq_dec q nullval) as [C|_]; [contradiction|]. Intros.
  assert_PROP (isptr q) as Hqp by (entailer!; apply isptr_of; auto).
  forward_if; [destruct q; try contradiction; discriminate |].
  destruct (eq_dec dst nullval) as [Hdst0|Hdst0].
  { subst dst. forward.
    apply semax_if_seq. forward_if; [| dead_branch]. forward.
    forward_if; [| dead_branch]. forward. entailer!. }
  Intros.
  assert_PROP (isptr dst) as Hdp' by (entailer!; apply isptr_of; auto).
  destruct dst as [| | | | | bd od]; try contradiction.
  forward.
  apply semax_if_seq. forward_if; [dead_branch |].
  destruct (eq_dec zds nullval) as [Hz0|Hz0].
  { subst zds. forward. forward_if; [| dead_branch]. forward. entailer!. }
  assert_PROP (isptr zds) as Hzp.
  { entailer!. apply isptr_of; auto. }
  destruct zds as [| | | | | bz oz]; try contradiction.
  forward.
  forward_if; [dead_branch |].
  set (dst := Vptr bd od). set (zds := Vptr bz oz).
  (* the model facts for this frame *)
  assert (Hrb: rb_frame l (Zlength l) (2 ^ 27) 0 c).
  { unfold rb_frame. unfold PTRDIFF_MAX in Hlmax. split; [exact Hnf|]. split; [exact H1|]. lia. }
  specialize (Hfirst _ _ _ _ _ Hrb).
  pose proof (fun i => Hhdr _ _ _ _ _ i Hrb) as Hhdr'. clear Hhdr. rename Hhdr' into Hhdr.
  pose proof (fun i => Hlast _ _ _ _ _ i Hrb) as Hlast'. clear Hlast. rename Hlast' into Hlast.
  pose proof (fun i => Hnext _ _ _ _ _ i Hrb) as Hnext'. clear Hnext. rename Hnext' into Hnext.
  pose proof (fun i md sel cur => Hrefused _ _ _ _ _ i md sel cur Hrb) as Hrefused'.
  clear Hrefused. rename Hrefused' into Hrefused.
  fold F in Hfirst, Hhdr, Hlast, Hnext, Hrefused.
  (* from here on F is only known by these facts: VST's tactics would otherwise compute with its definition *)
  clearbody F.
  destruct Hfirst as [HF4 Hat0].
  assert (Hb4: 0 <= Znth 4 F < 256) by (apply Forall_Znth; first [exact HFok | lia]).
  rewrite (byte_at_Znth F 4) in Hat0 by lia.
  forward.
  { byte_tc. }
  forward. forward.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _t'10 (Vint (Int.repr (hdr_t10 (Znth 4 F)))) :: Q) (SEPx R))) end.
  { forward. entailer!. match goal with H: Int.shru _ _ = _ |- _ => rewrite (hdr_t10_then _ Hb4 H) end. reflexivity. }
  { forward.
    - entailer!. pose proof (hdr_t10_ltu _ Hb4) as Hl. unfold Int.ltu in Hl.
      destruct zlt; [assumption | discriminate].
    - entailer!. match goal with H: Int.shru _ _ <> _ |- _ => rewrite (hdr_t10_else _ Hb4 H) end. reflexivity. }
  forward.
  { entailer!. destruct (Int.eq _ _); compute; split; discriminate. }
  rewrite (hdr_at _ Hb4).
  change (if Z.shiftr (Znth 4 F) 6 =? 0 then Z.land (Z.shiftr (Znth 4 F) 5) 1 else 2 ^ Z.shiftr (Znth 4 F) 6)
    with (hdr_t10 (Znth 4 F)) in Hat0.
  rewrite Hat0.
  (* the walk over the block headers: at is the offset of the i-th header *)
  forward_call tt.
  Intros sk0.
  pose proof (nf_blocks_pos _ _ _ _ _ Hnf) as Hpos.
  forward_loop (EX i: nat, EX sk: Z,
    PROP ((i < length (nc_blocks c))%nat; 0 <= sk <= 255)
    LOCAL (temp _skip (Vint (Int.repr sk)); temp _at (Vlong (Int64.repr (blk_off (Zlength l) 0 c i)));
           temp _zds zds; temp _dst dst; temp _cap (Vlong (Int64.repr cap)); temp _frame q;
           lvar _completed tulong v_completed; lvar _written tulong v_written; lvar _len tulong v_len; gvars gv)
    SEP (mem_mgr gv; zstd_globals gv; DC gv zds dctx_init && valid_pointer zds;
         malloc_token Ews (tarray tuchar cap) dst; data_at_ Ews (tarray tuchar cap) dst;
         malloc_token Ews (tarray tuchar (Zlength l)) data;
         data_at Ews (tarray tuchar (Zlength l)) (zbytes (nf_data l c)) data;
         data_at Tsh tulong (Vlong (Int64.repr (Zlength F))) v_len;
         malloc_token Ews (tarray tuchar (Zlength F)) q; data_at Ews (tarray tuchar (Zlength F)) (zbytes F) q;
         data_at_ Tsh tulong v_completed; data_at_ Tsh tulong v_written; TT; has_ext tt))
  continue: (EX i: nat, EX sk: Z,
    PROP ((i < length (nc_blocks c))%nat; 1 <= sk <= 255)
    LOCAL (temp _skip (Vint (Int.repr sk)); temp _at (Vlong (Int64.repr (blk_off (Zlength l) 0 c i)));
           temp _zds zds; temp _dst dst; temp _cap (Vlong (Int64.repr cap)); temp _frame q;
           lvar _completed tulong v_completed; lvar _written tulong v_written; lvar _len tulong v_len; gvars gv)
    SEP (mem_mgr gv; zstd_globals gv; DC gv zds dctx_init && valid_pointer zds;
         malloc_token Ews (tarray tuchar cap) dst; data_at_ Ews (tarray tuchar cap) dst;
         malloc_token Ews (tarray tuchar (Zlength l)) data;
         data_at Ews (tarray tuchar (Zlength l)) (zbytes (nf_data l c)) data;
         data_at Tsh tulong (Vlong (Int64.repr (Zlength F))) v_len;
         malloc_token Ews (tarray tuchar (Zlength F)) q; data_at Ews (tarray tuchar (Zlength F)) (zbytes F) q;
         data_at_ Tsh tulong v_completed; data_at_ Tsh tulong v_written; TT; has_ext tt))
  break: (EX i: nat,
    PROP ((i < length (nc_blocks c))%nat)
    LOCAL (temp _at (Vlong (Int64.repr (blk_off (Zlength l) 0 c i))); temp _zds zds; temp _dst dst; temp _cap (Vlong (Int64.repr cap)); temp _frame q;
           lvar _completed tulong v_completed; lvar _written tulong v_written; lvar _len tulong v_len; gvars gv)
    SEP (mem_mgr gv; zstd_globals gv; DC gv zds dctx_init && valid_pointer zds;
         malloc_token Ews (tarray tuchar cap) dst; data_at_ Ews (tarray tuchar cap) dst;
         malloc_token Ews (tarray tuchar (Zlength l)) data;
         data_at Ews (tarray tuchar (Zlength l)) (zbytes (nf_data l c)) data;
         data_at Tsh tulong (Vlong (Int64.repr (Zlength F))) v_len;
         malloc_token Ews (tarray tuchar (Zlength F)) q; data_at Ews (tarray tuchar (Zlength F)) (zbytes F) q;
         data_at_ Tsh tulong v_completed; data_at_ Tsh tulong v_written; TT; has_ext tt)).
  { Exists 0%nat sk0. entailer!. }
  - (* the loop body *)
    Intros i sk.
    match goal with H: (i < _)%nat |- _ => rename H into Hi end.
    match goal with H: 0 <= sk <= 255 |- _ => rename H into Hsk end.
    destruct (Hhdr i Hi) as [Ho0 Ho3].
    pose proof (Hlast i Hi) as Hli.
    set (o := blk_off (Zlength l) 0 c i) in *.
    rewrite (byte_at_Znth F o) in Hli by lia.
    assert (Hb0: 0 <= Znth o F < 256) by (apply Forall_Znth; first [exact HFok | lia]).
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp _t'12 (Vint (Int.repr
        (if andb (0 <? sk) (Z.land (Znth o F) 1 =? 0) then 1 else 0))) :: Q) (SEPx R))) end.
    + forward. { byte_tc. } forward. entailer!.
      rewrite Hli. rewrite (proj2 (Z.ltb_lt 0 sk)) by lia. destruct (_ =? _)%nat; reflexivity.
    + forward. entailer!. rewrite (proj2 (Z.ltb_ge 0 sk)) by lia. reflexivity.
    + forward_if.
      * (* not the last block and skip > 0: the step to the next header *)
        match goal with H: (if _ then 1 else 0) <> 0 |- _ => rename H into Hgo end.
        assert (Hsk1: 0 < sk /\ Z.land (Znth o F) 1 = 0).
        { destruct (0 <? sk) eqn:E1; [|simpl in Hgo; contradiction].
          destruct (Z.land (Znth o F) 1 =? 0) eqn:E2; [|simpl in Hgo; contradiction].
          split; [apply Z.ltb_lt | apply Z.eqb_eq]; assumption. }
        destruct Hsk1 as [Hsk1 Hb0l].
        assert (Hsi: (S i < length (nc_blocks c))%nat).
        { rewrite Hb0l in Hli. destruct (S i =? length (nc_blocks c))%nat eqn:E; [discriminate|].
          apply Nat.eqb_neq in E. lia. }
        pose proof (Hnext i Hsi) as Hn. fold o in Hn.
        rewrite !byte_at_Znth in Hn by lia.
        assert (Hb1: 0 <= Znth (o + 1) F < 256) by (apply Forall_Znth; first [exact HFok | lia]).
        assert (Hb2: 0 <= Znth (o + 2) F < 256) by (apply Forall_Znth; first [exact HFok | lia]).
        change (if Z.land (Z.shiftr (Znth o F) 1) 3 =? 1 then 1
                else Z.shiftr (Z.lor (Z.lor (Znth o F) (Z.shiftl (Znth (o + 1) F) 8)) (Z.shiftl (Znth (o + 2) F) 16)) 3)
          with (blk_step (Znth o F) (Znth (o + 1) F) (Znth (o + 2) F)) in Hn.
        pose proof (blk_step_bound _ _ _ Hb0 Hb1 Hb2) as Hstep.
        forward. { byte_tc. }
        match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
          forward_if (PROPx P (LOCALx (temp _t'13 (Vint (Int.repr
            (blk_step (Znth o F) (Znth (o + 1) F) (Znth (o + 2) F)))) :: Q) (SEPx R))) end.
        -- (* an RLE block: 1 byte *)
           forward. entailer!.
           match goal with H: Int.and (Int.shr _ _) _ = Int.repr 1 |- _ =>
             assert (E: (Z.land (Z.shiftr (Znth o F) 1) 3 =? 1) = true)
               by (rewrite <- (blk_rle_eq _ Hb0), H; reflexivity) end.
           unfold blk_step. rewrite E. reflexivity.
        -- (* a Raw block: Block_Size bytes *)
           forward; try byte_tc. forward; try byte_tc. forward; try byte_tc. forward.
           entailer!.
           match goal with H: Int.and (Int.shr _ _) _ <> Int.repr 1 |- _ =>
             assert (E: (Z.land (Z.shiftr (Znth o F) 1) 3 =? 1) = false)
               by (rewrite <- (blk_rle_eq _ Hb0); apply Int.eq_false; exact H) end.
           unfold blk_step. rewrite E.
           rewrite (proj1 (blk_size_int _ _ _ Hb0 Hb1 Hb2)). reflexivity.
        -- forward.
           Exists (S i) sk. entailer!. rewrite Hn. f_equal. f_equal. lia.
      * forward. Exists i. entailer!.
  - (* skip-- *)
    Intros i sk. forward. Exists i (sk - 1). entailer!.
  - (* after the walk: the header at o gets Block_Type 3 *)
    Intros i.
    match goal with H: (i < _)%nat |- _ => rename H into Hi end.
    destruct (Hhdr i Hi) as [Ho0 Ho3].
    set (o := blk_off (Zlength l) 0 c i) in *.
    assert (Hb0: 0 <= Znth o F < 256) by (apply Forall_Znth; first [exact HFok | lia]).
    forward; try byte_tc.
    forward.
    rewrite (reserved_zbytes F o HFok) by lia.
    (* the frame now: F' = reserved_at F o, a series zstd refuses *)
    set (F' := reserved_at F o) in *.
    assert (HF'l: Zlength F' = Zlength F) by (apply Hrlen; lia).
    assert (HF'ok: bytes_ok F') by (apply Hrok; [exact HFok | lia]).
    destruct (Hrefused i md_dflt sel_none (Some no_dict) Hi eq_refl eq_refl ltac:(reflexivity) ltac:(discriminate))
      as [Hr1 _].
    destruct (Hrefused i (dmode_w (dmode_of (dc_par dctx_init))) (fst (st_sel dctx_init)) (snd (st_sel dctx_init))
      Hi eq_refl eq_refl ltac:(reflexivity) ltac:(simpl; discriminate)) as [Hr2 Hr3].
    fold o F' in Hr1, Hr2, Hr3.
    clearbody F'.
    rewrite <- HF'l.
    (* ZSTD_decompress(dst, cap, frame, len), at the decoder's compspecs; the malloc_tokens vouch for the buffers *)
    forward.
    sep_apply (to_Z Ews (Zlength F') (zbytes F') q).
    sep_apply (to_Z_ Ews cap dst).
    sep_apply (tok_to_Z Ews (Zlength F') q).
    sep_apply (tok_to_Z Ews cap dst).
    sep_apply (pws_fold (tarray tuchar (Zlength F')) q (tarray tuchar cap) dst).
    forward_call ([pw_token Ews (tarray tuchar (Zlength F')) q; pw_token Ews (tarray tuchar cap) dst],
                  gv, Ews, dst, cap, Ews, q, F').
    { split; (apply buf_ok_tok; [simpl; tauto | auto | lia | first [exact Hdp' | exact Hqp]]). }
    Intros vret. destruct vret as [r out]. cbn [fst snd] in *. rewrite mbuf_isptr by auto.
    match goal with H: oneshot_ok _ _ _ _ _ _ |- _ => rename H into Hok1 end.
    (* the model: the series is refused one-shot *)
    pose proof (oneshot_refused Hunk F' cap r out HF'ok Hr1 Hok1) as Herr.
    forward.
    (* stream_all(zds, frame, len, dst, cap, &written, &completed), at the harness's compspecs *)
    forward.
    sep_apply (of_Z Ews (Zlength F') (zbytes F') q).
    sep_apply (of_Z Ews cap out dst).
    sep_apply (drop_vp (DC gv zds dctx_init) zds).
    sep_apply (dc_res_intro DC DD gv zds Ews).
    forward_call ([pw_token Ews (tarray tuchar (Zlength F')) q; pw_token Ews (tarray tuchar cap) dst],
                  gv, zds, dctx_init, Ews, q, F', Ews, dst, cap, out, Tsh, v_written, Tsh, v_completed).
    { cancel. }
    { split; [unfold stream_dict_ok; simpl; auto |].
      split; (apply buf_ok_tok; [simpl; tauto | auto | lia | first [exact Hdp' | exact Hqp]]). }
    Intros vret. destruct vret as [[r2 y] z]. cbn [fst snd] in *.
    match goal with Hc: stream_call _ _ _ y r2 z |- _ => rename Hc into Hcall end.
    match goal with Hr: stream_run _ _ _ _ y |- _ => rename Hr into Hrun end.
    assert (Hr2r: 0 <= r2 <= Int64.max_unsigned) by (destruct Hcall as (? & ? & ? & _ & _ & Hr & _); exact Hr).
    (* the model: no call of the run returns 0 *)
    pose proof (Hnoend F' cap dst dctx_init out y r2 z HF'ok ltac:(reflexivity) ltac:(reflexivity) Hr2 Hr3 Hrun Hcall)
      as Hdone.
    rewrite Hdone.
    forward.
    (* out_of_memory(result) || out_of_memory(last): the run ends *)
    repeat apply -> seq_assoc.
    forward_call r.
    apply semax_if_seq. forward_if.
    { forward. forward_if; [forward; entailer! | dead_branch]. }
    (* t'18 = out_of_memory(last); t'17 = (_Bool) t'18: the call, then the cast as a statement of its own *)
    eapply semax_seq'.
    forward_call r2.
    forward. apply andp_left2. apply derives_refl.
    abbreviate_semax.
    forward_if; [forward; entailer! |].
    (* the check: ZSTD_isError(result) && completed == 0 *)
    forward_call r. rewrite Herr.
    apply semax_if_seq. forward_if; [| dead_branch].
    forward. forward.
    forward_call Int.one.
    forward.
    cancel.
Qed.

End Main.
