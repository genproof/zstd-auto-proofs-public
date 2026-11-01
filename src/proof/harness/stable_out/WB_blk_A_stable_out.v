(* w_compressed_block, segment A (statements 0..11: out_t blk, the counters, the literals mode) in the unit
   stable_out: seg_A of WBlkDefs_stable_out.  Template: WB_blk_A.

   Proof shape: the big statics stay in data_at_ form (or folded in blk_fixed) while going forward; the
   literals mode is drawn by cases (have_huf, then choose's result), each `if (litmode == k)` is pushed
   into both branches (semax_if_seq) and decided; at K the big SEP items are made opaque variables
   (blkA_hide) before entailer! (cancel unfolds them otherwise and overflows the stack). *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.harness.stable_out.WBlkDefs_stable_out.
Local Open Scope logic.

(* ---------- helpers: the statics' initial forms, blk's out_t ---------- *)

(* WM_BlkGen.gen_nil, proved here (same statement) *)
Lemma blkA_gen_nil : forall wsize rep0 hist out, gen_ok wsize rep0 hist out [] [] [] rep0.
Proof. intros. unfold gen_ok. intros Y. simpl. rewrite app_nil_r. reflexivity. Qed.

Lemma blkA_set_rep_same : forall S, set_rep S (wt_rep S) = S.
Proof. intros [r h t]. reflexivity. Qed.

Lemma blkA_code_rows_nil : forall p,
  data_at_ Ews (tarray (tarray tuchar 65536) 3) p =
  data_at Ews (tarray (tarray tuchar 65536) 3) (code_rows []) p.
Proof.
  intros. rewrite (data_at__tarray' Ews (tarray tuchar 65536) 3 (code_rows [])); [reflexivity |].
  unfold code_rows. rewrite Zlength_nil. cbn [map app]. rewrite Z.sub_0_r. reflexivity.
Qed.

Lemma blkA_extra_rows_nil : forall p,
  data_at_ Ews (tarray (tarray tuint 65536) 3) p =
  data_at Ews (tarray (tarray tuint 65536) 3) (extra_rows []) p.
Proof.
  intros. rewrite (data_at__tarray' Ews (tarray tuint 65536) 3 (extra_rows [])); [reflexivity |].
  unfold extra_rows. rewrite Zlength_nil. cbn [map app]. rewrite Z.sub_0_r. reflexivity.
Qed.

Lemma blkA_lit_nil : forall p,
  data_at_ Ews (tarray tuchar 131072) p =
  data_at Ews (tarray tuchar 131072) (zbytes [] ++ Zrepeat Vundef (131072 - Zlength (@nil Z))) p.
Proof.
  intros. rewrite (data_at__tarray' Ews tuchar 131072 (zbytes [] ++ Zrepeat Vundef (131072 - Zlength (@nil Z))));
    [reflexivity |].
  rewrite Zlength_nil, Z.sub_0_r. reflexivity.
Qed.

Lemma blkA_out : forall p v,
  out_rep Tsh Ews v p 135168 [] (Zrepeat Vundef 135168) =
  data_at Tsh t_out (p, (Vlong (Int64.repr (Int.signed (Int.repr 0))), Vptrofs (Ptrofs.repr 135168))) v *
  data_at_ Ews (tarray tuchar 135168) p.
Proof.
  intros. unfold out_rep. rewrite data_at__tarray. apply prop_true_andp.
  split; [rewrite Zlength_nil, Zlength_Zrepeat by lia; reflexivity | constructor].
Qed.

Lemma blkA_perm : forall A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 : mpred,
  A1 * A2 * A3 * A4 * A5 * A6 * A7 * A8 * A9 * A10 * A11 * A12 * A13 * A14 =
  (A1 * A2 * A3 * A6 * A9 * A11 * A12 * A13 * A14) * A4 * A5 * A7 * A8 * A10.
Proof. intros. apply pred_ext; cancel. Qed.

(* G_blk at the entry: blk_fixed, w_code, w_extra, w_lit, blk_buf, newhuf (the big arrays stay in
   data_at_ form while going forward: saturate_local on code_rows [] would compute its 65536 rows) *)
Lemma blkA_G : forall gv,
  G_blk gv =
  blk_fixed gv *
  data_at_ Ews (tarray (tarray tuchar 65536) 3) (gv _x_stable_out__w_code) *
  data_at_ Ews (tarray (tarray tuint 65536) 3) (gv _x_stable_out__w_extra) *
  data_at_ Ews (tarray tuchar 131072) (gv _x_stable_out__w_lit) *
  data_at_ Ews (tarray tuchar 135168) (gv _x_stable_out__blk_buf) *
  (EX v: reptype t_huf, !! huf_def v && data_at Ews t_huf v (gv _x_stable_out__newhuf)).
Proof.
  intros. unfold G_blk, blk_fixed. apply blkA_perm.
Qed.

(* the big SEP items as opaque variables (cancel would unfold them and overflow the stack) *)
Ltac blkA_hide :=
  repeat match goal with
  | |- context [data_at_ Ews ?ty ?q] =>
      let X := fresh "X" in set (X := data_at_ Ews ty q); clearbody X
  | |- context [blk_fixed ?g] => let X := fresh "X" in set (X := blk_fixed g); clearbody X
  | |- context [data_at Ews (tarray tuchar HIST_SIZE) ?v ?q] =>
      let X := fresh "X" in set (X := data_at Ews (tarray tuchar HIST_SIZE) v q); clearbody X
  | |- context [data_at Ews t_huf ?v ?q] =>
      let X := fresh "X" in set (X := data_at Ews t_huf v q); clearbody X
  | |- context [data_at ?sh t_wstate ?v ?q] =>
      let X := fresh "X" in set (X := data_at sh t_wstate v q); clearbody X
  | |- context [out_rep ?a ?b ?c ?d ?e ?f ?g] =>
      let X := fresh "X" in set (X := out_rep a b c d e f g); clearbody X
  end.

Lemma blkA_rep_ok : forall S, wt_ok S -> rep_ok (wt_rep S).
Proof. intros S [H _]. unfold rep_ok. destruct (wt_rep S) as [[a b] c]. exact H. Qed.

(* at K: the entailment into blk_gen with the literals mode lm (rleb, Hl), newhuf holding nh *)
Ltac blkA_end HK stv htl lm rleb Hl nh :=
  eapply semax_pre; [| exact HK];
  Exists lm rleb Hl;
  unfold blk_gen, blk_locals, blk_bsm, hp_val; blk_env_simpl;
  Exists stv htl nh;
  rewrite blkA_set_rep_same, blkA_out, <- blkA_code_rows_nil, <- blkA_extra_rows_nil, <- blkA_lit_nil;
  rewrite !app_nil_r, Zlength_nil, Z.add_0_r;
  clear HK; blkA_hide; entailer!.

Lemma blkA_lm_ok : forall S lm rleb Hl, 0 <= lm <= 3 -> 0 <= rleb < 256 ->
  (2 <= lm -> huf_ok Hl) -> (lm = 3 -> wt_huf S = Some Hl) -> lm_ok S lm rleb Hl.
Proof. intros. unfold lm_ok. auto. Qed.

Lemma blkA_huf_ok : forall S H, wt_ok S -> wt_huf S = Some H -> huf_ok H.
Proof. intros S H [_ [Hh _]] E. exact (Hh H E). Qed.

(* the pure part of blk_gen left by entailer! *)
Ltac blkA_pure :=
  lazymatch goal with
  | |- lm_ok _ _ _ _ /\ _ =>
      split; [apply blkA_lm_ok; intros; first [lia | assumption | eapply blkA_huf_ok; eassumption] |]
  | _ => idtac
  end;
  repeat match goal with |- _ /\ _ => split end;
  first [ apply blkA_gen_nil | apply blkA_rep_ok; assumption | solve [constructor] | rewrite ?Zlength_nil; lia
        | intros; assumption | solve [auto]
        | unfold field_address; destruct (field_compatible_dec _ _ _) as [_ | Hn];
            [reflexivity | exfalso; apply Hn; auto with field_compatible] ].

Definition blkA_H0 : whuf := {| wh_w := []; wh_log := 0; wh_last := 0; wh_used := [] |}.

Lemma seg_A_ok : seg_A.
Proof.
  unfold seg_A. blk_seg_start.
  unfold blk_entry, blk_env_ok, blk_locals, blk_bsm in *.
  destruct E as [gv osh bsh o p cap bs tl ssh stp stv S hsh hnp hist out htl t window
                 vblk vmode vopts vvalid vforms vopts1 vbt]; blk_env_simpl.
  destruct H as (Hosh & Hbsh & Hssh & Hhsh & Hwt & Hrep & Hbh & Hbo & Hlh & Hlo & Hwin & Ht & Hhs & Hhl).
  rewrite blkA_G. Intros nhv.
  forward. forward. forward.
  forward. forward. forward. forward. forward.
  assert (Hhh: wv_have_huf stv = vb (match wt_huf S with Some _ => true | None => false end)) by apply Hrep.
  forward. forward. forward. forward. forward. forward. forward. forward. forward. forward.
  forward.
  { match goal with |- context [tc_val tint ?v] => replace v with (vb (match wt_huf S with Some _ => true | None => false end)) by (symmetry; exact Hhh) end.
    entailer!; destruct (wt_huf S); exact I. }
  match goal with |- context [temp _x_stable_out__t'115 ?v] => replace v with (vb (match wt_huf S with Some _ => true | None => false end)) by (symmetry; exact Hhh) end.
  destruct (wt_huf S) as [Hs|] eqn:EH.
- apply semax_if_seq. forward_if. 2: { exfalso. discriminate. }
  forward. forward. forward. forward_call 4. Intros r.
  assert (Hr: r = 0 \/ r = 1 \/ r = 2 \/ r = 3) by lia.
  destruct Hr as [-> | [-> | [-> | ->]]]; forward.
  + (* raw *)
    apply semax_if_seq; forward_if; [exfalso; lia |].
    apply semax_if_seq; forward_if; [exfalso; lia |].
    apply semax_if_seq; forward_if; [exfalso; lia |].
    blkA_end H0 stv htl 0 0 blkA_H0 nhv. all: blkA_pure.
  + (* RLE *)
    apply semax_if_seq; forward_if; [| exfalso; lia].
    forward_call 256. Intros rb.
    apply semax_if_seq; forward_if; [exfalso; lia |].
    apply semax_if_seq; forward_if; [exfalso; lia |].
    blkA_end H0 stv htl 1 rb blkA_H0 nhv. all: blkA_pure.
  + (* new Huffman code *)
    apply semax_if_seq; forward_if; [exfalso; lia |].
    apply semax_if_seq; forward_if; [| exfalso; lia].
    forward_call (Ews, gv _x_stable_out__newhuf, nhv). Intros vret. destruct vret as [Hl nhv']; cbn [fst snd] in *. forward.
    apply semax_if_seq; forward_if; [exfalso; lia |].
    blkA_end H0 stv htl 2 0 Hl nhv'. all: blkA_pure.
  + (* st's Huffman code *)
    apply semax_if_seq; forward_if; [exfalso; lia |].
    apply semax_if_seq; forward_if; [exfalso; lia |].
    apply semax_if_seq; forward_if; [| exfalso; lia].
    forward.
    assert_PROP (field_compatible t_wstate [] stp) as Hfc by entailer!.
    blkA_end H0 stv htl 3 0 Hs nhv. all: blkA_pure.
- apply semax_if_seq. forward_if.
  { exfalso. match goal with Hc: Int.repr 0 <> Int.zero |- _ => apply Hc; reflexivity end. }
  forward_call 3. Intros r.
  assert (Hr: r = 0 \/ r = 1 \/ r = 2) by lia.
  destruct Hr as [-> | [-> | ->]]; forward.
  + (* raw *)
    apply semax_if_seq; forward_if; [exfalso; lia |].
    apply semax_if_seq; forward_if; [exfalso; lia |].
    apply semax_if_seq; forward_if; [exfalso; lia |].
    blkA_end H0 stv htl 0 0 blkA_H0 nhv. all: blkA_pure.
  + (* RLE *)
    apply semax_if_seq; forward_if; [| exfalso; lia].
    forward_call 256. Intros rb.
    apply semax_if_seq; forward_if; [exfalso; lia |].
    apply semax_if_seq; forward_if; [exfalso; lia |].
    blkA_end H0 stv htl 1 rb blkA_H0 nhv. all: blkA_pure.
  + (* new Huffman code *)
    apply semax_if_seq; forward_if; [exfalso; lia |].
    apply semax_if_seq; forward_if; [| exfalso; lia].
    forward_call (Ews, gv _x_stable_out__newhuf, nhv). Intros vret. destruct vret as [Hl nhv']; cbn [fst snd] in *. forward.
    apply semax_if_seq; forward_if; [exfalso; lia |].
    blkA_end H0 stv htl 2 0 Hl nhv'. all: blkA_pure.
Qed.
