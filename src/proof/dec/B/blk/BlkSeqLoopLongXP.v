(* The long loop against the exact block model: the last literals (the epilogue) (BlkSeqLoopLongX: the predicates). Plain Coq. *)
Require Export Zstd.proof.dec.B.blk.BlkSeqLoopLongX.
Require Import Zstd.proof.model.ExCSeq Zstd.proof.model.ExBlock.
Require Import Coq.micromega.Lia.
Local Open Scope Z_scope.

(* ---------- the C's copies of the last literals as xl_put ---------- *)

(* reading k cells of the output array in order gives its sublist *)
Lemma xp_lrdn (k: nat) (c: list val) (i: Z) :
  0 <= i -> i + Z.of_nat k <= Zlength c -> lrdn k c LW i = sublist i (i + Z.of_nat k) c.
Proof.
  revert i. induction k as [|k IH]; intros i Hi Hk.
  - cbn. rewrite sublist_nil' by lia. reflexivity.
  - cbn [lrdn lrd]. rewrite IH by lia.
    rewrite (sublist_split i (i + 1) (i + Z.of_nat (S k))) by lia. rewrite (sublist_one i (i + 1)) by lia.
    cbn [app]. f_equal. f_equal. lia.
Qed.

(* the stores of a run of values at d replace the cells [d, d + |vs|) *)
Lemma xp_lwrn (vs c: list val) (d: Z) :
  0 <= d -> d + Zlength vs <= Zlength c -> lwrn vs c d = xl_put c d vs.
Proof.
  revert c d. induction vs as [|v vs IH]; intros c d Hd Hb.
  - cbn [lwrn]. unfold xl_put. list_solve.
  - rewrite Zlength_cons in Hb. pose proof (Zlength_nonneg vs).
    cbn [lwrn]. rewrite IH; [|lia|list_solve]. unfold xl_put. list_solve.
Qed.

(* memmove within the output array (all read, then all stored): the cells [d, d + k) take the old [i, i + k) *)
Lemma xp_lmove (k: nat) (c: list val) (d i: Z) :
  0 <= d -> 0 <= i -> i + Z.of_nat k <= Zlength c -> d + Z.of_nat k <= Zlength c ->
  lmove k c d LW i = xl_put c d (sublist i (i + Z.of_nat k) c).
Proof.
  intros. unfold lmove. rewrite xp_lrdn by lia. apply xp_lwrn; [lia|]. rewrite Zlength_sublist by lia. lia.
Qed.

(* memcpy from a separate array (the input, litExtraBuffer): the cells [d, d + k) take the source's [i, i + k) *)
Lemma xp_lfwd_LS (k: nat) (c cs: list val) (d i: Z) :
  0 <= d -> 0 <= i -> i + Z.of_nat k <= Zlength cs -> d + Z.of_nat k <= Zlength c ->
  lfwd k c d (LS cs) i = xl_put c d (sublist i (i + Z.of_nat k) cs).
Proof.
  intros Hd Hi Hs Hc. rewrite <- xp_lwrn by (rewrite ?Zlength_sublist; lia).
  revert c d i Hd Hi Hs Hc. induction k as [|k IH]; intros c d i Hd Hi Hs Hc.
  - cbn. rewrite sublist_nil' by lia. reflexivity.
  - cbn [lfwd lrd]. rewrite IH by (rewrite ?Zlength_upd_Znth; lia).
    rewrite (sublist_split i (i + 1) (i + Z.of_nat (S k))) by lia. rewrite (sublist_one i (i + 1)) by lia.
    cbn [app lwrn]. f_equal. f_equal. lia.
Qed.

(* memcpy within the output array, the source at or after the end of the destination (literals in dst lie at
   or after oend): as a move *)
Lemma xp_lfwd_LW (k: nat) (c: list val) (d i: Z) :
  0 <= d -> d + Z.of_nat k <= i -> i + Z.of_nat k <= Zlength c ->
  lfwd k c d LW i = xl_put c d (sublist i (i + Z.of_nat k) c).
Proof.
  revert c d i. induction k as [|k IH]; intros c d i Hd Hdi Hc; cbn [lfwd lrd].
  - rewrite sublist_nil' by lia. unfold xl_put. list_solve.
  - rewrite Nat2Z.inj_succ in *.
    rewrite IH by (rewrite ?Zlength_upd_Znth; lia).
    unfold xl_put. rewrite Zlength_upd_Znth, !Zlength_sublist by (rewrite ?Zlength_upd_Znth; lia).
    replace (i + 1 + Z.of_nat k) with (i + Z.succ (Z.of_nat k)) by lia.
    replace (d + 1 + (i + Z.succ (Z.of_nat k) - (i + 1))) with (d + (i + Z.succ (Z.of_nat k) - i)) by lia.
    list_solve.
Qed.

(* the last literals, split head first (lastLLSize = litBufferEnd - litPtr: checked against oend, memmove to
   op = d + K of the head's rest, at lit_li of the output array), then litExtraBuffer from its start *)
Lemma xl_epi_head (a: la) (K: Z) (c: list val) (crep: Z * Z * Z) (j lb: Z) :
  xl_ctx a -> xl_pos a K j false c -> a_l a = LSplit lb -> xl_aft a K c crep j false ->
  let k := a_d a + K in let n1 := lit_lim a false - lit_li a false j in
  (a_E a - k < n1 -> xl_none a) /\
  (n1 <= a_E a - k ->
   xl_aft a (K + n1) (xl_put c k (sublist (lit_li a false j) (lit_lim a false) c)) crep (j + n1) true).
Proof.
  intros Hctx Hpos Hl Haft. cbv zeta.
  destruct Hctx as (Hoa & Hiw & Hla & _ & _ & _ & _ & _ & Hlxb).
  destruct Hpos as (HK & HE & Hj & Hsw & Hc).
  unfold a_E, a_d, a_cap, a_n, lit_lim, lit_li in *. rewrite Hl in HE, Hsw, Hla |- *.
  pose proof Hoa as (_ & HoN & _ & Hd0 & Hcap0 & HdN).
  destruct Hla as (_ & Hn0 & HnL & Hlb & Hlbe & _).
  destruct Hlxb as (HlxL & _).
  set (n1 := lb + (Zlength (a_lits a) - LITBUFFEREXTRASIZE) - (lb + j)).
  (* the model's state after the sequences, its split head n1 = lim - li, its room oend - op *)
  assert (Hcom: forall rb m body bo lr li lim sp ps ds de, xl_hyp a rb m body bo lr li lim sp ps ds de ->
    let e := xl_env a rb body ps ds de in
    exists s, xl_rel a e rb lr li lim sp c K j false s /\
      xl_X a rb m body lr li lim sp ps ds de =
        match x_last e s with Some (m', op') => Some (m', op', crep) | None => None end /\
      xsp s = true /\ xlr s = R_dst /\ xlim s - xli s = n1 /\
      xe_oend e - xop s = oa_d (a_o a) + oa_cap (a_o a) - (oa_d (a_o a) + K) /\
      rb + xli s = lb + j /\ 0 <= rb <= oa_d (a_o a)).
  { intros rb m body bo lr li lim sp ps ds de Hh e.
    destruct (Haft rb m body bo lr li lim sp ps ds de Hh) as (s & Hrel & HX).
    exists s. split; [exact Hrel|]. split; [exact HX|].
    pose proof Hrel as (Hop & Hlr & Hli & Hlim & Hsp & _).
    destruct Hh as (_ & Hrb & _ & _ & _ & _ & _ & Hll & _).
    unfold litloc_rel in Hll. rewrite Hl in Hll. destruct Hll as (-> & -> & -> & ->).
    unfold e, xl_env, seq_oend. cbn [xe_oend]. rewrite Hl.
    unfold a_d, a_cap, a_n in *. repeat split; try assumption; lia. }
  split.
  - intros Hcap rb m body bo lr li lim sp ps ds de Hh.
    destruct (Hcom rb m body bo lr li lim sp ps ds de Hh) as (s & _ & HX & Hsp & _ & Hn1 & Hoe & _).
    rewrite HX. unfold x_last. rewrite Hsp, Hn1, Hoe.
    replace (n1 >? oa_d (a_o a) + oa_cap (a_o a) - (oa_d (a_o a) + K)) with true by (unfold a_n in *; lia).
    reflexivity.
  - intros Hfit rb m body bo lr li lim sp ps ds de Hh.
    destruct (Hcom rb m body bo lr li lim sp ps ds de Hh) as (s & Hrel & HX & Hsp & Hlr' & Hn1 & Hoe & Hli' & Hrb).
    destruct Hrel as (Hop & _ & _ & _ & _ & Hlx & Hdr & Hxl). unfold a_d, a_n in *.
    rewrite Hlr' in Hxl. destruct Hxl as (Hl0 & Hxl).
    assert (Hnn: Z.of_nat (Z.to_nat n1) = n1) by (apply Z2Nat.id; unfold n1; lia).
    destruct (xm_move_def body (Z.to_nat n1) (xmm s) (xop s) R_dst (xli s)) as (m' & Hmv & Hle & Hw);
      [lia|lia| |].
    { rewrite Hnn. intros q Hq. apply Hxl. unfold WILDCOPY_OVERLENGTH. lia. }
    destruct (xm_move_l body (Z.to_nat n1) (xmm s) m' (xop s) R_dst (xli s) c (zbytes body)
      (zbytes (xm_lxb (xmm s))) rb 0 Hmv Hdr) as [Hlx' Hdr'].
    { unfold src_rel. rewrite Zlength_map, sublist_same by (rewrite ?Zlength_map; lia).
      repeat split; auto; lia. }
    { lia. }
    { rewrite Hnn. unfold WILDCOPY_OVERLENGTH in *; lia. }
    cbn [reg_l reg_o] in Hdr'.
    rewrite xp_lmove, Hnn in Hdr' by (rewrite ?Hnn; unfold WILDCOPY_OVERLENGTH in *; lia).
    replace (rb + xop s) with (oa_d (a_o a) + K) in Hdr' by lia.
    rewrite Hli' in Hdr'.
    replace (lb + j + n1) with (lb + (Zlength (a_lits a) - LITBUFFEREXTRASIZE)) in Hdr' by (unfold n1; lia).
    exists {| xmm := m'; xop := xop s + n1; xlr := R_lxb; xli := 0; xlim := XLITEXTRA; xsp := false |}.
    split.
    + unfold xl_rel, a_d, a_n. cbn [xop xlr xli xlim xsp xmm].
      split; [lia|]. split; [reflexivity|]. split; [unfold n1; lia|].
      split; [reflexivity|]. split; [reflexivity|]. split; [congruence|]. split; [exact Hdr'|].
      unfold xl_ok. split; [unfold XLITEXTRA; lia|]. rewrite Hlx', Hlx, HlxL.
      unfold XLITEXTRA, LITEXTRA_N, LITBUFFEREXTRASIZE. lia.
    + rewrite HX. unfold x_last at 1. rewrite Hsp, Hn1, Hoe.
      replace (n1 >? oa_d (a_o a) + oa_cap (a_o a) - (oa_d (a_o a) + K)) with false by (unfold a_n in *; lia).
      cbn [xl_env xe_src]. rewrite Hmv. reflexivity.
Qed.

(* the last literals not the split head (lastLLSize = litBufferEnd - litPtr: checked against oend, memmove to
   op = d + K of the literals left, at lit_li of their array xl_larr) *)
Lemma xl_epi_last (a: la) (K: Z) (c: list val) (crep: Z * Z * Z) (j: Z) (sw: bool) :
  xl_ctx a -> xl_pos a K j sw c -> match a_l a with LSplit _ => sw = true | _ => True end ->
  xl_aft a K c crep j sw ->
  let k := a_d a + K in let n := lit_lim a sw - lit_li a sw j in
  (a_E a - k < n -> xl_none a) /\
  (n <= a_E a - k ->
   forall rb m body bo lr li lim sp ps ds de, xl_hyp a rb m body bo lr li lim sp ps ds de ->
     match xl_X a rb m body lr li lim sp ps ds de with
     | None => False
     | Some (mm, op', rep2) =>
         K + n = op' - (oa_d (a_o a) - rb) /\
         dst_rel (xl_put c k (sublist (lit_li a sw j) (lit_lim a sw) (xl_larr a sw c))) rb (xm_dst mm) /\
         rep2 = crep
     end).
Proof.
  intros Hctx Hpos Hsw Haft. cbv zeta.
  destruct Hctx as (Hoa & Hiw & Hla & _ & _ & _ & _ & _ & Hlxb).
  destruct Hpos as (HK & HE & Hj & Hsw' & Hc).
  pose proof Hoa as (_ & HoN & _ & Hd0 & Hcap0 & HdN).
  pose proof Hiw as (_ & _ & _ & _ & HiN & _).
  destruct Hlxb as (HlxL & _).
  destruct Hla as (_ & Hn0 & Hla).
  set (n := lit_lim a sw - lit_li a sw j).
  (* the oend of the model is the C's, below the array's end *)
  assert (HEN: a_E a <= oa_d (a_o a) + oa_cap (a_o a)).
  { unfold a_E, a_d, a_cap. destruct (a_l a) eqn:El; rewrite ?El in *; try lia. destruct Hla as (_ & ? & _). unfold WILDCOPY_OVERLENGTH in *. lia. }
  (* the model's state after the sequences: not split, its literals left n = lim - li, its room oend - op *)
  assert (Hcom: forall rb m body bo lr li lim sp ps ds de, xl_hyp a rb m body bo lr li lim sp ps ds de ->
    exists s, xl_rel a (xl_env a rb body ps ds de) rb lr li lim sp c K j sw s /\
      xl_X a rb m body lr li lim sp ps ds de =
        match x_last (xl_env a rb body ps ds de) s with Some (m', op') => Some (m', op', crep) | None => None end /\
      xsp s = false /\ xlim s - xli s = n /\
      xe_oend (xl_env a rb body ps ds de) - xop s = a_E a - (a_d a + K) /\ 0 <= rb <= oa_d (a_o a)).
  { intros rb m body bo lr li lim sp ps ds de Hh.
    destruct (Haft rb m body bo lr li lim sp ps ds de Hh) as (s & Hrel & HX).
    exists s. split; [exact Hrel|]. split; [exact HX|].
    pose proof Hrel as (Hop & Hlr & Hli & Hlim & Hsp & _).
    destruct Hh as (_ & Hrb & _ & _ & _ & _ & _ & Hll & _).
    unfold n, lit_lim, lit_li, a_E, xl_env, seq_oend, litloc_rel in *. cbn [xe_oend].
    unfold a_d, a_n, a_cap in *.
    destruct (a_l a) eqn:El; rewrite ?El in *;
      destruct Hll as (-> & -> & -> & ->); try subst sw; rewrite Hsp, Hlim, Hli, Hop; cbv beta iota;
      repeat split; lia. }
  split.
  - intros Hcap rb m body bo lr li lim sp ps ds de Hh.
    destruct (Hcom rb m body bo lr li lim sp ps ds de Hh) as (s & _ & HX & Hsp & Hn & Hoe & _).
    rewrite HX. unfold x_last. rewrite Hsp. cbv beta iota. rewrite Hn, Hoe.
    replace (n >? a_E a - (a_d a + K)) with true by lia.
    reflexivity.
  - intros Hfit rb m body bo lr li lim sp ps ds de Hh.
    destruct (Hcom rb m body bo lr li lim sp ps ds de Hh) as (s & Hrel & HX & Hsp & Hn & Hoe & Hrb).
    rewrite HX. unfold x_last. rewrite Hsp. cbv beta iota. rewrite Hn, Hoe.
    replace (n >? a_E a - (a_d a + K)) with false by lia. cbv beta iota.
    destruct Hrel as (Hop & Hlr & Hli & Hlim & _ & Hlx & Hdr & Hxl).
    destruct Hxl as (Hl0 & Hxl).
    assert (Hn0': 0 <= n) by lia.
    assert (Hnn: Z.of_nat (Z.to_nat n) = n) by (apply Z2Nat.id; lia).
    pose proof Hh as (_ & _ & _ & _ & Hbo & Hbn & Hbs & Hll & _ & _ & Hli0 & _).
    unfold a_d in Hop.
    destruct (xm_fwd_def body (Z.to_nat n) (xmm s) (xop s) (xlr s) (xli s)) as (m' & Hf & _ & _); [lia|lia| |].
    { rewrite Hnn. destruct (xlr s).
      - intros q Hq. apply Hxl. revert Hq. destruct (xli s <? xop s); intros; unfold WILDCOPY_OVERLENGTH; lia.
      - unfold WILDCOPY_OVERLENGTH in *; lia.
      - cbn [xl_env xe_src] in Hxl. unfold WILDCOPY_OVERLENGTH in *; lia. }
    cbn [xl_env xe_src]. rewrite Hf. cbv beta iota. split; [lia|]. split; [|reflexivity].
    destruct (xm_fwd_l body (Z.to_nat n) (xmm s) m' (xop s) (xlr s) (xli s) c (iw_c (a_i a)) (zbytes (a_lxb a))
      rb bo Hf Hdr) as (_ & Hd).
    { rewrite Hlx. unfold src_rel. repeat split; auto; lia. }
    { lia. }
    { rewrite Hnn. unfold a_d in *. lia. }
    replace (rb + xop s) with (a_d a + K) in Hd by (unfold a_d; lia).
    unfold n, lit_lim, lit_li, xl_larr, a_E, litloc_rel in *. unfold a_n in *.
    destruct (a_l a) eqn:El; rewrite ?El in *;
      destruct Hll as (-> & -> & -> & ->); try subst sw; rewrite Hlr, Hli in Hd; cbn [reg_l reg_o] in Hd.
    (* in the input, in litExtraBuffer (LExtra, or split after the switch): memcpy from another array; in dst:
       the literals lie at or after oend, the copy is a move *)
    all: first [ rewrite xp_lfwd_LS in Hd by (rewrite ?Hnn, ?Zlength_map;
                   unfold a_d, a_cap, LITEXTRA_N, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *; lia)
               | rewrite xp_lfwd_LW in Hd by (rewrite ?Hnn; unfold a_d, a_cap, WILDCOPY_OVERLENGTH in *; lia) ];
      rewrite Hnn in Hd;
      match type of Hd with dst_rel (xl_put _ _ (sublist ?x ?y ?l)) _ _ =>
        match goal with |- dst_rel (xl_put _ _ (sublist ?x' ?y' ?l')) _ _ =>
          replace (sublist x y l) with (sublist x' y' l') in Hd by (f_equal; lia) end end;
      exact Hd.
Qed.

