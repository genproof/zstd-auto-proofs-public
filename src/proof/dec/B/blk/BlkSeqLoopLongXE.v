(* The long loop against the exact block model: the executor's steps (the queue head by ZSTD_execSequence, ZSTD_execSequenceSplitLitBuffer, or the switch of split literals to litExtraBuffer) (BlkSeqLoopLongX: the predicates). Plain Coq. *)
Require Export Zstd.proof.dec.B.blk.BlkSeqLoopLongX.
Require Import Zstd.proof.model.ExCSeq Zstd.proof.model.ExBlock.
Require Import Coq.micromega.Lia.
Local Open Scope Z_scope.

(* ===================== tools: the model's coordinates and the C's ===================== *)

(* the model's environment for one choice of the region: oend, prefixStart, virtualStart in array offsets;
   dictEnd is the extDict's end, or (no extDict: ext_len = 0, the C's dictEnd field is never read) the
   prefix start *)
Lemma xl_env_facts (a: la) (rb: Z) (m: list (option Z)) (body: list Z) (bo: Z) (lr: xreg) (li lim: Z)
    (sp: bool) (ps ds de: Z) :
  xl_hyp a rb m body bo lr li lim sp ps ds de ->
  let e := xl_env a rb body ps ds de in
  xe_oend e = a_E a - rb /\ xe_ps e = a_ps a - rb /\ xe_vs e = a_ps a - ext_len (a_x a) - rb /\
  (xe_de e = ext_end (a_x a) - rb \/ (ext_len (a_x a) = 0 /\ xe_de e = xe_ps e)).
Proof.
  intros (Hr & _). cbv zeta. unfold xl_env, a_E, a_ps, a_x, seq_oend; cbn [xe_oend xe_ps xe_vs xe_de].
  unfold hc_region in Hr.
  split; [destruct (a_l a); reflexivity|].
  destruct (hc_ext (a_h a)); inversion Hr; subst; cbn [ext_len ext_end].
  - split; [lia|]. split; [lia|]. right. split; lia.
  - split; [lia|]. split; [lia|]. left; lia.
Qed.

(* the C's error condition of ZSTD_execSequence is the model's, shifted by the region's base rb (and the
   literals by any t) *)
Lemma xexec_err_shift (e: xenv) (rb t op li lim ll ml off: Z) :
  xexec_err e op li lim ll ml off =
  exec_err (rb + op) (rb + xe_oend e) (t + li) (t + lim) ll ml off (rb + xe_ps e) (xe_ps e - xe_vs e).
Proof.
  unfold xexec_err, exec_err.
  match goal with |- ((?a <? _) || (?c <? _) || (?d <? _))%bool = ((?a' <? _) || (?c' <? _) || (?d' <? _))%bool =>
    replace a' with a by lia; replace c' with c by lia; replace d' with d by lia; reflexivity end.
Qed.

(* the same for ZSTD_execSequenceSplitLitBuffer (literals in dst) *)
Lemma xsplit_err_shift (e: xenv) (rb op li ll ml off: Z) :
  xsplit_err e op li ll ml off =
  exec_split_err (rb + op) (rb + xe_oend e) (rb + li) ll ml off (rb + xe_ps e) (xe_ps e - xe_vs e).
Proof.
  unfold xsplit_err, exec_split_err.
  assert (Hs: forall x y, (rb + x <? rb + y) = (x <? y))
    by (intros x y; destruct (Z.ltb_spec (rb + x) (rb + y)), (Z.ltb_spec x y); lia).
  replace (rb + li + ll) with (rb + (li + ll)) by lia.
  rewrite (Hs li op), (Hs op (li + ll)).
  replace (rb + xe_oend e - (rb + op)) with (xe_oend e - op) by lia.
  replace (rb + op + ll - (rb + xe_ps e) + (xe_ps e - xe_vs e)) with (op + ll - xe_vs e) by lia.
  reflexivity.
Qed.

(* lexec / lexec_split read dictEnd only for a match reaching into the extDict (offset beyond
   oLitEnd - prefixStart): otherwise its value does not matter *)
Lemma xl_lexec_de_irr (ps vs de1 de2 oend: Z) (c: list val) (op: Z) (s: lsrc) (li llim ll ml off: Z) :
  off <= op + ll - ps ->
  lexec ps vs de1 oend c op s li llim ll ml off = lexec ps vs de2 oend c op s li llim ll ml off.
Proof.
  intros H. unfold lexec, lmatch. cbv zeta.
  replace (off >? op + ll - ps) with false by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
  reflexivity.
Qed.

Lemma xl_lexec_split_de_irr (ps vs de1 de2 oend: Z) (c: list val) (op li llim ll ml off: Z) :
  off <= op + ll - ps ->
  lexec_split ps vs de1 oend c op li llim ll ml off = lexec_split ps vs de2 oend c op li llim ll ml off.
Proof.
  intros H. unfold lexec_split, lmatch. cbv zeta.
  replace (off >? op + ll - ps) with false by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
  reflexivity.
Qed.

(* the C's output end lies in the output array *)
Lemma xl_E_le (a: la) : xl_ctx a -> a_E a <= oa_N (a_o a).
Proof.
  intros ((_ & _ & _ & _ & _ & HN) & _ & Hla & _).
  unfold a_E, a_d, a_cap. unfold lits_at in Hla.
  destruct (a_l a); try lia. decompose record Hla. unfold WILDCOPY_OVERLENGTH in *. lia.
Qed.

(* the block's body and litExtraBuffer as the sources of the model's copies *)
Lemma xl_src_rel (a: la) (rb: Z) (m: list (option Z)) (body: list Z) (bo: Z) (lr: xreg) (li lim: Z)
    (sp: bool) (ps ds de: Z) (mm: xmem) :
  xl_ctx a -> xl_hyp a rb m body bo lr li lim sp ps ds de -> xm_lxb mm = a_lxb a ->
  src_rel (xe_src (xl_env a rb body ps ds de)) (xm_lxb mm) (iw_c (a_i a)) bo (zbytes (a_lxb a)).
Proof.
  intros (_ & Hi & _) (_ & _ & _ & _ & Hbo & Hbn & Hbs & _) Hlx.
  destruct Hi as (_ & _ & _ & _ & Hic & _).
  rewrite Hlx. unfold xl_env; cbn [xe_src]. unfold src_rel. repeat split; auto; lia.
Qed.

(* the literals of the C (source, index, limit) are the model's region, index and limit: the queue head
   by ZSTD_execSequence (literals not the split head) *)
Lemma xl_lit_coords (a: la) (e: xenv) (rb: Z) (m: list (option Z)) (body: list Z) (bo: Z) (lr: xreg)
    (li lim: Z) (sp: bool) (ps ds de: Z) (c: list val) (K j: Z) (sw: bool) (s: xex) :
  xl_hyp a rb m body bo lr li lim sp ps ds de -> xl_pos a K j sw c ->
  match a_l a with LSplit _ => sw = true | _ => True end ->
  xl_rel a e rb lr li lim sp c K j sw s ->
  xsp s = false /\ reg_l (xlr s) (iw_c (a_i a)) (zbytes (a_lxb a)) = xl_lsrc a sw /\
  reg_o (xlr s) rb bo + xli s = lit_li a sw j /\ reg_o (xlr s) rb bo + xlim s = lit_lim a sw.
Proof.
  intros (_ & _ & _ & _ & _ & _ & _ & Hl & _) (_ & _ & _ & Hsw & _) Hsp (_ & Hlr & Hli & Hlim & Hs & _).
  rewrite Hlr, Hli, Hlim, Hs. unfold xl_lsrc, lit_li, lit_lim, a_n.
  destruct (a_l a); cbn in Hl, Hsw, Hsp; destruct Hl as (Hl1 & Hl2 & Hl3 & Hl4);
    rewrite ?Hsw, ?Hsp, ?Hl1, ?Hl3, ?Hl4; cbn; unfold LITBUFFEREXTRASIZE; repeat split; lia.
Qed.

(* the written cells and the literals' readability after a step that extends the region *)
Lemma xl_ok_after (e: xenv) (m m': xmem) (lr: xreg) (li lim ll: Z) :
  xl_ok e m lr li lim -> xm_le m m' -> 0 <= ll -> li + ll <= lim -> xl_ok e m' lr (li + ll) lim.
Proof.
  intros (H1 & H2) (Hle & Hlx) Hll Hlim. split; [lia|].
  destruct lr; try (rewrite Hlx); try exact H2.
  intros k Hk. apply Hle, H2. lia.
Qed.

Lemma xh_ok_after (e: xenv) (m m': xmem) (op op': Z) :
  xh_ok e m op -> xm_le m m' -> op <= op' -> xwr_rng m' op op' -> xh_ok e m' op'.
Proof.
  intros (H1 & H2 & H3 & H4 & H5) (Hle & _) Hop Hw.
  split; [lia|]. split; [lia|]. split; [lia|]. split.
  - intros k Hk. destruct (Z.lt_ge_cases k op).
    + apply Hle, H4. lia.
    + apply Hw. lia.
  - intros k Hk. apply Hle, H5. lia.
Qed.

Lemma xm_le_refl (m: xmem) : xm_le m m.
Proof. split; auto. Qed.

Lemma xm_le_trans (m1 m2 m3: xmem) : xm_le m1 m2 -> xm_le m2 m3 -> xm_le m1 m3.
Proof. intros (A1 & B1) (A2 & B2). split; [auto | congruence]. Qed.

(* the queue's head executed first *)
Lemma xl_cont_cons (a: la) (e: xenv) (t: seq_tabs) (ll ml off: Z) (q: list (Z * Z * Z)) (k: nat)
    (st: Z * Z * Z) (pos: Z) (crep: Z * Z * Z) (s: xex) :
  xl_cont a e t ((ll, ml, off) :: q) k st pos crep s =
  match x_step e s ll ml off with None => None | Some s' => xl_cont a e t q k st pos crep s' end.
Proof.
  unfold xl_cont. destruct t as [[tLL tOF] tML]. cbn [x_steps].
  destruct (x_step e s ll ml off); reflexivity.
Qed.

(* one step of the executor: when, for every choice of the region, the model's step from a related state
   fails exactly when the C errs (b) and otherwise relates the C's next state, the invariant moves to the
   rest of the queue (or the model fails on every choice) *)
Lemma xl_inv_step (a: la) (t: seq_tabs) (id K K': Z) (c c': list val) (crep: Z * Z * Z) (j j': Z)
    (sw sw': bool) (pos lo: Z) (st: Z * Z * Z) (q: list (Z * Z * Z)) (ll ml off: Z) (b: bool) :
  (forall rb m body bo lr li lim sp ps ds de, xl_hyp a rb m body bo lr li lim sp ps ds de ->
     forall s, xl_rel a (xl_env a rb body ps ds de) rb lr li lim sp c K j sw s ->
       xh_ok (xl_env a rb body ps ds de) (xmm s) (xop s) ->
       match x_step (xl_env a rb body ps ds de) s ll ml off with
       | None => b = true
       | Some s' => b = false /\ xl_rel a (xl_env a rb body ps ds de) rb lr li lim sp c' K' j' sw' s' /\
           xh_ok (xl_env a rb body ps ds de) (xmm s') (xop s')
       end) ->
  xl_inv a t id K c crep j sw pos lo st ((ll, ml, off) :: q) ->
  (b = true -> xl_none a) /\ (b = false -> xl_inv a t id K' c' crep j' sw' pos lo st q).
Proof.
  intros Hstep Hinv. split.
  - intros Hb rb m body bo lr li lim sp ps ds de Hh.
    destruct (Hinv rb m body bo lr li lim sp ps ds de Hh) as [(s & Hrel & Hhk & _ & _ & HX)|(_ & HX)];
      [|exact HX].
    rewrite HX, xl_cont_cons. specialize (Hstep rb m body bo lr li lim sp ps ds de Hh s Hrel Hhk).
    destruct (x_step _ _ _ _ _) as [s'|]; [destruct Hstep; congruence | reflexivity].
  - intros Hb rb m body bo lr li lim sp ps ds de Hh. cbv zeta.
    destruct (Hinv rb m body bo lr li lim sp ps ds de Hh) as [(s & Hrel & Hhk & Hb1 & Hb2 & HX)|(Hp & HX)];
      [|right; auto].
    specialize (Hstep rb m body bo lr li lim sp ps ds de Hh s Hrel Hhk).
    rewrite HX, xl_cont_cons. destruct (x_step _ _ _ _ _) as [s'|]; [|congruence].
    destruct Hstep as (_ & Hrel' & Hhk').
    left. exists s'. auto.
Qed.

(* with a region, the extDict is not separate *)
Lemma xl_noext (a: la) (rb ps ds de: Z) (P Q: Prop) :
  hc_region (a_h a) rb = Some (ps, ds, de) ->
  match a_x a with ExtSep _ _ _ _ _ _ => P | _ => Q end -> Q.
Proof. unfold hc_region, a_x. destruct (hc_ext (a_h a)); intros Hr H; try discriminate; exact H. Qed.

(* the stores of ZSTD_safecopyDstBeforeSrc keep the array's length *)
Lemma lfwd_Zlength (k: nat) (c: list val) (d: Z) (s: lsrc) (i: Z) : Zlength (lfwd k c d s i) = Zlength c.
Proof.
  revert c d i. induction k as [|k IH]; intros c d i; cbn [lfwd]; [reflexivity|].
  rewrite IH. apply Zlength_upd_Znth.
Qed.

Lemma lwrn_Zlength (vs c: list val) (d: Z) : Zlength (lwrn vs c d) = Zlength c.
Proof.
  revert c d. induction vs as [|v vs IH]; intros c d; cbn [lwrn]; [reflexivity|].
  rewrite IH. apply Zlength_upd_Znth.
Qed.

Lemma lchunks16_Zlength (k: nat) (c: list val) (d: Z) (s: lsrc) (i: Z) :
  Zlength (lchunks16 k c d s i) = Zlength c.
Proof.
  revert c d i. induction k as [|k IH]; intros c d i; cbn [lchunks16]; [reflexivity|].
  rewrite IH. unfold lmove. apply lwrn_Zlength.
Qed.

Lemma lsdbs_Zlength (c: list val) (op ip len: Z) : Zlength (lsdbs c op ip len) = Zlength c.
Proof.
  unfold lsdbs. cbv zeta.
  destruct ((len <? 8) || (op - ip >? -8))%bool; [apply lfwd_Zlength|].
  destruct ((len >=? 32) && (op - ip <? -16))%bool; rewrite lfwd_Zlength; [|reflexivity].
  unfold lwild. destruct (_ && _)%bool; [apply lfwd_Zlength | apply lchunks16_Zlength].
Qed.

(* the queue head (ll, ml, off) by ZSTD_execSequence (BlkSeqEXEC's exec_spec: its error iff exec_err, its
   stores lexec), literals not the split head (not LSplit, or switched), op = d + K *)
Lemma xl_exec_N (a: la) (t: seq_tabs) (id K: Z) (c c': list val) (crep: Z * Z * Z) (j: Z) (sw: bool)
    (pos lo: Z) (st: Z * Z * Z) (q: list (Z * Z * Z)) (ll ml off r: Z) :
  xl_ctx a -> xl_pos a K j sw c -> match a_l a with LSplit _ => sw = true | _ => True end ->
  0 <= ll -> 1 <= ml -> 1 <= off ->
  xl_inv a t id K c crep j sw pos lo st ((ll, ml, off) :: q) ->
  is_error_code r = exec_err (a_d a + K) (a_E a) (lit_li a sw j) (lit_lim a sw) ll ml off (a_ps a)
                      (ext_len (a_x a)) ->
  match a_x a with
  | ExtSep _ _ _ _ _ _ => True
  | _ => is_error_code r = false ->
         c' = lexec (a_ps a) (a_ps a - ext_len (a_x a)) (ext_end (a_x a)) (a_E a) c (a_d a + K) (xl_lsrc a sw)
                (lit_li a sw j) (lit_lim a sw) ll ml off
  end ->
  (is_error_code r = true -> xl_none a) /\
  (is_error_code r = false -> xl_inv a t id (K + (ll + ml)) c' crep (j + ll) sw pos lo st q).
Proof.
  intros Hctx Hpos Hsw Hll Hml Hoff Hinv Herr Hc'.
  apply (xl_inv_step a t id K (K + (ll + ml)) c c' crep j (j + ll) sw sw pos lo st q ll ml off
           (is_error_code r)); [|exact Hinv].
  intros rb m body bo lr li lim sp ps ds de Hh s Hrel Hhk.
  destruct (xl_lit_coords a (xl_env a rb body ps ds de) rb m body bo lr li lim sp ps ds de c K j sw s
              Hh Hpos Hsw Hrel) as (Hsp & HL & HLi & HLim).
  destruct (xl_env_facts a rb m body bo lr li lim sp ps ds de Hh) as (Hoe & Hps & Hvs & Hde).
  set (e := xl_env a rb body ps ds de) in *.
  pose proof Hrel as (Hop & Hlr & Hli & Hlim & Hsp' & Hlx & Hd & Hl).
  assert (Hrb: 0 <= rb) by (destruct Hh as (_ & ? & _); lia).
  assert (HE := xl_E_le a Hctx).
  assert (Herr': is_error_code r = xexec_err e (xop s) (xli s) (xlim s) ll ml off).
  { rewrite Herr, (xexec_err_shift e rb (reg_o (xlr s) rb bo)), HLi, HLim. f_equal; lia. }
  unfold x_step. rewrite Hsp.
  pose proof (x_exec_def e (xmm s) (xop s) (xlr s) (xli s) (xlim s) ll ml off Hhk Hl Hll Hml Hoff) as D.
  destruct (x_exec _ _ _ _ _ _ _ _ _) as [[[m' op'] li']|] eqn:Ex; [|congruence].
  destruct D as (He & Hop' & Hli' & Hle & Hw).
  assert (Hr: is_error_code r = false) by congruence.
  split; [exact Hr|].
  assert (Hc2: c' = lexec (a_ps a) (a_ps a - ext_len (a_x a)) (ext_end (a_x a)) (a_E a) c (a_d a + K)
                      (xl_lsrc a sw) (lit_li a sw j) (lit_lim a sw) ll ml off).
  { destruct Hh as (Hreg & _). unfold hc_region in Hreg. unfold a_x in Hc' |- *.
    destruct (hc_ext (a_h a)); try discriminate; exact (Hc' Hr). }
  pose proof He as He'. unfold xexec_err in He'.
  apply orb_false_iff in He' as [He' He3]. apply orb_false_iff in He' as [He1 He2].
  apply Z.ltb_ge in He1, He2, He3.
  destruct (x_exec_l e (xmm s) m' (xop s) (xlr s) (xli s) (xlim s) ll ml off op' li' c (iw_c (a_i a))
              (zbytes (a_lxb a)) rb bo Ex Hd (xl_src_rel a rb m body bo lr li lim sp ps ds de (xmm s) Hctx Hh Hlx)
              Hll ltac:(lia) Hrb ltac:(destruct Hpos as (_ & _ & _ & _ & Hc); lia)) as [_ HD].
  rewrite HL, HLi, HLim in HD.
  pose proof Hle as (Hle1 & Hlxm).
  split.
  - unfold xl_rel; cbn [xmm xop xlr xli xlim xsp].
    split; [lia|]. split; [exact Hlr|]. split; [destruct sw; lia|]. split; [exact Hlim|].
    split; [congruence|]. split; [congruence|].
    split.
    + rewrite Hc2.
      replace (lexec (a_ps a) (a_ps a - ext_len (a_x a)) (ext_end (a_x a)) (a_E a) c (a_d a + K)
                 (xl_lsrc a sw) (lit_li a sw j) (lit_lim a sw) ll ml off)
        with (lexec (rb + xe_ps e) (rb + xe_vs e) (rb + xe_de e) (rb + xe_oend e) c (rb + xop s)
                 (xl_lsrc a sw) (lit_li a sw j) (lit_lim a sw) ll ml off); [exact HD|].
      destruct Hde as [Hde|(Hl0 & Hde)].
      * f_equal; lia.
      * rewrite (xl_lexec_de_irr _ _ (rb + xe_de e) (ext_end (a_x a))) by lia. f_equal; lia.
    + rewrite Hli'. apply (xl_ok_after e (xmm s) m'); [exact Hl | exact Hle | lia | lia].
  - cbn [xmm xop]. apply (xh_ok_after e (xmm s) m' (xop s) op'); [exact Hhk | exact Hle | lia | exact Hw].
Qed.

(* the queue head by ZSTD_execSequenceSplitLitBuffer: the split head holds its literals *)
Lemma xl_exec_S (a: la) (t: seq_tabs) (id K: Z) (c c': list val) (crep: Z * Z * Z) (j: Z) (lb: Z)
    (pos lo: Z) (st: Z * Z * Z) (q: list (Z * Z * Z)) (ll ml off r: Z) :
  xl_ctx a -> xl_pos a K j false c -> a_l a = LSplit lb -> lit_li a false j + ll <= lit_lim a false ->
  0 <= ll -> 1 <= ml -> 1 <= off ->
  xl_inv a t id K c crep j false pos lo st ((ll, ml, off) :: q) ->
  is_error_code r = exec_split_err (a_d a + K) (a_E a) (lit_li a false j) ll ml off (a_ps a) (ext_len (a_x a)) ->
  match a_x a with
  | ExtSep _ _ _ _ _ _ => True
  | _ => is_error_code r = false ->
         c' = lexec_split (a_ps a) (a_ps a - ext_len (a_x a)) (ext_end (a_x a)) (a_E a) c (a_d a + K)
                (lit_li a false j) (lit_lim a false) ll ml off
  end ->
  (is_error_code r = true -> xl_none a) /\
  (is_error_code r = false -> xl_inv a t id (K + (ll + ml)) c' crep (j + ll) false pos lo st q).
Proof.
  intros Hctx Hpos El Hfit Hll Hml Hoff Hinv Herr Hc'.
  apply (xl_inv_step a t id K (K + (ll + ml)) c c' crep j (j + ll) false false pos lo st q ll ml off
           (is_error_code r)); [|exact Hinv].
  intros rb m body bo lr li lim sp ps ds de Hh s Hrel Hhk.
  destruct (xl_env_facts a rb m body bo lr li lim sp ps ds de Hh) as (Hoe & Hps & Hvs & Hde).
  set (e := xl_env a rb body ps ds de) in *.
  pose proof Hh as (_ & Hrb & _ & _ & _ & _ & _ & Hlr0 & _).
  rewrite El in Hlr0; cbn in Hlr0. destruct Hlr0 as (Hlr0 & Hlb & Hlim0 & Hsp0).
  pose proof Hctx as (_ & _ & Hla & _). unfold lits_at in Hla. rewrite El in Hla.
  destruct Hla as (_ & _ & Hn & Hd0 & Hcap & _).
  pose proof Hrel as (Hop & Hlr & Hli & Hlim & Hsp' & Hlx & Hd & Hl). cbn in Hlr, Hli, Hlim, Hsp'.
  rewrite Hlr, Hlr0 in Hl.
  assert (HE := xl_E_le a Hctx).
  unfold lit_li, lit_lim, a_E in *. rewrite El in *. unfold a_n, a_d, a_cap in *.
  assert (Hoend: xlim s + WILDCOPY_OVERLENGTH <= xe_oend e) by lia.
  assert (Herr': is_error_code r = xsplit_err e (xop s) (xli s) ll ml off).
  { rewrite Herr, (xsplit_err_shift e rb). f_equal; lia. }
  unfold x_step. rewrite Hsp', Hsp0.
  replace (xlim s - xli s <? ll) with false by (symmetry; apply Z.ltb_ge; lia).
  pose proof (x_exec_split_def e (xmm s) (xop s) (xli s) (xlim s) ll ml off Hhk Hl ltac:(lia) Hoend
                Hll Hml Hoff) as D.
  destruct (x_exec_split _ _ _ _ _ _ _ _) as [[[m' op'] li']|] eqn:Ex; [|congruence].
  destruct D as (He & Hop' & Hli' & Hle & Hw).
  assert (Hr: is_error_code r = false) by congruence.
  split; [exact Hr|].
  assert (Hc2: c' = lexec_split (a_ps a) (a_ps a - ext_len (a_x a)) (ext_end (a_x a)) (oa_d (a_o a) + oa_cap (a_o a))
                      c (oa_d (a_o a) + K) (lb + j) (lb + (Zlength (a_lits a) - LITBUFFEREXTRASIZE)) ll ml off).
  { destruct Hh as (Hreg & _). unfold hc_region in Hreg. unfold a_x in Hc' |- *.
    destruct (hc_ext (a_h a)); try discriminate; exact (Hc' Hr). }
  pose proof He as He'. unfold xsplit_err in He'.
  apply orb_false_iff in He' as [He' He3]. apply orb_false_iff in He' as [He1 He2].
  apply Z.ltb_ge in He1, He3.
  destruct (x_exec_split_l e (xmm s) m' (xop s) (xli s) (xlim s) ll ml off op' li' c rb Ex Hd Hll ltac:(lia)
              ltac:(lia) ltac:(destruct Hpos as (_ & _ & _ & _ & Hc); lia) Hoend) as [_ HD].
  pose proof Hle as (Hle1 & Hlxm).
  split.
  - unfold xl_rel, a_d; cbn [xmm xop xlr xli xlim xsp].
    split; [lia|]. split; [congruence|]. split; [lia|]. split; [exact Hlim|].
    split; [congruence|]. split; [congruence|].
    split.
    + rewrite Hc2.
      replace (lexec_split (a_ps a) (a_ps a - ext_len (a_x a)) (ext_end (a_x a)) (oa_d (a_o a) + oa_cap (a_o a))
                 c (oa_d (a_o a) + K) (lb + j) (lb + (Zlength (a_lits a) - LITBUFFEREXTRASIZE)) ll ml off)
        with (lexec_split (rb + xe_ps e) (rb + xe_vs e) (rb + xe_de e) (rb + xe_oend e) c (rb + xop s)
                 (rb + xli s) (rb + xlim s) ll ml off); [exact HD|].
      destruct Hde as [Hde|(Hl0 & Hde)].
      * f_equal; lia.
      * rewrite (xl_lexec_split_de_irr _ _ (rb + xe_de e) (ext_end (a_x a))) by lia. f_equal; lia.
    + rewrite Hli'. apply (xl_ok_after e (xmm s) m'); [exact Hl | exact Hle | lia | lia].
  - cbn [xmm xop]. apply (xh_ok_after e (xmm s) m' (xop s) op'); [exact Hhk | exact Hle | lia | exact Hw].
Qed.

(* the queue head when the split head ends before its literals: the leftover lo0 (checked against oend, copied
   by ZSTD_safecopyDstBeforeSrc: BlkSeqCOPY's lsdbs), the switch to litExtraBuffer, ZSTD_execSequence with the
   rest of the literals *)
Lemma xl_exec_X1 (a: la) (t: seq_tabs) (id K: Z) (c: list val) (crep: Z * Z * Z) (j: Z) (lb: Z)
    (pos lo: Z) (st: Z * Z * Z) (q: list (Z * Z * Z)) (ll ml off: Z) :
  xl_ctx a -> xl_pos a K j false c -> a_l a = LSplit lb -> lit_lim a false - lit_li a false j < ll ->
  0 <= ll -> 1 <= ml -> 1 <= off ->
  xl_inv a t id K c crep j false pos lo st ((ll, ml, off) :: q) ->
  let k := a_d a + K in let lo0 := lit_lim a false - lit_li a false j in
  (0 < lo0 -> a_E a - k < lo0 -> xl_none a) /\
  forall c1, (lo0 = 0 -> c1 = c) ->
  (0 < lo0 -> lo0 <= a_E a - k /\ c1 = lsdbs c k (lit_li a false j) lo0) ->
  let k1 := k + lo0 in let li1 := lit_li a true (j + lo0) in let lim1 := lit_lim a true in
  forall r c',
  is_error_code r = exec_err k1 (a_E a) li1 lim1 (ll - lo0) ml off (a_ps a) (ext_len (a_x a)) ->
  match a_x a with
  | ExtSep _ _ _ _ _ _ => True
  | _ => is_error_code r = false ->
         c' = lexec (a_ps a) (a_ps a - ext_len (a_x a)) (ext_end (a_x a)) (a_E a) c1 k1 (xl_lsrc a true)
                li1 lim1 (ll - lo0) ml off
  end ->
  (is_error_code r = true -> xl_none a) /\
  (is_error_code r = false -> xl_inv a t id (K + (ll + ml)) c' crep (j + ll) true pos lo st q).
Proof.
  cbv zeta.
  intros Hctx Hpos El Hgt Hll Hml Hoff Hinv.
  assert (HE := xl_E_le a Hctx).
  destruct Hpos as (HK & HKE & Hj & Hjs & Hlc). rewrite El in Hjs.
  pose proof Hctx as (_ & _ & Hla & _ & _ & _ & _ & _ & Hlxb).
  unfold lits_at in Hla. rewrite El in Hla. destruct Hla as (_ & _ & Hn & Hd0 & Hcap & _).
  destruct Hlxb as (Hlxn & _).
  unfold lit_li, lit_lim, xl_lsrc, a_E, a_n, a_d, a_cap in *. rewrite El in *. cbv beta iota in *.
  remember (lb + (Zlength (a_lits a) - LITBUFFEREXTRASIZE) - (lb + j)) as lo0 eqn:Hlo0.
  split.
  { (* the leftover does not fit before oend: the model fails *)
    intros Hp HEk.
    refine (proj1 (xl_inv_step a t id K K c c crep j j false false pos lo st q ll ml off true _ Hinv) eq_refl).
    intros rb m body bo lr li lim sp ps ds de Hh s Hrel Hhk.
    destruct (xl_env_facts a rb m body bo lr li lim sp ps ds de Hh) as (Hoe & Hps & Hvs & Hde).
    set (e := xl_env a rb body ps ds de) in *.
    pose proof Hh as (Hreg & Hrb & _ & _ & _ & _ & _ & Hlr0 & _).
    rewrite El in Hlr0; cbn in Hlr0. destruct Hlr0 as (Hlr0 & Hlb & Hlim0 & Hsp0).
    pose proof Hrel as (Hop & Hlr & Hli & Hlim & Hsp' & Hlx & Hd & Hl). cbn in Hlr, Hli, Hlim, Hsp'.
    unfold a_E, a_d, a_cap in Hoe, Hop. rewrite El in Hoe.
    unfold x_step; cbv zeta. rewrite Hsp', Hsp0.
    replace (xlim s - xli s) with lo0 by lia.
    replace (lo0 <? ll) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (lo0 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (lo0 >? xe_oend e - xop s) with true by (symmetry; apply Z.gtb_lt; lia).
    reflexivity. }
  intros c1 Hc10 Hc1p r c' Herr Hc'.
  assert (Hlc1: Zlength c1 = Zlength c).
  { destruct (Z.eq_dec lo0 0) as [H0|H0]; [rewrite (Hc10 H0); reflexivity|].
    destruct (Hc1p ltac:(lia)) as (_ & ->). apply lsdbs_Zlength. }
  apply (xl_inv_step a t id K (K + (ll + ml)) c c' crep j (j + ll) false true pos lo st q ll ml off
           (is_error_code r)); [|exact Hinv].
  intros rb m body bo lr li lim sp ps ds de Hh s Hrel Hhk.
  destruct (xl_env_facts a rb m body bo lr li lim sp ps ds de Hh) as (Hoe & Hps & Hvs & Hde).
  set (e := xl_env a rb body ps ds de) in *.
  pose proof Hh as (Hreg & Hrb & _ & _ & _ & _ & _ & Hlr0 & _).
  rewrite El in Hlr0; cbn in Hlr0. destruct Hlr0 as (Hlr0 & Hlb & Hlim0 & Hsp0).
  pose proof Hrel as (Hop & Hlr & Hli & Hlim & Hsp' & Hlx & Hd & Hl). cbn in Hlr, Hli, Hlim, Hsp'.
  rewrite Hlr, Hlr0 in Hl.
  unfold a_E, a_d, a_cap in Hoe, Hop. rewrite El in Hoe.
  pose proof Hhk as (Hhk1 & _).
  unfold x_step; cbv zeta. rewrite Hsp', Hsp0.
  replace (xlim s - xli s) with lo0 by lia.
  replace (lo0 <? ll) with true by (symmetry; apply Z.ltb_lt; lia).
  (* the leftover copied by ZSTD_safecopyDstBeforeSrc *)
  assert (Hmo: exists m1,
    (if lo0 =? 0 then Some (xmm s, xop s) else
     if lo0 >? xe_oend e - xop s then None else
     match xm_sdbs (xe_src e) (xmm s) (xop s) (xli s) lo0 with
     | Some m => Some (m, xop s + lo0)
     | None => None
     end) = Some (m1, xop s + lo0) /\
    xm_le (xmm s) m1 /\ xwr_rng m1 (xop s) (xop s + lo0) /\ dst_rel c1 rb (xm_dst m1)).
  { destruct (Z.eq_dec lo0 0) as [H0|H0].
    - exists (xmm s). replace (lo0 =? 0) with true by (symmetry; apply Z.eqb_eq; exact H0).
      rewrite (Hc10 H0), H0, Z.add_0_r.
      split; [reflexivity|]. split; [apply xm_le_refl|]. split; [intros x Hx; lia|]. exact Hd.
    - destruct (Hc1p ltac:(lia)) as (Hle0 & Hc1).
      replace (lo0 =? 0) with false by (symmetry; apply Z.eqb_neq; exact H0).
      replace (lo0 >? xe_oend e - xop s) with false
        by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
      destruct (xm_sdbs_def (xe_src e) (xmm s) (xop s) (xli s) lo0) as (m1 & Hs1 & Hle1 & Hw1).
      1-3: destruct Hl; lia.
      { destruct Hl as (_ & Hlw). intros x Hx. apply Hlw. unfold WILDCOPY_OVERLENGTH; lia. }
      rewrite Hs1. exists m1. split; [reflexivity|]. split; [exact Hle1|]. split; [exact Hw1|].
      rewrite Hc1.
      destruct (xm_sdbs_l (xe_src e) (xmm s) m1 (xop s) (xli s) lo0 c rb Hs1 Hd ltac:(lia) ltac:(lia))
        as [_ HD0].
      replace (oa_d (a_o a) + K) with (rb + xop s) by lia.
      replace (lb + j) with (rb + xli s) by lia. exact HD0. }
  destruct Hmo as (m1 & Hmo & Hle1 & Hw1 & Hd1). rewrite Hmo.
  assert (Hhk2: xh_ok e m1 (xop s + lo0)) by (apply (xh_ok_after e (xmm s) m1 (xop s)); auto; lia).
  assert (Hlx1: xm_lxb m1 = a_lxb a) by (destruct Hle1; congruence).
  assert (Hl1: xl_ok e m1 R_lxb 0 XLITEXTRA).
  { unfold xl_ok. split; [unfold XLITEXTRA; lia|].
    rewrite Hlx1, Hlxn. unfold XLITEXTRA, LITEXTRA_N, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH; lia. }
  pose proof (x_exec_def e m1 (xop s + lo0) R_lxb 0 XLITEXTRA (ll - lo0) ml off Hhk2 Hl1 ltac:(lia) Hml Hoff)
    as D.
  assert (Herr': is_error_code r = xexec_err e (xop s + lo0) 0 XLITEXTRA (ll - lo0) ml off).
  { rewrite Herr, (xexec_err_shift e rb 0). unfold XLITEXTRA, LITBUFFEREXTRASIZE in *. f_equal; lia. }
  destruct (x_exec _ _ _ _ _ _ _ _ _) as [[[m' op'] li']|] eqn:Ex; [|congruence].
  destruct D as (He & Hop' & Hli' & Hle & Hw).
  assert (Hr: is_error_code r = false) by congruence.
  split; [exact Hr|].
  pose proof (xl_noext a rb ps ds de _ _ Hreg Hc' Hr) as Hc2.
  pose proof He as He'. unfold xexec_err in He'.
  apply orb_false_iff in He' as [He' He3]. apply orb_false_iff in He' as [He1 He2].
  apply Z.ltb_ge in He1, He2, He3.
  destruct (x_exec_l e m1 m' (xop s + lo0) R_lxb 0 XLITEXTRA (ll - lo0) ml off op' li' c1 (iw_c (a_i a))
              (zbytes (a_lxb a)) rb bo Ex Hd1 (xl_src_rel a rb m body bo lr li lim sp ps ds de m1 Hctx Hh Hlx1)
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [_ HD].
  cbn [reg_l reg_o] in HD.
  pose proof Hle as (Hle2 & Hlxm).
  split.
  - unfold xl_rel, a_d, a_n; cbn [xmm xop xlr xli xlim xsp].
    split; [lia|]. split; [reflexivity|]. split; [lia|]. split; [reflexivity|].
    split; [reflexivity|]. split; [congruence|].
    split.
    + rewrite Hc2.
      match goal with |- dst_rel ?X _ _ => match type of HD with dst_rel ?Y _ _ =>
        replace X with Y; [exact HD|] end end.
      destruct Hde as [Hde|(Hl0 & Hde)].
      * unfold XLITEXTRA, LITBUFFEREXTRASIZE in *. f_equal; lia.
      * rewrite (xl_lexec_de_irr _ _ (rb + xe_de e) (ext_end (a_x a))) by lia.
        unfold XLITEXTRA, LITBUFFEREXTRASIZE in *. f_equal; lia.
    + rewrite Hli'. apply (xl_ok_after e m1 m' R_lxb 0 XLITEXTRA (ll - lo0)); [exact Hl1 | exact Hle | lia | lia].
  - cbn [xmm xop]. apply (xh_ok_after e m1 m' (xop s + lo0) op'); [exact Hhk2 | exact Hle | lia | exact Hw].
Qed.

