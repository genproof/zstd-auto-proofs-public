(* LOOP / long loop: the sequence tables with their pointers fixed (tabs_seq_tp). *)
Require Import Zstd.proof.dec.B.blk.BlkSeqLoopLongDefs.
Local Open Scope logic.

(* the pool of the borrow (as seqtabs_borrow in BlkSeqLoopCommon): a DDict's sequence table of kind
   k, a predefined table of kind k *)
Definition lt_ddslot (ox: option ddx) (k: seqkind) : mpred :=
  match ox_seq k ox with
  | Some t => seqspace_at Ews k (Some t) (dd_seq k (ox_q ox))
  | None => emp
  end.
Definition lt_gslot (gv: globals) (k: seqkind) : mpred :=
  seqtab_at_fm Ers k (sk_predef k) predef_fm (gv (sk_gdefault k)).

Lemma lt_dent_split (gv: globals) (ox: option ddx) :
  exists Rd: mpred, dent_of dent_def gv ox = lt_ddslot ox KLL * lt_ddslot ox KOF * lt_ddslot ox KML * Rd.
Proof.
  unfold lt_ddslot, ox_seq.
  destruct ox as [x|].
  2: { exists emp. simpl. rewrite !emp_sepcon. reflexivity. }
  simpl dent_of. simpl ox_ent. simpl ox_q.
  destruct (ddx_ent x) as [st|].
  2: { exists (dent_def gv (dx_q x) None). rewrite !emp_sepcon. reflexivity. }
  unfold dent_def.
  destruct (st_seq st) as [[[a b] c]|] eqn:Hs.
  2: { simpl seq_of. exists (match st_huf st with Some _ => FF | None => FF end).
       rewrite !emp_sepcon. destruct (st_huf st); reflexivity. }
  simpl seq_of.
  destruct (st_huf st) as [ht|].
  - match goal with |- exists Rd, (andp ?P (?H * _ * _ * _ * ?Rp * ?W)) = _ =>
      exists (andp P (H * Rp * W)) end.
    apply pred_ext; entailer!.
  - exists FF. rewrite sepcon_FF. reflexivity.
Qed.

Lemma lt_one (gv: globals) (p: val) (ox: option ddx) (k: seqkind) (t: fse_table) (tp: val) :
  seq_where_tp gv p ox k t tp * lt_ddslot ox k * lt_gslot gv k |--
  EX sh: share, EX fm: Z, EX Rk: mpred,
    !! (readable_share sh /\
        (seq_ptr_at p k tp * seqtab_at_fm sh k t fm tp * Rk
         |-- seq_where_tp gv p ox k t tp * lt_ddslot ox k * lt_gslot gv k)) &&
    (seq_ptr_at p k tp * seqtab_at_fm sh k t fm tp * Rk).
Proof.
  unfold seq_where_tp. Intros w. destruct w.
  - Intros. subst tp. unfold seqspace_at at 1, seqtab_at. Intros fm.
    Exists Ews fm
      (data_at_ Ews (tarray t_seqSymbol (sk_size k - 1 - 2 ^ ft_log t))
         (offset_val (8 * (1 + 2 ^ ft_log t)) (ctx_seq k p)) * lt_ddslot ox k * lt_gslot gv k).
    apply andp_right; [apply prop_right | cancel].
    split; [auto with share |].
    Exists TCtx. unfold seqspace_at, seqtab_at. Exists fm. entailer!.
  - Intros. rename H into Ho. subst tp. unfold lt_ddslot at 1. rewrite Ho.
    unfold seqspace_at at 2, seqtab_at. Intros fm.
    Exists Ews fm
      (seqspace_at Ews k None (ctx_seq k p) *
       data_at_ Ews (tarray t_seqSymbol (sk_size k - 1 - 2 ^ ft_log t))
         (offset_val (8 * (1 + 2 ^ ft_log t)) (dd_seq k (ox_q ox))) * lt_gslot gv k).
    apply andp_right; [apply prop_right | cancel].
    split; [auto with share |].
    Exists TDict. try (unfold lt_ddslot; rewrite Ho).
    unfold seqspace_at, seqtab_at. Exists fm. entailer!.
  - Intros. subst t tp. unfold lt_gslot at 1.
    Exists Ers predef_fm (seqspace_at Ews k None (ctx_seq k p) * lt_ddslot ox k).
    apply andp_right; [apply prop_right | cancel].
    split; [auto with share |].
    Exists TGlob. unfold lt_gslot. entailer!.
Qed.

Lemma lt_where_intro (gv: globals) (p: val) (ox: option ddx) (k: seqkind) (t: fse_table) :
  seq_where gv p ox k t |-- EX tp: val, seq_where_tp gv p ox k t tp.
Proof.
  unfold seq_where, seq_where_tp. Intros tp w. Exists tp w. apply derives_refl.
Qed.

Lemma lt_where_elim (gv: globals) (p: val) (ox: option ddx) (k: seqkind) (t: fse_table) (tp: val) :
  seq_where_tp gv p ox k t tp |-- seq_where gv p ox k t.
Proof.
  unfold seq_where, seq_where_tp. Intros w. Exists tp w. apply derives_refl.
Qed.

Lemma lt_intro : TABS_INTRO.
Proof.
  intros gv p ox [[a b] c] fe. unfold tabs_seq, tabs_seq_tp.
  sep_apply (lt_where_intro gv p ox KLL a). Intros pa.
  sep_apply (lt_where_intro gv p ox KOF b). Intros pb.
  sep_apply (lt_where_intro gv p ox KML c). Intros pc.
  Exists (pa, pb, pc). cancel.
Qed.

Lemma lt_elim : TABS_ELIM.
Proof.
  intros gv p ox [[a b] c] fe [[pa pb] pc]. unfold tabs_seq, tabs_seq_tp.
  sep_apply (lt_where_elim gv p ox KLL a pa).
  sep_apply (lt_where_elim gv p ox KOF b pb).
  sep_apply (lt_where_elim gv p ox KML c pc).
  cancel.
Qed.

Lemma lt_borrow : TABS_BORROW.
Proof.
  intros HG gv p ox t fe tp.
  destruct t as [[a b] c]. destruct tp as [[pa pb] pc].
  destruct (lt_dent_split gv ox) as [Rd Hd]. destruct (HG gv) as [Rg Hg].
  rewrite Hd, Hg. unfold predef_tabs.
  change (seqtab_at_fm Ers KLL LL_predef predef_fm (gv _LL_defaultDTable)) with (lt_gslot gv KLL).
  change (seqtab_at_fm Ers KOF OF_predef predef_fm (gv _OF_defaultDTable)) with (lt_gslot gv KOF).
  change (seqtab_at_fm Ers KML ML_predef predef_fm (gv _ML_defaultDTable)) with (lt_gslot gv KML).
  unfold tabs_seq_tp.
  sep_apply (lt_one gv p ox KLL a pa). Intros sha fma Ra.
  sep_apply (lt_one gv p ox KOF b pb). Intros shb fmb Rb.
  sep_apply (lt_one gv p ox KML c pc). Intros shc fmc Rc.
  Exists (sha, shb, shc) (fma, fmb, fmc) (Ra * Rb * Rc * Rd * Rg).
  unfold seq_ptrs, seqtabs_at.
  unfold seq_ptr_at in *.
  apply andp_right; [apply prop_right | cancel].
  split; [simpl; auto |].
  intros fe'.
  sep_apply H0. sep_apply H2. sep_apply H4. cancel.
Qed.

Lemma lg_tabs_ok : TABS_INTRO /\ TABS_ELIM /\ TABS_BORROW.
Proof.
  split; [exact lt_intro | split; [exact lt_elim | exact lt_borrow]].
Qed.
