(* FS3 streaming, case zdss_loadHeader, G4: the model side of the new frame (alive_ok). *)
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3Stmts Zstd.proof.dec.v3.FS.stream.lh.LH3G42_dict Zstd.proof.dec.v3.FS.stream.lh.LH3G42_frame Zstd.proof.dec.v3.FS.stream.lh.LH3G42_skip.
Local Open Scope Z_scope.

Section CM_LH3G42_alive_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* the facts the main lemmas take (g4_read derives them: lhC_facts, lh_dd_ok) *)
Definition g4_gaps (a: dsa) (w: lw) (h: frame_header) (c: lhc) : Prop :=
  (lc_dd c = None -> lc_did c = 0) /\
  (forall x buf, lc_dd c = Some (x, buf) -> ddx_model x <> None).

(* the view of the stream after piece D *)
Definition g4_sv (st: dctx_st) (hb: list Z) (h: frame_header) (c: lhc) : sview :=
  {| sv_fp := if fh_frameType h =? 1 then FP_skip hb 0
              else FP_zstd hb (z_start h (g4_dm_of (lc_dd c)) (sm_bsm (sm_of st) h) (md_ignore (dmode_of (dc_par st))));
     sv_pend := nil; sv_ahead := nil; sv_lay := g4_lay (lc_dd c); sv_dd := lc_dd c |}.

Lemma g4_hist : forall stable k sv dd, sv_lay sv = g4_lay dd -> hist_ok stable k sv.
Proof.
intros stable k sv dd E. unfold hist_ok. intros _ _ _. rewrite E. unfold g4_lay.
destruct dd as [[x buf]|]; [ destruct (eq_dec buf nullval) | ]; exact I.
Qed.

Lemma g4_alive : MF3 -> hs_probe_ok -> forall W a w hb h tbl d1 did1 c s3 sv0 sin sout,
  let k := w_k w in
  let k1 := k_A k (fh_val h) d1 did1 in
  let k3 := lhD_k (lhC_k k1 hb h c) h s3 in
  base_call (a_st a) k -> stream_dict_ok W (a_st a) ->
  (c3_set k = nil -> c3_sp k = nullval) -> (c3_set k <> nil -> c3_sp k <> nullval) ->
  lhA_sel k hb 0 (fh_val h) tbl d1 did1 -> get_frame_header_m (lh_mg k) hb = FH_ok h ->
  gfh3_facts (lh_mg k) hb h -> fh_headerSize h = Zlength hb -> bytes_ok hb ->
  lhC_facts a w k1 h c -> g4_gaps a w h c -> g4_local_ok (a_st a) (snd (getddict_res d1)) ->
  bytes_ok sin ->
  sv_fp sv0 = FP_hdr hb -> sv_pend sv0 = nil ->
  alive_ok (a_st a) k sv0 sin sout ->
  alive_ok (a_st a) k3 (g4_sv (a_st a) hb h c) sin sout.
Proof.
intros HMF Hpr W a w hb h tbl d1 did1 c s3 sv0 sin sout k k1 k3 Hb Hsd Hsp0 Hsp1 Hsel Hgfh Hgf Hlen Hbhb HC
  (Gap1 & Gap2) Hloc Hbsin Hfp0 Hpend0 Halive.
set (st := a_st a) in *. set (sm := sm_of st).
unfold alive_ok in *. destruct Halive as [Hd | (cd & Hm & Hcd & _)]; [ left; exact Hd | ].
destruct Hm as (dsin & fb & recs & Hsin & Hser & Hcur & Hcr & Hout).
rewrite Hfp0 in Hcr, Hcd, Hout. rewrite Hpend0 in Hout. cbn [cur_rel] in Hcr. destruct Hcr as [-> _].
cbn [next_cd] in Hcd.
assert (Hbd: bytes_ok dsin).
{ rewrite Hsin in Hbsin. unfold bytes_ok in *. apply Forall_app in Hbsin. apply Hbsin. }
assert (Hdead: fdead sm cd hb -> dead (sm_of st) sin).
{ intros Hf. rewrite Hsin. exact (mf_dead_of_fdead HMF sm cd dsin recs hb Hbd Hser Hcur Hf). }
pose proof Hb as Hb'. destruct Hb' as (_ & Hpar & _ & _ & _).
assert (Hmg: sm_mg sm = lh_mg k) by (unfold sm_mg, sm, sm_of, lh_mg; cbn; rewrite Hpar; reflexivity).
assert (Hcd0: st_sel st = (sel_none, None) -> cd = None).
{ intros E. rewrite <- Hcur. unfold series_cur, sm, sm_of. cbn [sm_sel sm_cur]. rewrite E. cbn [fst snd].
  apply g4_walk_cur_none. }
destruct Hgf as (G5 & Gfcs & Gws & Gbsm & Gbsm2 & Gck & Gft & Gskm & Gsk & Gdid & Ghs).
destruct HC as (HCdd & HCcold & HCdidr & HCst & HCid & _ & HCwin).
rewrite <- Hmg in Hgfh.
destruct Gft as [Ft | Ft].
- (* a Zstandard frame *)
  unfold g4_sv. replace (fh_frameType h =? 1) with false by (symmetry; apply Z.eqb_neq; lia).
  destruct (frame_dict (sm_mg sm) (sm_sel sm) cd hb) as [dm'|] eqn:Efd.
  2: { left. apply Hdead. exact (proj1 (mf_hdr_zstd HMF sm cd hb h Hbhb Hgfh Ft (eq_sym Hlen)) Efd). }
  destruct (Z.eq_dec (fh_dictID h) 0) as [Hz|Hz];
  [ | destruct (Z.eq_dec (fh_dictID h) (dm_id dm')) as [Hz'|Hz'];
      [ | left; apply Hdead; exact (proj1 (proj2 (mf_hdr_zstd HMF sm cd hb h Hbhb Hgfh Ft (eq_sym Hlen))) dm' Efd Hz Hz') ] ];
  [ assert (Hid: fh_dictID h = 0 \/ fh_dictID h = dm_id dm') by (left; exact Hz)
  | assert (Hid: fh_dictID h = 0 \/ fh_dictID h = dm_id dm') by (right; exact Hz') ];
  clear Hz; try clear Hz'.
  all: rewrite Hmg in Efd.
  all: destruct (g4_dm Hpr W a k hb h tbl d1 did1 c cd dm' Hb Hsd Hsp0 Hsp1 Hsel Gdid HCdd
                   (HCid ltac:(lia)) Gap1 Hloc Hcd0 Hcd ltac:(rewrite <- Hmg; exact Hgfh) Efd) as [Hddm Hcdk].
  all: rewrite (g4_dm_of_eq _ _ Hddm).
  all: rewrite <- Hmg in Efd.
  all: right; exists cd; split; [ | split; [ apply Hcdk; reflexivity | apply (g4_hist _ _ _ (lc_dd c)); reflexivity ] ].
  all: exists dsin, hb, recs; split; [ exact Hsin | split; [ exact Hser | split; [ exact Hcur | split ] ] ];
       [ exact (proj2 (proj2 (proj2 (mf_hdr_zstd HMF sm cd hb h Hbhb Hgfh Ft (eq_sym Hlen)))) dm' Efd Hid)
       | cbn [sv_pend sv_fp fp_content zp_out z_start] in Hout |- *; exact Hout ].
- (* a skippable frame *)
  unfold g4_sv. rewrite Ft. change (1 =? 1) with true. cbv iota.
  assert (Hmg0: sm_mg sm = false) by (rewrite Hmg; apply Gskm; exact Ft).
  assert (Hg: get_frame_header hb = FH_ok h) by (rewrite Hmg0 in Hgfh; exact Hgfh).
  destruct (mf_hdr_skip HMF sm cd hb h Hbhb Hmg0 Hg Ft (eq_sym Hlen)) as (_ & _ & _ & Hok).
  right. exists cd. split; [ | split; [ | apply (g4_hist _ _ _ (lc_dd c)); reflexivity ] ].
  + exists dsin, hb, recs. split; [ exact Hsin | split; [ exact Hser | split; [ exact Hcur | split ] ] ].
    * exact Hok.
    * cbn [sv_pend sv_fp fp_content] in Hout |- *; exact Hout.
  + cbn [next_cd sv_fp]. unfold sm_of. cbn [sm_md sm_sel].
    assert (Hvar: fh_dictID h = Z.land (le_field hb 0 4) 15)
      by (apply (g4_skip_did hb h Hbhb Hg Ft); apply Gskm; exact Ft).
    apply (g4_cd_skip2 Hpr W a k hb h tbl d1 did1 cd k3 Hb Hsd Hsp0 Hsp1 Hsel Gdid Hvar Hcd0 Hcd); reflexivity.
Qed.

End CM_LH3G42_alive_1.
