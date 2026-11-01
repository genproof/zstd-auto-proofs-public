(* FS3 streaming, case zdss_loadHeader, piece B: the dictionary fields after the shortcut as zstd sets
   them (lhB_sw), from usingDDict_int_spec3's single-frame POST (FS3 R3) on the frame that starts with the header *)
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3Stmts.
Require Zstd.proof.dec.v3.FS.stream.lh.LH3RetG.

Section CM_LH3Bsw_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma lhB_sw_of (k1: cst3) (tbl: list val) (ibs: list Z) (ipos ipc isz cSize: Z) (hb: list Z) (h: frame_header)
    (d': dfields) :
  bytes_ok ibs -> Zlength ibs = isz -> 0 <= ipos -> ipos <= ipc -> ipc <= isz ->
  hb = sublist ipos ipc ibs -> get_frame_header_m (lh_mg k1) hb = FH_ok h -> fh_headerSize h = Zlength hb ->
  fh_frameType h = 0 ->
  frame_compressed_size_m (lh_mg k1) (sublist ipos isz ibs) = Some cSize -> cSize <= isz - ipos ->
  lhB_dict k1 d' ->
  (sel_on (c3_par k1) (c3_sp k1) = true ->
   frame_compressed_size_m (lh_mg k1) (sublist ipos (ipos + cSize) ibs) =
     Some (Zlength (sublist ipos (ipos + cSize) ibs)) ->
   forall h0, get_frame_header_m (lh_mg k1) (sublist ipos (ipos + cSize) ibs) = FH_ok h0 -> fh_frameType h0 = 0 ->
   d' = snd (getddict_res (c3_dict k1)) \/
   (exists q, In q (map fst (c3_set k1)) /\ d' = switch_fields q /\ q = hs_probe (c3_set k1) tbl (fh_dictID h0))) ->
  lhB_sw k1 tbl (sublist ipos (ipos + cSize) ibs) d'.
Proof.
intros Hb Hl H0 H1 H2 Ehb G Hs Ht F Hc Hd HP.
assert (Hgap: ipc <= ipos + cSize)
  by exact (LH3RetG.RG.gap_of_hdr_m _ ibs ipos ipc isz hb h cSize Hb Hl H0 H1 H2 (eq_sym Ehb) G Hs F).
assert (Hbh: bytes_ok hb) by (rewrite Ehb; unfold bytes_ok in *; apply Forall_sublist; auto).
assert (Hx: sublist ipos (ipos + cSize) ibs = hb ++ sublist ipc (ipos + cSize) ibs)
  by (rewrite Ehb, <- sublist_split; auto; lia).
assert (Hgx: get_frame_header_m (lh_mg k1) (sublist ipos (ipos + cSize) ibs) = FH_ok h)
  by (rewrite Hx; apply LH3RetG.RG.gfh_m_ext; auto).
assert (Hlx: Zlength (sublist ipos (ipos + cSize) ibs) = cSize) by (rewrite Zlength_sublist; lia).
assert (Hfx: frame_compressed_size_m (lh_mg k1) (sublist ipos (ipos + cSize) ibs) =
             Some (Zlength (sublist ipos (ipos + cSize) ibs))).
{ assert (Hbs: bytes_ok (sublist ipos isz ibs)) by (unfold bytes_ok in *; apply Forall_sublist; auto).
  destruct (LH3RetG.RG.fcs_m_trunc _ _ _ Hbs F) as [_ Ht']. rewrite <- sublist_firstn, sublist_sublist in Ht' by lia.
  rewrite Hlx. rewrite <- Ht'. f_equal. f_equal; lia. }
destruct Hd as [E | (Hon & q & Hq & E)]; [ left; exact E | ].
destruct (HP Hon Hfx h Hgx Ht) as [E2 | (q' & Hq' & E' & Ep)]; [ left; exact E2 | right ].
split; [ exact Hon | ]. exists q'. split; [ exact Hq' | ]. split; [ exact E' | ].
intros h'' G''. rewrite Hgx in G''. injection G'' as E''. subst h''. exact Ep.
Qed.

End CM_LH3Bsw_1.
