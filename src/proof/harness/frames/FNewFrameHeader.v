(* The frame header new_frame writes into its buffer of N bytes (harness/frames.h): put_le(f, magic, 4),
   f[4] = Frame_Header_Descriptor, f[5] = Window_Descriptor, then from at = 5 (Single_Segment, the
   Window_Descriptor byte is overwritten) or 6: put_le(f + at, dict_id, DID_Field_Size),
   put_le(f + at + DID_Field_Size, FCS field value, FCS_Field_Size).  The buffer then holds the header
   bytes nh_bytes (FModel.v) followed by the bytes not yet written (Vundef). *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.zstd.PickLemmas.
Require Import Zstd.proof.harness.frames.FSpecs.

(* A write of k bytes at i into a buffer holding the bytes l followed by M undefined cells, when the write
   starts inside the written prefix (i <= Zlength l) and ends at or beyond it: the buffer then holds the
   first i bytes of l, the k written bytes, and the rest still undefined. *)
Lemma mem_written_prefix : forall l M i k v,
  0 <= i <= Zlength l -> Zlength l <= i + k <= Zlength l + M -> 0 <= k ->
  Zstd.proof.zstd.Spec_util.mem_written (zbytes l ++ Zrepeat Vundef M) i k v =
  zbytes (sublist 0 i l ++ le_bytes (Z.to_nat k) v) ++ Zrepeat Vundef (Zlength l + M - (i + k)).
Proof.
  intros. unfold Zstd.proof.zstd.Spec_util.mem_written.
  pose proof (Zlength_le_bytes (Z.to_nat k) v).
  rewrite map_app. list_solve.
Qed.

(* A write of no bytes leaves the buffer unchanged. *)
Lemma mem_written_zero : forall c i v,
  0 <= i <= Zlength c -> Zstd.proof.zstd.Spec_util.mem_written c i 0 v = c.
Proof.
  intros. unfold Zstd.proof.zstd.Spec_util.mem_written. simpl. list_solve.
Qed.

(* Storing the byte b just after the written prefix l extends it by b. *)
Lemma upd_Znth_prefix : forall l M b,
  1 <= M ->
  upd_Znth (Zlength l) (zbytes l ++ Zrepeat Vundef M) (Vint (Int.repr b)) =
  zbytes (l ++ [b]) ++ Zrepeat Vundef (M - 1).
Proof.
  intros. rewrite map_app. list_solve.
Qed.

Lemma nf_header_written : forall fcs maxw did (h: nf_header) N,
  nh_ok fcs maxw did h -> 18 <= N ->
  let a := if nh_single h then 5 else 6 in
  Zstd.proof.zstd.Spec_util.mem_written
    (Zstd.proof.zstd.Spec_util.mem_written
       (upd_Znth 5
          (upd_Znth 4 (Zstd.proof.zstd.Spec_util.mem_written (Zrepeat Vundef N) 0 4 ZSTD_MAGICNUMBER)
             (Vint (Int.repr (nh_fhd h))))
          (Vint (Int.repr (nh_wd h))))
       a (nh_did_size h) did)
    (a + nh_did_size h) (nh_fcs_size h) (nh_fcs_value fcs h) =
  zbytes (nh_bytes fcs did h) ++ Zrepeat Vundef (N - Zlength (nh_bytes fcs did h)).
Proof.
  intros fcs maxw did h N Hok HN a.
  destruct Hok as (Hfl & _ & _ & _ & _ & _ & Hdl & _).
  (* the field sizes: DID 0..4 bytes, FCS 0..8 bytes, and at least 1 FCS byte with Single_Segment *)
  assert (Hds: 0 <= nh_did_size h <= 4).
  { unfold nh_did_size. destruct (Z.eqb_spec (nh_did_flag h) 3); lia. }
  assert (Hfs: 0 <= nh_fcs_size h <= 8 /\ (nh_single h = true -> 1 <= nh_fcs_size h)).
  { unfold nh_fcs_size, zb. destruct (Z.eqb_spec (nh_fcs_flag h) 0).
    - destruct (nh_single h); lia.
    - assert (nh_fcs_flag h = 1 \/ nh_fcs_flag h = 2 \/ nh_fcs_flag h = 3) as [-> | [-> | ->]] by lia;
        simpl; lia. }
  replace (Zrepeat Vundef N) with (zbytes [] ++ Zrepeat Vundef N) by reflexivity.
  rewrite mem_written_prefix by (simpl; list_solve).
  rewrite sublist_nil, app_nil_l, Zlength_nil. change (Z.to_nat 4) with 4%nat.
  remember (le_bytes 4 ZSTD_MAGICNUMBER) as L4 eqn:EL4.
  remember (le_bytes (Z.to_nat (nh_did_size h)) did) as D eqn:ED.
  remember (le_bytes (Z.to_nat (nh_fcs_size h)) (nh_fcs_value fcs h)) as F eqn:EF.
  assert (HL4: Zlength L4 = 4) by (subst L4; apply Zlength_le_bytes).
  assert (HD: Zlength D = nh_did_size h) by (subst D; rewrite Zlength_le_bytes; lia).
  assert (HF: Zlength F = nh_fcs_size h) by (subst F; rewrite Zlength_le_bytes; lia).
  unfold nh_bytes; rewrite <- EL4, <- ED, <- EF.
  rewrite <- HL4 at 1. rewrite upd_Znth_prefix by list_solve.
  replace 5 with (Zlength (L4 ++ [nh_fhd h])) at 1 by list_solve.
  rewrite upd_Znth_prefix by list_solve.
  rewrite <- app_assoc. simpl app.
  subst a. destruct Hfs as [Hfs Hfs1]. destruct (nh_single h).
  - (* Single_Segment: the DID field (if any) overwrites the Window_Descriptor byte, else the FCS field does *)
    specialize (Hfs1 eq_refl).
    destruct (Z.eq_dec (nh_did_size h) 0) as [Hd0 | Hd0].
    + rewrite Hd0, mem_written_zero by list_solve.
      rewrite Hd0 in HD. apply Zlength_nil_inv in HD. subst D.
      rewrite mem_written_prefix by list_solve. rewrite <- EF.
      list_solve.
    + rewrite mem_written_prefix by list_solve. rewrite <- ED.
      rewrite mem_written_prefix by list_solve. rewrite <- EF.
      list_solve.
  - rewrite mem_written_prefix by list_solve. rewrite <- ED.
    rewrite mem_written_prefix by list_solve. rewrite <- EF.
    list_solve.
Qed.
