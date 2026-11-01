(* ZSTD_decompressStream, case zdss_loadHeader with the exact claim: G4, after piece D: the fall-through into
   zdss_read with ex_call (S3XKit.ex_loop_fall).  From the configuration of a new context (no dictionary, default
   parameters, buffered output) the model's iteration from the loadHeader state is st_header_done, which (the
   shortcut not taken) ends with st_read on a stage-read state g4_z2; the context after pieces A, C and D represents
   that state (zrel_end). *)
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3XDefs.
Require Import Zstd.proof.model.ExCall Zstd.proof.model.ExStream Zstd.proof.model.ExStreamFacts.
Require Import Zstd.proof.model.ExStreamBnd Zstd.proof.model.ExStreamOver Zstd.proof.model.ParamsH.
Require Zstd.proof.model.ExHuf Zstd.proof.model.ExBlock Zstd.proof.model.Exact.
(* ---------- the model: st_header_done without the shortcut ---------- *)

(* the frame state after ZSTD_decompressBegin and the header (no dictionary): a skippable frame's size to skip, or
   the first block header to read with the checksum flag *)
Definition g4_d1 (hb: list Z) (h: frame_header) (d: dstate XS) : dstate XS :=
  let d0 := d_begin XS (ExBlock.xst_begin ExHuf.xhuf) d in
  if is_skippable_magic (le_field hb 0 4) then d_goto XS d0 DS_skipFrame (le_field hb 4 4)
  else d_goto XS (d_set_check XS d0 (fh_checksumFlag h =? 1)) DS_decodeBlockHeader ZSTD_blockHeaderSize.

(* fParams once the header is consumed (windowSize raised to 1 KiB) *)
Definition g4_fp (h: frame_header) : frame_header :=
  {| fh_contentSize := fh_contentSize h; fh_windowSize := Z.max (fh_windowSize h) (2 ^ ZSTD_WINDOWLOG_ABSOLUTEMIN);
     fh_blockSizeMax := fh_blockSizeMax h; fh_frameType := fh_frameType h; fh_headerSize := fh_headerSize h;
     fh_dictID := fh_dictID h; fh_checksumFlag := fh_checksumFlag h |}.

(* the stage-read state st_header_done hands to st_read (z: the loadHeader state, h its header) *)
Definition g4_z2 (z: zstate_x) (h: frame_header) : zstate_x :=
  let z' := z_fp XS z h in
  let fcs := fh_contentSize h in
  let ws := Z.max (fh_windowSize h) (2 ^ ZSTD_WINDOWLOG_ABSOLUTEMIN) in
  let bsm := fh_blockSizeMax h in
  let needIn := Z.max bsm 4 in
  let needOut := Z.min fcs (ws + 2 * Z.min (Z.min ws ZSTD_BLOCKSIZE_MAX) bsm + 2 * ZS_WILDCOPY_OVERLENGTH) in
  let over := if zs_inbs XS z' + zs_outbs XS z' >=? (needIn + needOut) * ZS_WORKSPACETOOLARGE_FACTOR
              then zs_over XS z' + 1 else 0 in
  let realloc := orb (orb (zs_inbs XS z' <? needIn) (zs_outbs XS z' <? needOut))
                     (over >=? ZS_WORKSPACETOOLARGE_MAXDURATION) in
  let z1 := z_dc XS (z_fp XS z' (g4_fp h)) (g4_d1 (zs_hbuf XS z') h (zs_dc XS z')) in
  let z2 := if realloc then z_bufs XS z1 needIn needOut over (ring_fresh needOut)
            else z_bufs XS z1 (zs_inbs XS z') (zs_outbs XS z') over (zs_mem XS z') in
  z_stage XS z2 ZDSS_read.

(* st_header_done when the shortcut's conditions fail, the header asks for no dictionary (or is a skippable
   frame's) and the window is within the default limit: st_read on g4_z2 *)
Lemma g4_iter (inp: list Z) (room: Z) (z: zstate_x) (h: frame_header) (ip: Z) :
  (fh_contentSize h <> ZSTD_CONTENTSIZE_UNKNOWN -> fh_frameType h <> 1 -> fh_contentSize h <= room ->
   Zlength (zs_hbuf XS z) = ip -> forall cs, frame_compressed_size inp = Some cs -> Zlength inp < cs) ->
  (is_skippable_magic (le_field (zs_hbuf XS z) 0 4) = false -> fh_dictID h = 0) ->
  Z.max (fh_windowSize h) (2 ^ ZSTD_WINDOWLOG_ABSOLUTEMIN) <= ZS_MAXWINDOWSIZE_DEFAULT ->
  st_header_done XS (ExBlock.xst_begin ExHuf.xhuf) Exact.xblock xframe1 inp room (z_fp XS z h) h ip nil =
  st_read XS Exact.xblock inp (g4_z2 z h) ip nil.
Proof.
intros Hsc Hdid Hws.
unfold st_header_done, g4_z2, g4_d1. cbv zeta.
lazymatch goal with |- match ?s with Some _ => _ | None => _ end = _ => assert (Hn: s = None); [|rewrite Hn] end.
{ lazymatch goal with |- (if ?b then _ else None) = None => destruct b eqn:E; [|reflexivity] end.
  rewrite !andb_true_iff in E. destruct E as (((E1 & E2) & E3) & E4).
  rewrite negb_true_iff, Z.eqb_neq in E1, E2. rewrite Z.geb_le in E3. rewrite Z.eqb_eq in E4.
  rewrite Zlength_nil in E3. cbn [zs_hbuf z_fp] in E4.
  pose proof (Hsc E1 E2 ltac:(lia) E4) as Hc.
  destruct (frame_compressed_size inp) as [cs|] eqn:Fc; [|reflexivity].
  pose proof (Hc cs eq_refl). destruct (Z.leb_spec cs (Zlength inp)); [lia|reflexivity]. }
cbn [zs_hbuf z_fp zs_dc].
destruct (is_skippable_magic (le_field (zs_hbuf XS z) 0 4)) eqn:Es.
- destruct (Z.gtb_spec (Z.max (fh_windowSize h) (2 ^ ZSTD_WINDOWLOG_ABSOLUTEMIN)) ZS_MAXWINDOWSIZE_DEFAULT); [lia|].
  reflexivity.
- assert (Ed: (fh_dictID h =? 0) = true) by (rewrite (Hdid eq_refl); reflexivity). rewrite Ed. cbn [negb].
  destruct (Z.gtb_spec (Z.max (fh_windowSize h) (2 ^ ZSTD_WINDOWLOG_ABSOLUTEMIN)) ZS_MAXWINDOWSIZE_DEFAULT); [lia|].
  reflexivity.
Qed.

(* the fields of g4_z2: the stage read, the frame state begun, the buffers sized as st_header_done does *)
Lemma g4_z2_fields (z: zstate_x) (h: frame_header) :
  let z2 := g4_z2 z h in
  let ws := Z.max (fh_windowSize h) (2 ^ ZSTD_WINDOWLOG_ABSOLUTEMIN) in
  let bsm := fh_blockSizeMax h in
  let needIn := Z.max bsm 4 in
  let needOut := Z.min (fh_contentSize h) (ws + 2 * Z.min (Z.min ws ZSTD_BLOCKSIZE_MAX) bsm + 2 * ZS_WILDCOPY_OVERLENGTH) in
  let over := if zs_inbs XS z + zs_outbs XS z >=? (needIn + needOut) * ZS_WORKSPACETOOLARGE_FACTOR
              then zs_over XS z + 1 else 0 in
  zs_stage XS z2 = ZDSS_read /\ zs_hbuf XS z2 = zs_hbuf XS z /\ zs_fp XS z2 = g4_fp h /\
  zs_ibuf XS z2 = zs_ibuf XS z /\ zs_inpos XS z2 = zs_inpos XS z /\ zs_ostart XS z2 = zs_ostart XS z /\
  zs_oend XS z2 = zs_oend XS z /\ zs_nfp XS z2 = zs_nfp XS z /\ zs_host XS z2 = zs_host XS z /\
  zs_dc XS z2 = g4_d1 (zs_hbuf XS z) h (zs_dc XS z) /\ zs_over XS z2 = over /\
  if orb (orb (zs_inbs XS z <? needIn) (zs_outbs XS z <? needOut)) (over >=? ZS_WORKSPACETOOLARGE_MAXDURATION)
  then zs_inbs XS z2 = needIn /\ zs_outbs XS z2 = needOut /\ zs_mem XS z2 = ring_fresh needOut
  else zs_inbs XS z2 = zs_inbs XS z /\ zs_outbs XS z2 = zs_outbs XS z /\ zs_mem XS z2 = zs_mem XS z.
Proof.
intros z2 ws bsm needIn needOut over. subst z2 ws bsm needIn needOut over.
unfold g4_z2. cbv zeta. cbn [z_fp zs_inbs zs_outbs zs_over zs_mem zs_hbuf zs_dc].
match goal with |- context [if ?b then _ else _] => destruct b end;
  cbn; repeat split; reflexivity.
Qed.

(* field computations of the stream and frame states (as in model/ExStreamFacts.v, whose tactics are local) *)
Local Ltac g4_zd :=
  unfold d_goto, d_set_check, d_begin;
  cbn [d_stage d_expected d_btype d_rle d_out d_check d_ent d_prev d_pfx d_ds d_de].
Local Ltac g4_consts :=
  unfold ZSTD_blockHeaderSize, DS_decodeBlockHeader, DS_decompressBlock, DS_decompressLastBlock, DS_checkChecksum,
    DS_skipFrame, BT_reserved, ZDSS_init, ZDSS_loadHeader, ZDSS_read, ZDSS_load, ZDSS_flush in *.

(* g4_z2 keeps the fuel invariant of the loadHeader state (as ExStreamFacts.st_header_done_ok shows for the state
   st_read starts from): the header h is complete and its window within the default maximum *)
Lemma g4_z2_zinv (z: zstate_x) (h: frame_header) :
  zinv_x z -> zs_stage XS z = ZDSS_loadHeader -> get_frame_header (zs_hbuf XS z) = FH_ok h ->
  Z.max (fh_windowSize h) (2 ^ ZSTD_WINDOWLOG_ABSOLUTEMIN) <= ZS_MAXWINDOWSIZE_DEFAULT ->
  zinv_x (g4_z2 z h).
Proof.
intros Hz Hs Hg Hws.
pose proof Hz as (Hd & Hr & Hbf & He & Ho).
destruct Hbf as (Hl & Hn & Hli & Hhb & Hib & Hih & Hlh & Hfc & Hbs).
destruct Hr as (Ho1 & Ho2 & Hmb & Hml & Hoff).
assert (Hs': zs_stage XS z <> ZDSS_load) by (rewrite Hs; discriminate).
destruct (Hn Hs') as [Hp0 Hi0].
assert (He0: d_expected XS (zs_dc XS z) = 0) by (apply Hih; right; exact Hs).
destruct (Hlh Hs) as [Hos Hoe].
destruct (zf_gfh_bounds _ _ Hhb Hg) as (G1 & G2 & G3).
pose proof (zf_gfh_bsm _ _ Hg) as Hbm.
pose proof Hd as (Dst & Dbt & Dex & Drl & Din & Dg).
pose proof (g4_z2_fields z h) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12).
set (d1 := g4_d1 (zs_hbuf XS z) h (zs_dc XS z)) in *.
(* the frame state begun: in range, no ring offsets yet, inside a frame's blocks only for a non-skippable frame *)
assert (D1: zi_dc XS xgood_x d1 /\ d_prev XS d1 = None /\ d_pfx XS d1 = None /\ d_ds XS d1 = None /\
            d_de XS d1 = None /\ (zin XS d1 -> is_skippable_magic (le_field (zs_hbuf XS z) 0 4) = false)).
{ subst d1. unfold g4_d1. destruct (is_skippable_magic _) eqn:Esk.
  - pose proof (zf_le_field_lt (zs_hbuf XS z) 4 4 Hhb ltac:(lia)) as L1.
    pose proof (zf_le_field_nonneg (zs_hbuf XS z) 4 4 Hhb) as L2.
    change (2 ^ (8 * 4)) with (2 ^ 32) in L1.
    unfold zi_dc, zin; g4_zd; g4_consts.
    split; [split; [lia|]; split; [lia|]; split; [lia|]; split; [exact Drl|]; split; [intros; lia|];
            apply xgood_x_begin, Dg|].
    repeat split; auto. intros; lia.
  - unfold zi_dc, zin; g4_zd; g4_consts.
    split; [split; [lia|]; split; [lia|]; split; [lia|]; split; [exact Drl|]; split; [intros; lia|];
            apply xgood_x_begin, Dg|].
    repeat split; auto. }
destruct D1 as (D1 & P1 & P2 & P3 & P4 & Psk).
assert (Hoffn: forall n, zi_off XS d1 n) by (intros n x [Hx|[Hx|[Hx|Hx]]]; congruence).
set (ws := Z.max (fh_windowSize h) (2 ^ ZSTD_WINDOWLOG_ABSOLUTEMIN)) in *.
set (needOut := Z.min (fh_contentSize h)
                  (ws + 2 * Z.min (Z.min ws ZSTD_BLOCKSIZE_MAX) (fh_blockSizeMax h) + 2 * ZS_WILDCOPY_OVERLENGTH)) in *.
assert (Hno: 0 <= needOut).
{ subst needOut ws. unfold ZSTD_BLOCKSIZE_MAX, ZS_WILDCOPY_OVERLENGTH, ZSTD_WINDOWLOG_ABSOLUTEMIN.
  clear - G1 G2. lia. }
(* oversizedDuration: ExStreamFacts.zi_over_bufs on the state with the header *)
assert (HOv: zi_over XS (g4_z2 z h)).
{ unfold g4_z2. cbv zeta. eapply zi_over_bufs; [exact Ho | apply Z.le_max_r | exact Hno |].
  subst needOut ws. unfold ZS_MAXWINDOWSIZE_DEFAULT, ZSTD_BLOCKSIZE_MAX, ZS_WILDCOPY_OVERLENGTH,
    ZSTD_WINDOWLOG_ABSOLUTEMIN in *. clear - Hws Hbm G1 G2. lia. }
set (z2 := g4_z2 z h) in *.
unfold zinv_x, zinv. split; [rewrite F10; exact D1|]. split; [|split; [|split; [|exact HOv]]].
- unfold zi_ring. rewrite F6, F7, F10, Hos, Hoe.
  revert F12. match goal with |- (if ?b then _ else _) -> _ => destruct b end; intros (B1 & B2 & B3);
    rewrite B2, B3.
  + split; [clear - Hno; lia|]. split; [clear - Hno; lia|].
    split; [unfold bytes_ok, ring_fresh; apply Forall_forall; intros x Hx; apply repeat_spec in Hx; subst x;
            unfold is_byte; lia|].
    split; [unfold ring_fresh; rewrite Zlength_correct, repeat_length; clear - Hno; lia|]. apply Hoffn.
  + split; [clear - Ho2 Hoe; lia|]. split; [clear - Ho2 Hoe; lia|]. split; [exact Hmb|]. split; [exact Hml|].
    apply Hoffn.
- unfold zi_buf. cbv zeta. rewrite F1, F2, F3, F4, F5, F10. g4_consts. cbn [g4_fp fh_contentSize fh_blockSizeMax].
  split; [intros C; discriminate C|]. split; [intros _; split; assumption|]. split; [intros C; discriminate C|].
  split; [exact Hhb|]. split; [exact Hib|]. split; [intros [C|C]; discriminate C|].
  split; [intros C; discriminate C|]. split; assumption.
- unfold zi_ext. cbv zeta. rewrite F1, F3, F6, F10. cbn [g4_fp fh_contentSize fh_blockSizeMax].
  intros Hz0. split; [intros Hc; apply G3; [apply Psk, Hz0 | exact Hc]|].
  split; [intros C; contradiction|]. split; [intros _; split; [left; exact P1 | intros C; contradiction]|].
  g4_consts. intros C; discriminate C.
Qed.

(* the ring size zstd computes (S3Defs.ring_needed) is the model's needOut *)
Lemma g4_ring_needed (h: frame_header) :
  ring_needed h (fh_blockSizeMax h) =
  Z.min (fh_contentSize h) (Z.max (fh_windowSize h) (2 ^ ZSTD_WINDOWLOG_ABSOLUTEMIN) +
    2 * Z.min (Z.min (Z.max (fh_windowSize h) (2 ^ ZSTD_WINDOWLOG_ABSOLUTEMIN)) ZSTD_BLOCKSIZE_MAX) (fh_blockSizeMax h) +
    2 * ZS_WILDCOPY_OVERLENGTH).
Proof.
unfold ring_needed. cbv zeta.
replace (2 ^ ZSTD_WINDOWLOG_ABSOLUTEMIN) with ZSTD_WINDOWSIZE_ABSMIN by reflexivity.
f_equal. unfold WILDCOPY_OVERLENGTH, ZS_WILDCOPY_OVERLENGTH. ring.
Qed.

(* zstd's fParams once the frame starts (S3Defs.fh_adj, blockSizeMax not capped) is the model's *)
Lemma g4_fp_adj (h: frame_header) : fh_adj h (fh_blockSizeMax h) = g4_fp h.
Proof. reflexivity. Qed.

(* the frame begun has no Huffman table (ExBlock.xst_begin), so its table is in range (ExBlockBytes.xh_good) *)
Lemma g4_xh_good_begin (st: ExBlock.xst ExHuf.xhuf) :
  ExBlockBytes.xh_good (ExBlock.x_huf ExHuf.xhuf (ExBlock.xst_begin ExHuf.xhuf st)).
Proof. exact I. Qed.

Local Open Scope logic.

Section CM_LH3G4X_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.

Lemma lh_read_x_ok : lh_read_x_stmt.
Proof.
intros HMF Hpr Hddb DENT TABS a w hb h tbl d1 did1 c s3 Hctx Hx Hgfh Hgf Hsel Hns k1 HC HCx k3 HD HDx w3.
apply prop_right.
pose proof Hctx as (Ha & Hso & Hci & Hsmw & Hle & He & Hfpv & Hdl & Hah & Hpend & Hent & Hun).
apply ex_call_next_mk; [exact Hsmw |]. intros Hf.
destruct (lhx_view a w hb He Hx Hf) as (z0 & zi & f & Hl & Hz & Hst & Hhb & Hone).
pose proof Hf as (Hfd & Hfpar & Hfset & Hfst & Hfex).
pose proof He as (Hs1 & Hlh & Hl18 & Hbo & Hsub & Hhost & Hip0 & Hos0 & Hoe0 & Hipc & Hopc & Hocl & _ & Hbc & Hlen).
pose proof Hbc as (Hbst & Hbpar & Hbset & Hbdict & _ & Hfpok & _).
assert (Hmg: lh_mg (w_k w) = false) by (unfold lh_mg; rewrite Hbpar, Hfpar; reflexivity).
rewrite Hmg in Hgfh, Hgf. change (get_frame_header hb = FH_ok h) in Hgfh.
assert (Hopc0: w_opc w = a_opos a).
{ destruct Hci as (_ & _ & _ & _ & Hdll & _). rewrite Hdl, Zlength_nil in Hdll. lia. }
(* no dictionary, no selection: piece C began the frame without a DDict *)
assert (Hsoff: sel_on (c3_par (w_k w)) (c3_sp (w_k w)) = false) by (unfold sel_on; rewrite Hbpar, Hfpar; reflexivity).
destruct Hsel as (_ & _ & id & _ & Hsb). unfold sel_by in Hsb. rewrite Hsoff in Hsb. destruct Hsb as (Ed1 & Edid1).
assert (Hu0: df_uses (c3_dict (w_k w)) = 0).
{ unfold dict_rel3 in Hbdict. rewrite Hfd, Hfset in Hbdict.
  destruct Hbdict as [(Hu & _) | (Hne & _)]; [exact Hu | congruence]. }
assert (Hgd: getddict_res (c3_dict k1) = (nullval, df_none)).
{ unfold getddict_res. change (c3_dict k1) with d1. rewrite Ed1, Hu0. reflexivity. }
pose proof HC as (HCdd & HCcold & HCdid & _ & HCdid2 & HCnone & HCw).
assert (Hdd: lc_dd c = None).
{ destruct (lc_dd c) as [[x buf]|] eqn:Edd; [| reflexivity]. exfalso. cbn [lhC_dd] in HCdd.
  destruct HCdd as (Hq & Hqn & _). rewrite Hgd in Hq. cbn [fst] in Hq. contradiction. }
assert (Hdid0: lc_did c = 0) by auto.
assert (Hpar1: c3_par k1 = dparams_dflt) by (change (c3_par k1) with (c3_par (w_k w)); rewrite Hbpar; exact Hfpar).
rewrite Hpar1 in HCw.
pose proof Hgf as (Gsl & Gcs & Gws & Gbs & Gbs2 & Gck & Gft & Gskip & Gskip2 & Gdid & Ghs).
pose proof Hz as (Hz1 & Hz2 & Hz3 & Hz4 & Hz5 & Hz6 & Hz7 & Hz8 & Hz9 & Hz10 & Hzl & Hzr).
destruct (Hzl Hst) as (Ezl & Ez18 & Ezb & Ezs & Ezip & Ezinp & Ezos & Ezoe & Ezost & Ezoen & Ezh & Ezhost).
assert (Hlx: Zlength (a_xin a) = a_isz a - a_ipos a).
{ destruct Ha as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hip & _ & Hlb & _).
  unfold a_xin. rewrite Zlength_sublist; lia. }
(* the model: st_load_header, then st_header_done without the shortcut, is st_read on g4_z2 *)
assert (Hsk: fh_frameType h = 1 <-> is_skippable_magic (le_field hb 0 4) = true) by (rewrite Gskip; tauto).
assert (Hsc: fh_contentSize h <> ZSTD_CONTENTSIZE_UNKNOWN -> fh_frameType h <> 1 -> fh_contentSize h <= a_xroom a ->
   Zlength (zs_hbuf XS zi) = w_ipc w - a_ipos a ->
   forall cs, frame_compressed_size (a_xin a) = Some cs -> Zlength (a_xin a) < cs).
{ intros E1 E2 E3 E4 cs Fc. rewrite Hhb in E4. unfold a_xroom in E3. rewrite Hlx. unfold lhB_none in Hns. rewrite Hmg in Hns.
  apply (Hns E1 E2 ltac:(lia) ltac:(lia) cs Fc). }
assert (Hdid: is_skippable_magic (le_field (zs_hbuf XS zi) 0 4) = false -> fh_dictID h = 0).
{ intros Es. rewrite Hhb in Es. assert (Hft: fh_frameType h <> 1) by (rewrite Hsk, Es; discriminate).
  destruct (HCdid2 Hft) as [E|E]; [exact E | rewrite E; exact Hdid0]. }
assert (Hws: Z.max (fh_windowSize h) (2 ^ ZSTD_WINDOWLOG_ABSOLUTEMIN) <= ZS_MAXWINDOWSIZE_DEFAULT).
{ exact HCw. }
assert (Hiter: one_iter_x (a_xin a) (a_xroom a) zi (w_ipc w - a_ipos a) [] =
               one_iter_x (a_xin a) (a_xroom a) (g4_z2 zi h) (w_ipc w - a_ipos a) []).
{ rewrite Hone. unfold st_load_header. cbv zeta. rewrite Hhb at 1. rewrite Hgfh.
  rewrite (g4_iter _ _ _ _ _ Hsc Hdid Hws). unfold one_iter_x.
  rewrite one_iter_read; [reflexivity | exact (proj1 (g4_z2_fields zi h))]. }
assert (Hzi: zinv_x zi) by (destruct Hl as (_ & _ & Hi & _); exact Hi).
pose proof (g4_z2_zinv zi h Hzi Hst ltac:(rewrite Hhb; exact Hgfh) Hws) as Hz2i.
pose proof (zinv_x_bnd _ Hz2i) as Hbnd.
exists z0, (g4_z2 zi h), f. split.
{ change (w_ipc w3) with (w_ipc w). change (w_dl w3) with (w_dl w). rewrite Hdl.
  apply (ex_loop_fall a z0 zi); auto.
  unfold zpot. rewrite (proj1 (g4_z2_fields zi h)), Hst. reflexivity. }
(* piece D's buffers are st_header_done's *)
assert (Ein: sf_inSize (c3_s k3) = zs_inbs XS zi) by (change (sf_inSize (c3_s k3)) with (sf_inSize (w_sx w)); exact Hz3).
assert (Eout: sf_outSize (c3_s k3) = zs_outbs XS zi) by (change (sf_outSize (c3_s k3)) with (sf_outSize (w_sx w)); exact Hz4).
assert (Eov: sf_over (c3_s k3) = zs_over XS zi) by (change (sf_over (c3_s k3)) with (sf_over (w_sx w)); exact Hz5).
assert (Estab: c3_stable k3 = false) by (change (c3_stable k3) with (c3_stable (w_k w)); rewrite Hbst; exact Hfst).
assert (Ebsm: lh_bsm k3 h = fh_blockSizeMax h).
{ unfold lh_bsm, dmode_of. change (c3_par k3) with (c3_par k1). rewrite Hpar1. cbn [md_bmax dp_bmax dparams_dflt].
  unfold ZSTD_BLOCKSIZE_MAX in *. cbn [Z.eqb]. lia. }
pose proof (g4_ring_needed h) as Erng.
pose proof (HDx Estab ltac:(rewrite Eov; pose proof (zinv_x_over zi Hzi); rep_lia)) as HDx'. cbv zeta in HDx'.
rewrite Ebsm, Erng, Ein, Eout, Eov in HDx'.
pose proof (g4_z2_fields zi h) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12).
destruct HDx' as (Hov3 & Hbuf3).
pose proof HD as (Hd_stage & Hd_inPos & Hd_os & Hd_oe & Hd_lh & Hd_hbuf & Hd_host & Hd_nfp & Hd_exp & Hd_ib & Hd_ibp &
  Hd_ins & Hd_sum & Hd_os2 & Hd_mem & Hd_held).
change (w_sx w3) with (sf_strip s3). change (w_fs w3) with (fsu_fParams (lhC_fs k1 hb h c) (fh_val (fh_adj h (lh_bsm k3 h)))).
change (w_tabs w3) with (TInit (dd_ox (lc_dd c)) (lh_dd_ts (lc_dd c) (lc_lxb c))).
rewrite Ebsm, Hdd. unfold lhC_fs. rewrite Hdd. cbn [lh_dd_fs dd_ox lh_dd_ts].
rewrite Hhb in F10.
rewrite Hpar1, (g4_fp_adj h).
assert (Elxb: lc_lxb c = ExBlock.x_lxb ExHuf.xhuf (d_ent XS (zs_dc XS zi))).
{ rewrite HCx. change (tabs_lxb (c3_tabs k1)) with (tabs_lxb (w_tabs w)). exact Hz10. }
rewrite Elxb, Hdid0. cbn [dd_ox].
pose proof Hbnd as (Bst & Bbt & Bexp & Brle & Bo1 & Bo2 & Bmb & Bml & _ & _ & _ & _ & _).
rewrite F10 in Bst, Bbt, Bexp, Brle. rewrite F6, F7 in Bo1. rewrite F7 in Bo2.
(* the buffers *)
assert (Hbufs: sf_inSize s3 = zs_inbs XS (g4_z2 zi h) /\ sf_outSize s3 = zs_outbs XS (g4_z2 zi h) /\
   sublist (zs_inbs XS (g4_z2 zi h)) (zs_inbs XS (g4_z2 zi h) + zs_outbs XS (g4_z2 zi h)) (sf_ring s3) =
   zbytes (zs_mem XS (g4_z2 zi h))).
{ revert Hbuf3 F12. match goal with |- (if ?b then _ else _) -> _ => destruct b end;
    intros (B1 & B2 & B3) (G1 & G2 & G3); rewrite G1, G2, G3.
  - auto.
  - rewrite B3. split; [exact B1 | split; [exact B2 |]].
    change (sf_ring (c3_s k3)) with (sf_ring (w_sx w)). exact Hz9. }
clear Hbuf3 F12.
change (sf_inPos (c3_s k3)) with (sf_inPos (c3_s (w_k w))) in Hd_inPos. rewrite Hip0 in Hd_inPos.
change (sf_outStart (c3_s k3)) with (sf_outStart (c3_s (w_k w))) in Hd_os. rewrite Hos0 in Hd_os.
change (sf_outEnd (c3_s k3)) with (sf_outEnd (c3_s (w_k w))) in Hd_oe. rewrite Hoe0 in Hd_oe.
change (sf_hostage (c3_s k3)) with (sf_hostage (c3_s (w_k w))) in Hd_host. rewrite Hhost in Hd_host.
change (sf_nfp (c3_s k3)) with (sf_nfp (w_sx w)) in Hd_nfp. rewrite Hz6 in Hd_nfp.
rewrite Ezinp in F5. rewrite Ezost in F6. rewrite Ezoen in F7. rewrite Ezhost in F9.
destruct (is_skippable_magic (le_field hb 0 4)) eqn:Es.
- assert (Eft: (fh_frameType h =? 1) = true) by (apply Z.eqb_eq, Hsk; reflexivity). rewrite Eft.
  unfold g4_d1 in F10. rewrite Es in F10. cbv zeta in F10.
  unfold g4_d1 in Bst, Bbt, Bexp, Brle. rewrite Es in Bst, Bbt, Bexp, Brle.
  cbn [d_goto d_begin d_stage d_btype d_expected d_rle] in Bst, Bbt, Bexp, Brle.
  rewrite Ezoen in Bo2. destruct Hbufs as (Hb1 & Hb2 & Hb3).
  unfold zrel_end, zrel. rewrite F1, F3, F5, F6, F7, F8, F9, F10, F11.
  cbn [sf_strip sf_stage sf_inSize sf_outSize sf_over sf_nfp sf_ring sf_inPos sf_outStart sf_outEnd sf_hostage
       sf_outBuff sf_lhSize sf_hbuf].
  rewrite Hd_stage, Hb1, Hb2, Hb3, Hov3, Hd_nfp, Hd_inPos, Hd_os, Hd_oe, Hd_host.
  split; [| split; [intros _; split; [reflexivity | intros _; reflexivity] |
                    split; [unfold ZDSS_read, ZDSS_init; intros; lia | repeat split; auto]]].
  split; [reflexivity |]. split; [unfold ZDSS_read; lia |].
  split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
  split; [exact Bml |]. split; [exact Bmb |]. split; [reflexivity |]. split; [reflexivity |].
  split; [unfold ZDSS_read, ZDSS_loadHeader; intros; lia |].
  intros _. split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |]. split; [lia |].
  split; [lia |]. split; [reflexivity |]. split; [left; reflexivity |].
  split; [| unfold ZDSS_read, ZDSS_load; intros; lia].
  + eexists. split; [reflexivity |].
    unfold drel. cbn [d_goto d_begin d_stage d_btype d_expected d_rle d_prev d_pfx d_ds d_de d_out d_check d_ent].
    split; [reflexivity |].
    split; [cbn [g4_fp fh_contentSize]; lia |].
    split; [cbn [g4_fp fh_blockSizeMax]; unfold ZSTD_BLOCKSIZE_MAX in Gbs2; rep_lia |].
    split; [cbn [g4_fp fh_checksumFlag]; destruct Gck as [E|E]; rewrite E; rep_lia |].
    split; [exact Bst |]. split; [rep_lia |]. split; [exact Bbt |]. split; [rep_lia |].
    split; [intros x [E|[E|[E|E]]]; discriminate |].
    split; [apply g4_xh_good_begin |].
    split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
    split; [unfold DS_skipFrame, DS_decompressBlock, DS_decompressLastBlock; intros [E|E]; discriminate |].
    unfold DS_skipFrame, DS_decodeBlockHeader, DS_checkChecksum; intros; lia.
- assert (Eft: (fh_frameType h =? 1) = false) by (apply Z.eqb_neq; intros E; apply Hsk in E; discriminate).
  rewrite Eft.
  change (negb (dp_ignore dparams_dflt =? 1)) with true. rewrite andb_true_r.
  unfold g4_d1 in F10. rewrite Es in F10. cbv zeta in F10.
  unfold g4_d1 in Bst, Bbt, Bexp, Brle. rewrite Es in Bst, Bbt, Bexp, Brle.
  cbn [d_goto d_set_check d_begin d_stage d_btype d_expected d_rle] in Bst, Bbt, Bexp, Brle.
  rewrite Ezoen in Bo2. destruct Hbufs as (Hb1 & Hb2 & Hb3).
  unfold zrel_end, zrel. rewrite F1, F3, F5, F6, F7, F8, F9, F10, F11.
  cbn [sf_strip sf_stage sf_inSize sf_outSize sf_over sf_nfp sf_ring sf_inPos sf_outStart sf_outEnd sf_hostage
       sf_outBuff sf_lhSize sf_hbuf].
  rewrite Hd_stage, Hb1, Hb2, Hb3, Hov3, Hd_nfp, Hd_inPos, Hd_os, Hd_oe, Hd_host.
  split; [| split; [intros _; split; [reflexivity | intros _; reflexivity] |
                    split; [unfold ZDSS_read, ZDSS_init; intros; lia | repeat split; auto]]].
  split; [reflexivity |]. split; [unfold ZDSS_read; lia |].
  split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
  split; [exact Bml |]. split; [exact Bmb |]. split; [reflexivity |]. split; [reflexivity |].
  split; [unfold ZDSS_read, ZDSS_loadHeader; intros; lia |].
  intros _. split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |]. split; [lia |].
  split; [lia |]. split; [reflexivity |]. split; [left; reflexivity |].
  split; [| unfold ZDSS_read, ZDSS_load; intros; lia].
  + eexists. split; [reflexivity |].
    unfold drel.
    cbn [d_goto d_set_check d_begin d_stage d_btype d_expected d_rle d_prev d_pfx d_ds d_de d_out d_check d_ent].
    split; [reflexivity |].
    split; [cbn [g4_fp fh_contentSize]; lia |].
    split; [cbn [g4_fp fh_blockSizeMax]; unfold ZSTD_BLOCKSIZE_MAX in Gbs2; rep_lia |].
    split; [cbn [g4_fp fh_checksumFlag]; destruct Gck as [E|E]; rewrite E; rep_lia |].
    split; [exact Bst |]. split; [rep_lia |]. split; [exact Bbt |]. split; [rep_lia |].
    split; [intros x [E|[E|[E|E]]]; discriminate |].
    split; [apply g4_xh_good_begin |].
    split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
    split; [unfold DS_decodeBlockHeader, DS_decompressBlock, DS_decompressLastBlock; intros [E|E]; discriminate |].
    intros _. split; [reflexivity |]. split; [constructor |]. split; [reflexivity |].
    split; [intros E; cbn [fs_xxh fsu_fParams fsu_stage fsu_expected fsu_processedCSize fsu_xxh]; rewrite E; reflexivity |].
    repeat split; reflexivity.
Qed.

End CM_LH3G4X_1.
