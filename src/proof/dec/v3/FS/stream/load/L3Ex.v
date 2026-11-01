(* FS3 streaming, case zdss_load: the exact claim (S3Main.ex_call, ex_err) at the exits of the case, as plain lemmas
   the VST pieces use.  At the case's start the model's loop is at a state zi (S3XKit.ex_call_go) whose image the
   fields are (S3XRel.zrel); its iteration is ExStream.st_load:
   - the input ends before the unit is complete: LStop at the state with the bytes loaded (ld_x_stop);
   - the unit is complete: ExStream.z_dcs on inBuff, as ZSTD_decompressContinueStream does it (S3Specs.cont_exact):
     an error of the call is the model's LErr (ld_x_err), a success its LNext (ld_x_next).
   Only the stream's exact configuration (Spec_api6.fresh_cfg: buffered, no dictionary) is concerned. *)
Require Import Zstd.proof.dec.v3.FS.stream.load.L3Stmts Zstd.proof.dec.v3.FS.stream.S3XKit.
Require Import Zstd.proof.model.ExCall Zstd.proof.model.ExStreamFacts Zstd.proof.model.ExStreamBnd.
Require Import Zstd.proof.model.ExStream.
Require Zstd.proof.model.ExHuf Zstd.proof.model.ExBlock Zstd.proof.model.Exact.

Section CM_L3Ex_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.

Local Open Scope Z_scope.

(* byte lists are determined by their cells *)
Lemma ldx_zbytes_inj (a b: list Z) : bytes_ok a -> bytes_ok b -> zbytes a = zbytes b -> a = b.
Proof.
  intros Ha. revert b. induction Ha as [| x a Hx Ha IH]; intros b Hb E; destruct b as [| y b]; try discriminate.
  - reflexivity.
  - inversion Hb as [| ? ? Hy Hb']; subst. unfold is_byte in Hx, Hy.
    pose proof (f_equal (fun c => match c with Vint i :: _ => Int.unsigned i | _ => 0 end) E) as E1.
    pose proof (f_equal (@tl val) E) as E2. cbn [map] in E1. simpl in E2.
    rewrite !Int.unsigned_repr in E1 by rep_lia. subst y.
    f_equal. apply IH; auto.
Qed.

Lemma ldx_vint_eq (x y: Z) : 0 <= x <= Int.max_unsigned -> 0 <= y <= Int.max_unsigned ->
  Vint (Int.repr x) = Vint (Int.repr y) -> x = y.
Proof.
  intros Hx Hy E. assert (E1: Int.repr x = Int.repr y) by congruence.
  apply (f_equal Int.unsigned) in E1. rewrite !Int.unsigned_repr in E1 by rep_lia. exact E1.
Qed.

(* what the case reads of the frame state relation (S3XRel.drel) *)
Lemma ldx_drel_parts (fh: frame_header) (d: dstate XS) (ob: val) (fs: fstate) (ts: tstate) :
  drel fh d ob fs ts ->
  0 <= d_stage XS d <= DS_skipFrame /\ 0 <= d_expected XS d <= Int64.max_unsigned /\ ts_x ts = d_ent XS d /\
  fs_stage fs = Vint (Int.repr (d_stage XS d)) /\ fs_expected fs = vlong (d_expected XS d).
Proof. unfold drel. tauto. Qed.

(* the bytes delivered in this call fit in the caller's output room (S3XKit.ex_loop_next, ex_loop_stop) *)
Lemma ld_dl_room (a: dsa) (k: cst3) (sv: sview) (ipc opc: Z) (oc: list val) (dl: list Z) :
  call_inv a k sv ipc opc oc dl -> Zlength dl <= a_xroom a.
Proof.
  intros (_ & Hopc & _ & _ & Hdl & _). unfold a_xroom. lia.
Qed.

(* the loop state at the case's start *)
Definition ld_w0 (k0: cst3) (sv: sview) (ipc opc: Z) (oc: list val) (dl: list Z) : lw :=
  {| w_smw := 1; w_k := k0; w_sv := sv; w_ipc := ipc; w_opc := opc; w_oc := oc; w_dl := dl |}.

(* the model's state at the start of the case: stage zdss_load, expected and inPos as the fields hold them, a
   skippable frame exactly when the view says so, no DDict *)
Lemma ld_x_go (a: dsa) (k0: cst3) (sv: sview) (ipc opc: Z) (oc: list val) (dl: list Z) (E: Z) :
  call_inv a k0 sv ipc opc oc dl -> sf_stage (c3_s k0) = zdss_load ->
  fs_expected (c3_fs k0) = vlong E -> 0 <= E < 2 ^ 32 ->
  ex_call a (ld_w0 k0 sv ipc opc oc dl) -> fresh_cfg (a_st a) ->
  exists z0 zi f ts,
    ex_loop a z0 zi f (ipc - a_ipos a) dl /\ zrel zi (sf_strip (c3_s k0)) (c3_fs k0) (c3_tabs k0) /\
    c3_tabs k0 = TInit None ts /\ drel (zs_fp XS zi) (zs_dc XS zi) (sf_outBuff (c3_s k0)) (c3_fs k0) ts /\
    zs_stage XS zi = ZDSS_load /\ d_expected XS (zs_dc XS zi) = E /\ zs_inpos XS zi = fp_inpos (sv_fp sv) /\
    (d_stage XS (zs_dc XS zi) = DS_skipFrame <-> is_skip (sv_fp sv) = true) /\ sv_dd sv = None.
Proof.
  intros Hinv Hst HE HE0 Hx Hf.
  destruct (ex_call_go a _ Hx eq_refl Hf) as (z0 & zi & f & Hl & Hz).
  assert (Hzr: zrel zi (sf_strip (c3_s k0)) (c3_fs k0) (c3_tabs k0)).
  { destruct Hz as [(_ & _ & _ & H)|(H & _)]; exact H. }
  pose proof Hinv as Hinv'.
  destruct Hinv' as (_&_&_&_&_&_&_&_&_&_&_&_&Hcore&_).
  destruct (load_facts _ _ _ _ _ Hcore Hst) as (E' & fst & HE' & HP & HPE & HE32 & Hfst & Hfst7 & Hskip & HEin & [ts' Hts'] & Hib).
  rewrite HE in HE'. apply vlong_eq in HE'; [|lia|lia]. subst E'.
  pose proof Hzr as Hzr'.
  destruct Hzr' as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10 & Z11 & Z12).
  cbn [sf_strip sf_stage sf_inSize sf_outSize sf_over sf_nfp sf_ring sf_inPos sf_outStart sf_outEnd sf_hostage
       sf_outBuff] in *.
  assert (Hzs: zs_stage XS zi = ZDSS_load) by (rewrite <- Z1, Hst; reflexivity).
  destruct (Z12 ltac:(rewrite Hzs; unfold ZDSS_read, ZDSS_load; lia))
    as (Hip & Hos & Hoe & Ho1 & Ho2 & Hh & Hh01 & (ts & Ht & Hd) & Hld).
  destruct Hl as (Hr0 & Hi0 & Hii & Hp & Hl).
  pose proof Hd as Hd'.
  destruct (ldx_drel_parts _ _ _ _ _ Hd') as (D5 & D6 & D10 & D12 & D13).
  assert (HdE: d_expected XS (zs_dc XS zi) = E) by (rewrite D13 in HE; apply vlong_eq in HE; rep_lia).
  assert (Hds: d_stage XS (zs_dc XS zi) = fst).
  { rewrite D12 in Hfst. apply ldx_vint_eq in Hfst; [exact Hfst| |]; unfold DS_skipFrame in D5; rep_lia. }
  pose proof Hii as Hii'. destruct Hii' as (_ & _ & (Hil & _) & _).
  specialize (Hil Hzs). rewrite HdE in Hil.
  assert (HzP: zs_inpos XS zi = fp_inpos (sv_fp sv)) by (rewrite HP in Hip; apply vlong_eq in Hip; lia).
  exists z0, zi, f, ts.
  split; [unfold ex_loop; cbn [w_ipc w_dl ld_w0] in *; tauto|]. split; [exact Hzr|]. split; [exact Ht|]. split; [exact Hd|].
  split; [exact Hzs|]. split; [exact HdE|]. split; [exact HzP|].
  split; [rewrite Hds; unfold DS_skipFrame; rewrite <- Hskip; unfold ds_skipFrame; tauto|].
  rewrite Ht in Hts'. inversion Hts' as [[Hox Hts]]. destruct (sv_dd sv); [discriminate|reflexivity].
Qed.

(* ExStream.st_load once expected and inPos are known: the check of toLoad against the input buffer never fails
   (a Zstandard frame's unit fits in inBuff), loaded = L bytes are appended to inBuff, then LStop or the call *)
Lemma ldx_st_load (inp: list Z) (z: zstate_x) (ip: Z) (dl: list Z) (E P L: Z) :
  d_expected XS (zs_dc XS z) = E -> zs_inpos XS z = P ->
  (d_stage XS (zs_dc XS z) <> DS_skipFrame -> E <= zs_inbs XS z) ->
  L = Z.min (E - P) (Zlength inp - ip) ->
  let ib := if d_stage XS (zs_dc XS z) =? DS_skipFrame then zs_ibuf XS z else zs_ibuf XS z ++ slice inp ip L in
  st_load XS Exact.xblock inp z ip dl =
    if L <? E - P then LStop XS (z_in XS z ib (P + L)) (ip + L) dl
    else match z_dcs XS Exact.xblock (z_in XS (z_in XS z ib (P + L)) nil 0)
                 (if d_stage XS (zs_dc XS z) =? DS_skipFrame then nil else ib) E with
         | None => LErr XS
         | Some z2 => LNext XS z2 (ip + L) dl
         end.
Proof.
  intros HE HP Hin HL ib. unfold st_load. cbv zeta. rewrite HE, HP, <- HL.
  destruct (Z.eqb_spec (d_stage XS (zs_dc XS z)) DS_skipFrame) as [Hs|Hs].
  - reflexivity.
  - specialize (Hin Hs). cbn [negb andb].
    replace (E - P >? zs_inbs XS z - P) with false by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
    reflexivity.
Qed.

Lemma ldx_slice (l: list Z) (lo hi i k: Z) :
  0 <= lo -> 0 <= i -> 0 <= k -> lo + i + k <= hi -> hi <= Zlength l ->
  slice (sublist lo hi l) i k = sublist (lo + i) (lo + i + k) l.
Proof.
  intros H1 H2 H3 H4 H5. unfold slice.
  replace (firstn (Z.to_nat k) (skipn (Z.to_nat i) (sublist lo hi l))) with (sublist i (i + k) (sublist lo hi l))
    by (rewrite firstn_skipn_comm; unfold sublist at 1; f_equal; f_equal; lia).
  rewrite sublist_sublist by lia. f_equal; lia.
Qed.

(* the stream buffer after the copy of L input bytes at inPos = P (none for a skippable frame): the ring's output
   part is untouched (the unit fits in inBuff), the input part holds the bytes loaded so far *)
Lemma ldx_ring_load (ring: list val) (ibs: list Z) (fp: fprog) (P L ipc inS outS: Z) (ibuf mem: list Z) :
  Zlength ring = inS + outS -> 0 <= P -> 0 <= L -> (is_skip fp = false -> P + L <= inS) -> 0 <= ipc ->
  ipc + L <= Zlength ibs -> 0 <= outS ->
  sublist inS (inS + outS) ring = zbytes mem ->
  sublist inS (inS + outS) (ring_load fp ring P ibs ipc L) = zbytes mem /\
  (is_skip fp = false -> Zlength ibuf = P -> sublist 0 P ring = zbytes ibuf ->
     sublist 0 (P + L) (ring_load fp ring P ibs ipc L) = zbytes (ibuf ++ sublist ipc (ipc + L) ibs)).
Proof.
  intros Hrl HP HL Hin Hipc Hibs Hout Hm. unfold ring_load. destruct (is_skip fp) eqn:Hk.
  - split; [exact Hm | intros H; discriminate].
  - specialize (Hin eq_refl).
    assert (Hzl: Zlength (zbytes ibs) = Zlength ibs) by (rewrite Zlength_map; reflexivity).
    split.
    + rewrite <- Hm. apply sublist_skip_eq with (n := P + L); [lia|]. apply skipn_copy_cells; lia.
    + intros _ Hb1 Hb3. rewrite sublist_copy_cells_pre by lia. rewrite Hb3, map_app, sublist_map. reflexivity.
Qed.

(* the input runs out before the unit is complete: the loop stops (someMoreWork = 0) at the state with the bytes
   loaded *)
Lemma ld_x_stop (a: dsa) (k0: cst3) (sv: sview) (ipc opc: Z) (oc: list val) (dl: list Z) (E L: Z) :
  dsa_ok a -> call_inv a k0 sv ipc opc oc dl -> sf_stage (c3_s k0) = zdss_load ->
  fs_expected (c3_fs k0) = vlong E -> 0 <= E < 2 ^ 32 ->
  L = Z.min (E - fp_inpos (sv_fp sv)) (a_isz a - ipc) -> L < E - fp_inpos (sv_fp sv) ->
  Zlength (sf_ring (c3_s k0)) = sf_inSize (c3_s k0) + sf_outSize (c3_s k0) ->
  ex_call a (ld_w0 k0 sv ipc opc oc dl) ->
  ex_call a {| w_smw := 0;
               w_k := k_load k0 (fp_inpos (sv_fp sv) + L)
                        (ring_load (sv_fp sv) (sf_ring (c3_s k0)) (fp_inpos (sv_fp sv)) (a_ibs a) ipc L);
               w_sv := sv_load sv (sublist ipc (ipc + L) (a_ibs a)); w_ipc := ipc + L; w_opc := opc; w_oc := oc;
               w_dl := dl |}.
Proof.
  intros Ha Hinv Hst HE HE0 HL Hlt Hrl Hx.
  apply ex_call_stop_mk; [reflexivity|]. intros Hf.
  destruct (ld_x_go a k0 sv ipc opc oc dl E Hinv Hst HE HE0 Hx Hf)
    as (z0 & zi & f & ts & Hl & Hz & Ht & Hd & Hzs & HdE & HzP & Hsk & Hdd).
  (* the output room (a premise of S3XKit.ex_loop_next / ex_loop_stop in the shared batch 2) *)
  pose proof (ld_dl_room a k0 sv ipc opc oc dl Hinv) as Hdlr.
  set (P := fp_inpos (sv_fp sv)) in *.
  pose proof Hinv as Hinv'.
  destruct Hinv' as (Hipc & _&_&_&_&_&_&_&_&_&_&_&Hcore&_).
  destruct (load_facts _ _ _ _ _ Hcore Hst) as (E' & fst & HE' & HP & HPE & HE32 & Hfst & Hfst7 & Hskip & HEin & _ & Hib).
  rewrite HE in HE'. apply vlong_eq in HE'; [|lia|lia]. subst E'. fold P in HP, HPE, HEin.
  destruct Ha as (_&_&_&_&_&_&_&_&_&_&_&_&Hipos&Hisz&Hlibs&Hbibs&_).
  pose proof Hz as Hz'.
  destruct Hz' as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10 & Z11 & Z12).
  cbn [sf_strip sf_stage sf_inSize sf_outSize sf_over sf_nfp sf_ring sf_inPos sf_outStart sf_outEnd sf_hostage
       sf_outBuff] in *.
  destruct (Z12 ltac:(rewrite Hzs; unfold ZDSS_read, ZDSS_load; lia))
    as (Hip & Hos & Hoe & Ho1 & Ho2 & Hh & Hh01 & _ & Hld).
  assert (Hinp: Zlength (a_xin a) = a_isz a - a_ipos a)
    by (clear - Hipos Hlibs; unfold a_xin; rewrite Zlength_sublist; lia).
  assert (HL': L = Z.min (E - P) (Zlength (a_xin a) - (ipc - a_ipos a))) by (rewrite Hinp, HL; f_equal; ring).
  assert (Hsl: slice (a_xin a) (ipc - a_ipos a) L = sublist ipc (ipc + L) (a_ibs a)).
  { unfold a_xin.
    rewrite ldx_slice by (clear - HL Hipc Hipos Hlibs HPE; destruct (Z.min_spec (E - P) (a_isz a - ipc)); lia).
    f_equal; ring. }
  assert (Hin: d_stage XS (zs_dc XS zi) <> DS_skipFrame -> E <= zs_inbs XS zi).
  { intros Hn. rewrite <- Z3. apply HEin. destruct (is_skip (sv_fp sv)) eqn:Hk; [|reflexivity].
    exfalso. apply Hn. apply Hsk. reflexivity. }
  pose proof (ldx_st_load (a_xin a) zi (ipc - a_ipos a) dl E P L HdE HzP Hin HL') as Hsl1.
  cbv zeta in Hsl1. rewrite Hsl in Hsl1.
  replace (L <? E - P) with true in Hsl1 by (symmetry; apply Z.ltb_lt; clear - Hlt; lia).
  set (ib := if d_stage XS (zs_dc XS zi) =? DS_skipFrame then zs_ibuf XS zi
             else zs_ibuf XS zi ++ sublist ipc (ipc + L) (a_ibs a)) in Hsl1.
  assert (Hone: one_iter_x (a_xin a) (a_xroom a) zi (ipc - a_ipos a) dl =
                LStop XS (z_in XS zi ib (P + L)) (ipc - a_ipos a + L) dl).
  { unfold one_iter_x. rewrite one_iter_load by exact Hzs. exact Hsl1. }
  assert (Hbin: bytes_ok (a_xin a)) by (unfold a_xin, bytes_ok in *; apply Forall_sublist; exact Hbibs).
  destruct (ex_loop_stop a z0 zi f (ipc - a_ipos a) dl _ _ _ Hbin ltac:(clear - Hinp Hipc Hipos; lia) Hdlr Hl Hone) as (Hal & Hz1).
  destruct Hl as (Hr0 & Hi0 & _).
  exists z0, (z_in XS zi ib (P + L)).
  split; [exact Hr0|]. split; [exact Hi0|]. split; [exact Hz1|].
  split; [cbn [w_ipc w_dl]; replace (ipc + L - a_ipos a) with (ipc - a_ipos a + L) by ring; exact Hal|].
  assert (HL0: 0 <= L) by (clear - HL HPE Hipc; rewrite HL; lia).
  assert (Hring: sublist (zs_inbs XS zi) (zs_inbs XS zi + zs_outbs XS zi)
                   (ring_load (sv_fp sv) (sf_ring (c3_s k0)) P (a_ibs a) ipc L) = zbytes (zs_mem XS zi) /\
                 (d_stage XS (zs_dc XS zi) <> DS_skipFrame ->
                    Zlength ib = P + L /\ bytes_ok ib /\
                    sublist 0 (P + L) (ring_load (sv_fp sv) (sf_ring (c3_s k0)) P (a_ibs a) ipc L) = zbytes ib)).
  { assert (HPL: is_skip (sv_fp sv) = false -> P + L <= zs_inbs XS zi)
      by (intros Hk; specialize (HEin Hk); clear - HEin HL Hlt Z3; rewrite <- Z3; lia).
    rewrite <- Z3, <- Z4 in Z9 |- *. rewrite <- Z3 in HPL.
    destruct (ldx_ring_load (sf_ring (c3_s k0)) (a_ibs a) (sv_fp sv) P L ipc (sf_inSize (c3_s k0))
                (sf_outSize (c3_s k0)) (zs_ibuf XS zi) (zs_mem XS zi) Hrl ltac:(clear - HPE; lia) HL0 HPL
                ltac:(clear - Hipc Hipos; lia) ltac:(clear - HL Hipc Hlibs HL0; rewrite Hlibs; rewrite HL in *; lia)
                ltac:(clear - Z4 Z7; rewrite Z4, <- Z7; apply Zlength_nonneg) Z9) as [Hr1 Hr2].
    split; [exact Hr1|]. intros Hn.
    assert (Hk: is_skip (sv_fp sv) = false)
      by (destruct (is_skip (sv_fp sv)) eqn:Hk; [exfalso; apply Hn, Hsk; reflexivity | reflexivity]).
    destruct (Hld Hzs Hn) as (Hb1 & Hb2 & Hb3). rewrite HzP in Hb1, Hb3.
    assert (Hib': ib = zs_ibuf XS zi ++ sublist ipc (ipc + L) (a_ibs a))
      by (unfold ib; rewrite (proj2 (Z.eqb_neq _ _) Hn); reflexivity).
    rewrite Hib'. split; [rewrite Zlength_app, Zlength_sublist; clear - Hb1 HL0 HL Hipc Hipos Hlibs HPE; rewrite HL in *; lia|].
    split; [apply Forall_app; split; [exact Hb2| apply Forall_sublist; exact Hbibs]|].
    exact (Hr2 Hk Hb1 Hb3). }
  destruct Hring as [Hr1 Hr2].
  destruct (ldx_drel_parts _ _ _ _ _ Hd) as (_ & _ & _ & D12 & D13).
  unfold zrel_end, zrel, w_sx, w_fs, w_tabs, k_load, c3_with_s.
  cbn [w_k c3_s c3_fs c3_tabs sf_strip s_load sf_stage sf_inSize sf_outSize sf_over sf_nfp sf_ring sf_inPos
       sf_outStart sf_outEnd sf_hostage sf_outBuff sf_lhSize sf_hbuf z_in zs_stage zs_inbs zs_outbs zs_over zs_nfp
       zs_mem zs_dc zs_hbuf zs_inpos zs_ostart zs_oend zs_host zs_fp zs_ibuf].
  refine (conj (conj Z1 (conj Z2 (conj Z3 (conj Z4 (conj Z5 (conj Z6 (conj Z7 (conj Z8 (conj Hr1 (conj Z10
            (conj _ _)))))))))))
          (conj _ (conj _ (conj eq_refl (conj Hos (conj Hoe (conj Hh Hh01))))))).
  - intros H; rewrite Hzs in H; unfold ZDSS_load, ZDSS_loadHeader in H; discriminate.
  - intros _. refine (conj eq_refl (conj Hos (conj Hoe (conj Ho1 (conj Ho2 (conj Hh (conj Hh01
             (conj (ex_intro _ ts (conj Ht Hd)) _)))))))).
    intros _ Hn. exact (Hr2 Hn).
  - intros _. split; [exact D13 | intros _; exact D12].
  - intros H; rewrite Hzs in H; unfold ZDSS_load, ZDSS_init in H; discriminate.
Qed.

(* a skippable frame's content is not read: ZSTD_decompressContinue at DS_skipFrame does not look at src *)
Lemma ldx_dcont_skip (fh: frame_header) (d: dstate XS) (mem: list Z) (dst cap: Z) (u: list Z) (n: Z) :
  d_stage XS d = DS_skipFrame ->
  d_continue XS Exact.xblock fh d mem dst cap u n = d_continue XS Exact.xblock fh d mem dst cap nil n.
Proof.
  intros H. assert (Hs: d_stage XS (d_continuity XS d dst cap) = DS_skipFrame)
    by (unfold d_continuity; destruct (_ && _)%bool; exact H).
  unfold d_continue. cbv zeta. rewrite Hs. reflexivity.
Qed.

(* the unit is complete: ZSTD_decompressContinueStream on inBuff is the model's z_dcs (S3Specs.cont_exact); an error
   is the model's LErr, a success its LNext at the state the fields after the call represent *)
Lemma ld_x_unit (a: dsa) (k0: cst3) (sv: sview) (ipc opc: Z) (oc: list val) (dl: list Z) (E L ostart rr: Z)
    (oc': list val) (fs': fstate) (tabs': option tstate) (ts': tstate) :
  dsa_ok a -> call_inv a k0 sv ipc opc oc dl -> sf_stage (c3_s k0) = zdss_load ->
  fs_expected (c3_fs k0) = vlong E -> 0 <= E < 2 ^ 32 ->
  L = Z.min (E - fp_inpos (sv_fp sv)) (a_isz a - ipc) -> L = E - fp_inpos (sv_fp sv) ->
  Zlength (sf_ring (c3_s k0)) = sf_inSize (c3_s k0) + sf_outSize (c3_s k0) ->
  c3_tabs k0 = TInit (dd_ox (sv_dd sv)) ts' ->
  sf_outStart (c3_s k0) = vlong ostart -> 0 <= ostart <= sf_outSize (c3_s k0) -> 0 <= sf_inSize (c3_s k0) ->
  let ring1 := ring_load (sv_fp sv) (sf_ring (c3_s k0)) (fp_inpos (sv_fp sv)) (a_ibs a) ipc L in
  let u := ld_u sv (a_ibs a) ipc L in
  (is_skip (sv_fp sv) = false -> inwin_ok (i_bf (c3_s k0) ring1 u)) ->
  (sv_dd sv = None -> cont_exact (c3_fs k0) ts' (o_bf (c3_s k0) ring1 ostart sv) u E rr oc' fs' tabs') ->
  ex_call a (ld_w0 k0 sv ipc opc oc dl) -> fresh_cfg (a_st a) ->
  let rd := andb (rr =? 0) (negb (is_skip (sv_fp sv))) in
  let s2 := s_cont (c3_s k0) (if rd then zdss_read else zdss_flush)
              (if rd then sf_outEnd (c3_s k0) else vlong (ostart + rr))
              (sublist 0 (sf_inSize (c3_s k0)) ring1 ++ oc') in
  exists z0 zi f, ex_loop a z0 zi f (ipc - a_ipos a) dl /\
    ((is_error_code rr = true /\ one_iter_x (a_xin a) (a_xroom a) zi (ipc - a_ipos a) dl = LErr XS) \/
     (is_error_code rr = false /\ exists z2 f1, ex_loop a z0 z2 f1 (ipc + L - a_ipos a) dl /\
        forall lxb, zrel_end z2 (sf_strip s2) fs' (tabs_of (sv_dd sv) lxb tabs'))).
Proof.
  intros Ha Hinv Hst HE HE0 HL HLE Hrl Hts' Hos0 Hos1 Hin0 ring1 u Hiw Hce Hx Hf.
  destruct (ld_x_go a k0 sv ipc opc oc dl E Hinv Hst HE HE0 Hx Hf)
    as (z0 & zi & f & ts & Hl & Hz & Ht & Hd & Hzs & HdE & HzP & Hsk & Hdd).
  (* the output room (a premise of S3XKit.ex_loop_next / ex_loop_stop in the shared batch 2) *)
  pose proof (ld_dl_room a k0 sv ipc opc oc dl Hinv) as Hdlr.
  rewrite Ht, Hdd in Hts'. cbn [dd_ox option_map] in Hts'. inversion Hts'; subst ts'. clear Hts'.
  specialize (Hce Hdd).
  set (P := fp_inpos (sv_fp sv)) in *.
  pose proof Hinv as Hinv'.
  destruct Hinv' as (Hipc & _&_&_&_&_&_&_&_&_&_&_&Hcore&_).
  destruct (load_facts _ _ _ _ _ Hcore Hst) as (E' & fst & HE' & HP & HPE & HE32 & Hfst & Hfst7 & Hskip & HEin & _ & Hib).
  rewrite HE in HE'. apply vlong_eq in HE'; [|lia|lia]. subst E'. fold P in HP, HPE, HEin.
  assert (Hsz: sf_inSize (c3_s k0) + sf_outSize (c3_s k0) <= 2 ^ 32) by (unfold c_core in Hcore; tauto).
  destruct Ha as (_&_&_&_&_&_&_&_&_&_&_&_&Hipos&Hisz&Hlibs&Hbibs&_).
  pose proof Hz as Hz'.
  destruct Hz' as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10 & Z11 & Z12).
  cbn [sf_strip sf_stage sf_inSize sf_outSize sf_over sf_nfp sf_ring sf_inPos sf_outStart sf_outEnd sf_hostage
       sf_outBuff] in *.
  destruct (Z12 ltac:(rewrite Hzs; unfold ZDSS_read, ZDSS_load; lia))
    as (Hip & Hos & Hoe & Ho1 & Ho2 & Hh & Hh01 & _ & Hld).
  assert (Hskb: (d_stage XS (zs_dc XS zi) =? DS_skipFrame) = is_skip (sv_fp sv)).
  { destruct (is_skip (sv_fp sv)) eqn:Hk; [apply Z.eqb_eq, Hsk; reflexivity|].
    apply Z.eqb_neq. intros He. apply Hsk in He. congruence. }
  assert (HL0: 0 <= L) by (clear - HLE HPE; lia).
  assert (Hinp: Zlength (a_xin a) = a_isz a - a_ipos a)
    by (clear - Hipos Hlibs; unfold a_xin; rewrite Zlength_sublist; lia).
  assert (HL': L = Z.min (E - P) (Zlength (a_xin a) - (ipc - a_ipos a))) by (rewrite Hinp, HL; f_equal; ring).
  assert (Hsl: slice (a_xin a) (ipc - a_ipos a) L = sublist ipc (ipc + L) (a_ibs a)).
  { unfold a_xin.
    rewrite ldx_slice by (clear - HL Hipc Hipos Hlibs HPE; destruct (Z.min_spec (E - P) (a_isz a - ipc)); lia).
    f_equal; ring. }
  assert (Hin: d_stage XS (zs_dc XS zi) <> DS_skipFrame -> E <= zs_inbs XS zi).
  { intros Hn. rewrite <- Z3. apply HEin. destruct (is_skip (sv_fp sv)) eqn:Hk; [|reflexivity].
    exfalso. apply Hn. apply Hsk. reflexivity. }
  pose proof (ldx_st_load (a_xin a) zi (ipc - a_ipos a) dl E P L HdE HzP Hin HL') as Hsl1.
  cbv zeta in Hsl1. rewrite Hsl in Hsl1.
  replace (L <? E - P) with false in Hsl1 by (symmetry; apply Z.ltb_ge; clear - HLE; lia).
  set (ib := if d_stage XS (zs_dc XS zi) =? DS_skipFrame then zs_ibuf XS zi
             else zs_ibuf XS zi ++ sublist ipc (ipc + L) (a_ibs a)) in Hsl1.
  (* the stream buffer as loaded *)
  assert (Hring: sublist (zs_inbs XS zi) (zs_inbs XS zi + zs_outbs XS zi) ring1 = zbytes (zs_mem XS zi) /\
                 (d_stage XS (zs_dc XS zi) <> DS_skipFrame ->
                    Zlength ib = P + L /\ bytes_ok ib /\ sublist 0 (P + L) ring1 = zbytes ib)).
  { assert (HPL: is_skip (sv_fp sv) = false -> P + L <= zs_inbs XS zi)
      by (intros Hk; specialize (HEin Hk); clear - HEin HLE Z3; rewrite <- Z3; lia).
    rewrite <- Z3, <- Z4 in Z9 |- *. rewrite <- Z3 in HPL.
    destruct (ldx_ring_load (sf_ring (c3_s k0)) (a_ibs a) (sv_fp sv) P L ipc (sf_inSize (c3_s k0))
                (sf_outSize (c3_s k0)) (zs_ibuf XS zi) (zs_mem XS zi) Hrl ltac:(clear - HPE; lia) HL0 HPL
                ltac:(clear - Hipc Hipos; lia) ltac:(clear - HL Hipc Hlibs HL0; rewrite Hlibs; rewrite HL in *; lia)
                ltac:(clear - Z4 Z7; rewrite Z4, <- Z7; apply Zlength_nonneg) Z9) as [Hr1 Hr2].
    split; [exact Hr1|]. intros Hn.
    assert (Hk: is_skip (sv_fp sv) = false)
      by (destruct (is_skip (sv_fp sv)) eqn:Hk; [exfalso; apply Hn, Hsk; reflexivity | reflexivity]).
    destruct (Hld Hzs Hn) as (Hb1 & Hb2 & Hb3). rewrite HzP in Hb1, Hb3.
    assert (Hib': ib = zs_ibuf XS zi ++ sublist ipc (ipc + L) (a_ibs a))
      by (unfold ib; rewrite (proj2 (Z.eqb_neq _ _) Hn); reflexivity).
    rewrite Hib'. split; [rewrite Zlength_app, Zlength_sublist; clear - Hb1 HL0 HL Hipc Hipos Hlibs HPE; rewrite HL in *; lia|].
    split; [apply Forall_app; split; [exact Hb2| apply Forall_sublist; exact Hbibs]|].
    exact (Hr2 Hk Hb1 Hb3). }
  destruct Hring as [Hr1 Hr2].
  pose proof (zinv_x_bnd zi (proj1 (proj2 (proj2 Hl)))) as Hzb. unfold zbnd_x in Hzb; cbv zeta in Hzb.
  assert (Hoz: ostart = zs_ostart XS zi).
  { rewrite Hos0 in Hos. apply vlong_eq in Hos; [exact Hos| |]; clear - Hos1 Hsz Hin0 Ho1 Ho2 Z4; lia. }
  subst ostart.
  assert (Hcap: oa_cap (o_bf (c3_s k0) ring1 (zs_ostart XS zi) sv) =
                (if d_stage XS (zs_dc XS zi) =? DS_skipFrame then 0 else zs_outbs XS zi - zs_ostart XS zi))
    by (unfold o_bf; cbn [oa_cap]; rewrite Hskb, Z4; reflexivity).
  assert (Hoc: oa_c (o_bf (c3_s k0) ring1 (zs_ostart XS zi) sv) = zbytes (zs_mem XS zi))
    by (unfold o_bf; cbn [oa_c]; rewrite Z3, Z4; exact Hr1).
  assert (Hroom: (d_stage XS (zs_dc XS zi) = DS_decompressBlock \/ d_stage XS (zs_dc XS zi) = DS_decompressLastBlock) ->
     d_btype XS (zs_dc XS zi) = 2 -> oa_cap (o_bf (c3_s k0) ring1 (zs_ostart XS zi) sv) = 0 ->
     d_de XS (zs_dc XS zi) = None).
  { intros Hb Ht2 Hc0. rewrite Hcap in Hc0.
    destruct (d_de XS (zs_dc XS zi)) eqn:Hde; [|reflexivity]. exfalso.
    destruct Hzb as (_&_&_&_&_&_&_&_&_&_&_&Hrm&_).
    assert (Hlt': zs_ostart XS zi < zs_outbs XS zi)
      by (apply Hrm; [rewrite Hzs; unfold ZDSS_read, ZDSS_load; lia | exact Hb | exact Ht2 | congruence]).
    replace (d_stage XS (zs_dc XS zi) =? DS_skipFrame) with false in Hc0
      by (destruct Hb as [Hb|Hb]; rewrite Hb; reflexivity).
    clear - Hlt' Hc0; lia. }
  assert (Hsrc: d_continue XS Exact.xblock (zs_fp XS zi) (zs_dc XS zi) (zs_mem XS zi) (zs_ostart XS zi)
                  (if d_stage XS (zs_dc XS zi) =? DS_skipFrame then 0 else zs_outbs XS zi - zs_ostart XS zi) u E =
                d_continue XS Exact.xblock (zs_fp XS zi) (zs_dc XS zi) (zs_mem XS zi) (zs_ostart XS zi)
                  (if d_stage XS (zs_dc XS zi) =? DS_skipFrame then 0 else zs_outbs XS zi - zs_ostart XS zi)
                  (if d_stage XS (zs_dc XS zi) =? DS_skipFrame then nil else ib) E).
  { destruct (Z.eqb_spec (d_stage XS (zs_dc XS zi)) DS_skipFrame) as [Hs|Hs].
    - apply ldx_dcont_skip; exact Hs.
    - f_equal.
      assert (Hk: is_skip (sv_fp sv) = false)
        by (destruct (is_skip (sv_fp sv)) eqn:Hk; [exfalso; apply Hs, Hsk; reflexivity | reflexivity]).
      destruct (Hr2 Hs) as (Hb1 & Hb2 & Hb3).
      destruct (Hiw Hk) as (_&_&_&_&_&_&Hu2&Hu3). cbn [i_bf iw_sh iw_N iw_c iw_off iw_s] in Hu2, Hu3.
      assert (Hlu: Zlength u = P + L).
      { unfold u, ld_u. rewrite Zlength_app, Zlength_sublist by (clear - HL Hipc Hipos Hlibs HL0; rewrite HL in *; lia).
        assert (Hfl: Zlength (fp_loaded (sv_fp sv)) = P)
          by (unfold P; destruct (sv_fp sv); cbn in Hk |- *; [reflexivity|reflexivity|discriminate|reflexivity]).
        rewrite Hfl. ring. }
      rewrite Hlu, Z.add_0_l, sublist_sublist in Hu3 by (clear - HLE Hin Hs Z3 HPE HL0; rewrite <- Z3 in Hin; specialize (Hin Hs); lia).
      rewrite !Z.add_0_r in Hu3.
      apply ldx_zbytes_inj; [exact Hu2 | exact Hb2 | rewrite <- Hu3, <- Hb3; reflexivity]. }
  pose proof (Hce (zs_fp XS zi) (zs_dc XS zi) (zs_mem XS zi) Hd Hoc Z8 Hroom) as Hcx.
  change (oa_d (o_bf (c3_s k0) ring1 (zs_ostart XS zi) sv)) with (zs_ostart XS zi) in Hcx.
  rewrite Hcap, Hsrc in Hcx.
  unfold z_dcs in Hsl1. cbv zeta in Hsl1. cbn [z_in zs_dc zs_fp zs_mem zs_ostart zs_outbs] in Hsl1.
  assert (Hbin: bytes_ok (a_xin a)) by (unfold a_xin, bytes_ok in *; apply Forall_sublist; exact Hbibs).
  exists z0, zi, f. split; [exact Hl|].
  revert Hsl1 Hcx.
  destruct (d_continue XS Exact.xblock (zs_fp XS zi) (zs_dc XS zi) (zs_mem XS zi) (zs_ostart XS zi)
             (if d_stage XS (zs_dc XS zi) =? DS_skipFrame then 0 else zs_outbs XS zi - zs_ostart XS zi)
             (if d_stage XS (zs_dc XS zi) =? DS_skipFrame then nil else ib) E) as [[[d' mem'] r0]|];
    intros Hsl1 Hcx.
  2: { left. split; [exact Hcx|]. unfold one_iter_x. rewrite one_iter_load by exact Hzs. rewrite Hsl1. reflexivity. }
  destruct Hcx as (Hrr & Hoc' & ts2 & Htabs & Hd2). subst rr oc' tabs'.
  rewrite Hdd. cbn [tabs_of dd_ox option_map].
  rewrite Hskb in Hsl1.
  destruct (ldx_drel_parts _ _ _ _ _ Hd2) as (_ & _ & Hx2 & D12 & D13).
  assert (Hlxb2: ts_lxb ts2 = ExBlock.x_lxb ExHuf.xhuf (d_ent XS d'))
    by (change (ts_lxb ts2) with (ExBlock.x_lxb ExHuf.xhuf (ts_x ts2)); rewrite Hx2; reflexivity).
  pose proof (Zlength_nonneg (zs_mem XS zi)) as Hmn0.
  assert (Hlr1: Zlength (sublist 0 (sf_inSize (c3_s k0)) ring1) = sf_inSize (c3_s k0)).
  { assert (Hl1: Zlength ring1 = sf_inSize (c3_s k0) + sf_outSize (c3_s k0)).
    { unfold ring1, ring_load. destruct (is_skip (sv_fp sv)) eqn:Hk; [exact Hrl|].
      specialize (HEin eq_refl). pose proof (Zlength_nonneg (zs_mem XS zi)) as Hmn.
      rewrite Zlength_copy_cells; [exact Hrl|..];
        clear - HEin HLE HL HPE Hrl Hipc Hipos Hlibs Hin0 Z4 Z7 Hmn; try rewrite Zlength_map; rewrite HL in *; lia. }
    rewrite Zlength_sublist; clear - Hl1 Hin0 Z4 Z7 Hmn0; lia. }
  revert Hsl1. destruct ((r0 =? 0) && negb (is_skip (sv_fp sv)))%bool eqn:Hb; intros Hsl1.
  - (* nothing written: zdss_read *)
    set (z2 := z_stage XS (z_mem XS (z_dc XS (z_in XS (z_in XS zi ib (P + L)) [] 0) d') mem') ZDSS_read).
    assert (Hone: one_iter_x (a_xin a) (a_xroom a) zi (ipc - a_ipos a) dl = LNext XS z2 (ipc - a_ipos a + L) dl)
      by (unfold one_iter_x; rewrite one_iter_load by exact Hzs; rewrite Hsl1; reflexivity).
    destruct (ex_loop_next a z0 zi f (ipc - a_ipos a) dl z2 _ _ Hbin ltac:(clear - Hinp Hipc Hipos; lia) Hdlr Hl Hone)
      as (f1 & Hl1 & Hip1).
    pose proof (zinv_x_bnd z2 (proj1 (proj2 (proj2 Hl1)))) as Hzb2. unfold zbnd_x in Hzb2; cbv zeta in Hzb2.
    destruct Hzb2 as (_&_&_&_&Hb5&Hb6&Hb7&Hb8&_). unfold z2 in Hb5, Hb6, Hb7, Hb8.
    cbn [z_stage z_mem z_dc z_in zs_ostart zs_oend zs_outbs zs_mem] in Hb5, Hb6, Hb7, Hb8.
    apply andb_prop in Hb. destruct Hb as [Hb _]. apply Z.eqb_eq in Hb. subst r0.
    right. split; [reflexivity|]. exists z2, f1.
    split; [replace (ipc + L - a_ipos a) with (ipc - a_ipos a + L) by ring; exact Hl1|]. intros _.
    assert (Hring2: sublist (zs_inbs XS zi) (zs_inbs XS zi + zs_outbs XS zi)
                      (sublist 0 (sf_inSize (c3_s k0)) ring1 ++ zbytes mem') = zbytes mem').
    { rewrite <- Z3, <- Z4. rewrite sublist_app2 by (rewrite Hlr1; clear - Hin0; lia).
      rewrite Hlr1, Z.sub_diag. replace (sf_inSize (c3_s k0) + sf_outSize (c3_s k0) - sf_inSize (c3_s k0))
        with (Zlength (zbytes mem')) by (rewrite Zlength_map; clear - Hb8 Z4; lia).
      apply sublist_same; reflexivity. }
    unfold zrel_end, zrel, z2.
    cbn [sf_strip s_cont sf_stage sf_inSize sf_outSize sf_over sf_nfp sf_ring sf_inPos sf_outStart sf_outEnd
         sf_hostage sf_outBuff sf_lhSize sf_hbuf z_stage z_mem z_dc z_in zs_stage zs_inbs zs_outbs zs_over zs_nfp
         zs_mem zs_dc zs_hbuf zs_inpos zs_ostart zs_oend zs_host zs_fp zs_ibuf tabs_lxb].
    refine (conj (conj eq_refl (conj _ (conj Z3 (conj Z4 (conj Z5 (conj Z6 (conj Hb8
              (conj Hb7 (conj Hring2 (conj Hlxb2 (conj _ _)))))))))))
            (conj _ (conj _ (conj eq_refl (conj Hos (conj Hoe (conj Hh Hh01))))))).
    + unfold ZDSS_read; lia.
    + intros H; unfold ZDSS_read, ZDSS_loadHeader in H; discriminate.
    + intros _. refine (conj eq_refl (conj Hos (conj Hoe (conj Hb5 (conj Hb6 (conj Hh (conj Hh01
               (conj (ex_intro _ ts2 (conj eq_refl Hd2)) _)))))))).
      intros H; unfold ZDSS_read, ZDSS_load in H; discriminate.
    + intros _. split; [exact D13 | intros _; exact D12].
    + intros H; unfold ZDSS_read, ZDSS_init in H; discriminate.
  - (* r0 bytes written at outStart: zdss_flush *)
    set (z2 := z_stage XS (z_ring XS (z_mem XS (z_dc XS (z_in XS (z_in XS zi ib (P + L)) [] 0) d') mem')
                 (zs_ostart XS zi) (zs_ostart XS zi + r0)) ZDSS_flush).
    assert (Hone: one_iter_x (a_xin a) (a_xroom a) zi (ipc - a_ipos a) dl = LNext XS z2 (ipc - a_ipos a + L) dl)
      by (unfold one_iter_x; rewrite one_iter_load by exact Hzs; rewrite Hsl1; reflexivity).
    destruct (ex_loop_next a z0 zi f (ipc - a_ipos a) dl z2 _ _ Hbin ltac:(clear - Hinp Hipc Hipos; lia) Hdlr Hl Hone)
      as (f1 & Hl1 & Hip1).
    pose proof (zinv_x_bnd z2 (proj1 (proj2 (proj2 Hl1)))) as Hzb2. unfold zbnd_x in Hzb2; cbv zeta in Hzb2.
    destruct Hzb2 as (_&_&_&_&Hb5&Hb6&Hb7&Hb8&_). unfold z2 in Hb5, Hb6, Hb7, Hb8.
    cbn [z_stage z_ring z_mem z_dc z_in zs_ostart zs_oend zs_outbs zs_mem] in Hb5, Hb6, Hb7, Hb8.
    right. split.
    { unfold is_error_code. apply Z.ltb_ge. clear - Hb5 Hb6 Z4 Hsz Hin0. lia. }
    exists z2, f1.
    split; [replace (ipc + L - a_ipos a) with (ipc - a_ipos a + L) by ring; exact Hl1|]. intros _.
    assert (Hring2: sublist (zs_inbs XS zi) (zs_inbs XS zi + zs_outbs XS zi)
                      (sublist 0 (sf_inSize (c3_s k0)) ring1 ++ zbytes mem') = zbytes mem').
    { rewrite <- Z3, <- Z4. rewrite sublist_app2 by (rewrite Hlr1; clear - Hin0; lia).
      rewrite Hlr1, Z.sub_diag. replace (sf_inSize (c3_s k0) + sf_outSize (c3_s k0) - sf_inSize (c3_s k0))
        with (Zlength (zbytes mem')) by (rewrite Zlength_map; clear - Hb8 Z4; lia).
      apply sublist_same; reflexivity. }
    unfold zrel_end, zrel, z2.
    cbn [sf_strip s_cont sf_stage sf_inSize sf_outSize sf_over sf_nfp sf_ring sf_inPos sf_outStart sf_outEnd
         sf_hostage sf_outBuff sf_lhSize sf_hbuf z_stage z_ring z_mem z_dc z_in zs_stage zs_inbs zs_outbs zs_over
         zs_nfp zs_mem zs_dc zs_hbuf zs_inpos zs_ostart zs_oend zs_host zs_fp zs_ibuf tabs_lxb].
    refine (conj (conj eq_refl (conj _ (conj Z3 (conj Z4 (conj Z5 (conj Z6 (conj Hb8
              (conj Hb7 (conj Hring2 (conj Hlxb2 (conj _ _)))))))))))
            (conj _ (conj _ (conj eq_refl (conj Hos (conj eq_refl (conj Hh Hh01))))))).
    + unfold ZDSS_flush; lia.
    + intros H; unfold ZDSS_flush, ZDSS_loadHeader in H; discriminate.
    + intros _. refine (conj eq_refl (conj Hos (conj eq_refl (conj Hb5 (conj Hb6 (conj Hh (conj Hh01
               (conj (ex_intro _ ts2 (conj eq_refl Hd2)) _)))))))).
      intros H; unfold ZDSS_flush, ZDSS_load in H; discriminate.
    + intros _. split; [exact D13 | intros _; exact D12].
    + intros H; unfold ZDSS_flush, ZDSS_init in H; discriminate.
Qed.

(* an error of ZSTD_decompressContinueStream on the loaded unit: the model fails on the call too *)
Lemma ld_x_err (a: dsa) (k0: cst3) (sv: sview) (ipc opc: Z) (oc: list val) (dl: list Z) (E L ostart rr: Z)
    (oc': list val) (fs': fstate) (tabs': option tstate) (ts': tstate) :
  dsa_ok a -> call_inv a k0 sv ipc opc oc dl -> sf_stage (c3_s k0) = zdss_load ->
  fs_expected (c3_fs k0) = vlong E -> 0 <= E < 2 ^ 32 ->
  L = Z.min (E - fp_inpos (sv_fp sv)) (a_isz a - ipc) -> L = E - fp_inpos (sv_fp sv) ->
  Zlength (sf_ring (c3_s k0)) = sf_inSize (c3_s k0) + sf_outSize (c3_s k0) ->
  c3_tabs k0 = TInit (dd_ox (sv_dd sv)) ts' ->
  sf_outStart (c3_s k0) = vlong ostart -> 0 <= ostart <= sf_outSize (c3_s k0) -> 0 <= sf_inSize (c3_s k0) ->
  let ring1 := ring_load (sv_fp sv) (sf_ring (c3_s k0)) (fp_inpos (sv_fp sv)) (a_ibs a) ipc L in
  let u := ld_u sv (a_ibs a) ipc L in
  (is_skip (sv_fp sv) = false -> inwin_ok (i_bf (c3_s k0) ring1 u)) ->
  (sv_dd sv = None -> cont_exact (c3_fs k0) ts' (o_bf (c3_s k0) ring1 ostart sv) u E rr oc' fs' tabs') ->
  ex_call a (ld_w0 k0 sv ipc opc oc dl) -> is_error_code rr = true ->
  ex_err a rr.
Proof.
  intros Ha Hinv Hst HE HE0 HL HLE Hrl Hts Hos Hos1 Hin0 ring1 u Hiw Hce Hx Her.
  apply ex_err_of_loop. intros Hf.
  destruct (ld_x_unit a k0 sv ipc opc oc dl E L ostart rr oc' fs' tabs' ts' Ha Hinv Hst HE HE0 HL HLE Hrl Hts Hos
              Hos1 Hin0 Hiw Hce Hx Hf) as (z0 & zi & f & Hl & [[_ He]|[He _]]).
  - exists z0, zi, f, (ipc - a_ipos a), dl. split; [exact Hl | exact He].
  - congruence.
Qed.

(* a success: the loop goes on (zdss_read or zdss_flush) from the model's next state *)
Lemma ld_x_next (a: dsa) (k0: cst3) (sv: sview) (ipc opc: Z) (oc: list val) (dl: list Z) (E L ostart rr: Z)
    (oc': list val) (fs': fstate) (tabs': option tstate) (ts': tstate) (sv2: sview) (lxb: list Z) :
  dsa_ok a -> call_inv a k0 sv ipc opc oc dl -> sf_stage (c3_s k0) = zdss_load ->
  fs_expected (c3_fs k0) = vlong E -> 0 <= E < 2 ^ 32 ->
  L = Z.min (E - fp_inpos (sv_fp sv)) (a_isz a - ipc) -> L = E - fp_inpos (sv_fp sv) ->
  Zlength (sf_ring (c3_s k0)) = sf_inSize (c3_s k0) + sf_outSize (c3_s k0) ->
  c3_tabs k0 = TInit (dd_ox (sv_dd sv)) ts' ->
  sf_outStart (c3_s k0) = vlong ostart -> 0 <= ostart <= sf_outSize (c3_s k0) -> 0 <= sf_inSize (c3_s k0) ->
  let ring1 := ring_load (sv_fp sv) (sf_ring (c3_s k0)) (fp_inpos (sv_fp sv)) (a_ibs a) ipc L in
  let u := ld_u sv (a_ibs a) ipc L in
  (is_skip (sv_fp sv) = false -> inwin_ok (i_bf (c3_s k0) ring1 u)) ->
  (sv_dd sv = None -> cont_exact (c3_fs k0) ts' (o_bf (c3_s k0) ring1 ostart sv) u E rr oc' fs' tabs') ->
  ex_call a (ld_w0 k0 sv ipc opc oc dl) -> is_error_code rr = false ->
  let rd := andb (rr =? 0) (negb (is_skip (sv_fp sv))) in
  ex_call a {| w_smw := 1;
               w_k := k_cont k0 fs' tabs' lxb (sv_dd sv)
                        (s_cont (c3_s k0) (if rd then zdss_read else zdss_flush)
                           (if rd then sf_outEnd (c3_s k0) else vlong (ostart + rr))
                           (sublist 0 (sf_inSize (c3_s k0)) ring1 ++ oc'));
               w_sv := sv2; w_ipc := ipc + L; w_opc := opc; w_oc := oc; w_dl := dl |}.
Proof.
  intros Ha Hinv Hst HE HE0 HL HLE Hrl Hts Hos Hos1 Hin0 ring1 u Hiw Hce Hx Hok rd.
  apply ex_call_next_mk; [reflexivity|]. intros Hf.
  destruct (ld_x_unit a k0 sv ipc opc oc dl E L ostart rr oc' fs' tabs' ts' Ha Hinv Hst HE HE0 HL HLE Hrl Hts Hos
              Hos1 Hin0 Hiw Hce Hx Hf) as (z0 & zi & f & Hl & [[He _]|[_ (z2 & f1 & Hl1 & Hz)]]).
  - congruence.
  - exists z0, z2, f1. split; [exact Hl1|]. exact (Hz lxb).
Qed.

End CM_L3Ex_1.
