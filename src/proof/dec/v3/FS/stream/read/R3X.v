(* Case zdss_read with the exact claim: the model side (ExStream.st_read at model/Exact.v's instance) of each way the
   case leaves, as plain lemmas on S3Main.ex_call.  From the loop invariant's ex_call at stage zdss_read
   (rx_iter: the model's state zi, its iteration is st_read, and the size ZSTD_nextSrcSizeToDecompressWithInputSize
   computes from the frame fields is the model's d_next_in), each exit rebuilds ex_call or gives ex_err:
   - rx_end: the frame's end (size 0), the loop stops in zdss_init;
   - rx_noin: no input left, the loop stops;
   - rx_fall: the fall-through into zdss_load inside the same iteration (S3XKit.ex_loop_fall);
   - rx_err / rx_ok: the unit decoded from the caller's input by ZSTD_decompressContinueStream (S3Specs.cont_exact),
     an error or the next state (ExStream.z_dcs). *)
Require Import Zstd.proof.model.ExCall Zstd.proof.model.ExStream Zstd.proof.model.ExStreamFacts.
Require Import Zstd.proof.model.ExStreamBnd.
Require Zstd.proof.model.ExHuf Zstd.proof.model.ExBlock Zstd.proof.model.Exact.
Require Import Zstd.proof.dec.v3.FS.stream.read.R3Base Zstd.proof.dec.v3.FS.stream.read.R3Inv Zstd.proof.dec.v3.FS.stream.S3XKit.
Local Open Scope logic.

(* ---------- small facts ---------- *)

Lemma rx_vlong_inj : forall x y, 0 <= x <= Int64.max_unsigned -> 0 <= y <= Int64.max_unsigned ->
  Vlong (Int64.repr x) = Vlong (Int64.repr y) -> x = y.
Proof.
intros x y Hx Hy H. assert (H1: Int64.repr x = Int64.repr y) by congruence.
apply (f_equal Int64.unsigned) in H1. rewrite !Int64.unsigned_repr in H1 by lia. exact H1.
Qed.

Lemma rx_vint_inj : forall x y, 0 <= x <= Int.max_unsigned -> 0 <= y <= Int.max_unsigned ->
  Vint (Int.repr x) = Vint (Int.repr y) -> x = y.
Proof.
intros x y Hx Hy H. assert (H1: Int.repr x = Int.repr y) by congruence.
apply (f_equal Int.unsigned) in H1. rewrite !Int.unsigned_repr in H1 by lia. exact H1.
Qed.

(* the model's unit of the caller's input is the C's window *)
Lemma rx_slice_sub : forall (l: list Z) i k, 0 <= i -> 0 <= k -> slice l i k = sublist i (i + k) l.
Proof.
intros l i k Hi Hk. unfold slice, sublist. rewrite skipn_firstn_comm. f_equal. lia.
Qed.

Lemma rx_slice : forall (l: list Z) i j n, 0 <= i <= j -> 0 <= n -> j + n <= Zlength l ->
  slice (sublist i (Zlength l) l) (j - i) n = sublist j (j + n) l.
Proof.
intros l i j n Hij Hn Hl. rewrite rx_slice_sub by lia. rewrite sublist_sublist by lia.
f_equal; lia.
Qed.

(* the frame's progress is a skippable frame's iff ZSTD_decompressContinue's stage is skipFrame (inside a frame) *)
Lemma rx_skip : forall fs tabs fp l dd fstage, c_frame fs tabs fp l dd -> fp_complete fp = false ->
  fs_stage fs = Vint (Int.repr fstage) -> 0 <= fstage <= 7 -> is_skip fp = (fstage =? DS_skipFrame).
Proof.
intros fs tabs fp l dd fstage Hc Hnc Hs Hr.
destruct fp as [| | hdr got | hdr z]; unfold c_frame in Hc; try tauto.
- destruct Hc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hg). cbn [fp_complete] in Hnc. rewrite Hnc in Hg.
  destruct Hg as [Hg _]. rewrite Hs in Hg. apply rx_vint_inj in Hg; [|rep_lia|unfold ds_skipFrame; rep_lia].
  subst. reflexivity.
- destruct Hc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hph & _).
  cbn [fp_complete] in Hnc. cbn [is_skip]. unfold phase_fields in Hph.
  destruct (zp_ph z) as [|bh| |]; try discriminate.
  + destruct Hph as [Hp _]. rewrite Hs in Hp. apply rx_vint_inj in Hp; [|rep_lia|unfold ds_decodeBlockHeader; rep_lia].
    subst. reflexivity.
  + destruct Hph as (c & _ & Hp & _). rewrite Hs in Hp.
    destruct (bp_last (block_props_of bh) =? 1);
      apply rx_vint_inj in Hp; try (unfold ds_decompressLastBlock, ds_decompressBlock; rep_lia); subst; reflexivity.
  + destruct Hph as [Hp _]. rewrite Hs in Hp. apply rx_vint_inj in Hp; [|rep_lia|unfold ds_checkChecksum; rep_lia].
    subst. reflexivity.
Qed.

(* ---------- the model's state at stage zdss_read ---------- *)

(* the frame fields a zdss_read state is the image of *)
Lemma rx_drel : forall z s fs t, zrel z s fs t -> ZDSS_read <= zs_stage XS z ->
  exists ts, t = TInit None ts /\ drel (zs_fp XS z) (zs_dc XS z) (sf_outBuff s) fs ts.
Proof.
intros z s fs t H Hs. destruct H as (_&_&_&_&_&_&_&_&_&_&_&Hrd). destruct (Hrd Hs) as (_&_&_&_&_&_&_&Hd&_).
exact Hd.
Qed.

(* inside a frame, zrel already pins what the code after the loop reads *)
Lemma rx_zrel_end : forall z s fs t, zrel z s fs t -> ZDSS_read <= zs_stage XS z -> zrel_end z s fs t.
Proof.
intros z s fs t H Hs. pose proof H as H'. destruct H' as (_&_&_&_&_&_&_&_&_&_&_&Hrd).
destruct (Hrd Hs) as (Hip&Hos&Hoe&_&_&Hh&Hh01&(ts&Ht&Hd)&_).
destruct Hd as (_&_&_&_&_&_&_&_&_&_&_&_&Hfst&Hfex&_).
unfold zrel_end. split; [exact H|].
split; [intros _; split; [exact Hfex | intros _; exact Hfst]|].
split; [intros E; rewrite E in Hs; unfold ZDSS_init, ZDSS_read in Hs; lia|].
auto.
Qed.

(* the size ZSTD_nextSrcSizeToDecompressWithInputSize computes from the frame fields is the model's *)
Lemma rx_needed : forall z s fs t fstage e n,
  zrel z s fs t -> zs_stage XS z = ZDSS_read ->
  fs_stage fs = Vint (Int.repr fstage) -> 0 <= fstage <= 7 ->
  fs_expected fs = Vlong (Int64.repr e) -> 0 <= e <= Int64.max_unsigned ->
  d_next_in XS (zs_dc XS z) n = next_size fstage (bt_of (fs_bType fs)) e n.
Proof.
intros z s fs t fstage e n H Hs Hfs Hfr Hfe Her.
destruct (rx_drel z s fs t H ltac:(rewrite Hs; unfold ZDSS_read; lia)) as (ts & _ & Hd).
destruct Hd as (_&_&_&_&Hst&Hex&Hbt&_&_&_&_&_&Hfst&Hfex&Hbb&_).
rewrite Hfs in Hfst. apply rx_vint_inj in Hfst; [|rep_lia|unfold DS_skipFrame in Hst; rep_lia].
unfold vlong in Hfex. rewrite Hfe in Hfex. apply rx_vlong_inj in Hfex; [|lia|lia].
subst fstage e. unfold d_next_in, next_size.
unfold ds_decompressBlock, ds_decompressLastBlock, DS_decompressBlock, DS_decompressLastBlock in *.
destruct ((d_stage XS (zs_dc XS z) =? 3) || (d_stage XS (zs_dc XS z) =? 4))%bool eqn:E; [|reflexivity].
destruct (Hbb ltac:(apply orb_true_iff in E; destruct E as [E|E]; apply Z.eqb_eq in E; lia)) as [Hb _].
rewrite Hb. unfold bt_of. rewrite Int.signed_repr by rep_lia. reflexivity.
Qed.

Ltac rx_simpl := cbn [sf_strip sf_set_stage sf_cont sf_stage sf_inBuff sf_inSize sf_inPos sf_outBuff sf_outSize sf_outStart
  sf_outEnd sf_lhSize sf_hostage sf_nfp sf_expOut sf_hbuf sf_over sf_ring sf_mem sf_held
  z_stage z_mem z_dc z_ring zs_stage zs_hbuf zs_fp zs_ibuf zs_inpos zs_inbs zs_outbs zs_over zs_mem zs_ostart zs_oend
  zs_nfp zs_host zs_dc] in *.

Ltac zlia := unfold zdss_init, zdss_loadHeader, zdss_read, zdss_load, zdss_flush,
  ZDSS_init, ZDSS_loadHeader, ZDSS_read, ZDSS_load, ZDSS_flush in *; lia.

(* the frame's end: the same state in zdss_init *)
Lemma rx_zrel_end_init : forall s0 z fs t, zrel_end z (sf_strip s0) fs t -> zs_stage XS z = ZDSS_read ->
  zrel_end (z_stage XS z ZDSS_init) (sf_strip (sf_set_stage s0 zdss_init)) fs t.
Proof.
intros s0 z fs t H Hs. destruct H as (Hz & Hx & _ & Hip & Hos & Hoe & Hh & Hh01).
destruct (rx_drel _ _ _ _ Hz ltac:(zlia)) as (ts & Ht & Hd).
destruct Hz as (Hst&Hsr&Hin&Hout&Hov&Hnf&Hlm&Hbm&Hring&Hlxb&_&_).
unfold zrel_end, zrel. rx_simpl.
split; [|split; [intros _; apply Hx; zlia|]].
- repeat split; auto; try zlia.
- split; [intros _ _; exists ts; split; [exact Ht | exact Hd]|]. auto.
Qed.

(* the fall-through: the same state in zdss_load, its input buffer empty *)
Lemma rx_zrel_end_load : forall s0 z fs t, zrel_end z (sf_strip s0) fs t -> zs_stage XS z = ZDSS_read ->
  zs_inpos XS z = 0 -> zs_ibuf XS z = nil ->
  zrel_end (z_stage XS z ZDSS_load) (sf_strip (sf_set_stage s0 zdss_load)) fs t.
Proof.
intros s0 z fs t H Hs Hp0 Hib. destruct H as (Hz & Hx & Hi0 & Hip & Hos & Hoe & Hh & Hh01).
destruct Hz as (Hst&Hsr&Hin&Hout&Hov&Hnf&Hlm&Hbm&Hring&Hlxb&_&Hrd).
destruct (Hrd ltac:(zlia)) as (Hip'&Hos'&Hoe'&Hoo&Hob&Hh'&Hh01'&Hd&_).
unfold zrel_end, zrel. rx_simpl.
split; [|split; [intros _; apply Hx; zlia|]].
- split; [reflexivity|]. split; [zlia|]. do 8 (split; [assumption|]). split; [intros E; zlia|].
  intros _. do 7 (split; [assumption|]). split; [exact Hd|].
  intros _ _. rewrite Hib, Hp0. split; [reflexivity|]. split; [constructor|]. rewrite sublist_nil. reflexivity.
- split; [intros E; zlia|]. auto.
Qed.

(* ZSTD_decompressContinue's return value is at most the block size (never an error code) *)
Lemma rx_dcont_le : forall fh d mem dst cap src n d' mem' r,
  d_continue XS Exact.xblock fh d mem dst cap src n = Some (d', mem', r) -> r <= Z.max 0 (fh_blockSizeMax fh).
Proof.
intros fh d mem dst cap src n d' mem' r H. unfold d_continue in H. cbv zeta in H.
repeat match type of H with
  | context [if ?c then _ else _] => destruct c eqn:?
  | context [match ?m with _ => _ end] => destruct m eqn:?
  end; try discriminate; inversion H; subst; try lia.
all: repeat match goal with Hb: (_ >? _) = false |- _ => rewrite Z.gtb_ltb, Z.ltb_ge in Hb end; lia.
Qed.

Definition rx_cap (s: sfields) (fp: fprog) (ostart: Z) : Z := if is_skip fp then 0 else sf_outSize s - ostart.

Definition rx_next (zi: zstate_x) (d': ExStream.dstate XS) (mem': list Z) (r ostart: Z) (skip: bool) : zstate_x :=
  if ((r =? 0) && negb skip)%bool then z_stage XS (z_mem XS (z_dc XS zi d') mem') ZDSS_read
  else z_stage XS (z_ring XS (z_mem XS (z_dc XS zi d') mem') ostart (ostart + r)) ZDSS_flush.

(* the state after a unit decoded from the caller's input (ExStream.z_dcs) against the fields the code leaves *)
Lemma rx_zrel_end_next : forall s0 fs t zi d' mem' r ostart skip fs' ts' oc',
  zrel_end zi (sf_strip s0) fs t -> zs_stage XS zi = ZDSS_read -> zs_ostart XS zi = ostart ->
  drel (zs_fp XS zi) d' (sf_outBuff s0) fs' ts' -> oc' = zbytes mem' -> Zlength oc' = sf_outSize s0 ->
  Zlength (sf_ring s0) = sf_inSize s0 + sf_outSize s0 -> 0 <= sf_inSize s0 ->
  zbnd_x (rx_next zi d' mem' r ostart skip) ->
  zrel_end (rx_next zi d' mem' r ostart skip)
    (sf_strip (sf_cont s0 (if ((r =? 0) && negb skip)%bool then zdss_read else zdss_flush)
                 (if ((r =? 0) && negb skip)%bool then sf_outEnd s0 else vlong (ostart + r))
                 (sublist 0 (sf_inSize s0) (sf_ring s0) ++ oc'))) fs' (TInit None ts').
Proof.
intros s0 fs t zi d' mem' r ostart skip fs' ts' oc' H Hs Hzo Hd Hoc Hloc Hlr Hi0 Hbnd.
destruct H as (Hz & _ & _ & Hip & Hos & Hoe & Hh & Hh01).
destruct Hz as (_&_&Hin&Hout&Hov&Hnf&_).
pose proof Hd as (_&_&_&_&_&_&_&_&_&_&Htx&_&Hfst&Hfex&_).
assert (Hring: sublist (sf_inSize s0) (sf_inSize s0 + sf_outSize s0) (sublist 0 (sf_inSize s0) (sf_ring s0) ++ oc') = oc')
  by list_solve.
assert (Hlm: Zlength mem' = sf_outSize s0) by (rewrite <- Hloc, Hoc, Zlength_map; reflexivity).
unfold rx_next in *.
destruct ((r =? 0) && negb skip)%bool eqn:Erd.
- destruct Hbnd as (_&_&_&_&Hoo&Hob&Hbm&_). rx_simpl.
  unfold zrel_end, zrel. rx_simpl.
  split; [|split; [intros _; split; [exact Hfex | intros _; exact Hfst]|]].
  + split; [reflexivity|]. split; [zlia|]. do 4 (split; [assumption|]).
    split; [lia|]. split; [exact Hbm|]. split; [rewrite <- Hin, <- Hout, Hring; exact Hoc|].
    split; [cbn [tabs_lxb]; rewrite <- Htx; reflexivity|]. split; [intros E; zlia|].
    intros _. split; [exact Hip|]. split; [rewrite ?Hzo in *; exact Hos|]. split; [exact Hoe|].
    split; [exact Hoo|]. split; [exact Hob|]. split; [exact Hh|]. split; [exact Hh01|].
    split; [exists ts'; split; [reflexivity | exact Hd]|]. intros E; zlia.
  + split; [intros E; zlia|]. split; [exact Hip|]. split; [rewrite ?Hzo in *; exact Hos|].
    split; [exact Hoe|]. split; [exact Hh | exact Hh01].
- destruct Hbnd as (_&_&_&_&Hoo&Hob&Hbm&_). rx_simpl.
  unfold zrel_end, zrel. rx_simpl.
  split; [|split; [intros _; split; [exact Hfex | intros _; exact Hfst]|]].
  + split; [reflexivity|]. split; [zlia|]. do 4 (split; [assumption|]).
    split; [lia|]. split; [exact Hbm|]. split; [rewrite <- Hin, <- Hout, Hring; exact Hoc|].
    split; [cbn [tabs_lxb]; rewrite <- Htx; reflexivity|]. split; [intros E; zlia|].
    intros _. split; [exact Hip|]. split; [rewrite ?Hzo in *; exact Hos|]. split; [reflexivity|].
    split; [exact Hoo|]. split; [exact Hob|]. split; [exact Hh|]. split; [exact Hh01|].
    split; [exists ts'; split; [reflexivity | exact Hd]|]. intros E; zlia.
  + split; [intros E; zlia|]. split; [exact Hip|]. split; [rewrite ?Hzo in *; exact Hos|].
    split; [reflexivity|]. split; [exact Hh | exact Hh01].
Qed.

Section RX.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.

(* the frame fields as case zdss_read reads them (FSSpecs3.next_size's arguments) *)
Definition rx_hd (a: dsa) (w: lw) (fstage e: Z) : Prop :=
  dsa_ok a /\ a_ipos a <= w_ipc w <= a_isz a /\ sf_stage (c3_s (w_k w)) = zdss_read /\
  fs_stage (c3_fs (w_k w)) = Vint (Int.repr fstage) /\ 0 <= fstage <= 7 /\
  fs_expected (c3_fs (w_k w)) = Vlong (Int64.repr e) /\ 0 <= e <= Int64.max_unsigned /\
  Zlength (w_dl w) <= a_xroom a.

(* the size of the unit the code asks for *)
Definition rx_ns (a: dsa) (w: lw) (fstage e: Z) : Z :=
  next_size fstage (bt_of (fs_bType (c3_fs (w_k w)))) e (a_isz a - w_ipc w).

Lemma rx_hd_of (a: dsa) (w: lw) (fstage e: Z) :
  dsa_ok a -> call_inv a (w_k w) (w_sv w) (w_ipc w) (w_opc w) (w_oc w) (w_dl w) ->
  sf_stage (c3_s (w_k w)) = zdss_read ->
  fs_stage (c3_fs (w_k w)) = Vint (Int.repr fstage) -> 0 <= fstage <= 7 ->
  fs_expected (c3_fs (w_k w)) = Vlong (Int64.repr e) -> 0 <= e <= Int64.max_unsigned ->
  rx_hd a w fstage e.
Proof.
intros Ha (Hip & Hop & _ & _ & Hdl & _) Hst Hfs Hfr Hfe Her. unfold rx_hd, a_xroom.
refine (conj Ha (conj Hip (conj Hst (conj Hfs (conj Hfr (conj Hfe (conj Her _))))))). lia.
Qed.

(* the iteration at stage zdss_read: the model's state zi, its iteration st_read, the input left, the size *)
Lemma rx_iter (a: dsa) (w: lw) (fstage e: Z) :
  ex_call a w -> w_smw w = 1 -> fresh_cfg (a_st a) -> rx_hd a w fstage e ->
  exists z0 zi f, ex_loop a z0 zi f (w_ipc w - a_ipos a) (w_dl w) /\
    zrel_end zi (w_sx w) (w_fs w) (w_tabs w) /\ zs_stage XS zi = ZDSS_read /\
    bytes_ok (a_xin a) /\ 0 <= w_ipc w - a_ipos a <= Zlength (a_xin a) /\
    Zlength (a_xin a) - (w_ipc w - a_ipos a) = a_isz a - w_ipc w /\
    one_iter_x (a_xin a) (a_xroom a) zi (w_ipc w - a_ipos a) (w_dl w) =
      st_read XS Exact.xblock (a_xin a) zi (w_ipc w - a_ipos a) (w_dl w) /\
    d_next_in XS (zs_dc XS zi) (a_isz a - w_ipc w) = rx_ns a w fstage e.
Proof.
intros Hx Hs Hf (Ha & Hipc & Hst & Hfs & Hfr & Hfe & Her & _).
destruct (ex_call_go a w Hx Hs Hf) as (z0 & zi & f & Hl & Hz).
assert (Hzr: zrel zi (w_sx w) (w_fs w) (w_tabs w)) by (destruct Hz as [(_&_&_&Hz)|(Hz&_)]; exact Hz).
assert (Hzs: zs_stage XS zi = ZDSS_read).
{ destruct Hzr as (Hz1&_). unfold w_sx in Hz1. cbn [sf_strip sf_stage] in Hz1. rewrite Hst in Hz1. zlia. }
destruct Ha as (_&_&_&_&_&_&_&_&_&_&_&_&Hipos&_&Hlibs&Hbibs&_).
assert (Hlen: Zlength (a_xin a) = a_isz a - a_ipos a) by (unfold a_xin; rewrite Zlength_sublist; lia).
exists z0, zi, f. split; [exact Hl|].
split; [apply rx_zrel_end; [exact Hzr | zlia]|]. split; [exact Hzs|].
split; [unfold a_xin; apply Forall_sublist; exact Hbibs|].
split; [lia|]. split; [lia|].
split; [unfold one_iter_x; apply one_iter_read; exact Hzs|].
apply (rx_needed zi (w_sx w) (w_fs w) (w_tabs w)); auto.
Qed.

(* the end of the frame (size 0): the loop stops in zdss_init *)
Lemma rx_end (a: dsa) (w: lw) (fstage e: Z) :
  ex_call a w -> w_smw w = 1 -> rx_hd a w fstage e -> rx_ns a w fstage e = 0 ->
  ex_call a {| w_smw := 0; w_k := k_stage (w_k w) zdss_init; w_sv := w_sv w; w_ipc := w_ipc w;
               w_opc := w_opc w; w_oc := w_oc w; w_dl := w_dl w |}.
Proof.
intros Hx Hs Hh Hns. apply ex_call_stop_mk; [reflexivity|]. intros Hf. cbn [w_ipc w_dl w_k].
destruct (rx_iter a w fstage e Hx Hs Hf Hh) as (z0 & zi & f & Hl & Hze & Hzs & Hb & Hip & Hlen & Hone & Hneed).
assert (Hst1: one_iter_x (a_xin a) (a_xroom a) zi (w_ipc w - a_ipos a) (w_dl w) =
              LStop XS (z_stage XS zi ZDSS_init) (w_ipc w - a_ipos a) (w_dl w)).
{ rewrite Hone. unfold st_read. cbv zeta. rewrite Hlen, Hneed, Hns. reflexivity. }
pose proof Hh as (_&_&_&_&_&_&_&Hdl).
destruct (ex_loop_stop a z0 zi f _ _ _ _ _ Hb Hip Hdl Hl Hst1) as [Hal Hz1].
destruct Hl as (Hr & H0 & _).
exists z0, (z_stage XS zi ZDSS_init). split; [exact Hr|]. split; [exact H0|]. split; [exact Hz1|].
split; [exact Hal|].
unfold w_sx, w_fs, w_tabs, k_stage. cbn [c3_with_s c3_s c3_fs c3_tabs].
apply rx_zrel_end_init; [exact Hze | exact Hzs].
Qed.

(* no input left: the loop stops *)
Lemma rx_noin (a: dsa) (w: lw) (fstage e: Z) :
  ex_call a w -> w_smw w = 1 -> rx_hd a w fstage e -> rx_ns a w fstage e <> 0 -> w_ipc w = a_isz a ->
  ex_call a {| w_smw := 0; w_k := w_k w; w_sv := w_sv w; w_ipc := w_ipc w;
               w_opc := w_opc w; w_oc := w_oc w; w_dl := w_dl w |}.
Proof.
intros Hx Hs Hh Hns Hie. apply ex_call_stop_mk; [reflexivity|]. intros Hf. cbn [w_ipc w_dl w_k].
destruct (rx_iter a w fstage e Hx Hs Hf Hh) as (z0 & zi & f & Hl & Hze & Hzs & Hb & Hip & Hlen & Hone & Hneed).
assert (Hn0: 0 <= rx_ns a w fstage e).
{ unfold rx_ns, next_size. destruct Hh as (_&_&_&_&_&_&Her&_). destruct (_ && _)%bool; lia. }
assert (Hst1: one_iter_x (a_xin a) (a_xroom a) zi (w_ipc w - a_ipos a) (w_dl w) =
              LStop XS zi (w_ipc w - a_ipos a) (w_dl w)).
{ rewrite Hone. unfold st_read. cbv zeta. rewrite Hlen, Hneed.
  rewrite Hie, Z.sub_diag in *.
  destruct (Z.eqb_spec (rx_ns a w fstage e) 0); [contradiction|].
  destruct (Z.geb_spec 0 (rx_ns a w fstage e)); [lia|]. reflexivity. }
pose proof Hh as (_&_&_&_&_&_&_&Hdl).
destruct (ex_loop_stop a z0 zi f _ _ _ _ _ Hb Hip Hdl Hl Hst1) as [Hal Hz1].
destruct Hl as (Hr & H0 & _).
exists z0, zi. split; [exact Hr|]. split; [exact H0|]. split; [exact Hz1|]. split; [exact Hal|]. exact Hze.
Qed.

(* the fall-through into zdss_load (less input than the unit, some left): the model's iteration is st_load on the
   stage-load state *)
Lemma rx_fall (a: dsa) (w: lw) (fstage e: Z) :
  ex_call a w -> w_smw w = 1 -> rx_hd a w fstage e -> a_isz a - w_ipc w < rx_ns a w fstage e ->
  w_ipc w <> a_isz a ->
  ex_call a {| w_smw := 1; w_k := k_stage (w_k w) zdss_load; w_sv := w_sv w; w_ipc := w_ipc w;
               w_opc := w_opc w; w_oc := w_oc w; w_dl := w_dl w |}.
Proof.
intros Hx Hs Hh Hlt Hne. apply ex_call_next_mk; [reflexivity|]. intros Hf. cbn [w_ipc w_dl w_k].
destruct (rx_iter a w fstage e Hx Hs Hf Hh) as (z0 & zi & f & Hl & Hze & Hzs & Hb & Hip & Hlen & Hone & Hneed).
pose proof Hh as (_ & Hipc & _).
pose proof Hl as (_ & _ & Hzi & _).
pose proof Hzi as (_ & _ & (_ & Hn & _) & _).
assert (Hp0: zs_inpos XS zi = 0) by (apply (fun H => proj1 (Hn H)); zlia).
destruct (zinv_x_bnd zi Hzi) as (_&_&_&_&_&_&_&_&_&_&Hibn&_).
specialize (Hibn ltac:(zlia)).
set (zl := z_stage XS zi ZDSS_load).
(* the unit is a whole part: expected, more than the input left *)
assert (Hex: rx_ns a w fstage e = d_expected XS (zs_dc XS zi)).
{ rewrite <- Hneed in Hlt |- *. unfold d_next_in in *. destruct (_ && _)%bool; [lia|reflexivity]. }
assert (Hst1: one_iter_x (a_xin a) (a_xroom a) zi (w_ipc w - a_ipos a) (w_dl w) =
              one_iter_x (a_xin a) (a_xroom a) zl (w_ipc w - a_ipos a) (w_dl w)).
{ rewrite Hone. unfold one_iter_x. rewrite one_iter_load by (unfold zl; reflexivity).
  unfold st_read. cbv zeta. rewrite Hlen, Hneed.
  destruct (Z.eqb_spec (rx_ns a w fstage e) 0); [lia|].
  destruct (Z.geb_spec (a_isz a - w_ipc w) (rx_ns a w fstage e)); [lia|].
  destruct (Z.eqb_spec (a_isz a - w_ipc w) 0); [lia|]. reflexivity. }
assert (Hzl: zinv_x zl).
{ unfold zinv_x, zl. apply zinv_read_load; [exact Hzi | exact Hzs |].
  rewrite <- Hex. lia. }
exists z0, zl, f. split.
- apply (ex_loop_fall a z0 zi zl f _ _ Hl Hzl); [symmetry; exact Hst1|].
  unfold zpot, zl. rx_simpl. rewrite Hzs. cbv [ZDSS_load ZDSS_read ZDSS_flush Z.eqb Pos.eqb]. lia.
- unfold w_sx, w_fs, w_tabs, k_stage. cbn [c3_with_s c3_s c3_fs c3_tabs].
  apply rx_zrel_end_load; assumption.
Qed.

(* ZSTD_decompressContinueStream on the unit of the caller's input (stage, room and ring as the code passes them):
   the model's iteration decodes the same unit with the same d_continue, whose outcome cont_exact relates to the
   C's *)
Lemma rx_dec_core (a: dsa) (w: lw) (fstage e ns: Z) fp l dd ts ostart rr oc' fs' tabs' :
  ex_call a w -> w_smw w = 1 -> fresh_cfg (a_st a) -> rx_hd a w fstage e ->
  rx_ns a w fstage e = ns -> 0 < ns -> ns <= a_isz a - w_ipc w ->
  c_frame (c3_fs (w_k w)) (c3_tabs (w_k w)) fp l dd -> fp_complete fp = false ->
  c3_tabs (w_k w) = TInit (dd_ox dd) ts ->
  sf_outStart (c3_s (w_k w)) = vlong ostart -> 0 <= ostart <= sf_outSize (c3_s (w_k w)) ->
  sf_outSize (c3_s (w_k w)) <= Int64.max_unsigned ->
  (dd = None -> cont_exact (c3_fs (w_k w)) ts (oa_ring (c3_s (w_k w)) fp ostart)
                  (sublist (w_ipc w) (w_ipc w + ns) (a_ibs a)) ns rr oc' fs' tabs') ->
  exists z0 zi f, ex_loop a z0 zi f (w_ipc w - a_ipos a) (w_dl w) /\
    zrel_end zi (w_sx w) (w_fs w) (w_tabs w) /\ zs_stage XS zi = ZDSS_read /\
    bytes_ok (a_xin a) /\ 0 <= w_ipc w - a_ipos a <= Zlength (a_xin a) /\ dd = None /\
    drel (zs_fp XS zi) (zs_dc XS zi) (sf_outBuff (c3_s (w_k w))) (c3_fs (w_k w)) ts /\
    zs_ostart XS zi = ostart /\
    one_iter_x (a_xin a) (a_xroom a) zi (w_ipc w - a_ipos a) (w_dl w) =
      match d_continue XS Exact.xblock (zs_fp XS zi) (zs_dc XS zi) (zs_mem XS zi) ostart
              (rx_cap (c3_s (w_k w)) fp ostart) (sublist (w_ipc w) (w_ipc w + ns) (a_ibs a)) ns with
      | None => LErr XS
      | Some (d', mem', r) => LNext XS (rx_next zi d' mem' r ostart (is_skip fp)) (w_ipc w - a_ipos a + ns) (w_dl w)
      end /\
    match d_continue XS Exact.xblock (zs_fp XS zi) (zs_dc XS zi) (zs_mem XS zi) ostart
            (rx_cap (c3_s (w_k w)) fp ostart) (sublist (w_ipc w) (w_ipc w + ns) (a_ibs a)) ns with
    | None => is_error_code rr = true
    | Some (d', mem', r0) =>
        rr = r0 /\ oc' = zbytes mem' /\
        exists ts', tabs' = Some ts' /\ drel (zs_fp XS zi) d' (sf_outBuff (c3_s (w_k w))) fs' ts'
    end.
Proof.
intros Hx Hs Hf Hh Hns Hn0 Hge Hcf Hnc Hts Hos Ho0 HoN Hce.
destruct (rx_iter a w fstage e Hx Hs Hf Hh) as (z0 & zi & f & Hl & Hze & Hzs & Hb & Hip & Hlen & Hone & Hneed).
pose proof Hh as (Ha & Hipc & Hst & Hfs & Hfr & Hfe & Her & _).
pose proof Hl as (_ & _ & Hzi & _).
destruct (zinv_x_bnd zi Hzi) as (_&_&_&_&_&_&_&_&_&_&_&Hde&_).
pose proof Hze as (Hzr & _).
destruct (rx_drel _ _ _ _ Hzr ltac:(zlia)) as (ts0 & Ht0 & Hd).
unfold w_tabs in Ht0. rewrite Hts in Ht0. injection Ht0 as Hox <-.
assert (Hdd: dd = None) by (destruct dd; [discriminate | reflexivity]).
pose proof Hzr as (_&_&Hin&Hout&_&_&_&Hbm&Hring&_&_&Hrd).
destruct (Hrd ltac:(zlia)) as (_&Hos'&_&Hoo&Hob&_).
unfold w_sx, w_fs in *. cbn [sf_strip sf_inSize sf_outSize sf_outStart sf_outBuff sf_ring] in *.
assert (Hzo: zs_ostart XS zi = ostart).
{ rewrite Hos in Hos'. unfold vlong in Hos'. apply rx_vlong_inj in Hos'; lia. }
(* ZSTD_decompressContinue's stage *)
pose proof Hd as (_&_&_&_&Hdst&_&_&_&_&_&_&_&Hdfs&_).
rewrite Hfs in Hdfs. apply rx_vint_inj in Hdfs; [|rep_lia|unfold DS_skipFrame in Hdst; rep_lia].
pose proof (rx_skip _ _ _ _ _ _ Hcf Hnc Hfs Hfr) as Hsk.
exists z0, zi, f. split; [exact Hl|]. split; [exact Hze|]. split; [exact Hzs|]. split; [exact Hb|].
split; [exact Hip|]. split; [exact Hdd|]. split; [exact Hd|]. split; [exact Hzo|].
split.
- rewrite Hone. unfold st_read. cbv zeta. rewrite Hlen, Hneed, Hns.
  destruct (Z.eqb_spec ns 0); [lia|].
  destruct (Z.geb_spec (a_isz a - w_ipc w) ns); [|lia].
  destruct Ha as (_&_&_&_&_&_&_&_&_&_&_&_&Hipos&_&Hlibs&_).
  unfold a_xin. rewrite <- Hlibs. rewrite rx_slice by lia.
  unfold z_dcs. cbv zeta. rewrite Hzo, <- Hout, <- Hdfs, <- Hsk. unfold rx_cap.
  replace (w_ipc w - a_ipos a + ns) with (w_ipc w - a_ipos a + ns) by reflexivity.
  destruct (d_continue _ _ _ _ _ _ _ _ _) as [[[d' mem'] r]|]; [|reflexivity].
  unfold rx_next. destruct ((r =? 0) && negb (is_skip fp))%bool; reflexivity.
- specialize (Hce Hdd (zs_fp XS zi) (zs_dc XS zi) (zs_mem XS zi) Hd).
  unfold oa_ring in Hce. cbn [oa_c oa_d oa_cap oa_base] in Hce.
  rewrite Hin, Hout in Hce. specialize (Hce Hring Hbm).
  unfold rx_cap. rewrite Hout. apply Hce. intros Hbl Hbt Hc0.
  destruct (d_de XS (zs_dc XS zi)) as [x|] eqn:Ex; [|reflexivity]. exfalso.
  specialize (Hde ltac:(zlia) Hbl Hbt ltac:(congruence)).
  rewrite Hsk, Hdfs in Hc0.
  destruct Hbl as [Hbl|Hbl]; rewrite Hbl in Hc0; cbn in Hc0; lia.
Qed.

(* the unit's decoding failed: so does the model's *)
Lemma rx_err (a: dsa) (w: lw) (fstage e ns: Z) fp l dd ts ostart rr oc' fs' tabs' :
  ex_call a w -> w_smw w = 1 -> rx_hd a w fstage e ->
  rx_ns a w fstage e = ns -> 0 < ns -> ns <= a_isz a - w_ipc w ->
  c_frame (c3_fs (w_k w)) (c3_tabs (w_k w)) fp l dd -> fp_complete fp = false ->
  c3_tabs (w_k w) = TInit (dd_ox dd) ts ->
  sf_outStart (c3_s (w_k w)) = vlong ostart -> 0 <= ostart <= sf_outSize (c3_s (w_k w)) ->
  sf_outSize (c3_s (w_k w)) <= Int64.max_unsigned ->
  (dd = None -> cont_exact (c3_fs (w_k w)) ts (oa_ring (c3_s (w_k w)) fp ostart)
                  (sublist (w_ipc w) (w_ipc w + ns) (a_ibs a)) ns rr oc' fs' tabs') ->
  is_error_code rr = true ->
  ex_err a rr.
Proof.
intros Hx Hs Hh Hns Hn0 Hge Hcf Hnc Hts Hos Ho0 HoN Hce Herr.
apply ex_err_of_loop. intros Hf.
destruct (rx_dec_core a w fstage e ns fp l dd ts ostart rr oc' fs' tabs' Hx Hs Hf Hh Hns Hn0 Hge Hcf Hnc Hts Hos
            Ho0 HoN Hce) as (z0 & zi & f & Hl & _ & _ & _ & _ & _ & Hd & _ & Hone & Hm).
exists z0, zi, f, (w_ipc w - a_ipos a), (w_dl w). split; [exact Hl|]. rewrite Hone.
revert Hm. destruct (d_continue _ _ _ _ _ _ _ _ _) as [[[d' mem'] r]|] eqn:E; [|reflexivity].
intros (-> & _). exfalso.
pose proof (rx_dcont_le _ _ _ _ _ _ _ _ _ _ E) as Hr.
destruct Hd as (_&_&Hbsm&_).
unfold is_error_code in Herr. apply Z.ltb_lt in Herr. rep_lia.
Qed.

(* the unit decoded: the loop goes on from the model's next state *)
Lemma rx_ok (a: dsa) (w: lw) (fstage e ns: Z) fp l dd ts ostart rr oc' fs' tabs' sv' :
  ex_call a w -> w_smw w = 1 -> rx_hd a w fstage e ->
  rx_ns a w fstage e = ns -> 0 < ns -> ns <= a_isz a - w_ipc w ->
  c_frame (c3_fs (w_k w)) (c3_tabs (w_k w)) fp l dd -> fp_complete fp = false ->
  c3_tabs (w_k w) = TInit (dd_ox dd) ts ->
  sf_outStart (c3_s (w_k w)) = vlong ostart -> 0 <= ostart <= sf_outSize (c3_s (w_k w)) ->
  sf_outSize (c3_s (w_k w)) <= Int64.max_unsigned ->
  (dd = None -> cont_exact (c3_fs (w_k w)) ts (oa_ring (c3_s (w_k w)) fp ostart)
                  (sublist (w_ipc w) (w_ipc w + ns) (a_ibs a)) ns rr oc' fs' tabs') ->
  is_error_code rr = false ->
  Zlength oc' = sf_outSize (c3_s (w_k w)) ->
  Zlength (sf_ring (c3_s (w_k w))) = sf_inSize (c3_s (w_k w)) + sf_outSize (c3_s (w_k w)) ->
  0 <= sf_inSize (c3_s (w_k w)) ->
  ex_call a {| w_smw := 1;
               w_k := c3_with_s (c3_with_fs (w_k w) fs' (tabs_of dd nil tabs'))
                        (sf_cont (c3_s (w_k w)) (if ((rr =? 0) && negb (is_skip fp))%bool then zdss_read else zdss_flush)
                           (if ((rr =? 0) && negb (is_skip fp))%bool then sf_outEnd (c3_s (w_k w))
                            else vlong (ostart + rr))
                           (sublist 0 (sf_inSize (c3_s (w_k w))) (sf_ring (c3_s (w_k w))) ++ oc'));
               w_sv := sv'; w_ipc := w_ipc w + ns; w_opc := w_opc w; w_oc := w_oc w; w_dl := w_dl w |}.
Proof.
intros Hx Hs Hh Hns Hn0 Hge Hcf Hnc Hts Hos Ho0 HoN Hce Hok Hloc Hlr Hi0.
apply ex_call_next_mk; [reflexivity|]. intros Hf. cbn [w_ipc w_dl w_k].
destruct (rx_dec_core a w fstage e ns fp l dd ts ostart rr oc' fs' tabs' Hx Hs Hf Hh Hns Hn0 Hge Hcf Hnc Hts Hos
            Ho0 HoN Hce) as (z0 & zi & f & Hl & Hze & Hzs & Hb & Hip & Hdd & Hd & Hzo & Hone & Hm).
revert Hone Hm. destruct (d_continue _ _ _ _ _ _ _ _ _) as [[[d' mem'] r]|] eqn:E;
  [|intros _ Hm; rewrite Hm in Hok; discriminate].
intros Hone (-> & Hoc & ts' & -> & Hd').
pose proof Hh as (_&_&_&_&_&_&_&Hdl).
destruct (ex_loop_next a z0 zi f _ _ _ _ _ Hb Hip Hdl Hl Hone) as (f1 & Hl1 & _).
exists z0, (rx_next zi d' mem' r ostart (is_skip fp)), f1. split.
- replace (w_ipc w + ns - a_ipos a) with (w_ipc w - a_ipos a + ns) by lia. exact Hl1.
- unfold w_sx, w_fs, w_tabs. cbn [c3_with_s c3_with_fs c3_s c3_fs c3_tabs tabs_of]. subst dd. cbn [dd_ox option_map].
  pose proof Hl1 as (_ & _ & Hz1 & _).
  apply (rx_zrel_end_next _ (c3_fs (w_k w)) (w_tabs w)); auto.
  apply zinv_x_bnd, Hz1.
Qed.

End RX.
