(* FS3 streaming, case zdss_load: the facts of the loaded unit in stable mode (the premises of
   P_load_cont_stable unpacked), and the unit zstd is given (v2 load_call_pre, stable part). *)
Require Export Zstd.proof.dec.v3.FS.stream.load.L3StStep.
Local Open Scope logic.

Section CM_L3StFacts_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* the unit of a Zstandard frame once loaded: what fs_expected asked for *)
Lemma lcp_unit_z : forall fs tabs hdr z l dd E,
  c_frame fs tabs (FP_zstd hdr z) l dd -> fp_complete (FP_zstd hdr z) = false ->
  fp_rawbody (FP_zstd hdr z) = false -> fs_expected fs = vlong E -> 0 <= E < 2 ^ 32 ->
  unit_ok (FP_zstd hdr (zp_set_got z nil)) E.
Proof.
intros fs tabs hdr z l dd E Hcf Hnc Hnr HE HE0.
unfold c_frame in Hcf. cbv zeta in Hcf.
destruct Hcf as (_&_&_&_&_&_&_&Hbsm&Hbsm2&_&_&_&_&_&_&Hph&_&_&_&_&Hx&_).
unfold phase_fields in Hph. unfold unit_ok. cbn [zp_set_got zp_with zp_ph zp_got].
cbn [fp_complete fp_rawbody] in Hnc, Hnr.
destruct (zp_ph z) as [|bh| |] eqn:Ep.
- destruct Hph as [_ Hexp]. rewrite HE in Hexp. split; [reflexivity|].
  change (Vlong (Int64.repr ZSTD_blockHeaderSize)) with (vlong 3) in Hexp.
  apply vlong_eq in Hexp; [exact Hexp|lia|lia].
- destruct Hph as (c&Hc&_&_&_&Hexp). rewrite Hnr in Hexp. rewrite HE in Hexp.
  destruct Hx as (_&_&c'&Hc'&Hcb&_). rewrite Hc in Hc'. inversion Hc'; subst c'.
  exists c. split; [exact Hc|]. rewrite Hnr. split; [reflexivity|].
  change (Vlong (Int64.repr c)) with (vlong c) in Hexp.
  unfold ZSTD_BLOCKSIZE_MAX in Hbsm2.
  apply vlong_eq in Hexp; [exact Hexp|lia|lia].
- destruct Hph as [_ Hexp]. rewrite HE in Hexp. split; [reflexivity|].
  change (Vlong (Int64.repr 4)) with (vlong 4) in Hexp.
  apply vlong_eq in Hexp; [exact Hexp|lia|lia].
- discriminate.
Qed.

(* the premises of the stable success, unpacked *)
Lemma ld_st_facts : forall a k0 sv ipc opc oc dl E L,
  ld_ok a k0 sv ipc opc oc dl E L -> dc_stable (a_st a) = true ->
  sv_ahead sv = nil /\ sv_pend sv = nil /\ sf_hostage (c3_s k0) = Vint (Int.repr 0) /\
  c_frame (c3_fs k0) (c3_tabs k0) (sv_fp sv) (sv_lay sv) (sv_dd sv) /\
  c_ring true (Some (a_ob a, a_osz a)) (ss_out (dc_ss (a_st a)) ++ dl) (c3_s k0) (sv_fp sv) nil (sv_lay sv) /\
  fp_complete (sv_fp sv) = false /\ fp_rawbody (sv_fp sv) = false /\
  sf_outStart (c3_s k0) = sf_outEnd (c3_s k0) /\ sf_inSize (c3_s k0) + sf_outSize (c3_s k0) <= 2 ^ 32 /\
  0 <= fp_inpos (sv_fp sv) < E /\ 0 < L /\ ipc + L <= a_isz a /\
  sublist 0 opc oc = zbytes (ss_out (dc_ss (a_st a)) ++ dl) /\
  Zlength (ss_out (dc_ss (a_st a)) ++ dl) = opc /\ opc <= a_osz a /\ Zlength oc = a_osz a /\
  bytes_ok (a_sin a ++ sublist (a_ipos a) ipc (a_ibs a)) /\ bytes_ok (sublist ipc (ipc + L) (a_ibs a)) /\
  Zlength (sublist ipc (ipc + L) (a_ibs a)) = L /\ dd_small (sv_dd sv).
Proof.
intros a k0 sv ipc opc oc dl E L Hld Hst.
destruct Hld as (Ha&Hi&Hs&HE&HE0&HL&HLE&Hin&Hout&Hrl0&Hrl&Hbc&Hdd).
destruct Ha as (_&_&_&_&_&_&_&_&_&Hopos&_&Hloc&Hipos&_&Hlibs&Hbibs&_).
unfold call_inv in Hi. cbv zeta in Hi.
destruct Hi as (H1&H2&H3&H4&H5&H6&H7&H8&H9&H10&H11&H12&Hcore&H14&Hstout&_).
rewrite Hst in Hcore, Hstout. specialize (Hstout eq_refl).
destruct (load_facts _ _ _ _ _ Hcore Hs) as (E2 & st2 & HE2 & _ & HPE2 & HE232 & _).
rewrite HE in HE2. apply vlong_eq in HE2; [|lia|lia]. subst E2.
unfold c_core in Hcore. cbv zeta in Hcore.
destruct Hcore as (Hhost & Hcold & Hsz & Hrest). rewrite Hs in Hrest.
replace (zdss_load =? zdss_init) with false in Hrest by reflexivity.
replace (zdss_load =? zdss_loadHeader) with false in Hrest by reflexivity.
destruct Hrest as (_ & Hcf & Hring & _ & Hld & _ & _).
destruct (Hld eq_refl) as (Hpend & Hnc & Hnraw & Hoso & Hinpos & Hpref).
assert (Hah: sf_hostage (c3_s k0) = Vint (Int.repr 0) /\ sv_ahead sv = nil).
{ destruct Hhost as [[Hx _]|[Hh|(_&_&_&_&_&Hx)]]; auto; rewrite Hs in Hx.
  - unfold zdss_load, zdss_init in Hx; lia.
  - unfold zdss_load, zdss_init, zdss_read, zdss_flush in Hx; lia. }
destruct Hah as [Hh0 Hah].
assert (HL': L = a_isz a - ipc \/ L < a_isz a - ipc) by lia.
assert (HLi: ipc + L <= a_isz a) by lia.
assert (Hls: Zlength (ss_out (dc_ss (a_st a)) ++ dl) = opc).
{ apply (f_equal (@Zlength val)) in Hstout. rewrite Zlength_map, Zlength_sublist in Hstout by lia. lia. }
split; [exact Hah|]. split; [exact Hpend|]. split; [exact Hh0|]. split; [exact Hcf|].
split; [rewrite <- Hpend; exact Hring|].
split; [exact Hnc|]. split; [exact Hnraw|]. split; [exact Hoso|]. split; [exact Hsz|].
split; [lia|]. split; [lia|]. split; [exact HLi|].
split; [exact Hstout|]. split; [exact Hls|]. split; [lia|]. split; [exact H3|].
split; [apply Forall_app; split; [exact H9|apply Forall_sublist; exact Hbibs]|].
split; [apply Forall_sublist; exact Hbibs|].
split; [rewrite Zlength_sublist; lia|].
intros x buf Hx. apply (Hdd x buf Hx).
Qed.

End CM_L3StFacts_1.
