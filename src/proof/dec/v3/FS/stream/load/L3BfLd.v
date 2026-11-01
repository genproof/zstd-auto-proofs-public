(* FS3 streaming, case zdss_load: the facts of the loaded unit in buffered mode (the premises of
   P_load_cont_buf unpacked), the stream buffer as loaded, and copies of L3StGen.cur_rel_unget /
   L3StFacts.lcp_unit_z on this chain. *)
Require Export Zstd.proof.dec.v3.FS.stream.load.L3BfStep.
Local Open Scope logic.

Section CM_L3BfLd_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* the unit's bytes loaded before this call belong to the current frame's bytes *)
Lemma lb_cur_rel_unget : forall md sel cd fb hdr z, cur_rel md sel cd fb (FP_zstd hdr z) ->
  match zp_ph z with ZP_body bh => bp_type (block_props_of bh) <> 0 | ZP_end => False | _ => True end ->
  exists fb0, fb = fb0 ++ zp_got z /\ cur_rel md sel cd fb0 (FP_zstd hdr (zp_set_got z nil)).
Proof.
intros md sel cd fb hdr z Hc Hph. unfold cur_rel in *. cbv zeta in *.
cbn [zp_set_got zp_with zp_h zp_dm zp_bsm zp_ign zp_bl zp_ts zp_out zp_ph zp_got] in *.
destruct Hc as (H1&H2&H3&H4&H5&H6&H7&outc&last&Hb&Hfb&Hp).
destruct (zp_ph z) as [|bh| |] eqn:Ep; try contradiction.
- exists (hdr ++ zp_bl z ++ nil). split; [rewrite Hfb, app_nil_r, app_assoc; reflexivity|].
  repeat (split; [assumption|]). exists outc, last. split; [exact Hb|]. split; [reflexivity|].
  destruct Hp as (A&B&_). split; [exact A|]. split; [exact B|]. rewrite Zlength_nil. unfold ZSTD_blockHeaderSize. lia.
- exists (hdr ++ zp_bl z ++ (bh ++ nil)). split; [rewrite Hfb, !app_nil_r, !app_assoc; reflexivity|].
  repeat (split; [assumption|]). exists outc, last. split; [exact Hb|]. split; [reflexivity|].
  destruct Hp as (A&B&c&Hc1&Hc2&Hc3&Hc4). split; [exact A|]. split; [exact B|].
  exists c. split; [exact Hc1|]. split; [exact Hc2|]. split; [rewrite Zlength_nil; lia|].
  rewrite Hc4. destruct (bp_type (block_props_of bh) =? 0) eqn:Eb; [apply Z.eqb_eq in Eb; contradiction|].
  reflexivity.
- exists (hdr ++ zp_bl z ++ nil). split; [rewrite Hfb, app_nil_r, app_assoc; reflexivity|].
  repeat (split; [assumption|]). exists outc, last. split; [exact Hb|]. split; [reflexivity|].
  destruct Hp as (A&B&C&D&_). split; [exact A|]. split; [exact B|]. split; [exact C|]. split; [exact D|].
  rewrite Zlength_nil; lia.
Qed.

(* the unit of a Zstandard frame once loaded: what fs_expected asked for *)
Lemma lb_unit_z : forall fs tabs hdr z l dd E,
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

(* the stream buffer as loaded: the out part is unchanged *)
Lemma lb_ring_out : forall s fp ibs ipc L E,
  Zlength (sf_ring s) = sf_inSize s + sf_outSize s -> 0 <= sf_outSize s ->
  0 <= fp_inpos fp -> 0 <= L -> fp_inpos fp + L = E -> (is_skip fp = false -> E <= sf_inSize s) ->
  0 <= ipc -> ipc + L <= Zlength ibs ->
  sublist (sf_inSize s) (sf_inSize s + sf_outSize s) (ring_load fp (sf_ring s) (fp_inpos fp) ibs ipc L) =
  sublist (sf_inSize s) (sf_inSize s + sf_outSize s) (sf_ring s).
Proof.
intros s fp ibs ipc L E Hl HO HP HL HE Hin Hipc Hib. unfold ring_load.
destruct (is_skip fp) eqn:Hsk; [reflexivity|]. specialize (Hin eq_refl).
apply sublist_skip_eq with (n := fp_inpos fp + L); [lia|].
apply skipn_copy_cells; try lia. rewrite Zlength_map. lia.
Qed.

(* c_ring of the unit view, over the loaded stream buffer *)
Lemma lb_c_ring_unit : forall stable obuf sout s fp pend l inpos ring',
  sublist (sf_inSize s) (sf_inSize s + sf_outSize s) ring' =
    sublist (sf_inSize s) (sf_inSize s + sf_outSize s) (sf_ring s) ->
  c_ring stable obuf sout s fp pend l -> c_ring stable obuf sout (s_load s inpos ring') (fp_unit fp) pend l.
Proof.
intros stable obuf sout s fp pend l inpos ring' Heq H.
destruct fp as [|hb|hdr got|hdr z]; unfold c_ring in *;
  cbn [s_load sf_inBuff sf_inSize sf_outSize sf_outStart sf_outEnd sf_ring sf_outBuff fp_unit fp_bsm
       fp_content fp_fcs fp_ws zp_set_got zp_with zp_h zp_out zp_bsm] in *; rewrite Heq; exact H.
Qed.

(* the premises of the buffered success, unpacked *)
Lemma lb_facts : forall a k0 sv ipc opc oc dl E L,
  ld_ok a k0 sv ipc opc oc dl E L -> dc_stable (a_st a) = false ->
  sv_ahead sv = nil /\ sv_pend sv = nil /\ sf_hostage (c3_s k0) = Vint (Int.repr 0) /\
  c_frame (c3_fs k0) (c3_tabs k0) (sv_fp sv) (sv_lay sv) (sv_dd sv) /\
  c_ring false (Some (a_ob a, a_osz a)) (ss_out (dc_ss (a_st a)) ++ dl) (c3_s k0) (sv_fp sv) nil (sv_lay sv) /\
  fp_complete (sv_fp sv) = false /\ fp_rawbody (sv_fp sv) = false /\
  sf_outStart (c3_s k0) = sf_outEnd (c3_s k0) /\ sf_inSize (c3_s k0) + sf_outSize (c3_s k0) <= 2 ^ 32 /\
  0 <= fp_inpos (sv_fp sv) < E /\ 0 < L /\ fp_inpos (sv_fp sv) + L = E /\ a_ipos a <= ipc /\ ipc + L <= a_isz a /\
  bytes_ok (a_sin a ++ sublist (a_ipos a) ipc (a_ibs a)) /\ bytes_ok (sublist ipc (ipc + L) (a_ibs a)) /\
  Zlength (sublist ipc (ipc + L) (a_ibs a)) = L /\
  sublist (sf_inSize (c3_s k0)) (sf_inSize (c3_s k0) + sf_outSize (c3_s k0)) (ld_ring sv (c3_s k0) (a_ibs a) ipc L) =
    sublist (sf_inSize (c3_s k0)) (sf_inSize (c3_s k0) + sf_outSize (c3_s k0)) (sf_ring (c3_s k0)) /\
  sublist 0 (Zlength (fp_loaded (sv_fp sv))) (sf_ring (c3_s k0)) = zbytes (fp_loaded (sv_fp sv)) /\
  (is_skip (sv_fp sv) = false -> E <= sf_inSize (c3_s k0)).
Proof.
intros a k0 sv ipc opc oc dl E L Hld Hst.
destruct Hld as (Ha&Hi&Hs&HE&HE0&HL&HLE&Hin&Hout&Hrl0&Hrl&Hbc&Hdd).
destruct Ha as (_&_&_&_&_&_&_&_&_&_&_&_&Hipos&_&Hlibs&Hbibs&_).
pose proof Hi as Hi'. unfold call_inv in Hi'. cbv zeta in Hi'.
destruct Hi' as (H1&H2&H3&H4&H5&H6&H7&H8&H9&H10&H11&H12&Hcore&_).
rewrite Hst in Hcore.
destruct (load_facts _ _ _ _ _ Hcore Hs) as (E2 & st2 & HE2 & _ & HPE2 & HE232 & _ & _ & _ & HEin & _).
rewrite HE in HE2. apply vlong_eq in HE2; [|lia|lia]. subst E2.
unfold c_core in Hcore. cbv zeta in Hcore.
destruct Hcore as (Hhost & Hcold & Hsz & Hrest). rewrite Hs in Hrest.
replace (zdss_load =? zdss_init) with false in Hrest by reflexivity.
replace (zdss_load =? zdss_loadHeader) with false in Hrest by reflexivity.
destruct Hrest as (_ & Hcf & Hring & _ & Hldd & _ & _).
destruct (Hldd eq_refl) as (Hpend & Hnc & Hnraw & Hoso & Hinpos & Hpref).
assert (Hah: sf_hostage (c3_s k0) = Vint (Int.repr 0) /\ sv_ahead sv = nil).
{ destruct Hhost as [[Hx _]|[Hh|(_&_&_&_&_&Hx)]]; auto; rewrite Hs in Hx.
  - unfold zdss_load, zdss_init in Hx; lia.
  - unfold zdss_load, zdss_init, zdss_read, zdss_flush in Hx; lia. }
destruct Hah as [Hh0 Hah].
split; [exact Hah|]. split; [exact Hpend|]. split; [exact Hh0|]. split; [exact Hcf|].
split; [rewrite <- Hpend; exact Hring|].
split; [exact Hnc|]. split; [exact Hnraw|]. split; [exact Hoso|]. split; [exact Hsz|].
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [apply Forall_app; split; [exact H9|apply Forall_sublist; exact Hbibs]|].
split; [apply Forall_sublist; exact Hbibs|].
split; [rewrite Zlength_sublist; lia|].
split; [|split; [exact Hpref|exact HEin]].
unfold ld_ring. apply (lb_ring_out _ _ _ _ _ E Hrl0 Hout); try lia; auto.
Qed.

(* the frame's DDict across the call (sv_dd_ok at a later stage) *)
Lemma lb_dd_ok : forall st k k' sv sv', c3_dict k' = c3_dict k -> sv_dd sv' = sv_dd sv ->
  sf_stage (c3_s k) = zdss_load -> sv_dd_ok st k sv -> sv_dd_ok st k' sv'.
Proof.
intros st k k' sv sv' Hd Hdd Hs H. unfold sv_dd_ok, dd_src in *. rewrite Hd, Hdd. intros _ x buf E.
apply H; [rewrite Hs; unfold zdss_read, zdss_load; lia|exact E].
Qed.

End CM_L3BfLd_1.
