(* FS3 streaming, case zdss_read: the loop invariant after a unit read from the input (v2
   StreamSeg_read.v call_inv_next / c_core_rf, v3 context). *)
Require Export Zstd.proof.dec.v3.FS.stream.read.R3RingNew.
Local Open Scope logic.

Section CM_R3Step_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma zstep_bsm : forall z u cnt ts', zp_bsm (zstep z u cnt ts') = zp_bsm z.
Proof.
intros z u cnt ts'. unfold zstep. destruct (zp_ph z); try reflexivity.
- destruct (cblock_size u); [destruct (_ =? 0)|]; reflexivity.
- destruct (_ =? 0); [destruct (match cblock_size bh with Some c => _ | None => false end)|]; reflexivity.
Qed.

Lemma zstep_dm : forall z u cnt ts', zp_dm (zstep z u cnt ts') = zp_dm z.
Proof.
intros z u cnt ts'. unfold zstep. destruct (zp_ph z); try reflexivity.
- destruct (cblock_size u); [destruct (_ =? 0)|]; reflexivity.
- destruct (_ =? 0); [destruct (match cblock_size bh with Some c => _ | None => false end)|]; reflexivity.
Qed.

(* the parameters' header zstd keeps (fParams) is the same before and after a unit *)
Lemma c_frame_fparams_z : forall fs tabs hdr z l dd fs' tabs' z' l',
  c_frame fs tabs (FP_zstd hdr z) l dd -> c_frame fs' tabs' (FP_zstd hdr z') l' dd ->
  zp_h z' = zp_h z -> zp_bsm z' = zp_bsm z -> fs_fParams fs' = fs_fParams fs.
Proof.
intros fs tabs hdr z l dd fs' tabs' z' l' H H' Eh Eb.
destruct H as (_&_&_&_&_&_&Hf&_). destruct H' as (_&_&_&_&_&_&Hf'&_). rewrite Hf, Hf', Eh, Eb. reflexivity.
Qed.

Lemma c_frame_fparams_s : forall fs tabs hdr g l dd fs' tabs' g' l',
  c_frame fs tabs (FP_skip hdr g) l dd -> c_frame fs' tabs' (FP_skip hdr g') l' dd ->
  fs_fParams fs' = fs_fParams fs.
Proof.
intros fs tabs hdr g l dd fs' tabs' g' l' H H'.
destruct H as (_&_&_&_&_&_&_&(h&Hh&_&Hf)&_). destruct H' as (_&_&_&_&_&_&_&(h'&Hh'&_&Hf')&_).
rewrite Hh in Hh'. inversion Hh'; subst h'. rewrite Hf, Hf'. reflexivity.
Qed.

(* c_core at zdss_read / zdss_flush, field by field *)
Lemma c_core_rf3 : forall stable obuf sout k sv,
  sf_hostage (c3_s k) = Vint (Int.repr 0) -> sv_ahead sv = nil ->
  (fs_ddictIsCold (c3_fs k) = Vint (Int.repr 0) \/ fs_ddictIsCold (c3_fs k) = Vint (Int.repr 1)) ->
  sf_inSize (c3_s k) + sf_outSize (c3_s k) <= 2 ^ 32 ->
  (sf_stage (c3_s k) = zdss_read \/ sf_stage (c3_s k) = zdss_flush) ->
  c_frame (c3_fs k) (c3_tabs k) (sv_fp sv) (sv_lay sv) (sv_dd sv) ->
  c_ring stable obuf sout (c3_s k) (sv_fp sv) (sv_pend sv) (sv_lay sv) ->
  (stable = true -> sf_stage (c3_s k) <> zdss_flush) ->
  sf_inPos (c3_s k) = vlong 0 ->
  (fp_rawbody (sv_fp sv) = true \/ fp_loaded (sv_fp sv) = nil \/ fp_complete (sv_fp sv) = true) ->
  match sv_fp sv with FP_skip _ got => got = 0 \/ fp_complete (sv_fp sv) = true | _ => True end ->
  (sf_stage (c3_s k) = zdss_read -> sv_pend sv = nil /\ sf_outStart (c3_s k) = sf_outEnd (c3_s k)) ->
  c_core stable obuf sout k sv.
Proof.
intros stable obuf sout k sv Hh Ha Hcold Hsz Hst Hcf Hr Hstb Hip Hld Hsk Hrd.
unfold c_core. split; [right; left; auto|]. split; [auto|]. split; [auto|].
destruct Hst as [Hst|Hst]; rewrite Hst in Hstb, Hrd |- *;
  unfold zdss_read, zdss_flush, zdss_init, zdss_loadHeader, zdss_load in *; simpl.
all: split; [lia|]. all: split; [exact Hcf|]. all: split; [exact Hr|]. all: split; [exact Hstb|].
all: split; [intros; discriminate|].
all: split; [intros _; split; [exact Hip|split; [exact Hld|exact Hsk]]|].
- exact Hrd.
- intros; discriminate.
Qed.

(* the loop invariant after a unit read from the input (ip advanced to ipc' > ipc, no hostage byte): what
   remains to show is the new context's c_core, its DDict facts and the model part *)
Lemma call_inv_next3 : forall a k sv ipc opc oc dl k' sv' ipc',
  call_inv a k sv ipc opc oc dl -> ipc < ipc' <= a_isz a ->
  c3_stable k' = c3_stable k -> c3_dict k' = c3_dict k -> c3_par k' = c3_par k -> c3_set k' = c3_set k ->
  sf_mem (c3_s k') = sf_mem (c3_s k) -> sf_held (c3_s k') = sf_held (c3_s k) -> c3_sp k' = c3_sp k ->
  fs_fParams (c3_fs k') = fs_fParams (c3_fs k) ->
  sf_nfp (c3_s k') = sf_nfp (c3_s k) -> sv_ahead sv' = nil ->
  (forall hb, sv_fp sv' <> FP_hdr hb) -> sv_ahead sv = nil ->
  (dc_stable (a_st a) = true -> sf_stage (c3_s k') <> zdss_init ->
     sf_expOut (c3_s k') = (a_obf a, (vlong (a_osz a), vlong (a_opos a)))) ->
  c_core (dc_stable (a_st a)) (Some (a_ob a, a_osz a)) (ss_out (dc_ss (a_st a)) ++ dl) k' sv' ->
  sv_dd_ok (a_st a) k' sv' ->
  alive_ok (a_st a) k' sv' (a_sin a ++ sublist (a_ipos a) ipc' (a_ibs a)) (ss_out (dc_ss (a_st a)) ++ dl) ->
  call_inv a k' sv' ipc' opc oc dl.
Proof.
intros a k sv ipc opc oc dl k' sv' ipc' Hi Hipc Hstb Hdi Hpar Hset Hmem Hheld Hsp Hfp Hnfp Hah Hnh Hah0 Hexp Hcore Hdd Hm.
destruct Hi as (H1&H2&H3&H4&H5&H6&H7&H8&Hbin&H10&H11&H12&_&_&Hstout&_&_&_&_&Hsin&_).
rewrite Hah0, app_nil_r in Hsin.
destruct H8 as (B1&B2&B3&B4&B5&B6&B7).
unfold call_inv. cbv zeta. rewrite Hah, app_nil_r, Hnfp.
split; [lia|]. do 6 (split; [assumption|]).
split; [unfold base_call, mem_call, mem_room in *; rewrite Hstb, Hpar, Hset, Hdi, Hfp, Hmem, Hheld; auto 10|].
split; [assumption|]. split; [assumption|].
split; [left; lia|].
split; [assumption|].
split; [exact Hcore|]. split; [exact Hdd|].
split; [exact Hstout|].
split; [intros []; reflexivity|].
split; [intros; lia|].
split; [exact Hm|].
split; [intros _ hb Hf; exfalso; exact (Hnh hb Hf)|].
split; [rewrite ?app_nil_r; exact Hsin|]. split; [exact Hexp|]. intros; lia.
Qed.

Lemma sv_dd_ok_same : forall st k k' sv sv', c3_dict k' = c3_dict k -> sv_dd sv' = sv_dd sv ->
  sf_stage (c3_s k) = zdss_read -> sv_dd_ok st k sv -> sv_dd_ok st k' sv'.
Proof.
intros st k k' sv sv' Hd Hdd Hs H. unfold sv_dd_ok, dd_src in *. rewrite Hd, Hdd. intros _ x buf E.
apply H; [rewrite Hs; lia|exact E].
Qed.

Lemma cur_dict_ok_same : forall st k k' cd, c3_dict k' = c3_dict k -> fs_fParams (c3_fs k') = fs_fParams (c3_fs k) ->
  cur_dict_ok st k cd -> cur_dict_ok st k' cd.
Proof. intros st k k' cd Hd Hf H. unfold cur_dict_ok in *. rewrite Hd, Hf. exact H. Qed.

End CM_R3Step_1.
