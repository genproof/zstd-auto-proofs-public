(* FS3 streaming: the error returns of ZSTD_decompressStream from inside the loop, as statements
   (RET3), so that the segment proofs assume them (MF3 -> RET3 -> ...) while S3Ret proves them (RET3_ok).
   The statements are fixed: both sides rely on them.  v2's StreamRet proof was the template. *)
Require Export Zstd.proof.dec.v3.FS.stream.S3Mem.
Local Open Scope logic.

Section CM_S3RetStmts_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* the state after an error returned with input->pos = ip (ipos, or isz without a hostage byte) and
   output->pos unchanged *)
Definition ret_st (a: dsa) (r ip: Z) : dctx_st :=
  let st := a_st a in let ss := dc_ss st in
  set_last
    (set_ss st {| ss_in := ss_in ss ++ sublist (a_ipos a + ss_ahead ss) (ip + ss_ahead ss) (a_ibs a);
                  ss_out := ss_out ss ++ nil; ss_stall := ss_stall ss; ss_err := is_error_code r;
                  ss_obuf := if dc_stable st then Some (a_obf a, a_osz a) else None; ss_ahead := ss_ahead ss ;
                  ss_calls := ss_calls ss ++ [(sublist (a_ipos a) (a_isz a) (a_ibs a), a_osz a - a_opos a)] |})
    (Some stream_mark).

(* the state with input->pos = ip (written before an error return) *)
Definition ds_S_ip DENT TABS (a: dsa) (w: lw) (ip: Z) : list mpred :=
  [data_at Tsh (tptr tschar) (offset_val (w_opc w) (a_ob a)) (a_vop a); pws_pred (a_W a); mem_mgr (a_gv a);
   zstd_globals (a_gv a); ctx_rep3 DENT TABS (a_gv a) (a_d a) (w_k w);
   dict_res (DD3x DENT) (a_gv a) Ews (dc_dict (a_st a));
   set_res (DD3x DENT) (a_gv a) Ews (dc_set (a_st a)) (dc_dict (a_st a));
   data_at (a_sho a) t_outBuffer (a_obf a, (vlong (a_osz a), vlong (a_opos a))) (a_outp a);
   data_at (a_shi a) t_inBuffer (a_ibf a, (vlong (a_isz a), vlong ip)) (a_inp a);
   data_at (a_shob a) (tarray tuchar (a_osz a)) (w_oc w) (a_ob a);
   data_at (a_shb a) (tarray tuchar (a_isz a)) (zbytes (a_ibs a)) (a_ib a)].

(* an error returned as it is, before input->pos / output->pos are written (in.pos = ipos, out.pos = opos):
   the stream's claims hold with the bytes read so far (ss_in) and nothing delivered by this call *)
Definition P_ret_err_ok : Prop :=
  forall DENT TABS BR (a: dsa) (w: lw) (r: Z),
  TABS_OK TABS -> dsa_ok a -> start_ok a -> base_call (a_st a) (w_k w) ->
  Zlength (w_oc w) = a_osz a -> sublist 0 (a_opos a) (w_oc w) = sublist 0 (a_opos a) (a_oc a) ->
  0 <= r <= Int64.max_unsigned -> err_why a r ->
  PROPx [] (LOCALx (ds_LI_L a w) (SEPx (ds_LI_S DENT TABS a w))) |--
    RA_return (ds_R DENT TABS BR a) (Some (Vlong (Int64.repr r))).

(* an error returned after input->pos = input->size (zdss_loadHeader, more input than the header needs):
   all of the caller's input counts as read *)
Definition P_ret_err_end_ok : Prop :=
  forall DENT TABS BR (a: dsa) (w: lw) (r: Z),
  TABS_OK TABS -> dsa_ok a -> start_ok a -> ss_ahead (dc_ss (a_st a)) = 0 -> base_call (a_st a) (w_k w) ->
  Zlength (w_oc w) = a_osz a -> sublist 0 (a_opos a) (w_oc w) = sublist 0 (a_opos a) (a_oc a) ->
  0 <= r <= Int64.max_unsigned -> err_why a r ->
  PROPx [] (LOCALx (ds_LI_L a w) (SEPx (ds_S_ip DENT TABS a w (a_isz a)))) |--
    RA_return (ds_R DENT TABS BR a) (Some (Vlong (Int64.repr r))).

Definition RET3 : Prop := P_ret_err_ok /\ P_ret_err_end_ok.

(* the same two returns against the full specification (S3Main.ds_R_x): the model fails on the call too, or the error
   is a memory allocation (S3Main.ex_err) *)
Definition P_ret_err_ok_x : Prop :=
  forall DENT TABS BR (a: dsa) (w: lw) (r: Z),
  TABS_OK TABS -> dsa_ok a -> start_ok a -> base_call (a_st a) (w_k w) ->
  Zlength (w_oc w) = a_osz a -> sublist 0 (a_opos a) (w_oc w) = sublist 0 (a_opos a) (a_oc a) ->
  0 <= r <= Int64.max_unsigned -> err_why a r -> ex_err a r ->
  PROPx [] (LOCALx (ds_LI_L a w) (SEPx (ds_LI_S DENT TABS a w))) |--
    RA_return (ds_R_x DENT TABS BR a) (Some (Vlong (Int64.repr r))).

Definition P_ret_err_end_ok_x : Prop :=
  forall DENT TABS BR (a: dsa) (w: lw) (r: Z),
  TABS_OK TABS -> dsa_ok a -> start_ok a -> ss_ahead (dc_ss (a_st a)) = 0 -> base_call (a_st a) (w_k w) ->
  Zlength (w_oc w) = a_osz a -> sublist 0 (a_opos a) (w_oc w) = sublist 0 (a_opos a) (a_oc a) ->
  0 <= r <= Int64.max_unsigned -> err_why a r -> ex_err a r ->
  PROPx [] (LOCALx (ds_LI_L a w) (SEPx (ds_S_ip DENT TABS a w (a_isz a)))) |--
    RA_return (ds_R_x DENT TABS BR a) (Some (Vlong (Int64.repr r))).

Definition RET3x : Prop := P_ret_err_ok_x /\ P_ret_err_end_ok_x.

Lemma ret3x_err_ok : RET3x -> P_ret_err_ok_x.
Proof. intros [H _]; exact H. Qed.
Lemma ret3x_err_end_ok : RET3x -> P_ret_err_end_ok_x.
Proof. intros [_ H]; exact H. Qed.

Lemma ret3_err_ok : RET3 -> P_ret_err_ok.
Proof. intros [H _]; exact H. Qed.
Lemma ret3_err_end_ok : RET3 -> P_ret_err_end_ok.
Proof. intros [_ H]; exact H. Qed.

End CM_S3RetStmts_1.
