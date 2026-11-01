(* valid_dict_api main: the frees and the return (VDA3Defs.VDA_epi_ok). *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.harness.valid_dict_api.WTopSpecs_valid_dict_api.
Require Import Zstd.proof.harness.valid_dict_api.VDA3Defs.

Lemma vda_dd_res_split DD gv (ddv: list val) i : Zlength ddv = 3 -> 0 <= i < 3 ->
  dd_res DD gv (sublist i 3 ddv) =
  ((if eq_dec (Znth i ddv) nullval then emp else EX x: ddict_st, DD gv (Znth i ddv) x) *
   dd_res DD gv (sublist (i + 1) 3 ddv))%logic.
Proof.
  intros Hl Hi. rewrite (sublist_split i (i + 1) 3) by lia.
  rewrite sublist_len_1 by lia. reflexivity.
Qed.

Lemma vda_epi_ok DC DD WG WDS : VDA_epi_ok DC DD WG WDS.
Proof.
  intros Espec gv v_dd n cap dn src buf dctx st ddv.
  unfold VDA_E, VDA_Delta, VDA_R, VDA_epi_s.
  Intros.
  abbreviate_semax.
  forward_call (gv, dctx, Some st).
  forward_for_simple_bound 3 (EX i: Z,
    PROP ()
    LOCAL (temp _dctx dctx; temp _src src; temp _buf buf; lvar _dd t_ddp v_dd; gvars gv)
    SEP (mem_mgr gv; zstd_globals gv; @data_at HOK_valid_dict_api.CompSpecs Tsh t_ddp ddv v_dd;
         dd_res DD gv (sublist i 3 ddv);
         @malloc_token HOK_valid_dict_api.CompSpecs Ews (tarray tuchar (Z.max 1 n)) src;
         @data_at_ HOK_valid_dict_api.CompSpecs Ews (tarray tuchar (Z.max 1 n)) src;
         @malloc_token HOK_valid_dict_api.CompSpecs Ews (tarray tuchar (cap + 1 + dn)) buf;
         @data_at_ HOK_valid_dict_api.CompSpecs Ews (tarray tuchar (cap + 1 + dn)) buf; TT))%assert.
  { rewrite sublist_same by lia. entailer!. }
  { assert (Hpn: is_pointer_or_null (Znth i ddv)) by (apply (proj1 (Forall_Znth ddv _) H0); lia).
    unfold t_ddp. forward.
    rewrite (vda_dd_res_split DD gv ddv i H) by lia.
    destruct (eq_dec (Znth i ddv) nullval) as [E|E].
    - forward_call (gv, Znth i ddv, @None ddict_st). entailer!. unfold t_ddp; entailer!.
    - Intros x. forward_call (gv, Znth i ddv, Some x). unfold t_ddp; entailer!. }
  rewrite sublist_nil.
  forward_call (tarray tuchar (Z.max 1 n), src, gv).
  { rewrite if_false by (destruct src; try contradiction; discriminate). cancel. }
  forward_call (tarray tuchar (cap + 1 + dn), buf, gv).
  { rewrite if_false by (destruct buf; try contradiction; discriminate). cancel. }
  eapply semax_pre with (P' := PROP () LOCAL (lvar _dd (tarray (tptr t_ddict) 3) v_dd)
    SEP (@data_at_ HOK_valid_dict_api.CompSpecs Tsh (tarray (tptr t_ddict) 3) v_dd; TT)).
  { unfold t_ddp. entailer!. }
  forward.
  cancel.
Qed.
