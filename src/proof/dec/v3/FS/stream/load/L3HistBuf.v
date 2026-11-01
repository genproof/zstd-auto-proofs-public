(* FS3 streaming, case zdss_load: buffered-mode history of the call (P_load_cont_hist_buf, statement in L3Stmts). *)
Require Import Zstd.proof.dec.v3.FS.stream.load.L3Stmts.
Require Import Zstd.proof.dec.v3.FS.stream.load.L3HbDef.
Local Open Scope logic.

Section CM_L3HistBuf_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma load_cont_hist_buf_ok : P_load_cont_hist_buf.
Proof.
intros a k0 sv ipc opc oc dl E L ostart Hld Hst Hos.
destruct Hld as (_&Hinv&Hs&_&_&_&_&HI&HO&_&Hlr1&Hby&_).
destruct Hinv as (_&_&_&_&_&_&_&_&_&_&_&_&Hcore&_).
rewrite Hst in Hcore.
destruct Hcore as (_&_&_&Hrest). rewrite Hs in Hrest.
replace (zdss_load =? zdss_init) with false in Hrest by reflexivity.
replace (zdss_load =? zdss_loadHeader) with false in Hrest by reflexivity.
destruct Hrest as (_&Hfr&Hring&_&_&_).
destruct Hfr as (_&_&_&_&Hld&_).
set (ring1 := ld_ring sv (c3_s k0) (a_ibs a) ipc L) in *.
set (OC := sublist (sf_inSize (c3_s k0)) (sf_inSize (c3_s k0) + sf_outSize (c3_s k0)) ring1).
assert (HOCb: byte_cells OC) by (unfold OC, byte_cells in *; apply Forall_sublist; exact Hby).
assert (HOCl: Zlength OC = sf_outSize (c3_s k0)) by (unfold OC; rewrite Zlength_sublist by lia; lia).
destruct Hring as (_&_&_&os&oe&Hos'&_&Hoo&Hr). cbv beta iota zeta in Hr.
destruct Hr as (Hoeb&_&_&_&Hl).
destruct (sv_fp sv) as [| | |hdr z] eqn:Hfp; try exact I.
unfold cont_hist, fp_unit. simpl zp_ph.
destruct (zp_ph z); try exact I. intros _ Hcap.
cbn [o_bf oa_base oa_d oa_cap oa_c] in *. rewrite Hfp in Hcap |- *. cbn [is_skip] in Hcap |- *. fold ring1 OC.
unfold lmove. rewrite (proj2 (Z.leb_gt _ 0)) by lia.
destruct (sv_lay sv) as [|eb ec gp|b pe od|b ps pe e].
- split; [apply hb_hist_def; [exact HOCb|lia|lia|exact I]|right; exact HOCb].
- cbn [lay_dd dd_pre] in Hld. destruct Hld as (x&_&->&_&Hbx&_).
  split; [|right; exact HOCb]. apply hb_hist_def; [exact HOCb|lia|lia|].
  unfold ext_of_dict. cbn [hb_ext_ok]. split; [apply hb_zbytes_cells; exact Hbx|lia].
- exact I.
- destruct Hl as (_&->&Hpe&Hpc&Hroom&_).
  destruct (pe =? ostart).
  + split; [|right; exact HOCb]. apply hb_hist_def; [exact HOCb|lia|lia|].
    destruct e as [|e1 elen|sh eb en ec e1 elen]; cbn [hb_ext_ok]; auto.
    * cbn [lay_room] in Hroom. destruct Hroom as (->&_&Hr1&_). lia.
    * cbn [lay_dd] in Hld. destruct Hld as (_&->&->&->&gp&x&_&->&_&Hbx&_).
      split; [apply hb_zbytes_cells; exact Hbx|lia].
  + split; [|right; exact HOCb]. apply hb_hist_def; [exact HOCb|lia|lia|].
    cbn [hb_ext_ok]. lia.
Qed.

End CM_L3HistBuf_1.
