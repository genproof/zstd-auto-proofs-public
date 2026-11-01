(* valid_dict_api main: the prologue's segments (VDA3Defs.VDA_pro_ok), their statements and the states
   between them.  The prologue is the spine of main's body (Ssequence s0 (Ssequence s1 ...)) up to the allocation check:
     s0..s6   : mode = choose(7), nd/which/cap/fail, dd[i] = NULL, mode 0's nd          (VDA3Pro.v)       -> VDA_P1
     s7       : the w_dict loop with mode 0's gp_assumes                               (VDA3ProWD.v)     -> VDA_P2
     s8..s10  : which, wd = &vd_wd[which], gp_assume(!wd->formatted) for modes 1/3/4    (VDA3Pro.v)       -> VDA_P3
     s11      : mode 2's vd_raw and w_series(&sr, &vd_raw), else w_series(&sr, wd)      (VDA3ProWS.v)     -> VDA_P4
     s12..s15 : mode 0's frames gp_assumes, mode 4's gp_assume, dn = wd->n, cap          (VDA3ProFR.v)     -> VDA_P5
     s16..s21 : src, buf, dctx, dst, dict                                               (VDA3Pro.v)       -> VDA_B *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.harness.valid_dict_api.WTopSpecs_valid_dict_api.
Require Import Zstd.proof.harness.valid_dict_api.VDA3Defs.

Local Notation HCS := Zstd.proof.harness.valid_dict_api.HOK_valid_dict_api.CompSpecs.

(* ---------- the statements: the elements of the spine of main's body ---------- *)

Fixpoint vda_seq_nth (n: nat) (s: statement) : statement :=
  match n, s with
  | O, Ssequence a _ => a
  | S n', Ssequence _ b => vda_seq_nth n' b
  | _, _ => Sskip
  end.

Definition VDA_spine : statement := ltac:(
  let b := eval cbv delta [f_main fn_body] beta iota in (fn_body f_main) in
  lazymatch b with Ssequence ?s _ => exact s end).

Definition VDA_s7 : statement := ltac:(let x := eval cbv [vda_seq_nth VDA_spine] in (vda_seq_nth 7 VDA_spine) in exact x).
Definition VDA_s11 : statement := ltac:(let x := eval cbv [vda_seq_nth VDA_spine] in (vda_seq_nth 11 VDA_spine) in exact x).
Definition VDA_s12_15 : statement := ltac:(let x := eval cbv [vda_seq_nth VDA_spine] in
  (Ssequence (Ssequence (Ssequence (vda_seq_nth 12 VDA_spine) (vda_seq_nth 13 VDA_spine)) (vda_seq_nth 14 VDA_spine))
     (vda_seq_nth 15 VDA_spine)) in exact x).

(* ---------- the states ---------- *)

Section States.
Variable WG : globals -> mpred.
Variable WDS : wdict -> reptype t_wstate -> Prop.

(* vd_wd[i..3), still zero *)
Definition vda_rest (gv: globals) (i: Z) : mpred :=
  @data_at HCS Ews (tarray t_wdict (3 - i)) (Zrepeat (@zero_val HCS t_wdict) (3 - i)) (vda_wd_addr gv i).

(* after s0..s6: the mode and the number of dictionaries *)
Definition VDA_P1 (gv: globals) (v_dd: val) (mode nd: Z) : environ -> mpred :=
  PROP (0 <= mode < 7; if mode =? 0 then 2 <= nd <= 3 else nd = 1)
  LOCAL (temp _mode (vu mode); temp _nd (vu nd); temp _which (vu 0); temp _cap (vl 0); temp _fail (vu 0);
         lvar _dd t_ddp v_dd; gvars gv)
  SEP (mem_mgr gv; zstd_globals gv; WG gv;
       @data_at HCS Ews t_wseries (@zero_val HCS t_wseries) (gv _x_valid_dict_api__sr);
       vda_rest gv 0;
       @data_at HCS Ews t_wdict (@zero_val HCS t_wdict) (gv _vd_raw);
       @data_at HCS Tsh t_ddp (Zrepeat nullval 3) v_dd;
       TT).

(* the facts of the dictionaries written by the w_dict loop *)
Definition vda_wds_facts (mode nd: Z) (wds: list wdict) : Prop :=
  Zlength wds = nd /\ Forall dict_facts wds /\ Forall wdict_wf wds /\
  (mode = 0 -> Forall (fun w => wd_formatted w = true) wds /\ NoDup (map wd_id wds)) /\
  Forall (fun w => wd_formatted w = true -> wd_id w <> 0) wds.

(* after s7: the dictionaries wds in vd_wd[0..nd) *)
Definition VDA_P2 (gv: globals) (v_dd: val) (mode nd: Z) (wds: list wdict) : environ -> mpred :=
  PROP (0 <= mode < 7; if mode =? 0 then 2 <= nd <= 3 else nd = 1; vda_wds_facts mode nd wds)
  LOCAL (temp _mode (vu mode); temp _nd (vu nd); temp _which (vu 0); temp _cap (vl 0); temp _fail (vu 0);
         lvar _dd t_ddp v_dd; gvars gv)
  SEP (mem_mgr gv; zstd_globals gv; WG gv;
       @data_at HCS Ews t_wseries (@zero_val HCS t_wseries) (gv _x_valid_dict_api__sr);
       vda_wds_from WDS gv 0 wds; vda_rest gv nd;
       @data_at HCS Ews t_wdict (@zero_val HCS t_wdict) (gv _vd_raw);
       @data_at HCS Tsh t_ddp (Zrepeat nullval 3) v_dd;
       TT).

(* the choice of wd = vd_wd[which] *)
Definition vda_which_facts (mode nd which: Z) (wds: list wdict) (wd: wdict) : Prop :=
  0 <= which < nd /\ (mode <> 0 -> which = 0) /\ nth_error wds (Z.to_nat which) = Some wd /\
  (mode = 1 \/ mode = 3 \/ mode = 4 -> wd_formatted wd = false).

(* after s8..s10: wd = vd_wd[which] borrowed from vd_wd[0..nd) *)
Definition VDA_P3 (gv: globals) (v_dd: val) (mode nd which: Z) (wds: list wdict) (wd: wdict) : environ -> mpred :=
  PROP (0 <= mode < 7; if mode =? 0 then 2 <= nd <= 3 else nd = 1; vda_wds_facts mode nd wds;
        vda_which_facts mode nd which wds wd)
  LOCAL (temp _mode (vu mode); temp _nd (vu nd); temp _cap (vl 0); temp _fail (vu 0);
         temp _wd (vda_wd_addr gv which); lvar _dd t_ddp v_dd; gvars gv)
  SEP (mem_mgr gv; zstd_globals gv; WG gv;
       @data_at HCS Ews t_wseries (@zero_val HCS t_wseries) (gv _x_valid_dict_api__sr);
       wdict_rep WDS Ews wd (vda_wd_addr gv which);
       wdict_rep WDS Ews wd (vda_wd_addr gv which) -* vda_wds_from WDS gv 0 wds;
       @data_at HCS Ews t_wdict (@zero_val HCS t_wdict) (gv _vd_raw);
       @data_at HCS Tsh t_ddp (Zrepeat nullval 3) v_dd;
       TT).

(* the series written (mode 2: for wd's bytes as raw content) *)
Definition vda_series_facts (mode: Z) (wd: wdict) (ws: wseries) : Prop :=
  (mode = 2 -> wd_formatted wd = true /\ Zlength (wd_bytes wd) <= 4096) /\
  series_facts (vda_dm mode wd) ws /\ wseries_wf ws /\ series_dwin (vda_dm mode wd) ws.

(* after s11: the series ws in sr *)
Definition VDA_P4 (gv: globals) (v_dd: val) (mode nd which: Z) (wds: list wdict) (wd: wdict) (ws: wseries)
    : environ -> mpred :=
  PROP (0 <= mode < 7; if mode =? 0 then 2 <= nd <= 3 else nd = 1; vda_wds_facts mode nd wds;
        vda_which_facts mode nd which wds wd; vda_series_facts mode wd ws)
  LOCAL (temp _mode (vu mode); temp _nd (vu nd); temp _cap (vl 0); temp _fail (vu 0);
         temp _wd (vda_wd_addr gv which); lvar _dd t_ddp v_dd; gvars gv)
  SEP (mem_mgr gv; zstd_globals gv;
       @data_at HCS Ews t_wseries (wseries_val ws) (gv _x_valid_dict_api__sr);
       wdict_rep WDS Ews wd (vda_wd_addr gv which);
       wdict_rep WDS Ews wd (vda_wd_addr gv which) -* vda_wds_from WDS gv 0 wds;
       @data_at HCS Tsh t_ddp (Zrepeat nullval 3) v_dd;
       TT).

(* the gp_assumes on the frames and the capacity *)
Definition vda_cap_facts (mode: Z) (wd: wdict) (ws: wseries) (cap: Z) : Prop :=
  (mode = 0 -> Forall (fun f => wi_skippable f = true \/ (wi_did_size f <> 0 /\ wi_did f = wd_id wd)) (ws_frames ws)) /\
  (mode = 4 -> Zlength (ws_frames ws) = 1 /\ wi_skippable (hd winfo0 (ws_frames ws)) = false) /\
  (mode = 5 \/ mode = 6 -> cap = 0) /\ 0 <= cap <= Zlength (ws_content ws) + 16.

(* after s12..s15: dn and cap *)
Definition VDA_P5 (gv: globals) (v_dd: val) (mode nd which: Z) (wds: list wdict) (wd: wdict) (ws: wseries) (cap: Z)
    : environ -> mpred :=
  PROP (0 <= mode < 7; if mode =? 0 then 2 <= nd <= 3 else nd = 1; vda_wds_facts mode nd wds;
        vda_which_facts mode nd which wds wd; vda_series_facts mode wd ws; vda_cap_facts mode wd ws cap)
  LOCAL (temp _mode (vu mode); temp _nd (vu nd); temp _cap (vl cap); temp _fail (vu 0);
         temp _wd (vda_wd_addr gv which); temp _dn (vl (Zlength (wd_bytes wd))); lvar _dd t_ddp v_dd; gvars gv)
  SEP (mem_mgr gv; zstd_globals gv;
       @data_at HCS Ews t_wseries (wseries_val ws) (gv _x_valid_dict_api__sr);
       wdict_rep WDS Ews wd (vda_wd_addr gv which);
       wdict_rep WDS Ews wd (vda_wd_addr gv which) -* vda_wds_from WDS gv 0 wds;
       @data_at HCS Tsh t_ddp (Zrepeat nullval 3) v_dd;
       TT).

End States.

(* ---------- the segments delegated to their own files ---------- *)

Definition VDA_wd_ok : Prop :=
  forall DC DD WG WDS (Espec: OracleKind) gv v_dd mode nd,
    @semax HCS Espec (VDA_Delta DC DD WG WDS) (VDA_P1 WG gv v_dd mode nd) VDA_s7
      (normal_ret_assert (EX wds: list wdict, VDA_P2 WG WDS gv v_dd mode nd wds)).

Definition VDA_ws_ok : Prop :=
  forall DC DD WG WDS (Espec: OracleKind) gv v_dd mode nd which wds wd,
    @semax HCS Espec (VDA_Delta DC DD WG WDS) (VDA_P3 WG WDS gv v_dd mode nd which wds wd) VDA_s11
      (normal_ret_assert (EX ws: wseries, VDA_P4 WDS gv v_dd mode nd which wds wd ws)).

Definition VDA_fr_ok : Prop :=
  forall DC DD WG WDS (Espec: OracleKind) gv v_dd mode nd which wds wd ws,
    @semax HCS Espec (VDA_Delta DC DD WG WDS) (VDA_P4 WDS gv v_dd mode nd which wds wd ws) VDA_s12_15
      (normal_ret_assert (EX cap: Z, VDA_P5 WDS gv v_dd mode nd which wds wd ws cap)).
