(* FS3 one-shot frames, ZSTD_decompressMultiFrame: the DDict of each frame (the local variable
   `ddict` after fix F4's probe) and the resources around the calls of one loop iteration. *)
Require Export Zstd.proof.dec.v3.FS.frames.Multi3Ser.
Local Open Scope logic.

Section CM_Multi3Res_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* the dictionary a frame is begun with when the variable `ddict` is qv: the argument a itself (qv = its DDict,
   also NULL for no DDict), else the set's DDict qv *)
Definition mf_dict (a: darg) (l: list (val * ddict_st)) (shk: share) (qv: val) : darg :=
  if veqb qv (darg_ddict a) then a
  else match find (fun e => veqb (fst e) qv) l with
       | Some e => DA_ddict (dd_x qv (snd e)) (dd_buf (snd e)) shk
       | None => a
       end.

(* the selection the spec's claim uses: the probe's with the selection and a DDict argument, else none *)
Definition mf_sel (pr: dparams) (sp: val) (a: darg) (l: list (val * ddict_st)) (tbl: list val) : Z -> option dict_model :=
  if andb (sel_on pr sp) (negb (veqb (darg_ddict a) nullval)) then psel l tbl else sel_none.

(* `ddict` after the probe of fix F4 on the bytes sfr (getFrameHeader_advanced on all of them) *)
Definition mf_probe (pr: dparams) (sp: val) (a: darg) (l: list (val * ddict_st)) (tbl: list val) (qv: val)
    (sfr: list Z) : val :=
  if andb (sel_on pr sp) (negb (veqb (darg_ddict a) nullval)) then
    match get_frame_header_m (dp_fmt pr =? 1) sfr with
    | FH_ok h => let x := hs_probe l tbl (fh_dictID h) in if eq_dec x nullval then qv else x
    | _ => qv
    end
  else qv.

(* `ddict`: the argument's DDict, or (selection, a DDict argument) one of the set *)
Definition qv_ok (pr: dparams) (sp: val) (a: darg) (l: list (val * ddict_st)) (qv: val) : Prop :=
  qv = darg_ddict a \/ (sel_on pr sp = true /\ darg_ddict a <> nullval /\ In qv (map fst l)).

(* the context's dictionary fields: the initial ones, or (selection) a DDict of the set *)
Definition dc_ok (pr: dparams) (sp: val) (l: list (val * ddict_st)) (d dcur: dfields) : Prop :=
  dcur = d \/ (sel_on pr sp = true /\ exists q, In q (map fst l) /\ dcur = switch_fields q).

Section R.
Variable DENT : dent_pred.

(* what ZSTD_decompressBegin_usingDict / usingDDict take of the frame's dictionary (with a DDict's allocation
   tokens, which the call does not touch: Multi3_body frames them around it) *)
Definition begin_res (gv: globals) (a: darg) : mpred :=
  match a with
  | DA_none => emp
  | DA_dict sh pk b => data_at sh (tarray tuchar (Zlength b)) (zbytes b) pk
  | DA_ddict x buf sh => ddict_struct x buf * DENT gv (dx_q x) (ddx_ent x) * ddict_mem x buf
  end.

(* the selection's resources ZSTD_decompressFrame_spec3 takes, with the tables' DDict ox (lent: the local one) *)
Definition mf_fsel (gv: globals) (p: val) (pr: dparams) (sp: val) (dcur: dfields) (l: list (val * ddict_st))
    (tbl: list val) (xq: option (val * val)) (lent: bool) (am: option cmem) (hb: Z) (ox: option ddx) : mpred :=
  sel_any DENT gv p pr sp dcur l tbl xq lent am hb * dent_of DENT gv ox.

End R.

End CM_Multi3Res_1.
