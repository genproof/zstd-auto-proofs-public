(* Group HUF split into five sub-groups, each a subtree_ok obligation of its own
   against the group's context G_HUF and the exports of the other sub-groups it calls.  BHuf.v assembles
   them with BCompose.subtree_compose. *)
Require Export Zstd.proof.dec.B.huf.HufIface.
Local Open Scope logic.

(* the context of group HUF (BGroups.HUF_obligation) *)
Definition G_HUF : funspecs := G_B0 ++ ENT_exports.

(* X1T: building an X1 table *)
Definition ids_X1T : list ident := [ _HUF_DEltX1_set4; _HUF_rescaleStats; _HUF_readDTableX1_wksp ].
Definition X1T_exports : funspecs := [ HUF_readDTableX1_wksp_spec ].
Definition X1T_imports : funspecs := [ HUF_getDTableDesc_spec ].

(* X2T: building an X2 table (the internal specifications of the fill functions are X2T's choice) *)
Definition ids_X2T : list ident :=
  [ _HUF_buildDEltX2U32; _HUF_buildDEltX2; _HUF_fillDTableX2ForWeight; _HUF_fillDTableX2Level2;
    _HUF_fillDTableX2; _HUF_readDTableX2_wksp ].
Definition X2T_exports : funspecs := [ HUF_readDTableX2_wksp_spec ].
Definition X2T_imports : funspecs := [ HUF_getDTableDesc_spec ].

(* X1D: decoding 1 / 4 streams with an X1 table *)
Definition ids_X1D : list ident :=
  [ _HUF_decodeSymbolX1; _HUF_decodeStreamX1; _HUF_decompress1X1_usingDTable_internal_body;
    _HUF_decompress4X1_usingDTable_internal_body; _HUF_decompress4X1_usingDTable_internal_default;
    _HUF_decompress1X1_usingDTable_internal; _HUF_decompress4X1_usingDTable_internal ].
Definition X1D_exports : funspecs :=
  [ HUF_decompress1X1_usingDTable_internal_spec; HUF_decompress4X1_usingDTable_internal_spec ].
Definition X1D_imports : funspecs :=
  [ HUF_getDTableDesc_spec; HUF_decompress4X1_usingDTable_internal_fast_c_loop_spec;
    HUF_decompress4X1_usingDTable_internal_fast_spec ].

(* X2D: decoding 1 / 4 streams with an X2 table *)
Definition ids_X2D : list ident :=
  [ _HUF_decodeSymbolX2; _HUF_decodeLastSymbolX2; _HUF_decodeStreamX2;
    _HUF_decompress1X2_usingDTable_internal_body; _HUF_decompress4X2_usingDTable_internal_body;
    _HUF_decompress4X2_usingDTable_internal_default; _HUF_decompress4X2_usingDTable_internal;
    _HUF_decompress1X2_usingDTable_internal ].
Definition X2D_exports : funspecs :=
  [ HUF_decompress1X2_usingDTable_internal_spec; HUF_decompress4X2_usingDTable_internal_spec ].
Definition X2D_imports : funspecs :=
  [ HUF_getDTableDesc_spec; HUF_decompress4X2_usingDTable_internal_fast_c_loop_spec;
    HUF_decompress4X2_usingDTable_internal_fast_spec ].

(* TOP: the descriptor, the dead fast loops, the selector, the entry points *)
Definition ids_TOP : list ident :=
  [ _HUF_getDTableDesc; _HUF_getDTableLog; _HUF_initFastDStream; _HUF_DecompressFastArgs_init;
    _HUF_initRemainingDStream; _HUF_decompress4X1_usingDTable_internal_fast_c_loop;
    _HUF_decompress4X1_usingDTable_internal_fast; _HUF_decompress4X1_DCtx_wksp;
    _HUF_decompress4X2_usingDTable_internal_fast_c_loop; _HUF_decompress4X2_usingDTable_internal_fast;
    _HUF_decompress4X2_DCtx_wksp; _HUF_selectDecoder; _HUF_decompress1X_usingDTable;
    _HUF_decompress1X1_DCtx_wksp; _HUF_decompress4X_usingDTable; _HUF_decompress4X_hufOnly_wksp ].
Definition TOP_exports : funspecs :=
  [ HUF_getDTableDesc_spec; HUF_decompress4X1_usingDTable_internal_fast_c_loop_spec;
    HUF_decompress4X1_usingDTable_internal_fast_spec; HUF_decompress4X2_usingDTable_internal_fast_c_loop_spec;
    HUF_decompress4X2_usingDTable_internal_fast_spec;
    HUF_decompress1X1_DCtx_wksp_spec; HUF_decompress4X_hufOnly_wksp_spec;
    HUF_decompress1X_usingDTable_spec; HUF_decompress4X_usingDTable_spec ].
Definition TOP_imports : funspecs :=
  [ HUF_readDTableX1_wksp_spec; HUF_readDTableX2_wksp_spec;
    HUF_decompress1X1_usingDTable_internal_spec; HUF_decompress4X1_usingDTable_internal_spec;
    HUF_decompress1X2_usingDTable_internal_spec; HUF_decompress4X2_usingDTable_internal_spec ].

Definition X1T_obligation : Prop := subtree_ok ids_X1T X1T_exports (G_HUF ++ X1T_imports).
Definition X2T_obligation : Prop := subtree_ok ids_X2T X2T_exports (G_HUF ++ X2T_imports).
Definition X1D_obligation : Prop := subtree_ok ids_X1D X1D_exports (G_HUF ++ X1D_imports).
Definition X2D_obligation : Prop := subtree_ok ids_X2D X2D_exports (G_HUF ++ X2D_imports).
Definition TOP_obligation : Prop := subtree_ok ids_TOP TOP_exports (G_HUF ++ TOP_imports).
