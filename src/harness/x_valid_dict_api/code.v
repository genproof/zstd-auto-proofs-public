From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Module Info.
  Definition version := "3.15".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "x86".
  Definition model := "64".
  Definition abi := "standard".
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "harness/x_valid_dict_api.c".
  Definition normalized := true.
End Info.

Definition _x_valid_dict_api__W_LL_base : ident := $"x_valid_dict_api__W_LL_base".
Definition _x_valid_dict_api__W_LL_bits : ident := $"x_valid_dict_api__W_LL_bits".
Definition _x_valid_dict_api__W_ML_base : ident := $"x_valid_dict_api__W_ML_base".
Definition _x_valid_dict_api__W_ML_bits : ident := $"x_valid_dict_api__W_ML_bits".
Definition _ZSTD_DCtx_loadDictionary_advanced : ident := $"ZSTD_DCtx_loadDictionary_advanced".
Definition _ZSTD_DCtx_refDDict : ident := $"ZSTD_DCtx_refDDict".
Definition _ZSTD_DCtx_refPrefix_advanced : ident := $"ZSTD_DCtx_refPrefix_advanced".
Definition _ZSTD_DCtx_s : ident := $"ZSTD_DCtx_s".
Definition _ZSTD_DCtx_setParameter : ident := $"ZSTD_DCtx_setParameter".
Definition _ZSTD_DDict_s : ident := $"ZSTD_DDict_s".
Definition _ZSTD_createDCtx : ident := $"ZSTD_createDCtx".
Definition _ZSTD_createDDict : ident := $"ZSTD_createDDict".
Definition _ZSTD_decompressDCtx : ident := $"ZSTD_decompressDCtx".
Definition _ZSTD_decompressStream : ident := $"ZSTD_decompressStream".
Definition _ZSTD_freeDCtx : ident := $"ZSTD_freeDCtx".
Definition _ZSTD_freeDDict : ident := $"ZSTD_freeDDict".
Definition _ZSTD_getErrorCode : ident := $"ZSTD_getErrorCode".
Definition _ZSTD_inBuffer_s : ident := $"ZSTD_inBuffer_s".
Definition _ZSTD_initDStream_usingDDict : ident := $"ZSTD_initDStream_usingDDict".
Definition _ZSTD_initDStream_usingDict : ident := $"ZSTD_initDStream_usingDict".
Definition _ZSTD_isError : ident := $"ZSTD_isError".
Definition _ZSTD_outBuffer_s : ident := $"ZSTD_outBuffer_s".
Definition _ZSTD_resetDStream : ident := $"ZSTD_resetDStream".
Definition ___builtin_ais_annot : ident := $"__builtin_ais_annot".
Definition ___builtin_annot : ident := $"__builtin_annot".
Definition ___builtin_annot_intval : ident := $"__builtin_annot_intval".
Definition ___builtin_bswap : ident := $"__builtin_bswap".
Definition ___builtin_bswap16 : ident := $"__builtin_bswap16".
Definition ___builtin_bswap32 : ident := $"__builtin_bswap32".
Definition ___builtin_bswap64 : ident := $"__builtin_bswap64".
Definition ___builtin_clz : ident := $"__builtin_clz".
Definition ___builtin_clzl : ident := $"__builtin_clzl".
Definition ___builtin_clzll : ident := $"__builtin_clzll".
Definition ___builtin_ctz : ident := $"__builtin_ctz".
Definition ___builtin_ctzl : ident := $"__builtin_ctzl".
Definition ___builtin_ctzll : ident := $"__builtin_ctzll".
Definition ___builtin_debug : ident := $"__builtin_debug".
Definition ___builtin_expect : ident := $"__builtin_expect".
Definition ___builtin_fabs : ident := $"__builtin_fabs".
Definition ___builtin_fabsf : ident := $"__builtin_fabsf".
Definition ___builtin_fmadd : ident := $"__builtin_fmadd".
Definition ___builtin_fmax : ident := $"__builtin_fmax".
Definition ___builtin_fmin : ident := $"__builtin_fmin".
Definition ___builtin_fmsub : ident := $"__builtin_fmsub".
Definition ___builtin_fnmadd : ident := $"__builtin_fnmadd".
Definition ___builtin_fnmsub : ident := $"__builtin_fnmsub".
Definition ___builtin_fsqrt : ident := $"__builtin_fsqrt".
Definition ___builtin_membar : ident := $"__builtin_membar".
Definition ___builtin_memcpy_aligned : ident := $"__builtin_memcpy_aligned".
Definition ___builtin_read16_reversed : ident := $"__builtin_read16_reversed".
Definition ___builtin_read32_reversed : ident := $"__builtin_read32_reversed".
Definition ___builtin_sel : ident := $"__builtin_sel".
Definition ___builtin_sqrt : ident := $"__builtin_sqrt".
Definition ___builtin_unreachable : ident := $"__builtin_unreachable".
Definition ___builtin_va_arg : ident := $"__builtin_va_arg".
Definition ___builtin_va_copy : ident := $"__builtin_va_copy".
Definition ___builtin_va_end : ident := $"__builtin_va_end".
Definition ___builtin_va_start : ident := $"__builtin_va_start".
Definition ___builtin_write16_reversed : ident := $"__builtin_write16_reversed".
Definition ___builtin_write32_reversed : ident := $"__builtin_write32_reversed".
Definition ___compcert_i64_dtos : ident := $"__compcert_i64_dtos".
Definition ___compcert_i64_dtou : ident := $"__compcert_i64_dtou".
Definition ___compcert_i64_sar : ident := $"__compcert_i64_sar".
Definition ___compcert_i64_sdiv : ident := $"__compcert_i64_sdiv".
Definition ___compcert_i64_shl : ident := $"__compcert_i64_shl".
Definition ___compcert_i64_shr : ident := $"__compcert_i64_shr".
Definition ___compcert_i64_smod : ident := $"__compcert_i64_smod".
Definition ___compcert_i64_smulh : ident := $"__compcert_i64_smulh".
Definition ___compcert_i64_stod : ident := $"__compcert_i64_stod".
Definition ___compcert_i64_stof : ident := $"__compcert_i64_stof".
Definition ___compcert_i64_udiv : ident := $"__compcert_i64_udiv".
Definition ___compcert_i64_umod : ident := $"__compcert_i64_umod".
Definition ___compcert_i64_umulh : ident := $"__compcert_i64_umulh".
Definition ___compcert_i64_utod : ident := $"__compcert_i64_utod".
Definition ___compcert_i64_utof : ident := $"__compcert_i64_utof".
Definition ___compcert_va_composite : ident := $"__compcert_va_composite".
Definition ___compcert_va_float64 : ident := $"__compcert_va_float64".
Definition ___compcert_va_int32 : ident := $"__compcert_va_int32".
Definition ___compcert_va_int64 : ident := $"__compcert_va_int64".
Definition ___gp_bits_t : ident := $"__gp_bits_t".
Definition ___gp_fse_t : ident := $"__gp_fse_t".
Definition ___gp_huf_t : ident := $"__gp_huf_t".
Definition ___gp_out_t : ident := $"__gp_out_t".
Definition ___gp_wdict_t : ident := $"__gp_wdict_t".
Definition ___gp_winfo_t : ident := $"__gp_winfo_t".
Definition ___gp_wseries_t : ident := $"__gp_wseries_t".
Definition ___gp_wstate_t : ident := $"__gp_wstate_t".
Definition _acc : ident := $"acc".
Definition _at : ident := $"at".
Definition _at_end : ident := $"at_end".
Definition _b : ident := $"b".
Definition _base : ident := $"base".
Definition _bits : ident := $"bits".
Definition _bits_end_mark : ident := $"bits_end_mark".
Definition _bits_pad : ident := $"bits_pad".
Definition _bits_put : ident := $"bits_put".
Definition _bitsz : ident := $"bitsz".
Definition _blk : ident := $"blk".
Definition _x_valid_dict_api__blk_buf : ident := $"x_valid_dict_api__blk_buf".
Definition _blocks : ident := $"blocks".
Definition _bmax : ident := $"bmax".
Definition _body : ident := $"body".
Definition _bsize : ident := $"bsize".
Definition _buf : ident := $"buf".
Definition _bytes : ident := $"bytes".
Definition _c : ident := $"c".
Definition _c__1 : ident := $"c__1".
Definition _calls : ident := $"calls".
Definition _can4 : ident := $"can4".
Definition _cap : ident := $"cap".
Definition _cell : ident := $"cell".
Definition _checksum : ident := $"checksum".
Definition _choose : ident := $"choose".
Definition _choose_in : ident := $"choose_in".
Definition _cnt : ident := $"cnt".
Definition _code : ident := $"code".
Definition _content : ident := $"content".
Definition _content_n : ident := $"content_n".
Definition _covers : ident := $"covers".
Definition _csize : ident := $"csize".
Definition _cstart : ident := $"cstart".
Definition _d : ident := $"d".
Definition _dctx : ident := $"dctx".
Definition _dd : ident := $"dd".
Definition _depth : ident := $"depth".
Definition _dict : ident := $"dict".
Definition _dictn : ident := $"dictn".
Definition _did : ident := $"did".
Definition _did_size : ident := $"did_size".
Definition _didflag : ident := $"didflag".
Definition _direct_ok : ident := $"direct_ok".
Definition _dn : ident := $"dn".
Definition _ds : ident := $"ds".
Definition _dst : ident := $"dst".
Definition _e : ident := $"e".
Definition _emin : ident := $"emin".
Definition _exact_copy : ident := $"exact_copy".
Definition _f : ident := $"f".
Definition _fail : ident := $"fail".
Definition _fcs : ident := $"fcs".
Definition _fcs_present : ident := $"fcs_present".
Definition _fcsflag : ident := $"fcsflag".
Definition _fi : ident := $"fi".
Definition _form : ident := $"form".
Definition _formatted : ident := $"formatted".
Definition _forms : ident := $"forms".
Definition _forms__1 : ident := $"forms__1".
Definition _found : ident := $"found".
Definition _frame_pos : ident := $"frame_pos".
Definition _fse_build : ident := $"fse_build".
Definition _fse_copy : ident := $"fse_copy".
Definition _fse_has : ident := $"fse_has".
Definition _fse_ok : ident := $"fse_ok".
Definition _fse_pick : ident := $"fse_pick".
Definition _fse_predefined : ident := $"fse_predefined".
Definition _fse_put_description : ident := $"fse_put_description".
Definition _fse_rle : ident := $"fse_rle".
Definition _fse_states : ident := $"fse_states".
Definition _got : ident := $"got".
Definition _gp_assert : ident := $"gp_assert".
Definition _gp_assume : ident := $"gp_assume".
Definition _h : ident := $"h".
Definition _have_huf : ident := $"have_huf".
Definition _have_tab : ident := $"have_tab".
Definition _x_valid_dict_api__hdr : ident := $"x_valid_dict_api__hdr".
Definition _hi : ident := $"hi".
Definition _high : ident := $"high".
Definition _highbit : ident := $"highbit".
Definition _hn : ident := $"hn".
Definition _hp : ident := $"hp".
Definition _hsize : ident := $"hsize".
Definition _huf : ident := $"huf".
Definition _huf_copy : ident := $"huf_copy".
Definition _huf_pick : ident := $"huf_pick".
Definition _huf_put_description : ident := $"huf_put_description".
Definition _huf_put_fse_weights : ident := $"huf_put_fse_weights".
Definition _huf_put_stream : ident := $"huf_put_stream".
Definition _hv : ident := $"hv".
Definition _i : ident := $"i".
Definition _ib : ident := $"ib".
Definition _id : ident := $"id".
Definition _idx : ident := $"idx".
Definition _ilen : ident := $"ilen".
Definition _in : ident := $"in".
Definition _ipos : ident := $"ipos".
Definition _j : ident := $"j".
Definition _j__1 : ident := $"j__1".
Definition _k : ident := $"k".
Definition _kind : ident := $"kind".
Definition _last : ident := $"last".
Definition _leaves : ident := $"leaves".
Definition _left : ident := $"left".
Definition _len : ident := $"len".
Definition _lim : ident := $"lim".
Definition _lit : ident := $"lit".
Definition _litmode : ident := $"litmode".
Definition _ll : ident := $"ll".
Definition _ll_code : ident := $"ll_code".
Definition _lo : ident := $"lo".
Definition _log : ident := $"log".
Definition _lower_mask : ident := $"lower_mask".
Definition _m : ident := $"m".
Definition _main : ident := $"main".
Definition _max : ident := $"max".
Definition _x_valid_dict_api__maxlog : ident := $"x_valid_dict_api__maxlog".
Definition _x_valid_dict_api__maxlog__1 : ident := $"x_valid_dict_api__maxlog__1".
Definition _maxoff : ident := $"maxoff".
Definition _x_valid_dict_api__maxsym : ident := $"x_valid_dict_api__maxsym".
Definition _x_valid_dict_api__maxsym__1 : ident := $"x_valid_dict_api__maxsym__1".
Definition _ml : ident := $"ml".
Definition _ml_code : ident := $"ml_code".
Definition _mode : ident := $"mode".
Definition _n : ident := $"n".
Definition _nb : ident := $"nb".
Definition _nblocks : ident := $"nblocks".
Definition _nd : ident := $"nd".
Definition _x_valid_dict_api__need : ident := $"x_valid_dict_api__need".
Definition _x_valid_dict_api__need__1 : ident := $"x_valid_dict_api__need__1".
Definition _x_valid_dict_api__need__2 : ident := $"x_valid_dict_api__need__2".
Definition _x_valid_dict_api__newhuf : ident := $"x_valid_dict_api__newhuf".
Definition _next : ident := $"next".
Definition _nf : ident := $"nf".
Definition _nf__1 : ident := $"nf__1".
Definition _nforms : ident := $"nforms".
Definition _nframes : ident := $"nframes".
Definition _nlit : ident := $"nlit".
Definition _no : ident := $"no".
Definition _no__1 : ident := $"no__1".
Definition _nondet_u32 : ident := $"nondet_u32".
Definition _nonzero : ident := $"nonzero".
Definition _nopt : ident := $"nopt".
Definition _norm : ident := $"norm".
Definition _nseq : ident := $"nseq".
Definition _nsym : ident := $"nsym".
Definition _x_valid_dict_api__ntab : ident := $"x_valid_dict_api__ntab".
Definition _nused : ident := $"nused".
Definition _nv : ident := $"nv".
Definition _o : ident := $"o".
Definition _ob : ident := $"ob".
Definition _off : ident := $"off".
Definition _olen : ident := $"olen".
Definition _opos0 : ident := $"opos0".
Definition _options : ident := $"options".
Definition _opts : ident := $"opts".
Definition _opts__1 : ident := $"opts__1".
Definition _x_valid_dict_api__order : ident := $"x_valid_dict_api__order".
Definition _out : ident := $"out".
Definition _ov : ident := $"ov".
Definition _p : ident := $"p".
Definition _pick : ident := $"pick".
Definition _pos : ident := $"pos".
Definition _pre : ident := $"pre".
Definition _x_valid_dict_api__pre_LL : ident := $"x_valid_dict_api__pre_LL".
Definition _x_valid_dict_api__pre_ML : ident := $"x_valid_dict_api__pre_ML".
Definition _x_valid_dict_api__pre_OF : ident := $"x_valid_dict_api__pre_OF".
Definition _put8 : ident := $"put8".
Definition _put_bytes : ident := $"put_bytes".
Definition _put_le : ident := $"put_le".
Definition _put_literals_huf : ident := $"put_literals_huf".
Definition _put_literals_raw_rle : ident := $"put_literals_raw_rle".
Definition _q : ident := $"q".
Definition _quickproof_free : ident := $"quickproof_free".
Definition _quickproof_malloc : ident := $"quickproof_malloc".
Definition _r : ident := $"r".
Definition _rem : ident := $"rem".
Definition _remaining : ident := $"remaining".
Definition _rep : ident := $"rep".
Definition _reserve : ident := $"reserve".
Definition _rleb : ident := $"rleb".
Definition _room : ident := $"room".
Definition _s : ident := $"s".
Definition _s1 : ident := $"s1".
Definition _s2 : ident := $"s2".
Definition _s3 : ident := $"s3".
Definition _same : ident := $"same".
Definition _scale : ident := $"scale".
Definition _seg : ident := $"seg".
Definition _single : ident := $"single".
Definition _size : ident := $"size".
Definition _skip_n : ident := $"skip_n".
Definition _skippable : ident := $"skippable".
Definition _slots_after : ident := $"slots_after".
Definition _splits : ident := $"splits".
Definition _x_valid_dict_api__sr : ident := $"x_valid_dict_api__sr".
Definition _src : ident := $"src".
Definition _x_valid_dict_api__st : ident := $"x_valid_dict_api__st".
Definition _st__1 : ident := $"st__1".
Definition _stall_error : ident := $"stall_error".
Definition _stalled : ident := $"stalled".
Definition _start : ident := $"start".
Definition _state : ident := $"state".
Definition _step : ident := $"step".
Definition _streams4 : ident := $"streams4".
Definition _sv : ident := $"sv".
Definition _sym : ident := $"sym".
Definition _symbol : ident := $"symbol".
Definition _x_valid_dict_api__t : ident := $"x_valid_dict_api__t".
Definition _t__1 : ident := $"t__1".
Definition _tab : ident := $"tab".
Definition _tb : ident := $"tb".
Definition _threshold : ident := $"threshold".
Definition _x_valid_dict_api__tmp : ident := $"x_valid_dict_api__tmp".
Definition _x_valid_dict_api__tmp__1 : ident := $"x_valid_dict_api__tmp__1".
Definition _ty : ident := $"ty".
Definition _type : ident := $"type".
Definition _u : ident := $"u".
Definition _x_valid_dict_api__upd : ident := $"x_valid_dict_api__upd".
Definition _use_fse : ident := $"use_fse".
Definition _used : ident := $"used".
Definition _uses_dict : ident := $"uses_dict".
Definition _v : ident := $"v".
Definition _v1 : ident := $"v1".
Definition _v2 : ident := $"v2".
Definition _v3 : ident := $"v3".
Definition _v4 : ident := $"v4".
Definition _val : ident := $"val".
Definition _valid : ident := $"valid".
Definition _variant : ident := $"variant".
Definition _vd_chunk : ident := $"vd_chunk".
Definition _vd_raw : ident := $"vd_raw".
Definition _vd_stream : ident := $"vd_stream".
Definition _vd_wd : ident := $"vd_wd".
Definition _w : ident := $"w".
Definition _x_valid_dict_api__w_code : ident := $"x_valid_dict_api__w_code".
Definition _w_compressed_block : ident := $"w_compressed_block".
Definition _w_dict : ident := $"w_dict".
Definition _x_valid_dict_api__w_extra : ident := $"x_valid_dict_api__w_extra".
Definition _w_frame : ident := $"w_frame".
Definition _x_valid_dict_api__w_hist : ident := $"x_valid_dict_api__w_hist".
Definition _x_valid_dict_api__w_lit : ident := $"x_valid_dict_api__w_lit".
Definition _w_series : ident := $"w_series".
Definition _x_valid_dict_api__w_st : ident := $"x_valid_dict_api__w_st".
Definition _wd : ident := $"wd".
Definition _which : ident := $"which".
Definition _window : ident := $"window".
Definition _window_log : ident := $"window_log".
Definition _within_oneshot : ident := $"within_oneshot".
Definition _within_stream : ident := $"within_stream".
Definition _wstate_copy : ident := $"wstate_copy".
Definition _x_valid_dict_api__wv : ident := $"x_valid_dict_api__wv".
Definition _x : ident := $"x".
Definition _xmerge : ident := $"xmerge".
Definition _xread : ident := $"xread".
Definition _xrotl : ident := $"xrotl".
Definition _xround : ident := $"xround".
Definition _xxh64 : ident := $"xxh64".
Definition _z : ident := $"z".
Definition _x_valid_dict_api__t'1 : ident := 128%positive.
Definition _x_valid_dict_api__t'10 : ident := 137%positive.
Definition _x_valid_dict_api__t'100 : ident := 227%positive.
Definition _x_valid_dict_api__t'101 : ident := 228%positive.
Definition _x_valid_dict_api__t'102 : ident := 229%positive.
Definition _x_valid_dict_api__t'103 : ident := 230%positive.
Definition _x_valid_dict_api__t'104 : ident := 231%positive.
Definition _x_valid_dict_api__t'105 : ident := 232%positive.
Definition _x_valid_dict_api__t'106 : ident := 233%positive.
Definition _x_valid_dict_api__t'107 : ident := 234%positive.
Definition _x_valid_dict_api__t'108 : ident := 235%positive.
Definition _x_valid_dict_api__t'109 : ident := 236%positive.
Definition _x_valid_dict_api__t'11 : ident := 138%positive.
Definition _x_valid_dict_api__t'110 : ident := 237%positive.
Definition _x_valid_dict_api__t'111 : ident := 238%positive.
Definition _x_valid_dict_api__t'112 : ident := 239%positive.
Definition _x_valid_dict_api__t'113 : ident := 240%positive.
Definition _x_valid_dict_api__t'114 : ident := 241%positive.
Definition _x_valid_dict_api__t'115 : ident := 242%positive.
Definition _x_valid_dict_api__t'12 : ident := 139%positive.
Definition _x_valid_dict_api__t'13 : ident := 140%positive.
Definition _x_valid_dict_api__t'14 : ident := 141%positive.
Definition _x_valid_dict_api__t'15 : ident := 142%positive.
Definition _x_valid_dict_api__t'16 : ident := 143%positive.
Definition _x_valid_dict_api__t'17 : ident := 144%positive.
Definition _x_valid_dict_api__t'18 : ident := 145%positive.
Definition _x_valid_dict_api__t'19 : ident := 146%positive.
Definition _x_valid_dict_api__t'2 : ident := 129%positive.
Definition _x_valid_dict_api__t'20 : ident := 147%positive.
Definition _x_valid_dict_api__t'21 : ident := 148%positive.
Definition _x_valid_dict_api__t'22 : ident := 149%positive.
Definition _x_valid_dict_api__t'23 : ident := 150%positive.
Definition _x_valid_dict_api__t'24 : ident := 151%positive.
Definition _x_valid_dict_api__t'25 : ident := 152%positive.
Definition _x_valid_dict_api__t'26 : ident := 153%positive.
Definition _x_valid_dict_api__t'27 : ident := 154%positive.
Definition _x_valid_dict_api__t'28 : ident := 155%positive.
Definition _x_valid_dict_api__t'29 : ident := 156%positive.
Definition _x_valid_dict_api__t'3 : ident := 130%positive.
Definition _x_valid_dict_api__t'30 : ident := 157%positive.
Definition _x_valid_dict_api__t'31 : ident := 158%positive.
Definition _x_valid_dict_api__t'32 : ident := 159%positive.
Definition _x_valid_dict_api__t'33 : ident := 160%positive.
Definition _x_valid_dict_api__t'34 : ident := 161%positive.
Definition _x_valid_dict_api__t'35 : ident := 162%positive.
Definition _x_valid_dict_api__t'36 : ident := 163%positive.
Definition _x_valid_dict_api__t'37 : ident := 164%positive.
Definition _x_valid_dict_api__t'38 : ident := 165%positive.
Definition _x_valid_dict_api__t'39 : ident := 166%positive.
Definition _x_valid_dict_api__t'4 : ident := 131%positive.
Definition _x_valid_dict_api__t'40 : ident := 167%positive.
Definition _x_valid_dict_api__t'41 : ident := 168%positive.
Definition _x_valid_dict_api__t'42 : ident := 169%positive.
Definition _x_valid_dict_api__t'43 : ident := 170%positive.
Definition _x_valid_dict_api__t'44 : ident := 171%positive.
Definition _x_valid_dict_api__t'45 : ident := 172%positive.
Definition _x_valid_dict_api__t'46 : ident := 173%positive.
Definition _x_valid_dict_api__t'47 : ident := 174%positive.
Definition _x_valid_dict_api__t'48 : ident := 175%positive.
Definition _x_valid_dict_api__t'49 : ident := 176%positive.
Definition _x_valid_dict_api__t'5 : ident := 132%positive.
Definition _x_valid_dict_api__t'50 : ident := 177%positive.
Definition _x_valid_dict_api__t'51 : ident := 178%positive.
Definition _x_valid_dict_api__t'52 : ident := 179%positive.
Definition _x_valid_dict_api__t'53 : ident := 180%positive.
Definition _x_valid_dict_api__t'54 : ident := 181%positive.
Definition _x_valid_dict_api__t'55 : ident := 182%positive.
Definition _x_valid_dict_api__t'56 : ident := 183%positive.
Definition _x_valid_dict_api__t'57 : ident := 184%positive.
Definition _x_valid_dict_api__t'58 : ident := 185%positive.
Definition _x_valid_dict_api__t'59 : ident := 186%positive.
Definition _x_valid_dict_api__t'6 : ident := 133%positive.
Definition _x_valid_dict_api__t'60 : ident := 187%positive.
Definition _x_valid_dict_api__t'61 : ident := 188%positive.
Definition _x_valid_dict_api__t'62 : ident := 189%positive.
Definition _x_valid_dict_api__t'63 : ident := 190%positive.
Definition _x_valid_dict_api__t'64 : ident := 191%positive.
Definition _x_valid_dict_api__t'65 : ident := 192%positive.
Definition _x_valid_dict_api__t'66 : ident := 193%positive.
Definition _x_valid_dict_api__t'67 : ident := 194%positive.
Definition _x_valid_dict_api__t'68 : ident := 195%positive.
Definition _x_valid_dict_api__t'69 : ident := 196%positive.
Definition _x_valid_dict_api__t'7 : ident := 134%positive.
Definition _x_valid_dict_api__t'70 : ident := 197%positive.
Definition _x_valid_dict_api__t'71 : ident := 198%positive.
Definition _x_valid_dict_api__t'72 : ident := 199%positive.
Definition _x_valid_dict_api__t'73 : ident := 200%positive.
Definition _x_valid_dict_api__t'74 : ident := 201%positive.
Definition _x_valid_dict_api__t'75 : ident := 202%positive.
Definition _x_valid_dict_api__t'76 : ident := 203%positive.
Definition _x_valid_dict_api__t'77 : ident := 204%positive.
Definition _x_valid_dict_api__t'78 : ident := 205%positive.
Definition _x_valid_dict_api__t'79 : ident := 206%positive.
Definition _x_valid_dict_api__t'8 : ident := 135%positive.
Definition _x_valid_dict_api__t'80 : ident := 207%positive.
Definition _x_valid_dict_api__t'81 : ident := 208%positive.
Definition _x_valid_dict_api__t'82 : ident := 209%positive.
Definition _x_valid_dict_api__t'83 : ident := 210%positive.
Definition _x_valid_dict_api__t'84 : ident := 211%positive.
Definition _x_valid_dict_api__t'85 : ident := 212%positive.
Definition _x_valid_dict_api__t'86 : ident := 213%positive.
Definition _x_valid_dict_api__t'87 : ident := 214%positive.
Definition _x_valid_dict_api__t'88 : ident := 215%positive.
Definition _x_valid_dict_api__t'89 : ident := 216%positive.
Definition _x_valid_dict_api__t'9 : ident := 136%positive.
Definition _x_valid_dict_api__t'90 : ident := 217%positive.
Definition _x_valid_dict_api__t'91 : ident := 218%positive.
Definition _x_valid_dict_api__t'92 : ident := 219%positive.
Definition _x_valid_dict_api__t'93 : ident := 220%positive.
Definition _x_valid_dict_api__t'94 : ident := 221%positive.
Definition _x_valid_dict_api__t'95 : ident := 222%positive.
Definition _x_valid_dict_api__t'96 : ident := 223%positive.
Definition _x_valid_dict_api__t'97 : ident := 224%positive.
Definition _x_valid_dict_api__t'98 : ident := 225%positive.
Definition _x_valid_dict_api__t'99 : ident := 226%positive.

Definition f_choose := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_k, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_x_valid_dict_api__t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _x_valid_dict_api__t'1) (Evar _nondet_u32 (Tfunction nil tuint cc_default)) nil)
  (Sreturn (Some (Ebinop Omod (Etempvar _x_valid_dict_api__t'1 tuint) (Etempvar _k tuint)
                   tuint))))
|}.

Definition f_choose_in := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_lo, tulong) :: (_hi, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_x_valid_dict_api__t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Scall None (Evar _gp_assert (Tfunction (tint :: nil) tvoid cc_default))
    ((Ebinop Ole (Etempvar _lo tulong) (Etempvar _hi tulong) tint) :: nil))
  (Ssequence
    (Scall (Some _x_valid_dict_api__t'1) (Evar _nondet_u32 (Tfunction nil tuint cc_default))
      nil)
    (Sreturn (Some (Ebinop Oadd (Etempvar _lo tulong)
                     (Ecast
                       (Ebinop Omod (Etempvar _x_valid_dict_api__t'1 tuint)
                         (Ecast
                           (Ebinop Oadd
                             (Ebinop Osub (Etempvar _hi tulong)
                               (Etempvar _lo tulong) tulong)
                             (Econst_int (Int.repr 1) tint) tulong) tuint)
                         tuint) tulong) tulong)))))
|}.

Definition f_highbit := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_x, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_r, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _r (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Swhile
      (Ebinop Ogt (Etempvar _x tulong) (Econst_int (Int.repr 1) tint) tint)
      (Ssequence
        (Sset _x
          (Ebinop Oshr (Etempvar _x tulong) (Econst_int (Int.repr 1) tint)
            tulong))
        (Sset _r
          (Ebinop Oadd (Etempvar _r tuint) (Econst_int (Int.repr 1) tint)
            tuint))))
    (Sreturn (Some (Etempvar _r tuint)))))
|}.

Definition f_put8 := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_o, (tptr (Tstruct ___gp_out_t noattr))) :: (_v, tuint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_x_valid_dict_api__t'5, tulong) :: (_x_valid_dict_api__t'4, tulong) :: (_x_valid_dict_api__t'3, tulong) ::
               (_x_valid_dict_api__t'2, (tptr tuchar)) :: (_x_valid_dict_api__t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _x_valid_dict_api__t'4
      (Efield
        (Ederef (Etempvar _o (tptr (Tstruct ___gp_out_t noattr)))
          (Tstruct ___gp_out_t noattr)) _n tulong))
    (Ssequence
      (Sset _x_valid_dict_api__t'5
        (Efield
          (Ederef (Etempvar _o (tptr (Tstruct ___gp_out_t noattr)))
            (Tstruct ___gp_out_t noattr)) _cap tulong))
      (Scall None
        (Evar _gp_assume (Tfunction (tint :: nil) tvoid cc_default))
        ((Ebinop Olt (Etempvar _x_valid_dict_api__t'4 tulong) (Etempvar _x_valid_dict_api__t'5 tulong) tint) ::
         nil))))
  (Ssequence
    (Ssequence
      (Sset _x_valid_dict_api__t'2
        (Efield
          (Ederef (Etempvar _o (tptr (Tstruct ___gp_out_t noattr)))
            (Tstruct ___gp_out_t noattr)) _p (tptr tuchar)))
      (Ssequence
        (Sset _x_valid_dict_api__t'3
          (Efield
            (Ederef (Etempvar _o (tptr (Tstruct ___gp_out_t noattr)))
              (Tstruct ___gp_out_t noattr)) _n tulong))
        (Sassign
          (Ederef
            (Ebinop Oadd (Etempvar _x_valid_dict_api__t'2 (tptr tuchar)) (Etempvar _x_valid_dict_api__t'3 tulong)
              (tptr tuchar)) tuchar)
          (Ecast
            (Ebinop Oand (Etempvar _v tuint) (Econst_int (Int.repr 255) tint)
              tuint) tuchar))))
    (Ssequence
      (Sset _x_valid_dict_api__t'1
        (Efield
          (Ederef (Etempvar _o (tptr (Tstruct ___gp_out_t noattr)))
            (Tstruct ___gp_out_t noattr)) _n tulong))
      (Sassign
        (Efield
          (Ederef (Etempvar _o (tptr (Tstruct ___gp_out_t noattr)))
            (Tstruct ___gp_out_t noattr)) _n tulong)
        (Ebinop Oadd (Etempvar _x_valid_dict_api__t'1 tulong) (Econst_int (Int.repr 1) tint)
          tulong)))))
|}.

Definition f_put_le := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_o, (tptr (Tstruct ___gp_out_t noattr))) :: (_v, tulong) ::
                (_k, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Econst_int (Int.repr 0) tint))
  (Sloop
    (Ssequence
      (Sifthenelse (Ebinop Olt (Etempvar _i tuint) (Etempvar _k tuint) tint)
        Sskip
        Sbreak)
      (Scall None
        (Evar _put8 (Tfunction
                      ((tptr (Tstruct ___gp_out_t noattr)) :: tuint :: nil)
                      tvoid cc_default))
        ((Etempvar _o (tptr (Tstruct ___gp_out_t noattr))) ::
         (Ecast
           (Ebinop Oand
             (Ebinop Oshr (Etempvar _v tulong)
               (Ebinop Omul (Econst_int (Int.repr 8) tint)
                 (Etempvar _i tuint) tuint) tulong)
             (Econst_int (Int.repr 255) tint) tulong) tuint) :: nil)))
    (Sset _i
      (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint) tuint))))
|}.

Definition f_put_bytes := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_o, (tptr (Tstruct ___gp_out_t noattr))) ::
                (_b, (tptr tuchar)) :: (_k, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tulong) :: (_x_valid_dict_api__t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
  (Sloop
    (Ssequence
      (Sifthenelse (Ebinop Olt (Etempvar _i tulong) (Etempvar _k tulong)
                     tint)
        Sskip
        Sbreak)
      (Ssequence
        (Sset _x_valid_dict_api__t'1
          (Ederef
            (Ebinop Oadd (Etempvar _b (tptr tuchar)) (Etempvar _i tulong)
              (tptr tuchar)) tuchar))
        (Scall None
          (Evar _put8 (Tfunction
                        ((tptr (Tstruct ___gp_out_t noattr)) :: tuint :: nil)
                        tvoid cc_default))
          ((Etempvar _o (tptr (Tstruct ___gp_out_t noattr))) ::
           (Etempvar _x_valid_dict_api__t'1 tuchar) :: nil))))
    (Sset _i
      (Ebinop Oadd (Etempvar _i tulong) (Econst_int (Int.repr 1) tint)
        tulong))))
|}.

Definition f_bits_put := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_b, (tptr (Tstruct ___gp_bits_t noattr))) :: (_v, tulong) ::
                (_nb, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_x_valid_dict_api__t'1, tint) :: (_x_valid_dict_api__t'10, tuint) :: (_x_valid_dict_api__t'9, tuint) ::
               (_x_valid_dict_api__t'8, tulong) :: (_x_valid_dict_api__t'7, tuint) :: (_x_valid_dict_api__t'6, tuint) ::
               (_x_valid_dict_api__t'5, tulong) ::
               (_x_valid_dict_api__t'4, (tptr (Tstruct ___gp_out_t noattr))) ::
               (_x_valid_dict_api__t'3, tulong) :: (_x_valid_dict_api__t'2, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sifthenelse (Ebinop Ole (Etempvar _nb tuint)
                   (Econst_int (Int.repr 32) tint) tint)
      (Ssequence
        (Sset _x_valid_dict_api__t'10
          (Efield
            (Ederef (Etempvar _b (tptr (Tstruct ___gp_bits_t noattr)))
              (Tstruct ___gp_bits_t noattr)) _bits tuint))
        (Sset _x_valid_dict_api__t'1
          (Ecast
            (Ebinop Olt (Etempvar _x_valid_dict_api__t'10 tuint) (Econst_int (Int.repr 8) tint)
              tint) tbool)))
      (Sset _x_valid_dict_api__t'1 (Econst_int (Int.repr 0) tint)))
    (Scall None (Evar _gp_assert (Tfunction (tint :: nil) tvoid cc_default))
      ((Etempvar _x_valid_dict_api__t'1 tint) :: nil)))
  (Ssequence
    (Scall None (Evar _gp_assert (Tfunction (tint :: nil) tvoid cc_default))
      ((Ebinop Olt (Etempvar _v tulong)
         (Ebinop Oshl (Econst_long (Int64.repr 1) tulong)
           (Etempvar _nb tuint) tulong) tint) :: nil))
    (Ssequence
      (Ssequence
        (Sset _x_valid_dict_api__t'8
          (Efield
            (Ederef (Etempvar _b (tptr (Tstruct ___gp_bits_t noattr)))
              (Tstruct ___gp_bits_t noattr)) _acc tulong))
        (Ssequence
          (Sset _x_valid_dict_api__t'9
            (Efield
              (Ederef (Etempvar _b (tptr (Tstruct ___gp_bits_t noattr)))
                (Tstruct ___gp_bits_t noattr)) _bits tuint))
          (Sassign
            (Efield
              (Ederef (Etempvar _b (tptr (Tstruct ___gp_bits_t noattr)))
                (Tstruct ___gp_bits_t noattr)) _acc tulong)
            (Ebinop Oor (Etempvar _x_valid_dict_api__t'8 tulong)
              (Ebinop Oshl (Etempvar _v tulong) (Etempvar _x_valid_dict_api__t'9 tuint) tulong)
              tulong))))
      (Ssequence
        (Ssequence
          (Sset _x_valid_dict_api__t'7
            (Efield
              (Ederef (Etempvar _b (tptr (Tstruct ___gp_bits_t noattr)))
                (Tstruct ___gp_bits_t noattr)) _bits tuint))
          (Sassign
            (Efield
              (Ederef (Etempvar _b (tptr (Tstruct ___gp_bits_t noattr)))
                (Tstruct ___gp_bits_t noattr)) _bits tuint)
            (Ebinop Oadd (Etempvar _x_valid_dict_api__t'7 tuint) (Etempvar _nb tuint) tuint)))
        (Sloop
          (Ssequence
            (Ssequence
              (Sset _x_valid_dict_api__t'6
                (Efield
                  (Ederef (Etempvar _b (tptr (Tstruct ___gp_bits_t noattr)))
                    (Tstruct ___gp_bits_t noattr)) _bits tuint))
              (Sifthenelse (Ebinop Oge (Etempvar _x_valid_dict_api__t'6 tuint)
                             (Econst_int (Int.repr 8) tint) tint)
                Sskip
                Sbreak))
            (Ssequence
              (Ssequence
                (Sset _x_valid_dict_api__t'4
                  (Efield
                    (Ederef
                      (Etempvar _b (tptr (Tstruct ___gp_bits_t noattr)))
                      (Tstruct ___gp_bits_t noattr)) _o
                    (tptr (Tstruct ___gp_out_t noattr))))
                (Ssequence
                  (Sset _x_valid_dict_api__t'5
                    (Efield
                      (Ederef
                        (Etempvar _b (tptr (Tstruct ___gp_bits_t noattr)))
                        (Tstruct ___gp_bits_t noattr)) _acc tulong))
                  (Scall None
                    (Evar _put8 (Tfunction
                                  ((tptr (Tstruct ___gp_out_t noattr)) ::
                                   tuint :: nil) tvoid cc_default))
                    ((Etempvar _x_valid_dict_api__t'4 (tptr (Tstruct ___gp_out_t noattr))) ::
                     (Ecast
                       (Ebinop Oand (Etempvar _x_valid_dict_api__t'5 tulong)
                         (Econst_int (Int.repr 255) tint) tulong) tuint) ::
                     nil))))
              (Ssequence
                (Ssequence
                  (Sset _x_valid_dict_api__t'3
                    (Efield
                      (Ederef
                        (Etempvar _b (tptr (Tstruct ___gp_bits_t noattr)))
                        (Tstruct ___gp_bits_t noattr)) _acc tulong))
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _b (tptr (Tstruct ___gp_bits_t noattr)))
                        (Tstruct ___gp_bits_t noattr)) _acc tulong)
                    (Ebinop Oshr (Etempvar _x_valid_dict_api__t'3 tulong)
                      (Econst_int (Int.repr 8) tint) tulong)))
                (Ssequence
                  (Sset _x_valid_dict_api__t'2
                    (Efield
                      (Ederef
                        (Etempvar _b (tptr (Tstruct ___gp_bits_t noattr)))
                        (Tstruct ___gp_bits_t noattr)) _bits tuint))
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _b (tptr (Tstruct ___gp_bits_t noattr)))
                        (Tstruct ___gp_bits_t noattr)) _bits tuint)
                    (Ebinop Osub (Etempvar _x_valid_dict_api__t'2 tuint)
                      (Econst_int (Int.repr 8) tint) tuint))))))
          Sskip)))))
|}.

Definition f_bits_end_mark := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_b, (tptr (Tstruct ___gp_bits_t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_x_valid_dict_api__t'4, tuint) :: (_x_valid_dict_api__t'3, tulong) :: (_x_valid_dict_api__t'2, tulong) ::
               (_x_valid_dict_api__t'1, (tptr (Tstruct ___gp_out_t noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _x_valid_dict_api__t'3
      (Efield
        (Ederef (Etempvar _b (tptr (Tstruct ___gp_bits_t noattr)))
          (Tstruct ___gp_bits_t noattr)) _acc tulong))
    (Ssequence
      (Sset _x_valid_dict_api__t'4
        (Efield
          (Ederef (Etempvar _b (tptr (Tstruct ___gp_bits_t noattr)))
            (Tstruct ___gp_bits_t noattr)) _bits tuint))
      (Sassign
        (Efield
          (Ederef (Etempvar _b (tptr (Tstruct ___gp_bits_t noattr)))
            (Tstruct ___gp_bits_t noattr)) _acc tulong)
        (Ebinop Oor (Etempvar _x_valid_dict_api__t'3 tulong)
          (Ebinop Oshl (Econst_long (Int64.repr 1) tulong)
            (Etempvar _x_valid_dict_api__t'4 tuint) tulong) tulong))))
  (Ssequence
    (Ssequence
      (Sset _x_valid_dict_api__t'1
        (Efield
          (Ederef (Etempvar _b (tptr (Tstruct ___gp_bits_t noattr)))
            (Tstruct ___gp_bits_t noattr)) _o
          (tptr (Tstruct ___gp_out_t noattr))))
      (Ssequence
        (Sset _x_valid_dict_api__t'2
          (Efield
            (Ederef (Etempvar _b (tptr (Tstruct ___gp_bits_t noattr)))
              (Tstruct ___gp_bits_t noattr)) _acc tulong))
        (Scall None
          (Evar _put8 (Tfunction
                        ((tptr (Tstruct ___gp_out_t noattr)) :: tuint :: nil)
                        tvoid cc_default))
          ((Etempvar _x_valid_dict_api__t'1 (tptr (Tstruct ___gp_out_t noattr))) ::
           (Ecast
             (Ebinop Oand (Etempvar _x_valid_dict_api__t'2 tulong)
               (Econst_int (Int.repr 255) tint) tulong) tuint) :: nil))))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _b (tptr (Tstruct ___gp_bits_t noattr)))
            (Tstruct ___gp_bits_t noattr)) _acc tulong)
        (Econst_int (Int.repr 0) tint))
      (Sassign
        (Efield
          (Ederef (Etempvar _b (tptr (Tstruct ___gp_bits_t noattr)))
            (Tstruct ___gp_bits_t noattr)) _bits tuint)
        (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_bits_pad := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_b, (tptr (Tstruct ___gp_bits_t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_x_valid_dict_api__t'3, tulong) ::
               (_x_valid_dict_api__t'2, (tptr (Tstruct ___gp_out_t noattr))) ::
               (_x_valid_dict_api__t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _x_valid_dict_api__t'1
      (Efield
        (Ederef (Etempvar _b (tptr (Tstruct ___gp_bits_t noattr)))
          (Tstruct ___gp_bits_t noattr)) _bits tuint))
    (Sifthenelse (Ebinop Ogt (Etempvar _x_valid_dict_api__t'1 tuint)
                   (Econst_int (Int.repr 0) tint) tint)
      (Ssequence
        (Sset _x_valid_dict_api__t'2
          (Efield
            (Ederef (Etempvar _b (tptr (Tstruct ___gp_bits_t noattr)))
              (Tstruct ___gp_bits_t noattr)) _o
            (tptr (Tstruct ___gp_out_t noattr))))
        (Ssequence
          (Sset _x_valid_dict_api__t'3
            (Efield
              (Ederef (Etempvar _b (tptr (Tstruct ___gp_bits_t noattr)))
                (Tstruct ___gp_bits_t noattr)) _acc tulong))
          (Scall None
            (Evar _put8 (Tfunction
                          ((tptr (Tstruct ___gp_out_t noattr)) :: tuint ::
                           nil) tvoid cc_default))
            ((Etempvar _x_valid_dict_api__t'2 (tptr (Tstruct ___gp_out_t noattr))) ::
             (Ecast
               (Ebinop Oand (Etempvar _x_valid_dict_api__t'3 tulong)
                 (Econst_int (Int.repr 255) tint) tulong) tuint) :: nil))))
      Sskip))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _b (tptr (Tstruct ___gp_bits_t noattr)))
          (Tstruct ___gp_bits_t noattr)) _acc tulong)
      (Econst_int (Int.repr 0) tint))
    (Sassign
      (Efield
        (Ederef (Etempvar _b (tptr (Tstruct ___gp_bits_t noattr)))
          (Tstruct ___gp_bits_t noattr)) _bits tuint)
      (Econst_int (Int.repr 0) tint))))
|}.

Definition f_xrotl := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_x, tulong) :: (_r, tuint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop Oor
                 (Ebinop Oshl (Etempvar _x tulong) (Etempvar _r tuint)
                   tulong)
                 (Ebinop Oshr (Etempvar _x tulong)
                   (Ebinop Osub (Econst_int (Int.repr 64) tint)
                     (Etempvar _r tuint) tuint) tulong) tulong)))
|}.

Definition f_xread := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr tuchar)) :: (_k, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_v, tulong) :: (_i, tuint) :: (_x_valid_dict_api__t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Sset _v (Ecast (Econst_int (Int.repr 0) tint) tulong))
  (Ssequence
    (Ssequence
      (Sset _i (Econst_int (Int.repr 0) tint))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _i tuint) (Etempvar _k tuint)
                         tint)
            Sskip
            Sbreak)
          (Ssequence
            (Sset _x_valid_dict_api__t'1
              (Ederef
                (Ebinop Oadd (Etempvar _p (tptr tuchar)) (Etempvar _i tuint)
                  (tptr tuchar)) tuchar))
            (Sset _v
              (Ebinop Oor (Etempvar _v tulong)
                (Ebinop Oshl (Ecast (Etempvar _x_valid_dict_api__t'1 tuchar) tulong)
                  (Ebinop Omul (Econst_int (Int.repr 8) tint)
                    (Etempvar _i tuint) tuint) tulong) tulong))))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
            tuint))))
    (Sreturn (Some (Etempvar _v tulong)))))
|}.

Definition f_xround := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_acc, tulong) :: (_in, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_x_valid_dict_api__t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sset _acc
    (Ebinop Oadd (Etempvar _acc tulong)
      (Ebinop Omul (Etempvar _in tulong)
        (Econst_long (Int64.repr (-4417276706812531889)) tulong) tulong)
      tulong))
  (Ssequence
    (Ssequence
      (Scall (Some _x_valid_dict_api__t'1)
        (Evar _xrotl (Tfunction (tulong :: tuint :: nil) tulong cc_default))
        ((Etempvar _acc tulong) :: (Econst_int (Int.repr 31) tint) :: nil))
      (Sset _acc (Etempvar _x_valid_dict_api__t'1 tulong)))
    (Sreturn (Some (Ebinop Omul (Etempvar _acc tulong)
                     (Econst_long (Int64.repr (-7046029288634856825)) tulong)
                     tulong)))))
|}.

Definition f_xmerge := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_h, tulong) :: (_v, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_x_valid_dict_api__t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _x_valid_dict_api__t'1)
      (Evar _xround (Tfunction (tulong :: tulong :: nil) tulong cc_default))
      ((Econst_int (Int.repr 0) tint) :: (Etempvar _v tulong) :: nil))
    (Sset _h
      (Ebinop Oxor (Etempvar _h tulong) (Etempvar _x_valid_dict_api__t'1 tulong) tulong)))
  (Sreturn (Some (Ebinop Oadd
                   (Ebinop Omul (Etempvar _h tulong)
                     (Econst_long (Int64.repr (-7046029288634856825)) tulong)
                     tulong)
                   (Econst_long (Int64.repr (-8796714831421723037)) tulong)
                   tulong))))
|}.

Definition f_xxh64 := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr tuchar)) :: (_len, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tulong) :: (_h, tulong) :: (_v1, tulong) ::
               (_v2, tulong) :: (_v3, tulong) :: (_v4, tulong) ::
               (_x_valid_dict_api__t'22, tulong) :: (_x_valid_dict_api__t'21, tulong) :: (_x_valid_dict_api__t'20, tulong) ::
               (_x_valid_dict_api__t'19, tulong) :: (_x_valid_dict_api__t'18, tulong) :: (_x_valid_dict_api__t'17, tulong) ::
               (_x_valid_dict_api__t'16, tulong) :: (_x_valid_dict_api__t'15, tulong) :: (_x_valid_dict_api__t'14, tulong) ::
               (_x_valid_dict_api__t'13, tulong) :: (_x_valid_dict_api__t'12, tulong) :: (_x_valid_dict_api__t'11, tulong) ::
               (_x_valid_dict_api__t'10, tulong) :: (_x_valid_dict_api__t'9, tulong) :: (_x_valid_dict_api__t'8, tulong) ::
               (_x_valid_dict_api__t'7, tulong) :: (_x_valid_dict_api__t'6, tulong) :: (_x_valid_dict_api__t'5, tulong) ::
               (_x_valid_dict_api__t'4, tulong) :: (_x_valid_dict_api__t'3, tulong) :: (_x_valid_dict_api__t'2, tulong) ::
               (_x_valid_dict_api__t'1, tulong) :: (_x_valid_dict_api__t'23, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
  (Ssequence
    (Sifthenelse (Ebinop Oge (Etempvar _len tulong)
                   (Econst_int (Int.repr 32) tint) tint)
      (Ssequence
        (Sset _v1
          (Ebinop Oadd
            (Econst_long (Int64.repr (-7046029288634856825)) tulong)
            (Econst_long (Int64.repr (-4417276706812531889)) tulong) tulong))
        (Ssequence
          (Sset _v2 (Econst_long (Int64.repr (-4417276706812531889)) tulong))
          (Ssequence
            (Sset _v3 (Ecast (Econst_int (Int.repr 0) tint) tulong))
            (Ssequence
              (Sset _v4
                (Ebinop Osub (Econst_int (Int.repr 0) tint)
                  (Econst_long (Int64.repr (-7046029288634856825)) tulong)
                  tulong))
              (Ssequence
                (Sloop
                  (Ssequence
                    (Sifthenelse (Ebinop Ole
                                   (Ebinop Oadd (Etempvar _i tulong)
                                     (Econst_int (Int.repr 32) tint) tulong)
                                   (Etempvar _len tulong) tint)
                      Sskip
                      Sbreak)
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Scall (Some _x_valid_dict_api__t'1)
                            (Evar _xread (Tfunction
                                           ((tptr tuchar) :: tuint :: nil)
                                           tulong cc_default))
                            ((Ebinop Oadd (Etempvar _p (tptr tuchar))
                               (Etempvar _i tulong) (tptr tuchar)) ::
                             (Econst_int (Int.repr 8) tint) :: nil))
                          (Scall (Some _x_valid_dict_api__t'2)
                            (Evar _xround (Tfunction
                                            (tulong :: tulong :: nil) tulong
                                            cc_default))
                            ((Etempvar _v1 tulong) ::
                             (Etempvar _x_valid_dict_api__t'1 tulong) :: nil)))
                        (Sset _v1 (Etempvar _x_valid_dict_api__t'2 tulong)))
                      (Ssequence
                        (Ssequence
                          (Ssequence
                            (Scall (Some _x_valid_dict_api__t'3)
                              (Evar _xread (Tfunction
                                             ((tptr tuchar) :: tuint :: nil)
                                             tulong cc_default))
                              ((Ebinop Oadd
                                 (Ebinop Oadd (Etempvar _p (tptr tuchar))
                                   (Etempvar _i tulong) (tptr tuchar))
                                 (Econst_int (Int.repr 8) tint)
                                 (tptr tuchar)) ::
                               (Econst_int (Int.repr 8) tint) :: nil))
                            (Scall (Some _x_valid_dict_api__t'4)
                              (Evar _xround (Tfunction
                                              (tulong :: tulong :: nil)
                                              tulong cc_default))
                              ((Etempvar _v2 tulong) ::
                               (Etempvar _x_valid_dict_api__t'3 tulong) :: nil)))
                          (Sset _v2 (Etempvar _x_valid_dict_api__t'4 tulong)))
                        (Ssequence
                          (Ssequence
                            (Ssequence
                              (Scall (Some _x_valid_dict_api__t'5)
                                (Evar _xread (Tfunction
                                               ((tptr tuchar) :: tuint ::
                                                nil) tulong cc_default))
                                ((Ebinop Oadd
                                   (Ebinop Oadd (Etempvar _p (tptr tuchar))
                                     (Etempvar _i tulong) (tptr tuchar))
                                   (Econst_int (Int.repr 16) tint)
                                   (tptr tuchar)) ::
                                 (Econst_int (Int.repr 8) tint) :: nil))
                              (Scall (Some _x_valid_dict_api__t'6)
                                (Evar _xround (Tfunction
                                                (tulong :: tulong :: nil)
                                                tulong cc_default))
                                ((Etempvar _v3 tulong) ::
                                 (Etempvar _x_valid_dict_api__t'5 tulong) :: nil)))
                            (Sset _v3 (Etempvar _x_valid_dict_api__t'6 tulong)))
                          (Ssequence
                            (Ssequence
                              (Scall (Some _x_valid_dict_api__t'7)
                                (Evar _xread (Tfunction
                                               ((tptr tuchar) :: tuint ::
                                                nil) tulong cc_default))
                                ((Ebinop Oadd
                                   (Ebinop Oadd (Etempvar _p (tptr tuchar))
                                     (Etempvar _i tulong) (tptr tuchar))
                                   (Econst_int (Int.repr 24) tint)
                                   (tptr tuchar)) ::
                                 (Econst_int (Int.repr 8) tint) :: nil))
                              (Scall (Some _x_valid_dict_api__t'8)
                                (Evar _xround (Tfunction
                                                (tulong :: tulong :: nil)
                                                tulong cc_default))
                                ((Etempvar _v4 tulong) ::
                                 (Etempvar _x_valid_dict_api__t'7 tulong) :: nil)))
                            (Sset _v4 (Etempvar _x_valid_dict_api__t'8 tulong)))))))
                  (Sset _i
                    (Ebinop Oadd (Etempvar _i tulong)
                      (Econst_int (Int.repr 32) tint) tulong)))
                (Ssequence
                  (Ssequence
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Scall (Some _x_valid_dict_api__t'9)
                            (Evar _xrotl (Tfunction (tulong :: tuint :: nil)
                                           tulong cc_default))
                            ((Etempvar _v1 tulong) ::
                             (Econst_int (Int.repr 1) tint) :: nil))
                          (Scall (Some _x_valid_dict_api__t'10)
                            (Evar _xrotl (Tfunction (tulong :: tuint :: nil)
                                           tulong cc_default))
                            ((Etempvar _v2 tulong) ::
                             (Econst_int (Int.repr 7) tint) :: nil)))
                        (Scall (Some _x_valid_dict_api__t'11)
                          (Evar _xrotl (Tfunction (tulong :: tuint :: nil)
                                         tulong cc_default))
                          ((Etempvar _v3 tulong) ::
                           (Econst_int (Int.repr 12) tint) :: nil)))
                      (Scall (Some _x_valid_dict_api__t'12)
                        (Evar _xrotl (Tfunction (tulong :: tuint :: nil)
                                       tulong cc_default))
                        ((Etempvar _v4 tulong) ::
                         (Econst_int (Int.repr 18) tint) :: nil)))
                    (Sset _h
                      (Ebinop Oadd
                        (Ebinop Oadd
                          (Ebinop Oadd (Etempvar _x_valid_dict_api__t'9 tulong)
                            (Etempvar _x_valid_dict_api__t'10 tulong) tulong)
                          (Etempvar _x_valid_dict_api__t'11 tulong) tulong)
                        (Etempvar _x_valid_dict_api__t'12 tulong) tulong)))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _x_valid_dict_api__t'13)
                        (Evar _xmerge (Tfunction (tulong :: tulong :: nil)
                                        tulong cc_default))
                        ((Etempvar _h tulong) :: (Etempvar _v1 tulong) ::
                         nil))
                      (Sset _h (Etempvar _x_valid_dict_api__t'13 tulong)))
                    (Ssequence
                      (Ssequence
                        (Scall (Some _x_valid_dict_api__t'14)
                          (Evar _xmerge (Tfunction (tulong :: tulong :: nil)
                                          tulong cc_default))
                          ((Etempvar _h tulong) :: (Etempvar _v2 tulong) ::
                           nil))
                        (Sset _h (Etempvar _x_valid_dict_api__t'14 tulong)))
                      (Ssequence
                        (Ssequence
                          (Scall (Some _x_valid_dict_api__t'15)
                            (Evar _xmerge (Tfunction
                                            (tulong :: tulong :: nil) tulong
                                            cc_default))
                            ((Etempvar _h tulong) :: (Etempvar _v3 tulong) ::
                             nil))
                          (Sset _h (Etempvar _x_valid_dict_api__t'15 tulong)))
                        (Ssequence
                          (Scall (Some _x_valid_dict_api__t'16)
                            (Evar _xmerge (Tfunction
                                            (tulong :: tulong :: nil) tulong
                                            cc_default))
                            ((Etempvar _h tulong) :: (Etempvar _v4 tulong) ::
                             nil))
                          (Sset _h (Etempvar _x_valid_dict_api__t'16 tulong))))))))))))
      (Sset _h (Econst_long (Int64.repr 2870177450012600261) tulong)))
    (Ssequence
      (Sset _h
        (Ebinop Oadd (Etempvar _h tulong)
          (Ecast (Etempvar _len tulong) tulong) tulong))
      (Ssequence
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Ole
                           (Ebinop Oadd (Etempvar _i tulong)
                             (Econst_int (Int.repr 8) tint) tulong)
                           (Etempvar _len tulong) tint)
              Sskip
              Sbreak)
            (Ssequence
              (Ssequence
                (Ssequence
                  (Scall (Some _x_valid_dict_api__t'17)
                    (Evar _xread (Tfunction ((tptr tuchar) :: tuint :: nil)
                                   tulong cc_default))
                    ((Ebinop Oadd (Etempvar _p (tptr tuchar))
                       (Etempvar _i tulong) (tptr tuchar)) ::
                     (Econst_int (Int.repr 8) tint) :: nil))
                  (Scall (Some _x_valid_dict_api__t'18)
                    (Evar _xround (Tfunction (tulong :: tulong :: nil) tulong
                                    cc_default))
                    ((Econst_int (Int.repr 0) tint) ::
                     (Etempvar _x_valid_dict_api__t'17 tulong) :: nil)))
                (Sset _h
                  (Ebinop Oxor (Etempvar _h tulong) (Etempvar _x_valid_dict_api__t'18 tulong)
                    tulong)))
              (Ssequence
                (Scall (Some _x_valid_dict_api__t'19)
                  (Evar _xrotl (Tfunction (tulong :: tuint :: nil) tulong
                                 cc_default))
                  ((Etempvar _h tulong) :: (Econst_int (Int.repr 27) tint) ::
                   nil))
                (Sset _h
                  (Ebinop Oadd
                    (Ebinop Omul (Etempvar _x_valid_dict_api__t'19 tulong)
                      (Econst_long (Int64.repr (-7046029288634856825)) tulong)
                      tulong)
                    (Econst_long (Int64.repr (-8796714831421723037)) tulong)
                    tulong)))))
          (Sset _i
            (Ebinop Oadd (Etempvar _i tulong) (Econst_int (Int.repr 8) tint)
              tulong)))
        (Ssequence
          (Sifthenelse (Ebinop Ole
                         (Ebinop Oadd (Etempvar _i tulong)
                           (Econst_int (Int.repr 4) tint) tulong)
                         (Etempvar _len tulong) tint)
            (Ssequence
              (Ssequence
                (Scall (Some _x_valid_dict_api__t'20)
                  (Evar _xread (Tfunction ((tptr tuchar) :: tuint :: nil)
                                 tulong cc_default))
                  ((Ebinop Oadd (Etempvar _p (tptr tuchar))
                     (Etempvar _i tulong) (tptr tuchar)) ::
                   (Econst_int (Int.repr 4) tint) :: nil))
                (Sset _h
                  (Ebinop Oxor (Etempvar _h tulong)
                    (Ebinop Omul (Etempvar _x_valid_dict_api__t'20 tulong)
                      (Econst_long (Int64.repr (-7046029288634856825)) tulong)
                      tulong) tulong)))
              (Ssequence
                (Ssequence
                  (Scall (Some _x_valid_dict_api__t'21)
                    (Evar _xrotl (Tfunction (tulong :: tuint :: nil) tulong
                                   cc_default))
                    ((Etempvar _h tulong) ::
                     (Econst_int (Int.repr 23) tint) :: nil))
                  (Sset _h
                    (Ebinop Oadd
                      (Ebinop Omul (Etempvar _x_valid_dict_api__t'21 tulong)
                        (Econst_long (Int64.repr (-4417276706812531889)) tulong)
                        tulong)
                      (Econst_long (Int64.repr 1609587929392839161) tulong)
                      tulong)))
                (Sset _i
                  (Ebinop Oadd (Etempvar _i tulong)
                    (Econst_int (Int.repr 4) tint) tulong))))
            Sskip)
          (Ssequence
            (Sloop
              (Ssequence
                (Sifthenelse (Ebinop Olt (Etempvar _i tulong)
                               (Etempvar _len tulong) tint)
                  Sskip
                  Sbreak)
                (Ssequence
                  (Ssequence
                    (Sset _x_valid_dict_api__t'23
                      (Ederef
                        (Ebinop Oadd (Etempvar _p (tptr tuchar))
                          (Etempvar _i tulong) (tptr tuchar)) tuchar))
                    (Sset _h
                      (Ebinop Oxor (Etempvar _h tulong)
                        (Ebinop Omul (Ecast (Etempvar _x_valid_dict_api__t'23 tuchar) tulong)
                          (Econst_long (Int64.repr 2870177450012600261) tulong)
                          tulong) tulong)))
                  (Ssequence
                    (Scall (Some _x_valid_dict_api__t'22)
                      (Evar _xrotl (Tfunction (tulong :: tuint :: nil) tulong
                                     cc_default))
                      ((Etempvar _h tulong) ::
                       (Econst_int (Int.repr 11) tint) :: nil))
                    (Sset _h
                      (Ebinop Omul (Etempvar _x_valid_dict_api__t'22 tulong)
                        (Econst_long (Int64.repr (-7046029288634856825)) tulong)
                        tulong)))))
              (Sset _i
                (Ebinop Oadd (Etempvar _i tulong)
                  (Econst_int (Int.repr 1) tint) tulong)))
            (Ssequence
              (Sset _h
                (Ebinop Oxor (Etempvar _h tulong)
                  (Ebinop Oshr (Etempvar _h tulong)
                    (Econst_int (Int.repr 33) tint) tulong) tulong))
              (Ssequence
                (Sset _h
                  (Ebinop Omul (Etempvar _h tulong)
                    (Econst_long (Int64.repr (-4417276706812531889)) tulong)
                    tulong))
                (Ssequence
                  (Sset _h
                    (Ebinop Oxor (Etempvar _h tulong)
                      (Ebinop Oshr (Etempvar _h tulong)
                        (Econst_int (Int.repr 29) tint) tulong) tulong))
                  (Ssequence
                    (Sset _h
                      (Ebinop Omul (Etempvar _h tulong)
                        (Econst_long (Int64.repr 1609587929392839161) tulong)
                        tulong))
                    (Ssequence
                      (Sset _h
                        (Ebinop Oxor (Etempvar _h tulong)
                          (Ebinop Oshr (Etempvar _h tulong)
                            (Econst_int (Int.repr 32) tint) tulong) tulong))
                      (Sreturn (Some (Etempvar _h tulong))))))))))))))
|}.

Definition f_fse_build := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_x_valid_dict_api__t, (tptr (Tstruct ___gp_fse_t noattr))) :: nil);
  fn_vars := ((_next, (tarray tuint 53)) :: nil);
  fn_temps := ((_size, tuint) :: (_high, tuint) :: (_pos, tuint) ::
               (_step, tuint) :: (_s, tuint) :: (_i, tuint) ::
               (_state, tuint) :: (_x, tuint) :: (_nb, tuint) ::
               (_x_valid_dict_api__t'1, tuint) :: (_x_valid_dict_api__t'11, tuint) :: (_x_valid_dict_api__t'10, tuint) ::
               (_x_valid_dict_api__t'9, tshort) :: (_x_valid_dict_api__t'8, tshort) :: (_x_valid_dict_api__t'7, tuint) ::
               (_x_valid_dict_api__t'6, tshort) :: (_x_valid_dict_api__t'5, tshort) :: (_x_valid_dict_api__t'4, tuchar) ::
               (_x_valid_dict_api__t'3, tuint) :: (_x_valid_dict_api__t'2, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _x_valid_dict_api__t'11
      (Efield
        (Ederef (Etempvar _x_valid_dict_api__t (tptr (Tstruct ___gp_fse_t noattr)))
          (Tstruct ___gp_fse_t noattr)) _log tuint))
    (Sset _size
      (Ebinop Oshl (Econst_int (Int.repr 1) tuint) (Etempvar _x_valid_dict_api__t'11 tuint)
        tuint)))
  (Ssequence
    (Sset _high
      (Ebinop Osub (Etempvar _size tuint) (Econst_int (Int.repr 1) tint)
        tuint))
    (Ssequence
      (Sset _pos (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Sset _step
          (Ebinop Oadd
            (Ebinop Oadd
              (Ebinop Oshr (Etempvar _size tuint)
                (Econst_int (Int.repr 1) tint) tuint)
              (Ebinop Oshr (Etempvar _size tuint)
                (Econst_int (Int.repr 3) tint) tuint) tuint)
            (Econst_int (Int.repr 3) tint) tuint))
        (Ssequence
          (Ssequence
            (Sset _s (Econst_int (Int.repr 0) tint))
            (Sloop
              (Ssequence
                (Ssequence
                  (Sset _x_valid_dict_api__t'10
                    (Efield
                      (Ederef
                        (Etempvar _x_valid_dict_api__t (tptr (Tstruct ___gp_fse_t noattr)))
                        (Tstruct ___gp_fse_t noattr)) _nsym tuint))
                  (Sifthenelse (Ebinop Olt (Etempvar _s tuint)
                                 (Etempvar _x_valid_dict_api__t'10 tuint) tint)
                    Sskip
                    Sbreak))
                (Ssequence
                  (Sset _x_valid_dict_api__t'8
                    (Ederef
                      (Ebinop Oadd
                        (Efield
                          (Ederef
                            (Etempvar _x_valid_dict_api__t (tptr (Tstruct ___gp_fse_t noattr)))
                            (Tstruct ___gp_fse_t noattr)) _norm
                          (tarray tshort 53)) (Etempvar _s tuint)
                        (tptr tshort)) tshort))
                  (Sifthenelse (Ebinop Oeq (Etempvar _x_valid_dict_api__t'8 tshort)
                                 (Eunop Oneg (Econst_int (Int.repr 1) tint)
                                   tint) tint)
                    (Ssequence
                      (Sassign
                        (Ederef
                          (Ebinop Oadd
                            (Efield
                              (Ederef
                                (Etempvar _x_valid_dict_api__t (tptr (Tstruct ___gp_fse_t noattr)))
                                (Tstruct ___gp_fse_t noattr)) _sym
                              (tarray tuchar 512)) (Etempvar _high tuint)
                            (tptr tuchar)) tuchar)
                        (Ecast (Etempvar _s tuint) tuchar))
                      (Ssequence
                        (Sset _high
                          (Ebinop Osub (Etempvar _high tuint)
                            (Econst_int (Int.repr 1) tint) tuint))
                        (Sassign
                          (Ederef
                            (Ebinop Oadd (Evar _next (tarray tuint 53))
                              (Etempvar _s tuint) (tptr tuint)) tuint)
                          (Econst_int (Int.repr 1) tint))))
                    (Ssequence
                      (Sset _x_valid_dict_api__t'9
                        (Ederef
                          (Ebinop Oadd
                            (Efield
                              (Ederef
                                (Etempvar _x_valid_dict_api__t (tptr (Tstruct ___gp_fse_t noattr)))
                                (Tstruct ___gp_fse_t noattr)) _norm
                              (tarray tshort 53)) (Etempvar _s tuint)
                            (tptr tshort)) tshort))
                      (Sassign
                        (Ederef
                          (Ebinop Oadd (Evar _next (tarray tuint 53))
                            (Etempvar _s tuint) (tptr tuint)) tuint)
                        (Ecast (Etempvar _x_valid_dict_api__t'9 tshort) tuint))))))
              (Sset _s
                (Ebinop Oadd (Etempvar _s tuint)
                  (Econst_int (Int.repr 1) tint) tuint))))
          (Ssequence
            (Ssequence
              (Sset _s (Econst_int (Int.repr 0) tint))
              (Sloop
                (Ssequence
                  (Ssequence
                    (Sset _x_valid_dict_api__t'7
                      (Efield
                        (Ederef
                          (Etempvar _x_valid_dict_api__t (tptr (Tstruct ___gp_fse_t noattr)))
                          (Tstruct ___gp_fse_t noattr)) _nsym tuint))
                    (Sifthenelse (Ebinop Olt (Etempvar _s tuint)
                                   (Etempvar _x_valid_dict_api__t'7 tuint) tint)
                      Sskip
                      Sbreak))
                  (Ssequence
                    (Sset _x_valid_dict_api__t'5
                      (Ederef
                        (Ebinop Oadd
                          (Efield
                            (Ederef
                              (Etempvar _x_valid_dict_api__t (tptr (Tstruct ___gp_fse_t noattr)))
                              (Tstruct ___gp_fse_t noattr)) _norm
                            (tarray tshort 53)) (Etempvar _s tuint)
                          (tptr tshort)) tshort))
                    (Sifthenelse (Ebinop Ogt (Etempvar _x_valid_dict_api__t'5 tshort)
                                   (Econst_int (Int.repr 0) tint) tint)
                      (Ssequence
                        (Sset _i (Econst_int (Int.repr 0) tint))
                        (Sloop
                          (Ssequence
                            (Ssequence
                              (Sset _x_valid_dict_api__t'6
                                (Ederef
                                  (Ebinop Oadd
                                    (Efield
                                      (Ederef
                                        (Etempvar _x_valid_dict_api__t (tptr (Tstruct ___gp_fse_t noattr)))
                                        (Tstruct ___gp_fse_t noattr)) _norm
                                      (tarray tshort 53)) (Etempvar _s tuint)
                                    (tptr tshort)) tshort))
                              (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                                             (Ecast (Etempvar _x_valid_dict_api__t'6 tshort)
                                               tuint) tint)
                                Sskip
                                Sbreak))
                            (Ssequence
                              (Sassign
                                (Ederef
                                  (Ebinop Oadd
                                    (Efield
                                      (Ederef
                                        (Etempvar _x_valid_dict_api__t (tptr (Tstruct ___gp_fse_t noattr)))
                                        (Tstruct ___gp_fse_t noattr)) _sym
                                      (tarray tuchar 512))
                                    (Etempvar _pos tuint) (tptr tuchar))
                                  tuchar) (Ecast (Etempvar _s tuint) tuchar))
                              (Ssequence
                                (Sset _pos
                                  (Ebinop Oand
                                    (Ebinop Oadd (Etempvar _pos tuint)
                                      (Etempvar _step tuint) tuint)
                                    (Ebinop Osub (Etempvar _size tuint)
                                      (Econst_int (Int.repr 1) tint) tuint)
                                    tuint))
                                (Swhile
                                  (Ebinop Ogt (Etempvar _pos tuint)
                                    (Etempvar _high tuint) tint)
                                  (Sset _pos
                                    (Ebinop Oand
                                      (Ebinop Oadd (Etempvar _pos tuint)
                                        (Etempvar _step tuint) tuint)
                                      (Ebinop Osub (Etempvar _size tuint)
                                        (Econst_int (Int.repr 1) tint) tuint)
                                      tuint))))))
                          (Sset _i
                            (Ebinop Oadd (Etempvar _i tuint)
                              (Econst_int (Int.repr 1) tint) tuint))))
                      Sskip)))
                (Sset _s
                  (Ebinop Oadd (Etempvar _s tuint)
                    (Econst_int (Int.repr 1) tint) tuint))))
            (Ssequence
              (Sset _state (Econst_int (Int.repr 0) tint))
              (Sloop
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Etempvar _state tuint)
                                 (Etempvar _size tuint) tint)
                    Sskip
                    Sbreak)
                  (Ssequence
                    (Ssequence
                      (Sset _x_valid_dict_api__t'4
                        (Ederef
                          (Ebinop Oadd
                            (Efield
                              (Ederef
                                (Etempvar _x_valid_dict_api__t (tptr (Tstruct ___gp_fse_t noattr)))
                                (Tstruct ___gp_fse_t noattr)) _sym
                              (tarray tuchar 512)) (Etempvar _state tuint)
                            (tptr tuchar)) tuchar))
                      (Sset _x
                        (Ederef
                          (Ebinop Oadd (Evar _next (tarray tuint 53))
                            (Etempvar _x_valid_dict_api__t'4 tuchar) (tptr tuint)) tuint)))
                    (Ssequence
                      (Ssequence
                        (Scall (Some _x_valid_dict_api__t'1)
                          (Evar _highbit (Tfunction (tulong :: nil) tuint
                                           cc_default))
                          ((Etempvar _x tuint) :: nil))
                        (Ssequence
                          (Sset _x_valid_dict_api__t'3
                            (Efield
                              (Ederef
                                (Etempvar _x_valid_dict_api__t (tptr (Tstruct ___gp_fse_t noattr)))
                                (Tstruct ___gp_fse_t noattr)) _log tuint))
                          (Sset _nb
                            (Ebinop Osub (Etempvar _x_valid_dict_api__t'3 tuint)
                              (Etempvar _x_valid_dict_api__t'1 tuint) tuint))))
                      (Ssequence
                        (Ssequence
                          (Sset _x_valid_dict_api__t'2
                            (Ederef
                              (Ebinop Oadd
                                (Efield
                                  (Ederef
                                    (Etempvar _x_valid_dict_api__t (tptr (Tstruct ___gp_fse_t noattr)))
                                    (Tstruct ___gp_fse_t noattr)) _sym
                                  (tarray tuchar 512))
                                (Etempvar _state tuint) (tptr tuchar))
                              tuchar))
                          (Sassign
                            (Ederef
                              (Ebinop Oadd (Evar _next (tarray tuint 53))
                                (Etempvar _x_valid_dict_api__t'2 tuchar) (tptr tuint)) tuint)
                            (Ebinop Oadd (Etempvar _x tuint)
                              (Econst_int (Int.repr 1) tint) tuint)))
                        (Ssequence
                          (Sassign
                            (Ederef
                              (Ebinop Oadd
                                (Efield
                                  (Ederef
                                    (Etempvar _x_valid_dict_api__t (tptr (Tstruct ___gp_fse_t noattr)))
                                    (Tstruct ___gp_fse_t noattr)) _nb
                                  (tarray tuchar 512))
                                (Etempvar _state tuint) (tptr tuchar))
                              tuchar) (Ecast (Etempvar _nb tuint) tuchar))
                          (Sassign
                            (Ederef
                              (Ebinop Oadd
                                (Efield
                                  (Ederef
                                    (Etempvar _x_valid_dict_api__t (tptr (Tstruct ___gp_fse_t noattr)))
                                    (Tstruct ___gp_fse_t noattr)) _base
                                  (tarray tushort 512))
                                (Etempvar _state tuint) (tptr tushort))
                              tushort)
                            (Ecast
                              (Ebinop Osub
                                (Ebinop Oshl (Etempvar _x tuint)
                                  (Etempvar _nb tuint) tuint)
                                (Etempvar _size tuint) tuint) tushort)))))))
                (Sset _state
                  (Ebinop Oadd (Etempvar _state tuint)
                    (Econst_int (Int.repr 1) tint) tuint))))))))))
|}.

Definition f_fse_rle := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_x_valid_dict_api__t, (tptr (Tstruct ___gp_fse_t noattr))) ::
                (_symbol, tuint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Efield
      (Ederef (Etempvar _x_valid_dict_api__t (tptr (Tstruct ___gp_fse_t noattr)))
        (Tstruct ___gp_fse_t noattr)) _nsym tuint)
    (Ebinop Oadd (Etempvar _symbol tuint) (Econst_int (Int.repr 1) tint)
      tuint))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _x_valid_dict_api__t (tptr (Tstruct ___gp_fse_t noattr)))
          (Tstruct ___gp_fse_t noattr)) _log tuint)
      (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Sassign
        (Ederef
          (Ebinop Oadd
            (Efield
              (Ederef (Etempvar _x_valid_dict_api__t (tptr (Tstruct ___gp_fse_t noattr)))
                (Tstruct ___gp_fse_t noattr)) _sym (tarray tuchar 512))
            (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar)
        (Ecast (Etempvar _symbol tuint) tuchar))
      (Ssequence
        (Sassign
          (Ederef
            (Ebinop Oadd
              (Efield
                (Ederef (Etempvar _x_valid_dict_api__t (tptr (Tstruct ___gp_fse_t noattr)))
                  (Tstruct ___gp_fse_t noattr)) _nb (tarray tuchar 512))
              (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar)
          (Econst_int (Int.repr 0) tint))
        (Sassign
          (Ederef
            (Ebinop Oadd
              (Efield
                (Ederef (Etempvar _x_valid_dict_api__t (tptr (Tstruct ___gp_fse_t noattr)))
                  (Tstruct ___gp_fse_t noattr)) _base (tarray tushort 512))
              (Econst_int (Int.repr 0) tint) (tptr tushort)) tushort)
          (Econst_int (Int.repr 0) tint))))))
|}.

Definition f_fse_has := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_x_valid_dict_api__t, (tptr (Tstruct ___gp_fse_t noattr))) :: (_s, tuint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_x_valid_dict_api__t'1, tint) :: (_x_valid_dict_api__t'5, tuchar) :: (_x_valid_dict_api__t'4, tuint) ::
               (_x_valid_dict_api__t'3, tshort) :: (_x_valid_dict_api__t'2, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _x_valid_dict_api__t'4
      (Efield
        (Ederef (Etempvar _x_valid_dict_api__t (tptr (Tstruct ___gp_fse_t noattr)))
          (Tstruct ___gp_fse_t noattr)) _log tuint))
    (Sifthenelse (Ebinop Oeq (Etempvar _x_valid_dict_api__t'4 tuint)
                   (Econst_int (Int.repr 0) tint) tint)
      (Ssequence
        (Sset _x_valid_dict_api__t'5
          (Ederef
            (Ebinop Oadd
              (Efield
                (Ederef (Etempvar _x_valid_dict_api__t (tptr (Tstruct ___gp_fse_t noattr)))
                  (Tstruct ___gp_fse_t noattr)) _sym (tarray tuchar 512))
              (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar))
        (Sreturn (Some (Ebinop Oeq (Etempvar _x_valid_dict_api__t'5 tuchar) (Etempvar _s tuint)
                         tint))))
      Sskip))
  (Ssequence
    (Ssequence
      (Sset _x_valid_dict_api__t'2
        (Efield
          (Ederef (Etempvar _x_valid_dict_api__t (tptr (Tstruct ___gp_fse_t noattr)))
            (Tstruct ___gp_fse_t noattr)) _nsym tuint))
      (Sifthenelse (Ebinop Olt (Etempvar _s tuint) (Etempvar _x_valid_dict_api__t'2 tuint)
                     tint)
        (Ssequence
          (Sset _x_valid_dict_api__t'3
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef (Etempvar _x_valid_dict_api__t (tptr (Tstruct ___gp_fse_t noattr)))
                    (Tstruct ___gp_fse_t noattr)) _norm (tarray tshort 53))
                (Etempvar _s tuint) (tptr tshort)) tshort))
          (Sset _x_valid_dict_api__t'1
            (Ecast
              (Ebinop One (Etempvar _x_valid_dict_api__t'3 tshort)
                (Econst_int (Int.repr 0) tint) tint) tbool)))
        (Sset _x_valid_dict_api__t'1 (Econst_int (Int.repr 0) tint))))
    (Sreturn (Some (Etempvar _x_valid_dict_api__t'1 tint)))))
|}.

Definition f_fse_pick := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_x_valid_dict_api__t, (tptr (Tstruct ___gp_fse_t noattr))) :: (_log, tuint) ::
                (_x_valid_dict_api__maxsym, tuint) :: (_x_valid_dict_api__need, (tptr tuchar)) :: nil);
  fn_vars := ((_options, (tarray tint 3)) :: nil);
  fn_temps := ((_remaining, tint) :: (_s, tuint) :: (_nonzero, tuint) ::
               (_left, tuint) :: (_slots_after, tuint) :: (_last, tuint) ::
               (_reserve, tint) :: (_nopt, tint) :: (_kind, tint) ::
               (_p, tint) :: (_x_valid_dict_api__t'16, tint) :: (_x_valid_dict_api__t'15, tulong) ::
               (_x_valid_dict_api__t'14, tint) :: (_x_valid_dict_api__t'13, tuint) :: (_x_valid_dict_api__t'12, tint) ::
               (_x_valid_dict_api__t'11, tint) :: (_x_valid_dict_api__t'10, tint) :: (_x_valid_dict_api__t'9, tint) ::
               (_x_valid_dict_api__t'8, tuint) :: (_x_valid_dict_api__t'7, tint) :: (_x_valid_dict_api__t'6, tint) ::
               (_x_valid_dict_api__t'5, tint) :: (_x_valid_dict_api__t'4, tint) :: (_x_valid_dict_api__t'3, tuint) ::
               (_x_valid_dict_api__t'2, tint) :: (_x_valid_dict_api__t'1, tint) :: (_x_valid_dict_api__t'19, tuchar) ::
               (_x_valid_dict_api__t'18, tuchar) :: (_x_valid_dict_api__t'17, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Sset _remaining
    (Ebinop Oshl (Econst_int (Int.repr 1) tint) (Etempvar _log tuint) tint))
  (Ssequence
    (Sset _nonzero (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Sset _left (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Ssequence
          (Sifthenelse (Ebinop Ole (Etempvar _log tuint)
                         (Econst_int (Int.repr 9) tint) tint)
            (Sset _x_valid_dict_api__t'1
              (Ecast
                (Ebinop Olt (Etempvar _x_valid_dict_api__maxsym tuint)
                  (Econst_int (Int.repr 53) tint) tint) tbool))
            (Sset _x_valid_dict_api__t'1 (Econst_int (Int.repr 0) tint)))
          (Scall None
            (Evar _gp_assert (Tfunction (tint :: nil) tvoid cc_default))
            ((Etempvar _x_valid_dict_api__t'1 tint) :: nil)))
        (Ssequence
          (Ssequence
            (Sset _s (Econst_int (Int.repr 0) tint))
            (Sloop
              (Ssequence
                (Sifthenelse (Ebinop Ole (Etempvar _s tuint)
                               (Etempvar _x_valid_dict_api__maxsym tuint) tint)
                  Sskip
                  Sbreak)
                (Ssequence
                  (Ssequence
                    (Sset _x_valid_dict_api__t'19
                      (Ederef
                        (Ebinop Oadd (Etempvar _x_valid_dict_api__need (tptr tuchar))
                          (Etempvar _s tuint) (tptr tuchar)) tuchar))
                    (Sifthenelse (Etempvar _x_valid_dict_api__t'19 tuchar)
                      (Sset _x_valid_dict_api__t'2 (Ecast (Econst_int (Int.repr 1) tint) tint))
                      (Sset _x_valid_dict_api__t'2 (Ecast (Econst_int (Int.repr 0) tint) tint))))
                  (Sset _left
                    (Ebinop Oadd (Etempvar _left tuint) (Etempvar _x_valid_dict_api__t'2 tint)
                      tuint))))
              (Sset _s
                (Ebinop Oadd (Etempvar _s tuint)
                  (Econst_int (Int.repr 1) tint) tuint))))
          (Ssequence
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _left tuint)
                             (Econst_int (Int.repr 2) tint) tint)
                (Sset _x_valid_dict_api__t'3
                  (Ecast
                    (Ebinop Osub (Econst_int (Int.repr 2) tint)
                      (Etempvar _left tuint) tuint) tuint))
                (Sset _x_valid_dict_api__t'3 (Ecast (Econst_int (Int.repr 0) tint) tuint)))
              (Scall None
                (Evar _gp_assume (Tfunction (tint :: nil) tvoid cc_default))
                ((Ebinop Ole
                   (Ebinop Oadd (Etempvar _left tuint) (Etempvar _x_valid_dict_api__t'3 tuint)
                     tuint) (Ecast (Etempvar _remaining tint) tuint) tint) ::
                 nil)))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef (Etempvar _x_valid_dict_api__t (tptr (Tstruct ___gp_fse_t noattr)))
                    (Tstruct ___gp_fse_t noattr)) _log tuint)
                (Etempvar _log tuint))
              (Ssequence
                (Ssequence
                  (Sset _s (Econst_int (Int.repr 0) tint))
                  (Sloop
                    (Ssequence
                      (Sifthenelse (Ebinop Ogt (Etempvar _remaining tint)
                                     (Econst_int (Int.repr 0) tint) tint)
                        Sskip
                        Sbreak)
                      (Ssequence
                        (Sset _slots_after
                          (Ebinop Osub (Etempvar _x_valid_dict_api__maxsym tuint)
                            (Etempvar _s tuint) tuint))
                        (Ssequence
                          (Sset _last
                            (Ebinop Oeq (Etempvar _s tuint)
                              (Etempvar _x_valid_dict_api__maxsym tuint) tint))
                          (Ssequence
                            (Sset _nopt (Econst_int (Int.repr 0) tint))
                            (Ssequence
                              (Scall None
                                (Evar _gp_assert (Tfunction (tint :: nil)
                                                   tvoid cc_default))
                                ((Ebinop Ole (Etempvar _s tuint)
                                   (Etempvar _x_valid_dict_api__maxsym tuint) tint) :: nil))
                              (Ssequence
                                (Ssequence
                                  (Sset _x_valid_dict_api__t'18
                                    (Ederef
                                      (Ebinop Oadd
                                        (Etempvar _x_valid_dict_api__need (tptr tuchar))
                                        (Etempvar _s tuint) (tptr tuchar))
                                      tuchar))
                                  (Sifthenelse (Etempvar _x_valid_dict_api__t'18 tuchar)
                                    (Sset _left
                                      (Ebinop Osub (Etempvar _left tuint)
                                        (Econst_int (Int.repr 1) tint) tuint))
                                    Sskip))
                                (Ssequence
                                  (Sset _reserve
                                    (Ecast (Etempvar _left tuint) tint))
                                  (Ssequence
                                    (Sifthenelse (Ebinop Olt
                                                   (Ebinop Oadd
                                                     (Ebinop Oadd
                                                       (Etempvar _nonzero tuint)
                                                       (Econst_int (Int.repr 1) tint)
                                                       tuint)
                                                     (Etempvar _left tuint)
                                                     tuint)
                                                   (Econst_int (Int.repr 2) tint)
                                                   tint)
                                      (Sset _reserve
                                        (Ebinop Oadd (Etempvar _reserve tint)
                                          (Ecast
                                            (Ebinop Osub
                                              (Econst_int (Int.repr 2) tint)
                                              (Ebinop Oadd
                                                (Ebinop Oadd
                                                  (Etempvar _nonzero tuint)
                                                  (Econst_int (Int.repr 1) tint)
                                                  tuint)
                                                (Etempvar _left tuint) tuint)
                                              tuint) tint) tint))
                                      Sskip)
                                    (Ssequence
                                      (Ssequence
                                        (Ssequence
                                          (Ssequence
                                            (Ssequence
                                              (Sset _x_valid_dict_api__t'17
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Etempvar _x_valid_dict_api__need (tptr tuchar))
                                                    (Etempvar _s tuint)
                                                    (tptr tuchar)) tuchar))
                                              (Sifthenelse (Eunop Onotbool
                                                             (Etempvar _x_valid_dict_api__t'17 tuchar)
                                                             tint)
                                                (Sset _x_valid_dict_api__t'5
                                                  (Ecast
                                                    (Eunop Onotbool
                                                      (Etempvar _last tuint)
                                                      tint) tbool))
                                                (Sset _x_valid_dict_api__t'5
                                                  (Econst_int (Int.repr 0) tint))))
                                            (Sifthenelse (Etempvar _x_valid_dict_api__t'5 tint)
                                              (Sset _x_valid_dict_api__t'6
                                                (Ecast
                                                  (Ebinop Oge
                                                    (Ebinop Oadd
                                                      (Etempvar _nonzero tuint)
                                                      (Etempvar _slots_after tuint)
                                                      tuint)
                                                    (Econst_int (Int.repr 2) tint)
                                                    tint) tbool))
                                              (Sset _x_valid_dict_api__t'6
                                                (Econst_int (Int.repr 0) tint))))
                                          (Sifthenelse (Etempvar _x_valid_dict_api__t'6 tint)
                                            (Ssequence
                                              (Sifthenelse (Ebinop Olt
                                                             (Ebinop Oadd
                                                               (Etempvar _nonzero tuint)
                                                               (Etempvar _left tuint)
                                                               tuint)
                                                             (Econst_int (Int.repr 2) tint)
                                                             tint)
                                                (Sset _x_valid_dict_api__t'8
                                                  (Ecast
                                                    (Ebinop Osub
                                                      (Econst_int (Int.repr 2) tint)
                                                      (Ebinop Oadd
                                                        (Etempvar _nonzero tuint)
                                                        (Etempvar _left tuint)
                                                        tuint) tuint) tuint))
                                                (Sset _x_valid_dict_api__t'8
                                                  (Ecast
                                                    (Econst_int (Int.repr 0) tint)
                                                    tuint)))
                                              (Sset _x_valid_dict_api__t'7
                                                (Ecast
                                                  (Ebinop Oge
                                                    (Etempvar _remaining tint)
                                                    (Ebinop Oadd
                                                      (Ecast
                                                        (Etempvar _left tuint)
                                                        tint)
                                                      (Ecast
                                                        (Etempvar _x_valid_dict_api__t'8 tuint)
                                                        tint) tint) tint)
                                                  tbool)))
                                            (Sset _x_valid_dict_api__t'7
                                              (Econst_int (Int.repr 0) tint))))
                                        (Sifthenelse (Etempvar _x_valid_dict_api__t'7 tint)
                                          (Ssequence
                                            (Ssequence
                                              (Sset _x_valid_dict_api__t'4
                                                (Etempvar _nopt tint))
                                              (Sset _nopt
                                                (Ebinop Oadd
                                                  (Etempvar _x_valid_dict_api__t'4 tint)
                                                  (Econst_int (Int.repr 1) tint)
                                                  tint)))
                                            (Sassign
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Evar _options (tarray tint 3))
                                                  (Etempvar _x_valid_dict_api__t'4 tint)
                                                  (tptr tint)) tint)
                                              (Econst_int (Int.repr 0) tint)))
                                          Sskip))
                                      (Ssequence
                                        (Ssequence
                                          (Sifthenelse (Ebinop Oge
                                                         (Ebinop Osub
                                                           (Etempvar _remaining tint)
                                                           (Econst_int (Int.repr 1) tint)
                                                           tint)
                                                         (Etempvar _reserve tint)
                                                         tint)
                                            (Sifthenelse (Eunop Onotbool
                                                           (Etempvar _last tuint)
                                                           tint)
                                              (Sset _x_valid_dict_api__t'10
                                                (Ecast
                                                  (Econst_int (Int.repr 1) tint)
                                                  tbool))
                                              (Ssequence
                                                (Sset _x_valid_dict_api__t'10
                                                  (Ecast
                                                    (Ebinop Oeq
                                                      (Etempvar _remaining tint)
                                                      (Econst_int (Int.repr 1) tint)
                                                      tint) tbool))
                                                (Sset _x_valid_dict_api__t'10
                                                  (Ecast
                                                    (Etempvar _x_valid_dict_api__t'10 tint)
                                                    tbool))))
                                            (Sset _x_valid_dict_api__t'10
                                              (Econst_int (Int.repr 0) tint)))
                                          (Sifthenelse (Etempvar _x_valid_dict_api__t'10 tint)
                                            (Ssequence
                                              (Ssequence
                                                (Sset _x_valid_dict_api__t'9
                                                  (Etempvar _nopt tint))
                                                (Sset _nopt
                                                  (Ebinop Oadd
                                                    (Etempvar _x_valid_dict_api__t'9 tint)
                                                    (Econst_int (Int.repr 1) tint)
                                                    tint)))
                                              (Sassign
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Evar _options (tarray tint 3))
                                                    (Etempvar _x_valid_dict_api__t'9 tint)
                                                    (tptr tint)) tint)
                                                (Econst_int (Int.repr 1) tint)))
                                            Sskip))
                                        (Ssequence
                                          (Ssequence
                                            (Sifthenelse (Ebinop Oge
                                                           (Ebinop Osub
                                                             (Etempvar _remaining tint)
                                                             (Etempvar _reserve tint)
                                                             tint)
                                                           (Econst_int (Int.repr 1) tint)
                                                           tint)
                                              (Sifthenelse (Eunop Onotbool
                                                             (Etempvar _last tuint)
                                                             tint)
                                                (Sset _x_valid_dict_api__t'12
                                                  (Ecast
                                                    (Econst_int (Int.repr 1) tint)
                                                    tbool))
                                                (Ssequence
                                                  (Sset _x_valid_dict_api__t'12
                                                    (Ecast
                                                      (Ebinop Oeq
                                                        (Etempvar _reserve tint)
                                                        (Econst_int (Int.repr 0) tint)
                                                        tint) tbool))
                                                  (Sset _x_valid_dict_api__t'12
                                                    (Ecast
                                                      (Etempvar _x_valid_dict_api__t'12 tint)
                                                      tbool))))
                                              (Sset _x_valid_dict_api__t'12
                                                (Econst_int (Int.repr 0) tint)))
                                            (Sifthenelse (Etempvar _x_valid_dict_api__t'12 tint)
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _x_valid_dict_api__t'11
                                                    (Etempvar _nopt tint))
                                                  (Sset _nopt
                                                    (Ebinop Oadd
                                                      (Etempvar _x_valid_dict_api__t'11 tint)
                                                      (Econst_int (Int.repr 1) tint)
                                                      tint)))
                                                (Sassign
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Evar _options (tarray tint 3))
                                                      (Etempvar _x_valid_dict_api__t'11 tint)
                                                      (tptr tint)) tint)
                                                  (Econst_int (Int.repr 2) tint)))
                                              Sskip))
                                          (Ssequence
                                            (Scall None
                                              (Evar _gp_assert (Tfunction
                                                                 (tint ::
                                                                  nil) tvoid
                                                                 cc_default))
                                              ((Ebinop Ogt
                                                 (Etempvar _nopt tint)
                                                 (Econst_int (Int.repr 0) tint)
                                                 tint) :: nil))
                                            (Ssequence
                                              (Ssequence
                                                (Scall (Some _x_valid_dict_api__t'13)
                                                  (Evar _choose (Tfunction
                                                                  (tuint ::
                                                                   nil) tuint
                                                                  cc_default))
                                                  ((Ecast
                                                     (Etempvar _nopt tint)
                                                     tuint) :: nil))
                                                (Sset _kind
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Evar _options (tarray tint 3))
                                                      (Etempvar _x_valid_dict_api__t'13 tuint)
                                                      (tptr tint)) tint)))
                                              (Ssequence
                                                (Sifthenelse (Ebinop Oeq
                                                               (Etempvar _kind tint)
                                                               (Econst_int (Int.repr 0) tint)
                                                               tint)
                                                  (Sset _p
                                                    (Econst_int (Int.repr 0) tint))
                                                  (Sifthenelse (Ebinop Oeq
                                                                 (Etempvar _kind tint)
                                                                 (Econst_int (Int.repr 1) tint)
                                                                 tint)
                                                    (Sset _p
                                                      (Eunop Oneg
                                                        (Econst_int (Int.repr 1) tint)
                                                        tint))
                                                    (Ssequence
                                                      (Sifthenelse (Etempvar _last tuint)
                                                        (Sset _x_valid_dict_api__t'14
                                                          (Ecast
                                                            (Etempvar _remaining tint)
                                                            tint))
                                                        (Ssequence
                                                          (Scall (Some _x_valid_dict_api__t'15)
                                                            (Evar _choose_in 
                                                            (Tfunction
                                                              (tulong ::
                                                               tulong :: nil)
                                                              tulong
                                                              cc_default))
                                                            ((Econst_int (Int.repr 1) tint) ::
                                                             (Ecast
                                                               (Ebinop Osub
                                                                 (Etempvar _remaining tint)
                                                                 (Etempvar _reserve tint)
                                                                 tint)
                                                               tulong) ::
                                                             nil))
                                                          (Sset _x_valid_dict_api__t'14
                                                            (Ecast
                                                              (Ecast
                                                                (Etempvar _x_valid_dict_api__t'15 tulong)
                                                                tint) tint))))
                                                      (Sset _p
                                                        (Etempvar _x_valid_dict_api__t'14 tint)))))
                                                (Ssequence
                                                  (Sassign
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _x_valid_dict_api__t (tptr (Tstruct ___gp_fse_t noattr)))
                                                            (Tstruct ___gp_fse_t noattr))
                                                          _norm
                                                          (tarray tshort 53))
                                                        (Etempvar _s tuint)
                                                        (tptr tshort))
                                                      tshort)
                                                    (Ecast (Etempvar _p tint)
                                                      tshort))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sifthenelse (Ebinop Olt
                                                                    (Etempvar _p tint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                        (Sset _x_valid_dict_api__t'16
                                                          (Ecast
                                                            (Econst_int (Int.repr 1) tint)
                                                            tint))
                                                        (Sset _x_valid_dict_api__t'16
                                                          (Ecast
                                                            (Etempvar _p tint)
                                                            tint)))
                                                      (Sset _remaining
                                                        (Ebinop Osub
                                                          (Etempvar _remaining tint)
                                                          (Etempvar _x_valid_dict_api__t'16 tint)
                                                          tint)))
                                                    (Sifthenelse (Ebinop One
                                                                   (Etempvar _p tint)
                                                                   (Econst_int (Int.repr 0) tint)
                                                                   tint)
                                                      (Sset _nonzero
                                                        (Ebinop Oadd
                                                          (Etempvar _nonzero tuint)
                                                          (Econst_int (Int.repr 1) tint)
                                                          tuint))
                                                      Sskip)))))))))))))))))
                    (Sset _s
                      (Ebinop Oadd (Etempvar _s tuint)
                        (Econst_int (Int.repr 1) tint) tuint))))
                (Ssequence
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _x_valid_dict_api__t (tptr (Tstruct ___gp_fse_t noattr)))
                        (Tstruct ___gp_fse_t noattr)) _nsym tuint)
                    (Etempvar _s tuint))
                  (Ssequence
                    (Scall None
                      (Evar _gp_assert (Tfunction (tint :: nil) tvoid
                                         cc_default))
                      ((Ebinop Oge (Etempvar _nonzero tuint)
                         (Econst_int (Int.repr 2) tint) tint) :: nil))
                    (Scall None
                      (Evar _fse_build (Tfunction
                                         ((tptr (Tstruct ___gp_fse_t noattr)) ::
                                          nil) tvoid cc_default))
                      ((Etempvar _x_valid_dict_api__t (tptr (Tstruct ___gp_fse_t noattr))) ::
                       nil))))))))))))
|}.

Definition f_fse_put_description := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_o, (tptr (Tstruct ___gp_out_t noattr))) ::
                (_x_valid_dict_api__t, (tptr (Tstruct ___gp_fse_t noattr))) :: nil);
  fn_vars := ((_b, (Tstruct ___gp_bits_t noattr)) :: nil);
  fn_temps := ((_remaining, tint) :: (_s, tuint) :: (_p, tint) ::
               (_val, tuint) :: (_bits, tuint) :: (_lower_mask, tuint) ::
               (_threshold, tuint) :: (_z, tuint) :: (_x_valid_dict_api__t'3, tint) ::
               (_x_valid_dict_api__t'2, tint) :: (_x_valid_dict_api__t'1, tuint) :: (_x_valid_dict_api__t'8, tuint) ::
               (_x_valid_dict_api__t'7, tuint) :: (_x_valid_dict_api__t'6, tuint) :: (_x_valid_dict_api__t'5, tshort) ::
               (_x_valid_dict_api__t'4, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sassign
    (Efield (Evar _b (Tstruct ___gp_bits_t noattr)) _o
      (tptr (Tstruct ___gp_out_t noattr)))
    (Etempvar _o (tptr (Tstruct ___gp_out_t noattr))))
  (Ssequence
    (Sassign (Efield (Evar _b (Tstruct ___gp_bits_t noattr)) _acc tulong)
      (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Sassign (Efield (Evar _b (Tstruct ___gp_bits_t noattr)) _bits tuint)
        (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Ssequence
          (Sset _x_valid_dict_api__t'8
            (Efield
              (Ederef (Etempvar _x_valid_dict_api__t (tptr (Tstruct ___gp_fse_t noattr)))
                (Tstruct ___gp_fse_t noattr)) _log tuint))
          (Sset _remaining
            (Ebinop Oshl (Econst_int (Int.repr 1) tint) (Etempvar _x_valid_dict_api__t'8 tuint)
              tint)))
        (Ssequence
          (Sset _s (Econst_int (Int.repr 0) tint))
          (Ssequence
            (Ssequence
              (Sset _x_valid_dict_api__t'7
                (Efield
                  (Ederef (Etempvar _x_valid_dict_api__t (tptr (Tstruct ___gp_fse_t noattr)))
                    (Tstruct ___gp_fse_t noattr)) _log tuint))
              (Scall None
                (Evar _bits_put (Tfunction
                                  ((tptr (Tstruct ___gp_bits_t noattr)) ::
                                   tulong :: tuint :: nil) tvoid cc_default))
                ((Eaddrof (Evar _b (Tstruct ___gp_bits_t noattr))
                   (tptr (Tstruct ___gp_bits_t noattr))) ::
                 (Ebinop Osub (Etempvar _x_valid_dict_api__t'7 tuint)
                   (Econst_int (Int.repr 5) tint) tuint) ::
                 (Econst_int (Int.repr 4) tint) :: nil)))
            (Ssequence
              (Sloop
                (Ssequence
                  (Ssequence
                    (Sset _x_valid_dict_api__t'6
                      (Efield
                        (Ederef
                          (Etempvar _x_valid_dict_api__t (tptr (Tstruct ___gp_fse_t noattr)))
                          (Tstruct ___gp_fse_t noattr)) _nsym tuint))
                    (Sifthenelse (Ebinop Olt (Etempvar _s tuint)
                                   (Etempvar _x_valid_dict_api__t'6 tuint) tint)
                      Sskip
                      Sbreak))
                  (Ssequence
                    (Sset _p
                      (Ederef
                        (Ebinop Oadd
                          (Efield
                            (Ederef
                              (Etempvar _x_valid_dict_api__t (tptr (Tstruct ___gp_fse_t noattr)))
                              (Tstruct ___gp_fse_t noattr)) _norm
                            (tarray tshort 53)) (Etempvar _s tuint)
                          (tptr tshort)) tshort))
                    (Ssequence
                      (Sset _val
                        (Ecast
                          (Ebinop Oadd (Etempvar _p tint)
                            (Econst_int (Int.repr 1) tint) tint) tuint))
                      (Ssequence
                        (Ssequence
                          (Scall (Some _x_valid_dict_api__t'1)
                            (Evar _highbit (Tfunction (tulong :: nil) tuint
                                             cc_default))
                            ((Ebinop Oadd
                               (Ecast (Etempvar _remaining tint) tulong)
                               (Econst_int (Int.repr 1) tint) tulong) :: nil))
                          (Sset _bits
                            (Ebinop Oadd (Etempvar _x_valid_dict_api__t'1 tuint)
                              (Econst_int (Int.repr 1) tint) tuint)))
                        (Ssequence
                          (Sset _lower_mask
                            (Ebinop Osub
                              (Ebinop Oshl (Econst_int (Int.repr 1) tuint)
                                (Ebinop Osub (Etempvar _bits tuint)
                                  (Econst_int (Int.repr 1) tint) tuint)
                                tuint) (Econst_int (Int.repr 1) tint) tuint))
                          (Ssequence
                            (Sset _threshold
                              (Ebinop Osub
                                (Ebinop Osub
                                  (Ebinop Oshl
                                    (Econst_int (Int.repr 1) tuint)
                                    (Etempvar _bits tuint) tuint)
                                  (Econst_int (Int.repr 1) tint) tuint)
                                (Ecast
                                  (Ebinop Oadd (Etempvar _remaining tint)
                                    (Econst_int (Int.repr 1) tint) tint)
                                  tuint) tuint))
                            (Ssequence
                              (Sifthenelse (Ebinop Olt (Etempvar _val tuint)
                                             (Etempvar _threshold tuint)
                                             tint)
                                (Scall None
                                  (Evar _bits_put (Tfunction
                                                    ((tptr (Tstruct ___gp_bits_t noattr)) ::
                                                     tulong :: tuint :: nil)
                                                    tvoid cc_default))
                                  ((Eaddrof
                                     (Evar _b (Tstruct ___gp_bits_t noattr))
                                     (tptr (Tstruct ___gp_bits_t noattr))) ::
                                   (Etempvar _val tuint) ::
                                   (Ebinop Osub (Etempvar _bits tuint)
                                     (Econst_int (Int.repr 1) tint) tuint) ::
                                   nil))
                                (Sifthenelse (Ebinop Ole
                                               (Etempvar _val tuint)
                                               (Etempvar _lower_mask tuint)
                                               tint)
                                  (Scall None
                                    (Evar _bits_put (Tfunction
                                                      ((tptr (Tstruct ___gp_bits_t noattr)) ::
                                                       tulong :: tuint ::
                                                       nil) tvoid cc_default))
                                    ((Eaddrof
                                       (Evar _b (Tstruct ___gp_bits_t noattr))
                                       (tptr (Tstruct ___gp_bits_t noattr))) ::
                                     (Etempvar _val tuint) ::
                                     (Etempvar _bits tuint) :: nil))
                                  (Scall None
                                    (Evar _bits_put (Tfunction
                                                      ((tptr (Tstruct ___gp_bits_t noattr)) ::
                                                       tulong :: tuint ::
                                                       nil) tvoid cc_default))
                                    ((Eaddrof
                                       (Evar _b (Tstruct ___gp_bits_t noattr))
                                       (tptr (Tstruct ___gp_bits_t noattr))) ::
                                     (Ebinop Oadd (Etempvar _val tuint)
                                       (Etempvar _threshold tuint) tuint) ::
                                     (Etempvar _bits tuint) :: nil))))
                              (Ssequence
                                (Ssequence
                                  (Sifthenelse (Ebinop Olt (Etempvar _p tint)
                                                 (Econst_int (Int.repr 0) tint)
                                                 tint)
                                    (Sset _x_valid_dict_api__t'2
                                      (Ecast (Econst_int (Int.repr 1) tint)
                                        tint))
                                    (Sset _x_valid_dict_api__t'2
                                      (Ecast (Etempvar _p tint) tint)))
                                  (Sset _remaining
                                    (Ebinop Osub (Etempvar _remaining tint)
                                      (Etempvar _x_valid_dict_api__t'2 tint) tint)))
                                (Ssequence
                                  (Sset _s
                                    (Ebinop Oadd (Etempvar _s tuint)
                                      (Econst_int (Int.repr 1) tint) tuint))
                                  (Sifthenelse (Ebinop Oeq (Etempvar _p tint)
                                                 (Econst_int (Int.repr 0) tint)
                                                 tint)
                                    (Ssequence
                                      (Sset _z
                                        (Econst_int (Int.repr 0) tint))
                                      (Ssequence
                                        (Sloop
                                          (Ssequence
                                            (Ssequence
                                              (Ssequence
                                                (Sset _x_valid_dict_api__t'4
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _x_valid_dict_api__t (tptr (Tstruct ___gp_fse_t noattr)))
                                                      (Tstruct ___gp_fse_t noattr))
                                                    _nsym tuint))
                                                (Sifthenelse (Ebinop Olt
                                                               (Ebinop Oadd
                                                                 (Etempvar _s tuint)
                                                                 (Etempvar _z tuint)
                                                                 tuint)
                                                               (Etempvar _x_valid_dict_api__t'4 tuint)
                                                               tint)
                                                  (Ssequence
                                                    (Sset _x_valid_dict_api__t'5
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _x_valid_dict_api__t (tptr (Tstruct ___gp_fse_t noattr)))
                                                              (Tstruct ___gp_fse_t noattr))
                                                            _norm
                                                            (tarray tshort 53))
                                                          (Ebinop Oadd
                                                            (Etempvar _s tuint)
                                                            (Etempvar _z tuint)
                                                            tuint)
                                                          (tptr tshort))
                                                        tshort))
                                                    (Sset _x_valid_dict_api__t'3
                                                      (Ecast
                                                        (Ebinop Oeq
                                                          (Etempvar _x_valid_dict_api__t'5 tshort)
                                                          (Econst_int (Int.repr 0) tint)
                                                          tint) tbool)))
                                                  (Sset _x_valid_dict_api__t'3
                                                    (Econst_int (Int.repr 0) tint))))
                                              (Sifthenelse (Etempvar _x_valid_dict_api__t'3 tint)
                                                Sskip
                                                Sbreak))
                                            (Sset _z
                                              (Ebinop Oadd
                                                (Etempvar _z tuint)
                                                (Econst_int (Int.repr 1) tint)
                                                tuint)))
                                          Sskip)
                                        (Ssequence
                                          (Sset _s
                                            (Ebinop Oadd (Etempvar _s tuint)
                                              (Etempvar _z tuint) tuint))
                                          (Ssequence
                                            (Swhile
                                              (Ebinop Oge (Etempvar _z tuint)
                                                (Econst_int (Int.repr 3) tint)
                                                tint)
                                              (Ssequence
                                                (Scall None
                                                  (Evar _bits_put (Tfunction
                                                                    ((tptr (Tstruct ___gp_bits_t noattr)) ::
                                                                    tulong ::
                                                                    tuint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                  ((Eaddrof
                                                     (Evar _b (Tstruct ___gp_bits_t noattr))
                                                     (tptr (Tstruct ___gp_bits_t noattr))) ::
                                                   (Econst_int (Int.repr 3) tint) ::
                                                   (Econst_int (Int.repr 2) tint) ::
                                                   nil))
                                                (Sset _z
                                                  (Ebinop Osub
                                                    (Etempvar _z tuint)
                                                    (Econst_int (Int.repr 3) tint)
                                                    tuint))))
                                            (Scall None
                                              (Evar _bits_put (Tfunction
                                                                ((tptr (Tstruct ___gp_bits_t noattr)) ::
                                                                 tulong ::
                                                                 tuint ::
                                                                 nil) tvoid
                                                                cc_default))
                                              ((Eaddrof
                                                 (Evar _b (Tstruct ___gp_bits_t noattr))
                                                 (tptr (Tstruct ___gp_bits_t noattr))) ::
                                               (Etempvar _z tuint) ::
                                               (Econst_int (Int.repr 2) tint) ::
                                               nil))))))
                                    Sskip))))))))))
                Sskip)
              (Ssequence
                (Scall None
                  (Evar _gp_assert (Tfunction (tint :: nil) tvoid cc_default))
                  ((Ebinop Oeq (Etempvar _remaining tint)
                     (Econst_int (Int.repr 0) tint) tint) :: nil))
                (Scall None
                  (Evar _bits_pad (Tfunction
                                    ((tptr (Tstruct ___gp_bits_t noattr)) ::
                                     nil) tvoid cc_default))
                  ((Eaddrof (Evar _b (Tstruct ___gp_bits_t noattr))
                     (tptr (Tstruct ___gp_bits_t noattr))) :: nil))))))))))
|}.

Definition f_fse_states := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_x_valid_dict_api__t, (tptr (Tstruct ___gp_fse_t noattr))) ::
                (_c, (tptr tuchar)) :: (_k, tulong) ::
                (_x_valid_dict_api__st, (tptr tushort)) :: nil);
  fn_vars := nil;
  fn_temps := ((_size, tuint) :: (_s, tuint) :: (_n, tuint) ::
               (_pick, tuint) :: (_i, tulong) :: (_found, tuint) ::
               (_x_valid_dict_api__t'3, tint) :: (_x_valid_dict_api__t'2, tint) :: (_x_valid_dict_api__t'1, tuint) ::
               (_x_valid_dict_api__t'15, tuint) :: (_x_valid_dict_api__t'14, tuchar) :: (_x_valid_dict_api__t'13, tuchar) ::
               (_x_valid_dict_api__t'12, tuchar) :: (_x_valid_dict_api__t'11, tuchar) :: (_x_valid_dict_api__t'10, tushort) ::
               (_x_valid_dict_api__t'9, tushort) :: (_x_valid_dict_api__t'8, tuchar) :: (_x_valid_dict_api__t'7, tuchar) ::
               (_x_valid_dict_api__t'6, tuchar) :: (_x_valid_dict_api__t'5, tushort) :: (_x_valid_dict_api__t'4, tushort) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _x_valid_dict_api__t'15
      (Efield
        (Ederef (Etempvar _x_valid_dict_api__t (tptr (Tstruct ___gp_fse_t noattr)))
          (Tstruct ___gp_fse_t noattr)) _log tuint))
    (Sset _size
      (Ebinop Oshl (Econst_int (Int.repr 1) tuint) (Etempvar _x_valid_dict_api__t'15 tuint)
        tuint)))
  (Ssequence
    (Sset _n (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Ssequence
        (Sset _s (Econst_int (Int.repr 0) tint))
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _s tuint)
                           (Etempvar _size tuint) tint)
              Sskip
              Sbreak)
            (Ssequence
              (Sset _x_valid_dict_api__t'13
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef
                        (Etempvar _x_valid_dict_api__t (tptr (Tstruct ___gp_fse_t noattr)))
                        (Tstruct ___gp_fse_t noattr)) _sym
                      (tarray tuchar 512)) (Etempvar _s tuint) (tptr tuchar))
                  tuchar))
              (Ssequence
                (Sset _x_valid_dict_api__t'14
                  (Ederef
                    (Ebinop Oadd (Etempvar _c (tptr tuchar))
                      (Ebinop Osub (Etempvar _k tulong)
                        (Econst_int (Int.repr 1) tint) tulong) (tptr tuchar))
                    tuchar))
                (Sifthenelse (Ebinop Oeq (Etempvar _x_valid_dict_api__t'13 tuchar)
                               (Etempvar _x_valid_dict_api__t'14 tuchar) tint)
                  (Sset _n
                    (Ebinop Oadd (Etempvar _n tuint)
                      (Econst_int (Int.repr 1) tint) tuint))
                  Sskip))))
          (Sset _s
            (Ebinop Oadd (Etempvar _s tuint) (Econst_int (Int.repr 1) tint)
              tuint))))
      (Ssequence
        (Scall None
          (Evar _gp_assert (Tfunction (tint :: nil) tvoid cc_default))
          ((Ebinop Ogt (Etempvar _n tuint) (Econst_int (Int.repr 0) tint)
             tint) :: nil))
        (Ssequence
          (Ssequence
            (Scall (Some _x_valid_dict_api__t'1)
              (Evar _choose (Tfunction (tuint :: nil) tuint cc_default))
              ((Etempvar _n tuint) :: nil))
            (Sset _pick (Etempvar _x_valid_dict_api__t'1 tuint)))
          (Ssequence
            (Ssequence
              (Sset _s (Econst_int (Int.repr 0) tint))
              (Sloop
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Etempvar _s tuint)
                                 (Etempvar _size tuint) tint)
                    Sskip
                    Sbreak)
                  (Ssequence
                    (Sset _x_valid_dict_api__t'11
                      (Ederef
                        (Ebinop Oadd
                          (Efield
                            (Ederef
                              (Etempvar _x_valid_dict_api__t (tptr (Tstruct ___gp_fse_t noattr)))
                              (Tstruct ___gp_fse_t noattr)) _sym
                            (tarray tuchar 512)) (Etempvar _s tuint)
                          (tptr tuchar)) tuchar))
                    (Ssequence
                      (Sset _x_valid_dict_api__t'12
                        (Ederef
                          (Ebinop Oadd (Etempvar _c (tptr tuchar))
                            (Ebinop Osub (Etempvar _k tulong)
                              (Econst_int (Int.repr 1) tint) tulong)
                            (tptr tuchar)) tuchar))
                      (Sifthenelse (Ebinop Oeq (Etempvar _x_valid_dict_api__t'11 tuchar)
                                     (Etempvar _x_valid_dict_api__t'12 tuchar) tint)
                        (Ssequence
                          (Sifthenelse (Ebinop Oeq (Etempvar _pick tuint)
                                         (Econst_int (Int.repr 0) tint) tint)
                            (Sassign
                              (Ederef
                                (Ebinop Oadd (Etempvar _x_valid_dict_api__st (tptr tushort))
                                  (Ebinop Osub (Etempvar _k tulong)
                                    (Econst_int (Int.repr 1) tint) tulong)
                                  (tptr tushort)) tushort)
                              (Ecast (Etempvar _s tuint) tushort))
                            Sskip)
                          (Sset _pick
                            (Ebinop Osub (Etempvar _pick tuint)
                              (Econst_int (Int.repr 1) tint) tuint)))
                        Sskip))))
                (Sset _s
                  (Ebinop Oadd (Etempvar _s tuint)
                    (Econst_int (Int.repr 1) tint) tuint))))
            (Ssequence
              (Sset _i
                (Ebinop Osub (Etempvar _k tulong)
                  (Econst_int (Int.repr 1) tint) tulong))
              (Swhile
                (Ebinop Ogt (Etempvar _i tulong)
                  (Econst_int (Int.repr 0) tint) tint)
                (Ssequence
                  (Sset _found (Econst_int (Int.repr 0) tint))
                  (Ssequence
                    (Sset _i
                      (Ebinop Osub (Etempvar _i tulong)
                        (Econst_int (Int.repr 1) tint) tulong))
                    (Ssequence
                      (Ssequence
                        (Sset _s (Econst_int (Int.repr 0) tint))
                        (Sloop
                          (Ssequence
                            (Sifthenelse (Ebinop Olt (Etempvar _s tuint)
                                           (Etempvar _size tuint) tint)
                              Sskip
                              Sbreak)
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Sset _x_valid_dict_api__t'7
                                    (Ederef
                                      (Ebinop Oadd
                                        (Efield
                                          (Ederef
                                            (Etempvar _x_valid_dict_api__t (tptr (Tstruct ___gp_fse_t noattr)))
                                            (Tstruct ___gp_fse_t noattr))
                                          _sym (tarray tuchar 512))
                                        (Etempvar _s tuint) (tptr tuchar))
                                      tuchar))
                                  (Ssequence
                                    (Sset _x_valid_dict_api__t'8
                                      (Ederef
                                        (Ebinop Oadd
                                          (Etempvar _c (tptr tuchar))
                                          (Etempvar _i tulong) (tptr tuchar))
                                        tuchar))
                                    (Sifthenelse (Ebinop Oeq
                                                   (Etempvar _x_valid_dict_api__t'7 tuchar)
                                                   (Etempvar _x_valid_dict_api__t'8 tuchar)
                                                   tint)
                                      (Ssequence
                                        (Sset _x_valid_dict_api__t'9
                                          (Ederef
                                            (Ebinop Oadd
                                              (Efield
                                                (Ederef
                                                  (Etempvar _x_valid_dict_api__t (tptr (Tstruct ___gp_fse_t noattr)))
                                                  (Tstruct ___gp_fse_t noattr))
                                                _base (tarray tushort 512))
                                              (Etempvar _s tuint)
                                              (tptr tushort)) tushort))
                                        (Ssequence
                                          (Sset _x_valid_dict_api__t'10
                                            (Ederef
                                              (Ebinop Oadd
                                                (Etempvar _x_valid_dict_api__st (tptr tushort))
                                                (Ebinop Oadd
                                                  (Etempvar _i tulong)
                                                  (Econst_int (Int.repr 1) tint)
                                                  tulong) (tptr tushort))
                                              tushort))
                                          (Sset _x_valid_dict_api__t'2
                                            (Ecast
                                              (Ebinop Ole
                                                (Etempvar _x_valid_dict_api__t'9 tushort)
                                                (Etempvar _x_valid_dict_api__t'10 tushort)
                                                tint) tbool))))
                                      (Sset _x_valid_dict_api__t'2
                                        (Econst_int (Int.repr 0) tint)))))
                                (Sifthenelse (Etempvar _x_valid_dict_api__t'2 tint)
                                  (Ssequence
                                    (Sset _x_valid_dict_api__t'4
                                      (Ederef
                                        (Ebinop Oadd
                                          (Etempvar _x_valid_dict_api__st (tptr tushort))
                                          (Ebinop Oadd (Etempvar _i tulong)
                                            (Econst_int (Int.repr 1) tint)
                                            tulong) (tptr tushort)) tushort))
                                    (Ssequence
                                      (Sset _x_valid_dict_api__t'5
                                        (Ederef
                                          (Ebinop Oadd
                                            (Efield
                                              (Ederef
                                                (Etempvar _x_valid_dict_api__t (tptr (Tstruct ___gp_fse_t noattr)))
                                                (Tstruct ___gp_fse_t noattr))
                                              _base (tarray tushort 512))
                                            (Etempvar _s tuint)
                                            (tptr tushort)) tushort))
                                      (Ssequence
                                        (Sset _x_valid_dict_api__t'6
                                          (Ederef
                                            (Ebinop Oadd
                                              (Efield
                                                (Ederef
                                                  (Etempvar _x_valid_dict_api__t (tptr (Tstruct ___gp_fse_t noattr)))
                                                  (Tstruct ___gp_fse_t noattr))
                                                _nb (tarray tuchar 512))
                                              (Etempvar _s tuint)
                                              (tptr tuchar)) tuchar))
                                        (Sset _x_valid_dict_api__t'3
                                          (Ecast
                                            (Ebinop Olt
                                              (Ebinop Osub
                                                (Etempvar _x_valid_dict_api__t'4 tushort)
                                                (Etempvar _x_valid_dict_api__t'5 tushort) tint)
                                              (Ebinop Oshl
                                                (Econst_int (Int.repr 1) tuint)
                                                (Etempvar _x_valid_dict_api__t'6 tuchar) tuint)
                                              tint) tbool)))))
                                  (Sset _x_valid_dict_api__t'3 (Econst_int (Int.repr 0) tint))))
                              (Sifthenelse (Etempvar _x_valid_dict_api__t'3 tint)
                                (Ssequence
                                  (Sassign
                                    (Ederef
                                      (Ebinop Oadd
                                        (Etempvar _x_valid_dict_api__st (tptr tushort))
                                        (Etempvar _i tulong) (tptr tushort))
                                      tushort)
                                    (Ecast (Etempvar _s tuint) tushort))
                                  (Sset _found
                                    (Econst_int (Int.repr 1) tint)))
                                Sskip)))
                          (Sset _s
                            (Ebinop Oadd (Etempvar _s tuint)
                              (Econst_int (Int.repr 1) tint) tuint))))
                      (Scall None
                        (Evar _gp_assume (Tfunction (tint :: nil) tvoid
                                           cc_default))
                        ((Etempvar _found tuint) :: nil)))))))))))))
|}.

Definition v_x_valid_dict_api__pre_LL := {|
  gvar_info := (tarray tshort 36);
  gvar_init := (Init_int16 (Int.repr 4) :: Init_int16 (Int.repr 3) ::
                Init_int16 (Int.repr 2) :: Init_int16 (Int.repr 2) ::
                Init_int16 (Int.repr 2) :: Init_int16 (Int.repr 2) ::
                Init_int16 (Int.repr 2) :: Init_int16 (Int.repr 2) ::
                Init_int16 (Int.repr 2) :: Init_int16 (Int.repr 2) ::
                Init_int16 (Int.repr 2) :: Init_int16 (Int.repr 2) ::
                Init_int16 (Int.repr 2) :: Init_int16 (Int.repr 1) ::
                Init_int16 (Int.repr 1) :: Init_int16 (Int.repr 1) ::
                Init_int16 (Int.repr 2) :: Init_int16 (Int.repr 2) ::
                Init_int16 (Int.repr 2) :: Init_int16 (Int.repr 2) ::
                Init_int16 (Int.repr 2) :: Init_int16 (Int.repr 2) ::
                Init_int16 (Int.repr 2) :: Init_int16 (Int.repr 2) ::
                Init_int16 (Int.repr 2) :: Init_int16 (Int.repr 3) ::
                Init_int16 (Int.repr 2) :: Init_int16 (Int.repr 1) ::
                Init_int16 (Int.repr 1) :: Init_int16 (Int.repr 1) ::
                Init_int16 (Int.repr 1) :: Init_int16 (Int.repr 1) ::
                Init_int16 (Int.repr (-1)) :: Init_int16 (Int.repr (-1)) ::
                Init_int16 (Int.repr (-1)) :: Init_int16 (Int.repr (-1)) ::
                nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_x_valid_dict_api__pre_ML := {|
  gvar_info := (tarray tshort 53);
  gvar_init := (Init_int16 (Int.repr 1) :: Init_int16 (Int.repr 4) ::
                Init_int16 (Int.repr 3) :: Init_int16 (Int.repr 2) ::
                Init_int16 (Int.repr 2) :: Init_int16 (Int.repr 2) ::
                Init_int16 (Int.repr 2) :: Init_int16 (Int.repr 2) ::
                Init_int16 (Int.repr 2) :: Init_int16 (Int.repr 1) ::
                Init_int16 (Int.repr 1) :: Init_int16 (Int.repr 1) ::
                Init_int16 (Int.repr 1) :: Init_int16 (Int.repr 1) ::
                Init_int16 (Int.repr 1) :: Init_int16 (Int.repr 1) ::
                Init_int16 (Int.repr 1) :: Init_int16 (Int.repr 1) ::
                Init_int16 (Int.repr 1) :: Init_int16 (Int.repr 1) ::
                Init_int16 (Int.repr 1) :: Init_int16 (Int.repr 1) ::
                Init_int16 (Int.repr 1) :: Init_int16 (Int.repr 1) ::
                Init_int16 (Int.repr 1) :: Init_int16 (Int.repr 1) ::
                Init_int16 (Int.repr 1) :: Init_int16 (Int.repr 1) ::
                Init_int16 (Int.repr 1) :: Init_int16 (Int.repr 1) ::
                Init_int16 (Int.repr 1) :: Init_int16 (Int.repr 1) ::
                Init_int16 (Int.repr 1) :: Init_int16 (Int.repr 1) ::
                Init_int16 (Int.repr 1) :: Init_int16 (Int.repr 1) ::
                Init_int16 (Int.repr 1) :: Init_int16 (Int.repr 1) ::
                Init_int16 (Int.repr 1) :: Init_int16 (Int.repr 1) ::
                Init_int16 (Int.repr 1) :: Init_int16 (Int.repr 1) ::
                Init_int16 (Int.repr 1) :: Init_int16 (Int.repr 1) ::
                Init_int16 (Int.repr 1) :: Init_int16 (Int.repr 1) ::
                Init_int16 (Int.repr (-1)) :: Init_int16 (Int.repr (-1)) ::
                Init_int16 (Int.repr (-1)) :: Init_int16 (Int.repr (-1)) ::
                Init_int16 (Int.repr (-1)) :: Init_int16 (Int.repr (-1)) ::
                Init_int16 (Int.repr (-1)) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_x_valid_dict_api__pre_OF := {|
  gvar_info := (tarray tshort 29);
  gvar_init := (Init_int16 (Int.repr 1) :: Init_int16 (Int.repr 1) ::
                Init_int16 (Int.repr 1) :: Init_int16 (Int.repr 1) ::
                Init_int16 (Int.repr 1) :: Init_int16 (Int.repr 1) ::
                Init_int16 (Int.repr 2) :: Init_int16 (Int.repr 2) ::
                Init_int16 (Int.repr 2) :: Init_int16 (Int.repr 1) ::
                Init_int16 (Int.repr 1) :: Init_int16 (Int.repr 1) ::
                Init_int16 (Int.repr 1) :: Init_int16 (Int.repr 1) ::
                Init_int16 (Int.repr 1) :: Init_int16 (Int.repr 1) ::
                Init_int16 (Int.repr 1) :: Init_int16 (Int.repr 1) ::
                Init_int16 (Int.repr 1) :: Init_int16 (Int.repr 1) ::
                Init_int16 (Int.repr 1) :: Init_int16 (Int.repr 1) ::
                Init_int16 (Int.repr 1) :: Init_int16 (Int.repr 1) ::
                Init_int16 (Int.repr (-1)) :: Init_int16 (Int.repr (-1)) ::
                Init_int16 (Int.repr (-1)) :: Init_int16 (Int.repr (-1)) ::
                Init_int16 (Int.repr (-1)) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_fse_predefined := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_x_valid_dict_api__t, (tptr (Tstruct ___gp_fse_t noattr))) ::
                (_type, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_n, (tptr tshort)) :: (_k, tuint) :: (_s, tuint) ::
               (_x_valid_dict_api__t'3, tint) :: (_x_valid_dict_api__t'2, tint) :: (_x_valid_dict_api__t'1, (tptr tshort)) ::
               (_x_valid_dict_api__t'4, tshort) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sifthenelse (Ebinop Oeq (Etempvar _type tuint)
                   (Econst_int (Int.repr 0) tint) tint)
      (Sset _x_valid_dict_api__t'1 (Ecast (Evar _x_valid_dict_api__pre_LL (tarray tshort 36)) (tptr tshort)))
      (Sifthenelse (Ebinop Oeq (Etempvar _type tuint)
                     (Econst_int (Int.repr 1) tint) tint)
        (Ssequence
          (Sset _x_valid_dict_api__t'1 (Ecast (Evar _x_valid_dict_api__pre_OF (tarray tshort 29)) (tptr tshort)))
          (Sset _x_valid_dict_api__t'1 (Ecast (Etempvar _x_valid_dict_api__t'1 (tptr tshort)) (tptr tshort))))
        (Ssequence
          (Sset _x_valid_dict_api__t'1 (Ecast (Evar _x_valid_dict_api__pre_ML (tarray tshort 53)) (tptr tshort)))
          (Sset _x_valid_dict_api__t'1 (Ecast (Etempvar _x_valid_dict_api__t'1 (tptr tshort)) (tptr tshort))))))
    (Sset _n (Etempvar _x_valid_dict_api__t'1 (tptr tshort))))
  (Ssequence
    (Ssequence
      (Sifthenelse (Ebinop Oeq (Etempvar _type tuint)
                     (Econst_int (Int.repr 0) tint) tint)
        (Sset _x_valid_dict_api__t'2 (Ecast (Econst_int (Int.repr 36) tint) tint))
        (Sifthenelse (Ebinop Oeq (Etempvar _type tuint)
                       (Econst_int (Int.repr 1) tint) tint)
          (Ssequence
            (Sset _x_valid_dict_api__t'2 (Ecast (Econst_int (Int.repr 29) tint) tint))
            (Sset _x_valid_dict_api__t'2 (Ecast (Etempvar _x_valid_dict_api__t'2 tint) tint)))
          (Ssequence
            (Sset _x_valid_dict_api__t'2 (Ecast (Econst_int (Int.repr 53) tint) tint))
            (Sset _x_valid_dict_api__t'2 (Ecast (Etempvar _x_valid_dict_api__t'2 tint) tint)))))
      (Sset _k (Etempvar _x_valid_dict_api__t'2 tint)))
    (Ssequence
      (Ssequence
        (Sset _s (Econst_int (Int.repr 0) tint))
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _s tuint) (Etempvar _k tuint)
                           tint)
              Sskip
              Sbreak)
            (Ssequence
              (Sset _x_valid_dict_api__t'4
                (Ederef
                  (Ebinop Oadd (Etempvar _n (tptr tshort))
                    (Etempvar _s tuint) (tptr tshort)) tshort))
              (Sassign
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef
                        (Etempvar _x_valid_dict_api__t (tptr (Tstruct ___gp_fse_t noattr)))
                        (Tstruct ___gp_fse_t noattr)) _norm
                      (tarray tshort 53)) (Etempvar _s tuint) (tptr tshort))
                  tshort) (Etempvar _x_valid_dict_api__t'4 tshort))))
          (Sset _s
            (Ebinop Oadd (Etempvar _s tuint) (Econst_int (Int.repr 1) tint)
              tuint))))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _x_valid_dict_api__t (tptr (Tstruct ___gp_fse_t noattr)))
              (Tstruct ___gp_fse_t noattr)) _nsym tuint) (Etempvar _k tuint))
        (Ssequence
          (Ssequence
            (Sifthenelse (Ebinop Oeq (Etempvar _type tuint)
                           (Econst_int (Int.repr 1) tint) tint)
              (Sset _x_valid_dict_api__t'3 (Ecast (Econst_int (Int.repr 5) tint) tint))
              (Sset _x_valid_dict_api__t'3 (Ecast (Econst_int (Int.repr 6) tint) tint)))
            (Sassign
              (Efield
                (Ederef (Etempvar _x_valid_dict_api__t (tptr (Tstruct ___gp_fse_t noattr)))
                  (Tstruct ___gp_fse_t noattr)) _log tuint)
              (Etempvar _x_valid_dict_api__t'3 tint)))
          (Scall None
            (Evar _fse_build (Tfunction
                               ((tptr (Tstruct ___gp_fse_t noattr)) :: nil)
                               tvoid cc_default))
            ((Etempvar _x_valid_dict_api__t (tptr (Tstruct ___gp_fse_t noattr))) :: nil)))))))
|}.

Definition f_huf_pick := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_h, (tptr (Tstruct ___gp_huf_t noattr))) :: nil);
  fn_vars := ((_depth, (tarray tuchar 256)) :: nil);
  fn_temps := ((_leaves, tuint) :: (_x_valid_dict_api__t, tuint) :: (_splits, tuint) ::
               (_i, tuint) :: (_s, tuint) :: (_w, tuint) :: (_cell, tuint) ::
               (_j, tuint) :: (_j__1, tuint) :: (_d, tuchar) ::
               (_x_valid_dict_api__t'6, tuint) :: (_x_valid_dict_api__t'5, tuint) :: (_x_valid_dict_api__t'4, tuint) ::
               (_x_valid_dict_api__t'3, tint) :: (_x_valid_dict_api__t'2, tuint) :: (_x_valid_dict_api__t'1, tuint) ::
               (_x_valid_dict_api__t'21, tuchar) :: (_x_valid_dict_api__t'20, tuchar) :: (_x_valid_dict_api__t'19, tuchar) ::
               (_x_valid_dict_api__t'18, tuchar) :: (_x_valid_dict_api__t'17, tuchar) :: (_x_valid_dict_api__t'16, tuchar) ::
               (_x_valid_dict_api__t'15, tuint) :: (_x_valid_dict_api__t'14, tuchar) :: (_x_valid_dict_api__t'13, tuchar) ::
               (_x_valid_dict_api__t'12, tuint) :: (_x_valid_dict_api__t'11, tuint) :: (_x_valid_dict_api__t'10, tuint) ::
               (_x_valid_dict_api__t'9, tuint) :: (_x_valid_dict_api__t'8, tuchar) :: (_x_valid_dict_api__t'7, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _leaves (Econst_int (Int.repr 1) tint))
  (Ssequence
    (Sassign
      (Ederef
        (Ebinop Oadd (Evar _depth (tarray tuchar 256))
          (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar)
      (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Ssequence
        (Scall (Some _x_valid_dict_api__t'1)
          (Evar _choose (Tfunction (tuint :: nil) tuint cc_default))
          ((Econst_int (Int.repr 255) tint) :: nil))
        (Sset _splits
          (Ebinop Oadd (Econst_int (Int.repr 1) tint) (Etempvar _x_valid_dict_api__t'1 tuint)
            tuint)))
      (Ssequence
        (Ssequence
          (Sset _x_valid_dict_api__t (Econst_int (Int.repr 0) tint))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _x_valid_dict_api__t tuint)
                             (Etempvar _splits tuint) tint)
                Sskip
                Sbreak)
              (Ssequence
                (Ssequence
                  (Scall (Some _x_valid_dict_api__t'2)
                    (Evar _choose (Tfunction (tuint :: nil) tuint cc_default))
                    ((Etempvar _leaves tuint) :: nil))
                  (Sset _j (Etempvar _x_valid_dict_api__t'2 tuint)))
                (Ssequence
                  (Ssequence
                    (Sset _x_valid_dict_api__t'21
                      (Ederef
                        (Ebinop Oadd (Evar _depth (tarray tuchar 256))
                          (Etempvar _j tuint) (tptr tuchar)) tuchar))
                    (Sifthenelse (Ebinop Olt (Etempvar _x_valid_dict_api__t'21 tuchar)
                                   (Econst_int (Int.repr 11) tint) tint)
                      (Sset _x_valid_dict_api__t'3
                        (Ecast
                          (Ebinop Olt (Etempvar _leaves tuint)
                            (Econst_int (Int.repr 256) tint) tint) tbool))
                      (Sset _x_valid_dict_api__t'3 (Econst_int (Int.repr 0) tint))))
                  (Sifthenelse (Etempvar _x_valid_dict_api__t'3 tint)
                    (Ssequence
                      (Ssequence
                        (Sset _x_valid_dict_api__t'20
                          (Ederef
                            (Ebinop Oadd (Evar _depth (tarray tuchar 256))
                              (Etempvar _j tuint) (tptr tuchar)) tuchar))
                        (Sassign
                          (Ederef
                            (Ebinop Oadd (Evar _depth (tarray tuchar 256))
                              (Etempvar _j tuint) (tptr tuchar)) tuchar)
                          (Ebinop Oadd (Etempvar _x_valid_dict_api__t'20 tuchar)
                            (Econst_int (Int.repr 1) tint) tint)))
                      (Ssequence
                        (Ssequence
                          (Sset _x_valid_dict_api__t'19
                            (Ederef
                              (Ebinop Oadd (Evar _depth (tarray tuchar 256))
                                (Etempvar _j tuint) (tptr tuchar)) tuchar))
                          (Sassign
                            (Ederef
                              (Ebinop Oadd (Evar _depth (tarray tuchar 256))
                                (Etempvar _leaves tuint) (tptr tuchar))
                              tuchar) (Etempvar _x_valid_dict_api__t'19 tuchar)))
                        (Sset _leaves
                          (Ebinop Oadd (Etempvar _leaves tuint)
                            (Econst_int (Int.repr 1) tint) tuint))))
                    Sskip))))
            (Sset _x_valid_dict_api__t
              (Ebinop Oadd (Etempvar _x_valid_dict_api__t tuint) (Econst_int (Int.repr 1) tint)
                tuint))))
        (Ssequence
          (Ssequence
            (Sset _i (Etempvar _leaves tuint))
            (Sloop
              (Ssequence
                (Sifthenelse (Ebinop Ogt (Etempvar _i tuint)
                               (Econst_int (Int.repr 1) tint) tint)
                  Sskip
                  Sbreak)
                (Ssequence
                  (Ssequence
                    (Scall (Some _x_valid_dict_api__t'4)
                      (Evar _choose (Tfunction (tuint :: nil) tuint
                                      cc_default))
                      ((Etempvar _i tuint) :: nil))
                    (Sset _j__1 (Etempvar _x_valid_dict_api__t'4 tuint)))
                  (Ssequence
                    (Ssequence
                      (Sset _x_valid_dict_api__t'18
                        (Ederef
                          (Ebinop Oadd (Evar _depth (tarray tuchar 256))
                            (Ebinop Osub (Etempvar _i tuint)
                              (Econst_int (Int.repr 1) tint) tuint)
                            (tptr tuchar)) tuchar))
                      (Sset _d (Ecast (Etempvar _x_valid_dict_api__t'18 tuchar) tuchar)))
                    (Ssequence
                      (Ssequence
                        (Sset _x_valid_dict_api__t'17
                          (Ederef
                            (Ebinop Oadd (Evar _depth (tarray tuchar 256))
                              (Etempvar _j__1 tuint) (tptr tuchar)) tuchar))
                        (Sassign
                          (Ederef
                            (Ebinop Oadd (Evar _depth (tarray tuchar 256))
                              (Ebinop Osub (Etempvar _i tuint)
                                (Econst_int (Int.repr 1) tint) tuint)
                              (tptr tuchar)) tuchar) (Etempvar _x_valid_dict_api__t'17 tuchar)))
                      (Sassign
                        (Ederef
                          (Ebinop Oadd (Evar _depth (tarray tuchar 256))
                            (Etempvar _j__1 tuint) (tptr tuchar)) tuchar)
                        (Etempvar _d tuchar))))))
              (Sset _i
                (Ebinop Osub (Etempvar _i tuint)
                  (Econst_int (Int.repr 1) tint) tuint))))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _h (tptr (Tstruct ___gp_huf_t noattr)))
                  (Tstruct ___gp_huf_t noattr)) _log tuint)
              (Econst_int (Int.repr 0) tint))
            (Ssequence
              (Ssequence
                (Sset _i (Econst_int (Int.repr 0) tint))
                (Sloop
                  (Ssequence
                    (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                                   (Etempvar _leaves tuint) tint)
                      Sskip
                      Sbreak)
                    (Ssequence
                      (Sset _x_valid_dict_api__t'14
                        (Ederef
                          (Ebinop Oadd (Evar _depth (tarray tuchar 256))
                            (Etempvar _i tuint) (tptr tuchar)) tuchar))
                      (Ssequence
                        (Sset _x_valid_dict_api__t'15
                          (Efield
                            (Ederef
                              (Etempvar _h (tptr (Tstruct ___gp_huf_t noattr)))
                              (Tstruct ___gp_huf_t noattr)) _log tuint))
                        (Sifthenelse (Ebinop Ogt (Etempvar _x_valid_dict_api__t'14 tuchar)
                                       (Etempvar _x_valid_dict_api__t'15 tuint) tint)
                          (Ssequence
                            (Sset _x_valid_dict_api__t'16
                              (Ederef
                                (Ebinop Oadd
                                  (Evar _depth (tarray tuchar 256))
                                  (Etempvar _i tuint) (tptr tuchar)) tuchar))
                            (Sassign
                              (Efield
                                (Ederef
                                  (Etempvar _h (tptr (Tstruct ___gp_huf_t noattr)))
                                  (Tstruct ___gp_huf_t noattr)) _log tuint)
                              (Etempvar _x_valid_dict_api__t'16 tuchar)))
                          Sskip))))
                  (Sset _i
                    (Ebinop Oadd (Etempvar _i tuint)
                      (Econst_int (Int.repr 1) tint) tuint))))
              (Ssequence
                (Ssequence
                  (Sset _s (Econst_int (Int.repr 0) tint))
                  (Sloop
                    (Ssequence
                      (Sifthenelse (Ebinop Olt (Etempvar _s tuint)
                                     (Econst_int (Int.repr 256) tint) tint)
                        Sskip
                        Sbreak)
                      (Sassign
                        (Ederef
                          (Ebinop Oadd
                            (Efield
                              (Ederef
                                (Etempvar _h (tptr (Tstruct ___gp_huf_t noattr)))
                                (Tstruct ___gp_huf_t noattr)) _w
                              (tarray tuchar 256)) (Etempvar _s tuint)
                            (tptr tuchar)) tuchar)
                        (Econst_int (Int.repr 0) tint)))
                    (Sset _s
                      (Ebinop Oadd (Etempvar _s tuint)
                        (Econst_int (Int.repr 1) tint) tuint))))
                (Ssequence
                  (Ssequence
                    (Scall (Some _x_valid_dict_api__t'5)
                      (Evar _choose (Tfunction (tuint :: nil) tuint
                                      cc_default))
                      ((Ebinop Osub (Econst_int (Int.repr 257) tint)
                         (Etempvar _leaves tuint) tuint) :: nil))
                    (Sset _s (Etempvar _x_valid_dict_api__t'5 tuint)))
                  (Ssequence
                    (Ssequence
                      (Sset _i (Econst_int (Int.repr 0) tint))
                      (Sloop
                        (Ssequence
                          (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                                         (Etempvar _leaves tuint) tint)
                            Sskip
                            Sbreak)
                          (Ssequence
                            (Scall None
                              (Evar _gp_assert (Tfunction (tint :: nil) tvoid
                                                 cc_default))
                              ((Ebinop Ole (Etempvar _s tuint)
                                 (Econst_int (Int.repr 255) tint) tint) ::
                               nil))
                            (Ssequence
                              (Ssequence
                                (Sset _x_valid_dict_api__t'12
                                  (Efield
                                    (Ederef
                                      (Etempvar _h (tptr (Tstruct ___gp_huf_t noattr)))
                                      (Tstruct ___gp_huf_t noattr)) _log
                                    tuint))
                                (Ssequence
                                  (Sset _x_valid_dict_api__t'13
                                    (Ederef
                                      (Ebinop Oadd
                                        (Evar _depth (tarray tuchar 256))
                                        (Etempvar _i tuint) (tptr tuchar))
                                      tuchar))
                                  (Sassign
                                    (Ederef
                                      (Ebinop Oadd
                                        (Efield
                                          (Ederef
                                            (Etempvar _h (tptr (Tstruct ___gp_huf_t noattr)))
                                            (Tstruct ___gp_huf_t noattr)) _w
                                          (tarray tuchar 256))
                                        (Etempvar _s tuint) (tptr tuchar))
                                      tuchar)
                                    (Ecast
                                      (Ebinop Osub
                                        (Ebinop Oadd (Etempvar _x_valid_dict_api__t'12 tuint)
                                          (Econst_int (Int.repr 1) tint)
                                          tuint) (Etempvar _x_valid_dict_api__t'13 tuchar)
                                        tuint) tuchar))))
                              (Ssequence
                                (Sassign
                                  (Ederef
                                    (Ebinop Oadd
                                      (Efield
                                        (Ederef
                                          (Etempvar _h (tptr (Tstruct ___gp_huf_t noattr)))
                                          (Tstruct ___gp_huf_t noattr)) _used
                                        (tarray tuchar 256))
                                      (Etempvar _i tuint) (tptr tuchar))
                                    tuchar)
                                  (Ecast (Etempvar _s tuint) tuchar))
                                (Ssequence
                                  (Sassign
                                    (Efield
                                      (Ederef
                                        (Etempvar _h (tptr (Tstruct ___gp_huf_t noattr)))
                                        (Tstruct ___gp_huf_t noattr)) _last
                                      tuint) (Etempvar _s tuint))
                                  (Sifthenelse (Ebinop Olt
                                                 (Ebinop Oadd
                                                   (Etempvar _i tuint)
                                                   (Econst_int (Int.repr 1) tint)
                                                   tuint)
                                                 (Etempvar _leaves tuint)
                                                 tint)
                                    (Ssequence
                                      (Scall (Some _x_valid_dict_api__t'6)
                                        (Evar _choose (Tfunction
                                                        (tuint :: nil) tuint
                                                        cc_default))
                                        ((Ebinop Osub
                                           (Ebinop Osub
                                             (Econst_int (Int.repr 256) tint)
                                             (Etempvar _s tuint) tuint)
                                           (Ebinop Osub
                                             (Ebinop Osub
                                               (Etempvar _leaves tuint)
                                               (Etempvar _i tuint) tuint)
                                             (Econst_int (Int.repr 1) tint)
                                             tuint) tuint) :: nil))
                                      (Sset _s
                                        (Ebinop Oadd (Etempvar _s tuint)
                                          (Ebinop Oadd
                                            (Econst_int (Int.repr 1) tint)
                                            (Etempvar _x_valid_dict_api__t'6 tuint) tuint)
                                          tuint)))
                                    Sskip))))))
                        (Sset _i
                          (Ebinop Oadd (Etempvar _i tuint)
                            (Econst_int (Int.repr 1) tint) tuint))))
                    (Ssequence
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _h (tptr (Tstruct ___gp_huf_t noattr)))
                            (Tstruct ___gp_huf_t noattr)) _nused tuint)
                        (Etempvar _leaves tuint))
                      (Ssequence
                        (Sset _cell (Econst_int (Int.repr 0) tint))
                        (Ssequence
                          (Ssequence
                            (Sset _w (Econst_int (Int.repr 1) tint))
                            (Sloop
                              (Ssequence
                                (Ssequence
                                  (Sset _x_valid_dict_api__t'11
                                    (Efield
                                      (Ederef
                                        (Etempvar _h (tptr (Tstruct ___gp_huf_t noattr)))
                                        (Tstruct ___gp_huf_t noattr)) _log
                                      tuint))
                                  (Sifthenelse (Ebinop Ole
                                                 (Etempvar _w tuint)
                                                 (Etempvar _x_valid_dict_api__t'11 tuint) tint)
                                    Sskip
                                    Sbreak))
                                (Ssequence
                                  (Sset _s (Econst_int (Int.repr 0) tint))
                                  (Sloop
                                    (Ssequence
                                      (Ssequence
                                        (Sset _x_valid_dict_api__t'10
                                          (Efield
                                            (Ederef
                                              (Etempvar _h (tptr (Tstruct ___gp_huf_t noattr)))
                                              (Tstruct ___gp_huf_t noattr))
                                            _last tuint))
                                        (Sifthenelse (Ebinop Ole
                                                       (Etempvar _s tuint)
                                                       (Etempvar _x_valid_dict_api__t'10 tuint)
                                                       tint)
                                          Sskip
                                          Sbreak))
                                      (Ssequence
                                        (Sset _x_valid_dict_api__t'8
                                          (Ederef
                                            (Ebinop Oadd
                                              (Efield
                                                (Ederef
                                                  (Etempvar _h (tptr (Tstruct ___gp_huf_t noattr)))
                                                  (Tstruct ___gp_huf_t noattr))
                                                _w (tarray tuchar 256))
                                              (Etempvar _s tuint)
                                              (tptr tuchar)) tuchar))
                                        (Sifthenelse (Ebinop Oeq
                                                       (Etempvar _x_valid_dict_api__t'8 tuchar)
                                                       (Etempvar _w tuint)
                                                       tint)
                                          (Ssequence
                                            (Ssequence
                                              (Sset _x_valid_dict_api__t'9
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _h (tptr (Tstruct ___gp_huf_t noattr)))
                                                    (Tstruct ___gp_huf_t noattr))
                                                  _log tuint))
                                              (Sassign
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _h (tptr (Tstruct ___gp_huf_t noattr)))
                                                        (Tstruct ___gp_huf_t noattr))
                                                      _nb
                                                      (tarray tuchar 256))
                                                    (Etempvar _s tuint)
                                                    (tptr tuchar)) tuchar)
                                                (Ecast
                                                  (Ebinop Osub
                                                    (Ebinop Oadd
                                                      (Etempvar _x_valid_dict_api__t'9 tuint)
                                                      (Econst_int (Int.repr 1) tint)
                                                      tuint)
                                                    (Etempvar _w tuint)
                                                    tuint) tuchar)))
                                            (Ssequence
                                              (Sassign
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _h (tptr (Tstruct ___gp_huf_t noattr)))
                                                        (Tstruct ___gp_huf_t noattr))
                                                      _code
                                                      (tarray tushort 256))
                                                    (Etempvar _s tuint)
                                                    (tptr tushort)) tushort)
                                                (Ecast
                                                  (Ebinop Oshr
                                                    (Etempvar _cell tuint)
                                                    (Ebinop Osub
                                                      (Etempvar _w tuint)
                                                      (Econst_int (Int.repr 1) tint)
                                                      tuint) tuint) tushort))
                                              (Sset _cell
                                                (Ebinop Oadd
                                                  (Etempvar _cell tuint)
                                                  (Ebinop Oshl
                                                    (Econst_int (Int.repr 1) tuint)
                                                    (Ebinop Osub
                                                      (Etempvar _w tuint)
                                                      (Econst_int (Int.repr 1) tint)
                                                      tuint) tuint) tuint))))
                                          Sskip)))
                                    (Sset _s
                                      (Ebinop Oadd (Etempvar _s tuint)
                                        (Econst_int (Int.repr 1) tint) tuint)))))
                              (Sset _w
                                (Ebinop Oadd (Etempvar _w tuint)
                                  (Econst_int (Int.repr 1) tint) tuint))))
                          (Ssequence
                            (Sset _x_valid_dict_api__t'7
                              (Efield
                                (Ederef
                                  (Etempvar _h (tptr (Tstruct ___gp_huf_t noattr)))
                                  (Tstruct ___gp_huf_t noattr)) _log tuint))
                            (Scall None
                              (Evar _gp_assert (Tfunction (tint :: nil) tvoid
                                                 cc_default))
                              ((Ebinop Oeq (Etempvar _cell tuint)
                                 (Ebinop Oshl (Econst_int (Int.repr 1) tuint)
                                   (Etempvar _x_valid_dict_api__t'7 tuint) tuint) tint) :: nil))))))))))))))))
|}.

Definition v_x_valid_dict_api__t := {|
  gvar_info := (Tstruct ___gp_fse_t noattr);
  gvar_init := (Init_space 2164 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_x_valid_dict_api__need := {|
  gvar_info := (tarray tuchar 53);
  gvar_init := (Init_space 53 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_x_valid_dict_api__wv := {|
  gvar_info := (tarray tuchar 256);
  gvar_init := (Init_space 256 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_x_valid_dict_api__st := {|
  gvar_info := (tarray tushort 258);
  gvar_init := (Init_space 516 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_huf_put_fse_weights := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_o, (tptr (Tstruct ___gp_out_t noattr))) ::
                (_h, (tptr (Tstruct ___gp_huf_t noattr))) :: nil);
  fn_vars := ((_b, (Tstruct ___gp_bits_t noattr)) :: nil);
  fn_temps := ((_n, tuint) :: (_i, tuint) :: (_s, tuint) :: (_size, tuint) ::
               (_cnt, tuint) :: (_pick, tuint) :: (_found, tuint) ::
               (_x_valid_dict_api__t'8, tint) :: (_x_valid_dict_api__t'7, tint) :: (_x_valid_dict_api__t'6, tint) ::
               (_x_valid_dict_api__t'5, tuint) :: (_x_valid_dict_api__t'4, tint) :: (_x_valid_dict_api__t'3, tuint) ::
               (_x_valid_dict_api__t'2, tuint) :: (_x_valid_dict_api__t'1, tint) :: (_x_valid_dict_api__t'37, tuchar) ::
               (_x_valid_dict_api__t'36, tuchar) :: (_x_valid_dict_api__t'35, tuint) :: (_x_valid_dict_api__t'34, tuchar) ::
               (_x_valid_dict_api__t'33, tuchar) :: (_x_valid_dict_api__t'32, tuchar) :: (_x_valid_dict_api__t'31, tuchar) ::
               (_x_valid_dict_api__t'30, tuchar) :: (_x_valid_dict_api__t'29, tuchar) :: (_x_valid_dict_api__t'28, tuchar) ::
               (_x_valid_dict_api__t'27, tuchar) :: (_x_valid_dict_api__t'26, tuchar) :: (_x_valid_dict_api__t'25, tuchar) ::
               (_x_valid_dict_api__t'24, tushort) :: (_x_valid_dict_api__t'23, tushort) :: (_x_valid_dict_api__t'22, tuchar) ::
               (_x_valid_dict_api__t'21, tuchar) :: (_x_valid_dict_api__t'20, tuchar) :: (_x_valid_dict_api__t'19, tushort) ::
               (_x_valid_dict_api__t'18, tushort) :: (_x_valid_dict_api__t'17, tuchar) :: (_x_valid_dict_api__t'16, tushort) ::
               (_x_valid_dict_api__t'15, tushort) :: (_x_valid_dict_api__t'14, tushort) :: (_x_valid_dict_api__t'13, tushort) ::
               (_x_valid_dict_api__t'12, tuint) :: (_x_valid_dict_api__t'11, tushort) :: (_x_valid_dict_api__t'10, tuint) ::
               (_x_valid_dict_api__t'9, tushort) :: nil);
  fn_body :=
(Ssequence
  (Sset _n
    (Efield
      (Ederef (Etempvar _h (tptr (Tstruct ___gp_huf_t noattr)))
        (Tstruct ___gp_huf_t noattr)) _last tuint))
  (Ssequence
    (Sassign
      (Efield (Evar _b (Tstruct ___gp_bits_t noattr)) _o
        (tptr (Tstruct ___gp_out_t noattr)))
      (Etempvar _o (tptr (Tstruct ___gp_out_t noattr))))
    (Ssequence
      (Sassign (Efield (Evar _b (Tstruct ___gp_bits_t noattr)) _acc tulong)
        (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Sassign (Efield (Evar _b (Tstruct ___gp_bits_t noattr)) _bits tuint)
          (Econst_int (Int.repr 0) tint))
        (Ssequence
          (Ssequence
            (Sifthenelse (Ebinop Oge (Etempvar _n tuint)
                           (Econst_int (Int.repr 2) tint) tint)
              (Sset _x_valid_dict_api__t'1
                (Ecast
                  (Ebinop Ole (Etempvar _n tuint)
                    (Econst_int (Int.repr 255) tint) tint) tbool))
              (Sset _x_valid_dict_api__t'1 (Econst_int (Int.repr 0) tint)))
            (Scall None
              (Evar _gp_assert (Tfunction (tint :: nil) tvoid cc_default))
              ((Etempvar _x_valid_dict_api__t'1 tint) :: nil)))
          (Ssequence
            (Ssequence
              (Sset _s (Econst_int (Int.repr 0) tint))
              (Sloop
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Etempvar _s tuint)
                                 (Econst_int (Int.repr 53) tint) tint)
                    Sskip
                    Sbreak)
                  (Sassign
                    (Ederef
                      (Ebinop Oadd (Evar _x_valid_dict_api__need (tarray tuchar 53))
                        (Etempvar _s tuint) (tptr tuchar)) tuchar)
                    (Econst_int (Int.repr 0) tint)))
                (Sset _s
                  (Ebinop Oadd (Etempvar _s tuint)
                    (Econst_int (Int.repr 1) tint) tuint))))
            (Ssequence
              (Ssequence
                (Sset _i (Econst_int (Int.repr 0) tint))
                (Sloop
                  (Ssequence
                    (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                                   (Etempvar _n tuint) tint)
                      Sskip
                      Sbreak)
                    (Ssequence
                      (Ssequence
                        (Sset _x_valid_dict_api__t'37
                          (Ederef
                            (Ebinop Oadd
                              (Efield
                                (Ederef
                                  (Etempvar _h (tptr (Tstruct ___gp_huf_t noattr)))
                                  (Tstruct ___gp_huf_t noattr)) _w
                                (tarray tuchar 256)) (Etempvar _i tuint)
                              (tptr tuchar)) tuchar))
                        (Sassign
                          (Ederef
                            (Ebinop Oadd (Evar _x_valid_dict_api__wv (tarray tuchar 256))
                              (Etempvar _i tuint) (tptr tuchar)) tuchar)
                          (Etempvar _x_valid_dict_api__t'37 tuchar)))
                      (Ssequence
                        (Sset _x_valid_dict_api__t'36
                          (Ederef
                            (Ebinop Oadd
                              (Efield
                                (Ederef
                                  (Etempvar _h (tptr (Tstruct ___gp_huf_t noattr)))
                                  (Tstruct ___gp_huf_t noattr)) _w
                                (tarray tuchar 256)) (Etempvar _i tuint)
                              (tptr tuchar)) tuchar))
                        (Sassign
                          (Ederef
                            (Ebinop Oadd (Evar _x_valid_dict_api__need (tarray tuchar 53))
                              (Etempvar _x_valid_dict_api__t'36 tuchar) (tptr tuchar)) tuchar)
                          (Econst_int (Int.repr 1) tint)))))
                  (Sset _i
                    (Ebinop Oadd (Etempvar _i tuint)
                      (Econst_int (Int.repr 1) tint) tuint))))
              (Ssequence
                (Ssequence
                  (Scall (Some _x_valid_dict_api__t'2)
                    (Evar _choose (Tfunction (tuint :: nil) tuint cc_default))
                    ((Econst_int (Int.repr 2) tint) :: nil))
                  (Scall None
                    (Evar _fse_pick (Tfunction
                                      ((tptr (Tstruct ___gp_fse_t noattr)) ::
                                       tuint :: tuint :: (tptr tuchar) ::
                                       nil) tvoid cc_default))
                    ((Eaddrof (Evar _x_valid_dict_api__t (Tstruct ___gp_fse_t noattr))
                       (tptr (Tstruct ___gp_fse_t noattr))) ::
                     (Ebinop Oadd (Econst_int (Int.repr 5) tint)
                       (Etempvar _x_valid_dict_api__t'2 tuint) tuint) ::
                     (Econst_int (Int.repr 11) tint) ::
                     (Evar _x_valid_dict_api__need (tarray tuchar 53)) :: nil)))
                (Ssequence
                  (Scall None
                    (Evar _fse_put_description (Tfunction
                                                 ((tptr (Tstruct ___gp_out_t noattr)) ::
                                                  (tptr (Tstruct ___gp_fse_t noattr)) ::
                                                  nil) tvoid cc_default))
                    ((Etempvar _o (tptr (Tstruct ___gp_out_t noattr))) ::
                     (Eaddrof (Evar _x_valid_dict_api__t (Tstruct ___gp_fse_t noattr))
                       (tptr (Tstruct ___gp_fse_t noattr))) :: nil))
                  (Ssequence
                    (Ssequence
                      (Sset _x_valid_dict_api__t'35
                        (Efield (Evar _x_valid_dict_api__t (Tstruct ___gp_fse_t noattr)) _log
                          tuint))
                      (Sset _size
                        (Ebinop Oshl (Econst_int (Int.repr 1) tuint)
                          (Etempvar _x_valid_dict_api__t'35 tuint) tuint)))
                    (Ssequence
                      (Sset _cnt (Econst_int (Int.repr 0) tint))
                      (Ssequence
                        (Ssequence
                          (Sset _s (Econst_int (Int.repr 0) tint))
                          (Sloop
                            (Ssequence
                              (Sifthenelse (Ebinop Olt (Etempvar _s tuint)
                                             (Etempvar _size tuint) tint)
                                Sskip
                                Sbreak)
                              (Ssequence
                                (Sset _x_valid_dict_api__t'33
                                  (Ederef
                                    (Ebinop Oadd
                                      (Efield
                                        (Evar _x_valid_dict_api__t (Tstruct ___gp_fse_t noattr))
                                        _sym (tarray tuchar 512))
                                      (Etempvar _s tuint) (tptr tuchar))
                                    tuchar))
                                (Ssequence
                                  (Sset _x_valid_dict_api__t'34
                                    (Ederef
                                      (Ebinop Oadd
                                        (Evar _x_valid_dict_api__wv (tarray tuchar 256))
                                        (Ebinop Osub (Etempvar _n tuint)
                                          (Econst_int (Int.repr 1) tint)
                                          tuint) (tptr tuchar)) tuchar))
                                  (Sifthenelse (Ebinop Oeq
                                                 (Etempvar _x_valid_dict_api__t'33 tuchar)
                                                 (Etempvar _x_valid_dict_api__t'34 tuchar)
                                                 tint)
                                    (Sset _cnt
                                      (Ebinop Oadd (Etempvar _cnt tuint)
                                        (Econst_int (Int.repr 1) tint) tuint))
                                    Sskip))))
                            (Sset _s
                              (Ebinop Oadd (Etempvar _s tuint)
                                (Econst_int (Int.repr 1) tint) tuint))))
                        (Ssequence
                          (Ssequence
                            (Scall (Some _x_valid_dict_api__t'3)
                              (Evar _choose (Tfunction (tuint :: nil) tuint
                                              cc_default))
                              ((Etempvar _cnt tuint) :: nil))
                            (Sset _pick (Etempvar _x_valid_dict_api__t'3 tuint)))
                          (Ssequence
                            (Ssequence
                              (Sset _s (Econst_int (Int.repr 0) tint))
                              (Sloop
                                (Ssequence
                                  (Sifthenelse (Ebinop Olt
                                                 (Etempvar _s tuint)
                                                 (Etempvar _size tuint) tint)
                                    Sskip
                                    Sbreak)
                                  (Ssequence
                                    (Sset _x_valid_dict_api__t'31
                                      (Ederef
                                        (Ebinop Oadd
                                          (Efield
                                            (Evar _x_valid_dict_api__t (Tstruct ___gp_fse_t noattr))
                                            _sym (tarray tuchar 512))
                                          (Etempvar _s tuint) (tptr tuchar))
                                        tuchar))
                                    (Ssequence
                                      (Sset _x_valid_dict_api__t'32
                                        (Ederef
                                          (Ebinop Oadd
                                            (Evar _x_valid_dict_api__wv (tarray tuchar 256))
                                            (Ebinop Osub (Etempvar _n tuint)
                                              (Econst_int (Int.repr 1) tint)
                                              tuint) (tptr tuchar)) tuchar))
                                      (Sifthenelse (Ebinop Oeq
                                                     (Etempvar _x_valid_dict_api__t'31 tuchar)
                                                     (Etempvar _x_valid_dict_api__t'32 tuchar)
                                                     tint)
                                        (Ssequence
                                          (Sifthenelse (Ebinop Oeq
                                                         (Etempvar _pick tuint)
                                                         (Econst_int (Int.repr 0) tint)
                                                         tint)
                                            (Sassign
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Evar _x_valid_dict_api__st (tarray tushort 258))
                                                  (Ebinop Osub
                                                    (Etempvar _n tuint)
                                                    (Econst_int (Int.repr 1) tint)
                                                    tuint) (tptr tushort))
                                                tushort)
                                              (Ecast (Etempvar _s tuint)
                                                tushort))
                                            Sskip)
                                          (Sset _pick
                                            (Ebinop Osub
                                              (Etempvar _pick tuint)
                                              (Econst_int (Int.repr 1) tint)
                                              tuint)))
                                        Sskip))))
                                (Sset _s
                                  (Ebinop Oadd (Etempvar _s tuint)
                                    (Econst_int (Int.repr 1) tint) tuint))))
                            (Ssequence
                              (Sset _cnt (Econst_int (Int.repr 0) tint))
                              (Ssequence
                                (Ssequence
                                  (Sset _s (Econst_int (Int.repr 0) tint))
                                  (Sloop
                                    (Ssequence
                                      (Sifthenelse (Ebinop Olt
                                                     (Etempvar _s tuint)
                                                     (Etempvar _size tuint)
                                                     tint)
                                        Sskip
                                        Sbreak)
                                      (Ssequence
                                        (Ssequence
                                          (Sset _x_valid_dict_api__t'28
                                            (Ederef
                                              (Ebinop Oadd
                                                (Efield
                                                  (Evar _x_valid_dict_api__t (Tstruct ___gp_fse_t noattr))
                                                  _sym (tarray tuchar 512))
                                                (Etempvar _s tuint)
                                                (tptr tuchar)) tuchar))
                                          (Ssequence
                                            (Sset _x_valid_dict_api__t'29
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Evar _x_valid_dict_api__wv (tarray tuchar 256))
                                                  (Ebinop Osub
                                                    (Etempvar _n tuint)
                                                    (Econst_int (Int.repr 2) tint)
                                                    tuint) (tptr tuchar))
                                                tuchar))
                                            (Sifthenelse (Ebinop Oeq
                                                           (Etempvar _x_valid_dict_api__t'28 tuchar)
                                                           (Etempvar _x_valid_dict_api__t'29 tuchar)
                                                           tint)
                                              (Ssequence
                                                (Sset _x_valid_dict_api__t'30
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Efield
                                                        (Evar _x_valid_dict_api__t (Tstruct ___gp_fse_t noattr))
                                                        _nb
                                                        (tarray tuchar 512))
                                                      (Etempvar _s tuint)
                                                      (tptr tuchar)) tuchar))
                                                (Sset _x_valid_dict_api__t'4
                                                  (Ecast
                                                    (Ebinop Ogt
                                                      (Etempvar _x_valid_dict_api__t'30 tuchar)
                                                      (Econst_int (Int.repr 0) tint)
                                                      tint) tbool)))
                                              (Sset _x_valid_dict_api__t'4
                                                (Econst_int (Int.repr 0) tint)))))
                                        (Sifthenelse (Etempvar _x_valid_dict_api__t'4 tint)
                                          (Sset _cnt
                                            (Ebinop Oadd
                                              (Etempvar _cnt tuint)
                                              (Econst_int (Int.repr 1) tint)
                                              tuint))
                                          Sskip)))
                                    (Sset _s
                                      (Ebinop Oadd (Etempvar _s tuint)
                                        (Econst_int (Int.repr 1) tint) tuint))))
                                (Ssequence
                                  (Scall None
                                    (Evar _gp_assume (Tfunction (tint :: nil)
                                                       tvoid cc_default))
                                    ((Ebinop Ogt (Etempvar _cnt tuint)
                                       (Econst_int (Int.repr 0) tint) tint) ::
                                     nil))
                                  (Ssequence
                                    (Ssequence
                                      (Scall (Some _x_valid_dict_api__t'5)
                                        (Evar _choose (Tfunction
                                                        (tuint :: nil) tuint
                                                        cc_default))
                                        ((Etempvar _cnt tuint) :: nil))
                                      (Sset _pick (Etempvar _x_valid_dict_api__t'5 tuint)))
                                    (Ssequence
                                      (Ssequence
                                        (Sset _s
                                          (Econst_int (Int.repr 0) tint))
                                        (Sloop
                                          (Ssequence
                                            (Sifthenelse (Ebinop Olt
                                                           (Etempvar _s tuint)
                                                           (Etempvar _size tuint)
                                                           tint)
                                              Sskip
                                              Sbreak)
                                            (Ssequence
                                              (Ssequence
                                                (Sset _x_valid_dict_api__t'25
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Efield
                                                        (Evar _x_valid_dict_api__t (Tstruct ___gp_fse_t noattr))
                                                        _sym
                                                        (tarray tuchar 512))
                                                      (Etempvar _s tuint)
                                                      (tptr tuchar)) tuchar))
                                                (Ssequence
                                                  (Sset _x_valid_dict_api__t'26
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Evar _x_valid_dict_api__wv (tarray tuchar 256))
                                                        (Ebinop Osub
                                                          (Etempvar _n tuint)
                                                          (Econst_int (Int.repr 2) tint)
                                                          tuint)
                                                        (tptr tuchar))
                                                      tuchar))
                                                  (Sifthenelse (Ebinop Oeq
                                                                 (Etempvar _x_valid_dict_api__t'25 tuchar)
                                                                 (Etempvar _x_valid_dict_api__t'26 tuchar)
                                                                 tint)
                                                    (Ssequence
                                                      (Sset _x_valid_dict_api__t'27
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Efield
                                                              (Evar _x_valid_dict_api__t (Tstruct ___gp_fse_t noattr))
                                                              _nb
                                                              (tarray tuchar 512))
                                                            (Etempvar _s tuint)
                                                            (tptr tuchar))
                                                          tuchar))
                                                      (Sset _x_valid_dict_api__t'6
                                                        (Ecast
                                                          (Ebinop Ogt
                                                            (Etempvar _x_valid_dict_api__t'27 tuchar)
                                                            (Econst_int (Int.repr 0) tint)
                                                            tint) tbool)))
                                                    (Sset _x_valid_dict_api__t'6
                                                      (Econst_int (Int.repr 0) tint)))))
                                              (Sifthenelse (Etempvar _x_valid_dict_api__t'6 tint)
                                                (Ssequence
                                                  (Sifthenelse (Ebinop Oeq
                                                                 (Etempvar _pick tuint)
                                                                 (Econst_int (Int.repr 0) tint)
                                                                 tint)
                                                    (Sassign
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _x_valid_dict_api__st (tarray tushort 258))
                                                          (Ebinop Osub
                                                            (Etempvar _n tuint)
                                                            (Econst_int (Int.repr 2) tint)
                                                            tuint)
                                                          (tptr tushort))
                                                        tushort)
                                                      (Ecast
                                                        (Etempvar _s tuint)
                                                        tushort))
                                                    Sskip)
                                                  (Sset _pick
                                                    (Ebinop Osub
                                                      (Etempvar _pick tuint)
                                                      (Econst_int (Int.repr 1) tint)
                                                      tuint)))
                                                Sskip)))
                                          (Sset _s
                                            (Ebinop Oadd (Etempvar _s tuint)
                                              (Econst_int (Int.repr 1) tint)
                                              tuint))))
                                      (Ssequence
                                        (Sset _i
                                          (Ebinop Osub (Etempvar _n tuint)
                                            (Econst_int (Int.repr 2) tint)
                                            tuint))
                                        (Ssequence
                                          (Swhile
                                            (Ebinop Ogt (Etempvar _i tuint)
                                              (Econst_int (Int.repr 0) tint)
                                              tint)
                                            (Ssequence
                                              (Sset _found
                                                (Econst_int (Int.repr 0) tint))
                                              (Ssequence
                                                (Sset _i
                                                  (Ebinop Osub
                                                    (Etempvar _i tuint)
                                                    (Econst_int (Int.repr 1) tint)
                                                    tuint))
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _s
                                                      (Econst_int (Int.repr 0) tint))
                                                    (Sloop
                                                      (Ssequence
                                                        (Sifthenelse 
                                                          (Ebinop Olt
                                                            (Etempvar _s tuint)
                                                            (Etempvar _size tuint)
                                                            tint)
                                                          Sskip
                                                          Sbreak)
                                                        (Ssequence
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _x_valid_dict_api__t'21
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _x_valid_dict_api__t (Tstruct ___gp_fse_t noattr))
                                                                    _sym
                                                                    (tarray tuchar 512))
                                                                    (Etempvar _s tuint)
                                                                    (tptr tuchar))
                                                                  tuchar))
                                                              (Ssequence
                                                                (Sset _x_valid_dict_api__t'22
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_valid_dict_api__wv (tarray tuchar 256))
                                                                    (Etempvar _i tuint)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                (Sifthenelse 
                                                                  (Ebinop Oeq
                                                                    (Etempvar _x_valid_dict_api__t'21 tuchar)
                                                                    (Etempvar _x_valid_dict_api__t'22 tuchar)
                                                                    tint)
                                                                  (Ssequence
                                                                    (Sset _x_valid_dict_api__t'23
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _x_valid_dict_api__t (Tstruct ___gp_fse_t noattr))
                                                                    _base
                                                                    (tarray tushort 512))
                                                                    (Etempvar _s tuint)
                                                                    (tptr tushort))
                                                                    tushort))
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'24
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_valid_dict_api__st (tarray tushort 258))
                                                                    (Ebinop Oadd
                                                                    (Etempvar _i tuint)
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tuint)
                                                                    (tptr tushort))
                                                                    tushort))
                                                                    (Sset _x_valid_dict_api__t'7
                                                                    (Ecast
                                                                    (Ebinop Ole
                                                                    (Etempvar _x_valid_dict_api__t'23 tushort)
                                                                    (Etempvar _x_valid_dict_api__t'24 tushort)
                                                                    tint)
                                                                    tbool))))
                                                                  (Sset _x_valid_dict_api__t'7
                                                                    (Econst_int (Int.repr 0) tint)))))
                                                            (Sifthenelse (Etempvar _x_valid_dict_api__t'7 tint)
                                                              (Ssequence
                                                                (Sset _x_valid_dict_api__t'18
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_valid_dict_api__st (tarray tushort 258))
                                                                    (Ebinop Oadd
                                                                    (Etempvar _i tuint)
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tuint)
                                                                    (tptr tushort))
                                                                    tushort))
                                                                (Ssequence
                                                                  (Sset _x_valid_dict_api__t'19
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _x_valid_dict_api__t (Tstruct ___gp_fse_t noattr))
                                                                    _base
                                                                    (tarray tushort 512))
                                                                    (Etempvar _s tuint)
                                                                    (tptr tushort))
                                                                    tushort))
                                                                  (Ssequence
                                                                    (Sset _x_valid_dict_api__t'20
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _x_valid_dict_api__t (Tstruct ___gp_fse_t noattr))
                                                                    _nb
                                                                    (tarray tuchar 512))
                                                                    (Etempvar _s tuint)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Sset _x_valid_dict_api__t'8
                                                                    (Ecast
                                                                    (Ebinop Olt
                                                                    (Ebinop Osub
                                                                    (Etempvar _x_valid_dict_api__t'18 tushort)
                                                                    (Etempvar _x_valid_dict_api__t'19 tushort)
                                                                    tint)
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tuint)
                                                                    (Etempvar _x_valid_dict_api__t'20 tuchar)
                                                                    tuint)
                                                                    tint)
                                                                    tbool)))))
                                                              (Sset _x_valid_dict_api__t'8
                                                                (Econst_int (Int.repr 0) tint))))
                                                          (Sifthenelse (Etempvar _x_valid_dict_api__t'8 tint)
                                                            (Ssequence
                                                              (Sassign
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Evar _x_valid_dict_api__st (tarray tushort 258))
                                                                    (Etempvar _i tuint)
                                                                    (tptr tushort))
                                                                  tushort)
                                                                (Ecast
                                                                  (Etempvar _s tuint)
                                                                  tushort))
                                                              (Sset _found
                                                                (Econst_int (Int.repr 1) tint)))
                                                            Sskip)))
                                                      (Sset _s
                                                        (Ebinop Oadd
                                                          (Etempvar _s tuint)
                                                          (Econst_int (Int.repr 1) tint)
                                                          tuint))))
                                                  (Scall None
                                                    (Evar _gp_assume 
                                                    (Tfunction (tint :: nil)
                                                      tvoid cc_default))
                                                    ((Etempvar _found tuint) ::
                                                     nil))))))
                                          (Ssequence
                                            (Sset _i
                                              (Ebinop Osub
                                                (Etempvar _n tuint)
                                                (Econst_int (Int.repr 2) tint)
                                                tuint))
                                            (Ssequence
                                              (Swhile
                                                (Ebinop Ogt
                                                  (Etempvar _i tuint)
                                                  (Econst_int (Int.repr 0) tint)
                                                  tint)
                                                (Ssequence
                                                  (Sset _i
                                                    (Ebinop Osub
                                                      (Etempvar _i tuint)
                                                      (Econst_int (Int.repr 1) tint)
                                                      tuint))
                                                  (Ssequence
                                                    (Sset _x_valid_dict_api__t'13
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _x_valid_dict_api__st (tarray tushort 258))
                                                          (Ebinop Oadd
                                                            (Etempvar _i tuint)
                                                            (Econst_int (Int.repr 2) tint)
                                                            tuint)
                                                          (tptr tushort))
                                                        tushort))
                                                    (Ssequence
                                                      (Sset _x_valid_dict_api__t'14
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _x_valid_dict_api__st (tarray tushort 258))
                                                            (Etempvar _i tuint)
                                                            (tptr tushort))
                                                          tushort))
                                                      (Ssequence
                                                        (Sset _x_valid_dict_api__t'15
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Efield
                                                                (Evar _x_valid_dict_api__t (Tstruct ___gp_fse_t noattr))
                                                                _base
                                                                (tarray tushort 512))
                                                              (Etempvar _x_valid_dict_api__t'14 tushort)
                                                              (tptr tushort))
                                                            tushort))
                                                        (Ssequence
                                                          (Sset _x_valid_dict_api__t'16
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _x_valid_dict_api__st (tarray tushort 258))
                                                                (Etempvar _i tuint)
                                                                (tptr tushort))
                                                              tushort))
                                                          (Ssequence
                                                            (Sset _x_valid_dict_api__t'17
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Efield
                                                                    (Evar _x_valid_dict_api__t (Tstruct ___gp_fse_t noattr))
                                                                    _nb
                                                                    (tarray tuchar 512))
                                                                  (Etempvar _x_valid_dict_api__t'16 tushort)
                                                                  (tptr tuchar))
                                                                tuchar))
                                                            (Scall None
                                                              (Evar _bits_put 
                                                              (Tfunction
                                                                ((tptr (Tstruct ___gp_bits_t noattr)) ::
                                                                 tulong ::
                                                                 tuint ::
                                                                 nil) tvoid
                                                                cc_default))
                                                              ((Eaddrof
                                                                 (Evar _b (Tstruct ___gp_bits_t noattr))
                                                                 (tptr (Tstruct ___gp_bits_t noattr))) ::
                                                               (Ebinop Osub
                                                                 (Etempvar _x_valid_dict_api__t'13 tushort)
                                                                 (Etempvar _x_valid_dict_api__t'15 tushort)
                                                                 tint) ::
                                                               (Etempvar _x_valid_dict_api__t'17 tuchar) ::
                                                               nil)))))))))
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _x_valid_dict_api__t'11
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Evar _x_valid_dict_api__st (tarray tushort 258))
                                                        (Econst_int (Int.repr 1) tint)
                                                        (tptr tushort))
                                                      tushort))
                                                  (Ssequence
                                                    (Sset _x_valid_dict_api__t'12
                                                      (Efield
                                                        (Evar _x_valid_dict_api__t (Tstruct ___gp_fse_t noattr))
                                                        _log tuint))
                                                    (Scall None
                                                      (Evar _bits_put 
                                                      (Tfunction
                                                        ((tptr (Tstruct ___gp_bits_t noattr)) ::
                                                         tulong :: tuint ::
                                                         nil) tvoid
                                                        cc_default))
                                                      ((Eaddrof
                                                         (Evar _b (Tstruct ___gp_bits_t noattr))
                                                         (tptr (Tstruct ___gp_bits_t noattr))) ::
                                                       (Etempvar _x_valid_dict_api__t'11 tushort) ::
                                                       (Etempvar _x_valid_dict_api__t'12 tuint) ::
                                                       nil))))
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _x_valid_dict_api__t'9
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _x_valid_dict_api__st (tarray tushort 258))
                                                          (Econst_int (Int.repr 0) tint)
                                                          (tptr tushort))
                                                        tushort))
                                                    (Ssequence
                                                      (Sset _x_valid_dict_api__t'10
                                                        (Efield
                                                          (Evar _x_valid_dict_api__t (Tstruct ___gp_fse_t noattr))
                                                          _log tuint))
                                                      (Scall None
                                                        (Evar _bits_put 
                                                        (Tfunction
                                                          ((tptr (Tstruct ___gp_bits_t noattr)) ::
                                                           tulong :: tuint ::
                                                           nil) tvoid
                                                          cc_default))
                                                        ((Eaddrof
                                                           (Evar _b (Tstruct ___gp_bits_t noattr))
                                                           (tptr (Tstruct ___gp_bits_t noattr))) ::
                                                         (Etempvar _x_valid_dict_api__t'9 tushort) ::
                                                         (Etempvar _x_valid_dict_api__t'10 tuint) ::
                                                         nil))))
                                                  (Scall None
                                                    (Evar _bits_end_mark 
                                                    (Tfunction
                                                      ((tptr (Tstruct ___gp_bits_t noattr)) ::
                                                       nil) tvoid cc_default))
                                                    ((Eaddrof
                                                       (Evar _b (Tstruct ___gp_bits_t noattr))
                                                       (tptr (Tstruct ___gp_bits_t noattr))) ::
                                                     nil)))))))))))))))))))))))))))
|}.

Definition v_x_valid_dict_api__tmp := {|
  gvar_info := (tarray tuchar 512);
  gvar_init := (Init_space 512 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_huf_put_description := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_o, (tptr (Tstruct ___gp_out_t noattr))) ::
                (_h, (tptr (Tstruct ___gp_huf_t noattr))) :: nil);
  fn_vars := ((_t__1, (Tstruct ___gp_out_t noattr)) :: nil);
  fn_temps := ((_direct_ok, tuint) :: (_fse_ok, tuint) ::
               (_use_fse, tuint) :: (_j, tuint) :: (_lo, tuint) ::
               (_x_valid_dict_api__t'4, tint) :: (_x_valid_dict_api__t'3, tuint) :: (_x_valid_dict_api__t'2, tuint) ::
               (_x_valid_dict_api__t'1, tint) :: (_x_valid_dict_api__t'14, tuint) :: (_x_valid_dict_api__t'13, tuint) ::
               (_x_valid_dict_api__t'12, tulong) :: (_x_valid_dict_api__t'11, tulong) :: (_x_valid_dict_api__t'10, tulong) ::
               (_x_valid_dict_api__t'9, tuint) :: (_x_valid_dict_api__t'8, tuint) :: (_x_valid_dict_api__t'7, tuchar) ::
               (_x_valid_dict_api__t'6, tuint) :: (_x_valid_dict_api__t'5, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _x_valid_dict_api__t'14
      (Efield
        (Ederef (Etempvar _h (tptr (Tstruct ___gp_huf_t noattr)))
          (Tstruct ___gp_huf_t noattr)) _last tuint))
    (Sset _direct_ok
      (Ebinop Ole (Etempvar _x_valid_dict_api__t'14 tuint) (Econst_int (Int.repr 128) tint)
        tint)))
  (Ssequence
    (Ssequence
      (Sset _x_valid_dict_api__t'13
        (Efield
          (Ederef (Etempvar _h (tptr (Tstruct ___gp_huf_t noattr)))
            (Tstruct ___gp_huf_t noattr)) _last tuint))
      (Sset _fse_ok
        (Ebinop Oge (Etempvar _x_valid_dict_api__t'13 tuint) (Econst_int (Int.repr 2) tint)
          tint)))
    (Ssequence
      (Ssequence
        (Sifthenelse (Etempvar _direct_ok tuint)
          (Sset _x_valid_dict_api__t'1 (Econst_int (Int.repr 1) tint))
          (Sset _x_valid_dict_api__t'1 (Ecast (Etempvar _fse_ok tuint) tbool)))
        (Scall None
          (Evar _gp_assert (Tfunction (tint :: nil) tvoid cc_default))
          ((Etempvar _x_valid_dict_api__t'1 tint) :: nil)))
      (Ssequence
        (Ssequence
          (Sifthenelse (Eunop Onotbool (Etempvar _direct_ok tuint) tint)
            (Sset _x_valid_dict_api__t'2 (Ecast (Econst_int (Int.repr 1) tint) tuint))
            (Sifthenelse (Eunop Onotbool (Etempvar _fse_ok tuint) tint)
              (Ssequence
                (Sset _x_valid_dict_api__t'2 (Ecast (Econst_int (Int.repr 0) tint) tuint))
                (Sset _x_valid_dict_api__t'2 (Ecast (Etempvar _x_valid_dict_api__t'2 tuint) tuint)))
              (Ssequence
                (Ssequence
                  (Scall (Some _x_valid_dict_api__t'3)
                    (Evar _choose (Tfunction (tuint :: nil) tuint cc_default))
                    ((Econst_int (Int.repr 2) tint) :: nil))
                  (Sset _x_valid_dict_api__t'2 (Ecast (Etempvar _x_valid_dict_api__t'3 tuint) tuint)))
                (Sset _x_valid_dict_api__t'2 (Ecast (Etempvar _x_valid_dict_api__t'2 tuint) tuint)))))
          (Sset _use_fse (Etempvar _x_valid_dict_api__t'2 tuint)))
        (Sifthenelse (Etempvar _use_fse tuint)
          (Ssequence
            (Sassign
              (Efield (Evar _t__1 (Tstruct ___gp_out_t noattr)) _p
                (tptr tuchar)) (Evar _x_valid_dict_api__tmp (tarray tuchar 512)))
            (Ssequence
              (Sassign
                (Efield (Evar _t__1 (Tstruct ___gp_out_t noattr)) _n tulong)
                (Econst_int (Int.repr 0) tint))
              (Ssequence
                (Sassign
                  (Efield (Evar _t__1 (Tstruct ___gp_out_t noattr)) _cap
                    tulong) (Esizeof (tarray tuchar 512) tulong))
                (Ssequence
                  (Scall None
                    (Evar _huf_put_fse_weights (Tfunction
                                                 ((tptr (Tstruct ___gp_out_t noattr)) ::
                                                  (tptr (Tstruct ___gp_huf_t noattr)) ::
                                                  nil) tvoid cc_default))
                    ((Eaddrof (Evar _t__1 (Tstruct ___gp_out_t noattr))
                       (tptr (Tstruct ___gp_out_t noattr))) ::
                     (Etempvar _h (tptr (Tstruct ___gp_huf_t noattr))) ::
                     nil))
                  (Ssequence
                    (Ssequence
                      (Sset _x_valid_dict_api__t'12
                        (Efield (Evar _t__1 (Tstruct ___gp_out_t noattr)) _n
                          tulong))
                      (Scall None
                        (Evar _gp_assume (Tfunction (tint :: nil) tvoid
                                           cc_default))
                        ((Ebinop Ole (Etempvar _x_valid_dict_api__t'12 tulong)
                           (Econst_int (Int.repr 127) tint) tint) :: nil)))
                    (Ssequence
                      (Ssequence
                        (Sset _x_valid_dict_api__t'11
                          (Efield (Evar _t__1 (Tstruct ___gp_out_t noattr))
                            _n tulong))
                        (Scall None
                          (Evar _put8 (Tfunction
                                        ((tptr (Tstruct ___gp_out_t noattr)) ::
                                         tuint :: nil) tvoid cc_default))
                          ((Etempvar _o (tptr (Tstruct ___gp_out_t noattr))) ::
                           (Ecast (Etempvar _x_valid_dict_api__t'11 tulong) tuint) :: nil)))
                      (Ssequence
                        (Sset _x_valid_dict_api__t'10
                          (Efield (Evar _t__1 (Tstruct ___gp_out_t noattr))
                            _n tulong))
                        (Scall None
                          (Evar _put_bytes (Tfunction
                                             ((tptr (Tstruct ___gp_out_t noattr)) ::
                                              (tptr tuchar) :: tulong :: nil)
                                             tvoid cc_default))
                          ((Etempvar _o (tptr (Tstruct ___gp_out_t noattr))) ::
                           (Evar _x_valid_dict_api__tmp (tarray tuchar 512)) ::
                           (Etempvar _x_valid_dict_api__t'10 tulong) :: nil)))))))))
          (Ssequence
            (Ssequence
              (Sset _x_valid_dict_api__t'9
                (Efield
                  (Ederef (Etempvar _h (tptr (Tstruct ___gp_huf_t noattr)))
                    (Tstruct ___gp_huf_t noattr)) _last tuint))
              (Scall None
                (Evar _put8 (Tfunction
                              ((tptr (Tstruct ___gp_out_t noattr)) ::
                               tuint :: nil) tvoid cc_default))
                ((Etempvar _o (tptr (Tstruct ___gp_out_t noattr))) ::
                 (Ebinop Oadd (Econst_int (Int.repr 127) tint)
                   (Etempvar _x_valid_dict_api__t'9 tuint) tuint) :: nil)))
            (Ssequence
              (Sset _j (Econst_int (Int.repr 0) tint))
              (Sloop
                (Ssequence
                  (Ssequence
                    (Sset _x_valid_dict_api__t'8
                      (Efield
                        (Ederef
                          (Etempvar _h (tptr (Tstruct ___gp_huf_t noattr)))
                          (Tstruct ___gp_huf_t noattr)) _last tuint))
                    (Sifthenelse (Ebinop Olt (Etempvar _j tuint)
                                   (Etempvar _x_valid_dict_api__t'8 tuint) tint)
                      Sskip
                      Sbreak))
                  (Ssequence
                    (Ssequence
                      (Ssequence
                        (Sset _x_valid_dict_api__t'6
                          (Efield
                            (Ederef
                              (Etempvar _h (tptr (Tstruct ___gp_huf_t noattr)))
                              (Tstruct ___gp_huf_t noattr)) _last tuint))
                        (Sifthenelse (Ebinop Olt
                                       (Ebinop Oadd (Etempvar _j tuint)
                                         (Econst_int (Int.repr 1) tint)
                                         tuint) (Etempvar _x_valid_dict_api__t'6 tuint) tint)
                          (Ssequence
                            (Sset _x_valid_dict_api__t'7
                              (Ederef
                                (Ebinop Oadd
                                  (Efield
                                    (Ederef
                                      (Etempvar _h (tptr (Tstruct ___gp_huf_t noattr)))
                                      (Tstruct ___gp_huf_t noattr)) _w
                                    (tarray tuchar 256))
                                  (Ebinop Oadd (Etempvar _j tuint)
                                    (Econst_int (Int.repr 1) tint) tuint)
                                  (tptr tuchar)) tuchar))
                            (Sset _x_valid_dict_api__t'4 (Ecast (Etempvar _x_valid_dict_api__t'7 tuchar) tint)))
                          (Sset _x_valid_dict_api__t'4
                            (Ecast (Econst_int (Int.repr 0) tint) tint))))
                      (Sset _lo (Etempvar _x_valid_dict_api__t'4 tint)))
                    (Ssequence
                      (Sset _x_valid_dict_api__t'5
                        (Ederef
                          (Ebinop Oadd
                            (Efield
                              (Ederef
                                (Etempvar _h (tptr (Tstruct ___gp_huf_t noattr)))
                                (Tstruct ___gp_huf_t noattr)) _w
                              (tarray tuchar 256)) (Etempvar _j tuint)
                            (tptr tuchar)) tuchar))
                      (Scall None
                        (Evar _put8 (Tfunction
                                      ((tptr (Tstruct ___gp_out_t noattr)) ::
                                       tuint :: nil) tvoid cc_default))
                        ((Etempvar _o (tptr (Tstruct ___gp_out_t noattr))) ::
                         (Ebinop Oor
                           (Ebinop Oshl (Ecast (Etempvar _x_valid_dict_api__t'5 tuchar) tuint)
                             (Econst_int (Int.repr 4) tint) tuint)
                           (Etempvar _lo tuint) tuint) :: nil)))))
                (Sset _j
                  (Ebinop Oadd (Etempvar _j tuint)
                    (Econst_int (Int.repr 2) tint) tuint))))))))))
|}.

Definition f_huf_put_stream := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_o, (tptr (Tstruct ___gp_out_t noattr))) ::
                (_h, (tptr (Tstruct ___gp_huf_t noattr))) ::
                (_lit, (tptr tuchar)) :: (_k, tulong) :: nil);
  fn_vars := ((_b, (Tstruct ___gp_bits_t noattr)) :: nil);
  fn_temps := ((_i, tulong) :: (_x_valid_dict_api__t'6, tuchar) :: (_x_valid_dict_api__t'5, tuchar) ::
               (_x_valid_dict_api__t'4, tuchar) :: (_x_valid_dict_api__t'3, tuchar) :: (_x_valid_dict_api__t'2, tushort) ::
               (_x_valid_dict_api__t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Sassign
    (Efield (Evar _b (Tstruct ___gp_bits_t noattr)) _o
      (tptr (Tstruct ___gp_out_t noattr)))
    (Etempvar _o (tptr (Tstruct ___gp_out_t noattr))))
  (Ssequence
    (Sassign (Efield (Evar _b (Tstruct ___gp_bits_t noattr)) _acc tulong)
      (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Sassign (Efield (Evar _b (Tstruct ___gp_bits_t noattr)) _bits tuint)
        (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Sset _i (Etempvar _k tulong))
        (Ssequence
          (Swhile
            (Ebinop Ogt (Etempvar _i tulong) (Econst_int (Int.repr 0) tint)
              tint)
            (Ssequence
              (Sset _i
                (Ebinop Osub (Etempvar _i tulong)
                  (Econst_int (Int.repr 1) tint) tulong))
              (Ssequence
                (Ssequence
                  (Sset _x_valid_dict_api__t'5
                    (Ederef
                      (Ebinop Oadd (Etempvar _lit (tptr tuchar))
                        (Etempvar _i tulong) (tptr tuchar)) tuchar))
                  (Ssequence
                    (Sset _x_valid_dict_api__t'6
                      (Ederef
                        (Ebinop Oadd
                          (Efield
                            (Ederef
                              (Etempvar _h (tptr (Tstruct ___gp_huf_t noattr)))
                              (Tstruct ___gp_huf_t noattr)) _w
                            (tarray tuchar 256)) (Etempvar _x_valid_dict_api__t'5 tuchar)
                          (tptr tuchar)) tuchar))
                    (Scall None
                      (Evar _gp_assert (Tfunction (tint :: nil) tvoid
                                         cc_default))
                      ((Ebinop One (Etempvar _x_valid_dict_api__t'6 tuchar)
                         (Econst_int (Int.repr 0) tint) tint) :: nil))))
                (Ssequence
                  (Sset _x_valid_dict_api__t'1
                    (Ederef
                      (Ebinop Oadd (Etempvar _lit (tptr tuchar))
                        (Etempvar _i tulong) (tptr tuchar)) tuchar))
                  (Ssequence
                    (Sset _x_valid_dict_api__t'2
                      (Ederef
                        (Ebinop Oadd
                          (Efield
                            (Ederef
                              (Etempvar _h (tptr (Tstruct ___gp_huf_t noattr)))
                              (Tstruct ___gp_huf_t noattr)) _code
                            (tarray tushort 256)) (Etempvar _x_valid_dict_api__t'1 tuchar)
                          (tptr tushort)) tushort))
                    (Ssequence
                      (Sset _x_valid_dict_api__t'3
                        (Ederef
                          (Ebinop Oadd (Etempvar _lit (tptr tuchar))
                            (Etempvar _i tulong) (tptr tuchar)) tuchar))
                      (Ssequence
                        (Sset _x_valid_dict_api__t'4
                          (Ederef
                            (Ebinop Oadd
                              (Efield
                                (Ederef
                                  (Etempvar _h (tptr (Tstruct ___gp_huf_t noattr)))
                                  (Tstruct ___gp_huf_t noattr)) _nb
                                (tarray tuchar 256)) (Etempvar _x_valid_dict_api__t'3 tuchar)
                              (tptr tuchar)) tuchar))
                        (Scall None
                          (Evar _bits_put (Tfunction
                                            ((tptr (Tstruct ___gp_bits_t noattr)) ::
                                             tulong :: tuint :: nil) tvoid
                                            cc_default))
                          ((Eaddrof (Evar _b (Tstruct ___gp_bits_t noattr))
                             (tptr (Tstruct ___gp_bits_t noattr))) ::
                           (Etempvar _x_valid_dict_api__t'2 tushort) ::
                           (Etempvar _x_valid_dict_api__t'4 tuchar) :: nil)))))))))
          (Scall None
            (Evar _bits_end_mark (Tfunction
                                   ((tptr (Tstruct ___gp_bits_t noattr)) ::
                                    nil) tvoid cc_default))
            ((Eaddrof (Evar _b (Tstruct ___gp_bits_t noattr))
               (tptr (Tstruct ___gp_bits_t noattr))) :: nil)))))))
|}.

Definition f_put_literals_raw_rle := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_o, (tptr (Tstruct ___gp_out_t noattr))) ::
                (_type, tuint) :: (_lit, (tptr tuchar)) :: (_k, tulong) ::
                nil);
  fn_vars := ((_forms, (tarray tuint 3)) :: nil);
  fn_temps := ((_nforms, tuint) :: (_f, tuint) :: (_x_valid_dict_api__t'6, tuint) ::
               (_x_valid_dict_api__t'5, tuint) :: (_x_valid_dict_api__t'4, tuint) :: (_x_valid_dict_api__t'3, tuint) ::
               (_x_valid_dict_api__t'2, tuint) :: (_x_valid_dict_api__t'1, tuint) :: (_x_valid_dict_api__t'7, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Sset _nforms (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Sifthenelse (Ebinop Ole (Etempvar _k tulong)
                   (Econst_int (Int.repr 31) tint) tint)
      (Ssequence
        (Ssequence
          (Sset _x_valid_dict_api__t'1 (Etempvar _nforms tuint))
          (Sset _nforms
            (Ebinop Oadd (Etempvar _x_valid_dict_api__t'1 tuint) (Econst_int (Int.repr 1) tint)
              tuint)))
        (Sassign
          (Ederef
            (Ebinop Oadd (Evar _forms (tarray tuint 3)) (Etempvar _x_valid_dict_api__t'1 tuint)
              (tptr tuint)) tuint) (Econst_int (Int.repr 0) tint)))
      Sskip)
    (Ssequence
      (Sifthenelse (Ebinop Ole (Etempvar _k tulong)
                     (Econst_int (Int.repr 4095) tint) tint)
        (Ssequence
          (Ssequence
            (Sset _x_valid_dict_api__t'2 (Etempvar _nforms tuint))
            (Sset _nforms
              (Ebinop Oadd (Etempvar _x_valid_dict_api__t'2 tuint)
                (Econst_int (Int.repr 1) tint) tuint)))
          (Sassign
            (Ederef
              (Ebinop Oadd (Evar _forms (tarray tuint 3))
                (Etempvar _x_valid_dict_api__t'2 tuint) (tptr tuint)) tuint)
            (Econst_int (Int.repr 1) tint)))
        Sskip)
      (Ssequence
        (Sifthenelse (Ebinop Ole (Etempvar _k tulong)
                       (Econst_int (Int.repr 1048575) tint) tint)
          (Ssequence
            (Ssequence
              (Sset _x_valid_dict_api__t'3 (Etempvar _nforms tuint))
              (Sset _nforms
                (Ebinop Oadd (Etempvar _x_valid_dict_api__t'3 tuint)
                  (Econst_int (Int.repr 1) tint) tuint)))
            (Sassign
              (Ederef
                (Ebinop Oadd (Evar _forms (tarray tuint 3))
                  (Etempvar _x_valid_dict_api__t'3 tuint) (tptr tuint)) tuint)
              (Econst_int (Int.repr 2) tint)))
          Sskip)
        (Ssequence
          (Scall None
            (Evar _gp_assert (Tfunction (tint :: nil) tvoid cc_default))
            ((Ebinop Ogt (Etempvar _nforms tuint)
               (Econst_int (Int.repr 0) tint) tint) :: nil))
          (Ssequence
            (Ssequence
              (Scall (Some _x_valid_dict_api__t'4)
                (Evar _choose (Tfunction (tuint :: nil) tuint cc_default))
                ((Etempvar _nforms tuint) :: nil))
              (Sset _f
                (Ederef
                  (Ebinop Oadd (Evar _forms (tarray tuint 3))
                    (Etempvar _x_valid_dict_api__t'4 tuint) (tptr tuint)) tuint)))
            (Ssequence
              (Sifthenelse (Ebinop Oeq (Etempvar _f tuint)
                             (Econst_int (Int.repr 0) tint) tint)
                (Scall None
                  (Evar _put8 (Tfunction
                                ((tptr (Tstruct ___gp_out_t noattr)) ::
                                 tuint :: nil) tvoid cc_default))
                  ((Etempvar _o (tptr (Tstruct ___gp_out_t noattr))) ::
                   (Ebinop Oor (Etempvar _type tuint)
                     (Ecast
                       (Ebinop Oshl (Etempvar _k tulong)
                         (Econst_int (Int.repr 3) tint) tulong) tuint) tuint) ::
                   nil))
                (Sifthenelse (Ebinop Oeq (Etempvar _f tuint)
                               (Econst_int (Int.repr 1) tint) tint)
                  (Scall None
                    (Evar _put_le (Tfunction
                                    ((tptr (Tstruct ___gp_out_t noattr)) ::
                                     tulong :: tuint :: nil) tvoid
                                    cc_default))
                    ((Etempvar _o (tptr (Tstruct ___gp_out_t noattr))) ::
                     (Ebinop Oor
                       (Ebinop Oor (Etempvar _type tuint)
                         (Ebinop Oshl (Econst_int (Int.repr 1) tuint)
                           (Econst_int (Int.repr 2) tint) tuint) tuint)
                       (Ebinop Oshl (Ecast (Etempvar _k tulong) tulong)
                         (Econst_int (Int.repr 4) tint) tulong) tulong) ::
                     (Econst_int (Int.repr 2) tint) :: nil))
                  (Scall None
                    (Evar _put_le (Tfunction
                                    ((tptr (Tstruct ___gp_out_t noattr)) ::
                                     tulong :: tuint :: nil) tvoid
                                    cc_default))
                    ((Etempvar _o (tptr (Tstruct ___gp_out_t noattr))) ::
                     (Ebinop Oor
                       (Ebinop Oor (Etempvar _type tuint)
                         (Ebinop Oshl (Econst_int (Int.repr 3) tuint)
                           (Econst_int (Int.repr 2) tint) tuint) tuint)
                       (Ebinop Oshl (Ecast (Etempvar _k tulong) tulong)
                         (Econst_int (Int.repr 4) tint) tulong) tulong) ::
                     (Econst_int (Int.repr 3) tint) :: nil))))
              (Sifthenelse (Ebinop Oeq (Etempvar _type tuint)
                             (Econst_int (Int.repr 0) tint) tint)
                (Scall None
                  (Evar _put_bytes (Tfunction
                                     ((tptr (Tstruct ___gp_out_t noattr)) ::
                                      (tptr tuchar) :: tulong :: nil) tvoid
                                     cc_default))
                  ((Etempvar _o (tptr (Tstruct ___gp_out_t noattr))) ::
                   (Etempvar _lit (tptr tuchar)) :: (Etempvar _k tulong) ::
                   nil))
                (Ssequence
                  (Sifthenelse (Ebinop Ogt (Etempvar _k tulong)
                                 (Econst_int (Int.repr 0) tint) tint)
                    (Ssequence
                      (Sset _x_valid_dict_api__t'7
                        (Ederef
                          (Ebinop Oadd (Etempvar _lit (tptr tuchar))
                            (Econst_int (Int.repr 0) tint) (tptr tuchar))
                          tuchar))
                      (Sset _x_valid_dict_api__t'5 (Ecast (Etempvar _x_valid_dict_api__t'7 tuchar) tuint)))
                    (Ssequence
                      (Scall (Some _x_valid_dict_api__t'6)
                        (Evar _choose (Tfunction (tuint :: nil) tuint
                                        cc_default))
                        ((Econst_int (Int.repr 256) tint) :: nil))
                      (Sset _x_valid_dict_api__t'5 (Ecast (Etempvar _x_valid_dict_api__t'6 tuint) tuint))))
                  (Scall None
                    (Evar _put8 (Tfunction
                                  ((tptr (Tstruct ___gp_out_t noattr)) ::
                                   tuint :: nil) tvoid cc_default))
                    ((Etempvar _o (tptr (Tstruct ___gp_out_t noattr))) ::
                     (Etempvar _x_valid_dict_api__t'5 tuint) :: nil)))))))))))
|}.

Definition v_x_valid_dict_api__tmp__1 := {|
  gvar_info := (tarray tuchar 262144);
  gvar_init := (Init_space 262144 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_put_literals_huf := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_o, (tptr (Tstruct ___gp_out_t noattr))) ::
                (_type, tuint) ::
                (_h, (tptr (Tstruct ___gp_huf_t noattr))) ::
                (_lit, (tptr tuchar)) :: (_k, tulong) :: nil);
  fn_vars := ((_body, (Tstruct ___gp_out_t noattr)) ::
              (_forms, (tarray tuint 3)) :: nil);
  fn_temps := ((_can4, tuint) :: (_streams4, tuint) :: (_nforms, tuint) ::
               (_form, tuint) :: (_bitsz, tuint) :: (_c, tulong) ::
               (_seg, tulong) :: (_at, tulong) :: (_s1, tulong) ::
               (_s2, tulong) :: (_s3, tulong) :: (_j, tulong) ::
               (_x_valid_dict_api__t'15, tint) :: (_x_valid_dict_api__t'14, tint) :: (_x_valid_dict_api__t'13, tuint) ::
               (_x_valid_dict_api__t'12, tint) :: (_x_valid_dict_api__t'11, tuint) :: (_x_valid_dict_api__t'10, tint) ::
               (_x_valid_dict_api__t'9, tuint) :: (_x_valid_dict_api__t'8, tint) :: (_x_valid_dict_api__t'7, tuint) ::
               (_x_valid_dict_api__t'6, tuint) :: (_x_valid_dict_api__t'5, tint) :: (_x_valid_dict_api__t'4, tint) ::
               (_x_valid_dict_api__t'3, tint) :: (_x_valid_dict_api__t'2, tuint) :: (_x_valid_dict_api__t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sassign
    (Efield (Evar _body (Tstruct ___gp_out_t noattr)) _p (tptr tuchar))
    (Evar _x_valid_dict_api__tmp__1 (tarray tuchar 262144)))
  (Ssequence
    (Sassign (Efield (Evar _body (Tstruct ___gp_out_t noattr)) _n tulong)
      (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Sassign (Efield (Evar _body (Tstruct ___gp_out_t noattr)) _cap tulong)
        (Esizeof (tarray tuchar 262144) tulong))
      (Ssequence
        (Sset _can4
          (Ebinop Oge (Etempvar _k tulong) (Econst_int (Int.repr 6) tint)
            tint))
        (Ssequence
          (Sset _nforms (Econst_int (Int.repr 0) tint))
          (Ssequence
            (Ssequence
              (Sifthenelse (Eunop Onotbool (Etempvar _can4 tuint) tint)
                (Sset _x_valid_dict_api__t'1 (Ecast (Econst_int (Int.repr 0) tint) tuint))
                (Sifthenelse (Ebinop Ogt (Etempvar _k tulong)
                               (Econst_int (Int.repr 1023) tint) tint)
                  (Ssequence
                    (Sset _x_valid_dict_api__t'1 (Ecast (Econst_int (Int.repr 1) tint) tuint))
                    (Sset _x_valid_dict_api__t'1 (Ecast (Etempvar _x_valid_dict_api__t'1 tuint) tuint)))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _x_valid_dict_api__t'2)
                        (Evar _choose (Tfunction (tuint :: nil) tuint
                                        cc_default))
                        ((Econst_int (Int.repr 2) tint) :: nil))
                      (Sset _x_valid_dict_api__t'1 (Ecast (Etempvar _x_valid_dict_api__t'2 tuint) tuint)))
                    (Sset _x_valid_dict_api__t'1 (Ecast (Etempvar _x_valid_dict_api__t'1 tuint) tuint)))))
              (Sset _streams4 (Etempvar _x_valid_dict_api__t'1 tuint)))
            (Ssequence
              (Sifthenelse (Ebinop Oeq (Etempvar _type tuint)
                             (Econst_int (Int.repr 2) tint) tint)
                (Scall None
                  (Evar _huf_put_description (Tfunction
                                               ((tptr (Tstruct ___gp_out_t noattr)) ::
                                                (tptr (Tstruct ___gp_huf_t noattr)) ::
                                                nil) tvoid cc_default))
                  ((Eaddrof (Evar _body (Tstruct ___gp_out_t noattr))
                     (tptr (Tstruct ___gp_out_t noattr))) ::
                   (Etempvar _h (tptr (Tstruct ___gp_huf_t noattr))) :: nil))
                Sskip)
              (Ssequence
                (Sifthenelse (Eunop Onotbool (Etempvar _streams4 tuint) tint)
                  (Scall None
                    (Evar _huf_put_stream (Tfunction
                                            ((tptr (Tstruct ___gp_out_t noattr)) ::
                                             (tptr (Tstruct ___gp_huf_t noattr)) ::
                                             (tptr tuchar) :: tulong :: nil)
                                            tvoid cc_default))
                    ((Eaddrof (Evar _body (Tstruct ___gp_out_t noattr))
                       (tptr (Tstruct ___gp_out_t noattr))) ::
                     (Etempvar _h (tptr (Tstruct ___gp_huf_t noattr))) ::
                     (Etempvar _lit (tptr tuchar)) :: (Etempvar _k tulong) ::
                     nil))
                  (Ssequence
                    (Sset _seg
                      (Ebinop Odiv
                        (Ebinop Oadd (Etempvar _k tulong)
                          (Econst_int (Int.repr 3) tint) tulong)
                        (Econst_int (Int.repr 4) tint) tulong))
                    (Ssequence
                      (Sset _at
                        (Efield (Evar _body (Tstruct ___gp_out_t noattr)) _n
                          tulong))
                      (Ssequence
                        (Ssequence
                          (Sset _j
                            (Ecast (Econst_int (Int.repr 0) tint) tulong))
                          (Sloop
                            (Ssequence
                              (Sifthenelse (Ebinop Olt (Etempvar _j tulong)
                                             (Econst_int (Int.repr 6) tint)
                                             tint)
                                Sskip
                                Sbreak)
                              (Scall None
                                (Evar _put8 (Tfunction
                                              ((tptr (Tstruct ___gp_out_t noattr)) ::
                                               tuint :: nil) tvoid
                                              cc_default))
                                ((Eaddrof
                                   (Evar _body (Tstruct ___gp_out_t noattr))
                                   (tptr (Tstruct ___gp_out_t noattr))) ::
                                 (Econst_int (Int.repr 0) tint) :: nil)))
                            (Sset _j
                              (Ebinop Oadd (Etempvar _j tulong)
                                (Econst_int (Int.repr 1) tint) tulong))))
                        (Ssequence
                          (Sset _s1
                            (Efield (Evar _body (Tstruct ___gp_out_t noattr))
                              _n tulong))
                          (Ssequence
                            (Scall None
                              (Evar _huf_put_stream (Tfunction
                                                      ((tptr (Tstruct ___gp_out_t noattr)) ::
                                                       (tptr (Tstruct ___gp_huf_t noattr)) ::
                                                       (tptr tuchar) ::
                                                       tulong :: nil) tvoid
                                                      cc_default))
                              ((Eaddrof
                                 (Evar _body (Tstruct ___gp_out_t noattr))
                                 (tptr (Tstruct ___gp_out_t noattr))) ::
                               (Etempvar _h (tptr (Tstruct ___gp_huf_t noattr))) ::
                               (Etempvar _lit (tptr tuchar)) ::
                               (Etempvar _seg tulong) :: nil))
                            (Ssequence
                              (Sset _s2
                                (Efield
                                  (Evar _body (Tstruct ___gp_out_t noattr))
                                  _n tulong))
                              (Ssequence
                                (Scall None
                                  (Evar _huf_put_stream (Tfunction
                                                          ((tptr (Tstruct ___gp_out_t noattr)) ::
                                                           (tptr (Tstruct ___gp_huf_t noattr)) ::
                                                           (tptr tuchar) ::
                                                           tulong :: nil)
                                                          tvoid cc_default))
                                  ((Eaddrof
                                     (Evar _body (Tstruct ___gp_out_t noattr))
                                     (tptr (Tstruct ___gp_out_t noattr))) ::
                                   (Etempvar _h (tptr (Tstruct ___gp_huf_t noattr))) ::
                                   (Ebinop Oadd (Etempvar _lit (tptr tuchar))
                                     (Etempvar _seg tulong) (tptr tuchar)) ::
                                   (Etempvar _seg tulong) :: nil))
                                (Ssequence
                                  (Sset _s3
                                    (Efield
                                      (Evar _body (Tstruct ___gp_out_t noattr))
                                      _n tulong))
                                  (Ssequence
                                    (Scall None
                                      (Evar _huf_put_stream (Tfunction
                                                              ((tptr (Tstruct ___gp_out_t noattr)) ::
                                                               (tptr (Tstruct ___gp_huf_t noattr)) ::
                                                               (tptr tuchar) ::
                                                               tulong :: nil)
                                                              tvoid
                                                              cc_default))
                                      ((Eaddrof
                                         (Evar _body (Tstruct ___gp_out_t noattr))
                                         (tptr (Tstruct ___gp_out_t noattr))) ::
                                       (Etempvar _h (tptr (Tstruct ___gp_huf_t noattr))) ::
                                       (Ebinop Oadd
                                         (Etempvar _lit (tptr tuchar))
                                         (Ebinop Omul
                                           (Econst_int (Int.repr 2) tint)
                                           (Etempvar _seg tulong) tulong)
                                         (tptr tuchar)) ::
                                       (Etempvar _seg tulong) :: nil))
                                    (Ssequence
                                      (Sset _c
                                        (Efield
                                          (Evar _body (Tstruct ___gp_out_t noattr))
                                          _n tulong))
                                      (Ssequence
                                        (Scall None
                                          (Evar _huf_put_stream (Tfunction
                                                                  ((tptr (Tstruct ___gp_out_t noattr)) ::
                                                                   (tptr (Tstruct ___gp_huf_t noattr)) ::
                                                                   (tptr tuchar) ::
                                                                   tulong ::
                                                                   nil) tvoid
                                                                  cc_default))
                                          ((Eaddrof
                                             (Evar _body (Tstruct ___gp_out_t noattr))
                                             (tptr (Tstruct ___gp_out_t noattr))) ::
                                           (Etempvar _h (tptr (Tstruct ___gp_huf_t noattr))) ::
                                           (Ebinop Oadd
                                             (Etempvar _lit (tptr tuchar))
                                             (Ebinop Omul
                                               (Econst_int (Int.repr 3) tint)
                                               (Etempvar _seg tulong) tulong)
                                             (tptr tuchar)) ::
                                           (Ebinop Osub (Etempvar _k tulong)
                                             (Ebinop Omul
                                               (Econst_int (Int.repr 3) tint)
                                               (Etempvar _seg tulong) tulong)
                                             tulong) :: nil))
                                        (Ssequence
                                          (Ssequence
                                            (Ssequence
                                              (Sifthenelse (Ebinop Ole
                                                             (Ebinop Osub
                                                               (Etempvar _s2 tulong)
                                                               (Etempvar _s1 tulong)
                                                               tulong)
                                                             (Econst_int (Int.repr 65535) tint)
                                                             tint)
                                                (Sset _x_valid_dict_api__t'3
                                                  (Ecast
                                                    (Ebinop Ole
                                                      (Ebinop Osub
                                                        (Etempvar _s3 tulong)
                                                        (Etempvar _s2 tulong)
                                                        tulong)
                                                      (Econst_int (Int.repr 65535) tint)
                                                      tint) tbool))
                                                (Sset _x_valid_dict_api__t'3
                                                  (Econst_int (Int.repr 0) tint)))
                                              (Sifthenelse (Etempvar _x_valid_dict_api__t'3 tint)
                                                (Sset _x_valid_dict_api__t'4
                                                  (Ecast
                                                    (Ebinop Ole
                                                      (Ebinop Osub
                                                        (Etempvar _c tulong)
                                                        (Etempvar _s3 tulong)
                                                        tulong)
                                                      (Econst_int (Int.repr 65535) tint)
                                                      tint) tbool))
                                                (Sset _x_valid_dict_api__t'4
                                                  (Econst_int (Int.repr 0) tint))))
                                            (Scall None
                                              (Evar _gp_assume (Tfunction
                                                                 (tint ::
                                                                  nil) tvoid
                                                                 cc_default))
                                              ((Etempvar _x_valid_dict_api__t'4 tint) :: nil)))
                                          (Ssequence
                                            (Sassign
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Evar _x_valid_dict_api__tmp__1 (tarray tuchar 262144))
                                                  (Ebinop Oadd
                                                    (Etempvar _at tulong)
                                                    (Econst_int (Int.repr 0) tint)
                                                    tulong) (tptr tuchar))
                                                tuchar)
                                              (Ecast
                                                (Ebinop Oand
                                                  (Ebinop Osub
                                                    (Etempvar _s2 tulong)
                                                    (Etempvar _s1 tulong)
                                                    tulong)
                                                  (Econst_int (Int.repr 255) tint)
                                                  tulong) tuchar))
                                            (Ssequence
                                              (Sassign
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Evar _x_valid_dict_api__tmp__1 (tarray tuchar 262144))
                                                    (Ebinop Oadd
                                                      (Etempvar _at tulong)
                                                      (Econst_int (Int.repr 1) tint)
                                                      tulong) (tptr tuchar))
                                                  tuchar)
                                                (Ecast
                                                  (Ebinop Oshr
                                                    (Ebinop Osub
                                                      (Etempvar _s2 tulong)
                                                      (Etempvar _s1 tulong)
                                                      tulong)
                                                    (Econst_int (Int.repr 8) tint)
                                                    tulong) tuchar))
                                              (Ssequence
                                                (Sassign
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Evar _x_valid_dict_api__tmp__1 (tarray tuchar 262144))
                                                      (Ebinop Oadd
                                                        (Etempvar _at tulong)
                                                        (Econst_int (Int.repr 2) tint)
                                                        tulong)
                                                      (tptr tuchar)) tuchar)
                                                  (Ecast
                                                    (Ebinop Oand
                                                      (Ebinop Osub
                                                        (Etempvar _s3 tulong)
                                                        (Etempvar _s2 tulong)
                                                        tulong)
                                                      (Econst_int (Int.repr 255) tint)
                                                      tulong) tuchar))
                                                (Ssequence
                                                  (Sassign
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Evar _x_valid_dict_api__tmp__1 (tarray tuchar 262144))
                                                        (Ebinop Oadd
                                                          (Etempvar _at tulong)
                                                          (Econst_int (Int.repr 3) tint)
                                                          tulong)
                                                        (tptr tuchar))
                                                      tuchar)
                                                    (Ecast
                                                      (Ebinop Oshr
                                                        (Ebinop Osub
                                                          (Etempvar _s3 tulong)
                                                          (Etempvar _s2 tulong)
                                                          tulong)
                                                        (Econst_int (Int.repr 8) tint)
                                                        tulong) tuchar))
                                                  (Ssequence
                                                    (Sassign
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _x_valid_dict_api__tmp__1 (tarray tuchar 262144))
                                                          (Ebinop Oadd
                                                            (Etempvar _at tulong)
                                                            (Econst_int (Int.repr 4) tint)
                                                            tulong)
                                                          (tptr tuchar))
                                                        tuchar)
                                                      (Ecast
                                                        (Ebinop Oand
                                                          (Ebinop Osub
                                                            (Etempvar _c tulong)
                                                            (Etempvar _s3 tulong)
                                                            tulong)
                                                          (Econst_int (Int.repr 255) tint)
                                                          tulong) tuchar))
                                                    (Sassign
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _x_valid_dict_api__tmp__1 (tarray tuchar 262144))
                                                          (Ebinop Oadd
                                                            (Etempvar _at tulong)
                                                            (Econst_int (Int.repr 5) tint)
                                                            tulong)
                                                          (tptr tuchar))
                                                        tuchar)
                                                      (Ecast
                                                        (Ebinop Oshr
                                                          (Ebinop Osub
                                                            (Etempvar _c tulong)
                                                            (Etempvar _s3 tulong)
                                                            tulong)
                                                          (Econst_int (Int.repr 8) tint)
                                                          tulong) tuchar))))))))))))))))))))
                (Ssequence
                  (Sset _c
                    (Efield (Evar _body (Tstruct ___gp_out_t noattr)) _n
                      tulong))
                  (Ssequence
                    (Sifthenelse (Eunop Onotbool (Etempvar _streams4 tuint)
                                   tint)
                      (Ssequence
                        (Ssequence
                          (Sifthenelse (Ebinop Ole (Etempvar _k tulong)
                                         (Econst_int (Int.repr 1023) tint)
                                         tint)
                            (Sset _x_valid_dict_api__t'5
                              (Ecast
                                (Ebinop Ole (Etempvar _c tulong)
                                  (Econst_int (Int.repr 1023) tint) tint)
                                tbool))
                            (Sset _x_valid_dict_api__t'5 (Econst_int (Int.repr 0) tint)))
                          (Scall None
                            (Evar _gp_assume (Tfunction (tint :: nil) tvoid
                                               cc_default))
                            ((Etempvar _x_valid_dict_api__t'5 tint) :: nil)))
                        (Ssequence
                          (Ssequence
                            (Sset _x_valid_dict_api__t'6 (Etempvar _nforms tuint))
                            (Sset _nforms
                              (Ebinop Oadd (Etempvar _x_valid_dict_api__t'6 tuint)
                                (Econst_int (Int.repr 1) tint) tuint)))
                          (Sassign
                            (Ederef
                              (Ebinop Oadd (Evar _forms (tarray tuint 3))
                                (Etempvar _x_valid_dict_api__t'6 tuint) (tptr tuint)) tuint)
                            (Econst_int (Int.repr 0) tint))))
                      (Ssequence
                        (Ssequence
                          (Sifthenelse (Ebinop Ole (Etempvar _k tulong)
                                         (Econst_int (Int.repr 1023) tint)
                                         tint)
                            (Sset _x_valid_dict_api__t'8
                              (Ecast
                                (Ebinop Ole (Etempvar _c tulong)
                                  (Econst_int (Int.repr 1023) tint) tint)
                                tbool))
                            (Sset _x_valid_dict_api__t'8 (Econst_int (Int.repr 0) tint)))
                          (Sifthenelse (Etempvar _x_valid_dict_api__t'8 tint)
                            (Ssequence
                              (Ssequence
                                (Sset _x_valid_dict_api__t'7 (Etempvar _nforms tuint))
                                (Sset _nforms
                                  (Ebinop Oadd (Etempvar _x_valid_dict_api__t'7 tuint)
                                    (Econst_int (Int.repr 1) tint) tuint)))
                              (Sassign
                                (Ederef
                                  (Ebinop Oadd (Evar _forms (tarray tuint 3))
                                    (Etempvar _x_valid_dict_api__t'7 tuint) (tptr tuint))
                                  tuint) (Econst_int (Int.repr 1) tint)))
                            Sskip))
                        (Ssequence
                          (Ssequence
                            (Sifthenelse (Ebinop Ole (Etempvar _k tulong)
                                           (Econst_int (Int.repr 16383) tint)
                                           tint)
                              (Sset _x_valid_dict_api__t'10
                                (Ecast
                                  (Ebinop Ole (Etempvar _c tulong)
                                    (Econst_int (Int.repr 16383) tint) tint)
                                  tbool))
                              (Sset _x_valid_dict_api__t'10 (Econst_int (Int.repr 0) tint)))
                            (Sifthenelse (Etempvar _x_valid_dict_api__t'10 tint)
                              (Ssequence
                                (Ssequence
                                  (Sset _x_valid_dict_api__t'9 (Etempvar _nforms tuint))
                                  (Sset _nforms
                                    (Ebinop Oadd (Etempvar _x_valid_dict_api__t'9 tuint)
                                      (Econst_int (Int.repr 1) tint) tuint)))
                                (Sassign
                                  (Ederef
                                    (Ebinop Oadd
                                      (Evar _forms (tarray tuint 3))
                                      (Etempvar _x_valid_dict_api__t'9 tuint) (tptr tuint))
                                    tuint) (Econst_int (Int.repr 2) tint)))
                              Sskip))
                          (Ssequence
                            (Ssequence
                              (Sifthenelse (Ebinop Ole (Etempvar _k tulong)
                                             (Econst_int (Int.repr 262143) tint)
                                             tint)
                                (Sset _x_valid_dict_api__t'12
                                  (Ecast
                                    (Ebinop Ole (Etempvar _c tulong)
                                      (Econst_int (Int.repr 262143) tint)
                                      tint) tbool))
                                (Sset _x_valid_dict_api__t'12 (Econst_int (Int.repr 0) tint)))
                              (Sifthenelse (Etempvar _x_valid_dict_api__t'12 tint)
                                (Ssequence
                                  (Ssequence
                                    (Sset _x_valid_dict_api__t'11 (Etempvar _nforms tuint))
                                    (Sset _nforms
                                      (Ebinop Oadd (Etempvar _x_valid_dict_api__t'11 tuint)
                                        (Econst_int (Int.repr 1) tint) tuint)))
                                  (Sassign
                                    (Ederef
                                      (Ebinop Oadd
                                        (Evar _forms (tarray tuint 3))
                                        (Etempvar _x_valid_dict_api__t'11 tuint) (tptr tuint))
                                      tuint) (Econst_int (Int.repr 3) tint)))
                                Sskip))
                            (Scall None
                              (Evar _gp_assume (Tfunction (tint :: nil) tvoid
                                                 cc_default))
                              ((Ebinop Ogt (Etempvar _nforms tuint)
                                 (Econst_int (Int.repr 0) tint) tint) :: nil))))))
                    (Ssequence
                      (Ssequence
                        (Scall (Some _x_valid_dict_api__t'13)
                          (Evar _choose (Tfunction (tuint :: nil) tuint
                                          cc_default))
                          ((Etempvar _nforms tuint) :: nil))
                        (Sset _form
                          (Ederef
                            (Ebinop Oadd (Evar _forms (tarray tuint 3))
                              (Etempvar _x_valid_dict_api__t'13 tuint) (tptr tuint)) tuint)))
                      (Ssequence
                        (Ssequence
                          (Sifthenelse (Ebinop Ole (Etempvar _form tuint)
                                         (Econst_int (Int.repr 1) tint) tint)
                            (Sset _x_valid_dict_api__t'14
                              (Ecast (Econst_int (Int.repr 10) tint) tint))
                            (Sifthenelse (Ebinop Oeq (Etempvar _form tuint)
                                           (Econst_int (Int.repr 2) tint)
                                           tint)
                              (Ssequence
                                (Sset _x_valid_dict_api__t'14
                                  (Ecast (Econst_int (Int.repr 14) tint)
                                    tint))
                                (Sset _x_valid_dict_api__t'14
                                  (Ecast (Etempvar _x_valid_dict_api__t'14 tint) tint)))
                              (Ssequence
                                (Sset _x_valid_dict_api__t'14
                                  (Ecast (Econst_int (Int.repr 18) tint)
                                    tint))
                                (Sset _x_valid_dict_api__t'14
                                  (Ecast (Etempvar _x_valid_dict_api__t'14 tint) tint)))))
                          (Sset _bitsz (Etempvar _x_valid_dict_api__t'14 tint)))
                        (Ssequence
                          (Ssequence
                            (Sifthenelse (Ebinop Ole (Etempvar _form tuint)
                                           (Econst_int (Int.repr 1) tint)
                                           tint)
                              (Sset _x_valid_dict_api__t'15
                                (Ecast (Econst_int (Int.repr 3) tint) tint))
                              (Sifthenelse (Ebinop Oeq (Etempvar _form tuint)
                                             (Econst_int (Int.repr 2) tint)
                                             tint)
                                (Ssequence
                                  (Sset _x_valid_dict_api__t'15
                                    (Ecast (Econst_int (Int.repr 4) tint)
                                      tint))
                                  (Sset _x_valid_dict_api__t'15
                                    (Ecast (Etempvar _x_valid_dict_api__t'15 tint) tint)))
                                (Ssequence
                                  (Sset _x_valid_dict_api__t'15
                                    (Ecast (Econst_int (Int.repr 5) tint)
                                      tint))
                                  (Sset _x_valid_dict_api__t'15
                                    (Ecast (Etempvar _x_valid_dict_api__t'15 tint) tint)))))
                            (Scall None
                              (Evar _put_le (Tfunction
                                              ((tptr (Tstruct ___gp_out_t noattr)) ::
                                               tulong :: tuint :: nil) tvoid
                                              cc_default))
                              ((Etempvar _o (tptr (Tstruct ___gp_out_t noattr))) ::
                               (Ebinop Oor
                                 (Ebinop Oor
                                   (Ebinop Oor (Etempvar _type tuint)
                                     (Ebinop Oshl (Etempvar _form tuint)
                                       (Econst_int (Int.repr 2) tint) tuint)
                                     tuint)
                                   (Ebinop Oshl
                                     (Ecast (Etempvar _k tulong) tulong)
                                     (Econst_int (Int.repr 4) tint) tulong)
                                   tulong)
                                 (Ebinop Oshl
                                   (Ecast (Etempvar _c tulong) tulong)
                                   (Ebinop Oadd
                                     (Econst_int (Int.repr 4) tint)
                                     (Etempvar _bitsz tuint) tuint) tulong)
                                 tulong) :: (Etempvar _x_valid_dict_api__t'15 tint) :: nil)))
                          (Scall None
                            (Evar _put_bytes (Tfunction
                                               ((tptr (Tstruct ___gp_out_t noattr)) ::
                                                (tptr tuchar) :: tulong ::
                                                nil) tvoid cc_default))
                            ((Etempvar _o (tptr (Tstruct ___gp_out_t noattr))) ::
                             (Evar _x_valid_dict_api__tmp__1 (tarray tuchar 262144)) ::
                             (Etempvar _c tulong) :: nil)))))))))))))))
|}.

Definition v_x_valid_dict_api__W_LL_base := {|
  gvar_info := (tarray tuint 36);
  gvar_init := (Init_int32 (Int.repr 0) :: Init_int32 (Int.repr 1) ::
                Init_int32 (Int.repr 2) :: Init_int32 (Int.repr 3) ::
                Init_int32 (Int.repr 4) :: Init_int32 (Int.repr 5) ::
                Init_int32 (Int.repr 6) :: Init_int32 (Int.repr 7) ::
                Init_int32 (Int.repr 8) :: Init_int32 (Int.repr 9) ::
                Init_int32 (Int.repr 10) :: Init_int32 (Int.repr 11) ::
                Init_int32 (Int.repr 12) :: Init_int32 (Int.repr 13) ::
                Init_int32 (Int.repr 14) :: Init_int32 (Int.repr 15) ::
                Init_int32 (Int.repr 16) :: Init_int32 (Int.repr 18) ::
                Init_int32 (Int.repr 20) :: Init_int32 (Int.repr 22) ::
                Init_int32 (Int.repr 24) :: Init_int32 (Int.repr 28) ::
                Init_int32 (Int.repr 32) :: Init_int32 (Int.repr 40) ::
                Init_int32 (Int.repr 48) :: Init_int32 (Int.repr 64) ::
                Init_int32 (Int.repr 128) :: Init_int32 (Int.repr 256) ::
                Init_int32 (Int.repr 512) :: Init_int32 (Int.repr 1024) ::
                Init_int32 (Int.repr 2048) :: Init_int32 (Int.repr 4096) ::
                Init_int32 (Int.repr 8192) :: Init_int32 (Int.repr 16384) ::
                Init_int32 (Int.repr 32768) :: Init_int32 (Int.repr 65536) ::
                nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_x_valid_dict_api__W_LL_bits := {|
  gvar_info := (tarray tuchar 36);
  gvar_init := (Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 1) :: Init_int8 (Int.repr 1) ::
                Init_int8 (Int.repr 1) :: Init_int8 (Int.repr 1) ::
                Init_int8 (Int.repr 2) :: Init_int8 (Int.repr 2) ::
                Init_int8 (Int.repr 3) :: Init_int8 (Int.repr 3) ::
                Init_int8 (Int.repr 4) :: Init_int8 (Int.repr 6) ::
                Init_int8 (Int.repr 7) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 9) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 11) :: Init_int8 (Int.repr 12) ::
                Init_int8 (Int.repr 13) :: Init_int8 (Int.repr 14) ::
                Init_int8 (Int.repr 15) :: Init_int8 (Int.repr 16) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_x_valid_dict_api__W_ML_base := {|
  gvar_info := (tarray tuint 53);
  gvar_init := (Init_int32 (Int.repr 3) :: Init_int32 (Int.repr 4) ::
                Init_int32 (Int.repr 5) :: Init_int32 (Int.repr 6) ::
                Init_int32 (Int.repr 7) :: Init_int32 (Int.repr 8) ::
                Init_int32 (Int.repr 9) :: Init_int32 (Int.repr 10) ::
                Init_int32 (Int.repr 11) :: Init_int32 (Int.repr 12) ::
                Init_int32 (Int.repr 13) :: Init_int32 (Int.repr 14) ::
                Init_int32 (Int.repr 15) :: Init_int32 (Int.repr 16) ::
                Init_int32 (Int.repr 17) :: Init_int32 (Int.repr 18) ::
                Init_int32 (Int.repr 19) :: Init_int32 (Int.repr 20) ::
                Init_int32 (Int.repr 21) :: Init_int32 (Int.repr 22) ::
                Init_int32 (Int.repr 23) :: Init_int32 (Int.repr 24) ::
                Init_int32 (Int.repr 25) :: Init_int32 (Int.repr 26) ::
                Init_int32 (Int.repr 27) :: Init_int32 (Int.repr 28) ::
                Init_int32 (Int.repr 29) :: Init_int32 (Int.repr 30) ::
                Init_int32 (Int.repr 31) :: Init_int32 (Int.repr 32) ::
                Init_int32 (Int.repr 33) :: Init_int32 (Int.repr 34) ::
                Init_int32 (Int.repr 35) :: Init_int32 (Int.repr 37) ::
                Init_int32 (Int.repr 39) :: Init_int32 (Int.repr 41) ::
                Init_int32 (Int.repr 43) :: Init_int32 (Int.repr 47) ::
                Init_int32 (Int.repr 51) :: Init_int32 (Int.repr 59) ::
                Init_int32 (Int.repr 67) :: Init_int32 (Int.repr 83) ::
                Init_int32 (Int.repr 99) :: Init_int32 (Int.repr 131) ::
                Init_int32 (Int.repr 259) :: Init_int32 (Int.repr 515) ::
                Init_int32 (Int.repr 1027) :: Init_int32 (Int.repr 2051) ::
                Init_int32 (Int.repr 4099) :: Init_int32 (Int.repr 8195) ::
                Init_int32 (Int.repr 16387) :: Init_int32 (Int.repr 32771) ::
                Init_int32 (Int.repr 65539) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_x_valid_dict_api__W_ML_bits := {|
  gvar_info := (tarray tuchar 53);
  gvar_init := (Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 1) :: Init_int8 (Int.repr 1) ::
                Init_int8 (Int.repr 1) :: Init_int8 (Int.repr 1) ::
                Init_int8 (Int.repr 2) :: Init_int8 (Int.repr 2) ::
                Init_int8 (Int.repr 3) :: Init_int8 (Int.repr 3) ::
                Init_int8 (Int.repr 4) :: Init_int8 (Int.repr 4) ::
                Init_int8 (Int.repr 5) :: Init_int8 (Int.repr 7) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 9) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 11) ::
                Init_int8 (Int.repr 12) :: Init_int8 (Int.repr 13) ::
                Init_int8 (Int.repr 14) :: Init_int8 (Int.repr 15) ::
                Init_int8 (Int.repr 16) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_ll_code := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_ll, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_c, tuint) :: (_x_valid_dict_api__t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _c (Econst_int (Int.repr 35) tint))
  (Ssequence
    (Sloop
      (Ssequence
        (Ssequence
          (Sset _x_valid_dict_api__t'1
            (Ederef
              (Ebinop Oadd (Evar _x_valid_dict_api__W_LL_base (tarray tuint 36))
                (Etempvar _c tuint) (tptr tuint)) tuint))
          (Sifthenelse (Ebinop Ogt (Etempvar _x_valid_dict_api__t'1 tuint)
                         (Etempvar _ll tulong) tint)
            Sskip
            Sbreak))
        (Sset _c
          (Ebinop Osub (Etempvar _c tuint) (Econst_int (Int.repr 1) tint)
            tuint)))
      Sskip)
    (Sreturn (Some (Etempvar _c tuint)))))
|}.

Definition f_ml_code := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_ml, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_c, tuint) :: (_x_valid_dict_api__t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _c (Econst_int (Int.repr 52) tint))
  (Ssequence
    (Sloop
      (Ssequence
        (Ssequence
          (Sset _x_valid_dict_api__t'1
            (Ederef
              (Ebinop Oadd (Evar _x_valid_dict_api__W_ML_base (tarray tuint 53))
                (Etempvar _c tuint) (tptr tuint)) tuint))
          (Sifthenelse (Ebinop Ogt (Etempvar _x_valid_dict_api__t'1 tuint)
                         (Etempvar _ml tulong) tint)
            Sskip
            Sbreak))
        (Sset _c
          (Ebinop Osub (Etempvar _c tuint) (Econst_int (Int.repr 1) tint)
            tuint)))
      Sskip)
    (Sreturn (Some (Etempvar _c tuint)))))
|}.

Definition f_fse_copy := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_d, (tptr (Tstruct ___gp_fse_t noattr))) ::
                (_s, (tptr (Tstruct ___gp_fse_t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tuint) :: (_x_valid_dict_api__t'6, tshort) :: (_x_valid_dict_api__t'5, tuint) ::
               (_x_valid_dict_api__t'4, tuint) :: (_x_valid_dict_api__t'3, tuchar) :: (_x_valid_dict_api__t'2, tuchar) ::
               (_x_valid_dict_api__t'1, tushort) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _i (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                       (Econst_int (Int.repr 53) tint) tint)
          Sskip
          Sbreak)
        (Ssequence
          (Sset _x_valid_dict_api__t'6
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct ___gp_fse_t noattr)))
                    (Tstruct ___gp_fse_t noattr)) _norm (tarray tshort 53))
                (Etempvar _i tuint) (tptr tshort)) tshort))
          (Sassign
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef (Etempvar _d (tptr (Tstruct ___gp_fse_t noattr)))
                    (Tstruct ___gp_fse_t noattr)) _norm (tarray tshort 53))
                (Etempvar _i tuint) (tptr tshort)) tshort)
            (Etempvar _x_valid_dict_api__t'6 tshort))))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
          tuint))))
  (Ssequence
    (Ssequence
      (Sset _x_valid_dict_api__t'5
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct ___gp_fse_t noattr)))
            (Tstruct ___gp_fse_t noattr)) _nsym tuint))
      (Sassign
        (Efield
          (Ederef (Etempvar _d (tptr (Tstruct ___gp_fse_t noattr)))
            (Tstruct ___gp_fse_t noattr)) _nsym tuint) (Etempvar _x_valid_dict_api__t'5 tuint)))
    (Ssequence
      (Ssequence
        (Sset _x_valid_dict_api__t'4
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct ___gp_fse_t noattr)))
              (Tstruct ___gp_fse_t noattr)) _log tuint))
        (Sassign
          (Efield
            (Ederef (Etempvar _d (tptr (Tstruct ___gp_fse_t noattr)))
              (Tstruct ___gp_fse_t noattr)) _log tuint)
          (Etempvar _x_valid_dict_api__t'4 tuint)))
      (Ssequence
        (Sset _i (Econst_int (Int.repr 0) tint))
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                           (Ebinop Oshl (Econst_int (Int.repr 1) tuint)
                             (Econst_int (Int.repr 9) tint) tuint) tint)
              Sskip
              Sbreak)
            (Ssequence
              (Ssequence
                (Sset _x_valid_dict_api__t'3
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct ___gp_fse_t noattr)))
                          (Tstruct ___gp_fse_t noattr)) _sym
                        (tarray tuchar 512)) (Etempvar _i tuint)
                      (tptr tuchar)) tuchar))
                (Sassign
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef
                          (Etempvar _d (tptr (Tstruct ___gp_fse_t noattr)))
                          (Tstruct ___gp_fse_t noattr)) _sym
                        (tarray tuchar 512)) (Etempvar _i tuint)
                      (tptr tuchar)) tuchar) (Etempvar _x_valid_dict_api__t'3 tuchar)))
              (Ssequence
                (Ssequence
                  (Sset _x_valid_dict_api__t'2
                    (Ederef
                      (Ebinop Oadd
                        (Efield
                          (Ederef
                            (Etempvar _s (tptr (Tstruct ___gp_fse_t noattr)))
                            (Tstruct ___gp_fse_t noattr)) _nb
                          (tarray tuchar 512)) (Etempvar _i tuint)
                        (tptr tuchar)) tuchar))
                  (Sassign
                    (Ederef
                      (Ebinop Oadd
                        (Efield
                          (Ederef
                            (Etempvar _d (tptr (Tstruct ___gp_fse_t noattr)))
                            (Tstruct ___gp_fse_t noattr)) _nb
                          (tarray tuchar 512)) (Etempvar _i tuint)
                        (tptr tuchar)) tuchar) (Etempvar _x_valid_dict_api__t'2 tuchar)))
                (Ssequence
                  (Sset _x_valid_dict_api__t'1
                    (Ederef
                      (Ebinop Oadd
                        (Efield
                          (Ederef
                            (Etempvar _s (tptr (Tstruct ___gp_fse_t noattr)))
                            (Tstruct ___gp_fse_t noattr)) _base
                          (tarray tushort 512)) (Etempvar _i tuint)
                        (tptr tushort)) tushort))
                  (Sassign
                    (Ederef
                      (Ebinop Oadd
                        (Efield
                          (Ederef
                            (Etempvar _d (tptr (Tstruct ___gp_fse_t noattr)))
                            (Tstruct ___gp_fse_t noattr)) _base
                          (tarray tushort 512)) (Etempvar _i tuint)
                        (tptr tushort)) tushort) (Etempvar _x_valid_dict_api__t'1 tushort))))))
          (Sset _i
            (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
              tuint)))))))
|}.

Definition f_huf_copy := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_d, (tptr (Tstruct ___gp_huf_t noattr))) ::
                (_s, (tptr (Tstruct ___gp_huf_t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tuint) :: (_x_valid_dict_api__t'7, tuchar) :: (_x_valid_dict_api__t'6, tushort) ::
               (_x_valid_dict_api__t'5, tuchar) :: (_x_valid_dict_api__t'4, tuchar) :: (_x_valid_dict_api__t'3, tuint) ::
               (_x_valid_dict_api__t'2, tuint) :: (_x_valid_dict_api__t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _i (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                       (Econst_int (Int.repr 256) tint) tint)
          Sskip
          Sbreak)
        (Ssequence
          (Ssequence
            (Sset _x_valid_dict_api__t'7
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef (Etempvar _s (tptr (Tstruct ___gp_huf_t noattr)))
                      (Tstruct ___gp_huf_t noattr)) _w (tarray tuchar 256))
                  (Etempvar _i tuint) (tptr tuchar)) tuchar))
            (Sassign
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef (Etempvar _d (tptr (Tstruct ___gp_huf_t noattr)))
                      (Tstruct ___gp_huf_t noattr)) _w (tarray tuchar 256))
                  (Etempvar _i tuint) (tptr tuchar)) tuchar)
              (Etempvar _x_valid_dict_api__t'7 tuchar)))
          (Ssequence
            (Ssequence
              (Sset _x_valid_dict_api__t'6
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef
                        (Etempvar _s (tptr (Tstruct ___gp_huf_t noattr)))
                        (Tstruct ___gp_huf_t noattr)) _code
                      (tarray tushort 256)) (Etempvar _i tuint)
                    (tptr tushort)) tushort))
              (Sassign
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef
                        (Etempvar _d (tptr (Tstruct ___gp_huf_t noattr)))
                        (Tstruct ___gp_huf_t noattr)) _code
                      (tarray tushort 256)) (Etempvar _i tuint)
                    (tptr tushort)) tushort) (Etempvar _x_valid_dict_api__t'6 tushort)))
            (Ssequence
              (Ssequence
                (Sset _x_valid_dict_api__t'5
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct ___gp_huf_t noattr)))
                          (Tstruct ___gp_huf_t noattr)) _nb
                        (tarray tuchar 256)) (Etempvar _i tuint)
                      (tptr tuchar)) tuchar))
                (Sassign
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef
                          (Etempvar _d (tptr (Tstruct ___gp_huf_t noattr)))
                          (Tstruct ___gp_huf_t noattr)) _nb
                        (tarray tuchar 256)) (Etempvar _i tuint)
                      (tptr tuchar)) tuchar) (Etempvar _x_valid_dict_api__t'5 tuchar)))
              (Ssequence
                (Sset _x_valid_dict_api__t'4
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct ___gp_huf_t noattr)))
                          (Tstruct ___gp_huf_t noattr)) _used
                        (tarray tuchar 256)) (Etempvar _i tuint)
                      (tptr tuchar)) tuchar))
                (Sassign
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef
                          (Etempvar _d (tptr (Tstruct ___gp_huf_t noattr)))
                          (Tstruct ___gp_huf_t noattr)) _used
                        (tarray tuchar 256)) (Etempvar _i tuint)
                      (tptr tuchar)) tuchar) (Etempvar _x_valid_dict_api__t'4 tuchar)))))))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
          tuint))))
  (Ssequence
    (Ssequence
      (Sset _x_valid_dict_api__t'3
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct ___gp_huf_t noattr)))
            (Tstruct ___gp_huf_t noattr)) _last tuint))
      (Sassign
        (Efield
          (Ederef (Etempvar _d (tptr (Tstruct ___gp_huf_t noattr)))
            (Tstruct ___gp_huf_t noattr)) _last tuint) (Etempvar _x_valid_dict_api__t'3 tuint)))
    (Ssequence
      (Ssequence
        (Sset _x_valid_dict_api__t'2
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct ___gp_huf_t noattr)))
              (Tstruct ___gp_huf_t noattr)) _log tuint))
        (Sassign
          (Efield
            (Ederef (Etempvar _d (tptr (Tstruct ___gp_huf_t noattr)))
              (Tstruct ___gp_huf_t noattr)) _log tuint)
          (Etempvar _x_valid_dict_api__t'2 tuint)))
      (Ssequence
        (Sset _x_valid_dict_api__t'1
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct ___gp_huf_t noattr)))
              (Tstruct ___gp_huf_t noattr)) _nused tuint))
        (Sassign
          (Efield
            (Ederef (Etempvar _d (tptr (Tstruct ___gp_huf_t noattr)))
              (Tstruct ___gp_huf_t noattr)) _nused tuint)
          (Etempvar _x_valid_dict_api__t'1 tuint))))))
|}.

Definition f_wstate_copy := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_d, (tptr (Tstruct ___gp_wstate_t noattr))) ::
                (_s, (tptr (Tstruct ___gp_wstate_t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tuint) :: (_x_valid_dict_api__t'3, tuint) :: (_x_valid_dict_api__t'2, tint) ::
               (_x_valid_dict_api__t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _i (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                       (Econst_int (Int.repr 3) tint) tint)
          Sskip
          Sbreak)
        (Ssequence
          (Ssequence
            (Sset _x_valid_dict_api__t'3
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct ___gp_wstate_t noattr)))
                      (Tstruct ___gp_wstate_t noattr)) _rep (tarray tuint 3))
                  (Etempvar _i tuint) (tptr tuint)) tuint))
            (Sassign
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef
                      (Etempvar _d (tptr (Tstruct ___gp_wstate_t noattr)))
                      (Tstruct ___gp_wstate_t noattr)) _rep (tarray tuint 3))
                  (Etempvar _i tuint) (tptr tuint)) tuint)
              (Etempvar _x_valid_dict_api__t'3 tuint)))
          (Scall None
            (Evar _fse_copy (Tfunction
                              ((tptr (Tstruct ___gp_fse_t noattr)) ::
                               (tptr (Tstruct ___gp_fse_t noattr)) :: nil)
                              tvoid cc_default))
            ((Ebinop Oadd
               (Efield
                 (Ederef (Etempvar _d (tptr (Tstruct ___gp_wstate_t noattr)))
                   (Tstruct ___gp_wstate_t noattr)) _tab
                 (tarray (Tstruct ___gp_fse_t noattr) 3)) (Etempvar _i tuint)
               (tptr (Tstruct ___gp_fse_t noattr))) ::
             (Ebinop Oadd
               (Efield
                 (Ederef (Etempvar _s (tptr (Tstruct ___gp_wstate_t noattr)))
                   (Tstruct ___gp_wstate_t noattr)) _tab
                 (tarray (Tstruct ___gp_fse_t noattr) 3)) (Etempvar _i tuint)
               (tptr (Tstruct ___gp_fse_t noattr))) :: nil))))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
          tuint))))
  (Ssequence
    (Scall None
      (Evar _huf_copy (Tfunction
                        ((tptr (Tstruct ___gp_huf_t noattr)) ::
                         (tptr (Tstruct ___gp_huf_t noattr)) :: nil) tvoid
                        cc_default))
      ((Eaddrof
         (Efield
           (Ederef (Etempvar _d (tptr (Tstruct ___gp_wstate_t noattr)))
             (Tstruct ___gp_wstate_t noattr)) _huf
           (Tstruct ___gp_huf_t noattr)) (tptr (Tstruct ___gp_huf_t noattr))) ::
       (Eaddrof
         (Efield
           (Ederef (Etempvar _s (tptr (Tstruct ___gp_wstate_t noattr)))
             (Tstruct ___gp_wstate_t noattr)) _huf
           (Tstruct ___gp_huf_t noattr)) (tptr (Tstruct ___gp_huf_t noattr))) ::
       nil))
    (Ssequence
      (Ssequence
        (Sset _x_valid_dict_api__t'2
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct ___gp_wstate_t noattr)))
              (Tstruct ___gp_wstate_t noattr)) _have_huf tint))
        (Sassign
          (Efield
            (Ederef (Etempvar _d (tptr (Tstruct ___gp_wstate_t noattr)))
              (Tstruct ___gp_wstate_t noattr)) _have_huf tint)
          (Etempvar _x_valid_dict_api__t'2 tint)))
      (Ssequence
        (Sset _x_valid_dict_api__t'1
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct ___gp_wstate_t noattr)))
              (Tstruct ___gp_wstate_t noattr)) _have_tab tint))
        (Sassign
          (Efield
            (Ederef (Etempvar _d (tptr (Tstruct ___gp_wstate_t noattr)))
              (Tstruct ___gp_wstate_t noattr)) _have_tab tint)
          (Etempvar _x_valid_dict_api__t'1 tint))))))
|}.

Definition v_x_valid_dict_api__need__1 := {|
  gvar_info := (tarray tuchar 53);
  gvar_init := (Init_space 53 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_x_valid_dict_api__maxsym := {|
  gvar_info := (tarray tuint 3);
  gvar_init := (Init_int32 (Int.repr 35) :: Init_int32 (Int.repr 31) ::
                Init_int32 (Int.repr 52) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_x_valid_dict_api__maxlog := {|
  gvar_info := (tarray tuint 3);
  gvar_init := (Init_int32 (Int.repr 9) :: Init_int32 (Int.repr 8) ::
                Init_int32 (Int.repr 9) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_x_valid_dict_api__order := {|
  gvar_info := (tarray tuint 3);
  gvar_init := (Init_int32 (Int.repr 1) :: Init_int32 (Int.repr 2) ::
                Init_int32 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_w_dict := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_d, (tptr (Tstruct ___gp_wdict_t noattr))) :: nil);
  fn_vars := ((_o, (Tstruct ___gp_out_t noattr)) :: nil);
  fn_temps := ((_k, tulong) :: (_i, tulong) :: (_s, tuint) ::
               (_t__1, tuint) :: (_ty, tuint) :: (_x_valid_dict_api__t'11, tuint) ::
               (_x_valid_dict_api__t'10, tulong) :: (_x_valid_dict_api__t'9, tulong) :: (_x_valid_dict_api__t'8, tuint) ::
               (_x_valid_dict_api__t'7, tuint) :: (_x_valid_dict_api__t'6, tint) :: (_x_valid_dict_api__t'5, tint) ::
               (_x_valid_dict_api__t'4, tint) :: (_x_valid_dict_api__t'3, tuint) :: (_x_valid_dict_api__t'2, tulong) ::
               (_x_valid_dict_api__t'1, tuint) :: (_x_valid_dict_api__t'21, tuchar) :: (_x_valid_dict_api__t'20, tuchar) ::
               (_x_valid_dict_api__t'19, tuchar) :: (_x_valid_dict_api__t'18, tuchar) :: (_x_valid_dict_api__t'17, tuint) ::
               (_x_valid_dict_api__t'16, tuint) :: (_x_valid_dict_api__t'15, tuint) :: (_x_valid_dict_api__t'14, tuint) ::
               (_x_valid_dict_api__t'13, tint) :: (_x_valid_dict_api__t'12, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sassign (Efield (Evar _o (Tstruct ___gp_out_t noattr)) _p (tptr tuchar))
    (Efield
      (Ederef (Etempvar _d (tptr (Tstruct ___gp_wdict_t noattr)))
        (Tstruct ___gp_wdict_t noattr)) _bytes (tarray tuchar 6144)))
  (Ssequence
    (Sassign (Efield (Evar _o (Tstruct ___gp_out_t noattr)) _n tulong)
      (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Sassign (Efield (Evar _o (Tstruct ___gp_out_t noattr)) _cap tulong)
        (Esizeof (tarray tuchar 6144) tulong))
      (Ssequence
        (Ssequence
          (Scall (Some _x_valid_dict_api__t'1)
            (Evar _choose (Tfunction (tuint :: nil) tuint cc_default))
            ((Econst_int (Int.repr 2) tint) :: nil))
          (Sassign
            (Efield
              (Ederef (Etempvar _d (tptr (Tstruct ___gp_wdict_t noattr)))
                (Tstruct ___gp_wdict_t noattr)) _formatted tint)
            (Etempvar _x_valid_dict_api__t'1 tuint)))
        (Ssequence
          (Ssequence
            (Sset _x_valid_dict_api__t'13
              (Efield
                (Ederef (Etempvar _d (tptr (Tstruct ___gp_wdict_t noattr)))
                  (Tstruct ___gp_wdict_t noattr)) _formatted tint))
            (Sifthenelse (Eunop Onotbool (Etempvar _x_valid_dict_api__t'13 tint) tint)
              (Ssequence
                (Ssequence
                  (Scall (Some _x_valid_dict_api__t'2)
                    (Evar _choose_in (Tfunction (tulong :: tulong :: nil)
                                       tulong cc_default))
                    ((Econst_int (Int.repr 8) tint) ::
                     (Ebinop Oshl (Econst_int (Int.repr 1) tuint)
                       (Econst_int (Int.repr 12) tint) tuint) :: nil))
                  (Sset _k (Etempvar _x_valid_dict_api__t'2 tulong)))
                (Ssequence
                  (Ssequence
                    (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
                    (Sloop
                      (Ssequence
                        (Sifthenelse (Ebinop Olt (Etempvar _i tulong)
                                       (Etempvar _k tulong) tint)
                          Sskip
                          Sbreak)
                        (Ssequence
                          (Scall (Some _x_valid_dict_api__t'3)
                            (Evar _choose (Tfunction (tuint :: nil) tuint
                                            cc_default))
                            ((Econst_int (Int.repr 256) tint) :: nil))
                          (Scall None
                            (Evar _put8 (Tfunction
                                          ((tptr (Tstruct ___gp_out_t noattr)) ::
                                           tuint :: nil) tvoid cc_default))
                            ((Eaddrof (Evar _o (Tstruct ___gp_out_t noattr))
                               (tptr (Tstruct ___gp_out_t noattr))) ::
                             (Etempvar _x_valid_dict_api__t'3 tuint) :: nil))))
                      (Sset _i
                        (Ebinop Oadd (Etempvar _i tulong)
                          (Econst_int (Int.repr 1) tint) tulong))))
                  (Ssequence
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Ssequence
                            (Sset _x_valid_dict_api__t'20
                              (Ederef
                                (Ebinop Oadd
                                  (Efield
                                    (Ederef
                                      (Etempvar _d (tptr (Tstruct ___gp_wdict_t noattr)))
                                      (Tstruct ___gp_wdict_t noattr)) _bytes
                                    (tarray tuchar 6144))
                                  (Econst_int (Int.repr 0) tint)
                                  (tptr tuchar)) tuchar))
                            (Sifthenelse (Ebinop Oeq (Etempvar _x_valid_dict_api__t'20 tuchar)
                                           (Econst_int (Int.repr 55) tint)
                                           tint)
                              (Ssequence
                                (Sset _x_valid_dict_api__t'21
                                  (Ederef
                                    (Ebinop Oadd
                                      (Efield
                                        (Ederef
                                          (Etempvar _d (tptr (Tstruct ___gp_wdict_t noattr)))
                                          (Tstruct ___gp_wdict_t noattr))
                                        _bytes (tarray tuchar 6144))
                                      (Econst_int (Int.repr 1) tint)
                                      (tptr tuchar)) tuchar))
                                (Sset _x_valid_dict_api__t'4
                                  (Ecast
                                    (Ebinop Oeq (Etempvar _x_valid_dict_api__t'21 tuchar)
                                      (Econst_int (Int.repr 164) tint) tint)
                                    tbool)))
                              (Sset _x_valid_dict_api__t'4 (Econst_int (Int.repr 0) tint))))
                          (Sifthenelse (Etempvar _x_valid_dict_api__t'4 tint)
                            (Ssequence
                              (Sset _x_valid_dict_api__t'19
                                (Ederef
                                  (Ebinop Oadd
                                    (Efield
                                      (Ederef
                                        (Etempvar _d (tptr (Tstruct ___gp_wdict_t noattr)))
                                        (Tstruct ___gp_wdict_t noattr))
                                      _bytes (tarray tuchar 6144))
                                    (Econst_int (Int.repr 2) tint)
                                    (tptr tuchar)) tuchar))
                              (Sset _x_valid_dict_api__t'5
                                (Ecast
                                  (Ebinop Oeq (Etempvar _x_valid_dict_api__t'19 tuchar)
                                    (Econst_int (Int.repr 48) tint) tint)
                                  tbool)))
                            (Sset _x_valid_dict_api__t'5 (Econst_int (Int.repr 0) tint))))
                        (Sifthenelse (Etempvar _x_valid_dict_api__t'5 tint)
                          (Ssequence
                            (Sset _x_valid_dict_api__t'18
                              (Ederef
                                (Ebinop Oadd
                                  (Efield
                                    (Ederef
                                      (Etempvar _d (tptr (Tstruct ___gp_wdict_t noattr)))
                                      (Tstruct ___gp_wdict_t noattr)) _bytes
                                    (tarray tuchar 6144))
                                  (Econst_int (Int.repr 3) tint)
                                  (tptr tuchar)) tuchar))
                            (Sset _x_valid_dict_api__t'6
                              (Ecast
                                (Ebinop Oeq (Etempvar _x_valid_dict_api__t'18 tuchar)
                                  (Econst_int (Int.repr 236) tint) tint)
                                tbool)))
                          (Sset _x_valid_dict_api__t'6 (Econst_int (Int.repr 0) tint))))
                      (Scall None
                        (Evar _gp_assume (Tfunction (tint :: nil) tvoid
                                           cc_default))
                        ((Eunop Onotbool (Etempvar _x_valid_dict_api__t'6 tint) tint) :: nil)))
                    (Ssequence
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _d (tptr (Tstruct ___gp_wdict_t noattr)))
                            (Tstruct ___gp_wdict_t noattr)) _id tuint)
                        (Econst_int (Int.repr 0) tint))
                      (Ssequence
                        (Sassign
                          (Efield
                            (Ederef
                              (Etempvar _d (tptr (Tstruct ___gp_wdict_t noattr)))
                              (Tstruct ___gp_wdict_t noattr)) _content
                            (tptr tuchar))
                          (Efield
                            (Ederef
                              (Etempvar _d (tptr (Tstruct ___gp_wdict_t noattr)))
                              (Tstruct ___gp_wdict_t noattr)) _bytes
                            (tarray tuchar 6144)))
                        (Ssequence
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _d (tptr (Tstruct ___gp_wdict_t noattr)))
                                (Tstruct ___gp_wdict_t noattr)) _content_n
                              tulong) (Etempvar _k tulong))
                          (Ssequence
                            (Sassign
                              (Efield
                                (Efield
                                  (Ederef
                                    (Etempvar _d (tptr (Tstruct ___gp_wdict_t noattr)))
                                    (Tstruct ___gp_wdict_t noattr)) _x_valid_dict_api__st
                                  (Tstruct ___gp_wstate_t noattr)) _have_huf
                                tint) (Econst_int (Int.repr 0) tint))
                            (Ssequence
                              (Sassign
                                (Efield
                                  (Efield
                                    (Ederef
                                      (Etempvar _d (tptr (Tstruct ___gp_wdict_t noattr)))
                                      (Tstruct ___gp_wdict_t noattr)) _x_valid_dict_api__st
                                    (Tstruct ___gp_wstate_t noattr))
                                  _have_tab tint)
                                (Econst_int (Int.repr 0) tint))
                              (Ssequence
                                (Sassign
                                  (Ederef
                                    (Ebinop Oadd
                                      (Efield
                                        (Efield
                                          (Ederef
                                            (Etempvar _d (tptr (Tstruct ___gp_wdict_t noattr)))
                                            (Tstruct ___gp_wdict_t noattr))
                                          _x_valid_dict_api__st
                                          (Tstruct ___gp_wstate_t noattr))
                                        _rep (tarray tuint 3))
                                      (Econst_int (Int.repr 0) tint)
                                      (tptr tuint)) tuint)
                                  (Econst_int (Int.repr 1) tint))
                                (Ssequence
                                  (Sassign
                                    (Ederef
                                      (Ebinop Oadd
                                        (Efield
                                          (Efield
                                            (Ederef
                                              (Etempvar _d (tptr (Tstruct ___gp_wdict_t noattr)))
                                              (Tstruct ___gp_wdict_t noattr))
                                            _x_valid_dict_api__st
                                            (Tstruct ___gp_wstate_t noattr))
                                          _rep (tarray tuint 3))
                                        (Econst_int (Int.repr 1) tint)
                                        (tptr tuint)) tuint)
                                    (Econst_int (Int.repr 4) tint))
                                  (Sassign
                                    (Ederef
                                      (Ebinop Oadd
                                        (Efield
                                          (Efield
                                            (Ederef
                                              (Etempvar _d (tptr (Tstruct ___gp_wdict_t noattr)))
                                              (Tstruct ___gp_wdict_t noattr))
                                            _x_valid_dict_api__st
                                            (Tstruct ___gp_wstate_t noattr))
                                          _rep (tarray tuint 3))
                                        (Econst_int (Int.repr 2) tint)
                                        (tptr tuint)) tuint)
                                    (Econst_int (Int.repr 8) tint))))))))))))
              (Ssequence
                (Scall None
                  (Evar _put_le (Tfunction
                                  ((tptr (Tstruct ___gp_out_t noattr)) ::
                                   tulong :: tuint :: nil) tvoid cc_default))
                  ((Eaddrof (Evar _o (Tstruct ___gp_out_t noattr))
                     (tptr (Tstruct ___gp_out_t noattr))) ::
                   (Econst_int (Int.repr (-332356553)) tuint) ::
                   (Econst_int (Int.repr 4) tint) :: nil))
                (Ssequence
                  (Ssequence
                    (Scall (Some _x_valid_dict_api__t'7)
                      (Evar _choose (Tfunction (tuint :: nil) tuint
                                      cc_default))
                      ((Econst_int (Int.repr (-1)) tuint) :: nil))
                    (Sassign
                      (Efield
                        (Ederef
                          (Etempvar _d (tptr (Tstruct ___gp_wdict_t noattr)))
                          (Tstruct ___gp_wdict_t noattr)) _id tuint)
                      (Ebinop Oadd (Econst_int (Int.repr 1) tint)
                        (Etempvar _x_valid_dict_api__t'7 tuint) tuint)))
                  (Ssequence
                    (Ssequence
                      (Sset _x_valid_dict_api__t'17
                        (Efield
                          (Ederef
                            (Etempvar _d (tptr (Tstruct ___gp_wdict_t noattr)))
                            (Tstruct ___gp_wdict_t noattr)) _id tuint))
                      (Scall None
                        (Evar _put_le (Tfunction
                                        ((tptr (Tstruct ___gp_out_t noattr)) ::
                                         tulong :: tuint :: nil) tvoid
                                        cc_default))
                        ((Eaddrof (Evar _o (Tstruct ___gp_out_t noattr))
                           (tptr (Tstruct ___gp_out_t noattr))) ::
                         (Etempvar _x_valid_dict_api__t'17 tuint) ::
                         (Econst_int (Int.repr 4) tint) :: nil)))
                    (Ssequence
                      (Scall None
                        (Evar _huf_pick (Tfunction
                                          ((tptr (Tstruct ___gp_huf_t noattr)) ::
                                           nil) tvoid cc_default))
                        ((Eaddrof
                           (Efield
                             (Efield
                               (Ederef
                                 (Etempvar _d (tptr (Tstruct ___gp_wdict_t noattr)))
                                 (Tstruct ___gp_wdict_t noattr)) _x_valid_dict_api__st
                               (Tstruct ___gp_wstate_t noattr)) _huf
                             (Tstruct ___gp_huf_t noattr))
                           (tptr (Tstruct ___gp_huf_t noattr))) :: nil))
                      (Ssequence
                        (Scall None
                          (Evar _huf_put_description (Tfunction
                                                       ((tptr (Tstruct ___gp_out_t noattr)) ::
                                                        (tptr (Tstruct ___gp_huf_t noattr)) ::
                                                        nil) tvoid
                                                       cc_default))
                          ((Eaddrof (Evar _o (Tstruct ___gp_out_t noattr))
                             (tptr (Tstruct ___gp_out_t noattr))) ::
                           (Eaddrof
                             (Efield
                               (Efield
                                 (Ederef
                                   (Etempvar _d (tptr (Tstruct ___gp_wdict_t noattr)))
                                   (Tstruct ___gp_wdict_t noattr)) _x_valid_dict_api__st
                                 (Tstruct ___gp_wstate_t noattr)) _huf
                               (Tstruct ___gp_huf_t noattr))
                             (tptr (Tstruct ___gp_huf_t noattr))) :: nil))
                        (Ssequence
                          (Sassign
                            (Efield
                              (Efield
                                (Ederef
                                  (Etempvar _d (tptr (Tstruct ___gp_wdict_t noattr)))
                                  (Tstruct ___gp_wdict_t noattr)) _x_valid_dict_api__st
                                (Tstruct ___gp_wstate_t noattr)) _have_huf
                              tint) (Econst_int (Int.repr 1) tint))
                          (Ssequence
                            (Ssequence
                              (Sset _t__1 (Econst_int (Int.repr 0) tint))
                              (Sloop
                                (Ssequence
                                  (Sifthenelse (Ebinop Olt
                                                 (Etempvar _t__1 tuint)
                                                 (Econst_int (Int.repr 3) tint)
                                                 tint)
                                    Sskip
                                    Sbreak)
                                  (Ssequence
                                    (Sset _ty
                                      (Ederef
                                        (Ebinop Oadd
                                          (Evar _x_valid_dict_api__order (tarray tuint 3))
                                          (Etempvar _t__1 tuint)
                                          (tptr tuint)) tuint))
                                    (Ssequence
                                      (Ssequence
                                        (Sset _s
                                          (Econst_int (Int.repr 0) tint))
                                        (Sloop
                                          (Ssequence
                                            (Sifthenelse (Ebinop Olt
                                                           (Etempvar _s tuint)
                                                           (Econst_int (Int.repr 53) tint)
                                                           tint)
                                              Sskip
                                              Sbreak)
                                            (Sassign
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Evar _x_valid_dict_api__need__1 (tarray tuchar 53))
                                                  (Etempvar _s tuint)
                                                  (tptr tuchar)) tuchar)
                                              (Econst_int (Int.repr 0) tint)))
                                          (Sset _s
                                            (Ebinop Oadd (Etempvar _s tuint)
                                              (Econst_int (Int.repr 1) tint)
                                              tuint))))
                                      (Ssequence
                                        (Ssequence
                                          (Ssequence
                                            (Sset _x_valid_dict_api__t'16
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Evar _x_valid_dict_api__maxlog (tarray tuint 3))
                                                  (Etempvar _ty tuint)
                                                  (tptr tuint)) tuint))
                                            (Scall (Some _x_valid_dict_api__t'8)
                                              (Evar _choose (Tfunction
                                                              (tuint :: nil)
                                                              tuint
                                                              cc_default))
                                              ((Ebinop Osub
                                                 (Etempvar _x_valid_dict_api__t'16 tuint)
                                                 (Econst_int (Int.repr 4) tint)
                                                 tuint) :: nil)))
                                          (Ssequence
                                            (Sset _x_valid_dict_api__t'15
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Evar _x_valid_dict_api__maxsym (tarray tuint 3))
                                                  (Etempvar _ty tuint)
                                                  (tptr tuint)) tuint))
                                            (Scall None
                                              (Evar _fse_pick (Tfunction
                                                                ((tptr (Tstruct ___gp_fse_t noattr)) ::
                                                                 tuint ::
                                                                 tuint ::
                                                                 (tptr tuchar) ::
                                                                 nil) tvoid
                                                                cc_default))
                                              ((Ebinop Oadd
                                                 (Efield
                                                   (Efield
                                                     (Ederef
                                                       (Etempvar _d (tptr (Tstruct ___gp_wdict_t noattr)))
                                                       (Tstruct ___gp_wdict_t noattr))
                                                     _x_valid_dict_api__st
                                                     (Tstruct ___gp_wstate_t noattr))
                                                   _tab
                                                   (tarray (Tstruct ___gp_fse_t noattr) 3))
                                                 (Etempvar _ty tuint)
                                                 (tptr (Tstruct ___gp_fse_t noattr))) ::
                                               (Ebinop Oadd
                                                 (Econst_int (Int.repr 5) tint)
                                                 (Etempvar _x_valid_dict_api__t'8 tuint) tuint) ::
                                               (Etempvar _x_valid_dict_api__t'15 tuint) ::
                                               (Evar _x_valid_dict_api__need__1 (tarray tuchar 53)) ::
                                               nil))))
                                        (Scall None
                                          (Evar _fse_put_description 
                                          (Tfunction
                                            ((tptr (Tstruct ___gp_out_t noattr)) ::
                                             (tptr (Tstruct ___gp_fse_t noattr)) ::
                                             nil) tvoid cc_default))
                                          ((Eaddrof
                                             (Evar _o (Tstruct ___gp_out_t noattr))
                                             (tptr (Tstruct ___gp_out_t noattr))) ::
                                           (Ebinop Oadd
                                             (Efield
                                               (Efield
                                                 (Ederef
                                                   (Etempvar _d (tptr (Tstruct ___gp_wdict_t noattr)))
                                                   (Tstruct ___gp_wdict_t noattr))
                                                 _x_valid_dict_api__st
                                                 (Tstruct ___gp_wstate_t noattr))
                                               _tab
                                               (tarray (Tstruct ___gp_fse_t noattr) 3))
                                             (Etempvar _ty tuint)
                                             (tptr (Tstruct ___gp_fse_t noattr))) ::
                                           nil))))))
                                (Sset _t__1
                                  (Ebinop Oadd (Etempvar _t__1 tuint)
                                    (Econst_int (Int.repr 1) tint) tuint))))
                            (Ssequence
                              (Sassign
                                (Efield
                                  (Efield
                                    (Ederef
                                      (Etempvar _d (tptr (Tstruct ___gp_wdict_t noattr)))
                                      (Tstruct ___gp_wdict_t noattr)) _x_valid_dict_api__st
                                    (Tstruct ___gp_wstate_t noattr))
                                  _have_tab tint)
                                (Econst_int (Int.repr 1) tint))
                              (Ssequence
                                (Ssequence
                                  (Scall (Some _x_valid_dict_api__t'9)
                                    (Evar _choose_in (Tfunction
                                                       (tulong :: tulong ::
                                                        nil) tulong
                                                       cc_default))
                                    ((Econst_int (Int.repr 1) tint) ::
                                     (Ebinop Oshl
                                       (Econst_int (Int.repr 1) tuint)
                                       (Econst_int (Int.repr 12) tint) tuint) ::
                                     nil))
                                  (Sset _k (Etempvar _x_valid_dict_api__t'9 tulong)))
                                (Ssequence
                                  (Ssequence
                                    (Sset _t__1
                                      (Econst_int (Int.repr 0) tint))
                                    (Sloop
                                      (Ssequence
                                        (Sifthenelse (Ebinop Olt
                                                       (Etempvar _t__1 tuint)
                                                       (Econst_int (Int.repr 3) tint)
                                                       tint)
                                          Sskip
                                          Sbreak)
                                        (Ssequence
                                          (Ssequence
                                            (Scall (Some _x_valid_dict_api__t'10)
                                              (Evar _choose_in (Tfunction
                                                                 (tulong ::
                                                                  tulong ::
                                                                  nil) tulong
                                                                 cc_default))
                                              ((Econst_int (Int.repr 1) tint) ::
                                               (Etempvar _k tulong) :: nil))
                                            (Sassign
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Efield
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _d (tptr (Tstruct ___gp_wdict_t noattr)))
                                                        (Tstruct ___gp_wdict_t noattr))
                                                      _x_valid_dict_api__st
                                                      (Tstruct ___gp_wstate_t noattr))
                                                    _rep (tarray tuint 3))
                                                  (Etempvar _t__1 tuint)
                                                  (tptr tuint)) tuint)
                                              (Ecast (Etempvar _x_valid_dict_api__t'10 tulong)
                                                tuint)))
                                          (Ssequence
                                            (Sset _x_valid_dict_api__t'14
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Efield
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _d (tptr (Tstruct ___gp_wdict_t noattr)))
                                                        (Tstruct ___gp_wdict_t noattr))
                                                      _x_valid_dict_api__st
                                                      (Tstruct ___gp_wstate_t noattr))
                                                    _rep (tarray tuint 3))
                                                  (Etempvar _t__1 tuint)
                                                  (tptr tuint)) tuint))
                                            (Scall None
                                              (Evar _put_le (Tfunction
                                                              ((tptr (Tstruct ___gp_out_t noattr)) ::
                                                               tulong ::
                                                               tuint :: nil)
                                                              tvoid
                                                              cc_default))
                                              ((Eaddrof
                                                 (Evar _o (Tstruct ___gp_out_t noattr))
                                                 (tptr (Tstruct ___gp_out_t noattr))) ::
                                               (Etempvar _x_valid_dict_api__t'14 tuint) ::
                                               (Econst_int (Int.repr 4) tint) ::
                                               nil)))))
                                      (Sset _t__1
                                        (Ebinop Oadd (Etempvar _t__1 tuint)
                                          (Econst_int (Int.repr 1) tint)
                                          tuint))))
                                  (Ssequence
                                    (Sset _i
                                      (Efield
                                        (Evar _o (Tstruct ___gp_out_t noattr))
                                        _n tulong))
                                    (Ssequence
                                      (Ssequence
                                        (Sset _s
                                          (Econst_int (Int.repr 0) tint))
                                        (Sloop
                                          (Ssequence
                                            (Sifthenelse (Ebinop Olt
                                                           (Etempvar _s tuint)
                                                           (Etempvar _k tulong)
                                                           tint)
                                              Sskip
                                              Sbreak)
                                            (Ssequence
                                              (Scall (Some _x_valid_dict_api__t'11)
                                                (Evar _choose (Tfunction
                                                                (tuint ::
                                                                 nil) tuint
                                                                cc_default))
                                                ((Econst_int (Int.repr 256) tint) ::
                                                 nil))
                                              (Scall None
                                                (Evar _put8 (Tfunction
                                                              ((tptr (Tstruct ___gp_out_t noattr)) ::
                                                               tuint :: nil)
                                                              tvoid
                                                              cc_default))
                                                ((Eaddrof
                                                   (Evar _o (Tstruct ___gp_out_t noattr))
                                                   (tptr (Tstruct ___gp_out_t noattr))) ::
                                                 (Etempvar _x_valid_dict_api__t'11 tuint) ::
                                                 nil))))
                                          (Sset _s
                                            (Ebinop Oadd (Etempvar _s tuint)
                                              (Econst_int (Int.repr 1) tint)
                                              tuint))))
                                      (Ssequence
                                        (Sassign
                                          (Efield
                                            (Ederef
                                              (Etempvar _d (tptr (Tstruct ___gp_wdict_t noattr)))
                                              (Tstruct ___gp_wdict_t noattr))
                                            _content (tptr tuchar))
                                          (Ebinop Oadd
                                            (Efield
                                              (Ederef
                                                (Etempvar _d (tptr (Tstruct ___gp_wdict_t noattr)))
                                                (Tstruct ___gp_wdict_t noattr))
                                              _bytes (tarray tuchar 6144))
                                            (Etempvar _i tulong)
                                            (tptr tuchar)))
                                        (Sassign
                                          (Efield
                                            (Ederef
                                              (Etempvar _d (tptr (Tstruct ___gp_wdict_t noattr)))
                                              (Tstruct ___gp_wdict_t noattr))
                                            _content_n tulong)
                                          (Etempvar _k tulong)))))))))))))))))
          (Ssequence
            (Sset _x_valid_dict_api__t'12
              (Efield (Evar _o (Tstruct ___gp_out_t noattr)) _n tulong))
            (Sassign
              (Efield
                (Ederef (Etempvar _d (tptr (Tstruct ___gp_wdict_t noattr)))
                  (Tstruct ___gp_wdict_t noattr)) _n tulong)
              (Etempvar _x_valid_dict_api__t'12 tulong))))))))
|}.

Definition v_x_valid_dict_api__w_hist := {|
  gvar_info := (tarray tuchar 266240);
  gvar_init := (Init_space 266240 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_x_valid_dict_api__w_code := {|
  gvar_info := (tarray (tarray tuchar 65536) 3);
  gvar_init := (Init_space 196608 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_x_valid_dict_api__w_extra := {|
  gvar_info := (tarray (tarray tuint 65536) 3);
  gvar_init := (Init_space 786432 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_x_valid_dict_api__w_st := {|
  gvar_info := (tarray (tarray tushort 65536) 3);
  gvar_init := (Init_space 393216 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_x_valid_dict_api__w_lit := {|
  gvar_info := (tarray tuchar 131072);
  gvar_init := (Init_space 131072 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_x_valid_dict_api__blk_buf := {|
  gvar_info := (tarray tuchar 135168);
  gvar_init := (Init_space 135168 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_x_valid_dict_api__need__2 := {|
  gvar_info := (tarray tuchar 53);
  gvar_init := (Init_space 53 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_x_valid_dict_api__newhuf := {|
  gvar_info := (Tstruct ___gp_huf_t noattr);
  gvar_init := (Init_space 1292 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_x_valid_dict_api__ntab := {|
  gvar_info := (tarray (Tstruct ___gp_fse_t noattr) 3);
  gvar_init := (Init_space 6492 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_x_valid_dict_api__maxsym__1 := {|
  gvar_info := (tarray tuint 3);
  gvar_init := (Init_int32 (Int.repr 35) :: Init_int32 (Int.repr 31) ::
                Init_int32 (Int.repr 52) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_x_valid_dict_api__maxlog__1 := {|
  gvar_info := (tarray tuint 3);
  gvar_init := (Init_int32 (Int.repr 9) :: Init_int32 (Int.repr 8) ::
                Init_int32 (Int.repr 9) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_x_valid_dict_api__upd := {|
  gvar_info := (tarray tuint 3);
  gvar_init := (Init_int32 (Int.repr 2) :: Init_int32 (Int.repr 1) ::
                Init_int32 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_w_compressed_block := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_o, (tptr (Tstruct ___gp_out_t noattr))) ::
                (_st__1, (tptr (Tstruct ___gp_wstate_t noattr))) ::
                (_dictn, tulong) :: (_hn, (tptr tulong)) ::
                (_t__1, tulong) :: (_window, tulong) :: (_bmax, tulong) ::
                nil);
  fn_vars := ((_blk, (Tstruct ___gp_out_t noattr)) ::
              (_mode, (tarray tuint 3)) :: (_opts, (tarray tuint 4)) ::
              (_valid, (tarray tuint 3)) :: (_forms, (tarray tuint 3)) ::
              (_opts__1, (tarray tuint 4)) ::
              (_b, (Tstruct ___gp_bits_t noattr)) :: nil);
  fn_temps := ((_nseq, tulong) :: (_nlit, tulong) :: (_rem, tulong) ::
               (_i, tulong) :: (_litmode, tuint) :: (_rleb, tuint) ::
               (_ty, tuint) :: (_s, tuint) ::
               (_hp, (tptr (Tstruct ___gp_huf_t noattr))) :: (_no, tuint) ::
               (_ll, tulong) :: (_ml, tulong) :: (_pos, tulong) ::
               (_maxoff, tulong) :: (_off, tulong) :: (_ov, tulong) ::
               (_j, tulong) :: (_frame_pos, tulong) :: (_nv, tuint) ::
               (_r, tuint) :: (_kind, tuint) :: (_idx, tuint) ::
               (_v, tuint) :: (_c, tuchar) :: (_c__1, tuchar) ::
               (_nf, tuint) :: (_f, tuint) :: (_no__1, tuint) ::
               (_same, tuint) :: (_pre, tuint) :: (_covers, tuint) ::
               (_q, tulong) :: (_u, tuint) ::
               (_tb, (tptr (Tstruct ___gp_fse_t noattr))) ::
               (_sv, (tptr tushort)) :: (_x_valid_dict_api__t'51, tint) :: (_x_valid_dict_api__t'50, tint) ::
               (_x_valid_dict_api__t'49, tuint) :: (_x_valid_dict_api__t'48, tuint) :: (_x_valid_dict_api__t'47, tuint) ::
               (_x_valid_dict_api__t'46, tint) :: (_x_valid_dict_api__t'45, tuint) :: (_x_valid_dict_api__t'44, tuint) ::
               (_x_valid_dict_api__t'43, tuint) :: (_x_valid_dict_api__t'42, tint) :: (_x_valid_dict_api__t'41, tuint) ::
               (_x_valid_dict_api__t'40, tuint) :: (_x_valid_dict_api__t'39, tuint) :: (_x_valid_dict_api__t'38, tuint) ::
               (_x_valid_dict_api__t'37, tuint) :: (_x_valid_dict_api__t'36, tulong) :: (_x_valid_dict_api__t'35, tulong) ::
               (_x_valid_dict_api__t'34, tuint) :: (_x_valid_dict_api__t'33, tuint) :: (_x_valid_dict_api__t'32, tint) ::
               (_x_valid_dict_api__t'31, tuint) :: (_x_valid_dict_api__t'30, tuint) :: (_x_valid_dict_api__t'29, tuint) ::
               (_x_valid_dict_api__t'28, tulong) :: (_x_valid_dict_api__t'27, tulong) :: (_x_valid_dict_api__t'26, tuint) ::
               (_x_valid_dict_api__t'25, tuint) :: (_x_valid_dict_api__t'24, tint) :: (_x_valid_dict_api__t'23, tint) ::
               (_x_valid_dict_api__t'22, tint) :: (_x_valid_dict_api__t'21, tulong) :: (_x_valid_dict_api__t'20, tuint) ::
               (_x_valid_dict_api__t'19, tint) :: (_x_valid_dict_api__t'18, tuint) :: (_x_valid_dict_api__t'17, tuint) ::
               (_x_valid_dict_api__t'16, tuint) :: (_x_valid_dict_api__t'15, tuint) :: (_x_valid_dict_api__t'14, tulong) ::
               (_x_valid_dict_api__t'13, tint) :: (_x_valid_dict_api__t'12, tulong) :: (_x_valid_dict_api__t'11, tulong) ::
               (_x_valid_dict_api__t'10, tulong) :: (_x_valid_dict_api__t'9, tuint) :: (_x_valid_dict_api__t'8, tint) ::
               (_x_valid_dict_api__t'7, tint) :: (_x_valid_dict_api__t'6, tuint) :: (_x_valid_dict_api__t'5, tuint) ::
               (_x_valid_dict_api__t'4, tuint) :: (_x_valid_dict_api__t'3, tuint) :: (_x_valid_dict_api__t'2, tuint) ::
               (_x_valid_dict_api__t'1, tuint) :: (_x_valid_dict_api__t'115, tint) :: (_x_valid_dict_api__t'114, tulong) ::
               (_x_valid_dict_api__t'113, tuint) :: (_x_valid_dict_api__t'112, tuint) :: (_x_valid_dict_api__t'111, tuint) ::
               (_x_valid_dict_api__t'110, tuint) :: (_x_valid_dict_api__t'109, tuint) :: (_x_valid_dict_api__t'108, tuint) ::
               (_x_valid_dict_api__t'107, tuint) :: (_x_valid_dict_api__t'106, tuint) :: (_x_valid_dict_api__t'105, tuint) ::
               (_x_valid_dict_api__t'104, tuint) :: (_x_valid_dict_api__t'103, tuchar) :: (_x_valid_dict_api__t'102, tuchar) ::
               (_x_valid_dict_api__t'101, tulong) :: (_x_valid_dict_api__t'100, tulong) :: (_x_valid_dict_api__t'99, tulong) ::
               (_x_valid_dict_api__t'98, tuint) :: (_x_valid_dict_api__t'97, tuchar) :: (_x_valid_dict_api__t'96, tuint) ::
               (_x_valid_dict_api__t'95, tuchar) :: (_x_valid_dict_api__t'94, tuchar) :: (_x_valid_dict_api__t'93, tuint) ::
               (_x_valid_dict_api__t'92, tuchar) :: (_x_valid_dict_api__t'91, tuchar) :: (_x_valid_dict_api__t'90, tuchar) ::
               (_x_valid_dict_api__t'89, tuchar) :: (_x_valid_dict_api__t'88, tuchar) :: (_x_valid_dict_api__t'87, tint) ::
               (_x_valid_dict_api__t'86, tuint) :: (_x_valid_dict_api__t'85, tuchar) :: (_x_valid_dict_api__t'84, tuchar) ::
               (_x_valid_dict_api__t'83, tuint) :: (_x_valid_dict_api__t'82, tuint) :: (_x_valid_dict_api__t'81, tuint) ::
               (_x_valid_dict_api__t'80, tuint) :: (_x_valid_dict_api__t'79, tuint) :: (_x_valid_dict_api__t'78, tuint) ::
               (_x_valid_dict_api__t'77, tuint) :: (_x_valid_dict_api__t'76, tuint) :: (_x_valid_dict_api__t'75, tuchar) ::
               (_x_valid_dict_api__t'74, tuint) :: (_x_valid_dict_api__t'73, tuint) :: (_x_valid_dict_api__t'72, tuchar) ::
               (_x_valid_dict_api__t'71, tushort) :: (_x_valid_dict_api__t'70, tushort) :: (_x_valid_dict_api__t'69, tushort) ::
               (_x_valid_dict_api__t'68, tushort) :: (_x_valid_dict_api__t'67, tuchar) :: (_x_valid_dict_api__t'66, tuchar) ::
               (_x_valid_dict_api__t'65, tuint) :: (_x_valid_dict_api__t'64, tuchar) :: (_x_valid_dict_api__t'63, tuchar) ::
               (_x_valid_dict_api__t'62, tuint) :: (_x_valid_dict_api__t'61, tuchar) :: (_x_valid_dict_api__t'60, tuint) ::
               (_x_valid_dict_api__t'59, tuint) :: (_x_valid_dict_api__t'58, tushort) :: (_x_valid_dict_api__t'57, tuint) ::
               (_x_valid_dict_api__t'56, tushort) :: (_x_valid_dict_api__t'55, tuint) :: (_x_valid_dict_api__t'54, tushort) ::
               (_x_valid_dict_api__t'53, tulong) :: (_x_valid_dict_api__t'52, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sassign (Efield (Evar _blk (Tstruct ___gp_out_t noattr)) _p (tptr tuchar))
    (Evar _x_valid_dict_api__blk_buf (tarray tuchar 135168)))
  (Ssequence
    (Sassign (Efield (Evar _blk (Tstruct ___gp_out_t noattr)) _n tulong)
      (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Sassign (Efield (Evar _blk (Tstruct ___gp_out_t noattr)) _cap tulong)
        (Esizeof (tarray tuchar 135168) tulong))
      (Ssequence
        (Sset _nseq (Ecast (Econst_int (Int.repr 0) tint) tulong))
        (Ssequence
          (Sset _nlit (Ecast (Econst_int (Int.repr 0) tint) tulong))
          (Ssequence
            (Sset _rem (Etempvar _t__1 tulong))
            (Ssequence
              (Sset _rleb (Econst_int (Int.repr 0) tint))
              (Ssequence
                (Sset _hp
                  (Ecast (Econst_int (Int.repr 0) tint)
                    (tptr (Tstruct ___gp_huf_t noattr))))
                (Ssequence
                  (Ssequence
                    (Sset _no (Econst_int (Int.repr 0) tint))
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Sset _x_valid_dict_api__t'1 (Etempvar _no tuint))
                          (Sset _no
                            (Ebinop Oadd (Etempvar _x_valid_dict_api__t'1 tuint)
                              (Econst_int (Int.repr 1) tint) tuint)))
                        (Sassign
                          (Ederef
                            (Ebinop Oadd (Evar _opts (tarray tuint 4))
                              (Etempvar _x_valid_dict_api__t'1 tuint) (tptr tuint)) tuint)
                          (Econst_int (Int.repr 0) tint)))
                      (Ssequence
                        (Ssequence
                          (Ssequence
                            (Sset _x_valid_dict_api__t'2 (Etempvar _no tuint))
                            (Sset _no
                              (Ebinop Oadd (Etempvar _x_valid_dict_api__t'2 tuint)
                                (Econst_int (Int.repr 1) tint) tuint)))
                          (Sassign
                            (Ederef
                              (Ebinop Oadd (Evar _opts (tarray tuint 4))
                                (Etempvar _x_valid_dict_api__t'2 tuint) (tptr tuint)) tuint)
                            (Econst_int (Int.repr 1) tint)))
                        (Ssequence
                          (Ssequence
                            (Ssequence
                              (Sset _x_valid_dict_api__t'3 (Etempvar _no tuint))
                              (Sset _no
                                (Ebinop Oadd (Etempvar _x_valid_dict_api__t'3 tuint)
                                  (Econst_int (Int.repr 1) tint) tuint)))
                            (Sassign
                              (Ederef
                                (Ebinop Oadd (Evar _opts (tarray tuint 4))
                                  (Etempvar _x_valid_dict_api__t'3 tuint) (tptr tuint)) tuint)
                              (Econst_int (Int.repr 2) tint)))
                          (Ssequence
                            (Ssequence
                              (Sset _x_valid_dict_api__t'115
                                (Efield
                                  (Ederef
                                    (Etempvar _st__1 (tptr (Tstruct ___gp_wstate_t noattr)))
                                    (Tstruct ___gp_wstate_t noattr))
                                  _have_huf tint))
                              (Sifthenelse (Etempvar _x_valid_dict_api__t'115 tint)
                                (Ssequence
                                  (Ssequence
                                    (Sset _x_valid_dict_api__t'4 (Etempvar _no tuint))
                                    (Sset _no
                                      (Ebinop Oadd (Etempvar _x_valid_dict_api__t'4 tuint)
                                        (Econst_int (Int.repr 1) tint) tuint)))
                                  (Sassign
                                    (Ederef
                                      (Ebinop Oadd
                                        (Evar _opts (tarray tuint 4))
                                        (Etempvar _x_valid_dict_api__t'4 tuint) (tptr tuint))
                                      tuint) (Econst_int (Int.repr 3) tint)))
                                Sskip))
                            (Ssequence
                              (Scall (Some _x_valid_dict_api__t'5)
                                (Evar _choose (Tfunction (tuint :: nil) tuint
                                                cc_default))
                                ((Etempvar _no tuint) :: nil))
                              (Sset _litmode
                                (Ederef
                                  (Ebinop Oadd (Evar _opts (tarray tuint 4))
                                    (Etempvar _x_valid_dict_api__t'5 tuint) (tptr tuint))
                                  tuint))))))))
                  (Ssequence
                    (Sifthenelse (Ebinop Oeq (Etempvar _litmode tuint)
                                   (Econst_int (Int.repr 1) tint) tint)
                      (Ssequence
                        (Scall (Some _x_valid_dict_api__t'6)
                          (Evar _choose (Tfunction (tuint :: nil) tuint
                                          cc_default))
                          ((Econst_int (Int.repr 256) tint) :: nil))
                        (Sset _rleb (Etempvar _x_valid_dict_api__t'6 tuint)))
                      Sskip)
                    (Ssequence
                      (Sifthenelse (Ebinop Oeq (Etempvar _litmode tuint)
                                     (Econst_int (Int.repr 2) tint) tint)
                        (Ssequence
                          (Scall None
                            (Evar _huf_pick (Tfunction
                                              ((tptr (Tstruct ___gp_huf_t noattr)) ::
                                               nil) tvoid cc_default))
                            ((Eaddrof
                               (Evar _x_valid_dict_api__newhuf (Tstruct ___gp_huf_t noattr))
                               (tptr (Tstruct ___gp_huf_t noattr))) :: nil))
                          (Sset _hp
                            (Eaddrof
                              (Evar _x_valid_dict_api__newhuf (Tstruct ___gp_huf_t noattr))
                              (tptr (Tstruct ___gp_huf_t noattr)))))
                        Sskip)
                      (Ssequence
                        (Sifthenelse (Ebinop Oeq (Etempvar _litmode tuint)
                                       (Econst_int (Int.repr 3) tint) tint)
                          (Sset _hp
                            (Eaddrof
                              (Efield
                                (Ederef
                                  (Etempvar _st__1 (tptr (Tstruct ___gp_wstate_t noattr)))
                                  (Tstruct ___gp_wstate_t noattr)) _huf
                                (Tstruct ___gp_huf_t noattr))
                              (tptr (Tstruct ___gp_huf_t noattr))))
                          Sskip)
                        (Ssequence
                          (Sloop
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Sifthenelse (Ebinop Oge
                                                 (Etempvar _rem tulong)
                                                 (Econst_int (Int.repr 3) tint)
                                                 tint)
                                    (Sset _x_valid_dict_api__t'7
                                      (Ecast
                                        (Ebinop Olt (Etempvar _nseq tulong)
                                          (Ebinop Osub
                                            (Ebinop Oshl
                                              (Econst_int (Int.repr 1) tuint)
                                              (Econst_int (Int.repr 16) tint)
                                              tuint)
                                            (Econst_int (Int.repr 1) tint)
                                            tuint) tint) tbool))
                                    (Sset _x_valid_dict_api__t'7
                                      (Econst_int (Int.repr 0) tint)))
                                  (Sifthenelse (Etempvar _x_valid_dict_api__t'7 tint)
                                    (Ssequence
                                      (Scall (Some _x_valid_dict_api__t'9)
                                        (Evar _choose (Tfunction
                                                        (tuint :: nil) tuint
                                                        cc_default))
                                        ((Econst_int (Int.repr 4) tint) ::
                                         nil))
                                      (Sset _x_valid_dict_api__t'8
                                        (Ecast
                                          (Ebinop One (Etempvar _x_valid_dict_api__t'9 tuint)
                                            (Econst_int (Int.repr 0) tint)
                                            tint) tbool)))
                                    (Sset _x_valid_dict_api__t'8
                                      (Econst_int (Int.repr 0) tint))))
                                (Sifthenelse (Etempvar _x_valid_dict_api__t'8 tint)
                                  Sskip
                                  Sbreak))
                              (Ssequence
                                (Ssequence
                                  (Scall (Some _x_valid_dict_api__t'10)
                                    (Evar _choose_in (Tfunction
                                                       (tulong :: tulong ::
                                                        nil) tulong
                                                       cc_default))
                                    ((Econst_int (Int.repr 0) tint) ::
                                     (Ebinop Osub (Etempvar _rem tulong)
                                       (Econst_int (Int.repr 3) tint) tulong) ::
                                     nil))
                                  (Sset _ll (Etempvar _x_valid_dict_api__t'10 tulong)))
                                (Ssequence
                                  (Ssequence
                                    (Sset _x_valid_dict_api__t'114
                                      (Ederef (Etempvar _hn (tptr tulong))
                                        tulong))
                                    (Sset _frame_pos
                                      (Ebinop Osub (Etempvar _x_valid_dict_api__t'114 tulong)
                                        (Etempvar _dictn tulong) tulong)))
                                  (Ssequence
                                    (Sset _nv (Econst_int (Int.repr 0) tint))
                                    (Ssequence
                                      (Sset _pos
                                        (Ebinop Oadd
                                          (Etempvar _frame_pos tulong)
                                          (Etempvar _ll tulong) tulong))
                                      (Ssequence
                                        (Ssequence
                                          (Scall (Some _x_valid_dict_api__t'11)
                                            (Evar _choose_in (Tfunction
                                                               (tulong ::
                                                                tulong ::
                                                                nil) tulong
                                                               cc_default))
                                            ((Econst_int (Int.repr 3) tint) ::
                                             (Ebinop Osub
                                               (Etempvar _rem tulong)
                                               (Etempvar _ll tulong) tulong) ::
                                             nil))
                                          (Sset _ml (Etempvar _x_valid_dict_api__t'11 tulong)))
                                        (Ssequence
                                          (Ssequence
                                            (Sifthenelse (Ebinop Olt
                                                           (Etempvar _pos tulong)
                                                           (Ebinop Osub
                                                             (Etempvar _window tulong)
                                                             (Econst_int (Int.repr 1) tint)
                                                             tulong) tint)
                                              (Sset _x_valid_dict_api__t'12
                                                (Ecast (Etempvar _pos tulong)
                                                  tulong))
                                              (Sset _x_valid_dict_api__t'12
                                                (Ecast
                                                  (Ecast
                                                    (Ebinop Osub
                                                      (Etempvar _window tulong)
                                                      (Econst_int (Int.repr 1) tint)
                                                      tulong) tulong) tulong)))
                                            (Sset _maxoff
                                              (Etempvar _x_valid_dict_api__t'12 tulong)))
                                          (Ssequence
                                            (Ssequence
                                              (Sifthenelse (Ebinop Ogt
                                                             (Etempvar _dictn tulong)
                                                             (Econst_int (Int.repr 0) tint)
                                                             tint)
                                                (Sset _x_valid_dict_api__t'13
                                                  (Ecast
                                                    (Ebinop Ole
                                                      (Ebinop Oadd
                                                        (Etempvar _pos tulong)
                                                        (Etempvar _ml tulong)
                                                        tulong)
                                                      (Etempvar _window tulong)
                                                      tint) tbool))
                                                (Sset _x_valid_dict_api__t'13
                                                  (Econst_int (Int.repr 0) tint)))
                                              (Sifthenelse (Etempvar _x_valid_dict_api__t'13 tint)
                                                (Sset _maxoff
                                                  (Ebinop Oadd
                                                    (Etempvar _pos tulong)
                                                    (Etempvar _dictn tulong)
                                                    tulong))
                                                Sskip))
                                            (Ssequence
                                              (Sifthenelse (Ebinop Oeq
                                                             (Etempvar _maxoff tulong)
                                                             (Econst_int (Int.repr 0) tint)
                                                             tint)
                                                Sbreak
                                                Sskip)
                                              (Ssequence
                                                (Ssequence
                                                  (Scall (Some _x_valid_dict_api__t'14)
                                                    (Evar _choose_in 
                                                    (Tfunction
                                                      (tulong :: tulong ::
                                                       nil) tulong
                                                      cc_default))
                                                    ((Econst_int (Int.repr 1) tint) ::
                                                     (Etempvar _maxoff tulong) ::
                                                     nil))
                                                  (Sset _off
                                                    (Etempvar _x_valid_dict_api__t'14 tulong)))
                                                (Ssequence
                                                  (Sifthenelse (Ebinop Ogt
                                                                 (Etempvar _ll tulong)
                                                                 (Econst_int (Int.repr 0) tint)
                                                                 tint)
                                                    (Ssequence
                                                      (Sset _r
                                                        (Econst_int (Int.repr 0) tint))
                                                      (Sloop
                                                        (Ssequence
                                                          (Sifthenelse 
                                                            (Ebinop Olt
                                                              (Etempvar _r tuint)
                                                              (Econst_int (Int.repr 3) tint)
                                                              tint)
                                                            Sskip
                                                            Sbreak)
                                                          (Ssequence
                                                            (Sset _x_valid_dict_api__t'113
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Efield
                                                                    (Ederef
                                                                    (Etempvar _st__1 (tptr (Tstruct ___gp_wstate_t noattr)))
                                                                    (Tstruct ___gp_wstate_t noattr))
                                                                    _rep
                                                                    (tarray tuint 3))
                                                                  (Etempvar _r tuint)
                                                                  (tptr tuint))
                                                                tuint))
                                                            (Sifthenelse 
                                                              (Ebinop Oeq
                                                                (Etempvar _x_valid_dict_api__t'113 tuint)
                                                                (Etempvar _off tulong)
                                                                tint)
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Sset _x_valid_dict_api__t'15
                                                                    (Etempvar _nv tuint))
                                                                  (Sset _nv
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x_valid_dict_api__t'15 tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)))
                                                                (Sassign
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _valid (tarray tuint 3))
                                                                    (Etempvar _x_valid_dict_api__t'15 tuint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                  (Ebinop Oadd
                                                                    (Etempvar _r tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)))
                                                              Sskip)))
                                                        (Sset _r
                                                          (Ebinop Oadd
                                                            (Etempvar _r tuint)
                                                            (Econst_int (Int.repr 1) tint)
                                                            tuint))))
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sset _x_valid_dict_api__t'112
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Efield
                                                                (Ederef
                                                                  (Etempvar _st__1 (tptr (Tstruct ___gp_wstate_t noattr)))
                                                                  (Tstruct ___gp_wstate_t noattr))
                                                                _rep
                                                                (tarray tuint 3))
                                                              (Econst_int (Int.repr 1) tint)
                                                              (tptr tuint))
                                                            tuint))
                                                        (Sifthenelse 
                                                          (Ebinop Oeq
                                                            (Etempvar _x_valid_dict_api__t'112 tuint)
                                                            (Etempvar _off tulong)
                                                            tint)
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _x_valid_dict_api__t'16
                                                                (Etempvar _nv tuint))
                                                              (Sset _nv
                                                                (Ebinop Oadd
                                                                  (Etempvar _x_valid_dict_api__t'16 tuint)
                                                                  (Econst_int (Int.repr 1) tint)
                                                                  tuint)))
                                                            (Sassign
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _valid (tarray tuint 3))
                                                                  (Etempvar _x_valid_dict_api__t'16 tuint)
                                                                  (tptr tuint))
                                                                tuint)
                                                              (Econst_int (Int.repr 1) tint)))
                                                          Sskip))
                                                      (Ssequence
                                                        (Ssequence
                                                          (Sset _x_valid_dict_api__t'111
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Efield
                                                                  (Ederef
                                                                    (Etempvar _st__1 (tptr (Tstruct ___gp_wstate_t noattr)))
                                                                    (Tstruct ___gp_wstate_t noattr))
                                                                  _rep
                                                                  (tarray tuint 3))
                                                                (Econst_int (Int.repr 2) tint)
                                                                (tptr tuint))
                                                              tuint))
                                                          (Sifthenelse 
                                                            (Ebinop Oeq
                                                              (Etempvar _x_valid_dict_api__t'111 tuint)
                                                              (Etempvar _off tulong)
                                                              tint)
                                                            (Ssequence
                                                              (Ssequence
                                                                (Sset _x_valid_dict_api__t'17
                                                                  (Etempvar _nv tuint))
                                                                (Sset _nv
                                                                  (Ebinop Oadd
                                                                    (Etempvar _x_valid_dict_api__t'17 tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)))
                                                              (Sassign
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Evar _valid (tarray tuint 3))
                                                                    (Etempvar _x_valid_dict_api__t'17 tuint)
                                                                    (tptr tuint))
                                                                  tuint)
                                                                (Econst_int (Int.repr 2) tint)))
                                                            Sskip))
                                                        (Ssequence
                                                          (Ssequence
                                                            (Sset _x_valid_dict_api__t'109
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Efield
                                                                    (Ederef
                                                                    (Etempvar _st__1 (tptr (Tstruct ___gp_wstate_t noattr)))
                                                                    (Tstruct ___gp_wstate_t noattr))
                                                                    _rep
                                                                    (tarray tuint 3))
                                                                  (Econst_int (Int.repr 0) tint)
                                                                  (tptr tuint))
                                                                tuint))
                                                            (Sifthenelse 
                                                              (Ebinop Ogt
                                                                (Etempvar _x_valid_dict_api__t'109 tuint)
                                                                (Econst_int (Int.repr 1) tint)
                                                                tint)
                                                              (Ssequence
                                                                (Sset _x_valid_dict_api__t'110
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _st__1 (tptr (Tstruct ___gp_wstate_t noattr)))
                                                                    (Tstruct ___gp_wstate_t noattr))
                                                                    _rep
                                                                    (tarray tuint 3))
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                (Sset _x_valid_dict_api__t'19
                                                                  (Ecast
                                                                    (Ebinop Oeq
                                                                    (Ebinop Osub
                                                                    (Etempvar _x_valid_dict_api__t'110 tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)
                                                                    (Etempvar _off tulong)
                                                                    tint)
                                                                    tbool)))
                                                              (Sset _x_valid_dict_api__t'19
                                                                (Econst_int (Int.repr 0) tint))))
                                                          (Sifthenelse (Etempvar _x_valid_dict_api__t'19 tint)
                                                            (Ssequence
                                                              (Ssequence
                                                                (Sset _x_valid_dict_api__t'18
                                                                  (Etempvar _nv tuint))
                                                                (Sset _nv
                                                                  (Ebinop Oadd
                                                                    (Etempvar _x_valid_dict_api__t'18 tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)))
                                                              (Sassign
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Evar _valid (tarray tuint 3))
                                                                    (Etempvar _x_valid_dict_api__t'18 tuint)
                                                                    (tptr tuint))
                                                                  tuint)
                                                                (Econst_int (Int.repr 3) tint)))
                                                            Sskip)))))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Scall (Some _x_valid_dict_api__t'20)
                                                        (Evar _choose 
                                                        (Tfunction
                                                          (tuint :: nil)
                                                          tuint cc_default))
                                                        ((Ebinop Oadd
                                                           (Etempvar _nv tuint)
                                                           (Econst_int (Int.repr 1) tint)
                                                           tuint) :: nil))
                                                      (Sset _kind
                                                        (Etempvar _x_valid_dict_api__t'20 tuint)))
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sifthenelse 
                                                          (Ebinop Olt
                                                            (Etempvar _kind tuint)
                                                            (Etempvar _nv tuint)
                                                            tint)
                                                          (Ssequence
                                                            (Sset _x_valid_dict_api__t'108
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _valid (tarray tuint 3))
                                                                  (Etempvar _kind tuint)
                                                                  (tptr tuint))
                                                                tuint))
                                                            (Sset _x_valid_dict_api__t'21
                                                              (Ecast
                                                                (Etempvar _x_valid_dict_api__t'108 tuint)
                                                                tulong)))
                                                          (Sset _x_valid_dict_api__t'21
                                                            (Ecast
                                                              (Ebinop Oadd
                                                                (Etempvar _off tulong)
                                                                (Econst_int (Int.repr 3) tint)
                                                                tulong)
                                                              tulong)))
                                                        (Sset _ov
                                                          (Etempvar _x_valid_dict_api__t'21 tulong)))
                                                      (Ssequence
                                                        (Scall None
                                                          (Evar _gp_assume 
                                                          (Tfunction
                                                            (tint :: nil)
                                                            tvoid cc_default))
                                                          ((Ebinop Olt
                                                             (Etempvar _ov tulong)
                                                             (Ebinop Oshl
                                                               (Econst_long (Int64.repr 2) tulong)
                                                               (Econst_int (Int.repr 31) tint)
                                                               tulong) tint) ::
                                                           nil))
                                                        (Ssequence
                                                          (Ssequence
                                                            (Sifthenelse 
                                                              (Ebinop Ogt
                                                                (Etempvar _ov tulong)
                                                                (Econst_int (Int.repr 3) tint)
                                                                tint)
                                                              (Sset _x_valid_dict_api__t'23
                                                                (Econst_int (Int.repr 1) tint))
                                                              (Sifthenelse 
                                                                (Ebinop Oeq
                                                                  (Etempvar _ov tulong)
                                                                  (Econst_int (Int.repr 3) tint)
                                                                  tint)
                                                                (Ssequence
                                                                  (Sset _x_valid_dict_api__t'23
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _ll tulong)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    tbool))
                                                                  (Sset _x_valid_dict_api__t'23
                                                                    (Ecast
                                                                    (Etempvar _x_valid_dict_api__t'23 tint)
                                                                    tbool)))
                                                                (Sset _x_valid_dict_api__t'23
                                                                  (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tbool))))
                                                            (Sifthenelse (Etempvar _x_valid_dict_api__t'23 tint)
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Sset _x_valid_dict_api__t'107
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _st__1 (tptr (Tstruct ___gp_wstate_t noattr)))
                                                                    (Tstruct ___gp_wstate_t noattr))
                                                                    _rep
                                                                    (tarray tuint 3))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                  (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _st__1 (tptr (Tstruct ___gp_wstate_t noattr)))
                                                                    (Tstruct ___gp_wstate_t noattr))
                                                                    _rep
                                                                    (tarray tuint 3))
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _x_valid_dict_api__t'107 tuint)))
                                                                (Ssequence
                                                                  (Ssequence
                                                                    (Sset _x_valid_dict_api__t'106
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _st__1 (tptr (Tstruct ___gp_wstate_t noattr)))
                                                                    (Tstruct ___gp_wstate_t noattr))
                                                                    _rep
                                                                    (tarray tuint 3))
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _st__1 (tptr (Tstruct ___gp_wstate_t noattr)))
                                                                    (Tstruct ___gp_wstate_t noattr))
                                                                    _rep
                                                                    (tarray tuint 3))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _x_valid_dict_api__t'106 tuint)))
                                                                  (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _st__1 (tptr (Tstruct ___gp_wstate_t noattr)))
                                                                    (Tstruct ___gp_wstate_t noattr))
                                                                    _rep
                                                                    (tarray tuint 3))
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Ecast
                                                                    (Etempvar _off tulong)
                                                                    tuint))))
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _ll tulong)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Sset _x_valid_dict_api__t'22
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint))
                                                                    (Sset _x_valid_dict_api__t'22
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)))
                                                                  (Sset _idx
                                                                    (Ebinop Oadd
                                                                    (Ebinop Osub
                                                                    (Ecast
                                                                    (Etempvar _ov tulong)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)
                                                                    (Etempvar _x_valid_dict_api__t'22 tint)
                                                                    tuint)))
                                                                (Ssequence
                                                                  (Sset _v
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _st__1 (tptr (Tstruct ___gp_wstate_t noattr)))
                                                                    (Tstruct ___gp_wstate_t noattr))
                                                                    _rep
                                                                    (tarray tuint 3))
                                                                    (Etempvar _idx tuint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                  (Ssequence
                                                                    (Swhile
                                                                    (Ebinop Ogt
                                                                    (Etempvar _idx tuint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'105
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _st__1 (tptr (Tstruct ___gp_wstate_t noattr)))
                                                                    (Tstruct ___gp_wstate_t noattr))
                                                                    _rep
                                                                    (tarray tuint 3))
                                                                    (Ebinop Osub
                                                                    (Etempvar _idx tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _st__1 (tptr (Tstruct ___gp_wstate_t noattr)))
                                                                    (Tstruct ___gp_wstate_t noattr))
                                                                    _rep
                                                                    (tarray tuint 3))
                                                                    (Etempvar _idx tuint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _x_valid_dict_api__t'105 tuint)))
                                                                    (Sset _idx
                                                                    (Ebinop Osub
                                                                    (Etempvar _idx tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint))))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _st__1 (tptr (Tstruct ___gp_wstate_t noattr)))
                                                                    (Tstruct ___gp_wstate_t noattr))
                                                                    _rep
                                                                    (tarray tuint 3))
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _v tuint)))))))
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _j
                                                                (Ecast
                                                                  (Econst_int (Int.repr 0) tint)
                                                                  tulong))
                                                              (Sloop
                                                                (Ssequence
                                                                  (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _j tulong)
                                                                    (Etempvar _ll tulong)
                                                                    tint)
                                                                    Sskip
                                                                    Sbreak)
                                                                  (Ssequence
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _litmode tuint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall (Some _x_valid_dict_api__t'25)
                                                                    (Evar _choose 
                                                                    (Tfunction
                                                                    (tuint ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                    ((Econst_int (Int.repr 256) tint) ::
                                                                    nil))
                                                                    (Sset _x_valid_dict_api__t'24
                                                                    (Ecast
                                                                    (Ecast
                                                                    (Etempvar _x_valid_dict_api__t'25 tuint)
                                                                    tuchar)
                                                                    tint)))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _litmode tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'24
                                                                    (Ecast
                                                                    (Ecast
                                                                    (Etempvar _rleb tuint)
                                                                    tuchar)
                                                                    tint))
                                                                    (Sset _x_valid_dict_api__t'24
                                                                    (Ecast
                                                                    (Etempvar _x_valid_dict_api__t'24 tint)
                                                                    tint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'104
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _hp (tptr (Tstruct ___gp_huf_t noattr)))
                                                                    (Tstruct ___gp_huf_t noattr))
                                                                    _nused
                                                                    tuint))
                                                                    (Scall (Some _x_valid_dict_api__t'26)
                                                                    (Evar _choose 
                                                                    (Tfunction
                                                                    (tuint ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                    ((Etempvar _x_valid_dict_api__t'104 tuint) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'103
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _hp (tptr (Tstruct ___gp_huf_t noattr)))
                                                                    (Tstruct ___gp_huf_t noattr))
                                                                    _used
                                                                    (tarray tuchar 256))
                                                                    (Etempvar _x_valid_dict_api__t'26 tuint)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Sset _x_valid_dict_api__t'24
                                                                    (Ecast
                                                                    (Etempvar _x_valid_dict_api__t'103 tuchar)
                                                                    tint))))
                                                                    (Sset _x_valid_dict_api__t'24
                                                                    (Ecast
                                                                    (Etempvar _x_valid_dict_api__t'24 tint)
                                                                    tint)))))
                                                                    (Sset _c
                                                                    (Ecast
                                                                    (Etempvar _x_valid_dict_api__t'24 tint)
                                                                    tuchar)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'27
                                                                    (Etempvar _nlit tulong))
                                                                    (Sset _nlit
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x_valid_dict_api__t'27 tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong)))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_valid_dict_api__w_lit (tarray tuchar 131072))
                                                                    (Etempvar _x_valid_dict_api__t'27 tulong)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Etempvar _c tuchar)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'28
                                                                    (Ederef
                                                                    (Etempvar _hn (tptr tulong))
                                                                    tulong))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Etempvar _hn (tptr tulong))
                                                                    tulong)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x_valid_dict_api__t'28 tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong)))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_valid_dict_api__w_hist (tarray tuchar 266240))
                                                                    (Etempvar _x_valid_dict_api__t'28 tulong)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Etempvar _c tuchar))))))
                                                                (Sset _j
                                                                  (Ebinop Oadd
                                                                    (Etempvar _j tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong))))
                                                            (Ssequence
                                                              (Ssequence
                                                                (Sset _j
                                                                  (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tulong))
                                                                (Sloop
                                                                  (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _j tulong)
                                                                    (Etempvar _ml tulong)
                                                                    tint)
                                                                    Sskip
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'100
                                                                    (Ederef
                                                                    (Etempvar _hn (tptr tulong))
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'101
                                                                    (Ederef
                                                                    (Etempvar _hn (tptr tulong))
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'102
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_valid_dict_api__w_hist (tarray tuchar 266240))
                                                                    (Ebinop Osub
                                                                    (Etempvar _x_valid_dict_api__t'101 tulong)
                                                                    (Etempvar _off tulong)
                                                                    tulong)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_valid_dict_api__w_hist (tarray tuchar 266240))
                                                                    (Etempvar _x_valid_dict_api__t'100 tulong)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Etempvar _x_valid_dict_api__t'102 tuchar)))))
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'99
                                                                    (Ederef
                                                                    (Etempvar _hn (tptr tulong))
                                                                    tulong))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Etempvar _hn (tptr tulong))
                                                                    tulong)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x_valid_dict_api__t'99 tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong)))))
                                                                  (Sset _j
                                                                    (Ebinop Oadd
                                                                    (Etempvar _j tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong))))
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Scall (Some _x_valid_dict_api__t'29)
                                                                    (Evar _ll_code 
                                                                    (Tfunction
                                                                    (tulong ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                    ((Etempvar _ll tulong) ::
                                                                    nil))
                                                                  (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_valid_dict_api__w_code (tarray (tarray tuchar 65536) 3))
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr (tarray tuchar 65536)))
                                                                    (tarray tuchar 65536))
                                                                    (Etempvar _nseq tulong)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Ecast
                                                                    (Etempvar _x_valid_dict_api__t'29 tuint)
                                                                    tuchar)))
                                                                (Ssequence
                                                                  (Ssequence
                                                                    (Sset _x_valid_dict_api__t'97
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_valid_dict_api__w_code (tarray (tarray tuchar 65536) 3))
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr (tarray tuchar 65536)))
                                                                    (tarray tuchar 65536))
                                                                    (Etempvar _nseq tulong)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'98
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_valid_dict_api__W_LL_base (tarray tuint 36))
                                                                    (Etempvar _x_valid_dict_api__t'97 tuchar)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_valid_dict_api__w_extra (tarray (tarray tuint 65536) 3))
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr (tarray tuint 65536)))
                                                                    (tarray tuint 65536))
                                                                    (Etempvar _nseq tulong)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Ecast
                                                                    (Ebinop Osub
                                                                    (Etempvar _ll tulong)
                                                                    (Etempvar _x_valid_dict_api__t'98 tuint)
                                                                    tulong)
                                                                    tuint))))
                                                                  (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _x_valid_dict_api__t'30)
                                                                    (Evar _ml_code 
                                                                    (Tfunction
                                                                    (tulong ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                    ((Etempvar _ml tulong) ::
                                                                    nil))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_valid_dict_api__w_code (tarray (tarray tuchar 65536) 3))
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    (tptr (tarray tuchar 65536)))
                                                                    (tarray tuchar 65536))
                                                                    (Etempvar _nseq tulong)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Ecast
                                                                    (Etempvar _x_valid_dict_api__t'30 tuint)
                                                                    tuchar)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'95
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_valid_dict_api__w_code (tarray (tarray tuchar 65536) 3))
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    (tptr (tarray tuchar 65536)))
                                                                    (tarray tuchar 65536))
                                                                    (Etempvar _nseq tulong)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'96
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_valid_dict_api__W_ML_base (tarray tuint 53))
                                                                    (Etempvar _x_valid_dict_api__t'95 tuchar)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_valid_dict_api__w_extra (tarray (tarray tuint 65536) 3))
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    (tptr (tarray tuint 65536)))
                                                                    (tarray tuint 65536))
                                                                    (Etempvar _nseq tulong)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Ecast
                                                                    (Ebinop Osub
                                                                    (Etempvar _ml tulong)
                                                                    (Etempvar _x_valid_dict_api__t'96 tuint)
                                                                    tulong)
                                                                    tuint))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _x_valid_dict_api__t'31)
                                                                    (Evar _highbit 
                                                                    (Tfunction
                                                                    (tulong ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                    ((Etempvar _ov tulong) ::
                                                                    nil))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_valid_dict_api__w_code (tarray (tarray tuchar 65536) 3))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr (tarray tuchar 65536)))
                                                                    (tarray tuchar 65536))
                                                                    (Etempvar _nseq tulong)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Ecast
                                                                    (Etempvar _x_valid_dict_api__t'31 tuint)
                                                                    tuchar)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'94
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_valid_dict_api__w_code (tarray (tarray tuchar 65536) 3))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr (tarray tuchar 65536)))
                                                                    (tarray tuchar 65536))
                                                                    (Etempvar _nseq tulong)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_valid_dict_api__w_extra (tarray (tarray tuint 65536) 3))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr (tarray tuint 65536)))
                                                                    (tarray tuint 65536))
                                                                    (Etempvar _nseq tulong)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Ecast
                                                                    (Ebinop Osub
                                                                    (Etempvar _ov tulong)
                                                                    (Ebinop Oshl
                                                                    (Econst_long (Int64.repr 1) tulong)
                                                                    (Etempvar _x_valid_dict_api__t'94 tuchar)
                                                                    tulong)
                                                                    tulong)
                                                                    tuint)))
                                                                    (Ssequence
                                                                    (Sset _nseq
                                                                    (Ebinop Oadd
                                                                    (Etempvar _nseq tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong))
                                                                    (Sset _rem
                                                                    (Ebinop Osub
                                                                    (Etempvar _rem tulong)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _ll tulong)
                                                                    (Etempvar _ml tulong)
                                                                    tulong)
                                                                    tulong))))))))))))))))))))))))))
                            Sskip)
                          (Ssequence
                            (Ssequence
                              (Sset _i
                                (Ecast (Econst_int (Int.repr 0) tint) tulong))
                              (Sloop
                                (Ssequence
                                  (Sifthenelse (Ebinop Olt
                                                 (Etempvar _i tulong)
                                                 (Etempvar _rem tulong) tint)
                                    Sskip
                                    Sbreak)
                                  (Ssequence
                                    (Ssequence
                                      (Sifthenelse (Ebinop Oeq
                                                     (Etempvar _litmode tuint)
                                                     (Econst_int (Int.repr 0) tint)
                                                     tint)
                                        (Ssequence
                                          (Scall (Some _x_valid_dict_api__t'33)
                                            (Evar _choose (Tfunction
                                                            (tuint :: nil)
                                                            tuint cc_default))
                                            ((Econst_int (Int.repr 256) tint) ::
                                             nil))
                                          (Sset _x_valid_dict_api__t'32
                                            (Ecast
                                              (Ecast (Etempvar _x_valid_dict_api__t'33 tuint)
                                                tuchar) tint)))
                                        (Sifthenelse (Ebinop Oeq
                                                       (Etempvar _litmode tuint)
                                                       (Econst_int (Int.repr 1) tint)
                                                       tint)
                                          (Ssequence
                                            (Sset _x_valid_dict_api__t'32
                                              (Ecast
                                                (Ecast (Etempvar _rleb tuint)
                                                  tuchar) tint))
                                            (Sset _x_valid_dict_api__t'32
                                              (Ecast (Etempvar _x_valid_dict_api__t'32 tint)
                                                tint)))
                                          (Ssequence
                                            (Ssequence
                                              (Ssequence
                                                (Sset _x_valid_dict_api__t'93
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _hp (tptr (Tstruct ___gp_huf_t noattr)))
                                                      (Tstruct ___gp_huf_t noattr))
                                                    _nused tuint))
                                                (Scall (Some _x_valid_dict_api__t'34)
                                                  (Evar _choose (Tfunction
                                                                  (tuint ::
                                                                   nil) tuint
                                                                  cc_default))
                                                  ((Etempvar _x_valid_dict_api__t'93 tuint) ::
                                                   nil)))
                                              (Ssequence
                                                (Sset _x_valid_dict_api__t'92
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _hp (tptr (Tstruct ___gp_huf_t noattr)))
                                                          (Tstruct ___gp_huf_t noattr))
                                                        _used
                                                        (tarray tuchar 256))
                                                      (Etempvar _x_valid_dict_api__t'34 tuint)
                                                      (tptr tuchar)) tuchar))
                                                (Sset _x_valid_dict_api__t'32
                                                  (Ecast
                                                    (Etempvar _x_valid_dict_api__t'92 tuchar)
                                                    tint))))
                                            (Sset _x_valid_dict_api__t'32
                                              (Ecast (Etempvar _x_valid_dict_api__t'32 tint)
                                                tint)))))
                                      (Sset _c__1
                                        (Ecast (Etempvar _x_valid_dict_api__t'32 tint) tuchar)))
                                    (Ssequence
                                      (Ssequence
                                        (Ssequence
                                          (Sset _x_valid_dict_api__t'35
                                            (Etempvar _nlit tulong))
                                          (Sset _nlit
                                            (Ebinop Oadd
                                              (Etempvar _x_valid_dict_api__t'35 tulong)
                                              (Econst_int (Int.repr 1) tint)
                                              tulong)))
                                        (Sassign
                                          (Ederef
                                            (Ebinop Oadd
                                              (Evar _x_valid_dict_api__w_lit (tarray tuchar 131072))
                                              (Etempvar _x_valid_dict_api__t'35 tulong)
                                              (tptr tuchar)) tuchar)
                                          (Etempvar _c__1 tuchar)))
                                      (Ssequence
                                        (Ssequence
                                          (Sset _x_valid_dict_api__t'36
                                            (Ederef
                                              (Etempvar _hn (tptr tulong))
                                              tulong))
                                          (Sassign
                                            (Ederef
                                              (Etempvar _hn (tptr tulong))
                                              tulong)
                                            (Ebinop Oadd
                                              (Etempvar _x_valid_dict_api__t'36 tulong)
                                              (Econst_int (Int.repr 1) tint)
                                              tulong)))
                                        (Sassign
                                          (Ederef
                                            (Ebinop Oadd
                                              (Evar _x_valid_dict_api__w_hist (tarray tuchar 266240))
                                              (Etempvar _x_valid_dict_api__t'36 tulong)
                                              (tptr tuchar)) tuchar)
                                          (Etempvar _c__1 tuchar))))))
                                (Sset _i
                                  (Ebinop Oadd (Etempvar _i tulong)
                                    (Econst_int (Int.repr 1) tint) tulong))))
                            (Ssequence
                              (Sifthenelse (Ebinop Ole
                                             (Etempvar _litmode tuint)
                                             (Econst_int (Int.repr 1) tint)
                                             tint)
                                (Scall None
                                  (Evar _put_literals_raw_rle (Tfunction
                                                                ((tptr (Tstruct ___gp_out_t noattr)) ::
                                                                 tuint ::
                                                                 (tptr tuchar) ::
                                                                 tulong ::
                                                                 nil) tvoid
                                                                cc_default))
                                  ((Eaddrof
                                     (Evar _blk (Tstruct ___gp_out_t noattr))
                                     (tptr (Tstruct ___gp_out_t noattr))) ::
                                   (Etempvar _litmode tuint) ::
                                   (Evar _x_valid_dict_api__w_lit (tarray tuchar 131072)) ::
                                   (Etempvar _nlit tulong) :: nil))
                                (Scall None
                                  (Evar _put_literals_huf (Tfunction
                                                            ((tptr (Tstruct ___gp_out_t noattr)) ::
                                                             tuint ::
                                                             (tptr (Tstruct ___gp_huf_t noattr)) ::
                                                             (tptr tuchar) ::
                                                             tulong :: nil)
                                                            tvoid cc_default))
                                  ((Eaddrof
                                     (Evar _blk (Tstruct ___gp_out_t noattr))
                                     (tptr (Tstruct ___gp_out_t noattr))) ::
                                   (Etempvar _litmode tuint) ::
                                   (Etempvar _hp (tptr (Tstruct ___gp_huf_t noattr))) ::
                                   (Evar _x_valid_dict_api__w_lit (tarray tuchar 131072)) ::
                                   (Etempvar _nlit tulong) :: nil)))
                              (Ssequence
                                (Sifthenelse (Ebinop Oeq
                                               (Etempvar _litmode tuint)
                                               (Econst_int (Int.repr 2) tint)
                                               tint)
                                  (Ssequence
                                    (Scall None
                                      (Evar _huf_copy (Tfunction
                                                        ((tptr (Tstruct ___gp_huf_t noattr)) ::
                                                         (tptr (Tstruct ___gp_huf_t noattr)) ::
                                                         nil) tvoid
                                                        cc_default))
                                      ((Eaddrof
                                         (Efield
                                           (Ederef
                                             (Etempvar _st__1 (tptr (Tstruct ___gp_wstate_t noattr)))
                                             (Tstruct ___gp_wstate_t noattr))
                                           _huf (Tstruct ___gp_huf_t noattr))
                                         (tptr (Tstruct ___gp_huf_t noattr))) ::
                                       (Eaddrof
                                         (Evar _x_valid_dict_api__newhuf (Tstruct ___gp_huf_t noattr))
                                         (tptr (Tstruct ___gp_huf_t noattr))) ::
                                       nil))
                                    (Sassign
                                      (Efield
                                        (Ederef
                                          (Etempvar _st__1 (tptr (Tstruct ___gp_wstate_t noattr)))
                                          (Tstruct ___gp_wstate_t noattr))
                                        _have_huf tint)
                                      (Econst_int (Int.repr 1) tint)))
                                  Sskip)
                                (Ssequence
                                  (Sifthenelse (Ebinop Oeq
                                                 (Etempvar _nseq tulong)
                                                 (Econst_int (Int.repr 0) tint)
                                                 tint)
                                    (Ssequence
                                      (Scall (Some _x_valid_dict_api__t'37)
                                        (Evar _choose (Tfunction
                                                        (tuint :: nil) tuint
                                                        cc_default))
                                        ((Econst_int (Int.repr 2) tint) ::
                                         nil))
                                      (Sifthenelse (Etempvar _x_valid_dict_api__t'37 tuint)
                                        (Scall None
                                          (Evar _put8 (Tfunction
                                                        ((tptr (Tstruct ___gp_out_t noattr)) ::
                                                         tuint :: nil) tvoid
                                                        cc_default))
                                          ((Eaddrof
                                             (Evar _blk (Tstruct ___gp_out_t noattr))
                                             (tptr (Tstruct ___gp_out_t noattr))) ::
                                           (Econst_int (Int.repr 0) tint) ::
                                           nil))
                                        (Scall None
                                          (Evar _put_le (Tfunction
                                                          ((tptr (Tstruct ___gp_out_t noattr)) ::
                                                           tulong :: tuint ::
                                                           nil) tvoid
                                                          cc_default))
                                          ((Eaddrof
                                             (Evar _blk (Tstruct ___gp_out_t noattr))
                                             (tptr (Tstruct ___gp_out_t noattr))) ::
                                           (Econst_int (Int.repr 128) tint) ::
                                           (Econst_int (Int.repr 2) tint) ::
                                           nil))))
                                    (Ssequence
                                      (Sset _nf
                                        (Econst_int (Int.repr 0) tint))
                                      (Ssequence
                                        (Sifthenelse (Ebinop Olt
                                                       (Etempvar _nseq tulong)
                                                       (Econst_int (Int.repr 128) tint)
                                                       tint)
                                          (Ssequence
                                            (Ssequence
                                              (Sset _x_valid_dict_api__t'38
                                                (Etempvar _nf tuint))
                                              (Sset _nf
                                                (Ebinop Oadd
                                                  (Etempvar _x_valid_dict_api__t'38 tuint)
                                                  (Econst_int (Int.repr 1) tint)
                                                  tuint)))
                                            (Sassign
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Evar _forms (tarray tuint 3))
                                                  (Etempvar _x_valid_dict_api__t'38 tuint)
                                                  (tptr tuint)) tuint)
                                              (Econst_int (Int.repr 0) tint)))
                                          Sskip)
                                        (Ssequence
                                          (Sifthenelse (Ebinop Olt
                                                         (Etempvar _nseq tulong)
                                                         (Econst_int (Int.repr 32512) tint)
                                                         tint)
                                            (Ssequence
                                              (Ssequence
                                                (Sset _x_valid_dict_api__t'39
                                                  (Etempvar _nf tuint))
                                                (Sset _nf
                                                  (Ebinop Oadd
                                                    (Etempvar _x_valid_dict_api__t'39 tuint)
                                                    (Econst_int (Int.repr 1) tint)
                                                    tuint)))
                                              (Sassign
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Evar _forms (tarray tuint 3))
                                                    (Etempvar _x_valid_dict_api__t'39 tuint)
                                                    (tptr tuint)) tuint)
                                                (Econst_int (Int.repr 1) tint)))
                                            Sskip)
                                          (Ssequence
                                            (Sifthenelse (Ebinop Oge
                                                           (Etempvar _nseq tulong)
                                                           (Econst_int (Int.repr 32512) tint)
                                                           tint)
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _x_valid_dict_api__t'40
                                                    (Etempvar _nf tuint))
                                                  (Sset _nf
                                                    (Ebinop Oadd
                                                      (Etempvar _x_valid_dict_api__t'40 tuint)
                                                      (Econst_int (Int.repr 1) tint)
                                                      tuint)))
                                                (Sassign
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Evar _forms (tarray tuint 3))
                                                      (Etempvar _x_valid_dict_api__t'40 tuint)
                                                      (tptr tuint)) tuint)
                                                  (Econst_int (Int.repr 2) tint)))
                                              Sskip)
                                            (Ssequence
                                              (Ssequence
                                                (Scall (Some _x_valid_dict_api__t'41)
                                                  (Evar _choose (Tfunction
                                                                  (tuint ::
                                                                   nil) tuint
                                                                  cc_default))
                                                  ((Etempvar _nf tuint) ::
                                                   nil))
                                                (Sset _f
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Evar _forms (tarray tuint 3))
                                                      (Etempvar _x_valid_dict_api__t'41 tuint)
                                                      (tptr tuint)) tuint)))
                                              (Ssequence
                                                (Sifthenelse (Ebinop Oeq
                                                               (Etempvar _f tuint)
                                                               (Econst_int (Int.repr 0) tint)
                                                               tint)
                                                  (Scall None
                                                    (Evar _put8 (Tfunction
                                                                  ((tptr (Tstruct ___gp_out_t noattr)) ::
                                                                   tuint ::
                                                                   nil) tvoid
                                                                  cc_default))
                                                    ((Eaddrof
                                                       (Evar _blk (Tstruct ___gp_out_t noattr))
                                                       (tptr (Tstruct ___gp_out_t noattr))) ::
                                                     (Ecast
                                                       (Etempvar _nseq tulong)
                                                       tuint) :: nil))
                                                  (Sifthenelse (Ebinop Oeq
                                                                 (Etempvar _f tuint)
                                                                 (Econst_int (Int.repr 1) tint)
                                                                 tint)
                                                    (Ssequence
                                                      (Scall None
                                                        (Evar _put8 (Tfunction
                                                                    ((tptr (Tstruct ___gp_out_t noattr)) ::
                                                                    tuint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                        ((Eaddrof
                                                           (Evar _blk (Tstruct ___gp_out_t noattr))
                                                           (tptr (Tstruct ___gp_out_t noattr))) ::
                                                         (Ebinop Oadd
                                                           (Econst_int (Int.repr 128) tint)
                                                           (Ecast
                                                             (Ebinop Oshr
                                                               (Etempvar _nseq tulong)
                                                               (Econst_int (Int.repr 8) tint)
                                                               tulong) tuint)
                                                           tuint) :: nil))
                                                      (Scall None
                                                        (Evar _put8 (Tfunction
                                                                    ((tptr (Tstruct ___gp_out_t noattr)) ::
                                                                    tuint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                        ((Eaddrof
                                                           (Evar _blk (Tstruct ___gp_out_t noattr))
                                                           (tptr (Tstruct ___gp_out_t noattr))) ::
                                                         (Ecast
                                                           (Ebinop Oand
                                                             (Etempvar _nseq tulong)
                                                             (Econst_int (Int.repr 255) tint)
                                                             tulong) tuint) ::
                                                         nil)))
                                                    (Ssequence
                                                      (Scall None
                                                        (Evar _put8 (Tfunction
                                                                    ((tptr (Tstruct ___gp_out_t noattr)) ::
                                                                    tuint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                        ((Eaddrof
                                                           (Evar _blk (Tstruct ___gp_out_t noattr))
                                                           (tptr (Tstruct ___gp_out_t noattr))) ::
                                                         (Econst_int (Int.repr 255) tint) ::
                                                         nil))
                                                      (Scall None
                                                        (Evar _put_le 
                                                        (Tfunction
                                                          ((tptr (Tstruct ___gp_out_t noattr)) ::
                                                           tulong :: tuint ::
                                                           nil) tvoid
                                                          cc_default))
                                                        ((Eaddrof
                                                           (Evar _blk (Tstruct ___gp_out_t noattr))
                                                           (tptr (Tstruct ___gp_out_t noattr))) ::
                                                         (Ebinop Osub
                                                           (Etempvar _nseq tulong)
                                                           (Econst_int (Int.repr 32512) tint)
                                                           tulong) ::
                                                         (Econst_int (Int.repr 2) tint) ::
                                                         nil)))))
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _ty
                                                      (Econst_int (Int.repr 0) tint))
                                                    (Sloop
                                                      (Ssequence
                                                        (Sifthenelse 
                                                          (Ebinop Olt
                                                            (Etempvar _ty tuint)
                                                            (Econst_int (Int.repr 3) tint)
                                                            tint)
                                                          Sskip
                                                          Sbreak)
                                                        (Ssequence
                                                          (Sset _no__1
                                                            (Econst_int (Int.repr 0) tint))
                                                          (Ssequence
                                                            (Sset _same
                                                              (Econst_int (Int.repr 1) tint))
                                                            (Ssequence
                                                              (Sset _pre
                                                                (Econst_int (Int.repr 1) tint))
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Sset _i
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tulong))
                                                                  (Sloop
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _i tulong)
                                                                    (Etempvar _nseq tulong)
                                                                    tint)
                                                                    Sskip
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'90
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_valid_dict_api__w_code (tarray (tarray tuchar 65536) 3))
                                                                    (Etempvar _ty tuint)
                                                                    (tptr (tarray tuchar 65536)))
                                                                    (tarray tuchar 65536))
                                                                    (Etempvar _i tulong)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'91
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_valid_dict_api__w_code (tarray (tarray tuchar 65536) 3))
                                                                    (Etempvar _ty tuint)
                                                                    (tptr (tarray tuchar 65536)))
                                                                    (tarray tuchar 65536))
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Sifthenelse 
                                                                    (Ebinop One
                                                                    (Etempvar _x_valid_dict_api__t'90 tuchar)
                                                                    (Etempvar _x_valid_dict_api__t'91 tuchar)
                                                                    tint)
                                                                    (Sset _same
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    Sskip)))
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _ty tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'89
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_valid_dict_api__w_code (tarray (tarray tuchar 65536) 3))
                                                                    (Etempvar _ty tuint)
                                                                    (tptr (tarray tuchar 65536)))
                                                                    (tarray tuchar 65536))
                                                                    (Etempvar _i tulong)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Sset _x_valid_dict_api__t'42
                                                                    (Ecast
                                                                    (Ebinop Ogt
                                                                    (Etempvar _x_valid_dict_api__t'89 tuchar)
                                                                    (Econst_int (Int.repr 28) tint)
                                                                    tint)
                                                                    tbool)))
                                                                    (Sset _x_valid_dict_api__t'42
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                    (Sifthenelse (Etempvar _x_valid_dict_api__t'42 tint)
                                                                    (Sset _pre
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    Sskip))))
                                                                    (Sset _i
                                                                    (Ebinop Oadd
                                                                    (Etempvar _i tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong))))
                                                                (Ssequence
                                                                  (Sifthenelse (Etempvar _pre tuint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'43
                                                                    (Etempvar _no__1 tuint))
                                                                    (Sset _no__1
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x_valid_dict_api__t'43 tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _opts__1 (tarray tuint 4))
                                                                    (Etempvar _x_valid_dict_api__t'43 tuint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                    Sskip)
                                                                  (Ssequence
                                                                    (Sifthenelse (Etempvar _same tuint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'44
                                                                    (Etempvar _no__1 tuint))
                                                                    (Sset _no__1
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x_valid_dict_api__t'44 tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _opts__1 (tarray tuint 4))
                                                                    (Etempvar _x_valid_dict_api__t'44 tuint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Econst_int (Int.repr 1) tint)))
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'45
                                                                    (Etempvar _no__1 tuint))
                                                                    (Sset _no__1
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x_valid_dict_api__t'45 tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _opts__1 (tarray tuint 4))
                                                                    (Etempvar _x_valid_dict_api__t'45 tuint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Econst_int (Int.repr 2) tint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'87
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _st__1 (tptr (Tstruct ___gp_wstate_t noattr)))
                                                                    (Tstruct ___gp_wstate_t noattr))
                                                                    _have_tab
                                                                    tint))
                                                                    (Sifthenelse (Etempvar _x_valid_dict_api__t'87 tint)
                                                                    (Ssequence
                                                                    (Sset _covers
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _i
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tulong))
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _i tulong)
                                                                    (Etempvar _nseq tulong)
                                                                    tint)
                                                                    Sskip
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'88
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_valid_dict_api__w_code (tarray (tarray tuchar 65536) 3))
                                                                    (Etempvar _ty tuint)
                                                                    (tptr (tarray tuchar 65536)))
                                                                    (tarray tuchar 65536))
                                                                    (Etempvar _i tulong)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Scall (Some _x_valid_dict_api__t'46)
                                                                    (Evar _fse_has 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct ___gp_fse_t noattr)) ::
                                                                    tuint ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Ebinop Oadd
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _st__1 (tptr (Tstruct ___gp_wstate_t noattr)))
                                                                    (Tstruct ___gp_wstate_t noattr))
                                                                    _tab
                                                                    (tarray (Tstruct ___gp_fse_t noattr) 3))
                                                                    (Etempvar _ty tuint)
                                                                    (tptr (Tstruct ___gp_fse_t noattr))) ::
                                                                    (Etempvar _x_valid_dict_api__t'88 tuchar) ::
                                                                    nil)))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _x_valid_dict_api__t'46 tint)
                                                                    tint)
                                                                    (Sset _covers
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    Sskip)))
                                                                    (Sset _i
                                                                    (Ebinop Oadd
                                                                    (Etempvar _i tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong))))
                                                                    (Sifthenelse (Etempvar _covers tuint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'47
                                                                    (Etempvar _no__1 tuint))
                                                                    (Sset _no__1
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x_valid_dict_api__t'47 tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _opts__1 (tarray tuint 4))
                                                                    (Etempvar _x_valid_dict_api__t'47 tuint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Econst_int (Int.repr 3) tint)))
                                                                    Sskip)))
                                                                    Sskip))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _x_valid_dict_api__t'48)
                                                                    (Evar _choose 
                                                                    (Tfunction
                                                                    (tuint ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                    ((Etempvar _no__1 tuint) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'86
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _opts__1 (tarray tuint 4))
                                                                    (Etempvar _x_valid_dict_api__t'48 tuint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _mode (tarray tuint 3))
                                                                    (Etempvar _ty tuint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _x_valid_dict_api__t'86 tuint))))
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'79
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _mode (tarray tuint 3))
                                                                    (Etempvar _ty tuint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _x_valid_dict_api__t'79 tuint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Scall None
                                                                    (Evar _fse_predefined 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct ___gp_fse_t noattr)) ::
                                                                    tuint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Ebinop Oadd
                                                                    (Evar _x_valid_dict_api__ntab (tarray (Tstruct ___gp_fse_t noattr) 3))
                                                                    (Etempvar _ty tuint)
                                                                    (tptr (Tstruct ___gp_fse_t noattr))) ::
                                                                    (Etempvar _ty tuint) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'80
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _mode (tarray tuint 3))
                                                                    (Etempvar _ty tuint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _x_valid_dict_api__t'80 tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'85
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_valid_dict_api__w_code (tarray (tarray tuchar 65536) 3))
                                                                    (Etempvar _ty tuint)
                                                                    (tptr (tarray tuchar 65536)))
                                                                    (tarray tuchar 65536))
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Scall None
                                                                    (Evar _fse_rle 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct ___gp_fse_t noattr)) ::
                                                                    tuint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Ebinop Oadd
                                                                    (Evar _x_valid_dict_api__ntab (tarray (Tstruct ___gp_fse_t noattr) 3))
                                                                    (Etempvar _ty tuint)
                                                                    (tptr (Tstruct ___gp_fse_t noattr))) ::
                                                                    (Etempvar _x_valid_dict_api__t'85 tuchar) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'81
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _mode (tarray tuint 3))
                                                                    (Etempvar _ty tuint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _x_valid_dict_api__t'81 tuint)
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _s
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _s tuint)
                                                                    (Econst_int (Int.repr 53) tint)
                                                                    tint)
                                                                    Sskip
                                                                    Sbreak)
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_valid_dict_api__need__2 (tarray tuchar 53))
                                                                    (Etempvar _s tuint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                    (Sset _s
                                                                    (Ebinop Oadd
                                                                    (Etempvar _s tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _i
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tulong))
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _i tulong)
                                                                    (Etempvar _nseq tulong)
                                                                    tint)
                                                                    Sskip
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'84
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_valid_dict_api__w_code (tarray (tarray tuchar 65536) 3))
                                                                    (Etempvar _ty tuint)
                                                                    (tptr (tarray tuchar 65536)))
                                                                    (tarray tuchar 65536))
                                                                    (Etempvar _i tulong)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_valid_dict_api__need__2 (tarray tuchar 53))
                                                                    (Etempvar _x_valid_dict_api__t'84 tuchar)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 1) tint))))
                                                                    (Sset _i
                                                                    (Ebinop Oadd
                                                                    (Etempvar _i tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'83
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_valid_dict_api__maxlog__1 (tarray tuint 3))
                                                                    (Etempvar _ty tuint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Scall (Some _x_valid_dict_api__t'49)
                                                                    (Evar _choose 
                                                                    (Tfunction
                                                                    (tuint ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                    ((Ebinop Osub
                                                                    (Etempvar _x_valid_dict_api__t'83 tuint)
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tuint) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'82
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_valid_dict_api__maxsym__1 (tarray tuint 3))
                                                                    (Etempvar _ty tuint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Scall None
                                                                    (Evar _fse_pick 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct ___gp_fse_t noattr)) ::
                                                                    tuint ::
                                                                    tuint ::
                                                                    (tptr tuchar) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Ebinop Oadd
                                                                    (Evar _x_valid_dict_api__ntab (tarray (Tstruct ___gp_fse_t noattr) 3))
                                                                    (Etempvar _ty tuint)
                                                                    (tptr (Tstruct ___gp_fse_t noattr))) ::
                                                                    (Ebinop Oadd
                                                                    (Econst_int (Int.repr 5) tint)
                                                                    (Etempvar _x_valid_dict_api__t'49 tuint)
                                                                    tuint) ::
                                                                    (Etempvar _x_valid_dict_api__t'82 tuint) ::
                                                                    (Evar _x_valid_dict_api__need__2 (tarray tuchar 53)) ::
                                                                    nil))))))
                                                                    (Scall None
                                                                    (Evar _fse_copy 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct ___gp_fse_t noattr)) ::
                                                                    (tptr (Tstruct ___gp_fse_t noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Ebinop Oadd
                                                                    (Evar _x_valid_dict_api__ntab (tarray (Tstruct ___gp_fse_t noattr) 3))
                                                                    (Etempvar _ty tuint)
                                                                    (tptr (Tstruct ___gp_fse_t noattr))) ::
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _st__1 (tptr (Tstruct ___gp_wstate_t noattr)))
                                                                    (Tstruct ___gp_wstate_t noattr))
                                                                    _tab
                                                                    (tarray (Tstruct ___gp_fse_t noattr) 3))
                                                                    (Etempvar _ty tuint)
                                                                    (tptr (Tstruct ___gp_fse_t noattr))) ::
                                                                    nil))))))))))))))))))
                                                      (Sset _ty
                                                        (Ebinop Oadd
                                                          (Etempvar _ty tuint)
                                                          (Econst_int (Int.repr 1) tint)
                                                          tuint))))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sset _x_valid_dict_api__t'76
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _mode (tarray tuint 3))
                                                            (Econst_int (Int.repr 0) tint)
                                                            (tptr tuint))
                                                          tuint))
                                                      (Ssequence
                                                        (Sset _x_valid_dict_api__t'77
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _mode (tarray tuint 3))
                                                              (Econst_int (Int.repr 1) tint)
                                                              (tptr tuint))
                                                            tuint))
                                                        (Ssequence
                                                          (Sset _x_valid_dict_api__t'78
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _mode (tarray tuint 3))
                                                                (Econst_int (Int.repr 2) tint)
                                                                (tptr tuint))
                                                              tuint))
                                                          (Scall None
                                                            (Evar _put8 
                                                            (Tfunction
                                                              ((tptr (Tstruct ___gp_out_t noattr)) ::
                                                               tuint :: nil)
                                                              tvoid
                                                              cc_default))
                                                            ((Eaddrof
                                                               (Evar _blk (Tstruct ___gp_out_t noattr))
                                                               (tptr (Tstruct ___gp_out_t noattr))) ::
                                                             (Ebinop Oor
                                                               (Ebinop Oor
                                                                 (Ebinop Oshl
                                                                   (Etempvar _x_valid_dict_api__t'76 tuint)
                                                                   (Econst_int (Int.repr 6) tint)
                                                                   tuint)
                                                                 (Ebinop Oshl
                                                                   (Etempvar _x_valid_dict_api__t'77 tuint)
                                                                   (Econst_int (Int.repr 4) tint)
                                                                   tuint)
                                                                 tuint)
                                                               (Ebinop Oshl
                                                                 (Etempvar _x_valid_dict_api__t'78 tuint)
                                                                 (Econst_int (Int.repr 2) tint)
                                                                 tuint)
                                                               tuint) :: nil)))))
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sset _ty
                                                          (Econst_int (Int.repr 0) tint))
                                                        (Sloop
                                                          (Ssequence
                                                            (Sifthenelse 
                                                              (Ebinop Olt
                                                                (Etempvar _ty tuint)
                                                                (Econst_int (Int.repr 3) tint)
                                                                tint)
                                                              Sskip
                                                              Sbreak)
                                                            (Ssequence
                                                              (Sset _x_valid_dict_api__t'73
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Evar _mode (tarray tuint 3))
                                                                    (Etempvar _ty tuint)
                                                                    (tptr tuint))
                                                                  tuint))
                                                              (Sifthenelse 
                                                                (Ebinop Oeq
                                                                  (Etempvar _x_valid_dict_api__t'73 tuint)
                                                                  (Econst_int (Int.repr 1) tint)
                                                                  tint)
                                                                (Ssequence
                                                                  (Sset _x_valid_dict_api__t'75
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_valid_dict_api__w_code (tarray (tarray tuchar 65536) 3))
                                                                    (Etempvar _ty tuint)
                                                                    (tptr (tarray tuchar 65536)))
                                                                    (tarray tuchar 65536))
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                  (Scall None
                                                                    (Evar _put8 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct ___gp_out_t noattr)) ::
                                                                    tuint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _blk (Tstruct ___gp_out_t noattr))
                                                                    (tptr (Tstruct ___gp_out_t noattr))) ::
                                                                    (Etempvar _x_valid_dict_api__t'75 tuchar) ::
                                                                    nil)))
                                                                (Ssequence
                                                                  (Sset _x_valid_dict_api__t'74
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _mode (tarray tuint 3))
                                                                    (Etempvar _ty tuint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                  (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _x_valid_dict_api__t'74 tuint)
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint)
                                                                    (Scall None
                                                                    (Evar _fse_put_description 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct ___gp_out_t noattr)) ::
                                                                    (tptr (Tstruct ___gp_fse_t noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _blk (Tstruct ___gp_out_t noattr))
                                                                    (tptr (Tstruct ___gp_out_t noattr))) ::
                                                                    (Ebinop Oadd
                                                                    (Evar _x_valid_dict_api__ntab (tarray (Tstruct ___gp_fse_t noattr) 3))
                                                                    (Etempvar _ty tuint)
                                                                    (tptr (Tstruct ___gp_fse_t noattr))) ::
                                                                    nil))
                                                                    Sskip)))))
                                                          (Sset _ty
                                                            (Ebinop Oadd
                                                              (Etempvar _ty tuint)
                                                              (Econst_int (Int.repr 1) tint)
                                                              tuint))))
                                                      (Ssequence
                                                        (Ssequence
                                                          (Sset _ty
                                                            (Econst_int (Int.repr 0) tint))
                                                          (Sloop
                                                            (Ssequence
                                                              (Sifthenelse 
                                                                (Ebinop Olt
                                                                  (Etempvar _ty tuint)
                                                                  (Econst_int (Int.repr 3) tint)
                                                                  tint)
                                                                Sskip
                                                                Sbreak)
                                                              (Scall None
                                                                (Evar _fse_states 
                                                                (Tfunction
                                                                  ((tptr (Tstruct ___gp_fse_t noattr)) ::
                                                                   (tptr tuchar) ::
                                                                   tulong ::
                                                                   (tptr tushort) ::
                                                                   nil) tvoid
                                                                  cc_default))
                                                                ((Ebinop Oadd
                                                                   (Evar _x_valid_dict_api__ntab (tarray (Tstruct ___gp_fse_t noattr) 3))
                                                                   (Etempvar _ty tuint)
                                                                   (tptr (Tstruct ___gp_fse_t noattr))) ::
                                                                 (Ederef
                                                                   (Ebinop Oadd
                                                                    (Evar _x_valid_dict_api__w_code (tarray (tarray tuchar 65536) 3))
                                                                    (Etempvar _ty tuint)
                                                                    (tptr (tarray tuchar 65536)))
                                                                   (tarray tuchar 65536)) ::
                                                                 (Etempvar _nseq tulong) ::
                                                                 (Ederef
                                                                   (Ebinop Oadd
                                                                    (Evar _x_valid_dict_api__w_st (tarray (tarray tushort 65536) 3))
                                                                    (Etempvar _ty tuint)
                                                                    (tptr (tarray tushort 65536)))
                                                                   (tarray tushort 65536)) ::
                                                                 nil)))
                                                            (Sset _ty
                                                              (Ebinop Oadd
                                                                (Etempvar _ty tuint)
                                                                (Econst_int (Int.repr 1) tint)
                                                                tuint))))
                                                        (Ssequence
                                                          (Ssequence
                                                            (Sassign
                                                              (Efield
                                                                (Evar _b (Tstruct ___gp_bits_t noattr))
                                                                _o
                                                                (tptr (Tstruct ___gp_out_t noattr)))
                                                              (Eaddrof
                                                                (Evar _blk (Tstruct ___gp_out_t noattr))
                                                                (tptr (Tstruct ___gp_out_t noattr))))
                                                            (Ssequence
                                                              (Sassign
                                                                (Efield
                                                                  (Evar _b (Tstruct ___gp_bits_t noattr))
                                                                  _acc
                                                                  tulong)
                                                                (Econst_int (Int.repr 0) tint))
                                                              (Ssequence
                                                                (Sassign
                                                                  (Efield
                                                                    (Evar _b (Tstruct ___gp_bits_t noattr))
                                                                    _bits
                                                                    tuint)
                                                                  (Econst_int (Int.repr 0) tint))
                                                                (Ssequence
                                                                  (Sset _q
                                                                    (Etempvar _nseq tulong))
                                                                  (Ssequence
                                                                    (Swhile
                                                                    (Ebinop Ogt
                                                                    (Etempvar _q tulong)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _q
                                                                    (Ebinop Osub
                                                                    (Etempvar _q tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Ebinop Oadd
                                                                    (Etempvar _q tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong)
                                                                    (Etempvar _nseq tulong)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _s
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _s tuint)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tint)
                                                                    Sskip
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Sset _u
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_valid_dict_api__upd (tarray tuint 3))
                                                                    (Etempvar _s tuint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _u tuint)
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint)
                                                                    (Sset _x_valid_dict_api__t'50
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _u tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'50
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint))
                                                                    (Sset _x_valid_dict_api__t'50
                                                                    (Ecast
                                                                    (Etempvar _x_valid_dict_api__t'50 tint)
                                                                    tint)))
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'50
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint))
                                                                    (Sset _x_valid_dict_api__t'50
                                                                    (Ecast
                                                                    (Etempvar _x_valid_dict_api__t'50 tint)
                                                                    tint)))))
                                                                    (Sset _tb
                                                                    (Ebinop Oadd
                                                                    (Evar _x_valid_dict_api__ntab (tarray (Tstruct ___gp_fse_t noattr) 3))
                                                                    (Etempvar _x_valid_dict_api__t'50 tint)
                                                                    (tptr (Tstruct ___gp_fse_t noattr)))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _u tuint)
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint)
                                                                    (Sset _x_valid_dict_api__t'51
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _u tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'51
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint))
                                                                    (Sset _x_valid_dict_api__t'51
                                                                    (Ecast
                                                                    (Etempvar _x_valid_dict_api__t'51 tint)
                                                                    tint)))
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'51
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint))
                                                                    (Sset _x_valid_dict_api__t'51
                                                                    (Ecast
                                                                    (Etempvar _x_valid_dict_api__t'51 tint)
                                                                    tint)))))
                                                                    (Sset _sv
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_valid_dict_api__w_st (tarray (tarray tushort 65536) 3))
                                                                    (Etempvar _x_valid_dict_api__t'51 tint)
                                                                    (tptr (tarray tushort 65536)))
                                                                    (tarray tushort 65536))))
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'68
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _sv (tptr tushort))
                                                                    (Ebinop Oadd
                                                                    (Etempvar _q tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong)
                                                                    (tptr tushort))
                                                                    tushort))
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'69
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _sv (tptr tushort))
                                                                    (Etempvar _q tulong)
                                                                    (tptr tushort))
                                                                    tushort))
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'70
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _tb (tptr (Tstruct ___gp_fse_t noattr)))
                                                                    (Tstruct ___gp_fse_t noattr))
                                                                    _base
                                                                    (tarray tushort 512))
                                                                    (Etempvar _x_valid_dict_api__t'69 tushort)
                                                                    (tptr tushort))
                                                                    tushort))
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'71
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _sv (tptr tushort))
                                                                    (Etempvar _q tulong)
                                                                    (tptr tushort))
                                                                    tushort))
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'72
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _tb (tptr (Tstruct ___gp_fse_t noattr)))
                                                                    (Tstruct ___gp_fse_t noattr))
                                                                    _nb
                                                                    (tarray tuchar 512))
                                                                    (Etempvar _x_valid_dict_api__t'71 tushort)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Scall None
                                                                    (Evar _bits_put 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct ___gp_bits_t noattr)) ::
                                                                    tulong ::
                                                                    tuint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _b (Tstruct ___gp_bits_t noattr))
                                                                    (tptr (Tstruct ___gp_bits_t noattr))) ::
                                                                    (Ebinop Osub
                                                                    (Etempvar _x_valid_dict_api__t'68 tushort)
                                                                    (Etempvar _x_valid_dict_api__t'70 tushort)
                                                                    tint) ::
                                                                    (Etempvar _x_valid_dict_api__t'72 tuchar) ::
                                                                    nil)))))))))))
                                                                    (Sset _s
                                                                    (Ebinop Oadd
                                                                    (Etempvar _s tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint))))
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'65
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_valid_dict_api__w_extra (tarray (tarray tuint 65536) 3))
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr (tarray tuint 65536)))
                                                                    (tarray tuint 65536))
                                                                    (Etempvar _q tulong)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'66
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_valid_dict_api__w_code (tarray (tarray tuchar 65536) 3))
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr (tarray tuchar 65536)))
                                                                    (tarray tuchar 65536))
                                                                    (Etempvar _q tulong)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'67
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_valid_dict_api__W_LL_bits (tarray tuchar 36))
                                                                    (Etempvar _x_valid_dict_api__t'66 tuchar)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Scall None
                                                                    (Evar _bits_put 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct ___gp_bits_t noattr)) ::
                                                                    tulong ::
                                                                    tuint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _b (Tstruct ___gp_bits_t noattr))
                                                                    (tptr (Tstruct ___gp_bits_t noattr))) ::
                                                                    (Etempvar _x_valid_dict_api__t'65 tuint) ::
                                                                    (Etempvar _x_valid_dict_api__t'67 tuchar) ::
                                                                    nil)))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'62
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_valid_dict_api__w_extra (tarray (tarray tuint 65536) 3))
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    (tptr (tarray tuint 65536)))
                                                                    (tarray tuint 65536))
                                                                    (Etempvar _q tulong)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'63
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_valid_dict_api__w_code (tarray (tarray tuchar 65536) 3))
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    (tptr (tarray tuchar 65536)))
                                                                    (tarray tuchar 65536))
                                                                    (Etempvar _q tulong)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'64
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_valid_dict_api__W_ML_bits (tarray tuchar 53))
                                                                    (Etempvar _x_valid_dict_api__t'63 tuchar)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Scall None
                                                                    (Evar _bits_put 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct ___gp_bits_t noattr)) ::
                                                                    tulong ::
                                                                    tuint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _b (Tstruct ___gp_bits_t noattr))
                                                                    (tptr (Tstruct ___gp_bits_t noattr))) ::
                                                                    (Etempvar _x_valid_dict_api__t'62 tuint) ::
                                                                    (Etempvar _x_valid_dict_api__t'64 tuchar) ::
                                                                    nil)))))
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'60
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_valid_dict_api__w_extra (tarray (tarray tuint 65536) 3))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr (tarray tuint 65536)))
                                                                    (tarray tuint 65536))
                                                                    (Etempvar _q tulong)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'61
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_valid_dict_api__w_code (tarray (tarray tuchar 65536) 3))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr (tarray tuchar 65536)))
                                                                    (tarray tuchar 65536))
                                                                    (Etempvar _q tulong)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Scall None
                                                                    (Evar _bits_put 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct ___gp_bits_t noattr)) ::
                                                                    tulong ::
                                                                    tuint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _b (Tstruct ___gp_bits_t noattr))
                                                                    (tptr (Tstruct ___gp_bits_t noattr))) ::
                                                                    (Etempvar _x_valid_dict_api__t'60 tuint) ::
                                                                    (Etempvar _x_valid_dict_api__t'61 tuchar) ::
                                                                    nil)))))))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'58
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_valid_dict_api__w_st (tarray (tarray tushort 65536) 3))
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    (tptr (tarray tushort 65536)))
                                                                    (tarray tushort 65536))
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tushort))
                                                                    tushort))
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'59
                                                                    (Efield
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_valid_dict_api__ntab (tarray (Tstruct ___gp_fse_t noattr) 3))
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    (tptr (Tstruct ___gp_fse_t noattr)))
                                                                    (Tstruct ___gp_fse_t noattr))
                                                                    _log
                                                                    tuint))
                                                                    (Scall None
                                                                    (Evar _bits_put 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct ___gp_bits_t noattr)) ::
                                                                    tulong ::
                                                                    tuint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _b (Tstruct ___gp_bits_t noattr))
                                                                    (tptr (Tstruct ___gp_bits_t noattr))) ::
                                                                    (Etempvar _x_valid_dict_api__t'58 tushort) ::
                                                                    (Etempvar _x_valid_dict_api__t'59 tuint) ::
                                                                    nil))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'56
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_valid_dict_api__w_st (tarray (tarray tushort 65536) 3))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr (tarray tushort 65536)))
                                                                    (tarray tushort 65536))
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tushort))
                                                                    tushort))
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'57
                                                                    (Efield
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_valid_dict_api__ntab (tarray (Tstruct ___gp_fse_t noattr) 3))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr (Tstruct ___gp_fse_t noattr)))
                                                                    (Tstruct ___gp_fse_t noattr))
                                                                    _log
                                                                    tuint))
                                                                    (Scall None
                                                                    (Evar _bits_put 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct ___gp_bits_t noattr)) ::
                                                                    tulong ::
                                                                    tuint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _b (Tstruct ___gp_bits_t noattr))
                                                                    (tptr (Tstruct ___gp_bits_t noattr))) ::
                                                                    (Etempvar _x_valid_dict_api__t'56 tushort) ::
                                                                    (Etempvar _x_valid_dict_api__t'57 tuint) ::
                                                                    nil))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'54
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_valid_dict_api__w_st (tarray (tarray tushort 65536) 3))
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr (tarray tushort 65536)))
                                                                    (tarray tushort 65536))
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tushort))
                                                                    tushort))
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'55
                                                                    (Efield
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_valid_dict_api__ntab (tarray (Tstruct ___gp_fse_t noattr) 3))
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr (Tstruct ___gp_fse_t noattr)))
                                                                    (Tstruct ___gp_fse_t noattr))
                                                                    _log
                                                                    tuint))
                                                                    (Scall None
                                                                    (Evar _bits_put 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct ___gp_bits_t noattr)) ::
                                                                    tulong ::
                                                                    tuint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _b (Tstruct ___gp_bits_t noattr))
                                                                    (tptr (Tstruct ___gp_bits_t noattr))) ::
                                                                    (Etempvar _x_valid_dict_api__t'54 tushort) ::
                                                                    (Etempvar _x_valid_dict_api__t'55 tuint) ::
                                                                    nil))))
                                                                    (Scall None
                                                                    (Evar _bits_end_mark 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct ___gp_bits_t noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _b (Tstruct ___gp_bits_t noattr))
                                                                    (tptr (Tstruct ___gp_bits_t noattr))) ::
                                                                    nil))))))))))
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _ty
                                                                (Econst_int (Int.repr 0) tint))
                                                              (Sloop
                                                                (Ssequence
                                                                  (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _ty tuint)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tint)
                                                                    Sskip
                                                                    Sbreak)
                                                                  (Scall None
                                                                    (Evar _fse_copy 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct ___gp_fse_t noattr)) ::
                                                                    (tptr (Tstruct ___gp_fse_t noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Ebinop Oadd
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _st__1 (tptr (Tstruct ___gp_wstate_t noattr)))
                                                                    (Tstruct ___gp_wstate_t noattr))
                                                                    _tab
                                                                    (tarray (Tstruct ___gp_fse_t noattr) 3))
                                                                    (Etempvar _ty tuint)
                                                                    (tptr (Tstruct ___gp_fse_t noattr))) ::
                                                                    (Ebinop Oadd
                                                                    (Evar _x_valid_dict_api__ntab (tarray (Tstruct ___gp_fse_t noattr) 3))
                                                                    (Etempvar _ty tuint)
                                                                    (tptr (Tstruct ___gp_fse_t noattr))) ::
                                                                    nil)))
                                                                (Sset _ty
                                                                  (Ebinop Oadd
                                                                    (Etempvar _ty tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint))))
                                                            (Sassign
                                                              (Efield
                                                                (Ederef
                                                                  (Etempvar _st__1 (tptr (Tstruct ___gp_wstate_t noattr)))
                                                                  (Tstruct ___gp_wstate_t noattr))
                                                                _have_tab
                                                                tint)
                                                              (Econst_int (Int.repr 1) tint)))))))))))))))
                                  (Ssequence
                                    (Ssequence
                                      (Sset _x_valid_dict_api__t'53
                                        (Efield
                                          (Evar _blk (Tstruct ___gp_out_t noattr))
                                          _n tulong))
                                      (Scall None
                                        (Evar _gp_assume (Tfunction
                                                           (tint :: nil)
                                                           tvoid cc_default))
                                        ((Ebinop Ole (Etempvar _x_valid_dict_api__t'53 tulong)
                                           (Etempvar _bmax tulong) tint) ::
                                         nil)))
                                    (Ssequence
                                      (Sset _x_valid_dict_api__t'52
                                        (Efield
                                          (Evar _blk (Tstruct ___gp_out_t noattr))
                                          _n tulong))
                                      (Scall None
                                        (Evar _put_bytes (Tfunction
                                                           ((tptr (Tstruct ___gp_out_t noattr)) ::
                                                            (tptr tuchar) ::
                                                            tulong :: nil)
                                                           tvoid cc_default))
                                        ((Etempvar _o (tptr (Tstruct ___gp_out_t noattr))) ::
                                         (Evar _x_valid_dict_api__blk_buf (tarray tuchar 135168)) ::
                                         (Etempvar _x_valid_dict_api__t'52 tulong) :: nil)))))))))))))))))))))
|}.

Definition v_x_valid_dict_api__hdr := {|
  gvar_info := (tarray tuchar 32);
  gvar_init := (Init_space 32 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_w_frame := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_x_valid_dict_api__sr, (tptr (Tstruct ___gp_wseries_t noattr))) ::
                (_o, (tptr (Tstruct ___gp_out_t noattr))) ::
                (_fi, (tptr (Tstruct ___gp_winfo_t noattr))) ::
                (_n, tulong) ::
                (_d, (tptr (Tstruct ___gp_wdict_t noattr))) :: nil);
  fn_vars := ((_st__1, (Tstruct ___gp_wstate_t noattr)) :: (_hn, tulong) ::
              (_h, (Tstruct ___gp_out_t noattr)) ::
              (_forms, (tarray tuint 4)) :: (_forms__1, (tarray tuint 4)) ::
              (_opts, (tarray tuint 4)) :: nil);
  fn_temps := ((_dictn, tulong) :: (_left, tulong) :: (_i, tulong) ::
               (_window, tulong) :: (_bmax, tulong) :: (_fcsflag, tuint) ::
               (_didflag, tuint) :: (_nblocks, tuint) :: (_single, tuint) ::
               (_e, tuint) :: (_m, tuint) :: (_nf, tuint) ::
               (_nf__1, tuint) :: (_emin, tuint) :: (_no, tuint) ::
               (_id, tuint) :: (_t__1, tulong) :: (_start, tulong) ::
               (_type, tuint) :: (_last, tuint) :: (_c, tuchar) ::
               (_c__1, tuchar) :: (_bsize, tulong) :: (_hv, tulong) ::
               (_x_valid_dict_api__t'42, tulong) :: (_x_valid_dict_api__t'41, tulong) :: (_x_valid_dict_api__t'40, tulong) ::
               (_x_valid_dict_api__t'39, tuint) :: (_x_valid_dict_api__t'38, tulong) :: (_x_valid_dict_api__t'37, tuint) ::
               (_x_valid_dict_api__t'36, tuint) :: (_x_valid_dict_api__t'35, tint) :: (_x_valid_dict_api__t'34, tuint) ::
               (_x_valid_dict_api__t'33, tulong) :: (_x_valid_dict_api__t'32, tulong) :: (_x_valid_dict_api__t'31, tulong) ::
               (_x_valid_dict_api__t'30, tint) :: (_x_valid_dict_api__t'29, tint) :: (_x_valid_dict_api__t'28, tint) ::
               (_x_valid_dict_api__t'27, tuint) :: (_x_valid_dict_api__t'26, tuint) :: (_x_valid_dict_api__t'25, tuint) ::
               (_x_valid_dict_api__t'24, tuint) :: (_x_valid_dict_api__t'23, tuint) :: (_x_valid_dict_api__t'22, tuint) ::
               (_x_valid_dict_api__t'21, tuint) :: (_x_valid_dict_api__t'20, tuint) :: (_x_valid_dict_api__t'19, tuint) ::
               (_x_valid_dict_api__t'18, tuint) :: (_x_valid_dict_api__t'17, tint) :: (_x_valid_dict_api__t'16, tuint) ::
               (_x_valid_dict_api__t'15, tuint) :: (_x_valid_dict_api__t'14, tuint) :: (_x_valid_dict_api__t'13, tint) ::
               (_x_valid_dict_api__t'12, tuint) :: (_x_valid_dict_api__t'11, tuint) :: (_x_valid_dict_api__t'10, tuint) ::
               (_x_valid_dict_api__t'9, tuint) :: (_x_valid_dict_api__t'8, tuint) :: (_x_valid_dict_api__t'7, tint) ::
               (_x_valid_dict_api__t'6, tuint) :: (_x_valid_dict_api__t'5, tuint) :: (_x_valid_dict_api__t'4, tuint) ::
               (_x_valid_dict_api__t'3, tuint) :: (_x_valid_dict_api__t'2, tulong) :: (_x_valid_dict_api__t'1, tint) ::
               (_x_valid_dict_api__t'60, tulong) :: (_x_valid_dict_api__t'59, tulong) :: (_x_valid_dict_api__t'58, tuint) ::
               (_x_valid_dict_api__t'57, tuint) :: (_x_valid_dict_api__t'56, tuint) :: (_x_valid_dict_api__t'55, tuint) ::
               (_x_valid_dict_api__t'54, tulong) :: (_x_valid_dict_api__t'53, tulong) :: (_x_valid_dict_api__t'52, tuchar) ::
               (_x_valid_dict_api__t'51, (tptr tuchar)) :: (_x_valid_dict_api__t'50, tulong) ::
               (_x_valid_dict_api__t'49, (tptr tuchar)) :: (_x_valid_dict_api__t'48, (tptr tuchar)) ::
               (_x_valid_dict_api__t'47, (tptr tuchar)) :: (_x_valid_dict_api__t'46, tulong) ::
               (_x_valid_dict_api__t'45, tuchar) :: (_x_valid_dict_api__t'44, tulong) :: (_x_valid_dict_api__t'43, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sifthenelse (Etempvar _d (tptr (Tstruct ___gp_wdict_t noattr)))
        (Ssequence
          (Sset _x_valid_dict_api__t'60
            (Efield
              (Ederef (Etempvar _d (tptr (Tstruct ___gp_wdict_t noattr)))
                (Tstruct ___gp_wdict_t noattr)) _content_n tulong))
          (Sset _x_valid_dict_api__t'1
            (Ecast
              (Ebinop Ogt (Etempvar _x_valid_dict_api__t'60 tulong)
                (Econst_int (Int.repr 0) tint) tint) tbool)))
        (Sset _x_valid_dict_api__t'1 (Econst_int (Int.repr 0) tint)))
      (Sifthenelse (Etempvar _x_valid_dict_api__t'1 tint)
        (Ssequence
          (Sset _x_valid_dict_api__t'59
            (Efield
              (Ederef (Etempvar _d (tptr (Tstruct ___gp_wdict_t noattr)))
                (Tstruct ___gp_wdict_t noattr)) _content_n tulong))
          (Sset _x_valid_dict_api__t'2 (Ecast (Etempvar _x_valid_dict_api__t'59 tulong) tulong)))
        (Sset _x_valid_dict_api__t'2 (Ecast (Econst_int (Int.repr 0) tint) tulong))))
    (Sset _dictn (Etempvar _x_valid_dict_api__t'2 tulong)))
  (Ssequence
    (Sset _left (Etempvar _n tulong))
    (Ssequence
      (Sset _nblocks (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Sset _e (Econst_int (Int.repr 0) tint))
        (Ssequence
          (Sset _m (Econst_int (Int.repr 0) tint))
          (Ssequence
            (Sassign
              (Efield (Evar _h (Tstruct ___gp_out_t noattr)) _p
                (tptr tuchar)) (Evar _x_valid_dict_api__hdr (tarray tuchar 32)))
            (Ssequence
              (Sassign
                (Efield (Evar _h (Tstruct ___gp_out_t noattr)) _n tulong)
                (Econst_int (Int.repr 0) tint))
              (Ssequence
                (Sassign
                  (Efield (Evar _h (Tstruct ___gp_out_t noattr)) _cap tulong)
                  (Esizeof (tarray tuchar 32) tulong))
                (Ssequence
                  (Ssequence
                    (Scall (Some _x_valid_dict_api__t'3)
                      (Evar _choose (Tfunction (tuint :: nil) tuint
                                      cc_default))
                      ((Econst_int (Int.repr 2) tint) :: nil))
                    (Sset _single (Etempvar _x_valid_dict_api__t'3 tuint)))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _x_valid_dict_api__t'4)
                        (Evar _choose (Tfunction (tuint :: nil) tuint
                                        cc_default))
                        ((Econst_int (Int.repr 2) tint) :: nil))
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _fi (tptr (Tstruct ___gp_winfo_t noattr)))
                            (Tstruct ___gp_winfo_t noattr)) _checksum tuint)
                        (Etempvar _x_valid_dict_api__t'4 tuint)))
                    (Ssequence
                      (Sifthenelse (Etempvar _single tuint)
                        (Ssequence
                          (Sset _nf (Econst_int (Int.repr 0) tint))
                          (Ssequence
                            (Sifthenelse (Ebinop Ole (Etempvar _n tulong)
                                           (Econst_int (Int.repr 255) tint)
                                           tint)
                              (Ssequence
                                (Ssequence
                                  (Sset _x_valid_dict_api__t'5 (Etempvar _nf tuint))
                                  (Sset _nf
                                    (Ebinop Oadd (Etempvar _x_valid_dict_api__t'5 tuint)
                                      (Econst_int (Int.repr 1) tint) tuint)))
                                (Sassign
                                  (Ederef
                                    (Ebinop Oadd
                                      (Evar _forms (tarray tuint 4))
                                      (Etempvar _x_valid_dict_api__t'5 tuint) (tptr tuint))
                                    tuint) (Econst_int (Int.repr 0) tint)))
                              Sskip)
                            (Ssequence
                              (Ssequence
                                (Sifthenelse (Ebinop Oge (Etempvar _n tulong)
                                               (Econst_int (Int.repr 256) tint)
                                               tint)
                                  (Sset _x_valid_dict_api__t'7
                                    (Ecast
                                      (Ebinop Ole (Etempvar _n tulong)
                                        (Econst_int (Int.repr 65791) tint)
                                        tint) tbool))
                                  (Sset _x_valid_dict_api__t'7 (Econst_int (Int.repr 0) tint)))
                                (Sifthenelse (Etempvar _x_valid_dict_api__t'7 tint)
                                  (Ssequence
                                    (Ssequence
                                      (Sset _x_valid_dict_api__t'6 (Etempvar _nf tuint))
                                      (Sset _nf
                                        (Ebinop Oadd (Etempvar _x_valid_dict_api__t'6 tuint)
                                          (Econst_int (Int.repr 1) tint)
                                          tuint)))
                                    (Sassign
                                      (Ederef
                                        (Ebinop Oadd
                                          (Evar _forms (tarray tuint 4))
                                          (Etempvar _x_valid_dict_api__t'6 tuint) (tptr tuint))
                                        tuint)
                                      (Econst_int (Int.repr 1) tint)))
                                  Sskip))
                              (Ssequence
                                (Ssequence
                                  (Ssequence
                                    (Sset _x_valid_dict_api__t'8 (Etempvar _nf tuint))
                                    (Sset _nf
                                      (Ebinop Oadd (Etempvar _x_valid_dict_api__t'8 tuint)
                                        (Econst_int (Int.repr 1) tint) tuint)))
                                  (Sassign
                                    (Ederef
                                      (Ebinop Oadd
                                        (Evar _forms (tarray tuint 4))
                                        (Etempvar _x_valid_dict_api__t'8 tuint) (tptr tuint))
                                      tuint) (Econst_int (Int.repr 2) tint)))
                                (Ssequence
                                  (Ssequence
                                    (Ssequence
                                      (Sset _x_valid_dict_api__t'9 (Etempvar _nf tuint))
                                      (Sset _nf
                                        (Ebinop Oadd (Etempvar _x_valid_dict_api__t'9 tuint)
                                          (Econst_int (Int.repr 1) tint)
                                          tuint)))
                                    (Sassign
                                      (Ederef
                                        (Ebinop Oadd
                                          (Evar _forms (tarray tuint 4))
                                          (Etempvar _x_valid_dict_api__t'9 tuint) (tptr tuint))
                                        tuint)
                                      (Econst_int (Int.repr 3) tint)))
                                  (Ssequence
                                    (Ssequence
                                      (Scall (Some _x_valid_dict_api__t'10)
                                        (Evar _choose (Tfunction
                                                        (tuint :: nil) tuint
                                                        cc_default))
                                        ((Etempvar _nf tuint) :: nil))
                                      (Sset _fcsflag
                                        (Ederef
                                          (Ebinop Oadd
                                            (Evar _forms (tarray tuint 4))
                                            (Etempvar _x_valid_dict_api__t'10 tuint)
                                            (tptr tuint)) tuint)))
                                    (Ssequence
                                      (Sset _window (Etempvar _n tulong))
                                      (Sassign
                                        (Efield
                                          (Ederef
                                            (Etempvar _fi (tptr (Tstruct ___gp_winfo_t noattr)))
                                            (Tstruct ___gp_winfo_t noattr))
                                          _window_log tuint)
                                        (Econst_int (Int.repr 0) tint)))))))))
                        (Ssequence
                          (Sset _nf__1 (Econst_int (Int.repr 0) tint))
                          (Ssequence
                            (Sset _emin (Econst_int (Int.repr 0) tint))
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Sset _x_valid_dict_api__t'11 (Etempvar _nf__1 tuint))
                                  (Sset _nf__1
                                    (Ebinop Oadd (Etempvar _x_valid_dict_api__t'11 tuint)
                                      (Econst_int (Int.repr 1) tint) tuint)))
                                (Sassign
                                  (Ederef
                                    (Ebinop Oadd
                                      (Evar _forms__1 (tarray tuint 4))
                                      (Etempvar _x_valid_dict_api__t'11 tuint) (tptr tuint))
                                    tuint) (Econst_int (Int.repr 0) tint)))
                              (Ssequence
                                (Ssequence
                                  (Sifthenelse (Ebinop Oge
                                                 (Etempvar _n tulong)
                                                 (Econst_int (Int.repr 256) tint)
                                                 tint)
                                    (Sset _x_valid_dict_api__t'13
                                      (Ecast
                                        (Ebinop Ole (Etempvar _n tulong)
                                          (Econst_int (Int.repr 65791) tint)
                                          tint) tbool))
                                    (Sset _x_valid_dict_api__t'13
                                      (Econst_int (Int.repr 0) tint)))
                                  (Sifthenelse (Etempvar _x_valid_dict_api__t'13 tint)
                                    (Ssequence
                                      (Ssequence
                                        (Sset _x_valid_dict_api__t'12 (Etempvar _nf__1 tuint))
                                        (Sset _nf__1
                                          (Ebinop Oadd (Etempvar _x_valid_dict_api__t'12 tuint)
                                            (Econst_int (Int.repr 1) tint)
                                            tuint)))
                                      (Sassign
                                        (Ederef
                                          (Ebinop Oadd
                                            (Evar _forms__1 (tarray tuint 4))
                                            (Etempvar _x_valid_dict_api__t'12 tuint)
                                            (tptr tuint)) tuint)
                                        (Econst_int (Int.repr 1) tint)))
                                    Sskip))
                                (Ssequence
                                  (Ssequence
                                    (Ssequence
                                      (Sset _x_valid_dict_api__t'14 (Etempvar _nf__1 tuint))
                                      (Sset _nf__1
                                        (Ebinop Oadd (Etempvar _x_valid_dict_api__t'14 tuint)
                                          (Econst_int (Int.repr 1) tint)
                                          tuint)))
                                    (Sassign
                                      (Ederef
                                        (Ebinop Oadd
                                          (Evar _forms__1 (tarray tuint 4))
                                          (Etempvar _x_valid_dict_api__t'14 tuint)
                                          (tptr tuint)) tuint)
                                      (Econst_int (Int.repr 2) tint)))
                                  (Ssequence
                                    (Ssequence
                                      (Ssequence
                                        (Sset _x_valid_dict_api__t'15 (Etempvar _nf__1 tuint))
                                        (Sset _nf__1
                                          (Ebinop Oadd (Etempvar _x_valid_dict_api__t'15 tuint)
                                            (Econst_int (Int.repr 1) tint)
                                            tuint)))
                                      (Sassign
                                        (Ederef
                                          (Ebinop Oadd
                                            (Evar _forms__1 (tarray tuint 4))
                                            (Etempvar _x_valid_dict_api__t'15 tuint)
                                            (tptr tuint)) tuint)
                                        (Econst_int (Int.repr 3) tint)))
                                    (Ssequence
                                      (Ssequence
                                        (Scall (Some _x_valid_dict_api__t'16)
                                          (Evar _choose (Tfunction
                                                          (tuint :: nil)
                                                          tuint cc_default))
                                          ((Etempvar _nf__1 tuint) :: nil))
                                        (Sset _fcsflag
                                          (Ederef
                                            (Ebinop Oadd
                                              (Evar _forms__1 (tarray tuint 4))
                                              (Etempvar _x_valid_dict_api__t'16 tuint)
                                              (tptr tuint)) tuint)))
                                      (Ssequence
                                        (Sloop
                                          (Ssequence
                                            (Ssequence
                                              (Sifthenelse (Ebinop Olt
                                                             (Etempvar _emin tuint)
                                                             (Econst_int (Int.repr 7) tint)
                                                             tint)
                                                (Sset _x_valid_dict_api__t'17
                                                  (Ecast
                                                    (Ebinop Olt
                                                      (Ebinop Oshl
                                                        (Ecast
                                                          (Econst_int (Int.repr 6) tint)
                                                          tulong)
                                                        (Ebinop Oadd
                                                          (Econst_int (Int.repr 10) tint)
                                                          (Etempvar _emin tuint)
                                                          tuint) tulong)
                                                      (Etempvar _n tulong)
                                                      tint) tbool))
                                                (Sset _x_valid_dict_api__t'17
                                                  (Econst_int (Int.repr 0) tint)))
                                              (Sifthenelse (Etempvar _x_valid_dict_api__t'17 tint)
                                                Sskip
                                                Sbreak))
                                            (Sset _emin
                                              (Ebinop Oadd
                                                (Etempvar _emin tuint)
                                                (Econst_int (Int.repr 1) tint)
                                                tuint)))
                                          Sskip)
                                        (Ssequence
                                          (Ssequence
                                            (Scall (Some _x_valid_dict_api__t'18)
                                              (Evar _choose (Tfunction
                                                              (tuint :: nil)
                                                              tuint
                                                              cc_default))
                                              ((Ebinop Osub
                                                 (Econst_int (Int.repr 32) tint)
                                                 (Etempvar _emin tuint)
                                                 tuint) :: nil))
                                            (Sset _e
                                              (Ebinop Oadd
                                                (Etempvar _emin tuint)
                                                (Etempvar _x_valid_dict_api__t'18 tuint) tuint)))
                                          (Ssequence
                                            (Ssequence
                                              (Scall (Some _x_valid_dict_api__t'19)
                                                (Evar _choose (Tfunction
                                                                (tuint ::
                                                                 nil) tuint
                                                                cc_default))
                                                ((Econst_int (Int.repr 8) tint) ::
                                                 nil))
                                              (Sset _m
                                                (Etempvar _x_valid_dict_api__t'19 tuint)))
                                            (Ssequence
                                              (Sset _window
                                                (Ebinop Oadd
                                                  (Ebinop Oshl
                                                    (Econst_long (Int64.repr 1) tulong)
                                                    (Ebinop Oadd
                                                      (Econst_int (Int.repr 10) tint)
                                                      (Etempvar _e tuint)
                                                      tuint) tulong)
                                                  (Ebinop Omul
                                                    (Ebinop Odiv
                                                      (Ebinop Oshl
                                                        (Econst_long (Int64.repr 1) tulong)
                                                        (Ebinop Oadd
                                                          (Econst_int (Int.repr 10) tint)
                                                          (Etempvar _e tuint)
                                                          tuint) tulong)
                                                      (Econst_int (Int.repr 8) tint)
                                                      tulong)
                                                    (Etempvar _m tuint)
                                                    tulong) tulong))
                                              (Sassign
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _fi (tptr (Tstruct ___gp_winfo_t noattr)))
                                                    (Tstruct ___gp_winfo_t noattr))
                                                  _window_log tuint)
                                                (Ebinop Oadd
                                                  (Econst_int (Int.repr 10) tint)
                                                  (Etempvar _e tuint) tuint))))))))))))))
                      (Ssequence
                        (Sassign
                          (Efield
                            (Ederef
                              (Etempvar _fi (tptr (Tstruct ___gp_winfo_t noattr)))
                              (Tstruct ___gp_winfo_t noattr)) _window tulong)
                          (Etempvar _window tulong))
                        (Ssequence
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _fi (tptr (Tstruct ___gp_winfo_t noattr)))
                                (Tstruct ___gp_winfo_t noattr)) _single tint)
                            (Ecast (Etempvar _single tuint) tint))
                          (Ssequence
                            (Ssequence
                              (Sset _no (Econst_int (Int.repr 0) tint))
                              (Ssequence
                                (Ssequence
                                  (Sifthenelse (Etempvar _d (tptr (Tstruct ___gp_wdict_t noattr)))
                                    (Ssequence
                                      (Sset _x_valid_dict_api__t'58
                                        (Efield
                                          (Ederef
                                            (Etempvar _d (tptr (Tstruct ___gp_wdict_t noattr)))
                                            (Tstruct ___gp_wdict_t noattr))
                                          _id tuint))
                                      (Sset _x_valid_dict_api__t'20
                                        (Ecast (Etempvar _x_valid_dict_api__t'58 tuint) tuint)))
                                    (Sset _x_valid_dict_api__t'20
                                      (Ecast (Econst_int (Int.repr 0) tint)
                                        tuint)))
                                  (Sset _id (Etempvar _x_valid_dict_api__t'20 tuint)))
                                (Ssequence
                                  (Ssequence
                                    (Ssequence
                                      (Sset _x_valid_dict_api__t'21 (Etempvar _no tuint))
                                      (Sset _no
                                        (Ebinop Oadd (Etempvar _x_valid_dict_api__t'21 tuint)
                                          (Econst_int (Int.repr 1) tint)
                                          tuint)))
                                    (Sassign
                                      (Ederef
                                        (Ebinop Oadd
                                          (Evar _opts (tarray tuint 4))
                                          (Etempvar _x_valid_dict_api__t'21 tuint)
                                          (tptr tuint)) tuint)
                                      (Econst_int (Int.repr 0) tint)))
                                  (Ssequence
                                    (Sifthenelse (Ebinop Ole
                                                   (Etempvar _id tuint)
                                                   (Econst_int (Int.repr 255) tint)
                                                   tint)
                                      (Ssequence
                                        (Ssequence
                                          (Sset _x_valid_dict_api__t'22 (Etempvar _no tuint))
                                          (Sset _no
                                            (Ebinop Oadd
                                              (Etempvar _x_valid_dict_api__t'22 tuint)
                                              (Econst_int (Int.repr 1) tint)
                                              tuint)))
                                        (Sassign
                                          (Ederef
                                            (Ebinop Oadd
                                              (Evar _opts (tarray tuint 4))
                                              (Etempvar _x_valid_dict_api__t'22 tuint)
                                              (tptr tuint)) tuint)
                                          (Econst_int (Int.repr 1) tint)))
                                      Sskip)
                                    (Ssequence
                                      (Sifthenelse (Ebinop Ole
                                                     (Etempvar _id tuint)
                                                     (Econst_int (Int.repr 65535) tint)
                                                     tint)
                                        (Ssequence
                                          (Ssequence
                                            (Sset _x_valid_dict_api__t'23 (Etempvar _no tuint))
                                            (Sset _no
                                              (Ebinop Oadd
                                                (Etempvar _x_valid_dict_api__t'23 tuint)
                                                (Econst_int (Int.repr 1) tint)
                                                tuint)))
                                          (Sassign
                                            (Ederef
                                              (Ebinop Oadd
                                                (Evar _opts (tarray tuint 4))
                                                (Etempvar _x_valid_dict_api__t'23 tuint)
                                                (tptr tuint)) tuint)
                                            (Econst_int (Int.repr 2) tint)))
                                        Sskip)
                                      (Ssequence
                                        (Ssequence
                                          (Ssequence
                                            (Sset _x_valid_dict_api__t'24 (Etempvar _no tuint))
                                            (Sset _no
                                              (Ebinop Oadd
                                                (Etempvar _x_valid_dict_api__t'24 tuint)
                                                (Econst_int (Int.repr 1) tint)
                                                tuint)))
                                          (Sassign
                                            (Ederef
                                              (Ebinop Oadd
                                                (Evar _opts (tarray tuint 4))
                                                (Etempvar _x_valid_dict_api__t'24 tuint)
                                                (tptr tuint)) tuint)
                                            (Econst_int (Int.repr 3) tint)))
                                        (Ssequence
                                          (Ssequence
                                            (Scall (Some _x_valid_dict_api__t'25)
                                              (Evar _choose (Tfunction
                                                              (tuint :: nil)
                                                              tuint
                                                              cc_default))
                                              ((Etempvar _no tuint) :: nil))
                                            (Sset _didflag
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Evar _opts (tarray tuint 4))
                                                  (Etempvar _x_valid_dict_api__t'25 tuint)
                                                  (tptr tuint)) tuint)))
                                          (Ssequence
                                            (Sifthenelse (Ebinop Oeq
                                                           (Etempvar _didflag tuint)
                                                           (Econst_int (Int.repr 0) tint)
                                                           tint)
                                              (Sset _x_valid_dict_api__t'26
                                                (Ecast
                                                  (Econst_int (Int.repr 0) tint)
                                                  tuint))
                                              (Ssequence
                                                (Scall (Some _x_valid_dict_api__t'27)
                                                  (Evar _choose (Tfunction
                                                                  (tuint ::
                                                                   nil) tuint
                                                                  cc_default))
                                                  ((Econst_int (Int.repr 2) tint) ::
                                                   nil))
                                                (Sifthenelse (Etempvar _x_valid_dict_api__t'27 tuint)
                                                  (Ssequence
                                                    (Sset _x_valid_dict_api__t'26
                                                      (Ecast
                                                        (Etempvar _id tuint)
                                                        tuint))
                                                    (Sset _x_valid_dict_api__t'26
                                                      (Ecast
                                                        (Etempvar _x_valid_dict_api__t'26 tuint)
                                                        tuint)))
                                                  (Ssequence
                                                    (Sset _x_valid_dict_api__t'26
                                                      (Ecast
                                                        (Econst_int (Int.repr 0) tint)
                                                        tuint))
                                                    (Sset _x_valid_dict_api__t'26
                                                      (Ecast
                                                        (Etempvar _x_valid_dict_api__t'26 tuint)
                                                        tuint))))))
                                            (Sassign
                                              (Efield
                                                (Ederef
                                                  (Etempvar _fi (tptr (Tstruct ___gp_winfo_t noattr)))
                                                  (Tstruct ___gp_winfo_t noattr))
                                                _did tuint)
                                              (Etempvar _x_valid_dict_api__t'26 tuint))))))))))
                            (Ssequence
                              (Ssequence
                                (Sifthenelse (Ebinop Oeq
                                               (Etempvar _didflag tuint)
                                               (Econst_int (Int.repr 0) tint)
                                               tint)
                                  (Sset _x_valid_dict_api__t'28
                                    (Ecast (Econst_int (Int.repr 0) tint)
                                      tint))
                                  (Sifthenelse (Ebinop Oeq
                                                 (Etempvar _didflag tuint)
                                                 (Econst_int (Int.repr 1) tint)
                                                 tint)
                                    (Ssequence
                                      (Sset _x_valid_dict_api__t'28
                                        (Ecast (Econst_int (Int.repr 1) tint)
                                          tint))
                                      (Sset _x_valid_dict_api__t'28
                                        (Ecast (Etempvar _x_valid_dict_api__t'28 tint) tint)))
                                    (Sifthenelse (Ebinop Oeq
                                                   (Etempvar _didflag tuint)
                                                   (Econst_int (Int.repr 2) tint)
                                                   tint)
                                      (Ssequence
                                        (Ssequence
                                          (Sset _x_valid_dict_api__t'28
                                            (Ecast
                                              (Econst_int (Int.repr 2) tint)
                                              tint))
                                          (Sset _x_valid_dict_api__t'28
                                            (Ecast (Etempvar _x_valid_dict_api__t'28 tint)
                                              tint)))
                                        (Sset _x_valid_dict_api__t'28
                                          (Ecast (Etempvar _x_valid_dict_api__t'28 tint) tint)))
                                      (Ssequence
                                        (Ssequence
                                          (Sset _x_valid_dict_api__t'28
                                            (Ecast
                                              (Econst_int (Int.repr 4) tint)
                                              tint))
                                          (Sset _x_valid_dict_api__t'28
                                            (Ecast (Etempvar _x_valid_dict_api__t'28 tint)
                                              tint)))
                                        (Sset _x_valid_dict_api__t'28
                                          (Ecast (Etempvar _x_valid_dict_api__t'28 tint) tint))))))
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _fi (tptr (Tstruct ___gp_winfo_t noattr)))
                                      (Tstruct ___gp_winfo_t noattr))
                                    _did_size tuint) (Etempvar _x_valid_dict_api__t'28 tint)))
                              (Ssequence
                                (Scall None
                                  (Evar _put_le (Tfunction
                                                  ((tptr (Tstruct ___gp_out_t noattr)) ::
                                                   tulong :: tuint :: nil)
                                                  tvoid cc_default))
                                  ((Eaddrof
                                     (Evar _h (Tstruct ___gp_out_t noattr))
                                     (tptr (Tstruct ___gp_out_t noattr))) ::
                                   (Econst_int (Int.repr (-47205080)) tuint) ::
                                   (Econst_int (Int.repr 4) tint) :: nil))
                                (Ssequence
                                  (Ssequence
                                    (Sset _x_valid_dict_api__t'57
                                      (Efield
                                        (Ederef
                                          (Etempvar _fi (tptr (Tstruct ___gp_winfo_t noattr)))
                                          (Tstruct ___gp_winfo_t noattr))
                                        _checksum tuint))
                                    (Scall None
                                      (Evar _put8 (Tfunction
                                                    ((tptr (Tstruct ___gp_out_t noattr)) ::
                                                     tuint :: nil) tvoid
                                                    cc_default))
                                      ((Eaddrof
                                         (Evar _h (Tstruct ___gp_out_t noattr))
                                         (tptr (Tstruct ___gp_out_t noattr))) ::
                                       (Ebinop Oor
                                         (Ebinop Oor
                                           (Ebinop Oor
                                             (Ebinop Oshl
                                               (Etempvar _fcsflag tuint)
                                               (Econst_int (Int.repr 6) tint)
                                               tuint)
                                             (Ebinop Oshl
                                               (Etempvar _single tuint)
                                               (Econst_int (Int.repr 5) tint)
                                               tuint) tuint)
                                           (Ebinop Oshl
                                             (Etempvar _x_valid_dict_api__t'57 tuint)
                                             (Econst_int (Int.repr 2) tint)
                                             tuint) tuint)
                                         (Etempvar _didflag tuint) tuint) ::
                                       nil)))
                                  (Ssequence
                                    (Sifthenelse (Eunop Onotbool
                                                   (Etempvar _single tuint)
                                                   tint)
                                      (Scall None
                                        (Evar _put8 (Tfunction
                                                      ((tptr (Tstruct ___gp_out_t noattr)) ::
                                                       tuint :: nil) tvoid
                                                      cc_default))
                                        ((Eaddrof
                                           (Evar _h (Tstruct ___gp_out_t noattr))
                                           (tptr (Tstruct ___gp_out_t noattr))) ::
                                         (Ebinop Oor
                                           (Ebinop Oshl (Etempvar _e tuint)
                                             (Econst_int (Int.repr 3) tint)
                                             tuint) (Etempvar _m tuint)
                                           tuint) :: nil))
                                      Sskip)
                                    (Ssequence
                                      (Ssequence
                                        (Sset _x_valid_dict_api__t'55
                                          (Efield
                                            (Ederef
                                              (Etempvar _fi (tptr (Tstruct ___gp_winfo_t noattr)))
                                              (Tstruct ___gp_winfo_t noattr))
                                            _did tuint))
                                        (Ssequence
                                          (Sset _x_valid_dict_api__t'56
                                            (Efield
                                              (Ederef
                                                (Etempvar _fi (tptr (Tstruct ___gp_winfo_t noattr)))
                                                (Tstruct ___gp_winfo_t noattr))
                                              _did_size tuint))
                                          (Scall None
                                            (Evar _put_le (Tfunction
                                                            ((tptr (Tstruct ___gp_out_t noattr)) ::
                                                             tulong ::
                                                             tuint :: nil)
                                                            tvoid cc_default))
                                            ((Eaddrof
                                               (Evar _h (Tstruct ___gp_out_t noattr))
                                               (tptr (Tstruct ___gp_out_t noattr))) ::
                                             (Etempvar _x_valid_dict_api__t'55 tuint) ::
                                             (Etempvar _x_valid_dict_api__t'56 tuint) :: nil))))
                                      (Ssequence
                                        (Ssequence
                                          (Sifthenelse (Etempvar _single tuint)
                                            (Sset _x_valid_dict_api__t'29
                                              (Econst_int (Int.repr 1) tint))
                                            (Sset _x_valid_dict_api__t'29
                                              (Ecast
                                                (Ebinop One
                                                  (Etempvar _fcsflag tuint)
                                                  (Econst_int (Int.repr 0) tint)
                                                  tint) tbool)))
                                          (Sassign
                                            (Efield
                                              (Ederef
                                                (Etempvar _fi (tptr (Tstruct ___gp_winfo_t noattr)))
                                                (Tstruct ___gp_winfo_t noattr))
                                              _fcs_present tint)
                                            (Etempvar _x_valid_dict_api__t'29 tint)))
                                        (Ssequence
                                          (Sassign
                                            (Efield
                                              (Ederef
                                                (Etempvar _fi (tptr (Tstruct ___gp_winfo_t noattr)))
                                                (Tstruct ___gp_winfo_t noattr))
                                              _fcs tulong)
                                            (Etempvar _n tulong))
                                          (Ssequence
                                            (Ssequence
                                              (Sifthenelse (Ebinop Oeq
                                                             (Etempvar _fcsflag tuint)
                                                             (Econst_int (Int.repr 0) tint)
                                                             tint)
                                                (Sset _x_valid_dict_api__t'30
                                                  (Ecast
                                                    (Etempvar _single tuint)
                                                    tbool))
                                                (Sset _x_valid_dict_api__t'30
                                                  (Econst_int (Int.repr 0) tint)))
                                              (Sifthenelse (Etempvar _x_valid_dict_api__t'30 tint)
                                                (Scall None
                                                  (Evar _put8 (Tfunction
                                                                ((tptr (Tstruct ___gp_out_t noattr)) ::
                                                                 tuint ::
                                                                 nil) tvoid
                                                                cc_default))
                                                  ((Eaddrof
                                                     (Evar _h (Tstruct ___gp_out_t noattr))
                                                     (tptr (Tstruct ___gp_out_t noattr))) ::
                                                   (Ecast
                                                     (Etempvar _n tulong)
                                                     tuint) :: nil))
                                                (Sifthenelse (Ebinop Oeq
                                                               (Etempvar _fcsflag tuint)
                                                               (Econst_int (Int.repr 1) tint)
                                                               tint)
                                                  (Scall None
                                                    (Evar _put_le (Tfunction
                                                                    ((tptr (Tstruct ___gp_out_t noattr)) ::
                                                                    tulong ::
                                                                    tuint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                    ((Eaddrof
                                                       (Evar _h (Tstruct ___gp_out_t noattr))
                                                       (tptr (Tstruct ___gp_out_t noattr))) ::
                                                     (Ebinop Osub
                                                       (Etempvar _n tulong)
                                                       (Econst_int (Int.repr 256) tint)
                                                       tulong) ::
                                                     (Econst_int (Int.repr 2) tint) ::
                                                     nil))
                                                  (Sifthenelse (Ebinop Oeq
                                                                 (Etempvar _fcsflag tuint)
                                                                 (Econst_int (Int.repr 2) tint)
                                                                 tint)
                                                    (Ssequence
                                                      (Scall None
                                                        (Evar _gp_assume 
                                                        (Tfunction
                                                          (tint :: nil) tvoid
                                                          cc_default))
                                                        ((Ebinop Ole
                                                           (Etempvar _n tulong)
                                                           (Econst_long (Int64.repr 4294967295) tulong)
                                                           tint) :: nil))
                                                      (Scall None
                                                        (Evar _put_le 
                                                        (Tfunction
                                                          ((tptr (Tstruct ___gp_out_t noattr)) ::
                                                           tulong :: tuint ::
                                                           nil) tvoid
                                                          cc_default))
                                                        ((Eaddrof
                                                           (Evar _h (Tstruct ___gp_out_t noattr))
                                                           (tptr (Tstruct ___gp_out_t noattr))) ::
                                                         (Etempvar _n tulong) ::
                                                         (Econst_int (Int.repr 4) tint) ::
                                                         nil)))
                                                    (Sifthenelse (Ebinop Oeq
                                                                   (Etempvar _fcsflag tuint)
                                                                   (Econst_int (Int.repr 3) tint)
                                                                   tint)
                                                      (Scall None
                                                        (Evar _put_le 
                                                        (Tfunction
                                                          ((tptr (Tstruct ___gp_out_t noattr)) ::
                                                           tulong :: tuint ::
                                                           nil) tvoid
                                                          cc_default))
                                                        ((Eaddrof
                                                           (Evar _h (Tstruct ___gp_out_t noattr))
                                                           (tptr (Tstruct ___gp_out_t noattr))) ::
                                                         (Etempvar _n tulong) ::
                                                         (Econst_int (Int.repr 8) tint) ::
                                                         nil))
                                                      Sskip)))))
                                            (Ssequence
                                              (Ssequence
                                                (Sset _x_valid_dict_api__t'54
                                                  (Efield
                                                    (Evar _h (Tstruct ___gp_out_t noattr))
                                                    _n tulong))
                                                (Scall None
                                                  (Evar _put_bytes (Tfunction
                                                                    ((tptr (Tstruct ___gp_out_t noattr)) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                  ((Etempvar _o (tptr (Tstruct ___gp_out_t noattr))) ::
                                                   (Evar _x_valid_dict_api__hdr (tarray tuchar 32)) ::
                                                   (Etempvar _x_valid_dict_api__t'54 tulong) ::
                                                   nil)))
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _x_valid_dict_api__t'53
                                                    (Efield
                                                      (Evar _h (Tstruct ___gp_out_t noattr))
                                                      _n tulong))
                                                  (Sassign
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _fi (tptr (Tstruct ___gp_winfo_t noattr)))
                                                        (Tstruct ___gp_winfo_t noattr))
                                                      _hsize tulong)
                                                    (Etempvar _x_valid_dict_api__t'53 tulong)))
                                                (Ssequence
                                                  (Ssequence
                                                    (Sifthenelse (Ebinop Olt
                                                                   (Etempvar _window tulong)
                                                                   (Ebinop Oshl
                                                                    (Econst_long (Int64.repr 1) tulong)
                                                                    (Econst_int (Int.repr 17) tint)
                                                                    tulong)
                                                                   tint)
                                                      (Sset _x_valid_dict_api__t'31
                                                        (Ecast
                                                          (Ecast
                                                            (Etempvar _window tulong)
                                                            tulong) tulong))
                                                      (Sset _x_valid_dict_api__t'31
                                                        (Ecast
                                                          (Ebinop Oshl
                                                            (Ecast
                                                              (Econst_int (Int.repr 1) tint)
                                                              tulong)
                                                            (Econst_int (Int.repr 17) tint)
                                                            tulong) tulong)))
                                                    (Sset _bmax
                                                      (Etempvar _x_valid_dict_api__t'31 tulong)))
                                                  (Ssequence
                                                    (Sifthenelse (Etempvar _d (tptr (Tstruct ___gp_wdict_t noattr)))
                                                      (Ssequence
                                                        (Scall None
                                                          (Evar _wstate_copy 
                                                          (Tfunction
                                                            ((tptr (Tstruct ___gp_wstate_t noattr)) ::
                                                             (tptr (Tstruct ___gp_wstate_t noattr)) ::
                                                             nil) tvoid
                                                            cc_default))
                                                          ((Eaddrof
                                                             (Evar _st__1 (Tstruct ___gp_wstate_t noattr))
                                                             (tptr (Tstruct ___gp_wstate_t noattr))) ::
                                                           (Eaddrof
                                                             (Efield
                                                               (Ederef
                                                                 (Etempvar _d (tptr (Tstruct ___gp_wdict_t noattr)))
                                                                 (Tstruct ___gp_wdict_t noattr))
                                                               _x_valid_dict_api__st
                                                               (Tstruct ___gp_wstate_t noattr))
                                                             (tptr (Tstruct ___gp_wstate_t noattr))) ::
                                                           nil))
                                                        (Ssequence
                                                          (Sset _i
                                                            (Ecast
                                                              (Econst_int (Int.repr 0) tint)
                                                              tulong))
                                                          (Sloop
                                                            (Ssequence
                                                              (Sifthenelse 
                                                                (Ebinop Olt
                                                                  (Etempvar _i tulong)
                                                                  (Etempvar _dictn tulong)
                                                                  tint)
                                                                Sskip
                                                                Sbreak)
                                                              (Ssequence
                                                                (Sset _x_valid_dict_api__t'51
                                                                  (Efield
                                                                    (Ederef
                                                                    (Etempvar _d (tptr (Tstruct ___gp_wdict_t noattr)))
                                                                    (Tstruct ___gp_wdict_t noattr))
                                                                    _content
                                                                    (tptr tuchar)))
                                                                (Ssequence
                                                                  (Sset _x_valid_dict_api__t'52
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x_valid_dict_api__t'51 (tptr tuchar))
                                                                    (Etempvar _i tulong)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                  (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_valid_dict_api__w_hist (tarray tuchar 266240))
                                                                    (Etempvar _i tulong)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Etempvar _x_valid_dict_api__t'52 tuchar)))))
                                                            (Sset _i
                                                              (Ebinop Oadd
                                                                (Etempvar _i tulong)
                                                                (Econst_int (Int.repr 1) tint)
                                                                tulong)))))
                                                      (Ssequence
                                                        (Sassign
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Efield
                                                                (Evar _st__1 (Tstruct ___gp_wstate_t noattr))
                                                                _rep
                                                                (tarray tuint 3))
                                                              (Econst_int (Int.repr 0) tint)
                                                              (tptr tuint))
                                                            tuint)
                                                          (Econst_int (Int.repr 1) tint))
                                                        (Ssequence
                                                          (Sassign
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Efield
                                                                  (Evar _st__1 (Tstruct ___gp_wstate_t noattr))
                                                                  _rep
                                                                  (tarray tuint 3))
                                                                (Econst_int (Int.repr 1) tint)
                                                                (tptr tuint))
                                                              tuint)
                                                            (Econst_int (Int.repr 4) tint))
                                                          (Ssequence
                                                            (Sassign
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Efield
                                                                    (Evar _st__1 (Tstruct ___gp_wstate_t noattr))
                                                                    _rep
                                                                    (tarray tuint 3))
                                                                  (Econst_int (Int.repr 2) tint)
                                                                  (tptr tuint))
                                                                tuint)
                                                              (Econst_int (Int.repr 8) tint))
                                                            (Ssequence
                                                              (Sassign
                                                                (Efield
                                                                  (Evar _st__1 (Tstruct ___gp_wstate_t noattr))
                                                                  _have_huf
                                                                  tint)
                                                                (Econst_int (Int.repr 0) tint))
                                                              (Sassign
                                                                (Efield
                                                                  (Evar _st__1 (Tstruct ___gp_wstate_t noattr))
                                                                  _have_tab
                                                                  tint)
                                                                (Econst_int (Int.repr 0) tint)))))))
                                                    (Ssequence
                                                      (Sassign
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _fi (tptr (Tstruct ___gp_winfo_t noattr)))
                                                            (Tstruct ___gp_winfo_t noattr))
                                                          _uses_dict tint)
                                                        (Ebinop One
                                                          (Etempvar _d (tptr (Tstruct ___gp_wdict_t noattr)))
                                                          (Ecast
                                                            (Econst_int (Int.repr 0) tint)
                                                            (tptr tvoid))
                                                          tint))
                                                      (Ssequence
                                                        (Sassign
                                                          (Evar _hn tulong)
                                                          (Etempvar _dictn tulong))
                                                        (Ssequence
                                                          (Sloop
                                                            (Ssequence
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _left tulong)
                                                                    (Etempvar _bmax tulong)
                                                                    tint)
                                                                    (Sset _x_valid_dict_api__t'32
                                                                    (Ecast
                                                                    (Etempvar _left tulong)
                                                                    tulong))
                                                                    (Sset _x_valid_dict_api__t'32
                                                                    (Ecast
                                                                    (Etempvar _bmax tulong)
                                                                    tulong)))
                                                                  (Scall (Some _x_valid_dict_api__t'33)
                                                                    (Evar _choose_in 
                                                                    (Tfunction
                                                                    (tulong ::
                                                                    tulong ::
                                                                    nil)
                                                                    tulong
                                                                    cc_default))
                                                                    ((Econst_int (Int.repr 0) tint) ::
                                                                    (Etempvar _x_valid_dict_api__t'32 tulong) ::
                                                                    nil)))
                                                                (Sset _t__1
                                                                  (Etempvar _x_valid_dict_api__t'33 tulong)))
                                                              (Ssequence
                                                                (Sset _start
                                                                  (Efield
                                                                    (Ederef
                                                                    (Etempvar _o (tptr (Tstruct ___gp_out_t noattr)))
                                                                    (Tstruct ___gp_out_t noattr))
                                                                    _n
                                                                    tulong))
                                                                (Ssequence
                                                                  (Ssequence
                                                                    (Scall (Some _x_valid_dict_api__t'34)
                                                                    (Evar _choose 
                                                                    (Tfunction
                                                                    (tuint ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                    ((Econst_int (Int.repr 3) tint) ::
                                                                    nil))
                                                                    (Sset _type
                                                                    (Etempvar _x_valid_dict_api__t'34 tuint)))
                                                                  (Ssequence
                                                                    (Scall None
                                                                    (Evar _gp_assume 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Ebinop Olt
                                                                    (Etempvar _nblocks tuint)
                                                                    (Econst_int (Int.repr 6) tint)
                                                                    tint) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t__1 tulong)
                                                                    (Etempvar _left tulong)
                                                                    tint)
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Ebinop Oadd
                                                                    (Etempvar _nblocks tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 6) tint)
                                                                    tint)
                                                                    (Sset _x_valid_dict_api__t'35
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tbool))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _x_valid_dict_api__t'36)
                                                                    (Evar _choose 
                                                                    (Tfunction
                                                                    (tuint ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                    ((Econst_int (Int.repr 4) tint) ::
                                                                    nil))
                                                                    (Sset _x_valid_dict_api__t'35
                                                                    (Ecast
                                                                    (Ebinop One
                                                                    (Etempvar _x_valid_dict_api__t'36 tuint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    tbool)))
                                                                    (Sset _x_valid_dict_api__t'35
                                                                    (Ecast
                                                                    (Etempvar _x_valid_dict_api__t'35 tint)
                                                                    tbool))))
                                                                    (Sset _x_valid_dict_api__t'35
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                    (Sset _last
                                                                    (Etempvar _x_valid_dict_api__t'35 tint)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _put_le 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct ___gp_out_t noattr)) ::
                                                                    tulong ::
                                                                    tuint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _o (tptr (Tstruct ___gp_out_t noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    (Econst_int (Int.repr 3) tint) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _type tuint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _i
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tulong))
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _i tulong)
                                                                    (Etempvar _t__1 tulong)
                                                                    tint)
                                                                    Sskip
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _x_valid_dict_api__t'37)
                                                                    (Evar _choose 
                                                                    (Tfunction
                                                                    (tuint ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                    ((Econst_int (Int.repr 256) tint) ::
                                                                    nil))
                                                                    (Sset _c
                                                                    (Ecast
                                                                    (Ecast
                                                                    (Etempvar _x_valid_dict_api__t'37 tuint)
                                                                    tuchar)
                                                                    tuchar)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _put8 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct ___gp_out_t noattr)) ::
                                                                    tuint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _o (tptr (Tstruct ___gp_out_t noattr))) ::
                                                                    (Etempvar _c tuchar) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'38
                                                                    (Evar _hn tulong))
                                                                    (Sassign
                                                                    (Evar _hn tulong)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x_valid_dict_api__t'38 tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong)))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_valid_dict_api__w_hist (tarray tuchar 266240))
                                                                    (Etempvar _x_valid_dict_api__t'38 tulong)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Etempvar _c tuchar))))))
                                                                    (Sset _i
                                                                    (Ebinop Oadd
                                                                    (Etempvar _i tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong))))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _type tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _x_valid_dict_api__t'39)
                                                                    (Evar _choose 
                                                                    (Tfunction
                                                                    (tuint ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                    ((Econst_int (Int.repr 256) tint) ::
                                                                    nil))
                                                                    (Sset _c__1
                                                                    (Ecast
                                                                    (Ecast
                                                                    (Etempvar _x_valid_dict_api__t'39 tuint)
                                                                    tuchar)
                                                                    tuchar)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _gp_assume 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Ebinop Oge
                                                                    (Etempvar _bmax tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _put8 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct ___gp_out_t noattr)) ::
                                                                    tuint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _o (tptr (Tstruct ___gp_out_t noattr))) ::
                                                                    (Etempvar _c__1 tuchar) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Sset _i
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tulong))
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _i tulong)
                                                                    (Etempvar _t__1 tulong)
                                                                    tint)
                                                                    Sskip
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'40
                                                                    (Evar _hn tulong))
                                                                    (Sassign
                                                                    (Evar _hn tulong)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x_valid_dict_api__t'40 tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong)))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_valid_dict_api__w_hist (tarray tuchar 266240))
                                                                    (Etempvar _x_valid_dict_api__t'40 tulong)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Etempvar _c__1 tuchar))))
                                                                    (Sset _i
                                                                    (Ebinop Oadd
                                                                    (Etempvar _i tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong)))))))
                                                                    (Scall None
                                                                    (Evar _w_compressed_block 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct ___gp_out_t noattr)) ::
                                                                    (tptr (Tstruct ___gp_wstate_t noattr)) ::
                                                                    tulong ::
                                                                    (tptr tulong) ::
                                                                    tulong ::
                                                                    tulong ::
                                                                    tulong ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _o (tptr (Tstruct ___gp_out_t noattr))) ::
                                                                    (Eaddrof
                                                                    (Evar _st__1 (Tstruct ___gp_wstate_t noattr))
                                                                    (tptr (Tstruct ___gp_wstate_t noattr))) ::
                                                                    (Etempvar _dictn tulong) ::
                                                                    (Eaddrof
                                                                    (Evar _hn tulong)
                                                                    (tptr tulong)) ::
                                                                    (Etempvar _t__1 tulong) ::
                                                                    (Etempvar _window tulong) ::
                                                                    (Etempvar _bmax tulong) ::
                                                                    nil))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _type tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    (Sset _x_valid_dict_api__t'41
                                                                    (Ecast
                                                                    (Etempvar _t__1 tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'50
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _o (tptr (Tstruct ___gp_out_t noattr)))
                                                                    (Tstruct ___gp_out_t noattr))
                                                                    _n
                                                                    tulong))
                                                                    (Sset _x_valid_dict_api__t'41
                                                                    (Ecast
                                                                    (Ebinop Osub
                                                                    (Ebinop Osub
                                                                    (Etempvar _x_valid_dict_api__t'50 tulong)
                                                                    (Etempvar _start tulong)
                                                                    tulong)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tulong)
                                                                    tulong))))
                                                                    (Sset _bsize
                                                                    (Etempvar _x_valid_dict_api__t'41 tulong)))
                                                                    (Ssequence
                                                                    (Sset _hv
                                                                    (Ebinop Oor
                                                                    (Ebinop Oor
                                                                    (Etempvar _last tuint)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _type tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)
                                                                    tuint)
                                                                    (Ebinop Oshl
                                                                    (Ecast
                                                                    (Etempvar _bsize tulong)
                                                                    tulong)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Ebinop Ole
                                                                    (Etempvar _bsize tulong)
                                                                    (Etempvar _bmax tulong)
                                                                    tint) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'49
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _o (tptr (Tstruct ___gp_out_t noattr)))
                                                                    (Tstruct ___gp_out_t noattr))
                                                                    _p
                                                                    (tptr tuchar)))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x_valid_dict_api__t'49 (tptr tuchar))
                                                                    (Etempvar _start tulong)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Ecast
                                                                    (Ebinop Oand
                                                                    (Etempvar _hv tulong)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tulong)
                                                                    tuchar)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'48
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _o (tptr (Tstruct ___gp_out_t noattr)))
                                                                    (Tstruct ___gp_out_t noattr))
                                                                    _p
                                                                    (tptr tuchar)))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x_valid_dict_api__t'48 (tptr tuchar))
                                                                    (Ebinop Oadd
                                                                    (Etempvar _start tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Ecast
                                                                    (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _hv tulong)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tulong)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tulong)
                                                                    tuchar)))
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'47
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _o (tptr (Tstruct ___gp_out_t noattr)))
                                                                    (Tstruct ___gp_out_t noattr))
                                                                    _p
                                                                    (tptr tuchar)))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x_valid_dict_api__t'47 (tptr tuchar))
                                                                    (Ebinop Oadd
                                                                    (Etempvar _start tulong)
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tulong)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Ecast
                                                                    (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _hv tulong)
                                                                    (Econst_int (Int.repr 16) tint)
                                                                    tulong)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tulong)
                                                                    tuchar))))))))
                                                                    (Ssequence
                                                                    (Sset _left
                                                                    (Ebinop Osub
                                                                    (Etempvar _left tulong)
                                                                    (Etempvar _t__1 tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _nblocks
                                                                    (Ebinop Oadd
                                                                    (Etempvar _nblocks tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint))
                                                                    (Sifthenelse (Etempvar _last tuint)
                                                                    Sbreak
                                                                    Sskip)))))))))))
                                                            Sskip)
                                                          (Ssequence
                                                            (Sassign
                                                              (Efield
                                                                (Ederef
                                                                  (Etempvar _fi (tptr (Tstruct ___gp_winfo_t noattr)))
                                                                  (Tstruct ___gp_winfo_t noattr))
                                                                _blocks
                                                                tuint)
                                                              (Etempvar _nblocks tuint))
                                                            (Ssequence
                                                              (Ssequence
                                                                (Sset _x_valid_dict_api__t'46
                                                                  (Evar _hn tulong))
                                                                (Scall None
                                                                  (Evar _gp_assert 
                                                                  (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                  ((Ebinop Oeq
                                                                    (Ebinop Osub
                                                                    (Etempvar _x_valid_dict_api__t'46 tulong)
                                                                    (Etempvar _dictn tulong)
                                                                    tulong)
                                                                    (Etempvar _n tulong)
                                                                    tint) ::
                                                                   nil)))
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Sset _i
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tulong))
                                                                  (Sloop
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _i tulong)
                                                                    (Etempvar _n tulong)
                                                                    tint)
                                                                    Sskip
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'44
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _x_valid_dict_api__sr (tptr (Tstruct ___gp_wseries_t noattr)))
                                                                    (Tstruct ___gp_wseries_t noattr))
                                                                    _content_n
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'45
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_valid_dict_api__w_hist (tarray tuchar 266240))
                                                                    (Ebinop Oadd
                                                                    (Etempvar _dictn tulong)
                                                                    (Etempvar _i tulong)
                                                                    tulong)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _x_valid_dict_api__sr (tptr (Tstruct ___gp_wseries_t noattr)))
                                                                    (Tstruct ___gp_wseries_t noattr))
                                                                    _content
                                                                    (tarray tuchar 262144))
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x_valid_dict_api__t'44 tulong)
                                                                    (Etempvar _i tulong)
                                                                    tulong)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Etempvar _x_valid_dict_api__t'45 tuchar)))))
                                                                    (Sset _i
                                                                    (Ebinop Oadd
                                                                    (Etempvar _i tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong))))
                                                                (Ssequence
                                                                  (Sset _x_valid_dict_api__t'43
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _fi (tptr (Tstruct ___gp_winfo_t noattr)))
                                                                    (Tstruct ___gp_winfo_t noattr))
                                                                    _checksum
                                                                    tuint))
                                                                  (Sifthenelse (Etempvar _x_valid_dict_api__t'43 tuint)
                                                                    (Ssequence
                                                                    (Scall (Some _x_valid_dict_api__t'42)
                                                                    (Evar _xxh64 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    tulong ::
                                                                    nil)
                                                                    tulong
                                                                    cc_default))
                                                                    ((Ebinop Oadd
                                                                    (Evar _x_valid_dict_api__w_hist (tarray tuchar 266240))
                                                                    (Etempvar _dictn tulong)
                                                                    (tptr tuchar)) ::
                                                                    (Etempvar _n tulong) ::
                                                                    nil))
                                                                    (Scall None
                                                                    (Evar _put_le 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct ___gp_out_t noattr)) ::
                                                                    tulong ::
                                                                    tuint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _o (tptr (Tstruct ___gp_out_t noattr))) ::
                                                                    (Ebinop Oand
                                                                    (Etempvar _x_valid_dict_api__t'42 tulong)
                                                                    (Econst_long (Int64.repr 4294967295) tulong)
                                                                    tulong) ::
                                                                    (Econst_int (Int.repr 4) tint) ::
                                                                    nil)))
                                                                    Sskip))))))))))))))))))))))))))))))))))
|}.

Definition f_w_series := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_x_valid_dict_api__sr, (tptr (Tstruct ___gp_wseries_t noattr))) ::
                (_d, (tptr (Tstruct ___gp_wdict_t noattr))) :: nil);
  fn_vars := ((_o, (Tstruct ___gp_out_t noattr)) :: nil);
  fn_temps := ((_k, tuint) :: (_f, tuint) ::
               (_fi, (tptr (Tstruct ___gp_winfo_t noattr))) ::
               (_m, tulong) :: (_i, tulong) :: (_room, tulong) ::
               (_scale, tulong) :: (_n, tulong) :: (_x_valid_dict_api__t'8, tulong) ::
               (_x_valid_dict_api__t'7, tulong) :: (_x_valid_dict_api__t'6, tuint) :: (_x_valid_dict_api__t'5, tuint) ::
               (_x_valid_dict_api__t'4, tuint) :: (_x_valid_dict_api__t'3, tulong) :: (_x_valid_dict_api__t'2, tuint) ::
               (_x_valid_dict_api__t'1, tuint) :: (_x_valid_dict_api__t'17, tulong) :: (_x_valid_dict_api__t'16, tulong) ::
               (_x_valid_dict_api__t'15, tuint) :: (_x_valid_dict_api__t'14, tulong) :: (_x_valid_dict_api__t'13, tulong) ::
               (_x_valid_dict_api__t'12, tuint) :: (_x_valid_dict_api__t'11, tulong) :: (_x_valid_dict_api__t'10, tulong) ::
               (_x_valid_dict_api__t'9, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sassign (Efield (Evar _o (Tstruct ___gp_out_t noattr)) _p (tptr tuchar))
    (Efield
      (Ederef (Etempvar _x_valid_dict_api__sr (tptr (Tstruct ___gp_wseries_t noattr)))
        (Tstruct ___gp_wseries_t noattr)) _bytes (tarray tuchar 524288)))
  (Ssequence
    (Sassign (Efield (Evar _o (Tstruct ___gp_out_t noattr)) _n tulong)
      (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Sassign (Efield (Evar _o (Tstruct ___gp_out_t noattr)) _cap tulong)
        (Esizeof (tarray tuchar 524288) tulong))
      (Ssequence
        (Ssequence
          (Scall (Some _x_valid_dict_api__t'1)
            (Evar _choose (Tfunction (tuint :: nil) tuint cc_default))
            ((Econst_int (Int.repr 4) tint) :: nil))
          (Sset _k
            (Ebinop Oadd (Econst_int (Int.repr 1) tint) (Etempvar _x_valid_dict_api__t'1 tuint)
              tuint)))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _x_valid_dict_api__sr (tptr (Tstruct ___gp_wseries_t noattr)))
                (Tstruct ___gp_wseries_t noattr)) _content_n tulong)
            (Econst_int (Int.repr 0) tint))
          (Ssequence
            (Ssequence
              (Sset _f (Econst_int (Int.repr 0) tint))
              (Sloop
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Etempvar _f tuint)
                                 (Etempvar _k tuint) tint)
                    Sskip
                    Sbreak)
                  (Ssequence
                    (Sset _fi
                      (Ebinop Oadd
                        (Efield
                          (Ederef
                            (Etempvar _x_valid_dict_api__sr (tptr (Tstruct ___gp_wseries_t noattr)))
                            (Tstruct ___gp_wseries_t noattr)) _f
                          (tarray (Tstruct ___gp_winfo_t noattr) 4))
                        (Etempvar _f tuint)
                        (tptr (Tstruct ___gp_winfo_t noattr))))
                    (Ssequence
                      (Ssequence
                        (Sset _x_valid_dict_api__t'17
                          (Efield (Evar _o (Tstruct ___gp_out_t noattr)) _n
                            tulong))
                        (Sassign
                          (Efield
                            (Ederef
                              (Etempvar _fi (tptr (Tstruct ___gp_winfo_t noattr)))
                              (Tstruct ___gp_winfo_t noattr)) _start tulong)
                          (Etempvar _x_valid_dict_api__t'17 tulong)))
                      (Ssequence
                        (Ssequence
                          (Sset _x_valid_dict_api__t'16
                            (Efield
                              (Ederef
                                (Etempvar _x_valid_dict_api__sr (tptr (Tstruct ___gp_wseries_t noattr)))
                                (Tstruct ___gp_wseries_t noattr)) _content_n
                              tulong))
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _fi (tptr (Tstruct ___gp_winfo_t noattr)))
                                (Tstruct ___gp_winfo_t noattr)) _cstart
                              tulong) (Etempvar _x_valid_dict_api__t'16 tulong)))
                        (Ssequence
                          (Ssequence
                            (Scall (Some _x_valid_dict_api__t'2)
                              (Evar _choose (Tfunction (tuint :: nil) tuint
                                              cc_default))
                              ((Econst_int (Int.repr 4) tint) :: nil))
                            (Sassign
                              (Efield
                                (Ederef
                                  (Etempvar _fi (tptr (Tstruct ___gp_winfo_t noattr)))
                                  (Tstruct ___gp_winfo_t noattr)) _skippable
                                tuint)
                              (Ebinop Oeq (Etempvar _x_valid_dict_api__t'2 tuint)
                                (Econst_int (Int.repr 0) tint) tint)))
                          (Ssequence
                            (Ssequence
                              (Sset _x_valid_dict_api__t'12
                                (Efield
                                  (Ederef
                                    (Etempvar _fi (tptr (Tstruct ___gp_winfo_t noattr)))
                                    (Tstruct ___gp_winfo_t noattr))
                                  _skippable tuint))
                              (Sifthenelse (Etempvar _x_valid_dict_api__t'12 tuint)
                                (Ssequence
                                  (Ssequence
                                    (Scall (Some _x_valid_dict_api__t'3)
                                      (Evar _choose_in (Tfunction
                                                         (tulong :: tulong ::
                                                          nil) tulong
                                                         cc_default))
                                      ((Econst_int (Int.repr 0) tint) ::
                                       (Econst_int (Int.repr 64) tint) ::
                                       nil))
                                    (Sset _m (Etempvar _x_valid_dict_api__t'3 tulong)))
                                  (Ssequence
                                    (Ssequence
                                      (Scall (Some _x_valid_dict_api__t'4)
                                        (Evar _choose (Tfunction
                                                        (tuint :: nil) tuint
                                                        cc_default))
                                        ((Econst_int (Int.repr 16) tint) ::
                                         nil))
                                      (Sassign
                                        (Efield
                                          (Ederef
                                            (Etempvar _fi (tptr (Tstruct ___gp_winfo_t noattr)))
                                            (Tstruct ___gp_winfo_t noattr))
                                          _variant tuint)
                                        (Etempvar _x_valid_dict_api__t'4 tuint)))
                                    (Ssequence
                                      (Ssequence
                                        (Sset _x_valid_dict_api__t'15
                                          (Efield
                                            (Ederef
                                              (Etempvar _fi (tptr (Tstruct ___gp_winfo_t noattr)))
                                              (Tstruct ___gp_winfo_t noattr))
                                            _variant tuint))
                                        (Scall None
                                          (Evar _put_le (Tfunction
                                                          ((tptr (Tstruct ___gp_out_t noattr)) ::
                                                           tulong :: tuint ::
                                                           nil) tvoid
                                                          cc_default))
                                          ((Eaddrof
                                             (Evar _o (Tstruct ___gp_out_t noattr))
                                             (tptr (Tstruct ___gp_out_t noattr))) ::
                                           (Ebinop Oadd
                                             (Econst_int (Int.repr 407710288) tuint)
                                             (Etempvar _x_valid_dict_api__t'15 tuint) tuint) ::
                                           (Econst_int (Int.repr 4) tint) ::
                                           nil)))
                                      (Ssequence
                                        (Scall None
                                          (Evar _put_le (Tfunction
                                                          ((tptr (Tstruct ___gp_out_t noattr)) ::
                                                           tulong :: tuint ::
                                                           nil) tvoid
                                                          cc_default))
                                          ((Eaddrof
                                             (Evar _o (Tstruct ___gp_out_t noattr))
                                             (tptr (Tstruct ___gp_out_t noattr))) ::
                                           (Etempvar _m tulong) ::
                                           (Econst_int (Int.repr 4) tint) ::
                                           nil))
                                        (Ssequence
                                          (Ssequence
                                            (Sset _i
                                              (Ecast
                                                (Econst_int (Int.repr 0) tint)
                                                tulong))
                                            (Sloop
                                              (Ssequence
                                                (Sifthenelse (Ebinop Olt
                                                               (Etempvar _i tulong)
                                                               (Etempvar _m tulong)
                                                               tint)
                                                  Sskip
                                                  Sbreak)
                                                (Ssequence
                                                  (Scall (Some _x_valid_dict_api__t'5)
                                                    (Evar _choose (Tfunction
                                                                    (tuint ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                    ((Econst_int (Int.repr 256) tint) ::
                                                     nil))
                                                  (Scall None
                                                    (Evar _put8 (Tfunction
                                                                  ((tptr (Tstruct ___gp_out_t noattr)) ::
                                                                   tuint ::
                                                                   nil) tvoid
                                                                  cc_default))
                                                    ((Eaddrof
                                                       (Evar _o (Tstruct ___gp_out_t noattr))
                                                       (tptr (Tstruct ___gp_out_t noattr))) ::
                                                     (Etempvar _x_valid_dict_api__t'5 tuint) ::
                                                     nil))))
                                              (Sset _i
                                                (Ebinop Oadd
                                                  (Etempvar _i tulong)
                                                  (Econst_int (Int.repr 1) tint)
                                                  tulong))))
                                          (Ssequence
                                            (Sassign
                                              (Efield
                                                (Ederef
                                                  (Etempvar _fi (tptr (Tstruct ___gp_winfo_t noattr)))
                                                  (Tstruct ___gp_winfo_t noattr))
                                                _skip_n tulong)
                                              (Etempvar _m tulong))
                                            (Ssequence
                                              (Sassign
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _fi (tptr (Tstruct ___gp_winfo_t noattr)))
                                                    (Tstruct ___gp_winfo_t noattr))
                                                  _hsize tulong)
                                                (Econst_int (Int.repr 8) tint))
                                              (Sassign
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _fi (tptr (Tstruct ___gp_winfo_t noattr)))
                                                    (Tstruct ___gp_winfo_t noattr))
                                                  _csize tulong)
                                                (Econst_int (Int.repr 0) tint)))))))))
                                (Ssequence
                                  (Ssequence
                                    (Sset _x_valid_dict_api__t'14
                                      (Efield
                                        (Ederef
                                          (Etempvar _x_valid_dict_api__sr (tptr (Tstruct ___gp_wseries_t noattr)))
                                          (Tstruct ___gp_wseries_t noattr))
                                        _content_n tulong))
                                    (Sset _room
                                      (Ebinop Osub
                                        (Ebinop Oshl
                                          (Econst_int (Int.repr 1) tuint)
                                          (Econst_int (Int.repr 18) tint)
                                          tuint) (Etempvar _x_valid_dict_api__t'14 tulong)
                                        tulong)))
                                  (Ssequence
                                    (Ssequence
                                      (Scall (Some _x_valid_dict_api__t'6)
                                        (Evar _choose (Tfunction
                                                        (tuint :: nil) tuint
                                                        cc_default))
                                        ((Econst_int (Int.repr 4) tint) ::
                                         nil))
                                      (Sset _scale
                                        (Ecast (Etempvar _x_valid_dict_api__t'6 tuint) tulong)))
                                    (Ssequence
                                      (Ssequence
                                        (Ssequence
                                          (Sifthenelse (Ebinop Oeq
                                                         (Etempvar _scale tulong)
                                                         (Econst_int (Int.repr 0) tint)
                                                         tint)
                                            (Sifthenelse (Ebinop Olt
                                                           (Etempvar _room tulong)
                                                           (Econst_int (Int.repr 16) tint)
                                                           tint)
                                              (Ssequence
                                                (Sset _x_valid_dict_api__t'7
                                                  (Ecast
                                                    (Etempvar _room tulong)
                                                    tulong))
                                                (Sset _x_valid_dict_api__t'7
                                                  (Ecast
                                                    (Etempvar _x_valid_dict_api__t'7 tulong)
                                                    tulong)))
                                              (Ssequence
                                                (Sset _x_valid_dict_api__t'7
                                                  (Ecast
                                                    (Econst_int (Int.repr 16) tint)
                                                    tulong))
                                                (Sset _x_valid_dict_api__t'7
                                                  (Ecast
                                                    (Etempvar _x_valid_dict_api__t'7 tulong)
                                                    tulong))))
                                            (Sifthenelse (Ebinop Oeq
                                                           (Etempvar _scale tulong)
                                                           (Econst_int (Int.repr 1) tint)
                                                           tint)
                                              (Sifthenelse (Ebinop Olt
                                                             (Etempvar _room tulong)
                                                             (Econst_int (Int.repr 300) tint)
                                                             tint)
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _x_valid_dict_api__t'7
                                                      (Ecast
                                                        (Etempvar _room tulong)
                                                        tulong))
                                                    (Sset _x_valid_dict_api__t'7
                                                      (Ecast
                                                        (Etempvar _x_valid_dict_api__t'7 tulong)
                                                        tulong)))
                                                  (Sset _x_valid_dict_api__t'7
                                                    (Ecast
                                                      (Etempvar _x_valid_dict_api__t'7 tulong)
                                                      tulong)))
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _x_valid_dict_api__t'7
                                                      (Ecast
                                                        (Econst_int (Int.repr 300) tint)
                                                        tulong))
                                                    (Sset _x_valid_dict_api__t'7
                                                      (Ecast
                                                        (Etempvar _x_valid_dict_api__t'7 tulong)
                                                        tulong)))
                                                  (Sset _x_valid_dict_api__t'7
                                                    (Ecast
                                                      (Etempvar _x_valid_dict_api__t'7 tulong)
                                                      tulong))))
                                              (Sifthenelse (Ebinop Oeq
                                                             (Etempvar _scale tulong)
                                                             (Econst_int (Int.repr 2) tint)
                                                             tint)
                                                (Sifthenelse (Ebinop Olt
                                                               (Etempvar _room tulong)
                                                               (Econst_int (Int.repr 5000) tint)
                                                               tint)
                                                  (Ssequence
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sset _x_valid_dict_api__t'7
                                                          (Ecast
                                                            (Etempvar _room tulong)
                                                            tulong))
                                                        (Sset _x_valid_dict_api__t'7
                                                          (Ecast
                                                            (Etempvar _x_valid_dict_api__t'7 tulong)
                                                            tulong)))
                                                      (Sset _x_valid_dict_api__t'7
                                                        (Ecast
                                                          (Etempvar _x_valid_dict_api__t'7 tulong)
                                                          tulong)))
                                                    (Sset _x_valid_dict_api__t'7
                                                      (Ecast
                                                        (Etempvar _x_valid_dict_api__t'7 tulong)
                                                        tulong)))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sset _x_valid_dict_api__t'7
                                                          (Ecast
                                                            (Econst_int (Int.repr 5000) tint)
                                                            tulong))
                                                        (Sset _x_valid_dict_api__t'7
                                                          (Ecast
                                                            (Etempvar _x_valid_dict_api__t'7 tulong)
                                                            tulong)))
                                                      (Sset _x_valid_dict_api__t'7
                                                        (Ecast
                                                          (Etempvar _x_valid_dict_api__t'7 tulong)
                                                          tulong)))
                                                    (Sset _x_valid_dict_api__t'7
                                                      (Ecast
                                                        (Etempvar _x_valid_dict_api__t'7 tulong)
                                                        tulong))))
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _x_valid_dict_api__t'7
                                                      (Ecast
                                                        (Etempvar _room tulong)
                                                        tulong))
                                                    (Sset _x_valid_dict_api__t'7
                                                      (Ecast
                                                        (Etempvar _x_valid_dict_api__t'7 tulong)
                                                        tulong)))
                                                  (Sset _x_valid_dict_api__t'7
                                                    (Ecast
                                                      (Etempvar _x_valid_dict_api__t'7 tulong)
                                                      tulong))))))
                                          (Scall (Some _x_valid_dict_api__t'8)
                                            (Evar _choose_in (Tfunction
                                                               (tulong ::
                                                                tulong ::
                                                                nil) tulong
                                                               cc_default))
                                            ((Econst_int (Int.repr 0) tint) ::
                                             (Etempvar _x_valid_dict_api__t'7 tulong) :: nil)))
                                        (Sset _n (Etempvar _x_valid_dict_api__t'8 tulong)))
                                      (Ssequence
                                        (Scall None
                                          (Evar _w_frame (Tfunction
                                                           ((tptr (Tstruct ___gp_wseries_t noattr)) ::
                                                            (tptr (Tstruct ___gp_out_t noattr)) ::
                                                            (tptr (Tstruct ___gp_winfo_t noattr)) ::
                                                            tulong ::
                                                            (tptr (Tstruct ___gp_wdict_t noattr)) ::
                                                            nil) tvoid
                                                           cc_default))
                                          ((Etempvar _x_valid_dict_api__sr (tptr (Tstruct ___gp_wseries_t noattr))) ::
                                           (Eaddrof
                                             (Evar _o (Tstruct ___gp_out_t noattr))
                                             (tptr (Tstruct ___gp_out_t noattr))) ::
                                           (Etempvar _fi (tptr (Tstruct ___gp_winfo_t noattr))) ::
                                           (Etempvar _n tulong) ::
                                           (Etempvar _d (tptr (Tstruct ___gp_wdict_t noattr))) ::
                                           nil))
                                        (Ssequence
                                          (Sassign
                                            (Efield
                                              (Ederef
                                                (Etempvar _fi (tptr (Tstruct ___gp_winfo_t noattr)))
                                                (Tstruct ___gp_winfo_t noattr))
                                              _csize tulong)
                                            (Etempvar _n tulong))
                                          (Ssequence
                                            (Sset _x_valid_dict_api__t'13
                                              (Efield
                                                (Ederef
                                                  (Etempvar _x_valid_dict_api__sr (tptr (Tstruct ___gp_wseries_t noattr)))
                                                  (Tstruct ___gp_wseries_t noattr))
                                                _content_n tulong))
                                            (Sassign
                                              (Efield
                                                (Ederef
                                                  (Etempvar _x_valid_dict_api__sr (tptr (Tstruct ___gp_wseries_t noattr)))
                                                  (Tstruct ___gp_wseries_t noattr))
                                                _content_n tulong)
                                              (Ebinop Oadd
                                                (Etempvar _x_valid_dict_api__t'13 tulong)
                                                (Etempvar _n tulong) tulong))))))))))
                            (Ssequence
                              (Sset _x_valid_dict_api__t'10
                                (Efield
                                  (Evar _o (Tstruct ___gp_out_t noattr)) _n
                                  tulong))
                              (Ssequence
                                (Sset _x_valid_dict_api__t'11
                                  (Efield
                                    (Ederef
                                      (Etempvar _fi (tptr (Tstruct ___gp_winfo_t noattr)))
                                      (Tstruct ___gp_winfo_t noattr)) _start
                                    tulong))
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _fi (tptr (Tstruct ___gp_winfo_t noattr)))
                                      (Tstruct ___gp_winfo_t noattr)) _size
                                    tulong)
                                  (Ebinop Osub (Etempvar _x_valid_dict_api__t'10 tulong)
                                    (Etempvar _x_valid_dict_api__t'11 tulong) tulong))))))))))
                (Sset _f
                  (Ebinop Oadd (Etempvar _f tuint)
                    (Econst_int (Int.repr 1) tint) tuint))))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _x_valid_dict_api__sr (tptr (Tstruct ___gp_wseries_t noattr)))
                    (Tstruct ___gp_wseries_t noattr)) _nframes tuint)
                (Etempvar _k tuint))
              (Ssequence
                (Sset _x_valid_dict_api__t'9
                  (Efield (Evar _o (Tstruct ___gp_out_t noattr)) _n tulong))
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _x_valid_dict_api__sr (tptr (Tstruct ___gp_wseries_t noattr)))
                      (Tstruct ___gp_wseries_t noattr)) _n tulong)
                  (Etempvar _x_valid_dict_api__t'9 tulong))))))))))
|}.

Definition f_within_oneshot := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_x_valid_dict_api__sr, (tptr (Tstruct ___gp_wseries_t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_k, tuint) :: (_x_valid_dict_api__t'3, tint) :: (_x_valid_dict_api__t'2, tint) :: (_x_valid_dict_api__t'1, tint) ::
               (_x_valid_dict_api__t'7, tuint) :: (_x_valid_dict_api__t'6, tint) :: (_x_valid_dict_api__t'5, tuint) ::
               (_x_valid_dict_api__t'4, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _k (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Ssequence
          (Sset _x_valid_dict_api__t'7
            (Efield
              (Ederef (Etempvar _x_valid_dict_api__sr (tptr (Tstruct ___gp_wseries_t noattr)))
                (Tstruct ___gp_wseries_t noattr)) _nframes tuint))
          (Sifthenelse (Ebinop Olt (Etempvar _k tuint) (Etempvar _x_valid_dict_api__t'7 tuint)
                         tint)
            Sskip
            Sbreak))
        (Ssequence
          (Ssequence
            (Ssequence
              (Sset _x_valid_dict_api__t'5
                (Efield
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef
                          (Etempvar _x_valid_dict_api__sr (tptr (Tstruct ___gp_wseries_t noattr)))
                          (Tstruct ___gp_wseries_t noattr)) _f
                        (tarray (Tstruct ___gp_winfo_t noattr) 4))
                      (Etempvar _k tuint)
                      (tptr (Tstruct ___gp_winfo_t noattr)))
                    (Tstruct ___gp_winfo_t noattr)) _skippable tuint))
              (Sifthenelse (Eunop Onotbool (Etempvar _x_valid_dict_api__t'5 tuint) tint)
                (Ssequence
                  (Sset _x_valid_dict_api__t'6
                    (Efield
                      (Ederef
                        (Ebinop Oadd
                          (Efield
                            (Ederef
                              (Etempvar _x_valid_dict_api__sr (tptr (Tstruct ___gp_wseries_t noattr)))
                              (Tstruct ___gp_wseries_t noattr)) _f
                            (tarray (Tstruct ___gp_winfo_t noattr) 4))
                          (Etempvar _k tuint)
                          (tptr (Tstruct ___gp_winfo_t noattr)))
                        (Tstruct ___gp_winfo_t noattr)) _single tint))
                  (Sset _x_valid_dict_api__t'1
                    (Ecast (Eunop Onotbool (Etempvar _x_valid_dict_api__t'6 tint) tint) tbool)))
                (Sset _x_valid_dict_api__t'1 (Econst_int (Int.repr 0) tint))))
            (Sifthenelse (Etempvar _x_valid_dict_api__t'1 tint)
              (Ssequence
                (Sifthenelse (Ebinop Oeq (Esizeof tulong tulong)
                               (Econst_int (Int.repr 4) tint) tint)
                  (Sset _x_valid_dict_api__t'3 (Ecast (Econst_int (Int.repr 30) tint) tint))
                  (Sset _x_valid_dict_api__t'3 (Ecast (Econst_int (Int.repr 31) tint) tint)))
                (Ssequence
                  (Sset _x_valid_dict_api__t'4
                    (Efield
                      (Ederef
                        (Ebinop Oadd
                          (Efield
                            (Ederef
                              (Etempvar _x_valid_dict_api__sr (tptr (Tstruct ___gp_wseries_t noattr)))
                              (Tstruct ___gp_wseries_t noattr)) _f
                            (tarray (Tstruct ___gp_winfo_t noattr) 4))
                          (Etempvar _k tuint)
                          (tptr (Tstruct ___gp_winfo_t noattr)))
                        (Tstruct ___gp_winfo_t noattr)) _window_log tuint))
                  (Sset _x_valid_dict_api__t'2
                    (Ecast
                      (Ebinop Ogt (Etempvar _x_valid_dict_api__t'4 tuint)
                        (Ecast (Etempvar _x_valid_dict_api__t'3 tint) tint) tint) tbool))))
              (Sset _x_valid_dict_api__t'2 (Econst_int (Int.repr 0) tint))))
          (Sifthenelse (Etempvar _x_valid_dict_api__t'2 tint)
            (Sreturn (Some (Econst_int (Int.repr 0) tint)))
            Sskip)))
      (Sset _k
        (Ebinop Oadd (Etempvar _k tuint) (Econst_int (Int.repr 1) tint)
          tuint))))
  (Sreturn (Some (Econst_int (Int.repr 1) tint))))
|}.

Definition f_within_stream := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_x_valid_dict_api__sr, (tptr (Tstruct ___gp_wseries_t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_k, tuint) :: (_x_valid_dict_api__t'2, tint) :: (_x_valid_dict_api__t'1, tint) ::
               (_x_valid_dict_api__t'5, tuint) :: (_x_valid_dict_api__t'4, tulong) :: (_x_valid_dict_api__t'3, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _k (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Ssequence
          (Sset _x_valid_dict_api__t'5
            (Efield
              (Ederef (Etempvar _x_valid_dict_api__sr (tptr (Tstruct ___gp_wseries_t noattr)))
                (Tstruct ___gp_wseries_t noattr)) _nframes tuint))
          (Sifthenelse (Ebinop Olt (Etempvar _k tuint) (Etempvar _x_valid_dict_api__t'5 tuint)
                         tint)
            Sskip
            Sbreak))
        (Ssequence
          (Ssequence
            (Sset _x_valid_dict_api__t'3
              (Efield
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef
                        (Etempvar _x_valid_dict_api__sr (tptr (Tstruct ___gp_wseries_t noattr)))
                        (Tstruct ___gp_wseries_t noattr)) _f
                      (tarray (Tstruct ___gp_winfo_t noattr) 4))
                    (Etempvar _k tuint)
                    (tptr (Tstruct ___gp_winfo_t noattr)))
                  (Tstruct ___gp_winfo_t noattr)) _skippable tuint))
            (Sifthenelse (Eunop Onotbool (Etempvar _x_valid_dict_api__t'3 tuint) tint)
              (Ssequence
                (Sset _x_valid_dict_api__t'4
                  (Efield
                    (Ederef
                      (Ebinop Oadd
                        (Efield
                          (Ederef
                            (Etempvar _x_valid_dict_api__sr (tptr (Tstruct ___gp_wseries_t noattr)))
                            (Tstruct ___gp_wseries_t noattr)) _f
                          (tarray (Tstruct ___gp_winfo_t noattr) 4))
                        (Etempvar _k tuint)
                        (tptr (Tstruct ___gp_winfo_t noattr)))
                      (Tstruct ___gp_winfo_t noattr)) _window tulong))
                (Sset _x_valid_dict_api__t'1
                  (Ecast
                    (Ebinop Ogt (Etempvar _x_valid_dict_api__t'4 tulong)
                      (Ebinop Oshl (Econst_long (Int64.repr 1) tulong)
                        (Econst_int (Int.repr 27) tint) tulong) tint) tbool)))
              (Sset _x_valid_dict_api__t'1 (Econst_int (Int.repr 0) tint))))
          (Sifthenelse (Etempvar _x_valid_dict_api__t'1 tint)
            (Sreturn (Some (Econst_int (Int.repr 0) tint)))
            Sskip)))
      (Sset _k
        (Ebinop Oadd (Etempvar _k tuint) (Econst_int (Int.repr 1) tint)
          tuint))))
  (Ssequence
    (Scall (Some _x_valid_dict_api__t'2)
      (Evar _within_oneshot (Tfunction
                              ((tptr (Tstruct ___gp_wseries_t noattr)) ::
                               nil) tint cc_default))
      ((Etempvar _x_valid_dict_api__sr (tptr (Tstruct ___gp_wseries_t noattr))) :: nil))
    (Sreturn (Some (Etempvar _x_valid_dict_api__t'2 tint)))))
|}.

Definition f_stall_error := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_e, tint) :: (_stalled, tulong) ::
                (_in, (tptr (Tstruct _ZSTD_inBuffer_s noattr))) ::
                (_out, (tptr (Tstruct _ZSTD_outBuffer_s noattr))) ::
                (_opos0, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_x_valid_dict_api__t'4, tint) :: (_x_valid_dict_api__t'3, tint) :: (_x_valid_dict_api__t'2, tint) ::
               (_x_valid_dict_api__t'1, tint) :: (_x_valid_dict_api__t'12, tulong) :: (_x_valid_dict_api__t'11, tulong) ::
               (_x_valid_dict_api__t'10, tulong) :: (_x_valid_dict_api__t'9, tulong) :: (_x_valid_dict_api__t'8, tulong) ::
               (_x_valid_dict_api__t'7, tulong) :: (_x_valid_dict_api__t'6, tulong) :: (_x_valid_dict_api__t'5, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sifthenelse (Ebinop Olt
                     (Ebinop Oadd (Etempvar _stalled tulong)
                       (Econst_int (Int.repr 1) tint) tulong)
                     (Econst_int (Int.repr 16) tint) tint)
        (Sset _x_valid_dict_api__t'1 (Econst_int (Int.repr 1) tint))
        (Ssequence
          (Sset _x_valid_dict_api__t'12
            (Efield
              (Ederef (Etempvar _in (tptr (Tstruct _ZSTD_inBuffer_s noattr)))
                (Tstruct _ZSTD_inBuffer_s noattr)) _pos tulong))
          (Sset _x_valid_dict_api__t'1
            (Ecast
              (Ebinop One (Etempvar _x_valid_dict_api__t'12 tulong)
                (Econst_int (Int.repr 0) tint) tint) tbool))))
      (Sifthenelse (Etempvar _x_valid_dict_api__t'1 tint)
        (Sset _x_valid_dict_api__t'2 (Econst_int (Int.repr 1) tint))
        (Ssequence
          (Sset _x_valid_dict_api__t'11
            (Efield
              (Ederef
                (Etempvar _out (tptr (Tstruct _ZSTD_outBuffer_s noattr)))
                (Tstruct _ZSTD_outBuffer_s noattr)) _pos tulong))
          (Sset _x_valid_dict_api__t'2
            (Ecast
              (Ebinop One (Etempvar _x_valid_dict_api__t'11 tulong) (Etempvar _opos0 tulong)
                tint) tbool)))))
    (Sifthenelse (Etempvar _x_valid_dict_api__t'2 tint)
      (Sreturn (Some (Econst_int (Int.repr 0) tint)))
      Sskip))
  (Ssequence
    (Sifthenelse (Ebinop Oeq (Etempvar _e tint)
                   (Econst_int (Int.repr 80) tint) tint)
      (Ssequence
        (Sset _x_valid_dict_api__t'9
          (Efield
            (Ederef (Etempvar _out (tptr (Tstruct _ZSTD_outBuffer_s noattr)))
              (Tstruct _ZSTD_outBuffer_s noattr)) _pos tulong))
        (Ssequence
          (Sset _x_valid_dict_api__t'10
            (Efield
              (Ederef
                (Etempvar _out (tptr (Tstruct _ZSTD_outBuffer_s noattr)))
                (Tstruct _ZSTD_outBuffer_s noattr)) _size tulong))
          (Sreturn (Some (Ebinop Oeq (Etempvar _x_valid_dict_api__t'9 tulong)
                           (Etempvar _x_valid_dict_api__t'10 tulong) tint)))))
      Sskip)
    (Ssequence
      (Ssequence
        (Sifthenelse (Ebinop Oeq (Etempvar _e tint)
                       (Econst_int (Int.repr 82) tint) tint)
          (Ssequence
            (Sset _x_valid_dict_api__t'7
              (Efield
                (Ederef
                  (Etempvar _out (tptr (Tstruct _ZSTD_outBuffer_s noattr)))
                  (Tstruct _ZSTD_outBuffer_s noattr)) _pos tulong))
            (Ssequence
              (Sset _x_valid_dict_api__t'8
                (Efield
                  (Ederef
                    (Etempvar _out (tptr (Tstruct _ZSTD_outBuffer_s noattr)))
                    (Tstruct _ZSTD_outBuffer_s noattr)) _size tulong))
              (Sset _x_valid_dict_api__t'3
                (Ecast
                  (Ebinop Olt (Etempvar _x_valid_dict_api__t'7 tulong) (Etempvar _x_valid_dict_api__t'8 tulong)
                    tint) tbool))))
          (Sset _x_valid_dict_api__t'3 (Econst_int (Int.repr 0) tint)))
        (Sifthenelse (Etempvar _x_valid_dict_api__t'3 tint)
          (Ssequence
            (Sset _x_valid_dict_api__t'5
              (Efield
                (Ederef
                  (Etempvar _in (tptr (Tstruct _ZSTD_inBuffer_s noattr)))
                  (Tstruct _ZSTD_inBuffer_s noattr)) _pos tulong))
            (Ssequence
              (Sset _x_valid_dict_api__t'6
                (Efield
                  (Ederef
                    (Etempvar _in (tptr (Tstruct _ZSTD_inBuffer_s noattr)))
                    (Tstruct _ZSTD_inBuffer_s noattr)) _size tulong))
              (Sset _x_valid_dict_api__t'4
                (Ecast
                  (Ebinop Oeq (Etempvar _x_valid_dict_api__t'5 tulong) (Etempvar _x_valid_dict_api__t'6 tulong)
                    tint) tbool))))
          (Sset _x_valid_dict_api__t'4 (Econst_int (Int.repr 0) tint))))
      (Sreturn (Some (Etempvar _x_valid_dict_api__t'4 tint))))))
|}.

Definition f_exact_copy := {|
  fn_return := (tptr tuchar);
  fn_callconv := cc_default;
  fn_params := ((_b, (tptr tuchar)) :: (_n, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr tuchar)) :: (_i, tulong) :: (_x_valid_dict_api__t'2, (tptr tvoid)) ::
               (_x_valid_dict_api__t'1, tulong) :: (_x_valid_dict_api__t'3, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sifthenelse (Ebinop Ogt (Etempvar _n tulong)
                     (Econst_int (Int.repr 0) tint) tint)
        (Sset _x_valid_dict_api__t'1 (Ecast (Etempvar _n tulong) tulong))
        (Sset _x_valid_dict_api__t'1 (Ecast (Econst_int (Int.repr 1) tint) tulong)))
      (Scall (Some _x_valid_dict_api__t'2)
        (Evar _quickproof_malloc (Tfunction (tulong :: nil) (tptr tvoid)
                                   cc_default))
        ((Etempvar _x_valid_dict_api__t'1 tulong) :: nil)))
    (Sset _p (Etempvar _x_valid_dict_api__t'2 (tptr tvoid))))
  (Ssequence
    (Sifthenelse (Ebinop One (Etempvar _p (tptr tuchar))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Ssequence
        (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _i tulong)
                           (Etempvar _n tulong) tint)
              Sskip
              Sbreak)
            (Ssequence
              (Sset _x_valid_dict_api__t'3
                (Ederef
                  (Ebinop Oadd (Etempvar _b (tptr tuchar))
                    (Etempvar _i tulong) (tptr tuchar)) tuchar))
              (Sassign
                (Ederef
                  (Ebinop Oadd (Etempvar _p (tptr tuchar))
                    (Etempvar _i tulong) (tptr tuchar)) tuchar)
                (Etempvar _x_valid_dict_api__t'3 tuchar))))
          (Sset _i
            (Ebinop Oadd (Etempvar _i tulong) (Econst_int (Int.repr 1) tint)
              tulong))))
      Sskip)
    (Sreturn (Some (Etempvar _p (tptr tuchar))))))
|}.

Definition v_vd_wd := {|
  gvar_info := (tarray (Tstruct ___gp_wdict_t noattr) 3);
  gvar_init := (Init_space 41952 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_vd_raw := {|
  gvar_info := (Tstruct ___gp_wdict_t noattr);
  gvar_init := (Init_space 13984 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_x_valid_dict_api__sr := {|
  gvar_info := (Tstruct ___gp_wseries_t noattr);
  gvar_init := (Init_space 786936 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_vd_chunk := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_max, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_c, tuint) :: (_lim, tulong) :: (_x_valid_dict_api__t'4, tulong) ::
               (_x_valid_dict_api__t'3, tulong) :: (_x_valid_dict_api__t'2, tulong) :: (_x_valid_dict_api__t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _x_valid_dict_api__t'1)
      (Evar _choose (Tfunction (tuint :: nil) tuint cc_default))
      ((Econst_int (Int.repr 4) tint) :: nil))
    (Sset _c (Etempvar _x_valid_dict_api__t'1 tuint)))
  (Ssequence
    (Ssequence
      (Sifthenelse (Ebinop Oeq (Etempvar _c tuint)
                     (Econst_int (Int.repr 0) tint) tint)
        (Sset _x_valid_dict_api__t'2 (Ecast (Econst_int (Int.repr 16) tint) tulong))
        (Sifthenelse (Ebinop Oeq (Etempvar _c tuint)
                       (Econst_int (Int.repr 1) tint) tint)
          (Ssequence
            (Sset _x_valid_dict_api__t'2 (Ecast (Econst_int (Int.repr 512) tint) tulong))
            (Sset _x_valid_dict_api__t'2 (Ecast (Etempvar _x_valid_dict_api__t'2 tulong) tulong)))
          (Sifthenelse (Ebinop Oeq (Etempvar _c tuint)
                         (Econst_int (Int.repr 2) tint) tint)
            (Ssequence
              (Ssequence
                (Sset _x_valid_dict_api__t'2 (Ecast (Econst_int (Int.repr 70000) tint) tulong))
                (Sset _x_valid_dict_api__t'2 (Ecast (Etempvar _x_valid_dict_api__t'2 tulong) tulong)))
              (Sset _x_valid_dict_api__t'2 (Ecast (Etempvar _x_valid_dict_api__t'2 tulong) tulong)))
            (Ssequence
              (Ssequence
                (Sset _x_valid_dict_api__t'2 (Ecast (Etempvar _max tulong) tulong))
                (Sset _x_valid_dict_api__t'2 (Ecast (Etempvar _x_valid_dict_api__t'2 tulong) tulong)))
              (Sset _x_valid_dict_api__t'2 (Ecast (Etempvar _x_valid_dict_api__t'2 tulong) tulong))))))
      (Sset _lim (Etempvar _x_valid_dict_api__t'2 tulong)))
    (Ssequence
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _lim tulong)
                       (Etempvar _max tulong) tint)
          (Sset _x_valid_dict_api__t'3 (Ecast (Etempvar _lim tulong) tulong))
          (Sset _x_valid_dict_api__t'3 (Ecast (Etempvar _max tulong) tulong)))
        (Scall (Some _x_valid_dict_api__t'4)
          (Evar _choose_in (Tfunction (tulong :: tulong :: nil) tulong
                             cc_default))
          ((Econst_int (Int.repr 0) tint) :: (Etempvar _x_valid_dict_api__t'3 tulong) :: nil)))
      (Sreturn (Some (Etempvar _x_valid_dict_api__t'4 tulong))))))
|}.

Definition f_vd_stream := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ds, (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
                (_src, (tptr tuchar)) :: nil);
  fn_vars := ((_in, (Tstruct _ZSTD_inBuffer_s noattr)) ::
              (_out, (Tstruct _ZSTD_outBuffer_s noattr)) :: nil);
  fn_temps := ((_ipos, tulong) :: (_got, tulong) :: (_calls, tulong) ::
               (_stalled, tulong) :: (_r, tulong) :: (_j, tulong) ::
               (_k, tuint) :: (_ilen, tulong) :: (_olen, tulong) ::
               (_ib, (tptr tuchar)) :: (_ob, (tptr tuchar)) ::
               (_at_end, tint) :: (_x_valid_dict_api__t'16, tint) :: (_x_valid_dict_api__t'15, tulong) ::
               (_x_valid_dict_api__t'14, tint) :: (_x_valid_dict_api__t'13, tuint) :: (_x_valid_dict_api__t'12, tint) ::
               (_x_valid_dict_api__t'11, tint) :: (_x_valid_dict_api__t'10, tint) :: (_x_valid_dict_api__t'9, tint) ::
               (_x_valid_dict_api__t'8, tint) :: (_x_valid_dict_api__t'7, tint) :: (_x_valid_dict_api__t'6, tulong) ::
               (_x_valid_dict_api__t'5, tint) :: (_x_valid_dict_api__t'4, (tptr tvoid)) ::
               (_x_valid_dict_api__t'3, (tptr tuchar)) :: (_x_valid_dict_api__t'2, tulong) :: (_x_valid_dict_api__t'1, tulong) ::
               (_x_valid_dict_api__t'35, tulong) :: (_x_valid_dict_api__t'34, tulong) :: (_x_valid_dict_api__t'33, tulong) ::
               (_x_valid_dict_api__t'32, tulong) :: (_x_valid_dict_api__t'31, tulong) :: (_x_valid_dict_api__t'30, tulong) ::
               (_x_valid_dict_api__t'29, tulong) :: (_x_valid_dict_api__t'28, tuchar) :: (_x_valid_dict_api__t'27, tuchar) ::
               (_x_valid_dict_api__t'26, tulong) :: (_x_valid_dict_api__t'25, tulong) :: (_x_valid_dict_api__t'24, tulong) ::
               (_x_valid_dict_api__t'23, tulong) :: (_x_valid_dict_api__t'22, tuint) :: (_x_valid_dict_api__t'21, tulong) ::
               (_x_valid_dict_api__t'20, tulong) :: (_x_valid_dict_api__t'19, tulong) :: (_x_valid_dict_api__t'18, tulong) ::
               (_x_valid_dict_api__t'17, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sset _ipos (Ecast (Econst_int (Int.repr 0) tint) tulong))
  (Ssequence
    (Sset _got (Ecast (Econst_int (Int.repr 0) tint) tulong))
    (Ssequence
      (Sset _stalled (Ecast (Econst_int (Int.repr 0) tint) tulong))
      (Ssequence
        (Sset _calls (Ecast (Econst_int (Int.repr 0) tint) tulong))
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _calls tulong)
                           (Econst_int (Int.repr 4096) tint) tint)
              Sskip
              Sbreak)
            (Ssequence
              (Ssequence
                (Ssequence
                  (Sset _x_valid_dict_api__t'35
                    (Efield (Evar _x_valid_dict_api__sr (Tstruct ___gp_wseries_t noattr)) _n
                      tulong))
                  (Scall (Some _x_valid_dict_api__t'1)
                    (Evar _vd_chunk (Tfunction (tulong :: nil) tulong
                                      cc_default))
                    ((Ebinop Osub (Etempvar _x_valid_dict_api__t'35 tulong)
                       (Etempvar _ipos tulong) tulong) :: nil)))
                (Sset _ilen (Etempvar _x_valid_dict_api__t'1 tulong)))
              (Ssequence
                (Ssequence
                  (Scall (Some _x_valid_dict_api__t'2)
                    (Evar _vd_chunk (Tfunction (tulong :: nil) tulong
                                      cc_default))
                    ((Ebinop Oshl (Econst_int (Int.repr 1) tuint)
                       (Econst_int (Int.repr 18) tint) tuint) :: nil))
                  (Sset _olen
                    (Ebinop Oadd (Econst_int (Int.repr 1) tint)
                      (Etempvar _x_valid_dict_api__t'2 tulong) tulong)))
                (Ssequence
                  (Ssequence
                    (Scall (Some _x_valid_dict_api__t'3)
                      (Evar _exact_copy (Tfunction
                                          ((tptr tuchar) :: tulong :: nil)
                                          (tptr tuchar) cc_default))
                      ((Ebinop Oadd (Etempvar _src (tptr tuchar))
                         (Etempvar _ipos tulong) (tptr tuchar)) ::
                       (Etempvar _ilen tulong) :: nil))
                    (Sset _ib (Etempvar _x_valid_dict_api__t'3 (tptr tuchar))))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _x_valid_dict_api__t'4)
                        (Evar _quickproof_malloc (Tfunction (tulong :: nil)
                                                   (tptr tvoid) cc_default))
                        ((Etempvar _olen tulong) :: nil))
                      (Sset _ob (Etempvar _x_valid_dict_api__t'4 (tptr tvoid))))
                    (Ssequence
                      (Ssequence
                        (Sifthenelse (Ebinop Oeq (Etempvar _ib (tptr tuchar))
                                       (Ecast (Econst_int (Int.repr 0) tint)
                                         (tptr tvoid)) tint)
                          (Sset _x_valid_dict_api__t'5 (Econst_int (Int.repr 1) tint))
                          (Sset _x_valid_dict_api__t'5
                            (Ecast
                              (Ebinop Oeq (Etempvar _ob (tptr tuchar))
                                (Ecast (Econst_int (Int.repr 0) tint)
                                  (tptr tvoid)) tint) tbool)))
                        (Sifthenelse (Etempvar _x_valid_dict_api__t'5 tint)
                          (Ssequence
                            (Scall None
                              (Evar _quickproof_free (Tfunction
                                                       ((tptr tvoid) :: nil)
                                                       tvoid cc_default))
                              ((Etempvar _ib (tptr tuchar)) :: nil))
                            (Ssequence
                              (Scall None
                                (Evar _quickproof_free (Tfunction
                                                         ((tptr tvoid) ::
                                                          nil) tvoid
                                                         cc_default))
                                ((Etempvar _ob (tptr tuchar)) :: nil))
                              Sbreak))
                          Sskip))
                      (Ssequence
                        (Sassign
                          (Efield
                            (Evar _in (Tstruct _ZSTD_inBuffer_s noattr)) _src
                            (tptr tvoid)) (Etempvar _ib (tptr tuchar)))
                        (Ssequence
                          (Sassign
                            (Efield
                              (Evar _in (Tstruct _ZSTD_inBuffer_s noattr))
                              _size tulong) (Etempvar _ilen tulong))
                          (Ssequence
                            (Sassign
                              (Efield
                                (Evar _in (Tstruct _ZSTD_inBuffer_s noattr))
                                _pos tulong) (Econst_int (Int.repr 0) tint))
                            (Ssequence
                              (Sassign
                                (Efield
                                  (Evar _out (Tstruct _ZSTD_outBuffer_s noattr))
                                  _dst (tptr tvoid))
                                (Etempvar _ob (tptr tuchar)))
                              (Ssequence
                                (Sassign
                                  (Efield
                                    (Evar _out (Tstruct _ZSTD_outBuffer_s noattr))
                                    _size tulong) (Etempvar _olen tulong))
                                (Ssequence
                                  (Sassign
                                    (Efield
                                      (Evar _out (Tstruct _ZSTD_outBuffer_s noattr))
                                      _pos tulong)
                                    (Econst_int (Int.repr 0) tint))
                                  (Ssequence
                                    (Ssequence
                                      (Scall (Some _x_valid_dict_api__t'6)
                                        (Evar _ZSTD_decompressStream 
                                        (Tfunction
                                          ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
                                           (tptr (Tstruct _ZSTD_outBuffer_s noattr)) ::
                                           (tptr (Tstruct _ZSTD_inBuffer_s noattr)) ::
                                           nil) tulong cc_default))
                                        ((Etempvar _ds (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
                                         (Eaddrof
                                           (Evar _out (Tstruct _ZSTD_outBuffer_s noattr))
                                           (tptr (Tstruct _ZSTD_outBuffer_s noattr))) ::
                                         (Eaddrof
                                           (Evar _in (Tstruct _ZSTD_inBuffer_s noattr))
                                           (tptr (Tstruct _ZSTD_inBuffer_s noattr))) ::
                                         nil))
                                      (Sset _r (Etempvar _x_valid_dict_api__t'6 tulong)))
                                    (Ssequence
                                      (Ssequence
                                        (Sset _x_valid_dict_api__t'33
                                          (Efield
                                            (Evar _in (Tstruct _ZSTD_inBuffer_s noattr))
                                            _pos tulong))
                                        (Ssequence
                                          (Sset _x_valid_dict_api__t'34
                                            (Efield
                                              (Evar _in (Tstruct _ZSTD_inBuffer_s noattr))
                                              _size tulong))
                                          (Scall None
                                            (Evar _gp_assert (Tfunction
                                                               (tint :: nil)
                                                               tvoid
                                                               cc_default))
                                            ((Ebinop Ole
                                               (Etempvar _x_valid_dict_api__t'33 tulong)
                                               (Etempvar _x_valid_dict_api__t'34 tulong) tint) ::
                                             nil))))
                                      (Ssequence
                                        (Ssequence
                                          (Sset _x_valid_dict_api__t'31
                                            (Efield
                                              (Evar _out (Tstruct _ZSTD_outBuffer_s noattr))
                                              _pos tulong))
                                          (Ssequence
                                            (Sset _x_valid_dict_api__t'32
                                              (Efield
                                                (Evar _out (Tstruct _ZSTD_outBuffer_s noattr))
                                                _size tulong))
                                            (Scall None
                                              (Evar _gp_assert (Tfunction
                                                                 (tint ::
                                                                  nil) tvoid
                                                                 cc_default))
                                              ((Ebinop Ole
                                                 (Etempvar _x_valid_dict_api__t'31 tulong)
                                                 (Etempvar _x_valid_dict_api__t'32 tulong)
                                                 tint) :: nil))))
                                        (Ssequence
                                          (Ssequence
                                            (Sset _j
                                              (Ecast
                                                (Econst_int (Int.repr 0) tint)
                                                tulong))
                                            (Sloop
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _x_valid_dict_api__t'30
                                                    (Efield
                                                      (Evar _out (Tstruct _ZSTD_outBuffer_s noattr))
                                                      _pos tulong))
                                                  (Sifthenelse (Ebinop Olt
                                                                 (Etempvar _j tulong)
                                                                 (Etempvar _x_valid_dict_api__t'30 tulong)
                                                                 tint)
                                                    Sskip
                                                    Sbreak))
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _x_valid_dict_api__t'29
                                                      (Efield
                                                        (Evar _x_valid_dict_api__sr (Tstruct ___gp_wseries_t noattr))
                                                        _content_n tulong))
                                                    (Scall None
                                                      (Evar _gp_assert 
                                                      (Tfunction
                                                        (tint :: nil) tvoid
                                                        cc_default))
                                                      ((Ebinop Olt
                                                         (Ebinop Oadd
                                                           (Etempvar _got tulong)
                                                           (Etempvar _j tulong)
                                                           tulong)
                                                         (Etempvar _x_valid_dict_api__t'29 tulong)
                                                         tint) :: nil)))
                                                  (Ssequence
                                                    (Sset _x_valid_dict_api__t'27
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Etempvar _ob (tptr tuchar))
                                                          (Etempvar _j tulong)
                                                          (tptr tuchar))
                                                        tuchar))
                                                    (Ssequence
                                                      (Sset _x_valid_dict_api__t'28
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Efield
                                                              (Evar _x_valid_dict_api__sr (Tstruct ___gp_wseries_t noattr))
                                                              _content
                                                              (tarray tuchar 262144))
                                                            (Ebinop Oadd
                                                              (Etempvar _got tulong)
                                                              (Etempvar _j tulong)
                                                              tulong)
                                                            (tptr tuchar))
                                                          tuchar))
                                                      (Scall None
                                                        (Evar _gp_assert 
                                                        (Tfunction
                                                          (tint :: nil) tvoid
                                                          cc_default))
                                                        ((Ebinop Oeq
                                                           (Etempvar _x_valid_dict_api__t'27 tuchar)
                                                           (Etempvar _x_valid_dict_api__t'28 tuchar)
                                                           tint) :: nil))))))
                                              (Sset _j
                                                (Ebinop Oadd
                                                  (Etempvar _j tulong)
                                                  (Econst_int (Int.repr 1) tint)
                                                  tulong))))
                                          (Ssequence
                                            (Ssequence
                                              (Sset _x_valid_dict_api__t'26
                                                (Efield
                                                  (Evar _out (Tstruct _ZSTD_outBuffer_s noattr))
                                                  _pos tulong))
                                              (Sset _got
                                                (Ebinop Oadd
                                                  (Etempvar _got tulong)
                                                  (Etempvar _x_valid_dict_api__t'26 tulong)
                                                  tulong)))
                                            (Ssequence
                                              (Ssequence
                                                (Sset _x_valid_dict_api__t'25
                                                  (Efield
                                                    (Evar _in (Tstruct _ZSTD_inBuffer_s noattr))
                                                    _pos tulong))
                                                (Sset _ipos
                                                  (Ebinop Oadd
                                                    (Etempvar _ipos tulong)
                                                    (Etempvar _x_valid_dict_api__t'25 tulong)
                                                    tulong)))
                                              (Ssequence
                                                (Scall None
                                                  (Evar _quickproof_free 
                                                  (Tfunction
                                                    ((tptr tvoid) :: nil)
                                                    tvoid cc_default))
                                                  ((Etempvar _ib (tptr tuchar)) ::
                                                   nil))
                                                (Ssequence
                                                  (Scall None
                                                    (Evar _quickproof_free 
                                                    (Tfunction
                                                      ((tptr tvoid) :: nil)
                                                      tvoid cc_default))
                                                    ((Etempvar _ob (tptr tuchar)) ::
                                                     nil))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Scall (Some _x_valid_dict_api__t'13)
                                                        (Evar _ZSTD_isError 
                                                        (Tfunction
                                                          (tulong :: nil)
                                                          tuint cc_default))
                                                        ((Etempvar _r tulong) ::
                                                         nil))
                                                      (Sifthenelse (Etempvar _x_valid_dict_api__t'13 tuint)
                                                        (Ssequence
                                                          (Ssequence
                                                            (Ssequence
                                                              (Ssequence
                                                                (Scall (Some _x_valid_dict_api__t'7)
                                                                  (Evar _within_stream 
                                                                  (Tfunction
                                                                    ((tptr (Tstruct ___gp_wseries_t noattr)) ::
                                                                    nil) tint
                                                                    cc_default))
                                                                  ((Eaddrof
                                                                    (Evar _x_valid_dict_api__sr (Tstruct ___gp_wseries_t noattr))
                                                                    (tptr (Tstruct ___gp_wseries_t noattr))) ::
                                                                   nil))
                                                                (Sifthenelse 
                                                                  (Eunop Onotbool
                                                                    (Etempvar _x_valid_dict_api__t'7 tint)
                                                                    tint)
                                                                  (Sset _x_valid_dict_api__t'8
                                                                    (Econst_int (Int.repr 1) tint))
                                                                  (Ssequence
                                                                    (Scall (Some _x_valid_dict_api__t'9)
                                                                    (Evar _ZSTD_getErrorCode 
                                                                    (Tfunction
                                                                    (tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Etempvar _r tulong) ::
                                                                    nil))
                                                                    (Sset _x_valid_dict_api__t'8
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _x_valid_dict_api__t'9 tint)
                                                                    (Econst_int (Int.repr 64) tint)
                                                                    tint)
                                                                    tbool)))))
                                                              (Sifthenelse (Etempvar _x_valid_dict_api__t'8 tint)
                                                                (Sset _x_valid_dict_api__t'10
                                                                  (Econst_int (Int.repr 1) tint))
                                                                (Ssequence
                                                                  (Ssequence
                                                                    (Scall (Some _x_valid_dict_api__t'11)
                                                                    (Evar _ZSTD_getErrorCode 
                                                                    (Tfunction
                                                                    (tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Etempvar _r tulong) ::
                                                                    nil))
                                                                    (Scall (Some _x_valid_dict_api__t'12)
                                                                    (Evar _stall_error 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    tulong ::
                                                                    (tptr (Tstruct _ZSTD_inBuffer_s noattr)) ::
                                                                    (tptr (Tstruct _ZSTD_outBuffer_s noattr)) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Etempvar _x_valid_dict_api__t'11 tint) ::
                                                                    (Etempvar _stalled tulong) ::
                                                                    (Eaddrof
                                                                    (Evar _in (Tstruct _ZSTD_inBuffer_s noattr))
                                                                    (tptr (Tstruct _ZSTD_inBuffer_s noattr))) ::
                                                                    (Eaddrof
                                                                    (Evar _out (Tstruct _ZSTD_outBuffer_s noattr))
                                                                    (tptr (Tstruct _ZSTD_outBuffer_s noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil)))
                                                                  (Sset _x_valid_dict_api__t'10
                                                                    (Ecast
                                                                    (Etempvar _x_valid_dict_api__t'12 tint)
                                                                    tbool)))))
                                                            (Scall None
                                                              (Evar _gp_assert 
                                                              (Tfunction
                                                                (tint :: nil)
                                                                tvoid
                                                                cc_default))
                                                              ((Etempvar _x_valid_dict_api__t'10 tint) ::
                                                               nil)))
                                                          Sbreak)
                                                        Sskip))
                                                    (Ssequence
                                                      (Ssequence
                                                        (Ssequence
                                                          (Ssequence
                                                            (Sset _x_valid_dict_api__t'23
                                                              (Efield
                                                                (Evar _in (Tstruct _ZSTD_inBuffer_s noattr))
                                                                _pos tulong))
                                                            (Sifthenelse 
                                                              (Ebinop Oeq
                                                                (Etempvar _x_valid_dict_api__t'23 tulong)
                                                                (Econst_int (Int.repr 0) tint)
                                                                tint)
                                                              (Ssequence
                                                                (Sset _x_valid_dict_api__t'24
                                                                  (Efield
                                                                    (Evar _out (Tstruct _ZSTD_outBuffer_s noattr))
                                                                    _pos
                                                                    tulong))
                                                                (Sset _x_valid_dict_api__t'14
                                                                  (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _x_valid_dict_api__t'24 tulong)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    tbool)))
                                                              (Sset _x_valid_dict_api__t'14
                                                                (Econst_int (Int.repr 0) tint))))
                                                          (Sifthenelse (Etempvar _x_valid_dict_api__t'14 tint)
                                                            (Sset _x_valid_dict_api__t'15
                                                              (Ecast
                                                                (Ebinop Oadd
                                                                  (Etempvar _stalled tulong)
                                                                  (Econst_int (Int.repr 1) tint)
                                                                  tulong)
                                                                tulong))
                                                            (Sset _x_valid_dict_api__t'15
                                                              (Ecast
                                                                (Econst_int (Int.repr 0) tint)
                                                                tulong))))
                                                        (Sset _stalled
                                                          (Etempvar _x_valid_dict_api__t'15 tulong)))
                                                      (Sifthenelse (Ebinop Oeq
                                                                    (Etempvar _r tulong)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                        (Ssequence
                                                          (Sset _at_end
                                                            (Econst_int (Int.repr 0) tint))
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _k
                                                                (Econst_int (Int.repr 0) tint))
                                                              (Sloop
                                                                (Ssequence
                                                                  (Ssequence
                                                                    (Sset _x_valid_dict_api__t'22
                                                                    (Efield
                                                                    (Evar _x_valid_dict_api__sr (Tstruct ___gp_wseries_t noattr))
                                                                    _nframes
                                                                    tuint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _k tuint)
                                                                    (Etempvar _x_valid_dict_api__t'22 tuint)
                                                                    tint)
                                                                    Sskip
                                                                    Sbreak))
                                                                  (Ssequence
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'18
                                                                    (Efield
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _x_valid_dict_api__sr (Tstruct ___gp_wseries_t noattr))
                                                                    _f
                                                                    (tarray (Tstruct ___gp_winfo_t noattr) 4))
                                                                    (Etempvar _k tuint)
                                                                    (tptr (Tstruct ___gp_winfo_t noattr)))
                                                                    (Tstruct ___gp_winfo_t noattr))
                                                                    _start
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'19
                                                                    (Efield
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _x_valid_dict_api__sr (Tstruct ___gp_wseries_t noattr))
                                                                    _f
                                                                    (tarray (Tstruct ___gp_winfo_t noattr) 4))
                                                                    (Etempvar _k tuint)
                                                                    (tptr (Tstruct ___gp_winfo_t noattr)))
                                                                    (Tstruct ___gp_winfo_t noattr))
                                                                    _size
                                                                    tulong))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x_valid_dict_api__t'18 tulong)
                                                                    (Etempvar _x_valid_dict_api__t'19 tulong)
                                                                    tulong)
                                                                    (Etempvar _ipos tulong)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'20
                                                                    (Efield
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _x_valid_dict_api__sr (Tstruct ___gp_wseries_t noattr))
                                                                    _f
                                                                    (tarray (Tstruct ___gp_winfo_t noattr) 4))
                                                                    (Etempvar _k tuint)
                                                                    (tptr (Tstruct ___gp_winfo_t noattr)))
                                                                    (Tstruct ___gp_winfo_t noattr))
                                                                    _cstart
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'21
                                                                    (Efield
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _x_valid_dict_api__sr (Tstruct ___gp_wseries_t noattr))
                                                                    _f
                                                                    (tarray (Tstruct ___gp_winfo_t noattr) 4))
                                                                    (Etempvar _k tuint)
                                                                    (tptr (Tstruct ___gp_winfo_t noattr)))
                                                                    (Tstruct ___gp_winfo_t noattr))
                                                                    _csize
                                                                    tulong))
                                                                    (Sset _x_valid_dict_api__t'16
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _got tulong)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x_valid_dict_api__t'20 tulong)
                                                                    (Etempvar _x_valid_dict_api__t'21 tulong)
                                                                    tulong)
                                                                    tint)
                                                                    tbool))))
                                                                    (Sset _x_valid_dict_api__t'16
                                                                    (Econst_int (Int.repr 0) tint)))))
                                                                    (Sifthenelse (Etempvar _x_valid_dict_api__t'16 tint)
                                                                    (Sset _at_end
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    Sskip)))
                                                                (Sset _k
                                                                  (Ebinop Oadd
                                                                    (Etempvar _k tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint))))
                                                            (Ssequence
                                                              (Scall None
                                                                (Evar _gp_assert 
                                                                (Tfunction
                                                                  (tint ::
                                                                   nil) tvoid
                                                                  cc_default))
                                                                ((Etempvar _at_end tint) ::
                                                                 nil))
                                                              (Ssequence
                                                                (Sset _x_valid_dict_api__t'17
                                                                  (Efield
                                                                    (Evar _x_valid_dict_api__sr (Tstruct ___gp_wseries_t noattr))
                                                                    _n
                                                                    tulong))
                                                                (Sifthenelse 
                                                                  (Ebinop Oeq
                                                                    (Etempvar _ipos tulong)
                                                                    (Etempvar _x_valid_dict_api__t'17 tulong)
                                                                    tint)
                                                                  Sbreak
                                                                  Sskip)))))
                                                        Sskip)))))))))))))))))))))))
          (Sset _calls
            (Ebinop Oadd (Etempvar _calls tulong)
              (Econst_int (Int.repr 1) tint) tulong)))))))
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := ((_dd, (tarray (tptr (Tstruct _ZSTD_DDict_s noattr)) 3)) :: nil);
  fn_temps := ((_mode, tuint) :: (_nd, tuint) :: (_which, tuint) ::
               (_i, tuint) :: (_k, tuint) :: (_cap, tulong) ::
               (_r, tulong) :: (_j, tulong) :: (_dn, tulong) ::
               (_wd, (tptr (Tstruct ___gp_wdict_t noattr))) ::
               (_src, (tptr tuchar)) :: (_buf, (tptr tuchar)) ::
               (_dst, (tptr tuchar)) :: (_dict, (tptr tuchar)) ::
               (_dctx, (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
               (_fail, tint) :: (_m, tint) :: (_t__1, tint) ::
               (_x_valid_dict_api__t'56, tint) :: (_x_valid_dict_api__t'55, tuint) :: (_x_valid_dict_api__t'54, tint) ::
               (_x_valid_dict_api__t'53, tuint) :: (_x_valid_dict_api__t'52, tint) :: (_x_valid_dict_api__t'51, tint) ::
               (_x_valid_dict_api__t'50, tint) :: (_x_valid_dict_api__t'49, tulong) :: (_x_valid_dict_api__t'48, tuint) ::
               (_x_valid_dict_api__t'47, tulong) :: (_x_valid_dict_api__t'46, tint) :: (_x_valid_dict_api__t'45, tuint) ::
               (_x_valid_dict_api__t'44, tulong) :: (_x_valid_dict_api__t'43, tint) ::
               (_x_valid_dict_api__t'42, (tptr (Tstruct _ZSTD_DDict_s noattr))) ::
               (_x_valid_dict_api__t'41, tuint) :: (_x_valid_dict_api__t'40, tulong) :: (_x_valid_dict_api__t'39, tuint) ::
               (_x_valid_dict_api__t'38, tulong) :: (_x_valid_dict_api__t'37, tint) :: (_x_valid_dict_api__t'36, tuint) ::
               (_x_valid_dict_api__t'35, tuint) :: (_x_valid_dict_api__t'34, tuint) :: (_x_valid_dict_api__t'33, tulong) ::
               (_x_valid_dict_api__t'32, tulong) :: (_x_valid_dict_api__t'31, tint) :: (_x_valid_dict_api__t'30, tuint) ::
               (_x_valid_dict_api__t'29, tuint) :: (_x_valid_dict_api__t'28, tulong) :: (_x_valid_dict_api__t'27, tint) ::
               (_x_valid_dict_api__t'26, tuint) :: (_x_valid_dict_api__t'25, tint) :: (_x_valid_dict_api__t'24, tint) ::
               (_x_valid_dict_api__t'23, tuint) :: (_x_valid_dict_api__t'22, tuint) :: (_x_valid_dict_api__t'21, tulong) ::
               (_x_valid_dict_api__t'20, tint) ::
               (_x_valid_dict_api__t'19, (tptr (Tstruct _ZSTD_DDict_s noattr))) ::
               (_x_valid_dict_api__t'18, tint) :: (_x_valid_dict_api__t'17, tuint) :: (_x_valid_dict_api__t'16, tulong) ::
               (_x_valid_dict_api__t'15, tint) :: (_x_valid_dict_api__t'14, tint) ::
               (_x_valid_dict_api__t'13, (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
               (_x_valid_dict_api__t'12, (tptr tvoid)) :: (_x_valid_dict_api__t'11, (tptr tuchar)) ::
               (_x_valid_dict_api__t'10, tint) :: (_x_valid_dict_api__t'9, tulong) :: (_x_valid_dict_api__t'8, tint) ::
               (_x_valid_dict_api__t'7, tint) :: (_x_valid_dict_api__t'6, tint) :: (_x_valid_dict_api__t'5, tint) ::
               (_x_valid_dict_api__t'4, tint) :: (_x_valid_dict_api__t'3, tuint) :: (_x_valid_dict_api__t'2, tuint) ::
               (_x_valid_dict_api__t'1, tuint) :: (_x_valid_dict_api__t'84, tint) :: (_x_valid_dict_api__t'83, tuint) ::
               (_x_valid_dict_api__t'82, tuint) :: (_x_valid_dict_api__t'81, tint) :: (_x_valid_dict_api__t'80, tulong) ::
               (_x_valid_dict_api__t'79, tint) :: (_x_valid_dict_api__t'78, tulong) :: (_x_valid_dict_api__t'77, tuint) ::
               (_x_valid_dict_api__t'76, tuint) :: (_x_valid_dict_api__t'75, tuint) :: (_x_valid_dict_api__t'74, tuint) ::
               (_x_valid_dict_api__t'73, tuint) :: (_x_valid_dict_api__t'72, tuint) :: (_x_valid_dict_api__t'71, tuint) ::
               (_x_valid_dict_api__t'70, tulong) :: (_x_valid_dict_api__t'69, tulong) :: (_x_valid_dict_api__t'68, tuchar) ::
               (_x_valid_dict_api__t'67, tulong) ::
               (_x_valid_dict_api__t'66, (tptr (Tstruct _ZSTD_DDict_s noattr))) ::
               (_x_valid_dict_api__t'65, (tptr (Tstruct _ZSTD_DDict_s noattr))) ::
               (_x_valid_dict_api__t'64, (tptr (Tstruct _ZSTD_DDict_s noattr))) ::
               (_x_valid_dict_api__t'63, (tptr (Tstruct _ZSTD_DDict_s noattr))) ::
               (_x_valid_dict_api__t'62, tulong) :: (_x_valid_dict_api__t'61, tulong) :: (_x_valid_dict_api__t'60, tuchar) ::
               (_x_valid_dict_api__t'59, tuchar) :: (_x_valid_dict_api__t'58, tulong) ::
               (_x_valid_dict_api__t'57, (tptr (Tstruct _ZSTD_DDict_s noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Scall (Some _x_valid_dict_api__t'1)
        (Evar _choose (Tfunction (tuint :: nil) tuint cc_default))
        ((Econst_int (Int.repr 7) tint) :: nil))
      (Sset _mode (Etempvar _x_valid_dict_api__t'1 tuint)))
    (Ssequence
      (Sset _nd (Econst_int (Int.repr 1) tint))
      (Ssequence
        (Sset _which (Econst_int (Int.repr 0) tint))
        (Ssequence
          (Sset _cap (Ecast (Econst_int (Int.repr 0) tint) tulong))
          (Ssequence
            (Sset _fail (Econst_int (Int.repr 0) tint))
            (Ssequence
              (Ssequence
                (Sset _i (Econst_int (Int.repr 0) tint))
                (Sloop
                  (Ssequence
                    (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                                   (Econst_int (Int.repr 3) tint) tint)
                      Sskip
                      Sbreak)
                    (Sassign
                      (Ederef
                        (Ebinop Oadd
                          (Evar _dd (tarray (tptr (Tstruct _ZSTD_DDict_s noattr)) 3))
                          (Etempvar _i tuint)
                          (tptr (tptr (Tstruct _ZSTD_DDict_s noattr))))
                        (tptr (Tstruct _ZSTD_DDict_s noattr)))
                      (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
                  (Sset _i
                    (Ebinop Oadd (Etempvar _i tuint)
                      (Econst_int (Int.repr 1) tint) tuint))))
              (Ssequence
                (Sifthenelse (Ebinop Oeq (Etempvar _mode tuint)
                               (Econst_int (Int.repr 0) tint) tint)
                  (Ssequence
                    (Scall (Some _x_valid_dict_api__t'2)
                      (Evar _choose (Tfunction (tuint :: nil) tuint
                                      cc_default))
                      ((Ebinop Osub (Econst_int (Int.repr 3) tint)
                         (Econst_int (Int.repr 1) tint) tint) :: nil))
                    (Sset _nd
                      (Ebinop Oadd (Econst_int (Int.repr 2) tint)
                        (Etempvar _x_valid_dict_api__t'2 tuint) tuint)))
                  Sskip)
                (Ssequence
                  (Ssequence
                    (Sset _i (Econst_int (Int.repr 0) tint))
                    (Sloop
                      (Ssequence
                        (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                                       (Etempvar _nd tuint) tint)
                          Sskip
                          Sbreak)
                        (Ssequence
                          (Scall None
                            (Evar _w_dict (Tfunction
                                            ((tptr (Tstruct ___gp_wdict_t noattr)) ::
                                             nil) tvoid cc_default))
                            ((Ebinop Oadd
                               (Evar _vd_wd (tarray (Tstruct ___gp_wdict_t noattr) 3))
                               (Etempvar _i tuint)
                               (tptr (Tstruct ___gp_wdict_t noattr))) :: nil))
                          (Sifthenelse (Ebinop Oeq (Etempvar _mode tuint)
                                         (Econst_int (Int.repr 0) tint) tint)
                            (Ssequence
                              (Ssequence
                                (Sset _x_valid_dict_api__t'84
                                  (Efield
                                    (Ederef
                                      (Ebinop Oadd
                                        (Evar _vd_wd (tarray (Tstruct ___gp_wdict_t noattr) 3))
                                        (Etempvar _i tuint)
                                        (tptr (Tstruct ___gp_wdict_t noattr)))
                                      (Tstruct ___gp_wdict_t noattr))
                                    _formatted tint))
                                (Scall None
                                  (Evar _gp_assume (Tfunction (tint :: nil)
                                                     tvoid cc_default))
                                  ((Etempvar _x_valid_dict_api__t'84 tint) :: nil)))
                              (Ssequence
                                (Sset _k (Econst_int (Int.repr 0) tint))
                                (Sloop
                                  (Ssequence
                                    (Sifthenelse (Ebinop Olt
                                                   (Etempvar _k tuint)
                                                   (Etempvar _i tuint) tint)
                                      Sskip
                                      Sbreak)
                                    (Ssequence
                                      (Sset _x_valid_dict_api__t'82
                                        (Efield
                                          (Ederef
                                            (Ebinop Oadd
                                              (Evar _vd_wd (tarray (Tstruct ___gp_wdict_t noattr) 3))
                                              (Etempvar _i tuint)
                                              (tptr (Tstruct ___gp_wdict_t noattr)))
                                            (Tstruct ___gp_wdict_t noattr))
                                          _id tuint))
                                      (Ssequence
                                        (Sset _x_valid_dict_api__t'83
                                          (Efield
                                            (Ederef
                                              (Ebinop Oadd
                                                (Evar _vd_wd (tarray (Tstruct ___gp_wdict_t noattr) 3))
                                                (Etempvar _k tuint)
                                                (tptr (Tstruct ___gp_wdict_t noattr)))
                                              (Tstruct ___gp_wdict_t noattr))
                                            _id tuint))
                                        (Scall None
                                          (Evar _gp_assume (Tfunction
                                                             (tint :: nil)
                                                             tvoid
                                                             cc_default))
                                          ((Ebinop One (Etempvar _x_valid_dict_api__t'82 tuint)
                                             (Etempvar _x_valid_dict_api__t'83 tuint) tint) ::
                                           nil)))))
                                  (Sset _k
                                    (Ebinop Oadd (Etempvar _k tuint)
                                      (Econst_int (Int.repr 1) tint) tuint)))))
                            Sskip)))
                      (Sset _i
                        (Ebinop Oadd (Etempvar _i tuint)
                          (Econst_int (Int.repr 1) tint) tuint))))
                  (Ssequence
                    (Sifthenelse (Ebinop Oeq (Etempvar _mode tuint)
                                   (Econst_int (Int.repr 0) tint) tint)
                      (Ssequence
                        (Scall (Some _x_valid_dict_api__t'3)
                          (Evar _choose (Tfunction (tuint :: nil) tuint
                                          cc_default))
                          ((Etempvar _nd tuint) :: nil))
                        (Sset _which (Etempvar _x_valid_dict_api__t'3 tuint)))
                      Sskip)
                    (Ssequence
                      (Sset _wd
                        (Ebinop Oadd
                          (Evar _vd_wd (tarray (Tstruct ___gp_wdict_t noattr) 3))
                          (Etempvar _which tuint)
                          (tptr (Tstruct ___gp_wdict_t noattr))))
                      (Ssequence
                        (Ssequence
                          (Ssequence
                            (Sifthenelse (Ebinop Oeq (Etempvar _mode tuint)
                                           (Econst_int (Int.repr 1) tint)
                                           tint)
                              (Sset _x_valid_dict_api__t'4 (Econst_int (Int.repr 1) tint))
                              (Sset _x_valid_dict_api__t'4
                                (Ecast
                                  (Ebinop Oeq (Etempvar _mode tuint)
                                    (Econst_int (Int.repr 3) tint) tint)
                                  tbool)))
                            (Sifthenelse (Etempvar _x_valid_dict_api__t'4 tint)
                              (Sset _x_valid_dict_api__t'5 (Econst_int (Int.repr 1) tint))
                              (Sset _x_valid_dict_api__t'5
                                (Ecast
                                  (Ebinop Oeq (Etempvar _mode tuint)
                                    (Econst_int (Int.repr 4) tint) tint)
                                  tbool))))
                          (Sifthenelse (Etempvar _x_valid_dict_api__t'5 tint)
                            (Ssequence
                              (Sset _x_valid_dict_api__t'81
                                (Efield
                                  (Ederef
                                    (Etempvar _wd (tptr (Tstruct ___gp_wdict_t noattr)))
                                    (Tstruct ___gp_wdict_t noattr))
                                  _formatted tint))
                              (Scall None
                                (Evar _gp_assume (Tfunction (tint :: nil)
                                                   tvoid cc_default))
                                ((Eunop Onotbool (Etempvar _x_valid_dict_api__t'81 tint) tint) ::
                                 nil)))
                            Sskip))
                        (Ssequence
                          (Sifthenelse (Ebinop Oeq (Etempvar _mode tuint)
                                         (Econst_int (Int.repr 2) tint) tint)
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Sset _x_valid_dict_api__t'79
                                    (Efield
                                      (Ederef
                                        (Etempvar _wd (tptr (Tstruct ___gp_wdict_t noattr)))
                                        (Tstruct ___gp_wdict_t noattr))
                                      _formatted tint))
                                  (Sifthenelse (Etempvar _x_valid_dict_api__t'79 tint)
                                    (Ssequence
                                      (Sset _x_valid_dict_api__t'80
                                        (Efield
                                          (Ederef
                                            (Etempvar _wd (tptr (Tstruct ___gp_wdict_t noattr)))
                                            (Tstruct ___gp_wdict_t noattr))
                                          _n tulong))
                                      (Sset _x_valid_dict_api__t'6
                                        (Ecast
                                          (Ebinop Ole (Etempvar _x_valid_dict_api__t'80 tulong)
                                            (Ebinop Oshl
                                              (Econst_int (Int.repr 1) tuint)
                                              (Econst_int (Int.repr 12) tint)
                                              tuint) tint) tbool)))
                                    (Sset _x_valid_dict_api__t'6
                                      (Econst_int (Int.repr 0) tint))))
                                (Scall None
                                  (Evar _gp_assume (Tfunction (tint :: nil)
                                                     tvoid cc_default))
                                  ((Etempvar _x_valid_dict_api__t'6 tint) :: nil)))
                              (Ssequence
                                (Sassign
                                  (Efield
                                    (Evar _vd_raw (Tstruct ___gp_wdict_t noattr))
                                    _formatted tint)
                                  (Econst_int (Int.repr 0) tint))
                                (Ssequence
                                  (Sassign
                                    (Efield
                                      (Evar _vd_raw (Tstruct ___gp_wdict_t noattr))
                                      _id tuint)
                                    (Econst_int (Int.repr 0) tint))
                                  (Ssequence
                                    (Sassign
                                      (Efield
                                        (Evar _vd_raw (Tstruct ___gp_wdict_t noattr))
                                        _content (tptr tuchar))
                                      (Efield
                                        (Ederef
                                          (Etempvar _wd (tptr (Tstruct ___gp_wdict_t noattr)))
                                          (Tstruct ___gp_wdict_t noattr))
                                        _bytes (tarray tuchar 6144)))
                                    (Ssequence
                                      (Ssequence
                                        (Sset _x_valid_dict_api__t'78
                                          (Efield
                                            (Ederef
                                              (Etempvar _wd (tptr (Tstruct ___gp_wdict_t noattr)))
                                              (Tstruct ___gp_wdict_t noattr))
                                            _n tulong))
                                        (Sassign
                                          (Efield
                                            (Evar _vd_raw (Tstruct ___gp_wdict_t noattr))
                                            _content_n tulong)
                                          (Etempvar _x_valid_dict_api__t'78 tulong)))
                                      (Ssequence
                                        (Sassign
                                          (Efield
                                            (Efield
                                              (Evar _vd_raw (Tstruct ___gp_wdict_t noattr))
                                              _x_valid_dict_api__st
                                              (Tstruct ___gp_wstate_t noattr))
                                            _have_huf tint)
                                          (Econst_int (Int.repr 0) tint))
                                        (Ssequence
                                          (Sassign
                                            (Efield
                                              (Efield
                                                (Evar _vd_raw (Tstruct ___gp_wdict_t noattr))
                                                _x_valid_dict_api__st
                                                (Tstruct ___gp_wstate_t noattr))
                                              _have_tab tint)
                                            (Econst_int (Int.repr 0) tint))
                                          (Ssequence
                                            (Sassign
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Efield
                                                    (Efield
                                                      (Evar _vd_raw (Tstruct ___gp_wdict_t noattr))
                                                      _x_valid_dict_api__st
                                                      (Tstruct ___gp_wstate_t noattr))
                                                    _rep (tarray tuint 3))
                                                  (Econst_int (Int.repr 0) tint)
                                                  (tptr tuint)) tuint)
                                              (Econst_int (Int.repr 1) tint))
                                            (Ssequence
                                              (Sassign
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Efield
                                                      (Efield
                                                        (Evar _vd_raw (Tstruct ___gp_wdict_t noattr))
                                                        _x_valid_dict_api__st
                                                        (Tstruct ___gp_wstate_t noattr))
                                                      _rep (tarray tuint 3))
                                                    (Econst_int (Int.repr 1) tint)
                                                    (tptr tuint)) tuint)
                                                (Econst_int (Int.repr 4) tint))
                                              (Ssequence
                                                (Sassign
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Efield
                                                        (Efield
                                                          (Evar _vd_raw (Tstruct ___gp_wdict_t noattr))
                                                          _x_valid_dict_api__st
                                                          (Tstruct ___gp_wstate_t noattr))
                                                        _rep
                                                        (tarray tuint 3))
                                                      (Econst_int (Int.repr 2) tint)
                                                      (tptr tuint)) tuint)
                                                  (Econst_int (Int.repr 8) tint))
                                                (Scall None
                                                  (Evar _w_series (Tfunction
                                                                    ((tptr (Tstruct ___gp_wseries_t noattr)) ::
                                                                    (tptr (Tstruct ___gp_wdict_t noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                  ((Eaddrof
                                                     (Evar _x_valid_dict_api__sr (Tstruct ___gp_wseries_t noattr))
                                                     (tptr (Tstruct ___gp_wseries_t noattr))) ::
                                                   (Eaddrof
                                                     (Evar _vd_raw (Tstruct ___gp_wdict_t noattr))
                                                     (tptr (Tstruct ___gp_wdict_t noattr))) ::
                                                   nil))))))))))))
                            (Scall None
                              (Evar _w_series (Tfunction
                                                ((tptr (Tstruct ___gp_wseries_t noattr)) ::
                                                 (tptr (Tstruct ___gp_wdict_t noattr)) ::
                                                 nil) tvoid cc_default))
                              ((Eaddrof
                                 (Evar _x_valid_dict_api__sr (Tstruct ___gp_wseries_t noattr))
                                 (tptr (Tstruct ___gp_wseries_t noattr))) ::
                               (Etempvar _wd (tptr (Tstruct ___gp_wdict_t noattr))) ::
                               nil)))
                          (Ssequence
                            (Sifthenelse (Ebinop Oeq (Etempvar _mode tuint)
                                           (Econst_int (Int.repr 0) tint)
                                           tint)
                              (Ssequence
                                (Sset _k (Econst_int (Int.repr 0) tint))
                                (Sloop
                                  (Ssequence
                                    (Ssequence
                                      (Sset _x_valid_dict_api__t'77
                                        (Efield
                                          (Evar _x_valid_dict_api__sr (Tstruct ___gp_wseries_t noattr))
                                          _nframes tuint))
                                      (Sifthenelse (Ebinop Olt
                                                     (Etempvar _k tuint)
                                                     (Etempvar _x_valid_dict_api__t'77 tuint)
                                                     tint)
                                        Sskip
                                        Sbreak))
                                    (Ssequence
                                      (Ssequence
                                        (Sset _x_valid_dict_api__t'73
                                          (Efield
                                            (Ederef
                                              (Ebinop Oadd
                                                (Efield
                                                  (Evar _x_valid_dict_api__sr (Tstruct ___gp_wseries_t noattr))
                                                  _f
                                                  (tarray (Tstruct ___gp_winfo_t noattr) 4))
                                                (Etempvar _k tuint)
                                                (tptr (Tstruct ___gp_winfo_t noattr)))
                                              (Tstruct ___gp_winfo_t noattr))
                                            _skippable tuint))
                                        (Sifthenelse (Etempvar _x_valid_dict_api__t'73 tuint)
                                          (Sset _x_valid_dict_api__t'7
                                            (Econst_int (Int.repr 1) tint))
                                          (Ssequence
                                            (Sset _x_valid_dict_api__t'74
                                              (Efield
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Efield
                                                      (Evar _x_valid_dict_api__sr (Tstruct ___gp_wseries_t noattr))
                                                      _f
                                                      (tarray (Tstruct ___gp_winfo_t noattr) 4))
                                                    (Etempvar _k tuint)
                                                    (tptr (Tstruct ___gp_winfo_t noattr)))
                                                  (Tstruct ___gp_winfo_t noattr))
                                                _did_size tuint))
                                            (Sifthenelse (Ebinop One
                                                           (Etempvar _x_valid_dict_api__t'74 tuint)
                                                           (Econst_int (Int.repr 0) tint)
                                                           tint)
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _x_valid_dict_api__t'75
                                                    (Efield
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Efield
                                                            (Evar _x_valid_dict_api__sr (Tstruct ___gp_wseries_t noattr))
                                                            _f
                                                            (tarray (Tstruct ___gp_winfo_t noattr) 4))
                                                          (Etempvar _k tuint)
                                                          (tptr (Tstruct ___gp_winfo_t noattr)))
                                                        (Tstruct ___gp_winfo_t noattr))
                                                      _did tuint))
                                                  (Ssequence
                                                    (Sset _x_valid_dict_api__t'76
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _wd (tptr (Tstruct ___gp_wdict_t noattr)))
                                                          (Tstruct ___gp_wdict_t noattr))
                                                        _id tuint))
                                                    (Sset _x_valid_dict_api__t'7
                                                      (Ecast
                                                        (Ebinop Oeq
                                                          (Etempvar _x_valid_dict_api__t'75 tuint)
                                                          (Etempvar _x_valid_dict_api__t'76 tuint)
                                                          tint) tbool))))
                                                (Sset _x_valid_dict_api__t'7
                                                  (Ecast (Etempvar _x_valid_dict_api__t'7 tint)
                                                    tbool)))
                                              (Sset _x_valid_dict_api__t'7
                                                (Ecast
                                                  (Econst_int (Int.repr 0) tint)
                                                  tbool))))))
                                      (Scall None
                                        (Evar _gp_assume (Tfunction
                                                           (tint :: nil)
                                                           tvoid cc_default))
                                        ((Etempvar _x_valid_dict_api__t'7 tint) :: nil))))
                                  (Sset _k
                                    (Ebinop Oadd (Etempvar _k tuint)
                                      (Econst_int (Int.repr 1) tint) tuint))))
                              Sskip)
                            (Ssequence
                              (Sifthenelse (Ebinop Oeq (Etempvar _mode tuint)
                                             (Econst_int (Int.repr 4) tint)
                                             tint)
                                (Ssequence
                                  (Ssequence
                                    (Sset _x_valid_dict_api__t'71
                                      (Efield
                                        (Evar _x_valid_dict_api__sr (Tstruct ___gp_wseries_t noattr))
                                        _nframes tuint))
                                    (Sifthenelse (Ebinop Oeq
                                                   (Etempvar _x_valid_dict_api__t'71 tuint)
                                                   (Econst_int (Int.repr 1) tint)
                                                   tint)
                                      (Ssequence
                                        (Sset _x_valid_dict_api__t'72
                                          (Efield
                                            (Ederef
                                              (Ebinop Oadd
                                                (Efield
                                                  (Evar _x_valid_dict_api__sr (Tstruct ___gp_wseries_t noattr))
                                                  _f
                                                  (tarray (Tstruct ___gp_winfo_t noattr) 4))
                                                (Econst_int (Int.repr 0) tint)
                                                (tptr (Tstruct ___gp_winfo_t noattr)))
                                              (Tstruct ___gp_winfo_t noattr))
                                            _skippable tuint))
                                        (Sset _x_valid_dict_api__t'8
                                          (Ecast
                                            (Eunop Onotbool
                                              (Etempvar _x_valid_dict_api__t'72 tuint) tint)
                                            tbool)))
                                      (Sset _x_valid_dict_api__t'8
                                        (Econst_int (Int.repr 0) tint))))
                                  (Scall None
                                    (Evar _gp_assume (Tfunction (tint :: nil)
                                                       tvoid cc_default))
                                    ((Etempvar _x_valid_dict_api__t'8 tint) :: nil)))
                                Sskip)
                              (Ssequence
                                (Sset _dn
                                  (Efield
                                    (Ederef
                                      (Etempvar _wd (tptr (Tstruct ___gp_wdict_t noattr)))
                                      (Tstruct ___gp_wdict_t noattr)) _n
                                    tulong))
                                (Ssequence
                                  (Ssequence
                                    (Sifthenelse (Ebinop One
                                                   (Etempvar _mode tuint)
                                                   (Econst_int (Int.repr 5) tint)
                                                   tint)
                                      (Sset _x_valid_dict_api__t'10
                                        (Ecast
                                          (Ebinop One (Etempvar _mode tuint)
                                            (Econst_int (Int.repr 6) tint)
                                            tint) tbool))
                                      (Sset _x_valid_dict_api__t'10
                                        (Econst_int (Int.repr 0) tint)))
                                    (Sifthenelse (Etempvar _x_valid_dict_api__t'10 tint)
                                      (Ssequence
                                        (Ssequence
                                          (Sset _x_valid_dict_api__t'70
                                            (Efield
                                              (Evar _x_valid_dict_api__sr (Tstruct ___gp_wseries_t noattr))
                                              _content_n tulong))
                                          (Scall (Some _x_valid_dict_api__t'9)
                                            (Evar _choose_in (Tfunction
                                                               (tulong ::
                                                                tulong ::
                                                                nil) tulong
                                                               cc_default))
                                            ((Econst_int (Int.repr 0) tint) ::
                                             (Ebinop Oadd
                                               (Etempvar _x_valid_dict_api__t'70 tulong)
                                               (Econst_int (Int.repr 16) tint)
                                               tulong) :: nil)))
                                        (Sset _cap (Etempvar _x_valid_dict_api__t'9 tulong)))
                                      Sskip))
                                  (Ssequence
                                    (Ssequence
                                      (Ssequence
                                        (Sset _x_valid_dict_api__t'69
                                          (Efield
                                            (Evar _x_valid_dict_api__sr (Tstruct ___gp_wseries_t noattr))
                                            _n tulong))
                                        (Scall (Some _x_valid_dict_api__t'11)
                                          (Evar _exact_copy (Tfunction
                                                              ((tptr tuchar) ::
                                                               tulong :: nil)
                                                              (tptr tuchar)
                                                              cc_default))
                                          ((Efield
                                             (Evar _x_valid_dict_api__sr (Tstruct ___gp_wseries_t noattr))
                                             _bytes (tarray tuchar 524288)) ::
                                           (Etempvar _x_valid_dict_api__t'69 tulong) :: nil)))
                                      (Sset _src
                                        (Etempvar _x_valid_dict_api__t'11 (tptr tuchar))))
                                    (Ssequence
                                      (Ssequence
                                        (Scall (Some _x_valid_dict_api__t'12)
                                          (Evar _quickproof_malloc (Tfunction
                                                                    (tulong ::
                                                                    nil)
                                                                    (tptr tvoid)
                                                                    cc_default))
                                          ((Ebinop Oadd
                                             (Ebinop Oadd
                                               (Etempvar _cap tulong)
                                               (Econst_int (Int.repr 1) tint)
                                               tulong) (Etempvar _dn tulong)
                                             tulong) :: nil))
                                        (Sset _buf
                                          (Etempvar _x_valid_dict_api__t'12 (tptr tvoid))))
                                      (Ssequence
                                        (Ssequence
                                          (Scall (Some _x_valid_dict_api__t'13)
                                            (Evar _ZSTD_createDCtx (Tfunction
                                                                    nil
                                                                    (tptr (Tstruct _ZSTD_DCtx_s noattr))
                                                                    cc_default))
                                            nil)
                                          (Sset _dctx
                                            (Etempvar _x_valid_dict_api__t'13 (tptr (Tstruct _ZSTD_DCtx_s noattr)))))
                                        (Ssequence
                                          (Sset _dst
                                            (Etempvar _buf (tptr tuchar)))
                                          (Ssequence
                                            (Sset _dict
                                              (Ecast
                                                (Econst_int (Int.repr 0) tint)
                                                (tptr tvoid)))
                                            (Ssequence
                                              (Sifthenelse (Ebinop One
                                                             (Etempvar _buf (tptr tuchar))
                                                             (Ecast
                                                               (Econst_int (Int.repr 0) tint)
                                                               (tptr tvoid))
                                                             tint)
                                                (Sset _dict
                                                  (Ebinop Oadd
                                                    (Ebinop Oadd
                                                      (Etempvar _buf (tptr tuchar))
                                                      (Etempvar _cap tulong)
                                                      (tptr tuchar))
                                                    (Econst_int (Int.repr 1) tint)
                                                    (tptr tuchar)))
                                                Sskip)
                                              (Ssequence
                                                (Ssequence
                                                  (Ssequence
                                                    (Sifthenelse (Ebinop Oeq
                                                                   (Etempvar _src (tptr tuchar))
                                                                   (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                   tint)
                                                      (Sset _x_valid_dict_api__t'14
                                                        (Econst_int (Int.repr 1) tint))
                                                      (Sset _x_valid_dict_api__t'14
                                                        (Ecast
                                                          (Ebinop Oeq
                                                            (Etempvar _buf (tptr tuchar))
                                                            (Ecast
                                                              (Econst_int (Int.repr 0) tint)
                                                              (tptr tvoid))
                                                            tint) tbool)))
                                                    (Sifthenelse (Etempvar _x_valid_dict_api__t'14 tint)
                                                      (Sset _x_valid_dict_api__t'15
                                                        (Econst_int (Int.repr 1) tint))
                                                      (Sset _x_valid_dict_api__t'15
                                                        (Ecast
                                                          (Ebinop Oeq
                                                            (Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr)))
                                                            (Ecast
                                                              (Econst_int (Int.repr 0) tint)
                                                              (tptr tvoid))
                                                            tint) tbool))))
                                                  (Sifthenelse (Etempvar _x_valid_dict_api__t'15 tint)
                                                    (Ssequence
                                                      (Scall None
                                                        (Evar _quickproof_free 
                                                        (Tfunction
                                                          ((tptr tvoid) ::
                                                           nil) tvoid
                                                          cc_default))
                                                        ((Etempvar _src (tptr tuchar)) ::
                                                         nil))
                                                      (Ssequence
                                                        (Scall None
                                                          (Evar _quickproof_free 
                                                          (Tfunction
                                                            ((tptr tvoid) ::
                                                             nil) tvoid
                                                            cc_default))
                                                          ((Etempvar _buf (tptr tuchar)) ::
                                                           nil))
                                                        (Ssequence
                                                          (Scall None
                                                            (Evar _ZSTD_freeDCtx 
                                                            (Tfunction
                                                              ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
                                                               nil) tulong
                                                              cc_default))
                                                            ((Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
                                                             nil))
                                                          (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
                                                    Sskip))
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _j
                                                      (Ecast
                                                        (Econst_int (Int.repr 0) tint)
                                                        tulong))
                                                    (Sloop
                                                      (Ssequence
                                                        (Sifthenelse 
                                                          (Ebinop Olt
                                                            (Etempvar _j tulong)
                                                            (Etempvar _dn tulong)
                                                            tint)
                                                          Sskip
                                                          Sbreak)
                                                        (Ssequence
                                                          (Sset _x_valid_dict_api__t'68
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Efield
                                                                  (Ederef
                                                                    (Etempvar _wd (tptr (Tstruct ___gp_wdict_t noattr)))
                                                                    (Tstruct ___gp_wdict_t noattr))
                                                                  _bytes
                                                                  (tarray tuchar 6144))
                                                                (Etempvar _j tulong)
                                                                (tptr tuchar))
                                                              tuchar))
                                                          (Sassign
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Etempvar _dict (tptr tuchar))
                                                                (Etempvar _j tulong)
                                                                (tptr tuchar))
                                                              tuchar)
                                                            (Etempvar _x_valid_dict_api__t'68 tuchar))))
                                                      (Sset _j
                                                        (Ebinop Oadd
                                                          (Etempvar _j tulong)
                                                          (Econst_int (Int.repr 1) tint)
                                                          tulong))))
                                                  (Ssequence
                                                    (Sifthenelse (Ebinop Oeq
                                                                   (Etempvar _mode tuint)
                                                                   (Econst_int (Int.repr 0) tint)
                                                                   tint)
                                                      (Ssequence
                                                        (Ssequence
                                                          (Scall (Some _x_valid_dict_api__t'16)
                                                            (Evar _ZSTD_DCtx_setParameter 
                                                            (Tfunction
                                                              ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
                                                               tint ::
                                                               tint :: nil)
                                                              tulong
                                                              cc_default))
                                                            ((Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
                                                             (Econst_int (Int.repr 1003) tint) ::
                                                             (Econst_int (Int.repr 1) tint) ::
                                                             nil))
                                                          (Sset _r
                                                            (Etempvar _x_valid_dict_api__t'16 tulong)))
                                                        (Ssequence
                                                          (Ssequence
                                                            (Scall (Some _x_valid_dict_api__t'17)
                                                              (Evar _ZSTD_isError 
                                                              (Tfunction
                                                                (tulong ::
                                                                 nil) tuint
                                                                cc_default))
                                                              ((Etempvar _r tulong) ::
                                                               nil))
                                                            (Scall None
                                                              (Evar _gp_assert 
                                                              (Tfunction
                                                                (tint :: nil)
                                                                tvoid
                                                                cc_default))
                                                              ((Eunop Onotbool
                                                                 (Etempvar _x_valid_dict_api__t'17 tuint)
                                                                 tint) ::
                                                               nil)))
                                                          (Ssequence
                                                            (Sset _i
                                                              (Econst_int (Int.repr 0) tint))
                                                            (Sloop
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _i tuint)
                                                                    (Etempvar _nd tuint)
                                                                    tint)
                                                                    (Sset _x_valid_dict_api__t'18
                                                                    (Ecast
                                                                    (Eunop Onotbool
                                                                    (Etempvar _fail tint)
                                                                    tint)
                                                                    tbool))
                                                                    (Sset _x_valid_dict_api__t'18
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                  (Sifthenelse (Etempvar _x_valid_dict_api__t'18 tint)
                                                                    Sskip
                                                                    Sbreak))
                                                                (Ssequence
                                                                  (Ssequence
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'67
                                                                    (Efield
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _vd_wd (tarray (Tstruct ___gp_wdict_t noattr) 3))
                                                                    (Etempvar _i tuint)
                                                                    (tptr (Tstruct ___gp_wdict_t noattr)))
                                                                    (Tstruct ___gp_wdict_t noattr))
                                                                    _n
                                                                    tulong))
                                                                    (Scall (Some _x_valid_dict_api__t'19)
                                                                    (Evar _ZSTD_createDDict 
                                                                    (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    tulong ::
                                                                    nil)
                                                                    (tptr (Tstruct _ZSTD_DDict_s noattr))
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _vd_wd (tarray (Tstruct ___gp_wdict_t noattr) 3))
                                                                    (Etempvar _i tuint)
                                                                    (tptr (Tstruct ___gp_wdict_t noattr)))
                                                                    (Tstruct ___gp_wdict_t noattr))
                                                                    _bytes
                                                                    (tarray tuchar 6144)) ::
                                                                    (Etempvar _x_valid_dict_api__t'67 tulong) ::
                                                                    nil)))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _dd (tarray (tptr (Tstruct _ZSTD_DDict_s noattr)) 3))
                                                                    (Etempvar _i tuint)
                                                                    (tptr (tptr (Tstruct _ZSTD_DDict_s noattr))))
                                                                    (tptr (Tstruct _ZSTD_DDict_s noattr)))
                                                                    (Etempvar _x_valid_dict_api__t'19 (tptr (Tstruct _ZSTD_DDict_s noattr)))))
                                                                  (Ssequence
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'65
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _dd (tarray (tptr (Tstruct _ZSTD_DDict_s noattr)) 3))
                                                                    (Etempvar _i tuint)
                                                                    (tptr (tptr (Tstruct _ZSTD_DDict_s noattr))))
                                                                    (tptr (Tstruct _ZSTD_DDict_s noattr))))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _x_valid_dict_api__t'65 (tptr (Tstruct _ZSTD_DDict_s noattr)))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    (Sset _x_valid_dict_api__t'20
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'66
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _dd (tarray (tptr (Tstruct _ZSTD_DDict_s noattr)) 3))
                                                                    (Etempvar _i tuint)
                                                                    (tptr (tptr (Tstruct _ZSTD_DDict_s noattr))))
                                                                    (tptr (Tstruct _ZSTD_DDict_s noattr))))
                                                                    (Scall (Some _x_valid_dict_api__t'21)
                                                                    (Evar _ZSTD_DCtx_refDDict 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
                                                                    (tptr (Tstruct _ZSTD_DDict_s noattr)) ::
                                                                    nil)
                                                                    tulong
                                                                    cc_default))
                                                                    ((Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
                                                                    (Etempvar _x_valid_dict_api__t'66 (tptr (Tstruct _ZSTD_DDict_s noattr))) ::
                                                                    nil)))
                                                                    (Scall (Some _x_valid_dict_api__t'22)
                                                                    (Evar _ZSTD_isError 
                                                                    (Tfunction
                                                                    (tulong ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                    ((Etempvar _x_valid_dict_api__t'21 tulong) ::
                                                                    nil)))
                                                                    (Sset _x_valid_dict_api__t'20
                                                                    (Ecast
                                                                    (Etempvar _x_valid_dict_api__t'22 tuint)
                                                                    tbool)))))
                                                                    (Sifthenelse (Etempvar _x_valid_dict_api__t'20 tint)
                                                                    (Sset _fail
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    Sskip))))
                                                              (Sset _i
                                                                (Ebinop Oadd
                                                                  (Etempvar _i tuint)
                                                                  (Econst_int (Int.repr 1) tint)
                                                                  tuint))))))
                                                      (Ssequence
                                                        (Sifthenelse 
                                                          (Ebinop Oeq
                                                            (Etempvar _mode tuint)
                                                            (Econst_int (Int.repr 1) tint)
                                                            tint)
                                                          (Sset _x_valid_dict_api__t'46
                                                            (Econst_int (Int.repr 1) tint))
                                                          (Sset _x_valid_dict_api__t'46
                                                            (Ecast
                                                              (Ebinop Oeq
                                                                (Etempvar _mode tuint)
                                                                (Econst_int (Int.repr 2) tint)
                                                                tint) tbool)))
                                                        (Sifthenelse (Etempvar _x_valid_dict_api__t'46 tint)
                                                          (Ssequence
                                                            (Ssequence
                                                              (Ssequence
                                                                (Scall (Some _x_valid_dict_api__t'23)
                                                                  (Evar _choose 
                                                                  (Tfunction
                                                                    (tuint ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                  ((Econst_int (Int.repr 2) tint) ::
                                                                   nil))
                                                                (Sifthenelse (Etempvar _x_valid_dict_api__t'23 tuint)
                                                                  (Sset _x_valid_dict_api__t'24
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint))
                                                                  (Sset _x_valid_dict_api__t'24
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint))))
                                                              (Sset _m
                                                                (Etempvar _x_valid_dict_api__t'24 tint)))
                                                            (Ssequence
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _mode tuint)
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint)
                                                                    (Sset _x_valid_dict_api__t'25
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    (Ssequence
                                                                    (Scall (Some _x_valid_dict_api__t'26)
                                                                    (Evar _choose 
                                                                    (Tfunction
                                                                    (tuint ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                    ((Econst_int (Int.repr 2) tint) ::
                                                                    nil))
                                                                    (Sset _x_valid_dict_api__t'25
                                                                    (Ecast
                                                                    (Etempvar _x_valid_dict_api__t'26 tuint)
                                                                    tbool))))
                                                                  (Sifthenelse (Etempvar _x_valid_dict_api__t'25 tint)
                                                                    (Sset _x_valid_dict_api__t'27
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint))
                                                                    (Sset _x_valid_dict_api__t'27
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint))))
                                                                (Sset _t__1
                                                                  (Etempvar _x_valid_dict_api__t'27 tint)))
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Scall (Some _x_valid_dict_api__t'28)
                                                                    (Evar _ZSTD_DCtx_loadDictionary_advanced 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
                                                                    (tptr tvoid) ::
                                                                    tulong ::
                                                                    tint ::
                                                                    tint ::
                                                                    nil)
                                                                    tulong
                                                                    cc_default))
                                                                    ((Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
                                                                    (Etempvar _dict (tptr tuchar)) ::
                                                                    (Etempvar _dn tulong) ::
                                                                    (Etempvar _m tint) ::
                                                                    (Etempvar _t__1 tint) ::
                                                                    nil))
                                                                  (Scall (Some _x_valid_dict_api__t'29)
                                                                    (Evar _ZSTD_isError 
                                                                    (Tfunction
                                                                    (tulong ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                    ((Etempvar _x_valid_dict_api__t'28 tulong) ::
                                                                    nil)))
                                                                (Sset _fail
                                                                  (Etempvar _x_valid_dict_api__t'29 tuint)))))
                                                          (Sifthenelse 
                                                            (Ebinop Oeq
                                                              (Etempvar _mode tuint)
                                                              (Econst_int (Int.repr 3) tint)
                                                              tint)
                                                            (Ssequence
                                                              (Ssequence
                                                                (Scall (Some _x_valid_dict_api__t'34)
                                                                  (Evar _choose 
                                                                  (Tfunction
                                                                    (tuint ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                  ((Econst_int (Int.repr 2) tint) ::
                                                                   nil))
                                                                (Sifthenelse (Etempvar _x_valid_dict_api__t'34 tuint)
                                                                  (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _x_valid_dict_api__t'30)
                                                                    (Evar _choose 
                                                                    (Tfunction
                                                                    (tuint ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                    ((Econst_int (Int.repr 2) tint) ::
                                                                    nil))
                                                                    (Sifthenelse (Etempvar _x_valid_dict_api__t'30 tuint)
                                                                    (Sset _x_valid_dict_api__t'31
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint))
                                                                    (Sset _x_valid_dict_api__t'31
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint))))
                                                                    (Scall (Some _x_valid_dict_api__t'32)
                                                                    (Evar _ZSTD_DCtx_loadDictionary_advanced 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
                                                                    (tptr tvoid) ::
                                                                    tulong ::
                                                                    tint ::
                                                                    tint ::
                                                                    nil)
                                                                    tulong
                                                                    cc_default))
                                                                    ((Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
                                                                    (Etempvar _dict (tptr tuchar)) ::
                                                                    (Etempvar _dn tulong) ::
                                                                    (Etempvar _x_valid_dict_api__t'31 tint) ::
                                                                    (Econst_int (Int.repr 2) tint) ::
                                                                    nil)))
                                                                    (Sset _r
                                                                    (Etempvar _x_valid_dict_api__t'32 tulong)))
                                                                  (Ssequence
                                                                    (Scall (Some _x_valid_dict_api__t'33)
                                                                    (Evar _ZSTD_DCtx_refPrefix_advanced 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
                                                                    (tptr tvoid) ::
                                                                    tulong ::
                                                                    tint ::
                                                                    nil)
                                                                    tulong
                                                                    cc_default))
                                                                    ((Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
                                                                    (Etempvar _dict (tptr tuchar)) ::
                                                                    (Etempvar _dn tulong) ::
                                                                    (Econst_int (Int.repr 2) tint) ::
                                                                    nil))
                                                                    (Sset _r
                                                                    (Etempvar _x_valid_dict_api__t'33 tulong)))))
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Scall (Some _x_valid_dict_api__t'35)
                                                                    (Evar _ZSTD_isError 
                                                                    (Tfunction
                                                                    (tulong ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                    ((Etempvar _r tulong) ::
                                                                    nil))
                                                                  (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _x_valid_dict_api__t'35 tuint) ::
                                                                    nil)))
                                                                (Sset _fail
                                                                  (Econst_int (Int.repr 1) tint))))
                                                            (Sifthenelse 
                                                              (Ebinop Oeq
                                                                (Etempvar _mode tuint)
                                                                (Econst_int (Int.repr 4) tint)
                                                                tint)
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _x_valid_dict_api__t'36)
                                                                    (Evar _choose 
                                                                    (Tfunction
                                                                    (tuint ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                    ((Econst_int (Int.repr 2) tint) ::
                                                                    nil))
                                                                    (Sifthenelse (Etempvar _x_valid_dict_api__t'36 tuint)
                                                                    (Sset _x_valid_dict_api__t'37
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint))
                                                                    (Sset _x_valid_dict_api__t'37
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint))))
                                                                    (Scall (Some _x_valid_dict_api__t'38)
                                                                    (Evar _ZSTD_DCtx_refPrefix_advanced 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
                                                                    (tptr tvoid) ::
                                                                    tulong ::
                                                                    tint ::
                                                                    nil)
                                                                    tulong
                                                                    cc_default))
                                                                    ((Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
                                                                    (Etempvar _dict (tptr tuchar)) ::
                                                                    (Etempvar _dn tulong) ::
                                                                    (Etempvar _x_valid_dict_api__t'37 tint) ::
                                                                    nil)))
                                                                  (Scall (Some _x_valid_dict_api__t'39)
                                                                    (Evar _ZSTD_isError 
                                                                    (Tfunction
                                                                    (tulong ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                    ((Etempvar _x_valid_dict_api__t'38 tulong) ::
                                                                    nil)))
                                                                (Sset _fail
                                                                  (Etempvar _x_valid_dict_api__t'39 tuint)))
                                                              (Sifthenelse 
                                                                (Ebinop Oeq
                                                                  (Etempvar _mode tuint)
                                                                  (Econst_int (Int.repr 5) tint)
                                                                  tint)
                                                                (Ssequence
                                                                  (Ssequence
                                                                    (Scall (Some _x_valid_dict_api__t'40)
                                                                    (Evar _ZSTD_initDStream_usingDict 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
                                                                    (tptr tvoid) ::
                                                                    tulong ::
                                                                    nil)
                                                                    tulong
                                                                    cc_default))
                                                                    ((Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
                                                                    (Etempvar _dict (tptr tuchar)) ::
                                                                    (Etempvar _dn tulong) ::
                                                                    nil))
                                                                    (Scall (Some _x_valid_dict_api__t'41)
                                                                    (Evar _ZSTD_isError 
                                                                    (Tfunction
                                                                    (tulong ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                    ((Etempvar _x_valid_dict_api__t'40 tulong) ::
                                                                    nil)))
                                                                  (Sset _fail
                                                                    (Etempvar _x_valid_dict_api__t'41 tuint)))
                                                                (Ssequence
                                                                  (Ssequence
                                                                    (Scall (Some _x_valid_dict_api__t'42)
                                                                    (Evar _ZSTD_createDDict 
                                                                    (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    tulong ::
                                                                    nil)
                                                                    (tptr (Tstruct _ZSTD_DDict_s noattr))
                                                                    cc_default))
                                                                    ((Etempvar _dict (tptr tuchar)) ::
                                                                    (Etempvar _dn tulong) ::
                                                                    nil))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _dd (tarray (tptr (Tstruct _ZSTD_DDict_s noattr)) 3))
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr (tptr (Tstruct _ZSTD_DDict_s noattr))))
                                                                    (tptr (Tstruct _ZSTD_DDict_s noattr)))
                                                                    (Etempvar _x_valid_dict_api__t'42 (tptr (Tstruct _ZSTD_DDict_s noattr)))))
                                                                  (Ssequence
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'63
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _dd (tarray (tptr (Tstruct _ZSTD_DDict_s noattr)) 3))
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr (tptr (Tstruct _ZSTD_DDict_s noattr))))
                                                                    (tptr (Tstruct _ZSTD_DDict_s noattr))))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _x_valid_dict_api__t'63 (tptr (Tstruct _ZSTD_DDict_s noattr)))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    (Sset _x_valid_dict_api__t'43
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'64
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _dd (tarray (tptr (Tstruct _ZSTD_DDict_s noattr)) 3))
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr (tptr (Tstruct _ZSTD_DDict_s noattr))))
                                                                    (tptr (Tstruct _ZSTD_DDict_s noattr))))
                                                                    (Scall (Some _x_valid_dict_api__t'44)
                                                                    (Evar _ZSTD_initDStream_usingDDict 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
                                                                    (tptr (Tstruct _ZSTD_DDict_s noattr)) ::
                                                                    nil)
                                                                    tulong
                                                                    cc_default))
                                                                    ((Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
                                                                    (Etempvar _x_valid_dict_api__t'64 (tptr (Tstruct _ZSTD_DDict_s noattr))) ::
                                                                    nil)))
                                                                    (Scall (Some _x_valid_dict_api__t'45)
                                                                    (Evar _ZSTD_isError 
                                                                    (Tfunction
                                                                    (tulong ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                    ((Etempvar _x_valid_dict_api__t'44 tulong) ::
                                                                    nil)))
                                                                    (Sset _x_valid_dict_api__t'43
                                                                    (Ecast
                                                                    (Etempvar _x_valid_dict_api__t'45 tuint)
                                                                    tbool)))))
                                                                    (Sset _fail
                                                                    (Etempvar _x_valid_dict_api__t'43 tint))))))))))
                                                    (Ssequence
                                                      (Sifthenelse (Eunop Onotbool
                                                                    (Etempvar _fail tint)
                                                                    tint)
                                                        (Ssequence
                                                          (Sifthenelse 
                                                            (Ebinop Oeq
                                                              (Etempvar _mode tuint)
                                                              (Econst_int (Int.repr 5) tint)
                                                              tint)
                                                            (Sset _x_valid_dict_api__t'56
                                                              (Econst_int (Int.repr 1) tint))
                                                            (Sset _x_valid_dict_api__t'56
                                                              (Ecast
                                                                (Ebinop Oeq
                                                                  (Etempvar _mode tuint)
                                                                  (Econst_int (Int.repr 6) tint)
                                                                  tint)
                                                                tbool)))
                                                          (Sifthenelse (Etempvar _x_valid_dict_api__t'56 tint)
                                                            (Ssequence
                                                              (Scall None
                                                                (Evar _vd_stream 
                                                                (Tfunction
                                                                  ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
                                                                   (tptr tuchar) ::
                                                                   nil) tvoid
                                                                  cc_default))
                                                                ((Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
                                                                 (Etempvar _src (tptr tuchar)) ::
                                                                 nil))
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Scall (Some _x_valid_dict_api__t'47)
                                                                    (Evar _ZSTD_resetDStream 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
                                                                    nil)
                                                                    tulong
                                                                    cc_default))
                                                                    ((Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
                                                                    nil))
                                                                  (Scall (Some _x_valid_dict_api__t'48)
                                                                    (Evar _ZSTD_isError 
                                                                    (Tfunction
                                                                    (tulong ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                    ((Etempvar _x_valid_dict_api__t'47 tulong) ::
                                                                    nil)))
                                                                (Sifthenelse 
                                                                  (Eunop Onotbool
                                                                    (Etempvar _x_valid_dict_api__t'48 tuint)
                                                                    tint)
                                                                  (Scall None
                                                                    (Evar _vd_stream 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
                                                                    (tptr tuchar) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
                                                                    (Etempvar _src (tptr tuchar)) ::
                                                                    nil))
                                                                  Sskip)))
                                                            (Ssequence
                                                              (Sifthenelse 
                                                                (Ebinop Oeq
                                                                  (Etempvar _mode tuint)
                                                                  (Econst_int (Int.repr 0) tint)
                                                                  tint)
                                                                (Ssequence
                                                                  (Scall (Some _x_valid_dict_api__t'55)
                                                                    (Evar _choose 
                                                                    (Tfunction
                                                                    (tuint ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                    ((Econst_int (Int.repr 2) tint) ::
                                                                    nil))
                                                                  (Sset _x_valid_dict_api__t'54
                                                                    (Ecast
                                                                    (Etempvar _x_valid_dict_api__t'55 tuint)
                                                                    tbool)))
                                                                (Sset _x_valid_dict_api__t'54
                                                                  (Econst_int (Int.repr 0) tint)))
                                                              (Sifthenelse (Etempvar _x_valid_dict_api__t'54 tint)
                                                                (Scall None
                                                                  (Evar _vd_stream 
                                                                  (Tfunction
                                                                    ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
                                                                    (tptr tuchar) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                  ((Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
                                                                   (Etempvar _src (tptr tuchar)) ::
                                                                   nil))
                                                                (Ssequence
                                                                  (Ssequence
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'62
                                                                    (Efield
                                                                    (Evar _x_valid_dict_api__sr (Tstruct ___gp_wseries_t noattr))
                                                                    _n
                                                                    tulong))
                                                                    (Scall (Some _x_valid_dict_api__t'49)
                                                                    (Evar _ZSTD_decompressDCtx 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
                                                                    (tptr tvoid) ::
                                                                    tulong ::
                                                                    (tptr tvoid) ::
                                                                    tulong ::
                                                                    nil)
                                                                    tulong
                                                                    cc_default))
                                                                    ((Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
                                                                    (Etempvar _dst (tptr tuchar)) ::
                                                                    (Etempvar _cap tulong) ::
                                                                    (Etempvar _src (tptr tuchar)) ::
                                                                    (Etempvar _x_valid_dict_api__t'62 tulong) ::
                                                                    nil)))
                                                                    (Sset _r
                                                                    (Etempvar _x_valid_dict_api__t'49 tulong)))
                                                                  (Ssequence
                                                                    (Scall (Some _x_valid_dict_api__t'53)
                                                                    (Evar _ZSTD_isError 
                                                                    (Tfunction
                                                                    (tulong ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                    ((Etempvar _r tulong) ::
                                                                    nil))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _x_valid_dict_api__t'53 tuint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'61
                                                                    (Efield
                                                                    (Evar _x_valid_dict_api__sr (Tstruct ___gp_wseries_t noattr))
                                                                    _content_n
                                                                    tulong))
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Ebinop Oeq
                                                                    (Etempvar _r tulong)
                                                                    (Etempvar _x_valid_dict_api__t'61 tulong)
                                                                    tint) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Sset _j
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tulong))
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _j tulong)
                                                                    (Etempvar _r tulong)
                                                                    tint)
                                                                    Sskip
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'59
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _dst (tptr tuchar))
                                                                    (Etempvar _j tulong)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'60
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _x_valid_dict_api__sr (Tstruct ___gp_wseries_t noattr))
                                                                    _content
                                                                    (tarray tuchar 262144))
                                                                    (Etempvar _j tulong)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Ebinop Oeq
                                                                    (Etempvar _x_valid_dict_api__t'59 tuchar)
                                                                    (Etempvar _x_valid_dict_api__t'60 tuchar)
                                                                    tint) ::
                                                                    nil)))))
                                                                    (Sset _j
                                                                    (Ebinop Oadd
                                                                    (Etempvar _j tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong)))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _x_valid_dict_api__t'58
                                                                    (Efield
                                                                    (Evar _x_valid_dict_api__sr (Tstruct ___gp_wseries_t noattr))
                                                                    _content_n
                                                                    tulong))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oge
                                                                    (Etempvar _cap tulong)
                                                                    (Etempvar _x_valid_dict_api__t'58 tulong)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall (Some _x_valid_dict_api__t'52)
                                                                    (Evar _within_oneshot 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct ___gp_wseries_t noattr)) ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _x_valid_dict_api__sr (Tstruct ___gp_wseries_t noattr))
                                                                    (tptr (Tstruct ___gp_wseries_t noattr))) ::
                                                                    nil))
                                                                    (Sset _x_valid_dict_api__t'51
                                                                    (Ecast
                                                                    (Etempvar _x_valid_dict_api__t'52 tint)
                                                                    tbool)))
                                                                    (Sset _x_valid_dict_api__t'51
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse (Etempvar _x_valid_dict_api__t'51 tint)
                                                                    (Ssequence
                                                                    (Scall (Some _x_valid_dict_api__t'50)
                                                                    (Evar _ZSTD_getErrorCode 
                                                                    (Tfunction
                                                                    (tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Etempvar _r tulong) ::
                                                                    nil))
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Ebinop Oeq
                                                                    (Etempvar _x_valid_dict_api__t'50 tint)
                                                                    (Econst_int (Int.repr 64) tint)
                                                                    tint) ::
                                                                    nil)))
                                                                    Sskip)))))))))
                                                        Sskip)
                                                      (Ssequence
                                                        (Scall None
                                                          (Evar _ZSTD_freeDCtx 
                                                          (Tfunction
                                                            ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
                                                             nil) tulong
                                                            cc_default))
                                                          ((Etempvar _dctx (tptr (Tstruct _ZSTD_DCtx_s noattr))) ::
                                                           nil))
                                                        (Ssequence
                                                          (Ssequence
                                                            (Sset _i
                                                              (Econst_int (Int.repr 0) tint))
                                                            (Sloop
                                                              (Ssequence
                                                                (Sifthenelse 
                                                                  (Ebinop Olt
                                                                    (Etempvar _i tuint)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tint)
                                                                  Sskip
                                                                  Sbreak)
                                                                (Ssequence
                                                                  (Sset _x_valid_dict_api__t'57
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _dd (tarray (tptr (Tstruct _ZSTD_DDict_s noattr)) 3))
                                                                    (Etempvar _i tuint)
                                                                    (tptr (tptr (Tstruct _ZSTD_DDict_s noattr))))
                                                                    (tptr (Tstruct _ZSTD_DDict_s noattr))))
                                                                  (Scall None
                                                                    (Evar _ZSTD_freeDDict 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _ZSTD_DDict_s noattr)) ::
                                                                    nil)
                                                                    tulong
                                                                    cc_default))
                                                                    ((Etempvar _x_valid_dict_api__t'57 (tptr (Tstruct _ZSTD_DDict_s noattr))) ::
                                                                    nil))))
                                                              (Sset _i
                                                                (Ebinop Oadd
                                                                  (Etempvar _i tuint)
                                                                  (Econst_int (Int.repr 1) tint)
                                                                  tuint))))
                                                          (Ssequence
                                                            (Scall None
                                                              (Evar _quickproof_free 
                                                              (Tfunction
                                                                ((tptr tvoid) ::
                                                                 nil) tvoid
                                                                cc_default))
                                                              ((Etempvar _src (tptr tuchar)) ::
                                                               nil))
                                                            (Ssequence
                                                              (Scall None
                                                                (Evar _quickproof_free 
                                                                (Tfunction
                                                                  ((tptr tvoid) ::
                                                                   nil) tvoid
                                                                  cc_default))
                                                                ((Etempvar _buf (tptr tuchar)) ::
                                                                 nil))
                                                              (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))))))))))))))))))))))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition composites : list composite_definition :=
(Composite ___gp_out_t Struct
   (Member_plain _p (tptr tuchar) :: Member_plain _n tulong ::
    Member_plain _cap tulong :: nil)
   noattr ::
 Composite ___gp_bits_t Struct
   (Member_plain _o (tptr (Tstruct ___gp_out_t noattr)) ::
    Member_plain _acc tulong :: Member_plain _bits tuint :: nil)
   noattr ::
 Composite ___gp_fse_t Struct
   (Member_plain _norm (tarray tshort 53) :: Member_plain _nsym tuint ::
    Member_plain _log tuint :: Member_plain _sym (tarray tuchar 512) ::
    Member_plain _nb (tarray tuchar 512) ::
    Member_plain _base (tarray tushort 512) :: nil)
   noattr ::
 Composite ___gp_huf_t Struct
   (Member_plain _w (tarray tuchar 256) ::
    Member_plain _code (tarray tushort 256) ::
    Member_plain _nb (tarray tuchar 256) :: Member_plain _last tuint ::
    Member_plain _log tuint :: Member_plain _used (tarray tuchar 256) ::
    Member_plain _nused tuint :: nil)
   noattr ::
 Composite ___gp_wstate_t Struct
   (Member_plain _rep (tarray tuint 3) ::
    Member_plain _huf (Tstruct ___gp_huf_t noattr) ::
    Member_plain _have_huf tint ::
    Member_plain _tab (tarray (Tstruct ___gp_fse_t noattr) 3) ::
    Member_plain _have_tab tint :: nil)
   noattr ::
 Composite ___gp_wdict_t Struct
   (Member_plain _bytes (tarray tuchar 6144) :: Member_plain _n tulong ::
    Member_plain _formatted tint :: Member_plain _id tuint ::
    Member_plain _content (tptr tuchar) :: Member_plain _content_n tulong ::
    Member_plain _x_valid_dict_api__st (Tstruct ___gp_wstate_t noattr) :: nil)
   noattr ::
 Composite ___gp_winfo_t Struct
   (Member_plain _skippable tuint :: Member_plain _variant tuint ::
    Member_plain _start tulong :: Member_plain _size tulong ::
    Member_plain _cstart tulong :: Member_plain _csize tulong ::
    Member_plain _fcs_present tint :: Member_plain _fcs tulong ::
    Member_plain _did_size tuint :: Member_plain _did tuint ::
    Member_plain _single tint :: Member_plain _window tulong ::
    Member_plain _window_log tuint :: Member_plain _checksum tuint ::
    Member_plain _blocks tuint :: Member_plain _skip_n tulong ::
    Member_plain _hsize tulong :: Member_plain _uses_dict tint :: nil)
   noattr ::
 Composite ___gp_wseries_t Struct
   (Member_plain _bytes (tarray tuchar 524288) :: Member_plain _n tulong ::
    Member_plain _content (tarray tuchar 262144) ::
    Member_plain _content_n tulong ::
    Member_plain _f (tarray (Tstruct ___gp_winfo_t noattr) 4) ::
    Member_plain _nframes tuint :: nil)
   noattr ::
 Composite _ZSTD_inBuffer_s Struct
   (Member_plain _src (tptr tvoid) :: Member_plain _size tulong ::
    Member_plain _pos tulong :: nil)
   noattr ::
 Composite _ZSTD_outBuffer_s Struct
   (Member_plain _dst (tptr tvoid) :: Member_plain _size tulong ::
    Member_plain _pos tulong :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___compcert_va_int32,
   Gfun(External (EF_runtime "__compcert_va_int32"
                   (mksignature (AST.Xptr :: nil) AST.Xint cc_default))
     ((tptr tvoid) :: nil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_runtime "__compcert_va_int64"
                   (mksignature (AST.Xptr :: nil) AST.Xlong cc_default))
     ((tptr tvoid) :: nil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_runtime "__compcert_va_float64"
                   (mksignature (AST.Xptr :: nil) AST.Xfloat cc_default))
     ((tptr tvoid) :: nil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_runtime "__compcert_va_composite"
                   (mksignature (AST.Xptr :: AST.Xlong :: nil) AST.Xptr
                     cc_default)) ((tptr tvoid) :: tulong :: nil)
     (tptr tvoid) cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Xfloat :: nil) AST.Xlong cc_default))
     (tdouble :: nil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Xfloat :: nil) AST.Xlong cc_default))
     (tdouble :: nil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Xlong :: nil) AST.Xfloat cc_default))
     (tlong :: nil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Xlong :: nil) AST.Xfloat cc_default))
     (tulong :: nil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Xlong :: nil) AST.Xsingle cc_default))
     (tlong :: nil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Xlong :: nil) AST.Xsingle cc_default))
     (tulong :: nil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tlong :: tint :: nil) tlong cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tulong :: tint :: nil) tulong cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tlong :: tint :: nil) tlong cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___builtin_ais_annot,
   Gfun(External (EF_builtin "__builtin_ais_annot"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     ((tptr tschar) :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Xlong :: nil) AST.Xlong cc_default))
     (tulong :: nil) tulong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Xint16unsigned :: nil)
                     AST.Xint16unsigned cc_default)) (tushort :: nil) tushort
     cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fabsf,
   Gfun(External (EF_builtin "__builtin_fabsf"
                   (mksignature (AST.Xsingle :: nil) AST.Xsingle cc_default))
     (tfloat :: nil) tfloat cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_sqrt,
   Gfun(External (EF_builtin "__builtin_sqrt"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Xptr :: AST.Xptr :: AST.Xlong :: AST.Xlong :: nil)
                     AST.Xvoid cc_default))
     ((tptr tvoid) :: (tptr tvoid) :: tulong :: tulong :: nil) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Xbool :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (tbool :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     ((tptr tschar) :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xint
                     cc_default)) ((tptr tschar) :: tint :: nil) tint
     cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Xvoid cc_default)) nil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr tvoid) :: nil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xvoid
                     cc_default)) ((tptr tvoid) :: tuint :: nil) tvoid
     cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xvoid
                     cc_default)) ((tptr tvoid) :: (tptr tvoid) :: nil) tvoid
     cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr tvoid) :: nil) tvoid cc_default)) ::
 (___builtin_unreachable,
   Gfun(External (EF_builtin "__builtin_unreachable"
                   (mksignature nil AST.Xvoid cc_default)) nil tvoid
     cc_default)) ::
 (___builtin_expect,
   Gfun(External (EF_builtin "__builtin_expect"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Xfloat :: AST.Xfloat :: nil) AST.Xfloat
                     cc_default)) (tdouble :: tdouble :: nil) tdouble
     cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Xfloat :: AST.Xfloat :: nil) AST.Xfloat
                     cc_default)) (tdouble :: tdouble :: nil) tdouble
     cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Xptr :: nil) AST.Xint16unsigned
                     cc_default)) ((tptr tushort) :: nil) tushort
     cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Xptr :: nil) AST.Xint cc_default))
     ((tptr tuint) :: nil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Xptr :: AST.Xint16unsigned :: nil)
                     AST.Xvoid cc_default))
     ((tptr tushort) :: tushort :: nil) tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xvoid
                     cc_default)) ((tptr tuint) :: tuint :: nil) tvoid
     cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Xint :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (tint :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_quickproof_malloc,
   Gfun(External (EF_external "quickproof_malloc"
                   (mksignature (AST.Xlong :: nil) AST.Xptr cc_default))
     (tulong :: nil) (tptr tvoid) cc_default)) ::
 (_quickproof_free,
   Gfun(External (EF_external "quickproof_free"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr tvoid) :: nil) tvoid cc_default)) ::
 (_nondet_u32,
   Gfun(External (EF_external "nondet_u32"
                   (mksignature nil AST.Xint cc_default)) nil tuint
     cc_default)) ::
 (_gp_assert,
   Gfun(External (EF_external "gp_assert"
                   (mksignature (AST.Xint :: nil) AST.Xvoid cc_default))
     (tint :: nil) tvoid cc_default)) ::
 (_gp_assume,
   Gfun(External (EF_external "gp_assume"
                   (mksignature (AST.Xint :: nil) AST.Xvoid cc_default))
     (tint :: nil) tvoid cc_default)) ::
 (_choose, Gfun(Internal f_choose)) ::
 (_choose_in, Gfun(Internal f_choose_in)) ::
 (_highbit, Gfun(Internal f_highbit)) :: (_put8, Gfun(Internal f_put8)) ::
 (_put_le, Gfun(Internal f_put_le)) ::
 (_put_bytes, Gfun(Internal f_put_bytes)) ::
 (_bits_put, Gfun(Internal f_bits_put)) ::
 (_bits_end_mark, Gfun(Internal f_bits_end_mark)) ::
 (_bits_pad, Gfun(Internal f_bits_pad)) ::
 (_xrotl, Gfun(Internal f_xrotl)) :: (_xread, Gfun(Internal f_xread)) ::
 (_xround, Gfun(Internal f_xround)) :: (_xmerge, Gfun(Internal f_xmerge)) ::
 (_xxh64, Gfun(Internal f_xxh64)) ::
 (_fse_build, Gfun(Internal f_fse_build)) ::
 (_fse_rle, Gfun(Internal f_fse_rle)) ::
 (_fse_has, Gfun(Internal f_fse_has)) ::
 (_fse_pick, Gfun(Internal f_fse_pick)) ::
 (_fse_put_description, Gfun(Internal f_fse_put_description)) ::
 (_fse_states, Gfun(Internal f_fse_states)) :: (_x_valid_dict_api__pre_LL, Gvar v_x_valid_dict_api__pre_LL) ::
 (_x_valid_dict_api__pre_ML, Gvar v_x_valid_dict_api__pre_ML) :: (_x_valid_dict_api__pre_OF, Gvar v_x_valid_dict_api__pre_OF) ::
 (_fse_predefined, Gfun(Internal f_fse_predefined)) ::
 (_huf_pick, Gfun(Internal f_huf_pick)) :: (_x_valid_dict_api__t, Gvar v_x_valid_dict_api__t) ::
 (_x_valid_dict_api__need, Gvar v_x_valid_dict_api__need) :: (_x_valid_dict_api__wv, Gvar v_x_valid_dict_api__wv) :: (_x_valid_dict_api__st, Gvar v_x_valid_dict_api__st) ::
 (_huf_put_fse_weights, Gfun(Internal f_huf_put_fse_weights)) ::
 (_x_valid_dict_api__tmp, Gvar v_x_valid_dict_api__tmp) ::
 (_huf_put_description, Gfun(Internal f_huf_put_description)) ::
 (_huf_put_stream, Gfun(Internal f_huf_put_stream)) ::
 (_put_literals_raw_rle, Gfun(Internal f_put_literals_raw_rle)) ::
 (_x_valid_dict_api__tmp__1, Gvar v_x_valid_dict_api__tmp__1) ::
 (_put_literals_huf, Gfun(Internal f_put_literals_huf)) ::
 (_x_valid_dict_api__W_LL_base, Gvar v_x_valid_dict_api__W_LL_base) :: (_x_valid_dict_api__W_LL_bits, Gvar v_x_valid_dict_api__W_LL_bits) ::
 (_x_valid_dict_api__W_ML_base, Gvar v_x_valid_dict_api__W_ML_base) :: (_x_valid_dict_api__W_ML_bits, Gvar v_x_valid_dict_api__W_ML_bits) ::
 (_ll_code, Gfun(Internal f_ll_code)) ::
 (_ml_code, Gfun(Internal f_ml_code)) ::
 (_fse_copy, Gfun(Internal f_fse_copy)) ::
 (_huf_copy, Gfun(Internal f_huf_copy)) ::
 (_wstate_copy, Gfun(Internal f_wstate_copy)) ::
 (_x_valid_dict_api__need__1, Gvar v_x_valid_dict_api__need__1) :: (_x_valid_dict_api__maxsym, Gvar v_x_valid_dict_api__maxsym) ::
 (_x_valid_dict_api__maxlog, Gvar v_x_valid_dict_api__maxlog) :: (_x_valid_dict_api__order, Gvar v_x_valid_dict_api__order) ::
 (_w_dict, Gfun(Internal f_w_dict)) :: (_x_valid_dict_api__w_hist, Gvar v_x_valid_dict_api__w_hist) ::
 (_x_valid_dict_api__w_code, Gvar v_x_valid_dict_api__w_code) :: (_x_valid_dict_api__w_extra, Gvar v_x_valid_dict_api__w_extra) ::
 (_x_valid_dict_api__w_st, Gvar v_x_valid_dict_api__w_st) :: (_x_valid_dict_api__w_lit, Gvar v_x_valid_dict_api__w_lit) ::
 (_x_valid_dict_api__blk_buf, Gvar v_x_valid_dict_api__blk_buf) :: (_x_valid_dict_api__need__2, Gvar v_x_valid_dict_api__need__2) ::
 (_x_valid_dict_api__newhuf, Gvar v_x_valid_dict_api__newhuf) :: (_x_valid_dict_api__ntab, Gvar v_x_valid_dict_api__ntab) ::
 (_x_valid_dict_api__maxsym__1, Gvar v_x_valid_dict_api__maxsym__1) :: (_x_valid_dict_api__maxlog__1, Gvar v_x_valid_dict_api__maxlog__1) ::
 (_x_valid_dict_api__upd, Gvar v_x_valid_dict_api__upd) ::
 (_w_compressed_block, Gfun(Internal f_w_compressed_block)) ::
 (_x_valid_dict_api__hdr, Gvar v_x_valid_dict_api__hdr) :: (_w_frame, Gfun(Internal f_w_frame)) ::
 (_w_series, Gfun(Internal f_w_series)) ::
 (_ZSTD_isError,
   Gfun(External (EF_external "ZSTD_isError"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tuint cc_default)) ::
 (_ZSTD_getErrorCode,
   Gfun(External (EF_external "ZSTD_getErrorCode"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (_ZSTD_createDCtx,
   Gfun(External (EF_external "ZSTD_createDCtx"
                   (mksignature nil AST.Xptr cc_default)) nil
     (tptr (Tstruct _ZSTD_DCtx_s noattr)) cc_default)) ::
 (_ZSTD_freeDCtx,
   Gfun(External (EF_external "ZSTD_freeDCtx"
                   (mksignature (AST.Xptr :: nil) AST.Xlong cc_default))
     ((tptr (Tstruct _ZSTD_DCtx_s noattr)) :: nil) tulong cc_default)) ::
 (_ZSTD_decompressDCtx,
   Gfun(External (EF_external "ZSTD_decompressDCtx"
                   (mksignature
                     (AST.Xptr :: AST.Xptr :: AST.Xlong :: AST.Xptr ::
                      AST.Xlong :: nil) AST.Xlong cc_default))
     ((tptr (Tstruct _ZSTD_DCtx_s noattr)) :: (tptr tvoid) :: tulong ::
      (tptr tvoid) :: tulong :: nil) tulong cc_default)) ::
 (_ZSTD_DCtx_setParameter,
   Gfun(External (EF_external "ZSTD_DCtx_setParameter"
                   (mksignature (AST.Xptr :: AST.Xint :: AST.Xint :: nil)
                     AST.Xlong cc_default))
     ((tptr (Tstruct _ZSTD_DCtx_s noattr)) :: tint :: tint :: nil) tulong
     cc_default)) ::
 (_ZSTD_decompressStream,
   Gfun(External (EF_external "ZSTD_decompressStream"
                   (mksignature (AST.Xptr :: AST.Xptr :: AST.Xptr :: nil)
                     AST.Xlong cc_default))
     ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
      (tptr (Tstruct _ZSTD_outBuffer_s noattr)) ::
      (tptr (Tstruct _ZSTD_inBuffer_s noattr)) :: nil) tulong cc_default)) ::
 (_ZSTD_createDDict,
   Gfun(External (EF_external "ZSTD_createDDict"
                   (mksignature (AST.Xptr :: AST.Xlong :: nil) AST.Xptr
                     cc_default)) ((tptr tvoid) :: tulong :: nil)
     (tptr (Tstruct _ZSTD_DDict_s noattr)) cc_default)) ::
 (_ZSTD_freeDDict,
   Gfun(External (EF_external "ZSTD_freeDDict"
                   (mksignature (AST.Xptr :: nil) AST.Xlong cc_default))
     ((tptr (Tstruct _ZSTD_DDict_s noattr)) :: nil) tulong cc_default)) ::
 (_ZSTD_DCtx_refDDict,
   Gfun(External (EF_external "ZSTD_DCtx_refDDict"
                   (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xlong
                     cc_default))
     ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
      (tptr (Tstruct _ZSTD_DDict_s noattr)) :: nil) tulong cc_default)) ::
 (_ZSTD_DCtx_loadDictionary_advanced,
   Gfun(External (EF_external "ZSTD_DCtx_loadDictionary_advanced"
                   (mksignature
                     (AST.Xptr :: AST.Xptr :: AST.Xlong :: AST.Xint ::
                      AST.Xint :: nil) AST.Xlong cc_default))
     ((tptr (Tstruct _ZSTD_DCtx_s noattr)) :: (tptr tvoid) :: tulong ::
      tint :: tint :: nil) tulong cc_default)) ::
 (_ZSTD_DCtx_refPrefix_advanced,
   Gfun(External (EF_external "ZSTD_DCtx_refPrefix_advanced"
                   (mksignature
                     (AST.Xptr :: AST.Xptr :: AST.Xlong :: AST.Xint :: nil)
                     AST.Xlong cc_default))
     ((tptr (Tstruct _ZSTD_DCtx_s noattr)) :: (tptr tvoid) :: tulong ::
      tint :: nil) tulong cc_default)) ::
 (_ZSTD_initDStream_usingDict,
   Gfun(External (EF_external "ZSTD_initDStream_usingDict"
                   (mksignature (AST.Xptr :: AST.Xptr :: AST.Xlong :: nil)
                     AST.Xlong cc_default))
     ((tptr (Tstruct _ZSTD_DCtx_s noattr)) :: (tptr tvoid) :: tulong :: nil)
     tulong cc_default)) ::
 (_ZSTD_initDStream_usingDDict,
   Gfun(External (EF_external "ZSTD_initDStream_usingDDict"
                   (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xlong
                     cc_default))
     ((tptr (Tstruct _ZSTD_DCtx_s noattr)) ::
      (tptr (Tstruct _ZSTD_DDict_s noattr)) :: nil) tulong cc_default)) ::
 (_ZSTD_resetDStream,
   Gfun(External (EF_external "ZSTD_resetDStream"
                   (mksignature (AST.Xptr :: nil) AST.Xlong cc_default))
     ((tptr (Tstruct _ZSTD_DCtx_s noattr)) :: nil) tulong cc_default)) ::
 (_within_oneshot, Gfun(Internal f_within_oneshot)) ::
 (_within_stream, Gfun(Internal f_within_stream)) ::
 (_stall_error, Gfun(Internal f_stall_error)) ::
 (_exact_copy, Gfun(Internal f_exact_copy)) :: (_vd_wd, Gvar v_vd_wd) ::
 (_vd_raw, Gvar v_vd_raw) :: (_x_valid_dict_api__sr, Gvar v_x_valid_dict_api__sr) ::
 (_vd_chunk, Gfun(Internal f_vd_chunk)) ::
 (_vd_stream, Gfun(Internal f_vd_stream)) ::
 (_main, Gfun(Internal f_main)) :: nil).

Definition public_idents : list ident :=
(_main :: _ZSTD_resetDStream :: _ZSTD_initDStream_usingDDict ::
 _ZSTD_initDStream_usingDict :: _ZSTD_DCtx_refPrefix_advanced ::
 _ZSTD_DCtx_loadDictionary_advanced :: _ZSTD_DCtx_refDDict ::
 _ZSTD_freeDDict :: _ZSTD_createDDict :: _ZSTD_decompressStream ::
 _ZSTD_DCtx_setParameter :: _ZSTD_decompressDCtx :: _ZSTD_freeDCtx ::
 _ZSTD_createDCtx :: _ZSTD_getErrorCode :: _ZSTD_isError :: _gp_assume ::
 _gp_assert :: _nondet_u32 :: _quickproof_free :: _quickproof_malloc ::
 ___builtin_debug :: ___builtin_write32_reversed ::
 ___builtin_write16_reversed :: ___builtin_read32_reversed ::
 ___builtin_read16_reversed :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_fmin ::
 ___builtin_fmax :: ___builtin_expect :: ___builtin_unreachable ::
 ___builtin_va_end :: ___builtin_va_copy :: ___builtin_va_arg ::
 ___builtin_va_start :: ___builtin_membar :: ___builtin_annot_intval ::
 ___builtin_annot :: ___builtin_sel :: ___builtin_memcpy_aligned ::
 ___builtin_sqrt :: ___builtin_fsqrt :: ___builtin_fabsf ::
 ___builtin_fabs :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
 ___builtin_bswap16 :: ___builtin_bswap32 :: ___builtin_bswap ::
 ___builtin_bswap64 :: ___builtin_ais_annot :: ___compcert_i64_umulh ::
 ___compcert_i64_smulh :: ___compcert_i64_sar :: ___compcert_i64_shr ::
 ___compcert_i64_shl :: ___compcert_i64_umod :: ___compcert_i64_smod ::
 ___compcert_i64_udiv :: ___compcert_i64_sdiv :: ___compcert_i64_utof ::
 ___compcert_i64_stof :: ___compcert_i64_utod :: ___compcert_i64_stod ::
 ___compcert_i64_dtou :: ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


