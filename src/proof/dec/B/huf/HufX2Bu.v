(* X2T bodies: HUF_buildDEltX2U32, HUF_buildDEltX2. *)
Require Import Zstd.proof.dec.B.huf.HufX2S.
Local Open Scope logic.

Lemma body_HUF_buildDEltX2U32 : semax_body Vprog G_X2 f_HUF_buildDEltX2U32 HUF_buildDEltX2U32_spec.
Proof.
  start_function.
  forward_call tt.
  forward_if.
  2: { exfalso. apply Int.one_not_zero. exact H3. }
  forward_if (PROP () LOCAL (temp _t'1 (Vint (Int.repr (if lv =? 1 then sym else bs + 256 * sym)));
     temp _nbBits (Vint (Int.repr nb)); temp _level (Vint (Int.repr lv))) SEP ()).
  - forward. entailer!.
  - forward. entailer!.
    replace (lv =? 1) with false by (symmetry; apply Z.eqb_neq; exact H4).
    rewrite Int.shl_mul_two_p. change (two_p (Int.unsigned (Int.repr 8))) with 256.
    rewrite mul_repr, add_repr. do 2 f_equal. lia.
  - forward. forward. entailer!. unfold deltu.
    rewrite !Int.shl_mul_two_p. change (two_p (Int.unsigned (Int.repr 16))) with 65536.
    change (two_p (Int.unsigned (Int.repr 24))) with 16777216.
    rewrite !mul_repr, !add_repr. do 2 f_equal. lia.
Qed.

Lemma body_HUF_buildDEltX2 : semax_body Vprog G_X2 f_HUF_buildDEltX2 HUF_buildDEltX2_spec.
Proof.
  start_function.
  forward_call (sym, nb, bs, lv).
  forward.
  forward_call (Tsh, sh, v_val, p, existT (fun t => reptype t) tuint (Vint (Int.repr (deltu sym nb bs lv)))).
  { memcpy_side. }
  simpl projT1; simpl projT2. entailer!.
Qed.
