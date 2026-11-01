(* Group ENT: the exported wrappers FSE_readNCount and HUF_readStats_wksp.  Their
   specifications are BIface's; the bodies relate the C-faithful results (ncount_res, huf_parse_res) to the
   model's. *)
Require Import Zstd.proof.dec.B.ent.EntSpecs.
Local Open Scope logic.

Lemma ex_short_val (l: list Z) : Forall (fun x => -1 <= x <= 512) l ->
  map short_val l = map (fun x => Vint (Int.repr x)) l.
Proof.
  induction 1; simpl; auto. rewrite IHForall. f_equal. unfold short_val. f_equal.
  apply sign_ext_inrange. rewrite Int.signed_repr by rep_lia. simpl. lia.
Qed.

Lemma body_ent_readncount : NCOUNT_RES_OK ->
  semax_body Vprog (G_B0 ++ [FSE_readNCount_bmi2_spec]) f_FSE_readNCount FSE_readNCount_spec.
Proof.
  intros HRO.
  start_function.
  forward_call (gv, shn, pn, nn, shm, pm, sht, pt, maxsv, sh, base, N, c, off, s).
  Intros vret. destruct vret as [[r nc] res]. simpl fst in *; simpl snd in *.
  match goal with Hr: nc_rel _ _ _ |- _ => rename Hr into Hrel end.
  assert (Hres: forall norm log size, res = Some (norm, log, size) ->
            size <= Zlength s /\ ncount_ok norm log maxsv).
  { intros norm log size ->. unfold nc_rel in Hrel. destruct (Zlength s <? 8).
    - destruct Hrel as [_ [Hz Hk]]. auto.
    - symmetry in Hrel. destruct (HRO s maxsv norm log size ltac:(lia) Hrel). split; [lia | auto]. }
  assert (Hmod: forall x, read_ncount s maxsv = Some x -> res = Some x).
  { intros x Ex. pose proof (ncount_model_c s maxsv x ltac:(lia) Ex) as Ec. unfold nc_rel in Hrel.
    destruct (Zlength s <? 8); [apply (proj1 Hrel); exact Ec | rewrite Hrel; exact Ec]. }
  match goal with h: res = x_ncount s maxsv |- _ => subst res end.
  forward. Exists r nc (x_ncount s maxsv). entailer!.
  destruct (x_ncount s maxsv) as [[[norm log] size]|]; [|assumption].
  match goal with Hs: r = size /\ _ |- _ => destruct Hs as [-> Hc] end. destruct (Hres norm log size eq_refl) as [Hz Hk].
  split; [reflexivity|]. split; [lia|]. split; [exact Hk|].
  intros Hl. rewrite Hc by (right; exact Hl). apply ex_short_val.
  destruct Hk as (_ & _ & Hrng & _). eapply Forall_impl; [|exact Hrng]. intros x [Hx1 Hx2]. split; [lia|].
  assert (2 ^ log <= 2 ^ 9) by (apply Z.pow_le_mono_r; lia). change (2 ^ 9) with 512 in *. lia.
Qed.

(* HUF_readStats_body ignores FSE_decompress_wksp's readNCount result when it does not call it *)
Lemma huf_parse_res_nowin res nk b : rs_window b = None -> huf_parse_res res nk b = huf_parse_res None nk b.
Proof.
  intros H. unfold huf_parse_res, huf_parse_w, huf_desc_weights_w. unfold rs_window in H. cbv zeta.
  destruct (Zlength b <? 1) eqn:E1; [reflexivity|].
  destruct (byte_at b 0 >=? 128) eqn:E2; [reflexivity|].
  destruct (Zlength b <? byte_at b 0 + 1) eqn:E3; [reflexivity|].
  exfalso. rewrite Z.ltb_ge in E1, E3. rewrite Z.geb_leb, Z.leb_gt in E2.
  rewrite (proj2 (Z.leb_le 1 _)), (proj2 (Z.ltb_lt _ 128)), (proj2 (Z.leb_le _ (Zlength b))) in H by lia.
  discriminate.
Qed.

(* HUF_readStats_wksp's result is zstd's exact reading x_readstats once the body's readNCount result is exact *)
Lemma readstats_res_x res s :
  match rs_window s with Some w => res = x_ncount w 255 | None => True end -> huf_parse_res res 219 s = x_readstats s.
Proof.
  intros H. unfold x_readstats.
  destruct (rs_window s) eqn:E; [subst; reflexivity|]. apply huf_parse_res_nowin; exact E.
Qed.

Lemma body_ent_readstats_wksp : HUF_MODEL_C -> HUF_RES_OK ->
  semax_body Vprog (G_B0 ++ [HUF_readStats_body_default_spec]) f_HUF_readStats_wksp HUF_readStats_wksp_spec.
Proof.
  intros HMC HRO.
  start_function.
  forward_if (PROP () LOCAL (temp _huffWeight pw; temp _hwSize (Vlong (Int64.repr 256)); temp _rankStats pr;
      temp _nbSymbolsPtr ps; temp _tableLogPtr pt; temp _src (offset_val off base);
      temp _srcSize (Vlong (Int64.repr (Zlength s))); temp _workSpace pk; temp _wkspSize (Vlong (Int64.repr (4 * 219)));
      gvars gv)
    SEP (zstd_globals gv; data_at_ shw (tarray tuchar 256) pw; data_at_ shr (tarray tuint 13) pr;
         data_at_ shs tuint ps; data_at_ sht tuint pt; data_at sh (tarray tuchar N) c base;
         data_at_ shk (tarray tuint 219) pk)).
  { exfalso; congruence. }
  { forward. entailer!. }
  forward_call (gv, shw, pw, shr, pr, shs, ps, sht, pt, sh, base, N, c, off, s, shk, pk, 219).
  Intros vret. destruct vret as [[r wc] res]. simpl fst in *; simpl snd in *.
  forward.
  assert (Hx: huf_parse_res res 219 s = x_readstats s)
    by (apply readstats_res_x; match goal with h: match rs_window s with Some _ => res = _ | None => True end |- _ => exact h end).
  Exists r wc (huf_parse_res res 219 s).
  assert (Hb: bytes_ok s) by (destruct H as (_ & _ & _ & _ & _ & _ & Hb & _); exact Hb).
  assert (Hb0: 0 <= byte_at s 0 < 256).
  { unfold byte_at. destruct s as [|b0 s']; simpl; [lia|]. inversion Hb; subst; auto. }
  entailer!.
  destruct (huf_parse_res res 219 s) as [[ht size]|] eqn:E; [|exact H3].
  destruct H3 as [-> Hw]. destruct (HRO res s ht size Hb E) as (Hs & Hok & Hl & Hw0).
  split; [reflexivity|]. split; [lia|]. split; [exact Hok|]. split; [lia|]. split; [exact Hw0 | exact Hw].
Qed.
