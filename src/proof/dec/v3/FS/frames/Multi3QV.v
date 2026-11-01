(* FS3 one-shot frames, ZSTD_decompressMultiFrame: the pointer tests of the body (`ddict`, ddictSet). *)
Require Export Zstd.proof.dec.v3.FS.frames.Multi3Aux.
Local Open Scope logic.

Section CM_Multi3QV_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* the DDict struct of ddict_rep_at: dictBuffer at offset 0 *)
Lemma mf_rep_valid: forall DENT gv x buf, ddict_rep_at DENT gv x buf |-- valid_pointer (dx_q x).
Proof.
  intros. unfold ddict_rep_at, ddict_struct.
  do 3 apply sepcon_valid_pointer1. apply andp_left2.
  repeat apply sepcon_valid_pointer1.
  apply field_at_valid_ptr0; auto; reflexivity.
Qed.

(* `if (ddict)`: the variable is NULL, the argument's DDict, or (selection) a DDict of the set *)
Lemma mf_qv_valid: forall DENT gv p pr sp d l tbl shk a W shd cap dst dcur qv am hb,
  (sel_on pr sp = true -> msel_ok W d l a shk shd cap dst) ->
  (sel_on pr sp = true -> darg_local d a = true -> ~ In (darg_ddict a) (map fst l)) ->
  qv_ok pr sp a l qv -> dc_ok pr sp l d dcur -> (darg_local d a = true -> qv = darg_ddict a -> dcur = d) ->
  msel_res DENT gv p pr sp dcur l tbl shk a am hb * darg_res3 DENT gv pr sp d a |-- valid_pointer qv.
Proof.
  intros DENT gv p pr sp d l tbl shk a W shd cap dst dcur qv am hb Hok Hg Hq Hdc Hloc.
  destruct Hq as [Hq | (Hon & Hn & Hin)].
  - destruct (eq_dec qv nullval) as [N|N]; [subst qv; rewrite N; apply valid_pointer_null|].
    destruct a as [| sh0 pk b | x buf sh]; simpl in Hq; try (subst; contradiction).
    subst qv. unfold darg_res3.
    destruct (sel_on pr sp && darg_local d (DA_ddict x buf sh))%bool eqn:E.
    + apply andb_prop in E. destruct E as [Hon Hl].
      rewrite (Hloc Hl eq_refl).
      destruct (Hok Hon) as (_ & _ & Hlx & _). destruct (Hlx Hl) as (x' & buf' & sh' & Ea & Hd).
      inversion Ea; subst x' buf' sh'.
      apply sepcon_valid_pointer1. unfold msel_res. rewrite Hon.
      do 3 apply sepcon_valid_pointer1. apply sepcon_valid_pointer2.
      unfold dgroup. apply sepcon_valid_pointer2. unfold local_rep. rewrite Hd.
      destruct (eq_dec (df_local d) nullval) as [Z|Z].
      * exfalso. unfold darg_local in Hl. rewrite Z in Hl. simpl in Hl.
        rewrite veqb_refl in Hl. rewrite andb_false_r in Hl. discriminate.
      * apply andp_left2. apply mf_rep_valid.
    + apply sepcon_valid_pointer2. simpl. apply sepcon_valid_pointer1. apply mf_rep_valid.
  - destruct (mf_probe_split DENT gv p pr sp d l tbl shk a W shd cap dst dcur am hb Hon (Hok Hon) (Hg Hon) Hdc)
      as (MK0 & H1 & _).
    eapply derives_trans; [exact H1|].
    apply sepcon_valid_pointer1. apply sepcon_valid_pointer2. apply set_ids_valid; auto.
Qed.

(* `dctx->ddictSet` tested when refMultipleDDicts is set: NULL, or the set's struct (msel_res) *)
Lemma mf_sp_valid: forall DENT gv p pr sp dcur l tbl shk a am hb,
  dp_multi pr = 1 -> is_pointer_or_null sp ->
  msel_res DENT gv p pr sp dcur l tbl shk a am hb |-- valid_pointer sp.
Proof.
  intros DENT gv p pr sp dcur l tbl shk a am hb Hm Hp.
  destruct (eq_dec sp nullval) as [N|N]; [subst sp; apply valid_pointer_null|].
  unfold msel_res. replace (sel_on pr sp) with true.
  2:{ unfold sel_on. rewrite Hm. simpl. unfold veqb. destruct (Val.eq sp nullval); [contradiction|reflexivity]. }
  apply sepcon_valid_pointer1. apply sepcon_valid_pointer2. unfold hset_tbl.
  Intros tp. apply sepcon_valid_pointer1. apply sepcon_valid_pointer2.
  apply data_at_valid_ptr; [auto | simpl; lia].
Qed.

Lemma mf_qv_all : True.
Proof. pose proof mf_qv_valid. pose proof mf_sp_valid. exact I. Qed.

End CM_Multi3QV_1.
