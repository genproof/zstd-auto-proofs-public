(* FS3 streaming, case zdss_load: the frame's dictionary is one the model handles (dm_ok), from the
   current dictionary (cur_dict_ok) and the byte content of the context's dictionaries (dicts_bytes, from their
   DDicts' representation).  dict_auto_dm_ok: a copy of an earlier proof of the model facts. *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Block Zstd.proof.model.Series Zstd.proof.model.Huffman.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Require Import Zstd.proof.dec.v3.FS.stream.S3Defs Zstd.proof.dec.v3.FS.stream.load.L3ErABase.
Import ListNotations.
Local Open Scope Z_scope.

Section CM_L3Dm_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma l3d_huf_desc_len : forall b ws size, bytes_ok b -> Huffman.huf_desc_weights b = Some (ws, size) ->
  (length ws <= 255)%nat.
Proof.
  unfold Huffman.huf_desc_weights; intros.
  destruct (Zlength b <? 1); [discriminate|].
  pose proof (bytes_ok_byte_at b 0 H).
  destruct (byte_at b 0 >=? 128) eqn:E.
  - destruct (Zlength b <? _); [discriminate|]. inversion H0; subst.
    unfold Huffman.huf_direct_weights. rewrite length_map, length_seq. lia.
  - destruct (Zlength b <? _); [discriminate|].
    destruct (Huffman.huf_fse_weights _) as [ws'|] eqn:F; [|discriminate]. inversion H0; subst.
    unfold Huffman.huf_fse_weights in F.
    repeat match type of F with
    | context [match ?e with _ => _ end] => let E := fresh "E" in destruct e eqn:E; try discriminate
    | context [if ?b then _ else _] => let E := fresh "E" in destruct b eqn:E; try discriminate
    end.
    all: inversion F; subst; apply Zgtb_le in E5 || idtac; rewrite Zlength_correct in *; lia.
Qed.

Lemma l3d_huf_parse_len : forall b t size, bytes_ok b -> Huffman.huf_parse_desc b = Some (t, size) ->
  (length (Huffman.ht_weights t) <= 256)%nat.
Proof.
  unfold Huffman.huf_parse_desc; intros.
  destruct (Huffman.huf_desc_weights b) as [[ws sz]|] eqn:E; [|discriminate].
  pose proof (l3d_huf_desc_len _ _ _ H E).
  repeat match type of H0 with context [if ?c then _ else _] => destruct c; [discriminate|] end.
  inversion H0; subst. simpl. rewrite length_app. simpl. lia.
Qed.

Lemma l3d_raw_dm_ok : forall b, bytes_ok b -> dm_ok (dict_raw b).
Proof. intros. split; auto. simpl. discriminate. Qed.

Lemma l3d_auto_dm_ok : forall b dm, bytes_ok b -> dict_auto b = Some dm -> dm_ok dm.
Proof.
  intros b dm Hb H. unfold dict_auto in H.
  destruct (Zlength b <? 8); [inversion H; subst; apply l3d_raw_dm_ok; auto|].
  destruct (negb _); [inversion H; subst; apply l3d_raw_dm_ok; auto|].
  destruct (load_dentropy b) as [[st esize]|] eqn:L; [|discriminate]. inversion H; subst; clear H.
  split; [apply bytes_ok_skipn; auto|]. cbn [dm_state].
  unfold load_dentropy in L.
  destruct (Zlength b <=? 8); [discriminate|].
  destruct (huf_parse_desc (skipn 8 b)) as [[ht hs]|] eqn:P; [|discriminate].
  pose proof (l3d_huf_parse_len _ _ _ (bytes_ok_skipn _ _ Hb) P).
  repeat match type of L with
  | context [match ?e with _ => _ end] => let E := fresh "E" in destruct e eqn:E; try discriminate
  | context [if ?c then _ else _] => let E := fresh "E" in destruct c eqn:E; try discriminate
  end.
  inversion L; subst. simpl. intros t Ht. inversion Ht; subst. auto.
Qed.

(* the byte content of the context's dictionaries (from their DDicts, dict_res / set_res / dgroup) *)
Definition dicts_bytes (st: dctx_st) : Prop :=
  (dc_set st = nil -> forall dr, dc_dict st = Some dr -> bytes_ok (dr_bytes dr)) /\
  (forall q dd, In (q, dd) (dc_set st) -> bytes_ok (dd_bytes dd)).

Lemma cur_dict_dm_ok : forall st k dm, dicts_bytes st -> cur_dict_ok st k (Some dm) -> dm_ok dm.
Proof.
intros st k dm [Hd Hs] Hc. destruct (Hc dm eq_refl) as [(Hn&Hm)|(_&_&(dd&Hin&Ha)&_)].
- unfold dictref_model in Hm. destruct (dc_dict st) as [dr|] eqn:E.
  + specialize (Hd Hn dr eq_refl). destruct (dr_raw dr).
    * inversion Hm; subst. apply l3d_raw_dm_ok; auto.
    * eapply l3d_auto_dm_ok; eauto.
  + inversion Hm; subst. apply l3d_raw_dm_ok. constructor.
- eapply l3d_auto_dm_ok; [|exact Ha]. eapply Hs; eauto.
Qed.

Lemma ld_dm_of : forall st k sm fp cd, dicts_bytes st -> cur_dict_ok st k (next_cd sm fp cd) ->
  forall hdr z, fp = FP_zstd hdr z -> dm_ok (zp_dm z).
Proof.
intros st k sm fp cd Hb Hc hdr z E. subst fp. cbn [next_cd] in Hc. eapply cur_dict_dm_ok; eauto.
Qed.

End CM_L3Dm_1.
