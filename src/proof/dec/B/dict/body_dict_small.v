(* ZSTD_DDict_dictContent, ZSTD_DDict_dictSize *)
Require Export Zstd.proof.dec.B.dict.DictSpecs.
Local Open Scope logic.

Lemma body_dict_content : body_ok DICT_G ZSTD_DDict_dictContent_spec.
Proof.
  exists f_ZSTD_DDict_dictContent; split; [reflexivity | split; [reflexivity |]].
  start_function. unfold ddict_struct. Intros.
  match goal with H: isptr buf \/ _ |- _ => assert (is_pointer_or_null buf)
    by (destruct H as [Hp | (-> & _)]; [destruct buf; try contradiction; simpl; auto | simpl; auto]) end.
  forward. forward. unfold ddict_struct. entailer!.
Qed.

Lemma body_dict_size : body_ok DICT_G ZSTD_DDict_dictSize_spec.
Proof.
  exists f_ZSTD_DDict_dictSize; split; [reflexivity | split; [reflexivity |]].
  start_function. unfold ddict_struct. Intros.
  match goal with H: isptr buf \/ _ |- _ => assert (is_pointer_or_null buf)
    by (destruct H as [Hp | (-> & _)]; [destruct buf; try contradiction; simpl; auto | simpl; auto]) end.
  forward. forward. unfold ddict_struct. entailer!.
Qed.
