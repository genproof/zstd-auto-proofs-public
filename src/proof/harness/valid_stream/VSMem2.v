(* valid_stream's main reads sr.content[k]: forward on the field_at of the 2^18-byte array overflows the stack,
   so main borrows the one byte (sr.content is at offset 524296 = 2^19 + 8 of wseries_t). *)
Require Import VST.floyd.proofauto.
Require Export Zstd.proof.harness.valid_stream.WTopSpecs_valid_stream.

Local Notation HCS := Zstd.proof.harness.valid_stream.HOK_valid_stream.CompSpecs.

Lemma VSC_borrow (P Q R: mpred) : P |-- Q * R -> Q * R |-- P -> P |-- R * (R -* P).
Proof.
  intros H1 H2. eapply derives_trans; [exact H1|].
  rewrite (sepcon_comm Q R). apply sepcon_derives; [apply derives_refl|].
  apply wand_sepcon_adjoint. exact H2.
Qed.

Lemma VSC_content_split (V: list val) p k :
  0 <= k < 2 ^ 18 -> Zlength V = 2 ^ 18 ->
  field_compatible (cs := HCS) t_wseries (DOT _content) p ->
  @field_at HCS Ews t_wseries (DOT _content) V p =
  (@data_at HCS Ews (Tarray tuchar k noattr) (sublist 0 k V) (offset_val 524296 p) *
  @data_at HCS Ews tuchar (Znth k V) (offset_val (524296 + k) p) *
  @data_at HCS Ews (Tarray tuchar (262144 - (k + 1)) noattr) (sublist (k + 1) 262144 V)
    (offset_val (524296 + (k + 1)) p))%logic.
Proof.
  intros Hk HV FC.
  rewrite field_at_data_at.
  assert (FC1 := field_compatible_app nil t_wseries (DOT _content) p FC).
  assert (FA: field_address t_wseries (DOT _content) p = offset_val 524296 p).
  { unfold field_address. rewrite if_true by auto. reflexivity. }
  rewrite FA in *.
  change (nested_field_type t_wseries (DOT _content)) with (Tarray tuchar 262144 noattr) in *.
  rewrite (split3_data_at_Tarray_tuchar Ews 262144 k (k + 1) V) by lia.
  rewrite !field_address0_offset by auto with field_compatible.
  simpl nested_field_type. simpl nested_field_offset. rewrite !offset_offset_val.
  replace (524296 + (0 + 1 * k)) with (524296 + k) by lia.
  replace (524296 + (0 + 1 * (k + 1))) with (524296 + (k + 1)) by lia.
  replace (k + 1 - k) with 1 by lia.
  rewrite sublist_len_1 by lia.
  rewrite (data_at_singleton_array_eq Ews tuchar (Znth k V) [Znth k V]) by reflexivity.
  reflexivity.
Qed.

Lemma VS_content_borrow (V: list val) p k :
  0 <= k < 2 ^ 18 -> Zlength V = 2 ^ 18 ->
  @field_at HCS Ews t_wseries (DOT _content) V p |--
  @data_at HCS Ews tuchar (Znth k V) (offset_val (524296 + k) p) *
  (@data_at HCS Ews tuchar (Znth k V) (offset_val (524296 + k) p) -*
   @field_at HCS Ews t_wseries (DOT _content) V p).
Proof.
  intros Hk HV.
  eapply derives_trans; [rewrite field_at_compatible'; apply derives_refl|].
  apply derives_extract_prop; intro FC.
  rewrite (VSC_content_split V p k Hk HV FC).
  apply VSC_borrow with
    (Q := (@data_at HCS Ews (Tarray tuchar k noattr) (sublist 0 k V) (offset_val 524296 p) *
          @data_at HCS Ews (Tarray tuchar (262144 - (k + 1)) noattr) (sublist (k + 1) 262144 V)
            (offset_val (524296 + (k + 1)) p))%logic);
    cancel.
Qed.
