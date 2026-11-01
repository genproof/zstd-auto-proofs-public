(* ParamsW.v's no-dictionary parts, proved (ParamsW.params_w is proved too): without a dictionary
   (hist = []) the dictionary window rule changes nothing.  Plain Coq. *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Block Zstd.proof.model.Series.
Require Import Zstd.proof.model.StreamModel Zstd.proof.model.Params.

Lemma exec_seqs_w_nil_so (wsize: Z) (rep: Z * Z * Z) (lits out: list Z) (seqs: list sequence) :
  exec_seqs_w wsize rep nil lits out seqs = exec_seqs wsize rep nil lits out seqs.
Proof.
  revert rep lits out. induction seqs as [|sq rest IH]; intros rep lits out; simpl; [reflexivity|].
  destruct (sq_ll sq >? Zlength lits); [reflexivity|].
  destruct (resolve_offset rep (sq_ll sq) (sq_ov sq)) as [[offset rep']|]; [|reflexivity].
  rewrite Zlength_nil, Z.add_0_r.
  destruct (offset >? Zlength (out ++ firstn (Z.to_nat (sq_ll sq)) lits)) eqn:E1; [reflexivity|].
  simpl. destruct (offset >? wsize); simpl; [reflexivity|]. apply IH.
Qed.

Lemma decode_block_w_nil_so (st: dstate) (out b: list Z) (bsm wsize: Z) :
  decode_block_w st nil out b bsm wsize = decode_block st nil out b bsm wsize.
Proof.
  unfold decode_block_w, decode_block.
  destruct (Zlength b >? bsm); [reflexivity|].
  destruct (decode_literals (st_huf st) b bsm) as [[[lits lused] huf]|]; [|reflexivity].
  destruct (decode_seq_header _ _) as [[[nbSeq tabs] hused]|]; [|reflexivity].
  destruct (if nbSeq =? 0 then _ else _) as [seqs|]; [|reflexivity].
  rewrite exec_seqs_w_nil_so. reflexivity.
Qed.

Lemma decode_blocks_w_nil_so (fuel: nat) (st: dstate) (s out: list Z) (bsm wsize: Z) :
  decode_blocks_w fuel st nil s out bsm wsize = decode_blocks fuel st nil s out bsm wsize.
Proof.
  revert st s out. induction fuel as [|f IH]; intros st s out; simpl; [reflexivity|].
  destruct (cblock_size s) as [c|]; [|reflexivity].
  destruct (c >? Zlength s - ZSTD_blockHeaderSize); [reflexivity|].
  rewrite decode_block_w_nil_so.
  destruct (if bp_type (block_props_of s) =? 0 then _ else _) as [[st' out']|]; [|reflexivity].
  rewrite IH. reflexivity.
Qed.

Lemma decode_frame_m_w_nodict_so (md: dmode) (wl: Z) (s: list Z) :
  decode_frame_m (dmode_w md) no_dict wl s = decode_frame_m md no_dict wl s.
Proof.
  unfold decode_frame_m. cbn [md_magicless md_ignore md_bmax md_dwin dmode_w].
  destruct (md_dwin md); [reflexivity|].
  cbn [dm_content no_dict dict_raw].
  destruct (get_frame_header_m (md_magicless md) s); try reflexivity.
  rewrite decode_blocks_w_nil_so. reflexivity.
Qed.

Lemma walk_m_w_nodict_so (fuel: nat) (md: dmode) (wl: Z) (s: list Z) (off: Z) :
  walk_m fuel (dmode_w md) sel_none (Some no_dict) wl s off = walk_m fuel md sel_none (Some no_dict) wl s off.
Proof.
  revert s off. induction fuel as [|f IH]; intros s off; simpl; [reflexivity|].
  destruct (Zlength s <? starting_len (md_magicless md)); [reflexivity|].
  destruct ((negb (md_magicless md) && is_skippable_magic (le_field s 0 4))%bool).
  - destruct (skippable_frame_size s) as [k|]; [|reflexivity].
    destruct (md_dwin md); rewrite IH; reflexivity.
  - assert (Hfd: frame_dict (md_magicless md) sel_none (Some no_dict) s = Some no_dict)
      by (unfold frame_dict, sel_none; destruct (get_frame_header_m _ _); reflexivity).
    rewrite Hfd, decode_frame_m_w_nodict_so.
    destruct (decode_frame_m md no_dict wl s); try reflexivity. rewrite IH. reflexivity.
Qed.

Lemma series_frames_m_w_nodict_so (md: dmode) (wl: Z) (s: list Z) :
  series_frames_m (dmode_w md) sel_none (Some no_dict) wl s = series_frames_m md sel_none (Some no_dict) wl s.
Proof. unfold series_frames_m. apply walk_m_w_nodict_so. Qed.
