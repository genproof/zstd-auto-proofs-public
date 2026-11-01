(* With zstd's default parameters and no dictionary selection, the functions of model/Params.v are those of
   Series.v / StreamModel.v.  Plain Coq.  params_dflt is the one statement to prove;
   the lemmas below are its parts. *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Block Zstd.proof.model.Series.
Require Import Zstd.proof.model.StreamModel Zstd.proof.model.Params.

Lemma pd_fh_bmax (s: list Z) (h: frame_header) :
  get_frame_header s = FH_ok h -> fh_blockSizeMax h <= ZSTD_BLOCKSIZE_MAX.
Proof.
  unfold get_frame_header. intros H.
  repeat match type of H with
  | context [if ?c then _ else _] => destruct c
  end; try discriminate; inversion H; subst; simpl;
  unfold ZSTD_BLOCKSIZE_MAX; lia.
Qed.

Lemma pd_frame (dm: dict_model) (wl: Z) (s: list Z) : decode_frame_m md_dflt dm wl s = decode_frame dm wl s.
Proof.
  unfold decode_frame_m, decode_frame, get_frame_header_m. simpl md_magicless. simpl md_ignore. simpl md_bmax.
  cbv beta iota zeta. rewrite !Z.sub_0_r.
  destruct (get_frame_header s) as [|k|h] eqn:E; try reflexivity.
  cbn [negb andb]. rewrite (Z.min_l _ _ (pd_fh_bmax s h E)). reflexivity.
Qed.

Lemma pd_walk (n: nat) (dm: dict_model) (wl: Z) (s: list Z) (off: Z) :
  walk_m n md_dflt sel_none (Some dm) wl s off = walk n dm wl s off.
Proof.
  revert s off. induction n as [|n IH]; intros s off; [reflexivity|].
  simpl. unfold starting_len. 
  destruct (Zlength s <? ZSTD_FRAMEHEADERSIZE_PREFIX); [reflexivity|].
  destruct (is_skippable_magic (le_field s 0 4)).
  - destruct (skippable_frame_size s); [|reflexivity]. rewrite IH. reflexivity.
  - assert (Hd: frame_dict false sel_none (Some dm) s = Some dm).
    { unfold frame_dict, sel_none. destruct (get_frame_header_m false s); reflexivity. }
    rewrite Hd, pd_frame. destruct (decode_frame dm wl s); try reflexivity. rewrite IH. reflexivity.
Qed.

Lemma pd_bl (md: dmode) (dm: dict_model) (b b': blst) (c out: list Z) :
  bl_step md dm b c = BLOk b' out -> bs_out b' = bs_out b ++ out.
Proof.
  assert (Hdone: forall b ds content, bl_block_done b ds content = BLOk b' out -> bs_out b' = bs_out b ++ out).
  { intros b0 ds content. unfold bl_block_done, bl_frame_end.
    repeat match goal with
    | |- context [if ?c then _ else _] => destruct c
    | |- context [match bs_stage ?x with _ => _ end] => destruct (bs_stage x)
    end; intros H; try discriminate; inversion H; subst; reflexivity. }
  unfold bl_step. intros H.
  destruct (bs_stage b).
  all: repeat match type of H with
  | context [if ?c then _ else _] => destruct c
  | context [match ?x with _ => _ end] =>
      lazymatch x with bs_stage _ => fail | _ => destruct x eqn:? end
  | bl_block_done _ _ _ = _ => apply Hdone in H; exact H
  end; try discriminate; try (inversion H; subst; simpl; rewrite app_nil_r; reflexivity).
Qed.

Theorem params_dflt :
  (forall (dm: dict_model) (wl: Z) (s: list Z), decode_frame_m md_dflt dm wl s = decode_frame dm wl s) /\
  (forall (dm: dict_model) (wl: Z) (s: list Z),
     series_frames_m md_dflt sel_none (Some dm) wl s = series_frames dm wl s) /\
  (forall (sin: list Z), stream_alive_m md_dflt sel_none (Some no_dict) sin <-> stream_alive sin) /\
  (forall (sin0 sout0 sin sall sout: list Z) (a1: Z) (ocap: option Z) (r: Z),
     stream_claims_m md_dflt sel_none (Some no_dict) stream_wlim sin0 sout0 sin sall sout a1 ocap r <->
     stream_claims sin0 sout0 sin sall sout a1 ocap r) /\
  (* a step of the buffer-less model only appends to the frame's content: what it delivers *)
  (forall (md: dmode) (dm: dict_model) (b b': blst) (c out: list Z),
     bl_step md dm b c = BLOk b' out -> bs_out b' = bs_out b ++ out).
Proof.
  split; [exact pd_frame|]. split.
  { intros dm wl s. unfold series_frames_m, series_frames. apply pd_walk. }
  split.
  { intros sin. unfold stream_alive_m, stream_alive, series_frames_m.
    setoid_rewrite pd_walk. reflexivity. }
  split.
  { intros. unfold stream_claims_m, stream_claims, series_frames_m.
    setoid_rewrite pd_walk. reflexivity. }
  exact pd_bl.
Qed.

Lemma decode_frame_m_dflt (dm: dict_model) (wl: Z) (s: list Z) :
  decode_frame_m md_dflt dm wl s = decode_frame dm wl s.
Proof. apply params_dflt. Qed.

Lemma series_frames_m_dflt (dm: dict_model) (wl: Z) (s: list Z) :
  series_frames_m md_dflt sel_none (Some dm) wl s = series_frames dm wl s.
Proof. apply params_dflt. Qed.

Lemma decode_series_m_dflt (dm: dict_model) (wl: Z) (s: list Z) :
  decode_series_m md_dflt sel_none (Some dm) wl s = decode_series dm wl s.
Proof. unfold decode_series_m, decode_series. rewrite series_frames_m_dflt. reflexivity. Qed.

Lemma stream_alive_m_dflt (sin: list Z) :
  stream_alive_m md_dflt sel_none (Some no_dict) sin <-> stream_alive sin.
Proof. apply params_dflt. Qed.

Lemma stream_claims_m_dflt (sin0 sout0 sin sall sout: list Z) (a1: Z) (ocap: option Z) (r: Z) :
  stream_claims_m md_dflt sel_none (Some no_dict) stream_wlim sin0 sout0 sin sall sout a1 ocap r <->
  stream_claims sin0 sout0 sin sall sout a1 ocap r.
Proof. apply params_dflt. Qed.

Lemma bl_step_out (md: dmode) (dm: dict_model) (b b': blst) (c out: list Z) :
  bl_step md dm b c = BLOk b' out -> bs_out b' = bs_out b ++ out.
Proof. apply params_dflt. Qed.
