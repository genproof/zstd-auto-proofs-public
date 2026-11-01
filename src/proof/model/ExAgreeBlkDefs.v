(* The vocabulary of the proof that the exact block model (Exact.xblock, ExBlock.x_block) agrees with
   Block.decode_block (ExAgreeBlock.v): what the memory of the exact model holds (the frame's output so far in
   the destination, the literals not yet consumed in their region), and the invariant of the sequence loop
   that relates an execution state of the exact model (ExBlock.xex) to the format model's execution
   (Block.exec_seqs: output so far, literals left).  Plain Coq. *)
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Import ListNotations.
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Bitstream Zstd.proof.model.BitsFast Zstd.proof.model.Fse.
Require Import Zstd.proof.model.Block Zstd.proof.model.ExCSeq Zstd.proof.model.ExBlock.
Local Open Scope Z_scope.

(* ---------- the memory ---------- *)

(* the destination cell p (None: never written) *)
Definition dcell (m: xmem) (p: Z) : option Z := nth (Z.to_nat p) (xm_dst m) None.

(* region r (of a block whose input is src) holds the bytes l from index i on *)
Definition reg_has (src: list Z) (m: xmem) (r: xreg) (i: Z) (l: list Z) : Prop :=
  forall k, 0 <= k < Zlength l -> xm_rd src m r (i + k) = Some (byte_at l k).

(* the n cells of region r from index i on are defined (a copy may read them past the bytes it needs) *)
Definition reg_def (src: list Z) (m: xmem) (r: xreg) (i n: Z) : Prop :=
  forall k, 0 <= k < n -> exists v, xm_rd src m r (i + k) = Some v.

(* the destination holds l from index i on (the block's input plays no role for R_dst) *)
Definition dst_has (m: xmem) (i: Z) (l: list Z) : Prop := reg_has nil m R_dst i l.

(* the destination cells from index a on are those of m (a copy wrote below a only) *)
Definition dst_same_from (m m': xmem) (a: Z) : Prop := forall p, a <= p -> dcell m' p = dcell m p.

(* ---------- the sequences ---------- *)

Definition sum_ll (l: list sequence) : Z := fold_right (fun sq a => sq_ll sq + a) 0 l.
Definition sum_ml (l: list sequence) : Z := fold_right (fun sq a => sq_ml sq + a) 0 l.

(* ---------- the invariant of the sequence loop ---------- *)

(* The literals left, lits, are where the execution state s reads them, followed by XWILDCOPY defined cells
   (zstd's copies read up to 32 bytes past the literals they copy):
   - not split: in region xlr from xli to xlim; when that region is the destination (literals placed after the
     block's room), the output end lies before them, so no store reaches them;
   - split: the first ones in the destination from xli to xlim, the last XLITEXTRA ones at the start of
     litExtraBuffer; the output is at least XLITEXTRA - XWILDCOPY bytes plus the matches still to come (M)
     before the literals, so no store of the output reaches a literal not yet read. *)
Definition lit_inv (e: xenv) (s: xex) (lits: list Z) (M: Z) : Prop :=
  if xsp s then
    exists Ld Lx, lits = Ld ++ Lx /\ Zlength Lx = XLITEXTRA /\
      dst_has (xmm s) (xli s) Ld /\ xlim s = xli s + Zlength Ld /\
      reg_def (xe_src e) (xmm s) R_dst (xlim s) XWILDCOPY /\
      reg_has (xe_src e) (xmm s) R_lxb 0 Lx /\ Zlength (xm_lxb (xmm s)) = XLITEXTRA + XWILDCOPY /\
      xop s + M + XLITEXTRA - XWILDCOPY <= xli s
  else
    0 <= xli s /\
    reg_has (xe_src e) (xmm s) (xlr s) (xli s) lits /\ xlim s = xli s + Zlength lits /\
    reg_def (xe_src e) (xmm s) (xlr s) (xlim s) XWILDCOPY /\
    (xlr s = R_dst -> xe_oend e <= xli s).

(* The execution state s of a block decoded one-shot without a dictionary (prefixStart = virtualStart = 0)
   stands for the format model's output so far outc (the destination's first cells, op at its end) and
   literals left lits; M = the total match length of the sequences still to execute, and the content still
   to come (lits and the matches) fits before the output end. *)
Definition ex_inv (e: xenv) (s: xex) (outc lits: list Z) (M: Z) : Prop :=
  xe_ps e = 0 /\ xe_vs e = 0 /\ xop s = Zlength outc /\ dst_has (xmm s) 0 outc /\
  0 <= M /\ xop s + Zlength lits + M <= xe_oend e /\ lit_inv e s lits M.

(* the number of literals the state s has left to read *)
Definition xcnt (s: xex) : Z := if xsp s then xlim s - xli s + XLITEXTRA else xlim s - xli s.

(* ---------- decoding one sequence ---------- *)

(* Block.decode_seqs takes, sequence by sequence, the step ExCSeq.dseq_one the exact model takes (with the
   state update omitted after the last one). *)
Lemma decode_seqs_step : forall tLL tOF tML V k sLL sOF sML pos l p,
  decode_seqs tLL tOF tML V (S k) sLL sOF sML pos = Some (l, p) ->
  exists sq nLL nOF nML pos' l',
    dseq_one tLL tOF tML V (Nat.eqb k 0) sLL sOF sML pos = Some (sq, (nLL, nOF, nML), pos') /\
    l = sq :: l' /\ decode_seqs tLL tOF tML V k nLL nOF nML pos' = Some (l', p).
Proof.
  intros tLL tOF tML V k sLL sOF sML pos l p H.
  simpl in H. unfold dseq_one.
  destruct (rd V pos _) as [[eOF p1]|]; [|discriminate].
  destruct (rd V p1 _) as [[eML p2]|]; [|discriminate].
  destruct (rd V p2 _) as [[eLL p3]|]; [|discriminate].
  destruct k as [|k'].
  - inversion H; subst. do 6 eexists. split; [reflexivity|]. split; [reflexivity|]. reflexivity.
  - simpl Nat.eqb. cbv iota.
    destruct (rd V p3 _) as [[uLL p4]|]; [|discriminate].
    destruct (rd V p4 _) as [[uML p5]|]; [|discriminate].
    destruct (rd V p5 _) as [[uOF p6]|]; [|discriminate].
    destruct (decode_seqs _ _ _ _ _ _ _ _ _) as [[l' p']|] eqn:E; [|discriminate].
    inversion H; subst. do 6 eexists. split; [reflexivity|]. split; [reflexivity|]. exact E.
Qed.
