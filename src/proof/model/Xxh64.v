(* The format model: XXH64 (the frame checksum is its low 32 bits on the frame's content, seed 0).
   A functional transcription of lib/common/xxhash.h (XXH64, XXH64_finalize, XXH64_avalanche), on
   unbounded integers reduced mod 2^64. *)
Require Import Zstd.proof.model.Bytes.

Definition m64 (x: Z) : Z := x mod 2^64.
Definition XXH_P1 : Z := 11400714785074694791.  (* 0x9E3779B185EBCA87 *)
Definition XXH_P2 : Z := 14029467366897019727.  (* 0xC2B2AE3D27D4EB4F *)
Definition XXH_P3 : Z := 1609587929392839161.   (* 0x165667B19E3779F9 *)
Definition XXH_P4 : Z := 9650029242287828579.   (* 0x85EBCA77C2B2AE63 *)
Definition XXH_P5 : Z := 2870177450012600261.   (* 0x27D4EB2F165667C5 *)

Definition rotl64 (x r: Z) : Z := m64 (Z.lor (Z.shiftl x r) (Z.shiftr (m64 x) (64 - r))).

Definition xxh_round (acc input: Z) : Z :=
  m64 (rotl64 (m64 (acc + m64 (input * XXH_P2))) 31 * XXH_P1).

Definition xxh_merge (acc v: Z) : Z :=
  m64 (Z.lxor acc (xxh_round 0 v) * XXH_P1 + XXH_P4).

Definition xxh_avalanche (h: Z) : Z :=
  let h := Z.lxor h (Z.shiftr h 33) in
  let h := m64 (h * XXH_P2) in
  let h := Z.lxor h (Z.shiftr h 29) in
  let h := m64 (h * XXH_P3) in
  Z.lxor h (Z.shiftr h 32).

(* the 32-byte stripes: four accumulators *)
Fixpoint xxh_stripes (n: nat) (v: Z * Z * Z * Z) (l: list Z) : (Z * Z * Z * Z) * list Z :=
  match n with
  | O => (v, l)
  | S n' =>
      match v with (v1, v2, v3, v4) =>
        if Z.of_nat (length l) <? 32 then (v, l) else
        let v1 := xxh_round v1 (le_field l 0 8) in
        let v2 := xxh_round v2 (le_field l 8 8) in
        let v3 := xxh_round v3 (le_field l 16 8) in
        let v4 := xxh_round v4 (le_field l 24 8) in
        xxh_stripes n' (v1, v2, v3, v4) (skipn 32 l)
      end
  end.

(* XXH64_finalize on the remaining (< 32) bytes *)
Fixpoint xxh_tail8 (n: nat) (h: Z) (l: list Z) : Z * list Z :=
  match n with
  | O => (h, l)
  | S n' =>
      if Z.of_nat (length l) <? 8 then (h, l) else
      let k1 := xxh_round 0 (le_field l 0 8) in
      let h := m64 (rotl64 (Z.lxor h k1) 27 * XXH_P1 + XXH_P4) in
      xxh_tail8 n' h (skipn 8 l)
  end.

Definition xxh_tail4 (h: Z) (l: list Z) : Z * list Z :=
  if Z.of_nat (length l) <? 4 then (h, l) else
  let h := Z.lxor h (m64 (le_field l 0 4 * XXH_P1)) in
  (m64 (rotl64 h 23 * XXH_P2 + XXH_P3), skipn 4 l).

Fixpoint xxh_tail1 (h: Z) (l: list Z) : Z :=
  match l with
  | nil => h
  | b :: l' => xxh_tail1 (m64 (rotl64 (Z.lxor h (m64 (b * XXH_P5))) 11 * XXH_P1)) l'
  end.

Definition xxh_finalize (h: Z) (rest: list Z) : Z :=
  let (h, r) := xxh_tail8 4%nat h rest in
  let (h, r) := xxh_tail4 h r in
  xxh_avalanche (xxh_tail1 h r).

(* XXH64 as the streaming digest computes it (total length mod 2^64; the stripes always run): the same as the
   one-shot XXH64 (xxh64_br below) for every input shorter than 2^64 bytes (lemma xxh64_br_eq). *)
Definition xxh64 (input: list Z) (seed: Z) : Z :=
  let len := Z.of_nat (length input) in
  let '((v1, v2, v3, v4), rest) :=
    xxh_stripes (length input) (m64 (seed + XXH_P1 + XXH_P2), m64 (seed + XXH_P2), m64 seed, m64 (seed - XXH_P1)) input in
  let h :=
    if m64 len >=? 32 then
      let h := m64 (rotl64 v1 1 + rotl64 v2 7 + rotl64 v3 12 + rotl64 v4 18) in
      let h := xxh_merge h v1 in
      let h := xxh_merge h v2 in
      let h := xxh_merge h v3 in
      xxh_merge h v4
    else m64 (v3 + XXH_P5) in
  xxh_finalize (m64 (h + len)) rest.

(* the one-shot XXH64 (XXH64_endian_align): the long branch only for >= 32 bytes *)
Definition xxh64_br (input: list Z) (seed: Z) : Z :=
  let len := Z.of_nat (length input) in
  let '(h, rest) :=
    if m64 len >=? 32 then
      let '((v1, v2, v3, v4), rest) :=
        xxh_stripes (length input) (m64 (seed + XXH_P1 + XXH_P2), m64 (seed + XXH_P2), m64 seed, m64 (seed - XXH_P1)) input in
      let h := m64 (rotl64 v1 1 + rotl64 v2 7 + rotl64 v3 12 + rotl64 v4 18) in
      let h := xxh_merge h v1 in
      let h := xxh_merge h v2 in
      let h := xxh_merge h v3 in
      let h := xxh_merge h v4 in
      (h, rest)
    else (m64 (seed + XXH_P5), input) in
  xxh_finalize (m64 (h + len)) rest.

Lemma xxh64_br_eq: forall input seed, Z.of_nat (length input) < 2 ^ 64 ->
  xxh64 input seed = xxh64_br input seed.
Proof.
  intros input seed Hl. unfold xxh64, xxh64_br.
  assert (Hm: m64 (Z.of_nat (length input)) = Z.of_nat (length input))
    by (unfold m64; apply Z.mod_small; lia).
  rewrite Hm.
  destruct (Z.of_nat (length input) >=? 32) eqn:E.
  - destruct (xxh_stripes _ _ _) as [[[[v1 v2] v3] v4] r]. reflexivity.
  - assert (E': Z.of_nat (length input) < 32) by (rewrite Z.geb_leb, Z.leb_gt in E; lia).
    replace (xxh_stripes (length input) (m64 (seed + XXH_P1 + XXH_P2), m64 (seed + XXH_P2), m64 seed, m64 (seed - XXH_P1)) input)
      with ((m64 (seed + XXH_P1 + XXH_P2), m64 (seed + XXH_P2), m64 seed, m64 (seed - XXH_P1)), input).
    + replace (m64 (m64 seed + XXH_P5)) with (m64 (seed + XXH_P5)); [reflexivity|].
      unfold m64. rewrite Zplus_mod_idemp_l. reflexivity.
    + destruct (length input) eqn:L; simpl. reflexivity.
      rewrite L. replace (Z.of_nat (S n) <? 32) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

(* Test vectors (xxhash's reference values): XXH64("", 0) = 0xEF46DB3751D8E999,
   XXH64("a", 0) = 0xD24EC4F1A98C6E5B. *)
Example xxh64_empty : xxh64 [] 0 = 17241709254077376921. Proof. vm_compute. reflexivity. Qed.
Example xxh64_a : xxh64 [97] 0 = 15154266338359012955. Proof. vm_compute. reflexivity. Qed.
(* b[i] = (7 i + 3) mod 256, against the native lib/common/xxhash.h *)
Definition xxh_test_input (n: nat) : list Z := map (fun i => (7 * Z.of_nat i + 3) mod 256) (seq 0 n).
Example xxh64_100 : xxh64 (xxh_test_input 100) 0 = 11970441692518016305. Proof. vm_compute. reflexivity. Qed.
Example xxh64_37 : xxh64 (xxh_test_input 37) 0 = 16370292415966585853. Proof. vm_compute. reflexivity. Qed.
Example xxh64_13 : xxh64 (xxh_test_input 13) 0 = 17837354129420566472. Proof. vm_compute. reflexivity. Qed.
