(* The format model: FSE decoding tables (RFC 8878, 4.1.1) and the sequence codes (3.1.1.3.2.1).

   A decoding table of accuracy log `log` has 2^log states; state t gives (symbol, nbBits, base):
   decoding emits `symbol`, then the next state is base + (the next nbBits bits of the bitstream).
   `fse_build norm log` is the specification's construction from a normalized distribution
   (norm[s] = -1 for "less than 1"); it is also what harness/build.h's fse_build computes. *)
Require Import Zstd.proof.model.Bytes.

Record fse_entry := { fe_sym : Z; fe_nb : Z; fe_base : Z }.
Record fse_table := { ft_log : Z; ft_cells : list fse_entry }.

Definition fse_cell (t: fse_table) (state: Z) : fse_entry :=
  nth (Z.to_nat state) (ft_cells t) {| fe_sym := 0; fe_nb := 0; fe_base := 0 |}.

(* list update at position i *)
Fixpoint upd {A} (l: list A) (i: nat) (x: A) : list A :=
  match l, i with
  | nil, _ => nil
  | _ :: l', O => x :: l'
  | y :: l', S i' => y :: upd l' i' x
  end.

Section Build.
Variables (norm: list Z) (log: Z).
Let size : Z := 2 ^ log.
Let nsym : nat := length norm.
Let mask : Z := size - 1.
Let step : Z := Z.shiftr size 1 + Z.shiftr size 3 + 3.

(* 1. the "less than 1" symbols, from the top: returns (symbol table, high) *)
Fixpoint place_low (s: nat) (n: nat) (tab: list Z) (high: Z) : list Z * Z :=
  match n with
  | O => (tab, high)
  | S n' =>
      if nth s norm 0 =? -1 then place_low (S s) n' (upd tab (Z.to_nat high) (Z.of_nat s)) (high - 1)
      else place_low (S s) n' tab high
  end.

(* skip the positions above high *)
Fixpoint skip_high (fuel: nat) (high pos: Z) : Z :=
  match fuel with
  | O => pos
  | S f => if pos >? high then skip_high f high (Z.land (pos + step) mask) else pos
  end.

(* 2. spread symbol s, k times, from pos *)
Fixpoint spread_one (k: nat) (s: Z) (high: Z) (tab: list Z) (pos: Z) : list Z * Z :=
  match k with
  | O => (tab, pos)
  | S k' =>
      let tab := upd tab (Z.to_nat pos) s in
      let pos := skip_high (Z.to_nat size) high (Z.land (pos + step) mask) in
      spread_one k' s high tab pos
  end.

Fixpoint spread (s: nat) (n: nat) (high: Z) (tab: list Z) (pos: Z) : list Z :=
  match n with
  | O => tab
  | S n' =>
      let c := nth s norm 0 in
      let '(tab, pos) := if c >? 0 then spread_one (Z.to_nat c) (Z.of_nat s) high tab pos else (tab, pos) in
      spread (S s) n' high tab pos
  end.

(* 3. the states: next[s] starts at max(norm[s], 1) and counts up *)
Fixpoint states (tab: list Z) (next: list Z) : list fse_entry :=
  match tab with
  | nil => nil
  | s :: tab' =>
      let x := nth (Z.to_nat s) next 0 in
      let nb := log - highbit x in
      {| fe_sym := s; fe_nb := nb; fe_base := Z.shiftl x nb - size |}
        :: states tab' (upd next (Z.to_nat s) (x + 1))
  end.

Definition fse_build : fse_table :=
  let '(tab, high) := place_low 0 nsym (repeat 0 (Z.to_nat size)) (size - 1) in
  let tab := spread 0 nsym high tab 0 in
  let next := map (fun c => if c =? -1 then 1 else c) norm in
  {| ft_log := log; ft_cells := states tab next |}.
End Build.

Definition fse_rle (sym: Z) : fse_table :=
  {| ft_log := 0; ft_cells := [ {| fe_sym := sym; fe_nb := 0; fe_base := 0 |} ] |}.

(* The predefined distributions (RFC 8878, 3.1.1.3.2.2) *)
Definition LL_norm : list Z := [4; 3; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 1; 1; 1; 2; 2; 2; 2; 2; 2; 2; 2; 2; 3; 2;
  1; 1; 1; 1; 1; -1; -1; -1; -1].
Definition ML_norm : list Z := [1; 4; 3; 2; 2; 2; 2; 2; 2; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1;
  1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; -1; -1; -1; -1; -1; -1; -1].
Definition OF_norm : list Z := [1; 1; 1; 1; 1; 1; 2; 2; 2; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; -1; -1;
  -1; -1; -1].

Definition LL_predef : fse_table := fse_build LL_norm 6.
Definition ML_predef : fse_table := fse_build ML_norm 6.
Definition OF_predef : fse_table := fse_build OF_norm 5.

(* The codes (RFC 8878, 3.1.1.3.2.1.1): baseline and number of extra bits *)
Definition LL_base_tab : list Z := [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 18; 20; 22; 24;
  28; 32; 40; 48; 64; 128; 256; 512; 1024; 2048; 4096; 8192; 16384; 32768; 65536].
Definition LL_bits_tab : list Z := [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 1; 1; 1; 2; 2; 3; 3;
  4; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16].
Definition ML_base_tab : list Z := [3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23;
  24; 25; 26; 27; 28; 29; 30; 31; 32; 33; 34; 35; 37; 39; 41; 43; 47; 51; 59; 67; 83; 99; 131; 259; 515; 1027;
  2051; 4099; 8195; 16387; 32771; 65539].
Definition ML_bits_tab : list Z := [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
  0; 0; 0; 0; 0; 0; 0; 0; 1; 1; 1; 1; 2; 2; 3; 3; 4; 4; 5; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16].

Definition MaxLL : Z := 35.
Definition MaxML : Z := 52.
Definition MaxOff : Z := 31.

(* Sanity: the predefined tables have 64/64/32 states and the first states of RFC 8878's
   Appendix A (literal lengths: state 0 = symbol 0, 4 bits, base 0; state 1 = symbol 0, 4 bits, base 16). *)
Example LL_predef_size : length (ft_cells LL_predef) = 64%nat. Proof. vm_compute. reflexivity. Qed.
Example OF_predef_size : length (ft_cells OF_predef) = 32%nat. Proof. vm_compute. reflexivity. Qed.
Example LL_predef_0 : fse_cell LL_predef 0 = {| fe_sym := 0; fe_nb := 4; fe_base := 0 |}.
Proof. vm_compute. reflexivity. Qed.
Example LL_predef_1 : fse_cell LL_predef 1 = {| fe_sym := 0; fe_nb := 4; fe_base := 16 |}.
Proof. vm_compute. reflexivity. Qed.
