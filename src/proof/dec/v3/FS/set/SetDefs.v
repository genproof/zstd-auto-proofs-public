(* FS3, the DDict hash set part: what the set proofs share.
   - (ZSTD_getDictID_fromDDict: FSSpecs3.ZSTD_getDictID_fromDDict_int_spec, on ddid-or-NULL);
   - hs_inv0: hs_inv without the upper size bound (a table being refilled by ZSTD_DDictHashSet_expand);
   - the specifications chosen for ZSTD_DDictHashSet_getIndex, _emplaceDDict, _expand;
   - PF_*: the plain-Coq facts the bodies use (proved in SetPure.v), MF_*: the memory facts (SetMem.v);
   - the small function contexts G_* of the bodies (lifted to FS3_G by body_ok_mono in body3_set.v). *)
Require Export Zstd.proof.dec.v3.FS.FSOblig3.
Local Open Scope logic.

Section CM_SetDefs_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* ---------- the weak invariant, the raw set ---------- *)

Definition hs_nonnull (tbl: list val) : list val := filter (fun v => negb (veqb v nullval)) tbl.

Definition hs_inv0 (l: list (val * ddict_st)) (tbl: list val) : Prop :=
  let n := Zlength tbl in
  (exists k, 6 <= k /\ n = 2 ^ k) /\ Zlength l < n /\
  NoDup (map fst l) /\ ids_distinct (map (fun e => dd_id (snd e)) l) = true /\
  Forall (fun e => isptr (fst e)) l /\
  Permutation (hs_nonnull tbl) (map fst l) /\
  Forall (fun v => v = nullval \/ isptr v) tbl /\
  (forall j e, 0 <= j < n -> In e l -> Znth j tbl = fst e ->
     forall t, 0 <= t < (j - hs_home (dd_id (snd e)) n) mod n ->
       Znth (hs_slot (hs_home (dd_id (snd e)) n) t n) tbl <> nullval).

(* the set struct at sp with table tbl and count |l|, no invariant, allocated through am *)
Definition hs_raw (am: option cmem) (sp: val) (l: list (val * ddict_st)) (tbl: list val) : mpred :=
  EX tp: val,
  blk_tok am t_hset sp *
  data_at Ews t_hset (tp, (Vlong (Int64.repr (Zlength tbl)), Vlong (Int64.repr (Zlength l)))) sp *
  hs_table am tp tbl.

(* the allocator's state does not depend on the count of bytes for the default allocator *)
Lemma cm_have_eq (am: option cmem) (h h': Z) : (am <> None -> h = h') -> cm_have am h |-- cm_have am h'.
Proof. destruct am as [m|]; simpl; intros E; [rewrite E by discriminate|]; apply derives_refl. Qed.

Lemma cm_room_le (am: option cmem) (h n n': Z) : cm_room am h n -> 0 <= n' <= n -> cm_room am h n'.
Proof. destruct am; simpl; lia. Qed.

Lemma cm_room_shift (am: option cmem) (h a b: Z) : cm_room am h (a + b) -> 0 <= a -> 0 <= b -> cm_room am (h + a) b.
Proof. destruct am; simpl; lia. Qed.

(* the member of l at pointer v (expand re-adds the old table's entries in slot order) *)
Definition set_entry (l: list (val * ddict_st)) (v: val) : val * ddict_st :=
  match find (fun e => veqb (fst e) v) l with
  | Some e => e
  | None => (v, {| dd_bytes := nil; dd_ref := None; dd_buf := nullval; dd_ld := None |})
  end.

Definition l_upto (l: list (val * ddict_st)) (tbl: list val) (i: Z) : list (val * ddict_st) :=
  map (set_entry l) (hs_nonnull (sublist 0 i tbl)).

(* ---------- the chosen specifications ---------- *)

(* XXH64 of the 4 bytes of dictID, masked by the table size (read from the struct) *)
Definition getIndex_spec3 : ident * funspec :=
  DECLARE _ZSTD_DDictHashSet_getIndex
  WITH sh: share, sp: val, tp: val, n: Z, c: val, id: Z
  PRE [ tptr t_hset, tuint ]
    PROP (readable_share sh; 0 <= id <= Int.max_unsigned; 1 <= n <= Int64.max_unsigned)
    PARAMS (sp; Vint (Int.repr id))
    SEP (data_at sh t_hset (tp, (Vlong (Int64.repr n), c)) sp)
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr (hs_home id n)))
    SEP (data_at sh t_hset (tp, (Vlong (Int64.repr n), c)) sp).

(* emplace the DDict q (an entry (q, dd) of L, whose IDs the caller lends) into the members l: set_add *)
Definition emplace_spec3 : ident * funspec :=
  DECLARE _ZSTD_DDictHashSet_emplaceDDict
  WITH sp: val, tp: val, L: list (val * ddict_st), l: list (val * ddict_st), tbl: list val, q: val,
       dd: ddict_st
  PRE [ tptr t_hset, tptr t_ddict ]
    PROP (hs_inv0 l tbl; Zlength l + 1 < Zlength tbl; Zlength tbl <= 2 ^ 30;
          In (q, dd) L; NoDup (map fst L); incl l L; ~ In q (map fst l))
    PARAMS (sp; q)
    SEP (data_at Ews t_hset (tp, (Vlong (Int64.repr (Zlength tbl)), Vlong (Int64.repr (Zlength l)))) sp;
         data_at Ews (tarray (tptr t_ddict) (Zlength tbl)) tbl tp; set_ids L)
  POST [ tulong ]
    EX tbl': list val,
    PROP (hs_inv0 (set_add l q dd) tbl'; Zlength tbl' = Zlength tbl)
    RETURN (Vlong (Int64.repr 0))
    SEP (data_at Ews t_hset
           (tp, (Vlong (Int64.repr (Zlength tbl)), Vlong (Int64.repr (Zlength (set_add l q dd))))) sp;
         data_at Ews (tarray (tptr t_ddict) (Zlength tbl)) tbl' tp; set_ids L).

(* double the table and re-emplace (the same members), or a memory error with the set unchanged; the tables go
   through the allocator am, which has given out h bytes and needs room for the new table while the old one is
   still held; afterwards it holds the bytes of the new table instead of the old one's (FSRep3.set_bytes) *)
Definition expand_spec3 : ident * funspec :=
  DECLARE _ZSTD_DDictHashSet_expand
  WITH gv: globals, sp: val, l: list (val * ddict_st), tbl: list val, shm: share, pm: val, am: option cmem, h: Z
  PRE [ tptr t_hset, tptr t_cmem ]
    PROP (readable_share shm; hs_inv l tbl; Zlength tbl <= 2 ^ 23; cmem_ok am;
          cm_room am h (8 * (2 * Zlength tbl)))
    PARAMS (sp; pm) GLOBALS (gv)
    SEP (mem_mgr gv; data_at shm t_cmem (cmem_v am) pm; cm_have am h; hs_raw am sp l tbl; set_ids l)
  POST [ tulong ]
    EX r: Z, EX tbl': list val,
    PROP ((r = 0 /\ hs_inv0 l tbl' /\ Zlength tbl' = (2 * Zlength tbl)%Z) \/
          (r = err_code ZSTD_error_memory_allocation /\ tbl' = tbl))
    RETURN (Vlong (Int64.repr r))
    SEP (mem_mgr gv; data_at shm t_cmem (cmem_v am) pm;
         cm_have am (h + set_bytes am (Zlength tbl') - set_bytes am (Zlength tbl)); hs_raw am sp l tbl'; set_ids l).

(* ---------- the function contexts of the bodies ---------- *)

Definition G_getIndex : funspecs := [ ZSTD_XXH64_spec ].
Definition G_emplace : funspecs := [ ZSTD_getDictID_fromDDict_int_spec; getIndex_spec3 ].
Definition G_expand : funspecs := [ ERR_isError_spec; ZSTD_customCallocP_cm_spec; ZSTD_customFreeP_cm_spec; emplace_spec3 ].
Definition G_getDDict : funspecs := [ ZSTD_getDictID_fromDDict_int_spec; getIndex_spec3 ].
Definition G_create : funspecs := [ ZSTD_customMallocP_cm_spec; ZSTD_customCallocP_cm_spec; ZSTD_customFreeP_cm_spec ].
Definition G_free : funspecs := [ ZSTD_customFreeP_cm_spec ].
Definition G_add : funspecs := [ ERR_isError_spec; emplace_spec3; expand_spec3 ].

(* ---------- plain-Coq facts (SetPure.v) ---------- *)

Definition PF_member : Prop := forall l tbl j,
  hs_inv0 l tbl -> 0 <= j < Zlength tbl -> Znth j tbl <> nullval -> exists e, In e l /\ fst e = Znth j tbl.

Definition PF_set_id : Prop := forall (l: list (val * ddict_st)) e,
  NoDup (map fst l) -> In e l -> set_id_of l (fst e) = dd_id (snd e).

Definition PF_notfull : Prop := forall l tbl h,
  hs_inv0 l tbl -> 0 <= h < Zlength tbl ->
  exists t, 0 <= t < Zlength tbl /\ Znth (hs_slot h t (Zlength tbl)) tbl = nullval.

Definition PF_inv0 : Prop := forall l tbl, hs_inv l tbl -> hs_inv0 l tbl.

(* emplace: the probe from q's home reaches a NULL slot (t probes, none of the same ID): q joins *)
Definition PF_insert : Prop := forall l tbl q dd t,
  let n := Zlength tbl in let h := hs_home (dd_id dd) n in
  hs_inv0 l tbl -> Zlength l + 1 < n -> isptr q -> ~ In q (map fst l) -> 0 <= t < n ->
  Znth (hs_slot h t n) tbl = nullval ->
  (forall t', 0 <= t' < t ->
     Znth (hs_slot h t' n) tbl <> nullval /\ set_id_of l (Znth (hs_slot h t' n) tbl) <> dd_id dd) ->
  set_add l q dd = l ++ [(q, dd)] /\
  hs_inv0 (l ++ [(q, dd)]) (upd_Znth (hs_slot h t n) tbl q).

(* emplace: a slot on the probe holds a DDict of the same ID: q replaces it *)
Definition PF_replace : Prop := forall l tbl q dd t,
  let n := Zlength tbl in let h := hs_home (dd_id dd) n in
  hs_inv0 l tbl -> isptr q -> ~ In q (map fst l) -> 0 <= t < n ->
  Znth (hs_slot h t n) tbl <> nullval -> set_id_of l (Znth (hs_slot h t n) tbl) = dd_id dd ->
  Zlength (set_add l q dd) = Zlength l /\ hs_inv0 (set_add l q dd) (upd_Znth (hs_slot h t n) tbl q).

(* a fresh set (ZSTD_createDDictHashSet) *)
Definition PF_init : Prop := hs_inv nil (Zrepeat nullval 64).

Definition PF_exp_init : Prop := forall k, 6 <= k -> hs_inv0 nil (Zrepeat nullval (2 ^ k)).

Definition PF_exp_step : Prop := forall l tbl i,
  hs_inv l tbl -> 0 <= i < Zlength tbl -> Znth i tbl <> nullval ->
  set_entry l (Znth i tbl) = (Znth i tbl, snd (set_entry l (Znth i tbl))) /\
  In (set_entry l (Znth i tbl)) l /\
  incl (l_upto l tbl i) l /\ ~ In (Znth i tbl) (map fst (l_upto l tbl i)) /\
  Zlength (l_upto l tbl i) < Zlength l /\
  set_add (l_upto l tbl i) (Znth i tbl) (snd (set_entry l (Znth i tbl))) = l_upto l tbl (i + 1).

Definition PF_exp_skip : Prop := forall l tbl i,
  0 <= i < Zlength tbl -> Znth i tbl = nullval -> l_upto l tbl (i + 1) = l_upto l tbl i.

Definition PF_exp_end : Prop := forall l tbl tbl',
  hs_inv l tbl -> hs_inv0 (l_upto l tbl (Zlength tbl)) tbl' ->
  hs_inv0 l tbl' /\ Zlength (l_upto l tbl (Zlength tbl)) = Zlength l.

Definition PF_add_noexp : Prop := forall l tbl tbl' q dd,
  hs_inv l tbl -> (4 * Zlength l < Zlength tbl)%Z -> Zlength tbl' = Zlength tbl ->
  hs_inv0 (set_add l q dd) tbl' -> hs_inv (set_add l q dd) tbl'.

Definition PF_add_exp : Prop := forall l tbl tbl' q dd,
  hs_inv l tbl -> (Zlength tbl <= 4 * Zlength l)%Z -> Zlength tbl' = (2 * Zlength tbl)%Z ->
  hs_inv0 (set_add l q dd) tbl' -> hs_inv (set_add l q dd) tbl'.

(* ---------- memory facts (SetMem.v) ---------- *)

(* calloc'd zero bytes (with malloc's alignment) are a table of NULL pointers *)
Definition MF_calloc_tbl : Prop := forall p n,
  0 <= n -> (8 * n)%Z <= Ptrofs.max_unsigned -> malloc_compatible (8 * n) p ->
  data_at Ews (tarray tuchar (8 * n)%Z) (Zrepeat (Vint Int.zero) (8 * n)%Z) p
  |-- data_at Ews (tarray (tptr t_ddict) n) (Zrepeat nullval n) p.

(* a table is bytes for free *)
Definition MF_tbl_bytes : Prop := forall p n (tbl: list val),
  Zlength tbl = n -> data_at Ews (tarray (tptr t_ddict) n) tbl p |-- data_at_ Ews (tarray tuchar (8 * n)%Z) p.

(* a uint is its 4 little-endian bytes *)
Definition MF_uint_bytes : Prop := forall sh p id,
  0 <= id <= Int.max_unsigned -> field_compatible tuint nil p ->
  data_at sh tuint (Vint (Int.repr id)) p = data_at sh (tarray tuchar 4) (xxh_bytes (le_bytes 4 id)) p.

Definition MF_ids_focus : Prop := forall (L: list (val * ddict_st)) e,
  In e L -> exists L1 L2, L = L1 ++ e :: L2 /\ set_ids L = ddid (fst e) (dd_id (snd e)) (ddb (snd e)) * set_ids (L1 ++ L2).

Definition MF_ids_app : Prop := forall (L: list (val * ddict_st)) x,
  set_ids (L ++ [x]) = set_ids L * ddid (fst x) (dd_id (snd x)) (ddb (snd x)).

(* what a ddid gives: zstd tests a set member against NULL, and compares its uint dictID *)
Definition MF_ddid_wvp : Prop := forall q id db, ddid q id db |-- weak_valid_pointer q.

Definition MF_ddid_range : Prop := forall q id db, ddid q id db |-- !! (0 <= id <= Int.max_unsigned).

End CM_SetDefs_1.
