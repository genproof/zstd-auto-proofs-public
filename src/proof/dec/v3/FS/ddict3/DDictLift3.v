(* FS3 ddict3: the DDict bodies are proved against their callees only and lifted to FS3_G (Layer.body_ok_mono). *)
Require Import Zstd.proof.dec.v3.FS.FSOblig3.
Local Open Scope logic.

Section CM_DDictLift3_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma ddict3_nodup DENT TABS SR BR : NoDup (map fst Vprog ++ map fst (FS3_G DENT TABS SR BR)).
Proof. apply list_norepet_NoDup. apply compute_list_norepet_e. vm_compute. reflexivity. Qed.

Lemma ddict3_lift (G: funspecs) (ix: ident * funspec) DENT TABS SR BR :
  Forall (fun x => initial_world.find_id (fst x) (FS3_G DENT TABS SR BR) = Some (snd x)) G ->
  body_ok G ix -> body_ok (FS3_G DENT TABS SR BR) ix.
Proof.
  intros HG Hb. apply (body_ok_mono G); [exact Hb | | apply ddict3_nodup].
  intros [i phi] Hx. rewrite Forall_forall in HG. apply initial_world.find_id_e. exact (HG _ Hx).
Qed.


End CM_DDictLift3_1.

Ltac ddict3_in := repeat constructor; reflexivity.
