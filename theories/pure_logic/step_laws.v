From iris.heap_lang Require Export lang notation.

(* primitive laws about [rtc erased_step] of HeapLang *)
Lemma erased_step_allocn (l : loc) (n : Z) (v : val) σ :
  (0 < n)%Z →
  (∀ i : Z, (0 ≤ i)%Z → (i < n)%Z → heap σ !! (l +ₗ i) = None) →
  erased_step ([AllocN #n v]%E, σ) ([Val #l], state_init_heap l n v σ).
Proof.
  intros Hn Hfresh. exists [].
  eapply (step_atomic _ _ _ _ _ []); rewrite ?left_id_L ?right_id_L; [reflexivity..|].
  apply base_prim_step. by econstructor.
Qed.

Lemma erased_step_alloc (l : loc) (v : val) σ :
  heap σ !! l = None →
  erased_step ([ref v]%E, σ) ([Val #l], state_init_heap l 1 v σ).
Proof.
  intros ?. apply erased_step_allocn; first lia.
  intros i ??. replace i with 0%Z by lia.
  by rewrite Loc.add_0.
Qed.

Lemma erased_step_load l (v : val) σ :
  heap σ !! l = Some (Some v) →
  erased_step ([(! #(LitLoc l))%E], σ) ([Val v], σ).
Proof.
  intros Hlookup. exists [].
  eapply (step_atomic _ _ _ _ _ []); rewrite ?left_id_L ?right_id_L; [reflexivity..|].
  apply base_prim_step. econstructor. done.
Qed.

Lemma erased_step_store l (v w : val) σ :
  heap σ !! l = Some (Some v) →
  erased_step ([(#(LitLoc l) <- w)%E], σ) ([Val #()], state_upd_heap <[l:=Some w]> σ).
Proof.
  intros Hlookup. exists [].
  eapply (step_atomic _ _ _ _ _ []); rewrite ?left_id_L ?right_id_L; [reflexivity..|].
  apply base_prim_step. econstructor. done.
Qed.

Lemma erased_step_cmpxchg_suc (l : loc) (v w : val) σ :
  vals_compare_safe v v →
  heap σ !! l = Some (Some v) →
  erased_step ([(CmpXchg #l v w)%E],σ) ([Val (v, #true)],state_upd_heap <[l:=Some w]> σ).
Proof.
  intros Hsafe Hlookup. exists [].
  eapply (step_atomic _ _ _ _ _ []); rewrite ?left_id_L ?right_id_L; [reflexivity..|].
  apply base_prim_step. econstructor; [done..|].
  by rewrite bool_decide_eq_true_2.
Qed.

Lemma erased_step_fork (e : expr) σ :
  erased_step ([Fork e], σ) ([Val #(); e], σ).
Proof.
  exists [].
  eapply (step_atomic _ _ _ _ _ [] []); rewrite ?left_id_L; [reflexivity..|].
  apply base_prim_step. constructor.
Qed.
