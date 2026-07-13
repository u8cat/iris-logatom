From iris.heap_lang Require Export proofmode notation.

Global Instance state_empty : Empty state :=
  {| heap := ∅; used_proph_id := ∅ |}.

Global Instance substate : SubsetEq state := λ σ1 σ2,
  σ1.(heap) ⊆ σ2.(heap) ∧ σ1.(used_proph_id) ⊆ σ2.(used_proph_id).

Global Instance state_disjoint : Disjoint state := λ σ1 σ2,
  σ1.(heap) ##ₘ σ2.(heap) ∧ σ1.(used_proph_id) ## σ2.(used_proph_id).

Global Instance state_union : Union state := λ σ1 σ2,
  {| heap := σ1.(heap) ∪ σ2.(heap); used_proph_id := σ1.(used_proph_id) ∪ σ2.(used_proph_id) |}.

Global Instance state_difference : Difference state := λ σ1 σ2,
  {| heap := σ1.(heap)∖σ2.(heap); used_proph_id := σ1.(used_proph_id)∖σ2.(used_proph_id) |}.

Global Instance substate_preorder : PreOrder (⊆@{state}).
Proof.
  constructor.
  - intros [h p]. rewrite /subseteq /substate //.
  - intros [h1 p1] [h2 p2] [h3 p3]. rewrite /subseteq /substate /=.
    intros [Hh12 Hp12] [Hh23 Hp23]. split; by etrans.
Qed.

Global Instance state_empty_left_id : LeftId (=@{state}) ∅ (∪).
Proof.
  intros [h p]. rewrite /union /state_union /= left_id.
  f_equal. set_solver.
Qed.

Global Instance state_empty_right_id : RightId (=@{state}) ∅ (∪).
Proof.
  intros [h p]. rewrite /union /state_union /= right_id.
  f_equal. set_solver.
Qed.

Lemma state_disjoint_difference_r1 (σ0 σ1 σ2 : state) :
  σ0 ⊆ σ2 → σ0 ## σ1∖σ2.
Proof.
  intros [Hsubseth%subseteq_dom Hsubsetp].
  split; first apply map_disjoint_dom; set_solver.
Qed.

Lemma state_disjoint_difference_l1 (σ1 σ2 σ0 : state) :
  σ0 ⊆ σ2 → σ1∖σ2 ## σ0.
Proof.
  intros [Hsubseth%subseteq_dom Hsubsetp].
  split; first apply map_disjoint_dom; set_solver.
Qed.

Lemma state_union_difference (σ1 σ2 : state) :
  σ1 ⊆ σ2 → σ2 = σ1 ∪ σ2∖σ1.
Proof.
  destruct σ1 as [h1 p1]. destruct σ2 as [h2 p2].
  intros [Hsubseth Hsubsetp]. simpl in Hsubseth, Hsubsetp.
  rewrite /union /difference /state_union /state_difference /=.
  f_equal.
  - rewrite map_difference_union //.
  - rewrite -union_difference_L //.
Qed.

Lemma state_union_comm (σ1 σ2 : state) :
  σ1 ## σ2 → σ1 ∪ σ2 = σ2 ∪ σ1.
Proof.
  intros [Hdisjm Hdisjp].
  destruct σ1, σ2. rewrite /union /state_union /=.
  f_equal.
  - by apply map_union_comm.
  - apply: comm.
Qed.

Local Lemma heap_difference_difference_r (h1 h2 : gmap loc (option val)) :
  h2 ⊆ h1 → (h1 ∖ (h1 ∖ h2)) = h2.
Proof.
  intros Hsubseth.
  rewrite map_subseteq_spec in Hsubseth.
  apply map_eq => l.
  rewrite !lookup_difference.
  destruct (h2!!l) as [h2l|] eqn:Hlookup2; first auto.
  destruct (h1!!l) as [h1l|] eqn:Hlookup1; auto.
Qed.

Lemma state_difference_difference_r (σ1 σ2 : state) :
  σ2 ⊆ σ1 → (σ1 ∖ (σ1 ∖ σ2)) = σ2.
Proof.
  destruct σ1 as [h1 p1]. destruct σ2 as [h2 p2].
  intros [Hsubseth Hsubsetp]. simpl in Hsubseth, Hsubsetp.
  rewrite /difference /state_difference /=.
  f_equal.
  - by apply heap_difference_difference_r.
  - rewrite difference_difference_r_L.
    set_solver.
Qed.

Lemma state_subseteq_difference_l (σ1 σ2 σ0 : state) :
  σ1 ⊆ σ0 → σ1∖σ2 ⊆ σ0.
Proof.
  destruct σ1, σ2, σ0.
  rewrite /subseteq /substate /difference /state_difference /=.
  intros [??]. split.
  - by apply map_subseteq_difference_l.
  - set_solver.
Qed.

Lemma state_disjoint_empty_l (σ : state) : ∅ ## σ.
Proof.
  rewrite /disjoint /state_disjoint. split.
  - apply map_disjoint_empty_l.
  - apply disjoint_empty_l.
Qed.

Lemma state_disjoint_empty_r (σ : state) : σ ## ∅.
Proof.
  rewrite /disjoint /state_disjoint. split.
  - apply map_disjoint_empty_r.
  - apply disjoint_empty_r.
Qed.

Lemma state_disjoint_union_l (σ1 σ2 σ0 : state) :
  σ1 ∪ σ2 ## σ0 ↔ σ1 ## σ0 ∧ σ2 ## σ0.
Proof.
  rewrite /disjoint /state_disjoint /union /state_union /=.
  rewrite map_disjoint_union_l disjoint_union_l.
  naive_solver.
Qed.

Lemma state_disjoint_union_r (σ0 σ1 σ2 : state) :
  σ0 ## σ1 ∪ σ2 ↔ σ0 ## σ1 ∧ σ0 ## σ2.
Proof.
  rewrite /disjoint /state_disjoint /union /state_union /=.
  rewrite map_disjoint_union_r disjoint_union_r.
  naive_solver.
Qed.

Global Instance : Assoc (=) (union (A:=state)).
Proof.
  intros σ1 σ2 σ3.
  by rewrite /union /state_union /= !assoc_L.
Qed.

Global Instance : Symmetric (disjoint (A:=state)).
Proof.
  intros σ1 σ2.
  rewrite /disjoint /state_disjoint.
  intros [H1 H2]. split; symmetry; done.
Qed.

Section substate.
  Implicit Types (e : expr) (σ : state) (κ κs : list observation) (efs : list expr).

  Local Lemma atomic_reducible_mono e σ σ' κ v σ2 efs : σ ⊆ σ' →
    base_step e σ κ (Val v) σ2 efs →
    (∃ κ v σ2, base_step e σ' κ (Val v) σ2 efs).
  Proof.
    intros [Hsubheap Hsubproph] Hbase_step.
    remember (Val v) as e2.
    induction Hbase_step; simplify_eq; try solve [do 3 eexists; econstructor; eauto using lookup_weaken].
    - do 3 eexists; econstructor; eauto.
      intros i Hi1 Hi2. apply not_elem_of_dom_1, Loc.fresh_fresh. done.
    - do 3 eexists; econstructor; eauto. apply is_fresh.
    - rename select (heap _ ⊆ _ → _) into IHHbase_step.
      destruct (IHHbase_step Hsubheap Hsubproph eq_refl) as (κ & v2 & σ2 & Hbase_step').
      do 3 eexists; econstructor; eauto.
  Qed.

  Lemma base_reducible_mono e σ σ' : σ ⊆ σ' → base_reducible e σ → base_reducible e σ'.
  Proof.
    intros [Hsubheap Hsubproph] Hred.
    destruct Hred as (κ & e2 & σ2 & efs & Hbase_step). simpl in *.
    destruct Hbase_step; simplify_eq; try solve [do 4 eexists; econstructor; eauto using lookup_weaken].
    - do 4 eexists; econstructor; eauto.
      intros i Hi1 Hi2. apply not_elem_of_dom_1, Loc.fresh_fresh. done.
    - do 4 eexists; econstructor; eauto. apply is_fresh.
    - rename select (base_step _ _ _ _ _ _) into Hbase_step.
      apply (atomic_reducible_mono _ _ σ') in Hbase_step as (κ & v' & σ2 & Hbase_step'); last done.
      do 4 eexists; econstructor; eauto.
  Qed.

  Lemma reducible_mono e σ σ' : σ ⊆ σ' → reducible e σ → reducible e σ'.
  Proof.
    intros Hsubstate Hred.
    destruct Hred as (κ & e2 & σ2 & efs & Hprim_step). simpl in *.
    destruct Hprim_step as [K e_ e2_ -> -> Hbase_step]. simpl in *.
    apply base_prim_fill_reducible.
    eapply base_reducible_mono; first eassumption.
    do 4 econstructor; eassumption.
  Qed.

  Local Lemma base_reducible_free_loc l σ :
    base_reducible (Free (Val (LitV (LitLoc l)))) σ →
    ∃ v, σ.(heap) !! l = Some (Some v).
  Proof.
    intros Hred.
    destruct Hred as (κ & e2 & σ2 & efs & Hbase_step).
    simpl in *.
    inversion Hbase_step. eauto.
  Qed.

  Local Lemma base_reducible_load_loc l σ :
    base_reducible (Load (Val (LitV (LitLoc l)))) σ →
    ∃ v, σ.(heap) !! l = Some (Some v).
  Proof.
    intros Hred.
    destruct Hred as (κ & e2 & σ2 & efs & Hbase_step).
    simpl in *.
    inversion Hbase_step. eauto.
  Qed.

  Local Lemma base_reducible_store_loc l w σ :
    base_reducible (Store (Val (LitV (LitLoc l))) (Val w)) σ →
    ∃ v, σ.(heap) !! l = Some (Some v).
  Proof.
    intros Hred.
    destruct Hred as (κ & e2 & σ2 & efs & Hbase_step).
    simpl in *.
    inversion Hbase_step. eauto.
  Qed.

  Local Lemma base_reducible_xchg_loc l v2 σ :
    base_reducible (Xchg (Val (LitV (LitLoc l))) (Val v2)) σ →
    ∃ v, σ.(heap) !! l = Some (Some v).
  Proof.
    intros Hred.
    destruct Hred as (κ & e2 & σ2 & efs & Hbase_step).
    simpl in *.
    inversion Hbase_step. eauto.
  Qed.

  Local Lemma base_reducible_cmpxchg_loc l v1 v2 σ :
    base_reducible (CmpXchg (Val (LitV (LitLoc l))) (Val v1) (Val v2)) σ →
    ∃ v, σ.(heap) !! l = Some (Some v).
  Proof.
    intros Hred.
    destruct Hred as (κ & e2 & σ2 & efs & Hbase_step).
    simpl in *.
    inversion Hbase_step. eauto.
  Qed.

  Local Lemma base_reducible_faa_loc l i2 σ :
    base_reducible (FAA (Val (LitV (LitLoc l))) (Val (LitV (LitInt i2)))) σ →
    ∃ i1, σ.(heap) !! l = Some (Some (LitV (LitInt i1))).
  Proof.
    intros Hred.
    destruct Hred as (κ & e2 & σ2 & efs & Hbase_step).
    simpl in *.
    inversion Hbase_step. eauto.
  Qed.

  Local Lemma base_reducible_resolve_red e p w σ σl κ v σ' efs :
    base_step e σ κ (Val v) σ' efs →
    base_reducible (Resolve e (Val (LitV (LitProphecy p))) (Val w)) σl →
    p ∈ σl.(used_proph_id) ∧ ∃ κl vl σl' efsl, base_step e σl κl (Val vl) σl' efsl.
  Proof.
    intros Hatomic Hred.
    destruct Hred as (? & e2 & σ2 & ? & Hbase_step).
    simpl in *.
    inversion Hbase_step. eauto 6.
  Qed.

  Local Lemma state_init_heap_subseteq l n v σ :
    (0 < n)%Z →
    (∀ i : Z, (0 ≤ i)%Z → (i < n)%Z → heap σ !! (l +ₗ i) = None) →
    σ ⊆ state_init_heap l n v σ.
  Proof.
    intros Hn Hfresh. destruct σ as [h p].
    rewrite /state_init_heap /subseteq /substate.
    simpl in *. split; last done.
    apply map_union_subseteq_r.
    apply heap_array_map_disjoint.
    rewrite length_replicate Z2Nat.id; [done|lia].
  Qed.

  Local Lemma subseteq_heap_update_local (σ σl : state) l v :
    σl ⊆ σ → is_Some (heap σl !! l) →
    σ ∖ σl ⊆ state_upd_heap <[l:=v]> σ.
  Proof.
    destruct σ as [h ?], σl as [hl ?].
    rewrite /subseteq /substate /=.
    intros [Hsubset ?] HisSome. split; last set_solver.
    clear - Hsubset HisSome.
    apply map_subseteq_spec => l' v' Hlookup.
    rewrite lookup_difference in Hlookup.
    destruct HisSome as [? Hhl_l'].
    destruct (decide (l = l')) as [<- | Hne].
    - rewrite Hhl_l' in Hlookup. discriminate Hlookup.
    - rewrite lookup_insert_ne //.
      destruct (hl!!l'); done.
  Qed.

  Local Lemma subseteq_used_proph_id_union_local (σ σl : state) p :
    σl ⊆ σ → p ∉ used_proph_id σ →
    σ ∖ σl ⊆ state_upd_used_proph_id (union {[p]}) σ.
  Proof.
    destruct σl, σ.
    rewrite /subseteq /substate /difference /state_difference /=.
    intros [??] ?. split.
    - by apply map_subseteq_difference_l.
    - set_solver.
  Qed.

  Local Lemma atomic_base_step_ext_subset e σ σl κ κl v vl σ' σl' efs efsl :
    σl ⊆ σ →
    base_step e σl κl (Val vl) σl' efsl →
    base_step e σ κ (Val v) σ' efs →
    σ ∖ σl ⊆ σ'.
  Proof.
    intros Hsubset Hbase_stepl Hbase_step.
    revert κl Hbase_stepl.
    induction Hbase_step => κl Hbase_stepl;
    try solve [apply state_subseteq_difference_l; reflexivity].
    - (* AllocN *)
      match goal with Hsubset: σl ⊆ ?x |- _ => rename x into σ end.
      trans σ; first by apply state_subseteq_difference_l.
      by apply state_init_heap_subseteq.
    - (* Free *)
      inversion Hbase_stepl. simplify_eq.
      apply subseteq_heap_update_local => //.
    - (* Store *)
      inversion Hbase_stepl. simplify_eq.
      apply subseteq_heap_update_local => //.
    - (* Xchg *)
      inversion Hbase_stepl. simplify_eq.
      apply subseteq_heap_update_local => //.
    - (* CmpXchg *)
      rename select bool into b.
      destruct b; last by apply state_subseteq_difference_l.
      inversion Hbase_stepl. simplify_eq.
      apply subseteq_heap_update_local => //.
    - (* FAA *)
      inversion Hbase_stepl. simplify_eq.
      apply subseteq_heap_update_local => //.
    - (* NewProph *)
      apply subseteq_used_proph_id_union_local => //.
    - (* Resolve *)
      inversion Hbase_stepl. simplify_eq.
      eauto.
  Qed.

  Local Lemma base_step_ext_subset e σ κ e' σ' efs σl :
    σl ⊆ σ → base_reducible e σl → base_step e σ κ e' σ' efs →
    σ ∖ σl ⊆ σ'.
  Proof.
    intros Hsubset Hred Hbase_step.
    destruct Hbase_step; try solve [apply state_subseteq_difference_l; reflexivity].
    - (* AllocN *)
      match goal with Hsubset: σl ⊆ ?x |- _ => rename x into σ end.
      trans σ; first by apply state_subseteq_difference_l.
      by apply state_init_heap_subseteq.
    - (* Free *)
      apply base_reducible_free_loc in Hred as [??].
      apply subseteq_heap_update_local => //.
    - (* Store *)
      apply base_reducible_store_loc in Hred as [??].
      apply subseteq_heap_update_local => //.
    - (* Xchg *)
      apply base_reducible_xchg_loc in Hred as [??].
      apply subseteq_heap_update_local => //.
    - (* CmpXchg *)
      rename select bool into b.
      destruct b; last by apply state_subseteq_difference_l.
      apply base_reducible_cmpxchg_loc in Hred as [??].
      apply subseteq_heap_update_local => //.
    - (* FAA *)
      apply base_reducible_faa_loc in Hred as [??].
      apply subseteq_heap_update_local => //.
    - (* NewProph *)
      apply subseteq_used_proph_id_union_local => //.
    - (* Resolve *)
      eapply base_reducible_resolve_red in Hred as [Hin (?&?&?&?&Hbase_step')]; last eassumption.
      by eapply atomic_base_step_ext_subset.
  Qed.

  Local Lemma fresh_heap_mono (h h' : gmap loc (option val) ) n (l : loc) :
    h ⊆ h' →
    (∀ i : Z, (0 ≤ i)%Z → (i < n)%Z → h' !! (l +ₗ i) = None) →
    (∀ i : Z, (0 ≤ i)%Z → (i < n)%Z → h !! (l +ₗ i) = None).
  Proof.
    intros Hsubset Hfresh i H0i Hin.
    eauto using lookup_weaken_None.
  Qed.

  Local Lemma init_heap_local (σ σl : state) l n v :
    σl ⊆ σ → (0 < n)%Z →
    (∀ i : Z, (0 ≤ i)%Z → (i < n)%Z → heap σ !! (l +ₗ i) = None) →
    state_init_heap l n v σ ∖ (σ ∖ σl) = state_init_heap l n v σl.
  Proof.
    intros Hsubstate H0n Hfresh.
    rewrite /state_init_heap /state_upd_heap /difference /state_difference /=.
    destruct Hsubstate.
    f_equal; last (rewrite difference_difference_r_L; set_solver).
    apply map_eq => l'.
    rewrite !lookup_difference !lookup_union.
    repeat case_match.
    - done.
    - apply eq_sym, union_None. split; last reflexivity.
      eapply map_disjoint_Some_r.
      + apply heap_array_map_disjoint.
        rewrite length_replicate Z2Nat.id; [done|lia].
      + eassumption.
    - f_equal. by eapply lookup_weaken.
    - f_equal. done.
  Qed.

  Local Lemma heap_update_local (σ σl : state) l v :
    σl ⊆ σ → is_Some (heap σl !! l) →
    state_upd_heap <[l:=v]> σ ∖ (σ ∖σl) = state_upd_heap <[l:=v]> σl.
  Proof.
    rewrite /state_upd_heap /subseteq /substate /difference /state_difference /=.
    intros [Hsubset ?] HisSome.
    f_equal; last (rewrite difference_difference_r_L; set_solver).
    apply map_eq => l'.
    destruct HisSome as [? Hσl_l].
    destruct (decide (l = l')) as [<-|Hne].
    - rewrite !lookup_difference !lookup_insert_eq Hσl_l //.
    - rewrite !lookup_difference !lookup_insert_ne //.
      destruct (heap σl !! l') eqn:?; first by eapply lookup_weaken.
      destruct (heap σ !! l'); done.
  Qed.

  Local Lemma used_proph_id_union_local (σ σl : state) p :
    σl ⊆ σ → p ∉ used_proph_id σ →
    state_upd_used_proph_id (union {[p]}) σ ∖ (σ ∖ σl) = state_upd_used_proph_id (union {[p]}) σl.
  Proof.
    rewrite /state_upd_used_proph_id /subseteq /substate /difference /state_difference /=.
    intros [? Hsubset] Hfresh.
    f_equal; first by apply heap_difference_difference_r.
    rewrite difference_union_distr_l_L.
    rewrite (difference_difference_r_L (used_proph_id σ)).
    set_solver.
  Qed.

  Local Lemma atomic_base_step_subset e σ σl κ κl v vl σ' σl' efs efsl  :
    σl ⊆ σ →
    base_step e σl κl (Val vl) σl' efsl →
    base_step e σ κ (Val v) σ' efs →
    base_step e σl κ (Val v) (σ'∖(σ∖σl)) efs.
  Proof.
    intros Hsubstate Hbase_stepl Hbase_step.
    remember (Val v) as val_v eqn:Heq.
    revert κl Hbase_stepl.
    induction Hbase_step => κl Hbase_stepl; try solve [
      inversion Hbase_stepl; simplify_eq;
      rewrite state_difference_difference_r //].
    - (* App (function call) *)
      inversion Hbase_stepl; simplify_eq.
      rename select (Val v = subst' _ _ _) into Heqv.
      rename select (Val vl = subst' _ _ _) into Heqvl.
      rewrite -Heqv in Heqvl.
      injection Heqvl as ->.
      rewrite state_difference_difference_r //.
    - (* AllocN *)
      inversion Hbase_stepl; simplify_eq.
      rewrite init_heap_local //.
      econstructor; first assumption.
      destruct Hsubstate.
      by eapply fresh_heap_mono.
    - (* Free *)
      inversion Hbase_stepl; simplify_eq.
      rewrite heap_update_local //.
    - (* Load *)
      inversion Hbase_stepl; simplify_eq.
      match goal with H: (heap ?σ0 !! ?l0 = Some (Some v)) |- _ =>
        rename σ0 into σ;
        rename l0 into l;
        rename H into Hlookup
      end.
      assert (Hlookup': heap σ !! l = Some (Some vl)).
      { destruct Hsubstate. eapply lookup_weaken; eassumption. }
      rewrite Hlookup' in Hlookup.
      injection Hlookup as ->.
      rewrite state_difference_difference_r //.
    - (* Store *)
      inversion Hbase_stepl; simplify_eq.
      rewrite heap_update_local //.
    - (* Xchg *)
      inversion Hbase_stepl; simplify_eq.
      match goal with H: (heap ?σ0 !! ?l0 = Some (Some v)) |- _ =>
        rename σ0 into σ;
        rename l0 into l;
        rename H into Hlookup
      end.
      assert (Hlookup': heap σ !! l = Some (Some vl)).
      { destruct Hsubstate. eapply lookup_weaken; eassumption. }
      rewrite Hlookup' in Hlookup.
      injection Hlookup as ->.
      rewrite heap_update_local //.
    - (* CmpXchg *)
      inversion Hbase_stepl; simplify_eq.
      match goal with
        Hl: (heap σl !! ?l0 = Some (Some _)),
        H: (heap ?σ0 !! ?l0 = Some (Some _))|- _ =>
        rename σ0 into σ;
        rename l0 into l;
        rename H into Hlookup;
        rename Hl into Hlookupl
      end.
      pose proof (lookup_weaken σl.(heap) σ.(heap) l _ Hlookupl (proj1 Hsubstate)) as Hlookup'.
      rewrite Hlookup' in Hlookup.
      injection Hlookup as ->.
      case_match.
      + rewrite heap_update_local //.
      + rewrite state_difference_difference_r //.
    - (* FAA *)
      inversion Hbase_stepl; simplify_eq.
      match goal with
        Hl: (heap σl !! ?l0 = Some (Some _)),
        H: (heap ?σ0 !! ?l0 = Some (Some _))|- _ =>
        rename σ0 into σ;
        rename l0 into l;
        rename H into Hlookup;
        rename Hl into Hlookupl
      end.
      pose proof (lookup_weaken σl.(heap) σ.(heap) l _ Hlookupl (proj1 Hsubstate)) as Hlookup'.
      rewrite Hlookup' in Hlookup.
      injection Hlookup as ->.
      rewrite heap_update_local //.
    - (* NewProph *)
      inversion Hbase_stepl; simplify_eq.
      rewrite used_proph_id_union_local //.
      constructor.
      destruct Hsubstate. set_solver.
    - (* Resolve *)
      inversion Hbase_stepl; simplify_eq.
      constructor; eauto.
  Qed.

  Lemma base_step_subset e σ κ e' σ' efs σl :
    σl ⊆ σ → base_reducible e σl → base_step e σ κ e' σ' efs →
    ∃ σ_ext σl', σl##σ_ext ∧ σl'##σ_ext ∧ σ = σl ∪ σ_ext ∧ σ' = σl' ∪ σ_ext ∧ base_step e σl κ e' σl' efs.
  Proof.
    intros Hsubstate Hred Hbase_step.
    exists (σ∖σl), (σ'∖(σ∖σl)).
    assert (σl ## σ ∖ σl) as Hdisj1.
    {  apply (state_disjoint_difference_r1). reflexivity. }
    assert (σ' ∖ (σ ∖ σl) ## σ ∖ σl) as Hdisj2.
    { apply (state_disjoint_difference_l1). reflexivity. }
    split; last split; last split; last split; try assumption.
    { by apply state_union_difference. }
    { rewrite state_union_comm //.
      apply state_union_difference.
      by eapply base_step_ext_subset. }

    simpl in *.
    destruct Hbase_step; try solve [
      rewrite state_difference_difference_r //; econstructor; eauto].
    - (* AllocN *)
      rewrite init_heap_local //.
      econstructor; eauto.
      destruct Hsubstate.
      by eapply fresh_heap_mono.
    - (* Free *)
      apply (base_reducible_free_loc) in Hred as [v' Hlookup].
      rewrite heap_update_local //.
      econstructor; eauto.
    - (* Load *)
      apply (base_reducible_load_loc) in Hred as [v' Hlookup].
      pose proof (lookup_weaken σl.(heap) _ _ (Some v') Hlookup (proj1 Hsubstate)) as Hlookup'.
      simplify_eq.
      rewrite state_difference_difference_r //.
      econstructor; eauto.
    - (* Store *)
      apply (base_reducible_store_loc) in Hred as [v' Hlookup].
      rewrite heap_update_local //.
      econstructor; eauto.
    - (* Xchg *)
      apply (base_reducible_xchg_loc) in Hred as [v' Hlookup].
      pose proof (lookup_weaken σl.(heap) _ _ (Some v') Hlookup (proj1 Hsubstate)) as Hlookup'.
      simplify_eq.
      rewrite heap_update_local //.
      econstructor; eauto.
    - (* CmpXchg *)
      apply (base_reducible_cmpxchg_loc) in Hred as [v' Hlookup].
      pose proof (lookup_weaken σl.(heap) _ _ (Some v') Hlookup (proj1 Hsubstate)) as Hlookup'.
      simplify_eq.
      match goal with Hdisj2: context [bool_decide (?vl = ?v1)] |- _ =>
        destruct (bool_decide (vl = v1)) eqn:Hbool_decide
      end.
      + rewrite heap_update_local //.
        econstructor; eauto.
      + rewrite state_difference_difference_r //.
        econstructor; eauto.
    - (* FAA *)
      apply (base_reducible_faa_loc) in Hred as [i1' Hlookup].
      pose proof (lookup_weaken σl.(heap) _ _ (Some (LitV (LitInt i1'))) Hlookup (proj1 Hsubstate)) as Hlookup'.
      simplify_eq.
      rewrite heap_update_local //.
      econstructor; eauto.
    - (* NewProph *)
      rewrite used_proph_id_union_local //.
      econstructor; eauto.
      destruct Hsubstate.
      set_solver.
    - (* Resolve *)
      eapply base_reducible_resolve_red in Hred as [Hin (κsl & vl & σl' & tsl & Hbase_step')];
        last eassumption.
      econstructor; eauto.
      by eapply atomic_base_step_subset.
  Qed.

  Lemma prim_step_subset e σ κ e' σ' efs σl :
    σl ⊆ σ → reducible e σl → prim_step e σ κ e' σ' efs →
    ∃ σ_ext σl', σl##σ_ext ∧ σl'##σ_ext ∧ σ = σl ∪ σ_ext ∧ σ' = σl' ∪ σ_ext ∧ prim_step e σl κ e' σl' efs.
  Proof.
    intros Hsubstate Hred Hprim_step.
    destruct Hprim_step as [K e_ e2_ -> -> Hbase_step]. simpl in *.
    apply reducible_fill_inv in Hred; last by eapply val_base_stuck.
    destruct (base_step_subset e_ σ κ e2_ σ' efs σl Hsubstate)
      as (σ_ext & σl' & Hdisj1 & Hdisj2 & Heq1 & Heq2 & Hbase_stepl);
      [|assumption|].
    { apply prim_base_reducible; first assumption.
      intros K' e' Heq Hnot_val. simpl in *.
      induction K' as [|k' K' _] using rev_ind; first done.
      rewrite fill_app /= in Heq.
      rewrite Heq in Hbase_step.
      apply base_ctx_step_val in Hbase_step.
      destruct Hbase_step as [? [-> ->]%to_val_fill_some].
      discriminate Hnot_val. }
    exists σ_ext, σl'.
    do 4 (split; first done).
    econstructor; eauto.
  Qed.

  Lemma base_step_heap_subdom e1 σ1 κs e2 σ2 efs :
    base_step e1 σ1 κs e2 σ2 efs → dom σ1.(heap) ⊆ dom σ2.(heap).
  Proof.
    intros Hstep. induction Hstep; try done.
    - rewrite /state_init_heap dom_union_L. set_solver.
    - rewrite /state_upd_heap dom_insert_L. set_solver.
    - rewrite /state_upd_heap dom_insert_L. set_solver.
    - rewrite /state_upd_heap dom_insert_L. set_solver.
    - case_match; first rewrite /state_upd_heap dom_insert_L; set_solver.
    - rewrite /state_upd_heap dom_insert_L. set_solver.
  Qed.

  Lemma prim_step_heap_subdom e1 σ1 κs e2 σ2 efs :
    prim_step e1 σ1 κs e2 σ2 efs → dom σ1.(heap) ⊆ dom σ2.(heap).
  Proof. intros []. by eapply base_step_heap_subdom. Qed.

  Lemma step_heap_subdom t1 σ1 κs t2 σ2 :
    step (t1,σ1) κs (t2,σ2) → dom σ1.(heap) ⊆ dom σ2.(heap).
  Proof. intros []. simplify_eq. by eapply prim_step_heap_subdom. Qed.

  Lemma erased_step_heap_subdom t1 σ1 t2 σ2 :
    erased_step (t1,σ1) (t2,σ2) → dom σ1.(heap) ⊆ dom σ2.(heap).
  Proof. intros []. by eapply step_heap_subdom. Qed.

  Lemma erased_nsteps_heap_subdom n t1 σ1 t2 σ2 :
    relations.nsteps erased_step n (t1,σ1) (t2,σ2) → dom σ1.(heap) ⊆ dom σ2.(heap).
  Proof.
    revert t1 σ1 t2 σ2.
    induction n as [|n IH] => t1 σ1 t2 σ2 Hsteps;
      inversion Hsteps; simplify_eq; first done.
    rename select (cfg _) into ρ. destruct ρ.
    etrans.
    - by eapply erased_step_heap_subdom.
    - by eapply IH.
  Qed.

  Lemma erased_steps_heap_subdom t1 σ1 t2 σ2 :
    rtc erased_step (t1,σ1) (t2,σ2) → dom σ1.(heap) ⊆ dom σ2.(heap).
  Proof.
    intros [n Hnsteps]%rtc_nsteps_1.
    by eapply erased_nsteps_heap_subdom.
  Qed.

  Lemma base_step_proph_subset e1 σ1 κs e2 σ2 efs :
    base_step e1 σ1 κs e2 σ2 efs → σ1.(used_proph_id) ⊆ σ2.(used_proph_id).
  Proof.
    intros Hstep. induction Hstep; try done.
    - case_match; first rewrite /state_upd_heap; set_solver.
    - rewrite /state_upd_used_proph_id. set_solver.
  Qed.

  Lemma prim_step_proph_subset e1 σ1 κs e2 σ2 efs :
    prim_step e1 σ1 κs e2 σ2 efs → σ1.(used_proph_id) ⊆ σ2.(used_proph_id).
  Proof. intros []. by eapply base_step_proph_subset. Qed.

  Lemma step_proph_subset t1 σ1 κs t2 σ2 :
    step (t1,σ1) κs (t2,σ2) → σ1.(used_proph_id) ⊆ σ2.(used_proph_id).
  Proof. intros []. simplify_eq. by eapply prim_step_proph_subset. Qed.

  Lemma erased_step_proph_subset t1 σ1 t2 σ2 :
    erased_step (t1,σ1) (t2,σ2) → σ1.(used_proph_id) ⊆ σ2.(used_proph_id).
  Proof. intros []. by eapply step_proph_subset. Qed.

  Lemma erased_nsteps_proph_subset n t1 σ1 t2 σ2 :
    relations.nsteps erased_step n (t1,σ1) (t2,σ2) → σ1.(used_proph_id) ⊆ σ2.(used_proph_id).
  Proof.
    revert t1 σ1 t2 σ2.
    induction n as [|n IH] => t1 σ1 t2 σ2 Hsteps;
      inversion Hsteps; simplify_eq; first done.
    rename select (cfg _) into ρ. destruct ρ.
    etrans.
    - by eapply erased_step_proph_subset.
    - by eapply IH.
  Qed.

  Lemma erased_steps_proph_subset t1 σ1 t2 σ2 :
    rtc erased_step (t1,σ1) (t2,σ2) → σ1.(used_proph_id) ⊆ σ2.(used_proph_id).
  Proof.
    intros [n Hnsteps]%rtc_nsteps_1.
    by eapply erased_nsteps_proph_subset.
  Qed.
End substate.
