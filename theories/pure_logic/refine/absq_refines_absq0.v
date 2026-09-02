(* absq_refines_absq0.v: the backward simulation relation [bs] from [AbsQ]
  to [AbsQ0], following the eight-condition relation defined in the proof
  of Lemma 1 of Bouajjani et al. [2017].

  Two of the paper's conditions are strengthened so that
  [bs[absq_init] = {absq0_init}] — as required by clause (i) of
  Definition 6 — holds directly from the definition:
  - conditions (5) and (7) are merged into a single iff [bs_A_iff] that
    exactly characterizes when [cp0(k) = A]. (As written, the paper's
    (5) is an iff over all [k] but its (7) gives [cp0(k) = A] under
    disjoint hypotheses; the natural reading is that (5) is implicitly
    conditioned on [k ∈ O], with (7) covering [k ∉ O], which is what
    [bs_A_iff] makes explicit.)
  - a new domain condition [bs_in0_dom] ties [dom(in0)] to [cp]'s
    enqueue control points; the paper's (4) only constrains [in0(k)]
    for *pending* enqueues, leaving completed-enqueue [in0] entries
    unspecified — without [bs_in0_dom] the paper's claim that "if we
    fix [D] and [σ_t] then [t] becomes unique" doesn't go through.

  The bs-step proofs additionally rely on:
  - data independence (no two enqueues share an input value); this
    isn't enforced by [absq_step] but is needed to recover the unique
    enqueue key for each value in [σ] in the LIN-DEQ and CALL-ENQ-A
    cases.
  - a well-formedness invariant of [AbsQ] / [AbsQ0] states (e.g.,
    [rv_s(k) = None] when [cp_s(k) = R1]); not entailed by [bs] alone,
    so for a fully-mechanized proof either the invariant must be
    threaded as a precondition or [bs] must be strengthened to include
    these domain constraints. *)

From iris_logatom.pure_logic.refine Require Import absq backward_simulation.
From iris_logatom.pure_logic.models Require bag_like.
Import bag_like (response_mayempty, MayEmpty, NeverEmpty).
From iris.heap_lang Require Import notation.
From stdpp Require Import gmap.

(** The happens-before order on values induced by an [AbsQ] labelling [ℓ]
  and order [<]. Written [≺] in the paper: [d1 ≺ d2] iff there exist
  operation identifiers [k1], [k2] such that [ℓ_1(k1) = d1],
  [ℓ_1(k2) = d2], and [k1 < k2]. *)
Definition absq_val_lt
  (ℓ : gmap positive (val * op_flag))
  (lt : gset (positive * positive))
  (d1 d2 : val) : Prop :=
  ∃ k1 k2 f1 f2,
    ℓ !! k1 = Some (d1, f1) ∧
    ℓ !! k2 = Some (d2, f2) ∧
    (k1, k2) ∈ lt.

(** The backward simulation relation from [AbsQ] to [AbsQ0]. The eight
  conditions of Lemma 1 are split below (condition (1) of the paper,
  which existentially quantifies a set [D] with
  [ℓ_1(COMP(O)) ⊆ D ⊆ ℓ_1(O)] such that [σ] is a linearization of
  [(D, ≺)], is broken into four constituents: [bs_nodup],
  [bs_completed_in], [bs_seq_from_O], and [bs_linearization]; the
  uniquely-determined [D] is [list_to_set σ]). Conditions (5) and (7)
  are merged into a single iff [bs_A_iff], and a new [bs_in0_dom] is
  added to pin down [dom(in0)]; see the top-of-file comment. *)
Record bs (s : absq_state) (t : absq0_state) : Prop := {
  (** (1a) The keys tagged on [σ] are distinct (every enqueue linearizes
    at most once). *)
  bs_nodup : NoDup (absq0_seq t).*1;
  (** (1b) [ℓ_1(COMP(O)) ⊆ σ]: every completed enqueue in [O] has its
    (key, value) pair in [σ]. *)
  bs_completed_in : ∀ k d,
    k ∈ absq_O s → absq_l s !! k = Some (d, COMP) →
    (k, d) ∈ absq0_seq t;
  (** (1c) Every pair in [σ] comes from some enqueue in [O] with that
    key and value. *)
  bs_seq_from_O : ∀ k d,
    (k, d) ∈ absq0_seq t →
    ∃ f, k ∈ absq_O s ∧ absq_l s !! k = Some (d, f);
  (** (1d) [σ] linearizes the happens-before order on keys: for every
    pair of positions [i < j] in [σ], the key at [j] is not
    happens-before the key at [i]. ([AbsQ0] enqueues append to [σ], so
    keys closer to the head are older — matching [bag_like.queue_model].) *)
  bs_linearization : ∀ i j k_i d_i k_j d_j,
    i < j →
    absq0_seq t !! i = Some (k_i, d_i) →
    absq0_seq t !! j = Some (k_j, d_j) →
    (k_j, k_i) ∉ absq_lt s;

  (** (2) Return values fixed at dequeue linearization points agree. *)
  bs_rv_agree : ∀ k,
    absq_rv s !! k = absq0_rv t !! k;

  (** (3) Every dequeue is at the same control point in [s] and [t]. *)
  bs_R1_iff : ∀ k,
    absq_cp s !! k = Some R1 ↔ absq0_cp t !! k = Some R1;
  bs_R2_iff : ∀ k,
    absq_cp s !! k = Some R2 ↔ absq0_cp t !! k = Some R2;
  bs_R3_iff : ∀ k,
    absq_cp s !! k = Some R3 ↔ absq0_cp t !! k = Some R3;

  (** (4) Every enqueue in [O] has the same input value as recorded by
    [AbsQ0]'s [in0]. *)
  bs_enq_input : ∀ k d f,
    absq_l s !! k = Some (d, f) → absq0_in t !! k = Some d;

  (** (extra) The domain of [in0] is exactly the set of keys which have
    an enqueue control point in [s]. (Not in the paper, but needed to
    make [bs[init1] ⊆ {init2}] hold — see the top-of-file comment.) *)
  bs_in0_dom : ∀ k,
    is_Some (absq0_in t !! k) ↔
    (absq_cp s !! k = Some A1 ∨ absq_cp s !! k = Some A2);

  (** (6) [cp0(k) = A1] iff [k] is a pending enqueue in [O] whose value
    is not yet in [σ]. The paper's formal statement of condition (6) drops
    the "from O" clause from its English prose; we reinstate it here, since
    without the [k ∈ O] conjunct [bs] becomes inconsistent at states where
    a pending-then-dequeued enqueue has [k ∉ O ∧ cp(k) = A1] — (7) would
    force [cp0(k) = A], while the unrestricted (6) would force
    [cp0(k) = A1]. *)
  bs_A1_iff : ∀ k,
    absq0_cp t !! k = Some A1 ↔
    (k ∈ absq_O s ∧ ∃ d, absq_l s !! k = Some (d, PEND) ∧ (k, d) ∉ absq0_seq t);

  (** (5+7) [cp0(k) = A] iff either [k] is a pending enqueue in [O] whose
    value is in [σ], or [k] has already been dequeued while still pending
    in [AbsQ]. (Strengthens the paper's one-way (5) and (7) into an iff;
    the uniqueness of [t] claimed by the paper depends on this.) *)
  bs_A_iff : ∀ k,
    absq0_cp t !! k = Some A ↔
    ((∃ d, absq_l s !! k = Some (d, PEND) ∧ (k, d) ∈ absq0_seq t)
     ∨ (k ∉ absq_O s ∧ absq_cp s !! k = Some A1));

  (** (8) Completed enqueues agree. *)
  bs_A2_iff : ∀ k,
    absq_cp s !! k = Some A2 ↔ absq0_cp t !! k = Some A2;
}.

(** Recover the forward directions of conditions (5) and (7) from
  [bs_A_iff], for convenience when reasoning about steps. *)
Lemma bs_linearized s t k d :
  bs s t →
  absq_l s !! k = Some (d, PEND) → (k, d) ∈ absq0_seq t →
  absq0_cp t !! k = Some A.
Proof.
  intros Hbs Hℓ Hd. apply (bs_A_iff _ _ Hbs). left. by exists d.
Qed.

Lemma bs_pending_not_in_O s t k :
  bs s t →
  k ∉ absq_O s → absq_cp s !! k = Some A1 →
  absq0_cp t !! k = Some A.
Proof.
  intros Hbs HO Hcp. apply (bs_A_iff _ _ Hbs). by right.
Qed.

(** Clause (i) of Definition 6 of the paper: [bs[init1] = {init2}].
  Forward direction. *)
Lemma bs_init : bs absq_init absq0_init.
Proof.
  split; rewrite /absq_init /absq0_init /=.
  - constructor.
  - intros k d _. rewrite lookup_empty. intros [=].
  - intros k d Hd. apply elem_of_nil in Hd. done.
  - intros i j ????? _. rewrite lookup_nil. intros [=].
  - intros k. by rewrite !lookup_empty.
  - intros k. rewrite lookup_empty. split; intros [=].
  - intros k. rewrite lookup_empty. split; intros [=].
  - intros k. rewrite lookup_empty. split; intros [=].
  - intros k d f. rewrite lookup_empty. intros [=].
  - intros k. rewrite lookup_empty. split.
    + intros [? [=]].
    + intros [[=] | [=]].
  - intros k. rewrite lookup_empty. split.
    + intros [=].
    + intros (Hfalse & _). set_solver.
  - intros k. rewrite lookup_empty. split.
    + intros [=].
    + intros [(? & Hfalse & _) | (_ & [=])]. discriminate Hfalse.
  - intros k. rewrite !lookup_empty. split; intros [=].
Qed.

(** Clause (i) of Definition 6: uniqueness. *)
Lemma bs_init_only t : bs absq_init t → t = absq0_init.
Proof.
  intros Hbs. destruct t as [σ in0 rv0 cp0].
  rewrite /absq0_init. f_equal.
  - (* σ = [] *)
    destruct σ as [|[k_e d] σ']; first done.
    destruct (bs_seq_from_O _ _ Hbs k_e d) as (f & Hk & _).
    { by left. }
    rewrite /absq_init /= in Hk. set_solver.
  - (* in0 = ∅ *)
    apply map_eq; intros k. rewrite lookup_empty.
    destruct (in0 !! k) as [d|] eqn:Hin0; last done.
    exfalso.
    pose proof (mk_is_Some _ _ Hin0) as Hsome.
    apply (bs_in0_dom _ _ Hbs k) in Hsome as [HA | HA];
      rewrite /absq_init /= lookup_empty in HA; discriminate.
  - (* rv0 = ∅ *)
    apply map_eq; intros k. rewrite lookup_empty.
    rewrite -(bs_rv_agree _ _ Hbs k). rewrite /absq_init /= lookup_empty //.
  - (* cp0 = ∅ *)
    apply map_eq; intros k. rewrite lookup_empty.
    destruct (cp0 !! k) as [cp_val|] eqn:Hcp0; last done.
    exfalso. destruct cp_val.
    + (* A1 *) apply (bs_A1_iff _ _ Hbs k) in Hcp0 as (_ & ? & Hfalse & _).
      rewrite /absq_init /= lookup_empty in Hfalse. discriminate.
    + (* A *) apply (bs_A_iff _ _ Hbs k) in Hcp0 as [(? & Hfalse & _) | (_ & Hfalse)].
      * rewrite /absq_init /= lookup_empty in Hfalse. discriminate.
      * rewrite /absq_init /= lookup_empty in Hfalse. discriminate.
    + (* A2 *) apply (bs_A2_iff _ _ Hbs k) in Hcp0.
      rewrite /absq_init /= lookup_empty in Hcp0. discriminate.
    + (* R1 *) apply (bs_R1_iff _ _ Hbs k) in Hcp0.
      rewrite /absq_init /= lookup_empty in Hcp0. discriminate.
    + (* R2 *) apply (bs_R2_iff _ _ Hbs k) in Hcp0.
      rewrite /absq_init /= lookup_empty in Hcp0. discriminate.
    + (* R3 *) apply (bs_R3_iff _ _ Hbs k) in Hcp0.
      rewrite /absq_init /= lookup_empty in Hcp0. discriminate.
Qed.

(* ============================================== *)
(* Γ = C ∪ R ∪ Lin(deq): every [absq_action] except [ALinEnq]. *)

Definition is_observable (x : positive * absq_action) : Prop :=
  match x.2 with
  | ALinEnq _ => False
  | _ => True
  end.

Global Instance is_observable_dec x : Decision (is_observable x).
Proof. rewrite /is_observable. destruct x.2; apply _. Defined.

(* ============================================== *)
(* Clause (ii) of Definition 6: the backward step condition. *)

(** The well-formedness invariant of [absq_state] used as the forward
  invariant passed to [backward_simulation_with_inv]. Bundles facts
  that are preserved by every [absq_step] but not directly enforced
  by the constructors; see the individual field comments below. *)
Record absq_wf (valid_value : val → Prop) (s : absq_state) : Prop := AbsqWf {
  absq_wf_dom : dom (absq_l s) ⊆ dom (absq_cp s);
  (** Every [ℓ]-entry is an enqueue operation (cp ∈ {A1, A2}); needed
    in LIN-DEQ1/2 to derive a contradiction when dequeuing a [PEND]
    enqueue — the bs conditions force [cp0'(k') = A1] and
    simultaneously [cp0'(k') = A], which are incompatible. *)
  absq_wf_ℓcp : ∀ k d f,
    absq_l s !! k = Some (d, f) →
    absq_cp s !! k = Some A1 ∨ absq_cp s !! k = Some A2;
  (** A completed enqueue (flag [COMP]) has [cp = A2]: the only way to
    reach flag [COMP] is via [RET-ENQ1], which simultaneously moves
    [cp] from [A1] to [A2]. Needed for [bs_A_iff] in LIN-DEQ1/2 at
    [k0 = k']: prevents the unreachable-but-not-syntactically-ruled-out
    state [cp(k') = A1] ∧ [ℓ(k') = (_, COMP)]. *)
  absq_wf_COMP : ∀ k d,
    absq_l s !! k = Some (d, COMP) → absq_cp s !! k = Some A2;
  absq_wf_rv : ∀ k,
    is_Some (absq_rv s !! k) →
    absq_cp s !! k = Some R2 ∨ absq_cp s !! k = Some R3;
  (** A pending enqueue still in [O] has [cp = A1]: [RET-ENQ1] flips the
    flag to [COMP] and [cp] to [A2] simultaneously, and [RET-ENQ2] (which
    sets [cp = A2] without touching [ℓ]) requires [k ∉ O]. Needed by
    LIN-DEQ1 at [k' ∈ O] with [ℓ(k') = (d, PEND)] to conclude
    [cp(k') = A1]. *)
  absq_wf_PEND_O : ∀ k d,
    k ∈ absq_O s → absq_l s !! k = Some (d, PEND) →
    absq_cp s !! k = Some A1;
  (** Every [lt]-edge has a [COMP] source: [CALL-ENQ] only adds edges
    from [COMP(O)] keys, and [COMP] is monotone. Needed by forward
    [RET-ENQ1] (Case B) to rule out outgoing edges from a pending key. *)
  absq_wf_lt_COMP : ∀ k1 k2,
    (k1, k2) ∈ absq_lt s →
    ∃ d, absq_l s !! k1 = Some (d, COMP);
  (** Every [ℓ]-entry carries a [valid_value] queue value.  The only way a
    value enters [ℓ] is via [CALL-ENQ], which requires its input to
    be [valid_value]; [RET-ENQ1] preserves the value.  Needed by
    [bs_step]'s CALL-ENQ Case B and LIN-DEQ2 to discharge the
    [valid_value d] precondition of [absq0_step_lin_enq]. *)
  absq_wf_valid_value : ∀ k d f,
    absq_l s !! k = Some (d, f) → valid_value d;
}.

Lemma absq_wf_init valid_value : absq_wf valid_value absq_init.
Proof.
  rewrite /absq_init. split; simpl.
  - set_solver.
  - intros k d f Hℓ. rewrite lookup_empty in Hℓ. discriminate.
  - intros k d Hℓ. rewrite lookup_empty in Hℓ. discriminate.
  - intros k [? Hrv]. rewrite lookup_empty in Hrv. discriminate.
  - intros k d Hk. set_solver.
  - intros k1 k2. set_solver.
  - intros k d f Hℓ. rewrite lookup_empty in Hℓ. discriminate.
Qed.

Lemma absq_wf_step rme valid_value s l s' :
  absq_wf valid_value s → absq_step rme valid_value s l s' → absq_wf valid_value s'.
Proof.
  intros [Hdom Hℓcp Hcomp Hrv Hpendo Hlt_comp Hvalid_value] Hstep.
  inversion Hstep as
    [ O lt ℓ rv cp k d Hfresh Hd_ub
    | O lt ℓ rv cp k Hfresh
    | O lt ℓ rv cp k d Hcp HkO Hℓeq
    | O lt ℓ rv cp k Hcp HkNotO
    | O lt ℓ rv cp k d Hcp Hrveq
    | O lt ℓ rv cp k k' d f Hcp Hmin Hℓeq
    | O lt ℓ rv cp k Hrme_eq Hcp HallPend ];
    subst; simpl in Hdom, Hℓcp, Hcomp, Hrv, Hpendo, Hlt_comp; split; simpl.
  (* ----- CALL-ENQ ----- *)
  - rewrite !dom_insert_L. set_solver.
  - intros k0 d0 f0 Hℓ'.
    destruct (decide (k = k0)) as [<-|Hne].
    { rewrite lookup_insert_eq. by left. }
    rewrite (lookup_insert_ne _ _ _ _ Hne).
    rewrite (lookup_insert_ne _ _ _ _ Hne) in Hℓ'. by eapply Hℓcp.
  - intros k0 d0 Hℓ'.
    destruct (decide (k = k0)) as [<-|Hne].
    { rewrite lookup_insert_eq in Hℓ'. inversion Hℓ'. }
    rewrite (lookup_insert_ne _ _ _ _ Hne).
    rewrite (lookup_insert_ne _ _ _ _ Hne) in Hℓ'. by eapply Hcomp.
  - intros k0 Hrv_some.
    destruct (decide (k = k0)) as [<-|Hne].
    { apply Hrv in Hrv_some as [Hcp|Hcp];
        apply not_elem_of_dom in Hfresh; rewrite Hfresh in Hcp; discriminate. }
    rewrite (lookup_insert_ne _ _ _ _ Hne). by apply Hrv.
  - intros k0 d0 Hk0_O Hℓ'.
    destruct (decide (k = k0)) as [<-|Hne].
    { by rewrite lookup_insert_eq. }
    rewrite (lookup_insert_ne _ _ _ _ Hne).
    rewrite (lookup_insert_ne _ _ _ _ Hne) in Hℓ'.
    apply (Hpendo k0 d0); last done. set_solver.
  - intros k1 k2 Hedge.
    assert (ℓ !! k = None) as Hℓk.
    { apply not_elem_of_dom. intros Hk_dom. by apply Hdom in Hk_dom. }
    apply elem_of_union in Hedge as [Hold | Hnew].
    + destruct (Hlt_comp _ _ Hold) as (d' & Hℓk1).
      assert (k1 ≠ k) as Hne by (intros ->; congruence).
      exists d'. rewrite (lookup_insert_ne _ k k1 _ (λ H, Hne (eq_sym H))) //.
    + apply elem_of_map in Hnew as (k' & Heq & Hk'_comp).
      inversion Heq; subst k1 k2.
      apply elem_of_filter in Hk'_comp as [[d' Hℓk'] _].
      assert (k' ≠ k) as Hne by (intros ->; congruence).
      exists d'. rewrite (lookup_insert_ne _ k k' _ (λ H, Hne (eq_sym H))) //.
  - (* valid_value (CALL-ENQ): the new k↦(d,PEND) gets [valid_value d]
       from the step's premise. *)
    intros k0 d0 f0 Hℓ'.
    destruct (decide (k = k0)) as [<-|Hk_ne].
    { rewrite lookup_insert_eq in Hℓ'. by inversion Hℓ'; subst. }
    rewrite (lookup_insert_ne _ _ _ _ Hk_ne) in Hℓ'. by eapply Hvalid_value.
  (* ----- CALL-DEQ ----- *)
  - rewrite dom_insert_L. set_solver.
  - intros k0 d0 f0 Hℓ.
    destruct (decide (k = k0)) as [<-|Hne].
    { apply Hℓcp in Hℓ as [Hcp|Hcp];
        apply not_elem_of_dom in Hfresh; rewrite Hfresh in Hcp; discriminate. }
    rewrite (lookup_insert_ne _ _ _ _ Hne). by eapply Hℓcp.
  - intros k0 d0 Hℓ.
    destruct (decide (k = k0)) as [<-|Hne].
    { apply Hcomp in Hℓ. apply not_elem_of_dom in Hfresh.
      rewrite Hfresh in Hℓ. discriminate. }
    rewrite (lookup_insert_ne _ _ _ _ Hne). by eapply Hcomp.
  - intros k0 Hrv_some.
    destruct (decide (k = k0)) as [<-|Hne].
    { apply Hrv in Hrv_some as [Hcp|Hcp];
        apply not_elem_of_dom in Hfresh; rewrite Hfresh in Hcp; discriminate. }
    rewrite (lookup_insert_ne _ _ _ _ Hne). by apply Hrv.
  - intros k0 d0 Hk0_O Hℓ'.
    destruct (decide (k = k0)) as [<-|Hne].
    { exfalso. apply Hfresh. apply Hdom.
      apply elem_of_dom. by eexists. }
    rewrite (lookup_insert_ne _ _ _ _ Hne).
    by apply (Hpendo k0 d0).
  - apply Hlt_comp.
  - (* valid_value (CALL-DEQ): ℓ unchanged. *) apply Hvalid_value.
  (* ----- RET-ENQ1 ----- *)
  - rewrite !dom_insert_L.
    assert (k ∈ dom cp) by (apply elem_of_dom; by eexists).
    set_solver.
  - intros k0 d0 f0 Hℓ'.
    destruct (decide (k = k0)) as [<-|Hne].
    { rewrite lookup_insert_eq. by right. }
    rewrite (lookup_insert_ne _ _ _ _ Hne).
    rewrite (lookup_insert_ne _ _ _ _ Hne) in Hℓ'. by eapply Hℓcp.
  - intros k0 d0 Hℓ'.
    destruct (decide (k = k0)) as [<-|Hne].
    { by rewrite lookup_insert_eq. }
    rewrite (lookup_insert_ne _ _ _ _ Hne).
    rewrite (lookup_insert_ne _ _ _ _ Hne) in Hℓ'. by eapply Hcomp.
  - intros k0 Hrv_some.
    destruct (decide (k = k0)) as [<-|Hne].
    { apply Hrv in Hrv_some as [Hcp'|Hcp']; rewrite Hcp in Hcp'; discriminate. }
    rewrite (lookup_insert_ne _ _ _ _ Hne). by apply Hrv.
  - intros k0 d0 Hk0_O Hℓ'.
    destruct (decide (k = k0)) as [<-|Hne].
    { rewrite lookup_insert_eq in Hℓ'. inversion Hℓ'. }
    rewrite (lookup_insert_ne _ _ _ _ Hne).
    rewrite (lookup_insert_ne _ _ _ _ Hne) in Hℓ'.
    by apply (Hpendo k0 d0).
  - intros k1 k2 Hedge.
    destruct (Hlt_comp _ _ Hedge) as (d' & Hℓk1).
    destruct (decide (k = k1)) as [<-|Hne].
    { exists d. by rewrite lookup_insert_eq. }
    exists d'. by rewrite (lookup_insert_ne _ _ _ _ Hne).
  - (* valid_value (RET-ENQ1): new k↦(d,COMP); d was in ℓ as (d,PEND). *)
    intros k0 d0 f0 Hℓ'.
    destruct (decide (k = k0)) as [<-|Hk_ne].
    { rewrite lookup_insert_eq in Hℓ'. inversion Hℓ'; subst d0.
      by eapply (Hvalid_value _ _ PEND). }
    rewrite (lookup_insert_ne _ _ _ _ Hk_ne) in Hℓ'. by eapply Hvalid_value.
  (* ----- RET-ENQ2 ----- *)
  - rewrite dom_insert_L. set_solver.
  - intros k0 d0 f0 Hℓ.
    destruct (decide (k = k0)) as [<-|Hne].
    { rewrite lookup_insert_eq. by right. }
    rewrite (lookup_insert_ne _ _ _ _ Hne). by eapply Hℓcp.
  - intros k0 d0 Hℓ.
    destruct (decide (k = k0)) as [<-|Hne].
    { apply Hcomp in Hℓ. rewrite Hcp in Hℓ. discriminate. }
    rewrite (lookup_insert_ne _ _ _ _ Hne). by eapply Hcomp.
  - intros k0 Hrv_some.
    destruct (decide (k = k0)) as [<-|Hne].
    { apply Hrv in Hrv_some as [Hcp'|Hcp']; rewrite Hcp in Hcp'; discriminate. }
    rewrite (lookup_insert_ne _ _ _ _ Hne). by apply Hrv.
  - intros k0 d0 Hk0_O Hℓ'.
    destruct (decide (k = k0)) as [<-|Hne].
    { done. }
    rewrite (lookup_insert_ne _ _ _ _ Hne).
    by apply (Hpendo k0 d0).
  - apply Hlt_comp.
  - (* valid_value (RET-ENQ2): ℓ unchanged. *) apply Hvalid_value.
  (* ----- RET-DEQ ----- *)
  - rewrite dom_insert_L. set_solver.
  - intros k0 d0 f0 Hℓ.
    destruct (decide (k = k0)) as [<-|Hne].
    { apply Hℓcp in Hℓ as [Hcp'|Hcp']; rewrite Hcp in Hcp'; discriminate. }
    rewrite (lookup_insert_ne _ _ _ _ Hne). by eapply Hℓcp.
  - intros k0 d0 Hℓ.
    destruct (decide (k = k0)) as [<-|Hne].
    { apply Hcomp in Hℓ. rewrite Hcp in Hℓ. discriminate. }
    rewrite (lookup_insert_ne _ _ _ _ Hne). by eapply Hcomp.
  - intros k0 Hrv_some.
    destruct (decide (k = k0)) as [<-|Hne].
    { rewrite lookup_insert_eq. by right. }
    rewrite (lookup_insert_ne _ _ _ _ Hne). by apply Hrv.
  - intros k0 d0 Hk0_O Hℓ'.
    destruct (decide (k = k0)) as [<-|Hne].
    { specialize (Hpendo k d0 Hk0_O Hℓ'). rewrite Hcp in Hpendo. discriminate. }
    rewrite (lookup_insert_ne _ _ _ _ Hne). by apply (Hpendo k0 d0).
  - apply Hlt_comp.
  - (* valid_value (RET-DEQ): ℓ unchanged. *) apply Hvalid_value.
  (* ----- LIN-DEQ1 ----- *)
  - rewrite dom_insert_L. set_solver.
  - intros k0 d0 f0 Hℓ.
    destruct (decide (k = k0)) as [<-|Hne].
    { apply Hℓcp in Hℓ as [Hcp'|Hcp']; rewrite Hcp in Hcp'; discriminate. }
    rewrite (lookup_insert_ne _ _ _ _ Hne). by eapply Hℓcp.
  - intros k0 d0 Hℓ.
    destruct (decide (k = k0)) as [<-|Hne].
    { apply Hcomp in Hℓ. rewrite Hcp in Hℓ. discriminate. }
    rewrite (lookup_insert_ne _ _ _ _ Hne). by eapply Hcomp.
  - intros k0 Hrv_some.
    destruct (decide (k = k0)) as [<-|Hne].
    { rewrite lookup_insert_eq. by left. }
    rewrite (lookup_insert_ne _ _ _ _ Hne).
    rewrite (lookup_insert_ne _ _ _ _ Hne) in Hrv_some. by apply Hrv.
  - intros k0 d0 Hk0_O Hℓ'.
    destruct (decide (k = k0)) as [<-|Hne].
    { assert (k ∈ O) as Hk_O by set_solver.
      specialize (Hpendo k d0 Hk_O Hℓ'). rewrite Hcp in Hpendo. discriminate. }
    rewrite (lookup_insert_ne _ _ _ _ Hne). apply (Hpendo k0 d0); last done.
    set_solver.
  - intros k1 k2 Hedge.
    apply elem_of_filter in Hedge as [_ Hold].
    by apply (Hlt_comp _ _ Hold).
  - (* valid_value (LIN-DEQ1): ℓ unchanged. *) apply Hvalid_value.
  (* ----- LIN-DEQ2 ----- *)
  - rewrite dom_insert_L. set_solver.
  - intros k0 d0 f0 Hℓ.
    destruct (decide (k = k0)) as [<-|Hne].
    { apply Hℓcp in Hℓ as [Hcp'|Hcp']; rewrite Hcp in Hcp'; discriminate. }
    rewrite (lookup_insert_ne _ _ _ _ Hne). by eapply Hℓcp.
  - intros k0 d0 Hℓ.
    destruct (decide (k = k0)) as [<-|Hne].
    { apply Hcomp in Hℓ. rewrite Hcp in Hℓ. discriminate. }
    rewrite (lookup_insert_ne _ _ _ _ Hne). by eapply Hcomp.
  - intros k0 Hrv_some.
    destruct (decide (k = k0)) as [<-|Hne].
    { rewrite lookup_insert_eq. by left. }
    rewrite (lookup_insert_ne _ _ _ _ Hne).
    rewrite (lookup_insert_ne _ _ _ _ Hne) in Hrv_some. by apply Hrv.
  - intros k0 d0 Hk0_O Hℓ'.
    destruct (decide (k = k0)) as [<-|Hne].
    { specialize (Hpendo k d0 Hk0_O Hℓ'). rewrite Hcp in Hpendo. discriminate. }
    rewrite (lookup_insert_ne _ _ _ _ Hne). by apply (Hpendo k0 d0).
  - apply Hlt_comp.
  - (* valid_value (LIN-DEQ2): ℓ unchanged. *) apply Hvalid_value.
Qed.

(** Filtering a [NoDup] list preserves the positions of the remaining
  elements: any [i < j] in the filtered list corresponds to some
  [i' < j'] in the original. Used by [bs_fwd_step]'s LIN-DEQ1 case
  to transfer the linearization of [σ_u] through the removal of [d]. *)
Lemma filter_lookup_mono {A} `{EqDecision A} (P : A → Prop) `{!∀ x, Decision (P x)}
  (l : list A) (i j : nat) (x y : A) :
  NoDup l →
  i < j →
  filter P l !! i = Some x →
  filter P l !! j = Some y →
  ∃ i' j', i' < j' ∧ l !! i' = Some x ∧ l !! j' = Some y.
Proof.
  revert i j. induction l as [|a l IH]; intros i j Hnd Hij Hi Hj; first done.
  rewrite filter_cons in Hi, Hj.
  apply NoDup_cons in Hnd as [Ha_nin Hnd].
  destruct (decide (P a)) as [HPa|HPa].
  - destruct i as [|i']; destruct j as [|j']; first lia.
    + simpl in Hi. inversion Hi; subst x.
      simpl in Hj.
      pose proof (list_elem_of_lookup_2 _ _ _ Hj) as Hy_in.
      apply list_elem_of_filter in Hy_in as [_ Hy_l].
      apply list_elem_of_lookup_1 in Hy_l as (j'' & Hj_l).
      exists 0, (S j''). split_and!; [lia|done|done].
    + lia.
    + simpl in Hi, Hj.
      assert (i' < j') by lia.
      destruct (IH i' j' Hnd ltac:(lia) Hi Hj) as (i'' & j'' & ? & ? & ?).
      exists (S i''), (S j''). split_and!; [lia|done|done].
  - destruct (IH i j Hnd Hij Hi Hj) as (i'' & j'' & ? & ? & ?).
    exists (S i''), (S j''). split_and!; [lia|done|done].
Qed.

(** [cp0] with each key in [ks] mapped to [c]; built right-to-left so
  later inserts in [ks] override earlier ones (irrelevant when [ks]
  is no-duplicates). *)
Definition insert_all (c : control_point) (cp0 : gmap positive control_point)
  (ks : list positive) : gmap positive control_point :=
  foldr (λ k acc, <[k := c]> acc) cp0 ks.

Lemma insert_all_cons c cp0 k ks :
  insert_all c cp0 (k :: ks) = <[k := c]> (insert_all c cp0 ks).
Proof. done. Qed.

Lemma insert_all_commute c cp0 k ks :
  k ∉ ks →
  insert_all c (<[k := c]> cp0) ks = <[k := c]>(insert_all c cp0 ks).
Proof.
  intros Hk_notin. unfold insert_all.
  induction ks as [|k' ks' IH]; first done.
  simpl. apply not_elem_of_cons in Hk_notin as [Hne Hk_notin].
  rewrite IH //. by apply insert_insert_ne.
Qed.

Lemma insert_all_lookup_in c cp0 ks k :
  k ∈ ks → insert_all c cp0 ks !! k = Some c.
Proof.
  unfold insert_all.
  induction ks as [|k' ks' IH]; first by intros []%not_elem_of_nil.
  intros Hk. apply elem_of_cons in Hk as [->|Hk].
  - by rewrite /= lookup_insert_eq.
  - simpl. destruct (decide (k' = k)) as [->|Hne].
    + by rewrite lookup_insert_eq.
    + rewrite (lookup_insert_ne _ _ _ _ Hne). by apply IH.
Qed.

Lemma insert_all_lookup_notin c cp0 ks k :
  k ∉ ks → insert_all c cp0 ks !! k = cp0 !! k.
Proof.
  unfold insert_all.
  induction ks as [|k' ks' IH]; first done.
  intros Hk. apply not_elem_of_cons in Hk as [Hne Hk].
  simpl. rewrite (lookup_insert_ne _ _ _ _ (λ Heq, Hne (eq_sym Heq))).
  by apply IH.
Qed.

Global Opaque insert_all.

Section bs_step.
  Context (rme : response_mayempty) (valid_value : val → Prop).

  (** Iterating LIN-ENQ steps. Given a list [kvs] of (key, value) pairs
    with distinct keys and a per-element precondition
    [cp0(k) = Some A1 ∧ in0(k) = Some v ∧ valid_value v], the sequence
    of [(k_i, ALinEnq v_i)] AbsQ0 actions can be applied, yielding a
    state with [σ] extended by appending [kvs] (each LIN-ENQ appends,
    matching [bag_like.queue_model]'s head=oldest convention) and
    [cp0] updated by mapping each key in [kvs] to [A]. Used by
    CALL-ENQ Case B and LIN-DEQ2 to lift the AbsQ [σ] structure back
    through AbsQ0 LIN-ENQ steps. *)
  Lemma absq0_lin_enq_seq_steps σ in0 rv0 cp0 (kvs : list (positive * val)) :
    NoDup kvs.*1 →
    Forall (λ kv, cp0 !! kv.1 = Some A1
                  ∧ in0 !! kv.1 = Some kv.2
                  ∧ valid_value kv.2) kvs →
    absq0_steps rme valid_value
      (AbsQ0State σ in0 rv0 cp0)
      (map (λ kv, (kv.1, ALinEnq kv.2)) kvs)
      (AbsQ0State (σ ++ kvs) in0 rv0 (insert_all A cp0 kvs.*1)).
  Proof.
    revert σ cp0.
    induction kvs as [|[k0 v0] kvs IH]; intros σ cp0 Hnd Hpre.
    - rewrite app_nil_r. apply lts_steps_nil.
    - simpl. simpl in Hnd. apply NoDup_cons in Hnd as [Hk0_notin Hnd_ks].
      inversion Hpre as [|? ? Hhead Htail]; subst.
      destruct Hhead as (Hcp_k0 & Hin_k0 & Hv0_ub).
      simpl in Hcp_k0, Hin_k0, Hv0_ub.
      eapply lts_steps_cons.
      { by apply absq0_step_lin_enq. }
      replace (σ ++ (k0, v0) :: kvs) with ((σ ++ [(k0, v0)]) ++ kvs); last first.
      { by rewrite -app_assoc. }
      rewrite insert_all_cons -insert_all_commute //.
      apply IH; [done|].
      (* Push cp0 → <[k0:=A]>cp0 through Htail: since [k0 ∉ kvs.*1],
         every kv ∈ kvs has kv.1 ≠ k0, so the lookup is unchanged. *)
      apply Forall_forall. intros [k v] Hkv_in.
      rewrite Forall_forall in Htail.
      specialize (Htail _ Hkv_in) as (Hcp_k & Hin_k & Hv_ub).
      simpl in Hcp_k, Hin_k, Hv_ub.
      assert (k0 ≠ k) as Hne.
      { intros ->. apply Hk0_notin.
        apply list_elem_of_fmap. by exists (k, v). }
      simpl. split_and!; [|done|done].
      by rewrite (lookup_insert_ne cp0 k0 k A Hne).
  Qed.

  (** The backward step condition of Definition 6, instantiated to
    [AbsQ] → [AbsQ0]. *)
  Lemma bs_step s l s' u' :
    absq_wf valid_value s →
    absq_step rme valid_value s l s' → bs s' u' →
    ∃ u ls, bs s u ∧ absq0_steps rme valid_value u ls u' ∧
            project_labels is_observable [l] = project_labels is_observable ls.
  Proof.
    intros Hwf Hstep Hbs'.
    inversion Hstep as
      [ O lt ℓ rv cp k d Hfresh Hd_ub
      | O lt ℓ rv cp k Hfresh
      | O lt ℓ rv cp k d Hcp Hin Hℓ
      | O lt ℓ rv cp k Hcp HnotIn
      | O lt ℓ rv cp k d Hcp Hrv
      | O lt ℓ rv cp k k' d f Hcp Hmin Hℓ
      | O lt ℓ rv cp k Hrme_eq Hcp HallPend ];
      subst.
    (* CALL-ENQ. The paper splits on whether [k ∈ D_{u'}], i.e., whether
        [d ∈ σ'] (equivalent here to [cp0'(k) = A] vs [cp0'(k) = A1]):
        - if [d ∉ σ'] / [cp0'(k) = A1]: take [u] equal to [u'] minus
          [k]'s entries in [in0] and [cp0]; one AbsQ0 [CALL-ENQ] step.
        - if [d ∈ σ'] / [cp0'(k) = A]: write [σ' = pre ++ [d] ++ post]
          (head=oldest, matching [bag_like.queue_model]); take
          [σ_u = pre] (the older prefix that already existed before
          [k]'s call). The matching AbsQ0 trace is
          [CALL-ENQ(k, d) :: LIN-ENQ(k, d) :: LIN-ENQ(k_1, post_1) ::
            … :: LIN-ENQ(k_j, post_j)] where [post = [post_1, …, post_j]]
          and each [k_i] is the (unique by data independence) pending
          enqueue with [ℓ(k_i) = post_i]. *)
    - destruct u' as [σ' in0' rv0' cp0'].
      (* From Hwf and Hfresh: k ∉ dom ℓ, so ℓ !! k = None. *)
      assert (ℓ !! k = None) as Hℓk_none.
      { apply not_elem_of_dom. intros Hk.
        apply Hfresh. apply (absq_wf_dom _ _ Hwf), Hk. }
      (* From bs_enq_input on s' at k: in0' !! k = Some d. *)
      assert (in0' !! k = Some d) as Hin0'k.
      { apply (bs_enq_input _ _ Hbs' k d PEND).
        simpl. by rewrite lookup_insert_eq. }
      destruct (decide ((k, d) ∈ σ')) as [Hd_in|Hd_notin]; last first.
      + (* Case A: (k, d) ∉ σ'. Then cp0'(k) = A1, and one AbsQ0 CALL-ENQ
          step from u (= u' minus [k] in in0' and cp0') yields u'. *)
        assert (cp0' !! k = Some A1) as Hcp0'k.
        { apply (bs_A1_iff _ _ Hbs' k). split.
          { simpl. set_solver. }
          exists d. split; last done.
          simpl. by rewrite lookup_insert_eq. }
        exists (AbsQ0State σ' (delete k in0') rv0' (delete k cp0')),
               [(k, ACallEnq d)].
        split_and!; last first.
        * done.
        * eapply lts_steps_cons; last apply lts_steps_nil.
          replace cp0' with (<[k := A1]> (delete k cp0')) at 2;
            last by apply (insert_delete_id _ _ _ Hcp0'k).
          replace in0' with (<[k := d]> (delete k in0')) at 2;
            last by apply (insert_delete_id _ _ _ Hin0'k).
          apply absq0_step_call_enq; [|done].
          rewrite dom_delete_L. set_solver.
        * (* bs(s, u) *)
          apply not_elem_of_dom in Hfresh as Hcpk_none.
          split; simpl.
          -- apply (bs_nodup _ _ Hbs').
          -- (* bs_completed_in *)
            intros k0 d0 Hk0_O Hℓk0.
            destruct (decide (k = k0)) as [->|Hne_k0].
            { rewrite Hℓk_none in Hℓk0. discriminate. }
            apply (bs_completed_in _ _ Hbs' k0 d0); simpl.
            { set_solver. }
            rewrite (lookup_insert_ne _ _ _ _ Hne_k0) //.
          -- (* bs_seq_from_O *)
            intros k0 d0 Hkd0.
            destruct (bs_seq_from_O _ _ Hbs' k0 d0 Hkd0)
              as (f & Hk0_O' & Hℓ'k0).
            simpl in Hℓ'k0.
            destruct (decide (k = k0)) as [->|Hne_k0].
            { rewrite lookup_insert_eq in Hℓ'k0. inversion Hℓ'k0; subst.
              exfalso. by apply Hd_notin. }
            rewrite (lookup_insert_ne _ _ _ _ Hne_k0) in Hℓ'k0.
            exists f. split; last done. set_solver.
          -- (* bs_linearization *)
            intros i j ki di kj dj Hij Hi Hj Hlt.
            eapply (bs_linearization _ _ Hbs' i j ki di kj dj Hij Hi Hj).
            simpl. set_solver.
          -- apply (bs_rv_agree _ _ Hbs').
          -- (* bs_R1_iff *)
            intros k0.
            destruct (decide (k = k0)) as [->|Hne_k0].
            { rewrite Hcpk_none lookup_delete_eq.
              split; intros [=]. }
            rewrite lookup_delete_ne //.
            pose proof (bs_R1_iff _ _ Hbs' k0) as Hiff. simpl in Hiff.
            rewrite (lookup_insert_ne _ _ _ _ Hne_k0) in Hiff. exact Hiff.
          -- (* bs_R2_iff *)
            intros k0.
            destruct (decide (k = k0)) as [->|Hne_k0].
            { rewrite Hcpk_none lookup_delete_eq.
              split; intros [=]. }
            rewrite lookup_delete_ne //.
            pose proof (bs_R2_iff _ _ Hbs' k0) as Hiff. simpl in Hiff.
            rewrite (lookup_insert_ne _ _ _ _ Hne_k0) in Hiff. exact Hiff.
          -- (* bs_R3_iff *)
            intros k0.
            destruct (decide (k = k0)) as [->|Hne_k0].
            { rewrite Hcpk_none lookup_delete_eq.
              split; intros [=]. }
            rewrite lookup_delete_ne //.
            pose proof (bs_R3_iff _ _ Hbs' k0) as Hiff. simpl in Hiff.
            rewrite (lookup_insert_ne _ _ _ _ Hne_k0) in Hiff. exact Hiff.
          -- (* bs_enq_input *)
            intros k0 d0 f0 Hℓk0.
            destruct (decide (k = k0)) as [->|Hne_k0].
            { rewrite Hℓk_none in Hℓk0. discriminate. }
            rewrite lookup_delete_ne //.
            apply (bs_enq_input _ _ Hbs' k0 d0 f0). simpl.
            rewrite (lookup_insert_ne _ _ _ _ Hne_k0) //.
          -- (* bs_in0_dom *)
            intros k0.
            pose proof (bs_in0_dom _ _ Hbs' k0) as Hiff. simpl in Hiff.
            destruct (decide (k = k0)) as [->|Hne_k0].
            { rewrite lookup_delete_eq Hcpk_none. split.
              - intros [? [=]].
              - intros [[=]|[=]]. }
            rewrite lookup_delete_ne //.
            rewrite (lookup_insert_ne _ _ _ _ Hne_k0) in Hiff. exact Hiff.
          -- (* bs_A1_iff *)
            intros k0.
            destruct (decide (k = k0)) as [->|Hne_k0].
            { rewrite lookup_delete_eq. split.
              - intros [=].
              - intros (_ & d0 & Hℓk0 & _).
                rewrite Hℓk_none in Hℓk0. discriminate. }
            rewrite lookup_delete_ne //.
            pose proof (bs_A1_iff _ _ Hbs' k0) as Hiff. simpl in Hiff.
            rewrite (lookup_insert_ne _ _ _ _ Hne_k0) in Hiff.
            split.
            { intros HA1. apply Hiff in HA1 as (Hk0_O' & d0 & Hℓk0 & Hd0_out).
              split; last by exists d0. set_solver. }
            intros (Hk0_O & d0 & Hℓk0 & Hd0_out).
            apply Hiff. split; [set_solver| by exists d0].
          -- (* bs_A_iff *)
            intros k0.
            destruct (decide (k = k0)) as [->|Hne_k0].
            { rewrite lookup_delete_eq. split.
              - intros [=].
              - intros [(d0 & Hℓk0 & _) | (_ & Hcp_k)].
                + rewrite Hℓk_none in Hℓk0. discriminate.
                + rewrite Hcpk_none in Hcp_k. discriminate. }
            rewrite lookup_delete_ne //.
            pose proof (bs_A_iff _ _ Hbs' k0) as Hiff. simpl in Hiff.
            rewrite (lookup_insert_ne _ _ _ _ Hne_k0) in Hiff.
            rewrite (lookup_insert_ne _ _ _ _ Hne_k0) in Hiff.
            split.
            { intros HA. apply Hiff in HA as
                [(d0 & Hℓk0 & Hd0_in) | (HnotO & Hcp_k0)].
              - left. exists d0. split; done.
              - right. split; last done. set_solver. }
            intros [(d0 & Hℓk0 & Hd0_in) | (HnotO & Hcp_k0)].
            { apply Hiff. left. exists d0. split; done. }
            apply Hiff. right. split; last done. set_solver.
          -- (* bs_A2_iff *)
            intros k0.
            destruct (decide (k = k0)) as [->|Hne_k0].
            { rewrite Hcpk_none lookup_delete_eq.
              split; intros [=]. }
            rewrite lookup_delete_ne //.
            pose proof (bs_A2_iff _ _ Hbs' k0) as Hiff. simpl in Hiff.
            rewrite (lookup_insert_ne _ _ _ _ Hne_k0) in Hiff. exact Hiff.
      + (* Case B: (k, d) ∈ σ'. *)
        assert (cp0' !! k = Some A) as Hcp0'_A.
        { apply (bs_A_iff _ _ Hbs' k). left. exists d.
          split; last done. simpl. by rewrite lookup_insert_eq. }
        assert (in0' !! k = Some d) as Hin0'_d.
        { apply (bs_enq_input _ _ Hbs' k d PEND).
          simpl. by rewrite lookup_insert_eq. }
        assert (cp !! k = None) as Hcpk_none
          by (apply not_elem_of_dom; exact Hfresh).
        (* Split σ' = pre_p ++ (k, d) :: post_p at the pair (k, d).
           Under [bag_like.queue_model]'s head=oldest convention,
           [pre_p] is the older prefix (already in [u]'s [σ_u]) and
           [post_p] is the newer suffix that linearizes after [k] and
           must be replayed via LIN-ENQ steps. *)
        destruct (list_elem_of_split _ _ Hd_in) as (pre_p & post_p & Hσ'_split).
        pose proof (bs_nodup _ _ Hbs') as Hnd_σ'.
        simpl in Hnd_σ'. rewrite Hσ'_split in Hnd_σ'.
        rewrite fmap_app fmap_cons in Hnd_σ'. simpl in Hnd_σ'.
        rewrite NoDup_app in Hnd_σ'.
        destruct Hnd_σ' as (Hnd_pre_keys & Hpre_keys_notin_kpost & Hnd_kpost).
        apply NoDup_cons in Hnd_kpost as [Hk_notin_post_keys Hnd_post_keys].
        assert (k ∉ pre_p.*1) as Hk_notin_pre_keys.
        { intros Hk_pre. apply (Hpre_keys_notin_kpost k Hk_pre).
          rewrite elem_of_cons. by left. }
        (* Tag-level facts for the two sublists. *)
        assert (∀ k' v, (k', v) ∈ pre_p → k' ∈ pre_p.*1) as Hpre_key_in.
        { intros k' v Hkv. apply list_elem_of_fmap. by exists (k', v). }
        assert (∀ k' v, (k', v) ∈ post_p → k' ∈ post_p.*1) as Hpost_key_in.
        { intros k' v Hkv. apply list_elem_of_fmap. by exists (k', v). }
        (* For each (k_v, v) ∈ post_p: k_v ∈ O, ℓ(k_v) = (v, PEND),
           cp(k_v) = A1, cp0'(k_v) = A. The newer-than-[k] elements
           must still be pending in [s] because at [s] they have not
           yet been completed (otherwise [k]'s CALL-ENQ would have
           added a happens-before edge from them to [k], contradicting
           [bs_linearization]'s direction on σ'). *)
        assert (Hkeys_props : Forall (λ kv : positive * val,
          ℓ !! kv.1 = Some (kv.2, PEND) ∧
          kv.1 ∈ O ∧
          cp !! kv.1 = Some A1 ∧
          cp0' !! kv.1 = Some A) post_p).
        { (* Step 1: No (k_v, v) ∈ post_p has a COMP flag —
              [bs_linearization] applied at positions [length pre_p]
              (for [k]) and at the position of [k_v] (in the [post_p]
              part of σ', strictly larger) forbids the new edge
              [(k_v, k)] that CALL-ENQ would have added. *)
          assert (∀ k_v v, (k_v, v) ∈ post_p →
            ∀ f, ℓ !! k_v = Some (v, f) → f = PEND) as Hno_comp.
          { intros k_v v Hkv_post f Hℓk_v.
            destruct f as [|]; first done.
            exfalso.
            destruct (list_elem_of_lookup_1 _ _ Hkv_post) as (i & Hi_post).
            set (j := length pre_p + S i).
            assert (σ' !! j = Some (k_v, v)) as Hj_σ'.
            { rewrite Hσ'_split /j lookup_app_r; last lia.
              replace (length pre_p + S i - length pre_p) with (S i) by lia.
              simpl. exact Hi_post. }
            assert (σ' !! length pre_p = Some (k, d)) as Hkd_σ'.
            { rewrite Hσ'_split.
              rewrite lookup_app_r // Nat.sub_diag //. }
            assert (length pre_p < j) as Hlt_j by (unfold j; lia).
            assert (k_v ≠ k) as Hk_v_ne.
            { intros ->. apply Hk_notin_post_keys. by eapply Hpost_key_in. }
            apply (bs_linearization _ _ Hbs' (length pre_p) j k d k_v v
                     Hlt_j Hkd_σ' Hj_σ').
            simpl. apply elem_of_union. right.
            apply elem_of_map. exists k_v. split; first done.
            rewrite /absq_COMP. apply elem_of_filter.
            split; last first.
            { (* k_v ∈ O: from bs_seq_from_O on s'. *)
              pose proof (list_elem_of_lookup_2 _ _ _ Hj_σ') as Hkv_σ'.
              destruct (bs_seq_from_O _ _ Hbs' _ _ Hkv_σ')
                as (f' & Hk_v_O' & _).
              simpl in Hk_v_O'. set_solver. }
            rewrite /is_COMP. by exists v. }
          apply Forall_forall. intros [k_v v] Hkv_post.
          assert ((k_v, v) ∈ σ') as Hkv_σ'.
          { rewrite Hσ'_split. apply elem_of_app. right.
            apply elem_of_cons. by right. }
          destruct (bs_seq_from_O _ _ Hbs' _ _ Hkv_σ')
            as (f_v & Hk_v_O' & Hℓ'k_v).
          simpl in Hk_v_O', Hℓ'k_v.
          assert (k_v ≠ k) as Hk_v_ne.
          { intros ->. apply Hk_notin_post_keys. by eapply Hpost_key_in. }
          rewrite (lookup_insert_ne _ k k_v _
                   (λ H, Hk_v_ne (eq_sym H))) in Hℓ'k_v.
          assert (k_v ∈ O) as Hk_v_O by set_solver.
          assert (f_v = PEND) as -> by (by eapply Hno_comp).
          assert (cp0' !! k_v = Some A) as Hcp0'_A_v.
          { apply (bs_A_iff _ _ Hbs' k_v). left. exists v.
            split; last exact Hkv_σ'. simpl.
            by rewrite (lookup_insert_ne _ k k_v _
                     (λ H, Hk_v_ne (eq_sym H))). }
          assert (cp !! k_v = Some A1) as Hcp_A1_v.
          { destruct (absq_wf_ℓcp _ _ Hwf _ _ _ Hℓ'k_v) as [|Hcp_A2];
              first done.
            exfalso.
            assert (cp0' !! k_v = Some A2) as Hcp0'_A2.
            { apply (bs_A2_iff _ _ Hbs' k_v). simpl.
              by rewrite (lookup_insert_ne _ k k_v _
                       (λ H, Hk_v_ne (eq_sym H))). }
            rewrite Hcp0'_A_v in Hcp0'_A2. discriminate. }
          simpl. done. }
        (* Helper: lookup Hkeys_props by key. *)
        assert (Hkv_props : ∀ k_v v,
          (k_v, v) ∈ post_p →
          ℓ !! k_v = Some (v, PEND) ∧ k_v ∈ O ∧
          cp !! k_v = Some A1 ∧ cp0' !! k_v = Some A).
        { rewrite Forall_forall in Hkeys_props.
          intros k_v v Hkv. by apply (Hkeys_props (k_v, v) Hkv). }
        (* Pick u with σ_u = pre_p (the older prefix already in u),
            in0_u = delete k in0', rv0_u = rv0',
            cp0_u = (delete k cp0') with each [k_v ∈ post_p.*1 ↦ A1]. *)
        exists (AbsQ0State pre_p (delete k in0') rv0'
                (insert_all A1 (delete k cp0') post_p.*1)),
               ((k, ACallEnq d) :: (k, ALinEnq d) ::
                 map (λ kv, (kv.1, ALinEnq kv.2)) post_p).
        split_and!; last first.
        * (* Label projection: only [(k, ACallEnq d)] is observable. *)
          unfold project_labels.
          rewrite filter_cons_True; last done.
          rewrite filter_nil.
          rewrite filter_cons_True; last done.
          rewrite filter_cons_False; last by intros [].
          f_equal.
          (* The LIN-ENQ tail filters to []. *)
          symmetry.
          generalize post_p. clear. intros l.
          induction l as [|[k0 v0] l IH]; simpl; first done.
          rewrite filter_cons_False; [|by intros []]. exact IH.
        * (* AbsQ0 trace: CALL-ENQ + LIN-ENQ(k, d) + LIN-ENQ tail. *)
          change ((k, ACallEnq d) :: (k, ALinEnq d) ::
                  map (λ kv, (kv.1, ALinEnq kv.2)) post_p)
            with ([(k, ACallEnq d); (k, ALinEnq d)] ++
                  map (λ kv, (kv.1, ALinEnq kv.2)) post_p).
          eapply lts_steps_app.
          { (* Part 1: CALL-ENQ + LIN-ENQ(k, d). *)
            eapply lts_steps_cons.
            { apply absq0_step_call_enq.
              - apply not_elem_of_dom.
                rewrite insert_all_lookup_notin //.
                by rewrite lookup_delete_eq.
              - exact Hd_ub. }
            eapply lts_steps_cons.
            { apply absq0_step_lin_enq;
                [by rewrite lookup_insert_eq
                |by rewrite lookup_insert_eq
                |exact Hd_ub]. }
            apply lts_steps_nil. }
          (* Part 2: massage post-state to match the helper's output. *)
          assert (AbsQ0State σ' in0' rv0' cp0' =
                   AbsQ0State
                     ((pre_p ++ [(k, d)]) ++ post_p)
                     (<[k := d]> (delete k in0'))
                     rv0'
                     (insert_all A
                        (<[k := A]>
                         (<[k := A1]>
                          (insert_all A1 (delete k cp0') post_p.*1)))
                        post_p.*1)) as Heq.
          { f_equal.
            - by rewrite -app_assoc /= -Hσ'_split.
            - symmetry. by apply (insert_delete_id _ _ _ Hin0'_d).
            - apply map_eq. intros x.
              rewrite insert_insert_eq.
              destruct (decide (k = x)) as [<-|Hne].
              + rewrite insert_all_lookup_notin //.
                by rewrite lookup_insert_eq.
              + destruct (decide (x ∈ post_p.*1)) as [Hx_in|Hx_notin].
                * rewrite insert_all_lookup_in //.
                  apply list_elem_of_fmap in Hx_in as ([x' v] & -> & Hxv).
                  destruct (Hkv_props _ _ Hxv) as (_ & _ & _ & Hcp0'_A_x).
                  done.
                * rewrite insert_all_lookup_notin //.
                  rewrite (lookup_insert_ne _ _ _ _ Hne).
                  rewrite insert_all_lookup_notin //.
                  by rewrite lookup_delete_ne. }
          rewrite Heq.
          apply absq0_lin_enq_seq_steps; first exact Hnd_post_keys.
          (* Build the Forall over post_p from Hkeys_props. *)
          rewrite Forall_forall. intros [k_i v_i] Hkv_post.
          destruct (Hkv_props _ _ Hkv_post) as (Hℓ_k_i & Hk_i_O & Hcp_k_i_A1 & Hcp0'_A_k_i).
          assert (k_i ∈ post_p.*1) as Hk_i_post by (by eapply Hpost_key_in).
          assert (k_i ≠ k) as Hk_i_ne_k
            by (intros ->; by apply Hk_notin_post_keys).
          simpl. split_and!.
          ** rewrite insert_insert_eq.
             rewrite (lookup_insert_ne _ k k_i _
                      (λ H, Hk_i_ne_k (eq_sym H))).
             by apply insert_all_lookup_in.
          ** rewrite (lookup_insert_ne _ k k_i _
                      (λ H, Hk_i_ne_k (eq_sym H))).
             rewrite lookup_delete_ne; last
               (exact (λ H, Hk_i_ne_k (eq_sym H))).
             apply (bs_enq_input _ _ Hbs' k_i v_i PEND). simpl.
             by rewrite (lookup_insert_ne _ k k_i _
                        (λ H, Hk_i_ne_k (eq_sym H))).
          ** by eapply (absq_wf_valid_value _ _ Hwf _ _ PEND).
        * (* bs(s, u). 12 fields to verify. *)
          split; simpl.
          -- (* bs_nodup: pre_p.*1 is NoDup *) exact Hnd_pre_keys.
          -- (* bs_completed_in: a COMP enqueue cannot be in post_p (no
                COMP there by Hkv_props), nor be (k, d) (k is fresh), so
                must lie in pre_p. *)
            intros k0 d0 Hk0_O Hℓk0.
            destruct (decide (k = k0)) as [<-|Hne_k0].
            { rewrite Hℓk_none in Hℓk0. discriminate. }
            assert ((<[k := (d, PEND)]>ℓ) !! k0 = Some (d0, COMP)) as Hℓ'k0.
            { by rewrite (lookup_insert_ne _ _ _ _ Hne_k0). }
            assert (k0 ∈ O ∪ {[k]}) as Hk0_O' by set_solver.
            pose proof (bs_completed_in _ _ Hbs' _ _ Hk0_O' Hℓ'k0) as Hkd0_σ'.
            simpl in Hkd0_σ'. rewrite Hσ'_split in Hkd0_σ'.
            apply elem_of_app in Hkd0_σ' as [Hd0_pre | Hd0_kpost].
            { exact Hd0_pre. }
            apply elem_of_cons in Hd0_kpost as [Heq | Hd0_post].
            { inversion Heq; subst.
              exfalso. apply Hne_k0. done. }
            (* (k0, d0) ∈ post_p: contradicts Hkv_props (gives PEND flag). *)
            exfalso.
            destruct (Hkv_props _ _ Hd0_post) as (Hℓk_d0 & _).
            rewrite Hℓk_d0 in Hℓk0. inversion Hℓk0.
          -- (* bs_seq_from_O *)
            intros k_q v_q Hkv_q_pre.
            assert ((k_q, v_q) ∈ σ') as Hkv_q_σ'.
            { rewrite Hσ'_split. apply elem_of_app. by left. }
            destruct (bs_seq_from_O _ _ Hbs' _ _ Hkv_q_σ')
              as (f0 & Hk_q_O' & Hℓ'k_q).
            simpl in Hk_q_O', Hℓ'k_q.
            destruct (decide (k = k_q)) as [<-|Hne_k_q].
            { rewrite lookup_insert_eq in Hℓ'k_q.
              inversion Hℓ'k_q; subst.
              exfalso. apply Hk_notin_pre_keys. by eapply Hpre_key_in. }
            rewrite (lookup_insert_ne _ _ _ _ Hne_k_q) in Hℓ'k_q.
            exists f0. split; last done. set_solver.
          -- (* bs_linearization: pre_p positions in σ_u are the same
                positions in σ' (since pre_p is a prefix of σ'). *)
            intros i j ki di kj dj Hij Hi Hj Hlt.
            assert (σ' !! i = Some (ki, di)) as Hi'.
            { rewrite Hσ'_split. by apply lookup_app_l_Some. }
            assert (σ' !! j = Some (kj, dj)) as Hj'.
            { rewrite Hσ'_split. by apply lookup_app_l_Some. }
            apply (bs_linearization _ _ Hbs' i j ki di kj dj Hij Hi' Hj').
            simpl. set_solver.
          -- (* bs_rv_agree *) apply (bs_rv_agree _ _ Hbs').
          -- (* bs_R1_iff *)
            intros k0.
            destruct (decide (k = k0)) as [<-|Hne_k0].
            { rewrite Hcpk_none.
              rewrite insert_all_lookup_notin //.
              rewrite lookup_delete_eq.
              split; intros [=]. }
            destruct (decide (k0 ∈ post_p.*1)) as [Hk0_ks|Hk0_not_ks].
            { apply list_elem_of_fmap in Hk0_ks as Hk0_ks_ex.
              destruct Hk0_ks_ex as ([k0' v] & -> & Hkv_post).
              destruct (Hkv_props _ _ Hkv_post) as (_ & _ & Hcp_A1 & _).
              rewrite Hcp_A1.
              rewrite (insert_all_lookup_in _ _ _ _ Hk0_ks).
              split; intros Heq; inversion Heq. }
            rewrite insert_all_lookup_notin // lookup_delete_ne //.
            pose proof (bs_R1_iff _ _ Hbs' k0) as Hiff. simpl in Hiff.
            rewrite (lookup_insert_ne _ _ _ _ Hne_k0) in Hiff. exact Hiff.
          -- (* bs_R2_iff *)
            intros k0.
            destruct (decide (k = k0)) as [<-|Hne_k0].
            { rewrite Hcpk_none.
              rewrite insert_all_lookup_notin //.
              rewrite lookup_delete_eq.
              split; intros [=]. }
            destruct (decide (k0 ∈ post_p.*1)) as [Hk0_ks|Hk0_not_ks].
            { apply list_elem_of_fmap in Hk0_ks as Hk0_ks_ex.
              destruct Hk0_ks_ex as ([k0' v] & -> & Hkv_post).
              destruct (Hkv_props _ _ Hkv_post) as (_ & _ & Hcp_A1 & _).
              rewrite Hcp_A1.
              rewrite (insert_all_lookup_in _ _ _ _ Hk0_ks).
              split; intros Heq; inversion Heq. }
            rewrite insert_all_lookup_notin // lookup_delete_ne //.
            pose proof (bs_R2_iff _ _ Hbs' k0) as Hiff. simpl in Hiff.
            rewrite (lookup_insert_ne _ _ _ _ Hne_k0) in Hiff. exact Hiff.
          -- (* bs_R3_iff *)
            intros k0.
            destruct (decide (k = k0)) as [<-|Hne_k0].
            { rewrite Hcpk_none.
              rewrite insert_all_lookup_notin //.
              rewrite lookup_delete_eq.
              split; intros [=]. }
            destruct (decide (k0 ∈ post_p.*1)) as [Hk0_ks|Hk0_not_ks].
            { apply list_elem_of_fmap in Hk0_ks as Hk0_ks_ex.
              destruct Hk0_ks_ex as ([k0' v] & -> & Hkv_post).
              destruct (Hkv_props _ _ Hkv_post) as (_ & _ & Hcp_A1 & _).
              rewrite Hcp_A1.
              rewrite (insert_all_lookup_in _ _ _ _ Hk0_ks).
              split; intros Heq; inversion Heq. }
            rewrite insert_all_lookup_notin // lookup_delete_ne //.
            pose proof (bs_R3_iff _ _ Hbs' k0) as Hiff. simpl in Hiff.
            rewrite (lookup_insert_ne _ _ _ _ Hne_k0) in Hiff. exact Hiff.
          -- (* bs_enq_input *)
            intros k0 d0 f0 Hℓk0.
            destruct (decide (k = k0)) as [<-|Hne_k0].
            { rewrite Hℓk_none in Hℓk0. discriminate. }
            rewrite lookup_delete_ne //.
            apply (bs_enq_input _ _ Hbs' k0 d0 f0). simpl.
            by rewrite (lookup_insert_ne _ _ _ _ Hne_k0).
          -- (* bs_in0_dom *)
            intros k0.
            pose proof (bs_in0_dom _ _ Hbs' k0) as Hiff. simpl in Hiff.
            destruct (decide (k = k0)) as [<-|Hne_k0].
            { rewrite lookup_delete_eq Hcpk_none. split.
              { intros [? [=]]. }
              intros [[=]|[=]]. }
            rewrite lookup_delete_ne //.
            rewrite (lookup_insert_ne _ _ _ _ Hne_k0) in Hiff.
            exact Hiff.
          -- (* bs_A1_iff: keys at A1 in u are exactly post_p.*1
                (those marked A1 by [insert_all]). *)
            intros k0.
            destruct (decide (k = k0)) as [<-|Hne_k0].
            { rewrite insert_all_lookup_notin // lookup_delete_eq. split.
              - intros [=].
              - intros (_ & d_w & Hℓk & _).
                rewrite Hℓk_none in Hℓk. discriminate. }
            destruct (decide (k0 ∈ post_p.*1)) as [Hk0_ks|Hk0_not_ks].
            { apply list_elem_of_fmap in Hk0_ks as Hk0_ks_ex.
              destruct Hk0_ks_ex as ([k0' v] & Hk0_eq & Hkv_post).
              simpl in Hk0_eq. subst k0'.
              destruct (Hkv_props _ _ Hkv_post)
                as (Hℓk0 & Hk0_O & _ & _).
              assert (k0 ∈ post_p.*1) as Hk0_in_post by (by eapply Hpost_key_in).
              assert (k0 ∉ pre_p.*1) as Hk0_notpre.
              { intros Hk0_pre.
                apply (Hpre_keys_notin_kpost k0 Hk0_pre).
                apply elem_of_cons. by right. }
              rewrite insert_all_lookup_in; last exact Hk0_in_post.
              split.
              - intros _. split; [done|]. exists v. split; first done.
                intros Hpre. apply Hk0_notpre. by eapply Hpre_key_in.
              - done. }
            rewrite insert_all_lookup_notin // lookup_delete_ne //.
            pose proof (bs_A1_iff _ _ Hbs' k0) as Hiff. simpl in Hiff.
            rewrite (lookup_insert_ne _ _ _ _ Hne_k0) in Hiff.
            rewrite Hiff. clear Hiff.
            split.
            { intros (Hk0_O' & d_w & Hℓk0 & Hd_w_σ').
              split. { set_solver. }
              exists d_w. split; first done.
              intros Hd_w_pre. apply Hd_w_σ'.
              rewrite Hσ'_split. apply elem_of_app. by left. }
            intros (Hk0_O & d_w & Hℓk0 & Hd_w_pre).
            split. { set_solver. }
            exists d_w. split; first done.
            intros Hd_w_σ'. rewrite Hσ'_split in Hd_w_σ'.
            apply elem_of_app in Hd_w_σ' as [Hd_w_pre' | Hd_w_kpost]; first done.
            apply elem_of_cons in Hd_w_kpost as [Heq|Hd_w_post].
            { inversion Heq; subst. by apply Hne_k0. }
            apply Hk0_not_ks. by eapply Hpost_key_in.
          -- (* bs_A_iff *)
            intros k0.
            destruct (decide (k = k0)) as [<-|Hne_k0].
            { rewrite insert_all_lookup_notin // lookup_delete_eq. split.
              { intros [=]. }
              intros [(d_w & Hℓk & _) | (_ & Hcp_k0)].
              { rewrite Hℓk_none in Hℓk. discriminate. }
              rewrite Hcpk_none in Hcp_k0. discriminate. }
            destruct (decide (k0 ∈ post_p.*1)) as [Hk0_ks|Hk0_not_ks].
            { pose proof Hk0_ks as Hk0_ks_ex.
              apply list_elem_of_fmap in Hk0_ks_ex.
              destruct Hk0_ks_ex as ([k0' v] & Heq & Hkv_post).
              simpl in Heq. subst k0'.
              destruct (Hkv_props _ _ Hkv_post)
                as (Hℓk0 & Hk0_O & Hcp_A1_k0 & _).
              assert (k0 ∉ pre_p.*1) as Hk0_notpre.
              { intros Hk0_pre. apply (Hpre_keys_notin_kpost k0 Hk0_pre).
                apply elem_of_cons. by right. }
              rewrite insert_all_lookup_in; last exact Hk0_ks.
              split.
              { intros [=]. }
              intros [(d_w & Hℓ'k0 & Hkd_w_pre) | (HnotO & _)].
              { exfalso. rewrite Hℓ'k0 in Hℓk0. inversion Hℓk0; subst d_w.
                apply Hk0_notpre. by eapply Hpre_key_in. }
              exfalso. by apply HnotO. }
            rewrite insert_all_lookup_notin // lookup_delete_ne //.
            pose proof (bs_A_iff _ _ Hbs' k0) as Hiff. simpl in Hiff.
            rewrite (lookup_insert_ne _ _ _ _ Hne_k0) in Hiff.
            rewrite (lookup_insert_ne _ _ _ _ Hne_k0) in Hiff.
            rewrite Hiff. clear Hiff.
            split.
            { intros [(d_w & Hℓk0 & Hkd_w_σ') | (HnotO' & Hcp_A1)].
              { rewrite Hσ'_split in Hkd_w_σ'.
                apply elem_of_app in Hkd_w_σ' as [Hkd_w_pre | Hkd_w_dpost].
                { left. exists d_w. split; done. }
                apply elem_of_cons in Hkd_w_dpost as [Heq|Hkd_w_post].
                { inversion Heq; subst. by exfalso; apply Hne_k0. }
                exfalso. apply Hk0_not_ks. by eapply Hpost_key_in. }
              right. split; last done. set_solver. }
            intros [(d_w & Hℓk0 & Hkd_w_pre) | (HnotO & Hcp_A1)].
            { left. exists d_w. split; first done.
              rewrite Hσ'_split. apply elem_of_app. by left. }
            right. split; last done. set_solver.
          -- (* bs_A2_iff *)
            intros k0.
            destruct (decide (k = k0)) as [<-|Hne_k0].
            { rewrite Hcpk_none.
              rewrite insert_all_lookup_notin //.
              rewrite lookup_delete_eq.
              split; intros [=]. }
            destruct (decide (k0 ∈ post_p.*1)) as [Hk0_ks|Hk0_not_ks].
            { apply list_elem_of_fmap in Hk0_ks as Hk0_ks_ex.
              destruct Hk0_ks_ex as ([k0' v] & -> & Hkv_post).
              destruct (Hkv_props _ _ Hkv_post) as (_ & _ & Hcp_A1 & _).
              rewrite Hcp_A1.
              rewrite (insert_all_lookup_in _ _ _ _ Hk0_ks).
              split; intros Heq; inversion Heq. }
            rewrite insert_all_lookup_notin // lookup_delete_ne //.
            pose proof (bs_A2_iff _ _ Hbs' k0) as Hiff. simpl in Hiff.
            rewrite (lookup_insert_ne _ _ _ _ Hne_k0) in Hiff. exact Hiff.
    - (* CALL-DEQ:
        [s = (O, lt, ℓ, rv, cp)], [s' = (O, lt, ℓ, rv, cp[k ↦ R1])],
        labelled [(k, ACallDeq)]. We pick [u] to be [u'] with [cp0(k)]
        removed (so that applying AbsQ0's CALL-DEQ transition from [u]
        yields [u']). *)
      destruct u' as [σ' in0' rv0' cp0'].
      (* From bs_R1_iff on s' we get cp0'(k) = Some R1. *)
      assert (absq_cp
        {| absq_O := O; absq_lt := lt; absq_l := ℓ;
           absq_rv := rv; absq_cp := <[k:=R1]> cp |} !! k = Some R1) as HLHS.
      { cbn. by rewrite lookup_insert_eq. }
      pose proof (proj1 (bs_R1_iff _ _ Hbs' k) HLHS) as HR1'.
      clear HLHS.
      exists (AbsQ0State σ' in0' rv0' (delete k cp0')),
             [(k, ACallDeq)].
      split_and!; last first.
      + done.
      + eapply lts_steps_cons; last apply lts_steps_nil.
        (* AbsQ0's CALL-DEQ step from the modified u' *)
        replace cp0' with (<[k := R1]> (delete k cp0')) at 2;
          last by apply (insert_delete_id _ _ _ HR1').
        apply absq0_step_call_deq.
        rewrite dom_delete_L. set_solver.
      + (* bs(s, u) *)
        split; simpl.
        * apply (bs_nodup _ _ Hbs').
        * apply (bs_completed_in _ _ Hbs').
        * apply (bs_seq_from_O _ _ Hbs').
        * apply (bs_linearization _ _ Hbs').
        * apply (bs_rv_agree _ _ Hbs').
        * intros k0.
          apply not_elem_of_dom in Hfresh.
          destruct (decide (k = k0)) as [->|Hne].
          { rewrite lookup_delete_eq Hfresh. split; intros [=]. }
          rewrite lookup_delete_ne //.
          rewrite -(bs_R1_iff _ _ Hbs' k0) /=.
          rewrite lookup_insert_ne //.
        * intros k0.
          apply not_elem_of_dom in Hfresh.
          destruct (decide (k = k0)) as [->|Hne].
          { rewrite Hfresh lookup_delete_eq. split; intros [=]. }
          rewrite lookup_delete_ne //.
          rewrite -(bs_R2_iff _ _ Hbs' k0) /=.
          rewrite lookup_insert_ne //.
        * intros k0.
          apply not_elem_of_dom in Hfresh.
          destruct (decide (k = k0)) as [->|Hne].
          { rewrite Hfresh lookup_delete_eq. split; intros [=]. }
          rewrite lookup_delete_ne //.
          rewrite -(bs_R3_iff _ _ Hbs' k0) /=.
          rewrite lookup_insert_ne //.
        * intros k0 d0 f0. apply (bs_enq_input _ _ Hbs' k0 d0 f0).
        * intros k0.
          apply not_elem_of_dom in Hfresh.
          pose proof (bs_in0_dom _ _ Hbs' k0) as Hdom. simpl in Hdom.
          destruct (decide (k = k0)) as [->|Hne].
          { rewrite lookup_insert_eq in Hdom.
            rewrite Hfresh. split.
            - intros Hsome. apply Hdom in Hsome as [?|?]; discriminate.
            - intros [[=]|[=]]. }
          rewrite (lookup_insert_ne _ _ _ _ Hne) in Hdom. exact Hdom.
        * (* bs_A1_iff *)
          intros k0.
          apply not_elem_of_dom in Hfresh.
          destruct (decide (k = k0)) as [->|Hne].
          { rewrite lookup_delete_eq. split.
            - intros Heq. discriminate Heq.
            - intros (_ & d0 & Hℓk & _).
              pose proof (bs_enq_input _ _ Hbs' _ _ _ Hℓk) as Hin0k.
              assert (is_Some (in0' !! k0)) as Hsome by (by eexists).
              apply (proj1 (bs_in0_dom _ _ Hbs' k0)) in Hsome as [Hcp_k|Hcp_k];
                simpl in Hcp_k; rewrite lookup_insert_eq in Hcp_k; discriminate. }
          rewrite lookup_delete_ne //.
          apply (bs_A1_iff _ _ Hbs' k0).
        * (* bs_A_iff *)
          intros k0.
          apply not_elem_of_dom in Hfresh.
          destruct (decide (k = k0)) as [->|Hne].
          { rewrite lookup_delete_eq. split.
            - intros Heq. discriminate Heq.
            - intros [(d0 & Hℓk & _) | (_ & Hcp_k)].
              + pose proof (bs_enq_input _ _ Hbs' _ _ _ Hℓk) as Hin0k.
                assert (is_Some (in0' !! k0)) as Hsome by (by eexists).
                apply (proj1 (bs_in0_dom _ _ Hbs' k0)) in Hsome as [Hcp_k|Hcp_k];
                  simpl in Hcp_k; rewrite lookup_insert_eq in Hcp_k; discriminate.
              + rewrite Hfresh in Hcp_k. discriminate. }
          rewrite lookup_delete_ne //.
          (* goal: cp0' !! k0 = Some A ↔ (∃ d, ℓ !! k0 = Some (d, PEND) ∧ d ∈ σ')
                                      ∨ (k0 ∉ O ∧ cp !! k0 = Some A1).
             Use bs_A_iff on s', u' for k0: s' has <[k:=R1]> cp, so the RHS
             disjunct mentions <[k:=R1]> cp !! k0, which for k0 ≠ k equals
             cp !! k0. *)
          pose proof (bs_A_iff _ _ Hbs' k0) as Hiff. simpl in Hiff.
          rewrite (lookup_insert_ne _ _ _ _ Hne) in Hiff. exact Hiff.
        * intros k0.
          apply not_elem_of_dom in Hfresh.
          destruct (decide (k = k0)) as [->|Hne].
          { rewrite Hfresh lookup_delete_eq. split; intros [=]. }
          rewrite lookup_delete_ne //.
          rewrite -(bs_A2_iff _ _ Hbs' k0) /=.
          rewrite (lookup_insert_ne _ _ _ _ Hne) //.
    - (* RET-ENQ1: cp(k) = A1, k ∈ O, ℓ(k) = (d, PEND).
        s' has ℓ flipped to (d, COMP) and cp[k ↦ A2]. We pick u with
        cp0_u(k) = A so that AbsQ0's RET-ENQ from u yields u'. *)
      destruct u' as [σ' in0' rv0' cp0'].
      pose proof (bs_A2_iff _ _ Hbs' k) as HA2'. simpl in HA2'.
      rewrite lookup_insert_eq in HA2'.
      destruct HA2' as [HA2' _]. specialize (HA2' eq_refl).
      (* d ∈ σ', from bs_completed_in on s' (k ∈ O, s'.ℓ(k) = (d, COMP)) *)
      pose proof (bs_completed_in _ _ Hbs' k d Hin) as Hd_in_seq.
      simpl in Hd_in_seq. rewrite lookup_insert_eq in Hd_in_seq.
      specialize (Hd_in_seq eq_refl).
      exists (AbsQ0State σ' in0' rv0' (<[k := A]> cp0')),
             [(k, ARetEnq)].
      split_and!; last first.
      + done.
      + eapply lts_steps_cons; last apply lts_steps_nil.
        replace cp0' with (<[k := A2]> (<[k := A]> cp0')) at 2;
          last by rewrite insert_insert_eq (insert_id _ _ _ HA2').
        apply absq0_step_ret_enq.
        by rewrite lookup_insert_eq.
      + (* bs(s, u) *)
        split; simpl.
        * apply (bs_nodup _ _ Hbs').
        * (* bs_completed_in *)
          intros k0 d0 Hk0_O Hℓk0.
          destruct (decide (k = k0)) as [->|Hne].
          { rewrite Hℓ in Hℓk0. discriminate. }
          apply (bs_completed_in _ _ Hbs' k0 d0 Hk0_O).
          simpl. by rewrite lookup_insert_ne.
        * (* bs_seq_from_O *)
          intros k0 d0 Hkd0.
          destruct (bs_seq_from_O _ _ Hbs' k0 d0 Hkd0)
            as (f0 & Hk0_O & Hℓk0).
          simpl in Hℓk0.
          destruct (decide (k = k0)) as [->|Hne].
          { rewrite lookup_insert_eq in Hℓk0. inversion Hℓk0; subst.
            exists PEND. split; first done. exact Hℓ. }
          rewrite lookup_insert_ne // in Hℓk0.
          exists f0. split; done.
        * (* bs_linearization *)
          intros i j ki di kj dj Hij Hi Hj Hlt.
          eapply (bs_linearization _ _ Hbs' i j ki di kj dj Hij Hi Hj).
          simpl. exact Hlt.
        * apply (bs_rv_agree _ _ Hbs').
        * (* bs_R1_iff *)
          intros k0.
          destruct (decide (k = k0)) as [->|Hne].
          { rewrite Hcp lookup_insert_eq. split; intros [=]. }
          rewrite (lookup_insert_ne _ _ _ _ Hne).
          pose proof (bs_R1_iff _ _ Hbs' k0) as Hiff. simpl in Hiff.
          rewrite (lookup_insert_ne _ _ _ _ Hne) in Hiff. exact Hiff.
        * (* bs_R2_iff *)
          intros k0.
          destruct (decide (k = k0)) as [->|Hne].
          { rewrite Hcp lookup_insert_eq. split; intros [=]. }
          rewrite (lookup_insert_ne _ _ _ _ Hne).
          pose proof (bs_R2_iff _ _ Hbs' k0) as Hiff. simpl in Hiff.
          rewrite (lookup_insert_ne _ _ _ _ Hne) in Hiff. exact Hiff.
        * (* bs_R3_iff *)
          intros k0.
          destruct (decide (k = k0)) as [->|Hne].
          { rewrite Hcp lookup_insert_eq. split; intros [=]. }
          rewrite (lookup_insert_ne _ _ _ _ Hne).
          pose proof (bs_R3_iff _ _ Hbs' k0) as Hiff. simpl in Hiff.
          rewrite (lookup_insert_ne _ _ _ _ Hne) in Hiff. exact Hiff.
        * (* bs_enq_input *)
          intros k0 d0 f0 Hℓk0.
          destruct (decide (k = k0)) as [->|Hne].
          { rewrite Hℓ in Hℓk0. inversion Hℓk0; subst.
            apply (bs_enq_input _ _ Hbs' k0 d0 COMP).
            simpl. by rewrite lookup_insert_eq. }
          apply (bs_enq_input _ _ Hbs' k0 d0 f0).
          simpl. by rewrite lookup_insert_ne.
        * (* bs_in0_dom *)
          intros k0.
          pose proof (bs_in0_dom _ _ Hbs' k0) as Hiff. simpl in Hiff.
          destruct (decide (k = k0)) as [->|Hne].
          { rewrite Hcp. split.
            - intros _. by left.
            - intros _.
              pose proof (bs_enq_input _ _ Hbs' k0 d COMP) as Hin0_eq.
              simpl in Hin0_eq. rewrite lookup_insert_eq in Hin0_eq.
              specialize (Hin0_eq eq_refl).
              by eexists. }
          rewrite (lookup_insert_ne _ _ _ _ Hne) in Hiff. exact Hiff.
        * (* bs_A1_iff *)
          intros k0.
          destruct (decide (k = k0)) as [->|Hne].
          { rewrite lookup_insert_eq. split.
            - intros [=].
            - intros (_ & d0 & Hℓk0 & Hd0_notin).
              rewrite Hℓ in Hℓk0. inversion Hℓk0; subst d0.
              exfalso. by apply Hd0_notin. }
          rewrite (lookup_insert_ne _ _ _ _ Hne).
          pose proof (bs_A1_iff _ _ Hbs' k0) as Hiff. simpl in Hiff.
          rewrite (lookup_insert_ne _ _ _ _ Hne) in Hiff. exact Hiff.
        * (* bs_A_iff *)
          intros k0.
          destruct (decide (k = k0)) as [->|Hne].
          { rewrite lookup_insert_eq. split.
            - intros _. left. exists d. split; done.
            - intros _. done. }
          rewrite (lookup_insert_ne _ _ _ _ Hne).
          pose proof (bs_A_iff _ _ Hbs' k0) as Hiff. simpl in Hiff.
          rewrite (lookup_insert_ne cp k k0 A2 Hne) in Hiff.
          rewrite (lookup_insert_ne ℓ k k0 (d, COMP) Hne) in Hiff. exact Hiff.
        * (* bs_A2_iff *)
          intros k0.
          destruct (decide (k = k0)) as [->|Hne].
          { rewrite Hcp lookup_insert_eq. split; intros [=]. }
          rewrite (lookup_insert_ne _ _ _ _ Hne).
          pose proof (bs_A2_iff _ _ Hbs' k0) as Hiff. simpl in Hiff.
          rewrite (lookup_insert_ne _ _ _ _ Hne) in Hiff. exact Hiff.
    - (* RET-ENQ2: cp(k) = A1, k ∉ O. ℓ unchanged.
        s' has cp[k ↦ A2]. We pick u with cp0_u(k) = A. *)
      destruct u' as [σ' in0' rv0' cp0'].
      pose proof (bs_A2_iff _ _ Hbs' k) as HA2'. simpl in HA2'.
      rewrite lookup_insert_eq in HA2'.
      destruct HA2' as [HA2' _]. specialize (HA2' eq_refl).
      exists (AbsQ0State σ' in0' rv0' (<[k := A]> cp0')),
             [(k, ARetEnq)].
      split_and!; last first.
      + done.
      + eapply lts_steps_cons; last apply lts_steps_nil.
        replace cp0' with (<[k := A2]> (<[k := A]> cp0')) at 2;
          last by rewrite insert_insert_eq (insert_id _ _ _ HA2').
        apply absq0_step_ret_enq.
        by rewrite lookup_insert_eq.
      + (* bs(s, u) *)
        split; simpl.
        * apply (bs_nodup _ _ Hbs').
        * apply (bs_completed_in _ _ Hbs').
        * apply (bs_seq_from_O _ _ Hbs').
        * apply (bs_linearization _ _ Hbs').
        * apply (bs_rv_agree _ _ Hbs').
        * (* bs_R1_iff *)
          intros k0.
          destruct (decide (k = k0)) as [->|Hne].
          { rewrite Hcp lookup_insert_eq. split; intros [=]. }
          rewrite (lookup_insert_ne _ _ _ _ Hne).
          pose proof (bs_R1_iff _ _ Hbs' k0) as Hiff. simpl in Hiff.
          rewrite (lookup_insert_ne _ _ _ _ Hne) in Hiff. exact Hiff.
        * (* bs_R2_iff *)
          intros k0.
          destruct (decide (k = k0)) as [->|Hne].
          { rewrite Hcp lookup_insert_eq. split; intros [=]. }
          rewrite (lookup_insert_ne _ _ _ _ Hne).
          pose proof (bs_R2_iff _ _ Hbs' k0) as Hiff. simpl in Hiff.
          rewrite (lookup_insert_ne _ _ _ _ Hne) in Hiff. exact Hiff.
        * (* bs_R3_iff *)
          intros k0.
          destruct (decide (k = k0)) as [->|Hne].
          { rewrite Hcp lookup_insert_eq. split; intros [=]. }
          rewrite (lookup_insert_ne _ _ _ _ Hne).
          pose proof (bs_R3_iff _ _ Hbs' k0) as Hiff. simpl in Hiff.
          rewrite (lookup_insert_ne _ _ _ _ Hne) in Hiff. exact Hiff.
        * apply (bs_enq_input _ _ Hbs').
        * (* bs_in0_dom *)
          intros k0.
          pose proof (bs_in0_dom _ _ Hbs' k0) as Hiff. simpl in Hiff.
          destruct (decide (k = k0)) as [->|Hne].
          { rewrite lookup_insert_eq in Hiff. rewrite Hcp. split.
            - intros _. by left.
            - intros _. apply Hiff. by right. }
          rewrite (lookup_insert_ne _ _ _ _ Hne) in Hiff. exact Hiff.
        * (* bs_A1_iff *)
          intros k0.
          destruct (decide (k = k0)) as [->|Hne].
          { rewrite lookup_insert_eq. split.
            - intros [=].
            - (* RHS impossible: by bs_A1_iff on s', u' at k, need cp0'(k) = A1
                 but cp0'(k) = A2. *)
              intros HRHS.
              pose proof (bs_A1_iff _ _ Hbs' k0) as HA1'. simpl in HA1'.
              destruct HA1' as [_ HA1']. specialize (HA1' HRHS).
              rewrite HA1' in HA2'. discriminate. }
          rewrite (lookup_insert_ne _ _ _ _ Hne).
          apply (bs_A1_iff _ _ Hbs' k0).
        * (* bs_A_iff *)
          intros k0.
          destruct (decide (k = k0)) as [->|Hne].
          { rewrite lookup_insert_eq. split.
            - intros _. right. split; done.
            - intros _. done. }
          rewrite (lookup_insert_ne _ _ _ _ Hne).
          pose proof (bs_A_iff _ _ Hbs' k0) as Hiff. simpl in Hiff.
          rewrite (lookup_insert_ne cp k k0 A2 Hne) in Hiff. exact Hiff.
        * (* bs_A2_iff *)
          intros k0.
          destruct (decide (k = k0)) as [->|Hne].
          { rewrite Hcp lookup_insert_eq. split; intros [=]. }
          rewrite (lookup_insert_ne _ _ _ _ Hne).
          pose proof (bs_A2_iff _ _ Hbs' k0) as Hiff. simpl in Hiff.
          rewrite (lookup_insert_ne _ _ _ _ Hne) in Hiff. exact Hiff.
    - (* RET-DEQ:
        [s = (O, lt, ℓ, rv, cp)] with cp(k) = R2 and rv(k) = d;
        [s' = (O, lt, ℓ, rv, cp[k ↦ R3])]; labelled [(k, ARetDeq d)].
        We pick [u] so that [u] --ret(deq,d,k)→_AbsQ0 u'. *)
      destruct u' as [σ' in0' rv0' cp0'].
      pose proof (bs_R3_iff _ _ Hbs' k) as HR3'.
      rewrite /= lookup_insert_eq in HR3'.
      destruct HR3' as [HR3' _]. specialize (HR3' eq_refl).
      exists (AbsQ0State σ' in0' rv0' (<[k := R2]> cp0')),
             [(k, ARetDeq d)].
      split_and!; last first.
      + done.
      + eapply lts_steps_cons; last apply lts_steps_nil.
        replace cp0' with (<[k := R3]> (<[k := R2]> cp0')) at 2;
          last by rewrite insert_insert_eq (insert_id _ _ _ HR3').
        apply absq0_step_ret_deq.
        * by rewrite lookup_insert_eq.
        * rewrite -(bs_rv_agree _ _ Hbs' k) /=. done.
      + (* bs(s, u) *)
        split; simpl.
        * apply (bs_nodup _ _ Hbs').
        * apply (bs_completed_in _ _ Hbs').
        * apply (bs_seq_from_O _ _ Hbs').
        * apply (bs_linearization _ _ Hbs').
        * apply (bs_rv_agree _ _ Hbs').
        * intros k0.
          destruct (decide (k = k0)) as [->|Hne].
          { rewrite Hcp lookup_insert_eq. split; intros [=]. }
          rewrite (lookup_insert_ne _ _ _ _ Hne).
          pose proof (bs_R1_iff _ _ Hbs' k0) as Hiff. simpl in Hiff.
          rewrite (lookup_insert_ne _ _ _ _ Hne) in Hiff. exact Hiff.
        * intros k0.
          destruct (decide (k = k0)) as [->|Hne].
          { rewrite Hcp lookup_insert_eq. split; intros _; done. }
          rewrite (lookup_insert_ne _ _ _ _ Hne).
          pose proof (bs_R2_iff _ _ Hbs' k0) as Hiff. simpl in Hiff.
          rewrite (lookup_insert_ne _ _ _ _ Hne) in Hiff. exact Hiff.
        * intros k0.
          destruct (decide (k = k0)) as [->|Hne].
          { rewrite lookup_insert_eq. split.
            - intros Hcp_k. rewrite Hcp in Hcp_k. discriminate.
            - intros [=]. }
          rewrite (lookup_insert_ne _ _ _ _ Hne).
          pose proof (bs_R3_iff _ _ Hbs' k0) as Hiff. simpl in Hiff.
          rewrite (lookup_insert_ne _ _ _ _ Hne) in Hiff. exact Hiff.
        * intros k0 d0 f0. apply (bs_enq_input _ _ Hbs' k0 d0 f0).
        * intros k0.
          pose proof (bs_in0_dom _ _ Hbs' k0) as Hiff. simpl in Hiff.
          destruct (decide (k = k0)) as [->|Hne].
          { rewrite lookup_insert_eq in Hiff. rewrite Hcp. split.
            - intros Hsome. apply Hiff in Hsome as [[=]|[=]].
            - intros [[=]|[=]]. }
          rewrite !(lookup_insert_ne _ _ _ _ Hne) in Hiff. exact Hiff.
        * intros k0.
          destruct (decide (k = k0)) as [->|Hne].
          { rewrite lookup_insert_eq. split.
            - intros [=].
            - intros (_ & d0 & Hℓk & _).
              pose proof (bs_enq_input _ _ Hbs' _ _ _ Hℓk) as Hin0k.
              assert (is_Some (in0' !! k0)) as Hsome by (by eexists).
              apply (proj1 (bs_in0_dom _ _ Hbs' k0)) in Hsome as [Hcp_k|Hcp_k];
                simpl in Hcp_k; rewrite lookup_insert_eq in Hcp_k; discriminate. }
          rewrite (lookup_insert_ne _ _ _ _ Hne).
          apply (bs_A1_iff _ _ Hbs' k0).
        * intros k0.
          destruct (decide (k = k0)) as [->|Hne].
          { rewrite lookup_insert_eq. split.
            - intros [=].
            - intros [(d0 & Hℓk & _) | (_ & Hcp_k)].
              + pose proof (bs_enq_input _ _ Hbs' _ _ _ Hℓk) as Hin0k.
                assert (is_Some (in0' !! k0)) as Hsome by (by eexists).
                apply (proj1 (bs_in0_dom _ _ Hbs' k0)) in Hsome as [Hcp_k|Hcp_k];
                  simpl in Hcp_k; rewrite lookup_insert_eq in Hcp_k; discriminate.
              + rewrite Hcp in Hcp_k. discriminate. }
          rewrite (lookup_insert_ne _ _ _ _ Hne).
          pose proof (bs_A_iff _ _ Hbs' k0) as Hiff. simpl in Hiff.
          rewrite (lookup_insert_ne _ _ _ _ Hne) in Hiff. exact Hiff.
        * intros k0.
          destruct (decide (k = k0)) as [->|Hne].
          { rewrite Hcp lookup_insert_eq. split; intros [=]. }
          rewrite (lookup_insert_ne _ _ _ _ Hne).
          pose proof (bs_A2_iff _ _ Hbs' k0) as Hiff. simpl in Hiff.
          rewrite (lookup_insert_ne _ _ _ _ Hne) in Hiff. exact Hiff.
    - (* LIN-DEQ1: removes minimal enqueue [k'] from [O] and dequeues
        its value as [SOMEV d]. Under [bag_like.queue_model]'s
        head=oldest convention, the minimal enqueue sits at the head
        of [σ_u]. Take [σ_u = (k', d) :: σ'], [cp0_u(k) = R1], and
        [rv0_u(k) = None]; one AbsQ0 LIN-DEQ1 step (remove head)
        yields [u']. *)
      destruct u' as [σ' in0' rv0' cp0'].
      (* k ≠ k': [k] is the dequeue (cp = R1), [k'] is the enqueue
         (cp ∈ {A1, A2} by [absq_wf_ℓcp]). *)
      assert (k ≠ k') as Hk_ne_k'.
      { intros <-. apply (absq_wf_ℓcp _ _ Hwf) in Hℓ as [Hcp'|Hcp'];
          rewrite Hcp in Hcp'; discriminate. }
      (* k' ∈ O: from [k' ∈ absq_min O lt]. *)
      assert (k' ∈ O) as Hk'_O by (apply elem_of_filter in Hmin; tauto).
      (* k' ∉ σ'.*1: any key in σ' is in O' = O ∖ {k'}, so it can't be k'. *)
      assert (k' ∉ σ'.*1) as Hk'_notin.
      { intros Hk'_in.
        apply list_elem_of_fmap in Hk'_in as ([k'' d'] & Hk''_eq & Hkd_in).
        simpl in Hk''_eq. subst k''.
        destruct (bs_seq_from_O _ _ Hbs' _ _ Hkd_in) as (f0 & Hk0_O' & _).
        simpl in Hk0_O'. set_solver. }
      (* cp(k'): [A1] if [f = PEND] (via [absq_wf_PEND_O]) and [A2] if
         [f = COMP] (via [absq_wf_COMP]). Kept as a case split (rather
         than forcing [f = COMP]) since the fixed [bs_A1_iff] no longer
         rules out [f = PEND]. *)
      assert (cp !! k' = Some A1 ∨ cp !! k' = Some A2) as Hcp_k'.
      { destruct f as [|]; [left | right].
        - apply (absq_wf_PEND_O _ _ Hwf _ d); done.
        - by apply (absq_wf_COMP _ _ Hwf _ _ Hℓ). }
      (* rv(k) = None (by [absq_wf_rv] and [cp(k) = R1]). *)
      assert (rv !! k = None) as Hrv_k_none.
      { destruct (rv !! k) as [v|] eqn:Heq; last done.
        exfalso. specialize (absq_wf_rv _ _ Hwf k (mk_is_Some _ _ Heq))
          as [Hcp'|Hcp']; rewrite Hcp in Hcp'; discriminate. }
      (* From [bs_R2_iff s' u'] at [k]: [cp0' !! k = Some R2]. *)
      assert (cp0' !! k = Some R2) as Hcp0'_k_R2.
      { apply (bs_R2_iff _ _ Hbs' k). simpl. by rewrite lookup_insert_eq. }
      (* From [bs_rv_agree s' u'] at [k]: [rv0' !! k = Some (SOMEV d)]. *)
      assert (rv0' !! k = Some (SOMEV d)) as Hrv0'_k_d.
      { rewrite -(bs_rv_agree _ _ Hbs' k). simpl. by rewrite lookup_insert_eq. }
      exists (AbsQ0State ((k', d) :: σ') in0' (delete k rv0')
               (<[k := R1]> (delete k cp0'))),
             [(k, ALinDeq (SOMEV d))].
      split_and!; last first.
      + done.
      + eapply lts_steps_cons; last apply lts_steps_nil.
        replace cp0' with (<[k := R2]>(<[k := R1]>(delete k cp0'))) at 2; last first.
        { rewrite insert_insert_eq. by apply (insert_delete_id _ _ _ Hcp0'_k_R2). }
        replace rv0' with (<[k := SOMEV d]>(delete k rv0')) at 2;
          last by apply (insert_delete_id _ _ _ Hrv0'_k_d).
        eapply absq0_step_lin_deq1; [by rewrite lookup_insert_eq | done].
      + (* bs(s, u) *)
        split; simpl.
        * (* bs_nodup: ((k', d) :: σ').*1 = k' :: σ'.*1 NoDup since σ'.*1
             is NoDup and k' ∉ σ'.*1. *)
          apply NoDup_cons. split; [exact Hk'_notin | apply (bs_nodup _ _ Hbs')].
        * (* bs_completed_in *)
          intros k0 d0 Hk0_O Hℓk0.
          destruct (decide (k' = k0)) as [<-|Hne_k'k0].
          { rewrite Hℓk0 in Hℓ. inversion Hℓ; subst.
            apply elem_of_cons. by left. }
          assert (k0 ∈ O ∖ {[k']}) as Hk0_O' by set_solver.
          specialize (bs_completed_in _ _ Hbs' k0 d0 Hk0_O' Hℓk0) as Hd0_in.
          apply elem_of_cons. by right.
        * (* bs_seq_from_O *)
          intros k0 d0 Hkd0.
          apply elem_of_cons in Hkd0 as [Hkd0_d | Hkd0_σ'].
          { inversion Hkd0_d; subst k0 d0. exists f. split; done. }
          destruct (bs_seq_from_O _ _ Hbs' _ _ Hkd0_σ') as (f0 & Hk0_O' & Hℓk0).
          exists f0. split; last done. set_solver.
        * (* bs_linearization: under head=oldest, position 0 is [k'];
             positions ≥1 reindex into [σ']. The new edge direction
             [(k_j, k_i) ∉ lt for i<j] becomes:
             - i=0: forbids [(k_j, k') ∈ lt] for [k_j ∈ σ'.*1] —
               follows from [k']'s minimality.
             - i>0: reindex to [σ']'s [bs_linearization] on [s'.lt =
               absq_remove lt k']; lift back to [lt] using the fact
               that neither [ki] nor [kj] equals [k']. *)
          intros i j ki di kj dj Hij Hi Hj Hlt.
          destruct i as [|i'].
          { simpl in Hi. inversion Hi; subst ki di.
            destruct j as [|j']; first lia.
            simpl in Hj.
            apply list_elem_of_lookup_2 in Hj as Hkj_σ'.
            destruct (bs_seq_from_O _ _ Hbs' _ _ Hkj_σ') as (f' & Hkj_O' & _).
            simpl in Hkj_O'.
            assert (kj ∈ O) as Hkj_O by set_solver.
            apply elem_of_filter in Hmin as [Hmin_cond _].
            by apply (Hmin_cond kj Hkj_O). }
          destruct j as [|j']; first lia.
          simpl in Hi, Hj.
          assert (ki ≠ k') as Hki_ne_k'.
          { intros ->. apply Hk'_notin.
            apply list_elem_of_fmap. exists (k', di).
            split; first done. by eapply list_elem_of_lookup_2. }
          assert (kj ≠ k') as Hkj_ne_k'.
          { intros ->. apply Hk'_notin.
            apply list_elem_of_fmap. exists (k', dj).
            split; first done. by eapply list_elem_of_lookup_2. }
          apply (bs_linearization _ _ Hbs' i' j' ki di kj dj
                   ltac:(lia) Hi Hj).
          simpl. apply elem_of_filter. split; last exact Hlt.
          simpl. split; auto.
        * (* bs_rv_agree *)
          intros k0.
          destruct (decide (k = k0)) as [<-|Hne].
          { by rewrite lookup_delete_eq Hrv_k_none. }
          rewrite lookup_delete_ne //.
          pose proof (bs_rv_agree _ _ Hbs' k0) as Hag. simpl in Hag.
          rewrite (lookup_insert_ne _ _ _ _ Hne) in Hag. exact Hag.
        * (* bs_R1_iff *)
          intros k0.
          destruct (decide (k = k0)) as [<-|Hne].
          { rewrite lookup_insert_eq Hcp. tauto. }
          rewrite (lookup_insert_ne _ _ _ _ Hne).
          rewrite lookup_delete_ne //.
          pose proof (bs_R1_iff _ _ Hbs' k0) as Hiff. simpl in Hiff.
          rewrite (lookup_insert_ne _ _ _ _ Hne) in Hiff. exact Hiff.
        * (* bs_R2_iff *)
          intros k0.
          destruct (decide (k = k0)) as [<-|Hne].
          { rewrite lookup_insert_eq Hcp. split; intros [=]. }
          rewrite (lookup_insert_ne _ _ _ _ Hne).
          rewrite lookup_delete_ne //.
          pose proof (bs_R2_iff _ _ Hbs' k0) as Hiff. simpl in Hiff.
          rewrite (lookup_insert_ne _ _ _ _ Hne) in Hiff. exact Hiff.
        * (* bs_R3_iff *)
          intros k0.
          destruct (decide (k = k0)) as [<-|Hne].
          { rewrite lookup_insert_eq Hcp. split; intros [=]. }
          rewrite (lookup_insert_ne _ _ _ _ Hne).
          rewrite lookup_delete_ne //.
          pose proof (bs_R3_iff _ _ Hbs' k0) as Hiff. simpl in Hiff.
          rewrite (lookup_insert_ne _ _ _ _ Hne) in Hiff. exact Hiff.
        * (* bs_enq_input *)
          intros k0 d0 f0. apply (bs_enq_input _ _ Hbs' k0 d0 f0).
        * (* bs_in0_dom *)
          intros k0.
          pose proof (bs_in0_dom _ _ Hbs' k0) as Hiff. simpl in Hiff.
          destruct (decide (k = k0)) as [<-|Hne].
          { rewrite lookup_insert_eq in Hiff. rewrite Hcp.
            split.
            - intros Hsome. apply Hiff in Hsome as [[=]|[=]].
            - intros [[=]|[=]]. }
          rewrite (lookup_insert_ne _ _ _ _ Hne) in Hiff. exact Hiff.
        * (* bs_A1_iff *)
          intros k0.
          destruct (decide (k = k0)) as [<-|Hne].
          { rewrite lookup_insert_eq. split.
            - intros [=].
            - intros (_ & d_w & Hℓk & _).
              apply (absq_wf_ℓcp _ _ Hwf) in Hℓk as [Hcp'|Hcp'];
                rewrite Hcp in Hcp'; discriminate. }
          rewrite (lookup_insert_ne _ _ _ _ Hne).
          rewrite lookup_delete_ne //.
          pose proof (bs_A1_iff _ _ Hbs' k0) as Hiff. simpl in Hiff.
          rewrite Hiff. clear Hiff.
          split.
          { intros (Hk0_O' & d_w & Hℓk0 & Hkd_w_notσ').
            split. { set_solver. }
            exists d_w. split; first done.
            intros Hkd_w_cons.
            apply elem_of_cons in Hkd_w_cons as [Hin_kd|Hkd_w_σ']; last done.
            inversion Hin_kd; subst. set_solver. }
          intros (Hk0_O & d_w & Hℓk0 & Hkd_w_notcons).
          split.
          { assert (k0 ≠ k') as Hne_k'.
            { intros ->. apply Hkd_w_notcons.
              rewrite Hℓ in Hℓk0. inversion Hℓk0; subst.
              apply elem_of_cons. by left. }
            set_solver. }
          exists d_w.
          split; first done.
          intros Hkd_w_σ'. apply Hkd_w_notcons.
          apply elem_of_cons. by right.
        * (* bs_A_iff *)
          intros k0.
          destruct (decide (k = k0)) as [<-|Hne].
          { rewrite lookup_insert_eq. split.
            - intros [=].
            - intros [(d_w & Hℓk & _) | (_ & Hcp_k_A1)].
              + apply (absq_wf_ℓcp _ _ Hwf) in Hℓk as [Hcp'|Hcp'];
                  rewrite Hcp in Hcp'; discriminate.
              + rewrite Hcp in Hcp_k_A1. discriminate. }
          rewrite (lookup_insert_ne _ _ _ _ Hne).
          rewrite lookup_delete_ne //.
          pose proof (bs_A_iff _ _ Hbs' k0) as Hiff. simpl in Hiff.
          rewrite (lookup_insert_ne _ _ _ _ Hne) in Hiff.
          rewrite Hiff. clear Hiff.
          split.
          { intros [(d_w & Hℓk0 & Hkd_w_σ') | (HnotO' & Hcp_A1)].
            - left. exists d_w. split; first done.
              apply elem_of_cons. by right.
            - destruct (decide (k0 = k')) as [->|Hne_k'].
              + (* k0 = k'. f = PEND → first disjunct with (k', d) ∈ (k',d)::σ'.
                   f = COMP → cp(k') = A2 (absq_wf_COMP), contradicts Hcp_A1. *)
                destruct f as [|].
                * left. exists d. split; first done.
                  apply elem_of_cons. by left.
                * pose proof (absq_wf_COMP _ _ Hwf _ _ Hℓ) as Hcp_k'_A2.
                  rewrite Hcp_k'_A2 in Hcp_A1. discriminate.
              + right. split; last done. set_solver. }
          intros [(d_w & Hℓk0 & Hkd_w_in_cons) | (HnotO & Hcp_A1)].
          { (* (k0, d_w) ∈ (k', d) :: σ'. *)
            apply elem_of_cons in Hkd_w_in_cons as [Hkd_w_d|Hkd_w_σ'].
            - inversion Hkd_w_d. subst k0 d_w.
              (* (k0, d_w) = (k', d). f = PEND: cp(k') = A1 (absq_wf_PEND_O);
                 use second disjunct. f = COMP: ℓ(k') = (d, COMP) ≠ (d, PEND). *)
              destruct f as [|].
              + right. split. { set_solver. }
                by apply (absq_wf_PEND_O _ _ Hwf _ d).
              + rewrite Hℓ in Hℓk0. inversion Hℓk0.
            - left. exists d_w. split; done. }
          right. split; last done. set_solver.
        * (* bs_A2_iff *)
          intros k0.
          destruct (decide (k = k0)) as [<-|Hne].
          { rewrite lookup_insert_eq Hcp. split; intros [=]. }
          rewrite (lookup_insert_ne _ _ _ _ Hne).
          rewrite lookup_delete_ne //.
          pose proof (bs_A2_iff _ _ Hbs' k0) as Hiff. simpl in Hiff.
          rewrite (lookup_insert_ne _ _ _ _ Hne) in Hiff. exact Hiff.
    - (* LIN-DEQ2: dequeues [NONEV]; requires AbsQ's [O] to be all-pending.
        Pick [σ_u = ⟨⟩]; take LIN-DEQ2 first (σ stays ⟨⟩), then LIN-ENQ
        steps for each value in [σ_{u'}] in order (head=oldest: each
        LIN-ENQ appends to σ, no reverse needed), each using the unique
        key [k_v] (by data independence) with [ℓ(k_v) = (v, PEND)]. *)
      destruct u' as [σ' in0' rv0' cp0'].
      assert (cp !! k = Some R1) as Hcp_k_R1 by exact Hcp.
      assert (rv !! k = None) as Hrv_k_none.
      { destruct (rv !! k) as [v|] eqn:Heq; last done.
        exfalso. specialize (absq_wf_rv _ _ Hwf k (mk_is_Some _ _ Heq))
          as [Hcp'|Hcp']; rewrite Hcp in Hcp'; discriminate. }
      assert (k ∉ O) as Hk_notO.
      { intros Hk_O. destruct (HallPend _ Hk_O) as (d_k & Hℓ_k).
        apply (absq_wf_ℓcp _ _ Hwf) in Hℓ_k as [Hcp'|Hcp'];
          rewrite Hcp in Hcp'; discriminate. }
      assert (cp0' !! k = Some R2) as Hcp0'_R2.
      { apply (bs_R2_iff _ _ Hbs' k). simpl. by rewrite lookup_insert_eq. }
      assert (rv0' !! k = Some NONEV) as Hrv0'_empty.
      { rewrite -(bs_rv_agree _ _ Hbs' k). simpl. by rewrite lookup_insert_eq. }
      pose proof (bs_nodup _ _ Hbs') as Hnd_σ'_keys.
      simpl in Hnd_σ'_keys.
      (* k ∉ σ'.*1: any key in σ' is in O (via bs_seq_from_O), k ∉ O. *)
      assert (k ∉ σ'.*1) as Hk_notin_σ'.
      { intros Hk_in.
        apply list_elem_of_fmap in Hk_in as ([k'' d'] & Hk''_eq & Hkd_in).
        simpl in Hk''_eq. subst k''.
        destruct (bs_seq_from_O _ _ Hbs' _ _ Hkd_in) as (f0 & Hk_O & _).
        simpl in Hk_O. by apply Hk_notO. }
      (* Hkeys_props: for each (k_v, v) ∈ σ', ℓ(k_v) = (v, PEND) ∧ ... *)
      assert (Hkeys_props : Forall (λ kv : positive * val,
        ℓ !! kv.1 = Some (kv.2, PEND) ∧
        kv.1 ∈ O ∧
        cp !! kv.1 = Some A1 ∧
        cp0' !! kv.1 = Some A) σ').
      { apply Forall_forall. intros [k_v v] Hkv_σ'.
        destruct (bs_seq_from_O _ _ Hbs' _ _ Hkv_σ')
          as (f_v & Hk_v_O & Hℓ'k_v).
        simpl in Hk_v_O, Hℓ'k_v.
        destruct (HallPend k_v Hk_v_O) as (d_v & Hℓk_v_PEND).
        assert (k_v ≠ k) as Hk_v_ne_k
          by (intros ->; by apply Hk_notO).
        rewrite Hℓ'k_v in Hℓk_v_PEND.
        injection Hℓk_v_PEND as _ Hflag.
        subst f_v.
        assert (cp0' !! k_v = Some A) as Hcp0'_A_v.
        { apply (bs_A_iff _ _ Hbs' k_v). left. exists v.
          split; last exact Hkv_σ'. simpl. exact Hℓ'k_v. }
        assert (cp !! k_v = Some A1) as Hcp_A1_v.
        { destruct (absq_wf_ℓcp _ _ Hwf _ _ _ Hℓ'k_v) as [|Hcp_A2];
            first done.
          exfalso.
          assert (cp0' !! k_v = Some A2) as Hcp0'_A2.
          { apply (bs_A2_iff _ _ Hbs' k_v). simpl.
            rewrite (lookup_insert_ne _ k k_v _
                     (λ H, Hk_v_ne_k (eq_sym H))).
            exact Hcp_A2. }
          rewrite Hcp0'_A_v in Hcp0'_A2. discriminate. }
        simpl. done. }
      assert (Hkv_props : ∀ k_v v,
        (k_v, v) ∈ σ' →
        ℓ !! k_v = Some (v, PEND) ∧ k_v ∈ O ∧
        cp !! k_v = Some A1 ∧ cp0' !! k_v = Some A).
      { rewrite Forall_forall in Hkeys_props.
        intros k_v v Hkv. by apply (Hkeys_props (k_v, v) Hkv). }
      exists (AbsQ0State [] in0' (delete k rv0')
              (<[k := R1]>(insert_all A1 (delete k cp0') σ'.*1))),
             ((k, ALinDeq NONEV) ::
              map (λ kv, (kv.1, ALinEnq kv.2)) σ').
      split_and!; last first.
      + (* Label projection: only [(k, ALinDeq NONEV)] is observable. *)
        unfold project_labels.
        rewrite filter_cons_True; last done.
        rewrite filter_nil.
        rewrite filter_cons_True; last done.
        f_equal.
        symmetry.
        generalize σ'. clear. intros l.
        induction l as [|[k0 v0] l IH]; simpl; first done.
        rewrite filter_cons_False; [|by intros []]. exact IH.
      + (* AbsQ0 trace: LIN-DEQ2 + LIN-ENQ tail (in σ' order). *)
        eapply lts_steps_cons.
        { apply absq0_step_lin_deq2; first done.
          by rewrite lookup_insert_eq. }
        rewrite insert_insert_eq.
        assert (AbsQ0State σ' in0' rv0' cp0' =
                 AbsQ0State σ'
                   in0'
                   (<[k := NONEV]>(delete k rv0'))
                   (insert_all A
                     (<[k := R2]>(insert_all A1 (delete k cp0') σ'.*1))
                     σ'.*1)) as Heq.
        { f_equal.
          - symmetry. by apply (insert_delete_id _ _ _ Hrv0'_empty).
          - apply map_eq. intros x.
            destruct (decide (k = x)) as [<-|Hne].
            { rewrite insert_all_lookup_notin //.
              by rewrite lookup_insert_eq. }
            destruct (decide (x ∈ σ'.*1)) as [Hx_in|Hx_notin].
            { rewrite insert_all_lookup_in //.
              apply list_elem_of_fmap in Hx_in as ([x' v] & -> & Hxv).
              destruct (Hkv_props _ _ Hxv) as (_ & _ & _ & Hcp0'_A_x).
              done. }
            rewrite insert_all_lookup_notin //.
            rewrite (lookup_insert_ne _ _ _ _ Hne).
            rewrite insert_all_lookup_notin //.
            by rewrite lookup_delete_ne. }
        rewrite Heq.
        apply absq0_lin_enq_seq_steps; first exact Hnd_σ'_keys.
        (* Build Forall over σ' from Hkeys_props. *)
        rewrite Forall_forall. intros [k_i v_i] Hkv_σ'.
        destruct (Hkv_props _ _ Hkv_σ')
          as (Hℓ_k_i & Hk_i_O & Hcp_k_i_A1 & Hcp0'_A_k_i).
        assert (k_i ∈ σ'.*1) as Hk_i_σ'
          by (apply list_elem_of_fmap; by exists (k_i, v_i)).
        assert (k_i ≠ k) as Hk_i_ne_k
          by (intros ->; by apply Hk_notin_σ').
        simpl. split_and!.
        * rewrite (lookup_insert_ne _ k k_i _
                   (λ H, Hk_i_ne_k (eq_sym H))).
          by apply insert_all_lookup_in.
        * apply (bs_enq_input _ _ Hbs' k_i v_i PEND). exact Hℓ_k_i.
        * by eapply (absq_wf_valid_value _ _ Hwf _ _ PEND).
      + (* bs(s, u) *)
        split; simpl.
        * (* bs_nodup: NoDup [] *) constructor.
        * (* bs_completed_in: vacuous via HallPend (all PEND, not COMP) *)
          intros k0 d0 Hk0_O Hℓk0.
          destruct (HallPend _ Hk0_O) as (d_k0 & Hℓk0_PEND).
          rewrite Hℓk0 in Hℓk0_PEND. inversion Hℓk0_PEND.
        * (* bs_seq_from_O: vacuous (σ_u = []) *)
          intros k0 d0 Hkd0. exfalso. by apply elem_of_nil in Hkd0.
        * (* bs_linearization: vacuous (σ_u = [], no positions) *)
          intros i j ki di kj dj _ Hi _ _. by rewrite lookup_nil in Hi.
        * (* bs_rv_agree *)
          intros k0.
          destruct (decide (k = k0)) as [<-|Hne].
          { by rewrite lookup_delete_eq Hrv_k_none. }
          rewrite lookup_delete_ne //.
          pose proof (bs_rv_agree _ _ Hbs' k0) as Hag. simpl in Hag.
          rewrite (lookup_insert_ne _ _ _ _ Hne) in Hag. exact Hag.
        * (* bs_R1_iff *)
          intros k0.
          destruct (decide (k = k0)) as [<-|Hne].
          { rewrite Hcp_k_R1 lookup_insert_eq. tauto. }
          destruct (decide (k0 ∈ σ'.*1)) as [Hk0_ks|Hk0_not_ks].
          { pose proof Hk0_ks as Hk0_ks_ex.
            apply list_elem_of_fmap in Hk0_ks_ex as ([k0' v] & -> & Hkv).
            destruct (Hkv_props _ _ Hkv) as (_ & _ & Hcp_A1 & _).
            rewrite Hcp_A1.
            rewrite (lookup_insert_ne _ _ _ _ Hne).
            rewrite (insert_all_lookup_in _ _ _ _ Hk0_ks).
            split; intros Heq; inversion Heq. }
          rewrite (lookup_insert_ne _ _ _ _ Hne).
          rewrite insert_all_lookup_notin // lookup_delete_ne //.
          pose proof (bs_R1_iff _ _ Hbs' k0) as Hiff. simpl in Hiff.
          rewrite (lookup_insert_ne _ _ _ _ Hne) in Hiff. exact Hiff.
        * (* bs_R2_iff *)
          intros k0.
          destruct (decide (k = k0)) as [<-|Hne].
          { rewrite Hcp_k_R1 lookup_insert_eq.
            split; intros [=]. }
          destruct (decide (k0 ∈ σ'.*1)) as [Hk0_ks|Hk0_not_ks].
          { pose proof Hk0_ks as Hk0_ks_ex.
            apply list_elem_of_fmap in Hk0_ks_ex as ([k0' v] & -> & Hkv).
            destruct (Hkv_props _ _ Hkv) as (_ & _ & Hcp_A1 & _).
            rewrite Hcp_A1.
            rewrite (lookup_insert_ne _ _ _ _ Hne).
            rewrite (insert_all_lookup_in _ _ _ _ Hk0_ks).
            split; intros Heq; inversion Heq. }
          rewrite (lookup_insert_ne _ _ _ _ Hne).
          rewrite insert_all_lookup_notin // lookup_delete_ne //.
          pose proof (bs_R2_iff _ _ Hbs' k0) as Hiff. simpl in Hiff.
          rewrite (lookup_insert_ne _ _ _ _ Hne) in Hiff. exact Hiff.
        * (* bs_R3_iff *)
          intros k0.
          destruct (decide (k = k0)) as [<-|Hne].
          { rewrite Hcp_k_R1 lookup_insert_eq.
            split; intros [=]. }
          destruct (decide (k0 ∈ σ'.*1)) as [Hk0_ks|Hk0_not_ks].
          { pose proof Hk0_ks as Hk0_ks_ex.
            apply list_elem_of_fmap in Hk0_ks_ex as ([k0' v] & -> & Hkv).
            destruct (Hkv_props _ _ Hkv) as (_ & _ & Hcp_A1 & _).
            rewrite Hcp_A1.
            rewrite (lookup_insert_ne _ _ _ _ Hne).
            rewrite (insert_all_lookup_in _ _ _ _ Hk0_ks).
            split; intros Heq; inversion Heq. }
          rewrite (lookup_insert_ne _ _ _ _ Hne).
          rewrite insert_all_lookup_notin // lookup_delete_ne //.
          pose proof (bs_R3_iff _ _ Hbs' k0) as Hiff. simpl in Hiff.
          rewrite (lookup_insert_ne _ _ _ _ Hne) in Hiff. exact Hiff.
        * (* bs_enq_input *)
          intros k0 d0 f0 Hℓk0.
          destruct (decide (k = k0)) as [<-|Hne].
          { exfalso. apply (absq_wf_ℓcp _ _ Hwf) in Hℓk0
              as [Hcp'|Hcp']; rewrite Hcp in Hcp'; discriminate. }
          by apply (bs_enq_input _ _ Hbs' k0 d0 f0).
        * (* bs_in0_dom *)
          intros k0.
          pose proof (bs_in0_dom _ _ Hbs' k0) as Hiff. simpl in Hiff.
          destruct (decide (k = k0)) as [<-|Hne].
          { rewrite lookup_insert_eq in Hiff.
            rewrite Hcp.
            split.
            { intros Hsome. apply Hiff in Hsome as [[=]|[=]]. }
            intros [[=]|[=]]. }
          rewrite (lookup_insert_ne _ _ _ _ Hne) in Hiff. exact Hiff.
        * (* bs_A1_iff *)
          intros k0.
          destruct (decide (k = k0)) as [<-|Hne].
          { rewrite (lookup_insert_eq).
            split.
            { intros [=]. }
            intros (_ & d_w & Hℓk & _).
            apply (absq_wf_ℓcp _ _ Hwf) in Hℓk
              as [Hcp'|Hcp']; rewrite Hcp in Hcp'; discriminate. }
          destruct (decide (k0 ∈ σ'.*1)) as [Hk0_ks|Hk0_not_ks].
          { pose proof Hk0_ks as Hk0_ks_ex.
            apply list_elem_of_fmap in Hk0_ks_ex as ([k0' v] & -> & Hkv).
            destruct (Hkv_props _ _ Hkv) as (Hℓk0 & Hk0_O & _ & _).
            rewrite (lookup_insert_ne _ _ _ _ Hne).
            rewrite (insert_all_lookup_in _ _ _ _ Hk0_ks).
            split.
            { intros _. split; first done. exists v. split; first done.
              by intros []%elem_of_nil. }
            done. }
          rewrite (lookup_insert_ne _ _ _ _ Hne).
          rewrite insert_all_lookup_notin // lookup_delete_ne //.
          pose proof (bs_A1_iff _ _ Hbs' k0) as Hiff. simpl in Hiff.
          rewrite Hiff. clear Hiff.
          split.
          { intros (Hk0_O & d_w & Hℓk0 & Hkd_w_σ').
            split; first done.
            exists d_w. split; first done.
            by intros []%elem_of_nil. }
          intros (Hk0_O & d_w & Hℓk0 & _).
          split; first done.
          exists d_w. split; first done.
          intros Hkd_w_σ'. apply Hk0_not_ks.
          apply list_elem_of_fmap. by exists (k0, d_w).
        * (* bs_A_iff *)
          intros k0.
          destruct (decide (k = k0)) as [<-|Hne].
          { rewrite (lookup_insert_eq).
            split.
            { intros [=]. }
            intros [(d_w & Hℓk & _) | (_ & Hcp_A1)].
            { apply (absq_wf_ℓcp _ _ Hwf) in Hℓk
                as [Hcp'|Hcp']; rewrite Hcp in Hcp'; discriminate. }
            rewrite Hcp in Hcp_A1. discriminate. }
          destruct (decide (k0 ∈ σ'.*1)) as [Hk0_ks|Hk0_not_ks].
          { pose proof Hk0_ks as Hk0_ks_ex.
            apply list_elem_of_fmap in Hk0_ks_ex as ([k0' v] & -> & Hkv).
            destruct (Hkv_props _ _ Hkv) as (_ & Hk0_O & _ & _).
            rewrite (lookup_insert_ne _ _ _ _ Hne).
            rewrite (insert_all_lookup_in _ _ _ _ Hk0_ks).
            split.
            { intros [=]. }
            intros [(d_w & _ & []%elem_of_nil) | (HnotO & _)].
            exfalso. by apply HnotO. }
          rewrite (lookup_insert_ne _ _ _ _ Hne).
          rewrite insert_all_lookup_notin // lookup_delete_ne //.
          pose proof (bs_A_iff _ _ Hbs' k0) as Hiff. simpl in Hiff.
          rewrite (lookup_insert_ne _ _ _ _ Hne) in Hiff.
          rewrite Hiff. clear Hiff.
          split.
          { intros [(d_w & Hℓk0 & Hkd_w_σ') | (HnotO & Hcp_A1)].
            { exfalso. apply Hk0_not_ks.
              apply list_elem_of_fmap. by exists (k0, d_w). }
            right. split; done. }
          intros [(d_w & _ & []%elem_of_nil) | (HnotO & Hcp_A1)].
          right. split; done.
        * (* bs_A2_iff *)
          intros k0.
          destruct (decide (k = k0)) as [<-|Hne].
          { rewrite Hcp_k_R1 lookup_insert_eq.
            split; intros [=]. }
          destruct (decide (k0 ∈ σ'.*1)) as [Hk0_ks|Hk0_not_ks].
          { pose proof Hk0_ks as Hk0_ks_ex.
            apply list_elem_of_fmap in Hk0_ks_ex as ([k0' v] & -> & Hkv).
            destruct (Hkv_props _ _ Hkv) as (_ & _ & Hcp_A1 & _).
            rewrite Hcp_A1.
            rewrite (lookup_insert_ne _ _ _ _ Hne).
            rewrite (insert_all_lookup_in _ _ _ _ Hk0_ks).
            split; intros Heq; inversion Heq. }
          rewrite (lookup_insert_ne _ _ _ _ Hne).
          rewrite insert_all_lookup_notin // lookup_delete_ne //.
          pose proof (bs_A2_iff _ _ Hbs' k0) as Hiff. simpl in Hiff.
          rewrite (lookup_insert_ne _ _ _ _ Hne) in Hiff. exact Hiff.
  Qed.

  (** Forward-simulation helper: given [bs s u] and a step [s → s'],
    construct some [u'] with [bs s' u']. Unlike [bs_step], the [u']
    here need not be reachable from [u] in [AbsQ0]; we only need its
    existence so that [bs_total] can establish [bs] at every reachable
    [AbsQ] state. *)
  Lemma bs_fwd_step s l s' u :
    absq_wf valid_value s → absq_step rme valid_value s l s' → bs s u → ∃ u', bs s' u'.
  Proof.
    intros Hwf Hstep Hbs.
    inversion Hstep as
      [ O lt ℓ rv cp k d Hfresh Hdub
      | O lt ℓ rv cp k Hfresh
      | O lt ℓ rv cp k d Hcp HkO Hℓeq
      | O lt ℓ rv cp k Hcp HkNotO
      | O lt ℓ rv cp k d Hcp Hrveq
      | O lt ℓ rv cp k k' d f Hcp Hmin Hℓeq
      | O lt ℓ rv cp k Hrme_eq Hcp HallPend ];
      subst; destruct u as [σ in0 rv0 cp0]; simpl in *.
    - (* CALL-ENQ: pick u' = (σ, <[k:=d]>in0, rv0, <[k:=A1]>cp0). *)
      exists (AbsQ0State σ (<[k := d]> in0) rv0 (<[k := A1]> cp0)).
      assert (ℓ !! k = None) as Hℓk_none.
      { apply not_elem_of_dom. intros Hk_dom.
        apply (absq_wf_dom _ _ Hwf) in Hk_dom. by apply Hfresh. }
      assert (k ∉ σ.*1) as Hk_notin_σ.
      { intros Hk_in.
        apply list_elem_of_fmap in Hk_in as ([k'' d''] & Hk_eq & Hkd_in).
        simpl in Hk_eq. subst k''.
        destruct (bs_seq_from_O _ _ Hbs _ _ Hkd_in) as (f0 & _ & Hℓk0).
        by rewrite Hℓk_none in Hℓk0. }
      split; simpl.
      + apply (bs_nodup _ _ Hbs).
      + (* bs_completed_in *)
        intros k0 d0 Hk0_O Hℓ'.
        destruct (decide (k = k0)) as [<-|Hne].
        { rewrite lookup_insert_eq in Hℓ'. discriminate. }
        rewrite (lookup_insert_ne _ _ _ _ Hne) in Hℓ'.
        apply (bs_completed_in _ _ Hbs k0 d0); last done. set_solver.
      + (* bs_seq_from_O *)
        intros k0 d0 Hkd0.
        destruct (bs_seq_from_O _ _ Hbs _ _ Hkd0) as (f0 & Hk0_O & Hℓk0).
        exists f0. split; first set_solver.
        destruct (decide (k = k0)) as [<-|Hne]; first by rewrite Hℓk_none in Hℓk0.
        by rewrite (lookup_insert_ne _ _ _ _ Hne).
      + (* bs_linearization (new direction (k_j, k_i) ∉ lt for i<j):
           the new edges from CALL-ENQ have shape (k_c, k) where
           k_c ∈ COMP. So (k_j, k_i) ∈ new edges forces k_i = k. But
           k ∉ σ.*1, contradiction. *)
        intros i j ki di kj dj Hij Hi Hj Hlt.
        apply elem_of_union in Hlt as [Hlt_old|Hnew]; last first.
        { exfalso. apply elem_of_map in Hnew as (k' & Heq & _).
          inversion Heq; subst. apply Hk_notin_σ.
          apply list_elem_of_fmap. exists (k, di). split; first done.
          by eapply list_elem_of_lookup_2. }
        apply (bs_linearization _ _ Hbs i j ki di kj dj Hij Hi Hj).
        exact Hlt_old.
      + apply (bs_rv_agree _ _ Hbs).
      + (* bs_R1_iff *)
        intros k0. destruct (decide (k = k0)) as [<-|Hne].
        { rewrite !lookup_insert_eq. split; intros [=]. }
        rewrite !(lookup_insert_ne _ _ _ _ Hne). apply (bs_R1_iff _ _ Hbs).
      + intros k0. destruct (decide (k = k0)) as [<-|Hne].
        { rewrite !lookup_insert_eq. split; intros [=]. }
        rewrite !(lookup_insert_ne _ _ _ _ Hne). apply (bs_R2_iff _ _ Hbs).
      + intros k0. destruct (decide (k = k0)) as [<-|Hne].
        { rewrite !lookup_insert_eq. split; intros [=]. }
        rewrite !(lookup_insert_ne _ _ _ _ Hne). apply (bs_R3_iff _ _ Hbs).
      + (* bs_enq_input *)
        intros k0 d0 f0 Hℓ'.
        destruct (decide (k = k0)) as [<-|Hne].
        { rewrite lookup_insert_eq in Hℓ'. inversion Hℓ'; subst.
          by rewrite lookup_insert_eq. }
        rewrite (lookup_insert_ne _ _ _ _ Hne) in Hℓ'.
        rewrite (lookup_insert_ne _ _ _ _ Hne). by apply (bs_enq_input _ _ Hbs) in Hℓ'.
      + (* bs_in0_dom *)
        intros k0. destruct (decide (k = k0)) as [<-|Hne].
        { rewrite !lookup_insert_eq. split; [by left|by eexists]. }
        rewrite !(lookup_insert_ne _ _ _ _ Hne). apply (bs_in0_dom _ _ Hbs).
      + (* bs_A1_iff *)
        intros k0. destruct (decide (k = k0)) as [<-|Hne].
        { rewrite !lookup_insert_eq. split.
          - intros _. split; first set_solver. exists d. split; first done.
            intros Hkd_σ. apply Hk_notin_σ.
            apply list_elem_of_fmap. by exists (k, d).
          - done. }
        rewrite !(lookup_insert_ne _ _ _ _ Hne).
        pose proof (bs_A1_iff _ _ Hbs k0) as Hiff.
        split.
        { intros HA1. apply Hiff in HA1 as (Hk0_O & ? & ? & ?).
          split; first set_solver. by eexists. }
        intros (Hk0_O & ? & ? & ?). apply Hiff. split; first set_solver. by eexists.
      + (* bs_A_iff *)
        intros k0. destruct (decide (k = k0)) as [<-|Hne].
        { rewrite !lookup_insert_eq. split.
          - intros [=].
          - intros [(d_w & Hinsert & Hkd_w_σ) | (HnotO & _)].
            { exfalso. apply Hk_notin_σ.
              apply list_elem_of_fmap. by exists (k, d_w). }
            set_solver. }
        rewrite !(lookup_insert_ne _ _ _ _ Hne).
        pose proof (bs_A_iff _ _ Hbs k0) as Hiff.
        split.
        { intros HA. apply Hiff in HA as [(d_w & Hℓk0 & Hkd_w_σ) | (HnotO & Hcp_A1)].
          - left. by exists d_w.
          - right. split; last done. set_solver. }
        intros [(d_w & Hℓk0 & Hkd_w_σ) | (HnotO & Hcp_A1)]; apply Hiff.
        { left. by exists d_w. }
        right. split; last done. set_solver.
      + (* bs_A2_iff *)
        intros k0. destruct (decide (k = k0)) as [<-|Hne].
        { rewrite !lookup_insert_eq. split; intros [=]. }
        rewrite !(lookup_insert_ne _ _ _ _ Hne). apply (bs_A2_iff _ _ Hbs).
    - (* CALL-DEQ: u' = (σ, in0, rv0, <[k:=R1]>cp0). *)
      exists (AbsQ0State σ in0 rv0 (<[k := R1]> cp0)).
      assert (ℓ !! k = None) as Hℓk_none.
      { apply not_elem_of_dom. intros Hk_dom.
        apply (absq_wf_dom _ _ Hwf) in Hk_dom. by apply Hfresh. }
      assert (cp0 !! k = None) as Hcp0k_none.
      { destruct (cp0 !! k) as [c|] eqn:Hc; last done. exfalso.
        destruct c.
        - apply (bs_A1_iff _ _ Hbs) in Hc as (_ & d_w & Hℓk & _).
          by rewrite Hℓk_none in Hℓk.
        - apply (bs_A_iff _ _ Hbs) in Hc as [(d_w & Hℓk & _) | (_ & Hcp_A1)].
          + by rewrite Hℓk_none in Hℓk.
          + apply not_elem_of_dom in Hfresh. by rewrite Hcp_A1 in Hfresh.
        - apply (bs_A2_iff _ _ Hbs) in Hc.
          apply not_elem_of_dom in Hfresh. by rewrite Hc in Hfresh.
        - apply (bs_R1_iff _ _ Hbs) in Hc.
          apply not_elem_of_dom in Hfresh. by rewrite Hc in Hfresh.
        - apply (bs_R2_iff _ _ Hbs) in Hc.
          apply not_elem_of_dom in Hfresh. by rewrite Hc in Hfresh.
        - apply (bs_R3_iff _ _ Hbs) in Hc.
          apply not_elem_of_dom in Hfresh. by rewrite Hc in Hfresh. }
      split; simpl.
      + apply (bs_nodup _ _ Hbs).
      + apply (bs_completed_in _ _ Hbs).
      + apply (bs_seq_from_O _ _ Hbs).
      + apply (bs_linearization _ _ Hbs).
      + apply (bs_rv_agree _ _ Hbs).
      + intros k0. destruct (decide (k = k0)) as [<-|Hne].
        { by rewrite !lookup_insert_eq. }
        rewrite !(lookup_insert_ne _ _ _ _ Hne). apply (bs_R1_iff _ _ Hbs).
      + intros k0. destruct (decide (k = k0)) as [<-|Hne].
        { rewrite !lookup_insert_eq. split; intros [=]. }
        rewrite !(lookup_insert_ne _ _ _ _ Hne). apply (bs_R2_iff _ _ Hbs).
      + intros k0. destruct (decide (k = k0)) as [<-|Hne].
        { rewrite !lookup_insert_eq. split; intros [=]. }
        rewrite !(lookup_insert_ne _ _ _ _ Hne). apply (bs_R3_iff _ _ Hbs).
      + apply (bs_enq_input _ _ Hbs).
      + intros k0. destruct (decide (k = k0)) as [<-|Hne].
        { rewrite !lookup_insert_eq. split.
          - intros Hsome. apply (bs_in0_dom _ _ Hbs) in Hsome as [Hcp_A|Hcp_A];
              apply not_elem_of_dom in Hfresh; rewrite Hcp_A in Hfresh; discriminate.
          - intros [[=]|[=]]. }
        rewrite !(lookup_insert_ne _ _ _ _ Hne). apply (bs_in0_dom _ _ Hbs).
      + intros k0. destruct (decide (k = k0)) as [<-|Hne].
        { rewrite !lookup_insert_eq. split.
          - intros [=].
          - intros (_ & ? & Hℓk & _). by rewrite Hℓk_none in Hℓk. }
        rewrite !(lookup_insert_ne _ _ _ _ Hne). apply (bs_A1_iff _ _ Hbs).
      + intros k0. destruct (decide (k = k0)) as [<-|Hne].
        { rewrite !lookup_insert_eq. split.
          - intros [=].
          - intros [(? & Hℓk & _) | (_ & [=])]. by rewrite Hℓk_none in Hℓk. }
        rewrite !(lookup_insert_ne _ _ _ _ Hne). apply (bs_A_iff _ _ Hbs).
      + intros k0. destruct (decide (k = k0)) as [<-|Hne].
        { rewrite !lookup_insert_eq. split; intros [=]. }
        rewrite !(lookup_insert_ne _ _ _ _ Hne). apply (bs_A2_iff _ _ Hbs).
    - (* RET-ENQ1: cp(k) = A1, k ∈ O, ℓ(k) = (d, PEND).
         Case A: d ∈ σ, cp0(k) = A. u' same σ, flip cp0(k) to A2.
         Case B: d ∉ σ, cp0(k) = A1. u' prepend d to σ, flip cp0(k) to A2. *)
      assert (cp0 !! k = Some A1 ∨ cp0 !! k = Some A) as Hcp0_k.
      { destruct (decide ((k, d) ∈ σ)) as [Hd|Hd]; [right|left].
        - apply (bs_A_iff _ _ Hbs k). left. exists d. by split.
        - apply (bs_A1_iff _ _ Hbs k). split; first done.
          exists d. by split. }
      destruct (decide ((k, d) ∈ σ)) as [Hd_in|Hd_notin].
      + (* Case A: (k, d) ∈ σ *)
        exists (AbsQ0State σ in0 rv0 (<[k := A2]> cp0)).
        split; simpl.
        * apply (bs_nodup _ _ Hbs).
        * intros k0 d0 Hk0_O Hℓ'.
          destruct (decide (k = k0)) as [<-|Hne].
          { rewrite lookup_insert_eq in Hℓ'. inversion Hℓ'; subst. done. }
          rewrite (lookup_insert_ne _ _ _ _ Hne) in Hℓ'.
          by apply (bs_completed_in _ _ Hbs k0 d0).
        * intros k0 d0 Hkd0.
          destruct (bs_seq_from_O _ _ Hbs _ _ Hkd0) as (f0 & Hk0_O & Hℓk0).
          destruct (decide (k = k0)) as [<-|Hne].
          { rewrite Hℓeq in Hℓk0. inversion Hℓk0; subst d0 f0.
            exists COMP. split; first done. by rewrite lookup_insert_eq. }
          exists f0. split; first done. by rewrite (lookup_insert_ne _ _ _ _ Hne).
        * intros i j ki di kj dj Hij Hi Hj Hlt.
          apply (bs_linearization _ _ Hbs i j ki di kj dj Hij Hi Hj). exact Hlt.
        * apply (bs_rv_agree _ _ Hbs).
        * intros k0. destruct (decide (k = k0)) as [<-|Hne].
          { rewrite !lookup_insert_eq. split; intros [=]. }
          rewrite !(lookup_insert_ne _ _ _ _ Hne). apply (bs_R1_iff _ _ Hbs).
        * intros k0. destruct (decide (k = k0)) as [<-|Hne].
          { rewrite !lookup_insert_eq. split; intros [=]. }
          rewrite !(lookup_insert_ne _ _ _ _ Hne). apply (bs_R2_iff _ _ Hbs).
        * intros k0. destruct (decide (k = k0)) as [<-|Hne].
          { rewrite !lookup_insert_eq. split; intros [=]. }
          rewrite !(lookup_insert_ne _ _ _ _ Hne). apply (bs_R3_iff _ _ Hbs).
        * intros k0 d0 f0 Hℓ'.
          destruct (decide (k = k0)) as [<-|Hne].
          { rewrite lookup_insert_eq in Hℓ'. inversion Hℓ'; subst.
            apply (bs_enq_input _ _ Hbs _ _ PEND Hℓeq). }
          rewrite (lookup_insert_ne _ _ _ _ Hne) in Hℓ'.
          by apply (bs_enq_input _ _ Hbs) in Hℓ'.
        * intros k0. destruct (decide (k = k0)) as [<-|Hne].
          { rewrite !lookup_insert_eq. split.
            - intros _. by right.
            - intros _. apply (bs_in0_dom _ _ Hbs). by left. }
          rewrite !(lookup_insert_ne _ _ _ _ Hne). apply (bs_in0_dom _ _ Hbs).
        * intros k0. destruct (decide (k = k0)) as [<-|Hne].
          { rewrite !lookup_insert_eq. split.
            - intros [=].
            - intros (_ & ? & [=] & _). }
          rewrite !(lookup_insert_ne _ _ _ _ Hne). apply (bs_A1_iff _ _ Hbs).
        * intros k0. destruct (decide (k = k0)) as [<-|Hne].
          { rewrite !lookup_insert_eq. split.
            - intros [=].
            - intros [(? & [=] & _) | (? & [=])]. }
          rewrite !(lookup_insert_ne _ _ _ _ Hne). apply (bs_A_iff _ _ Hbs).
        * intros k0. destruct (decide (k = k0)) as [<-|Hne].
          { rewrite !lookup_insert_eq. split; done. }
          rewrite !(lookup_insert_ne _ _ _ _ Hne). apply (bs_A2_iff _ _ Hbs).
      + (* Case B: (k, d) ∉ σ. Under head=oldest, place [k] at the tail
           (newest end) of [σ] — this is consistent with [k] having no
           outgoing happens-before edges (it's a freshly-completed
           enqueue at this state). *)
        exists (AbsQ0State (σ ++ [(k, d)]) in0 rv0 (<[k := A2]> cp0)).
        assert (cp0 !! k = Some A1) as Hcp0_k_A1.
        { destruct Hcp0_k as [|Hc]; first done.
          apply (bs_A_iff _ _ Hbs) in Hc as [(d_w & Hℓk & Hkd_in_σ) | (? & ?)]; last done.
          rewrite Hℓeq in Hℓk. inversion Hℓk; subst. done. }
        assert (∀ k2, (k, k2) ∉ lt) as Hk_no_out.
        { intros k2 Hedge. apply (absq_wf_lt_COMP _ _ Hwf) in Hedge as (d' & Hℓk).
          simpl in Hℓk. rewrite Hℓk in Hℓeq. inversion Hℓeq. }
        (* k ∉ σ.*1: if it were, by [bs_seq_from_O] there would be some
           [(k, d'') ∈ σ], forcing [ℓ(k) = (d'', _)]. But [ℓ(k) = (d, _)]
           (from Hℓeq), so [d'' = d] and [(k, d) ∈ σ], contradicting
           Case B's [Hd_notin]. *)
        assert (k ∉ σ.*1) as Hk_notin_σ.
        { intros Hk_in.
          apply list_elem_of_fmap in Hk_in as ([k'' d''] & Hk_eq & Hkd_in).
          simpl in Hk_eq. subst k''.
          destruct (bs_seq_from_O _ _ Hbs _ _ Hkd_in) as (f' & _ & Hℓk).
          simpl in Hℓk. rewrite Hℓeq in Hℓk. inversion Hℓk; subst d'' f'.
          apply Hd_notin. exact Hkd_in. }
        split; simpl.
        * (* bs_nodup: σ.*1 ++ [k] is NoDup since σ.*1 NoDup and k ∉ σ.*1. *)
          rewrite fmap_app /=. apply NoDup_app. split_and!.
          -- apply (bs_nodup _ _ Hbs).
          -- intros x Hx Hx_sing.
             apply list_elem_of_singleton in Hx_sing. subst x. done.
          -- by apply NoDup_singleton.
        * intros k0 d0 Hk0_O Hℓ'.
          destruct (decide (k = k0)) as [<-|Hne].
          { rewrite lookup_insert_eq in Hℓ'. inversion Hℓ'; subst.
            apply elem_of_app. right. by apply list_elem_of_singleton. }
          rewrite (lookup_insert_ne _ _ _ _ Hne) in Hℓ'.
          apply elem_of_app. left.
          by apply (bs_completed_in _ _ Hbs k0 d0).
        * intros k0 d0 Hkd0.
          apply elem_of_app in Hkd0 as [Hkd0_σ | Hkd0_k].
          { destruct (bs_seq_from_O _ _ Hbs _ _ Hkd0_σ) as (f0 & Hk0_O & Hℓk0).
            destruct (decide (k = k0)) as [<-|Hne].
            { rewrite Hℓeq in Hℓk0. inversion Hℓk0; subst d0 f0.
              exists COMP. split; first done. by rewrite lookup_insert_eq. }
            exists f0. split; first done. by rewrite (lookup_insert_ne _ _ _ _ Hne). }
          apply list_elem_of_singleton in Hkd0_k. inversion Hkd0_k; subst k0 d0.
          exists COMP. split; first done. by rewrite lookup_insert_eq.
        * intros i j ki di kj dj Hij Hi Hj Hlt.
          assert (j ≤ length σ) as Hj_bound.
          { apply lookup_lt_Some in Hj. rewrite length_app /= in Hj. lia. }
          destruct (decide (j = length σ)) as [Hj_eq | Hj_lt'].
          { (* j = |σ|, so (kj, dj) = (k, d). Use Hk_no_out: (k, ki) ∉ lt. *)
            subst j.
            assert (i < length σ) as Hi_lt by lia.
            rewrite (lookup_app_l _ _ _ Hi_lt) in Hi.
            rewrite (lookup_app_r σ [(k, d)] (length σ) (Nat.le_refl _)) in Hj.
            rewrite Nat.sub_diag in Hj. simpl in Hj.
            inversion Hj; subst kj dj.
            by apply (Hk_no_out ki). }
          assert (j < length σ) as Hj_lt by lia.
          assert (i < length σ) as Hi_lt by lia.
          rewrite (lookup_app_l _ _ _ Hi_lt) in Hi.
          rewrite (lookup_app_l _ _ _ Hj_lt) in Hj.
          apply (bs_linearization _ _ Hbs i j ki di kj dj Hij Hi Hj).
          exact Hlt.
        * apply (bs_rv_agree _ _ Hbs).
        * intros k0. destruct (decide (k = k0)) as [<-|Hne].
          { rewrite !lookup_insert_eq. split; intros [=]. }
          rewrite !(lookup_insert_ne _ _ _ _ Hne). apply (bs_R1_iff _ _ Hbs).
        * intros k0. destruct (decide (k = k0)) as [<-|Hne].
          { rewrite !lookup_insert_eq. split; intros [=]. }
          rewrite !(lookup_insert_ne _ _ _ _ Hne). apply (bs_R2_iff _ _ Hbs).
        * intros k0. destruct (decide (k = k0)) as [<-|Hne].
          { rewrite !lookup_insert_eq. split; intros [=]. }
          rewrite !(lookup_insert_ne _ _ _ _ Hne). apply (bs_R3_iff _ _ Hbs).
        * intros k0 d0 f0 Hℓ'.
          destruct (decide (k = k0)) as [<-|Hne].
          { rewrite lookup_insert_eq in Hℓ'. inversion Hℓ'; subst.
            apply (bs_enq_input _ _ Hbs _ _ PEND Hℓeq). }
          rewrite (lookup_insert_ne _ _ _ _ Hne) in Hℓ'.
          by apply (bs_enq_input _ _ Hbs) in Hℓ'.
        * intros k0. destruct (decide (k = k0)) as [<-|Hne].
          { rewrite !lookup_insert_eq. split.
            - intros _. by right.
            - intros _. apply (bs_in0_dom _ _ Hbs). by left. }
          rewrite !(lookup_insert_ne _ _ _ _ Hne). apply (bs_in0_dom _ _ Hbs).
        * intros k0. destruct (decide (k = k0)) as [<-|Hne].
          { rewrite !lookup_insert_eq. split.
            - intros [=].
            - intros (_ & ? & [=] & _). }
          rewrite !(lookup_insert_ne _ _ _ _ Hne).
          pose proof (bs_A1_iff _ _ Hbs k0) as Hiff.
          rewrite Hiff. split.
          { intros (Hk0_O & d_w & Hℓk0 & Hkd_notin). split; first done.
            exists d_w. split; first done.
            intros Hin. apply elem_of_app in Hin as [|Hsing]; first done.
            apply list_elem_of_singleton in Hsing.
            inversion Hsing; subst. by apply Hne. }
          intros (Hk0_O & d_w & Hℓk0 & Hkd_notin').
          split; first done. exists d_w. split; first done.
          intros Hin. apply Hkd_notin'.
          apply elem_of_app. by left.
        * intros k0. destruct (decide (k = k0)) as [<-|Hne].
          { rewrite !lookup_insert_eq. split.
            - intros [=].
            - intros [(? & [=] & _) | (? & [=])]. }
          rewrite !(lookup_insert_ne _ _ _ _ Hne).
          pose proof (bs_A_iff _ _ Hbs k0) as Hiff.
          rewrite Hiff. split.
          { intros [(d_w & Hℓk0 & Hkd_σ) | (? & Hcp_A1)]; [left | right].
            - exists d_w. split; first done.
              apply elem_of_app. by left.
            - done. }
          intros [(d_w & Hℓk0 & Hkd_app) | (? & Hcp_A1)]; [left | right].
          { apply elem_of_app in Hkd_app as [Hkd_σ|Hkd_sing].
            - by exists d_w.
            - apply list_elem_of_singleton in Hkd_sing.
              inversion Hkd_sing; subst. by exfalso; apply Hne. }
          done.
        * intros k0. destruct (decide (k = k0)) as [<-|Hne].
          { rewrite !lookup_insert_eq. split; done. }
          rewrite !(lookup_insert_ne _ _ _ _ Hne). apply (bs_A2_iff _ _ Hbs).
    - (* RET-ENQ2: cp(k) = A1, k ∉ O. ℓ unchanged, O unchanged. *)
      exists (AbsQ0State σ in0 rv0 (<[k := A2]> cp0)).
      split; simpl.
      + apply (bs_nodup _ _ Hbs).
      + apply (bs_completed_in _ _ Hbs).
      + apply (bs_seq_from_O _ _ Hbs).
      + apply (bs_linearization _ _ Hbs).
      + apply (bs_rv_agree _ _ Hbs).
      + intros k0. destruct (decide (k = k0)) as [<-|Hne].
        { rewrite !lookup_insert_eq. split; intros [=]. }
        rewrite !(lookup_insert_ne _ _ _ _ Hne). apply (bs_R1_iff _ _ Hbs).
      + intros k0. destruct (decide (k = k0)) as [<-|Hne].
        { rewrite !lookup_insert_eq. split; intros [=]. }
        rewrite !(lookup_insert_ne _ _ _ _ Hne). apply (bs_R2_iff _ _ Hbs).
      + intros k0. destruct (decide (k = k0)) as [<-|Hne].
        { rewrite !lookup_insert_eq. split; intros [=]. }
        rewrite !(lookup_insert_ne _ _ _ _ Hne). apply (bs_R3_iff _ _ Hbs).
      + apply (bs_enq_input _ _ Hbs).
      + intros k0. destruct (decide (k = k0)) as [<-|Hne].
        { rewrite !lookup_insert_eq. split.
          - intros _. by right.
          - intros _. apply (bs_in0_dom _ _ Hbs). by left. }
        rewrite (lookup_insert_ne _ _ _ _ Hne). apply (bs_in0_dom _ _ Hbs).
      + intros k0. destruct (decide (k = k0)) as [<-|Hne].
        { rewrite !lookup_insert_eq. split.
          - intros [=].
          - intros (? & ?). set_solver. }
        rewrite (lookup_insert_ne _ _ _ _ Hne). apply (bs_A1_iff _ _ Hbs).
      + intros k0. destruct (decide (k = k0)) as [<-|Hne].
        { rewrite !lookup_insert_eq. split.
          - intros [=].
          - intros [(d_w & Hℓk & Hkd_w_σ) | (_ & [=])].
            exfalso.
            destruct (bs_seq_from_O _ _ Hbs _ _ Hkd_w_σ) as (f_x & Hkx_O & _).
            simpl in Hkx_O. by apply HkNotO. }
        rewrite !(lookup_insert_ne _ _ _ _ Hne). apply (bs_A_iff _ _ Hbs).
      + intros k0. destruct (decide (k = k0)) as [<-|Hne].
        { rewrite !lookup_insert_eq. done. }
        rewrite !(lookup_insert_ne _ _ _ _ Hne). apply (bs_A2_iff _ _ Hbs).
    - (* RET-DEQ: cp(k) = R2, rv(k) = Some d. cp' = <[k:=R3]>cp. *)
      exists (AbsQ0State σ in0 rv0 (<[k := R3]> cp0)).
      assert (ℓ !! k = None) as Hℓk_none.
      { destruct (ℓ !! k) as [[d' f']|] eqn:Hℓk; last done. exfalso.
        apply (absq_wf_ℓcp _ _ Hwf) in Hℓk as [Hcp'|Hcp']; rewrite Hcp in Hcp'; discriminate. }
      split; simpl.
      + apply (bs_nodup _ _ Hbs).
      + apply (bs_completed_in _ _ Hbs).
      + apply (bs_seq_from_O _ _ Hbs).
      + apply (bs_linearization _ _ Hbs).
      + apply (bs_rv_agree _ _ Hbs).
      + intros k0. destruct (decide (k = k0)) as [<-|Hne].
        { rewrite !lookup_insert_eq. split; intros [=]. }
        rewrite !(lookup_insert_ne _ _ _ _ Hne). apply (bs_R1_iff _ _ Hbs).
      + intros k0. destruct (decide (k = k0)) as [<-|Hne].
        { rewrite !lookup_insert_eq. split; intros [=]. }
        rewrite !(lookup_insert_ne _ _ _ _ Hne). apply (bs_R2_iff _ _ Hbs).
      + intros k0. destruct (decide (k = k0)) as [<-|Hne].
        { rewrite !lookup_insert_eq. done. }
        rewrite !(lookup_insert_ne _ _ _ _ Hne). apply (bs_R3_iff _ _ Hbs).
      + apply (bs_enq_input _ _ Hbs).
      + intros k0. destruct (decide (k = k0)) as [<-|Hne].
        { rewrite !lookup_insert_eq. split.
          - intros Hsome. apply (bs_in0_dom _ _ Hbs) in Hsome as [H|H]; rewrite Hcp in H; discriminate.
          - intros [[=]|[=]]. }
        rewrite !(lookup_insert_ne _ _ _ _ Hne). apply (bs_in0_dom _ _ Hbs).
      + intros k0. destruct (decide (k = k0)) as [<-|Hne].
        { rewrite !lookup_insert_eq. split.
          - intros [=].
          - intros (_ & ? & Hℓk & _). by rewrite Hℓk_none in Hℓk. }
        rewrite !(lookup_insert_ne _ _ _ _ Hne). apply (bs_A1_iff _ _ Hbs).
      + intros k0. destruct (decide (k = k0)) as [<-|Hne].
        { rewrite !lookup_insert_eq. split.
          - intros [=].
          - intros [(? & Hℓk & _) | (_ & [=])].
            by rewrite Hℓk_none in Hℓk. }
        rewrite !(lookup_insert_ne _ _ _ _ Hne). apply (bs_A_iff _ _ Hbs).
      + intros k0. destruct (decide (k = k0)) as [<-|Hne].
        { rewrite !lookup_insert_eq. split; intros [=]. }
        rewrite !(lookup_insert_ne _ _ _ _ Hne). apply (bs_A2_iff _ _ Hbs).
    - (* LIN-DEQ1: removes k' ∈ min(O) from O, dequeues d = ℓ(k').1.
         σ_u' = σ_u filtered to remove d (no change if d ∉ σ_u);
         cp0_u'(k') set to A (if f = PEND) or A2 (if f = COMP).
         Note: we don't require d be at the end of σ_u, since we're
         constructing u' directly rather than simulating an AbsQ0 trace. *)
      assert (ℓ !! k = None) as Hℓk_none.
      { destruct (ℓ !! k) as [[d' f']|] eqn:Hℓk; last done. exfalso.
        apply (absq_wf_ℓcp _ _ Hwf) in Hℓk as [Hcp'|Hcp']; rewrite Hcp in Hcp'; discriminate. }
      assert (k ≠ k') as Hk_ne_k'.
      { intros ->. apply (absq_wf_ℓcp _ _ Hwf) in Hℓeq as [H|H]; rewrite Hcp in H; discriminate. }
      assert (k' ∈ O) as Hk'_O by (apply elem_of_filter in Hmin; tauto).
      assert (cp !! k' = Some A1 ∨ cp !! k' = Some A2) as Hcp_k'.
      { destruct f as [|]; [left|right].
        - apply (absq_wf_PEND_O _ _ Hwf _ d); done.
        - by apply (absq_wf_COMP _ _ Hwf _ _ Hℓeq). }
      exists (AbsQ0State
                (filter (λ kv, kv.1 ≠ k') σ)
                in0
                (<[k := SOMEV d]> rv0)
                (<[k := R2]> (<[k' := match f with PEND => A | COMP => A2 end]> cp0))).
      split; simpl.
      + (* bs_nodup: (filter P σ).*1 is a sublist of σ.*1, which is NoDup. *)
        pose proof (bs_nodup _ _ Hbs) as Hnd_σ. simpl in Hnd_σ.
        (* Induction on σ directly to avoid sublist manipulation. *)
        clear -Hnd_σ. induction σ as [|[k_i v_i] σ IH]; first done.
        simpl in Hnd_σ. apply NoDup_cons in Hnd_σ as [Hk_i_notin Hnd_σ].
        rewrite filter_cons. case_decide as Hcond; last by apply IH.
        simpl. apply NoDup_cons. split; last by apply IH.
        intros Hin. apply list_elem_of_fmap in Hin as ([k'' v'] & Heq & Hin).
        simpl in Heq; subst k''. apply list_elem_of_filter in Hin as (_ & Hin).
        apply Hk_i_notin. apply list_elem_of_fmap. by exists (k_i, v').
      + (* bs_completed_in *)
        intros k0 d0 Hk0_O' Hℓk0.
        apply list_elem_of_filter. split.
        { simpl. intros <-. set_solver. }
        apply (bs_completed_in _ _ Hbs k0 d0); last done. set_solver.
      + (* bs_seq_from_O *)
        intros k0 d0 Hkd0.
        apply list_elem_of_filter in Hkd0 as (Hk0_ne & Hkd0_σ).
        simpl in Hk0_ne.
        destruct (bs_seq_from_O _ _ Hbs _ _ Hkd0_σ) as (f0 & Hk0_O & Hℓk0).
        exists f0. split; last done. set_solver.
      + (* bs_linearization *)
        intros i j ki di kj dj Hij Hi Hj Hlt.
        (* filter preserves order, and σ is NoDup (pairs) since σ.*1 is. *)
        assert (NoDup σ) as Hnd_σ_pairs.
        { pose proof (bs_nodup _ _ Hbs) as Hnd. simpl in Hnd.
          by apply (NoDup_fmap_1 fst) in Hnd. }
        destruct (filter_lookup_mono (λ kv : positive * val, kv.1 ≠ k') σ
                    i j _ _ Hnd_σ_pairs Hij Hi Hj) as (i' & j' & Hij' & Hi' & Hj').
        apply (bs_linearization _ _ Hbs i' j' ki di kj dj Hij' Hi' Hj').
        apply elem_of_filter in Hlt as [_ Hlt_in]. exact Hlt_in.
      + (* bs_rv_agree *)
        intros k0. destruct (decide (k = k0)) as [<-|Hne].
        { by rewrite !lookup_insert_eq. }
        rewrite !(lookup_insert_ne _ _ _ _ Hne). apply (bs_rv_agree _ _ Hbs).
      + (* bs_R1_iff *)
        intros k0. destruct (decide (k = k0)) as [<-|Hne1].
        { rewrite !lookup_insert_eq. split; intros [=]. }
        rewrite !(lookup_insert_ne _ _ _ _ Hne1).
        destruct (decide (k' = k0)) as [<-|Hne2].
        { rewrite lookup_insert_eq.
          destruct Hcp_k' as [Hc|Hc]; rewrite Hc; destruct f; split; intros [=]. }
        rewrite (lookup_insert_ne _ _ _ _ Hne2). apply (bs_R1_iff _ _ Hbs).
      + (* bs_R2_iff *)
        intros k0. destruct (decide (k = k0)) as [<-|Hne1].
        { by rewrite !lookup_insert_eq. }
        rewrite !(lookup_insert_ne _ _ _ _ Hne1).
        destruct (decide (k' = k0)) as [<-|Hne2].
        { rewrite lookup_insert_eq.
          destruct Hcp_k' as [Hc|Hc]; rewrite Hc; destruct f; split; intros [=]. }
        rewrite (lookup_insert_ne _ _ _ _ Hne2). apply (bs_R2_iff _ _ Hbs).
      + (* bs_R3_iff *)
        intros k0. destruct (decide (k = k0)) as [<-|Hne1].
        { rewrite !lookup_insert_eq. split; intros [=]. }
        rewrite !(lookup_insert_ne _ _ _ _ Hne1).
        destruct (decide (k' = k0)) as [<-|Hne2].
        { rewrite lookup_insert_eq.
          destruct Hcp_k' as [Hc|Hc]; rewrite Hc; destruct f; split; intros [=]. }
        rewrite (lookup_insert_ne _ _ _ _ Hne2). apply (bs_R3_iff _ _ Hbs).
      + (* bs_enq_input *) apply (bs_enq_input _ _ Hbs).
      + (* bs_in0_dom *)
        intros k0.
        destruct (decide (k = k0)) as [<-|Hne1].
        { split.
          - intros Hsome. apply (bs_in0_dom _ _ Hbs) in Hsome as [H|H]; rewrite Hcp in H; discriminate.
          - intros [Hc|Hc]; rewrite lookup_insert_eq in Hc; discriminate. }
        destruct (decide (k' = k0)) as [<-|Hne2].
        { rewrite (lookup_insert_ne _ k k' _ Hk_ne_k').
          apply (bs_in0_dom _ _ Hbs). }
        rewrite (lookup_insert_ne _ k k0 _ Hne1). apply (bs_in0_dom _ _ Hbs).
      + (* bs_A1_iff *)
        intros k0.
        destruct (decide (k = k0)) as [<-|Hne1].
        { rewrite lookup_insert_eq. split.
          - intros [=].
          - intros (_ & ? & Hℓk & _). by rewrite Hℓk_none in Hℓk. }
        rewrite (lookup_insert_ne _ _ _ _ Hne1).
        destruct (decide (k' = k0)) as [<-|Hne2].
        { rewrite lookup_insert_eq. split.
          - destruct f; intros [=].
          - intros (Hk0_O & _). set_solver. }
        rewrite (lookup_insert_ne _ _ _ _ Hne2).
        pose proof (bs_A1_iff _ _ Hbs k0) as Hiff. rewrite Hiff. split.
        { intros (Hk0_O & d_w & Hℓk0 & Hkd_w_σ).
          split; first set_solver.
          exists d_w. split; first done.
          intros [_ Hkd_w_filter]%list_elem_of_filter. done. }
        intros (Hk0_O & d_w & Hℓk0 & Hkd_w_filter).
        split; first set_solver.
        exists d_w. split; first done.
        intros Hkd_w_σ. apply Hkd_w_filter. apply list_elem_of_filter. split; last done.
        simpl. done.
      + (* bs_A_iff *)
        intros k0.
        destruct (decide (k = k0)) as [<-|Hne1].
        { rewrite !lookup_insert_eq. split.
          - intros [=].
          - intros [(? & Hℓk & _) | (_ & [=])].
            by rewrite Hℓk_none in Hℓk. }
        rewrite (lookup_insert_ne _ _ _ _ Hne1).
        destruct (decide (k' = k0)) as [<-|Hne2].
        { rewrite lookup_insert_eq. destruct f as [|].
          - (* f = PEND: cp0_u'(k') = A *)
            split.
            + intros _. right. split.
              * set_solver.
              * rewrite (lookup_insert_ne _ k k' _ Hk_ne_k').
                destruct Hcp_k' as [H|H]; first done. exfalso.
                pose proof (absq_wf_PEND_O _ _ Hwf _ _ Hk'_O Hℓeq) as H1.
                rewrite H1 in H. discriminate.
            + done.
          - (* f = COMP: cp0_u'(k') = A2, so LHS Some A2 = Some A is False *)
            split.
            + intros [=].
            + intros [(d_w & Hℓk & Hkd_w_σ') | (HnotO & Hcp'_A1)].
              * rewrite Hℓeq in Hℓk. inversion Hℓk.
              * rewrite (lookup_insert_ne _ k k' _ Hk_ne_k') in Hcp'_A1.
                pose proof (absq_wf_COMP _ _ Hwf _ _ Hℓeq) as H1.
                rewrite H1 in Hcp'_A1. discriminate. }
        rewrite (lookup_insert_ne _ _ _ _ Hne2).
        rewrite (lookup_insert_ne _ k k0 _ Hne1).
        pose proof (bs_A_iff _ _ Hbs k0) as Hiff. rewrite Hiff. split.
        { intros [(d_w & Hℓk0 & Hkd_w_σ) | (HnotO & Hcp_A1)]; [left | right].
          - exists d_w. split; first done. apply list_elem_of_filter. split; last done.
            simpl. done.
          - split; last done. set_solver. }
        intros [(d_w & Hℓk0 & [_ Hkd_w_σ]%list_elem_of_filter) | (HnotO & Hcp_A1)]; [left | right].
        { by exists d_w. }
        split; last done. set_solver.
      + (* bs_A2_iff *)
        intros k0.
        destruct (decide (k = k0)) as [<-|Hne1].
        { rewrite !lookup_insert_eq. split; intros [=]. }
        rewrite !(lookup_insert_ne _ _ _ _ Hne1).
        destruct (decide (k' = k0)) as [<-|Hne2].
        { rewrite lookup_insert_eq. destruct f as [|].
          - pose proof (absq_wf_PEND_O _ _ Hwf _ _ Hk'_O Hℓeq) as HA1.
            rewrite HA1. split; intros [=].
          - pose proof (absq_wf_COMP _ _ Hwf _ _ Hℓeq) as HA2.
            rewrite HA2. done. }
        rewrite (lookup_insert_ne _ _ _ _ Hne2). apply (bs_A2_iff _ _ Hbs).
    - (* LIN-DEQ2: cp(k) = R1, all O are PEND. σ untouched. The
         option-encoded return value [NONEV] is recorded in [rv0]. *)
      exists (AbsQ0State σ in0 (<[k := NONEV]> rv0) (<[k := R2]> cp0)).
      assert (ℓ !! k = None) as Hℓk_none.
      { destruct (ℓ !! k) as [[d' f']|] eqn:Hℓk; last done. exfalso.
        apply (absq_wf_ℓcp _ _ Hwf) in Hℓk as [Hcp'|Hcp']; rewrite Hcp in Hcp'; discriminate. }
      split; simpl.
      + apply (bs_nodup _ _ Hbs).
      + apply (bs_completed_in _ _ Hbs).
      + apply (bs_seq_from_O _ _ Hbs).
      + apply (bs_linearization _ _ Hbs).
      + intros k0. destruct (decide (k = k0)) as [<-|Hne].
        { by rewrite !lookup_insert_eq. }
        rewrite !(lookup_insert_ne _ _ _ _ Hne). apply (bs_rv_agree _ _ Hbs).
      + intros k0. destruct (decide (k = k0)) as [<-|Hne].
        { rewrite !lookup_insert_eq. split; intros [=]. }
        rewrite !(lookup_insert_ne _ _ _ _ Hne). apply (bs_R1_iff _ _ Hbs).
      + intros k0. destruct (decide (k = k0)) as [<-|Hne].
        { rewrite !lookup_insert_eq. done. }
        rewrite !(lookup_insert_ne _ _ _ _ Hne). apply (bs_R2_iff _ _ Hbs).
      + intros k0. destruct (decide (k = k0)) as [<-|Hne].
        { rewrite !lookup_insert_eq. split; intros [=]. }
        rewrite !(lookup_insert_ne _ _ _ _ Hne). apply (bs_R3_iff _ _ Hbs).
      + apply (bs_enq_input _ _ Hbs).
      + intros k0. destruct (decide (k = k0)) as [<-|Hne].
        { rewrite !lookup_insert_eq. split.
          - intros Hsome. apply (bs_in0_dom _ _ Hbs) in Hsome as [H|H]; rewrite Hcp in H; discriminate.
          - intros [[=]|[=]]. }
        rewrite !(lookup_insert_ne _ _ _ _ Hne). apply (bs_in0_dom _ _ Hbs).
      + intros k0. destruct (decide (k = k0)) as [<-|Hne].
        { rewrite !lookup_insert_eq. split.
          - intros [=].
          - intros (_ & ? & Hℓk & _). by rewrite Hℓk_none in Hℓk. }
        rewrite !(lookup_insert_ne _ _ _ _ Hne). apply (bs_A1_iff _ _ Hbs).
      + intros k0. destruct (decide (k = k0)) as [<-|Hne].
        { rewrite !lookup_insert_eq. split.
          - intros [=].
          - intros [(? & Hℓk & _) | (_ & [=])]. by rewrite Hℓk_none in Hℓk. }
        rewrite !(lookup_insert_ne _ _ _ _ Hne). apply (bs_A_iff _ _ Hbs).
      + intros k0. destruct (decide (k = k0)) as [<-|Hne].
        { rewrite !lookup_insert_eq. split; intros [=]. }
        rewrite !(lookup_insert_ne _ _ _ _ Hne). apply (bs_A2_iff _ _ Hbs).
  Qed.

  (** Clause (ii') of Definition 6 (the totality condition): every
    [AbsQ]-reachable state has a [bs]-matching [AbsQ0] state.
    Established by forward induction on the trace, using [bs_init]
    at the base and [bs_fwd_step] at each step. *)
  Lemma bs_fwd_steps s0 u0 ls s :
    absq_wf valid_value s0 → bs s0 u0 → absq_steps rme valid_value s0 ls s → ∃ u, bs s u.
  Proof.
    intros Hwf Hbs Hsteps.
    revert u0 Hwf Hbs.
    induction Hsteps as [s0|s0 s1 s2 l ls Hstep _ IH];
      intros u0 Hwf Hbs; first by eauto.
    destruct (bs_fwd_step _ _ _ _ Hwf Hstep Hbs) as [u1 Hbs1].
    apply (IH u1 (absq_wf_step _ _ _ _ _ Hwf Hstep) Hbs1).
  Qed.

  Lemma bs_total s ls :
    absq_steps rme valid_value absq_init ls s → ∃ u, bs s u.
  Proof.
    intros Hsteps.
    apply (bs_fwd_steps absq_init absq0_init ls s);
      [apply absq_wf_init | apply bs_init | exact Hsteps].
  Qed.
End bs_step.

(** The main refinement theorem: every observable trace of [AbsQ] is
  also an observable trace of [AbsQ0]. Obtained by combining the six
  pieces built above via [backward_simulation_with_inv_refines]:
  [bs_init], [bs_init_only] (clause (i) of Def. 6); [absq_wf_init],
  [absq_wf_step] (forward invariant); [bs_total] (clause (ii')); and
  [bs_step] (clause (ii)). *)
Theorem absq_refines_absq0 rme valid_value :
  Γ_refines absq_init (absq_step rme valid_value) absq0_init (absq0_step rme valid_value)
    is_observable.
Proof.
  apply (backward_simulation_with_inv_refines _ _ _ _ _ bs (absq_wf valid_value)).
  split.
  - apply bs_init.
  - apply bs_init_only.
  - apply absq_wf_init.
  - intros s l s' Hstep Hwf. by eapply absq_wf_step.
  - apply (bs_total rme valid_value).
  - intros s l s' u' Hwf Hstep Hbs'. by eapply bs_step.
Qed.
