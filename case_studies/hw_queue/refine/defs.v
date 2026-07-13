(* refine_defs.v: shared definitions for the HWQ refinement proof.

  Extracted from the monolithic [refine.v] to speed up incremental
  rebuilds when editing a single lemma.  Contains: ghost-state type
  [op_info], the [hwqG] camera, the trace invariant [I_lang_hwq], the
  forward-simulation predicate [fs1_sim] and its initialisation
  lemma, the [absq_wf_steps] helper, and the skeleton [Section
  hwq_skeleton] definitions ([Nhwq], [hwq_inv_body], [is_hwq],
  [Nhwq_notroot], [hwq_repr], [init_hwq]).

  Each proof file ([refine_new_queue.v], [refine_enq_cont.v],
  [refine_deq_cont.v], [refine_op_spec.v]) re-opens a Section with the
  same Context and aliases these shared definitions via [Local
  Notation], so unchanged code in those files can continue to write
  [hwq_inv_body γ ar back l] without passing [empty sz] explicitly. *)

From iris.algebra Require Import auth excl gmap.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import invariants.
From iris_logatom.program_logic Require Import atomic_complete.
From iris.heap_lang Require Import adequacy primitive_laws notation proofmode.
From iris_logatom.heap_lang Require Import mgc fork_free.
From iris_logatom.heap_lang.lib Require Import trace.
From iris_logatom.pure_logic Require Import linear adequacy.
From iris_logatom.pure_logic.refine Require Import absq absq_refines_absq0
                                                    absq0_linearizable
                                                    backward_simulation.
From iris_logatom.pure_logic.models Require Import bag_like.

From case_studies.hw_queue Require Import impl.

(* ========================================================================= *)
(* Per-operation metadata tracked via ghost state.  Operations in flight
  register an [op_info] entry keyed by their trace identifier [τ].  For an
  enqueue, [op_info_reserved] starts as [None] and becomes [Some i] after
  the FAA reserves array position [i].  Dequeues carry no reservation. *)

Inductive op_kind : Set :=
  | OpEnq (d : val)
  (* [OpDeq observed rng_τ]: a dequeue in progress.  [observed] is an
    ordered log of offsets τ has loaded and, for each one, the unique
    storer of that offset at τ's observation time (if any).  The
    [option positive] is [Some k'] iff [k'] already had [stored_at k' =
    Some j] at τ's load of [j], and [None] otherwise.  Because the load
    either saw [NONEV] or [τ] subsequently CAS-failed on a [SOMEV], any
    recorded [k'] must have been removed from [absq_O] by some other
    dequeue's CAS-clear step, and by monotonicity of [O] it stays
    removed forever.

    [rng_τ] is the value of [back_val] at τ's most recent outer-Löb
    reset (or at [CALL-DEQ] before the first reset).  Bundled so that
    the fs1_sim invariant [Hlt_res_obs] can assert that any
    [lt]-predecessor [k] of an enqueue [k_e] with reservation [r_e <
    rng_τ] cannot have [(r_k, None) ∈ obs] at position [r_k =
    stored_at k].  At CAS-success [r_e = length obs < rng_τ] so this
    rules out the [None]-branch of the minimality discharge. *)
  | OpDeq (observed : list (Z * option positive)) (rng_τ : Z).

Record op_info : Set := {
  op_info_kind : op_kind;
  op_info_reserved : option Z;
  op_info_stored : bool;
}.

Global Instance op_kind_eqdec : EqDecision op_kind.
Proof. solve_decision. Defined.

Global Instance op_info_eqdec : EqDecision op_info.
Proof. solve_decision. Defined.

Definition opmapUR : ucmra := gmapUR positive (exclR (leibnizO op_info)).

Definition to_opmap (m : gmap positive op_info) : gmap positive (excl (leibnizO op_info)) :=
  Excl <$> m.

(* [svmapUR]: [agreeR]-based gmap tracking the value a storer wrote at
  each array offset.  Once set for an offset, the value is frozen — so
  any later observer extracting a frag at that offset sees the same
  value.  Used to discharge the semantically-unreachable [SOMEV e]
  CAS-fail branch: the outer iInv observes [SOMEV d], extracts a
  persistent frag; the inner iInv3 with [SOMEV e] extracts another
  frag; [agreeR] forces [d = e], contradicting [Hne_cas]. *)
Definition svmapUR : ucmra := gmapUR nat (agreeR (leibnizO val)).

Definition to_svmap (m : gmap nat val) : gmap nat (agree (leibnizO val)) :=
  to_agree <$> m.

(* [dqmapUR]: [agreeR]-based gmap tracking the value a dequeue τ
  observed as its LIN-DEQ1 result.  At CAS-success in deq_cont we
  allocate [dq_map[τ := d]] where [d] is the cell's stored value.
  Emitting a persistent singleton frag at that site and returning
  it through [Hdeq_spec]'s post lets the RET-DEQ iInv re-establish
  [dq_map τ = Some v] and thus, via [dq_inv], [rv τ = Some v],
  discharging the [absq_step_ret_deq] side-condition. *)
Definition dqmapUR : ucmra := gmapUR positive (agreeR (leibnizO val)).

Definition to_dqmap (m : gmap positive val) : gmap positive (agree (leibnizO val)) :=
  to_agree <$> m.

Class hwqG Σ := HwqG {
  hwqG_op_inG :: inG Σ (authR opmapUR);
  hwqG_sv_inG :: inG Σ (authR svmapUR);
  hwqG_dq_inG :: inG Σ (authR dqmapUR);
}.

Global Instance absq_state_inhabited : Inhabited absq_state := populate absq_init.

Definition hwqΣ : gFunctors := #[ GFunctor (authR opmapUR);
                                  GFunctor (authR svmapUR);
                                  GFunctor (authR dqmapUR) ].

Global Instance subG_hwqΣ Σ : subG hwqΣ Σ → hwqG Σ.
Proof. solve_inG. Qed.

(* ========================================================================= *)
(* The trace invariant: [ts] is the Call/Ret projection of some reachable
  AbsQ execution. This is exactly [trace_refines_absq] (the hypothesis of
  the refine technique's [refines_absq_trace_linearizable]), so that
  [bdgjst_free]'s [I_lang R ts] conclusion delivers what the
  refinement bridge expects. *)

(** HWQ's chosen [valid_value] predicate.  HWQ stores [SOMEV d] cells
  in the array and uses [CmpXchg] on them, so the wrapped form needs
  to be unboxed. *)
Definition hwq_valid_value : val → Prop :=
  λ v, val_is_unboxed (SOMEV v).

Definition I_lang_hwq (ts : list (positive * trace)) : Prop :=
  ∃ s ls, absq_steps NeverEmpty hwq_valid_value absq_init ls s ∧
          ts = filter (not ∘ is_lin ∘ snd) (trace_of_absq_labels ls).

Lemma I_lang_hwq_init : I_lang_hwq [].
Proof.
  exists absq_init, []. split.
  - apply lts_steps_nil.
  - by rewrite /trace_of_absq_labels /= filter_nil.
Qed.

(* ========================================================================= *)
(* Forward-simulation predicate [fs1_sim] between the HWQ physical state
  and an AbsQ witness.  Pass 1 carries only the invariants needed for the
  enqueue path of [op_spec]: heap shape, freshness of trace ids,
  domain correspondence with [op_map], and the pending/returned
  control-point invariants for enqueues.  Pass 2 will extend this with
  the paper's conditions (a), (b), (c) over the happens-before order
  [<] and per-dequeue observation history, needed for the CAS
  linearisation-point argument. *)

Definition fs1_sim
  (valid_value : val → Prop)
  (sz : Z)
  (items : list val)
  (back_val : Z)
  (s : absq_state)
  (op_map : gmap positive op_info)
  (stored_at : gmap positive nat)
  (ts : list (positive * trace))
  : Prop :=
  (* Heap shape.  [back_val] may grow past [sz] via FAA (the code
    then diverges instead of storing); the [slots_free] clause is
    then vacuous. *)
  length items = Z.to_nat sz ∧
  (0 ≤ back_val)%Z ∧
  (∀ i : nat, (Z.to_nat back_val ≤ i < Z.to_nat sz)%nat →
              items !! i = Some NONEV) ∧
  (* Freshness: every identifier used in AbsQ has already appeared in the
    trace, so a fresh trace [τ] is fresh in [s.absq_cp] too. *)
  dom s.(absq_cp) ⊆ list_to_set ts.*1 ∧
  (* [op_map] covers a subset of the in-progress operations in AbsQ;
    at RET the fragment is surrendered and the entry deleted, so the
    containment is strict by the completed ops. *)
  dom op_map ⊆ dom s.(absq_cp) ∧
  (* Enqueue correspondence.  [op_map[τ] = Some (OpEnq …)] means the
    operation is in its [A1] phase.  The [op_info_stored] flag
    distinguishes pre-store (false) from post-store (true):
    pre-store, [τ ∈ O] (no [LIN-DEQ1] fires on [τ] until we store a
    [SOMEV] at the reserved position) and, when reserved, [items[i] =
    NONEV].  Post-store, either [τ ∈ O] and [items[i] = SOMEV d] or
    [τ ∉ O] and [items[i] = NONEV] (dequeue CAS-removed). *)
  (∀ τ d r b,
    op_map !! τ = Some {| op_info_kind := OpEnq d;
                          op_info_reserved := r;
                          op_info_stored := b |} →
    s.(absq_cp) !! τ = Some A1 ∧
    s.(absq_l) !! τ = Some (d, PEND) ∧
    (b = false → τ ∈ s.(absq_O)) ∧
    (∀ i, r = Some i →
       (0 ≤ i < back_val)%Z ∧
       ((i < sz)%Z →
          (b = false → items !! Z.to_nat i = Some NONEV) ∧
          (b = true →
             (τ ∈ s.(absq_O) → items !! Z.to_nat i = Some (SOMEV d)) ∧
             (τ ∉ s.(absq_O) → items !! Z.to_nat i = Some NONEV))))) ∧
  (* Dequeue correspondence.  At RET-DEQ time we delete [τ] from
    op_map; until then [op_map[τ] = Some OpDeq] implies [cp ∈ {R1,
    R2}].  The [op_info_stored] flag marks whether LIN-DEQ1 has
    fired for [τ]: pre-LIN [stored=false] → [cp=R1]; post-LIN
    [stored=true] → [cp=R2] ∧ [rv(τ) = Some d].  Needed in Pass 2
    to rule out [cp=R2] when the deq-fragment holds [stored=false]
    at the CAS-success site. *)
  (∀ τ obs rng_τ r b,
    op_map !! τ = Some {| op_info_kind := OpDeq obs rng_τ;
                          op_info_reserved := r;
                          op_info_stored := b |} →
    (b = false → s.(absq_cp) !! τ = Some R1) ∧
    (b = true → s.(absq_cp) !! τ = Some R2 ∧
                ∃ d, s.(absq_rv) !! τ = Some d)) ∧
  (* Reserved array positions are unique. *)
  (∀ τ τ' d d' i b b',
    op_map !! τ  = Some {| op_info_kind := OpEnq d;
                           op_info_reserved := Some i;
                           op_info_stored := b |} →
    op_map !! τ' = Some {| op_info_kind := OpEnq d';
                           op_info_reserved := Some i;
                           op_info_stored := b' |} →
    τ = τ') ∧
  (* Array-cell well-formedness: every in-range cell is either [NONEV]
    or [SOMEV d] for some [d] satisfying both [valid_value d] (lifted
    from the abstract enqueue precondition) and [val_is_unboxed
    (SOMEV d)] (a separate concrete fact about the wrapped form,
    needed by Pass 2 to discharge [vals_compare_safe] on the dequeue
    [CmpXchg]). *)
  (∀ i : nat, (i < Z.to_nat sz)%nat →
    items !! i = Some NONEV ∨
    ∃ d, items !! i = Some (SOMEV d) ∧ valid_value d ∧ val_is_unboxed (SOMEV d)) ∧
  (* Forward items → enqueue correspondence: every [SOMEV d] cell was
    stored by some enqueue still in [O] whose [ℓ] entry records [d].
    Needed in Pass 2 to witness the [k_e] that [absq_step_lin_deq1]
    removes at CAS-success time. *)
  (∀ (i : nat) (d : val),
    items !! i = Some (SOMEV d) →
    ∃ k_e, k_e ∈ s.(absq_O) ∧ ∃ f, s.(absq_l) !! k_e = Some (d, f)) ∧
  (* Persistent storer log.  [stored_at τ = Some i] records that
    enqueue τ stored its value at cell i; survives past RET-ENQ,
    unlike [op_map] entries.  Together, the clauses pin each
    [SOMEV d] cell to a unique storer that is in [ℓ] and O. *)
  (∀ τ i, stored_at !! τ = Some i →
    (i < Z.to_nat back_val)%nat ∧
    ∃ d f, s.(absq_l) !! τ = Some (d, f) ∧
      (τ ∈ s.(absq_O) → items !! i = Some (SOMEV d)) ∧
      (τ ∉ s.(absq_O) → items !! i = Some NONEV)) ∧
  (∀ τ₁ τ₂ i, stored_at !! τ₁ = Some i → stored_at !! τ₂ = Some i →
    τ₁ = τ₂) ∧
  (∀ i d, items !! i = Some (SOMEV d) →
    ∃ τ, stored_at !! τ = Some i ∧ τ ∈ s.(absq_O) ∧
         ∃ f, s.(absq_l) !! τ = Some (d, f)) ∧
  (∀ τ d r, op_map !! τ = Some {| op_info_kind := OpEnq d;
                                  op_info_reserved := r;
                                  op_info_stored := false |} →
    stored_at !! τ = None) ∧
  (* Post-store op_map entries have a recorded stored_at entry at
    the reserved position.  Linking these lets CAS-success ' enq_clause
    preservation rule out τ' ≠ k_e at [i' = rng-i] via the
    [stored_at] injectivity. *)
  (∀ τ d i, op_map !! τ = Some {| op_info_kind := OpEnq d;
                                  op_info_reserved := Some i;
                                  op_info_stored := true |} →
    stored_at !! τ = Some (Z.to_nat i)) ∧
  (* Cross-uniqueness: pre-store reservations are disjoint from stored_at's
    image.  At FAA the newly assigned [r = back_val] is fresh because
    [Hstored]'s bound [i < back_val] holds before the increment.  Lets
    [Hstored] and [Hstored_inj] preservation at store rule out the
    [τ' ≠ τ] case when [stored_at τ' = Some (Z.to_nat r)]. *)
  (∀ τ d r, op_map !! τ = Some {| op_info_kind := OpEnq d;
                                  op_info_reserved := Some r;
                                  op_info_stored := false |} →
    ∀ τ' i, stored_at !! τ' = Some i → Z.to_nat r ≠ i) ∧
  (* Observation-history invariant (V1B-a, task #47).  For an in-flight
    pre-LIN dequeue τ with observed list [obs], every recorded
    [(j, Some k')] entry witnesses that [k'] had stored at offset [j]
    at τ's observation (stored_at carries this) and that τ's load saw
    the cell as [NONEV] (or τ subsequently CAS-failed on a [SOMEV]),
    which physically forces [k' ∉ O] at observation time.  By
    monotonicity of [O], [k' ∉ O] persists.

    We only record [Some k'] when [stored_at] actually had a storer
    at observation; otherwise we record [None], for which no invariant
    is asserted.  At CAS-success this invariant, combined with the
    completeness of [obs] over [0..j_e-1], discharges the minimality
    of the dequeued [k_e] in [absq_min O lt]. *)
  (∀ τ obs rng_τ r b,
    op_map !! τ = Some {| op_info_kind := OpDeq obs rng_τ;
                          op_info_reserved := r;
                          op_info_stored := b |} →
    b = false →
    ∀ j k', (j, Some k') ∈ obs →
      stored_at !! k' = Some (Z.to_nat j) ∧ k' ∉ s.(absq_O)) ∧
  (* Lt-reservation bound (V-lt-reservations, task #47).  Every
    [lt]-edge [(k, k_e)] in the AbsQ state bounds the stored position
    of [k] strictly below [k_e]'s reserved position (when those are
    defined).  The proof: [(k, k_e) ∈ lt] is added at [k_e]'s
    [CALL-ENQ] with [k ∈ absq_COMP], so [k] had stored (and
    [RET-ENQ1]'d) before [k_e]'s [CALL-ENQ].  Via back-monotonicity:
    [r_k < back-at-[k]'s-FAA-post < back-at-[k_e]'s-CALL ≤ r_e].  Used
    at the dequeue CAS-success to force any [lt]-predecessor of [k_e]
    into the observation range [[0, j_e - 1]]. *)
  (∀ k k_e d r_e b,
    (k, k_e) ∈ s.(absq_lt) →
    op_map !! k_e = Some {| op_info_kind := OpEnq d;
                            op_info_reserved := Some r_e;
                            op_info_stored := b |} →
    ∀ r_k, stored_at !! k = Some r_k → r_k < Z.to_nat r_e) ∧
  (* Observation-list structural invariant (task #47).  For each
    pre-LIN dequeue τ with [op_map τ = OpDeq obs _ false], the observed
    list has exactly one entry per iterated offset, in ascending order:
    [obs !! i = Some (Z.of_nat i, _)] for every [i < length obs].
    Combined with the WP-level length invariant [length obs = Z.to_nat
    (rng - i)], this lets the CAS-success proof look up the obs entry
    corresponding to any [lt]-predecessor's stored offset [r_k' < j_e]. *)
  (∀ τ obs rng_τ r b,
    op_map !! τ = Some {| op_info_kind := OpDeq obs rng_τ;
                          op_info_reserved := r;
                          op_info_stored := b |} →
    b = false →
    ∀ i : nat, (i < length obs)%nat →
      ∃ k_opt, obs !! i = Some (Z.of_nat i, k_opt)) ∧
  (* COMP-stored (task #47).  Any [COMP] enqueue has a [stored_at] entry
    (COMP is reached via [RET-ENQ1], which fires only after the store
    step writes to [stored_at]).  Used at CAS-success to lift [(k', k_e)
    ∈ lt] (giving [ℓ[k'] = (_, COMP)] via [absq_wf_lt_COMP]) into a
    [stored_at k' = Some r_k'] witness. *)
  (∀ k d, s.(absq_l) !! k = Some (d, COMP) →
    ∃ r, stored_at !! k = Some r) ∧
  (* Lt-stored bound (task #47).  The stored_at-based form of
    [Hlt_res]: every [lt]-edge [(k, k_e)] bounds [r_k < r_k_e] when
    both have [stored_at] entries.  Derivable from [Hlt_res] at store
    steps (where the new [stored_at k_e] is added alongside an OpEnq
    fragment); useful at CAS-success even when [k_e] has already
    retired ([op_map k_e = None]), bypassing [Hlt_res]'s op_map-based
    pattern. *)
  (∀ k k_e r_k r_k_e,
    (k, k_e) ∈ s.(absq_lt) →
    stored_at !! k = Some r_k →
    stored_at !! k_e = Some r_k_e →
    r_k < r_k_e) ∧
  (* [rng_τ] monotonicity (task #47).  [rng_τ] is the [back_val]
    snapshot stored in τ's [OpDeq] fragment at [CALL-DEQ] or at each
    outer-Löb reset; since [back] only increases via [FAA], any such
    snapshot stays ≤ the current [back_val]. *)
  (∀ τ obs rng_τ r b,
    op_map !! τ = Some {| op_info_kind := OpDeq obs rng_τ;
                          op_info_reserved := r;
                          op_info_stored := b |} →
    (rng_τ ≤ back_val)%Z) ∧
  (* [lt] → obs Some-ness (task #47).  For a pre-LIN dequeue τ with
    [op_map τ = OpDeq obs rng_τ false], and any [lt]-edge [(k, k_e)]
    whose [k_e] is in [op_map] with reservation [Some r_e < rng_τ]: if
    [stored_at k = Some r_k] with [r_k < length obs], then τ's obs
    entry at position [r_k] must be [Some (_, Some k'')] (not [None]).

    At [CAS-success] with [k_e] currently stored (pre-[LIN-DEQ1]), we
    have [r_e = length obs < rng_τ] (WP-level [i ≥ 1] gives [rng - i <
    rng ≤ rng_τ]).  Combined with [Hlt_stored]'s [r_k < r_e] and
    [Hobs_struct], this rules out the [None]-branch of the minimality
    discharge.  Preservation at [FAA] of some [k_e_new] is vacuous
    because [Hrng_τ_bound] gives [rng_τ ≤ back_val = r_e_new], so [r_e
    < rng_τ] fails.  Preservation at obs-extension (None branch) is
    vacuous because the branch was taken under [∀ k, stored_at k ≠
    Some (Z.to_nat (rng - i))]. *)
  (∀ τ obs rng_τ r,
    op_map !! τ = Some {| op_info_kind := OpDeq obs rng_τ;
                          op_info_reserved := r;
                          op_info_stored := false |} →
    ∀ k k_e d r_e b_e,
      (k, k_e) ∈ s.(absq_lt) →
      op_map !! k_e = Some {| op_info_kind := OpEnq d;
                              op_info_reserved := Some r_e;
                              op_info_stored := b_e |} →
      (r_e < rng_τ)%Z →
      ∀ r_k, stored_at !! k = Some r_k →
        (r_k < length obs)%nat →
        ∃ k'', obs !! r_k = Some (Z.of_nat r_k, Some k'')) ∧
  (* [lt] → obs stored_at-form (task #47).  The [stored_at]-based
    sibling of [Hlt_res_obs]: applies even when [k_e] has retired via
    [RET-ENQ1] (so [op_map k_e = None]).  Preservation at [Store] of
    [k_e_new] follows from the [op_map]-form pre-step IH; at
    [RET-ENQ1] of [k_e] the [stored_at] entry persists and the [obs]
    list is unchanged.  Used at the CAS-success discharge when [k_e]
    has already retired to [COMP]. *)
  (∀ τ obs rng_τ r,
    op_map !! τ = Some {| op_info_kind := OpDeq obs rng_τ;
                          op_info_reserved := r;
                          op_info_stored := false |} →
    ∀ k k_e r_k_e,
      (k, k_e) ∈ s.(absq_lt) →
      stored_at !! k_e = Some r_k_e →
      (Z.of_nat r_k_e < rng_τ)%Z →
      ∀ r_k, stored_at !! k = Some r_k →
        (r_k < length obs)%nat →
        ∃ k'', obs !! r_k = Some (Z.of_nat r_k, Some k'')).

Lemma fs1_sim_init valid_value sz :
  (0 ≤ sz)%Z →
  fs1_sim valid_value sz (replicate (Z.to_nat sz) NONEV) 0 absq_init ∅ ∅ [].
Proof.
  intros Hsz.
  rewrite /fs1_sim /absq_init /=.
  split_and!.
  - by rewrite length_replicate.
  - lia.
  - intros i Hi. apply lookup_replicate_2. lia.
  - set_solver.
  - set_solver.
  - intros τ d r. rewrite lookup_empty. done.
  - intros τ obs rng_τ r b. rewrite lookup_empty. done.
  - intros τ τ' d d' i. rewrite lookup_empty. done.
  - intros i Hi. left. apply lookup_replicate_2. lia.
  - intros i d Hitems_i.
    rewrite lookup_replicate in Hitems_i. destruct Hitems_i as [Heq _].
    inversion Heq.
  - intros τ i Hlookup. rewrite lookup_empty in Hlookup. discriminate.
  - intros τ₁ τ₂ i H1. rewrite lookup_empty in H1. discriminate.
  - intros i d Hitems_i.
    rewrite lookup_replicate in Hitems_i. destruct Hitems_i as [Heq _].
    inversion Heq.
  - intros τ d r. rewrite lookup_empty. done.
  - intros τ d i. rewrite lookup_empty. done.
  - intros τ d r. rewrite lookup_empty. done.
  - intros τ obs rng_τ r b. rewrite lookup_empty. done.
  - intros k k_e d r_e b Hlt. set_solver.
  - intros τ obs rng_τ r b. rewrite lookup_empty. done.
  - intros k d Hℓ. rewrite lookup_empty in Hℓ. discriminate.
  - intros k k_e r_k r_k_e Hlt. set_solver.
  - intros τ obs rng_τ r b. rewrite lookup_empty. done.
  - intros τ obs rng_τ r. rewrite lookup_empty. done.
  - intros τ obs rng_τ r. rewrite lookup_empty. done.
Qed.

(** Iterated [absq_wf_step] over [absq_steps]: every state reachable
  from a wellformed one is itself wellformed.  Used in [op_spec]
  to derive [dom ℓ ⊆ dom cp] at CALL-ENQ from the [Hsteps] hypothesis
  carried in the HWQ invariant. *)
Lemma absq_wf_steps (rme : response_mayempty) (valid_value : val → Prop) (s0 : absq_state) ls s :
  absq_steps rme valid_value s0 ls s → absq_wf valid_value s0 → absq_wf valid_value s.
Proof.
  induction 1 as [|s0' s1' s2' l' ls' Hstep Hrest IH]; auto.
  intros Hwf0. apply IH. by eapply absq_wf_step.
Qed.

(** [gmap]-image decidability: a finite map either has some key mapping
  to a specific value, or no key does.  Used in the dequeue observation
  step to case-split on whether the loaded offset already has a storer
  in [stored_at]; the [Some k'] branch records that storer in the
  [OpDeq] observation list, the [None] branch records that no storer
  existed at that moment. *)
Lemma gmap_image_dec {K A : Type} `{EqDecision K, Countable K, EqDecision A}
  (m : gmap K A) (v : A) :
  (∃ k, m !! k = Some v) ∨ (∀ k, m !! k ≠ Some v).
Proof.
  induction m as [|k v' m Hk IH] using map_ind.
  - right. intros k. by rewrite lookup_empty.
  - destruct (decide (v' = v)) as [->|Hne].
    + left. exists k. by rewrite lookup_insert_eq.
    + destruct IH as [[k' Hk']|Hne_all].
      * left. exists k'.
        destruct (decide (k' = k)) as [->|Hne_k].
        { rewrite Hk in Hk'. discriminate. }
        rewrite lookup_insert_ne; done.
      * right. intros k'.
        destruct (decide (k' = k)) as [->|Hne_k].
        { rewrite lookup_insert_eq. intros [=]. by apply Hne. }
        rewrite lookup_insert_ne; last done. by apply Hne_all.
Qed.

(* ========================================================================= *)

Section hwq_skeleton.
  Context `{!traceG Σ, !hwqG Σ}.
  Context (sz : Z).
  Hypothesis sz_pos : (0 < sz)%Z.

  (** Pin [valid_value] to [hwq_valid_value] inside this section so the
    [absq_steps]/[absq_wf]/[fs1_sim] arguments line up with [I_lang_hwq]. *)
  Local Notation valid_value := hwq_valid_value.
  Lemma valid_value_unbox d : valid_value d → val_is_unboxed (SOMEV d).
  Proof. done. Qed.

  Definition Nhwq : namespace := nroot .@ "hwq".

  Section with_heapGS.
    Context `{!heapGS Σ}.

  (* ======================================================================= *)
  (* Concrete [is_hwq]: an Iris invariant at namespace [Nhwq] owning the
    array cells, the back counter, the trace-is resource at the tracer
    [l], and a ghost [op_map] tracked via an authoritative gmap.  The
    invariant body existentially quantifies over the current AbsQ
    witness [(s, ls)] and maintains [fs1_sim] between the physical
    state and that witness. *)

  (* [cell_val_inv]: every storer's value is recorded in
    [cell_val_map] at the stored offset.  Forward direction links
    storer ℓ entries to the persistent cell-value map; used at
    observations (e.g., outer iInv SOMEV-d load) to extract a
    persistent [agreeR] frag that survives iInv close/re-open.  The
    [agreeR] camera freezes the value at that offset, giving
    cross-iInv witnesses for the SOMEV-e CAS-fail discharge. *)
  Definition cell_val_inv
    (stored_at : gmap positive nat) (s : absq_state)
    (cell_val_map : gmap nat val) : Prop :=
    (∀ τ i d f, stored_at !! τ = Some i → s.(absq_l) !! τ = Some (d, f) →
       cell_val_map !! i = Some d) ∧
    (∀ i v, cell_val_map !! i = Some v →
       ∃ τ f, stored_at !! τ = Some i ∧ s.(absq_l) !! τ = Some (v, f)).

  (* [dq_inv]: every recorded dequeue result [d] in [dq_map]
    corresponds to an option-encoded [SOMEV d] in [absq_rv]. The
    raw form lives in [dq_map] because [dequeue] returns the raw
    array entry; the option wrapping is added by [op] above
    [dequeue] and recorded in the abstract [absq_rv] by
    [absq_step_lin_deq1]. Allocated at CAS-success in deq_cont
    (where [absq_step_lin_deq1] simultaneously sets [rv τ := SOMEV d]);
    preserved trivially at every other step since neither [dq_map]
    nor [rv] changes. *)
  Definition dq_inv
    (dq_map : gmap positive val) (s : absq_state) : Prop :=
    ∀ τ d, dq_map !! τ = Some d → s.(absq_rv) !! τ = Some (SOMEV d).

  Definition hwq_inv_body
    (γ_op γ_sv γ_dq : gname) (ar back : loc) (l : loc) : iProp Σ :=
    ∃ (items : list val) (back_val : Z)
      (ts : list (positive * trace))
      (s : absq_state) (ls : list (positive * absq_action))
      (op_map : gmap positive op_info)
      (stored_at : gmap positive nat)
      (cell_val_map : gmap nat val)
      (dq_map : gmap positive val),
      back ↦ #back_val ∗
      ar ↦∗ items ∗
      trace_is l ts ∗
      own γ_op (● to_opmap op_map) ∗
      own γ_sv (● to_svmap cell_val_map) ∗
      own γ_sv (◯ to_svmap cell_val_map) ∗
      own γ_dq (● to_dqmap dq_map) ∗
      own γ_dq (◯ to_dqmap dq_map) ∗
      ⌜absq_steps NeverEmpty valid_value absq_init ls s⌝ ∗
      ⌜ts = filter (not ∘ is_lin ∘ snd) (trace_of_absq_labels ls)⌝ ∗
      ⌜fs1_sim valid_value sz items back_val s op_map stored_at ts⌝ ∗
      ⌜cell_val_inv stored_at s cell_val_map⌝ ∗
      ⌜dq_inv dq_map s⌝.

  Definition is_hwq (l : loc) (γ : gname) (obj : val) : iProp Σ :=
    ∃ (ar back : loc) (γ_sv γ_dq : gname),
      ⌜obj = (#sz, #ar, #back)%V⌝ ∗
      inv Nhwq (hwq_inv_body γ γ_sv γ_dq ar back l).

  Global Instance is_hwq_pers γ v l : Persistent (is_hwq γ v l).
  Proof. apply _. Qed.
  End with_heapGS.

  (* The [repr] instance fed into [bdgjst_free]. *)
  Definition hwq_repr : mgc_repr Σ := {|
    I_lang := I_lang_hwq;
    mgc_inv := @is_hwq;
  |}.

  (* ======================================================================= *)
  (* Spec obligations. A concrete HWQ verification discharges both. *)

  (* Init wrapper: [bdgjst_free] requires an [init : val] that
    takes [#()]. We partially apply [new_queue] to the desired size. *)
  Definition init_hwq : val := (λ: <>, new_queue #sz)%V.

End hwq_skeleton.
