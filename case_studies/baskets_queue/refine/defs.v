(* refine_defs.v: shared definitions for the Baskets-Queue refinement
  proof.  Mirrors the structure of [hw_queue/refine_defs.v]: ghost
  state, the trace invariant [I_lang_bq], the forward-simulation
  predicate [bq_sim] (analogue of HWQ's [fs1_sim]), the [absq_wf_steps]
  helper inherited by chaining, and the [Section bq_skeleton]
  definitions consumed by the per-method proofs ([Nbq], [bq_inv_body],
  [is_bq], [bq_repr], [init_bq]).

  Future-dependent linearisation points.  Two enqueues falling into
  the same basket overlap in time, so neither is [COMP] at the other's
  [CALL-ENQ] and the abstract relation [absq_lt] has no edge between
  them.  Their basket-internal FIFO order is therefore decided only at
  dequeue time.  In the simulation we key the per-enqueue ghost
  fragment by an abstract *node identity* — the heap location of the
  enqueueing node — not by an array index, since several pending
  enqueues can sit at "the same" basket position simultaneously. *)

From iris.algebra Require Import auth excl gmap gset agree mono_nat mono_list.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import invariants.
From iris_logatom.program_logic Require Import atomic_complete.
From iris.heap_lang Require Import adequacy primitive_laws notation proofmode.
From iris_logatom.heap_lang Require Import mgc fork_free.
From iris_logatom.heap_lang.lib Require Import trace.
From iris_logatom.pure_logic Require Import linear adequacy.
From iris_logatom.pure_logic.models Require Import bag_like.
From iris_logatom.pure_logic.refine Require Import absq absq_refines_absq0
                                                    absq0_linearizable
                                                    backward_simulation.

From case_studies.baskets_queue Require Import impl.

(* ========================================================================= *)
(** ** Per-operation ghost metadata.

    [op_kind]:
      - [OpEnq d]: an enqueue of value [d]; tracks [d] explicitly so
        that the ghost fragment owned by the enqueue thread carries
        the value being inserted.
      - [OpDeq observed rng_τ]: a dequeue in progress.  As in HWQ,
        [observed] is the ordered log of marked-prefix nodes the
        dequeue's walk has visited (along with the storer-identifier
        at the moment of the visit, when one exists in [node_at]);
        [rng_τ] is the tail-distance counter at the most recent outer
        retry, used by the simulation invariant to bound which
        [absq_lt]-predecessors can have been observed.

    [op_info]:
      - [op_info_kind]: as above.
      - [op_info_node]: for an enqueue, the heap location of [nd] once
        it has been allocated (i.e. after [E01]); [None] before.  For
        a dequeue, unused (always [None]).
      - [op_info_linked]: for an enqueue, [true] iff the basket-
        insertion CAS has succeeded and [nd] is reachable from the
        list head.  Pre-link, the fragment witnesses [τ ∈ absq_O ∧
        absq_l τ = (d, PEND)] without any list participation; post-
        link, it additionally witnesses that [op_info_node] equals the
        node currently storing [d] at some position in the list.  For
        a dequeue, the same field doubles as the post-LIN-DEQ flag
        ([true] iff [LIN-DEQ1]/[LIN-DEQ2] has fired). *)
Inductive op_kind : Set :=
  | OpEnq (d : val)
  | OpDeq (observed : list (loc * option positive)) (rng_τ : nat).

Record op_info : Set := {
  op_info_kind : op_kind;
  op_info_node : option loc;
  op_info_linked : bool;
}.

Global Instance op_kind_eqdec : EqDecision op_kind.
Proof. solve_decision. Defined.

Global Instance op_info_eqdec : EqDecision op_info.
Proof. solve_decision. Defined.

Definition opmapUR : ucmra := gmapUR positive (exclR (leibnizO op_info)).

Definition to_opmap (m : gmap positive op_info) : gmap positive (excl (leibnizO op_info)) :=
  Excl <$> m.

(* [nodemapUR]: [agreeR]-keyed map recording, for each heap location
  ever used as a node, the unique enqueue identifier that allocated it
  and the unique value it stores at offset 0.  Persistent fragments
  let separate invariant openings agree on a node's identifier and
  value across CAS retries.  The map has the same role as HWQ's
  [stored_at] together with [cell_val_map], merged into a single
  agree-typed structure because here both pieces of data are
  immutable once the node is allocated. *)
(* The dummy gets [None] for its identifier (it was allocated by
  [new_queue], not via [trace_fresh]); real enqueues' nodes get
  [Some τ] where [τ] is the enqueue's [trace_fresh]-allocated id.
  Using [option positive] keeps the dummy's "identifier" structurally
  distinct from any real enqueue's, so [trace_fresh] can never clash
  with it — no sentinel-collision concerns. *)
Definition node_info : Type := option positive * val.
Definition nodemapUR : ucmra := gmapUR loc (agreeR (leibnizO node_info)).

Definition to_nodemap (m : gmap loc node_info) : gmap loc (agree (leibnizO node_info)) :=
  to_agree <$> m.

(* [dqmapUR]: same role as in HWQ — agreement on the option-encoded
  return value of each dequeue, established at LIN-DEQ and consumed
  at RET-DEQ. *)
Definition dqmapUR : ucmra := gmapUR positive (agreeR (leibnizO val)).

Definition to_dqmap (m : gmap positive val) : gmap positive (agree (leibnizO val)) :=
  to_agree <$> m.

(* [witnessmapUR]: per-pending-enqueue chain snapshot.  When an enqueue
  τ in [op_spec_enq_cont] observes [tail.next = InjLV #()] at
  phase 4, we mint a persistent fragment recording the chain at that
  moment.  The fragment witnesses "at past inv-open during τ's body,
  chain was [snap] with [tail] at the chain-end".  Used in
  [op_spec_enq_basket]'s splice-success branch to derive that
  every [(k, τ) ∈ absq_lt] has its chain location in [snap] (k was
  COMP at τ.CALL hence linked at τ.CALL ≤ phase 4 mint), which in
  turn — combined with the chain-monotonicity property
  [Sublist snap nodes] — bounds k's current chain position by [tail]'s
  current position. *)
(* The witness records the chain at mint time (snap) for an enqueue τ
   that observed [tail_loc.next = InjLV #()] at phase 4 with [tail_loc]
   as the captured tail.  At mint, we use snap = [nodes_4] (the entire
   chain), valid because [tail_loc.next = #()] entails [tail_loc] is at
   the chain end, so [snap = take (length nodes_4) nodes_4 = nodes_4]
   and [snap !! (length snap - 1) = Some (tail_loc, _, _)] holds.

   Witnesses are keyed by [(τ, tail_loc)] so that the iLöb-driven
   re-entry to phase 4 (with potentially different [tail_val]) can mint
   a fresh witness at the new key without conflicting with the iter-1
   mint.  When the same [tail_val] is seen across iterations, the auth
   already has the entry and we extract it instead of minting. *)
Definition chain_snapshot : Type := list (loc * option positive * val).
Definition witnessmapUR : ucmra :=
  gmapUR (positive * loc) (agreeR (leibnizO chain_snapshot)).

Definition to_witnessmap (m : gmap (positive * loc) chain_snapshot)
  : gmap (positive * loc) (agree (leibnizO chain_snapshot)) := to_agree <$> m.

Class bqG Σ := BqG {
  bqG_op_inG :: inG Σ (authR opmapUR);
  bqG_node_inG :: inG Σ (authR nodemapUR);
  bqG_dq_inG :: inG Σ (authR dqmapUR);
  bqG_del_inG :: inG Σ mono_natR;
  bqG_calls_inG :: inG Σ (authR (gsetUR positive));
  bqG_ls_inG :: inG Σ (mono_listR (leibnizO (positive * absq_action)));
  bqG_witness_inG :: inG Σ (authR witnessmapUR);
}.

Global Instance absq_state_inhabited : Inhabited absq_state := populate absq_init.

Definition bqΣ : gFunctors := #[ GFunctor (authR opmapUR);
                                 GFunctor (authR nodemapUR);
                                 GFunctor (authR dqmapUR);
                                 GFunctor (mono_natR);
                                 GFunctor (authR (gsetUR positive));
                                 GFunctor (mono_listR (leibnizO (positive * absq_action)));
                                 GFunctor (authR witnessmapUR) ].

Global Instance subG_bqΣ Σ : subG bqΣ Σ → bqG Σ.
Proof. solve_inG. Qed.

(* ========================================================================= *)
(** ** Trace invariant. *)

(** Baskets queue stores values directly inside heap cells but our
  encoded [next] field uses [InjL]/[InjR] of unboxed literals; an
  unboxed [d] is sufficient for the [enq_basket] CAS payload [InjL
  #nd] (location, always unboxed).  We additionally require
  [val_is_unboxed (SOMEV d)] so that [dequeue] can wrap its result in
  [SOMEV] safely (matching HWQ's convention). *)
Definition bq_valid_value : val → Prop :=
  λ v, val_is_unboxed (SOMEV v).

Definition I_lang_bq (ts : list (positive * trace)) : Prop :=
  ∃ s ls, absq_steps MayEmpty bq_valid_value absq_init ls s ∧
          ts = filter (not ∘ is_lin ∘ snd) (trace_of_absq_labels ls).

Lemma I_lang_bq_init : I_lang_bq [].
Proof.
  exists absq_init, []. split.
  - apply lts_steps_nil.
  - by rewrite /trace_of_absq_labels /= filter_nil.
Qed.

(* ========================================================================= *)
(** ** List-shape predicate.

    The physical state of the queue is a chain of nodes starting at
    the dummy.  We model it as a list [nodes : list (loc * positive *
    val)]: the head of the list is the dummy (whose [positive] tag is
    irrelevant — we use a sentinel [1%positive]), followed by the
    user-allocated nodes in *physical* (link-traversal) order.

    For each node [(l, τ, v)] in the list we own
      - [l] (offset 0) = [v] — the immutable value cell;
      - [l +ₗ 1] = [next_field], the tagged pointer for [l]'s next
        link.  The encoding is given by [next_value_of] below.

    Marks form a prefix: there is some [d ≤ length nodes - 1] such
    that the first [d] non-dummy nodes are logically deleted (their
    *predecessor's* next pointer is marked).  The unmarked suffix is
    the live queue.  See [bq_marked_prefix] below. *)

(** Tagged-pointer encoding consumed by [bq_chain].
    [(unmarked, None)] is unmarked-null;
    [(unmarked, Some l')] is unmarked-pointer to [l'];
    [(marked, _)] is the corresponding marked variant. *)
Definition next_value_of (marked : bool) (succ : option loc) : val :=
  match marked, succ with
  | false, None    => InjLV #()
  | false, Some l' => InjLV #l'
  | true,  None    => InjRV #()
  | true,  Some l' => InjRV #l'
  end.

(* ========================================================================= *)
(** ** The simulation predicate [bq_sim].

    [bq_sim] relates the physical queue state (the chain [nodes], the
    marked prefix length [del_pref], the values of [head]/[tail], and
    the ghost maps [op_map], [node_map], [dq_map]) to an AbsQ witness
    [s] and the externally-projected trace [ts].

    The clauses captured here:
      - chain shape and head/tail position;
      - the marked-prefix invariant;
      - freshness of trace ids;
      - domain containment between [op_map] and [absq_cp];
      - the per-enqueue clause (pre/post-link cases);
      - the per-dequeue clause (pre/post-LIN cases);
      - injectivity of [op_info_node];
      - bookkeeping linking [node_map] to [absq_l] and the chain;
      - happens-before/list-order compatibility:
          [(τ_a, τ_b) ∈ absq_lt → τ_a is listed before τ_b in [nodes]];
      - the dequeue observation-history invariants needed to discharge
        minimality of the dequeued [k_e] in [absq_min O lt]. *)
Definition bq_sim
  (valid_value : val → Prop)
  (nodes : list (loc * option positive * val))
                                         (* dummy at position 0 has [None];
                                            real enqueues at positions ≥ 1
                                            have [Some τ] from [trace_fresh] *)
  (del_pref : nat)                        (* marked-prefix length *)
  (head_loc tail_loc : loc)
  (s : absq_state)
  (op_map : gmap positive op_info)
  (node_map : gmap loc node_info)
  (ts : list (positive * trace))
  : Prop :=
  (* 1. Chain non-empty (dummy is always present). *)
  (1 ≤ length nodes)%nat ∧
  (* 2. Mark-prefix length is well-formed. *)
  (del_pref < length nodes)%nat ∧
  (* 3. Freshness of trace ids: every identifier used in AbsQ has
        already appeared in the trace, so a fresh trace [τ] is fresh in
        [absq_cp]. *)
  dom s.(absq_cp) ⊆ list_to_set ts.*1 ∧
  (* 4. Domain containment between op_map and absq_cp. *)
  dom op_map ⊆ dom s.(absq_cp) ∧
  (* 5. Node-map → chain.  Every recorded [(l, (τ_opt, d))] entry
        corresponds to a chain position carrying [(l, τ_opt, d)] —
        either position 0 (the dummy, with [τ_opt = None]) or a
        position [i ≥ 1] established at the linking splice CAS in some
        completed-or-in-flight enqueue (with [τ_opt = Some τ]).
        Pending unlinked allocations are *not* in [node_map]; they
        are tracked solely through [op_map]. *)
  (∀ l τ_opt d, node_map !! l = Some (τ_opt, d) →
     ∃ i, nodes !! i = Some (l, τ_opt, d)) ∧
  (* 6. Per-enqueue clause.  An [OpEnq d] entry in [op_map] sits at
        AbsQ control point [A1] with [absq_l] = [(d, PEND)].  When
        [linked = true], the enqueue's node is in the chain at a
        position [i ≥ 1] tagged with [Some τ], consistent with
        [absq_O] membership iff [del_pref < i]. *)
  (∀ τ d node linked,
     op_map !! τ = Some {| op_info_kind := OpEnq d;
                            op_info_node := node;
                            op_info_linked := linked |} →
     s.(absq_cp) !! τ = Some A1 ∧
     s.(absq_l) !! τ = Some (d, PEND) ∧
     (linked = false → τ ∈ s.(absq_O)) ∧
     (linked = true → ∃ l i,
        node = Some l ∧
        (1 ≤ i)%nat ∧ nodes !! i = Some (l, Some τ, d) ∧
        node_map !! l = Some (Some τ, d) ∧
        (τ ∈ s.(absq_O) ↔ (del_pref < i)%nat))) ∧
  (* 7. Per-dequeue clause. *)
  (∀ τ obs rng node linked,
     op_map !! τ = Some {| op_info_kind := OpDeq obs rng;
                            op_info_node := node;
                            op_info_linked := linked |} →
     node = None ∧
     (linked = false → s.(absq_cp) !! τ = Some R1) ∧
     (linked = true → s.(absq_cp) !! τ = Some R2 ∧
                       ∃ v, s.(absq_rv) !! τ = Some v)) ∧
  (* 8. Node-id injectivity in the chain: distinct positions ≥ 1
        with [Some τ_i] / [Some τ_j] tags carry distinct τ. *)
  (∀ i j l_i l_j τ d_i d_j,
     (1 ≤ i)%nat → (1 ≤ j)%nat →
     nodes !! i = Some (l_i, Some τ, d_i) →
     nodes !! j = Some (l_j, Some τ, d_j) →
     i = j) ∧
  (* 9. Node-list correspondence.  Every non-dummy node (position [i ≥
        1] with [Some τ] tag) has a [node_map] entry consistent with
        [absq_l], and its [absq_O] membership matches its mark-prefix
        status. *)
  (∀ i l τ v,
     (1 ≤ i)%nat → nodes !! i = Some (l, Some τ, v) →
     node_map !! l = Some (Some τ, v) ∧
     (∃ f, s.(absq_l) !! τ = Some (v, f)) ∧
     (τ ∈ s.(absq_O) ↔ (del_pref < i)%nat)) ∧
  (* 10. Happens-before respects list order. *)
  (∀ k k_e, (k, k_e) ∈ s.(absq_lt) →
     ∃ p_k l_k d_k,
       (1 ≤ p_k)%nat ∧ nodes !! p_k = Some (l_k, Some k, d_k) ∧
       (∀ p_ke l_ke d_ke,
          (1 ≤ p_ke)%nat →
          nodes !! p_ke = Some (l_ke, Some k_e, d_ke) → (p_k < p_ke)%nat)) ∧
  (* 11. Dequeue observation invariants — TBD. *)
  True ∧
  (* 12. COMP enqueues are already linked. *)
  (∀ τ d, s.(absq_l) !! τ = Some (d, COMP) →
     ∃ p l, (1 ≤ p)%nat ∧ nodes !! p = Some (l, Some τ, d)) ∧
  (* 13. Tail-pointer is a chain location. *)
  (∃ i τ_t v_t, (i < length nodes)%nat ∧
     nodes !! i = Some (tail_loc, τ_t, v_t)) ∧
  (* 14. Head-pointer is some chain location within the marked prefix. *)
  (∃ i_h τ_h v_h, (i_h ≤ del_pref)%nat ∧
     nodes !! i_h = Some (head_loc, τ_h, v_h)) ∧
  (* 15. Chain → node_map.  Every chain location, including the dummy
        at position 0, has a [node_map] entry recording its identifier
        tag and value.  Combined with the persistent agreement on
        [node_map], the per-method WPs extract a persistent fragment
        for any observed chain location and re-use it across an [Nbq]
        close/reopen. *)
  (∀ i l τ_opt v, nodes !! i = Some (l, τ_opt, v) → node_map !! l = Some (τ_opt, v)) ∧
  (* 16. Non-dummy positions carry [Some τ] tags.  The dummy at
        position 0 is the only chain entry with [None] for its
        identifier; every node added by a splice/basket CAS in
        [enqueue] uses the enqueueing thread's [Some τ] from
        [trace_fresh].  This is what lets [τ : option positive] from
        clause 14 / 5 be unwrapped to a real [positive] when [i ≥ 1],
        without any sentinel-collision concerns. *)
  (∀ i l τ_opt v, (1 ≤ i)%nat → nodes !! i = Some (l, τ_opt, v) →
     ∃ τ, τ_opt = Some τ).

Lemma bq_sim_init valid_value (l : loc) :
  bq_sim valid_value [(l, None, #())] 0%nat l l absq_init ∅
         {[l := (None, #())]} [].
Proof.
  rewrite /bq_sim /absq_init.
  split_and!.
  - simpl. lia.
  - simpl. lia.
  - simpl. set_solver.
  - simpl. set_solver.
  - intros l' τ_opt d Hlk.
    destruct (decide (l' = l)) as [->|Hne].
    + rewrite lookup_singleton_eq in Hlk. injection Hlk as <- <-.
      exists 0%nat. reflexivity.
    + rewrite lookup_singleton_ne in Hlk; [discriminate|done].
  - intros τ d node linked Hlk. rewrite lookup_empty in Hlk. discriminate.
  - intros τ obs rng node linked Hlk. rewrite lookup_empty in Hlk. discriminate.
  - intros i j l_i l_j τ d_i d_j Hi Hj Hlu_i Hlu_j.
    destruct i as [|i]; [lia|]. destruct j as [|j]; [lia|].
    rewrite lookup_cons in Hlu_i. rewrite lookup_cons in Hlu_j.
    rewrite lookup_nil in Hlu_i, Hlu_j. discriminate.
  - intros i l' τ v Hi Hlu.
    destruct i as [|i]; [lia|].
    rewrite lookup_cons lookup_nil in Hlu. discriminate.
  - intros k k_e Hlt. simpl in Hlt. set_solver.
  - done.
  - intros τ d Hℓ. rewrite lookup_empty in Hℓ. discriminate.
  - exists 0%nat, None, #(). split; [simpl; lia|reflexivity].
  - exists 0%nat, None, #(). split; [lia|reflexivity].
  - intros i l' τ_opt v Hi.
    destruct i as [|i]; [|rewrite lookup_cons lookup_nil in Hi; discriminate].
    rewrite lookup_cons in Hi. injection Hi as <- <- <-.
    by rewrite lookup_singleton_eq.
  - intros i l' τ_opt v Hi_pos Hlu.
    destruct i as [|i]; [lia|].
    rewrite lookup_cons lookup_nil in Hlu. discriminate.
Qed.

(** Iterated [absq_wf_step] over [absq_steps]: every state reachable
    from a wellformed one is itself wellformed. *)
Lemma absq_wf_steps (rme : response_mayempty) (valid_value : val → Prop) (s0 : absq_state) ls s :
  absq_steps rme valid_value s0 ls s → absq_wf valid_value s0 → absq_wf valid_value s.
Proof.
  induction 1 as [|s0' s1' s2' l' ls' Hstep Hrest IH]; auto.
  intros Hwf0. apply IH. by eapply absq_wf_step.
Qed.

(** [absq_steps] preserves [τ ∈ dom absq_cp] (CALL-* only adds, never
    removes; RET-* / LIN-* only update existing entries). *)
Lemma absq_steps_cp_mono (rme : response_mayempty) (valid_value : val → Prop) (s0 : absq_state) ls s :
  absq_steps rme valid_value s0 ls s → dom s0.(absq_cp) ⊆ dom s.(absq_cp).
Proof.
  induction 1 as [|s0' s1' s2' l' ls' Hstep Hrest IH]; first done.
  etrans; [|exact IH]. clear IH Hrest.
  inversion Hstep; subst; simpl; rewrite dom_insert_L; set_solver.
Qed.

(** Stickiness of [τ ∉ absq_O] given [τ ∈ dom absq_cp].

    The empty-dequeue branch of [op_spec_deq_cont] needs to lift
    [τ_h ∉ absq_O] from a past observation to the current state.  The
    only AbsQ rule that adds to [absq_O] is [CALL-ENQ], which uses an
    identifier [k] satisfying [k ∉ dom absq_cp]; if [τ ∈ dom absq_cp]
    initially, this [k] cannot equal [τ], so the new [absq_O] still
    excludes [τ].  Other rules either don't touch [absq_O] ([CALL-DEQ],
    [RET-*], [LIN-DEQ2]) or shrink it ([LIN-DEQ1]).

    Combined with [absq_steps_cp_mono] (so [τ ∈ dom absq_cp] persists
    along the trajectory), this proves that [τ ∉ absq_O] is sticky. *)
Lemma absq_steps_O_sticky (rme : response_mayempty) (valid_value : val → Prop) (s0 : absq_state) ls s τ :
  absq_steps rme valid_value s0 ls s →
  τ ∈ dom s0.(absq_cp) →
  τ ∉ s0.(absq_O) →
  τ ∉ s.(absq_O).
Proof.
  induction 1 as [|s0' s1' s2' l' ls' Hstep Hrest IH]; auto.
  intros Hcp Hno_O. apply IH.
  - (* τ ∈ dom s1'.absq_cp. *)
    inversion Hstep; subst; simpl in *; rewrite dom_insert_L; set_solver.
  - (* τ ∉ s1'.absq_O. *)
    inversion Hstep as
      [O0 lt0 ℓ0 rv0 cp0 k0 d0 Hk0_notin Hvalid0
      |O0 lt0 ℓ0 rv0 cp0 k0 Hk0_notin
      |O0 lt0 ℓ0 rv0 cp0 k0 d0 Hcp0 Hk0_in Hℓ0
      |O0 lt0 ℓ0 rv0 cp0 k0 Hcp0 Hk0_notin
      |O0 lt0 ℓ0 rv0 cp0 k0 v0 Hcp0 Hrv0
      |O0 lt0 ℓ0 rv0 cp0 k0 k0' d0 f0 Hcp0 Hmin0 Hℓ0
      |O0 lt0 ℓ0 rv0 cp0 k0 Hcp0 HallPend0]; subst; simpl in *.
    + (* CALL-ENQ k0: O := O ∪ {k0}, k0 ∉ dom cp.  Since τ ∈ dom cp,
         k0 ≠ τ.  So τ ∉ O ∪ {k0}. *)
      assert (k0 ≠ τ) by set_solver. set_solver.
    + (* CALL-DEQ: O unchanged. *) done.
    + (* RET-ENQ1: O unchanged. *) done.
    + (* RET-ENQ2: O unchanged. *) done.
    + (* RET-DEQ: O unchanged. *) done.
    + (* LIN-DEQ1: O := O ∖ {k0'}.  τ ∉ O → τ ∉ O ∖ {k0'}. *) set_solver.
    + (* LIN-DEQ2: O unchanged. *) done.
Qed.

(** [absq_O ⊆ dom absq_l] is invariant: every identifier ever placed in
    [absq_O] was added by [CALL-ENQ], which simultaneously inserts it
    into [absq_l].  No other rule grows [absq_O], and only [LIN-DEQ1]
    shrinks it.  Used by the empty-dequeue branch of
    [op_spec_deq_cont] to discharge the [LIN-DEQ2] premise — it
    needs to invert [o ∈ O] into [∃ d f, absq_l !! o = Some (d, f)] so
    the case split on [f] can rule out [COMP] via the chain shape. *)
Lemma absq_steps_O_in_l (rme : response_mayempty) (valid_value : val → Prop) (s0 : absq_state) ls s :
  absq_steps rme valid_value s0 ls s →
  s0.(absq_O) ⊆ dom s0.(absq_l) →
  s.(absq_O) ⊆ dom s.(absq_l).
Proof.
  induction 1 as [|s0' s1' s2' l' ls' Hstep Hrest IH]; auto.
  intros HO_init. apply IH. clear IH Hrest.
  inversion Hstep; subst; simpl in *; rewrite ?dom_insert_L; set_solver.
Qed.

(* ========================================================================= *)
(** ** Heap representation of the chain.

    [bq_chain nodes] owns each node's two cells (offset-0 value, offset-1
    [next_field]) along the chain.  The next field of the dummy points
    to either the first non-dummy node or to [None]; in general
    position [i]'s next pointer references [nodes !! (i+1)] (or
    [None] at the end).  The mark on each next pointer is determined
    by the marked-prefix length [d]. *)
Section bq_heap.
  Context `{!heapGS Σ}.

  (** Successor location at chain position [i] (0-based).  The dummy
    lives at position 0; positions 1 .. length nodes - 1 are
    user-allocated nodes.  The successor of position [i] is the
    location at position [i+1] if any. *)
  Definition succ_at (nodes : list (loc * option positive * val)) (i : nat) : option loc :=
    match nodes !! (i + 1)%nat with
    | Some lτv => Some lτv.1.1
    | None => None
    end.

  (** Mark on position [i]'s next pointer: marked iff the *successor*
    (position [i+1]) lies in the deleted prefix.  In the convention
    inherited from the C code, "[N's next is marked]" means "[N]'s
    successor has been logically dequeued"; on the simulation side
    that is exactly [(i+1) ≤ del_pref]. *)
  Definition mark_at (del_pref : nat) (i : nat) : bool :=
    bool_decide (i + 1 ≤ del_pref)%nat.

  (** [bq_chain] is defined via [big_sepL] over the chain.  Each
    chain entry contributes its value cell ([l ↦ v]) and its next-
    field cell ([(l +ₗ 1) ↦ ...]).  The next-field's value is
    computed from the chain itself:
      - the mark bit at position [i] is [mark_at del_pref i];
      - the pointee is [succ_at nodes i] — i.e. the location of the
        node at index [i+1], or [None] if [i] is the last position.
    Defining the chain this way (rather than as a fixpoint) gives us
    [big_sepL_lookup_acc] / [big_sepL_insert_acc] for free; chain
    extension at the tail still needs a custom lemma because the
    OLD last node's next-field changes. *)
  Definition bq_chain (nodes : list (loc * option positive * val))
                      (del_pref : nat) : iProp Σ :=
    [∗ list] i ↦ x ∈ nodes,
      x.1.1 ↦ x.2 ∗
      (x.1.1 +ₗ 1) ↦ next_value_of (mark_at del_pref i) (succ_at nodes i).
End bq_heap.

(** [bq_chain_lookup_acc]: open one chain position. *)
Lemma bq_chain_lookup_acc `{!heapGS Σ} nodes del_pref i l (τ_opt : option positive) v :
  nodes !! i = Some (l, τ_opt, v) →
  bq_chain nodes del_pref ⊢
    l ↦ v ∗
    (l +ₗ 1) ↦ next_value_of (mark_at del_pref i) (succ_at nodes i) ∗
    (l ↦ v ∗ (l +ₗ 1) ↦ next_value_of (mark_at del_pref i) (succ_at nodes i)
       -∗ bq_chain nodes del_pref).
Proof.
  intros Hi.
  iIntros "Hch".
  iDestruct (big_sepL_lookup_acc _ _ i (l, τ_opt, v) Hi with "Hch") as "[Hcell HW]".
  simpl. iDestruct "Hcell" as "[Hv Hn]". iFrame "Hv Hn".
  iIntros "[Hv Hn]". iApply ("HW" with "[$Hv $Hn]").
Qed.

(** Inverse of [bq_chain_snoc]: extract the chain's last cell with
    its current next-pointer in hand, leaving the prefix.  Used in
    the CAS step to decompose [bq_chain] before flipping the last
    cell's next-pointer. *)
Lemma bq_chain_split_last `{!heapGS Σ}
  (nodes : list (loc * option positive * val)) (del_pref : nat)
  (l_t : loc) (τ_t : option positive) (v_t : val) :
  (1 ≤ length nodes)%nat →
  nodes !! (length nodes - 1)%nat = Some (l_t, τ_t, v_t) →
  bq_chain nodes del_pref ⊢
    ([∗ list] i ↦ x ∈ take (length nodes - 1) nodes,
       x.1.1 ↦ x.2 ∗
       (x.1.1 +ₗ 1) ↦ next_value_of (mark_at del_pref i) (succ_at nodes i)) ∗
    l_t ↦ v_t ∗
    (l_t +ₗ 1) ↦ next_value_of
      (mark_at del_pref (length nodes - 1)) (succ_at nodes (length nodes - 1)).
Proof.
  intros Hlen Hlt.
  iIntros "Hch".
  pose proof (take_drop_middle nodes _ _ Hlt) as Hsplit.
  set (n := length nodes) in *.
  assert (Datatypes.S (n - 1) = n) as HSn by lia.
  rewrite HSn drop_all in Hsplit. clear HSn.
  iEval (rewrite /bq_chain) in "Hch".
  iEval (rewrite -[X in big_sepL _ X]Hsplit) in "Hch".
  iEval (rewrite big_sepL_snoc) in "Hch".
  rewrite length_take_le; last lia.
  iDestruct "Hch" as "[$ [Hv Hn]]". simpl.
  by iFrame.
Qed.

(** [bq_chain_snoc]: extend the chain with one new node at the end.
    The OLD last node's next-cell must already have been updated to
    point to [new_l] (via the splice CAS), and the new node's cells
    must be in hand. *)
Lemma bq_chain_snoc `{!heapGS Σ} (nodes : list (loc * option positive * val))
  (l_t : loc) (τ_t : option positive) (v_t : val)
  (new_l : loc) (τ_new : option positive) (d_new : val) (del_pref : nat) :
  (1 ≤ length nodes)%nat →
  (del_pref < length nodes)%nat →
  nodes !! (length nodes - 1)%nat = Some (l_t, τ_t, v_t) →
  ([∗ list] i ↦ x ∈ take (length nodes - 1) nodes,
     x.1.1 ↦ x.2 ∗
     (x.1.1 +ₗ 1) ↦ next_value_of (mark_at del_pref i) (succ_at nodes i)) ∗
  l_t ↦ v_t ∗
  (l_t +ₗ 1) ↦ InjLV #new_l ∗
  new_l ↦ d_new ∗
  (new_l +ₗ 1) ↦ InjLV #() ⊢
  bq_chain (nodes ++ [(new_l, τ_new, d_new)]) del_pref.
Proof.
  intros Hlen Hdel Hlt.
  assert (Hsucc_new : succ_at (nodes ++ [(new_l, τ_new, d_new)]) (length nodes) = None)
    by (rewrite /succ_at lookup_app_r; [|lia];
        replace (length nodes + 1 - length nodes)%nat with 1%nat by lia; done).
  assert (Hmark_new : mark_at del_pref (length nodes) = false)
    by (rewrite /mark_at; apply bool_decide_eq_false_2; lia).
  assert (Hsucc_old : succ_at (nodes ++ [(new_l, τ_new, d_new)]) (length nodes - 1) = Some new_l)
    by (rewrite /succ_at;
        replace (length nodes - 1 + 1)%nat with (length nodes) by lia;
        rewrite lookup_app_r; [|lia];
        replace (length nodes - length nodes)%nat with 0%nat by lia; done).
  assert (Hmark_old : mark_at del_pref (length nodes - 1) = false)
    by (rewrite /mark_at; apply bool_decide_eq_false_2; lia).
  assert (Hsucc_pref : ∀ i, (i < length nodes - 1)%nat →
            succ_at (nodes ++ [(new_l, τ_new, d_new)]) i = succ_at nodes i)
    by (intros i Hi; rewrite /succ_at lookup_app_l; [done|lia]).
  iIntros "[Hpref [Hvt [Hnt [Hvnew Hnnew]]]]".
  iEval (rewrite /bq_chain).
  rewrite big_sepL_snoc. simpl.
  rewrite Hmark_new Hsucc_new /next_value_of.
  iFrame "Hvnew Hnnew".
  pose proof (take_drop_middle nodes _ _ Hlt) as Hsplit.
  assert (Datatypes.S (length nodes - 1) = length nodes) as HSn by lia.
  rewrite HSn drop_all in Hsplit. clear HSn.
  iEval (rewrite -[X in big_sepL _ X]Hsplit).
  rewrite big_sepL_snoc.
  rewrite length_take_le; last lia.
  simpl. rewrite Hmark_old Hsucc_old.
  iFrame "Hvt Hnt".
  iApply (big_sepL_mono with "Hpref").
  iIntros (k y Hk) "[Hv Hn]".
  apply lookup_lt_Some in Hk as Hk'.
  rewrite length_take_le in Hk'; last lia.
  rewrite (Hsucc_pref k Hk').
  iFrame.
Qed.

(** [bq_chain_insert]: middle-of-list insertion of a new node between
    [l_t] (at chain position [i_t]) and its successor [l_succ] (at
    chain position [i_t + 1]).  The OLD chain's [l_t] next-cell must
    already have been updated to point to [new_l] (via the splice
    CAS), and [new_l]'s next-cell must point to [l_succ].

    The condition [del_pref ≤ i_t] says that [l_t] is in the unmarked
    region of the chain — i.e., [l_t]'s mark and the new
    [new_l]/[l_succ] entries' marks all evaluate to [false] under the
    inserted-in chain.  The lemma's prefix and suffix cells are
    indexed against the OLD [nodes] (not the inserted-in chain), so
    callers don't have to re-shift indices.

    The structure is similar to [bq_chain_snoc] but with index-shifting
    for positions ≥ [i_t + 2] in the new chain.  *)
Lemma bq_chain_insert `{!heapGS Σ}
  (nodes : list (loc * option positive * val)) (del_pref : nat)
  (l_t : loc) (τ_t : option positive) (v_t : val) (i_t : nat)
  (l_succ : loc) (τ_succ : option positive) (v_succ : val)
  (new_l : loc) (τ_new : option positive) (d_new : val) :
  (del_pref ≤ i_t)%nat →
  nodes !! i_t = Some (l_t, τ_t, v_t) →
  nodes !! (i_t + 1)%nat = Some (l_succ, τ_succ, v_succ) →
  ([∗ list] j ↦ x ∈ take i_t nodes,
     x.1.1 ↦ x.2 ∗
     (x.1.1 +ₗ 1) ↦ next_value_of (mark_at del_pref j) (succ_at nodes j)) ∗
  l_t ↦ v_t ∗
  (l_t +ₗ 1) ↦ InjLV #new_l ∗
  new_l ↦ d_new ∗
  (new_l +ₗ 1) ↦ InjLV #l_succ ∗
  ([∗ list] j ↦ x ∈ drop (i_t + 1)%nat nodes,
     x.1.1 ↦ x.2 ∗
     (x.1.1 +ₗ 1) ↦ next_value_of (mark_at del_pref (i_t + 1 + j)%nat)
                     (succ_at nodes (i_t + 1 + j)%nat)) ⊢
  bq_chain
    (take (i_t + 1)%nat nodes ++ [(new_l, τ_new, d_new)] ++ drop (i_t + 1)%nat nodes)
    del_pref.
Proof.
  intros Hdel Hi_t Hi_tp1.
  pose proof (lookup_lt_Some _ _ _ Hi_tp1) as Hlen_nodes.
  pose proof (lookup_lt_Some _ _ _ Hi_t) as Hlen_nodes_t.
  set (nodes' := take (i_t + 1) nodes ++ [(new_l, τ_new, d_new)] ++ drop (i_t + 1) nodes).
  assert (Hlen_take : length (take (i_t + 1) nodes) = (i_t + 1)%nat)
    by (rewrite length_take_le; lia).
  assert (Hsucc_lt : ∀ j, (j < i_t)%nat → succ_at nodes' j = succ_at nodes j).
  { intros j Hj. rewrite /succ_at /nodes' lookup_app_l;
      [|rewrite Hlen_take; lia].
    rewrite lookup_take_lt; [done|lia]. }
  assert (Hsucc_t : succ_at nodes' i_t = Some new_l).
  { rewrite /succ_at /nodes' lookup_app_r; [|rewrite Hlen_take; lia].
    rewrite Hlen_take. replace (i_t + 1 - (i_t + 1))%nat with 0%nat by lia.
    done. }
  assert (Hsucc_t1 : succ_at nodes' (i_t + 1)%nat = Some l_succ).
  { rewrite /succ_at /nodes' lookup_app_r; [|rewrite Hlen_take; lia].
    rewrite Hlen_take.
    replace (i_t + 1 + 1 - (i_t + 1))%nat with 1%nat by lia.
    change (([(new_l, τ_new, d_new)] ++ drop (i_t + 1) nodes) !! 1)
      with (drop (i_t + 1) nodes !! 0).
    rewrite lookup_drop.
    replace (i_t + 1 + 0)%nat with (i_t + 1)%nat by lia.
    rewrite Hi_tp1. done. }
  assert (Hsucc_gt : ∀ j, succ_at nodes' (i_t + 2 + j)%nat
                          = succ_at nodes (i_t + 1 + j)%nat).
  { intros j. rewrite /succ_at /nodes' lookup_app_r; [|rewrite Hlen_take; lia].
    rewrite Hlen_take.
    replace (i_t + 2 + j + 1 - (i_t + 1))%nat with (Datatypes.S (j + 1))%nat by lia.
    change (([(new_l, τ_new, d_new)] ++ drop (i_t + 1) nodes) !! Datatypes.S (j + 1))
      with (drop (i_t + 1) nodes !! (j + 1)).
    rewrite lookup_drop.
    replace (i_t + 1 + (j + 1))%nat with (i_t + 1 + j + 1)%nat by lia.
    done. }
  assert (Hmark_t : mark_at del_pref i_t = false)
    by (rewrite /mark_at; apply bool_decide_eq_false_2; lia).
  assert (Hmark_t1 : mark_at del_pref (i_t + 1)%nat = false)
    by (rewrite /mark_at; apply bool_decide_eq_false_2; lia).
  assert (Hmark_gt : ∀ j, mark_at del_pref (i_t + 2 + j)%nat = false)
    by (intros j; rewrite /mark_at; apply bool_decide_eq_false_2; lia).
  iIntros "(Hpref & Hv_t & Hn_t & Hv_new & Hn_new & Hsuf)".
  iEval (rewrite /bq_chain).
  assert (Htake_eq : take (i_t + 1) nodes = take i_t nodes ++ [(l_t, τ_t, v_t)]).
  { replace (i_t + 1)%nat with (Datatypes.S i_t) by lia.
    by erewrite take_S_r. }
  unfold nodes' at 1.
  rewrite Htake_eq.
  rewrite !big_sepL_app.
  rewrite length_take_le; last lia.
  cbn [length].
  iEval (rewrite Htake_eq).
  rewrite big_sepL_app.
  cbn [length].
  rewrite length_take_le; last lia.
  assert (Hreassoc : (take i_t nodes ++ [(l_t, τ_t, v_t)])
                       ++ [(new_l, τ_new, d_new)] ++ drop (i_t + 1) nodes = nodes').
  { rewrite /nodes' Htake_eq -app_assoc //. }
  rewrite Hreassoc.
  iSplitL "Hpref Hv_t Hn_t".
  - iSplitL "Hpref".
    + iApply (big_sepL_mono with "Hpref"). iIntros (k y Hk) "[$ Hn]".
      apply lookup_lt_Some in Hk as Hk'. rewrite length_take_le in Hk'; last lia.
      rewrite Hsucc_lt; last lia. iFrame.
    + simpl. replace (i_t + 0)%nat with i_t by lia.
      rewrite Hmark_t Hsucc_t. simpl. iFrame.
  - iSplitL "Hv_new Hn_new".
    + simpl. replace (i_t + 1 + 0)%nat with (i_t + 1)%nat by lia.
      rewrite Hmark_t1 Hsucc_t1. simpl. iFrame.
    + iApply (big_sepL_mono with "Hsuf"). iIntros (k y Hk) "[$ Hn]".
      replace (i_t + 1 + (1 + k))%nat with (i_t + 2 + k)%nat by lia.
      rewrite Hmark_gt Hsucc_gt.
      assert (Hmark_eq : mark_at del_pref (i_t + 1 + k) = false) by
        (rewrite /mark_at; apply bool_decide_eq_false_2; lia).
      rewrite Hmark_eq. iFrame.
Qed.

(** [bq_chain_split_at]: split a [bq_chain] at a specific position
    [i_t] into prefix (positions 0..i_t-1), the cell at [i_t], and
    suffix (positions i_t+1..N-1).  Used by [bq_chain_insert]'s
    callers to extract the pieces needed for middle insertion. *)
Lemma bq_chain_split_at `{!heapGS Σ}
  (nodes : list (loc * option positive * val)) (del_pref : nat)
  (l_t : loc) (τ_t : option positive) (v_t : val) (i_t : nat) :
  nodes !! i_t = Some (l_t, τ_t, v_t) →
  bq_chain nodes del_pref ⊢
    ([∗ list] j ↦ x ∈ take i_t nodes,
       x.1.1 ↦ x.2 ∗
       (x.1.1 +ₗ 1) ↦ next_value_of (mark_at del_pref j) (succ_at nodes j)) ∗
    l_t ↦ v_t ∗
    (l_t +ₗ 1) ↦ next_value_of (mark_at del_pref i_t) (succ_at nodes i_t) ∗
    ([∗ list] j ↦ x ∈ drop (i_t + 1)%nat nodes,
       x.1.1 ↦ x.2 ∗
       (x.1.1 +ₗ 1) ↦ next_value_of (mark_at del_pref (i_t + 1 + j)%nat)
                       (succ_at nodes (i_t + 1 + j)%nat)).
Proof.
  intros Hlt.
  iIntros "Hch".
  pose proof (take_drop_middle nodes _ _ Hlt) as Hsplit.
  iEval (rewrite /bq_chain) in "Hch".
  iEval (rewrite -[X in big_sepL _ X]Hsplit) in "Hch".
  rewrite big_sepL_app big_sepL_cons.
  rewrite length_take_le; last (apply lookup_lt_Some in Hlt; lia).
  iDestruct "Hch" as "(Hpref & [Hv Hn] & Hsuf)".
  simpl. replace (i_t + 0)%nat with i_t by lia.
  iFrame "Hv Hn Hpref".
  replace (Datatypes.S i_t) with (i_t + 1)%nat by lia.
  iApply (big_sepL_mono with "Hsuf").
  iIntros (k y Hk) "[Hv Hn]".
  replace (i_t + Datatypes.S k)%nat with (i_t + 1 + k)%nat by lia.
  iFrame.
Qed.

(** [bq_chain_advance]: rebuild [bq_chain] at [del_pref + 1] given the
    chain split at the boundary cell [i_t = del_pref].  The boundary
    cell's next-pointer must already have been flipped from [InjLV] to
    [InjRV] (mark CAS).  Used in [refine_deq_cont]'s LIN-DEQ1 branch
    to advance the marked-prefix length after the dequeue's mark
    CAS. *)
Lemma bq_chain_advance `{!heapGS Σ}
  (nodes : list (loc * option positive * val)) (del_pref : nat)
  (l_t : loc) (τ_t : option positive) (v_t : val) :
  nodes !! del_pref = Some (l_t, τ_t, v_t) →
  ([∗ list] j ↦ x ∈ take del_pref nodes,
     x.1.1 ↦ x.2 ∗
     (x.1.1 +ₗ 1) ↦ next_value_of (mark_at del_pref j) (succ_at nodes j)) ∗
  l_t ↦ v_t ∗
  (l_t +ₗ 1) ↦ next_value_of (mark_at (del_pref + 1)%nat del_pref)
                  (succ_at nodes del_pref) ∗
  ([∗ list] j ↦ x ∈ drop (del_pref + 1)%nat nodes,
     x.1.1 ↦ x.2 ∗
     (x.1.1 +ₗ 1) ↦ next_value_of (mark_at del_pref (del_pref + 1 + j)%nat)
                     (succ_at nodes (del_pref + 1 + j)%nat))
  ⊢ bq_chain nodes (del_pref + 1)%nat.
Proof.
  intros Hi_t.
  iIntros "(Hpref & Hv_t & Hn_t & Hsuf)".
  rewrite /bq_chain.
  pose proof (take_drop_middle nodes _ _ Hi_t) as Hsplit.
  iEval (rewrite -{2}Hsplit).
  iEval (rewrite big_sepL_app big_sepL_cons).
  rewrite length_take_le; last (apply lookup_lt_Some in Hi_t; lia).
  replace (Datatypes.S del_pref) with (del_pref + 1)%nat by lia.
  iSplitL "Hpref".
  { iApply (big_sepL_mono with "Hpref").
    iIntros (k y Hk) "Hcell".
    apply lookup_lt_Some in Hk as Hk'.
    rewrite length_take_le in Hk'; last (apply lookup_lt_Some in Hi_t; lia).
    assert (mark_at del_pref k = mark_at (del_pref + 1)%nat k) as ->.
    { rewrite /mark_at. apply bool_decide_ext. lia. }
    iFrame. }
  simpl. iSplitL "Hv_t Hn_t".
  { replace (del_pref + 0)%nat with del_pref by lia. iFrame. }
  iApply (big_sepL_mono with "Hsuf").
  iIntros (k y Hk) "Hcell".
  replace (del_pref + Datatypes.S k)%nat with (del_pref + 1 + k)%nat by lia.
  assert (mark_at del_pref (del_pref + 1 + k)%nat
          = mark_at (del_pref + 1)%nat (del_pref + 1 + k)%nat) as ->.
  { rewrite /mark_at. apply bool_decide_ext. lia. }
  iFrame.
Qed.

(* ========================================================================= *)

Section bq_skeleton.
  Context `{!traceG Σ, !bqG Σ}.

  Local Notation valid_value := bq_valid_value.

  Definition Nbq : namespace := nroot .@ "bq".

  Section with_heapGS.
  Context `{!heapGS Σ}.

  (** Forward direction of the [node_map] invariant: every recorded
    storer's value is consistent with the AbsQ entry [ℓ τ].  The
    invariant is structurally restricted to [Some τ] entries: the
    dummy at [chain[0]] carries [None] for its identifier and is
    therefore not constrained by either conjunct. *)
  Definition node_val_inv
    (node_map : gmap loc node_info) (s : absq_state) : Prop :=
    (∀ l τ d, node_map !! l = Some (Some τ, d) →
       ∃ f, s.(absq_l) !! τ = Some (d, f)) ∧
    (∀ l₁ l₂ τ d₁ d₂,
       node_map !! l₁ = Some (Some τ, d₁) → node_map !! l₂ = Some (Some τ, d₂) →
       l₁ = l₂).

  (** Same role as [hwq.dq_inv]. *)
  Definition dq_inv
    (dq_map : gmap positive val) (s : absq_state) : Prop :=
    ∀ τ v, dq_map !! τ = Some v → s.(absq_rv) !! τ = Some v.

  (** Reverse direction of [bq_sim] clause 6: if a non-dummy chain
    position carries a [Some τ] tag and τ is still tracked in [op_map]
    (i.e. its [RET-ENQ] hasn't fired yet to delete it), then the
    [op_map] entry has [linked = true].  This pins down the fact that
    a chain location is created exclusively at the linking splice CAS
    in the enqueue's per-method WP, with [linked] flipped to [true]
    in the same step.

    The forward direction lives inside [bq_sim]'s clause 6
    ([linked = true → ∃ l i, ...]).  Together they give the
    [op_spec_enq_cont] splice CAS what it needs to discharge
    "no chain position has [Some τ] tag when [op_map(τ).linked =
    false]" without an additional ghost.  The implication is
    formulated against [op_map(τ) = Some info] (rather than equality
    to a specific record) so that [RET-ENQ]'s [delete τ op_map]
    update does not invalidate the invariant for τ's chain location. *)
  Definition chain_op_inv
    (nodes : list (loc * option positive * val))
    (op_map : gmap positive op_info) : Prop :=
    ∀ i l τ d, (1 ≤ i)%nat → nodes !! i = Some (l, Some τ, d) →
      ∀ info, op_map !! τ = Some info → info.(op_info_linked) = true.

  (** [chain_witness_inv]: each persistent chain-snapshot fragment for
    a pending unlinked enqueue τ is a sublist of the current chain,
    has at least one entry, and contains the chain location of every
    [(k, τ) ∈ absq_lt] edge.  Concretely: at τ's phase-4 mint, [snap]
    was the chain with [tail] (= τ's tail1) at the chain-end.  Because
    snapshots are sublists of the current chain, the relative order of
    snap's entries is preserved across subsequent splices; combined
    with chain-id injectivity this lets the basket splice-success
    branch derive that any (k, τ) ∈ absq_lt has its chain location at
    a current chain position bounded by [tail]'s current position. *)
  Definition chain_witness_inv
    (witness_map : gmap (positive * loc) chain_snapshot)
    (nodes : list (loc * option positive * val))
    (s : absq_state) : Prop :=
    (∀ k, k ∈ dom witness_map → k.1 ∈ dom s.(absq_cp)) ∧
    ∀ τ tail_loc snap, witness_map !! (τ, tail_loc) = Some snap →
      sublist snap nodes ∧
      (1 ≤ length snap)%nat ∧
      succ_at snap (length snap - 1) = None ∧
      (∃ τ_t v_t, snap !! (length snap - 1) = Some (tail_loc, τ_t, v_t)) ∧
      (∀ k, (k, τ) ∈ s.(absq_lt) →
         ∃ i l d, (snap !! i = Some (l, Some k, d)) ∧ (1 ≤ i)%nat).

  (** Helper: sublist is preserved by inserting an element at any
    position.  Used to maintain [chain_witness_inv]'s sublist clause
    across splice CASes (which insert at [tail1.position + 1]). *)
  Lemma sublist_insert_at {A} (snap : list A) (l : list A) (i : nat) (x : A) :
    snap `sublist_of` l → snap `sublist_of` (take i l ++ x :: drop i l).
  Proof.
    intros Hsub.
    apply sublist_app_cons_r. left.
    by rewrite take_drop.
  Qed.

  (** Helper: sublist is order-preserving when the larger list has
    [NoDup].  Used in [refine_enq_basket]'s splice-success branch to
    convert "k appears in [snap_τ] before [tail1]" into "k's current
    chain position ≤ tail1's current chain position". *)
  Lemma NoDup_sublist_lookup_mono {A} (l1 l2 : list A) :
    NoDup l2 →
    l1 `sublist_of` l2 →
    ∀ (i j : nat) (x y : A) (p_x p_y : nat),
      l1 !! i = Some x → l1 !! j = Some y → (i ≤ j)%nat →
      l2 !! p_x = Some x → l2 !! p_y = Some y → (p_x ≤ p_y)%nat.
  Proof.
    intros Hnd Hsub.
    induction Hsub as [|z l1 l2 Hsub IH|z l1 l2 Hsub IH];
      intros i j x y p_x p_y Hi Hj Hij Hp_x Hp_y.
    - rewrite lookup_nil in Hi. discriminate.
    - apply NoDup_cons in Hnd as [Hznotin Hnd2].
      rewrite lookup_cons_Some in Hi.
      rewrite lookup_cons_Some in Hj.
      rewrite lookup_cons_Some in Hp_x.
      rewrite lookup_cons_Some in Hp_y.
      destruct Hi as [Hi|Hi]; destruct Hj as [Hj|Hj].
      + (* i = j = 0: x = z = y *)
        destruct Hi as [Hi_eq Hzx]. destruct Hj as [Hj_eq Hzy]. subst.
        destruct Hp_x as [Hpx|Hpx]; [destruct Hpx; lia|].
        destruct Hpx as [Hpx_pos Hpx_lk].
        exfalso. apply Hznotin.
        apply list_elem_of_lookup_2 with (p_x - 1)%nat. exact Hpx_lk.
      + (* i = 0, j ≥ 1: x = z, y in l1 *)
        destruct Hi as [Hi_eq Hzx]. subst x.
        destruct Hj as [Hj_pos Hj_lk].
        destruct Hp_x as [Hpx|Hpx]; [destruct Hpx; lia|].
        destruct Hpx as [Hpx_pos Hpx_lk].
        exfalso. apply Hznotin.
        apply list_elem_of_lookup_2 with (p_x - 1)%nat. exact Hpx_lk.
      + (* i ≥ 1, j = 0: but i ≤ j gives contradiction *)
        destruct Hi as [Hi_pos _]. destruct Hj as [Hj_eq _]. lia.
      + (* i ≥ 1, j ≥ 1: both in l1, apply IH *)
        destruct Hi as [Hi_pos Hi_lk]. destruct Hj as [Hj_pos Hj_lk].
        destruct Hp_x as [Hpx|Hpx].
        * destruct Hpx as [_ Hpx_eq]. subst x.
          exfalso. apply Hznotin.
          apply (sublist_subseteq _ _ Hsub).
          apply list_elem_of_lookup_2 with (i - 1)%nat. exact Hi_lk.
        * destruct Hpx as [Hpx_pos Hpx_lk].
          destruct Hp_y as [Hpy|Hpy].
          -- destruct Hpy as [_ Hpy_eq]. subst y.
             exfalso. apply Hznotin.
             apply (sublist_subseteq _ _ Hsub).
             apply list_elem_of_lookup_2 with (j - 1)%nat. exact Hj_lk.
          -- destruct Hpy as [Hpy_pos Hpy_lk].
             assert ((p_x - 1) ≤ (p_y - 1))%nat; [|lia].
             apply (IH Hnd2 (i - 1)%nat (j - 1)%nat x y _ _ Hi_lk Hj_lk
                       ltac:(lia) Hpx_lk Hpy_lk).
    - apply NoDup_cons in Hnd as [Hznotin Hnd2].
      rewrite lookup_cons_Some in Hp_x.
      rewrite lookup_cons_Some in Hp_y.
      destruct Hp_x as [Hpx|Hpx].
      + destruct Hpx as [_ Hpx_eq]. subst x.
        exfalso. apply Hznotin.
        apply (sublist_subseteq _ _ Hsub).
        apply list_elem_of_lookup_2 with i. exact Hi.
      + destruct Hpx as [Hpx_pos Hpx_lk].
        destruct Hp_y as [Hpy|Hpy].
        * destruct Hpy as [_ Hpy_eq]. subst y.
          exfalso. apply Hznotin.
          apply (sublist_subseteq _ _ Hsub).
          apply list_elem_of_lookup_2 with j. exact Hj.
        * destruct Hpy as [Hpy_pos Hpy_lk].
          assert ((p_x - 1) ≤ (p_y - 1))%nat; [|lia].
          apply (IH Hnd2 i j x y _ _ Hi Hj Hij Hpx_lk Hpy_lk).
  Qed.

  Definition bq_inv_body
    (γ_op γ_nm γ_dq γ_del γ_calls γ_no_O γ_ls γ_w : gname) (head tail : loc) (l : loc) : iProp Σ :=
    ∃ (nodes : list (loc * option positive * val))
      (del_pref : nat)
      (head_val tail_val dummy_loc : loc)
      (ts : list (positive * trace))
      (s : absq_state) (ls : list (positive * absq_action))
      (op_map : gmap positive op_info)
      (node_map : gmap loc node_info)
      (dq_map : gmap positive val)
      (no_O_set : gset positive)
      (witness_map : gmap (positive * loc) chain_snapshot),
      head ↦ #head_val ∗
      tail ↦ #tail_val ∗
      bq_chain nodes del_pref ∗
      trace_is l ts ∗
      own γ_op (● to_opmap op_map) ∗
      own γ_nm (● to_nodemap node_map) ∗
      own γ_nm (◯ to_nodemap node_map) ∗
      own γ_dq (● to_dqmap dq_map) ∗
      own γ_dq (◯ to_dqmap dq_map) ∗
      own γ_del (mono_nat_auth (DfracOwn 1) del_pref) ∗
      own γ_calls (● dom s.(absq_cp)) ∗
      own γ_no_O (● no_O_set) ∗
      own γ_ls (●ML (ls : list (leibnizO (positive * absq_action)))) ∗
      own γ_w (● to_witnessmap witness_map) ∗
      own γ_w (◯ to_witnessmap witness_map) ∗
      ⌜absq_steps MayEmpty valid_value absq_init ls s⌝ ∗
      ⌜ts = filter (not ∘ is_lin ∘ snd) (trace_of_absq_labels ls)⌝ ∗
      ⌜bq_sim valid_value nodes del_pref head_val tail_val s op_map node_map ts⌝ ∗
      ⌜nodes !! 0%nat = Some (dummy_loc, None, #())⌝ ∗
      ⌜node_val_inv node_map s⌝ ∗
      ⌜dq_inv dq_map s⌝ ∗
      ⌜no_O_set ⊆ dom s.(absq_cp) ∧ no_O_set ## s.(absq_O)⌝ ∗
      ⌜chain_op_inv nodes op_map⌝ ∗
      ⌜chain_witness_inv witness_map nodes s⌝.

  Definition is_bq (l : loc) (γ : gname) (obj : val) : iProp Σ :=
    ∃ (head tail : loc) (γ_nm γ_dq γ_del γ_calls γ_no_O γ_ls γ_w : gname),
      ⌜obj = (#head, #tail)%V⌝ ∗
      inv Nbq (bq_inv_body γ γ_nm γ_dq γ_del γ_calls γ_no_O γ_ls γ_w head tail l).

  Global Instance is_bq_pers γ v l : Persistent (is_bq γ v l).
  Proof. apply _. Qed.
  End with_heapGS.

  Definition bq_repr : mgc_repr Σ := {|
    I_lang := I_lang_bq;
    mgc_inv := @is_bq;
  |}.

  Definition init_bq : expr := new_queue #().

End bq_skeleton.
