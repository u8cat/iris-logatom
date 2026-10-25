(* absq.v: the abstract queues [AbsQ] and [AbsQ0] of Bouajjani et al. [2017]
  "Proving linearizability using forward simulations" (arXiv:1702.02705).
  [AbsQ] is defined in Section 4.2 and Figure 3; [AbsQ0] is the standard
  sequence-based atomic queue, with transitions given in Figure 8. *)

From iris.heap_lang Require Import notation.
From stdpp Require Import gmap.
From iris_logatom.pure_logic.refine Require Import backward_simulation.
From iris_logatom.pure_logic.models Require Import bag_like.

(** Control points of operations. [A1], [A2] and [R1], [R2], [R3] are the
  control points used in [AbsQ]: [A1], [A2] are for enqueue operations,
  [R1], [R2], [R3] are for dequeue operations. [AbsQ0] additionally uses
  the intermediate control point [A] for an enqueue that has reached its
  linearization point but has not yet returned. *)
Inductive control_point : Set :=
  | A1 | A | A2 | R1 | R2 | R3.

(** The pending/completed flag attached to every enqueue operation. *)
Inductive op_flag : Set :=
  | PEND | COMP.

Global Instance control_point_eqdecision : EqDecision control_point.
Proof. solve_decision. Defined.

Global Instance op_flag_eqdecision : EqDecision op_flag.
Proof. solve_decision. Defined.

(** The state of [AbsQ]: a tuple ⟨O, <, ℓ, rv, cp⟩ where
  - [absq_O] is the set of enqueue operation identifiers currently in the queue;
  - [absq_lt] (written [<] in the paper) is a strict partial order over
    [absq_O] capturing the happens-before constraints between enqueues;
  - [absq_l] labels every identifier with its input value and a
    pending/completed flag;
  - [absq_rv] records the return value of a dequeue operation fixed at its
    linearization point;
  - [absq_cp] records the control point of every enqueue and dequeue
    operation.

  The initial state [absq_init] has all five components empty. *)
Record absq_state : Type := AbsQState {
  absq_O : gset positive;
  absq_lt : gset (positive * positive);
  absq_l : gmap positive (val * op_flag);
  absq_rv : gmap positive val;
  absq_cp : gmap positive control_point;
}.

Definition absq_init : absq_state := {|
  absq_O := ∅;
  absq_lt := ∅;
  absq_l := ∅;
  absq_rv := ∅;
  absq_cp := ∅;
|}.

(** The alphabet of [AbsQ] and [AbsQ0]: call and return actions, the
  linearization points of dequeue operations [lin(deq, d, k)], and the
  linearization points of enqueue operations [lin(enq, d, k)]. [AbsQ] does
  not use [ALinEnq]; the remaining actions are shared between [AbsQ] and
  [AbsQ0]. *)
Inductive absq_action : Set :=
  | ACallEnq (v : val)
  | ACallDeq
  | ARetEnq
  | ARetDeq (v : val)
  | ALinEnq (v : val)
  | ALinDeq (v : val).

Global Instance absq_action_eqdecision : EqDecision absq_action.
Proof. solve_decision. Defined.

(** An operation identifier [k] is marked as completed in [ℓ]. *)
Definition is_COMP (ℓ : gmap positive (val * op_flag)) (k : positive) : Prop :=
  ∃ d, ℓ !! k = Some (d, COMP).

Global Instance is_COMP_dec ℓ k : Decision (is_COMP ℓ k).
Proof.
  rewrite /is_COMP.
  destruct (ℓ !! k) as [[d [|]]|].
  - right. by intros [? [=]].
  - left. by eexists.
  - right. by intros [? [=]].
Defined.

(** The set of completed enqueues in [O], written [COMP(O)] in the paper. *)
Definition absq_COMP (O : gset positive) (ℓ : gmap positive (val * op_flag))
  : gset positive := filter (is_COMP ℓ) O.

(** The set of elements of [O] that are minimal in the order [<], written
  [min(O)] in the paper. *)
Definition absq_min (O : gset positive) (lt : gset (positive * positive))
  : gset positive := filter (λ k, ∀ k', k' ∈ O → (k', k) ∉ lt) O.

(** The relation [<] with every pair mentioning [k] removed, written
  [<↑k] in the paper. *)
Definition absq_remove (lt : gset (positive * positive)) (k : positive)
  : gset (positive * positive) := filter (λ p, p.1 ≠ k ∧ p.2 ≠ k) lt.

Section absq_step.
  (** Predicate restricting the values that may be enqueued.  Each
    instantiation (e.g. HWQ) picks a concrete predicate (e.g.
    [val_is_unboxed]); the abstract machine here only needs that the
    predicate is preserved across enqueue/return. The [rme] parameter
    additionally controls whether the empty-dequeue rule [LIN-DEQ2] is
    available: when [rme = NeverEmpty] AbsQ rejects empty dequeues,
    matching the corresponding queue model. *)
  Context (rme : response_mayempty) (valid_value : val → Prop).

  (** The transition relation of [AbsQ] (Figure 3 of the paper). An action
    [lin(deq, _, _)] has no corresponding rule in the paper; it is represented
    here by the two alternative rules [absq_step_lin_deq1] (non-empty queue)
    and [absq_step_lin_deq2] (empty queue).

    Dequeue results are encoded as options ([SOMEV d] for non-empty,
    [NONEV] for empty) so that the abstract machine matches the
    [bag_like.queue_model] convention without a separate sentinel. *)
  Inductive absq_step : relationL absq_state (positive * absq_action) :=
    (* [CALL-ENQ]: an enqueue of value [d] (satisfying [valid_value]) is
      invoked with a fresh identifier [k] and ordered after every
      completed enqueue. *)
    | absq_step_call_enq O lt ℓ rv cp k d :
      k ∉ dom cp → valid_value d →
      absq_step
        (AbsQState O lt ℓ rv cp)
        (AbsQState
          (O ∪ {[k]})
          (lt ∪ set_map (λ k', (k', k)) (absq_COMP O ℓ))
          (<[k := (d, PEND)]> ℓ)
          rv
          (<[k := A1]> cp))
        [(k, ACallEnq d)]
    (* [CALL-DEQ]: a dequeue is invoked with a fresh identifier [k]. *)
    | absq_step_call_deq O lt ℓ rv cp k :
      k ∉ dom cp →
      absq_step
        (AbsQState O lt ℓ rv cp)
        (AbsQState O lt ℓ rv (<[k := R1]> cp))
        [(k, ACallDeq)]
    (* [RET-ENQ1]: an enqueue whose value is still present in the queue
      transitions from pending to completed. *)
    | absq_step_ret_enq1 O lt ℓ rv cp k d :
      cp !! k = Some A1 → k ∈ O → ℓ !! k = Some (d, PEND) →
      absq_step
        (AbsQState O lt ℓ rv cp)
        (AbsQState O lt (<[k := (d, COMP)]> ℓ) rv (<[k := A2]> cp))
        [(k, ARetEnq)]
    (* [RET-ENQ2]: an enqueue whose value has already been removed by a
      dequeue simply advances its control point. *)
    | absq_step_ret_enq2 O lt ℓ rv cp k :
      cp !! k = Some A1 → k ∉ O →
      absq_step
        (AbsQState O lt ℓ rv cp)
        (AbsQState O lt ℓ rv (<[k := A2]> cp))
        [(k, ARetEnq)]
    (* [RET-DEQ]: a dequeue returns the value fixed at its linearization
      point. *)
    | absq_step_ret_deq O lt ℓ rv cp k v :
      cp !! k = Some R2 → rv !! k = Some v →
      absq_step
        (AbsQState O lt ℓ rv cp)
        (AbsQState O lt ℓ rv (<[k := R3]> cp))
        [(k, ARetDeq v)]
    (* [LIN-DEQ1]: the linearization point of a non-empty dequeue is enabled
      when its return value [d] was added by a minimal enqueue [k']; the
      enqueue [k'] is then removed from the current state and every
      happens-before edge mentioning [k'] is dropped. The dequeue records
      [SOMEV d] as its option-encoded return value. *)
    | absq_step_lin_deq1 O lt ℓ rv cp k k' d f :
      cp !! k = Some R1 →
      k' ∈ absq_min O lt → ℓ !! k' = Some (d, f) →
      absq_step
        (AbsQState O lt ℓ rv cp)
        (AbsQState (O ∖ {[k']}) (absq_remove lt k') ℓ
          (<[k := SOMEV d]> rv) (<[k := R2]> cp))
        [(k, ALinDeq (SOMEV d))]
    (* [LIN-DEQ2]: the linearization point of an empty-queue dequeue is
      enabled when every enqueue in the current state is still pending. The
      dequeue records [NONEV] as its option-encoded return value. Only
      available when [rme = MayEmpty] (encoded via the [if rme then True
      else False] guard so [inversion] doesn't try to substitute
      [rme]). *)
    | absq_step_lin_deq2 O lt ℓ rv cp k :
      (if rme then True else False) →
      cp !! k = Some R1 →
      (∀ o, o ∈ O → ∃ d, ℓ !! o = Some (d, PEND)) →
      absq_step
        (AbsQState O lt ℓ rv cp)
        (AbsQState O lt ℓ (<[k := NONEV]> rv) (<[k := R2]> cp))
        [(k, ALinDeq NONEV)].

  Global Instance absq_step_singleton_relationL : SingletonRelationL absq_step.
  Proof. by intros ??? []. Qed.
End absq_step.

(* ========================================== *)
(* AbsQ0: the standard sequence-based abstract queue (Figure 8 of the paper) *)

(** The state of [AbsQ0]: a tuple ⟨σ, in⁰, rv⁰, cp⁰⟩ where
  - [absq0_seq] (written [σ] in the paper) is the current sequence of
    enqueue (identifier, value) pairs in the queue; enqueue appends to
    [σ] and dequeue removes the head, matching the FIFO orientation of
    [bag_like.queue_model] (head = oldest). The paper's [σ] is a
    sequence of values; we tag each element with the identifier of the
    enqueue that produced it so that the backward simulation can pair
    [σ] positions with [AbsQ] operations by identifier rather than by
    value (removing the data-independence assumption that enqueued
    values are unique).
  - [absq0_in] (written [in⁰] in the paper) records the input value of
    every enqueue operation;
  - [absq0_rv] (written [rv⁰] in the paper) records the return value of a
    dequeue fixed at its linearization point;
  - [absq0_cp] (written [cp⁰] in the paper) records the control point of
    every enqueue (in [{A1, A, A2}]) and dequeue (in [{R1, R2, R3}])
    operation.

  The initial state [absq0_init] has all four components empty. *)
Record absq0_state : Type := AbsQ0State {
  absq0_seq : list (positive * val);
  absq0_in : gmap positive val;
  absq0_rv : gmap positive val;
  absq0_cp : gmap positive control_point;
}.

Definition absq0_init : absq0_state := {|
  absq0_seq := [];
  absq0_in := ∅;
  absq0_rv := ∅;
  absq0_cp := ∅;
|}.

Section absq0_step.
  (** Same predicate as in [absq_step]; values entering [σ] / [in0]
    must satisfy [valid_value]. The [rme] parameter additionally
    forbids the [LIN-DEQ2] (empty-dequeue) rule when [rme = NeverEmpty],
    matching the underlying queue model's restriction. *)
  Context (rme : response_mayempty) (valid_value : val → Prop).

  (** The transition relation of [AbsQ0] (Figure 8 of the paper). As in
    [AbsQ], the single action [lin(deq, _, _)] is represented by the two
    alternative rules [absq0_step_lin_deq1] (non-empty queue) and
    [absq0_step_lin_deq2] (empty queue). Dequeue results are
    option-encoded as [SOMEV d]/[NONEV] to match
    [bag_like.queue_model]. *)
  Inductive absq0_step : relationL absq0_state (positive * absq_action) :=
    (* [CALL-ENQ]: an enqueue of value [d] is invoked with a fresh
      identifier [k]; [d] is recorded as the input value of [k]. *)
    | absq0_step_call_enq σ in0 rv0 cp0 k d :
      k ∉ dom cp0 → valid_value d →
      absq0_step
        (AbsQ0State σ in0 rv0 cp0)
        (AbsQ0State σ (<[k := d]> in0) rv0 (<[k := A1]> cp0))
        [(k, ACallEnq d)]
    (* [LIN-ENQ]: the linearization point of an enqueue [k] appends the
      tagged value [(k, d)] to the sequence [σ]. The paper's Figure 8
      rule leaves [d] formally unconstrained; we tighten it to require
      [d] match the value originally passed at the [CALL-ENQ] (i.e.,
      [in0(k) = Some d]) and to satisfy [valid_value]. The key [k] is
      tagged onto [σ] so the backward simulation can match [σ]
      positions with [AbsQ] operations by identifier. *)
    | absq0_step_lin_enq σ in0 rv0 cp0 k d :
      cp0 !! k = Some A1 → in0 !! k = Some d →
      valid_value d →
      absq0_step
        (AbsQ0State σ in0 rv0 cp0)
        (AbsQ0State (σ ++ [(k, d)]) in0 rv0 (<[k := A]> cp0))
        [(k, ALinEnq d)]
    (* [RET-ENQ]: an enqueue that has been linearized advances to its
      return control point. *)
    | absq0_step_ret_enq σ in0 rv0 cp0 k :
      cp0 !! k = Some A →
      absq0_step
        (AbsQ0State σ in0 rv0 cp0)
        (AbsQ0State σ in0 rv0 (<[k := A2]> cp0))
        [(k, ARetEnq)]
    (* [CALL-DEQ]: a dequeue is invoked with a fresh identifier [k]. *)
    | absq0_step_call_deq σ in0 rv0 cp0 k :
      k ∉ dom cp0 →
      absq0_step
        (AbsQ0State σ in0 rv0 cp0)
        (AbsQ0State σ in0 rv0 (<[k := R1]> cp0))
        [(k, ACallDeq)]
    (* [LIN-DEQ1]: the linearization point of a non-empty dequeue [k]
      removes the head element [(k_e, d)] from the sequence
      [σ = (k_e, d) :: σ'] and records [SOMEV d] as the return value
      of [k]. The tag [k_e] is the identifier of the enqueue that
      contributed [d]; it is dropped in the observable label
      [ALinDeq (SOMEV d)]. *)
    | absq0_step_lin_deq1 σ σ' in0 rv0 cp0 k k_e d :
      cp0 !! k = Some R1 → σ = (k_e, d) :: σ' →
      absq0_step
        (AbsQ0State σ in0 rv0 cp0)
        (AbsQ0State σ' in0 (<[k := SOMEV d]> rv0) (<[k := R2]> cp0))
        [(k, ALinDeq (SOMEV d))]
    (* [LIN-DEQ2]: the linearization point of a dequeue on an empty
      sequence records [NONEV] as its return value. Only available
      when [rme = MayEmpty] (encoded via the [if rme then True else
      False] guard so [inversion] doesn't try to substitute [rme]). *)
    | absq0_step_lin_deq2 in0 rv0 cp0 k :
      (if rme then True else False) →
      cp0 !! k = Some R1 →
      absq0_step
        (AbsQ0State [] in0 rv0 cp0)
        (AbsQ0State [] in0 (<[k := NONEV]> rv0) (<[k := R2]> cp0))
        [(k, ALinDeq NONEV)]
    (* [RET-DEQ]: a dequeue returns the value fixed at its linearization
      point. *)
    | absq0_step_ret_deq σ in0 rv0 cp0 k v :
      cp0 !! k = Some R2 → rv0 !! k = Some v →
      absq0_step
        (AbsQ0State σ in0 rv0 cp0)
        (AbsQ0State σ in0 rv0 (<[k := R3]> cp0))
        [(k, ARetDeq v)].

  Global Instance absq0_step_singleton_relationL : SingletonRelationL absq0_step.
  Proof. by intros ??? []. Qed.
End absq0_step.
