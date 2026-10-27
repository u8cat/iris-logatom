(* conc_his_rel.v, ported from aspect-oriented queue linearizability *)
(* Adapts the concurrent history relations from the stack theory to queues *)
(* Key difference: FIFO ordering instead of LIFO *)

From stdpp Require Import finite relations.
From iris_logatom.lib Require Import list.
From iris_logatom.pure_logic Require Export linear.
From iris_logatom.pure_logic.aspect.bag.ext Require Export conc_his_rel.

Class abstract_queue_model := AbstractQueueModel {
  operation : Type;
  operation_eq_dec :: EqDecision operation;
  operation_finite :: Finite operation;
}.

Notation Acyclic R := (Irreflexive (tc R)).
Local Instance relation_union {A} : Union (relation A) :=
  λ r1 r2, Relation_Operators.union A r1 r2.

Section def.
  Context `{abstract_queue_model}.
  Implicit Types (pre val : relation operation) (empty : operation → Prop).

  #[local] Existing Instances pre_transitive pre_antisymmetric pre_irreflexive pre_abcd.
  #[local] Existing Instances empty_pre_conchistory empty_operation_finite.
  #[local] Existing Instances sequential_empty_history_wellformed
    sequential_empty_set_sequential_empty_history.

  (* Helper: transitive closure of a transitive relation is just the relation *)
  Lemma tc_transitive_collapse (r : relation operation) (x y : operation) :
    Transitive r → tc r x y → r x y.
  Proof.
    intros Htrans Hxy.
    induction Hxy as [a b Hab|a b c Hab Hbc IH].
    - exact Hab.
    - eapply Htrans; [exact Hab|exact IH].
  Qed.

  Lemma lem_transitive_irreflexive_then_acyclic (r : relation operation) :
    Transitive r → Irreflexive r → Acyclic r.
  Proof.
    intros Htrans Hirr x Htc.
    apply (Hirr x). apply tc_transitive_collapse; assumption.
  Qed.

  (* Helper: subrelation is preserved by tc *)
  Lemma tc_subrel (r r' : relation operation) x y :
    subrelation r' r → tc r' x y → tc r x y.
  Proof.
    intros Hsub Htc.
    induction Htc as [a b Hab|a b c Hab Hbc IH].
    - apply tc_once. exact (Hsub _ _ Hab).
    - eapply tc_l; [exact (Hsub _ _ Hab)|exact IH].
  Qed.

  (* Helper: acyclicity is preserved under subrelation *)
  Lemma acyclic_subset (r r' : relation operation) :
    subrelation r' r → Acyclic r → Acyclic r'.
  Proof.
    intros Hsub Hacyc x Htc.
    apply (Hacyc x).
    eapply tc_subrel; [exact Hsub|exact Htc].
  Qed.

  Lemma lem_irreflexive_then_not_equal (r : relation operation) a b :
    Irreflexive r → r a b → a ≠ b.
  Proof.
    intros Hirr Hab Heq. subst b. by eapply Hirr.
  Qed.

  Definition same_val val : relation operation :=
    λ a b, val a b ∨ val b a.

  Lemma same_val_symmetric val : Symmetric (same_val val).
  Proof.
    intros a b [Hab|Hba]; [right|left]; done.
  Qed.

  (* --- Insertion and removal orders --- *)
  (* These are the key definitions that differ for queues *)

  (* ins_order: Ordering on enqueue operations
     For FIFO: if enq(a) precedes enq(b), then a was enqueued first *)
  Definition ins_order (pre val ir : relation operation) : relation operation :=
    λ a b, is_push val a ∧ is_push val b ∧ (pre a b ∨ ∃ c, pre a c ∧ ir c b).

  (* rem_order: Ordering on dequeue operations
     For FIFO: if deq(a) precedes deq(b), then a was dequeued first *)
  Definition rem_order (pre val ir : relation operation) : relation operation :=
    λ a b, is_pop val a ∧ is_pop val b ∧ (pre a b ∨ (∃ c, ir a c ∧ ir c b)).

  Definition order_correct pre val :=
    (∀ e1 e2 d1 d2, pre e1 e2 → val e1 d1 → val e2 d2 → ¬ pre d2 d1).

  (* --- Wellformed History --- *)
  Class WellformedHistory pre val := {
    #[local] wf_pre_transitive :: Transitive pre;
    #[local] wf_pre_antisymmetric :: Antisymmetric operation (=) pre;
    #[local] wf_pre_irreflexive :: Irreflexive pre;
    def_enqueue_once : push_once val;
    def_dequeue_once : pop_once val;
    def_val_order : val_order val;
    def_enqueue_or_dequeue : ∀ a b, pre a b → (∃ c, val a c ∨ val c a) ∧ (∃ c, val b c ∨ val c b);
    def_val_then_not_pr : val_then_not_pr pre val;
  }.

  (* Helper lemmas for WellformedHistory *)
  Lemma lem_enqueue_or_dequeue1 pre val a b :
    WellformedHistory pre val → pre a b → is_push val a ∨ is_pop val a.
  Proof.
    intros Hwf Hpre.
    destruct (def_enqueue_or_dequeue a b Hpre) as [[c [Hac|Hca]] _].
    - left. exists c. done.
    - right. exists c. done.
  Qed.

  Lemma lem_enqueue_or_dequeue2 pre val a b :
    WellformedHistory pre val → pre a b → is_push val b ∨ is_pop val b.
  Proof.
    intros Hwf Hpre.
    destruct (def_enqueue_or_dequeue a b Hpre) as [_ [c [Hbc|Hcb]]].
    - left. exists c. done.
    - right. exists c. done.
  Qed.

  Lemma lem_enqueue_then_dequeue_exists val a : is_push val a → ∃ b, val a b ∧ is_pop val b.
  Proof.
    intros [ra Hvara].
    exists ra. split; [done|].
    exists a. done.
  Qed.

  Lemma lem_dequeue_then_enqueue_exists val a : is_pop val a → ∃ b, val b a ∧ is_push val b.
  Proof.
    intros [ia Hvalia].
    exists ia. split; [done|].
    exists a. done.
  Qed.

  Lemma lem_val_then_enqueue_and_dequeue val a b : val a b → is_push val a ∧ is_pop val b.
  Proof.
    intros Hab.
    split.
    - exists b. done.
    - exists a. done.
  Qed.

  (* Helper: val a b implies a is enqueue *)
  Lemma val_enqueue val a b : val a b → is_push val a.
  Proof.
    intros Hab. exists b. done.
  Qed.

  (* Helper: val a b implies b is dequeue *)
  Lemma val_dequeue val a b : val a b → is_pop val b.
  Proof.
    intros Hab. exists a. done.
  Qed.

  (* --- Sequential Set (same structure as stack) --- *)
  Class SequentialSet pre val := {
    sequential_set_wellformed :: WellformedHistory pre val;
    total_on_enqueue a b : is_push val a → is_push val b → a ≠ b → pre a b ∨ pre b a;
    total_on_dequeue a b: is_pop val a → is_pop val b → a ≠ b → pre a b ∨ pre b a;
    total_on_enqueue_dequeue a b: is_push val a → is_pop val b → pre a b ∨ pre b a;
  }.

  (* --- Sequential FIFO (the key FIFO property) --- *)
  (* For queues: if enq(ia) < enq(ib) and deq(ra) < deq(rb) with val ia ra and val ib rb,
     then this is the expected FIFO behavior (first in, first out) *)
  Definition sequential_fifo pre val :=
    ∀ ia ib ra rb, val ia ra → val ib rb → pre ia ib → pre ra rb.
    (* Note: This is DIFFERENT from the LIFO property for stacks:
       Stack (LIFO): pre ia ib → pre ib ra → pre rb ra
       Queue (FIFO): pre ia ib → pre ra rb
       meaning: if ia enqueued before ib, then ra (dequeue of ia) happens before rb *)

  (* --- Sequential Queue and Set classes --- *)
  Class SequentialQueue pre val := {
    #[local] sequential_queue_sequential_set :: SequentialSet pre val;
    def_sequential_fifo : sequential_fifo pre val;
  }.

  Class SequentialEmptyQueue pre val empty := {
    #[local] sequential_empty_queue_sequential_empty_set :: SequentialEmptySet pre val empty;
    empty_def_sequential_fifo : sequential_fifo pre val;
  }.

  (* --- Linearizability definitions --- *)
  Definition linearizable_non_empty_queue pre val :=
    ConcHistory pre ∧ ∃ prt (_ : RelDecision prt), subrelation pre prt ∧ SequentialQueue prt val.

  Definition linearizable_queue pre val empty :=
    ConcHistory pre ∧
    ∃ prt (_ : RelDecision prt), subrelation pre prt ∧ SequentialEmptyQueue prt val empty.

  (* --- Helper lemmas --- *)

  Lemma wellformed_empty_then_wellformed pre val empty:
    WellformedEmptyHistory pre val empty →
    WellformedHistory (non_empty_pre pre empty) val.
  Proof.
    intros Hwfe.
    destruct Hwfe.
    rename select (all_popped_or_empty _ _) into Hadeq.
    rename select (val_then_not_pr _ _) into Hvnpr.
    constructor.
    - (* Transitive *)
      intros a b c (Hab & Hnea & Hneb) (Hbc & _ & Hnec).
      split; last split; try done.
      by etrans.
    - (* Antisymmetric *)
      intros a b (Hab & Hnea & Hneb) (Hba & _ & _).
      by eapply pre_antisymmetric.
    - (* Irreflexive *)
      intros a (Haa & _ & _).
      by eapply pre_irreflexive.
    - done.
    - done.
    - done.
    - intros a b (Hab & Hnea & Hneb).
      destruct (Hadeq a) as [Hea|Ha]; first done.
      destruct (Hadeq b) as [Heb|Hb]; first done.
      done.
    - intros ia ra Hval Hpre.
      destruct Hpre as (Hpre & _ & _).
      by eapply Hvnpr.
  Qed.

  Lemma linearizable_set_then_wellformed pre val empty:
    linearizable_set pre val empty →
    WellformedHistory (non_empty_pre pre empty) val.
  Proof.
    intros Hls.
    apply wellformed_empty_then_wellformed.
    by apply linearizable_set_then_wellformed_empty.
  Qed.

  (* --- Additional helper lemmas --- *)

  Lemma empty_rem_then_rem pre val empty ir ra rb :
    rem_order (non_empty_pre pre empty) val ir ra rb →
    WellformedHistory (non_empty_pre pre empty) val →
    rem_order pre val ir ra rb.
  Proof.
    intros (Hdeqa & Hdeqb & Horder) Hwf.
    split; last split; try done.
    destruct Horder as [(Hab & _ & _)|(c & Hrac & Hcb)].
    - left. done.
    - right. exists c. done.
  Qed.

End def.
