(* conc_his_rel.v, ported from aspect-oriented queue linearizability *)
(* Adapts the concurrent history relations from the stack theory to queues *)
(* Key difference: FIFO ordering instead of LIFO *)

From Stdlib Require Export Logic.Decidable.
From stdpp Require Import finite relations.
From iris_logatom.lib Require Import list.
From iris_logatom.pure_logic Require Export linear.

Class abstract_queue_model := AbstractQueueModel {
  operation : Type;
  operation_eq_dec :: EqDecision operation;
  operation_finite :: Finite operation;
}.

(* Decidable existential over a list of operations. *)
Lemma dec_list_exists `{abstract_queue_model} (l : list operation) (P : operation → Prop) :
  (∀ x, decidable (P x)) →
  decidable (∃ x, x ∈ l ∧ P x).
Proof.
  intros HP. induction l as [|a l' IH].
  - right. intros (x & Hx & _). by apply elem_of_nil in Hx.
  - destruct (HP a) as [Ha | Hna].
    + left. exists a. split; [by left | exact Ha].
    + destruct IH as [(x & Hxl & Hpx) | Hno].
      * left. exists x. split; [by right | exact Hpx].
      * right. intros (x & Hxl & Hpx).
        rewrite elem_of_cons in Hxl. destruct Hxl as [->|Hxl]; first done.
        apply Hno. by exists x.
Qed.

Lemma dec_exists_op `{abstract_queue_model} (P : operation → Prop) :
  (∀ x, decidable (P x)) →
  decidable (∃ x, P x).
Proof.
  intros HP. destruct (dec_list_exists (enum operation) P HP) as [(x & _ & Hx)|Hno].
  - left. by exists x.
  - right. intros (x & Hx). apply Hno. exists x. split; [apply elem_of_enum|done].
Qed.

Notation Acyclic R := (Irreflexive (tc R)).
Local Instance relation_union {A} : Union (relation A) :=
  λ r1 r2, Relation_Operators.union A r1 r2.

Section def.
  Context `{abstract_queue_model}.
  Implicit Types (pre val : relation operation) (empty : operation → Prop).

  (* --- Abcd property (same as stack) --- *)
  Class Abcd (r : relation operation) : Prop :=
    abcd: ∀ a b c d, r a b → r c d → r a d ∨ r c b.

  Lemma lem_total_then_abcd r :
    Total r → Transitive r → Abcd r.
  Proof.
    intros Htotal Htrans a b c d Hab Hcd.
    destruct (Htotal a d) as [Had|Hda].
    - left. done.
    - right. eapply Htrans; eauto.
  Qed.

  Lemma lem_trichotomy_then_abcd r :
    Trichotomy r → Transitive r → Abcd r.
  Proof.
    intros Htri Htrans a b c d Hab Hcd.
    destruct (Htri a d) as [Had|[Heq|Hda]].
    - left. done.
    - subst d. right. eapply Htrans; eauto.
    - right. eapply Htrans; eauto.
  Qed.

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

  (* --- ConcHistory (same as stack) --- *)
  Class ConcHistory pre : Prop := {
    #[local] pre_transitive :: Transitive pre;
    #[local] pre_antisymmetric :: Antisymmetric operation (=) pre;
    #[local] pre_irreflexive :: Irreflexive pre;
    #[local] pre_abcd :: Abcd pre;
    conc_pre_decidable : ∀ a b, decidable (pre a b);
  }.

  (* --- Value relation properties (adapted for queue: enqueue/dequeue) --- *)

  (* val_order: No operation can be both an enqueue target and dequeue source *)
  Definition val_order val :=
    ∀ ia ra, val ia ra → ¬∃ b, val b ia ∨ val ra b.

  (* enqueue_once: Each dequeue returns a unique enqueued value *)
  Definition enqueue_once val :=
    ∀ ia ib ra, val ia ra → val ib ra → ia = ib.

  (* dequeue_once: Each enqueue is dequeued at most once *)
  Definition dequeue_once val :=
    ∀ ia ra rb, val ia ra → val ia rb → ra = rb.

  Definition val_then_not_pr pre val :=
    ∀ ia ra, val ia ra → ¬ pre ra ia.

  (* --- Enqueue and dequeue predicates --- *)
  Definition is_enqueue val op :=
    ∃ op', val op op'.

  Definition is_dequeue val op :=
    ∃ op', val op' op.

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
    λ a b, is_enqueue val a ∧ is_enqueue val b ∧ (pre a b ∨ ∃ c, pre a c ∧ ir c b).

  (* rem_order: Ordering on dequeue operations
     For FIFO: if deq(a) precedes deq(b), then a was dequeued first *)
  Definition rem_order (pre val ir : relation operation) : relation operation :=
    λ a b, is_dequeue val a ∧ is_dequeue val b ∧ (pre a b ∨ (∃ c, ir a c ∧ ir c b)).

  Definition order_correct pre val :=
    (∀ e1 e2 d1 d2, pre e1 e2 → val e1 d1 → val e2 d2 → ¬ pre d2 d1).

  (* --- Wellformed History --- *)
  Class WellformedHistory pre val := {
    #[local] wf_pre_transitive :: Transitive pre;
    #[local] wf_pre_antisymmetric :: Antisymmetric operation (=) pre;
    #[local] wf_pre_irreflexive :: Irreflexive pre;
    def_enqueue_once : enqueue_once val;
    def_dequeue_once : dequeue_once val;
    def_val_order : val_order val;
    def_enqueue_or_dequeue : ∀ a b, pre a b → (∃ c, val a c ∨ val c a) ∧ (∃ c, val b c ∨ val c b);
    def_val_then_not_pr : val_then_not_pr pre val;
    def_wf_pre_decidable : ∀ a b, decidable (pre a b);
    def_wf_val_decidable : ∀ a b, decidable (val a b);
  }.

  (* Helper lemmas for WellformedHistory *)
  Lemma lem_enqueue_or_dequeue1 pre val a b :
    WellformedHistory pre val → pre a b → is_enqueue val a ∨ is_dequeue val a.
  Proof.
    intros Hwf Hpre.
    destruct (def_enqueue_or_dequeue a b Hpre) as [[c [Hac|Hca]] _].
    - left. exists c. done.
    - right. exists c. done.
  Qed.

  Lemma lem_enqueue_or_dequeue2 pre val a b :
    WellformedHistory pre val → pre a b → is_enqueue val b ∨ is_dequeue val b.
  Proof.
    intros Hwf Hpre.
    destruct (def_enqueue_or_dequeue a b Hpre) as [_ [c [Hbc|Hcb]]].
    - left. exists c. done.
    - right. exists c. done.
  Qed.

  Lemma lem_enqueue_then_dequeue_exists val a : is_enqueue val a → ∃ b, val a b ∧ is_dequeue val b.
  Proof.
    intros [ra Hvara].
    exists ra. split; [done|].
    exists a. done.
  Qed.

  Lemma lem_dequeue_then_enqueue_exists val a : is_dequeue val a → ∃ b, val b a ∧ is_enqueue val b.
  Proof.
    intros [ia Hvalia].
    exists ia. split; [done|].
    exists a. done.
  Qed.

  Lemma lem_val_then_enqueue_and_dequeue val a b : val a b → is_enqueue val a ∧ is_dequeue val b.
  Proof.
    intros Hab.
    split.
    - exists b. done.
    - exists a. done.
  Qed.

  (* Helper: val a b implies a is enqueue *)
  Lemma val_enqueue val a b : val a b → is_enqueue val a.
  Proof.
    intros Hab. exists b. done.
  Qed.

  (* Helper: val a b implies b is dequeue *)
  Lemma val_dequeue val a b : val a b → is_dequeue val b.
  Proof.
    intros Hab. exists a. done.
  Qed.

  (* --- Sequential Set (same structure as stack) --- *)
  Class SequentialSet pre val := {
    sequential_set_wellformed :: WellformedHistory pre val;
    total_on_enqueue a b : is_enqueue val a → is_enqueue val b → a ≠ b → pre a b ∨ pre b a;
    total_on_dequeue a b: is_dequeue val a → is_dequeue val b → a ≠ b → pre a b ∨ pre b a;
    total_on_enqueue_dequeue a b: is_enqueue val a → is_dequeue val b → pre a b ∨ pre b a;
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

  (* --- Empty operation handling --- *)
  Definition all_dequeued_or_empty val empty :=
    ∀ a, empty a ∨ ∃ b, val a b ∨ val b a.

  Definition empty_then_not_val val empty :=
    ∀ a, empty a → ¬(∃ b, val a b) ∧ ¬(∃ b, val b a).

  Class WellformedEmptyHistory pre val empty := {
    #[local] empty_pre_conchistory :: ConcHistory pre;
    empty_def_enqueue_once : enqueue_once val;
    empty_def_dequeue_once : dequeue_once val;
    empty_def_val_order : val_order val;
    empty_def_all_dequeued_or_empty : all_dequeued_or_empty val empty;
    empty_def_empty_then_not_val : empty_then_not_val val empty;
    empty_def_val_then_not_pr : val_then_not_pr pre val;
    empty_def_empty_decidable : ∀ a, decidable (empty a);
    empty_def_val_decidable : ∀ a b, decidable (val a b);
  }.

  Class SequentialEmptyHistory pre val empty := {
    #[local] sequential_empty_history_wellformed :: WellformedEmptyHistory pre val empty;
    def_trichotomy : Trichotomy pre;
  }.

  Definition correct_empty pre val empty :=
    ∀ a, empty a → ∀ ib rb, val ib rb → pre ib a ∧ pre rb a ∨ pre a ib ∧ pre a rb.

  Definition non_empty_pre pre empty : relation operation :=
    λ a b, pre a b ∧ ¬ empty a ∧ ¬ empty b.

  (* --- Sequential Queue and Set classes --- *)
  Class SequentialQueue pre val := {
    #[local] sequential_queue_sequential_set :: SequentialSet pre val;
    def_sequential_fifo : sequential_fifo pre val;
  }.

  Class SequentialEmptySet pre val empty := {
    #[local] sequential_empty_set_sequential_empty_history :: SequentialEmptyHistory pre val empty;
    def_correct_empty : correct_empty pre val empty;
  }.

  Class SequentialEmptyQueue pre val empty := {
    #[local] sequential_empty_queue_sequential_empty_set :: SequentialEmptySet pre val empty;
    empty_def_sequential_fifo : sequential_fifo pre val;
  }.

  (* --- Linearizability definitions --- *)
  Definition linearizable_set pre val empty :=
    ConcHistory pre ∧ ∃ prt, subrelation pre prt ∧ SequentialEmptySet prt val empty.

  Definition linearizable_non_empty_queue pre val :=
    ConcHistory pre ∧ ∃ prt, subrelation pre prt ∧ SequentialQueue prt val.

  Definition linearizable_queue pre val empty :=
    ConcHistory pre ∧ ∃ prt, subrelation pre prt ∧ SequentialEmptyQueue prt val empty.

  (* --- Helper lemmas --- *)

  Lemma pre_conc_history_then_non_empty_pre_conc_history pre empty :
    ConcHistory pre →
    (∀ a, decidable (empty a)) →
    ConcHistory (non_empty_pre pre empty).
  Proof.
    intros Hch Hemp_dec.
    constructor.
    - intros a b c (Hab & Hnea & Hneb) (Hbc & Hneb' & Hnec).
      split; last split; try done.
      by etrans.
    - intros a b (Hab & Hnea & Hneb) (Hba & Hneb' & Hnea').
      by eapply pre_antisymmetric.
    - intros a (Haa & Hnea & Hnea').
      by eapply pre_irreflexive.
    - intros a b c d (Hab & Hnea & Hneb) (Hcd & Hnec & Hned).
      destruct (abcd a b c d Hab Hcd) as [Had|Hcb].
      + left. split; last split; done.
      + right. split; last split; done.
    - intros a b. unfold non_empty_pre.
      apply dec_and; first by apply conc_pre_decidable.
      apply dec_and; by apply dec_not, Hemp_dec.
  Qed.

  Lemma linearizable_set_then_wellformed_empty pre val empty :
    linearizable_set pre val empty →
    WellformedEmptyHistory pre val empty.
  Proof.
    intros (Hch & prt & Hsub & Hseq).
    destruct Hseq as [Hwf _].
    destruct Hwf as [Hwfe Htotal].
    destruct Hwfe.
    rename select (val_then_not_pr _ _) into Hvnpr.
    constructor; try done.
    intros ia ra Hval Hpre.
    eapply Hvnpr; first exact Hval.
    by apply Hsub.
  Qed.

  Lemma wellformed_empty_then_wellformed pre val empty:
    WellformedEmptyHistory pre val empty →
    WellformedHistory (non_empty_pre pre empty) val.
  Proof.
    intros Hwfe.
    assert (Hpre_dec : ∀ a b, decidable (pre a b)) by apply conc_pre_decidable.
    destruct Hwfe.
    rename select (all_dequeued_or_empty _ _) into Hadeq.
    rename select (val_then_not_pr _ _) into Hvnpr.
    rename select (∀ a, decidable (empty a)) into Hemp_dec.
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
    - intros a b. unfold non_empty_pre.
      apply dec_and; first by apply Hpre_dec.
      apply dec_and; by apply dec_not, Hemp_dec.
    - done.
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
