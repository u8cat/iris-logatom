(* conc_his_rel.v, ported from concur_history_relations.thy *)
(* The part of the concurrent history relations shared by the queue and stack theorems:
   histories that are linearizable with respect to a set (bag) with emptiness checks. *)

From stdpp Require Import finite relations.
From iris_logatom.lib Require Import list.
From iris_logatom.pure_logic Require Export linear.

Class FinitePredicate {A} `{!EqDecision A} (P : A → Prop) : Prop :=
  finite_predicate: ∃ enum, NoDup enum ∧ (∀ x, P x → x ∈ enum).

Section def.
  Context {A : Type} `{!EqDecision A}.
  Implicit Types (pre val : relation A) (empty : A → Prop).

  (* concur_history_relations.thy:5 *)
  Class Abcd (r : relation A) : Prop :=
    abcd: ∀ a b c d, r a b → r c d → r a d ∨ r c b.

  (* concur_history_relations.thy:16 *)
  Lemma lem_total_then_abcd r :
    Total r → Transitive r → Abcd r.
  Proof.
    intros Htotal Htrans a b c d Hab Hcd.
    destruct (Htotal a d) as [Had|Hda].
    - left. done.
    - right. eapply Htrans; eauto.
  Qed.

  (* Variant for strict total orders using Trichotomy *)
  Lemma lem_trichotomy_then_abcd r :
    Trichotomy r → Transitive r → Abcd r.
  Proof.
    intros Htri Htrans a b c d Hab Hcd.
    destruct (Htri a d) as [Had|[Heq|Hda]].
    - left. done.
    - subst d. right. eapply Htrans; eauto.
    - right. eapply Htrans; eauto.
  Qed.

  (* concur_history_relations.thy:28 *)
  Class ConcHistory pre : Prop := {
    #[local] pre_transitive :: Transitive pre;
    #[local] pre_antisymmetric :: Antisymmetric A (=) pre;
    #[local] pre_irreflexive :: Irreflexive pre;
    #[local] pre_abcd :: Abcd pre;
  }.

  (* concur_history_relations.thy:44 *)
  Definition val_order val :=
    ∀ ia ra, val ia ra → ¬∃ b, val b ia ∨ val ra b.

  (* concur_history_relations.thy:52 *)
  Definition push_once val :=
    ∀ ia ib ra, val ia ra → val ib ra → ia = ib.
  (* concur_history_relations.thy:56 *)
  Definition pop_once val :=
    ∀ ia ra rb, val ia ra → val ia rb → ra = rb.

  (* concur_history_relations.thy:60 *)
  Definition val_then_not_pr pre val :=
    ∀ ia ra, val ia ra → ¬ pre ra ia.

  (* concur_history_relations.thy:67 *)
  Definition is_push val op :=
    ∃ op', val op op'.
  (* concur_history_relations.thy:77 *)
  Definition is_pop val op :=
    ∃ op', val op' op.

  Global Instance is_push_dec `{!Finite A} val `{!RelDecision val} a :
    Decision (is_push val a).
  Proof. unfold is_push. apply _. Qed.

  Global Instance is_pop_dec `{!Finite A} val `{!RelDecision val} a :
    Decision (is_pop val a).
  Proof. unfold is_pop. apply _. Qed.

  (* concur_history_relations.thy:444 *)
  Definition all_popped_or_empty val empty :=
    ∀ a, empty a ∨ ∃ b, val a b ∨ val b a.

  (* concur_history_relations.thy:448 *)
  Definition empty_then_not_val val empty :=
    ∀ a, empty a → ¬(∃ b, val a b) ∧ ¬(∃ b, val b a).

  (* concur_history_relations.thy:453 *)
  Class WellformedEmptyHistory pre val empty := {
    #[local] empty_pre_conchistory :: ConcHistory pre;
    #[local] empty_operation_finite :: FinitePredicate (λ a, is_push val a ∨ is_pop val a);
    empty_def_push_once : push_once val;
    empty_def_pop_once : pop_once val;
    empty_def_val_order : val_order val;
    empty_def_all_popped_or_empty : all_popped_or_empty val empty;
    empty_def_empty_then_not_val : empty_then_not_val val empty;
    empty_def_val_then_not_pr : val_then_not_pr pre val;
  }.

  (* concur_history_relations.thy:540 *)
  (* NOTE: Changed from Total to Trichotomy to support strict (irreflexive) orders.
     Trichotomy gives: pre x y ∨ x = y ∨ pre y x, which is appropriate for
     strict total orders where pre x x is always false. *)
  Class SequentialEmptyHistory pre val empty := {
    #[local] sequential_empty_history_wellformed :: WellformedEmptyHistory pre val empty;
    def_trichotomy : Trichotomy pre;
  }.

  (* concur_history_relations.thy:562 *)
  Definition correct_empty pre val empty :=
    ∀ a, empty a → ∀ ib rb, val ib rb → pre ib a ∧ pre rb a ∨ pre a ib ∧ pre a rb.

  (* concur_history_relations.thy:566 *)
  Definition non_empty_pre pre empty : relation A :=
    λ a b, pre a b ∧ ¬ empty a ∧ ¬ empty b.

  Global Instance non_empty_pre_dec pre empty `{!RelDecision pre, ∀ a, Decision (empty a)} :
    RelDecision (non_empty_pre pre empty).
  Proof. intros a b. unfold non_empty_pre. apply _. Qed.

  (* concur_history_relations.thy:578 *)
  (* Lemma non_empty_pre_then_pre pre empty :
    ∀ a b, non_empty_pre pre empty a b → pre a b ∧ ¬ empty a ∧ ¬ empty b. *)

  (* concur_history_relations.thy:581 *)
  Lemma pre_conc_history_then_non_empty_pre_conc_history pre empty :
    ConcHistory pre → ConcHistory (non_empty_pre pre empty).
  Proof.
    intros Hch.
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
  Qed.

  (* concur_history_relations.thy:744 *)
  Class SequentialEmptySet pre val empty := {
    #[local] sequential_empty_set_sequential_empty_history :: SequentialEmptyHistory pre val empty;
    def_correct_empty : correct_empty pre val empty;
  }.

  (* concur_history_relations.thy:785 *)
  (* Unlike the Isabelle formalization, the linearizations are decidable. *)
  Definition linearizable_set pre val empty :=
    ConcHistory pre ∧
    ∃ prt (_ : RelDecision prt), subrelation pre prt ∧ SequentialEmptySet prt val empty.

  (* concur_history_relations.thy:815 *)
  Lemma linearizable_set_then_wellformed_empty pre val empty :
    linearizable_set pre val empty →
    WellformedEmptyHistory pre val empty.
  Proof.
    intros (Hch & prt & _ & Hsub & Hseq).
    destruct Hseq as [Hwf _].
    destruct Hwf as [Hwfe Htotal].
    destruct Hwfe.
    rename select (val_then_not_pr _ _) into Hvnpr.
    constructor; try done.
    intros ia ra Hval Hpre.
    eapply Hvnpr; first exact Hval.
    by apply Hsub.
  Qed.
End def.
