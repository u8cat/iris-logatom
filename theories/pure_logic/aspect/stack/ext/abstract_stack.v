(* stack.v *)
(* The stack theorem for aspect-oriented linearizability proof techique. *)

From iris_logatom.pure_logic.aspect.stack.ext Require Export conc_his_rel.
From iris_logatom.pure_logic.aspect.stack.ext Require Import remove_relaxed_stack elim_stack empty_stack.

Section proof.
  Context `{abstract_stack_model}.
  Implicit Types (pre val : relation operation) (empty : operation → Prop).

  (* stack_theorem.thy:11-13
     Let <A, pre, val> be a history, where A is the set of operations (the universe), pre is the
     precedence order, and val is the value relation. If <A, pre, val> is linearizable with respect to
     SET (linearizable_set pre val emp) and order-correct (order_correct pre val), then <A, pre, val>
     is linearizable with respect to STACK (linearizable_stack pre val emp). The predicate emp
     indicates pop-empty operations. *)
  Theorem abstract_stack_theorem pre val empty
      `{!RelDecision pre, !RelDecision val, ∀ a, Decision (empty a)} :
    linearizable_set pre val empty → order_correct pre val →
    linearizable_stack pre val empty.
  Proof.
    intros Hls Hoc.
    (* Step 1: Get ConcHistory pre from linearizable_set *)
    assert (Hch : ConcHistory pre).
    { destruct Hls as [Hch _]. done. }
    (* Step 2: Get ConcHistory (non_empty_pre pre empty) *)
    assert (Hch_ne : ConcHistory (non_empty_pre pre empty)).
    { by apply pre_conc_history_then_non_empty_pre_conc_history. }
    (* Step 3: Get WellformedHistory (non_empty_pre pre empty) val *)
    assert (Hwf_ne : WellformedHistory (non_empty_pre pre empty) val).
    { by apply linearizable_set_then_wellformed. }
    (* Step 4: Get RemoveRelaxedStack for elim_free from order_correct_then_remove_relaxed_stack *)
    destruct (order_correct_then_remove_relaxed_stack pre val empty Hls Hoc)
      as (ir' & Hir'_dec & Hrrs).
    (* Step 5: Get linearizable_non_empty_stack for elim_free from remove_relaxed_stack_linearizable_final *)
    assert (Hlin_ef : linearizable_non_empty_stack
                        (elim_free_pre (non_empty_pre pre empty) val)
                        (elim_free_val (non_empty_pre pre empty) val)).
    { apply (remove_relaxed_stack_linearizable_final _ _ (elim_free_ir (non_empty_pre pre empty) val ir')). done. }
    (* Step 6: Get linearizable_non_empty_stack (non_empty_pre pre empty) val from elimination_theorem *)
    assert (Hlin_ne : linearizable_non_empty_stack (non_empty_pre pre empty) val).
    { apply (elimination_theorem (non_empty_pre pre empty) val); [done|apply Hch_ne|done]. }
    (* Step 7: Get linearizable_stack from concurrent_empty_stack_linearizable_main *)
    by apply concurrent_empty_stack_linearizable_main.
  Qed.
End proof.
