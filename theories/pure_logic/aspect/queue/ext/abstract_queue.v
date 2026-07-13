From iris_logatom.pure_logic.aspect.queue.ext Require Export conc_his_rel.
From iris_logatom.pure_logic.aspect.queue.ext Require Import insert_relaxed_no_deq_order empty_queue.

Section proof.
  Context `{abstract_queue_model}.
  Implicit Types (pre val : relation operation) (empty : operation → Prop).

  (* queue_theorem.thy:11-13
     Let <A, pre, val> be a history, where A is the set of operations (the universe), pre is the
     precedence order, and val is the value relation. If <A, pre, val> is linearizable with respect to
     SET (linearizable_set pre val emp) and order-correct (order_correct pre val), then <A, pre, val>
     is linearizable with respect to QUEUE (linearizable_queue pre val emp). The predicate emp
     indicates pop-empty operations. *)
  Theorem abstract_queue_theorem pre val empty :
    linearizable_set pre val empty → order_correct pre val →
    linearizable_queue pre val empty.
  Proof.
    intros Hls Hoc.
    assert (Hch : ConcHistory pre).
    { destruct Hls as [Hch _]. done. }
    assert (Hempty_dec : ∀ a, decidable (empty a)).
    { destruct Hls as [_ (prt & _ & Hsel)].
      destruct Hsel as [Hseh _]. destruct Hseh as [Hweh _].
      by destruct Hweh as [_ _ _ _ _ _ _ ? _]. }
    assert (Hch_ne : ConcHistory (non_empty_pre pre empty)).
    { by apply pre_conc_history_then_non_empty_pre_conc_history. }
    assert (Hwf_ne : WellformedHistory (non_empty_pre pre empty) val).
    { by apply linearizable_set_then_wellformed. }
    specialize (order_correct_then_pr_relaxed_queue pre val empty Hls Hoc) as Hiprrq.
    assert (Hlin_ef : linearizable_non_empty_queue
                        (non_empty_pre pre empty) val).
    { apply (insert_pr_relaxed_queue_linearizable_final _ _).
      { eauto. }
      { done. }
    }
    by apply concurrent_empty_queue_linearizable_main.
  Qed.
End proof.
