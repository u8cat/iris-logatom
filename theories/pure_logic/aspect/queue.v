From iris_logatom.lib Require Import list.
From iris_logatom.pure_logic.aspect.bag Require Import close.
From iris_logatom.pure_logic.aspect.queue Require Import ext.abstract_queue close binder.
From iris_logatom.pure_logic.aspect Require Export bag.base queue.base.

Theorem queue_theorem rme valid_value ts :
  per_tag_wellformed_bag rme valid_value ts → I_queue ts →
  trace_linearizable (M:=queue_model rme valid_value) ts.
Proof.
  intros Hper_tag_wf [m HI_queue_pre].
  set (ts' := (close_trace ts m).1).
  set (m' := (close_trace ts m).2).
  assert (Hvalid: valid_match ts m) by by destruct HI_queue_pre.
  assert (Hvalid': valid_match ts' m') by by eapply close_preserves_validity.
  assert (Hcomplete': per_tag_complete ts') by by eapply close_complete.
  assert (Hclosed' : closed_match ts' m') by by eapply close_closed.

  destruct (close_prefix (queue_model rme valid_value) rme valid_value ts m
              eq_refl Hper_tag_wf)
    as (ts_mid & Hpfx_mid & Hadd_call).
  eapply (trace_linearizable_adds_call _ ts_mid Hadd_call).
  apply (trace_linearizable_prefix ts_mid ts'); first exact Hpfx_mid.
  eapply linearizable_queue__trace_linearizable_queue; [eassumption..| |].
  { by eapply close_preserves_wellformed. }
  apply (abstract_queue_theorem (trace_pre ts') (trace_val ts' m') (trace_empty ts' m')).
  - eapply trace_linearizable_bag__linearizable_set; [assumption..| |].
    + by eapply close_preserves_wellformed.
    + destruct HI_queue_pre as (_ & ? & _).
      by eapply close_preserves_pop_empty_sound.
  - apply I_queue_pre__order_correct; [assumption..|].
    by eapply close_preserves_I_queue_pre.
Qed.
