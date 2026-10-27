From iris_logatom.lib Require Import list.
From iris_logatom.pure_logic.aspect.bag Require Import close.
From iris_logatom.pure_logic.aspect.stack Require Import ext.abstract_stack ext.vis_rr close binder.
From iris_logatom.pure_logic.aspect Require Export bag.base stack.base stack.vis.

(* The trace-level stack theorem: a trace satisfying the incrementally maintained premise
   [I_stack] (stack/base.v) is linearizable with respect to the stack model. *)
Theorem stack_theorem rme valid_value ts :
  per_tag_wellformed_bag rme valid_value ts → I_stack ts →
  trace_linearizable (M:=stack_model rme valid_value) ts.
Proof.
  intros Hwf (m & ir & HI).
  set (ts' := (close_trace ts m).1).
  set (m' := (close_trace ts m).2).
  assert (Hvalid : valid_match ts m) by by destruct HI.
  assert (Hvalid' : valid_match ts' m') by by eapply close_preserves_validity.
  assert (Hcomplete' : per_tag_complete ts') by by eapply close_complete.
  assert (Hclosed' : closed_match ts' m') by by eapply close_closed.
  assert (Hwf' : per_tag_wellformed_bag rme valid_value ts')
    by by eapply close_preserves_wellformed.
  pose proof (close_preserves_I_stack_pre rme valid_value ts m ir Hwf HI) as HI'.
  destruct (close_prefix (stack_model rme valid_value) rme valid_value ts m eq_refl Hwf)
    as (ts_mid & Hpfx_mid & Hadd_call).
  eapply (trace_linearizable_adds_call _ ts_mid Hadd_call).
  apply (trace_linearizable_prefix ts_mid ts'); first exact Hpfx_mid.
  apply (linearizable_stack__trace_linearizable_stack rme valid_value ts' m'
           Hvalid' Hcomplete' Hclosed' Hwf').
  apply (abstract_stack_theorem (trace_pre ts') (trace_val ts' m') (trace_empty ts' m')).
  - apply (trace_linearizable_bag__linearizable_set rme valid_value ts' m'
             Hvalid' Hcomplete' Hclosed' Hwf').
    by destruct HI' as (_ & ? & _).
  - exact (I_stack_pre__order_correct rme valid_value ts' m' Hvalid' Hclosed' _ Hwf' HI').
Qed.

(* The same theorem with the premise [I_stack_vis] (stack/vis.v): visibility points and the
   commit order of pops, as in the TS-stack proof of Dodds, Haas, and Kirsch (POPL'15). *)
Theorem stack_theorem_vis rme valid_value ts :
  per_tag_wellformed_bag rme valid_value ts → I_stack_vis ts →
  trace_linearizable (M:=stack_model rme valid_value) ts.
Proof.
  intros Hwf (m & pts & HI).
  set (ts' := (close_trace ts m).1).
  set (m' := (close_trace ts m).2).
  pose proof (isv_valid _ _ _ HI) as Hvalid.
  assert (Hvalid' : valid_match ts' m') by by eapply close_preserves_validity.
  assert (Hcomplete' : per_tag_complete ts') by by eapply close_complete.
  assert (Hclosed' : closed_match ts' m') by by eapply close_closed.
  assert (Hwf' : per_tag_wellformed_bag rme valid_value ts')
    by by eapply close_preserves_wellformed.
  pose proof (close_preserves_I_stack_vis_pre rme valid_value ts m pts Hwf HI) as Hcv.
  destruct (close_prefix (stack_model rme valid_value) rme valid_value ts m eq_refl Hwf)
    as (ts_mid & Hpfx_mid & Hadd_call).
  eapply (trace_linearizable_adds_call _ ts_mid Hadd_call).
  apply (trace_linearizable_prefix ts_mid ts'); first exact Hpfx_mid.
  apply (linearizable_stack__trace_linearizable_stack rme valid_value ts' m'
           Hvalid' Hcomplete' Hclosed' Hwf').
  eapply (abstract_stack_theorem_vis (trace_pre ts') (trace_val ts' m') (trace_empty ts' m') _ _).
  - apply (trace_linearizable_bag__linearizable_set rme valid_value ts' m'
             Hvalid' Hcomplete' Hclosed' Hwf').
    exact (close_preserves_pop_empty_sound rme valid_value ts m Hwf (isv_empty _ _ _ HI) Hvalid).
  - exact (closed_vis__vis_rr rme valid_value ts' m' Hvalid' Hcomplete' Hclosed' _ _ Hwf' Hcv).
Qed.
