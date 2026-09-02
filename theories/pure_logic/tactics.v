From iris_logatom.pure_logic Require Import steps.
From iris.heap_lang Require Import tactics.

(* Tactics for HeapLang *)

Ltac erased_steps_pure :=
  lazymatch goal with
  | |- rtc erased_step (?e::?ts1, ?σ1) (?ts2, ?σ2) =>
    let H := fresh in
    reshape_expr e ltac:(fun K e' =>
      eassert (H: PureExec _ _ e' _) by tc_solve;
      change e with (fill K e'));
    refine (erased_steps_pure_exec_head _ _ _ _ _ σ1 σ2 ts1 ts2 H _ _);
    clear H;
    [try done|simpl]
  | _ => fail "erased_steps_pure: not a 'rtc erased_step'"
  end.

Ltac erased_steps_apply_core lem :=
  lazymatch goal with
  | |- rtc erased_step (?e::?efs1, ?σ1) (?t3,?σ3) =>
    reshape_expr e ltac:(fun K e1 =>
      change e with (fill K e1);
      first [
        refine (erased_steps_apply_head K e1 σ1 efs1 _ _ _ t3 σ3 _ _);
        [eapply lem|simpl]
      | refine (erased_steps_apply_head_nofork K e1 σ1 efs1 _ _ t3 σ3 _ _);
        [eapply lem|simpl]
      | refine (erased_steps_apply_once_head K e1 σ1 efs1 _ _ _ t3 σ3 _ _);
        [eapply lem|simpl]
      | refine (erased_steps_apply_once_head_nofork K e1 σ1 efs1 _ _ t3 σ3 _ _);
        [eapply lem|simpl]])
  | _ => fail 1 "erased_steps_apply: not a 'rtc erased_step'"
  end.

Tactic Notation "erased_steps_apply" open_constr(lem) :=
  first [erased_steps_apply_core lem].

(* Some very ad-hoc tactics to operate on the second thread *)
Ltac erased_steps_pure2 :=
  lazymatch goal with
  | |- rtc erased_step (?e0::?e::?ts1, ?σ1) (?ts2, ?σ2) =>
    let H := fresh in
    reshape_expr e ltac:(fun K e' =>
      eassert (H: PureExec _ _ e' _) by tc_solve;
      change e with (fill K e'));
    refine (erased_steps_pure_exec _ _ _ _ _ σ1 σ2 [e0] ts1 ts2 H _ _);
    clear H;
    [try done|simpl]
  | _ => fail "erased_steps_pure: not a 'rtc erased_step'"
  end.

Tactic Notation "erased_steps_apply2" open_constr(lem) :=
  etrans; [apply erased_steps_cons_l; erased_steps_apply lem; last reflexivity|].

(* Update two threads at the same time *)
Ltac erased_steps_2apply_core lem :=
  lazymatch goal with
  | |- rtc erased_step (?e0::?e::?efs1, ?σ1) (?t3,?σ3) =>
    reshape_expr e ltac:(fun K e1 =>
      change e with (fill K e1);
      refine (erased_steps_apply K [e0] e1 σ1 efs1 [_] _ _ _ t3 σ3 _ _ _);
      [reflexivity|eapply lem|simpl])
  | _ => fail 1 "erased_steps_2apply: not a 'rtc erased_step'"
  end.
Tactic Notation "erased_steps_2apply" open_constr(lem) :=
  first [erased_steps_2apply_core lem].
