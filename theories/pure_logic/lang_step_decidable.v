(* lang_step_decidable.v: a language-independent interface for deciding
   bounded executions of a language whose steps may be infinitely branching. *)
(* Most of this file is LLM-generated *)
(* Claude Opus 5.5 (1M context) *)

From stdpp Require Import gmap.
From iris.program_logic Require Import language.

Class BoundedLanguage (Λ : language) := {
  prim_step_bounded e1 σ1 :
    ∃ l: list (list (observation Λ) * expr Λ * state Λ * list (expr Λ)),
    ∀ κ e2 σ2 efs, prim_step e1 σ1 κ e2 σ2 efs ↔ (κ,e2,σ2,efs) ∈ l
}.

(** An abstract interpretation of a concrete language [Λc] by a symbolic
language [Λa].

Abstract objects contain symbolic variables; an [assignment] gives them values.
An abstract state records a _path condition_: [sat a σa] says that [a]
satisfies it. A symbolic step that chooses a fresh name (heap_lang: [AllocN],
[NewProph]) introduces a fresh symbolic variable and records the freshness
condition; a symbolic step whose outcome depends on the names (heap_lang:
comparing locations, aliasing of heap accesses) branches and records the
branch condition. Only finitely many symbolic steps are possible, see
[BoundedLanguage].

The symbolic steps are sound: a symbolic step concretizes to a concrete step
under every assignment satisfying the path condition of the resulting state.
They are complete: a concrete step from a concretization is the concretization
of a symbolic step under an extended assignment, which agrees with the
original assignment on everything that is well-formed in the original state
(this matters for the other threads of a configuration).

[unify σa va v] adds the condition that [va] concretizes to [v]. It is used to
match the value returned by a thread against a given trace.

The constraint theory is up to the instance; the only requirement is that the
satisfiability of path conditions is decidable. heap_lang only needs
(dis)equalities and orders of location variables plus constant offsets. A
language with a location difference [l1 - l2] may instantiate this interface
as long as its path conditions stay decidable, but not if it also multiplies
the resulting integers: then bounded executions encode Hilbert's tenth
problem. *)
Class LanguageAbsInterp (Λc Λa : language) := {
  assignment : Type; (* an assignment to symbolic variables *)

  (* translate a concrete object to an abstract object without symbolic variables *)
  ca_e : expr Λc → expr Λa;
  ca_s : state Λc → state Λa;

  (* translate an abstract object to a concrete object, for a given assignment
  to symbolic variables *)
  ac_e : assignment → expr Λa → expr Λc;
  ac_v : assignment → val Λa → val Λc;
  ac_s : assignment → state Λa → state Λc;

  (* path conditions *)
  sat : assignment → state Λa → Prop;
  unify : state Λa → val Λa → val Λc → state Λa;

  (* well-formedness: only the symbolic variables introduced by the state occur *)
  wf_state : state Λa → Prop;
  wf_expr : state Λa → expr Λa → Prop;

  ac_ca_e a e : ac_e a (ca_e e) = e;
  ac_ca_s a σ : ac_s a (ca_s σ) = σ;
  ac_to_val a e : to_val (ac_e a e) = ac_v a <$> to_val e;

  sat_ca_s σ : ∃ a, sat a (ca_s σ);
  sat_decide σa : (∃ a, sat a σa) ∨ ¬ (∃ a, sat a σa);

  unify_sat a σa va v : sat a (unify σa va v) ↔ sat a σa ∧ ac_v a va = v;
  unify_ac_s a σa va v : ac_s a (unify σa va v) = ac_s a σa;

  wf_state_ca_s σ : wf_state (ca_s σ);
  wf_expr_ca_e σa e : wf_expr σa (ca_e e);
  wf_state_unify σa va v :
    wf_state σa → wf_expr σa (of_val va) → wf_state (unify σa va v);
  wf_expr_unify σa va v e : wf_expr σa e → wf_expr (unify σa va v) e;
  prim_step_wf e1 σ1 κ e2 σ2 efs :
    prim_step e1 σ1 κ e2 σ2 efs →
    wf_state σ1 → wf_expr σ1 e1 →
    wf_state σ2 ∧ wf_expr σ2 e2 ∧ Forall (wf_expr σ2) efs ∧
      ∀ e, wf_expr σ1 e → wf_expr σ2 e;

  (* soundness *)
  prim_step_ac a e1 σ1 κ e2 σ2 efs :
    prim_step e1 σ1 κ e2 σ2 efs → sat a σ2 →
    ∃ κc, prim_step (ac_e a e1) (ac_s a σ1) κc (ac_e a e2) (ac_s a σ2) (ac_e a <$> efs);
  prim_step_sat a e1 σ1 κ e2 σ2 efs :
    prim_step e1 σ1 κ e2 σ2 efs → sat a σ2 → sat a σ1;

  (* completeness *)
  prim_step_ca a e1 σ1 κ e2 σ2 efs :
    sat a σ1 → wf_state σ1 → wf_expr σ1 e1 →
    prim_step (ac_e a e1) (ac_s a σ1) κ e2 σ2 efs →
    ∃ κa e1' σ1' efs' a',
      prim_step e1 σ1 κa e1' σ1' efs' ∧ sat a' σ1' ∧
      e2 = ac_e a' e1' ∧ σ2 = ac_s a' σ1' ∧ efs = ac_e a' <$> efs' ∧
      ∀ e, wf_expr σ1 e → ac_e a' e = ac_e a e;
}.

Global Arguments assignment Λc Λa {_} : assert.

Class LanguageSymbolicExecutable (Λ : language) := {
  Λ_symbolic : language;
  #[global] Λ_symbolic_bounded :: BoundedLanguage Λ_symbolic;
  #[global] Λ_symbolic_abs_interp :: LanguageAbsInterp Λ Λ_symbolic;
}.
