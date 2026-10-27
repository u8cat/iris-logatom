(* instance.v: heap_lang is symbolically executable. *)
(* Most of this file is LLM-generated *)
(* Claude Opus 5.5 (1M context) *)

From iris_logatom.pure_logic Require Import lang_step_decidable.
From iris_logatom.heap_lang.decide Require Import complete.
From iris.heap_lang Require Import lang.

Global Instance heap_lang_abs_interp : LanguageAbsInterp heap_lang sym_heap_lang := {|
  assignment := valuation;
  ca_e := ca_expr;
  ca_s := ca_state;
  ac_e := ac_expr;
  ac_v := ac_val;
  ac_s := ac_state;
  sat := ssat;
  unify := sunify;
  wf_state := sstate_wf;
  wf_expr := sexpr_wf_in;
  ac_ca_e := ac_ca_expr;
  ac_ca_s := ac_ca_state;
  ac_to_val := ac_expr_to_val;
  sat_ca_s σ := ex_intro _ (λ _, 0%Z) (ssat_ca_state _ σ);
  sat_decide := ssat_decide;
  unify_sat := sunify_sat;
  unify_ac_s := sunify_ac_state;
  wf_state_ca_s := sstate_wf_ca_state;
  wf_expr_ca_e := sexpr_wf_in_ca;
  wf_state_unify := sstate_wf_sunify;
  wf_expr_unify := sexpr_wf_in_sunify;
  prim_step_wf := sprim_step_wf;
  prim_step_ac := sprim_step_sound;
  prim_step_sat := sprim_step_sat;
  prim_step_ca := sprim_step_complete;
|}.

Global Instance heap_lang_symbolic_executable : LanguageSymbolicExecutable heap_lang :=
  {| Λ_symbolic := sym_heap_lang |}.
