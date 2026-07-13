From stdpp Require Import countable.
From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import lang.

Global Instance state_eqdecision : EqDecision state.
Proof. solve_decision. Defined.

Global Instance state_countable : Countable state.
Proof.
  refine (inj_countable'
    (λ σ, (heap σ,used_proph_id σ))
    (λ '(h,p), {| heap := h; used_proph_id := p|}) _).
  by intros [].
Qed.
