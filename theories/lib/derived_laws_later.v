From iris.algebra Require Import monoid.
From iris.bi Require Export derived_laws_later.

Module bi.
Import interface.bi.
Import derived_laws.bi.
Import derived_laws_later.bi.

Section later_derived.
Context {SI : sidx} {PROP : bi}.

Lemma laterN_False `{!BiLöb PROP} : ⊢@{PROP} ∃ n, ▷^n False.
Proof.
  rewrite -(löb (∃ n : nat, ▷^n False)%I).
  rewrite later_exist.
  apply entails_impl, exist_elim => n.
  by rewrite -(exist_intro (S n)).
Qed.
End later_derived.
End bi.
