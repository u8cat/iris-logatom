
From stdpp Require Import ssreflect.

Local Lemma nsteps_ind_r_weak `{R : relation A} (P : nat → A → A → Prop)
    (Prefl : ∀ x, P 0 x x)
    (Pstep : ∀ n x y z, nsteps R n x y → R y z → P n x y → P (S n) x z) :
  ∀ n x z, nsteps R n x z → P n x z.
Proof.
  cut (∀ n y z, nsteps R n y z → ∀ m x, nsteps R m x y → P m x y → P (m+n) x z).
  { intros H n x y Hsteps.
    exact (H n x y Hsteps 0 x (nsteps_O R x) (Prefl x)). }
  induction 1 as [|n].
  - intros ??. rewrite right_id_L. auto.
  - intros m ?. replace (m+S n) with (S m+n) by lia.
    eauto using nsteps_r.
Qed.

Lemma nsteps_ind_r `{R : relation A} (P : nat → A → Prop) (x : A)
  (Prefl : P 0 x) (Pstep : ∀ n y z, nsteps R n x y → R y z → P n y → P (S n) z) :
  ∀ n z, nsteps R n x z → P n z.
Proof.
  intros n z p. revert n x z p Prefl Pstep. refine (nsteps_ind_r_weak _ _ _); eauto.
Qed.
