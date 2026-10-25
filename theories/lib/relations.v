
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

(** A path [l] (as in [nsteps_list]) has an [nsteps] between any two of its positions. *)
(* This lemma was discovered by Claude Opus 5.5. *)
Lemma nsteps_list_lookup `{R : relation A} (l : list A) i j x y :
  (∀ k a b, l !! k = Some a → l !! S k = Some b → R a b) →
  i ≤ j → l !! i = Some x → l !! j = Some y →
  nsteps R (j - i) x y.
Proof.
  intros HR Hij Hi Hj.
  remember (j - i) as d eqn:Hd. revert i x Hij Hi Hd.
  induction d as [|d IH]; intros i x Hij Hi Hd.
  - assert (i = j) as -> by lia. rewrite Hj in Hi. injection Hi as ->. apply nsteps_O.
  - destruct (lookup_lt_is_Some_2 l (S i)) as [z Hz].
    { apply lookup_lt_Some in Hj. lia. }
    apply (nsteps_l _ _ _ z); first by eapply HR.
    apply (IH (S i)); [lia|done|lia].
Qed.
