(* constraint.v: satisfiability of conjunctions of comparisons between integer
   variables plus constant offsets is decidable. *)
(* Most of this file is LLM-generated *)
(* Claude Opus 5.5 (1M context) *)

From stdpp Require Import ssreflect list numbers list_numbers.

(** Path conditions of symbolic heap_lang executions compare symbolic names: a
symbolic location is a variable plus a constant offset, or a constant. A
satisfying valuation can be compressed into a bounded box: the compression
preserves the order of the values and their differences up to a bound [D] that
exceeds every difference of offsets, so it preserves every comparison. The box
is then searched exhaustively. *)

Local Open Scope Z_scope.

(** A valuation of the symbolic variables *)
Definition valuation := nat → Z.

(** A variable plus an offset, or a constant if [term_var = None] *)
Record term := Term { term_var : option nat; term_off : Z }.

Inductive cmp := CEq | CNe | CLe | CLt.

Record atom := Atom { atom_cmp : cmp; atom_lhs : term; atom_rhs : term }.

Definition term_base (ν : valuation) (t : term) : Z :=
  match term_var t with Some x => ν x | None => 0 end.
Definition term_eval (ν : valuation) (t : term) : Z := term_base ν t + term_off t.

Definition cmp_eval (c : cmp) (z1 z2 : Z) : Prop :=
  match c with
  | CEq => z1 = z2
  | CNe => z1 ≠ z2
  | CLe => z1 ≤ z2
  | CLt => z1 < z2
  end.
Global Instance cmp_eval_dec c z1 z2 : Decision (cmp_eval c z1 z2).
Proof. destruct c; simpl; apply _. Defined.

Definition atom_holds (ν : valuation) (α : atom) : Prop :=
  cmp_eval (atom_cmp α) (term_eval ν (atom_lhs α)) (term_eval ν (atom_rhs α)).
Global Instance atom_holds_dec ν α : Decision (atom_holds ν α).
Proof. rewrite /atom_holds. apply _. Defined.

Definition atoms_hold (ν : valuation) (cs : list atom) : Prop := Forall (atom_holds ν) cs.
Global Instance atoms_hold_dec ν cs : Decision (atoms_hold ν cs).
Proof. rewrite /atoms_hold. apply _. Defined.

Definition term_vars (t : term) : list nat :=
  match term_var t with Some x => [x] | None => [] end.
Definition atom_vars (α : atom) : list nat := term_vars (atom_lhs α) ++ term_vars (atom_rhs α).
Definition atoms_vars (cs : list atom) : list nat := cs ≫= atom_vars.

(** The largest absolute value of an offset *)
Definition atoms_max_off (cs : list atom) : Z :=
  foldr (λ α m, Z.abs (term_off (atom_lhs α)) `max` Z.abs (term_off (atom_rhs α)) `max` m) 0 cs.

(** The negation of an atom *)
Definition atom_neg (α : atom) : atom :=
  match atom_cmp α with
  | CEq => Atom CNe (atom_lhs α) (atom_rhs α)
  | CNe => Atom CEq (atom_lhs α) (atom_rhs α)
  | CLe => Atom CLt (atom_rhs α) (atom_lhs α)
  | CLt => Atom CLe (atom_rhs α) (atom_lhs α)
  end.

Lemma atom_neg_holds ν α : atom_holds ν (atom_neg α) ↔ ¬ atom_holds ν α.
Proof. destruct α as [[] t1 t2]; rewrite /atom_holds /=; lia. Qed.

Lemma atoms_hold_app ν cs1 cs2 :
  atoms_hold ν (cs1 ++ cs2) ↔ atoms_hold ν cs1 ∧ atoms_hold ν cs2.
Proof. apply Forall_app. Qed.

(** ** Only the variables of the atoms matter *)
Lemma term_eval_ext ν ν' t :
  (∀ x, x ∈ term_vars t → ν x = ν' x) → term_eval ν t = term_eval ν' t.
Proof.
  destruct t as [[x|] o]; rewrite /term_eval /term_base /=; intros Hagree; last done.
  rewrite Hagree //. by apply list_elem_of_singleton.
Qed.

Lemma atom_holds_ext ν ν' α :
  (∀ x, x ∈ atom_vars α → ν x = ν' x) → atom_holds ν α ↔ atom_holds ν' α.
Proof.
  intros Hagree. rewrite /atom_holds.
  assert (term_eval ν (atom_lhs α) = term_eval ν' (atom_lhs α)) as ->.
  { apply term_eval_ext. intros x Hx. apply Hagree. rewrite /atom_vars elem_of_app. by left. }
  assert (term_eval ν (atom_rhs α) = term_eval ν' (atom_rhs α)) as ->.
  { apply term_eval_ext. intros x Hx. apply Hagree. rewrite /atom_vars elem_of_app. by right. }
  done.
Qed.

Lemma atoms_hold_ext ν ν' cs :
  (∀ x, x ∈ atoms_vars cs → ν x = ν' x) → atoms_hold ν cs ↔ atoms_hold ν' cs.
Proof.
  intros Hagree. rewrite /atoms_hold !Forall_forall.
  assert (∀ α, α ∈ cs → atom_holds ν α ↔ atom_holds ν' α) as Hα.
  { intros α Hα. apply atom_holds_ext. intros x Hx.
    apply Hagree, list_elem_of_bind. by exists α. }
  split; intros Hcs α Hin; [rewrite -Hα|rewrite Hα]; auto.
Qed.

(** ** Compression *)
Local Lemma length_filter_Forall {A} (P : A → Prop) `{!∀ x, Decision (P x)} l :
  Forall P l → length (filter P l) = length l.
Proof.
  induction 1 as [|x l Hx Hl IH]; first done.
  rewrite filter_cons_True //=. by rewrite IH.
Qed.

Local Lemma length_bind_const {A B} (f : A → list B) (l : list A) n :
  (∀ x, length (f x) = n) → length (l ≫= f) = (length l * n)%nat.
Proof.
  intros Hf. induction l as [|x l IH]; first done.
  rewrite /= length_app Hf. csimpl in IH. rewrite IH. lia.
Qed.

Local Lemma cmp_eval_diff c z1 z2 w1 w2 :
  z1 - z2 = w1 - w2 → cmp_eval c z1 z2 ↔ cmp_eval c w1 w2.
Proof. destruct c; simpl; lia. Qed.

Section compress.
  (** The points [T] are spread out with distance at most [D] *)
  Context (T : list Z) (D : Z).
  Implicit Types (x y z p q : Z).

  Local Definition near z : Prop := Exists (λ t, t - D ≤ z ≤ t + D) T.
  Local Instance near_dec z : Decision (near z).
  Proof. rewrite /near. apply _. Defined.

  (** The number of points in [x, y) near [T] *)
  Local Definition cnt x y : nat := length (filter near (seqZ x (y - x))).

  (** The compression: the number of points in [base, z) near [T] *)
  Local Definition squash base z : Z := Z.of_nat (cnt base z).

  Local Lemma cnt_add x y z : x ≤ y → y ≤ z → cnt x z = (cnt x y + cnt y z)%nat.
  Proof.
    intros Hxy Hyz. rewrite /cnt.
    replace (z - x) with ((y - x) + (z - y)) by lia.
    rewrite seqZ_app; [|lia|lia].
    replace (x + (y - x)) with y by lia.
    by rewrite filter_app length_app.
  Qed.

  Local Lemma cnt_full x y :
    x ≤ y → (∀ z, x ≤ z < y → near z) → Z.of_nat (cnt x y) = y - x.
  Proof.
    intros Hxy Hnear. rewrite /cnt length_filter_Forall.
    - rewrite length_seqZ. lia.
    - apply Forall_forall. intros z Hz%elem_of_seqZ. apply Hnear. lia.
  Qed.

  Local Lemma cnt_bound x y : 0 ≤ D → Z.of_nat (cnt x y) ≤ Z.of_nat (length T) * (2 * D + 1).
  Proof.
    intros HD. rewrite /cnt.
    assert (filter near (seqZ x (y - x)) ⊆+ T ≫= (λ t, seqZ (t - D) (2 * D + 1))) as Hsub.
    { apply NoDup_submseteq; first by apply NoDup_filter, NoDup_seqZ.
      intros z (Hnear & _)%list_elem_of_filter.
      apply Exists_exists in Hnear as (t & Ht & Hz).
      apply list_elem_of_bind. exists t. split; last done.
      apply elem_of_seqZ. lia. }
    apply submseteq_length in Hsub.
    rewrite (length_bind_const _ _ (Z.to_nat (2 * D + 1))) in Hsub.
    2: { intros t. apply length_seqZ. }
    apply Nat2Z.inj_le in Hsub. rewrite Nat2Z.inj_mul Z2Nat.id in Hsub; lia.
  Qed.

  Local Lemma squash_bound base z :
    0 ≤ D → 0 ≤ squash base z ≤ Z.of_nat (length T) * (2 * D + 1).
  Proof. intros HD. rewrite /squash. pose proof (cnt_bound base z HD). lia. Qed.

  (** Compression preserves differences up to [D] between points of [T] and the
  order of points farther apart *)
  Local Lemma squash_diff base p q :
    0 ≤ D → q ∈ T → base ≤ q → q ≤ p →
    (p - q ≤ D → squash base p - squash base q = p - q) ∧
    (D < p - q → D < squash base p - squash base q).
  Proof.
    intros HD Hq Hbase Hqp.
    assert (squash base p - squash base q = Z.of_nat (cnt q p)) as ->.
    { rewrite /squash (cnt_add base q p) // Nat2Z.inj_add. lia. }
    split.
    - intros Hle. apply cnt_full; first done.
      intros z Hz. apply Exists_exists. exists q. split; [done|lia].
    - intros Hlt. rewrite (cnt_add q (q + D + 1) p); [|lia|lia].
      rewrite Nat2Z.inj_add (cnt_full q (q + D + 1)); [lia|lia|].
      intros z Hz. apply Exists_exists. exists q. split; [done|lia].
  Qed.

  Local Lemma squash_cmp base c p q o1 o2 :
    0 ≤ D → p ∈ T → q ∈ T → base ≤ p → base ≤ q → Z.abs (o2 - o1) < D →
    cmp_eval c (p + o1) (q + o2) ↔ cmp_eval c (squash base p + o1) (squash base q + o2).
  Proof.
    intros HD Hp Hq Hbp Hbq Ho.
    destruct (decide (q ≤ p)) as [Hqp|Hpq].
    - destruct (squash_diff base p q HD Hq Hbq Hqp) as [Hle Hgt].
      destruct (decide (p - q ≤ D)) as [Hd|Hd].
      + specialize (Hle Hd). destruct c; simpl; lia.
      + assert (D < squash base p - squash base q) by (apply Hgt; lia).
        destruct c; simpl; lia.
    - destruct (squash_diff base q p HD Hp Hbp ltac:(lia)) as [Hle Hgt].
      destruct (decide (q - p ≤ D)) as [Hd|Hd].
      + specialize (Hle Hd). destruct c; simpl; lia.
      + assert (D < squash base q - squash base p) by (apply Hgt; lia).
        destruct c; simpl; lia.
  Qed.
End compress.

(** ** Small model property *)
Local Lemma foldr_min_le (T : list Z) t : t ∈ T → foldr Z.min 0 T ≤ t.
Proof.
  induction T as [|t' T IH]; first by intros ?%elem_of_nil.
  intros [->|Ht]%elem_of_cons; simpl; [lia|]. specialize (IH Ht). lia.
Qed.

Local Lemma atoms_max_off_spec cs α :
  α ∈ cs →
  Z.abs (term_off (atom_lhs α)) ≤ atoms_max_off cs ∧
  Z.abs (term_off (atom_rhs α)) ≤ atoms_max_off cs.
Proof.
  induction cs as [|α' cs IH]; first by intros ?%elem_of_nil.
  intros [->|Hα]%elem_of_cons; simpl; [lia|]. specialize (IH Hα). lia.
Qed.

Local Lemma atoms_max_off_nonneg cs : 0 ≤ atoms_max_off cs.
Proof. induction cs as [|α cs IH]; simpl; lia. Qed.

(** The size of the box *)
Definition atoms_bound (cs : list atom) : Z :=
  Z.of_nat (S (length (atoms_vars cs))) * (2 * (2 * atoms_max_off cs + 1) + 1).

Lemma atoms_hold_small ν cs :
  atoms_hold ν cs → ∃ ν', atoms_hold ν' cs ∧ ∀ x, Z.abs (ν' x) ≤ atoms_bound cs.
Proof.
  intros Hcs.
  pose proof (atoms_max_off_nonneg cs) as Hoff.
  set (D := 2 * atoms_max_off cs + 1).
  set (T := 0 :: (ν <$> atoms_vars cs)).
  set (base := foldr Z.min 0 T).
  set (ν' := λ x, squash T D base (ν x) - squash T D base 0).
  assert (∀ t, term_eval ν' t = squash T D base (term_base ν t) - squash T D base 0 + term_off t)
    as Hterm.
  { intros [[x|] o]; rewrite /term_eval /term_base /ν' /=; lia. }
  assert (∀ α t, α ∈ cs → t = atom_lhs α ∨ t = atom_rhs α → term_base ν t ∈ T) as HT.
  { intros α [[x|] o] Hα Ht; rewrite /term_base /=; last by apply elem_of_cons; left.
    apply elem_of_cons. right. apply list_elem_of_fmap_2, list_elem_of_bind.
    exists α. split; last done. rewrite /atom_vars elem_of_app.
    destruct Ht as [<-|<-]; [left|right]; by apply list_elem_of_singleton. }
  exists ν'. split.
  - rewrite /atoms_hold Forall_forall in Hcs.
    rewrite /atoms_hold Forall_forall. intros α Hα.
    specialize (Hcs α Hα).
    destruct (atoms_max_off_spec cs α Hα) as [Ho1 Ho2].
    rewrite /atom_holds !Hterm.
    rewrite /atom_holds /term_eval in Hcs.
    rewrite -(cmp_eval_diff _ (squash T D base (term_base ν (atom_lhs α)) + term_off (atom_lhs α))
      (squash T D base (term_base ν (atom_rhs α)) + term_off (atom_rhs α))); last lia.
    rewrite -squash_cmp; [done|lia|..|lia].
    + by apply (HT α); [|left].
    + by apply (HT α); [|right].
    + apply foldr_min_le. by apply (HT α); [|left].
    + apply foldr_min_le. by apply (HT α); [|right].
  - intros x. rewrite /ν'.
    pose proof (squash_bound T D base (ν x) ltac:(lia)) as Hx.
    pose proof (squash_bound T D base 0 ltac:(lia)) as H0.
    rewrite /atoms_bound -/D.
    replace (Z.of_nat (S (length (atoms_vars cs)))) with (Z.of_nat (length T)); first lia.
    by rewrite /T /= length_fmap.
Qed.

(** ** Exhaustive search *)
Fixpoint valuations (xs : list nat) (B : Z) : list valuation :=
  match xs with
  | [] => [λ _, 0]
  | x :: xs =>
    z ← seqZ (- B) (2 * B + 1); ν ← valuations xs B;
    [λ y, if decide (y = x) then z else ν y]
  end.

Lemma valuations_complete xs B ν :
  (∀ x, x ∈ xs → Z.abs (ν x) ≤ B) →
  ∃ ν', ν' ∈ valuations xs B ∧ ∀ x, x ∈ xs → ν' x = ν x.
Proof.
  induction xs as [|x xs IH]; intros Hbound.
  { exists (λ _, 0). split; first by apply list_elem_of_singleton.
    by intros x ?%elem_of_nil. }
  destruct IH as (ν' & Hν' & Hagree).
  { intros y Hy. apply Hbound. apply elem_of_cons. by right. }
  exists (λ y, if decide (y = x) then ν x else ν' y). split.
  - simpl. apply list_elem_of_bind. exists (ν x). split.
    + apply list_elem_of_bind. exists ν'. split; [by apply list_elem_of_singleton|done].
    + apply elem_of_seqZ. assert (Z.abs (ν x) ≤ B) by (apply Hbound, elem_of_cons; by left).
      lia.
  - intros y Hy. case_decide as Hyx; first by subst.
    apply Hagree. by apply elem_of_cons in Hy as [?|?].
Qed.

(** ** Decidability *)
Lemma atoms_hold_decide cs : (∃ ν, atoms_hold ν cs) ∨ ¬ (∃ ν, atoms_hold ν cs).
Proof.
  destruct (decide (Exists (λ ν, atoms_hold ν cs)
    (valuations (atoms_vars cs) (atoms_bound cs)))) as [Hex|Hnex].
  - left. apply Exists_exists in Hex as (ν & _ & Hν). by exists ν.
  - right. intros (ν & Hν).
    apply atoms_hold_small in Hν as (ν' & Hν' & Hbound).
    destruct (valuations_complete (atoms_vars cs) (atoms_bound cs) ν')
      as (ν'' & Hin & Hagree).
    { intros x _. apply Hbound. }
    apply Hnex, Exists_exists. exists ν''. split; first done.
    by apply (atoms_hold_ext ν'' ν' cs).
Qed.
