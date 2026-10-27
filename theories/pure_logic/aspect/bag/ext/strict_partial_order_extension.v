(* strict_partial_order_extension.v *)
(* Constructive linear extension of an acyclic relation on a finite type.
   Replaces a Zorn's-lemma proof for arbitrary types. *)

From Stdlib Require Import Arith.Wf_nat.
From stdpp Require Import finite list relations.
From iris_logatom.lib Require Import relations.

(* On a finite type, [tc R] is witnessed by paths of bounded length. *)
Section tc_bounded.
  Context `{Finite A}.
  Context (R : relation A).

  (* Pigeonhole-based shortening: an nsteps path with n > |enum A| can be
     shortened to length ≥ 1 by pigeonholing on the first n vertices
     (positions 0..n-1), avoiding the potentially-degenerate (0, n) repeat. *)
  Lemma nsteps_shorten n x y :
    1 ≤ n →
    length (enum A) < n →
    nsteps R n x y →
    ∃ k, 1 ≤ k < n ∧ nsteps R k x y.
  Proof.
    intros Hn1 Hgt Hs.
    apply nsteps_list in Hs as (l & Hlen & Hh & Ht & HR).
    rewrite head_lookup in Hh. rewrite last_lookup, Hlen in Ht.
    (* Pigeonhole on the prefix of length n (positions 0..n-1). *)
    set (l' := take n l).
    assert (Hl'_len : length l' = n) by (subst l'; rewrite length_take; lia).
    assert (Hl'_sub : l' ⊆ enum A) by (intros a _; apply elem_of_enum).
    assert (Hl'_pigeon : length (enum A) < length l') by lia.
    destruct (list_pigeonhole l' (enum A) Hl'_sub Hl'_pigeon)
      as (i1 & i2 & v & Hi12 & Hi1' & Hi2').
    apply lookup_lt_Some in Hi1' as Hi1l.
    apply lookup_lt_Some in Hi2' as Hi2l.
    rewrite Hl'_len in Hi1l, Hi2l.
    (* take n l !! i = l !! i when i < n. *)
    assert (Hi1 : l !! i1 = Some v).
    { subst l'. rewrite lookup_take_Some in Hi1'. tauto. }
    assert (Hi2 : l !! i2 = Some v).
    { subst l'. rewrite lookup_take_Some in Hi2'. tauto. }
    exists (i1 + (n - i2)). split; first lia.
    assert (Hpart1 : nsteps R (i1 - 0) x v).
    { apply (nsteps_list_lookup l 0 i1 x v); [exact HR | lia | exact Hh | exact Hi1]. }
    assert (Hpart1' : nsteps R i1 x v).
    { replace i1 with (i1 - 0) by lia. exact Hpart1. }
    assert (Hpart2 : nsteps R (n - i2) v y).
    { apply (nsteps_list_lookup l i2 n v y); [exact HR | lia | exact Hi2 | exact Ht]. }
    by apply (nsteps_trans i1 (n - i2) x v y).
  Qed.

  Lemma tc_iff_bounded_step x y :
    tc R x y ↔ ∃ n, 1 ≤ n ∧ n ≤ length (enum A) ∧ nsteps R n x y.
  Proof.
    split; last (intros (n & Hn & _ & Hs); apply tc_nsteps; by exists n).
    intros Htc. apply tc_nsteps in Htc as (n & Hn & Hs).
    revert x y Hn Hs. induction n as [n IH] using lt_wf_ind.
    intros x y Hn Hs.
    destruct (decide (n ≤ length (enum A))) as [Hle|Hgt]; first by exists n.
    assert (Hgt' : length (enum A) < n) by lia.
    destruct (nsteps_shorten n x y Hn Hgt' Hs) as (k & [Hk1 Hk_lt] & Hsk).
    by apply (IH k Hk_lt x y Hk1 Hsk).
  Qed.

End tc_bounded.

(* Decidability of the transitive closure of a decidable relation on a finite type. *)
Section tc_decision.
  Context `{Finite A} (R : relation A) `{!RelDecision R}.

  Local Instance nsteps_decision n : RelDecision (nsteps R n).
  Proof.
    induction n as [|n IH]; intros x y.
    - destruct (decide (x = y)) as [->|Hne]; [left; constructor|right; by inv 1].
    - destruct (decide (∃ z, R x z ∧ nsteps R n z y)) as [Hex|Hno].
      + left. destruct Hex as (z & Hxz & Hzy). by eapply nsteps_l.
      + right. inv 1. naive_solver.
  Qed.

  Local Lemma bounded_exists_decision (P : nat → Prop) `{∀ n, Decision (P n)} N :
    Decision (∃ n, 1 ≤ n ∧ n ≤ N ∧ P n).
  Proof.
    induction N as [|N IH].
    - right. intros (n & ? & ? & _). lia.
    - destruct IH as [Hex|Hnone].
      + left. destruct Hex as (n & ? & ? & ?). exists n. split_and!; [done|lia|done].
      + destruct (decide (P (S N))) as [HP|HnP].
        * left. exists (S N). split_and!; [lia|done|done].
        * right. intros (n & ? & ? & Hn). destruct (decide (n ≤ N)).
          -- apply Hnone. by exists n.
          -- by assert (n = S N) as -> by lia.
  Qed.

  Global Instance tc_decision : RelDecision (tc R).
  Proof.
    intros x y.
    destruct (bounded_exists_decision (λ n, nsteps R n x y) (length (enum A))) as [Hb|Hb].
    - left. by apply tc_iff_bounded_step.
    - right. by rewrite tc_iff_bounded_step.
  Qed.
End tc_decision.

Section sort.
  Context `{Finite A}.
  Context (R : relation A).
  Context `{!RelDecision R}.
  Context `{!Irreflexive R}.
  Context `{!Transitive R}.

  Local Lemma R_asym x y : R x y → ¬ R y x.
  Proof. intros Hxy Hyx. apply (irreflexivity R x). etrans; eauto. Qed.

  (* Pick an R-minimal element from a non-empty NoDup list. *)
  Local Lemma pickmin (l : list A) :
    NoDup l → l ≠ [] →
    ∃ m, m ∈ l ∧ ∀ y, y ∈ l → ¬ R y m.
  Proof.
    induction l as [|a rest IH]; intros Hnd Hne; first done.
    destruct rest as [|b rest'].
    - exists a. split; first by left.
      intros y Hin. rewrite list_elem_of_singleton in Hin. subst y.
      intros Hr. by eapply (irreflexivity R).
    - assert (Hnd' : NoDup (b :: rest')) by (apply NoDup_cons in Hnd; tauto).
      destruct (IH Hnd' ltac:(done)) as (mn & Hmn_in & Hmin).
      destruct (decide (R a mn)) as [Ham|Hnam].
      + exists a. split; first by left.
        intros y Hin. rewrite elem_of_cons in Hin. destruct Hin as [->|Hin].
        * intros Hr. by eapply (irreflexivity R).
        * intros Hya. apply (Hmin y Hin). etrans; eauto.
      + exists mn. split; first by right.
        intros y Hin. rewrite elem_of_cons in Hin. destruct Hin as [->|Hin].
        * exact Hnam.
        * by apply Hmin.
  Qed.

  (* Topological sort: produce a NoDup permutation consistent with R. *)
  Lemma topo_sort_aux :
    ∀ (n : nat) (l : list A),
      length l = n →
      NoDup l →
      ∃ ord, NoDup ord ∧ (∀ x, x ∈ ord ↔ x ∈ l) ∧
        (∀ i j x y, i < j → ord !! i = Some x → ord !! j = Some y → ¬ R y x).
  Proof.
    intros n. induction n as [|n IH]; intros l Hlen Hnd.
    - destruct l; last (simpl in Hlen; lia).
      exists []. split_and!.
      + constructor.
      + intros x. done.
      + intros i j x y Hij Hi. destruct i; done.
    - destruct l as [|a l']; first (simpl in Hlen; lia).
      destruct (pickmin (a :: l') Hnd ltac:(done)) as (m & Hm_in & Hmin).
      apply list_elem_of_split in Hm_in as (before & after & Hsplit).
      set (l_rest := before ++ after).
      assert (Hnd_rest : NoDup l_rest).
      { unfold l_rest. rewrite Hsplit in Hnd.
        rewrite NoDup_app in Hnd. destruct Hnd as (Hnd_b & Hmn_b & Hnd_r).
        rewrite NoDup_cons in Hnd_r. destruct Hnd_r as [Hm_a Hnd_a].
        rewrite NoDup_app. split_and!; try done.
        intros x Hx_b Hx_a. apply (Hmn_b x Hx_b). right. exact Hx_a. }
      assert (Hlen_rest : length l_rest = n).
      { unfold l_rest. rewrite length_app.
        apply (f_equal length) in Hsplit.
        rewrite length_app in Hsplit. simpl in Hsplit, Hlen. lia. }
      assert (Hm_notin_rest : m ∉ l_rest).
      { unfold l_rest. rewrite Hsplit in Hnd.
        rewrite NoDup_app in Hnd. destruct Hnd as (_ & Hm_b & Hnd_r).
        rewrite NoDup_cons in Hnd_r. destruct Hnd_r as [Hm_a _].
        intros Hin. apply elem_of_app in Hin as [|].
        - apply (Hm_b m); [done|left; done].
        - done. }
      destruct (IH l_rest Hlen_rest Hnd_rest)
        as (ord_rest & Hnd_ord & Hord_mem & Hord_sorted).
      exists (m :: ord_rest). split_and!.
      + apply NoDup_cons. split; last exact Hnd_ord.
        intros Hin. apply Hord_mem in Hin. by apply Hm_notin_rest.
      + intros τ. split.
        * intros Hin. rewrite elem_of_cons in Hin.
          rewrite Hsplit. destruct Hin as [->|Hin_rest].
          { apply elem_of_app. right. left. }
          apply Hord_mem in Hin_rest. unfold l_rest in Hin_rest.
          apply elem_of_app in Hin_rest as [Hin_b|Hin_a].
          { apply elem_of_app. left. exact Hin_b. }
          apply elem_of_app. right. right. exact Hin_a.
        * intros Hin_l. destruct (decide (τ = m)) as [->|Hne];
            first (left; done).
          right. apply Hord_mem. unfold l_rest. rewrite Hsplit in Hin_l.
          apply elem_of_app in Hin_l as [Hin_b|Hin_ma].
          { apply elem_of_app. left. exact Hin_b. }
          rewrite elem_of_cons in Hin_ma. destruct Hin_ma as [->|Hin_a];
            first done. apply elem_of_app. right. exact Hin_a.
      + intros i j x y Hij Hi Hj.
        destruct i as [|i'].
        * simpl in Hi. injection Hi as <-.
          destruct j as [|j']; first lia. simpl in Hj.
          assert (Hy_in_ord : y ∈ ord_rest)
            by (eapply list_elem_of_lookup_2; exact Hj).
          assert (Hy_in_rest : y ∈ l_rest) by (by apply Hord_mem).
          assert (Hy_in_l : y ∈ a :: l').
          { rewrite Hsplit. unfold l_rest in Hy_in_rest.
            apply elem_of_app in Hy_in_rest as [|].
            - apply elem_of_app. left. done.
            - apply elem_of_app. right. right. done. }
          by apply Hmin.
        * destruct j as [|j']; first lia.
          simpl in Hi, Hj.
          apply (Hord_sorted i' j' x y); [lia|exact Hi|exact Hj].
  Qed.

End sort.

(* Decidability of "x positioned before y" in an ordering. *)
Section pos_lt.
  Context `{Finite A}.
  Context (ord : list A) (Hnd : NoDup ord).

  Definition pos_lt : relation A :=
    λ x y, ∃ i j, ord !! i = Some x ∧ ord !! j = Some y ∧ i < j.

  Lemma pos_lt_irreflexive : Irreflexive pos_lt.
  Proof.
    intros x (i & j & Hi & Hj & Hij).
    assert (i = j) by (eapply NoDup_lookup; eauto). lia.
  Qed.

  Lemma pos_lt_transitive : Transitive pos_lt.
  Proof.
    intros x y z (i1 & j1 & Hi1 & Hj1 & Hij1) (i2 & j2 & Hi2 & Hj2 & Hij2).
    assert (Heq : j1 = i2) by (eapply NoDup_lookup; [|exact Hj1|exact Hi2]; done).
    exists i1, j2. split_and!; [done|done|lia].
  Qed.

  (* For NoDup lists, list_find with equality gives the unique position. *)
  Global Instance pos_lt_dec : RelDecision pos_lt.
  Proof.
    intros x y. unfold pos_lt.
    destruct (list_find (eq x) ord) as [[i x']|] eqn:Hxfind.
    - apply list_find_Some in Hxfind as (Hxi & <- & _).
      destruct (list_find (eq y) ord) as [[j y']|] eqn:Hyfind.
      + apply list_find_Some in Hyfind as (Hyj & <- & _).
        destruct (decide (i < j)) as [Hij|Hnij].
        * left. exists i, j. by repeat split.
        * right. intros (i' & j' & Hi' & Hj' & Hij').
          assert (Hi_eq : i = i') by (eapply NoDup_lookup; eauto).
          assert (Hj_eq : j = j') by (eapply NoDup_lookup; eauto).
          subst i' j'. done.
      + right. intros (i' & j' & Hi' & Hj' & _).
        apply list_find_None in Hyfind.
        rewrite Forall_forall in Hyfind.
        eapply (Hyfind y); last reflexivity.
        eapply list_elem_of_lookup_2. exact Hj'.
    - right. intros (i' & j' & Hi' & _).
      apply list_find_None in Hxfind.
      rewrite Forall_forall in Hxfind.
      eapply (Hxfind x); last reflexivity.
      eapply list_elem_of_lookup_2. exact Hi'.
  Qed.

End pos_lt.

(* The main theorem: every irreflexive transitive decidable relation on a
   finite type extends to a decidable linear (total) strict order. *)
Theorem strict_partial_order_extension `{Finite A}
    (R : relation A) `{!RelDecision R} `{!Irreflexive R} `{!Transitive R} :
  ∃ T (_ : RelDecision T),
    Irreflexive T ∧ Transitive T ∧
    (∀ x y, R x y → T x y) ∧
    (∀ x y, x ≠ y → T x y ∨ T y x).
Proof.
  destruct (topo_sort_aux R (length (enum A)) (enum A) eq_refl (NoDup_enum _))
    as (ord & Hnd & Hmem & Hsorted).
  exists (pos_lt ord), (pos_lt_dec ord Hnd). split_and!.
  - apply (pos_lt_irreflexive ord Hnd).
  - apply (pos_lt_transitive ord Hnd).
  - (* R x y → pos_lt ord x y *)
    intros x y Hxy.
    assert (Hx_in : x ∈ ord) by (apply Hmem, elem_of_enum).
    assert (Hy_in : y ∈ ord) by (apply Hmem, elem_of_enum).
    apply list_elem_of_lookup_1 in Hx_in as [i Hi].
    apply list_elem_of_lookup_1 in Hy_in as [j Hj].
    destruct (decide (i < j)) as [Hij|Hij].
    + exists i, j. by repeat split.
    + exfalso.
      destruct (decide (i = j)) as [->|Hne_ij].
      { rewrite Hj in Hi. injection Hi as Hi_eq. subst.
        by eapply (irreflexivity R). }
      assert (j < i) by lia.
      eapply (Hsorted j i y x); [done|exact Hj|exact Hi|exact Hxy].
  - (* totality *)
    intros x y Hne.
    assert (Hx_in : x ∈ ord) by (apply Hmem, elem_of_enum).
    assert (Hy_in : y ∈ ord) by (apply Hmem, elem_of_enum).
    apply list_elem_of_lookup_1 in Hx_in as [i Hi].
    apply list_elem_of_lookup_1 in Hy_in as [j Hj].
    destruct (Nat.lt_total i j) as [Hij|[Heq|Hji]].
    + left. exists i, j. by repeat split.
    + subst j. rewrite Hi in Hj. injection Hj as <-. done.
    + right. exists j, i. by repeat split.
Qed.
