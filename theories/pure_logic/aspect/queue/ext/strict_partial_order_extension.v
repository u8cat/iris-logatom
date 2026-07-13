(* strict_partial_order_extension.v *)
(* Constructive linear extension of an acyclic relation on a finite type.
   Replaces a Zorn's-lemma proof for arbitrary types. *)

From Stdlib Require Import Logic.Decidable.
From Stdlib Require Import Arith.Wf_nat.
From stdpp Require Import finite list relations.

(* Decidability of the transitive closure of a decidable relation on a
   finite type. *)
Section tc_dec.
  Context `{Finite A}.
  Context (R : relation A) (R_dec : ∀ x y, decidable (R x y)).

  (* `step_n n x y` says there is a length-n R-path from x to y. *)
  Fixpoint step_n (n : nat) (x y : A) : Prop :=
    match n with
    | 0 => x = y
    | S k => ∃ z, R x z ∧ step_n k z y
    end.

  Local Lemma dec_list_exists_T (l : list A) (P : A → Prop) :
    (∀ x, decidable (P x)) →
    decidable (∃ x, x ∈ l ∧ P x).
  Proof.
    intros HP. induction l as [|a l' IH].
    - right. intros (x & Hx & _). by apply elem_of_nil in Hx.
    - destruct (HP a) as [Ha | Hna].
      + left. exists a. split; [by left | exact Ha].
      + destruct IH as [(x & Hxl & Hpx) | Hno].
        * left. exists x. split; [by right | exact Hpx].
        * right. intros (x & Hxl & Hpx).
          rewrite elem_of_cons in Hxl. destruct Hxl as [->|Hxl]; first done.
          apply Hno. by exists x.
  Qed.

  Local Lemma dec_exists_finite (P : A → Prop) :
    (∀ x, decidable (P x)) →
    decidable (∃ x, P x).
  Proof.
    intros HP. destruct (dec_list_exists_T (enum A) P HP) as [(x & _ & Hx)|Hno].
    - left. by exists x.
    - right. intros (x & Hx). apply Hno. exists x. split; [apply elem_of_enum|done].
  Qed.

  Lemma step_n_dec n x y : decidable (step_n n x y).
  Proof.
    revert x y. induction n as [|n IH]; intros x y.
    - simpl. destruct (decide (x = y)); [by left | by right].
    - simpl. apply dec_exists_finite. intros z.
      apply dec_and; [apply R_dec | apply IH].
  Qed.

  Lemma step_n_then_tc n x y : 1 ≤ n → step_n n x y → tc R x y.
  Proof.
    revert x y. induction n as [|n IH]; intros x y Hn Hs; first lia.
    destruct n as [|n'].
    - simpl in Hs. destruct Hs as (z & Hxz & ->). by apply tc_once.
    - simpl in Hs. destruct Hs as (z & Hxz & Hzy).
      eapply tc_l; first exact Hxz. apply IH; [lia | exact Hzy].
  Qed.

  Lemma tc_then_step_n x y : tc R x y → ∃ n, 1 ≤ n ∧ step_n n x y.
  Proof.
    induction 1 as [a b Hab|a b c Hab Hbc IH].
    - exists 1. split; [lia|]. by exists b.
    - destruct IH as (n & Hn & Hstep).
      exists (S n). split; [lia|]. exists b. done.
  Qed.

  Lemma step_n_compose n m x y z :
    step_n n x y → step_n m y z → step_n (n + m) x z.
  Proof.
    revert x. induction n as [|n IH]; intros x Hxy Hyz.
    - simpl in Hxy. by subst y.
    - simpl in Hxy. destruct Hxy as (u & Hxu & Huy).
      simpl. exists u. split; [done|]. by apply IH.
  Qed.

  (* Extract a path of intermediate vertices realising step_n n x y. *)
  Lemma step_n_path n x y :
    step_n n x y →
    ∃ l, length l = S n ∧
         l !! 0 = Some x ∧ l !! n = Some y ∧
         (∀ k, k < n → ∃ u v, l !! k = Some u ∧ l !! (S k) = Some v ∧ R u v).
  Proof.
    revert x. induction n as [|n IH]; intros x Hs.
    - simpl in Hs. subst y. exists [x]. split_and!.
      + done.
      + done.
      + done.
      + intros k Hk. lia.
    - simpl in Hs. destruct Hs as (z & Hxz & Hzy).
      destruct (IH z Hzy) as (l & Hlen & Hh & Ht & HR).
      exists (x :: l). split_and!.
      + simpl. by f_equal.
      + done.
      + simpl. exact Ht.
      + intros k Hk. destruct k as [|k'].
        * exists x, z. split_and!.
          -- done.
          -- simpl. exact Hh.
          -- exact Hxz.
        * destruct (HR k' ltac:(lia)) as (u & v & Hu & Hv & Hr).
          exists u, v. simpl. done.
  Qed.

  (* Extract a sub-step_n from a longer path: from position i to position j of
     a list with R-edges between consecutive elements. *)
  Lemma step_n_subpath (l : list A) i j x y :
    i ≤ j →
    l !! i = Some x →
    l !! j = Some y →
    (∀ k, i ≤ k < j → ∃ u v, l !! k = Some u ∧ l !! (S k) = Some v ∧ R u v) →
    step_n (j - i) x y.
  Proof.
    intros Hij Hi Hj HR.
    remember (j - i) as d eqn:Hd.
    revert i j x y Hij Hi Hj HR Hd.
    induction d as [|d IH]; intros i j x y Hij Hi Hj HR Hd.
    - assert (i = j) by lia. subst j. rewrite Hj in Hi.
      injection Hi as <-. by simpl.
    - assert (i < j) by lia.
      destruct (HR i ltac:(lia)) as (u & v & Hu & Hv & Hr).
      rewrite Hi in Hu. injection Hu as <-.
      simpl. exists v. split; first done.
      apply (IH (S i) j v y); [lia | exact Hv | exact Hj | | lia].
      intros k Hk. apply HR. lia.
  Qed.

  (* Pigeonhole-based shortening: a step_n path with n > |enum A| can be
     shortened to length ≥ 1 by pigeonholing on the first n vertices
     (positions 0..n-1), avoiding the potentially-degenerate (0, n) repeat. *)
  Lemma step_n_shorten n x y :
    1 ≤ n →
    length (enum A) < n →
    step_n n x y →
    ∃ k, 1 ≤ k < n ∧ step_n k x y.
  Proof.
    intros Hn1 Hgt Hs.
    destruct (step_n_path n x y Hs) as (l & Hlen & Hh & Ht & HR).
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
    assert (Hpart1 : step_n (i1 - 0) x v).
    { apply (step_n_subpath l 0 i1 x v); [lia | exact Hh | exact Hi1 |].
      intros k Hk. apply HR. lia. }
    assert (Hpart1' : step_n i1 x v).
    { replace i1 with (i1 - 0) by lia. exact Hpart1. }
    assert (Hpart2 : step_n (n - i2) v y).
    { apply (step_n_subpath l i2 n v y); [lia | exact Hi2 | exact Ht |].
      intros k Hk. apply HR. lia. }
    by apply (step_n_compose i1 (n - i2) x v y).
  Qed.

  Lemma tc_iff_bounded_step x y :
    tc R x y ↔ ∃ n, 1 ≤ n ∧ n ≤ length (enum A) ∧ step_n n x y.
  Proof.
    split; last (intros (n & Hn & _ & Hs); by eapply step_n_then_tc).
    intros Htc. apply tc_then_step_n in Htc as (n & Hn & Hs).
    revert x y Hn Hs. induction n as [n IH] using lt_wf_ind.
    intros x y Hn Hs.
    destruct (decide (n ≤ length (enum A))) as [Hle|Hgt]; first by exists n.
    assert (Hgt' : length (enum A) < n) by lia.
    destruct (step_n_shorten n x y Hn Hgt' Hs) as (k & [Hk1 Hk_lt] & Hsk).
    by apply (IH k Hk_lt x y Hk1 Hsk).
  Qed.

  Lemma tc_decidable x y : decidable (tc R x y).
  Proof.
    (* Decide via existence of a length-n path for n in [1, length (enum A)]. *)
    assert (Hdec_bounded : decidable (∃ n, 1 ≤ n ∧ n ≤ length (enum A) ∧ step_n n x y)).
    { induction (length (enum A)) as [|N IH].
      - right. intros (n & Hn & Hub & _). lia.
      - destruct IH as [(n & Hn & Hub & Hstep) | Hnone].
        + left. exists n. split_and!; [done | lia | done].
        + destruct (step_n_dec (S N) x y) as [Hs|Hns].
          * left. exists (S N). split_and!; [lia | done | done].
          * right. intros (n & Hn & Hub & Hstep).
            destruct (decide (n ≤ N)) as [|Hgt].
            -- apply Hnone. exists n. done.
            -- assert (n = S N) by lia. subst n. done. }
    destruct Hdec_bounded as [Hsome|Hnone].
    - left. apply tc_iff_bounded_step. done.
    - right. intros Htc. apply tc_iff_bounded_step in Htc. done.
  Qed.

End tc_dec.

Section sort.
  Context `{Finite A}.
  Context (R : relation A).
  Context (R_dec : ∀ x y, decidable (R x y)).
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
      destruct (R_dec a mn) as [Ham|Hnam].
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
  Lemma pos_lt_decidable x y : decidable (pos_lt x y).
  Proof.
    unfold pos_lt, decidable.
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
    (R : relation A) (R_dec : ∀ x y, decidable (R x y))
    `{!Irreflexive R} `{!Transitive R} :
  ∃ T : relation A,
    Irreflexive T ∧ Transitive T ∧
    (∀ x y, R x y → T x y) ∧
    (∀ x y, x ≠ y → T x y ∨ T y x) ∧
    (∀ x y, decidable (T x y)).
Proof.
  destruct (topo_sort_aux R R_dec (length (enum A)) (enum A) eq_refl (NoDup_enum _))
    as (ord & Hnd & Hmem & Hsorted).
  exists (pos_lt ord). split_and!.
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
  - apply (pos_lt_decidable ord Hnd).
Qed.
