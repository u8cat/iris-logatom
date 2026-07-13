(** not_stuck_restrict.v: a general heap-restriction lemma for heap_lang.

  Target lemma: fix a length-[n] list of values [ws]. If an expression
  [e] is [not_stuck] under *every* extension of [σ] by [ws] at a fresh
  starting location, then [e] is [not_stuck] under [σ] itself.

  Strengthenings over a naive single-cell universal-value formulation:
  - [n] adjacent locations instead of one;
  - the values [ws] are a *fixed* parameter outside the quantifier over
    the starting location, so the hypothesis only needs to hold for that
    particular [ws], not for every possible value choice.

  Reducibility is monotone upward under heap extension
  ([base_reducible_mono] in [state_set.v]), but the reverse fails
  pointwise: an extension could unstick [e] by providing the specific
  cell [e] needs. The fix is to quantify over starting locations: if
  [e] is not stuck under *every* fresh-range extension, then for any
  specific missing cell [e] might be waiting on, some starting
  location's range avoids that cell, so the extension fails to unstick
  [e], contradicting universality.

  We use two disjoint [n]-cell ranges as witnesses: any problematic
  [head_step] references a single location [l''], which can land in
  at most one of the two disjoint ranges, so the other extension's
  reducibility transfers back to [σ].

  The proof factors through a helper [base_step_reducible_in_σ]
  proved by induction on the inner [base_step]. For the ResolveS
  case the induction hypothesis peels off the outer Resolve layer
  and applies recursively to the nested base_step, so any finite
  nesting of Resolve is handled uniformly. *)

(* Most of this file is LLM-generated *)
(* Claude Opus 4.7 (1M context) *)

From stdpp Require Import fin_map_dom.
From iris.program_logic Require Import language ectx_language.
From iris.heap_lang Require Export lang notation.
From iris_logatom.pure_logic Require Import state_set.

Notation σ_ext l ws σ :=
  (state_upd_heap (λ h, heap_array l ws ∪ h) σ).

(** Characterize [heap_array]'s lookup: a key is either inside the
  range and takes a value from [ws], or outside and absent. *)
Local Lemma heap_array_lookup_in (l : loc) (ws : list val) (i : nat) :
  i < length ws →
  ∃ w, ws !! i = Some w ∧ heap_array l ws !! (l +ₗ i) = Some (Some w).
Proof.
  intros Hi.
  destruct (lookup_lt_is_Some_2 ws i Hi) as [w Hw].
  exists w. split; first done.
  apply heap_array_lookup. exists (Z.of_nat i), w.
  split_and!; [lia|done|done|].
  by rewrite Nat2Z.id.
Qed.

Local Lemma heap_array_lookup_out (l : loc) (ws : list val) (k : loc) :
  (∀ i : nat, i < length ws → k ≠ l +ₗ i) →
  heap_array l ws !! k = None.
Proof.
  intros Hk. destruct (heap_array l ws !! k) as [ow|] eqn:Hlk; last done.
  exfalso. apply heap_array_lookup in Hlk as (j & w & Hj & -> & -> & Hw).
  apply (Hk (Z.to_nat j)).
  - apply lookup_lt_Some in Hw. done.
  - rewrite Z2Nat.id //.
Qed.

Local Lemma heap_array_lookup_same_σ (l : loc) (ws : list val) (σh : gmap loc (option val)) (k : loc) :
  (∀ i : nat, i < length ws → k ≠ l +ₗ i) →
  (heap_array l ws ∪ σh) !! k = σh !! k.
Proof.
  intros Hk.
  rewrite lookup_union_r //.
  by apply heap_array_lookup_out.
Qed.

Local Instance decide_in_range (l l1 : loc) (n : nat) :
  Decision (∃ i : nat, i < n ∧ l = l1 +ₗ i).
Proof.
  destruct l as [k], l1 as [k1].
  destruct (decide (0 ≤ k - k1)%Z) as [Hpos|Hneg]; last first.
  { right. intros (i & Hi & Heq). rewrite /Loc.add /= in Heq.
    injection Heq as Heq. lia. }
  destruct (decide (Z.to_nat (k - k1) < n)%nat) as [Hlt|Hge]; last first.
  { right. intros (i & Hi & Heq). rewrite /Loc.add /= in Heq.
    injection Heq as Heq. lia. }
  destruct (decide (k = k1 + Z.of_nat (Z.to_nat (k - k1)))%Z) as [Heq|Hne]; last first.
  { right. intros (i & Hi & HEq). rewrite /Loc.add /= in HEq.
    injection HEq as HEq. rewrite Z2Nat.id in Hne; last done.
    apply Hne. lia. }
  left. exists (Z.to_nat (k - k1)). split; first done.
  rewrite /Loc.add /=. f_equal. lia.
Defined.

Local Lemma heap_array_fresh_disjoint (l : loc) (ws : list val) (σh : gmap loc (option val)) :
  (∀ i : nat, i < length ws → l +ₗ i ∉ dom σh) →
  heap_array l ws ##ₘ σh.
Proof.
  intros Hfresh. apply map_disjoint_spec. intros k w1 w2 Hl Hσ.
  apply heap_array_lookup in Hl as (j & w' & Hj & -> & -> & Hw').
  apply lookup_lt_Some in Hw' as Hj_lt.
  apply (Hfresh (Z.to_nat j) Hj_lt). rewrite Z2Nat.id //.
  apply elem_of_dom. by eexists.
Qed.

(** Subset lemma: if both ranges are fresh in σ and disjoint from each
  other, σ extended with ws1 at l1 is a submap of σ extended with ws1
  at l1 and ws2 at l2. *)
Local Lemma subseteq_ext_l1 (σ : state) (l1 l2 : loc) (ws1 ws2 : list val) :
  (∀ i : nat, i < length ws1 → l1 +ₗ i ∉ dom σ.(heap)) →
  (∀ i : nat, i < length ws2 → l2 +ₗ i ∉ dom σ.(heap)) →
  (∀ i j : nat, i < length ws1 → j < length ws2 → l1 +ₗ i ≠ l2 +ₗ j) →
  σ_ext l1 ws1 σ ⊆ σ_ext l2 ws2 (σ_ext l1 ws1 σ).
Proof.
  intros Hl1 Hl2 Hdisj. split; simpl; last done.
  apply map_subseteq_spec. intros k v Hlk.
  assert (Hl2_k: heap_array l2 ws2 !! k = None).
  { apply heap_array_lookup_out. intros i Hi Heq_k. subst k.
    apply lookup_union_Some_raw in Hlk as [Hin|[Hout Hin]].
    - apply heap_array_lookup in Hin as (j & w' & Hj & Heq_j & -> & Hw).
      apply lookup_lt_Some in Hw as Hj_lt.
      apply (Hdisj (Z.to_nat j) i Hj_lt Hi).
      destruct l1 as [k1], l2 as [k2].
      rewrite /Loc.add /= in Heq_j |- *.
      injection Heq_j as Heq_j. f_equal. lia.
    - by apply (Hl2 i Hi), elem_of_dom; eexists. }
  by rewrite lookup_union_r.
Qed.

Local Lemma subseteq_ext_l2 (σ : state) (l1 l2 : loc) (ws1 ws2 : list val) :
  (∀ i : nat, i < length ws1 → l1 +ₗ i ∉ dom σ.(heap)) →
  σ_ext l2 ws2 σ ⊆ σ_ext l2 ws2 (σ_ext l1 ws1 σ).
Proof.
  intros Hl1. split; simpl; last done.
  apply map_subseteq_spec. intros k v Hlk.
  apply lookup_union_Some_raw in Hlk as [Hin|[Hout Hin]].
  - by rewrite lookup_union_l'.
  - rewrite lookup_union_r; last done.
    rewrite lookup_union_r; first done.
    apply heap_array_lookup_out. intros i Hi Heq_k. subst k.
    apply (Hl1 i Hi), elem_of_dom. by eexists.
Qed.

(** Given base-steps at the same fill-decomposition in two disjoint
  fresh-range extensions of σ (possibly with different extension
  values ws1, ws2), the redex shape forces the two e's to agree.
  Proved via [base_redex_unique] after lifting both to the joint
  state. *)
Local Lemma heap_op_align
    (σ : state) (l1 l2 : loc) (ws1 ws2 : list val) (e_base : expr)
    (K1 K2 : list ectx_item)
    (κ1 : list observation) (e1' : expr) (σ1' : state) (efs1 : list expr)
    (κ2 : list observation) (e2' : expr) (σ2' : state) (efs2 : list expr)
    (e_r2 : expr) :
  (∀ i : nat, i < length ws1 → l1 +ₗ i ∉ dom σ.(heap)) →
  (∀ i : nat, i < length ws2 → l2 +ₗ i ∉ dom σ.(heap)) →
  (∀ i j : nat, i < length ws1 → j < length ws2 → l1 +ₗ i ≠ l2 +ₗ j) →
  base_step e_base (σ_ext l1 ws1 σ) κ1 e1' σ1' efs1 →
  base_step e_r2 (σ_ext l2 ws2 σ) κ2 e2' σ2' efs2 →
  fill K1 e_base = fill K2 e_r2 →
  e_r2 = e_base.
Proof.
  intros Hl1 Hl2 Hdisj Hbase1 Hbase2 Heq.
  pose proof (subseteq_ext_l1 σ l1 l2 ws1 ws2 Hl1 Hl2 Hdisj) as Hsub1.
  pose proof (subseteq_ext_l2 σ l1 l2 ws1 ws2 Hl1) as Hsub2.
  assert (Hred1: base_reducible e_base (σ_ext l2 ws2 (σ_ext l1 ws1 σ))).
  { eapply base_reducible_mono; first exact Hsub1. by do 4 eexists. }
  assert (Hred2: base_reducible e_r2 (σ_ext l2 ws2 (σ_ext l1 ws1 σ))).
  { eapply base_reducible_mono; first exact Hsub2. by do 4 eexists. }
  by pose proof (base_redex_unique _ _ _ _ _ Heq Hred1 Hred2) as [_ ->].
Qed.

(** Core helper, proved by induction on the base_step: given that the
  same expression has a base_step in one fresh-range extension of σ
  and is reducible in a disjoint fresh-range extension (possibly with
  different values), it is reducible in σ itself. The ResolveS case
  uses the induction hypothesis to peel off the Resolve layer and
  applies recursively to the nested base_step. *)
Local Lemma base_step_reducible_in_σ
    (e_r : expr) (σ : state) (l1 l2 : loc) (ws1 ws2 : list val)
    (κ : list observation) (e' : expr) (σ' : state) (efs : list expr) :
  (∀ i : nat, i < length ws1 → l1 +ₗ i ∉ dom σ.(heap)) →
  (∀ i : nat, i < length ws2 → l2 +ₗ i ∉ dom σ.(heap)) →
  (∀ i j : nat, i < length ws1 → j < length ws2 → l1 +ₗ i ≠ l2 +ₗ j) →
  base_step e_r (σ_ext l1 ws1 σ) κ e' σ' efs →
  base_reducible e_r (σ_ext l2 ws2 σ) →
  base_reducible e_r σ.
Proof.
  intros Hl1 Hl2 Hdisj Hbase1.
  remember (σ_ext l1 ws1 σ) as σ_l1 eqn:Hσ_l1.
  induction Hbase1 as [ | | | | | | | | | | | | |
                       |
                       l v σ0 H |
                       l v σ0 H |
                       l v w σ0 H |
                       l v1 v2 σ0 H |
                       l v1 v2 vl σ0 b H Hvsafe Hbeq |
                       l i1 i2 σ0 H |
                       |
                       |
                       p v e_inner σ0 w σ'_inner κs_inner ts_inner
                         Hbase_inner IH Hp_in ];
    intros Hred2.
  (* Dispatch: pure cases, AllocN, NewProph, Fork close directly;
     heap ops use the [l0 = l1 +ₗ i] case split; ResolveS uses IH. *)
  (* 1-13: pure *)
  1-13: by do 4 eexists; econstructor; eauto.
  (* 14. AllocN *)
  1: { do 4 eexists.
       apply (AllocNS _ _ _ (Loc.fresh (dom σ.(heap)))); first done.
       intros i ? ?. apply not_elem_of_dom_1, Loc.fresh_fresh. done. }
  (* 21. Fork *)
  7: by do 4 eexists; econstructor.
  (* 22. NewProph *)
  7: by do 4 eexists; econstructor; apply is_fresh.
  (* 23. ResolveS *)
  7: { destruct Hred2 as (κ2' & e_out2 & σ'_out2 & efs_out2 & Hbase_res2).
       inversion Hbase_res2; subst.
       rename select (base_step e_inner _ _ _ _ _) into Hbase_inner_l2.
       assert (Hinner_red_l2: base_reducible e_inner (σ_ext l2 ws2 σ))
         by by do 4 eexists.
       destruct (IH eq_refl Hinner_red_l2)
         as (κ_new & e_new & σ_new & efs_new & Hbase_new).
       pose proof (base_step_to_val _ _ _ _ _ _ _ _ _ _ _
                     Hbase_inner Hbase_new ltac:(by eexists)) as [v_new Hv_new].
       apply of_to_val in Hv_new as <-.
       do 4 eexists. econstructor; first exact Hbase_new.
       simpl in Hp_in. exact Hp_in. }
  (* 15-20: heap ops — handle each with the same case split. *)
  (* 15. FreeS *)
  - subst σ0; simpl in *.
    destruct (decide (∃ i : nat, i < length ws1 ∧ l = l1 +ₗ i))
      as [(i & Hi_lt & ->)|Hnotin].
    + exfalso.
      destruct Hred2 as (? & ? & ? & ? & Hbase2).
      inversion Hbase2; subst; simpl in *.
      match goal with H1 : (heap_array l2 ws2 ∪ _) !! _ = Some (Some _) |- _ =>
        rewrite heap_array_lookup_same_σ in H1;
          [|intros j Hj_lt Heq; apply (Hdisj i j Hi_lt Hj_lt); exact Heq];
        apply (Hl1 i Hi_lt), elem_of_dom;
        by rewrite H1
      end.
    + rewrite heap_array_lookup_same_σ in H;
        [|intros i Hi_lt Heq; by apply Hnotin; exists i].
      do 4 eexists. by eapply FreeS.
  (* 16. LoadS *)
  - subst σ0; simpl in *.
    destruct (decide (∃ i : nat, i < length ws1 ∧ l = l1 +ₗ i))
      as [(i & Hi_lt & ->)|Hnotin].
    + exfalso.
      destruct Hred2 as (? & ? & ? & ? & Hbase2).
      inversion Hbase2;
        subst; simpl in *.
      match goal with H1 : (heap_array l2 ws2 ∪ _) !! _ = Some (Some _) |- _ =>
        rewrite heap_array_lookup_same_σ in H1;
          [|intros j Hj_lt Heq; apply (Hdisj i j Hi_lt Hj_lt); exact Heq];
        apply (Hl1 i Hi_lt), elem_of_dom;
        by rewrite H1
      end.
    + rewrite heap_array_lookup_same_σ in H;
        [|intros i Hi_lt Heq; by apply Hnotin; exists i].
      do 4 eexists. by eapply LoadS.
  (* 17. StoreS *)
  - subst σ0; simpl in *.
    destruct (decide (∃ i : nat, i < length ws1 ∧ l = l1 +ₗ i))
      as [(i & Hi_lt & ->)|Hnotin].
    + exfalso.
      destruct Hred2 as (? & ? & ? & ? & Hbase2).
      inversion Hbase2;
        subst; simpl in *.
      match goal with H1 : (heap_array l2 ws2 ∪ _) !! _ = Some (Some _) |- _ =>
        rewrite heap_array_lookup_same_σ in H1;
          [|intros j Hj_lt Heq; apply (Hdisj i j Hi_lt Hj_lt); exact Heq];
        apply (Hl1 i Hi_lt), elem_of_dom;
        by rewrite H1
      end.
    + rewrite heap_array_lookup_same_σ in H;
        [|intros i Hi_lt Heq; by apply Hnotin; exists i].
      do 4 eexists. by eapply StoreS.
  (* 18. XchgS *)
  - subst σ0; simpl in *.
    destruct (decide (∃ i : nat, i < length ws1 ∧ l = l1 +ₗ i))
      as [(i & Hi_lt & ->)|Hnotin].
    + exfalso.
      destruct Hred2 as (? & ? & ? & ? & Hbase2).
      inversion Hbase2;
        subst; simpl in *.
      match goal with H1 : (heap_array l2 ws2 ∪ _) !! _ = Some (Some _) |- _ =>
        rewrite heap_array_lookup_same_σ in H1;
          [|intros j Hj_lt Heq; apply (Hdisj i j Hi_lt Hj_lt); exact Heq];
        apply (Hl1 i Hi_lt), elem_of_dom;
        by rewrite H1
      end.
    + rewrite heap_array_lookup_same_σ in H;
        [|intros i Hi_lt Heq; by apply Hnotin; exists i].
      do 4 eexists. by eapply XchgS.
  (* 19. CmpXchgS *)
  - subst σ0; simpl in *.
    destruct (decide (∃ i : nat, i < length ws1 ∧ l = l1 +ₗ i))
      as [(i & Hi_lt & ->)|Hnotin].
    + exfalso.
      destruct Hred2 as (? & ? & ? & ? & Hbase2).
      inversion Hbase2;
        subst; simpl in *.
      match goal with H1 : (heap_array l2 ws2 ∪ _) !! _ = Some (Some _) |- _ =>
        rewrite heap_array_lookup_same_σ in H1;
          [|intros j Hj_lt Heq; apply (Hdisj i j Hi_lt Hj_lt); exact Heq];
        apply (Hl1 i Hi_lt), elem_of_dom;
        by rewrite H1
      end.
    + rewrite heap_array_lookup_same_σ in H;
        [|intros i Hi_lt Heq; by apply Hnotin; exists i].
      do 4 eexists. eapply CmpXchgS; [eassumption|assumption|reflexivity].
  (* 20. FaaS *)
  - subst σ0; simpl in *.
    destruct (decide (∃ i : nat, i < length ws1 ∧ l = l1 +ₗ i))
      as [(i & Hi_lt & ->)|Hnotin].
    + exfalso.
      destruct Hred2 as (? & ? & ? & ? & Hbase2).
      inversion Hbase2;
        subst; simpl in *.
      match goal with H1 : (heap_array l2 ws2 ∪ _) !! _ = Some (Some _) |- _ =>
        rewrite heap_array_lookup_same_σ in H1;
          [|intros j Hj_lt Heq; apply (Hdisj i j Hi_lt Hj_lt); exact Heq];
        apply (Hl1 i Hi_lt), elem_of_dom;
        by rewrite H1
      end.
    + rewrite heap_array_lookup_same_σ in H;
        [|intros i Hi_lt Heq; by apply Hnotin; exists i].
      do 4 eexists. by eapply FaaS.
Qed.


(** Generalized form: the extension values [ws] may be *chosen per
  location*. At each fresh starting location [l], the caller picks
  some [ws] of length [n] and shows [e] is not stuck in the extended
  state. This is essential when the witness [ws] depends on [l]
  (e.g. when the extension encodes state that was produced by a
  proof that started at [l]). *)
Lemma not_stuck_heap_restrict (e : expr) (σ : state) (n : nat) :
  (∀ (l : loc),
     (∀ i : nat, i < n → l +ₗ i ∉ dom σ.(heap)) →
     ∃ (ws : list val), length ws = n ∧ not_stuck e (σ_ext l ws σ)) →
  not_stuck e σ.
Proof.
  intros Hall.
  destruct (to_val e) as [vl|] eqn:Hval.
  { left. by eexists. }
  right.
  set (l1 := Loc.fresh (dom σ.(heap))).
  set (l2 := l1 +ₗ (Z.of_nat n)).
  assert (Hl1_fresh_n: ∀ i : nat, i < n → l1 +ₗ i ∉ dom σ.(heap)).
  { intros i Hi. apply Loc.fresh_fresh. lia. }
  assert (Hl2_fresh_n: ∀ i : nat, i < n → l2 +ₗ i ∉ dom σ.(heap)).
  { intros i Hi. rewrite /l2 Loc.add_assoc.
    apply Loc.fresh_fresh. lia. }
  assert (Hdisj_n: ∀ i j : nat, i < n → j < n → l1 +ₗ i ≠ l2 +ₗ j).
  { intros i j Hi Hj. rewrite /l2 Loc.add_assoc.
    intros Heq. destruct l1 as [k]. rewrite /Loc.add in Heq. injection Heq. lia. }
  pose proof (Hall l1 Hl1_fresh_n) as (ws1 & Hn1 & Hns1).
  pose proof (Hall l2 Hl2_fresh_n) as (ws2 & Hn2 & Hns2).
  assert (Hl1_fresh: ∀ i : nat, i < length ws1 → l1 +ₗ i ∉ dom σ.(heap))
    by (rewrite Hn1; exact Hl1_fresh_n).
  assert (Hl2_fresh: ∀ i : nat, i < length ws2 → l2 +ₗ i ∉ dom σ.(heap))
    by (rewrite Hn2; exact Hl2_fresh_n).
  assert (Hdisj: ∀ i j : nat, i < length ws1 → j < length ws2 → l1 +ₗ i ≠ l2 +ₗ j).
  { rewrite Hn1 Hn2. exact Hdisj_n. }
  destruct Hns1 as [[vl1 Hvl1]|Hr1]; first by rewrite Hvl1 in Hval.
  destruct Hns2 as [[vl2 Hvl2]|Hr2]; first by rewrite Hvl2 in Hval.
  destruct Hr1 as (κ1 & e'1 & σ'1 & efs1 & Hprim1).
  destruct Hprim1 as [K1 e_r1 e'_r1 -> -> Hbase1]; simpl in *.
  destruct Hr2 as (κ2 & e'2 & σ'2 & efs2 & Hprim2).
  destruct Hprim2 as [K2 e_r2 e'_r2 He_K2 -> Hbase2]; simpl in *.
  pose proof (heap_op_align σ l1 l2 ws1 ws2 e_r1 K1 K2 _ _ _ _ _ _ _ _ _
                Hl1_fresh Hl2_fresh Hdisj Hbase1 Hbase2 He_K2) as ->.
  pose proof (base_step_reducible_in_σ e_r1 σ l1 l2 ws1 ws2 _ _ _ _
                Hl1_fresh Hl2_fresh Hdisj Hbase1
                ltac:(by do 4 eexists))
    as (κ_new & e_new & σ_new & efs_new & Hbase_new).
  do 4 eexists.
  apply (fill_prim_step K1), base_prim_step.
  exact Hbase_new.
Qed.
