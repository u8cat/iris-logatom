(* insert_pr_relaxed_queue_revised.v *)
From stdpp Require Import finite.
From iris_logatom.lib Require Import list.
From iris_logatom.pure_logic.aspect.queue.ext Require Import conc_his_rel insert_relaxed_queue strict_partial_order_extension.

Local Instance relation_union {A} : Union (relation A) :=
  λ r1 r2, Relation_Operators.union A r1 r2.

Section insert_pr_relaxed_queue_revised.
  Context `{abstract_queue_model}.
  Implicit Types (pre val : relation operation).

  (* ======================================================================== *)
  (* QUEUE AXIOMATIZATION                                                     *)
  (* ======================================================================== *)
  
  (* We include ConcHistory pre to get the Abcd property, which models 
     overlapping intervals (real-time execution). *)
  Class InsertPrRelaxedQueue pre val := {
    #[local] ipr_queue_wellformed :: WellformedHistory pre val;
    #[local] ipr_queue_conc_history :: ConcHistory pre;
    no_voord e1 e2 d1 d2 : pre e1 e2 → val e1 d1 → val e2 d2 → ¬ pre d2 d1
  }.

  Context pre val `{!InsertPrRelaxedQueue pre val}.

  #[local] Existing Instance ipr_queue_wellformed.
  #[local] Existing Instance empty_pre_conchistory.
  #[local] Existing Instance pre_transitive.
  #[local] Existing Instance pre_irreflexive.

  (* ======================================================================== *)
  (* STRUCTURAL RELATIONS (OVERLAPPING CYCLE DETECTION)                       *)
  (* ======================================================================== *)

  (* R_link connects two DISTINCT dequeues if their enqueues are identical or ordered. *)
  Definition R_link (d1 d2 : operation) : Prop :=
    d1 ≠ d2 ∧ exists e1 e2, val e1 d1 /\ val e2 d2 /\ (e1 = e2 \/ pre e1 e2).

  (* THE LYNCHPIN LEMMA: Abcd destroys the phantom cycles.
     If a dequeue strictly precedes another, and is linked to a third, 
     which strictly precedes a fourth, the first must strictly precede the fourth. *)
  Lemma linked_pre_collapse d1 d2 d3 d4 :
    pre d1 d2 -> R_link d2 d3 -> pre d3 d4 -> pre d1 d4.
  Proof.
    intros H12 (Hneq & e2 & e3 & Hv2 & Hv3 & Hlink) H34.
    destruct (pre_abcd _ _ _ _ H12 H34) as [H14 | H32].
    - exact H14.
    - exfalso. destruct Hlink as [Heq | Hpre].
      + subst e3. assert (d2 = d3) as Heq by (eapply def_dequeue_once; eauto).
        contradiction.
      + apply (no_voord _ _ _ _ Hpre Hv2 Hv3). exact H32.
  Qed.

  (* R_step groups a sequence of enqueue orders and a single dequeue order *)
  Definition R_step (d1 d3 : operation) : Prop :=
    exists d2, R_link d1 d2 /\ pre d2 d3.

  (* Any path in R_step that loops back on itself implies a contradiction. 
     This proves that the overlapping execution bounds are respected. *)
  Lemma tc_R_step_impossible a b u du da db :
    tc R_step a b -> val u du -> val a da -> val b db ->
    pre du da -> R_link b u -> False.
  Proof.
    intros Htc. revert u du da db.
    induction Htc as [x y Hxy | x y z Hxy Hyz IH]; intros u du dx dy Hvu Hvx Hvy Hpre Hlink.
    - (* Base case: R_step x y *)
      destruct Hxy as (m & Hlink_xm & Hpre_my).
      destruct Hlink_xm as (Hneq_xm & ex & em & Hvex & Hvem & Hlink_pre).
      (* R_link x m gives val ex x, meaning x is a dequeue.
         But Hvx : val x dx means x is an enqueue.
         By val_order, x cannot be both, so derive contradiction. *)
      exfalso.
      eapply def_val_order; first exact Hvx.
      exists ex. left. exact Hvex.
    - (* Inductive case: R_step x y, then tc R_step y z *)
      destruct Hxy as (m & Hlink_xm & Hpre_my).
      destruct Hlink_xm as (Hneq_xm & ex & em & Hvex & Hvem & Hlink_pre).
      (* Same reasoning: val ex x (x is dequeue) contradicts Hvx : val x dx (x is enqueue) *)
      exfalso.
      eapply def_val_order; first exact Hvx.
      exists ex. left. exact Hvex.
  Qed.

  (* ======================================================================== *)
  (* CONSTRUCTING THE ACYCLIC BASE RELATION                                   *)
  (* ======================================================================== *)

  Definition R_deq (d1 d2 : operation) :=
    pre d1 d2 \/ R_link d1 d2.

  (* Helper 1: R_link inherently requires a strict pre ordering on enqueues.
     The equality case in your R_link definition is actually impossible! *)
  Lemma R_link_to_pre_enq d1 d2 e1 e2 :
    R_link d1 d2 -> val e1 d1 -> val e2 d2 -> pre e1 e2.
  Proof.
    intros (Hneq & ex & ey & Hvx & Hvy & [Heq | Hpre]) Hv1 Hv2.
    - assert (ex = e1) by (eapply def_enqueue_once; eauto).
      assert (ey = e2) by (eapply def_enqueue_once; eauto).
      subst. 
      assert (d1 = d2) by (eapply def_dequeue_once; eauto). 
      contradiction.
    - assert (ex = e1) by (eapply def_enqueue_once; eauto).
      assert (ey = e2) by (eapply def_enqueue_once; eauto).
      subst. exact Hpre.
  Qed.

  (* Helper 2: Because pre is transitive, R_link is also transitive. *)
  Lemma R_link_trans d1 d2 d3 :
    R_link d1 d2 -> R_link d2 d3 -> R_link d1 d3.
  Proof.
    intros H12 H23.
    destruct H12 as (Hneq12 & e1 & e2 & Hv1 & Hv2 & Hord12).
    destruct H23 as (Hneq23 & e2' & e3 & Hv2' & Hv3 & Hord23).
    assert (e2 = e2') as Heq22 by (eapply def_enqueue_once; eauto). subst e2'.
    (* Both R_link edges must use the pre case (equality case implies d1=d2 or d2=d3) *)
    assert (Hpre12 : pre e1 e2).
    { destruct Hord12 as [Heq | Hpre]; [|exact Hpre].
      subst e2. pose proof (def_dequeue_once _ _ _ Hv1 Hv2) as Heq. contradiction. }
    assert (Hpre23 : pre e2 e3).
    { destruct Hord23 as [Heq | Hpre]; [|exact Hpre].
      subst e3. pose proof (def_dequeue_once _ _ _ Hv2' Hv3) as Heq. contradiction. }
    assert (Hpre13 : pre e1 e3) by (etrans; eauto).
    split.
    - intros Heq. subst d3.
      assert (e1 = e3) by (eapply def_enqueue_once; eauto). subst e3.
      eapply pre_irreflexive; eauto.
    - exists e1, e3. split; [exact Hv1|]. split; [exact Hv3|]. right. exact Hpre13.
  Qed.

  (* Helper 3: The symmetric collapse lemma for R_link ; pre ; R_link *)
  Lemma R_link_pre_R_link_collapse d1 d2 d3 d4 :
    R_link d1 d2 -> pre d2 d3 -> R_link d3 d4 -> R_link d1 d4.
  Proof.
    intros L12 P23 L34.
    destruct L12 as (N12 & e1 & e2 & Hv1 & Hv2 & Hord12).
    destruct L34 as (N34 & e3 & e4 & Hv3 & Hv4 & Hord34).
    assert (P12 : pre e1 e2).
    { destruct Hord12 as [Heq | Hpre]; [|exact Hpre].
      subst e2. pose proof (def_dequeue_once _ _ _ Hv1 Hv2) as Heq. contradiction. }
    assert (P34 : pre e3 e4).
    { destruct Hord34 as [Heq | Hpre]; [|exact Hpre].
      subst e4. pose proof (def_dequeue_once _ _ _ Hv3 Hv4) as Heq. contradiction. }
    destruct (pre_abcd _ _ _ _ P12 P34) as [P14 | P32].
    - split.
      + intros Heq. subst d4.
        assert (e1 = e4) by (eapply def_enqueue_once; eauto). subst e4.
        eapply pre_irreflexive; eauto.
      + exists e1, e4. split; [exact Hv1|]. split; [exact Hv4|]. right. exact P14.
    - exfalso. apply (no_voord _ _ _ _ P32 Hv3 Hv2). exact P23.
  Qed.

  (* R_comp defines the four possible normal forms of any path in R_deq *)
  Definition R_comp d1 d2 :=
    pre d1 d2 \/
    R_link d1 d2 \/
    (exists d, pre d1 d /\ R_link d d2) \/
    (exists d, R_link d1 d /\ pre d d2).

  Lemma R_deq_to_R_comp d1 d2 : R_deq d1 d2 -> R_comp d1 d2.
  Proof.
    intros [Hpre|Hlink].
    - left. exact Hpre.
    - right; left. exact Hlink.
  Qed.

  (* Any transitive closure path maps directly into the finite R_comp forms *)
  Lemma tc_R_deq_to_R_comp a b : tc R_deq a b -> R_comp a b.
  Proof.
    intros Htc. induction Htc as [x y Hxy | x y z Hxy Hyz IH].
    - apply R_deq_to_R_comp. exact Hxy.
    - (* Hxy : R_deq x y, IH : R_comp y z. Goal: R_comp x z *)
      destruct Hxy as [P1 | L1]; destruct IH as [P2 | [L2 | [(d & Pd & Ld) | (d & Ld & Pd)]]].
      + (* pre x y ; pre y z => pre x z *)
        left. eapply transitivity; eauto.
      + (* pre x y ; R_link y z => pre x y ; R_link y z *)
        right; right; left. exists y. split; [exact P1|exact L2].
      + (* pre x y ; (pre y d ; R_link d z) => pre x d ; R_link d z *)
        right; right; left. exists d. split; [eapply transitivity; eauto | exact Ld].
      + (* pre x y ; (R_link y d ; pre d z) => pre x z via linked_pre_collapse *)
        left. eapply linked_pre_collapse; eauto.
      + (* R_link x y ; pre y z => R_link x y ; pre y z *)
        right; right; right. exists y. split; [exact L1|exact P2].
      + (* R_link x y ; R_link y z => R_link x z *)
        right; left. eapply R_link_trans; eauto.
      + (* R_link x y ; (pre y d ; R_link d z) => R_link x z via R_link_pre_R_link_collapse *)
        right; left. eapply R_link_pre_R_link_collapse; eauto.
      + (* R_link x y ; (R_link y d ; pre d z) => R_link x d ; pre d z *)
        right; right; right. exists d. split; [eapply R_link_trans; eauto | exact Pd].
  Qed.

  (* A cycle is impossible in all four normal forms *)
  Lemma R_comp_irreflexive a : R_comp a a -> False.
  Proof.
    intros [P | [L | [(d & P & L) | (d & L & P)]]].
    - eapply pre_irreflexive; eauto.
    - destruct L as (Hneq & _). contradiction.
    - (* pre a d ; R_link d a with d = a *)
      destruct L as (Hneq & e1 & e2 & Hv1 & Hv2 & Hord).
      destruct Hord as [Heq | Hpre].
      + subst e2. pose proof (def_dequeue_once _ _ _ Hv1 Hv2) as Heq. contradiction.
      + apply (no_voord _ _ _ _ Hpre Hv1 Hv2). exact P.
    - (* R_link a d ; pre d a *)
      destruct L as (Hneq & e1 & e2 & Hv1 & Hv2 & Hord).
      destruct Hord as [Heq | Hpre].
      + subst e2. pose proof (def_dequeue_once _ _ _ Hv1 Hv2) as Heq. contradiction.
      + apply (no_voord _ _ _ _ Hpre Hv1 Hv2). exact P.
  Qed.

  (* The final irreflexivity lemma becomes trivial *)
  Lemma tc_R_deq_irreflexive : Irreflexive (tc R_deq).
  Proof.
    intros x Htc.
    apply tc_R_deq_to_R_comp in Htc.
    eapply R_comp_irreflexive; eauto.
  Qed.

  Local Instance R_deq_transitive : Transitive (tc R_deq).
  Proof. intros a b c. apply tc_transitive. Qed.

  (* ======================================================================== *)
  (* EXTENDED DEQUEUE ORDERING (ADDS VAL-CROSSING EDGES)                      *)
  (* ======================================================================== *)

  (* R_val_cross captures: if dequeue d1 precedes enqueue e, then d1 should
     come before e's dequeue d2 in the linearized dequeue order. *)
  Definition R_val_cross (d1 d2 : operation) : Prop :=
    d1 ≠ d2 ∧ ∃ e, val e d2 ∧ pre d1 e.

  Definition R_deq_ext (d1 d2 : operation) :=
    R_deq d1 d2 ∨ R_val_cross d1 d2.

  (* Helper: R_val_cross followed by pre gives pre (via abcd) *)
  Lemma R_val_cross_pre a b c :
    R_val_cross a b → pre b c → pre a c.
  Proof.
    intros (_ & e_b & Hval_b & Hpre_a_eb) Hpre_bc.
    destruct (pre_abcd _ _ _ _ Hpre_a_eb Hpre_bc) as [Hac | Hbe].
    - exact Hac.
    - exfalso. exact (def_val_then_not_pr _ _ Hval_b Hbe).
  Qed.

  (* Helper: R_val_cross followed by R_link gives R_val_cross *)
  Lemma R_val_cross_R_link a b c :
    R_val_cross a b → R_link b c → R_val_cross a c.
  Proof.
    intros (Hneq_ab & e_b & Hval_b & Hpre_a_eb) (Hneq_bc & e_b' & e_c & Hval_b' & Hval_c & Hord).
    assert (e_b = e_b') as Heq by (eapply def_enqueue_once; eauto). subst e_b'.
    destruct Hord as [Heq | Hpre_eb_ec].
    - subst e_c. pose proof (def_dequeue_once _ _ _ Hval_b Hval_c). contradiction.
    - split.
      + intros Heq. subst c.
        eapply def_val_then_not_pr; first exact Hval_c.
        eapply transitivity; eauto.
      + exists e_c. split; [exact Hval_c|]. eapply transitivity; eauto.
  Qed.

  (* Helper: R_val_cross followed by R_val_cross gives R_val_cross (via abcd) *)
  Lemma R_val_cross_R_val_cross a b c :
    R_val_cross a b → R_val_cross b c → R_val_cross a c.
  Proof.
    intros (_ & e_b & Hval_b & Hpre_a_eb) (_ & e_c & Hval_c & Hpre_b_ec).
    destruct (pre_abcd _ _ _ _ Hpre_a_eb Hpre_b_ec) as [Hac | Hbe].
    - split.
      + intros Heq. subst c. exact (def_val_then_not_pr _ _ Hval_c Hac).
      + exists e_c. split; [exact Hval_c|exact Hac].
    - exfalso. exact (def_val_then_not_pr _ _ Hval_b Hbe).
  Qed.

  (* Helper: R_link followed by R_val_cross gives R_link (via abcd) *)
  Lemma R_link_R_val_cross a b c :
    R_link a b → R_val_cross b c → R_link a c.
  Proof.
    intros (Hneq_ab & e_a & e_b & Hval_a & Hval_b & Hord_ab) (_ & e_c & Hval_c & Hpre_b_ec).
    assert (Hpre_ea_eb : pre e_a e_b).
    { destruct Hord_ab as [Heq | Hpre]; [|exact Hpre].
      subst e_b. pose proof (def_dequeue_once _ _ _ Hval_a Hval_b). contradiction. }
    destruct (pre_abcd _ _ _ _ Hpre_ea_eb Hpre_b_ec) as [Haec | Hbe].
    - split.
      + intros Heq. subst c. assert (e_a = e_c) by (eapply def_enqueue_once; eauto). subst.
        eapply pre_irreflexive; eauto.
      + exists e_a, e_c. split; [exact Hval_a|]. split; [exact Hval_c|]. right. exact Haec.
    - exfalso. exact (def_val_then_not_pr _ _ Hval_b Hbe).
  Qed.

  (* Helper: pre followed by R_val_cross gives R_val_cross *)
  Lemma pre_R_val_cross a b c :
    pre a b → R_val_cross b c → R_val_cross a c.
  Proof.
    intros Hpre_ab (_ & e_c & Hval_c & Hpre_b_ec).
    split.
    - intros Heq. subst c. eapply def_val_then_not_pr; first exact Hval_c.
      eapply transitivity; eauto.
    - exists e_c. split; [exact Hval_c|]. eapply transitivity; eauto.
  Qed.

  (* Normal forms for paths in tc R_deq_ext *)
  Definition R_comp_ext d1 d2 :=
    pre d1 d2 ∨
    R_link d1 d2 ∨
    (exists d, pre d1 d /\ R_link d d2) ∨
    (exists d, R_link d1 d /\ pre d d2) ∨
    R_val_cross d1 d2.

  Lemma R_deq_ext_to_R_comp_ext d1 d2 : R_deq_ext d1 d2 → R_comp_ext d1 d2.
  Proof.
    intros [Hdeq | Hval].
    - apply R_deq_to_R_comp in Hdeq.
      destruct Hdeq as [H1 | [H2 | [H3 | H4]]]; [left;exact H1|right;left;exact H2|right;right;left;exact H3|right;right;right;left;exact H4].
    - right; right; right; right. exact Hval.
  Qed.

  Lemma tc_R_deq_ext_to_R_comp_ext a b : tc R_deq_ext a b → R_comp_ext a b.
  Proof.
    intros Htc. induction Htc as [x y Hxy | x y z Hxy Hyz IH].
    - apply R_deq_ext_to_R_comp_ext. exact Hxy.
    - destruct Hxy as [[P1 | L1] | V1];
      destruct IH as [P2 | [L2 | [(d & Pd & Ld) | [(d & Ld & Pd) | V2]]]].
      (* pre ; pre *)
      + left. eapply transitivity; eauto.
      (* pre ; R_link *)
      + right; right; left. exists y. split; [exact P1|exact L2].
      (* pre ; pre;R_link *)
      + right; right; left. exists d. split; [eapply transitivity; eauto|exact Ld].
      (* pre ; R_link;pre *)
      + left. eapply linked_pre_collapse; eauto.
      (* pre ; R_val_cross *)
      + right; right; right; right. eapply pre_R_val_cross; eauto.
      (* R_link ; pre *)
      + right; right; right; left. exists y. split; [exact L1|exact P2].
      (* R_link ; R_link *)
      + right; left. eapply R_link_trans; eauto.
      (* R_link ; pre;R_link *)
      + right; left. eapply R_link_pre_R_link_collapse; eauto.
      (* R_link ; R_link;pre *)
      + right; right; right; left. exists d. split; [eapply R_link_trans; eauto|exact Pd].
      (* R_link ; R_val_cross *)
      + right; left. eapply R_link_R_val_cross; eauto.
      (* R_val_cross ; pre *)
      + left. eapply R_val_cross_pre; eauto.
      (* R_val_cross ; R_link *)
      + right; right; right; right. eapply R_val_cross_R_link; eauto.
      (* R_val_cross ; pre;R_link *)
      + right; right; left. exists d. split; [eapply R_val_cross_pre; eauto|exact Ld].
      (* R_val_cross ; R_link;pre *)
      + left. eapply R_val_cross_pre. eapply R_val_cross_R_link; eauto. exact Pd.
      (* R_val_cross ; R_val_cross *)
      + right; right; right; right. eapply R_val_cross_R_val_cross; eauto.
  Qed.

  Lemma R_comp_ext_irreflexive a : R_comp_ext a a → False.
  Proof.
    intros [P | [L | [(d & P & L) | [(d & L & P) | V]]]].
    - eapply pre_irreflexive; eauto.
    - destruct L as (Hneq & _). contradiction.
    - eapply R_comp_irreflexive. right; right; left. exists d. exact (conj P L).
    - eapply R_comp_irreflexive. right; right; right. exists d. exact (conj L P).
    - destruct V as (Hneq & _). contradiction.
  Qed.

  Lemma tc_R_deq_ext_irreflexive : Irreflexive (tc R_deq_ext).
  Proof.
    intros x Htc.
    apply tc_R_deq_ext_to_R_comp_ext in Htc.
    eapply R_comp_ext_irreflexive; eauto.
  Qed.

  Local Instance R_deq_ext_transitive : Transitive (tc R_deq_ext).
  Proof. intros a b c. apply tc_transitive. Qed.

  (* ======================================================================== *)
  (* ACYCLICITY OF R_all VIA GRAPH CONTRACTION                                *)
  (* ======================================================================== *)

  Definition is_valid_op (x : operation) :=
    is_enqueue val x \/ is_dequeue val x.

  Definition prt_deq_eq {A} prt_deq (d1 d2 : A) := prt_deq d1 d2 \/ d1 = d2.

  (* Bounds a sequence of edges crossing from Enqueue to Dequeue *)
  Definition cross_ED prt_deq da b :=
    prt_deq_eq prt_deq da b \/
    (exists e_m d_m d_em, is_enqueue val e_m /\ is_dequeue val d_m /\ val e_m d_em /\
      prt_deq_eq prt_deq da d_em /\ pre e_m d_m /\ prt_deq_eq prt_deq d_m b).

  (* Bounds a sequence of edges crossing from Dequeue to Enqueue *)
  Definition cross_DE prt_deq a db :=
    exists d_m e_m d_em, is_dequeue val d_m /\ is_enqueue val e_m /\ val e_m d_em /\
      prt_deq_eq prt_deq a d_m /\ pre d_m e_m /\ prt_deq_eq prt_deq d_em db.

  (* The unified invariant that classifies all paths in tc R_all *)
  (* NOTICE: The \/ disjunctions are gone for the cross edges! *)
  Definition R_collapsed prt_deq (a b : operation) : Prop :=
    (forall da db, is_enqueue val a -> is_enqueue val b -> val a da -> val b db -> prt_deq da db) /\
    (is_dequeue val a -> is_dequeue val b -> prt_deq a b) /\
    (forall db, is_dequeue val a -> is_enqueue val b -> val b db -> cross_DE prt_deq a db) /\
    (forall da, is_enqueue val a -> is_dequeue val b -> val a da -> cross_ED prt_deq da b).

  Lemma prt_deq_eq_trans_l {A} (prt_deq : relation A) :
    Transitive prt_deq -> forall a b c, prt_deq_eq prt_deq a b -> prt_deq b c -> prt_deq a c.
  Proof. intros Htrans a b c [Hab | Hab] Hbc; [eapply Htrans; eauto | subst; exact Hbc]. Qed.

  Lemma prt_deq_eq_trans_r {A} (prt_deq : relation A) :
    Transitive prt_deq -> forall a b c, prt_deq a b -> prt_deq_eq prt_deq b c -> prt_deq a c.
  Proof. intros Htrans a b c Hab [Hbc | Hbc]; [eapply Htrans; eauto | subst; exact Hab]. Qed.

  Lemma prt_deq_eq_trans {A} (prt_deq : relation A) :
    Transitive prt_deq -> forall a b c, prt_deq_eq prt_deq a b -> prt_deq_eq prt_deq b c -> prt_deq_eq prt_deq a c.
  Proof.
    intros Htrans a b c [Hab | Hab] [Hbc | Hbc].
    - left. eapply Htrans; eauto.
    - subst. left. exact Hab.
    - subst. left. exact Hbc.
    - subst. right. reflexivity.
  Qed.

  Lemma tc_R_all_collapse prt_deq a b :
    Irreflexive prt_deq -> Transitive prt_deq ->
    (forall x y, is_dequeue val x -> is_dequeue val y -> x <> y -> prt_deq x y \/ prt_deq y x) ->
    (forall d1 d2 e1 e2, val e1 d1 -> val e2 d2 -> pre e1 e2 -> prt_deq d1 d2) ->
    (forall d1 d2, is_dequeue val d1 -> is_dequeue val d2 -> pre d1 d2 -> prt_deq d1 d2) ->
    (forall d d' e, is_dequeue val d -> val e d' -> pre d e -> prt_deq d d') ->
    tc (fun a b =>
      pre a b \/
      (is_enqueue val a /\ is_enqueue val b /\ exists da db, val a da /\ val b db /\ prt_deq da db) \/
      (is_dequeue val a /\ is_dequeue val b /\ prt_deq a b) \/
      val a b
    ) a b -> R_collapsed prt_deq a b.
  Proof.
    intros Hirr Htrans Htot Hpre_enq Hpre_deq Hpre_deq_val Htc.
    induction Htc as [x y Hxy | x y z Hxy Hyz IH].
    - (* Base Case *)
      destruct Hxy as [Hpre | [[Hex [Hey [dx' [dy' [Hvx' [Hvy' Hprt]]]]]] | [[Hdx [Hdy Hprt]] | Hval_xy]]].
      + pose proof (def_enqueue_or_dequeue x y Hpre) as [[cx [Hvxcx | Hvcxx]] [cy [Hvycy | Hvcyy]]].
        * (* x=E, y=E *)
          split; [|split; [|split]].
          -- intros da db _ _ Hva Hvb.
             assert (da = cx) by (eapply def_dequeue_once; eauto). subst cx.
             assert (db = cy) by (eapply def_dequeue_once; eauto). subst cy.
             eapply Hpre_enq; eauto.
          -- intros Hdx' _. destruct Hdx' as [e He]. exfalso. eapply def_val_order; [exact He|]. exists cx; right; auto.
          -- intros db Hdx' _ _. destruct Hdx' as [e He]. exfalso. eapply def_val_order; [exact He|]. exists cx; right; auto.
          -- intros da _ Hdy' _. destruct Hdy' as [e He]. exfalso. eapply def_val_order; [exact He|]. exists cy; right; auto.
        * (* x=E, y=D *)
          split; [|split; [|split]].
          -- intros da db _ Hey' _ _. destruct Hey' as [d Hd]. exfalso. eapply def_val_order; [exact Hvcyy|]. exists d; right; auto.
          -- intros Hdx' _. destruct Hdx' as [e He]. exfalso. eapply def_val_order; [exact He|]. exists cx; right; auto.
          -- intros db Hdx' Hey' _. destruct Hdx' as [e He]. exfalso. eapply def_val_order; [exact He|]. exists cx; right; auto.
          -- intros da Hex' Hdy' Hva.
             assert (da = cx) by (eapply def_dequeue_once; eauto). subst cx.
             unfold cross_ED. right.
             exists x, y, da. repeat split; auto.
             ++ right; reflexivity.
             ++ right; reflexivity.
        * (* x=D, y=E *)
          split; [|split; [|split]].
          -- intros da db Hex' _ _ _. destruct Hex' as [d Hd]. exfalso. eapply def_val_order; [exact Hvcxx|]. exists d; right; auto.
          -- intros _ Hey'. destruct Hey' as [d Hd]. exfalso. eapply def_val_order; [exact Hd|]. exists cy; right; auto.
          -- intros db Hdx' Hey' Hvb.
             assert (db = cy) by (eapply def_dequeue_once; eauto). subst cy.
             unfold cross_DE.
             exists x, y, db. repeat split; auto.
             ++ right; reflexivity.
             ++ right; reflexivity.
          -- intros da Hex' _ _. destruct Hex' as [d Hd]. exfalso. eapply def_val_order; [exact Hvcxx|]. exists d; right; auto.
        * (* x=D, y=D *)
          split; [|split; [|split]].
          -- intros da db Hex' _ _ _. destruct Hex' as [d Hd]. exfalso. eapply def_val_order; [exact Hvcxx|]. exists d; right; auto.
          -- intros _ _. eapply Hpre_deq; [exists cx | exists cy |]; auto.
          -- intros db _ Hey' _. destruct Hey' as [d Hd]. exfalso. eapply def_val_order; [exact Hvcyy|]. exists d; right; auto.
          -- intros da Hex' _ _. destruct Hex' as [d Hd]. exfalso. eapply def_val_order; [exact Hvcxx|]. exists d; right; auto.
      + (* x=E, y=E (explicit) *)
        split; [|split; [|split]].
        * intros da db _ _ Hva Hvb.
          assert (da = dx') by (eapply def_dequeue_once; eauto). subst da.
          assert (db = dy') by (eapply def_dequeue_once; eauto). subst db.
          exact Hprt.
        * intros Hdx' _. destruct Hdx' as [e He]. exfalso. eapply def_val_order; [exact He|]. exists dx'; right; auto.
        * intros db Hdx' _ _. destruct Hdx' as [e He]. exfalso. eapply def_val_order; [exact He|]. exists dx'; right; auto.
        * intros da _ Hdy' _. destruct Hdy' as [e He]. exfalso. eapply def_val_order; [exact He|]. exists dy'; right; auto.
      + (* x=D, y=D (explicit) *)
        split; [|split; [|split]].
        * intros da db Hex' _ _ _. destruct Hex' as [d Hd]. destruct Hdx as [ex Hvex]. exfalso. eapply def_val_order; [exact Hvex|]. exists d; right; auto.
        * intros _ _. exact Hprt.
        * intros db _ Hey' _. destruct Hey' as [d Hd]. destruct Hdy as [ey Hvey]. exfalso. eapply def_val_order; [exact Hvey|]. exists d; right; auto.
        * intros da Hex' _ _. destruct Hex' as [d Hd]. destruct Hdx as [ex Hvex]. exfalso. eapply def_val_order; [exact Hvex|]. exists d; right; auto.
      + (* val x y (x=E, y=D) *)
        split; [|split; [|split]].
        * intros da db _ Hey' _ _. destruct Hey' as [d Hd]. exfalso. eapply def_val_order; [exact Hval_xy|]. exists d; right; auto.
        * intros Hdx' _. destruct Hdx' as [e He]. exfalso. eapply def_val_order; [exact He|]. exists y; right; auto.
        * intros db Hdx' _ _. destruct Hdx' as [e He]. exfalso. eapply def_val_order; [exact He|]. exists y; right; auto.
        * intros da Hex' Hdy' Hva.
          assert (da = y) by (eapply def_dequeue_once; eauto). subst da.
          unfold cross_ED. left. right; reflexivity.

    - (* Inductive Case: Compose R_all x y with R_collapsed y z *)
      destruct IH as [IH_EE [IH_DD [IH_DE IH_ED]]].
      destruct Hxy as [Hpre_xy | [[Hex_xy [Hey_xy [dx_xy [dy_xy [Hvx_xy [Hvy_xy Hprt_xy]]]]]] | [[Hdx_xy [Hdy_xy Hprt_xy]] | Hval_xy]]].
      + pose proof (def_enqueue_or_dequeue x y Hpre_xy) as [[cx [Hvxcx | Hvcxx]] [cy [Hvycy | Hvcyy]]].
        * (* x=E, y=E *)
          split; [|split; [|split]].
          -- intros dx dz Hex Hez Hvx Hvz.
             assert (dx = cx) by (eapply def_dequeue_once; eauto). subst dx.
             assert (Hprt_cx_cy : prt_deq cx cy) by (eapply Hpre_enq; eauto).
             specialize (IH_EE cy dz (ex_intro _ cy Hvycy) Hez Hvycy Hvz).
             eapply Htrans; eauto.
          -- intros Hdx _. destruct Hdx as [ex Hvex]. exfalso. eapply def_val_order; [exact Hvxcx|]. exists ex; left; auto.
          -- intros dz Hdx _ _. destruct Hdx as [ex Hvex]. exfalso. eapply def_val_order; [exact Hvxcx|]. exists ex; left; auto.
          -- intros dx Hex Hdz Hvx.
             assert (dx = cx) by (eapply def_dequeue_once; eauto). subst dx.
             assert (Hprt_cx_cy : prt_deq cx cy) by (eapply Hpre_enq; eauto).
             specialize (IH_ED cy (ex_intro _ cy Hvycy) Hdz Hvycy).
             unfold cross_ED.
             destruct IH_ED as [Hprt_cy_z | [e_m [d_m [d_em [Hem_enq [Hdm_deq [Hval_em [Hprt1 [Hpre_em_dm Hprt2]]]]]]]]].
             ++ left. eapply prt_deq_eq_trans; eauto. left. exact Hprt_cx_cy.
             ++ right. exists e_m, d_m, d_em. repeat split; auto.
                eapply prt_deq_eq_trans; eauto. left. exact Hprt_cx_cy.
        * (* x=E, y=D *)
          split; [|split; [|split]].
          -- intros dx dz Hex Hez Hvx Hvz.
             assert (dx = cx) by (eapply def_dequeue_once; eauto). subst dx.
             specialize (IH_DE dz (ex_intro _ cy Hvcyy) Hez Hvz).
             destruct IH_DE as [d_m [e_m [d_em [Hdm_deq [Hem_enq [Hval_em [Hprt1 [Hpre_dm_em Hprt2]]]]]]]].
             destruct (pre_abcd _ _ _ _ Hpre_xy Hpre_dm_em) as [Hpre_x_em | Hpre_dm_y].
             ++ assert (Hprt_cx_dem : prt_deq cx d_em). 
                { eapply Hpre_enq; [exact Hvxcx | exact Hval_em | exact Hpre_x_em]. }
                eapply prt_deq_eq_trans_r; [exact Htrans | exact Hprt_cx_dem | exact Hprt2].
             ++ exfalso.
                destruct Hprt1 as [Hprt_y_dm | Heq_y_dm].
                ** apply (Hirr y). eapply Htrans; [exact Hprt_y_dm|].
                   eapply Hpre_deq.
                   { eauto. }
                   { eexists; eauto. }
                   { eauto. }
                ** subst d_m. eapply pre_irreflexive; eauto.
          -- intros Hdx _. destruct Hdx as [ex Hvex]. exfalso. eapply def_val_order; [exact Hvxcx|]. exists ex; left; auto.
          -- intros dz Hdx _ _. destruct Hdx as [ex Hvex]. exfalso. eapply def_val_order; [exact Hvxcx|]. exists ex; left; auto.
          -- intros dx Hex Hdz Hvx.
             assert (dx = cx) by (eapply def_dequeue_once; eauto). subst dx.
             specialize (IH_DD (ex_intro _ cy Hvcyy) Hdz).
             unfold cross_ED. right.
             exists x, y, cx. repeat split; auto; intuition.
             { eexists; eauto. }
             right; auto.
             left; auto.
        * (* x=D, y=E *)
          split; [|split; [|split]].
          -- intros dx dz Hex _ _ _. destruct Hex as [d Hd]. exfalso. eapply def_val_order; [exact Hvcxx|]. exists d; right; auto.
          -- intros Hdx Hdz.
             specialize (IH_ED cy (ex_intro _ cy Hvycy) Hdz Hvycy).
             destruct IH_ED as [Hprt_cy_z | [e_m [d_m [d_em [Hem_enq [Hdm_deq [Hval_em [Hprt1 [Hpre_em_dm Hprt2]]]]]]]]].
             ++ (* Left: prt_deq_eq cy z *)
                destruct Hprt_cy_z as [Hprt_cy_z | Heq_cy_z].
                ** assert (Hprt_x_cy : prt_deq x cy).
                   { eapply Hpre_deq_val; [exact Hdx | exact Hvycy | exact Hpre_xy]. }
                   eapply Htrans; eauto.
                ** subst z.
                   eapply Hpre_deq_val; [exact Hdx | exact Hvycy | exact Hpre_xy].
             ++ (* Right: existing with abcd *)
                destruct (pre_abcd _ _ _ _ Hpre_xy Hpre_em_dm) as [Hpre_x_dm | Hpre_em_y].
                ** assert (Hprt_x_dm : prt_deq x d_m).
                   { eapply Hpre_deq; [exact Hdx | exact Hdm_deq | exact Hpre_x_dm]. }
                   eapply prt_deq_eq_trans_r; [exact Htrans | exact Hprt_x_dm | exact Hprt2].
                ** assert (Hprt_dem_cy : prt_deq d_em cy).
                   { eapply Hpre_enq; [exact Hval_em | exact Hvycy | exact Hpre_em_y]. }
                   exfalso.
                   destruct Hprt1 as [Hprt_cy_dem | Heq_cy_dem].
                   --- apply (Hirr cy). eapply Htrans; eauto.
                   --- subst d_em. apply (Hirr cy). exact Hprt_dem_cy.
          -- intros dz Hdx Hez Hvz.
             specialize (IH_EE cy dz (ex_intro _ cy Hvycy) Hez Hvycy Hvz).
             unfold cross_DE.
             exists x, y, cy. repeat split; auto.
             { eexists; eauto. }
             right; auto.
             left; auto.
          -- intros dx Hex _ _. destruct Hex as [d Hd]. exfalso. eapply def_val_order; [exact Hvcxx|]. exists d; right; auto.
        * (* x=D, y=D *)
          split; [|split; [|split]].
          -- intros dx dz Hex _ _ _. destruct Hex as [d Hd]. exfalso. eapply def_val_order; [exact Hvcxx|]. exists d; right; auto.
          -- intros Hdx Hdz.
             specialize (IH_DD (ex_intro _ cy Hvcyy) Hdz).
             assert (Hprt_x_y : prt_deq x y).
             { eapply Hpre_deq; [exact Hdx | exists cy; exact Hvcyy | exact Hpre_xy]. }
             eapply Htrans; eauto.
          -- intros dz Hdx Hez Hvz.
             specialize (IH_DE dz (ex_intro _ cy Hvcyy) Hez Hvz).
             destruct IH_DE as [d_m [e_m [d_em [Hdm_deq [Hem_enq [Hval_em [Hprt1 [Hpre_dm_em Hprt2]]]]]]]].
             unfold cross_DE.
             exists d_m, e_m, d_em. repeat split; auto.
             eapply prt_deq_eq_trans; [exact Htrans | |exact Hprt1].
             left. eapply Hpre_deq; [exact Hdx | exists cy; exact Hvcyy | exact Hpre_xy].
          -- intros dx Hex _ _. destruct Hex as [d Hd]. exfalso. eapply def_val_order; [exact Hvcxx|]. exists d; right; auto.
      + (* Case: E->E explicit *)
        split; [|split; [|split]].
        * intros dx dz Hex Hez Hvx Hvz.
          assert (dx = dx_xy) by (eapply def_dequeue_once; eauto). subst dx.
          specialize (IH_EE dy_xy dz Hey_xy Hez Hvy_xy Hvz).
          eapply Htrans; eauto.
        * intros Hdx _. destruct Hdx as [ex Hvex]. exfalso. eapply def_val_order; [exact Hvx_xy|]. exists ex; left; auto.
        * intros dz Hdx _ _. destruct Hdx as [ex Hvex]. exfalso. eapply def_val_order; [exact Hvx_xy|]. exists ex; left; auto.
        * intros dx Hex Hdz Hvx.
          assert (dx = dx_xy) by (eapply def_dequeue_once; eauto). subst dx.
          specialize (IH_ED dy_xy Hey_xy Hdz Hvy_xy).
          unfold cross_ED.
          destruct IH_ED as [Hprt_dy_z | [e_m [d_m [d_em [Hem_enq [Hdm_deq [Hval_em [Hprt1 [Hpre_em_dm Hprt2]]]]]]]]].
          ++ left. eapply prt_deq_eq_trans; eauto. left. exact Hprt_xy.
          ++ right. exists e_m, d_m, d_em. repeat split; auto.
             eapply prt_deq_eq_trans; eauto. left. exact Hprt_xy.
      + (* Case: D->D explicit *)
        split; [|split; [|split]].
        * intros dx dz Hex _ _ _. destruct Hex as [d Hd]. destruct Hdx_xy as [ex Hvex]. exfalso. eapply def_val_order; [exact Hvex|]. exists d; right; auto.
        * intros Hdx Hdz.
          specialize (IH_DD Hdy_xy Hdz).
          eapply Htrans; eauto.
        * intros dz Hdx Hez Hvz.
          specialize (IH_DE dz Hdy_xy Hez Hvz).
          destruct IH_DE as [d_m [e_m [d_em [Hdm_deq [Hem_enq [Hval_em [Hprt1 [Hpre_dm_em Hprt2]]]]]]]].
          unfold cross_DE.
          exists d_m, e_m, d_em. repeat split; auto.
          eapply prt_deq_eq_trans; eauto. left. exact Hprt_xy.
        * intros dx Hex _ _. destruct Hex as [d Hd]. destruct Hdx_xy as [ex Hvex]. exfalso. eapply def_val_order; [exact Hvex|]. exists d; right; auto.
      + (* Case: val x y (x=E, y=D), compose with R_collapsed y z *)
        split; [|split; [|split]].
        * (* EE: x=E, z=E *)
          intros dx dz Hex Hez Hvx Hvz.
          assert (dx = y) by (eapply def_dequeue_once; eauto). subst dx.
          specialize (IH_DE dz (ex_intro _ x Hval_xy) Hez Hvz).
          destruct IH_DE as [d_m [e_m [d_em [Hdm_deq [Hem_enq [Hval_em [Hprt1 [Hpre_dm_em Hprt2]]]]]]]].
          assert (Hprt_dm_dem : prt_deq d_m d_em).
          { eapply Hpre_deq_val; eauto. }
          eapply prt_deq_eq_trans_l; [exact Htrans | exact Hprt1 |].
          eapply prt_deq_eq_trans_r; [exact Htrans | exact Hprt_dm_dem | exact Hprt2].
        * (* DD: x=D — vacuous *)
          intros Hdx _. destruct Hdx as [e He]. exfalso. eapply def_val_order; [exact He|]. exists y; right; auto.
        * (* DE: x=D — vacuous *)
          intros dz Hdx _ _. destruct Hdx as [e He]. exfalso. eapply def_val_order; [exact He|]. exists y; right; auto.
        * (* ED: x=E, z=D *)
          intros dx Hex Hdz Hvx.
          assert (dx = y) by (eapply def_dequeue_once; eauto). subst dx.
          specialize (IH_DD (ex_intro _ x Hval_xy) Hdz).
          unfold cross_ED. left. left. exact IH_DD.
  Qed.

  Lemma lem_tc_R_all_irreflexive prt_deq :
    Irreflexive prt_deq -> Transitive prt_deq ->
    (forall x y, is_dequeue val x -> is_dequeue val y -> x <> y -> prt_deq x y \/ prt_deq y x) ->
    (forall d1 d2 e1 e2, val e1 d1 -> val e2 d2 -> pre e1 e2 -> prt_deq d1 d2) ->
    (forall d1 d2, is_dequeue val d1 -> is_dequeue val d2 -> pre d1 d2 -> prt_deq d1 d2) ->
    (forall d d' e, is_dequeue val d -> val e d' -> pre d e -> prt_deq d d') ->
    Irreflexive (tc (fun a b =>
      pre a b \/
      (is_enqueue val a /\ is_enqueue val b /\ exists da db, val a da /\ val b db /\ prt_deq da db) \/
      (is_dequeue val a /\ is_dequeue val b /\ prt_deq a b) \/
      val a b)).
  Proof.
    intros Hirr Htrans Htot Hpre_enq Hpre_deq Hpre_deq_val x Hcycle.
    assert (Hvalid : is_enqueue val x \/ is_dequeue val x).
    { inversion Hcycle as [x' y' Hxy Heqx Heqy | x' y' z' Hxy Hyz Heqx Heqz].
      - subst x' y'.
        destruct Hxy as [Hpre | [[Hex [Hey Hrest]] | [[Hdx [Hdy Hprt]] | Hval_step]]].
        + destruct (def_enqueue_or_dequeue x x Hpre) as [[cx [Hcx | Hcx]] _].
          * left. exists cx. exact Hcx.
          * right. exists cx. exact Hcx.
        + left. exact Hex.
        + right. exact Hdx.
        + left. exists x. exact Hval_step.
      - subst x' z'.
        destruct Hxy as [Hpre | [[Hex [Hey Hrest]] | [[Hdx [Hdy Hprt]] | Hval_step]]].
        + destruct (def_enqueue_or_dequeue x y' Hpre) as [[cx [Hcx | Hcx]] _].
          * left. exists cx. exact Hcx.
          * right. exists cx. exact Hcx.
        + left. exact Hex.
        + right. exact Hdx.
        + left. exists y'. exact Hval_step. }

    apply tc_R_all_collapse in Hcycle; auto.
    destruct Hvalid as [[dx Hx] | Hdx].
    - destruct Hcycle as [Hee _].
      assert (Hprt : prt_deq dx dx).
      { apply Hee; try (exists dx; exact Hx); exact Hx. }
      eapply Hirr; eauto.
    - destruct Hcycle as [_ [Hdd _]].
      assert (Hprt : prt_deq x x) by (apply Hdd; auto).
      eapply Hirr; eauto.
  Qed.



  Theorem insert_pr_relaxed_queue_linearizable :
    ∃ prt, subrelation pre prt ∧ InsertRelaxedQueue prt val.
  Proof.
    (* 1. Topologically sort the DEQUEUES using the acyclic R_deq_ext constraints. *)
    assert (Hop_eq_dec : ∀ x y : operation, decidable (x = y)).
    { intros x y. destruct (decide (x = y)); [by left | by right]. }
    assert (HR_link_dec : ∀ x y, decidable (R_link x y)).
    { intros d1 d2. unfold R_link.
      apply dec_and; first by apply dec_not.
      apply dec_exists_op. intros e1. apply dec_exists_op. intros e2.
      apply dec_and; first by apply def_wf_val_decidable.
      apply dec_and; first by apply def_wf_val_decidable.
      apply dec_or; [apply Hop_eq_dec | by apply def_wf_pre_decidable]. }
    assert (HR_deq_dec : ∀ x y, decidable (R_deq x y)).
    { intros. unfold R_deq. apply dec_or; [by apply def_wf_pre_decidable | apply HR_link_dec]. }
    assert (HR_val_cross_dec : ∀ x y, decidable (R_val_cross x y)).
    { intros. unfold R_val_cross.
      apply dec_and; first by apply dec_not.
      apply dec_exists_op. intros e.
      apply dec_and; [by apply def_wf_val_decidable | by apply def_wf_pre_decidable]. }
    assert (HR_deq_ext_dec_base : ∀ x y, decidable (R_deq_ext x y)).
    { intros. unfold R_deq_ext. apply dec_or; auto. }
    assert (HR_deq_ext_dec : ∀ x y, decidable (tc R_deq_ext x y))
      by (intros; by apply tc_decidable).
    pose proof tc_R_deq_ext_irreflexive as Hirr0.
    pose proof R_deq_ext_transitive as Htrans0.
    destruct (strict_partial_order_extension (tc R_deq_ext) HR_deq_ext_dec)
      as [prt_deq [Hirr_deq [Htrans_deq [Hsub_deq [Htot_deq Hprt_deq_dec]]]]].

    (* 2. Define the total relationship for ALL operations. *)
    pose (R_all a b :=
      pre a b \/
      (is_enqueue val a /\ is_enqueue val b /\ exists da db, val a da /\ val b db /\ prt_deq da db) \/
      (is_dequeue val a /\ is_dequeue val b /\ prt_deq a b) \/
      val a b).

    (* Helpers mapping pre to prt_deq to satisfy the acyclicity requirements *)
    assert (Hpre_enq_to_prt_deq : forall e1 e2 d1 d2,
      val e1 d1 -> val e2 d2 -> pre e1 e2 -> prt_deq d1 d2).
    { intros e1 e2 d1 d2 Hv1 Hv2 Hpre.
      apply Hsub_deq. apply tc_once. left. right.
      split.
      - intros Heq. subst d2.
        assert (e1 = e2) by (eapply def_enqueue_once; eauto). subst.
        eapply pre_irreflexive; eauto.
      - exists e1, e2. auto. }

    assert (Hpre_deq_to_prt_deq : forall d1 d2,
      is_dequeue val d1 -> is_dequeue val d2 -> pre d1 d2 -> prt_deq d1 d2).
    { intros d1 d2 _ _ Hpre. apply Hsub_deq. apply tc_once. left. left. exact Hpre. }

    assert (Hpre_deq_val_to_prt_deq : forall d d' e,
      is_dequeue val d -> val e d' -> pre d e -> prt_deq d d').
    { intros d d' e Hd Hval Hpre.
      apply Hsub_deq. apply tc_once. right.
      split.
      - intros Heq. subst d'. exact (def_val_then_not_pr _ _ Hval Hpre).
      - exists e. split; [exact Hval | exact Hpre]. }

    assert (Hprt_deq_enq_R_all : forall e1 e2 d1 d2,
      val e1 d1 -> val e2 d2 -> prt_deq d1 d2 -> R_all e1 e2).
    { intros e1 e2 d1 d2 Hv1 Hv2 Hdeq.
      right; left. split; [exists d1; exact Hv1|].
      split; [exists d2; exact Hv2|].
      exists d1, d2. auto. }

    assert (Hprt_deq_deq_R_all : forall d1 d2 e1 e2,
      val e1 d1 -> val e2 d2 -> prt_deq d1 d2 -> R_all d1 d2).
    { intros d1 d2 e1 e2 Hv1 Hv2 Hdeq.
      right; right; left. split; [exists e1; exact Hv1|].
      split; [exists e2; exact Hv2|]. exact Hdeq. }

    (* 3. Topologically sort ALL operations based on R_all. *)
    assert (Hisenq_dec : ∀ a, decidable (is_enqueue val a)).
    { intros a. unfold is_enqueue. apply dec_exists_op. intros y. apply def_wf_val_decidable. }
    assert (Hisdeq_dec : ∀ a, decidable (is_dequeue val a)).
    { intros a. unfold is_dequeue. apply dec_exists_op. intros y. apply def_wf_val_decidable. }
    assert (HR_all_dec_base : ∀ x y, decidable (R_all x y)).
    { intros a b. unfold R_all.
      apply dec_or; first by apply def_wf_pre_decidable.
      apply dec_or.
      - apply dec_and; first by apply Hisenq_dec.
        apply dec_and; first by apply Hisenq_dec.
        apply dec_exists_op. intros da. apply dec_exists_op. intros db.
        apply dec_and; first by apply def_wf_val_decidable.
        apply dec_and; [by apply def_wf_val_decidable | apply Hprt_deq_dec].
      - apply dec_or; last by apply def_wf_val_decidable.
        apply dec_and; first by apply Hisdeq_dec.
        apply dec_and; [by apply Hisdeq_dec | apply Hprt_deq_dec]. }
    assert (HR_all_dec : ∀ x y, decidable (tc R_all x y))
      by (intros; by apply tc_decidable).
    assert (HR_all_irr : Irreflexive (tc R_all)) by (eapply lem_tc_R_all_irreflexive; eauto).
    destruct (strict_partial_order_extension (tc R_all) HR_all_dec)
      as [prt_raw [Hirr [Htrans [Hsub [Htot Hprt_raw_dec]]]]].

    (* 4. Filter out any junk operations from the total order *)
    pose (prt_valid a b := is_valid_op a /\ is_valid_op b /\ prt_raw a b).

    exists prt_valid.
    split.
    - intros a b Hpre. split; [|split].
      + eapply lem_enqueue_or_dequeue1 in Hpre; eauto. apply ipr_queue_wellformed.
      + eapply lem_enqueue_or_dequeue2 in Hpre; eauto. apply ipr_queue_wellformed.
      + apply Hsub. apply tc_once. left. exact Hpre.
    - constructor.
      + (* WellformedHistory prt_valid val *)
        constructor.
        * (* Transitive *)
          intros a b c (Hva & Hvb & Hab) (_ & Hvc & Hbc).
          split; [exact Hva|]. split; [exact Hvc|]. eapply Htrans; eauto.
        * (* Antisymmetric *)
          intros a b (Hva & Hvb & Hab) (_ & _ & Hba).
          exfalso. apply (Hirr a). eapply Htrans; eauto.
        * (* Irreflexive *)
          intros a (_ & _ & Haa). exact (Hirr a Haa).
        * (* def_enqueue_once *) apply def_enqueue_once.
        * (* def_dequeue_once *) apply def_dequeue_once.
        * (* def_val_order *) apply def_val_order.
        * (* def_enqueue_or_dequeue *)
          intros a b (Hva & Hvb & _).
          split.
          -- destruct Hva as [[d Hd] | [e He]]; [exists d; left | exists e; right]; eauto.
          -- destruct Hvb as [[d Hd] | [e He]]; [exists d; left | exists e; right]; eauto.
        * (* val_then_not_pr *)
          intros e d Hval (Hve & Hvd & Hprt).
          assert (Hprt_ed : prt_raw e d).
          { apply Hsub. apply tc_once. right; right; right. exact Hval. }
          apply (Hirr e). eapply Htrans; eauto.
        * (* def_wf_pre_decidable for prt_valid *)
          intros a b. unfold prt_valid, is_valid_op.
          apply dec_and; first by (apply dec_or; (apply dec_exists_op; intros; apply def_wf_val_decidable)).
          apply dec_and; first by (apply dec_or; (apply dec_exists_op; intros; apply def_wf_val_decidable)).
          apply Hprt_raw_dec.
        * (* def_wf_val_decidable *) apply def_wf_val_decidable.

      + (* dequeue_ordered *)
        intros a b Hda Hdb Hneq.
        destruct (Htot a b Hneq) as [Hraw | Hraw].
        * left. repeat split; eauto; right; eauto.
        * right. repeat split; eauto; right; eauto.

      + (* enqueue_dequeue_ordered *)
        intros e d He Hd.
        destruct (decide (e = d)) as [Heq | Hneq].
        * subst d. exfalso.
          destruct He as [re Hve]. destruct Hd as [ie Hvi].
          eapply def_val_order; [exact Hve|]. exists ie. left. exact Hvi.
        * destruct (Htot e d Hneq) as [Hraw | Hraw].
          -- left. split; [left; exact He|]. split; [right; exact Hd|]. exact Hraw.
          -- right. split; [right; exact Hd|]. split; [left; exact He|]. exact Hraw.

      + (* ir_ooo: FIFO property *)
        intros ia ra ib rb Hva Hvb (Hvia & Hvib & Hprt_ia_ib) (Hvib' & Hvra & Hprt_ib_ra).
        destruct (decide (ra = rb)) as [Heq|Hneq2].
        * subst rb. exfalso.
          assert (ia = ib) by (eapply def_enqueue_once; eauto).
          subst. eapply Hirr; eauto.
        * destruct (Htot_deq ra rb Hneq2) as [Hdeq|Hdeq].
          -- split; [right; exists ia; exact Hva|].
             split; [right; exists ib; exact Hvb|].
             apply Hsub. apply tc_once.
             eapply Hprt_deq_deq_R_all; eauto.
          -- exfalso.
             assert (Hprt_ib_ia : prt_raw ib ia).
             { apply Hsub. apply tc_once.
               eapply Hprt_deq_enq_R_all; eauto. }
             apply (Hirr ia). eapply Htrans; eauto.
  Qed.
End insert_pr_relaxed_queue_revised.

Lemma order_correct_then_pr_relaxed_queue `{abstract_queue_model} pre val empty :
  linearizable_set pre val empty →
  order_correct pre val →
  InsertPrRelaxedQueue (non_empty_pre pre empty) val.
Proof.
  intros Hls Hnoord.
  assert (Hwf_ne : WellformedHistory (non_empty_pre pre empty) val).
  { by apply linearizable_set_then_wellformed. }
  assert (Hch : ConcHistory pre).
  { by destruct Hls as [Hch _]. }
  assert (Hempty_dec : ∀ a, decidable (empty a)).
  { destruct Hls as [_ (prt & _ & Hsel)].
    destruct Hsel as [Hseh _]. destruct Hseh as [Hweh _].
    by destruct Hweh as [_ _ _ _ _ _ _ ? _]. }
  assert (Hch_ne : ConcHistory (non_empty_pre pre empty)).
  { by apply pre_conc_history_then_non_empty_pre_conc_history. }
  constructor.
  - exact Hwf_ne.
  - exact Hch_ne.
  - intros e1 e2 d1 d2 Hefpe1 Hefve1d1 Hefve2d2 Hfalso.
    (* Translate to original relations and use Hooo *)
    assert (Hpree : pre e1 e2).
    { destruct Hefpe1 as (?&?); eauto. }
    assert (Hpred : pre d2 d1).
    { destruct Hfalso as (?&?); eauto. }
    eapply (Hnoord e1 e2 d1 d2); eauto.
Qed.

Theorem insert_pr_relaxed_queue_linearizable_final `{abstract_queue_model} pre val :
  ConcHistory pre →
  InsertPrRelaxedQueue pre val → linearizable_non_empty_queue pre val.
Proof.
  intros Hconc Hrrs.
  destruct (@insert_pr_relaxed_queue_linearizable _ pre val Hrrs) as [prt1 [Hsub1 Hipr]].
  destruct (@insert_relaxed_queue_linearizable _ prt1 val Hipr) as [prt2 [Hsub2 Hseq]].
  (* Construct linearizable_non_empty_stack *)
  unfold linearizable_non_empty_queue.
  split.
  - eauto.
  - exists prt2.
    split.
    + (* subrelation pre prt2 *)
      intros a b Hpre.
      apply Hsub2. apply Hsub1. done.
    + exact Hseq.
Qed.
