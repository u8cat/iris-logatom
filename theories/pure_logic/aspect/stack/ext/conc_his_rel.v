(* conc_his_rel.v, ported from concur_history_relations.thy *)

From stdpp Require Import finite relations.
From iris_logatom.lib Require Import list.
From iris_logatom.pure_logic Require Export linear.

Class abstract_stack_model := AbstractStackModel {
  operation : Type;
  operation_eqdec :: EqDecision operation;
  operation_countable :: Countable operation;
}.

Notation Acyclic R := (Irreflexive (tc R)).
Local Instance relation_union {A} : Union (relation A) :=
  λ r1 r2, Relation_Operators.union A r1 r2.

Class FinitePredicate {A} `{!EqDecision A} (P : A → Prop) : Prop :=
  finite_predicate: ∃ enum, NoDup enum ∧ (∀ x, P x → x ∈ enum).

Section def.
  Context `{abstract_stack_model}.
  Implicit Types (pre val : relation operation) (empty : operation → Prop).

  (* concur_history_relations.thy:5 *)
  Class Abcd (r : relation operation) : Prop :=
    abcd: ∀ a b c d, r a b → r c d → r a d ∨ r c b.

  (* concur_history_relations.thy:16 *)
  Lemma lem_total_then_abcd r :
    Total r → Transitive r → Abcd r.
  Proof.
    intros Htotal Htrans a b c d Hab Hcd.
    destruct (Htotal a d) as [Had|Hda].
    - left. done.
    - right. eapply Htrans; eauto.
  Qed.

  (* Variant for strict total orders using Trichotomy *)
  Lemma lem_trichotomy_then_abcd r :
    Trichotomy r → Transitive r → Abcd r.
  Proof.
    intros Htri Htrans a b c d Hab Hcd.
    destruct (Htri a d) as [Had|[Heq|Hda]].
    - left. done.
    - subst d. right. eapply Htrans; eauto.
    - right. eapply Htrans; eauto.
  Qed.

  (* Helper: transitive closure of a transitive relation is just the relation *)
  Lemma tc_transitive_collapse (r : relation operation) (x y : operation) :
    Transitive r → tc r x y → r x y.
  Proof.
    intros Htrans Hxy.
    induction Hxy as [a b Hab|a b c Hab Hbc IH].
    - exact Hab.
    - eapply Htrans; [exact Hab|exact IH].
  Qed.

  (* concur_history_relations.thy:20 *)
  Lemma lem_transitive_irreflexive_then_acyclic (r : relation operation) :
    Transitive r → Irreflexive r → Acyclic r.
  Proof.
    intros Htrans Hirr x Htc.
    apply (Hirr x). apply tc_transitive_collapse; assumption.
  Qed.

  (* Helper: subrelation is preserved by tc *)
  Lemma tc_subrel (r r' : relation operation) x y :
    subrelation r' r → tc r' x y → tc r x y.
  Proof.
    intros Hsub Htc.
    induction Htc as [a b Hab|a b c Hab Hbc IH].
    - apply tc_once. exact (Hsub _ _ Hab).
    - eapply tc_l; [exact (Hsub _ _ Hab)|exact IH].
  Qed.

  (* Helper: acyclicity is preserved under subrelation *)
  Lemma acyclic_subset (r r' : relation operation) :
    subrelation r' r → Acyclic r → Acyclic r'.
  Proof.
    intros Hsub Hacyc x Htc.
    apply (Hacyc x).
    eapply tc_subrel; [exact Hsub|exact Htc].
  Qed.

  (* concur_history_relations.thy:23 *)
  Lemma lem_irreflexive_then_not_equal (r : relation operation) a b :
    Irreflexive r → r a b → a ≠ b.
  Proof.
    intros Hirr Hab Heq. subst b. by eapply Hirr.
  Qed.

  (* concur_history_relations.thy:28 *)
  Class ConcHistory pre : Prop := {
    #[local] pre_transitive :: Transitive pre;
    #[local] pre_antisymmetric :: Antisymmetric operation (=) pre;
    #[local] pre_irreflexive :: Irreflexive pre;
    #[local] pre_abcd :: Abcd pre;
  }.

  (* concur_history_relations.thy:44 *)
  Definition val_order val :=
    ∀ ia ra, val ia ra → ¬∃ b, val b ia ∨ val ra b.

  (* concur_history_relations.thy:52 *)
  Definition push_once val :=
    ∀ ia ib ra, val ia ra → val ib ra → ia = ib.
  (* concur_history_relations.thy:56 *)
  Definition pop_once val :=
    ∀ ia ra rb, val ia ra → val ia rb → ra = rb.

  (* concur_history_relations.thy:60 *)
  Definition val_then_not_pr pre val :=
    ∀ ia ra, val ia ra → ¬ pre ra ia.

  (* concur_history_relations.thy:67 *)
  Definition is_push val op :=
    ∃ op', val op op'.
  (* concur_history_relations.thy:77 *)
  Definition is_pop val op :=
    ∃ op', val op' op.

  (* concur_history_relations.thy:88 *)
  Definition same_val val : relation operation :=
    λ a b, val a b ∨ val b a.

  (* concur_history_relations.thy:103 *)
  Lemma same_val_symmetric val : Symmetric (same_val val).
  Proof.
    intros a b [Hab|Hba]; [right|left]; done.
  Qed.

  (* concur_history_relations.thy:106 *)
  Definition elim_free pre val :=
    λ a, ∃ b, same_val val a b ∧ (pre a b ∨ pre b a).

  (* concur_history_relations.thy:119 *)
  Lemma elim_free_push_pop pre val a :
    elim_free pre val a → is_push val a ∨ is_pop val a.
  Proof.
    intros (b & Hsv & _).
    destruct Hsv as [Hab|Hba].
    - left. exists b. done.
    - right. exists b. done.
  Qed.

  (* concur_history_relations.thy:126 *)
  Lemma finite_elim_free pre val :
    FinitePredicate (λ a, is_push val a ∨ is_pop val a) →
    FinitePredicate (elim_free pre val).
  Proof.
    intros [enum [Hnodup Henum]].
    exists enum. split; first done.
    intros x Hef.
    apply Henum.
    by apply (elim_free_push_pop pre val).
  Qed.

  (* concur_history_relations.thy:134 *)
  Definition elim pre val :=
    λ a, (is_push val a ∨ is_pop val a) ∧ ¬ elim_free pre val a.

  (* concur_history_relations.thy:142 *)
  Definition elim_free_pre pre val : relation operation :=
    λ a b, elim_free pre val a ∧ elim_free pre val b ∧ pre a b.

  (* concur_history_relations.thy:154 *)
  Definition elim_free_val pre val : relation operation :=
    λ a b, elim_free pre val a ∧ elim_free pre val b ∧ val a b.

  (* concur_history_relations.thy:166 *)
  Definition elim_free_ir pre val ir : relation operation :=
    λ a b, elim_free pre val a ∧ elim_free pre val b ∧ ir a b.

  (* concur_history_relations.thy:178 *)
  Definition ins_order (pre val ir : relation operation) : relation operation :=
    λ a b, is_push val a ∧ is_push val b ∧ (pre a b ∨ ∃ c, pre a c ∧ ir c b).

  (* concur_history_relations.thy:195 *)
  Definition rem_order (pre val ir : relation operation) : relation operation :=
    λ a b, is_pop val a ∧ is_pop val b ∧ (pre a b ∨ (∃ c, ir a c ∧ ir c b)).

  (* concur_history_relations.thy:212 *)
  Record alternating (val ir : relation operation) := Alternating {
    alternating_sound: ∀ a b, ir a b → is_push val a ∧ is_pop val b ∨ is_pop val a ∧ is_push val b;
    alternating_complete: ∀ a b, is_push val a → is_pop val b → ir a b ∨ ir b a;
  }.

  (* concur_history_relations.thy:226 *)
  Definition order_correct pre val :=
    ∃ ir, alternating val ir ∧ (Acyclic (pre ∪ ir)) ∧
      (∀ ia ra ib, val ia ra → pre ia ra → ins_order pre val ir ia ib → ir ib ra →
        ∃ rb, val ib rb ∧ ¬ rem_order pre val ir ra rb).

  (* concur_history_relations.thy:257 *)
  (* Note: Unlike ConcHistory, WellformedHistory does not require Abcd.
     This matches the Isabelle formalization where wellformed_history only
     requires trans, antisym, irrefl without abcd. *)
  Class WellformedHistory pre val := {
    #[local] wf_pre_transitive :: Transitive pre;
    #[local] wf_pre_antisymmetric :: Antisymmetric operation (=) pre;
    #[local] wf_pre_irreflexive :: Irreflexive pre;
    #[local] operation_finite :: FinitePredicate (λ a, is_push val a ∨ is_pop val a);
    def_push_once : push_once val;
    def_pop_once : pop_once val;
    def_val_order : val_order val;
    def_push_or_pop : ∀ a b, pre a b → (∃ c, val a c ∨ val c a) ∧ (∃ c, val b c ∨ val c b);
    def_val_then_not_pr : val_then_not_pr pre val;
  }.

  (* concur_history_relations.thy:322 *)
  Lemma lem_push_or_pop1 pre val a b :
    WellformedHistory pre val → pre a b → is_push val a ∨ is_pop val a.
  Proof.
    intros Hwf Hpre.
    destruct (def_push_or_pop a b Hpre) as [[c [Hac|Hca]] _].
    - left. exists c. done.
    - right. exists c. done.
  Qed.

  (* concur_history_relations.thy:325 *)
  Lemma lem_push_or_pop2 pre val a b :
    WellformedHistory pre val → pre a b → is_push val b ∨ is_pop val b.
  Proof.
    intros Hwf Hpre.
    destruct (def_push_or_pop a b Hpre) as [_ [c [Hbc|Hcb]]].
    - left. exists c. done.
    - right. exists c. done.
  Qed.

  (* concur_history_relations.thy:328 *)
  Lemma lem_push_then_pop_exists val a : is_push val a → ∃ b, val a b ∧ is_pop val b.
  Proof.
    intros [ra Hvara].
    exists ra. split; [done|].
    exists a. done.
  Qed.

  (* concur_history_relations.thy:331 *)
  Lemma lem_pop_then_push_exists val a : is_pop val a → ∃ b, val b a ∧ is_push val b.
  Proof.
    intros [ia Hvalia].
    exists ia. split; [done|].
    exists a. done.
  Qed.

  (* concur_history_relations.thy:334 *)
  Lemma lem_val_then_push_and_pop val a b : val a b → is_push val a ∧ is_pop val b.
  Proof.
    intros Hab.
    split.
    - exists b. done.
    - exists a. done.
  Qed.

  (* Helper: val a b implies a is push *)
  Lemma val_push val a b : val a b → is_push val a.
  Proof.
    intros Hab. exists b. done.
  Qed.

  (* Helper: val a b implies b is pop *)
  Lemma val_pop val a b : val a b → is_pop val b.
  Proof.
    intros Hab. exists a. done.
  Qed.

  (* concur_history_relations.thy:339 *)
  Lemma val_preserves_ef1 pre val a b :
    WellformedHistory pre val → val a b → elim_free pre val a → elim_free pre val b.
  Proof.
    intros Hwf Hab (c & Hsv & Hpre).
    exists a. split.
    - right. done.
    - destruct Hsv as [Hac|Hca].
      + (* a is push, c is pop *)
        pose proof (def_pop_once _ _ _ Hac Hab) as Heq. subst c.
        destruct Hpre; [right|left]; done.
      + (* c is push, a is pop - contradiction with val_order *)
        exfalso.
        eapply def_val_order; first exact Hca.
        exists b. right. done.
  Qed.

  (* concur_history_relations.thy:342 *)
  Lemma val_preserves_ef2 pre val a b :
    WellformedHistory pre val → val a b → elim_free pre val b → elim_free pre val a.
  Proof.
    intros Hwf Hab (c & Hsv & Hpre).
    exists b. split.
    - left. done.
    - destruct Hsv as [Hbc|Hcb].
      + (* b is push - contradiction with val_order *)
        exfalso.
        eapply def_val_order; first exact Hab.
        exists c. right. done.
      + (* c is push, b is pop *)
        pose proof (def_push_once _ _ _ Hcb Hab) as Heq. subst c.
        destruct Hpre; [right|left]; done.
  Qed.

  (* concur_history_relations.thy:345 *)
  Lemma alternating_then_ef_alternating pre val ir :
    WellformedHistory pre val → alternating val ir →
    alternating (elim_free_val pre val) (elim_free_ir pre val ir).
  Proof.
    intros Hwf [Hsound Hcomplete].
    constructor.
    - intros a b (Hefa & Hefb & Hir).
      destruct (Hsound _ _ Hir) as [[Hpusha Hpopb]|[Hpopa Hpushb]].
      + left. split.
        * destruct Hpusha as [c Hac].
          exists c. split; last split; try done.
          eapply val_preserves_ef1; eauto.
        * destruct Hpopb as [c Hcb].
          exists c. split; last split; try done.
          eapply val_preserves_ef2; eauto.
      + right. split.
        * destruct Hpopa as [c Hca].
          exists c. split; last split; try done.
          eapply val_preserves_ef2; eauto.
        * destruct Hpushb as [c Hbc].
          exists c. split; last split; try done.
          eapply val_preserves_ef1; eauto.
    - intros a b (c & Hefa & Hefc & Hac) (d & Hefd & Hefb & Hdb).
      destruct (Hcomplete a b) as [Hab|Hba].
      + exists c. done.
      + exists d. done.
      + left. split; last split; done.
      + right. split; last split; done.
  Qed.

  (* concur_history_relations.thy:380 *)
  Class SequentialSet pre val := {
    sequential_set_wellformed :: WellformedHistory pre val;
    total_on_push a b : is_push val a → is_push val b → a ≠ b → pre a b ∨ pre b a;
    total_on_pop a b: is_pop val a → is_pop val b → a ≠ b → pre a b ∨ pre b a;
    total_on_push_pop a b: is_push val a → is_pop val b → pre a b ∨ pre b a;
  }.

  (* concur_history_relations.thy:414 *)
  Definition sequential_lifo pre val :=
    ∀ ia ib ra rb, val ia ra → val ib rb → pre ia ib → pre ib ra → pre rb ra.

  (* concur_history_relations.thy:418 *)
  Lemma ef_conf_history pre val :
    ConcHistory pre → ConcHistory (elim_free_pre pre val).
  Proof.
    intros Hch.
    constructor.
    - intros a b c (Hefa & Hefb & Hab) (Hefb' & Hefc & Hbc).
      split; last split; try done.
      by etrans.
    - intros a b (Hefa & Hefb & Hab) (Hefb' & Hefa' & Hba).
      by eapply pre_antisymmetric.
    - intros a (Hefa & Hefa' & Haa).
      by eapply pre_irreflexive.
    - intros a b c d (Hefa & Hefb & Hab) (Hefc & Hefd & Hcd).
      destruct (abcd a b c d Hab Hcd) as [Had|Hcb].
      + left. split; last split; done.
      + right. split; last split; done.
  Qed.

  (* concur_history_relations.thy:427 *)
  Lemma ef_finite pre val :
    FinitePredicate (λ a, is_push val a ∨ is_pop val a) →
    FinitePredicate (λ a, is_push (elim_free_val pre val) a ∨ is_pop (elim_free_val pre val) a).
  Proof.
    intros [enum [Hnodup Henum]].
    exists enum. split; first done.
    intros x [[b (Hefa & Hefb & Hab)]|[b (Hefb & Hefa & Hba)]].
    - apply Henum. left. exists b. done.
    - apply Henum. right. exists b. done.
  Qed.

  (* concur_history_relations.thy:432 *)
  Lemma val_then_ef_val pre val a b :
    elim_free pre val a → val a b → val_order val → pop_once val →
    elim_free_val pre val a b.
  Proof.
    intros (c & Hsv & Hpre) Hab Hvo Hpo.
    split; last split; try done.
    - exists c. split; try done.
    - exists a. split.
      + right. done.
      + destruct Hsv as [Hac|Hca].
        * pose proof (Hpo _ _ _ Hac Hab) as Heq. subst c.
          destruct Hpre; [right|left]; done.
        * exfalso. eapply Hvo; first exact Hca.
          exists b. right. done.
  Qed.

  (* concur_history_relations.thy:440 *)
  Lemma val_then_not_pr_mono pre prt val :
    val_then_not_pr pre val → subrelation pre prt →
    val_then_not_pr pre val.
  Proof.
    intros Hvnp Hsub ia ra Hval.
    apply Hvnp. done.
  Qed.

  (* concur_history_relations.thy:444 *)
  Definition all_popped_or_empty val empty :=
    ∀ a, empty a ∨ ∃ b, val a b ∨ val b a.

  (* concur_history_relations.thy:448 *)
  Definition empty_then_not_val val empty :=
    ∀ a, empty a → ¬(∃ b, val a b) ∧ ¬(∃ b, val b a).

  (* concur_history_relations.thy:453 *)
  Class WellformedEmptyHistory pre val empty := {
    #[local] empty_pre_conchistory :: ConcHistory pre;
    #[local] empty_operation_finite :: FinitePredicate (λ a, is_push val a ∨ is_pop val a);
    empty_def_push_once : push_once val;
    empty_def_pop_once : pop_once val;
    empty_def_val_order : val_order val;
    empty_def_all_popped_or_empty : all_popped_or_empty val empty;
    empty_def_empty_then_not_val : empty_then_not_val val empty;
    empty_def_val_then_not_pr : val_then_not_pr pre val;
  }.

  (* concur_history_relations.thy:540 *)
  (* NOTE: Changed from Total to Trichotomy to support strict (irreflexive) orders.
     Trichotomy gives: pre x y ∨ x = y ∨ pre y x, which is appropriate for
     strict total orders where pre x x is always false. *)
  Class SequentialEmptyHistory pre val empty := {
    #[local] sequential_empty_history_wellformed :: WellformedEmptyHistory pre val empty;
    def_trichotomy : Trichotomy pre;
  }.

  (* concur_history_relations.thy:562 *)
  Definition correct_empty pre val empty :=
    ∀ a, empty a → ∀ ib rb, val ib rb → pre ib a ∧ pre rb a ∨ pre a ib ∧ pre a rb.

  (* concur_history_relations.thy:566 *)
  Definition non_empty_pre pre empty : relation operation :=
    λ a b, pre a b ∧ ¬ empty a ∧ ¬ empty b.

  (* concur_history_relations.thy:578 *)
  (* Lemma non_empty_pre_then_pre pre empty :
    ∀ a b, non_empty_pre pre empty a b → pre a b ∧ ¬ empty a ∧ ¬ empty b. *)

  (* concur_history_relations.thy:581 *)
  Lemma pre_conc_history_then_non_empty_pre_conc_history pre empty :
    ConcHistory pre → ConcHistory (non_empty_pre pre empty).
  Proof.
    intros Hch.
    constructor.
    - intros a b c (Hab & Hnea & Hneb) (Hbc & Hneb' & Hnec).
      split; last split; try done.
      by etrans.
    - intros a b (Hab & Hnea & Hneb) (Hba & Hneb' & Hnea').
      by eapply pre_antisymmetric.
    - intros a (Haa & Hnea & Hnea').
      by eapply pre_irreflexive.
    - intros a b c d (Hab & Hnea & Hneb) (Hcd & Hnec & Hned).
      destruct (abcd a b c d Hab Hcd) as [Had|Hcb].
      + left. split; last split; done.
      + right. split; last split; done.
  Qed.

  (* concur_history_relations.thy:593
  TODO: the translation might be wrong *)
  Lemma ef_all_popped pre val empty :
    ∀ a b, pre a b →
    (empty a ∨ ∃ c, val a c ∨ val c a) ∧ (empty b ∨ ∃ c, val b c ∨ val c b) →
    val_order val → pop_once val → push_once val →
    elim_free_pre (non_empty_pre pre empty) val a b →
    (∃ c, elim_free_val (non_empty_pre pre empty) val a c ∨ elim_free_val (non_empty_pre pre empty) val c a) ∧
    (∃ c, elim_free_val (non_empty_pre pre empty) val b c ∨ elim_free_val (non_empty_pre pre empty) val c b).
  Proof.
    intros a b Hpre [Haec Hbec] Hvo Hpo Hpuo (Hefa & Hefb & (Hnepre & Hnea & Hneb)).
    destruct Hefa as (c & Hsva & Hprea).
    destruct Hefb as (d & Hsvb & Hpreb).
    assert (Hefa' : elim_free (non_empty_pre pre empty) val a).
    { exists c. split; done. }
    assert (Hefc : elim_free (non_empty_pre pre empty) val c).
    { exists a. split.
      - destruct Hsva as [Hac|Hca]; [right|left]; done.
      - destruct Hprea as [Hprea|Hprea]; [right|left]; done. }
    assert (Hefb' : elim_free (non_empty_pre pre empty) val b).
    { exists d. split; done. }
    assert (Hefd : elim_free (non_empty_pre pre empty) val d).
    { exists b. split.
      - destruct Hsvb as [Hbd|Hdb]; [right|left]; done.
      - destruct Hpreb as [Hpreb|Hpreb]; [right|left]; done. }
    split.
    - destruct Hsva as [Hac|Hca].
      + exists c. left. split; last split; done.
      + exists c. right. split; last split; done.
    - destruct Hsvb as [Hbd|Hdb].
      + exists d. left. split; last split; done.
      + exists d. right. split; last split; done.
  Qed.

  (* concur_history_relations.thy:626 *)
  Lemma ef_empty_mono pre prt val empty :
    subrelation pre prt → subrelation (elim_free_pre (non_empty_pre pre empty) val) prt.
  Proof.
    intros Hsub a b (Hefa & Hefb & (Hab & Hnea & Hneb)).
    by apply Hsub.
  Qed.

  (* concur_history_relations.thy:632 *)
  Lemma ef_val_then_val pre val empty a b :
    elim_free_val (non_empty_pre pre empty) val a b →
    val a b.
  Proof.
    intros (Hefa & Hefb & Hab). done.
  Qed.

  (* concur_history_relations.thy:635 *)
  Lemma ef_push_then_empty_push pre val empty a :
    is_push (elim_free_val pre val) a → empty_then_not_val val empty →
    is_push (elim_free_val (non_empty_pre pre empty) val) a.
  Proof.
    intros [b ((c & Hsva & Hpreca) & (d & Hsvb & Hprecb) & Hab)] Henv.
    exists b. split; last split; try done.
    - exists c. split; first done.
      destruct Hpreca as [Hac|Hca].
      + left. split; last split; try done.
        * intros Hea. destruct (Henv a Hea) as [Hnv _].
          apply Hnv. exists b. done.
        * intros Hec. destruct Hsva as [Hac'|Hca'].
          -- destruct (Henv c Hec) as [_ Hnv]. apply Hnv. exists a. done.
          -- destruct (Henv c Hec) as [Hnv _]. apply Hnv. exists a. done.
      + right. split; last split; try done.
        * intros Hec. destruct Hsva as [Hac'|Hca'].
          -- destruct (Henv c Hec) as [_ Hnv]. apply Hnv. exists a. done.
          -- destruct (Henv c Hec) as [Hnv _]. apply Hnv. exists a. done.
        * intros Hea. destruct (Henv a Hea) as [Hnv _].
          apply Hnv. exists b. done.
    - exists d. split; first done.
      destruct Hprecb as [Hbd|Hdb].
      + left. split; last split; try done.
        * intros Heb. destruct (Henv b Heb) as [_ Hnv].
          apply Hnv. exists a. done.
        * intros Hed. destruct Hsvb as [Hbd'|Hdb'].
          -- destruct (Henv d Hed) as [_ Hnv]. apply Hnv. exists b. done.
          -- destruct (Henv d Hed) as [Hnv _]. apply Hnv. exists b. done.
      + right. split; last split; try done.
        * intros Hed. destruct Hsvb as [Hbd'|Hdb'].
          -- destruct (Henv d Hed) as [_ Hnv]. apply Hnv. exists b. done.
          -- destruct (Henv d Hed) as [Hnv _]. apply Hnv. exists b. done.
        * intros Heb. destruct (Henv b Heb) as [_ Hnv].
          apply Hnv. exists a. done.
  Qed.

  (* concur_history_relations.thy:661 *)
  Lemma empty_push_then_ef_push pre val empty a :
    is_push (elim_free_val (non_empty_pre pre empty) val) a →
    is_push (elim_free_val pre val) a.
  Proof.
    intros [b ((c & Hsva & Hpreca) & (d & Hsvb & Hprecb) & Hab)].
    exists b. split; last split; try done.
    - exists c. split; first done.
      destruct Hpreca as [(Hac & _ & _)|(Hca & _ & _)]; [left|right]; done.
    - exists d. split; first done.
      destruct Hprecb as [(Hbd & _ & _)|(Hdb & _ & _)]; [left|right]; done.
  Qed.

  (* concur_history_relations.thy:673 *)
  Lemma ef_pop_then_empty_pop pre val empty a :
    is_pop (elim_free_val pre val) a →
    empty_then_not_val val empty →
    val_order val → pop_once val → push_once val →
    is_pop (elim_free_val (non_empty_pre pre empty) val) a.
  Proof.
    intros [b ((c & Hsvb & Hprecb) & (d & Hsva & Hpreca) & Hba)] Henv Hvo Hpo Hpuo.
    exists b. split; last split; try done.
    - exists c. split; first done.
      destruct Hprecb as [Hbc|Hcb].
      + left. split; last split; try done.
        * intros Heb. destruct (Henv b Heb) as [Hnv _].
          apply Hnv. exists a. done.
        * intros Hec. destruct Hsvb as [Hbc'|Hcb'].
          -- destruct (Henv c Hec) as [_ Hnv]. apply Hnv. exists b. done.
          -- destruct (Henv c Hec) as [Hnv _]. apply Hnv. exists b. done.
      + right. split; last split; try done.
        * intros Hec. destruct Hsvb as [Hbc'|Hcb'].
          -- destruct (Henv c Hec) as [_ Hnv]. apply Hnv. exists b. done.
          -- destruct (Henv c Hec) as [Hnv _]. apply Hnv. exists b. done.
        * intros Heb. destruct (Henv b Heb) as [Hnv _].
          apply Hnv. exists a. done.
    - exists d. split; first done.
      destruct Hpreca as [Had|Hda].
      + left. split; last split; try done.
        * intros Hea. destruct (Henv a Hea) as [_ Hnv].
          apply Hnv. exists b. done.
        * intros Hed. destruct Hsva as [Had'|Hda'].
          -- destruct (Henv d Hed) as [_ Hnv]. apply Hnv. exists a. done.
          -- destruct (Henv d Hed) as [Hnv _]. apply Hnv. exists a. done.
      + right. split; last split; try done.
        * intros Hed. destruct Hsva as [Had'|Hda'].
          -- destruct (Henv d Hed) as [_ Hnv]. apply Hnv. exists a. done.
          -- destruct (Henv d Hed) as [Hnv _]. apply Hnv. exists a. done.
        * intros Hea. destruct (Henv a Hea) as [_ Hnv].
          apply Hnv. exists b. done.
  Qed.

  (* concur_history_relations.thy:699 *)
  Lemma empty_pop_then_ef_pop pre val empty a :
    is_pop (elim_free_val (non_empty_pre pre empty) val) a →
    is_pop (elim_free_val pre val) a.
  Proof.
    intros [b ((c & Hsvb & Hprecb) & (d & Hsva & Hpreca) & Hba)].
    exists b. split; last split; try done.
    - exists c. split; first done.
      destruct Hprecb as [(Hbc & _ & _)|(Hcb & _ & _)]; [left|right]; done.
    - exists d. split; first done.
      destruct Hpreca as [(Had & _ & _)|(Hda & _ & _)]; [left|right]; done.
  Qed.

  (* concur_history_relations.thy:711 *)
  Lemma ef_ins_then_ins pre val empty ir ia ib :
    ins_order (elim_free_pre (non_empty_pre pre empty) val)
      (elim_free_val (non_empty_pre pre empty) val) ir
      ia ib →
    ins_order pre val ir ia ib.
  Proof.
    intros (Hpusha & Hpushb & Horder).
    split; last split.
    - destruct Hpusha as [c (Hefa & Hefc & Hac)]. exists c. done.
    - destruct Hpushb as [c (Hefb & Hefc & Hbc)]. exists c. done.
    - destruct Horder as [(Hefa & Hefb & (Hab & _ & _))|(c & (Hefa & Hefc & (Hac & _ & _)) & Hcb)].
      + left. done.
      + right. exists c. done.
  Qed.

  (* concur_history_relations.thy:720 *)
  Lemma ef_rem_then_rem pre val empty ir ra rb :
    rem_order (elim_free_pre (non_empty_pre pre empty) val)
      (elim_free_val (non_empty_pre pre empty) val) ir
      ra rb →
    rem_order pre val ir ra rb.
  Proof.
    intros (Hpopa & Hpopb & Horder).
    split; last split.
    - destruct Hpopa as [c (Hefc & Hefa & Hca)]. exists c. done.
    - destruct Hpopb as [c (Hefc & Hefb & Hcb)]. exists c. done.
    - destruct Horder as [(Hefa & Hefb & (Hab & _ & _))|(c & Hac & Hcb)].
      + left. done.
      + right. exists c. done.
  Qed.

  (* concur_history_relations.thy:730 *)
  Class SequentialStack pre val := {
    #[local] sequential_stack_sequential_set :: SequentialSet pre val;
    def_sequential_lifo : sequential_lifo pre val;
  }.

  (* concur_history_relations.thy:744 *)
  Class SequentialEmptySet pre val empty := {
    #[local] sequential_empty_set_sequential_empty_history :: SequentialEmptyHistory pre val empty;
    def_correct_empty : correct_empty pre val empty;
  }.

  (* concur_history_relations.thy:761 *)
  Class SequentialEmptyStack pre val empty := {
    #[local] sequential_empty_stack_sequential_empty_set :: SequentialEmptySet pre val empty;
    empty_def_sequential_lifo : sequential_lifo pre val;
  }.

  (* concur_history_relations.thy:785 *)
  Definition linearizable_set pre val empty :=
    ConcHistory pre ∧ ∃ prt, subrelation pre prt ∧ SequentialEmptySet prt val empty.

  (* concur_history_relations.thy:795 *)
  Definition linearizable_non_empty_stack pre val :=
    ConcHistory pre ∧ ∃ prt, subrelation pre prt ∧ SequentialStack prt val.

  (* concur_history_relations.thy:805 *)
  Definition linearizable_stack pre val empty :=
    ConcHistory pre ∧ ∃ prt, subrelation pre prt ∧ SequentialEmptyStack prt val empty.

  (* concur_history_relations.thy:815 *)
  Lemma linearizable_set_then_wellformed_empty pre val empty :
    linearizable_set pre val empty →
    WellformedEmptyHistory pre val empty.
  Proof.
    intros (Hch & prt & Hsub & Hseq).
    destruct Hseq as [Hwf _].
    destruct Hwf as [Hwfe Htotal].
    destruct Hwfe.
    rename select (val_then_not_pr _ _) into Hvnpr.
    constructor; try done.
    intros ia ra Hval Hpre.
    eapply Hvnpr; first exact Hval.
    by apply Hsub.
  Qed.

  (* concur_history_relations.thy:838 *)
  Lemma wellformed_empty_then_wellformed pre val empty:
    WellformedEmptyHistory pre val empty →
    WellformedHistory (non_empty_pre pre empty) val.
  Proof.
    intros Hwfe.
    destruct Hwfe.
    rename select (all_popped_or_empty _ _) into Hapoe.
    rename select (val_then_not_pr _ _) into Hvnpr.
    constructor.
    - (* Transitive *)
      intros a b c (Hab & Hnea & Hneb) (Hbc & _ & Hnec).
      split; last split; try done.
      by etrans.
    - (* Antisymmetric *)
      intros a b (Hab & Hnea & Hneb) (Hba & _ & _).
      by eapply pre_antisymmetric.
    - (* Irreflexive *)
      intros a (Haa & _ & _).
      by eapply pre_irreflexive.
    - done.
    - done.
    - done.
    - done.
    - intros a b (Hab & Hnea & Hneb).
      destruct (Hapoe a) as [Hea|Ha]; first done.
      destruct (Hapoe b) as [Heb|Hb]; first done.
      done.
    - intros ia ra Hval Hpre.
      destruct Hpre as (Hpre & _ & _).
      by eapply Hvnpr.
  Qed.

  (* concur_history_relations.thy:853 *)
  Lemma linearizable_set_then_wellformed pre val empty:
    linearizable_set pre val empty →
    WellformedHistory (non_empty_pre pre empty) val.
  Proof.
    intros Hls.
    apply wellformed_empty_then_wellformed.
    by apply linearizable_set_then_wellformed_empty.
  Qed.

  (* concur_history_relations.thy:856 *)
  Lemma wellformed_then_ef_wellformed pre val :
    WellformedHistory pre val →
    WellformedHistory (elim_free_pre pre val) (elim_free_val pre val).
  Proof.
    intros Hwf.
    constructor.
    - (* Transitive *)
      intros a b c (Hefa & Hefb & Hab) (Hefb' & Hefc & Hbc).
      split; last split; try done.
      by etrans.
    - (* Antisymmetric *)
      intros a b (Hefa & Hefb & Hab) (Hefb' & Hefa' & Hba).
      by eapply antisymmetry.
    - (* Irreflexive *)
      intros a (Hefa & Hefa' & Haa).
      exfalso. eapply wf_pre_irreflexive. exact Haa.
    - apply ef_finite. apply operation_finite.
    - intros ia ib ra (Hefa & Hefra & Hia) (Hefb & Hefra' & Hib).
      f_equal. eapply def_push_once; done.
    - intros ia ra rb (Hefa & Hefra & Hia) (Hefa' & Hefrb & Hib).
      f_equal. eapply def_pop_once; done.
    - intros ia ra (Hefa & Hefra & Hia).
      intros (b & Hb). destruct Hb as [(Hbef & _ & Hbia)|(Hefra_ & _ & Hrab)].
      + eapply def_val_order; first exact Hia.
        exists b. left. done.
      + eapply def_val_order; first exact Hia.
        exists b. right. done.
    - intros a b (Hefa & Hefb & Hab).
      assert (Hefa' : elim_free pre val a) by exact Hefa.
      assert (Hefb' : elim_free pre val b) by exact Hefb.
      split.
      + destruct Hefa as (c & Hsva & Hpreca).
        destruct Hsva as [Hac|Hca].
        * exists c. left.
          split; [exact Hefa'|].
          split; [|exact Hac].
          eapply (val_preserves_ef1 pre val a c Hwf Hac Hefa').
        * exists c. right.
          split; [|split; [|exact Hca]].
          -- eapply (val_preserves_ef2 pre val c a Hwf Hca).
             exists c. split; [right; done|done].
          -- exists c. split; [right; done|done].
      + destruct Hefb as (c & Hsvb & Hprecb).
        destruct Hsvb as [Hbc|Hcb].
        * exists c. left.
          split; [exact Hefb'|].
          split; [|exact Hbc].
          eapply (val_preserves_ef1 pre val b c Hwf Hbc Hefb').
        * exists c. right.
          split; [|split; [|exact Hcb]].
          -- eapply (val_preserves_ef2 pre val c b Hwf Hcb).
             exists c. split; [right; done|done].
          -- exists c. split; [right; done|done].
    - intros ia ra (Hefa & Hefra & Hia) (Hefra' & Hefa' & Hrai).
      eapply def_val_then_not_pr; done.
  Qed.

  (* concur_history_relations.thy:898 *)
  Lemma ef_ir_in_ir pre val empty ir :
    subrelation (elim_free_ir (non_empty_pre pre empty) val ir) ir.
  Proof.
    intros a b (Hefa & Hefb & Hir). done.
  Qed.

  (* concur_history_relations.thy:901 *)
  Lemma help_me pre val empty ir :
    subrelation (pre ∪ elim_free_ir (non_empty_pre pre empty) val ir) (pre ∪ ir).
  Proof.
    intros a b [Hpre|Hefir].
    - left. done.
    - right. by eapply ef_ir_in_ir.
  Qed.

  (* concur_history_relations.thy:904 *)
  Lemma ef_val_then_pre pre val empty ia ra :
    WellformedHistory (non_empty_pre pre empty) val →
    elim_free_val (non_empty_pre pre empty) val ia ra →
    pre ia ra.
  Proof.
    intros Hwf (Hefia & Hefra & Hval).
    destruct Hefra as (d & Hsvra & Hprecra).
    destruct Hsvra as [Hrad|Hdra].
    - (* ra is push - contradiction with val_order *)
      exfalso. eapply def_val_order; first exact Hval.
      exists d. right. done.
    - (* d is push, ra is pop *)
      pose proof (def_push_once _ _ _ Hdra Hval) as Heq. subst d.
      destruct Hprecra as [(Hpre & Hnera & Hneia)|(Hpre & Hneia & Hnera)].
      + (* pre ra ia - contradiction with val_then_not_pr *)
        exfalso. eapply def_val_then_not_pr; first exact Hval.
        split; last split; done.
      + (* pre ia ra - correct! *)
        done.
  Qed.

  (* concur_history_relations.thy:915 *)
  Lemma elim_ef_rem_then_rem pre val ir ra rb :
    rem_order (elim_free_pre pre val) (elim_free_val pre val) (elim_free_ir pre val ir) ra rb →
    WellformedHistory pre val →
    rem_order pre val ir ra rb.
  Proof.
    intros (Hpopa & Hpopb & Horder) Hwf.
    split; last split.
    - destruct Hpopa as [c (Hefc & Hefra & Hcra)]. exists c. done.
    - destruct Hpopb as [c (Hefc & Hefrb & Hcrb)]. exists c. done.
    - destruct Horder as [(Hefra & Hefrb & Hab)|(c & (Hefra & Hefc & Hrac) & (Hefc' & Hefrb & Hcb))].
      + left. done.
      + right. exists c. done.
  Qed.

  (* concur_history_relations.thy:933 *)
  Lemma empty_rem_then_rem pre val empty ir ra rb :
    rem_order (non_empty_pre pre empty) val ir ra rb →
    WellformedHistory (non_empty_pre pre empty) val →
    rem_order pre val ir ra rb.
  Proof.
    intros (Hpopa & Hpopb & Horder) Hwf.
    split; last split; try done.
    destruct Horder as [(Hab & _ & _)|(c & Hrac & Hcb)].
    - left. done.
    - right. exists c. done.
  Qed.
End def.

