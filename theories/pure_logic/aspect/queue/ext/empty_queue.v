(* empty_queue.v *)
(* Handling empty-returning dequeue operations *)
(* Adapts empty_stack.v for queues with FIFO semantics *)

From stdpp Require Import finite.
From iris_logatom.pure_logic.aspect.queue.ext Require Import conc_his_rel.

Section empty_queue.
  Context `{abstract_queue_model}.
  Implicit Types (pre val slin elin : relation operation) (empty : operation → Prop).

  (* ConcurrentEmptyQueue locale *)
  Class ConcurrentEmptyQueue pre val empty slin elin := {
    #[local] ceq_wellformed :: WellformedEmptyHistory pre val empty;
    ceq_queue_linearizable : SequentialQueue slin val;
    ceq_pr_in_slin : ∀ a b, pre a b → ¬ empty a → ¬ empty b → slin a b;
    ceq_set_linearizable : SequentialEmptySet elin val empty;
    ceq_pr_in_elin : ∀ a b, pre a b → elin a b;
  }.

  Section wellformed_empty_history_context.
    Context pre val empty `{!WellformedEmptyHistory pre val empty}.

    Lemma concurrent_empty_queueI slin elin :
      SequentialQueue slin val →
      (∀ a b, pre a b → ¬ empty a → ¬ empty b → slin a b) →
      SequentialEmptySet elin val empty →
      (∀ a b, pre a b → elin a b) →
      ConcurrentEmptyQueue pre val empty slin elin.
    Proof.
      intros Hqueue Hpr_slin Hset Hpr_elin.
      constructor; done.
    Qed.

  End wellformed_empty_history_context.

  Section concurrent_empty_queue_context.
    Context pre val empty slin elin `{!ConcurrentEmptyQueue pre val empty slin elin}.
    Context `{∀ a, Decision (empty a), !RelDecision slin, !RelDecision elin}.

    Lemma slin_transitive : Transitive slin.
    Proof.
      destruct ceq_queue_linearizable as [Hseqset _].
      destruct Hseqset as [Hwf _ _ _].
      destruct Hwf. assumption.
    Qed.

    Lemma slin_irreflexive : Irreflexive slin.
    Proof.
      destruct ceq_queue_linearizable as [Hseqset _].
      destruct Hseqset as [Hwf _ _ _].
      destruct Hwf. assumption.
    Qed.

    Lemma slin_antisymmetric : Antisymmetric operation (=) slin.
    Proof.
      destruct ceq_queue_linearizable as [Hseqset _].
      destruct Hseqset as [Hwf _ _ _].
      destruct Hwf. assumption.
    Qed.

    Lemma slin_total a b :
      ¬ empty a → ¬ empty b → a = b ∨ slin a b ∨ slin b a.
    Proof.
      intros Hnea Hneb.
      destruct ceq_queue_linearizable as [Hseqset _].
      destruct ceq_wellformed as [_ _ _ _ _ Hapo Henv _].
      destruct (Hapo a) as [Hea|[c Hac]]; first done.
      destruct (Hapo b) as [Heb|[d Hbd]]; first done.
      destruct (decide (a = b)) as [->|Hne]; first by left.
      right.
      assert (Henqa : is_push val a ∨ is_pop val a).
      { destruct Hac as [Hac|Hca]; [left; exists c|right; exists c]; done. }
      assert (Henqb : is_push val b ∨ is_pop val b).
      { destruct Hbd as [Hbd|Hdb]; [left; exists d|right; exists d]; done. }
      destruct Henqa as [Henqa|Hdeqa]; destruct Henqb as [Henqb|Hdeqb].
      - (* a is enqueue, b is enqueue *)
        by destruct (total_on_enqueue a b Henqa Henqb Hne) as [Hab|Hba]; [left|right].
      - (* a is enqueue, b is dequeue *)
        by destruct (total_on_enqueue_dequeue a b Henqa Hdeqb) as [Hab|Hba]; [left|right].
      - (* a is dequeue, b is enqueue *)
        by destruct (total_on_enqueue_dequeue b a Henqb Hdeqa) as [Hba|Hab]; [right|left].
      - (* a is dequeue, b is dequeue *)
        by destruct (total_on_dequeue a b Hdeqa Hdeqb Hne) as [Hab|Hba]; [left|right].
    Qed.

    Lemma val_then_slin a b :
      val a b → slin a b.
    Proof.
      intros Hab.
      destruct ceq_wellformed as [_ _ _ _ _ _ Henv _].
      assert (Hnea : ¬ empty a).
      { intros Hea. destruct (Henv a Hea) as [Hnv _]. apply Hnv. exists b. done. }
      assert (Hneb : ¬ empty b).
      { intros Heb. destruct (Henv b Heb) as [_ Hnv]. apply Hnv. exists a. done. }
      destruct (slin_total a b Hnea Hneb) as [Heq|[Hslin|Hslin]].
      - subst b. exfalso.
        destruct ceq_queue_linearizable as [Hseqset _].
        destruct Hseqset as [Hwf _ _ _].
        eapply def_val_order; first exact Hab.
        exists a. left. done.
      - done.
      - exfalso.
        destruct ceq_queue_linearizable as [Hseqset _].
        destruct Hseqset as [Hwf _ _ _].
        eapply def_val_then_not_pr; done.
    Qed.

    (* FIFO property of slin *)
    Lemma slin_fifo ia ra ib rb :
      val ia ra → val ib rb → slin ia ib → slin ra rb.
    Proof.
      intros Hia Hib Hiab.
      destruct ceq_queue_linearizable as [_ Hfifo].
      unfold sequential_fifo in Hfifo.
      eapply Hfifo; eauto.
    Qed.

    Lemma elin_transitive : Transitive elin.
    Proof.
      destruct ceq_set_linearizable as [Hseh _].
      destruct Hseh as [Hwfeh _].
      destruct Hwfeh. apply pre_transitive.
    Qed.

    Lemma elin_irreflexive : Irreflexive elin.
    Proof.
      destruct ceq_set_linearizable as [Hseh _].
      destruct Hseh as [Hwfeh _].
      destruct Hwfeh. apply pre_irreflexive.
    Qed.

    Lemma elin_antisymmetric : Antisymmetric operation (=) elin.
    Proof.
      destruct ceq_set_linearizable as [Hseh _].
      destruct Hseh as [Hwfeh _].
      destruct Hwfeh. apply pre_antisymmetric.
    Qed.

    Lemma elin_total a b :
      a = b ∨ elin a b ∨ elin b a.
    Proof.
      destruct ceq_set_linearizable as [Hseh _].
      destruct Hseh as [_ Htri].
      destruct (Htri a b) as [Hab|[Heq|Hba]].
      - right. left. done.
      - left. done.
      - right. right. done.
    Qed.

    Lemma elin_correct_empty a ib rb :
      empty a → val ib rb →
      (elin ib a ∧ elin rb a) ∨ (elin a ib ∧ elin a rb).
    Proof.
      intros Hea Hval.
      destruct ceq_set_linearizable as [_ Hcorrect].
      unfold correct_empty in Hcorrect.
      apply Hcorrect; done.
    Qed.

    (* w1: witness that two operations are separated by an empty-returning dequeue *)
    Definition w1 : relation operation :=
      λ a b, ¬ empty a ∧ ¬ empty b ∧ ∃ c, empty c ∧ elin a c ∧ elin c b.

    Lemma w1D a b :
      w1 a b → ¬ empty a ∧ ¬ empty b ∧ ∃ c, empty c ∧ elin a c ∧ elin c b.
    Proof. done. Qed.

    Local Instance w1_dec : RelDecision w1.
    Proof. intros a b. unfold w1. apply _. Qed.

    Lemma w1I a b c :
      ¬ empty a → ¬ empty b → empty c → elin a c → elin c b → w1 a b.
    Proof.
      intros Hnea Hneb Hec Hac Hcb.
      split; last split; try done.
      exists c. done.
    Qed.

    Lemma w1_transitive : Transitive w1.
    Proof.
      intros a b c (Hnea & Hneb & d & Hed & Had & Hdb) (Hneb' & Hnec & e & Hee & Hbe & Hec).
      split; last split; try done.
      exists d. split; first done.
      split; first done.
      eapply elin_transitive; first exact Hdb.
      eapply elin_transitive; eauto.
    Qed.

    Lemma w1_antisymmetric : Antisymmetric operation (=) w1.
    Proof.
      intros a b Hab Hba.
      apply w1D in Hab as (Hnea & Hneb & c & Hec & Hac & Hcb).
      apply w1D in Hba as (_ & _ & d & Hed & Hbd & Hda).
      assert (elin a a) as Haa.
      { eapply elin_transitive; first exact Hac.
        eapply elin_transitive; first exact Hcb.
        eapply elin_transitive; eauto. }
      exfalso. by eapply elin_irreflexive.
    Qed.

    Lemma w1_irreflexive : Irreflexive w1.
    Proof.
      intros a (Hnea & Hnea' & c & Hec & Hac & Hca).
      assert (elin a a) as Haa by (eapply elin_transitive; eauto).
      by eapply elin_irreflexive.
    Qed.

    Lemma val_then_not_w1 a b :
      val a b → ¬ w1 a b ∧ ¬ w1 b a.
    Proof.
      intros Hab.
      split.
      - intros Hw1.
        apply w1D in Hw1 as (Hnea & Hneb & c & Hec & Hac & Hcb).
        destruct (elin_correct_empty c a b Hec Hab) as [[Hac' Hbc]|[Hca Hcb']].
        + assert (Heq : c = b) by (eapply elin_antisymmetric; done).
          subst c. done.
        + assert (Heq : a = c) by (eapply elin_antisymmetric; done).
          subst c. done.
      - intros Hw1.
        apply w1D in Hw1 as (Hneb & Hnea & d & Hed & Hbd & Hda).
        destruct (elin_correct_empty d a b Hed Hab) as [[Had Hbd']|[Hda' Hdb]].
        + assert (Heq : a = d) by (eapply elin_antisymmetric; done).
          subst d. done.
        + assert (Heq : b = d) by (eapply elin_antisymmetric; done).
          subst d. done.
    Qed.

    Lemma not_w1_then_same_with_empty a b c :
      ¬ w1 a b → ¬ w1 b a → ¬ empty a → ¬ empty b → empty c →
      elin a c → elin b c.
    Proof.
      intros Hnab Hnba Hnea Hneb Hec Hac.
      destruct (elin_total b c) as [Heq|[Hbc|Hcb]].
      - subst c. done.
      - done.
      - exfalso. apply Hnab. eapply w1I; done.
    Qed.

    (* The witness relation for the full linearization including empty operations *)
    Definition witness : relation operation :=
      λ a b, (empty a ∧ elin a b) ∨
             (empty b ∧ elin a b) ∨
             w1 a b ∨
             (¬ empty a ∧ ¬ empty b ∧ ¬ w1 a b ∧ ¬ w1 b a ∧ slin a b).

    Lemma witnessD a b :
      witness a b →
      (empty a ∧ elin a b) ∨
      (empty b ∧ elin a b) ∨
      w1 a b ∨
      (¬ empty a ∧ ¬ empty b ∧ ¬ w1 a b ∧ ¬ w1 b a ∧ slin a b).
    Proof. done. Qed.

    Lemma witnessI1 a b :
      empty a → elin a b → witness a b.
    Proof. intros Hea Hab. left. done. Qed.

    Lemma witnessI2 a b :
      empty b → elin a b → witness a b.
    Proof. intros Heb Hab. right. left. done. Qed.

    Lemma witnessI3 a b :
      w1 a b → witness a b.
    Proof. intros Hw1. right. right. left. done. Qed.

    Lemma witnessI4 a b :
      ¬ empty a → ¬ empty b → ¬ w1 a b → ¬ w1 b a → slin a b → witness a b.
    Proof. intros Hnea Hneb Hnw1ab Hnw1ba Hslin. right. right. right. done. Qed.

    Lemma pr_in_witness : subrelation pre witness.
    Proof.
      intros a b Hpre.
      destruct (decide (empty a)) as [Hea|Hnea].
      - apply witnessI1; first done. by apply ceq_pr_in_elin.
      - destruct (decide (empty b)) as [Heb|Hneb].
        + apply witnessI2; first done. by apply ceq_pr_in_elin.
        + destruct (decide (w1 a b)) as [Hw1|Hnw1].
          * by apply witnessI3.
          * apply witnessI4; try done.
            -- intros Hw1ba.
               apply w1D in Hw1ba as (_ & _ & c & Hec & Hbc & Hca).
               assert (elin a b) as Hab by (by apply ceq_pr_in_elin).
               assert (elin a a) as Haa.
               { eapply elin_transitive; first exact Hab.
                 eapply elin_transitive; eauto. }
               by eapply elin_irreflexive.
            -- by apply ceq_pr_in_slin.
    Qed.

    Lemma witness_transitive : Transitive witness.
    Proof.
      intros a b c Hab Hbc.
      apply witnessD in Hab.
      apply witnessD in Hbc.
      destruct Hab as [[Hea Hab]|[[Heb1 Hab]|[Hw1ab|Hab4]]].
      - (* Case 1: empty a ∧ elin a b *)
        destruct Hbc as [[Heb Hbc]|[[Hec Hbc]|[Hw1bc|Hbc4]]].
        + (* 1.1: empty b ∧ elin b c *)
          apply witnessI1; first done. eapply elin_transitive; eauto.
        + (* 1.2: empty c ∧ elin b c *)
          apply witnessI1; first done. eapply elin_transitive; eauto.
        + (* 1.3: w1 b c *)
          apply w1D in Hw1bc as (Hneb & Hnec & d & Hed & Hbd & Hdc).
          apply witnessI1; first done. eapply elin_transitive; first exact Hab.
          eapply elin_transitive; eauto.
        + (* 1.4: ¬ empty b ∧ ¬ empty c ∧ ... ∧ slin b c *)
          destruct Hbc4 as (Hneb & Hnec & Hnw1bc & Hnw1cb & Hslinbc).
          (* Use elin_total to get elin a c relationship *)
          destruct (elin_total a c) as [Heq|[Hac|Hca]].
          * subst c. apply witnessI1; done.
          * apply witnessI1; done.
          * (* elin c a case *)
            destruct (elin_total b c) as [Heqbc|[Hbcelin|Hcbelin]].
            -- subst c. apply witnessI1; done.
            -- apply witnessI1; first done. eapply elin_transitive; eauto.
            -- (* In this case, we have elin c a and elin c b. *)
               (* We construct w1 c b using a as the empty witness. *)
               (* Since ¬ w1 c b (from Hnw1cb), we get a contradiction. *)
               exfalso. apply Hnw1cb. eapply w1I; try done.
      - (* Case 2: empty b ∧ elin a b *)
        destruct Hbc as [[Heb' Hbc]|[[Hec Hbc]|[Hw1bc|Hbc4]]].
        + (* 2.1: empty b ∧ elin b c - need to figure out witness a c *)
          assert (Hacelin : elin a c) by (eapply elin_transitive; eauto).
          destruct (decide (empty a)) as [Hea|Hnea].
          * apply witnessI1; done.
          * destruct (decide (empty c)) as [Hec'|Hnec].
            -- apply witnessI2; done.
            -- (* a and c are non-empty, b is empty, construct w1 a c *)
               apply witnessI3. eapply (w1I a c b); done.
        + (* 2.2: empty c ∧ elin b c *)
          apply witnessI2; first done. eapply elin_transitive; eauto.
        + (* w1 b c but empty b - contradiction *)
          apply w1D in Hw1bc as (Hneb & _ & _). done.
        + destruct Hbc4 as (Hneb & _ & _ & _ & _). done.
      - (* Case 3: w1 a b *)
        apply w1D in Hw1ab as (Hnea & Hneb & d & Hed & Had & Hdb).
        destruct Hbc as [[Heb Hbc]|[[Hec Hbc]|[Hw1bc|Hbc4]]].
        + (* 3.1: empty b - contradiction with w1 a b *)
          done.
        + (* 3.2: empty c ∧ elin b c *)
          apply witnessI2; first done. eapply elin_transitive; first exact Had.
          eapply elin_transitive; eauto.
        + (* 3.3: w1 b c *)
          apply witnessI3. eapply w1_transitive.
          * eapply w1I; [done|done|done|done|done].
          * done.
        + (* 3.4: ¬ empty b ∧ ¬ empty c ∧ ... ∧ slin b c *)
          destruct Hbc4 as (Hneb' & Hnec & Hnw1bc & Hnw1cb & Hslin).
          (* We have w1 a b with witness d: empty d, elin a d, elin d b *)
          (* Want w1 a c, need witness e with empty e, elin a e, elin e c *)
          (* Use d as witness, need elin d c *)
          apply witnessI3.
          destruct (elin_total b d) as [Heqbd|[Hbd|Hdb']].
          * (* b = d contradicts empty d and ¬ empty b *)
            subst d. done.
          * (* elin b d - can use not_w1_then_same_with_empty *)
            assert (elin c d) as Hcd by (eapply not_w1_then_same_with_empty; try done).
            destruct (elin_total d c) as [Heqdc|[Hdc|Hcd']].
            -- subst c. done.
            -- (* elin d c - but we also have elin c d, so c = d, contradiction *)
               exfalso. assert (c = d) by (eapply elin_antisymmetric; done). subst d. done.
            -- (* elin c d - same as Hcd, need elin d c to construct w1 *)
               (* Actually, we can construct w1 c b using elin c d and elin d b *)
               (* But ¬ w1 c b, so this gives contradiction *)
               exfalso. apply Hnw1cb. eapply w1I; [done|done|done|done|done].
          * (* elin d b - same as Hdb, can't directly apply the lemma *)
            (* Try elin_total d c *)
            destruct (elin_total d c) as [Heqdc|[Hdc|Hcd]].
            -- (* d = c contradicts empty d and ¬ empty c *)
               subst c. done.
            -- eapply w1I; [done|done|done|done|done].
            -- (* elin c d *)
               (* We have elin d b and elin c d, so elin c b by transitivity *)
               (* This gives us w1 c b with witness d: elin c d, elin d b *)
               (* But ¬ w1 c b contradicts this! *)
               exfalso. apply Hnw1cb. eapply w1I; [done|done|done|done|done].
      - (* Case 4: ¬ empty a ∧ ¬ empty b ∧ ¬ w1 a b ∧ ¬ w1 b a ∧ slin a b *)
        destruct Hab4 as (Hnea & Hneb & Hnw1ab & Hnw1ba & Hslinab).
        destruct Hbc as [[Heb Hbc]|[[Hec Hbc]|[Hw1bc|Hbc4]]].
        + (* 4.1: empty b - contradiction *)
          done.
        + (* 4.2: empty c ∧ elin b c *)
          apply witnessI2; first done.
          eapply not_w1_then_same_with_empty; try done.
        + (* 4.3: w1 b c *)
          apply w1D in Hw1bc as (Hneb' & Hnec & d & Hed & Hbd & Hdc).
          apply witnessI3.
          assert (elin a d) as Had by (eapply not_w1_then_same_with_empty; try done).
          eapply w1I; try done.
        + (* 4.4: ¬ empty b ∧ ¬ empty c ∧ ... ∧ slin b c *)
          destruct Hbc4 as (Hneb' & Hnec & Hnw1bc & Hnw1cb & Hslinbc).
          destruct (decide (w1 a c)) as [Hw1ac|Hnw1ac].
          * by apply witnessI3.
          * destruct (decide (w1 c a)) as [Hw1ca|Hnw1ca].
            -- (* w1 c a: derive contradiction *)
               apply w1D in Hw1ca as (_ & _ & d & Hed & Hcd & Hda).
               (* Get elin b d using not_w1_then_same_with_empty *)
               assert (elin b d) as Hbd by (eapply not_w1_then_same_with_empty; try done).
               (* Now we have elin b d and elin d a, so w1 b a holds *)
               (* But ¬ w1 b a, contradiction! *)
               exfalso. apply Hnw1ba. eapply w1I; [done|done|done|done|done].
            -- apply witnessI4; try done.
               eapply slin_transitive; eauto.
    Qed.

    Lemma witness_irreflexive : Irreflexive witness.
    Proof.
      intros a Hw.
      destruct Hw as [[Hea Haa]|[[Hea Haa]|[Hw1|Hlast]]].
      - by eapply elin_irreflexive.
      - by eapply elin_irreflexive.
      - by eapply w1_irreflexive.
      - destruct Hlast as (? & ? & ? & ? & Hslin). by eapply slin_irreflexive.
    Qed.

    Lemma witness_antisymmetric : Antisymmetric operation (=) witness.
    Proof.
      intros a b Hab Hba.
      pose proof (witness_transitive a b a Hab Hba) as Haa.
      exfalso. by eapply witness_irreflexive.
    Qed.

    Lemma witness_trichotomy : Trichotomy witness.
    Proof.
      intros a b.
      (* Use trichotomy of elin *)
      destruct (elin_total a b) as [Heq|[Hab|Hba]].
      - (* a = b *) right. left. done.
      - (* elin a b *)
        destruct (decide (empty a)) as [Hea|Hnea].
        + (* empty a *) left. by apply witnessI1.
        + destruct (decide (empty b)) as [Heb|Hneb].
          * (* empty b *) left. by apply witnessI2.
          * (* ¬ empty a, ¬ empty b - use slin trichotomy *)
            destruct (slin_total a b Hnea Hneb) as [Heq'|[Hsab|Hsba]].
            -- right. left. done.
            -- (* slin a b *)
               destruct (decide (w1 a b)) as [Hw1|Hnw1].
               ++ left. by apply witnessI3.
               ++ destruct (decide (w1 b a)) as [Hw1'|Hnw1'].
                  ** right. right. by apply witnessI3.
                  ** left. by apply witnessI4.
            -- (* slin b a *)
               destruct (decide (w1 b a)) as [Hw1|Hnw1].
               ++ right. right. by apply witnessI3.
               ++ destruct (decide (w1 a b)) as [Hw1'|Hnw1'].
                  ** left. by apply witnessI3.
                  ** right. right. by apply witnessI4.
      - (* elin b a *)
        destruct (decide (empty b)) as [Heb|Hneb].
        + (* empty b *) right. right. by apply witnessI1.
        + destruct (decide (empty a)) as [Hea|Hnea].
          * (* empty a *) right. right. by apply witnessI2.
          * (* ¬ empty a, ¬ empty b - use slin trichotomy *)
            destruct (slin_total a b Hnea Hneb) as [Heq'|[Hsab|Hsba]].
            -- right. left. done.
            -- (* slin a b *)
               destruct (decide (w1 a b)) as [Hw1|Hnw1].
               ++ left. by apply witnessI3.
               ++ destruct (decide (w1 b a)) as [Hw1'|Hnw1'].
                  ** right. right. by apply witnessI3.
                  ** left. by apply witnessI4.
            -- (* slin b a *)
               destruct (decide (w1 b a)) as [Hw1|Hnw1].
               ++ right. right. by apply witnessI3.
               ++ destruct (decide (w1 a b)) as [Hw1'|Hnw1'].
                  ** left. by apply witnessI3.
                  ** right. right. by apply witnessI4.
    Qed.

    Lemma witness_correct_empty a ib rb :
      empty a → val ib rb →
      (witness ib a ∧ witness rb a) ∨ (witness a ib ∧ witness a rb).
    Proof.
      intros Hea Hval.
      destruct (elin_correct_empty a ib rb Hea Hval) as [[Hib_a Hrb_a]|[Ha_ib Ha_rb]].
      - left. split; by apply witnessI2.
      - right. split; by apply witnessI1.
    Qed.

    Lemma val_then_not_witness ia ra :
      val ia ra → ¬ witness ra ia.
    Proof.
      intros Hval Hw.
      apply witnessD in Hw.
      destruct ceq_wellformed as [_ _ _ _ _ _ Henv _].
      assert (Hneia : ¬ empty ia).
      { intros Heia. destruct (Henv ia Heia) as [Hnv _]. apply Hnv. exists ra. done. }
      assert (Hnera : ¬ empty ra).
      { intros Hera. destruct (Henv ra Hera) as [_ Hnv]. apply Hnv. exists ia. done. }
      destruct Hw as [[Hera Hrain]|[[Heia Hrain]|[Hw1|Hlast]]].
      - done.
      - done.
      - destruct (val_then_not_w1 ia ra Hval) as [_ Hnw1]. done.
      - destruct Hlast as (_ & _ & _ & _ & Hslinra).
        pose proof (val_then_slin ia ra Hval) as Hslinia.
        assert (ra = ia) by (eapply slin_antisymmetric; done).
        subst ra. by eapply slin_irreflexive.
    Qed.

    (* FIFO property of witness *)
    Lemma witness_fifo ia ra ib rb :
      val ia ra → val ib rb → witness ia ib → witness ra rb.
    Proof.
      intros Hvalia Hvalib Hiaib.
      apply witnessD in Hiaib.
      destruct ceq_wellformed as [_ _ _ _ _ _ Henv _].
      (* ia, ra, ib, rb are not empty since they participate in val *)
      assert (Hneia : ¬ empty ia).
      { intros Heia. destruct (Henv ia Heia) as [Hnv _]. apply Hnv. exists ra. done. }
      assert (Hnera : ¬ empty ra).
      { intros Hera. destruct (Henv ra Hera) as [_ Hnv]. apply Hnv. exists ia. done. }
      assert (Hneib : ¬ empty ib).
      { intros Heib. destruct (Henv ib Heib) as [Hnv _]. apply Hnv. exists rb. done. }
      assert (Hnerb : ¬ empty rb).
      { intros Herb. destruct (Henv rb Herb) as [_ Hnv]. apply Hnv. exists ib. done. }
      destruct Hiaib as [[Heia _]|[[Heib _]|[Hw1iaib|Hiaib4]]].
      - (* empty ia - contradiction *) done.
      - (* empty ib - contradiction *) done.
      - (* w1 ia ib *)
        apply w1D in Hw1iaib as (_ & _ & c & Hec & Hiac & Hcib).
        (* Use elin_correct_empty to relate c to (ia, ra) and (ib, rb) *)
        destruct (elin_correct_empty c ia ra Hec Hvalia) as [[Hiac' Hrac]|[Hcia Hcra]].
        + (* elin ia c ∧ elin ra c *)
          destruct (elin_correct_empty c ib rb Hec Hvalib) as [[Hibc Hrbc]|[Hcib' Hcrb]].
          * (* elin ib c ∧ elin rb c - contradiction: c = ib *)
            assert (c = ib) by (eapply elin_antisymmetric; done). subst c. done.
          * (* elin c ib ∧ elin c rb - construct w1 ra rb *)
            apply witnessI3. eapply w1I; [done|done|done|done|done].
        + (* elin c ia ∧ elin c ra - contradiction: ia = c *)
          assert (ia = c) by (eapply elin_antisymmetric; done). subst c. done.
      - (* ¬ empty ia ∧ ¬ empty ib ∧ ¬ w1 ia ib ∧ ¬ w1 ib ia ∧ slin ia ib *)
        destruct Hiaib4 as (_ & _ & Hnw1iaib & Hnw1ibia & Hsliaib).
        (* Use slin_fifo to get slin ra rb *)
        pose proof (slin_fifo ia ra ib rb Hvalia Hvalib Hsliaib) as Hslrarb.
        (* Now show ¬ w1 ra rb and ¬ w1 rb ra *)
        assert (Hnw1rarb : ¬ w1 ra rb).
        { intros Hw1.
          apply w1D in Hw1 as (_ & _ & c & Hec & Hrac & Hcrb).
          destruct (elin_correct_empty c ia ra Hec Hvalia) as [[Hiac Hrac']|[Hcia Hcra]].
          - (* elin ia c ∧ elin ra c *)
            destruct (elin_correct_empty c ib rb Hec Hvalib) as [[Hibc Hrbc]|[Hcib Hcrb']].
            + (* elin ib c ∧ elin rb c - contradiction: c = rb *)
              assert (c = rb) by (eapply elin_antisymmetric; done). subst c. done.
            + (* elin c ib ∧ elin c rb - this gives w1 ia ib, contradiction *)
              apply Hnw1iaib. eapply w1I; [done|done|done|done|done].
          - (* elin c ia ∧ elin c ra - contradiction: ra = c *)
            assert (ra = c) by (eapply elin_antisymmetric; done). subst c. done. }
        assert (Hnw1rbra : ¬ w1 rb ra).
        { intros Hw1.
          apply w1D in Hw1 as (_ & _ & c & Hec & Hrbc & Hcra).
          destruct (elin_correct_empty c ib rb Hec Hvalib) as [[Hibc Hrbc']|[Hcib Hcrb]].
          - (* elin ib c ∧ elin rb c *)
            destruct (elin_correct_empty c ia ra Hec Hvalia) as [[Hiac Hrac]|[Hcia Hcra']].
            + (* elin ia c ∧ elin ra c - contradiction: c = ra *)
              assert (c = ra) by (eapply elin_antisymmetric; done). subst c. done.
            + (* elin c ia ∧ elin c ra - this gives w1 ib ia, contradiction *)
              apply Hnw1ibia. eapply w1I; [done|done|done|done|done].
          - (* elin c ib ∧ elin c rb - contradiction: rb = c *)
            assert (rb = c) by (eapply elin_antisymmetric; done). subst c. done. }
        apply witnessI4; done.
    Qed.

    Local Instance witness_dec : RelDecision witness.
    Proof. intros a b. unfold witness. apply _. Qed.

    Lemma witness_sequential_empty_queue : SequentialEmptyQueue witness val empty.
    Proof.
      constructor.
      - (* SequentialEmptySet witness val empty *)
        constructor.
        + (* SequentialEmptyHistory witness val empty *)
          constructor.
          * (* WellformedEmptyHistory witness val empty *)
            destruct ceq_wellformed as [Hch Hfin Henqo Hdeqo Hvo Hapo Hetn Hvtnp].
            constructor.
            -- (* ConcHistory witness *)
               constructor.
               ++ apply witness_transitive.
               ++ apply witness_antisymmetric.
               ++ apply witness_irreflexive.
               ++ apply lem_trichotomy_then_abcd; [apply witness_trichotomy | apply witness_transitive].
            -- done.
            -- done.
            -- done.
            -- done.
            -- done.
            -- done.
            -- intros a b Hval Hw.
               by eapply val_then_not_witness.
          * apply witness_trichotomy.
        + intros a Hea ib rb Hval.
          by apply witness_correct_empty.
      - (* sequential_fifo witness val *)
        intros ia ib ra rb Hvalia Hvalib Hiaib.
        by eapply witness_fifo.
    Qed.

    Theorem concurrent_empty_queue_linearizable :
      ∃ prt (_ : RelDecision prt), subrelation pre prt ∧ SequentialEmptyQueue prt val empty.
    Proof.
      exists witness, _. split.
      - apply pr_in_witness.
      - apply witness_sequential_empty_queue.
    Qed.

  End concurrent_empty_queue_context.

  (* Final assembly lemma *)
  Lemma queue_set_then_set pre val empty :
    linearizable_non_empty_queue (non_empty_pre pre empty) val →
    linearizable_set pre val empty →
    ∃ elin slin (_ : RelDecision elin) (_ : RelDecision slin),
      ConcurrentEmptyQueue pre val empty slin elin.
  Proof.
    intros [Hch_ne (slin & Hslin_dec & Hsub_slin & Hslin)]
      [Hch_pre (elin & Helin_dec & Hsub_elin & Hselin)].
    exists elin, slin, _, _.
    destruct Hselin as [Hselin_seh Hselin_ce].
    destruct Hselin_seh as [Hselin_weh Hselin_total].
    destruct Hselin_weh as [Hch_elin Hfin_elin Henqo_elin Hdeqo_elin Hvo_elin Hapo Hetn Hvtnp_elin].
    destruct Hslin as [Hslin_ss Hslin_fifo].
    destruct Hslin_ss as [Hslin_wh Htotenq Htotdeq Htoted].
    destruct Hslin_wh as [Hch_slin Henqo_slin Hdeqo_slin Hvo_slin Henqdeq_slin Hvtnp_slin].
    constructor.
    - (* ceq_wellformed : WellformedEmptyHistory pre val empty *)
      constructor; try done.
      intros a b Hval Hpre.
      apply (Hvtnp_elin a b Hval).
      by apply Hsub_elin.
    - (* ceq_queue_linearizable : SequentialQueue slin val *)
      constructor.
      + constructor; done.
      + done.
    - (* ceq_pr_in_slin *)
      intros a b Hpre Hnea Hneb.
      apply Hsub_slin.
      unfold non_empty_pre. done.
    - (* ceq_set_linearizable : SequentialEmptySet elin val empty *)
      constructor.
      + (* SequentialEmptyHistory *)
        constructor.
        * (* WellformedEmptyHistory *)
          constructor; done.
        * (* Trichotomy *)
          done.
      + (* correct_empty *)
        done.
    - (* ceq_pr_in_elin *)
      intros a b Hpre.
      by apply Hsub_elin.
  Qed.

  Theorem concurrent_empty_queue_linearizable_main pre val empty `{∀ a, Decision (empty a)} :
    linearizable_non_empty_queue (non_empty_pre pre empty) val →
    linearizable_set pre val empty →
    linearizable_queue pre val empty.
  Proof.
    intros Hne Hls.
    destruct (queue_set_then_set pre val empty Hne Hls)
      as (elin & slin & Helin_dec & Hslin_dec & Hceq).
    unfold linearizable_queue.
    split.
    - destruct Hls as [Hch _]. done.
    - destruct (concurrent_empty_queue_linearizable pre val empty slin elin)
        as (prt & Hprt_dec & Hsub & Hseq).
      exists prt, _. done.
  Qed.

End empty_queue.
