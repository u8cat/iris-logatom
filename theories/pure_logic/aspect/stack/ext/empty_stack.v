(* empty_stack.v, ported from empty_stack.thy *)

From Stdlib Require Import Classical.
From iris_logatom.pure_logic.aspect.stack.ext Require Import conc_his_rel.

Section empty_stack.
  Context `{abstract_stack_model}.
  Implicit Types (pre val slin elin : relation operation) (empty : operation → Prop).

  (* empty_stack.thy:5-11 - concurrent_empty_stack locale *)
  Class ConcurrentEmptyStack pre val empty slin elin := {
    #[local] ces_wellformed :: WellformedEmptyHistory pre val empty;
    ces_stack_linearizable : SequentialStack slin val;
    ces_pr_in_slin : ∀ a b, pre a b → ¬ empty a → ¬ empty b → slin a b;
    ces_set_linearizable : SequentialEmptySet elin val empty;
    ces_pr_in_elin : ∀ a b, pre a b → elin a b;
  }.

  Section wellformed_empty_history_context.
    Context pre val empty `{!WellformedEmptyHistory pre val empty}.

    (* empty_stack.thy:16-30 - concurrent_empty_stackI *)
    Lemma concurrent_empty_stackI slin elin :
      SequentialStack slin val →
      (∀ a b, pre a b → ¬ empty a → ¬ empty b → slin a b) →
      SequentialEmptySet elin val empty →
      (∀ a b, pre a b → elin a b) →
      ConcurrentEmptyStack pre val empty slin elin.
    Proof.
      intros Hstack Hpr_slin Hset Hpr_elin.
      constructor; done.
    Qed.

  End wellformed_empty_history_context.

  Section concurrent_empty_stack_context.
    Context pre val empty slin elin `{!ConcurrentEmptyStack pre val empty slin elin}.

    (* empty_stack.thy:37-45 *)
    Lemma slin_transitive : Transitive slin.
    Proof.
      destruct ces_stack_linearizable as [Hseqset _].
      destruct Hseqset as [Hwf _ _ _].
      destruct Hwf. assumption.
    Qed.

    (* empty_stack.thy:47-55 *)
    Lemma slin_irreflexive : Irreflexive slin.
    Proof.
      destruct ces_stack_linearizable as [Hseqset _].
      destruct Hseqset as [Hwf _ _ _].
      destruct Hwf. assumption.
    Qed.

    (* empty_stack.thy:57-66 *)
    Lemma slin_antisymmetric : Antisymmetric operation (=) slin.
    Proof.
      destruct ces_stack_linearizable as [Hseqset _].
      destruct Hseqset as [Hwf _ _ _].
      destruct Hwf. assumption.
    Qed.

    (* empty_stack.thy:68-75 *)
    Lemma slin_total a b :
      ¬ empty a → ¬ empty b → a = b ∨ slin a b ∨ slin b a.
    Proof.
      intros Hnea Hneb.
      destruct ces_stack_linearizable as [Hseqset _].
      (* From WellformedEmptyHistory, non-empty operations are pushes or pops *)
      destruct ces_wellformed as [_ _ _ _ _ Hapo Henv _].
      destruct (Hapo a) as [Hea|[c Hac]]; first done.
      destruct (Hapo b) as [Heb|[d Hbd]]; first done.
      destruct (decide (a = b)) as [->|Hne]; first by left.
      right.
      (* Now we case split on whether a and b are pushes or pops *)
      assert (Hpusha : is_push val a ∨ is_pop val a).
      { destruct Hac as [Hac|Hca]; [left; exists c|right; exists c]; done. }
      assert (Hpushb : is_push val b ∨ is_pop val b).
      { destruct Hbd as [Hbd|Hdb]; [left; exists d|right; exists d]; done. }
      destruct Hpusha as [Hpusha|Hpopa]; destruct Hpushb as [Hpushb|Hpopb].
      - (* a is push, b is push *)
        by destruct (total_on_push a b Hpusha Hpushb Hne) as [Hab|Hba]; [left|right].
      - (* a is push, b is pop *)
        by destruct (total_on_push_pop a b Hpusha Hpopb) as [Hab|Hba]; [left|right].
      - (* a is pop, b is push *)
        by destruct (total_on_push_pop b a Hpushb Hpopa) as [Hba|Hab]; [right|left].
      - (* a is pop, b is pop *)
        by destruct (total_on_pop a b Hpopa Hpopb Hne) as [Hab|Hba]; [left|right].
    Qed.

    (* empty_stack.thy:77-85 *)
    Lemma val_then_slin a b :
      val a b → slin a b.
    Proof.
      intros Hab.
      (* From WellformedEmptyHistory, val implies not empty *)
      destruct ces_wellformed as [_ _ _ _ _ _ Henv _].
      assert (Hnea : ¬ empty a).
      { intros Hea. destruct (Henv a Hea) as [Hnv _]. apply Hnv. exists b. done. }
      assert (Hneb : ¬ empty b).
      { intros Heb. destruct (Henv b Heb) as [_ Hnv]. apply Hnv. exists a. done. }
      (* Use slin_total *)
      destruct (slin_total a b Hnea Hneb) as [Heq|[Hslin|Hslin]].
      - (* a = b contradicts val_order *)
        subst b. exfalso.
        destruct ces_stack_linearizable as [Hseqset _].
        destruct Hseqset as [Hwf _ _ _].
        eapply def_val_order; first exact Hab.
        exists a. left. done.
      - (* slin a b - the goal *)
        done.
      - (* slin b a contradicts val_then_not_pr *)
        exfalso.
        destruct ces_stack_linearizable as [Hseqset _].
        destruct Hseqset as [Hwf _ _ _].
        eapply def_val_then_not_pr; done.
    Qed.

    (* empty_stack.thy:87-93 *)
    Lemma slin_ooo ia ra ib rb :
      val ia ra → val ib rb → slin ia ib → slin ib ra → slin rb ra.
    Proof.
      intros Hia Hib Hiab Hibra.
      destruct ces_stack_linearizable as [_ Hlifo].
      unfold sequential_lifo in Hlifo.
      eapply Hlifo; eauto.
    Qed.

    (* empty_stack.thy:95-101 *)
    Lemma elin_transitive : Transitive elin.
    Proof.
      destruct ces_set_linearizable as [Hseh _].
      destruct Hseh as [Hwfeh _].
      destruct Hwfeh. apply pre_transitive.
    Qed.

    (* empty_stack.thy:104-110 *)
    Lemma elin_irreflexive : Irreflexive elin.
    Proof.
      destruct ces_set_linearizable as [Hseh _].
      destruct Hseh as [Hwfeh _].
      destruct Hwfeh. apply pre_irreflexive.
    Qed.

    (* empty_stack.thy:112-118 *)
    Lemma elin_antisymmetric : Antisymmetric operation (=) elin.
    Proof.
      destruct ces_set_linearizable as [Hseh _].
      destruct Hseh as [Hwfeh _].
      destruct Hwfeh. apply pre_antisymmetric.
    Qed.

    (* empty_stack.thy:120-127 *)
    Lemma elin_total a b :
      a = b ∨ elin a b ∨ elin b a.
    Proof.
      destruct ces_set_linearizable as [Hseh _].
      destruct Hseh as [_ Htri].
      destruct (Htri a b) as [Hab|[Heq|Hba]].
      - right. left. done.
      - left. done.
      - right. right. done.
    Qed.

    (* empty_stack.thy:129-136 *)
    Lemma elin_correct_empty a ib rb :
      empty a → val ib rb →
      (elin ib a ∧ elin rb a) ∨ (elin a ib ∧ elin a rb).
    Proof.
      intros Hea Hval.
      destruct ces_set_linearizable as [_ Hcorrect].
      unfold correct_empty in Hcorrect.
      apply Hcorrect; done.
    Qed.

    (* empty_stack.thy:138-139 - Definition of w1 *)
    Definition w1 : relation operation :=
      λ a b, ¬ empty a ∧ ¬ empty b ∧ ∃ c, empty c ∧ elin a c ∧ elin c b.

    (* empty_stack.thy:141-143 *)
    Lemma w1D a b :
      w1 a b → ¬ empty a ∧ ¬ empty b ∧ ∃ c, empty c ∧ elin a c ∧ elin c b.
    Proof. done. Qed.

    (* empty_stack.thy:145-148 *)
    Lemma w1I a b c :
      ¬ empty a → ¬ empty b → empty c → elin a c → elin c b → w1 a b.
    Proof.
      intros Hnea Hneb Hec Hac Hcb.
      split; last split; try done.
      exists c. done.
    Qed.

    (* empty_stack.thy:150-151 *)
    Lemma w1_transitive : Transitive w1.
    Proof.
      intros a b c (Hnea & Hneb & d & Hed & Had & Hdb) (Hneb' & Hnec & e & Hee & Hbe & Hec).
      split; last split; try done.
      exists d. split; first done.
      split; first done.
      eapply elin_transitive; first exact Hdb.
      eapply elin_transitive; eauto.
    Qed.

    (* empty_stack.thy:153-154 *)
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

    (* empty_stack.thy:156-157 *)
    Lemma w1_irreflexive : Irreflexive w1.
    Proof.
      intros a (Hnea & Hnea' & c & Hec & Hac & Hca).
      assert (elin a a) as Haa by (eapply elin_transitive; eauto).
      by eapply elin_irreflexive.
    Qed.

    (* empty_stack.thy:159-160 *)
    Lemma w1_then_not_inv_pr a b :
      w1 a b → ¬ pre b a.
    Proof.
      intros Hw1 Hpre.
      apply w1D in Hw1 as (Hnea & Hneb & c & Hec & Hac & Hcb).
      assert (elin b a) as Hba by (eapply ces_pr_in_elin; done).
      assert (elin b b) as Hbb.
      { eapply elin_transitive; first exact Hba.
        eapply elin_transitive; eauto. }
      by eapply elin_irreflexive.
    Qed.

    (* empty_stack.thy:162-170 *)
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

    (* empty_stack.thy:172-180 *)
    Lemma val_then_not_w1 a b :
      val a b → ¬ w1 a b ∧ ¬ w1 b a.
    Proof.
      intros Hab.
      split.
      - (* ¬ w1 a b *)
        intros Hw1.
        apply w1D in Hw1 as (Hnea & Hneb & c & Hec & Hac & Hcb).
        destruct (elin_correct_empty c a b Hec Hab) as [[Hac' Hbc]|[Hca Hcb']].
        + (* elin a c ∧ elin b c *)
          (* From elin c b and elin b c, by antisymmetry b = c *)
          assert (Heq : c = b) by (eapply elin_antisymmetric; done).
          subst c. done.
        + (* elin c a ∧ elin c b *)
          (* From elin a c and elin c a, by antisymmetry a = c *)
          assert (Heq : a = c) by (eapply elin_antisymmetric; done).
          subst c. done.
      - (* ¬ w1 b a *)
        intros Hw1.
        apply w1D in Hw1 as (Hneb & Hnea & d & Hed & Hbd & Hda).
        destruct (elin_correct_empty d a b Hed Hab) as [[Had Hbd']|[Hda' Hdb]].
        + (* elin a d ∧ elin b d *)
          (* From elin d a and elin a d, by antisymmetry a = d *)
          assert (Heq : a = d) by (eapply elin_antisymmetric; done).
          subst d. done.
        + (* elin d a ∧ elin d b *)
          (* From elin b d and elin d b, by antisymmetry b = d *)
          assert (Heq : b = d) by (eapply elin_antisymmetric; done).
          subst d. done.
    Qed.

    (* empty_stack.thy:182-183 *)
    Lemma val_then_same_w11 ia ra b :
      val ia ra → w1 b ia → w1 b ra.
    Proof.
      intros Hval Hw1.
      apply w1D in Hw1 as (Hneb & Hneia & c & Hec & Hbc & Hcia).
      destruct ces_wellformed as [_ _ _ _ _ _ Henv _].
      assert (Hnera : ¬ empty ra).
      { intros Hera. destruct (Henv ra Hera) as [_ Hnv]. apply Hnv. exists ia. done. }
      destruct (elin_correct_empty c ia ra Hec Hval) as [[Hiac Hrac]|[Hcia' Hcra]].
      - (* elin ia c ∧ elin ra c - contradiction *)
        exfalso. assert (c = ia) by (eapply elin_antisymmetric; done).
        subst c. done.
      - (* elin c ia ∧ elin c ra - use c as witness *)
        eapply w1I; [done|done|done|done|done].
    Qed.

    (* empty_stack.thy:185-186 *)
    Lemma val_then_same_w12 ia ra b :
      val ia ra → w1 b ra → w1 b ia.
    Proof.
      intros Hval Hw1.
      apply w1D in Hw1 as (Hneb & Hnera & c & Hec & Hbc & Hcra).
      destruct ces_wellformed as [_ _ _ _ _ _ Henv _].
      assert (Hneia : ¬ empty ia).
      { intros Heia. destruct (Henv ia Heia) as [Hnv _]. apply Hnv. exists ra. done. }
      destruct (elin_correct_empty c ia ra Hec Hval) as [[Hiac Hrac]|[Hcia Hcra']].
      - (* elin ia c ∧ elin ra c - contradiction *)
        exfalso. assert (c = ra) by (eapply elin_antisymmetric; done).
        subst c. done.
      - (* elin c ia ∧ elin c ra - use c as witness *)
        eapply w1I; [done|done|done|done|done].
    Qed.

    (* empty_stack.thy:188-189 *)
    Lemma val_then_same_w13 ia ra b :
      val ia ra → w1 ia b → w1 ra b.
    Proof.
      intros Hval Hw1.
      apply w1D in Hw1 as (Hneia & Hneb & c & Hec & Hiac & Hcb).
      destruct ces_wellformed as [_ _ _ _ _ _ Henv _].
      assert (Hnera : ¬ empty ra).
      { intros Hera. destruct (Henv ra Hera) as [_ Hnv]. apply Hnv. exists ia. done. }
      destruct (elin_correct_empty c ia ra Hec Hval) as [[Hiac' Hrac]|[Hcia Hcra]].
      - (* elin ia c ∧ elin ra c - use c as witness *)
        eapply w1I; [done|done|done|done|done].
      - (* elin c ia ∧ elin c ra - contradiction *)
        exfalso. assert (ia = c) by (eapply elin_antisymmetric; done).
        subst c. done.
    Qed.

    (* empty_stack.thy:191-192 *)
    Lemma val_then_same_w14 ia ra b :
      val ia ra → w1 ra b → w1 ia b.
    Proof.
      intros Hval Hw1.
      apply w1D in Hw1 as (Hnera & Hneb & c & Hec & Hrac & Hcb).
      destruct ces_wellformed as [_ _ _ _ _ _ Henv _].
      assert (Hneia : ¬ empty ia).
      { intros Heia. destruct (Henv ia Heia) as [Hnv _]. apply Hnv. exists ra. done. }
      destruct (elin_correct_empty c ia ra Hec Hval) as [[Hiac Hrac']|[Hcia Hcra]].
      - (* elin ia c ∧ elin ra c - use c as witness *)
        eapply w1I; [done|done|done|done|done].
      - (* elin c ia ∧ elin c ra - contradiction *)
        exfalso. assert (ra = c) by (eapply elin_antisymmetric; done).
        subst c. done.
    Qed.

    (* empty_stack.thy:194-198 - Definition of witness *)
    Definition witness : relation operation :=
      λ a b, (empty a ∧ elin a b) ∨
             (empty b ∧ elin a b) ∨
             w1 a b ∨
             (¬ empty a ∧ ¬ empty b ∧ ¬ w1 a b ∧ ¬ w1 b a ∧ slin a b).

    (* empty_stack.thy:200-205 *)
    Lemma witnessD a b :
      witness a b →
      (empty a ∧ elin a b) ∨
      (empty b ∧ elin a b) ∨
      w1 a b ∨
      (¬ empty a ∧ ¬ empty b ∧ ¬ w1 a b ∧ ¬ w1 b a ∧ slin a b).
    Proof. done. Qed.

    (* empty_stack.thy:207-209 *)
    Lemma witnessI1 a b :
      empty a → elin a b → witness a b.
    Proof. intros Hea Hab. left. done. Qed.

    (* empty_stack.thy:211-213 *)
    Lemma witnessI2 a b :
      empty b → elin a b → witness a b.
    Proof. intros Heb Hab. right. left. done. Qed.

    (* empty_stack.thy:215-217 *)
    Lemma witnessI3 a b :
      w1 a b → witness a b.
    Proof. intros Hw1. right. right. left. done. Qed.

    (* empty_stack.thy:219-221 *)
    Lemma witnessI4 a b :
      ¬ empty a → ¬ empty b → ¬ w1 a b → ¬ w1 b a → slin a b → witness a b.
    Proof. intros Hnea Hneb Hnw1ab Hnw1ba Hslin. right. right. right. done. Qed.

    (* empty_stack.thy:223-232 *)
    Lemma pr_in_witness : subrelation pre witness.
    Proof.
      intros a b Hpre.
      destruct (classic (empty a)) as [Hea|Hnea].
      - apply witnessI1; first done. by apply ces_pr_in_elin.
      - destruct (classic (empty b)) as [Heb|Hneb].
        + apply witnessI2; first done. by apply ces_pr_in_elin.
        + destruct (classic (w1 a b)) as [Hw1|Hnw1].
          * by apply witnessI3.
          * apply witnessI4; try done.
            -- intros Hw1ba. eapply w1_then_not_inv_pr; eauto.
            -- by apply ces_pr_in_slin.
    Qed.

    (* empty_stack.thy:234-259 *)
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
          destruct (classic (empty a)) as [Hea|Hnea].
          * apply witnessI1; done.
          * destruct (classic (empty c)) as [Hec'|Hnec].
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
          destruct (classic (w1 a c)) as [Hw1ac|Hnw1ac].
          * by apply witnessI3.
          * destruct (classic (w1 c a)) as [Hw1ca|Hnw1ca].
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

    (* empty_stack.thy:261-262 *)
    Lemma witness_irreflexive : Irreflexive witness.
    Proof.
      intros a Hw.
      destruct Hw as [[Hea Haa]|[[Hea Haa]|[Hw1|Hlast]]].
      - by eapply elin_irreflexive.
      - by eapply elin_irreflexive.
      - by eapply w1_irreflexive.
      - destruct Hlast as (? & ? & ? & ? & Hslin). by eapply slin_irreflexive.
    Qed.

    (* empty_stack.thy:264-265 *)
    Lemma witness_antisymmetric : Antisymmetric operation (=) witness.
    Proof.
      intros a b Hab Hba.
      pose proof (witness_transitive a b a Hab Hba) as Haa.
      exfalso. by eapply witness_irreflexive.
    Qed.

    (* empty_stack.thy:267-268 *)
    Lemma witness_trichotomy : Trichotomy witness.
    Proof.
      intros a b.
      (* Use trichotomy of elin *)
      destruct (elin_total a b) as [Heq|[Hab|Hba]].
      - (* a = b *) right. left. done.
      - (* elin a b *)
        destruct (classic (empty a)) as [Hea|Hnea].
        + (* empty a *) left. by apply witnessI1.
        + destruct (classic (empty b)) as [Heb|Hneb].
          * (* empty b *) left. by apply witnessI2.
          * (* ¬ empty a, ¬ empty b - use slin trichotomy *)
            destruct (slin_total a b Hnea Hneb) as [Heq'|[Hsab|Hsba]].
            -- right. left. done.
            -- (* slin a b *)
               destruct (classic (w1 a b)) as [Hw1|Hnw1].
               ++ left. by apply witnessI3.
               ++ destruct (classic (w1 b a)) as [Hw1'|Hnw1'].
                  ** right. right. by apply witnessI3.
                  ** left. by apply witnessI4.
            -- (* slin b a *)
               destruct (classic (w1 b a)) as [Hw1|Hnw1].
               ++ right. right. by apply witnessI3.
               ++ destruct (classic (w1 a b)) as [Hw1'|Hnw1'].
                  ** left. by apply witnessI3.
                  ** right. right. by apply witnessI4.
      - (* elin b a *)
        destruct (classic (empty b)) as [Heb|Hneb].
        + (* empty b *) right. right. by apply witnessI1.
        + destruct (classic (empty a)) as [Hea|Hnea].
          * (* empty a *) right. right. by apply witnessI2.
          * (* ¬ empty a, ¬ empty b - use slin trichotomy *)
            destruct (slin_total a b Hnea Hneb) as [Heq'|[Hsab|Hsba]].
            -- right. left. done.
            -- (* slin a b *)
               destruct (classic (w1 a b)) as [Hw1|Hnw1].
               ++ left. by apply witnessI3.
               ++ destruct (classic (w1 b a)) as [Hw1'|Hnw1'].
                  ** right. right. by apply witnessI3.
                  ** left. by apply witnessI4.
            -- (* slin b a *)
               destruct (classic (w1 b a)) as [Hw1|Hnw1].
               ++ right. right. by apply witnessI3.
               ++ destruct (classic (w1 a b)) as [Hw1'|Hnw1'].
                  ** left. by apply witnessI3.
                  ** right. right. by apply witnessI4.
    Qed.

    (* empty_stack.thy:270-272 *)
    Lemma witness_correct_empty a ib rb :
      empty a → val ib rb →
      (witness ib a ∧ witness rb a) ∨ (witness a ib ∧ witness a rb).
    Proof.
      intros Hea Hval.
      destruct (elin_correct_empty a ib rb Hea Hval) as [[Hib_a Hrb_a]|[Ha_ib Ha_rb]].
      - left. split; by apply witnessI2.
      - right. split; by apply witnessI1.
    Qed.

    (* empty_stack.thy:274-275 *)
    Lemma val_then_not_witness ia ra :
      val ia ra → ¬ witness ra ia.
    Proof.
      intros Hval Hw.
      apply witnessD in Hw.
      destruct ces_wellformed as [_ _ _ _ _ _ Henv _].
      (* ia and ra are not empty since they're involved in val *)
      assert (Hneia : ¬ empty ia).
      { intros Heia. destruct (Henv ia Heia) as [Hnv _]. apply Hnv. exists ra. done. }
      assert (Hnera : ¬ empty ra).
      { intros Hera. destruct (Henv ra Hera) as [_ Hnv]. apply Hnv. exists ia. done. }
      destruct Hw as [[Hera Hrain]|[[Heia Hrain]|[Hw1|Hlast]]].
      - (* empty ra - contradiction *) done.
      - (* empty ia - contradiction *) done.
      - (* w1 ra ia - contradicts val_then_not_w1 *)
        destruct (val_then_not_w1 ia ra Hval) as [_ Hnw1]. done.
      - (* slin ra ia - contradicts val_then_slin with antisymmetry *)
        destruct Hlast as (_ & _ & _ & _ & Hslinra).
        pose proof (val_then_slin ia ra Hval) as Hslinia.
        assert (ra = ia) by (eapply slin_antisymmetric; done).
        subst ra. by eapply slin_irreflexive.
    Qed.

    (* empty_stack.thy:277-304 *)
    Lemma witness_ooo ia ra ib rb :
      val ia ra → val ib rb → witness ia ib → witness ib ra → witness rb ra.
    Proof.
      intros Hvalia Hvalib Hiaib Hibra.
      apply witnessD in Hiaib.
      apply witnessD in Hibra.
      destruct ces_wellformed as [_ _ _ _ _ _ Henv _].
      (* ia, ra, ib, rb are not empty since they're involved in val *)
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
      - (* empty ib *) done.
      - (* w1 ia ib *)
        destruct Hibra as [[Heib _]|[[Hera _]|[Hw1ibra|Hibra4]]].
        + done.
        + done.
        + (* w1 ib ra *)
          apply w1D in Hw1ibra as (? & ? & d & Hed & Hibd & Hdra).
          (* Use elin_correct_empty to relate rb and d *)
          destruct (elin_correct_empty d ib rb Hed Hvalib) as [[Hibd' Hrbd]|[Hdib Hdrb]].
          * (* elin ib d ∧ elin rb d - construct w1 rb ra *)
            apply witnessI3. eapply w1I; [done|done|done|done|done].
          * (* elin d ib ∧ elin d rb - contradiction: ib = d *)
            assert (ib = d) by (eapply elin_antisymmetric; done). subst d. done.
        + (* slin case for ib ra *)
          destruct Hibra4 as (? & ? & Hnw1ibra & Hnw1raib & Hslibra).
          (* From w1 ia ib and elin_correct_empty, derive contradiction or witness rb ra *)
          apply w1D in Hw1iaib as (? & ? & c & Hec & Hiac & Hcib).
          destruct (elin_correct_empty c ib rb Hec Hvalib) as [[Hibc Hrbc]|[Hcib' Hcrb]].
          * (* elin ib c ∧ elin rb c - contradiction via c = ib *)
            assert (c = ib) by (eapply elin_antisymmetric; done). subst c. done.
          * (* elin c ib ∧ elin c rb *)
            (* Construct w1 ia rb, then w1 ra rb, which leads to contradiction *)
            exfalso.
            assert (Hw1iarb : w1 ia rb) by (eapply w1I; [done|done|done|done|done]).
            assert (Hw1rarb : w1 ra rb) by (eapply val_then_same_w13; [exact Hvalia|done]).
            (* From w1 ra rb, get witness e *)
            apply w1D in Hw1rarb as (? & ? & e & Hee & Hrae & Herb).
            (* Use elin_correct_empty e ib rb *)
            destruct (elin_correct_empty e ib rb Hee Hvalib) as [[Hibe Hrbe]|[Heib Herb']].
            -- (* elin ib e ∧ elin rb e - contradiction: e = rb *)
               assert (e = rb) by (eapply elin_antisymmetric; done). subst e. done.
            -- (* elin e ib ∧ elin e rb - construct w1 ra ib, contradicts ¬ w1 ra ib *)
               apply Hnw1raib. eapply w1I; [done|done|done|done|done].
      - (* slin ia ib case *)
        destruct Hiaib4 as (? & ? & Hnw1iaib & Hnw1ibia & Hsliaib).
        destruct Hibra as [[Heib _]|[[Hera _]|[Hw1ibra|Hibra4]]].
        + done.
        + done.
        + (* w1 ib ra *)
          apply w1D in Hw1ibra as (? & ? & d & Hed & Hibd & Hdra).
          (* Use elin_correct_empty d ib rb to derive w1 rb ra *)
          destruct (elin_correct_empty d ib rb Hed Hvalib) as [[Hibd' Hrbd]|[Hdib Hdrb]].
          * (* elin ib d ∧ elin rb d - construct w1 rb ra *)
            apply witnessI3. eapply w1I; [done|done|done|done|done].
          * (* elin d ib ∧ elin d rb - contradiction: d = ib *)
            assert (d = ib) by (eapply elin_antisymmetric; done). subst d. done.
        + (* slin ib ra *)
          destruct Hibra4 as (? & ? & Hnw1ibra & Hnw1raib & Hslibra).
          (* Use slin_ooo to get slin rb ra *)
          pose proof (slin_ooo ia ra ib rb Hvalia Hvalib Hsliaib Hslibra) as Hslrbra.
          destruct (classic (w1 rb ra)) as [Hw1|Hnw1].
          * by apply witnessI3.
          * destruct (classic (w1 ra rb)) as [Hw1'|Hnw1'].
            -- (* w1 ra rb - derive contradiction *)
               apply w1D in Hw1' as (? & ? & e & Hee & Hrae & Herb).
               assert (Hibe : elin ib e) by (eapply not_w1_then_same_with_empty; try done).
               (* Use elin_correct_empty e ia ra *)
               destruct (elin_correct_empty e ia ra Hee Hvalia) as [[Hiae Hrae']|[Heia Hera]].
               ++ (* elin ia e ∧ elin ra e *)
                  (* Try elin_total e ib to get elin e ib or elin ib e *)
                  destruct (elin_total e ib) as [Heqeib|[Heib|Hibe']].
                  ** subst ib. done. (* e = ib contradicts empty e and ¬ empty ib *)
                  ** (* elin e ib - construct w1 ia ib, contradiction *)
                     exfalso. apply Hnw1iaib. eapply w1I; [done|done|done|done|done].
                  ** (* elin ib e - try elin_total e ia *)
                     destruct (elin_total e ia) as [Heqeia|[Heia'|Hiae']].
                     --- subst ia. done.
                     --- (* elin e ia - construct w1 ib ia, contradiction *)
                         exfalso. apply Hnw1ibia. eapply w1I; [done|done|done|done|done].
                     --- (* elin ia e - same as Hiae, can we get more? *)
                         (* Use elin_total e ra *)
                         destruct (elin_total e ra) as [Heqera|[Hera'|Hrae'']].
                         +++ subst ra. done.
                         +++ (* elin e ra - construct w1 ib ra, contradiction *)
                             exfalso. apply Hnw1ibra. eapply w1I; [done|done|done|done|done].
                         +++ (* elin ra e - same as Hrae, consistent *)
                             (* Use elin_correct_empty e ib rb to derive contradiction *)
                             destruct (elin_correct_empty e ib rb Hee Hvalib) as [[Hibe'' Hrbe]|[Heib Herb']].
                             *** (* elin ib e ∧ elin rb e - but we have elin e rb, so rb = e, contradiction *)
                                 assert (rb = e) by (eapply elin_antisymmetric; done). subst rb. done.
                             *** (* elin e ib ∧ elin e rb - we have elin ib e, so ib = e, contradiction *)
                                 assert (ib = e) by (eapply elin_antisymmetric; done). subst ib. done.
               ++ (* elin e ia ∧ elin e ra - contradiction: e = ra *)
                  assert (e = ra) by (eapply elin_antisymmetric; done). subst e. done.
            -- apply witnessI4; done.
    Qed.

    (* empty_stack.thy:306-323 *)
    Lemma witness_sequential_empty_stack : SequentialEmptyStack witness val empty.
    Proof.
      constructor.
      - (* SequentialEmptySet witness val empty *)
        constructor.
        + (* SequentialEmptyHistory witness val empty *)
          constructor.
          * (* WellformedEmptyHistory witness val empty *)
            destruct ces_wellformed as [Hch Hfin Hpo Hpoo Hvo Hapo Hetn Hvtnp].
            constructor.
            -- (* ConcHistory witness *)
               constructor.
               ++ apply witness_transitive.
               ++ apply witness_antisymmetric.
               ++ apply witness_irreflexive.
               ++ apply lem_trichotomy_then_abcd; [apply witness_trichotomy | apply witness_transitive].
            -- (* FinitePredicate *) done.
            -- (* push_once *) done.
            -- (* pop_once *) done.
            -- (* val_order *) done.
            -- (* all_popped_or_empty *) done.
            -- (* empty_then_not_val *) done.
            -- (* val_then_not_pr witness val *)
               intros a b Hval Hw.
               by eapply val_then_not_witness.
          * (* Trichotomy witness *)
            apply witness_trichotomy.
        + (* correct_empty witness val empty *)
          intros a Hea ib rb Hval.
          by apply witness_correct_empty.
      - (* sequential_lifo witness val *)
        intros ia ib ra rb Hvalia Hvalib Hiaib Hibra.
        by eapply witness_ooo.
    Qed.

    (* empty_stack.thy:325-329 *)
    Theorem concurrent_empty_stack_linearizable :
      ∃ prt, subrelation pre prt ∧ SequentialEmptyStack prt val empty.
    Proof.
      exists witness. split.
      - apply pr_in_witness.
      - apply witness_sequential_empty_stack.
    Qed.

  End concurrent_empty_stack_context.

  (* empty_stack.thy:333-385 *)
  Lemma stack_set_then_set pre val empty :
    linearizable_non_empty_stack (non_empty_pre pre empty) val →
    linearizable_set pre val empty →
    ∃ elin slin, ConcurrentEmptyStack pre val empty slin elin.
  Proof.
    intros [Hch_ne (slin & Hsub_slin & Hslin)] [Hch_pre (elin & Hsub_elin & Hselin)].
    exists elin, slin.
    (* Get wellformed properties from SequentialEmptySet *)
    destruct Hselin as [Hselin_seh Hselin_ce].
    destruct Hselin_seh as [Hselin_weh Hselin_total].
    destruct Hselin_weh as [Hch_elin Hfin_elin Hpo_elin Hpoo_elin Hvo_elin Hapo Hetn Hvtnp_elin].
    (* Get wellformed properties from SequentialStack *)
    destruct Hslin as [Hslin_ss Hslin_lifo].
    destruct Hslin_ss as [Hslin_wh Htop Htopo Htopp].
    destruct Hslin_wh as [Hch_slin Hfin_slin Hpo_slin Hpoo_slin Hvo_slin Hpop_slin Hvtnp_slin].
    (* Build ConcurrentEmptyStack *)
    constructor.
    - (* WellformedEmptyHistory pre val empty *)
      constructor.
      + done. (* ConcHistory pre *)
      + done. (* FinitePredicate *)
      + done. (* push_once *)
      + done. (* pop_once *)
      + done. (* val_order *)
      + done. (* all_popped_or_empty *)
      + done. (* empty_then_not_val *)
      + (* val_then_not_pr pre val *)
        intros a b Hval Hpre.
        apply (Hvtnp_elin a b Hval).
        by apply Hsub_elin.
    - (* SequentialStack slin val *)
      constructor.
      + constructor; done.
      + done.
    - (* pre a b → ¬ empty a → ¬ empty b → slin a b *)
      intros a b Hpre Hnea Hneb.
      apply Hsub_slin.
      unfold non_empty_pre. done.
    - (* SequentialEmptySet elin val empty *)
      constructor.
      + constructor; [constructor|]; done.
      + done.
    - (* pre a b → elin a b *)
      intros a b Hpre.
      by apply Hsub_elin.
  Qed.

  (* empty_stack.thy:387-393 *)
  Theorem concurrent_empty_stack_linearizable_main pre val empty :
    linearizable_non_empty_stack (non_empty_pre pre empty) val →
    linearizable_set pre val empty →
    linearizable_stack pre val empty.
  Proof.
    intros Hne Hls.
    destruct (stack_set_then_set pre val empty Hne Hls) as (elin & slin & Hces).
    unfold linearizable_stack.
    split.
    - (* ConcHistory pre *)
      destruct Hls as [Hch _]. done.
    - (* ∃ prt, subrelation pre prt ∧ SequentialEmptyStack prt val empty *)
      destruct (@concurrent_empty_stack_linearizable _ _ _ _ _ Hces) as (prt & Hsub & Hses).
      exists prt. done.
  Qed.

End empty_stack.
