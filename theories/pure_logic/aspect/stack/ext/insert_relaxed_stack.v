(* insert_relaxed_stack.v, ported from insert_relaxed_stack.thy *)

From iris_logatom.pure_logic.aspect.stack.ext Require Import conc_his_rel.

Section insert_relaxed_stack.
  Context `{abstract_stack_model}.
  Implicit Types (pre val : relation operation).

  (* insert_relaxed_stack.thy:10-13 *)
  Class InsertRelaxedStack pre val := {
    #[local] ir_stack_wellformed :: WellformedHistory pre val;
    pop_ordered a b : is_pop val a → is_pop val b → a ≠ b → pre a b ∨ pre b a;
    push_pop_ordered a b : is_push val a → is_pop val b → pre a b ∨ pre b a;
    ir_ooo ia ra ib rb : val ia ra → val ib rb → pre ia ib → pre ib ra → pre rb ra;
  }.

  Context pre val `{!InsertRelaxedStack pre val}.

  (* Make parent class instances available for typeclass resolution *)
  #[local] Existing Instance ir_stack_wellformed.
  #[local] Existing Instance wf_pre_transitive.
  #[local] Existing Instance wf_pre_antisymmetric.
  #[local] Existing Instance wf_pre_irreflexive.

  (* insert_relaxed_stack.thy:18-21 *)
  Definition witness : relation operation :=
    λ a b, pre a b ∨
           (∃ ra rb, val a ra ∧ val b rb ∧
             (pre ra b ∨ (pre a rb ∧ pre b ra ∧ pre rb ra))).

  (* insert_relaxed_stack.thy:23-25 *)
  Lemma witnessI1 a b : pre a b → witness a b.
  Proof. left. done. Qed.

  (* insert_relaxed_stack.thy:27-30 *)
  Lemma witnessI2 a ra b rb : val a ra → val b rb → pre ra b → witness a b.
  Proof.
    intros Hva Hvb Hrab.
    right. exists ra, rb. split; first done. split; first done. left. done.
  Qed.

  (* insert_relaxed_stack.thy:32-35 *)
  Lemma witnessI3 a ra b rb :
    val a ra → val b rb → pre a rb → pre b ra → pre rb ra → witness a b.
  Proof.
    intros Hva Hvb Harb Hbra Hrba.
    right. exists ra, rb. split; first done. split; first done. right. done.
  Qed.

  (* insert_relaxed_stack.thy:37-42 *)
  Lemma witnessD a b : witness a b →
    pre a b ∨
    (∃ ra rb, val a ra ∧ val b rb ∧ pre ra b) ∨
    (∃ ra rb, val a ra ∧ val b rb ∧ pre a rb ∧ pre b ra ∧ pre rb ra).
  Proof.
    intros [Hpre|(ra & rb & Hva & Hvb & [Hrab|(Harb & Hbra & Hrba)])].
    - left. done.
    - right. left. exists ra, rb. done.
    - right. right. exists ra, rb. done.
  Qed.

  (* insert_relaxed_stack.thy:170-171 - moved early for dependency *)
  Lemma lem_val_then_pr ia ra : val ia ra → pre ia ra.
  Proof.
    intros Hval.
    destruct (push_pop_ordered ia ra) as [Hir|Hri].
    - exists ra. done.
    - exists ia. done.
    - done.
    - exfalso. eapply def_val_then_not_pr; eauto.
  Qed.

  (* insert_relaxed_stack.thy:173-174 *)
  Lemma lem_val_then_not_witness ia ra : val ia ra → ¬ witness ra ia.
  Proof.
    intros Hval Hw.
    apply witnessD in Hw.
    destruct Hw as [Hpre|[(rx & rix & Hvr & Hvi & Hpre)|(rx & rix & Hvr & Hvi & H1 & H2 & H3)]].
    - eapply def_val_then_not_pr; eauto.
    - eapply def_val_order; first exact Hval. exists rx. right. done.
    - eapply def_val_order; first exact Hval. exists rx. right. done.
  Qed.

  (* insert_relaxed_stack.thy:44-54 *)
  Lemma lem_witness_irreflexive : Irreflexive witness.
  Proof.
    intros a Haa.
    apply witnessD in Haa.
    destruct Haa as [Hpre|[(ra & rb & Hva & Hvb & Hpre)|(ra & rb & Hva & Hvb & H1 & H2 & H3)]].
    - by eapply wf_pre_irreflexive.
    - exact (def_val_then_not_pr _ _ Hva Hpre).
    - pose proof (def_pop_once _ _ _ Hva Hvb) as Heq. subst rb.
      exact (wf_pre_irreflexive _ H3).
  Qed.

  (* insert_relaxed_stack.thy:140-141 *)
  Lemma lem_pr_in_witness : subrelation pre witness.
  Proof. intros a b. apply witnessI1. Qed.

  (* insert_relaxed_stack.thy:164-165 *)
  Lemma lem_witness_total_on_pop a b :
    is_pop val a → is_pop val b → a ≠ b → witness a b ∨ witness b a.
  Proof.
    intros Ha Hb Hneq.
    destruct (pop_ordered a b Ha Hb Hneq) as [Hab|Hba]; [left|right]; by apply witnessI1.
  Qed.

  (* insert_relaxed_stack.thy:167-168 *)
  Lemma lem_witness_total_on_push_pop a b :
    is_push val a → is_pop val b → witness a b ∨ witness b a.
  Proof.
    intros Ha Hb.
    destruct (push_pop_ordered a b Ha Hb) as [Hab|Hba]; [left|right]; by apply witnessI1.
  Qed.

  (* insert_relaxed_stack.thy:143-162 *)
  Lemma lem_witness_total_on_push a b :
    is_push val a → is_push val b → a ≠ b → witness a b ∨ witness b a.
  Proof.
    intros [ra Hva] [rb Hvb] Hneq.
    destruct (push_pop_ordered a rb) as [Harb|Hrba].
    - exists ra. done.
    - exists b. done.
    - destruct (push_pop_ordered b ra) as [Hbra|Hrab].
      + exists rb. done.
      + exists a. done.
      + (* pre a rb, pre b ra *)
        assert (Hra : is_pop val ra) by (exists a; done).
        assert (Hrb : is_pop val rb) by (exists b; done).
        destruct (decide (ra = rb)) as [Heq|Hneq_r].
        * subst rb. exfalso. apply Hneq. eapply def_push_once; eauto.
        * destruct (pop_ordered ra rb Hra Hrb Hneq_r) as [Hrarb|Hrbra].
          -- right. eapply (witnessI3 b rb a ra); done.
          -- left. eapply (witnessI3 a ra b rb); done.
      + (* pre ra b *)
        left. eapply (witnessI2 a ra b rb); done.
    - (* pre rb a *)
      right. eapply (witnessI2 b rb a ra); done.
  Qed.

  (* Helper for common contradiction pattern in transitivity proof:
     If we have witness-case-3 data for (a,b) and pre b a, contradiction. *)
  Local Lemma ir_contra a b ra rb :
    val a ra → val b rb → pre a rb → pre b ra → pre rb ra → pre b a → False.
  Proof.
    intros Hva Hvb Harb Hbra Hrba Hba.
    assert (pre ra rb) by (eapply ir_ooo; eauto).
    assert (ra = rb) by (by eapply wf_pre_antisymmetric).
    subst. assert (a = b) by (eapply def_push_once; eauto).
    subst. by eapply wf_pre_irreflexive.
  Qed.

  (* Helper: ir_ooo with antisymmetry gives contradiction *)
  Local Lemma ir_ooo_contra a b ra rb :
    val a ra → val b rb → pre b a → pre a rb → pre rb ra → False.
  Proof.
    intros Hva Hvb Hba Harb Hrbra.
    assert (pre ra rb) by (eapply ir_ooo; eauto).
    assert (ra = rb) by (by eapply wf_pre_antisymmetric).
    subst. by eapply wf_pre_irreflexive.
  Qed.

  (* insert_relaxed_stack.thy:56-117 *)
  Lemma lem_witness_transitive : Transitive witness.
  Proof.
    intros x y z Hxy Hyz.
    apply witnessD in Hxy.
    apply witnessD in Hyz.
    destruct Hxy as [Hxy|[(rx & ry & Hvx & Hvy & Hrxy)|(rx & ry & Hvx & Hvy & Hxry & Hyrx & Hryrx)]];
    destruct Hyz as [Hyz|[(ry' & rz & Hvy' & Hvz & Hry'z)|(ry' & rz & Hvy' & Hvz & Hyrz & Hzry' & Hrzry')]].

    - (* (1,1) pre x y, pre y z *)
      apply witnessI1. by etrans.

    - (* (1,2) pre x y; val y ry', val z rz, pre ry' z *)
      apply witnessI1.
      etrans; first exact Hxy.
      etrans; first exact (lem_val_then_pr _ _ Hvy'). exact Hry'z.

    - (* (1,3) pre x y; val y ry', val z rz, pre y rz, pre z ry', pre rz ry' *)
      destruct (def_push_or_pop x y Hxy) as [[cx [Hvcx|Hcvx]] _].
      + (* x is push: val x cx *)
        destruct (push_pop_ordered z cx) as [Hzcx|Hcxz];
          [exists rz; done|exists x; done| |by eapply witnessI2].
        (* pre z cx *)
        destruct (push_pop_ordered y cx) as [Hycx|Hcxy];
          [exists ry'; done|exists x; done| |].
        * (* pre y cx → ir_ooo gives pre ry' cx *)
          assert (pre ry' cx) by (eapply ir_ooo; eauto).
          eapply (witnessI3 x cx z rz); try done.
          -- by etrans.
          -- etrans; first exact Hrzry'. done.
        * (* pre cx y *)
          destruct (push_pop_ordered x ry') as [Hxry'|Hry'x];
            [exists cx; done|exists y; done| |].
          -- (* pre x ry' *)
             destruct (decide (cx = ry')) as [->|Hneq].
             ++ (* cx = ry' → x = y → pre x x → contradiction *)
                exfalso.
                assert (x = y) by (eapply def_push_once; eauto).
                subst. by eapply wf_pre_irreflexive.
             ++ destruct (pop_ordered cx ry') as [Hcxry'|Hry'cx];
                  [exists x; done|exists y; done|done| |].
                ** (* pre cx ry' → ir_ooo gives ry' = rz → y = z → witnessI1 *)
                   assert (Hry'rz : pre ry' rz) by
                     (eapply (ir_ooo z rz y ry'); [exact Hvz|exact Hvy'| |exact Hyrz];
                      etrans; first exact Hzcx; exact Hcxy).
                   pose proof (wf_pre_antisymmetric _ _ Hry'rz Hrzry') as Heq. subst.
                   assert (y = z) by (eapply def_push_once; eauto). subst.
                   apply witnessI1. done.
                ** (* pre ry' cx *)
                   eapply (witnessI3 x cx z rz); try done.
                   --- etrans; first exact Hxy. exact Hyrz.
                   --- etrans; first exact Hrzry'. done.
          -- (* pre ry' x → rz before cx via ry' and x *)
             eapply (witnessI3 x cx z rz); try done.
             ++ by etrans.
             ++ etrans; first exact Hrzry'.
                etrans; first exact Hry'x.
                exact (lem_val_then_pr _ _ Hvcx).
      + (* x is pop: val cx x → push_pop_ordered gives pre x z or contradiction *)
        destruct (push_pop_ordered z x) as [Hzx|Hxz];
          [exists rz; done|exists cx; done| |apply witnessI1; done].
        (* pre z x → ir_ooo_contra *)
        exfalso. eapply (ir_ooo_contra y z ry' rz); try done.
        by etrans.

    - (* (2,1) val x rx, val y ry, pre rx y; pre y z *)
      apply witnessI1.
      etrans; first exact (lem_val_then_pr _ _ Hvx).
      etrans; first exact Hrxy. exact Hyz.

    - (* (2,2) val x rx, val y ry, pre rx y; val y ry', val z rz, pre ry' z *)
      pose proof (def_pop_once _ _ _ Hvy Hvy') as ->. rename ry' into ry.
      eapply (witnessI2 x rx z rz); try done.
      etrans; first exact Hrxy.
      etrans; first exact (lem_val_then_pr _ _ Hvy). exact Hry'z.

    - (* (2,3) val x rx, val y ry, pre rx y; val y ry', val z rz, pre y rz, pre z ry', pre rz ry' *)
      pose proof (def_pop_once _ _ _ Hvy Hvy') as ->. rename ry' into ry.
      destruct (push_pop_ordered z rx) as [Hzrx|Hrxz];
        [exists rz; done|exists x; done| |by eapply witnessI2].
      (* pre z rx *)
      destruct (decide (rx = ry)) as [->|Hneq].
      + (* rx = ry → x = y → contradiction *)
        exfalso. assert (x = y) by (eapply def_push_once; eauto).
        subst. eapply wf_pre_irreflexive.
        etrans; first exact Hrxy. exact (lem_val_then_pr _ _ Hvy).
      + destruct (pop_ordered rx ry) as [Hrxry|Hryrx];
          [exists x; done|exists y; done|done| |].
        * (* pre rx ry → ir_ooo_contra *)
          exfalso. eapply (ir_ooo_contra y z ry rz); try done.
          by etrans.
        * (* pre ry rx *)
          eapply (witnessI3 x rx z rz); try done.
          -- etrans; first exact (lem_val_then_pr _ _ Hvx).
             etrans; first exact Hrxy. exact Hyrz.
          -- etrans; first exact Hrzry'. exact Hryrx.

    - (* (3,1) val x rx, val y ry, pre x ry, pre y rx, pre ry rx; pre y z *)
      destruct (def_push_or_pop y z Hyz) as [_ [cz [Hvcz|Hczv]]].
      + (* z is push: val z cz *)
        destruct (push_pop_ordered z rx) as [Hzrx|Hrxz];
          [exists cz; done|exists x; done| |by eapply witnessI2].
        (* pre z rx *)
        destruct (push_pop_ordered x cz) as [Hxcz|Hczx];
          [exists rx; done|exists z; done| |].
        * (* pre x cz *)
          destruct (push_pop_ordered z ry) as [Hzry|Hryz];
            [exists cz; done|exists y; done| |].
          -- (* pre z ry → ir_ooo(y,ry,z,cz) → pre cz ry *)
             assert (pre cz ry) by (eapply ir_ooo; eauto).
             assert (Hczrx : pre cz rx) by (by etrans).
             eapply (witnessI3 x rx z cz); try done.
          -- (* pre ry z → pre x z by trans → witnessI1 *)
             apply witnessI1. etrans; first exact Hxry. exact Hryz.
        * (* pre cz x → pre y x → ir_contra *)
          exfalso. eapply (ir_contra x y rx ry); try done.
          etrans; first exact Hyz. etrans; first exact (lem_val_then_pr _ _ Hvcz). exact Hczx.
      + (* z is pop: val cz z *)
        destruct (push_pop_ordered x z) as [Hxz|Hzx];
          [exists rx; done|exists cz; done|apply witnessI1; done|].
        (* pre z x → pre y x → ir_contra *)
        exfalso. eapply (ir_contra x y rx ry); try done.
        by etrans.

    - (* (3,2) val x rx, val y ry, pre x ry, pre y rx, pre ry rx;
              val y ry', val z rz, pre ry' z *)
      pose proof (def_pop_once _ _ _ Hvy Hvy') as ->. rename ry' into ry.
      destruct (push_pop_ordered z rx) as [Hzrx|Hrxz];
        [exists rz; done|exists x; done| |by eapply witnessI2].
      (* pre z rx *)
      destruct (push_pop_ordered x rz) as [Hxrz|Hrzx];
        [exists rx; done|exists z; done| |].
      + (* pre x rz *)
        destruct (decide (rx = rz)) as [->|Hneq].
        * (* rx = rz → x = z → pre y x → ir_contra *)
          exfalso. assert (Heq : x = z) by (eapply def_push_once; eauto).
          subst. apply (ir_contra _ _ _ _ Hvx Hvy Hxry Hyrx Hryrx).
          etrans; first exact (lem_val_then_pr _ _ Hvy). exact Hry'z.
        * destruct (pop_ordered rx rz) as [Hrxrz|Hrzrx];
            [exists x; done|exists z; done|done| |].
          -- (* pre rx rz → ir_ooo(x,rx,z,rz) → pre rz rx contradiction *)
             exfalso.
             assert (pre x z) by (etrans; first exact Hxry; exact Hry'z).
             assert (pre rz rx) by (eapply ir_ooo; eauto).
             assert (rx = rz) by (by eapply wf_pre_antisymmetric).
             done.
          -- (* pre rz rx *)
             by eapply (witnessI3 x rx z rz).
      + (* pre rz x → pre y x → ir_contra *)
        exfalso. eapply (ir_contra x y rx ry); try done.
        etrans; first exact (lem_val_then_pr _ _ Hvy).
        etrans; first exact Hry'z.
        etrans; first exact (lem_val_then_pr _ _ Hvz). exact Hrzx.

    - (* (3,3) val x rx, val y ry, pre x ry, pre y rx, pre ry rx;
              val y ry', val z rz, pre y rz, pre z ry', pre rz ry' *)
      pose proof (def_pop_once _ _ _ Hvy Hvy') as ->. rename ry' into ry.
      destruct (push_pop_ordered z rx) as [Hzrx|Hrxz];
        [exists rz; done|exists x; done| |by eapply witnessI2].
      (* pre z rx *)
      destruct (push_pop_ordered x rz) as [Hxrz|Hrzx];
        [exists rx; done|exists z; done| |].
      + (* pre x rz *)
        destruct (decide (rx = rz)) as [->|Hneq].
        * (* rx = rz → x = z → pre ry rz ∧ pre rz ry → ry = rz → contradiction *)
          exfalso.
          assert (x = z) by (eapply def_push_once; eauto).
          subst.
          assert (rz = ry) by (by eapply wf_pre_antisymmetric).
          subst. by eapply wf_pre_irreflexive.
        * destruct (pop_ordered rx rz) as [Hrxrz|Hrzrx];
            [exists x; done|exists z; done|done| |].
          -- (* pre rx rz → pre rz rx by trans(rz,ry,rx) → contradiction *)
             exfalso.
             assert (pre rz rx) by (etrans; first exact Hrzry'; exact Hryrx).
             assert (rx = rz) by (by eapply wf_pre_antisymmetric). done.
          -- (* pre rz rx *)
             by eapply (witnessI3 x rx z rz).
      + (* pre rz x → pre y x → ir_contra *)
        exfalso. eapply (ir_contra x y rx ry); try done.
        etrans; first exact Hyrz. exact Hrzx.
  Qed.

  (* insert_relaxed_stack.thy:119-138 *)
  Lemma lem_witness_antisymmetric : Antisymmetric operation (=) witness.
  Proof.
    intros a b Hab Hba.
    apply witnessD in Hab.
    apply witnessD in Hba.
    destruct Hab as [Hab|[(ra & rb & Hva & Hvb & Hrab)|(ra & rb & Hva & Hvb & Harb & Hbra & Hrba)]];
    destruct Hba as [Hba|[(rb2 & ra2 & Hvb2 & Hva2 & Hrb2a)|(rb2 & ra2 & Hvb2 & Hva2 & Hbra2 & Harb2 & Hra2rb2)]].
    - (* (1,1) pre a b, pre b a *)
      by eapply wf_pre_antisymmetric.
    - (* (1,2) pre a b; val b rb2, val a ra2, pre rb2 a *)
      exfalso. eapply def_val_then_not_pr; first exact Hvb2.
      by etrans.
    - (* (1,3) pre a b; val b rb2, val a ra2, pre b ra2, pre a rb2, pre ra2 rb2 *)
      pose proof (ir_ooo _ _ _ _ Hva2 Hvb2 Hab Hbra2) as Hrb2ra2.
      pose proof (wf_pre_antisymmetric _ _ Hra2rb2 Hrb2ra2) as Heq. subst ra2.
      eapply def_push_once; eauto.
    - (* (2,1) val a ra, val b rb, pre ra b; pre b a *)
      exfalso. eapply def_val_then_not_pr; first exact Hva.
      by etrans.
    - (* (2,2) val a ra, val b rb, pre ra b; val b rb2, val a ra2, pre rb2 a *)
      pose proof (def_pop_once _ _ _ Hva Hva2) as ->. rename ra2 into ra.
      pose proof (def_pop_once _ _ _ Hvb Hvb2) as ->. rename rb2 into rb.
      eapply wf_pre_antisymmetric.
      + etrans; first exact (lem_val_then_pr _ _ Hva). exact Hrab.
      + etrans; first exact (lem_val_then_pr _ _ Hvb). exact Hrb2a.
    - (* (2,3) val a ra, val b rb, pre ra b; val b rb2, val a ra2, pre b ra2, pre a rb2, pre ra2 rb2 *)
      pose proof (def_pop_once _ _ _ Hva Hva2) as ->. rename ra2 into ra.
      pose proof (def_pop_once _ _ _ Hvb Hvb2) as ->. rename rb2 into rb.
      exfalso.
      pose proof (wf_pre_antisymmetric _ _ Hrab Hbra2) as Heq. subst ra.
      eapply def_val_order; first exact Hva. exists rb. right. done.
    - (* (3,1) val a ra, val b rb, pre a rb, pre b ra, pre rb ra; pre b a *)
      pose proof (ir_ooo _ _ _ _ Hvb Hva Hba Harb) as Hrarb.
      pose proof (wf_pre_antisymmetric _ _ Hrba Hrarb) as Heq. subst ra.
      eapply def_push_once; eauto.
    - (* (3,2) val a ra, val b rb, pre a rb, pre b ra, pre rb ra;
              val b rb2, val a ra2, pre rb2 a *)
      pose proof (def_pop_once _ _ _ Hva Hva2) as ->. rename ra2 into ra.
      pose proof (def_pop_once _ _ _ Hvb Hvb2) as ->. rename rb2 into rb.
      exfalso.
      pose proof (wf_pre_antisymmetric _ _ Harb Hrb2a) as Heq. subst rb.
      eapply def_val_order; first exact Hva. exists b. left. done.
    - (* (3,3) val a ra, val b rb, pre a rb, pre b ra, pre rb ra;
              val b rb2, val a ra2, pre b ra2, pre a rb2, pre ra2 rb2 *)
      pose proof (def_pop_once _ _ _ Hva Hva2) as ->. rename ra2 into ra.
      pose proof (def_pop_once _ _ _ Hvb Hvb2) as ->. rename rb2 into rb.
      pose proof (wf_pre_antisymmetric _ _ Hrba Hra2rb2) as Heq. subst ra.
      eapply def_push_once; eauto.
  Qed.

  (* Helper: Abcd for witness (needed by ConcHistory) *)
  Local Lemma lem_witness_abcd : Abcd witness.
  Proof.
    intros a b c d Hab Hcd.
    assert (Ha : is_push val a ∨ is_pop val a).
    { destruct (witnessD _ _ Hab) as [Hpre|[(ra & rb & Hva & _ & _)|(ra & rb & Hva & _ & _)]].
      - destruct (def_push_or_pop _ _ Hpre) as [[ca [?|?]] _]; [left|right]; eexists; eauto.
      - left. eexists. exact Hva.
      - left. eexists. exact Hva. }
    assert (Hd : is_push val d ∨ is_pop val d).
    { destruct (witnessD _ _ Hcd) as [Hpre|[(_ & rd & _ & Hvd & _)|(_ & rd & _ & Hvd & _)]].
      - destruct (def_push_or_pop _ _ Hpre) as [_ [cd [?|?]]]; [left|right]; eexists; eauto.
      - left. eexists. exact Hvd.
      - left. eexists. exact Hvd. }
    destruct (decide (a = d)) as [->|Hneq].
    - right. exact (lem_witness_transitive _ _ _ Hcd Hab).
    - assert (Htotal : witness a d ∨ witness d a).
      { destruct Ha as [Ha|Ha]; destruct Hd as [Hd|Hd].
        - exact (lem_witness_total_on_push a d Ha Hd Hneq).
        - exact (lem_witness_total_on_push_pop a d Ha Hd).
        - destruct (lem_witness_total_on_push_pop d a Hd Ha) as [?|?]; [right|left]; done.
        - exact (lem_witness_total_on_pop a d Ha Hd Hneq). }
      destruct Htotal as [Had|Hda].
      + left. done.
      + right. exact (lem_witness_transitive _ _ _
          (lem_witness_transitive _ _ _ Hcd Hda) Hab).
  Qed.

  (* insert_relaxed_stack.thy:176-187 *)
  Lemma lem_witness_wellformed : WellformedHistory witness val.
  Proof.
    constructor.
    - (* Transitive witness *)
      exact lem_witness_transitive.
    - (* Antisymmetric witness *)
      exact lem_witness_antisymmetric.
    - (* Irreflexive witness *)
      exact lem_witness_irreflexive.
    - (* FinitePredicate - same val, so same finite ops *)
      exact operation_finite.
    - exact def_push_once.
    - exact def_pop_once.
    - exact def_val_order.
    - (* push_or_pop for witness *)
      intros a b Hw.
      destruct (witnessD _ _ Hw) as [Hpre|[(ra & rb & Hva & Hvb & _)|(ra & rb & Hva & Hvb & _)]].
      + exact (def_push_or_pop _ _ Hpre).
      + split; [exists ra; left|exists rb; left]; done.
      + split; [exists ra; left|exists rb; left]; done.
    - (* val_then_not_pr for witness *)
      exact lem_val_then_not_witness.
  Qed.

  (* insert_relaxed_stack.thy:189-198 *)
  Lemma lem_witness_sequential_history : SequentialSet witness val.
  Proof.
    constructor.
    - exact lem_witness_wellformed.
    - exact lem_witness_total_on_push.
    - exact lem_witness_total_on_pop.
    - exact lem_witness_total_on_push_pop.
  Qed.

  (* insert_relaxed_stack.thy:200-201 *)
  Lemma push_witness_pop_then_pr a b :
    witness a b → is_push val a → is_pop val b → pre a b.
  Proof.
    intros Hw [ra Hva] [cb Hcb].
    destruct (witnessD _ _ Hw) as [Hpre|[(_ & rb & _ & Hvb & _)|(_ & rb & _ & Hvb & _)]].
    - done.
    - exfalso. eapply def_val_order; first exact Hvb. exists cb. left. done.
    - exfalso. eapply def_val_order; first exact Hvb. exists cb. left. done.
  Qed.

  (* insert_relaxed_stack.thy:203-215 *)
  Lemma lem_witness_ooo : sequential_lifo witness val.
  Proof.
    intros ia ib ra rb Hva Hvb Hwiab Hwibra.
    (* Establish pre ib ra from push_witness_pop_then_pr *)
    assert (Hibra : pre ib ra).
    { apply push_witness_pop_then_pr; try done.
      - exists rb. done.
      - exists ia. done. }
    (* Destruct witness ia ib *)
    destruct (witnessD _ _ Hwiab) as
      [Hpre|[(rx & ry & Hvx & Hvy & Hrxib)|(rx & ry & Hvx & Hvy & Hiary & Hibrx & Hryrx)]].
    - (* case 1: pre ia ib → ir_ooo gives pre rb ra → witnessI1 *)
      apply witnessI1. eapply ir_ooo; eauto.
    - (* case 2: val ia rx, val ib ry, pre rx ib *)
      pose proof (def_pop_once _ _ _ Hva Hvx) as ->. rename rx into ra.
      pose proof (def_pop_once _ _ _ Hvb Hvy) as ->. rename ry into rb.
      (* pre ra ib and pre ib ra → ra = ib → val_order contradiction *)
      pose proof (wf_pre_antisymmetric _ _ Hrxib Hibra) as Heq. subst.
      exfalso. eapply def_val_order; first exact Hva. exists rb. right. done.
    - (* case 3: val ia rx, val ib ry, pre ia ry, pre ib rx, pre ry rx *)
      pose proof (def_pop_once _ _ _ Hva Hvx) as ->. rename rx into ra.
      pose proof (def_pop_once _ _ _ Hvb Hvy) as ->. rename ry into rb.
      (* pre rb ra directly → witnessI1 *)
      apply witnessI1. exact Hryrx.
  Qed.

  (* insert_relaxed_stack.thy:217-222 *)
  Lemma lem_witness_sequential_stack : SequentialStack witness val.
  Proof.
    constructor.
    - exact lem_witness_sequential_history.
    - exact lem_witness_ooo.
  Qed.

  (* insert_relaxed_stack.thy:224-228 *)
  Local Instance witness_dec `{!RelDecision pre, !RelDecision val} : RelDecision witness.
  Proof. intros a b. unfold witness. apply _. Qed.

  Theorem insert_relaxed_stack_linearizable `{!RelDecision pre, !RelDecision val} :
    ∃ prt (_ : RelDecision prt), subrelation pre prt ∧ SequentialStack prt val.
  Proof.
    exists witness, _.
    split.
    - exact lem_pr_in_witness.
    - exact lem_witness_sequential_stack.
  Qed.

End insert_relaxed_stack.
